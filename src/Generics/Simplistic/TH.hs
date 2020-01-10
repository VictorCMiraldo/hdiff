{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE CPP #-}
module Generics.Simplistic.TH where

import Data.Function (on)
import Data.Char (isAlphaNum)
import Data.List (sortBy)

import Control.Monad
import Control.Monad.State
import Control.Monad.Writer   (WriterT, tell, runWriterT)
import Control.Monad.Identity (runIdentity)
import Control.Arrow ((***))

import Language.Haskell.TH hiding (match)

import qualified Data.Map as M

-- Returns all the types we need to derive Deep
-- and or Generic to.
getTypesInvolved :: [Name] -> Q Type -> Q [Dec]
getTypesInvolved prims t
  = do sty                <- t >>= convertType 
       (_ , (Idxs _ m _)) <- runIdxsM (reifySTy prims sty)
       -- Now we make sure we have processed all
       -- types
       m' <- mapM extractDTI (M.toList m)
       let final = sortBy (compare `on` second) m'
{-
       gens   <- if not deriveGenerics 
                 then return []
                 else concat <$> mapM (mkGen . first) final
       mydefs <- concat <$> mapM (mkDec prims . first) final
       return $ gens ++ mydefs
-}
       [d| type TypesInvolved = $(mkTys (map first final)) |]
 where
    first  (x , _ , _) = x
    second (_ , x , _) = x
    
    extractDTI (sty , (_ix , Nothing))
      = fail $ "Type " ++ show sty ++ " has no datatype information."
    extractDTI (sty , (ix , Just dti))
      = return (sty , ix , dti)

mkTys :: [STy] -> Q Type
mkTys [] = [t| '[] |]
mkTys (x:xs) = [t| ( $(return $ trevnocType x) ': $(mkTys xs)) |]

{-
mkGen :: STy -> Q [Dec]
mkGen ty = [d| instance G.Generic $(return $ trevnocType ty) |]

mkDec :: [Name] -> STy -> Q [Dec]
mkDec ns ty = [d| instance Deep $(mkList ns) $(return $ trevnocType ty) |]
  where
    mkList [] = [t| '[] |]
    mkList (x:xs) = [t| ( $(return $ ConT x) ': $(mkList xs)) |]
-}


-- Sketch;
--
--   Given a module:
--
--    > module Test where
--    > data Rose a = Fork a [Rose a]
--    > $(deriveFamily [t| Rose Int |])
--
--  We will see we are looking into deriving a family
--  for an AppT (ConT Rose) (ConT Int).
--
--  Working with a (M.Map STy (Int , DInfo (K + I))) in a state;
--
--  0) Translate to a simpler Type-expression, call it STy.
--  1) Register (AppST (ConST Rose) (ConST Int)) as family index Z
--  2) reify lhs: [d| data Rose a = Fork a [Rose a] |]
--      a) reduce rhs of (1): (\a -> Fork a [Rose a]) @ (ConT Int)
--                        == Fork Int [Rose Int]
--      b) Take the fields that require processing: [ConT Int , AppST List (AppST Rose Int)]
--      c) Somehow figure out that (ConT Int) is a Konstant.
--      d) Look into (AppST List (AppST Rose Int))
--      e) Is it already processed?
--      f) If yes, we are done.
--  3) Register (AppST List (AppST Rose Int))as family index (S Z)
--  4) reify lhs: [d| data List a = Nil | Cons a (List a) |]
--      a) reduce rhs of (4): (\a -> Nil | Cons a (List a)) @ (AppST Rose Int)
--      b) Take the fields of each constructor:
--           [] , [AppST Rose Int , AppST List (AppST Rose Int)]
--      c) Notice that both fields of 'Cons' have already
--         been registered; hence they become: [I Z , I (S Z)]
--

-- * Data Structures

type DataName  = Name
type ConName   = Name
type FieldName = Name
type Args      = [Name]

-- |Datatype information, parametrized by the type of Type-expressions
--  that appear on the fields of the constructors.
data DTI ty
  = ADT DataName Args [ CI ty ]
  | New DataName Args (CI ty)
  deriving (Eq , Show , Functor)

-- |Constructor information
data CI ty
  = Normal ConName [ty]
  | Infix  ConName Fixity ty ty
  | Record ConName [ (FieldName , ty) ]
  deriving (Eq , Show , Functor)

-- ** Monadic Maps

ciMapM :: (Monad m) => (ty -> m tw) -> CI ty -> m (CI tw)
ciMapM f (Normal name tys)  = Normal name  <$> mapM f tys
ciMapM f (Infix name x l r) = Infix name x <$> f l <*> f r
ciMapM f (Record name tys)  = Record name  <$> mapM (rstr . (id *** f)) tys
  where
    rstr (a , b) = b >>= return . (a,)

dtiMapM :: (Monad m) => (ty -> m tw) -> DTI ty -> m (DTI tw)
dtiMapM f (ADT name args ci) = ADT name args <$> mapM (ciMapM f) ci
dtiMapM f (New name args ci) = New name args <$> ciMapM f ci

-- defined but not used
-- dtiName :: DTI ty -> DataName
-- dtiName (ADT name _ _) = name
-- dtiName (New name _ _) = name

dti2ci :: DTI ty -> [CI ty]
dti2ci (ADT _ _ cis) = cis
dti2ci (New _ _ ci)  = [ ci ]

ci2ty :: CI ty -> [ty]
ci2ty (Normal _ tys)  = tys
ci2ty (Infix _ _ a b) = [a , b]
ci2ty (Record _ tys)  = map snd tys

ciName :: CI ty -> Name
ciName (Normal n _)    = n
ciName (Infix n _ _ _) = n
ciName (Record n _)    = n

ci2Pat :: CI ty -> Q ([Name] , Pat)
ci2Pat ci
  = do ns <- mapM (const (newName "x")) (ci2ty ci)
       return (ns , (ConP (ciName ci) (map VarP ns)))

ci2Exp :: CI ty -> Q ([Name], Exp)
ci2Exp ci
  = do ns <- mapM (const (newName "y")) (ci2ty ci)
       return (ns , foldl (\e n -> AppE e (VarE n)) (ConE (ciName ci)) ns)

-- * Simpler STy Language

-- A Simplified version of Language.Haskell.TH
data STy
  = AppST STy STy
  | VarST Name
  | ConST Name
  deriving (Eq , Show, Ord)

styFold :: (a -> a -> a) -> (Name -> a) -> (Name -> a) -> STy -> a
styFold app var con (AppST a b) = app (styFold app var con a) (styFold app var con b)
styFold _   var _   (VarST n)   = var n
styFold _   _   con (ConST n)   = con n

-- |Does a STy have a varible name?
isClosed :: STy -> Bool
isClosed = styFold (&&) (const False) (const True)

-- ** Back and Forth conversion

convertType :: (Monad m) => Type -> m STy
convertType (AppT a b)  = AppST <$> convertType a <*> convertType b
convertType (SigT t _)  = convertType t
convertType (VarT n)    = return (VarST n)
convertType (ConT n)    = return (ConST n)
convertType (ParensT t) = convertType t
convertType ListT       = return (ConST (mkName "[]"))
convertType (TupleT n)  = return (ConST (mkName $ '(':replicate (n-1) ',' ++ ")"))
convertType t           = fail ("convertType: Unsupported Type: " ++ show t)

trevnocType :: STy -> Type
trevnocType (AppST a b) = AppT (trevnocType a) (trevnocType b)
trevnocType (VarST n)   = VarT n
trevnocType (ConST n)
  | n == mkName "[]" = ListT
  | isTupleN n       = TupleT $ length (show n) - 1
  | otherwise        = ConT n
  where isTupleN n0 = take 2 (show n0) == "(,"

-- |Handy substitution function.
--
--  @stySubst t m n@ substitutes m for n within t, that is: t[m/n]
stySubst :: STy -> Name -> STy -> STy
stySubst (AppST a b) m n = AppST (stySubst a m n) (stySubst b m n)
stySubst (ConST a)   _ _ = ConST a
stySubst (VarST x)   m n
  | x == m    = n
  | otherwise = VarST x

-- |Just like subst, but applies a list of substitutions
styReduce :: [(Name , STy)] -> STy -> STy
styReduce parms t = foldr (\(n , m) ty -> stySubst ty n m) t parms

-- |Flattens an application into a list of arguments;
--
--  @styFlatten (AppST (AppST Tree A) B) == (Tree , [A , B])@
styFlatten :: STy -> (STy , [STy])
styFlatten (AppST a b) = id *** (++ [b]) $ styFlatten a
styFlatten sty         = (sty , [])

-- * Parsing Haskell's AST

reifyDec :: Name -> Q Dec
reifyDec name =
  do info <- reify name
     case info of TyConI dec -> return dec
                  _          -> fail $ show name ++ " is not a declaration"

argInfo :: TyVarBndr -> Name
argInfo (PlainTV  n)   = n
argInfo (KindedTV n _) = n

-- Extracts a DTI from a Dec
decInfo :: Dec -> Q (DTI STy)
decInfo (TySynD     _name _args _ty)       = fail "Type Synonyms not supported"
decInfo (DataD    _ name args    _ cons _) = ADT name (map argInfo args) <$> mapM conInfo cons
decInfo (NewtypeD _ name args    _ con _)  = New name (map argInfo args) <$> conInfo con
decInfo _                                  = fail "Only type declarations are supported"

-- Extracts a CI from a Con
conInfo :: Con -> Q (CI STy)
conInfo (NormalC  name ty) = Normal name <$> mapM (convertType . snd) ty
conInfo (RecC     name ty) = Record name <$> mapM (\(s , _ , t) -> (s,) <$> convertType t) ty
conInfo (InfixC l name r)
  = do info <- reifyFixity name
       let fixity = maybe defaultFixity id $ info
       Infix name fixity <$> convertType (snd l) <*> convertType (snd r)
conInfo (ForallC _ _ _) = fail "Existentials not supported"
#if MIN_VERSION_template_haskell(2,11,0)
conInfo (GadtC _ _ _)    = fail "GADTs not supported"
conInfo (RecGadtC _ _ _) = fail "GADTs not supported"
#endif

-- |Reduces the rhs of a datatype declaration
--  with some provided arguments. Step (2.a) of our sketch.
--
--  Precondition: application is fully saturated;
--  ie, args and parms have the same length
--
dtiReduce :: DTI STy -> [STy] -> DTI STy
dtiReduce (ADT name args cons) parms
  = ADT name [] (map (ciReduce (zip args parms)) cons)
dtiReduce (New name args con)  parms
  = New name [] (ciReduce (zip args parms) con)

ciReduce :: [(Name , STy)] -> CI STy -> CI STy
ciReduce parms ci = runIdentity (ciMapM (return . styReduce parms) ci)  

-- * Monad
--
-- Keeks the (M.Map STy (Int , DTI Sty)) in a state.

data IK
  = AtomI Int
  | AtomK Name
  deriving (Eq , Show)

-- defined but not used
-- ikElim :: (Int -> a) -> (Name -> a) -> IK -> a
-- ikElim i k (AtomI n) = i n
-- ikElim i k (AtomK n) = k n

data Idxs 
  = Idxs { idxsNext :: Int
         , idxsMap  :: M.Map STy (Int , Maybe (DTI IK))
         , idxsSyns :: M.Map STy STy
         }
  deriving (Show)

onMap :: (M.Map STy (Int , Maybe (DTI IK)) -> M.Map STy (Int , Maybe (DTI IK)))
      -> Idxs -> Idxs
onMap f (Idxs n m eqs) = Idxs n (f m) eqs

type IdxsM = StateT Idxs

runIdxsM :: (Monad m) => IdxsM m a -> m (a , Idxs)
runIdxsM = flip runStateT (Idxs 0 M.empty M.empty)

-- |The actual monad we need to run all of this;
type M = IdxsM Q

-- |Returns the index of a "Name" within the family.
--  If this name has not been registered yet, returns
--  a fresh index.
indexOf :: (Monad m) => STy -> IdxsM m Int
indexOf name
  = do st <- get
       case M.lookup name (idxsSyns st) of
         Just orig -> indexOf orig -- TODO: make sure orig is in the map! :P
         Nothing ->
           case M.lookup name (idxsMap st) of
             Just i  -> return (fst i)
             Nothing -> let i = idxsNext st
                         in put (Idxs (i + 1)
                                      (M.insert name (i , Nothing) (idxsMap st))
                                      (idxsSyns st))
                         >> return i

-- |Register some Datatype Information for a given STy
register :: (Monad m) => STy -> DTI IK -> IdxsM m ()
register ty info = indexOf ty -- the call to indexOf guarantees the
                              -- adjust will do something;
                >> modify (onMap $ M.adjust (id *** const (Just info)) ty)

-- | All the necessary lookups:
lkup :: (Monad m) => STy -> IdxsM m (Maybe (Int , Maybe (DTI IK)))
lkup ty = M.lookup ty . idxsMap <$> get


-- | Adds another type with the same index as the previous
addTySynEquiv :: (Monad m) => STy -> STy -> IdxsM m ()
addTySynEquiv orig new = 
  modify (\st -> st { idxsSyns = M.insert new orig (idxsSyns st) })

-- defined but not used
-- lkupInfo :: (Monad m) => STy -> IdxsM m (Maybe Int)
-- lkupInfo ty = fmap fst <$> lkup ty

lkupData :: (Monad m) => STy -> IdxsM m (Maybe (DTI IK))
lkupData ty = join . fmap snd <$> lkup ty

hasData :: (Monad m) => STy -> IdxsM m Bool
hasData ty = maybe False (const True) <$> lkupData ty

----------------------------
-- * Preprocessing Data * --
----------------------------

-- |Performs step 2 of the sketch;
reifySTy :: [Name] -> STy -> M ()
reifySTy prims sty0
  = do _ <- indexOf sty0 -- we don't care about the index of sty now, but we
                        -- need to register it
       (dec , args) <- preprocess sty0
       go dec args
  where
    preprocess :: STy -> M (DTI STy , [STy])
    preprocess ty = 
      let (head , args) = styFlatten ty
       in case head of
         ConST name -> do
           dec <- lift (reifyDec name)
           resolveTySyn (addTySynEquiv ty) dec args
         _ -> fail "I can't convert appST or varST in reifySTy"

    resolveTySyn :: (STy -> M ()) -> Dec -> [STy] -> M (DTI STy , [STy])
    resolveTySyn upd8 (TySynD _ defargs def) localargs = do
      sdef <- convertType def
      let dict = zip (map argInfo defargs) localargs
      let res = styReduce dict sdef
      upd8 res
      preprocess res
    resolveTySyn _ def localargs = (,localargs) <$> lift (decInfo def)
    
    go :: DTI STy -> [STy] -> M ()
    go dec args
      = do -- TODO: Check that the precondition holds.
           let res = dtiReduce dec args
           (final , todo) <- runWriterT $ dtiMapM (convertSTy prims) res
           register sty0 final
           mapM_ (reifySTy prims) todo
    
    -- Convert the STy's in the fields of the constructors;
    -- tells a list of STy's we still need to process.
    convertSTy :: [Name] -> STy -> WriterT [STy] M IK
    convertSTy prims ty
      -- We remove sty from the list of todos
      -- otherwise we get an infinite loop
      | ty == sty0 = AtomI <$> lift (indexOf ty)
      | isClosed ty
      = case makeCons prims ty of
          Just k  -> return (AtomK k)
          Nothing -> do ix     <- lift (indexOf ty)
                        hasDti <- lift (hasData ty)
                        when (not hasDti) (tell [ty])
                        return (AtomI ix)
      | otherwise
      = fail $ "I can't convert type variable " ++ show ty
              ++ " when converting " ++ show sty0

    makeCons :: [Name] -> STy -> Maybe Name
    makeCons prims (ConST n)
      | n `elem` prims = Just n
      | otherwise      = Nothing
    makeCons _      _        = Nothing
