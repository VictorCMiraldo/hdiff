module Data.Digems.Generic.Treefix where

data UTx :: (kon -> *) -> [*] -> [[[Atom kon]]] -> Nat -> * -> *  where
  UTxHere :: x -> UTx ki fam codes i x
  UTxPeel :: (IsNat n) => Constr (Lkup i codes) n
         -> UTxNP ki fam codes (Lkup n (Lkup i codes)) x
         -> UTx ki fam codes i x

data UTxNP :: (kon -> *) -> [*] -> [[[Atom kon]]] -> [Atom kon] -> * -> *
    where
  UTxNPNil   :: UTxNP ki fam codes '[] x
  UTxNPPath  :: (IsNat i)
            => UTx ki fam codes i x
            -> UTxNP ki fam codes prod x
            -> UTxNP ki fam codes (I i ': prod) x
  UTxNPSolid :: ki k
            -> UTxNP ki fam codes prod x
            -> UTxNP ki fam codes (K k ': prod) x

utxGetX :: UTx ki fam codes i x -> [x]
utxGetX utx = go utx []
  where 
    go :: UTx ki fam codes i x -> ([x] -> [x])
    go (UTxHere x) = (x:)
    go (UTxPeel _ xs)  = utxnpGetX xs

    utxnpGetX :: UTxNP ki fam codes prod x -> ([x] -> [x])
    utxnpGetX UTxNPNil = id
    utxnpGetX (UTxNPSolid _ ps) = utxnpGetX ps
    utxnpGetX (UTxNPPath i ps) = go i . utxnpGetX ps 

instance (Show1 ki , Show x) => Show (UTx ki fam codes i x) where
  show (UTxHere x) = "[" ++ show x ++ "]"
  show (UTxPeel c rest) = "(" ++ show c ++ "| " ++ show rest ++ ")"

instance (Show1 ki , Show x) => Show (UTxNP ki fam codes prod x) where
  show UTxNPNil = "Nil"
  show (UTxNPPath p ps) = show p ++ " :* " ++ show ps
  show (UTxNPSolid ki ps) = show1 ki ++ " :* " ++ show ps
