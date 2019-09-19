-- | 
-- Module      : Language.Go.Parser
-- Copyright   : (c) 2011 Andrew Robbins
-- License     : GPLv3 (see COPYING)
--
-- This module contains analysis functions that parse Go source code into an
-- abstract syntax tree (AST). For more information, see one of the submodules.

module Languages.Go.Parser where
import Languages.Go.Parser.Lexer
import Languages.Go.Parser.Parser
import Languages.Go.Parser.Tokens
