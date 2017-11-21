module TreeGrammar where

type FSymbol = String

data NonTerm
  = NamedNonTerm String
  | NumberedNonTerm Integer
  deriving (Eq, Ord, Show)

data Production = Prod
  { prodFrom :: NonTerm
  , prodSymb :: FSymbol
  , prodTo :: [NonTerm]
  } deriving (Eq, Ord, Show)

data TreeGrammar = Grammar
  { alphabet :: [FSymbol]
  , startSymbols :: [NonTerm]
  , productions :: [Production]
  }
