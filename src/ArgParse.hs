module ArgParse where

import Data.Semigroup ((<>))
import Options.Applicative

data Options = Options
  { inFile :: String
  , verbose :: Bool
  , solver :: String
  , example :: Bool
  , getModel :: Bool
  , parseBanshee :: Bool
  }

sample :: Parser Options
sample =
  Options <$>
  strOption
    (long "infile" <> metavar "FILE" <> help "File to read set-constraints from") <*>
  switch (long "verbose" <> short 'v' <> help "Whether to log SMT output") <*>
  strOption (long "solver" <> metavar "STRING" <> help "SMT solver to use") <*>
  switch
    (long "example" <> short 'e' <> help "Print an example satisfiable member") <*>
  switch
    (long "getModel" <> short 'm' <>
     help "Get the tree grammars for each variable") <*>
  switch
    (long "banshee" <> short 'b' <>
     help
       "Parse the given input file as output from Banshee's Andersen analysis")
