{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Types where

import Data.Word
import Data.ShortWord.TH

mkShortWord "U16" "U16" "aU16" "I16" "I16" "anI16" ''Word64 16 []
