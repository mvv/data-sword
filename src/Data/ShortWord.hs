{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE TypeFamilies #-}

-- | This module provides signed and unsigned binary word data types of sizes
--   2, 3, 4, 5, 6, 7, 24, and 48 bits.
module Data.ShortWord
  ( module Data.BinaryWord
  , Word2
  , Word3
  , Word4
  , Word5
  , Word6
  , Word7
  , Word24
  , Word48
  , Int2
  , Int3
  , Int4
  , Int5
  , Int6
  , Int7
  , Int24
  , Int48
  ) where

import Data.Word
import Data.BinaryWord
import Data.ShortWord.TH

mkShortWord "Word2" "Word2" "Int2" "Int2" ''Word8 2 []
mkShortWord "Word3" "Word3" "Int3" "Int3" ''Word8 3 []
mkShortWord "Word4" "Word4" "Int4" "Int4" ''Word8 4 []
mkShortWord "Word5" "Word5" "Int5" "Int5" ''Word8 5 []
mkShortWord "Word6" "Word6" "Int6" "Int6" ''Word8 6 []
mkShortWord "Word7" "Word7" "Int7" "Int7" ''Word8 7 []
mkShortWord "Word24" "Word24" "Int24" "Int24" ''Word32 24 []
mkShortWord "Word48" "Word48" "Int48" "Int48" ''Word64 48 []
