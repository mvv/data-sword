{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies #-}

-- | This module provides signed and unsigned binary word data types of sizes
--   2, 3, 4, 5, 6, 7, 24, and 48 bits.
module Data.ShortWord
  ( module Data.BinaryWord
  , Word2
  , aWord2
  , Word3
  , aWord3
  , Word4
  , aWord4
  , Word5
  , aWord5
  , Word6
  , aWord6
  , Word7
  , aWord7
  , Word24
  , aWord24
  , Word48
  , aWord48
  , Int2
  , anInt2
  , Int3
  , anInt3
  , Int4
  , anInt4
  , Int5
  , anInt5
  , Int6
  , anInt6
  , Int7
  , anInt7
  , Int24
  , anInt24
  , Int48
  , anInt48
  ) where

import Data.Word
import Data.BinaryWord
import Data.ShortWord.TH

mkShortWord "Word2" "Word2" "aWord2" "Int2" "Int2" "anInt2" ''Word8 2 []
mkShortWord "Word3" "Word3" "aWord3" "Int3" "Int3" "anInt3" ''Word8 3 []
mkShortWord "Word4" "Word4" "aWord4" "Int4" "Int4" "anInt4" ''Word8 4 []
mkShortWord "Word5" "Word5" "aWord5" "Int5" "Int5" "anInt5" ''Word8 5 []
mkShortWord "Word6" "Word6" "aWord6" "Int6" "Int6" "anInt6" ''Word8 6 []
mkShortWord "Word7" "Word7" "aWord7" "Int7" "Int7" "anInt7" ''Word8 7 []
mkShortWord "Word24" "Word24" "aWord24" "Int24" "Int24" "anInt24"
            ''Word32 24 []
mkShortWord "Word48" "Word48" "aWord48" "Int48" "Int48" "anInt48"
            ''Word64 48 []
