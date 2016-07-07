{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE TypeFamilies #-}

-- | This module provides signed and unsigned binary word data types of sizes
--   2, 4, 7, 24, and 48 bits.
module Data.ShortWord
  ( module Data.BinaryWord
  , Word2
  , Word4
  , Word7
  , Word24
  , Word48
  , Int2
  , Int4
  , Int7
  , Int24
  , Int48
  ) where

import Data.Typeable
import Data.Word
import Data.BinaryWord
import Data.ShortWord.TH

mkShortWord "Word2" "Word2" "Int2" "Int2" ''Word8 2 [''Typeable]
mkShortWord "Word4" "Word4" "Int4" "Int4" ''Word8 4 [''Typeable]
mkShortWord "Word7" "Word7" "Int7" "Int7" ''Word8 7 [''Typeable]
mkShortWord "Word24" "Word24" "Int24" "Int24" ''Word32 24 [''Typeable]
mkShortWord "Word48" "Word48" "Int48" "Int48" ''Word64 48 [''Typeable]
