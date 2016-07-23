{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

import Test.Tasty (defaultMain, localOption, testGroup)
import Test.Tasty.QuickCheck hiding ((.&.))

import Data.Bits
import Data.Word
import Data.Int
import Data.ShortWord (BinaryWord(..))
import Types

class Iso α τ | τ → α where
  fromArbitrary ∷ α → τ 
  toArbitrary ∷ τ → α
  isValid ∷ τ → Bool

instance Iso Word16 U16 where
  fromArbitrary w = U16 $ fromIntegral w `shiftL` 48
  toArbitrary (U16 w) = fromIntegral $ w `shiftR` 48
  isValid (U16 w) = (w .&. 0xFFFFFFFFFF) == 0

instance Iso Int16 I16 where
  fromArbitrary w = I16 $ fromIntegral w `shiftL` 48
  toArbitrary (I16 w) = fromIntegral $ w `shiftR` 48
  isValid (I16 w) = (w .&. 0xFFFFFFFFFF) == 0

main = defaultMain
     $ localOption (QuickCheckTests 1000)
     $ testGroup "Tests"
         [ isoTestGroup "Word64/16" (0 ∷ U16)
         , isoTestGroup "Int64/16" (0 ∷ I16) ]

isoTestGroup name t =
  testGroup name
    [ testProperty "Iso" $ prop_conv t
    , testGroup "Eq" [ testProperty "(==)" $ prop_eq t ]
    , testGroup "Ord" [ testProperty "compare" $ prop_compare t ]
    , testGroup "Bounded"
        [ testProperty "minBound" $ prop_minBound t
        , testProperty "maxBound" $ prop_maxBound t ]
    , testGroup "Enum"
        [ testProperty "succ" $ prop_succ t
        , testProperty "pred" $ prop_pred t ]
    , testGroup "Num"
        [ testProperty "negate" $ prop_negate t
        , testProperty "abs" $ prop_abs t
        , testProperty "signum" $ prop_signum t
        , testProperty "(+)" $ prop_add t
        , testProperty "(-)" $ prop_sub t
        , testProperty "(*)" $ prop_mul t
        , testProperty "fromInteger" $ prop_fromInteger t ]
    , testGroup "Real"
        [ testProperty "toRational" $ prop_toRational t ]
    , testGroup "Integral"
        [ testProperty "toInteger" $ prop_toInteger t
        , testProperty "quotRem" $ prop_quotRem t
        , testProperty "quot" $ prop_quot t
        , testProperty "rem" $ prop_rem t
        , testProperty "divMod" $ prop_divMod t
        , testProperty "div" $ prop_div t
        , testProperty "mod" $ prop_mod t ]
    , testGroup "Bits"
        [ testProperty "complement" $ prop_complement t
        , testProperty "xor" $ prop_xor t
        , testProperty "(.&.)" $ prop_and t
        , testProperty "(.|.)" $ prop_or t
        , testProperty "shiftL" $ prop_shiftL t
        , testProperty "shiftR" $ prop_shiftR t
        , testProperty "rotateL" $ prop_rotateL t
        , testProperty "rotateR" $ prop_rotateR t
        , testProperty "bit" $ prop_bit t
        , testProperty "setBit" $ prop_setBit t
        , testProperty "clearBit" $ prop_clearBit t
        , testProperty "complementBit" $ prop_complementBit t
        , testProperty "testBit" $ prop_testBit t
        , testProperty "popCount" $ prop_popCount t
        ]
    , testGroup "BinaryWord"
        [ testProperty "unwrappedAdd" $ prop_unwrappedAdd t
        , testProperty "unwrappedMul" $ prop_unwrappedMul t
        , testProperty "leadingZeroes" $ prop_leadingZeroes t
        , testProperty "trailingZeroes" $ prop_trailingZeroes t
        , testProperty "allZeroes" $ prop_allZeroes t
        , testProperty "allOnes" $ prop_allOnes t
        , testProperty "msb" $ prop_msb t
        , testProperty "lsb" $ prop_lsb t
        , testProperty "testMsb" $ prop_testMsb t
        , testProperty "testLsb" $ prop_testLsb t
        ]
    ]

toType ∷ Iso α τ ⇒ τ → α → τ 
toType _ = fromArbitrary

fromType ∷ Iso α τ ⇒ τ → τ → α 
fromType _ = toArbitrary

withUnary ∷ Iso α τ ⇒ τ → (τ → β) → α → β
withUnary _ f = f . fromArbitrary

withBinary ∷ Iso α τ ⇒ τ → (τ → τ → β) → α → α → β
withBinary _ f x y = f (fromArbitrary x) (fromArbitrary y)

propUnary f g t w = isValid r && toArbitrary r == f w
  where r = withUnary t g w
propUnary' f g t w = f w == withUnary t g w

propBinary f g t w1 w2 = isValid r && f w1 w2 == toArbitrary r
  where r = withBinary t g w1 w2
propBinary' f g t w1 w2 = f w1 w2 == withBinary t g w1 w2

prop_conv t w = toArbitrary (toType t w) == w

prop_eq = propBinary' (==) (==)

prop_compare = propBinary' compare compare

prop_minBound t = minBound == fromType t minBound
prop_maxBound t = maxBound == fromType t maxBound

prop_succ t w = (w /= maxBound) ==> (isValid r && succ w == toArbitrary r)
  where r = withUnary t succ w
prop_pred t w = (w /= minBound) ==> (isValid r && pred w == toArbitrary r)
  where r = withUnary t pred w

prop_unwrappedAdd ∷ (Iso α τ, Iso (UnsignedWord α) (UnsignedWord τ),
                     BinaryWord α, BinaryWord τ)
                  ⇒ τ → α → α → Bool
prop_unwrappedAdd t x y = h1 == toArbitrary h2 && l1 == toArbitrary l2
  where (h1, l1) = unwrappedAdd x y
        (h2, l2) = unwrappedAdd (toType t x) (toType t y)

prop_unwrappedMul ∷ (Iso α τ, Iso (UnsignedWord α) (UnsignedWord τ),
                     BinaryWord α, BinaryWord τ)
                  ⇒ τ → α → α → Bool
prop_unwrappedMul t x y = h1 == toArbitrary h2 && l1 == toArbitrary l2
  where (h1, l1) = unwrappedMul x y
        (h2, l2) = unwrappedMul (toType t x) (toType t y)

prop_leadingZeroes = propUnary' leadingZeroes leadingZeroes
prop_trailingZeroes = propUnary' trailingZeroes trailingZeroes
prop_allZeroes t = allZeroes == fromType t allZeroes
prop_allOnes t = allOnes == fromType t allOnes
prop_msb t = msb == fromType t msb
prop_lsb t = lsb == fromType t lsb
prop_testMsb = propUnary' testMsb testMsb
prop_testLsb = propUnary' testLsb testLsb

prop_negate = propUnary negate negate
prop_abs = propUnary abs abs
prop_signum = propUnary signum signum
prop_add = propBinary (+) (+)
prop_sub = propBinary (-) (-)
prop_mul = propBinary (*) (*)
prop_fromInteger t i = fromInteger i == fromType t (fromInteger i) 

prop_toRational = propUnary' toRational toRational

prop_toInteger = propUnary' toInteger toInteger
prop_quotRem t n d = (d /= 0) ==> (qr == (fromType t q1, fromType t r1))
  where qr = quotRem n d
        (q1, r1) = quotRem (fromArbitrary n) (fromArbitrary d)
prop_quot t n d = (d /= 0) ==> (q == fromType t q1)
  where q = quot n d
        q1 = quot (fromArbitrary n) (fromArbitrary d)
prop_rem t n d = (d /= 0) ==> (r == fromType t r1)
  where r = rem n d
        r1 = rem (fromArbitrary n) (fromArbitrary d)
prop_divMod t n d = (d /= 0) ==> (qr == (fromType t q1, fromType t r1))
  where qr = divMod n d
        (q1, r1) = divMod (fromArbitrary n) (fromArbitrary d)
prop_div t n d = (d /= 0) ==> (q == fromType t q1)
  where q = div n d
        q1 = div (fromArbitrary n) (fromArbitrary d)
prop_mod t n d = (d /= 0) ==> (r == fromType t r1)
  where r = mod n d
        r1 = mod (fromArbitrary n) (fromArbitrary d)

prop_complement = propUnary complement complement
prop_xor = propBinary xor xor
prop_and = propBinary (.&.) (.&.)
prop_or = propBinary (.|.) (.|.)
propOffsets f g t w =
  all (\b → let r = withUnary t (`g` b) w in
              isValid r && toArbitrary r == f w b)
      [0 .. finiteBitSize t]
prop_shiftL = propOffsets shiftL shiftL
prop_shiftR = propOffsets shiftR shiftR
prop_rotateL = propOffsets rotateL rotateL
prop_rotateR = propOffsets rotateR rotateR
prop_bit t = all (\b → bit b == fromType t (bit b))
                 [0 .. finiteBitSize t - 1]
propBits f g t w =
  all (\b → let r = withUnary t (`g` b) w in
              isValid r && toArbitrary r == f w b)
      [0 .. finiteBitSize t - 1]
prop_setBit = propBits setBit setBit
prop_clearBit = propBits clearBit clearBit
prop_complementBit = propBits complementBit complementBit
prop_testBit t w =
  all (\b → testBit w b == withUnary t (`testBit` b) w)
      [0 .. finiteBitSize t - 1]
prop_popCount = propUnary' popCount popCount
