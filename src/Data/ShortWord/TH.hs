{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Template Haskell utilities for generating short words declarations
module Data.ShortWord.TH
  ( mkShortWord
  ) where

import GHC.Arr (Ix(..))
import GHC.Enum (succError, predError, toEnumError)
import Data.Data
import Data.Proxy (Proxy(..))
import Data.Ratio ((%))
import Data.Bits (Bits(..))
import Data.Bits (FiniteBits(..))
#if MIN_VERSION_hashable(1,2,0)
import Data.Hashable (Hashable(..), hashWithSalt)
#else
import Data.Hashable (Hashable(..), combine)
#endif
import Data.Char (toLower)
import Data.List (union)
import Control.Applicative ((<$>), (<*>))
import Language.Haskell.TH
import Language.Haskell.TH.Syntax (Module(..), ModName(..))
import Data.BinaryWord (BinaryWord(..))

-- | Declare signed and unsigned binary word types that use a subset
--   of the bits of the specified underlying type. For each data type
--   the following instances are declared: 'Typeable', 'Data', 'Eq', 'Ord',
--   'Bounded', 'Enum', 'Num', 'Real', 'Integral', 'Show', 'Read',
--   'Hashable', 'Ix', 'Bits', 'BinaryWord'.
mkShortWord ∷ String -- ^ Unsigned variant type name
            → String -- ^ Unsigned variant constructor name
            → String -- ^ Unsigned variant proxy name
            → String -- ^ Signed variant type name
            → String -- ^ Signed variant constructor name
            → String -- ^ Signed variant proxy name
            → Name   -- ^ The underlying (unsigned) type
            → Int    -- ^ The bit length
            → [Name] -- ^ List of instances for automatic derivation
            → Q [Dec]
mkShortWord un uc upn sn sc spn utp bl ad =
    (++) <$> mkShortWord' False un' uc' upn' sn' sc' utp bl ad
         <*> mkShortWord' True  sn' sc' spn' un' uc' utp bl ad
  where un'  = mkName un
        uc'  = mkName uc
        upn' = mkName upn
        sn'  = mkName sn
        sc'  = mkName sc
        spn' = mkName spn

mkShortWord' ∷ Bool
             → Name → Name
             → Name
             → Name → Name
             → Name
             → Int
             → [Name]
             → Q [Dec]
mkShortWord' signed tp cn pn otp ocn utp bl ad = returnDecls $
    [ NewtypeD [] tp []
#if MIN_VERSION_template_haskell(2,11,0)
               Nothing
               (NormalC cn [(Bang NoSourceUnpackedness
                                  NoSourceStrictness,
                             uT)])
# if MIN_VERSION_template_haskell(2,12,0)
               [DerivClause Nothing (ConT <$> union [''Typeable] ad)]
# else
               (ConT <$> union [''Typeable] ad)
# endif
#else
               (NormalC cn [(NotStrict, uT)])
               (union [''Typeable] ad)
#endif
    , SigD pn (AppT (ConT ''Proxy) tpT)
    , fun pn $ ConE 'Proxy
    , inst ''Eq [tp] $
        {- (W x) == (W y) = x == y -}
        [ funUn2 '(==) $ appVN '(==) [x, y]
        , inline '(==) ]
    , inst ''Ord [tp]
        {- compare (W x) (W y) = x `compare` y -}
        [ funUn2 'compare $ appVN 'compare [x, y]
        , inline 'compare ]
    , inst ''Bounded [tp]
        {- minBound = W (minBound .&. MASK) -}
        [ fun 'minBound $ appW $ appV '(.&.) [VarE 'minBound, maskE]
        , inline 'minBound
        {- maxBound = W (maxBound .&. MASK) -}
        , fun 'maxBound $ appW $ appV '(.&.) [VarE 'maxBound, maskE]
        , inline 'maxBound ]
    , inst ''Enum [tp]
        {-
          succ x@(W y) = if x == maxBound then succError "TYPE"
                                          else W (y + shiftL 1 SHIFT)
        -}
        [ funUnAsX 'succ $
            CondE (appVN '(==) [x, 'maxBound])
                  (appV 'succError [litS (show tp)])
                  (appW (appV '(+) [VarE y, appV 'shiftL [litI 1, shiftE]]))
        , inlinable 'succ
        {-
          pred x@(W y) = if x == minBound then predError "TYPE"
                                          else W (y - shiftL 1 SHIFT)
        -}
        , funUnAsX 'pred $
            CondE (appVN '(==) [x, 'minBound])
                  (appV 'predError [litS (show tp)])
                  (appW (appV '(-) [VarE y, appV 'shiftL [litI 1, shiftE]]))
        , inlinable 'pred
        {-
          toEnum x = if y < shiftR minBound SHIFT || y > shiftR maxBound SHIFT
                     then toEnumError "TYPE" x [minBound ∷ TYPE, maxBound ∷ TYPE]
                     else W (shiftL y SHIFT)
            where y = toEnum x
        -}
        , funX' 'toEnum
            (CondE (appV '(||) [ appV '(<) [ VarE y
                                           , appV 'shiftR
                                                  [VarE 'minBound, shiftE]
                                           ]
                               , appV '(>) [ VarE y
                                           , appV 'shiftR
                                                  [VarE 'maxBound, shiftE]
                                           ]
                               ])
                   (appV 'toEnumError [ litS (show tp)
                                      , VarE x
                                      , TupE [ SigE (VarE 'minBound) tpT
                                             , SigE (VarE 'maxBound) tpT
                                             ]
                                      ])
                   (appW $ appV 'shiftL [VarE y, shiftE]))
            [val y $ appVN 'toEnum [x]]
        {- fromEnum (W x) = fromEnum (shiftR x SHIFT) -}
        , funUn 'fromEnum $ appV 'fromEnum [appV 'shiftR [VarE x, shiftE]]
        , inline 'fromEnum
        {- enumFrom x = enumFromTo x maxBound -}
        , funX 'enumFrom $ appVN 'enumFromTo [x, 'maxBound]
        , inline 'enumFrom
        {- 
          enumFromThen x y =
            enumFromThenTo x y $ if y >= x then maxBound else minBound 
        -}
        , funXY 'enumFromThen $
            appV 'enumFromThenTo
              [ VarE x
              , VarE y
              , CondE (appVN '(>=) [x, y]) (VarE 'maxBound) (VarE 'minBound)
              ]
        , inlinable 'enumFromThen
        {-
          enumFromTo x y = case y `compare` x of
              LT → x : down y x
              EQ → [x]
              GT → x : up y x
            where down to c = next : if next == to then [] else down to next
                    where next = c - 1
                  up to c = next : if next == to then [] else up to next
                    where next = c + 1 
        -}
        , FunD 'enumFromTo $ return $
            Clause
              [VarP x, VarP y]
              (NormalB $
                 CaseE (appVN 'compare [y, x])
                   [ Match
                       (ConP 'LT [])
                       (NormalB $ appC '(:) [VarE x, appVN down [y, x]])
                       []
                   , Match
                       (ConP 'EQ [])
                       (NormalB $ appC '(:) [VarE x, ConE '[]])
                       []
                   , Match
                       (ConP 'GT [])
                       (NormalB $ appC '(:) [VarE x, appVN up [y, x]])
                       []
                   ])
              [ FunD down $ return $
                  Clause [VarP to, VarP c]
                    (NormalB $
                       appC '(:)
                         [ VarE next
                         , CondE (appVN '(==) [next, to])
                                 (ConE '[]) (appVN down [to, next])
                         ])
                    [ValD (VarP next)
                          (NormalB $ appVN '(-) [c, 'lsb]) []]
              , FunD up $ return $
                  Clause [VarP to, VarP c]
                    (NormalB $
                       appC '(:)
                         [ VarE next
                         , CondE (appVN '(==) [next, to])
                                 (ConE '[]) (appVN up [to, next])
                         ])
                    [ValD (VarP next)
                          (NormalB $ appVN '(+) [c, 'lsb]) []]
              ]
        {-
          enumFromThenTo x y z = case y `compare` x of 
              LT → if z > x then [] else down (x - y) z x
              EQ → repeat x
              GT → if z < x then [] else up (y - x) z x
            where down s to c = c : if next < to then [] else down s to next
                    where next = c - s
                  up s to c = c : if next > to then [] else up s to next
                    where next = c + s 
        -}
        , FunD 'enumFromThenTo $ return $
            Clause [VarP x, VarP y, VarP z]
              (NormalB $
                CaseE (appVN 'compare [y, x])
                  [ Match
                      (ConP 'LT [])
                      (NormalB $
                         CondE (appVN '(>) [z, x])
                               (ConE '[])
                               (appV down [appVN '(-) [x, y], VarE z, VarE x]))
                      []
                  , Match (ConP 'EQ []) (NormalB $ appVN 'repeat [x]) []
                  , Match
                      (ConP 'GT [])
                      (NormalB $
                         CondE (appVN '(<) [z, x]) (ConE '[])
                               (appV up [appVN '(-) [y, x], VarE z, VarE x]))
                      []
                  ])
              [ FunD down $ return $
                  Clause [VarP step, VarP to, VarP c]
                    (NormalB $
                       appC '(:)
                         [ VarE c
                         , CondE (appVN '(<) [next, to])
                                 (ConE '[]) (appVN down [step, to, next])
                         ])
                    [ValD (VarP next) (NormalB $ appVN '(-) [c, step]) []]
              , FunD up $ return $
                  Clause [VarP step, VarP to, VarP c]
                    (NormalB $
                       appC '(:)
                         [ VarE c
                         , CondE (appVN '(==) [next, to])
                                 (ConE '[]) (appVN up [step, to, next])
                         ])
                    [ValD (VarP next) (NormalB $ appVN '(+) [c, step]) []]]
        ]
    , inst ''Num [tp]
        {- negate (W x) = W (negate x) -}
        [ funUn 'negate $ appW $ appVN 'negate [x]
        , inline 'negate
        {- 
          abs x@(W y) = if SIGNED
                        then if y < 0 then W (negate y) else x 
                        else x
        -}
        , if signed
          then funUnAsX 'abs $
                 CondE (appVN '(<) [y, 'allZeroes])
                       (appW $ appVN 'negate [y]) (VarE x)
          else funX 'abs $ VarE x
        , if signed then inlinable 'abs else inline 'abs
        {- signum (W x) = W (shiftL (signum x) SHIFT) -}
        , funUn 'signum $ appW $ appV 'shiftL [appVN 'signum [x], shiftE]
        , inline 'signum
        {- (W x) + (W y) = W (x + y) -}
        , funUn2 '(+) $ appW $ appVN '(+) [x, y]
        , inline '(+)
        {- (W x) * (W y) = W (shiftR x SHIFT * y) -}
        , funUn2 '(*) $
            appW $ appV '(*) [appV 'shiftR [VarE x, shiftE], VarE y]
        , inline '(*)
        {- fromInteger x = W (shiftL (fromInteger x) SHIFT) -}
        , funX 'fromInteger $
            appW $ appV 'shiftL [appVN 'fromInteger [x], shiftE]
        , inline 'fromInteger
        ]
    , inst ''Real [tp]
        {- toRational x = toInteger x % 1 -}
        [ funX 'toRational $ appV '(%) [appVN 'toInteger [x], litI 1]
        , inline 'toRational ]
    , inst ''Integral [tp] $
        {- toInteger (W x) = toInteger (shiftR x SHIFT) -}
        [ funUn 'toInteger $ appV 'toInteger [appV 'shiftR [VarE x, shiftE]]
        , inline 'toInteger
        {-
           quotRem (W x) (W y) = (W (shiftL q SHIFT), W r)
             where (q, r) = quotRem x y
        -}
        , funUn2' 'quotRem
            (TupE [appW (appV 'shiftL [VarE q, shiftE]), appWN r])
            [vals [q, r] $ appVN 'quotRem [x, y]]
        , inline 'quotRem
        {-
           divMod (W x) (W y) = (W (shiftL q SHIFT), W r)
             where (q, r) = divMod x y
        -}
        , funUn2' 'divMod
            (TupE [appW (appV 'shiftL [VarE q, shiftE]), appWN r])
            [vals [q, r] $ appVN 'divMod [x, y]]
        , inline 'divMod
        ]
    , inst ''Show [tp]
        [ {- show (W x) = show (shiftR x SHIFT) -}
          funUn 'show $ appV 'show [appV 'shiftR [VarE x, shiftE]]
        , inline 'show ]
    , inst ''Read [tp]
        {-
          readsPrec x y = fmap (\(q, r) → (fromInteger q, r))
                        $ readsPrec x y
        -}
        [ funXY 'readsPrec $
            appV 'fmap [ LamE [TupP [VarP q, VarP r]]
                              (TupE [appVN 'fromInteger [q], VarE r])
                       , appVN 'readsPrec [x, y] ]
        ]
    , inst ''Hashable [tp]
#if MIN_VERSION_hashable(1,2,0)
        {- hashWithSalt x (W y) = x `hashWithSalt` y -}
        [ funXUn 'hashWithSalt $ appVN 'hashWithSalt [x, y]
#else
        {- hash (W x) = hash x -}
        [ funUn 'hash $ appVN 'hash [x]
        , inline 'hash
#endif
        , inline 'hashWithSalt ]
    , inst ''Ix [tp]
        {- range (x, y) = enumFromTo x y -}
        [ funTup 'range $ appVN 'enumFromTo [x, y]
        , inline 'range
        {- unsafeIndex (x, _) z = fromIntegral z - fromIntegral x -}
        , funTupLZ 'unsafeIndex $
            appV '(-) [appVN 'fromIntegral [z], appVN 'fromIntegral [x]]
        , inline 'unsafeIndex
        {- inRange (x, y) z = z >= x && z <= y -}
        , funTupZ 'inRange $
            appV '(&&) [appVN '(>=) [z, x], appVN '(<=) [z, y]]
        , inline 'inRange ]
    , inst ''Bits [tp] $
        {- bitSize _ = SIZE -}
        [ fun_ 'bitSize $ sizeE
        , inline 'bitSize
        {- bitSizeMaybe _ = Just SIZE -}
        , fun_ 'bitSizeMaybe $ app (ConE 'Just) [sizeE]
        , inline 'bitSizeMaybe
        {- isSigned _ = SIGNED -}
        , fun_ 'isSigned $ ConE $ if signed then 'True else 'False
        , inline 'isSigned
        {- complement (W x) = W (complement x .&. MASK) -}
        , funUn 'complement $
            appW $ appV '(.&.) [appVN 'complement [x], maskE]
        , inline 'complement
        {- xor (W x) (W y) = W (xor x y) -}
        , funUn2 'xor $ appW $ appVN 'xor [x, y]
        , inline 'xor
        {- (W x) .&. (W y) = W (x .&. y) -}
        , funUn2 '(.&.) $ appW $ appVN '(.&.) [x, y]
        , inline '(.&.)
        {- (W x) .|. (W y) = W (x .|. y) -}
        , funUn2 '(.|.) $ appW $ appVN '(.|.) [x, y]
        , inline '(.|.)
        {- shiftL (W x) y = W (shiftL x y) -}
        , funUnY 'shiftL $ appW $ appVN 'shiftL [x, y]
        , inline 'shiftL
        {- shiftR (W x) y = W (shiftR x y .&. MASK) -}
        , funUnY 'shiftR $ appW $ appV '(.&.) [appVN 'shiftR [x, y], maskE]
        , inline 'shiftR
        {-
           UNSIGNED:
             rotateL (W x) y = W (shiftL x y .|.
                                  (shiftR x (SIZE - y) .&. MASK))

           SIGNED:
             rotateL (W x) y =
               W (shiftL x y .|.
                  (signedWord (shiftR (unsignedWord x) (SIZE - y)) .&.
                   MASK))
        -}
        , funUnY 'rotateL $ appW $ appV '(.|.) $ (appVN 'shiftL [x, y] :) $
            return $ appV '(.&.) $
              [ if signed
                then appV 'signedWord [ appV 'shiftR
                                             [ appVN 'unsignedWord [x]
                                             , appV '(-) [sizeE, VarE y]
                                             ]
                                      ]
                else appV 'shiftR [VarE x, appV '(-) [sizeE, VarE y]]
              , maskE
              ]
        , inline 'rotateL
        {- rotateR x y = rotateL x (SIZE - y) -}
        , funXY 'rotateR $ appV 'rotateL [VarE x, appV '(-) [sizeE, VarE y]]
        , inline 'rotateR
        {- bit x = W (bit (x + SHIFT)) -}
        , funX 'bit $ appW $ appV 'bit [appV '(+) [VarE x, shiftE]]
        , inline 'bit
        {- setBit (W x) y = W (setBit x (y + SHIFT)) -}
        , funUnY 'setBit $
            appW $ appV 'setBit [VarE x, appV '(+) [VarE y, shiftE]]
        , inline 'setBit
        {- clearBit (W x) y = W (clearBit x (y + SHIFT)) -}
        , funUnY 'clearBit $
            appW $ appV 'clearBit [VarE x, appV '(+) [VarE y, shiftE]]
        , inline 'clearBit
        {- complementBit (W x) y = W (complementBit x (y + SHIFT)) -}
        , funUnY 'complementBit $
            appW $ appV 'complementBit [VarE x, appV '(+) [VarE y, shiftE]]
        , inline 'complementBit
        {- testBit (W x) y = testBit x (y + SHIFT) -}
        , funUnY 'testBit $ appV 'testBit [VarE x, appV '(+) [VarE y, shiftE]]
        , inline 'testBit
        {- popCount (W x) = popCount x -}
        , funUn 'popCount $ appVN 'popCount [x]
        , inline 'popCount
        ]
    , inst ''FiniteBits [tp]
        {- finiteBitSize _ = SIZE -}
        [ fun_ 'finiteBitSize $ sizeE
        , inline 'finiteBitSize
# if MIN_VERSION_base(4,8,0)
        {- countLeadingZeros = leadingZeroes -}
        , fun 'countLeadingZeros $ VarE 'leadingZeroes
        , inline 'countLeadingZeros
        {- countTrailingZeros = trailingZeroes -}
        , fun 'countTrailingZeros $ VarE 'trailingZeroes
        , inline 'countTrailingZeros
# endif
        ]
    , inst ''BinaryWord [tp]
        [ tySynInst ''UnsignedWord [tpT] $
            ConT $ if signed then otp else tp
        , tySynInst ''SignedWord [tpT] $
            ConT $ if signed then tp else otp
        {-
          UNSIGNED:
            unsignedWord = id
          
          SIGNED:
            unsignedWord (W x) = U (unsignedWord x)
        -}
        , if signed
          then funUn 'unsignedWord $ appC ocn [appVN 'unsignedWord [x]]
          else fun 'unsignedWord $ VarE 'id
        , inline 'unsignedWord
        {-
          UNSIGNED:
            signedWord (W x) = S (signedWord hi)
          
          SIGNED:
            signedWord = id
        -}
        , if signed
          then fun 'signedWord $ VarE 'id
          else funUn 'signedWord $ appC ocn [appVN 'signedWord [x]]
        , inline 'signedWord
        {-
          unwrappedAdd (W x) (W y) = (W (shiftL t1 SHIFT),
                                      U (unsignedWord t2))
            where (t1, t2) = unwrappedAdd x y
        -}
        , funUn2' 'unwrappedAdd
            (TupE [ appW (appV 'shiftL [VarE t1, shiftE])
                  , appC (if signed then ocn else cn)
                         [appVN 'unsignedWord [t2]]
                  ])
            [vals [t1, t2] $ appVN 'unwrappedAdd [x, y]]
        , inline 'unwrappedAdd
        {-
          unwrappedMul (W x) (W y) = (W (shiftL t1 SHIFT),
                                      U (unsignedWord t2))
            where (t1, t2) = unwrappedMul (shiftR x SHIFT) y
        -}
        , funUn2' 'unwrappedMul
            (TupE [ appW (appV 'shiftL [VarE t1, shiftE])
                  , appC (if signed then ocn else cn)
                         [appVN 'unsignedWord [t2]]
                  ])
            [vals [t1, t2] $
               appV 'unwrappedMul [appV 'shiftR [VarE x, shiftE], VarE y]]
        , inline 'unwrappedMul
        {- leadingZeroes (W x) = leadingZeroes (x .|. complement MASK) -}
        , funUn 'leadingZeroes $
            appV 'leadingZeroes [appV '(.|.)
                                      [VarE x, appV 'complement [maskE]]]
        , inline 'leadingZeroes
        {- trailingZeroes (W x) = trailingZeroes x - SHIFT -}
        , funUn 'trailingZeroes $
            appV '(-) [appVN 'trailingZeroes [x], shiftE]
        , inline 'trailingZeroes
        {- allZeroes = W allZeroes -}
        , fun 'allZeroes $ appWN 'allZeroes
        , inline 'allZeroes
        {- allOnes = W (allOnes .&. MASK) -}
        , fun 'allOnes $ appW $ appV '(.&.) [VarE 'allOnes, maskE]
        , inline 'allOnes
        {- msb = W msb -}
        , fun 'msb $ appWN 'msb
        , inline 'msb
        {- lsb = W (shiftL lsb SHIFT) -}
        , fun 'lsb $ appW $ appV 'shiftL [VarE 'lsb, shiftE]
        , inline 'lsb
        {- testMsb (W x) = testMsb x -}
        , funUn 'testMsb $ appVN 'testMsb [x]
        , inline 'testMsb
        {- testLsb (W x) = testBit x SHIFT -}
        , funUn 'testLsb $ appV 'testBit [VarE x, shiftE]
        , inline 'testLsb
        {- setMsb (W x) = W (setMsb x) -}
        , funUn 'setMsb $ appW $ appVN 'setMsb [x]
        , inline 'setMsb
        {- setLsb (W x) = W (setBit x SHIFT) -}
        , funUn 'setLsb $ appW $ appV 'setBit [VarE x, shiftE]
        , inline 'setLsb
        {- clearMsb (W x) = W (clearMsb x) -}
        , funUn 'clearMsb $ appW $ appVN 'clearMsb [x]
        , inline 'clearMsb
        {- clearLsb (W x) = W (clearBit x SHIFT) -}
        , funUn 'clearLsb $ appW $ appV 'clearBit [VarE x, shiftE]
        , inline 'clearLsb
        ]
    , rule ("fromIntegral/" ++ show tp ++ "->" ++ show tp)
           (VarE 'fromIntegral)
           (SigE (VarE 'id) (AppT (AppT ArrowT tpT) tpT))
    , rule ("fromIntegral/" ++ show tp ++ "->" ++ show otp)
           (VarE 'fromIntegral)
           (SigE (VarE $ if signed then 'unsignedWord else 'signedWord)
                 (AppT (AppT ArrowT tpT) (ConT otp)))
    , rule ("fromIntegral/" ++ show tp ++ "->a")
           (VarE 'fromIntegral)
           (LetE [funUn fn $ appV 'fromIntegral
                                  [appV 'shiftR [VarE x, shiftE]]]
                 (VarE fn))
    , rule ("fromIntegral/a->" ++ show tp)
           (VarE 'fromIntegral)
           (appV '(.) [ appV '(.) [ ConE tp
                                  , appV 'flip [VarE 'shiftL, shiftE] ]
                      , VarE 'fromIntegral ])
    ]
  where
    x    = mkName "x"
    y    = mkName "y"
    z    = mkName "z"
    q    = mkName "q"
    r    = mkName "r"
    t1   = mkName "t1"
    t2   = mkName "t2"
    c    = mkName "c"
    next = mkName "next_"
    step = mkName "step_"
    to   = mkName "to_"
    down = mkName "down_"
    up   = mkName "up_"
    fn   = mkName "fn_"
    uT   | signed    = AppT (ConT ''SignedWord) (ConT utp)
         | otherwise = AppT (ConT ''UnsignedWord) (ConT utp)
    tpT  = ConT tp
    tySynInst n ps t =
#if MIN_VERSION_template_haskell(2,9,0)
      TySynInstD n (TySynEqn ps t)
#else
      TySynInstD n ps t
#endif
    inst cls params = InstanceD 
#if MIN_VERSION_template_haskell(2,11,0)
                                Nothing
#endif
                                [] (foldl AppT (ConT cls) (ConT <$> params))
    fun n e        = FunD n [Clause [] (NormalB e) []]
    fun_ n e       = FunD n [Clause [WildP] (NormalB e) []]
    funUn' n e ds  =
      FunD n [Clause [ConP cn [VarP x]] (NormalB e) ds]
    funUn n e      = funUn' n e []
    funUnAsX' n e ds = FunD n [Clause [AsP x (ConP cn [VarP y])]
                                      (NormalB e) ds]
    funUnAsX n e     = funUnAsX' n e []
    funUn2' n e ds =
      FunD n [Clause [ConP cn [VarP x], ConP cn [VarP y]] (NormalB e) ds]
    funUn2 n e     = funUn2' n e []
    funXUn' n e ds =
      FunD n [Clause [VarP x, ConP cn [VarP y]] (NormalB e) ds]
    funXUn n e     = funXUn' n e []
    funUnY' n e ds =
      FunD n [Clause [ConP cn [VarP x], VarP y] (NormalB e) ds]
    funUnY n e     = funUnY' n e []
    funX' n e ds   = FunD n [Clause [VarP x] (NormalB e) ds]
    funX n e       = funX' n e []
    funXY' n e ds  = FunD n [Clause [VarP x, VarP y] (NormalB e) ds]
    funXY n e      = funXY' n e []
    funTup n e     = FunD n [Clause [TupP [VarP x, VarP y]] (NormalB e) []]
    funTupZ n e    =
      FunD n [Clause [TupP [VarP x, VarP y], VarP z] (NormalB e) []]
    funTupLZ n e   =
      FunD n [Clause [TupP [VarP x, WildP], VarP z] (NormalB e) []]
    fun_ZC n e     = FunD n [Clause [WildP, VarP z, VarP c] (NormalB e) []]
    inline n = PragmaD $ InlineP n Inline FunLike AllPhases
    inlinable n = PragmaD $ InlineP n Inlinable FunLike AllPhases
    rule n m e = PragmaD $ RuleP n [] m e AllPhases
    val n e   = ValD (VarP n) (NormalB e) []
    vals ns e = ValD (TupP (VarP <$> ns)) (NormalB e) []
    app f   = foldl AppE f
    appN f  = app f . fmap VarE
    appV f  = app (VarE f)
    appC f  = app (ConE f)
    appW e  = appC cn [e]
    appVN f = appN (VarE f)
    appCN f = appN (ConE f)
    appWN e = appCN cn [e]
    litI = LitE . IntegerL
    litS = LitE . StringL
    sizeE = litI $ toInteger bl
    shiftE = appV '(-)
               [ appV 'finiteBitSize [SigE (VarE 'undefined) uT]
               , sizeE ]
    maskE = appV 'shiftL [VarE 'allOnes, shiftE]
    returnDecls ds = do
      Module _ (ModName modName) ← thisModule
      let typeVar = mkName $ uncapitalize (show tp) ++ "Type"
            where uncapitalize (h : t) = toLower h : t
                  uncapitalize []      = []
          fullName = modName ++ "." ++ show tp
      return $ (ds ++) $
        {- TYPEType ∷ DataType -}
        [ SigD typeVar (ConT ''DataType)
        {- TYPEType = mkIntType TYPE -}
        , fun typeVar $ appV 'mkIntType [litS fullName]
        , inst ''Data [tp] $
            {- toConstr = mkIntegralConstr TYPE -}
            [ fun 'toConstr $ appVN 'mkIntegralConstr [typeVar]
            {-
               gunfold _ z c = case constRep c of
                                 IntConstr x → z (fromIntegral x)
                                 _ → error $ "Data.Data.gunfold: Constructor" ++
                                             show c ++ " is not of type " ++
                                             fullName
            -}
            , fun_ZC 'gunfold $ CaseE (appVN 'constrRep [c]) $
                [ Match (ConP 'IntConstr [VarP x])
                        (NormalB $ appV z [appVN 'fromIntegral [x]])
                        []
                , Match WildP
                        (NormalB $
                           appV 'error
                                [appV '(++)
                                      [ litS "Data.Data.gunfold: Constructor"
                                      , appV '(++)
                                             [ appVN 'show [c]
                                             , appV '(++)
                                                    [ litS " is not of type "
                                                    , litS fullName ]
                                             ]
                                      ]
                                ])
                        []
                ]
            {- dataTypeOf _ = TYPEType -}
            , fun_ 'dataTypeOf $ VarE typeVar
            ]
        ]
