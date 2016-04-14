{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE ExplicitNamespaces   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
-- |
-- License    :  BSD3
-- Maintainer :  Oleg Grenrus <oleg.grenrus@iki.fi>
--
-- Symbolic differentiation.
module Math.Symbolic (
    -- * Synopsis
    -- |
    --
    -- /Mathematica/:
    --
    -- @
    -- In[1]: D[x Exp[y y], y]
    -- Out[1]: 2 E^y^2 x y
    --
    -- In[2] % \/. {x -> 3, y -> 2} \/\/ N
    -- Out[2]: 655.178
    -- @
    --
    -- "Math.SD":
    --
    -- @
    -- λ Math.SD > let { x = Proxy :: Proxy "x"; y = Proxy :: Proxy "y" }
    --             in toDouble $ subst x 3 $ subst y 2 $ diff y $ Var x * (exp $ Var y ^ (2 :: Int))
    -- 655.1778003977308
    --
    -- λ Math.SD > let { x = Proxy :: Proxy "x"; y = Proxy :: Proxy "y"; vars = K 3 :* K 2 :* Nil :: NP (K Double) '["x", "y"] }
    --             in toDouble $ substAll vars $ diff y $ var x * (exp $ var y ^ (2 :: Int))
    -- 655.1778003977308
    -- @

    -- * API
    Expr(..),
    var,
    diff,
    partials,
    subst,
    substAll,
    toDouble,

    -- * generics-sop re-exports
    NP(..),
    K(..),
    All,

    -- * Helpers
    InSymbolList,
    InSymbolListF,
    ) where

import Prelude hiding (sum)

import Data.List.NonEmpty (NonEmpty (..))
import Data.Proxy         (Proxy (..))
import Data.Ratio         (numerator, denominator)
import Data.Type.Bool     (type (||))
import Data.Type.Equality (type (==), type (:~:)(..))
import GHC.TypeLits       (KnownSymbol, Symbol, symbolVal)
import Generics.SOP       (NP(..), K(..), All, SList(..), SListI(..))

import qualified Data.List.NonEmpty as NE
import qualified Data.Monoid        as Monoid (Product (..), Sum (..))

import Unsafe.Coerce (unsafeCoerce)

-------------------------------------------------------------------------------
-- Expr
-------------------------------------------------------------------------------

data UnaryFn = Recip | Exp | Sin | Cos
  deriving (Eq, Ord, Show, Enum, Bounded)

unary :: Floating a => UnaryFn -> a -> a
unary Recip = recip
unary Exp   = exp
unary Sin   = sin
unary Cos   = cos

-- | Abstract representation of differentiable expressions.
data Expr (vs :: [Symbol]) a where
    Var   :: InSymbolList v vs => Proxy v -> Expr vs a
    Int   :: Integer -> Expr vs a
    Lit   :: a -> Expr vs a
    Sum   :: NonEmpty (Expr vs a) -> Expr vs a
    Prod  :: NonEmpty (Expr vs a) -> Expr vs a
    Unary :: UnaryFn -> Expr vs a -> Expr vs a

deriving instance Show a => Show (Expr vs a)

instance Num a => Num (Expr vs a) where
    abs = error "abs @Expr is not differentiable"
    signum = error "signum @Expr is not differntiable"
    fromInteger = Int

    negate e = Int (-1) * e

    a + b = sum (a :| [b])
    a * b = prod (a :| [b])

-- |
-- @
-- let x = Proxy :: Proxy "x" in diff x $ recip $ var x :: Expr '["x"] Double
-- @
instance Fractional a => Fractional (Expr vs a) where
    recip (Lit e)         = Lit $ recip e
    recip (Unary Recip e) = e
    recip e               = Unary Recip e

    fromRational r = fromInteger (numerator r) / fromInteger (denominator r)

unaryImpl :: Floating a => UnaryFn -> Expr vs a -> Expr vs a
unaryImpl f (Lit e) = Lit $ unary f e
unaryImpl f e       = Unary f e

instance Floating a => Floating (Expr vs a) where
    pi = Lit pi
    exp = unaryImpl Exp
    sin = unaryImpl Sin
    cos = unaryImpl Cos

    log = error "log @Expr is not supported"
    sqrt = error "sqrt @Expr is not supported"

    asin = error "asin @Expr is not supported"
    acos = error "acos @Expr is not supported"
    atan = error "atan @Expr is not supported"

    sinh = error "sinh @Expr is not supported"
    cosh = error "cosh @Expr is not supported"

    asinh = error "asinh @Expr is not supported"
    acosh = error "acosh @Expr is not supported"
    atanh = error "atanh @Expr is not supported"

-- | Smart constructor for 'Var'.
var :: forall v vs a. InSymbolList v vs => Proxy v -> Expr vs a
var _ = Var (Proxy :: Proxy v)

isZero :: Expr vs a -> Bool
isZero (Int 0) = True
isZero _       = False

isOne :: Expr vs a -> Bool
isOne (Int 1) = True
isOne _       = False

sum :: NonEmpty (Expr vs a) -> Expr vs a
sum (e :| []) = e
sum es =
    case NE.filter (not . isZero) (flattenSum es) of
        []        -> Int 0
        [x]       -> x
        (x : xs)  -> Sum (x :| xs)

flattenSum :: NonEmpty (Expr vs a) -> NonEmpty (Expr vs a)
flattenSum = (>>= f)
  where
    f (Sum es) = es
    f e        = pure e

prod :: NonEmpty (Expr vs a) -> Expr vs a
prod (e :| []) = e
prod es
    | any isZero es = Int 0
    | otherwise     = case NE.filter (not . isOne) (flattenProd es) of
        []        -> Int 1
        [x]       -> x
        (x : xs)  -> Prod (x :| xs)

flattenProd :: NonEmpty (Expr vs a) -> NonEmpty (Expr vs a)
flattenProd= (>>= f)
  where
    f (Prod es) = es
    f e         = pure e

-------------------------------------------------------------------------------
-- Differentiation
-------------------------------------------------------------------------------

-- | The `diff` function symbolically calculates the first derivative of an `Expr`. 
diff
    :: forall v vs a proxy. (InSymbolList v vs, Floating a)
    => proxy v -> Expr vs a -> Expr vs a
diff p = go
  where
    go (Var q)
        | symbolVal p == symbolVal q = Int 1
        | otherwise                  = Int 0
    go (Int _)                       = Int 0
    go (Lit _)                       = Int 0
    go (Sum as)                      = sum (diff p <$> as)
    go (Prod as)                     = sum $ fmap (uncurry f) $ sliding as
      where
        f :: Expr vs a -> [Expr vs a] -> Expr vs a
        f e es = prod (go e :| es)

    go (Unary Recip e)               = negate (go e) / (e * e)
    go e@(Unary Exp e')              = go e' * e
    go (Unary Sin e)                 = go e * cos e
    go (Unary Cos e)                 = negate $ go e * sin e

-- | The `partials` function symbolically calculates all partial derivatives of an `Expr`.
partials
    :: forall vs a. (All KnownSymbol vs, Floating a)
    => Expr vs a -> NP (K (Expr vs a)) vs
partials e = magic (Proxy :: Proxy vs) (\p -> diff p e)

-------------------------------------------------------------------------------
-- Substitution
-------------------------------------------------------------------------------

-- | Substitute the first variable in 'Expr' with concrete 'Double' value
subst :: forall v vs a proxy. (KnownSymbol v, Floating a) => proxy v -> a -> Expr (v ': vs) a -> Expr vs a
subst _ x = go
  where
    go (Var q) = reifyEqSymbol q p' (Proxy :: Proxy vs)
        (Lit x)
        (Var q)
    go (Int i)   = Int i
    go (Lit d)   = Lit d
    go (Sum es)  = sum $ go <$> es
    go (Prod es) = prod $ go <$> es
    go (Unary f e) = Unary f $ go e

    p' = Proxy :: Proxy v

-- | Substitute all variables in 'Expr'
substAll
    :: (All KnownSymbol vs, Floating a)
    => NP (K a) vs -> Expr vs a -> Expr '[] a 
substAll vars = go
  where
    go (Var q)   = Lit $ findNPK q vars
    go (Int i)   = Int i
    go (Lit d)   = Lit d
    go (Sum es)  = sum $ go <$> es
    go (Prod es) = prod $ go <$> es
    go (Unary f e) = Unary f $ go e

-- | Closed 'Expr' can be reduced to 'Double'.
toDouble :: Floating a => Expr '[] a -> a
toDouble (Int i)   = fromInteger i
toDouble (Lit d)   = d
toDouble (Sum es)  = Monoid.getSum $ foldMap (Monoid.Sum . toDouble) es
toDouble (Prod es) = Monoid.getProduct $ foldMap (Monoid.Product . toDouble) es
toDouble (Unary f e) = unary f $ toDouble e
toDouble _ = error "toDouble: panic!"

-------------------------------------------------------------------------------
-- tools
-------------------------------------------------------------------------------

sliding :: NonEmpty a -> NonEmpty (a, [a])
sliding = go []
  where
    go :: [a] -> NonEmpty a -> NonEmpty (a, [a])
    go prev (x :| [])          = (x, prev) :| []
    go prev (x :| xs@(y : ys)) = (x, prev ++ xs) `NE.cons` go (x : prev) (y :| ys)

-------------------------------------------------------------------------------
-- Bool singleton
-------------------------------------------------------------------------------

data SBool b where
    STrue :: SBool 'True
    SFalse :: SBool 'False

class SBoolI b where
    sbool :: Proxy b -> SBool b

instance SBoolI 'True  where sbool _ = STrue
instance SBoolI 'False where sbool _ = SFalse

symbolEqDec
    :: forall (a :: Symbol) (b :: Symbol). (KnownSymbol a, KnownSymbol b)
    => Proxy a -> Proxy b -> SBool (a == b)
symbolEqDec pa pb = if symbolVal pa == symbolVal pb
    then unsafeCoerce STrue
    else unsafeCoerce SFalse

reifyEqSymbol
    :: forall v w ws x. (KnownSymbol v, KnownSymbol w, InSymbolList v (w ': ws))
    => Proxy v -> Proxy w -> Proxy ws
    -> ((v == w) ~ 'True => x)
    -> (InSymbolList v ws => x)
    -> x
reifyEqSymbol pv pw _ con alt =
    case symbolEqDec pv pw of
        STrue  -> con
        SFalse -> alt

magic
    :: forall vs r. All KnownSymbol vs
    => Proxy vs
    -> (forall x. InSymbolList x vs => Proxy x -> r)
    -> NP (K r) vs
magic _ f = go (sList :: SList vs)
  where
    go :: forall xs. (All KnownSymbol xs) => SList xs -> NP (K r) xs
    go SNil = Nil
    go SCons = go'

    go' :: forall x xs. (KnownSymbol x, All KnownSymbol xs) => NP (K r) (x ': xs)
    go' = case witness of
        Refl -> K (f p) :* go sList
      where
        p = Proxy :: Proxy x

        -- All 'x' are from vs list, so this is safe
        witness :: InSymbolListF x vs :~: 'True
        witness = unsafeCoerce trivial

trivial :: () :~: ()
trivial = Refl

findNPK
    :: forall v vs a. (InSymbolList v vs, KnownSymbol v, All KnownSymbol vs)
    => Proxy v -> NP (K a) vs -> a
findNPK p = go' 
  where
    go :: forall w ws. (KnownSymbol w, All KnownSymbol ws)
       => NP (K a) (w ': ws) -> a
    go (K x :* xs)
        | symbolVal p == symbolVal (Proxy :: Proxy w) = x
        | otherwise                                   = go' xs

    go' :: forall ws. (All KnownSymbol ws)
        => NP (K a) ws -> a
    go' y@(_ :* _) = go y
    go' _ = error "findNPK: panic!"

-------------------------------------------------------------------------------
-- InSymbolList
-------------------------------------------------------------------------------

-- | `elem` on a type level for 'Symbol' lists.
type family InSymbolListF (x :: Symbol) (ys :: [Symbol]) :: Bool
type instance InSymbolListF x '[] = 'False
type instance InSymbolListF x (y ': ys) = x == y || InSymbolListF x ys

-- | Constraint version of 'InSymbolListF'
type InSymbolList v vs = (KnownSymbol v, InSymbolListF v vs ~ 'True)
