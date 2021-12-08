
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE KindSignatures #-}

module Mem2 where

import Control.Arrow
import Control.Applicative
import Control.Monad
import Data.Coerce
import Data.Functor
import Data.Function



-- | Model of a complete memory interaction.
--
-- At the start of a memory interaction, the write data is unknown.
-- For the interaction to be complete, the circuit must provide the
-- relevant data.
--
data Mem r w = Mem
    { readMem :: r
    , contFun :: r -> w }

onMem :: (r -> w) -> Mem r w -> Mem r w
onMem f (Mem r _) = Mem r f

completeMem :: Applicative g => (g w -> g r) -> g (Mem r w) -> g (Mem r w)
completeMem save =
    fmap startMem . save . fmap (uncurry ($) . (contFun &&& readMem))

startMem :: r -> Mem r w
startMem r = Mem r undefined

type Mem1 a     = Mem a a
type MemF f a   = Mem a (f a)


-- | Compose with a coercion.
--
(#.) :: Coercible c b => (b -> c) -> (a -> b) -> (a -> c)
(#.) _ =
    coerce (\x -> x :: g) :: forall f g. Coercible g f => f -> g
    -- ^ Given that @Coercible c b@ implies @Coercible (a -> c) (a -> b)@,
    -- @(#.) q p@ becomes just a coercion on @id p@.

(.#) :: Coercible c b => (a -> b) -> (b -> c) -> (a -> c)
(.#) p _ = coerce p

-- | Minimal implementation of lenses for convenient field access.
--
-- Typical lenses should look something like:
-- >>> lens :: Functor f => (a -> f b) -> s -> f t
-- >>> lens k s = k (lensField s) <&> \field -> T field
--
-- Given this definition, observe that
-- >>> lens Const s
-- >>>   == Const (lensField s) <&> \field -> T field
-- >>>   == Const (lensField s)
--          (from @Const v <&> f == Const v@)
--
-- Also observe that
-- >>> lens (\_ -> Identity v) s
-- >>>   == (\_ -> Identity v) (lensField s) <&> \field -> T field
-- >>>   == Identity v <&> \field -> T field
-- >>>   == Identity (T field)
--          (from @Identity v <&> f == Identity (f v)@)
--
type Lens s t a b = forall f. Functor f => (a -> f b) -> s -> f t

-- | Convex lenses can /focus in/ on a field of a record.
--
type Convex r s a = (a -> Const r a) -> s -> Const r s

view :: Convex a s a -> a
view l = getConst #. l Const

-- | Concave lenses let the values of a field diverge with changes in
-- incidence.
--
type Concave s t a b = (a -> Identity b) -> s -> Identity t

over :: Concave s t a b -> (a -> b) -> s -> t
over = coerce

set :: Concave s t a b -> b -> s -> t
set l b = runIdentity #. l (\_ -> Identity b)


