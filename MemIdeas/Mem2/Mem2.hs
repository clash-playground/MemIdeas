
{-# LANGUAGE StarIsType #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE KindSignatures #-}

module MemIdeas.Mem2.Mem2 where

import Control.Arrow
import Control.Applicative
import Control.Monad
import Control.Monad.State
import Data.Functor
import Data.Function
import Data.Tuple
import GHC.Err                          (undefined)

import NanoLens.Lens

import Clash.Signal



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


autoMemMealy
    :: ( AutoMem m
       , HiddenClockResetEnable dom )
    => m
    -> ( i -> MemInteract m -> (o, MemInteract m) )
    -> Signal dom i
    -> Signal dom o
autoMemMealy reset circuit input = output where
    mem     = autoMem reset mem'
    circOut = circuit <$> input <*> mem

    output  = fst <$> circOut
    mem'    = snd <$> circOut    

autoMemMealyState
    :: ( AutoMem m
       , HiddenClockResetEnable dom )
    => m
    -> ( i -> State (MemInteract m) o )
    -> Signal dom i
    -> Signal dom o
autoMemMealyState reset circuit = autoMemMealy reset step where
    step i m = runState (circuit i) m

class AutoMem m where
    type MemInteract m :: *

    autoMem
        :: HiddenClockResetEnable dom
        => m
        -> Signal dom (MemInteract m)
        -> Signal dom (MemInteract m)

