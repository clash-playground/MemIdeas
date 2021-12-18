
{-# LANGUAGE StarIsType #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE KindSignatures #-}

module MemIdeas.AutoMem.AutoMem where

import Control.Arrow
import Control.Applicative
import Control.Monad
import Control.Monad.State
import Data.Functor
import Data.Function
import Data.Maybe
import Data.Tuple
import GHC.Enum
import GHC.Int
import GHC.TypeLits

import NanoLens.Lens

import Clash.XException
import Clash.Promoted.Nat
import Clash.Sized.Vector
import Clash.Sized.Index
import Clash.Signal
import Clash.Prelude.RAM
import Clash.Prelude.BlockRam



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

-- | Complete a memory interaction by applying the given continuation
-- function and starting the next interaction.
-- 
completeMem :: Applicative g => (g w -> g r) -> g (Mem r w) -> g (Mem r w)
completeMem save =
    fmap startMem . save . fmap (uncurry ($) . (contFun &&& readMem))

startMem :: r -> Mem r w
startMem r = Mem r undefined

-- | Lens over a memory interaction and update it with a function.
--
($=)
    :: MonadState s m
    => Lens' s (Mem r w)
    -> (r -> w)
    -> m ()
l $= f = l %= onMem f

-- | Lens over a memory interaction and update it with a value.
--
(!=)
    :: MonadState s m
    => Lens' s (Mem r w)
    -> w
    -> m ()
l != w = l %= onMem (const w)

type Mem1 a     = Mem a a
type MemF f a   = Mem a (f a)


-- | Create a Mealy machine for a circuit using 'autoMem'.
--
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

-- | Create an 'AutoMem' Mealy machine on top of a 'State' monad.
--
autoMemMealyState
    :: ( AutoMem m
       , HiddenClockResetEnable dom )
    => m
    -> ( i -> State (MemInteract m) o )
    -> Signal dom i
    -> Signal dom o
autoMemMealyState reset circuit = autoMemMealy reset step where
    step i m = runState (circuit i) m

-- | 
class AutoMem m where
    type MemInteract m :: *

    autoMem
        :: HiddenClockResetEnable dom
        => m
        -> Signal dom (MemInteract m)
        -> Signal dom (MemInteract m)


-- | Simple singleton register implementing interactions on Clash's
-- 'regMaybe' primitive.
--
newtype Reg a = Reg { unReg :: a }

instance NFDataX a => AutoMem (Reg a) where
    type MemInteract (Reg a) = MemF Maybe a

    autoMem reset = completeMem $ regMaybe (unReg reset)


-- | Synchronous RAM with an underlying vector.
--
newtype SyncRamVec (n :: Nat) a =
    SyncRamVec { unSyncRamVec :: Vec n a }

instance (KnownNat n, NFDataX a) => AutoMem (SyncRamVec n a) where
    type MemInteract (SyncRamVec n a) = MemF (RamControl n) a

    autoMem reset = completeMem go where
        go input =
            let unReset = unSyncRamVec reset
                rdAddress = ramReadAddress <$> input
                wrContent = ramWriteContent <$> input
            in blockRam unReset rdAddress wrContent


data RamControl (n :: Nat) a
    = RamRead   Int
    | RamWrite  Int Int a

ramReadAddress :: KnownNat n => RamControl n a -> Index n
ramReadAddress ramControl = case ramControl of
    RamRead ix      -> toEnum ix
    RamWrite ix _ _ -> toEnum ix

ramWriteContent :: KnownNat n => RamControl n a -> Maybe (Index n, a)
ramWriteContent ramControl = case ramControl of
    RamRead _       -> Nothing
    RamWrite _ ix a -> Just (toEnum ix, a)


