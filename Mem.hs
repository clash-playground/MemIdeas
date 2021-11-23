
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}

module MemIdeas.Mem where

import Control.Applicative
import Data.Functor
import Data.Tuple
import Data.Maybe
import Data.Function
import GHC.TypeLits
import GHC.Enum

import Clash.XException
import Clash.Promoted.Nat
import Clash.Sized.Index
import Clash.Prelude.RAM
import Clash.Prelude.BlockRam
import Clash.Signal



-- | Underlying memory type with a known interaction model.
--
class KnownMem m where
    type MemElement     m :: *
    type MemControl     m :: * -> *
    type MemInteract    m :: *

newtype Mem r w = Mem { unMem :: (r, w) }

readMem :: Mem r w -> r
readMem = fst . unMem

writeMem :: w -> Mem r w -> Mem r w
writeMem w m = Mem (readMem m, w)

onMem :: (r -> w) -> Mem r w -> Mem r w
onMem f m = writeMem (f $ readMem m) m

startMem :: r -> Mem r w
startMem r = (r, undefined)

type MemF f a = Mem a (f a)


-- | Underlying register memory.
--
newtype UnderlyReg a = UnderlyReg a

instance KnownMem (UnderlyReg a) where
    type MemElement  (UnderlyReg a) = a
    type MemInteract (UnderlyReg a) = MemF Maybe a


class (NFDataX u, NFDataX a) => KnownSave u f a where
    knownSave
        :: forall dom.
           HiddenClockResetEnable dom
        => u
        -> Signal dom (f a)
        -> Signal dom a


class KnownMem m => AutoMem m where
    autoMem
        :: forall dom.
           HiddenClockResetEnable dom
        => m
        -> Signal dom (MemInteract m)
        -> Signal dom (MemInteract m)

instance KnownSave u f a => AutoMem u

