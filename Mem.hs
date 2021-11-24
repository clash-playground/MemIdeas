
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StarIsType #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}

module MemIdeas.Mem where

import Control.Applicative
import Data.Functor
import Data.Tuple
import Data.Maybe
import Data.Function
import Data.Proxy
import GHC.TypeLits
import GHC.Enum

import Clash.XException
import Clash.Promoted.Nat
import Clash.Sized.Index
import Clash.Sized.Vector
import Clash.Prelude.RAM
import Clash.Prelude.BlockRam
import Clash.Signal



autoMemMealy
    :: ( AutoMem m
       , HiddenClockResetEnable dom )
    => m
    -> (MemInteract m -> MemInteract m)
    -> Signal dom (MemElement m)
autoMemMealy reset trans = readMem <$> x where
    x = autoMem reset y
    y = trans <$> x


-- | Underlying memory type with a known reset strategy.
--
class KnownReset m where
    type MemElement     m :: *
    
    zeroReset :: m

-- | Types with a known control scheme and saving strategy.
--
class KnownReset m => KnownSave m where
    type MemControl     m :: * -> *
    
    knownSave
        :: forall f a dom.
           ( a ~ MemElement m
           , f ~ MemControl m
           , HiddenClockResetEnable dom )
        => m
        -> Signal dom (f a)
        -> Signal dom a

        
data Mem r w = Mem
    { readMem :: r
    , toWrite :: w }

writeMem :: w -> Mem r w -> Mem r w
writeMem w (Mem r _) = Mem r w

onMem :: (r -> w) -> Mem r w -> Mem r w
onMem f m = writeMem (f $ readMem m) m

startMem :: r -> Mem r w
startMem r = Mem r undefined

type MemF f a = Mem a (f a)
    
-- | Automatically derive memories for memory interactions.
--
class KnownReset m => AutoMem m where
    type MemInteract    m :: *
    
    autoMem
        :: forall inter dom.
           HiddenClockResetEnable dom
        => m
        -> Signal dom (MemInteract m)
        -> Signal dom (MemInteract m)

instance (KnownReset m, KnownSave m) => AutoMem m where
    type MemInteract m = MemF (MemControl m) (MemElement m)
    
    autoMem reset =
        fmap startMem . knownSave reset . fmap toWrite

    
-- | Example: Register memory.
--
newtype RegForm a = RegForm { unRegForm :: a }

instance NFDataX a => KnownReset (RegForm a) where
    type MemElement     (RegForm a) = a

instance NFDataX a => KnownSave (RegForm a) where
    type MemControl     (RegForm a) = Maybe
    
    knownSave reset = regMaybe (unRegForm reset)

-- | Example: RAM memory.
--
data RamSync = AsyncRam | SyncRam

newtype RamVecForm (sync :: RamSync) (n :: Nat) a =
    RamVecForm { unRamVecForm :: Vec n a }

instance (KnownNat n, NFDataX a) => KnownReset (RamVecForm sync n a) where
    type MemElement     (RamVecForm sync n a) = a
    
instance (KnownNat n, NFDataX a) => KnownSave (RamVecForm AsyncRam n a) where
    type MemControl     (RamVecForm AsyncRam n a) = RamControl n
    
    knownSave _ = withRam (asyncRam sn) where
        sn = snatProxy (Proxy :: Proxy n)
        
instance (KnownNat n, NFDataX a) => KnownSave (RamVecForm SyncRam n a) where
    type MemControl     (RamVecForm SyncRam n a) = RamControl n
    
    knownSave reset = withRam $ blockRam (unRamVecForm reset)

data RamControl (n :: Nat) a
    = ReadRam   (Index n)
    | WriteRam  (Index n) (Index n) a
    
ramReadAddress = \case
    ReadRam  i      -> i
    WriteRam i _ _  -> i

ramWriteContent = \case
    WriteRam _ i a  -> Just (i, a)
    _               -> Nothing
    
withRam
    :: forall n a dom.
       HiddenClockResetEnable dom
    => (    Signal dom (Index n)
         -> Signal dom (Maybe (Index n, a))
         -> Signal dom a )
    -> Signal dom (RamControl n a)
    -> Signal dom a
withRam ramFun ramMem =
    let rdAddr = ramReadAddress <$> ramMem
        wrCont = ramWriteContent <$> ramMem
    in ramFun rdAddr wrCont
    
