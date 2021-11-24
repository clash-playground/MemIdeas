
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



-- | Create a Mealy machine for a state type with a known
-- 'AutoMem' instance.
--
autoMemMealy
    :: ( AutoMem m
       , HiddenClockResetEnable dom )
    => m
    -> ( i -> MemInteract m -> (o, MemInteract m) )
    -> Signal dom i
    -> Signal dom o
autoMemMealy reset circuit input = output where
    circOut = circuit <$> input <*> mem
    mem = autoMem reset mem'
    
    output = fst <$> circOut
    mem' = snd <$> circOut


-- | Underlying memory type with a known reset strategy.
--
class KnownReset m where
    type MemElement m :: *

-- | Types with a known control scheme and saving strategy.
--
class KnownReset m => KnownSave m where
    type MemControl m :: * -> *
    
    knownSave
        :: HiddenClockResetEnable dom
        => m
        -> Signal dom (MemControl m (MemElement m))
        -> Signal dom (MemElement m)

        
-- | Model of a complete memory interaction.
--
-- At the start of a memory interaction, the write data is unknown.
-- For the interaction to be complete, the circuit must provide the
-- relevant data.
--
data Mem r w = Mem
    { readMem :: r
    , toWrite :: w }

writeMem :: w -> Mem r w -> Mem r w
writeMem w (Mem r _) = Mem r w

onMem :: (r -> w) -> Mem r w -> Mem r w
onMem f (Mem r _) = Mem r $ f r

startMem :: r -> Mem r w
startMem r = Mem r undefined

type MemF f a = Mem a (f a)
    
-- | Automatically derive memories for memory interactions.
--
class KnownReset m => AutoMem m where
    type MemInteract m :: *
    
    autoMem
        :: HiddenClockResetEnable dom
        => m
        -> Signal dom (MemInteract m)
        -> Signal dom (MemInteract m)

-- TODO: Automatic derivation with TH.

instance (KnownReset m, KnownSave m) => AutoMem m where
    type MemInteract m = MemF (MemControl m) (MemElement m)
    
    autoMem reset =
        fmap startMem . knownSave reset . fmap toWrite

    
-- | Example: Register memory.
--
newtype Reg a = Reg { unReg :: a }

instance NFDataX a => KnownReset (Reg a) where
    type MemElement (Reg a) = a

instance NFDataX a => KnownSave (Reg a) where
    type MemControl (Reg a) = Maybe
    
    knownSave reset = regMaybe (unReg reset)

-- | Example: RAM memory.
--
data RamSync = AsyncRam | SyncRam

newtype RamVec (sync :: RamSync) (n :: Nat) a =
    RamVec { unRamVec :: Vec n a }

instance (KnownNat n, NFDataX a) => KnownReset (RamVec sync n a) where
    type MemElement (RamVec sync n a) = a
    
instance (KnownNat n, NFDataX a) => KnownSave (RamVec AsyncRam n a) where
    type MemControl (RamVec AsyncRam n a) = RamControl n
    
    knownSave _ = withRam (asyncRam sn) where
        sn = snatProxy (Proxy :: Proxy n)
        
instance (KnownNat n, NFDataX a) => KnownSave (RamVec SyncRam n a) where
    type MemControl (RamVec SyncRam n a) = RamControl n
    
    knownSave reset = withRam $ blockRam (unRamVec reset)

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
    :: HiddenClockResetEnable dom
    => (    Signal dom (Index n)
         -> Signal dom (Maybe (Index n, a))
         -> Signal dom a )
    -> Signal dom (RamControl n a)
    -> Signal dom a
withRam ramFun ramMem =
    let rdAddr = ramReadAddress <$> ramMem
        wrCont = ramWriteContent <$> ramMem
    in ramFun rdAddr wrCont
    
