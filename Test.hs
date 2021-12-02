

module MemIdeas.Test where

import Clash.Prelude

import MemIdeas.Mem



data MyMem = MyMem
    { myRam :: SyncRamVec 32 Int
    , myField :: Reg (Unsigned 6) }

deriveAllMem ''MyMem


myCircuit
    :: (Unsigned 6, Int)
    -> MemInteract MyMem
    -> (Int, MemInteract MyMem)
myCircuit (addr, val) oldMem = (readMem queue, newMem) where
    newMem = MyMemI queue' reg'

    queue'  = writeMem (writeRam (readMem reg) addr val) queue
    reg'    = writeMem (Just addr) reg

    reg     = myFieldI oldMem
    queue   = myRamI oldMem


myCircuitMealy
    :: HiddenClockResetEnable dom
    => Signal dom (Unsigned 6, Int)
    -> Signal dom Int
myCircuitMealy =
    autoMemMealy
        (MyMem (SyncRamVec $ repeat 0) (Reg 0))
        myCircuit


