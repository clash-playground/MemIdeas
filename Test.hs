

module MemIdeas.Test where

import Clash.Prelude

import MemIdeas.Mem



data MyMem = MyMem
    { myRam :: SyncRamVec 32 Int
    , myField :: Reg (Index 32) }

deriveAllMem ''MyMem


myCircuit
    :: (Index 32, Int)
    -> MemInteract MyMem
    -> (Int, MemInteract MyMem)
myCircuit (addr, val) oldMem = (readMem queue, newMem) where
    newMem = MyMemInteract queue' reg'

    queue'  = writeMem (WriteRam (readMem reg) addr val) queue
    reg'    = writeMem (Just addr) reg

    reg     = myFieldInteract oldMem
    queue   = myRamInteract oldMem


myCircuitMealy
    :: HiddenClockResetEnable dom
    => Signal dom (Index 32, Int)
    -> Signal dom Int
myCircuitMealy =
    autoMemMealy
        (MyMem (SyncRamVec $ repeat 0) (Reg 0))
        myCircuit


