

module MemIdeas.Test where

import GHC.Int

import MemIdeas.Mem



data MyMem = MyMem
    { myRam :: SyncRamVec 32 Int
    , myField :: Reg Int }

deriveAllMem ''MyMem



