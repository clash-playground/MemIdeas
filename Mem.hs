
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StarIsType #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}

module MemIdeas.Mem where

import              Control.Applicative
import              Control.Monad
import              Data.String
import              Data.Tuple
import              Data.List
import              Data.Maybe
import              Data.Eq
import              Data.Function
import              Data.Functor
import              Data.Proxy
import              GHC.Int
import              GHC.TypeLits
import              GHC.Enum
import              Text.Show

import              Language.Haskell.TH
import              Language.Haskell.TH.Syntax
import              Language.Haskell.TH.Datatype hiding (Strictness)
import qualified    Language.Haskell.TH.Datatype as DT  (Strictness (..))
import              Language.Haskell.TH.Ppr

import              Clash.XException
import              Clash.Promoted.Nat
import              Clash.Sized.Index
import              Clash.Sized.Vector                  (Vec (..))
import qualified    Clash.Sized.Vector           as Vec
import              Clash.Prelude.RAM
import              Clash.Prelude.BlockRam
import              Clash.Signal



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

deriveAllMem :: Name -> Q [Dec]
deriveAllMem tyName = do
    tyInfo <- reify tyName
    let (tyName, tyDec, tyVars, tyCons) = case tyInfo of
            TyConI dec@(DataD _ nm tvs _ cons _) -> (nm, dec, tvs, cons)
    case tyCons of
         [con]  -> deriveAllMemDecs tyName tyDec tyVars con
         []     -> fail "cannot derive AutoMem instance for empty types"
         _      -> fail "cannot derive AutoMem instance for sum types"

deriveAllMemDecs
    :: Name
    -> Dec
    -> [TyVarBndr]
    -> Con
    -> Q [Dec]
deriveAllMemDecs tyName tyDec tyVars tyCon = do
    let fields = case tyCon of
            RecC _ xs -> xs
        
        varName :: TyVarBndr -> Name
        varName (PlainTV nm)    = nm
        varName (KindedTV nm _) = nm
        
        ty = foldl AppT (ConT tyName) (VarT . varName <$> tyVars)
        
    kresetDecs <-
        deriveKnownReset tyName tyVars ty tyCon fields
    
    autoMemDecs <-
        deriveAutoMem tyName tyVars ty tyCon fields
    
    return $ kresetDecs ++ autoMemDecs
    
    
-- | Underlying memory type with a known reset strategy.
--
class KnownReset m where
    type MemElement m :: *

deriveKnownReset
    :: Name
    -> [TyVarBndr]
    -> Type
    -> Con
    -> [(Name, Bang, Type)]
    -> Q [Dec]
deriveKnownReset tyName tyVars ty tyCon fields = do
    let conName = case tyCon of { RecC nm _ -> nm }
    
    elTyName    <- newName $ nameBase tyName ++ "Element"
    elConName   <- newName $ nameBase conName ++ "Element"
    
    -- Determine the needed context
    ctx <- requiredContext ''KnownReset tyCon
    
    -- Build the element datatype
    let genElField (name, strict, ty) = do
            name'   <- newName $ nameBase name ++ "Element"
            let ty' = AppT (ConT ''MemElement) ty
            return (name', strict, ty')
        
    elCon <- recC elConName $ map genElField fields

    let varName :: TyVarBndr -> Name
        varName (PlainTV nm)    = nm
        varName (KindedTV nm _) = nm
        
        elTy  = foldl AppT (ConT elTyName) (VarT . varName <$> tyVars)
        
        elDec = DataD [] elTyName tyVars Nothing [elCon] []
        elSyn = TySynInstD ''MemElement $ TySynEqn [ty] elTy
    
        -- Construct the instance using the new type
        kResetDec = InstanceD Nothing ctx (AppT (ConT ''KnownReset) ty)
                [ elSyn ]

    return [elDec, kResetDec]
    
    
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
    
deriveAutoMem
    :: Name
    -> [TyVarBndr]
    -> Type
    -> Con
    -> [(Name, Bang, Type)]
    -> Q [Dec]
deriveAutoMem tyName tyVars ty tyCon fields = do
    let conName = case tyCon of { RecC nm _ -> nm }
        fieldNames = map (\(nm, _, _) -> nm) fields
    
    inTyName    <- newName $ nameBase tyName ++ "Interact"
    inConName   <- newName $ nameBase conName ++ "Interact"
    
    let inConE = conE inConName
    
    ctx <- requiredContext ''AutoMem tyCon
    
    let genInField (name, strict, ty) = do
            name'   <- newName $ nameBase name ++ "Interact"
            let ty' = AppT (ConT ''MemInteract) ty
            return (name', strict, ty')
            
    inCon <- recC inConName $ map genInField fields
    
    let varName :: TyVarBndr -> Name
        varName (PlainTV nm)    = nm
        varName (KindedTV nm _) = nm
        
        inTy  = foldl AppT (ConT inTyName) (VarT . varName <$> tyVars)
        
        inDec = DataD [] inTyName tyVars Nothing [inCon] []
        inSyn = TySynInstD ''MemInteract $ TySynEqn [ty] inTy
    
    args <- mapM newName [ "reset", "input" ]
    let [ resetE, inputE ] = map varE args
        argsP = map varP args
    
        genField :: Name -> Int -> Q Dec
        genField name nr = do
            let fieldSel = do
                    xName <- newName "x"
                    let fieldP = [ if nr == n then varP xName else wildP
                                 | (n, _) <- zip [0..] fields ]
                    lamE [conP inConName fieldP] (varE xName)
                
            valD (varP name) (normalB [| $fieldSel <$> $inputE |]) []
  
    parts <- generateNames "field" fields
    fieldDecs <- sequence $ zipWith genField parts [0..]
    
    sigs <- generateNames "sig" fields
    
    resets <- generateNames "reset" fields
    let resetP = conP conName (map varP resets)
    resetDec <- valD resetP (normalB resetE) []
    
    let genAutoMemDecl :: Q Pat -> Q Exp -> Q Exp -> Name -> Q [Dec]
        genAutoMemDecl s v i name = [d| $s = autoMem $i $v |]
        
    partDecs <- concat <$> ( sequence $ zipWith4 genAutoMemDecl
        (varP <$> sigs) (varE <$> parts) (varE <$> resets) fieldNames )
        
    let decs = map pure (resetDec : fieldDecs ++ partDecs)
        
        body = case map varE sigs of
            (sig0:rest) ->
                foldl (\acc sigN -> [| $acc <*> $sigN |])
                      ([| $inConE <$> $sig0 |]) rest
            _ -> [| $inConE |]
        
    autoMemFunDec <- funD 'autoMem [clause argsP (normalB body) decs]
    
    let autoMemDec =
            InstanceD Nothing ctx (AppT (ConT ''AutoMem) ty)
                [ inSyn
                , autoMemFunDec
                , PragmaD (InlineP 'autoMem Inline FunLike AllPhases) ]
    
    return [ inDec, autoMemDec ]


--instance {-# OVERLAPPABLE #-} (KnownReset m, KnownSave m) => AutoMem m where
--    type MemInteract m = MemF (MemControl m) (MemElement m)
--    
--    autoMem reset =
--        fmap startMem . knownSave reset . fmap toWrite

knownSaveAutoMem
    :: ( KnownReset m
       , KnownSave m
       , HiddenClockResetEnable dom
       , f ~ MemControl m )
    => m
    -> Signal dom (MemF f (MemElement m))
    -> Signal dom (MemF f (MemElement m))
knownSaveAutoMem reset =
    fmap startMem . knownSave reset . fmap toWrite

    
-- | Example: Register memory.
--
newtype Reg a = Reg { unReg :: a }

instance NFDataX a => KnownReset (Reg a) where
    type MemElement (Reg a) = a

instance NFDataX a => KnownSave (Reg a) where
    type MemControl (Reg a) = Maybe
    
    knownSave reset = regMaybe (unReg reset)

instance NFDataX a => AutoMem (Reg a) where
    type MemInteract (Reg a) = MemF Maybe a
    
    autoMem = knownSaveAutoMem

    
-- | Example: Asynchronous RAM memory.
--
newtype AsyncRamVec (n :: Nat) a =
    AsyncRamVec { unAsyncRamVec :: Vec n a }

instance (KnownNat n, NFDataX a) => KnownReset (AsyncRamVec n a) where
    type MemElement (AsyncRamVec n a) = a
    
instance (KnownNat n, NFDataX a) => KnownSave (AsyncRamVec n a) where
    type MemControl (AsyncRamVec n a) = RamControl n
    
    knownSave _ = withRam (asyncRam sn) where
        sn = snatProxy (Proxy :: Proxy n)

instance (KnownNat n, NFDataX a) => AutoMem (AsyncRamVec n a) where
    type MemInteract (AsyncRamVec n a) = MemF (RamControl n) a
    
    autoMem = knownSaveAutoMem
    
        
-- | Example: Synchronous RAM memory.
--
newtype SyncRamVec (n :: Nat) a =
    SyncRamVec { unSyncRamVec :: Vec n a }

instance (KnownNat n, NFDataX a) => KnownReset (SyncRamVec n a) where
    type MemElement (SyncRamVec n a) = a
    
instance (KnownNat n, NFDataX a) => KnownSave (SyncRamVec n a) where
    type MemControl (SyncRamVec n a) = RamControl n
    
    knownSave reset = withRam $ blockRam (unSyncRamVec reset)

instance (KnownNat n, NFDataX a) => AutoMem (SyncRamVec n a) where
    type MemInteract (SyncRamVec n a) = MemF (RamControl n) a
    
    autoMem = knownSaveAutoMem

    
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
    

-- | Template Haskell utility functions.
--
requiredContext :: Name -> Con -> Q Cxt
requiredContext className (RecC _ fields) = do
    let fieldTys = map (\ (_, _, ty) -> ty) fields
    wantedInstances <-
        mapM (\ty -> constraintsFor className [ty]) (nub fieldTys)
    return $ nub (concat wantedInstances)
    
constraintsFor :: Name -> [Type] -> Q Cxt
constraintsFor className tys
    | show className == "GHC.TypeNats.KnownNat" = do
        return [foldl AppT (ConT className) tys]

constraintsFor className [ty] = case ty of
    VarT _ -> return [AppT (ConT className) ty]
    ConT _ -> return []
    
    _ -> return [] -- ^ TODO: Implement support for more involved classes
    
generateNames :: String -> [a] -> Q [Name]
generateNames prefix xs =
    sequence (zipWith (\n _ -> newName $ prefix ++ show @Int n) [0..] xs)
