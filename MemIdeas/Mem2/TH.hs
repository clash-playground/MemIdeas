
{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module MemIdeas.Mem2.TH where

import Control.Applicative
import Control.Monad
import Data.Eq
import Data.Functor
import Data.Function
import Data.List
import Data.Maybe
import Data.String
import Data.Tuple
import GHC.Int
import Text.Show

import NanoLens.Lens

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Lib

import MemIdeas.Mem2.Mem2



deriveAutoMem
    :: Name
    -> Q [Dec]
deriveAutoMem tyName = do
    tyInfo <- reify tyName
    let (tyName, tyDec, tyVars, tyCons) = case tyInfo of
            TyConI dec@(DataD _ nm tvs _ cons _) -> (nm, dec, tvs, cons)
    case tyCons of
         [con]  -> go tyName tyDec tyVars con
         []     -> fail "cannot derive AutoMem for empty types"
         _      -> fail "cannot derive AutoMem for sum types"
  where
    go :: Name -> Dec -> [TyVarBndr] -> Con -> Q [Dec]
    go tyName tyDec tyVars tyCon = do
        let fields = case tyCon of
                RecC _ xs -> xs

            varName :: TyVarBndr -> Name
            varName (PlainTV nm)    = nm
            varName (KindedTV nm _) = nm

            ty = foldl AppT (ConT tyName) (VarT . varName <$> tyVars)

        (amTyCon, amTyDec, amSynDec) <-
            deriveAMType tyName tyVars ty tyCon fields
        amLenses <- deriveAMLenses amTyCon fields
        amInstance <-
            deriveAMInstance ty tyCon amTyCon fields amSynDec

        return $ [ amTyDec ] ++ amLenses ++ amInstance


deriveAMType
    :: Name
    -> [TyVarBndr]
    -> Type
    -> Con
    -> [(Name, Bang, Type)]
    -> Q (Con, Dec, Dec)
deriveAMType tyName tyVars ty tyCon fields = do
    let conName = case tyCon of { RecC nm _ -> nm }
        fieldNames = map (\(nm, _, _) -> nm) fields

    inTyName  <- newName $ nameBase tyName ++ "Interact"
    inConName <- newName $ nameBase conName ++ "Interact"
 
    let genInField (name, strict, ty) = do
            name' <- newName $ nameBase name ++ "Interact"
            let ty'   = AppT (ConT ''MemInteract) ty
            return (name', strict, ty')

        inConE = conE inConName

    inCon <- recC inConName $ map genInField fields

    let varName :: TyVarBndr -> Name
        varName (PlainTV nm)    = nm
        varName (KindedTV nm _) = nm

        inTy  = foldl AppT (ConT inTyName) (VarT . varName <$> tyVars)
        inDec = DataD [] inTyName tyVars Nothing [inCon] []

#if MIN_VERSION_template_haskell (2, 15, 0)
        inSyn = TySynInstD $
            TySynEqn Nothing (AppT (ConT ''MemInteract) ty) inTy
#else
        inSyn = TySynInstD ''MemInteract $ TySynEqn [ty] inTy
#endif

    return (inCon, inDec, inSyn)

deriveAMLenses
    :: Con
    -> [(Name, Bang, Type)]
    -> Q [Dec]
deriveAMLenses con origFields = do
    let (conName, iFields) = case con of { RecC nm fs -> (nm, fs) }

        fieldNames = map (\(nm, _, _) -> nm)
        origFieldNames = fieldNames origFields
        iFieldNames    = fieldNames iFields

        lensNames = map (\nm -> mkName $ nameBase nm ++ "Lens") origFieldNames

    lenses <- sequence $
        zipWith (\nm nr -> genNumberedLens nm con nr) lensNames [0..]

    return lenses

genAMFun :: Con -> Con -> [(Name, Bang, Type)] -> Q Dec
genAMFun resetCon inputCon fields = do
    let conName con = case con of { RecC nm _ -> nm }
        resetConName = conName resetCon
        inputConName = conName inputCon

    resetName  <- newName "reset"
    resetNames <- generateNames "reset" fields
    let resetE = varE resetName
        resetP = conP resetConName (map varP resetNames)
    resetD <- valD resetP (normalB resetE) []

    inputName  <- newName "input"
    inputNames <- generateNames "input" fields 
    let inputE = varE inputName
        genSel name nr =
            valD (varP name) (normalB [| $fieldSel <$> $inputE |]) []
          where
            fieldSel = do
                xName <- newName "x"
                let fieldP = [ if nr == n then varP xName else wildP
                             | (n, _) <- zip [0..] fields ]
                lamE [conP inputConName fieldP] (varE xName)
    inputD <- sequence $ zipWith genSel inputNames [0..]

    sigName  <- newName "sig"
    sigNames <- generateNames "sig" fields
    let genSig s r v = [d| $s = autoMem $r $v |]
    sigsD <- fmap concat $ sequence $ zipWith3 genSig
        (varP <$> sigNames)
        (varE <$> resetNames)
        (varE <$> inputNames)

    let inputConE = conE inputConName
        recFill []          = [| $inputConE |]
        recFill (sig:[])    = [| $inputConE <$> $sig |]
        recFill (sig:sigs)  = [| $fillins <*> $sig |]
            where fillins = recFill sigs

    let argsP = [ varP resetName, varP inputName ]

        body = recFill . map varE . reverse $ sigNames
        supp = map pure (resetD : sigsD ++ inputD)

    dec <- funD 'autoMem [clause argsP (normalB body) supp]
    return dec
        

deriveAMInstance
    :: Type
    -> Con
    -> Con
    -> [(Name, Bang, Type)]
    -> Dec
    -> Q [Dec]
deriveAMInstance ty resetCon inputCon fields inSynDec = do
    ctx <- requiredContext ''AutoMem resetCon

    amFunDec <- genAMFun resetCon inputCon fields

    let autoMemDec =
            InstanceD Nothing ctx (AppT (ConT ''AutoMem) ty)
                [ inSynDec
                , amFunDec
                , PragmaD (InlineP 'autoMem Inline FunLike AllPhases) ]

    return [ autoMemDec ]


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
generateNames prefix xs = sequence $
    zipWith (\n _ -> newName $ prefix ++ show @Int n) [0..] xs



