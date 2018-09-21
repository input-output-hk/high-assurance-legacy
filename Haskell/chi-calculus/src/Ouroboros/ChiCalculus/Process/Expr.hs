{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
module Ouroboros.ChiCalculus.Process.Expr (

    expr

) where

import Prelude hiding (map, drop, zipWith)

import Control.Monad.Trans.Reader (runReader, ask)

import Data.Functor.Const (Const (Const, getConst))
import Data.List.FixedLength as List (map, zipWith, firstNaturals)
import Data.Text as Text (Text, pack, drop)

import Numeric.Natural (Natural)

import Ouroboros.ChiCalculus.Process (Process (..), Interpretation)

expr :: Interpretation (Const Text) Text
expr dataInter prc = worker prc `runReader` VarIndexes 0 0 0

    where

    worker Stop = do
        return "Stop"
    worker (cond :?: cnt) = do
        cntMeaning <- worker cnt
        return $ "⟨" <> getConst (dataInter cond) <> "⟩ " <> cntMeaning
    worker (chan :<: val) = do
        return $ getConst (dataInter chan) <> " ◁ " <> getConst (dataInter val)
    worker (chan :>: cnt) = do
        varIndexes <- ask
        let valIx = valueIndex varIndexes
        let valVar = "x_" <> pack (show valIx)
        let varIndexes' = varIndexes { valueIndex = succ valIx }
        let prcMeaning = worker (cnt (Const valVar)) `runReader` varIndexes'
        return $ getConst (dataInter chan) <>
                 " ▷ "                     <>
                 valVar                    <>
                 ". "                      <>
                 prcMeaning
    worker (prc1 :|: prc2) = do
        prcMeaning1 <- worker prc1
        prcMeaning2 <- worker prc2
        return $ "(" <> prcMeaning1 <> " ‖ " <> prcMeaning2 <> ")"
    worker (NewChannel cnt) = do
        varIndexes <- ask
        let chanIx = channelIndex varIndexes
        let chanVar = "c_" <> pack (show chanIx)
        let varIndexes' = varIndexes { channelIndex = succ chanIx }
        let prcMeaning = worker (cnt (Const chanVar)) `runReader` varIndexes'
        return $ "ν" <> chanVar <> ". " <> prcMeaning
    worker (Letrec defs res) = do
        varIndexes <- ask
        let prcIx = processIndex varIndexes
        let prcVarPrefix = "p_" <> pack (show prcIx) <> "_"
        let prcVars = map ((prcVarPrefix  <>) . pack . show)
                          (firstNaturals @_ @Natural)
        let defPrcs = defs prcVars
        let varIndexes' = varIndexes { processIndex = succ prcIx }
        let defPrcMeanings = mapM worker defPrcs `runReader` varIndexes'
        let defTexts = zipWith (\ prcVar defPrcMeaning -> prcVar        <> 
                                                          " = "         <>
                                                          defPrcMeaning)
                               prcVars
                               defPrcMeanings
        let defsText = "{" <> drop 1 (foldMap ("; " <>) defTexts) <> " }"
        resMeaning <- worker (res prcVars)
        return $ "let " <> defsText <> " in " <> resMeaning
    worker (PVar meaning) = do
        return meaning

data VarIndexes = VarIndexes {
    channelIndex, valueIndex, processIndex :: Natural
}
