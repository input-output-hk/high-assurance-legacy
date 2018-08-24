{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Ouroboros.Chi_Calculus.Process.Expr (

    expr

) where

import           Prelude                            hiding (drop, map, zipWith)

import           Control.Monad.Trans.Reader         (ask, runReader)

import           Data.Functor.Const                 (Const (Const, getConst))
import           Data.List.FixedLength              as List (firstNaturals, map,
                                                             zipWith)
import           Data.Text                          as Text (Text, drop, pack)

import           Numeric.Natural                    (Natural)

import qualified Ouroboros.Chi_Calculus.Data        as Data
import           Ouroboros.Chi_Calculus.Environment (Env' (..))
import           Ouroboros.Chi_Calculus.Process     (Interpretation,
                                                     Process (..))

expr :: Interpretation (Const Natural) (Const Text) (Const Text)
expr (dataInter :: Data.Interpretation dat (Const Text)) = Const . worker 0
  where
    worker :: Natural
           -> Env' (Process dat (Const Natural) (Const Text) (Const Text)) (Const Natural) xs
           -> Text
    worker (n :: Natural) (Nil p)  = expr' dataInter p n
    worker n              (Cons f) = worker (n + 1) (f $ Const n)

expr' :: forall dat .
         Data.Interpretation dat (Const Text)
      -> Process dat (Const Natural) (Const Text) (Const Text)
      -> Natural
      -> Text
expr' dataInter prc n = worker prc `runReader` VarIndexes n 0 0

  where

    worker Stop = do
        return "Stop"
    worker (chan :<: (dq, val)) = do
        return $ channelVar chan <> " [" <> pack (show dq) <> "] ◁ " <> fromDat val
    worker (chan :>: cont) = do
        varIndexes <- ask
        let valIx = valueIndex varIndexes
        let valVar = "x_" <> pack (show valIx)
        let varIndexes' = varIndexes { valueIndex = succ valIx }
        let prcMeaning = worker (cont (Const valVar)) `runReader` varIndexes'
        return $ channelVar chan <> " ▷ " <> valVar <> ". " <> prcMeaning
    worker (prc1 :|: prc2) = do
        prcMeaning1 <- worker prc1
        prcMeaning2 <- worker prc2
        return $ "(" <> prcMeaning1 <> " ‖ " <> prcMeaning2 <> ")"
    worker (NewChannel cont) = do
        varIndexes <- ask
        let chanIx = channelIndex varIndexes
        let chan = Const chanIx
        let varIndexes' = varIndexes { channelIndex = succ chanIx }
        let prcMeaning = worker (cont chan) `runReader` varIndexes'
        return $ "ν" <> channelVar chan <> ". " <> prcMeaning
    worker (Guard val prc') = do
        prcMeaning <- worker prc'
        return $ "(guard " <> fromDat val <> " " <> prcMeaning <> ")"
    worker (Var (Const meaning)) = do
        return meaning
    worker (Letrec defs res) = do
        varIndexes <- ask
        let prcIx = processIndex varIndexes
        let prcVarPrefix = "p_" <> pack (show prcIx) <> "_"
        let prcVars = map ((prcVarPrefix  <>) . pack . show)
                          (firstNaturals @_ @Natural)
        let defPrcs = defs $ map Const prcVars
        let varIndexes' = varIndexes { processIndex = succ prcIx }
        let defPrcMeanings = mapM worker defPrcs `runReader` varIndexes'
        let defTexts = zipWith (\ prcVar defPrcMeaning -> prcVar        <>
                                                          " = "         <>
                                                          defPrcMeaning)
                               prcVars
                               defPrcMeanings
        let defsText = "{" <> drop 1 (foldMap ("; " <>) defTexts) <> " }"
        resMeaning <- worker (res $ map Const prcVars)
        return $ "let " <> defsText <> " in " <> resMeaning

    fromDat :: dat (Const Text) a -> Text
    fromDat = getConst . dataInter

data VarIndexes = VarIndexes {
    channelIndex, valueIndex, processIndex :: Natural
}

channelVar :: Const Natural a -> Text
channelVar chan = "c_" <> pack (show (getConst chan))
