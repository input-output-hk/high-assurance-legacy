{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Ouroboros where

import Data.List (maximumBy)
import Data.Ord (comparing)
import qualified Data.Set as Set

newtype StakeholderNumber = StakeholderNumber Int
  deriving (Eq, Ord, Enum)

data GenesisBlock = GenesisBlock
  { genesisStakeholders :: StakeholderNumber -> (PubKey, Stake)
  , genesisAuxInfo      :: GenesisAuxInfo
  }

data PubKey
data PrivKey
data Stake

data BitString = BitString -- to be abstract
  deriving (Eq)

newtype GenesisAuxInfo = GenesisAuxInfo BitString

newtype SlotNumber = SlotNumber Int
  deriving (Eq, Ord, Enum)

-- | A block as defined in Definition 4.3 on page 10.
--
-- A block B generated at a slot sl i ∈ {sl 1 , ... , sl R } contains
-- the current state st ∈ {0, 1} λ,
-- data d ∈ {0, 1} ∗,
-- the slot number sl i and
-- a signature σ = Sign sk i (st, d, sl) computed under sk i corresponding
-- to the stakeholder U i generating the block.
--
data Block = Block
  { blockState :: Hash -- will be the hash of the previous block
  , blockData  :: BitString
  , blockSlot  :: SlotNumber
  , blockSig   :: Signature (Hash, BitString, SlotNumber)
  }

newtype Hash = Hash BitString
  deriving (Eq)

-- | We track for internal clarity the type of information we sign.
data Signature a

-- | A blockchain as define in Definition 4.4 on page 10.
--
-- We do treat the genesis block as part of the blockchain,
-- and we do not define head, but rather hashHead.
--
data Chain =
    InitBlock GenesisBlock
  | ChainBlock Chain Block

-- | A combination of function H(-) and function head, where
-- H is introduced in Definition 4.4 on page 10, and head is
-- also introduced in Definition 4.4 on page 10.
--
hashHead :: Chain -> Hash
hashHead = undefined

-- | Length of a chain, as defined in Definition 4.4 on page 10.
--
-- We do not count the genesis block.
--
chainLen :: Chain -> Int
chainLen (InitBlock _)            = 0
chainLen (ChainBlock initChain _) = 1 + chainLen initChain

-- | Leader selection function.
--
-- See page 10 and Definition 4.7.
--
-- This corresponds to F.
--
-- It takes the auxiliary info in the genesis block and a slot
-- number to assign a slot leader.
--
data LeaderSelection = LeaderSelection
  { select :: GenesisAuxInfo -> SlotNumber -> StakeholderNumber }

type Protocol = Functionality -> StakeholderNumber -> Stakeholder

-- I think we can expect the functionality to be "eventually"
-- deterministic. So computing the functionality may need IO,
-- because we may have to involve random number generation, but
-- the functionality as far as the stakeholders see it is
-- probably deterministic.
--
data Functionality = Functionality
  { genblock_req :: StakeholderNumber -> (GenesisBlock, LeaderSelection) }

-- Again, I think stakeholders don't need "inherent" nondeterminism.
-- We can compute erratic or random stakeholders within IO or other
-- monads, but this can be captured using stakeholder-internal
-- state.
--
data Stakeholder = Stakeholder
  (SlotNumber -> [Chain] -> ([Chain], Stakeholder))

-- | The SPoS protocol as defined in Figure 2 on page 12.
--
-- The protocol describes what honest stakeholders are supposed
-- to do. Adversaries can implement different protocols.
--
protocol_SPoS :: PrivKey -> Protocol
protocol_SPoS privKey functionality stakeHolderNr =
  initialisation
  where
    initialisation :: Stakeholder
    initialisation =
      let
        (b0@(GenesisBlock stakeholders rho), leaderSelection) = genblock_req functionality stakeHolderNr
      in
        go
          (select leaderSelection rho)
          (fst . stakeholders)
          (InitBlock b0)

    go ::
         (SlotNumber -> StakeholderNumber)
      -> (StakeholderNumber -> PubKey)
      -> Chain
      -> Stakeholder
    go leaders pubKeys currentChain = Stakeholder processSlot
      where
        processSlot :: SlotNumber -> [Chain] -> ([Chain], Stakeholder)
        processSlot slotNumber receivedChains =
            case publishedChains newCurrentChain of
              Nothing            -> ([], go leaders pubKeys newCurrentChain)
              Just extendedChain -> ([extendedChain], go leaders pubKeys extendedChain)
          where
            -- Corresponds to step 2a in Figure 2 on page 12.
            -- This is performed in every slot.
            newCurrentChain =
              let
                verifiedChains = filter verifyChain receivedChains
              in
                maxvalid_S currentChain verifiedChains

            -- Verifies a chain as described in step 2a in Figure 2.
            --
            -- TODO: Verification of the genesis block is an interesting problem.
            -- If we don't, we have to at least check that it corresponds to our
            -- genesis block, I think. Otherwise we could receive a completely
            -- different chain?
            --
            -- TODO: It is also unclear whether we have to verify that the
            -- state in each block correctly corresponds to the previous block
            -- hash. Otherwise, the chain could in principle be disconnected.
            --
            verifyChain :: Chain -> Bool
            verifyChain chain =
              case chain of
                InitBlock _b0 -> True -- TODO: do we have to verify the genesis block?
                ChainBlock initChain (Block st d sl sig) ->
                     verify (pubKeys (leaders sl)) sig (st, d, sl)
                  && verifyChain initChain

            -- Corresponds to the block generation describe
            -- in step 2b in Figure 2 on page 12.
            --
            -- Whether this block is used/published is dependent
            -- on whether we are slot leader or not.
            publishedChains :: Chain -> Maybe Chain
            publishedChains chain
              | leaders slotNumber /= stakeHolderNr = Nothing
              | otherwise =
                -- We are slot leader
                let
                  st = hashHead chain
                  d = undefined -- TODO: what data to use
                  newBlock = Block
                    st
                    d
                    slotNumber
                    (sign privKey (st, d, slotNumber))
                in
                  Just (ChainBlock chain newBlock)

-- | General signature function.
--
-- Used for signing blocks, implicitly defined in Definition 4.3
-- no page 10.
--
sign :: PrivKey -> a -> Signature a
sign = undefined

-- | General verification function.
--
-- Used for verifying blocks, implicitly defined in point 2a of
-- Figure 2 on page 12.
--
verify :: PubKey -> Signature a -> a -> Bool
verify = undefined

-- | maxvalid_S function as described / defined on page 11.
--
-- The slightly complicated definition is because we do
-- not want to rely on how 'maximumBy' resolves ties.
--
-- For the chains, it does not matter, because it's specified
-- as arbitrary. But we have to ensure that we prefer the
-- distinguished chain.
--
maxvalid_S :: Chain -> [Chain] -> Chain
maxvalid_S chain [] = chain
maxvalid_S chain (chains@(_ : _)) =
  let
    candidate = maximumBy (comparing chainLen) chains
  in
    if chainLen chain >= chainLen candidate
      then chain
      else candidate

