newtype StakeholderNumber = StakeholderNumber Int
  deriving (Eq, Ord, Enum)

data GenesisBlock = GenesisBlock {
       genesisStakeholders :: [(PubKey, Stake)],
       genesisAuxInfo      :: BitString
     }

newtype SlotNumber = SlotNumber Int
  deriving (Eq, Ord, Enum)

-- A block B generated at a slot sl i ∈ {sl 1 , ... , sl R } contains
-- the current state st ∈ {0, 1} λ,
-- data d ∈ {0, 1} ∗,
-- the slot number sl i and
-- a signature σ = Sign sk i (st, d, sl) computed under sk i corresponding
-- to the stakeholder U i generating the block.
data Block = Block {
       blockState :: BitString, -- will be the hash of the previous block
       blockData  :: BitString, 
       blockSlot  :: SlotNumber,
       blockSig   :: Signature
     }


data Chain = InitBlock GenesisBlock
           | ChainBlock Blockchain Block


data Functionality {
       genblock_req :: StakeholderNumber -> m (GenesisBlock, LeaderSelection)
     }

type Protocol = Functionality -> StakeholderNumber -> m (Stakeholder m)

data Stakeholder m = Stakeholder {
       eventNewSlot :: m Stakeholder,
       eventReceive :: Chain -> m Stakeholder
     }

protocol𝜋_SPoS :: Protocol
protocol𝜋_SPoS _𝓕  i =
    initialisation
  where
    -- When π_SPoS starts, each stakeholder U_i ∈ {U1, ... , Un } sends (genblock req, U i)  to
    -- 𝓕_(D,F,LS), receiving (genblock, B 0 , F) as answer.
    -- U i sets an internal blockchain C = B 0 and an initial internal state
    -- st = H(B 0 )
    initialisation = do

      (_𝐵₀, _𝗙) <- genblock_req _𝓕  i

      let _𝓒   = InitBlock _𝐵₀
          st = _𝐻(_𝐵₀)
          _ℂ = Set.empty

      return (Stakeholder (newSlot _𝓒  st) ((receive _𝓒  st))

    newSlot _𝓒  st _ℂ = do
