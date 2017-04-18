{-# LANGUAGE ScopedTypeVariables, GADTSyntax, RecordWildCards,
             GeneralizedNewtypeDeriving, OverloadedStrings #-}

import Data.List (maximumBy)
import Data.Ord (comparing)
import Data.ByteString (ByteString)
import Data.Map (Map)
import qualified Data.Map as Map

import Control.Applicative
import Control.Monad

import System.Random (StdGen, mkStdGen, Random(..))


newtype UserId = UserId Int
  deriving (Eq, Ord, Enum, Show)

newtype Stake = Stake Int
  deriving (Eq, Ord, Num, Show)

data Hash a = Hash a
  deriving (Eq)

hash :: a -> Hash a
hash = Hash

data PubKey  = PubKey  KeyPair_
  deriving (Eq)

data PrivKey = PrivKey KeyPair_
  deriving (Eq)

data KeyPair_ = KeyPair_ ByteString ByteString
  deriving (Eq)

instance Show PubKey where
  show (PubKey (KeyPair_ pub _)) = "PubKey " ++ show pub

instance Show PrivKey where
  show (PrivKey (KeyPair_ _ priv)) = "PrivKey " ++ show priv

data Signature a = Signature KeyPair_ a
  deriving (Eq)

sign :: PrivKey -> a -> Signature a
sign (PrivKey kp) x = Signature kp x

verify :: Eq a => PubKey -> Signature a -> a -> Bool
verify (PubKey kp) (Signature kp' x') x = kp == kp' && x == x'

newtype SlotNumber = SlotNumber Int
  deriving (Eq, Ord, Enum, Num, Real, Integral)

newtype EpochNumber = EpochNumber Int
  deriving (Eq, Ord, Enum, Num, Real, Integral)

data Block a
   = Block {
       blockState :: BlockHash a,
       blockData  :: a,
       blockSlot  :: SlotNumber,
       blockSig   :: Signature (BlockHash a, a, SlotNumber)
     }
  deriving (Eq)

signBlock :: BlockHash a -> a -> SlotNumber -> PrivKey -> Block a
signBlock st d sl ski = Block st d sl (sign ski (st, d, sl))

instance Show a => Show (Block a) where
  show = show . blockData

data GenesisBlock
   = GenesisBlock {
       genesisStakeholders :: Map UserId (PubKey, Stake),
       genesisAuxInfo      :: GenesisAuxInfo
     }
  deriving (Eq, Show)

data GenesisAuxInfo = GenesisAuxInfo Seed
  deriving (Eq, Show)

data Chain a = InitBlock GenesisBlock
             | ChainBlock (Chain a) (Block a)
  deriving Show

chainLen :: Chain a -> Int
chainLen (InitBlock _)    = 0
chainLen (ChainBlock c _) = 1 + chainLen c

dropBlocks :: Int -> Chain a -> Chain a
dropBlocks 0 c                = c
dropBlocks n c@InitBlock{}    = c
dropBlocks n (ChainBlock c _) = dropBlocks (n-1) c

class Transactions ts where
  adjustStakes :: ts -> Map UserId Stake -> Map UserId Stake

-- this is horribly expensive, spec only
stakeDist :: Transactions ts => (a -> ts) -> Chain a -> Map UserId Stake
stakeDist _ (InitBlock b0)   = fmap snd (genesisStakeholders b0)
stakeDist f (ChainBlock c b) = adjustStakes (f (blockData b)) (stakeDist f c)

type BlockHash a = Hash (Either GenesisBlock (Block a))

hashHead :: Chain a -> BlockHash a
hashHead (InitBlock b0)   = hash (Left b0)
hashHead (ChainBlock _ b) = hash (Right b)

newtype Seed = Seed Int
  deriving (Eq, Enum, Show)

seedPrng :: Seed -> StdGen
seedPrng (Seed s) = mkStdGen s

{-

In the paper the environment Z is a control program that supervises the
execution of the honest programs and the adversary program, which are
interactive Turing machines (ITMs). In the paper the network, key and
leadership election functionality are also modelled as ITMs.

In this model the functionality is incorporated as part of the control program
rather than as separate ITMs. The honest parties are modelled as values of a
suitable free monad type that captures all their visible actions. The control
program (aka simulator) executes these programs and provides their interactions
with the environment and functionality.


From the paper:

Diffuse functionality. It maintains a incoming string for each party Ui that
participates. A party, if activated, is allowed at any moment to fetch the
contents of its incoming string hence one may think of this as a mailbox.
Furthermore, parties can give the instruction to the functionality to diffuse
a message. The functionality keeps rounds and all parties are allowed to
diffuse once in a round. Rounds do not advance unless all parties have diffused
a message.

The adversary, when activated, can also interact with the functionality and
is allowed to read all inboxes and all diffuse requests and deliver messages
to the inboxes in any order it prefers. At the end of the round, the
functionality will ensure that all inboxes contain all messages that have been
diffused (but not necessarily in the same order they have been requested to be
diffused).
-}

data DiffuseFunctionality ts d m
   = DiffuseFunctionality {
       diffuse      :: Chain d -> m (),
       diffuseSkip  :: m (),
       receive      :: m [Chain d],
       transactions :: m ts
     }

data KeyFunctionality m
   = KeyFunctionality {
       getPubPrivKey :: UserId -> m (PubKey, PrivKey),
       getAllPubKeys :: m (Map UserId PubKey)
     }

data StaticLeaderSelectionFunctionality m
   = StaticLeaderSelectionFunctionality {
       genblock :: m (GenesisBlock, LeaderSelection)
     }

type LeaderSelection = GenesisAuxInfo -> SlotNumber -> UserId


-- The protocol executed by honest parties. This is modelled in such a way that
-- it is independent of the execution environment (simulation or otherwise),
-- just executing actions to interact with the functionality.
--
protocol_SPoS :: forall m ts d. (Monad m, Eq ts)
              => DiffuseFunctionality ts ts m
              -> KeyFunctionality m
              -> StaticLeaderSelectionFunctionality m
              -> UserId
              -> m ()
protocol_SPoS diffuseFunctionality@DiffuseFunctionality{..}
              KeyFunctionality{..}
              StaticLeaderSelectionFunctionality{..} ui = do

    -- Initialisation
    (b0, f)  <- genblock
    (_, ski) <- getPubPrivKey ui
    vks      <- getAllPubKeys

    let aux = genesisAuxInfo b0
        sl0 = 0
        c0  = InitBlock b0
        st0 = hashHead c0

    chainExtension_SPoS diffuseFunctionality ui vks ski f aux sl0 c0 st0

chainExtension_SPoS :: forall m ts d. (Monad m, Eq ts)
                    => DiffuseFunctionality ts ts m
                    -> UserId
                    -> Map UserId PubKey -> PrivKey
                    -> LeaderSelection -> GenesisAuxInfo
                    -> SlotNumber
                    -> Chain ts
                    -> BlockHash ts
                    -> m ()
chainExtension_SPoS DiffuseFunctionality{..} ui vks ski f aux = go
  where
    go slj c st = do

      -- 2(a)
      (c', st') <- collectValidChains c

      -- 2(b)
      if slotLeader slj == ui
        then do
          ts <- transactions
          let b   = signBlock st ts slj ski
              c'' = ChainBlock c' b
          diffuse c''
          -- Note that we do not update our own state here
          -- we'll pick up our own broadcast next slot

        else
          diffuseSkip

      go (succ slj) c' st'

    slotLeader = f aux

    collectValidChains :: Chain ts -> m (Chain ts, BlockHash ts)
    collectValidChains c = do
      cs <- receive
      let c'  = maxValid_SPoS c (filter verifyChain cs)
          st' = hashHead c'
      return (c', st')

    verifyChain :: Chain ts -> Bool
    verifyChain (InitBlock _) = True -- ?!?
    verifyChain (ChainBlock c (Block st' dl' sl' sig')) =
        verify vk' sig' (st', dl', sl') && verifyChain c
        -- do we not also need to check the slot number is right
        -- and each block has the hash of its predecessor?
      where
        vk' = vks Map.! slotLeader sl'

maxValid_SPoS :: Chain ts -> [Chain ts] -> Chain ts
maxValid_SPoS c [] = c
maxValid_SPoS c cs
  | chainLen c >= chainLen c' = c
  | otherwise                 = c'
  where
    c' = maximumBy (comparing chainLen) cs



data DynamicLeaderSelectionFunctionality m
   = DynamicLeaderSelectionFunctionality {
       genblock_epoch :: EpochNumber -> Map UserId Stake
                      -> m (GenesisBlock, LeaderSelection)
     }

protocol_DPoS :: forall m ts. (Monad m, Eq ts, Transactions ts)
              => DiffuseFunctionality ts (ts, GenesisAuxInfo) m
              -> KeyFunctionality m
              -> StaticLeaderSelectionFunctionality m
              -> DynamicLeaderSelectionFunctionality m
              -> Int  -- ^ @R@ epoch length in slots
              -> Int  -- ^ @k@ param, block stability depth
              -> UserId
              -> m ()
protocol_DPoS diffuseFunctionality@DiffuseFunctionality{..}
              KeyFunctionality{..}
              StaticLeaderSelectionFunctionality{..}
              dynamicLeaderSelectionFunctionality
              r k ui = do

    -- Initialisation
    (b0, f)  <- genblock
    (_, ski) <- getPubPrivKey ui
    vks      <- getAllPubKeys

    let aux = genesisAuxInfo b0
        sl0 = 0
        c0  = InitBlock b0
        st0 = hashHead c0

    chainExtension_DPoS
      diffuseFunctionality
      dynamicLeaderSelectionFunctionality
      r k ui vks ski
      f aux sl0 c0 st0

chainExtension_DPoS :: forall m ts.
                      (Monad m, Eq ts, Transactions ts)
                    => DiffuseFunctionality ts (ts, GenesisAuxInfo) m
                    -> DynamicLeaderSelectionFunctionality m
                    -> Int  -- ^ @R@ epoch length in slots
                    -> Int  -- ^ @k@ param, block stability depth
                    -> UserId
                    -> Map UserId PubKey -> PrivKey
                    -> LeaderSelection
                    -> GenesisAuxInfo
                    -> SlotNumber
                    -> Chain (ts, GenesisAuxInfo)
                    -> BlockHash (ts, GenesisAuxInfo)
                    -> m ()
chainExtension_DPoS DiffuseFunctionality{..}
                    DynamicLeaderSelectionFunctionality{..}
                    r k ui vks ski = go
  where
    go :: LeaderSelection
       -> GenesisAuxInfo
       -> SlotNumber
       -> Chain (ts, GenesisAuxInfo)
       -> BlockHash (ts, GenesisAuxInfo)
       -> m ()
    go f aux sl c st = do

      let (j, newEpoch) = (EpochNumber (d+1), m == 0)
                            where (d, m) = divMod (fromEnum sl) r

      -- 2(a)
      (f', aux') <-
        if newEpoch && j >= 2
          then do let sj = stakeDist fst (dropBlocks (k-1) c)
                  (bj0, f') <- genblock_epoch j sj
                  return (f', genesisAuxInfo bj0)
                  -- note: this is silly, it's the same 'f' every time
          else return (f, aux)

      -- 2(b)
      (c', st') <- collectValidChains f' aux' c

      -- 2(c)
      if slotLeader f' aux' sl == ui
        then do
          ts <- transactions
          let b   = signBlock st (ts, aux') sl ski
              c'' = ChainBlock c' b
          diffuse c''
          -- Note that we do not update our own state here
          -- we'll pick up our own broadcast next slot

        else
          diffuseSkip

      go f' aux' (succ sl) c' st'


    slotLeader f aux = f aux

    collectValidChains :: LeaderSelection -> GenesisAuxInfo
                       -> Chain (ts, GenesisAuxInfo)
                       -> m (Chain     (ts, GenesisAuxInfo),
                             BlockHash (ts, GenesisAuxInfo))
    collectValidChains f aux c = do
      cs <- receive
      let c'  = maxValid_DPoS c (filter (verifyChain f aux) cs)
          st' = hashHead c'
      return (c', st')

    verifyChain :: LeaderSelection -> GenesisAuxInfo
                -> Chain (ts, GenesisAuxInfo) -> Bool
    verifyChain f aux (InitBlock _) = True -- ?!?
    verifyChain f aux (ChainBlock c (Block st' dl' sl' sig')) =
        verify vk' sig' (st', dl', sl') && verifyChain f aux c
        -- do we not also need to check the slot number is right
        -- and each block has the hash of its predecessor?
      where
        vk' = vks Map.! slotLeader f aux sl'


maxValid_DPoS :: forall a. Chain a -> [Chain a] -> Chain a
maxValid_DPoS c [] = c
maxValid_DPoS c cs
  | chainLen c >= chainLen c' = c
  | otherwise                 = c'
  where
    c' = maximumBy (comparing chainLen) cs


data SimTransaction = SimTransaction Int
  deriving (Eq, Show)

instance Transactions SimTransaction where
  -- no change in stake distribution
  adjustStakes SimTransaction{} dist = dist

type SimChain = Chain [SimTransaction]

simDiffuseFunctionality :: DiffuseFunctionality [SimTransaction] [SimTransaction] SimM
simDiffuseFunctionality =
    DiffuseFunctionality {
      diffuse      = \c -> Diffuse c (Return ()),
      diffuseSkip  = DiffuseSkip (Return ()),
      receive      = Receive Return,
      transactions = Transactions Return
    }

-- does not include corruption features or new users
simKeyFunctionality :: Monad m
                    => Map UserId (PubKey, PrivKey)
                    -> KeyFunctionality m
simKeyFunctionality keys =
    KeyFunctionality {
      getPubPrivKey = \ui -> return (keys Map.! ui),
      getAllPubKeys = return (fmap fst keys)
    }

simStaticLeaderSelectionFunctionality :: Monad m
                                      => Seed
                                      -> Map UserId (PubKey, Stake)
                                      -> StaticLeaderSelectionFunctionality m
simStaticLeaderSelectionFunctionality seed0 users =
    StaticLeaderSelectionFunctionality {
      genblock = return (b0, f)
    }
  where
    b0 = GenesisBlock {
           genesisStakeholders = users,
           genesisAuxInfo      = GenesisAuxInfo seed0
         }

    f :: LeaderSelection
    f (GenesisAuxInfo seed) =
      let leaderIxs :: [Int]
          leaderIxs = randomRs (0, Map.size users - 1) (seedPrng seed)
       in \sl -> fst (Map.elemAt (leaderIxs !! fromEnum sl) users)

data SimM a where
  Return :: a -> SimM a
  Fail   :: String -> SimM a

  -- The only externally visible actions
  Diffuse      :: SimChain -> SimM b -> SimM b
  DiffuseSkip  ::             SimM b -> SimM b
  Receive      :: ([SimChain]       -> SimM b) -> SimM b
  Transactions :: ([SimTransaction] -> SimM b) -> SimM b

instance Monad SimM where
  return = Return
  fail   = Fail

  Return x >>= f = f x
  Fail msg >>= _ = Fail msg

  Diffuse    c k >>= f = Diffuse    c (k >>= f)
  DiffuseSkip  k >>= f = DiffuseSkip  (k >>= f)
  Receive      k >>= f = Receive      (\c  -> k c  >>= f)
  Transactions k >>= f = Transactions (\ts -> k ts >>= f)

instance Functor SimM where
  fmap = liftM

instance Applicative SimM where
  pure  = return
  (<*>) = ap


example =
  sim_S
    (Seed 0)
    exampleUsers
    [ [SimTransaction n] | n <- [0..10] ]

exampleUsers :: [(UserId, PubKey, PrivKey, Stake)]
exampleUsers =
    [ mkUser 0 "pub0" "priv0" 1
    , mkUser 1 "pub1" "priv1" 2
    , mkUser 2 "pub2" "priv2" 1
    ]

mkUser :: Int -> ByteString -> ByteString -> Stake
       -> (UserId, PubKey, PrivKey, Stake)
mkUser ui pub priv s =
    (toEnum ui, PubKey keyPair, PrivKey keyPair, s)
  where
    keyPair = KeyPair_ pub priv


sim_S :: Seed
      -> [(UserId, PubKey, PrivKey, Stake)]
      -> [[SimTransaction]]
      -> Trace
sim_S seed users ts =
    runSimRounds ts [] (simSetup_S seed users)

simSetup_S :: Seed
           -> [(UserId, PubKey, PrivKey, Stake)]
           -> [(UserId, Program)]
simSetup_S seed users =
    [ (ui, party ui)
    | (ui, _, _, _) <- users ]
  where
    party = protocol_SPoS
              simDiffuseFunctionality
              (simKeyFunctionality keys)
              (simStaticLeaderSelectionFunctionality seed stakes)

    keys :: Map UserId (PubKey, PrivKey)
    keys = Map.fromList [ (ui, (vk, sk)) | (ui, vk, sk, _s) <- users ]

    stakes :: Map UserId (PubKey, Stake)
    stakes = Map.fromList [ (ui, (vk, s)) | (ui, vk, _sk, s) <- users ]

type Mailbox = [SimChain]
type Program = SimM ()

type Trace = [TraceEvent]
data TraceEvent = TraceDiffuse  UserId SimChain
                | TraceProgStop UserId
                | TraceProgFail UserId String
                | TraceSimEnded
  deriving Show

runSimRounds :: [[SimTransaction]] -> Mailbox -> [(UserId, Program)] -> Trace
runSimRounds []       _  _  = [TraceSimEnded]
runSimRounds (ts:tss) cs ps =
    case runSimPartiesRound ts cs ps of
      Left  err               -> [err]
      Right (trace, cs', ps') -> trace ++ runSimRounds tss cs' ps'


runSimPartiesRound :: [SimTransaction]
                   -> Mailbox
                   -> [(UserId, Program)]
                   -> Either TraceEvent (Trace, Mailbox, [(UserId, Program)])
runSimPartiesRound ts cs =
    go [] [] []
  where
    go :: Trace -> Mailbox -> [(UserId, Program)] -> [(UserId, Program)]
       -> Either TraceEvent (Trace, Mailbox, [(UserId, Program)])
    go trace cs' ps' []          = Right (reverse trace, reverse cs', reverse ps')
    go trace cs' ps' ((ui,p):ps) =
      case runSimPartyRound ts cs p of
        RoundDiffuseSkip p' -> go trace      cs'  ((ui,p'):ps') ps
        RoundDiffuse  c' p' -> go trace' (c':cs') ((ui,p'):ps') ps
          where
            trace' = TraceDiffuse ui c' : trace
        RoundStop           -> Left (TraceProgStop ui)
        RoundFail msg       -> Left (TraceProgFail ui msg)


-- | Run a SimM party for one round, ie until it diffuses or skips.
--
runSimPartyRound :: [SimTransaction]
                 -> [SimChain]
                 -> SimM ()
                 -> RoundResult
runSimPartyRound _  _  (Return ())      = RoundStop
runSimPartyRound _  _  (Fail  msg)      = RoundFail msg
runSimPartyRound _  _  (Diffuse    c k) = RoundDiffuse   c k
runSimPartyRound _  _  (DiffuseSkip  k) = RoundDiffuseSkip k
runSimPartyRound ts cs (Receive      k) = runSimPartyRound ts cs (k cs)
runSimPartyRound ts cs (Transactions k) = runSimPartyRound ts cs (k ts)

data RoundResult = RoundDiffuse (SimChain) (SimM ())
                 | RoundDiffuseSkip        (SimM ())
                 | RoundStop         -- program unexpectedly terminated
                 | RoundFail String  -- program failed

