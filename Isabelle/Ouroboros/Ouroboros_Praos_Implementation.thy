section \<open> Implementation of the Ouroboros Praos protocol \<close>

theory Ouroboros_Praos_Implementation
  imports
    Finite_Map_Extras
    "HOL-Library.BNF_Corec"
    "HOL-Library.Sublist"
    Chi_Calculus.Typed_Basic_Transition_System
    Complex_Main
begin

text \<open>
  In this section we present an implementation of the Ouroboros Praos protocol as defined in
  @{cite praos}. Since a security analysis of the protocol is out of scope, we do not model the
  environment \<open>\<Z>\<close>, the adversary \<open>\<A>\<close>, etc. However, we retain the use of the Universal
  Composability (UC) framework for the sake of design modularity. It's important to mention that in
  the paper the protocol is described in the so-called `hybrid model', in which the protocol assumes
  the availability of idealized versions of some cryptographic primitives, called `ideal
  functionalities', that can be invoked by the protocol participants, much like sub-routines. These
  ideal functionalities can be replaced later with concrete implementations without affecting the
  security properties of the protocol. Thus, we model these ideal functionalities as locale's.
\<close>

no_notation Sublist.parallel (infixl "\<parallel>" 50)

subsection \<open> Preliminaries \<close>

text \<open>
  We let \<open>v \<bar>\<bar> w\<close> denote concatenation of `strings' (i.e. arbitrary values):
\<close>

consts concat :: "'a \<Rightarrow> 'b \<Rightarrow> 'a" (infixl \<open>\<bar>\<bar>\<close> 65)

subsection \<open> Public-key cryptography \<close>

text \<open>
  The Praos protocol is based on a public-key cryptographic system. We define a locale with two
  parameters: a key generation function and a function to derive the verification key from the
  secret key. Also, we state an assumption that establishes a relationship between the two
  parameters, namely that if we generate \<open>sk\<close> and \<open>vk\<close> using the key generation function then it
  holds that \<open>vk\<close> is the verification key of \<open>sk\<close>. Furthermore, this locale is parametrized with the
  type of the security parameter:
\<close>

locale keys =
  fixes generate :: "'security_parameter \<Rightarrow> 'vkey \<times> 'skey"
    and verification_key_of :: "'skey \<Rightarrow> 'vkey"
  assumes correctness: "(vk, sk) = generate \<kappa> \<longrightarrow> verification_key_of sk = vk"

subsection \<open> Cryptographic hash functions \<close>

text \<open>
  The paper uses the random oracle model (ROM). In the ROM a hash function is modeled as a random
  oracle, which is basically a magical black box that implements a truly random function. As the ROM
  is used just for the purposes of the security proof, we model a collision-free cryptographic hash
  functions instead. To do so, we define a locale which is parametric in the type \<open>'a\<close> of values to
  be hashed and in the type \<open>'hash\<close> of hash values. Now, theoretically, cryptographic hash functions
  have certain properties, e.g. they are one-way functions, meaning that they are difficult to
  invert by an efficient adversary. But, the terms `difficult' and `efficient' are probabilistic in
  nature, so we cannot enforce these properties in the code:
\<close>

locale hashable =
  fixes \<H> :: "'a \<Rightarrow> 'hash"
  assumes collision_resistance: "inj \<H>"

subsection \<open> Verifiable random functions (VRFs) \<close>

text \<open>
  A VRF is basically a pseudorandom function such that everyone can check that the values of the
  function were computed correctly. In particular, in the Praos protocol, the stakeholders use a VRF
  for executing the private lottery to check whether they're slot leaders for a particular slot.
  Also, stakeholders use a VRF to include a pseudorandom value in each block they produce.
\<close>

text \<open>
  We model the output of a VRF as a pair comprised by a pseudorandom value and a proof that the
  value was computed correctly:
\<close>
type_synonym ('vrf\<^sub>y, 'vrf\<^sub>\<pi>) vrf\<^sub>o = "'vrf\<^sub>y \<times> 'vrf\<^sub>\<pi>"

text \<open>
  We define a locale with four parameters:
  \<^item>  A function that, given a secret key and an input value of an arbitrary type, evaluates the VRF
     and produces a VRF output.
  \<^item>  A function that, given a verification key, an input value, and a VRF output, verifies that the
     VRF value was produced correctly.
  \<^item>  A constant that specifies the size (or length) of the VRF values.
  \<^item>  A function that casts a VRF value into a real number.

  Also, we postulate some properties on the parameters of the locale:
  \<^item> We require that the value size be positive.
  \<^item> We require some properties to hold for VRFs according to the definition in the paper, namely:
    \<^descr> Uníqueness: This establishes that for any input \<open>x\<close> there exists a unique value \<open>y\<close> that can
      be proved to be valid. That is, if we can verify the correctness of both \<open>y\<close> and \<open>y'\<close> for \<open>x\<close>
      then \<open>y\<close> and \<open>y'\<close> must be equal.
    \<^descr> Provability: This establishes that the value produced by evaluating the VRF can be proved to
      be correctly computed, provided that the verification key used to check the correctness is
      derived from the secret key used to evaluate the VRF.

  Theoretically, VRFs must fulfill another property called `pseudorandomness', which is
  probabilistic and states that it's difficult for an efficient adversary to distinguish a VRF value
  from a truly random value. Furthermore, the paper uses a special VRF which is more secure than
  standard VRFs, since it guarantees that VRF values cannot be predicted even if the adversary is
  allowed to generate the secret and verification keys. Naturally, for this work, we stick to the
  regular definition of a VRF:
\<close>

locale vrf = keys generate verification_key_of
  for generate :: "'security_parameter \<Rightarrow> 'vkey \<times> 'skey"
    and verification_key_of :: "'skey \<Rightarrow> 'vkey" +
  fixes evaluate :: "'skey \<Rightarrow> 'a \<Rightarrow> ('vrf\<^sub>y, 'vrf\<^sub>\<pi>) vrf\<^sub>o"
    and verify :: "'vkey \<Rightarrow> 'a \<Rightarrow> ('vrf\<^sub>y, 'vrf\<^sub>\<pi>) vrf\<^sub>o \<Rightarrow> bool"
    and value_size :: nat (\<open>l\<^sub>V\<^sub>R\<^sub>F\<close>)
    and value_to_real :: "'vrf\<^sub>y \<Rightarrow> real"
  assumes value_size_positivity: "value_size > 0"
    and uniqueness: "verify vk x (y, \<pi>) = verify vk x (y', \<pi>') \<longrightarrow> y = y'"
    and provability: "vk = verification_key_of sk \<longrightarrow> verify vk x (evaluate sk x)"

text \<open>
  We also model two special tags that are used as súffixes when calling the VRF: \<open>TEST\<close> is used in
  slot leader election, and \<open>NONCE\<close> when creating and validating block nonces. The purpose of these
  tags is to provide domain separation, i.e. that we can simulate two independent `virtual VRFs'
  from a single VRF:
\<close>

datatype vrf_query_type = TEST | NONCE

subsection \<open> Digital signatures \<close>

text \<open>
  In the paper, digital signature schemes are modeled as ideal functionalities. Moreover, the paper
  describes two digital signature schemes: A regular digital signature scheme (denoted by
  \<open>\<F>\<close>$_{\mathsf{DSIG}}$) which is used to sign transactions, and a digital signature scheme (denoted
  by \<open>\<F>\<close>$_{\mathsf{KES}}$) which is used to sign blocks and has the capability of allowing the
  signing key to evolve, in such a way that the adversary cannot forge past signatures. For our
  purposes, though, we model a single, ordinary digital signature scheme for signing both
  transactions and blocks. To do so, we define a locale with two parameters:
  \<^item> A function that, given a secret key and a message of an arbitrary type, produces a signature for
    the message.
  \<^item> A function that, given a verification key, a message and a signature, verifies that the
    signature is a legitimate signature for the message.


  Also, we only require a provability property, stating that the signature produced by signing a
  message can be proved to be valid, provided that the verification key used to check the validity
  of the signature is derived from the secret key used to sign the message:
\<close>

locale digital_signature_scheme = keys generate verification_key_of
  for generate :: "'security_parameter \<Rightarrow> 'vkey \<times> 'skey"
    and verification_key_of :: "'skey \<Rightarrow> 'vkey" +
  fixes sign :: "'skey \<Rightarrow> 'm \<Rightarrow> 'sig"
    and verify :: "'vkey \<Rightarrow> 'm \<Rightarrow> 'sig \<Rightarrow> bool"
  assumes provability: "vk = verification_key_of sk \<longrightarrow> verify vk x (sign sk x)"

subsection \<open> Protocol parameters \<close>

text \<open>
  The protocol depends on a number of parameters. We use a locale for specifying those parameters
  and some properties on them. Namely, the parameters are:

  \<^item> \<open>k\<close>: Establishes how deep in the chain (in terms of number of blocks) a transaction needs to be
    in order to be declared as stable. Must be positive.
  \<^item> \<open>R\<close>: The length of an epoch, measured in number of slots. Must be positive.
  \<^item> \<open>f\<close>: The `active slot coefficient'. Establishes the probability that at least one stakeholder
    is elected as a slot leader in each slot, that is, the probability that a slot is not empty.
    Must be a strictly positive probability.
  \<^item> \<open>\<some>\<close>: The advantage in terms of stake of the honest stakeholders against the adversarial ones.
    Must be a probability strictly between 0 and 1.
\<close>

locale protocol_parameters =
  fixes k :: nat
    and R :: nat
    and f :: real
    and honest_advantage :: real (\<open>\<some>\<close>)
  assumes k_positivity: "k > 0"
    and R_positivity: "R > 0"
    and f_non_zero_probability: "f \<in> {0<..1}"
    and honest_advantage_bounded_probability: "\<some> \<in> {0<..<1}"

subsection \<open> Slots \<close>

text \<open>
  As defined in the paper, we model the concept of slot as a natural number, beginning at 1:
\<close>

type_synonym slot = nat

abbreviation (input) first_slot :: slot where
  "first_slot \<equiv> 1"

subsection \<open> Epochs \<close>

text \<open>
  As defined in the paper, we model the concept of epoch as a natural number, beginning at 1:
\<close>

type_synonym epoch = nat

abbreviation (input) first_epoch :: epoch where
  "first_epoch \<equiv> 1"

text \<open>
  By using basic arithmetic, we can compute the epoch to which a given slot belongs:
\<close>

definition (in protocol_parameters) slot_epoch :: "slot \<Rightarrow> epoch" where
  [simp]: "slot_epoch sl = nat \<lceil>sl / R\<rceil>"

text \<open>
  and we can check whether a given slot is the first one in its epoch:
\<close>

definition (in protocol_parameters) first_in_epoch :: "slot \<Rightarrow> bool" where
  [simp]: "first_in_epoch sl = (R dvd (sl - 1))"

subsection \<open> Stake distributions \<close>

text \<open>
  We model a stakeholder ID as a natural number and use a special syntax to match the notation used
  in the paper:
\<close>

datatype stakeholder_id = StakeholderId nat (\<open>U\<^bsub>_\<^esub>\<close>)

instance stakeholder_id :: countable
  by countable_datatype

text \<open>
  Now we model a stake distribution simply as a finite map from stakeholder IDs to their respective
  stakes:
\<close>

type_synonym stake = nat

type_synonym stake_distr = "(stakeholder_id, stake) fmap"

text \<open>
  Given a set \<open>X\<close> of stakeholder IDs and a stake distribution \<open>\<S>\<close>, we can calculate the absolute
  maximum stake controlled by \<open>X\<close>, denoted by \<open>s\<^sup>+\<^bsub>X\<^esub>(\<S>)\<close>, as simply the sum of the stakes in \<open>\<S>\<close>
  belonging to \<open>X\<close>, provided that \<open>X\<close> is included in the domain of \<open>\<S>\<close>:
\<close>

definition
  absolute_stake_of_set :: "stakeholder_id set \<Rightarrow> stake_distr \<Rightarrow> stake" (\<open>s\<^sup>+\<^bsub>_\<^esub>'(_')\<close>)
where
  [simp]: "s\<^sup>+\<^bsub>X\<^esub>(\<S>) = (\<Sum>U \<in> X. \<S> $$! U)" if "X \<subseteq> fmdom' \<S>"

text \<open>
  Based on the previous definition, we define the absolute stake controlled by @{emph \<open>all\<close>}
  stakeholders appearing in a stake distribution \<open>\<S>\<close>, denoted by \<open>s\<^sup>+\<^sub>\<P>(\<S>)\<close>:
\<close>

abbreviation (input)
  absolute_stake_of_univ :: "stake_distr \<Rightarrow> stake" (\<open>s\<^sup>+\<^sub>\<P>'(_')\<close>)
where
  "s\<^sup>+\<^sub>\<P>(\<S>) \<equiv> s\<^sup>+\<^bsub>fmdom' \<S>\<^esub>(\<S>)"

text \<open>
  And we define the absolute stake controlled by a @{emph \<open>single\<close>} stakeholder \<open>U\<close> appearing in a
  stake distribution \<open>\<S>\<close>, denoted by \<open>s\<^sup>+\<^bsub>U\<^esub>(\<S>)\<close>:
\<close>

abbreviation (input)
  absolute_stake_of :: "stakeholder_id \<Rightarrow> stake_distr \<Rightarrow> stake" (\<open>s\<^sup>+\<^bsub>_\<^esub>'(_')\<close>)
where
  "s\<^sup>+\<^bsub>U\<^esub>(\<S>) \<equiv> s\<^sup>+\<^bsub>{U}\<^esub>(\<S>)"

text \<open>
  A relative stake is simply a proportion of stake, so we define it as a real number:
\<close>

type_synonym relative_stake = real

text \<open>
  Now, we define the relative stake controlled by a set \<open>X\<close> of stakeholder IDs w.r.t. a stake
  distribution \<open>\<S>\<close>, namely, the proportion of stake controlled by \<open>X\<close> with respect to the whole
  stake in \<open>\<S>\<close>, denoted by \<open>\<alpha>\<^sup>+\<^bsub>X\<^esub>(\<S>)\<close>:
\<close>

definition
  relative_stake_of_set :: "stakeholder_id set \<Rightarrow> stake_distr \<Rightarrow> relative_stake" (\<open>\<alpha>\<^sup>+\<^bsub>_\<^esub>'(_')\<close>)
where
  [simp]: "\<alpha>\<^sup>+\<^bsub>X\<^esub>(\<S>) = s\<^sup>+\<^bsub>X\<^esub>(\<S>) / s\<^sup>+\<^sub>\<P>(\<S>)" if "\<S> \<noteq> {$$}"

text \<open>
  And we define the relative stake controlled by a @{emph \<open>single\<close>} stakeholder \<open>U\<close> w.r.t. a stake
  distribution \<open>\<S>\<close>, denoted by \<open>\<alpha>\<^sup>+\<^bsub>U\<^esub>(\<S>)\<close>:
\<close>

abbreviation (input)
  relative_stake_of :: "stakeholder_id \<Rightarrow> stake_distr \<Rightarrow> relative_stake" (\<open>\<alpha>\<^sup>+\<^bsub>_\<^esub>'(_')\<close>)
where
  "\<alpha>\<^sup>+\<^bsub>U\<^esub>(\<S>) \<equiv> \<alpha>\<^sup>+\<^bsub>{U}\<^esub>(\<S>)"

subsection \<open> Genesis block \<close>

text \<open>
  As defined in the paper, we have a genesis block associated to a chain. We assume that the same
  genesis block is used by all chains and stakeholders:
\<close>

type_synonym 'vkey stakeholder_keys = "
  'vkey \<times> \<comment> \<open> $v^\\mathrm{vrf}$ \<close>
  'vkey \<times> \<comment> \<open> $v^\\mathrm{kes}$ \<close>
  'vkey" \<comment> \<open> $v^\mathrm{dsig}$ \<close>

type_synonym ('vkey, 'nonce) genesis = "
  (stakeholder_id \<rightharpoonup> 'vkey stakeholder_keys) \<times> \<comment> \<open> stakeholders' verification keys \<close>
  stake_distr \<times> \<comment> \<open> initial stake distribution $\\mathbb{S}_0$ \<close>
  'nonce" \<comment> \<open> initial nonce \<open>\<eta>\<^sub>0\<close> \<close>

subsection \<open> Transactions \<close>

text \<open>
  In the paper, the environment \<open>\<Z>\<close> issues transactions on behalf of any stakeholder \<open>U\<^sub>i\<close> by
  requesting a signature on the transaction and handing the transaction data $d \in \{0,1\}^*$ to
  stakeholders to put them into blocks. We decide not to model transaction processing this way but
  use a more realistic approach instead: Transactions are assumed to be received by stakeholders
  through the network. A transaction body is assumed to be a simple assertion of the form
  `Stakeholder \<open>U\<^sub>i\<close> transfers stake \<open>s\<close> to Stakeholder \<open>U\<^sub>j\<close>':
\<close>

type_synonym transaction_body = "
  stakeholder_id \<times> \<comment> \<open> \<open>U\<^sub>i\<close> \<close>
  stakeholder_id \<times> \<comment> \<open> \<open>U\<^sub>j\<close> \<close>
  stake \<comment> \<open> \<open>s\<close> \<close>"

text \<open>
  and a transaction consists of a transaction body accompanied by a signature of it under the
  signing key corresponding to \<open>U\<^sub>i\<close>:
\<close>

type_synonym 'sig transaction = "transaction_body \<times> 'sig"

text \<open>
  We can apply a transaction to a stake distribution. The paper does not define how this is done,
  so we use the intuitive definition and assume that the source and target stakeholders exist in the
  stake distribution and that the source stakeholder has enough stake for the withdrawal:
\<close>

fun
  apply_transaction :: "'sig transaction \<Rightarrow> stake_distr \<Rightarrow> stake_distr"
where
  "apply_transaction ((U\<^sub>i, U\<^sub>j, s), _) \<S> = (
    let
      \<S>' = \<S>(U\<^sub>i $$:= \<S> $$! U\<^sub>i - s)
    in
      \<S>'(U\<^sub>j $$:= \<S>' $$! U\<^sub>j + s))"

subsection \<open> Blocks \<close>

text \<open>
  We define a block proof, denoted by \<open>B\<^sub>\<pi> = (U\<^sub>i, y, \<pi>)\<close> in the paper, which represents the `proof of
  leadership' of the block creator:
\<close>

type_synonym ('vrf\<^sub>y, 'vrf\<^sub>\<pi>) block_proof = "
  stakeholder_id \<times> \<comment> \<open> Stakeholder who created the block \<close>
  ('vrf\<^sub>y, 'vrf\<^sub>\<pi>) vrf\<^sub>o" \<comment> \<open> VRF output used for slot leader election \<close>

text \<open>
  and we distinguish between an \<open>unsigned block\<close> (a block without a signature, a concept not
  explicitly present in the paper) and a signed block. Since the latter corresponds to the concept
  of a block in the paper, we refer to a signed block as simply a \<open>block\<close>:
\<close>

type_synonym ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) unsigned_block = "
  slot \<times> \<comment> \<open> Slot when the block was created \<close>
  'hash option \<times> \<comment> \<open> Previous block hash (if any), denoted by \<open>st\<close> in the paper \<close>
  'sig transaction list \<times> \<comment> \<open> Transaction data, denoted by \<open>d\<close> in the paper \<close>
  ('vrf\<^sub>y, 'vrf\<^sub>\<pi>) block_proof \<times> \<comment> \<open> Block proof, denoted by \<open>B\<^sub>\<pi>\<close> in the paper \<close>
  ('vrf\<^sub>y, 'vrf\<^sub>\<pi>) vrf\<^sub>o" \<comment> \<open> Nonce proof, denoted by $\rho = (\rho_y, \rho_\pi)$ in the paper \<close>

type_synonym ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) block = "('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) unsigned_block \<times> 'sig"

fun bl_slot :: "('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) block \<Rightarrow> slot" where
  "bl_slot ((sl, _, _, _, _), _) = sl"

fun bl_txs :: "('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) block \<Rightarrow> 'sig transaction list" where
  "bl_txs ((_, _, d, _, _), _) = d"

fun bl_nonce_proof :: "('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) block \<Rightarrow> ('vrf\<^sub>y, 'vrf\<^sub>\<pi>) vrf\<^sub>o" where
  "bl_nonce_proof ((_, _, _, _, \<rho>), _) = \<rho>"

text \<open>
  We can apply a block to a stake distribution by applying all transactions in the block to the
  stake distribution:
\<close>

definition
  apply_block :: "('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) block \<Rightarrow> stake_distr \<Rightarrow> stake_distr"
where
  [simp]: "apply_block B = fold apply_transaction (bl_txs B)"

subsection \<open> Chains \<close>

text \<open>
  A chain is simply a sequence of blocks. As stated earlier, we do not record the genesis block
  explicitly as part of the chain:
\<close>

type_synonym ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain = "('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) block list"

text \<open>
  We let \<open>\<C>\<^sub>1 \<preceq> \<C>\<^sub>2\<close> indicate that the chain \<open>\<C>\<^sub>1\<close> is a prefix of the chain \<open>\<C>\<^sub>2\<close>:
\<close>

notation prefix (infix \<open>\<preceq>\<close> 50)

text \<open>
  We define a function to prune the last \<open>m\<close> blocks in a chain \<open>\<C>\<close>, denoted by \<open>\<C>\<^bsup>\<lceil>m\<^esup>\<close> in the
  paper:
\<close>

definition
  prune_chain :: "
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    nat \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain"
  (\<open>_\<^sup>\<lceil>\<^bsup>_\<^esup>\<close> [999] 999)
where
  [simp]: "\<C>\<^sup>\<lceil>\<^bsup>m\<^esup> = take (length \<C> - m) \<C>"

text \<open>
  Also, we define a function to prune the blocks in a chain which have slots greater than a
  given slot:
\<close>

definition
  prune_after :: "slot \<Rightarrow> ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow> ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain"
where
  [simp]: "prune_after sl = takeWhile (\<lambda>B. bl_slot B \<le> sl)"

text \<open>
  And we can apply a chain \<open>\<C>\<close> to a stake distribution \<open>\<S>\<close> by sequentially applying all blocks
  in \<open>\<C>\<close> to \<open>\<S>\<close>:
\<close>

definition
  apply_chain :: "('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow> stake_distr \<Rightarrow> stake_distr"
where
  [simp]: "apply_chain = fold apply_block"

subsection \<open> Functionality \<open>\<F>\<close>$^{\tau,r}_{RLB}$ and subprotocol \<open>\<pi>\<close>$_{RLB}$ \<close>

text \<open>
  In the paper, the functionality \<open>\<F>\<close>$^{\tau,r}_{RLB}$ models a randomness beacon that basically
  provides a fresh nonce for each epoch to (re)seed the election process. Furthermore, this beacon
  is resettable and leaky in order to strengthen the adversary. The paper also presents a
  subprotocol \<open>\<pi>\<close>$_{RLB}$ that simulates the beacon in the \<open>\<F>\<close>$_\mathsf{INIT}$-hybrid model. So, we
  choose to directly model \<open>\<pi>\<close>$_{RLB}$, and not explicitly model \<open>\<F>\<close>$_\mathsf{INIT}$ but instead
  assume that each stakeholder is given the genesis block as a parameter (see Section
  \ref{sec:sh-process-ref}):
\<close>

definition
  fold1 :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a"
where
  [simp]: "fold1 f xs = foldl f (hd xs) (tl xs)"

lemma "fold1 (\<bar>\<bar>) [a,b,c] = (a \<bar>\<bar> b) \<bar>\<bar> c"
  by simp

locale \<pi>\<^sub>R\<^sub>L\<^sub>B =
  protocol_parameters +
  hashable \<H>\<^sub>\<eta>
  for \<H>\<^sub>\<eta> :: "'nonce \<Rightarrow> 'nonce"
begin

function
  next_epoch_nonce :: "'nonce \<Rightarrow> epoch \<Rightarrow> ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow> 'nonce"
where
  "next_epoch_nonce \<eta>\<^sub>p\<^sub>r\<^sub>e\<^sub>v j \<C> = (
    let
      sl\<^sub>e\<^sub>n\<^sub>d = (j - (first_epoch + 1)) * R + 16 * nat \<lceil>of_nat k / (1 + \<some>)\<rceil>;
      \<C>' = prune_after sl\<^sub>e\<^sub>n\<^sub>d \<C>;
      v = fold1 (\<bar>\<bar>) (map bl_nonce_proof \<C>')
    in
      \<H>\<^sub>\<eta> (\<eta>\<^sub>p\<^sub>r\<^sub>e\<^sub>v \<bar>\<bar> j \<bar>\<bar> v))" if "j \<ge> first_epoch + 1"
| "next_epoch_nonce \<eta>\<^sub>p\<^sub>r\<^sub>e\<^sub>v j \<C> = undefined \<eta>\<^sub>p\<^sub>r\<^sub>e\<^sub>v j \<C>" if "j < first_epoch + 1"
  by (atomize, auto)
  termination by lexicographic_order

end

subsection \<open> Leader election \<close>

text \<open>
  In this section we model the procedure which determines whether a stakeholder is elected as a slot
  leader or not for a given slot:
\<close>

locale leader_election =
  protocol_parameters +
  vrf _ _ evaluate\<^sub>V\<^sub>R\<^sub>F verify\<^sub>V\<^sub>R\<^sub>F
  for evaluate\<^sub>V\<^sub>R\<^sub>F :: "'skey \<Rightarrow> 'nonce \<Rightarrow> ('vrf\<^sub>y, 'vrf\<^sub>\<pi>) vrf\<^sub>o"
  and verify\<^sub>V\<^sub>R\<^sub>F :: "'vkey \<Rightarrow> 'nonce \<Rightarrow> ('vrf\<^sub>y, 'vrf\<^sub>\<pi>) vrf\<^sub>o \<Rightarrow> bool"
begin

context
begin

text \<open>
  We define the probability \<open>\<phi>(\<alpha>)\<close> that a stakeholder with relative stake \<open>\<alpha>\<close> is elected as a slot
  leader:
\<close>

notation powr (\<open>_\<^bsup>_\<^esup>\<close> [81,81] 80)

definition
  slot_leader_probability :: "relative_stake \<Rightarrow> real" (\<open>\<phi>'(_')\<close>)
where
  [simp]: "\<phi>(\<alpha>) = 1 - (1 - f)\<^bsup>\<alpha>\<^esup>"

text \<open>
  Next, given epoch \<open>j\<close>, the initial stake distribution \<open>\<S>\<^sub>0\<close>, and a chain \<open>\<C>\<close>, we define a function
  \<open>\<S>\<^bsub>j\<^esub>(\<S>\<^sub>0, \<C>)\<close> that computes the stake distribution at the end of epoch \<open>j - (first_epoch + 1)\<close> as
  reflected in \<open>\<C>\<close> if \<open>j > first_epoch\<close>; otherwise returns \<open>\<S>\<^sub>0\<close>:
\<close>

private function
  epoch_stake_distr :: "
    epoch \<Rightarrow>
    stake_distr \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    stake_distr"
  (\<open>\<S>\<^bsub>_\<^esub>'(_,_')\<close>)
where
  "\<S>\<^bsub>j\<^esub>(\<S>\<^sub>0, _) = \<S>\<^sub>0" if "j = first_epoch"
| "\<S>\<^bsub>j\<^esub>(\<S>\<^sub>0, \<C>) = (
    let
      sl\<^sub>e\<^sub>n\<^sub>d = (j - (Suc first_epoch)) * R;
      \<C>' = prune_after sl\<^sub>e\<^sub>n\<^sub>d \<C>
    in
      apply_chain \<C>' \<S>\<^sub>0)" if "j > first_epoch"
| "\<S>\<^bsub>j\<^esub>(\<S>\<^sub>0, \<C>) = undefined j \<S>\<^sub>0 \<C>" if "j < first_epoch"
  by (auto, fastforce)
  termination by lexicographic_order

text \<open>
  Now, given the initial stake distribution \<open>\<S>\<^sub>0\<close> and a chain \<open>\<C>\<close>, a stakeholder \<open>U\<close> is an eligible
  slot leader for a particular slot in an epoch \<open>j\<close> if its VRF output is smaller than a @{emph
  \<open>threshold value\<close>}, denoted by \<open>T\<^bsub>U\<^esub>\<^bsup>j\<^esup>(\<S>\<^sub>0, \<C>)\<close> and defined as follows:
\<close>

private fun
  slot_leader_threshold :: "
    stakeholder_id \<Rightarrow>
    epoch \<Rightarrow>
    stake_distr \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    real"
  (\<open>T\<^bsub>_\<^esub>\<^bsup>_\<^esup>'(_,_')\<close>)
where
  "T\<^bsub>U\<^esub>\<^bsup>j\<^esup>(\<S>\<^sub>0, \<C>) = (
    let
      \<S>\<^sub>j = \<S>\<^bsub>j\<^esub>(\<S>\<^sub>0, \<C>);
      \<alpha> = \<alpha>\<^sup>+\<^bsub>U\<^esub>(\<S>\<^sub>j)
    in
      2\<^bsup>l\<^sub>V\<^sub>R\<^sub>F\<^esup> * \<phi>(\<alpha>))"

text \<open>
  Finally, a stakeholder can ask if they are a slot leader for a given slot (note that stakeholders
  can only check this for themselves, not for other stakeholders):
\<close>

fun
  is_slot_leader :: "
    stakeholder_id \<Rightarrow>
    slot \<Rightarrow>
    'skey \<Rightarrow>
    'nonce \<Rightarrow>
    stake_distr \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    (('vrf\<^sub>y, 'vrf\<^sub>\<pi>) vrf\<^sub>o) option"
where
  "is_slot_leader U sl sk \<eta> \<S>\<^sub>0 \<C> = (
    let
      j = slot_epoch sl;
      T = T\<^bsub>U\<^esub>\<^bsup>j\<^esup>(\<S>\<^sub>0, \<C>);
      (y, \<pi>) = evaluate\<^sub>V\<^sub>R\<^sub>F sk (\<eta> \<bar>\<bar> sl \<bar>\<bar> TEST)
    in
      if value_to_real y < T then Some (y, \<pi>) else None)"

end

end

subsection \<open> Chain update \<close>

text \<open>
  In this section we model the procedure by which a stakeholder decides which chain to adopt
  given a set of alternatives received over the network in the current round (the `longest chain'
  rule, i.e. that the intersection between the alternative chain and the current best chain is no
  more than \<open>k\<close> blocks back, and the alternative chain is strictly longer than the current best
  chain):
\<close>

locale chain_selection =
  protocol_parameters +
  hashable \<H>\<^sub>B
  for \<H>\<^sub>B :: "('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) block \<Rightarrow> 'block_hash"
begin

text \<open>
  Since the genesis block is not a proper block in a chain, we have to take care of it separately.
  So, we need to check whether two chains are `disjoint', i.e., whether the only intersection point
  between them is the genesis block. This amounts to checking whether their first blocks are
  different, since, by construction, if they differ in the first block then they must necessarily
  diverge:
\<close>

definition
  disjoint_chains :: "
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    bool"
where
  [iff]: "disjoint_chains \<C> \<C>' \<longleftrightarrow> \<H>\<^sub>B (hd \<C>) \<noteq> \<H>\<^sub>B (hd \<C>')" if "\<C> \<noteq> []" and "\<C>' \<noteq> []"

text \<open>
  Also, we can extract the hashed, longest common prefix of two chains:
\<close>

definition
  hashed_lcp :: "
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    'block_hash list"
where
  [simp]: "hashed_lcp \<C> \<C>' = Longest_common_prefix {map \<H>\<^sub>B \<C>, map \<H>\<^sub>B \<C>'}"

text \<open>
  Now, we can check whether a chain \<open>\<C>\<close> forks from another chain \<open>\<C>'\<close> at most \<open>n\<close> blocks, i.e. that
  we should roll back at most the most recent \<open>n\<close> blocks in \<open>\<C>\<close> in order to switch to \<open>\<C>'\<close>:
\<close>

definition
  forks_at_most :: "
    nat \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    bool"
where
  [iff]: "forks_at_most n \<C> \<C>' \<longleftrightarrow> (
    if
      disjoint_chains \<C> \<C>'
    then
      length \<C> \<le> n
    else
      length (drop (length (hashed_lcp \<C> \<C>')) \<C>) \<le> n)"

text \<open>
  For implementation purposes, we define a function that, given two chains \<open>\<C>\<close> and \<open>\<C>'\<close>, obtains
  the suffix of \<open>\<C>\<close> after trimming its hashed longest common prefix with \<open>\<C>'\<close>:
\<close>

fun
  first_suffix :: "
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain"
where
  "first_suffix \<C> \<C>' = (
    let
      hlcp = longest_common_prefix (map \<H>\<^sub>B \<C>) (map \<H>\<^sub>B \<C>')
    in
      drop (length hlcp) \<C>)"

text \<open>
  Also, we can compute the list of the longest chains in a given list of chains \<open>\<CC>\<close>:
\<close>

abbreviation (input) "is_longest_chain \<C> \<CC> \<equiv> \<forall>\<C>' \<in> set \<CC>. length \<C> \<ge> length \<C>'"

definition
  longest_chains :: "
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain list \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain list"
where
  "longest_chains \<CC> = [\<C> \<leftarrow> \<CC>. is_longest_chain \<C> \<CC>]"

text \<open>
  Now we can define the function that implements the `longest chain' rule, namely the
  $\mathsf{maxvalid}$ function in the paper:
\<close>

fun
  max_valid :: "
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain list \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain"
where
  "max_valid \<C> \<CC> = (
    let
      \<CC>' = [\<C>' \<leftarrow> \<C> # \<CC>. forks_at_most k \<C> \<C>']; \<comment> \<open>the \<open>k\<close> parameter\<close>
      \<CC>'' = longest_chains \<CC>'
    in
      if \<C> \<in> set \<CC>'' then \<C> else hd \<CC>'')"

end

subsection \<open> The semi-synchronous model \label{sec:semi-sync-model-ref} \<close>

text \<open>
  In the paper, a semi-synchronous model with an upper bound \<open>\<Delta>\<close> in message delay is used. Regarding
  \<open>\<Delta>\<close>, we stress the fact that the protocol is oblivious of \<open>\<Delta>\<close> and this bound is only used in the
  security analysis. Hence, from the protocol's point of view, the network is no better than an
  eventual delivery network (without a concrete bound), which can be modeled using our process
  calculus, for example, as a reliable broadcasting server process. Regarding synchrony, we simply
  assume that an external `clock process' signals each stakeholder when a round (i.e. slot) ends,
  and that messages sent in one round are guaranteed to be received at the onset of the next round.
\<close>

paragraph \<open> The Delayed Diffuse Functionality. \<close>

text \<open>
  We do not model the network as a separate ideal functionality \textsf{DDiffuse}\<open>\<^sub>\<Delta>\<close> but rely on
  our process calculus features for communication. In particular, a single channel is used both to
  read the received messages from a stakeholder's `incoming string' (or `mailbox') and to
  `diffuse' a message. Also, the restriction that a stakeholder is allowed to diffuse once in a
  round is explicitly enforced by the stakeholder process implementation, see Section
  \ref{sec:sh-process-ref}.
\<close>

subsection \<open> Broadcast messages \<close>

text \<open>
  In addition to broadcasting transactions and chains, we also assume that there is a `clock
  process' broadcasting the next slot at the end of each current slot, see Section
  \ref{sec:semi-sync-model-ref}:
\<close>

datatype ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) broadcast_msg =
    BroadcastTx (bm_tx: "'sig transaction")
  | BroadcastChain (bm_\<C>: "('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain")
  | BroadcastEndSlot (bm_sl: slot)

instance broadcast_msg :: (countable, countable, countable, countable) countable
  by countable_datatype

type_synonym ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) broadcast_channel = "
  ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) broadcast_msg channel"

text \<open>
  We assume that each stakeholder has access to a channel used to receive messages broadcasted by
  the network and a channel used to broadcast messages to the network, which constitute the
  stakeholder's network interface:
\<close>

type_synonym ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) receive_channel = "
  ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) broadcast_msg channel"

type_synonym ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) send_channel = "
  ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) broadcast_msg channel"

type_synonym ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) network_interface = "
  ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) send_channel \<times> ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) receive_channel"

subsection \<open> The stakeholder process \label{sec:sh-process-ref} \<close>

text \<open>
  Now we are ready to define the process representing a stakeholder running the protocol.
\<close>

subsubsection \<open> Stakeholder state \<close>

text \<open>
  Each stakeholder has access to its own state. We bundle the items comprising the stakeholder state
  in a record type:
\<close>

record ('skey, 'vkey, 'hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig, 'nonce) stakeholder_state =
  ss_id :: stakeholder_id \<comment> \<open> ID of the stakeholder in the set \<open>U\<^sub>1, ..., U\<^sub>n\<close> \<close>
  ss_G :: "('vkey, 'nonce) genesis" \<comment> \<open> genesis block \<close>
  ss_\<C> :: "('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain" \<comment> \<open> current chain \<close>
  ss_\<eta> :: 'nonce \<comment> \<open> current epoch nonce \<open>\<eta>\<^sub>j\<close> \<close>
  ss_\<CC> :: "('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain list" \<comment> \<open> chains received during the current slot \<close>
  ss_txs :: "'sig transaction list" \<comment> \<open> transactions received during the current slot \<close>
  ss_st :: "'hash option" \<comment> \<open> current state, namely the hash of the head of \<open>ss_\<C>\<close> \<close>
  ss_sk\<^sub>v\<^sub>r\<^sub>f :: 'skey \<comment> \<open> secret key for \<open>\<F>\<close>$_{\mathsf{VRF}}$ \<close>
  ss_sk\<^sub>k\<^sub>e\<^sub>s :: 'skey \<comment> \<open> secret key for \<open>\<F>\<close>$_{\mathsf{KES}}$ \<close>
  ss_sk\<^sub>d\<^sub>s\<^sub>i\<^sub>g :: 'skey \<comment> \<open> secret key for \<open>\<F>\<close>$_{\mathsf{DSIG}}$ \<close>

locale stakeholders =
  digital_signature_scheme _ _ sign\<^sub>K\<^sub>E\<^sub>S verify\<^sub>K\<^sub>E\<^sub>S +
  digital_signature_scheme _ _ sign\<^sub>D\<^sub>S\<^sub>I\<^sub>G verify\<^sub>D\<^sub>S\<^sub>I\<^sub>G +
  chain_selection _ _ _ _ \<H>\<^sub>B +
  leader_election _ _ _ _ _ _ _ _ evaluate\<^sub>V\<^sub>R\<^sub>F verify\<^sub>V\<^sub>R\<^sub>F +
  \<pi>\<^sub>R\<^sub>L\<^sub>B _ _ _ _ \<H>\<^sub>\<eta>
  for sign\<^sub>K\<^sub>E\<^sub>S :: "
    'skey \<Rightarrow>
    ('hash::countable, 'vrf\<^sub>y::countable, 'vrf\<^sub>\<pi>::countable, 'sig::countable) unsigned_block \<Rightarrow>
    'sig"
  and verify\<^sub>K\<^sub>E\<^sub>S :: "'vkey \<Rightarrow> ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) unsigned_block \<Rightarrow> 'sig \<Rightarrow> bool"
  and sign\<^sub>D\<^sub>S\<^sub>I\<^sub>G :: "'skey \<Rightarrow> transaction_body \<Rightarrow> 'sig"
  and verify\<^sub>D\<^sub>S\<^sub>I\<^sub>G :: "'vkey \<Rightarrow> transaction_body \<Rightarrow> 'sig \<Rightarrow> bool"
  and \<H>\<^sub>B :: "('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) block \<Rightarrow> 'hash"
  and evaluate\<^sub>V\<^sub>R\<^sub>F :: "'skey \<Rightarrow> 'nonce \<Rightarrow> ('vrf\<^sub>y, 'vrf\<^sub>\<pi>) vrf\<^sub>o"
  and verify\<^sub>V\<^sub>R\<^sub>F :: "'vkey \<Rightarrow> 'nonce \<Rightarrow> ('vrf\<^sub>y, 'vrf\<^sub>\<pi>) vrf\<^sub>o \<Rightarrow> bool"
  and \<H>\<^sub>\<eta> :: "'nonce \<Rightarrow> 'nonce"
begin

context
begin

subsubsection \<open> Verification \<close>

text \<open>
  We can verify that a transaction is valid w.r.t. a genesis block, namely that the source and
  target stakeholders exist in the genesis block's stake distribution, that the source stakeholder
  has enough stake for the withdrawal, and that the signature is valid. Here we assume that the
  given genesis block is well-formed, in particular that the domain of both maps coincide:
\<close>

private definition
  verify_tx :: "'sig transaction \<Rightarrow> ('vkey, 'nonce) genesis \<Rightarrow> bool"
where
  [iff]: "verify_tx tx G \<longleftrightarrow> (
    let
      (txbody, \<sigma>) = tx;
      (U\<^sub>i, U\<^sub>j, s) = txbody;
      (vks, \<S>\<^sub>0, _) = G;
      (_, _, vk\<^sub>i) = the (vks U\<^sub>i) \<comment> \<open>\<open>U\<^sub>i\<close>'s DSIG verification key\<close>
    in
      \<exists>s\<^sub>i s\<^sub>j. \<S>\<^sub>0 $$ U\<^sub>i = Some s\<^sub>i \<and> \<S>\<^sub>0 $$ U\<^sub>j = Some s\<^sub>j \<and> s\<^sub>i \<ge> s \<and> verify\<^sub>D\<^sub>S\<^sub>I\<^sub>G vk\<^sub>i txbody \<sigma>)"

text \<open>
  and thus we can trivially verify whether a list of transactions is valid w.r.t. a genesis block:
\<close>

private definition
  verify_tx_data :: "'sig transaction list \<Rightarrow> ('vkey, 'nonce) genesis \<Rightarrow> bool"
where
  [iff]: "verify_tx_data txs G \<longleftrightarrow> (\<forall>i \<in> {0..<length txs}. verify_tx (txs ! i) G)"

text \<open>
  A key component of block verification is verifying the block proof, i.e. that the stakeholder who
  created the block was in the slot leader set of the slot in which the block was created:
\<close>

private definition
  verify_block_proof :: "slot \<Rightarrow> 'vkey \<Rightarrow> 'nonce \<Rightarrow> ('vrf\<^sub>y, 'vrf\<^sub>\<pi>) vrf\<^sub>o \<Rightarrow> real \<Rightarrow> bool"
where
  [iff]: "verify_block_proof sl vk \<eta> v T \<longleftrightarrow>
    verify\<^sub>V\<^sub>R\<^sub>F vk (\<eta> \<bar>\<bar> sl \<bar>\<bar> TEST) v \<and> value_to_real (fst v) < T"

text \<open>
  Furthermore, we verify that the nonce proof in a block was properly created:
\<close>

private definition
  verify_block_nonce :: "slot \<Rightarrow> 'vkey \<Rightarrow> 'nonce \<Rightarrow> ('vrf\<^sub>y, 'vrf\<^sub>\<pi>) vrf\<^sub>o \<Rightarrow> bool"
where
  [iff]: "verify_block_nonce sl vk \<eta> v \<longleftrightarrow> verify\<^sub>V\<^sub>R\<^sub>F vk (\<eta> \<bar>\<bar> sl \<bar>\<bar> NONCE) v"

text \<open>
  Armed with these definitions, we can now verify that a block is indeed valid:
\<close>

private definition
  verify_block :: "
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) block \<Rightarrow>
    'hash option \<Rightarrow>
    ('vkey, 'nonce) genesis \<Rightarrow>
    'nonce \<Rightarrow>
    real \<Rightarrow>
    bool"
where
  [iff]: "verify_block B oh\<^sub>p\<^sub>r\<^sub>e\<^sub>v G \<eta> T \<longleftrightarrow> (
    let
      ((sl, st, d, B\<^sub>\<pi>, \<rho>), \<sigma>) = B;
      (U\<^sub>s, y, \<pi>) = B\<^sub>\<pi>;
      (\<rho>\<^sub>y, \<rho>\<^sub>\<pi>) = \<rho>
    in
      verify_tx_data d G \<and> (
      \<exists>v\<^sub>v\<^sub>r\<^sub>f v\<^sub>k\<^sub>e\<^sub>s v\<^sub>d\<^sub>s\<^sub>i\<^sub>g.
        Some (v\<^sub>v\<^sub>r\<^sub>f, v\<^sub>k\<^sub>e\<^sub>s, v\<^sub>d\<^sub>s\<^sub>i\<^sub>g) = (fst G) U\<^sub>s \<and> \<comment> \<open> \<open>U\<^sub>s\<close>'s verification keys \<close>
        verify_block_proof sl v\<^sub>v\<^sub>r\<^sub>f \<eta> (y, \<pi>) T \<and>
        verify_block_nonce sl v\<^sub>v\<^sub>r\<^sub>f \<eta> (\<rho>\<^sub>y, \<rho>\<^sub>\<pi>) \<and>
        verify\<^sub>K\<^sub>E\<^sub>S v\<^sub>k\<^sub>e\<^sub>s (sl, st, d, B\<^sub>\<pi>, \<rho>) \<sigma>) \<and> (
      case oh\<^sub>p\<^sub>r\<^sub>e\<^sub>v of
        None \<Rightarrow> True
      | Some h\<^sub>p\<^sub>r\<^sub>e\<^sub>v \<Rightarrow> the st = h\<^sub>p\<^sub>r\<^sub>e\<^sub>v))" \<comment> \<open> if \<open>oh\<^sub>p\<^sub>r\<^sub>e\<^sub>v\<close> is not \<open>None\<close> then \<open>st\<close> is not \<open>None\<close> either \<close>

text \<open>
  and we can verify that a chain is indeed valid. It is important to mention that candidate chains
  cannot be empty since they were diffused by slot leaders, which built them on top of the genesis
  block:
\<close>

private definition
  verify_chain :: "('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow> ('vkey, 'nonce) genesis \<Rightarrow> 'nonce \<Rightarrow> bool"
where
  [iff]: "verify_chain \<C> G \<eta> \<longleftrightarrow> (\<forall>i \<in> {0..<length \<C>}.
    let
      (_, \<S>\<^sub>0, _) = G;
      B = \<C> ! i; \<comment> \<open> current block \<close>
      ((sl, _, _, B\<^sub>\<pi>, _), _) = B;
      U\<^sub>s = fst B\<^sub>\<pi>;
      oh\<^sub>p\<^sub>r\<^sub>e\<^sub>v = if i = 0 then None else fst (snd (fst (\<C> ! (i - 1)))); \<comment> \<open> previous block hash \<close>
      j = slot_epoch sl;
      T\<^sub>s = T\<^bsub>U\<^sub>s\<^esub>\<^bsup>j\<^esup>(\<S>\<^sub>0, \<C>)
    in
      verify_block B oh\<^sub>p\<^sub>r\<^sub>e\<^sub>v G \<eta> T\<^sub>s)"

text \<open>
  Finally, we specify what the initial state for each stakeholder should be:
\<close>

fun
  init_stakeholder_state :: "
    stakeholder_id \<Rightarrow>
    ('vkey, 'nonce) genesis \<Rightarrow>
    'skey \<Rightarrow>
    'skey \<Rightarrow>
    'skey \<Rightarrow>
    ('skey, 'vkey, 'hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig, 'nonce) stakeholder_state"
where
  "init_stakeholder_state U\<^sub>i G sk\<^sub>v\<^sub>r\<^sub>f sk\<^sub>k\<^sub>e\<^sub>s sk\<^sub>d\<^sub>s\<^sub>i\<^sub>g = (
    let
      (_, _, \<eta>\<^sub>0) = G
    in
      \<lparr>
        ss_id = U\<^sub>i,
        ss_G = G,
        ss_\<C> = [],
        ss_\<eta> = \<eta>\<^sub>0,
        ss_\<CC> = [],
        ss_txs = [],
        ss_st = None,
        ss_sk\<^sub>v\<^sub>r\<^sub>f = sk\<^sub>v\<^sub>r\<^sub>f,
        ss_sk\<^sub>k\<^sub>e\<^sub>s = sk\<^sub>k\<^sub>e\<^sub>s,
        ss_sk\<^sub>d\<^sub>s\<^sub>i\<^sub>g = sk\<^sub>d\<^sub>s\<^sub>i\<^sub>g
      \<rparr>)"

subsubsection \<open> Chain extension \<close>

text \<open>
  In this section we model the procedure by which a stakeholder elected as a slot leader extends its
  current chain. We define a function that constructs a new block containing the transactions
  in the stakeholder's current state:
\<close>

private fun
  make_block :: "
    ('skey, 'vkey, 'hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig, 'nonce) stakeholder_state \<Rightarrow>
    slot \<Rightarrow>
    ('vrf\<^sub>y, 'vrf\<^sub>\<pi>) vrf\<^sub>o \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) block"
where
  "make_block ss sl v = (
    let
      U = ss_id ss;
      \<eta> = ss_\<eta> ss;
      st = if ss_\<C> ss = [] then None else Some (\<H>\<^sub>B (last (ss_\<C> ss)));
      d = ss_txs ss;
      B\<^sub>\<pi> = (U, v);
      \<rho> = evaluate\<^sub>V\<^sub>R\<^sub>F (ss_sk\<^sub>v\<^sub>r\<^sub>f ss) (\<eta> \<bar>\<bar> sl \<bar>\<bar> NONCE);
      uB = (sl, st, d, B\<^sub>\<pi>, \<rho>);
      \<sigma> = sign\<^sub>K\<^sub>E\<^sub>S (ss_sk\<^sub>k\<^sub>e\<^sub>s ss) uB
    in
      (uB, \<sigma>))"

text \<open>
  We can extend a stakeholder's current chain simply by appending a newly constructed block to
  it and updating its current `state' to the hash of this block:
\<close>

private fun
  extend_chain :: "
    ('skey, 'vkey, 'hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig, 'nonce) stakeholder_state \<Rightarrow>
    slot \<Rightarrow>
    ('vrf\<^sub>y, 'vrf\<^sub>\<pi>) vrf\<^sub>o \<Rightarrow>
    ('skey, 'vkey, 'hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig, 'nonce) stakeholder_state"
where
  "extend_chain ss sl v = (
    let
      B\<^sub>n\<^sub>e\<^sub>w = make_block ss sl v
    in
      ss
        \<lparr>
          ss_\<C> := ss_\<C> ss @ [B\<^sub>n\<^sub>e\<^sub>w],
          ss_st := Some (\<H>\<^sub>B B\<^sub>n\<^sub>e\<^sub>w),
          ss_txs := []
        \<rparr>)"

text \<open>
  We can easily define a function to store a given transaction in the transactions mempool of a
  stakeholder's state:
\<close>

private definition
  store_tx :: "
    ('skey, 'vkey, 'hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig, 'nonce) stakeholder_state \<Rightarrow>
    'sig transaction \<Rightarrow>
    ('skey, 'vkey, 'hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig, 'nonce) stakeholder_state"
where
  [simp]: "store_tx ss tx = ss\<lparr>ss_txs := tx # ss_txs ss\<rparr>"

text \<open>
  Also, we define a function to store a given chain in the chains mempool of a stakeholder's state,
  after pruning blocks belonging to future slots in the chain, and provided that the pruned chain
  is valid:
\<close>

private fun
  store_chain :: "
    slot \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    ('skey, 'vkey, 'hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig, 'nonce) stakeholder_state \<Rightarrow>
    ('skey, 'vkey, 'hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig, 'nonce) stakeholder_state"
where
  "store_chain sl \<C> ss = (
    let
      \<C>\<^sub>p = prune_after sl \<C>
    in
      if
        verify_chain \<C>\<^sub>p (ss_G ss) (ss_\<eta> ss)
      then
        ss\<lparr>ss_\<CC> := \<C>\<^sub>p # ss_\<CC> ss\<rparr>
      else
        ss)"

text \<open>
  We define a function to compute the new epoch nonce and store it in the stakeholder's state:
\<close>

private fun
  compute_new_epoch_randomness :: "
    slot \<Rightarrow>
    ('skey, 'vkey, 'hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig, 'nonce) stakeholder_state \<Rightarrow>
    ('skey, 'vkey, 'hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig, 'nonce) stakeholder_state"
where
  "compute_new_epoch_randomness sl\<^sub>n\<^sub>e\<^sub>x\<^sub>t ss = (
    let
      j = slot_epoch sl\<^sub>n\<^sub>e\<^sub>x\<^sub>t
    in
      ss\<lparr>ss_\<eta> := next_epoch_nonce (ss_\<eta> ss) j (ss_\<C> ss)\<rparr>)"

text \<open>
  We define a function to update the current best chain in a stakeholder's state to the longest
  chain seen so far by the stakeholder:
\<close>

private fun
  update_local_chain :: "
    ('skey, 'vkey, 'hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig, 'nonce) stakeholder_state \<Rightarrow>
    ('skey, 'vkey, 'hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig, 'nonce) stakeholder_state"
where
  "update_local_chain ss = (
    let
      \<C>\<^sub>m\<^sub>a\<^sub>x = max_valid (ss_\<C> ss) (ss_\<CC> ss)
    in
      ss\<lparr>
          ss_\<C> := \<C>\<^sub>m\<^sub>a\<^sub>x,
          ss_st := Some (\<H>\<^sub>B (last \<C>\<^sub>m\<^sub>a\<^sub>x)), \<comment> \<open> update `state' with hash of best chain's head \<close>
          ss_\<CC> := [] \<comment> \<open> empty chains mempool \<close>
        \<rparr>)"

text \<open>
  We define a process that is executed when an end-of-slot signal is received and that basically
  checks whether the associated stakeholder is a slot leader for the current slot, and, if so,
  extends its current chain, broadcasts it to the network, and runs a continuation process:
\<close>

private abbreviation
  start_of_slot :: "
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) network_interface \<Rightarrow>
    ('skey, 'vkey, 'hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig, 'nonce) stakeholder_state \<Rightarrow>
    slot \<Rightarrow>
    (('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) network_interface \<Rightarrow>
    ('skey, 'vkey, 'hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig, 'nonce) stakeholder_state \<Rightarrow> slot \<Rightarrow> process) \<Rightarrow>
    process"
where
  "start_of_slot ni ss sl \<K> \<equiv> (
    let
      (U, sk\<^sub>v\<^sub>r\<^sub>f, \<eta>, (_, \<S>\<^sub>0, _), \<C>) = (ss_id ss, ss_sk\<^sub>v\<^sub>r\<^sub>f ss, ss_\<eta> ss, ss_G ss, ss_\<C> ss)
    in (
      case is_slot_leader U sl sk\<^sub>v\<^sub>r\<^sub>f \<eta> \<S>\<^sub>0 \<C> of
          None \<Rightarrow>
            \<zero> \<parallel> \<K> ni ss sl \<comment> \<open>\<open>\<zero> \<parallel>\<close> is added to fulfill corecursive function requirements\<close>
        | Some v \<Rightarrow>
          let
            ss' = extend_chain ss sl v
          in
            (fst ni) \<triangleleft>\<degree> BroadcastChain (ss_\<C> ss') \<parallel> \<K> ni ss' sl))"

text \<open>
  Then we define a process that executes the `main loop' of the protocol:
\<close>

private corec
  main_loop :: "
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) network_interface \<Rightarrow>
    ('skey, 'vkey, 'hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig, 'nonce) stakeholder_state \<Rightarrow>
    slot \<Rightarrow>
    process"
where
  "main_loop ni ss sl =
    (snd ni) \<triangleright>\<degree> msg. (
      case msg of
        BroadcastTx tx \<Rightarrow> (
         \<comment> \<open>Store new transaction\<close>
          let
            ss' = store_tx ss tx
          in
            main_loop ni ss' sl)
      | BroadcastChain \<C> \<Rightarrow> (
         \<comment> \<open>Store new chain\<close>
          let
            ss' = store_chain sl \<C> ss
          in
            main_loop ni ss' sl)
      | BroadcastEndSlot sl\<^sub>n\<^sub>e\<^sub>x\<^sub>t \<Rightarrow> (
          let
            \<comment> \<open>If new epoch, compute and store new epoch randomness\<close>
            ss' = if first_in_epoch sl\<^sub>n\<^sub>e\<^sub>x\<^sub>t then compute_new_epoch_randomness sl\<^sub>n\<^sub>e\<^sub>x\<^sub>t ss else ss;
            \<comment> \<open>Update local chain\<close>
            ss' = update_local_chain ss'
          in
            start_of_slot ni ss' sl\<^sub>n\<^sub>e\<^sub>x\<^sub>t main_loop))"

text \<open>
  Finally, we define a process that implements a stakeholder running the protocol:
\<close>

fun
  stakeholder :: "
    stakeholder_id \<Rightarrow>
    ('vkey, 'nonce) genesis \<Rightarrow>
    'skey \<Rightarrow>
    'skey \<Rightarrow>
    'skey \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) network_interface \<Rightarrow>
    process"
where
  "stakeholder U\<^sub>i G sk\<^sub>v\<^sub>r\<^sub>f sk\<^sub>k\<^sub>e\<^sub>s sk\<^sub>d\<^sub>s\<^sub>i\<^sub>g ni = (
    let
      ss\<^sub>i\<^sub>n\<^sub>i\<^sub>t = init_stakeholder_state U\<^sub>i G sk\<^sub>v\<^sub>r\<^sub>f sk\<^sub>k\<^sub>e\<^sub>s sk\<^sub>d\<^sub>s\<^sub>i\<^sub>g
    in
      start_of_slot ni ss\<^sub>i\<^sub>n\<^sub>i\<^sub>t first_slot main_loop)"

end

end

subsection \<open> Proofs \<close>

subsubsection \<open> Slots and epochs \<close>

context protocol_parameters
begin

text \<open>
  A given epoch \<open>e\<^sub>j\<close> contains the interval of slots \<open>[(e\<^sub>j - 1) * R + 1, e\<^sub>j * R]\<close>:
\<close>

lemma slot_epoch_bounds:
  fixes n :: nat
  assumes "sl \<in> {n * R + 1..<Suc n * R + 1}"
  shows "slot_epoch sl = Suc n"
proof -
  let ?x = "sl / R"
  have "\<lceil>?x\<rceil> = Suc n \<longleftrightarrow> Suc n - 1 < ?x \<and> ?x \<le> Suc n"
    by (simp add: ceiling_eq_iff)
  moreover have "Suc n - 1 < ?x"
  proof -
    have "(n * R + 1) / R \<le> ?x"
    proof -
      have "0 < real R \<longrightarrow> real (n * R + 1) \<le> real sl"
      proof -
        have "(\<not> 0 < real R) = (real R \<le> 0)"
          by simp
        with assms show ?thesis
          by force
      qed
      then show ?thesis
        by (simp add: divide_le_cancel)
    qed
    moreover have "Suc n - 1 < (n * R + 1) / R"
      using R_positivity by (simp add: pos_less_divide_eq)
    ultimately show ?thesis
      by simp
  qed 
  moreover have "?x \<le> Suc n"
  proof -
    from assms have "sl \<le> Suc n * R"
      by simp
    then have "((of_nat sl)::real) \<le> of_nat ((Suc n) * R)"
      by (blast intro: of_nat_mono)
    also have "\<dots> = of_nat (Suc n) * of_nat R"
      by (blast intro: of_nat_mult)
    finally have "((of_nat sl)::real) \<le> of_nat (Suc n) * of_nat R" .
    moreover have "(0::real) < of_nat R"
      by (simp add: R_positivity)
    ultimately show ?thesis
      by (simp add: pos_divide_le_eq) 
  qed
  ultimately show ?thesis
    by simp
qed

notepad
begin
  assume "R = 2"
  then have "slot_epoch 1 = 1"
    and "slot_epoch 2 = 1"
    and "slot_epoch 3 = Suc 1"
    and "slot_epoch 4 = Suc 1"
    using slot_epoch_bounds by simp_all
end

end

subsubsection \<open> Stake distributions \<close>

context
begin

notepad
begin

  fix \<S> :: stake_distr and X :: "stakeholder_id set"
  assume a\<^sub>\<S>: "\<S> = {U\<^bsub>1\<^esub> $$:= 10, U\<^bsub>2\<^esub> $$:= 5, U\<^bsub>3\<^esub> $$:= 10}" and a\<^sub>X: "X = {U\<^bsub>1\<^esub>, U\<^bsub>3\<^esub>}"
  from a\<^sub>\<S> have "s\<^sup>+\<^sub>\<P>(\<S>) = 25"
  proof -
    from a\<^sub>\<S> have "fmdom' \<S> = {U\<^bsub>1\<^esub>, U\<^bsub>2\<^esub>, U\<^bsub>3\<^esub>}"
      by auto
    with a\<^sub>\<S> show ?thesis
      by simp
  qed
  moreover have "s\<^sup>+\<^bsub>X\<^esub>(\<S>) = 20"
  proof -
    from a\<^sub>\<S> and a\<^sub>X have "X \<subseteq> fmdom' \<S>"
      by simp
    with a\<^sub>\<S> and a\<^sub>X show ?thesis
      by simp
  qed
  moreover have "s\<^sup>+\<^bsub>U\<^bsub>1\<^esub>\<^esub>(\<S>) = 10"
  proof -
    from a\<^sub>\<S> have "{U\<^bsub>1\<^esub>} \<subseteq> fmdom' \<S>"
      by simp
    with a\<^sub>\<S> show ?thesis
      by simp
  qed
  ultimately have "\<alpha>\<^sup>+\<^bsub>U\<^bsub>1\<^esub>\<^esub>(\<S>) = 10/25" and "\<alpha>\<^sup>+\<^bsub>X\<^esub>(\<S>) = 20/25"
    using a\<^sub>\<S> by simp_all

end

end

subsubsection \<open> Transactions \<close>

context
begin

inductive
  tx_sts :: "
    stake_distr \<Rightarrow>
    'sig transaction \<Rightarrow>
    stake_distr \<Rightarrow>
    bool"
  (\<open>_ \<rightarrow>{_} _\<close> [51, 0, 51] 50)
where
  tx_sts_base:
    "\<S> \<rightarrow>{tx} \<S>'"
      if "((U\<^sub>i, U\<^sub>j, s), _) = tx"
      and "{U\<^sub>i, U\<^sub>j} \<subseteq> fmdom' \<S>"
      and "\<S> $$! U\<^sub>i \<ge> s"
      \<comment> \<open>\<open>\<S>\<close>''\<close>
      and "fmdom' \<S>'' = fmdom' \<S>"
      and "\<S>'' $$! U\<^sub>i = \<S> $$! U\<^sub>i - s"
      and "\<forall>U \<in> fmdom' \<S>''. U \<noteq> U\<^sub>i \<longrightarrow> \<S>'' $$! U = \<S> $$! U"
      \<comment> \<open>\<open>\<S>\<close>'\<close>
      and "fmdom' \<S>' = fmdom' \<S>"
      and "\<S>' $$! U\<^sub>j = \<S>'' $$! U\<^sub>j + s"
      and "\<forall>U \<in> fmdom' \<S>'. U \<noteq> U\<^sub>j \<longrightarrow> \<S>' $$! U = \<S>'' $$! U"

lemma apply_transaction_soundness:
  assumes "apply_transaction tx \<S> = \<S>'"
  and "((U\<^sub>i, U\<^sub>j, s), \<sigma>) = tx"
  and "{U\<^sub>i, U\<^sub>j} \<subseteq> fmdom' \<S>"
  and "\<S> $$! U\<^sub>i \<ge> s"
  shows "\<S> \<rightarrow>{tx} \<S>'"
proof -
  let ?\<S>'' = "\<S>(U\<^sub>i $$:= \<S> $$! U\<^sub>i - s)"
  from assms(3) have "fmdom' ?\<S>'' = fmdom' \<S>"
    by auto
  moreover have "?\<S>'' $$! U\<^sub>i = \<S> $$! U\<^sub>i - s"
    by simp
  moreover have "?\<S>'' $$! U = \<S> $$! U" if "U \<in> fmdom' ?\<S>''" and "U \<noteq> U\<^sub>i" for U
    using \<open>U \<noteq> U\<^sub>i\<close> by auto
  moreover from assms have "fmdom' \<S>' = fmdom' \<S>"
    by auto
  moreover from assms have "\<S>' $$! U\<^sub>j = ?\<S>'' $$! U\<^sub>j + s"
    by auto
  moreover from assms have "\<S>' $$! U = ?\<S>'' $$! U" if "U \<in> fmdom' \<S>'" and "U \<noteq> U\<^sub>j" for U
    using \<open>U \<noteq> U\<^sub>j\<close> by auto
  ultimately show ?thesis
    using assms(2-4) and tx_sts.simps[of \<S> tx \<S>'] by metis
qed

lemma apply_transaction_completeness:
  assumes "\<S> \<rightarrow>{tx} \<S>'"
  shows "apply_transaction tx \<S> = \<S>'"
proof -
  from assms show ?thesis
  proof cases
    case (tx_sts_base U\<^sub>i U\<^sub>j s _ \<S>'')
    then show ?thesis
    proof (intro fsubset_antisym)
      show "apply_transaction tx \<S> \<subseteq>\<^sub>f \<S>'"
      unfolding fmsubset.rep_eq proof (unfold map_le_def, intro ballI)
        fix U
        assume *: "U \<in> dom (($$) (apply_transaction tx \<S>))"
        then show "apply_transaction tx \<S> $$ U = \<S>' $$ U"
        proof (cases "U \<in> dom (($$) \<S>)")
          case True
          from tx_sts_base(1,2,3) have "apply_transaction tx \<S> $$ U =
            (let \<S>\<^sub>1 = \<S>(U\<^sub>i $$:= \<S> $$! U\<^sub>i - s) in \<S>\<^sub>1(U\<^sub>j $$:= \<S>\<^sub>1 $$! U\<^sub>j + s)) $$ U"
            by auto
          also have "\<dots> = Some (\<S>' $$! U)"
          proof -
            consider (a) "U = U\<^sub>i" | (b) "U = U\<^sub>j" | (c) "U \<noteq> U\<^sub>i" and "U \<noteq> U\<^sub>j"
              by auto
            then show ?thesis
              using True and tx_sts_base(4-9) by cases (auto simp add: fmlookup_dom'_iff)
          qed
          also have "\<dots> = \<S>' $$ U"
          proof -
            from True and tx_sts_base(7) have "U \<in> fmdom' \<S>'"
              by simp
            then show ?thesis
              by (simp add: fmlookup_dom'_iff)
          qed
          finally show "apply_transaction tx \<S> $$ U = \<S>' $$ U" .
        next
          case False
          with * and tx_sts_base(1,2,3) show ?thesis
            by auto
        qed
      qed
      then show "\<S>' \<subseteq>\<^sub>f apply_transaction tx \<S>"
      unfolding fmsubset.rep_eq proof (unfold map_le_def, intro ballI)
        fix U
        assume *: "U \<in> dom (($$) \<S>')"
        then show "\<S>' $$ U = apply_transaction tx \<S> $$ U"
        proof -
          from tx_sts_base(1,2,3) have "dom (($$) (apply_transaction tx \<S>)) =
            insert U\<^sub>j (fmdom' (\<S>(U\<^sub>i $$:= \<S> $$! U\<^sub>i - s)))"
            by auto
          with * and tx_sts_base(7) have "U \<in> dom (($$) (apply_transaction tx \<S>))"
            by simp
          with \<open>apply_transaction tx \<S> \<subseteq>\<^sub>f \<S>'\<close> show ?thesis
            by (simp add: fmsubset.rep_eq map_le_def)
        qed
      qed
    qed
  qed
qed

text \<open>
  Applying a transaction with the same stakeholder as sender and recipient does not change the
  stake distribution:
\<close>

lemma self_transfer_invariancy:
  assumes "U\<^sub>i \<in> fmdom' \<S>"
  and "\<S> $$! U\<^sub>i \<ge> s"
  shows "apply_transaction ((U\<^sub>i, U\<^sub>i, s), \<sigma>) \<S> = \<S>"
  using assms
proof (intro fsubset_antisym)
  let ?\<S>' = "apply_transaction ((U\<^sub>i, U\<^sub>i, s), \<sigma>) \<S>"
  show "?\<S>' \<subseteq>\<^sub>f \<S>"
  unfolding fmsubset.rep_eq proof (unfold map_le_def, intro ballI)
    fix U
    assume "U \<in> dom (($$) ?\<S>')"
    then show "?\<S>' $$ U = \<S> $$ U"
    proof (cases "U = U\<^sub>i")
      case True
      with assms have "?\<S>' $$ U = Some (\<S> $$! U - s + s)"
        by simp
      also from True and assms have "\<dots> = \<S> $$ U"
        by (simp add: fmlookup_dom'_iff)
      finally show ?thesis .
    next
      case False
      with assms show ?thesis
        by simp
    qed
  qed
  with assms show "\<S> \<subseteq>\<^sub>f apply_transaction ((U\<^sub>i, U\<^sub>i, s), \<sigma>) \<S>"
    unfolding fmsubset.rep_eq and map_le_def by simp
qed

end

subsubsection \<open> Blocks \<close>

context
begin

inductive
  txs_sts :: "
    stake_distr \<Rightarrow>
    'sig transaction list \<Rightarrow>
    stake_distr \<Rightarrow>
    bool"
  (\<open>_ \<rightarrow>\<^sup>*{_} _\<close> [51, 0, 51] 50)
where
  txs_sts_base:
    "\<S> \<rightarrow>\<^sup>*{[]} \<S>"
| txs_sts_ind:
    "\<S> \<rightarrow>\<^sup>*{txs @ [tx]} \<S>'"
      if "\<S> \<rightarrow>\<^sup>*{txs} \<S>''"
      and "\<S>'' \<rightarrow>{tx} \<S>'"

abbreviation
  bl_sts :: "
    stake_distr \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) block \<Rightarrow>
    stake_distr \<Rightarrow>
    bool"
  (\<open>_ \<rightarrow>\<^sub>b{_} _\<close> [51, 0, 51] 50)
where
  "\<S> \<rightarrow>\<^sub>b{B} \<S>' \<equiv> \<S> \<rightarrow>\<^sup>*{bl_txs B} \<S>'"

definition
  are_applicable_txs :: "'sig transaction list \<Rightarrow> stake_distr \<Rightarrow> bool"
where
  [iff]: "are_applicable_txs txs \<S> \<longleftrightarrow> (\<forall>\<S>'' U\<^sub>i U\<^sub>j s. \<forall>i \<in> {0..<length txs}.
    (U\<^sub>i, U\<^sub>j, s) = fst (txs ! i) \<and> \<S> \<rightarrow>\<^sup>*{take i txs} \<S>'' \<longrightarrow> \<S>'' $$! U\<^sub>i \<ge> s)"

lemma txs_init_is_applicable:
  assumes "are_applicable_txs txs \<S>"
  shows "are_applicable_txs (butlast txs) \<S>"
  using assms
proof (unfold are_applicable_txs_def, intro allI ballI impI, elim conjE)
  fix \<S>'' U\<^sub>i U\<^sub>j s i
  let ?txs' = "butlast txs"
  assume a\<^sub>1: "i \<in> {0..<length ?txs'}"
     and a\<^sub>2: "(U\<^sub>i, U\<^sub>j, s) = fst (?txs' ! i)"
     and a\<^sub>3: "\<S> \<rightarrow>\<^sup>*{take i ?txs'} \<S>''"
  from a\<^sub>1 have *: "i \<in> {0..<length txs}"
    by simp
  moreover from * and a\<^sub>1 and a\<^sub>2 have "(U\<^sub>i, U\<^sub>j, s) = fst (txs ! i)"
    by (simp add: nth_butlast)
  moreover from * and a\<^sub>3 have "\<S> \<rightarrow>\<^sup>*{take i txs} \<S>''"
    by (simp add: take_butlast)
  ultimately show "\<S>'' $$! U\<^sub>i \<ge> s"
    using assms by blast
qed

abbreviation
  are_known_stakeholders :: "'sig transaction list \<Rightarrow> stake_distr \<Rightarrow> bool"
where
  "are_known_stakeholders txs \<S> \<equiv> \<forall>((U\<^sub>i, U\<^sub>j, _), _) \<in> set txs. {U\<^sub>i, U\<^sub>j} \<subseteq> fmdom' \<S>"

lemma fold_apply_transaction_fmdom':
  assumes "are_known_stakeholders txs \<S>"
  shows "fmdom' (fold apply_transaction txs \<S>) = fmdom' \<S>"
  using assms
proof (induction txs arbitrary: \<S>)
  case Nil
  then show ?case
    by simp
next
  case (Cons tx txs)
  let ?\<S>' = "apply_transaction tx \<S>"
  obtain U\<^sub>i U\<^sub>j s \<sigma> where *: "tx = ((U\<^sub>i, U\<^sub>j, s), \<sigma>)"
    by (metis prod.collapse)
  have "fmdom' (fold apply_transaction (tx # txs) \<S>) = fmdom' (fold apply_transaction txs ?\<S>')"
    by simp
  also from Cons.prems and Cons.IH and * have "\<dots> = fmdom' \<S>"
    by (simp add: insert_absorb)
  finally show ?case .
qed

lemma fold_apply_transaction_soundness:
  assumes "fold apply_transaction txs \<S> = \<S>'"
  and "are_applicable_txs txs \<S>"
  and "are_known_stakeholders txs \<S>"
  shows "\<S> \<rightarrow>\<^sup>*{txs} \<S>'"
  using assms
proof (induction txs arbitrary: \<S>' rule: rev_induct)
  case Nil
  then show ?case
    by (simp add: txs_sts_base)
next
  case (snoc tx txs)
  let ?\<S>'' = "fold apply_transaction txs \<S>"
  have f\<^sub>1: "\<S> \<rightarrow>\<^sup>*{txs} ?\<S>''"
  proof -
    from snoc.prems(2) have "are_applicable_txs txs \<S>"
      using txs_init_is_applicable[of "txs @ [tx]" \<S>] by fastforce
    moreover from snoc.prems(3) have "are_known_stakeholders txs \<S>"
      by simp
    ultimately show ?thesis
      using snoc.IH by simp
  qed
  moreover have "?\<S>'' \<rightarrow>{tx} \<S>'"
  proof -
    obtain U\<^sub>i U\<^sub>j s \<sigma> where f\<^sub>2: "tx = ((U\<^sub>i, U\<^sub>j, s), \<sigma>)"
      by (metis prod.collapse)
    moreover from snoc.prems(1) have "apply_transaction tx ?\<S>'' = \<S>'"
      by simp
    moreover have "{U\<^sub>i, U\<^sub>j} \<subseteq> fmdom' ?\<S>''"
    proof -
      from f\<^sub>2 and snoc.prems(3) have "{U\<^sub>i, U\<^sub>j} \<subseteq> fmdom' \<S>"
        by simp
      with snoc.prems(3) show ?thesis
        by (simp add: fold_apply_transaction_fmdom')
    qed
    moreover have "?\<S>'' $$! U\<^sub>i \<ge> s"
    proof -
      let ?txs = "txs @ [tx]"
      let ?i = "length ?txs - 1"
      have "?i \<in> {0..<length ?txs}"
        by simp
      moreover from f\<^sub>2 have "(U\<^sub>i, U\<^sub>j, s) = fst (?txs ! ?i)"
        by simp
      moreover from f\<^sub>1 have "\<S> \<rightarrow>\<^sup>*{take ?i ?txs} ?\<S>''"
        by simp
      ultimately show ?thesis
        using snoc.prems(2) by blast
    qed
    ultimately show ?thesis
      by (simp add: apply_transaction_soundness)
  qed
  ultimately show ?case
    by (blast intro: txs_sts_ind)
qed

corollary apply_block_soundness:
  assumes "apply_block B \<S> = \<S>'"
  and "txs = bl_txs B"
  and "are_applicable_txs txs \<S>"
  and "are_known_stakeholders txs \<S>"
  shows "\<S> \<rightarrow>\<^sub>b{B} \<S>'"
  using assms and fold_apply_transaction_soundness by simp

lemma fold_apply_transaction_completeness:
  assumes "\<S> \<rightarrow>\<^sup>*{txs} \<S>'"
  shows "fold apply_transaction txs \<S> = \<S>'"
  using assms
  by induction (simp_all add: apply_transaction_completeness)

corollary apply_block_completeness:
  assumes "\<S> \<rightarrow>\<^sub>b{B} \<S>'"
  shows "apply_block B \<S> = \<S>'"
  using assms and fold_apply_transaction_completeness unfolding apply_block_def by blast

text \<open>
  Applying a block including only a transaction and its corresponding refund transaction does not
  affect the stake distribution:
\<close>

lemma transaction_refund_invariancy:
  assumes "bl_txs B = [((U\<^sub>i, U\<^sub>j, s), \<sigma>\<^sub>1), ((U\<^sub>j, U\<^sub>i, s), \<sigma>\<^sub>2)]"
  and "{U\<^sub>i, U\<^sub>j} \<subseteq> fmdom' \<S>"
  and "\<S> $$! U\<^sub>i \<ge> s"
  shows "apply_block B \<S> = \<S>"
proof -
  let ?\<S>\<^sub>1 = "\<S>(U\<^sub>i $$:= \<S> $$! U\<^sub>i - s)"
  let ?\<S>\<^sub>2 = "?\<S>\<^sub>1(U\<^sub>j $$:= ?\<S>\<^sub>1 $$! U\<^sub>j + s)"
  let ?\<S>\<^sub>3 = "?\<S>\<^sub>2(U\<^sub>j $$:= ?\<S>\<^sub>2 $$! U\<^sub>j - s)"
  let ?\<S>\<^sub>4 = "?\<S>\<^sub>3(U\<^sub>i $$:= ?\<S>\<^sub>3 $$! U\<^sub>i + s)"
  from assms(1) have "apply_block B \<S> =
    fold apply_transaction [((U\<^sub>j, U\<^sub>i, s), \<sigma>\<^sub>2)] (apply_transaction ((U\<^sub>i, U\<^sub>j, s), \<sigma>\<^sub>1) \<S>)"
    by simp
  also have "\<dots> = fold apply_transaction [((U\<^sub>j, U\<^sub>i, s), \<sigma>\<^sub>2)] ?\<S>\<^sub>2"
    by simp
  also have "\<dots> = ?\<S>\<^sub>4"
    by simp
  also have "\<dots> = \<S>"
  proof (rule fsubset_antisym)
    show "?\<S>\<^sub>4 \<subseteq>\<^sub>f \<S>"
    unfolding fmsubset.rep_eq proof (unfold map_le_def, intro ballI)
      fix U
      assume "U \<in> dom (($$) ?\<S>\<^sub>4)"
      consider (a) "U = U\<^sub>i" | (b) "U = U\<^sub>j" | (c) "U \<noteq> U\<^sub>i" and "U \<noteq> U\<^sub>j"
        by auto
      then show "?\<S>\<^sub>4 $$ U = \<S> $$ U"
      proof cases
        case a
        then have "?\<S>\<^sub>4 $$ U = Some (\<S> $$! U - s + s)"
          by simp
        also from a and assms(2,3) have "\<dots> = \<S> $$ U"
          by (simp add: fmlookup_dom'_iff)
        finally show ?thesis .
      next
        case b
        with assms(3) have "?\<S>\<^sub>4 $$ U = Some (\<S> $$! U + s - s)"
          by auto
        also from b and assms(2) have "\<dots> = \<S> $$ U"
          by (simp add: fmlookup_dom'_iff)
        finally show ?thesis .
      next
        case c
        then show ?thesis
          by simp
      qed
    qed
    show "\<S> \<subseteq>\<^sub>f ?\<S>\<^sub>4"
      using \<open>?\<S>\<^sub>4 \<subseteq>\<^sub>f \<S>\<close> unfolding fmsubset.rep_eq and map_le_def by auto
  qed
  finally show ?thesis .
qed

end

subsubsection \<open> Chains \<close>

inductive
  chain_sts :: "
    stake_distr \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    stake_distr \<Rightarrow>
    bool"
  (\<open>_ \<rightarrow>\<^sub>c{_} _\<close> [51, 0, 51] 50)
where
  chain_sts_base:
    "\<S> \<rightarrow>\<^sub>c{[]} \<S>"
| chain_sts_ind:
    "\<S> \<rightarrow>\<^sub>c{\<C> @ [B]} \<S>'"
      if "\<S> \<rightarrow>\<^sub>c{\<C>} \<S>''"
      and "\<S>'' \<rightarrow>\<^sub>b{B} \<S>'"

abbreviation chain_txs :: "('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow> ('sig transaction) list" where
  "chain_txs \<equiv> List.concat \<circ> map bl_txs"

lemma apply_chain_txs_is_apply_chain:
  shows "fold apply_transaction (chain_txs \<C>) \<S> = apply_chain \<C> \<S>"
  by (induction \<C> arbitrary: \<S>) (unfold apply_block_def apply_chain_def, simp_all)

lemma fold_apply_block_fmdom':
  assumes "\<forall>B \<in> set \<C>. are_known_stakeholders (bl_txs B) \<S>"
  shows "fmdom' (fold apply_block \<C> \<S>) = fmdom' \<S>"
  using assms
proof (induction \<C> arbitrary: \<S>)
  case Nil
  then show ?case
    by simp
next
  case (Cons B \<C>)
  let ?\<S>' = "apply_block B \<S>"
  have "fmdom' (fold apply_block (B # \<C>) \<S>) = fmdom' (fold apply_block \<C> ?\<S>')"
    by simp
  also from Cons.prems and Cons.IH have "\<dots> = fmdom' \<S>"
    unfolding apply_block_def by (simp add: fold_apply_transaction_fmdom')
  finally show ?case .
qed

lemma tx_append_applicability:
  assumes "are_applicable_txs [tx] (fold apply_transaction txs \<S>)"
    and "are_applicable_txs txs \<S>"
  shows "are_applicable_txs (txs @ [tx]) \<S>"
  using assms
proof (unfold are_applicable_txs_def, intro allI ballI impI, elim conjE)
  fix \<S>'' U\<^sub>i U\<^sub>j s i
  assume a\<^sub>1: "i \<in> {0..<length (txs @ [tx])}"
     and a\<^sub>2: "(U\<^sub>i, U\<^sub>j, s) = fst ((txs @ [tx]) ! i)"
     and a\<^sub>3: "\<S> \<rightarrow>\<^sup>*{take i (txs @ [tx])} \<S>''"
  then show "s \<le> \<S>'' $$! U\<^sub>i"
  proof (cases "i < length txs")
    case True
    from True have "i \<in> {0..<length txs}"
      by simp
    moreover from True and a\<^sub>2 have "(U\<^sub>i, U\<^sub>j, s) = fst (txs ! i)"
      by (simp add: nth_append)
    moreover from True and a\<^sub>3 have "\<S> \<rightarrow>\<^sup>*{take i txs} \<S>''"
      by simp
    ultimately show ?thesis
      using assms(2) by blast
  next
    case False
    from False and a\<^sub>1 and a\<^sub>2 have "(U\<^sub>i, U\<^sub>j, s) = fst tx"
      by (simp add: less_Suc_eq)
    moreover from False and a\<^sub>1 and a\<^sub>3 have "\<S> \<rightarrow>\<^sup>*{txs} \<S>''"
      by simp
    then have "fold apply_transaction txs \<S> = \<S>''"
      by (rule fold_apply_transaction_completeness)
    then have "fold apply_transaction txs \<S> \<rightarrow>\<^sup>*{[]} \<S>''"
      using fold_apply_transaction_soundness and txs_sts_base by simp
    ultimately show ?thesis
      using assms(1) and a\<^sub>1 by auto
  qed
qed

lemma last_tx_applicability:
  assumes "are_applicable_txs (txs @ [tx]) \<S>"
    and "are_known_stakeholders txs \<S>"
  shows "are_applicable_txs [tx] (fold apply_transaction txs \<S>)"
  using assms
proof (unfold are_applicable_txs_def, intro allI ballI impI, elim conjE)
  fix \<S>'' U\<^sub>i U\<^sub>j s i
  assume a\<^sub>1: "i \<in> {0..<length [tx]}"
     and a\<^sub>2: "(U\<^sub>i, U\<^sub>j, s) = fst ([tx] ! i)"
     and a\<^sub>3: "fold apply_transaction txs \<S> \<rightarrow>\<^sup>*{take i [tx]} \<S>''"
  from a\<^sub>1 have f\<^sub>1: "i = 0"
    by simp
  moreover from a\<^sub>2 and f\<^sub>1 have f\<^sub>2: "(U\<^sub>i, U\<^sub>j, s) = fst tx"
    by simp
  moreover from a\<^sub>3 and f\<^sub>1 have "fold apply_transaction txs \<S> \<rightarrow>\<^sup>*{[]} \<S>''"
    using fold_apply_transaction_completeness and txs_sts_base by fastforce
  then have f\<^sub>3: "fold apply_transaction txs \<S> = \<S>''"
    using fold_apply_transaction_completeness by force
  ultimately have "\<S> \<rightarrow>\<^sup>*{txs} \<S>''"
  proof -
    from assms(1) have "are_applicable_txs txs \<S>"
      using txs_init_is_applicable by fastforce 
    moreover from assms(2) have "are_known_stakeholders txs \<S>"
      by blast
    ultimately show ?thesis
      using f\<^sub>3 and fold_apply_transaction_soundness by simp
  qed
  with assms(1) and f\<^sub>2 show "s \<le> \<S>'' $$! U\<^sub>i"
    by force
qed

lemma txs_prefix_applicability:
  assumes "are_applicable_txs txs \<S>"
    and "n \<in> {0..length txs}"
  shows "are_applicable_txs (take n txs) \<S>"
  using assms
proof (unfold are_applicable_txs_def, intro allI ballI impI, elim conjE)
  fix \<S>'' U\<^sub>i U\<^sub>j s i
  assume a\<^sub>1: "i \<in> {0..<length (take n txs)}"
     and a\<^sub>2: "(U\<^sub>i, U\<^sub>j, s) = fst ((take n txs) ! i)"
     and a\<^sub>3: "\<S> \<rightarrow>\<^sup>*{take i (take n txs)} \<S>''"
  then show "s \<le> \<S>'' $$! U\<^sub>i"
  proof (cases "i < n")
    case True
    then show ?thesis
    proof -
      from True and a\<^sub>2 have "(U\<^sub>i, U\<^sub>j, s) = fst (txs ! i)"
        by simp
      moreover from a\<^sub>1 have "i < length txs"
        by simp
      moreover from True and a\<^sub>3 have "\<S> \<rightarrow>\<^sup>*{take i txs} \<S>''"
        by (simp add: min.strict_order_iff)
      ultimately show ?thesis
        using assms(1) by fastforce
    qed
  next
    case False
    with a\<^sub>1 show ?thesis
      by simp 
  qed
qed

lemma singleton_last_block_applicability:
  assumes "bl_txs B = [tx]"
    and "are_applicable_txs (chain_txs (\<C> @ [B])) \<S>"
    and "are_known_stakeholders (chain_txs \<C>) \<S>"
  shows "are_applicable_txs [tx] (fold apply_block \<C> \<S>)"
proof -
  from assms(1,2) have "are_applicable_txs (chain_txs \<C> @ [tx]) \<S>"
    by simp
  with assms(2,3) have "are_applicable_txs [tx] (fold apply_transaction (chain_txs \<C>) \<S>)"
    using last_tx_applicability by metis
  then show ?thesis
    using apply_chain_txs_is_apply_chain unfolding apply_chain_def by metis
qed

lemma last_tx_in_last_block_applicability:
  fixes txs :: "'sig transaction list"
    and B :: "('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) block"
  assumes "bl_txs B = txs @ [tx]"
    and "are_applicable_txs (chain_txs (\<C> @ [B])) \<S>"
    and "are_known_stakeholders (chain_txs (\<C> @ [B])) \<S>"
  shows "are_applicable_txs [tx] (fold apply_transaction txs (fold apply_block \<C> \<S>))"
  using assms
proof (induction txs arbitrary: B \<C>)
  case Nil
  from Nil.prems(1) have "bl_txs B = [tx]"
    by simp
  moreover from Nil.prems(3) have "are_known_stakeholders (chain_txs \<C>) \<S>"
    by simp
  ultimately have "are_applicable_txs [tx] (fold apply_block \<C> \<S>)"
    using Nil.prems(2) and singleton_last_block_applicability by metis
  then show ?case
    by (metis fold_simps(1))
next
  case (Cons tx' txs')
  let ?\<S>' = "fold apply_block \<C> \<S>"
  obtain B' :: "('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) block" where f1: "bl_txs B' = txs' @ [tx]"
    by force
  obtain B'' :: "('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) block" where f2: "bl_txs B'' = [tx']"
    by force
  from f2 have "fold apply_transaction (tx' # txs') ?\<S>' =
    fold apply_transaction txs' (apply_block B'' ?\<S>')"
    by simp
  also have "\<dots> = fold apply_transaction txs' (fold apply_block (\<C> @ [B'']) \<S>)"
    by simp
  finally have "are_applicable_txs [tx] (fold apply_transaction (tx' # txs') ?\<S>') =
    are_applicable_txs [tx] (fold apply_transaction txs' (fold apply_block (\<C> @ [B'']) \<S>))"
    by simp
  moreover from Cons.prems(1,2) and f1 and f2
  have "are_applicable_txs (chain_txs ((\<C> @ [B'']) @ [B'])) \<S>"
    by simp
  moreover from Cons.prems(1,3) and f1 and f2
  have "are_known_stakeholders (chain_txs (((\<C> @ [B'']) @ [B']))) \<S>"
    by simp
  ultimately show ?case
    using f1 and Cons.IH by presburger
qed

lemma last_block_applicability:
  fixes txs :: "'sig transaction list"
    and B :: "('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) block"
  assumes "bl_txs B = txs" 
    and "are_applicable_txs (chain_txs (\<C> @ [B])) \<S>"
    and "are_known_stakeholders (chain_txs (\<C> @ [B])) \<S>"
  shows "are_applicable_txs txs (fold apply_block \<C> \<S>)"
  using assms
proof (induction txs arbitrary: B rule: rev_induct)
  case Nil
  then show ?case
    unfolding are_applicable_txs_def by simp
next
  case (snoc tx txs)
  obtain B' :: "('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) block" where f1: "txs = bl_txs B'"
    by force
  have "are_applicable_txs [tx] (fold apply_transaction txs (fold apply_block \<C> \<S>))"
  proof -
    from snoc.prems(3) have "are_known_stakeholders (chain_txs (\<C> @ [B])) \<S>"
      by simp
    with snoc.prems(1,2) show ?thesis
      using last_tx_in_last_block_applicability by metis
  qed
  moreover have "are_applicable_txs txs (fold apply_block \<C> \<S>)"
  proof -
    from snoc.prems(1,2) and f1 have "are_applicable_txs (chain_txs (\<C> @ [B'])) \<S>"
      using txs_init_is_applicable[of "chain_txs \<C> @ txs @ [tx]" \<S>]
      by (simp add: butlast_append)
    moreover from snoc.prems(1,3) and f1 have "are_known_stakeholders (chain_txs (\<C> @ [B'])) \<S>"
      by simp
    ultimately show ?thesis
      using snoc.IH and f1 by blast
  qed
  ultimately show ?case
    using tx_append_applicability by metis
qed

theorem apply_chain_soundness:
  assumes "apply_chain \<C> \<S> = \<S>'"
    and "are_applicable_txs (List.concat (map bl_txs \<C>)) \<S>"
    and "are_known_stakeholders (List.concat (map bl_txs \<C>)) \<S>"
  shows "\<S> \<rightarrow>\<^sub>c{\<C>} \<S>'"
  using assms
proof (induction \<C> arbitrary: \<S>' rule: rev_induct)
  case Nil
  then show ?case
    using chain_sts_base by simp
next
  case (snoc B \<C>)
  let ?\<S>'' = "apply_chain \<C> \<S>"
  have "\<S> \<rightarrow>\<^sub>c{\<C>} ?\<S>''"
  proof -
    have "are_applicable_txs (chain_txs \<C>) \<S>"
    proof -
      from snoc.prems(2) have "are_applicable_txs (chain_txs \<C> @ bl_txs B) \<S>"
        by simp
      moreover have "length (chain_txs \<C>) \<in> {0..length (chain_txs \<C> @ bl_txs B)}"
        by simp
      ultimately have "are_applicable_txs (take (length (chain_txs \<C>)) (chain_txs \<C> @ bl_txs B)) \<S>"
        using txs_prefix_applicability by metis
      then show ?thesis
        by simp
    qed
    moreover from snoc.prems(3) have "are_known_stakeholders (chain_txs \<C>) \<S>"
      by simp
    ultimately show ?thesis
      using snoc.IH by simp
  qed
  moreover have "?\<S>'' \<rightarrow>\<^sub>b{B} \<S>'"
  proof -
    from snoc(2) have "apply_block B ?\<S>'' = \<S>'"
      by simp
    moreover from snoc.prems(2,3) have "are_applicable_txs (bl_txs B) ?\<S>''"
      unfolding apply_chain_def using last_block_applicability by (metis comp_apply) 
    moreover have "are_known_stakeholders (bl_txs B) ?\<S>''"
    proof -
      from snoc.prems(3) have "are_known_stakeholders (chain_txs \<C>) \<S>"
        by simp
      then have "fmdom' (fold apply_transaction (chain_txs \<C>) \<S>) = fmdom' \<S>"
        using fold_apply_transaction_fmdom' by blast
      then have "fmdom' (apply_chain \<C> \<S>) = fmdom' \<S>"
        using apply_chain_txs_is_apply_chain by metis
      with snoc.prems(3) show ?thesis
        by simp
    qed
    ultimately show ?thesis
      by (simp add: apply_block_soundness)
  qed
  ultimately show ?case
    using chain_sts_ind by blast
qed

corollary apply_chain_completeness:
  assumes "\<S> \<rightarrow>\<^sub>c{\<C>} \<S>'"
  shows "apply_chain \<C> \<S> = \<S>'"
  using assms unfolding apply_chain_def 
proof induction
  case chain_sts_base
  then show ?case
    by simp
next
  case (chain_sts_ind \<S> _ \<S>'' B \<S>')
  from \<open>\<S>'' \<rightarrow>\<^sub>b{B} \<S>'\<close> have "apply_block B \<S>'' = \<S>'"
    by (rule apply_block_completeness)
  with chain_sts_ind.IH show ?case
    by simp
qed

text \<open>
  For the sake of simplicity, we regard a chain as @{emph \<open>valid\<close>} whenever it contains a
  strictly increasing sequence of slots:
\<close>

abbreviation
  is_slot_increasing :: "('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow> bool"
where
  "is_slot_increasing \<C> \<equiv> sorted_wrt (\<lambda>B B'. bl_slot B < bl_slot B') \<C>"

abbreviation
  is_valid_chain :: "('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow> bool"
where
  "is_valid_chain \<C> \<equiv> is_slot_increasing \<C>"

text \<open>
  A prefix of a valid chain is a valid chain:
\<close>

lemma chain_prefix_validity:
  assumes "is_valid_chain \<C>\<^sub>2"
    and "\<C>\<^sub>1 \<preceq> \<C>\<^sub>2"
  shows "is_valid_chain \<C>\<^sub>1"
  using assms and sorted_wrt_append unfolding prefix_def by blast

text \<open>
  A prefix of a chain keeps all properties on its elements that hold for the original chain:
\<close>

lemma prefix_invariancy:
  assumes "\<forall>B \<in> set \<C>\<^sub>2. P B"
  and "\<C>\<^sub>1 \<preceq> \<C>\<^sub>2"
  shows "\<forall>B \<in> set \<C>\<^sub>1. P B"
  using assms
proof (intro ballI)
  fix B
  assume "B \<in> set \<C>\<^sub>1"
  from assms(2) have "\<exists>\<C>\<^sub>3. \<C>\<^sub>2 = \<C>\<^sub>1 @ \<C>\<^sub>3"
    by (blast dest: prefixE)
  with \<open>B \<in> set \<C>\<^sub>1\<close> have "B \<in> set \<C>\<^sub>2"
    by auto
  with assms(1) show "P B"
    by simp
qed

text \<open>
  The \<open>\<C>\<^bsup>\<lceil>m\<^esup>\<close> operator satisfies some simple laws:
\<close>

lemma zero_blocks_chain_prunning_identity:
  shows "\<C>\<^sup>\<lceil>\<^bsup>0\<^esup> = \<C>"
  by simp

lemma long_chain_prunning_emptiness:
  assumes "m \<ge> length \<C>"
  shows "\<C>\<^sup>\<lceil>\<^bsup>m\<^esup> = []"
  using assms by simp

lemma append_prune_chain_drop_identity:
  shows "\<C>\<^sup>\<lceil>\<^bsup>m\<^esup> @ drop (length \<C> - m) \<C> = \<C>"
  by simp

text \<open>
  Now we prove some properties about @{const prune_after}. As expected, chain validity is
  preserved by @{const prune_after}:
\<close>

lemma prune_after_validity_invariancy:
  assumes "is_valid_chain \<C>"
  shows "is_valid_chain (prune_after sl \<C>)"
  using assms unfolding prune_after_def
  by (metis (no_types, lifting) sorted_wrt_append takeWhile_dropWhile_id)

text \<open>
  And the pruned chain returned by @{const prune_after} is obviously a prefix of the original chain:
\<close>

lemma prune_after_is_prefix:
  shows "prune_after sl \<C> \<preceq> \<C>"
proof -
  let ?P = "\<lambda>B. bl_slot B \<le> sl"
  have "\<C> = takeWhile ?P \<C> @ dropWhile ?P \<C>"
    by simp
  then have "\<exists>\<C>'. \<C> = prune_after sl \<C> @ \<C>'"
    unfolding prune_after_def by blast
  then show ?thesis
    by (blast intro: prefixI)
qed

text \<open>
  Now, we define two auxiliary predicates: One predicate to check whether the slots in a chain are
  bounded by a given slot, and another predicate to check whether a chain is both a prefix of a
  given chain and bounded by a given slot:
\<close>

abbreviation
  is_slot_bounded_chain :: "('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow> slot \<Rightarrow> bool" (infix \<open>\<unlhd>\<close> 50)
where
  "\<C> \<unlhd> sl \<equiv> \<forall>B \<in> set \<C>. bl_slot B \<le> sl"

abbreviation
  is_slot_bounded_prefix :: "
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    slot \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    bool"
where
  "is_slot_bounded_prefix \<C>\<^sub>1 sl \<C>\<^sub>2 \<equiv> \<C>\<^sub>1 \<preceq> \<C>\<^sub>2 \<and> \<C>\<^sub>1 \<unlhd> sl"

text \<open>
  Any chain \<open>\<C>\<^sub>1\<close> which is a subsequence of another chain \<open>\<C>\<^sub>2\<close> that is slot-bounded by \<open>sl\<close> is also
  slot-bounded by \<open>sl\<close>:
\<close>

lemma subseq_is_slot_bounded:
  assumes "subseq \<C>\<^sub>1 \<C>\<^sub>2"
    and "\<C>\<^sub>2 \<unlhd> sl"
  shows "\<C>\<^sub>1 \<unlhd> sl"
  using assms
  by (metis (mono_tags, lifting) list_emb_set)

text \<open>
  The tail of a chain that is slot-bounded by \<open>sl\<close> is also slot-bounded by \<open>sl\<close>:
\<close>

lemma tail_is_slot_bounded:
  assumes "\<C> \<unlhd> sl"
  shows "tl \<C> \<unlhd> sl"
  using assms and subseq_is_slot_bounded by blast

text \<open>
  Armed with these predicates, we can prove more complex properties. For example, given a slot \<open>sl\<close>
  \<open>prune_after sl \<C>\<close> is bounded by any slot \<open>sl'\<close> such that \<open>sl \<le> sl'\<close>:
\<close>

lemma prune_after_is_slot_bounded:
  assumes "sl \<le> sl'"
  shows "prune_after sl \<C> \<unlhd> sl'"
  using assms by (induction \<C>) (simp, fastforce)

text \<open>
  Any \<open>sl\<close>-bounded prefix \<open>\<C>'\<close> of a chain \<open>\<C>\<close> is a prefix of \<open>\<C>\<close> when pruned after \<open>sl\<close>:
\<close>

lemma prune_after_includes_slot_bounded_prefix:
  assumes "is_slot_bounded_prefix \<C>' sl \<C>"
  shows "\<C>' \<preceq> prune_after sl \<C>"
  using assms unfolding prefix_def by auto

text \<open>
  A chain \<open>\<C>\<close>, when pruned after \<open>sl\<close>, is a \<open>sl\<close>-bounded prefix of \<open>\<C>\<close>:
\<close>

lemma prune_after_is_slot_bounded_prefix:
  shows "is_slot_bounded_prefix (prune_after sl \<C>) sl \<C>"
  using prune_after_is_prefix and prune_after_is_slot_bounded by fastforce

text \<open>
  A chain \<open>\<C>\<close>, when pruned after \<open>sl\<close>, is the longest \<open>sl\<close>-bounded prefix of \<open>\<C>\<close>
\<close>

lemma prune_after_is_longest_slot_bounded_prefix:
  assumes "is_slot_bounded_prefix \<C>\<^sub>l sl \<C>"
    and "\<forall>\<C>'. is_slot_bounded_prefix \<C>' sl \<C> \<longrightarrow> \<not> length \<C>\<^sub>l < length \<C>'"
  shows "prune_after sl \<C> = \<C>\<^sub>l"
proof -
  from assms(1) have "\<C>\<^sub>l \<preceq> prune_after sl \<C>"
    by (rule prune_after_includes_slot_bounded_prefix)
  moreover have "prune_after sl \<C> \<preceq> \<C>\<^sub>l"
  proof -
    from assms(2) have "length (prune_after sl \<C>) \<le> length \<C>\<^sub>l"
      using prune_after_is_slot_bounded_prefix and not_less by metis
    with \<open>\<C>\<^sub>l \<preceq> prune_after sl \<C>\<close> show ?thesis
      by (blast intro: prefix_length_prefix)
  qed
  ultimately show ?thesis
    by (simp add: prefix_order.antisym)
qed

text \<open>
  TODO: Complete.
\<close>

lemma prune_after_longer_than_slot_bounded_prefix:
  assumes "is_slot_bounded_prefix \<C>' sl \<C>"
  shows "\<not> length \<C>' > length (prune_after sl \<C>)"
proof -
  from assms have "\<C>' \<preceq> prune_after sl \<C>"
    by (rule prune_after_includes_slot_bounded_prefix)
  then have "length \<C>' \<le> length (prune_after sl \<C>)"
    by (simp add: prefix_length_le)
  then show ?thesis
    by simp
qed

text \<open>
  We define the specification of @{const \<open>prune_after\<close>}: The longest prefix of a given chain that
  is slot-bounded by a given slot:
\<close>

definition
  prune_after_spec :: "
    slot \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain"
where
  [simp]: "prune_after_spec sl \<C> = (ARG_MAX length \<C>'. is_slot_bounded_prefix \<C>' sl \<C>)"

text \<open>
  TODO: Complete.
\<close>

lemma prune_after_spec_satisfaction:
  shows "prune_after_spec sl \<C> = prune_after sl \<C>"
  unfolding prune_after_spec_def
  using
    prune_after_is_slot_bounded_prefix and
    prune_after_longer_than_slot_bounded_prefix and
    prune_after_is_longest_slot_bounded_prefix[symmetric]
    by (rule arg_maxI)

subsubsection \<open> Leader election \<close>

context leader_election
begin

notepad
begin

  fix oh\<^sub>1 oh\<^sub>2 oh\<^sub>3 oh\<^sub>4 oh\<^sub>5 oh\<^sub>6 :: "'hash option"
    and t\<sigma>\<^sub>1\<^sub>1 t\<sigma>\<^sub>1\<^sub>2 t\<sigma>\<^sub>2 t\<sigma>\<^sub>3 t\<sigma>\<^sub>4 t\<sigma>\<^sub>5 t\<sigma>\<^sub>6 B\<sigma>\<^sub>1 B\<sigma>\<^sub>2 B\<sigma>\<^sub>3 B\<sigma>\<^sub>4 B\<sigma>\<^sub>5 B\<sigma>\<^sub>6 :: 'sig
    and B\<^sub>\<pi>\<^sub>1 B\<^sub>\<pi>\<^sub>2 B\<^sub>\<pi>\<^sub>3 B\<^sub>\<pi>\<^sub>4 B\<^sub>\<pi>\<^sub>5 B\<^sub>\<pi>\<^sub>6 :: "('vrf\<^sub>y, 'vrf\<^sub>\<pi>) block_proof"
    and \<rho>\<^sub>1 \<rho>\<^sub>2 \<rho>\<^sub>3 \<rho>\<^sub>4 \<rho>\<^sub>5 \<rho>\<^sub>6 :: "('vrf\<^sub>y, 'vrf\<^sub>\<pi>) vrf\<^sub>o"

  let ?\<S>\<^sub>0 = "{U\<^bsub>1\<^esub> $$:= 10, U\<^bsub>2\<^esub> $$:= 20}::stake_distr"
  let ?tx\<^sub>1\<^sub>1 = "((U\<^bsub>1\<^esub>, U\<^bsub>2\<^esub>, 1), t\<sigma>\<^sub>1\<^sub>1)::'sig transaction"
  let ?tx\<^sub>1\<^sub>2 = "((U\<^bsub>1\<^esub>, U\<^bsub>2\<^esub>, 1), t\<sigma>\<^sub>1\<^sub>2)::'sig transaction"
  let ?tx\<^sub>2 = "((U\<^bsub>2\<^esub>, U\<^bsub>1\<^esub>, 1), t\<sigma>\<^sub>2)::'sig transaction"
  let ?tx\<^sub>3 = "((U\<^bsub>2\<^esub>, U\<^bsub>1\<^esub>, 5), t\<sigma>\<^sub>3)::'sig transaction"
  let ?tx\<^sub>4 = "((U\<^bsub>1\<^esub>, U\<^bsub>2\<^esub>, 2), t\<sigma>\<^sub>4)::'sig transaction"
  let ?tx\<^sub>5 = "((U\<^bsub>1\<^esub>, U\<^bsub>2\<^esub>, 1), t\<sigma>\<^sub>5)::'sig transaction"
  let ?tx\<^sub>6 = "((U\<^bsub>2\<^esub>, U\<^bsub>1\<^esub>, 2), t\<sigma>\<^sub>6)::'sig transaction"
  let ?B\<^sub>1 = "((1, oh\<^sub>1, [?tx\<^sub>1\<^sub>1, ?tx\<^sub>1\<^sub>2], B\<^sub>\<pi>\<^sub>1, \<rho>\<^sub>1), B\<sigma>\<^sub>1)::('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) block"
  let ?B\<^sub>2 = "((3, oh\<^sub>2, [?tx\<^sub>2], B\<^sub>\<pi>\<^sub>2, \<rho>\<^sub>2), B\<sigma>\<^sub>2)::('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) block"
  let ?B\<^sub>3 = "((4, oh\<^sub>3, [?tx\<^sub>3], B\<^sub>\<pi>\<^sub>3, \<rho>\<^sub>3), B\<sigma>\<^sub>3)::('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) block"
  let ?B\<^sub>4 = "((6, oh\<^sub>4, [?tx\<^sub>4], B\<^sub>\<pi>\<^sub>4, \<rho>\<^sub>4), B\<sigma>\<^sub>4)::('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) block"
  let ?B\<^sub>5 = "((7, oh\<^sub>5, [?tx\<^sub>5], B\<^sub>\<pi>\<^sub>5, \<rho>\<^sub>5), B\<sigma>\<^sub>5)::('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) block"
  let ?B\<^sub>6 = "((8, oh\<^sub>6, [?tx\<^sub>6], B\<^sub>\<pi>\<^sub>6, \<rho>\<^sub>6), B\<sigma>\<^sub>6)::('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) block"
  let ?\<C> = "[?B\<^sub>1, ?B\<^sub>2, ?B\<^sub>3, ?B\<^sub>4, ?B\<^sub>5, ?B\<^sub>6]::('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain"

  have "\<S>\<^bsub>1\<^esub>(?\<S>\<^sub>0, ?\<C>) = ?\<S>\<^sub>0"
    by simp

  have "\<S>\<^bsub>2\<^esub>(?\<S>\<^sub>0, ?\<C>) = ?\<S>\<^sub>0"
  proof -
    have "prune_after 0 ?\<C> = []"
      by simp
    then have "apply_chain [] ?\<S>\<^sub>0 = ?\<S>\<^sub>0"
      by simp
    with \<open>prune_after 0 ?\<C> = []\<close> show ?thesis
      by simp
  qed

  let ?\<S>\<^sub>3 = "{U\<^bsub>1\<^esub> $$:= 8, U\<^bsub>2\<^esub> $$:= 22}::stake_distr"

  assume "R = 2"
  have "\<S>\<^bsub>3\<^esub>(?\<S>\<^sub>0, ?\<C>) = ?\<S>\<^sub>3"
  proof -
    have "\<S>\<^bsub>Suc (Suc 1)\<^esub>(?\<S>\<^sub>0, ?\<C>) = apply_chain (prune_after (Suc 1) ?\<C>) ?\<S>\<^sub>0"
    proof -
      from \<open>R = 2\<close> have "Suc 1 = R"
        by simp
      then show ?thesis
        by simp
    qed
    moreover have "prune_after (Suc 1) ?\<C> = [?B\<^sub>1]"
      by simp
    moreover have "apply_chain [?B\<^sub>1] ?\<S>\<^sub>0 = ?\<S>\<^sub>3"
    proof -
      let ?\<S> = "{U\<^bsub>1\<^esub> $$:= 9, U\<^bsub>2\<^esub> $$:= 21}::stake_distr"
      have "apply_transaction ?tx\<^sub>1\<^sub>1 ?\<S>\<^sub>0 = ?\<S>"
      proof -
        let ?\<S>' = "?\<S>\<^sub>0(U\<^bsub>1\<^esub> $$:= (?\<S>\<^sub>0 $$! U\<^bsub>1\<^esub>) - 1)"
        have "?\<S>' = ({U\<^bsub>1\<^esub> $$:= 9, U\<^bsub>2\<^esub> $$:= 20}::stake_distr)"
          by eval
        have "?\<S>'(U\<^bsub>2\<^esub> $$:= ?\<S>' $$! U\<^bsub>2\<^esub> + 1) = ?\<S>"
          by eval
        then show ?thesis
          by simp
      qed
      moreover have "apply_transaction ?tx\<^sub>1\<^sub>2 ?\<S> = ?\<S>\<^sub>3"
      proof -
        let ?\<S>' = "?\<S>(U\<^bsub>1\<^esub> $$:= (?\<S> $$! U\<^bsub>1\<^esub>) - 1)"
        have "?\<S>' = ({U\<^bsub>1\<^esub> $$:= 8, U\<^bsub>2\<^esub> $$:= 21}::stake_distr)"
          by eval
        have "?\<S>'(U\<^bsub>2\<^esub> $$:= ?\<S>' $$! U\<^bsub>2\<^esub> + 1) = ?\<S>\<^sub>3"
          by eval
        then show ?thesis
          by simp
      qed
      ultimately have "apply_block ?B\<^sub>1 ?\<S>\<^sub>0 = ?\<S>\<^sub>3"
        by simp
      then show ?thesis
        by simp
    qed
    ultimately show ?thesis
      by simp
  qed

  assume "f = 1/2"
  have "\<phi>(1/3) = 1 - (1/2)\<^bsup>(1/3)\<^esup>"
  proof -
    from \<open>f = 1/2\<close> have "1 - f = f"
      by simp
    with \<open>f = 1/2\<close> show ?thesis
      unfolding slot_leader_probability_def by presburger
  qed

end

lemma independent_aggregation_aux:
  assumes "finite A"
    and "\<alpha> \<notin> A"
  shows "\<phi>(\<alpha>) * \<phi>(\<Sum>A) = \<phi>(\<alpha>) - (1 - f)\<^bsup>\<Sum>A\<^esup> + (1 - f)\<^bsup>\<Sum>({\<alpha>} \<union> A)\<^esup>"
proof -
  have "\<phi>(\<alpha>) * \<phi>(\<Sum>A) = \<phi>(\<alpha>) * (1 - (1 - f)\<^bsup>\<Sum>A\<^esup>)"
    unfolding slot_leader_probability_def ..
  also have "\<dots> = \<phi>(\<alpha>) - \<phi>(\<alpha>) * (1 - f)\<^bsup>\<Sum>A\<^esup>"
    by (simp add: right_diff_distrib')
  also have "\<dots> = \<phi>(\<alpha>) - (1 - (1 - f)\<^bsup>\<alpha>\<^esup>) * (1 - f)\<^bsup>\<Sum>A\<^esup>"
    unfolding slot_leader_probability_def ..
  also have "\<dots> = \<phi>(\<alpha>) - ((1 - f)\<^bsup>\<Sum>A\<^esup> - (1 - f)\<^bsup>\<alpha>\<^esup> * (1 - f)\<^bsup>\<Sum>A\<^esup>)"
    by (simp add: left_diff_distrib)
  also have "\<dots> = \<phi>(\<alpha>) - ((1 - f)\<^bsup>\<Sum>A\<^esup> - (1 - f)\<^bsup>(\<alpha> + \<Sum>A)\<^esup>)"
    by (simp add: powr_add)
  also from assms have "\<dots> = \<phi>(\<alpha>) - (1 - f)\<^bsup>\<Sum>A\<^esup> + (1 - f)\<^bsup>\<Sum>({\<alpha>} \<union> A)\<^esup>"
    by simp
  finally show ?thesis .
qed

theorem independent_aggregation:
  assumes "finite A"
    and "A \<noteq> {}"
  shows "1 - \<phi>(\<Sum>\<alpha> \<in> A. \<alpha>) = (\<Prod>\<alpha> \<in> A. (1 - \<phi>(\<alpha>)))"
  using assms
proof induction
  case empty
  then show ?case
    by simp
next
  case (insert \<alpha>' A')
  from insert.hyps show ?case
  proof cases
    case emptyI
    then show ?thesis
      by simp
  next
    case insertI
    let ?A = "A' \<union> {\<alpha>'}"
    from insert.hyps(1,2) have "(\<Prod>\<alpha> \<in> ?A. (1 - \<phi>(\<alpha>))) = (1 - \<phi>(\<alpha>')) * (\<Prod>\<alpha> \<in> A'. (1 - \<phi>(\<alpha>)))"
      by simp
    also from insert.IH and insertI(1) have "\<dots> = (1 - \<phi>(\<alpha>')) * (1 - \<phi>(\<Sum>A'))"
      by simp
    also have "\<dots> = 1 - \<phi>(\<Sum>A') - \<phi>(\<alpha>') + \<phi>(\<alpha>') * \<phi>(\<Sum>A')"
      by argo
    also from insert.hyps(1,2)
    have "\<dots> = 1 - \<phi>(\<Sum>A') - \<phi>(\<alpha>') + \<phi>(\<alpha>') - (1 - f)\<^bsup>\<Sum>A'\<^esup> + (1 - f)\<^bsup>\<Sum>?A\<^esup>"
      using independent_aggregation_aux by simp
    \<comment> \<open>for clarity:\<close>
    also have "\<dots> = 1 - 1 + (1 - f)\<^bsup>\<Sum>A'\<^esup> - \<phi>(\<alpha>') + \<phi>(\<alpha>') - (1 - f)\<^bsup>\<Sum>A'\<^esup> + (1 - f)\<^bsup>\<Sum>?A\<^esup>"
      by simp
    also have "\<dots> = 1 - 1 + (1 - f)\<^bsup>\<Sum>?A\<^esup>" \<comment> \<open>for clarity\<close>
      by simp
    finally show ?thesis 
      by simp
  qed
qed

end

subsubsection \<open> Chain selection \<close>

context chain_selection
begin

lemma first_suffix_eq_chains:
  shows "first_suffix \<C> \<C> = []"
proof -
  have "longest_common_prefix (map \<H>\<^sub>B \<C>) (map \<H>\<^sub>B \<C>) = map \<H>\<^sub>B \<C>"
    by (simp add: longest_common_prefix_max_prefix longest_common_prefix_prefix1
        prefix_order.eq_iff)
  then show ?thesis
    by simp
qed

lemma longest_chains_shorter_element:
  assumes "\<not> is_longest_chain \<C> \<CC>"
  shows "longest_chains (\<C> # \<CC>) = longest_chains \<CC>"
proof -
  from assms have "[\<C>' \<leftarrow> \<CC>. is_longest_chain \<C>' (\<C> # \<CC>)] = [\<C>' \<leftarrow> \<CC>. is_longest_chain \<C>' \<CC>]"
    by (metis (mono_tags, hide_lams) dual_order.trans le_cases list.set_intros(2) set_ConsD)
  with assms show ?thesis
    unfolding longest_chains_def by auto
qed

lemma longest_chains_empty:
  shows "longest_chains [] = []"
  unfolding longest_chains_def by simp

lemma longest_chains_elem_is_longest:
  assumes "is_longest_chain \<C> \<CC>"
  shows "\<C> \<in> set (longest_chains (\<C> # \<CC>))"
proof -
  have "\<C> \<in> set (\<C> # \<CC>)"
    by simp
  moreover from assms have "is_longest_chain \<C> (\<C> # \<CC>)"
    by simp
  ultimately show ?thesis
    unfolding longest_chains_def by simp
qed

lemma longest_chains_singleton:
  shows "longest_chains [\<C>] = [\<C>]"
  unfolding longest_chains_def by simp

lemma trimmed_hashed_lcp_is_first_suffix:
  assumes "\<not> disjoint_chains \<C> \<C>'"
  shows "drop (length (hashed_lcp \<C> \<C>')) \<C> = first_suffix \<C> \<C>'"
  using assms
proof (induction \<C> \<C>' rule: longest_common_prefix.induct)
  case (1 B \<C> B' \<C>')
  from \<open>\<not> disjoint_chains (B # \<C>) (B' # \<C>')\<close> have "\<H>\<^sub>B B = \<H>\<^sub>B B'"
    by simp
  have "hashed_lcp (B # \<C>) (B' # \<C>') = \<H>\<^sub>B B # hashed_lcp \<C> \<C>'"
  proof -
    from \<open>\<H>\<^sub>B B = \<H>\<^sub>B B'\<close>
    have "{map \<H>\<^sub>B (B # \<C>), map \<H>\<^sub>B (B' # \<C>')} = (#) (\<H>\<^sub>B B) ` {map \<H>\<^sub>B \<C>, map \<H>\<^sub>B \<C>'}"
      by simp
    then show ?thesis
      unfolding hashed_lcp_def by (metis Longest_common_prefix_image_Cons insert_not_empty)
  qed
  then
    have "drop (length (hashed_lcp (B # \<C>) (B' # \<C>'))) (B # \<C>) = drop (length (hashed_lcp \<C> \<C>')) \<C>"
    by simp
  also have "\<dots> = first_suffix \<C> \<C>'"
  proof (cases "\<not> disjoint_chains \<C> \<C>'")
    case True
    from \<open>\<H>\<^sub>B B = \<H>\<^sub>B B'\<close> have "B = B'"
      using collision_resistance by (meson inj_eq)
    with True and "1.IH" show ?thesis
      by simp
  next
    case False
    then show ?thesis
    proof (induction \<C> \<C>' rule: longest_common_prefix.induct)
      case (1 B \<C> B' \<C>')
      have "\<H>\<^sub>B B # map \<H>\<^sub>B \<C> \<in> {map \<H>\<^sub>B (B # \<C>), map \<H>\<^sub>B (B' # \<C>')}"
        by simp
      moreover have "\<H>\<^sub>B B' # map \<H>\<^sub>B \<C>' \<in> {map \<H>\<^sub>B (B # \<C>), map \<H>\<^sub>B (B' # \<C>')}"
        by simp
      moreover from "1.prems" have "\<H>\<^sub>B B \<noteq> \<H>\<^sub>B B'"
        by simp
      ultimately have "Longest_common_prefix {map \<H>\<^sub>B (B # \<C>), map \<H>\<^sub>B (B' # \<C>')} = []"
        by (metis Longest_common_prefix_eq_Nil)
      with \<open>\<H>\<^sub>B B \<noteq> \<H>\<^sub>B B'\<close> show ?case
        by simp
    next
      case ("2_1" \<C>')
      then show ?case
        by simp
    next
      case ("2_2" \<C>)
      then show ?case
        by (simp add: Longest_common_prefix_Nil)
    qed
  qed
  finally show ?case
    using \<open>\<H>\<^sub>B B = \<H>\<^sub>B B'\<close> by simp
next
  case ("2_1" \<C>')
  then show ?case
    by simp
next
  case ("2_2" \<C>)
  then show ?case
    by (simp add: Longest_common_prefix_Nil) 
qed

lemma first_chain_length_bound:
  assumes "disjoint_chains \<C> \<C>'"
    and "length (first_suffix \<C> \<C>') \<le> n"
  shows "length \<C> \<le> n"
proof -
  from \<open>disjoint_chains \<C> \<C>'\<close> have "first_suffix \<C> \<C>' = \<C>"
    by (induction \<C> \<C>' rule: longest_common_prefix.induct) simp_all
  with \<open>length (first_suffix \<C> \<C>') \<le> n\<close> show ?thesis
    by (simp del: first_suffix.simps)
qed

lemma forks_at_most_impl [code]:
  shows "forks_at_most n \<C> \<C>' \<longleftrightarrow> length (first_suffix \<C> \<C>') \<le> n"
proof (intro iffI)
  assume "forks_at_most n \<C> \<C>'"
  show "length (first_suffix \<C> \<C>') \<le> n"
  proof (cases "disjoint_chains \<C> \<C>'")
    case True
    with \<open>forks_at_most n \<C> \<C>'\<close> show ?thesis
      by simp
  next
    case False
    with \<open>forks_at_most n \<C> \<C>'\<close> show ?thesis
      using trimmed_hashed_lcp_is_first_suffix by force 
  qed
next
  assume "length (first_suffix \<C> \<C>') \<le> n"
  show "forks_at_most n \<C> \<C>'"
  proof (cases "disjoint_chains \<C> \<C>'")
    case True
    with \<open>length (first_suffix \<C> \<C>') \<le> n\<close> show ?thesis
      using first_chain_length_bound unfolding forks_at_most_def by presburger
  next
    case False
    with \<open>length (first_suffix \<C> \<C>') \<le> n\<close> show ?thesis
      using trimmed_hashed_lcp_is_first_suffix by simp
  qed
qed

lemma forks_at_mostI [intro]:
  shows "forks_at_most k \<C> \<C>"
  using first_suffix_eq_chains and forks_at_most_impl by simp

lemma max_valid_no_candidates:
  shows "max_valid \<C> [] = \<C>"
proof -
  have "longest_chains [\<C>] = [\<C>]"
    by (rule longest_chains_singleton)
  moreover have "forks_at_most k \<C> \<C>"
    by (intro forks_at_mostI)
  ultimately show ?thesis
    by auto
qed

lemma max_valid_local_bias:
  assumes "is_longest_chain \<C> \<CC>"
  shows "max_valid \<C> \<CC> = \<C>"
proof -
  from assms have "\<C> \<in> set (longest_chains (\<C> # [\<C>' \<leftarrow> \<CC>. forks_at_most k \<C> \<C>']))"
    using longest_chains_elem_is_longest by auto
  moreover have "forks_at_most k \<C> \<C>"
    by (intro forks_at_mostI)
  ultimately have "\<C> \<in> set (longest_chains [\<C>' \<leftarrow> \<C> # \<CC>. forks_at_most k \<C> \<C>'])"
    by auto
  then show ?thesis
    by (simp del: forks_at_most_def)
qed

lemma max_valid_preserves_order:
  assumes "\<not> is_longest_chain \<C> [\<C>' \<leftarrow> \<CC>. forks_at_most k \<C> \<C>']"
    and "\<CC>\<^sub>m\<^sub>a\<^sub>x = longest_chains [\<C>' \<leftarrow> \<CC>. forks_at_most k \<C> \<C>']"
    and "\<CC>\<^sub>m\<^sub>a\<^sub>x \<noteq> []"
  shows "max_valid \<C> \<CC> = hd \<CC>\<^sub>m\<^sub>a\<^sub>x"
proof -
  from assms have "\<CC>\<^sub>m\<^sub>a\<^sub>x = longest_chains [\<C>' \<leftarrow> \<C> # \<CC>. forks_at_most k \<C> \<C>']"
    using longest_chains_shorter_element by simp
  moreover from assms have "\<C> \<notin> set \<CC>\<^sub>m\<^sub>a\<^sub>x"
    unfolding longest_chains_def by simp
  ultimately show ?thesis
    by (simp del: forks_at_most_def)
qed

end

text \<open>
  Now we will test the chain selection rule algorithm using a test interpretation of
  @{locale chain_selection}, in which blocks are  basically `empty' except for the slot number, and
  the block hash function is simply the identity function:
\<close>

abbreviation (input) test_k :: nat where "test_k \<equiv> 2"
abbreviation (input) test_R :: nat where "test_R \<equiv> 4" \<comment> \<open>unused\<close>
abbreviation (input) test_f :: real where "test_f \<equiv> 1/2" \<comment> \<open>unused\<close>
abbreviation (input) test_ha :: real where "test_ha \<equiv> 3/4" \<comment> \<open>unused\<close>

type_synonym test_block = "(unit, unit, unit, unit) block"
type_synonym test_chain = "(unit, unit, unit, unit) chain"

abbreviation test_\<H>\<^sub>B :: "test_block \<Rightarrow> test_block" where "test_\<H>\<^sub>B \<equiv> id"

definition "test_forks_at_most = chain_selection.forks_at_most test_\<H>\<^sub>B"
definition "test_first_suffix = chain_selection.first_suffix test_\<H>\<^sub>B"
definition "test_max_valid = chain_selection.max_valid test_k test_\<H>\<^sub>B"
definition test_longest_chains :: "test_chain list \<Rightarrow> test_chain list" where
  "test_longest_chains = chain_selection.longest_chains"

interpretation test_chain_selection: chain_selection test_k test_R test_f test_ha test_\<H>\<^sub>B
  rewrites "chain_selection.forks_at_most test_\<H>\<^sub>B = test_forks_at_most"
    and "chain_selection.first_suffix test_\<H>\<^sub>B = test_first_suffix"
    and "chain_selection.longest_chains = test_longest_chains"
    and "chain_selection.max_valid test_k test_\<H>\<^sub>B = test_max_valid"
  unfolding test_forks_at_most_def
    and test_first_suffix_def
    and test_longest_chains_def
    and test_max_valid_def
  by unfold_locales simp_all

lemmas [code] = test_chain_selection.longest_chains_def

abbreviation make_test_block :: "slot \<Rightarrow> test_block" ("B\<^bsub>_\<^esub>") where
  "B\<^bsub>sl\<^esub> \<equiv> ((sl, None, [], (U\<^bsub>0\<^esub>, ((), ())), ((), ())), ())"

abbreviation make_test_chain :: "slot list \<Rightarrow> test_chain" ("\<langle>_\<rangle>") where
  "\<langle>ss\<rangle> \<equiv> map make_test_block ss"

notepad
begin

  let ?is_valid_fork = "\<lambda>n \<C> \<C>'. test_chain_selection.forks_at_most n \<C> \<C>'"

  text \<open>
    In this part we test the correctness of @{const chain_selection.forks_at_most}. To do so, we
    check that the following graphs represent @{emph \<open>valid\<close>} forks, with the chain at the top of
    each graph being the current local chain and the chain below the candidate chain:

    For \<open>k = 2\<close>: @{verbatim "
    
      G-0-1        G-0-1      G-0-1          G-0-1-2-3
      |              |            |              |
       -2-3-4         -2-3         -2-3           -4-5
    "}
  \<close>
  value "?is_valid_fork 2 \<langle>[0, 1]\<rangle> \<langle>[2, 3, 4]\<rangle>"
  value "?is_valid_fork 2 \<langle>[0, 1]\<rangle> \<langle>[0, 2, 3]\<rangle>"
  value "?is_valid_fork 2 \<langle>[0, 1]\<rangle> \<langle>[0, 1, 2, 3]\<rangle>"
  value "?is_valid_fork 2 \<langle>[0, 1, 2, 3]\<rangle> \<langle>[0, 1, 4, 5]\<rangle>"

  text \<open>
    And we check that the following graphs represent @{emph \<open>invalid\<close>} forks:

    For \<open>k = 2\<close>: @{verbatim "
    
      G-0-1-2        G-0-1-2-3
      |                |
       -3-4             -4-5
    "}

    For \<open>k = 1\<close>: @{verbatim "
    
      G-0-1
      |
       -2-3-4
    "}
  \<close>
  value "\<not> ?is_valid_fork 2 \<langle>[0, 1, 2]\<rangle> \<langle>[3, 4]\<rangle>"
  value "\<not> ?is_valid_fork 2 \<langle>[0, 1, 2, 3]\<rangle> \<langle>[0, 4, 5]\<rangle>"
  value "\<not> ?is_valid_fork 1 \<langle>[0, 1]\<rangle> \<langle>[2, 3, 4]\<rangle>"

  text \<open>
    Now we test the correctness of the @{const chain_selection.max_valid} function using the
    following test cases:
  \<close>

  \<comment> \<open>No candidate chains were broadcast during the current slot, so the local chain is not updated:\<close>
  value "test_chain_selection.max_valid \<langle>[0, 1]\<rangle> [] = \<langle>[0, 1]\<rangle>"

  \<comment> \<open>The only candidate chain is longer than the local chain and is a valid fork, so it is adopted:\<close>
  value "test_chain_selection.max_valid \<langle>[0, 1]\<rangle> [\<langle>[0, 1, 2]\<rangle>] = \<langle>[0, 1, 2]\<rangle>"

  \<comment> \<open>
    The only candidate chain is shorter than the local chain and a is valid fork, so it's not
    adopted:
  \<close>
  value "test_chain_selection.max_valid \<langle>[0, 1, 2]\<rangle> [\<langle>[0, 1]\<rangle>] = \<langle>[0, 1, 2]\<rangle>"

  \<comment> \<open>
    The only candidate chain is equal length as the local chain and is a valid fork, so it's not
    adopted (bias towards the local chain):
  \<close>
  value "test_chain_selection.max_valid \<langle>[0, 1]\<rangle> [\<langle>[3, 4]\<rangle>] = \<langle>[0, 1]\<rangle>"

  \<comment> \<open>
    The only candidate chain is longer than the local chain but is an invalid fork, so it's not
    adopted:
  \<close>
  value "test_chain_selection.max_valid \<langle>[0, 1, 2]\<rangle> [\<langle>[3, 4, 5, 6]\<rangle>] = \<langle>[0, 1, 2]\<rangle>"

  \<comment> \<open>The longest candidate is adopted:\<close>
  value "test_chain_selection.max_valid \<langle>[0, 1]\<rangle> [\<langle>[3, 4, 5, 6]\<rangle>, \<langle>[0, 1, 2]\<rangle>] = \<langle>[3, 4, 5, 6]\<rangle>"

  \<comment> \<open>The first longest candidate is adopted:\<close>
  value "test_chain_selection.max_valid \<langle>[0, 1]\<rangle> [\<langle>[0, 1, 2]\<rangle>, \<langle>[0, 1, 3]\<rangle>] = \<langle>[0, 1, 2]\<rangle>"

  \<comment> \<open>Invalid forks are filtered out:\<close>
  value "test_chain_selection.max_valid \<langle>[0, 1, 2]\<rangle> [\<langle>[3, 4, 5, 6]\<rangle>, \<langle>[0, 1, 2, 3]\<rangle>] = \<langle>[0, 1, 2, 3]\<rangle>"

  code_thms test_chain_selection.forks_at_most test_chain_selection.max_valid

end

end
