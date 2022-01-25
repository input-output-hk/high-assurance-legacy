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
  from a single VRF.
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
  "slot_epoch sl = nat \<lceil>sl / R\<rceil>"

text \<open>
  and we can check whether a given slot is the first one in its epoch:
\<close>

definition (in protocol_parameters) first_in_epoch :: "slot \<Rightarrow> bool" where
  "first_in_epoch sl = (R dvd (sl - 1))"

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
  "s\<^sup>+\<^bsub>X\<^esub>(\<S>) = (\<Sum>U \<in> X. \<S> $$! U)" if "X \<subseteq> fmdom' \<S>"

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
  "\<alpha>\<^sup>+\<^bsub>X\<^esub>(\<S>) = s\<^sup>+\<^bsub>X\<^esub>(\<S>) / s\<^sup>+\<^sub>\<P>(\<S>)" if "\<S> \<noteq> {$$}"

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

function
  apply_transaction :: "'sig transaction \<Rightarrow> stake_distr \<Rightarrow> stake_distr"
where
  "apply_transaction ((U\<^sub>i, U\<^sub>j, s), _) \<S> = (
    let
      \<S>' = \<S>(U\<^sub>i $$:= \<S> $$! U\<^sub>i - s)
    in
      \<S>'(U\<^sub>j $$:= \<S>' $$! U\<^sub>j + s))" if "{U\<^sub>i, U\<^sub>j} \<subseteq> fmdom' \<S>" and "\<S> $$! U\<^sub>i \<ge> s"
| "apply_transaction ((U\<^sub>i, U\<^sub>j, s), \<sigma>) \<S> =
    undefined ((U\<^sub>i, U\<^sub>j, s), \<sigma>) \<S>" if "\<not> ({U\<^sub>i, U\<^sub>j} \<subseteq> fmdom' \<S> \<and> \<S> $$! U\<^sub>i \<ge> s)"
  by (atomize, auto)
  termination by lexicographic_order

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
  "apply_block B = fold apply_transaction (bl_txs B)"

subsection \<open> Chains \<close>

text \<open>
  A chain is simply a sequence of blocks. As stated earlier, we do not record the genesis block
  explicitly as part of the chain:
\<close>

type_synonym ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain = "('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) block list"

text \<open>
  We let \<open>\<C>\<^sub>1 \<preceq> \<C>\<^sub>2\<close> indicate that the chain \<open>\<C>\<^sub>1\<close> is a prefix of the chain \<open>\<C>\<^sub>2\<close>:
\<close>

definition
  is_prefix_of :: "
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    bool"
  (infix \<open>\<preceq>\<close> 50)
where
  "\<C>\<^sub>1 \<preceq> \<C>\<^sub>2 \<longleftrightarrow> prefix \<C>\<^sub>1 \<C>\<^sub>2"

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
  "\<C>\<^sup>\<lceil>\<^bsup>m\<^esup> = take (length \<C> - m) \<C>"

text \<open>
  Also, we define a function to prune the blocks in a chain which have slots greater than a
  given slot:
\<close>

definition
  prune_after :: "slot \<Rightarrow> ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow> ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain"
where
  "prune_after sl = takeWhile (\<lambda>B. bl_slot B \<le> sl)"

text \<open>
  And we can apply a chain \<open>\<C>\<close> to a stake distribution \<open>\<S>\<close> by sequentially applying all blocks
  in \<open>\<C>\<close> to \<open>\<S>\<close>:
\<close>

definition
  apply_chain :: "('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow> stake_distr \<Rightarrow> stake_distr"
where
  "apply_chain = fold apply_block"

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
  "fold1 f xs = foldl f (hd xs) (tl xs)"

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

private definition
  slot_leader_probability :: "relative_stake \<Rightarrow> real" (\<open>\<phi>'(_')\<close>)
where
  "\<phi>(\<alpha>) = 1 - (1 - f)\<^bsup>\<alpha>\<^esup>"

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

private definition
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

definition
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

context
begin

text \<open>
  Since the genesis block is not a proper block in a chain, we have to take care of it separately.
  So, we need to check whether two chains are `disjoint', i.e., that the only intersection point
  between them is the genesis block. This amounts to checking whether their first blocks are
  different, since, by construction, if they differ in the first block then they must necessarily
  diverge:
\<close>

private definition
  disjoint_chains :: "
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    bool"
where
  "disjoint_chains \<C> \<C>' \<longleftrightarrow> \<H>\<^sub>B (hd \<C>) \<noteq> \<H>\<^sub>B (hd \<C>')" if "\<C> \<noteq> []" and "\<C>' \<noteq> []"

text \<open>
  Also, we can extract the hashed, longest common prefix of two chains:
\<close>

private definition
  hashed_lcp :: "
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    'block_hash list"
where
  "hashed_lcp \<C> \<C>' = Longest_common_prefix {map \<H>\<^sub>B \<C>, map \<H>\<^sub>B \<C>'}"

text \<open>
  Now, we can check whether a chain \<open>\<C>\<close> forks from another chain \<open>\<C>'\<close> at most \<open>n\<close> blocks, i.e. that
  we should roll back at most the most recent \<open>n\<close> blocks in \<open>\<C>\<close> in order to switch to \<open>\<C>'\<close>:
\<close>

private definition
  forks_at_most :: "
    nat \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    bool"
where
  "forks_at_most n \<C> \<C>' \<longleftrightarrow> (
    if
      disjoint_chains \<C> \<C>'
    then
      length \<C> \<le> n
    else
      length (drop (length (hashed_lcp \<C> \<C>')) \<C>) \<le> n)"

text \<open>
  Also, we can compute the list of the longest chains in a given list of chains \<open>\<CC>\<close>:
\<close>

private definition
  longest_chains :: "
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain list \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain list"
where
  "longest_chains \<CC> = (
    let
      is_longest_chain = \<lambda>\<C> \<CC>. \<forall>\<C>' \<in> set \<CC>. length \<C> \<ge> length \<C>'
    in
      [\<C>. \<C> \<leftarrow> \<CC>, is_longest_chain \<C> \<CC>])"

text \<open>
  Now we can define the function that implements the `longest chain' rule, namely the
  $\mathsf{maxvalid}$ function in the paper:
\<close>

definition
  max_valid :: "
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain list \<Rightarrow>
    ('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain"
where
  "max_valid \<C> \<CC> = (
    let
      \<CC>' = [\<C>'. \<C>' \<leftarrow> \<C> # \<CC>, forks_at_most k \<C> \<C>']; \<comment> \<open>the \<open>k\<close> parameter\<close>
      \<CC>' = longest_chains \<CC>'
    in
      if \<C> \<in> set \<CC>' then \<C> else hd \<CC>')"

end

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
  "verify_tx tx G \<longleftrightarrow> (
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
  "verify_tx_data txs G \<longleftrightarrow> (\<forall>i \<in> {0..<length txs}. verify_tx (txs ! i) G)"

text \<open>
  A key component of block verification is verifying the block proof, i.e. that the stakeholder who
  created the block was in the slot leader set of the slot in which the block was created:
\<close>

private definition
  verify_block_proof :: "slot \<Rightarrow> 'vkey \<Rightarrow> 'nonce \<Rightarrow> ('vrf\<^sub>y, 'vrf\<^sub>\<pi>) vrf\<^sub>o \<Rightarrow> real \<Rightarrow> bool"
where
  "verify_block_proof sl vk \<eta> v T \<longleftrightarrow> verify\<^sub>V\<^sub>R\<^sub>F vk (\<eta> \<bar>\<bar> sl \<bar>\<bar> TEST) v \<and> value_to_real (fst v) < T"

text \<open>
  Furthermore, we verify that the nonce proof in a block was properly created:
\<close>

private definition
  verify_block_nonce :: "slot \<Rightarrow> 'vkey \<Rightarrow> 'nonce \<Rightarrow> ('vrf\<^sub>y, 'vrf\<^sub>\<pi>) vrf\<^sub>o \<Rightarrow> bool"
where
  "verify_block_nonce sl vk \<eta> v \<longleftrightarrow> verify\<^sub>V\<^sub>R\<^sub>F vk (\<eta> \<bar>\<bar> sl \<bar>\<bar> NONCE) v"

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
  "verify_block B oh\<^sub>p\<^sub>r\<^sub>e\<^sub>v G \<eta> T \<longleftrightarrow> (
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
  and we can verify that a chain is indeed valid:
\<close>

private definition
  verify_chain :: "('hash, 'vrf\<^sub>y, 'vrf\<^sub>\<pi>, 'sig) chain \<Rightarrow> ('vkey, 'nonce) genesis \<Rightarrow> 'nonce \<Rightarrow> bool"
where
  "verify_chain \<C> G \<eta> \<longleftrightarrow> (\<forall>i \<in> {0..<length \<C>}.
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
  We specify what the initial state for each stakeholder should be:
\<close>

definition
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

private definition
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

private definition
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
  "store_tx ss tx = ss\<lparr>ss_txs := tx # ss_txs ss\<rparr>"

text \<open>
  Also, we define a function to store a given chain in the chains mempool of a stakeholder's state,
  after pruning blocks belonging to future slots in the chain, and provided that the pruned chain
  is valid:
\<close>

private definition
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

private definition
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

private definition
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

definition
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

end
