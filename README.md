Overview
========

The goal of this project is to develop implementations of blockchain
consensus protocols from the Ouroboros family in a process calculus and
verify that they have various key properties.

The bulk of the code in this repository is written in Isabelle/HOL and
falls into the following parts:

  * A framework for labeled transition systems

  * The implementation of the Þ-calculus, the process calculus we use
    for our protocol implementations

  * Implementations of consensus protocols in the Þ-calculus along with
    proofs of key properties they have
