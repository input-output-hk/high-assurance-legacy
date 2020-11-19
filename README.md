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


The Þ-calculus
==============

Currently the `main` branch contains an old framework for labeled
transition systems and our old process calculus, the ♮-calculus. The new
labeled transition framework and the Þ-calculus are being developed in
the branch [`thorn-calculus-preliminary`][thorn-calculus-preliminary].
Their code will soon be integrated into `main` step by step.

[main]:
    https://github.com/input-output-hk/ouroboros-high-assurance/tree/main
    "Main branch"
[thorn-calculus-preliminary]:
    https://github.com/input-output-hk/ouroboros-high-assurance/tree/thorn-calculus-preliminary
    "Preliminary branch for the Þ-calculus and the new LTS framework"
