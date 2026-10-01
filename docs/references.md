# Sources and attribution

## Mathematical sources

- Yair Carmon, John C. Duchi, Oliver Hinder, and Aaron Sidford, [*Lower Bounds for Finding Stationary Points I*](https://arxiv.org/abs/1710.11606). Source of the scalar zero-chain framework used by the reusable analytic layer. The package proves the scalar and chain facts it uses rather than treating the paper's lemmas as axioms.
- Yossi Arjevani, Yair Carmon, John C. Duchi, Dylan J. Foster, Nathan Srebro, and Blake Woodworth, [*Lower Bounds for Non-Convex Stochastic Optimization*](https://arxiv.org/abs/1912.02365). Background for stochastic lower constructions and randomized-algorithm arguments. This citation is not a claim that all of the paper's results or oracles are formalized in this package.
- Adrien Fradin, Abdurakhmon Sadiev, Laurent Condat, and Peter Richtárik, [*Tight Lower Bounds and Optimal Algorithms for Stochastic Nonconvex Optimization with Heavy-Tailed Noise*, arXiv v2](https://arxiv.org/abs/2512.18713v2). The normalized first-order Theorem 3.1 passed complete native builds, provenance checks and public axiom audits in the primary cache and an independent fresh directory under the [separate source contract](fradin-contract.md).

The complete randomized strict-K=1 lower theorem combines the project's unrestricted Bernoulli-chain lift with the gated Haar construction. It uses the single gradient-only dimension-uniform minimax model and retains the absolute accuracy condition in the [complete lower contract](full-lower-contract.md). This randomized lift is not attributed to Fradin's original zero-respecting batch theorem. The v0.1.0 integrated 218-module package passed its canonical native build, complete provenance and 18-entry public signature/axiom audit; the separate Full-entry import also passed. Version 0.2.0 retains this lower proof and adds the original shared-batch EMA upper theorem and same-model matching corollary, as detailed in the [upper contract](k1-upper-contract.md).

The gated Haar construction and its quantitative proof repairs are developed in this project. The formalized scope and exact public constants are stated in the [library overview](../README.md). Source attribution, mathematical novelty, and a kernel-checked theorem are separate claims. The package contains references and original formal proofs; it does not distribute the cited papers.

## Proof infrastructure

- [Lean 4](https://github.com/leanprover/lean4), pinned by `lean-toolchain` to `v4.34.0`.
- [mathlib](https://github.com/leanprover-community/mathlib4/tree/5ed2965256430c3649e86755f9576b54eca72435), pinned by the canonical Lake configuration and manifest. mathlib retains its Apache 2.0 license.

## Prepared CI revisions

The workflow uses official actions pinned to full commit hashes. Their release and input documentation was checked when preparing the local package:

- [actions/checkout v7.0.1](https://github.com/actions/checkout/releases/tag/v7.0.1), commit [`3d3c42e5aac5ba805825da76410c181273ba90b1`](https://github.com/actions/checkout/commit/3d3c42e5aac5ba805825da76410c181273ba90b1).
- [leanprover/lean-action v1.5.0](https://github.com/leanprover/lean-action/releases/tag/v1.5.0), commit [`38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9`](https://github.com/leanprover/lean-action/commit/38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9). The [official action documentation](https://github.com/leanprover/lean-action) describes the build and mathlib-cache inputs.

Preparing the workflow does not establish a successful hosted CI run. See [CITATION.cff](../CITATION.cff) for machine-readable software and source citation metadata.
