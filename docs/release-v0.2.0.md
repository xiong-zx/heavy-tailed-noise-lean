# v0.2.0 release notes — strict-K=1 matching bounds

This version extends the verified finite-`q` randomized lower bound
from v0.1.0 with the manuscript's original strict-`K=1` shared-batch
exponential-memory upper algorithm. Both bounds use the same gradient-only
`Admissible` model and the same dimension-uniform minimax complexity.

## New public results

- `HeavyTailedNoise.Upper.Full` exports
  `UpperK1.Admissible.strict_k1_shared_batch_ema_upper`: for every admissible
  finite-dimensional instance, `1<p≤2`, finite real `q≥1`, `σ≥0`, and
  positive `ε`, the original algorithm has expected gradient norm at most
  `ε` with a fixed response cap
  `N≤C(p,q)[S^r+A₊ max(S²,S^(r/q))]`, where
  `r=p/(p−1)`, `S=max(1,σ/ε)`, and `A₊=max(1,Lbar Δ/ε²)`.
  Its exact count is `1+(if q>1 and J>0 then n_I else 0)+T*n`.
  The theorem has no estimator-error, oracle second-moment, or independent-band
  premise.
- `UpperK1.strict_k1_shared_batch_ema_uniform_guarantee` gives one fixed
  response cap in every dimension, with the policy chosen before the
  objective and oracle. The private-index lift preserves the original
  algorithm's transcript, output, and risk.
- `HeavyTailedNoise.TightRate` exports
  `strictK1_same_model_minimax_tight_rate`. For
  `A=Lbar Δ/ε²≥10,752,000`, set `B=(σ/ε)^r` and
  `M=max(A+B+A B^(1/q), A S²)`. Then the same unrestricted minimax quantity
  satisfies `c(p,q) M < Nε ≤ 2 C(p,q) M` for positive coefficients depending
  only on `p,q`. The two displayed upper and lower rate shapes are within a
  factor of two. The lower side calls the unchanged `Lower.Full` theorem.

The upper proof retains the covariance of all bands formed from one response,
conditions before each whole runtime batch, and uses independent fresh seeds
for the responses in that batch. The algorithm receives one gradient per seed, with
no value or seed observation. The output requires no additional response.
The result includes `q=1`, `p=2`, finite `q>2`, and `σ=0`.

The separate Fradin v2 Theorem 3.1 formalization retains its own
zero-respecting shared-seed batch protocol. This release does not assert an
upper theorem for that protocol, a `q=∞` result, or a theorem for any later
algorithm variant.

## Reproduce and release

The package pins Lean 4.34.0 and mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. From a clean checkout:

```sh
lake exe cache get
lake build
lake env lean scripts/CheckAxioms.lean
```

The default target covers all 421 modules. The guarded audit prints 30 public
types and rejects transitive axioms outside `propext`, `Classical.choice`, and
`Quot.sound`. The local iMac build, independent public import and 30-entry
audit passed on 30 September 2026. A release also requires that the
GitHub Actions clean build and audit pass for the exact commit to be tagged
`v0.2.0`; the tag and release must point to that commit.

The source and documentation use the MIT license with Zhixiao Xiong as the
software author. Dependencies and cited mathematical sources retain their
own attribution and licenses. Use [CITATION.cff](../CITATION.cff) for the
software and cite the underlying papers separately.
