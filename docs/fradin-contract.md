# Fradin v2, Theorem 3.1: formalization contract

The source is Fradin, Sadiev, Condat, and Richtárik, *Tight Lower Bounds and Optimal Algorithms for Stochastic Nonconvex Optimization with Heavy-Tailed Noise*, [arXiv:2512.18713v2](https://arxiv.org/abs/2512.18713v2), revised 31 March 2026. The target is [Theorem 3.1 and Appendix C.3](https://arxiv.org/html/2512.18713v2), with Definitions B.1–B.4, §B.1.4, and Assumptions 2.3 and 2.6.

For `1 < p ≤ 2`, `1 ≤ q ≤ 2`, positive `Δ, Lbar`, nonnegative `σ`, and `0 < ε ≤ c₁ √(Lbar Δ)`, the source lower bound for **zero-respecting algorithms** has order

\[
\left(\frac{\sigma}{\epsilon}\right)^{p/(p-1)}
+\frac{\bar L\Delta}{\epsilon^2}
+\frac{\bar L\Delta}{\epsilon^2}
 \left(\frac{\sigma}{\epsilon}\right)^{p/(q(p-1))}.
\]

The source permits `K` simultaneous decisions sharing one fresh seed per round and returns population values and stochastic gradients. Its §B.1.4 complexity uses a round index and a queried-iterate stationarity criterion. Preserve unbiasedness, centered `p`-moment and same-seed `q`-increment bounds, the support restriction, and this protocol. Response-count conversion and an arbitrary response-free output require explicit bridges. Unrestricted-algorithm claims require a separate theorem.

Global zero-respecting requires each nonzero queried coordinate to have appeared in a past observed gradient, almost surely on actual runs, for every C¹ population objective and every measurable, integrable, unbiased first-order oracle. It imposes no constraint on unreachable transcripts.

## Package boundary

`HeavyTailedNoise/Lower/Fradin/` is reserved for this separate construction. It may reuse `Model/`, `Analysis/`, and `Probability/`. It must encode the source's algorithm class and protocol explicitly rather than identify them with `RandomAlgorithm` without a proved bridge. References to numbered source results must include the fixed v2 version and their actual hypotheses.

The complete first-slot-normalized Theorem 3.1 passed the canonical whole-library native build and public signature/transitive-axiom audit, including the response-only representation bridge. The original response-only entry is `HeavyTailedNoise.Fradin.original_theorem31_constants`; it has no stochastic, oracle-legality or support premise beyond public parameter conditions. Independent clean-directory full-library reproduction, source-provenance and public axiom audits also passed. Theorems 3.2 and 3.3 and the source's upper algorithms are outside this certificate.

## Proof normalization and an identified intermediate error

The v2 Appendix C.2 proof labels the sole possible noise coordinate as
`prog_(1/4)(x)+1`. That label is generally incorrect for the smoothed selector.
For T=1, continuity and Γ(1/4)=0 give some x in (1/4,1/2) with Γ(x)<1/2.
Then Θ₁(x)=Γ(1−Γ(x))=1 and F₁′(x)=−Φ′(x) is nonzero. A failed Bernoulli
trial produces nonzero noise in coordinate 1, whereas the written label is 2.
This argument requires no numerical sampling. Two separate Sol/xhigh proof
passes checked the implication. The valid support index is
`prog_(1/2)(x)+1`: the selector kills earlier coordinates, and the chain
kills later coordinates. The at-most-one-coordinate statement survives.
This is an error in an intermediate proof line, not a counterexample to
Theorem 3.1; the repaired support and oracle bounds passed native kernel verification.

The implementation uses Γ(t)=smoothstep(4t−1), the already proved quintic
C² window. Only the regularity needed for the first-order theorem is claimed.
Its derivative bound is 15/2 and the suffix selector Lipschitz bound is 225/4;
the original selector constant is not reused. The checked realization uses
same-seed increment constant 6087 and the public rate coefficient defined in
`RateComparison`. The source's general C∞ and higher-order assertions are
not part of this target.

The batch expression in §B.1.4 does not define which slot norm is meant.
The protocol makes the first pre-response slot explicit and the lower-proof
interface covers all batch slots through the same failure event. Round
n+1 is evaluated after n responsive rounds (n*K returned gradient vectors),
not after its own response. Seed and private-space universe parameters are
explicit; no StandardBorel restriction is imposed on private randomness.

## Checked public entry and coefficient realization

```lean
import HeavyTailedNoise.Lower.Fradin
#check HeavyTailedNoise.Fradin.original_theorem31_lower_bound
#check HeavyTailedNoise.Fradin.original_theorem31_constants
#check HeavyTailedNoise.Fradin.observedSourceRoundComplexity_eq
#check HeavyTailedNoise.Fradin.source_coefficient_realization
```

One accuracy constant `c₁=1/1024` precedes all parameters. For each fixed p,
a positive `cₚ=publicRateCoefficient p` works for every q∈[1,2], every K≥1
and all positive L,Δ,ε and nonnegative σ in the accuracy regime. The private
space is arbitrary in universe v; the oracle-seed universe is 0. No expected
stopping-time criterion is added. The full rate is `cₚ(S^r+A+AS^(r/q))`.

The source's deferred coefficient construction is a simultaneous existence
proof. Fix public θ, then choose `Lint=ℓ Lbar θ^((q−1)/q)/C`,
`β=Lint/(2ℓε)` and `α=Lint/(β²ℓ)`. `SourceCoefficients` proves the three
scale identities and positivity. This alone does not make an arbitrary θ
satisfy the noise constraint. Actual legality follows from the public clipped
reveal rate (`θ=1` for S≤92, otherwise `(92/S)^r`), `C=6087`, and the natural
chain floor. `PhysicalChain` and the actual oracle proofs discharge the gap,
centered p moment and same-seed increment together. Parameters contain no
algorithm, private realization, or sampled seed variable.

`Representation` proves that the internal query records convey no extra
oracle observation: past queries are reconstructed measurably from the
algorithm, private seed and past `(F,g)` responses. Two-way actual-run
couplings preserve the global zero-respecting condition, risk and complete
complexity, including empty-infimum and infinite-risk cases. Unreachable
histories are not required to have identical decision rules.

A fresh independent Sol/xhigh primary-source review found no remaining
mathematical gap in this normalized first-order statement. The exact written
C.2 support-index error is repaired as above. The result is a formal proof of
the normalized theorem using a documented equivalent C² realization, not a
claim that every original intermediate sentence or higher-order assertion
has been verified verbatim.
