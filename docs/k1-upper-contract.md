# Original strict-K=1 upper theorem: verified contract

This contract fixes the original algorithm, model and proof choices. The
upper, dimension-uniform guarantee and same-model matching declarations have
passed canonical modular compilation, independent public import/type/axiom
checks, the complete recursive 421-module build and the 30-entry guarded
public audit. The final statements use only `propext`, `Classical.choice`
and `Quot.sound`. The local proof certificate and each hosted CI run provide
separate evidence for their respective commits. The authoritative frozen source
is the iMac Dropbox/Overleaf `SGD under Heavy-tailed Noise/main.tex` at SHA-256
`1491f419c3cc66c16dcbc1085161fa8a340c9d72db67babaec3da4afe44be0ea`
(29 September 2026). The hashes of its algorithm, upper theorem, and upper
appendix blocks are, respectively,
`ecbc261da3d6bf81c4139fd05b7477f9ab4d737bf45942d792ef4d2ccfa8f35a`,
`a2f8f15c7085d605377e2db12c43b6ccc8bec91e976bd3f7154594d7b25d3ef6`,
and `08b01480a1a4f08fd296d3046a5c2fd2330e62871a83aa0b9dd3acfbbeb0e4af`.
Check differences against these blocks before using a subsequently synced file.

## Model and conclusion

For every positive finite dimension, `1 < p ≤ 2`, every finite `q ≥ 1`,
`σ ≥ 0`, `Δ, Lbar, ε > 0`, and every gradient-only oracle in the shared
`HeavyTailedNoise.Admissible` model from `Model/Basic.lean`, the checked
theorem bounds the risk of the specified algorithm. The model supplies global unbiasedness, centered p-BCM,
and same-seed q-WAS. A call returns one gradient vector at one pre-response
point from one fresh seed. The seed, sample function, and function value are
not observed. Private randomness is independent of all oracle seeds.

The public conclusion is `E ‖∇F(x_R)‖ ≤ ε` with a deterministic
response cap `N ≤ C(p,q) [B₊ + A₊ max(S²,S^(r/q))]`, where
`r=p/(p−1)`, `A₊=max(1,Lbar*Δ/ε²)`, `S=max(1,σ/ε)`, and `B₊=S^r`.
The constant may depend on p and q, but not dimension or physical parameters.
No new mathematical premise may remain in the final theorem.

## Literal algorithm

Use `ν=max(σ,ε)`, `a=2−p`, `s=p(1−1/q)`, `e₊=max(2−p−s,0)`,
`τ_j=12ν2^j`, `D_j=C_{τ_j}−C_{τ_{j−1}}`, and the least `J ≥ 0` with
`τ_J/ν ≥ C_tail S^(1/(p−1))`. Set `U=τ_J/ν` and choose the manuscript's
fixed legal constants. Then

```text
β    = 1 / (4 ceil S)
h    = c_h ε / Lbar
T    = ceil (4 A₊ / c_h)
α_j  = min (1, 1 / (κ (12·2^(j−1))^s))
n    = ceil (C_b S² U^e₊)
n_I  = ceil (C_I S² U^(2−p))
N    = 1 + (if q>1 and J>0 then n_I else 0) + T*n
```

Start at `x₁=0`; one fresh response sets `w₁`. If `q>1` and `J>0`, an
independent initialization batch sets all high-band memories. Every runtime
batch uses `n` independent fresh responses at the same pre-batch `x_t`.
Each returned vector contributes to the low band and every high band using the
same `w_t`; these transformed terms are correlated across scales. Its first
vector also updates `w_{t+1}` *after* the whole-batch estimator is formed,
without a second call. The normalized step uses the zero-estimator branch in
the manuscript. Independent `R` is uniform on `{1,…,T}`, and output `x_R`
requires no response. At `q=1`, initialization is skipped but all `J` high
bands still receive their runtime updates with `α_j=1`.

The canonical implementation is a `RandomAlgorithm` in the existing model.
Measurability, the independent fresh-seed coupling, whole-batch pre-response
decisions, and the exact pathwise count are proved.
The estimator analysis must condition on history *before the entire batch*;
it may use independence across different seeds and batches, but must retain
cross-scale covariance within a seed. Do not substitute a conditional moment
bound on the residual `g(x,ξ)−w` for the p-BCM assumption on
`g(x,ξ)−∇F(x)`.

## Permitted conservative kernel proof

The manuscript uses an exact double-band coefficient identity for
`Σ_k ‖Ψ_k(z)‖²`. The formal proof bounds the ℓ² norm over
lags of the **whole same-source band sum** by Minkowski:

```text
(Σ_k ‖Σ_j α_j(1−α_j)^k D_j(z)‖²)^(1/2)
  ≤ Σ_j ‖D_j(z)‖ (Σ_k α_j²(1−α_j)^(2k))^(1/2)
  ≤ Σ_j √α_j ‖D_j(z)‖.
```

This does not assert independence of bands; it controls all their cross
terms by a worst-case triangle inequality. The dyadic shell support and
`1−s/2>0` yield the same no-log exponent with a larger constant depending
only on p and q. The physical kernel and actual four-error assembly have
passed modular compilation. Their statements do not assume independence
between scales, or between runtime error and initial memory error.

The explicit legal choices in `ConvergenceConstants.lean` are
`c_h=1/8`, `C_I=4096`,
`C_tail=(128(1+C_p))^(1/(p−1))`,
`κ=(32 max(1,C_drift(p,q)))⁻¹`, and
`C_b=2048(1+C_p) max(1,C_kernel(p,q,κ))`, where
`C_p=4(1+36^p+815(243/8)^p)`. The component coefficients allocate ε/32
to each of runtime noise, initial memory, mean lag and terminal bias.
These are conservative constants in the manuscript's parameterized schedule;
the state updates and response protocol are unchanged.

## Public interfaces and minimax bridge

`HeavyTailedNoise.Upper.Full` exports
`UpperK1.Admissible.strict_k1_shared_batch_ema_upper`. Its only mathematical
inputs are an original `Admissible` instance and positive ε. The estimator
error bound, tracker moment, initialization and variance conditions are
proved internally, not additional assumptions of this declaration.

`Upper/K1/UniformGuarantee.lean` lifts the independent finite private index
through `ULift`, with exact transcript, output and risk equalities. This
reencoding permits the same algorithm in any private universe. The policy
and fixed response cap precede every admissible instance at each dimension
in `HasDimensionUniformGuarantee.{u,0}`. The bridge, updated `Upper.Full` entry and final matching corollaries have
passed canonical compilation and the independent public import audit. The
complete package build and expanded guarded public audit also passed.

## Same-model matching statement

Set `A=Lbar*Δ/ε²`, `B=(σ/ε)^r`, and define

```text
U = S^r + max(1,A) max(S²,S^(r/q))
M = max(A+B+A B^(1/q), A S²).
```

`RateComparison` proves `U≤2M` and `M≤2U` when `A≥1`, `σ≥0`,
`ε>0`, `p>1`, and finite `q≥1`. It includes `B=0`; it does not divide
by noise or assume an ordering between p and q.

`HeavyTailedNoise.strictK1_same_model_minimax_tight_rate` is the
final matching declaration. In the common regime `A≥10,752,000`, it reads

```text
ofReal(c_lower(p,q) M) < Nε ≤ ofReal(2 C_upper(p,q) M),
Nε = dimensionUniformMinimaxComplexity.{u,0} p q Δ σ Lbar ε.
```

Both coefficients are positive and depend only on p,q. The proof uses the
unchanged complete randomized `HeavyTailedNoise.Lower.Full` entry and the
fixed-cap uniform upper guarantee. The Fradin zero-respecting theorem is not
a premise. `strictK1_same_model_tight_rate` also provides the actual risk and
response-cap witness, and `strictK1_same_model_refutes_response_budget`
retains the complete lower's failure of every natural budget below its
threshold. The final matching declarations passed canonical compilation and their
transitive axiom checks. Neither oracle legality nor the estimator error is
left as an unproved premise. This does not formalize a k-buffer variant,
Fradin Theorems 3.2 or 3.3, or q=∞.
