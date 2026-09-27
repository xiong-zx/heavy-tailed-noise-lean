# Complete randomized strict-K=1 lower bound

The main entry is `HeavyTailedNoise.Lower.Full`. It combines the actual
randomized Bernoulli-chain baseline with the gated Gaussian lower branch in
the single `dimensionUniformMinimaxComplexity` model. Fradin's original
zero-respecting batch theorem remains a separate source result.

For `1<p≤2`, every finite real `q≥1`, L,Δ,ε>0 and σ≥0, set
`A=LΔ/ε²`, `t=σ/ε`, `r=p/(p-1)` and `B=t^r`. The integrated canonical
package proves

\[
N_\epsilon>c_{p,q}\max\{A+B+AB^{1/q},A\max(1,t)^2\}
\]

under the absolute accuracy condition `ε≤√(LΔ)/√10,752,000`. One accuracy
constant precedes p,q; the positive response coefficient depends only on p,q
and precedes all physical parameters and algorithms. An equivalent parameter
entry assumes `A≥10,752,000`. No claim removes this accuracy condition.

The algorithm class is arbitrary measurable-private, full-history,
gradient-only randomized strict-K=1 access. Every fresh independent seed
supplies one gradient response. Queries range over the entire Euclidean space;
the algorithm may output any measurable point without another response. The
budget is a fixed natural number, and the criterion is expected gradient norm,
including infinite risk. Dimension is chosen before the algorithm. No
zero-respecting, private StandardBorel or expected-stopping-time premise is
introduced.

The source implementation is unique under `Lower/Randomized/`. It closes
actual oracle legality, all-point stationarity, stopped-posterior residual
reflection symmetry, geometric second moments, the N+1 query/output count,
private-randomness integration, physical budgets and minimax assembly.
Geometric second moments do not impose a second-moment assumption on oracle
noise. q=1, finite q>2 and σ=0 are included. No oracle-legality, geometry,
stochastic-symmetry or baseline premise remains in the terminal theorem.

The independent 23-module checkpoint included one audit file. Its 22 proof
files were migrated without mathematical changes; the audit is now owned by
the canonical `scripts/CheckAxioms.lean`. The unified canonical 218-module
native build exited 0 against 223 unchanged frozen inputs. Complete provenance
passed for source/cache equality, nine locked clean dependencies, all native
outputs and traces, setup ownership, hash sidecars and allowed import paths.
The 18-entry public signature/axiom audit and standalone Full-entry import
check passed; every audited conclusion depends exactly on `propext`,
`Classical.choice` and `Quot.sound`. Verification cleared external `LEAN_PATH`
and `LEAN_SRC_PATH`. The earlier checkpoint remains historical evidence; no
independent clean 218-module rebuild was performed. After lossless generated-metadata compaction, both public checks passed again; all 223 frozen inputs, 1,090 native artifact/hash records and nine dependency revisions remained unchanged.

The customary expression `B₊+A max{S₊²,S₊^(r/q)}`, with `S₊=max(1,t)` and
`B₊=S₊^r`, is within a factor of two of the exact max expression when A≥1.
It is an order comparison, not an identity or a separately declared Lean
corollary. q=∞, a complete upper theorem, novelty and manuscript readiness
are outside this certificate.
