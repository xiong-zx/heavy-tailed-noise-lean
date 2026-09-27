# Numerical repairs in the gated construction

Formalization found two false intermediate comparisons in the written proof of the correction-gradient bound. The construction, public theorem names, and final constants were retained. The resulting Lean bounds use exact rational arithmetic and actual ambient Euclidean derivatives.

## Correction amplitude

The comparison `e · 1.792 < 4.87` is false: the product is approximately `4.87116`. The replacement uses the normalized Gaussian integral defining `Φ` and the exact estimate

\[
\int_0^{1/2} e^{-s^2/2}\,ds \le \frac{1843}{3840},
\qquad \sqrt e \le \frac{1649}{1000}.
\]

Their product is

\[
\frac{1649}{1000}\frac{1843}{3840}
=\frac{3039107}{3840000}<0.791435.
\]

Using mutually exclusive predecessor branches and the explicit exponential bound gives

\[
e\left(1+\frac{3039107}{3840000}\right)<4.87.
\]

[SupportResidualGradientBounds](../HeavyTailedNoise/Lower/Gated/SupportResidualGradientBounds.lean) proves the sufficient non-strict actual correction-amplitude bound `|q_k| ≤ 487/100`. Here `q_k` is a correction term, distinct from the oracle smoothness exponent `q`.

## Selector subtotal

The comparison `4.87 · 13.6 < 66.2` is also false. The exact product is `66.232`. Retaining it produces the first-order total `99.125693125 < 100`; downward rounding is unnecessary.

The active-index premises are then discharged separately: the actual ambient derivative of `q_k` has norm less than `30`, the selector derivative has norm at most `68/5`, and the residual derivative has norm at most `3169/10` whenever the outer gate derivative is nonzero. [SupportResidualGradientFinal](../HeavyTailedNoise/Lower/Gated/SupportResidualGradientFinal.lean) assembles the unconditional bound `‖∇Q_U(y)‖ ≤ 100` for every orthonormal frame and ambient point.

## Remaining constants in the assembled proof

[SupportResidualHessian](../HeavyTailedNoise/Lower/Gated/SupportResidualHessian.lean) uses a conservative exact budget below `4100`, preserving the correction Hessian bound. The radial map's verified second derivative estimate is `6/R`. With the preprojection Hessian bound `4252`, this yields

\[
4252+6/20+1/5=4252.5<4300.
\]

The final scaled objective remains globally `L`-smooth. These local estimates are connected to the stopped-history probability argument and minimax quantifiers by [GatedHaarFiniteLowerBound](../HeavyTailedNoise/Lower/Gated/GatedHaarFiniteLowerBound.lean). A component estimate alone does not certify an importer or an unfinished theorem.
