# Contributing

Keep one implementation of each mathematical object and one canonical Lake configuration. Place reusable results in `Model/`, `Analysis/`, or `Probability/`; place construction-specific results under their corresponding lower or upper branch. Public theorem names and constants form the existing API.

State dimensions, moment exponents, independence, unbiasedness, query access, stationarity criterion, and algorithm quantifiers explicitly. A theorem with a conditional-law or regularity premise remains conditional until a public entry discharges that premise. Incomplete research should be documented as incomplete without adding a proof placeholder or a project axiom.

Before proposing a change, run the [reproduction commands](../README.md#reproduce-the-checks). Check the complete recursive library and public axiom audit. For a changed public statement, compare its signature and mathematical assumptions with the intended source. A focused component compile is useful during development and complements the full package gate.

Contributions to the package's original code and documentation use the [MIT license](../LICENSE). Keep copyright notices, contributor attribution, and source references when adapting existing material. Identify the origin and license of copied code separately; the package license does not relicense its dependencies or cited papers. The citation metadata credits Zhixiao Xiong; mathematical sources and dependencies retain their original attribution.

Keep generated build products, dependency caches, full paper copies, private host paths, credentials, execution logs, and chat transcripts outside the public source package. The pinned Lean toolchain and mathlib manifest are part of the reproducible source.
