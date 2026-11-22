# autoresearch

Mathematical preprints by Joseph M. Shunia, with LaTeX sources and accompanying Lean proofs where available.

## ProofAtlas 418

### The entropy photon-number inequality without an energy assumption

Guha, Erkmen and Shapiro conjectured that, among pairs of independent light beams with prescribed entropies,
thermal beams give the least output entropy at a beam splitter. The October 2026 ProofAtlas status note credits
OpenAI with the finite-energy case. Theorem 1.1 removes the energy assumption for any finite number of modes,
resolving problem 418 even when both inputs have finite entropy and infinite mean photon number. The same bound
gives the minimum output entropy of an optical channel that mixes its input with a thermal bath.

[ProofAtlas problem 418](https://www.proofatlas.ai/open-problems/#problem-top500-omission-w045049-entropy-photon-number-inequality) · [Paper (PDF)](ProofAtlas-418/entropy-photon-number.pdf) · [LaTeX source](ProofAtlas-418/entropy-photon-number.tex) · [Lean proof of Theorem 1.1](ProofAtlas-418/lean/FiniteEntropyEPnI.lean)

## Research preprints

### Minimum support of Boolean functions on a slice

How few $k$-element subsets of an $n$-element set can a nonzero Boolean function of degree at most $d$ select?
The paper proves the minimum conjectured by Kiermaier, Mannaert and Wassermann for $d=2$, for all layers of width
$\min(k,n-k)\le 6$, and for every fixed $d$ once $n$ is sufficiently large. It also classifies the smallest
families one and two degrees below the width. The same counting method gives exact row-deletion thresholds.
For the matrix recording which 7-element subsets lie in which 10-element subsets of a 24-element set, at least
680 rows must be deleted to lower the rank over any field, and 680 suffice.

[Conjecture 7 in the original paper](https://arxiv.org/html/2510.02804v1#Thmtheorem7) · [Paper (PDF)](Boolean-Slice-Minimum-Support/boolean-slice-minimum-support.pdf) · [LaTeX source](Boolean-Slice-Minimum-Support/boolean-slice-minimum-support.tex) · [Weighted incidence and alternating moments (Lean)](Boolean-Slice-Minimum-Support/lean/JohnsonMatchingCubes.lean)

### Optimal pooled measurements with unknown values over abelian groups

A pooled test reports the sum of a chosen subset of entries in an unknown vector. For any fixed error fraction
below one quarter, a single test sequence per dimension works over every nontrivial abelian group. Its initial
segments use the optimal number of tests, up to constants, for each sparsity level and number of distinct nonzero
values. For example, if $n$ real entries take at most two distinct nonzero values, the optimal test count grows
as $n/\log n$, even when both values are unknown and that fraction of answers is corrupted.

[Paper (PDF)](Abelian-Pooled-Measurements/abelian-pooled-measurements.pdf) · [LaTeX source](Abelian-Pooled-Measurements/abelian-pooled-measurements.tex) · Lean formalization pending

### Universal fundamental groups in carry-free multiplication and cyclic tile packings

For a fixed binary multiplier, the sets of digit positions that can be used together without creating a carry
form a simplicial complex. The paper constructs one odd multiplier for which the fundamental group of a component
contains every finitely presented group. It also constructs a single tile on a cycle of prime length whose
packing complex has the same property. In each example, no algorithm can decide for every loop whether it
contracts to a point.

[Paper (PDF)](Carry-Free-Topology/carry-free-topology.pdf) · [LaTeX source](Carry-Free-Topology/carry-free-topology.tex) · [Chart lemmas and the homotopy consequence of a covering and retraction (Lean)](Carry-Free-Topology/lean/CarryFreeTopology.lean)

### Detecting signed powers over fields, with an application to hidden binary wirings

Suppose each unknown entry is zero or a signed power of a known field element. The paper determines how many
signed sums are needed for recovery, up to constants. In characteristic two all signs coincide, so swapping two
entries leaves every answer unchanged. Integer sums of powers of two encode a hidden wiring that permutes and
flips $n$ bits. Each query counts how many pairs of inputs reverse order after applying a chosen output mask.
The optimal number of counts is $\Theta(n\log\log n/\log n)$, even when a fixed fraction below one quarter of the
answers is corrupted.

[Paper (PDF)](Signed-Power-Measurements/signed-power-measurements.pdf) · [LaTeX source](Signed-Power-Measurements/signed-power-measurements.tex) · [Noiseless wiring reconstruction, Proposition 7.1 (Lean)](Signed-Power-Measurements/lean/Wiring.lean) · [Integer-base lemmas (Lean)](Signed-Power-Measurements/lean/SignedPowerMeasurements.lean) · [Field lemmas (Lean)](Signed-Power-Measurements/lean/RadixMeasurements.lean)

## Lean versions

The proof of Theorem 1.1 for ProofAtlas 418 uses Lean 4.34.1 and mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

The Boolean-slice, carry-free, and signed-power projects use Lean 4.32.2 and mathlib revision
`905b95818eb32af7874a58b427f50c1711a5e96c`. In each of these three projects, run
`lake exe cache get` from the paper’s `lean/` directory, then `lake build` to check its modules.
