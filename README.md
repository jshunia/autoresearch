# autoresearch

## ProofAtlas 418

*The entropy photon-number inequality without an energy assumption*, by Joseph M. Shunia. [Paper (PDF)](ProofAtlas-418/entropy-photon-number.pdf) · [LaTeX source](ProofAtlas-418/entropy-photon-number.tex) · [Lean proof of Theorem 1.1](ProofAtlas-418/lean/FiniteEntropyEPnI.lean)

The formalization uses Lean 4.34.1 and mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Research preprints

| Manuscript (PDF) | Source | Lean sources |
| --- | --- | --- |
| [Minimum support of Boolean functions on a slice](Boolean-Slice-Minimum-Support/boolean-slice-minimum-support.pdf) | [LaTeX](Boolean-Slice-Minimum-Support/boolean-slice-minimum-support.tex) | [Matching-cube lemmas](Boolean-Slice-Minimum-Support/lean/JohnsonMatchingCubes.lean) |
| [Optimal pooled measurements with unknown values over abelian groups](Abelian-Pooled-Measurements/abelian-pooled-measurements.pdf) | [LaTeX](Abelian-Pooled-Measurements/abelian-pooled-measurements.tex) | Formalization pending |
| [Universal fundamental groups in carry-free multiplication and cyclic tile packings](Carry-Free-Topology/carry-free-topology.pdf) | [LaTeX](Carry-Free-Topology/carry-free-topology.tex) | [Chart and covering lemmas](Carry-Free-Topology/lean/CarryFreeTopology.lean) |
| [Detecting signed powers over fields, with an application to hidden binary wirings](Signed-Power-Measurements/signed-power-measurements.pdf) | [LaTeX](Signed-Power-Measurements/signed-power-measurements.tex) | [Wiring reconstruction](Signed-Power-Measurements/lean/Wiring.lean) · [Integer-base lemmas](Signed-Power-Measurements/lean/SignedPowerMeasurements.lean) · [Field lemmas](Signed-Power-Measurements/lean/RadixMeasurements.lean) |

The three Lean projects in this table use Lean 4.32.2 and mathlib revision
`905b95818eb32af7874a58b427f50c1711a5e96c`. From the paper’s `lean/` directory, run
`lake exe cache get` to download the pinned mathlib build, then `lake build` to check the
local modules.

The Boolean-slice package verifies the weighted incidence and alternating-moment lemmas. The
carry-free package proves the homotopy implication assuming the covering and retraction
constructed in the paper. The signed-power package proves the noiseless wiring reconstruction
in Proposition 7.1 and several arithmetic lemmas. The asymptotic measurement rates have written proofs.
