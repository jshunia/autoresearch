import PhotonConsequences
import Lean

open OAI.EntropyPhotonNumber

/-- Check the exact frozen rank, including the treatment of infinite output entropy. -/
example : ProofAtlas.PhotonNumber.EntropyPhotonNumberInequality :=
  ProofGraph.PhotonEntropy.finiteEntropyEPnI

example (n : ℕ) (hn : 1 ≤ n) (A B C : State n)
    (hA : FiniteEnergy A) (hB : FiniteEnergy B) (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (hC : IsBeamSplitterOutput η A B C) :
    η * gInv (entropy A / n) + (1 - η) * gInv (entropy B / n) ≤ gInv (entropy C / n) :=
  entropy_photon_number_inequality n hn A B C hA hB η hη hC

open Lean in
run_cmd do
  let env ← getEnv
  for name in [``ProofGraph.PhotonEntropy.finiteEntropyEPnI,
      ``OAI.EntropyPhotonNumber.entropy_photon_number_inequality,
      ``ProofGraph.PhotonEntropy.finite_inputs_of_finite_output,
      ``ProofGraph.PhotonEntropy.thermal_attenuator_minimum] do
    let .thmInfo info ← getConstInfo name | throwError "Expected a theorem"
    let some mod := env.getModuleIdxFor? name | throwError "Expected an imported proof"
    let axioms := (← collectAxioms name).map toString
    let row := Json.mkObj [("declaration", toJson name.toString),
      ("module", toJson env.header.moduleNames[mod]!.toString),
      ("type_expr", toJson (reprStr info.type)), ("proof_expr", toJson (reprStr info.value)),
      ("uses", toJson ((info.value.getUsedConstants.map toString).qsort)), ("axioms", toJson axioms.qsort)]
    IO.println ("PROOFGRAPH_PHOTON " ++ row.compress)
