import OAI.InformationTheory.PhotonNumber.Basic

namespace ProofAtlas.PhotonNumber

open OAI.EntropyPhotonNumber

/-- Finiteness of the trace of the entropy operator. Its diagonal is nonnegative for a state.
This guards the upstream real-valued entropy sum, which defaults to zero if it diverges. -/
def FiniteEntropy {n : ℕ} (ρ : State n) : Prop :=
  Summable (fun k => (entry (cfc (fun z : ℂ => (-(z.re * Real.log z.re) : ℂ)) ρ.op) k k).re)

/-- ProofAtlas #418. An infinite output entropy satisfies the lower bound automatically,
so the real inequality is required for each output whose entropy is finite. -/
def EntropyPhotonNumberInequality : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (ρA ρB ρC : State n) (η : ℝ), η ∈ Set.Icc 0 1 →
    FiniteEntropy ρA → FiniteEntropy ρB → IsBeamSplitterOutput η ρA ρB ρC →
    FiniteEntropy ρC →
      (n : ℝ) * g (η * gInv (entropy ρA / n) + (1 - η) * gInv (entropy ρB / n)) ≤ entropy ρC

end ProofAtlas.PhotonNumber
