import EntropyFilter
import PhotonOutput

open OAI OAI.EntropyPhotonNumber OAI.QuantumTrace ProofAtlas.PhotonNumber
open scoped ENNReal ComplexOrder

namespace ProofGraph.PhotonEntropy

noncomputable section

private theorem sandwich_trace {n : ℕ} (r : Damping) (ρ : State n) :
    HasSum (fun k => (inner ℂ (numberBasis n k) (sandwich r ρ.op (numberBasis n k))).re) (mass r ρ) := by
  convert! mass_series r ρ using 1
  funext k
  rw [numberBasis_apply]
  change (entry (sandwich r ρ.op) k k).re = _
  rw [sandwich_entry, ← Complex.ofReal_mul]
  simp [Complex.mul_re, pow_two]

private theorem scale_trace {n : ℕ} (q : ℝ) (S : State n) :
    HasSum (fun k => (inner ℂ (numberBasis n k) (((q : ℂ) • S.op) (numberBasis n k))).re) q := by
  simpa only [smul_apply, inner_smul_right, Complex.re_ofReal_mul, mul_one] using
    (trace_one_numberBasis S).mul_left q

/-- A bound at each positive filter strength. Because the success probability approaches one,
it controls the upper entropy limit without any bound on the original photon number. -/
theorem entropy_bound_of_filter {n : ℕ} (r : Damping) (S ρ : State n)
    (hS : FiniteEntropy S) (hρ : FiniteEntropy ρ) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hdom : ∀ x, (inner ℂ x (((q : ℂ) • S.op) x)).re ≤ (inner ℂ x (sandwich r ρ.op x)).re) :
    q * (1 + entropy S) ≤ 1 + entropy ρ := by
  let b := numberBasis n
  have hscale := traceMassEntropy_scale_lower S hq hq1
  have hmono := traceMassEntropy_mono b (S.positive.smul_of_nonneg (show 0 ≤ (q:ℂ) by exact_mod_cast hq.le))
    (ρ.positive.adjoint_conj (damping r)) (scale_trace q S) (sandwich_trace r ρ) hq1 (mass_le_one r ρ) hdom
  have hcontract := traceMassEntropy_contraction b (damping r) ρ.op (damping_norm r) ρ.positive
    (trace_one_numberBasis ρ) (sandwich_trace r ρ) (mass_le_one r ρ)
  have hh := hscale.trans (hmono.trans hcontract)
  change ENNReal.ofReal q * traceMassEntropy (numberBasis n) S.op ≤ traceMassEntropy (numberBasis n) ρ.op at hh
  rw [traceMassEntropy_state S hS, traceMassEntropy_state ρ hρ, ← ENNReal.ofReal_mul hq.le] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith [entropy_nonneg ρ])).mp hh

theorem entropy_damped_upper {n : ℕ} (r : Damping) (ρ : State n) (hρ : FiniteEntropy ρ) :
    mass r ρ * (1 + entropy (damped r ρ)) ≤ 1 + entropy ρ := by
  apply entropy_bound_of_filter r _ ρ (entropy_summable _ (damped_finiteEnergy r ρ)) hρ
    (mass_pos _ _) (mass_le_one _ _)
  have he : ((mass r ρ : ℂ) • (damped r ρ).op) = sandwich r ρ.op := by
    change (mass r ρ : ℂ) • ((mass r ρ : ℂ)⁻¹ • sandwich r ρ.op) = _
    rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (mass_pos r ρ).ne'), one_smul]
  intro x
  rw [he]

theorem entropy_output_upper {n : ℕ} (r : Damping) (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (A B C : State n) (hC : IsBeamSplitterOutput η A B C) (hSC : FiniteEntropy C) :
    (mass r A * mass r B) * (1 + entropy (beamOutput η hη (damped r A) (damped r B))) ≤ 1 + entropy C := by
  exact entropy_bound_of_filter r _ C (entropy_summable _ (beamOutput_finiteEnergy _ _
    (damped_finiteEnergy r A) (damped_finiteEnergy r B))) hSC (mul_pos (mass_pos _ _) (mass_pos _ _))
    ((mul_le_mul_of_nonneg_right (mass_le_one r A) (mass_pos r B).le).trans (by simpa using mass_le_one r B))
    (output_dominated r η hη A B C hC)

end
end ProofGraph.PhotonEntropy
