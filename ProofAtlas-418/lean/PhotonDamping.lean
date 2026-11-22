import OAI.InformationTheory.PhotonNumber.Inequality
import PhotonFilterSector

open Filter Topology OAI OAI.EntropyPhotonNumber OAI.QuantumTrace
open scoped ComplexConjugate

namespace ProofGraph.PhotonEntropy

noncomputable section

abbrev Damping := Set.Ioo (0 : ℝ) 1

def weight {n : ℕ} (r : Damping) (k : NumberIndex n) : ℝ := (r : ℝ) ^ totalNumber k

theorem weight_pos {n : ℕ} (r : Damping) (k : NumberIndex n) : 0 < weight r k :=
  pow_pos r.property.1 _

theorem weight_le_one {n : ℕ} (r : Damping) (k : NumberIndex n) : weight r k ≤ 1 :=
  pow_le_one₀ r.property.1.le r.property.2.le

private theorem weight_bound {n : ℕ} (r : Damping) (k : NumberIndex n) :
    ‖(weight r k : ℂ)‖ ≤ 1 := by
  simpa [abs_of_pos (weight_pos r k)] using weight_le_one r k

def damping {n : ℕ} (r : Damping) : Fock n →L[ℂ] Fock n :=
  diagonalMap (fun k => (weight r k : ℂ)) ⟨1, weight_bound r⟩

theorem damping_norm {n : ℕ} (r : Damping) : ‖damping (n := n) r‖ ≤ 1 :=
  diagonalMap_norm_le _ _ zero_le_one (weight_bound r)

theorem damping_ket {n : ℕ} (r : Damping) (k : NumberIndex n) :
    damping r (numberKet k) = (weight r k : ℂ) • numberKet k := by
  unfold numberKet damping
  rw [diagonalMap_single, mul_one, ← lp.single_smul]
  simp

theorem damping_adjoint {n : ℕ} (r : Damping) : (damping (n := n) r).adjoint = damping r :=
  (diagonalMap_symmetric _ _).isSelfAdjoint

def sandwich {n : ℕ} (r : Damping) (T : Fock n →L[ℂ] Fock n) :=
  (damping r).adjoint.comp (T.comp (damping r))

theorem sandwich_entry {n : ℕ} (r : Damping) (T : Fock n →L[ℂ] Fock n) (k l : NumberIndex n) :
    entry (sandwich r T) k l = (weight r k : ℂ) * (weight r l : ℂ) * entry T k l := by
  simp only [sandwich, entry, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    damping_ket, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  ring

def mass {n : ℕ} (r : Damping) (ρ : State n) : ℝ :=
  ∑' k, (weight r k)^2 * (entry ρ.op k k).re

theorem mass_series {n : ℕ} (r : Damping) (ρ : State n) :
    HasSum (fun k => (weight r k)^2 * (entry ρ.op k k).re) (mass r ρ) := by
  apply Summable.hasSum
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (sq_nonneg _) (ρ.positive.re_inner_nonneg_right _))
    _ ρ.trace_one.summable
  intro k
  exact mul_le_of_le_one_left (ρ.positive.re_inner_nonneg_right _)
    (pow_le_one₀ (weight_pos r k).le (weight_le_one r k))

theorem mass_pos {n : ℕ} (r : Damping) (ρ : State n) : 0 < mass r ρ := by
  obtain ⟨k, hk⟩ : ∃ k, 0 < (entry ρ.op k k).re := by
    by_contra! h
    have hz : ∀ k, (entry ρ.op k k).re = 0 := fun k => le_antisymm (h k) (ρ.positive.re_inner_nonneg_right _)
    have hsum := ρ.trace_one.tsum_eq
    simp [hz] at hsum
  exact (mul_pos (sq_pos_of_pos (weight_pos r k)) hk).trans_le
    (((mass_series r ρ).summable.le_tsum k (fun i _ => mul_nonneg (sq_nonneg _)
      (ρ.positive.re_inner_nonneg_right _))).trans_eq (mass_series r ρ).tsum_eq)

theorem mass_le_one {n : ℕ} (r : Damping) (ρ : State n) : mass r ρ ≤ 1 :=
  hasSum_le (fun k => mul_le_of_le_one_left (ρ.positive.re_inner_nonneg_right _)
    (pow_le_one₀ (weight_pos r k).le (weight_le_one r k))) (mass_series r ρ) ρ.trace_one

def damped {n : ℕ} (r : Damping) (ρ : State n) : State n where
  op := ((mass r ρ)⁻¹ : ℂ) • sandwich r ρ.op
  positive := (ρ.positive.adjoint_conj (damping r)).smul_of_nonneg (by
    exact_mod_cast inv_nonneg.mpr (mass_pos r ρ).le)
  trace_one := by
    have h := (mass_series r ρ).mul_left (mass r ρ)⁻¹
    rw [inv_mul_cancel₀ (mass_pos r ρ).ne'] at h
    convert! h using 1
    funext k
    change (inner ℂ (numberKet k) (((mass r ρ : ℂ)⁻¹) • sandwich r ρ.op (numberKet k))).re = _
    rw [inner_smul_right]
    change (((mass r ρ : ℂ)⁻¹) * entry (sandwich r ρ.op) k k).re = _
    rw [sandwich_entry, ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_assoc, ← Complex.ofReal_mul]
    simp [Complex.mul_re, pow_two, mul_assoc]

theorem damped_entry {n : ℕ} (r : Damping) (ρ : State n) (k l : NumberIndex n) :
    (mass r ρ : ℂ) * entry (damped r ρ).op k l =
      ((r : ℝ) : ℂ) ^ totalNumber k * ((r : ℝ) : ℂ) ^ totalNumber l * entry ρ.op k l := by
  change (mass r ρ : ℂ) * inner ℂ (numberKet k) (((mass r ρ : ℂ)⁻¹) • sandwich r ρ.op (numberKet l)) = _
  rw [inner_smul_right, ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (mass_pos r ρ).ne'), one_mul]
  change entry (sandwich r ρ.op) k l = _
  simpa only [weight, Complex.ofReal_pow] using sandwich_entry r ρ.op k l

theorem damped_diag {n : ℕ} (r : Damping) (ρ : State n) (k : NumberIndex n) :
    (entry (damped r ρ).op k k).re = (mass r ρ)⁻¹ * ((weight r k)^2 * (entry ρ.op k k).re) := by
  have h := congrArg Complex.re (damped_entry r ρ k k)
  simp [Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow] at h
  field_simp [ (mass_pos r ρ).ne' ]
  simpa [weight, pow_two, mul_left_comm, mul_comm, mul_assoc] using h

theorem damped_finiteEnergy {n : ℕ} (r : Damping) (ρ : State n) : FiniteEnergy (damped r ρ) := by
  have hs : Summable (fun m : ℕ => (m : ℝ) * (r.val ^ 2) ^ m) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 (r := r.val ^ 2)
      (by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; nlinarith [r.property.1, r.property.2])
  let C := ∑' m : ℕ, (m : ℝ) * (r.val ^ 2) ^ m
  have hbound (m : ℕ) : (m : ℝ) * (r.val ^ 2) ^ m ≤ C :=
    hs.le_tsum m (fun i _ => by positivity)
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (Nat.cast_nonneg _) ((damped r ρ).positive.re_inner_nonneg_right _))
    _ (ρ.trace_one.summable.mul_left ((mass r ρ)⁻¹ * C))
  intro k
  change (totalNumber k : ℝ) * (entry (damped r ρ).op k k).re ≤ _
  rw [damped_diag]
  have hpow : weight r k ^ 2 = (r.val ^ 2) ^ totalNumber k := by simp [weight, ← pow_mul, Nat.mul_comm]
  rw [hpow]
  calc
    _ = ((mass r ρ)⁻¹ * ((totalNumber k : ℝ) * (r.val ^ 2) ^ totalNumber k)) * (entry ρ.op k k).re := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hbound _) (inv_nonneg.mpr (mass_pos r ρ).le))
      (ρ.positive.re_inner_nonneg_right _)

end
end ProofGraph.PhotonEntropy
