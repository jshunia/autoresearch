import PhotonDamping

open OAI OAI.EntropyPhotonNumber OAI.QuantumTrace OAI.TensorLp
open scoped ComplexConjugate ComplexOrder

namespace ProofGraph.PhotonEntropy

noncomputable section

private theorem diag_ensemble_entry {J I : Type*} [DecidableEq J] (v : I → SequenceHilbert J)
    (hv : Summable (fun i => ‖v i‖^2)) (a : J → ℝ)
    (ha : ∃ C : ℝ, ∀ i, ‖(a i : ℂ)‖ ≤ C)
    (D := diagonalMap (fun j => (a j : ℂ)) ha)
    (hD : D = diagonalMap (fun j => (a j : ℂ)) ha := by rfl)
    (hDv : Summable (fun i => ‖D (v i)‖^2)) (k l : J) :
    inner ℂ (lp.single 2 k 1) (TraceEnsemble.operator (fun i => D (v i)) (lp.single 2 l 1)) =
    (a k : ℂ) * (a l : ℂ) * inner ℂ (lp.single 2 k 1) (TraceEnsemble.operator v (lp.single 2 l 1)) := by
  subst D
  let T := diagonalMap (fun j => (a j : ℂ)) ha
  have hT : T.adjoint = T := (diagonalMap_symmetric a ha).isSelfAdjoint
  have ket (i : J) : T (lp.single 2 i 1) = (a i : ℂ) • lp.single 2 i 1 := by
    rw [show T (lp.single 2 i 1) = _ from diagonalMap_single _ _ _ _, mul_one, ← lp.single_smul]
    simp
  apply (TraceEnsemble.hasSum_entry hDv (lp.single 2 k 1) (lp.single 2 l 1)).unique
  convert! (TraceEnsemble.hasSum_entry hv (lp.single 2 k 1) (lp.single 2 l 1)).mul_left
    ((a k : ℂ)*(a l : ℂ)) using 1
  funext i
  change inner ℂ _ (T (v i)) * inner ℂ (T (v i)) _ = _
  rw [← ContinuousLinearMap.adjoint_inner_left T (v i) (lp.single 2 k 1),
    ← ContinuousLinearMap.adjoint_inner_right T (v i) (lp.single 2 l 1), hT,
    ket, ket, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  ring

/-- Discarded-port energy damping is a selective measurement. The complementary
positive partial trace witnesses the order inequality for the retained marginal. -/
theorem output_dominated {n : ℕ} (r : Damping) (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (A B C : State n) (hC : IsBeamSplitterOutput η A B C) :
    let C' := beamOutput η hη (damped r A) (damped r B)
    let q := mass r A * mass r B
    ∀ x, (inner ℂ x (((q : ℂ) • C'.op) x)).re ≤ (inner ℂ x (sandwich r C.op x)).re := by
  classical
  let C' := beamOutput η hη (damped r A) (damped r B)
  let q := mass r A * mass r B
  let v := mixedVector η hη A B
  have hv := (mixedVector_norm η hη A B).summable
  let a (ke : PairedIndex n) := weight r ke.1 * Real.sqrt (1 - (weight r ke.2)^2)
  have hw (e : NumberIndex n) : (weight r e)^2 ≤ 1 :=
    pow_le_one₀ (weight_pos _ _).le (weight_le_one _ _)
  have ha1 (ke : PairedIndex n) : ‖(a ke : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (weight_pos r _).le (Real.sqrt_nonneg _))]
    apply mul_le_one₀ (weight_le_one _ _) (Real.sqrt_nonneg _)
    apply Real.sqrt_le_one.mpr
    linarith [sq_nonneg (weight r ke.2)]
  let R := diagonalMap (fun ke => (a ke : ℂ)) ⟨1, ha1⟩
  have hRn : ‖R‖ ≤ 1 := diagonalMap_norm_le _ _ zero_le_one ha1
  have hRv : Summable (fun i => ‖R (v i)‖^2) := by
    apply Summable.of_nonneg_of_le (fun i => sq_nonneg _) _ hv
    intro i
    exact pow_le_pow_left₀ (norm_nonneg _) ((R.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hRn)) _
  let Z := partialTrace (fun i => R (v i))
  have hZ : Z.IsPositive := partialTrace_positive hRv
  have heq : (q : ℂ) • C'.op + Z = sandwich r C.op := by
    apply entry_ext
    intro k l
    change inner ℂ (numberKet k) ((((q : ℂ) • C'.op) + Z) (numberKet l)) = _
    simp only [add_apply, inner_add_right, smul_apply, inner_smul_right]
    change (q : ℂ) * entry C'.op k l + entry Z k l = _
    rw [sandwich_entry]
    have h1 := (beamOutput_spec η hη (damped r A) (damped r B) k l).mul_left (q : ℂ)
    have h2 := partialTrace_entry hRv k l
    have h3 := (hC k l).mul_left ((weight r k : ℂ) * (weight r l : ℂ))
    apply (h1.add h2).unique
    convert! h3 using 1
    funext e
    change (q : ℂ) * outputBlock η (damped r A) (damped r B) k l e +
      inner ℂ (lp.single 2 (k,e) 1) (TraceEnsemble.operator (fun i => R (v i)) (lp.single 2 (l,e) 1)) = _
    rw [diag_ensemble_entry v hv a ⟨1, ha1⟩ R rfl hRv, mixedVector_entry]
    have hh := filtered_outputBlock η A B (damped r A) (damped r B) ((r : ℝ) : ℂ)
      (mass r A : ℂ) (mass r B : ℂ) (damped_entry r A) (damped_entry r B) k l e
    have hh' : (q : ℂ) * outputBlock η (damped r A) (damped r B) k l e =
        (weight r k : ℂ) * (weight r l : ℂ) * (weight r e : ℂ)^2 * outputBlock η A B k l e := by
      simpa only [q, weight, Complex.ofReal_pow, Complex.ofReal_mul] using hh
    rw [hh']
    have hs : (Real.sqrt (1-(weight r e)^2) : ℂ)^2 = 1 - (weight r e : ℂ)^2 := by
      exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr (hw e))
    dsimp only [a]
    push_cast
    linear_combination (weight r k : ℂ) * (weight r l : ℂ) * outputBlock η A B k l e * hs
  change ∀ x, (inner ℂ x (((q : ℂ) • C'.op) x)).re ≤ _
  intro x
  rw [← heq, add_apply, inner_add_right, Complex.add_re]
  exact le_add_of_nonneg_right (hZ.re_inner_nonneg_right _)

end
end ProofGraph.PhotonEntropy
