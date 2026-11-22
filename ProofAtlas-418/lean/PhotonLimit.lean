import PhotonDamping

open Filter Topology OAI OAI.QuantumTrace OAI.EntropyPhotonNumber
open scoped ComplexOrder

namespace ProofGraph.PhotonEntropy

noncomputable section

/-- A concrete sequence strictly between zero and one, approaching one from below. -/
def parameter (m : ℕ) : Damping :=
  ⟨Real.exp (-(1 / ((m : ℝ)+1))), Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (by positivity))⟩

theorem parameter_tendsto : Tendsto (fun m => (parameter m : ℝ)) atTop (𝓝 1) := by
  simpa [parameter, Function.comp_def] using (Real.continuous_exp.continuousAt.tendsto.comp
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg)

theorem weight_tendsto {n : ℕ} (k : NumberIndex n) :
    Tendsto (fun m => weight (parameter m) k) atTop (𝓝 1) := by
  simpa [weight] using parameter_tendsto.pow (totalNumber k)

theorem mass_tendsto {n : ℕ} (ρ : State n) :
    Tendsto (fun m => mass (parameter m) ρ) atTop (𝓝 1) := by
  rw [← ρ.trace_one.tsum_eq]
  apply tendsto_tsum_of_dominated_convergence ρ.trace_one.summable
  · intro k
    simpa using ((weight_tendsto k).pow 2).mul_const ((entry ρ.op k k).re)
  · apply Eventually.of_forall
    intro m k
    have hnon : 0 ≤ weight (parameter m) k ^ 2 * (entry ρ.op k k).re :=
      mul_nonneg (sq_nonneg _) (ρ.positive.re_inner_nonneg_right _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnon]
    exact mul_le_of_le_one_left (ρ.positive.re_inner_nonneg_right _)
      (pow_le_one₀ (weight_pos _ _).le (weight_le_one _ _))

/-- The unnormalized square-root factors converge in operator norm. The error is at
most the square root of a damped trace tail, even for a state of infinite mean energy. -/
theorem factor_tendsto {n : ℕ} (ρ : State n) :
    Tendsto (fun m => (TraceEnsemble.positiveRoot ρ.op).comp (damping (parameter m))) atTop (𝓝 (TraceEnsemble.positiveRoot ρ.op)) := by
  let P := TraceEnsemble.positiveRoot ρ.op
  let f (m : ℕ) (k : NumberIndex n) := (1-weight (parameter m) k)^2 * (entry ρ.op k k).re
  have hn (m k) : 0 ≤ f m k := mul_nonneg (sq_nonneg _) (ρ.positive.re_inner_nonneg_right _)
  have hb (m k) : f m k ≤ (entry ρ.op k k).re :=
    mul_le_of_le_one_left (ρ.positive.re_inner_nonneg_right _) (pow_le_one₀
      (sub_nonneg.mpr (weight_le_one _ _)) (sub_le_self _ (weight_pos _ _).le))
  have hsum (m) := Summable.of_nonneg_of_le (hn m) (hb m) ρ.trace_one.summable
  have ht : Tendsto (fun m => ∑' k, f m k) atTop (𝓝 0) := by
    have hz (k : NumberIndex n) : Tendsto (fun m => f m k) atTop (𝓝 0) := by
      simpa [f] using (((tendsto_const_nhds (x := (1:ℝ))).sub (weight_tendsto k)).pow 2).mul_const ((entry ρ.op k k).re)
    simpa using tendsto_tsum_of_dominated_convergence ρ.trace_one.summable hz
      (Eventually.of_forall fun m k => by rw [Real.norm_eq_abs, abs_of_nonneg (hn m k)]; exact hb m k)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsqrt : Tendsto (fun m => Real.sqrt (∑' k, f m k)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp ht
  apply squeeze_zero (fun _ => norm_nonneg _) _ hsqrt
  intro m
  apply norm_le_sqrt_basis_sum (numberBasis n)
  convert! (hsum m).hasSum using 1
  funext k
  change ‖P (damping (parameter m) (numberBasis n k)) - P (numberBasis n k)‖^2 = _
  rw [numberBasis_apply, damping_ket, map_smul]
  have hsub (a : ℂ) (x : Fock n) : a • x - x = (a-1) • x := by rw [sub_smul, one_smul]
  rw [hsub, norm_smul, mul_pow]
  rw [show ‖P (numberKet k)‖^2 = (entry ρ.op k k).re from (TraceEnsemble.sqrt_quadratic ρ.positive _).symm]
  change ‖(weight (parameter m) k : ℂ) - 1‖^2 * _ = _
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  dsimp only [f]
  ring

private theorem root_properties {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {T : E →L[ℂ] E} (hT : T.IsPositive) :
    (TraceEnsemble.positiveRoot T).adjoint = TraceEnsemble.positiveRoot T ∧
    (TraceEnsemble.positiveRoot T).comp (TraceEnsemble.positiveRoot T) = T :=
  ⟨(ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg T)).isSelfAdjoint,
    by
      apply ContinuousLinearMap.ext
      intro x
      simpa [TraceEnsemble.positiveRoot, pow_two] using congrArg (fun R : E →L[ℂ] E => R x)
        (CFC.sq_sqrt T (ContinuousLinearMap.nonneg_iff_isPositive.mpr hT))⟩

theorem damped_tendsto {n : ℕ} (ρ : State n) :
    Tendsto (fun m => (damped (parameter m) ρ).op) atTop (𝓝 ρ.op) := by
  let P := TraceEnsemble.positiveRoot ρ.op
  let A := fun m => P.comp (damping (parameter m))
  have hP : P.adjoint = P := (root_properties ρ.positive).1
  have hPP : P.comp P = ρ.op := (root_properties ρ.positive).2
  have hgram (m) : (A m).adjoint.comp (A m) = sandwich (parameter m) ρ.op := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [A, sandwich, ContinuousLinearMap.adjoint_comp, hP, ContinuousLinearMap.comp_apply]
    exact congrArg _ (DFunLike.congr_fun hPP _)
  have hc : Continuous (fun T : Fock n →L[ℂ] Fock n => T.adjoint.comp T) :=
    ContinuousLinearMap.adjoint.continuous.clm_comp continuous_id
  have h := (hc.tendsto P).comp (factor_tendsto ρ)
  change Tendsto (fun m => (A m).adjoint.comp (A m)) atTop (𝓝 (P.adjoint.comp P)) at h
  simp only [hgram, hP, hPP] at h
  have hm := ((Complex.continuous_ofReal.continuousAt.tendsto).comp (mass_tendsto ρ)).inv₀
    (show (1 : ℂ) ≠ 0 by norm_num)
  simpa [damped] using hm.smul h

theorem entropy_eventually_gt {n : ℕ} (ρ : State n) (hρ : ProofAtlas.PhotonNumber.FiniteEntropy ρ)
    {y : ℝ} (hy : y < entropy ρ) :
    ∀ᶠ m in atTop, y < entropy (damped (parameter m) ρ) := by
  let b := numberBasis n
  have ht := entropyOperator_tendsto (fun m => (damped (parameter m) ρ).positive) ρ.positive
    (fun m => norm_le_trace b (damped (parameter m) ρ).positive (trace_one_numberBasis _))
    (norm_le_trace b ρ.positive (trace_one_numberBasis _)) (damped_tendsto ρ)
  have hS : HasSum (fun k => (inner ℂ (b k) (entropyOperator ρ.op (b k))).re) (entropy ρ) := by
    simpa only [b, entropy, entropyOperator_eq_complex ρ.positive.isSymmetric, numberBasis_apply, entry] using hρ.hasSum
  obtain ⟨F,hF⟩ := (hS.eventually (eventually_gt_nhds hy)).exists
  have hdiag (k : NumberIndex n) : Continuous (fun T : Fock n →L[ℂ] Fock n => (inner ℂ (b k) (T (b k))).re) := by fun_prop
  have hf := tendsto_finsetSum F (fun k _ => ((hdiag k).tendsto _).comp ht)
  filter_upwards [hf.eventually (eventually_gt_nhds hF)] with m hm
  apply hm.trans_le
  let S := damped (parameter m) ρ
  have hsm := entropy_hasSum S (damped_finiteEnergy _ _)
  rw [← hsm.tsum_eq]
  exact hsm.summable.sum_le_tsum F (fun k _ =>
    (entropyOperator_positive S.positive (norm_le_trace b S.positive (trace_one_numberBasis _))).re_inner_nonneg_right _)

end
end ProofGraph.PhotonEntropy
