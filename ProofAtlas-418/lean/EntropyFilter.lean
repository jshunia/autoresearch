import EntropyOrder
import OAI.InformationTheory.PhotonNumber.Inequality
import ProofAtlasPhotonNumber

open OAI OAI.QuantumTrace OAI.EntropyPhotonNumber ProofAtlas.PhotonNumber
open scoped ENNReal Topology ComplexOrder

namespace ProofGraph.PhotonEntropy

noncomputable section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I : Type*}

/-- Passing a positive trace-one operator through a contraction cannot increase its
modified entropy trace. The Gram operators exchange the location of the contraction. -/
theorem traceMassEntropy_contraction (b : HilbertBasis I ℂ E) (D T : E →L[ℂ] E)
    (hD : ‖D‖ ≤ 1) (hT : T.IsPositive)
    (htrace : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) 1)
    {s : ℝ} (hs : HasSum (fun i => (inner ℂ (b i) ((D.adjoint.comp (T.comp D)) (b i))).re) s)
    (hs1 : s ≤ 1) :
    traceMassEntropy b (D.adjoint.comp (T.comp D)) ≤ traceMassEntropy b T := by
  let P := CFC.sqrt T
  let A := P.comp D
  have hP : P.adjoint = P :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg T)).isSelfAdjoint
  have hPP (x : E) : P (P x) = T x := by
    simpa [P, pow_two] using congrArg (fun R : E →L[ℂ] E => R x)
      (CFC.sq_sqrt T (ContinuousLinearMap.nonneg_iff_isPositive.mpr hT))
  have hgram : A.adjoint.comp A = D.adjoint.comp (T.comp D) := by
    ext x
    simp only [A, ContinuousLinearMap.adjoint_comp, hP, ContinuousLinearMap.comp_apply, hPP]
  have hform (x : E) : (inner ℂ x ((A.comp A.adjoint) x)).re ≤ (inner ℂ x (T x)).re := by
    rw [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left,
      inner_self_eq_norm_sq_to_K, sqrt_inner_eq hT]
    simp [← Complex.ofReal_pow]
    change ‖A.adjoint x‖ ^ 2 ≤ ‖P x‖ ^ 2
    rw [show A.adjoint = D.adjoint.comp P from by simp [A, hP], ContinuousLinearMap.comp_apply]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((D.adjoint.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (by simpa using hD))) _
  have hY := A.isPositive_self_comp_adjoint
  have ht := (Summable.of_nonneg_of_le (fun i => hY.re_inner_nonneg_right (b i))
    (fun i => hform (b i)) htrace.summable).hasSum
  have ht1 := hasSum_le (fun i => hform (b i)) ht htrace
  rw [← hgram] at hs ⊢
  rw [traceMassEntropy_gram b A hs ht hs1 ht1]
  exact traceMassEntropy_mono b hY hT ht htrace ht1 le_rfl hform

theorem traceMassEntropy_state {n : ℕ} (ρ : State n) (hρ : FiniteEntropy ρ) :
    traceMassEntropy (numberBasis n) ρ.op = ENNReal.ofReal (1 + entropy ρ) := by
  have hs : HasSum (fun k => (inner ℂ (numberBasis n k) (entropyOperator ρ.op (numberBasis n k))).re)
      (entropy ρ) := by
    simpa only [entropy, entropyOperator_eq_complex ρ.positive.isSymmetric, numberBasis_apply, entry]
      using hρ.hasSum
  have ht := (trace_one_numberBasis ρ).add hs
  have hp := ρ.positive.add (entropyOperator_positive ρ.positive (norm_le_trace _ ρ.positive (trace_one_numberBasis ρ)))
  unfold traceMassEntropy diagonalTrace
  rw [← ht.tsum_eq, ENNReal.ofReal_tsum_of_nonneg]
  · simp only [Pi.add_apply, add_apply, inner_add_right, Complex.add_re]
  · intro k
    exact add_nonneg (ρ.positive.re_inner_nonneg_right _)
      ((entropyOperator_positive ρ.positive (norm_le_trace _ ρ.positive (trace_one_numberBasis ρ))).re_inner_nonneg_right _)
  · exact ht.summable

theorem traceMassEntropy_scale_lower {n : ℕ} (ρ : State n) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ENNReal.ofReal s * traceMassEntropy (numberBasis n) ρ.op ≤
      traceMassEntropy (numberBasis n) ((s : ℂ) • ρ.op) := by
  let b := numberBasis n
  have ht := trace_one_numberBasis ρ
  obtain ⟨J,c,p,hp,_,he⟩ := exists_positive_eigenbasis b ρ.positive ht
  have hop := ρ.positive.smul_of_nonneg (show 0 ≤ (s : ℂ) by exact_mod_cast hs.le)
  have hnorm : ‖(s : ℂ) • ρ.op‖ ≤ 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    exact (mul_le_mul_of_nonneg_left (norm_le_trace b ρ.positive ht) hs.le).trans (by simpa using hs1)
  have he' (j : J) : ((s : ℂ) • ρ.op) (c j) = ((s * p j : ℝ) : ℂ) • c j := by
    change (s : ℂ) • (ρ.op (c j)) = _
    rw [he, smul_smul, Complex.ofReal_mul]
  rw [traceMassEntropy_eigen _ _ ρ.positive (norm_le_trace b ρ.positive ht) he,
    traceMassEntropy_eigen _ _ hop hnorm he', ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro j
  rw [← ENNReal.ofReal_mul hs.le]
  apply ENNReal.ofReal_le_ofReal
  simp only [massEntropy, Real.negMulLog_mul]
  nlinarith [mul_nonneg (hp j) (Real.negMulLog_nonneg hs.le hs1)]

end
end ProofGraph.PhotonEntropy
