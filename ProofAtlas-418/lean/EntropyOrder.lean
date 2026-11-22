import OAI.Analysis.QuantumTrace.Basic

open Filter Topology Set
open OAI.QuantumTrace
open scoped ENNReal

namespace ProofGraph.PhotonEntropy

noncomputable section

/-- Adding the trace term makes the entropy integrand increasing on the entire state spectrum. -/
def massEntropy (x : ℝ) := x + Real.negMulLog x

theorem massEntropy_mono : MonotoneOn massEntropy (Icc 0 1) := by
  apply StrictMonoOn.monotoneOn
  apply strictMonoOn_of_deriv_pos (convex_Icc ..) ((continuous_id.add Real.continuous_negMulLog).continuousOn)
  intro x hx
  have hx' : x ∈ Ioo (0 : ℝ) 1 := by simpa using hx
  change 0 < deriv (fun x : ℝ => x + Real.negMulLog x) x
  rw [show deriv (fun x : ℝ => x + Real.negMulLog x) x = 1 + (-Real.log x - 1) from
    ((hasDerivAt_id x).add (Real.hasDerivAt_negMulLog hx'.1.ne')).deriv]
  linarith [Real.log_neg hx'.1 hx'.2]

universe u v
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I : Type v}

/-- An extended trace handles infinite entropy without Lean's real series convention. -/
def traceMassEntropy (b : HilbertBasis I ℂ E) (T : E →L[ℂ] E) : ℝ≥0∞ :=
  diagonalTrace b (T + entropyOperator T)

omit [CompleteSpace E] in
private theorem eigen_diagonal {J : Type*} (b : HilbertBasis J ℂ E) (T : E →L[ℂ] E)
    {p : J → ℝ} (he : ∀ i, T (b i) = (p i : ℂ) • b i) (i : J) :
    (inner ℂ (b i) (T (b i))).re = p i := by
  rw [he, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
  simp

theorem traceMassEntropy_eigen {J : Type*} (a : HilbertBasis I ℂ E) (b : HilbertBasis J ℂ E)
    {T : E →L[ℂ] E} (hT : T.IsPositive) (hn : ‖T‖ ≤ 1)
    {p : J → ℝ} (he : ∀ j, T (b j) = (p j : ℂ) • b j) :
    traceMassEntropy a T = ∑' j, ENNReal.ofReal (massEntropy (p j)) := by
  rw [traceMassEntropy, diagonalTrace_basis_independent a b (hT.add (entropyOperator_positive hT hn))]
  unfold diagonalTrace
  congr 1
  funext j
  simp only [add_apply, inner_add_right, Complex.add_re,
    eigen_diagonal b T he, eigen_diagonal b (entropyOperator T)
      (fun j => entropyOperator_apply_eigenvector hT.isSymmetric (he j)), massEntropy]

/-- Increasing modified entropy trace under quadratic-form domination. The proof measures
the smaller operator in an eigenbasis of the larger one and uses scalar Jensen. -/
theorem traceMassEntropy_mono (b : HilbertBasis I ℂ E) {X Y : E →L[ℂ] E}
    (hX : X.IsPositive) (hY : Y.IsPositive) {s t : ℝ}
    (hs : HasSum (fun i => (inner ℂ (b i) (X (b i))).re) s)
    (ht : HasSum (fun i => (inner ℂ (b i) (Y (b i))).re) t)
    (hs1 : s ≤ 1) (ht1 : t ≤ 1)
    (hXY : ∀ x, (inner ℂ x (X x)).re ≤ (inner ℂ x (Y x)).re) :
    traceMassEntropy b X ≤ traceMassEntropy b Y := by
  obtain ⟨J, c, p, hp, hsum, he⟩ := exists_positive_eigenbasis b hY ht
  have hnX := (norm_le_trace b hX hs).trans hs1
  have hnY := (norm_le_trace b hY ht).trans ht1
  rw [traceMassEntropy_eigen b c hY hnY he, traceMassEntropy,
    diagonalTrace_basis_independent b c (hX.add (entropyOperator_positive hX hnX))]
  apply ENNReal.tsum_le_tsum
  intro j
  apply ENNReal.ofReal_le_ofReal
  simp only [add_apply, inner_add_right, Complex.add_re]
  have hle := hXY (c j)
  rw [eigen_diagonal c Y he] at hle
  have hp1 : p j ≤ 1 := (hsum.summable.le_tsum j (fun k _ => hp k)).trans (hsum.tsum_eq.le.trans ht1)
  exact (add_le_add_right (entropyOperator_quadratic_le b hX hs (c j) (c.orthonormal.norm_eq_one j)) _).trans
    (massEntropy_mono ⟨hX.re_inner_nonneg_right _, hle.trans hp1⟩ ⟨hp _, hp1⟩ hle)

private theorem massEntropy_factor {x : ℝ} (hx : 0 ≤ x) :
    ENNReal.ofReal (massEntropy x) = ENNReal.ofReal x * ENNReal.ofReal (1 - Real.log x) := by
  rw [← ENNReal.ofReal_mul hx]
  congr 1
  simp [massEntropy, Real.negMulLog]
  ring

/-- The two reduced operators of a pure vector have the same entropy trace.
The proof pairs eigenbases through the matrix entries of a single operator, allowing
zero modes on either side and divergent entropy. -/
theorem traceMassEntropy_gram (b : HilbertBasis I ℂ E) (A : E →L[ℂ] E) {s t : ℝ}
    (hs : HasSum (fun i => (inner ℂ (b i) ((A.adjoint.comp A) (b i))).re) s)
    (ht : HasSum (fun i => (inner ℂ (b i) ((A.comp A.adjoint) (b i))).re) t)
    (hs1 : s ≤ 1) (ht1 : t ≤ 1) :
    traceMassEntropy b (A.adjoint.comp A) = traceMassEntropy b (A.comp A.adjoint) := by
  have hX := A.isPositive_adjoint_comp_self
  have hY := A.isPositive_self_comp_adjoint
  obtain ⟨J, c, p, hp, _, hep⟩ := exists_positive_eigenbasis b hX hs
  obtain ⟨K, d, q, hq, _, heq⟩ := exists_positive_eigenbasis b hY ht
  rw [traceMassEntropy_eigen b c hX ((norm_le_trace b hX hs).trans hs1) hep,
      traceMassEntropy_eigen b d hY ((norm_le_trace b hY ht).trans ht1) heq]
  let w (j : J) (k : K) := ENNReal.ofReal (‖inner ℂ (d k) (A (c j))‖ ^ 2)
  have col (j : J) : ∑' k, w j k = ENNReal.ofReal (p j) := by
    rw [show (∑' k, w j k) = _ from basis_tsum_enorm_sq d (A (c j))]
    congr 1
    rw [← eigen_diagonal c _ hep j, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have row (k : K) : ∑' j, w j k = ENNReal.ofReal (q k) := by
    have hflip (j : J) : w j k = ENNReal.ofReal (‖inner ℂ (c j) (A.adjoint (d k))‖ ^ 2) := by
      unfold w
      rw [← ContinuousLinearMap.adjoint_inner_left, norm_inner_symm]
    simp only [hflip, basis_tsum_enorm_sq]
    congr 1
    rw [← eigen_diagonal d _ heq k, ContinuousLinearMap.comp_apply,
      ← ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have pair (j : J) (k : K) :
      w j k * ENNReal.ofReal (1 - Real.log (p j)) =
        w j k * ENNReal.ofReal (1 - Real.log (q k)) := by
    by_cases hz : inner ℂ (d k) (A (c j)) = 0
    · simp [w, hz]
    have hsym := hY.isSymmetric (d k) (A (c j))
    have hmap : (A.comp A.adjoint) (A (c j)) = (p j : ℂ) • A (c j) := by
      change A ((A.adjoint.comp A) (c j)) = _
      rw [hep, map_smul]
    change inner ℂ ((A.comp A.adjoint) (d k)) (A (c j)) = inner ℂ (d k) ((A.comp A.adjoint) (A (c j))) at hsym
    rw [heq, hmap, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at hsym
    have he : q k = p j := Complex.ofReal_injective (mul_right_cancel₀ hz hsym)
    rw [he]
  calc
    _ = ∑' j, ∑' k, w j k * ENNReal.ofReal (1 - Real.log (p j)) := by
      congr 1
      funext j
      rw [massEntropy_factor (hp j), ← col j, ENNReal.tsum_mul_right]
    _ = ∑' k, ∑' j, w j k * ENNReal.ofReal (1 - Real.log (q k)) := by
      simp only [pair]
      exact ENNReal.tsum_comm
    _ = _ := by
      congr 1
      funext k
      rw [massEntropy_factor (hq k), ← row k, ENNReal.tsum_mul_right]

end
end ProofGraph.PhotonEntropy
