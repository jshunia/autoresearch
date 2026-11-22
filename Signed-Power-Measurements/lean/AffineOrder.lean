import Mathlib

/-! Signed concordance of an affine permutation of the binary cube in unsigned binary
order. Coordinate zero is the least significant bit. The sum over ordered pairs
counts each unordered pair twice. -/
namespace ProofGraph.AffineOrder

abbrev Bit := ZMod 2
abbrev Cube (n : ℕ) := Fin n → Bit

def sign (z : Bit) : ℤ := if z = 0 then 1 else -1

theorem sign_add (a b : Bit) : sign (a + b) = sign a * sign b := by
  fin_cases a <;> fin_cases b <;> decide

theorem sign_sq (a : Bit) : sign a * sign a = 1 := by
  fin_cases a <;> decide

theorem self_add (a : Bit) : a + a = 0 := by
  fin_cases a <;> decide

variable {n : ℕ}

/-- The highest differing position for words separated by a nonzero difference. -/
def pivot (d : Cube n) (h : d ≠ 0) : Fin n :=
  (Finset.univ.filter (fun i => d i ≠ 0)).max' (by
    by_contra! empty
    apply h
    ext i
    by_contra hi
    have hm : i ∈ Finset.univ.filter (fun k => d k ≠ 0) := by simpa using hi
    simp [empty] at hm)

/-- The sign of the ordinary unsigned comparison of x and x+d, including ties. -/
def comparison (x d : Cube n) : ℤ :=
  if h : d = 0 then 0 else sign (x (pivot d h))

/-- Twice the number of increasing unordered pairs minus twice the number of inversions. -/
def concordance (A : Cube n →ₗ[Bit] Cube n) (b : Cube n) : ℤ :=
  ∑ d : Cube n, ∑ x : Cube n, comparison x d * comparison (A x + b) (A d)

def copies (A : Cube n →ₗ[Bit] Cube n) (j i : Fin n) : Prop :=
  ∀ x : Cube n, A x j = x i

noncomputable instance copiesDec (A : Cube n →ₗ[Bit] Cube n) (j i : Fin n) : Decidable (copies A j i) :=
  Classical.propDecidable _

private theorem differing_signs (a b : Bit) (h : a ≠ b) : sign a * sign b = -1 := by
  fin_cases a <;> fin_cases b <;> first | contradiction | decide

/-- Character orthogonality on each fixed pair of decisive input and output bits. -/
theorem fiber_sum (A : Cube n →ₗ[Bit] Cube n) (b : Cube n) (i j : Fin n) :
    (∑ x : Cube n, sign (x i) * sign ((A x + b) j)) =
      if copies A j i then (Fintype.card (Cube n) : ℤ) * sign (b j) else 0 := by
  classical
  split_ifs with h
  · calc
      _ = ∑ _x : Cube n, sign (b j) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Pi.add_apply, h x, sign_add, ← mul_assoc, sign_sq, one_mul]
      _ = _ := by simp
  · obtain ⟨v, hv⟩ : ∃ v : Cube n, A v j ≠ v i := by
      simpa [copies] using h
    let g := fun x : Cube n => sign (x i) * sign ((A x + b) j)
    have flip (x : Cube n) : g (x + v) = -g x := by
      have hs := differing_signs (v i) (A v j) (Ne.symm hv)
      dsimp [g]
      rw [map_add]
      simp only [Pi.add_apply, sign_add]
      linear_combination sign (x i) * sign (A x j) * sign (b j) * hs
    have translated := Equiv.sum_comp (Equiv.addRight v) g
    change (∑ x : Cube n, g (x + v)) = ∑ x : Cube n, g x at translated
    simp_rw [flip, Finset.sum_neg_distrib] at translated
    change (∑ x : Cube n, g x) = 0
    omega

/-- Only copied coordinates contribute; each nonzero difference selects its pivots. -/
theorem concordance_formula (A : Cube n ≃ₗ[Bit] Cube n) (b : Cube n) :
    concordance A.toLinearMap b =
      ∑ d : Cube n, if hd : d = 0 then 0 else
        let i := pivot d hd
        let j := pivot (A d) (fun h => hd (A.map_eq_zero_iff.mp h))
        if copies A.toLinearMap j i then (Fintype.card (Cube n) : ℤ) * sign (b j) else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : d = 0
  · subst d
    simp [comparison]
  · have ha : A d ≠ 0 := fun h => hd (A.map_eq_zero_iff.mp h)
    simpa [comparison, hd, ha] using
      (fiber_sum A.toLinearMap b (pivot d hd) (pivot (A d) ha))

/-- An invertible map with no copied output has exactly balanced concordance for every bias. -/
theorem all_biases_balanced (A : Cube n ≃ₗ[Bit] Cube n)
    (h : ∀ j i, ¬ copies A.toLinearMap j i) (b : Cube n) :
    concordance A.toLinearMap b = 0 := by
  classical
  rw [concordance_formula]
  apply Finset.sum_eq_zero
  intro d _
  split_ifs <;> simp_all


/-- Counts each inverted unordered pair once, from its smaller input endpoint. -/
def inverted (A : Cube n →ₗ[Bit] Cube n) (b x d : Cube n) : ℤ :=
  if comparison x d = 1 ∧ comparison (A x + b) (A d) = -1 then 1 else 0

def inversions (A : Cube n →ₗ[Bit] Cube n) (b : Cube n) : ℤ :=
  ∑ d : Cube n, ∑ x : Cube n, inverted A b x d

theorem pivot_value (d : Cube n) (hd : d ≠ 0) : d (pivot d hd) ≠ 0 := by
  classical
  unfold pivot
  exact (Finset.mem_filter.mp (Finset.max'_mem (Finset.univ.filter fun k : Fin n => d k ≠ 0) _)).2

private theorem flip_sign (a c : Bit) (hc : c ≠ 0) : sign (a + c) = -sign a := by
  fin_cases a <;> fin_cases c <;> first | contradiction | decide

theorem reverse_comparison (x d : Cube n) :
    comparison (x + d) d = -comparison x d := by
  by_cases hd : d = 0
  · simp [comparison,hd]
  · simp only [comparison,dif_neg hd,Pi.add_apply]
    exact flip_sign _ _ (pivot_value d hd)

private theorem nonzero_vote (x d : Cube n) (hd : d ≠ 0) :
    comparison x d = 1 ∨ comparison x d = -1 := by
  simp only [comparison,dif_neg hd,sign]
  split <;> simp

private theorem pair_accounting (A : Cube n ≃ₗ[Bit] Cube n) (b d x : Cube n) (hd : d ≠ 0) :
    comparison x d * comparison (A x + b) (A d) +
      2 * (inverted A.toLinearMap b x d + inverted A.toLinearMap b (x+d) d) = 1 := by
  have ha : A d ≠ 0 := fun h => hd (A.map_eq_zero_iff.mp h)
  have perm : A (x+d)+b = (A x+b)+A d := by rw [map_add]; abel
  simp only [inverted,LinearEquiv.coe_coe,reverse_comparison,perm]
  rcases nonzero_vote x d hd with h|h <;>
    rcases nonzero_vote (A x+b) (A d) ha with k|k <;> simp [h,k]

/-- Signed concordance determines the ordinary unsigned binary inversion count. -/
theorem concordance_add_four_inversions (A : Cube n ≃ₗ[Bit] Cube n) (b : Cube n) :
    concordance A.toLinearMap b + 4 * inversions A.toLinearMap b =
      (Fintype.card (Cube n) : ℤ) * (Fintype.card (Cube n) - 1) := by
  classical
  let N : ℤ := Fintype.card (Cube n)
  have fiber (d : Cube n) :
      (∑ x, comparison x d * comparison (A x + b) (A d)) +
        4 * (∑ x : Cube n, inverted A.toLinearMap b x d) = if d = 0 then 0 else N := by
    split_ifs with hd
    · subst d; simp [comparison,inverted]
    · have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (Cube n))) rfl
            (fun x _ => pair_accounting A b d x hd)
      have translated := Equiv.sum_comp (Equiv.addRight d) (fun x => inverted A.toLinearMap b x d)
      change (∑ x : Cube n, inverted A.toLinearMap b (x+d) d) = _ at translated
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum,translated,
        Finset.sum_const, Finset.card_univ,nsmul_eq_mul, mul_one] at h
      dsimp [N]; linear_combination h
  unfold concordance inversions
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    _ = ∑ d : Cube n, (if d = 0 then (0 : ℤ) else N) :=
      Finset.sum_congr rfl (fun d _ => fiber d)
    _ = ∑ d : Cube n, (N - if d = 0 then N else 0) := by
      apply Finset.sum_congr rfl
      intro d _
      split_ifs <;> simp
    _ = _ := by simp [N, Finset.sum_sub_distrib]; ring

/-- Exact half of the unordered pairs are inverted, simultaneously for every bias. -/
theorem inversion_balance (A : Cube n ≃ₗ[Bit] Cube n)
    (h : ∀ j i, ¬ copies A.toLinearMap j i) (b : Cube n) :
    4 * inversions A.toLinearMap b =
      (2 : ℤ)^n * ((2 : ℤ)^n - 1) := by
  have t := concordance_add_four_inversions A b
  rw [all_biases_balanced A h b, zero_add] at t
  simpa [Cube, Bit, Fintype.card_pi, ZMod.card] using t

/-- A copy is exposed when the corresponding input and output bits decide the same pair. -/
def noExposedCopy (A : Cube n ≃ₗ[Bit] Cube n) : Prop :=
  ∀ (d : Cube n) (hd : d ≠ 0),
    ¬ copies A.toLinearMap (pivot (A d) (fun h => hd (A.map_eq_zero_iff.mp h))) (pivot d hd)

theorem balanced_iff_no_exposed_copy (A : Cube n ≃ₗ[Bit] Cube n) :
    (∀ b, concordance A.toLinearMap b = 0) ↔ noExposedCopy A := by
  classical
  constructor
  · intro all d hd hc
    let t (v : Cube n) : ℤ := if hv : v = 0 then 0 else
      if copies A.toLinearMap (pivot (A v) (fun h => hv (A.map_eq_zero_iff.mp h))) (pivot v hv)
      then ↑(Fintype.card (Cube n)) else 0
    have total : ∑ v, t v = 0 := by simpa [concordance_formula,t,sign] using all 0
    have pos (v : Cube n) : 0 ≤ t v := by unfold t; split_ifs <;> positivity
    have atd := (Finset.sum_eq_zero_iff_of_nonneg fun v _ => pos v).mp total d (Finset.mem_univ _)
    have cardpos : (0 : ℤ) < Fintype.card (Cube n) := by exact_mod_cast Fintype.card_pos
    simp [t,hd,hc] at atd
  · intro h b
    rw [concordance_formula]
    apply Finset.sum_eq_zero
    intro d _
    by_cases hd : d = 0
    · simp [hd]
    · simp [hd,h d hd]

def unitBit (i : Fin n) : Cube n := fun j => if j = i then 1 else 0

theorem bit_one {a : Bit} (h : a ≠ 0) : a = 1 := by
  have all : ∀ z : Bit, z ≠ 0 → z = 1 := by decide
  exact all a h

theorem nonzero_at {x : Cube n} {i} (h : x i ≠ 0) : x ≠ 0 := by
  intro hx; simp [hx] at h

theorem below_pivot {d : Cube n} (hd : d ≠ 0) {i} (h : d i ≠ 0) :
    i ≤ pivot d hd := by
  unfold pivot
  apply Finset.le_max'
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩

theorem pivot_of_support {x : Cube n} (h : x ≠ 0) (i : Fin n)
    (at_i : x i ≠ 0) (upper : ∀ j, x j ≠ 0 → j ≤ i) : pivot x h = i :=
  le_antisymm (upper _ (pivot_value x h)) (below_pivot h at_i)

private theorem pivot_unit (i : Fin n) (h : unitBit i ≠ 0) : pivot (unitBit i) h = i := by
  apply pivot_of_support h i (by simp [unitBit])
  intro j hj
  by_contra! lt
  simp [unitBit,ne_of_gt lt] at hj

private theorem pivot_pair (i k : Fin n) (hk : k < i) (h : unitBit i + unitBit k ≠ 0) :
    pivot (unitBit i + unitBit k) h = i := by
  apply pivot_of_support h i (by simp [unitBit,ne_of_gt hk])
  intro j hj
  by_contra! lt
  simp [Pi.add_apply,unitBit,ne_of_gt lt,ne_of_gt (lt_trans hk lt)] at hj

/-- A matrix with one mixed output has the remaining outputs wired by σ.
Any balanced such matrix must put the mixed row last and include every input in it. -/
theorem mixed_row_last_and_full (A : Cube n ≃ₗ[Bit] Cube n) (σ : Equiv.Perm (Fin n))
    (k : Fin n) (wire : ∀ i, i ≠ k → copies A.toLinearMap (σ i) i)
    (balanced : noExposedCopy A) :
    (∀ i, i ≠ k → σ i < σ k) ∧ (∀ i, A (unitBit i) (σ k) = 1) := by
  classical
  have W (l : Fin n) (hl : l ≠ k) (x : Cube n) : A x (σ l) = x l := wire l hl x
  have exposed (i : Fin n) (hi : i ≠ k) :
      σ i < σ k ∧ A (unitBit i) (σ k) ≠ 0 := by
    have hd : unitBit i ≠ 0 := nonzero_at (i:=i) (by simp [unitBit])
    have ha : A (unitBit i) ≠ 0 := fun h => hd (A.map_eq_zero_iff.mp h)
    have at_i : A (unitBit i) (σ i) ≠ 0 := by rw [W i hi]; simp [unitBit]
    have excluded : pivot (A (unitBit i)) ha ≠ σ i := by
      intro h; have bad := balanced (unitBit i) hd
      change ¬copies A.toLinearMap (pivot (A (unitBit i)) ha) (pivot (unitBit i) hd) at bad
      rw [h,pivot_unit] at bad
      exact bad (wire i hi)
    have eq : pivot (A (unitBit i)) ha = σ k := by
      obtain ⟨j,hj⟩ := σ.surjective (pivot (A (unitBit i)) ha)
      by_contra ne
      have hjk : j ≠ k := fun e => ne (hj.symm.trans (congrArg σ e))
      have nz := pivot_value (A (unitBit i)) ha
      rw [← hj,W j hjk] at nz
      have hji : j ≠ i := fun e => excluded (hj.symm.trans (congrArg σ e))
      simp [unitBit,hji] at nz
    have upper := below_pivot ha at_i
    rw [eq] at upper
    exact ⟨lt_of_le_of_ne upper (fun h => hi (σ.injective h)),eq ▸ pivot_value _ ha⟩
  refine ⟨fun i hi => (exposed i hi).1, fun i => bit_one ?_⟩
  by_cases hi : i = k
  · subst i
    intro absent
    have hz : A (unitBit k) = 0 := by
      ext j; obtain ⟨l,rfl⟩ := σ.surjective j
      by_cases h : l = k
      · simpa [h] using absent
      · rw [W l h]; simp [unitBit,h]
    have hz' := A.map_eq_zero_iff.mp hz
    have bad := congrFun hz' k
    simp [unitBit] at bad
  · exact (exposed i hi).2

/-- Ordered coordinates in a balanced permutation with exactly one mixed row. -/
theorem one_mixed_row_classification (A : Cube n ≃ₗ[Bit] Cube n) (σ : Equiv.Perm (Fin n))
    (k : Fin n) (wire : ∀ i, i ≠ k → copies A.toLinearMap (σ i) i)
    (mixed : ∀ i, ¬copies A.toLinearMap (σ k) i) :
    (∀ b, concordance A.toLinearMap b = 0) ↔
      (∀ i, i ≠ k → i < k ∧ σ i < σ k) ∧
      (∀ i, A (unitBit i) (σ k) = 1) ∧
      (∀ l i, l < i → i ≠ k → σ i < σ l) := by
  classical
  rw [balanced_iff_no_exposed_copy]
  have W (l : Fin n) (hl : l ≠ k) (x : Cube n) : A x (σ l) = x l := wire l hl x
  constructor
  · intro bal
    obtain ⟨last,full⟩ := mixed_row_last_and_full A σ k wire bal
    have pair (l i : Fin n) (hil : l < i) (hi : i ≠ k) : l ≠ k ∧ σ i < σ l := by
      let d := unitBit i + unitBit l
      have di : d i ≠ 0 := by simp [d,unitBit,ne_of_gt hil]
      have hd := nonzero_at di
      have ha : A d ≠ 0 := fun h => hd (A.map_eq_zero_iff.mp h)
      have special : A d (σ k) = 0 := by
        dsimp [d]; rw [map_add,Pi.add_apply,full,full]; exact self_add 1
      have absent := bal d hd
      change ¬ copies A.toLinearMap (pivot (A d) ha) (pivot d hd) at absent
      have hpi : pivot d hd = i := pivot_pair i l hil hd
      rw [hpi] at absent
      obtain ⟨j,hj⟩ := σ.surjective (pivot (A d) ha)
      have nz := pivot_value (A d) ha
      rw [← hj] at nz absent
      have jk : j ≠ k := fun h => nz (h ▸ special)
      have ji : j ≠ i := fun h => absent (h ▸ wire i hi)
      have jl : j = l := by
        by_contra ne
        rw [W j jk] at nz
        simp [d,Pi.add_apply,unitBit,ji,ne] at nz
      subst j
      have upper := below_pivot ha (i:=σ i) (by rwa [W i hi])
      exact ⟨jk,lt_of_le_of_ne (hj ▸ upper) (fun h => (ne_of_gt hil) (σ.injective h))⟩
    refine ⟨fun i hi => ⟨?_,last i hi⟩,full,fun l i h hi => (pair l i h hi).2⟩
    by_contra! lower
    exact (pair k i (lt_of_le_of_ne lower (Ne.symm hi)) hi).1 rfl
  · rintro ⟨top,full,rev⟩ d hd same
    have ha : A d ≠ 0 := fun h => hd (A.map_eq_zero_iff.mp h)
    let i := pivot d hd
    let j := pivot (A d) ha
    change copies A.toLinearMap j i at same
    obtain ⟨l,hl⟩ := σ.surjective j
    have lk : l ≠ k := by
      intro h; subst l; exact mixed i (hl ▸ same)
    have at_i : (unitBit i) l = (unitBit i) i := by
      calc
        _ = A (unitBit i) (σ l) := (W l lk _).symm
        _ = _ := hl ▸ same (unitBit i)
    have li : l = i := by by_contra ne; simp [unitBit,ne] at at_i
    subst l
    have single : d = unitBit i := by
      ext m
      by_cases mi : m = i
      · subst m; simpa [unitBit] using bit_one (pivot_value d hd)
      · have zero : d m = 0 := by
          by_contra nz
          have lt : m < i := lt_of_le_of_ne (below_pivot hd nz) mi
          have mk : m ≠ k := ne_of_lt (lt_trans lt (top i lk).1)
          have higher := rev m i lt lk
          have up := below_pivot ha (i:=σ m) (by rwa [W m mk])
          exact (not_le_of_gt higher) (hl ▸ up)
        simp [unitBit,mi,zero]
    have changed : A d (σ k) ≠ 0 := by rw [single,full]; decide
    have up := below_pivot ha changed
    exact (not_le_of_gt (top i lk).2) (hl ▸ up)

end ProofGraph.AffineOrder
