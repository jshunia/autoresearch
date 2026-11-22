import AffineOrder

/-! Inversion counts as measurements of signed coordinate permutations. Coordinates
are numbered by increasing significance and p maps output positions to input positions. -/
namespace ProofGraph.Wiring
open ProofGraph.AffineOrder
variable {n : ℕ}

def below (p : Equiv.Perm (Fin n)) (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun k => k < p j ∧ p.symm k < j

def support (d : Cube n) : Finset (Fin n) := Finset.univ.filter fun k => d k ≠ 0

def indicator (s : Finset (Fin n)) : Cube n := fun k => if k ∈ s then 1 else 0

@[simp] theorem support_indicator (s : Finset (Fin n)) : support (indicator s) = s := by
  ext k; by_cases hk : k ∈ s <;> simp [support,indicator,hk]

@[simp] theorem indicator_support (d : Cube n) : indicator (support d) = d := by
  ext k; by_cases hk : d k = 0
  · simp [indicator,support,hk]
  · simp [indicator,support,bit_one hk]

def cell (p : Equiv.Perm (Fin n)) (j : Fin n) : Finset (Cube n) :=
  Finset.univ.filter fun d => d (p j) ≠ 0 ∧ ∀ k, d k ≠ 0 → k = p j ∨ k ∈ below p j

theorem cell_card (p : Equiv.Perm (Fin n)) (j : Fin n) :
    (cell p j).card = 2 ^ (below p j).card := by
  classical
  let i := p j
  have no : i ∉ below p j := by simp [below,i]
  have image : cell p j = (below p j).powerset.image (fun s => indicator (insert i s)) := by
    ext d
    constructor
    · intro hd
      obtain ⟨di,rest⟩ := (Finset.mem_filter.mp hd).2
      refine Finset.mem_image.mpr ⟨(support d).erase i, Finset.mem_powerset.mpr ?_,?_⟩
      · intro k hk
        obtain ⟨ki,hs⟩ := Finset.mem_erase.mp hk
        exact (rest k ((Finset.mem_filter.mp hs).2)).resolve_left ki
      · have hi : i ∈ support d := by simpa [support,i] using di
        rw [Finset.insert_erase hi,indicator_support]
    · intro hd
      obtain ⟨s,sub,rfl⟩ := Finset.mem_image.mp hd
      obtain sub := Finset.mem_powerset.mp sub
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_,?_⟩
      · simp [indicator,i]
      · intro k nz
        by_cases eq : k = i
        · exact Or.inl eq
        · right;apply sub
          by_contra h
          simp [indicator,eq,h] at nz
  rw [image, Finset.card_image_of_injOn, Finset.card_powerset]
  intro s hs t ht same
  have both := congrArg support same
  simp only [support_indicator] at both
  have ns : i ∉ s := fun h => no (Finset.mem_powerset.mp hs h)
  have nt : i ∉ t := fun h => no (Finset.mem_powerset.mp ht h)
  simpa [Finset.erase_insert,ns,nt] using congrArg (fun a : Finset (Fin n) => a.erase i) both

theorem mem_cell_iff_pivots (p : Equiv.Perm (Fin n)) (A : Cube n ≃ₗ[Bit] Cube n)
    (wire : ∀ x j, A x j = x (p j)) (d : Cube n) (hd : d ≠ 0) (j : Fin n) :
    d ∈ cell p j ↔ pivot d hd = p j ∧ pivot (A d) (fun h => hd (A.map_eq_zero_iff.mp h)) = j := by
  have ha : A d ≠ 0 := fun h => hd (A.map_eq_zero_iff.mp h)
  constructor
  · intro mem
    obtain ⟨di,smaller⟩ := (Finset.mem_filter.mp mem).2
    constructor
    · apply pivot_of_support hd _ di
      intro k hk
      rcases smaller k hk with h|h
      · exact h.le
      · exact ((Finset.mem_filter.mp h).2.1).le
    · apply pivot_of_support ha _ (by rwa [wire])
      intro k hk
      rw [wire] at hk
      rcases smaller (p k) hk with h|h
      · exact (p.injective h).le
      · simpa using ((Finset.mem_filter.mp h).2.2).le
  · rintro ⟨hp,hj⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp ▸ pivot_value d hd,?_⟩
    intro k hk
    by_cases eq : k = p j
    · exact Or.inl eq
    · right; apply Finset.mem_filter.mpr
      have lower := below_pivot hd hk
      have outer := below_pivot ha (i:=p.symm k) (by simpa [wire] using hk)
      have neq : p.symm k ≠ j := fun h => eq (by rw [←h];simp)
      exact ⟨Finset.mem_univ _, lt_of_le_of_ne (hp ▸ lower) eq,lt_of_le_of_ne (hj ▸ outer) neq⟩

theorem copy_iff (p : Equiv.Perm (Fin n)) (A : Cube n ≃ₗ[Bit] Cube n)
    (wire : ∀ x j, A x j = x (p j)) (j i : Fin n) :
    copies A.toLinearMap j i ↔ p j = i := by
  constructor
  · intro c
    have h : A (unitBit i) j = unitBit i i := c _
    by_contra ne
    simp [wire,unitBit,ne] at h
  · intro h x; change A x j = x i;rw [wire,h]

/-- Each copy contributes one signed power of two, determined by the rank of its
input among the inputs driving outputs 0 through j. -/
theorem wiring_spectrum (p : Equiv.Perm (Fin n)) (A : Cube n ≃ₗ[Bit] Cube n)
    (wire : ∀ x j, A x j = x (p j)) (b : Cube n) :
    concordance A.toLinearMap b =
      ∑ j, (Fintype.card (Cube n) : ℤ) * sign (b j) * 2 ^ (below p j).card := by
  classical
  let N : ℤ := Fintype.card (Cube n)
  let term (d : Cube n) (j : Fin n) : ℤ := if d ∈ cell p j then N * sign (b j) else 0
  rw [concordance_formula]
  calc
    _ = ∑ d, ∑ j, term d j := by
      apply Finset.sum_congr rfl; intro d _
      by_cases hd : d = 0
      · subst d; simp [term,cell]
      · have ha : A d ≠ 0 := fun h => hd (A.map_eq_zero_iff.mp h)
        let j := pivot (A d) ha
        rw [Finset.sum_eq_single j]
        · simp [term,hd,mem_cell_iff_pivots p A wire d hd,copy_iff p A wire,j,N,eq_comm]
        · intro k _ ne
          have diff : pivot (A d) ha ≠ k := Ne.symm ne
          simp [term,mem_cell_iff_pivots p A wire d hd,diff]
        · simp
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl;intro j _
      simp [term,N,Finset.sum_ite_mem,cell_card,mul_comm]

def coefficient (p : Equiv.Perm (Fin n)) (b : Cube n) (j : Fin n) : ℤ :=
  sign (b j) * 2 ^ (below p j).card

theorem measurement_identity (p : Equiv.Perm (Fin n)) (A : Cube n ≃ₗ[Bit] Cube n)
    (wire : ∀ x j, A x j = x (p j)) (b : Cube n) :
    (Fintype.card (Cube n) : ℤ) * (∑ j, coefficient p b j) + 4 * inversions A.toLinearMap b =
      (Fintype.card (Cube n) : ℤ) * (Fintype.card (Cube n) - 1) := by
  have h := concordance_add_four_inversions A b
  rw [wiring_spectrum p A wire] at h
  simpa [Finset.mul_sum,coefficient,mul_assoc] using h

theorem flip_difference (p : Equiv.Perm (Fin n)) (A : Cube n ≃ₗ[Bit] Cube n)
    (wire : ∀ x j, A x j = x (p j)) (b : Cube n) (j : Fin n) :
    2 * (inversions A.toLinearMap (b + unitBit j) - inversions A.toLinearMap b) =
       Fintype.card (Cube n) * coefficient p b j := by
  have point (k : Fin n) : coefficient p b k - coefficient p (b+unitBit j) k =
        if k = j then 2 * coefficient p b j else 0 := by
    by_cases h : k = j
    · subst k
      have sign_one : sign (1 : Bit) = -1 := by decide
      simp [coefficient,Pi.add_apply,unitBit,sign_add,sign_one];ring
    · simp [coefficient,Pi.add_apply,unitBit,h]
  have total : (∑ k, coefficient p b k) - (∑ k, coefficient p (b+unitBit j) k) =
        2 * coefficient p b j := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [point]
    simp
  have h := measurement_identity p A wire b
  have h' := measurement_identity p A wire (b+unitBit j)
  nlinarith only [h,h',congrArg (fun t : ℤ => (Fintype.card (Cube n) : ℤ) * t) total]

/-- Baseline and all coordinate flips except a fixed one recover every signed coefficient. -/
theorem measurements_determine_spectrum
    (p q : Equiv.Perm (Fin n)) (A B : Cube n ≃ₗ[Bit] Cube n)
    (wp : ∀ x j, A x j = x (p j)) (wq : ∀ x j, B x j = x (q j))
    (b c : Cube n) (skip : Fin n)
    (base : inversions A.toLinearMap b = inversions B.toLinearMap c)
    (flips : ∀ j, j ≠ skip →
       inversions A.toLinearMap (b+unitBit j) = inversions B.toLinearMap (c+unitBit j)) :
    ∀ j, coefficient p b j = coefficient q c j := by
  have N : (Fintype.card (Cube n) : ℤ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have same (j : Fin n) (ne : j ≠ skip) : coefficient p b j = coefficient q c j := by
    have a := flip_difference p A wp b j
    rw [base,flips j ne] at a
    exact mul_left_cancel₀ N (a.symm.trans (flip_difference q B wq c j))
  have a := measurement_identity p A wp b
  rw [base] at a
  have combined := a.trans (measurement_identity q B wq c).symm
  have totals := mul_left_cancel₀ N (add_right_cancel combined)
  have rest : ∑ j ∈ Finset.univ.erase skip, coefficient p b j =
      ∑ j ∈ Finset.univ.erase skip, coefficient q c j :=
    Finset.sum_congr rfl fun j hj => same j (Finset.mem_erase.mp hj).1
  intro j;by_cases h : j = skip
  · subst j
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ skip),
        ← Finset.sum_erase_add _ _ (Finset.mem_univ skip),rest] at totals
    exact add_left_cancel totals
  · exact same j h

def earlier (p : Equiv.Perm (Fin n)) (j : Fin n) : Finset (Fin n) :=
  (Finset.Iio j).filter fun k => p k < p j

theorem below_card (p : Equiv.Perm (Fin n)) (j : Fin n) :
    (below p j).card = (earlier p j).card := by
  have h : below p j = (earlier p j).map p.toEmbedding := by
    ext k
    constructor
    · intro hk;obtain ⟨h1,h2⟩ := (Finset.mem_filter.mp hk).2
      exact Finset.mem_map.mpr ⟨p.symm k,by simp [earlier,h1,h2],p.apply_symm_apply k⟩
    · intro hk;obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp hk
      simpa [below,earlier,and_comm] using hl
  rw [h,Finset.card_map]

private theorem reverse_lt {a b c d : Fin n} (ab : a ≠ b) (cd : c ≠ d)
    (h : a < b ↔ c < d) : b < a ↔ d < c := by omega

private theorem prefix_one (p q : Equiv.Perm (Fin n)) (j : Fin n)
    (smaller : ∀ a, a < j → ∀ b, b < j → (p a < p b ↔ q a < q b))
    (size : (earlier p j).card = (earlier q j).card) (a : Fin n)
    (aj : a < j) (pai : p a < p j) : q a < q j := by
  by_contra h
  have ja : q j < q a := lt_of_le_of_ne (le_of_not_gt h) (fun e => (ne_of_gt aj) (q.injective e))
  have sub : earlier q j ⊆ earlier p j := by
    intro k hk;obtain ⟨kj,kq⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr ⟨kj,lt_trans ((smaller k (Finset.mem_Iio.mp kj) a aj).mpr (lt_trans kq ja)) pai⟩
  have strict : earlier q j ⊂ earlier p j := Finset.ssubset_iff_subset_ne.mpr ⟨sub,by
    intro eq
    have pin : a ∈ earlier p j := by simp [earlier,aj,pai]
    rw [←eq] at pin
    exact h (Finset.mem_filter.mp pin).2⟩
  exact (Nat.ne_of_lt (Finset.card_lt_card strict)) size.symm

/-- Insertion ranks determine the entire order of the coordinates. -/
theorem ranks_injective (p q : Equiv.Perm (Fin n))
    (cards : ∀ j, (earlier p j).card = (earlier q j).card) : p = q := by
  have prefixOrder (j : Fin n) : ∀ a, a < j → (p a < p j ↔ q a < q j) := by
    let wf : WellFounded (fun a b : Fin n => a < b) := wellFounded_lt
    induction j using wf.induction with
    | h j ih =>
      have smaller (a : Fin n) (ha : a < j) (b : Fin n) (hb : b < j) : p a < p b ↔ q a < q b := by
        rcases lt_trichotomy a b with ab|eq|ba
        · exact ih b hb a ab
        · simp [eq]
        · exact reverse_lt (fun e => ba.ne (p.injective e)) (fun e => ba.ne (q.injective e)) (ih a ha b ba)
      intro a ha
      exact ⟨prefix_one p q j smaller (cards j) a ha,
        prefix_one q p j (fun a ha b hb => (smaller a ha b hb).symm) (cards j).symm a ha⟩
  have comp (i j : Fin n) : p i < p j ↔ q i < q j := by
    rcases lt_trichotomy i j with h|eq|h
    · exact prefixOrder j i h
    · simp [eq]
    · exact reverse_lt (fun e => h.ne (p.injective e)) (fun e => h.ne (q.injective e)) (prefixOrder i j h)
  have count (r : Equiv.Perm (Fin n)) (j : Fin n) :
      (Finset.univ.filter fun i => r i < r j).card = (r j).val := by
    have eq : (Finset.univ.filter fun i => r i < r j).map r.toEmbedding = Finset.Iio (r j) := by
      ext k; constructor
      · intro h;obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp h
        exact Finset.mem_Iio.mpr (Finset.mem_filter.mp hl).2
      · intro h;exact Finset.mem_map.mpr ⟨r.symm k,by simpa using h,r.apply_symm_apply k⟩
    rw [← Finset.card_map (f:=r.toEmbedding),eq,Fin.card_Iio]
  ext j
  rw [←count p j,←count q j]
  congr 1;ext i;simp [comp]

private theorem signed_power_inj {a b : Bit} {i j : ℕ}
    (h : sign a * (2 : ℤ)^i = sign b * (2 : ℤ)^j) : a = b ∧ i = j := by
  have pos₁ : (0 : ℤ) < 2^i := by positivity
  have pos₂ : (0 : ℤ) < 2^j := by positivity
  have eq : a = b := by
    by_cases za : a = 0 <;> by_cases zb : b = 0
    · exact za.trans zb.symm
    · simp [sign,za,zb] at h;omega
    · simp [sign,za,zb] at h;omega
    · exact (bit_one za).trans (bit_one zb).symm
  subst b
  have nonzero : sign a ≠ 0 := by unfold sign;split <;> decide
  exact ⟨rfl,pow_right_injective₀ (by norm_num : (0 : ℤ) < 2) (by norm_num) (mul_left_cancel₀ nonzero h)⟩

/-- For n positive bits these are n fixed scalar measurements. They identify both
the affine translation and the permutation of input coordinates. -/
theorem signed_wiring_identifiable
    (p q : Equiv.Perm (Fin n)) (A B : Cube n ≃ₗ[Bit] Cube n)
    (wp : ∀ x j, A x j = x (p j)) (wq : ∀ x j, B x j = x (q j))
    (b c : Cube n) (skip : Fin n)
    (base : inversions A.toLinearMap b = inversions B.toLinearMap c)
    (flips : ∀ j, j ≠ skip → inversions A.toLinearMap (b+unitBit j) =
                              inversions B.toLinearMap (c+unitBit j)) : p = q ∧ b = c := by
  have spec := measurements_determine_spectrum p q A B wp wq b c skip base flips
  have both (j : Fin n) := signed_power_inj (spec j)
  exact ⟨ranks_injective p q fun j => by simpa only [below_card] using (both j).2,
    funext fun j => (both j).1⟩

def coordinateMap (p : Equiv.Perm (Fin n)) : Cube n ≃ₗ[Bit] Cube n where
  toFun x j := x (p j)
  invFun y i := y (p.symm i)
  left_inv x := by ext i;simp
  right_inv y := by ext j;simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem earlier_rev (j : Fin n) : earlier Fin.revPerm j = ∅ := by
  ext k
  simp [earlier,Fin.revPerm]
  omega

theorem bit_reversal_inversions (n : ℕ) :
    4 * inversions (coordinateMap (Fin.revPerm (n:=n))).toLinearMap 0 =
      (2 : ℤ)^n * ((2 : ℤ)^n - n - 1) := by
  let p : Equiv.Perm (Fin n) := Fin.revPerm
  have zero (j : Fin n) : (below p j).card = 0 := by rw [below_card,earlier_rev,Finset.card_empty]
  have h := measurement_identity p (coordinateMap p) (fun _ _ => rfl) 0
  simp [coefficient,zero,sign,Cube,Bit,Fintype.card_pi,ZMod.card] at h
  change 4 * inversions (coordinateMap p).toLinearMap 0 = _
  linear_combination h

/-- The exact inversion loss relative to reversing the coordinate order. -/
theorem reversal_defect (p : Equiv.Perm (Fin n)) :
    4 * (inversions (coordinateMap (Fin.revPerm (n := n))).toLinearMap 0 -
         inversions (coordinateMap p).toLinearMap 0) =
      (2 : ℤ)^n * ∑ j, ((2 : ℤ)^(earlier p j).card - 1) := by
  have h := measurement_identity p (coordinateMap p) (fun _ _ => rfl) 0
  simp [coefficient,below_card,sign,Cube,Bit,Fintype.card_pi,ZMod.card] at h
  rw [Finset.sum_sub_distrib]
  simp
  linear_combination bit_reversal_inversions n - h

/-- Each coordinate pair agreeing with increasing order costs at least N/4
inversions relative to bit reversal. -/
theorem reversal_stability (p : Equiv.Perm (Fin n)) :
    (2 : ℤ)^n * (∑ j, ((earlier p j).card : ℤ)) ≤
      4 * (inversions (coordinateMap (Fin.revPerm (n := n))).toLinearMap 0 -
           inversions (coordinateMap p).toLinearMap 0) := by
  rw [reversal_defect]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j _
  have lt : ((earlier p j).card : ℤ) < 2 ^ (earlier p j).card := by
    exact_mod_cast (Nat.lt_two_pow_self : (earlier p j).card < 2 ^ (earlier p j).card)
  omega

/-- Reversal is the unique unbiased coordinate permutation attaining its inversion count. -/
theorem reversal_rigid (p : Equiv.Perm (Fin n))
    (equal : inversions (coordinateMap p).toLinearMap 0 =
             inversions (coordinateMap (Fin.revPerm (n := n))).toLinearMap 0) : p = Fin.revPerm := by
  have bound := reversal_stability p
  rw [equal,sub_self,mul_zero] at bound
  have total : (∑ j, ((earlier p j).card : ℤ)) ≤ 0 := by
    by_contra! pos
    exact (not_lt_of_ge bound) (mul_pos (by positivity) pos)
  apply ranks_injective
  intro j
  rw [earlier_rev,Finset.card_empty]
  have le := Finset.single_le_sum (f := fun k : Fin n => ((earlier p k).card : ℤ))
    (fun _ _ => by positivity) (Finset.mem_univ j)
  omega

end ProofGraph.Wiring
