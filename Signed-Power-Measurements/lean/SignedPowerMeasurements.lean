import Wiring

/-! Exact consequences of the signed-power measurement model. -/
namespace ProofGraph.SignedPowerMeasurements
open ProofGraph.AffineOrder ProofGraph.Wiring
open scoped BigOperators

/-- Across an exponent gap, no multiple of the upper scale can cancel a smaller nonzero integer. -/
theorem split_at_gap (lo hi q : ℤ) (hq : 0 < q) (small : |lo| < q) :
    lo + q * hi = 0 ↔ lo = 0 ∧ hi = 0 := by
  constructor
  · intro eq
    have hz : hi = 0 := by
      by_contra h
      have pos := abs_pos.mpr h
      have one : 1 ≤ |hi| := by omega
      have mul := mul_le_mul_of_nonneg_left one hq.le
      have he : lo = -(q * hi) := by linarith
      rw [he, abs_neg, abs_mul, abs_of_pos hq] at small
      linarith
    exact ⟨by simpa [hz] using eq, hz⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- Moving an entire upper band preserves the zero rows of the comparison. -/
theorem move_band (lo hi b : ℤ) (hb : 0 < b) (u v : ℕ)
    (hu : |lo| < b ^ u) (hv : |lo| < b ^ v) :
    lo + b ^ u * hi = 0 ↔ lo + b ^ v * hi = 0 :=
  (split_at_gap lo hi _ (pow_pos hb _) hu).trans (split_at_gap lo hi _ (pow_pos hb _) hv).symm

/-- The sign rows flipping each tail coordinate have trivial kernel on differences
whose first entry has magnitude at most two, once there are five tail coordinates. -/
theorem tail_rows (k : ℕ) (hk : 5 ≤ k) (d : Fin (k + 1) → ℤ) (head : |d 0| ≤ 2)
    (rows : ∀ j : Fin k, 2 * d j.succ = ∑ i, d i) : ∀ i, d i = 0 := by
  let j₀ : Fin k := ⟨0, by omega⟩
  let t := d j₀.succ
  have constant (j : Fin k) : d j.succ = t := by
    dsimp [t]
    linarith [rows j, rows j₀]
  have sum : (∑ i, d i) = d 0 + (k : ℤ) * t := by
    rw [Fin.sum_univ_succ]
    simp [constant]
  have first := rows j₀
  rw [sum, constant] at first
  have hk' : (5 : ℤ) ≤ k := by exact_mod_cast hk
  have eq : d 0 = -(((k : ℤ) - 2) * t) := by linarith
  rw [eq, abs_neg, abs_mul, abs_of_nonneg (by omega : 0 ≤ (k : ℤ) - 2)] at head
  have ht : t = 0 := by
    by_contra ne
    have pos := abs_pos.mpr ne
    have one : 1 ≤ |t| := by omega
    have bound := mul_le_mul_of_nonneg_left one (by omega : 0 ≤ (k : ℤ) - 2)
    linarith
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [eq, ht]
  · rw [constant, ht]

/-- With six or more wires, the singleton flips of all outputs except output zero
recover the permutation and every complement bit using only raw inversion counts. -/
theorem singleton_inversions_identify (k : ℕ) (hk : 5 ≤ k)
    (p q : Equiv.Perm (Fin (k+1))) (A B : Cube (k+1) ≃ₗ[Bit] Cube (k+1))
    (wp : ∀ x j, A x j = x (p j)) (wq : ∀ x j, B x j = x (q j))
    (b c : Cube (k+1))
    (flips : ∀ j : Fin (k+1), j ≠ 0 →
       inversions A.toLinearMap (b + unitBit j) = inversions B.toLinearMap (c + unitBit j)) :
    p = q ∧ b = c := by
  let d := fun i => coefficient p b i - coefficient q c i
  have head : |d 0| ≤ 2 := by
    simp [d, coefficient, below, sign]
    split_ifs <;> norm_num
  have hN : (Fintype.card (Cube (k+1)) : ℤ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have a := measurement_identity p A wp b
  have z := measurement_identity q B wq c
  have rows (j : Fin k) : 2 * d j.succ = ∑ i, d i := by
    have ap := flip_difference p A wp b j.succ
    have bq := flip_difference q B wq c j.succ
    rw [flips j.succ (Fin.succ_ne_zero _)] at ap
    dsimp [d]
    rw [Finset.sum_sub_distrib]
    apply mul_left_cancel₀ hN
    linarith only [a, z, ap, bq]
  have same := tail_rows k hk d head rows
  have coeffs (i) : coefficient p b i = coefficient q c i := sub_eq_zero.mp (same i)
  simp_rw [coeffs] at a
  apply signed_wiring_identifiable p q A B wp wq b c 0 _ flips
  linarith only [a, z]

/-- The two attainable differences (2,2) and (2,-2) divide the rows between
them. Their smaller transcript distance is at most half the schedule length. -/
theorem two_pair_distance (m : ℕ) (s t : Fin m → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (ht : ∀ i, t i = 1 ∨ t i = -1) :
    min (Finset.univ.filter (fun i => 2 * s i + 2 * t i ≠ 0)).card
        (Finset.univ.filter (fun i => 2 * s i - 2 * t i ≠ 0)).card ≤ m / 2 := by
  have complement (i : Fin m) : (2 * s i - 2 * t i ≠ 0) ↔ ¬ (2 * s i + 2 * t i ≠ 0) := by
    rcases hs i with h|h <;> rcases ht i with k|k <;> norm_num [h,k]
  have count := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : Fin m => 2 * s i + 2 * t i ≠ 0)
  simp only [Fintype.card_fin, Finset.card_univ] at count
  simp_rw [complement]
  omega

/-- In a cyclic projection, copies of one shortened difference cannot wrap
around during any of the first n binomial steps. -/
theorem no_short_multiple (b : ℤ) (hb : 1 ≤ b) (h n : ℕ) (k w : ℤ)
    (hk : k ≠ 0) (hw : w ≠ 0) (steps : |k| ≤ (n : ℤ))
    (letter : |w| ≤ 1 + b ^ (h / 2)) (room : 2 * (n : ℤ) < b ^ (h / 2) - 1) :
    ¬ (b ^ h - 1 ∣ 2 * k * w) := by
  let B := b ^ (h / 2)
  have hB : 0 < B := pow_pos (by omega) _
  have square : B * B ≤ b ^ h := by
    dsimp [B]
    rw [← pow_add]
    exact pow_le_pow_right₀ hb (by omega)
  have mag : |2 * k * w| < b ^ h - 1 := by
    rw [abs_mul, abs_mul, abs_of_pos (by decide : (0:ℤ) < 2)]
    change |w| ≤ 1 + B at letter
    change 2 * (n : ℤ) < B - 1 at room
    have upper := mul_le_mul (show 2 * |k| ≤ 2 * (n : ℤ) by omega) letter
      (abs_nonneg w) (by positivity)
    have strict := mul_lt_mul_of_pos_right room (show 0 < 1 + B by omega)
    nlinarith
  intro divides
  obtain ⟨a, ha⟩ := divides
  have factor : a ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at ha
    exact (mul_ne_zero (mul_ne_zero (by decide) hk) hw) ha
  have one : 1 ≤ |a| := by have := abs_pos.mpr factor; omega
  have pos : 0 ≤ b ^ h - 1 := by have := abs_nonneg (2 * k * w); omega
  rw [ha, abs_mul, abs_of_nonneg pos] at mag
  have bound := mul_le_mul_of_nonneg_left one pos
  linarith

theorem distinct_binomial_residues (b : ℤ) (hb : 1 ≤ b) (h n : ℕ) (w l : ℤ)
    (hw : w ≠ 0) (letter : |w| ≤ 1 + b ^ (h/2)) (room : 2 * (n : ℤ) < b ^ (h/2) - 1)
    (i j : Fin (n+1)) (ne : i ≠ j) :
    ¬ ((2 * (i : ℤ) - l) * w ≡ (2 * (j : ℤ) - l) * w [ZMOD b ^ h - 1]) := by
  intro same
  have diff : (j : ℤ) - (i : ℤ) ≠ 0 := by
    intro eq
    apply ne
    apply Fin.ext
    omega
  apply no_short_multiple b hb h n ((j : ℤ) - i) w diff hw (by
    rw [abs_le]; constructor <;> omega) letter room
  convert Int.modEq_iff_dvd.mp same using 1
  ring

end ProofGraph.SignedPowerMeasurements
