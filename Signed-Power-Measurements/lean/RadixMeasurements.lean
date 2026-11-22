import Mathlib

/-! Evaluation at a transcendental radix transfers Hamming separation
from any one coefficient layer to the exact measured values. -/
namespace ProofGraph.RadixMeasurements
open Polynomial
open scoped BigOperators

noncomputable def rowPolynomial {n : ℕ} (s : Fin n → ℚ) (x : Fin n → ℚ[X]) : ℚ[X] :=
  ∑ j, C (s j) * x j

theorem row_coeff {n : ℕ} (s : Fin n → ℚ) (x : Fin n → ℚ[X]) (e : ℕ) :
    (rowPolynomial s x).coeff e = ∑ j, s j * (x j).coeff e := by
  simp [rowPolynomial, finsetSum_coeff, coeff_C_mul]

theorem row_eval {K : Type*} [Field K] [CharZero K] {n : ℕ} (α : K)
    (s : Fin n → ℚ) (x : Fin n → ℚ[X]) :
    aeval α (rowPolynomial s x) = ∑ j, algebraMap ℚ K (s j) * aeval α (x j) := by
  simp [rowPolynomial]

theorem transcendental_row_iff {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (α : K) (ha : Transcendental ℚ α) (s : Fin n → ℚ) (x y : Fin n → ℚ[X]) :
    (∑ j, algebraMap ℚ K (s j) * aeval α (x j)) =
    (∑ j, algebraMap ℚ K (s j) * aeval α (y j)) ↔
    ∀ e, (∑ j, s j * (x j).coeff e) = ∑ j, s j * (y j).coeff e := by
  rw [← row_eval, ← row_eval]
  have inj : Function.Injective (aeval α : ℚ[X] →ₐ[ℚ] K) := transcendental_iff_injective.mp ha
  rw [inj.eq_iff]
  constructor
  · intro h e
    simpa only [row_coeff] using congrArg (fun f : ℚ[X] => f.coeff e) h
  · intro h
    ext e
    simp only [row_coeff, h]

theorem layer_distance_le {K : Type*} [Field K] [CharZero K] [DecidableEq K] {n m : ℕ}
    (α : K) (ha : Transcendental ℚ α) (A : Fin m → Fin n → ℚ)
    (x y : Fin n → ℚ[X]) (e : ℕ) :
    (Finset.univ.filter (fun i => (∑ j, A i j * (x j).coeff e) ≠ ∑ j, A i j * (y j).coeff e)).card ≤
    (Finset.univ.filter (fun i => (∑ j, algebraMap ℚ K (A i j) * aeval α (x j)) ≠
                                  ∑ j, algebraMap ℚ K (A i j) * aeval α (y j))).card := by
  apply Finset.card_le_card
  intro i hi
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => ?_⟩
  exact (Finset.mem_filter.mp hi).2 ((transcendental_row_iff α ha (A i) x y).mp h e)

/-- In characteristic two every permitted sign maps to one. -/
theorem char_two_sign {K : Type*} [Field K] [CharP K 2] (r : Bool) :
    (if r then (1 : K) else -1) = 1 := by
  have h : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  cases r <;> simp_all [neg_eq_iff_add_eq_zero, ← two_mul]

end ProofGraph.RadixMeasurements
