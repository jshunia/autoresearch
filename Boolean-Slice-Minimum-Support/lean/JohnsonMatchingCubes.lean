import Mathlib

/-! Alternating moments and incidence weights used for minimum support on a uniform layer. -/
namespace ProofGraph.JohnsonMatchingCubes

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- Inverse incidence counts recover the family size by summing over the sampled cubes. -/
theorem weighted_incidence {σ τ : Type*} (cubes : Finset σ) (family : Finset τ)
    (sees : σ → τ → Prop) [∀ c x, Decidable (sees c x)] (weight : τ → ℕ)
    (multiplicity : ∀ x ∈ family, (cubes.filter (fun c => sees c x)).card * weight x = cubes.card) :
    ∑ c ∈ cubes, ∑ x ∈ family, (if sees c x then weight x else 0) =
      family.card * cubes.card := by
  rw [sum_comm]
  calc
    _ = ∑ x ∈ family, (cubes.filter (fun c => sees c x)).card * weight x := by
      apply sum_congr rfl
      intro x _
      rw [← sum_filter]
      simp
    _ = ∑ _x ∈ family, cubes.card := sum_congr rfl multiplicity
    _ = _ := by simp

variable {G : Type*} [AddCommGroup G]

private theorem alternating_monomial (U S : Finset ι) (c : G) (h : S.card < U.card) :
    ∑ A ∈ U.powerset, ((-1 : ℤ) ^ A.card) • (if S ⊆ A then c else 0) = 0 := by
  obtain ⟨i, hi, hs⟩ := exists_mem_notMem_of_card_lt_card h
  have split := sum_powerset_insert (s := U.erase i) (notMem_erase i U)
    (fun A => ((-1 : ℤ) ^ A.card) • (if S ⊆ A then c else 0))
  rw [insert_erase hi] at split
  rw [split, ← sum_add_distrib]
  apply sum_eq_zero
  intro A hA
  have hiA : i ∉ A := notMem_mono (mem_powerset.mp hA) (notMem_erase i U)
  by_cases hSA : S ⊆ A <;>
    simp [card_insert_of_notMem hiA, pow_succ, subset_insert_iff_of_notMem hs, hSA]

/-- Testing a degree-d polynomial against parity times any monomial of degree below
the codimension gives zero. The subset indicators are the square-free monomials. -/
theorem group_alternating_moment (U I : Finset ι) (terms : Finset (Finset ι))
    (coeff : Finset ι → G) (d : ℕ) (degree : ∀ S ∈ terms, S.card ≤ d)
    (room : d + I.card < U.card) :
    ∑ A ∈ U.powerset, ((-1 : ℤ) ^ A.card) •
      (if I ⊆ A then ∑ S ∈ terms, (if S ⊆ A then coeff S else 0) else 0) = 0 := by
  have expand (A : Finset ι) :
      (if I ⊆ A then ∑ S ∈ terms, (if S ⊆ A then coeff S else 0) else 0) =
        ∑ S ∈ terms, (if S ∪ I ⊆ A then coeff S else 0) := by
    by_cases h : I ⊆ A <;> simp [union_subset_iff, h]
  simp_rw [expand, Finset.smul_sum]
  rw [sum_comm]
  apply sum_eq_zero
  intro S hS
  apply alternating_monomial
  exact (card_union_le _ _).trans_lt (lt_of_le_of_lt (Nat.add_le_add_right (degree S hS) _) room)

/-- Real alternating sums in the polynomial notation of the Boolean classification. -/
theorem alternating_moment (U I : Finset ι) (terms : Finset (Finset ι))
    (coeff : Finset ι → ℝ) (d : ℕ) (degree : ∀ S ∈ terms, S.card ≤ d)
    (room : d + I.card < U.card) :
    ∑ A ∈ U.powerset, (-1 : ℝ) ^ A.card *
      (if I ⊆ A then ∑ S ∈ terms, (if S ⊆ A then coeff S else 0) else 0) = 0 := by
  simpa [zsmul_eq_mul] using group_alternating_moment U I terms coeff d degree room

/-- In retained-bit coordinates a degree-d polynomial which vanishes below level d
and has at most one possible nonzero value on that level is constant on one face
and zero elsewhere. This works with coefficients in any abelian group. -/
theorem face_of_one_outer_vertex (U R : Finset ι) (d : ℕ) (hR : R ⊆ U) (rankR : R.card = d)
    (f coeff : Finset ι → G)
    (expansion : ∀ A ⊆ U, f A = ∑ S ∈ A.powerset, coeff S)
    (degree : ∀ A ⊆ U, d < A.card → coeff A = 0)
    (below : ∀ A ⊆ U, A.card < d → f A = 0)
    (outer : ∀ A ⊆ U, A.card = d → A ≠ R → f A = 0) :
    ∀ A ⊆ U, f A = if R ⊆ A then f R else 0 := by
  have small (T : Finset ι) : T ⊆ U → T.card < d → coeff T = 0 := by
    induction T using Finset.strongInductionOn with
    | _ T ih =>
      intro hT hd
      have only : ∑ S ∈ T.powerset, coeff S = coeff T := by
        apply sum_eq_single_of_mem T (mem_powerset_self T)
        intro S hS hne
        have hsub := mem_powerset.mp hS
        have hlt := ssubset_of_subset_of_ne hsub hne
        exact ih S hlt (hsub.trans hT) ((card_lt_card hlt).trans hd)
      rw [← only, ← expansion T hT]
      exact below T hT hd
  have boundary (T : Finset ι) (hT : T ⊆ U) (hd : T.card = d) : f T = coeff T := by
    rw [expansion T hT]
    apply sum_eq_single_of_mem T (mem_powerset_self T)
    intro S hS hne
    have hsub := mem_powerset.mp hS
    apply small S (hsub.trans hT)
    rw [← hd]
    exact card_lt_card (ssubset_of_subset_of_ne hsub hne)
  have away (T : Finset ι) (hT : T ⊆ U) (hne : T ≠ R) : coeff T = 0 := by
    rcases lt_trichotomy T.card d with h | h | h
    · exact small T hT h
    · rw [← boundary T hT h]
      exact outer T hT h hne
    · exact degree T hT h
  intro A hA
  rw [expansion A hA]
  by_cases h : R ⊆ A
  · rw [if_pos h, boundary R hR rankR]
    exact sum_eq_single_of_mem R (mem_powerset.mpr h)
      (fun S hS => away S ((mem_powerset.mp hS).trans hA))
  · rw [if_neg h]
    apply sum_eq_zero
    intro S hS
    have sub := mem_powerset.mp hS
    exact away S (sub.trans hA) (fun he => h (he ▸ sub))

end ProofGraph.JohnsonMatchingCubes
