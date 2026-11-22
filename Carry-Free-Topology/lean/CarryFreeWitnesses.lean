import PrimeCircuitQuestions

/-! Distinct triple sums give a unique orientation to a distance clique.
The binary examples use the original same-width multiplication predicate. -/

namespace ProofGraph.CarryFreeWitnesses

/-- The same unordered triple, allowing repeated entries. -/
def SameTriple {α : Type*} (a b c d e f : α) : Prop :=
  (a = d ∧ b = e ∧ c = f) ∨ (a = d ∧ b = f ∧ c = e) ∨
  (a = e ∧ b = d ∧ c = f) ∨ (a = e ∧ b = f ∧ c = d) ∨
  (a = f ∧ b = d ∧ c = e) ∨ (a = f ∧ b = e ∧ c = d)

def TripleUnique {α : Type*} (mark : α → ℤ) : Prop :=
  ∀ a b c d e f, mark a + mark b + mark c = mark d + mark e + mark f →
    SameTriple a b c d e f

/-- Two non-loop marked differences whose difference is marked share a head or a tail. -/
theorem share_endpoint {α : Type*} {mark : α → ℤ} (unique : TripleUnique mark)
    {h t p q c d : α} (ht : h ≠ t) (pq : p ≠ q)
    (edge : (mark h - mark t) - (mark p - mark q) = mark c - mark d) :
    h = p ∨ t = q := by
  have perm := unique h q d t p c (by linarith)
  unfold SameTriple at perm
  rcases perm with x | x | x | x | x | x <;> grind

/-- Pairwise agreement on a head or a tail forces agreement on one coordinate throughout. -/
theorem common_coordinate {V α : Type*} (base : V) (head tail : V → α)
    (pair : ∀ i j, head i = head j ∨ tail i = tail j) :
    (∀ i, head i = head base) ∨ (∀ i, tail i = tail base) := by
  classical
  by_cases allHeads : ∀ i, head i = head base
  · exact Or.inl allHeads
  · push Not at allHeads
    obtain ⟨j, hj⟩ := allHeads
    have tj := (pair j base).resolve_left hj
    right
    intro i
    rcases pair i base with hi | hi
    · have different : head i ≠ head j := fun eq => hj (eq.symm.trans hi)
      exact ((pair i j).resolve_left different).trans tj
    · exact hi

/-- A family of compatible positive offsets from one physical site uses one
translation or one reflection of the labels. The index type represents the other sites. -/
theorem distance_clique_chart {V α : Type*} (base : V) {mark : α → ℤ}
    (unique : TripleUnique mark) (head tail : V → α) (nonloop : ∀ i, head i ≠ tail i)
    (site : V → ℤ) (origin : ℤ)
    (offset : ∀ i, site i - origin = mark (head i) - mark (tail i))
    (edge : ∀ i j, i ≠ j → ∃ c d, site i - site j = mark c - mark d) :
    (∃ shift, ∀ i, site i = shift + mark (head i)) ∨
    (∃ shift, ∀ i, site i = shift - mark (tail i)) := by
  have pair (i j : V) : head i = head j ∨ tail i = tail j := by
    by_cases eq : i = j
    · exact Or.inl (congrArg head eq)
    · obtain ⟨c, d, e⟩ := edge i j eq
      exact share_endpoint unique (nonloop i) (nonloop j) (c := c) (d := d)
        (by linarith [offset i, offset j])
  rcases common_coordinate base head tail pair with heads | tails
  · right
    refine ⟨origin + mark (head base), fun i => ?_⟩
    have h := offset i
    rw [heads i] at h
    linarith
  · left
    refine ⟨origin - mark (tail base), fun i => ?_⟩
    have h := offset i
    rw [tails i] at h
    linarith

/-- Distinct offsets exclude an ambiguity between the two coordinates. -/
theorem unique_handedness {V α : Type*} {mark : α → ℤ} (head tail : V → α) (i j : V)
    (distinct : mark (head i) - mark (tail i) ≠ mark (head j) - mark (tail j)) :
    ¬ (head i = head j ∧ tail i = tail j) := by
  rintro ⟨h, t⟩
  exact distinct (by rw [h, t])

/-- A common top bit and a forced second bit orient two packed words. -/
theorem nearer_second_bit_wins (forward reflected top marker : ℕ) (below : marker < top)
    (ft : forward.testBit top = true) (rt : reflected.testBit top = true)
    (gap : ∀ j, marker ≤ j → j ≠ top → forward.testBit j = false)
    (bit : reflected.testBit marker = true)
    (clear : ∀ j, marker < j → j ≠ top → reflected.testBit j = false) :
    forward < reflected := by
  apply Nat.lt_of_testBit marker (gap marker le_rfl (Nat.ne_of_lt below)) bit
  intro j hj
  by_cases h : j = top
  · simp [h, ft, rt]
  · rw [gap j hj.le h, clear j hj h]

/-- The small-clique remainder can be discarded by a single integer division. -/
theorem count_quotient (solutions fiber rest : ℕ) (positive : 0 < fiber) (small : rest < fiber) :
    (solutions * fiber + rest) / fiber = solutions := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ positive, Nat.div_eq_of_lt small, Nat.zero_add]

/-- Two separated pairs of bands, with a lower and an upper peg for each index. -/
def peg (width i : ℕ) (high second : Bool) : ℕ :=
  (if high then 80 * width else 35 * width) + (if second then 4 * width + 2 * i else i)

/-- A designated gap occurs only between the two pegs of its own index, even
when the other candidate endpoints can come from either band. -/
theorem protected_gap {A : Set ℕ} (free : ThreeAPFree A) (zone : ℕ → Bool)
    {width x y i : ℕ} (hx : x ∈ A) (hy : y ∈ A) (hi : i ∈ A)
    (bx : x < width) (by' : y < width) (bi : i < width) (sx sy : Bool)
    (gap : peg width y (zone y) sy = peg width x (zone x) sx + (4 * width + i)) :
    x = i ∧ y = i ∧ sx = false ∧ sy = true := by
  have geom : sx = false ∧ sy = true ∧ x + i = y + y := by
    cases sx <;> cases sy <;> cases zx : zone x <;> cases zy : zone y <;>
      simp_all [peg] <;> omega
  have eq := free hx hy hi geom.2.2
  exact ⟨by omega, by omega, geom.1, geom.2.1⟩

/-- Translating a pair with its own protected gap leaves a hole set at one end.
This also applies in the cyclic group of residues of the stride. -/
theorem protected_translate {G : Type*} [AddCommGroup G] (holes : Set G) (lo hi s : G)
    (hs : s ≠ 0)
    (unique : ∀ x ∈ holes, ∀ y ∈ holes, y - x = hi - lo → x = lo) :
    lo - s ∉ holes ∨ hi - s ∉ holes := by
  classical
  by_cases hx : lo - s ∈ holes
  · right
    intro hy
    have eq := unique _ hx _ hy (by abel)
    apply hs
    calc
      s = lo - (lo - s) := by abel
      _ = 0 := by rw [eq, sub_self]
  · exact Or.inl hx

/-- A translate of a whole pattern cannot hide among separated equal-size
patterns with distinct shapes. Coordinates are relative to each pattern's first site. -/
theorem isolated_template {I : Type*} (shape : I → Finset ℤ) (start : I → ℤ) (width : ℤ)
    (zero : ∀ i, 0 ∈ shape i) (bounded : ∀ i x, x ∈ shape i → 0 ≤ x ∧ x ≤ width)
    (cards : ∀ i j, (shape i).card = (shape j).card) (tags : Function.Injective shape)
    (apart : ∀ i j, i ≠ j → start i + 2 * width < start j ∨ start j + 2 * width < start i)
    (i : I) (s : ℤ) (hidden : ∀ x ∈ shape i, ∃ j, start i + x - s - start j ∈ shape j) :
    s = 0 := by
  classical
  obtain ⟨j, hj⟩ := hidden 0 (zero i)
  have atZero := bounded j _ hj
  let move := fun x : ℤ => start i + x - s - start j
  have sub : (shape i).image move ⊆ shape j := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k, hk⟩ := hidden u hu
    by_cases eq : k = j
    · subst k
      exact hk
    · have ub := bounded i _ hu
      have kb := bounded k _ hk
      rcases apart k j eq with h | h <;> omega
  have inj : Function.Injective move := by
    intro a b eq
    dsimp [move] at eq
    omega
  have onto : (shape i).image move = shape j :=
    Finset.eq_of_subset_of_card_le sub (by rw [Finset.card_image_of_injective _ inj, cards i j])
  have memZero : 0 ∈ (shape i).image move := onto ▸ zero j
  obtain ⟨x, hx, eq⟩ := Finset.mem_image.mp memZero
  have nonneg := (bounded i _ hx).1
  dsimp [move] at eq
  have fixed (x : ℤ) : move x = x := by dsimp [move]; omega
  have ident : move = id := funext fixed
  have same : shape i = shape j := by simpa [ident] using onto
  have ij := tags same
  subst j
  omega

open PrimeCircuitQuestions

def partnerCount (a : ℕ) : ℕ := (feasibleWords a).length

/-- The prescribed difference list controls the multiplier's entire own width. -/
def Realizes (n a stride : ℕ) (forbidden : Finset ℕ) : Prop :=
  a % 2 = 1 ∧ 2 ≤ stride ∧ stride * n < a.size ∧ a.size ≤ stride * (n + 1) ∧
    ∀ k : Fin a.size, 0 < k.val →
      ((a &&& (a >>> k.val)) ≠ 0 ↔ ¬stride ∣ k.val ∨ k.val / stride ∈ forbidden)

/-- The remaining logarithmic factor in the uniform width bound. -/
def QuadraticDistanceWidth : Prop :=
  ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ, 0 < n → ∀ forbidden : Finset ℕ, forbidden ⊆ Finset.Icc 1 n →
    ∃ a stride : ℕ, Realizes n a stride forbidden ∧ a.size ≤ c * n ^ 2

theorem nineteen_realizes_two : Realizes 2 19 2 {2} := by
  unfold Realizes
  decide

set_option maxRecDepth 16000 in
theorem nineteen_partners_of_seventy :
    partnerCount 70 = 19 ∧ greatestOptimum 70 = 73 ∧ maximumWeight 70 = 3 := by decide

theorem count_at_seven_and_nineteen : partnerCount 7 = 4 ∧ partnerCount 19 = 9 := by decide

end ProofGraph.CarryFreeWitnesses
