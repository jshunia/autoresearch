import CarryFreeWitnesses

namespace ProofGraph.CarryFreeTopology

open CarryFreeWitnesses

/-- A graph difference between two sites, with both orientations available. -/
def MarkedEdge {α : Type*} (mark : α → ℤ) (edge : α → α → Prop) (x y : ℤ) : Prop :=
  ∃ i j, edge i j ∧ x - y = mark i - mark j

theorem unique_difference {α : Type*} {mark : α → ℤ} (unique : TripleUnique mark)
    {h t p q : α} (ht : h ≠ t) (eq : mark h - mark t = mark p - mark q) :
    h = p ∧ t = q := by
  have perm := unique h q h p t h (by linarith)
  unfold SameTriple at perm
  rcases perm with x | x | x | x | x | x <;> grind

/-- In the link of the base site two different arcs are compatible exactly
inside a common incoming or outgoing chart, with the remaining labels adjacent. -/
theorem link_adjacency {α : Type*} {mark : α → ℤ} (unique : TripleUnique mark)
    {edge : α → α → Prop} (symm : Symmetric edge) {h t p q : α}
    (ht : h ≠ t) (pq : p ≠ q) (ne : mark h - mark t ≠ mark p - mark q) :
    MarkedEdge mark edge (mark h - mark t) (mark p - mark q) ↔
      (h = p ∧ edge t q) ∨ (t = q ∧ edge h p) := by
  constructor
  · rintro ⟨c, d, adj, eq⟩
    rcases share_endpoint unique ht pq eq with hSame | tSame
    · subst p
      have tq : q ≠ t := by rintro rfl; exact ne rfl
      obtain ⟨rfl, rfl⟩ := unique_difference unique tq
        (show mark q - mark t = mark c - mark d by linarith)
      exact Or.inl ⟨rfl, symm adj⟩
    · subst q
      have hp : h ≠ p := by rintro rfl; exact ne rfl
      obtain ⟨rfl, rfl⟩ := unique_difference unique hp
        (show mark h - mark p = mark c - mark d by linarith)
      exact Or.inr ⟨rfl, adj⟩
  · rintro (⟨rfl, e⟩ | ⟨rfl, e⟩)
    · exact ⟨q, t, symm e, by ring⟩
    · exact ⟨h, p, e, by ring⟩

/-- A chart of span at most the physical width cannot lose both endpoints
while still meeting the window. This is where the suspension apices are used. -/
theorem clipped_chart_keeps_apex (start span window point : ℤ)
    (fits : span ≤ window) (left : 0 ≤ point) (right : point ≤ span)
    (lo : 0 ≤ start + point) (hi : start + point ≤ window) :
    (0 ≤ start ∧ start ≤ window) ∨
      (0 ≤ start + span ∧ start + span ≤ window) := by omega

theorem two_pins_exclude_reflection (first other stride : ℕ)
    (ordered : first < other) (positive : 0 < stride) :
    (stride : ℤ) * ((first : ℤ) - (other : ℤ)) < 0 := by
  exact mul_neg_of_pos_of_neg (by exact_mod_cast positive) (by omega)

/-- A face that misses a whole four-cycle loses two possible vertices. -/
theorem distinct_top_charts_miss_a_ridge (groups used faceSize : ℕ)
    (miss : used < groups) (bound : faceSize ≤ 2 * used) :
    faceSize + 2 ≤ 2 * groups := by omega

/-- Opposite charts interchange the two labels on an edge. Their barycentric
coordinate maps agree in the coordinate torus, along the entire closed edge. -/
theorem reflected_edge_glues (x y : ℝ) (bary : x + y = 1) :
    ((x : AddCircle (1 : ℝ)), (y : AddCircle (1 : ℝ))) =
      (((-y : ℝ) : AddCircle (1 : ℝ)), ((-x : ℝ) : AddCircle (1 : ℝ))) := by
  have sum : (x : AddCircle (1 : ℝ)) + (y : AddCircle (1 : ℝ)) = 0 := by
    rw [← AddCircle.coe_add, bary, AddCircle.coe_period]
  apply Prod.ext
  · change (x : AddCircle (1 : ℝ)) = -(y : AddCircle (1 : ℝ))
    exact eq_neg_of_add_eq_zero_left sum
  · change (y : AddCircle (1 : ℝ)) = -(x : AddCircle (1 : ℝ))
    exact eq_neg_of_add_eq_zero_left ((add_comm _ _).trans sum)

/-- A chart that retracts upstairs reflects based relative homotopies
downstairs. Paths and based spheres are instances of the domain. -/
theorem covering_retract_reflects {A K E X : Type*} [TopologicalSpace A]
    [PreconnectedSpace A] [TopologicalSpace K] [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (cover : IsCoveringMap p) (i : C(K, E)) (r : C(E, K))
    (leftInv : r.comp i = ContinuousMap.id K) {f g : C(A, K)} {s : Set A}
    (pin : ∃ a ∈ s, f a = g a)
    (h : ((⟨p, cover.continuous⟩ : C(E, X)).comp (i.comp f)).HomotopicRel
      ((⟨p, cover.continuous⟩ : C(E, X)).comp (i.comp g)) s) : f.HomotopicRel g s := by
  obtain ⟨a, ha, eq⟩ := pin
  have up := (cover.homotopicRel_iff_comp (f₀ := i.comp f) (f₁ := i.comp g)
    ⟨a, ha, congrArg i eq⟩).mpr h
  have back := up.comp_continuousMap r
  simpa only [← ContinuousMap.comp_assoc, leftInv, ContinuousMap.id_comp] using back

/-- A support avoids every conflicting pair, with conflicts supplied by
a symmetric irreflexive graph in the applications. -/
def Packing {V : Type*} (conflict : V → V → Prop) (bits : V → Bool) : Prop :=
  ∀ x y, bits x = true → bits y = true → ¬ conflict x y

def FiberConflict {I V : Type*} (r : V → V → Prop) (x y : I × V) : Prop :=
  x.1 = y.1 ∧ r x.2 y.2

theorem fiber_packing {I V : Type*} (r : V → V → Prop) (f : I × V → Bool) :
    Packing (FiberConflict r) f ↔ ∀ i, Packing r (fun v => f (i, v)) := by
  constructor
  · intro h i v w hv hw e
    exact h (i, v) (i, w) hv hw ⟨rfl, e⟩
  · rintro h ⟨i, v⟩ ⟨j, w⟩ hv hw ⟨eq, e⟩
    change i = j at eq
    subst j
    exact h i v w hv hw e

def fiberPackingEquiv (I V : Type*) (r : V → V → Prop) :
    {f : I × V → Bool // Packing (FiberConflict r) f} ≃
    (I → {s : V → Bool // Packing r s}) where
  toFun f i := ⟨fun v => f.val (i, v), (fiber_packing r f.val).mp f.property i⟩
  invFun f := ⟨fun x => (f x.1).val x.2, (fiber_packing r _).mpr (fun i => (f i).property)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem fiber_count (I V : Type*) [Finite I] (r : V → V → Prop) :
    Nat.card {f : I × V → Bool // Packing (FiberConflict r) f} =
    Nat.card {s : V → Bool // Packing r s} ^ Nat.card I := by
  rw [Nat.card_congr (fiberPackingEquiv I V r), Nat.card_fun]

/-- The scalar comparison in the quadratic-field relative difference construction. -/
theorem ratio_labels {F : Type*} [Field F] (a b c d : F) (distinct : a ≠ b)
    (lin : a + d = c + b) (quad : a * d = c * b) : a = c ∧ b = d := by
  have prod : (a - c) * (a - b) = 0 := by linear_combination a * lin - quad
  rcases mul_eq_zero.mp prod with ac | ab
  · have eq := sub_eq_zero.mp ac
    exact ⟨eq, by linear_combination -lin + (sub_eq_zero.mpr eq)⟩
  · exact (distinct (sub_eq_zero.mp ab)).elim

open PrimeCircuitQuestions

def permittedNeighbors (a : ℕ) : List ℕ := (List.range a.size).filter fun i =>
  decide (0 < i ∧ CarryFree a (1 + 2^i))

def permittedPairs (a : ℕ) : List (ℕ × ℕ) :=
  (permittedNeighbors a).flatMap fun i =>
    ((permittedNeighbors a).filter fun j =>
      decide (i < j ∧ CarryFree a (1 + 2^i + 2^j))).map fun j => (i, j)

set_option maxRecDepth 16000 in
theorem square_link_at_seventy_three :
    permittedNeighbors 73 = [1,2,4,5] ∧
    permittedPairs 73 = [(1,2),(1,5),(2,4),(4,5)] := by decide

theorem dilation_of_three :
    partnerCount 3 = 3 ∧ partnerCount 5 = 6 ∧ partnerCount 10 = 9 := by decide

end ProofGraph.CarryFreeTopology
