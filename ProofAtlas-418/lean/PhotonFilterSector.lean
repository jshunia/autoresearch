import ProofAtlasPhotonNumber

open OAI.EntropyPhotonNumber

namespace ProofGraph.PhotonEntropy

/-- The two input occupations in a paired sector have exactly the total number
of its retained and discarded outputs, for every number of modes. -/
theorem split_total {n : ℕ} {k e : NumberIndex n} (a : SectorSplit k e) :
    totalNumber (splitLeft a) + totalNumber (splitRight a) = totalNumber k + totalNumber e := by
  simp only [totalNumber, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have h := (a j).isLt
  simp only [splitLeft, splitRight]
  omega

/-- The two normalizing traces multiply because the input ports are independent.
This equality is for each complex off-diagonal output matrix element and
each discarded occupation. It permits interference within each input block. -/
theorem filtered_outputBlock {n : ℕ} (η : ℝ) (A B A' B' : State n) (r a b : ℂ)
    (hA : ∀ k l, a * entry A'.op k l =
      r ^ totalNumber k * r ^ totalNumber l * entry A.op k l)
    (hB : ∀ k l, b * entry B'.op k l =
      r ^ totalNumber k * r ^ totalNumber l * entry B.op k l)
    (k l e : NumberIndex n) :
    (a*b) * outputBlock η A' B' k l e =
      r ^ totalNumber k * r ^ totalNumber l * (r ^ totalNumber e)^2 * outputBlock η A B k l e := by
  unfold outputBlock
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have hx : r ^ totalNumber (splitLeft x) * r ^ totalNumber (splitRight x) =
      r ^ totalNumber k * r ^ totalNumber e := by
    rw [← pow_add, split_total, pow_add]
  have hy : r ^ totalNumber (splitLeft y) * r ^ totalNumber (splitRight y) =
      r ^ totalNumber l * r ^ totalNumber e := by
    rw [← pow_add, split_total, pow_add]
  calc
    _ = (beamCoefficient η k e (splitLeft x) (splitRight x) : ℂ) *
        (a * entry A'.op (splitLeft x) (splitLeft y)) *
        (b * entry B'.op (splitRight x) (splitRight y)) *
        (beamCoefficient η l e (splitLeft y) (splitRight y) : ℂ) := by ring
    _ = (r ^ totalNumber (splitLeft x) * r ^ totalNumber (splitRight x)) *
        (r ^ totalNumber (splitLeft y) * r ^ totalNumber (splitRight y)) *
        ((beamCoefficient η k e (splitLeft x) (splitRight x) : ℂ) *
        entry A.op (splitLeft x) (splitLeft y) * entry B.op (splitRight x) (splitRight y) *
        (beamCoefficient η l e (splitLeft y) (splitRight y) : ℂ)) := by rw [hA, hB]; ring
    _ = _ := by rw [hx, hy]; ring

end ProofGraph.PhotonEntropy
