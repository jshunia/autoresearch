import FiniteEntropyEPnI

open OAI OAI.EntropyPhotonNumber OAI.QuantumTrace ProofAtlas.PhotonNumber Filter Topology

namespace ProofGraph.PhotonEntropy

noncomputable section

private theorem finiteEntropy_of_damped_bound {n : ℕ} (ρ : State n) (M : ℝ)
    (hM : ∀ᶠ m in atTop, entropy (damped (parameter m) ρ) ≤ M) : FiniteEntropy ρ := by
  let b := numberBasis n
  have ht := entropyOperator_tendsto (fun m => (damped (parameter m) ρ).positive) ρ.positive
    (fun m => norm_le_trace b (damped (parameter m) ρ).positive (trace_one_numberBasis _))
    (norm_le_trace b ρ.positive (trace_one_numberBasis _)) (damped_tendsto ρ)
  have hdiag (k : NumberIndex n) : Continuous (fun T : Fock n →L[ℂ] Fock n => (inner ℂ (b k) (T (b k))).re) := by fun_prop
  have hp (σ : State n) := entropyOperator_positive σ.positive (norm_le_trace b σ.positive (trace_one_numberBasis _))
  have hs : Summable (fun k => (inner ℂ (b k) (entropyOperator ρ.op (b k))).re) := by
    apply summable_of_sum_le (c := M) (fun k => (hp ρ).re_inner_nonneg_right _)
    intro F
    apply le_of_tendsto (tendsto_finsetSum F (fun k _ => ((hdiag k).tendsto _).comp ht))
    filter_upwards [hM] with m hm
    let S := damped (parameter m) ρ
    have he := entropy_hasSum S (damped_finiteEnergy _ _)
    exact ((he.summable.sum_le_tsum F (fun k _ => (hp S).re_inner_nonneg_right _)).trans_eq he.tsum_eq).trans hm
  simpa only [b, entropyOperator_eq_complex ρ.positive.isSymmetric, numberBasis_apply, entry, FiniteEntropy] using hs

private theorem input_entropy_bound {n : ℕ} (hn : 0 < (n : ℝ)) {s M t : ℝ}
    (hs : 0 ≤ s) (hM : 0 ≤ M) (ht : 0 < t) (h : t * gInv (s/n) ≤ gInv (M/n)) :
    s ≤ n * g (gInv (M/n)/t) := by
  have hs' := div_nonneg hs hn.le
  have hm' := div_nonneg hM hn.le
  have hle := (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using h)
  have hh := strictMonoOn_g.monotoneOn (gInv_nonneg hs') (div_nonneg (gInv_nonneg hm') ht.le) hle
  rw [g_gInv hs'] at hh
  simpa only [mul_comm] using (div_le_iff₀ hn).mp hh

/-- A genuinely mixed port cannot hide an infinite input entropy. The other input may
be arbitrary. No finite entropy or energy assumption is imposed on either input. -/
theorem finite_inputs_of_finite_output {n : ℕ} (hn : 1 ≤ n) (A B C : State n)
    (η : ℝ) (hη : η ∈ Set.Ioo 0 1) (hC : IsBeamSplitterOutput η A B C) (hSC : FiniteEntropy C) :
    FiniteEntropy A ∧ FiniteEntropy B := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hclosed : η ∈ Set.Icc 0 1 := ⟨hη.1.le, hη.2.le⟩
  let M := 2 * (1 + entropy C)
  have hM : 0 ≤ M := by dsimp [M]; linarith [entropy_nonneg C]
  let q (m : ℕ) := mass (parameter m) A * mass (parameter m) B
  have hq : Tendsto q atTop (𝓝 1) := by simpa [q] using (mass_tendsto A).mul (mass_tendsto B)
  have hhalf := hq.eventually (eventually_gt_nhds (show (1/2 : ℝ) < 1 by norm_num))
  have bounds : ∀ᶠ m in atTop,
      entropy (damped (parameter m) A) ≤ n * g (gInv (M/n)/η) ∧
      entropy (damped (parameter m) B) ≤ n * g (gInv (M/n)/(1-η)) := by
    filter_upwards [hhalf] with m hm
    let a := damped (parameter m) A
    let b := damped (parameter m) B
    let c := beamOutput η hclosed a b
    have hu : q m * (1 + entropy c) ≤ 1 + entropy C := entropy_output_upper _ η hclosed A B C hC hSC
    have hcm : entropy c ≤ M := by dsimp [M]; nlinarith [entropy_nonneg c, mul_nonneg (sub_nonneg.mpr hm.le) (entropy_nonneg c)]
    have hinv : gInv (entropy c / n) ≤ gInv (M / n) :=
      (le_gInv_iff (gInv_nonneg (div_nonneg (entropy_nonneg c) hnR.le)) (div_nonneg hM hnR.le)).mpr
        (by rw [g_gInv (div_nonneg (entropy_nonneg c) hnR.le)]; exact div_le_div_of_nonneg_right hcm hnR.le)
    have hfinite := (entropy_photon_number_inequality n hn a b c (damped_finiteEnergy _ _)
      (damped_finiteEnergy _ _) η hclosed (beamOutput_spec _ _ _ _)).trans hinv
    have hta := mul_nonneg hη.1.le (gInv_nonneg (div_nonneg (entropy_nonneg a) hnR.le))
    have htb := mul_nonneg (sub_nonneg.mpr hη.2.le) (gInv_nonneg (div_nonneg (entropy_nonneg b) hnR.le))
    exact ⟨input_entropy_bound hnR (entropy_nonneg a) hM hη.1 (by linarith),
      input_entropy_bound hnR (entropy_nonneg b) hM (sub_pos.mpr hη.2) (by linarith)⟩
  exact ⟨finiteEntropy_of_damped_bound A _ (bounds.mono (fun _ => And.left)),
    finiteEntropy_of_damped_bound B _ (bounds.mono (fun _ => And.right))⟩

/-- Among arbitrary finite-entropy inputs with the entropy of a positive-temperature thermal
state, a thermal input attains the minimum output entropy of a thermal attenuator.
The input may have infinite mean energy and correlations across modes. -/
theorem thermal_attenuator_minimum {n : ℕ} (hn : 1 ≤ n) (η a b : ℝ)
    (hη : η ∈ Set.Icc 0 1) (ha : 0 < a) (hb : 0 < b) :
    IsLeast {s : ℝ | ∃ A C : State n, FiniteEntropy A ∧ entropy A = n * g a ∧
      IsBeamSplitterOutput η A (thermalState n b hb) C ∧ FiniteEntropy C ∧ entropy C = s}
      ((n : ℝ) * g (η*a + (1-η)*b)) := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hc : 0 < η*a+(1-η)*b := by
    by_cases he : η = 0
    · simpa [he] using hb
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne hη.1 (Ne.symm he)) ha)
        (mul_nonneg (sub_nonneg.mpr hη.2) hb.le)
  constructor
  · refine ⟨thermalState n a ha, thermalState n (η*a+(1-η)*b) hc, entropy_summable _ (thermalState_finiteEnergy _ _ _),
      thermalState_entropy _ _ _, ?_, entropy_summable _ (thermalState_finiteEnergy _ _ _), thermalState_entropy _ _ _⟩
    rw [← thermal_beamOutput η a b hη ha hb hc]
    exact beamOutput_spec _ _ _ _
  · rintro s ⟨A,C,hA,heA,hC,hSC,rfl⟩
    have hh := finiteEntropyEPnI n hn A (thermalState n b hb) C η hη hA
      (entropy_summable _ (thermalState_finiteEnergy _ _ _)) hC hSC
    rw [heA, thermalState_entropy, mul_div_cancel_left₀ _ hnR, mul_div_cancel_left₀ _ hnR, gInv_g ha.le, gInv_g hb.le] at hh
    exact hh

end
end ProofGraph.PhotonEntropy
