import PhotonUpper
import PhotonLimit

open OAI OAI.EntropyPhotonNumber ProofAtlas.PhotonNumber Filter Topology
open scoped NNReal

namespace ProofGraph.PhotonEntropy

noncomputable section

theorem entropy_damped_tendsto {n : ℕ} (ρ : State n) (hρ : FiniteEntropy ρ) :
    Tendsto (fun m => entropy (damped (parameter m) ρ)) atTop (𝓝 (entropy ρ)) := by
  apply tendsto_order.mpr
  refine ⟨(fun _ hy => entropy_eventually_gt ρ hρ hy), ?_⟩
  intro z hz
  have ht : Tendsto (fun m => (1 + entropy ρ) / mass (parameter m) ρ - 1) atTop (𝓝 (entropy ρ)) := by
    simpa using ((tendsto_const_nhds (x := (1 + entropy ρ))).div (mass_tendsto ρ) one_ne_zero).sub_const 1
  filter_upwards [ht.eventually (eventually_lt_nhds hz)] with m hm
  have hh := entropy_damped_upper (parameter m) ρ hρ
  have h := (le_div_iff₀ (mass_pos (parameter m) ρ)).mpr (by simpa only [mul_comm] using hh)
  linarith

/-- The inverse thermal entropy function is continuous on its nonnegative physical domain. -/
private def thermalOrderIso : ℝ≥0 ≃o ℝ≥0 where
  toFun x := ⟨g x, g_nonneg x.2⟩
  invFun y := ⟨gInv y, gInv_nonneg y.2⟩
  left_inv x := Subtype.ext (gInv_g x.2)
  right_inv y := Subtype.ext (g_gInv y.2)
  map_rel_iff' := by
    intro x y
    exact strictMonoOn_g.le_iff_le x.2 y.2

private theorem inv_tendsto {x : ℕ → ℝ} {s : ℝ} (hs : 0 ≤ s) (hx : ∀ m, 0 ≤ x m)
    (h : Tendsto x atTop (𝓝 s)) : Tendsto (fun m => gInv (x m)) atTop (𝓝 (gInv s)) := by
  have hsub : Tendsto (fun m => (⟨x m, hx m⟩ : ℝ≥0)) atTop (𝓝 ⟨s,hs⟩) :=
    tendsto_subtype_rng.mpr h
  exact (continuous_subtype_val.tendsto _).comp ((thermalOrderIso.symm.continuous.tendsto _).comp hsub)

/-- The source-matched finite-entropy form of the multimode entropy photon-number
inequality. The finite-energy inequality used inside the limit is the published proof. -/
theorem finiteEntropyEPnI : ProofAtlas.PhotonNumber.EntropyPhotonNumberInequality := by
  intro n hn A B C η hη hA hB hC hSC
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  let F (a b : ℝ) := (n : ℝ) * g (η * gInv (a/n) + (1-η) * gInv (b/n))
  let q (m : ℕ) := mass (parameter m) A * mass (parameter m) B
  let a (m : ℕ) := damped (parameter m) A
  let b (m : ℕ) := damped (parameter m) B
  have bound (m : ℕ) : q m * (1 + F (entropy (a m)) (entropy (b m))) ≤ 1 + entropy C := by
    let c := beamOutput η hη (a m) (b m)
    have hfinite := entropy_photon_number_inequality n hn (a m) (b m) c
      (damped_finiteEnergy _ _) (damped_finiteEnergy _ _) η hη (beamOutput_spec _ _ _ _)
    have hmix : 0 ≤ η * gInv (entropy (a m)/n) + (1-η) * gInv (entropy (b m)/n) :=
      add_nonneg (mul_nonneg hη.1 (gInv_nonneg (div_nonneg (entropy_nonneg _) hnR.le)))
        (mul_nonneg (sub_nonneg.mpr hη.2) (gInv_nonneg (div_nonneg (entropy_nonneg _) hnR.le)))
    have hbase : F (entropy (a m)) (entropy (b m)) ≤ entropy c := by
      have hh := (le_gInv_iff hmix (div_nonneg (entropy_nonneg c) hnR.le)).mp hfinite
      simpa only [F, mul_comm] using (le_div_iff₀ hnR).mp hh
    exact (mul_le_mul_of_nonneg_left (add_le_add_right hbase 1)
      (mul_nonneg (mass_pos _ _).le (mass_pos _ _).le)).trans (entropy_output_upper _ η hη A B C hC hSC)
  have hIA := inv_tendsto (div_nonneg (entropy_nonneg A) hnR.le)
    (fun m => div_nonneg (entropy_nonneg (a m)) hnR.le) ((entropy_damped_tendsto A hA).div_const (n:ℝ))
  have hIB := inv_tendsto (div_nonneg (entropy_nonneg B) hnR.le)
    (fun m => div_nonneg (entropy_nonneg (b m)) hnR.le) ((entropy_damped_tendsto B hB).div_const (n:ℝ))
  have hF : Tendsto (fun m => F (entropy (a m)) (entropy (b m))) atTop (𝓝 (F (entropy A) (entropy B))) :=
    ((continuous_g.tendsto _).comp ((hIA.const_mul η).add (hIB.const_mul (1-η)))).const_mul (n : ℝ)
  have hq : Tendsto q atTop (𝓝 1) := by simpa [q] using (mass_tendsto A).mul (mass_tendsto B)
  have hh := le_of_tendsto (hq.mul (hF.const_add 1)) (Eventually.of_forall bound)
  change F (entropy A) (entropy B) ≤ entropy C
  linarith

end
end ProofGraph.PhotonEntropy
