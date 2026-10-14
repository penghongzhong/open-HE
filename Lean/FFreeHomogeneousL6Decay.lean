import FFreeSchwartzL6Decay

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.FreeTimeDecay
open EnergySpace SobolevStretch StationarySelfTest ActualStrichartz

/-- Dense-Schwartz extension, with the actual uniform free bound controlling the error. -/
theorem freeEnergyState_value_norm_decay_of_schwartz (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {l : Filter ℝ}
    (hdecay : ∀ phi : Test,
      Tendsto (fun t : ℝ => ‖energyValue (freeEnergyState hDensity hSob t (schwartzEnergyState phi))‖)
        l (𝓝 0)) (u : EnergyState) :
    Tendsto (fun t : ℝ => ‖energyValue (freeEnergyState hDensity hSob t u)‖) l (𝓝 0) := by
  let D := max (K^((6:ℝ)⁻¹)) 1*Real.sqrt 3
  obtain ⟨phi,hphi⟩ := schwartzEnergyState_approximation hDensity hSob u
  have herr : Tendsto (fun n => D*‖u-schwartzEnergyState (phi n)‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, mul_zero] using ((tendsto_const_nhds (x:=u)).sub hphi).norm.const_mul D
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun t => ha.trans_le (norm_nonneg _))
  · intro eps heps
    obtain ⟨n,hn⟩ := (herr.eventually (gt_mem_nhds (half_pos heps))).exists
    filter_upwards [(hdecay (phi n)).eventually (gt_mem_nhds (half_pos heps))] with t ht
    have hb : ‖energyValue (freeEnergyState hDensity hSob t u)-
        energyValue (freeEnergyState hDensity hSob t (schwartzEnergyState (phi n)))‖ ≤
        D*‖u-schwartzEnergyState (phi n)‖ := by
      rw [← map_sub, ← freeEnergyState_sub]
      exact (energyState_value_norm_le _).trans (freeEnergyState_norm_bound hDensity hSob t _)
    have htri := norm_le_norm_sub_add (energyValue (freeEnergyState hDensity hSob t u))
      (energyValue (freeEnergyState hDensity hSob t (schwartzEnergyState (phi n))))
    linarith

/-- The actual homogeneous free orbit decays in L6 at positive infinity.
No scalar-value L2 premise is imposed on u. -/
theorem freeEnergyState_value_norm_tendsto_zero_atTop (hDensity : OrdinaryH1Density)
    {K C : ℝ} (hSob : OrdinarySobolev K) (hS : OrdinaryHomogeneousStrichartz C) (u : EnergyState) :
    Tendsto (fun t : ℝ => ‖energyValue (freeEnergyState hDensity hSob t u)‖) atTop (𝓝 0) :=
  freeEnergyState_value_norm_decay_of_schwartz hDensity hSob
    (fun phi => (freeEnergyState_schwartz_value_norm_decay hDensity hSob hS phi).1) u

/-- The negative-time tail is proved with the same original homogeneous hypotheses. -/
theorem freeEnergyState_value_norm_tendsto_zero_atBot (hDensity : OrdinaryH1Density)
    {K C : ℝ} (hSob : OrdinarySobolev K) (hS : OrdinaryHomogeneousStrichartz C) (u : EnergyState) :
    Tendsto (fun t : ℝ => ‖energyValue (freeEnergyState hDensity hSob t u)‖) atBot (𝓝 0) :=
  freeEnergyState_value_norm_decay_of_schwartz hDensity hSob
    (fun phi => (freeEnergyState_schwartz_value_norm_decay hDensity hSob hS phi).2) u

#print axioms freeEnergyState_value_norm_decay_of_schwartz
#print axioms freeEnergyState_value_norm_tendsto_zero_atTop
#print axioms freeEnergyState_value_norm_tendsto_zero_atBot
end HartreeF.FreeTimeDecay
