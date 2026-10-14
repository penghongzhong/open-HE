import FEnergyFreeConsumers

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped Topology ENNReal
namespace HartreeF.FreeTimeDecay
open EnergySpace SobolevStretch StationarySelfTest

/-- Uniform continuity follows from the actual free group and its uniform
homogeneous graph bound, without a scalar-value L2 domain. -/
theorem freeEnergyState_uniformContinuous (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) (u : EnergyState) :
    UniformContinuous (fun t : ℝ => freeEnergyState hDensity hSob t u) := by
  let C := max (K^((6:ℝ)⁻¹)) 1*Real.sqrt 3
  have hC : 0≤C := mul_nonneg (le_trans (by norm_num) (le_max_right _ _)) (Real.sqrt_nonneg _)
  apply Metric.uniformContinuous_iff.mpr
  intro eps heps
  have hc := (freeEnergyState_time_continuous hDensity hSob u).continuousAt (x:=0)
  obtain ⟨delta,hdelta,hd⟩ := Metric.continuousAt_iff.mp hc (eps/(C+1)) (div_pos heps (by linarith))
  refine ⟨delta,hdelta,?_⟩
  intro s t hst
  have hh : dist (s-t) 0<delta := by simpa only [Real.dist_eq, sub_zero] using hst
  have hs := hd hh
  rw [freeEnergyState_zero_time, dist_eq_norm] at hs
  have hid : freeEnergyState hDensity hSob s u-freeEnergyState hDensity hSob t u =
      freeEnergyState hDensity hSob t (freeEnergyState hDensity hSob (s-t) u-u) := by
    rw [freeEnergyState_sub, ← freeEnergyState_add_time]
    congr 2
    ring
  rw [dist_eq_norm, hid]
  have hb := freeEnergyState_norm_bound hDensity hSob t (freeEnergyState hDensity hSob (s-t) u-u)
  have hn : 0≤‖freeEnergyState hDensity hSob (s-t) u-u‖ := norm_nonneg _
  have he : (C+1)*‖freeEnergyState hDensity hSob (s-t) u-u‖<eps := by
    simpa only [mul_comm] using (lt_div_iff₀ (by linarith : 0<C+1)).mp hs
  change _ ≤ C*‖freeEnergyState hDensity hSob (s-t) u-u‖ at hb
  linarith

/-- Uniform continuity of the actual L6 norm along every homogeneous free orbit. -/
theorem freeEnergyState_value_norm_uniformContinuous (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) (u : EnergyState) :
    UniformContinuous (fun t : ℝ => ‖energyValue (freeEnergyState hDensity hSob t u)‖) :=
  uniformContinuous_norm.comp (energyValue.uniformContinuous.comp
    (freeEnergyState_uniformContinuous hDensity hSob u))

#print axioms freeEnergyState_uniformContinuous
#print axioms freeEnergyState_value_norm_uniformContinuous
end HartreeF.FreeTimeDecay
