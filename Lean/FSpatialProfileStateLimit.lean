import FGivenBadSequenceConcentration
import FSharpWStateTopology

/-! The finite normalized free time is retained in the limiting datum.
Only the spatial affine map is a graph isometry. UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory Filter
open scoped Topology
namespace HartreeF.SpatialProfileLimit
open EnergySpace SobolevStretch StationarySelfTest CriticalAffine StateEnergy
  StateSharpThreshold DynamicSharpW ForcingDomain HeatRiesz
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace

/-- Exact norm transport by the actual spatial linear isometric equivalence. -/
theorem spatial_inverse_error_norm {a : ℝ} (ha : 0 < a) (y : Space)
    (u v : EnergyState) :
    ‖(criticalAffineState a ha y).symm u-v‖ =
      ‖u-criticalAffineState a ha y v‖ := by
  let A := criticalAffineState a ha y
  calc
    ‖A.symm u-v‖ = ‖A (A.symm u-v)‖ := (A.norm_map _).symm
    _ = ‖u-A v‖ := by rw [map_sub, A.apply_symm_apply]

/-- A varying free time converging to s* is absorbed into the limit datum,
not set to zero. The original data and each spatial frame retain their index. -/
theorem spatial_limit_of_finite_time (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (u : ℕ → EnergyState) (lambda : ℕ → ℝ)
    (hlambda : ∀ n, 0 < lambda n) (y : ℕ → Space) (s : ℕ → ℝ)
    (phi : EnergyState) {sstar : ℝ}
    (herr : Tendsto (fun n => ‖u n-criticalAffineState (lambda n) (hlambda n) (y n)
      (freeEnergyState hDensity hSob (s n) phi)‖) atTop (𝓝 0))
    (hs : Tendsto s atTop (𝓝 sstar)) :
    Tendsto (fun n => (criticalAffineState (lambda n) (hlambda n) (y n)).symm (u n))
      atTop (𝓝 (freeEnergyState hDensity hSob sstar phi)) := by
  have he : Tendsto (fun n =>
      (criticalAffineState (lambda n) (hlambda n) (y n)).symm (u n) -
        freeEnergyState hDensity hSob (s n) phi) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [spatial_inverse_error_norm] using herr
  have hf := ((freeEnergyState_time_continuous hDensity hSob phi).tendsto sstar).comp hs
  simpa only [sub_add_cancel, zero_add] using he.add hf

/-- Actual energy and kinetic bounds pass through spatial normalization and
strong convergence. No statement about graph isometry of free flow is used. -/
theorem spatial_limit_energy_kinetic {alpha Ec kappa : ℝ}
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (u : ℕ → EnergyState) (lambda : ℕ → ℝ) (hlambda : ∀ n, 0 < lambda n)
    (y : ℕ → Space) (psi : EnergyState)
    (hE : Tendsto (fun n => totalEnergy alpha (u n)) atTop (𝓝 Ec))
    (hkin : ∀ n, gradientSquared (u n) ≤ kappa*totalEnergy alpha (u n))
    (hz : Tendsto
      (fun n => (criticalAffineState (lambda n) (hlambda n) (y n)).symm (u n))
      atTop (𝓝 psi)) :
    totalEnergy alpha psi = Ec ∧ gradientSquared psi ≤ kappa*Ec := by
  let z (n : ℕ) := (criticalAffineState (lambda n) (hlambda n) (y n)).symm (u n)
  have henergy (n : ℕ) : totalEnergy alpha (z n) = totalEnergy alpha (u n) := by
    have h := criticalAffineState_totalEnergy hOrd (lambda n) (hlambda n) (y n) (z n)
    rw [show criticalAffineState (lambda n) (hlambda n) (y n) (z n) = u n from
      (criticalAffineState (lambda n) (hlambda n) (y n)).apply_symm_apply (u n)] at h
    exact h.symm
  have hgradient (n : ℕ) : gradientSquared (z n) = gradientSquared (u n) := by
    have h := criticalAffineState_gradientSquared (lambda n) (hlambda n) (y n) (z n)
    rw [show criticalAffineState (lambda n) (hlambda n) (y n) (z n) = u n from
      (criticalAffineState (lambda n) (hlambda n) (y n)).apply_symm_apply (u n)] at h
    exact h.symm
  have hEz : Tendsto (fun n => totalEnergy alpha (z n)) atTop (𝓝 Ec) := by
    simpa only [henergy] using hE
  have hEpsi : Tendsto (fun n => totalEnergy alpha (z n)) atTop
      (𝓝 (totalEnergy alpha psi)) := totalEnergy_tendsto hOrd hz
  have hApsi : Tendsto (fun n => gradientSquared (z n)) atTop
      (𝓝 (gradientSquared psi)) := (gradientSquared_continuous.tendsto psi).comp hz
  refine ⟨tendsto_nhds_unique hEpsi hEz, ?_⟩
  apply le_of_tendsto_of_tendsto hApsi (hE.const_mul kappa)
  exact Filter.Eventually.of_forall fun n => by
    simpa only [hgradient] using hkin n

end HartreeF.SpatialProfileLimit
