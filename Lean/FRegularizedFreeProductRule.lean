import FRegularizedFreeGenerator
import FRegularizedBochnerMild

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped Topology ENNReal
namespace HartreeF.Regularization.Actual
open EnergySpace EnergyRegularizer SobolevStretch StationarySelfTest

/-- The free-group product rule needs the generator domain only at the
single point being differentiated, not along the source derivative. -/
theorem free_product_hasDerivAt_of_J (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (n : ℕ) {w : ℝ → EnergyState} {dw : EnergyState} {t : ℝ}
    (u : EnergyState) (hw : HasDerivAt w dw t) (hval : w t = J hDensity hSob n u) :
    HasDerivAt (fun s => freeEnergyState hDensity hSob s (w s))
      (Complex.I • freeEnergyState hDensity hSob t (deltaJ hDensity hSob n u) +
        freeEnergyState hDensity hSob t dw) t := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have hc := freeEnergyState_continuous_path hDensity hSob
    (fun p : ℝ × EnergyState => p.1) (fun p => p.2) continuous_fst continuous_snd
  have ht : Tendsto (fun h : ℝ => t+h) (𝓝[≠] 0) (𝓝 t) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun h : ℝ => t+h) (𝓝[≠] 0) (𝓝 (t+0)))
  have hv := (hc.tendsto (t,dw)).comp (ht.prodMk_nhds hw.tendsto_slope_zero)
  have hf : Tendsto (fun h : ℝ => h⁻¹ •
      (freeEnergyState hDensity hSob (t+h) (w t) - freeEnergyState hDensity hSob t (w t)))
      (𝓝[≠] 0) (𝓝 (Complex.I • freeEnergyState hDensity hSob t (deltaJ hDensity hSob n u))) := by
    simpa only [hval] using (regularized_free_hasDerivAt hDensity hSob n u t).tendsto_slope_zero
  convert hf.add hv using 1
  funext h
  let A : EnergyState →L[ℝ] EnergyState := (freeEnergyCLM hDensity hSob (t+h)).restrictScalars ℝ
  change h⁻¹ • (A (w (t+h)) - freeEnergyState hDensity hSob t (w t)) =
    h⁻¹ • (A (w t) - freeEnergyState hDensity hSob t (w t)) +
      A (h⁻¹ • (w (t+h)-w t))
  rw [A.map_smul, A.map_sub]
  module

theorem regularized_free_product_hasDerivAt (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (n : ℕ) {w : ℝ → EnergyState} {dw : EnergyState} {t : ℝ}
    (hw : HasDerivAt w dw t) :
    HasDerivAt (fun s => freeEnergyState hDensity hSob s (J hDensity hSob n (w s)))
      (Complex.I • freeEnergyState hDensity hSob t (deltaJ hDensity hSob n (w t)) +
        freeEnergyState hDensity hSob t (J hDensity hSob n dw)) t :=
  free_product_hasDerivAt_of_J hDensity hSob n (w t)
    (((J hDensity hSob n).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hw) rfl

theorem deltaJ_free (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (n : ℕ) (t : ℝ) (u : EnergyState) :
    deltaJ hDensity hSob n (freeEnergyState hDensity hSob t u) =
      freeEnergyState hDensity hSob t (deltaJ hDensity hSob n u) :=
  (laplaceCutoff n).energyCLM_free hDensity hSob t u

theorem deltaJ_J_commute (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (m n : ℕ) (u : EnergyState) :
    deltaJ hDensity hSob m (J hDensity hSob n u) =
      J hDensity hSob m (deltaJ hDensity hSob n u) := by
  apply energyDistribution_injective
  change energyDistribution ((laplaceCutoff m).energyCLM hDensity hSob
    ((cutoff n).energyCLM hDensity hSob u)) =
      energyDistribution ((cutoff m).energyCLM hDensity hSob
        ((laplaceCutoff n).energyCLM hDensity hSob u))
  simp only [BoundedSymbol.energyCLM_distribution, BoundedSymbol.distribution]
  rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
      (cutoff n).temperate (laplaceCutoff m).temperate,
    TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
      (laplaceCutoff n).temperate (cutoff m).temperate]
  congr 2
  funext ξ
  simp only [cutoff, laplaceCutoff, laplaceSymbol, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

#print axioms free_product_hasDerivAt_of_J
#print axioms regularized_free_product_hasDerivAt
#print axioms deltaJ_J_commute
end HartreeF.Regularization.Actual
