import FEnergyRegularizerLaplacian

/-! Explicit ordinary linear-analysis foundations for Bessel convolution.
These are data/hypotheses, not axioms and not an EnergyState/PDE premise.
Aronszajn--Smith, AIF 11 (1961), §4 pp416--417, §10 pp470--471.
The approximation fields additionally use normalized dilations of an L1
kernel and density in Lp; see BIBLIOGRAPHY_CALLSITE_MAP.md for exact scope. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory FourierTransform Filter LineDeriv
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.Regularization.Actual
open EnergySpace EnergyRegularizer SobolevStretch StationarySelfTest

abbrev LpV (p : ℝ≥0∞) := Lp ℂ p (volume : Measure V)

def besselSymbol (a : ℝ) (ξ : V) : ℂ := resolvent a ξ

theorem besselSymbol_temperate (a : ℝ) : (besselSymbol a).HasTemperateGrowth :=
  Complex.hasTemperateGrowth_ofReal.comp (resolvent_temperate a)

def besselDistribution (a : ℝ) : TD →L[ℂ] TD :=
  TemperedDistribution.fourierMultiplierCLM ℂ (besselSymbol a)

theorem multiplier_sub {m q : V → ℂ} (hm : m.HasTemperateGrowth) (hq : q.HasTemperateGrowth)
    (T : TD) : TemperedDistribution.fourierMultiplierCLM ℂ (m-q) T =
      TemperedDistribution.fourierMultiplierCLM ℂ m T -
      TemperedDistribution.fourierMultiplierCLM ℂ q T := by
  simp only [TemperedDistribution.fourierMultiplierCLM_apply,
    TemperedDistribution.smulLeftCLM_sub hm hq, sub_apply]
  rfl

theorem bessel_cutoff_identity (n : ℕ) (T : TD) :
    besselDistribution (scale n)⁻¹ (T - besselDistribution (scale n) T) =
      (cutoff n).distribution T := by
  rw [map_sub]
  unfold besselDistribution BoundedSymbol.distribution
  rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
    (besselSymbol_temperate _) (besselSymbol_temperate _)]
  rw [← multiplier_sub (besselSymbol_temperate _)
    ((besselSymbol_temperate _).mul (besselSymbol_temperate _))]
  congr 2
  funext ξ
  simp only [Pi.sub_apply, Pi.mul_apply, cutoff, besselSymbol, symbol, realSymbol]
  push_cast
  ring

/-- Ordinary scalar Bessel convolution and its two dilation limits, for 1<p<∞.
The operator is tied to a literal scalar symbol in distributions, and its
norm estimate is numerical (1). No Hartree fact is included. -/
structure OrdinaryBesselLp (p : ℝ≥0∞) [Fact (1 ≤ p)] where
  one_lt : 1 < p
  finite : p < ∞
  operator : ℝ → LpV p →L[ℂ] LpV p
  distribution : ∀ a, 0 < a → ∀ f,
    Lp.toTemperedDistribution (operator a f) = besselDistribution a (Lp.toTemperedDistribution f)
  bound : ∀ a, 0 < a → ∀ f, ‖operator a f‖ ≤ ‖f‖
  small_tendsto : ∀ f, Tendsto (fun n => operator (scale n)⁻¹ f) atTop (𝓝 f)
  large_tendsto : ∀ f, Tendsto (fun n => operator (scale n) f) atTop (𝓝 0)

namespace OrdinaryBesselLp
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def cutoffLp (B : OrdinaryBesselLp p) (n : ℕ) : LpV p →L[ℂ] LpV p :=
  (B.operator (scale n)⁻¹).comp (ContinuousLinearMap.id ℂ (LpV p) - B.operator (scale n))

theorem cutoffLp_distribution (B : OrdinaryBesselLp p) (n : ℕ) (f : LpV p) :
    Lp.toTemperedDistribution (B.cutoffLp n f) =
      (cutoff n).distribution (Lp.toTemperedDistribution f) := by
  change Lp.toTemperedDistribution
    (B.operator (scale n)⁻¹ (f - B.operator (scale n) f)) = _
  rw [B.distribution _ (inv_pos.mpr (scale_pos n))]
  change besselDistribution (scale n)⁻¹
    ((Lp.toTemperedDistributionCLM ℂ (volume : Measure V) p) (f - B.operator (scale n) f)) = _
  rw [map_sub]
  change besselDistribution (scale n)⁻¹
    (Lp.toTemperedDistribution f - Lp.toTemperedDistribution (B.operator (scale n) f)) = _
  rw [B.distribution _ (scale_pos n), bessel_cutoff_identity]

theorem cutoffLp_bound (B : OrdinaryBesselLp p) (n : ℕ) (f : LpV p) :
    ‖B.cutoffLp n f‖ ≤ 2 * ‖f‖ := by
  calc
    _ ≤ ‖f - B.operator (scale n) f‖ := B.bound _ (inv_pos.mpr (scale_pos n)) _
    _ ≤ ‖f‖ + ‖B.operator (scale n) f‖ := norm_sub_le _ _
    _ ≤ ‖f‖ + ‖f‖ := by
      have hb : ‖B.operator (scale n) f‖ ≤ ‖f‖ := B.bound (scale n) (scale_pos n) f
      linarith
    _ = _ := by ring

theorem cutoffLp_strong (B : OrdinaryBesselLp p) (f : LpV p) :
    Tendsto (fun n => B.cutoffLp n f) atTop (𝓝 f) := by
  have hz : Tendsto (fun n => B.operator (scale n)⁻¹ (B.operator (scale n) f)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun n => B.bound _ (inv_pos.mpr (scale_pos n)) _)
      (by simpa only [norm_zero] using (B.large_tendsto f).norm)
  have ht := (B.small_tendsto f).sub hz
  simpa only [cutoffLp, ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.id_apply, map_sub, sub_zero] using ht

end OrdinaryBesselLp

abbrev sourceExponent : ℝ≥0∞ := ENNReal.ofReal (6/5 : ℝ)
abbrev SourceLp := LpV sourceExponent
instance sourceLp_fact : Fact ((1 : ℝ≥0∞) ≤ sourceExponent) := ⟨by norm_num⟩

/-- Bessel order-2 L^{6/5}->L6 and its distributional first derivatives into L2.
The positive-scale scalar-potential maps are ordinary linear analysis:
§4 eq.(4,5) plus §10(1), not the regularized Hartree EnergyState conclusion. -/
structure OrdinaryBesselSmoothing where
  value : ℝ → SourceLp →L[ℂ] L6
  gradient : ℝ → Fin 3 → SourceLp →L[ℂ] L2
  value_distribution : ∀ a, 0 < a → ∀ f,
    Lp.toTemperedDistribution (value a f) = besselDistribution a (Lp.toTemperedDistribution f)
  gradient_distribution : ∀ a, 0 < a → ∀ f j,
    ∂_{coordinate j} (besselDistribution a (Lp.toTemperedDistribution f)) =
      Lp.toTemperedDistribution (gradient a j f)

namespace OrdinaryBesselSmoothing

def energy (S : OrdinaryBesselSmoothing) (a : ℝ) (ha : 0 < a) : SourceLp →L[ℂ] EnergyState :=
  ((S.value a).prod (ContinuousLinearMap.pi (S.gradient a))).codRestrict energySubmodule (by
    intro f
    apply (mem_energySubmodule _).mpr
    intro j
    change ∂_{coordinate j} (Lp.toTemperedDistribution (S.value a f)) =
      Lp.toTemperedDistribution (S.gradient a j f)
    rw [S.value_distribution a ha]
    exact S.gradient_distribution a ha f j)

theorem energy_distribution (S : OrdinaryBesselSmoothing) (a : ℝ) (ha : 0 < a) (f : SourceLp) :
    energyDistribution (S.energy a ha f) = besselDistribution a (Lp.toTemperedDistribution f) :=
  S.value_distribution a ha f

/-- Actual CLM from the real forcing L^{6/5} domain into the existing C43 state.
The closed graph is assembled from the two scalar Bessel mappings. -/
def sourceJ (S : OrdinaryBesselSmoothing) (B : OrdinaryBesselLp sourceExponent) (n : ℕ) :
    SourceLp →L[ℂ] EnergyState :=
  (S.energy (scale n)⁻¹ (inv_pos.mpr (scale_pos n))).comp
    (ContinuousLinearMap.id ℂ SourceLp - B.operator (scale n))

theorem sourceJ_distribution (S : OrdinaryBesselSmoothing) (B : OrdinaryBesselLp sourceExponent)
    (n : ℕ) (f : SourceLp) :
    energyDistribution (S.sourceJ B n f) = (cutoff n).distribution (Lp.toTemperedDistribution f) := by
  change energyDistribution (S.energy (scale n)⁻¹ (inv_pos.mpr (scale_pos n))
    (f - B.operator (scale n) f)) = _
  rw [S.energy_distribution]
  change besselDistribution (scale n)⁻¹
    ((Lp.toTemperedDistributionCLM ℂ (volume : Measure V) sourceExponent)
      (f - B.operator (scale n) f)) = _
  rw [map_sub]
  change besselDistribution (scale n)⁻¹
    (Lp.toTemperedDistribution f - Lp.toTemperedDistribution (B.operator (scale n) f)) = _
  rw [B.distribution _ (scale_pos n), bessel_cutoff_identity]

theorem sourceJ_bound (S : OrdinaryBesselSmoothing) (B : OrdinaryBesselLp sourceExponent)
    (n : ℕ) (f : SourceLp) :
    ‖S.sourceJ B n f‖ ≤ ‖S.sourceJ B n‖ * ‖f‖ :=
  (S.sourceJ B n).le_opNorm f

theorem sourceJ_eq_J (S : OrdinaryBesselSmoothing) (B : OrdinaryBesselLp sourceExponent)
    (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (n : ℕ) (f : SourceLp) (u : EnergyState)
    (h : Lp.toTemperedDistribution f = energyDistribution u) :
    S.sourceJ B n f = J hDensity hSob n u := by
  apply energyDistribution_injective
  rw [S.sourceJ_distribution, h, J_distribution]
  rfl

end OrdinaryBesselSmoothing
end HartreeF.Regularization.Actual

#print axioms HartreeF.Regularization.Actual.OrdinaryBesselLp.cutoffLp_strong
#print axioms HartreeF.Regularization.Actual.OrdinaryBesselSmoothing.sourceJ_distribution
#print axioms HartreeF.Regularization.Actual.OrdinaryBesselSmoothing.sourceJ_eq_J
