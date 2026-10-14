import FL1RetardedScalarIdentity

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology
namespace HartreeF.ActualDuhamelPath.CompatibleL1IntervalSource
open CriticalPathSpace IntervalTimeTransport EnergySpace ForcingDomain
open SobolevStretch StationarySelfTest Retarded ActualStrichartz
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath energyDistribution retardedCriticalPath

variable {a b : ℝ}

/-- Native time-L1 subtraction, with the actual time-L2 spatial derivative classes. -/
def sub (E F : CompatibleL1IntervalSource a b) : CompatibleL1IntervalSource a b where
  value := E.value - F.value
  gradient := E.gradient - F.gradient
  derivative := by
    have hgrad := ae_all_iff.mpr (fun j => Lp.coeFn_sub (E.gradient j) (F.gradient j))
    filter_upwards [E.derivative, F.derivative, Lp.coeFn_sub E.value F.value, hgrad]
      with t hE hF hv hg
    intro j
    simp only [Pi.sub_apply] at hv hg ⊢
    rw [hv, hg]
    change (lineDerivOpCLM ℂ FreeFlow.TD (coordinate j))
      ((Lp.toTemperedDistributionCLM ℂ volume (ENNReal.ofReal (6/5 : ℝ)))
        (E.value t - F.value t)) =
      (Lp.toTemperedDistributionCLM ℂ volume (ENNReal.ofReal (6/5 : ℝ)))
        (E.gradient j t - F.gradient j t)
    rw [map_sub, map_sub, map_sub]
    exact congrArg₂ (fun x y : FreeFlow.TD => x - y) (hE j) (hF j)

theorem sub_value (E F : CompatibleL1IntervalSource a b) :
    (E.sub F).value = E.value - F.value := rfl

theorem sub_gradient (E F : CompatibleL1IntervalSource a b) :
    (E.sub F).gradient = E.gradient - F.gradient := rfl

/-- Representatives of the value quotient subtract at almost every original time. -/
theorem sub_value_ae (E F : CompatibleL1IntervalSource a b) :
    ((E.sub F).value : ℝ → SourceSpace) =ᵐ[localMeasure a b]
      (fun t => E.value t - F.value t) :=
  Lp.coeFn_sub E.value F.value

/-- Representatives of every actual derivative quotient subtract almost everywhere. -/
theorem sub_gradient_ae (E F : CompatibleL1IntervalSource a b) :
    ∀ᵐ t ∂localMeasure a b, ∀ j : Fin 3,
      (E.sub F).gradient j t = E.gradient j t - F.gradient j t :=
  ae_all_iff.mpr (fun j => Lp.coeFn_sub (E.gradient j) (F.gradient j))

/-- Subtraction remains the literal subtraction of the original spatial distributions. -/
theorem sub_distribution_ae (E F : CompatibleL1IntervalSource a b) :
    ∀ᵐ t ∂localMeasure a b,
      Lp.toTemperedDistribution ((E.sub F).value t) =
        Lp.toTemperedDistribution (E.value t) - Lp.toTemperedDistribution (F.value t) := by
  filter_upwards [E.sub_value_ae F] with t ht
  rw [ht]
  exact (Lp.toTemperedDistributionCLM ℂ volume (ENNReal.ofReal (6/5 : ℝ))).map_sub _ _

/-- Actual scalar integrability permits subtraction under the literal retarded integral. -/
theorem sub_retarded_scalar_integral (E F : CompatibleL1IntervalSource a b)
    (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (t : ℝ) (φ : FreeFlow.Test) :
    (∫ s in Set.Icc a b ∩ Set.Iio t,
      Lp.toTemperedDistribution ((E.sub F).value s) (freeTest (t-s) φ)) =
    (∫ s in Set.Icc a b ∩ Set.Iio t,
      Lp.toTemperedDistribution (E.value s) (freeTest (t-s) φ)) -
    (∫ s in Set.Icc a b ∩ Set.Iio t,
      Lp.toTemperedDistribution (F.value s) (freeTest (t-s) φ)) := by
  have hd := (ae_mono (Measure.restrict_mono_set volume
    (Set.inter_subset_left : Set.Icc a b ∩ Set.Iio t ⊆ Set.Icc a b)))
    (E.sub_distribution_ae F)
  calc
    _ = ∫ s in Set.Icc a b ∩ Set.Iio t,
        (Lp.toTemperedDistribution (E.value s) (freeTest (t-s) φ) -
          Lp.toTemperedDistribution (F.value s) (freeTest (t-s) φ)) := by
      apply integral_congr_ae
      filter_upwards [hd] with s hs
      rw [hs]
      rfl
    _ = _ := integral_sub (E.retarded_scalar_integrable hDensity hSob t φ)
      (F.retarded_scalar_integrable hDensity hSob t φ)

attribute [local irreducible] sub

/-- Scalar evaluation of the produced path preserves native source subtraction. -/
theorem retarded_sub_scalar (E F : CompatibleL1IntervalSource a b)
    (hDensity : OrdinaryH1Density) {K C0 C : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (t : Set.Icc a b) (φ : FreeFlow.Test) :
    energyDistribution (energyPath _ ((E.sub F).retardedCriticalPath hDensity hSob h0 h) t) φ =
      energyDistribution (energyPath _ (E.retardedCriticalPath hDensity hSob h0 h) t) φ -
        energyDistribution (energyPath _ (F.retardedCriticalPath hDensity hSob h0 h) t) φ := by
  exact ((E.sub F).retardedCriticalPath_scalar hDensity hSob h0 h t φ).trans
    ((E.sub_retarded_scalar_integral F hDensity hSob t φ).trans
      (congrArg₂ (fun x y : ℂ => x - y)
        (E.retardedCriticalPath_scalar hDensity hSob h0 h t φ).symm
        (F.retardedCriticalPath_scalar hDensity hSob h0 h t φ).symm))

/-- The actual retarded graph preserves native source subtraction. -/
theorem retarded_sub (E F : CompatibleL1IntervalSource a b)
    (hDensity : OrdinaryH1Density) {K C0 C : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) :
    (E.sub F).retardedCriticalPath hDensity hSob h0 h =
      E.retardedCriticalPath hDensity hSob h0 h -
        F.retardedCriticalPath hDensity hSob h0 h := by
  apply energyPath_injective (intervalMeasure a b)
  apply ContinuousMap.ext
  intro t
  apply energyDistribution_injective
  have hP := criticalPath_energy_sub_apply
    (E.retardedCriticalPath hDensity hSob h0 h)
    (F.retardedCriticalPath hDensity hSob h0 h) t
  have hD := energyDistribution.map_sub
    (energyPath _ (E.retardedCriticalPath hDensity hSob h0 h) t)
    (energyPath _ (F.retardedCriticalPath hDensity hSob h0 h) t)
  apply Eq.trans ?_ (hD.symm.trans (congrArg energyDistribution hP.symm))
  apply ContinuousLinearMap.ext
  intro φ
  exact E.retarded_sub_scalar F hDensity hSob h0 h t φ

end HartreeF.ActualDuhamelPath.CompatibleL1IntervalSource
