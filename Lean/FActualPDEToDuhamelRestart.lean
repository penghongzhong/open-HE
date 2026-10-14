import FActualPDEToDuhamel

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory LineDeriv Laplacian
open scoped ENNReal Topology SchwartzMap

namespace HartreeF.LinearWeakEquation
open EnergySpace Retarded FreeTestBounds SobolevStretch StationarySelfTest ActualStrichartz
open ActualDuhamelPath CriticalPathSpace IntervalTimeTransport

/-- Native transport of the exact bilinear test propagator, with no sign reversal. -/
theorem freeTestPair_transport (T : TD) (r q : ℝ) (φ : Test) :
    T (freeTest q (freeTest r φ)) = T (freeTest (r+q) φ) := by
  have h := congrArg (fun D : TD => D φ) (FreeFlow.free_add r q T)
  simpa only [free_apply] using h.symm

variable (hDensity : OrdinaryH1Density) {K C0 C a b : ℝ}
  (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
  (hret : OrdinaryRetardedStrichartz h0 C) (hab : a ≤ b)
  (E : CompatibleL1IntervalSource a b)

include hDensity hSob in
/-- Restart at any point of the same compact interval. The oriented integral
handles both directions, so no left-time existence or uniqueness assumption is added. -/
theorem literal_formula_restart
    (u : ℝ → EnergyState)
    (hFormula : ∀ t : Set.Icc a b, ∀ φ : FreeFlow.Test,
      energyDistribution (u t) φ =
        FreeFlow.free ((t : ℝ)-a) (energyDistribution (u a)) φ - Complex.I *
          ∫ s in Set.Ioc a (t : ℝ),
            Lp.toTemperedDistribution (E.value s) (freeTest ((t : ℝ)-s) φ))
    (t₀ t : Set.Icc a b) (φ : FreeFlow.Test) :
    IntervalIntegrable (fun s => Lp.toTemperedDistribution (E.value s)
      (freeTest ((t : ℝ)-s) φ)) volume (t₀ : ℝ) (t : ℝ) ∧
    energyDistribution (u t) φ =
      FreeFlow.free ((t : ℝ)-(t₀ : ℝ)) (energyDistribution (u t₀)) φ - Complex.I *
        ∫ s in (t₀ : ℝ)..(t : ℝ),
          Lp.toTemperedDistribution (E.value s) (freeTest ((t : ℝ)-s) φ) := by
  let k : ℝ → ℂ := fun s => Lp.toTemperedDistribution (E.value s) (freeTest ((t : ℝ)-s) φ)
  have hki : IntegrableOn k (Set.Icc a b) :=
    freeTestPair_integrable hDensity hSob (volume.restrict (Set.Icc a b)) t φ
      E.value E.value_integrable
  have hit : IntervalIntegrable k volume a (t : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le t.property.1).mpr
      (hki.mono_set (Set.Icc_subset_Icc le_rfl t.property.2))
  have hit₀ : IntervalIntegrable k volume a (t₀ : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le t₀.property.1).mpr
      (hki.mono_set (Set.Icc_subset_Icc le_rfl t₀.property.2))
  refine ⟨hit₀.symm.trans hit, ?_⟩
  have ht := hFormula t φ
  have ht₀ := hFormula t₀ (freeTest ((t : ℝ)-(t₀ : ℝ)) φ)
  have hp (s : ℝ) : Lp.toTemperedDistribution (E.value s)
      (freeTest ((t₀ : ℝ)-s) (freeTest ((t : ℝ)-(t₀ : ℝ)) φ)) = k s := by
    rw [freeTestPair_transport]
    congr 2
    ring
  have hf : FreeFlow.free ((t₀ : ℝ)-a) (energyDistribution (u a))
      (freeTest ((t : ℝ)-(t₀ : ℝ)) φ) =
      FreeFlow.free ((t : ℝ)-a) (energyDistribution (u a)) φ := by
    rw [← free_apply, ← FreeFlow.free_add]
    congr 2
    ring
  rw [hf] at ht₀
  simp only [hp] at ht₀
  rw [← intervalIntegral.integral_of_le t.property.1] at ht
  rw [← intervalIntegral.integral_of_le t₀.property.1] at ht₀
  rw [free_apply, ht₀, ht]
  change _ = _ - Complex.I * ∫ s in (t₀ : ℝ)..(t : ℝ), k s
  rw [← intervalIntegral.integral_interval_sub_left hit hit₀]
  ring

include hDensity hSob h0 hret hab in
theorem distributional_energy_literal_formula_at
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2HomogeneousUniqueness)
    (u : ℝ → EnergyState) (hucont : ContinuousOn u (Set.Icc a b))
    (hu : WeakEquation a b (fun t => energyDistribution (u t))
      (fun t => Lp.toTemperedDistribution (E.value t)))
    (t₀ t : Set.Icc a b) (φ : FreeFlow.Test) :
    IntervalIntegrable (fun s => Lp.toTemperedDistribution (E.value s)
      (freeTest ((t : ℝ)-s) φ)) volume (t₀ : ℝ) (t : ℝ) ∧
    energyDistribution (u t) φ =
      FreeFlow.free ((t : ℝ)-(t₀ : ℝ)) (energyDistribution (u t₀)) φ - Complex.I *
        ∫ s in (t₀ : ℝ)..(t : ℝ),
          Lp.toTemperedDistribution (E.value s) (freeTest ((t : ℝ)-s) φ) :=
  literal_formula_restart hDensity hSob E u
    (distributional_energy_literal_formula hDensity hSob h0 hret hab E (u a)
      hgen hUnique u hucont hu rfl) t₀ t φ

end HartreeF.LinearWeakEquation
