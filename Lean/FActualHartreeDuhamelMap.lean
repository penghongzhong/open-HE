import FIntervalRetardedPath
import FIntervalHartreeSources

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology
namespace HartreeF.ActualDuhamelPath
open CriticalPathSpace IntervalTimeTransport EnergySpace LocalScalarSource ForcingDomain TimeHolder
open SobolevStretch StationarySelfTest Retarded ActualStrichartz
attribute [local irreducible] criticalPathIntervalSource intervalRetardedCriticalPath
  freeCriticalPath criticalPathOfGlobalFields CriticalJointSources.jointFields

/-- The actual Hartree Duhamel map on the established complete path space.
The coefficient is +i for i u_t + Δu + N(u) = 0. Its source, weak derivatives,
time continuity and all three critical output coordinates are constructed. -/
def hartreeDuhamelMap (hDensity : OrdinaryH1Density) {K C0 Ch Cr alpha c a b : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (u0 : EnergyState)
    (u : CriticalPath (intervalMeasure a b)) : CriticalPath (intervalMeasure a b) :=
  freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) u0) +
    Complex.I • intervalRetardedCriticalPath hDensity hSob h0 hret
      (criticalPathIntervalSource hDensity hSob hH hab u 0)

attribute [local irreducible] hartreeDuhamelMap

theorem hartreeDuhamelMap_initial (hDensity : OrdinaryH1Density) {K C0 Ch Cr alpha c a b : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (u0 : EnergyState)
    (u : CriticalPath (intervalMeasure a b)) :
    energyPath _ (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u)
      ⟨a, le_rfl, hab⟩ = u0 := by
  simp only [hartreeDuhamelMap, map_add, map_smul, ContinuousMap.add_apply,
    ContinuousMap.smul_apply, freeCriticalPath_energy]
  rw [intervalRetardedCriticalPath_initial hDensity hSob h0 hret hab, smul_zero, add_zero]
  exact freeEnergyState_inverse hDensity hSob a u0

/-- The exact integral formula before replacing its source by its proven
literal Hartree representative. -/
theorem hartreeDuhamelMap_source_formula (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (u0 : EnergyState)
    (u : CriticalPath (intervalMeasure a b)) (t : Set.Icc a b) (φ : FreeFlow.Test) :
    energyDistribution (energyPath _ (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u) t) φ =
      FreeFlow.free ((t : ℝ) - a) (energyDistribution u0) φ + Complex.I *
        ∫ s in Set.Icc a b ∩ Set.Iio (t : ℝ),
          Lp.toTemperedDistribution
            ((criticalPathIntervalSource hDensity hSob hH hab u 0).value s)
            (freeTest ((t : ℝ)-s) φ) := by
  simp only [hartreeDuhamelMap, map_add, map_smul, ContinuousMap.add_apply,
    ContinuousMap.smul_apply, add_apply, smul_apply,
    freeCriticalPath_energy, intervalRetardedCriticalPath_scalar, smul_eq_mul]
  rw [← freeEnergyState_add_time, freeEnergyState_distribution]
  simp only [sub_eq_add_neg]

/-- The zero value has zero literal forcing, including all totalized powers. -/
theorem forcing_zero_function (alpha c : ℝ) : forcing alpha c (fun _ : Space => 0) = 0 := by
  ext x
  simp [forcing, localFactor]

/-- Zero-path forcing vanishes almost everywhere, without pointwise claims on Lp representatives. -/
theorem zeroPath_forcing_ae {a b : ℝ} (hab : a ≤ b) (alpha c s : ℝ) :
    forcing alpha c (energyValue (extendEnergyPath hab
      (energyPath (intervalMeasure a b) (0 : CriticalPath (intervalMeasure a b))) s)) =ᵐ[volume]
      (0 : Space → ℂ) := by
  change forcing alpha c (energyValue (0 : EnergyState)) =ᵐ[volume] (0 : Space → ℂ)
  rw [map_zero]
  have hz : ((0 : Lp ℂ 6 (volume : Measure Space)) : Space → ℂ) =ᵐ[volume]
      (fun _ => 0) := Lp.coeFn_zero ℂ 6 volume
  have hn := forcing_ae_of_ae (alpha := alpha) (c := c) hz
  simpa only [forcing_zero_function] using hn

/-- The constructed source with zero comparison path is the literal nonlinearity. -/
theorem criticalPathIntervalSource_single_coeFn (hDensity : OrdinaryH1Density)
    {K alpha c a b : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (u : CriticalPath (intervalMeasure a b)) :
    ∀ᵐ s ∂localMeasure a b,
      (criticalPathIntervalSource hDensity hSob hH hab u 0).value s =ᵐ[volume]
        forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ u) s)) := by
  filter_upwards [criticalPathIntervalSource_value_coeFn hDensity hSob hH hab u 0] with s hs
  filter_upwards [hs, zeroPath_forcing_ae hab alpha c s] with x hx hz
  simpa only [hz, Pi.zero_apply, sub_zero] using hx

/-- Representative replacement under the actual retarded scalar integral. -/
theorem localSource_integral_formula {a b : ℝ}
    (F : LocalEndpointSource (Set.Icc a b)) (f : ℝ → Space → ℂ)
    (hF : ∀ᵐ s ∂localMeasure a b, (F s : Space → ℂ) =ᵐ[volume] f s)
    (t : ℝ) (φ : FreeFlow.Test) :
    (∫ s in Set.Icc a b ∩ Set.Iio t,
      Lp.toTemperedDistribution (F s) (freeTest (t-s) φ)) =
      ∫ s in Set.Icc a b ∩ Set.Iio t, ∫ x, (freeTest (t-s) φ) x • f s x := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left hF] with s hs
  rw [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  exact hs.mono (fun x hx => congrArg (fun z : ℂ => (freeTest (t-s) φ) x • z) hx)

/-- The retarded integrand is the actual Hartree nonlinearity of the input path. -/
theorem hartreeDuhamelMap_literal_formula (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (u0 : EnergyState)
    (u : CriticalPath (intervalMeasure a b)) (t : Set.Icc a b) (φ : FreeFlow.Test) :
    energyDistribution (energyPath _ (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u) t) φ =
      FreeFlow.free ((t : ℝ) - a) (energyDistribution u0) φ + Complex.I *
        ∫ s in Set.Icc a b ∩ Set.Iio (t : ℝ), ∫ x,
          (freeTest ((t : ℝ)-s) φ) x •
            forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ u) s)) x := by
  rw [hartreeDuhamelMap_source_formula hDensity hSob h0 hfree hret hH hab u0 u t φ]
  apply congrArg (fun z : ℂ => FreeFlow.free ((t : ℝ) - a) (energyDistribution u0) φ + Complex.I * z)
  exact localSource_integral_formula
    (criticalPathIntervalSource hDensity hSob hH hab u 0).value
    (fun s => forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ u) s)))
    (criticalPathIntervalSource_single_coeFn hDensity hSob hH hab u) t φ

/-- The interval-domain conversion is proved before inserting a nonlinear integrand. -/
theorem localPast_integral_eq_forward {a b : ℝ} (t : Set.Icc a b) (f : ℝ → ℂ) :
    (∫ s in Set.Icc a b ∩ Set.Iio (t : ℝ), f s) = ∫ s in Set.Ioc a (t : ℝ), f s := by
  rw [intervalPast_eq_Ico, integral_Ico_eq_integral_Ioc]

/-- The conventional (a,t] Duhamel formula; endpoint choices agree for Lebesgue time. -/
theorem hartreeDuhamelMap_forward_formula (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (u0 : EnergyState)
    (u : CriticalPath (intervalMeasure a b)) (t : Set.Icc a b) (φ : FreeFlow.Test) :
    energyDistribution (energyPath _ (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u) t) φ =
      FreeFlow.free ((t : ℝ) - a) (energyDistribution u0) φ + Complex.I *
        ∫ s in Set.Ioc a (t : ℝ), ∫ x,
          (freeTest ((t : ℝ)-s) φ) x •
            forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ u) s)) x := by
  calc
    _ = FreeFlow.free ((t : ℝ) - a) (energyDistribution u0) φ + Complex.I *
        ∫ s in Set.Icc a b ∩ Set.Iio (t : ℝ), ∫ x,
          (freeTest ((t : ℝ)-s) φ) x •
            forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ u) s)) x :=
      hartreeDuhamelMap_literal_formula hDensity hSob h0 hfree hret hH hab u0 u t φ
    _ = _ := congrArg
      (fun z : ℂ => FreeFlow.free ((t : ℝ) - a) (energyDistribution u0) φ + Complex.I * z)
      (localPast_integral_eq_forward t (fun s => ∫ x,
        (freeTest ((t : ℝ)-s) φ) x •
          forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ u) s)) x))

end HartreeF.ActualDuhamelPath
