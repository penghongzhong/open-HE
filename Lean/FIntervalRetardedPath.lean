import FActualCriticalPathProducer
import FCompatibleIntervalSource
import FLocalRetardedEnergyState

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology
namespace HartreeF.ActualDuhamelPath
open CriticalPathSpace IntervalTimeTransport EnergySpace ForcingDomain TimeHolder
open SobolevStretch StationarySelfTest Retarded ActualStrichartz

/-- Extend the actual local sources by zero and construct the retarded output
in the complete path graph. Source derivative compatibility survives extension. -/
def intervalRetardedCriticalPath (hDensity : OrdinaryH1Density) {K C0 C a b : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (F : CompatibleIntervalSource a b) :
    CriticalPath (intervalMeasure a b) :=
  retardedCriticalPath hDensity hSob h0 h a b
    (extendEndpointSource (Set.Icc a b) measurableSet_Icc F.value)
    (fun j => extendEndpointSource (Set.Icc a b) measurableSet_Icc (F.gradient j))
    (ae_all_iff.mp (extendEndpointSource_coordinate_derivatives (Set.Icc a b)
      measurableSet_Icc F.value F.gradient F.derivative))

theorem intervalRetardedCriticalPath_scalar (hDensity : OrdinaryH1Density) {K C0 C a b : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (F : CompatibleIntervalSource a b)
    (t : Set.Icc a b) (φ : FreeFlow.Test) :
    energyDistribution (energyPath _ (intervalRetardedCriticalPath hDensity hSob h0 h F) t) φ =
      ∫ s in Set.Icc a b ∩ Set.Iio (t : ℝ),
        Lp.toTemperedDistribution (F.value s) (freeTest ((t : ℝ)-s) φ) := by
  unfold intervalRetardedCriticalPath
  rw [retardedCriticalPath_energy, retardedEnergyState, restrictedEnergyState, l2EnergyState_distribution]
  exact restrictedL2_extend_scalar h0 (Set.Icc a b) measurableSet_Icc F.value
    (Set.Iio (t : ℝ)) measurableSet_Iio t φ

theorem intervalRetardedCriticalPath_initial (hDensity : OrdinaryH1Density) {K C0 C a b : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (hab : a ≤ b) (F : CompatibleIntervalSource a b) :
    energyPath _ (intervalRetardedCriticalPath hDensity hSob h0 h F) ⟨a, le_rfl, hab⟩ = 0 := by
  apply energyDistribution_injective
  ext φ
  rw [intervalRetardedCriticalPath_scalar]
  have he : Set.Icc a b ∩ Set.Iio a = ∅ := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iio, Set.mem_empty_iff_false, iff_false]
    exact fun hs => (not_lt_of_ge hs.1.1) hs.2
  simp [he]

/-- On the closed output interval, the all-past support is the usual forward interval. -/
theorem intervalPast_eq_Ico {a b : ℝ} (t : Set.Icc a b) :
    Set.Icc a b ∩ Set.Iio (t : ℝ) = Set.Ico a (t : ℝ) := by
  ext s
  simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iio, Set.mem_Ico]
  constructor
  · exact fun hs => ⟨hs.1.1, hs.2⟩
  · exact fun hs => ⟨⟨hs.1, hs.2.le.trans t.property.2⟩, hs.2⟩

theorem intervalRetardedCriticalPath_forward_scalar (hDensity : OrdinaryH1Density)
    {K C0 C a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (F : CompatibleIntervalSource a b)
    (t : Set.Icc a b) (φ : FreeFlow.Test) :
    energyDistribution (energyPath _ (intervalRetardedCriticalPath hDensity hSob h0 h F) t) φ =
      ∫ s in Set.Ioc a (t : ℝ),
        Lp.toTemperedDistribution (F.value s) (freeTest ((t : ℝ)-s) φ) := by
  rw [intervalRetardedCriticalPath_scalar, intervalPast_eq_Ico, integral_Ico_eq_integral_Ioc]

end HartreeF.ActualDuhamelPath
