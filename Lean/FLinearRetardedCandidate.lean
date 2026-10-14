import FLinearEnergyWeakUniqueness

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
open MeasureTheory LineDeriv
open scoped ENNReal Topology SchwartzMap

namespace HartreeF.LinearWeakEquation
open EnergySpace SobolevStretch StationarySelfTest ActualStrichartz Retarded
open ActualDuhamelPath CriticalPathSpace IntervalTimeTransport

variable (hDensity : OrdinaryH1Density) {K C0 C a b : ℝ}
  (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
  (hret : OrdinaryRetardedStrichartz h0 C) (hab : a ≤ b)
  (E : CompatibleL1IntervalSource a b) (u₀ : EnergyState)

/-- The actual free plus normalized retarded path. Clamping only extends its domain
outside the interval; every later identity is asserted on the original interval. -/
def actualRetardedCandidate (t : ℝ) : EnergyState :=
  freeEnergyState hDensity hSob (t-a) u₀ - Complex.I •
    energyPath _ (E.retardedCriticalPath hDensity hSob h0 hret) (Set.projIcc a b hab t)

theorem actualRetardedCandidate_continuous :
    Continuous (actualRetardedCandidate hDensity hSob h0 hret hab E u₀) := by
  have hproj : Continuous (Set.projIcc a b hab) :=
    Continuous.subtype_mk (continuous_const.max (continuous_const.min continuous_id)) _
  exact ((freeEnergyState_time_continuous hDensity hSob u₀).comp
    (continuous_id.sub continuous_const)).sub
    (((energyPath _ (E.retardedCriticalPath hDensity hSob h0 hret)).continuous.comp
      hproj).const_smul Complex.I)

theorem actualRetardedCandidate_initial :
    actualRetardedCandidate hDensity hSob h0 hret hab E u₀ a = u₀ := by
  simp only [actualRetardedCandidate, sub_self, freeEnergyState_zero_time,
    Set.projIcc_left, E.retardedCriticalPath_initial hDensity hSob h0 hret hab,
    smul_zero, sub_zero]

/-- The candidate uses the original L1 source in the literal scalar integral. -/
theorem actualRetardedCandidate_scalar (t : Set.Icc a b) (φ : FreeFlow.Test) :
    energyDistribution (actualRetardedCandidate hDensity hSob h0 hret hab E u₀ t) φ =
      FreeFlow.free ((t : ℝ)-a) (energyDistribution u₀) φ - Complex.I *
        ∫ s in Set.Ioc a (t : ℝ),
          Lp.toTemperedDistribution (E.value s) (freeTest ((t : ℝ)-s) φ) := by
  simp only [actualRetardedCandidate, Set.projIcc_val, map_sub, map_smul,
    sub_apply, smul_apply, smul_eq_mul, freeEnergyState_distribution,
    E.retardedCriticalPath_forward_scalar hDensity hSob h0 hret]

/-- Explicit final consumer. The candidate's distributional PDE proof remains
a separately named prerequisite; it is not hidden inside a new ordinary interface.
Once that producer is supplied, the approximate path has the literal formula. -/
theorem literal_formula_of_candidate_weakEquation
    (hUnique : OrdinaryL2HomogeneousUniqueness)
    (u : ℝ → EnergyState) (hucont : ContinuousOn u (Set.Icc a b))
    (hu : WeakEquation a b (fun t => energyDistribution (u t))
      (fun t => Lp.toTemperedDistribution (E.value t)))
    (hCandidatePDE : WeakEquation a b
      (fun t => energyDistribution (actualRetardedCandidate hDensity hSob h0 hret hab E u₀ t))
      (fun t => Lp.toTemperedDistribution (E.value t)))
    (hinit : u a = u₀) (t : Set.Icc a b) (φ : FreeFlow.Test) :
    energyDistribution (u t) φ =
      FreeFlow.free ((t : ℝ)-a) (energyDistribution u₀) φ - Complex.I *
        ∫ s in Set.Ioc a (t : ℝ),
          Lp.toTemperedDistribution (E.value s) (freeTest ((t : ℝ)-s) φ) := by
  have he := energy_weak_uniqueness hUnique hSob (Set.left_mem_Icc.mpr hab) u
    (actualRetardedCandidate hDensity hSob h0 hret hab E u₀)
    (fun t => Lp.toTemperedDistribution (E.value t)) hucont
    (actualRetardedCandidate_continuous hDensity hSob h0 hret hab E u₀).continuousOn
    hu hCandidatePDE (hinit.trans (actualRetardedCandidate_initial hDensity hSob h0 hret hab E u₀).symm)
    t t.property
  rw [he]
  exact actualRetardedCandidate_scalar hDensity hSob h0 hret hab E u₀ t φ

end HartreeF.LinearWeakEquation
