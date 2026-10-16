import FLocalMildTrajectory
import FActualHartreeCompactPDE
import FActualPDEToDuhamelRestart

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory Filter Set
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.OriginalSignedDuhamel
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open MaximalTrajectory CriticalUniqueness HartreeDistributionalBridge
open SobolevStretch StationarySelfTest ForcingDomain Retarded FreeTestBounds
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  energyDistribution extendEnergyPath

variable {α c s₀ : ℝ} {u₀ : EnergyState} (U : LocalMildTrajectory α c s₀ u₀)

/-- The finite canonical path agrees with the original trajectory at every point
of the same closed interval, including both endpoints. -/
theorem local_path_extension_same {a b : ℝ} (hab : a ≤ b)
    (hI : Icc a b ⊆ U.domain) (s : ℝ) (hs : s ∈ Icc a b) :
    extendEnergyPath hab (energyPath _ (U.path hab hI)) s = U.state s :=
  (extendEnergyPath_val hab (energyPath _ (U.path hab hI)) ⟨s, hs⟩).trans
    (U.path_agrees hab hI ⟨s, hs⟩)

variable (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
  (hH : OrdinaryHLS α c)

/-- Nested a.e. equality binds the actual finite L1-time/L6/5-space source to the
literal forcing of the SAME original trajectory. It is uniform over spatial tests. -/
theorem local_source_same_forcing {a b : ℝ} (hab : a ≤ b)
    (hI : Icc a b ⊆ U.domain) :
    ∀ᵐ s ∂volume.restrict (Icc a b),
      (actualHartreeSourceL1 hDensity hSob hH hab (U.path hab hI)).value s =ᵐ[volume]
        forcing α c (energyValue (U.state s)) := by
  filter_upwards [actualHartreeSourceL1_value_ae hDensity hSob hH hab (U.path hab hI),
    ae_restrict_mem measurableSet_Icc] with s hs hmem
  rwa [local_path_extension_same U hab hI s hmem] at hs

include hDensity hSob hH in
/-- The original moving-test scalar integrand has its genuine temporal domain.
This is produced from the actual finite source and its same-representative identity. -/
theorem local_freeTest_source_integrable {a b : ℝ} (hab : a ≤ b)
    (hI : Icc a b ⊆ U.domain) (z : ℝ) (φ : Test) :
    IntegrableOn (fun s => ∫ x : V,
      freeTest (z-s) φ x * forcing α c (energyValue (U.state s)) x) (Icc a b) volume := by
  let E := actualHartreeSourceL1 hDensity hSob hH hab (U.path hab hI)
  have hi := freeTestPair_integrable hDensity hSob (volume.restrict (Icc a b)) z φ
    E.value E.value_integrable
  apply hi.congr
  filter_upwards [local_source_same_forcing U hDensity hSob hH hab hI] with s hs
  rw [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [hs] with x hx
  change freeTest (z-s) φ x * E.value s x = _
  rw [hx]

/-- The historical mild definition supplies the literal original finite formula;
no PDE, restart equality, endpoint bound or homogeneous uniqueness is an input. -/
theorem local_mild_forward_original {a b : ℝ} (hab : a ≤ b)
    (hI : Icc a b ⊆ U.domain) (φ : Test) :
    energyDistribution (U.state b) φ =
      energyDistribution (U.state a) (freeTest (b-a) φ) + Complex.I *
        ∫ s in Icc a b, ∫ x : V,
          freeTest (b-s) φ x * forcing α c (energyValue (U.state s)) x := by
  have h := U.path_mild hab hI (⟨b, hab, le_rfl⟩ : Icc a b) φ
  rw [U.path_agrees hab hI] at h
  rw [integral_Icc_eq_integral_Ioc]
  refine h.trans ?_
  congr 1
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [local_path_extension_same U hab hI s ⟨hs.1.le, hs.2⟩]
  rfl

end HartreeF.OriginalSignedDuhamel
