import FPaperStabilitySumNorm
import FJointLpRealization
import FCriticalPathRestriction

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.RawStabilityInputs
open EnergySpace CriticalPathSpace TimeHolder CriticalPathRestriction HomogeneousStability
open SobolevStretch StationarySelfTest EndpointOutput
attribute [local irreducible] energySubmodule criticalPathSubmodule criticalGradient

/-- The coordinate representatives are produced from continuity in the existing
energy space; no spacetime measurability of a chosen gradient is assumed. -/
def continuousGradientField {a b : ℝ} (q : C(Icc a b, EnergyState)) (j : Fin 3) :
    Icc a b × Space → ℂ :=
  strongJointLpRepresentative volume 2 (fun t => energyGradient j (q t))
    ((energyGradient j).continuous.comp q.continuous).stronglyMeasurable

theorem continuousGradientField_measurable {a b : ℝ}
    (q : C(Icc a b, EnergyState)) (j : Fin 3) :
    StronglyMeasurable (continuousGradientField q j) :=
  strongJointLpRepresentative_stronglyMeasurable _ _ _ _

theorem continuousGradientField_slice {a b : ℝ}
    (q : C(Icc a b, EnergyState)) (j : Fin 3) (t : Icc a b) :
    (fun x => continuousGradientField q j (t,x)) =ᵐ[volume] energyGradient j (q t) :=
  strongJointLpRepresentative_slice _ _ _ _ t

/-- Each coordinate is bounded by the actual Euclidean gradient, with joint
measurability proved before the mixed-norm monotonicity step. -/
theorem continuousGradientField_mixedNorm_le {a b : ℝ}
    (q : C(Icc a b, EnergyState)) (j : Fin 3) :
    mixedNorm (intervalMeasure a b) volume 10 criticalExponent
      (fun t x => continuousGradientField q j (t,x)) ≤
    mixedNorm (intervalMeasure a b) volume 10 criticalExponent
      (fun t => energyComplexGradient (q t)) := by
  apply eLpNorm_mono_enorm_ae
    (spatial_lp_time_measurable (intervalMeasure a b) volume criticalExponent
      (by norm_num) (by norm_num) _
      (continuousGradientField_measurable q j).aestronglyMeasurable)
  filter_upwards [] with t
  simp only [enorm_eq_self]
  rw [eLpNorm_congr_ae (continuousGradientField_slice q j t)]
  apply eLpNorm_mono (Lp.aestronglyMeasurable _)
  intro x
  rw [← energyComplexGradient_coordinate]
  exact PiLp.norm_apply_le _ j

/-- A continuous energy curve with locally finite actual W has its genuine
critical graph element. Finiteness is needed only on this compact interval. -/
def criticalPathOfContinuousActualW {a b : ℝ} (q : C(Icc a b, EnergyState))
    (hW : mixedNorm (intervalMeasure a b) volume 10 criticalExponent
      (fun t => energyComplexGradient (q t)) ≠ ∞) : CriticalPath (intervalMeasure a b) := by
  let d := continuousGradientField q
  have hm (j : Fin 3) : AEStronglyMeasurable (d j) ((intervalMeasure a b).prod volume) :=
    (continuousGradientField_measurable q j).aestronglyMeasurable
  have hf (j : Fin 3) : mixedNorm (intervalMeasure a b) volume 10 criticalExponent
      (fun t x => d j (t,x)) ≠ ∞ :=
    ne_top_of_le_ne_top hW (continuousGradientField_mixedNorm_le q j)
  have hs (j : Fin 3) : ∀ᵐ t ∂intervalMeasure a b,
      MemLp (fun x => d j (t,x)) criticalExponent volume :=
    finite_mixedNorm_ae_slice_memLp (intervalMeasure a b) volume 10 criticalExponent
      (by norm_num) (by norm_num) _ (hf j)
  let D (j : Fin 3) : CriticalGradient (intervalMeasure a b) :=
    jointLpRealization (intervalMeasure a b) volume 10 criticalExponent (d j) (hm j) (hs j) (hf j)
  refine ofRepresentativeAgreement (intervalMeasure a b) q D ?_
  intro j
  filter_upwards [jointLpRealization_coeFn (intervalMeasure a b) volume 10 criticalExponent
    (d j) (hm j) (hs j) (hf j)] with t ht
  exact Filter.EventuallyEq.trans (Filter.EventuallyEq.symm (continuousGradientField_slice q j t))
    (Filter.EventuallyEq.symm ht)

@[simp] theorem criticalPathOfContinuousActualW_energy {a b : ℝ}
    (q : C(Icc a b, EnergyState))
    (hW : mixedNorm (intervalMeasure a b) volume 10 criticalExponent
      (fun t => energyComplexGradient (q t)) ≠ ∞) (t : Icc a b) :
    energyPath _ (criticalPathOfContinuousActualW q hW) t = q t := rfl

/-- This input is only continuity on I and local actual W finiteness, the W
component already contained in the manuscript's locally finite Z hypothesis. -/
structure LocallyCriticalEnergyCurve (I : Set ℝ) (q : ℝ → EnergyState) : Prop where
  continuousOn : ContinuousOn q I
  localW : ∀ {a b : ℝ}, a ≤ b → Icc a b ⊆ I →
    mixedNorm (intervalMeasure a b) volume 10 criticalExponent
      (fun t => energyComplexGradient (q t)) ≠ ∞

namespace LocallyCriticalEnergyCurve
variable {I : Set ℝ} {q : ℝ → EnergyState} (h : LocallyCriticalEnergyCurve I q)

def compactPath {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I) :
    CriticalPath (intervalMeasure a b) :=
  criticalPathOfContinuousActualW
    ⟨fun t => q t, continuousOn_iff_continuous_domRestrict.mp (h.continuousOn.mono hI)⟩
    (h.localW hab hI)

@[simp] theorem compactPath_energy {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I)
    (t : Icc a b) : energyPath _ (h.compactPath hab hI) t = q t := rfl

theorem compactPath_restrict {a b c d : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    restrictPath hac hcd hdb (h.compactPath hab hI) =
      h.compactPath hcd ((Icc_subset_Icc hac hdb).trans hI) := by
  apply energyPath_injective
  apply ContinuousMap.ext
  intro t
  simp only [restrictPath_energy, compactPath_energy]
  rfl

theorem compactPath_norm_mono {a b c d : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    ‖h.compactPath hcd ((Icc_subset_Icc hac hdb).trans hI)‖ ≤ ‖h.compactPath hab hI‖ := by
  rw [← h.compactPath_restrict hab hI hac hcd hdb]
  exact restrictPath_norm_le hac hcd hdb _

end LocallyCriticalEnergyCurve
#print axioms criticalPathOfContinuousActualW
#print axioms LocallyCriticalEnergyCurve.compactPath_restrict
end HartreeF.RawStabilityInputs
