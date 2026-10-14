import FActualDifferenceNormExhaustion
import FTwoSidedNestedLpAssembly
import FIntervalExhaustionGeometry

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.IntervalNormExhaustion
open EnergySpace CriticalPathSpace CriticalSourceBounds CriticalJointSources
open TimeHolder EndpointOutput HomogeneousStability SobolevStretch StationarySelfTest ActualSTail
open ActualPerturbation
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath jointFields
  ActualNestedLpBound ActualPaperRealization fullZSDifferenceSize

/-- Each mixed component is glued from the actual left and right zero extensions.
The enlarged constant is explicit, including at the infinite time exponent. -/
theorem ActualPaperRealization.two_sided {I : Set ℝ} (hI : MeasurableSet I)
    (s : ℝ) (d : ℝ → EnergyState) (CL CR : ℝ)
    (hL : ActualPaperRealization (I ∩ Iic s) d CL)
    (hR : ActualPaperRealization (I ∩ Ici s) d CR) :
    ActualPaperRealization I d (CL+CR) := by
  unfold ActualPaperRealization at hL hR ⊢
  have glue {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E]
      (ν : Measure X) (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
      (g : ℝ → X → E)
      (hl : ActualNestedLpBound ν p r (I ∩ Iic s) g CL)
      (hr : ActualNestedLpBound ν p r (I ∩ Ici s) g CR) :
      ActualNestedLpBound ν p r I g (CL+CR) := by
    unfold ActualNestedLpBound at hl hr ⊢
    obtain ⟨FL,hlb,hla,hlz⟩ := hl
    obtain ⟨FR,hrb,hra,hrz⟩ := hr
    exact exists_global_nestedLp_of_two_halves ν p r I hI s g CL CR FL FR
      hlb hrb hla hra hlz hrz
  let : Fact ((1 : ℝ≥0∞) ≤ ∞) := ⟨le_top⟩
  exact ⟨glue volume ∞ 2 _ hL.1 hR.1,
    glue volume 10 criticalExponent _ hL.2.1 hR.2.1,
    glue volume 2 6 _ hL.2.2.1 hR.2.2.1,
    glue volume 10 10 _ hL.2.2.2 hR.2.2.2⟩

/-- Uniform anchored compact differences alone produce every global actual
mixed-Lp representative. No full-interval bound or global representative is
assumed; unbounded, open, closed and singleton intervals all share this proof. -/
theorem actualPaperRealization_of_anchored_compact_differences (hDensity : OrdinaryH1Density)
    {K C : ℝ} (hSob : OrdinarySobolev K) (hC : 0 ≤ C)
    (I : Set ℝ) (hI : OrdConnected I) {s : ℝ} (hs : s ∈ I)
    (u q : ℝ → EnergyState)
    (U Q : ∀ {a b : ℝ}, a ≤ b → Icc a b ⊆ I → CriticalPath (intervalMeasure a b))
    (hU : ∀ {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ I) (t : Icc a b),
      energyPath _ (U hab hsub) t=u t)
    (hQ : ∀ {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ I) (t : Icc a b),
      energyPath _ (Q hab hsub) t=q t)
    (hleft : ∀ {a : ℝ} (ha : a ∈ I) (has : a ≤ s),
      fullZSDifferenceSize (U has (hI.out' ha hs)) (Q has (hI.out' ha hs)) ≤ ENNReal.ofReal C)
    (hright : ∀ {b : ℝ} (hb : b ∈ I) (hsb : s ≤ b),
      fullZSDifferenceSize (U hsb (hI.out' hs hb)) (Q hsb (hI.out' hs hb)) ≤ ENNReal.ofReal C) :
    ActualPaperRealization I (fun t => u t-q t) (6*C) := by
  obtain ⟨a,ha,haI,hca⟩ := exists_left_interval_exhaustion I hI hs
  obtain ⟨b,hb,hbI,hcb⟩ := exists_right_interval_exhaustion I hI hs
  have hleft' : ActualPaperRealization (I ∩ Iic s) (fun t => u t-q t) (3*C) := by
    have hsub (n : ℕ) : Icc (a n) s ⊆ I := hI.out' (haI n).1 hs
    have hd (n : ℕ) (t : Icc (a n) s) :
        energyPath _ (U (haI n).2 (hsub n)-Q (haI n).2 (hsub n)) t=u t-q t := by
      exact (energyPath_sub_apply (intervalMeasure (a n) s)
        (U (haI n).2 (hsub n)) (Q (haI n).2 (hsub n)) t).trans
        (congrArg₂ (fun x y : EnergyState => x-y)
          (hU (haI n).2 (hsub n) t) (hQ (haI n).2 (hsub n) t))
    have h := actualPaperRealization_of_compact_differences (K:=K) (C:=C) hDensity hSob hC a (fun _ => s)
      ha (fun _ _ _ => le_rfl) (fun n => (haI n).2) (fun t => u t-q t)
      (fun n => U (haI n).2 (hsub n)) (fun n => Q (haI n).2 (hsub n)) hd
      (fun n => hleft (haI n).1 (haI n).2)
    exact hca ▸ h
  have hright' : ActualPaperRealization (I ∩ Ici s) (fun t => u t-q t) (3*C) := by
    have hsub (n : ℕ) : Icc s (b n) ⊆ I := hI.out' hs (hbI n).1
    have hd (n : ℕ) (t : Icc s (b n)) :
        energyPath _ (U (hbI n).2 (hsub n)-Q (hbI n).2 (hsub n)) t=u t-q t := by
      exact (energyPath_sub_apply (intervalMeasure s (b n))
        (U (hbI n).2 (hsub n)) (Q (hbI n).2 (hsub n)) t).trans
        (congrArg₂ (fun x y : EnergyState => x-y)
          (hU (hbI n).2 (hsub n) t) (hQ (hbI n).2 (hsub n) t))
    have h := actualPaperRealization_of_compact_differences (K:=K) (C:=C) hDensity hSob hC (fun _ => s) b
      (fun _ _ _ => le_rfl) hb (fun n => (hbI n).2) (fun t => u t-q t)
      (fun n => U (hbI n).2 (hsub n)) (fun n => Q (hbI n).2 (hsub n)) hd
      (fun n => hright (hbI n).1 (hbI n).2)
    exact hcb ▸ h
  have h := ActualPaperRealization.two_sided hI.measurableSet s _ (3*C) (3*C) hleft' hright'
  simpa only [show 3*C+3*C=6*C from by ring] using h

/-- The literal four-term paper sum for the original actual two state curves. -/
def actualPaperDifferenceSize (I : Set ℝ) (u q : ℝ → EnergyState) : ℝ≥0∞ :=
  mixedNorm (volume.restrict I) volume ∞ 2
    (fun t x => energyComplexGradient (u t) x-energyComplexGradient (q t) x) +
  mixedNorm (volume.restrict I) volume 10 criticalExponent
    (fun t x => energyComplexGradient (u t) x-energyComplexGradient (q t) x) +
  mixedNorm (volume.restrict I) volume 2 6
    (fun t x => energyComplexGradient (u t) x-energyComplexGradient (q t) x) +
  mixedNorm (volume.restrict I) volume 10 10
    (fun t x => energyValue (u t) x-energyValue (q t) x)

theorem actualPaperDifferenceSize_le_of_realization
    {I : Set ℝ} {u q : ℝ → EnergyState} {C : ℝ} (hC : 0 ≤ C)
    (h : ActualPaperRealization I (fun t => u t-q t) C) :
    actualPaperDifferenceSize I u q ≤ ENNReal.ofReal (4*C) := by
  unfold ActualPaperRealization at h
  have bound {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E]
      (ν : Measure X) (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
      (g : ℝ → X → E) (hg : ActualNestedLpBound ν p r I g C) :
      mixedNorm (volume.restrict I) ν p r g ≤ ENNReal.ofReal C := by
    unfold ActualNestedLpBound at hg
    obtain ⟨F,hF,hFa,_⟩ := hg
    exact actual_mixedNorm_le_of_global_nestedLp ν p r I F g hF hFa
  have heq (p r : ℝ≥0∞) : mixedNorm (volume.restrict I) volume p r
      (fun t x => energyComplexGradient (u t) x-energyComplexGradient (q t) x) =
      mixedNorm (volume.restrict I) volume p r (fun t => energyComplexGradient (u t-q t)) := by
    apply eLpNorm_congr_ae
    exact Eventually.of_forall fun t => (eLpNorm_congr_ae (energyComplexGradient_sub_ae (u t) (q t))).symm
  have hseq : mixedNorm (volume.restrict I) volume 10 10
      (fun t x => energyValue (u t) x-energyValue (q t) x) =
      mixedNorm (volume.restrict I) volume 10 10 (fun t => energyValue (u t-q t)) := by
    apply eLpNorm_congr_ae
    exact Eventually.of_forall fun t => (eLpNorm_congr_ae (energyValue_sub_ae (u t) (q t))).symm
  let : Fact ((1 : ℝ≥0∞) ≤ ∞) := ⟨le_top⟩
  unfold actualPaperDifferenceSize
  rw [heq,heq,heq,hseq]
  apply (add_le_add (add_le_add (add_le_add
    (bound volume ∞ 2 _ h.1) (bound volume 10 criticalExponent _ h.2.1))
    (bound volume 2 6 _ h.2.2.1)) (bound volume 10 10 _ h.2.2.2)).trans_eq
  rw [← ENNReal.ofReal_add hC hC,
    ← ENNReal.ofReal_add (add_nonneg hC hC) hC,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg hC hC) hC) hC]
  congr 1
  ring

#print axioms ActualPaperRealization.two_sided
#print axioms actualPaperRealization_of_anchored_compact_differences
#print axioms actualPaperDifferenceSize_le_of_realization
end HartreeF.IntervalNormExhaustion
