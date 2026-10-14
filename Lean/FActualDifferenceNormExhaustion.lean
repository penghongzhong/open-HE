import FActualVectorGradientExhaustion
import FActualCoherentPathValueExhaustion

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.IntervalNormExhaustion
open EnergySpace CriticalPathSpace CriticalSourceBounds CriticalJointSources
open TimeHolder EndpointOutput HomogeneousStability SobolevStretch StationarySelfTest ActualSTail
open ActualPerturbation
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath jointFields

local instance : Fact ((1 : ℝ≥0∞) ≤ ∞) := ⟨le_top⟩

def ActualNestedLpBound {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (ν : Measure X) (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)] (I : Set ℝ) (g : ℝ → X → E) (C : ℝ) : Prop :=
  ∃ F : Lp (Lp E r ν) p (volume : Measure ℝ), ‖F‖ ≤ C ∧
    (∀ᵐ t ∂volume.restrict I, (F t : X → E) =ᵐ[ν] g t) ∧
    (∀ᵐ t ∂volume, t ∉ I → F t=0)

/-- One state difference, with its actual Euclidean gradient and value in
all four mixed spaces. These are constructed representatives, not norm symbols. -/
def ActualPaperRealization (I : Set ℝ) (d : ℝ → EnergyState) (C : ℝ) : Prop :=
  ActualNestedLpBound volume ∞ 2 I (fun t => energyComplexGradient (d t)) C ∧
  ActualNestedLpBound volume 10 criticalExponent I (fun t => energyComplexGradient (d t)) C ∧
  ActualNestedLpBound volume 2 6 I (fun t => energyComplexGradient (d t)) C ∧
  ActualNestedLpBound volume 10 10 I (fun t => energyValue (d t)) C

theorem pathValueSize_sub_eq_actual {a b : ℝ}
    (u q : CriticalPath (intervalMeasure a b)) :
    pathValueSize (intervalMeasure a b) (u-q) =
      mixedNorm (intervalMeasure a b) volume 10 10
        (fun t x => energyValue (energyPath _ u t) x-energyValue (energyPath _ q t) x) := by
  apply eLpNorm_congr_ae
  filter_upwards [(jointFields _ (u-q)).slice_eq] with t ht
  apply eLpNorm_congr_ae
  have he := energyPath_sub_apply (intervalMeasure a b) u q t
  have hr : (energyValue (energyPath _ (u-q) t) : Space → ℂ) =ᵐ[volume]
      (energyValue (energyPath _ u t-energyPath _ q t) : Space → ℂ) :=
    Eventually.of_forall fun x => congrArg (fun z : EnergyState => energyValue z x) he
  exact ht.1.trans (hr.trans (energyValue_sub_ae _ _))

/-- Uniform genuine compact full-Z+S differences produce global actual
E,W,endpoint,S representatives on the exhausted interval, with explicit factor3. -/
theorem actualPaperRealization_of_compact_differences (hDensity : OrdinaryH1Density)
    {K C : ℝ} (hSob : OrdinarySobolev K) (hC : 0 ≤ C)
    (a b : ℕ → ℝ) (ha : Antitone a) (hb : Monotone b) (hab : ∀ n, a n ≤ b n)
    (d : ℝ → EnergyState)
    (U Q : ∀ n, CriticalPath (intervalMeasure (a n) (b n)))
    (hd : ∀ n (t : Icc (a n) (b n)), energyPath _ (U n-Q n) t=d t)
    (hcap : ∀ n, fullZSDifferenceSize (U n) (Q n) ≤ ENNReal.ofReal C) :
    ActualPaperRealization (⋃ n, Icc (a n) (b n)) d (3*C) := by
  have hC3 : 0 ≤ 3*C := mul_nonneg (by norm_num) hC
  have hpaper (n : ℕ) := paperDifferenceBound_of_fullZS (U n) (Q n) hC (hcap n)
  have hgrad (p r : ℝ≥0∞) (n : ℕ) := actual_complex_difference_mixedNorm_eq_at (U n) (Q n) p r
  have hs3 : Real.sqrt 3 ≤ 3 := by
    apply (Real.sqrt_le_iff).mpr
    norm_num
  have henergy (n : ℕ) : mixedNorm (intervalMeasure (a n) (b n)) volume ∞ 2
      (fun t => energyComplexGradient (energyPath _ (U n-Q n) t)) ≤ ENNReal.ofReal (3*C) :=
    (actual_complex_energy_le_sqrt_three_graph (U n-Q n)).trans
      (ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left
        (graph_difference_le_of_fullZS (U n) (Q n) hC (hcap n))
        (Real.sqrt_nonneg _)).trans (mul_le_mul_of_nonneg_right hs3 hC)))
  have hW (n : ℕ) : mixedNorm (intervalMeasure (a n) (b n)) volume 10 criticalExponent
      (fun t => energyComplexGradient (energyPath _ (U n-Q n) t)) ≤ ENNReal.ofReal (3*C) :=
    (hgrad 10 criticalExponent n).symm.le.trans (hpaper n).2.1
  have hP (n : ℕ) : mixedNorm (intervalMeasure (a n) (b n)) volume 2 6
      (fun t => energyComplexGradient (energyPath _ (U n-Q n) t)) ≤ ENNReal.ofReal (3*C) :=
    (hgrad 2 6 n).symm.le.trans (hpaper n).2.2.1
  have hS (n : ℕ) : pathValueSize (intervalMeasure (a n) (b n)) (U n-Q n) ≤
      ENNReal.ofReal (3*C) := (pathValueSize_sub_eq_actual (U n) (Q n)).le.trans (hpaper n).2.2.2
  let : Fact (criticalExponent ≠ ∞) := ⟨by norm_num⟩
  let : Fact ((6 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  refine ⟨?_,?_,?_,?_⟩
  · exact exists_actual_global_energy_gradient_of_compact hC3 a b ha hb hab d
      (fun n => U n-Q n) hd henergy
  · exact exists_actual_global_vector_gradient_of_compact 10 criticalExponent (by norm_num)
      hC3 a b ha hb hab d (fun n => U n-Q n) hd hW
  · exact exists_actual_global_vector_gradient_of_compact 2 6 (by norm_num)
      hC3 a b ha hb hab d (fun n => U n-Q n) hd hP
  · exact exists_actual_global_value_of_coherent_paths hDensity hSob hC3 a b ha hb hab d
      (fun n => U n-Q n) hd hS

#print axioms pathValueSize_sub_eq_actual
#print axioms actualPaperRealization_of_compact_differences
end HartreeF.IntervalNormExhaustion
