import FLocalMildSourceWindow
import FEndpointSourceReflection
import FLowpassNoWasteTranspose

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory Filter Set
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.OriginalSignedDuhamel
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open MaximalTrajectory CriticalUniqueness HartreeDistributionalBridge
open SobolevStretch StationarySelfTest ForcingDomain Retarded FreeTestBounds MassRecovery
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyDistribution

theorem actual_freeTest_comp (r s : ℝ) (φ : Test) :
    freeTest r (freeTest s φ) = freeTest (r+s) φ := by
  apply SchwartzMap.injective_toLp 2 volume
  simp only [freeTest_eq_freeSchwartz, FreeFlow.freeSchwartz_toL2, FreeFlow.freeL2_add]

theorem actual_freeTest_zero (φ : Test) : freeTest 0 φ = φ := by
  apply SchwartzMap.injective_toLp 2 volume
  change (freeTest 0 φ).toLp 2 volume = φ.toLp 2 volume
  rw [freeTest_eq_freeSchwartz, FreeFlow.freeSchwartz_toL2, FreeFlow.freeL2_zero]

theorem neg_preimage_Icc (t T : ℝ) :
    (Neg.neg : ℝ → ℝ) ⁻¹' Icc (-T) (-t) = Icc t T := by
  ext s
  simp only [mem_preimage, mem_Icc, neg_le_neg_iff]
  exact and_comm

/-- Actual reflection of a finite integral; both endpoints and Jacobian are exact. -/
theorem integral_reflection_Icc (f : ℝ → ℂ) (t T : ℝ) :
    (∫ s in Icc (-T) (-t), f s) = ∫ s in Icc t T, f (-s) := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
    (measurableEmbedding_neg : MeasurableEmbedding (Neg.neg : ℝ → ℝ)) f (Icc (-T) (-t))
  simpa only [neg_preimage_Icc] using h.symm

theorem integrableOn_reflection_Icc (f : ℝ → ℂ) (t T : ℝ)
    (hf : IntegrableOn f (Icc (-T) (-t)) volume) :
    IntegrableOn (fun s => f (-s)) (Icc t T) volume := by
  have h := ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (measurableEmbedding_neg : MeasurableEmbedding (Neg.neg : ℝ → ℝ))).mpr hf
  simpa only [neg_preimage_Icc, Function.comp_def] using h

variable {α c s₀ : ℝ} {u₀ : EnergyState} (U : LocalMildTrajectory α c s₀ u₀)

/-- Genuine terminal rebasing of the original positive-time mild formula. -/
theorem local_mild_terminal_positive {t T : ℝ} (htT : t ≤ T)
    (hI : Icc t T ⊆ U.domain) (φ : Test) :
    energyDistribution (U.state t) φ =
      energyDistribution (U.state T) (freeTest (t-T) φ) - Complex.I *
        ∫ s in Icc t T, ∫ x : V,
          freeTest (t-s) φ x * forcing α c (energyValue (U.state s)) x := by
  have h := local_mild_forward_original U htT hI (freeTest (t-T) φ)
  have hzero : (T-t)+(t-T) = 0 := by ring
  have htime (s : ℝ) : (T-s)+(t-T) = t-s := by ring
  simp only [actual_freeTest_comp, hzero, actual_freeTest_zero, htime] at h
  exact eq_sub_of_add_eq h.symm

/-- Negative orientation is obtained from the original finite mild formula on
[-T,-t] and a genuine time change. It is not a forward PDE claim for a reversed field. -/
theorem local_mild_terminal_negative {t T : ℝ} (htT : t ≤ T)
    (hI : Icc (-T) (-t) ⊆ U.domain) (φ : Test) :
    energyDistribution (U.state (-t)) φ =
      energyDistribution (U.state (-T)) (freeTest (-(t-T)) φ) + Complex.I *
        ∫ s in Icc t T, ∫ x : V,
          freeTest (-(t-s)) φ x * forcing α c (energyValue (U.state (-s))) x := by
  have h := local_mild_forward_original U (neg_le_neg htT) hI φ
  rw [integral_reflection_Icc] at h
  have htime (s : ℝ) : -t - -s = -(t-s) := by ring
  simpa only [htime] using h

/-- The SAME physical original trajectory has the literal signed finite formula
on every admissible finite physical window. No finite Duhamel premise is retained. -/
theorem local_mild_signed_finite {σ t T : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (htT : t ≤ T) (hI : ∀ s ∈ Icc t T, σ*s ∈ U.domain) (φ : Test) :
    energyDistribution (U.state (σ*t)) φ =
      energyDistribution (U.state (σ*T)) (freeTest (σ*(t-T)) φ) +
        noWasteCoefficient σ * ∫ s in Icc t T, ∫ x : V,
          freeTest (σ*(t-s)) φ x * forcing α c (energyValue (U.state (σ*s))) x := by
  rcases hσ with rfl | rfl
  · have h := local_mild_terminal_positive U htT (by intro s hs; simpa only [one_mul] using hI s hs) φ
    simpa only [one_mul, noWasteCoefficient, Complex.ofReal_one, mul_one, sub_eq_add_neg,
      neg_mul] using h
  · have hdom : Icc (-T) (-t) ⊆ U.domain := by
      intro s hs
      have hm : -s ∈ Icc t T := by constructor <;> linarith [hs.1, hs.2]
      simpa only [neg_one_mul, neg_neg] using hI (-s) hm
    have h := local_mild_terminal_negative U htT hdom φ
    simpa only [neg_one_mul, noWasteCoefficient, Complex.ofReal_neg, Complex.ofReal_one,
      mul_neg, mul_one, neg_neg] using h

variable (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
  (hH : OrdinaryHLS α c)

include hDensity hSob hH in
/-- The exact literal scalar domain required by the existing no-waste adapter is
produced for both signs from the same actual local source. -/
theorem local_mild_signed_window_integrable {σ t T : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (htT : t ≤ T) (hI : ∀ s ∈ Icc t T, σ*s ∈ U.domain) (φ : Test) :
    IntegrableOn (fun s => ∫ x : V,
      freeTest (σ*(t-s)) φ x * forcing α c (energyValue (U.state (σ*s))) x) (Icc t T) volume := by
  rcases hσ with rfl | rfl
  · simpa only [one_mul] using local_freeTest_source_integrable U hDensity hSob hH htT
      (by intro s hs; simpa only [one_mul] using hI s hs) t φ
  · have hdom : Icc (-T) (-t) ⊆ U.domain := by
      intro s hs
      have hm : -s ∈ Icc t T := by constructor <;> linarith [hs.1, hs.2]
      simpa only [neg_one_mul, neg_neg] using hI (-s) hm
    have hi := local_freeTest_source_integrable U hDensity hSob hH (neg_le_neg htT) hdom (-t) φ
    have hr := integrableOn_reflection_Icc _ t T hi
    have htime (s : ℝ) : -t - -s = -(t-s) := by ring
    simpa only [neg_one_mul, htime] using hr

end HartreeF.OriginalSignedDuhamel
