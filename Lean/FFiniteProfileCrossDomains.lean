import FGeneralMixedDomains

/-! Every-index domains for the genuine pure cross terms. The later orthogonality
limits alone would not imply these domains at every original index. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.FiniteProfileCrossDomains
open ForcingDomain TimeHolder GeneralProfileCross CompactCross CrossContinuity

private theorem zero_profile : ScalarProfile (0 : ℝ → Space → ℂ) 0 := by
  refine ⟨stronglyMeasurable_const, stronglyMeasurable_const, ?_, ?_, ?_⟩ <;>
    simp [mixedNorm]

/-- A genuine zero comparison supplies both pure-cross domains from true input
V/S/W domains. It does not infer finite norms from an asymptotic conclusion. -/
theorem scalar_cross_finite {α c : ℝ} (hH : OrdinaryHLS α c)
    {u h v k : ℝ → Space → ℂ} (hu : ScalarProfile u h) (hv : ScalarProfile v k) :
    forcingNorm (innerCross α c u h v) ≠ ∞ ∧
      forcingNorm (outerCross α c u v k) ≠ ∞ := by
  have hz := zero_profile
  have hJ := hu.jointInputs hz hv hz
  have hSlices := hu.sliceInputs hz hv hz
  let V := mixedNorm volume volume ∞ 6 u + mixedNorm volume volume ∞ 6 v
  let S := mixedNorm volume volume 10 10 u + mixedNorm volume volume 10 10 v
  let W := mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) h +
    mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) k
  have hV : V ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hu.value_V, hv.value_V⟩
  have hS : S ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hu.value_S, hv.value_S⟩
  have hW : W ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hu.gradient_W, hv.gradient_W⟩
  have hTotal : V + S + W ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hV, hS⟩, hW⟩
  let M : ℝ≥0 := (V + S + W).toNNReal
  have hM : (M : ℝ≥0∞) = V + S + W := ENNReal.coe_toNNReal hTotal
  have hVM : V ≤ (M : ℝ≥0∞) := by
    rw [hM]
    exact (le_add_right le_rfl).trans (le_add_right le_rfl)
  have hSM : S ≤ (M : ℝ≥0∞) := by
    rw [hM]
    exact (le_add_left le_rfl).trans (le_add_right le_rfl)
  have hWM : W ≤ (M : ℝ≥0∞) := by
    rw [hM]
    exact le_add_left le_rfl
  obtain ⟨C, hC⟩ := separate_cross_bounded_continuity hH
  have he := hC u 0 h 0 v 0 k 0 hJ hSlices M M
    (by simpa [valueSize, mixedNorm, V] using hVM)
    (by simpa [valueSize, mixedNorm, S] using hSM)
    (by simp [referenceSize, mixedNorm])
    (by simpa [changeSize, S] using hSM)
    (by simpa [changeSize, W] using hWM)
  have hi0 : innerCross α c (0 : ℝ → Space → ℂ) 0 0 = 0 := by
    funext t x
    simp [innerCross, WeakHartreeChain.localFactor]
  have ho0 : outerCross α c (0 : ℝ → Space → ℂ) 0 0 = 0 := by
    funext t x
    simp [outerCross]
  exact ⟨by simpa only [hi0, sub_zero] using he.1,
    by simpa only [ho0, sub_zero] using he.2.1⟩

end HartreeF.FiniteProfileCrossDomains
