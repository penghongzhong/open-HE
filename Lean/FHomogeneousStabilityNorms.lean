import FActualFullZForcingPerturbation
import FEnergyGradientTopology

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.HomogeneousStability
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest
open EndpointOutput TimeHolder ActualStrichartz ActualPerturbation
attribute [local instance] canonicalEnergyNormedSpace canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath criticalGradient CriticalJointSources.jointFields

/-- Actual complex vector synthesis at any Banach spatial exponent. -/
theorem energyComplexGradient_spatial_le_sum_at (u : EnergyState)
    {r : ℝ≥0∞} (hr : 1 ≤ r) :
    eLpNorm (energyComplexGradient u) r volume ≤
      ∑ j : Fin 3, eLpNorm (energyGradient j u) r volume := by
  rw [energyComplexGradient_eq_sum]
  calc
    _ ≤ ∑ j : Fin 3, eLpNorm (fun x => energyGradient j u x •
        (PiLp.single 2 j (1 : ℂ) : EuclideanSpace ℂ (Fin 3))) r volume := by
      simpa only [Finset.sum_fn] using
        (eLpNorm_sum_le (μ := (volume : Measure Space))
          (f := fun j : Fin 3 => fun x => energyGradient j u x •
            (PiLp.single 2 j (1 : ℂ) : EuclideanSpace ℂ (Fin 3))) hr)
    _ ≤ _ := Finset.sum_le_sum fun j _ => by
      apply eLpNorm_mono ((Lp.aestronglyMeasurable _).smul_const _)
      intro x
      simp [norm_smul]

private def assembleComplex (z : Space × Space) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 (fun j => (z.1 j : ℂ) + Complex.I * (z.2 j : ℂ))

private theorem assembleComplex_continuous : Continuous assembleComplex := by
  unfold assembleComplex
  fun_prop

/-- A canonical jointly measurable vector representative, from the existing
joint fields of the same path. No extra measurability premise is supplied. -/
def jointComplexGradient {a b : ℝ} (u : CriticalPath (intervalMeasure a b)) :
    Set.Icc a b → Space → EuclideanSpace ℂ (Fin 3) :=
  fun t => complexGradient ((CriticalJointSources.jointFields _ u).U t)
    ((CriticalJointSources.jointFields _ u).V t)

theorem jointComplexGradient_joint {a b : ℝ}
    (u : CriticalPath (intervalMeasure a b)) :
    AEStronglyMeasurable
      (fun tx : Set.Icc a b × Space => jointComplexGradient u tx.1 tx.2)
      ((intervalMeasure a b).prod volume) := by
  exact (assembleComplex_continuous.comp_stronglyMeasurable
    ((CriticalJointSources.jointFields _ u).joint_U.prodMk
      (CriticalJointSources.jointFields _ u).joint_V)).aestronglyMeasurable

theorem jointComplexGradient_slice_eq {a b : ℝ}
    (u : CriticalPath (intervalMeasure a b)) :
    ∀ᵐ t ∂intervalMeasure a b,
      jointComplexGradient u t =ᵐ[volume] energyComplexGradient (energyPath _ u t) := by
  filter_upwards [(CriticalJointSources.jointFields _ u).slice_eq] with t ht
  filter_upwards [ht.2.1, ht.2.2] with x hR hI
  exact congrArg₂ (fun R I : Space => assembleComplex (R, I)) hR hI

/-- Exact spatial AE identity on every time slice, including endpoints. -/
theorem actual_complex_difference_slice_eq {a b : ℝ}
    (u q : CriticalPath (intervalMeasure a b)) (t : Set.Icc a b) :
    energyComplexGradient (energyPath _ (u-q) t) =ᵐ[volume]
      (fun x => energyComplexGradient (energyPath _ u t) x -
        energyComplexGradient (energyPath _ q t) x) := by
  have hp : energyPath (intervalMeasure a b) (u-q) t =
      energyPath (intervalMeasure a b) u t - energyPath (intervalMeasure a b) q t :=
    congrArg (fun f : C(Set.Icc a b, EnergyState) => f t)
      ((energyPath (intervalMeasure a b)).map_sub u q)
  filter_upwards [energyComplexGradient_sub_ae
    (energyPath (intervalMeasure a b) u t) (energyPath (intervalMeasure a b) q t)] with x hx
  exact (congrArg (fun f : EnergyState => energyComplexGradient f x) hp).trans hx

theorem jointComplexGradient_difference_slice_eq {a b : ℝ}
    (u q : CriticalPath (intervalMeasure a b)) :
    ∀ᵐ t ∂intervalMeasure a b, jointComplexGradient (u-q) t =ᵐ[volume]
      (fun x => energyComplexGradient (energyPath _ u t) x -
        energyComplexGradient (energyPath _ q t) x) := by
  filter_upwards [jointComplexGradient_slice_eq (u-q)] with t ht
  exact ht.trans (actual_complex_difference_slice_eq u q t)

/-- Exact norm identity for arbitrary temporal and spatial exponents. -/
theorem actual_complex_difference_mixedNorm_eq_at {a b : ℝ}
    (u q : CriticalPath (intervalMeasure a b)) (p r : ℝ≥0∞) :
    mixedNorm (intervalMeasure a b) volume p r
      (fun t x => energyComplexGradient (energyPath _ u t) x -
        energyComplexGradient (energyPath _ q t) x) =
    mixedNorm (intervalMeasure a b) volume p r
      (fun t => energyComplexGradient (energyPath _ (u-q) t)) := by
  apply eLpNorm_congr_ae
  filter_upwards [] with t
  exact eLpNorm_congr_ae (actual_complex_difference_slice_eq u q t).symm

/-- Generic finite-spatial-exponent assembly, specialized below to the paper W. -/
theorem criticalPath_complex_mixed_le_sum {a b : ℝ}
    (u : CriticalPath (intervalMeasure a b)) {p r : ℝ≥0∞}
    (hp : 1 ≤ p) (hr : 1 ≤ r) (hrtop : r ≠ ∞) :
    mixedNorm (intervalMeasure a b) volume p r
      (fun t => energyComplexGradient (energyPath _ u t)) ≤
      ∑ j : Fin 3, mixedNorm (intervalMeasure a b) volume p r
        (fun t => energyGradient j (energyPath _ u t)) := by
  have hrzero : r ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) hr)
  have hm := spatial_lp_time_measurable (intervalMeasure a b) volume r
    hrzero hrtop (jointComplexGradient u) (jointComplexGradient_joint u)
  have hs : ∀ᵐ t ∂intervalMeasure a b, eLpNorm (jointComplexGradient u t) r volume ≤
      ∑ j : Fin 3, eLpNorm (energyGradient j (energyPath _ u t)) r volume := by
    filter_upwards [jointComplexGradient_slice_eq u] with t ht
    exact (eLpNorm_congr_ae ht).le.trans (energyComplexGradient_spatial_le_sum_at _ hr)
  have he : mixedNorm (intervalMeasure a b) volume p r
      (fun t => energyComplexGradient (energyPath _ u t)) =
      mixedNorm (intervalMeasure a b) volume p r (jointComplexGradient u) := by
    apply eLpNorm_congr_ae
    filter_upwards [jointComplexGradient_slice_eq u] with t ht
    exact eLpNorm_congr_ae ht.symm
  apply he.le.trans
  unfold mixedNorm
  calc
    _ ≤ eLpNorm (fun t => ∑ j : Fin 3,
        eLpNorm (energyGradient j (energyPath _ u t)) r volume) p (intervalMeasure a b) :=
      eLpNorm_mono_enorm_ae hm (by simpa only [enorm_eq_self] using hs)
    _ ≤ _ := by
      simpa only [Finset.sum_fn] using
        (eLpNorm_sum_le (μ := intervalMeasure a b)
          (f := fun j : Fin 3 => fun t =>
            eLpNorm (energyGradient j (energyPath _ u t)) r volume) hp)

/-- Euclidean W uses the actual complex coordinates, so its dimension constant
is 3. This sharpens the existing real-plus-imaginary assembly constant 6. -/
theorem actual_complex_W_le_three_graph {a b : ℝ}
    (u : CriticalPath (intervalMeasure a b)) :
    mixedNorm (intervalMeasure a b) volume 10 criticalExponent
      (fun t => energyComplexGradient (energyPath _ u t)) ≤ 3 * ENNReal.ofReal ‖u‖ := by
  apply (criticalPath_complex_mixed_le_sum u (by norm_num) (by norm_num) (by norm_num)).trans
  calc
    _ = ∑ j : Fin 3, ‖criticalGradient (intervalMeasure a b) j u‖ₑ := by
      simp only [mixedNorm, criticalGradient_eLpNorm]
    _ ≤ ∑ _j : Fin 3, ENNReal.ofReal ‖u‖ := Finset.sum_le_sum fun j _ => by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (criticalGradient_norm_le _ u j)
    _ = _ := by simp

theorem actual_complex_difference_W_le_three_graph {a b : ℝ}
    (u q : CriticalPath (intervalMeasure a b)) :
    mixedNorm (intervalMeasure a b) volume 10 criticalExponent
      (fun t x => energyComplexGradient (energyPath _ u t) x -
        energyComplexGradient (energyPath _ q t) x) ≤ 3 * ENNReal.ofReal ‖u-q‖ := by
  rw [actual_complex_difference_mixedNorm_eq_at]
  exact actual_complex_W_le_three_graph (u-q)

/-- The pure homogeneous energy of the very same path difference. -/
theorem pureGradient_difference_le_sqrt_three_graph {a b : ℝ}
    (u q : CriticalPath (intervalMeasure a b)) (t : Set.Icc a b) :
    pureGradientNorm (energyPath _ (u-q) t) ≤ Real.sqrt 3 * ‖u-q‖ :=
  (pureGradient_le_sqrt_three_energyState _).trans
    (mul_le_mul_of_nonneg_left (energyPath_value_norm_le _ (u-q) t) (Real.sqrt_nonneg _))

/-- A pointwise homogeneous energy cap yields the original continuous graph
energy cap. The nonnegative B hypothesis also covers the empty interval. -/
theorem energyPath_norm_le_of_pure_cap {K B a b : ℝ} (hSob : OrdinarySobolev K)
    (hB : 0 ≤ B) (u : CriticalPath (intervalMeasure a b))
    (hcap : ∀ t, pureGradientNorm (energyPath _ u t) ≤ B) :
    ‖energyPath (intervalMeasure a b) u‖ ≤ max (K^((6 : ℝ)⁻¹)) 1 * B := by
  have hA : 0 ≤ max (K^((6 : ℝ)⁻¹)) 1 := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right _ _)
  apply (ContinuousMap.norm_le _ (mul_nonneg hA hB)).mpr
  intro t
  exact (energyState_le_pureGradient hSob _).trans (mul_le_mul_of_nonneg_left (hcap t) hA)

/-- Initial perturbations require precisely the established Sobolev factor. -/
theorem initial_graph_difference_le_of_pure {K ε : ℝ} (hSob : OrdinarySobolev K)
    (f g : EnergyState) (hsmall : pureGradientNorm (f-g) ≤ ε) :
    ‖f-g‖ ≤ max (K^((6 : ℝ)⁻¹)) 1 * ε :=
  (energyState_le_pureGradient hSob (f-g)).trans
    (mul_le_mul_of_nonneg_left hsmall
      ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right _ _)))

/-- Paper norm bounds for literal paths. The energy conclusion holds at every
time, hence is stronger than its essential-supremum conclusion, even on a singleton. -/
def PaperDifferenceBound {a b : ℝ} (u q : CriticalPath (intervalMeasure a b))
    (R : ℝ) : Prop :=
  (∀ t, pureGradientNorm (energyPath _ (u-q) t) ≤ R) ∧
  mixedNorm (intervalMeasure a b) volume 10 criticalExponent
    (fun t x => energyComplexGradient (energyPath _ u t) x -
      energyComplexGradient (energyPath _ q t) x) ≤ ENNReal.ofReal R ∧
  mixedNorm (intervalMeasure a b) volume 2 6
    (fun t x => energyComplexGradient (energyPath _ u t) x -
      energyComplexGradient (energyPath _ q t) x) ≤ ENNReal.ofReal R ∧
  mixedNorm (intervalMeasure a b) volume 10 10
    (fun t x => energyValue (energyPath _ u t) x -
      energyValue (energyPath _ q t) x) ≤ ENNReal.ofReal R

theorem graph_difference_le_of_fullZS {a b R : ℝ}
    (u q : CriticalPath (intervalMeasure a b)) (hR : 0 ≤ R)
    (h : fullZSDifferenceSize u q ≤ ENNReal.ofReal R) : ‖u-q‖ ≤ R := by
  apply (ENNReal.ofReal_le_ofReal_iff hR).mp
  exact (le_add_of_nonneg_right (bot_le)).trans
    ((le_add_of_nonneg_right (bot_le)).trans h)

/-- The already accepted full-Z+S bound gives all original homogeneous output
bounds without any nonlinear/PDE hypothesis, or any change of the two paths. -/
theorem paperDifferenceBound_of_fullZS {a b R : ℝ}
    (u q : CriticalPath (intervalMeasure a b)) (hR : 0 ≤ R)
    (h : fullZSDifferenceSize u q ≤ ENNReal.ofReal R) :
    PaperDifferenceBound u q (3*R) := by
  have hg := graph_difference_le_of_fullZS u q hR h
  have hs3 : Real.sqrt 3 ≤ 3 := by
    apply (Real.sqrt_le_iff).mpr
    norm_num
  have hR3 : R ≤ 3*R := by linarith only [hR]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    exact (pureGradient_difference_le_sqrt_three_graph u q t).trans
      ((mul_le_mul_of_nonneg_left hg (Real.sqrt_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hs3 hR))
  · exact (actual_complex_difference_W_le_three_graph u q).trans
      ((mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hg)).trans_eq
        (by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat]))
  · have he : mixedNorm (intervalMeasure a b) volume 2 6
        (fun t x => energyComplexGradient (energyPath _ u t) x -
          energyComplexGradient (energyPath _ q t) x) ≤ fullZSDifferenceSize u q :=
      (le_add_of_nonneg_left (bot_le)).trans (le_add_of_nonneg_right (bot_le))
    exact he.trans (h.trans (ENNReal.ofReal_le_ofReal hR3))
  · exact (le_add_of_nonneg_left (bot_le)).trans
      (h.trans (ENNReal.ofReal_le_ofReal hR3))

end HartreeF.HomogeneousStability
