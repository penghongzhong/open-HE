import FHomogeneousStabilityNorms

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

theorem criticalExponent_eq_thirty_thirteenths :
    criticalExponent = (30/13 : ℝ≥0∞) := by
  change ENNReal.ofReal ((30 : ℝ)/13) = _
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 13)]
  norm_num

theorem energyComplexGradient_memLp_two (u : EnergyState) :
    MemLp (energyComplexGradient u) 2 (volume : Measure Space) := by
  rw [energyComplexGradient_eq_sum]
  apply memLp_finsetSum
  intro j _
  exact (Lp.memLp (energyGradient j u)).continuousLinearMap_comp
    (ContinuousLinearMap.toSpanSingleton ℂ
      (PiLp.single 2 j (1 : ℂ) : EuclideanSpace ℂ (Fin 3)))

/-- The paper's genuine Euclidean gradient L2 norm is exactly the native
pure homogeneous energy norm, rather than a coordinate maximum. -/
theorem energyComplexGradient_L2_eq_pure (u : EnergyState) :
    eLpNorm (energyComplexGradient u) 2 volume = ENNReal.ofReal (pureGradientNorm u) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
    (energyComplexGradient_memLp_two u)]
  have hk : (∫ x, ‖energyComplexGradient u x‖^2) = gradientSquared u :=
    state_kinetic_eq_gradientSquared u
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, hk, pureGradientNorm,
    Real.sqrt_eq_rpow]
  norm_num

/-- Coordinate W smallness follows with constant 1 from actual Euclidean W
smallness. In particular, no contraction W threshold is enlarged. -/
theorem criticalGradient_coordinate_le_actual_W {a b : ℝ}
    (u : CriticalPath (intervalMeasure a b)) (j : Fin 3) :
    ENNReal.ofReal ‖criticalGradient (intervalMeasure a b) j u‖ ≤
      mixedNorm (intervalMeasure a b) volume 10 criticalExponent
        (fun t => energyComplexGradient (energyPath _ u t)) := by
  have heq : ENNReal.ofReal ‖criticalGradient (intervalMeasure a b) j u‖ =
      eLpNorm (fun t => eLpNorm (energyGradient j (energyPath _ u t))
        criticalExponent volume) 10 (intervalMeasure a b) :=
    (ofReal_norm _).trans (criticalGradient_eLpNorm (intervalMeasure a b) u j).symm
  apply heq.le.trans
  apply eLpNorm_mono_enorm_ae
    (criticalGradient_norm_profile_memLp (intervalMeasure a b) u j).aestronglyMeasurable
  filter_upwards [] with t
  simp only [enorm_eq_self]
  apply eLpNorm_mono (Lp.aestronglyMeasurable _)
  intro x
  rw [← energyComplexGradient_coordinate]
  exact PiLp.norm_apply_le _ j

theorem criticalGradient_norm_le_of_actual_W_cap {a b R : ℝ}
    (u : CriticalPath (intervalMeasure a b)) (hR : 0 ≤ R)
    (hcap : mixedNorm (intervalMeasure a b) volume 10 criticalExponent
      (fun t => energyComplexGradient (energyPath _ u t)) ≤ ENNReal.ofReal R) :
    ‖fun j => criticalGradient (intervalMeasure a b) j u‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro j
  exact (ENNReal.ofReal_le_ofReal_iff hR).mp
    ((criticalGradient_coordinate_le_actual_W u j).trans hcap)

/-- Reverse graph control from the actual homogeneous energy and Euclidean W
caps. Both bounds concern this same path, with no assumed norm equivalence. -/
theorem criticalPath_norm_le_of_paper_caps {K B R a b : ℝ}
    (hSob : OrdinarySobolev K) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (u : CriticalPath (intervalMeasure a b))
    (hE : ∀ t, pureGradientNorm (energyPath _ u t) ≤ B)
    (hW : mixedNorm (intervalMeasure a b) volume 10 criticalExponent
      (fun t => energyComplexGradient (energyPath _ u t)) ≤ ENNReal.ofReal R) :
    ‖u‖ ≤ max (max (K^((6 : ℝ)⁻¹)) 1 * B) R := by
  rw [criticalPath_norm]
  exact max_le_max (energyPath_norm_le_of_pure_cap hSob hB u hE)
    (criticalGradient_norm_le_of_actual_W_cap u hR hW)

/-- The actual L-infinity-time, L2-space vector-gradient energy. This forward
bound is valid also for singleton and empty intervals; no full-support premise. -/
theorem actual_complex_energy_le_sqrt_three_graph {a b : ℝ}
    (u : CriticalPath (intervalMeasure a b)) :
    mixedNorm (intervalMeasure a b) volume ∞ 2
      (fun t => energyComplexGradient (energyPath _ u t)) ≤
        ENNReal.ofReal (Real.sqrt 3 * ‖u‖) := by
  have hm := spatial_lp_time_measurable (intervalMeasure a b) volume 2
    (by norm_num) (by norm_num) (jointComplexGradient u) (jointComplexGradient_joint u)
  have he : mixedNorm (intervalMeasure a b) volume ∞ 2
      (fun t => energyComplexGradient (energyPath _ u t)) =
      mixedNorm (intervalMeasure a b) volume ∞ 2 (jointComplexGradient u) := by
    apply eLpNorm_congr_ae
    filter_upwards [jointComplexGradient_slice_eq u] with t ht
    exact eLpNorm_congr_ae ht.symm
  rw [he]
  apply (eLpNorm_exponent_top hm).le.trans
  apply eLpNormEssSup_le_of_ae_enorm_bound
  filter_upwards [jointComplexGradient_slice_eq u] with t ht
  simp only [enorm_eq_self]
  rw [eLpNorm_congr_ae ht, energyComplexGradient_L2_eq_pure]
  exact ENNReal.ofReal_le_ofReal
    ((pureGradient_le_sqrt_three_energyState _).trans
      (mul_le_mul_of_nonneg_left (energyPath_value_norm_le _ u t) (Real.sqrt_nonneg _)))

theorem actual_complex_difference_energy_le_sqrt_three_graph {a b : ℝ}
    (u q : CriticalPath (intervalMeasure a b)) :
    mixedNorm (intervalMeasure a b) volume ∞ 2
      (fun t x => energyComplexGradient (energyPath _ u t) x -
        energyComplexGradient (energyPath _ q t) x) ≤
        ENNReal.ofReal (Real.sqrt 3 * ‖u-q‖) := by
  rw [actual_complex_difference_mixedNorm_eq_at]
  exact actual_complex_energy_le_sqrt_three_graph (u-q)

/-- The literal sum E + W + endpoint + S used in the paper. Every field is
evaluated on the same actual u and q. -/
def paperZSDifferenceSize {a b : ℝ} (u q : CriticalPath (intervalMeasure a b)) : ℝ≥0∞ :=
  mixedNorm (intervalMeasure a b) volume ∞ 2
    (fun t x => energyComplexGradient (energyPath _ u t) x -
      energyComplexGradient (energyPath _ q t) x) +
  mixedNorm (intervalMeasure a b) volume 10 criticalExponent
    (fun t x => energyComplexGradient (energyPath _ u t) x -
      energyComplexGradient (energyPath _ q t) x) +
  mixedNorm (intervalMeasure a b) volume 2 6
    (fun t x => energyComplexGradient (energyPath _ u t) x -
      energyComplexGradient (energyPath _ q t) x) +
  mixedNorm (intervalMeasure a b) volume 10 10
    (fun t x => energyValue (energyPath _ u t) x -
      energyValue (energyPath _ q t) x)

/-- A quantitative consumer of the accepted graph-plus-endpoint-plus-S bound.
The constant is explicit; no solution, forcing, or source premise is added. -/
theorem paperZSDifferenceSize_le_of_fullZS {a b R : ℝ}
    (u q : CriticalPath (intervalMeasure a b)) (hR : 0 ≤ R)
    (h : fullZSDifferenceSize u q ≤ ENNReal.ofReal R) :
    paperZSDifferenceSize u q ≤ ENNReal.ofReal ((Real.sqrt 3+4)*R) := by
  have hg := graph_difference_le_of_fullZS u q hR h
  have he := (actual_complex_difference_energy_le_sqrt_three_graph u q).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hg (Real.sqrt_nonneg _)))
  have hw : mixedNorm (intervalMeasure a b) volume 10 criticalExponent
      (fun t x => energyComplexGradient (energyPath _ u t) x -
        energyComplexGradient (energyPath _ q t) x) ≤ ENNReal.ofReal (3*R) := by
    rw [actual_complex_difference_mixedNorm_eq_at]
    exact (actual_complex_W_le_three_graph (u-q)).trans
      ((mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hg)).trans_eq
        (by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat]))
  have hps : mixedNorm (intervalMeasure a b) volume 2 6
      (fun t x => energyComplexGradient (energyPath _ u t) x -
        energyComplexGradient (energyPath _ q t) x) +
      mixedNorm (intervalMeasure a b) volume 10 10
        (fun t x => energyValue (energyPath _ u t) x -
          energyValue (energyPath _ q t) x) ≤ ENNReal.ofReal R := by
    apply le_trans _ h
    exact add_le_add (le_add_of_nonneg_left
      (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal ‖u-q‖ from bot_le)) le_rfl
  have hadd (x y z w X Y Z : ℝ≥0∞) (hx : x ≤ X) (hy : y ≤ Y) (hz : z+w ≤ Z) :
      x+y+z+w ≤ (X+Y)+Z := by
    rw [add_assoc (x+y)]
    exact add_le_add (add_le_add hx hy) hz
  apply (hadd _ _ _ _ _ _ _ he hw hps).trans_eq
  rw [← ENNReal.ofReal_add (mul_nonneg (Real.sqrt_nonneg _) hR) (by positivity),
    ← ENNReal.ofReal_add (by positivity) hR]
  congr 1
  ring

/-- The output conversion for the usual C epsilon bound, retaining the
stronger pointwise energy conclusion needed for compact-interval iteration. -/
theorem paper_stability_bounds_of_fullZS {a b C ε : ℝ}
    (u q : CriticalPath (intervalMeasure a b)) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (h : fullZSDifferenceSize u q ≤ ENNReal.ofReal (C*ε)) :
    (∀ t, pureGradientNorm (energyPath _ (u-q) t) ≤ (Real.sqrt 3*C)*ε) ∧
    paperZSDifferenceSize u q ≤ ENNReal.ofReal (((Real.sqrt 3+4)*C)*ε) := by
  constructor
  · intro t
    exact (pureGradient_difference_le_sqrt_three_graph u q t).trans
      ((mul_le_mul_of_nonneg_left (graph_difference_le_of_fullZS u q (mul_nonneg hC hε) h)
        (Real.sqrt_nonneg _)).trans_eq (by ring))
  · simpa only [mul_assoc] using paperZSDifferenceSize_le_of_fullZS u q (mul_nonneg hC hε) h

end HartreeF.HomogeneousStability
