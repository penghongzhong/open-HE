import FLocalFreePathCaps

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.FreeDataDependence
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest ActualStrichartz
local instance canonicalEnergyNormedSpace : NormedSpace ℂ EnergyState :=
  Submodule.normedSpace (𝕜 := ℂ) (R := ℂ) (E := EnergyAmbient) energySubmodule
local instance canonicalPathNormedSpace (a b : ℝ) :
    NormedSpace ℂ (CriticalPath (intervalMeasure a b)) :=
  Submodule.normedSpace (𝕜 := ℂ) (R := ℂ) (E := PathAmbient (intervalMeasure a b))
    (criticalPathSubmodule (intervalMeasure a b))
attribute [local irreducible] energySubmodule criticalPathSubmodule freeCriticalPath
  energyPath criticalGradient freeEnergyState

/-- Additivity holds for the full actual graph path. -/
theorem actual_freeCriticalPath_add (hDensity : OrdinaryH1Density) {K Ch : ℝ}
    (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (a b : ℝ) (u0 v0 : EnergyState) :
    freeCriticalPath hDensity hSob hfree a b (u0 + v0) =
      freeCriticalPath hDensity hSob hfree a b u0 +
      freeCriticalPath hDensity hSob hfree a b v0 := by
  apply energyPath_injective (intervalMeasure a b)
  apply ContinuousMap.ext
  intro t
  let f := freeCriticalPath hDensity hSob hfree a b
  let L := energyPath (intervalMeasure a b)
  have hm : L (f u0 + f v0) t = L (f u0) t + L (f v0) t :=
    congrArg (fun g : C(Set.Icc a b, EnergyState) => g t) (L.map_add (f u0) (f v0))
  exact (freeCriticalPath_energy hDensity hSob hfree a b (u0 + v0) t).trans
    ((freeEnergyState_add hDensity hSob t u0 v0).trans
      ((congrArg₂ (fun x y : EnergyState => x + y)
        (freeCriticalPath_energy hDensity hSob hfree a b u0 t).symm
        (freeCriticalPath_energy hDensity hSob hfree a b v0 t).symm).trans hm.symm))

/-- Complex scalar compatibility holds for the full actual graph path. -/
theorem actual_freeCriticalPath_smul (hDensity : OrdinaryH1Density) {K Ch : ℝ}
    (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (a b : ℝ) (z : ℂ) (u0 : EnergyState) :
    freeCriticalPath hDensity hSob hfree a b (z • u0) =
      z • freeCriticalPath hDensity hSob hfree a b u0 := by
  apply energyPath_injective (intervalMeasure a b)
  apply ContinuousMap.ext
  intro t
  let f := freeCriticalPath hDensity hSob hfree a b
  let L := energyPath (intervalMeasure a b)
  have hm : L (z • f u0) t = z • L (f u0) t :=
    congrArg (fun g : C(Set.Icc a b, EnergyState) => g t) (L.map_smul z (f u0))
  exact (freeCriticalPath_energy hDensity hSob hfree a b (z • u0) t).trans
    ((freeEnergyState_smul hDensity hSob t z u0).trans
      ((congrArg (fun x : EnergyState => z • x)
        (freeCriticalPath_energy hDensity hSob hfree a b u0 t).symm).trans hm.symm))

/-- The prescribed datum is attained exactly at the left endpoint. -/
theorem actual_shiftedFreeCriticalPath_initial (hDensity : OrdinaryH1Density)
    {K Ch a b : ℝ} (hSob : OrdinarySobolev K)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hab : a ≤ b) (u0 : EnergyState) :
    energyPath _ (freeCriticalPath hDensity hSob hfree a b
      (freeEnergyState hDensity hSob (-a) u0)) ⟨a, le_rfl, hab⟩ = u0 :=
  shiftedFreeCriticalPath_initial hDensity hSob hfree hab u0

/-- Subtraction for the actual Fourier free path follows from the energy
projection's injectivity, hence includes equality of all graph coordinates. -/
theorem actual_freeCriticalPath_sub (hDensity : OrdinaryH1Density) {K Ch : ℝ}
    (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (a b : ℝ) (u0 v0 : EnergyState) :
    freeCriticalPath hDensity hSob hfree a b (u0-v0) =
      freeCriticalPath hDensity hSob hfree a b u0 -
      freeCriticalPath hDensity hSob hfree a b v0 := by
  apply energyPath_injective (intervalMeasure a b)
  apply ContinuousMap.ext
  intro t
  let f := freeCriticalPath hDensity hSob hfree a b
  let L := energyPath (intervalMeasure a b)
  have hm : L (f u0 - f v0) t = L (f u0) t - L (f v0) t :=
    congrArg (fun g : C(Set.Icc a b, EnergyState) => g t) (L.map_sub (f u0) (f v0))
  exact (freeCriticalPath_energy hDensity hSob hfree a b (u0 - v0) t).trans
    ((freeEnergyState_sub hDensity hSob t u0 v0).trans
      ((congrArg₂ (fun x y : EnergyState => x - y)
        (freeCriticalPath_energy hDensity hSob hfree a b u0 t).symm
        (freeCriticalPath_energy hDensity hSob hfree a b v0 t).symm).trans hm.symm))

/-- Exact shifted free difference, for arbitrary homogeneous-energy data. -/
theorem actual_shiftedFreeCriticalPath_sub (hDensity : OrdinaryH1Density) {K Ch : ℝ}
    (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (a b : ℝ) (u0 v0 : EnergyState) :
    freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) u0) -
      freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) v0) =
    freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) (u0-v0)) := by
  exact ((congrArg (freeCriticalPath hDensity hSob hfree a b)
    (freeEnergyState_sub hDensity hSob (-a) u0 v0)).trans
      (actual_freeCriticalPath_sub hDensity hSob hfree a b
        (freeEnergyState hDensity hSob (-a) u0)
        (freeEnergyState hDensity hSob (-a) v0))).symm

/-- Actual E+W free bound with an interval-independent linear constant.
The W estimate uses KT(5) and the literal free gradient's L2 unitarity. -/
theorem actual_shiftedFreeCriticalPath_norm_le (hDensity : OrdinaryH1Density) {K Ch : ℝ}
    (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (a b : ℝ) (u0 : EnergyState) :
    ‖freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) u0)‖ ≤
      max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖u0‖ := by
  rw [criticalPath_norm]
  apply max_le
  · exact (shiftedFreeCriticalPath_energy_norm_le hDensity hSob hfree a b u0).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    have hg : ‖energyGradient j (freeEnergyState hDensity hSob (-a) u0)‖ ≤ ‖u0‖ := by
      rw [freeEnergyState_gradient, FreeFlow.freeL2_norm]
      exact energyState_gradient_norm_le u0 j
    have hbound : ‖criticalGradient (intervalMeasure a b) j
        (freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) u0))‖ ≤
        Ch * ‖energyGradient j (freeEnergyState hDensity hSob (-a) u0)‖ := by
      apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hfree.1 (norm_nonneg _))).mp
      simpa only [ofReal_norm] using freeCriticalPath_gradient_bound hDensity hSob hfree
        a b (freeEnergyState hDensity hSob (-a) u0) j
    exact hbound.trans ((mul_le_mul_of_nonneg_left hg hfree.1).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)))

/-- The free-path difference estimate is proved on the actual path objects;
no continuity or Lipschitz estimate is imported as an extra premise. -/
theorem actual_shiftedFreeCriticalPath_difference_norm (hDensity : OrdinaryH1Density)
    {K Ch : ℝ} (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (a b : ℝ) (u0 v0 : EnergyState) :
    ‖freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) u0) -
      freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) v0)‖ ≤
      max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖u0-v0‖ := by
  rw [actual_shiftedFreeCriticalPath_sub]
  exact actual_shiftedFreeCriticalPath_norm_le hDensity hSob hfree a b (u0-v0)

/-- The literal shifted free path, packaged as a bounded complex linear map.
Its bound was derived above from the actual E and W projections. -/
def actual_shiftedFreeCriticalPathCLM (hDensity : OrdinaryH1Density) {K Ch : ℝ}
    (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (a b : ℝ) : EnergyState →L[ℂ] CriticalPath (intervalMeasure a b) :=
  LinearMap.mkContinuous
    { toFun := fun u0 => freeCriticalPath hDensity hSob hfree a b
        (freeEnergyState hDensity hSob (-a) u0)
      map_add' := by
        intro u0 v0
        exact (congrArg (freeCriticalPath hDensity hSob hfree a b)
          (freeEnergyState_add hDensity hSob (-a) u0 v0)).trans
            (actual_freeCriticalPath_add hDensity hSob hfree a b
              (freeEnergyState hDensity hSob (-a) u0)
              (freeEnergyState hDensity hSob (-a) v0))
      map_smul' := by
        intro z u0
        change freeCriticalPath hDensity hSob hfree a b
          (freeEnergyState hDensity hSob (-a) (z • u0)) =
          z • freeCriticalPath hDensity hSob hfree a b
            (freeEnergyState hDensity hSob (-a) u0)
        exact (congrArg (freeCriticalPath hDensity hSob hfree a b)
          (freeEnergyState_smul hDensity hSob (-a) z u0)).trans
            (actual_freeCriticalPath_smul hDensity hSob hfree a b z
              (freeEnergyState hDensity hSob (-a) u0)) }
    (max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch)
    (actual_shiftedFreeCriticalPath_norm_le hDensity hSob hfree a b)

@[simp] theorem actual_shiftedFreeCriticalPathCLM_apply
    (hDensity : OrdinaryH1Density) {K Ch : ℝ}
    (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (a b : ℝ) (u0 : EnergyState) :
    actual_shiftedFreeCriticalPathCLM hDensity hSob hfree a b u0 =
      freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) u0) := rfl

end HartreeF.FreeDataDependence
