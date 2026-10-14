import FIntervalRetardedPathDifference

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology
namespace HartreeF.ActualDuhamelPath
open CriticalPathSpace IntervalTimeTransport EnergySpace LocalScalarSource ForcingDomain
open SobolevStretch StationarySelfTest Retarded ActualStrichartz
attribute [local irreducible] criticalPathIntervalSource intervalRetardedCriticalPath
  freeCriticalPath criticalPathOfGlobalFields CriticalJointSources.jointFields hartreeDuhamelMap
  energyPath energyDistribution criticalGradient


local instance canonicalEnergyNormedSpace : NormedSpace ℂ EnergyState :=
  Submodule.normedSpace (𝕜 := ℂ) (R := ℂ) (E := EnergyAmbient) energySubmodule
local instance canonicalPathNormedSpace (a b : ℝ) :
    NormedSpace ℂ (CriticalPath (intervalMeasure a b)) :=
  Submodule.normedSpace (𝕜 := ℂ) (R := ℂ) (E := PathAmbient (intervalMeasure a b))
    (criticalPathSubmodule (intervalMeasure a b))

attribute [local irreducible] energySubmodule criticalPathSubmodule

/-- The canonical inherited energy norm has not been replaced by a scalar-action instance. -/
theorem canonicalEnergy_norm_unchanged (u : EnergyState) :
    ‖u‖ = max ‖u.val.1‖ ‖u.val.2‖ := rfl

/-- The canonical inherited path norm is still the original E+W product maximum. -/
theorem canonicalPath_norm_unchanged {a b : ℝ} (u : CriticalPath (intervalMeasure a b)) :
    ‖u‖ = max ‖energyPath _ u‖ ‖fun j => criticalGradient _ j u‖ :=
  criticalPath_norm (intervalMeasure a b) u

section Abstract
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem complexUnit_norm (x : E) : ‖Complex.I • x‖ = ‖x‖ := by
  rw [norm_smul, Complex.norm_I, one_mul]

theorem complexIncrement_norm (x y : E) : ‖x + Complex.I • y - x‖ = ‖y‖ := by
  rw [add_sub_cancel_left, complexUnit_norm]

theorem complexIncrement_add_norm (x y : E) :
    ‖x + Complex.I • y‖ ≤ ‖x‖ + ‖y‖ := by
  simpa only [complexUnit_norm] using norm_add_le x (Complex.I • y)

theorem complexIncrement_sub (x y z : E) :
    (x + Complex.I • y) - (x + Complex.I • z) = Complex.I • (y-z) := by
  rw [add_sub_add_left_eq_sub, smul_sub]

theorem complexIncrement_map_norm (L : E →L[ℂ] F) (x y : E) :
    ‖L (x + Complex.I • y)‖ ≤ ‖L x‖ + ‖L y‖ := by
  rw [map_add, map_smul]
  exact complexIncrement_add_norm (L x) (L y)

theorem complexUnit_map_norm (L : E →L[ℂ] F) (x : E) :
    ‖L (Complex.I • x)‖ = ‖L x‖ := by
  rw [map_smul, complexUnit_norm]

theorem complexUnit_map_eval {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (L : E →L[ℂ] C(T,F)) (D : F →L[ℂ] ℂ) (x : E) (t : T) :
    D (L (Complex.I • x) t) = Complex.I * D (L x t) := by
  simp only [map_smul, ContinuousMap.smul_apply, smul_eq_mul]
theorem complexIncrement_curve_norm {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (f g h : C(T,E)) (B : ℝ) (hB : 0 ≤ B) (hh : ‖h‖ ≤ B)
    (he : ∀ t, f t = g t + Complex.I • h t) : ‖f‖ ≤ ‖g‖ + B := by
  apply (ContinuousMap.norm_le f (add_nonneg (norm_nonneg g) hB)).mpr
  intro t
  rw [he t]
  exact (complexIncrement_add_norm (g t) (h t)).trans
    (add_le_add (g.norm_coe_le_norm t) ((h.norm_coe_le_norm t).trans hh))
end Abstract

/-- The existing energy projection preserves scalar multiplication at each time. -/
theorem criticalPath_energy_smul_apply {a b : ℝ} (c : ℂ)
    (u : CriticalPath (intervalMeasure a b)) (t : Set.Icc a b) :
    energyPath _ (c • u) t = c • energyPath _ u t := by
  exact congrArg (fun f : C(Set.Icc a b, EnergyState) => f t)
    ((energyPath (intervalMeasure a b)).map_smul c u)

/-- The existing energy projection preserves addition at each time. -/
theorem criticalPath_energy_add_apply {a b : ℝ}
    (u v : CriticalPath (intervalMeasure a b)) (t : Set.Icc a b) :
    energyPath _ (u + v) t = energyPath _ u t + energyPath _ v t := by
  exact congrArg (fun f : C(Set.Icc a b, EnergyState) => f t)
    ((energyPath (intervalMeasure a b)).map_add u v)

/-- The genuine nonlinear increment is bounded in the full E+W norm. -/
theorem hartreeDuhamelMap_sub_free_norm (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (u0 : EnergyState)
    (u : CriticalPath (intervalMeasure a b)) :
    ‖hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u -
      freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) u0)‖ ≤
      max (energyEndpointConstant K C0) Cr *
        ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖ := by
  let f := freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) u0)
  let r := intervalRetardedCriticalPath hDensity hSob h0 hret
    (criticalPathIntervalSource hDensity hSob hH hab u 0)
  unfold hartreeDuhamelMap
  change ‖f + Complex.I • r - f‖ ≤ _
  exact (complexIncrement_norm f r).le.trans
    (intervalRetardedCriticalPath_norm hDensity hSob h0 hret _)

/-- An actual-map invariance estimate, with the free term retained explicitly. -/
theorem hartreeDuhamelMap_norm (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (u0 : EnergyState)
    (u : CriticalPath (intervalMeasure a b)) :
    ‖hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u‖ ≤
      ‖freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) u0)‖ +
        max (energyEndpointConstant K C0) Cr *
          ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖ := by
  let f := freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) u0)
  let r := intervalRetardedCriticalPath hDensity hSob h0 hret
    (criticalPathIntervalSource hDensity hSob hH hab u 0)
  unfold hartreeDuhamelMap
  change ‖f + Complex.I • r‖ ≤ ‖f‖ + _
  exact (complexIncrement_add_norm f r).trans
    (add_le_add (le_refl ‖f‖)
      (intervalRetardedCriticalPath_norm hDensity hSob h0 hret
        (criticalPathIntervalSource hDensity hSob hH hab u 0)))

/-- The energy cap keeps the actual free energy supremum separately. -/
theorem hartreeDuhamelMap_energy_norm (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (u0 : EnergyState)
    (u : CriticalPath (intervalMeasure a b)) :
    ‖energyPath _ (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u)‖ ≤
      ‖energyPath _ (freeCriticalPath hDensity hSob hfree a b
        (freeEnergyState hDensity hSob (-a) u0))‖ + energyEndpointConstant K C0 *
          ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖ := by
  let f := freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) u0)
  let r := intervalRetardedCriticalPath hDensity hSob h0 hret
    (criticalPathIntervalSource hDensity hSob hH hab u 0)
  have hr := intervalRetardedCriticalPath_energy_norm hDensity hSob h0 hret
    (criticalPathIntervalSource hDensity hSob hH hab u 0)
  unfold hartreeDuhamelMap
  change ‖energyPath _ (f + Complex.I • r)‖ ≤ ‖energyPath _ f‖ + _
  apply complexIncrement_curve_norm (E := EnergyState)
    (energyPath (intervalMeasure a b) (f + Complex.I • r))
    (energyPath (intervalMeasure a b) f) (energyPath (intervalMeasure a b) r)
    (energyEndpointConstant K C0 *
      ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖)
    (mul_nonneg (energyEndpointConstant_nonneg (K := K) h0)
      (norm_nonneg (criticalPathIntervalSource hDensity hSob hH hab u 0).gradient)) hr
  intro t
  exact (criticalPath_energy_add_apply f (Complex.I • r) t).trans
    (congrArg (fun z : EnergyState => energyPath (intervalMeasure a b) f t + z)
      (criticalPath_energy_smul_apply Complex.I r t))

/-- Each W cap keeps its actual free coordinate separately. -/
theorem hartreeDuhamelMap_gradient_norm (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (u0 : EnergyState)
    (u : CriticalPath (intervalMeasure a b)) (j : Fin 3) :
    ‖criticalGradient _ j (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u)‖ ≤
      ‖criticalGradient _ j (freeCriticalPath hDensity hSob hfree a b
        (freeEnergyState hDensity hSob (-a) u0))‖ + Cr *
          ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient j‖ := by
  let f := freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) u0)
  let r := intervalRetardedCriticalPath hDensity hSob h0 hret
    (criticalPathIntervalSource hDensity hSob hH hab u 0)
  have hr : ‖criticalGradient _ j r‖ ≤
      Cr * ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient j‖ := by
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hret.1 (norm_nonneg _))).mp
    simpa only [ofReal_norm] using intervalRetardedCriticalPath_gradient_bound
      hDensity hSob h0 hret (criticalPathIntervalSource hDensity hSob hH hab u 0) j
  unfold hartreeDuhamelMap
  change ‖criticalGradient _ j (f + Complex.I • r)‖ ≤ ‖criticalGradient _ j f‖ + _
  exact (complexIncrement_map_norm (criticalGradient (intervalMeasure a b) j) f r).trans
    (add_le_add (le_refl ‖criticalGradient _ j f‖) hr)

/-- For the same initial datum the free terms cancel. The remaining identity
uses the proved source subtraction and actual retarded linearity. -/
theorem hartreeDuhamelMap_sub (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (u0 : EnergyState)
    (u v : CriticalPath (intervalMeasure a b)) :
    hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u -
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 v =
        Complex.I • intervalRetardedCriticalPath hDensity hSob h0 hret
          (criticalPathIntervalSource hDensity hSob hH hab u v) := by
  let f := freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) u0)
  let Fu := criticalPathIntervalSource hDensity hSob hH hab u 0
  let Fv := criticalPathIntervalSource hDensity hSob hH hab v 0
  let R : CompatibleIntervalSource a b → CriticalPath (intervalMeasure a b) :=
    intervalRetardedCriticalPath hDensity hSob h0 hret
  have hr : R Fu - R Fv = R (criticalPathIntervalSource hDensity hSob hH hab u v) :=
    (intervalRetardedCriticalPath_sub hDensity hSob h0 hret Fu Fv).symm.trans
      (congrArg R (criticalPathIntervalSource_sub_zero hDensity hSob hH hab u v))
  unfold hartreeDuhamelMap
  change (f + Complex.I • R Fu) - (f + Complex.I • R Fv) = _
  exact (complexIncrement_sub f (R Fu) (R Fv)).trans
    (congrArg (fun x : CriticalPath (intervalMeasure a b) => Complex.I • x) hr)

/-- The output difference is the literal retarded Hartree forcing difference,
with representatives replaced only under the actual Bochner integrals. -/
theorem hartreeDuhamelMap_sub_literal_formula (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (u0 : EnergyState)
    (u v : CriticalPath (intervalMeasure a b)) (t : Set.Icc a b) (φ : FreeFlow.Test) :
    energyDistribution (energyPath _
      (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u -
        hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 v) t) φ =
      Complex.I * ∫ s in Set.Icc a b ∩ Set.Iio (t : ℝ), ∫ x,
        (freeTest ((t : ℝ)-s) φ) x •
          (forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ u) s)) x -
            forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ v) s)) x) := by
  let r := intervalRetardedCriticalPath hDensity hSob h0 hret
    (criticalPathIntervalSource hDensity hSob hH hab u v)
  let D : EnergyState →L[ℂ] ℂ :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).comp energyDistribution
  have hi := complexUnit_map_eval (energyPath (intervalMeasure a b)) D r t
  have hs := intervalRetardedCriticalPath_scalar hDensity hSob h0 hret
    (criticalPathIntervalSource hDensity hSob hH hab u v) t φ
  have hl := localSource_integral_formula (criticalPathIntervalSource hDensity hSob hH hab u v).value
    (fun s x => forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ u) s)) x -
      forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ v) s)) x)
    (criticalPathIntervalSource_value_coeFn hDensity hSob hH hab u v) t φ
  exact (congrArg (fun x : CriticalPath (intervalMeasure a b) =>
    energyDistribution (energyPath _ x t) φ)
    (hartreeDuhamelMap_sub hDensity hSob h0 hfree hret hH hab u0 u v)).trans
      (hi.trans (congrArg (fun z : ℂ => Complex.I * z) (hs.trans hl)))

/-- Full CriticalPath difference bound for the actual nonlinear map. -/
theorem hartreeDuhamelMap_sub_norm (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (u0 : EnergyState)
    (u v : CriticalPath (intervalMeasure a b)) :
    ‖hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u -
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 v‖ ≤
      max (energyEndpointConstant K C0) Cr *
        ‖(criticalPathIntervalSource hDensity hSob hH hab u v).gradient‖ := by
  rw [hartreeDuhamelMap_sub]
  exact (complexUnit_norm (intervalRetardedCriticalPath hDensity hSob h0 hret
    (criticalPathIntervalSource hDensity hSob hH hab u v))).le.trans
      (intervalRetardedCriticalPath_norm hDensity hSob h0 hret _)

/-- The energy cap can retain its own sharp linear constant. -/
theorem hartreeDuhamelMap_sub_energy_norm (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (u0 : EnergyState)
    (u v : CriticalPath (intervalMeasure a b)) :
    ‖energyPath _ (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u -
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 v)‖ ≤
      energyEndpointConstant K C0 *
        ‖(criticalPathIntervalSource hDensity hSob hH hab u v).gradient‖ := by
  let r := intervalRetardedCriticalPath hDensity hSob h0 hret
    (criticalPathIntervalSource hDensity hSob hH hab u v)
  have hr := intervalRetardedCriticalPath_energy_norm hDensity hSob h0 hret
    (criticalPathIntervalSource hDensity hSob hH hab u v)
  rw [hartreeDuhamelMap_sub]
  change ‖energyPath _ (Complex.I • r)‖ ≤ _
  apply (ContinuousMap.norm_le _
    (mul_nonneg (energyEndpointConstant_nonneg h0) (norm_nonneg _))).mpr
  intro t
  rw [criticalPath_energy_smul_apply]
  exact (complexUnit_norm (E := EnergyState) (energyPath _ r t)).le.trans
    (((energyPath _ r).norm_coe_le_norm t).trans hr)

/-- Each actual critical coordinate retains KT(7)'s linear constant. -/
theorem hartreeDuhamelMap_sub_gradient_norm (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (u0 : EnergyState)
    (u v : CriticalPath (intervalMeasure a b)) (j : Fin 3) :
    ‖criticalGradient _ j
      (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u -
        hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 v)‖ ≤
      Cr * ‖(criticalPathIntervalSource hDensity hSob hH hab u v).gradient j‖ := by
  have hr : ‖criticalGradient _ j
      (intervalRetardedCriticalPath hDensity hSob h0 hret
        (criticalPathIntervalSource hDensity hSob hH hab u v))‖ ≤
      Cr * ‖(criticalPathIntervalSource hDensity hSob hH hab u v).gradient j‖ := by
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hret.1 (norm_nonneg _))).mp
    simpa only [ofReal_norm] using intervalRetardedCriticalPath_gradient_bound
      hDensity hSob h0 hret (criticalPathIntervalSource hDensity hSob hH hab u v) j
  rw [hartreeDuhamelMap_sub]
  exact (complexUnit_map_norm (criticalGradient (intervalMeasure a b) j)
    (intervalRetardedCriticalPath hDensity hSob h0 hret
      (criticalPathIntervalSource hDensity hSob hH hab u v))).le.trans hr

/-- A coordinatewise estimate on the already constructed input gradient
source transfers to the entire map, with the exact Pi norm. -/
theorem hartreeDuhamelMap_sub_norm_of_gradient_bound (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b B : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (u0 : EnergyState)
    (u v : CriticalPath (intervalMeasure a b))
    (hB : ∀ j : Fin 3, ‖(criticalPathIntervalSource hDensity hSob hH hab u v).gradient j‖ ≤ B) :
    ‖hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u -
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 v‖ ≤
      max (energyEndpointConstant K C0) Cr * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  exact (hartreeDuhamelMap_sub_norm hDensity hSob h0 hfree hret hH hab u0 u v).trans
    (mul_le_mul_of_nonneg_left ((pi_norm_le_iff_of_nonneg hB0).mpr hB)
      ((energyEndpointConstant_nonneg h0).trans (le_max_left _ _)))

end HartreeF.ActualDuhamelPath
