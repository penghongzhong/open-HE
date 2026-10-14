import FIntervalAdvancedPathLinearity
import FActualHartreeDuhamelDifference
import FBackwardFreePathCaps

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualDuhamelPath
open EnergySpace CriticalPathSpace IntervalTimeTransport Retarded LocalScalarSource ForcingDomain
open SobolevStretch StationarySelfTest ActualStrichartz
local instance backwardEnergyNormedSpace : NormedSpace ℂ EnergyState :=
  Submodule.normedSpace (𝕜 := ℂ) (R := ℂ) (E := EnergyAmbient) energySubmodule
local instance backwardGraphNormedSpace (a b : ℝ) :
    NormedSpace ℂ (CriticalPath (intervalMeasure a b)) :=
  Submodule.normedSpace (𝕜 := ℂ) (R := ℂ) (E := PathAmbient (intervalMeasure a b))
    (criticalPathSubmodule (intervalMeasure a b))
attribute [local irreducible] energySubmodule criticalPathSubmodule criticalPathIntervalSource
  intervalAdvancedCriticalPath energyPath criticalGradient energyDistribution freeCriticalPath

/-- The backward map for i u_t + Δu + N(u) = 0 has coefficient minus i
on the positive future integral. Its source is the literal Hartree source. -/
def backwardHartreeDuhamelMap (hDensity : OrdinaryH1Density) {K C0 Ch Cr alpha c a b : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (ub : EnergyState)
    (u : CriticalPath (intervalMeasure a b)) : CriticalPath (intervalMeasure a b) :=
  freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-b) ub) -
    Complex.I • intervalAdvancedCriticalPath hDensity hSob h0 hfree hret
      (criticalPathIntervalSource hDensity hSob hH hab u 0)

attribute [local irreducible] backwardHartreeDuhamelMap

section Abstract
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
theorem complexDecrement_map_norm (L : E →L[ℂ] G) (x y : E) :
    ‖L (x - Complex.I • y)‖ ≤ ‖L x‖ + ‖L y‖ := by
  rw [map_sub, map_smul]
  simpa only [complexUnit_norm] using norm_sub_le (L x) (Complex.I • L y)
theorem complexDecrement_sub_norm (x y z : E) :
    ‖(x - Complex.I • y) - (x - Complex.I • z)‖ = ‖y-z‖ := by
  rw [sub_sub_sub_cancel_left, ← smul_sub, complexUnit_norm, norm_sub_rev]
theorem complexDecrement_map_eval {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (L : E →L[ℂ] C(T,G)) (D : G →L[ℂ] ℂ) (x y : E) (t : T) :
    D (L (x - Complex.I • y) t) = D (L x t) - Complex.I * D (L y t) := by
  simp only [map_sub, map_smul, ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul]
theorem complexDecrement_curve_eval {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (L : E →L[ℂ] C(T,G)) (x y : E) (t : T) :
    L (x - Complex.I • y) t = L x t - Complex.I • L y t := by
  simp only [map_sub, map_smul, ContinuousMap.sub_apply, ContinuousMap.smul_apply]
theorem complexDecrement_zero_eq (x : E) : x - Complex.I • (0 : E) = x := by
  rw [smul_zero, sub_zero]
theorem complexDecrement_curve_norm {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (f g h : C(T,E)) (B : ℝ) (hB : 0 ≤ B) (hh : ‖h‖ ≤ B)
    (he : ∀ t, f t = g t - Complex.I • h t) : ‖f‖ ≤ ‖g‖ + B := by
  apply (ContinuousMap.norm_le f (add_nonneg (norm_nonneg g) hB)).mpr
  intro t
  rw [he t]
  exact ((norm_sub_le (g t) (Complex.I • h t)).trans_eq
    (congrArg (fun z : ℝ => ‖g t‖ + z) (complexUnit_norm (h t)))).trans
    (add_le_add (g.norm_coe_le_norm t) ((h.norm_coe_le_norm t).trans hh))
end Abstract

theorem backwardHartreeDuhamelMap_terminal (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (ub : EnergyState)
    (u : CriticalPath (intervalMeasure a b)) :
    energyPath _ (backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab ub u)
      ⟨b, hab, le_rfl⟩ = ub := by
  let f := freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-b) ub)
  let r := intervalAdvancedCriticalPath hDensity hSob h0 hfree hret
    (criticalPathIntervalSource hDensity hSob hH hab u 0)
  let t : Set.Icc a b := ⟨b, hab, le_rfl⟩
  have hf : energyPath _ f t = ub := backwardFreeCriticalPath_terminal hDensity hSob hfree hab ub
  have hr : energyPath _ r t = 0 :=
    intervalAdvancedCriticalPath_terminal hDensity hSob h0 hfree hret hab _
  have he := complexDecrement_curve_eval (energyPath (intervalMeasure a b)) f r t
  unfold backwardHartreeDuhamelMap
  change energyPath _ (f - Complex.I • r) t = ub
  exact he.trans ((congrArg₂ (fun x y : EnergyState => x - Complex.I • y) hf hr).trans
    (complexDecrement_zero_eq ub))

/-- The continuous energy coordinate retains the derived true energy constant. -/
theorem backwardHartreeDuhamelMap_energy_norm (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (ub : EnergyState)
    (u : CriticalPath (intervalMeasure a b)) :
    ‖energyPath _ (backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab ub u)‖ ≤
      ‖energyPath _ (freeCriticalPath hDensity hSob hfree a b
        (freeEnergyState hDensity hSob (-b) ub))‖ + energyEndpointConstant K C0 *
          ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖ := by
  let f := freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-b) ub)
  let r := intervalAdvancedCriticalPath hDensity hSob h0 hfree hret
    (criticalPathIntervalSource hDensity hSob hH hab u 0)
  have hr := intervalAdvancedCriticalPath_energy_norm hDensity hSob h0 hfree hret
    (criticalPathIntervalSource hDensity hSob hH hab u 0)
  unfold backwardHartreeDuhamelMap
  change ‖energyPath _ (f - Complex.I • r)‖ ≤ ‖energyPath _ f‖ + _
  apply complexDecrement_curve_norm (E := EnergyState)
    (energyPath (intervalMeasure a b) (f - Complex.I • r))
    (energyPath (intervalMeasure a b) f) (energyPath (intervalMeasure a b) r)
    (energyEndpointConstant K C0 *
      ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖)
    (mul_nonneg (energyEndpointConstant_nonneg (K := K) h0) (norm_nonneg _)) hr
  exact complexDecrement_curve_eval (energyPath (intervalMeasure a b)) f r

/-- Actual sharp W coordinates retain Ch*C0+Cr from the future construction. -/
theorem backwardHartreeDuhamelMap_gradient_norm (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (ub : EnergyState)
    (u : CriticalPath (intervalMeasure a b)) (j : Fin 3) :
    ‖criticalGradient _ j (backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab ub u)‖ ≤
      ‖criticalGradient _ j (freeCriticalPath hDensity hSob hfree a b
        (freeEnergyState hDensity hSob (-b) ub))‖ + (Ch*C0+Cr) *
          ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient j‖ := by
  let f := freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-b) ub)
  let r := intervalAdvancedCriticalPath hDensity hSob h0 hfree hret
    (criticalPathIntervalSource hDensity hSob hH hab u 0)
  unfold backwardHartreeDuhamelMap
  change ‖criticalGradient _ j (f - Complex.I • r)‖ ≤ ‖criticalGradient _ j f‖ + _
  exact (complexDecrement_map_norm (criticalGradient (intervalMeasure a b) j) f r).trans
    (add_le_add (le_refl _) (intervalAdvancedCriticalPath_gradient_norm hDensity hSob h0 hfree hret _ j))

/-- The genuine nonlinear difference is bounded in the original full E+W norm. -/
theorem backwardHartreeDuhamelMap_sub_norm (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (ub : EnergyState)
    (u v : CriticalPath (intervalMeasure a b)) :
    ‖backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab ub u -
      backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab ub v‖ ≤
      max (energyEndpointConstant K C0) (Ch*C0+Cr) *
        ‖(criticalPathIntervalSource hDensity hSob hH hab u v).gradient‖ := by
  let f := freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-b) ub)
  let Fu := criticalPathIntervalSource hDensity hSob hH hab u 0
  let Fv := criticalPathIntervalSource hDensity hSob hH hab v 0
  let R : CompatibleIntervalSource a b → CriticalPath (intervalMeasure a b) :=
    intervalAdvancedCriticalPath hDensity hSob h0 hfree hret
  have hr : R Fu - R Fv = R (criticalPathIntervalSource hDensity hSob hH hab u v) :=
    (intervalAdvancedCriticalPath_sub hDensity hSob h0 hfree hret Fu Fv).symm.trans
      (congrArg R (criticalPathIntervalSource_sub_zero hDensity hSob hH hab u v))
  unfold backwardHartreeDuhamelMap
  change ‖(f - Complex.I • R Fu) - (f - Complex.I • R Fv)‖ ≤ _
  exact ((complexDecrement_sub_norm f (R Fu) (R Fv)).trans (congrArg norm hr)).le.trans
    (intervalAdvancedCriticalPath_norm hDensity hSob h0 hfree hret _)

theorem backwardHartreeDuhamelMap_sub_norm_of_gradient_bound (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b B : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (ub : EnergyState)
    (u v : CriticalPath (intervalMeasure a b))
    (hB : ∀ j : Fin 3, ‖(criticalPathIntervalSource hDensity hSob hH hab u v).gradient j‖ ≤ B) :
    ‖backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab ub u -
      backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab ub v‖ ≤
      max (energyEndpointConstant K C0) (Ch*C0+Cr) * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  exact (backwardHartreeDuhamelMap_sub_norm hDensity hSob h0 hfree hret hH hab ub u v).trans
    (mul_le_mul_of_nonneg_left ((pi_norm_le_iff_of_nonneg hB0).mpr hB)
      ((energyEndpointConstant_nonneg h0).trans (le_max_left _ _)))

/-- Exact scalar formula with the literal Hartree integrand on (t,b]. -/
theorem backwardHartreeDuhamelMap_literal_formula (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (ub : EnergyState)
    (u : CriticalPath (intervalMeasure a b)) (t : Set.Icc a b) (φ : FreeFlow.Test) :
    energyDistribution (energyPath _ (backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab ub u) t) φ =
      FreeFlow.free ((t : ℝ)-b) (energyDistribution ub) φ - Complex.I *
        ∫ s in Set.Ioc (t : ℝ) b, ∫ x,
          (freeTest ((t : ℝ)-s) φ) x •
            forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ u) s)) x := by
  let f := freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-b) ub)
  let r := intervalAdvancedCriticalPath hDensity hSob h0 hfree hret
    (criticalPathIntervalSource hDensity hSob hH hab u 0)
  let D : EnergyState →L[ℂ] ℂ :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).comp energyDistribution
  have he := complexDecrement_map_eval (energyPath (intervalMeasure a b)) D f r t
  have hf : D (energyPath _ f t) = FreeFlow.free ((t : ℝ)-b) (energyDistribution ub) φ := by
    change energyDistribution (energyPath _ f t) φ = _
    rw [freeCriticalPath_energy, ← freeEnergyState_add_time, freeEnergyState_distribution]
    rfl
  have hr := intervalAdvancedCriticalPath_scalar hDensity hSob h0 hfree hret
    (criticalPathIntervalSource hDensity hSob hH hab u 0) t φ
  have hrliteral : D (energyPath _ r t) =
      ∫ s in Set.Ioc (t : ℝ) b, ∫ x,
        (freeTest ((t : ℝ)-s) φ) x •
          forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ u) s)) x := by
    apply hr.trans
    apply integral_congr_ae
    have hsub : Set.Ioc (t : ℝ) b ⊆ Set.Icc a b := fun _ hs => ⟨t.2.1.trans hs.1.le, hs.2⟩
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub
      (criticalPathIntervalSource_single_coeFn hDensity hSob hH hab u)] with s hs
    rw [Lp.toTemperedDistribution_apply]
    exact integral_congr_ae (hs.mono fun x hx => congrArg (fun z : ℂ => (freeTest ((t : ℝ)-s) φ) x • z) hx)
  unfold backwardHartreeDuhamelMap
  change D (energyPath _ (f - Complex.I • r) t) = _
  exact he.trans (congrArg₂ (fun x y : ℂ => x - Complex.I * y) hf hrliteral)

end HartreeF.ActualDuhamelPath
