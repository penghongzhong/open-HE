import FIntervalAdvancedEnergy
import FCompatibleIntervalSourceLinear
import FIntervalRetardedPathDifference

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualDuhamelPath
open EnergySpace CriticalPathSpace IntervalTimeTransport Retarded
open SobolevStretch StationarySelfTest ActualStrichartz
local instance advancedPathEnergyNormedSpace : NormedSpace ℂ EnergyState :=
  Submodule.normedSpace (𝕜 := ℂ) (R := ℂ) (E := EnergyAmbient) energySubmodule
local instance advancedPathGraphNormedSpace (a b : ℝ) :
    NormedSpace ℂ (CriticalPath (intervalMeasure a b)) :=
  Submodule.normedSpace (𝕜 := ℂ) (R := ℂ) (E := PathAmbient (intervalMeasure a b))
    (criticalPathSubmodule (intervalMeasure a b))
attribute [local irreducible] energySubmodule criticalPathSubmodule
  freeCriticalPath intervalRetardedCriticalPath energyPath criticalGradient energyDistribution energyGradient
  freeEnergyState forwardEnergyState restrictedEnergyState intervalTotalSourceEnergy
  intervalFutureEnergyState restrictedL2 extendEndpointSource

/-- The actual future path is the full-source free path minus the actual past path.
Only the retained endpoint, homogeneous KT(5), and retarded KT(7) interfaces enter. -/
def intervalAdvancedCriticalPath (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (F : CompatibleIntervalSource a b) : CriticalPath (intervalMeasure a b) :=
  freeCriticalPath hDensity hSob hfree a b (intervalTotalSourceEnergy hDensity hSob h0 F) -
    intervalRetardedCriticalPath hDensity hSob h0 hret F

attribute [local irreducible] intervalAdvancedCriticalPath

/-- The energy projection is the literal full-minus-past realization. -/
theorem intervalAdvancedCriticalPath_energy (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (F : CompatibleIntervalSource a b) (t : Set.Icc a b) :
    energyPath (intervalMeasure a b) (intervalAdvancedCriticalPath hDensity hSob h0 hfree hret F) t =
      intervalFutureEnergyState hDensity hSob h0 F t := by
  unfold intervalAdvancedCriticalPath intervalFutureEnergyState
  rw [criticalPath_energy_sub_apply, freeCriticalPath_energy,
    intervalRetardedCriticalPath_eq_forward]

/-- All energy derivatives are the actual dual-endpoint future integrals. -/
theorem intervalAdvancedCriticalPath_gradient (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (F : CompatibleIntervalSource a b) (t : Set.Icc a b) (j : Fin 3) :
    energyGradient j (energyPath (intervalMeasure a b)
      (intervalAdvancedCriticalPath hDensity hSob h0 hfree hret F) t) =
      restrictedL2 h0 (Set.Ioc (t : ℝ) b) measurableSet_Ioc t (sourceGlobalGradient F j) := by
  rw [intervalAdvancedCriticalPath_energy]
  exact intervalFutureEnergyState_gradient hDensity hSob h0 F t j

/-- The critical Bochner coordinate represents the very same future L2 derivative. -/
theorem intervalAdvancedCriticalPath_coordinate_ae (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (F : CompatibleIntervalSource a b) (j : Fin 3) :
    ∀ᵐ (t : Set.Icc a b) ∂(intervalMeasure a b),
      (restrictedL2 h0 (Set.Ioc (t : ℝ) b) measurableSet_Ioc t
        (sourceGlobalGradient F j) : FreeFlow.V → ℂ) =ᵐ[volume]
      (criticalGradient (intervalMeasure a b) j
        (intervalAdvancedCriticalPath hDensity hSob h0 hfree hret F) t : FreeFlow.V → ℂ) := by
  have he := criticalGradient_ae_eq (intervalMeasure a b)
    (intervalAdvancedCriticalPath hDensity hSob h0 hfree hret F) j
  filter_upwards [he] with t ht
  rwa [intervalAdvancedCriticalPath_gradient] at ht

/-- The scalar formula is literally integrated over the future interval (t,b]. -/
theorem intervalAdvancedCriticalPath_scalar (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (F : CompatibleIntervalSource a b) (t : Set.Icc a b) (φ : FreeFlow.Test) :
    energyDistribution (energyPath (intervalMeasure a b)
      (intervalAdvancedCriticalPath hDensity hSob h0 hfree hret F) t) φ =
      ∫ s in Set.Ioc (t : ℝ) b,
        Lp.toTemperedDistribution (F.value s) (freeTest ((t : ℝ)-s) φ) := by
  rw [intervalAdvancedCriticalPath_energy]
  exact intervalFutureEnergyState_scalar hDensity hSob h0 F t φ

/-- The full graph construction has exactly zero terminal energy. -/
theorem intervalAdvancedCriticalPath_terminal (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hab : a ≤ b) (F : CompatibleIntervalSource a b) :
    energyPath (intervalMeasure a b) (intervalAdvancedCriticalPath hDensity hSob h0 hfree hret F)
      ⟨b,hab,le_rfl⟩ = 0 := by
  rw [intervalAdvancedCriticalPath_energy]
  exact intervalFutureEnergyState_right_zero hDensity hSob h0 hab F

/-- Distributional identification with the actual restricted L2 source operator. -/
theorem intervalAdvancedCriticalPath_distribution (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (F : CompatibleIntervalSource a b) (t : Set.Icc a b) :
    energyDistribution (energyPath (intervalMeasure a b)
      (intervalAdvancedCriticalPath hDensity hSob h0 hfree hret F) t) =
      (Lp.toTemperedDistributionCLM ℂ volume 2)
        ((restrictedL2CLM h0 (Set.Ioc (t : ℝ) b) measurableSet_Ioc t)
          (sourceGlobalValue F)) := by
  rw [intervalAdvancedCriticalPath_energy]
  exact intervalFutureEnergyState_distribution hDensity hSob h0 F t

/-- Genuine continuous-energy norm bound, with no dependence on the interval length. -/
theorem intervalAdvancedCriticalPath_energy_norm (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (F : CompatibleIntervalSource a b) :
    ‖energyPath (intervalMeasure a b) (intervalAdvancedCriticalPath hDensity hSob h0 hfree hret F)‖ ≤
      energyEndpointConstant K C0 * ‖F.gradient‖ := by
  apply (ContinuousMap.norm_le _
    (mul_nonneg (energyEndpointConstant_nonneg h0) (norm_nonneg F.gradient))).mpr
  intro t
  rw [intervalAdvancedCriticalPath_energy, intervalFutureEnergyState_eq_restricted]
  have hb := restrictedEnergyState_norm hDensity hSob h0 (sourceGlobalValue F)
    (sourceGlobalGradient F) (sourceGlobalDerivative F) (Set.Ioc (t : ℝ) b) measurableSet_Ioc t
  have he : ‖sourceGlobalGradient F‖ = ‖F.gradient‖ :=
    extendEndpointSource_family_norm (Set.Icc a b) measurableSet_Icc F.gradient
  simpa only [he] using hb

private theorem totalSource_gradient_bound (hDensity : OrdinaryH1Density)
    {K C0 a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (F : CompatibleIntervalSource a b) (j : Fin 3) :
    ‖energyGradient j (intervalTotalSourceEnergy hDensity hSob h0 F)‖ ≤ C0 * ‖F.gradient j‖ := by
  unfold intervalTotalSourceEnergy
  rw [restrictedEnergyState_gradient]
  exact restrictedL2_extend_norm h0 (Set.Icc a b) measurableSet_Icc
    (F.gradient j) (Set.Ioc a b) measurableSet_Ioc 0

private theorem freePath_gradient_real_bound (hDensity : OrdinaryH1Density)
    {K Ch : ℝ} (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (a b : ℝ) (u : EnergyState) (j : Fin 3) :
    ‖criticalGradient (intervalMeasure a b) j (freeCriticalPath hDensity hSob hfree a b u)‖ ≤
      Ch * ‖energyGradient j u‖ := by
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hfree.1 (norm_nonneg (energyGradient j u)))).mp
  simpa only [ofReal_norm] using freeCriticalPath_gradient_bound hDensity hSob hfree a b u j

private theorem abstractMap_sub_norm_le {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup G] [NormedSpace ℂ G]
    (L : E →L[ℂ] G) (u v : E) : ‖L (u-v)‖ ≤ ‖L u‖ + ‖L v‖ := by
  rw [L.map_sub]
  exact norm_sub_le _ _

private theorem path_gradient_sub_bound {a b : ℝ}
    (u v : CriticalPath (intervalMeasure a b)) (j : Fin 3) :
    ‖criticalGradient (intervalMeasure a b) j (u-v)‖ ≤
      ‖criticalGradient (intervalMeasure a b) j u‖ + ‖criticalGradient (intervalMeasure a b) j v‖ :=
  abstractMap_sub_norm_le (criticalGradient (intervalMeasure a b) j) u v

/-- The homogeneous and retarded bounds give the derived future W constant Ch*C0+Cr.
This concerns the unchanged sharp W exponents (10,30/13); optimality is not asserted. -/
theorem intervalAdvancedCriticalPath_gradient_norm (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (F : CompatibleIntervalSource a b) (j : Fin 3) :
    ‖criticalGradient (intervalMeasure a b) j (intervalAdvancedCriticalPath hDensity hSob h0 hfree hret F)‖ ≤
      (Ch * C0 + Cr) * ‖F.gradient j‖ := by
  have htotal := totalSource_gradient_bound hDensity hSob h0 F j
  have hfull := (freePath_gradient_real_bound hDensity hSob hfree a b
    (intervalTotalSourceEnergy hDensity hSob h0 F) j).trans
      (mul_le_mul_of_nonneg_left htotal hfree.1)
  have hpast : ‖criticalGradient (intervalMeasure a b) j
      (intervalRetardedCriticalPath hDensity hSob h0 hret F)‖ ≤ Cr * ‖F.gradient j‖ := by
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hret.1 (norm_nonneg (F.gradient j)))).mp
    simpa only [ofReal_norm] using intervalRetardedCriticalPath_gradient_bound
      hDensity hSob h0 hret F j
  have htriangle := path_gradient_sub_bound
    (freeCriticalPath hDensity hSob hfree a b (intervalTotalSourceEnergy hDensity hSob h0 F))
    (intervalRetardedCriticalPath hDensity hSob h0 hret F) j
  unfold intervalAdvancedCriticalPath
  calc
    _ ≤ ‖criticalGradient (intervalMeasure a b) j (freeCriticalPath hDensity hSob hfree a b
        (intervalTotalSourceEnergy hDensity hSob h0 F))‖ +
        ‖criticalGradient (intervalMeasure a b) j (intervalRetardedCriticalPath hDensity hSob h0 hret F)‖ :=
      htriangle
    _ ≤ Ch * (C0 * ‖F.gradient j‖) + Cr * ‖F.gradient j‖ := add_le_add hfull hpast
    _ = (Ch * C0 + Cr) * ‖F.gradient j‖ := by ring

/-- The explicit derived interval-independent E+W bound. -/
theorem intervalAdvancedCriticalPath_norm (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (F : CompatibleIntervalSource a b) :
    ‖intervalAdvancedCriticalPath hDensity hSob h0 hfree hret F‖ ≤
      max (energyEndpointConstant K C0) (Ch * C0 + Cr) * ‖F.gradient‖ := by
  rw [criticalPath_norm]
  apply max_le
  · exact (intervalAdvancedCriticalPath_energy_norm hDensity hSob h0 hfree hret F).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · apply (pi_norm_le_iff_of_nonneg (mul_nonneg
      (le_trans (energyEndpointConstant_nonneg h0) (le_max_left _ _)) (norm_nonneg _))).mpr
    intro j
    exact (intervalAdvancedCriticalPath_gradient_norm hDensity hSob h0 hfree hret F j).trans
      ((mul_le_mul_of_nonneg_left (norm_le_pi_norm F.gradient j)
        (add_nonneg (mul_nonneg hfree.1 h0.1) hret.1)).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)))

end HartreeF.ActualDuhamelPath
