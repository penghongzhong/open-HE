import FHighpassL2Realization

/-! The highpass is a genuine bounded linear map into the actual L2/weak-L2-gradient
H1 graph. Consequently continuous homogeneous-energy paths map to C_t H1. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology
namespace HartreeF.EnergySpace.Highpass
open HartreeF.EnergySpace SobolevStretch StationarySelfTest

variable (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
variable (q : Cutoff) {L : ℝ} (hL : 0 < L)

theorem highValueL2_add (u v : EnergyState) :
    highValueL2 hDensity hSob q hL (u + v) =
      highValueL2 hDensity hSob q hL u + highValueL2 hDensity hSob q hL v := by
  apply FreeFlow.l2_distribution_injective
  change Lp.toTemperedDistribution (highValueL2 hDensity hSob q hL (u + v)) =
    (Lp.toTemperedDistributionCLM ℂ volume 2) (_ + _)
  rw [map_add]
  change Lp.toTemperedDistribution (highValueL2 hDensity hSob q hL (u + v)) =
    Lp.toTemperedDistribution (highValueL2 hDensity hSob q hL u) +
      Lp.toTemperedDistribution (highValueL2 hDensity hSob q hL v)
  simp only [highValueL2_distribution, map_add]

theorem highValueL2_smul (c : ℂ) (u : EnergyState) :
    highValueL2 hDensity hSob q hL (c • u) = c • highValueL2 hDensity hSob q hL u := by
  apply FreeFlow.l2_distribution_injective
  change Lp.toTemperedDistribution (highValueL2 hDensity hSob q hL (c • u)) =
    (Lp.toTemperedDistributionCLM ℂ volume 2) (c • _)
  rw [map_smul]
  change Lp.toTemperedDistribution (highValueL2 hDensity hSob q hL (c • u)) =
    c • Lp.toTemperedDistribution (highValueL2 hDensity hSob q hL u)
  simp only [highValueL2_distribution, map_smul]

def highValueL2CLM : EnergyState →L[ℂ] L2 :=
  LinearMap.mkContinuous
    { toFun := highValueL2 hDensity hSob q hL
      map_add' := highValueL2_add hDensity hSob q hL
      map_smul' := highValueL2_smul hDensity hSob q hL }
    (L⁻¹ * Real.sqrt 3) (fun u => by
      calc
        _ ≤ L⁻¹ * pureGradientNorm u := highValueL2_bound hDensity hSob q hL u
        _ ≤ L⁻¹ * (Real.sqrt 3 * ‖u‖) :=
          mul_le_mul_of_nonneg_left (pureGradient_le_sqrt_three_energyState u)
            (inv_nonneg.mpr hL.le)
        _ = _ := (mul_assoc _ _ _).symm)

theorem highEnergyState_continuous : Continuous (highEnergyState hDensity hSob q hL) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  apply tendsto_of_gradientTendsto hSob
  intro j
  simpa only [highEnergyState_gradient, Function.comp_def] using
    ((highL2 q L).continuous.comp (energyGradient j).continuous).tendsto u

/-- H1 means the actual L2 value and actual L2 coordinate distributional derivatives. -/
def h1Residual (j : Fin 3) : (L2 × (Fin 3 → L2)) →L[ℂ] TD :=
  (lineDerivOpCLM ℂ TD (coordinate j)).comp
    ((Lp.toTemperedDistributionCLM ℂ volume 2).comp
      (ContinuousLinearMap.fst ℂ L2 (Fin 3 → L2))) -
  (Lp.toTemperedDistributionCLM ℂ volume 2).comp
    ((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.snd ℂ L2 (Fin 3 → L2)))

def h1Submodule : Submodule ℂ (L2 × (Fin 3 → L2)) :=
  ⨅ j : Fin 3, (h1Residual j).ker

abbrev H1State := h1Submodule

theorem mem_h1Submodule (z : L2 × (Fin 3 → L2)) : z ∈ h1Submodule ↔
    ∀ j : Fin 3, ∂_{coordinate j} (Lp.toTemperedDistribution z.1) =
      Lp.toTemperedDistribution (z.2 j) := by
  simp only [h1Submodule, Submodule.mem_iInf, LinearMap.mem_ker]
  change (∀ j : Fin 3, ∂_{coordinate j} (Lp.toTemperedDistribution z.1) -
    Lp.toTemperedDistribution (z.2 j) = 0) ↔ _
  simp only [sub_eq_zero]

theorem h1Submodule_isClosed : IsClosed (h1Submodule : Set (L2 × (Fin 3 → L2))) := by
  have he : (h1Submodule : Set (L2 × (Fin 3 → L2))) =
      ⋂ j : Fin 3, {z | h1Residual j z = 0} := by
    ext z
    change z ∈ h1Submodule ↔ _
    simp only [h1Submodule, Submodule.mem_iInf, LinearMap.mem_ker,
      Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  rw [he]
  exact isClosed_iInter (fun j => isClosed_eq (h1Residual j).continuous continuous_const)

instance h1State_complete : CompleteSpace H1State := h1Submodule_isClosed.completeSpace_coe

def highH1State (u : EnergyState) : H1State :=
  ⟨(highValueL2 hDensity hSob q hL u, fun j => highL2 q L (energyGradient j u)),
    (mem_h1Submodule _).mpr (highValueL2_derivative hDensity hSob q hL u)⟩

theorem highH1State_continuous : Continuous (highH1State hDensity hSob q hL) := by
  apply Continuous.subtype_mk
  exact (highValueL2CLM hDensity hSob q hL).continuous.prodMk
    (continuous_pi (fun j => (highL2 q L).continuous.comp (energyGradient j).continuous))

/-- No global orbit, scale normalization, original mass, or finite variance is required. -/
theorem continuous_highpass_H1 {T : Type*} [TopologicalSpace T] {u : T → EnergyState}
    (hu : Continuous u) : Continuous (fun t => highH1State hDensity hSob q hL (u t)) :=
  (highH1State_continuous hDensity hSob q hL).comp hu

theorem continuousOn_highpass_H1 {T : Type*} [TopologicalSpace T] {u : T → EnergyState}
    {I : Set T} (hu : ContinuousOn u I) :
    ContinuousOn (fun t => highH1State hDensity hSob q hL (u t)) I :=
  (highH1State_continuous hDensity hSob q hL).comp_continuousOn hu

theorem highH1State_same_value (u : EnergyState) :
    ((highH1State hDensity hSob q hL u).val.1 : V → ℂ) =ᵐ[volume]
      energyValue (highEnergyState hDensity hSob q hL u) :=
  (highEnergyState_value_ae hDensity hSob q hL u).symm

theorem highH1State_same_gradient (u : EnergyState) (j : Fin 3) :
    (highH1State hDensity hSob q hL u).val.2 j =
      energyGradient j (highEnergyState hDensity hSob q hL u) := rfl

end HartreeF.EnergySpace.Highpass
