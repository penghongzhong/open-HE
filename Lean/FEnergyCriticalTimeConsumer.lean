import FCriticalTimeSobolev
import FJointLpRepresentatives
import FEnergyStateWeakGradient

/-! A genuine C43-to-C42 consumer: a measurable EnergyState curve constructs
joint representatives. Their weak-gradient compatibility is transported from
C43, and is not required as a separate consumer assumption. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.CriticalTimeSobolev
open MeasureTheory Filter SobolevStretch StationarySelfTest TimeHolder EnergySpace
open scoped ENNReal NNReal RealInnerProductSpace

/-- Both entries of a distributional weak-gradient identity may be replaced
by spatial almost-everywhere equal representatives. -/
theorem weakGradient_congr_fields {f g : Space → ℝ} {F G : Space → Space}
    (h : HasWeakGradient f F) (hfg : f =ᵐ[volume] g) (hFG : F =ᵐ[volume] G) :
    HasWeakGradient g G := by
  refine ⟨h.function_local.congr hfg, h.gradient_local.congr hFG, ?_⟩
  intro e phi hphi hc
  calc
    (∫ x, g x * fderiv ℝ phi x e) = ∫ x, f x * fderiv ℝ phi x e := by
      apply integral_congr_ae
      filter_upwards [hfg] with x hx
      rw [hx]
    _ = -(∫ x, ⟪F x,e⟫ * phi x) := h.integration_by_parts e phi hphi hc
    _ = -(∫ x, ⟪G x,e⟫ * phi x) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hFG] with x hx
      rw [hx]

theorem inDotH1_congr_fields {u v : Space → ℂ} {U V P Q : Space → Space}
    (h : InDotH1 u U V) (huv : u =ᵐ[volume] v)
    (hUP : U =ᵐ[volume] P) (hVQ : V =ᵐ[volume] Q) : InDotH1 v P Q := by
  refine ⟨(memLp_congr_ae huv).mp h.function_L6,
    (memLp_congr_ae hUP).mp h.real_gradient_L2,
    (memLp_congr_ae hVQ).mp h.imag_gradient_L2,
    weakGradient_congr_fields h.real_weak ?_ hUP,
    weakGradient_congr_fields h.imag_weak ?_ hVQ⟩
  · exact huv.mono fun _ hx => congrArg Complex.re hx
  · exact huv.mono fun _ hx => congrArg Complex.im hx

/-- Actual jointly measurable fields realizing an EnergyState curve. The
record asks for class agreement only; weak compatibility follows below. -/
structure EnergyJointFields {T : Type*} [MeasurableSpace T]
    (mu : Measure T) (g : T → EnergyState) where
  u : T → Space → ℂ
  U : T → Space → Space
  V : T → Space → Space
  joint_u : StronglyMeasurable (fun z : T × Space => u z.1 z.2)
  joint_U : StronglyMeasurable (fun z : T × Space => U z.1 z.2)
  joint_V : StronglyMeasurable (fun z : T × Space => V z.1 z.2)
  slice_eq : ∀ᵐ t ∂mu,
    u t =ᵐ[volume] (energyValue (g t) : Space → ℂ) ∧
    U t =ᵐ[volume] energyProjectedGradient Complex.reCLM (g t) ∧
    V t =ᵐ[volume] energyProjectedGradient Complex.imCLM (g t)

/-- C42 selects the value and three coordinate representatives. Their real
and imaginary vector sums are jointly measurable representatives of C43's
projected gradients. No sigma-finiteness is needed for this selection. -/
def energyJointFields {T : Type*} [MeasurableSpace T]
    (mu : Measure T) (g : T → EnergyState) (hg : AEStronglyMeasurable g mu) :
    EnergyJointFields mu g := by
  let hv := energyValue.continuous.comp_aestronglyMeasurable hg
  let hd (j : Fin 3) := (energyGradient j).continuous.comp_aestronglyMeasurable hg
  let f := aeJointLpRepresentative mu volume 6 (fun t => energyValue (g t)) hv
  let d (j : Fin 3) := aeJointLpRepresentative mu volume 2 (fun t => energyGradient j (g t)) (hd j)
  have hf : StronglyMeasurable f := aeJointLpRepresentative_stronglyMeasurable _ _ _ _ _
  have hdm (j : Fin 3) : StronglyMeasurable (d j) :=
    aeJointLpRepresentative_stronglyMeasurable _ _ _ _ _
  have hproject (L : ℂ →L[ℝ] ℝ) :
      StronglyMeasurable (fun z : T × Space => ∑ j : Fin 3, L (d j z) • coordinate j) := by
    simpa only [Finset.sum_fn] using Finset.stronglyMeasurable_sum Finset.univ
      (fun j _ => (L.continuous.comp_stronglyMeasurable (hdm j)).smul_const (coordinate j))
  refine { u := fun t x => f (t, x)
           U := fun t x => ∑ j : Fin 3, (d j (t, x)).re • coordinate j
           V := fun t x => ∑ j : Fin 3, (d j (t, x)).im • coordinate j
           joint_u := hf
           joint_U := hproject Complex.reCLM
           joint_V := hproject Complex.imCLM
           slice_eq := ?_ }
  have hfe := aeJointLpRepresentative_slice mu volume 6 (fun t => energyValue (g t)) hv
  have hde (j : Fin 3) := aeJointLpRepresentative_slice mu volume 2
    (fun t => energyGradient j (g t)) (hd j)
  filter_upwards [hfe, eventually_all.mpr hde] with t hft hdt
  refine ⟨hft, ?_, ?_⟩
  · filter_upwards [eventually_all.mpr hdt] with x hx
    simp only [energyProjectedGradient]
    exact Finset.sum_congr rfl (fun j _ => by rw [show d j (t, x) = energyGradient j (g t) x from hx j]; rfl)
  · filter_upwards [eventually_all.mpr hdt] with x hx
    simp only [energyProjectedGradient]
    exact Finset.sum_congr rfl (fun j _ => by rw [show d j (t, x) = energyGradient j (g t) x from hx j]; rfl)

/-- Genuine weak compatibility of the C42 representatives is produced from
C43's distributional energy-state compatibility. -/
theorem EnergyJointFields.inDotH1 {T : Type*} [MeasurableSpace T]
    {mu : Measure T} {g : T → EnergyState} (r : EnergyJointFields mu g) :
    ∀ᵐ t ∂mu, InDotH1 (r.u t) (r.U t) (r.V t) := by
  filter_upwards [r.slice_eq] with t ht
  exact inDotH1_congr_fields (energyState_inDotH1 (g t)) ht.1.symm ht.2.1.symm ht.2.2.symm

/-- Any spatial exponent and time exponent preserve the mixed norms under
these almost-everywhere representative identities. -/
theorem EnergyJointFields.gradient_mixedNorm {T : Type*} [MeasurableSpace T]
    {mu : Measure T} {g : T → EnergyState} (r : EnergyJointFields mu g)
    (p q : ℝ≥0∞) :
    mixedNorm mu volume p q r.U =
      mixedNorm mu volume p q (fun t => energyProjectedGradient Complex.reCLM (g t)) ∧
    mixedNorm mu volume p q r.V =
      mixedNorm mu volume p q (fun t => energyProjectedGradient Complex.imCLM (g t)) := by
  constructor
  · apply eLpNorm_congr_ae
    filter_upwards [r.slice_eq] with t ht
    exact eLpNorm_congr_ae ht.2.1
  · apply eLpNorm_congr_ae
    filter_upwards [r.slice_eq] with t ht
    exact eLpNorm_congr_ae ht.2.2

/-- An actual C43 energy trajectory plus critical gradient spacetime bounds
has C42 joint value representatives with finite S=L10_t L10_x norm. Weak
compatibility, joint measurability and value L10 membership are all produced. -/
theorem energyJointFields_critical_finite_and_bound (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K)
    {T : Type*} [MeasurableSpace T] (mu : Measure T) [SigmaFinite mu]
    (g : T → EnergyState) (hg : AEStronglyMeasurable g mu)
    (hU : ∀ᵐ t ∂mu, MemLp (energyProjectedGradient Complex.reCLM (g t))
      (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : ∀ᵐ t ∂mu, MemLp (energyProjectedGradient Complex.imCLM (g t))
      (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hUFinite : mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => energyProjectedGradient Complex.reCLM (g t)) ≠ ∞)
    (hVFinite : mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => energyProjectedGradient Complex.imCLM (g t)) ≠ ∞) :
    let r := energyJointFields mu g hg
    (∀ᵐ t ∂mu, InDotH1 (r.u t) (r.U t) (r.V t)) ∧
    (∀ᵐ t ∂mu, MemLp (r.u t) 10 volume) ∧
    mixedNorm mu volume 10 10 r.u ≠ ∞ ∧
    MemLp (fun t => eLpNorm (r.u t) 10 volume) 10 mu ∧
    (mixedNorm mu volume 10 10 r.u).toReal ≤ ((5/3)*K^(1/6 : ℝ)) *
      ((mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ))
          (fun t => energyProjectedGradient Complex.reCLM (g t))).toReal +
       (mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ))
          (fun t => energyProjectedGradient Complex.imCLM (g t))).toReal) := by
  let r := energyJointFields mu g hg
  have hUr : ∀ᵐ t ∂mu, MemLp (r.U t) (ENNReal.ofReal (30/13 : ℝ)) volume := by
    filter_upwards [r.slice_eq, hU] with t ht hUt
    exact (memLp_congr_ae ht.2.1).mpr hUt
  have hVr : ∀ᵐ t ∂mu, MemLp (r.V t) (ENNReal.ofReal (30/13 : ℝ)) volume := by
    filter_upwards [r.slice_eq, hV] with t ht hVt
    exact (memLp_congr_ae ht.2.2).mpr hVt
  have heq := r.gradient_mixedNorm 10 (ENNReal.ofReal (30/13 : ℝ))
  have hUrFinite : mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) r.U ≠ ∞ := by
    rwa [heq.1]
  have hVrFinite : mixedNorm mu volume 10 (ENNReal.ofReal (30/13 : ℝ)) r.V ≠ ∞ := by
    rwa [heq.2]
  have hresult := critical_mixedNorm_ten_finite_and_bound hDensity hSob mu r.u r.U r.V
    r.joint_u.aestronglyMeasurable r.joint_U.aestronglyMeasurable
    r.joint_V.aestronglyMeasurable r.inDotH1 hUr hVr hUrFinite hVrFinite
  rw [heq.1, heq.2] at hresult
  exact ⟨r.inDotH1, hresult⟩

end HartreeF.CriticalTimeSobolev
