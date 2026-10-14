import FJointGradientBounds
import FActualRetardedTimeProducer

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.ActualStrichartz
open MeasureTheory Filter LineDeriv SobolevStretch StationarySelfTest TimeHolder EnergySpace Retarded
open scoped ENNReal NNReal

/-- C42's representative of the literal retarded L2 scalar integral. The
strong continuity needed here is already proved for that integral. -/
def retardedJoint {C0 : ℝ} (h0 : OrdinaryEndpointBound C0)
    (F : EndpointSource) (t : ℝ) (x : Space) : ℂ :=
  strongJointLpRepresentative volume 2 (retardedL2 h0 F)
    (retardedL2_time_continuous h0 F).stronglyMeasurable (t, x)

theorem retardedJoint_stronglyMeasurable {C0 : ℝ} (h0 : OrdinaryEndpointBound C0)
    (F : EndpointSource) :
    StronglyMeasurable (fun z : ℝ × Space => retardedJoint h0 F z.1 z.2) :=
  strongJointLpRepresentative_stronglyMeasurable _ _ _ _

theorem retardedJoint_slice {C0 : ℝ} (h0 : OrdinaryEndpointBound C0)
    (F : EndpointSource) (t : ℝ) :
    retardedJoint h0 F t =ᵐ[volume] retardedL2 h0 F t :=
  strongJointLpRepresentative_slice _ _ _ _ t

/-- Numerical Keel--Tao Theorem 1.2 (7), printed p956: input pair (2,6),
output pair (10,30/13), sigma=3/2, with input norm L2_t L(6/5)_x.
The already constructed literal all-past retardedL2 is fixed. The old endpoint
bound constructs this object but is not claimed to imply this new inequality.
No output object, continuity or gradient relation is supplied by this premise. -/
def OrdinaryRetardedStrichartz {C0 : ℝ} (h0 : OrdinaryEndpointBound C0) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ F : EndpointSource,
    mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) (retardedJoint h0 F) ≤
      ENNReal.ofReal (C * ‖F‖)

theorem retardedJoint_mixedNorm_finite {C0 C : ℝ} (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (F : EndpointSource) :
    mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) (retardedJoint h0 F) ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.2 F)

theorem retardedJoint_ae_critical_memLp {C0 C : ℝ} (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (F : EndpointSource) :
    ∀ᵐ t ∂(volume : Measure ℝ), MemLp (retardedJoint h0 F t)
      (ENNReal.ofReal (30/13 : ℝ)) volume :=
  finite_mixedNorm_ae_slice_memLp volume volume 10 _ (by norm_num) (by norm_num)
    (retardedJoint h0 F) (retardedJoint_mixedNorm_finite h0 h F)

variable (hDensity : OrdinaryH1Density) {K C0 C : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (h : OrdinaryRetardedStrichartz h0 C)
    (F : EndpointSource) (G : Fin 3 → EndpointSource)
    (hFG : ∀ j : Fin 3, ∀ᵐ s ∂volume,
      ∂_{coordinate j} (Lp.toTemperedDistribution (F s)) = Lp.toTemperedDistribution (G j s))

/-- The very same three input source coordinates generate the state's gradients. -/
theorem retardedJoint_energyGradient (j : Fin 3) :
    ∀ᵐ t ∂(volume : Measure ℝ), retardedJoint h0 (G j) t =ᵐ[volume]
      energyGradient j (retardedEnergyState hDensity hSob h0 F G hFG t) :=
  Eventually.of_forall (fun t => retardedJoint_slice h0 (G j) t)

include h in
theorem retardedEnergyState_projected_bound (L : ℂ →L[ℝ] ℝ)
    (hL : ∀ z, ‖L z‖ ≤ ‖z‖) :
    mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => energyProjectedGradient L (retardedEnergyState hDensity hSob h0 F G hFG t)) ≤
      ∑ j : Fin 3, ENNReal.ofReal (C * ‖G j‖) := by
  rw [energyProjected_mixedNorm_eq L _ _
    (retardedJoint_energyGradient hDensity hSob h0 F G hFG)]
  exact (jointProjection_mixedNorm_le L hL _
    (fun j => retardedJoint_stronglyMeasurable h0 (G j)) _
    (by norm_num) (by norm_num)).trans (Finset.sum_le_sum (fun j _ => h.2 _))

include h in
theorem retardedEnergyState_projected_finite (L : ℂ →L[ℝ] ℝ)
    (hL : ∀ z, ‖L z‖ ≤ ‖z‖) :
    mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => energyProjectedGradient L (retardedEnergyState hDensity hSob h0 F G hFG t)) ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.ofReal_ne_top))
    (retardedEnergyState_projected_bound hDensity hSob h0 h F G hFG L hL)

end HartreeF.ActualStrichartz
