import FJointGradientBounds
import FEnergyFreeConsumers

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.ActualStrichartz
open MeasureTheory Filter SobolevStretch StationarySelfTest TimeHolder EnergySpace
open scoped ENNReal NNReal

/-- C42's actual representative of the literal Fourier L2 trajectory. -/
def freeJoint (f : FreeFlow.L2) (t : ℝ) (x : Space) : ℂ :=
  strongJointLpRepresentative volume 2 (fun s => FreeFlow.freeL2 s f)
    (FreeFlow.freeL2_time_continuous f).stronglyMeasurable (t, x)

theorem freeJoint_stronglyMeasurable (f : FreeFlow.L2) :
    StronglyMeasurable (fun z : ℝ × Space => freeJoint f z.1 z.2) :=
  strongJointLpRepresentative_stronglyMeasurable _ _ _ _

theorem freeJoint_slice (f : FreeFlow.L2) (t : ℝ) :
    freeJoint f t =ᵐ[volume] FreeFlow.freeL2 t f :=
  strongJointLpRepresentative_slice _ _ _ _ t

/-- Precisely the numerical (5) specialization of Keel--Tao, Theorem 1.2,
printed p956, n=3, sigma=3/2, (q,r)=(10,30/13), on all real time.
Only an extended-norm inequality on the already constructed Fourier operator
is retained. No operator, EnergyState, continuity or gradient relation is input.
This proposition is an explicit standard analytic premise, not a native proof. -/
def OrdinaryHomogeneousStrichartz (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ f : FreeFlow.L2,
    mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) (freeJoint f) ≤
      ENNReal.ofReal (C * ‖f‖)

theorem freeJoint_mixedNorm_finite {C : ℝ} (h : OrdinaryHomogeneousStrichartz C)
    (f : FreeFlow.L2) :
    mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) (freeJoint f) ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.2 f)

/-- Almost-everywhere critical spatial membership is derived from the numerical
spacetime inequality, rather than supplied in the standard interface. -/
theorem freeJoint_ae_critical_memLp {C : ℝ} (h : OrdinaryHomogeneousStrichartz C)
    (f : FreeFlow.L2) :
    ∀ᵐ t ∂(volume : Measure ℝ), MemLp (freeJoint f t)
      (ENNReal.ofReal (30/13 : ℝ)) volume :=
  finite_mixedNorm_ae_slice_memLp volume volume 10 _ (by norm_num) (by norm_num)
    (freeJoint f) (freeJoint_mixedNorm_finite h f)

theorem freeJoint_energyGradient (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (u : EnergyState) (j : Fin 3) :
    ∀ᵐ t ∂(volume : Measure ℝ), freeJoint (energyGradient j u) t =ᵐ[volume]
      energyGradient j (freeEnergyState hDensity hSob t u) :=
  Eventually.of_forall (fun t => by rw [freeEnergyState_gradient]; exact freeJoint_slice _ _)

/-- Actual projected gradients of the full homogeneous energy orbit obey W.
The coordinate-to-state bridge uses its already proved derivative identity. -/
theorem freeEnergyState_projected_bound (hDensity : OrdinaryH1Density) {K C : ℝ}
    (hSob : OrdinarySobolev K) (h : OrdinaryHomogeneousStrichartz C)
    (u : EnergyState) (L : ℂ →L[ℝ] ℝ) (hL : ∀ z, ‖L z‖ ≤ ‖z‖) :
    mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => energyProjectedGradient L (freeEnergyState hDensity hSob t u)) ≤
      ∑ j : Fin 3, ENNReal.ofReal (C * ‖energyGradient j u‖) := by
  rw [energyProjected_mixedNorm_eq L _ _ (freeJoint_energyGradient hDensity hSob u)]
  exact (jointProjection_mixedNorm_le L hL _
    (fun j => freeJoint_stronglyMeasurable (energyGradient j u)) _
    (by norm_num) (by norm_num)).trans (Finset.sum_le_sum (fun j _ => h.2 _))

theorem freeEnergyState_projected_finite (hDensity : OrdinaryH1Density) {K C : ℝ}
    (hSob : OrdinarySobolev K) (h : OrdinaryHomogeneousStrichartz C)
    (u : EnergyState) (L : ℂ →L[ℝ] ℝ) (hL : ∀ z, ‖L z‖ ≤ ‖z‖) :
    mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => energyProjectedGradient L (freeEnergyState hDensity hSob t u)) ≠ ∞ := by
  exact ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.ofReal_ne_top))
    (freeEnergyState_projected_bound hDensity hSob h u L hL)

end HartreeF.ActualStrichartz
