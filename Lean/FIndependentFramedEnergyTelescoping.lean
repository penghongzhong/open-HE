import FOneProfileEnergySplit
import FCriticalAffineIsometry

/-! Finite energy telescoping for actual spatially framed residual chains.
All inverse-frame bounded-L6, a.e.-value and weak-gradient hypotheses are kept.
There is no profile extraction, frame orthogonality or free-time covariance claim. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace HartreeF.FramedEnergyIndependentReview
open CriticalAffine NonlocalBL EnergySpace EnergyVariation StateEnergy ForcingDomain SharpOrdinary

def pullbackState (lambda : ℝ) (hlambda : 0 < lambda) (y : Space) (u : EnergyState) : EnergyState :=
  (criticalAffineState lambda hlambda y).symm u

theorem pullbackState_energy {alpha : ℝ}
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (lambda : ℝ) (hlambda : 0 < lambda) (y : Space) (u : EnergyState) :
    totalEnergy alpha (pullbackState lambda hlambda y u)=totalEnergy alpha u := by
  have h := criticalAffineState_totalEnergy hOrd lambda hlambda y (pullbackState lambda hlambda y u)
  have hi : criticalAffineState lambda hlambda y (pullbackState lambda hlambda y u)=u :=
    (criticalAffineState lambda hlambda y).apply_symm_apply u
  rw [hi] at h
  exact h.symm

theorem pullback_sub_profile_energy {alpha : ℝ}
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (lambda : ℝ) (hlambda : 0 < lambda) (y : Space) (u f : EnergyState) :
    totalEnergy alpha (pullbackState lambda hlambda y u-f)=
      totalEnergy alpha (u-criticalAffineState lambda hlambda y f) := by
  have h := criticalAffineState_totalEnergy hOrd lambda hlambda y (pullbackState lambda hlambda y u-f)
  have hi : criticalAffineState lambda hlambda y (pullbackState lambda hlambda y u-f)=
      u-criticalAffineState lambda hlambda y f := by
    rw [map_sub]
    exact congrArg (fun v : EnergyState => v-criticalAffineState lambda hlambda y f)
      ((criticalAffineState lambda hlambda y).apply_symm_apply u)
  rw [hi] at h
  exact h.symm

/-- One actual spatial-frame subtraction, with explicit framed ordinary inputs. -/
theorem actual_spatial_frame_energy_split {alpha B : ℝ}
    (hH : SharpOrdinaryHLS alpha)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (lambda : ℕ → ℝ) (hlambda : ∀ n, 0 < lambda n) (y : ℕ → Space)
    (u : ℕ → EnergyState) (f : EnergyState)
    (hbound : ∀ n, ‖energyValue (pullbackState (lambda n) (hlambda n) (y n) (u n))‖ ≤ B)
    (hae : ∀ᵐ x ∂volume, Tendsto
      (fun n => energyValue (pullbackState (lambda n) (hlambda n) (y n) (u n)) x)
      atTop (𝓝 (energyValue f x)))
    (hweak : ∀ j : Fin 3, ∀ v : L2, Tendsto
      (fun n => inner ℝ (energyGradient j (pullbackState (lambda n) (hlambda n) (y n) (u n))) v)
      atTop (𝓝 (inner ℝ (energyGradient j f) v))) :
    Tendsto (fun n => totalEnergy alpha (u n)-
      totalEnergy alpha (u n-criticalAffineState (lambda n) (hlambda n) (y n) f)-totalEnergy alpha f)
      atTop (𝓝 0) := by
  have h := totalEnergy_split_one_profile hH hOrd f hbound hae hweak
  simpa only [pullbackState_energy hOrd,pullback_sub_profile_energy hOrd] using h

/-- Algebraic telescoping, used only after the actual one-step limits are proved. -/
theorem finite_energy_defect_identity (a e : ℕ → ℝ) (J : ℕ) :
    (∑ j ∈ Finset.range J, (a j-a (j+1)-e j)) =
      a 0-a J-∑ j ∈ Finset.range J, e j := by
  induction J with
  | zero => simp
  | succ J hJ =>
    rw [Finset.sum_range_succ,hJ,Finset.sum_range_succ]
    ring

/-- A fixed finite chain of genuinely spatially framed residuals has its actual
energy telescope. Every stage supplies its own inverse-frame weak/a.e. inputs;
there is no unframed convergence assumption forcing later profiles to be zero. -/
theorem finite_spatially_framed_energy_telescoping {alpha : ℝ}
    (hH : SharpOrdinaryHLS alpha)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (J : ℕ) (B : ℕ → ℝ) (lambda : ℕ → ℕ → ℝ)
    (hlambda : ∀ j n, 0 < lambda j n) (y : ℕ → ℕ → Space)
    (u : ℕ → ℕ → EnergyState) (f : ℕ → EnergyState)
    (hstep : ∀ j, j < J → ∀ n, u (j+1) n =
      u j n-criticalAffineState (lambda j n) (hlambda j n) (y j n) (f j))
    (hbound : ∀ j, j < J → ∀ n,
      ‖energyValue (pullbackState (lambda j n) (hlambda j n) (y j n) (u j n))‖ ≤ B j)
    (hae : ∀ j, j < J → ∀ᵐ x ∂volume, Tendsto
      (fun n => energyValue (pullbackState (lambda j n) (hlambda j n) (y j n) (u j n)) x)
      atTop (𝓝 (energyValue (f j) x)))
    (hweak : ∀ j, j < J → ∀ k : Fin 3, ∀ v : L2, Tendsto
      (fun n => inner ℝ (energyGradient k (pullbackState (lambda j n) (hlambda j n) (y j n) (u j n))) v)
      atTop (𝓝 (inner ℝ (energyGradient k (f j)) v))) :
    Tendsto (fun n => totalEnergy alpha (u 0 n)-totalEnergy alpha (u J n)-
      ∑ j ∈ Finset.range J, totalEnergy alpha (f j)) atTop (𝓝 0) := by
  have hone (j : ℕ) (hj : j < J) :
      Tendsto (fun n => totalEnergy alpha (u j n)-totalEnergy alpha (u (j+1) n)-
        totalEnergy alpha (f j)) atTop (𝓝 0) := by
    have h := actual_spatial_frame_energy_split hH hOrd (lambda j) (hlambda j) (y j)
      (u j) (f j) (hbound j hj) (hae j hj) (hweak j hj)
    simpa only [hstep j hj] using h
  have ht := tendsto_finsetSum (Finset.range J) (fun j hj => hone j (Finset.mem_range.mp hj))
  simpa only [finite_energy_defect_identity,Finset.sum_const_zero] using ht

#print axioms pullbackState
#print axioms pullbackState_energy
#print axioms pullback_sub_profile_energy
#print axioms actual_spatial_frame_energy_split
#print axioms finite_energy_defect_identity
#print axioms finite_spatially_framed_energy_telescoping
end HartreeF.FramedEnergyIndependentReview
