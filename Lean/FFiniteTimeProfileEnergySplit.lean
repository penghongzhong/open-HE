import FMovingFreeWeakTransport
import FDivergentProfileEnergySplit
import FRellichOneProfileEnergy
import FIndependentFramedEnergyTelescoping

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace HartreeF.ProfileEnergy
open EnergySpace SobolevStretch StationarySelfTest CriticalAffine
open EnergyVariation StateEnergy ForcingDomain SharpOrdinary LocalRellich FramedEnergyIndependentReview
attribute [local irreducible] energySubmodule
attribute [local instance 101] secondCountableTopologyEither_of_left

/-- Finite normalized-time atoms converge in the actual graph topology,
including both their L6 values and every coordinate L2 gradient. -/
theorem finite_free_atom_strong (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (phi : EnergyState) {s : ℕ → ℝ} {t : ℝ} (hs : Tendsto s atTop (𝓝 t)) :
    Tendsto (fun n => freeEnergyState hDensity hSob (s n) phi) atTop
      (𝓝 (freeEnergyState hDensity hSob t phi)) ∧
    Tendsto (fun n => energyValue (freeEnergyState hDensity hSob (s n) phi)) atTop
      (𝓝 (energyValue (freeEnergyState hDensity hSob t phi))) ∧
    GradientTendsto (fun n => freeEnergyState hDensity hSob (s n) phi) atTop
      (freeEnergyState hDensity hSob t phi) := by
  have ht := (freeEnergyState_time_continuous hDensity hSob phi).tendsto t |>.comp hs
  exact ⟨ht, energyValue.continuous.tendsto _ |>.comp ht, gradientTendsto_of_tendsto ht⟩

/-- Finite normalized-time one-profile Hartree splitting. The actual varying
atom remains in the conclusion; its limiting energy is E(U(t)phi), not E(phi). -/
theorem finite_time_profile_energy_split (hDensity : OrdinaryH1Density)
    (hRel : OrdinaryRellichBall) {K alpha B t : ℝ} (hSob : OrdinarySobolev K)
    (hH : SharpOrdinaryHLS alpha)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (lambda : ℕ → ℝ) (hlambda : ∀ n, 0 < lambda n) (y : ℕ → Space) (s : ℕ → ℝ)
    {u : ℕ → EnergyState} (phi : EnergyState) (hB : ∀ n, ‖u n‖ ≤ B)
    (hw : GradientWeakLimit
      (fun n => (linearProfileFrame hDensity hSob (lambda n) (hlambda n) (y n) (s n)).symm (u n)) phi)
    (hs : Tendsto s atTop (𝓝 t)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun n => totalEnergy alpha (u (σ n))-totalEnergy alpha
        (u (σ n)-linearProfileFrame hDensity hSob (lambda (σ n)) (hlambda (σ n)) (y (σ n)) (s (σ n)) phi)-
        totalEnergy alpha (linearProfileFrame hDensity hSob (lambda (σ n)) (hlambda (σ n)) (y (σ n)) (s (σ n)) phi))
        atTop (𝓝 0) := by
  let q (n : ℕ) := pullbackState (lambda n) (hlambda n) (y n) (u n)
  let psi := freeEnergyState hDensity hSob t phi
  let psin (n : ℕ) := freeEnergyState hDensity hSob (s n) phi
  let b (n : ℕ) := linearProfileFrame hDensity hSob (lambda n) (hlambda n) (y n) (s n) phi
  have hqb (n : ℕ) : ‖q n‖ ≤ B := by
    change ‖(criticalAffineState (lambda n) (hlambda n) (y n)).symm (u n)‖ ≤ B
    rw [(criticalAffineState (lambda n) (hlambda n) (y n)).symm.norm_map]
    exact hB n
  have hp (n : ℕ) : pureGradientNorm (u n) ≤ Real.sqrt 3*B :=
    (pureGradient_le_sqrt_three_energyState _).trans
      (mul_le_mul_of_nonneg_left (hB n) (Real.sqrt_nonneg _))
  have hqw : GradientWeakLimit q psi :=
    spatialPullback_weak_of_finite_fullFrame hDensity hSob lambda hlambda y s phi hp hw hs
  obtain ⟨σ,hσ,_,_,hbase⟩ := exists_energy_split_subsequence_of_gradient_weak hRel hSob hH hOrd psi hqb hqw
  have hstrong : Tendsto psin atTop (𝓝 psi) := (finite_free_atom_strong hDensity hSob phi hs).1
  have hstrongσ := hstrong.comp hσ.tendsto_atTop
  let D := max (K^((6:ℝ)⁻¹)) 1*pureGradientNorm phi
  have hpsin (n : ℕ) : ‖psin n‖ ≤ D := by
    have hh := energyState_le_pureGradient hSob (psin n)
    rwa [freeEnergyState_pureGradientNorm] at hh
  have hpsi : ‖psi‖ ≤ D := by
    have hh := energyState_le_pureGradient hSob psi
    rwa [freeEnergyState_pureGradientNorm] at hh
  have hfix (n : ℕ) : ‖q (σ n)-psi‖ ≤ B+D :=
    (norm_sub_le _ _).trans (add_le_add (hqb _) hpsi)
  have hvar (n : ℕ) : ‖q (σ n)-psin (σ n)‖ ≤ B+D :=
    (norm_sub_le _ _).trans (add_le_add (hqb _) (hpsin _))
  have hd : Tendsto (fun n => ‖(q (σ n)-psi)-(q (σ n)-psin (σ n))‖) atTop (𝓝 0) := by
    have he (n : ℕ) : (q (σ n)-psi)-(q (σ n)-psin (σ n))=psin (σ n)-psi := by abel
    simpa only [he, Function.comp_apply] using tendsto_iff_norm_sub_tendsto_zero.mp hstrongσ
  have herr := totalEnergy_difference_tendsto_zero hH hOrd hfix hvar hd
  have hlast : Tendsto (fun n => totalEnergy alpha psi-totalEnergy alpha (psin (σ n))) atTop (𝓝 0) := by
    simpa only [sub_self, Function.comp_apply] using (tendsto_const_nhds (x := totalEnergy alpha psi)).sub
      (totalEnergy_tendsto hOrd hstrongσ)
  have ht := (hbase.add herr).add hlast
  simp only [zero_add] at ht
  refine ⟨σ,hσ,?_⟩
  change Tendsto (fun n => totalEnergy alpha (u (σ n))-totalEnergy alpha (u (σ n)-b (σ n))-
    totalEnergy alpha (b (σ n))) atTop (𝓝 0)
  convert ht using 1
  funext n
  have heq : totalEnergy alpha (q (σ n))=totalEnergy alpha (u (σ n)) :=
    pullbackState_energy hOrd _ _ _ _
  have her : totalEnergy alpha (q (σ n)-psin (σ n))=totalEnergy alpha (u (σ n)-b (σ n)) :=
    pullback_sub_profile_energy hOrd _ _ _ _ _
  have heb : totalEnergy alpha (b (σ n))=totalEnergy alpha (psin (σ n)) :=
    linearProfileFrame_totalEnergy hDensity hSob hOrd _ _ _ _ phi
  rw [← heq, ← her, heb]
  ring

#print axioms finite_free_atom_strong
#print axioms finite_time_profile_energy_split
end HartreeF.ProfileEnergy
