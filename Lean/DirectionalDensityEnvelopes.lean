import DirectionalPotentialEnvelopes
import RieszTwoEnvelope
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
namespace HartreeF.DerivativeMajorization
open ForcingDomain WeakHartreeChain

theorem directional_density_pair_envelopes {α c : ℝ} (ha : 0<α) (hc : 0≤c)
    {u v h k : Space → ℂ} (hu : AEStronglyMeasurable u volume)
    (hv : AEStronglyMeasurable v volume) (hh : AEStronglyMeasurable h volume)
    (hk : AEStronglyMeasurable k volume) (x : Space)
    (hZ : Integrable (fun y => rieszKernel α c (x-y)*
      (sumAmplitude u v y^(2+α)*‖h y-k y‖)) volume)
    (hWY : Integrable (fun y => rieszKernel α c (x-y)*
      (sumAmplitude u v y^(1+α)*differenceAmplitude u v y*‖k y‖)) volume)
    (hY : Integrable (fun y => rieszKernel α c (x-y)*
      (sumAmplitude u v y^(2+α)*‖k y‖)) volume) :
    Integrable (fun y => rieszKernel α c (x-y)*directionalDensity α u h y) volume ∧
    Integrable (fun y => rieszKernel α c (x-y)*directionalDensity α v k y) volume ∧
    ‖rieszConvolution α c (directionalDensity α v k) x‖ ≤
      (3+α)*rieszConvolution α c (fun y => sumAmplitude u v y^(2+α)*‖k y‖) x ∧
    ‖rieszConvolution α c (directionalDensity α u h) x-
      rieszConvolution α c (directionalDensity α v k) x‖ ≤
      (3+α)*rieszConvolution α c (fun y => sumAmplitude u v y^(2+α)*‖h y-k y‖) x+
      ((3+α)*(2+α))*rieszConvolution α c
        (fun y => sumAmplitude u v y^(1+α)*differenceAmplitude u v y*‖k y‖) x := by
  have hmU := directionalDensity_measurable α hu hh
  have hmV := directionalDensity_measurable α hv hk
  have hboundV (y : Space) : ‖directionalDensity α v k y‖ ≤
      (3+α)*(sumAmplitude u v y^(2+α)*‖k y‖) := by
    have ht := densityDerivative_action_bound_right (by linarith : 1<3+α) (u y) (v y) (k y)
    simpa only [directionalDensity,sumAmplitude,show 3+α-1=2+α by ring,mul_assoc] using ht
  obtain ⟨hVi,hVn⟩ := riesz_fibre_norm_const_domination hc x hmV hY hboundV
  have hboundD (y : Space) : ‖directionalDensity α u h y-directionalDensity α v k y‖ ≤
      (3+α)*(sumAmplitude u v y^(2+α)*‖h y-k y‖)+
      ((3+α)*(2+α))*(sumAmplitude u v y^(1+α)*differenceAmplitude u v y*‖k y‖) := by
    have ht := densityDerivative_action_difference (by linarith : 3<3+α) (u y) (v y) (h y) (k y)
    simpa only [directionalDensity,sumAmplitude,differenceAmplitude,show 3+α-1=2+α by ring,
      show 3+α-2=1+α by ring,mul_assoc] using ht
  obtain ⟨hDi,hDn⟩ := riesz_two_envelope_domain hc x (hmU.sub hmV) hZ hWY hboundD
  have hUi : Integrable (fun y => rieszKernel α c (x-y)*directionalDensity α u h y) volume := by
    apply (hDi.add hVi).congr
    filter_upwards [] with y
    simp only [Pi.add_apply,Pi.sub_apply]
    ring
  refine ⟨hUi,hVi,hVn,?_⟩
  rw [riesz_subtraction_of_domains x hUi hVi] at hDn
  exact hDn

#print axioms directional_density_pair_envelopes
end HartreeF.DerivativeMajorization
