import Lemma_4_1_Reparametrization
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Three exact energy identities for the actual regularized transformation. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace BWork.Kelvin

theorem reparametrized_transverse {τ : ℝ ≃ₜ ℝ} {q : ℝ} {z : Space}
    (hq : q ≠ 0) (hτ : HasDerivAt τ q z.1)
    {a : ℝ → ℝ} {a' : ℝ} (ha : HasDerivAt a a' z.1)
    {g : Space → ℝ} (hg : DifferentiableAt ℝ g z) :
    transverseDensity (fderiv ℝ (reparametrized τ a g)) (clockLift τ z) =
      a z.1^2*transverseDensity (fderiv ℝ g) z := by
  unfold transverseDensity transverseGradient
  rw [(reparametrized_hasFDerivAt_image hq hτ ha hg).fderiv]
  simp [s,amplitudeDerivative,dilation]
  ring

theorem reparametrized_longitudinal {τ : ℝ ≃ₜ ℝ} {q : ℝ} {z : Space}
    (hq : q ≠ 0) (hτ : HasDerivAt τ q z.1)
    {a : ℝ → ℝ} {a' : ℝ} (ha : HasDerivAt a a' z.1)
    {g : Space → ℝ} (hg : DifferentiableAt ℝ g z) :
    fderiv ℝ (reparametrized τ a g) (clockLift τ z) (1,0) =
      q⁻¹*(a z.1*fderiv ℝ g z (1,0)+a'*g z) := by
  rw [(reparametrized_hasFDerivAt_image hq hτ ha hg).fderiv]
  rw [ContinuousLinearMap.comp_apply,dilation_apply]
  simp only [mul_one]
  change a z.1*fderiv ℝ g z (q⁻¹,0)+(a'*g z)*q⁻¹ = _
  have he : (q⁻¹,(0 : Plane)) = q⁻¹ • ((1 : ℝ),(0 : Plane)) := by simp
  rw [he,map_smul,smul_eq_mul]
  ring

def regularizedEnergy (h h' ε g gs : ℝ) : ℝ :=
  (h^2+ε)*gs^2+h*h'*g*gs+(h^2*h'^2)/(4*(h^2+ε))*g^2

theorem regularized_energy_algebra (h h' g gs : ℝ) {ε a : ℝ}
    (ha : 0 < a) (ha4 : a^4=h^2+ε) :
    (a^2)⁻¹*((a^2)*(a*gs+(h*h'/(2*a^3))*g))^2 =
      regularizedEnergy h h' ε g gs := by
  unfold regularizedEnergy
  rw [← ha4]
  field_simp
  ring

theorem regularized_transverse_integral {τ : ℝ ≃ₜ ℝ} {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) {ε : ℝ} (hε : 0 < ε)
    (hτ : ∀ s,HasDerivAt τ (clockSpeed h ε s) s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) :
    (∫ z,transverseDensity (fderiv ℝ (reparametrized τ (quarterAmplitude h ε) g)) z) =
      ∫ z,transverseDensity (fderiv ℝ g) z := by
  have hq (s : ℝ) : 0 < clockSpeed h ε s := inv_pos.mpr (Real.sqrt_pos.mpr (regularizedH_pos h hε s))
  rw [clockLift_integral τ (clockSpeed h ε) hq hτ]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [reparametrized_transverse (hq z.1).ne' (hτ z.1)
    (quarterAmplitude_hasDerivAt ((hh.differentiable (by norm_num)) z.1).hasDerivAt hε)
    (hg.differentiable (by norm_num) z),clockSpeed_eq]
  have ha := (quarterAmplitude_pos h hε z.1).ne'
  field_simp

theorem regularized_sixth_integral (τ : ℝ ≃ₜ ℝ) {h : ℝ → ℝ} {ε : ℝ}
    (hε : 0 < ε) (hτ : ∀ s,HasDerivAt τ (clockSpeed h ε s) s)
    (b : ℝ → ℝ) (a : Plane) (g : Space → ℝ) :
    (∫ z,centeredWeight b a z*(reparametrized τ (quarterAmplitude h ε) g z)^6) =
      ∫ z,centeredWeight b a z*regularizedH h ε z.1*g z^6 := by
  have hq (s : ℝ) : 0 < clockSpeed h ε s := inv_pos.mpr (Real.sqrt_pos.mpr (regularizedH_pos h hε s))
  rw [clockLift_integral τ (clockSpeed h ε) hq hτ]
  apply integral_congr_ae
  filter_upwards [] with z
  have hb : centeredWeight b a (clockLift τ z) = centeredWeight b a z := rfl
  rw [hb,reparametrized_on_image,clockSpeed_eq,← quarterAmplitude_fourth h hε z.1]
  have ha := (quarterAmplitude_pos h hε z.1).ne'
  field_simp

theorem regularized_longitudinal_integral {τ : ℝ ≃ₜ ℝ} {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) {ε : ℝ} (hε : 0 < ε)
    (hτ : ∀ s,HasDerivAt τ (clockSpeed h ε s) s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (b : ℝ → ℝ) (a : Plane) :
    (∫ z,centeredWeight b a z*
      longitudinalDensity (fderiv ℝ (reparametrized τ (quarterAmplitude h ε) g)) z) =
      ∫ z,centeredWeight b a z*
        regularizedEnergy (h z.1) (deriv h z.1) ε (g z) (fderiv ℝ g z (1,0)) := by
  have hq (s : ℝ) : 0 < clockSpeed h ε s := inv_pos.mpr (Real.sqrt_pos.mpr (regularizedH_pos h hε s))
  rw [clockLift_integral τ (clockSpeed h ε) hq hτ]
  apply integral_congr_ae
  filter_upwards [] with z
  have hb : centeredWeight b a (clockLift τ z) = centeredWeight b a z := rfl
  unfold longitudinalDensity
  rw [hb,reparametrized_longitudinal (hq z.1).ne' (hτ z.1)
    (quarterAmplitude_hasDerivAt ((hh.differentiable (by norm_num)) z.1).hasDerivAt hε)
    (hg.differentiable (by norm_num) z),clockSpeed_eq,inv_inv]
  rw [show (quarterAmplitude h ε z.1^2)⁻¹ *
      (centeredWeight b a z*(quarterAmplitude h ε z.1^2 *
        (quarterAmplitude h ε z.1*fderiv ℝ g z (1,0)+
          h z.1*deriv h z.1/(2*quarterAmplitude h ε z.1^3)*g z))^2) =
      centeredWeight b a z*((quarterAmplitude h ε z.1^2)⁻¹ *
        (quarterAmplitude h ε z.1^2 *
          (quarterAmplitude h ε z.1*fderiv ℝ g z (1,0)+
            h z.1*deriv h z.1/(2*quarterAmplitude h ε z.1^3)*g z))^2) by ring]
  rw [regularized_energy_algebra _ _ _ _ (quarterAmplitude_pos h hε z.1)
    (quarterAmplitude_fourth h hε z.1)]

/-- The three proved change-of-variables formulas are applied to the concrete
regularized clock and the proved weighted Sobolev inequality. -/
theorem regularized_weighted_estimate {G : ℝ} (hG : 0 < G)
    (sharp : SharpSobolev G) (pullback : LinearSobolevPullback)
    (glue : SmoothInterfaceGluing) (density : SmoothH1MomentDensity)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) {ε M : ℝ} (hε : 0 < ε)
    (hbound : ∀ s,h s^2 ≤ M)
    {b : ℝ → ℝ} (hb : MonotoneOn b (Ici 0)) (h₀ : ∀ r,0 ≤ r → 0 ≤ b r)
    (hbnd : ∃ B,∀ r,0 ≤ r → b r ≤ B) (a : Plane) :
    (∫ z,centeredWeight b a z*regularizedH h ε z.1*g z^6) ≤
      (54/G^2*(∫ z,transverseDensity (fderiv ℝ g) z)^2)*
        ∫ z,centeredWeight b a z*
          regularizedEnergy (h z.1) (deriv h z.1) ε (g z) (fderiv ℝ g z (1,0)) := by
  let τ := regularizedClock h hh hε hbound
  let v := reparametrized τ (quarterAmplitude h ε) g
  have hv := reparametrized_contDiff (regularizedClock_inverse_contDiff h hh hε hbound)
    (quarterAmplitude_contDiff hh hε) hg
  have hvc := reparametrized_compact τ (quarterAmplitude h ε) hc
  have hvH : InH1 v (fderiv ℝ v) := by
    have he := glue (fun _ => (1 : ℝ)) v v contDiff_const
      (fun z hz => by norm_num at hz) (hv.of_le (by norm_num)) (hv.of_le (by norm_num))
      (fun _ _ => rfl)
    simpa only [not_lt_of_ge zero_le_one,ite_false] using he (by simpa using hvc)
  have he := centeredWeight_anisotropic_H1 hG sharp pullback glue density hvH hb h₀ hbnd a
  have hτ := regularizedClock_hasDerivAt h hh hε hbound
  change (∫ z,centeredWeight b a z*(reparametrized τ (quarterAmplitude h ε) g z)^6) ≤
    (54/G^2*(∫ z,transverseDensity (fderiv ℝ (reparametrized τ (quarterAmplitude h ε) g)) z)^2)*
      ∫ z,centeredWeight b a z*longitudinalDensity (fderiv ℝ (reparametrized τ (quarterAmplitude h ε) g)) z at he
  rw [regularized_sixth_integral τ hε hτ b a g,
    regularized_transverse_integral hh hε hτ hg,
    regularized_longitudinal_integral hh hε hτ hg b a] at he
  exact he

theorem longitudinal_section_deriv {g : Space → ℝ} (hg : Differentiable ℝ g) (a : Plane) (s : ℝ) :
    deriv (fun t => g (t,a)) s = fderiv ℝ g (s,a) (1,0) := by
  have he := (hg (s,a)).hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s a))
  exact he.deriv

/-- Actual fixed-center slice estimate: no clock, transformed function,
energy identity, or section bound is assumed. All are constructed from g. -/
theorem regularized_section_estimate {G : ℝ} (hG : 0 < G)
    (sharp : SharpSobolev G) (pullback : LinearSobolevPullback)
    (glue : SmoothInterfaceGluing) (density : SmoothH1MomentDensity)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    {ε : ℝ} (hε : 0 < ε)
    {b : ℝ → ℝ} (hb : MonotoneOn b (Ici 0)) (h₀ : ∀ r,0 ≤ r → 0 ≤ b r)
    (hbnd : ∃ B,∀ r,0 ≤ r → b r ≤ B) (a : Plane) :
    (∫ z,centeredWeight b a z*(g (z.1,a)^2+ε)*g z^6) ≤
      (54/G^2*(∫ z,transverseDensity (fderiv ℝ g) z)^2)*
        ∫ z,centeredWeight b a z*
          regularizedEnergy (g (z.1,a)) (fderiv ℝ g (z.1,a) (1,0)) ε (g z) (fderiv ℝ g z (1,0)) := by
  obtain ⟨M,_,hM⟩ := compact_function_sq_bound hg.continuous hc
  have hh : ContDiff ℝ ∞ (fun t => g (t,a)) := hg.comp (contDiff_id.prodMk contDiff_const)
  have he := regularized_weighted_estimate hG sharp pullback glue density hg hc hh hε
    (fun s => hM (s,a)) hb h₀ hbnd a
  simp_rw [longitudinal_section_deriv (hg.differentiable (by norm_num)),regularizedH] at he
  exact he

#print axioms reparametrized_transverse
#print axioms reparametrized_longitudinal
#print axioms regularized_energy_algebra
#print axioms regularized_transverse_integral
#print axioms regularized_sixth_integral
#print axioms regularized_longitudinal_integral
#print axioms regularized_weighted_estimate
#print axioms longitudinal_section_deriv
#print axioms regularized_section_estimate
end BWork.Kelvin
