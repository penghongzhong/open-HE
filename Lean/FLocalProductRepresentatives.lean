import FLocalProductHolder
import FGeneralNestedNormTransport

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.LocalProfileProducts
open TimeHolder ProfileApproximation ProfileSpatialSmoothing GeneralProfileCross CompactCross
  EnergySpace CriticalTimeSobolev SobolevStretch

/-- Finite P and both ordered Q quantities follow from their actual finite S/W inputs. -/
theorem scalar_frame_PQQ_finite {u h v k : ℝ → Space → ℂ}
    (hu : ScalarProfile u h) (hv : ScalarProfile v k)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (y z : Space) (s r : ℝ) :
    localProductNorm 5 (seedFrame a y s (1/2) u) (seedFrame b z r (1/2) v) ≠ ∞ ∧
    localProductNorm (ENNReal.ofReal (15/8 : ℝ)) (seedFrame a y s (1/2) u) (seedFrame b z r (3/2) k) ≠ ∞ ∧
    localProductNorm (ENNReal.ofReal (15/8 : ℝ)) (seedFrame b z r (1/2) v) (seedFrame a y s (3/2) h) ≠ ∞ := by
  have hu' := hu.frame ha y s
  have hv' := hv.frame hb z r
  refine ⟨?_,?_,?_⟩
  · exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hu'.value_S hv'.value_S)
      (P_le _ _ hu'.value_joint.aestronglyMeasurable hv'.value_joint.aestronglyMeasurable hu'.value_S hv'.value_S)
  · exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hu'.value_S hv'.gradient_W)
      (Q_le _ _ hu'.value_joint.aestronglyMeasurable hv'.gradient_joint.aestronglyMeasurable hu'.value_S hv'.gradient_W)
  · exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hv'.value_S hu'.gradient_W)
      (Q_le _ _ hv'.value_joint.aestronglyMeasurable hu'.gradient_joint.aestronglyMeasurable hv'.value_S hu'.gradient_W)

/-- Nested representative equality transports the actual local product norm. -/
theorem localProductNorm_congr_nested_ae {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (q : ℝ≥0∞) {u U : ℝ → Space → E} {v V : ℝ → Space → F}
    (hu : ∀ᵐ t ∂volume, u t =ᵐ[volume] U t) (hv : ∀ᵐ t ∂volume, v t =ᵐ[volume] V t) :
    localProductNorm q u v = localProductNorm q U V := by
  apply mixedNorm_congr_nested_ae volume volume 5 q
  filter_upwards [hu,hv] with t hut hvt
  filter_upwards [hut,hvt] with x hux hvx
  simp only [normProduct,hux,hvx]

/-- P and both derivative-label Q norms use the original canonical EnergyState fields,
without presuming joint measurability of pointwise quotient representatives. -/
theorem framed_jointFields_PQQ_eq (g₁ g₂ : ℝ → EnergyState)
    (r₁ : EnergyJointFields volume g₁) (r₂ : EnergyJointFields volume g₂)
    (j : Fin 3) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (y z : Space) (s r : ℝ) :
    let u₁ := seedFrame a y s (1/2) (stateValueField g₁)
    let u₂ := seedFrame b z r (1/2) (stateValueField g₂)
    let h₁ := seedFrame a y s (3/2) (fun t => (energyGradient j (g₁ t) : Space → ℂ))
    let h₂ := seedFrame b z r (3/2) (fun t => (energyGradient j (g₂ t) : Space → ℂ))
    let v₁ := seedFrame a y s (1/2) r₁.u
    let v₂ := seedFrame b z r (1/2) r₂.u
    let k₁ := seedFrame a y s (3/2) (gradientCoordinate j (fun t => complexGradient (r₁.U t) (r₁.V t)))
    let k₂ := seedFrame b z r (3/2) (gradientCoordinate j (fun t => complexGradient (r₂.U t) (r₂.V t)))
    localProductNorm 5 u₁ u₂ = localProductNorm 5 v₁ v₂ ∧
    localProductNorm (ENNReal.ofReal (15/8 : ℝ)) u₁ h₂ = localProductNorm (ENNReal.ofReal (15/8 : ℝ)) v₁ k₂ ∧
    localProductNorm (ENNReal.ofReal (15/8 : ℝ)) u₂ h₁ = localProductNorm (ENNReal.ofReal (15/8 : ℝ)) v₂ k₁ := by
  have hu₁ := seedFrame_jointFields_value_nested_ae g₁ r₁ ha y s
  have hu₂ := seedFrame_jointFields_value_nested_ae g₂ r₂ hb z r
  have hh₁ := seedFrame_jointFields_gradient_nested_ae g₁ r₁ j ha y s
  have hh₂ := seedFrame_jointFields_gradient_nested_ae g₂ r₂ j hb z r
  exact ⟨localProductNorm_congr_nested_ae 5 hu₁ hu₂,
    localProductNorm_congr_nested_ae _ hu₁ hh₂,localProductNorm_congr_nested_ae _ hu₂ hh₁⟩

#print axioms scalar_frame_PQQ_finite
#print axioms framed_jointFields_PQQ_eq
end HartreeF.LocalProfileProducts
