import FGeneralPackedCross
import FGeneralNestedNormTransport

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.GeneralProfileCross
open TimeHolder ProfileApproximation ProfileSpatialSmoothing CompactCross CrossContinuity AffineMixed CriticalAffine EnergySpace CriticalTimeSobolev SobolevStretch

/-- The actual packed derivative is acted on with its true homogeneous weight 3/2. -/
def gradientFrame (a : ℝ) (y : Space) (s : ℝ) (G : ℝ → Space → CGradient) : ℝ → Space → CGradient :=
  parabolicField a⁻¹ (-(a⁻¹ • y)) s (3/2) G

theorem gradientFrame_coordinate (a : ℝ) (y : Space) (s : ℝ)
    (G : ℝ → Space → CGradient) (j : Fin 3) :
    (fun t x => gradientFrame a y s G t x j) = seedFrame a y s (3/2) (gradientCoordinate j G) := by
  rfl

theorem gradientFrame_joint_stronglyMeasurable (a : ℝ) (y : Space) (s : ℝ)
    (G : ℝ → Space → CGradient) (hG : StronglyMeasurable (fun z : ℝ × Space => G z.1 z.2)) :
    StronglyMeasurable (fun z : ℝ × Space => gradientFrame a y s G z.1 z.2) := by
  have hc : Continuous (fun z : ℝ × Space =>
      (timeAffine a⁻¹ s z.1, affine a⁻¹ (-(a⁻¹ • y)) z.2)) := by
    unfold timeAffine affine
    fun_prop
  exact (hG.comp_measurable hc.measurable).const_smul ((a⁻¹) ^ (3/2 : ℝ))

/-- The canonical packed gradient and the jointly measurable realization agree after framing. -/
theorem gradientFrame_jointFields_nested_ae (g : ℝ → EnergyState)
    (r : EnergyJointFields volume g) {a : ℝ} (ha : 0 < a) (y : Space) (s : ℝ) :
    ∀ᵐ t ∂volume,
      gradientFrame a y s (fun t => complexGradient (stateRealGradientField g t) (stateImagGradientField g t)) t =ᵐ[volume]
      gradientFrame a y s (fun t => complexGradient (r.U t) (r.V t)) t := by
  apply packedGradient_congr_nested_ae volume volume
  intro j
  have hh := seedFrame_jointFields_gradient_nested_ae g r j ha y s
  rw [← gradientCoordinate_state g j] at hh
  filter_upwards [hh] with t ht
  filter_upwards [ht] with x hx
  rw [congrFun (congrFun (gradientFrame_coordinate a y s _ j) t) x,
    congrFun (congrFun (gradientFrame_coordinate a y s _ j) t) x]
  exact hx

/-- Literal packed inner-cross equality needs only nested a.e. equality of its inputs. -/
theorem packedInnerCross_congr_nested_ae (α c : ℝ)
    {u U v V : ℝ → Space → ℂ} {H K : ℝ → Space → CGradient}
    (hu : ∀ᵐ t ∂volume, u t =ᵐ[volume] U t)
    (hH : ∀ᵐ t ∂volume, H t =ᵐ[volume] K t)
    (hv : ∀ᵐ t ∂volume, v t =ᵐ[volume] V t) :
    ∀ᵐ t ∂volume, packedInnerCross α c u H v t =ᵐ[volume] packedInnerCross α c U K V t := by
  apply packedGradient_congr_nested_ae volume volume
  intro j
  have hh : ∀ᵐ t ∂volume, (fun x => H t x j) =ᵐ[volume] (fun x => K t x j) :=
    hH.mono fun _ ht => ht.mono fun _ hx => congrArg (fun z : CGradient => z j) hx
  have he := innerCross_congr_nested_ae α c hu hh hv
  filter_upwards [he] with t ht
  filter_upwards [ht] with x hx
  rw [congrFun (congrFun (packedInnerCross_coordinate α c u H v j) t) x,
    congrFun (congrFun (packedInnerCross_coordinate α c U K V j) t) x]
  exact hx

theorem packedOuterCross_congr_nested_ae (α c : ℝ)
    {u U v V : ℝ → Space → ℂ} {H K : ℝ → Space → CGradient}
    (hu : ∀ᵐ t ∂volume, u t =ᵐ[volume] U t)
    (hv : ∀ᵐ t ∂volume, v t =ᵐ[volume] V t)
    (hH : ∀ᵐ t ∂volume, H t =ᵐ[volume] K t) :
    ∀ᵐ t ∂volume, packedOuterCross α c u v H t =ᵐ[volume] packedOuterCross α c U V K t := by
  apply packedGradient_congr_nested_ae volume volume
  intro j
  have hh : ∀ᵐ t ∂volume, (fun x => H t x j) =ᵐ[volume] (fun x => K t x j) :=
    hH.mono fun _ ht => ht.mono fun _ hx => congrArg (fun z : CGradient => z j) hx
  have he := outerCross_congr_nested_ae α c hu hv hh
  filter_upwards [he] with t ht
  filter_upwards [ht] with x hx
  rw [congrFun (congrFun (packedOuterCross_coordinate α c u v H j) t) x,
    congrFun (congrFun (packedOuterCross_coordinate α c U V K j) t) x]
  exact hx

/-- Original-state and joint-representative vector N norms coincide, without presuming
joint measurability of the canonical quotient representatives. -/
theorem framed_jointFields_four_vectorNorm_eq (α c : ℝ)
    (g₁ g₂ : ℝ → EnergyState) (r₁ : EnergyJointFields volume g₁) (r₂ : EnergyJointFields volume g₂)
    {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (y₁ y₂ : Space) (s₁ s₂ : ℝ) :
    let u₁ := seedFrame a₁ y₁ s₁ (1/2) (stateValueField g₁)
    let u₂ := seedFrame a₂ y₂ s₂ (1/2) (stateValueField g₂)
    let h₁ := gradientFrame a₁ y₁ s₁ (fun t => complexGradient (stateRealGradientField g₁ t) (stateImagGradientField g₁ t))
    let h₂ := gradientFrame a₂ y₂ s₂ (fun t => complexGradient (stateRealGradientField g₂ t) (stateImagGradientField g₂ t))
    let v₁ := seedFrame a₁ y₁ s₁ (1/2) r₁.u
    let v₂ := seedFrame a₂ y₂ s₂ (1/2) r₂.u
    let k₁ := gradientFrame a₁ y₁ s₁ (fun t => complexGradient (r₁.U t) (r₁.V t))
    let k₂ := gradientFrame a₂ y₂ s₂ (fun t => complexGradient (r₂.U t) (r₂.V t))
    vectorForcingNorm (packedInnerCross α c u₁ h₁ u₂) = vectorForcingNorm (packedInnerCross α c v₁ k₁ v₂) ∧
    vectorForcingNorm (packedOuterCross α c u₁ u₂ h₂) = vectorForcingNorm (packedOuterCross α c v₁ v₂ k₂) ∧
    vectorForcingNorm (packedInnerCross α c u₂ h₂ u₁) = vectorForcingNorm (packedInnerCross α c v₂ k₂ v₁) ∧
    vectorForcingNorm (packedOuterCross α c u₂ u₁ h₁) = vectorForcingNorm (packedOuterCross α c v₂ v₁ k₁) := by
  have hv₁ := seedFrame_jointFields_value_nested_ae g₁ r₁ ha₁ y₁ s₁
  have hv₂ := seedFrame_jointFields_value_nested_ae g₂ r₂ ha₂ y₂ s₂
  have hg₁ := gradientFrame_jointFields_nested_ae g₁ r₁ ha₁ y₁ s₁
  have hg₂ := gradientFrame_jointFields_nested_ae g₂ r₂ ha₂ y₂ s₂
  exact ⟨mixedNorm_congr_nested_ae volume volume _ _ (packedInnerCross_congr_nested_ae α c hv₁ hg₁ hv₂),
    mixedNorm_congr_nested_ae volume volume _ _ (packedOuterCross_congr_nested_ae α c hv₁ hv₂ hg₂),
    mixedNorm_congr_nested_ae volume volume _ _ (packedInnerCross_congr_nested_ae α c hv₂ hg₂ hv₁),
    mixedNorm_congr_nested_ae volume volume _ _ (packedOuterCross_congr_nested_ae α c hv₂ hv₁ hg₁)⟩

#print axioms gradientFrame_jointFields_nested_ae
#print axioms framed_jointFields_four_vectorNorm_eq
end HartreeF.GeneralProfileCross
