import FGeneralGradientCoordinates

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.GeneralProfileCross
open TimeHolder ProfileApproximation ProfileSpatialSmoothing SobolevStretch CompactCross
  CriticalAffine AffineMixed EnergySpace CriticalTimeSobolev ForcingDomain DerivativeMajorization

/-- The totalized scalar Riesz integral respects a.e. equality without an integrability premise. -/
theorem rieszConvolution_congr_ae (α c : ℝ) {f g : Space → ℝ}
    (h : f =ᵐ[volume] g) (x : Space) : rieszConvolution α c f x = rieszConvolution α c g x := by
  apply integral_congr_ae
  filter_upwards [h] with y hy
  rw [hy]

theorem potential_congr_ae (α c : ℝ) {u v : Space → ℂ}
    (h : u =ᵐ[volume] v) (x : Space) : potential α c u x = potential α c v x := by
  apply integral_congr_ae
  filter_upwards [h] with y hy
  simp only [powerDensity, hy]

/-- The input equalities are nested time/space a.e.; canonical joint measurability is unnecessary. -/
theorem innerCross_congr_nested_ae (α c : ℝ) {u u' h h' v v' : ℝ → Space → ℂ}
    (hu : ∀ᵐ t ∂volume, u t =ᵐ[volume] u' t)
    (hh : ∀ᵐ t ∂volume, h t =ᵐ[volume] h' t)
    (hv : ∀ᵐ t ∂volume, v t =ᵐ[volume] v' t) :
    ∀ᵐ t ∂volume, innerCross α c u h v t =ᵐ[volume] innerCross α c u' h' v' t := by
  filter_upwards [hu, hh, hv] with t hut hht hvt
  have hd : directionalDensity α (u t) (h t) =ᵐ[volume] directionalDensity α (u' t) (h' t) := by
    filter_upwards [hut, hht] with x hux hhx
    simp only [directionalDensity, hux, hhx]
  filter_upwards [hvt] with x hvx
  simp only [innerCross, rieszConvolution_congr_ae α c hd x, hvx]

theorem outerCross_congr_nested_ae (α c : ℝ) {u u' v v' k k' : ℝ → Space → ℂ}
    (hu : ∀ᵐ t ∂volume, u t =ᵐ[volume] u' t)
    (hv : ∀ᵐ t ∂volume, v t =ᵐ[volume] v' t)
    (hk : ∀ᵐ t ∂volume, k t =ᵐ[volume] k' t) :
    ∀ᵐ t ∂volume, outerCross α c u v k t =ᵐ[volume] outerCross α c u' v' k' t := by
  filter_upwards [hu, hv, hk] with t hut hvt hkt
  filter_upwards [hvt, hkt] with x hvx hkx
  simp only [outerCross, potential_congr_ae α c hut x, hvx, hkx]

theorem forcingNorm_congr_nested_ae {f g : ℝ → Space → ℂ}
    (h : ∀ᵐ t ∂volume, f t =ᵐ[volume] g t) : forcingNorm f = forcingNorm g := by
  apply eLpNorm_congr_ae
  exact h.mono fun _ ht => eLpNorm_congr_ae ht

theorem innerCross_forcingNorm_congr_nested_ae (α c : ℝ) {u u' h h' v v' : ℝ → Space → ℂ}
    (hu : ∀ᵐ t ∂volume, u t =ᵐ[volume] u' t)
    (hh : ∀ᵐ t ∂volume, h t =ᵐ[volume] h' t)
    (hv : ∀ᵐ t ∂volume, v t =ᵐ[volume] v' t) :
    forcingNorm (innerCross α c u h v) = forcingNorm (innerCross α c u' h' v') :=
  forcingNorm_congr_nested_ae (innerCross_congr_nested_ae α c hu hh hv)

theorem outerCross_forcingNorm_congr_nested_ae (α c : ℝ) {u u' v v' k k' : ℝ → Space → ℂ}
    (hu : ∀ᵐ t ∂volume, u t =ᵐ[volume] u' t)
    (hv : ∀ᵐ t ∂volume, v t =ᵐ[volume] v' t)
    (hk : ∀ᵐ t ∂volume, k t =ᵐ[volume] k' t) :
    forcingNorm (outerCross α c u v k) = forcingNorm (outerCross α c u' v' k') :=
  forcingNorm_congr_nested_ae (outerCross_congr_nested_ae α c hu hv hk)

/-- Positive affine spatial maps preserve arbitrary a.e. predicates. -/
theorem affine_ae_pullback {a : ℝ} (ha : 0 < a) (b : Space) {P : Space → Prop}
    (h : ∀ᵐ x ∂volume, P x) : ∀ᵐ x ∂volume, P (affine a b x) := by
  apply (affineHomeomorph ha.ne' b).toMeasurableEquiv.measurableEmbedding.ae_map_iff.mp
  change ∀ᵐ x ∂Measure.map (affine a b) volume, P x
  rw [affine_map_volume ha b]
  exact Measure.ae_smul_measure h _

theorem timeAffine_ae_pullback {a : ℝ} (ha : 0 < a) (s : ℝ) {P : ℝ → Prop}
    (h : ∀ᵐ t ∂volume, P t) : ∀ᵐ t ∂volume, P (timeAffine a s t) := by
  apply (timeAffineHomeomorph ha s).toMeasurableEquiv.measurableEmbedding.ae_map_iff.mp
  change ∀ᵐ t ∂Measure.map (timeAffine a s) volume, P t
  rw [timeAffine_map_volume ha s]
  exact Measure.ae_smul_measure h _

/-- Literal physical frames preserve nested a.e. equality, with their original time shift. -/
theorem seedFrame_congr_nested_ae {a : ℝ} (ha : 0 < a) (y : Space) (s w : ℝ)
    {f g : ℝ → Space → ℂ} (h : ∀ᵐ t ∂volume, f t =ᵐ[volume] g t) :
    ∀ᵐ t ∂volume, seedFrame a y s w f t =ᵐ[volume] seedFrame a y s w g t := by
  filter_upwards [timeAffine_ae_pullback (inv_pos.mpr ha) s h] with t ht
  filter_upwards [affine_ae_pullback (inv_pos.mpr ha) (-(a⁻¹ • y)) ht] with x hx
  simp only [seedFrame, parabolicField, hx]

/-- Value representative identity for the genuine homogeneous EnergyState. -/
theorem jointFields_value_nested_ae (g : ℝ → EnergyState) (r : EnergyJointFields volume g) :
    ∀ᵐ t ∂volume, stateValueField g t =ᵐ[volume] r.u t :=
  r.slice_eq.mono fun _ ht => ht.1.symm

/-- Each scalar direction is the actual complex weak derivative coordinate. -/
theorem jointFields_gradientCoordinate_nested_ae (g : ℝ → EnergyState)
    (r : EnergyJointFields volume g) (j : Fin 3) :
    ∀ᵐ t ∂volume, (energyGradient j (g t) : Space → ℂ) =ᵐ[volume]
      gradientCoordinate j (fun t => complexGradient (r.U t) (r.V t)) t := by
  filter_upwards [r.slice_eq] with t ht
  filter_upwards [ht.2.1, ht.2.2] with x hx hy
  simp only [gradientCoordinate, complexGradient, hx, hy]
  exact (state_complexGradient_coordinate (g t) x j).symm

theorem seedFrame_jointFields_value_nested_ae (g : ℝ → EnergyState)
    (r : EnergyJointFields volume g) {a : ℝ} (ha : 0 < a) (y : Space) (s : ℝ) :
    ∀ᵐ t ∂volume, seedFrame a y s (1/2) (stateValueField g) t =ᵐ[volume]
      seedFrame a y s (1/2) r.u t :=
  seedFrame_congr_nested_ae ha y s (1/2) (jointFields_value_nested_ae g r)

theorem seedFrame_jointFields_gradient_nested_ae (g : ℝ → EnergyState)
    (r : EnergyJointFields volume g) (j : Fin 3) {a : ℝ} (ha : 0 < a) (y : Space) (s : ℝ) :
    ∀ᵐ t ∂volume, seedFrame a y s (3/2) (fun t => (energyGradient j (g t) : Space → ℂ)) t =ᵐ[volume]
      seedFrame a y s (3/2) (gradientCoordinate j (fun t => complexGradient (r.U t) (r.V t))) t :=
  seedFrame_congr_nested_ae ha y s (3/2) (jointFields_gradientCoordinate_nested_ae g r j)

/-- All four literal scalar cross-forcing norms are unchanged by selecting joint representatives. -/
theorem framed_jointFields_four_forcingNorm_eq (α c : ℝ)
    (g₁ g₂ : ℝ → EnergyState) (r₁ : EnergyJointFields volume g₁) (r₂ : EnergyJointFields volume g₂)
    (j : Fin 3) {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (y₁ y₂ : Space) (s₁ s₂ : ℝ) :
    let u₁ := seedFrame a₁ y₁ s₁ (1/2) (stateValueField g₁)
    let u₂ := seedFrame a₂ y₂ s₂ (1/2) (stateValueField g₂)
    let h₁ := seedFrame a₁ y₁ s₁ (3/2) (fun t => (energyGradient j (g₁ t) : Space → ℂ))
    let h₂ := seedFrame a₂ y₂ s₂ (3/2) (fun t => (energyGradient j (g₂ t) : Space → ℂ))
    let v₁ := seedFrame a₁ y₁ s₁ (1/2) r₁.u
    let v₂ := seedFrame a₂ y₂ s₂ (1/2) r₂.u
    let k₁ := seedFrame a₁ y₁ s₁ (3/2) (gradientCoordinate j (fun t => complexGradient (r₁.U t) (r₁.V t)))
    let k₂ := seedFrame a₂ y₂ s₂ (3/2) (gradientCoordinate j (fun t => complexGradient (r₂.U t) (r₂.V t)))
    forcingNorm (innerCross α c u₁ h₁ u₂) = forcingNorm (innerCross α c v₁ k₁ v₂) ∧
    forcingNorm (outerCross α c u₁ u₂ h₂) = forcingNorm (outerCross α c v₁ v₂ k₂) ∧
    forcingNorm (innerCross α c u₂ h₂ u₁) = forcingNorm (innerCross α c v₂ k₂ v₁) ∧
    forcingNorm (outerCross α c u₂ u₁ h₁) = forcingNorm (outerCross α c v₂ v₁ k₁) := by
  have hv₁ := seedFrame_jointFields_value_nested_ae g₁ r₁ ha₁ y₁ s₁
  have hv₂ := seedFrame_jointFields_value_nested_ae g₂ r₂ ha₂ y₂ s₂
  have hg₁ := seedFrame_jointFields_gradient_nested_ae g₁ r₁ j ha₁ y₁ s₁
  have hg₂ := seedFrame_jointFields_gradient_nested_ae g₂ r₂ j ha₂ y₂ s₂
  exact ⟨innerCross_forcingNorm_congr_nested_ae α c hv₁ hg₁ hv₂,
    outerCross_forcingNorm_congr_nested_ae α c hv₁ hv₂ hg₂,
    innerCross_forcingNorm_congr_nested_ae α c hv₂ hg₂ hv₁,
    outerCross_forcingNorm_congr_nested_ae α c hv₂ hv₁ hg₁⟩

#print axioms innerCross_congr_nested_ae
#print axioms outerCross_congr_nested_ae
#print axioms seedFrame_congr_nested_ae
#print axioms jointFields_gradientCoordinate_nested_ae
#print axioms framed_jointFields_four_forcingNorm_eq
end HartreeF.GeneralProfileCross
