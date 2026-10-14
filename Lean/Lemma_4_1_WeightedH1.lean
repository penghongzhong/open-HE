import Lemma_4_1_Stieltjes

/-! Transfer of the proved radial estimate to actual H1 functions.
The sole new standard interface is smooth H1 density expressed in unweighted
L1 polynomial moments; see E-H1-DENSITY in EXTERNAL_INTERFACES.txt.
All weighted limits and the paper-specific inequality are proved below. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace BWork.Kelvin

/-- Strong L1 convergence with explicit integrability, using actual functions. -/
def L1Converges (F : ℕ → Space → ℝ) (f : Space → ℝ) : Prop :=
  (∀ n,Integrable (F n)) ∧ Integrable f ∧
    Tendsto (fun n => ∫ z,‖F n z-f z‖) atTop (𝓝 0)

/-- Standard Cc∞ density in H1(R3), Sobolev embedding H1 → L6, and
continuity of h ↦ h^k from Lk to L1 (k=2,6). It contains no weights,
radial geometry, sharp constants, tail estimates or nonlinear inequality. -/
def SmoothH1MomentDensity : Prop :=
  ∀ (u : Space → ℝ) (D : Space → Space →L[ℝ] ℝ),InH1 u D →
    ∃ φ : ℕ → Space → ℝ,
      (∀ n,ContDiff ℝ ∞ (φ n) ∧ HasCompactSupport (φ n)) ∧
      L1Converges (fun n z => φ n z^6) (fun z => u z^6) ∧
      ∀ e : Space,L1Converges (fun n z => (fderiv ℝ (φ n) z e)^2) (fun z => (D z e)^2)

/-- Bounded measurable multipliers preserve convergence of actual integrals. -/
theorem L1Converges.weighted_integral {F : ℕ → Space → ℝ} {f w : Space → ℝ}
    (h : L1Converges F f) (hw : AEStronglyMeasurable w volume)
    {M : ℝ} (hM : ∀ z,‖w z‖ ≤ M) :
    Tendsto (fun n => ∫ z,w z*F n z) atTop (𝓝 (∫ z,w z*f z)) := by
  have hi (n : ℕ) := (h.1 n).bdd_mul hw (Eventually.of_forall hM)
  have hf := h.2.1.bdd_mul hw (Eventually.of_forall hM)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (by simpa using h.2.2.const_mul M)
  rw [← integral_sub (hi n) hf]
  calc
    ‖∫ z,w z*F n z-w z*f z‖ ≤ ∫ z,‖w z*F n z-w z*f z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z,M*‖F n z-f z‖ := by
      apply integral_mono ((hi n).sub hf).norm (((h.1 n).sub h.2.1).norm.const_mul M)
      intro z
      dsimp only [Pi.sub_apply]
      rw [← mul_sub,norm_mul]
      exact mul_le_mul_of_nonneg_right (hM z) (norm_nonneg _)
    _ = M*(∫ z,‖F n z-f z‖) := integral_const_mul _ _

theorem L1Converges.integral {F : ℕ → Space → ℝ} {f : Space → ℝ}
    (h : L1Converges F f) :
    Tendsto (fun n => ∫ z,F n z) atTop (𝓝 (∫ z,f z)) := by
  simpa only [one_mul] using h.weighted_integral
    (w := fun _ => 1) aestronglyMeasurable_const (M := 1) (fun _ => by norm_num)

theorem radialWeight_measurable {b : ℝ → ℝ} (hb : MonotoneOn b (Ici 0)) :
    Measurable (radialWeight b) := by
  have hm : Monotone (fun t => b (Real.sqrt t)) :=
    fun _ _ h => hb (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt h)
  exact hm.measurable.comp radiusSq_contDiff.continuous.measurable

theorem radialWeight_bounded {b : ℝ → ℝ} (h₀ : ∀ r,0 ≤ r → 0 ≤ b r)
    {M : ℝ} (hM : ∀ r,0 ≤ r → b r ≤ M) (z : Space) : ‖radialWeight b z‖ ≤ M := by
  unfold radialWeight
  rw [Real.norm_eq_abs,abs_of_nonneg (h₀ _ (Real.sqrt_nonneg _))]
  exact hM _ (Real.sqrt_nonneg _)

theorem radialWeight_integrable {b : ℝ → ℝ} (hb : MonotoneOn b (Ici 0))
    (h₀ : ∀ r,0 ≤ r → 0 ≤ b r) (hbound : ∃ M,∀ r,0 ≤ r → b r ≤ M)
    {F : Space → ℝ} (hF : Integrable F) : Integrable (fun z => radialWeight b z*F z) := by
  obtain ⟨M,hM⟩ := hbound
  exact hF.bdd_mul (radialWeight_measurable hb).aestronglyMeasurable
    (Eventually.of_forall (radialWeight_bounded h₀ hM))

theorem radialWeight_H1_integrable {G : ℝ} (sharp : SharpSobolev G)
    {u : Space → ℝ} {D : Space → Space →L[ℝ] ℝ} (hu : InH1 u D)
    {b : ℝ → ℝ} (hb : MonotoneOn b (Ici 0)) (h₀ : ∀ r,0 ≤ r → 0 ≤ b r)
    (hbound : ∃ M,∀ r,0 ≤ r → b r ≤ M) :
    Integrable (fun z => radialWeight b z*u z^6) ∧
      Integrable (fun z => radialWeight b z*longitudinalDensity D z) := by
  exact ⟨radialWeight_integrable hb h₀ hbound (sharp u D hu).1,
    radialWeight_integrable hb h₀ hbound (longitudinalDensity_integrable hu.2.1)⟩

/-- Equation (14), including arbitrary bounded monotone weights and actual
real H1 functions with their chosen weak derivative. -/
theorem radialWeight_anisotropic_H1 {G : ℝ} (hG : 0 < G)
    (sharp : SharpSobolev G) (pullback : LinearSobolevPullback)
    (glue : SmoothInterfaceGluing) (density : SmoothH1MomentDensity)
    {u : Space → ℝ} {D : Space → Space →L[ℝ] ℝ} (hu : InH1 u D)
    {b : ℝ → ℝ} (hb : MonotoneOn b (Ici 0)) (h₀ : ∀ r,0 ≤ r → 0 ≤ b r)
    (hbound : ∃ M,∀ r,0 ≤ r → b r ≤ M) :
    (∫ z,radialWeight b z*u z^6) ≤
      (54/G^2*(∫ z,transverseDensity D z)^2)*
        ∫ z,radialWeight b z*longitudinalDensity D z := by
  obtain ⟨φ,hφ,h6,h2⟩ := density u D hu
  obtain ⟨M,hM⟩ := hbound
  have hwm : AEStronglyMeasurable (radialWeight b) volume := (radialWeight_measurable hb).aestronglyMeasurable
  have hwb := radialWeight_bounded h₀ hM
  have hV := h6.weighted_integral hwm hwb
  have hB := (h2 (1,0)).weighted_integral hwm hwb
  have hA₁ := (h2 (0,(1,0))).integral
  have hA₂ := (h2 (0,(0,1))).integral
  have hA : Tendsto (fun n => ∫ z,transverseDensity (fderiv ℝ (φ n)) z)
      atTop (𝓝 (∫ z,transverseDensity D z)) := by
    have hn (n : ℕ) : (∫ z,transverseDensity (fderiv ℝ (φ n)) z) =
        (∫ z,(fderiv ℝ (φ n) z (0,(1,0)))^2)+
          ∫ z,(fderiv ℝ (φ n) z (0,(0,1)))^2 :=
      integral_add ((h2 (0,(1,0))).1 n) ((h2 (0,(0,1))).1 n)
    have he : (∫ z,transverseDensity D z) =
        (∫ z,(D z (0,(1,0)))^2)+∫ z,(D z (0,(0,1)))^2 :=
      integral_add (h2 (0,(1,0))).2.1 (h2 (0,(0,1))).2.1
    simp_rw [hn,he]
    exact hA₁.add hA₂
  apply le_of_tendsto_of_tendsto hV ((hA.pow 2).const_mul (54/G^2) |>.mul hB)
  exact Eventually.of_forall (fun n => radialWeight_anisotropic_smooth hG sharp pullback glue
    (hφ n).1 (hφ n).2 hb h₀ ⟨M,hM⟩)

#print axioms L1Converges.weighted_integral
#print axioms L1Converges.integral
#print axioms radialWeight_measurable
#print axioms radialWeight_bounded
#print axioms radialWeight_integrable
#print axioms radialWeight_H1_integrable
#print axioms radialWeight_anisotropic_H1
end BWork.Kelvin
