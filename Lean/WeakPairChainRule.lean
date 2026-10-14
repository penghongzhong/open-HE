import PairCompositionContinuity
import H1AESmoothApproximation

/-!
Native weak chain rule for a real C1 function of two real H1 fields.
The only external analysis input is ordinary H1 density. Every composition
and coefficient limit is produced from genuine classical calculus and actual
L2 convergence. In particular no weak chain-rule identity is a premise.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped RealInnerProductSpace NNReal ENNReal Topology
namespace HartreeF.ModulusGradient
open SobolevStretch StationarySelfTest WeakCutoffLp

theorem continuous_bounded_coefficient_memLp
    {u v : Space → ℝ} {a : ℝ × ℝ → ℝ} {G : Space → Space} {B : ℝ}
    (hu : AEStronglyMeasurable u volume) (hv : AEStronglyMeasurable v volume)
    (ha : Continuous a) (hab : ∀ z, ‖a z‖ ≤ B) (hG : MemLp G 2 volume) :
    MemLp (fun x => a (u x, v x) • G x) 2 volume := by
  have hcoef : MemLp (fun x => a (u x, v x)) ∞ volume :=
    memLp_top_of_bound (ha.comp_aestronglyMeasurable (hu.prodMk hv)) B
      (ae_of_all _ (fun x => hab (u x, v x)))
  exact hcoef.smul hG

/-- Classical calculus produces the literal gradient, then actual integration
by parts supplies HasWeakGradient against the genuine C-infinity test class. -/
theorem smooth_pair_hasWeakGradient
    {F a b : ℝ × ℝ → ℝ}
    (hF : Differentiable ℝ F) (ha : Continuous a) (hb : Continuous b)
    (hd : ∀ z w, fderiv ℝ F z w = a z * w.1 + b z * w.2)
    {φ ψ : Space → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    HasWeakGradient (fun x => F (φ x, ψ x))
      (fun x => a (φ x, ψ x) • gradient φ x + b (φ x, ψ x) • gradient ψ x) := by
  apply hasWeakGradient_of_differentiable
    (hF.comp ((hφ.differentiable (by simp)).prodMk (hψ.differentiable (by simp))))
    (((ha.comp (hφ.continuous.prodMk hψ.continuous)).smul
      (cutoff_gradient_continuous hφ)).add
      ((hb.comp (hφ.continuous.prodMk hψ.continuous)).smul
        (cutoff_gradient_continuous hψ)))
  intro x w
  have hc := (hF (φ x, ψ x)).hasFDerivAt.comp x
    (((hφ.differentiable (by simp)) x).hasFDerivAt.prodMk
      ((hψ.differentiable (by simp)) x).hasFDerivAt)
  rw [hc.fderiv]
  change fderiv ℝ F (φ x, ψ x) (fderiv ℝ φ x w, fderiv ℝ ψ x w) =
    ⟪a (φ x, ψ x) • gradient φ x + b (φ x, ψ x) • gradient ψ x, w⟫
  simp only [hd, inner_add_left, real_inner_smul_left, inner_gradient_left]

/-- Actual weak pair composition, derived from ordinary density. The derivative
formula here is solely the classical finite-dimensional Frechet derivative. -/
theorem hasWeakGradient_pair_comp (hDensity : OrdinaryH1Density)
    {F a b : ℝ × ℝ → ℝ} {K : ℝ≥0} {B : ℝ}
    (hF : Differentiable ℝ F) (hLip : LipschitzWith K F) (hzero : F 0 = 0)
    (ha : Continuous a) (hb : Continuous b)
    (hab : ∀ z, ‖a z‖ ≤ B) (hbb : ∀ z, ‖b z‖ ≤ B)
    (hd : ∀ z w, fderiv ℝ F z w = a z * w.1 + b z * w.2)
    {u v : Space → ℝ} {U V : Space → Space}
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hU : MemLp U 2 volume) (hV : MemLp V 2 volume)
    (hwu : HasWeakGradient u U) (hwv : HasWeakGradient v V) :
    HasWeakGradient (fun x => F (u x, v x))
      (fun x => a (u x, v x) • U x + b (u x, v x) • V x) := by
  obtain ⟨pu⟩ := ordinary_h1_ae_smooth_approximation hDensity hu hU hwu
  obtain ⟨pv⟩ := ordinary_h1_ae_smooth_approximation hDensity hv hV hwv
  have hp : MemLp (fun x => (u x, v x)) 2 volume := memLp_prod_iff.mpr ⟨hu, hv⟩
  have hpn (n : ℕ) : MemLp (fun x => (pu.seq n x, pv.seq n x)) 2 volume :=
    memLp_prod_iff.mpr ⟨pu.function_L2 n, pv.function_L2 n⟩
  have hca : MemLp (fun x => a (u x, v x) • U x) 2 volume :=
    continuous_bounded_coefficient_memLp hu.aestronglyMeasurable hv.aestronglyMeasurable ha hab hU
  have hcb : MemLp (fun x => b (u x, v x) • V x) 2 volume :=
    continuous_bounded_coefficient_memLp hu.aestronglyMeasurable hv.aestronglyMeasurable hb hbb hV
  have hcan (n : ℕ) : MemLp
      (fun x => a (pu.seq n x, pv.seq n x) • gradient (pu.seq n) x) 2 volume :=
    continuous_bounded_coefficient_memLp (pu.function_L2 n).aestronglyMeasurable
      (pv.function_L2 n).aestronglyMeasurable ha hab (pu.gradient_L2 n)
  have hcbn (n : ℕ) : MemLp
      (fun x => b (pu.seq n x, pv.seq n x) • gradient (pv.seq n) x) 2 volume :=
    continuous_bounded_coefficient_memLp (pu.function_L2 n).aestronglyMeasurable
      (pv.function_L2 n).aestronglyMeasurable hb hbb (pv.gradient_L2 n)
  have hae : ∀ᵐ x ∂volume, Tendsto (fun n => (pu.seq n x, pv.seq n x))
      atTop (𝓝 (u x, v x)) := by
    filter_upwards [pu.ae_tendsto, pv.ae_tendsto] with x hx hy
    exact hx.prodMk_nhds hy
  have hca_lim := bounded_varying_coefficient_smul_strong_l2
    (fun n => ha.comp_aestronglyMeasurable (hpn n).aestronglyMeasurable)
    (ha.comp_aestronglyMeasurable hp.aestronglyMeasurable) pu.gradient_L2 hU
    (fun n => ae_of_all _ (fun x => hab (pu.seq n x, pv.seq n x)))
    (ae_of_all _ (fun x => hab (u x, v x)))
    (hae.mono (fun x hx => (ha.tendsto _).comp hx)) pu.gradient_tendsto
  have hcb_lim := bounded_varying_coefficient_smul_strong_l2
    (fun n => hb.comp_aestronglyMeasurable (hpn n).aestronglyMeasurable)
    (hb.comp_aestronglyMeasurable hp.aestronglyMeasurable) pv.gradient_L2 hV
    (fun n => ae_of_all _ (fun x => hbb (pu.seq n x, pv.seq n x)))
    (ae_of_all _ (fun x => hbb (u x, v x)))
    (hae.mono (fun x hx => (hb.tendsto _).comp hx)) pv.gradient_tendsto
  apply hasWeakGradient_of_strong_l2_limit
    (hLip.comp_memLp hzero hp) (hca.add hcb)
    (fun n => hLip.comp_memLp hzero (hpn n)) (fun n => (hcan n).add (hcbn n))
    (fun n => smooth_pair_hasWeakGradient hF ha hb hd (pu.smooth n) (pv.smooth n))
  · exact lipschitz_comp_strong_l2 hLip hp.aestronglyMeasurable
      (fun n => (hpn n).aestronglyMeasurable)
      (strong_l2_pair_limit hu hv pu.function_L2 pv.function_L2
        pu.function_tendsto pv.function_tendsto)
  · convert strong_l2_zero_add hca_lim hcb_lim using 1
    funext n
    congr 1
    funext x
    simp only [Pi.sub_apply, Pi.add_apply]
    abel

#print axioms continuous_bounded_coefficient_memLp
#print axioms smooth_pair_hasWeakGradient
#print axioms hasWeakGradient_pair_comp
end HartreeF.ModulusGradient
