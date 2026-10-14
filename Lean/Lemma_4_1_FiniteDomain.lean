import Lemma_4_1_PairEnergy

/-! Instantiation of the finite-domain 9/4 bound with the paper's actual
radial kernel, smooth function, weak-gradient representative and Lebesgue measure. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace BWork.Kelvin

def radialPairKernel (b : ℝ → ℝ) (p : Plane × Plane) : ℝ :=
  b (Real.sqrt (s (p.1.1-p.2.1) (p.1.2-p.2.2)))

theorem radialPairKernel_centered (b : ℝ → ℝ) (z : Space) (a : Plane) :
    radialPairKernel b (z.2,a) = centeredWeight b a z := rfl

theorem radialPairKernel_symmetric (b : ℝ → ℝ) (y a : Plane) :
    radialPairKernel b (y,a) = radialPairKernel b (a,y) := by
  unfold radialPairKernel
  congr 2
  unfold s
  ring

theorem radialPairKernel_measurable {b : ℝ → ℝ} (hb : MonotoneOn b (Ici 0)) :
    Measurable (radialPairKernel b) := by
  have hm : Monotone (fun t => b (Real.sqrt t)) :=
    fun _ _ h => hb (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt h)
  have hc : Continuous (fun p : Plane × Plane => s (p.1.1-p.2.1) (p.1.2-p.2.2)) := by
    unfold s; fun_prop
  exact hm.measurable.comp hc.measurable

theorem radialPairKernel_nonneg {b : ℝ → ℝ} (hb : ∀ r,0 ≤ r → 0 ≤ b r) (p : Plane × Plane) :
    0 ≤ radialPairKernel b p := hb _ (Real.sqrt_nonneg _)

theorem radialPairKernel_le {b : ℝ → ℝ} {B : ℝ}
    (hB : ∀ r,0 ≤ r → b r ≤ B) (p : Plane × Plane) : radialPairKernel b p ≤ B :=
  hB _ (Real.sqrt_nonneg _)

def longitudinalDerivative (g : Space → ℝ) (z : Space) : ℝ := fderiv ℝ g z (1,0)

theorem longitudinalDerivative_continuous {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) :
    Continuous (longitudinalDerivative g) := by
  have hd := (hg.fderiv_right (m := 0) (by norm_num)).continuous
  exact (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ),(0 : Plane))).continuous.comp hd

theorem longitudinalDerivative_sq_integrable {g : Space → ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (Y : Set Plane) :
    Integrable (fun z => longitudinalDerivative g z^2) (volume.prod (volume.restrict Y)) := by
  have hd := (derivative_eval_memLp (compact_derivative_memLp hg hc) (1,0)).integrable_sq
  exact hd.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)

/-- All integrability assumptions required by the 9/4 consumer are constructed
from the paper's actual smooth compact function on any finite transverse domain. -/
theorem paper_pairMoments_integrable {g : Space → ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    {b : ℝ → ℝ} (hb : MonotoneOn b (Ici 0)) (h₀ : ∀ r,0 ≤ r → 0 ≤ b r)
    (hbound : ∃ B,∀ r,0 ≤ r → b r ≤ B) {Y : Set Plane} (hY : volume Y < ⊤) :
    Integrable (pairMass (radialPairKernel b) g (longitudinalDerivative g))
      (pairMeasure (volume.restrict Y)) ∧
    Integrable (pairError (radialPairKernel b) (longitudinalDerivative g))
      (pairMeasure (volume.restrict Y)) := by
  have : IsFiniteMeasure (volume.restrict Y) := isFiniteMeasure_restrict.mpr hY.ne
  obtain ⟨B,hB⟩ := hbound
  obtain ⟨M,_,hM⟩ := compact_function_sq_bound hg.continuous hc
  exact pairMoments_integrable (volume.restrict Y) (radialPairKernel_measurable hb)
    (radialPairKernel_nonneg h₀) (radialPairKernel_le hB) hg.continuous.measurable hM
    (longitudinalDerivative_sq_integrable hg hc Y)

/-- The actual finite-domain integrated 9/4 estimate; no pair integral,
measurability or symmetry assumption remains hidden in the input. -/
theorem paper_nine_quarters {g : Space → ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    {b : ℝ → ℝ} (hb : MonotoneOn b (Ici 0)) (h₀ : ∀ r,0 ≤ r → 0 ≤ b r)
    (hbound : ∃ B,∀ r,0 ≤ r → b r ≤ B) {Y : Set Plane} (hY : volume Y < ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ p,pairRegularizedEnergy (radialPairKernel b) g (longitudinalDerivative g) ε p
      ∂pairMeasure (volume.restrict Y)) ≤
    9/4*(∫ p,pairMass (radialPairKernel b) g (longitudinalDerivative g) p
      ∂pairMeasure (volume.restrict Y))+
    ε*∫ p,pairError (radialPairKernel b) (longitudinalDerivative g) p
      ∂pairMeasure (volume.restrict Y) := by
  have : IsFiniteMeasure (volume.restrict Y) := isFiniteMeasure_restrict.mpr hY.ne
  obtain ⟨hI,hC⟩ := paper_pairMoments_integrable hg hc hb h₀ hbound hY
  exact pairRegularizedEnergy_integral_le (volume.restrict Y)
    (radialPairKernel_measurable hb) (radialPairKernel_nonneg h₀) (radialPairKernel_symmetric b)
    hg.continuous.measurable (longitudinalDerivative_continuous hg).measurable hε hI hC

def transverseDomain (g : Space → ℝ) : Set Plane :=
  Prod.snd '' tsupport g ∪ Prod.snd '' tsupport (longitudinalDerivative g)

theorem longitudinalDerivative_compact {g : Space → ℝ} (hc : HasCompactSupport g) :
    HasCompactSupport (longitudinalDerivative g) :=
  (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] ℝ => L (1,0)) rfl

theorem transverseDomain_compact {g : Space → ℝ} (hc : HasCompactSupport g) :
    IsCompact (transverseDomain g) :=
  (hc.image continuous_snd).union ((longitudinalDerivative_compact hc).image continuous_snd)

theorem transverseDomain_finite {g : Space → ℝ} (hc : HasCompactSupport g) :
    volume (transverseDomain g) < ⊤ := (transverseDomain_compact hc).measure_lt_top

theorem zero_outside_transverseDomain (g : Space → ℝ) {z : Space}
    (hz : z.2 ∉ transverseDomain g) : g z = 0 ∧ longitudinalDerivative g z = 0 := by
  constructor
  · by_contra hg
    exact hz (Or.inl ⟨z,subset_closure hg,rfl⟩)
  · by_contra hd
    exact hz (Or.inr ⟨z,subset_closure hd,rfl⟩)

/-- The finite transverse domain is itself constructed from the input g. -/
theorem paper_nine_quarters_on_support {g : Space → ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    {b : ℝ → ℝ} (hb : MonotoneOn b (Ici 0)) (h₀ : ∀ r,0 ≤ r → 0 ≤ b r)
    (hbound : ∃ B,∀ r,0 ≤ r → b r ≤ B) {ε : ℝ} (hε : 0 < ε) :
    (∫ p,pairRegularizedEnergy (radialPairKernel b) g (longitudinalDerivative g) ε p
      ∂pairMeasure (volume.restrict (transverseDomain g))) ≤
    9/4*(∫ p,pairMass (radialPairKernel b) g (longitudinalDerivative g) p
      ∂pairMeasure (volume.restrict (transverseDomain g)))+
    ε*∫ p,pairError (radialPairKernel b) (longitudinalDerivative g) p
      ∂pairMeasure (volume.restrict (transverseDomain g)) :=
  paper_nine_quarters hg hc hb h₀ hbound (transverseDomain_finite hc) hε

#print axioms radialPairKernel_centered
#print axioms radialPairKernel_symmetric
#print axioms radialPairKernel_measurable
#print axioms radialPairKernel_nonneg
#print axioms radialPairKernel_le
#print axioms longitudinalDerivative_continuous
#print axioms longitudinalDerivative_sq_integrable
#print axioms paper_pairMoments_integrable
#print axioms paper_nine_quarters
#print axioms longitudinalDerivative_compact
#print axioms transverseDomain_compact
#print axioms transverseDomain_finite
#print axioms zero_outside_transverseDomain
#print axioms paper_nine_quarters_on_support
end BWork.Kelvin
