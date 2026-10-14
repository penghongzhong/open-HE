import Lemma_4_1_FiniteDomain

/-! Finite-domain Fubini and the epsilon limit connecting (14) to (15). -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace BWork.Kelvin

def pairNonlinear (k : Plane × Plane → ℝ) (g : Space → ℝ) (p : PairSpace) : ℝ :=
  k p.2*g (p.1,p.2.2)^2*g (p.1,p.2.1)^6

def pairNonlinearError (k : Plane × Plane → ℝ) (g : Space → ℝ) (p : PairSpace) : ℝ :=
  k p.2*g (p.1,p.2.1)^6

def pairRegularizedNonlinear (k : Plane × Plane → ℝ) (g : Space → ℝ) (ε : ℝ)
    (p : PairSpace) : ℝ := pairNonlinear k g p+ε*pairNonlinearError k g p

theorem pairRegularizedNonlinear_eq (k : Plane × Plane → ℝ) (g : Space → ℝ)
    (ε : ℝ) (p : PairSpace) : pairRegularizedNonlinear k g ε p =
      k p.2*(g (p.1,p.2.2)^2+ε)*g (p.1,p.2.1)^6 := by
  unfold pairRegularizedNonlinear pairNonlinear pairNonlinearError; ring

theorem paper_pairNonlinear_integrable {g : Space → ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    {b : ℝ → ℝ} (hb : MonotoneOn b (Ici 0)) (h₀ : ∀ r,0 ≤ r → 0 ≤ b r)
    (hbound : ∃ B,∀ r,0 ≤ r → b r ≤ B) {Y : Set Plane} (hY : volume Y < ⊤) :
    Integrable (pairNonlinear (radialPairKernel b) g) (pairMeasure (volume.restrict Y)) ∧
      Integrable (pairNonlinearError (radialPairKernel b) g) (pairMeasure (volume.restrict Y)) := by
  have : IsFiniteMeasure (volume.restrict Y) := isFiniteMeasure_restrict.mpr hY.ne
  obtain ⟨B,hB⟩ := hbound
  obtain ⟨M,_,hM⟩ := compact_function_sq_bound hg.continuous hc
  have hc6 : HasCompactSupport (fun z => g z^6) := hc.comp_left (g := fun r : ℝ => r^6) (by norm_num)
  have h6 : Integrable (fun z => g z^6) (volume : Measure Space) :=
    (hg.continuous.pow 6).integrable_of_hasCompactSupport hc6
  have hD : Integrable (fun z => (g z^3)^2) (volume.prod (volume.restrict Y)) := by
    simpa only [← pow_mul] using h6.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hi := pairMoments_integrable (volume.restrict Y) (radialPairKernel_measurable hb)
    (radialPairKernel_nonneg h₀) (radialPairKernel_le hB) hg.continuous.measurable hM hD
  change Integrable (fun p : PairSpace => radialPairKernel b p.2*g (p.1,p.2.2)^2*(g (p.1,p.2.1)^3)^2) _ ∧
    Integrable (fun p : PairSpace => radialPairKernel b p.2*(g (p.1,p.2.1)^3)^2) _ at hi
  change Integrable (fun p : PairSpace => radialPairKernel b p.2*g (p.1,p.2.2)^2*g (p.1,p.2.1)^6) _ ∧
    Integrable (fun p : PairSpace => radialPairKernel b p.2*g (p.1,p.2.1)^6) _
  simpa only [← pow_mul] using hi

def pairFiber (ν : Measure Plane) (F : PairSpace → ℝ) (a : Plane) : ℝ :=
  ∫ z : Space,F (z.1,(z.2,a)) ∂volume.prod ν

theorem pairFiber_integrable (ν : Measure Plane) [SFinite ν] {F : PairSpace → ℝ}
    (hF : Integrable F (pairMeasure ν)) : Integrable (pairFiber ν F) ν := by
  have hp := (measurePreserving_prodAssoc volume ν ν).integrable_comp_of_integrable hF
  exact hp.integral_prod_right

theorem integral_pairFiber (ν : Measure Plane) [SFinite ν] {F : PairSpace → ℝ}
    (hF : Integrable F (pairMeasure ν)) :
    (∫ a,pairFiber ν F a ∂ν) = ∫ p,F p ∂pairMeasure ν := by
  have hp := (measurePreserving_prodAssoc volume ν ν).integrable_comp_of_integrable hF
  have hm := (measurePreserving_prodAssoc volume ν ν).integral_comp' F
  have hi := integral_prod_symm (F ∘ MeasurableEquiv.prodAssoc) hp
  exact hi.symm.trans hm

theorem transverse_restrict_integral (Y : Set Plane) (F : Space → ℝ)
    (hF : ∀ z,z.2 ∉ Y → F z=0) :
    (∫ z,F z ∂volume.prod (volume.restrict Y)) = ∫ z,F z := by
  have hμ : (volume : Measure ℝ).prod (volume.restrict Y) =
      (volume : Measure Space).restrict (univ ×ˢ Y) := by
    simpa only [Measure.restrict_univ,← Measure.volume_eq_prod] using
      (Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure Plane)) univ Y)
  rw [hμ]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  exact hF z (by simpa only [mem_prod,mem_univ,true_and] using hz)

theorem regularized_pair_estimate {G : ℝ} (hG : 0 < G)
    (sharp : SharpSobolev G) (pullback : LinearSobolevPullback)
    (glue : SmoothInterfaceGluing) (density : SmoothH1MomentDensity)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    {ε : ℝ} (hε : 0 < ε)
    {b : ℝ → ℝ} (hb : MonotoneOn b (Ici 0)) (h₀ : ∀ r,0 ≤ r → 0 ≤ b r)
    (hbnd : ∃ B,∀ r,0 ≤ r → b r ≤ B) :
    (∫ p,pairRegularizedNonlinear (radialPairKernel b) g ε p
      ∂pairMeasure (volume.restrict (transverseDomain g))) ≤
    (54/G^2*(∫ z,transverseDensity (fderiv ℝ g) z)^2)*
      ∫ p,pairRegularizedEnergy (radialPairKernel b) g (longitudinalDerivative g) ε p
        ∂pairMeasure (volume.restrict (transverseDomain g)) := by
  let ν := volume.restrict (transverseDomain g)
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (transverseDomain_finite hc).ne
  obtain ⟨hN,hNC⟩ := paper_pairNonlinear_integrable hg hc hb h₀ hbnd (transverseDomain_finite hc)
  have hNε : Integrable (pairRegularizedNonlinear (radialPairKernel b) g ε) (pairMeasure ν) :=
    hN.add (hNC.const_mul ε)
  obtain ⟨hI,hC⟩ := paper_pairMoments_integrable hg hc hb h₀ hbnd (transverseDomain_finite hc)
  have hE := pairRegularizedEnergy_integrable ν (radialPairKernel_measurable hb)
    (radialPairKernel_nonneg h₀) (radialPairKernel_symmetric b) hg.continuous.measurable
    (longitudinalDerivative_continuous hg).measurable hε hI hC
  have hpoint (a : Plane) :
      pairFiber ν (pairRegularizedNonlinear (radialPairKernel b) g ε) a ≤
      (54/G^2*(∫ z,transverseDensity (fderiv ℝ g) z)^2)*
        pairFiber ν (pairRegularizedEnergy (radialPairKernel b) g (longitudinalDerivative g) ε) a := by
    have he := regularized_section_estimate hG sharp pullback glue density hg hc hε hb h₀ hbnd a
    have hleft := transverse_restrict_integral (transverseDomain g)
      (fun z => centeredWeight b a z*(g (z.1,a)^2+ε)*g z^6)
      (fun z hz => by rw [(zero_outside_transverseDomain g hz).1]; ring)
    have hright := transverse_restrict_integral (transverseDomain g)
      (fun z => centeredWeight b a z*regularizedEnergy (g (z.1,a))
        (longitudinalDerivative g (z.1,a)) ε (g z) (longitudinalDerivative g z))
      (fun z hz => by
        obtain ⟨hz₁,hz₂⟩ := zero_outside_transverseDomain g hz
        simp only [hz₁,hz₂,regularizedEnergy]; ring)
    unfold pairFiber
    simp_rw [pairRegularizedNonlinear_eq,pairRegularizedEnergy,radialPairKernel_centered]
    rw [hleft,hright]
    exact he
  have he := integral_mono (pairFiber_integrable ν hNε)
    ((pairFiber_integrable ν hE).const_mul _) hpoint
  rw [integral_const_mul,integral_pairFiber ν hNε,integral_pairFiber ν hE] at he
  exact he

theorem pair_estimate_with_error {G : ℝ} (hG : 0 < G)
    (sharp : SharpSobolev G) (pullback : LinearSobolevPullback)
    (glue : SmoothInterfaceGluing) (density : SmoothH1MomentDensity)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    {ε : ℝ} (hε : 0 < ε)
    {b : ℝ → ℝ} (hb : MonotoneOn b (Ici 0)) (h₀ : ∀ r,0 ≤ r → 0 ≤ b r)
    (hbnd : ∃ B,∀ r,0 ≤ r → b r ≤ B) :
    (∫ p,pairNonlinear (radialPairKernel b) g p
      ∂pairMeasure (volume.restrict (transverseDomain g))) ≤
    (54/G^2*(∫ z,transverseDensity (fderiv ℝ g) z)^2)*
      (9/4*(∫ p,pairMass (radialPairKernel b) g (longitudinalDerivative g) p
        ∂pairMeasure (volume.restrict (transverseDomain g)))+
       ε*∫ p,pairError (radialPairKernel b) (longitudinalDerivative g) p
        ∂pairMeasure (volume.restrict (transverseDomain g))) := by
  obtain ⟨hN,hNC⟩ := paper_pairNonlinear_integrable hg hc hb h₀ hbnd (transverseDomain_finite hc)
  have hNε : Integrable (pairRegularizedNonlinear (radialPairKernel b) g ε)
      (pairMeasure (volume.restrict (transverseDomain g))) := hN.add (hNC.const_mul ε)
  have hNN := integral_mono hN hNε (fun p => by
    change pairNonlinear _ g p ≤ pairNonlinear _ g p+ε*pairNonlinearError _ g p
    have hn : 0 ≤ pairNonlinearError (radialPairKernel b) g p :=
      mul_nonneg (radialPairKernel_nonneg h₀ _) (by positivity)
    exact le_add_of_nonneg_right (mul_nonneg hε.le hn))
  have he := regularized_pair_estimate hG sharp pullback glue density hg hc hε hb h₀ hbnd
  exact hNN.trans (he.trans (mul_le_mul_of_nonneg_left
    (paper_nine_quarters_on_support hg hc hb h₀ hbnd hε) (by positivity)))

/-- Epsilon is removed only after all integrals are finite on the constructed
transverse support. No constant epsilon is integrated over an infinite plane. -/
theorem pair_estimate_on_support {G : ℝ} (hG : 0 < G)
    (sharp : SharpSobolev G) (pullback : LinearSobolevPullback)
    (glue : SmoothInterfaceGluing) (density : SmoothH1MomentDensity)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    {b : ℝ → ℝ} (hb : MonotoneOn b (Ici 0)) (h₀ : ∀ r,0 ≤ r → 0 ≤ b r)
    (hbnd : ∃ B,∀ r,0 ≤ r → b r ≤ B) :
    (∫ p,pairNonlinear (radialPairKernel b) g p
      ∂pairMeasure (volume.restrict (transverseDomain g))) ≤
    (243/(2*G^2)*(∫ z,transverseDensity (fderiv ℝ g) z)^2)*
      ∫ p,pairMass (radialPairKernel b) g (longitudinalDerivative g) p
        ∂pairMeasure (volume.restrict (transverseDomain g)) := by
  let A := ∫ z,transverseDensity (fderiv ℝ g) z
  let I := ∫ p,pairMass (radialPairKernel b) g (longitudinalDerivative g) p
    ∂pairMeasure (volume.restrict (transverseDomain g))
  let C := ∫ p,pairError (radialPairKernel b) (longitudinalDerivative g) p
    ∂pairMeasure (volume.restrict (transverseDomain g))
  have ht : Tendsto (fun ε : ℝ => (54/G^2*A^2)*(9/4*I+ε*C)) (𝓝[>] 0)
      (𝓝 ((54/G^2*A^2)*(9/4*I))) := by
    have hi : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa only [zero_mul,add_zero] using
      ((tendsto_const_nhds.add (hi.mul_const C)).const_mul (54/G^2*A^2))
  have he := ge_of_tendsto ht (Filter.mem_of_superset self_mem_nhdsWithin (fun ε hε =>
    pair_estimate_with_error hG sharp pullback glue density hg hc hε hb h₀ hbnd))
  have halg : (54/G^2*A^2)*(9/4*I) = (243/(2*G^2)*A^2)*I := by ring
  rw [halg] at he
  exact he

theorem pair_restrict_integral (Y : Set Plane) (F : PairSpace → ℝ)
    (hF : ∀ p,p.2.1 ∉ Y ∨ p.2.2 ∉ Y → F p=0) :
    (∫ p,F p ∂pairMeasure (volume.restrict Y)) = ∫ p,F p := by
  have hμ : pairMeasure (volume.restrict Y) =
      (volume : Measure PairSpace).restrict (univ ×ˢ (Y ×ˢ Y)) := by
    unfold pairMeasure
    rw [Measure.prod_restrict Y Y]
    simpa only [Measure.restrict_univ,← Measure.volume_eq_prod] using
      (Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Plane × Plane)))
        univ (Y ×ˢ Y))
  rw [hμ]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  apply hF
  simpa only [mem_prod,mem_univ,true_and,not_and_or] using hp

/-- Equation (15), for the actual smooth compact function, actual derivatives
and the actual bounded monotone radial kernel on full Lebesgue pair space. -/
theorem plane_pair_estimate {G : ℝ} (hG : 0 < G)
    (sharp : SharpSobolev G) (pullback : LinearSobolevPullback)
    (glue : SmoothInterfaceGluing) (density : SmoothH1MomentDensity)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    {b : ℝ → ℝ} (hb : MonotoneOn b (Ici 0)) (h₀ : ∀ r,0 ≤ r → 0 ≤ b r)
    (hbnd : ∃ B,∀ r,0 ≤ r → b r ≤ B) :
    (∫ p : PairSpace,pairNonlinear (radialPairKernel b) g p) ≤
    (243/(2*G^2)*(∫ z,transverseDensity (fderiv ℝ g) z)^2)*
      ∫ p : PairSpace,pairMass (radialPairKernel b) g (longitudinalDerivative g) p := by
  have hN := pair_restrict_integral (transverseDomain g) (pairNonlinear (radialPairKernel b) g)
    (fun p hp => by
      rcases hp with hp|hp
      · have hz := (zero_outside_transverseDomain g (z := (p.1,p.2.1)) hp).1
        simp only [pairNonlinear,hz,zero_pow (by norm_num : 6 ≠ 0),mul_zero]
      · have hz := (zero_outside_transverseDomain g (z := (p.1,p.2.2)) hp).1
        simp only [pairNonlinear,hz,zero_pow (by norm_num : 2 ≠ 0),mul_zero,zero_mul])
  have hI := pair_restrict_integral (transverseDomain g)
    (pairMass (radialPairKernel b) g (longitudinalDerivative g)) (fun p hp => by
      rcases hp with hp|hp
      · have hz := (zero_outside_transverseDomain g (z := (p.1,p.2.1)) hp).2
        simp only [pairMass,hz,zero_pow (by norm_num : 2 ≠ 0),mul_zero]
      · have hz := (zero_outside_transverseDomain g (z := (p.1,p.2.2)) hp).1
        simp only [pairMass,hz,zero_pow (by norm_num : 2 ≠ 0),mul_zero,zero_mul])
  have he := pair_estimate_on_support hG sharp pullback glue density hg hc hb h₀ hbnd
  rw [hN,hI] at he
  exact he

#print axioms pairRegularizedNonlinear_eq
#print axioms paper_pairNonlinear_integrable
#print axioms pairFiber_integrable
#print axioms integral_pairFiber
#print axioms transverse_restrict_integral
#print axioms regularized_pair_estimate
#print axioms pair_estimate_with_error
#print axioms pair_estimate_on_support
#print axioms pair_restrict_integral
#print axioms plane_pair_estimate
end BWork.Kelvin
