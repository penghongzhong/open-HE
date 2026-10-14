import FFreeValueQCoefficients

/-! Full signed directional candidate control by E^(2α) S^3 Q, on all
0 < α < 3. Author source, UNCOMPILED. HLS constants are chosen before the
fields. Absolute signed fibres and true spatial/time domains are retained. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HartreeF.FreeValueFullCandidate
open TimeHolder ForcingDomain WeakHartreeChain DerivativeMajorization
  CompactCross GeneralProfileCross ProfileApproximation LocalProfileProducts
  FiniteProfileMixedDefects FiniteProfileRieszMixed

/-- Actual mixed-space domains; the real time norm is used only after the
spatial slices have been proved finite. -/
structure MixedDomain {E : Type*} [NormedAddCommGroup E]
    (p q : ℝ≥0∞) (f : ℝ → Space → E) : Prop where
  joint : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume)
  spatial : ∀ᵐ t ∂volume, MemLp (f t) q volume
  time : MemLp (fun t => (eLpNorm (f t) q volume).toReal) p volume
  finite : mixedNorm volume volume p q f ≠ ∞

theorem mixedDomain_of_finite {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {p q : ℝ≥0∞} (hp : p ≠ 0) (hq : q ≠ 0) (hqT : q ≠ ∞)
    (f : ℝ → Space → E)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume))
    (hfin : mixedNorm volume volume p q f ≠ ∞) : MixedDomain p q f := by
  have hs := mixed_ae_slice hp f hfin
  refine ⟨hf, hs, ?_, hfin⟩
  change eLpNorm (fun t => (eLpNorm (f t) q volume).toReal) p volume < ∞
  rw [real_slice_mixed_eq volume p q hq hqT f hf hs]
  exact lt_top_iff_ne_top.mpr hfin

/-- The signed HLS/Holder producer retains the absolute fibres, Riesz domains,
product domains, and estimate. No norm-only surrogate supplies the fibres. -/
theorem signed_riesz_product_bound {α c q r v : ℝ} (hH : OrdinaryHLS α c)
    (hq1 : 1 < q) (hqα : q < 3/α) (hr : 0 < r) (hv : 0 < v)
    (hrel : 1/r = 1/q - α/3)
    {p₁ p₂ : ℝ≥0∞} [ENNReal.HolderTriple p₁ p₂ 2]
    [ENNReal.HolderTriple (ENNReal.ofReal r) (ENNReal.ofReal v) (ENNReal.ofReal (6/5 : ℝ))]
    (hp₁ : p₁ ≠ 0) (hp₂ : p₂ ≠ 0) :
    ∃ C : ℝ≥0, ∀ (f : ℝ → Space → ℝ) (g : ℝ → Space → ℂ),
      AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume) →
      AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2) (volume.prod volume) →
      mixedNorm volume volume p₁ (ENNReal.ofReal q) f ≠ ∞ →
      mixedNorm volume volume p₂ (ENNReal.ofReal v) g ≠ ∞ →
      (∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
        Integrable (fun y => rieszKernel α c (x-y) * f t y) volume) ∧
      MixedDomain p₁ (ENNReal.ofReal r) (fun t => rieszConvolution α c (f t)) ∧
      MixedDomain 2 (ENNReal.ofReal (6/5 : ℝ))
        (fun t x => rieszConvolution α c (f t) x • g t x) ∧
      forcingNorm (fun t x => rieszConvolution α c (f t) x • g t x) ≤
        (C : ℝ≥0∞) * mixedNorm volume volume p₁ (ENNReal.ofReal q) f *
          mixedNorm volume volume p₂ (ENNReal.ofReal v) g := by
  obtain ⟨C,hC⟩ := mixed_riesz_bound hH hq1 hqα hr hrel
  refine ⟨C, ?_⟩
  intro f g hf hg hff hgf
  obtain ⟨hfib, hs, hb⟩ := hC p₁ hp₁ f hf hff
  have hj := joint_riesz_measurable volume α c f hf
  have hrf : mixedNorm volume volume p₁ (ENNReal.ofReal r)
      (fun t => rieszConvolution α c (f t)) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hff) hb
  have hrd : MixedDomain p₁ (ENNReal.ofReal r) (fun t => rieszConvolution α c (f t)) := by
    refine ⟨hj, hs, ?_, hrf⟩
    change eLpNorm (fun t => (eLpNorm (rieszConvolution α c (f t))
      (ENNReal.ofReal r) volume).toReal) p₁ volume < ∞
    rw [real_slice_mixed_eq volume p₁ (ENNReal.ofReal r)
      (ne_of_gt (ENNReal.ofReal_pos.mpr hr)) ENNReal.ofReal_ne_top _ hj hs]
    exact lt_top_iff_ne_top.mpr hrf
  have hprod := (mixed_smul_le hp₁ hp₂
    (ne_of_gt (ENNReal.ofReal_pos.mpr hr)) ENNReal.ofReal_ne_top
    (ne_of_gt (ENNReal.ofReal_pos.mpr hv)) ENNReal.ofReal_ne_top
    (by norm_num : ENNReal.ofReal (6/5 : ℝ) ≠ 0) ENNReal.ofReal_ne_top
    (fun t => rieszConvolution α c (f t)) g hj hg hrf hgf).trans
      (mul_le_mul' hb le_rfl)
  have hpfin : forcingNorm (fun t x => rieszConvolution α c (f t) x • g t x) ≠ ∞ :=
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hff) hgf) hprod
  exact ⟨hfib, hrd, mixedDomain_of_finite (by norm_num) (by norm_num)
    ENNReal.ofReal_ne_top _ (hj.smul hg) hpfin, hprod⟩

/-- The literal candidate is the sum of both derivative placements. -/
theorem candidate_eq_cross (α c : ℝ) (u h : ℝ → Space → ℂ) :
    (fun t x => directionalCandidate α c (u t) (h t) x) =
      (fun t x => innerCross α c u h u t x + outerCross α c u u h t x) := by
  rfl

/-- Every field is produced from actual E/S/Q inputs. This packet does not
assert that h is a derivative of u. It is a conclusion, not an analytic input. -/
structure FullCandidateControl (α c : ℝ) (u h : ℝ → Space → ℂ) (K : ℝ≥0) : Prop where
  density_fibres : ∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
    Integrable (fun y => rieszKernel α c (x-y) * powerDensity α (u t) y) volume
  directional_fibres : ∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
    Integrable (fun y => rieszKernel α c (x-y) * directionalDensity α (u t) (h t) y) volume
  density_riesz : MixedDomain (t0 α) (ENNReal.ofReal (10/(3-α)))
    (fun t => potential α c (u t))
  directional_riesz : MixedDomain (t1 α) (ENNReal.ofReal (90/(19*(3-α))))
    (fun t => rieszConvolution α c (directionalDensity α (u t) (h t)))
  inner_domain : MixedDomain 2 (ENNReal.ofReal (6/5 : ℝ)) (innerCross α c u h u)
  outer_domain : MixedDomain 2 (ENNReal.ofReal (6/5 : ℝ)) (outerCross α c u u h)
  candidate_domain : MixedDomain 2 (ENNReal.ofReal (6/5 : ℝ))
    (fun t x => directionalCandidate α c (u t) (h t) x)
  candidate_joint : AEStronglyMeasurable
    (fun z : ℝ × Space => directionalCandidate α c (u z.1) (h z.1) z.2) (volume.prod volume)
  inner_finite : forcingNorm (innerCross α c u h u) ≠ ∞
  outer_finite : forcingNorm (outerCross α c u u h) ≠ ∞
  candidate_finite : forcingNorm (fun t x => directionalCandidate α c (u t) (h t) x) ≠ ∞
  cross_bound : forcingNorm (innerCross α c u h u) + forcingNorm (outerCross α c u u h) ≤
    (K : ℝ≥0∞) * mixedNorm volume volume ∞ 6 u ^ (2*α) *
      mixedNorm volume volume 10 10 u ^ (3 : ℝ) * Q u h
  candidate_bound : forcingNorm (fun t x => directionalCandidate α c (u t) (h t) x) ≤
    (K : ℝ≥0∞) * mixedNorm volume volume ∞ 6 u ^ (2*α) *
      mixedNorm volume volume 10 10 u ^ (3 : ℝ) * Q u h

private theorem x0_eq {α : ℝ} (ha : 0 < α) :
    x0 α = ENNReal.ofReal (30/(9+7*α)) := by
  rw [x0, reciprocal_eq (by linarith : 0 < (9+7*α)/30)]
  simp only [inv_div]

private theorem x1_eq {α : ℝ} (ha : 0 < α) :
    x1 α = ENNReal.ofReal (90/(57+11*α)) := by
  rw [x1, reciprocal_eq (by linarith : 0 < (57+11*α)/90)]
  simp only [inv_div]

private theorem x2_eq {α : ℝ} (ha : 0 < α) :
    x2 α = ENNReal.ofReal (90/(18+19*α)) := by
  rw [x2, reciprocal_eq (by linarith : 0 < (18+19*α)/90)]
  simp only [inv_div]

private theorem x3_eq {α : ℝ} (ha : 0 < α) :
    x3 α = ENNReal.ofReal (30/(16+3*α)) := by
  rw [x3, reciprocal_eq (by linarith : 0 < (16+3*α)/30)]
  simp only [inv_div]

private theorem time03_holder {α : ℝ} (ha : 0 < α) (ha3 : α < 3) :
    ENNReal.HolderTriple (t0 α) (t3 α) 2 := by
  have hh := reciprocal_holder (by linarith : 0 ≤ (3-α)/10)
    (by linarith : 0 ≤ (2+α)/10)
  simpa only [t0, t3, show (3-α)/10+(2+α)/10=(1/2 : ℝ) by ring,
    show reciprocal (1/2 : ℝ)=2 by norm_num [reciprocal]] using hh

private theorem time12_holder {α : ℝ} (ha : 0 < α) (ha3 : α < 3) :
    ENNReal.HolderTriple (t1 α) (t2 α) 2 := by
  have hh := reciprocal_holder (by linarith : 0 ≤ (3+2*α/3)/10)
    (by linarith : 0 ≤ (2-2*α/3)/10)
  simpa only [t1, t2, show (3+2*α/3)/10+(2-2*α/3)/10=(1/2 : ℝ) by ring,
    show reciprocal (1/2 : ℝ)=2 by norm_num [reciprocal]] using hh

private theorem space03_holder {α : ℝ} (ha : 0 < α) (ha3 : α < 3) :
    ENNReal.HolderTriple (ENNReal.ofReal (10/(3-α)))
      (ENNReal.ofReal (30/(16+3*α))) (ENNReal.ofReal (6/5 : ℝ)) := by
  have hh : Real.HolderTriple (10/(3-α)) (30/(16+3*α)) (6/5) := by
    refine ⟨?_, div_pos (by norm_num) (by linarith), div_pos (by norm_num) (by linarith)⟩
    simp only [inv_div]
    ring
  exact hh.ennrealOfReal

private theorem space12_holder {α : ℝ} (ha : 0 < α) (ha3 : α < 3) :
    ENNReal.HolderTriple (ENNReal.ofReal (90/(19*(3-α))))
      (ENNReal.ofReal (90/(18+19*α))) (ENNReal.ofReal (6/5 : ℝ)) := by
  have hh : Real.HolderTriple (90/(19*(3-α))) (90/(18+19*α)) (6/5) := by
    refine ⟨?_, div_pos (by norm_num) (by nlinarith), div_pos (by norm_num) (by linarith)⟩
    simp only [inv_div]
    ring
  exact hh.ennrealOfReal

/-- Nonnegative exponent addition remains valid at zero and infinity. -/
private theorem inner_power_collect (α : ℝ) (hα : 0 < α) (hα3 : α < 3)
    (E S Q C D : ℝ≥0∞) :
    C * (D * (E^(α/3) * S^(1+2*α/3) * Q)) *
        (E^(5*α/3) * S^(2-2*α/3)) =
      (C*D) * E^(2*α) * S^(3 : ℝ) * Q := by
  calc
    _ = (C*D) * (E^(α/3)*E^(5*α/3)) *
        (S^(1+2*α/3)*S^(2-2*α/3)) * Q := by ring
    _ = _ := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity : 0 ≤ α/3) (by positivity : 0 ≤ 5*α/3),
        ← ENNReal.rpow_add_of_nonneg _ _ (by positivity : 0 ≤ 1+2*α/3) (by linarith : 0 ≤ 2-2*α/3)]
      rw [show α/3+5*α/3=2*α by ring,
        show (1+2*α/3)+(2-2*α/3)=(3 : ℝ) by ring]

private theorem outer_power_collect (α : ℝ) (hα : 0 < α) (hα3 : α < 3)
    (E S Q C D : ℝ≥0∞) :
    C * (E^(2*α)*S^(3-α)) * (D * (S^α*Q)) =
      (C*D) * E^(2*α) * S^(3 : ℝ) * Q := by
  calc
    _ = (C*D) * E^(2*α) * (S^(3-α)*S^α) * Q := by ring
    _ = _ := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith : 0 ≤ 3-α) hα.le]
      rw [show (3-α)+α=(3 : ℝ) by ring]

/-- One finite nonnegative constant is chosen before the actual fields, all
frames and all depths. The direction consumes Q, and has no W assumption. -/
theorem full_candidate_bound {α c : ℝ} (hH : OrdinaryHLS α c) :
    ∃ K : ℝ≥0, ∀ (u h : ℝ → Space → ℂ),
      StronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) →
      StronglyMeasurable (fun z : ℝ × Space => h z.1 z.2) →
      mixedNorm volume volume ∞ 6 u ≠ ∞ →
      mixedNorm volume volume 10 10 u ≠ ∞ → Q u h ≠ ∞ →
      FullCandidateControl α c u h K := by
  have ha := hH.order_pos
  have ha3 := hH.order_lt_three
  have hi := ledger_hls_interior ha ha3
  letI := time03_holder ha ha3
  letI := time12_holder ha ha3
  letI := space03_holder ha ha3
  letI := space12_holder ha ha3
  obtain ⟨C0,hC0⟩ := signed_riesz_product_bound hH hi.1 hi.2.1
    (div_pos (by norm_num : (0 : ℝ) < 10) (by linarith : 0 < 3-α))
    (div_pos (by norm_num : (0 : ℝ) < 30) (by linarith : 0 < 16+3*α))
    (show 1/(10/(3-α)) = 1/(30/(9+7*α))-α/3 by simp only [one_div, inv_div]; ring)
    (p₁ := t0 α) (p₂ := t3 α) (reciprocal_ne_zero _) (reciprocal_ne_zero _)
  obtain ⟨C1,hC1⟩ := signed_riesz_product_bound hH hi.2.2.1 hi.2.2.2.1
    (div_pos (by norm_num : (0 : ℝ) < 90) (by nlinarith : 0 < 19*(3-α)))
    (div_pos (by norm_num : (0 : ℝ) < 90) (by linarith : 0 < 18+19*α))
    (show 1/(90/(19*(3-α))) = 1/(90/(57+11*α))-α/3 by simp only [one_div, inv_div]; ring)
    (p₁ := t1 α) (p₂ := t2 α) (reciprocal_ne_zero _) (reciprocal_ne_zero _)
  let D0 : ℝ≥0 := ⟨2+α, by linarith⟩
  let D1 : ℝ≥0 := ⟨3+α, by linarith⟩
  let K : ℝ≥0 := C1*D1 + C0*D0
  have hD0 : (D0 : ℝ≥0∞) = ENNReal.ofReal (2+α) :=
    (ENNReal.ofReal_eq_coe_nnreal (by linarith : 0 ≤ 2+α)).symm
  have hD1 : (D1 : ℝ≥0∞) = ENNReal.ofReal (3+α) :=
    (ENNReal.ofReal_eq_coe_nnreal (by linarith : 0 ≤ 3+α)).symm
  refine ⟨K, ?_⟩
  intro u h hu hh hE hS hQ
  have hm := q_coefficients_joint ha hu hh
  have hf := q_coefficients_finite ha ha3 hu hh hE hS hQ
  have hb := q_coefficients_bound ha ha3 hu hh hE hS hQ
  obtain ⟨hfib0, hr0, hp0, hn0⟩ := hC0 (pureDensity α u) (pureLocalDerivative α u h)
    hm.1 hm.2.2.2 (by simpa only [x0_eq ha] using hf.1)
      (by simpa only [x3_eq ha] using hf.2.2.2)
  obtain ⟨hfib1, hr1, hp1, hn1⟩ := hC1 (pureDensityDerivative α u h) (pureLocal α u)
    hm.2.1 hm.2.2.1 (by simpa only [x1_eq ha] using hf.2.1)
      (by simpa only [x2_eq ha] using hf.2.2.1)
  have hiD : MixedDomain 2 (ENNReal.ofReal (6/5 : ℝ)) (innerCross α c u h u) := hp1
  have hoD : MixedDomain 2 (ENNReal.ofReal (6/5 : ℝ)) (outerCross α c u u h) := hp0
  have hn1' : forcingNorm (innerCross α c u h u) ≤
      ((C1 : ℝ≥0∞)*D1) * mixedNorm volume volume ∞ 6 u ^ (2*α) *
        mixedNorm volume volume 10 10 u ^ (3 : ℝ) * Q u h := by
    have hr : forcingNorm (innerCross α c u h u) ≤
        (C1 : ℝ≥0∞) * mixedNorm volume volume (t1 α) (x1 α) (pureDensityDerivative α u h) *
          mixedNorm volume volume (t2 α) (x2 α) (pureLocal α u) := by
      simpa only [x1_eq ha, x2_eq ha] using hn1
    calc
      _ ≤ (C1 : ℝ≥0∞) *
          (ENNReal.ofReal (3+α) * (mixedNorm volume volume ∞ 6 u ^ (α/3) *
            mixedNorm volume volume 10 10 u ^ (1+2*α/3) * Q u h)) *
          (mixedNorm volume volume ∞ 6 u ^ (5*α/3) *
            mixedNorm volume volume 10 10 u ^ (2-2*α/3)) :=
        hr.trans (mul_le_mul' (mul_le_mul' le_rfl hb.2.1) hb.2.2.1)
      _ = _ := by rw [hD1]; exact inner_power_collect α ha ha3 _ _ _ _ _
  have hn0' : forcingNorm (outerCross α c u u h) ≤
      ((C0 : ℝ≥0∞)*D0) * mixedNorm volume volume ∞ 6 u ^ (2*α) *
        mixedNorm volume volume 10 10 u ^ (3 : ℝ) * Q u h := by
    have hr : forcingNorm (outerCross α c u u h) ≤
        (C0 : ℝ≥0∞) * mixedNorm volume volume (t0 α) (x0 α) (pureDensity α u) *
          mixedNorm volume volume (t3 α) (x3 α) (pureLocalDerivative α u h) := by
      simpa only [x0_eq ha, x3_eq ha] using hn0
    calc
      _ ≤ (C0 : ℝ≥0∞) *
          (mixedNorm volume volume ∞ 6 u ^ (2*α) * mixedNorm volume volume 10 10 u ^ (3-α)) *
          (ENNReal.ofReal (2+α) * (mixedNorm volume volume 10 10 u ^ α * Q u h)) :=
        hr.trans (mul_le_mul' (mul_le_mul' le_rfl hb.1) hb.2.2.2)
      _ = _ := by rw [hD0]; exact outer_power_collect α ha ha3 _ _ _ _ _
  have hcross : forcingNorm (innerCross α c u h u) + forcingNorm (outerCross α c u u h) ≤
      (K : ℝ≥0∞) * mixedNorm volume volume ∞ 6 u ^ (2*α) *
        mixedNorm volume volume 10 10 u ^ (3 : ℝ) * Q u h := by
    calc
      _ ≤ ((C1 : ℝ≥0∞)*D1) * mixedNorm volume volume ∞ 6 u ^ (2*α) *
            mixedNorm volume volume 10 10 u ^ (3 : ℝ) * Q u h +
          ((C0 : ℝ≥0∞)*D0) * mixedNorm volume volume ∞ 6 u ^ (2*α) *
            mixedNorm volume volume 10 10 u ^ (3 : ℝ) * Q u h := add_le_add hn1' hn0'
      _ = _ := by simp only [K, ENNReal.coe_add, ENNReal.coe_mul]; ring
  have hjC := joint_directional_candidate_measurable volume α c u h
    hu.aestronglyMeasurable hh.aestronglyMeasurable
  have htri : forcingNorm (fun t x => directionalCandidate α c (u t) (h t) x) ≤
      forcingNorm (innerCross α c u h u) + forcingNorm (outerCross α c u u h) := by
    rw [candidate_eq_cross]
    exact mixed_add_le (by norm_num) (by norm_num) ENNReal.ofReal_ne_top
      _ _ hiD.joint hoD.joint
  have hcf : forcingNorm (fun t x => directionalCandidate α c (u t) (h t) x) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hiD.finite, hoD.finite⟩) htri
  exact ⟨hfib0, hfib1, hr0, hr1, hiD, hoD,
    mixedDomain_of_finite (by norm_num) (by norm_num) ENNReal.ofReal_ne_top _ hjC hcf,
    hjC, hiD.finite, hoD.finite, hcf, hcross, htri.trans hcross⟩

/-- A convenient literal-full-C bound for a finite value sum. All cross-label
nonlocal interactions remain inside C of the actual sum. -/
theorem full_candidate_sum_bound {α c : ℝ} (hH : OrdinaryHLS α c) :
    ∃ K : ℝ≥0, ∀ {ι : Type*} (s : Finset ι) (u : ι → ℝ → Space → ℂ)
      (h : ℝ → Space → ℂ),
      (∀ i ∈ s, StronglyMeasurable (fun z : ℝ × Space => u i z.1 z.2)) →
      StronglyMeasurable (fun z : ℝ × Space => h z.1 z.2) →
      (∀ i ∈ s, mixedNorm volume volume ∞ 6 (u i) ≠ ∞) →
      (∀ i ∈ s, mixedNorm volume volume 10 10 (u i) ≠ ∞) →
      (∀ i ∈ s, Q (u i) h ≠ ∞) →
      FullCandidateControl α c (fun t x => ∑ i ∈ s, u i t x) h K ∧
      forcingNorm (fun t x => directionalCandidate α c (fun y => ∑ i ∈ s, u i t y) (h t) x) ≤
        (K : ℝ≥0∞) * mixedNorm volume volume ∞ 6 (fun t x => ∑ i ∈ s, u i t x) ^ (2*α) *
          mixedNorm volume volume 10 10 (fun t x => ∑ i ∈ s, u i t x) ^ (3 : ℝ) *
            ∑ i ∈ s, Q (u i) h := by
  classical
  obtain ⟨K,hK⟩ := full_candidate_bound hH
  refine ⟨K, ?_⟩
  intro ι s u h hu hh hE hS hQ
  have hsum := Finset.stronglyMeasurable_fun_sum s hu
  have hsumE : mixedNorm volume volume ∞ 6 (fun t x => ∑ i ∈ s, u i t x) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr hE)
      (mixed_sum_le s (by simp) (by norm_num) (by norm_num) u
        (fun i hi => (hu i hi).aestronglyMeasurable))
  have hsumS : mixedNorm volume volume 10 10 (fun t x => ∑ i ∈ s, u i t x) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr hS)
      (mixed_sum_le s (by norm_num) (by norm_num) (by norm_num) u
        (fun i hi => (hu i hi).aestronglyMeasurable))
  have hQB := Q_sum_le s u h (fun i hi => (hu i hi).aestronglyMeasurable) hh.aestronglyMeasurable
  have hsumQ : Q (fun t x => ∑ i ∈ s, u i t x) h ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr hQ) hQB
  have hc := hK _ h hsum hh hsumE hsumS hsumQ
  exact ⟨hc, hc.candidate_bound.trans (mul_le_mul' le_rfl hQB)⟩

end HartreeF.FreeValueFullCandidate
