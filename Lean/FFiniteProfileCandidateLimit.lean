import FFiniteCandidateExpansion
import FFiniteProfileRieszMixed
import FFiniteProfileFrameData

/-! The literal six-term finite-family candidate defect. Author source,
UNCOMPILED. Every spatial Riesz distribution below is justified on a common
finite intersection of true absolute fibre domains. All finite norms precede
limits, and every limit uses the supplied original filter. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HartreeF.FiniteProfileCandidateLimit
open TimeHolder ForcingDomain WeakHartreeChain DerivativeMajorization
  CompactCross CrossContinuity GeneralProfileCross ProfileApproximation
  LocalProfileProducts FinitePowerDefects FiniteCandidateExpansion
  FiniteProfileMixedDefects FiniteProfileRieszMixed FiniteProfileFrameData

variable {ι κ : Type*} [DecidableEq ι] {l : Filter κ}

/-- Internal closure data; only proved fields, never a premise of the public
candidate-defect theorem. The joint field is retained before every triangle. -/
private structure NSmall (f : κ → ℝ → Space → ℂ) : Prop where
  joint : ∀ n, AEStronglyMeasurable (fun z : ℝ × Space => f n z.1 z.2)
    (volume.prod volume)
  finite : ∀ n, forcingNorm (f n) ≠ ∞
  zero : Tendsto (fun n => forcingNorm (f n)) l (𝓝 0)

private theorem nsmall_add {f g : κ → ℝ → Space → ℂ}
    (hf : NSmall (l := l) f) (hg : NSmall (l := l) g) :
    NSmall (l := l) (fun n t x => f n t x + g n t x) := by
  have hb (n : κ) : forcingNorm (fun t x => f n t x + g n t x) ≤
      forcingNorm (f n) + forcingNorm (g n) :=
    mixed_add_le (by norm_num) (by norm_num) ENNReal.ofReal_ne_top
      (f n) (g n) (hf.joint n) (hg.joint n)
  refine ⟨fun n => (hf.joint n).add (hg.joint n),
    fun n => ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf.finite n, hg.finite n⟩) (hb n), ?_⟩
  have hz : Tendsto (fun n => forcingNorm (f n) + forcingNorm (g n)) l (𝓝 0) := by
    simpa only [add_zero] using hf.zero.add hg.zero
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
    (fun _ => bot_le) hb

private theorem nsmall_sum (s : Finset ι) (f : ι → κ → ℝ → Space → ℂ)
    (hf : ∀ i ∈ s, NSmall (l := l) (f i)) :
    NSmall (l := l) (fun n t x => ∑ i ∈ s, f i n t x) := by
  have hj (n : κ) : AEStronglyMeasurable
      (fun z : ℝ × Space => ∑ i ∈ s, f i n z.1 z.2) (volume.prod volume) :=
    Finset.aestronglyMeasurable_fun_sum s (fun i hi => (hf i hi).joint n)
  have hb (n : κ) : forcingNorm (fun t x => ∑ i ∈ s, f i n t x) ≤
      ∑ i ∈ s, forcingNorm (f i n) :=
    mixed_sum_le s (by norm_num) (by norm_num) ENNReal.ofReal_ne_top
      (fun i => f i n) (fun i hi => (hf i hi).joint n)
  refine ⟨hj, fun n => ne_top_of_le_ne_top
    (ENNReal.sum_ne_top.mpr (fun i hi => (hf i hi).finite n)) (hb n), ?_⟩
  have hz : Tendsto (fun n => ∑ i ∈ s, forcingNorm (f i n)) l (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum s (fun i hi => (hf i hi).zero)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
    (fun _ => bot_le) hb

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

private theorem row0_domains {α c : ℝ} (hH : OrdinaryHLS α c)
    (f : ℝ → Space → ℝ)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume))
    (hfin : mixedNorm volume volume (t0 α) (x0 α) f ≠ ∞) :
    ∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
      Integrable (fun y => rieszKernel α c (x-y) * f t y) volume := by
  have ha := hH.order_pos
  have ha3 := hH.order_lt_three
  have hi := ledger_hls_interior ha ha3
  obtain ⟨C, hC⟩ := mixed_riesz_bound hH hi.1 hi.2.1
    (div_pos (by norm_num : (0:ℝ)<10) (by linarith : 0<3-α))
    (show 1/(10/(3-α)) = 1/(30/(9+7*α))-α/3 by simp only [one_div, inv_div]; ring)
  exact (hC (t0 α) (reciprocal_ne_zero _) f hf (by simpa only [x0_eq ha] using hfin)).1

private theorem row1_domains {α c : ℝ} (hH : OrdinaryHLS α c)
    (f : ℝ → Space → ℝ)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume))
    (hfin : mixedNorm volume volume (t1 α) (x1 α) f ≠ ∞) :
    ∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
      Integrable (fun y => rieszKernel α c (x-y) * f t y) volume := by
  have ha := hH.order_pos
  have ha3 := hH.order_lt_three
  have hi := ledger_hls_interior ha ha3
  obtain ⟨C, hC⟩ := mixed_riesz_bound hH hi.2.2.1 hi.2.2.2.1
    (div_pos (by norm_num : (0:ℝ)<90) (by nlinarith : 0<19*(3-α)))
    (show 1/(90/(19*(3-α))) = 1/(90/(57+11*α))-α/3 by simp only [one_div, inv_div]; ring)
  exact (hC (t1 α) (reciprocal_ne_zero _) f hf (by simpa only [x1_eq ha] using hfin)).1

/-- Either the density remainder or its bounded local companion is small. -/
private theorem row0_small {α c : ℝ} (hH : OrdinaryHLS α c)
    (f : κ → ℝ → Space → ℝ) (g : κ → ℝ → Space → ℂ)
    (hf : ∀ n, AEStronglyMeasurable (fun z : ℝ × Space => f n z.1 z.2) (volume.prod volume))
    (hg : ∀ n, AEStronglyMeasurable (fun z : ℝ × Space => g n z.1 z.2) (volume.prod volume))
    (hff : ∀ n, mixedNorm volume volume (t0 α) (x0 α) (f n) ≠ ∞)
    (hgf : ∀ n, mixedNorm volume volume (t3 α) (x3 α) (g n) ≠ ∞)
    (hs : (Tendsto (fun n => mixedNorm volume volume (t0 α) (x0 α) (f n)) l (𝓝 0) ∧
        ∃ B : ℝ≥0, ∀ n, mixedNorm volume volume (t3 α) (x3 α) (g n) ≤ B) ∨
      ((∃ B : ℝ≥0, ∀ n, mixedNorm volume volume (t0 α) (x0 α) (f n) ≤ B) ∧
        Tendsto (fun n => mixedNorm volume volume (t3 α) (x3 α) (g n)) l (𝓝 0))) :
    NSmall (l := l) (fun n t x => rieszConvolution α c (f n t) x • g n t x) := by
  have ha := hH.order_pos
  have ha3 := hH.order_lt_three
  have hi := ledger_hls_interior ha ha3
  letI := time03_holder ha ha3
  letI := space03_holder ha ha3
  have hh := riesz_product_tendsto hH hi.1 hi.2.1
    (div_pos (by norm_num : (0:ℝ)<10) (by linarith : 0<3-α))
    (div_pos (by norm_num : (0:ℝ)<30) (by linarith : 0<16+3*α))
    (show 1/(10/(3-α)) = 1/(30/(9+7*α))-α/3 by simp only [one_div, inv_div]; ring)
    (p₁ := t0 α) (p₂ := t3 α) (reciprocal_ne_zero _) (reciprocal_ne_zero _)
    f g hf hg (by simpa only [x0_eq ha] using hff)
    (by simpa only [x3_eq ha] using hgf)
    (by simpa only [x0_eq ha, x3_eq ha] using hs)
  exact ⟨fun n => (joint_riesz_measurable volume α c (f n) (hf n)).smul (hg n), hh.1, hh.2⟩

private theorem row1_small {α c : ℝ} (hH : OrdinaryHLS α c)
    (f : κ → ℝ → Space → ℝ) (g : κ → ℝ → Space → ℂ)
    (hf : ∀ n, AEStronglyMeasurable (fun z : ℝ × Space => f n z.1 z.2) (volume.prod volume))
    (hg : ∀ n, AEStronglyMeasurable (fun z : ℝ × Space => g n z.1 z.2) (volume.prod volume))
    (hff : ∀ n, mixedNorm volume volume (t1 α) (x1 α) (f n) ≠ ∞)
    (hgf : ∀ n, mixedNorm volume volume (t2 α) (x2 α) (g n) ≠ ∞)
    (hs : (Tendsto (fun n => mixedNorm volume volume (t1 α) (x1 α) (f n)) l (𝓝 0) ∧
        ∃ B : ℝ≥0, ∀ n, mixedNorm volume volume (t2 α) (x2 α) (g n) ≤ B) ∨
      ((∃ B : ℝ≥0, ∀ n, mixedNorm volume volume (t1 α) (x1 α) (f n) ≤ B) ∧
        Tendsto (fun n => mixedNorm volume volume (t2 α) (x2 α) (g n)) l (𝓝 0))) :
    NSmall (l := l) (fun n t x => rieszConvolution α c (f n t) x • g n t x) := by
  have ha := hH.order_pos
  have ha3 := hH.order_lt_three
  have hi := ledger_hls_interior ha ha3
  letI := time12_holder ha ha3
  letI := space12_holder ha ha3
  have hh := riesz_product_tendsto hH hi.2.2.1 hi.2.2.2.1
    (div_pos (by norm_num : (0:ℝ)<90) (by nlinarith : 0<19*(3-α)))
    (div_pos (by norm_num : (0:ℝ)<90) (by linarith : 0<18+19*α))
    (show 1/(90/(19*(3-α))) = 1/(90/(57+11*α))-α/3 by simp only [one_div, inv_div]; ring)
    (p₁ := t1 α) (p₂ := t2 α) (reciprocal_ne_zero _) (reciprocal_ne_zero _)
    f g hf hg (by simpa only [x1_eq ha] using hff)
    (by simpa only [x2_eq ha] using hgf)
    (by simpa only [x1_eq ha, x2_eq ha] using hs)
  exact ⟨fun n => (joint_riesz_measurable volume α c (f n) (hf n)).smul (hg n), hh.1, hh.2⟩

private theorem pure_domains {α c : ℝ} (hH : OrdinaryHLS α c)
    {u h : ℝ → Space → ℂ} (hu : ScalarProfile u h) :
    ∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
      Integrable (fun y => rieszKernel α c (x-y) * pureDensity α u t y) volume ∧
      Integrable (fun y => rieszKernel α c (x-y) * pureDensityDerivative α u h t y) volume := by
  have hm := pure_coefficients_joint hH.order_pos hu
  have hf := pure_coefficients_finite hH.order_pos hH.order_lt_three hu
  have h0 := row0_domains hH (pureDensity α u) hm.1.aestronglyMeasurable hf.1
  have h1 := row1_domains hH (pureDensityDerivative α u h) hm.2.1.aestronglyMeasurable hf.2.1
  filter_upwards [h0, h1] with t ht0 ht1
  exact ht0.and ht1

/-- The six terms, with the second and fifth finite scalar sums distributed.
This is a literal field, not a target-norm bound or a smallness hypothesis. -/
private def sixTerms (α c : ℝ) (s : Finset ι)
    (u h : ι → ℝ → Space → ℂ) : ℝ → Space → ℂ :=
  fun t x =>
    rieszConvolution α c (R1 α s u h t) x •
      pureLocal α (fun t x => ∑ i ∈ s, u i t x) t x +
    (∑ i ∈ s, rieszConvolution α c (pureDensityDerivative α (u i) (h i) t) x • T0 α s u t x) +
    (∑ i ∈ s, ∑ j ∈ s.erase i, innerCross α c (u i) (h i) (u j) t x) +
    rieszConvolution α c (R0 α s u t) x •
      pureLocalDerivative α (fun t x => ∑ i ∈ s, u i t x)
        (fun t x => ∑ i ∈ s, h i t x) t x +
    (∑ i ∈ s, rieszConvolution α c (pureDensity α (u i) t) x • T1 α s u h t x) +
    (∑ i ∈ s, ∑ j ∈ s.erase i, outerCross α c (u i) (u j) (h j) t x)

/-- Common domains are proved from the actual V/S/W inputs before invoking
signed integral linearity. Only the finite active set is intersected. -/
private theorem candidate_six_terms_ae {α c : ℝ} (hH : OrdinaryHLS α c)
    (s : Finset ι) (u h : ι → ℝ → Space → ℂ)
    (hu : ∀ i ∈ s, ScalarProfile (u i) (h i)) :
    ∀ᵐ t ∂volume, (fun x => candidateDefect α c s (fun i => u i t) (fun i => h i t) x)
      =ᵐ[volume] sixTerms α c s u h t := by
  have hZ := scalarProfile_sum s u h hu
  have hz := pure_domains hH hZ
  have hi := (Filter.eventually_all_finset s).mpr (fun i hi => pure_domains hH (hu i hi))
  filter_upwards [hz, hi] with t hzt hit
  have hix := (Filter.eventually_all_finset s).mpr hit
  filter_upwards [hzt, hix] with x hzx hix
  have he := candidateDefect_six_terms α c s (fun i => u i t) (fun i => h i t) x
    hzx.1 (fun i hi => (hix i hi).1) hzx.2 (fun i hi => (hix i hi).2)
  simpa only [sixTerms, R0, R1, T0, T1, pureDensity, pureDensityDerivative,
    pureLocal, pureLocalDerivative, innerCross, outerCross, directionalDensity,
    potential, powerDensity, density, Finset.sum_smul] using he

/-- Every-index finiteness and original-filter vanishing of the SAME literal
finite directional candidate defect. The packet is produced from actual framed
profiles; neither this theorem nor the packet assumes a target defect norm.
Empty and singleton active sets are covered by the same finite-sum proof. -/
theorem candidate_defect_finite_tendsto {α c : ℝ} (hH : OrdinaryHLS α c)
    (s : Finset ι) (u h : κ → ι → ℝ → Space → ℂ)
    (P : FramedInputPacket s l α c u h) :
    (∀ n, forcingNorm (fun t => candidateDefect α c s
      (fun i => u n i t) (fun i => h n i t)) ≠ ∞) ∧
    Tendsto (fun n => forcingNorm (fun t => candidateDefect α c s
      (fun i => u n i t) (fun i => h n i t))) l (𝓝 0) := by
  have ha := hH.order_pos
  have ha3 := hH.order_lt_three
  -- The actual common-domain identity is available separately at every index.
  have heq (n : κ) := candidate_six_terms_ae hH s (u n) (h n) (P.profile n)
  let Z : κ → ℝ → Space → ℂ := fun n t x => ∑ i ∈ s, u n i t x
  let H : κ → ℝ → Space → ℂ := fun n t x => ∑ i ∈ s, h n i t x
  have hZ (n : κ) : ScalarProfile (Z n) (H n) := scalarProfile_sum s (u n) (h n) (P.profile n)
  obtain ⟨M, hM⟩ := P.uniform_bound
  have hZV (n : κ) : mixedNorm volume volume ∞ 6 (Z n) ≤ M :=
    (mixed_sum_le s (by simp) (by norm_num) (by norm_num) (u n)
      (fun i hi => (P.profile n i hi).value_joint.aestronglyMeasurable)).trans (hM n).1
  have hZS (n : κ) : mixedNorm volume volume 10 10 (Z n) ≤ M :=
    (mixed_sum_le s (by norm_num) (by norm_num) (by norm_num) (u n)
      (fun i hi => (P.profile n i hi).value_joint.aestronglyMeasurable)).trans (hM n).2.1
  have hHW (n : κ) : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) (H n) ≤ M :=
    (mixed_sum_le s (by norm_num) (by norm_num) (by norm_num) (h n)
      (fun i hi => (P.profile n i hi).gradient_joint.aestronglyMeasurable)).trans (hM n).2.2
  have hiV (n : κ) (i : ι) (hi : i ∈ s) : mixedNorm volume volume ∞ 6 (u n i) ≤ M :=
    (Finset.single_le_sum (fun j _ => bot_le) hi).trans (hM n).1
  have hiS (n : κ) (i : ι) (hi : i ∈ s) : mixedNorm volume volume 10 10 (u n i) ≤ M :=
    (Finset.single_le_sum (fun j _ => bot_le) hi).trans (hM n).2.1
  have hiW (n : κ) (i : ι) (hi : i ∈ s) :
      mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) (h n i) ≤ M :=
    (Finset.single_le_sum (fun j _ => bot_le) hi).trans (hM n).2.2
  obtain ⟨C, hC⟩ := pure_coefficients_uniform_bound ha ha3 M
  have hZC (n : κ) := hC (Z n) (H n) (hZ n) (hZV n) (hZS n) (hHW n)
  have hiC (n : κ) (i : ι) (hi : i ∈ s) :=
    hC (u n i) (h n i) (P.profile n i hi) (hiV n i hi) (hiS n i hi) (hiW n i hi)
  have hZJ (n : κ) := pure_coefficients_joint ha (hZ n)
  have hZF (n : κ) := pure_coefficients_finite ha ha3 (hZ n)
  have hiJ (n : κ) (i : ι) (hi : i ∈ s) := pure_coefficients_joint ha (P.profile n i hi)
  have hiF (n : κ) (i : ι) (hi : i ∈ s) := pure_coefficients_finite ha ha3 (P.profile n i hi)
  have hDJ (n : κ) := defects_joint ha s (u n) (h n) (P.profile n)
  have hDF (n : κ) := defects_finite ha ha3 s (u n) (h n) (P.profile n)
  have hRV (n : κ) : Vsize s (u n) ≤ M :=
    (radiusField_norm_le s (u n) (fun i hi => (P.profile n i hi).value_joint)
      (by simp) (by norm_num) (by norm_num)).trans (hM n).1
  have hRS (n : κ) : Ssize s (u n) ≤ M :=
    (radiusField_norm_le s (u n) (fun i hi => (P.profile n i hi).value_joint)
      (by norm_num) (by norm_num) (by norm_num)).trans (hM n).2.1
  have hD0 := defects_tendsto_zero ha ha3 s u h P.profile M hRV hRS
    (fun i hi j hj hij => (P.local_zero i hi j hj hij).1)
    (fun i hi j hj hij => (P.local_zero i hi j hj hij).2.1)
  -- Term 1: the derivative density remainder against the full local factor.
  have hA := row1_small hH (fun n => R1 α s (u n) (h n)) (fun n => pureLocal α (Z n))
    (fun n => (hDJ n).2.1.aestronglyMeasurable)
    (fun n => (hZJ n).2.2.1.aestronglyMeasurable)
    (fun n => (hDF n).2.1) (fun n => (hZF n).2.2.1)
    (Or.inl ⟨hD0.2.1, C, fun n => (hZC n).2.2.1⟩)
  -- Term 2: finite sum of bounded pure derivative coefficients times T0.
  have hB := nsmall_sum s
    (fun i n t x => rieszConvolution α c (pureDensityDerivative α (u n i) (h n i) t) x • T0 α s (u n) t x)
    (fun i hi => row1_small hH (fun n => pureDensityDerivative α (u n i) (h n i))
      (fun n => T0 α s (u n))
      (fun n => (hiJ n i hi).2.1.aestronglyMeasurable)
      (fun n => (hDJ n).2.2.1.aestronglyMeasurable)
      (fun n => (hiF n i hi).2.1) (fun n => (hDF n).2.2.1)
      (Or.inr ⟨⟨C, fun n => (hiC n i hi).2.1⟩, hD0.2.2.1⟩))
  -- Term 3: the genuine nonlocal inner cross terms, including every ordered pair.
  have hCROSS1 := nsmall_sum s
    (fun i n t x => ∑ j ∈ s.erase i, innerCross α c (u n i) (h n i) (u n j) t x)
    (fun i hi => nsmall_sum (s.erase i)
      (fun j n => innerCross α c (u n i) (h n i) (u n j)) (fun j hj => by
        have hjs := Finset.mem_of_mem_erase hj
        refine ⟨fun n => inner_joint_measurable α c
          (P.profile n i hi).value_joint.aestronglyMeasurable
          (P.profile n i hi).gradient_joint.aestronglyMeasurable
          (P.profile n j hjs).value_joint.aestronglyMeasurable, ?_, ?_⟩
        · intro n
          exact (FiniteProfileCrossDomains.scalar_cross_finite hH
            (P.profile n i hi) (P.profile n j hjs)).1
        · exact (P.cross_zero i hi j hjs (Finset.mem_erase.mp hj).1.symm).1))
  -- Term 4: the density remainder against the true derivative of the full sum.
  have hD := row0_small hH (fun n => R0 α s (u n))
    (fun n => pureLocalDerivative α (Z n) (H n))
    (fun n => (hDJ n).1.aestronglyMeasurable)
    (fun n => (hZJ n).2.2.2.aestronglyMeasurable)
    (fun n => (hDF n).1) (fun n => (hZF n).2.2.2)
    (Or.inl ⟨hD0.1, C, fun n => (hZC n).2.2.2⟩)
  -- Term 5: finite sum of bounded pure density coefficients times T1.
  have hE := nsmall_sum s
    (fun i n t x => rieszConvolution α c (pureDensity α (u n i) t) x • T1 α s (u n) (h n) t x)
    (fun i hi => row0_small hH (fun n => pureDensity α (u n i)) (fun n => T1 α s (u n) (h n))
      (fun n => (hiJ n i hi).1.aestronglyMeasurable)
      (fun n => (hDJ n).2.2.2.aestronglyMeasurable)
      (fun n => (hiF n i hi).1) (fun n => (hDF n).2.2.2)
      (Or.inr ⟨⟨C, fun n => (hiC n i hi).1⟩, hD0.2.2.2⟩))
  -- Term 6: the distinct outer derivative placement is retained separately.
  have hCROSS0 := nsmall_sum s
    (fun i n t x => ∑ j ∈ s.erase i, outerCross α c (u n i) (u n j) (h n j) t x)
    (fun i hi => nsmall_sum (s.erase i)
      (fun j n => outerCross α c (u n i) (u n j) (h n j)) (fun j hj => by
        have hjs := Finset.mem_of_mem_erase hj
        refine ⟨fun n => outer_joint_measurable α c
          (P.profile n i hi).value_joint.aestronglyMeasurable
          (P.profile n j hjs).value_joint.aestronglyMeasurable
          (P.profile n j hjs).gradient_joint.aestronglyMeasurable, ?_, ?_⟩
        · intro n
          exact (FiniteProfileCrossDomains.scalar_cross_finite hH
            (P.profile n i hi) (P.profile n j hjs)).2
        · exact (P.cross_zero i hi j hjs (Finset.mem_erase.mp hj).1.symm).2.1))
  have hSix : NSmall (l := l) (fun n => sixTerms α c s (u n) (h n)) :=
    nsmall_add (nsmall_add (nsmall_add (nsmall_add (nsmall_add hA hB) hCROSS1) hD) hE) hCROSS0
  have hnorm (n : κ) : forcingNorm (fun t => candidateDefect α c s
      (fun i => u n i t) (fun i => h n i t)) = forcingNorm (sixTerms α c s (u n) (h n)) :=
    forcingNorm_congr_nested_ae (heq n)
  refine ⟨fun n => ?_, ?_⟩
  · rw [hnorm n]
    exact hSix.finite n
  · simpa only [hnorm] using hSix.zero

#print axioms candidate_defect_finite_tendsto
end HartreeF.FiniteProfileCandidateLimit
