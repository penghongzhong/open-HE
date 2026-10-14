import PhysicalStretchDomain
import PhysicalStretchDerivative

/-!
Differentiation under the actual physical Hartree double integral and the exact
s=1 directional-pressure identity. The derivative majorant is produced on an
explicit positive interval around each scale. Ordinary HLS is used only to
produce the base Riesz pair domain in the L6 specialization.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
namespace HartreeF.PhysicalStretch
open PhysicalDensity ForcingDomain PressureDomain

def physicalStretchPairD1 (α c : ℝ) (ω : Space) (s : ℝ) (b : Space → ℝ) :
    Space × Space → ℝ :=
  pairDensity (fun q => physicalStretchKernelD1 α c ω s (q.1-q.2)) b

def directionalCosSq (ω z : Space) : ℝ := longitudinalSq ω z / ‖z‖^2

def directionalPhysicalPair (α c : ℝ) (ω : Space) (b : Space → ℝ)
    (q : Space × Space) : ℝ :=
  pairDensity (fun z => rieszKernel α c (z.1-z.2)) b q * directionalCosSq ω (q.1-q.2)

def directionalPhysicalMoment (α c : ℝ) (ω : Space) (b : Space → ℝ) : ℝ :=
  ∫ q, directionalPhysicalPair α c ω b q ∂volume.prod volume

theorem physicalStretchPairD1_aestronglyMeasurable (α c : ℝ) (ω : Space) (s : ℝ)
    {b : Space → ℝ} (hb : AEStronglyMeasurable b volume) :
    AEStronglyMeasurable (physicalStretchPairD1 α c ω s b) (volume.prod volume) :=
  pairDensity_aestronglyMeasurable
    ((physicalStretchKernelD1_measurable α c ω s).comp
      (measurable_fst.sub measurable_snd)).aestronglyMeasurable hb

theorem physicalStretchPairD1_norm_le_compact {α c : ℝ} (hα3 : α < 3)
    (hc : 0 ≤ c) {ω : Space} (hω : ‖ω‖ = 1)
    {m M s : ℝ} (hm : 0 < m) (hms : m ≤ s) (hsM : s ≤ M)
    {b : Space → ℝ} (hb0 : ∀ x, 0 ≤ b x) (q : Space × Space) :
    ‖physicalStretchPairD1 α c ω s b q‖ ≤ compactDerivativeBound α m M *
      pairDensity (fun z => rieszKernel α c (z.1-z.2)) b q := by
  have hk := physicalStretchKernelD1_abs_le_riesz_compact hα3 hc hω hm hms hsM (q.1-q.2)
  unfold physicalStretchPairD1 pairDensity
  rw [norm_mul, norm_mul, Real.norm_eq_abs (b q.1), Real.norm_eq_abs (b q.2),
    abs_of_nonneg (hb0 q.1), abs_of_nonneg (hb0 q.2), Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hk (hb0 q.2)) (hb0 q.1)).trans_eq (by ring)

theorem physicalStretchPair_hasDerivAt {α c : ℝ} (hα3 : α < 3)
    {ω : Space} (hω : ‖ω‖ = 1) {s : ℝ} (hs : 0 < s)
    (b : Space → ℝ) (q : Space × Space) :
    HasDerivAt (fun t => physicalStretchPair α c ω t b q)
      (physicalStretchPairD1 α c ω s b q) s :=
  ((physicalStretchKernel_hasDerivAt hα3 hω hs (q.1-q.2)).mul_const (b q.2)).mul_const (b q.1)

/-- Genuine derivative under the product-volume integral, at every positive scale. -/
theorem physicalStretchEnergy_hasDerivAt {α c : ℝ} (hα3 : α < 3)
    (hc : 0 ≤ c) {ω : Space} (hω : ‖ω‖ = 1) {s : ℝ} (hs : 0 < s)
    {b : Space → ℝ} (hb : AEStronglyMeasurable b volume) (hb0 : ∀ x, 0 ≤ b x)
    (hint : Integrable (pairDensity (fun q => rieszKernel α c (q.1-q.2)) b)
      (volume.prod volume)) :
    Integrable (physicalStretchPairD1 α c ω s b) (volume.prod volume) ∧
    HasDerivAt (physicalStretchEnergy α c ω b)
      (∫ q, physicalStretchPairD1 α c ω s b q ∂volume.prod volume) s := by
  have hm : 0 < s/2 := by linarith
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.prod volume) (s := Set.Ioo (s/2) (s+1))
    (F := fun t q => physicalStretchPair α c ω t b q)
    (F' := fun t q => physicalStretchPairD1 α c ω t b q)
    (bound := fun q => compactDerivativeBound α (s/2) (s+1) *
      pairDensity (fun z => rieszKernel α c (z.1-z.2)) b q)
    (Ioo_mem_nhds (by linarith) (by linarith))
  · exact Eventually.of_forall (fun t => physicalStretchPair_aestronglyMeasurable α c ω t hb)
  · exact physicalStretchPair_integrable hα3 hc hω hs hb hb0 hint
  · exact physicalStretchPairD1_aestronglyMeasurable α c ω s hb
  · filter_upwards [] with q
    intro t ht
    exact physicalStretchPairD1_norm_le_compact hα3 hc hω hm ht.1.le ht.2.le hb0 q
  · exact hint.const_mul _
  · filter_upwards [] with q
    intro t ht
    exact physicalStretchPair_hasDerivAt hα3 hω (hm.trans ht.1) b q

theorem directionalCosSq_nonneg (ω z : Space) : 0 ≤ directionalCosSq ω z :=
  div_nonneg (longitudinalSq_nonneg ω z) (sq_nonneg _)

theorem directionalCosSq_le_one {ω : Space} (hω : ‖ω‖ = 1) (z : Space) :
    directionalCosSq ω z ≤ 1 := by
  by_cases hz : z=0
  · subst z
    simp [directionalCosSq, longitudinalSq]
  · exact (div_le_one (sq_pos_of_pos (norm_pos_iff.mpr hz))).mpr
      (longitudinalSq_le_norm_sq hω z)

theorem directionalCosSq_measurable (ω : Space) : Measurable (directionalCosSq ω) :=
  ((continuous_const.inner continuous_id).pow 2).measurable.div (measurable_norm.pow_const 2)

theorem directionalPhysicalPair_integrable {α c : ℝ} (hc : 0 ≤ c)
    {ω : Space} (hω : ‖ω‖ = 1) {b : Space → ℝ} (hb0 : ∀ x, 0 ≤ b x)
    (hint : Integrable (pairDensity (fun q => rieszKernel α c (q.1-q.2)) b)
      (volume.prod volume)) :
    Integrable (directionalPhysicalPair α c ω b) (volume.prod volume) := by
  apply hint.mono'
    (hint.aestronglyMeasurable.mul ((directionalCosSq_measurable ω).comp
      (measurable_fst.sub measurable_snd)).aestronglyMeasurable)
  filter_upwards [] with q
  have hp : 0 ≤ pairDensity (fun z => rieszKernel α c (z.1-z.2)) b q := by
    apply pairDensity_nonneg _ hb0
    intro z
    unfold rieszKernel
    positivity
  change ‖pairDensity (fun z => rieszKernel α c (z.1-z.2)) b q * directionalCosSq ω (q.1-q.2)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp (directionalCosSq_nonneg ω (q.1-q.2)))]
  exact mul_le_of_le_one_right hp (directionalCosSq_le_one hω _)

theorem physicalStretchPairD1_one {α c : ℝ} (hα3 : α < 3)
    (ω : Space) (b : Space → ℝ) (q : Space × Space) :
    physicalStretchPairD1 α c ω 1 b q =
      ((1+α)/2) * pairDensity (fun z => rieszKernel α c (z.1-z.2)) b q +
      ((3-α)/2) * directionalPhysicalPair α c ω b q := by
  unfold physicalStretchPairD1 pairDensity
  dsimp only
  rw [physicalStretchKernelD1_one hα3]
  unfold directionalPhysicalPair pairDensity directionalCosSq
  ring

/-- The physical derivative at one is exactly the directional pressure numerator. -/
theorem physicalStretchEnergy_hasDerivAt_one {α c : ℝ} (hα3 : α < 3)
    (hc : 0 ≤ c) {ω : Space} (hω : ‖ω‖ = 1)
    {b : Space → ℝ} (hb : AEStronglyMeasurable b volume) (hb0 : ∀ x, 0 ≤ b x)
    (hint : Integrable (pairDensity (fun q => rieszKernel α c (q.1-q.2)) b)
      (volume.prod volume)) :
    HasDerivAt (physicalStretchEnergy α c ω b)
      (((1+α)/2) * (∫ q, pairDensity (fun z => rieszKernel α c (z.1-z.2)) b q
          ∂volume.prod volume) + ((3-α)/2) * directionalPhysicalMoment α c ω b) 1 := by
  have h := (physicalStretchEnergy_hasDerivAt hα3 hc hω (by norm_num : (0:ℝ)<1) hb hb0 hint).2
  have he : (∫ q, physicalStretchPairD1 α c ω 1 b q ∂volume.prod volume) =
      ((1+α)/2) * (∫ q, pairDensity (fun z => rieszKernel α c (z.1-z.2)) b q
          ∂volume.prod volume) + ((3-α)/2) * directionalPhysicalMoment α c ω b := by
    simp_rw [physicalStretchPairD1_one hα3]
    rw [integral_add (hint.const_mul _) ((directionalPhysicalPair_integrable hc hω hb0 hint).const_mul _),
      integral_const_mul, integral_const_mul]
    rfl
  rwa [he] at h

/-- Actual L6 Hartree specialization, with the ordinary HLS interface as the only external analysis. -/
theorem hartree_physicalStretchEnergy_hasDerivAt_one {α c : ℝ} (hHLS : OrdinaryHLS α c)
    {ω : Space} (hω : ‖ω‖ = 1) {f : Space → ℂ} (hf : MemLp f 6 volume) :
    HasDerivAt (physicalStretchEnergy α c ω (powerDensity α f))
      (((1+α)/2) * (∫ x, potential α c f x * powerDensity α f x) +
        ((3-α)/2) * directionalPhysicalMoment α c ω (powerDensity α f)) 1 := by
  rw [← hartree_energy_pair_identity hHLS hf]
  apply physicalStretchEnergy_hasDerivAt_one hHLS.order_lt_three hHLS.normalization_pos.le hω
  · exact (hf.aestronglyMeasurable.norm.aemeasurable.pow_const (3+α)).aestronglyMeasurable
  · intro x
    exact Real.rpow_nonneg (norm_nonneg _) _
  · exact rieszPairDensity_integrable hHLS hf

#print axioms physicalStretchPairD1_aestronglyMeasurable
#print axioms physicalStretchPairD1_norm_le_compact
#print axioms physicalStretchPair_hasDerivAt
#print axioms physicalStretchEnergy_hasDerivAt
#print axioms directionalCosSq_nonneg
#print axioms directionalCosSq_le_one
#print axioms directionalCosSq_measurable
#print axioms directionalPhysicalPair_integrable
#print axioms physicalStretchPairD1_one
#print axioms physicalStretchEnergy_hasDerivAt_one
#print axioms hartree_physicalStretchEnergy_hasDerivAt_one
end HartreeF.PhysicalStretch
