import PhysicalStretchKernel
import PhysicalDensityTruncation

/-!
Actual physical double-integral domains for positive directional stretch scales.
Generic nonnegative densities need only finite physical Riesz pair energy; the
Hartree specialization produces this from the inherited ordinary HLS and L6.
The checkpoint04 density truncation is now instantiated with the literal K_s.
No Fourier representation, integrated convexity, or directional coercivity is assumed.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
namespace HartreeF.PhysicalStretch
open PhysicalDensity ForcingDomain PressureDomain

def physicalStretchPair (α c : ℝ) (ω : Space) (s : ℝ) (b : Space → ℝ) :
    Space × Space → ℝ :=
  pairDensity (fun q => physicalStretchKernel α c ω s (q.1-q.2)) b

def physicalStretchEnergy (α c : ℝ) (ω : Space) (b : Space → ℝ) (s : ℝ) : ℝ :=
  ∫ q, physicalStretchPair α c ω s b q ∂volume.prod volume

theorem physicalStretchPair_nonneg {α c : ℝ} (hc : 0 ≤ c)
    {ω : Space} (hω : ‖ω‖ = 1) {s : ℝ} (hs : 0 ≤ s)
    {b : Space → ℝ} (hb0 : ∀ x, 0 ≤ b x) (q : Space × Space) :
    0 ≤ physicalStretchPair α c ω s b q :=
  pairDensity_nonneg (fun q => physicalStretchKernel_nonneg hc hω hs (q.1-q.2)) hb0 q

theorem physicalStretchPair_aestronglyMeasurable (α c : ℝ) (ω : Space) (s : ℝ)
    {b : Space → ℝ} (hb : AEStronglyMeasurable b volume) :
    AEStronglyMeasurable (physicalStretchPair α c ω s b) (volume.prod volume) :=
  pairDensity_aestronglyMeasurable
    (physicalStretchKernel_pair_measurable α c ω s).aestronglyMeasurable hb

@[simp] theorem physicalStretchPair_one (α c : ℝ) (ω : Space)
    (b : Space → ℝ) (q : Space × Space) :
    physicalStretchPair α c ω 1 b q =
      pairDensity (fun z => rieszKernel α c (z.1-z.2)) b q := by
  simp only [physicalStretchPair, pairDensity, physicalStretchKernel_one]

theorem physicalStretchPair_le_riesz_compact {α c : ℝ} (hα3 : α < 3)
    (hc : 0 ≤ c) {ω : Space} (hω : ‖ω‖ = 1)
    {m M s : ℝ} (hm : 0 < m) (hms : m ≤ s) (hsM : s ≤ M)
    {b : Space → ℝ} (hb0 : ∀ x, 0 ≤ b x) (q : Space × Space) :
    physicalStretchPair α c ω s b q ≤ compactScaleBound α m M *
      pairDensity (fun z => rieszKernel α c (z.1-z.2)) b q := by
  have hk := physicalStretchKernel_le_riesz_compact hα3 hc hω hm hms hsM (q.1-q.2)
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hk (hb0 q.2)) (hb0 q.1)
  unfold physicalStretchPair pairDensity
  exact h.trans_eq (by ring)

/-- Absolute integrability is produced by a proved compact-scale Riesz majorant. -/
theorem physicalStretchPair_integrable_compact {α c : ℝ} (hα3 : α < 3)
    (hc : 0 ≤ c) {ω : Space} (hω : ‖ω‖ = 1)
    {m M s : ℝ} (hm : 0 < m) (hms : m ≤ s) (hsM : s ≤ M)
    {b : Space → ℝ} (hb : AEStronglyMeasurable b volume) (hb0 : ∀ x, 0 ≤ b x)
    (hint : Integrable (pairDensity (fun q => rieszKernel α c (q.1-q.2)) b)
      (volume.prod volume)) :
    Integrable (physicalStretchPair α c ω s b) (volume.prod volume) := by
  apply (hint.const_mul (compactScaleBound α m M)).mono'
    (physicalStretchPair_aestronglyMeasurable α c ω s hb)
  filter_upwards [] with q
  rw [Real.norm_eq_abs, abs_of_nonneg
    (physicalStretchPair_nonneg hc hω (hm.trans_le hms).le hb0 q)]
  exact physicalStretchPair_le_riesz_compact hα3 hc hω hm hms hsM hb0 q

theorem physicalStretchPair_integrable {α c : ℝ} (hα3 : α < 3)
    (hc : 0 ≤ c) {ω : Space} (hω : ‖ω‖ = 1) {s : ℝ} (hs : 0 < s)
    {b : Space → ℝ} (hb : AEStronglyMeasurable b volume) (hb0 : ∀ x, 0 ≤ b x)
    (hint : Integrable (pairDensity (fun q => rieszKernel α c (q.1-q.2)) b)
      (volume.prod volume)) :
    Integrable (physicalStretchPair α c ω s b) (volume.prod volume) :=
  physicalStretchPair_integrable_compact hα3 hc hω hs (le_refl s) (le_refl s) hb hb0 hint

theorem physicalStretchEnergy_le_riesz_compact {α c : ℝ} (hα3 : α < 3)
    (hc : 0 ≤ c) {ω : Space} (hω : ‖ω‖ = 1)
    {m M s : ℝ} (hm : 0 < m) (hms : m ≤ s) (hsM : s ≤ M)
    {b : Space → ℝ} (hb : AEStronglyMeasurable b volume) (hb0 : ∀ x, 0 ≤ b x)
    (hint : Integrable (pairDensity (fun q => rieszKernel α c (q.1-q.2)) b)
      (volume.prod volume)) :
    physicalStretchEnergy α c ω b s ≤ compactScaleBound α m M *
      ∫ q, pairDensity (fun z => rieszKernel α c (z.1-z.2)) b q ∂volume.prod volume := by
  unfold physicalStretchEnergy
  rw [← integral_const_mul]
  exact integral_mono (physicalStretchPair_integrable_compact hα3 hc hω hm hms hsM hb hb0 hint)
    (hint.const_mul _) (physicalStretchPair_le_riesz_compact hα3 hc hω hm hms hsM hb0)

/-- The actual checkpoint04 density cutoff converges at every positive physical scale. -/
theorem physicalStretch_truncation_tendsto {α c : ℝ} (hα3 : α < 3)
    (hc : 0 ≤ c) {ω : Space} (hω : ‖ω‖ = 1) {s : ℝ} (hs : 0 < s)
    {b : Space → ℝ} (hb : AEStronglyMeasurable b volume) (hb0 : ∀ x, 0 ≤ b x)
    (hint : Integrable (pairDensity (fun q => rieszKernel α c (q.1-q.2)) b)
      (volume.prod volume)) :
    Tendsto (fun n : ℕ => physicalStretchEnergy α c ω (truncate b n) s) atTop
      (𝓝 (physicalStretchEnergy α c ω b s)) :=
  truncated_pair_integral_tendsto
    (physicalStretchKernel_pair_measurable α c ω s).aestronglyMeasurable
    (fun q => physicalStretchKernel_nonneg hc hω hs.le (q.1-q.2)) hb hb0
    (physicalStretchPair_integrable hα3 hc hω hs hb hb0 hint)

theorem physicalStretch_truncated_pair_integrable {α c : ℝ} (hα3 : α < 3)
    (hc : 0 ≤ c) {ω : Space} (hω : ‖ω‖ = 1) {s : ℝ} (hs : 0 < s)
    {b : Space → ℝ} (hb : AEStronglyMeasurable b volume) (hb0 : ∀ x, 0 ≤ b x)
    (hint : Integrable (pairDensity (fun q => rieszKernel α c (q.1-q.2)) b)
      (volume.prod volume)) (n : ℕ) :
    Integrable (physicalStretchPair α c ω s (truncate b n)) (volume.prod volume) :=
  truncated_pair_integrable
    (physicalStretchKernel_pair_measurable α c ω s).aestronglyMeasurable
    (fun q => physicalStretchKernel_nonneg hc hω hs.le (q.1-q.2)) hb hb0
    (physicalStretchPair_integrable hα3 hc hω hs hb hb0 hint) n

/-- Only ordinary HLS and L6 are needed for every actual stretched Hartree pair. -/
theorem hartree_physicalStretchPair_integrable {α c : ℝ} (hHLS : OrdinaryHLS α c)
    {ω : Space} (hω : ‖ω‖ = 1) {s : ℝ} (hs : 0 < s)
    {f : Space → ℂ} (hf : MemLp f 6 volume) :
    Integrable (physicalStretchPair α c ω s (powerDensity α f)) (volume.prod volume) := by
  apply physicalStretchPair_integrable hHLS.order_lt_three hHLS.normalization_pos.le hω hs
  · exact (hf.aestronglyMeasurable.norm.aemeasurable.pow_const (3+α)).aestronglyMeasurable
  · intro x
    exact Real.rpow_nonneg (norm_nonneg _) _
  · exact rieszPairDensity_integrable hHLS hf

theorem hartree_physicalStretchEnergy_one {α c : ℝ} (hHLS : OrdinaryHLS α c)
    (ω : Space) {f : Space → ℂ} (hf : MemLp f 6 volume) :
    physicalStretchEnergy α c ω (powerDensity α f) 1 =
      ∫ x, potential α c f x * powerDensity α f x := by
  unfold physicalStretchEnergy
  simp only [physicalStretchPair_one]
  exact hartree_energy_pair_identity hHLS hf

theorem hartree_physicalStretch_truncation_tendsto {α c : ℝ} (hHLS : OrdinaryHLS α c)
    {ω : Space} (hω : ‖ω‖ = 1) {s : ℝ} (hs : 0 < s)
    {f : Space → ℂ} (hf : MemLp f 6 volume) :
    Tendsto (fun n : ℕ => physicalStretchEnergy α c ω (truncate (powerDensity α f) n) s)
      atTop (𝓝 (physicalStretchEnergy α c ω (powerDensity α f) s)) := by
  apply physicalStretch_truncation_tendsto hHLS.order_lt_three hHLS.normalization_pos.le hω hs
  · exact (hf.aestronglyMeasurable.norm.aemeasurable.pow_const (3+α)).aestronglyMeasurable
  · intro x
    exact Real.rpow_nonneg (norm_nonneg _) _
  · exact rieszPairDensity_integrable hHLS hf

#print axioms physicalStretchPair_nonneg
#print axioms physicalStretchPair_aestronglyMeasurable
#print axioms physicalStretchPair_one
#print axioms physicalStretchPair_le_riesz_compact
#print axioms physicalStretchPair_integrable_compact
#print axioms physicalStretchPair_integrable
#print axioms physicalStretchEnergy_le_riesz_compact
#print axioms physicalStretch_truncation_tendsto
#print axioms physicalStretch_truncated_pair_integrable
#print axioms hartree_physicalStretchPair_integrable
#print axioms hartree_physicalStretchEnergy_one
#print axioms hartree_physicalStretch_truncation_tendsto
end HartreeF.PhysicalStretch
