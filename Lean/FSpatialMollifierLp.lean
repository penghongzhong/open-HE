import FSpatialLpIdentification

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology Convolution
namespace HartreeF.ProfileSpatialSmoothing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Literal normalized spatial convolution of an actual field. -/
def spatialMollify (φ : ContDiffBump (0 : Space)) (f : Space → E) : Space → E :=
  (φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f

theorem spatialMollify_congr (φ : ContDiffBump (0 : Space)) {f g : Space → E}
    (hfg : f =ᵐ[volume] g) : spatialMollify φ f = spatialMollify φ g :=
  convolution_congr _ EventuallyEq.rfl hfg

variable [CompleteSpace E] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

include q

theorem spatialMollify_eq_lpMollify (hp : p ≠ ∞) (φ : ContDiffBump (0 : Space))
    {f : Space → E} (hf : MemLp f p volume) (hf1 : Integrable f volume) :
    spatialMollify φ f =ᵐ[volume] (lpMollify φ (hf.toLp f) : Space → E) := by
  have h := lpMollify_coe_ae_of_integrable (q := q) hp φ (hf.toLp f)
    (hf1.congr hf.coeFn_toLp.symm)
  rw [← spatialMollify, spatialMollify_congr φ hf.coeFn_toLp] at h
  exact h.symm

/-- The literal convolution is an Lp contraction; no approximation interface is assumed. -/
theorem spatialMollify_eLpNorm_le (hp : p ≠ ∞) (φ : ContDiffBump (0 : Space))
    {f : Space → E} (hf : MemLp f p volume) (hf1 : Integrable f volume) :
    eLpNorm (spatialMollify φ f) p volume ≤ eLpNorm f p volume := by
  rw [eLpNorm_congr_ae (spatialMollify_eq_lpMollify (q := q) hp φ hf hf1), ← Lp.enorm_def,
    ← Lp.enorm_toLp hf, enorm_le_iff_norm_le]
  exact lpMollify_norm_le φ (hf.toLp f)

theorem spatialMollify_memLp (hp : p ≠ ∞) (φ : ContDiffBump (0 : Space))
    {f : Space → E} (hf : MemLp f p volume) (hf1 : Integrable f volume) :
    MemLp (spatialMollify φ f) p volume :=
  lt_of_le_of_lt (spatialMollify_eLpNorm_le (q := q) hp φ hf hf1) hf

/-- Genuine strong spatial approximate-identity convergence for actual Lp ∩ L1 fields. -/
theorem spatialMollify_eLpNorm_sub_tendsto {ι : Type*} {l : Filter ι} (hp : p ≠ ∞)
    {φ : ι → ContDiffBump (0 : Space)} (hφ : Tendsto (fun n => (φ n).rOut) l (𝓝 0))
    {f : Space → E} (hf : MemLp f p volume) (hf1 : Integrable f volume) :
    Tendsto (fun n => eLpNorm (fun x => spatialMollify (φ n) f x - f x) p volume) l (𝓝 0) := by
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm (fun n => lpMollify (φ n) (hf.toLp f)) f hf).mp
    (lpMollify_tendsto hp hφ (hf.toLp f))
  apply h.congr'
  filter_upwards [] with n
  exact (eLpNorm_congr_ae ((spatialMollify_eq_lpMollify (q := q) hp (φ n) hf hf1).sub EventuallyEq.rfl)).symm

#print axioms spatialMollify_eLpNorm_le
#print axioms spatialMollify_eLpNorm_sub_tendsto
end HartreeF.ProfileSpatialSmoothing
