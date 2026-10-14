import Lemma_4_1_KelvinExtension
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! Actual global H1 Kelvin extension relative to the universal, standard
smooth-interface Sobolev gluing theorem, stated explicitly below. All
Kelvin-specific hypotheses are proved in Lean, including removal of the axis,
compact support, and regularity/matching at the cylinder. No Kelvin assertion
is an input. The weak derivative is defined by actual Lebesgue test integrals.
See audit/EXTERNAL_INTERFACES.txt for the standard gluing interface and source. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace BWork.Kelvin

/-- The usual distributional weak derivative, tested in every constant
spatial direction against every smooth compactly supported scalar test. -/
def IsWeakDerivative (u : Space → ℝ) (D : Space → Space →L[ℝ] ℝ) : Prop :=
  ∀ (e : Space) (φ : Space → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ z, u z * fderiv ℝ φ z e) = -(∫ z, D z e * φ z)

/-- Genuine inhomogeneous H1: the function and its weak derivative lie in L2. -/
def InH1 (u : Space → ℝ) (D : Space → Space →L[ℝ] ℝ) : Prop :=
  MemLp u 2 volume ∧ MemLp D 2 volume ∧ IsWeakDerivative u D

/-- Registered universal analysis interface. This is the compactly supported
C1 / regular-level-set specialization of the standard Sobolev gluing theorem.
The two pieces need not have matching classical derivatives. The condition
`fderiv ρ ≠ 0` excludes a singular interface. There is no radius, inversion,
energy estimate, or paper-specific conclusion in this interface. -/
def SmoothInterfaceGluing : Prop :=
  ∀ (ρ u v : Space → ℝ), ContDiff ℝ 1 ρ →
    (∀ z, ρ z = 0 → fderiv ℝ ρ z ≠ 0) →
    ContDiff ℝ 1 u → ContDiff ℝ 1 v →
    (∀ z, ρ z = 0 → u z = v z) →
    HasCompactSupport (fun z => if ρ z < 0 then u z else v z) →
    InH1 (fun z => if ρ z < 0 then u z else v z)
      (fun z => if ρ z < 0 then fderiv ℝ u z else fderiv ℝ v z)

def radiusDerivative (z : Space) : Space →L[ℝ] ℝ :=
  (2*z.2.1) • ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Plane)) +
  (2*z.2.2) • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Plane))

theorem hasFDerivAt_radiusSq (z : Space) : HasFDerivAt radiusSq (radiusDerivative z) z := by
  have hx : HasFDerivAt (fun q : Space => q.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Plane)) z :=
    hasFDerivAt_fst.comp z hasFDerivAt_snd
  have hy : HasFDerivAt (fun q : Space => q.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Plane)) z :=
    hasFDerivAt_snd.comp z hasFDerivAt_snd
  convert! (hx.pow 2).add (hy.pow 2) using 1
  ext <;> simp [radiusDerivative]

theorem cylinder_regular {R : ℝ} (hR : 0 < R) (z : Space)
    (hz : radiusSq z - R^2 = 0) :
    fderiv ℝ (fun q => radiusSq q - R^2) z ≠ 0 := by
  rw [fderiv_sub_const,(hasFDerivAt_radiusSq z).fderiv]
  intro he
  have hh := congrArg (fun F : Space →L[ℝ] ℝ => F (0,z.2)) he
  simp [radiusDerivative] at hh
  unfold radiusSq s at hz
  nlinarith [sq_pos_of_pos hR]

def extensionDerivative (R : ℝ) (f : Space → ℝ) (z : Space) : Space →L[ℝ] ℝ :=
  if radiusSq z < R^2 then fderiv ℝ (innerExtension R f) z else fderiv ℝ f z

/-- The actual extension belongs to H1, including all weak test identities.
Only the universal standard gluing theorem is external. -/
theorem extension_inH1 (glue : SmoothInterfaceGluing) {R : ℝ} (hR : 0 < R)
    {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    InH1 (extension R f) (extensionDerivative R f) := by
  have hg := glue (fun z => radiusSq z - R^2) (innerExtension R f) f
    (radiusSq_contDiff.sub contDiff_const |>.of_le (by norm_num))
    (cylinder_regular hR)
    ((innerExtension_contDiff hR hf hc).of_le (by norm_num))
    (hf.of_le (by norm_num))
    (fun z hz => extension_circle hR f (sub_eq_zero.mp hz))
  have heq : (fun z : Space => if radiusSq z - R^2 < 0 then innerExtension R f z else f z) =
      extension R f := by funext z; simp [extension]
  have hs := extension_hasCompactSupport R hc
  rw [← heq] at hs
  have hout := hg hs
  change InH1 (fun z => if radiusSq z < R^2 then innerExtension R f z else f z)
    (fun z => if radiusSq z < R^2 then fderiv ℝ (innerExtension R f) z else fderiv ℝ f z)
  simpa only [sub_lt_zero] using hout

def cylinderJacobian (R : ℝ) (z : Space) : Space →L[ℝ] Space :=
  (ContinuousLinearMap.fst ℝ ℝ Plane).prod
    ((jacobian R z.2).comp (ContinuousLinearMap.snd ℝ ℝ Plane))

theorem derivative_cylinder_inversion (R : ℝ) (z : Space) (hz : radiusSq z ≠ 0) :
    HasFDerivAt (fun q : Space => (q.1,inversion R q.2)) (cylinderJacobian R z) z := by
  exact hasFDerivAt_fst.prodMk ((derivative_inversion R z.2 hz).comp z hasFDerivAt_snd)

theorem innerExtension_fderiv {R : ℝ} {f : Space → ℝ} {z : Space}
    (hf : DifferentiableAt ℝ f (z.1,inversion R z.2)) (hz : radiusSq z ≠ 0) :
    fderiv ℝ (innerExtension R f) z =
      (fderiv ℝ f (z.1,inversion R z.2)).comp (cylinderJacobian R z) := by
  have hn : ∀ᶠ q in 𝓝 z, radiusSq q ≠ 0 :=
    radiusSq_contDiff.continuous.continuousAt.eventually (isOpen_compl_singleton.mem_nhds hz)
  have he : innerExtension R f =ᶠ[𝓝 z] (fun q : Space => f (q.1,inversion R q.2)) := by
    filter_upwards [hn] with q hq
    simp [innerExtension,hq]
  rw [he.fderiv_eq]
  exact (hf.hasFDerivAt.comp z (derivative_cylinder_inversion R z hz)).fderiv

theorem innerExtension_longitudinal {R : ℝ} {f : Space → ℝ} {z : Space}
    (hf : DifferentiableAt ℝ f (z.1,inversion R z.2)) (hz : radiusSq z ≠ 0) :
    fderiv ℝ (innerExtension R f) z (1,0) = fderiv ℝ f (z.1,inversion R z.2) (1,0) := by
  rw [innerExtension_fderiv hf hz]
  simp [cylinderJacobian]

theorem innerExtension_transverse {R : ℝ} {f : Space → ℝ} {z : Space}
    (hf : DifferentiableAt ℝ f (z.1,inversion R z.2)) (hz : radiusSq z ≠ 0) (e : Plane) :
    fderiv ℝ (innerExtension R f) z (0,e) =
      fderiv ℝ f (z.1,inversion R z.2) (0,jacobian R z.2 e) := by
  rw [innerExtension_fderiv hf hz]
  simp [cylinderJacobian]

#print axioms hasFDerivAt_radiusSq
#print axioms cylinder_regular
#print axioms extension_inH1
#print axioms derivative_cylinder_inversion
#print axioms innerExtension_fderiv
#print axioms innerExtension_longitudinal
#print axioms innerExtension_transverse
end BWork.Kelvin
