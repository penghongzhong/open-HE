import FActualGradientWeakTests
import FGeneralPackedCoupling
import FFiniteCandidateExpansion

/-! Finite-family literal forcing weak gradients and canonical-frame coupling.
Author source, UNCOMPILED. All finite closures below include the empty family.
The ordinary density, Sobolev and HLS hypotheses remain explicit. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace HartreeF.FiniteProfileWeakGradient
open TimeHolder SobolevStretch StationarySelfTest WeakHartreeProduct ForcingDomain
open DerivativeMajorization GeneralProfileCross ProfileApproximation ProfileSpatialSmoothing
open EnergySpace CriticalTimeSobolev CompactCross CriticalAffine AffineMixed

variable {ι : Type*} [DecidableEq ι]

/-- The same literal error as in the finite-profile perturbation calculation. -/
def literalDefect (s : Finset ι) (α c : ℝ) (u : ι → Space → ℂ) : Space → ℂ :=
  fun x => forcing α c (fun y => ∑ i ∈ s, u i y) x -
    ∑ i ∈ s, forcing α c (u i) x

/-- This is assembled from genuine forcing gradients, before any mixed norm. -/
def gradientDefect (s : Finset ι) (α c : ℝ) (u : ι → Space → ℂ)
    (U V : ι → Space → Space) : Space → EuclideanSpace ℂ (Fin 3) :=
  fun x => actualFullGradient α c (fun y => ∑ i ∈ s, u i y)
    (fun y => ∑ i ∈ s, U i y) (fun y => ∑ i ∈ s, V i y) x -
      ∑ i ∈ s, actualFullGradient α c (u i) (U i) (V i) x

/-- A genuine jointly measurable candidate is built from joint input fields. -/
def jointCandidateDefect (s : Finset ι) (α c : ℝ) (u : ι → Space → ℂ)
    (U V : ι → Space → Space) : Space → EuclideanSpace ℂ (Fin 3) :=
  fun x => candidateFullGradient α c (fun y => ∑ i ∈ s, u i y)
    (fun y => ∑ i ∈ s, U i y) (fun y => ∑ i ∈ s, V i y) x -
      ∑ i ∈ s, candidateFullGradient α c (u i) (U i) (V i) x

theorem weakGradient_zero :
    HasWeakGradient (fun _ : Space => (0 : ℝ)) (fun _ => 0) := by
  refine ⟨locallyIntegrable_zero, locallyIntegrable_zero, ?_⟩
  intro e phi hphi hc
  simp

theorem weakGradient_add {f g : Space → ℝ} {F G : Space → Space}
    (hf : HasWeakGradient f F) (hg : HasWeakGradient g G) :
    HasWeakGradient (fun x => f x + g x) (fun x => F x + G x) := by
  refine ⟨hf.function_local.add hg.function_local,
    hf.gradient_local.add hg.gradient_local, ?_⟩
  intro e phi hphi hc
  have hft := hf.test_integrable hphi hc e
  have hgt := hg.test_integrable hphi hc e
  simp only [add_mul, inner_add_left]
  rw [integral_add hft.1 hgt.1, integral_add hft.2 hgt.2,
    hf.integration_by_parts e phi hphi hc, hg.integration_by_parts e phi hphi hc]
  ring

/-- Finite distributional closure includes the true compact-test integral domains. -/
theorem weakGradient_sum (s : Finset ι) (f : ι → Space → ℝ)
    (F : ι → Space → Space) (h : ∀ i ∈ s, HasWeakGradient (f i) (F i)) :
    HasWeakGradient (fun x => ∑ i ∈ s, f i x) (fun x => ∑ i ∈ s, F i x) := by
  revert h
  induction s using Finset.induction_on with
  | empty => intro h; simpa using weakGradient_zero
  | @insert a s ha ih =>
      intro h
      simpa only [Finset.sum_insert ha] using
        weakGradient_add (h a (Finset.mem_insert_self a s))
          (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Finite homogeneous Sobolev closure, with no scalar L2 premise. -/
theorem inDotH1_sum (s : Finset ι) (u : ι → Space → ℂ)
    (U V : ι → Space → Space) (h : ∀ i ∈ s, InDotH1 (u i) (U i) (V i)) :
    InDotH1 (fun x => ∑ i ∈ s, u i x)
      (fun x => ∑ i ∈ s, U i x) (fun x => ∑ i ∈ s, V i x) := by
  refine ⟨memLp_finsetSum s (fun i hi => (h i hi).function_L6),
    memLp_finsetSum s (fun i hi => (h i hi).real_gradient_L2),
    memLp_finsetSum s (fun i hi => (h i hi).imag_gradient_L2), ?_, ?_⟩
  · simpa using weakGradient_sum s (fun i x => (u i x).re) U
      (fun i hi => (h i hi).real_weak)
  · simpa using weakGradient_sum s (fun i x => (u i x).im) V
      (fun i hi => (h i hi).imag_weak)

theorem gradientReal_defect (s : Finset ι) (α c : ℝ) (u : ι → Space → ℂ)
    (U V : ι → Space → Space) (x : Space) :
    gradientReal (gradientDefect s α c u U V x) =
      forcingGradientRe α c (fun y => ∑ i ∈ s, u i y)
        (fun y => ∑ i ∈ s, U i y) (fun y => ∑ i ∈ s, V i y) x -
          ∑ i ∈ s, forcingGradientRe α c (u i) (U i) (V i) x := by
  ext j
  simp [gradientDefect, gradientReal, actualFullGradient_coordinate, map_sum]

theorem gradientImag_defect (s : Finset ι) (α c : ℝ) (u : ι → Space → ℂ)
    (U V : ι → Space → Space) (x : Space) :
    gradientImag (gradientDefect s α c u U V x) =
      forcingGradientIm α c (fun y => ∑ i ∈ s, u i y)
        (fun y => ∑ i ∈ s, U i y) (fun y => ∑ i ∈ s, V i y) x -
          ∑ i ∈ s, forcingGradientIm α c (u i) (U i) (V i) x := by
  ext j
  simp [gradientDefect, gradientImag, actualFullGradient_coordinate, map_sum]

/-- The finite forcing defect is produced directly from its finite family. It is
not a two-input nonlinear difference wrapper with a sum substituted for one input. -/
theorem finite_forcing_hasWeakGradients (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {α c : ℝ} (hH : OrdinaryHLS α c)
    (s : Finset ι) (u : ι → Space → ℂ) (U V : ι → Space → Space)
    (hd : ∀ i ∈ s, InDotH1 (u i) (U i) (V i))
    (hu : ∀ i ∈ s, MemLp (u i) 10 volume)
    (hU : ∀ i ∈ s, MemLp (U i) (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : ∀ i ∈ s, MemLp (V i) (ENNReal.ofReal (30/13 : ℝ)) volume) :
    HasWeakGradient (fun x => (literalDefect s α c u x).re)
      (fun x => gradientReal (gradientDefect s α c u U V x)) ∧
    HasWeakGradient (fun x => (literalDefect s α c u x).im)
      (fun x => gradientImag (gradientDefect s α c u U V x)) := by
  have hsum := hartree_forcing_weak_gradients hDensity hSob hH
    (inDotH1_sum s u U V hd) (memLp_finsetSum s hu)
    (memLp_finsetSum s hU) (memLp_finsetSum s hV)
  have hi (i : ι) (hi : i ∈ s) :=
    hartree_forcing_weak_gradients hDensity hSob hH (hd i hi) (hu i hi) (hU i hi) (hV i hi)
  constructor
  · simpa only [literalDefect, Complex.sub_re, Complex.re_sum, gradientReal_defect] using
      TimeHolder.weakGradient_sub hsum.1
        (weakGradient_sum s (fun i x => (forcing α c (u i) x).re)
          (fun i => forcingGradientRe α c (u i) (U i) (V i)) (fun i hit => (hi i hit).1))
  · simpa only [literalDefect, Complex.sub_im, Complex.im_sum, gradientImag_defect] using
      TimeHolder.weakGradient_sub hsum.2
        (weakGradient_sum s (fun i x => (forcing α c (u i) x).im)
          (fun i => forcingGradientIm α c (u i) (U i) (V i)) (fun i hit => (hi i hit).2))

/-- The full compact-smooth coordinate contract, including both true integrals. -/
def CoordinateTests (f : Space → ℂ) (G : Space → EuclideanSpace ℂ (Fin 3)) : Prop :=
  ∀ (j : Fin 3) (phi : Space → ℝ),
    ContDiff ℝ (⊤ : ℕ∞) phi → HasCompactSupport phi →
    Integrable (fun x => (f x).re *
      fderiv ℝ phi x (EuclideanSpace.basisFun (Fin 3) ℝ j)) volume ∧
    Integrable (fun x => (G x j).re * phi x) volume ∧
    (∫ x, (f x).re * fderiv ℝ phi x (EuclideanSpace.basisFun (Fin 3) ℝ j)) =
      -(∫ x, (G x j).re * phi x) ∧
    Integrable (fun x => (f x).im *
      fderiv ℝ phi x (EuclideanSpace.basisFun (Fin 3) ℝ j)) volume ∧
    Integrable (fun x => (G x j).im * phi x) volume ∧
    (∫ x, (f x).im * fderiv ℝ phi x (EuclideanSpace.basisFun (Fin 3) ℝ j)) =
      -(∫ x, (G x j).im * phi x)

theorem finite_forcing_coordinate_tests (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {α c : ℝ} (hH : OrdinaryHLS α c)
    (s : Finset ι) (u : ι → Space → ℂ) (U V : ι → Space → Space)
    (hd : ∀ i ∈ s, InDotH1 (u i) (U i) (V i))
    (hu : ∀ i ∈ s, MemLp (u i) 10 volume)
    (hU : ∀ i ∈ s, MemLp (U i) (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : ∀ i ∈ s, MemLp (V i) (ENNReal.ofReal (30/13 : ℝ)) volume) :
    CoordinateTests (literalDefect s α c u) (gradientDefect s α c u U V) := by
  obtain ⟨hR, hI⟩ := finite_forcing_hasWeakGradients hDensity hSob hH s u U V hd hu hU hV
  exact weakGradients_coordinate_tests hR hI

/-- One common spatial conull set for the finite family and its sum. -/
theorem gradientDefect_candidate_ae {α c : ℝ} (hH : OrdinaryHLS α c)
    (s : Finset ι) (u : ι → Space → ℂ) (U V : ι → Space → Space)
    (hd : ∀ i ∈ s, InDotH1 (u i) (U i) (V i))
    (hu : ∀ i ∈ s, MemLp (u i) 10 volume)
    (hU : ∀ i ∈ s, MemLp (U i) (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : ∀ i ∈ s, MemLp (V i) (ENNReal.ofReal (30/13 : ℝ)) volume) :
    gradientDefect s α c u U V =ᵐ[volume] jointCandidateDefect s α c u U V := by
  have hsum := actualFullGradient_candidate_ae hH _ _ _
    (inDotH1_sum s u U V hd) (memLp_finsetSum s hu)
    (memLp_finsetSum s hU) (memLp_finsetSum s hV)
  have hi : ∀ᵐ x ∂volume, ∀ i ∈ s,
      actualFullGradient α c (u i) (U i) (V i) x =
        candidateFullGradient α c (u i) (U i) (V i) x :=
    (eventually_all_finset s).2 (fun i hi =>
      actualFullGradient_candidate_ae hH _ _ _ (hd i hi) (hu i hi) (hU i hi) (hV i hi))
  filter_upwards [hsum, hi] with x hx hix
  exact congrArg₂ (· - ·) hx (Finset.sum_congr rfl hix)

theorem directionalField_sum (s : Finset ι) (U V : ι → Space → Space) (e : Space) :
    directionalField (fun x => ∑ i ∈ s, U i x) (fun x => ∑ i ∈ s, V i x) e =
      (fun x => ∑ i ∈ s, directionalField (U i) (V i) e x) := by
  funext x
  apply Complex.ext <;> simp [directionalField, sum_inner, map_sum]

theorem candidateFullGradient_coordinate (α c : ℝ) (u : Space → ℂ)
    (U V : Space → Space) (x : Space) (j : Fin 3) :
    candidateFullGradient α c u U V x j =
      directionalCandidate α c u (directionalField U V (EuclideanSpace.basisFun (Fin 3) ℝ j)) x := by
  fin_cases j <;> simp [candidateFullGradient, packGradient_coordinate]

/-- A pointwise identity for the chosen joint candidate; this is the bridge to
the scalar finite-family domain and six-term estimates. -/
theorem jointCandidateDefect_coordinate (s : Finset ι) (α c : ℝ)
    (u : ι → Space → ℂ) (U V : ι → Space → Space) (x : Space) (j : Fin 3) :
    jointCandidateDefect s α c u U V x j =
      FiniteCandidateExpansion.candidateDefect α c s u
        (fun i => directionalField (U i) (V i) (EuclideanSpace.basisFun (Fin 3) ℝ j)) x := by
  simp [jointCandidateDefect, candidateFullGradient_coordinate,
    directionalField_sum, FiniteCandidateExpansion.candidateDefect, map_sum]

/-- All three coordinates hold on the same finite good set. The right side is
exactly the candidate defect consumed by the finite six-term expansion. -/
theorem gradientDefect_coordinates_ae {α c : ℝ} (hH : OrdinaryHLS α c)
    (s : Finset ι) (u : ι → Space → ℂ) (U V : ι → Space → Space)
    (hd : ∀ i ∈ s, InDotH1 (u i) (U i) (V i))
    (hu : ∀ i ∈ s, MemLp (u i) 10 volume)
    (hU : ∀ i ∈ s, MemLp (U i) (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : ∀ i ∈ s, MemLp (V i) (ENNReal.ofReal (30/13 : ℝ)) volume) :
    ∀ᵐ x ∂volume, ∀ j : Fin 3, gradientDefect s α c u U V x j =
      FiniteCandidateExpansion.candidateDefect α c s u
        (fun i => directionalField (U i) (V i) (EuclideanSpace.basisFun (Fin 3) ℝ j)) x := by
  filter_upwards [gradientDefect_candidate_ae hH s u U V hd hu hU hV] with x hx
  intro j
  rw [hx]
  exact jointCandidateDefect_coordinate s α c u U V x j

private theorem finite_sum_ae {E : Type*} [AddCommMonoid E]
    (s : Finset ι) {f g : ι → Space → E}
    (h : ∀ i ∈ s, f i =ᵐ[volume] g i) :
    (fun x => ∑ i ∈ s, f i x) =ᵐ[volume] (fun x => ∑ i ∈ s, g i x) := by
  filter_upwards [(eventually_all_finset s).2 h] with x hx
  exact Finset.sum_congr rfl hx

private theorem finite_joint_sum {E : Type*} [NormedAddCommGroup E]
    (s : Finset ι) (f : ι → ℝ → Space → E)
    (h : ∀ i ∈ s, AEStronglyMeasurable (fun z : ℝ × Space => f i z.1 z.2)
      (volume.prod volume)) :
    AEStronglyMeasurable (fun z : ℝ × Space => ∑ i ∈ s, f i z.1 z.2)
      (volume.prod volume) := by
  revert h
  induction s using Finset.induction_on with
  | empty => intro h; simpa using (aestronglyMeasurable_const (b := (0 : E)))
  | @insert a s ha ih =>
      intro h
      simpa only [Finset.sum_insert ha] using
        (h a (Finset.mem_insert_self a s)).add
          (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Only joint measurability of the selected input fields is used here. -/
theorem jointCandidateDefect_joint_measurable (s : Finset ι) (α c : ℝ)
    (u : ι → ℝ → Space → ℂ) (U V : ι → ℝ → Space → Space)
    (hu : ∀ i ∈ s, AEStronglyMeasurable (fun z : ℝ × Space => u i z.1 z.2)
      (volume.prod volume))
    (hU : ∀ i ∈ s, AEStronglyMeasurable (fun z : ℝ × Space => U i z.1 z.2)
      (volume.prod volume))
    (hV : ∀ i ∈ s, AEStronglyMeasurable (fun z : ℝ × Space => V i z.1 z.2)
      (volume.prod volume)) :
    AEStronglyMeasurable (fun z : ℝ × Space => jointCandidateDefect s α c
      (fun i => u i z.1) (fun i => U i z.1) (fun i => V i z.1) z.2)
      (volume.prod volume) := by
  exact (candidateFullGradient_joint_measurable volume α c
    (fun t x => ∑ i ∈ s, u i t x) (fun t x => ∑ i ∈ s, U i t x)
    (fun t x => ∑ i ∈ s, V i t x) (finite_joint_sum s u hu)
    (finite_joint_sum s U hU) (finite_joint_sum s V hV)).sub
      (finite_joint_sum s (fun i t => candidateFullGradient α c (u i t) (U i t) (V i t))
        (fun i hi => candidateFullGradient_joint_measurable volume α c
          (u i) (U i) (V i) (hu i hi) (hU i hi) (hV i hi)))

/-- Totalized integral congruence is safe here: no integral linearity is used. -/
theorem directionalCandidate_congr_ae (α c : ℝ) {u v h k : Space → ℂ}
    (hu : u =ᵐ[volume] v) (hh : h =ᵐ[volume] k) :
    directionalCandidate α c u h =ᵐ[volume] directionalCandidate α c v k := by
  have hd : directionalDensity α u h =ᵐ[volume] directionalDensity α v k := by
    filter_upwards [hu, hh] with x hx hy
    simp only [directionalDensity, hx, hy]
  filter_upwards [hu, hh] with x hx hy
  simp only [directionalCandidate, rieszConvolution_congr_ae α c hd x,
    potential_congr_ae α c hu x, hx, hy]

theorem candidateFullGradient_congr_ae (α c : ℝ) {u v : Space → ℂ}
    {U V P Q : Space → Space} (hu : u =ᵐ[volume] v)
    (hU : U =ᵐ[volume] P) (hV : V =ᵐ[volume] Q) :
    candidateFullGradient α c u U V =ᵐ[volume] candidateFullGradient α c v P Q := by
  have hd (j : Fin 3) : directionalField U V (EuclideanSpace.basisFun (Fin 3) ℝ j) =ᵐ[volume]
      directionalField P Q (EuclideanSpace.basisFun (Fin 3) ℝ j) := by
    filter_upwards [hU, hV] with x hx hy
    simp only [directionalField, hx, hy]
  have hc (j : Fin 3) := directionalCandidate_congr_ae α c hu (hd j)
  filter_upwards [hc 0, hc 1, hc 2] with x h0 h1 h2
  simp only [candidateFullGradient, h0, h1, h2]

theorem jointCandidateDefect_congr_ae (s : Finset ι) (α c : ℝ)
    {u v : ι → Space → ℂ} {U V P Q : ι → Space → Space}
    (hu : ∀ i ∈ s, u i =ᵐ[volume] v i)
    (hU : ∀ i ∈ s, U i =ᵐ[volume] P i)
    (hV : ∀ i ∈ s, V i =ᵐ[volume] Q i) :
    jointCandidateDefect s α c u U V =ᵐ[volume] jointCandidateDefect s α c v P Q :=
  (candidateFullGradient_congr_ae α c (finite_sum_ae s hu)
    (finite_sum_ae s hU) (finite_sum_ae s hV)).sub
      (finite_sum_ae s (fun i hi => candidateFullGradient_congr_ae α c
        (hu i hi) (hU i hi) (hV i hi)))

/-- The actual source-order value frame. -/
def framedValue (g : ℝ → EnergyState) (a : ℝ) (y : Space) (τ : ℝ) : ℝ → Space → ℂ :=
  seedFrame a y τ (1/2) (stateValueField g)

/-- The actual source-order real and imaginary gradient frames. -/
def framedReal (g : ℝ → EnergyState) (a : ℝ) (y : Space) (τ : ℝ) : ℝ → Space → Space :=
  parabolicField a⁻¹ (-(a⁻¹ • y)) τ (3/2) (stateRealGradientField g)

def framedImag (g : ℝ → EnergyState) (a : ℝ) (y : Space) (τ : ℝ) : ℝ → Space → Space :=
  parabolicField a⁻¹ (-(a⁻¹ • y)) τ (3/2) (stateImagGradientField g)

/-- Canonical coordinates are the original EnergyState derivative coordinates,
with the same frame parameters and no change of time sequence. -/
theorem framed_directionalField (g : ℝ → EnergyState) (a : ℝ) (y : Space)
    (τ : ℝ) (j : Fin 3) (t : ℝ) :
    directionalField (framedReal g a y τ t) (framedImag g a y τ t)
      (EuclideanSpace.basisFun (Fin 3) ℝ j) =
      seedFrame a y τ (3/2) (fun t => (energyGradient j (g t) : Space → ℂ)) t := by
  rw [← gradientCoordinate_state g j]
  funext x
  apply Complex.ext <;>
    simp [directionalField, EuclideanSpace.inner_basisFun_real, framedReal,
      framedImag, seedFrame, parabolicField, gradientCoordinate, complexGradient,
      Complex.real_smul]

/-- Projection domains are produced from the packed W domain. -/
theorem packed_memLp_real_imag {p : ℝ≥0∞} {U V : Space → Space}
    (h : MemLp (complexGradient U V) p volume) : MemLp U p volume ∧ MemLp V p volume := by
  have hr : U = (fun x => ∑ j : Fin 3, (complexGradient U V x j).re • coordinate j) := by
    funext x
    simpa [complexGradient] using (coordinate_reconstruct (U x)).symm
  have hi : V = (fun x => ∑ j : Fin 3, (complexGradient U V x j).im • coordinate j) := by
    funext x
    simpa [complexGradient] using (coordinate_reconstruct (V x)).symm
  constructor
  · rw [hr]
    apply memLp_finsetSum
    intro j _
    exact (((EuclideanSpace.proj (𝕜 := ℂ) j).comp_memLp' h).continuousLinearMap_comp
      Complex.reCLM).continuousLinearMap_comp (ContinuousLinearMap.toSpanSingleton ℝ (coordinate j))
  · rw [hi]
    apply memLp_finsetSum
    intro j _
    exact (((EuclideanSpace.proj (𝕜 := ℂ) j).comp_memLp' h).continuousLinearMap_comp
      Complex.imCLM).continuousLinearMap_comp (ContinuousLinearMap.toSpanSingleton ℝ (coordinate j))

/-- Eligible actual slices are derived from the supplied profile S/W norms. -/
theorem actual_frame_slices (g : ℝ → EnergyState) {a : ℝ} (ha : 0 < a)
    (y : Space) (τ : ℝ)
    (hS : mixedNorm volume volume 10 10 (stateValueField g) ≠ ∞)
    (hW : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (stateRealGradientField g t) (stateImagGradientField g t)) ≠ ∞) :
    ∀ᵐ t ∂volume,
      InDotH1 (framedValue g a y τ t) (framedReal g a y τ t) (framedImag g a y τ t) ∧
      MemLp (framedValue g a y τ t) 10 volume ∧
      MemLp (framedReal g a y τ t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (framedImag g a y τ t) (ENNReal.ofReal (30/13 : ℝ)) volume := by
  have hs := finite_mixedNorm_ae_slice_memLp volume volume 10 10
    (by norm_num) (by norm_num) (stateValueField g) hS
  have hw := finite_mixedNorm_ae_slice_memLp volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
    (by norm_num) (by norm_num)
    (fun t => complexGradient (stateRealGradientField g t) (stateImagGradientField g t)) hW
  filter_upwards [timeAffine_ae_pullback (inv_pos.mpr ha) τ hs,
    timeAffine_ae_pullback (inv_pos.mpr ha) τ hw] with t hst hwt
  obtain ⟨hr, hi⟩ := packed_memLp_real_imag hwt
  refine ⟨actual_seedFrame_inDotH1 g ha y τ t, ?_, ?_, ?_⟩
  · exact (affine_memLp (inv_ne_zero ha.ne') (-(a⁻¹ • y)) (by norm_num) (by norm_num) hst).const_smul _
  · exact (affine_memLp (inv_ne_zero ha.ne') (-(a⁻¹ • y)) (by norm_num) (by norm_num) hr).const_smul _
  · exact (affine_memLp (inv_ne_zero ha.ne') (-(a⁻¹ • y)) (by norm_num) (by norm_num) hi).const_smul _

/-- Finite families share one conull time set; at each such time the coordinate
candidate identities share one conull spatial set. No target defect domain is assumed. -/
theorem actual_finite_framed_weak_gradients (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {α c : ℝ} (hH : OrdinaryHLS α c)
    (s : Finset ι) (g : ι → ℝ → EnergyState) (a τ : ι → ℝ) (y : ι → Space)
    (ha : ∀ i ∈ s, 0 < a i)
    (hS : ∀ i ∈ s, mixedNorm volume volume 10 10 (stateValueField (g i)) ≠ ∞)
    (hW : ∀ i ∈ s, mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (stateRealGradientField (g i) t) (stateImagGradientField (g i) t)) ≠ ∞) :
    let u := fun i => framedValue (g i) (a i) (y i) (τ i)
    let U := fun i => framedReal (g i) (a i) (y i) (τ i)
    let V := fun i => framedImag (g i) (a i) (y i) (τ i)
    ∀ᵐ t ∂volume,
      HasWeakGradient (fun x => (literalDefect s α c (fun i => u i t) x).re)
        (fun x => gradientReal (gradientDefect s α c (fun i => u i t)
          (fun i => U i t) (fun i => V i t) x)) ∧
      HasWeakGradient (fun x => (literalDefect s α c (fun i => u i t) x).im)
        (fun x => gradientImag (gradientDefect s α c (fun i => u i t)
          (fun i => U i t) (fun i => V i t) x)) ∧
      CoordinateTests (literalDefect s α c (fun i => u i t))
        (gradientDefect s α c (fun i => u i t) (fun i => U i t) (fun i => V i t)) ∧
      (∀ᵐ x ∂volume, ∀ j : Fin 3,
        gradientDefect s α c (fun i => u i t) (fun i => U i t) (fun i => V i t) x j =
          FiniteCandidateExpansion.candidateDefect α c s (fun i => u i t)
            (fun i => directionalField (U i t) (V i t) (EuclideanSpace.basisFun (Fin 3) ℝ j)) x) := by
  dsimp only
  have hh := (eventually_all_finset s).2 (fun i hi =>
    actual_frame_slices (g i) (ha i hi) (y i) (τ i) (hS i hi) (hW i hi))
  filter_upwards [hh] with t ht
  have hd := fun i hi => (ht i hi).1
  have hu := fun i hi => (ht i hi).2.1
  have hU := fun i hi => (ht i hi).2.2.1
  have hV := fun i hi => (ht i hi).2.2.2
  obtain ⟨hR, hI⟩ := finite_forcing_hasWeakGradients hDensity hSob hH s _ _ _ hd hu hU hV
  exact ⟨hR, hI, weakGradients_coordinate_tests hR hI,
    gradientDefect_coordinates_ae hH s _ _ _ hd hu hU hV⟩

/-- Shared EnergyJointFields choices are accepted as data, not reselected per coordinate. -/
def framedJointValue {g : ℝ → EnergyState} (r : EnergyJointFields volume g)
    (a : ℝ) (y : Space) (τ : ℝ) : ℝ → Space → ℂ := seedFrame a y τ (1/2) r.u

def framedJointReal {g : ℝ → EnergyState} (r : EnergyJointFields volume g)
    (a : ℝ) (y : Space) (τ : ℝ) : ℝ → Space → Space :=
  parabolicField a⁻¹ (-(a⁻¹ • y)) τ (3/2) r.U

def framedJointImag {g : ℝ → EnergyState} (r : EnergyJointFields volume g)
    (a : ℝ) (y : Space) (τ : ℝ) : ℝ → Space → Space :=
  parabolicField a⁻¹ (-(a⁻¹ • y)) τ (3/2) r.V

private theorem realFrame_joint_measurable (a : ℝ) (y : Space) (τ : ℝ)
    (U : ℝ → Space → Space) (hU : StronglyMeasurable (fun z : ℝ × Space => U z.1 z.2)) :
    StronglyMeasurable (fun z : ℝ × Space =>
      parabolicField a⁻¹ (-(a⁻¹ • y)) τ (3/2) U z.1 z.2) := by
  have hc : Continuous (fun z : ℝ × Space =>
      (timeAffine a⁻¹ τ z.1, affine a⁻¹ (-(a⁻¹ • y)) z.2)) := by
    unfold timeAffine affine
    fun_prop
  exact (hU.comp_measurable hc.measurable).const_smul _

theorem framedJoint_joint_measurable {g : ℝ → EnergyState} (r : EnergyJointFields volume g)
    (a : ℝ) (y : Space) (τ : ℝ) :
    StronglyMeasurable (fun z : ℝ × Space => framedJointValue r a y τ z.1 z.2) ∧
    StronglyMeasurable (fun z : ℝ × Space => framedJointReal r a y τ z.1 z.2) ∧
    StronglyMeasurable (fun z : ℝ × Space => framedJointImag r a y τ z.1 z.2) :=
  ⟨seedFrame_joint_stronglyMeasurable a y τ (1/2) r.u r.joint_u,
    realFrame_joint_measurable a y τ r.U r.joint_U,
    realFrame_joint_measurable a y τ r.V r.joint_V⟩

/-- The scalar derivative used by the finite estimates is this same real/imaginary
weak gradient, with the exact source-order frame and weight 3/2. -/
theorem framedJoint_directionalField {g : ℝ → EnergyState} (r : EnergyJointFields volume g)
    (a : ℝ) (y : Space) (τ : ℝ) (j : Fin 3) (t : ℝ) :
    directionalField (framedJointReal r a y τ t) (framedJointImag r a y τ t)
      (EuclideanSpace.basisFun (Fin 3) ℝ j) =
      seedFrame a y τ (3/2)
        (gradientCoordinate j (fun t => complexGradient (r.U t) (r.V t))) t := by
  funext x
  apply Complex.ext <;>
    simp [directionalField, EuclideanSpace.inner_basisFun_real, framedJointReal,
      framedJointImag, seedFrame, parabolicField, gradientCoordinate, complexGradient,
      Complex.real_smul]

private theorem realFrame_congr_nested_ae {a : ℝ} (ha : 0 < a) (y : Space) (τ : ℝ)
    {U P : ℝ → Space → Space} (h : ∀ᵐ t ∂volume, U t =ᵐ[volume] P t) :
    ∀ᵐ t ∂volume,
      parabolicField a⁻¹ (-(a⁻¹ • y)) τ (3/2) U t =ᵐ[volume]
        parabolicField a⁻¹ (-(a⁻¹ • y)) τ (3/2) P t := by
  filter_upwards [timeAffine_ae_pullback (inv_pos.mpr ha) τ h] with t ht
  filter_upwards [affine_ae_pullback (inv_pos.mpr ha) (-(a⁻¹ • y)) ht] with x hx
  simp only [parabolicField, hx]

theorem framedJoint_nested_ae (g : ℝ → EnergyState) (r : EnergyJointFields volume g)
    {a : ℝ} (ha : 0 < a) (y : Space) (τ : ℝ) :
    ∀ᵐ t ∂volume,
      framedValue g a y τ t =ᵐ[volume] framedJointValue r a y τ t ∧
      framedReal g a y τ t =ᵐ[volume] framedJointReal r a y τ t ∧
      framedImag g a y τ t =ᵐ[volume] framedJointImag r a y τ t := by
  have hU : ∀ᵐ t ∂volume, stateRealGradientField g t =ᵐ[volume] r.U t :=
    r.slice_eq.mono (fun _ ht => ht.2.1.symm)
  have hV : ∀ᵐ t ∂volume, stateImagGradientField g t =ᵐ[volume] r.V t :=
    r.slice_eq.mono (fun _ ht => ht.2.2.symm)
  filter_upwards [seedFrame_jointFields_value_nested_ae g r ha y τ,
    realFrame_congr_nested_ae ha y τ hU, realFrame_congr_nested_ae ha y τ hV]
    with t ht hUt hVt
  exact ⟨ht, hUt, hVt⟩

/-- Transfer to one shared genuinely joint representative for the whole finite
family. No canonical quotient joint measurability is a hypothesis or conclusion. -/
theorem actual_finite_framed_candidate_transfer {α c : ℝ} (hH : OrdinaryHLS α c)
    (s : Finset ι) (g : ι → ℝ → EnergyState) (r : ∀ i, EnergyJointFields volume (g i))
    (a τ : ι → ℝ) (y : ι → Space) (ha : ∀ i ∈ s, 0 < a i)
    (hS : ∀ i ∈ s, mixedNorm volume volume 10 10 (stateValueField (g i)) ≠ ∞)
    (hW : ∀ i ∈ s, mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (stateRealGradientField (g i) t) (stateImagGradientField (g i) t)) ≠ ∞) :
    let u := fun i => framedValue (g i) (a i) (y i) (τ i)
    let U := fun i => framedReal (g i) (a i) (y i) (τ i)
    let V := fun i => framedImag (g i) (a i) (y i) (τ i)
    let v := fun i => framedJointValue (r i) (a i) (y i) (τ i)
    let P := fun i => framedJointReal (r i) (a i) (y i) (τ i)
    let Q := fun i => framedJointImag (r i) (a i) (y i) (τ i)
    AEStronglyMeasurable (fun z : ℝ × Space => jointCandidateDefect s α c
      (fun i => v i z.1) (fun i => P i z.1) (fun i => Q i z.1) z.2) (volume.prod volume) ∧
    (∀ᵐ t ∂volume, gradientDefect s α c (fun i => u i t) (fun i => U i t) (fun i => V i t)
      =ᵐ[volume] jointCandidateDefect s α c (fun i => v i t) (fun i => P i t) (fun i => Q i t)) := by
  dsimp only
  constructor
  · apply jointCandidateDefect_joint_measurable
    · intro i hi
      exact (framedJoint_joint_measurable (r i) (a i) (y i) (τ i)).1.aestronglyMeasurable
    · intro i hi
      exact (framedJoint_joint_measurable (r i) (a i) (y i) (τ i)).2.1.aestronglyMeasurable
    · intro i hi
      exact (framedJoint_joint_measurable (r i) (a i) (y i) (τ i)).2.2.aestronglyMeasurable
  · have hh := (eventually_all_finset s).2 (fun i hi =>
        actual_frame_slices (g i) (ha i hi) (y i) (τ i) (hS i hi) (hW i hi))
    have he := (eventually_all_finset s).2 (fun i hi =>
        framedJoint_nested_ae (g i) (r i) (ha i hi) (y i) (τ i))
    filter_upwards [hh, he] with t ht heq
    exact (gradientDefect_candidate_ae hH s _ _ _
      (fun i hi => (ht i hi).1) (fun i hi => (ht i hi).2.1)
      (fun i hi => (ht i hi).2.2.1) (fun i hi => (ht i hi).2.2.2)).trans
        (jointCandidateDefect_congr_ae s α c
          (fun i hi => (heq i hi).1) (fun i hi => (heq i hi).2.1) (fun i hi => (heq i hi).2.2))

/-- A chosen spatial AE representative retains the SAME literal finite forcing
error, and produces its coordinate tests with their actual integrability. -/
theorem finite_forcing_representative_weak_tests (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {α c : ℝ} (hH : OrdinaryHLS α c)
    (s : Finset ι) (u : ι → Space → ℂ) (U V : ι → Space → Space)
    (hd : ∀ i ∈ s, InDotH1 (u i) (U i) (V i))
    (hu : ∀ i ∈ s, MemLp (u i) 10 volume)
    (hU : ∀ i ∈ s, MemLp (U i) (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : ∀ i ∈ s, MemLp (V i) (ENNReal.ofReal (30/13 : ℝ)) volume)
    (G : Space → EuclideanSpace ℂ (Fin 3))
    (hG : gradientDefect s α c u U V =ᵐ[volume] G) :
    HasWeakGradient (fun x => (literalDefect s α c u x).re) (fun x => gradientReal (G x)) ∧
    HasWeakGradient (fun x => (literalDefect s α c u x).im) (fun x => gradientImag (G x)) ∧
    CoordinateTests (literalDefect s α c u) G := by
  obtain ⟨hr, hi⟩ := finite_forcing_hasWeakGradients hDensity hSob hH s u U V hd hu hU hV
  have hR := weakGradient_congr_gradient hr (hG.mono fun _ hx => congrArg gradientReal hx)
  have hI := weakGradient_congr_gradient hi (hG.mono fun _ hx => congrArg gradientImag hx)
  exact ⟨hR, hI, weakGradients_coordinate_tests hR hI⟩

/-- Empty sums give the zero literal forcing error even at totalized exponents. -/
@[simp] theorem literalDefect_empty (α c : ℝ) (u : ι → Space → ℂ) :
    literalDefect ∅ α c u = 0 := by
  funext x
  simp [literalDefect, forcing, ForcingDomain.localFactor]

/-- Singleton families vanish by literal cancellation, with no analytic premise. -/
@[simp] theorem literalDefect_singleton (i : ι) (α c : ℝ) (u : ι → Space → ℂ) :
    literalDefect {i} α c u = 0 := by
  funext x
  simp [literalDefect]

@[simp] theorem gradientDefect_singleton (i : ι) (α c : ℝ) (u : ι → Space → ℂ)
    (U V : ι → Space → Space) : gradientDefect {i} α c u U V = 0 := by
  funext x
  simp [gradientDefect]

/-- The empty family is an actual finite Sobolev/forcing case, not a nonempty-only convention. -/
theorem empty_forcing_hasWeakGradients (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {α c : ℝ} (hH : OrdinaryHLS α c)
    (u : Fin 0 → Space → ℂ) (U V : Fin 0 → Space → Space) :
    HasWeakGradient (fun x => (literalDefect Finset.univ α c u x).re)
      (fun x => gradientReal (gradientDefect Finset.univ α c u U V x)) ∧
    HasWeakGradient (fun x => (literalDefect Finset.univ α c u x).im)
      (fun x => gradientImag (gradientDefect Finset.univ α c u U V x)) := by
  apply finite_forcing_hasWeakGradients hDensity hSob hH
  all_goals intro i hi; exact Fin.elim0 i

/-- The one-label enumeration is explicitly supported and cancels exactly. -/
theorem fin_one_defects_zero (α c : ℝ) (u : Fin 1 → Space → ℂ)
    (U V : Fin 1 → Space → Space) :
    literalDefect Finset.univ α c u = 0 ∧ gradientDefect Finset.univ α c u U V = 0 := by
  have hs : (Finset.univ : Finset (Fin 1)) = {0} := by
    ext i
    simp [Fin.eq_zero i]
  rw [hs]
  exact ⟨literalDefect_singleton 0 α c u, gradientDefect_singleton 0 α c u U V⟩

#print axioms inDotH1_sum
#print axioms finite_forcing_hasWeakGradients
#print axioms finite_forcing_coordinate_tests
#print axioms gradientDefect_coordinates_ae
#print axioms actual_finite_framed_weak_gradients
#print axioms actual_finite_framed_candidate_transfer
#print axioms finite_forcing_representative_weak_tests
end HartreeF.FiniteProfileWeakGradient
