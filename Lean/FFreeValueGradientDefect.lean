import FFreeValueCandidateSplice
import FFiniteProfileWeakGradient
import FGeneralVectorReassembly

/-! Genuine weak gradients for the literal free-value forcing difference.
Author source, UNCOMPILED. The only true states are A+z and A. Source domains
are produced from the original scalar-profile inputs and their true InDotH1
relations. EuclideanSpace, not a Pi supremum norm, is used throughout. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace HartreeF.FreeValueGradient
open TimeHolder ProfileApproximation GeneralProfileCross FreeValueSplice
open ForcingDomain WeakHartreeChain DerivativeMajorization CompactCross CrossContinuity
open SobolevStretch StationarySelfTest WeakHartreeProduct EnergySpace FiniteProfileWeakGradient

/-- The literal complex directional coordinate of the supplied real and
imaginary weak gradients. No independent direction representative is chosen. -/
def directionCoordinate (U V : ℝ → Space → Space) (j : Fin 3) : ℝ → Space → ℂ :=
  fun t => directionalField (U t) (V t) (EuclideanSpace.basisFun (Fin 3) ℝ j)

theorem directionCoordinate_add (U V P Q : ℝ → Space → Space) (j : Fin 3) :
    directionCoordinate (U+P) (V+Q) j = directionCoordinate U V j + directionCoordinate P Q j := by
  funext t x
  apply Complex.ext <;> simp [directionCoordinate, directionalField, inner_add_left]

/-- Projection domains are recovered from all three genuine scalar coordinate
memberships, without assuming the desired vector or source domain. -/
theorem projected_memLp_of_coordinates {p : ℝ≥0∞} (U V : Space → Space)
    (hd : ∀ j : Fin 3,
      MemLp (directionalField U V (EuclideanSpace.basisFun (Fin 3) ℝ j)) p volume) :
    MemLp U p volume ∧ MemLp V p volume := by
  have hR : U = (fun x => ∑ j : Fin 3,
      (directionalField U V (EuclideanSpace.basisFun (Fin 3) ℝ j) x).re • coordinate j) := by
    funext x
    change U x = ∑ j : Fin 3, (inner ℝ (U x) (EuclideanSpace.basisFun (Fin 3) ℝ j)) • coordinate j
    simpa only [EuclideanSpace.inner_basisFun_real] using
      (coordinate_reconstruct (U x)).symm
  have hI : V = (fun x => ∑ j : Fin 3,
      (directionalField U V (EuclideanSpace.basisFun (Fin 3) ℝ j) x).im • coordinate j) := by
    funext x
    change V x = ∑ j : Fin 3, (inner ℝ (V x) (EuclideanSpace.basisFun (Fin 3) ℝ j)) • coordinate j
    simpa only [EuclideanSpace.inner_basisFun_real] using
      (coordinate_reconstruct (V x)).symm
  constructor
  · rw [hR]
    apply memLp_finsetSum
    intro j _
    exact ((hd j).continuousLinearMap_comp Complex.reCLM).continuousLinearMap_comp
      (ContinuousLinearMap.toSpanSingleton ℝ (coordinate j))
  · rw [hI]
    apply memLp_finsetSum
    intro j _
    exact ((hd j).continuousLinearMap_comp Complex.imCLM).continuousLinearMap_comp
      (ContinuousLinearMap.toSpanSingleton ℝ (coordinate j))

/-- Genuine homogeneous Sobolev addition. The weak-add body is the selected
finite9 implementation, rather than a new Hartree subtraction wrapper. -/
theorem inDotH1_add {A z : Space → ℂ} {U V P Q : Space → Space}
    (hA : InDotH1 A U V) (hz : InDotH1 z P Q) :
    InDotH1 (A+z) (U+P) (V+Q) := by
  refine ⟨hA.function_L6.add hz.function_L6,
    hA.real_gradient_L2.add hz.real_gradient_L2,
    hA.imag_gradient_L2.add hz.imag_gradient_L2, ?_, ?_⟩
  · change HasWeakGradient (fun x => (A x + z x).re) (fun x => U x + P x)
    simpa only [Complex.add_re] using
      FiniteProfileWeakGradient.weakGradient_add hA.real_weak hz.real_weak
  · change HasWeakGradient (fun x => (A x + z x).im) (fun x => V x + Q x)
    simpa only [Complex.add_im] using
      FiniteProfileWeakGradient.weakGradient_add hA.imag_weak hz.imag_weak

/-- Exactly the two source states consumed by the pre-existing actual weak
Hartree derivative producer. In particular (A,U+P,V+Q) is not in this tuple. -/
def TruePairSlices (A z : ℝ → Space → ℂ) (U V P Q : ℝ → Space → Space) : Prop :=
  ∀ᵐ t ∂volume,
    InDotH1 ((A+z) t) ((U+P) t) ((V+Q) t) ∧ InDotH1 (A t) (U t) (V t) ∧
    MemLp ((A+z) t) 10 volume ∧ MemLp (A t) 10 volume ∧
    MemLp ((U+P) t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
    MemLp ((V+Q) t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
    MemLp (U t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
    MemLp (V t) (ENNReal.ofReal (30/13 : ℝ)) volume

/-- All L10 and projected L30/13 source domains are produced before applying
any weak-gradient identity. A finite intersection handles all coordinates. -/
theorem true_pair_slices (A z : ℝ → Space → ℂ) (U V P Q : ℝ → Space → Space)
    (hA : ∀ j, ScalarProfile A (directionCoordinate U V j))
    (hz : ∀ j, ScalarProfile z (directionCoordinate P Q j))
    (hDotA : ∀ᵐ t ∂volume, InDotH1 (A t) (U t) (V t))
    (hDotz : ∀ᵐ t ∂volume, InDotH1 (z t) (P t) (Q t)) : TruePairSlices A z U V P Q := by
  have hAS := finite_mixedNorm_ae_slice_memLp volume volume 10 10
    (by norm_num) (by norm_num) A (hA 0).value_S
  have hzS := finite_mixedNorm_ae_slice_memLp volume volume 10 10
    (by norm_num) (by norm_num) z (hz 0).value_S
  have hAW : ∀ᵐ t ∂volume, ∀ j : Fin 3,
      MemLp (directionCoordinate U V j t) (ENNReal.ofReal (30/13 : ℝ)) volume :=
    eventually_all.mpr (fun j => finite_mixedNorm_ae_slice_memLp volume volume 10
      (ENNReal.ofReal (30/13 : ℝ)) (by norm_num) (by norm_num) _ (hA j).gradient_W)
  have hzW : ∀ᵐ t ∂volume, ∀ j : Fin 3,
      MemLp (directionCoordinate P Q j t) (ENNReal.ofReal (30/13 : ℝ)) volume :=
    eventually_all.mpr (fun j => finite_mixedNorm_ae_slice_memLp volume volume 10
      (ENNReal.ofReal (30/13 : ℝ)) (by norm_num) (by norm_num) _ (hz j).gradient_W)
  filter_upwards [hDotA, hDotz, hAS, hzS, hAW, hzW] with t htA htz htAS htzS htAW htzW
  obtain ⟨hU, hV⟩ := projected_memLp_of_coordinates (U t) (V t) htAW
  obtain ⟨hP, hQ⟩ := projected_memLp_of_coordinates (P t) (Q t) htzW
  exact ⟨inDotH1_add htA htz, htA, htAS.add htzS, htAS,
    hU.add hP, hV.add hQ, hU, hV⟩

/-- The scalar whose distributional derivative is proved in this file. -/
def literalForcing (α c : ℝ) (A z : ℝ → Space → ℂ) : ℝ → Space → ℂ :=
  fun t x => forcing α c ((A+z) t) x - forcing α c (A t) x

/-- Literal difference of the two existing actual full gradients. -/
def actualGradient (α c : ℝ) (A z : ℝ → Space → ℂ)
    (U V P Q : ℝ → Space → Space) : ℝ → Space → EuclideanSpace ℂ (Fin 3) :=
  fun t x => actualFullGradient α c ((A+z) t) ((U+P) t) ((V+Q) t) x -
    actualFullGradient α c (A t) (U t) (V t) x

/-- A jointly measurable representative packed into actual complex Euclidean
space. Its coordinate is the literal same-direction splice candidate. -/
def candidateGradient (α c : ℝ) (A z : ℝ → Space → ℂ)
    (U V P Q : ℝ → Space → Space) : ℝ → Space → EuclideanSpace ℂ (Fin 3) :=
  fun t x => packGradient
    (scalarDefect α c A z (directionCoordinate U V 0) (directionCoordinate P Q 0) t x)
    (scalarDefect α c A z (directionCoordinate U V 1) (directionCoordinate P Q 1) t x)
    (scalarDefect α c A z (directionCoordinate U V 2) (directionCoordinate P Q 2) t x)

@[simp] theorem candidateGradient_coordinate (α c : ℝ) (A z : ℝ → Space → ℂ)
    (U V P Q : ℝ → Space → Space) (t : ℝ) (x : Space) (j : Fin 3) :
    candidateGradient α c A z U V P Q t x j =
      scalarDefect α c A z (directionCoordinate U V j) (directionCoordinate P Q j) t x := by
  fin_cases j <;> simp [candidateGradient, packGradient_coordinate]

theorem candidateGradient_eq_candidates (α c : ℝ) (A z : ℝ → Space → ℂ)
    (U V P Q : ℝ → Space → Space) (t : ℝ) (x : Space) :
    candidateGradient α c A z U V P Q t x =
      candidateFullGradient α c ((A+z) t) ((U+P) t) ((V+Q) t) x -
        candidateFullGradient α c (A t) (U t) (V t) x := by
  ext j
  rw [candidateGradient_coordinate]
  change scalarDefect α c A z (directionCoordinate U V j) (directionCoordinate P Q j) t x =
    candidateFullGradient α c ((A+z) t) ((U+P) t) ((V+Q) t) x j -
      candidateFullGradient α c (A t) (U t) (V t) x j
  rw [candidateFullGradient_coordinate, candidateFullGradient_coordinate]
  change scalarDefect α c A z (directionCoordinate U V j) (directionCoordinate P Q j) t x =
    C α c (A+z) (directionCoordinate (U+P) (V+Q) j) t x - C α c A (directionCoordinate U V j) t x
  rw [directionCoordinate_add]
  rfl

theorem candidateGradient_joint (α c : ℝ) (A z : ℝ → Space → ℂ)
    (U V P Q : ℝ → Space → Space)
    (hA : ∀ j, ScalarProfile A (directionCoordinate U V j))
    (hz : ∀ j, ScalarProfile z (directionCoordinate P Q j)) :
    AEStronglyMeasurable (fun p : ℝ × Space => candidateGradient α c A z U V P Q p.1 p.2)
      (volume.prod volume) := by
  have hm (j : Fin 3) : AEStronglyMeasurable
      (fun p : ℝ × Space => scalarDefect α c A z (directionCoordinate U V j)
        (directionCoordinate P Q j) p.1 p.2) (volume.prod volume) := by
    have hs := scalarProfile_add (hA j) (hz j)
    exact (joint_directional_candidate_measurable volume α c (A+z)
      (directionCoordinate U V j + directionCoordinate P Q j)
      hs.value_joint.aestronglyMeasurable hs.gradient_joint.aestronglyMeasurable).sub
        (joint_directional_candidate_measurable volume α c A (directionCoordinate U V j)
          (hA j).value_joint.aestronglyMeasurable (hA j).gradient_joint.aestronglyMeasurable)
  exact (((hm 0).smul_const (EuclideanSpace.basisFun (Fin 3) ℂ 0)).add
    ((hm 1).smul_const (EuclideanSpace.basisFun (Fin 3) ℂ 1))).add
    ((hm 2).smul_const (EuclideanSpace.basisFun (Fin 3) ℂ 2))

/-- Only nested AE transport is asserted for canonical/actual gradients.
Joint measurability belongs to the explicitly packed candidate. -/
theorem actualGradient_candidate_ae {α c : ℝ} (hH : OrdinaryHLS α c)
    (A z : ℝ → Space → ℂ) (U V P Q : ℝ → Space → Space)
    (hs : TruePairSlices A z U V P Q) :
    ∀ᵐ t ∂volume, actualGradient α c A z U V P Q t =ᵐ[volume]
      candidateGradient α c A z U V P Q t := by
  filter_upwards [hs] with t ht
  rcases ht with ⟨hdSum, hdA, hSum10, hA10, hUP, hVQ, hU, hV⟩
  have hsum := actualFullGradient_candidate_ae hH _ _ _ hdSum hSum10 hUP hVQ
  have hbase := actualFullGradient_candidate_ae hH _ _ _ hdA hA10 hU hV
  filter_upwards [hsum, hbase] with x hxSum hxA
  rw [candidateGradient_eq_candidates]
  exact congrArg₂ (· - ·) hxSum hxA

/-- No cap or smallness hypothesis occurs in the every-index domain packet. -/
structure ActualDefectDomains (α c : ℝ) (A z : ℝ → Space → ℂ)
    (U V P Q : ℝ → Space → Space) : Prop where
  source_slices : TruePairSlices A z U V P Q
  candidate_joint : AEStronglyMeasurable
    (fun p : ℝ × Space => candidateGradient α c A z U V P Q p.1 p.2) (volume.prod volume)
  actual_ae_candidate : ∀ᵐ t ∂volume, actualGradient α c A z U V P Q t =ᵐ[volume]
    candidateGradient α c A z U V P Q t
  candidate_finite : vectorForcingNorm (candidateGradient α c A z U V P Q) ≠ ∞
  actual_finite : vectorForcingNorm (actualGradient α c A z U V P Q) ≠ ∞
  candidate_slice : ∀ᵐ t ∂volume,
    MemLp (candidateGradient α c A z U V P Q t) (ENNReal.ofReal (6/5 : ℝ)) volume
  actual_slice : ∀ᵐ t ∂volume,
    MemLp (actualGradient α c A z U V P Q t) (ENNReal.ofReal (6/5 : ℝ)) volume
  actual_time : MemLp (fun t => eLpNorm (actualGradient α c A z U V P Q t)
    (ENNReal.ofReal (6/5 : ℝ)) volume) 2 volume
  candidate_real_time : MemLp (fun t => (eLpNorm (candidateGradient α c A z U V P Q t)
    (ENNReal.ofReal (6/5 : ℝ)) volume).toReal) 2 volume
  actual_real_time : MemLp (fun t => (eLpNorm (actualGradient α c A z U V P Q t)
    (ENNReal.ofReal (6/5 : ℝ)) volume).toReal) 2 volume
  candidate_weak : ∀ᵐ t ∂volume,
    HasWeakGradient (fun x => (literalForcing α c A z t x).re)
      (fun x => gradientReal (candidateGradient α c A z U V P Q t x)) ∧
    HasWeakGradient (fun x => (literalForcing α c A z t x).im)
      (fun x => gradientImag (candidateGradient α c A z U V P Q t x))
  actual_weak : ∀ᵐ t ∂volume,
    HasWeakGradient (fun x => (literalForcing α c A z t x).re)
      (fun x => gradientReal (actualGradient α c A z U V P Q t x)) ∧
    HasWeakGradient (fun x => (literalForcing α c A z t x).im)
      (fun x => gradientImag (actualGradient α c A z U V P Q t x))
  candidate_tests : ∀ᵐ t ∂volume,
    CoordinateTests (literalForcing α c A z t) (candidateGradient α c A z U V P Q t)
  actual_tests : ∀ᵐ t ∂volume,
    CoordinateTests (literalForcing α c A z t) (actualGradient α c A z U V P Q t)

/-- The existing two-state Hartree theorem is used directly after producing
all source domains; no weak-gradient/subtraction wrapper is re-proved. -/
theorem actual_free_value_gradient_domains (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {α c : ℝ} (hH : OrdinaryHLS α c)
    (A z : ℝ → Space → ℂ) (U V P Q : ℝ → Space → Space)
    (hA : ∀ j, ScalarProfile A (directionCoordinate U V j))
    (hz : ∀ j, ScalarProfile z (directionCoordinate P Q j))
    (hDotA : ∀ᵐ t ∂volume, InDotH1 (A t) (U t) (V t))
    (hDotz : ∀ᵐ t ∂volume, InDotH1 (z t) (P t) (Q t)) :
    ActualDefectDomains α c A z U V P Q := by
  have hs := true_pair_slices A z U V P Q hA hz hDotA hDotz
  have hm := candidateGradient_joint α c A z U V P Q hA hz
  have heq := actualGradient_candidate_ae hH A z U V P Q hs
  have hf (j : Fin 3) : forcingNorm
      (fun t x => candidateGradient α c A z U V P Q t x j) ≠ ∞ := by
    simpa only [candidateGradient_coordinate] using (scalar_defect_finite hH (hA j) (hz j)).2
  have hcf : vectorForcingNorm (candidateGradient α c A z U V P Q) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr (fun j _ => hf j))
      (vectorForcingNorm_le_sum_of_joint _ hm)
  have hnorm : vectorForcingNorm (actualGradient α c A z U V P Q) =
      vectorForcingNorm (candidateGradient α c A z U V P Q) :=
    mixedNorm_congr_nested_ae volume volume 2 (ENNReal.ofReal (6/5 : ℝ)) heq
  have haf : vectorForcingNorm (actualGradient α c A z U V P Q) ≠ ∞ := by rw [hnorm]; exact hcf
  have hcw : ∀ᵐ t ∂volume,
      HasWeakGradient (fun x => (literalForcing α c A z t x).re)
        (fun x => gradientReal (candidateGradient α c A z U V P Q t x)) ∧
      HasWeakGradient (fun x => (literalForcing α c A z t x).im)
        (fun x => gradientImag (candidateGradient α c A z U V P Q t x)) := by
    filter_upwards [hs, heq] with t ht heqt
    rcases ht with ⟨hdSum, hdA, hSum10, hA10, hUP, hVQ, hU, hV⟩
    exact TimeHolder.actual_gradient_representative_hasWeakGradients hDensity hSob hH
      hdSum hdA hSum10 hA10 hUP hVQ hU hV
      (candidateGradient α c A z U V P Q t) heqt.symm
  have haw : ∀ᵐ t ∂volume,
      HasWeakGradient (fun x => (literalForcing α c A z t x).re)
        (fun x => gradientReal (actualGradient α c A z U V P Q t x)) ∧
      HasWeakGradient (fun x => (literalForcing α c A z t x).im)
        (fun x => gradientImag (actualGradient α c A z U V P Q t x)) := by
    filter_upwards [hs] with t ht
    rcases ht with ⟨hdSum, hdA, hSum10, hA10, hUP, hVQ, hU, hV⟩
    exact TimeHolder.actual_gradient_representative_hasWeakGradients hDensity hSob hH
      hdSum hdA hSum10 hA10 hUP hVQ hU hV
      (actualGradient α c A z U V P Q t) (Filter.EventuallyEq.rfl)
  have hcd := FreeValueFullCandidate.mixedDomain_of_finite (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : ENNReal.ofReal (6/5 : ℝ) ≠ 0) ENNReal.ofReal_ne_top
    (candidateGradient α c A z U V P Q) hm hcf
  have hart : MemLp (fun t => (eLpNorm (actualGradient α c A z U V P Q t)
      (ENNReal.ofReal (6/5 : ℝ)) volume).toReal) 2 volume :=
    (memLp_congr_ae (heq.mono fun _ ht =>
      congrArg ENNReal.toReal (eLpNorm_congr_ae ht).symm)).mp hcd.time
  refine ⟨hs, hm, heq, hcf, haf, ?_, ?_, ?_, hcd.time, hart, hcw, haw, ?_, ?_⟩
  · exact finite_mixedNorm_ae_slice_memLp volume volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (by norm_num) (by norm_num) _ hcf
  · exact finite_mixedNorm_ae_slice_memLp volume volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (by norm_num) (by norm_num) _ haf
  · exact lt_top_iff_ne_top.mpr haf
  · exact hcw.mono fun _ ht => TimeHolder.weakGradients_coordinate_tests ht.1 ht.2
  · exact haw.mono fun _ ht => TimeHolder.weakGradients_coordinate_tests ht.1 ht.2

/-- Quantitative output uses the paper's Euclidean N, with all three literal
coordinates and the same full-C free-direction summand. -/
structure ActualDefectControl (α c : ℝ) (A z : ℝ → Space → ℂ)
    (U V P Q : ℝ → Space → Space) (Ccont KQ M d : ℝ≥0) : Prop where
  domains : ActualDefectDomains α c A z U V P Q
  coordinate_controls : ∀ j : Fin 3,
    SpliceControl α c A z (directionCoordinate U V j) (directionCoordinate P Q j) Ccont KQ M d
  coordinate_bound : ∀ j : Fin 3,
    forcingNorm (fun t x => actualGradient α c A z U V P Q t x j) ≤
      coordinateBound α Ccont KQ M d A (directionCoordinate P Q j)
  candidate_bound : vectorForcingNorm (candidateGradient α c A z U V P Q) ≤
    ∑ j : Fin 3, coordinateBound α Ccont KQ M d A (directionCoordinate P Q j)
  bound : vectorForcingNorm (actualGradient α c A z U V P Q) ≤
    ∑ j : Fin 3, coordinateBound α Ccont KQ M d A (directionCoordinate P Q j)

/-- Fixed constants precede all fields and finite caps. Every input concerns
actual fields and their source domains, never the target forcing defect. -/
theorem actual_free_value_gradient_bound (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {α c : ℝ} (hH : OrdinaryHLS α c) :
    ∃ Ccont KQ : ℝ≥0, ∀ (A z : ℝ → Space → ℂ) (U V P Q : ℝ → Space → Space),
      (∀ j, ScalarProfile A (directionCoordinate U V j)) →
      (∀ j, ScalarProfile z (directionCoordinate P Q j)) →
      (∀ᵐ t ∂volume, InDotH1 (A t) (U t) (V t)) →
      (∀ᵐ t ∂volume, InDotH1 (z t) (P t) (Q t)) → ∀ (M d : ℝ≥0),
      4*E A + 2*E z ≤ M → 4*S A + 2*S z ≤ M →
      (∀ j : Fin 3, 2*W (directionCoordinate U V j + directionCoordinate P Q j) ≤ M) →
      2*S z ≤ d → ActualDefectControl α c A z U V P Q Ccont KQ M d := by
  obtain ⟨Ccont, KQ, hC⟩ := same_direction_free_value_bound hH
  refine ⟨Ccont, KQ, ?_⟩
  intro A z U V P Q hA hz hDotA hDotz M d hE hS hW hd
  have hdom := actual_free_value_gradient_domains hDensity hSob hH A z U V P Q hA hz hDotA hDotz
  have hcoords (j : Fin 3) := hC A z (directionCoordinate U V j) (directionCoordinate P Q j)
    (hA j) (hz j) M d hE hS (hW j) hd
  have hcb : vectorForcingNorm (candidateGradient α c A z U V P Q) ≤
      ∑ j : Fin 3, coordinateBound α Ccont KQ M d A (directionCoordinate P Q j) := by
    apply (vectorForcingNorm_le_sum_of_joint _ hdom.candidate_joint).trans
    apply Finset.sum_le_sum
    intro j _
    simpa only [candidateGradient_coordinate] using (hcoords j).bound
  have hnorm : vectorForcingNorm (actualGradient α c A z U V P Q) =
      vectorForcingNorm (candidateGradient α c A z U V P Q) :=
    mixedNorm_congr_nested_ae volume volume 2 (ENNReal.ofReal (6/5 : ℝ)) hdom.actual_ae_candidate
  refine ⟨hdom, hcoords, ?_, hcb, ?_⟩
  · intro j
    have heq : ∀ᵐ t ∂volume, (fun x => actualGradient α c A z U V P Q t x j) =ᵐ[volume]
        (fun x => candidateGradient α c A z U V P Q t x j) := by
      filter_upwards [hdom.actual_ae_candidate] with t ht
      exact ht.mono fun _ hx => congrArg (fun v : EuclideanSpace ℂ (Fin 3) => v j) hx
    rw [show forcingNorm (fun t x => actualGradient α c A z U V P Q t x j) =
        forcingNorm (fun t x => candidateGradient α c A z U V P Q t x j) from
      mixedNorm_congr_nested_ae volume volume 2 (ENNReal.ofReal (6/5 : ℝ)) heq]
    simpa only [candidateGradient_coordinate] using (hcoords j).bound
  · rw [hnorm]
    exact hcb

#print axioms projected_memLp_of_coordinates
#print axioms true_pair_slices
#print axioms actualGradient_candidate_ae
#print axioms actual_free_value_gradient_domains
#print axioms actual_free_value_gradient_bound
end HartreeF.FreeValueGradient
