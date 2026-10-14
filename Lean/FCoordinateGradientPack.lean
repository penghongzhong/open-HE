import FActualRealSliceMembership
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain GradientMajorants SobolevStretch
open WeakHartreeProduct DerivativeMajorization DerivativeMajorizationReview
open scoped ENNReal NNReal RealInnerProductSpace

def packGradient (a b c : ℂ) : EuclideanSpace ℂ (Fin 3) :=
  a • EuclideanSpace.basisFun (Fin 3) ℂ 0 +
  b • EuclideanSpace.basisFun (Fin 3) ℂ 1 +
  c • EuclideanSpace.basisFun (Fin 3) ℂ 2

theorem packGradient_sub (a b c d e f : ℂ) :
    packGradient (a-d) (b-e) (c-f) = packGradient a b c - packGradient d e f := by
  simp only [packGradient, sub_smul]
  abel

theorem packGradient_coordinate (a b c : ℂ) (i : Fin 3) :
    packGradient a b c i = ![a,b,c] i := by
  fin_cases i <;> simp [packGradient, EuclideanSpace.basisFun_apply]

/-- The actual complex gradient, in the Euclidean norm of ℂ³. -/
def actualFullGradient (alpha c : ℝ) (u : Space → ℂ) (U V : Space → Space)
    (x : Space) : EuclideanSpace ℂ (Fin 3) :=
  packGradient
    (actualDirectionalDerivative alpha c u U V (EuclideanSpace.basisFun (Fin 3) ℝ 0) x)
    (actualDirectionalDerivative alpha c u U V (EuclideanSpace.basisFun (Fin 3) ℝ 1) x)
    (actualDirectionalDerivative alpha c u U V (EuclideanSpace.basisFun (Fin 3) ℝ 2) x)

theorem actualFullGradient_coordinate (alpha c : ℝ) (u : Space → ℂ)
    (U V : Space → Space) (x : Space) (i : Fin 3) :
    actualFullGradient alpha c u U V x i = Complex.equivRealProdCLM.symm
      (forcingGradientRe alpha c u U V x i, forcingGradientIm alpha c u U V x i) := by
  have hDir : ∀ j : Fin 3,
      actualDirectionalDerivative alpha c u U V (EuclideanSpace.basisFun (Fin 3) ℝ j) x =
        Complex.equivRealProdCLM.symm
          (forcingGradientRe alpha c u U V x j, forcingGradientIm alpha c u U V x j) := by
    intro j
    change Complex.equivRealProdCLM.symm
      (inner ℝ (forcingGradientRe alpha c u U V x) (EuclideanSpace.basisFun (Fin 3) ℝ j),
       inner ℝ (forcingGradientIm alpha c u U V x) (EuclideanSpace.basisFun (Fin 3) ℝ j)) = _
    rw [EuclideanSpace.inner_basisFun_real, EuclideanSpace.inner_basisFun_real]
  fin_cases i
  · simpa [actualFullGradient, packGradient_coordinate] using hDir 0
  · simpa [actualFullGradient, packGradient_coordinate] using hDir 1
  · simpa [actualFullGradient, packGradient_coordinate] using hDir 2

theorem coordinate_embedding_lp {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (q : ℝ≥0∞) (f : X → ℂ) (hf : AEStronglyMeasurable f mu)
    (i : Fin 3) :
    eLpNorm (fun x => f x • EuclideanSpace.basisFun (Fin 3) ℂ i) q mu =
      eLpNorm f q mu := by
  apply eLpNorm_congr_enorm_ae (hf.smul_const _) hf
  filter_upwards [] with x
  simp only [enorm_smul, OrthonormalBasis.enorm_eq_one, mul_one]

end HartreeF.TimeHolder
