import FFinitePowerDefects
import FCompactCrossTerms

/-! Actual finite integral linearity precedes the six-term candidate identity.
Every off-diagonal term is retained, including both derivative placements. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped BigOperators
namespace HartreeF.FiniteCandidateExpansion
open ForcingDomain WeakHartreeChain DerivativeMajorization FinitePowerDefects

variable {ι : Type*} [DecidableEq ι]

private theorem sum_smul_sum_off_diagonal (s : Finset ι)
    (a : ι → ℝ) (b : ι → ℂ) :
    (∑ i ∈ s, a i) • (∑ j ∈ s, b j) =
      (∑ i ∈ s, a i • b i) + ∑ i ∈ s, ∑ j ∈ s.erase i, a i • b j := by
  rw [Finset.sum_smul]
  calc
    (∑ i ∈ s, a i • ∑ j ∈ s, b j) =
        ∑ i ∈ s, (a i • b i + ∑ j ∈ s.erase i, a i • b j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.smul_sum]
      exact (Finset.add_sum_erase s (fun j => a i • b j) hi).symm
    _ = _ := Finset.sum_add_distrib

/-- Finite bilinear defect algebra; no integrals are distributed in this lemma. -/
theorem bilinear_defect (s : Finset ι) (a : ℝ) (b : ℂ)
    (A : ι → ℝ) (B : ι → ℂ) :
    a • b - ∑ i ∈ s, A i • B i =
      (a - ∑ i ∈ s, A i) • b +
      (∑ i ∈ s, A i) • (b - ∑ i ∈ s, B i) +
      ∑ i ∈ s, ∑ j ∈ s.erase i, A i • B j := by
  rw [sub_smul, smul_sub, sum_smul_sum_off_diagonal]
  abel

omit [DecidableEq ι] in
/-- Real signed Riesz linearity is used only with the actual absolute fibre domains. -/
theorem riesz_finite_difference (s : Finset ι) (α c : ℝ)
    (f : Space → ℝ) (g : ι → Space → ℝ) (x : Space)
    (hf : Integrable (fun y => rieszKernel α c (x-y) * f y) volume)
    (hg : ∀ i ∈ s, Integrable (fun y => rieszKernel α c (x-y) * g i y) volume) :
    rieszConvolution α c (fun y => f y - ∑ i ∈ s, g i y) x =
      rieszConvolution α c f x - ∑ i ∈ s, rieszConvolution α c (g i) x := by
  unfold rieszConvolution
  simp only [mul_sub, Finset.mul_sum]
  rw [integral_sub hf (integrable_finsetSum s hg), integral_finsetSum s hg]

/-- The literal finite-family directional candidate defect. -/
def candidateDefect (α c : ℝ) (s : Finset ι)
    (u h : ι → Space → ℂ) (x : Space) : ℂ :=
  directionalCandidate α c (fun y => ∑ i ∈ s, u i y)
    (fun y => ∑ i ∈ s, h i y) x -
      ∑ i ∈ s, directionalCandidate α c (u i) (h i) x

/-- Six actual terms, on the intersection of the original signed Riesz domains.
The four local defects here are the finite pointwise defects, not hypotheses. -/
theorem candidateDefect_six_terms (α c : ℝ) (s : Finset ι)
    (u h : ι → Space → ℂ) (x : Space)
    (hρ : Integrable (fun y => rieszKernel α c (x-y) *
      WeakHartreeChain.density (3+α) (∑ i ∈ s, u i y)) volume)
    (hρi : ∀ i ∈ s, Integrable (fun y => rieszKernel α c (x-y) *
      WeakHartreeChain.density (3+α) (u i y)) volume)
    (hd : Integrable (fun y => rieszKernel α c (x-y) *
      densityDerivative (3+α) (∑ i ∈ s, u i y) (∑ i ∈ s, h i y)) volume)
    (hdi : ∀ i ∈ s, Integrable (fun y => rieszKernel α c (x-y) *
      densityDerivative (3+α) (u i y) (h i y)) volume) :
    candidateDefect α c s u h x =
      rieszConvolution α c (fun y => densityDerivativeDefect α s
        (fun i => u i y) (fun i => h i y)) x •
          WeakHartreeChain.localFactor (1+α) (∑ i ∈ s, u i x) +
      (∑ i ∈ s, rieszConvolution α c (directionalDensity α (u i) (h i)) x) •
          localDefect α s (fun i => u i x) +
      (∑ i ∈ s, ∑ j ∈ s.erase i,
        rieszConvolution α c (directionalDensity α (u i) (h i)) x •
          WeakHartreeChain.localFactor (1+α) (u j x)) +
      rieszConvolution α c (fun y => densityDefect α s (fun i => u i y)) x •
          localFactorDerivative (1+α) (∑ i ∈ s, u i x) (∑ i ∈ s, h i x) +
      (∑ i ∈ s, potential α c (u i) x) •
          localDerivativeDefect α s (fun i => u i x) (fun i => h i x) +
      (∑ i ∈ s, ∑ j ∈ s.erase i,
        potential α c (u i) x • localFactorDerivative (1+α) (u j x) (h j x)) := by
  have hR0 := riesz_finite_difference s α c
    (fun y => WeakHartreeChain.density (3+α) (∑ i ∈ s, u i y))
    (fun i y => WeakHartreeChain.density (3+α) (u i y)) x hρ hρi
  have hR1 := riesz_finite_difference s α c
    (fun y => densityDerivative (3+α) (∑ i ∈ s, u i y) (∑ i ∈ s, h i y))
    (fun i y => densityDerivative (3+α) (u i y) (h i y)) x hd hdi
  change rieszConvolution α c (fun y => densityDefect α s (fun i => u i y)) x = _ at hR0
  change rieszConvolution α c (fun y => densityDerivativeDefect α s
    (fun i => u i y) (fun i => h i y)) x = _ at hR1
  rw [hR0, hR1]
  have hi := bilinear_defect s
    (rieszConvolution α c (directionalDensity α (fun y => ∑ i ∈ s, u i y)
      (fun y => ∑ i ∈ s, h i y)) x)
    (WeakHartreeChain.localFactor (1+α) (∑ i ∈ s, u i x))
    (fun i => rieszConvolution α c (directionalDensity α (u i) (h i)) x)
    (fun i => WeakHartreeChain.localFactor (1+α) (u i x))
  have ho := bilinear_defect s
    (potential α c (fun y => ∑ i ∈ s, u i y) x)
    (localFactorDerivative (1+α) (∑ i ∈ s, u i x) (∑ i ∈ s, h i x))
    (fun i => potential α c (u i) x)
    (fun i => localFactorDerivative (1+α) (u i x) (h i x))
  have hs := congrArg₂ (fun z w : ℂ => z + w) hi ho
  convert hs using 1 <;>
    dsimp only [candidateDefect, directionalCandidate, directionalDensity,
      localDefect, localDerivativeDefect, potential, rieszConvolution,
      powerDensity, WeakHartreeChain.density] <;>
    (try simp only [Finset.sum_add_distrib]) <;> abel

end HartreeF.FiniteCandidateExpansion
