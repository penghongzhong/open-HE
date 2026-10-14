import FLocalActualGradientBochnerSource

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain GradientMajorants SobolevStretch StationarySelfTest
open WeakHartreeProduct DerivativeMajorization DerivativeMajorizationReview
open scoped ENNReal NNReal RealInnerProductSpace

/-- The real coordinate projection from the actual complex Euclidean gradient. -/
def gradientReal (g : EuclideanSpace ℂ (Fin 3)) : Space :=
  WithLp.toLp 2 (fun i => (g i).re)

/-- The imaginary coordinate projection from the actual complex Euclidean gradient. -/
def gradientImag (g : EuclideanSpace ℂ (Fin 3)) : Space :=
  WithLp.toLp 2 (fun i => (g i).im)

theorem gradientReal_actual_difference (alpha c : ℝ) (u v : Space → ℂ)
    (U V P Q : Space → Space) (x : Space) :
    gradientReal (actualFullGradient alpha c u U V x - actualFullGradient alpha c v P Q x) =
      forcingGradientRe alpha c u U V x - forcingGradientRe alpha c v P Q x := by
  ext i
  simp [gradientReal, actualFullGradient_coordinate]

theorem gradientImag_actual_difference (alpha c : ℝ) (u v : Space → ℂ)
    (U V P Q : Space → Space) (x : Space) :
    gradientImag (actualFullGradient alpha c u U V x - actualFullGradient alpha c v P Q x) =
      forcingGradientIm alpha c u U V x - forcingGradientIm alpha c v P Q x := by
  ext i
  simp [gradientImag, actualFullGradient_coordinate]

theorem weakGradient_sub {f g : Space → ℝ} {F G : Space → Space}
    (hf : HasWeakGradient f F) (hg : HasWeakGradient g G) :
    HasWeakGradient (fun x => f x - g x) (fun x => F x - G x) := by
  refine ⟨hf.function_local.sub hg.function_local,
    hf.gradient_local.sub hg.gradient_local, ?_⟩
  intro e phi hphi hc
  have hft := hf.test_integrable hphi hc e
  have hgt := hg.test_integrable hphi hc e
  simp only [sub_mul, inner_sub_left]
  rw [integral_sub hft.1 hgt.1, integral_sub hft.2 hgt.2,
    hf.integration_by_parts e phi hphi hc, hg.integration_by_parts e phi hphi hc]
  ring

theorem weakGradient_congr_gradient {f : Space → ℝ} {F G : Space → Space}
    (hf : HasWeakGradient f F) (hFG : F =ᵐ[volume] G) : HasWeakGradient f G := by
  refine ⟨hf.function_local, hf.gradient_local.congr hFG, ?_⟩
  intro e phi hphi hc
  rw [hf.integration_by_parts e phi hphi hc]
  congr 1
  apply integral_congr_ae
  filter_upwards [hFG] with x hx
  rw [hx]

/-- The C26 weak identity, including its ordinary density and Sobolev interfaces,
is transported to any spatial AE representative of the C32 actual difference.
The desired weak-gradient conclusion is produced, rather than assumed. -/
theorem actual_gradient_representative_hasWeakGradients (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    {u v : Space → ℂ} {U V P Q : Space → Space}
    (hu : InDotH1 u U V) (hv : InDotH1 v P Q)
    (hu10 : MemLp u 10 volume) (hv10 : MemLp v 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hP : MemLp P (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hQ : MemLp Q (ENNReal.ofReal (30/13 : ℝ)) volume)
    (g : Space → EuclideanSpace ℂ (Fin 3))
    (hrep : ∀ᵐ x ∂(volume : Measure Space),
      g x = actualFullGradient alpha c u U V x - actualFullGradient alpha c v P Q x) :
    HasWeakGradient (fun x => (forcing alpha c u x - forcing alpha c v x).re)
      (fun x => gradientReal (g x)) ∧
    HasWeakGradient (fun x => (forcing alpha c u x - forcing alpha c v x).im)
      (fun x => gradientImag (g x)) := by
  have hwu := hartree_forcing_weak_gradients hDensity hSob hH hu hu10 hU hV
  have hwv := hartree_forcing_weak_gradients hDensity hSob hH hv hv10 hP hQ
  constructor
  · apply weakGradient_congr_gradient (by
      simpa only [Complex.sub_re] using weakGradient_sub hwu.1 hwv.1)
    filter_upwards [hrep] with x hx
    rw [hx, gradientReal_actual_difference]
  · apply weakGradient_congr_gradient (by
      simpa only [Complex.sub_im] using weakGradient_sub hwu.2 hwv.2)
    filter_upwards [hrep] with x hx
    rw [hx, gradientImag_actual_difference]

attribute [local instance] gradientSourceExponent_one_le gradientSourceExponent_ne_top

/-- A nested time/space AE representative of the actual gradient difference is
the genuine distributional gradient on almost every time slice. All three
ordinary analytic interfaces are explicit. -/
theorem actual_gradient_bochnerSource_hasWeakGradients (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    {T : Type*} [MeasurableSpace T] (mu : Measure T)
    (u v : T → Space → ℂ) (U V P Q : T → Space → Space)
    (hSlices : ∀ᵐ t ∂mu,
      InDotH1 (u t) (U t) (V t) ∧ InDotH1 (v t) (P t) (Q t) ∧
      MemLp (u t) 10 volume ∧ MemLp (v t) 10 volume ∧
      MemLp (U t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (V t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (P t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
      MemLp (Q t) (ENNReal.ofReal (30/13 : ℝ)) volume)
    (G : Lp (Lp (EuclideanSpace ℂ (Fin 3)) (ENNReal.ofReal (6/5 : ℝ))
      (volume : Measure Space)) 2 mu)
    (hrep : ∀ᵐ t ∂mu, ∀ᵐ x ∂(volume : Measure Space),
      G t x = actualFullGradient alpha c (u t) (U t) (V t) x -
        actualFullGradient alpha c (v t) (P t) (Q t) x) :
    ∀ᵐ t ∂mu,
      HasWeakGradient (fun x => (forcing alpha c (u t) x - forcing alpha c (v t) x).re)
        (fun x => gradientReal (G t x)) ∧
      HasWeakGradient (fun x => (forcing alpha c (u t) x - forcing alpha c (v t) x).im)
        (fun x => gradientImag (G t x)) := by
  filter_upwards [hSlices, hrep] with t hs hr
  exact actual_gradient_representative_hasWeakGradients hDensity hSob hH
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2.1
    hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2 (fun x => G t x) hr

/-- Coordinate tests are the usual compactly supported smooth distributional
tests; both sides are integrable. The smoothness index is the inner infinity
`(top : NatInfinity)`, exactly as in the genuine HasWeakGradient definition. -/
theorem weakGradients_coordinate_tests {f : Space → ℂ}
    {g : Space → EuclideanSpace ℂ (Fin 3)}
    (hR : HasWeakGradient (fun x => (f x).re) (fun x => gradientReal (g x)))
    (hI : HasWeakGradient (fun x => (f x).im) (fun x => gradientImag (g x)))
    (i : Fin 3) (phi : Space → ℝ)
    (hphi : ContDiff ℝ (⊤ : ℕ∞) phi) (hc : HasCompactSupport phi) :
    Integrable (fun x => (f x).re *
      fderiv ℝ phi x (EuclideanSpace.basisFun (Fin 3) ℝ i)) volume ∧
    Integrable (fun x => (g x i).re * phi x) volume ∧
    (∫ x, (f x).re * fderiv ℝ phi x (EuclideanSpace.basisFun (Fin 3) ℝ i)) =
      -(∫ x, (g x i).re * phi x) ∧
    Integrable (fun x => (f x).im *
      fderiv ℝ phi x (EuclideanSpace.basisFun (Fin 3) ℝ i)) volume ∧
    Integrable (fun x => (g x i).im * phi x) volume ∧
    (∫ x, (f x).im * fderiv ℝ phi x (EuclideanSpace.basisFun (Fin 3) ℝ i)) =
      -(∫ x, (g x i).im * phi x) := by
  have htR := hR.test_integrable hphi hc (EuclideanSpace.basisFun (Fin 3) ℝ i)
  have htI := hI.test_integrable hphi hc (EuclideanSpace.basisFun (Fin 3) ℝ i)
  have heR := hR.integration_by_parts (EuclideanSpace.basisFun (Fin 3) ℝ i) phi hphi hc
  have heI := hI.integration_by_parts (EuclideanSpace.basisFun (Fin 3) ℝ i) phi hphi hc
  have hcoordR : ∀ x, inner ℝ (gradientReal (g x))
      (EuclideanSpace.basisFun (Fin 3) ℝ i) = (g x i).re := by
    intro x
    rw [EuclideanSpace.inner_basisFun_real]
    rfl
  have hcoordI : ∀ x, inner ℝ (gradientImag (g x))
      (EuclideanSpace.basisFun (Fin 3) ℝ i) = (g x i).im := by
    intro x
    rw [EuclideanSpace.inner_basisFun_real]
    rfl
  simpa only [hcoordR, hcoordI] using
    And.intro htR.1 (And.intro htR.2 (And.intro heR (And.intro htI.1 (And.intro htI.2 heI))))

end HartreeF.TimeHolder
