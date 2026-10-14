import FRetardedScalarL2

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory FourierTransform LineDeriv
open scoped ENNReal SchwartzMap
namespace HartreeF.Retarded
open FreeFlow

/-- Distribution derivatives commute with the scalar Duhamel integrand because
we use the exact transpose of the previously proved Fourier group. -/
theorem scalarIntegrand_derivative (t s : ℝ) (F G : EndpointSource) (v : V)
    (h : ∂_{v} (Lp.toTemperedDistribution (F s)) = Lp.toTemperedDistribution (G s))
    (φ : Test) : -scalarIntegrand t F (∂_{v} φ) s = scalarIntegrand t G φ s := by
  have hd := congrArg (fun T : TD => T φ) (derivative_free (t-s)
    (Lp.toTemperedDistribution (F s)) v)
  rw [h, TemperedDistribution.lineDerivOp_apply_apply, free_apply, free_apply] at hd
  simpa only [map_neg, scalarIntegrand] using hd

/-- The L2 output derivative is produced by scalar integration. The hypothesis
is only source compatibility, which the actual C41 consumer establishes. -/
theorem restrictedL2_derivative {C : ℝ} (h : OrdinaryEndpointBound C)
    (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) (F G : EndpointSource) (v : V)
    (hFG : ∀ᵐ s ∂volume.restrict J,
      ∂_{v} (Lp.toTemperedDistribution (F s)) = Lp.toTemperedDistribution (G s)) :
    ∂_{v} (Lp.toTemperedDistribution (restrictedL2 h J hJ t F)) =
      Lp.toTemperedDistribution (restrictedL2 h J hJ t G) := by
  ext φ
  rw [TemperedDistribution.lineDerivOp_apply_apply, restrictedL2_scalar,
    restrictedL2_scalar]
  apply integral_congr_ae
  filter_upwards [hFG] with s hs
  simpa only [scalarIntegrand, map_neg] using scalarIntegrand_derivative t s F G v hs φ

theorem retardedL2_derivative {C : ℝ} (h : OrdinaryEndpointBound C)
    (F G : EndpointSource) (v : V)
    (hFG : ∀ᵐ s ∂volume,
      ∂_{v} (Lp.toTemperedDistribution (F s)) = Lp.toTemperedDistribution (G s))
    (t : ℝ) :
    ∂_{v} (Lp.toTemperedDistribution (retardedL2 h F t)) =
      Lp.toTemperedDistribution (retardedL2 h G t) :=
  restrictedL2_derivative h _ measurableSet_Iio t F G v (ae_restrict_of_ae hFG)

/-- Changing a numerical endpoint bound does not change the constructed output. -/
theorem restrictedL2_interface_independent {C D : ℝ}
    (hC : OrdinaryEndpointBound C) (hD : OrdinaryEndpointBound D)
    (J : Set ℝ) (hJ : MeasurableSet J) (t : ℝ) (F : EndpointSource) :
    restrictedL2 hC J hJ t F = restrictedL2 hD J hJ t F := by
  apply l2_distribution_injective
  ext φ
  rw [restrictedL2_scalar, restrictedL2_scalar]

/-- Forward zero-initial-data integral. Orientation is explicitly a ≤ t;
for t<a this set-integral is zero, rather than an oriented backward integral. -/
def forwardL2 {C : ℝ} (h : OrdinaryEndpointBound C) (a : ℝ)
    (F : EndpointSource) (t : ℝ) : L2 :=
  restrictedL2 h (Set.Ioc a t) measurableSet_Ioc t F

theorem forwardL2_scalar {C : ℝ} (h : OrdinaryEndpointBound C) (a : ℝ)
    (F : EndpointSource) (t : ℝ) (φ : Test) :
    Lp.toTemperedDistribution (forwardL2 h a F t) φ =
      ∫ s in Set.Ioc a t, scalarIntegrand t F φ s :=
  restrictedL2_scalar h _ measurableSet_Ioc t F φ

theorem forwardL2_initial {C : ℝ} (h : OrdinaryEndpointBound C)
    (a : ℝ) (F : EndpointSource) : forwardL2 h a F a = 0 := by
  apply l2_distribution_injective
  ext φ
  rw [forwardL2_scalar]
  simp

end HartreeF.Retarded
