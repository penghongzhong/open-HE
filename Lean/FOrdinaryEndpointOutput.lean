import FOrdinaryHomogeneousStrichartz
import FOrdinaryRetardedStrichartz

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.EndpointOutput
open MeasureTheory Filter SobolevStretch StationarySelfTest TimeHolder EnergySpace
open ActualStrichartz Retarded LineDeriv
open scoped ENNReal NNReal

/-- Keel--Tao, Endpoint Strichartz estimates, American Journal of Mathematics
120 (1998), 955--980, Theorem 1.2, printed p.956, (5), and Corollary 1.4,
printed p.958: n=3, sigma=3/2, output (q,r)=(2,6).
This is only the numerical bound for the literal constructed Fourier freeL2
representative. It supplies no operator, state, or compatibility witness.
It is an explicit analytic premise, not a native analytic theorem instance. -/
def OrdinaryHomogeneousEndpointOutput (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ f : FreeFlow.L2,
    mixedNorm volume volume 2 6 (freeJoint f) ≤ ENNReal.ofReal (C * ‖f‖)

/-- The same Keel--Tao Theorem 1.2, printed p.956, (7), Corollary 1.4,
printed p.958: n=3, sigma=3/2, input and output admissible pairs (2,6),
input dual norm L2_t L(6/5)_x, output norm L2_t L6_x.
The all-past retardedL2 and its joint representative are already constructed.
The older endpoint bound constructs that object but does not imply this bound.
This proposition retains just the exact numerical specialization needed for
the endpoint part of eq:linear in F_Compactness_Producer_20261006.tex. -/
def OrdinaryRetardedEndpointOutput {C0 : ℝ} (h0 : OrdinaryEndpointBound C0)
    (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ F : EndpointSource,
    mixedNorm volume volume 2 6 (retardedJoint h0 F) ≤ ENNReal.ofReal (C * ‖F‖)

theorem freeJoint_endpoint_finite {C : ℝ} (h : OrdinaryHomogeneousEndpointOutput C)
    (f : FreeFlow.L2) : mixedNorm volume volume 2 6 (freeJoint f) ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.2 f)

theorem retardedJoint_endpoint_finite {C0 C : ℝ} (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedEndpointOutput h0 C) (F : EndpointSource) :
    mixedNorm volume volume 2 6 (retardedJoint h0 F) ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.2 F)

theorem freeJoint_endpoint_memLp {C : ℝ} (h : OrdinaryHomogeneousEndpointOutput C)
    (f : FreeFlow.L2) : ∀ᵐ t ∂(volume : Measure ℝ), MemLp (freeJoint f t) 6 volume :=
  finite_mixedNorm_ae_slice_memLp volume volume 2 6 (by norm_num) (by norm_num)
    (freeJoint f) (freeJoint_endpoint_finite h f)

theorem retardedJoint_endpoint_memLp {C0 C : ℝ} (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedEndpointOutput h0 C) (F : EndpointSource) :
    ∀ᵐ t ∂(volume : Measure ℝ), MemLp (retardedJoint h0 F t) 6 volume :=
  finite_mixedNorm_ae_slice_memLp volume volume 2 6 (by norm_num) (by norm_num)
    (retardedJoint h0 F) (retardedJoint_endpoint_finite h0 h F)

theorem freeEnergyState_endpoint_bound (hDensity : OrdinaryH1Density) {K C : ℝ}
    (hSob : OrdinarySobolev K) (h : OrdinaryHomogeneousEndpointOutput C)
    (u : EnergyState) (j : Fin 3) :
    mixedNorm volume volume 2 6
      (fun t => energyGradient j (freeEnergyState hDensity hSob t u)) ≤
      ENNReal.ofReal (C * ‖energyGradient j u‖) := by
  have he : mixedNorm volume volume 2 6
      (fun t => energyGradient j (freeEnergyState hDensity hSob t u)) =
      mixedNorm volume volume 2 6 (freeJoint (energyGradient j u)) := by
    apply eLpNorm_congr_ae
    filter_upwards [freeJoint_energyGradient hDensity hSob u j] with t ht
    exact eLpNorm_congr_ae ht.symm
  rw [he]
  exact h.2 _

theorem retardedEnergyState_endpoint_bound (hDensity : OrdinaryH1Density) {K C0 C : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedEndpointOutput h0 C)
    (F : EndpointSource) (G : Fin 3 → EndpointSource)
    (hFG : ∀ j : Fin 3, ∀ᵐ s ∂volume,
      ∂_{coordinate j} (Lp.toTemperedDistribution (F s)) = Lp.toTemperedDistribution (G j s))
    (j : Fin 3) :
    mixedNorm volume volume 2 6
      (fun t => energyGradient j (retardedEnergyState hDensity hSob h0 F G hFG t)) ≤
      ENNReal.ofReal (C * ‖G j‖) := by
  have he : mixedNorm volume volume 2 6
      (fun t => energyGradient j (retardedEnergyState hDensity hSob h0 F G hFG t)) =
      mixedNorm volume volume 2 6 (retardedJoint h0 (G j)) := by
    apply eLpNorm_congr_ae
    filter_upwards [retardedJoint_energyGradient hDensity hSob h0 F G hFG j] with t ht
    exact eLpNorm_congr_ae ht.symm
  rw [he]
  exact h.2 _

end HartreeF.EndpointOutput
