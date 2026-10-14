import DirectionalCandidateAlgebra
import DirectionalDensityEnvelopes
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
namespace HartreeF.DerivativeMajorization
open ForcingDomain WeakHartreeChain GradientMajorants

/-- The literal directional derivative expression. Its identification with a
weak derivative is deliberately a separate producer. -/
def directionalCandidate (α c : ℝ) (u h : Space → ℂ) (x : Space) : ℂ :=
  rieszConvolution α c (directionalDensity α u h) x • WeakHartreeChain.localFactor (1+α) (u x)+
    potential α c u x • localFactorDerivative (1+α) (u x) (h x)

def weightedMajorantSum (α c : ℝ) (V W Y Z : Space → ℝ) (x : Space) : ℝ :=
  (2+α)*majorant1 α c V Z x+
  ((3+α)*(2+α))*majorant2 α c V W Y x+
  ((1+α)*(6+α))*majorant3 α c V W Y x+
  (3+α)*majorant4 α c V Z x+
  ((3+α)*(2+α))*majorant5 α c V W Y x+
  ((3+α)*(2+α))*majorant6 α c V W Y x

theorem directional_candidate_six_pointwise {α c : ℝ} (ha : 0<α) (hc : 0≤c)
    {u v h k : Space → ℂ} (hu : AEStronglyMeasurable u volume)
    (hv : AEStronglyMeasurable v volume) (hh : AEStronglyMeasurable h volume)
    (hk : AEStronglyMeasurable k volume) (x : Space)
    (hbase : Integrable (fun y => rieszKernel α c (x-y)*sumAmplitude u v y^(3+α)) volume)
    (hdiff : Integrable (fun y => rieszKernel α c (x-y)*
      (sumAmplitude u v y^(2+α)*differenceAmplitude u v y)) volume)
    (hZ : Integrable (fun y => rieszKernel α c (x-y)*
      (sumAmplitude u v y^(2+α)*‖h y-k y‖)) volume)
    (hWY : Integrable (fun y => rieszKernel α c (x-y)*
      (sumAmplitude u v y^(1+α)*differenceAmplitude u v y*‖k y‖)) volume)
    (hY : Integrable (fun y => rieszKernel α c (x-y)*
      (sumAmplitude u v y^(2+α)*‖k y‖)) volume) :
    ‖directionalCandidate α c u h x-directionalCandidate α c v k x‖ ≤
      weightedMajorantSum α c (sumAmplitude u v) (differenceAmplitude u v)
        (fun y => ‖k y‖) (fun y => ‖h y-k y‖) x := by
  obtain ⟨_,_,hA,hAB⟩ := potential_pair_envelopes ha hc hu hv x hbase hdiff
  obtain ⟨_,_,hE,hDE⟩ := directional_density_pair_envelopes ha hc hu hv hh hk x hZ hWY hY
  have he := directional_candidate_algebra ha (u x) (v x) (h x) (k x)
    (potential α c u x) (potential α c v x)
    (rieszConvolution α c (directionalDensity α u h) x)
    (rieszConvolution α c (directionalDensity α v k) x)
    _ _ _ _ _ hA hAB hE hDE
  convert he using 1 <;>
    dsimp [directionalCandidate,weightedMajorantSum,majorant1,majorant2,majorant3,majorant4,majorant5,majorant6,
    sumAmplitude,differenceAmplitude]
  ring

theorem directional_candidate_six_ae {α c : ℝ} (ha : 0<α) (hc : 0≤c)
    {u v h k : Space → ℂ} (hu : AEStronglyMeasurable u volume)
    (hv : AEStronglyMeasurable v volume) (hh : AEStronglyMeasurable h volume)
    (hk : AEStronglyMeasurable k volume)
    (hd : MajorantDomains α c (sumAmplitude u v) (differenceAmplitude u v)
      (fun y => ‖k y‖) (fun y => ‖h y-k y‖)) :
    ∀ᵐ x ∂volume,
      ‖directionalCandidate α c u h x-directionalCandidate α c v k x‖ ≤
      weightedMajorantSum α c (sumAmplitude u v) (differenceAmplitude u v)
        (fun y => ‖k y‖) (fun y => ‖h y-k y‖) x := by
  filter_upwards [hd.first,hd.second,hd.fourth,hd.fifth,hd.sixth] with x h1 h2 h4 h5 h6
  exact directional_candidate_six_pointwise ha hc hu hv hh hk x h1 h2 h4 h5 h6

#print axioms directionalCandidate
#print axioms weightedMajorantSum
#print axioms directional_candidate_six_pointwise
#print axioms directional_candidate_six_ae
end HartreeF.DerivativeMajorization
