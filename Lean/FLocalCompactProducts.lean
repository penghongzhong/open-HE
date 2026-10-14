import FLocalProductOrthogonality
import FLocalProductHolder

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.LocalProfileProducts
open TimeHolder CompactCross

theorem localProductNorm_comm {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (q : ℝ≥0∞) (f : ℝ → Space → E) (g : ℝ → Space → F) :
    localProductNorm q f g = localProductNorm q g f := by
  unfold localProductNorm normProduct
  congr 1
  funext t x
  exact mul_comm _ _

theorem compact_P_orthogonality {ι : Type*} {l : Filter ι}
    {f g : ℝ → Space → ℂ}
    (hf : Continuous (fun z : ℝ × Space => f z.1 z.2))
    (hg : Continuous (fun z : ℝ × Space => g z.1 z.2))
    (hfC : HasCompactSupport (fun z : ℝ × Space => f z.1 z.2))
    (hgC : HasCompactSupport (fun z : ℝ × Space => g z.1 z.2))
    {a b s r : ι → ℝ} {y z : ι → Space}
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (horth : Tendsto (fun i => a i/b i+b i/a i+‖y i-z i‖^2/(a i*b i)+
      |a i^2*s i-b i^2*r i|/(a i*b i)) l atTop) :
    Tendsto (fun i => localProductNorm 5
      (seedFrame (a i) (y i) (s i) (1/2) f)
      (seedFrame (b i) (z i) (r i) (1/2) g)) l (𝓝 0) := by
  have h := compact_frameProductNorm_orthogonality (q := 5) (w := 1/2) (v := 1/2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hf hg hfC hgC ha hb horth
  change Tendsto (fun i => localProductNorm (ENNReal.ofReal (5:ℝ))
    (seedFrame (a i) (y i) (s i) (1/2) f)
    (seedFrame (b i) (z i) (r i) (1/2) g)) l (𝓝 0) at h
  simpa only [ENNReal.ofReal_ofNat] using h

theorem compact_Q_orthogonality {ι : Type*} {l : Filter ι}
    {f g : ℝ → Space → ℂ}
    (hf : Continuous (fun z : ℝ × Space => f z.1 z.2))
    (hg : Continuous (fun z : ℝ × Space => g z.1 z.2))
    (hfC : HasCompactSupport (fun z : ℝ × Space => f z.1 z.2))
    (hgC : HasCompactSupport (fun z : ℝ × Space => g z.1 z.2))
    {a b s r : ι → ℝ} {y z : ι → Space}
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (horth : Tendsto (fun i => a i/b i+b i/a i+‖y i-z i‖^2/(a i*b i)+
      |a i^2*s i-b i^2*r i|/(a i*b i)) l atTop) :
    Tendsto (fun i => localProductNorm (ENNReal.ofReal (15/8 : ℝ))
      (seedFrame (a i) (y i) (s i) (1/2) f)
      (seedFrame (b i) (z i) (r i) (3/2) g)) l (𝓝 0) := by
  exact compact_frameProductNorm_orthogonality (q := 15/8) (w := 1/2) (v := 3/2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hf hg hfC hgC ha hb horth

theorem compact_Q_reverse_orthogonality {ι : Type*} {l : Filter ι}
    {f g : ℝ → Space → ℂ}
    (hf : Continuous (fun z : ℝ × Space => f z.1 z.2))
    (hg : Continuous (fun z : ℝ × Space => g z.1 z.2))
    (hfC : HasCompactSupport (fun z : ℝ × Space => f z.1 z.2))
    (hgC : HasCompactSupport (fun z : ℝ × Space => g z.1 z.2))
    {a b s r : ι → ℝ} {y z : ι → Space}
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (horth : Tendsto (fun i => a i/b i+b i/a i+‖y i-z i‖^2/(a i*b i)+
      |a i^2*s i-b i^2*r i|/(a i*b i)) l atTop) :
    Tendsto (fun i => localProductNorm (ENNReal.ofReal (15/8 : ℝ))
      (seedFrame (a i) (y i) (s i) (3/2) f)
      (seedFrame (b i) (z i) (r i) (1/2) g)) l (𝓝 0) := by
  have horth' : Tendsto (fun i => b i/a i+a i/b i+‖z i-y i‖^2/(b i*a i)+
      |b i^2*r i-a i^2*s i|/(b i*a i)) l atTop := by
    convert horth using 1
    funext i
    rw [norm_sub_rev (z i) (y i),abs_sub_comm (b i^2*r i) (a i^2*s i),mul_comm (b i) (a i)]
    ring
  have h := compact_Q_orthogonality hg hf hgC hfC hb ha horth'
  convert h using 1
  funext i
  exact localProductNorm_comm _ _ _

#print axioms localProductNorm_comm
#print axioms compact_P_orthogonality
#print axioms compact_Q_orthogonality
#print axioms compact_Q_reverse_orthogonality
end HartreeF.LocalProfileProducts
