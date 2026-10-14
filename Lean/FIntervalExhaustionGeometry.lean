import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.Instances.Real.Lemmas

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open Filter Set
open scoped Topology
namespace HartreeF.IntervalNormExhaustion

/-- A genuine increasing compact-prefix exhaustion, including a closed
finite endpoint when one exists. No boundedness or openness of I is needed. -/
theorem exists_right_interval_exhaustion (I : Set ℝ) (hI : OrdConnected I)
    {s : ℝ} (hs : s ∈ I) :
    ∃ b : ℕ → ℝ, Monotone b ∧ (∀ n, b n ∈ I ∧ s ≤ b n) ∧
      (⋃ n, Icc s (b n)) = I ∩ Ici s := by
  let J : Set ℝ := I ∩ Ici s
  let : OrdConnected J := hI.inter ordConnected_Ici
  let : Nonempty J := ⟨⟨s,hs,Set.self_mem_Ici⟩⟩
  obtain ⟨b,hb,hlim⟩ := exists_seq_monotone_tendsto_atTop_atTop J
  refine ⟨fun n => (b n).val,fun n m hnm => hb hnm,fun n => (b n).property,?_⟩
  ext t
  constructor
  · intro ht
    obtain ⟨n,hn⟩ := mem_iUnion.mp ht
    exact ⟨hI.out' hs (b n).property.1 hn,hn.1⟩
  · intro ht
    obtain ⟨n,hn⟩ := (hlim.eventually (eventually_ge_atTop (⟨t,ht⟩ : J))).exists
    exact mem_iUnion.mpr ⟨n,ht.2,hn⟩

/-- The matching decreasing compact-suffix exhaustion uses order duality
only in the time geometry, with no reflection of a Schrödinger solution. -/
theorem exists_left_interval_exhaustion (I : Set ℝ) (hI : OrdConnected I)
    {s : ℝ} (hs : s ∈ I) :
    ∃ a : ℕ → ℝ, Antitone a ∧ (∀ n, a n ∈ I ∧ a n ≤ s) ∧
      (⋃ n, Icc (a n) s) = I ∩ Iic s := by
  let J : Set ℝ := I ∩ Iic s
  let : OrdConnected J := hI.inter ordConnected_Iic
  let : Nonempty J := ⟨⟨s,hs,Set.self_mem_Iic⟩⟩
  obtain ⟨a,ha,hlim⟩ := exists_seq_antitone_tendsto_atTop_atBot J
  refine ⟨fun n => (a n).val,fun n m hnm => ha hnm,fun n => (a n).property,?_⟩
  ext t
  constructor
  · intro ht
    obtain ⟨n,hn⟩ := mem_iUnion.mp ht
    exact ⟨hI.out' (a n).property.1 hs hn,hn.2⟩
  · intro ht
    obtain ⟨n,hn⟩ := (hlim.eventually (eventually_le_atBot (⟨t,ht⟩ : J))).exists
    exact mem_iUnion.mpr ⟨n,hn,ht.2⟩

/-- Both endpoint sequences and the exact union are produced from I and its
center. Singleton intervals are included rather than silently discarded. -/
theorem exists_centered_interval_exhaustion (I : Set ℝ) (hI : OrdConnected I)
    {s : ℝ} (hs : s ∈ I) :
    ∃ a b : ℕ → ℝ, Antitone a ∧ Monotone b ∧
      (∀ n, a n ∈ I ∧ b n ∈ I ∧ a n ≤ s ∧ s ≤ b n) ∧
      (∀ n, Icc (a n) (b n) ⊆ I) ∧ (⋃ n, Icc (a n) (b n)) = I := by
  obtain ⟨a,ha,haI,hcovera⟩ := exists_left_interval_exhaustion I hI hs
  obtain ⟨b,hb,hbI,hcoverb⟩ := exists_right_interval_exhaustion I hI hs
  have hsub (n : ℕ) : Icc (a n) (b n) ⊆ I := hI.out' (haI n).1 (hbI n).1
  refine ⟨a,b,ha,hb,fun n => ⟨(haI n).1,(hbI n).1,(haI n).2,(hbI n).2⟩,hsub,?_⟩
  ext t
  constructor
  · intro ht
    obtain ⟨n,hn⟩ := mem_iUnion.mp ht
    exact hsub n hn
  · intro ht
    by_cases hst : s ≤ t
    · have hc : t ∈ ⋃ n, Icc s (b n) := hcoverb.symm ▸ ⟨ht,hst⟩
      obtain ⟨n,hn⟩ := mem_iUnion.mp hc
      exact mem_iUnion.mpr ⟨n,(haI n).2.trans hn.1,hn.2⟩
    · have hts : t ≤ s := le_of_not_ge hst
      have hc : t ∈ ⋃ n, Icc (a n) s := hcovera.symm ▸ ⟨ht,hts⟩
      obtain ⟨n,hn⟩ := mem_iUnion.mp hc
      exact mem_iUnion.mpr ⟨n,hn.1,hn.2.trans (hbI n).2⟩

#print axioms exists_right_interval_exhaustion
#print axioms exists_left_interval_exhaustion
#print axioms exists_centered_interval_exhaustion
end HartreeF.IntervalNormExhaustion
