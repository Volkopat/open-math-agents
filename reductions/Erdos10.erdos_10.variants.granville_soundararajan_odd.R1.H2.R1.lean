import OMAReductions.R_Erdos10_erdos_10_variants_granville_soundararajan_odd_R1

-- Reduction Erdos10.erdos_10.variants.granville_soundararajan_odd.R1.H2.R1 of step Erdos10.erdos_10.variants.granville_soundararajan_odd.R1.H2
-- Credit: @John-A-McMahon

namespace OMA.R_Erdos10_erdos_10_variants_granville_soundararajan_odd_R1_H2_R1

-- Finite initial segment.
def H1 : Prop :=
  ∀ n : ℕ, Even n → n ≠ 0 → n ≤ 256 → n ∈ Erdos10.sumPrimeAndTwoPows 4

-- Only the odd predecessors whose even successor cannot use the prime two remain.
def H2 : Prop :=
  ∀ m : ℕ, Odd m → 255 < m →
    (∀ s : Multiset ℕ, s.card ≤ 4 → (s.map (2 ^ ·)).sum ≠ m - 1) →
    m ∈ Erdos10.sumPrimeAndTwoPows 3

lemma add_one {n k : ℕ} (h : n ∈ Erdos10.sumPrimeAndTwoPows k) :
    n + 1 ∈ Erdos10.sumPrimeAndTwoPows (k + 1) := by
  rcases h with ⟨p, s, hp, hs, rfl⟩
  refine ⟨p, 0 ::ₘ s, hp, ?_, ?_⟩
  · simpa using Nat.add_le_add_right hs 1
  · simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma even_sum_of_no_zero (s : Multiset ℕ) (h : 0 ∉ s) :
    Even (s.map (2 ^ ·)).sum := by
  revert h
  induction s using Multiset.induction_on with
  | empty => intro h; exact ⟨0, by simp⟩
  | @cons a s ih =>
    intro h
    have ha : a ≠ 0 := by intro heq; apply h; simp [heq]
    have hs : 0 ∉ s := by intro hmem; apply h; simp [hmem]
    have hp : Even ((2 : ℕ) ^ a) := (show Even (2 : ℕ) from ⟨1, rfl⟩).pow_of_ne_zero ha
    simpa using hp.add (ih hs)

lemma predecessor_of_not_binary {n : ℕ} (hn : Even n)
    (h : n ∈ Erdos10.sumPrimeAndTwoPows 4)
    (hnb : ∀ s : Multiset ℕ, s.card ≤ 4 → (s.map (2 ^ ·)).sum ≠ n - 2) :
    n - 1 ∈ Erdos10.sumPrimeAndTwoPows 3 := by
  rcases h with ⟨p, s, hp, hcard, heq⟩
  have hpne : p ≠ 2 := by
    intro hp2
    subst p
    exact hnb s hcard (by omega)
  have hzero : 0 ∈ s := by
    by_contra hz
    have hs_even := even_sum_of_no_zero s hz
    rcases hn with ⟨a, ha⟩
    rcases hp.odd_of_ne_two hpne with ⟨b, hb⟩
    rcases hs_even with ⟨c, hc⟩
    omega
  rcases Multiset.exists_cons_of_mem hzero with ⟨t, rfl⟩
  refine ⟨p, t, hp, ?_, ?_⟩
  · simp only [Multiset.card_cons] at hcard
    omega
  · simp only [Multiset.map_cons, Multiset.sum_cons, pow_zero] at heq
    omega

lemma residual_necessary
    (h : OMA.R_Erdos10_erdos_10_variants_granville_soundararajan_odd_R1.H2) : H2 := by
  intro m hm hbound hnb
  have heven : Even (m + 1) := by
    rcases hm with ⟨k, hk⟩
    exact ⟨k + 1, by omega⟩
  have hrep : m + 1 ∈ Erdos10.sumPrimeAndTwoPows 4 :=
    h ⟨heven, by omega⟩
  have ht := predecessor_of_not_binary heven hrep (by
    intro s hs heq
    exact hnb s hs (by omega))
  simpa using ht

set_option maxHeartbeats 2000000 in
lemma finite_verified : H1 := by
  intro n ⟨k, hk⟩ h0 hbound
  have hk1 : 1 ≤ k := by omega
  have hk128 : k ≤ 128 := by omega
  have hn : n = 2 * k := by omega
  subst n
  interval_cases k
  · refine ⟨2, 0, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨3, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨5, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨7, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨7, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨11, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨13, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨13, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨17, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨19, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨19, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨23, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨23, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨23, {0, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨29, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨31, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨31, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨31, {0, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨37, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨37, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨41, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨43, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨43, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨47, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨47, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨47, {0, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨53, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨53, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨53, {0, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨59, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨61, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨61, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨61, {0, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨67, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨67, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨71, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨73, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨73, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨73, {0, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨79, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨79, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨83, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨83, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨83, {0, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨89, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨89, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨89, {0, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨89, {0, 1, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨97, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨97, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨101, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨103, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨103, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨107, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨109, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨109, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨113, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨113, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨113, {0, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨113, {0, 1, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨113, {0, 3}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨113, {0, 1, 3}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨113, {0, 2, 3}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨127, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨127, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨131, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨131, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨131, {0, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨137, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨139, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨139, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨139, {0, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨139, {0, 1, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨139, {0, 3}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨149, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨151, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨151, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨151, {0, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨157, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨157, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨157, {0, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨163, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨163, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨167, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨167, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨167, {0, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨173, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨173, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨173, {0, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨179, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨181, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨181, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨181, {0, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨181, {0, 1, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨181, {0, 3}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨191, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨193, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨193, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨197, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨199, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨199, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨199, {0, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨199, {0, 1, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨199, {0, 3}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨199, {0, 1, 3}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨211, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨211, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨211, {0, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨211, {0, 1, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨211, {0, 3}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨211, {0, 1, 3}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨223, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨223, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨227, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨229, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨229, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨233, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨233, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨233, {0, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨239, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨241, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨241, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨241, {0, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨241, {0, 1, 2}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨241, {0, 3}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨251, {0}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨251, {0, 1}, ?_, ?_, ?_⟩ <;> norm_num
  · refine ⟨251, {0, 2}, ?_, ?_, ?_⟩ <;> norm_num

theorem main : H1 → H2 → OMA.R_Erdos10_erdos_10_variants_granville_soundararajan_odd_R1.H2 := by
  classical
  intro h1 h2 n hn
  by_cases hsmall : n ≤ 256
  · exact h1 n hn.1 hn.2 hsmall
  by_cases hs : ∃ s : Multiset ℕ, s.card ≤ 4 ∧ (s.map (2 ^ ·)).sum = n - 2
  · rcases hs with ⟨s, hcard, hsum⟩
    refine ⟨2, s, Nat.prime_two, hcard, ?_⟩
    omega
  · have hodd : Odd (n - 1) := by
      rcases hn.1 with ⟨k, hk⟩
      exact ⟨k - 1, by omega⟩
    have hrep : n - 1 ∈ Erdos10.sumPrimeAndTwoPows 3 := by
      apply h2 (n - 1) hodd (by omega)
      intro s hcard heq
      apply hs
      exact ⟨s, hcard, by omega⟩
    have ht := add_one hrep
    have heq : n - 1 + 1 = n := by omega
    simpa only [heq] using ht

lemma odd_cover_suffices
    (h : {m : ℕ | Odd m ∧ 1 < m} ⊆ Erdos10.sumPrimeAndTwoPows 3) :
    OMA.R_Erdos10_erdos_10_variants_granville_soundararajan_odd_R1.H2 := by
  apply main finite_verified
  intro m hm hbound _
  exact h ⟨hm, by omega⟩

end OMA.R_Erdos10_erdos_10_variants_granville_soundararajan_odd_R1_H2_R1
