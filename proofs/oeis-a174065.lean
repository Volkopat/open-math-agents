import OMAStatements.S_oeis_a174065
import Mathlib

-- Problem: OEIS A174065, conjecture of Adamson: the sequence whose convolution with its
-- aerated variant is the partition numbers A000041 is the Euler transform of A035263, that is
-- the number of partitions into parts with an even 2-adic valuation.
-- Statement: statements/oeis-a174065.lean (declaration OMA.S_oeis_a174065.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Call a part admissible if its 2-adic valuation is even. Let c(n) be the number of
-- partitions of n into admissible parts. A part that is not admissible is 2 y with y
-- admissible, and the double of an admissible part is not admissible. So a partition of n is
-- the same as a pair: its admissible parts (a restricted partition of i) and the halves of the
-- other parts (a restricted partition of t), with i + 2 t = n. This bijection gives
-- Sum_{i + 2 t = n} c(i) c(t) = A000041(n), so c has the defining property. The property
-- gives a(0) = 1 and then a(n) from the smaller terms, so strong induction gives a = c.

namespace OMA.A174065

open OMA.S_oeis_a174065

/-- The admissible parts: even 2-adic valuation. -/
abbrev E (k : ℕ) : Prop := Even (padicValNat 2 k)

lemma val_two_mul (x : ℕ) (hx : 0 < x) : padicValNat 2 (2 * x) = padicValNat 2 x + 1 := by
  rw [padicValNat.mul (by norm_num) (by omega), padicValNat_self, add_comm]

lemma not_E_two_mul (x : ℕ) (hx : 0 < x) (h : E x) : ¬ E (2 * x) := by
  unfold E at *
  rw [val_two_mul x hx, Nat.even_add_one]
  exact not_not.mpr h

lemma of_not_E (x : ℕ) (hx : 0 < x) (h : ¬ E x) : ∃ y, 0 < y ∧ x = 2 * y ∧ E y := by
  unfold E at h
  have h1 : 1 ≤ padicValNat 2 x := by
    rcases Nat.eq_zero_or_pos (padicValNat 2 x) with h0 | h0
    · rw [h0] at h; exact absurd (by decide) h
    · exact h0
  obtain ⟨y, rfl⟩ := dvd_of_one_le_padicValNat h1
  have hy : 0 < y := by omega
  refine ⟨y, hy, rfl, ?_⟩
  rw [val_two_mul y hy, Nat.even_add_one, not_not] at h
  exact h

/-- The restricted partitions of n. -/
def R (n : ℕ) : Finset (Nat.Partition n) :=
  Finset.univ.filter (fun π => ∀ k ∈ π.parts, E k)

lemma euler_eq (n : ℕ) : euler n = (R n).card := by
  unfold euler R
  rw [Fintype.card_subtype]

/-- Join a restricted partition of i with the double of a restricted partition of t. -/
def join (i t n : ℕ) (h : i + 2 * t = n) (π : Nat.Partition i × Nat.Partition t) :
    Nat.Partition n where
  parts := π.1.parts + π.2.parts.map (fun x => 2 * x)
  parts_pos := by
    intro k hk
    rcases Multiset.mem_add.mp hk with hk | hk
    · exact π.1.parts_pos hk
    · obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hk
      have := π.2.parts_pos hx
      omega
  parts_sum := by
    rw [Multiset.sum_add, Multiset.sum_map_mul_left, π.1.parts_sum]
    simp [π.2.parts_sum, h]

lemma filter_join (i t n : ℕ) (h : i + 2 * t = n) (π : Nat.Partition i × Nat.Partition t)
    (h1 : π.1 ∈ R i) (h2 : π.2 ∈ R t) :
    (join i t n h π).parts.filter E = π.1.parts ∧
    (join i t n h π).parts.filter (fun k => ¬ E k) = π.2.parts.map (fun x => 2 * x) := by
  have a1 : ∀ k ∈ π.1.parts, E k := (Finset.mem_filter.mp h1).2
  have a2 : ∀ k ∈ π.2.parts, E k := (Finset.mem_filter.mp h2).2
  have b2 : ∀ k ∈ π.2.parts.map (fun x => 2 * x), ¬ E k := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hk
    exact not_E_two_mul x (π.2.parts_pos hx) (a2 x hx)
  constructor
  · show (π.1.parts + π.2.parts.map (fun x => 2 * x)).filter E = _
    rw [Multiset.filter_add, Multiset.filter_eq_self.mpr a1, Multiset.filter_eq_nil.mpr b2,
      add_zero]
  · show (π.1.parts + π.2.parts.map (fun x => 2 * x)).filter (fun k => ¬ E k) = _
    rw [Multiset.filter_add, Multiset.filter_eq_self.mpr b2,
      Multiset.filter_eq_nil.mpr (fun k hk => not_not.mpr (a1 k hk)), zero_add]

/-- The pair of sums that sorts the partitions of n. -/
def key (n : ℕ) (π : Nat.Partition n) : ℕ × ℕ :=
  ((π.parts.filter E).sum, (π.parts.filter (fun k => ¬ E k)).sum)

lemma key_mem (n : ℕ) (π : Nat.Partition n) : key n π ∈ Finset.HasAntidiagonal.antidiagonal n := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal]
  show (π.parts.filter E).sum + (π.parts.filter (fun k => ¬ E k)).sum = n
  rw [← Multiset.sum_add, Multiset.filter_add_not, π.parts_sum]

/-- The halves of the parts that are not admissible. -/
lemma half_facts (n : ℕ) (π : Nat.Partition n) :
    ((π.parts.filter (fun k => ¬ E k)).map (fun x => x / 2)).map (fun x => 2 * x)
      = π.parts.filter (fun k => ¬ E k) ∧
    (∀ k ∈ (π.parts.filter (fun k => ¬ E k)).map (fun x => x / 2), 0 < k ∧ E k) := by
  constructor
  · rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id (π.parts.filter (fun k => ¬ E k))]
    apply Multiset.map_congr rfl
    intro x hx
    obtain ⟨hx1, hx2⟩ := Multiset.mem_filter.mp hx
    obtain ⟨y, hy, rfl, -⟩ := of_not_E x (π.parts_pos hx1) hx2
    simp
  · intro k hk
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hk
    obtain ⟨hx1, hx2⟩ := Multiset.mem_filter.mp hx
    obtain ⟨y, hy, rfl, hE⟩ := of_not_E x (π.parts_pos hx1) hx2
    simpa using ⟨hy, hE⟩

lemma fibre_card (n : ℕ) (ij : ℕ × ℕ) (hij : ij ∈ Finset.HasAntidiagonal.antidiagonal n) :
    (Finset.univ.filter (fun π : Nat.Partition n => key n π = ij)).card
      = if Even ij.2 then (R ij.1).card * (R (ij.2 / 2)).card else 0 := by
  obtain ⟨i, j⟩ := ij
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  simp only at hij ⊢
  split_ifs with hj
  · obtain ⟨t, ht⟩ := hj
    have ht2 : j / 2 = t := by omega
    rw [ht2, ← Finset.card_product]
    have hn : i + 2 * t = n := by omega
    symm
    apply Finset.card_bij (fun π _ => join i t n hn π)
    · intro π hπ
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hπ
      obtain ⟨f1, f2⟩ := filter_join i t n hn π h1 h2
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      unfold key
      rw [f1, f2, Multiset.sum_map_mul_left, π.1.parts_sum]
      simp [π.2.parts_sum]
      omega
    · intro π hπ π' hπ' heq
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hπ
      obtain ⟨h1', h2'⟩ := Finset.mem_product.mp hπ'
      obtain ⟨f1, f2⟩ := filter_join i t n hn π h1 h2
      obtain ⟨f1', f2'⟩ := filter_join i t n hn π' h1' h2'
      rw [heq] at f1 f2
      have e1 : π.1.parts = π'.1.parts := by rw [← f1, ← f1']
      have e2 : π.2.parts.map (fun x => 2 * x) = π'.2.parts.map (fun x => 2 * x) := by
        rw [← f2, ← f2']
      have e2' : π.2.parts = π'.2.parts :=
        Multiset.map_injective (fun x y hxy => by simpa using hxy) e2
      exact Prod.ext (Nat.Partition.ext e1) (Nat.Partition.ext e2')
    · intro π hπ
      have hk : key n π = (i, j) := (Finset.mem_filter.mp hπ).2
      obtain ⟨g1, g2⟩ := half_facts n π
      have hs1 : (π.parts.filter E).sum = i := congrArg Prod.fst hk
      have hs2 : (π.parts.filter (fun k => ¬ E k)).sum = j := congrArg Prod.snd hk
      have hs3 : ((π.parts.filter (fun k => ¬ E k)).map (fun x => x / 2)).sum = t := by
        have : 2 * ((π.parts.filter (fun k => ¬ E k)).map (fun x => x / 2)).sum = j := by
          have h := congrArg Multiset.sum g1
          rw [Multiset.sum_map_mul_left, hs2] at h
          simpa using h
        omega
      refine ⟨(⟨π.parts.filter E, fun hk => π.parts_pos (Multiset.mem_filter.mp hk).1, hs1⟩,
        ⟨(π.parts.filter (fun k => ¬ E k)).map (fun x => x / 2), fun hk => (g2 _ hk).1, hs3⟩),
        ?_, ?_⟩
      · rw [Finset.mem_product]
        constructor
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun k hk => (Multiset.mem_filter.mp hk).2⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun k hk => (g2 k hk).2⟩
      · apply Nat.Partition.ext
        show π.parts.filter E + ((π.parts.filter (fun k => ¬ E k)).map (fun x => x / 2)).map
          (fun x => 2 * x) = π.parts
        rw [g1, Multiset.filter_add_not]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro π _ hk
    apply hj
    have hs2 : (π.parts.filter (fun k => ¬ E k)).sum = j := congrArg Prod.snd hk
    obtain ⟨g1, -⟩ := half_facts n π
    rw [← hs2, ← g1, Multiset.sum_map_mul_left]
    exact even_two_mul _

/-- The restricted partition numbers have the defining property. -/
lemma conv_R (n : ℕ) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, if Even ij.2 then (R ij.1).card * (R (ij.2 / 2)).card else 0)
    = Fintype.card (Nat.Partition n) := by
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := key n)
    (t := Finset.HasAntidiagonal.antidiagonal n) (fun π _ => key_mem n π)]
  exact (Finset.sum_congr rfl (fun ij hij => fibre_card n ij hij)).symm

/-- Split the convolution: the term with j = 0 and the rest. -/
lemma conv_split (f : ℕ → ℕ) (n : ℕ) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, if Even ij.2 then f ij.1 * f (ij.2 / 2) else 0)
    = (∑ k ∈ Finset.range n, if Even (n - k) then f k * f ((n - k) / 2) else 0) + f n * f 0 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
  simp

theorem main' : ∀ a : ℕ → ℕ, IsA a → ∀ n : ℕ, a n = euler n := by
  intro a ha n
  rw [euler_eq]
  have h0 : ∀ f : ℕ → ℕ, (∀ n, (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      if Even ij.2 then f ij.1 * f (ij.2 / 2) else 0) = Fintype.card (Nat.Partition n)) →
      f 0 = 1 := by
    intro f hf
    have h := hf 0
    have hc : Fintype.card (Nat.Partition 0) = 1 := by
      rw [Fintype.card_eq_one_iff]
      exact ⟨default, fun π => Subsingleton.elim _ _⟩
    rw [hc] at h
    simp at h
    exact h
  have a0 := h0 a ha
  have c0 := h0 (fun n => (R n).card) conv_R
  beta_reduce at c0
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [a0, c0]
    · have e1 := ha n
      have e2 := conv_R n
      rw [conv_split a n, a0] at e1
      rw [conv_split (fun n => (R n).card) n] at e2
      rw [c0] at e2
      have hrest : (∑ k ∈ Finset.range n, if Even (n - k) then a k * a ((n - k) / 2) else 0)
          = ∑ k ∈ Finset.range n,
            if Even (n - k) then (R k).card * (R ((n - k) / 2)).card else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        rw [ih k hk', ih ((n - k) / 2) (by omega)]
      rw [hrest] at e1
      omega

end OMA.A174065

theorem OMA.solution : type_of% @OMA.S_oeis_a174065.main :=
  OMA.A174065.main'
