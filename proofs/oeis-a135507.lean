import OMAStatements.S_oeis_a135507
import Mathlib

/-!
# A135507: McEachen's conjecture holds for every prime

The hypothesis on A135507 is not needed: every prime p is a term of A140460 or equals 2 plus a
term. First, k is in below m exactly when k < m and k is a term. A prime p is never a multiple
of an earlier term, since those terms are at least 2 and less than p. So if p is not a term,
then p = i + j with i < j earlier terms. For p = 2 this cannot happen, and for odd p one of
i, j is even. The only even term is 2, because 2 is a term and every larger even number is a
multiple of it. Hence p = 2 + j with j a term, and j = A140460(m) with m the number of terms
below j.
-/

namespace OMA.P135507

open OMA.S_oeis_a135507

theorem below_succ (m : ℕ) : below (m + 1) =
    if 2 ≤ m ∧ (∀ k ∈ below m, ¬ k ∣ m) ∧
        ¬ ∃ i ∈ below m, ∃ j ∈ below m, i < j ∧ i + j = m then
      below m ++ [m]
    else below m := by
  rfl

theorem lt_of_mem : ∀ m k, k ∈ below m → k < m := by
  intro m
  induction m with
  | zero => intro k hk; simp [below] at hk
  | succ m ih =>
    intro k hk
    rw [below_succ] at hk
    split_ifs at hk with h
    · rcases List.mem_append.1 hk with hk | hk
      · exact Nat.lt_succ_of_lt (ih k hk)
      · simp at hk; omega
    · exact Nat.lt_succ_of_lt (ih k hk)

theorem insieve_iff (k : ℕ) : InSieve k ↔ (2 ≤ k ∧ (∀ d ∈ below k, ¬ d ∣ k) ∧
    ¬ ∃ i ∈ below k, ∃ j ∈ below k, i < j ∧ i + j = k) := by
  unfold InSieve
  rw [below_succ]
  split_ifs with h
  · simp only [List.mem_append, List.mem_singleton, or_true, true_iff]
    exact h
  · simp only [h, iff_false]
    intro hk
    exact absurd (lt_of_mem k k hk) (lt_irrefl k)

theorem mem_below_iff : ∀ m k, k < m → (k ∈ below m ↔ InSieve k) := by
  intro m
  induction m with
  | zero => intro k hk; omega
  | succ m ih =>
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | hk'
    · rw [below_succ]
      split_ifs with h
      · rw [List.mem_append, ih k hk']
        simp only [List.mem_singleton]
        constructor
        · rintro (h1 | h1)
          · exact h1
          · omega
        · intro h1; exact Or.inl h1
      · exact ih k hk'
    · subst hk'
      rfl

theorem two_le_of_mem {m k : ℕ} (hk : k ∈ below m) : 2 ≤ k :=
  ((insieve_iff k).1 ((mem_below_iff m k (lt_of_mem m k hk)).1 hk)).1

theorem insieve_two : InSieve 2 := by
  rw [insieve_iff]
  refine ⟨le_refl 2, ?_, ?_⟩
  · intro d hd; exact absurd (lt_of_mem 2 d hd) (by have := two_le_of_mem hd; omega)
  · rintro ⟨i, hi, -⟩; exact absurd (lt_of_mem 2 i hi) (by have := two_le_of_mem hi; omega)

theorem exists_nth {q : ℕ} (hq : InSieve q) : ∃ m, b m = q := by
  classical
  exact ⟨Nat.count InSieve q, Nat.nth_count hq⟩

theorem even_eq_two {e : ℕ} (he : InSieve e) (h2 : 2 ∣ e) : e = 2 := by
  by_contra hne
  have h2e : 2 ≤ e := ((insieve_iff e).1 he).1
  have hlt : 2 < e := lt_of_le_of_ne h2e (Ne.symm hne)
  have hmem : 2 ∈ below e := (mem_below_iff e 2 hlt).2 insieve_two
  exact ((insieve_iff e).1 he).2.1 2 hmem h2

theorem prime_case (p : ℕ) (hp : p.Prime) : ∃ m : ℕ, p = b m ∨ p = b m + 2 := by
  by_cases hs : InSieve p
  · obtain ⟨m, hm⟩ := exists_nth hs
    exact ⟨m, Or.inl hm.symm⟩
  · have h2 : 2 ≤ p := hp.two_le
    rw [insieve_iff] at hs
    simp only [not_and, not_not] at hs
    have hdiv : ∀ d ∈ below p, ¬ d ∣ p := by
      intro d hd hdp
      rcases (Nat.dvd_prime hp).1 hdp with h | h
      · have := two_le_of_mem hd; omega
      · have := lt_of_mem p d hd; omega
    obtain ⟨i, hi, j, hj, hij, hsum⟩ := hs h2 hdiv
    have hi' := (mem_below_iff p i (lt_of_mem p i hi)).1 hi
    have hj' := (mem_below_iff p j (lt_of_mem p j hj)).1 hj
    have hi2 := two_le_of_mem hi
    have hodd : ¬ 2 ∣ p := by
      intro h
      rcases (Nat.dvd_prime hp).1 h with h | h
      · omega
      · omega
    by_cases hie : 2 ∣ i
    · have := even_eq_two hi' hie
      obtain ⟨m, hm⟩ := exists_nth hj'
      exact ⟨m, Or.inr (by omega)⟩
    · have hje : 2 ∣ j := by omega
      have := even_eq_two hj' hje
      omega

end OMA.P135507

open OMA.P135507 in
theorem OMA.solution : type_of% @OMA.S_oeis_a135507.main := by
  intro n _ p _ hp
  exact prime_case p hp

