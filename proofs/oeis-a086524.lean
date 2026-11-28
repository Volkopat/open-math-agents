import OMAStatements.S_oeis_a086524

namespace OMA.S_oeis_a086524




lemma a_succ (n : ℕ) : a (n + 1) = (terms n).getLast?.getD 0 := by simp [a]

lemma a_one : a 1 = 5 := by simp [a, terms]

lemma a_succ_succ (n : ℕ) : a (n + 2) = next (terms n) := by
  rw [a_succ]
  simp [terms]

lemma five_mem (n : ℕ) : 5 ∈ terms n := by
  induction n with
  | zero => simp [terms]
  | succ n ih => simp [terms, ih]

lemma last_mem (n : ℕ) : a (n + 1) ∈ terms n := by
  rw [a_succ]
  cases n with
  | zero => simp [terms]
  | succ n => simp [terms]

/-- A nonzero greedy choice is a new odd prime whose mean with the previous term is prime. -/
lemma next_spec {L : List ℕ} (h : next L ≠ 0) :
    (next L).Prime ∧ next L ≠ 2 ∧ next L ∉ L ∧
      ∃ m, m.Prime ∧ L.getLast?.getD 0 + next L = 2 * m := by
  by_cases hS : {q | q.Prime ∧ q ≠ 2 ∧ q ∉ L ∧ ∃ m, m.Prime ∧ L.getLast?.getD 0 + q = 2 * m}.Nonempty
  · exact Nat.sInf_mem hS
  · exfalso
    apply h
    rw [Set.not_nonempty_iff_eq_empty] at hS
    rw [next, hS, Nat.sInf_empty]

/-- Every term is 0 (if the greedy rule ever got stuck) or a prime == 5 (mod 12). -/
lemma inv (n : ℕ) : a (n + 1) = 0 ∨ ((a (n + 1)).Prime ∧ a (n + 1) % 12 = 5) := by
  induction n with
  | zero => right; rw [a_one]; norm_num
  | succ n ih =>
    rw [a_succ_succ]
    by_cases h0 : next (terms n) = 0
    · left; exact h0
    · right
      obtain ⟨hq, hq2, _, m, hm, he⟩ := next_spec h0
      rw [← a_succ] at he
      refine ⟨hq, ?_⟩
      have hqodd : next (terms n) % 2 = 1 := (hq.eq_two_or_odd).resolve_left hq2
      have hq3 : next (terms n) = 3 ∨ next (terms n) % 3 ≠ 0 := by
        rcases eq_or_ne (next (terms n) % 3) 0 with h | h
        · left
          have := (Nat.Prime.eq_one_or_self_of_dvd hq 3 (Nat.dvd_of_mod_eq_zero h))
          omega
        · right; exact h
      have hm3 : m = 3 ∨ m % 3 ≠ 0 := by
        rcases eq_or_ne (m % 3) 0 with h | h
        · left
          have := (Nat.Prime.eq_one_or_self_of_dvd hm 3 (Nat.dvd_of_mod_eq_zero h))
          omega
        · right; exact h
      have hm2 : m = 2 ∨ m % 2 = 1 := hm.eq_two_or_odd
      have hqge := hq.two_le
      rcases ih with h | ⟨_, h5⟩
      · rw [h] at he
        omega
      · omega

lemma a_two : a 2 = 17 := by
  rw [show (2 : ℕ) = 0 + 2 from rfl, a_succ_succ]
  have hS : 17 ∈ {q | q.Prime ∧ q ≠ 2 ∧ q ∉ terms 0 ∧
      ∃ m, m.Prime ∧ (terms 0).getLast?.getD 0 + q = 2 * m} := by
    refine ⟨by norm_num, by norm_num, by simp [terms], 11, by norm_num, by simp [terms]⟩
  apply le_antisymm (Nat.sInf_le hS)
  apply le_csInf ⟨17, hS⟩
  rintro q ⟨hp, h2, h5, m, hm, he⟩
  simp only [terms, List.getLast?_singleton, Option.getD_some, List.mem_singleton] at he h5
  by_contra hlt
  push_neg at hlt
  have hmq : m = (5 + q) / 2 := by omega
  rw [hmq] at hm
  clear hmq he
  interval_cases q <;> revert hp h2 h5 hm <;> decide

/-- Murthy's conjecture fails: 17 is a prime of the form 6k - 1 that is never the arithmetic mean
of two successive terms of A086523. -/
theorem disproof :
    ¬ (∀ p : ℕ, p.Prime → p % 6 = 5 → ∃ n : ℕ, 1 ≤ n ∧ a n + a (n + 1) = 2 * p) := by
  intro h
  obtain ⟨n, hn, hsum⟩ := h 17 (by norm_num) (by norm_num)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hsum' : a (k + 1) + a (k + 2) = 34 := hsum
  clear hsum
  have i1 := inv k
  have i2 : a (k + 2) = 0 ∨ ((a (k + 2)).Prime ∧ a (k + 2) % 12 = 5) := inv (k + 1)
  have hne : a (k + 2) ≠ 0 → a (k + 2) ∉ terms k := by
    intro h0
    rw [a_succ_succ] at h0 ⊢
    exact (next_spec h0).2.2.1
  rcases i1 with h1 | ⟨_, h1⟩ <;> rcases i2 with h2 | ⟨_, h2⟩
  · omega
  · omega
  · omega
  · have cases3 : (a (k + 1) = 5 ∧ a (k + 2) = 29) ∨ (a (k + 1) = 17 ∧ a (k + 2) = 17) ∨
        (a (k + 1) = 29 ∧ a (k + 2) = 5) := by omega
    rcases cases3 with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [a_two] at e2
        omega
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have hnot : a (j + 2) ∉ terms j := by
          rw [a_succ_succ] at e1 ⊢
          exact (next_spec (by omega)).2.2.1
        rw [show j + 1 + 1 = j + 2 by omega] at e1
        rw [e1] at hnot
        exact hnot (five_mem j)
    · have hnot := hne (by omega)
      rw [e2, ← e1] at hnot
      exact hnot (last_mem k)
    · have hnot := hne (by omega)
      rw [e2] at hnot
      exact hnot (five_mem k)

end OMA.S_oeis_a086524

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a086524.main) :=
  OMA.S_oeis_a086524.disproof
