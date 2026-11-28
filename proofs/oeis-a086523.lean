import OMAStatements.S_oeis_a086523

-- Problem: A086523: Beginning with 5, distinct odd primes such that the arithmetic mean of every pair of successive terms is prime.
-- Upstream: formal-conjectures statements/oeis-a086523.lean:0 (declaration OMA.S_oeis_a086523.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: 11 is a prime of the form 6k-1 that is never a term (Vim Wenders, 2008). Every term is
-- 5 mod 12 (or 0 if the search failed): if h = 5 mod 12 and p, q = (h + p)/2 are odd primes, then q
-- odd gives p = 1 mod 4, and q, p not divisible by 3 (q = 3 or p = 3 is impossible) gives
-- p = 2 mod 3; a term 0 has no successor but 0. Since 11 mod 12 = 11, 11 is not a term.

open OMA.S_oeis_a086523 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a086523.main) := by
  intro H
  have hcons : ∀ k : ℕ, ∃ y l, seq k = y :: l := by
    intro k
    cases k with
    | zero => exact ⟨5, [], rfl⟩
    | succ k => exact ⟨next (seq k), seq k, rfl⟩
  have inv : ∀ k : ℕ, ∀ x ∈ seq k, x = 0 ∨ x % 12 = 5 := by
    intro k
    induction k with
    | zero =>
      intro x hx
      have h5 : seq 0 = [5] := rfl
      rw [h5, List.mem_singleton] at hx
      subst hx
      omega
    | succ k ih =>
      intro x hx
      have hs : seq (k + 1) = next (seq k) :: seq k := rfl
      rw [hs, List.mem_cons] at hx
      rcases hx with hx | hx
      · rw [hx]
        obtain ⟨y, l, hyl⟩ := hcons k
        have hy : y = 0 ∨ y % 12 = 5 := ih y (by simp [hyl])
        have hh : (seq k).headD 0 = y := by simp [hyl]
        have key : next (seq k) = 0 ∨ ((next (seq k)).Prime ∧ Odd (next (seq k)) ∧
            ∃ q : ℕ, q.Prime ∧ 2 * q = (seq k).headD 0 + next (seq k)) := by
          unfold next
          by_cases hS : ({p : ℕ | p.Prime ∧ Odd p ∧ p ∉ seq k ∧
              ∃ q : ℕ, q.Prime ∧ 2 * q = (seq k).headD 0 + p}).Nonempty
          · obtain ⟨hp, hodd, _, q, hq, hq2⟩ := Nat.sInf_mem hS
            exact Or.inr ⟨hp, hodd, q, hq, hq2⟩
          · exact Or.inl (Nat.sInf_eq_zero.mpr (Or.inr (Set.not_nonempty_iff_eq_empty.mp hS)))
        obtain ⟨s, hsdef⟩ : ∃ s, s = next (seq k) := ⟨_, rfl⟩
        rw [← hsdef] at key ⊢
        rcases key with h0 | ⟨hp, hodd, q, hq, hq2⟩
        · exact Or.inl h0
        · right
          have hs2 := hp.two_le
          obtain ⟨c, hc⟩ := hodd
          have hq2' := hq.eq_two_or_odd
          have hq3 : q = 3 ∨ q % 3 ≠ 0 := by
            by_cases h3 : 3 ∣ q
            · have h3' := hq.eq_one_or_self_of_dvd 3 h3
              omega
            · omega
          have hs3 : s = 3 ∨ s % 3 ≠ 0 := by
            by_cases h3 : 3 ∣ s
            · have h3' := hp.eq_one_or_self_of_dvd 3 h3
              omega
            · omega
          omega
      · exact ih x hx
  obtain ⟨n, _, han⟩ := H 11 (by norm_num) (by norm_num)
  obtain ⟨y, l, hyl⟩ := hcons (n - 1)
  have hmem : a n ∈ seq (n - 1) := by
    unfold a
    simp [hyl]
  have h := inv (n - 1) (a n) hmem
  omega
