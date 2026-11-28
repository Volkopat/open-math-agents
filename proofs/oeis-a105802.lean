import OMAStatements.S_oeis_a105802

-- Problem: A105802: Smallest m such that the m-th Fibonacci number has exactly n divisors that are also Fibonacci numbers.
-- Upstream: formal-conjectures statements/oeis-a105802.lean:0 (declaration OMA.S_oeis_a105802.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: k = 5 is a counterexample to the first claim. The Fibonacci numbers dividing F(60) are
-- F(j) for j = 1, 3, 4, 5, 6, 10, 12, 15, 20, 30, 60 (F(2) = F(1) = 1), eleven numbers, so
-- a(11) <= 60; but 3*2^(Prime[4]-1) = 3*2^6 = 192.

open OMA.S_oeis_a105802 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a105802.main) := by
  intro H
  have hS : {d : ℕ | d ∣ Nat.fib 60 ∧ ∃ j, Nat.fib j = d} =
      ↑({1, 2, 3, 5, 8, 55, 144, 610, 6765, 832040, 1548008755920} : Finset ℕ) := by
    ext d
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hd, j, rfl⟩
      have hj : j ≤ 60 := by
        by_contra hlt
        have h1 : Nat.fib 61 ≤ Nat.fib j := Nat.fib_mono (by omega)
        have h2 : Nat.fib j ≤ Nat.fib 60 := Nat.le_of_dvd (by norm_num) hd
        have h3 : Nat.fib 60 < Nat.fib 61 := Nat.fib_lt_fib_succ (by norm_num)
        omega
      rw [Nat.dvd_iff_mod_eq_zero] at hd
      revert hd
      interval_cases j <;> norm_num
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      exacts [⟨Nat.dvd_of_mod_eq_zero (by norm_num), 1, by norm_num⟩,
        ⟨Nat.dvd_of_mod_eq_zero (by norm_num), 3, by norm_num⟩,
        ⟨Nat.dvd_of_mod_eq_zero (by norm_num), 4, by norm_num⟩,
        ⟨Nat.dvd_of_mod_eq_zero (by norm_num), 5, by norm_num⟩,
        ⟨Nat.dvd_of_mod_eq_zero (by norm_num), 6, by norm_num⟩,
        ⟨Nat.dvd_of_mod_eq_zero (by norm_num), 10, by norm_num⟩,
        ⟨Nat.dvd_of_mod_eq_zero (by norm_num), 12, by norm_num⟩,
        ⟨Nat.dvd_of_mod_eq_zero (by norm_num), 15, by norm_num⟩,
        ⟨Nat.dvd_of_mod_eq_zero (by norm_num), 20, by norm_num⟩,
        ⟨Nat.dvd_of_mod_eq_zero (by norm_num), 30, by norm_num⟩,
        ⟨Nat.dvd_of_mod_eq_zero (by norm_num), 60, by norm_num⟩]
  have hc : c 60 = 11 := by
    rw [c, hS, Set.ncard_coe_finset]
    decide
  have hle : a 11 ≤ 60 := by
    show sInf {m : ℕ | 1 ≤ m ∧ c m = 11} ≤ 60
    apply Nat.sInf_le
    rw [Set.mem_ofPred_eq]
    exact ⟨by norm_num, hc⟩
  have h5 := H.1 5 (by norm_num)
  rw [show (5 : ℕ) - 2 = 3 from rfl, Nat.nth_prime_three_eq_seven] at h5
  norm_num at h5
  omega
