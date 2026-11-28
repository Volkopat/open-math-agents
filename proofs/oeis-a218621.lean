import OMAStatements.S_oeis_a218621

-- Problem: A218621: a(n) = unique divisor d of n such that d + (n/d - 1)/2 is minimal and integral.
-- Upstream: formal-conjectures statements/oeis-a218621.lean:0 (declaration OMA.S_oeis_a218621.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: n = 81 is a counterexample to condition 2. The divisors of 81 = 3^4 are 1, 3, 9, 27, 81,
-- all with odd cofactor, and their values d + (81/d - 1)/2 are 41, 16, 13, 28, 81, so a(81) = 9
-- (as in the entry's data). But 81 is odd and composite, and condition 2 would make 9 an element
-- of the set of primes p dividing 81 with p * p <= 81, while 9 is not prime.

open OMA.S_oeis_a218621 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a218621.main) := by
  intro H
  have hadm : Adm 81 9 := ⟨by norm_num, ⟨13, by norm_num [val]⟩⟩
  have hmin : ∀ e : ℕ, Adm 81 e → val 81 9 ≤ val 81 e := by
    intro e he
    obtain ⟨hed, -⟩ := he
    have h3 : e ∣ 3 ^ 4 := by
      rw [show (3 : ℕ) ^ 4 = 81 by norm_num]
      exact hed
    obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h3
    interval_cases k <;> norm_num [val]
  have hA : IsA 81 9 := ⟨hadm, hmin⟩
  have hodd : Odd (81 : ℕ) := ⟨40, by norm_num⟩
  have hnp : ¬ Nat.Prime 81 := by norm_num
  have h2 := (H 81 9 (by norm_num) hA).2.1 ⟨hodd, by norm_num, hnp⟩
  have h9 : 9 ∣ 81 ∧ 9 * 9 ≤ 81 ∧ Nat.Prime 9 := h2.1
  have hn9 : ¬ Nat.Prime 9 := by norm_num
  exact hn9 h9.2.2
