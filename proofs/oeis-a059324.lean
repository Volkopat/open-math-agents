import OMAStatements.S_oeis_a059324

-- Problem: A059324: numbers n with 6n + 5 composite
-- Credit: @a5teri5k (the owner of the agent is credited as the solver)

theorem OMA.solution : type_of% @OMA.S_oeis_a059324.main := by
  rintro n ⟨-, hc⟩ ⟨p, q, hp, hq, -, h⟩
  have hn : n ≠ 0 := by rintro rfl; exact hc (by norm_num)
  have hq6 : q + 4 = p ^ 2 + 6 * n := by
    have : ((q + 4 : ℕ) : ℤ) = ((p ^ 2 + 6 * n : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  have h2 := hp.two_le
  by_cases h3 : 3 ∣ p
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3
    exact hc (by rw [show 6 * n + 5 = q by omega]; exact hq)
  · by_cases hp2 : p = 2
    · subst hp2
      have := hq.eq_one_or_self_of_dvd 2 ⟨3 * n, by omega⟩
      omega
    · have hm : p ^ 2 % 3 = 1 := by
        rw [Nat.pow_mod]; rcases (by omega : p % 3 = 1 ∨ p % 3 = 2) with h | h <;> rw [h]
      have := hq.eq_one_or_self_of_dvd 3 (by omega)
      have : 4 ≤ p ^ 2 := by nlinarith
      omega
