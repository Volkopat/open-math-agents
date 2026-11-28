import OMAStatements.S_oeis_a249760

-- Problem: A249760, conjectures (2) and (3). If k + 1 is prime and sigma(k) is prime: k is even
-- (k = 1 fails), write k = 2^e r with r odd; sigma(k) = sigma(2^e) sigma(r) is prime and sigma(2^e) >= 3,
-- so r = 1. Then 2^e + 1 prime forces e = 2^m (Fermat), and sigma(2^e) = 2^(e+1) - 1 is a Mersenne number.

theorem OMA.solution : type_of% @OMA.S_oeis_a249760.main := by
  intro k hk hs
  have hg : ∀ e : ℕ, ∑ k ∈ Finset.range (e + 1), 2 ^ k + 1 = 2 ^ (e + 1) := by
    intro e
    induction e with
    | zero => simp
    | succ e ih => rw [Finset.sum_range_succ, add_right_comm, ih]; ring
  have hk0 : k ≠ 0 := by rintro rfl; exact Nat.not_prime_zero (by simpa using hs)
  obtain ⟨e, r, hr, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hk0
  have hcop : Nat.Coprime (2 ^ e) r := Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hr)
  have hmul : ArithmeticFunction.sigma 1 (2 ^ e * r)
      = ArithmeticFunction.sigma 1 (2 ^ e) * ArithmeticFunction.sigma 1 r :=
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
  have h2e : ArithmeticFunction.sigma 1 (2 ^ e) + 1 = 2 ^ (e + 1) := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]; exact hg e
  have he : e ≠ 0 := by
    rintro rfl
    simp only [pow_zero, one_mul] at hk hs
    have h2 := hk.even_iff.mp hr.add_one
    have hr1 : r = 1 := by omega
    subst hr1
    exact Nat.not_prime_one (by simpa using hs)
  have hr1 : r = 1 := by
    by_contra hne
    rw [hmul, Nat.prime_mul_iff] at hs
    rcases hs with ⟨_, h⟩ | ⟨_, h⟩
    · have hsub : ({1, r} : Finset ℕ) ⊆ r.divisors := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp [hr.pos.ne']
      have hle := Finset.sum_le_sum_of_subset (f := fun d => d) hsub
      rw [Finset.sum_pair (Ne.symm hne), ← ArithmeticFunction.sigma_one_apply, h] at hle
      have := hr.pos
      omega
    · have h4 : 1 < 2 ^ e := Nat.one_lt_two_pow he
      rw [pow_succ, h] at h2e
      omega
  subst hr1
  simp only [mul_one] at hk hs ⊢
  constructor
  · obtain ⟨m, hm⟩ := Nat.pow_of_pow_add_prime (by norm_num) he hk
    exact ⟨m, by rw [hm]; rfl⟩
  · exact ⟨e + 1, by unfold mersenne; omega⟩
