import OMAStatements.S_oeis_a258454

/-!
# A258454: the conjecture "a prime p has φ(p) = 2 φ(p-2) iff p is a Fermat prime" is false

Counterexample: p = 83623937, which is prime and not of the form 2^(2^k) + 1, while
p - 2 = 83623935 = 3 · 5 · 17 · 353 · 929 has φ(p - 2) = 2 · 4 · 16 · 352 · 928 = 41811968 = (p - 1) / 2.
(83623935 is the known sixth solution of 2 φ(m) = m + 1, OEIS A050474.)
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a258454.main) := by
  intro h
  have hp : Nat.Prime 83623937 := by norm_num
  have ht : Nat.totient (83623937 - 2) = 41811968 := by
    have e : (83623937 - 2 : ℕ) = 3 * (5 * (17 * (353 * 929))) := by norm_num
    rw [e, Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num),
      Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num),
      Nat.totient_prime (by norm_num)]
  obtain ⟨k, hk⟩ := (h 83623937 hp).mp (by rw [Nat.totient_prime hp, ht])
  rcases Nat.lt_or_ge k 5 with hlt | hge
  · interval_cases k <;> omega
  · have h1 : 2 ^ 2 ^ 5 ≤ 2 ^ 2 ^ k :=
      Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hge)
    norm_num at h1
    omega
