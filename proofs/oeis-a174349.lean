import OMAStatements.S_oeis_a174349

/-! Apart from the first gap, successive primes are strictly increasing and odd. -/

open OMA.S_oeis_a174349 in
theorem OMA.solution : type_of% @OMA.S_oeis_a174349.main := by
  intro i hi
  constructor
  · rintro ⟨n, _, _, h⟩ rfl
    norm_num [prime, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three] at h
    omega
  · intro h
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    have hm := Nat.nth_strictMono Nat.infinite_setOfPred_prime
    have odd (k : ℕ) (hk : 0 < k) : Odd (k.nth Nat.Prime) :=
      (Nat.prime_nth_prime k).odd_of_ne_two (by
        rw [← Nat.nth_prime_zero_eq_two]
        exact (hm hk).ne')
    have hlt : j.nth Nat.Prime < (j + 1).nth Nat.Prime := hm (Nat.lt_succ_self j)
    obtain ⟨d, hd⟩ := Nat.Odd.sub_odd (odd (j + 1) (by omega)) (odd j (by omega))
    refine ⟨d, by omega, hi, ?_⟩
    change (j + 1).nth Nat.Prime = j.nth Nat.Prime + 2 * d
    omega
