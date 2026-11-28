import FormalConjectures.Wikipedia.ThabitNumber

/-! Direct polynomial proof of Thābit ibn Qurra's amicable number rule via `2 ^ (n - 1) = u + 2`. -/

open ArithmeticFunction ThabitNumber

theorem OMA.solution : type_of% @ThabitNumber.thabit_amicable_rule := by
  intro n hn hp hq hr
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 2 ≤ 2 ^ m := Nat.pow_le_pow_right zero_lt_two (i := 1) (by omega)
  obtain ⟨u, hu⟩ : ∃ u, 2 ^ m = u + 2 := ⟨2 ^ m - 2, by omega⟩
  have h1 : 2 ^ (m + 1) = 2 * u + 4 := by rw [pow_succ', hu]; ring
  have h2 : 9 * 2 ^ (2 * (m + 1) - 1) - 1 = 18 * u ^ 2 + 72 * u + 71 := by
    rw [show 2 * (m + 1) - 1 = m + 1 + m by omega, pow_add, h1, hu,
      show 9 * ((2 * u + 4) * (u + 2)) = 18 * u ^ 2 + 72 * u + 71 + 1 by ring,
      Nat.add_sub_cancel]
  have hp' : thabitNumber (m + 1 - 1) = 3 * u + 5 := by simp [thabitNumber, hu]; omega
  have hq' : thabitNumber (m + 1) = 6 * u + 11 := by simp [thabitNumber, h1]; omega
  have sm {a x : ℕ} (hx : x.Prime) (h : a.Coprime x) :
      sigma 1 (a * x) = sigma 1 a * (x + 1) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime h, sigma_one_apply x, hx.sum_divisors]
  have cop {x : ℕ} (hx : x.Prime) (h : 2 < x) : (2 ^ (m + 1)).Coprime x :=
    ((Nat.coprime_primes Nat.prime_two hx).2 (by omega)).pow_left _
  have hs : sigma 1 (2 ^ (m + 1)) = 4 * u + 7 := by
    rw [sigma_one_apply_prime_pow Nat.prime_two, Nat.geomSum_eq le_rfl, pow_succ', h1]
    omega
  rw [hp'] at hp ⊢; rw [hq'] at hq ⊢; rw [h2] at hr ⊢
  refine ⟨?_, ?_, fun h => ?_⟩
  · rw [sm hq ((cop hq (by omega)).mul_left ((Nat.coprime_primes hp hq).2 (by omega))),
      sm hp (cop hp (by omega)), hs, h1]
    ring
  · rw [sm hr (cop hr (by omega)), hs, h1]
    ring
  · rw [h1, mul_assoc] at h
    have := Nat.eq_of_mul_eq_mul_left (by positivity) h
    nlinarith
