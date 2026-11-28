import FormalConjectures.Wikipedia.ThabitNumber

/-!
# Thābit ibn Qurra's construction of amicable numbers

We calculate the common divisor sum once for two products of primes and a power of two,
then specialize the resulting criterion to the Thābit numbers.
-/

open ArithmeticFunction ThabitNumber

private lemma sigma_mul_prime {a p : ℕ} (hp : p.Prime) (h : a.Coprime p) :
    sigma 1 (a * p) = sigma 1 a * (p + 1) := by
  rw [isMultiplicative_sigma.map_mul_of_coprime h,
    show sigma 1 p = p + 1 by rw [sigma_one_apply, hp.sum_divisors]]

/-- Both candidates have the same divisor sum. The balance condition identifies it with their sum. -/
theorem OMA.amicable_of_balance {k p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hp2 : 2 < p) (hpq : p < q) (hprod : (p + 1) * (q + 1) = r + 1)
    (hbal : 2 ^ k * ((p + 1) + (q + 1)) = r + 1) :
    IsAmicable (2 ^ k * p * q) (2 ^ k * r) := by
  have cop {x : ℕ} (hx : x.Prime) (hne : 2 ≠ x) : (2 ^ k).Coprime x :=
    ((Nat.coprime_primes Nat.prime_two hx).2 hne).pow_left k
  have hs : sigma 1 (2 ^ k) + 1 = 2 * 2 ^ k := by
    rw [sigma_one_apply_prime_pow Nat.prime_two]
    simpa [pow_succ'] using geom_sum_mul_add (1 : ℕ) (k + 1)
  have he : p * q + p + q = r := by nlinarith only [hprod]
  have total : sigma 1 (2 ^ k) * (r + 1) = 2 ^ k * p * q + 2 ^ k * r := by
    nlinarith only [congrArg (fun a : ℕ => a * (r + 1)) hs,
      congrArg (fun a : ℕ => 2 ^ k * a) he, hbal]
  refine ⟨?_, ?_, ?_⟩
  · rw [sigma_mul_prime hq ((cop hq (by omega)).mul_left ((Nat.coprime_primes hp hq).2 hpq.ne)),
      sigma_mul_prime hp (cop hp (by omega)), mul_assoc, hprod]
    exact total
  · rw [sigma_mul_prime hr (cop hr (by omega))]
    exact total
  · rw [mul_assoc]
    exact (Nat.mul_lt_mul_of_pos_left (by omega : p * q < r) (by positivity)).ne

theorem OMA.solution : type_of% @ThabitNumber.thabit_amicable_rule := by
  intro n hn hp hq hr
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let t : ℕ := 2 ^ m
  have ht : 2 ≤ t := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ m)
  have hn' : 2 ^ (m + 1) = 2 * t := pow_succ' 2 m
  have he : 2 ^ (2 * (m + 1) - 1) = (2 * t) * t := by
    rw [show 2 * (m + 1) - 1 = (m + 1) + m by omega, pow_add, hn']
  have hP : thabitNumber (m + 1 - 1) + 1 = 3 * t := by
    simp only [Nat.add_sub_cancel, thabitNumber]
    change 3 * t - 1 + 1 = 3 * t
    omega
  have hQ : thabitNumber (m + 1) + 1 = 6 * t := by
    rw [thabitNumber, hn']
    omega
  have hR : 9 * 2 ^ (2 * (m + 1) - 1) - 1 + 1 = 18 * (t * t) := by
    rw [he, Nat.sub_add_cancel (Nat.succ_le_of_lt (by positivity))]
    ring
  apply OMA.amicable_of_balance hp hq hr (by omega) (by omega)
  · rw [hP, hQ, hR]
    ring
  · rw [hP, hQ, hR, hn']
    ring
