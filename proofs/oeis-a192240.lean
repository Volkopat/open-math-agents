import OMAStatements.S_oeis_a192240

open Polynomial

private lemma monic_fib_poly : (X ^ 2 - X - 1 : ℤ[X]).Monic := by
  have h : (X ^ 2 - X - 1 : ℤ[X]) = X ^ 2 - (X + 1) := by ring
  rw [h]
  apply Polynomial.Monic.sub_of_left (Polynomial.monic_X_pow 2)
  have h1 : (X + 1 : ℤ[X]).degree ≤ 1 := by
    calc (X + 1 : ℤ[X]).degree ≤ max (X : ℤ[X]).degree (1 : ℤ[X]).degree := degree_add_le _ _
      _ ≤ 1 := by simp [degree_X]
  have h2 : (X ^ 2 : ℤ[X]).degree = 2 := by simp [degree_X_pow]
  rw [h2]
  exact lt_of_le_of_lt h1 (by decide)

private lemma degree_fib_poly : (X ^ 2 - X - 1 : ℤ[X]).degree = 2 := by
  have h : (X ^ 2 - X - 1 : ℤ[X]) = X ^ 2 - (X + 1) := by ring
  rw [h, degree_sub_eq_left_of_degree_lt]
  · simp [degree_X_pow]
  · have h1 : (X + 1 : ℤ[X]).degree ≤ 1 := by
      calc (X + 1 : ℤ[X]).degree ≤ max (X : ℤ[X]).degree (1 : ℤ[X]).degree := degree_add_le _ _
        _ ≤ 1 := by simp [degree_X]
    have h2 : (X ^ 2 : ℤ[X]).degree = 2 := by simp [degree_X_pow]
    rw [h2]
    exact lt_of_le_of_lt h1 (by decide)

private lemma degree_linear_lt_two (c0 c1 : ℤ) :
    (C c0 + C c1 * X : ℤ[X]).degree < 2 := by
  have h1 : (C c0 : ℤ[X]).degree ≤ 0 := degree_C_le
  have h2 : (C c1 * X : ℤ[X]).degree ≤ 1 := by
    calc (C c1 * X : ℤ[X]).degree ≤ (C c1 : ℤ[X]).degree + (X : ℤ[X]).degree := degree_mul_le _ _
      _ ≤ 0 + 1 := add_le_add degree_C_le (by simp [degree_X])
      _ = 1 := by norm_num
  have h3 : (C c0 + C c1 * X : ℤ[X]).degree ≤ 1 := by
    calc (C c0 + C c1 * X : ℤ[X]).degree
        ≤ max (C c0 : ℤ[X]).degree (C c1 * X : ℤ[X]).degree := degree_add_le _ _
      _ ≤ 1 := max_le (le_trans h1 (by decide)) h2
  exact lt_of_le_of_lt h3 (by decide)

private lemma dvd_X_sub_one_pow (i : ℕ) :
    (X ^ 2 - X - 1 : ℤ[X]) ∣
      (X - 1 : ℤ[X]) ^ i -
        (C ((-1 : ℤ) ^ i * (Nat.fib (i + 1) : ℤ)) +
          C ((-1 : ℤ) ^ (i + 1) * (Nat.fib i : ℤ)) * X) := by
  induction i with
  | zero =>
    simp [Nat.fib]
  | succ i ih =>
    rcases ih with ⟨q, hq⟩
    refine ⟨q * (X - 1) + C ((-1 : ℤ) ^ (i + 1) * (Nat.fib i : ℤ)), ?_⟩
    have hpow : (X - 1 : ℤ[X]) ^ (i + 1) = (X - 1 : ℤ[X]) ^ i * (X - 1) := pow_succ _ _
    have hsub : (X - 1 : ℤ[X]) ^ i =
        (X ^ 2 - X - 1 : ℤ[X]) * q +
          (C ((-1 : ℤ) ^ i * (Nat.fib (i + 1) : ℤ)) +
            C ((-1 : ℤ) ^ (i + 1) * (Nat.fib i : ℤ)) * X) := by
      linear_combination hq
    have hfib : (Nat.fib (i + 2) : ℤ) = (Nat.fib i : ℤ) + (Nat.fib (i + 1) : ℤ) := by
      exact_mod_cast Nat.fib_add_two
    rw [hpow, hsub]
    simp only [Nat.succ_eq_add_one, hfib, map_add, map_mul, map_pow, map_neg, map_one,
      pow_succ]
    ring

theorem OMA.solution : type_of% @OMA.S_oeis_a192240.main := by
  intro n
  unfold OMA.S_oeis_a192240.a
  set d : ℤ[X] := X ^ 2 - X - 1
  set c0 : ℤ := ∑ i ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ i * (Nat.fib (i + 1) : ℤ) * (n.choose i : ℤ) * 4 ^ (n - i)
  set c1 : ℤ := ∑ i ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ (i + 1) * (Nat.fib i : ℤ) * (n.choose i : ℤ) * 4 ^ (n - i)
  have hdvd : d ∣ (X + 3 : ℤ[X]) ^ n - (C c0 + C c1 * X) := by
    have hadd : (X + 3 : ℤ[X]) = (X - 1 : ℤ[X]) + 4 := by ring
    rw [hadd, add_pow]
    have hR : C c0 + C c1 * X =
        ∑ i ∈ Finset.range (n + 1),
          (C ((-1 : ℤ) ^ i * (Nat.fib (i + 1) : ℤ)) +
            C ((-1 : ℤ) ^ (i + 1) * (Nat.fib i : ℤ)) * X) *
            (4 : ℤ[X]) ^ (n - i) * (n.choose i : ℤ[X]) := by
      simp only [c0, c1, map_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [map_mul, map_pow, map_natCast, map_neg, map_one, map_ofNat]
      ring
    rw [hR, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun i _ => ?_
    have hfactor :
        (X - 1 : ℤ[X]) ^ i * (4 : ℤ[X]) ^ (n - i) * (n.choose i : ℤ[X]) -
          (C ((-1 : ℤ) ^ i * (Nat.fib (i + 1) : ℤ)) +
            C ((-1 : ℤ) ^ (i + 1) * (Nat.fib i : ℤ)) * X) *
            (4 : ℤ[X]) ^ (n - i) * (n.choose i : ℤ[X]) =
        ((X - 1 : ℤ[X]) ^ i -
          (C ((-1 : ℤ) ^ i * (Nat.fib (i + 1) : ℤ)) +
            C ((-1 : ℤ) ^ (i + 1) * (Nat.fib i : ℤ)) * X)) *
          ((4 : ℤ[X]) ^ (n - i) * (n.choose i : ℤ[X])) := by
      ring
    rw [hfactor]
    exact dvd_mul_of_dvd_left (dvd_X_sub_one_pow i) _
  rcases hdvd with ⟨q, hq⟩
  have hmod : ((X + 3 : ℤ[X]) ^ n) %ₘ d = C c0 + C c1 * X := by
    have hsplit : (X + 3 : ℤ[X]) ^ n = (C c0 + C c1 * X) + d * q := by
      linear_combination hq
    rw [hsplit, Polynomial.add_modByMonic,
      (Polynomial.modByMonic_eq_zero_iff_dvd monic_fib_poly).2 (dvd_mul_right d q), add_zero]
    rw [Polynomial.modByMonic_eq_self_iff monic_fib_poly]
    rw [degree_fib_poly]
    exact degree_linear_lt_two c0 c1
  rw [hmod]
  simp
