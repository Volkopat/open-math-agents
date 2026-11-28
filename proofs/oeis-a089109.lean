import OMAStatements.S_oeis_a089109

-- Problem: A089109: Convoluted convolved Fibonacci numbers G_5^(r).
-- Upstream: formal-conjectures statements/oeis-a089109.lean:0 (declaration OMA.S_oeis_a089109.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: a(r) = (1/r) * sum over d | r of mobius(d) * [X^4] f(X^d)^(r/d). If u * g = 1 and
-- u * p = 1 - E with X^5 | E, then X^5 | g - p, hence X^5 | g^m - p^m and [X^4] g^m = [X^4] p^m.
-- With p = 1 + X + 2X^2 + 3X^3 + 5X^4 (d = 1), 1 + X^2 + 2X^4 (d = 2), 1 + X^3 (d = 3), 1 (d >= 5)
-- the coefficients of p^m follow by induction on m: [X^4] f(X)^m = P(m) =
-- m(m+1)(m+2)(m+3)/24 + m(m+1)(m+2)/2 + m(m+1)/2, [X^4] f(X^2)^m = m(m+3)/2, and 0 for d = 3 and
-- d >= 5; mobius(4) = 0. So a(r) = P(r)/r for odd r and (P(r) - k(k+3)/2)/r for r = 2k, which is
-- the closed form. The g.f. follows by comparing coefficients: for m >= 7 the coefficient is the
-- order-6 recurrence of the closed form, and for m <= 6 it is checked from a(0) = 0, ..., a(6) = 51.

open OMA.S_oeis_a089109 in
theorem OMA.solution : type_of% @OMA.S_oeis_a089109.main := by
  -- approximation modulo X^5
  have approx : ∀ (u g p E : PowerSeries ℚ), u * g = 1 → u * p = 1 - E →
      (PowerSeries.X : PowerSeries ℚ) ^ 5 ∣ E →
      ∀ m : ℕ, PowerSeries.coeff 4 (g ^ m) = PowerSeries.coeff 4 (p ^ m) := by
    intro u g p E hug hup hE m
    have h1 : g - p = g * E := by
      have h2 : g * (u * p) = p := by rw [← mul_assoc, mul_comm g u, hug, one_mul]
      rw [hup] at h2
      linear_combination h2
    have h4 : (PowerSeries.X : PowerSeries ℚ) ^ 5 ∣ g - p := by
      rw [h1]
      exact Dvd.dvd.mul_left hE g
    have h3 : (PowerSeries.X : PowerSeries ℚ) ^ 5 ∣ g ^ m - p ^ m := dvd_trans h4 (sub_dvd_pow_sub_pow g p m)
    have h5 := PowerSeries.X_pow_dvd_iff.mp h3 4 (by norm_num)
    rw [map_sub] at h5
    exact sub_eq_zero.mp h5
  -- f d is the inverse of 1 - X^d - (X^d)^2
  have hinv : ∀ d : ℕ, 1 ≤ d →
      (1 - PowerSeries.X ^ d - (PowerSeries.X ^ d) ^ 2 : PowerSeries ℚ) * f d = 1 := by
    intro d hd
    have hd0 : d ≠ 0 := by omega
    have hc : PowerSeries.constantCoeff
        (1 - PowerSeries.X ^ d - (PowerSeries.X ^ d) ^ 2 : PowerSeries ℚ) = 1 := by
      simp only [map_sub, map_one, map_pow, PowerSeries.constantCoeff_X, zero_pow hd0]
      norm_num
    show (1 - PowerSeries.X ^ d - (PowerSeries.X ^ d) ^ 2 : PowerSeries ℚ) *
      (1 - PowerSeries.X ^ d - (PowerSeries.X ^ d) ^ 2)⁻¹ = 1
    exact PowerSeries.mul_inv_cancel _ (by rw [hc]; exact one_ne_zero)
  -- d = 1: p1 = 1 + X + 2X^2 + 3X^3 + 5X^4
  obtain ⟨p1, hp1⟩ : ∃ p : PowerSeries ℚ, p = 1 + PowerSeries.X + 2 * PowerSeries.X ^ 2 +
      3 * PowerSeries.X ^ 3 + 5 * PowerSeries.X ^ 4 := ⟨_, rfl⟩
  have mul1 : ∀ q : PowerSeries ℚ, q * p1 = q + q * PowerSeries.X ^ 1 +
      (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 * (q * PowerSeries.X ^ 2) +
      (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3 * (q * PowerSeries.X ^ 3) +
      (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5 * (q * PowerSeries.X ^ 4) := by
    intro q
    rw [hp1, map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5]
    ring
  have L1 : ∀ (q : PowerSeries ℚ) (k : ℕ), PowerSeries.coeff k (q * p1) =
      PowerSeries.coeff k q + (if 1 ≤ k then PowerSeries.coeff (k - 1) q else 0) +
      2 * (if 2 ≤ k then PowerSeries.coeff (k - 2) q else 0) +
      3 * (if 3 ≤ k then PowerSeries.coeff (k - 3) q else 0) +
      5 * (if 4 ≤ k then PowerSeries.coeff (k - 4) q else 0) := by
    intro q k
    rw [mul1]
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow']
  have L1v : ∀ q : PowerSeries ℚ,
      PowerSeries.coeff 0 (q * p1) = PowerSeries.coeff 0 q ∧
      PowerSeries.coeff 1 (q * p1) = PowerSeries.coeff 1 q + PowerSeries.coeff 0 q ∧
      PowerSeries.coeff 2 (q * p1) = PowerSeries.coeff 2 q + PowerSeries.coeff 1 q +
        2 * PowerSeries.coeff 0 q ∧
      PowerSeries.coeff 3 (q * p1) = PowerSeries.coeff 3 q + PowerSeries.coeff 2 q +
        2 * PowerSeries.coeff 1 q + 3 * PowerSeries.coeff 0 q ∧
      PowerSeries.coeff 4 (q * p1) = PowerSeries.coeff 4 q + PowerSeries.coeff 3 q +
        2 * PowerSeries.coeff 2 q + 3 * PowerSeries.coeff 1 q + 5 * PowerSeries.coeff 0 q := by
    intro q
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [L1 q 0]
      norm_num
    · rw [L1 q 1]
      norm_num
    · rw [L1 q 2]
      norm_num
    · rw [L1 q 3]
      norm_num
    · rw [L1 q 4]
      norm_num
  have C1 : ∀ m : ℕ, PowerSeries.coeff 0 (p1 ^ m) = 1 ∧ PowerSeries.coeff 1 (p1 ^ m) = m ∧
      PowerSeries.coeff 2 (p1 ^ m) = (m : ℚ) * (m + 3) / 2 ∧
      PowerSeries.coeff 3 (p1 ^ m) = (m : ℚ) * (m + 1) + m * (m + 1) * (m + 2) / 6 ∧
      PowerSeries.coeff 4 (p1 ^ m) = (m : ℚ) * (m + 1) * (m + 2) * (m + 3) / 24 +
        m * (m + 1) * (m + 2) / 2 + m * (m + 1) / 2 := by
    intro m
    induction m with
    | zero => norm_num [PowerSeries.coeff_one]
    | succ m ih =>
      obtain ⟨h0, h1, h2, h3, h4⟩ := ih
      obtain ⟨e0, e1, e2, e3, e4⟩ := L1v (p1 ^ m)
      rw [pow_succ, Nat.cast_succ]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · linear_combination e0 + h0
      · linear_combination e1 + h1 + h0
      · linear_combination e2 + h2 + h1 + 2 * h0
      · linear_combination e3 + h3 + h2 + 2 * h1 + 3 * h0
      · linear_combination e4 + h4 + h3 + 2 * h2 + 3 * h1 + 5 * h0
  have hup1 : (1 - PowerSeries.X ^ 1 - (PowerSeries.X ^ 1) ^ 2 : PowerSeries ℚ) * p1 =
      1 - (8 * PowerSeries.X ^ 5 + 5 * PowerSeries.X ^ 6) := by
    rw [hp1]
    ring
  have hE1 : (PowerSeries.X : PowerSeries ℚ) ^ 5 ∣ 8 * PowerSeries.X ^ 5 + 5 * PowerSeries.X ^ 6 :=
    ⟨8 + 5 * PowerSeries.X, by ring⟩
  have K1 : ∀ m : ℕ, PowerSeries.coeff 4 (f 1 ^ m) =
      (m : ℚ) * (m + 1) * (m + 2) * (m + 3) / 24 + m * (m + 1) * (m + 2) / 2 +
        m * (m + 1) / 2 := by
    intro m
    rw [approx _ _ _ _ (hinv 1 le_rfl) hup1 hE1 m]
    exact (C1 m).2.2.2.2
  -- d = 2: p2 = 1 + X^2 + 2X^4
  obtain ⟨p2, hp2⟩ : ∃ p : PowerSeries ℚ, p = 1 + PowerSeries.X ^ 2 +
      2 * PowerSeries.X ^ 4 := ⟨_, rfl⟩
  have mul2 : ∀ q : PowerSeries ℚ, q * p2 = q + q * PowerSeries.X ^ 2 +
      (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 * (q * PowerSeries.X ^ 4) := by
    intro q
    rw [hp2, map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
    ring
  have L2 : ∀ (q : PowerSeries ℚ) (k : ℕ), PowerSeries.coeff k (q * p2) =
      PowerSeries.coeff k q + (if 2 ≤ k then PowerSeries.coeff (k - 2) q else 0) +
      2 * (if 4 ≤ k then PowerSeries.coeff (k - 4) q else 0) := by
    intro q k
    rw [mul2]
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow']
  have L2v : ∀ q : PowerSeries ℚ,
      PowerSeries.coeff 0 (q * p2) = PowerSeries.coeff 0 q ∧
      PowerSeries.coeff 2 (q * p2) = PowerSeries.coeff 2 q + PowerSeries.coeff 0 q ∧
      PowerSeries.coeff 4 (q * p2) = PowerSeries.coeff 4 q + PowerSeries.coeff 2 q +
        2 * PowerSeries.coeff 0 q := by
    intro q
    refine ⟨?_, ?_, ?_⟩
    · rw [L2 q 0]
      norm_num
    · rw [L2 q 2]
      norm_num
    · rw [L2 q 4]
      norm_num
  have C2 : ∀ m : ℕ, PowerSeries.coeff 0 (p2 ^ m) = 1 ∧ PowerSeries.coeff 2 (p2 ^ m) = m ∧
      PowerSeries.coeff 4 (p2 ^ m) = (m : ℚ) * (m + 3) / 2 := by
    intro m
    induction m with
    | zero => norm_num [PowerSeries.coeff_one]
    | succ m ih =>
      obtain ⟨h0, h2, h4⟩ := ih
      obtain ⟨e0, e2, e4⟩ := L2v (p2 ^ m)
      rw [pow_succ, Nat.cast_succ]
      refine ⟨?_, ?_, ?_⟩
      · linear_combination e0 + h0
      · linear_combination e2 + h2 + h0
      · linear_combination e4 + h4 + h2 + 2 * h0
  have hup2 : (1 - PowerSeries.X ^ 2 - (PowerSeries.X ^ 2) ^ 2 : PowerSeries ℚ) * p2 =
      1 - (3 * PowerSeries.X ^ 6 + 2 * PowerSeries.X ^ 8) := by
    rw [hp2]
    ring
  have hE2 : (PowerSeries.X : PowerSeries ℚ) ^ 5 ∣ 3 * PowerSeries.X ^ 6 + 2 * PowerSeries.X ^ 8 :=
    ⟨3 * PowerSeries.X + 2 * PowerSeries.X ^ 3, by ring⟩
  have K2 : ∀ m : ℕ, PowerSeries.coeff 4 (f 2 ^ m) = (m : ℚ) * (m + 3) / 2 := by
    intro m
    rw [approx _ _ _ _ (hinv 2 (by norm_num)) hup2 hE2 m]
    exact (C2 m).2.2
  -- d = 3: p3 = 1 + X^3
  obtain ⟨p3, hp3⟩ : ∃ p : PowerSeries ℚ, p = 1 + PowerSeries.X ^ 3 := ⟨_, rfl⟩
  have mul3 : ∀ q : PowerSeries ℚ, q * p3 = q + q * PowerSeries.X ^ 3 := by
    intro q
    rw [hp3]
    ring
  have L3 : ∀ (q : PowerSeries ℚ) (k : ℕ), PowerSeries.coeff k (q * p3) =
      PowerSeries.coeff k q + (if 3 ≤ k then PowerSeries.coeff (k - 3) q else 0) := by
    intro q k
    rw [mul3]
    simp only [map_add, PowerSeries.coeff_mul_X_pow']
  have L3v : ∀ q : PowerSeries ℚ,
      PowerSeries.coeff 1 (q * p3) = PowerSeries.coeff 1 q ∧
      PowerSeries.coeff 4 (q * p3) = PowerSeries.coeff 4 q + PowerSeries.coeff 1 q := by
    intro q
    refine ⟨?_, ?_⟩
    · rw [L3 q 1]
      norm_num
    · rw [L3 q 4]
      norm_num
  have C3 : ∀ m : ℕ, PowerSeries.coeff 1 (p3 ^ m) = 0 ∧ PowerSeries.coeff 4 (p3 ^ m) = 0 := by
    intro m
    induction m with
    | zero => norm_num [PowerSeries.coeff_one]
    | succ m ih =>
      obtain ⟨h1, h4⟩ := ih
      obtain ⟨e1, e4⟩ := L3v (p3 ^ m)
      rw [pow_succ]
      exact ⟨by linear_combination e1 + h1, by linear_combination e4 + h4 + h1⟩
  have hup3 : (1 - PowerSeries.X ^ 3 - (PowerSeries.X ^ 3) ^ 2 : PowerSeries ℚ) * p3 =
      1 - (2 * PowerSeries.X ^ 6 + PowerSeries.X ^ 9) := by
    rw [hp3]
    ring
  have hE3 : (PowerSeries.X : PowerSeries ℚ) ^ 5 ∣ 2 * PowerSeries.X ^ 6 + PowerSeries.X ^ 9 :=
    ⟨2 * PowerSeries.X + PowerSeries.X ^ 4, by ring⟩
  have K3 : ∀ m : ℕ, PowerSeries.coeff 4 (f 3 ^ m) = 0 := by
    intro m
    rw [approx _ _ _ _ (hinv 3 (by norm_num)) hup3 hE3 m]
    exact (C3 m).2
  -- d >= 5: p = 1
  have K5 : ∀ d m : ℕ, 5 ≤ d → PowerSeries.coeff 4 (f d ^ m) = 0 := by
    intro d m hd
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 5 := ⟨d - 5, by omega⟩
    have hup : (1 - PowerSeries.X ^ (e + 5) - (PowerSeries.X ^ (e + 5)) ^ 2 : PowerSeries ℚ) * 1 =
        1 - (PowerSeries.X ^ (e + 5) + (PowerSeries.X ^ (e + 5)) ^ 2) := by
      ring
    have hE : (PowerSeries.X : PowerSeries ℚ) ^ 5 ∣
        PowerSeries.X ^ (e + 5) + (PowerSeries.X ^ (e + 5)) ^ 2 :=
      ⟨PowerSeries.X ^ e + PowerSeries.X ^ e * PowerSeries.X ^ (e + 5), by ring⟩
    rw [approx _ _ _ _ (hinv (e + 5) (by omega)) hup hE m, one_pow, PowerSeries.coeff_one,
      if_neg (show ¬ ((4 : ℕ) = 0) by norm_num)]
  -- mobius(4) = 0
  have hmu4 : ArithmeticFunction.moebius 4 = 0 := by
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro h
    have h2 := h 2 ⟨1, by norm_num⟩
    rw [Nat.isUnit_iff] at h2
    omega
  have hT0 : ∀ d m : ℕ, 3 ≤ d →
      ((ArithmeticFunction.moebius d : ℤ) : ℚ) * PowerSeries.coeff 4 (f d ^ m) = 0 := by
    intro d m hd
    rcases (show d = 3 ∨ d = 4 ∨ 5 ≤ d by omega) with h | h | h
    · rw [h, K3 m, mul_zero]
    · rw [h, hmu4, Int.cast_zero, zero_mul]
    · rw [K5 d m h, mul_zero]
  -- a(n) as a divisor sum
  have hx : ∀ S : PowerSeries ℚ, PowerSeries.coeff 5 (S * PowerSeries.X ^ 1) =
      PowerSeries.coeff 4 S := fun S => PowerSeries.coeff_mul_X_pow S 1 4
  have hA : ∀ n : ℕ, a n = 1 / (n : ℚ) * ∑ d ∈ n.divisors,
      ((ArithmeticFunction.moebius d : ℤ) : ℚ) * PowerSeries.coeff 4 (f d ^ (n / d)) := by
    intro n
    have e : W n = PowerSeries.C (1 / (n : ℚ)) * ((∑ d ∈ n.divisors,
        PowerSeries.C ((ArithmeticFunction.moebius d : ℤ) : ℚ) * f d ^ (n / d)) *
          PowerSeries.X ^ 1) := by
      rw [W]
      ring
    rw [a, e, PowerSeries.coeff_C_mul, hx, map_sum]
    simp only [PowerSeries.coeff_C_mul]
  -- the closed form
  have hclosed : ∀ n : ℕ, 1 ≤ n →
      a n = (66 - 18 * (-1) ^ n + (115 - 3 * (-1) ^ n) * (n : ℚ) + 36 * (n : ℚ) ^ 2 +
        2 * (n : ℚ) ^ 3) / 48 := by
    intro n hn
    rw [hA n]
    have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hinvn : (n : ℚ) * (1 / (n : ℚ)) = 1 := mul_one_div_cancel hn0
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | hodd
    · have hsub : ({1, 2} : Finset ℕ) ⊆ n.divisors := by
        intro d hd
        rw [Finset.mem_insert, Finset.mem_singleton] at hd
        rw [Nat.mem_divisors]
        rcases hd with rfl | rfl
        · exact ⟨one_dvd n, by omega⟩
        · exact ⟨⟨k, by omega⟩, by omega⟩
      have hf : ∀ d ∈ n.divisors, d ∉ ({1, 2} : Finset ℕ) →
          ((ArithmeticFunction.moebius d : ℤ) : ℚ) * PowerSeries.coeff 4 (f d ^ (n / d)) = 0 := by
        intro d hd hd12
        rw [Finset.mem_insert, Finset.mem_singleton] at hd12
        rw [Nat.mem_divisors] at hd
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd.1 (by omega)
        exact hT0 d (n / d) (by omega)
      have hkq : (n : ℚ) = 2 * k := by
        rw [hk, Nat.cast_add]
        ring
      rw [← Finset.sum_subset hsub hf, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2),
        ArithmeticFunction.moebius_apply_one,
        ArithmeticFunction.moebius_apply_prime Nat.prime_two, Int.cast_neg, Int.cast_one,
        Nat.div_one, K1 n, show n / 2 = k by omega, K2 k, Even.neg_one_pow ⟨k, hk⟩, hkq]
      rw [hkq] at hinvn
      linear_combination ((2 * (k : ℚ) + 1) * (2 * (k : ℚ) + 2) * (2 * (k : ℚ) + 3) / 24 +
        (2 * (k : ℚ) + 1) * (2 * (k : ℚ) + 2) / 2 + (2 * (k : ℚ) + 1) / 2 -
        ((k : ℚ) + 3) / 4) * hinvn
    · have hodd' : n % 2 = 1 := Nat.odd_iff.mp hodd
      have hsub : ({1} : Finset ℕ) ⊆ n.divisors := by
        intro d hd
        rw [Finset.mem_singleton] at hd
        rw [hd, Nat.mem_divisors]
        exact ⟨one_dvd n, by omega⟩
      have hf : ∀ d ∈ n.divisors, d ∉ ({1} : Finset ℕ) →
          ((ArithmeticFunction.moebius d : ℤ) : ℚ) * PowerSeries.coeff 4 (f d ^ (n / d)) = 0 := by
        intro d hd hd1
        rw [Finset.mem_singleton] at hd1
        rw [Nat.mem_divisors] at hd
        have hd2 : d ≠ 2 := by
          rintro rfl
          omega
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd.1 (by omega)
        exact hT0 d (n / d) (by omega)
      rw [← Finset.sum_subset hsub hf, Finset.sum_singleton,
        ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul, Nat.div_one, K1 n,
        Odd.neg_one_pow hodd]
      linear_combination (((n : ℚ) + 1) * ((n : ℚ) + 2) * ((n : ℚ) + 3) / 24 +
        ((n : ℚ) + 1) * ((n : ℚ) + 2) / 2 + ((n : ℚ) + 1) / 2) * hinvn
  -- the values a(0), ..., a(6)
  have a0 : a 0 = 0 := by
    rw [hA 0, Nat.divisors_zero, Finset.sum_empty, mul_zero]
  have a1 : a 1 = 5 := by
    rw [hclosed 1 le_rfl]
    norm_num
  have a2 : a 2 = 9 := by
    rw [hclosed 2 (by norm_num)]
    norm_num
  have a3 : a 3 = 17 := by
    rw [hclosed 3 (by norm_num)]
    norm_num
  have a4 : a 4 = 25 := by
    rw [hclosed 4 (by norm_num)]
    norm_num
  have a5 : a 5 = 38 := by
    rw [hclosed 5 (by norm_num)]
    norm_num
  have a6 : a 6 = 51 := by
    rw [hclosed 6 (by norm_num)]
    norm_num
  -- the recurrence of order 6 for n >= 7
  have hrec : ∀ m : ℕ, 7 ≤ m → a m - 2 * a (m - 1) - a (m - 2) + 4 * a (m - 3) - a (m - 4) -
      2 * a (m - 5) + a (m - 6) = 0 := by
    intro m hm
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 7 := ⟨m - 7, by omega⟩
    rw [show j + 7 - 1 = j + 6 by omega, show j + 7 - 2 = j + 5 by omega,
      show j + 7 - 3 = j + 4 by omega, show j + 7 - 4 = j + 3 by omega,
      show j + 7 - 5 = j + 2 by omega, show j + 7 - 6 = j + 1 by omega]
    rw [hclosed (j + 7) (by omega), hclosed (j + 6) (by omega), hclosed (j + 5) (by omega),
      hclosed (j + 4) (by omega), hclosed (j + 3) (by omega), hclosed (j + 2) (by omega),
      hclosed (j + 1) (by omega)]
    push_cast
    ring
  refine ⟨hclosed, ?_⟩
  have eL : PowerSeries.mk a * ((PowerSeries.X - 1) ^ 4 * (PowerSeries.X + 1) ^ 2) =
      PowerSeries.mk a
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 * (PowerSeries.mk a * PowerSeries.X ^ 1)
        - PowerSeries.mk a * PowerSeries.X ^ 2
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 * (PowerSeries.mk a * PowerSeries.X ^ 3)
        - PowerSeries.mk a * PowerSeries.X ^ 4
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 * (PowerSeries.mk a * PowerSeries.X ^ 5)
        + PowerSeries.mk a * PowerSeries.X ^ 6 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4]
    ring
  have eR : (-PowerSeries.X * (PowerSeries.X ^ 5 - 2 * PowerSeries.X ^ 4 -
      2 * PowerSeries.X ^ 3 + 6 * PowerSeries.X ^ 2 + PowerSeries.X - 5) : PowerSeries ℚ) =
      PowerSeries.X ^ 1 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5
        - PowerSeries.X ^ 2
        - PowerSeries.X ^ 3 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6
        + PowerSeries.X ^ 4 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2
        + PowerSeries.X ^ 5 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2
        - PowerSeries.X ^ 6 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
    ring
  rw [eL, eR]
  ext m
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow]
  rcases Nat.lt_or_ge m 7 with hm | hm
  · interval_cases m
    · norm_num [a0]
    · norm_num [a0, a1]
    · norm_num [a0, a1, a2]
    · norm_num [a0, a1, a2, a3]
    · norm_num [a0, a1, a2, a3, a4]
    · norm_num [a0, a1, a2, a3, a4, a5]
    · norm_num [a0, a1, a2, a3, a4, a5, a6]
  · simp (disch := omega) only [if_pos, if_neg]
    linarith [hrec m hm]
