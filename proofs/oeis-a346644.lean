import OMAStatements.S_oeis_a346644

open ArithmeticFunction Finset

theorem OMA.solution : type_of% @OMA.S_oeis_a346644.main := by
  intro n hn
  obtain ⟨v, u, hu, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  have hv1 : 1 ≤ 2 ^ v := Nat.one_le_two_pow
  have hpow : 2 ≤ 2 ^ (2 ^ v) := by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hv1
  set G := 2 ^ (2 ^ v) - 1
  have hG : G + 1 = 2 ^ (2 ^ v) := by omega
  have hGodd : Odd G :=
    Nat.not_even_iff_odd.1 (Nat.even_add_one.1 (hG.symm ▸ Nat.even_pow.2 ⟨even_two, by omega⟩))
  set M := u * G
  have hModd : Odd M := hu.mul hGodd
  have hMpos : 0 < M := hModd.pos
  obtain ⟨p, hgt, hp, hpmod⟩ := Nat.forall_exists_prime_gt_and_modEq 2 (q := 2 * M)
    (a := 2 * M - 1) (by omega) (by rw [show 2 * M = (2 * M - 1) + 1 by omega]; simp)
  have hpz : (p : ZMod (2 * M)) = -1 := by
    rw [(ZMod.natCast_eq_natCast_iff ..).2 hpmod]
    exact eq_neg_of_add_eq_zero_left (by
      norm_cast; rw [Nat.sub_add_cancel (by omega)]; exact ZMod.natCast_self _)
  set S := ∑ j ∈ range M, p ^ j
  have hS1 : (S : ZMod (2 * M)) = 1 := by
    obtain ⟨t, ht⟩ := hModd
    simp only [S, ht, Nat.cast_sum, Nat.cast_pow, hpz]
    clear ht
    induction t with
    | zero => simp
    | succ t ih =>
      rw [show 2 * (t + 1) + 1 = 2 * t + 1 + 1 + 1 by omega, sum_range_succ, sum_range_succ, ih,
        pow_succ, pow_succ]
      ring
  have hScop : Nat.Coprime S (2 * M) := (ZMod.isUnit_iff_coprime ..).1 (hS1 ▸ isUnit_one)
  have hScopn : Nat.Coprime S (2 ^ v * u) :=
    ((hScop.coprime_dvd_right (dvd_mul_right 2 M)).pow_right v).mul_right
      (hScop.coprime_dvd_right ⟨2 * G, by ring⟩)
  have hcopk : Nat.Coprime (2 ^ (2 ^ v - 1)) (p ^ (M - 1)) :=
    ((Nat.coprime_primes Nat.prime_two hp).2 (by omega)).pow _ _
  have h2g : ∑ j ∈ range (2 ^ v), 2 ^ j = G := by
    suffices ∀ m, ∑ j ∈ range m, 2 ^ j + 1 = 2 ^ m by have := this (2 ^ v); omega
    intro m; induction m with
    | zero => simp
    | succ m ih => rw [sum_range_succ, pow_succ]; omega
  refine ⟨2 ^ (2 ^ v - 1) * p ^ (M - 1), by have := hp.pos; positivity, ?_⟩
  have hcard : (2 ^ (2 ^ v - 1) * p ^ (M - 1)).divisors.card = 2 ^ v * M := by
    rw [← sigma_zero_apply, isMultiplicative_sigma.map_mul_of_coprime hcopk,
      sigma_zero_apply_prime_pow Nat.prime_two, sigma_zero_apply_prime_pow hp,
      Nat.sub_add_cancel hv1, Nat.sub_add_cancel hMpos]
  have hsum : ∑ d ∈ (2 ^ (2 ^ v - 1) * p ^ (M - 1)).divisors, d = G * S := by
    rw [← sigma_one_apply, isMultiplicative_sigma.map_mul_of_coprime hcopk,
      sigma_one_apply_prime_pow Nat.prime_two, sigma_one_apply_prime_pow hp,
      Nat.sub_add_cancel hv1, Nat.sub_add_cancel hMpos, h2g]
  rw [OMA.S_oeis_a346644.divisorMean, hsum, hcard]
  have hq : ((G * S : ℕ) : ℚ) / ((2 ^ v * M : ℕ) : ℚ) =
      ((S : ℤ) : ℚ) / (((2 ^ v * u : ℕ) : ℤ) : ℚ) := by
    have hG0 : (G : ℚ) ≠ 0 := by exact_mod_cast (show G ≠ 0 by omega)
    have hn0 : ((2 : ℚ) ^ v * u) ≠ 0 := by exact_mod_cast hn.ne'
    simp only [M]; push_cast; field_simp
  rw [hq]
  exact_mod_cast Rat.den_div_eq_of_coprime (a := (S : ℤ)) (b := ((2 ^ v * u : ℕ) : ℤ))
    (by exact_mod_cast hn) (by rw [Int.natAbs_natCast, Int.natAbs_natCast]; exact hScopn)
