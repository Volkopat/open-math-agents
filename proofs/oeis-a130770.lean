import OMAStatements.S_oeis_a130770
import Mathlib

lemma OMA.den_eq (a b : ℤ) (hb : 0 < b) (h : IsCoprime a b) : (((a : ℚ) / b).den : ℤ) = b := by
  have h' : Nat.Coprime a.natAbs b.natAbs := Int.isCoprime_iff_gcd_eq_one.mp h
  have := Rat.den_div_eq_of_coprime hb h'
  exact_mod_cast this

theorem OMA.solution : type_of% @OMA.S_oeis_a130770.main := by
  intro n hn
  obtain ⟨x, rfl⟩ : ∃ x, n = x + 1 := ⟨n - 1, by omega⟩
  simp only [OMA.S_oeis_a130770.a, OMA.S_oeis_a130770.A046163]
  have hN : (x + 1) ^ 2 + (x + 1) + 1 = x ^ 2 + 3 * x + 3 := by ring
  rw [hN]
  by_cases h3 : 3 ∣ x
  · obtain ⟨y, rfl⟩ := h3
    have hq : ((((3 * y + 1 : ℕ) : ℚ) - 1) ^ 2 / (((3 * y + 1 : ℕ) : ℚ) ^ 2 + ((3 * y + 1 : ℕ) : ℚ) + 1)) =
        ((3 * (y : ℤ) ^ 2 : ℤ) : ℚ) / ((3 * (y : ℤ) ^ 2 + 3 * (y : ℤ) + 1 : ℤ) : ℚ) := by
      push_cast
      have : (3 * (y : ℚ) ^ 2 + 3 * y + 1) ≠ 0 := by positivity
      field_simp
      ring
    rw [hq]
    have hc : IsCoprime (3 * (y : ℤ) ^ 2) (3 * (y : ℤ) ^ 2 + 3 * (y : ℤ) + 1) :=
      ⟨3 * (y : ℤ) + 2, 1 - 3 * (y : ℤ), by ring⟩
    have hd := OMA.den_eq _ _ (by positivity) hc
    have e : (3 * y) ^ 2 + 3 * (3 * y) + 3 = 3 * (3 * y ^ 2 + 3 * y + 1) := by ring
    rw [e, Nat.lcm_eq_right (dvd_mul_right 3 _), Nat.mul_div_cancel_left _ (by norm_num)]
    zify
    push_cast at hd ⊢
    exact hd.symm
  · have hq : ((((x + 1 : ℕ) : ℚ) - 1) ^ 2 / (((x + 1 : ℕ) : ℚ) ^ 2 + ((x + 1 : ℕ) : ℚ) + 1)) =
        (((x ^ 2 : ℕ) : ℤ) : ℚ) / (((x ^ 2 + 3 * x + 3 : ℕ) : ℤ) : ℚ) := by
      push_cast
      ring
    rw [hq]
    have cx3 : Nat.Coprime x 3 := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3))
    have c1 : Nat.Coprime x (x ^ 2 + 3 * x + 3) := by
      rw [show x ^ 2 + 3 * x + 3 = 3 + x * (x + 3) by ring, Nat.coprime_add_mul_left_right]
      exact cx3
    have c2 : Nat.Coprime 3 (x ^ 2 + 3 * x + 3) := by
      rw [show x ^ 2 + 3 * x + 3 = x ^ 2 + 3 * (x + 1) by ring, Nat.coprime_add_mul_left_right]
      exact Nat.Coprime.pow_right 2 cx3.symm
    have hc : IsCoprime ((x ^ 2 : ℕ) : ℤ) ((x ^ 2 + 3 * x + 3 : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left 2 c1)
    have hd := OMA.den_eq _ _ (by positivity) hc
    rw [Nat.Coprime.lcm_eq_mul c2, Nat.mul_div_cancel_left _ (by norm_num)]
    zify
    push_cast at hd ⊢
    exact hd.symm
