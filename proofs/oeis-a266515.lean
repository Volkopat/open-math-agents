import OMAStatements.S_oeis_a266515

namespace OMA.A266515Proof
open OMA.S_oeis_a266515 PowerSeries

def P (t : ℕ) (x : ℤ) : Bool :=
  if t % 2 = 0 then (if x = 0 then true else false) else (if x = -1 then false else true)

theorem S (t : ℕ) : ∀ x, state 29 t x = P t x := by
  induction t with
  | zero => intro x; simp [state, P]
  | succ t ih =>
    intro x
    simp only [state, step, ih, P]
    split_ifs <;> first | rfl | (exfalso; omega)

theorem V (n : ℕ) : (a n : ℚ) = ∑ i ∈ Finset.range (2 * n + 1), if P n ((n : ℤ) - i) then (10 : ℚ) ^ i else 0 := by
  simp only [a, rowDigits, S]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  cases P n ((n : ℤ) - i) <;> simp

theorem E (n : ℕ) (h : Even n) : (a n : ℚ) = 10 ^ n := by
  rw [V, Finset.sum_eq_single n]
  · simp [P, Nat.even_iff.1 h]
  · intro i _ hi
    simp [P, Nat.even_iff.1 h, sub_eq_zero, Ne.symm hi]
  · intro hn; simp at hn; omega

theorem O (n : ℕ) (h : Odd n) : (a n : ℚ) = (10 * (100 ^ n - 9 * 10 ^ n) - 1) / 9 := by
  have hn : n % 2 = 1 := Nat.odd_iff.1 h
  have hn1 : 1 ≤ n := h.pos
  rw [V]
  have e : ∀ i ∈ Finset.range (2 * n + 1),
      (if P n ((n : ℤ) - i) then (10 : ℚ) ^ i else 0) = 10 ^ i - if i = n + 1 then 10 ^ i else 0 := by
    intro i _
    by_cases hi : i = n + 1
    · subst hi; simp [P, hn]
    · simp [P, hn, hi, show ¬ ((n : ℤ) - i = -1) by omega]
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (by simp; omega),
    geom_sum_eq (by norm_num), show (100 : ℚ) ^ n = 10 ^ (2 * n) by rw [pow_mul]; norm_num]
  ring

theorem F (n : ℕ) : (a n : ℚ) = (1 + (-1) ^ n) / 2 * 10 ^ n + (1 - (-1) ^ n) / 2 * ((10 * (100 ^ n - 9 * 10 ^ n) - 1) / 9) := by
  rcases Nat.even_or_odd n with h | h
  · rw [E n h, h.neg_one_pow]; ring
  · rw [O n h, h.neg_one_pow]; ring

theorem R (n : ℕ) (hn : 5 < n) : (a n : ℤ) = 10101 * a (n - 2) - 1010100 * a (n - 4) + 1000000 * a (n - 6) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 6 := ⟨n - 6, by omega⟩
  have h : (a (p + 6) : ℚ) = 10101 * a (p + 4) - 1010100 * a (p + 2) + 1000000 * a p := by
    rw [F, F, F, F]; ring
  rw [show p + 6 - 2 = p + 4 by omega, show p + 6 - 4 = p + 2 by omega, show p + 6 - 6 = p by omega]
  exact_mod_cast h
theorem G : A = (1 + 11 * X - 10001 * X ^ 2 + 990000 * X ^ 3 + 10000 * X ^ 4 - 1100000 * X ^ 5) * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 100 * X) * (1 + 100 * X))⁻¹ := by
  have hd : constantCoeff (((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 100 * X) * (1 + 100 * X)) : ℚ⟦X⟧) ≠ 0 := by simp
  have k : A * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 100 * X) * (1 + 100 * X)) = 1 + 11 * X - 10001 * X ^ 2 + 990000 * X ^ 3 + 10000 * X ^ 4 - 1100000 * X ^ 5 := by
    rw [show A * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 100 * X) * (1 + 100 * X)) = C (1 : ℚ) * A + C (-10101 : ℚ) * (A * X ^ 2) + C (1010100 : ℚ) * (A * X ^ 4) + C (-1000000 : ℚ) * (A * X ^ 6) by simp only [map_neg, map_ofNat, map_one]; ring,
      show (1 + 11 * X - 10001 * X ^ 2 + 990000 * X ^ 3 + 10000 * X ^ 4 - 1100000 * X ^ 5 : ℚ⟦X⟧) = C (1 : ℚ) + C (11 : ℚ) * X ^ 1 + C (-10001 : ℚ) * X ^ 2 + C (990000 : ℚ) * X ^ 3 + C (10000 : ℚ) * X ^ 4 + C (-1100000 : ℚ) * X ^ 5 by simp only [map_neg, map_ofNat, map_one]; ring]
    ext n
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, A, coeff_C]
    rcases Nat.lt_or_ge n 6 with hn | hn
    · interval_cases n <;> norm_num [F]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      simp only [show 1 ≤ m + 6 by omega, show 2 ≤ m + 6 by omega, show 3 ≤ m + 6 by omega, show 4 ≤ m + 6 by omega, show 5 ≤ m + 6 by omega, show 6 ≤ m + 6 by omega, show m + 6 ≠ 0 by omega, show m + 6 - 1 ≠ 0 by omega, show m + 4 ≠ 0 by omega, show m + 6 - 3 ≠ 0 by omega, show m + 2 ≠ 0 by omega, show m + 6 - 5 ≠ 0 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 6 = m + 0 by omega, ↓reduceIte]
      rw [F (m + 6), F (m + 4), F (m + 2), F (m + 0)]
      ring
  rw [← k, mul_assoc, PowerSeries.mul_inv_cancel _ hd, mul_one]

end OMA.A266515Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a266515.main := ⟨OMA.A266515Proof.R, OMA.A266515Proof.G, OMA.A266515Proof.O, OMA.A266515Proof.E⟩
