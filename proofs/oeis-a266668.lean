import OMAStatements.S_oeis_a266668

namespace OMA.A266668Proof
open OMA.S_oeis_a266668 PowerSeries

def P (t : ℕ) (x : ℤ) : Bool := if t % 2 = 0 then (if x = 0 then true else false) else (if x = 0 then false else true)

theorem S (t : ℕ) : ∀ x, state 51 t x = P t x := by
  induction t with
  | zero => intro x; simp [state, P]
  | succ t ih => intro x; simp only [state, step, ih, P]; split_ifs <;> first | rfl | (exfalso; omega)

theorem V (n : ℕ) : (a n : ℚ) = ∑ i ∈ Finset.range (2 * n + 1), if P n ((n : ℤ) - i) then (2 : ℚ) ^ i else 0 := by
  simp only [a, rowValue, S]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  cases P n ((n : ℤ) - i) <;> simp

theorem E (n : ℕ) (h : Even n) : (a n : ℚ) = 2 ^ n := by
  rw [V, Finset.sum_eq_single n]
  · simp [P, Nat.even_iff.1 h]
  · intro i _ hi
    simp [P, Nat.even_iff.1 h, sub_eq_zero, Ne.symm hi]
  · intro hn; simp at hn; omega

theorem O (n : ℕ) (h : Odd n) : (a n : ℚ) = 2 * 4 ^ n - 2 ^ n - 1 := by
  have hn : n % 2 = 1 := Nat.odd_iff.1 h
  rw [V]
  have e : ∀ i ∈ Finset.range (2 * n + 1),
      (if P n ((n : ℤ) - i) then (2 : ℚ) ^ i else 0) = 2 ^ i - if i = n then 2 ^ i else 0 := by
    intro i _
    by_cases hi : i = n
    · subst hi; simp [P, hn]
    · simp [P, hn, hi, sub_eq_zero, Ne.symm hi]
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (by simp; omega),
    geom_sum_eq (by norm_num), show (4 : ℚ) ^ n = 2 ^ (2 * n) by rw [pow_mul]; norm_num]
  ring

theorem F (n : ℕ) : (a n : ℚ) = -1 / 2 - (-4) ^ n + (-2) ^ n + (-1) ^ n / 2 + 4 ^ n := by
  rcases Nat.even_or_odd n with h | h
  · rw [E n h, h.neg_pow, h.neg_pow, h.neg_one_pow]; ring
  · rw [O n h, h.neg_pow, h.neg_pow, h.neg_one_pow]; ring

theorem G : A = (1 + 7 * X - 3 * X ^ 2 + 8 * X ^ 3 + 32 * X ^ 4) * ((1 - X) * (1 + X) * (1 + 2 * X) * (1 - 4 * X) * (1 + 4 * X))⁻¹ := by
  have hd : constantCoeff (((1 - X) * (1 + X) * (1 + 2 * X) * (1 - 4 * X) * (1 + 4 * X)) : ℚ⟦X⟧) ≠ 0 := by simp
  have k : A * ((1 - X) * (1 + X) * (1 + 2 * X) * (1 - 4 * X) * (1 + 4 * X)) = 1 + 7 * X - 3 * X ^ 2 + 8 * X ^ 3 + 32 * X ^ 4 := by
    rw [show A * ((1 - X) * (1 + X) * (1 + 2 * X) * (1 - 4 * X) * (1 + 4 * X)) = C (1 : ℚ) * A + C (2 : ℚ) * (A * X ^ 1) + C (-17 : ℚ) * (A * X ^ 2) + C (-34 : ℚ) * (A * X ^ 3) + C (16 : ℚ) * (A * X ^ 4) + C (32 : ℚ) * (A * X ^ 5) by simp only [map_neg, map_ofNat, map_one]; ring,
      show (1 + 7 * X - 3 * X ^ 2 + 8 * X ^ 3 + 32 * X ^ 4 : ℚ⟦X⟧) = C (1 : ℚ) + C (7 : ℚ) * X ^ 1 + C (-3 : ℚ) * X ^ 2 + C (8 : ℚ) * X ^ 3 + C (32 : ℚ) * X ^ 4 by simp only [map_neg, map_ofNat, map_one]; ring]
    ext n
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, A, coeff_C]
    rcases Nat.lt_or_ge n 5 with hn | hn
    · interval_cases n <;> norm_num [F]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
      simp only [show 1 ≤ m + 5 by omega, show 2 ≤ m + 5 by omega, show 3 ≤ m + 5 by omega, show 4 ≤ m + 5 by omega, show 5 ≤ m + 5 by omega, show m + 5 ≠ 0 by omega, show m + 4 ≠ 0 by omega, show m + 3 ≠ 0 by omega, show m + 2 ≠ 0 by omega, show m + 1 ≠ 0 by omega, show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega, show m + 5 - 5 = m + 0 by omega, ↓reduceIte]
      rw [F (m + 5), F (m + 4), F (m + 3), F (m + 2), F (m + 1), F (m + 0)]
      ring
  rw [← k, mul_assoc, PowerSeries.mul_inv_cancel _ hd, mul_one]

end OMA.A266668Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a266668.main := ⟨OMA.A266668Proof.F, OMA.A266668Proof.G, OMA.A266668Proof.O, OMA.A266668Proof.E⟩
