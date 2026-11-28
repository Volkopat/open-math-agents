import OMAStatements.S_oeis_a110515

-- Original proof by @jleguina.

namespace OMA.S_oeis_a110515

open PowerSeries

lemma G_mul : G * (1 - X ^ 4) = 1 - X + X ^ 2 + X ^ 3 := by
  have h : constantCoeff (1 - X ^ 4 : ℚ⟦X⟧) ≠ 0 := by simp
  rw [G, mul_assoc, PowerSeries.inv_mul_cancel _ h, mul_one]

/-- The coefficient recursion `g(m) = c(m) + g(m-4)`. -/
lemma coeff_rec (m : ℕ) :
    coeff m G = coeff m (1 - X + X ^ 2 + X ^ 3 : ℚ⟦X⟧) + if 4 ≤ m then coeff (m - 4) G else 0 := by
  have h := congrArg (coeff m) G_mul
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow'] at h
  exact sub_eq_iff_eq_add.mp h

lemma coeff_G (m : ℕ) : coeff m G = if m % 4 = 1 then -1 else 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [coeff_rec]
    simp only [map_add, map_sub, coeff_one, coeff_X, coeff_X_pow]
    rcases Nat.lt_or_ge m 4 with hm | hm
    · rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) with rfl | rfl | rfl | rfl <;> norm_num
    · rw [if_pos hm, ih (m - 4) (by omega)]
      simp (disch := omega) [if_neg, show (m - 4) % 4 = m % 4 by omega]

lemma jacobi_value (m : ℕ) : jacobiSym ((2 : ℤ) ^ m) (2 * m + 1) = if m % 4 = 1 then -1 else 1 := by
  rw [jacobiSym.pow_left, jacobiSym.at_two ⟨m, by omega⟩, ZMod.χ₈_nat_eq_if_mod_eight,
    show (2 * m + 1) % 2 = 1 by omega, show (2 * m + 1) % 8 = 2 * (m % 4) + 1 by omega]
  have hp := pow_eq_pow_mod m (show (-1 : ℤ) ^ 4 = 1 by decide)
  generalize hm : m % 4 = r at hp ⊢
  have hr : r < 4 := hm ▸ Nat.mod_lt m (by decide)
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;> simp [hp]

/-- The conjectured formula: `T(n,k) = Jacobi(2^(n-k), 2(n-k)+1)` for `k ≤ n`, and `0` otherwise. -/
theorem conjecture (n k : ℕ) :
    T n k = if k ≤ n then ((jacobiSym ((2 : ℤ) ^ (n - k)) (2 * (n - k) + 1) : ℤ) : ℚ) else 0 := by
  simp only [T, coeff_G, jacobi_value]
  split_ifs <;> norm_num

/-- Control: the first rows 1; -1, 1; 1, -1, 1; 1, 1, -1, 1. -/
example : T 0 0 = 1 ∧ T 1 0 = -1 ∧ T 2 0 = 1 ∧ T 3 0 = 1 ∧ T 3 1 = 1 ∧ T 3 2 = -1 := by
  simp only [T, coeff_G]
  norm_num

end OMA.S_oeis_a110515

theorem OMA.solution : type_of% @OMA.S_oeis_a110515.main :=
  fun n k => OMA.S_oeis_a110515.conjecture n k
