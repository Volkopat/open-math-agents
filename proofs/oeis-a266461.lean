import OMAStatements.S_oeis_a266461

namespace OMA.A266461Proof
open OMA.S_oeis_a266461 PowerSeries

def P (t : ℕ) (x : ℤ) : Bool :=
  if t % 2 = 0 then (if 2 * x = t then true else false) else (if 2 * x = t - 1 then false else true)

theorem S (t : ℕ) : ∀ x, state 27 t x = P t x := by
  induction t with
  | zero => intro x; simp [state, P]
  | succ t ih =>
    intro x
    simp only [state, step, ih, P]
    push_cast
    split_ifs <;> first | rfl | (exfalso; omega)

theorem V (n : ℕ) : (a n : ℚ) = ∑ i ∈ Finset.range (2 * n + 1), if P n ((n : ℤ) - i) then (2 : ℚ) ^ i else 0 := by
  simp only [a, rowValue, S]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  cases P n ((n : ℤ) - i) <;> simp

theorem E (n : ℕ) (h : n % 2 = 0) : (a n : ℚ) = 2 ^ (n / 2) := by
  rw [V, Finset.sum_eq_single (n - n / 2)]
  · simp only [P, h, ↓reduceIte]
    split_ifs <;> first | (exfalso; omega) | contradiction | rw [show n - n / 2 = n / 2 by omega]
  · intro i _ hi
    simp [P, h, show ¬ (2 * ((n : ℤ) - i) = n) by omega]
  · intro hn; simp at hn; omega

theorem O (n : ℕ) (h : n % 2 = 1) : (a n : ℚ) = 2 * (4 ^ n - 2 ^ (n / 2)) - 1 := by
  rw [V, Finset.sum_congr rfl (g := fun i => (2 : ℚ) ^ i - if i = n / 2 + 1 then 2 ^ i else 0),
    Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (by simp; omega), geom_sum_eq (by norm_num),
    show (4 : ℚ) ^ n = 2 ^ (2 * n) by rw [pow_mul]; norm_num]
  · ring
  · intro i _
    by_cases hi : i = n / 2 + 1
    · subst hi; simp only [P, h, ↓reduceIte]
      split_ifs <;> first | (exfalso; omega) | simp
    · simp [P, h, hi, show ¬ (2 * ((n : ℤ) - i) = n - 1) by omega]

theorem R (n : ℕ) (hn : 5 < n) : (a n : ℤ) = 19 * a (n - 2) - 50 * a (n - 4) + 32 * a (n - 6) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 6 := ⟨n - 6, by omega⟩
  have h : (a (p + 6) : ℚ) = 19 * a (p + 4) - 50 * a (p + 2) + 32 * a p := by
    rcases Nat.even_or_odd p with ⟨q, hq⟩ | ⟨q, hq⟩ <;> subst hq
    · rw [E _ (by omega), E _ (by omega), E _ (by omega), E _ (by omega), show (q + q + 6) / 2 = q + 3 by omega,
        show (q + q + 4) / 2 = q + 2 by omega, show (q + q + 2) / 2 = q + 1 by omega, show (q + q) / 2 = q by omega]
      ring
    · rw [O _ (by omega), O _ (by omega), O _ (by omega), O _ (by omega), show (2 * q + 1 + 6) / 2 = q + 3 by omega,
        show (2 * q + 1 + 4) / 2 = q + 2 by omega, show (2 * q + 1 + 2) / 2 = q + 1 by omega, show (2 * q + 1) / 2 = q by omega]
      ring
  rw [show p + 6 - 2 = p + 4 by omega, show p + 6 - 4 = p + 2 by omega, show p + 6 - 6 = p by omega]
  exact_mod_cast h
theorem G : A = (1 + 5 * X - 17 * X ^ 2 + 28 * X ^ 3 + 16 * X ^ 4 - 48 * X ^ 5) * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 2 * X ^ 2))⁻¹ := by
  have hd : constantCoeff (((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 2 * X ^ 2)) : ℚ⟦X⟧) ≠ 0 := by simp
  have k : A * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 2 * X ^ 2)) = 1 + 5 * X - 17 * X ^ 2 + 28 * X ^ 3 + 16 * X ^ 4 - 48 * X ^ 5 := by
    rw [show A * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 2 * X ^ 2)) = C (1 : ℚ) * A + C (-19 : ℚ) * (A * X ^ 2) + C (50 : ℚ) * (A * X ^ 4) + C (-32 : ℚ) * (A * X ^ 6) by simp only [map_neg, map_ofNat, map_one]; ring,
      show (1 + 5 * X - 17 * X ^ 2 + 28 * X ^ 3 + 16 * X ^ 4 - 48 * X ^ 5 : ℚ⟦X⟧) = C (1 : ℚ) + C (5 : ℚ) * X ^ 1 + C (-17 : ℚ) * X ^ 2 + C (28 : ℚ) * X ^ 3 + C (16 : ℚ) * X ^ 4 + C (-48 : ℚ) * X ^ 5 by simp only [map_neg, map_ofNat, map_one]; ring]
    ext n
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, A, coeff_C]
    rcases Nat.lt_or_ge n 6 with hn | hn
    · interval_cases n <;> norm_num [E, O]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      simp only [show 1 ≤ m + 6 by omega, show 2 ≤ m + 6 by omega, show 3 ≤ m + 6 by omega, show 4 ≤ m + 6 by omega, show 5 ≤ m + 6 by omega, show 6 ≤ m + 6 by omega, show m + 6 ≠ 0 by omega, show m + 6 - 1 ≠ 0 by omega, show m + 4 ≠ 0 by omega, show m + 6 - 3 ≠ 0 by omega, show m + 2 ≠ 0 by omega, show m + 6 - 5 ≠ 0 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 6 = m + 0 by omega, ↓reduceIte]
      have h := congrArg (Int.cast : ℤ → ℚ) (R (m + 6) (by omega))
      simp only [show m + 6 - 2 = m + 4 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 6 = m + 0 by omega] at h
      push_cast at h
      linear_combination h
  rw [← k, mul_assoc, PowerSeries.mul_inv_cancel _ hd, mul_one]

end OMA.A266461Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a266461.main := ⟨OMA.A266461Proof.R, OMA.A266461Proof.G, fun n h => by exact_mod_cast OMA.A266461Proof.O n (Nat.odd_iff.1 h), fun n h => by exact_mod_cast OMA.A266461Proof.E n (Nat.even_iff.1 h)⟩
