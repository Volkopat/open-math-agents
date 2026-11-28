import OMAStatements.S_oeis_a266671

namespace OMA.A266671Proof
open OMA.S_oeis_a266671 PowerSeries

def P (t : ℕ) (x : ℤ) : Bool :=
  if t % 2 = 0 then (if 2 * x = -t then true else false) else (if 2 * x = -(t + 1) then false else true)

theorem S (t : ℕ) : ∀ x, state t x = P t x := by
  induction t with
  | zero => intro x; simp [state, P]
  | succ t ih =>
    intro x
    simp only [state, rule, ih, P]
    push_cast
    split_ifs <;> first | rfl | (exfalso; omega)

theorem T (N : ℕ) : ∑ k ∈ Finset.range (N + 1), (2 : ℚ) ^ (N - k) = 2 ^ (N + 1) - 1 := by
  have := Finset.sum_range_reflect (fun k => (2 : ℚ) ^ k) (N + 1)
  simp only [Nat.add_sub_cancel] at this
  rw [this, geom_sum_eq (by norm_num)]
  norm_num

theorem V (n : ℕ) : (a n : ℚ) = ∑ k ∈ Finset.range (2 * n + 1), if P n ((k : ℤ) - n) then (2 : ℚ) ^ (2 * n - k) else 0 := by
  simp only [a, S]
  push_cast
  rfl

theorem E (n : ℕ) (h : n % 2 = 0) : (a n : ℚ) = 2 ^ (n + n / 2) := by
  rw [V, Finset.sum_eq_single (n - n / 2)]
  · simp only [P, h, ↓reduceIte]
    split_ifs <;> first | (exfalso; omega) | contradiction | rw [show 2 * n - (n - n / 2) = n + n / 2 by omega]
  · intro k _ hk
    simp only [P, h, ↓reduceIte]
    split_ifs <;> first | (exfalso; omega) | rfl
  · intro hn; simp at hn; omega

theorem O (n : ℕ) (h : n % 2 = 1) : (a n : ℚ) = 2 ^ (2 * n + 1) - 1 - 2 ^ (n + (n + 1) / 2) := by
  rw [V, Finset.sum_congr rfl (g := fun k => (2 : ℚ) ^ (2 * n - k) - if k = n - (n + 1) / 2 then 2 ^ (2 * n - k) else 0),
    Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (by simp; omega), T, show 2 * n - (n - (n + 1) / 2) = n + (n + 1) / 2 by omega]
  intro k _
  simp only [P, h, ↓reduceIte]
  split_ifs <;> first | (exfalso; omega) | contradiction | simp

theorem R (n : ℕ) (hn : 5 < n) : (a n : ℤ) = 25 * a (n - 2) - 152 * a (n - 4) + 128 * a (n - 6) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 6 := ⟨n - 6, by omega⟩
  have h : (a (p + 6) : ℚ) = 25 * a (p + 4) - 152 * a (p + 2) + 128 * a p := by
    rcases Nat.even_or_odd p with ⟨q, hq⟩ | ⟨q, hq⟩ <;> subst hq
    · rw [E _ (by omega), E _ (by omega), E _ (by omega), E _ (by omega), show (q + q + 6) / 2 = q + 3 by omega,
        show (q + q + 4) / 2 = q + 2 by omega, show (q + q + 2) / 2 = q + 1 by omega, show (q + q) / 2 = q by omega]
      ring
    · rw [O _ (by omega), O _ (by omega), O _ (by omega), O _ (by omega), show (2 * q + 1 + 6 + 1) / 2 = q + 4 by omega,
        show (2 * q + 1 + 4 + 1) / 2 = q + 3 by omega, show (2 * q + 1 + 2 + 1) / 2 = q + 2 by omega,
        show (2 * q + 1 + 1) / 2 = q + 1 by omega]
      ring
  rw [show p + 6 - 2 = p + 4 by omega, show p + 6 - 4 = p + 2 by omega, show p + 6 - 6 = p by omega]
  exact_mod_cast h
theorem G : (PowerSeries.mk (fun n => (a n : ℚ))) = (1 + 3 * X - 17 * X ^ 2 + 20 * X ^ 3 + 16 * X ^ 4 - 128 * X ^ 5) * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 8 * X ^ 2))⁻¹ := by
  have hd : constantCoeff (((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 8 * X ^ 2)) : ℚ⟦X⟧) ≠ 0 := by simp
  have k : (PowerSeries.mk (fun n => (a n : ℚ))) * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 8 * X ^ 2)) = 1 + 3 * X - 17 * X ^ 2 + 20 * X ^ 3 + 16 * X ^ 4 - 128 * X ^ 5 := by
    rw [show (PowerSeries.mk (fun n => (a n : ℚ))) * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 8 * X ^ 2)) = C (1 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ))) + C (-25 : ℚ) * ((PowerSeries.mk (fun n => (a n : ℚ))) * X ^ 2) + C (152 : ℚ) * ((PowerSeries.mk (fun n => (a n : ℚ))) * X ^ 4) + C (-128 : ℚ) * ((PowerSeries.mk (fun n => (a n : ℚ))) * X ^ 6) by simp only [map_neg, map_ofNat, map_one]; ring,
      show (1 + 3 * X - 17 * X ^ 2 + 20 * X ^ 3 + 16 * X ^ 4 - 128 * X ^ 5 : ℚ⟦X⟧) = C (1 : ℚ) + C (3 : ℚ) * X ^ 1 + C (-17 : ℚ) * X ^ 2 + C (20 : ℚ) * X ^ 3 + C (16 : ℚ) * X ^ 4 + C (-128 : ℚ) * X ^ 5 by simp only [map_neg, map_ofNat, map_one]; ring]
    ext n
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_C]
    rcases Nat.lt_or_ge n 6 with hn | hn
    · interval_cases n <;> norm_num [E, O]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      simp only [show 1 ≤ m + 6 by omega, show 2 ≤ m + 6 by omega, show 3 ≤ m + 6 by omega, show 4 ≤ m + 6 by omega, show 5 ≤ m + 6 by omega, show 6 ≤ m + 6 by omega, show m + 6 ≠ 0 by omega, show m + 6 - 1 ≠ 0 by omega, show m + 4 ≠ 0 by omega, show m + 6 - 3 ≠ 0 by omega, show m + 2 ≠ 0 by omega, show m + 6 - 5 ≠ 0 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 6 = m + 0 by omega, ↓reduceIte]
      have h := congrArg (Int.cast : ℤ → ℚ) (R (m + 6) (by omega))
      simp only [show m + 6 - 2 = m + 4 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 6 = m + 0 by omega] at h
      push_cast at h
      linear_combination h
  rw [← k, mul_assoc, PowerSeries.mul_inv_cancel _ hd, mul_one]

end OMA.A266671Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a266671.main := ⟨OMA.A266671Proof.R, OMA.A266671Proof.G⟩
