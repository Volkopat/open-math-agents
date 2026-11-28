import OMAStatements.S_oeis_a266850

namespace OMA.A266850Proof
open OMA.S_oeis_a266850 PowerSeries

def P (t : ℕ) (x : ℤ) : Bool :=
  if t % 2 = 0 then (if x = 0 then true else false) else (if x = 1 then false else true)

theorem S (t : ℕ) : ∀ x, state t x = P t x := by
  induction t with
  | zero => intro x; simp [state, P]
  | succ t ih =>
    intro x
    simp only [state, eca, ih, P]
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

theorem E (n : ℕ) (h : n % 2 = 0) : (a n : ℚ) = 2 ^ (n) := by
  rw [V, Finset.sum_eq_single (n)]
  · simp only [P, h]
    split_ifs <;> first | (exfalso; omega) | contradiction | rw [show 2 * n - (n) = n by omega]
  · intro k _ hk
    simp only [P, h]
    split_ifs <;> first | (exfalso; omega) | rfl
  · intro hn; simp at hn; omega
theorem O (n : ℕ) (h : n % 2 = 1) : (a n : ℚ) = 2 ^ (2 * n + 1) - 1 - 2 ^ (n - 1) := by
  rw [V, Finset.sum_congr rfl (g := fun k => (2 : ℚ) ^ (2 * n - k) - if k = n + 1 then 2 ^ (2 * n - k) else 0),
    Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (by simp; omega), T, show 2 * n - (n + 1) = n - 1 by omega]
  intro k _
  simp only [P, h, ↓reduceIte]
  split_ifs <;> first | (exfalso; omega) | contradiction | simp

theorem R (n : ℕ) (hn : 5 < n) : (a n : ℤ) = 21 * a (n - 2) - 84 * a (n - 4) + 64 * a (n - 6) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 6 := ⟨n - 6, by omega⟩
  have h : (a (p + 6) : ℚ) = 21 * a (p + 4) - 84 * a (p + 2) + 64 * a (p) := by
    rcases Nat.even_or_odd p with ⟨q, hq⟩ | ⟨q, hq⟩ <;> subst hq
    · rw [E _ (by omega), E _ (by omega), E _ (by omega), E _ (by omega)]
      ring
    · rw [O _ (by omega), O _ (by omega), O _ (by omega), O _ (by omega), show (2 * q + 1 + 6) - 1 = 2 * q + 6 by omega, show (2 * q + 1 + 4) - 1 = 2 * q + 4 by omega, show (2 * q + 1 + 2) - 1 = 2 * q + 2 by omega, show (2 * q + 1) - 1 = 2 * q + 0 by omega]
      ring
  rw [show p + 6 - 2 = p + 4 by omega, show p + 6 - 4 = p + 2 by omega, show p + 6 - 6 = p by omega]
  exact_mod_cast h
theorem G : (mk (fun n => (a n : ℤ))) * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 - 4 * X) * (1 + 4 * X)) = 1 + 6 * X - 17 * X ^ 2 - 3 * X ^ 3 + 16 * X ^ 4 - 48 * X ^ 5 := by
  have k : (mk (fun n => (a n : ℤ))) * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 - 4 * X) * (1 + 4 * X)) = 1 + 6 * X - 17 * X ^ 2 - 3 * X ^ 3 + 16 * X ^ 4 - 48 * X ^ 5 := by
    rw [show (mk (fun n => (a n : ℤ))) * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 - 4 * X) * (1 + 4 * X)) = C (1 : ℤ) * (mk (fun n => (a n : ℤ))) + C (-21 : ℤ) * ((mk (fun n => (a n : ℤ))) * X ^ 2) + C (84 : ℤ) * ((mk (fun n => (a n : ℤ))) * X ^ 4) + C (-64 : ℤ) * ((mk (fun n => (a n : ℤ))) * X ^ 6) by simp only [map_neg, map_ofNat, map_one]; ring,
      show (1 + 6 * X - 17 * X ^ 2 - 3 * X ^ 3 + 16 * X ^ 4 - 48 * X ^ 5 : ℤ⟦X⟧) = C (1 : ℤ) + C (6 : ℤ) * X ^ 1 + C (-17 : ℤ) * X ^ 2 + C (-3 : ℤ) * X ^ 3 + C (16 : ℤ) * X ^ 4 + C (-48 : ℤ) * X ^ 5 by simp only [map_neg, map_ofNat, map_one]; ring]
    ext n
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_C]
    rcases Nat.lt_or_ge n 6 with hn | hn
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      simp only [show 1 ≤ m + 6 by omega, show 2 ≤ m + 6 by omega, show 3 ≤ m + 6 by omega, show 4 ≤ m + 6 by omega, show 5 ≤ m + 6 by omega, show 6 ≤ m + 6 by omega, show m + 6 ≠ 0 by omega, show m + 6 - 1 ≠ 0 by omega, show m + 4 ≠ 0 by omega, show m + 6 - 3 ≠ 0 by omega, show m + 2 ≠ 0 by omega, show m + 6 - 5 ≠ 0 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 6 = m + 0 by omega, ↓reduceIte]
      have h := (R (m + 6) (by omega))
      simp only [show m + 6 - 2 = m + 4 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 6 = m + 0 by omega] at h
      linear_combination h
  exact k

end OMA.A266850Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a266850.main := ⟨OMA.A266850Proof.R, OMA.A266850Proof.G⟩
