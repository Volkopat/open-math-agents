import OMAStatements.S_oeis_a267816

namespace OMA.A267816Proof
open OMA.S_oeis_a267816 PowerSeries

def P (t : ℕ) (x : ℤ) : Bool :=
  if t = 0 then (if x = 0 then true else false) else (if x = -1 then false else true)

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

theorem F (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = 2 ^ (2 * n + 1) - 1 - 2 ^ (n + 1) := by
  rw [V, Finset.sum_congr rfl (g := fun k => (2 : ℚ) ^ (2 * n - k) - (if k = n - 1 then 2 ^ (2 * n - k) else 0)), Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (by simp <;> omega), T]
  try simp only [show 2 * n - (n - 1) = n + 1 by omega]
  intro k _
  simp only [P]
  split_ifs <;> first | (exfalso; omega) | contradiction | simp

theorem R (n : ℕ) (hn : 3 < n) : (a n : ℤ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 4 := ⟨n - 4, by omega⟩
  have h : (a (p + 4) : ℚ) = 7 * a (p + 3) - 14 * a (p + 2) + 8 * a (p + 1) := by
    rw [F _ (by omega), F _ (by omega), F _ (by omega), F _ (by omega)]
    ring
  rw [show p + 4 - 1 = p + 3 by omega, show p + 4 - 2 = p + 2 by omega, show p + 4 - 3 = p + 1 by omega]
  exact_mod_cast h

theorem G : (mk (fun n => (a n : ℤ))) * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) = 1 - 4 * X + 16 * X ^ 2 - 16 * X ^ 3 := by
  have k : (mk (fun n => (a n : ℤ))) * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) = 1 - 4 * X + 16 * X ^ 2 - 16 * X ^ 3 := by
    rw [show (mk (fun n => (a n : ℤ))) * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) = C (1 : ℤ) * (mk (fun n => (a n : ℤ))) + C (-7 : ℤ) * ((mk (fun n => (a n : ℤ))) * X ^ 1) + C (14 : ℤ) * ((mk (fun n => (a n : ℤ))) * X ^ 2) + C (-8 : ℤ) * ((mk (fun n => (a n : ℤ))) * X ^ 3) by simp only [map_neg, map_ofNat, map_one]; ring,
      show (1 - 4 * X + 16 * X ^ 2 - 16 * X ^ 3 : ℤ⟦X⟧) = C (1 : ℤ) + C (-4 : ℤ) * X ^ 1 + C (16 : ℤ) * X ^ 2 + C (-16 : ℤ) * X ^ 3 by simp only [map_neg, map_ofNat, map_one]; ring]
    ext n
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_C]
    rcases Nat.lt_or_ge n 4 with hn | hn
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      simp only [show 1 ≤ m + 4 by omega, show 2 ≤ m + 4 by omega, show 3 ≤ m + 4 by omega, show m + 4 ≠ 0 by omega, show m + 3 ≠ 0 by omega, show m + 2 ≠ 0 by omega, show m + 1 ≠ 0 by omega, show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega, ↓reduceIte]
      have h := (R (m + 4) (by omega))
      simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega] at h
      linear_combination h
  exact k

end OMA.A267816Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a267816.main := ⟨OMA.A267816Proof.R, OMA.A267816Proof.G⟩
