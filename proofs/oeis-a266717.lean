import OMAStatements.S_oeis_a266717

namespace OMA.A266717Proof
open OMA.S_oeis_a266717 PowerSeries

def P (t : ℕ) (x : ℤ) : Bool :=
  if t = 0 then (if x = 0 then true else false) else if t % 2 = 1 then (if 2 * x = t - 1 then false else true) else (if 2 * x = t - 2 ∨ 2 * x = t then true else false)

theorem S (t : ℕ) : ∀ x, state t x = P t x := by
  induction t with
  | zero => intro x; simp [state, P]
  | succ t ih =>
    intro x
    simp only [state, eca, ih, P]
    push_cast
    split_ifs <;> first | rfl | (exfalso; omega)

theorem T (N : ℕ) : ∑ k ∈ Finset.range (N + 1), (10 : ℚ) ^ (N - k) = (10 ^ (N + 1) - 1) / 9 := by
  have := Finset.sum_range_reflect (fun k => (10 : ℚ) ^ k) (N + 1)
  simp only [Nat.add_sub_cancel] at this
  rw [this, geom_sum_eq (by norm_num)]
  norm_num

theorem V (n : ℕ) : (a n : ℚ) = ∑ k ∈ Finset.range (2 * n + 1), if P n ((k : ℤ) - n) then (10 : ℚ) ^ (2 * n - k) else 0 := by
  simp only [a, S]
  push_cast
  rfl

theorem E (n : ℕ) (h : n % 2 = 0) (hn : 0 < n) : (a n : ℚ) = 10 ^ (n - n / 2 + 1) + 10 ^ (n - n / 2) := by
  rw [V, Finset.sum_eq_add (n + n / 2 - 1) (n + n / 2) (by omega)]
  · simp only [P, h]
    split_ifs <;> first | (exfalso; omega) | contradiction | rw [show 2 * n - (n + n / 2 - 1) = n - n / 2 + 1 by omega, show 2 * n - (n + n / 2) = n - n / 2 by omega]
  · intro k _ hk
    simp only [P, h]
    split_ifs <;> first | (exfalso; omega) | rfl
  · intro hk; simp at hk; omega
  · intro hk; simp at hk; omega
theorem O (n : ℕ) (h : n % 2 = 1) : (a n : ℚ) = (10 ^ (2 * n + 1) - 1) / 9 - 10 ^ (n - (n - 1) / 2) := by
  rw [V, Finset.sum_congr rfl (g := fun k => (10 : ℚ) ^ (2 * n - k) - if k = n + (n - 1) / 2 then 10 ^ (2 * n - k) else 0),
    Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (by simp; omega), T, show 2 * n - (n + (n - 1) / 2) = n - (n - 1) / 2 by omega]
  intro k _
  simp only [P, h, ↓reduceIte]
  split_ifs <;> first | (exfalso; omega) | contradiction | simp

theorem R (n : ℕ) (hn : 6 < n) : (a n : ℤ) = 10011 * a (n - 2) - 110010 * a (n - 4) + 100000 * a (n - 6) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 7 := ⟨n - 7, by omega⟩
  have h : (a (p + 7) : ℚ) = 10011 * a (p + 5) - 110010 * a (p + 3) + 100000 * a (p + 1) := by
    rcases Nat.even_or_odd p with ⟨q, hq⟩ | ⟨q, hq⟩ <;> subst hq
    · rw [O _ (by omega), O _ (by omega), O _ (by omega), O _ (by omega), show (q + q + 7) - ((q + q + 7) - 1) / 2 = 1 * q + 4 by omega, show (q + q + 5) - ((q + q + 5) - 1) / 2 = 1 * q + 3 by omega, show (q + q + 3) - ((q + q + 3) - 1) / 2 = 1 * q + 2 by omega, show (q + q + 1) - ((q + q + 1) - 1) / 2 = 1 * q + 1 by omega]
      ring
    · rw [E _ (by omega) (by omega), E _ (by omega) (by omega), E _ (by omega) (by omega), E _ (by omega) (by omega), show (2 * q + 1 + 7) - (2 * q + 1 + 7) / 2 + 1 = 1 * q + 5 by omega, show (2 * q + 1 + 7) - (2 * q + 1 + 7) / 2 = 1 * q + 4 by omega, show (2 * q + 1 + 5) - (2 * q + 1 + 5) / 2 + 1 = 1 * q + 4 by omega, show (2 * q + 1 + 5) - (2 * q + 1 + 5) / 2 = 1 * q + 3 by omega, show (2 * q + 1 + 3) - (2 * q + 1 + 3) / 2 + 1 = 1 * q + 3 by omega, show (2 * q + 1 + 3) - (2 * q + 1 + 3) / 2 = 1 * q + 2 by omega, show (2 * q + 1 + 1) - (2 * q + 1 + 1) / 2 + 1 = 1 * q + 2 by omega, show (2 * q + 1 + 1) - (2 * q + 1 + 1) / 2 = 1 * q + 1 by omega]
      ring
  rw [show p + 7 - 2 = p + 5 by omega, show p + 7 - 4 = p + 3 by omega, show p + 7 - 6 = p + 1 by omega]
  exact_mod_cast h
theorem G : (mk (fun n => (a n : ℤ))) * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 - 10 * X ^ 2)) = 1 + 101 * X - 9901 * X ^ 2 + 99900 * X ^ 3 - 990100 * X ^ 4 - 110000 * X ^ 5 + 1000000 * X ^ 6 := by
  have k : (mk (fun n => (a n : ℤ))) * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 - 10 * X ^ 2)) = 1 + 101 * X - 9901 * X ^ 2 + 99900 * X ^ 3 - 990100 * X ^ 4 - 110000 * X ^ 5 + 1000000 * X ^ 6 := by
    rw [show (mk (fun n => (a n : ℤ))) * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 - 10 * X ^ 2)) = C (1 : ℤ) * (mk (fun n => (a n : ℤ))) + C (-10011 : ℤ) * ((mk (fun n => (a n : ℤ))) * X ^ 2) + C (110010 : ℤ) * ((mk (fun n => (a n : ℤ))) * X ^ 4) + C (-100000 : ℤ) * ((mk (fun n => (a n : ℤ))) * X ^ 6) by simp only [map_neg, map_ofNat, map_one]; ring,
      show (1 + 101 * X - 9901 * X ^ 2 + 99900 * X ^ 3 - 990100 * X ^ 4 - 110000 * X ^ 5 + 1000000 * X ^ 6 : ℤ⟦X⟧) = C (1 : ℤ) + C (101 : ℤ) * X ^ 1 + C (-9901 : ℤ) * X ^ 2 + C (99900 : ℤ) * X ^ 3 + C (-990100 : ℤ) * X ^ 4 + C (-110000 : ℤ) * X ^ 5 + C (1000000 : ℤ) * X ^ 6 by simp only [map_neg, map_ofNat, map_one]; ring]
    ext n
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_C]
    rcases Nat.lt_or_ge n 7 with hn | hn
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
      simp only [show 1 ≤ m + 7 by omega, show 2 ≤ m + 7 by omega, show 3 ≤ m + 7 by omega, show 4 ≤ m + 7 by omega, show 5 ≤ m + 7 by omega, show 6 ≤ m + 7 by omega, show m + 7 ≠ 0 by omega, show m + 7 - 1 ≠ 0 by omega, show m + 5 ≠ 0 by omega, show m + 7 - 3 ≠ 0 by omega, show m + 3 ≠ 0 by omega, show m + 7 - 5 ≠ 0 by omega, show m + 1 ≠ 0 by omega, show m + 7 - 2 = m + 5 by omega, show m + 7 - 4 = m + 3 by omega, show m + 7 - 6 = m + 1 by omega, ↓reduceIte]
      have h := (R (m + 7) (by omega))
      simp only [show m + 7 - 2 = m + 5 by omega, show m + 7 - 4 = m + 3 by omega, show m + 7 - 6 = m + 1 by omega] at h
      linear_combination h
  exact k

end OMA.A266717Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a266717.main := ⟨OMA.A266717Proof.R, OMA.A266717Proof.G⟩
