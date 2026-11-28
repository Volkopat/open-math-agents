import OMAStatements.S_oeis_a267002

namespace OMA.A267002Proof
open OMA.S_oeis_a267002 PowerSeries

def P (t : ℕ) (x : ℤ) : Bool :=
  if t % 2 = 0 then (if 2 * x = -t then true else false) else (if 2 * x = 1 - t then false else true)

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

theorem E (n : ℕ) (h : n % 2 = 0) : (a n : ℚ) = 10 ^ (n + n / 2) := by
  rw [V, Finset.sum_eq_single (n - n / 2)]
  · simp only [P, h]
    split_ifs <;> first | (exfalso; omega) | contradiction | rw [show 2 * n - (n - n / 2) = n + n / 2 by omega]
  · intro k _ hk
    simp only [P, h]
    split_ifs <;> first | (exfalso; omega) | rfl
  · intro hn; simp at hn; omega
theorem O (n : ℕ) (h : n % 2 = 1) : (a n : ℚ) = (10 ^ (2 * n + 1) - 1) / 9 - 10 ^ (n + (n - 1) / 2) := by
  rw [V, Finset.sum_congr rfl (g := fun k => (10 : ℚ) ^ (2 * n - k) - if k = n - (n - 1) / 2 then 10 ^ (2 * n - k) else 0),
    Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (by simp; omega), T, show 2 * n - (n - (n - 1) / 2) = n + (n - 1) / 2 by omega]
  intro k _
  simp only [P, h, ↓reduceIte]
  split_ifs <;> first | (exfalso; omega) | contradiction | simp

theorem R (n : ℕ) (hn : 5 < n) : (a n : ℤ) = 11001 * a (n - 2) - 10011000 * a (n - 4) + 10000000 * a (n - 6) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 6 := ⟨n - 6, by omega⟩
  have h : (a (p + 6) : ℚ) = 11001 * a (p + 4) - 10011000 * a (p + 2) + 10000000 * a (p) := by
    rcases Nat.even_or_odd p with ⟨q, hq⟩ | ⟨q, hq⟩ <;> subst hq
    · rw [E _ (by omega), E _ (by omega), E _ (by omega), E _ (by omega), show (q + q + 6) + (q + q + 6) / 2 = 3 * q + 9 by omega, show (q + q + 4) + (q + q + 4) / 2 = 3 * q + 6 by omega, show (q + q + 2) + (q + q + 2) / 2 = 3 * q + 3 by omega, show (q + q) + (q + q) / 2 = 3 * q + 0 by omega]
      ring
    · rw [O _ (by omega), O _ (by omega), O _ (by omega), O _ (by omega), show (2 * q + 1 + 6) + ((2 * q + 1 + 6) - 1) / 2 = 3 * q + 10 by omega, show (2 * q + 1 + 4) + ((2 * q + 1 + 4) - 1) / 2 = 3 * q + 7 by omega, show (2 * q + 1 + 2) + ((2 * q + 1 + 2) - 1) / 2 = 3 * q + 4 by omega, show (2 * q + 1) + ((2 * q + 1) - 1) / 2 = 3 * q + 1 by omega]
      ring
  rw [show p + 6 - 2 = p + 4 by omega, show p + 6 - 4 = p + 2 by omega, show p + 6 - 6 = p by omega]
  exact_mod_cast h
theorem G : (mk (fun n => (a n : ℤ))) * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 - 1000 * X ^ 2)) = 1 + 101 * X - 10001 * X ^ 2 - 9990 * X ^ 3 + 10000 * X ^ 4 - 1100000 * X ^ 5 := by
  have k : (mk (fun n => (a n : ℤ))) * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 - 1000 * X ^ 2)) = 1 + 101 * X - 10001 * X ^ 2 - 9990 * X ^ 3 + 10000 * X ^ 4 - 1100000 * X ^ 5 := by
    rw [show (mk (fun n => (a n : ℤ))) * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 - 1000 * X ^ 2)) = C (1 : ℤ) * (mk (fun n => (a n : ℤ))) + C (-11001 : ℤ) * ((mk (fun n => (a n : ℤ))) * X ^ 2) + C (10011000 : ℤ) * ((mk (fun n => (a n : ℤ))) * X ^ 4) + C (-10000000 : ℤ) * ((mk (fun n => (a n : ℤ))) * X ^ 6) by simp only [map_neg, map_ofNat, map_one]; ring,
      show (1 + 101 * X - 10001 * X ^ 2 - 9990 * X ^ 3 + 10000 * X ^ 4 - 1100000 * X ^ 5 : ℤ⟦X⟧) = C (1 : ℤ) + C (101 : ℤ) * X ^ 1 + C (-10001 : ℤ) * X ^ 2 + C (-9990 : ℤ) * X ^ 3 + C (10000 : ℤ) * X ^ 4 + C (-1100000 : ℤ) * X ^ 5 by simp only [map_neg, map_ofNat, map_one]; ring]
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

end OMA.A267002Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a267002.main := ⟨OMA.A267002Proof.R, OMA.A267002Proof.G⟩
