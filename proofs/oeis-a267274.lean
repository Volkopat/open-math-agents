import OMAStatements.S_oeis_a267274

namespace OMA.A267274Proof
open OMA.S_oeis_a267274 PowerSeries

def P (r t : ℕ) (x : ℤ) : Bool :=
  if t = 0 then (if x = 0 then true else false)
  else if t = 1 ∧ r = 117 then (if x = -1 then false else true)
  else if t % 2 = 0 then (if x = -t ∨ x = 1 - t then true else false)
  else (if x = -t ∨ x = 1 - t then false else true)

theorem S (r : ℕ) (hr : r = 117 ∨ r = 81) (t : ℕ) : ∀ x, state r t x = P r t x := by
  induction t with
  | zero => intro x; simp [state, P]
  | succ t ih =>
    intro x
    simp only [state, step, ih, P]
    push_cast
    rcases hr with rfl | rfl <;> split_ifs <;> first | rfl | (exfalso; omega)

theorem L (n i : ℕ) (hn : 2 ≤ n) (hi : i < 2 * n + 1) :
    (P 117 n (n - i)).toNat = if i < 2 * n - 1 then n % 2 else 1 - n % 2 := by
  simp only [P]
  split_ifs <;> first | (exfalso; omega) | contradiction | (simp; omega)

theorem V (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = ((-4) ^ n + (-1) ^ n + 2 ^ (2 * n + 1) - 1) / 2 := by
  have e : a n = ∑ i ∈ Finset.range (2 * n - 1), n % 2 * 2 ^ i + (1 - n % 2) * (2 ^ (2 * n - 1) + 2 ^ (2 * n)) := by
    simp only [a, rowValue, S 117 (by norm_num)]
    rw [show 2 * n + 1 = 2 * n - 1 + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_congr rfl fun i hi => by rw [L n i hn (by simp at hi; omega), if_pos (by simp at hi; omega)],
      L n _ hn (by omega), L n _ hn (by omega), if_neg (by omega), if_neg (by omega),
      show 2 * n - 1 + 1 = 2 * n by omega]
    ring
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  rw [e, show 2 * (p + 1) - 1 = 2 * p + 1 by omega]
  push_cast
  rw [← Finset.mul_sum, geom_sum_eq (by norm_num)]
  rcases Nat.even_or_odd p with h | h
  · rw [show (p + 1) % 2 = 1 by have := Nat.even_iff.1 h; omega, (h.add_one).neg_pow, (h.add_one).neg_one_pow, show (4 : ℚ) ^ (p + 1) = 2 ^ (2 * (p + 1)) by rw [pow_mul]; norm_num]
    push_cast; ring
  · rw [show (p + 1) % 2 = 0 by have := Nat.odd_iff.1 h; omega, (h.add_one).neg_pow, (h.add_one).neg_one_pow, show (4 : ℚ) ^ (p + 1) = 2 ^ (2 * (p + 1)) by rw [pow_mul]; norm_num]
    push_cast; ring

theorem R (n : ℕ) (hn : 5 < n) : (a n : ℤ) = 17 * a (n - 2) - 16 * a (n - 4) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 6 := ⟨n - 6, by omega⟩
  have h : (a (p + 6) : ℚ) = 17 * a (p + 4) - 16 * a (p + 2) := by
    rw [V _ (by omega), V _ (by omega), V _ (by omega)]; ring
  rw [show p + 6 - 2 = p + 4 by omega, show p + 6 - 4 = p + 2 by omega]
  exact_mod_cast h

theorem G : A = (1 + 3 * X + 7 * X ^ 2 - 20 * X ^ 3 - 8 * X ^ 4 + 32 * X ^ 5) *
      ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X))⁻¹ := by
  have hd : constantCoeff (((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X)) : ℚ⟦X⟧) ≠ 0 := by simp
  have k : A * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X)) = 1 + 3 * X + 7 * X ^ 2 - 20 * X ^ 3 - 8 * X ^ 4 + 32 * X ^ 5 := by
    rw [show A * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X)) = C (1 : ℚ) * A + C (-17 : ℚ) * (A * X ^ 2) + C (16 : ℚ) * (A * X ^ 4) by
      simp only [map_neg, map_ofNat, map_one]; ring,
      show (1 + 3 * X + 7 * X ^ 2 - 20 * X ^ 3 - 8 * X ^ 4 + 32 * X ^ 5 : ℚ⟦X⟧) = C (1 : ℚ) + C (3 : ℚ) * X ^ 1 + C (7 : ℚ) * X ^ 2 + C (-20 : ℚ) * X ^ 3 + C (-8 : ℚ) * X ^ 4 + C (32 : ℚ) * X ^ 5 by
      simp only [map_neg, map_ofNat, map_one]; ring]
    ext n
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk, coeff_C]
    rcases Nat.lt_or_ge n 6 with hn | hn
    · have a0 : a 0 = 1 := rfl
      have a1 : a 1 = 3 := by decide
      interval_cases n <;> norm_num [a0, a1, V]
    · have := R n (by omega)
      have h2 : ((a n : ℤ) : ℚ) = 17 * a (n - 2) - 16 * a (n - 4) := by exact_mod_cast this
      simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega,
        show n ≠ 0 by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
        show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega, ↓reduceIte]
      push_cast at h2
      linear_combination h2
  rw [← k, mul_assoc, PowerSeries.mul_inv_cancel _ hd, mul_one]

theorem M : type_of% @OMA.S_oeis_a267274.main := by
  refine ⟨V, fun n hn => ?_, R, G⟩
  have e : ∀ x, P 117 n x = P 81 n x := fun x => by simp [P, show n ≠ 0 by omega, show n ≠ 1 by omega]
  simp only [a, b, rowValue, S 117 (by norm_num), S 81 (by norm_num), e]

end OMA.A267274Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a267274.main := OMA.A267274Proof.M
