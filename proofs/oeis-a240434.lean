import OMAStatements.S_oeis_a240434

-- Problem: A240434 (statement of PR #7604). By Pascal's rule a(n+1) = 2 a(n) + 4 sum_k C(n,k) (k+1)^2, and
-- sum_k C(n,k) (k+1)^2 = 2^n (n+1)(n+4)/4, so by induction a(n) = 2^n n (n+1)(n+5)/6, the closed form.
-- The generating function: the coefficients of mk a * (1 - 2X)^4 are a fourth finite difference of
-- 2^n times a cubic, hence 0 from n = 4 on; n = 0..3 give 0, 4, -4, 0, i.e. 4X(1 - X).

namespace OMA.A240434Q

open Finset

lemma pascal (f : ℕ → ℚ) (n : ℕ) :
    ∑ k ∈ range (n + 2), ((n + 1).choose k : ℚ) * f k
      = ∑ k ∈ range (n + 1), (n.choose k : ℚ) * f k
        + ∑ k ∈ range (n + 1), (n.choose k : ℚ) * f (k + 1) := by
  rw [sum_range_succ' _ (n + 1)]
  simp only [Nat.choose_succ_succ, Nat.cast_add, add_mul, sum_add_distrib, Nat.choose_zero_right]
  rw [sum_range_succ (fun k => (n.choose (k + 1) : ℚ) * f (k + 1)), Nat.choose_succ_self,
    Nat.cast_zero, zero_mul, add_zero, sum_range_succ' (fun k => (n.choose k : ℚ) * f k),
    Nat.choose_zero_right]
  ring

lemma ess_succ (k : ℕ) : OMA.S_oeis_a240434.evenSquareSum (k + 1)
    = OMA.S_oeis_a240434.evenSquareSum k + 4 * ((k : ℚ) + 1) ^ 2 := by
  unfold OMA.S_oeis_a240434.evenSquareSum
  rw [sum_range_succ]; ring

lemma d_eq (n : ℕ) : ∑ k ∈ range (n + 1), (n.choose k : ℚ) * (2 * k + 3) = (2 : ℚ) ^ n * ((n : ℚ) + 3) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pascal (fun k => 2 * (k : ℚ) + 3)]
    have : ∑ k ∈ range (n + 1), (n.choose k : ℚ) * (2 * ((k + 1 : ℕ) : ℚ) + 3)
        = ∑ k ∈ range (n + 1), (n.choose k : ℚ) * (2 * k + 3)
          + 2 * ∑ k ∈ range (n + 1), (n.choose k : ℚ) := by
      rw [mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun k _ => by push_cast; ring
    have h2 : ∑ k ∈ range (n + 1), (n.choose k : ℚ) = 2 ^ n := by exact_mod_cast Nat.sum_range_choose n
    simp only [Nat.cast_add, Nat.cast_one] at this ⊢
    rw [this, ih, h2]; push_cast; ring

lemma c_eq (n : ℕ) : ∑ k ∈ range (n + 1), (n.choose k : ℚ) * ((k : ℚ) + 1) ^ 2
    = (2 : ℚ) ^ n * ((n : ℚ) + 1) * ((n : ℚ) + 4) / 4 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pascal (fun k => ((k : ℚ) + 1) ^ 2)]
    have : ∑ k ∈ range (n + 1), (n.choose k : ℚ) * (((k + 1 : ℕ) : ℚ) + 1) ^ 2
        = ∑ k ∈ range (n + 1), (n.choose k : ℚ) * ((k : ℚ) + 1) ^ 2
          + ∑ k ∈ range (n + 1), (n.choose k : ℚ) * (2 * k + 3) := by
      rw [← sum_add_distrib]; exact sum_congr rfl fun k _ => by push_cast; ring
    rw [this, d_eq, ih]; push_cast; ring

lemma a_eq (n : ℕ) : OMA.S_oeis_a240434.a n = (2 : ℚ) ^ n * n * ((n : ℚ) + 1) * ((n : ℚ) + 5) / 6 := by
  induction n with
  | zero => simp [OMA.S_oeis_a240434.a, OMA.S_oeis_a240434.evenSquareSum]
  | succ n ih =>
    unfold OMA.S_oeis_a240434.a at ih ⊢
    rw [pascal OMA.S_oeis_a240434.evenSquareSum]
    have h1 : ∑ k ∈ range (n + 1), (n.choose k : ℚ) * OMA.S_oeis_a240434.evenSquareSum (k + 1)
        = ∑ k ∈ range (n + 1), (n.choose k : ℚ) * OMA.S_oeis_a240434.evenSquareSum k
          + 4 * ∑ k ∈ range (n + 1), (n.choose k : ℚ) * ((k : ℚ) + 1) ^ 2 := by
      rw [mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun k _ => by rw [ess_succ]; ring
    rw [h1, ih, c_eq]; push_cast; ring

end OMA.A240434Q

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a240434.main := by
  refine ⟨fun n => ?_, ?_⟩
  · rw [OMA.A240434Q.a_eq]
    rcases n with _ | n
    · simp
    · rw [Nat.add_sub_cancel, pow_succ]; push_cast; ring
  · have hpoly : ((1 : PowerSeries ℚ) - PowerSeries.C 2 * PowerSeries.X) ^ 4
        = 1 - C 8 * X ^ 1 + C 24 * X ^ 2 - C 32 * X ^ 3 + C 16 * X ^ 4 := by
      simp only [map_ofNat]; ring
    have hrhs : (4 : PowerSeries ℚ) * X * (1 - X) = C 4 * X ^ 1 - C 4 * X ^ 2 := by
      simp only [map_ofNat]; ring
    have hco : ∀ (f : PowerSeries ℚ) (c : ℚ) (k n : ℕ),
        coeff n (f * (C c * X ^ k)) = if k ≤ n then c * coeff (n - k) f else 0 := by
      intro f c k n
      rw [show f * (C c * X ^ k) = f * X ^ k * C c by ring, coeff_mul_C, coeff_mul_X_pow']
      split_ifs <;> simp [mul_comm]
    have hco1 : ∀ (f : PowerSeries ℚ) (c : ℚ) (n : ℕ),
        coeff n (f * (C c * X)) = if 1 ≤ n then c * coeff (n - 1) f else 0 := by
      intro f c n; rw [← hco, pow_one]
    rw [hpoly, hrhs]
    ext n
    simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mk, coeff_C_mul_X_pow]
    simp only [hco, hco1, coeff_mk]
    rcases n with _ | _ | _ | _ | m
    · simp [OMA.A240434Q.a_eq]
    · simp [OMA.A240434Q.a_eq]; norm_num
    · simp [OMA.A240434Q.a_eq]; norm_num
    · simp [OMA.A240434Q.a_eq]; norm_num
    · simp only [show 1 ≤ m + 4 by omega, show 2 ≤ m + 4 by omega, show 3 ≤ m + 4 by omega,
        show 4 ≤ m + 4 by omega, if_true, show m + 4 ≠ 1 by omega, show m + 4 ≠ 2 by omega, if_false,
        show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
        show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega, OMA.A240434Q.a_eq]
      push_cast; ring
