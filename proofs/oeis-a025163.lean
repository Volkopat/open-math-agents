import OMAStatements.S_oeis_a025163
import Mathlib

/-!
OEIS A025163: the three-term recurrence for a(n) = 2^(3n/2 - 1) * P_n^1(2^(-1/2)).

Write P n and D n for the values at a real point x of the n-th Legendre polynomial and of its
derivative. From the defining recurrence (n+2) P(n+2) = (2n+3) x P(n+1) - (n+1) P(n) and its
derivative we prove together, by induction on n,
  D(n+1) = x D(n) + (n+1) P(n),
  x D(n+1) - D(n) = (n+1) P(n+1),
  (x^2 - 1) D(n+1) = (n+1) (x P(n+1) - P(n)).
The first two give (n+1) D(n+2) = (2n+3) x D(n+1) - (n+2) D(n), and the statement follows at
x = 2^(-1/2), where x^2 = 1/2 and 2^(3/2) x = 2.
-/

namespace OMA.A025163

open OMA.S_oeis_a025163 Polynomial

lemma p_rec (x : ℝ) (n : ℕ) :
    ((n : ℝ) + 2) * (legendrePoly (n + 2)).eval x =
      (2 * (n : ℝ) + 3) * x * (legendrePoly (n + 1)).eval x -
        ((n : ℝ) + 1) * (legendrePoly n).eval x := by
  have h : ((n : ℝ) + 2) ≠ 0 := by positivity
  rw [legendrePoly]
  simp only [eval_sub, eval_smul, eval_mul, eval_X, smul_eq_mul]
  field_simp

lemma d_rec (x : ℝ) (n : ℕ) :
    ((n : ℝ) + 2) * (derivative (legendrePoly (n + 2))).eval x =
      (2 * (n : ℝ) + 3) *
          ((legendrePoly (n + 1)).eval x + x * (derivative (legendrePoly (n + 1))).eval x) -
        ((n : ℝ) + 1) * (derivative (legendrePoly n)).eval x := by
  have h : ((n : ℝ) + 2) ≠ 0 := by positivity
  rw [legendrePoly]
  simp only [derivative_sub, derivative_smul, derivative_mul, derivative_X, eval_sub, eval_smul,
    eval_mul, eval_add, eval_X, one_mul, smul_eq_mul]
  field_simp

lemma key (x : ℝ) (n : ℕ) :
    ((derivative (legendrePoly (n + 1))).eval x =
        x * (derivative (legendrePoly n)).eval x + ((n : ℝ) + 1) * (legendrePoly n).eval x) ∧
    (x * (derivative (legendrePoly (n + 1))).eval x - (derivative (legendrePoly n)).eval x =
        ((n : ℝ) + 1) * (legendrePoly (n + 1)).eval x) ∧
    ((x ^ 2 - 1) * (derivative (legendrePoly (n + 1))).eval x =
        ((n : ℝ) + 1) * (x * (legendrePoly (n + 1)).eval x - (legendrePoly n).eval x)) := by
  induction n with
  | zero =>
    simp [legendrePoly]
    ring
  | succ n ih =>
    obtain ⟨-, hB, hC⟩ := ih
    have pr := p_rec x n
    have dr := d_rec x n
    have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
    have hA' : (derivative (legendrePoly (n + 2))).eval x =
        x * (derivative (legendrePoly (n + 1))).eval x +
          ((n : ℝ) + 2) * (legendrePoly (n + 1)).eval x := by
      apply mul_left_cancel₀ h2
      linear_combination dr + ((n : ℝ) + 1) * hB
    simp only [show n + 1 + 1 = n + 2 from rfl]
    refine ⟨?_, ?_, ?_⟩
    · push_cast
      linear_combination hA'
    · push_cast
      linear_combination x * hA' + hC - pr
    · push_cast
      linear_combination (x ^ 2 - 1) * hA' + x * hC - x * pr

end OMA.A025163

open OMA.S_oeis_a025163 Polynomial in
theorem OMA.solution : type_of% @OMA.S_oeis_a025163.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := rfl
  have e2 : m + 2 - 2 = m := rfl
  rw [e1, e2]
  unfold a
  have hpos : (0 : ℝ) < 2 := by norm_num
  have hxx : ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num
  have hRx : (2 : ℝ) ^ ((3 : ℝ) / 2) * (2 : ℝ) ^ (-(1 / 2 : ℝ)) = 2 := by
    rw [← Real.rpow_add hpos]
    norm_num
  have h1 : (2 : ℝ) ^ (3 * (((m + 1 : ℕ) : ℝ)) / 2 - 1) =
      (2 : ℝ) ^ (3 * (m : ℝ) / 2 - 1) * (2 : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [← Real.rpow_add hpos]
    congr 1
    push_cast
    ring
  have h2 : (2 : ℝ) ^ (3 * (((m + 2 : ℕ) : ℝ)) / 2 - 1) =
      (2 : ℝ) ^ (3 * (m : ℝ) / 2 - 1) * 8 := by
    have h8 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by norm_num
    rw [h8, ← Real.rpow_add hpos]
    congr 1
    push_cast
    ring
  rw [h1, h2]
  generalize (2 : ℝ) ^ (-(1 / 2 : ℝ)) = x at hxx hRx ⊢
  generalize (2 : ℝ) ^ (3 * (m : ℝ) / 2 - 1) = S
  generalize (2 : ℝ) ^ ((3 : ℝ) / 2) = R at hRx ⊢
  obtain ⟨hA1, -, -⟩ := OMA.A025163.key x (m + 1)
  obtain ⟨-, hB0, -⟩ := OMA.A025163.key x m
  simp only [show m + 1 + 1 = m + 2 from rfl] at hA1
  push_cast at hA1 ⊢
  have hrec : ((m : ℝ) + 1) * (derivative (legendrePoly (m + 2))).eval x =
      (2 * (m : ℝ) + 3) * x * (derivative (legendrePoly (m + 1))).eval x -
        ((m : ℝ) + 2) * (derivative (legendrePoly m)).eval x := by
    linear_combination ((m : ℝ) + 1) * hA1 - ((m : ℝ) + 2) * hB0
  linear_combination 8 * S * x * hrec +
    8 * (2 * (m : ℝ) + 3) * S * (derivative (legendrePoly (m + 1))).eval x * hxx -
    2 * (2 * (m : ℝ) + 3) * S * (derivative (legendrePoly (m + 1))).eval x * hRx
