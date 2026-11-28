import OMAStatements.S_oeis_a108306
import Mathlib

open OMA.S_oeis_a108306
open PowerSeries

namespace P108306

theorem inv_succ (f : ℕ → ℤ) (n : ℕ) :
    invert f (n + 1) = ∑ k ∈ Finset.range (n + 1), f (k + 1) * invert f (n - k) := by
  rw [invert, Fin.sum_univ_eq_sum_range (fun k => f (k + 1) * invert f (n - k))]

/-- `W n = Sum_(j = 0..n) b^j * t(n - j)`. -/
def W (a b : ℤ) (n : ℕ) : ℤ := ∑ j ∈ Finset.range (n + 1), b ^ j * invert (s a b) (n - j)

theorem t2 (a b : ℤ) (n : ℕ) :
    invert (s a b) (n + 2) = invert (s a b) (n + 1) + a * W a b n := by
  rw [inv_succ, Finset.sum_range_succ', W, Finset.mul_sum]
  simp only [s, Nat.sub_zero, one_mul]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [show n + 1 - (k + 1) = n - k by omega]
  ring

theorem W_succ (a b : ℤ) (n : ℕ) : W a b (n + 1) = invert (s a b) (n + 1) + b * W a b n := by
  rw [W, Finset.sum_range_succ', W, Finset.mul_sum]
  simp only [pow_zero, one_mul, Nat.sub_zero]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [show n + 1 - (k + 1) = n - k by omega]
  ring

theorem t0 (a b : ℤ) : invert (s a b) 0 = 1 := by rw [invert]
theorem t1 (a b : ℤ) : invert (s a b) 1 = 1 := by rw [inv_succ]; simp [s, t0]

theorem trec (a b : ℤ) (n : ℕ) :
    invert (s a b) (n + 2) = (1 + b) * invert (s a b) (n + 1) - (b - a) * invert (s a b) n := by
  rcases n with _ | n
  · rw [t2, t1, W]; simp [t0]; ring
  · have h1 := t2 a b (n + 1)
    have h2 := t2 a b n
    rw [W_succ] at h1
    rw [h1]
    linear_combination (-b) * h2

theorem Mrec (a b : ℤ) (n : ℕ) :
    (M a b ^ (n + 2)) 0 0 = (1 + b) * (M a b ^ (n + 1)) 0 0 - (b - a) * (M a b ^ n) 0 0 := by
  rw [show M a b ^ (n + 2) = M a b ^ n * (M a b * M a b) by rw [pow_add, pow_two],
    show M a b ^ (n + 1) = M a b ^ n * M a b from pow_succ _ _]
  simp [Matrix.mul_apply, Fin.sum_univ_two, M]
  ring

theorem general (a b : ℤ) (n : ℕ) : invert (s a b) n = (M a b ^ n) 0 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [t0]
    | 1, _ => simp [t1, M]
    | k + 2, ih => rw [trec, Mrec, ih k (by omega), ih (k + 1) (by omega)]

theorem A_eq : A * (1 - 3 * X - 3 * X ^ 2) = 1 + 3 * X := by
  have h : constantCoeff (1 - 3 * X - 3 * X ^ 2 : PowerSeries ℚ) ≠ 0 := by simp
  rw [A, mul_assoc, PowerSeries.inv_mul_cancel _ h, mul_one]

theorem cA (n : ℕ) : coeff n A = (invert (s 5 2) (n + 1) : ℚ) := by
  have h3 : (3 : PowerSeries ℚ) = C 3 := (map_ofNat C 3).symm
  have e : A - C 3 * (X * A) - C 3 * (X * (X * A)) = 1 + C 3 * X := by
    rw [← h3]; linear_combination A_eq
  have c0 : coeff 0 A = 1 := by
    have := congrArg (coeff 0) e
    simpa using this
  have c1 : coeff 1 A = 6 := by
    have := congrArg (coeff 1) e
    simp [coeff_succ_X_mul, c0] at this
    linarith
  have hc : ∀ m, coeff (m + 2) A = 3 * coeff (m + 1) A + 3 * coeff m A := by
    intro m
    have := congrArg (coeff (m + 2)) e
    simp [coeff_succ_X_mul] at this
    linarith
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rw [c0, t1]; simp
    | 1, _ => rw [c1, trec, t1, t0]; norm_num
    | k + 2, ih =>
      rw [hc, ih k (by omega), ih (k + 1) (by omega), trec 5 2 (k + 1)]
      push_cast; ring

end P108306

theorem OMA.solution : type_of% @OMA.S_oeis_a108306.main := by
  refine ⟨fun a b n _ => P108306.general a b n, fun n => ⟨P108306.cA n, ?_⟩⟩
  rw [P108306.cA, P108306.general]
