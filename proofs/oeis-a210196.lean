import OMAStatements.S_oeis_a210196
import Mathlib

open Polynomial OMA.S_oeis_a210196

private theorem eliminate_u (r : ℕ) : (2*X)*u (r+1)+1 = v (r+1)+2*X := by
  cases r with
  | zero => simp [u, v, add_comm]
  | succ r => rw [u, v]; ring

private theorem closed (r : ℕ) : v (r+1)+1 = 2*(1+2*X)^r := by
  induction r with
  | zero => simp [v]; norm_num
  | succ r ih =>
    calc
      v (r+2)+1 = (v (r+1)+1)*(1+2*X) := by
        rw [v]
        linear_combination eliminate_u r
      _ = _ := by rw [ih,pow_succ]; ring

private theorem coefficients (r k : ℕ) :
    ((1+2*X : ℤ[X])^r).coeff k = 2^k*(r.choose k : ℤ) := by
  induction r generalizing k with
  | zero => cases k <;> simp [Polynomial.coeff_one]
  | succ r ih =>
    rw [pow_succ, mul_add, mul_one, ← mul_assoc, coeff_add]
    cases k with
    | zero => simp [ih]
    | succ k =>
      simp only [coeff_mul_X, coeff_mul_ofNat, ih, Nat.choose_succ_succ, Nat.cast_add,
        pow_succ (2 : ℤ) k]
      ring

theorem OMA.solution : type_of% @OMA.S_oeis_a210196.main := by
  rintro (_ | r) hn
  · omega
  have co (k : ℕ) := congrArg (fun P : ℤ[X] => P.coeff k) (closed r)
  simp only [coeff_add, coeff_ofNat_mul, coefficients] at co
  constructor
  · have e := co 0
    simp [T] at e ⊢
    omega
  · rintro (_ | k) hk _
    · omega
    have e := co (k+1)
    simp only [Polynomial.coeff_one, Nat.succ_ne_zero, ↓reduceIte, add_zero] at e
    change (v (r+1)).coeff (k+1) = _
    rw [e, Nat.add_sub_cancel, pow_succ (2:ℤ) (k+1)]
    ring
