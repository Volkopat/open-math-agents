import OMAStatements.S_oeis_a193229
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring

/-! Peter Bala's formula for the triangle OEIS A193229.

Write `T = a193229`. Comparing the sums for `T (n + 1) (k + 1)` and `T (n + 1) (k + 2)`, only the
term `i = k` differs, so `T (n + 1) (k + 1) = T (n + 1) (k + 2) + (k + 1) T n k` for `k ≤ n`; also
`T (n + 1) 0 = T (n + 1) 1` and `T (n + 1) (n + 2) = 0`. With `j = n - k`, the claim reads
`2^j j! T n k = (n + j)!`. Induct on `n`, then on `j`: the step is
`2 (j + 1) (n + j + 1)! + (k + 1) (n + j + 1)! = (n + j + 2)!`, since
`n + j + 2 = 2 (j + 1) + (k + 1)` when `n = k + 1 + j`. -/

namespace OpenMath.A193229

open Finset OMA.S_oeis_a193229

private theorem R1 (n : ℕ) : a193229 (n + 1) 0 = a193229 (n + 1) 1 := by
  rw [a193229, a193229]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [if_pos (Nat.zero_le _), if_pos (by omega)]

private theorem R2 (n k : ℕ) (hk : k ≤ n) :
    a193229 (n + 1) (k + 1) = a193229 (n + 1) (k + 1 + 1) + (k + 1) * a193229 n k := by
  have hsplit : ∀ i, (if k + 1 ≤ i + 1 then (i + 1) * a193229 n i else 0) =
      (if k + 1 + 1 ≤ i + 1 then (i + 1) * a193229 n i else 0) +
        (if i = k then (i + 1) * a193229 n i else 0) := by
    intro i
    rcases lt_trichotomy i k with h | rfl | h
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), add_zero]
    · rw [if_pos (Nat.le_refl _), if_neg (by omega), if_pos rfl, zero_add]
    · rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), add_zero]
  rw [a193229, a193229, Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib,
    Finset.sum_ite_eq', if_pos (Finset.mem_range.2 (by omega))]

private theorem R3 (n : ℕ) : a193229 (n + 1) (n + 1 + 1) = 0 := by
  rw [a193229]
  refine Finset.sum_eq_zero fun i hi => if_neg ?_
  rw [Finset.mem_range] at hi
  omega

private theorem L : ∀ n j k : ℕ, k + j = n →
    2 ^ j * j.factorial * a193229 n k = (n + j).factorial := by
  intro n
  induction n with
  | zero =>
    intro j k hk
    obtain ⟨rfl, rfl⟩ : k = 0 ∧ j = 0 := by omega
    simp [a193229]
  | succ n ih =>
    intro j
    induction j with
    | zero =>
      intro k hk
      obtain rfl : k = n + 1 := by omega
      have h0 := ih 0 n (by omega)
      simp only [pow_zero, Nat.factorial_zero, one_mul, add_zero] at h0 ⊢
      rw [R2 n n le_rfl, R3, zero_add, h0, Nat.factorial_succ]
    | succ j ihj =>
      intro k hk
      cases k with
      | zero =>
        have hA := ihj 1 (by omega)
        have e1 : 2 ^ (j + 1) * (j + 1).factorial * a193229 (n + 1) 1 =
            2 * (j + 1) * (n + 1 + j).factorial := by
          rw [← hA, pow_succ, Nat.factorial_succ]
          ring
        rw [R1, e1, show n + 1 + (j + 1) = n + 1 + j + 1 by omega, Nat.factorial_succ,
          show n + 1 + j + 1 = 2 * (j + 1) by omega]
      | succ k =>
        have hA := ihj (k + 1 + 1) (by omega)
        have hB := ih (j + 1) k (by omega)
        have e1 : 2 ^ (j + 1) * (j + 1).factorial * a193229 (n + 1) (k + 1 + 1) =
            2 * (j + 1) * (n + 1 + j).factorial := by
          rw [← hA, pow_succ, Nat.factorial_succ]
          ring
        have e2 : 2 ^ (j + 1) * (j + 1).factorial * ((k + 1) * a193229 n k) =
            (k + 1) * (n + 1 + j).factorial := by
          rw [show n + 1 + j = n + (j + 1) by omega, ← hB]
          ring
        rw [R2 n k (by omega), mul_add, e1, e2, show n + 1 + (j + 1) = n + 1 + j + 1 by omega,
          Nat.factorial_succ, show n + 1 + j + 1 = 2 * (j + 1) + (k + 1) by omega,
          add_mul (2 * (j + 1)) (k + 1)]

theorem main :
    ∀ n k : ℕ, k ≤ n →
      2 ^ (n - k) * (n - k).factorial * a193229 n k = (2 * n - k).factorial := by
  intro n k hk
  rw [L n (n - k) k (by omega), show 2 * n - k = n + (n - k) by omega]

end OpenMath.A193229

theorem OMA.solution : type_of% @OMA.S_oeis_a193229.main := OpenMath.A193229.main
