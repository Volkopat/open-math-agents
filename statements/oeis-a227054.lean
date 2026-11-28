import Mathlib

/-!
# A227054: least triangular `t > 0` with `n * t` triangular; the listed zeros

Source: https://oeis.org/A227054
Credit: @avivorly

Definition (A227054, offset 1): a(n) = least triangular number t > 0 such that n*t is a triangular number, or 0 if
no such t exists.

Claim (comment in the entry): Indices of conjectured 0's: 4, 9, 16, 25, 49, 64, 81, 121, 144, 169, 225, 256, 289,
361, 400, 441, 529, 576, 625, 729, ... These are squares of 2, 3, 4, 5, 7, 8, 9, 11, 12, 13, 15, 16, 17, 19, 20, 21,
23, 24, 25, 27.

Conventions:
- Triangular numbers are `T j = j * (j + 1) / 2` for `j ≥ 0`. A triangular number `t > 0` is `T k` with `k ≥ 1`;
  `T 0 = 0` is the excluded `t = 0`.
- `a(n) = 0` exactly when no `k ≥ 1` and no `j` satisfy `n * T k = T j`; this is `IsZero n`.
- The list is read as the zeros of the sequence in increasing order, so up to its last listed value 729 it is
  exactly the set of zeros: for `1 ≤ n ≤ 729`, `a(n) = 0` if and only if `n` is one of the 20 listed values `L`.
-/

namespace OMA.S_oeis_a227054

/-- The `k`-th triangular number `k * (k + 1) / 2`. -/
def T (k : ℕ) : ℕ := k * (k + 1) / 2

/-- `a(n) = 0`: no triangular number `t = T k > 0` (that is, `k ≥ 1`) makes `n * t` a triangular number `T j`. -/
def IsZero (n : ℕ) : Prop := ¬ ∃ k j : ℕ, 1 ≤ k ∧ n * T k = T j

/-- The 20 listed indices of zeros. -/
def L : Finset ℕ :=
  {4, 9, 16, 25, 49, 64, 81, 121, 144, 169, 225, 256, 289, 361, 400, 441, 529, 576, 625, 729}

theorem main : ∀ n : ℕ, 1 ≤ n → n ≤ 729 → (IsZero n ↔ n ∈ L) := by
  sorry

end OMA.S_oeis_a227054
