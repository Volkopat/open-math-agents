import Mathlib

/-!
# A051159: Beck's conjecture about three lower triangular matrices

The rows and columns are indexed from zero. The row polynomial for `U`
uses the signed integers `-1, 2, -3, …` from the OEIS entry. Matrix
multiplication uses the finite row sum for lower triangular matrices.
The proposed inverse is expressed by both product identities, and the
absolute-value comparison is entrywise.

Sources
- https://oeis.org/A051159
- https://oeis.org/A057077
-/

namespace OMA.S_oeis_a051159

open Finset Polynomial

def T (n k : ℕ) : ℤ := ((n % 2).choose (k % 2) * (n / 2).choose (k / 2) : ℕ)

noncomputable def U (n k : ℕ) : ℤ :=
  (∏ j ∈ range n, (1 + C (((-1 : ℤ) ^ (j + 1)) * ((j : ℤ) + 1)) * X)).coeff k

def V (n k : ℕ) : ℤ := if n = k then (-1 : ℤ) ^ (n / 2) else 0

def identityEntry (n k : ℕ) : ℤ := if n = k then 1 else 0

def triangularProduct (A B : ℕ → ℕ → ℤ) (n k : ℕ) : ℤ :=
  ∑ j ∈ range (n + 1), A n j * B j k

theorem main :
    (∀ n k, triangularProduct U U n k = identityEntry n k) ∧
    (∀ n k, T n k = triangularProduct U V n k) ∧
    (∀ n k, triangularProduct T (triangularProduct V U) n k = identityEntry n k ∧
      triangularProduct (triangularProduct V U) T n k = identityEntry n k) ∧
    (∀ n k, |T n k| = |U n k|) := by
  sorry

end OMA.S_oeis_a051159
