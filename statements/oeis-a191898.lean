import Mathlib

/-!
# A191898: Symmetric square array T(n, k) with no zero elements

Source: https://oeis.org/A191898

Conjecture (Mats Granvik):
No element of the symmetric square array `T(n, k)` (`n ≥ 1`, `k ≥ 1`) is equal to `0`,
where `T(n, 1) = 1`, `T(1, k) = 1`,
`T(n, k) = -∑_{i=1}^{k-1} T(n - i, k)` for `n ≥ k ≥ 2`,
and `T(n, k) = T(k, n)` for `1 ≤ n < k`.

Conventions:
- Offset: `1` (1-indexed rows `n ≥ 1` and columns `k ≥ 1`).
- Main diagonal `T(n, n)` starts `1, -1, -2, -1, -4, 2, -6, -1, ...` (A023900).
- Computed in `ℤ` by structural recursion on the column index `k` and row index `n`.
-/

namespace OMA.S_oeis_a191898

/-- Prefix list `[T(0, k), T(1, k), ..., T(n, k)]` for column `k ≥ 2`,
given `init j = T(k, j)` for `1 ≤ j < k`. -/
def tColAux (k : ℕ) (init : ℕ → ℤ) : ℕ → List ℤ
  | 0 => [0]
  | m + 1 =>
    let xs := tColAux k init m
    let val : ℤ :=
      if m + 1 < k then
        init (m + 1)
      else
        -(∑ j ∈ Finset.range (k - 1), xs.getD (m - j) 0)
    xs ++ [val]

/-- List of column functions `[col 0, col 1, ..., col k]` for A191898,
where `col j n = T(n, j)` for `n ≥ 1` and `1 ≤ j ≤ k`. -/
def tCols : ℕ → List (ℕ → ℤ)
  | 0 => [fun _ => 0]
  | 1 => [fun _ => 0, fun _ => 1]
  | k + 2 =>
    let prev := tCols (k + 1)
    let init : ℕ → ℤ := fun j => (prev.getD j (fun _ => 0)) (k + 2)
    let col : ℕ → ℤ := fun n => (tColAux (k + 2) init n).getD n 0
    prev ++ [col]

/-- The symmetric square array `T(n, k)` of OEIS A191898 for `n ≥ 1`, `k ≥ 1`. -/
def T (n k : ℕ) : ℤ :=
  if k ≤ n then
    ((tCols k).getD k (fun _ => 0)) n
  else
    ((tCols n).getD n (fun _ => 0)) k

/-- Conjecture (Mats Granvik): no entry `T(n, k)` (`n ≥ 1`, `k ≥ 1`) of A191898 is zero. -/
theorem main :
    ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → T n k ≠ 0 := by
  sorry

end OMA.S_oeis_a191898
