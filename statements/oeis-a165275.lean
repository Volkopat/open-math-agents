import Mathlib

/-!
# A165275: Table read by antidiagonals: T(n, k) is the k-th number with n-1 odd-power summands in its base 2 representation.

Source: https://oeis.org/A165275
Credit: @ceejcake

Formalizes John W. Layman's conjecture (Sep 15 2009) for OEIS A165275 (offset 1):
For all `n ≥ 3`, `a(t(n)) = 4 * a(t(n - 1)) + 2`, where `t(n) = n * (n + 1) / 2` is the `n`-th
triangular number (A000217). (Confirmed true in the OEIS comments by Sela Fried, Nov 11 2025.)

Conventions:
* `oddBitCount m` counts the odd bit positions `j` (`j % 2 = 1`) where `m.testBit j = true`
  (i.e. the number of odd powers of `2` in the base-2 representation of `m`).
* `T n k` (for `n ≥ 1, k ≥ 1`) is the `k`-th positive integer `m` with `oddBitCount m = n - 1`,
  using `Nat.nth` (0-indexed at `k - 1`).
* `a idx` (for `idx ≥ 1`, offset 1) reads `T` by antidiagonals: `(1, 1), (1, 2), (2, 1), (1, 3),
  (2, 2), (3, 1), ...`, where antidiagonal `d` runs `r = 1..d` with `(r, d + 1 - r)`.
* All 58 OEIS A165275 DATA terms match: `1, 4, 2, 5, 3, 10, 16, 6, 11, 42, 17, 7, 14, 43, 170, ...`.
-/

namespace OMA.S_oeis_a165275

/-- The `n`-th triangular number `t(n) = n * (n + 1) / 2` (OEIS A000217). -/
def tri (n : ℕ) : ℕ :=
  n * (n + 1) / 2

/-- Number of odd powers of `2` in the binary representation of `m`. -/
def oddBitCount (m : ℕ) : ℕ :=
  ((Finset.range (Nat.log2 m + 1)).filter (fun j => j % 2 = 1 ∧ m.testBit j)).card

/-- `T n k` (1-indexed, `n ≥ 1, k ≥ 1`) is the `k`-th positive integer with `n - 1` odd-power
summands in its base-2 representation. -/
noncomputable def T (n k : ℕ) : ℕ :=
  Nat.nth (fun m : ℕ => 0 < m ∧ oddBitCount m = n - 1) (k - 1)

/-- The antidiagonal index `d` containing `idx` (least `d` with `idx ≤ tri d`). -/
def diagOf (idx : ℕ) : ℕ :=
  ((Finset.range (idx + 1)).filter (fun d => idx ≤ tri d)).min'
    (by
      refine ⟨idx, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_self idx), ?_⟩⟩
      unfold tri
      have h : 2 * idx ≤ idx * (idx + 1) := by
        rcases idx with _ | idx
        · simp
        · nlinarith
      omega)

/-- OEIS A165275 (offset 1): the table `T(n, k)` read by antidiagonals. -/
noncomputable def a (idx : ℕ) : ℕ :=
  if 1 ≤ idx then
    let d := diagOf idx
    let r := idx - tri (d - 1)
    T r (d + 1 - r)
  else 0

/-- Conjecture (John W. Layman, OEIS A165275): for every `n ≥ 3`,
`a(t(n)) = 4 * a(t(n - 1)) + 2`. -/
theorem main : ∀ n : ℕ, 3 ≤ n → a (tri n) = 4 * a (tri (n - 1)) + 2 := by
  sorry

end OMA.S_oeis_a165275
