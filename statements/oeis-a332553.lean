import Mathlib

/-!
# A332553: a(n) = n + A082183(n) - A082184(n)

Source: https://oeis.org/A332553
Credit: @avivorly

Definitions (OEIS, all three entries have offset 2):
- A332553: `a(n) = n + A082183(n) - A082184(n)`.
- A082183: smallest `k > 0` such that `T(n) + T(k) = T(m)`, for some `m`, `T(i)` being the triangular numbers,
  `n > 1`.
- A082184: the `a(n)`-th triangular number is the sum of the `n`-th triangular number and the smallest triangular
  number possible (A082184 cross-reference: index of second term is in A082183).

Conjectures (N. J. A. Sloane, Feb 23 2020, in A332553), verbatim:
To study the lowest values taken by `a(n)`, consider the record high values of `n/a(n)`. The data suggests two
conjectures.
Conjecture 1: The record high values of `n/a(n)` are `j/2 + 1` for `j = 2,3,4,5,...` and occur at
`n = j*(j+1)/2 - 1`.
This would imply:
Conjecture 2: Let `j = 2,3,4,5,...` For `1 <= n < T_j - 1`, `a(n) > 2*n/(j+2)`.

Conventions:
- `T i = i * (i + 1) / 2` in `ℕ`; the division is exact since `i * (i + 1)` is even.
- `A082183 n = sInf {k | 0 < k ∧ ∃ m, T n + T k = T m}`. In Mathlib the `sInf` of a nonempty set of naturals is
  its least element (it is defined as `Nat.find` of the nonemptiness proof), and `sInf ∅ = 0`. For `n ≥ 2` the set
  is nonempty (`k = T(n) - 1`, `m = T(n)`, the bound in A082183), so `A082183 n` is the least such `k`, as in the
  entry. For `n = 1` there is no such `k` (`T(1) + T(k) = T(m)` means `(m - k) * (m + k + 1) = 2`, which forces
  `k = 0`); this is why the entries start at `n = 2`. Values at `n ≤ 1` are junk and are never used below.
- `A082184 n = sInf {m | T n + T (A082183 n) = T m}`: since `T` is strictly increasing this set has exactly one
  element for `n ≥ 2`, the `m` of the triple. The smallest triangular number possible in the name of A082184 is
  `T (A082183 n)`, the smallest positive one (`T 0 = 0` would give the trivial `m = n`); the data
  `A082184(2) = 3`, `A082184(4) = 10` agree with this reading.
- `a n` is taken in `ℤ`, so no truncated subtraction occurs. (In fact `a n ≥ 1` for `n ≥ 2`, a remark of Bradley Klee
  in the entry; this is part of what a proof shows, so the ratio `n / a n` never divides by zero on the domain.)
- The ratio `n / a(n)` is read in `ℚ`.
- Record: `n` (with `n ≥ 2`, a term of the sequence) is a record of `n / a(n)` when `n / a(n) > n' / a(n')` for every
  term `n'` with `2 ≤ n' < n` (strict, the usual OEIS sense). The first term `n = 2` is a record (vacuously); it is
  the case `j = 2`.
- Conjecture 1 is read as: the records are exactly the `n = j*(j+1)/2 - 1` with `j ≥ 2`, and at such `n` the
  ratio is `j/2 + 1`. (So the record values are exactly the `j/2 + 1`, `j ≥ 2`.)
- Conjecture 2: the range `1 <= n < T_j - 1` is read as `2 ≤ n < T_j - 1`, since `a(1)` does not exist (offset 2).
  For `j = 2` the range is empty. The inequality `a(n) > 2*n/(j+2)` is read in `ℚ`.
- `j * (j + 1) / 2 - 1` and `T j - 1` are in `ℕ`; both are exact, as `j * (j + 1)` is even and `T j ≥ 3` for
  `j ≥ 2`.
- `main` is the conjunction of Conjecture 1 (both parts) and Conjecture 2.
-/

namespace OMA.S_oeis_a332553

/-- The triangular number `T(i) = i(i+1)/2`. -/
def T (i : ℕ) : ℕ := i * (i + 1) / 2

/-- A082183(n): the smallest `k > 0` such that `T(n) + T(k) = T(m)` for some `m` (meaningful for `n ≥ 2`). -/
noncomputable def A082183 (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ ∃ m : ℕ, T n + T k = T m}

/-- A082184(n): the `m` with `T(m) = T(n) + T(A082183(n))` (meaningful for `n ≥ 2`). -/
noncomputable def A082184 (n : ℕ) : ℕ :=
  sInf {m : ℕ | T n + T (A082183 n) = T m}

/-- A332553(n) = n + A082183(n) - A082184(n), computed in `ℤ`. -/
noncomputable def a (n : ℕ) : ℤ :=
  (n : ℤ) + (A082183 n : ℤ) - (A082184 n : ℤ)

/-- `n` is a record (high value) of `n / a(n)`: `n ≥ 2` and `n' / a(n') < n / a(n)` for every `2 ≤ n' < n`. -/
def IsRecord (n : ℕ) : Prop :=
  2 ≤ n ∧ ∀ n' : ℕ, 2 ≤ n' → n' < n → (n' : ℚ) / (a n' : ℚ) < (n : ℚ) / (a n : ℚ)

/-- Sloane's Conjectures 1 and 2 in A332553. -/
theorem main :
    ((∀ n : ℕ, IsRecord n ↔ ∃ j : ℕ, 2 ≤ j ∧ n = j * (j + 1) / 2 - 1) ∧
      (∀ j : ℕ, 2 ≤ j →
        ((j * (j + 1) / 2 - 1 : ℕ) : ℚ) / (a (j * (j + 1) / 2 - 1) : ℚ) = (j : ℚ) / 2 + 1)) ∧
    (∀ j : ℕ, 2 ≤ j → ∀ n : ℕ, 2 ≤ n → n < T j - 1 →
      (a n : ℚ) > 2 * (n : ℚ) / ((j : ℚ) + 2)) := by
  sorry

end OMA.S_oeis_a332553
