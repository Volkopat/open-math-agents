import Mathlib

/-!
# A064873: first part of the lexicographically minimal decomposition of `n` in 4 squares

Source: https://oeis.org/A064873
Credit: @avivorly

A064873 (offset 0) is the first of four sequences representing the lexicographical minimal decomposition of `n` in
4 squares: `n = a(n)^2 + A064874(n)^2 + A064875(n)^2 + A064876(n)^2`. A064874 (offset 0) is the second of the four
sequences. The entry adds: `a(n)` is the minimum `k` such that `A072401(n - k^2) = 0`, that is, such that `n - k^2` is
a sum of three squares.

Conjecture (Zhuorui He, Oct 23 2025, in the entry): `a(n) = A064874(n - A064874(n)^2)`.

Conventions:
- A decomposition of `n` in 4 squares is a 4-tuple `(a, b, c, d)` of natural numbers with
  `a^2 + b^2 + c^2 + d^2 = n` (a square of an integer is the square of its absolute value, and the data is
  nonnegative). Every `n` has one by Lagrange's four-square theorem (`Nat.sum_four_squares`), and only finitely many,
  so the lexicographically minimal one exists.
- The lexicographic order on `ℕ × ℕ × ℕ × ℕ` compares first entries and breaks ties by the next entry. Hence the
  minimal decomposition `(a, b, c, d)` has `a` = the least first part of any decomposition, and `b` = the least second
  part of a decomposition with first part `a`. These nested minima are the definitions below (`Nat.find`):
  `a064873 n` is the least `k` with `k^2 + y^2 + z^2 + w^2 = n` for some `y, z, w` (equivalently: `k^2 ≤ n` and
  `n - k^2` is a sum of three squares, as in the entry's comment), and `a064874 n` is the least `j` with
  `a064873 n ^ 2 + j^2 + z^2 + w^2 = n` for some `z, w`.
- Offsets: both sequences start at `n = 0` (`%O 0`); `a(0) = A064874(0) = 0` from `0 = 0^2 + 0^2 + 0^2 + 0^2`.
  The conjecture is stated for every `n ≥ 0`.
- `n - A064874(n)^2` is read in `ℕ`; the subtraction is exact, since `A064874(n)^2 ≤ n`.
-/

namespace OMA.S_oeis_a064873

open Classical in
/-- A064873(n): the first part of the lexicographically minimal decomposition of `n` in 4 squares, i.e. the least `k`
such that `k^2 + y^2 + z^2 + w^2 = n` for some naturals `y, z, w` (one exists by `Nat.sum_four_squares`). -/
noncomputable def a064873 (n : ℕ) : ℕ :=
  Nat.find (p := fun k => ∃ y z w : ℕ, k ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n)
    (by obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n; exact ⟨a, b, c, d, h⟩)

open Classical in
/-- A064874(n): the second part of the lexicographically minimal decomposition of `n` in 4 squares, i.e. the least `j`
such that `a064873 n ^ 2 + j^2 + z^2 + w^2 = n` for some naturals `z, w` (one exists by the definition of
`a064873 n`). -/
noncomputable def a064874 (n : ℕ) : ℕ :=
  Nat.find (p := fun j => ∃ z w : ℕ, a064873 n ^ 2 + j ^ 2 + z ^ 2 + w ^ 2 = n)
    (by
      obtain ⟨y, z, w, h⟩ : ∃ y z w : ℕ, a064873 n ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n :=
        Nat.find_spec (p := fun k => ∃ y z w : ℕ, k ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n)
          (by obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n; exact ⟨a, b, c, d, h⟩)
      exact ⟨y, z, w, h⟩)

theorem main : ∀ n : ℕ, a064873 n = a064874 (n - a064874 n ^ 2) := by
  sorry

end OMA.S_oeis_a064873
