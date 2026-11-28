import Mathlib

/-!
# A152458: Numbers k that A064413(k) = k.

Source: https://oeis.org/A152458
Credit: @luciusacarr

The entry records one conjecture: this sequence is finite. Its known terms are 1, 2, 8, 40, 64
(a(6) > 10^5, if it exists).

Reading of the source:
* A064413 is the EKG sequence: `a(1) = 1`, `a(2) = 2`, and for `n ≥ 3`, `a(n)` is the smallest
  positive integer not already in the sequence that has a common factor (`gcd > 1`) with
  `a(n-1)`.
* `terms n` is the list `[a(n), a(n-1), ..., a(1)]` of the first `n` terms (most recent first);
  the next term is the infimum of the admissible values (such a value always exists, e.g. a large
  multiple of `a(n-1)`). With this definition the fixed points `a(k) = k` with `k ≤ 2000` are
  exactly 1, 2, 8, 40, 64.
* The sequence is the set of `k ≥ 1` with `a(k) = k`.
-/

namespace OMA.S_oeis_a152458

/-- The first `n` terms of the EKG sequence, most recent first. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [2, 1]
  | n + 3 =>
    sInf {m : ℕ | 0 < m ∧ m ∉ terms (n + 2) ∧ 1 < Nat.gcd m ((terms (n + 2)).headD 0)} ::
      terms (n + 2)

/-- A064413(k), the `k`-th term of the EKG sequence (for `k ≥ 1`). -/
noncomputable def ekg (k : ℕ) : ℕ := (terms k).headD 0

theorem main : {k : ℕ | 1 ≤ k ∧ ekg k = k}.Finite := by
  sorry

end OMA.S_oeis_a152458
