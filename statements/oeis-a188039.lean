import Mathlib

/-!
# OEIS A188039: the zeros of A188038 sit at 3n + 2 + 2 floor(n sqrt 2)

Source: https://oeis.org/A188039 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Mar 19 2011), offset 1: Positions of 0 in A188038; complement of A188040.
There is (conjecturally) a connection a(1+n) = f(n) where f(n) = 3*n +2 +2*floor(n*sqrt 2) is
defined in A120861. Tested numerically up to n=40000. - R. J. Mathar, Jul 22 2020
Data: 2, 7, 12, 19, 24, 31, 36, 41, 48, 53, 60, 65, ...
A188038 (Clark Kimberling), offset 1: a(n) = [n*r]-[k*r]-[n*r-k*r], where r=sqrt(2), k=2,
[ ]=floor. Data: 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, ...
A120861 (Clark Kimberling): Define f(n) = 3*n + 2*floor(n*sqrt(2)) + 2.

Formalization notes:
* `s n` is A188038(n), an integer (at n = 1 the last floor is of a negative number).
* `a j` is A188039(j) for j >= 1: `Nat.nth p (j - 1)` is the j-th natural number satisfying `p`,
  in increasing order, where `p n` says that n >= 1 and A188038(n) = 0.
* `f n` is f(n) of A120861, which defines it for positive n; `main` states the conjecture for
  every n >= 1.
-/

namespace OMA.S_oeis_a188039

/-- A188038(n) = floor(n r) - floor(2 r) - floor(n r - 2 r) with r = sqrt 2. -/
noncomputable def s (n : ℕ) : ℤ :=
  ⌊(n : ℝ) * Real.sqrt 2⌋ - ⌊2 * Real.sqrt 2⌋ - ⌊(n : ℝ) * Real.sqrt 2 - 2 * Real.sqrt 2⌋

/-- A188039(j): the position of the j-th 0 in A188038 (offset 1). -/
noncomputable def a (j : ℕ) : ℕ := Nat.nth (fun n => 1 ≤ n ∧ s n = 0) (j - 1)

/-- f(n) = 3n + 2 + 2 floor(n sqrt 2), from A120861. -/
noncomputable def f (n : ℕ) : ℕ := 3 * n + 2 + 2 * ⌊(n : ℝ) * Real.sqrt 2⌋₊

/-- The conjecture (R. J. Mathar): a(1 + n) = f(n). -/
theorem main : ∀ n : ℕ, 1 ≤ n → a (1 + n) = f n := by
  sorry

end OMA.S_oeis_a188039
