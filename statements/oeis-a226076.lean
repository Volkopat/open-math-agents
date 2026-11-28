import Mathlib

/-!
# OEIS A226076: the lexicographically least sum-free sequence of squares, a(n) = 4 a(n-3)

Source: https://oeis.org/A226076 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (2013), offset 1: Lexicographically least sequence of squares that are sum-free. Comment: A
sum-free sequence has no term that is the sum of a subset of its previous terms. This sequence is
lexicographically the first. Example: a(10)=576 as 576 is the next square after a(9)=289 that
cannot be formed from distinct sums of a(1),...,a(9) (1,4,9,16,36,64,144,256,289). Formula:
Conjecture: a(n) = 4*a(n-3) for n>9. G.f.: -x*(33*x^8 +112*x^7 +80*x^6 +28*x^5 +20*x^4 +12*x^3
+9*x^2 +4*x +1) / (4*x^3 -1). - Colin Barker, May 28 2013

Formalization notes:
* A subset of the previous terms is a sublist of the list of previous terms, so each term is
  used at most once; the empty subset has sum 0.
* The sequence is built greedily, as in the entry's example and program: a(n) is the least square
  that is not the sum of a subset of a(1), ..., a(n-1). This greedy sequence is the
  lexicographically least sum-free sequence of squares (any sum-free sequence that agrees with
  it before position n has an n-th term that is admissible, hence at least the greedy one, and
  the greedy choice can always be continued). Since 0 is the empty sum, a(1) = 1.
* `next L` is the infimum of the squares that are not subset sums of L (this set is never
  empty); `terms n` is the list a(1), ..., a(n); a(n) = next (terms (n - 1)) for n >= 1.
* `main` is the conjunction of both conjectured formulas: the recurrence for n > 9, and the
  g.f. identity stated as A(x) * (4x^3 - 1) = -x * (33x^8 + ... + 1) in Q[[x]], where
  A(x) = Sum_{n >= 1} a(n) x^n (equivalent to the quotient form because 4x^3 - 1 is invertible).
* Controls proved in the proof file: a(1..10) = 1, 4, 9, 16, 36, 64, 144, 256, 289, 576.
-/

namespace OMA.S_oeis_a226076

/-- x is the sum of a subset of the terms in the list L (a sublist, so each term once). -/
def IsSubsetSum (L : List ℕ) (x : ℕ) : Prop := ∃ M : List ℕ, M.Sublist L ∧ M.sum = x

/-- The next term after the terms L: the least square that is not a sum of a subset of L. -/
noncomputable def next (L : List ℕ) : ℕ := sInf {m : ℕ | IsSquare m ∧ ¬ IsSubsetSum L m}

/-- The list of the first n terms. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => []
  | n + 1 => terms n ++ [next (terms n)]

/-- a(n) for n >= 1: the term that follows the first n - 1 terms. -/
noncomputable def a (n : ℕ) : ℕ := next (terms (n - 1))

open PowerSeries in
/-- Barker's conjectures: a(n) = 4 a(n-3) for n > 9, and the g.f. -/
theorem main : (∀ n : ℕ, 9 < n → a n = 4 * a (n - 3)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (4 * X ^ 3 - 1) =
      -X * (33 * X ^ 8 + 112 * X ^ 7 + 80 * X ^ 6 + 28 * X ^ 5 + 20 * X ^ 4 + 12 * X ^ 3 +
        9 * X ^ 2 + 4 * X + 1) := by
  sorry

end OMA.S_oeis_a226076
