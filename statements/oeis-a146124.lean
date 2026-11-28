import Mathlib

/-!
# A146124: Number of n X n arrays of squares of integers summing to 5 with every element equal to at least one neighbor.

A146124(n) counts the `n × n` arrays `x` of natural numbers such that every entry is the square of
an integer, the entries sum to 5, and every entry equals at least one of its neighbors. Neighbors are the
horizontally and vertically adjacent cells: a brute-force count of this reading gives
0, 32, 516, 2307 for n = 2..5, matching the listed terms, while counting diagonal neighbors too does not.
(The sum condition bounds every entry, so the set counted is finite.)

The offset is 2; values of `a` below it are not terms of the sequence and are replaced by 0
in the generating function.

The problem: the conjectures of Colin Barker (Mar 23 2018):
  G.f.: x^3*(32 + 356*x + 47*x^2 - 223*x^3 + 89*x^4 - 13*x^5) / (1 - x)^5,
  a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n > 8.
The g.f. is stated after multiplying both sides by `(1 - x)^5`.

Source: https://oeis.org/A146124
Credit: @VashaTS
-/

namespace OMA.S_oeis_a146124

open PowerSeries

/-- Cells `p` and `q` of an `n × n` array are horizontally or vertically adjacent. -/
def Adj {n : ℕ} (p q : Fin n × Fin n) : Prop :=
  (p.1 = q.1 ∧ (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)) ∨
    (p.2 = q.2 ∧ (p.1.val + 1 = q.1.val ∨ q.1.val + 1 = p.1.val))


/-- A146124(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin n → Fin n → ℕ //
    (∀ i j, IsSquare (x i j)) ∧ ∑ p : Fin n × Fin n, x p.1 p.2 = 5 ∧
      ∀ p : Fin n × Fin n, ∃ q, Adj p q ∧ x q.1 q.2 = x p.1 p.2}

theorem main :
    PowerSeries.mk (fun n => if n < 2 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      32 * X ^ 3 + 356 * X ^ 4 + 47 * X ^ 5 - 223 * X ^ 6 + 89 * X ^ 7 - 13 * X ^ 8 ∧
    ∀ n : ℕ, 8 < n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a146124
