import Mathlib

/-!
# A146123: Number of n X n arrays of squares of integers with every (n-3) X (n-3) subblock summing to 4 and every element equal to at least one neighbor.

A146123(n) counts the `n × n` arrays `x` of natural numbers such that every entry is the square of
an integer, every `(n-3) X (n-3)` subblock of consecutive rows and columns sums to 4, and every entry equals at least one of its neighbors. Neighbors are the
horizontally and vertically adjacent cells: a brute-force count of this reading gives
1, 540, 4120 for n = 5, 6, 7, matching the listed terms, while counting diagonal neighbors too does not.
(The sum condition bounds every entry, so the set counted is finite.)

The offset is 5; values of `a` below it are not terms of the sequence and are replaced by 0
in the generating function.

The problem: the conjectures of Colin Barker (Mar 23 2018):
  G.f.: x^5*(1 + 535*x + 1430*x^2 - 3022*x^3 + 5865*x^4 - 4405*x^5 + 1564*x^6 - 204*x^7) / (1 - x)^5,
  a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n > 12.
The g.f. is stated after multiplying both sides by `(1 - x)^5`.

Source: https://oeis.org/A146123
Credit: @VashaTS
-/

namespace OMA.S_oeis_a146123

open PowerSeries

/-- Cells `p` and `q` of an `n × n` array are horizontally or vertically adjacent. -/
def Adj {n : ℕ} (p q : Fin n × Fin n) : Prop :=
  (p.1 = q.1 ∧ (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)) ∨
    (p.2 = q.2 ∧ (p.1.val + 1 = q.1.val ∨ q.1.val + 1 = p.1.val))

/-- Every `k × k` subblock of consecutive rows and columns of `x` sums to `s`. -/
def BlockSums {n : ℕ} (k s : ℕ) (x : Fin n → Fin n → ℕ) : Prop :=
  ∀ r c : ℕ, r + k ≤ n → c + k ≤ n →
    ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n =>
      r ≤ p.1.val ∧ p.1.val < r + k ∧ c ≤ p.2.val ∧ p.2.val < c + k), x p.1 p.2 = s

/-- A146123(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin n → Fin n → ℕ //
    (∀ i j, IsSquare (x i j)) ∧ BlockSums (n - 3) 4 x ∧
      ∀ p : Fin n × Fin n, ∃ q, Adj p q ∧ x q.1 q.2 = x p.1 p.2}

theorem main :
    PowerSeries.mk (fun n => if n < 5 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X ^ 5 + 535 * X ^ 6 + 1430 * X ^ 7 - 3022 * X ^ 8 + 5865 * X ^ 9 - 4405 * X ^ 10
        + 1564 * X ^ 11 - 204 * X ^ 12 ∧
    ∀ n : ℕ, 12 < n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a146123
