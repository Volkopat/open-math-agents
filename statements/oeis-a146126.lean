import Mathlib

/-!
# A146126: Number of n X n arrays of squares of integers with every (n-2) X (n-2) subblock summing to 5 and every element equal to at least one neighbor.

A146126(n) counts the `n × n` arrays `x` of natural numbers such that every entry is the square of
an integer, every `(n-2) X (n-2)` subblock of consecutive rows and columns sums to 5, and every entry equals at least one of its neighbors. Neighbors are the
horizontally and vertically adjacent cells: a brute-force count of this reading gives
0, 235, 9716 for n = 4, 5, 6, matching the listed terms, while counting diagonal neighbors too does not.
(The sum condition bounds every entry, so the set counted is finite.)

The offset is 4; values of `a` below it are not terms of the sequence and are replaced by 0
in the generating function.

The problem: the conjectures of Colin Barker (Mar 23 2018):
  G.f.: x^5*(235 + 8541*x - 3029*x^2 + 3869*x^3 + 1132*x^4 - 1212*x^5 + 430*x^6 + 18*x^7) / (1 - x)^5,
  a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n > 12.
The g.f. is stated after multiplying both sides by `(1 - x)^5`.

Source: https://oeis.org/A146126
Credit: @VashaTS
-/

namespace OMA.S_oeis_a146126

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

/-- A146126(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin n → Fin n → ℕ //
    (∀ i j, IsSquare (x i j)) ∧ BlockSums (n - 2) 5 x ∧
      ∀ p : Fin n × Fin n, ∃ q, Adj p q ∧ x q.1 q.2 = x p.1 p.2}

theorem main :
    PowerSeries.mk (fun n => if n < 4 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      235 * X ^ 5 + 8541 * X ^ 6 - 3029 * X ^ 7 + 3869 * X ^ 8 + 1132 * X ^ 9 - 1212 * X ^ 10
        + 430 * X ^ 11 + 18 * X ^ 12 ∧
    ∀ n : ℕ, 12 < n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a146126
