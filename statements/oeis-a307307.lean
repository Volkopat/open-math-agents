import Mathlib

/-!
# A307307: a(n) is the forgotten index of the Lucas cube Lambda(n).

Source: https://oeis.org/A307307
Credit: @rtflynn

Colin Barker (Apr 02 2019), in the formula section of A307307:
  Conjectures: G.f.: 2*x^2*(5 - 5*x + 6*x^2 - 4*x^3 + 27*x^4 - 25*x^5 - 6*x^6 + 9*x^8 + 3*x^9) / (1 - x - x^2)^4.
  a(n) = 4*a(n-1) - 2*a(n-2) - 8*a(n-3) + 5*a(n-4) + 8*a(n-5) - 2*a(n-6) - 4*a(n-7) - a(n-8) for n>11.

Definitions from the comments of the entry: the Lucas cube Lambda(n) is the graph whose vertices are the
binary strings of length n without either two consecutive 1's or a 1 in the first and in the
  last position, and in which two vertices are adjacent when their Hamming distance is exactly 1. The
forgotten topological index of a graph is the sum of the cubes of its vertex degrees.

Conventions:
* A binary string of length n is a function w : Fin n → Bool (`true` = 1); two consecutive 1's
  are positions i, i + 1 both equal to 1. The Hamming distance is Mathlib's `hammingDist`.
* *A 1 in the first and in the last position*: w(0) = 1 and w(n-1) = 1. For n = 1 these are the
  same position, so the string 1 is excluded and Lambda(1) has the single vertex 0; this gives
  a(1) = 0, the first term of the entry.
* The degree of a vertex v is the number of vertices at Hamming distance exactly 1 from v.
* Offset 1. The definition also gives a(0) = 0 (one vertex, the empty string, of degree 0), so the
  power series ∑ a(n) X^n over all n ≥ 0 is the g.f. of the entry; the g.f. is stated as an
  identity of formal power series over ℚ, (∑ a(n) X^n) * (1 - X - X^2)^4 = numerator.
* The recurrence is stated in ℤ for every n ≥ 12 (n > 11).

Numerical check: a Python copy of the definition gives 0, 10, 30, 112, 300, 840, 2044, 4864, 10944, 23960, 50908 for n = 1..11, the DATA of the entry.
-/

namespace OMA.S_oeis_a307307

/-- The vertices of the Lucas cube Lambda(n). -/
def V (n : ℕ) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun w =>
    (∀ i j : Fin n, j.1 = i.1 + 1 → ¬ (w i = true ∧ w j = true)) ∧
      ¬ (∃ (i j : Fin n), i.1 = 0 ∧ j.1 = n - 1 ∧ w i = true ∧ w j = true))

/-- The degree of a vertex v: the number of vertices at Hamming distance 1 from v. -/
def deg (n : ℕ) (v : Fin n → Bool) : ℕ :=
  ((V n).filter (fun u => hammingDist u v = 1)).card

/-- A307307: the forgotten index (sum of cubed degrees) of the Lucas cube Lambda(n). -/
def a (n : ℕ) : ℕ := ∑ v ∈ V n, deg n v ^ 3

/-- Barker's conjectures: the rational g.f. and the recurrence for n > 11. -/
theorem main : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - PowerSeries.X - PowerSeries.X ^ 2) ^ 4 =
      2 * PowerSeries.X ^ 2 * (5 - 5 * PowerSeries.X + 6 * PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3 +
        27 * PowerSeries.X ^ 4 - 25 * PowerSeries.X ^ 5 - 6 * PowerSeries.X ^ 6 + 9 * PowerSeries.X ^ 8 +
        3 * PowerSeries.X ^ 9) ∧
    ∀ n : ℕ, 12 ≤ n → (a n : ℤ) = 4 * a (n - 1) - 2 * a (n - 2) - 8 * a (n - 3) + 5 * a (n - 4) +
      8 * a (n - 5) - 2 * a (n - 6) - 4 * a (n - 7) - a (n - 8) := by
  sorry

end OMA.S_oeis_a307307
