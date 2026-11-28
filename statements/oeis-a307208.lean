import Mathlib

/-!
# A307208: a(n) is the forgotten index of the Fibonacci cube Gamma(n).

Source: https://oeis.org/A307208
Credit: @rtflynn

Colin Barker (Mar 29 2019), in the formula section of A307208:
  Conjectures: G.f.: 2*x*(1 + x + 8*x^2 - 7*x^3 + 4*x^4 - 3*x^5 + 3*x^6) / (1 - x - x^2)^4.
  a(n) = 4*a(n-1) - 2*a(n-2) - 8*a(n-3) + 5*a(n-4) + 8*a(n-5) - 2*a(n-6) - 4*a(n-7) - a(n-8) for n>8.

Definitions from the comments of the entry: the Fibonacci cube Gamma(n) is the graph whose vertices are the
binary strings of length n without two consecutive 1's, and in which two vertices are adjacent when their Hamming distance is exactly 1. The
forgotten topological index of a graph is the sum of the cubes of its vertex degrees.

Conventions:
* A binary string of length n is a function w : Fin n → Bool (`true` = 1); two consecutive 1's
  are positions i, i + 1 both equal to 1. The Hamming distance is Mathlib's `hammingDist`.
* The degree of a vertex v is the number of vertices at Hamming distance exactly 1 from v.
* Offset 1. The definition also gives a(0) = 0 (one vertex, the empty string, of degree 0), so the
  power series ∑ a(n) X^n over all n ≥ 0 is the g.f. of the entry; the g.f. is stated as an
  identity of formal power series over ℚ, (∑ a(n) X^n) * (1 - X - X^2)^4 = numerator.
* The recurrence is stated in ℤ for every n ≥ 9 (n > 8).

Numerical check: a Python copy of the definition gives 2, 10, 52, 158, 466, 1192, 2914, 6722, 14972, 32286, 67914 for n = 1..11, the DATA of the entry.
-/

namespace OMA.S_oeis_a307208

/-- The vertices of the Fibonacci cube Gamma(n). -/
def V (n : ℕ) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun w =>
    (∀ i j : Fin n, j.1 = i.1 + 1 → ¬ (w i = true ∧ w j = true)))

/-- The degree of a vertex v: the number of vertices at Hamming distance 1 from v. -/
def deg (n : ℕ) (v : Fin n → Bool) : ℕ :=
  ((V n).filter (fun u => hammingDist u v = 1)).card

/-- A307208: the forgotten index (sum of cubed degrees) of the Fibonacci cube Gamma(n). -/
def a (n : ℕ) : ℕ := ∑ v ∈ V n, deg n v ^ 3

/-- Barker's conjectures: the rational g.f. and the recurrence for n > 8. -/
theorem main : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - PowerSeries.X - PowerSeries.X ^ 2) ^ 4 =
      2 * PowerSeries.X * (1 + PowerSeries.X + 8 * PowerSeries.X ^ 2 - 7 * PowerSeries.X ^ 3 +
        4 * PowerSeries.X ^ 4 - 3 * PowerSeries.X ^ 5 + 3 * PowerSeries.X ^ 6) ∧
    ∀ n : ℕ, 9 ≤ n → (a n : ℤ) = 4 * a (n - 1) - 2 * a (n - 2) - 8 * a (n - 3) + 5 * a (n - 4) +
      8 * a (n - 5) - 2 * a (n - 6) - 4 * a (n - 7) - a (n - 8) := by
  sorry

end OMA.S_oeis_a307208
