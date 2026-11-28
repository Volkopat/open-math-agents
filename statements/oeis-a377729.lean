import Mathlib

/-!
# A377729: smallest number that is a sum of n distinct nonzero n-gonal numbers in exactly 2 ways.

Source: https://oeis.org/A377729
Credit: @rtflynn

From the formula section of A377729:
  Conjecture: a(n) = (n^4 - 2*n^3 + 38*n^2 - 85*n + 72)/6 for n >= 5. (David A. Corneth, Nov 06 2024)
  Conjectured g.f.: x^3*(19 - 5*x - 98*x^2 + 199*x^3 - 171*x^4 + 72*x^5 - 12*x^6) / (1 - x)^5.

Conventions:
* The k-th n-gonal number is P(n, k) = (n - 2) * k * (k - 1) / 2 + k (k * (k - 1) is even, so the
  division in ℕ is exact); the nonzero n-gonal numbers are P(n, k) for k ≥ 1.
* A way to write m as a sum of n distinct nonzero n-gonal numbers is a finite set of n nonzero
  n-gonal numbers with sum m; ways are counted with `Nat.card` of the subtype of such sets
  (each such set lies in {0, ..., m}, so there are finitely many).
* a(n) is the least m with exactly 2 ways (`sInf`); Corneth's comment in the entry exhibits an m
  with 2 ways for n ≥ 5, and the examples give a(3) = 19, a(4) = 90.
* Offset 3: the g.f. is stated as an identity of formal power series over ℚ for the series with
  coefficient a(n) for n ≥ 3 and 0 for n < 3.
* The closed form is stated in ℚ for every n ≥ 5.

Numerical check: a Python brute force of the definition gives a(3..9) = 19, 90, 162, 299, 509,
816, 1248, the DATA of the entry; the g.f. expands to the same terms.
-/

namespace OMA.S_oeis_a377729

/-- The k-th n-gonal number. -/
def P (n k : ℕ) : ℕ := (n - 2) * k * (k - 1) / 2 + k

/-- The number of ways to write m as a sum of n distinct nonzero n-gonal numbers. -/
noncomputable def ways (n m : ℕ) : ℕ :=
  Nat.card {s : Finset ℕ // s.card = n ∧ (∀ x ∈ s, ∃ k, 0 < k ∧ x = P n k) ∧ ∑ x ∈ s, x = m}

/-- A377729: the smallest number with exactly 2 such representations. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m | ways n m = 2}

/-- Corneth's closed form for n ≥ 5 and the conjectured g.f. -/
theorem main : (∀ n : ℕ, 5 ≤ n →
      (a n : ℚ) = ((n : ℚ) ^ 4 - 2 * n ^ 3 + 38 * n ^ 2 - 85 * n + 72) / 6) ∧
    PowerSeries.mk (fun n => if n < 3 then (0 : ℚ) else a n) * (1 - PowerSeries.X) ^ 5 =
      PowerSeries.X ^ 3 * (19 - 5 * PowerSeries.X - 98 * PowerSeries.X ^ 2 + 199 * PowerSeries.X ^ 3 -
        171 * PowerSeries.X ^ 4 + 72 * PowerSeries.X ^ 5 - 12 * PowerSeries.X ^ 6) := by
  sorry

end OMA.S_oeis_a377729
