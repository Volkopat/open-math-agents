import Mathlib

/-!
# A027984: a(n) = Sum_{k=0..n} T(n, k)*T(n, n+k), T given by A027960.

Source: https://oeis.org/A027984
Credit: @agchua

Colin Barker (Feb 25 2015), in the formula section of A027984:
  Conjectures from Colin Barker, Feb 25 2015: (Start)
  a(n) = 4*a(n-1) - 3*a(n-2) - 2*a(n-3) + a(n-4).
  G.f.: (1-x)*(1+x)*(1+2*x) / ((1-3*x+x^2)*(1-x-x^2)). (End)
This file states both parts: the recurrence for n ≥ 4 (offset 0, so that all indices are terms),
and the g.f. as an identity of formal power series over ℚ,
(∑ a(n) X^n) * ((1 - 3X + X^2) * (1 - X - X^2)) = (1 - X) * (1 + X) * (1 + 2X).
Definition: T is the Lucas array A027960, exactly as in the PARI programs of A027960 and A027984:
T(r, k) = 0 for k > 2r; T(r, 0) = T(r, 2r) = 1; T(r, 1) = 3 for r ≥ 1; otherwise
T(r, k) = T(r-1, k-1) + T(r-1, k-2) (the recurrence in the formula section of A027960).
Then a(n) = Sum_{k=0..n} T(n, k) T(n, n+k), with the terms taken in ℤ.
-/

namespace OMA.S_oeis_a027984

/-- A027960, the Lucas array: row r has the entries T(r, 0), ..., T(r, 2r), and T(r, k) = 0 for
k > 2r. -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | r + 1, k =>
    if 2 * (r + 1) < k then 0
    else if k = 0 ∨ k = 2 * (r + 1) then 1
    else if k = 1 then 3
    else T r (k - 1) + T r (k - 2)

/-- A027984: a(n) = Sum_{k=0..n} T(n, k) * T(n, n+k). -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), (T n k : ℤ) * (T n (n + k) : ℤ)

/-- Barker's conjectures: a(n) = 4a(n-1) - 3a(n-2) - 2a(n-3) + a(n-4) for n ≥ 4, and the g.f.
(1-x)(1+x)(1+2x)/((1-3x+x^2)(1-x-x^2)). -/
theorem main : (∀ n : ℕ, 4 ≤ n → a n = 4 * a (n - 1) - 3 * a (n - 2) - 2 * a (n - 3) + a (n - 4)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) *
        ((1 - 3 * PowerSeries.X + PowerSeries.X ^ 2) * (1 - PowerSeries.X - PowerSeries.X ^ 2)) =
      (1 - PowerSeries.X) * (1 + PowerSeries.X) * (1 + 2 * PowerSeries.X) := by
  sorry

end OMA.S_oeis_a027984
