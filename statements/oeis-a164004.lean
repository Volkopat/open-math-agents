import Mathlib

/-!
# A164004: Zero together with row 4 of the array in A163280

Source: https://oeis.org/A164004
Credit: @ivillar

Omar E. Pol's sequence (offset 0). A163280 is the square array whose column k lists, in increasing
order, the numbers j whose largest divisor <= sqrt(j) (A033676(j)) is k. Row 4 of the array is
formed by the 4th terms of the columns k = 1, 2, 3, ... (5, 10, 18, 28, ...), and a(0) = 0.

Conjectures from Colin Barker, Apr 07 2015:
  a(n) = n*(3+n) = A028552(n) for n > 1.
  a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n > 4.
  G.f.: x*(x^3 - 3*x^2 + 5*x - 5) / (x-1)^3.
(The identification with A028552, a(n) = n*(n+3), is the closed form itself.) The recurrence is
stated in ℤ and the g.f. as a power series over ℚ.
-/

namespace OMA.S_oeis_a164004

/-- A033676: the largest divisor e of j with e <= sqrt(j), i.e. e*e <= j (equal to 0 for j = 0). -/
def d (j : ℕ) : ℕ := (j.divisors.filter (fun e => e * e ≤ j)).sup id

/-- A164004 (offset 0): a(0) = 0, and for n ≥ 1, a(n) is the entry in row 4 of column n of the array
A163280, i.e. the 4th smallest j with A033676(j) = n (`Nat.nth` is 0-indexed). -/
noncomputable def a (n : ℕ) : ℕ := if n = 0 then 0 else Nat.nth (fun j => d j = n) 3

/-- The conjectured g.f. x*(x^3 - 3*x^2 + 5*x - 5) / (x-1)^3 over ℚ. -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (PowerSeries.X ^ 3 - 3 * PowerSeries.X ^ 2 + 5 * PowerSeries.X - 5)) *
    ((PowerSeries.X - 1) ^ 3)⁻¹

/-- Barker's conjectures: a(n) = n*(3+n) for n > 1, the recurrence for n > 4, and the g.f. -/
theorem main :
    (∀ n : ℕ, 1 < n → a n = n * (3 + n)) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) = G := by
  sorry

end OMA.S_oeis_a164004
