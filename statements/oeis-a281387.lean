import Mathlib

/-!
# A281387: Pairs (x, y) of relatively prime positive integers such that (x^2 - 5)/y and (y^2 - 5)/x are both positive integers.

Source: https://oeis.org/A281387
Credit: @agchua

Conjectures from Chai Wah Wu, Jan 28 2024, in the formula section of A281387 (verbatim):
  a(n) = 3*a(n-2) - a(n-4) for n > 4.
  G.f.: x*(-4*x^3 - x^2 + 11*x + 4)/(x^4 - 3*x^2 + 1).
This file states both parts.

Offset 1. The entry lists the solution pairs flattened, a(2m-1) = x and a(2m) = y for the m-th
pair: (4, 11), (11, 29), (29, 76), ... The condition is symmetric in x and y and x = y gives no
solution, so each pair is listed once, as (x, y) with x < y, and the pairs are ordered by x.
`Sol x y` is the condition of the name: x and y are positive and coprime, 5 < x^2 and y divides
x^2 - 5 (so (x^2 - 5)/y is a positive integer), and 5 < y^2 and x divides y^2 - 5. `xs m` is
the m-th smallest (counting from m = 0) first coordinate x of a solution pair (x, y) with x < y,
and `ys m` is the least y with xs m < y such that (xs m, y) is a solution, that is, the second
coordinate of the pair with first coordinate xs m. Then a(2m+1) = xs m and a(2m+2) = ys m.
The recurrence is stated for n > 4 (so that n - 4 is an index of the entry), in ℤ. The g.f. is
stated as an identity of formal power series over ℚ, with coefficient 0 at X^0 (offset 1):
(Sum_{n >= 1} a(n) X^n) * (X^4 - 3 X^2 + 1) = X * (-4 X^3 - X^2 + 11 X + 4).
-/

namespace OMA.S_oeis_a281387

/-- The condition of the name for the pair (x, y): x and y are relatively prime positive
integers, and (x^2 - 5)/y and (y^2 - 5)/x are both positive integers. -/
def Sol (x y : ℕ) : Prop :=
  0 < x ∧ 0 < y ∧ Nat.Coprime x y ∧ 5 < x ^ 2 ∧ y ∣ x ^ 2 - 5 ∧ 5 < y ^ 2 ∧ x ∣ y ^ 2 - 5

/-- The first coordinates x of the solution pairs (x, y) with x < y, in increasing order. -/
noncomputable def xs (m : ℕ) : ℕ := Nat.nth (fun x => ∃ y, x < y ∧ Sol x y) m

/-- The second coordinate of the solution pair whose first coordinate is xs m. -/
noncomputable def ys (m : ℕ) : ℕ := sInf {y | xs m < y ∧ Sol (xs m) y}

/-- A281387 (offset 1): a(2m+1) = xs m and a(2m+2) = ys m. -/
noncomputable def a (n : ℕ) : ℕ := if n % 2 = 1 then xs (n / 2) else ys (n / 2 - 1)

/-- Wu's conjectures: a(n) = 3a(n-2) - a(n-4) for n > 4, and the g.f.
x(-4x^3 - x^2 + 11x + 4)/(x^4 - 3x^2 + 1). -/
theorem main : (∀ n : ℕ, 4 < n → (a n : ℤ) = 3 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        (PowerSeries.X ^ 4 - 3 * PowerSeries.X ^ 2 + 1) =
      PowerSeries.X * (-4 * PowerSeries.X ^ 3 - PowerSeries.X ^ 2 + 11 * PowerSeries.X + 4) := by
  sorry

end OMA.S_oeis_a281387
