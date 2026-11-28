import Mathlib

/-!
# A119652: Number of different values of <= n standard American coins (pennies, nickels, dimes and quarters).

Source: https://oeis.org/A119652
Credit: @Salofe

The entry's FORMULA section reads, verbatim:
  "Conjectures from Colin Barker, Oct 25 2019: (Start)
   G.f.: x*(4 + 5*x + 5*x^2 + 5*x^3 + 4*x^4 + 2*x^5) / (1 - x)^2.
   a(n) = 2*a(n-1) - a(n-2) for n>6.
   a(n) = 25*n-56 for n>4.
   (End)"

Formalization notes:
* Offset 1, as in the entry (data: 4, 13, 27, 46, 69, 94, 119, 144, ...).
* A collection of coins is given by its numbers `p, m, d, q` of pennies (1 cent), nickels
  (5 cents), dimes (10 cents) and quarters (25 cents); its value is `p + 5m + 10d + 25q`.
  "<= n coins" means `1 <= p + m + d + q <= n`: the empty collection is not counted, as the
  entry's data and example require (a(1) = 4, the totals 1, 5, 10, 25; and a(2) = 13).
* `a n` is the number of different values: the `Set.ncard` of the set of values of such
  collections, a finite set since every value is at most `25 n`.
* The generating function is stated as an identity of formal power series over `ℤ` with the
  denominator cleared: `(Σ_{n ≥ 1} a(n) x^n) * (1 - x)^2 = x*(4 + 5x + 5x^2 + 5x^3 + 4x^4 + 2x^5)`.
  The coefficient of `x^0` is `0` because the sequence starts at n = 1; the value of `a 0`
  plays no role.
* The recurrence and the closed form are stated in `ℤ`, for the index ranges of the entry
  (n > 6 and n > 4 respectively).
-/

namespace OMA.S_oeis_a119652

/-- The values of collections of at least one and at most `n` coins, each a penny (1 cent),
a nickel (5 cents), a dime (10 cents) or a quarter (25 cents): `p` pennies, `m` nickels,
`d` dimes and `q` quarters. -/
def coinValues (n : ℕ) : Set ℕ :=
  {v | ∃ p m d q : ℕ, 1 ≤ p + m + d + q ∧ p + m + d + q ≤ n ∧
    v = p + 5 * m + 10 * d + 25 * q}

/-- A119652: the number of different values of `≤ n` standard American coins. -/
noncomputable def a (n : ℕ) : ℕ := (coinValues n).ncard

/-- Barker's three conjectures: the generating function, the recurrence for `n > 6`, and the
closed form for `n > 4`. -/
theorem main :
    (let x : PowerSeries ℤ := PowerSeries.X
     PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℤ)) * (1 - x) ^ 2 =
       x * (4 + 5 * x + 5 * x ^ 2 + 5 * x ^ 3 + 4 * x ^ 4 + 2 * x ^ 5)) ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2)) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 25 * n - 56) := by
  sorry

end OMA.S_oeis_a119652
