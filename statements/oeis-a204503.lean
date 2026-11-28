import Mathlib

/-!
# A204503: squares n^2 with floor(n^2/9) a square: Barker's closed form and g.f.

Source: https://oeis.org/A204503
Credit: @ivillar

A204503 (offset 1) lists, in increasing order, the squares n^2 such that floor(n^2/9) is again a
square: 0, 1, 4, 9, 16, 36, 81, 144, 225, ...
Conjectures (Colin Barker, Sep 15 2014): a(n) = 9*(n-4)^2 for n > 5; G.f.:
x^2*(7*x^6-12*x^5-11*x^4-x-1) / (x-1)^3. Jianing Song (Nov 12 2026): the conjectures are correct.

Formalization notes.
* `IsTerm m` says that m is a perfect square and that floor(m/9) (natural-number division) is a
  perfect square. a(n) is the n-th such number in increasing order, `Nat.nth IsTerm (n - 1)`
  (Nat.nth counts from 0, the sequence from 1).
* The g.f. of the offset-1 sequence is Sum_{n >= 1} a(n) x^n, written as `PowerSeries.mk` of the
  function that is 0 at n = 0 and a(n) for n ≥ 1; the identity is stated over ℤ⟦X⟧,
  cross-multiplied by the denominator (x-1)^3, whose constant coefficient is -1.
-/

namespace OMA.S_oeis_a204503

open PowerSeries

/-- m is a perfect square and floor(m/9) is a perfect square. -/
def IsTerm (m : ℕ) : Prop := IsSquare m ∧ IsSquare (m / 9)

/-- A204503 (offset 1): the n-th term in increasing order. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- Barker's conjectures: the closed form for n > 5, and the g.f. (cross-multiplied). -/
theorem main :
    (∀ n : ℕ, 5 < n → a n = 9 * (n - 4) ^ 2) ∧
    PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℤ)) * ((X - 1) ^ 3 : PowerSeries ℤ) =
      X ^ 2 * (7 * X ^ 6 - 12 * X ^ 5 - 11 * X ^ 4 - X - 1) := by
  sorry

end OMA.S_oeis_a204503
