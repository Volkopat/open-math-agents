import Mathlib

/-!
# OEIS A182615: Wu's recurrence and generating function for the greatest k with floor(k/r^n) = n

Source: https://oeis.org/A182615 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Nov 22 2010), offset 1: Greatest k such that floor(k/r^n)=n, where
r = golden mean = (1+sqrt(5))/2. Data: 3, 7, 16, 34, 66, 125, 232, 422, 760, 1352, ...
Example: The integers k satisfying floor(k/r^3)=3 are 13,14,15,16, so that a(3)=16.
The formula section states: Conjectures from Chai Wah Wu, Jan 12 2023: (Start)
a(n) = 2*a(n-1) + 2*a(n-2) - 4*a(n-3) - 2*a(n-4) + 2*a(n-5) + a(n-6) for n > 8.
G.f.: x*(-x^7 - x^6 + 3*x^5 + 4*x^2 - x - 3)/((x - 1)*(x + 1)*(x^2 + x - 1)^2). (End)

Formalization notes:
* k ranges over the nonnegative integers and floor is `Int.floor` on the reals; a(n) is the
  supremum in the natural numbers of the set of such k (for n >= 1 the set is a nonempty finite
  interval, so this is its greatest element).
* The recurrence is stated in the integers for every n > 8 (all indices n - 1, ..., n - 6 are then
  at least 3, inside the offset).
* The generating function is A(x) = Sum_{n >= 1} a(n) x^n (offset 1). The identity
  A(x) = N(x)/D(x) is stated as A(x) D(x) = N(x) in Z[[x]], which is equivalent because
  D(x) = (x - 1)(x + 1)(x^2 + x - 1)^2 has constant term -1, a unit.
* `main` is the conjunction of Wu's two conjectures.
* Controls proved in the proof file: a(1..10) = 3, 7, 16, 34, 66, 125, 232, 422, 760, 1352, as in
  the entry.
-/

namespace OMA.S_oeis_a182615

open PowerSeries

/-- A182615(n): the greatest k with floor(k / r^n) = n, where r = (1 + sqrt 5)/2. -/
noncomputable def a (n : ℕ) : ℕ :=
  sSup {k : ℕ | ⌊(k : ℝ) / ((1 + Real.sqrt 5) / 2) ^ n⌋ = n}

/-- Wu's conjectures: the recurrence for n > 8 and the generating function. -/
theorem main :
    (∀ n : ℕ, 8 < n → (a n : ℤ) = 2 * a (n - 1) + 2 * a (n - 2) - 4 * a (n - 3) -
      2 * a (n - 4) + 2 * a (n - 5) + a (n - 6)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) *
      ((X - 1) * (X + 1) * (X ^ 2 + X - 1) ^ 2) =
        X * (-X ^ 7 - X ^ 6 + 3 * X ^ 5 + 4 * X ^ 2 - X - 3) := by
  sorry

end OMA.S_oeis_a182615
