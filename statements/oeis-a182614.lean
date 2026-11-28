import Mathlib

/-!
# OEIS A182614: Wu's recurrence and generating function for the least k with floor(k/r^n) = n

Source: https://oeis.org/A182614 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Nov 22 2010), offset 1: Least k such that floor(k/r^n)=n, where
r = golden ratio = (1+sqrt(5))/2. Data: 2, 6, 13, 28, 56, 108, 204, 376, 685, 1230, ...
The formula section states: Conjectures from Chai Wah Wu, Jan 12 2023: (Start)
a(n) = 2*a(n-1) + 2*a(n-2) - 4*a(n-3) - 2*a(n-4) + 2*a(n-5) + a(n-6) for n > 6.
G.f.: x*(-2*x^4 + 2*x^3 + 3*x^2 - 2*x - 2)/((x - 1)*(x + 1)*(x^2 + x - 1)^2). (End)

Formalization notes:
* k ranges over the nonnegative integers and floor is `Int.floor` on the reals; a(n) is the
  infimum in the natural numbers of the set of such k (for n >= 1 the set is nonempty, so this
  is its least element).
* The recurrence is stated in the integers for every n > 6 (all indices n - 1, ..., n - 6 are then
  at least 1, inside the offset).
* The generating function is A(x) = Sum_{n >= 1} a(n) x^n (offset 1). The identity
  A(x) = N(x)/D(x) is stated as A(x) D(x) = N(x) in Z[[x]], which is equivalent because
  D(x) = (x - 1)(x + 1)(x^2 + x - 1)^2 has constant term -1, a unit.
* `main` is the conjunction of Wu's two conjectures.
* Controls proved in the proof file: a(1..16), the entry's data.
-/

namespace OMA.S_oeis_a182614

open PowerSeries

/-- A182614(n): the least k with floor(k / r^n) = n, where r = (1 + sqrt 5)/2. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | ⌊(k : ℝ) / ((1 + Real.sqrt 5) / 2) ^ n⌋ = n}

/-- Wu's conjectures: the recurrence for n > 6 and the generating function. -/
theorem main :
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 2 * a (n - 1) + 2 * a (n - 2) - 4 * a (n - 3) -
      2 * a (n - 4) + 2 * a (n - 5) + a (n - 6)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) *
      ((X - 1) * (X + 1) * (X ^ 2 + X - 1) ^ 2) =
        X * (-2 * X ^ 4 + 2 * X ^ 3 + 3 * X ^ 2 - 2 * X - 2) := by
  sorry

end OMA.S_oeis_a182614
