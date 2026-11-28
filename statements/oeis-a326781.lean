import Mathlib

/-!
# OEIS A326781: Barker's g.f. and recurrence for the numbers with no 1 at a power-of-2 position

Source: https://oeis.org/A326781 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Gus Wiseman, Jul 25 2019), offset 1: No position of a 1 in the reversed binary expansion of
n is a power of 2. The formula section states: Conjectures from Colin Barker, Jul 27 2019: (Start)
G.f.: 4*x^2*(1 + 3*x + x^2 + 3*x^3 + x^4 + 3*x^5 + x^6 + 3*x^7 + x^8 + 3*x^9 + x^10 + 3*x^11 +
x^12 + 3*x^13 + x^14 + 35*x^15) / ((1 - x)^2*(1 + x)*(1 + x^2)*(1 + x^4)*(1 + x^8)).
a(n) = a(n-1) + a(n-16) - a(n-17) for n>17. (End)

Formalization notes:
* Positions in the reversed binary expansion are counted from 1 at the least significant bit, so
  bit i of m (`Nat.testBit m i`) sits at position i + 1, as in the entry's Mathematica program.
* The terms are the numbers m >= 0 with the property in increasing order; with offset 1, a(n) is
  `Nat.nth Good (n - 1)`, so a(1) = 0.
* `main` is the conjunction of both conjectures. The g.f. is the series Sum_{n >= 1} a(n) x^n; the
  identity A(x) = N(x)/D(x) is stated as A(x)*D(x) = N(x) in Q[[x]], which is equivalent because
  D has constant term 1.
* Controls: the definitions give a(1..20) = 0, 4, 16, 20, 32, 36, 48, 52, 64, 68, 80, 84, 96, 100,
  112, 116, 256, 260, 272, 276, as in the entry.
-/

namespace OMA.S_oeis_a326781

/-- No 1 of `m` sits at a position `i + 1` (bit `i`) that is a power of 2. -/
def Good (m : ℕ) : Prop := ∀ i, m.testBit i = true → ¬ ∃ k, i + 1 = 2 ^ k

/-- A326781 (offset 1): `a n` is the `n`-th number with the property, in increasing order. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth Good (n - 1)

open PowerSeries in
/-- Barker's conjectures: the g.f., and a(n) = a(n-1) + a(n-16) - a(n-17) for n > 17. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2) * (1 + X ^ 4) * (1 + X ^ 8)) =
      4 * X ^ 2 * (1 + 3 * X + X ^ 2 + 3 * X ^ 3 + X ^ 4 + 3 * X ^ 5 + X ^ 6 + 3 * X ^ 7 + X ^ 8 +
        3 * X ^ 9 + X ^ 10 + 3 * X ^ 11 + X ^ 12 + 3 * X ^ 13 + X ^ 14 + 35 * X ^ 15) ∧
    ∀ n : ℕ, 17 < n → (a n : ℤ) = a (n - 1) + a (n - 16) - a (n - 17) := by
  sorry

end OMA.S_oeis_a326781
