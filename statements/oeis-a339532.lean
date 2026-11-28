import Mathlib

/-!
# OEIS A339532: Wu's recurrence and g.f. for the b with 2, 3 and 5 base-b Wieferich primes

Source: https://oeis.org/A339532 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Felix Fröhlich, Dec 08 2020), offset 1: Numbers b > 1 such that the smallest three primes,
i.e., 2, 3 and 5 are base-b Wieferich primes. The formula section states: Conjectures from Chai Wah
Wu, Aug 18 2025: (Start) a(n) = a(n-1) + a(n-8) - a(n-9) for n > 9. G.f.: x*(-x^8 + 108*x^7 +
36*x^6 + 56*x^5 + 52*x^4 + 56*x^3 + 36*x^2 + 108*x + 449)/(x^9 - x^8 - x + 1). (End)

Formalization notes:
* A prime p is a base-b Wieferich prime when b^(p-1) == 1 (mod p^2), as in the entry's
  Mathematica and PARI programs.
* The terms are the numbers b > 1 with the property in increasing order; with offset 1, a(n) is
  `Nat.nth P (n - 1)`.
* `main` is the conjunction of both conjectures. The g.f. is the series Sum_{n >= 1} a(n) x^n; the
  identity A(x) = N(x)/D(x) is stated as A(x)*D(x) = N(x) in Q[[x]], which is equivalent because
  D has constant term 1.
* Controls: the definitions give a(1..9) = 449, 557, 593, 649, 701, 757, 793, 901, 1349, as in the
  entry.
-/

namespace OMA.S_oeis_a339532

/-- `p` is a base-`b` Wieferich prime: `b^(p-1) ≡ 1 (mod p^2)`. -/
def Wieferich (p b : ℕ) : Prop := b ^ (p - 1) ≡ 1 [MOD p ^ 2]

/-- 2, 3 and 5 are base-`b` Wieferich primes. -/
def Q (b : ℕ) : Prop := Wieferich 2 b ∧ Wieferich 3 b ∧ Wieferich 5 b

/-- The entry's condition: `b > 1` and 2, 3 and 5 are base-`b` Wieferich primes. -/
def P (b : ℕ) : Prop := 1 < b ∧ Q b

/-- A339532 (offset 1): the `n`-th number with the property, in increasing order. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth P (n - 1)

open PowerSeries in
/-- Wu's conjectures: a(n) = a(n-1) + a(n-8) - a(n-9) for n > 9, and the g.f. -/
theorem main :
    (∀ n : ℕ, 9 < n → (a n : ℤ) = a (n - 1) + a (n - 8) - a (n - 9)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (X ^ 9 - X ^ 8 - X + 1) =
      X * (-X ^ 8 + 108 * X ^ 7 + 36 * X ^ 6 + 56 * X ^ 5 + 52 * X ^ 4 + 56 * X ^ 3 + 36 * X ^ 2 +
        108 * X + 449) := by
  sorry

end OMA.S_oeis_a339532
