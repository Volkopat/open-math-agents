import Mathlib

/-!
# OEIS A321777: Barker's g.f. and recurrence for seven-part compositions with distinct multiplicities

Source: https://oeis.org/A321777 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A321777 (Alois P. Heinz, Nov 18 2018), offset 7: Number of compositions of n into parts with distinct multiplicities and with exactly seven parts.
Formula section:
Conjectures from Colin Barker, Dec 11 2018: (Start)
G.f.: x^7*(1 + 8*x + 36*x^2 + 78*x^3 + 245*x^4 + 475*x^5 + 719*x^6 + 1069*x^7 + 1419*x^8 + 1539*x^9 + 1645*x^10 + 1478*x^11 + 1100*x^12 + 708*x^13 + 505*x^14) / ((1 - x)^3*(1 + x)^2*(1 - x + x^2)*(1 + x^2)*(1 + x + x^2)*(1 + x + x^2 + x^3 + x^4)*(1 + x + x^2 + x^3 + x^4 + x^5 + x^6)).
a(n) = -a(n-1) - a(n-2) - a(n-3) + a(n-5) + 2*a(n-6) + 3*a(n-7) + 3*a(n-8) + 2*a(n-9) + a(n-10) - a(n-11) - 2*a(n-12) - 3*a(n-13) - 3*a(n-14) - 2*a(n-15) - a(n-16) + a(n-18) + a(n-19) + a(n-20) + a(n-21) for n>27.
(End)

Formalization notes:
* A composition of n with exactly 7 parts is a sequence c : Fin 7 -> Fin (n + 1) of positive
  parts (c i).val with sum n; every part is at most n, so Fin (n + 1) loses nothing. The parts
  have distinct multiplicities when any two different values among the parts occur a different
  number of times.
* a(n) is defined for every n; it is 0 for n < 7, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n, which equals the entry's Sum_{n >= 7} a(n) x^n.
* The statement is the conjunction of the two parts of the site's problem: the g.f. as an identity
  in the formal power series ring over the rationals (denominator times A(x) equals numerator),
  and the recurrence for every n > 27 as an identity of integers.
* The definition reproduces the entry's data (1, 7, 28, 42, 168, 238, 280, 428, ... from n = 7,
  checked by direct enumeration).
-/

namespace OMA.S_oeis_a321777

open PowerSeries Finset

/-- Seven positive parts with sum n whose distinct values occur with distinct multiplicities. -/
def good {n : ℕ} (c : Fin 7 → Fin (n + 1)) : Prop :=
  (∀ i, 0 < (c i).val) ∧ ∑ i, (c i).val = n ∧
    ∀ i j, c i ≠ c j →
      (univ.filter (fun k => c k = c i)).card ≠ (univ.filter (fun k => c k = c j)).card

instance : ∀ {n : ℕ}, DecidablePred (@good n) := fun c => by unfold good; infer_instance

/-- A321777: the number of compositions of n into parts with distinct multiplicities and with
exactly seven parts. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 7 → Fin (n + 1))).filter good).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) ^ 3 * (1 + X) ^ 2 * (1 - X + X ^ 2) * (1 + X ^ 2) * (1 + X + X ^ 2) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6)) =
        X ^ 7 * (1 + 8 * X + 36 * X ^ 2 + 78 * X ^ 3 + 245 * X ^ 4 + 475 * X ^ 5 + 719 * X ^ 6 + 1069 * X ^ 7 + 1419 * X ^ 8 + 1539 * X ^ 9 + 1645 * X ^ 10 + 1478 * X ^ 11 + 1100 * X ^ 12 + 708 * X ^ 13 + 505 * X ^ 14) ∧
    ∀ n : ℕ, 27 < n → (a n : ℤ) = -a (n - 1) - a (n - 2) - a (n - 3) + a (n - 5) + 2 * a (n - 6) + 3 * a (n - 7) + 3 * a (n - 8) + 2 * a (n - 9) + a (n - 10) - a (n - 11) - 2 * a (n - 12) - 3 * a (n - 13) - 3 * a (n - 14) - 2 * a (n - 15) - a (n - 16) + a (n - 18) + a (n - 19) + a (n - 20) + a (n - 21) := by
  sorry

end OMA.S_oeis_a321777
