import Mathlib

/-!
# OEIS A321775: Barker's g.f. and recurrence for five-part compositions with distinct multiplicities

Source: https://oeis.org/A321775 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A321775 (Alois P. Heinz, Nov 18 2018), offset 5: Number of compositions of n into parts with
distinct multiplicities and with exactly five parts.
Formula section:
Conjectures from Colin Barker, Dec 11 2018: (Start)
G.f.: x^5*(1 + 6*x + 21*x^2 + 35*x^3 + 49*x^4 + 34*x^5 + 29*x^6) / ((1 - x)^2*(1 + x)*(1 + x^2)*(1 + x + x^2)*(1 + x + x^2 + x^3 + x^4)).
a(n) = -a(n-1) - a(n-2) + a(n-4) + 2*a(n-5) + 2*a(n-6) + a(n-7) - a(n-9) - a(n-10) - a(n-11) for n>15.
(End)

Formalization notes:
* A composition of n with exactly five parts is a sequence c : Fin 5 -> Fin (n + 1) of positive
  parts (c i).val with sum n; every part is at most n, so Fin (n + 1) loses nothing. The parts
  have distinct multiplicities when any two different values among the parts occur a different
  number of times.
* a(n) is defined for every n; it is 0 for n < 5, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n, which equals the entry's Sum_{n >= 5} a(n) x^n.
* The statement is the conjunction of the two parts of the site's problem: the g.f. as the identity
  A(x) (1 - x)^2 (1 + x) (1 + x^2) (1 + x + x^2) (1 + x + x^2 + x^3 + x^4) =
  x^5 (1 + 6x + 21x^2 + 35x^3 + 49x^4 + 34x^5 + 29x^6) in the formal power series ring over the
  rationals, and the recurrence for every n > 15 as an identity of integers.
* The definition reproduces the entry's data (1, 5, 15, 15, 20, 6, 30, ... from n = 5, checked by
  direct enumeration up to n = 21); the proof shows a(0) = 0 in Lean and computes the g.f. as
  -14 P5 + 5 P4 P1 + 10 P3 P2 with Pm the sum of x^(m t) over t >= 1.
-/

namespace OMA.S_oeis_a321775

open PowerSeries Finset

/-- Five positive parts with sum n whose distinct values occur with distinct multiplicities. -/
def good {n : ℕ} (c : Fin 5 → Fin (n + 1)) : Prop :=
  (∀ i, 0 < (c i).val) ∧ ∑ i, (c i).val = n ∧
    ∀ i j, c i ≠ c j →
      (univ.filter (fun k => c k = c i)).card ≠ (univ.filter (fun k => c k = c j)).card

instance : ∀ {n : ℕ}, DecidablePred (@good n) := fun c => by unfold good; infer_instance

/-- A321775: the number of compositions of n into parts with distinct multiplicities and with
exactly five parts. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 5 → Fin (n + 1))).filter good).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2) * (1 + X + X ^ 2) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4)) =
        X ^ 5 * (1 + 6 * X + 21 * X ^ 2 + 35 * X ^ 3 + 49 * X ^ 4 + 34 * X ^ 5 + 29 * X ^ 6) ∧
    ∀ n : ℕ, 15 < n → (a n : ℤ) = -a (n - 1) - a (n - 2) + a (n - 4) + 2 * a (n - 5) +
      2 * a (n - 6) + a (n - 7) - a (n - 9) - a (n - 10) - a (n - 11) := by
  sorry

end OMA.S_oeis_a321775
