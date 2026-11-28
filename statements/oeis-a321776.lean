import Mathlib

/-!
# OEIS A321776: Barker's g.f. and recurrence for six-part compositions with distinct multiplicities

Source: https://oeis.org/A321776 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A321776 (Alois P. Heinz, Nov 18 2018), offset 6: Number of compositions of n into parts with distinct multiplicities and with exactly six parts.
Formula section:
Conjectures from Colin Barker, Dec 11 2018: (Start)
G.f.: x^6*(1 + 7*x + 28*x^2 + 33*x^3 + 122*x^4 + 286*x^5 + 394*x^6 + 638*x^7 + 687*x^8 + 652*x^9 + 433*x^10 + 319*x^11) / ((1 - x)^3*(1 + x)^2*(1 - x + x^2)*(1 + x^2)*(1 + x + x^2)^2*(1 + x + x^2 + x^3 + x^4)).
a(n) = -a(n-1) - a(n-2) + a(n-4) + 2*a(n-5) + 3*a(n-6) + 2*a(n-7) + a(n-8) - a(n-9) - 2*a(n-10) - 3*a(n-11) - 2*a(n-12) - a(n-13) + a(n-15) + a(n-16) + a(n-17).
(End)

Formalization notes:
* A composition of n with exactly 6 parts is a sequence c : Fin 6 -> Fin (n + 1) of positive
  parts (c i).val with sum n; every part is at most n, so Fin (n + 1) loses nothing. The parts
  have distinct multiplicities when any two different values among the parts occur a different
  number of times.
* a(n) is defined for every n; it is 0 for n < 6, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n, which equals the entry's Sum_{n >= 6} a(n) x^n.
* The statement is the conjunction of the two parts of the site's problem: the g.f. as an identity
  in the formal power series ring over the rationals (denominator times A(x) equals numerator),
  and the recurrence, which the block states without a range, for every n > 17 (the g.f. numerator has degree 17, so this is exactly where the recurrence starts to hold) as an identity of integers.
* The definition reproduces the entry's data (1, 6, 21, 6, 96, 192, 142, 372, ... from n = 6,
  checked by direct enumeration).
-/

namespace OMA.S_oeis_a321776

open PowerSeries Finset

/-- Six positive parts with sum n whose distinct values occur with distinct multiplicities. -/
def good {n : ℕ} (c : Fin 6 → Fin (n + 1)) : Prop :=
  (∀ i, 0 < (c i).val) ∧ ∑ i, (c i).val = n ∧
    ∀ i j, c i ≠ c j →
      (univ.filter (fun k => c k = c i)).card ≠ (univ.filter (fun k => c k = c j)).card

instance : ∀ {n : ℕ}, DecidablePred (@good n) := fun c => by unfold good; infer_instance

/-- A321776: the number of compositions of n into parts with distinct multiplicities and with
exactly six parts. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 6 → Fin (n + 1))).filter good).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) ^ 3 * (1 + X) ^ 2 * (1 - X + X ^ 2) * (1 + X ^ 2) * (1 + X + X ^ 2) ^ 2 * (1 + X + X ^ 2 + X ^ 3 + X ^ 4)) =
        X ^ 6 * (1 + 7 * X + 28 * X ^ 2 + 33 * X ^ 3 + 122 * X ^ 4 + 286 * X ^ 5 + 394 * X ^ 6 + 638 * X ^ 7 + 687 * X ^ 8 + 652 * X ^ 9 + 433 * X ^ 10 + 319 * X ^ 11) ∧
    ∀ n : ℕ, 17 < n → (a n : ℤ) = -a (n - 1) - a (n - 2) + a (n - 4) + 2 * a (n - 5) + 3 * a (n - 6) + 2 * a (n - 7) + a (n - 8) - a (n - 9) - 2 * a (n - 10) - 3 * a (n - 11) - 2 * a (n - 12) - a (n - 13) + a (n - 15) + a (n - 16) + a (n - 17) := by
  sorry

end OMA.S_oeis_a321776
