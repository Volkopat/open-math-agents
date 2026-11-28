import Mathlib

/-!
# OEIS A321774: Barker's g.f. and recurrence for four-part compositions with distinct multiplicities

Source: https://oeis.org/A321774 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A321774 (Alois P. Heinz, Nov 18 2018), offset 4: Number of compositions of n into parts with
distinct multiplicities and with exactly four parts.
Formula section:
Conjectures from Colin Barker, Dec 11 2018: (Start)
G.f.: x^4*(1 + 4*x + 4*x^2 + 7*x^3) / ((1 - x)^2*(1 + x)*(1 + x^2)*(1 + x + x^2)).
a(n) = a(n-3) + a(n-4) - a(n-7) for n>10.
(End)

Formalization notes:
* A composition of n with exactly four parts is a sequence c : Fin 4 -> Fin (n + 1) of positive
  parts (c i).val with sum n; every part is at most n, so Fin (n + 1) loses nothing. The parts
  have distinct multiplicities when any two different values among c 0, ..., c 3 occur a
  different number of times.
* a(n) is defined for every n; it is 0 for n < 4, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n, which equals the entry's Sum_{n >= 4} a(n) x^n.
* The statement is the conjunction of the two parts of the site's problem: the g.f. as the identity
  A(x) (1 - x)^2 (1 + x) (1 + x^2) (1 + x + x^2) = x^4 (1 + 4x + 4x^2 + 7x^3) in the formal power
  series ring over the rationals, and the recurrence for every n > 10 as an identity of integers.
* Controls proved in the proof file: the definition gives 0, 0, 0, 1, 4, 4, 8 for n = 1..7, and
  a(n) + 3 [4 | n] = 4 floor((n - 1)/3) for every n >= 1.
-/

namespace OMA.S_oeis_a321774

open PowerSeries Finset

/-- Four positive parts with sum n whose distinct values occur with distinct multiplicities. -/
def good {n : ℕ} (c : Fin 4 → Fin (n + 1)) : Prop :=
  (∀ i, 0 < (c i).val) ∧ ∑ i, (c i).val = n ∧
    ∀ i j, c i ≠ c j →
      (univ.filter (fun k => c k = c i)).card ≠ (univ.filter (fun k => c k = c j)).card

instance : ∀ {n : ℕ}, DecidablePred (@good n) := fun c => by unfold good; infer_instance

/-- A321774: the number of compositions of n into parts with distinct multiplicities and with
exactly four parts. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 4 → Fin (n + 1))).filter good).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2) * (1 + X + X ^ 2)) =
        X ^ 4 * (1 + 4 * X + 4 * X ^ 2 + 7 * X ^ 3) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = a (n - 3) + a (n - 4) - a (n - 7) := by
  sorry

end OMA.S_oeis_a321774
