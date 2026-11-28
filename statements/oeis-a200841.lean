import Mathlib

/-!
# OEIS A200841: Barker's conjectures for 0..n arrays of 6 elements without any two consecutive increases or two consecutive decreases

Source: https://oeis.org/A200841 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A200841 (R. H. Hardin, Nov 23 2011), offset 1: Number of 0..n arrays x(0..5) of 6 elements without any two consecutive increases or two consecutive decreases.
Formula section:
Empirical: a(n) = (61/360)*n^6 + (93/40)*n^5 + (779/72)*n^4 + (521/24)*n^3 + (1801/90)*n^2 + (239/30)*n + 1.
Conjectures from Colin Barker, Oct 14 2017: (Start)
G.f.: x*(64 + 81*x - 3*x^2 - 36*x^3 + 22*x^4 - 7*x^5 + x^6) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.
(End)

Formalization notes:
* An array x(0..5) of 6 elements of 0..n is a map x : Fin 6 -> Fin (n + 1). The
  condition is checked on every three consecutive entries x i, x j, x k (j = i + 1, k = i + 2):
  No two consecutive increases or decreases: no three consecutive entries with x(i) < x(i+1) < x(i+2) or x(i) > x(i+1) > x(i+2).
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n (a(0) = 1, the zero array, is left out).
* The statement is the conjunction of the parts of the site's problem: the g.f., as the identity
  A(x) (1 - x)^7 = x N(x) with N the numerator in the entry, in the formal power series ring
  over the rationals; and the recurrence, for every n > 7, as an identity of integers.
* The definition reproduces the entry's data (64, 529, 2356, 7587, 19930, 45465, ... from n = 1, checked by direct
  enumeration for small n and against every listed term through the formula of the proof).
-/

namespace OMA.S_oeis_a200841

open PowerSeries Finset

/-- No two consecutive increases or decreases: no three consecutive entries with x(i) < x(i+1) < x(i+2) or x(i) > x(i+1) > x(i+2). -/
def good {L N : ℕ} (x : Fin L → Fin N) : Prop :=
  ∀ i j k : Fin L, j.val = i.val + 1 → k.val = i.val + 2 → ¬ (x i < x j ∧ x j < x k) ∧ ¬ (x i > x j ∧ x j > x k)

instance {L N : ℕ} : DecidablePred (@good L N) := fun x => by unfold good; infer_instance

/-- A200841: the number of 0..n arrays x(0..5) of 6 elements without any two consecutive increases or two consecutive decreases. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 6 → Fin (n + 1))).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (64 + 81 * X - 3 * X ^ 2 - 36 * X ^ 3 + 22 * X ^ 4 - 7 * X ^ 5 + X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a200841
