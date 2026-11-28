import Mathlib

/-!
# OEIS A200842: Barker's conjectures for 0..n arrays of 7 elements without any two consecutive increases or two consecutive decreases

Source: https://oeis.org/A200842 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A200842 (R. H. Hardin, Nov 23 2011), offset 1: Number of 0..n arrays x(0..6) of 7 elements without any two consecutive increases or two consecutive decreases.
Formula section:
Empirical: a(n) = (34/315)*n^7 + (163/90)*n^6 + (1981/180)*n^5 + (557/18)*n^4 + (7807/180)*n^3 + (1361/45)*n^2 + (333/35)*n + 1.
Conjectures from Colin Barker, Oct 14 2017: (Start)
G.f.: x*(128 + 441*x + 74*x^2 - 151*x^3 + 74*x^4 - 29*x^5 + 8*x^6 - x^7) / (1 - x)^8.
a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8) for n>8.
(End)

Formalization notes:
* An array x(0..6) of 7 elements of 0..n is a map x : Fin 7 -> Fin (n + 1). The
  condition is checked on every three consecutive entries x i, x j, x k (j = i + 1, k = i + 2):
  No two consecutive increases or decreases: no three consecutive entries with x(i) < x(i+1) < x(i+2) or x(i) > x(i+1) > x(i+2).
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n (a(0) = 1, the zero array, is left out).
* The statement is the conjunction of the parts of the site's problem: the g.f., as the identity
  A(x) (1 - x)^8 = x N(x) with N the numerator in the entry, in the formal power series ring
  over the rationals; and the recurrence, for every n > 8, as an identity of integers.
* The definition reproduces the entry's data (128, 1465, 8210, 31677, 96690, 250913, ... from n = 1, checked by direct
  enumeration for small n and against every listed term through the formula of the proof).
-/

namespace OMA.S_oeis_a200842

open PowerSeries Finset

/-- No two consecutive increases or decreases: no three consecutive entries with x(i) < x(i+1) < x(i+2) or x(i) > x(i+1) > x(i+2). -/
def good {L N : ℕ} (x : Fin L → Fin N) : Prop :=
  ∀ i j k : Fin L, j.val = i.val + 1 → k.val = i.val + 2 → ¬ (x i < x j ∧ x j < x k) ∧ ¬ (x i > x j ∧ x j > x k)

instance {L N : ℕ} : DecidablePred (@good L N) := fun x => by unfold good; infer_instance

/-- A200842: the number of 0..n arrays x(0..6) of 7 elements without any two consecutive increases or two consecutive decreases. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 7 → Fin (n + 1))).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 8 =
      X * (128 + 441 * X + 74 * X ^ 2 - 151 * X ^ 3 + 74 * X ^ 4 - 29 * X ^ 5 + 8 * X ^ 6 - X ^ 7) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  sorry

end OMA.S_oeis_a200842
