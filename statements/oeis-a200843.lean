import Mathlib

/-!
# OEIS A200843: Barker's conjectures for 0..n arrays of 8 elements without any two consecutive increases or two consecutive decreases

Source: https://oeis.org/A200843 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A200843 (R. H. Hardin, Nov 23 2011), offset 1: Number of 0..n arrays x(0..7) of 8 elements without any two consecutive increases or two consecutive decreases.
Formula section:
Empirical: a(n) = (277/4032)*n^8 + (1375/1008)*n^7 + (4933/480)*n^6 + (2723/72)*n^5 + (14161/192)*n^4 + (11197/144)*n^3 + (216211/5040)*n^2 + (929/84)*n + 1.
Conjectures from Colin Barker, Oct 14 2017: (Start)
G.f.: x*(256 + 1753*x + 1313*x^2 - 679*x^3 + 177*x^4 - 77*x^5 + 35*x^6 - 9*x^7 + x^8) / (1 - x)^9.
a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>9.
(End)

Formalization notes:
* An array x(0..7) of 8 elements of 0..n is a map x : Fin 8 -> Fin (n + 1). The
  condition is checked on every three consecutive entries x i, x j, x k (j = i + 1, k = i + 2):
  No two consecutive increases or decreases: no three consecutive entries with x(i) < x(i+1) < x(i+2) or x(i) > x(i+1) > x(i+2).
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n (a(0) = 1, the zero array, is left out).
* The statement is the conjunction of the parts of the site's problem: the g.f., as the identity
  A(x) (1 - x)^9 = x N(x) with N the numerator in the entry, in the formal power series ring
  over the rationals; and the recurrence, for every n > 9, as an identity of integers.
* The definition reproduces the entry's data (256, 4057, 28610, 132263, 469116, 1384813, ... from n = 1, checked by direct
  enumeration for small n and against every listed term through the formula of the proof).
-/

namespace OMA.S_oeis_a200843

open PowerSeries Finset

/-- No two consecutive increases or decreases: no three consecutive entries with x(i) < x(i+1) < x(i+2) or x(i) > x(i+1) > x(i+2). -/
def good {L N : ℕ} (x : Fin L → Fin N) : Prop :=
  ∀ i j k : Fin L, j.val = i.val + 1 → k.val = i.val + 2 → ¬ (x i < x j ∧ x j < x k) ∧ ¬ (x i > x j ∧ x j > x k)

instance {L N : ℕ} : DecidablePred (@good L N) := fun x => by unfold good; infer_instance

/-- A200843: the number of 0..n arrays x(0..7) of 8 elements without any two consecutive increases or two consecutive decreases. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 8 → Fin (n + 1))).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (256 + 1753 * X + 1313 * X ^ 2 - 679 * X ^ 3 + 177 * X ^ 4 - 77 * X ^ 5 + 35 * X ^ 6 - 9 * X ^ 7 + X ^ 8) ∧
    ∀ n : ℕ, 9 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  sorry

end OMA.S_oeis_a200843
