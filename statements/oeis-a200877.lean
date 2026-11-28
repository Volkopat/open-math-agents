import Mathlib

/-!
# OEIS A200877: Barker's conjectures for 0..n arrays of 9 elements without any interior element greater than both neighbors or less than both neighbors

Source: https://oeis.org/A200877 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A200877 (R. H. Hardin, Nov 23 2011), offset 1: Number of 0..n arrays x(0..8) of 9 elements without any interior element greater than both neighbors or less than both neighbors.
Formula section:
Empirical: a(n) = (1/181440)*n^9 + (131/20160)*n^8 + (8893/30240)*n^7 + (4621/1440)*n^6 + (118933/8640)*n^5 + (83957/2880)*n^4 + (763489/22680)*n^3 + (36343/1680)*n^2 + (9169/1260)*n + 1.
Conjectures from Colin Barker, Oct 16 2017: (Start)
G.f.: x*(110 + 423*x - 422*x^2 - 766*x^3 + 848*x^4 - 246*x^5 + 90*x^6 - 44*x^7 + 10*x^8 - x^9) / (1 - x)^10.
a(n) = 10*a(n-1) - 45*a(n-2) + 120*a(n-3) - 210*a(n-4) + 252*a(n-5) - 210*a(n-6) + 120*a(n-7) - 45*a(n-8) + 10*a(n-9) - a(n-10) for n>10.
(End)

Formalization notes:
* An array x(0..8) of 9 elements of 0..n is a map x : Fin 9 -> Fin (n + 1). The
  condition is checked on every three consecutive entries x i, x j, x k (j = i + 1, k = i + 2):
  No interior element greater than both neighbors or less than both neighbors: for any three consecutive entries, x(i+1) is neither above both x(i), x(i+2) nor below both.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n (a(0) = 1, the zero array, is left out).
* The statement is the conjunction of the parts of the site's problem: the g.f., as the identity
  A(x) (1 - x)^10 = x N(x) with N the numerator in the entry, in the formal power series ring
  over the rationals; and the recurrence, for every n > 10, as an identity of integers.
* The definition reproduces the entry's data (110, 1523, 9858, 42479, 141688, 395929, ... from n = 1, checked by direct
  enumeration for small n and against every listed term through the formula of the proof).
-/

namespace OMA.S_oeis_a200877

open PowerSeries Finset

/-- No interior element greater than both neighbors or less than both neighbors: for any three consecutive entries, x(i+1) is neither above both x(i), x(i+2) nor below both. -/
def good {L N : ℕ} (x : Fin L → Fin N) : Prop :=
  ∀ i j k : Fin L, j.val = i.val + 1 → k.val = i.val + 2 → ¬ (x j > x i ∧ x j > x k) ∧ ¬ (x j < x i ∧ x j < x k)

instance {L N : ℕ} : DecidablePred (@good L N) := fun x => by unfold good; infer_instance

/-- A200877: the number of 0..n arrays x(0..8) of 9 elements without any interior element greater than both neighbors or less than both neighbors. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 9 → Fin (n + 1))).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 10 =
      X * (110 + 423 * X - 422 * X ^ 2 - 766 * X ^ 3 + 848 * X ^ 4 - 246 * X ^ 5 + 90 * X ^ 6 - 44 * X ^ 7 + 10 * X ^ 8 - X ^ 9) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) := by
  sorry

end OMA.S_oeis_a200877
