import Mathlib

/-!
# OEIS A200875: Barker's conjectures for 0..n arrays of 7 elements without any interior element greater than both neighbors or less than both neighbors

Source: https://oeis.org/A200875 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A200875 (R. H. Hardin, Nov 23 2011), offset 1: Number of 0..n arrays x(0..6) of 7 elements without any interior element greater than both neighbors or less than both neighbors.
Formula section:
Empirical: a(n) = (1/2520)*n^7 + (17/180)*n^6 + (281/180)*n^5 + (64/9)*n^4 + (4927/360)*n^3 + (2303/180)*n^2 + (604/105)*n + 1.
Conjectures from Colin Barker, Oct 16 2017: (Start)
G.f.: x*(42 + 7*x - 40*x^2 - 55*x^3 + 70*x^4 - 29*x^5 + 8*x^6 - x^7) / (1 - x)^8.
a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8) for n>8.
(End)

Formalization notes:
* An array x(0..6) of 7 elements of 0..n is a map x : Fin 7 -> Fin (n + 1). The
  condition is checked on every three consecutive entries x i, x j, x k (j = i + 1, k = i + 2):
  No interior element greater than both neighbors or less than both neighbors: for any three consecutive entries, x(i+1) is neither above both x(i), x(i+2) nor below both.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n (a(0) = 1, the zero array, is left out).
* The statement is the conjunction of the parts of the site's problem: the g.f., as the identity
  A(x) (1 - x)^8 = x N(x) with N the numerator in the entry, in the formal power series ring
  over the rationals; and the recurrence, for every n > 8, as an identity of integers.
* The definition reproduces the entry's data (42, 343, 1528, 4917, 12890, 29325, ... from n = 1, checked by direct
  enumeration for small n and against every listed term through the formula of the proof).
-/

namespace OMA.S_oeis_a200875

open PowerSeries Finset

/-- No interior element greater than both neighbors or less than both neighbors: for any three consecutive entries, x(i+1) is neither above both x(i), x(i+2) nor below both. -/
def good {L N : ℕ} (x : Fin L → Fin N) : Prop :=
  ∀ i j k : Fin L, j.val = i.val + 1 → k.val = i.val + 2 → ¬ (x j > x i ∧ x j > x k) ∧ ¬ (x j < x i ∧ x j < x k)

instance {L N : ℕ} : DecidablePred (@good L N) := fun x => by unfold good; infer_instance

/-- A200875: the number of 0..n arrays x(0..6) of 7 elements without any interior element greater than both neighbors or less than both neighbors. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 7 → Fin (n + 1))).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 8 =
      X * (42 + 7 * X - 40 * X ^ 2 - 55 * X ^ 3 + 70 * X ^ 4 - 29 * X ^ 5 + 8 * X ^ 6 - X ^ 7) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  sorry

end OMA.S_oeis_a200875
