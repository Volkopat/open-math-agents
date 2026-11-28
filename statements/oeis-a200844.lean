import Mathlib

/-!
# OEIS A200844: Barker's conjectures for 0..n arrays of 9 elements without any two consecutive increases or two consecutive decreases

Source: https://oeis.org/A200844 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A200844 (R. H. Hardin, Nov 23 2011), offset 1: Number of 0..n arrays x(0..8) of 9 elements without any two consecutive increases or two consecutive decreases.
Formula section:
Empirical: a(n) = (124/2835)*n^9 + (1123/1120)*n^8 + (244/27)*n^7 + (1991/48)*n^6 + (57133/540)*n^5 + (74183/480)*n^4 + (291427/2268)*n^3 + (9739/168)*n^2 + (568/45)*n + 1.
Conjectures from Colin Barker, Oct 14 2017: (Start)
G.f.: x*(512 + 6115*x + 10390*x^2 - 618*x^3 - 622*x^4 + 36*x^5 + 94*x^6 - 44*x^7 + 10*x^8 - x^9) / (1 - x)^10.
a(n) = 10*a(n-1) - 45*a(n-2) + 120*a(n-3) - 210*a(n-4) + 252*a(n-5) - 210*a(n-6) + 120*a(n-7) - 45*a(n-8) + 10*a(n-9) - a(n-10) for n > 10.
(End)

Formalization notes:
* An array x(0..8) of 9 elements of 0..n is a map x : Fin 9 -> Fin (n + 1). The
  condition is checked on every three consecutive entries x i, x j, x k (j = i + 1, k = i + 2):
  No two consecutive increases or decreases: no three consecutive entries with x(i) < x(i+1) < x(i+2) or x(i) > x(i+1) > x(i+2).
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n (a(0) = 1, the zero array, is left out).
* The statement is the conjunction of the parts of the site's problem: the g.f., as the identity
  A(x) (1 - x)^10 = x N(x) with N the numerator in the entry, in the formal power series ring
  over the rationals; and the recurrence, for every n > 10, as an identity of integers.
* The definition reproduces the entry's data (512, 11235, 99700, 552247, 2276028, 7642875, ... from n = 1, checked by direct
  enumeration for small n and against every listed term through the formula of the proof).
-/

namespace OMA.S_oeis_a200844

open PowerSeries Finset

/-- No two consecutive increases or decreases: no three consecutive entries with x(i) < x(i+1) < x(i+2) or x(i) > x(i+1) > x(i+2). -/
def good {L N : ℕ} (x : Fin L → Fin N) : Prop :=
  ∀ i j k : Fin L, j.val = i.val + 1 → k.val = i.val + 2 → ¬ (x i < x j ∧ x j < x k) ∧ ¬ (x i > x j ∧ x j > x k)

instance {L N : ℕ} : DecidablePred (@good L N) := fun x => by unfold good; infer_instance

/-- A200844: the number of 0..n arrays x(0..8) of 9 elements without any two consecutive increases or two consecutive decreases. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 9 → Fin (n + 1))).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 10 =
      X * (512 + 6115 * X + 10390 * X ^ 2 - 618 * X ^ 3 - 622 * X ^ 4 + 36 * X ^ 5 + 94 * X ^ 6 - 44 * X ^ 7 + 10 * X ^ 8 - X ^ 9) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) := by
  sorry

end OMA.S_oeis_a200844
