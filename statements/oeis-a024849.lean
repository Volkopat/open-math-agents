import Mathlib

/-!
# OEIS A024849: Wu's recurrence and generating function

Source: https://oeis.org/A024849 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling), offset 2: a(n) = least m such that if r and s in
{|F(h+1)-tau*F(h)|: h = 1,2,...,n} satisfy r < s, then r < k/m < s for some integer k, where
F = A000045 (Fibonacci numbers) and tau = (1+sqrt(5))/2 (golden ratio). Formula section:
Conjectures from Chai Wah Wu, May 15 2026: a(n) = a(n-1) + 2*a(n-2) - a(n-3) - a(n-4) for n > 7.
G.f.: x^2*(x^5 - x^4 - 3*x^3 - 2*x^2 + 2*x + 2)/((x - 1)*(x + 1)*(x^2 + x - 1)).

Formalization notes:
* tau is Mathlib's `goldenRatio`, (1 + sqrt 5)/2, and F is `Nat.fib`.
* The set is the image of h = 1..n under h -> |F(h+1) - tau F(h)|. A positive integer m is
  admissible when every two elements r < s of the set have a fraction k/m (k an integer) strictly
  between them; a(n) is the least admissible m (`sInf` of the admissible positive integers).
* The g.f. is the formal power series Sum_{n >= 2} a(n) x^n over the rationals (offset 2, the
  coefficients of x^0 and x^1 are 0), and the claim is that it equals the numerator times the
  inverse of the denominator, whose constant term is 1. The recurrence is stated in the integers
  for n > 7.
* `main` is the conjunction of Wu's two conjectures.
* Controls (proved in the proof file): a(2..10) = 2, 4, 6, 9, 14, 23, 36, 59, 94, the entry's data.
-/

namespace OMA.S_oeis_a024849

open Real PowerSeries

/-- The set {|F(h+1) - tau F(h)| : h = 1..n}. -/
noncomputable def S (n : ℕ) : Finset ℝ :=
  (Finset.Icc 1 n).image fun h => |(Nat.fib (h + 1) : ℝ) - goldenRatio * Nat.fib h|

/-- m separates the set: between any two of its elements r < s there is a fraction k/m. -/
def Good (n m : ℕ) : Prop :=
  ∀ r ∈ S n, ∀ s ∈ S n, r < s → ∃ k : ℤ, r < k / m ∧ (k : ℝ) / m < s

/-- A024849(n): the least positive m that separates the set. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | 0 < m ∧ Good n m}

/-- The generating function Sum_{n >= 2} a(n) x^n (offset 2). -/
noncomputable def gf : ℚ⟦X⟧ := PowerSeries.mk fun n => if n < 2 then 0 else (a n : ℚ)

/-- Wu's conjectures: the recurrence for n > 7 and the g.f. -/
theorem main :
    (∀ n : ℕ, 7 < n → (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - a (n - 3) - a (n - 4)) ∧
    gf = X ^ 2 * (X ^ 5 - X ^ 4 - 3 * X ^ 3 - 2 * X ^ 2 + 2 * X + 2) *
      ((X - 1) * (X + 1) * (X ^ 2 + X - 1))⁻¹ := by
  sorry

end OMA.S_oeis_a024849
