import Mathlib

/-!
# OEIS A076935: a(n) = floor(cn) + 0 or + 1 for the real root c of 1-2x+x^2-x^3+x^4-x^5

Source: https://oeis.org/A076935 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Benoit Cloitre, Nov 27 2002), offset 1: a(1)=1,
a(n)=n-a(n-1)+a(a(n-1))-a(a(a(n-1)))+a(a(a(a(n-1))))-a(a(a(a(a(n-1))))). Formula section:
Conjecture: let c be the real root of 1-2*x+x^2-x^3+x^4-x^5, c=0.5974970086825179626770716964446...,
then a(n)=floor(cn) +0 /+ 1.

Formalization notes:
* The sequence is defined by its recurrence, with values in the integers. Every inner value a(m)
  lies between 1 and m, so each nested index is smaller than n; the guards `< n + 2` in the
  definition always hold and only make the recursion visibly well founded.
* The polynomial is strictly decreasing on the reals, so it has exactly one real root; `main` is
  stated for every real c with 1 - 2c + c^2 - c^3 + c^4 - c^5 = 0, which is that root.
* a(n) = floor(cn) + 0 / + 1 is read as: a(n) is floor(cn) or floor(cn) + 1, for every n >= 1.
* Controls (proved in the proof file): the definition gives the entry's data, for instance
  a(300) = 180 is reached through the same certified table.
-/

namespace OMA.S_oeis_a076935

/-- A076935: a(1) = 1, a(n) = n - a(n-1) + a(a(n-1)) - a(a(a(n-1))) + a(a(a(a(n-1)))) -
a(a(a(a(a(n-1))))) for n >= 2. Every inner value a(m) lies in 1..m, so each guard `< n + 2` holds;
the guards only make the recursion visibly well founded. -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    let x1 := a (n + 1)
    let x2 := if _h : x1.toNat < n + 2 then a x1.toNat else 0
    let x3 := if _h : x2.toNat < n + 2 then a x2.toNat else 0
    let x4 := if _h : x3.toNat < n + 2 then a x3.toNat else 0
    let x5 := if _h : x4.toNat < n + 2 then a x4.toNat else 0
    (n + 2 : ℤ) - x1 + x2 - x3 + x4 - x5
termination_by n => n
decreasing_by all_goals omega

/-- Cloitre's conjecture: for the real root c of 1 - 2x + x^2 - x^3 + x^4 - x^5, every a(n) with
n >= 1 is floor(cn) or floor(cn) + 1. -/
theorem main : ∀ c : ℝ, 1 - 2 * c + c ^ 2 - c ^ 3 + c ^ 4 - c ^ 5 = 0 →
    ∀ n : ℕ, 1 ≤ n → (a n = ⌊c * n⌋ ∨ a n = ⌊c * n⌋ + 1) := by
  sorry

end OMA.S_oeis_a076935
