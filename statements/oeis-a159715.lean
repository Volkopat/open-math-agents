import Mathlib

/-!
# A159715: three conjectured formulas

Source: https://oeis.org/A159715
Credit: @ivillar

Status: recorded in the entry as conjectures; no proof or verification is noted there. All three
statements follow from the closed form of the entry, which is used as the definition here; the second
conjecture is that closed form itself.

A159715 (offset 2): number of permutations of 2 indistinguishable copies of 1..n arranged in a circle
with exactly 1 local maximum;
data 4, 18, 72, 270, 972, 3402, 11664, 39366, 131220, 433026, 1417176, 4605822, ...

Conjectures from Colin Barker, Mar 23 2018:
(1) G.f.: 2*x^2*(2 - 3*x) / (1 - 3*x)^2.
(2) a(n) = 2*3^(n-2)*n for n>1.
(3) a(n) = 6*a(n-1) - 9*a(n-2) for n>3.

Formalization: the entry records a(n) = (copies*n)*(copies+1)^(n-2) with copies = 2, that is
a(n) = 2*n*3^(n-2), and this formula is the definition of a(n) used here for n ≥ 2, with values in ℤ;
a(0) = a(1) = 0, since the sequence has offset 2 and the conjectured g.f. starts at x^2. The g.f.
conjecture is stated as the identity (Sum_n a(n) x^n) * (1 - 3*x)^2 = 2*x^2*(2 - 3*x) of formal power
series over ℚ. `main` is the conjunction of (1), (2) and (3).
-/

namespace OMA.S_oeis_a159715

open PowerSeries

/-- a(n) = 2*n*3^(n-2) for n ≥ 2, the closed form recorded in the entry; a(0) = a(1) = 0. -/
def a (n : ℕ) : ℤ := if n < 2 then 0 else 2 * (n : ℤ) * 3 ^ (n - 2)

/-- The three conjectures of Colin Barker for A159715. -/
theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 3 * X) ^ 2 = 2 * X ^ 2 * (2 - 3 * X)) ∧
    (∀ n : ℕ, 1 < n → a n = 2 * 3 ^ (n - 2) * (n : ℤ)) ∧
    (∀ n : ℕ, 3 < n → a n = 6 * a (n - 1) - 9 * a (n - 2)) := by
  sorry

end OMA.S_oeis_a159715
