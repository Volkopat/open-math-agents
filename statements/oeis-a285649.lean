import Mathlib

/-!
# OEIS A285649

Decimal representation of the diagonal from the corner to the origin of the n-th stage of growth
of the two-dimensional cellular automaton defined by "Rule 73", based on the 5-celled von Neumann
neighborhood.

Source: https://oeis.org/A285649
Conjectures from Colin Barker, Apr 24 2017:
  G.f.: (1 + 2*x - 4*x^2 + 2*x^3 - x^4 + 11*x^5 + 4*x^6 - 12*x^7) /
        ((1 - x)*(1 + x)*(1 - 2*x)*(1 + 2*x)).
  a(n) = 0 for n>3 and even.
  a(n) = 2^(1+n) - 1 for n>3 and odd.
  a(n) = 5*a(n-2) - 4*a(n-4) for n>7.

Conventions (as in the merged statement of the sibling entry A285645): initially only the origin
is ON. On the whole integer plane, bit c+2s of the rule gives the next state, where c is the
central bit and s counts the four orthogonal ON neighbors (the rule is applied to every cell,
including the background). The diagonal of stage n runs from the corner (-n, -n) to the origin
inclusive; its first cell is the most significant binary digit. The sequence starts at n = 0
(data: 1, 2, 1, 12, 0, 63, 0, 255, ...). Generating functions are ordinary formal power series.

Prior art: an informal treatment of the Rule 73 diagonals A285647-A285650 (the
'Von-Neumann-diagonals' notes) is referenced in the withdrawn statement PRs #15157 and #15312;
this formalization follows that result (the whole pattern is uniform from stage 4 on).
-/

namespace OMA.S_oeis_a285649

open PowerSeries

/-- Synchronous evolution on the integer plane from one ON cell. -/
def state (r : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t+1, x, y =>
    let s := state r t
    r.testBit ((s x y).toNat + 2 * ((s (x-1) y).toNat + (s (x+1) y).toNat +
      (s x (y-1)).toNat + (s x (y+1)).toNat))

/-- Read the diagonal from corner to origin, most significant digit first. -/
def digits (r n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n+1), ((state r n ((i : ℤ) - n) ((i : ℤ) - n)).toNat : ℤ) * 2 ^ (n-i)

/-- A285649(n). -/
def a (n : ℕ) : ℤ := digits 73 n

theorem main :
    (PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) =
      1 + 2 * X - 4 * X ^ 2 + 2 * X ^ 3 - X ^ 4 + 11 * X ^ 5 + 4 * X ^ 6 - 12 * X ^ 7) ∧
    (∀ n : ℕ, 3 < n → n % 2 = 0 → a n = 0) ∧
    (∀ n : ℕ, 3 < n → n % 2 = 1 → a n = 2 ^ (1 + n) - 1) ∧
    (∀ n : ℕ, 7 < n → a n = 5 * a (n - 2) - 4 * a (n - 4)) := by
  sorry

end OMA.S_oeis_a285649
