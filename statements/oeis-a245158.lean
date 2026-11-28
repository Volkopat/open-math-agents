import Mathlib

/-!
# A245158: 0..3 arrays with new values introduced in order from both ends

A245158(n) is the number of length n arrays with values in 0..3 in which new values are
introduced in order (0 first, then 1, then 2, then 3) when the array is read from the left
end, and also when it is read from the right end. Equivalently, for every position `i`,
every value smaller than `x i` occurs somewhere to the left of `i`, and also somewhere to
the right of `i`. (Read from the left this is the usual restricted growth condition: the
first entry is 0 and each entry is at most one more than the maximum before it.)
A brute-force count of this reading gives 1, 1, 2, 4, 9, 23, 65, 199, 653, 2275, 8313 for
n = 1..11, matching the listed terms.

The offset is 1; `a 0` is not a term of the sequence and is set to 0 in the generating
function, which has no constant term.

The problem: the conjectures of Colin Barker (Nov 03 2018):
  G.f.: x*(1 - 9*x + 29*x^2 - 43*x^3 + 31*x^4 - 11*x^5) / ((1 - x)^2*(1 - 2*x)^2*(1 - 4*x)),
  a(n) = (-64 - 27*2^(2+n) + 4^n + 12*(32+3*2^n)*n) / 576 for n > 1.
The g.f. is stated after multiplying both sides by the denominator.

Source: https://oeis.org/A245158
Credit: @VashaTS
-/

namespace OMA.S_oeis_a245158

open PowerSeries

/-- New values are introduced in order from both ends: every value below `x i` occurs both
to the left and to the right of position `i`. -/
def InOrderBothEnds {n : ℕ} (x : Fin n → Fin 4) : Prop :=
  ∀ i : Fin n, ∀ v : Fin 4, v < x i →
    (∃ j : Fin n, j < i ∧ x j = v) ∧ ∃ j : Fin n, i < j ∧ x j = v

instance {n : ℕ} (x : Fin n → Fin 4) : Decidable (InOrderBothEnds x) := by
  unfold InOrderBothEnds; infer_instance

/-- A245158(n). -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin n → Fin 4 => InOrderBothEnds x).card

theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - X) ^ 2 * (1 - 2 * X) ^ 2 * (1 - 4 * X)) =
      X * (1 - 9 * X + 29 * X ^ 2 - 43 * X ^ 3 + 31 * X ^ 4 - 11 * X ^ 5) ∧
    ∀ n : ℕ, 1 < n →
      (a n : ℚ) = (-64 - 27 * 2 ^ (2 + n) + 4 ^ n + 12 * (32 + 3 * 2 ^ n) * n) / 576 := by
  sorry

end OMA.S_oeis_a245158
