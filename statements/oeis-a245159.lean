import Mathlib

/-!
# A245159: 0..4 arrays with new values introduced in order from both ends

A245159(n) is the number of length n arrays with values in 0..4 in which new values are
introduced in order (0 first, then 1, 2, 3, 4) when the array is read from the left end,
and also when it is read from the right end. Equivalently, for every position `i`, every
value smaller than `x i` occurs somewhere to the left of `i`, and also somewhere to the
right of `i`. A brute-force count of this reading gives
1, 1, 2, 4, 9, 23, 65, 199, 654, 2296 for n = 1..10, matching the listed terms.

The offset is 1; `a 0` is not a term of the sequence and is set to 0 in the generating
function, which has no constant term.

The problem: the conjectures of Colin Barker (Nov 03 2018):
  G.f.: x*(1 - 16*x + 103*x^2 - 346*x^3 + 656*x^4 - 710*x^5 + 425*x^6 - 124*x^7) /
        ((1 - x)^2*(1 - 2*x)^2*(1 - 3*x)^2*(1 - 5*x)),
  a(n) = (-3375 - 525*2^(4+n) - 1300*3^n + 3*5^n + 100*(297+9*2^(2+n) + 2*3^n)*n) / 43200.
The g.f. is stated after multiplying both sides by the denominator. The source gives no
range for the closed form, but at n = 1 it evaluates to 13440/43200, not a(1) = 1 (the g.f.
numerator has degree 8 > 7, so the closed form can only hold from n = 2 on); it is stated
for n > 1, where it agrees with all 210 terms of the b-file.

Source: https://oeis.org/A245159
Credit: @VashaTS
-/

namespace OMA.S_oeis_a245159

open PowerSeries

/-- New values are introduced in order from both ends: every value below `x i` occurs both
to the left and to the right of position `i`. -/
def InOrderBothEnds {n : ℕ} (x : Fin n → Fin 5) : Prop :=
  ∀ i : Fin n, ∀ v : Fin 5, v < x i →
    (∃ j : Fin n, j < i ∧ x j = v) ∧ ∃ j : Fin n, i < j ∧ x j = v

instance {n : ℕ} (x : Fin n → Fin 5) : Decidable (InOrderBothEnds x) := by
  unfold InOrderBothEnds; infer_instance

/-- A245159(n). -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin n → Fin 5 => InOrderBothEnds x).card

theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - X) ^ 2 * (1 - 2 * X) ^ 2 * (1 - 3 * X) ^ 2 * (1 - 5 * X)) =
      X * (1 - 16 * X + 103 * X ^ 2 - 346 * X ^ 3 + 656 * X ^ 4 - 710 * X ^ 5 + 425 * X ^ 6
        - 124 * X ^ 7) ∧
    ∀ n : ℕ, 1 < n →
      (a n : ℚ) = (-3375 - 525 * 2 ^ (4 + n) - 1300 * 3 ^ n + 3 * 5 ^ n
        + 100 * (297 + 9 * 2 ^ (2 + n) + 2 * 3 ^ n) * n) / 43200 := by
  sorry

end OMA.S_oeis_a245159
