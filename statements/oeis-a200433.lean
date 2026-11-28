import Mathlib

/-!
# Six bounded integers with no vanishing consecutive pair or triple

OEIS A200433 counts ordered six-term arrays in the integer interval `[-n,n]`.
The sum must vanish and every consecutive block of length two or three
must have nonzero sum. The sequence starts at index one. The same counting
definition gives zero at index zero, so it also supplies the constant
coefficient of the ordinary generating series.

The generating function and the recurrence were conjectured by Colin Barker.
Source: https://oeis.org/A200433
Credit: @jacklarmer
-/

namespace OMA.S_oeis_a200433

noncomputable def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin 6 => Finset.Icc (-(n : ℤ)) n).filter fun v =>
    ∑ i, v i = 0 ∧
    (∀ i : Fin 5, v i.castSucc + v i.succ ≠ 0) ∧
    ∀ i : Fin 4, v i.castSucc.castSucc + v i.succ.castSucc + v i.succ.succ ≠ 0).card

open PowerSeries

theorem main :
    (PowerSeries.mk (fun n => (a n : ℤ)) * (1 - X) ^ 6 =
      4 * X ^ 2 * (53 + 240 * X + 199 * X ^ 2 + 36 * X ^ 3)) ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) =
      6 * (a (n-1) : ℤ) - 15 * (a (n-2) : ℤ) + 20 * (a (n-3) : ℤ) -
      15 * (a (n-4) : ℤ) + 6 * (a (n-5) : ℤ) - (a (n-6) : ℤ)) := by
  sorry

end OMA.S_oeis_a200433
