import Mathlib

/-!
# A190035: Number of nondecreasing arrangements of n+2 numbers in 0..3 with the last equal to 3 and each after the second equal to the sum of one or two of the preceding three

Source: https://oeis.org/A190035
Credit: @Jack-Whitcomb

The conjectures (Colin Barker, May 03 2018):
  G.f.: x*(5 - 3*x + x^2 + x^3) / (1 - x)^2.
  a(n) = 2*a(n-1) - a(n-2) for n > 4.

Reading of the definition. An arrangement is a sequence `s 0, …, s (n+1)` of numbers in `0..3`,
nondecreasing, with `s (n+1) = 3`, such that every term `s i` with `i ≥ 2` (each after the
second) is equal to one of `s (i-1), s (i-2), s (i-3)` (those that exist), or to the sum of two
of them taken at two different positions. This is the reading that reproduces the data of the
OEIS entry (5, 7, 10, 14, 18, 22, … for n = 1, 2, 3, …) and its list of the 14 solutions for
n = 4; letting a term be used twice (e.g. `2 = 1 + 1` from a single `1`) gives 5, 8, 12, … instead.

The sequence has offset 1. The generating function `x*(5 - 3*x + x^2 + x^3)/(1 - x)^2` has
constant term 0, so the g.f. claim is stated for the series `∑_{n ≥ 1} a(n) x^n`, i.e. with the
`n = 0` coefficient taken to be 0 (the counting definition is not used at `n = 0`).
-/

namespace OMA.S_oeis_a190035

open PowerSeries

/-- The arrangement `s` of `n + 2` numbers in `0..3` satisfies the condition of A190035. -/
def IsArrangement (n : ℕ) (s : Fin (n + 2) → Fin 4) : Prop :=
  (∀ i j : Fin (n + 2), i ≤ j → s i ≤ s j) ∧
  s (Fin.last (n + 1)) = 3 ∧
  ∀ i : Fin (n + 2), 2 ≤ i.val →
    (∃ j : Fin (n + 2), j < i ∧ i.val ≤ j.val + 3 ∧ s i = s j) ∨
    (∃ j k : Fin (n + 2), j < k ∧ k < i ∧ i.val ≤ j.val + 3 ∧
      (s i : ℕ) = (s j : ℕ) + (s k : ℕ))

instance (n : ℕ) : DecidablePred (IsArrangement n) := fun s => by
  unfold IsArrangement; infer_instance

/-- `a n`: the number of such arrangements of `n + 2` numbers (meaningful for `n ≥ 1`). -/
def a (n : ℕ) : ℕ := (Finset.univ.filter (IsArrangement n)).card

theorem main :
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) * (1 - X) ^ 2 =
        X * (5 - 3 * X + X ^ 2 + X ^ 3)) ∧
      ∀ n : ℕ, 4 < n → (a n : ℤ) = 2 * (a (n - 1) : ℤ) - (a (n - 2) : ℤ) := by
  sorry

end OMA.S_oeis_a190035
