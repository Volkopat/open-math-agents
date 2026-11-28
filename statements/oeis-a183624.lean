import Mathlib

/-!
# A183624: Number of (n+1) X 2 0..2 arrays with every 2 x 2 subblock summing to 4.

Source: https://oeis.org/A183624 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

Entry (R. H. Hardin, Jan 06 2011), offset 1: a(n) is the number of (n+1) X 2 arrays with
entries in 0..2 such that every 2 X 2 subblock sums to 4. Terms: 19, 45, 115, 309, 859, ...
The formula section reads:

  Empirical: a(n) = 6*a(n-1) - 11*a(n-2) + 6*a(n-3).
  Conjectures from Colin Barker, Feb 22 2018: (Start)
  G.f.: x*(19 - 69*x + 54*x^2) / ((1 - x)*(1 - 2*x)*(1 - 3*x)).
  a(n) = 2 + 2^(2+n) + 3^(1+n).
  (End)

The empirical recurrence is in R. H. Hardin's entry (undated); the generating function and the
closed form are Colin Barker's. All three are stated here, as a conjunction.

Formalization notes:
* An array is a function `Fin (n + 1) → Fin 2 → Fin 3` (row, column ↦ entry in 0..2).
  With two columns, the 2 X 2 subblocks are exactly the blocks formed by rows i, i+1
  (0 ≤ i < n) and both columns; `IsValid` asks that each of them sums to 4.
* `a n` is the number of valid arrays for n ≥ 1, in ℤ. The entry has offset 1, so the
  generating function has no constant term; accordingly `a 0 := 0` (this value is used only in
  the generating-function clause, where it is the constant coefficient 0).
* The closed form is stated for every n ≥ 1 (the entry's range). The recurrence mentions
  a(n-3), so it is stated for n ≥ 4, where all terms belong to the sequence.
* The generating function is stated with its denominator cleared, in `PowerSeries ℤ`:
  (∑ a(n) x^n) * ((1 - x)(1 - 2x)(1 - 3x)) = x(19 - 69x + 54x^2). The denominator has
  constant term 1, so this is equivalent to the quotient form.
* Controls: the definition gives a(1..4) = 19, 45, 115, 309, as in the entry.
-/

namespace OMA.S_oeis_a183624

/-- An (n+1) X 2 array with entries in 0..2. -/
abbrev Grid (n : ℕ) := Fin (n + 1) → Fin 2 → Fin 3

/-- Every 2 X 2 subblock (rows i and i+1, both columns) sums to 4. -/
def IsValid {n : ℕ} (g : Grid n) : Prop :=
  ∀ i : Fin n,
    (g i.castSucc 0).val + (g i.castSucc 1).val + (g i.succ 0).val + (g i.succ 1).val = 4

instance {n : ℕ} (g : Grid n) : Decidable (IsValid g) := by
  unfold IsValid
  infer_instance

/-- A183624, offset 1; `a 0 = 0` is the constant coefficient of the generating function. -/
def a : ℕ → ℤ
  | 0 => 0
  | n + 1 => ((Finset.univ.filter (fun g : Grid (n + 1) => IsValid g)).card : ℤ)

open PowerSeries

/-- Barker's closed form (n ≥ 1), Hardin's empirical recurrence (n ≥ 4) and Barker's
generating function with its denominator cleared. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → a n = 2 + 2 ^ (2 + n) + 3 ^ (1 + n)) ∧
    (∀ n : ℕ, 4 ≤ n → a n = 6 * a (n - 1) - 11 * a (n - 2) + 6 * a (n - 3)) ∧
    (PowerSeries.mk a * ((1 - X) * (1 - 2 * X) * (1 - 3 * X)) =
      X * (19 - 69 * X + 54 * X ^ 2)) := by
  sorry

end OMA.S_oeis_a183624
