import Mathlib

/-!
# A267528: Number of ON (black) cells in the n-th iteration of the Rule 141 elementary cellular automaton starting with a single ON (black) cell

Source: https://oeis.org/A267528 (OEIS Foundation, CC BY-SA 4.0).
Sequence submitted by Robert Price.
Conjectures by Colin Barker (Jan 16 2016 and Apr 17 2019) and Stefano Spezia (Feb 20 2023).
Formalization: @longling12 (drafted with AI assistance)

The automaton evolves on the whole integer line starting at step 0 with a single ON cell
at site 0 on an OFF background. At step n, a(n) counts the ON cells among sites -n through n,
matching the Mathematica program in OEIS A267528; A007494 is the offset-0 sequence of
nonnegative integers congruent to 0 or 2 modulo 3. The ordinary generating function is stated
by clearing its denominator (constant term 1), and the exponential generating function is
stated via convergent power series sums over ℝ.
-/

namespace OMA.S_oeis_a267528

/-- Elementary cellular automaton local update for Wolfram rule 141. -/
def ruleOut (left center right : Bool) : Bool :=
  (141 : ℕ).testBit (4 * left.toNat + 2 * center.toNat + right.toNat)

/-- State of site `i` at step `n` under Rule 141, starting from a single ON cell at `0`. -/
def cell : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | n + 1, i => ruleOut (cell n (i - 1)) (cell n i) (cell n (i + 1))

/-- A267528(n): number of ON cells among sites `-n` through `n` at step `n`. -/
def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2 * n + 1), if cell n ((j : ℤ) - n) then 1 else 0

/-- A007494(m): the `m`-th nonnegative integer congruent to `0` or `2` modulo `3` (offset `0`). -/
noncomputable def a007494 (m : ℕ) : ℤ :=
  (Nat.nth (fun k : ℕ => k % 3 = 0 ∨ k % 3 = 2) m : ℤ)

open PowerSeries in
theorem main :
    (∀ n : ℕ, 4 < n → a n = a (n - 1) + a (n - 2) - a (n - 3)) ∧
    (∀ n : ℕ, 4 < n → a n = a007494 (n - 1)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X)) =
      1 + X ^ 3 + X ^ 4) ∧
    (∀ x : ℝ,
      HasSum (fun n : ℕ => (a n : ℝ) * x ^ n / (n.factorial : ℝ))
        (2 + x + (3 * x / 2 - 1) * Real.cosh x + 3 * (x - 1) * Real.sinh x / 2)) := by
  sorry

end OMA.S_oeis_a267528
