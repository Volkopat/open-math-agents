import Mathlib

/-!
# A334811: shortest overlap-free binary word with `n` periods

Source: https://oeis.org/A334811
Credit: @jagraj28

`a(n)` is the length of a shortest overlap-free binary word having `n` periods. The entry
(Jeffrey Shallit, 2020) lists `1, 2, 5, 12, 46, 182, 726` for `n = 1, …, 7` and records:

  Conjecture: `a(n) = (17/6) * 4^(n-3) + 2/3` for `n ≥ 4`.

Definitions, as in the entry.
* A binary word is a `List Bool`.
* A word is *overlap-free* if it has no factor of the form `a x a x a`, where `a` is a single
  letter and `x` is a (possibly empty) word.
* A *period* of a word `w` is an integer `p` with `1 ≤ p ≤ |w|` such that `w[i] = w[i + p]` for
  every index `i` with `i + p < |w|`. A nonempty word always has the period `|w|`.
* "Having `n` periods" means having exactly `n` periods: the entry's examples `00100` (periods
  3, 4, 5) and `001001100100` (periods 9, 10, 11, 12) have exactly 3 and 4 periods. A brute-force
  search over words of length at most 14 gives `a(1), …, a(4) = 1, 2, 5, 12`, as in the entry.

`a n` is the infimum of the lengths of such words (`sInf ∅ = 0` by convention, which the
conjecture excludes). The conjectured formula is multiplied by 6 to stay in `ℕ`:
`6 * a(n) = 17 * 4^(n-3) + 4`. It matches the listed terms `a(4), …, a(7) = 12, 46, 182, 726`.
-/

namespace OMA.S_oeis_a334811

/-- A binary word is overlap-free if it has no factor `a x a x a` with `a` a letter. -/
def OverlapFree (w : List Bool) : Prop :=
  ¬ ∃ (u v x : List Bool) (a : Bool), w = u ++ (a :: x) ++ (a :: x) ++ [a] ++ v

/-- `p` is a period of `w`: `w[i] = w[i + p]` whenever both indices are in range. -/
def IsPeriod (w : List Bool) (p : ℕ) : Prop :=
  ∀ i < w.length - p, w[i]? = w[i + p]?

instance (w : List Bool) (p : ℕ) : Decidable (IsPeriod w p) := by
  unfold IsPeriod; infer_instance

/-- The number of periods `p` of `w`, with `1 ≤ p ≤ |w|`. -/
def numPeriods (w : List Bool) : ℕ :=
  ((Finset.Icc 1 w.length).filter (IsPeriod w)).card

/-- A334811: the least length of an overlap-free binary word with exactly `n` periods. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {L | ∃ w : List Bool, w.length = L ∧ OverlapFree w ∧ numPeriods w = n}

/-- Conjecture in OEIS A334811: `a(n) = (17/6) * 4^(n-3) + 2/3` for `n ≥ 4`. -/
theorem main : ∀ n ≥ 4, 6 * a n = 17 * 4 ^ (n - 3) + 4 := by
  sorry

end OMA.S_oeis_a334811
