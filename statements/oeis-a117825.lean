import Mathlib

/-!
# A117825: Distance from n-th highly composite number (cf. A002182) to nearest prime.

Source: https://oeis.org/A117825
Credit: @divmxnd0x

Conjecture (stated in A117825): entries `> 1` will always be prime.

Formalization notes:
* `h` is highly composite (A002182) when `h > 0` and every `0 < m < h` has fewer divisors than `h`.
* `dist h` is the distance from `h` to the nearest prime: the least `d` such that `h + d` or
  `h - d` (with `d ≤ h`) is prime; data `1, 0, 1, 1, 1, 1, 1, 1, 1, 7, ...`.
* The conjecture: for every highly composite `h`, if `dist h > 1` then `dist h` is prime.
-/

namespace OMA.S_oeis_a117825

/-- `h` is a highly composite number. -/
def IsHighlyComposite (h : ℕ) : Prop :=
  0 < h ∧ ∀ m : ℕ, 0 < m → m < h → m.divisors.card < h.divisors.card

/-- The distance from `h` to the nearest prime. -/
noncomputable def dist (h : ℕ) : ℕ :=
  sInf {d : ℕ | (h + d).Prime ∨ (d ≤ h ∧ (h - d).Prime)}

/-- For highly composite `h`, a distance to the nearest prime greater than `1` is prime. -/
theorem main : ∀ h : ℕ, IsHighlyComposite h → 1 < dist h → (dist h).Prime := by
  sorry

end OMA.S_oeis_a117825
