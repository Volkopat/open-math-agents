import Mathlib

/-!
# A126501: Number of n-tuples of numbers [0..5] (leading zeros allowed) in which adjacent digits differ by 4 or less.

Source: https://oeis.org/A126501 (conjecture by Colin Barker, Jan 20 2017)

`a(n)` (offset 0) is the number of tuples `f : Fin n → Fin 6` (entries in `0..5`) such that
any two adjacent entries differ by at most 4; adjacency is expressed by requiring the list
`List.ofFn f` of the entries to satisfy `List.IsChain` for the relation `|x - y| ≤ 4` (computed
in `ℤ`). For `n = 0` the empty tuple counts, so `a(0) = 1`.

The conjecture (no range is stated, so it is stated for every `n >= 0`, in `ℝ`):
a(n) = (2^(-1-n)*((5-sqrt(41))^n*(-7+sqrt(41)) + (5+sqrt(41))^n*(7+sqrt(41)))) / sqrt(41),
where `2^(-1-n)` is the integer power `(2 : ℝ) ^ (-1 - n : ℤ)`.
-/

namespace OMA.S_oeis_a126501

/-- Two digits differ by 4 or less. -/
def near (x y : Fin 6) : Prop := |((x : ℕ) : ℤ) - ((y : ℕ) : ℤ)| ≤ 4

instance : DecidableRel near := fun x y => by unfold near; infer_instance

/-- Adjacent entries of the tuple differ by 4 or less. -/
def good {n : ℕ} (f : Fin n → Fin 6) : Prop := List.IsChain near (List.ofFn f)

instance {n : ℕ} : DecidablePred (@good n) := fun f => by unfold good; infer_instance

/-- The number of good `n`-tuples. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter (fun f : Fin n → Fin 6 => good f)).card

theorem main : ∀ n : ℕ, (a n : ℝ) =
    (2 : ℝ) ^ (-1 - (n : ℤ)) * ((5 - Real.sqrt 41) ^ n * (-7 + Real.sqrt 41) +
      (5 + Real.sqrt 41) ^ n * (7 + Real.sqrt 41)) / Real.sqrt 41 := by
  sorry

end OMA.S_oeis_a126501
