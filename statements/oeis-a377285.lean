import Mathlib

/-!
# A377285: Position of first 0 in the n-th differences of the strict partition numbers A000009, or 0 if 0 does not appear.

Source: https://oeis.org/A377285
Credit: @eltociear

`a(n)` (offset 0) is the position of the first `0` in the `n`-th forward differences of the strict
partition numbers `q(0), q(1), q(2), …` (A000009), or `0` if no `0` appears (`a(7) = 7`: the 7th
differences are `25, -16, 7, -6, 10, -9, 0, …`). The entry records (Chai Wah Wu):

  a(12) = 47. Conjecture: a(n) = 0 for n > 12.

`main` states that for every `n > 12` the `n`-th differences never vanish. The differences are
taken in `ℤ`: `Δ f k = f (k + 1) - f k`, and the `n`-th differences are `Δ^[n]` applied to `q`.
-/

namespace OMA.S_oeis_a377285

/-- The strict partition function `q(m)` (A000009): partitions of `m` into distinct parts. -/
def q (m : ℕ) : ℕ := (Nat.Partition.distincts m).card

/-- The forward difference operator on integer sequences. -/
def Δ (f : ℕ → ℤ) (k : ℕ) : ℤ := f (k + 1) - f k

/-- The conjecture in OEIS A377285: for `n > 12`, no `n`-th difference of `q` is `0`. -/
theorem main : ∀ n : ℕ, 12 < n → ∀ k : ℕ, (Δ^[n] (fun m => (q m : ℤ))) k ≠ 0 := by
  sorry

end OMA.S_oeis_a377285
