import Mathlib

/-!
# A109634: number of 1's among ternary strings with no two consecutive 1's

Source: https://oeis.org/A109634
Credit: @sntntHb

`a(n)` is the total number of letters `1` occurring in all ternary strings of length `n`
(over the alphabet `{0, 1, 2}`) that contain no two consecutive `1`'s. The entry records a
conjecture of R. J. Mathar (Aug 18 2008): `a(n) = A073388(n-1)`, where A073388 is the second
column of the convolution triangle A073387, with the closed form (from its entry)
`A073388(m) = Sum_{k=0..floor(m/2)} binomial(m-k+1, 1) * binomial(m-k, k) * 2^(m-k)`.

A ternary string of length `n` is a function `f : Fin n → Fin 3`; it has no two consecutive
`1`'s when there are no positions `i`, `j` with `j = i + 1` and `f i = f j = 1`. `a n` sums, over
these strings, the number of positions holding a `1`. This matches the data
`0, 1, 4, 16, 56, 188, 608, 1920, ...` (checked by brute force for `n ≤ 9`), and `b` below
matches A073388 `1, 4, 16, 56, 188, 608, ...`.

`main` states the conjecture for every `n ≥ 1`.
-/

namespace OMA.S_oeis_a109634

/-- `a n`: the number of `1`'s among all ternary strings of length `n` with no two consecutive
`1`'s (OEIS A109634). -/
def a (n : ℕ) : ℕ :=
  ∑ f ∈ Finset.univ.filter (fun f : Fin n → Fin 3 =>
      ∀ i j : Fin n, j.val = i.val + 1 → ¬ (f i = 1 ∧ f j = 1)),
    (Finset.univ.filter (fun i : Fin n => f i = 1)).card

/-- `b m`: OEIS A073388, via `Sum_{k=0..floor(m/2)} (m-k+1) * binomial(m-k, k) * 2^(m-k)`. -/
def b (m : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (m / 2 + 1), (m - k + 1) * Nat.choose (m - k) k * 2 ^ (m - k)

/-- Mathar's conjecture for OEIS A109634: `a(n) = A073388(n-1)` for `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = b (n - 1) := by
  sorry

end OMA.S_oeis_a109634
