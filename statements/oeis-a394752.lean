import Mathlib

/-!
# A394752: P-positions of the octal game .404

Source: https://oeis.org/A394752
Credit: @gblacher2

A394752 lists the indices of zeros (P-positions) in the Sprague-Grundy sequence of the octal game
.404: 0, 1, 2, 20, 28, 86, 286.

The entry describes the game: the digits are `d₁ = 4`, `d₂ = 0`, `d₃ = 4`, and bit 2 of a digit
`dᵢ` means "remove `i` stones and split the remaining stones into 2 nonempty piles". So a single
legal move from a pile of `n` stones is: take 1 stone and split the remaining `n - 1` stones into
two nonempty piles, or take 3 stones and split the remaining `n - 3` stones into two nonempty piles.
The entry's formula: `G(n) = mex ({G(a) xor G(b) : a + b = n - 1, a, b ≥ 1} ∪
{G(a) xor G(b) : a + b = n - 3, a, b ≥ 1})`, and the sequence lists the `n` with `G(n) = 0`.

Conjecture (in the entry): "a(7) = 286 is the largest P-position; equivalently, every n >= 287 is
an N-position (first player wins)." `main` states both parts: `G 286 = 0`, and `G n ≠ 0` for every
`n ≥ 287` (a single pile is an N-position exactly when its Sprague-Grundy value is nonzero).

Checks: with the definition below (computed by the same recursion), `G 0, …, G 19` are
0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 1, 1, 5, 6, 3, 3, 2, 2, 1, 1, and the zeros of `G` on `0 ≤ n ≤ 6000`
are exactly 0, 1, 2, 20, 28, 86, 286, the seven listed terms (checked numerically).
-/

namespace OMA.S_oeis_a394752

/-- The minimum excluded value of a finite set of natural numbers. -/
def mex (s : Finset ℕ) : ℕ :=
  Nat.find (p := fun m => m ∉ s)
    ⟨s.sup id + 1, fun h => Nat.not_succ_le_self _ (Finset.le_sup (f := id) h)⟩

/-- The Sprague-Grundy value `G n` of a single pile of `n` stones in the octal game .404:
a move removes `k ∈ {1, 3}` stones and splits the remaining `n - k` stones into two nonempty
piles of `a ≥ 1` and `n - k - a ≥ 1` stones, whose value is `G a xor G (n - k - a)`. -/
def G (n : ℕ) : ℕ :=
  let g : ℕ → ℕ := fun a => if a < n then G a else 0
  mex (((({1, 3} : Finset ℕ) ×ˢ Finset.range n).filter
      (fun p => 1 ≤ p.2 ∧ p.1 + p.2 < n)).image
      (fun p => g p.2 ^^^ g (n - p.1 - p.2)))

/-- **A394752 conjecture.** `286` is the largest P-position of the octal game .404: it is a
P-position, and every pile of `n ≥ 287` stones is an N-position. -/
theorem main : G 286 = 0 ∧ ∀ n : ℕ, 287 ≤ n → G n ≠ 0 := by
  sorry

end OMA.S_oeis_a394752
