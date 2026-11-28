import Mathlib

/-!
# A036685: the single-heap P-positions of Grundy's game

Source: https://oeis.org/A036685
Credit: @jagraj28

A036685 lists the single-heap P-positions in Grundy's game: 0, 1, 2, 4, 7, 10, 20, 23, 26, 50,
53, 270, ..., 1222 (42 terms). The entry records the conjecture that there are no other terms.

In Grundy's game a move splits one heap into two nonempty heaps of different sizes; the player who
cannot move loses (normal play). A single heap of size `n` is a P-position exactly when its
Sprague–Grundy value is 0, and the value of a heap is
`g(n) = mex { g(a) xor g(b) : a + b = n, 1 ≤ a < b }`.

`main` states: for the Grundy function `g` of the game (any function satisfying the recursion
above, which determines it uniquely by strong induction), the set of `n` with `g(n) = 0` is
exactly the set of the 42 listed terms.

Conventions: `mex T` is the least natural number not in `T`, written `sInf` of the complement.
A computation of `g` for `n ≤ 1300` gives exactly the listed zeros.
-/

namespace OMA.S_oeis_a036685

/-- `g` is the Sprague–Grundy function of single heaps in Grundy's game. -/
def IsGrundyFunction (g : ℕ → ℕ) : Prop :=
  ∀ n, g n = sInf {m : ℕ | ∀ a b : ℕ, 1 ≤ a → a < b → a + b = n → (g a ^^^ g b) ≠ m}

/-- The conjecture in OEIS A036685: the listed terms are all single-heap P-positions. -/
theorem main : ∀ g : ℕ → ℕ, IsGrundyFunction g →
    {n : ℕ | g n = 0} = {0, 1, 2, 4, 7, 10, 20, 23, 26, 50, 53, 270, 273, 276, 282, 285, 288,
      316, 334, 337, 340, 346, 359, 362, 365, 386, 389, 392, 566, 630, 633, 636, 639, 673, 676,
      682, 685, 923, 926, 929, 932, 1222} := by
  sorry

end OMA.S_oeis_a036685
