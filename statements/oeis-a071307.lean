import Mathlib

/-!
# A071307: orthogonal matrices modulo 9

Source: https://oeis.org/A071307 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A071307 (offset 1): 1/2 number of n X n 0..8 matrices with MM' mod 9 = I.
Data 1, 12, 648, 419904, 3061100160.

Formula section: Conjecture: a(n) = 3^(n*(n-1)/2) * A071302(n) for n >= 1.
- Michel Marcus, Nov 08 2022

Related entry A071302 (offset 1): a(n) = (1/2) * (number of n X n 0..2 matrices M with
MM' mod 3 = I, where M' is the transpose of M and I is the n X n identity matrix).
Data 1, 4, 24, 576, 51840, 13063680, 9170703360, 19808719257600.

Formalization notes.
* An n X n matrix with entries in 0..m-1 is a matrix over `ZMod m`, and the condition
  MM' mod m = I is the equation `M * Mᵀ = 1` over `ZMod m`.
* `a n` is A071307(n) and `b n` is A071302(n): one half of the number of such matrices over
  `ZMod 9` and over `ZMod 3` (division of natural numbers; both counts are even for n >= 1).
* `main` is the conjecture for each n >= 1.
-/

namespace OMA.S_oeis_a071307

/-- A071307: one half of the number of n X n matrices M over Z/9 with M M' = I. -/
def a (n : ℕ) : ℕ :=
  Fintype.card {M : Matrix (Fin n) (Fin n) (ZMod 9) // M * M.transpose = 1} / 2

/-- A071302: one half of the number of n X n matrices M over Z/3 with M M' = I. -/
def b (n : ℕ) : ℕ :=
  Fintype.card {M : Matrix (Fin n) (Fin n) (ZMod 3) // M * M.transpose = 1} / 2

/-- Conjecture of Marcus: A071307(n) = 3^(n(n-1)/2) * A071302(n) for n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = 3 ^ (n * (n - 1) / 2) * b n := by
  sorry

end OMA.S_oeis_a071307
