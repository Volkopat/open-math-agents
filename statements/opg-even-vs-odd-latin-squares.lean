import Mathlib

/-!
# Even vs. odd latin squares

Source: https://www.openproblemgarden.org/op/even_vs_odd_latin_squares
(N. Alon, M. Tarsi)
Credit: @ishaanzee

A latin square is even if the product of the signs of all of the row and column permutations is
`1` and is odd otherwise.

**Conjecture** (Alon–Tarsi). For every positive even integer `n`, the number of even latin squares
of order `n` and the number of odd latin squares of order `n` are different.

(For odd `n > 1` the two numbers are equal.)

Formalization: a latin square of order `n` is `L : Fin n → Fin n → Fin n` whose rows `j ↦ L i j`
and columns `i ↦ L i j` are all bijections of `Fin n`, i.e. permutations; their signs are
`Equiv.Perm.sign`. The square is even when the product of the `2n` signs is `1` (and odd when it
is `-1`). The numbers of even and odd latin squares are counted with `Nat.card`.
-/

namespace OMA.S_opg_even_vs_odd_latin_squares

open Equiv

/-- The latin squares of order `n`: every row and every column is a permutation of `Fin n`. -/
def LatinSquare (n : ℕ) : Type :=
  {L : Fin n → Fin n → Fin n //
    (∀ i, Function.Bijective (L i)) ∧ ∀ j, Function.Bijective fun i => L i j}

/-- The product of the signs of all row and column permutations of a latin square. -/
noncomputable def sign {n : ℕ} (L : LatinSquare n) : ℤˣ :=
  (∏ i, Perm.sign (Equiv.ofBijective _ (L.2.1 i))) *
    ∏ j, Perm.sign (Equiv.ofBijective _ (L.2.2 j))

/-- **Alon–Tarsi conjecture**: for every positive even `n`, the numbers of even and of odd latin
squares of order `n` differ. -/
theorem main : ∀ n : ℕ, 0 < n → Even n →
    Nat.card {L : LatinSquare n // sign L = 1} ≠ Nat.card {L : LatinSquare n // sign L = -1} := by
  sorry

end OMA.S_opg_even_vs_odd_latin_squares
