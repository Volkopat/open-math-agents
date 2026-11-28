import Mathlib

/-!
# Maximum number of mutually orthogonal n-bit sequences

Source: https://mathoverflow.net/questions/254840
Asked by MathOverflow user lchen.

The question asks for the maximum number of mutually orthogonal `n`-bit sequences.
A Hadamard matrix gives `n` mutually orthogonal `n`-bit sequences, and the question
asks: can we do better, i.e. can one construct more than `n` mutually orthogonal
`n`-bit sequences?

Translation choices.
* As for the rows of a Hadamard matrix, a bit is encoded by a sign, so an `n`-bit
  sequence is a function `Fin n → ℤ` all of whose values are `1` or `-1`, and two
  sequences `a, b` are orthogonal when `∑ i, a i * b i = 0`.
* A family of mutually orthogonal sequences is a finite set of such sequences in which
  any two distinct members are orthogonal.
* The length `n` is at least one (for `n = 0` there is a single, empty, sequence).
* `main` is the affirmative answer to the question whether one can do better: for some
  length `n ≥ 1` there is a family of more than `n` mutually orthogonal `n`-bit sequences.
  The second part of the question, about sequences of low correlation, is not
  formalized here.
-/

namespace OMA.S_mo_254840

theorem main :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ S : Finset (Fin n → ℤ),
      (∀ a ∈ S, ∀ i, a i = 1 ∨ a i = -1) ∧
      (∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∑ i, a i * b i = 0) ∧
      n < S.card := by
  sorry

end OMA.S_mo_254840
