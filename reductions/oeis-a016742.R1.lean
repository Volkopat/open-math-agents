import OMAStatements.S_oeis_a016742
import Mathlib

/-! The conjecture recorded at OEIS A016742 is an equivalence: for `n ≥ 2`, a regular Hadamard
matrix of order `n` exists if and only if `n` is an even square `(2m)^2`.

The forward direction is classical: if `H` is a regular Hadamard matrix with common row and
column sum `s`, summing all entries of `H Hᵀ = n I` gives `n s^2 = n^2`, so `n = s^2`; the
orthogonality of two distinct rows of `±1` entries makes `n` even, hence `s` even and
`n = (2m)^2`. It is `H1`.

The backward direction (a regular Hadamard matrix exists in every even-square order) is the
open part; it contains the Hadamard conjecture for these orders. It is `H2`. -/

namespace OMA.R_oeis_a016742_R1

/-- The classical direction: the order of a regular Hadamard matrix is an even square. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 ≤ n → (∃ H : Matrix (Fin n) (Fin n) ℤ, OMA.S_oeis_a016742.IsRegularHadamard H) →
    ∃ m : ℕ, n = (2 * m) ^ 2

/-- The open direction: every even-square order carries a regular Hadamard matrix. -/
def H2 : Prop :=
  ∀ n : ℕ, 2 ≤ n → (∃ m : ℕ, n = (2 * m) ^ 2) →
    ∃ H : Matrix (Fin n) (Fin n) ℤ, OMA.S_oeis_a016742.IsRegularHadamard H

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a016742.main := by
  intro h1 h2 n hn
  exact ⟨h1 n hn, h2 n hn⟩

end OMA.R_oeis_a016742_R1
