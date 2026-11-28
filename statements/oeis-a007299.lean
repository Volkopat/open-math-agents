import Mathlib

/-!
# A007299: Number of Hadamard matrices of order 4n.

Source: https://oeis.org/A007299
Credit: @divmxnd0x

Conjecture (the Hadamard conjecture, J. Hadamard 1893, stated in A007299): `a(n) > 0` for all
`n ≥ 0`.

Formalization notes:
* A Hadamard matrix of order `m` is an `m × m` matrix `H` with entries `±1` and `H Hᵀ = m I`;
  `a n` counts the Hadamard matrices of order `4 n` (all of them, not up to equivalence, as in the
  data `1, 768, 4954521600, ...` of A007299). The set is finite (its elements are `±1` matrices), so
  `Nat.card` is the number of such matrices, and `a 0 = 1` (the empty matrix).
* The conjecture `a(n) > 0` therefore says that a Hadamard matrix of order `4 n` exists for every
  `n ≥ 0`. The same conjecture is stated with a determinant definition in
  `FormalConjectures/Wikipedia/Hadamard.lean`; this file follows the OEIS entry.
-/

namespace OMA.S_oeis_a007299

/-- `H` is a Hadamard matrix of order `m`: entries `±1` and `H * Hᵀ = m • 1`. -/
def IsHadamardMatrix {m : ℕ} (H : Matrix (Fin m) (Fin m) ℤ) : Prop :=
  (∀ i j, H i j = 1 ∨ H i j = -1) ∧ H * H.transpose = (m : ℤ) • (1 : Matrix (Fin m) (Fin m) ℤ)

/-- A007299(n): the number of Hadamard matrices of order `4 n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {H : Matrix (Fin (4 * n)) (Fin (4 * n)) ℤ // IsHadamardMatrix H}

/-- The Hadamard conjecture as stated in A007299: `a(n) > 0` for all `n ≥ 0`. -/
theorem main : ∀ n : ℕ, 0 < a n := by
  sorry

end OMA.S_oeis_a007299
