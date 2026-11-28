import Mathlib

/-!
# MathOverflow 310301: a Legendre-symbol determinant for primes `p ≡ 1 (mod 4)`

Source: https://mathoverflow.net/questions/310301 (Zhi-Wei Sun, CC BY-SA 4.0).

For an odd prime `p` let `A_p = [a_{ij}]_{1 ≤ i, j ≤ (p-1)/2}` with `a_{1j} = (j/p)` and
`a_{ij} = ((i² + j²)/p)` for `i > 1`, where `(·/p)` is the Legendre symbol. Question: is
`-det A_p` always an odd square for each prime `p ≡ 1 (mod 4)`? The asker conjectures yes
(checked for `p < 2000`; `√(-det A_p) = 1, 3, 21, 83, …` for `p = 5, 13, 17, 29, …`), and `main`
states that conjecture.

Conventions: rows and columns are indexed by `Fin ((p-1)/2)`, the entry in position `(i, j)`
being `a_{i+1, j+1}`. For a prime `p` the Jacobi symbol `jacobiSym a p` is the Legendre symbol.
-/

namespace OMA.S_mo_310301

/-- The matrix `A_p`, indexed from `0`. -/
def A (p : ℕ) : Matrix (Fin ((p - 1) / 2)) (Fin ((p - 1) / 2)) ℤ :=
  fun i j => if (i : ℕ) = 0 then jacobiSym ((j : ℤ) + 1) p
    else jacobiSym (((i : ℤ) + 1) ^ 2 + ((j : ℤ) + 1) ^ 2) p

theorem main : ∀ p : ℕ, p.Prime → p % 4 = 1 → ∃ m : ℤ, Odd m ∧ -(A p).det = m ^ 2 := by
  sorry

end OMA.S_mo_310301
