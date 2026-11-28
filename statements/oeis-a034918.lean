import Mathlib

/-!
# A034918: Maximal determinant of persymmetric {-1, 0, +1} matrices

Source: https://oeis.org/A034918
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the maximal determinant of an `n × n` persymmetric matrix with entries in
`{-1, 0, +1}`. Conjecture (Jeffrey Shallit, OEIS, 2026): for `n ≠ 2`, the maximal determinant is
achieved by a matrix with entries `{-1, +1}` only.

## Encoding

* Matrices are `Matrix (Fin n) (Fin n) ℤ`. Persymmetric means symmetric about the
  anti-diagonal: `M i j = M (n-1-j) (n-1-i)`, written with `Fin.rev`.
* `main`: for every `n ≠ 2` (offset `1`, so `n ≥ 1`) some persymmetric `±1` matrix has
  determinant at least that of every persymmetric `{-1, 0, 1}` matrix.
-/

namespace OMA.S_oeis_a034918

/-- `M` is persymmetric. -/
def IsPersymmetric {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∀ i j, M i j = M j.rev i.rev

theorem main :
    ∀ n : ℕ, 1 ≤ n → n ≠ 2 →
      ∃ M : Matrix (Fin n) (Fin n) ℤ, IsPersymmetric M ∧ (∀ i j, M i j = 1 ∨ M i j = -1) ∧
        ∀ N : Matrix (Fin n) (Fin n) ℤ, IsPersymmetric N → (∀ i j, N i j ∈ ({-1, 0, 1} : Set ℤ)) →
          N.det ≤ M.det := by
  sorry

end OMA.S_oeis_a034918
