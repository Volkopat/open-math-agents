import Mathlib

/-!
# Erdős Problem 129

Source: https://www.erdosproblems.com/129
Credit: @mattdorman

The source states (conjectured by Erdős and Gyárfás): let `R(n; k, r)` be the smallest `N` such
that if the edges of `K_N` are `r`-coloured then there is a set of `n` vertices which does not
contain a copy of `K_k` in at least one of the `r` colours. Prove that there is a constant
`C = C(r) > 1` such that `R(n; 3, r) < C^{√n}`.

Reading used here: `r ≥ 2` colours; an `r`-colouring of the edges of `K_N` is a map
`Sym2 (Fin N) → Fin r` (its values on the diagonal are irrelevant). A set `S` contains no copy of
`K_3` in colour `i` when no three distinct vertices of `S` have all three of their edges
coloured `i`. Since `R(n; 3, r)` is the least `N` with the property, `R(n; 3, r) < X` holds
exactly when some `N < X` has it, and the statement is written in that form. The source records
that this statement, as written, is easily disproved (a random colouring gives
`R(n; 3, 2) ≥ Cⁿ`); it is stated faithfully, so a disproof settles it.
-/

namespace OMA.S_erdos_129

/-- In the colouring `c`, the set `S` contains no triangle all of whose edges have colour `i`. -/
def NoMonoTriangle {N r : ℕ} (c : Sym2 (Fin N) → Fin r) (S : Finset (Fin N)) (i : Fin r) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y → y ≠ z → x ≠ z →
    ¬ (c s(x, y) = i ∧ c s(y, z) = i ∧ c s(x, z) = i)

theorem main :
    ∀ r : ℕ, 2 ≤ r → ∃ C : ℝ, 1 < C ∧ ∀ n : ℕ, ∃ N : ℕ, (N : ℝ) < C ^ Real.sqrt n ∧
      ∀ c : Sym2 (Fin N) → Fin r, ∃ S : Finset (Fin N), S.card = n ∧
        ∃ i : Fin r, NoMonoTriangle c S i := by
  sorry

end OMA.S_erdos_129
