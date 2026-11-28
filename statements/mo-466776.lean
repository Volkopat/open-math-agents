import Mathlib

/-!
# Hyponontiling Wang tiles

Source: https://mathoverflow.net/questions/466776 (domotorp)
Credit: Sudharsan Rajendiran

Call a finite collection of tiles *tiling* if the plane can be tiled using each tile at least
once. Is there a collection of at least `3` tiles that is not tiling, but such that removing any
one tile from it gives a tiling collection? The question leaves the notion of tile open on
purpose ("it can be Wang tiles ... with translations or rotations").

The accepted answer on the source page answers yes, with three Wang tiles when quarter-turn
rotations are allowed. We state the question in that model, in its affirmative form: there is
such a collection of Wang tiles with rotations.

Conventions:
- A Wang tile is a unit square with a colour (a natural number) on each side, given as
  `t : Fin 4 → ℕ` with sides `0` = top, `1` = right, `2` = bottom, `3` = left. Rotating it by
  `r` quarter turns gives side colours `k ↦ t (k + r)` (indices mod `4`).
- A tiling places a rotated copy of some tile of the collection on every cell `(i, j)` of `ℤ²`;
  colours must agree on every shared edge (the right side of `(i, j)` with the left side of
  `(i + 1, j)`, the top side of `(i, j)` with the bottom side of `(i, j + 1)`). The collection is
  tiling if some tiling uses every tile of it at least once.
- A collection of `n` tiles is `T : Fin n → Fin 4 → ℕ`; the collection with tile `k` removed is
  the index set `Finset.univ.erase k`.
-/

namespace OMA.S_mo_466776

/-- The colours of the four sides of a Wang tile `t` placed after `r` quarter turns:
side `0` = top, `1` = right, `2` = bottom, `3` = left. -/
def side (t : Fin 4 → ℕ) (r : Fin 4) (k : Fin 4) : ℕ := t (k + r)

/-- The collection `T` of `n` Wang tiles, restricted to the indices in `S`, tiles the plane:
there is a placement `g` of rotated copies of tiles from `S` on the cells of `ℤ²` with matching
colours on shared edges, using every tile of `S` at least once. -/
def Tiles {n : ℕ} (T : Fin n → Fin 4 → ℕ) (S : Finset (Fin n)) : Prop :=
  ∃ g : ℤ × ℤ → Fin n × Fin 4,
    (∀ c, (g c).1 ∈ S) ∧
    (∀ i j : ℤ, side (T (g (i, j)).1) (g (i, j)).2 1 = side (T (g (i + 1, j)).1) (g (i + 1, j)).2 3) ∧
    (∀ i j : ℤ, side (T (g (i, j)).1) (g (i, j)).2 0 = side (T (g (i, j + 1)).1) (g (i, j + 1)).2 2) ∧
    ∀ k ∈ S, ∃ c, (g c).1 = k

theorem main : ∃ (n : ℕ) (T : Fin n → Fin 4 → ℕ), 3 ≤ n ∧ ¬ Tiles T Finset.univ ∧
    ∀ k : Fin n, Tiles T (Finset.univ.erase k) := by
  sorry

end OMA.S_mo_466776
