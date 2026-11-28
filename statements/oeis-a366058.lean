import Mathlib

/-!
# A366058: self-avoiding walks on the cubic lattice that never step closer to the origin

Source: https://oeis.org/A366058 (conjectured formula in the OEIS entry)

An `n`-step walk on the cubic lattice `Z^3` starting at the origin is encoded by its
sequence of steps `s : Fin n → Fin 6`, each step being one of the six unit vectors `dir i`.
The position after `k` steps is `pos s k`, the sum of the first `k` steps. The walk is
counted when it is self-avoiding (the positions after `0, 1, ..., n` steps are pairwise
distinct) and no step goes to a lattice point closer to the origin than the current point,
i.e. the squared Euclidean distance to the origin never decreases along the walk.
`a(n)` (offset 0) is the number of such walks.

Conjecture: `a(n) = 6*(4*3^(n-1) - 4*2^(n-1) + 1)` for `n > 0`.
-/

namespace OMA.S_oeis_a366058

/-- The six unit steps of the cubic lattice. -/
def dir : Fin 6 → ℤ × ℤ × ℤ :=
  ![(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]

/-- The position after the first `k` steps of the walk with steps `s`. -/
def pos {n : ℕ} (s : Fin n → Fin 6) (k : ℕ) : ℤ × ℤ × ℤ :=
  (((List.ofFn s).take k).map dir).sum

/-- Squared Euclidean distance to the origin. -/
def sqDist (p : ℤ × ℤ × ℤ) : ℤ := p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2

/-- Self-avoiding, and no step moves closer to the origin. -/
def IsWalk {n : ℕ} (s : Fin n → Fin 6) : Prop :=
  (∀ i j : ℕ, i ≤ n → j ≤ n → pos s i = pos s j → i = j) ∧
    ∀ k : ℕ, k < n → sqDist (pos s k) ≤ sqDist (pos s (k + 1))

/-- The number of such `n`-step walks. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {s : Fin n → Fin 6 // IsWalk s}

theorem main : ∀ n : ℕ, 1 ≤ n → (a n : ℤ) = 6 * (4 * 3 ^ (n - 1) - 4 * 2 ^ (n - 1) + 1) := by
  sorry

end OMA.S_oeis_a366058
