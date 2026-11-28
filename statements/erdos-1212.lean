import Mathlib

/-!
# Erdős Problem 1212

Source: https://www.erdosproblems.com/1212
Credit: @mattdorman

The source asks: let `G` be the graph with vertex set the pairs `(x, y) ∈ ℕ²` with
`gcd(x, y) = 1`, two vertices joined if they differ in only one coordinate, and there by `±1`.
Is there a path going to infinity on `G`, say `P`, such that for all `(x, y) ∈ P` both
`min(x, y) > 1` and at least one of `x` or `y` is composite?

Reading used here: a path going to infinity is an infinite sequence of pairwise distinct vertices,
consecutive ones adjacent in `G` (every vertex of `G` has at most four neighbours, so an infinite
path of distinct vertices leaves every finite set). Since `min(x, y) > 1`, a coordinate is
composite exactly when it is not prime. The statement below is the affirmative answer.
-/

namespace OMA.S_erdos_1212

/-- Adjacency in `G`: equal in one coordinate, differing by one in the other. -/
def LatticeAdj (u v : ℕ × ℕ) : Prop :=
  (u.1 = v.1 ∧ (u.2 + 1 = v.2 ∨ v.2 + 1 = u.2)) ∨ (u.2 = v.2 ∧ (u.1 + 1 = v.1 ∨ v.1 + 1 = u.1))

theorem main :
    ∃ P : ℕ → ℕ × ℕ, Function.Injective P ∧
      (∀ n, Nat.gcd (P n).1 (P n).2 = 1) ∧
      (∀ n, LatticeAdj (P n) (P (n + 1))) ∧
      (∀ n, 1 < min (P n).1 (P n).2 ∧ (¬ (P n).1.Prime ∨ ¬ (P n).2.Prime)) := by
  sorry

end OMA.S_erdos_1212
