import Mathlib

/-!
# Does the compact-open topology retain topological groups?

Source: https://mathoverflow.net/questions/361305
Credit: @ivillar

Let $X$ be a topological space and $Y$ a topological group. Then $C(X,Y)$ is a group, and can
also be endowed with the compact-open topology.

Is $C(X,Y)$ in the compact-open topology necessarily a topological group? If not, is there
some property of $X$ which will guarantee it?

Formalization notes:
* `C(X, Y)` is Mathlib's type of continuous maps with its compact-open topology
  (`ContinuousMap.compactOpen`) and the pointwise group structure.
* No hypothesis is placed on `X`, and `Y` is an arbitrary (not necessarily commutative or
  Hausdorff) topological group.
* `main` is the affirmative answer: multiplication and inversion on `C(X, Y)` are continuous.
-/

namespace OMA.S_mo_361305

theorem main : ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [Group Y]
    [IsTopologicalGroup Y], IsTopologicalGroup C(X, Y) := by
  sorry

end OMA.S_mo_361305
