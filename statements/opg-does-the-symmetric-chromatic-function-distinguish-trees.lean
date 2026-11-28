import Mathlib

/-!
# Does the chromatic symmetric function distinguish between trees?

Source: https://www.openproblemgarden.org/op/does_the_symmetric_chromatic_function_distinguish_trees
Credit: @ishaanzee

**Problem** (R. P. Stanley). Do there exist non-isomorphic trees which have the same chromatic
symmetric function?

Stanley's chromatic symmetric function of a graph `G = (V, E)` is `X_G = ∑_f ∏_{v ∈ V} x_{f(v)}`,
the sum over all proper colorings `f : V → ℕ`. Stanley conjectured that the answer is no (the
chromatic symmetric function distinguishes trees); we state this.

Formalization:
* Trees are finite (`SimpleGraph.IsTree` on a finite vertex type).
* The coefficient of the monomial `∏ᵢ xᵢ^(dᵢ)` in `X_G`, for `d : ℕ →₀ ℕ`, is the number of proper
  colorings `f : V → ℕ` in which exactly `dᵢ` vertices get color `i`, for every `i`. Two graphs
  have the same chromatic symmetric function iff all these coefficients agree.
-/

namespace OMA.S_opg_does_the_symmetric_chromatic_function_distinguish_trees

/-- The coefficient of `∏ᵢ xᵢ^(d i)` in the chromatic symmetric function of `G`: the number of
proper colorings `f : V → ℕ` with exactly `d i` vertices of color `i` for every `i`. -/
noncomputable def chromSymCoeff {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ →₀ ℕ) : ℕ :=
  {f : V → ℕ | (∀ u v, G.Adj u v → f u ≠ f v) ∧
    ∀ i : ℕ, (Finset.univ.filter fun v => f v = i).card = d i}.ncard

/-- **Stanley's tree conjecture**: finite trees with the same chromatic symmetric function are
isomorphic (so no two non-isomorphic trees share it). -/
theorem main : ∀ (V W : Type) [Fintype V] [Fintype W] (T : SimpleGraph V) (T' : SimpleGraph W),
    T.IsTree → T'.IsTree → (∀ d : ℕ →₀ ℕ, chromSymCoeff T d = chromSymCoeff T' d) →
      Nonempty (T ≃g T') := by
  sorry

end OMA.S_opg_does_the_symmetric_chromatic_function_distinguish_trees
