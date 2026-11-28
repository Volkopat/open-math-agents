import Mathlib

/-!
# Real roots of the flow polynomial

Source: https://www.openproblemgarden.org/op/real_roots_of_the_flow_polynomial
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Welsh): all real roots of nonzero flow polynomials are at most `4`.

Conventions:
* Graphs are finite multigraphs, loops allowed: a finite vertex type `V`, a finite edge type `E`
  and endpoints `src, tgt : E → V` (an arbitrary reference orientation; the count below does not
  depend on it).
* For `k ≥ 1`, a nowhere-zero `ℤ_k`-flow is `f : E → ZMod k` with `f e ≠ 0` for all `e` and
  inflow equal to outflow at every vertex. The flow polynomial `F_G` is the polynomial with
  `F_G(k) =` the number of nowhere-zero `ℤ_k`-flows for all `k ≥ 1` (Tutte); it is unique, since
  a polynomial is determined by its values at infinitely many points. `main` quantifies over
  every polynomial with these values, so it does not depend on the existence proof.
-/

namespace OMA.S_opg_real_roots_of_the_flow_polynomial

open Classical

/-- The number of nowhere-zero `ℤ_k`-flows of the multigraph `(src, tgt) : E → V × V`. -/
noncomputable def nzFlowCount {V E : Type} [Fintype V] [Fintype E] (src tgt : E → V) (k : ℕ) :
    ℕ :=
  Nat.card {f : E → ZMod k // (∀ e, f e ≠ 0) ∧
    ∀ v : V, (∑ e ∈ Finset.univ.filter (fun e => tgt e = v), f e) =
      ∑ e ∈ Finset.univ.filter (fun e => src e = v), f e}

/-- Every real root of a nonzero flow polynomial is at most `4`. -/
theorem main : ∀ (V E : Type) [Fintype V] [Fintype E] (src tgt : E → V) (F : Polynomial ℝ),
    (∀ k : ℕ, 1 ≤ k → F.eval (k : ℝ) = nzFlowCount src tgt k) → F ≠ 0 →
    ∀ x : ℝ, F.IsRoot x → x ≤ 4 := by
  sorry

end OMA.S_opg_real_roots_of_the_flow_polynomial
