import Mathlib

/-!
# Oberwolfach problem

Source: https://en.wikipedia.org/wiki/Oberwolfach_problem
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Source question: for which 2-regular `n`-vertex graphs `G` can the complete graph `K_n` be
decomposed into edge-disjoint copies of `G`? A solution requires `n` odd. The source records that
`OP(4,5)` and `OP(3,3,5)` (and, in the even-`n` variant with a perfect matching removed, `OP(3^2)`
and `OP(3^4)`) have no solution, and that it is widely believed that all other instances have a
solution. The statement below is this conjectured answer for the problem as posed (complete
graph `K_n`, so `n` odd): every 2-regular graph on an odd number `n` of vertices, other than
`C_4 + C_5` and `C_3 + C_3 + C_5`, decomposes `K_n`.

Conventions:
* `G` is a simple graph on `Fin n`; 2-regular means every vertex has degree exactly 2, so `G` is
  a disjoint union of cycles, one per connected component, and the cycle lengths are the
  component sizes. The two exceptions are identified by the multiset of component sizes
  (`{4, 5}` and `{3, 3, 5}`), which determines a 2-regular graph up to isomorphism;
* a copy of `G` in `K_n` is the image of `G` under a bijection `σ` of `Fin n` (a copy of a
  spanning 2-regular graph uses all `n` vertices); a decomposition is a finite family of copies
  such that every pair of distinct vertices is an edge of exactly one copy (so the copies are
  edge-disjoint and cover all edges of `K_n`);
* the even-`n` variant (`K_n` minus a perfect matching) is an extension mentioned by the source
  and is not stated here.
-/

namespace OMA.S_wp_oberwolfach_problem

open Classical in
/-- The multiset of sizes of the connected components of a graph on `Fin n` (for a 2-regular
graph: the multiset of its cycle lengths). -/
noncomputable def componentSizes {n : ℕ} (G : SimpleGraph (Fin n)) : Multiset ℕ :=
  (Finset.univ : Finset G.ConnectedComponent).val.map fun c => c.supp.ncard

theorem main : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    Odd n → (∀ v, G.degree v = 2) →
    componentSizes G ≠ {4, 5} → componentSizes G ≠ {3, 3, 5} →
      ∃ (m : ℕ) (σ : Fin m → Equiv.Perm (Fin n)),
        ∀ u v : Fin n, u ≠ v → ∃! i : Fin m, G.Adj ((σ i).symm u) ((σ i).symm v) := by
  sorry

end OMA.S_wp_oberwolfach_problem
