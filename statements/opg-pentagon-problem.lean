import Mathlib

/-!
# Pentagon problem

Source: https://www.openproblemgarden.org/op/pentagon_problem
Credit: @ishaanzee

**Question** (J. Nešetřil). Let `G` be a 3-regular graph that contains no cycle of length shorter
than `g`. Is it true that for large enough `g` there is a homomorphism `G → C₅`?

(By Brooks' theorem every triangle-free cubic graph is 3-colorable, i.e. maps to `C₃`.) We state the
affirmative answer.

Formalization: graphs are finite simple graphs; 3-regular is `IsRegularOfDegree 3`; "no cycle of
length shorter than `g`" is `g ≤ egirth` (`egirth` is the length of a shortest cycle, `⊤` if there
is none); `C₅` is Mathlib's `cycleGraph 5`, and a homomorphism is a `SimpleGraph.Hom`.
-/

namespace OMA.S_opg_pentagon_problem

/-- **Nešetřil's pentagon problem**, affirmative form: there is `g` such that every cubic graph of
girth at least `g` admits a homomorphism to the 5-cycle. -/
theorem main : ∃ g : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsRegularOfDegree 3 → (g : ℕ∞) ≤ G.egirth → Nonempty (G →g SimpleGraph.cycleGraph 5) := by
  sorry

end OMA.S_opg_pentagon_problem
