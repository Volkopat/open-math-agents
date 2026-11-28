import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Int.Basic
import Mathlib.Logic.Relation

/-!
# Equal first and strict second outdegrees on the integer line

Source: Archr, Math.StackExchange 4941096, July 3, 2024, CC BY-SA 4.0.
https://math.stackexchange.com/questions/4941096/is-there-a-digraph-with-these-3-properties

The question asks whether an example exists and explicitly suggests
impossibility. We state that suggested impossibility; a disproof constructs
an example. A uniform bound on arc length implies finite out-neighborhoods.
A finset of neighbors also encodes the exclusion of multiple arcs.
-/
namespace OMA.S_mse_4941096

def second (out : ℤ → Finset ℤ) (v : ℤ) : Finset ℤ :=
  (out v).biUnion out \ out v

def exampleGraph (out : ℤ → Finset ℤ) : Prop :=
  (∀ v, v ∉ out v) ∧ (∀ v w, w ∈ out v → v ∉ out w) ∧
  (∀ v w, Relation.ReflTransGen (fun i j => j ∈ out i) v w) ∧
  (∃ W : ℕ, ∀ v w, w ∈ out v → v-(W : ℤ) ≤ w ∧ w ≤ v+(W : ℤ)) ∧
  (∀ v, (out v).card = (second out v).card)

theorem main : ¬ ∃ out : ℤ → Finset ℤ, exampleGraph out := by
  sorry

end OMA.S_mse_4941096
