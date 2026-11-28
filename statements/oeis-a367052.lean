import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Logic.Relation

namespace OMA.S_oeis_a367052

/-- The set of `n × n` `{0, 1}`-matrices over `ℚ` whose characteristic polynomial is
`X ^ n - X ^ (n - 1)` (OEIS A367052). -/
def isTargetMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Prop :=
  (∀ i j, A i j = 0 ∨ A i j = 1) ∧
  A.charpoly = Polynomial.X ^ n - Polynomial.X ^ (n - 1)

/-- A labeled directed acyclic graph (DAG) on `Fin n` (counted by OEIS A003024):
a binary relation `R` whose transitive closure is irreflexive. -/
def isDAG {n : ℕ} (R : Fin n → Fin n → Prop) : Prop :=
  ∀ u, ¬ Relation.TransGen R u u

/-- OEIS A367052 conjecture: for every `n ≥ 1`, the number of `n × n` `{0, 1}`-matrices with
characteristic polynomial `X ^ n - X ^ (n - 1)` equals `n * A003024(n)`, where `A003024(n)` is
the number of labeled acyclic digraphs on `n` vertices. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      Nat.card {A : Matrix (Fin n) (Fin n) ℚ // isTargetMatrix A} =
        n * Nat.card {R : Fin n → Fin n → Prop // isDAG R} := by
  sorry

end OMA.S_oeis_a367052
