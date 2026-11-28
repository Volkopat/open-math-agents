import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod

/-! Source: https://mathoverflow.net/questions/498823 -/

namespace OMA.S_mo_498823

/--
The two copies of the edge with left endpoint `v` and label `j` both have right
endpoint `dst v j`. For each left vertex, the equivalence indexes its labeled
edge copies by the perfect matching that uses them.
-/
theorem main :
    ∀ (n m : ℕ) (dst : Fin n → Fin m → Fin n),
      (∀ r : Fin n,
        (Finset.univ.filter fun e : Fin n × Fin m => dst e.1 e.2 = r).card = m) →
      ∃ matchEdge : (v : Fin n) → Fin (2 * m) ≃ Fin m × Bool,
        (∀ c, Function.Bijective fun v => dst v (matchEdge v c).1) ∧
        (∀ v w, m ≤
          (Finset.univ.filter fun c => (matchEdge v c).1 ≤ (matchEdge w c).1).card) := by
  sorry

end OMA.S_mo_498823
