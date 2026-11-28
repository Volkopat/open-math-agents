import Mathlib

/-!
# How many values a polynomial map misses?

Source: https://mathoverflow.net/questions/120175/how-many-values-a-polynomial-map-misses
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question: let `F` be an infinite field and `f ∈ F[x]`. If `f` misses one value (is not
surjective as a map `F → F`), does it miss infinitely many values?

## Encoding

* `F` is any infinite field (`Infinite F`); `f` acts by `Polynomial.eval`.
* The question is stated with the answer yes (as the asker expects).
-/

namespace OMA.S_mo_120175

theorem main :
    ∀ (F : Type) [Field F] [Infinite F] (f : Polynomial F),
      ¬ Function.Surjective (fun x => f.eval x) →
        (Set.range (fun x => f.eval x))ᶜ.Infinite := by
  sorry

end OMA.S_mo_120175
