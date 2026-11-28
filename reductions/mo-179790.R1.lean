import OMAStatements.S_mo_179790
import Mathlib

/-!
# Reduction of MathOverflow 179790 (is the fixed point property preserved by products?)

* `H1` (classical, an Abian–Brown type theorem): if every chain of `P` and every chain of `Q`
  (the empty chain included, so both have a least element) has a least upper bound, then every
  order-preserving self-map of `P × Q` has a fixed point. The product is again chain-complete
  (take coordinatewise suprema), and Zorn's lemma applied to `{x | x ≤ f x}` gives a maximal
  element `m`; since `f m` is again in that set and `m ≤ f m`, maximality gives `f m = m`.
  This covers all complete lattices and all finite posets with a least element, whatever the
  fixed point property of the factors.
* `H2` (the open core): the product question when `P` or `Q` is not chain-complete.

This is a classical partial case, not progress on the open question.
-/

namespace OMA.R_mo_179790_R1

/-- Products of chain-complete posets (every chain, empty or not, has a supremum) have the
fixed point property. -/
def H1 : Prop :=
  ∀ (P Q : Type) [PartialOrder P] [PartialOrder Q],
    (∀ c : Set P, IsChain (· ≤ ·) c → ∃ s, IsLUB c s) →
    (∀ c : Set Q, IsChain (· ≤ ·) c → ∃ s, IsLUB c s) →
    OMA.S_mo_179790.FPP (P × Q)

/-- The open core: the product question when one factor is not chain-complete. -/
def H2 : Prop :=
  ∀ (P Q : Type) [PartialOrder P] [PartialOrder Q],
    OMA.S_mo_179790.FPP P → OMA.S_mo_179790.FPP Q →
    ¬ ((∀ c : Set P, IsChain (· ≤ ·) c → ∃ s, IsLUB c s) ∧
      (∀ c : Set Q, IsChain (· ≤ ·) c → ∃ s, IsLUB c s)) →
    OMA.S_mo_179790.FPP (P × Q)

theorem main : H1 → H2 → type_of% @OMA.S_mo_179790.main := by
  intro h1 h2 P Q _ _ hP hQ
  by_cases hc : (∀ c : Set P, IsChain (· ≤ ·) c → ∃ s, IsLUB c s) ∧
      (∀ c : Set Q, IsChain (· ≤ ·) c → ∃ s, IsLUB c s)
  · exact h1 P Q hc.1 hc.2
  · exact h2 P Q hP hQ hc

end OMA.R_mo_179790_R1
