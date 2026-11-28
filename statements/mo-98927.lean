import Mathlib

/-!
# Index of a cyclic subgroup in its normal closure

Source: https://mathoverflow.net/questions/98927
Credit: @koolkao

Question (Wei Zhou, MathOverflow 98927, 2012; CC BY-SA 3.0). Let `G` be a finite group,
`x, y ∈ G`. Let `m = |⟨x⟩^G : ⟨x⟩|`, `n = |⟨y⟩^G : ⟨y⟩|`. In general, we can not get that
`(*) mn = |⟨xy⟩^G : ⟨xy⟩|`. So we need additional condition to make `(*)` hold. If we require that
`⟨x⟩^G ∩ ⟨y⟩^G = 1`, does `(*)` hold? If not, which conditions can make it hold? We also interested
with the case that `G` is a infinite group. Any reference about the normal closure of the product
of two element will be welcomed.

`main` states that the answer to the yes/no question is yes: for every finite group `G` and all
`x, y ∈ G` with `⟨x⟩^G ∩ ⟨y⟩^G = 1`, `(*)` holds. A disproof is a counterexample.

Translation choices:
* `⟨x⟩` is `Subgroup.zpowers x` and `⟨x⟩^G` is its normal closure, the smallest normal subgroup
  containing `x`, `Subgroup.normalClosure {x}` (the same subgroup as the normal closure of
  `⟨x⟩`);
* `|⟨x⟩^G : ⟨x⟩|` is the index of `⟨x⟩` in `⟨x⟩^G`, `(zpowers x).relIndex (normalClosure {x})`
  (here `⟨x⟩ ≤ ⟨x⟩^G`, so this is the usual index of a subgroup in an overgroup; for finite `G` it
  is a positive integer);
* `⟨x⟩^G ∩ ⟨y⟩^G = 1` is `normalClosure {x} ⊓ normalClosure {y} = ⊥`;
* `G` is finite (`Finite G`) and lives in `Type`; the statement is invariant under isomorphism;
* not formalized: the open-ended follow-ups ("which conditions can make it hold?", the infinite
  case, and the request for references).
-/

namespace OMA.S_mo_98927

open Subgroup

/-- If `⟨x⟩^G ∩ ⟨y⟩^G = 1` in a finite group `G`, then
`|⟨x⟩^G : ⟨x⟩| · |⟨y⟩^G : ⟨y⟩| = |⟨xy⟩^G : ⟨xy⟩|`. -/
theorem main :
    ∀ (G : Type) [Group G] [Finite G] (x y : G),
      normalClosure {x} ⊓ normalClosure {y} = ⊥ →
        (zpowers x).relIndex (normalClosure {x}) * (zpowers y).relIndex (normalClosure {y}) =
          (zpowers (x * y)).relIndex (normalClosure {x * y}) := by
  sorry

end OMA.S_mo_98927
