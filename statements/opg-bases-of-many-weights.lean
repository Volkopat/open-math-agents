import Mathlib

/-!
# Bases of many weights

Source: https://www.openproblemgarden.org/op/bases_of_many_weights
Credit: @shc261392

Let `G` be an additive abelian group and for `S ⊆ G` let `stab(S) = {g ∈ G : g + S = S}`.

Conjecture (Schrijver and Seymour; posted by DeVos): let `M` be a matroid on `E`, let
`w : E → G`, put `S = {∑_{b ∈ B} w(b) : B is a base}` and `H = stab(S)`. Then
`|S| ≥ |H| (1 - rk(M) + ∑_{Q ∈ G/H} rk(w⁻¹(Q)))`.

Reading used here:
* `M` is a matroid on a finite type `α` (its ground set `M.E ⊆ α`), `w : α → G`; `rk(M)` is
  `M.eRank` and `rk(X)` is `M.eRk X`, both finite here and read in `ℤ`.
* `stab(S)` is the stabilizer of `S` for the action of `G` on `Set G` by translation, an
  additive subgroup `H`; the cosets `Q ∈ G ⧸ H` with `w⁻¹(Q)` nonempty are finitely many, so the
  sum is a `finsum`.
* `S` is finite and nonempty (a matroid has a base), so `H` is finite; sizes are `Set.ncard`.
-/

namespace OMA.S_opg_bases_of_many_weights

open Pointwise

/-- The set of weights of bases. -/
def baseWeights {α G : Type} [AddCommGroup G] (M : Matroid α) (w : α → G) : Set G :=
  {g | ∃ B, M.IsBase B ∧ g = ∑ᶠ b ∈ B, w b}

theorem main :
    ∀ (α G : Type) [Finite α] [AddCommGroup G] (M : Matroid α) (w : α → G),
      let S := baseWeights M w
      let H := AddAction.stabilizer G S
      (S.ncard : ℤ) ≥ ((H : Set G).ncard : ℤ) * (1 - (M.eRank.toNat : ℤ) +
        ∑ᶠ Q : G ⧸ H, ((M.eRk (w ⁻¹' {g | (g : G ⧸ H) = Q})).toNat : ℤ)) := by
  sorry

end OMA.S_opg_bases_of_many_weights
