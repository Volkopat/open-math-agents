import FormalConjectures.Other.HyperbolicGroupsResiduallyFinite
import Mathlib.GroupTheory.FreeGroup.Basic

/-!
The two steps separate free-product normal forms from small cancellation.
For the first, take the free product of two copies of the torsion-free
non-residually-finite group from the OpenAI construction (PR 3425). The
copies of one undetected nonidentity element freely generate a rank-two
subgroup on which every homomorphism to a finite group is trivial.
For the second, apply Olshanskii's quotient theorem to this free subgroup,
as in Minasyan, Osin and Witzel, Quasi-isometric diversity of marked groups,
Theorem 4.6. Torsion-freeness rules out nontrivial finite subgroups, and a
free subgroup of rank two is not virtually cyclic.

MechaNuggan's notes 54270 and 54460 proposed a quotient surjective on the
finite residual. Doubling the source supplies a specific free subgroup in
the residual to which the quotient theorem applies.
-/

namespace OMA.R_HyperbolicGroupsResiduallyFinite_hyperbolic_exists_finiteIndex_ne_top_R3

def H1 : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Group.IsHyperbolic G),
    (∀ (g : G) (n : ℕ), 0 < n → g ^ n = 1 → g = 1) ∧
    ∃ i : FreeGroup (Fin 2) →* G, Function.Injective i ∧
      ∀ (F : Type) [Group F] [Finite F] (u : G →* F) (j : Fin 2),
        u (i (FreeGroup.of j)) = 1

def H2 : Prop :=
  ∀ (G : Type) [Group G] [Group.IsHyperbolic G],
    (∀ (g : G) (n : ℕ), 0 < n → g ^ n = 1 → g = 1) →
    ∀ i : FreeGroup (Fin 2) →* G, Function.Injective i →
      ∃ (Q : Type) (_ : Group Q) (_ : Group.IsHyperbolic Q) (_ : Nontrivial Q)
        (f : G →* Q), Function.Surjective (f.comp i)

theorem main : H1 → H2 → type_of% @HyperbolicGroupsResiduallyFinite.hyperbolic_exists_finiteIndex_ne_top := by
  classical
  intro h1 h2 hAll
  obtain ⟨G, _, _, ht, i, hi, hk⟩ := h1
  obtain ⟨Q, _, _, _, f, hf⟩ := h2 G ht i hi
  obtain ⟨S, hproper, hindex⟩ := hAll Q
  let : S.FiniteIndex := hindex
  apply hproper
  apply top_unique
  intro q _
  apply S.normalCore_le
  rw [Subgroup.normalCore_eq_ker]
  apply MonoidHom.mem_ker.mpr
  obtain ⟨x, rfl⟩ := hf q
  let u := (MulAction.toPermHom Q (Q ⧸ S)).comp f
  have trivial : u.comp i = 1 := by
    apply FreeGroup.lift.symm.injective
    funext j
    exact hk (Equiv.Perm (Q ⧸ S)) u j
  exact DFunLike.congr_fun trivial x

end OMA.R_HyperbolicGroupsResiduallyFinite_hyperbolic_exists_finiteIndex_ne_top_R3
