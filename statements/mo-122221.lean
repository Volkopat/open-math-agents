import Mathlib

/-!
# Classifying spaces of monoids embedded in their group completions

Can the canonical map from a discrete monoid to its group completion be
injective while inducing a map of classifying spaces with no homotopy inverse?

[MathOverflow question](https://mathoverflow.net/questions/122221)
-/

open CategoryTheory

namespace OMA.S_mo_122221

noncomputable def classifyingSpace (M : Type) [Monoid M] : TopCat :=
  SSet.toTop.obj (nerve (SingleObj M))

noncomputable def classifyingMap {M G : Type} [Monoid M] [Group G] (ι : M →* G) :
    ContinuousMap (classifyingSpace M) (classifyingSpace G) :=
  (SSet.toTop.map (nerveMap (SingleObj.mapHom M G ι))).hom

def IsGroupCompletion {M G : Type} [Monoid M] [Group G] (ι : M →* G) : Prop :=
  ∀ (H : Type) [Group H] (f : M →* H), ∃! g : G →* H, g.comp ι = f

theorem main :
    ∃ (M G : Type) (monoid : Monoid M) (group : Group G),
      letI : Monoid M := monoid
      letI : Group G := group
      ∃ ι : M →* G, Function.Injective ι ∧ IsGroupCompletion ι ∧
        ¬ ∃ h : ContinuousMap (classifyingSpace G) (classifyingSpace M),
          ((h.comp (classifyingMap ι)).Homotopic
            (ContinuousMap.id (classifyingSpace M))) ∧
          (((classifyingMap ι).comp h).Homotopic
            (ContinuousMap.id (classifyingSpace G))) := by
  sorry

end OMA.S_mo_122221
