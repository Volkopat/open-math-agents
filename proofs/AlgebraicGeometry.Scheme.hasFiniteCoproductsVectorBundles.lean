import FormalConjectures.Paper.HartshorneConjecture
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.SetTheory.Cardinal.Finite

/-! Coproduct cocones lift along the fully faithful forgetful functor. Binary sums
are trivialized on intersections of the covers of the factors. The initial bundle
is the free sheaf on the empty type. The previous proof is credited to @Minimisthupper. -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace SheafOfModules

universe u
variable (S : Scheme.{u})

private def forgetFullyFaithful : (Scheme.VectorBundles.toModule S).FullyFaithful where
  preimage f := ⟨f⟩
  map_preimage _ := rfl
  preimage_map _ := rfl

local instance : (Scheme.VectorBundles.toModule S).Full := (forgetFullyFaithful S).full
local instance : (Scheme.VectorBundles.toModule S).Faithful := (forgetFullyFaithful S).faithful

private lemma over_isLeftAdjoint (W : S.Opens) :
    (overFunctor S.ringCatSheaf W).IsLeftAdjoint :=
  inferInstanceAs (pushforward (𝟙 (S.ringCatSheaf.over W))).IsLeftAdjoint

private lemma free_empty_rank :
    IsVectorBundleWithRank (J := Opens.grothendieckTopology S)
      (free (R := S.ringCatSheaf) PEmpty.{u + 1}) 0 := by
  have := over_isLeftAdjoint S (⊤ : S.Opens)
  let D : (free (R := S.ringCatSheaf) PEmpty.{u + 1}).FiniteRankVectorBundleData :=
    { OpensIndex := PUnit.{u + 1}
      opens := fun _ => (⊤ : S.Opens)
      coversTop := by simp [Opens.coversTop_iff, IsOpenCover]
      BasisIndex := fun _ => PEmpty.{u + 1}
      locallyFree := fun _ => (mapFreeIso (overFunctor S.ringCatSheaf ⊤) _ (Iso.refl _)).symm
      finite := fun _ => inferInstance }
  exact { exists_vector_bundle_data := ⟨D, fun _ => Nat.card_of_isEmpty⟩ }

private def restrictTrivialization {M : S.Modules} (D : M.FiniteRankVectorBundleData)
    (i : D.OpensIndex) {W : S.Opens} (h : W ≤ D.opens i) :
    M.over W ≅ free (D.BasisIndex i) :=
  let f : W ⟶ D.opens i := homOfLE h
  ((overFunctorMap S.ringCatSheaf f).app M).symm ≪≫
    (overMap S.ringCatSheaf f).mapIso (D.locallyFree i) ≪≫
    (mapFreeIso (overMap S.ringCatSheaf f) _ (overMapUnitIso f).symm).symm

private lemma coprod_rank {M N : S.Modules} {m n : ℕ}
    (hM : IsVectorBundleWithRank (J := Opens.grothendieckTopology S) M m)
    (hN : IsVectorBundleWithRank (J := Opens.grothendieckTopology S) N n) :
    IsVectorBundleWithRank (J := Opens.grothendieckTopology S) (M ⨿ N) (m + n) := by
  obtain ⟨DM, hDM⟩ := hM.exists_vector_bundle_data
  obtain ⟨DN, hDN⟩ := hN.exists_vector_bundle_data
  let D : (M ⨿ N).FiniteRankVectorBundleData :=
    { OpensIndex := DM.OpensIndex × DN.OpensIndex
      opens := fun p => DM.opens p.1 ⊓ DN.opens p.2
      coversTop := by
        rw [Opens.coversTop_iff, IsOpenCover, ← iSup_inf_iSup]
        rw [(Opens.coversTop_iff S _).mp DM.coversTop, (Opens.coversTop_iff S _).mp DN.coversTop, inf_top_eq]
      BasisIndex := fun p => DM.BasisIndex p.1 ⊕ DN.BasisIndex p.2
      locallyFree := fun p => by
        let W := DM.opens p.1 ⊓ DN.opens p.2
        have := over_isLeftAdjoint S W
        exact (PreservesColimitPair.iso (overFunctor S.ringCatSheaf W) M N).symm ≪≫
          coprod.mapIso (restrictTrivialization S DM p.1 inf_le_left)
            (restrictTrivialization S DN p.2 inf_le_right) ≪≫ freeSumIso _ _
      finite := fun p => by
        have := DM.finite p.1
        have := DN.finite p.2
        infer_instance }
  refine { exists_vector_bundle_data := ⟨D, fun p => ?_⟩ }
  have := DM.finite p.1
  have := DN.finite p.2
  simp [D, Nat.card_sum, hDM, hDN]

private lemma bundle_initial : HasInitial S.VectorBundles := by
  let Z : S.VectorBundles := ⟨free PEmpty.{u + 1}, 0, free_empty_rank S⟩
  let e (Y : S.VectorBundles) : (Z ⟶ Y) ≃ (PEmpty.{u + 1} → Y.carrier.sections) :=
    (forgetFullyFaithful S).homEquiv.trans (freeHomEquiv _)
  have (Y : S.VectorBundles) : Nonempty (Z ⟶ Y) := ⟨(e Y).symm PEmpty.elim⟩
  have (Y : S.VectorBundles) : Subsingleton (Z ⟶ Y) :=
    ⟨fun f g => (e Y).injective (Subsingleton.elim _ _)⟩
  exact hasInitial_of_unique Z

private lemma bundle_binary : HasBinaryCoproducts S.VectorBundles := by
  have : ∀ (X Y : S.VectorBundles), HasColimit (pair X Y) := fun X Y => by
    let F := Scheme.VectorBundles.toModule S
    let e : pair X Y ⋙ F ≅ pair X.carrier Y.carrier := mapPairIso (Iso.refl _) (Iso.refl _)
    let h := (IsColimit.precomposeHomEquiv e _).symm (coprodIsCoprod X.carrier Y.carrier)
    let B : S.VectorBundles :=
      ⟨X.carrier ⨿ Y.carrier, X.rank + Y.rank,
        coprod_rank S X.isLocallyFreeFiniteConstantRank Y.isLocallyFreeFiniteConstantRank⟩
    letI : HasColimit (pair X Y ⋙ F) := ⟨⟨_, h⟩⟩
    letI : CreatesColimit (pair X Y) F := createsColimitOfFullyFaithfulOfIso' h B (Iso.refl _)
    exact hasColimit_of_created (pair X Y) F
  exact hasBinaryCoproducts_of_hasColimit_pair S.VectorBundles

theorem OMA.solution : type_of% @AlgebraicGeometry.Scheme.hasFiniteCoproductsVectorBundles := by
  intro S
  exact @CategoryTheory.hasFiniteCoproducts_of_has_binary_and_initial S.VectorBundles _
    (bundle_binary S) (bundle_initial S)

end
