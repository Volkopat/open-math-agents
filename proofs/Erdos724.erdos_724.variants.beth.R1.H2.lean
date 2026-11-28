import OMAReductions.R_Erdos724_erdos_724_variants_beth_R1

-- Step Erdos724.erdos_724.variants.wilson.R1.H2: hypothesis H2 of reduction Erdos724.erdos_724.variants.wilson.R1
-- Credit: @ivillar
-- MacNeish's product construction: the direct products of m mutually orthogonal squares of
-- order a with m of order b are m mutually orthogonal squares of order ab.

open Finset

namespace O2W2

open Erdos724

/-- The direct product of a square of order `a` and a square of order `b`. -/
def prodSq {a b : ℕ} (L : LatinSquare a) (M : LatinSquare b) : LatinSquare (a * b) where
  mat := fun x y => finProdFinEquiv
    (L.mat (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm y).1,
     M.mat (finProdFinEquiv.symm x).2 (finProdFinEquiv.symm y).2)
  row_injective := by
    intro x y y' h
    have h' := finProdFinEquiv.injective h
    simp only [Prod.mk.injEq] at h'
    have h1 := L.row_injective _ h'.1
    have h2 := M.row_injective _ h'.2
    exact finProdFinEquiv.symm.injective (Prod.ext h1 h2)
  col_injective := by
    intro y x x' h
    have h' := finProdFinEquiv.injective h
    simp only [Prod.mk.injEq] at h'
    have h1 := L.col_injective _ h'.1
    have h2 := M.col_injective _ h'.2
    exact finProdFinEquiv.symm.injective (Prod.ext h1 h2)

lemma prodSq_orth {a b : ℕ} {L L' : LatinSquare a} {M M' : LatinSquare b}
    (hL : IsOrthogonal L L') (hM : IsOrthogonal M M') :
    IsOrthogonal (prodSq L M) (prodSq L' M') := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  simp only [prodSq, Prod.mk.injEq] at h
  have h1 := finProdFinEquiv.injective h.1
  have h2 := finProdFinEquiv.injective h.2
  simp only [Prod.mk.injEq] at h1 h2
  have e1 := hL (a₁ := ((finProdFinEquiv.symm x).1, (finProdFinEquiv.symm y).1))
    (a₂ := ((finProdFinEquiv.symm x').1, (finProdFinEquiv.symm y').1))
    (Prod.ext h1.1 h2.1)
  have e2 := hM (a₁ := ((finProdFinEquiv.symm x).2, (finProdFinEquiv.symm y).2))
    (a₂ := ((finProdFinEquiv.symm x').2, (finProdFinEquiv.symm y').2))
    (Prod.ext h1.2 h2.2)
  simp only [Prod.mk.injEq] at e1 e2
  have hx : x = x' := finProdFinEquiv.symm.injective (Prod.ext e1.1 e2.1)
  have hy : y = y' := finProdFinEquiv.symm.injective (Prod.ext e1.2 e2.2)
  rw [hx, hy]

lemma prodSq_left {a b : ℕ} (hb : 0 < b) {L L' : LatinSquare a} {M M' : LatinSquare b}
    (h : prodSq L M = prodSq L' M') : L = L' := by
  have hm : ∀ u v : Fin a, L.mat u v = L'.mat u v := by
    intro u v
    have := congrArg (fun P : LatinSquare (a * b) =>
      (finProdFinEquiv.symm (P.mat (finProdFinEquiv (u, ⟨0, hb⟩))
        (finProdFinEquiv (v, ⟨0, hb⟩)))).1) h
    simp only [prodSq, Equiv.symm_apply_apply] at this
    exact this
  cases L; cases L'
  simp only [LatinSquare.mk.injEq]
  funext u v
  exact hm u v

lemma bdd (n : ℕ) : BddAbove {k : ℕ | ∃ S : Finset (LatinSquare n), #S = k ∧
    (S : Set (LatinSquare n)).Pairwise IsOrthogonal} := by
  classical
  refine ⟨Fintype.card (LatinSquare n), ?_⟩
  rintro k ⟨S, rfl, -⟩
  exact card_le_univ S

lemma attain (n : ℕ) : ∃ S : Finset (LatinSquare n), #S = maxMOLS n ∧
    (S : Set (LatinSquare n)).Pairwise IsOrthogonal := by
  have h := Nat.sSup_mem (s := {k : ℕ | ∃ S : Finset (LatinSquare n), #S = k ∧
    (S : Set (LatinSquare n)).Pairwise IsOrthogonal}) ⟨0, ∅, by simp, by simp⟩ (bdd n)
  exact h

theorem macNeish (a b : ℕ) (_ha : 1 ≤ a) (hb : 1 ≤ b) :
    min (maxMOLS a) (maxMOLS b) ≤ maxMOLS (a * b) := by
  classical
  set m := min (maxMOLS a) (maxMOLS b)
  obtain ⟨Sa, hSa, hpa⟩ := attain a
  obtain ⟨Sb, hSb, hpb⟩ := attain b
  obtain ⟨Ta, hTa, hTac⟩ := exists_subset_card_eq (show m ≤ #Sa by rw [hSa]; exact min_le_left _ _)
  obtain ⟨Tb, hTb, hTbc⟩ := exists_subset_card_eq (show m ≤ #Sb by rw [hSb]; exact min_le_right _ _)
  have hpa' := hpa.mono (coe_subset.mpr hTa)
  have hpb' := hpb.mono (coe_subset.mpr hTb)
  let fa : Fin m → LatinSquare a := fun i => (Ta.equivFinOfCardEq hTac).symm i
  let fb : Fin m → LatinSquare b := fun i => (Tb.equivFinOfCardEq hTbc).symm i
  have fa_mem : ∀ i, fa i ∈ Ta := fun i => ((Ta.equivFinOfCardEq hTac).symm i).2
  have fb_mem : ∀ i, fb i ∈ Tb := fun i => ((Tb.equivFinOfCardEq hTbc).symm i).2
  have fa_inj : Function.Injective fa := by
    intro i j h
    exact (Ta.equivFinOfCardEq hTac).symm.injective (Subtype.ext h)
  have fb_inj : Function.Injective fb := by
    intro i j h
    exact (Tb.equivFinOfCardEq hTbc).symm.injective (Subtype.ext h)
  let g : Fin m → LatinSquare (a * b) := fun i => prodSq (fa i) (fb i)
  have g_inj : Function.Injective g := fun i j h => fa_inj (prodSq_left (by omega) h)
  refine le_csSup (bdd (a * b)) ⟨univ.image g, ?_, ?_⟩
  · rw [card_image_of_injective _ g_inj, card_univ, Fintype.card_fin]
  · intro P hP Q hQ hPQ
    simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at hP hQ
    obtain ⟨i, rfl⟩ := hP
    obtain ⟨j, rfl⟩ := hQ
    have hij : i ≠ j := fun h => hPQ (by rw [h])
    exact prodSq_orth (hpa' (fa_mem i) (fa_mem j) (fun h => hij (fa_inj h)))
      (hpb' (fb_mem i) (fb_mem j) (fun h => hij (fb_inj h)))

end O2W2

theorem OMA.solution : OMA.R_Erdos724_erdos_724_variants_beth_R1.H2 := O2W2.macNeish
