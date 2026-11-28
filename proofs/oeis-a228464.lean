import OMAStatements.S_oeis_a228464

namespace OMA.S_oeis_a228464

open PowerSeries



/-- The largest array whose maxima of three adjacent elements are at most Y: entry j is the
minimum of the Y i over the windows i that contain j. -/
def XS (Y : Fin 7 → ℕ) : Fin 9 → ℕ := ![Y 0, min (Y 0) (Y 1), min (Y 0) (min (Y 1) (Y 2)), min (Y 1) (min (Y 2) (Y 3)), min (Y 2) (min (Y 3) (Y 4)), min (Y 3) (min (Y 4) (Y 5)), min (Y 4) (min (Y 5) (Y 6)), min (Y 5) (Y 6), Y 6]

/-- y is a maxima array: each y i is at most every y a over the windows a containing one of the
positions i, i+1, i+2 (written out; the conditions for i = 0 and i = 6 always hold). -/
def good (y : Fin 7 → ℕ) : Prop :=
  (y 1 ≤ y 0 ∨ (y 1 ≤ y 2 ∧ y 1 ≤ y 3)) ∧
    ((y 2 ≤ y 0 ∧ y 2 ≤ y 1) ∨ (y 2 ≤ y 1 ∧ y 2 ≤ y 3) ∨ (y 2 ≤ y 3 ∧ y 2 ≤ y 4)) ∧
    ((y 3 ≤ y 1 ∧ y 3 ≤ y 2) ∨ (y 3 ≤ y 2 ∧ y 3 ≤ y 4) ∨ (y 3 ≤ y 4 ∧ y 3 ≤ y 5)) ∧
    ((y 4 ≤ y 2 ∧ y 4 ≤ y 3) ∨ (y 4 ≤ y 3 ∧ y 4 ≤ y 5) ∨ (y 4 ≤ y 5 ∧ y 4 ≤ y 6)) ∧
    ((y 5 ≤ y 3 ∧ y 5 ≤ y 4) ∨ y 5 ≤ y 6)

instance : DecidablePred good := fun x => by unfold good; infer_instance

/-- The count of the arrays with property `good`. -/
def b (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun y : Fin 7 → Fin (n + 1) => good (fun i => (y i : ℕ)))).card

/-- Every maxima array satisfies `good` (written out for y k = max x k (max x (k+1) x (k+2))):
y i is the x j attaining the maximum, which is at most every y a over the windows containing j. -/
lemma core (x0 x1 x2 x3 x4 x5 x6 x7 x8 : ℕ) :
    ((max x1 (max x2 x3)) ≤ (max x0 (max x1 x2)) ∨ ((max x1 (max x2 x3)) ≤ (max x2 (max x3 x4)) ∧ (max x1 (max x2 x3)) ≤ (max x3 (max x4 x5)))) ∧
    (((max x2 (max x3 x4)) ≤ (max x0 (max x1 x2)) ∧ (max x2 (max x3 x4)) ≤ (max x1 (max x2 x3))) ∨ ((max x2 (max x3 x4)) ≤ (max x1 (max x2 x3)) ∧ (max x2 (max x3 x4)) ≤ (max x3 (max x4 x5))) ∨ ((max x2 (max x3 x4)) ≤ (max x3 (max x4 x5)) ∧ (max x2 (max x3 x4)) ≤ (max x4 (max x5 x6)))) ∧
    (((max x3 (max x4 x5)) ≤ (max x1 (max x2 x3)) ∧ (max x3 (max x4 x5)) ≤ (max x2 (max x3 x4))) ∨ ((max x3 (max x4 x5)) ≤ (max x2 (max x3 x4)) ∧ (max x3 (max x4 x5)) ≤ (max x4 (max x5 x6))) ∨ ((max x3 (max x4 x5)) ≤ (max x4 (max x5 x6)) ∧ (max x3 (max x4 x5)) ≤ (max x5 (max x6 x7)))) ∧
    (((max x4 (max x5 x6)) ≤ (max x2 (max x3 x4)) ∧ (max x4 (max x5 x6)) ≤ (max x3 (max x4 x5))) ∨ ((max x4 (max x5 x6)) ≤ (max x3 (max x4 x5)) ∧ (max x4 (max x5 x6)) ≤ (max x5 (max x6 x7))) ∨ ((max x4 (max x5 x6)) ≤ (max x5 (max x6 x7)) ∧ (max x4 (max x5 x6)) ≤ (max x6 (max x7 x8)))) ∧
    (((max x5 (max x6 x7)) ≤ (max x3 (max x4 x5)) ∧ (max x5 (max x6 x7)) ≤ (max x4 (max x5 x6))) ∨ (max x5 (max x6 x7)) ≤ (max x6 (max x7 x8))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases max_choice x1 (max x2 x3) with h | h
    · rw [h]
      exact Or.inl ((le_max_left _ _).trans (le_max_right _ _))
    · rcases max_choice x2 x3 with h' | h'
      · rw [h, h']
        exact Or.inl ((le_max_right _ _).trans (le_max_right _ _))
      · rw [h, h']
        exact Or.inr ⟨(le_max_left _ _).trans (le_max_right _ _), le_max_left _ _⟩
  · rcases max_choice x2 (max x3 x4) with h | h
    · rw [h]
      exact Or.inl ⟨(le_max_right _ _).trans (le_max_right _ _), (le_max_left _ _).trans (le_max_right _ _)⟩
    · rcases max_choice x3 x4 with h' | h'
      · rw [h, h']
        exact Or.inr (Or.inl ⟨(le_max_right _ _).trans (le_max_right _ _), le_max_left _ _⟩)
      · rw [h, h']
        exact Or.inr (Or.inr ⟨(le_max_left _ _).trans (le_max_right _ _), le_max_left _ _⟩)
  · rcases max_choice x3 (max x4 x5) with h | h
    · rw [h]
      exact Or.inl ⟨(le_max_right _ _).trans (le_max_right _ _), (le_max_left _ _).trans (le_max_right _ _)⟩
    · rcases max_choice x4 x5 with h' | h'
      · rw [h, h']
        exact Or.inr (Or.inl ⟨(le_max_right _ _).trans (le_max_right _ _), le_max_left _ _⟩)
      · rw [h, h']
        exact Or.inr (Or.inr ⟨(le_max_left _ _).trans (le_max_right _ _), le_max_left _ _⟩)
  · rcases max_choice x4 (max x5 x6) with h | h
    · rw [h]
      exact Or.inl ⟨(le_max_right _ _).trans (le_max_right _ _), (le_max_left _ _).trans (le_max_right _ _)⟩
    · rcases max_choice x5 x6 with h' | h'
      · rw [h, h']
        exact Or.inr (Or.inl ⟨(le_max_right _ _).trans (le_max_right _ _), le_max_left _ _⟩)
      · rw [h, h']
        exact Or.inr (Or.inr ⟨(le_max_left _ _).trans (le_max_right _ _), le_max_left _ _⟩)
  · rcases max_choice x5 (max x6 x7) with h | h
    · rw [h]
      exact Or.inl ⟨(le_max_right _ _).trans (le_max_right _ _), (le_max_left _ _).trans (le_max_right _ _)⟩
    · rcases max_choice x6 x7 with h' | h'
      · rw [h, h']
        exact Or.inr (le_max_left _ _)
      · rw [h, h']
        exact Or.inr ((le_max_left _ _).trans (le_max_right _ _))

lemma XS_lt {N : ℕ} (Y : Fin 7 → ℕ) (h : ∀ i, Y i < N) (j : Fin 9) : XS Y j < N := by
  have := h 0
  fin_cases j <;> simp [XS, min_lt_iff, h]

/-- y is a maxima array iff it satisfies `good`. -/
lemma mem_iff {n : ℕ} (y : Fin 7 → Fin (n + 1)) :
    (∃ x : Fin 9 → Fin (n + 1), maxima x = y) ↔ good (fun i => (y i : ℕ)) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact core (x 0 : ℕ) (x 1 : ℕ) (x 2 : ℕ) (x 3 : ℕ) (x 4 : ℕ) (x 5 : ℕ) (x 6 : ℕ) (x 7 : ℕ) (x 8 : ℕ)
  · intro hg
    refine ⟨fun j => ⟨XS (fun i => (y i : ℕ)) j, XS_lt _ (fun i => (y i).isLt) j⟩, ?_⟩
    funext i
    apply Fin.ext
    fin_cases i
    · show max ((y 0 : ℕ)) (max (min ((y 0 : ℕ)) ((y 1 : ℕ))) (min ((y 0 : ℕ)) (min ((y 1 : ℕ)) ((y 2 : ℕ))))) = (y 0 : ℕ)
      exact le_antisymm (max_le (le_refl _) (max_le (min_le_left _ _) (min_le_left _ _)))
        (le_max_of_le_left (le_refl _))
    · show max (min ((y 0 : ℕ)) ((y 1 : ℕ))) (max (min ((y 0 : ℕ)) (min ((y 1 : ℕ)) ((y 2 : ℕ)))) (min ((y 1 : ℕ)) (min ((y 2 : ℕ)) ((y 3 : ℕ))))) = (y 1 : ℕ)
      rcases hg.1 with h1 | ⟨h1, h2⟩
      · exact le_antisymm (max_le (min_le_right _ _) (max_le ((min_le_right _ _).trans (min_le_left _ _)) (min_le_left _ _)))
          (le_max_of_le_left (le_min (h1) (le_refl _)))
      · exact le_antisymm (max_le (min_le_right _ _) (max_le ((min_le_right _ _).trans (min_le_left _ _)) (min_le_left _ _)))
          (le_max_of_le_right (le_max_of_le_right (le_min (le_refl _) (le_min (h1) (h2)))))
    · show max (min ((y 0 : ℕ)) (min ((y 1 : ℕ)) ((y 2 : ℕ)))) (max (min ((y 1 : ℕ)) (min ((y 2 : ℕ)) ((y 3 : ℕ)))) (min ((y 2 : ℕ)) (min ((y 3 : ℕ)) ((y 4 : ℕ))))) = (y 2 : ℕ)
      rcases hg.2.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact le_antisymm (max_le ((min_le_right _ _).trans (min_le_right _ _)) (max_le ((min_le_right _ _).trans (min_le_left _ _)) (min_le_left _ _)))
          (le_max_of_le_left (le_min (h1) (le_min (h2) (le_refl _))))
      · exact le_antisymm (max_le ((min_le_right _ _).trans (min_le_right _ _)) (max_le ((min_le_right _ _).trans (min_le_left _ _)) (min_le_left _ _)))
          (le_max_of_le_right (le_max_of_le_left (le_min (h1) (le_min (le_refl _) (h2)))))
      · exact le_antisymm (max_le ((min_le_right _ _).trans (min_le_right _ _)) (max_le ((min_le_right _ _).trans (min_le_left _ _)) (min_le_left _ _)))
          (le_max_of_le_right (le_max_of_le_right (le_min (le_refl _) (le_min (h1) (h2)))))
    · show max (min ((y 1 : ℕ)) (min ((y 2 : ℕ)) ((y 3 : ℕ)))) (max (min ((y 2 : ℕ)) (min ((y 3 : ℕ)) ((y 4 : ℕ)))) (min ((y 3 : ℕ)) (min ((y 4 : ℕ)) ((y 5 : ℕ))))) = (y 3 : ℕ)
      rcases hg.2.2.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact le_antisymm (max_le ((min_le_right _ _).trans (min_le_right _ _)) (max_le ((min_le_right _ _).trans (min_le_left _ _)) (min_le_left _ _)))
          (le_max_of_le_left (le_min (h1) (le_min (h2) (le_refl _))))
      · exact le_antisymm (max_le ((min_le_right _ _).trans (min_le_right _ _)) (max_le ((min_le_right _ _).trans (min_le_left _ _)) (min_le_left _ _)))
          (le_max_of_le_right (le_max_of_le_left (le_min (h1) (le_min (le_refl _) (h2)))))
      · exact le_antisymm (max_le ((min_le_right _ _).trans (min_le_right _ _)) (max_le ((min_le_right _ _).trans (min_le_left _ _)) (min_le_left _ _)))
          (le_max_of_le_right (le_max_of_le_right (le_min (le_refl _) (le_min (h1) (h2)))))
    · show max (min ((y 2 : ℕ)) (min ((y 3 : ℕ)) ((y 4 : ℕ)))) (max (min ((y 3 : ℕ)) (min ((y 4 : ℕ)) ((y 5 : ℕ)))) (min ((y 4 : ℕ)) (min ((y 5 : ℕ)) ((y 6 : ℕ))))) = (y 4 : ℕ)
      rcases hg.2.2.2.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact le_antisymm (max_le ((min_le_right _ _).trans (min_le_right _ _)) (max_le ((min_le_right _ _).trans (min_le_left _ _)) (min_le_left _ _)))
          (le_max_of_le_left (le_min (h1) (le_min (h2) (le_refl _))))
      · exact le_antisymm (max_le ((min_le_right _ _).trans (min_le_right _ _)) (max_le ((min_le_right _ _).trans (min_le_left _ _)) (min_le_left _ _)))
          (le_max_of_le_right (le_max_of_le_left (le_min (h1) (le_min (le_refl _) (h2)))))
      · exact le_antisymm (max_le ((min_le_right _ _).trans (min_le_right _ _)) (max_le ((min_le_right _ _).trans (min_le_left _ _)) (min_le_left _ _)))
          (le_max_of_le_right (le_max_of_le_right (le_min (le_refl _) (le_min (h1) (h2)))))
    · show max (min ((y 3 : ℕ)) (min ((y 4 : ℕ)) ((y 5 : ℕ)))) (max (min ((y 4 : ℕ)) (min ((y 5 : ℕ)) ((y 6 : ℕ)))) (min ((y 5 : ℕ)) ((y 6 : ℕ)))) = (y 5 : ℕ)
      rcases hg.2.2.2.2 with ⟨h1, h2⟩ | h1
      · exact le_antisymm (max_le ((min_le_right _ _).trans (min_le_right _ _)) (max_le ((min_le_right _ _).trans (min_le_left _ _)) (min_le_left _ _)))
          (le_max_of_le_left (le_min (h1) (le_min (h2) (le_refl _))))
      · exact le_antisymm (max_le ((min_le_right _ _).trans (min_le_right _ _)) (max_le ((min_le_right _ _).trans (min_le_left _ _)) (min_le_left _ _)))
          (le_max_of_le_right (le_max_of_le_right (le_min (le_refl _) (h1))))
    · show max (min ((y 4 : ℕ)) (min ((y 5 : ℕ)) ((y 6 : ℕ)))) (max (min ((y 5 : ℕ)) ((y 6 : ℕ))) ((y 6 : ℕ))) = (y 6 : ℕ)
      exact le_antisymm (max_le ((min_le_right _ _).trans (min_le_right _ _)) (max_le (min_le_right _ _) (le_refl _)))
        (le_max_of_le_right (le_max_of_le_right (le_refl _)))

lemma a_eq_b : a = b := by
  funext n
  unfold a b
  rw [Finset.filter_congr (fun y _ => mem_iff y)]

section Patterns

variable {k : ℕ} (P : (Fin k → ℕ) → Prop) [DecidablePred P]

/-- The number of surjective patterns g : Fin k → Fin j with the property. -/
def pc (j : ℕ) : ℕ :=
  (Finset.univ.filter (fun g : Fin k → Fin j => Function.Surjective g ∧ P (fun i => (g i : ℕ)))).card

variable {P}

/-- The arrays with image S correspond to the surjective patterns onto Fin S.card. -/
theorem fiber_card (hP : ∀ (m : ℕ) (e₁ e₂ : Fin m ↪o ℕ) (g : Fin k → Fin m),
      P (fun i => e₁ (g i)) ↔ P (fun i => e₂ (g i)))
    {n : ℕ} (S : Finset (Fin (n + 1))) :
    ((Finset.univ.filter (fun x : Fin k → Fin (n + 1) => P (fun i => (x i : ℕ)))).filter
      (fun x => Finset.univ.image x = S)).card = pc P S.card := by
  symm
  unfold pc
  apply Finset.card_bij (fun g _ => fun i => S.orderEmbOfFin rfl (g i))
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    obtain ⟨hs, hp⟩ := hg
    refine ⟨?_, ?_⟩
    · have h := hP S.card ((S.orderEmbOfFin rfl).trans (Fin.valOrderEmb (n + 1)))
        (Fin.valOrderEmb S.card) g
      simp only [RelEmbedding.trans_apply, Fin.valOrderEmb_apply] at h
      exact h.2 hp
    · ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        exact Finset.orderEmbOfFin_mem S rfl (g i)
      · intro hy
        have hy' : y ∈ Set.range (S.orderEmbOfFin rfl) := by
          rw [Finset.range_orderEmbOfFin]
          exact hy
        obtain ⟨j, hj⟩ := hy'
        obtain ⟨i, hi⟩ := hs j
        exact ⟨i, by rw [hi, hj]⟩
  · intro g₁ _ g₂ _ h
    funext i
    exact (S.orderEmbOfFin rfl).injective (congrFun h i)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hp, himg⟩ := hx
    have hmem : ∀ i, x i ∈ S := fun i => by
      rw [← himg]
      exact Finset.mem_image_of_mem x (Finset.mem_univ i)
    have hx_eq : ∀ i, S.orderEmbOfFin rfl ((S.orderIsoOfFin rfl).symm ⟨x i, hmem i⟩) = x i := by
      intro i
      rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
    refine ⟨fun i => (S.orderIsoOfFin rfl).symm ⟨x i, hmem i⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · intro j
        have hj : S.orderEmbOfFin rfl j ∈ Finset.univ.image x := by
          rw [himg]
          exact Finset.orderEmbOfFin_mem S rfl j
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hj
        obtain ⟨i, hi⟩ := hj
        refine ⟨i, ?_⟩
        apply (S.orderEmbOfFin rfl).injective
        show S.orderEmbOfFin rfl ((S.orderIsoOfFin rfl).symm ⟨x i, hmem i⟩) = S.orderEmbOfFin rfl j
        rw [hx_eq]
        exact hi
      · have h := hP S.card ((S.orderEmbOfFin rfl).trans (Fin.valOrderEmb (n + 1)))
          (Fin.valOrderEmb S.card) (fun i => (S.orderIsoOfFin rfl).symm ⟨x i, hmem i⟩)
        simp only [RelEmbedding.trans_apply, Fin.valOrderEmb_apply, hx_eq] at h
        exact h.1 hp
    · funext i
      exact hx_eq i

/-- The count of arrays as a sum over pattern sizes. -/
theorem count_eq (hP : ∀ (m : ℕ) (e₁ e₂ : Fin m ↪o ℕ) (g : Fin k → Fin m),
      P (fun i => e₁ (g i)) ↔ P (fun i => e₂ (g i))) (n : ℕ) :
    (Finset.univ.filter (fun x : Fin k → Fin (n + 1) => P (fun i => (x i : ℕ)))).card =
      ∑ j ∈ Finset.range (k + 1), (n + 1).choose j * pc P j := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x : Fin k → Fin (n + 1) => Finset.univ.image x)
    (t := Finset.univ) (by intro x _; simp)]
  refine (Finset.sum_congr rfl (fun S _ => fiber_card hP S)).trans ?_
  rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card (f := pc P)]
  simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hz : ∀ j, k < j → pc P j = 0 := by
    intro j hj
    unfold pc
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro g - ⟨hs, -⟩
    have := Fintype.card_le_of_surjective g hs
    simp only [Fintype.card_fin] at this
    omega
  have e1 : ∑ m ∈ Finset.range (n + 1 + 1), (n + 1).choose m * pc P m =
      ∑ m ∈ Finset.range (n + k + 2), (n + 1).choose m * pc P m := by
    apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
    intro m _ hm
    simp only [Finset.mem_range, not_lt] at hm
    rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
  have e2 : ∑ m ∈ Finset.range (k + 1), (n + 1).choose m * pc P m =
      ∑ m ∈ Finset.range (n + k + 2), (n + 1).choose m * pc P m := by
    apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
    intro m _ hm
    simp only [Finset.mem_range, not_lt] at hm
    rw [hz m (by omega), mul_zero]
  rw [e1, e2]

end Patterns

section Head

variable {k : ℕ} (P : (Fin (k + 1) → ℕ) → Prop) [DecidablePred P]

/-- Splitting a count of functions on Fin (k + 1) by the value at 0. -/
theorem card_by_head {j : ℕ} (Q : (Fin (k + 1) → Fin j) → Prop) [DecidablePred Q] :
    (Finset.univ.filter Q).card =
      ∑ v : Fin j, (Finset.univ.filter (fun h : Fin k → Fin j => Q (Fin.cons v h))).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g : Fin (k + 1) → Fin j => g 0) (t := Finset.univ)
    (by intro x _; simp)]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  symm
  apply Finset.card_bij (fun h _ => (Fin.cons v h : Fin (k + 1) → Fin j))
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    exact ⟨hh, by simp⟩
  · intro h₁ _ h₂ _ e
    simpa using congrArg Fin.tail e
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨hq, h0⟩ := hg
    refine ⟨Fin.tail g, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← h0, Fin.cons_self_tail]
      exact hq
    · show Fin.cons v (Fin.tail g) = g
      rw [← h0, Fin.cons_self_tail]

/-- The number of surjective patterns g : Fin (k + 1) → Fin j with the property and g 0 = v. -/
def pcs (j : ℕ) (v : Fin j) : ℕ :=
  (Finset.univ.filter (fun h : Fin k → Fin j =>
    Function.Surjective (Fin.cons v h : Fin (k + 1) → Fin j) ∧
      P (fun i => ((Fin.cons v h : Fin (k + 1) → Fin j) i : ℕ)))).card

theorem pc_succ (j : ℕ) : pc P j = ∑ v : Fin j, pcs P j v := by
  unfold pc pcs
  exact card_by_head (fun g : Fin (k + 1) → Fin j => Function.Surjective g ∧ P (fun i => (g i : ℕ)))

end Head

lemma ch2 (n : ℕ) : ((n + 1).choose 2 : ℚ) = (n + 1) * n / 2 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ m ih =>
    have h : (m + 1 + 1).choose 2 = (m + 1).choose 1 + (m + 1).choose 2 :=
      Nat.choose_succ_succ' (m + 1) 1
    rw [h, Nat.cast_add, ih, Nat.choose_one_right]
    push_cast
    ring

lemma ch3 (n : ℕ) : ((n + 1).choose 3 : ℚ) = (n + 1) * n * (n - 1) / 6 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ m ih =>
    have h : (m + 1 + 1).choose 3 = (m + 1).choose 2 + (m + 1).choose 3 :=
      Nat.choose_succ_succ' (m + 1) 2
    rw [h, Nat.cast_add, ih, ch2]
    push_cast
    ring

lemma ch4 (n : ℕ) : ((n + 1).choose 4 : ℚ) = (n + 1) * n * (n - 1) * (n - 2) / 24 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ m ih =>
    have h : (m + 1 + 1).choose 4 = (m + 1).choose 3 + (m + 1).choose 4 :=
      Nat.choose_succ_succ' (m + 1) 3
    rw [h, Nat.cast_add, ih, ch3]
    push_cast
    ring

lemma ch5 (n : ℕ) : ((n + 1).choose 5 : ℚ) = (n + 1) * n * (n - 1) * (n - 2) * (n - 3) / 120 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ m ih =>
    have h : (m + 1 + 1).choose 5 = (m + 1).choose 4 + (m + 1).choose 5 :=
      Nat.choose_succ_succ' (m + 1) 4
    rw [h, Nat.cast_add, ih, ch4]
    push_cast
    ring

lemma ch6 (n : ℕ) : ((n + 1).choose 6 : ℚ) = (n + 1) * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) / 720 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ m ih =>
    have h : (m + 1 + 1).choose 6 = (m + 1).choose 5 + (m + 1).choose 6 :=
      Nat.choose_succ_succ' (m + 1) 5
    rw [h, Nat.cast_add, ih, ch5]
    push_cast
    ring

lemma ch7 (n : ℕ) : ((n + 1).choose 7 : ℚ) = (n + 1) * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) / 5040 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ m ih =>
    have h : (m + 1 + 1).choose 7 = (m + 1).choose 6 + (m + 1).choose 7 :=
      Nat.choose_succ_succ' (m + 1) 6
    rw [h, Nat.cast_add, ih, ch6]
    push_cast
    ring

lemma hP : ∀ (m : ℕ) (e₁ e₂ : Fin m ↪o ℕ) (g : Fin 7 → Fin m),
    good (fun i => e₁ (g i)) ↔ good (fun i => e₂ (g i)) := by
  intro m e₁ e₂ g
  simp only [good, OrderEmbedding.le_iff_le]

section DP5Count

/-- The windows (a, b, c, d, e), (b, c, d, e, f), ... of a list of numbers all pass W and its last
four entries pass E (lists shorter than four fail). -/
def wins5E (W : ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (E : ℕ → ℕ → ℕ → ℕ → Bool) : List ℕ → Bool
  | a :: b :: c :: d :: e :: t => W a b c d e && wins5E W E (b :: c :: d :: e :: t)
  | [a, b, c, d] => E a b c d
  | _ => false

/-- The first four entries of a list pass S (lists shorter than four fail). -/
def startE (S : ℕ → ℕ → ℕ → ℕ → Bool) : List ℕ → Bool
  | a :: b :: c :: d :: _ => S a b c d
  | _ => false

/-- The windows (a, b, c, d, h 0), (b, c, d, h 0, h 1), ... pass W and the last four values pass E. -/
def chain5 {N : ℕ} (W : ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (E : ℕ → ℕ → ℕ → ℕ → Bool) :
    (L : ℕ) → ℕ → ℕ → ℕ → ℕ → (Fin L → Fin N) → Bool
  | 0, a, b, c, d, _ => E a b c d
  | L + 1, a, b, c, d, h => W a b c d (h 0) && chain5 W E L b c d (h 0) (Fin.tail h)

lemma chain5_wins {N : ℕ} (W : ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (E : ℕ → ℕ → ℕ → ℕ → Bool) :
    ∀ (L : ℕ) (a b c d : ℕ) (h : Fin L → Fin N),
    chain5 W E L a b c d h = wins5E W E (a :: b :: c :: d :: List.ofFn (fun i => (h i : ℕ)))
  | 0, a, b, c, d, h => by simp [chain5, wins5E]
  | L + 1, a, b, c, d, h => by
    rw [chain5, chain5_wins W E L, List.ofFn_succ, wins5E]
    rfl

/-- The number of sequences h : Fin L → Fin N continuing a, b, c, d that pass chain5. The kernel
evaluates each value once. -/
def dp5 (W : ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (E : ℕ → ℕ → ℕ → ℕ → Bool) (N : ℕ) :
    (L : ℕ) → Fin N → Fin N → Fin N → Fin N → ℕ
  | 0, a, b, c, d => if E a b c d = true then 1 else 0
  | L + 1, a, b, c, d => ∑ v : Fin N, if W a b c d v = true then dp5 W E N L b c d v else 0

theorem dp5_eq (W : ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (E : ℕ → ℕ → ℕ → ℕ → Bool) (N : ℕ) :
    ∀ (L : ℕ) (a b c d : Fin N), dp5 W E N L a b c d =
      (Finset.univ.filter (fun h : Fin L → Fin N => chain5 W E L a b c d h = true)).card
  | 0, a, b, c, d => by
    rw [dp5]
    have hu : (Finset.univ : Finset (Fin 0 → Fin N)) = {Fin.elim0} := by
      ext g
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      funext i
      exact i.elim0
    rw [hu, Finset.filter_singleton]
    by_cases hE : E a b c d = true <;> simp [chain5, hE]
  | L + 1, a, b, c, d => by
    rw [dp5, card_by_head]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    split_ifs with hW
    · rw [dp5_eq W E N L b c d v]
      congr 1
      ext h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, chain5, Fin.cons_zero, Fin.tail_cons,
        hW, Bool.true_and]
    · symm
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro h - hc
      simp only [chain5, Fin.cons_zero, Bool.and_eq_true] at hc
      exact hW hc.1

/-- The arrays counted by a start test S on the first four entries, a window test W of five and
an end test E on the last four, through dp5, split by the first four entries. -/
theorem count_eq_dp5 {k : ℕ} (P : (Fin (k + 4) → ℕ) → Prop) [DecidablePred P]
    (W : ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (E S : ℕ → ℕ → ℕ → ℕ → Bool)
    (hP : ∀ y, P y ↔ (startE S (List.ofFn y) && wins5E W E (List.ofFn y)) = true) (n : ℕ) :
    (Finset.univ.filter (fun y : Fin (k + 4) → Fin (n + 1) => P (fun i => (y i : ℕ)))).card =
      ∑ v : Fin (n + 1), ∑ w : Fin (n + 1), ∑ u : Fin (n + 1), ∑ t : Fin (n + 1),
        if S v w u t = true then dp5 W E (n + 1) k v w u t else 0 := by
  rw [card_by_head]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [card_by_head]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [card_by_head]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [card_by_head]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  split_ifs with hS
  · rw [dp5_eq]
    congr 1
    ext h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hP, chain5_wins, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, startE, hS, Bool.true_and]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro h _ hc
    rw [hP, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ] at hc
    simp only [Fin.cons_zero, Fin.cons_succ, startE, Bool.and_eq_true] at hc
    exact hS hc.1

end DP5Count

/-- The test of `good` on five consecutive entries a, b, c, d, e (center c). -/
def W5 (a b c d e : ℕ) : Bool :=
  (decide (c ≤ a) && decide (c ≤ b)) || (decide (c ≤ b) && decide (c ≤ d)) ||
    (decide (c ≤ d) && decide (c ≤ e))

/-- The test of `good` on the first four entries (center b). -/
def S5 (a b c d : ℕ) : Bool := decide (b ≤ a) || (decide (b ≤ c) && decide (b ≤ d))

/-- The test of `good` on the last four entries (center c). -/
def E5 (a b c d : ℕ) : Bool := (decide (c ≤ a) && decide (c ≤ b)) || decide (c ≤ d)

lemma hW5 (y : Fin 7 → ℕ) :
    good y ↔ (startE S5 (List.ofFn y) && wins5E W5 E5 (List.ofFn y)) = true := by
  rw [show List.ofFn y = [y 0, y 1, y 2, y 3, y 4, y 5, y 6] from rfl]
  simp [good, startE, wins5E, W5, S5, E5, or_assoc, and_assoc]

lemma bv0 : b 0 = 1 := by
  unfold b
  rw [count_eq_dp5 good W5 E5 S5 hW5 0]
  decide +kernel

lemma bv1 : b 1 = 44 := by
  unfold b
  rw [count_eq_dp5 good W5 E5 S5 hW5 1]
  decide +kernel

lemma bv2 : b 2 = 383 := by
  unfold b
  rw [count_eq_dp5 good W5 E5 S5 hW5 2]
  decide +kernel

lemma bv3 : b 3 = 1821 := by
  unfold b
  rw [count_eq_dp5 good W5 E5 S5 hW5 3]
  decide +kernel

lemma bv4 : b 4 = 6254 := by
  unfold b
  rw [count_eq_dp5 good W5 E5 S5 hW5 4]
  decide +kernel

lemma bv5 : b 5 = 17487 := by
  unfold b
  rw [count_eq_dp5 good W5 E5 S5 hW5 5]
  decide +kernel

lemma bv6 : b 6 = 42386 := by
  unfold b
  rw [count_eq_dp5 good W5 E5 S5 hW5 6]
  decide +kernel

lemma pc0 : pc good 0 = 0 := by
  decide +kernel

/-- Solving count_eq at n = 0..k-1 for the pattern counts, with the counts as variables. -/
lemma lin (p : ℕ → ℕ) (h0 : p 0 = 0) (e0 : 1 = ∑ j ∈ Finset.range (7 + 1), (0 + 1).choose j * p j)
    (e1 : 44 = ∑ j ∈ Finset.range (7 + 1), (1 + 1).choose j * p j) (e2 : 383 = ∑ j ∈ Finset.range
    (7 + 1), (2 + 1).choose j * p j) (e3 : 1821 = ∑ j ∈ Finset.range (7 + 1), (3 + 1).choose j * p
    j) (e4 : 6254 = ∑ j ∈ Finset.range (7 + 1), (4 + 1).choose j * p j) (e5 : 17487 = ∑ j ∈
    Finset.range (7 + 1), (5 + 1).choose j * p j) (e6 : 42386 = ∑ j ∈ Finset.range (7 + 1), (6 +
    1).choose j * p j) : p 0 = 0 ∧ p 1 = 1 ∧ p 2 = 42 ∧ p 3 = 254 ∧ p 4 = 549 ∧ p 5 = 544 ∧ p 6 =
    272 ∧ p 7 = 64 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at e0 e1 e2 e3 e4 e5 e6
  norm_num [Nat.choose] at e0 e1 e2 e3 e4 e5 e6
  omega

lemma pcv : pc good 0 = 0 ∧ pc good 1 = 1 ∧ pc good 2 = 42 ∧ pc good 3 = 254 ∧ pc good 4 = 549 ∧ pc
    good 5 = 544 ∧ pc good 6 = 272 ∧ pc good 7 = 64 :=
  lin (pc good) pc0 (bv0.symm.trans (count_eq hP 0)) (bv1.symm.trans (count_eq hP 1))
    (bv2.symm.trans (count_eq hP 2)) (bv3.symm.trans (count_eq hP 3)) (bv4.symm.trans (count_eq hP
    4)) (bv5.symm.trans (count_eq hP 5)) (bv6.symm.trans (count_eq hP 6))

/-- The closed form a(n) = Sum_j c_j binomial(n+1, j). -/
lemma a_eq (n : ℕ) : (a n : ℚ) =
    1 * (n + 1) + 42 * ((n + 1) * n / 2) + 254 * ((n + 1) * n * (n - 1) / 6) + 549 * ((n + 1) * n * (n - 1) * (n - 2) / 24) + 544 * ((n + 1) * n * (n - 1) * (n - 2) * (n - 3) / 120) + 272 * ((n + 1) * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) / 720) + 64 * ((n + 1) * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) / 5040) := by
  have h := count_eq hP n
  rw [a_eq_b]
  unfold b
  rw [h]
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := pcv
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, p0, p1, p2, p3, p4, p5, p6, p7]
  push_cast
  simp only [ch2, ch3, ch4, ch5, ch6, ch7]
  simp
  ring

lemma values : a 1 = 44 ∧ a 2 = 383 ∧ a 3 = 1821 ∧ a 4 = 6254 ∧ a 5 = 17487 ∧ a 6 = 42386 ∧ a 7 = 92430 ∧ a 8 = 185727 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [← Nat.cast_inj (R := ℚ), a_eq]
    norm_num

/-- Barker's recurrence, for n > 8. -/
theorem recurrence (n : ℕ) (hn : 8 < n) :
    (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 9 := ⟨n - 9, by omega⟩
  simp only [show q + 9 - 1 = q + 8 by omega, show q + 9 - 2 = q + 7 by omega, show q + 9 - 3 = q +
    6 by omega, show q + 9 - 4 = q + 5 by omega, show q + 9 - 5 = q + 4 by omega, show q + 9 - 6 =
    q + 3 by omega, show q + 9 - 7 = q + 2 by omega, show q + 9 - 8 = q + 1 by omega]
  have h : (a (q + 9) : ℚ) = 8 * a (q + 8) - 28 * a (q + 7) + 56 * a (q + 6) - 70 * a (q + 5) + 56 * a (q + 4) - 28 * a (q + 3) + 8 * a (q + 2) - a (q + 1) := by
    rw [a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq]
    push_cast
    ring
  exact_mod_cast h

/-- Barker's g.f., as A(x) (1 - x)^8 = N(x) in Z[[x]]. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 8 =
    X * (44 + 31 * X - 11 * X ^ 2 - 54 * X ^ 3 + 75 * X ^ 4 - 28 * X ^ 5 + 8 * X ^ 6 - X ^ 7) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 8 =
      A - C 8 * (A * X ^ 1) + C 28 * (A * X ^ 2) - C 56 * (A * X ^ 3) + C 70 * (A * X ^ 4) - C 56 *
        (A * X ^ 5) + C 28 * (A * X ^ 6) - C 8 * (A * X ^ 7) + A * X ^ 8 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (44 + 31 * X - 11 * X ^ 2 - 54 * X ^ 3 + 75 * X ^ 4 - 28 * X ^ 5 + 8 * X ^ 6 - X ^ 7) : ℤ⟦X⟧) =
      X ^ 1 * C 44 + X ^ 2 * C 31 - X ^ 3 * C 11 - X ^ 4 * C 54 + X ^ 5 * C 75 - X ^ 6 * C 28 + X ^
        7 * C 8 - X ^ 8 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  have v := values
  rcases Nat.lt_or_ge n 9 with hn | hn
  · interval_cases n <;> simp_all
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 9 := ⟨n - 9, by omega⟩
    have h := recurrence (q + 9) (by omega)
    simp only [show q + 9 - 1 = q + 8 by omega, show q + 9 - 2 = q + 7 by omega, show q + 9 - 3 =
      q + 6 by omega, show q + 9 - 4 = q + 5 by omega, show q + 9 - 5 = q + 4 by omega, show q + 9 -
      6 = q + 3 by omega, show q + 9 - 7 = q + 2 by omega, show q + 9 - 8 = q + 1 by omega] at h ⊢
    simp only [show ¬ q + 9 = 0 by omega, show ¬ q + 8 = 0 by omega, show ¬ q + 7 = 0 by omega, show
      ¬ q + 6 = 0 by omega, show ¬ q + 5 = 0 by omega, show ¬ q + 4 = 0 by omega, show ¬ q + 3 = 0
      by omega, show ¬ q + 2 = 0 by omega, show ¬ q + 1 = 0 by omega, show 1 ≤ q + 9 by omega, show
      2 ≤ q + 9 by omega, show 3 ≤ q + 9 by omega, show 4 ≤ q + 9 by omega, show 5 ≤ q + 9 by omega,
      show 6 ≤ q + 9 by omega, show 7 ≤ q + 9 by omega, show 8 ≤ q + 9 by omega, show ¬ q + 9 = 1 by
      omega, show ¬ q + 9 = 2 by omega, show ¬ q + 9 = 3 by omega, show ¬ q + 9 = 4 by omega, show ¬
      q + 9 = 5 by omega, show ¬ q + 9 = 6 by omega, show ¬ q + 9 = 7 by omega, show ¬ q + 9 = 8 by
      omega, if_true, if_false]
    rw [h]
    ring

/-- Hardin's empirical formula, for all n. -/
theorem empirical (n : ℕ) : (a n : ℚ) = (4 / 315) * n ^ 7 + (1 / 5) * n ^ 6 + (91 / 45) * n ^ 5 + (63 / 8) * n ^ 4 + (2557 / 180) * n ^ 3 + (517 / 40) * n ^ 2 + (2419 / 420) * n + 1 := by
  rw [a_eq]
  ring

/-- Controls: the entry's data a(1..27). -/
theorem controls : a 1 = 44 ∧ a 2 = 383 ∧ a 3 = 1821 ∧ a 4 = 6254 ∧ a 5 = 17487 ∧ a 6 = 42386 ∧
    a 7 = 92430 ∧ a 8 = 185727 ∧ a 9 = 349558 ∧ a 10 = 623513 ∧ a 11 = 1063283 ∧ a 12 = 1745172 ∧
    a 13 = 2771393 ∧ a 14 = 4276212 ∧ a 15 = 6433004 ∧ a 16 = 9462285 ∧ a 17 = 13640784 ∧
    a 18 = 19311619 ∧ a 19 = 26895641 ∧ a 20 = 36904010 ∧ a 21 = 49952067 ∧ a 22 = 66774566 ∧
    a 23 = 88242330 ∧ a 24 = 115380395 ∧ a 25 = 149387706 ∧ a 26 = 191658429 ∧
    a 27 = 243804943 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [← Nat.cast_inj (R := ℚ), a_eq]
    norm_num

/-- Both of Barker's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 8 < n →
      (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 8 =
      X * (44 + 31 * X - 11 * X ^ 2 - 54 * X ^ 3 + 75 * X ^ 4 - 28 * X ^ 5 + 8 * X ^ 6 - X ^ 7) :=
  ⟨recurrence, gf⟩

end OMA.S_oeis_a228464

theorem OMA.solution : type_of% @OMA.S_oeis_a228464.main :=
  OMA.S_oeis_a228464.conjecture
