import OMAStatements.S_oeis_a228463

namespace OMA.S_oeis_a228463

open PowerSeries



/-- The largest array whose maxima of three adjacent elements are at most Y: entry j is the
minimum of the Y i over the windows i that contain j. -/
def XS (Y : Fin 6 → ℕ) : Fin 8 → ℕ := ![Y 0, min (Y 0) (Y 1), min (Y 0) (min (Y 1) (Y 2)), min (Y 1) (min (Y 2) (Y 3)), min (Y 2) (min (Y 3) (Y 4)), min (Y 3) (min (Y 4) (Y 5)), min (Y 4) (Y 5), Y 5]

/-- y is the array of maxima of XS y (written out). -/
def good (y : Fin 6 → ℕ) : Prop :=
  max (y 0) (max (min (y 0) (y 1)) (min (y 0) (min (y 1) (y 2)))) = y 0 ∧
    max (min (y 0) (y 1)) (max (min (y 0) (min (y 1) (y 2))) (min (y 1) (min (y 2) (y 3)))) = y 1 ∧
    max (min (y 0) (min (y 1) (y 2))) (max (min (y 1) (min (y 2) (y 3))) (min (y 2) (min (y 3) (y 4)))) = y 2 ∧
    max (min (y 1) (min (y 2) (y 3))) (max (min (y 2) (min (y 3) (y 4))) (min (y 3) (min (y 4) (y 5)))) = y 3 ∧
    max (min (y 2) (min (y 3) (y 4))) (max (min (y 3) (min (y 4) (y 5))) (min (y 4) (y 5))) = y 4 ∧
    max (min (y 3) (min (y 4) (y 5))) (max (min (y 4) (y 5)) (y 5)) = y 5

instance : DecidablePred good := fun x => by unfold good; infer_instance

/-- The count of the arrays with property `good`. -/
def b (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun y : Fin 6 → Fin (n + 1) => good (fun i => (y i : ℕ)))).card

/-- Every maxima array satisfies `good` (written out for y k = max (x k) (max (x (k+1))
(x (k+2)))): each x j is at most every y i whose window contains j, hence at most XS y j. -/
lemma core (x0 x1 x2 x3 x4 x5 x6 x7 : ℕ) :
    max ((max x0 (max x1 x2))) (max (min ((max x0 (max x1 x2))) ((max x1 (max x2 x3)))) (min ((max x0 (max x1 x2))) (min ((max x1 (max x2 x3))) ((max x2 (max x3 x4)))))) = (max x0 (max x1 x2)) ∧
    max (min ((max x0 (max x1 x2))) ((max x1 (max x2 x3)))) (max (min ((max x0 (max x1 x2))) (min ((max x1 (max x2 x3))) ((max x2 (max x3 x4))))) (min ((max x1 (max x2 x3))) (min ((max x2 (max x3 x4))) ((max x3 (max x4 x5)))))) = (max x1 (max x2 x3)) ∧
    max (min ((max x0 (max x1 x2))) (min ((max x1 (max x2 x3))) ((max x2 (max x3 x4))))) (max (min ((max x1 (max x2 x3))) (min ((max x2 (max x3 x4))) ((max x3 (max x4 x5))))) (min ((max x2 (max x3 x4))) (min ((max x3 (max x4 x5))) ((max x4 (max x5 x6)))))) = (max x2 (max x3 x4)) ∧
    max (min ((max x1 (max x2 x3))) (min ((max x2 (max x3 x4))) ((max x3 (max x4 x5))))) (max (min ((max x2 (max x3 x4))) (min ((max x3 (max x4 x5))) ((max x4 (max x5 x6))))) (min ((max x3 (max x4 x5))) (min ((max x4 (max x5 x6))) ((max x5 (max x6 x7)))))) = (max x3 (max x4 x5)) ∧
    max (min ((max x2 (max x3 x4))) (min ((max x3 (max x4 x5))) ((max x4 (max x5 x6))))) (max (min ((max x3 (max x4 x5))) (min ((max x4 (max x5 x6))) ((max x5 (max x6 x7))))) (min ((max x4 (max x5 x6))) ((max x5 (max x6 x7))))) = (max x4 (max x5 x6)) ∧
    max (min ((max x3 (max x4 x5))) (min ((max x4 (max x5 x6))) ((max x5 (max x6 x7))))) (max (min ((max x4 (max x5 x6))) ((max x5 (max x6 x7)))) ((max x5 (max x6 x7)))) = (max x5 (max x6 x7)) :=
  ⟨le_antisymm (max_le (le_refl _) (max_le (min_le_left _ _) (min_le_left _ _)))
    (max_le_max (le_max_left _ _) (max_le_max (le_min ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _)) (le_min ((le_max_right _ _).trans (le_max_right _ _)) (le_min ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _))))),
   le_antisymm (max_le (min_le_right _ _) (max_le ((min_le_right _ _).trans (min_le_left _ _)) (min_le_left _ _)))
    (max_le_max (le_min ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _)) (max_le_max (le_min ((le_max_right _ _).trans (le_max_right _ _)) (le_min ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _))) (le_min ((le_max_right _ _).trans (le_max_right _ _)) (le_min ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _))))),
   le_antisymm (max_le ((min_le_right _ _).trans (min_le_right _ _)) (max_le ((min_le_right _ _).trans (min_le_left _ _)) (min_le_left _ _)))
    (max_le_max (le_min ((le_max_right _ _).trans (le_max_right _ _)) (le_min ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _))) (max_le_max (le_min ((le_max_right _ _).trans (le_max_right _ _)) (le_min ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _))) (le_min ((le_max_right _ _).trans (le_max_right _ _)) (le_min ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _))))),
   le_antisymm (max_le ((min_le_right _ _).trans (min_le_right _ _)) (max_le ((min_le_right _ _).trans (min_le_left _ _)) (min_le_left _ _)))
    (max_le_max (le_min ((le_max_right _ _).trans (le_max_right _ _)) (le_min ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _))) (max_le_max (le_min ((le_max_right _ _).trans (le_max_right _ _)) (le_min ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _))) (le_min ((le_max_right _ _).trans (le_max_right _ _)) (le_min ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _))))),
   le_antisymm (max_le ((min_le_right _ _).trans (min_le_right _ _)) (max_le ((min_le_right _ _).trans (min_le_left _ _)) (min_le_left _ _)))
    (max_le_max (le_min ((le_max_right _ _).trans (le_max_right _ _)) (le_min ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _))) (max_le_max (le_min ((le_max_right _ _).trans (le_max_right _ _)) (le_min ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _))) (le_min ((le_max_right _ _).trans (le_max_right _ _)) ((le_max_left _ _).trans (le_max_right _ _))))),
   le_antisymm (max_le ((min_le_right _ _).trans (min_le_right _ _)) (max_le (min_le_right _ _) (le_refl _)))
    (max_le_max (le_min ((le_max_right _ _).trans (le_max_right _ _)) (le_min ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _))) (max_le_max (le_min ((le_max_right _ _).trans (le_max_right _ _)) ((le_max_left _ _).trans (le_max_right _ _))) ((le_max_right _ _).trans (le_max_right _ _))))⟩

lemma XS_lt {N : ℕ} (Y : Fin 6 → ℕ) (h : ∀ i, Y i < N) (j : Fin 8) : XS Y j < N := by
  have := h 0
  fin_cases j <;> simp [XS, min_lt_iff, h]

/-- y is a maxima array iff it satisfies `good`. -/
lemma mem_iff {n : ℕ} (y : Fin 6 → Fin (n + 1)) :
    (∃ x : Fin 8 → Fin (n + 1), maxima x = y) ↔ good (fun i => (y i : ℕ)) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact core (x 0 : ℕ) (x 1 : ℕ) (x 2 : ℕ) (x 3 : ℕ) (x 4 : ℕ) (x 5 : ℕ) (x 6 : ℕ) (x 7 : ℕ)
  · intro hg
    refine ⟨fun j => ⟨XS (fun i => (y i : ℕ)) j, XS_lt _ (fun i => (y i).isLt) j⟩, ?_⟩
    funext i
    apply Fin.ext
    fin_cases i
    · show max ((y 0 : ℕ)) (max (min ((y 0 : ℕ)) ((y 1 : ℕ))) (min ((y 0 : ℕ)) (min ((y 1 : ℕ)) ((y 2 : ℕ))))) = (y 0 : ℕ)
      exact hg.1
    · show max (min ((y 0 : ℕ)) ((y 1 : ℕ))) (max (min ((y 0 : ℕ)) (min ((y 1 : ℕ)) ((y 2 : ℕ)))) (min ((y 1 : ℕ)) (min ((y 2 : ℕ)) ((y 3 : ℕ))))) = (y 1 : ℕ)
      exact hg.2.1
    · show max (min ((y 0 : ℕ)) (min ((y 1 : ℕ)) ((y 2 : ℕ)))) (max (min ((y 1 : ℕ)) (min ((y 2 : ℕ)) ((y 3 : ℕ)))) (min ((y 2 : ℕ)) (min ((y 3 : ℕ)) ((y 4 : ℕ))))) = (y 2 : ℕ)
      exact hg.2.2.1
    · show max (min ((y 1 : ℕ)) (min ((y 2 : ℕ)) ((y 3 : ℕ)))) (max (min ((y 2 : ℕ)) (min ((y 3 : ℕ)) ((y 4 : ℕ)))) (min ((y 3 : ℕ)) (min ((y 4 : ℕ)) ((y 5 : ℕ))))) = (y 3 : ℕ)
      exact hg.2.2.2.1
    · show max (min ((y 2 : ℕ)) (min ((y 3 : ℕ)) ((y 4 : ℕ)))) (max (min ((y 3 : ℕ)) (min ((y 4 : ℕ)) ((y 5 : ℕ)))) (min ((y 4 : ℕ)) ((y 5 : ℕ)))) = (y 4 : ℕ)
      exact hg.2.2.2.2.1
    · show max (min ((y 3 : ℕ)) (min ((y 4 : ℕ)) ((y 5 : ℕ)))) (max (min ((y 4 : ℕ)) ((y 5 : ℕ))) ((y 5 : ℕ))) = (y 5 : ℕ)
      exact hg.2.2.2.2.2

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

lemma hP : ∀ (m : ℕ) (e₁ e₂ : Fin m ↪o ℕ) (g : Fin 6 → Fin m),
    good (fun i => e₁ (g i)) ↔ good (fun i => e₂ (g i)) := by
  intro m e₁ e₂ g
  simp only [good, ← e₁.monotone.map_max, ← e₁.monotone.map_min, ← e₂.monotone.map_max,
    ← e₂.monotone.map_min, EmbeddingLike.apply_eq_iff_eq]

section SCount

/-- The number of h : Fin k → Fin j passing the test Q whose values, together with `used`, cover
Fin j. A branch is cut as soon as too few positions are left to cover the missing values. -/
def scnt : (k j : ℕ) → Finset (Fin j) → ((Fin k → Fin j) → Bool) → ℕ
  | 0, _, used, Q => if used = Finset.univ ∧ Q Fin.elim0 = true then 1 else 0
  | k + 1, j, used, Q =>
      if k + 1 < (Finset.univ \ used).card then 0
      else ∑ v : Fin j, scnt k j (insert v used) (fun h => Q (Fin.cons v h))

lemma image_cons {k j : ℕ} (v : Fin j) (h : Fin k → Fin j) :
    Finset.univ.image (Fin.cons v h : Fin (k + 1) → Fin j) = insert v (Finset.univ.image h) := by
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Fin.exists_fin_succ,
    Fin.cons_zero, Fin.cons_succ]
  constructor
  · rintro (h1 | ⟨i, hi⟩)
    · exact Or.inl h1.symm
    · exact Or.inr ⟨i, hi⟩
  · rintro (h1 | ⟨i, hi⟩)
    · exact Or.inl h1.symm
    · exact Or.inr ⟨i, hi⟩

theorem scnt_eq : ∀ (k j : ℕ) (used : Finset (Fin j)) (Q : (Fin k → Fin j) → Bool),
    scnt k j used Q = (Finset.univ.filter
      (fun h : Fin k → Fin j => used ∪ Finset.univ.image h = Finset.univ ∧ Q h = true)).card
  | 0, j, used, Q => by
    rw [scnt]
    have hu : (Finset.univ : Finset (Fin 0 → Fin j)) = {Fin.elim0} := by
      ext g
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      funext i
      exact i.elim0
    have him : Finset.univ.image (Fin.elim0 : Fin 0 → Fin j) = ∅ := by simp
    rw [hu, Finset.filter_singleton, him, Finset.union_empty]
    split_ifs <;> simp_all
  | k + 1, j, used, Q => by
    rw [scnt]
    split_ifs with hlt
    · symm
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro g - ⟨hcov, -⟩
      have h1 : Finset.univ \ used ⊆ Finset.univ.image g := by
        intro y hy
        have hy' : y ∈ used ∪ Finset.univ.image g := by rw [hcov]; exact Finset.mem_univ y
        rcases Finset.mem_union.1 hy' with h | h
        · exact absurd h (Finset.mem_sdiff.1 hy).2
        · exact h
      have h2 := Finset.card_le_card h1
      have h3 : (Finset.univ.image g).card ≤ k + 1 := by
        calc (Finset.univ.image g).card ≤ (Finset.univ : Finset (Fin (k + 1))).card :=
              Finset.card_image_le
          _ = k + 1 := by simp
      omega
    · rw [card_by_head]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [scnt_eq k j (insert v used) _]
      congr 1
      ext h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, image_cons, Finset.union_insert,
        Finset.insert_union]

theorem pc_eq_scnt {k : ℕ} (P : (Fin k → ℕ) → Prop) [DecidablePred P] (j : ℕ)
    (T : (Fin k → Fin j) → Bool) (hT : ∀ g, T g = true ↔ P (fun i => (g i : ℕ))) :
    pc P j = scnt k j ∅ T := by
  rw [scnt_eq]
  unfold pc
  congr 1
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.empty_union, hT]
  constructor
  · rintro ⟨hs, hp⟩
    refine ⟨?_, hp⟩
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    exact hs y
  · rintro ⟨hs, hp⟩
    refine ⟨fun y => ?_, hp⟩
    have hy : y ∈ Finset.univ.image g := by rw [hs]; exact Finset.mem_univ y
    simpa using hy

end SCount

/-- A Bool copy of `good`. -/
def goodB (x : Fin 6 → ℕ) : Bool := decide (good x)

lemma good_iff (x : Fin 6 → ℕ) : good x ↔ goodB x = true := by
  simp [goodB]

/-- The test of one pattern with values in Fin j. -/
def tst (j : ℕ) (g : Fin 6 → Fin j) : Bool := goodB (fun i => (g i : ℕ))

section SCountB

/-! scnt with the set of used values kept as a bit mask, together with the number of values still
missing; the kernel evaluates these with machine arithmetic. -/

/-- The bit mask `mask` lists the members of S. -/
def Rep {j : ℕ} (mask : ℕ) (S : Finset (Fin j)) : Prop := ∀ v : Fin j, mask.testBit v = decide (v ∈ S)

/-- Adding the value v to a (mask, missing count) pair. -/
def insM {j : ℕ} (p : ℕ × ℕ) (v : Fin j) : ℕ × ℕ :=
  (p.1 ||| 2 ^ (v : ℕ), if p.1.testBit v then p.2 else p.2 - 1)

lemma rep_insM {j : ℕ} {p : ℕ × ℕ} {S : Finset (Fin j)} (hr : Rep p.1 S)
    (hm : p.2 = (Finset.univ \ S).card) (v : Fin j) :
    Rep (insM p v).1 (insert v S) ∧ (insM p v).2 = (Finset.univ \ insert v S).card := by
  constructor
  · intro u
    simp only [insM, Nat.testBit_or, hr u, Nat.testBit_two_pow, Finset.mem_insert]
    by_cases h : u = v
    · subst h
      simp
    · have h' : (v : ℕ) ≠ u := fun e => h (Fin.ext e.symm)
      simp [h, h']
  · simp only [insM, hr v]
    by_cases h : v ∈ S
    · simp [h, Finset.insert_eq_of_mem h, hm]
    · have hv : v ∈ Finset.univ \ S := by simp [h]
      have e : Finset.univ \ insert v S = (Finset.univ \ S).erase v := by
        ext u
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, not_or,
          Finset.mem_erase]
      simp [h, hm, e, Finset.card_erase_of_mem hv]

lemma rep_zero {j : ℕ} : Rep 0 (∅ : Finset (Fin j)) := fun v => by simp

def scntB : (k j : ℕ) → ℕ × ℕ → ((Fin k → Fin j) → Bool) → ℕ
  | 0, _, p, Q => if p.2 = 0 ∧ Q Fin.elim0 = true then 1 else 0
  | k + 1, j, p, Q =>
      if k + 1 < p.2 then 0
      else ∑ v : Fin j, scntB k j (insM p v) (fun h => Q (Fin.cons v h))

theorem scntB_eq : ∀ (k j : ℕ) (p : ℕ × ℕ) (S : Finset (Fin j)) (Q : (Fin k → Fin j) → Bool),
    Rep p.1 S → p.2 = (Finset.univ \ S).card → scntB k j p Q = scnt k j S Q
  | 0, j, p, S, Q, _, hm => by
    rw [scntB, scnt, hm]
    have e : (Finset.univ \ S).card = 0 ↔ S = Finset.univ := by
      rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset, Finset.univ_subset_iff]
    simp only [e]
  | k + 1, j, p, S, Q, hr, hm => by
    rw [scntB, scnt, hm]
    split_ifs
    · rfl
    · refine Finset.sum_congr rfl (fun v _ => ?_)
      obtain ⟨hr', hm'⟩ := rep_insM hr hm v
      exact scntB_eq k j _ _ _ hr' hm'

end SCountB

lemma pc_tst (j : ℕ) : pc good j = scntB 6 j ((0 : ℕ), j) (tst j) :=
  (pc_eq_scnt good j (tst j) (fun g => (good_iff _).symm)).trans
    (scntB_eq 6 j _ ∅ (tst j) rep_zero (by simp)).symm

/-- The patterns onto Fin j with first value v. -/
def sc (j : ℕ) (v : Fin j) : ℕ :=
  scntB 5 j (insM ((0 : ℕ), j) v) (fun h => tst j (Fin.cons v h))

lemma scnt_split (j : ℕ) (hj : ¬ 5 + 1 < ((0 : ℕ), j).2) :
    scntB 6 j ((0 : ℕ), j) (tst j) = ∑ v : Fin j, sc j v := by
  rw [scntB, if_neg hj]
  rfl

lemma sum_fin4 (f : Fin 4 → ℕ) (n0 n1 n2 n3 : ℕ) (h0 : f 0 = n0) (h1 : f 1 = n1) (h2 : f 2 = n2) (h3
    : f 3 = n3) : ∑ v, f v = n0 + n1 + n2 + n3 := by
  rw [Fin.sum_univ_four, h0, h1, h2, h3]

lemma sum_fin5 (f : Fin 5 → ℕ) (n0 n1 n2 n3 n4 : ℕ) (h0 : f 0 = n0) (h1 : f 1 = n1) (h2 : f 2 = n2)
    (h3 : f 3 = n3) (h4 : f 4 = n4) : ∑ v, f v = n0 + n1 + n2 + n3 + n4 := by
  rw [Fin.sum_univ_five, h0, h1, h2, h3, h4]

lemma sum_fin6 (f : Fin 6 → ℕ) (n0 n1 n2 n3 n4 n5 : ℕ) (h0 : f 0 = n0) (h1 : f 1 = n1) (h2 : f 2 =
    n2) (h3 : f 3 = n3) (h4 : f 4 = n4) (h5 : f 5 = n5) : ∑ v, f v = n0 + n1 + n2 + n3 + n4 + n5 :=
    by
  rw [Fin.sum_univ_six, h0, h1, h2, h3, h4, h5]

lemma pc0 : pc good 0 = 0 := by
  rw [pc_tst]
  decide +kernel

lemma pc1 : pc good 1 = 1 := by
  rw [pc_tst]
  decide +kernel

lemma pc2 : pc good 2 = 25 := by
  rw [pc_tst]
  decide +kernel

lemma pc3 : pc good 3 = 105 := by
  rw [pc_tst]
  decide +kernel

lemma r4_0 : sc 4 0 = 15 := by
  decide +kernel

lemma r4_1 : sc 4 1 = 20 := by
  decide +kernel

lemma r4_2 : sc 4 2 = 40 := by
  decide +kernel

lemma r4_3 : sc 4 3 = 87 := by
  decide +kernel

lemma pc4 : pc good 4 = 162 := by
  rw [pc_tst, scnt_split 4 (by decide), sum_fin4 (sc 4) _ _ _ _ r4_0 r4_1 r4_2 r4_3]

lemma r5_0 : sc 5 0 = 5 := by
  decide +kernel

lemma r5_1 : sc 5 1 = 6 := by
  decide +kernel

lemma r5_2 : sc 5 2 = 13 := by
  decide +kernel

lemma r5_3 : sc 5 3 = 28 := by
  decide +kernel

lemma r5_4 : sc 5 4 = 60 := by
  decide +kernel

lemma pc5 : pc good 5 = 112 := by
  rw [pc_tst, scnt_split 5 (by decide), sum_fin5 (sc 5) _ _ _ _ _ r5_0 r5_1 r5_2 r5_3 r5_4]

lemma r6_0 : sc 6 0 = 1 := by
  decide +kernel

lemma r6_1 : sc 6 1 = 1 := by
  decide +kernel

lemma r6_2 : sc 6 2 = 2 := by
  decide +kernel

lemma r6_3 : sc 6 3 = 4 := by
  decide +kernel

lemma r6_4 : sc 6 4 = 8 := by
  decide +kernel

lemma r6_5 : sc 6 5 = 16 := by
  decide +kernel

lemma pc6 : pc good 6 = 32 := by
  rw [pc_tst, scnt_split 6 (by decide), sum_fin6 (sc 6) _ _ _ _ _ _ r6_0 r6_1 r6_2 r6_3 r6_4 r6_5]

lemma pcv : pc good 0 = 0 ∧ pc good 1 = 1 ∧ pc good 2 = 25 ∧ pc good 3 = 105 ∧ pc good 4 = 162 ∧ pc
    good 5 = 112 ∧ pc good 6 = 32 :=
  ⟨pc0, pc1, pc2, pc3, pc4, pc5, pc6⟩

/-- The closed form a(n) = Sum_j c_j binomial(n+1, j). -/
lemma a_eq (n : ℕ) : (a n : ℚ) =
    1 * (n + 1) + 25 * ((n + 1) * n / 2) + 105 * ((n + 1) * n * (n - 1) / 6) + 162 * ((n + 1) * n * (n - 1) * (n - 2) / 24) + 112 * ((n + 1) * n * (n - 1) * (n - 2) * (n - 3) / 120) + 32 * ((n + 1) * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) / 720) := by
  have h := count_eq hP n
  rw [a_eq_b]
  unfold b
  rw [h]
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := pcv
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, p0, p1, p2, p3, p4, p5, p6]
  push_cast
  simp only [ch2, ch3, ch4, ch5, ch6]
  simp
  ring

lemma values : a 1 = 27 ∧ a 2 = 183 ∧ a 3 = 736 ∧ a 4 = 2227 ∧ a 5 = 5615 ∧ a 6 = 12453 ∧ a 7 = 25096 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [← Nat.cast_inj (R := ℚ), a_eq]
    norm_num

/-- Barker's recurrence, for n > 7. -/
theorem recurrence (n : ℕ) (hn : 7 < n) :
    (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 8 := ⟨n - 8, by omega⟩
  simp only [show q + 8 - 1 = q + 7 by omega, show q + 8 - 2 = q + 6 by omega, show q + 8 - 3 = q +
    5 by omega, show q + 8 - 4 = q + 4 by omega, show q + 8 - 5 = q + 3 by omega, show q + 8 - 6 =
    q + 2 by omega, show q + 8 - 7 = q + 1 by omega]
  have h : (a (q + 8) : ℚ) = 7 * a (q + 7) - 21 * a (q + 6) + 35 * a (q + 5) - 35 * a (q + 4) + 21 * a (q + 3) - 7 * a (q + 2) + a (q + 1) := by
    rw [a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq]
    push_cast
    ring
  exact_mod_cast h

/-- Barker's g.f., as A(x) (1 - x)^7 = N(x) in Z[[x]]. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 7 =
    X * (27 - 6 * X + 22 * X ^ 2 - 27 * X ^ 3 + 22 * X ^ 4 - 7 * X ^ 5 + X ^ 6) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 7 =
      A - C 7 * (A * X ^ 1) + C 21 * (A * X ^ 2) - C 35 * (A * X ^ 3) + C 35 * (A * X ^ 4) - C 21 *
        (A * X ^ 5) + C 7 * (A * X ^ 6) - A * X ^ 7 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (27 - 6 * X + 22 * X ^ 2 - 27 * X ^ 3 + 22 * X ^ 4 - 7 * X ^ 5 + X ^ 6) : ℤ⟦X⟧) =
      X ^ 1 * C 27 - X ^ 2 * C 6 + X ^ 3 * C 22 - X ^ 4 * C 27 + X ^ 5 * C 22 - X ^ 6 * C 7 + X ^ 7
        := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  have v := values
  rcases Nat.lt_or_ge n 8 with hn | hn
  · interval_cases n <;> simp_all
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 8 := ⟨n - 8, by omega⟩
    have h := recurrence (q + 8) (by omega)
    simp only [show q + 8 - 1 = q + 7 by omega, show q + 8 - 2 = q + 6 by omega, show q + 8 - 3 =
      q + 5 by omega, show q + 8 - 4 = q + 4 by omega, show q + 8 - 5 = q + 3 by omega, show q + 8 -
      6 = q + 2 by omega, show q + 8 - 7 = q + 1 by omega] at h ⊢
    simp only [show ¬ q + 8 = 0 by omega, show ¬ q + 7 = 0 by omega, show ¬ q + 6 = 0 by omega, show
      ¬ q + 5 = 0 by omega, show ¬ q + 4 = 0 by omega, show ¬ q + 3 = 0 by omega, show ¬ q + 2 = 0
      by omega, show ¬ q + 1 = 0 by omega, show 1 ≤ q + 8 by omega, show 2 ≤ q + 8 by omega, show 3
      ≤ q + 8 by omega, show 4 ≤ q + 8 by omega, show 5 ≤ q + 8 by omega, show 6 ≤ q + 8 by omega,
      show 7 ≤ q + 8 by omega, show ¬ q + 8 = 1 by omega, show ¬ q + 8 = 2 by omega, show ¬ q + 8 =
      3 by omega, show ¬ q + 8 = 4 by omega, show ¬ q + 8 = 5 by omega, show ¬ q + 8 = 6 by omega,
      show ¬ q + 8 = 7 by omega, if_true, if_false]
    rw [h]
    ring

/-- Hardin's empirical formula, for all n. -/
theorem empirical (n : ℕ) : (a n : ℚ) = (2 / 45) * n ^ 6 + (8 / 15) * n ^ 5 + (115 / 36) * n ^ 4 + 8 * n ^ 3 + (1667 / 180) * n ^ 2 + (149 / 30) * n + 1 := by
  rw [a_eq]
  ring

/-- Controls: the entry's data a(1..29). -/
theorem controls : a 1 = 27 ∧ a 2 = 183 ∧ a 3 = 736 ∧ a 4 = 2227 ∧ a 5 = 5615 ∧ a 6 = 12453 ∧
    a 7 = 25096 ∧ a 8 = 46941 ∧ a 9 = 82699 ∧ a 10 = 138699 ∧ a 11 = 223224 ∧ a 12 = 346879 ∧
    a 13 = 522991 ∧ a 14 = 768041 ∧ a 15 = 1102128 ∧ a 16 = 1549465 ∧ a 17 = 2138907 ∧
    a 18 = 2904511 ∧ a 19 = 3886128 ∧ a 20 = 5130027 ∧ a 21 = 6689551 ∧ a 22 = 8625805 ∧
    a 23 = 11008376 ∧ a 24 = 13916085 ∧ a 25 = 17437771 ∧ a 26 = 21673107 ∧ a 27 = 26733448 ∧
    a 28 = 32742711 ∧ a 29 = 39838287 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [← Nat.cast_inj (R := ℚ), a_eq]
    norm_num

/-- Both of Barker's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 7 < n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 7 =
      X * (27 - 6 * X + 22 * X ^ 2 - 27 * X ^ 3 + 22 * X ^ 4 - 7 * X ^ 5 + X ^ 6) :=
  ⟨recurrence, gf⟩

end OMA.S_oeis_a228463

theorem OMA.solution : type_of% @OMA.S_oeis_a228463.main :=
  OMA.S_oeis_a228463.conjecture
