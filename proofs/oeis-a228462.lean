import OMAStatements.S_oeis_a228462

namespace OMA.S_oeis_a228462

open PowerSeries



/-- The largest array whose maxima of three adjacent elements are at most Y: entry j is the
minimum of the Y i over the windows i that contain j. -/
def XS (Y : Fin 5 → ℕ) : Fin 7 → ℕ := ![Y 0, min (Y 0) (Y 1), min (Y 0) (min (Y 1) (Y 2)), min (Y 1) (min (Y 2) (Y 3)), min (Y 2) (min (Y 3) (Y 4)), min (Y 3) (Y 4), Y 4]

/-- y is the array of maxima of XS y (written out). -/
def good (y : Fin 5 → ℕ) : Prop :=
  max (y 0) (max (min (y 0) (y 1)) (min (y 0) (min (y 1) (y 2)))) = y 0 ∧
    max (min (y 0) (y 1)) (max (min (y 0) (min (y 1) (y 2))) (min (y 1) (min (y 2) (y 3)))) = y 1 ∧
    max (min (y 0) (min (y 1) (y 2))) (max (min (y 1) (min (y 2) (y 3))) (min (y 2) (min (y 3) (y 4)))) = y 2 ∧
    max (min (y 1) (min (y 2) (y 3))) (max (min (y 2) (min (y 3) (y 4))) (min (y 3) (y 4))) = y 3 ∧
    max (min (y 2) (min (y 3) (y 4))) (max (min (y 3) (y 4)) (y 4)) = y 4

instance : DecidablePred good := fun x => by unfold good; infer_instance

/-- The count of the arrays with property `good`. -/
def b (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun y : Fin 5 → Fin (n + 1) => good (fun i => (y i : ℕ)))).card

/-- Every maxima array satisfies `good` (written out for y k = max (x k) (max (x (k+1))
(x (k+2)))): each x j is at most every y i whose window contains j, hence at most XS y j. -/
lemma core (x0 x1 x2 x3 x4 x5 x6 : ℕ) :
    max ((max x0 (max x1 x2))) (max (min ((max x0 (max x1 x2))) ((max x1 (max x2 x3)))) (min ((max x0 (max x1 x2))) (min ((max x1 (max x2 x3))) ((max x2 (max x3 x4)))))) = (max x0 (max x1 x2)) ∧
    max (min ((max x0 (max x1 x2))) ((max x1 (max x2 x3)))) (max (min ((max x0 (max x1 x2))) (min ((max x1 (max x2 x3))) ((max x2 (max x3 x4))))) (min ((max x1 (max x2 x3))) (min ((max x2 (max x3 x4))) ((max x3 (max x4 x5)))))) = (max x1 (max x2 x3)) ∧
    max (min ((max x0 (max x1 x2))) (min ((max x1 (max x2 x3))) ((max x2 (max x3 x4))))) (max (min ((max x1 (max x2 x3))) (min ((max x2 (max x3 x4))) ((max x3 (max x4 x5))))) (min ((max x2 (max x3 x4))) (min ((max x3 (max x4 x5))) ((max x4 (max x5 x6)))))) = (max x2 (max x3 x4)) ∧
    max (min ((max x1 (max x2 x3))) (min ((max x2 (max x3 x4))) ((max x3 (max x4 x5))))) (max (min ((max x2 (max x3 x4))) (min ((max x3 (max x4 x5))) ((max x4 (max x5 x6))))) (min ((max x3 (max x4 x5))) ((max x4 (max x5 x6))))) = (max x3 (max x4 x5)) ∧
    max (min ((max x2 (max x3 x4))) (min ((max x3 (max x4 x5))) ((max x4 (max x5 x6))))) (max (min ((max x3 (max x4 x5))) ((max x4 (max x5 x6)))) ((max x4 (max x5 x6)))) = (max x4 (max x5 x6)) :=
  ⟨le_antisymm (max_le (le_refl _) (max_le (min_le_left _ _) (min_le_left _ _)))
    (max_le_max (le_max_left _ _) (max_le_max (le_min ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _)) (le_min ((le_max_right _ _).trans (le_max_right _ _)) (le_min ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _))))),
   le_antisymm (max_le (min_le_right _ _) (max_le ((min_le_right _ _).trans (min_le_left _ _)) (min_le_left _ _)))
    (max_le_max (le_min ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _)) (max_le_max (le_min ((le_max_right _ _).trans (le_max_right _ _)) (le_min ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _))) (le_min ((le_max_right _ _).trans (le_max_right _ _)) (le_min ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _))))),
   le_antisymm (max_le ((min_le_right _ _).trans (min_le_right _ _)) (max_le ((min_le_right _ _).trans (min_le_left _ _)) (min_le_left _ _)))
    (max_le_max (le_min ((le_max_right _ _).trans (le_max_right _ _)) (le_min ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _))) (max_le_max (le_min ((le_max_right _ _).trans (le_max_right _ _)) (le_min ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _))) (le_min ((le_max_right _ _).trans (le_max_right _ _)) (le_min ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _))))),
   le_antisymm (max_le ((min_le_right _ _).trans (min_le_right _ _)) (max_le ((min_le_right _ _).trans (min_le_left _ _)) (min_le_left _ _)))
    (max_le_max (le_min ((le_max_right _ _).trans (le_max_right _ _)) (le_min ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _))) (max_le_max (le_min ((le_max_right _ _).trans (le_max_right _ _)) (le_min ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _))) (le_min ((le_max_right _ _).trans (le_max_right _ _)) ((le_max_left _ _).trans (le_max_right _ _))))),
   le_antisymm (max_le ((min_le_right _ _).trans (min_le_right _ _)) (max_le (min_le_right _ _) (le_refl _)))
    (max_le_max (le_min ((le_max_right _ _).trans (le_max_right _ _)) (le_min ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _))) (max_le_max (le_min ((le_max_right _ _).trans (le_max_right _ _)) ((le_max_left _ _).trans (le_max_right _ _))) ((le_max_right _ _).trans (le_max_right _ _))))⟩

lemma XS_lt {N : ℕ} (Y : Fin 5 → ℕ) (h : ∀ i, Y i < N) (j : Fin 7) : XS Y j < N := by
  have := h 0
  fin_cases j <;> simp [XS, min_lt_iff, h]

/-- y is a maxima array iff it satisfies `good`. -/
lemma mem_iff {n : ℕ} (y : Fin 5 → Fin (n + 1)) :
    (∃ x : Fin 7 → Fin (n + 1), maxima x = y) ↔ good (fun i => (y i : ℕ)) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact core (x 0 : ℕ) (x 1 : ℕ) (x 2 : ℕ) (x 3 : ℕ) (x 4 : ℕ) (x 5 : ℕ) (x 6 : ℕ)
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
    · show max (min ((y 1 : ℕ)) (min ((y 2 : ℕ)) ((y 3 : ℕ)))) (max (min ((y 2 : ℕ)) (min ((y 3 : ℕ)) ((y 4 : ℕ)))) (min ((y 3 : ℕ)) ((y 4 : ℕ)))) = (y 3 : ℕ)
      exact hg.2.2.2.1
    · show max (min ((y 2 : ℕ)) (min ((y 3 : ℕ)) ((y 4 : ℕ)))) (max (min ((y 3 : ℕ)) ((y 4 : ℕ))) ((y 4 : ℕ))) = (y 4 : ℕ)
      exact hg.2.2.2.2

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

lemma hP : ∀ (m : ℕ) (e₁ e₂ : Fin m ↪o ℕ) (g : Fin 5 → Fin m),
    good (fun i => e₁ (g i)) ↔ good (fun i => e₂ (g i)) := by
  intro m e₁ e₂ g
  simp only [good, ← e₁.monotone.map_max, ← e₁.monotone.map_min, ← e₂.monotone.map_max,
    ← e₂.monotone.map_min, EmbeddingLike.apply_eq_iff_eq]

lemma pc0 : pc good 0 = 0 := by
  decide +kernel

lemma pc1 : pc good 1 = 1 := by
  decide +kernel

lemma pc2 : pc good 2 = 15 := by
  decide +kernel

lemma pc3 : pc good 3 = 43 := by
  decide +kernel

lemma pc4 : pc good 4 = 44 := by
  decide +kernel

lemma pcs0 : pcs good 5 0 = 1 := by
  decide +kernel

lemma pcs1 : pcs good 5 1 = 1 := by
  decide +kernel

lemma pcs2 : pcs good 5 2 = 2 := by
  decide +kernel

lemma pcs3 : pcs good 5 3 = 4 := by
  decide +kernel

lemma pcs4 : pcs good 5 4 = 8 := by
  decide +kernel

lemma pc5 : pc good 5 = 16 := by
  simp only [pc_succ, Fin.sum_univ_five, pcs0, pcs1, pcs2, pcs3, pcs4]

lemma pcv : pc good 0 = 0 ∧ pc good 1 = 1 ∧ pc good 2 = 15 ∧ pc good 3 = 43 ∧ pc good 4 = 44 ∧ pc good 5 = 16 :=
  ⟨pc0, pc1, pc2, pc3, pc4, pc5⟩

/-- The closed form a(n) = Sum_j c_j binomial(n+1, j). -/
lemma a_eq (n : ℕ) : (a n : ℚ) =
    1 * (n + 1) + 15 * ((n + 1) * n / 2) + 43 * ((n + 1) * n * (n - 1) / 6) + 44 * ((n + 1) * n * (n - 1) * (n - 2) / 24) + 16 * ((n + 1) * n * (n - 1) * (n - 2) * (n - 3) / 120) := by
  have h := count_eq hP n
  rw [a_eq_b]
  unfold b
  rw [h]
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := pcv
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, p0, p1, p2, p3, p4, p5]
  push_cast
  simp only [ch2, ch3, ch4, ch5]
  simp
  ring

lemma values : a 1 = 17 ∧ a 2 = 91 ∧ a 3 = 310 ∧ a 4 = 821 ∧ a 5 = 1847 ∧ a 6 = 3703 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [← Nat.cast_inj (R := ℚ), a_eq]
    norm_num

/-- Barker's recurrence, for n > 6. -/
theorem recurrence (n : ℕ) (hn : 6 < n) :
    (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 7 := ⟨n - 7, by omega⟩
  simp only [show q + 7 - 1 = q + 6 by omega, show q + 7 - 2 = q + 5 by omega, show q + 7 - 3 = q +
    4 by omega, show q + 7 - 4 = q + 3 by omega, show q + 7 - 5 = q + 2 by omega, show q + 7 - 6 =
    q + 1 by omega]
  have h : (a (q + 7) : ℚ) = 6 * a (q + 6) - 15 * a (q + 5) + 20 * a (q + 4) - 15 * a (q + 3) + 6 * a (q + 2) - a (q + 1) := by
    rw [a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq]
    push_cast
    ring
  exact_mod_cast h

/-- Barker's g.f., as A(x) (1 - x)^6 = N(x) in Z[[x]]. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
    X * (17 - 11 * X + 19 * X ^ 2 - 14 * X ^ 3 + 6 * X ^ 4 - X ^ 5) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 6 =
      A - C 6 * (A * X ^ 1) + C 15 * (A * X ^ 2) - C 20 * (A * X ^ 3) + C 15 * (A * X ^ 4) - C 6 *
        (A * X ^ 5) + A * X ^ 6 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (17 - 11 * X + 19 * X ^ 2 - 14 * X ^ 3 + 6 * X ^ 4 - X ^ 5) : ℤ⟦X⟧) =
      X ^ 1 * C 17 - X ^ 2 * C 11 + X ^ 3 * C 19 - X ^ 4 * C 14 + X ^ 5 * C 6 - X ^ 6 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  have v := values
  rcases Nat.lt_or_ge n 7 with hn | hn
  · interval_cases n <;> simp_all
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 7 := ⟨n - 7, by omega⟩
    have h := recurrence (q + 7) (by omega)
    simp only [show q + 7 - 1 = q + 6 by omega, show q + 7 - 2 = q + 5 by omega, show q + 7 - 3 =
      q + 4 by omega, show q + 7 - 4 = q + 3 by omega, show q + 7 - 5 = q + 2 by omega, show q + 7 -
      6 = q + 1 by omega] at h ⊢
    simp only [show ¬ q + 7 = 0 by omega, show ¬ q + 6 = 0 by omega, show ¬ q + 5 = 0 by omega, show
      ¬ q + 4 = 0 by omega, show ¬ q + 3 = 0 by omega, show ¬ q + 2 = 0 by omega, show ¬ q + 1 = 0
      by omega, show 1 ≤ q + 7 by omega, show 2 ≤ q + 7 by omega, show 3 ≤ q + 7 by omega, show 4 ≤
      q + 7 by omega, show 5 ≤ q + 7 by omega, show 6 ≤ q + 7 by omega, show ¬ q + 7 = 1 by omega,
      show ¬ q + 7 = 2 by omega, show ¬ q + 7 = 3 by omega, show ¬ q + 7 = 4 by omega, show ¬ q +
      7 = 5 by omega, show ¬ q + 7 = 6 by omega, if_true, if_false]
    rw [h]
    ring

/-- Hardin's empirical formula, for all n. -/
theorem empirical (n : ℕ) : (a n : ℚ) = (2 / 15) * n ^ 5 + (7 / 6) * n ^ 4 + (25 / 6) * n ^ 3 + (19 / 3) * n ^ 2 + (21 / 5) * n + 1 := by
  rw [a_eq]
  ring

/-- Controls: the entry's data a(1..32). -/
theorem controls : a 1 = 17 ∧ a 2 = 91 ∧ a 3 = 310 ∧ a 4 = 821 ∧ a 5 = 1847 ∧ a 6 = 3703 ∧
    a 7 = 6812 ∧ a 8 = 11721 ∧ a 9 = 19117 ∧ a 10 = 29843 ∧ a 11 = 44914 ∧ a 12 = 65533 ∧
    a 13 = 93107 ∧ a 14 = 129263 ∧ a 15 = 175864 ∧ a 16 = 235025 ∧ a 17 = 309129 ∧ a 18 = 400843 ∧
    a 19 = 513134 ∧ a 20 = 649285 ∧ a 21 = 812911 ∧ a 22 = 1007975 ∧ a 23 = 1238804 ∧
    a 24 = 1510105 ∧ a 25 = 1826981 ∧ a 26 = 2194947 ∧ a 27 = 2619946 ∧ a 28 = 3108365 ∧
    a 29 = 3667051 ∧ a 30 = 4303327 ∧ a 31 = 5025008 ∧ a 32 = 5840417 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [← Nat.cast_inj (R := ℚ), a_eq]
    norm_num

/-- Both of Barker's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
      X * (17 - 11 * X + 19 * X ^ 2 - 14 * X ^ 3 + 6 * X ^ 4 - X ^ 5) :=
  ⟨recurrence, gf⟩

end OMA.S_oeis_a228462

theorem OMA.solution : type_of% @OMA.S_oeis_a228462.main :=
  OMA.S_oeis_a228462.conjecture
