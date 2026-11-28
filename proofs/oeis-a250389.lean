import OMAStatements.S_oeis_a250389

namespace OMA.S_oeis_a250389

open PowerSeries





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
  simp only [good, split4, ← e₁.monotone.map_max, ← e₁.monotone.map_min, ← e₂.monotone.map_max,
    ← e₂.monotone.map_min, EmbeddingLike.apply_eq_iff_eq]

section Count

/-- The number of functions Fin k → Fin j on which the test Q is true, by recursion on k. -/
def cnt : (k j : ℕ) → ((Fin k → Fin j) → Bool) → ℕ
  | 0, _, Q => if Q Fin.elim0 then 1 else 0
  | k + 1, j, Q => ∑ v : Fin j, cnt k j (fun h => Q (Fin.cons v h))

theorem card_eq_cnt : ∀ (k j : ℕ) (Q : (Fin k → Fin j) → Bool),
    (Finset.univ.filter (fun g => Q g = true)).card = cnt k j Q
  | 0, j, Q => by
    rw [cnt]
    have hu : (Finset.univ : Finset (Fin 0 → Fin j)) = {Fin.elim0} := by
      ext g
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      funext i
      exact i.elim0
    rw [hu, Finset.filter_singleton]
    split_ifs <;> simp_all
  | k + 1, j, Q => by
    rw [cnt, card_by_head]
    exact Finset.sum_congr rfl (fun v _ => card_eq_cnt k j _)

end Count

/-- A Bool copy of `split4`. -/
def split4B (a b c d : ℕ) : Bool :=
  max a b == min c d || max a c == min b d || max a d == min b c || max b c == min a d || max b d ==
    min a c || max c d == min a b

/-- A Bool copy of `good`. -/
def goodB (x : Fin 6 → ℕ) : Bool :=
  !split4B (x 0) (x 1) (x 2) (x 3) &&
    !split4B (x 1) (x 2) (x 3) (x 4) &&
    !split4B (x 2) (x 3) (x 4) (x 5)

lemma good_iff (x : Fin 6 → ℕ) : good x ↔ goodB x = true := by
  simp [good, goodB, split4, split4B, and_assoc, or_assoc]

/-- The test of one array with entries in 0..j-1. -/
def tst (j : ℕ) (g : Fin 6 → Fin j) : Bool := goodB (fun i => (g i : ℕ))

lemma a_cnt (n : ℕ) : a n = cnt 6 (n + 1) (tst (n + 1)) := by
  rw [← card_eq_cnt]
  unfold a tst
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact good_iff _

/-- The same with j = n + 1 given, so that no defeq check has to evaluate a count. -/
lemma a_cnt' (n j : ℕ) (h : n + 1 = j) : a n = cnt 6 j (tst j) := by
  subst h
  exact a_cnt n

/-- The arrays with entries in 0..j-1 and first entry v. -/
def sub1 (j : ℕ) (v : Fin j) : ℕ := cnt 5 j (fun h => tst j (Fin.cons v h))

lemma cnt_one (j : ℕ) : cnt 6 j (tst j) = ∑ v : Fin j, sub1 j v := rfl

lemma sum_fin4 (f : Fin 4 → ℕ) (n0 n1 n2 n3 : ℕ) (h0 : f 0 = n0) (h1 : f 1 = n1) (h2 : f 2 = n2) (h3
    : f 3 = n3) : ∑ v, f v = n0 + n1 + n2 + n3 := by
  rw [Fin.sum_univ_four, h0, h1, h2, h3]

lemma sum_fin5 (f : Fin 5 → ℕ) (n0 n1 n2 n3 n4 : ℕ) (h0 : f 0 = n0) (h1 : f 1 = n1) (h2 : f 2 = n2)
    (h3 : f 3 = n3) (h4 : f 4 = n4) : ∑ v, f v = n0 + n1 + n2 + n3 + n4 := by
  rw [Fin.sum_univ_five, h0, h1, h2, h3, h4]

lemma av0 : a 0 = 0 := by
  rw [a_cnt' 0 1 rfl]
  decide +kernel

lemma av1 : a 1 = 6 := by
  rw [a_cnt' 1 2 rfl]
  decide +kernel

lemma av2 : a 2 = 146 := by
  rw [a_cnt' 2 3 rfl]
  decide +kernel

lemma s4_0 : sub1 4 0 = 320 := by
  decide +kernel

lemma s4_1 : sub1 4 1 = 284 := by
  decide +kernel

lemma s4_2 : sub1 4 2 = 284 := by
  decide +kernel

lemma s4_3 : sub1 4 3 = 320 := by
  decide +kernel

lemma av3 : a 3 = 1208 := by
  rw [a_cnt' 3 4 rfl, cnt_one, sum_fin4 (sub1 4) _ _ _ _ s4_0 s4_1 s4_2 s4_3]

lemma s5_0 : sub1 5 0 = 1240 := by
  decide +kernel

lemma s5_1 : sub1 5 1 = 1135 := by
  decide +kernel

lemma s5_2 : sub1 5 2 = 1098 := by
  decide +kernel

lemma s5_3 : sub1 5 3 = 1135 := by
  decide +kernel

lemma s5_4 : sub1 5 4 = 1240 := by
  decide +kernel

lemma av4 : a 4 = 5848 := by
  rw [a_cnt' 4 5 rfl, cnt_one, sum_fin5 (sub1 5) _ _ _ _ _ s5_0 s5_1 s5_2 s5_3 s5_4]

lemma pc0 : pc good 0 = 0 := by
  decide +kernel

/-- The surjective maps Fin 6 → Fin 6 are the 720 permutations. -/
lemma card_surj6 : (Finset.univ.filter (fun g : Fin 6 → Fin 6 => Function.Surjective g)).card = 720 := by
  rw [← Fintype.card_subtype]
  have e : {g : Fin 6 → Fin 6 // Function.Surjective g} ≃ Equiv.Perm (Fin 6) :=
    { toFun := fun g => Equiv.ofBijective g.1 ⟨Finite.injective_iff_surjective.2 g.2, g.2⟩
      invFun := fun σ => ⟨σ, σ.surjective⟩
      left_inv := fun g => rfl
      right_inv := fun σ => Equiv.ext fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_perm, Fintype.card_fin]
  rfl

/-- The values of an injective map are pairwise different. -/
lemma val_ne {g : Fin 6 → Fin 6} (hi : Function.Injective g) {a b : Fin 6} (h : a ≠ b) :
    (g a : ℕ) ≠ (g b : ℕ) := fun e => h (hi (Fin.ext e))

/-- Every permutation has the property. -/
lemma good_perm (g : Fin 6 → Fin 6) (hs : Function.Surjective g) :
    good (fun i => (g i : ℕ)) := by
  have hi : Function.Injective g := Finite.injective_iff_surjective.2 hs
  have d01 := val_ne hi (show (0 : Fin 6) ≠ 1 by decide)
  have d02 := val_ne hi (show (0 : Fin 6) ≠ 2 by decide)
  have d03 := val_ne hi (show (0 : Fin 6) ≠ 3 by decide)
  have d04 := val_ne hi (show (0 : Fin 6) ≠ 4 by decide)
  have d05 := val_ne hi (show (0 : Fin 6) ≠ 5 by decide)
  have d12 := val_ne hi (show (1 : Fin 6) ≠ 2 by decide)
  have d13 := val_ne hi (show (1 : Fin 6) ≠ 3 by decide)
  have d14 := val_ne hi (show (1 : Fin 6) ≠ 4 by decide)
  have d15 := val_ne hi (show (1 : Fin 6) ≠ 5 by decide)
  have d23 := val_ne hi (show (2 : Fin 6) ≠ 3 by decide)
  have d24 := val_ne hi (show (2 : Fin 6) ≠ 4 by decide)
  have d25 := val_ne hi (show (2 : Fin 6) ≠ 5 by decide)
  have d34 := val_ne hi (show (3 : Fin 6) ≠ 4 by decide)
  have d35 := val_ne hi (show (3 : Fin 6) ≠ 5 by decide)
  have d45 := val_ne hi (show (4 : Fin 6) ≠ 5 by decide)
  simp only [good, split4]
  omega

lemma pc6 : pc good 6 = 720 := by
  unfold pc
  rw [Finset.filter_congr (fun g _ => and_iff_left_of_imp (good_perm g))]
  exact card_surj6

/-- Solving count_eq at n = 0..4 for the pattern counts, with the counts as variables. -/
lemma lin (p : ℕ → ℕ) (h0 : p 0 = 0) (h6 : p 6 = 720) (e0 : 0 = ∑ j ∈ Finset.range (6 + 1), (0 +
    1).choose j * p j) (e1 : 6 = ∑ j ∈ Finset.range (6 + 1), (1 + 1).choose j * p j) (e2 : 146 = ∑ j
    ∈ Finset.range (6 + 1), (2 + 1).choose j * p j) (e3 : 1208 = ∑ j ∈ Finset.range (6 + 1), (3 +
    1).choose j * p j) (e4 : 5848 = ∑ j ∈ Finset.range (6 + 1), (4 + 1).choose j * p j) : p 0 = 0 ∧
    p 1 = 0 ∧ p 2 = 6 ∧ p 3 = 128 ∧ p 4 = 660 ∧ p 5 = 1208 ∧ p 6 = 720 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at e0 e1 e2 e3 e4
  norm_num [Nat.choose] at e0 e1 e2 e3 e4
  omega

lemma pcv : pc good 0 = 0 ∧ pc good 1 = 0 ∧ pc good 2 = 6 ∧ pc good 3 = 128 ∧ pc good 4 = 660 ∧ pc
    good 5 = 1208 ∧ pc good 6 = 720 :=
  lin (pc good) pc0 pc6 (av0.symm.trans (count_eq hP 0)) (av1.symm.trans (count_eq hP 1))
    (av2.symm.trans (count_eq hP 2)) (av3.symm.trans (count_eq hP 3)) (av4.symm.trans (count_eq hP
    4))

/-- The closed form a(n) = Sum_j c_j binomial(n+1, j). -/
lemma a_eq (n : ℕ) : (a n : ℚ) =
    6 * ((n + 1) * n / 2) + 128 * ((n + 1) * n * (n - 1) / 6) + 660 * ((n + 1) * n * (n - 1) * (n - 2) / 24) + 1208 * ((n + 1) * n * (n - 1) * (n - 2) * (n - 3) / 120) + 720 * ((n + 1) * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) / 720) := by
  have h := count_eq hP n
  unfold a
  rw [h]
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := pcv
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, p0, p1, p2, p3, p4, p5, p6]
  push_cast
  simp only [ch2, ch3, ch4, ch5, ch6]
  simp
  ring

lemma values : a 1 = 6 ∧ a 2 = 146 ∧ a 3 = 1208 ∧ a 4 = 5848 ∧ a 5 = 20518 ∧ a 6 = 58114 ∧ a 7 = 141344 := by
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
    2 * X * (3 + 52 * X + 156 * X ^ 2 + 124 * X ^ 3 + 25 * X ^ 4) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 7 =
      A - C 7 * (A * X ^ 1) + C 21 * (A * X ^ 2) - C 35 * (A * X ^ 3) + C 35 * (A * X ^ 4) - C 21 *
        (A * X ^ 5) + C 7 * (A * X ^ 6) - A * X ^ 7 := by
    simp only [map_ofNat]; ring
  have e2 : (2 * X * (3 + 52 * X + 156 * X ^ 2 + 124 * X ^ 3 + 25 * X ^ 4) : ℤ⟦X⟧) =
      X ^ 1 * C 6 + X ^ 2 * C 104 + X ^ 3 * C 312 + X ^ 4 * C 248 + X ^ 5 * C 50 := by
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
      3 by omega, show ¬ q + 8 = 4 by omega, show ¬ q + 8 = 5 by omega, if_true, if_false]
    rw [h]
    ring

/-- Hardin's empirical formula, for all n. -/
theorem empirical (n : ℕ) : (a n : ℚ) = n ^ 6 + (16 / 15) * n ^ 5 + (13 / 6) * n ^ 4 + (5 / 3) * n ^ 3 - (1 / 6) * n ^ 2 + (4 / 15) * n := by
  rw [a_eq]
  ring

/-- Controls: the entry's data a(1..26). -/
theorem controls : a 1 = 6 ∧ a 2 = 146 ∧ a 3 = 1208 ∧ a 4 = 5848 ∧ a 5 = 20518 ∧ a 6 = 58114 ∧
    a 7 = 141344 ∧ a 8 = 306816 ∧ a 9 = 609846 ∧ a 10 = 1129986 ∧ a 11 = 1977272 ∧ a 12 = 3299192 ∧
    a 13 = 5288374 ∧ a 14 = 8190994 ∧ a 15 = 12315904 ∧ a 16 = 18044480 ∧ a 17 = 25841190 ∧
    a 18 = 36264882 ∧ a 19 = 49980792 ∧ a 20 = 67773272 ∧ a 21 = 90559238 ∧ a 22 = 119402338 ∧
    a 23 = 155527840 ∧ a 24 = 200338240 ∧ a 25 = 255429590 ∧ a 26 = 322608546 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩ <;>
  · rw [← Nat.cast_inj (R := ℚ), a_eq]
    norm_num

/-- Both of Barker's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 7 < n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 7 =
      2 * X * (3 + 52 * X + 156 * X ^ 2 + 124 * X ^ 3 + 25 * X ^ 4) :=
  ⟨recurrence, gf⟩

end OMA.S_oeis_a250389

theorem OMA.solution : type_of% @OMA.S_oeis_a250389.main :=
  OMA.S_oeis_a250389.conjecture
