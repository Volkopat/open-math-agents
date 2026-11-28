import OMAStatements.S_oeis_a254700

namespace OMA.S_oeis_a254700

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
  simp only [good, split5, ← e₁.monotone.map_max, ← e₁.monotone.map_min, ← e₂.monotone.map_max,
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

/-- A Bool copy of `split5`. -/
def split5B (a b c d e : ℕ) : Bool :=
  max a b == min (min c d) e || max a c == min (min b d) e || max a d == min (min b c) e || max a e
    == min (min b c) d || max b c == min (min a d) e || max b d == min (min a c) e || max b e == min
    (min a c) d || max c d == min (min a b) e || max c e == min (min a b) d || max d e == min (min a
    b) c

/-- A Bool copy of `good`. -/
def goodB (x : Fin 6 → ℕ) : Bool :=
  split5B (x 0) (x 1) (x 2) (x 3) (x 4) &&
    split5B (x 1) (x 2) (x 3) (x 4) (x 5)

lemma good_iff (x : Fin 6 → ℕ) : good x ↔ goodB x = true := by
  simp [good, goodB, split5, split5B, and_assoc, or_assoc]

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

lemma av0 : a 0 = 1 := by
  rw [a_cnt' 0 1 rfl]
  decide +kernel

lemma av1 : a 1 = 34 := by
  rw [a_cnt' 1 2 rfl]
  decide +kernel

lemma av2 : a 2 = 267 := by
  rw [a_cnt' 2 3 rfl]
  decide +kernel

lemma s4_0 : sub1 4 0 = 232 := by
  decide +kernel

lemma s4_1 : sub1 4 1 = 310 := by
  decide +kernel

lemma s4_2 : sub1 4 2 = 302 := by
  decide +kernel

lemma s4_3 : sub1 4 3 = 272 := by
  decide +kernel

lemma av3 : a 3 = 1116 := by
  rw [a_cnt' 3 4 rfl, cnt_one, sum_fin4 (sub1 4) _ _ _ _ s4_0 s4_1 s4_2 s4_3]

lemma s5_0 : sub1 5 0 = 525 := by
  decide +kernel

lemma s5_1 : sub1 5 1 = 697 := by
  decide +kernel

lemma s5_2 : sub1 5 2 = 745 := by
  decide +kernel

lemma s5_3 : sub1 5 3 = 709 := by
  decide +kernel

lemma s5_4 : sub1 5 4 = 665 := by
  decide +kernel

lemma av4 : a 4 = 3341 := by
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

/-- No permutation has a split in its first window. -/
lemma pc6 : pc good 6 = 0 := by
  unfold pc
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro g - ⟨hs, hg⟩
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
  simp only [good] at hg
  have h1 := hg.1
  simp only [split5] at h1
  omega

/-- Solving count_eq at n = 0..4 for the pattern counts, with the counts as variables. -/
lemma lin (p : ℕ → ℕ) (h0 : p 0 = 0) (h6 : p 6 = 0) (e0 : 1 = ∑ j ∈ Finset.range (6 + 1), (0 +
    1).choose j * p j) (e1 : 34 = ∑ j ∈ Finset.range (6 + 1), (1 + 1).choose j * p j) (e2 : 267 = ∑
    j ∈ Finset.range (6 + 1), (2 + 1).choose j * p j) (e3 : 1116 = ∑ j ∈ Finset.range (6 + 1), (3 +
    1).choose j * p j) (e4 : 3341 = ∑ j ∈ Finset.range (6 + 1), (4 + 1).choose j * p j) : p 0 = 0 ∧
    p 1 = 1 ∧ p 2 = 32 ∧ p 3 = 168 ∧ p 4 = 248 ∧ p 5 = 96 ∧ p 6 = 0 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at e0 e1 e2 e3 e4
  norm_num [Nat.choose] at e0 e1 e2 e3 e4
  omega

lemma pcv : pc good 0 = 0 ∧ pc good 1 = 1 ∧ pc good 2 = 32 ∧ pc good 3 = 168 ∧ pc good 4 = 248 ∧ pc
    good 5 = 96 ∧ pc good 6 = 0 :=
  lin (pc good) pc0 pc6 (av0.symm.trans (count_eq hP 0)) (av1.symm.trans (count_eq hP 1))
    (av2.symm.trans (count_eq hP 2)) (av3.symm.trans (count_eq hP 3)) (av4.symm.trans (count_eq hP
    4))

/-- The closed form a(n) = Sum_j c_j binomial(n+1, j). -/
lemma a_eq (n : ℕ) : (a n : ℚ) =
    1 * (n + 1) + 32 * ((n + 1) * n / 2) + 168 * ((n + 1) * n * (n - 1) / 6) + 248 * ((n + 1) * n * (n - 1) * (n - 2) / 24) + 96 * ((n + 1) * n * (n - 1) * (n - 2) * (n - 3) / 120) := by
  have h := count_eq hP n
  unfold a
  rw [h]
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := pcv
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, p0, p1, p2, p3, p4, p5, p6]
  push_cast
  simp only [ch2, ch3, ch4, ch5, ch6]
  simp
  ring

lemma values : a 1 = 34 ∧ a 2 = 267 ∧ a 3 = 1116 ∧ a 4 = 3341 ∧ a 5 = 8142 ∧ a 6 = 17255 := by
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
    X * (34 + 63 * X + 24 * X ^ 2 - 30 * X ^ 3 + 6 * X ^ 4 - X ^ 5) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 6 =
      A - C 6 * (A * X ^ 1) + C 15 * (A * X ^ 2) - C 20 * (A * X ^ 3) + C 15 * (A * X ^ 4) - C 6 *
        (A * X ^ 5) + A * X ^ 6 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (34 + 63 * X + 24 * X ^ 2 - 30 * X ^ 3 + 6 * X ^ 4 - X ^ 5) : ℤ⟦X⟧) =
      X ^ 1 * C 34 + X ^ 2 * C 63 + X ^ 3 * C 24 - X ^ 4 * C 30 + X ^ 5 * C 6 - X ^ 6 := by
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
theorem empirical (n : ℕ) : (a n : ℚ) = (4 / 5) * n ^ 5 + (19 / 3) * n ^ 4 + (34 / 3) * n ^ 3 + (29 / 3) * n ^ 2 + (73 / 15) * n + 1 := by
  rw [a_eq]
  ring

/-- Controls: the entry's data a(1..32). -/
theorem controls : a 1 = 34 ∧ a 2 = 267 ∧ a 3 = 1116 ∧ a 4 = 3341 ∧ a 5 = 8142 ∧ a 6 = 17255 ∧
    a 7 = 33048 ∧ a 8 = 58617 ∧ a 9 = 97882 ∧ a 10 = 155683 ∧ a 11 = 237876 ∧ a 12 = 351429 ∧
    a 13 = 504518 ∧ a 14 = 706623 ∧ a 15 = 968624 ∧ a 16 = 1302897 ∧ a 17 = 1723410 ∧
    a 18 = 2245819 ∧ a 19 = 2887564 ∧ a 20 = 3667965 ∧ a 21 = 4608318 ∧ a 22 = 5731991 ∧
    a 23 = 7064520 ∧ a 24 = 8633705 ∧ a 25 = 10469706 ∧ a 26 = 12605139 ∧ a 27 = 15075172 ∧
    a 28 = 17917621 ∧ a 29 = 21173046 ∧ a 30 = 24884847 ∧ a 31 = 29099360 ∧ a 32 = 33865953 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [← Nat.cast_inj (R := ℚ), a_eq]
    norm_num

/-- Both of Barker's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
      X * (34 + 63 * X + 24 * X ^ 2 - 30 * X ^ 3 + 6 * X ^ 4 - X ^ 5) :=
  ⟨recurrence, gf⟩

end OMA.S_oeis_a254700

theorem OMA.solution : type_of% @OMA.S_oeis_a254700.main :=
  OMA.S_oeis_a254700.conjecture
