import OMAStatements.S_oeis_a269413

namespace OMA.S_oeis_a269413

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

lemma ch7 (n : ℕ) : ((n + 1).choose 7 : ℚ) = (n + 1) * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) / 5040 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ m ih =>
    have h : (m + 1 + 1).choose 7 = (m + 1).choose 6 + (m + 1).choose 7 :=
      Nat.choose_succ_succ' (m + 1) 6
    rw [h, Nat.cast_add, ih, ch6]
    push_cast
    ring

section RepCount

/-- The order-only property is invariant under an injective, strictly monotone relabeling. -/
lemma repsL_map {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) : ∀ l : List α, repsL (l.map f) = (repsL l).map f
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
    have ih := repsL_map f hf (b :: t)
    simp only [List.map_cons] at ih ⊢
    by_cases h : a = b
    · subst h
      simp only [repsL, if_true, List.map_cons, ih]
    · have h' : f a ≠ f b := fun e => h (hf e)
      simp only [repsL, if_neg h, if_neg h', ih]

lemma mem_repsL {α : Type*} [DecidableEq α] : ∀ (l : List α) (y : α), y ∈ repsL l → y ∈ l
  | [], _, h => by simp [repsL] at h
  | [_], _, h => by simp [repsL] at h
  | a :: b :: t, y, h => by
    by_cases hab : a = b
    · simp only [repsL, if_pos hab, List.mem_cons] at h
      rcases h with h | h
      · simp [h]
      · exact List.mem_cons_of_mem _ (mem_repsL (b :: t) y h)
    · simp only [repsL, if_neg hab] at h
      exact List.mem_cons_of_mem _ (mem_repsL (b :: t) y h)

/-- okR p r l: after an entry p and a last repeated value r, the repeated values of p :: l keep
strictly decreasing. -/
def okR : ℕ → ℕ → List ℕ → Bool
  | _, _, [] => true
  | p, r, v :: t => if v = p then (decide (v < r) && okR v v t) else okR v r t

lemma okR_iff : ∀ (l : List ℕ) (p r : ℕ),
    okR p r l = true ↔ (r :: repsL (p :: l)).IsChain (· > ·)
  | [], p, r => by simp [okR, repsL]
  | v :: t, p, r => by
    have ih := okR_iff t
    by_cases h : v = p
    · subst h
      simp only [okR, if_true, repsL, Bool.and_eq_true, decide_eq_true_eq, ih, List.isChain_cons_cons,
        gt_iff_lt]
    · have h' : p ≠ v := fun e => h e.symm
      simp only [okR, if_neg h, repsL, if_neg h', ih]

/-- The number of sequences h : Fin L → Fin N continuing an entry p with last repeated value r
(r = N for none yet) that pass okR. The kernel evaluates each value once. -/
def dpR (N : ℕ) : (L : ℕ) → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | L + 1, p, r => ∑ v : Fin N,
      if (v : ℕ) = p then (if (v : ℕ) < r then dpR N L v v else 0) else dpR N L v r

theorem dpR_eq (N : ℕ) : ∀ (L p r : ℕ), dpR N L p r =
    (Finset.univ.filter (fun h : Fin L → Fin N => okR p r (List.ofFn (fun i => (h i : ℕ))) = true)).card
  | 0, p, r => by
    rw [dpR]
    have hu : (Finset.univ : Finset (Fin 0 → Fin N)) = {Fin.elim0} := by
      ext g
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      funext i
      exact i.elim0
    rw [hu, Finset.filter_singleton]
    simp [okR]
  | L + 1, p, r => by
    rw [dpR, card_by_head]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have e : ∀ h : Fin L → Fin N, List.ofFn (fun i => ((Fin.cons v h : Fin (L + 1) → Fin N) i : ℕ)) =
        (v : ℕ) :: List.ofFn (fun i => (h i : ℕ)) := fun h => by
      rw [List.ofFn_succ]
      simp
    by_cases hv : (v : ℕ) = p
    · rw [if_pos hv]
      by_cases hr : (v : ℕ) < r
      · rw [if_pos hr, dpR_eq N L v v]
        congr 1
        ext h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, e, okR, if_pos hv, hr,
          decide_true, Bool.true_and]
      · rw [if_neg hr]
        symm
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro h _ hc
        simp only [e, okR, if_pos hv, Bool.and_eq_true, decide_eq_true_eq] at hc
        exact hr hc.1
    · rw [if_neg hv, dpR_eq N L v r]
      congr 1
      ext h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, e, okR, if_neg hv]

/-- The arrays whose repeated values strictly decrease, through dpR, split by the first entry. -/
theorem count_eq_dpR (k n : ℕ) :
    (Finset.univ.filter (fun x : Fin (k + 1) → Fin (n + 1) =>
      (repsL (List.ofFn (fun i => (x i : ℕ)))).IsChain (· > ·))).card =
      ∑ v : Fin (n + 1), dpR (n + 1) k v (n + 1) := by
  rw [card_by_head]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [dpR_eq]
  congr 1
  ext h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [List.ofFn_succ, okR_iff]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have hlt : ∀ y ∈ repsL ((v : ℕ) :: List.ofFn (fun i => (h i : ℕ))), y < n + 1 := by
    intro y hy
    have := mem_repsL _ y hy
    simp only [List.mem_cons, List.mem_ofFn] at this
    rcases this with rfl | ⟨i, rfl⟩
    · exact v.isLt
    · exact (h i).isLt
  rw [List.isChain_cons]
  constructor
  · intro hc
    exact ⟨fun y hy => hlt y (List.mem_of_mem_head? hy), hc⟩
  · exact fun hc => hc.2

end RepCount

lemma hP : ∀ (m : ℕ) (e₁ e₂ : Fin m ↪o ℕ) (g : Fin 7 → Fin m),
    good (fun i => e₁ (g i)) ↔ good (fun i => e₂ (g i)) := by
  intro m e₁ e₂ g
  have key : ∀ e : Fin m ↪o ℕ, good (fun i => e (g i)) ↔ (repsL (List.ofFn g)).IsChain (· > ·) := by
    intro e
    unfold good
    rw [show List.ofFn (fun i => e (g i)) = (List.ofFn g).map e by rw [List.map_ofFn]; rfl,
      repsL_map e e.injective, List.isChain_map]
    simp only [gt_iff_lt, OrderEmbedding.lt_iff_lt]
  rw [key e₁, key e₂]

lemma av0 : a 0 = 0 := by
  unfold a good
  show (Finset.univ.filter (fun x : Fin (6 + 1) → Fin (0 + 1) =>
    (repsL (List.ofFn (fun i => (x i : ℕ)))).IsChain (· > ·))).card = 0
  rw [count_eq_dpR 6 0]
  decide +kernel

lemma av1 : a 1 = 20 := by
  unfold a good
  show (Finset.univ.filter (fun x : Fin (6 + 1) → Fin (1 + 1) =>
    (repsL (List.ofFn (fun i => (x i : ℕ)))).IsChain (· > ·))).card = 20
  rw [count_eq_dpR 6 1]
  decide +kernel

lemma av2 : a 2 = 957 := by
  unfold a good
  show (Finset.univ.filter (fun x : Fin (6 + 1) → Fin (2 + 1) =>
    (repsL (List.ofFn (fun i => (x i : ℕ)))).IsChain (· > ·))).card = 957
  rw [count_eq_dpR 6 2]
  decide +kernel

lemma av3 : a 3 = 10132 := by
  unfold a good
  show (Finset.univ.filter (fun x : Fin (6 + 1) → Fin (3 + 1) =>
    (repsL (List.ofFn (fun i => (x i : ℕ)))).IsChain (· > ·))).card = 10132
  rw [count_eq_dpR 6 3]
  decide +kernel

lemma av4 : a 4 = 56890 := by
  unfold a good
  show (Finset.univ.filter (fun x : Fin (6 + 1) → Fin (4 + 1) =>
    (repsL (List.ofFn (fun i => (x i : ℕ)))).IsChain (· > ·))).card = 56890
  rw [count_eq_dpR 6 4]
  decide +kernel

lemma av5 : a 5 = 223320 := by
  unfold a good
  show (Finset.univ.filter (fun x : Fin (6 + 1) → Fin (5 + 1) =>
    (repsL (List.ofFn (fun i => (x i : ℕ)))).IsChain (· > ·))).card = 223320
  rw [count_eq_dpR 6 5]
  decide +kernel

lemma av6 : a 6 = 695135 := by
  unfold a good
  show (Finset.univ.filter (fun x : Fin (6 + 1) → Fin (6 + 1) =>
    (repsL (List.ofFn (fun i => (x i : ℕ)))).IsChain (· > ·))).card = 695135
  rw [count_eq_dpR 6 6]
  decide +kernel

lemma pc0 : pc good 0 = 0 := by
  decide +kernel

/-- Solving count_eq at n = 0..k-1 for the pattern counts, with the counts as variables. -/
lemma lin (p : ℕ → ℕ) (h0 : p 0 = 0) (e0 : 0 = ∑ j ∈ Finset.range (7 + 1), (0 + 1).choose j * p j)
    (e1 : 20 = ∑ j ∈ Finset.range (7 + 1), (1 + 1).choose j * p j) (e2 : 957 = ∑ j ∈ Finset.range
    (7 + 1), (2 + 1).choose j * p j) (e3 : 10132 = ∑ j ∈ Finset.range (7 + 1), (3 + 1).choose j * p
    j) (e4 : 56890 = ∑ j ∈ Finset.range (7 + 1), (4 + 1).choose j * p j) (e5 : 223320 = ∑ j ∈
    Finset.range (7 + 1), (5 + 1).choose j * p j) (e6 : 695135 = ∑ j ∈ Finset.range (7 + 1), (6 +
    1).choose j * p j) : p 0 = 0 ∧ p 1 = 0 ∧ p 2 = 20 ∧ p 3 = 897 ∧ p 4 = 6424 ∧ p 5 = 15600 ∧ p 6 =
    15120 ∧ p 7 = 5040 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at e0 e1 e2 e3 e4 e5 e6
  norm_num [Nat.choose] at e0 e1 e2 e3 e4 e5 e6
  omega

lemma pcv : pc good 0 = 0 ∧ pc good 1 = 0 ∧ pc good 2 = 20 ∧ pc good 3 = 897 ∧ pc good 4 = 6424 ∧ pc
    good 5 = 15600 ∧ pc good 6 = 15120 ∧ pc good 7 = 5040 :=
  lin (pc good) pc0 (av0.symm.trans (count_eq hP 0)) (av1.symm.trans (count_eq hP 1))
    (av2.symm.trans (count_eq hP 2)) (av3.symm.trans (count_eq hP 3)) (av4.symm.trans (count_eq hP
    4)) (av5.symm.trans (count_eq hP 5)) (av6.symm.trans (count_eq hP 6))

/-- The closed form a(n) = Sum_j c_j binomial(n+1, j). -/
lemma a_eq (n : ℕ) : (a n : ℚ) =
    20 * ((n + 1) * n / 2) + 897 * ((n + 1) * n * (n - 1) / 6) + 6424 * ((n + 1) * n * (n - 1) * (n - 2) / 24) + 15600 * ((n + 1) * n * (n - 1) * (n - 2) * (n - 3) / 120) + 15120 * ((n + 1) * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) / 720) + 5040 * ((n + 1) * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) / 5040) := by
  have h := count_eq hP n
  unfold a
  rw [h]
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := pcv
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, p0, p1, p2, p3, p4, p5, p6, p7]
  push_cast
  simp only [ch2, ch3, ch4, ch5, ch6, ch7]
  simp
  ring

lemma values : a 1 = 20 ∧ a 2 = 957 ∧ a 3 = 10132 ∧ a 4 = 56890 ∧ a 5 = 223320 ∧ a 6 = 695135 ∧ a 7 = 1837752 ∧ a 8 = 4302612 := by
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
    X * (20 + 797 * X + 3036 * X ^ 2 + 1510 * X ^ 3 - 296 * X ^ 4 - 27 * X ^ 5) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 8 =
      A - C 8 * (A * X ^ 1) + C 28 * (A * X ^ 2) - C 56 * (A * X ^ 3) + C 70 * (A * X ^ 4) - C 56 *
        (A * X ^ 5) + C 28 * (A * X ^ 6) - C 8 * (A * X ^ 7) + A * X ^ 8 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (20 + 797 * X + 3036 * X ^ 2 + 1510 * X ^ 3 - 296 * X ^ 4 - 27 * X ^ 5) : ℤ⟦X⟧) =
      X ^ 1 * C 20 + X ^ 2 * C 797 + X ^ 3 * C 3036 + X ^ 4 * C 1510 - X ^ 5 * C 296 - X ^ 6 * C 27
        := by
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
      q + 9 = 5 by omega, show ¬ q + 9 = 6 by omega, if_true, if_false]
    rw [h]
    ring

/-- Hardin's empirical formula, for all n. -/
theorem empirical (n : ℕ) : (a n : ℚ) = n ^ 7 + 7 * n ^ 6 + 11 * n ^ 5 + (8 / 3) * n ^ 4 - (11 / 6) * n ^ 3 + (1 / 3) * n ^ 2 - (1 / 6) * n := by
  rw [a_eq]
  ring

/-- Controls: the entry's data a(1..23). -/
theorem controls : a 1 = 20 ∧ a 2 = 957 ∧ a 3 = 10132 ∧ a 4 = 56890 ∧ a 5 = 223320 ∧ a 6 = 695135 ∧
    a 7 = 1837752 ∧ a 8 = 4302612 ∧ a 9 = 9168780 ∧ a 10 = 18124865 ∧ a 11 = 33696300 ∧
    a 12 = 59523022 ∧ a 13 = 100692592 ∧ a 14 = 164133795 ∧ a 15 = 259075760 ∧ a 16 = 397577640 ∧
    a 17 = 595133892 ∧ a 18 = 871360197 ∧ a 19 = 1250765060 ∧ a 20 = 1763612130 ∧
    a 21 = 2446878280 ∧ a 22 = 3345312487 ∧ a 23 = 4512600552 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩ <;>
  · rw [← Nat.cast_inj (R := ℚ), a_eq]
    norm_num

/-- Both of Barker's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 8 < n →
      (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 8 =
      X * (20 + 797 * X + 3036 * X ^ 2 + 1510 * X ^ 3 - 296 * X ^ 4 - 27 * X ^ 5) :=
  ⟨recurrence, gf⟩

end OMA.S_oeis_a269413

theorem OMA.solution : type_of% @OMA.S_oeis_a269413.main :=
  OMA.S_oeis_a269413.conjecture
