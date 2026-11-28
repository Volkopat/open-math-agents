import OMAStatements.S_oeis_a250145

namespace OMA.S_oeis_a250145

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

lemma ch8 (n : ℕ) : ((n + 1).choose 8 : ℚ) = (n + 1) * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) * (n - 6) / 40320 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ m ih =>
    have h : (m + 1 + 1).choose 8 = (m + 1).choose 7 + (m + 1).choose 8 :=
      Nat.choose_succ_succ' (m + 1) 7
    rw [h, Nat.cast_add, ih, ch7]
    push_cast
    ring

lemma hP : ∀ (m : ℕ) (e₁ e₂ : Fin m ↪o ℕ) (g : Fin 8 → Fin m),
    good (fun i => e₁ (g i)) ↔ good (fun i => e₂ (g i)) := by
  intro m e₁ e₂ g
  simp only [good, med, ← e₁.monotone.map_max, ← e₁.monotone.map_min, ← e₂.monotone.map_max,
    ← e₂.monotone.map_min, OrderEmbedding.le_iff_le]

section DPCount

/-- The windows (a, b, c), (b, c, d), ... of a list of numbers all pass WN. -/
def wins3 (WN : ℕ → ℕ → ℕ → Bool) : List ℕ → Bool
  | a :: b :: c :: t => WN a b c && wins3 WN (b :: c :: t)
  | _ => true

/-- The windows (a, b, h 0), (b, h 0, h 1), ... of a sequence h continuing a, b all pass WN. -/
def chain3 {N : ℕ} (WN : ℕ → ℕ → ℕ → Bool) : (L : ℕ) → ℕ → ℕ → (Fin L → Fin N) → Bool
  | 0, _, _, _ => true
  | L + 1, a, b, h => WN a b (h 0) && chain3 WN L b (h 0) (Fin.tail h)

lemma chain3_wins {N : ℕ} (WN : ℕ → ℕ → ℕ → Bool) : ∀ (L : ℕ) (a b : ℕ) (h : Fin L → Fin N),
    chain3 WN L a b h = wins3 WN (a :: b :: List.ofFn (fun i => (h i : ℕ)))
  | 0, a, b, h => by simp [chain3, wins3]
  | L + 1, a, b, h => by
    rw [chain3, chain3_wins WN L, List.ofFn_succ, wins3]
    rfl

/-- The number of sequences h : Fin L → Fin N continuing a, b whose windows pass WN. The kernel
evaluates each value dp3 WN N L a b once, so the work is about N^3 L. -/
def dp3 (WN : ℕ → ℕ → ℕ → Bool) (N : ℕ) : (L : ℕ) → Fin N → Fin N → ℕ
  | 0, _, _ => 1
  | L + 1, a, b => ∑ v : Fin N, if WN a b v = true then dp3 WN N L b v else 0

theorem dp3_eq (WN : ℕ → ℕ → ℕ → Bool) (N : ℕ) : ∀ (L : ℕ) (a b : Fin N),
    dp3 WN N L a b = (Finset.univ.filter (fun h : Fin L → Fin N => chain3 WN L a b h = true)).card
  | 0, a, b => by
    rw [dp3]
    have hu : (Finset.univ : Finset (Fin 0 → Fin N)) = {Fin.elim0} := by
      ext g
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      funext i
      exact i.elim0
    rw [hu, Finset.filter_singleton]
    simp [chain3]
  | L + 1, a, b => by
    rw [dp3, card_by_head]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    split_ifs with hW
    · rw [dp3_eq WN N L b v]
      congr 1
      ext h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, chain3, Fin.cons_zero, Fin.tail_cons,
        hW, Bool.true_and]
    · symm
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro h - hc
      simp only [chain3, Fin.cons_zero, Bool.and_eq_true] at hc
      exact hW hc.1

/-- The arrays counted by a window property of three, through dp3, split by the first two
entries. -/
theorem count_eq_dp3 {k : ℕ} (P : (Fin (k + 2) → ℕ) → Prop) [DecidablePred P]
    (WN : ℕ → ℕ → ℕ → Bool) (hP : ∀ x, P x ↔ wins3 WN (List.ofFn x) = true) (n : ℕ) :
    (Finset.univ.filter (fun x : Fin (k + 2) → Fin (n + 1) => P (fun i => (x i : ℕ)))).card =
      ∑ v : Fin (n + 1), ∑ w : Fin (n + 1), dp3 WN (n + 1) k v w := by
  rw [card_by_head]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [card_by_head]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [dp3_eq]
  congr 1
  ext h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hP, chain3_wins, List.ofFn_succ, List.ofFn_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- Windows of four. -/
def wins4 (WN : ℕ → ℕ → ℕ → ℕ → Bool) : List ℕ → Bool
  | a :: b :: c :: d :: t => WN a b c d && wins4 WN (b :: c :: d :: t)
  | _ => true

def chain4 {N : ℕ} (WN : ℕ → ℕ → ℕ → ℕ → Bool) : (L : ℕ) → ℕ → ℕ → ℕ → (Fin L → Fin N) → Bool
  | 0, _, _, _, _ => true
  | L + 1, a, b, c, h => WN a b c (h 0) && chain4 WN L b c (h 0) (Fin.tail h)

lemma chain4_wins {N : ℕ} (WN : ℕ → ℕ → ℕ → ℕ → Bool) :
    ∀ (L : ℕ) (a b c : ℕ) (h : Fin L → Fin N),
    chain4 WN L a b c h = wins4 WN (a :: b :: c :: List.ofFn (fun i => (h i : ℕ)))
  | 0, a, b, c, h => by simp [chain4, wins4]
  | L + 1, a, b, c, h => by
    rw [chain4, chain4_wins WN L, List.ofFn_succ, wins4]
    rfl

def dp4 (WN : ℕ → ℕ → ℕ → ℕ → Bool) (N : ℕ) : (L : ℕ) → Fin N → Fin N → Fin N → ℕ
  | 0, _, _, _ => 1
  | L + 1, a, b, c => ∑ v : Fin N, if WN a b c v = true then dp4 WN N L b c v else 0

theorem dp4_eq (WN : ℕ → ℕ → ℕ → ℕ → Bool) (N : ℕ) : ∀ (L : ℕ) (a b c : Fin N),
    dp4 WN N L a b c =
      (Finset.univ.filter (fun h : Fin L → Fin N => chain4 WN L a b c h = true)).card
  | 0, a, b, c => by
    rw [dp4]
    have hu : (Finset.univ : Finset (Fin 0 → Fin N)) = {Fin.elim0} := by
      ext g
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      funext i
      exact i.elim0
    rw [hu, Finset.filter_singleton]
    simp [chain4]
  | L + 1, a, b, c => by
    rw [dp4, card_by_head]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    split_ifs with hW
    · rw [dp4_eq WN N L b c v]
      congr 1
      ext h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, chain4, Fin.cons_zero, Fin.tail_cons,
        hW, Bool.true_and]
    · symm
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro h - hc
      simp only [chain4, Fin.cons_zero, Bool.and_eq_true] at hc
      exact hW hc.1

/-- The arrays counted by a window property of four, through dp4, split by the first three
entries. -/
theorem count_eq_dp4 {k : ℕ} (P : (Fin (k + 3) → ℕ) → Prop) [DecidablePred P]
    (WN : ℕ → ℕ → ℕ → ℕ → Bool) (hP : ∀ x, P x ↔ wins4 WN (List.ofFn x) = true) (n : ℕ) :
    (Finset.univ.filter (fun x : Fin (k + 3) → Fin (n + 1) => P (fun i => (x i : ℕ)))).card =
      ∑ v : Fin (n + 1), ∑ w : Fin (n + 1), ∑ u : Fin (n + 1), dp4 WN (n + 1) k v w u := by
  rw [card_by_head]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [card_by_head]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [card_by_head]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [dp4_eq]
  congr 1
  ext h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hP, chain4_wins, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

end DPCount

/-- The test of `good` on four consecutive entries. -/
def WN (a b c d : ℕ) : Bool := Nat.ble (med a b c) (med b c d)

lemma hW (x : Fin 8 → ℕ) : good x ↔ wins4 WN (List.ofFn x) = true := by
  rw [show List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] from rfl]
  simp [good, wins4, WN, Nat.ble_eq, and_assoc]

lemma av0 : a 0 = 1 := by
  unfold a
  rw [count_eq_dp4 good WN hW 0]
  decide +kernel

lemma av1 : a 1 = 111 := by
  unfold a
  rw [count_eq_dp4 good WN hW 1]
  decide +kernel

lemma av2 : a 2 = 2026 := by
  unfold a
  rw [count_eq_dp4 good WN hW 2]
  decide +kernel

lemma av3 : a 3 = 16104 := by
  unfold a
  rw [count_eq_dp4 good WN hW 3]
  decide +kernel

lemma av4 : a 4 = 81664 := by
  unfold a
  rw [count_eq_dp4 good WN hW 4]
  decide +kernel

lemma av5 : a 5 = 311498 := by
  unfold a
  rw [count_eq_dp4 good WN hW 5]
  decide +kernel

lemma av6 : a 6 = 974944 := by
  unfold a
  rw [count_eq_dp4 good WN hW 6]
  decide +kernel

lemma av7 : a 7 = 2637228 := by
  unfold a
  rw [count_eq_dp4 good WN hW 7]
  decide +kernel

lemma pc0 : pc good 0 = 0 := by
  decide +kernel

/-- Solving count_eq at n = 0..k-1 for the pattern counts, with the counts as variables. -/
lemma lin (p : ℕ → ℕ) (h0 : p 0 = 0) (e0 : 1 = ∑ j ∈ Finset.range (8 + 1), (0 + 1).choose j * p j)
    (e1 : 111 = ∑ j ∈ Finset.range (8 + 1), (1 + 1).choose j * p j) (e2 : 2026 = ∑ j ∈ Finset.range
    (8 + 1), (2 + 1).choose j * p j) (e3 : 16104 = ∑ j ∈ Finset.range (8 + 1), (3 + 1).choose j * p
    j) (e4 : 81664 = ∑ j ∈ Finset.range (8 + 1), (4 + 1).choose j * p j) (e5 : 311498 = ∑ j ∈
    Finset.range (8 + 1), (5 + 1).choose j * p j) (e6 : 974944 = ∑ j ∈ Finset.range (8 + 1), (6 +
    1).choose j * p j) (e7 : 2637228 = ∑ j ∈ Finset.range (8 + 1), (7 + 1).choose j * p j) : p 0 = 0 ∧
    p 1 = 1 ∧ p 2 = 109 ∧ p 3 = 1696 ∧ p 4 = 8662 ∧ p 5 = 20299 ∧ p 6 = 24213 ∧ p 7 = 14348 ∧ p 8 =
    3360 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at e0 e1 e2 e3 e4 e5 e6 e7
  norm_num [Nat.choose] at e0 e1 e2 e3 e4 e5 e6 e7
  omega

lemma pcv : pc good 0 = 0 ∧ pc good 1 = 1 ∧ pc good 2 = 109 ∧ pc good 3 = 1696 ∧ pc good 4 = 8662 ∧
    pc good 5 = 20299 ∧ pc good 6 = 24213 ∧ pc good 7 = 14348 ∧ pc good 8 = 3360 :=
  lin (pc good) pc0 (av0.symm.trans (count_eq hP 0)) (av1.symm.trans (count_eq hP 1))
    (av2.symm.trans (count_eq hP 2)) (av3.symm.trans (count_eq hP 3)) (av4.symm.trans (count_eq hP
    4)) (av5.symm.trans (count_eq hP 5)) (av6.symm.trans (count_eq hP 6)) (av7.symm.trans (count_eq
    hP 7))

/-- The closed form a(n) = Sum_j c_j binomial(n+1, j). -/
lemma a_eq (n : ℕ) : (a n : ℚ) =
    1 * (n + 1) + 109 * ((n + 1) * n / 2) + 1696 * ((n + 1) * n * (n - 1) / 6) + 8662 * ((n + 1) * n * (n - 1) * (n - 2) / 24) + 20299 * ((n + 1) * n * (n - 1) * (n - 2) * (n - 3) / 120) + 24213 * ((n + 1) * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) / 720) + 14348 * ((n + 1) * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) / 5040) + 3360 * ((n + 1) * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) * (n - 6) / 40320) := by
  have h := count_eq hP n
  unfold a
  rw [h]
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8⟩ := pcv
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, p0, p1, p2, p3, p4, p5, p6, p7, p8]
  push_cast
  simp only [ch2, ch3, ch4, ch5, ch6, ch7, ch8]
  simp
  ring

lemma values : a 1 = 111 ∧ a 2 = 2026 ∧ a 3 = 16104 ∧ a 4 = 81664 ∧ a 5 = 311498 ∧ a 6 = 974944 ∧ a 7 = 2637228 ∧ a 8 = 6376143 ∧ a 9 = 14100493 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [← Nat.cast_inj (R := ℚ), a_eq]
    norm_num

/-- Barker's recurrence, for n > 9. -/
theorem recurrence (n : ℕ) (hn : 9 < n) :
    (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 10 := ⟨n - 10, by omega⟩
  simp only [show q + 10 - 1 = q + 9 by omega, show q + 10 - 2 = q + 8 by omega, show q + 10 - 3 =
    q + 7 by omega, show q + 10 - 4 = q + 6 by omega, show q + 10 - 5 = q + 5 by omega, show q +
    10 - 6 = q + 4 by omega, show q + 10 - 7 = q + 3 by omega, show q + 10 - 8 = q + 2 by omega,
    show q + 10 - 9 = q + 1 by omega]
  have h : (a (q + 10) : ℚ) = 9 * a (q + 9) - 36 * a (q + 8) + 84 * a (q + 7) - 126 * a (q + 6) + 126 * a (q + 5) - 84 * a (q + 4) + 36 * a (q + 3) - 9 * a (q + 2) + a (q + 1) := by
    rw [a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq]
    push_cast
    ring
  exact_mod_cast h

/-- Barker's g.f., as A(x) (1 - x)^9 = N(x) in Z[[x]]. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 9 =
    X * (111 + 1027 * X + 1866 * X ^ 2 + 340 * X ^ 3 + 68 * X ^ 4 - 80 * X ^ 5 + 36 * X ^ 6 - 9 * X ^ 7 + X ^ 8) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 9 =
      A - C 9 * (A * X ^ 1) + C 36 * (A * X ^ 2) - C 84 * (A * X ^ 3) + C 126 * (A * X ^ 4) - C
        126 * (A * X ^ 5) + C 84 * (A * X ^ 6) - C 36 * (A * X ^ 7) + C 9 * (A * X ^ 8) - A * X ^ 9
        := by
    simp only [map_ofNat]; ring
  have e2 : (X * (111 + 1027 * X + 1866 * X ^ 2 + 340 * X ^ 3 + 68 * X ^ 4 - 80 * X ^ 5 + 36 * X ^ 6 - 9 * X ^ 7 + X ^ 8) : ℤ⟦X⟧) =
      X ^ 1 * C 111 + X ^ 2 * C 1027 + X ^ 3 * C 1866 + X ^ 4 * C 340 + X ^ 5 * C 68 - X ^ 6 * C
        80 + X ^ 7 * C 36 - X ^ 8 * C 9 + X ^ 9 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  have v := values
  rcases Nat.lt_or_ge n 10 with hn | hn
  · interval_cases n <;> simp_all
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 10 := ⟨n - 10, by omega⟩
    have h := recurrence (q + 10) (by omega)
    simp only [show q + 10 - 1 = q + 9 by omega, show q + 10 - 2 = q + 8 by omega, show q + 10 - 3 =
      q + 7 by omega, show q + 10 - 4 = q + 6 by omega, show q + 10 - 5 = q + 5 by omega, show q +
      10 - 6 = q + 4 by omega, show q + 10 - 7 = q + 3 by omega, show q + 10 - 8 = q + 2 by omega,
      show q + 10 - 9 = q + 1 by omega] at h ⊢
    simp only [show ¬ q + 10 = 0 by omega, show ¬ q + 9 = 0 by omega, show ¬ q + 8 = 0 by omega,
      show ¬ q + 7 = 0 by omega, show ¬ q + 6 = 0 by omega, show ¬ q + 5 = 0 by omega, show ¬ q +
      4 = 0 by omega, show ¬ q + 3 = 0 by omega, show ¬ q + 2 = 0 by omega, show ¬ q + 1 = 0 by
      omega, show 1 ≤ q + 10 by omega, show 2 ≤ q + 10 by omega, show 3 ≤ q + 10 by omega, show 4 ≤
      q + 10 by omega, show 5 ≤ q + 10 by omega, show 6 ≤ q + 10 by omega, show 7 ≤ q + 10 by omega,
      show 8 ≤ q + 10 by omega, show 9 ≤ q + 10 by omega, show ¬ q + 10 = 1 by omega, show ¬ q +
      10 = 2 by omega, show ¬ q + 10 = 3 by omega, show ¬ q + 10 = 4 by omega, show ¬ q + 10 = 5 by
      omega, show ¬ q + 10 = 6 by omega, show ¬ q + 10 = 7 by omega, show ¬ q + 10 = 8 by omega,
      show ¬ q + 10 = 9 by omega, if_true, if_false]
    rw [h]
    ring

/-- Hardin's empirical formula, for all n. -/
theorem empirical (n : ℕ) : (a n : ℚ) = (1 / 12) * n ^ 8 + (1487 / 1260) * n ^ 7 + (4757 / 720) * n ^ 6 + (13757 / 720) * n ^ 5 + (4519 / 144) * n ^ 4 + (21611 / 720) * n ^ 3 + (2957 / 180) * n ^ 2 + (2183 / 420) * n + 1 := by
  rw [a_eq]
  ring

/-- Controls: the entry's data a(1..23). -/
theorem controls : a 1 = 111 ∧ a 2 = 2026 ∧ a 3 = 16104 ∧ a 4 = 81664 ∧ a 5 = 311498 ∧
    a 6 = 974944 ∧ a 7 = 2637228 ∧ a 8 = 6376143 ∧ a 9 = 14100493 ∧ a 10 = 28998090 ∧
    a 11 = 56144452 ∧ a 12 = 103306710 ∧ a 13 = 181980592 ∧ a 14 = 308701712 ∧ a 15 = 506675752 ∧
    a 16 = 807775485 ∧ a 17 = 1254955947 ∧ a 18 = 1905142426 ∧ a 19 = 2832649296 ∧
    a 20 = 4133191084 ∧ a 21 = 5928550518 ∧ a 22 = 8371971664 ∧ a 23 = 11654349620 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩ <;>
  · rw [← Nat.cast_inj (R := ℚ), a_eq]
    norm_num

/-- Both of Barker's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 10 < n →
      (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 9 =
      X * (111 + 1027 * X + 1866 * X ^ 2 + 340 * X ^ 3 + 68 * X ^ 4 - 80 * X ^ 5 + 36 * X ^ 6 - 9 * X ^ 7 + X ^ 8) :=
  ⟨fun n hn => recurrence n (by omega), gf⟩

end OMA.S_oeis_a250145

theorem OMA.solution : type_of% @OMA.S_oeis_a250145.main :=
  OMA.S_oeis_a250145.conjecture
