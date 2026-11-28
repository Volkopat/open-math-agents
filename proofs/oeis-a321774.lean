import OMAStatements.S_oeis_a321774

namespace OMA.S_oeis_a321774

open PowerSeries Finset




section pattern

variable {α : Type*} [DecidableEq α]

/-- Distinct values occur with distinct multiplicities. -/
def DM (c : Fin 4 → α) : Prop :=
  ∀ i j, c i ≠ c j →
    (univ.filter (fun k => c k = c i)).card ≠ (univ.filter (fun k => c k = c j)).card

/-- All four equal, or one position p different from the three others, which are equal. -/
def Shape (c : Fin 4 → α) : Prop :=
  (∀ i j, c i = c j) ∨ ∃ p, ∀ i, i ≠ p → c i ≠ c p ∧ ∀ j, j ≠ p → c i = c j

instance (c : Fin 4 → α) : Decidable (DM c) := by unfold DM; infer_instance
instance (c : Fin 4 → α) : Decidable (Shape c) := by unfold Shape; infer_instance

/-- The equality pattern: the first index carrying the same value. -/
def pat (c : Fin 4 → α) : Fin 4 → Fin 4 := fun i =>
  if c 0 = c i then 0 else if c 1 = c i then 1 else if c 2 = c i then 2 else 3

lemma pat_spec (c : Fin 4 → α) (i : Fin 4) : c (pat c i) = c i := by
  unfold pat
  split_ifs with h0 h1 h2
  · exact h0
  · exact h1
  · exact h2
  · fin_cases i <;> simp_all

lemma pat_eq (c : Fin 4 → α) (i j : Fin 4) : pat c i = pat c j ↔ c i = c j := by
  constructor
  · intro h
    rw [← pat_spec c i, ← pat_spec c j, h]
  · intro h
    unfold pat
    rw [h]

lemma DM_iff_pat (c : Fin 4 → α) : DM c ↔ DM (pat c) := by
  have hm : ∀ i, (univ.filter (fun k => c k = c i)).card =
      (univ.filter (fun k => pat c k = pat c i)).card := by
    intro i
    congr 1
    ext k
    simp [pat_eq]
  unfold DM
  constructor
  · intro h i j hne
    rw [← hm, ← hm]
    exact h i j (fun e => hne ((pat_eq c i j).2 e))
  · intro h i j hne
    rw [hm, hm]
    exact h i j (fun e => hne ((pat_eq c i j).1 e))

lemma Shape_iff_pat (c : Fin 4 → α) : Shape c ↔ Shape (pat c) := by
  unfold Shape
  simp only [pat_eq, ne_eq]

lemma DM_iff_Shape_fin : ∀ d : Fin 4 → Fin 4, DM d ↔ Shape d := by
  decide +kernel

lemma DM_iff (c : Fin 4 → α) : DM c ↔ Shape c := by
  rw [DM_iff_pat, Shape_iff_pat]
  exact DM_iff_Shape_fin _

end pattern

/-- The compositions with all four parts equal. -/
lemma card_all (n : ℕ) :
    ((univ : Finset (Fin 4 → Fin (n + 1))).filter
      (fun c => (∀ i, 0 < (c i).val) ∧ ∑ i, (c i).val = n ∧ ∀ i j, c i = c j)).card =
    if 0 < n ∧ n % 4 = 0 then 1 else 0 := by
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨fun _ => ⟨n / 4, by omega⟩, ?_⟩
    ext c
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨hp, hs, he⟩
      funext i
      apply Fin.ext
      simp only [Fin.sum_univ_four] at hs
      have e1 := congrArg Fin.val (he 0 i)
      have e2 := congrArg Fin.val (he 1 0)
      have e3 := congrArg Fin.val (he 2 0)
      have e4 := congrArg Fin.val (he 3 0)
      simp only at e1 e2 e3 e4 ⊢
      omega
    · rintro rfl
      refine ⟨fun _ => by simp; omega, by simp [Fin.sum_univ_four]; omega, fun _ _ => rfl⟩
  · rw [Finset.card_eq_zero]
    ext c
    simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
    intro hp hs he
    apply h
    simp only [Fin.sum_univ_four] at hs
    have e2 := congrArg Fin.val (he 1 0)
    have e3 := congrArg Fin.val (he 2 0)
    have e4 := congrArg Fin.val (he 3 0)
    have p0 := hp 0
    omega

/-- The common values allowed for three equal parts and one different part. -/
def S (n : ℕ) : Finset (Fin (n + 1)) :=
  univ.filter (fun x => 0 < x.val ∧ 3 * x.val < n ∧ n - 3 * x.val ≠ x.val)

/-- The compositions whose part at p differs from the three others, which are equal. -/
def odd (n : ℕ) (p : Fin 4) : Finset (Fin 4 → Fin (n + 1)) :=
  univ.filter (fun c => (∀ i, 0 < (c i).val) ∧ ∑ i, (c i).val = n ∧
    ∀ i, i ≠ p → c i ≠ c p ∧ ∀ j, j ≠ p → c i = c j)

lemma sum_odd (n : ℕ) (p : Fin 4) (x : Fin (n + 1)) (y : ℕ) :
    ∑ i, (if i = p then y else x.val) = y + 3 * x.val := by
  fin_cases p <;> simp [Fin.sum_univ_four] <;> ring

lemma card_odd (n : ℕ) (p : Fin 4) : (odd n p).card = (S n).card := by
  symm
  refine Finset.card_bij' (fun x _ => fun i => if i = p then ⟨n - 3 * x.val, by omega⟩ else x)
    (fun c _ => c (p + 1)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [S, odd, mem_filter, mem_univ, true_and] at hx ⊢
    obtain ⟨h1, h2, h3⟩ := hx
    refine ⟨fun i => ?_, ?_, fun i hi => ⟨?_, fun j hj => ?_⟩⟩
    · split_ifs
      · simp only
        omega
      · exact h1
    · have := sum_odd n p x (n - 3 * x.val)
      simp only [apply_ite Fin.val, Fin.val_mk] at this ⊢
      rw [this]
      omega
    · rw [if_neg hi, if_pos trivial]
      intro e
      have := congrArg Fin.val e
      simp only at this
      exact h3 this.symm
    · rw [if_neg hi, if_neg hj]
  · intro c hc
    simp only [S, odd, mem_filter, mem_univ, true_and] at hc ⊢
    obtain ⟨h1, h2, h3⟩ := hc
    have hq : p + 1 ≠ p := by fin_cases p <;> decide
    have hsum : ∑ i, (c i).val = (c p).val + 3 * (c (p + 1)).val := by
      have e : ∀ i, (c i).val = if i = p then (c p).val else (c (p + 1)).val := by
        intro i
        split_ifs with hi
        · rw [hi]
        · rw [(h3 i hi).2 (p + 1) hq]
      rw [Finset.sum_congr rfl (fun i _ => e i), sum_odd]
    have hs : (c p).val + 3 * (c (p + 1)).val = n := by omega
    have hne := (h3 (p + 1) hq).1
    refine ⟨h1 _, by have := h1 p; omega, fun e => hne ?_⟩
    apply Fin.ext
    omega
  · intro x _
    exact if_neg (by fin_cases p <;> decide)
  · intro c hc
    simp only [odd, mem_filter, mem_univ, true_and] at hc
    obtain ⟨h1, h2, h3⟩ := hc
    have hq : p + 1 ≠ p := by fin_cases p <;> decide
    have hsum : ∑ i, (c i).val = (c p).val + 3 * (c (p + 1)).val := by
      have e : ∀ i, (c i).val = if i = p then (c p).val else (c (p + 1)).val := by
        intro i
        split_ifs with hi
        · rw [hi]
        · rw [(h3 i hi).2 (p + 1) hq]
      rw [Finset.sum_congr rfl (fun i _ => e i), sum_odd]
    have hs : (c p).val + 3 * (c (p + 1)).val = n := by omega
    funext i
    split_ifs with hi
    · rw [hi]
      apply Fin.ext
      simp only
      omega
    · exact ((h3 i hi).2 (p + 1) hq).symm

lemma card_S (n : ℕ) (hn : 1 ≤ n) :
    (S n).card + (if n % 4 = 0 then 1 else 0) = (n - 1) / 3 := by
  have e1 : (S n).card = ((range (n + 1)).filter
      (fun m => 0 < m ∧ 3 * m < n ∧ n - 3 * m ≠ m)).card := by
    refine Finset.card_bij (fun x _ => x.val) ?_ ?_ ?_
    · intro x hx
      simp only [S, mem_filter, mem_univ, true_and, mem_range] at hx ⊢
      exact ⟨x.isLt, hx⟩
    · intro x _ y _ h
      exact Fin.ext h
    · intro m hm
      simp only [mem_filter, mem_range] at hm
      exact ⟨⟨m, hm.1⟩, by simp only [S, mem_filter, mem_univ, true_and]; exact hm.2, rfl⟩
  have e2 : (range (n + 1)).filter (fun m => 0 < m ∧ 3 * m < n ∧ n - 3 * m ≠ m) =
      Icc 1 ((n - 1) / 3) \ (if n % 4 = 0 then {n / 4} else ∅) := by
    ext m
    simp only [mem_filter, mem_range, mem_sdiff, mem_Icc]
    split_ifs with h4
    · simp only [mem_singleton]
      omega
    · simp only [Finset.notMem_empty, not_false_eq_true, and_true]
      omega
  rw [e1, e2]
  split_ifs with h4
  · rw [Finset.card_sdiff, Finset.singleton_inter_of_mem (by simp only [mem_Icc]; omega)]
    simp only [Nat.card_Icc, card_singleton]
    omega
  · simp

/-- The count for n >= 1: a(n) + 3 [4 | n] = 4 floor((n - 1)/3). -/
lemma a_formula (n : ℕ) (hn : 1 ≤ n) : a n + 3 * (if n % 4 = 0 then 1 else 0) = 4 * ((n - 1) / 3) := by
  have hsplit : ((univ : Finset (Fin 4 → Fin (n + 1))).filter good) =
      ((univ : Finset (Fin 4 → Fin (n + 1))).filter
        (fun c => (∀ i, 0 < (c i).val) ∧ ∑ i, (c i).val = n ∧ ∀ i j, c i = c j)) ∪
      univ.biUnion (odd n) := by
    ext c
    simp only [mem_union, mem_filter, mem_univ, true_and, mem_biUnion, odd, good]
    have := DM_iff c
    unfold DM Shape at this
    rw [this]
    constructor
    · rintro ⟨h1, h2, (h3 | ⟨p, hp⟩)⟩
      · exact Or.inl ⟨h1, h2, h3⟩
      · exact Or.inr ⟨p, h1, h2, hp⟩
    · rintro (⟨h1, h2, h3⟩ | ⟨p, h1, h2, hp⟩)
      · exact ⟨h1, h2, Or.inl h3⟩
      · exact ⟨h1, h2, Or.inr ⟨p, hp⟩⟩
  have hdisj : Disjoint ((univ : Finset (Fin 4 → Fin (n + 1))).filter
        (fun c => (∀ i, 0 < (c i).val) ∧ ∑ i, (c i).val = n ∧ ∀ i j, c i = c j))
      (univ.biUnion (odd n)) := by
    rw [Finset.disjoint_left]
    intro c hc hc'
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, odd] at hc hc'
    obtain ⟨p, -, -, hp⟩ := hc'
    have hq : p + 1 ≠ p := by fin_cases p <;> decide
    exact (hp (p + 1) hq).1 (hc.2.2 _ _)
  have hpair : ∀ p ∈ (univ : Finset (Fin 4)), ∀ p' ∈ (univ : Finset (Fin 4)), p ≠ p' →
      Disjoint (odd n p) (odd n p') := by
    intro p _ p' _ hpp
    rw [Finset.disjoint_left]
    intro c hc hc'
    simp only [odd, mem_filter, mem_univ, true_and] at hc hc'
    have hthird : ∀ p p' : Fin 4, p ≠ p' → ∃ j, j ≠ p ∧ j ≠ p' := by decide
    obtain ⟨j, hj, hj'⟩ := hthird p p' hpp
    have h1 := (hc.2.2 j hj).2 p' (Ne.symm hpp)
    have h2 := (hc'.2.2 p hpp).2 j hj'
    exact (hc.2.2 p' (Ne.symm hpp)).1 (h1.symm.trans h2.symm)
  unfold a
  rw [hsplit, Finset.card_union_of_disjoint hdisj, card_all, Finset.card_biUnion hpair]
  simp only [card_odd, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have := card_S n hn
  split_ifs at this ⊢ with h1 h2 h2 <;> omega

lemma a_small : a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0 ∧ a 4 = 1 ∧ a 5 = 4 ∧ a 6 = 4 ∧ a 7 = 8 := by
  have h1 := a_formula 1 (by norm_num)
  have h2 := a_formula 2 (by norm_num)
  have h3 := a_formula 3 (by norm_num)
  have h4 := a_formula 4 (by norm_num)
  have h5 := a_formula 5 (by norm_num)
  have h6 := a_formula 6 (by norm_num)
  have h7 := a_formula 7 (by norm_num)
  rw [if_neg (show ¬ (1 % 4 = 0) by norm_num)] at h1
  rw [if_neg (show ¬ (2 % 4 = 0) by norm_num)] at h2
  rw [if_neg (show ¬ (3 % 4 = 0) by norm_num)] at h3
  rw [if_pos (show 4 % 4 = 0 by norm_num)] at h4
  rw [if_neg (show ¬ (5 % 4 = 0) by norm_num)] at h5
  rw [if_neg (show ¬ (6 % 4 = 0) by norm_num)] at h6
  rw [if_neg (show ¬ (7 % 4 = 0) by norm_num)] at h7
  omega

lemma ind_eq (m : ℕ) : (if m % 4 = 0 then 1 else 0) = 1 - min 1 (m % 4) := by
  split_ifs with h <;> omega

lemma a_rec (n : ℕ) : (a (n + 8) : ℤ) = a (n + 5) + a (n + 4) - a (n + 1) := by
  have h8 := a_formula (n + 8) (by omega)
  have h5 := a_formula (n + 5) (by omega)
  have h4 := a_formula (n + 4) (by omega)
  have h1 := a_formula (n + 1) (by omega)
  rw [ind_eq] at h8 h5 h4 h1
  rw [show (n + 8 - 1) / 3 = (n + 5 - 1) / 3 + 1 by omega, show (n + 8) % 4 = (n + 4) % 4 by omega]
    at h8
  rw [show (n + 4 - 1) / 3 = (n + 1 - 1) / 3 + 1 by omega] at h4
  rw [show (n + 5) % 4 = (n + 1) % 4 by omega] at h5
  have : (a (n + 8) : ℤ) + a (n + 1) = a (n + 5) + a (n + 4) := by
    have : a (n + 8) + a (n + 1) = a (n + 5) + a (n + 4) := by omega
    exact_mod_cast this
  linarith

/-- The recurrence of the entry, for n > 10. -/
theorem recur : ∀ n : ℕ, 10 < n → (a n : ℤ) = a (n - 3) + a (n - 4) - a (n - 7) := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 11 := ⟨n - 11, by omega⟩
  have h := a_rec (j + 3)
  rw [show j + 3 + 8 = j + 11 by omega, show j + 3 + 5 = j + 8 by omega,
    show j + 3 + 4 = j + 7 by omega, show j + 3 + 1 = j + 4 by omega] at h
  rw [show j + 11 - 3 = j + 8 by omega, show j + 11 - 4 = j + 7 by omega,
    show j + 11 - 7 = j + 4 by omega]
  exact h

/-- Barker's g.f. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2) * (1 + X + X ^ 2)) =
      X ^ 4 * (1 + 4 * X + 4 * X ^ 2 + 7 * X ^ 3) := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7⟩ := a_small
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2) * (1 + X + X ^ 2)) =
      A - A * X ^ 3 - A * X ^ 4 + A * X ^ 7 := by
    ring
  have e2 : (X ^ 4 * (1 + 4 * X + 4 * X ^ 2 + 7 * X ^ 3) : ℚ⟦X⟧) =
      X ^ 4 + X ^ 5 * C 4 + X ^ 6 * C 4 + X ^ 7 * C 7 := by
    rw [show (C (4 : ℚ) : ℚ⟦X⟧) = 4 from map_ofNat C 4, show (C (7 : ℚ) : ℚ⟦X⟧) = 7 from map_ofNat C 7]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | n
  · simp
  · simp [v1]
  · simp [v2]
  · simp [v3]
  · simp [v1, v4] <;> norm_num
  · simp [v1, v2, v5] <;> norm_num
  · simp [v2, v3, v6] <;> norm_num
  · simp [v3, v4, v7] <;> norm_num
  · have h := a_rec n
    have hq : (a (n + 8) : ℚ) = a (n + 5) + a (n + 4) - a (n + 1) := by exact_mod_cast h
    simp only [show ¬ (n + 8 = 0) by omega,
      show 3 ≤ n + 8 by omega, show ¬ (n + 8 - 3 = 0) by omega, show n + 8 - 3 = n + 5 by omega,
      show ¬ (n + 5 = 0) by omega,
      show 4 ≤ n + 8 by omega, show ¬ (n + 8 - 4 = 0) by omega, show n + 8 - 4 = n + 4 by omega,
      show ¬ (n + 4 = 0) by omega,
      show 7 ≤ n + 8 by omega, show ¬ (n + 8 - 7 = 0) by omega, show n + 8 - 7 = n + 1 by omega,
      show ¬ (n + 1 = 0) by omega,
      show ¬ (n + 8 = 4) by omega, show ¬ (n + 8 = 5) by omega, show ¬ (n + 8 = 6) by omega,
      show ¬ (n + 8 = 7) by omega, if_false, if_true]
    linear_combination hq

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2) * (1 + X + X ^ 2)) =
        X ^ 4 * (1 + 4 * X + 4 * X ^ 2 + 7 * X ^ 3) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = a (n - 3) + a (n - 4) - a (n - 7) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a321774

theorem OMA.solution : type_of% @OMA.S_oeis_a321774.main :=
  OMA.S_oeis_a321774.conjecture
