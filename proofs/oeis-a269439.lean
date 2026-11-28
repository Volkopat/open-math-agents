import OMAStatements.S_oeis_a269439
import Mathlib

-- oeis-a269439: the conjectured generating function of a count of length-7 arrays over 0..n.
--
-- Method (works for any property of arrays that is invariant under strictly increasing
-- relabelling of the values):
--  A. the arrays over an alphabet of size m with the property split by their set of values S;
--     the strictly increasing bijection from 0..|S|-1 onto S shows that the number with value
--     set S depends only on |S|, so the count is  sum_j C(m, j) * c_j  for fixed c_0..c_7;
--  B. the property is recognised by a small automaton, which lets the kernel count the arrays
--     over alphabets of size 0..7; these 8 values determine c_j = [0, 1, 90, 1449, 7528, 16200, 15120, 5040];
--  C. sum_n C(n+s, j) x^n = x^(j-s) / (1-x)^(j+1) for j >= s.

open PowerSeries

/-- All lists of length L over 0..m-1. -/
def hl_lists (m : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | L + 1 => (List.range m).flatMap (fun x => (hl_lists m L).map (fun l => x :: l))

theorem hl_mem (m : ℕ) : ∀ (L : ℕ) (l : List ℕ),
    l ∈ hl_lists m L ↔ l.length = L ∧ ∀ x ∈ l, x < m
  | 0, l => by
      simp only [hl_lists, List.mem_singleton]
      constructor
      · rintro rfl
        simp
      · rintro ⟨h, -⟩
        exact List.length_eq_zero_iff.mp h
  | L + 1, l => by
      simp only [hl_lists, List.mem_flatMap, List.mem_range, List.mem_map]
      constructor
      · rintro ⟨x, hx, t, ht, rfl⟩
        obtain ⟨h1, h2⟩ := (hl_mem m L t).mp ht
        refine ⟨by simp [h1], ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx
        · exact h2 y hy
      · rintro ⟨h1, h2⟩
        cases l with
        | nil => simp at h1
        | cons x t =>
          exact ⟨x, h2 x (by simp), t,
            (hl_mem m L t).mpr ⟨by simpa using h1, fun y hy => h2 y (by simp [hy])⟩, rfl⟩

theorem hl_nodup (m : ℕ) : ∀ L : ℕ, (hl_lists m L).Nodup
  | 0 => by simp [hl_lists]
  | L + 1 => by
      simp only [hl_lists]
      rw [List.nodup_flatMap]
      refine ⟨fun x _ => (hl_nodup m L).map (fun a b h => (List.cons_injective h)), ?_⟩
      apply List.nodup_range.pairwise_of_forall_ne
      intro a _ b _ hab
      rw [Function.onFun, List.disjoint_left]
      intro l h1 h2
      obtain ⟨t, -, rfl⟩ := List.mem_map.mp h1
      obtain ⟨t', -, h⟩ := List.mem_map.mp h2
      exact hab (List.cons.inj h).1.symm

/-- Counting functions Fin L → 0..m-1 with a property of the list of values is counting lists. -/
theorem hl_bridge (m L : ℕ) (P : List ℕ → Prop) [DecidablePred P] :
    ((Fintype.piFinset fun _ : Fin L => Finset.range m).filter
        (fun v => P (List.ofFn v))).card =
      ((hl_lists m L).filter (fun l => decide (P l))).length := by
  classical
  rw [← List.toFinset_card_of_nodup ((hl_nodup m L).filter _),
    ← Finset.card_image_of_injective _ (List.ofFn_injective (n := L) (α := ℕ))]
  congr 1
  ext l
  simp only [Finset.mem_image, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
    List.mem_toFinset, List.mem_filter, hl_mem, decide_eq_true_eq]
  constructor
  · rintro ⟨v, ⟨hv, hP⟩, rfl⟩
    refine ⟨⟨by simp, ?_⟩, hP⟩
    intro x hx
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' v x).mp hx
    exact hv i
  · rintro ⟨⟨hlen, hlt⟩, hP⟩
    subst hlen
    refine ⟨fun i => l.get i, ⟨fun i => hlt _ (List.get_mem _ _), ?_⟩, List.ofFn_get l⟩
    rw [List.ofFn_get]
    exact hP

/-- The strictly increasing map that sends 0..|S|-1 onto S. -/
noncomputable def hl_g (S : Finset ℕ) (x : ℕ) : ℕ :=
  if h : x < S.card then S.orderEmbOfFin rfl ⟨x, h⟩ else S.sup id + 1 + x

theorem hl_g_mem (S : Finset ℕ) (x : ℕ) (hx : x < S.card) : hl_g S x ∈ S := by
  unfold hl_g
  rw [dif_pos hx]
  exact S.orderEmbOfFin_mem rfl _

theorem hl_g_strictMono (S : Finset ℕ) : StrictMono (hl_g S) := by
  intro x y hxy
  by_cases hx : x < S.card
  · by_cases hy : y < S.card
    · unfold hl_g
      rw [dif_pos hx, dif_pos hy]
      exact (S.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr hxy)
    · have h1 : hl_g S x ≤ S.sup id := Finset.le_sup (f := id) (hl_g_mem S x hx)
      have h2 : hl_g S y = S.sup id + 1 + y := by
        unfold hl_g
        rw [dif_neg hy]
      omega
  · have hy : ¬ y < S.card := by omega
    unfold hl_g
    rw [dif_neg hx, dif_neg hy]
    omega

theorem hl_g_surj (S : Finset ℕ) (s : ℕ) (hs : s ∈ S) : ∃ x, x < S.card ∧ hl_g S x = s := by
  have h : s ∈ Set.range (S.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hs
  obtain ⟨i, hi⟩ := h
  refine ⟨i, i.2, ?_⟩
  unfold hl_g
  rw [dif_pos i.2]
  exact hi

/-- The number of arrays with the property and value set S depends only on |S|. -/
theorem hl_fiber (L : ℕ) (Q : List ℕ → Prop) [DecidablePred Q]
    (hinv : ∀ g : ℕ → ℕ, StrictMono g → ∀ l : List ℕ, (Q (l.map g) ↔ Q l))
    (m : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range m) :
    (((Fintype.piFinset fun _ : Fin L => Finset.range m).filter
        (fun v => Q (List.ofFn v))).filter (fun v => Finset.univ.image v = S)).card =
      ((Fintype.piFinset fun _ : Fin L => Finset.range S.card).filter
        (fun w => Q (List.ofFn w) ∧ ∀ i ∈ List.range S.card, i ∈ List.ofFn w)).card := by
  classical
  symm
  apply Finset.card_bij (fun w _ => fun k => hl_g S (w k))
  · intro w hw
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hw ⊢
    obtain ⟨hw1, hQ, hsurj⟩ := hw
    refine ⟨⟨fun k => Finset.mem_range.mp (hS (hl_g_mem S _ (hw1 k))), ?_⟩, ?_⟩
    · have e : List.ofFn (fun k => hl_g S (w k)) = (List.ofFn w).map (hl_g S) := by
        rw [List.map_ofFn]
        rfl
      rw [e, hinv _ (hl_g_strictMono S)]
      exact hQ
    · ext s
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨k, rfl⟩
        exact hl_g_mem S _ (hw1 k)
      · intro hs
        obtain ⟨x, hx, rfl⟩ := hl_g_surj S s hs
        obtain ⟨k, hk⟩ := (List.mem_ofFn' w x).mp (hsurj x (List.mem_range.mpr hx))
        exact ⟨k, by rw [hk]⟩
  · intro w1 _ w2 _ h
    funext k
    exact (hl_g_strictMono S).injective (congrFun h k)
  · intro v hv
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hv
    obtain ⟨⟨hv1, hQ⟩, himg⟩ := hv
    have hmem : ∀ k, v k ∈ S := fun k => by
      rw [← himg]
      exact Finset.mem_image_of_mem v (Finset.mem_univ k)
    choose w hw1 hw2 using fun k => hl_g_surj S (v k) (hmem k)
    have hgw : (fun k => hl_g S (w k)) = v := funext hw2
    refine ⟨w, ?_, hgw⟩
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨hw1, ?_, ?_⟩
    · have e : List.ofFn v = (List.ofFn w).map (hl_g S) := by
        rw [List.map_ofFn, ← hgw]
        rfl
      rw [e, hinv _ (hl_g_strictMono S)] at hQ
      exact hQ
    · intro i hi
      have hi' := List.mem_range.mp hi
      have h1 : hl_g S i ∈ Finset.univ.image v := by
        rw [himg]
        exact hl_g_mem S i hi'
      obtain ⟨k, -, hk⟩ := Finset.mem_image.mp h1
      rw [List.mem_ofFn']
      refine ⟨k, ?_⟩
      apply (hl_g_strictMono S).injective
      rw [hw2 k, hk]

/-- Step A: the count is a combination of binomial coefficients. -/
theorem hl_decomp (L : ℕ) (Q : List ℕ → Prop) [DecidablePred Q]
    (hinv : ∀ g : ℕ → ℕ, StrictMono g → ∀ l : List ℕ, (Q (l.map g) ↔ Q l)) (m : ℕ) :
    ((Fintype.piFinset fun _ : Fin L => Finset.range m).filter
        (fun v => Q (List.ofFn v))).card =
      ∑ j ∈ Finset.range (m + 1), m.choose j *
        ((Fintype.piFinset fun _ : Fin L => Finset.range j).filter
          (fun w => Q (List.ofFn w) ∧ ∀ i ∈ List.range j, i ∈ List.ofFn w)).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun v : Fin L → ℕ => Finset.univ.image v)
    (t := (Finset.range m).powerset)]
  · rw [Finset.sum_congr rfl
      (fun S hS => hl_fiber L Q hinv m S (Finset.mem_powerset.mp hS))]
    have h := Finset.sum_powerset_apply_card (α := ℕ)
      (fun j => ((Fintype.piFinset fun _ : Fin L => Finset.range j).filter
        (fun w => Q (List.ofFn w) ∧ ∀ i ∈ List.range j, i ∈ List.ofFn w)).card)
      (x := Finset.range m)
    rw [h, Finset.card_range]
    simp only [smul_eq_mul]
  · intro v hv
    have hv' := Finset.mem_coe.mp hv
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hv'
    apply Finset.mem_coe.mpr
    rw [Finset.mem_powerset]
    intro x hx
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
    exact hv'.1 k

/-- No array of length L uses more than L values. -/
theorem hl_c_zero (L j : ℕ) (Q : List ℕ → Prop) [DecidablePred Q] (hj : L < j) :
    ((Fintype.piFinset fun _ : Fin L => Finset.range j).filter
      (fun w => Q (List.ofFn w) ∧ ∀ i ∈ List.range j, i ∈ List.ofFn w)).card = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro w - ⟨-, hsurj⟩
  have hsub : Finset.range j ⊆ Finset.univ.image w := by
    intro i hi
    obtain ⟨k, hk⟩ := (List.mem_ofFn' w i).mp
      (hsurj i (List.mem_range.mpr (Finset.mem_range.mp hi)))
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk⟩
  have h1 := Finset.card_le_card hsub
  have h2 : (Finset.univ.image w).card ≤ L :=
    calc (Finset.univ.image w).card ≤ (Finset.univ : Finset (Fin L)).card := Finset.card_image_le
      _ = L := by simp
  rw [Finset.card_range] at h1
  omega

theorem hl_sum_trim (f : ℕ → ℕ) (a b : ℕ) (hz : ∀ j, a ≤ j → f j = 0) :
    ∑ j ∈ Finset.range a, f j = ∑ j ∈ Finset.range (a + b), f j := by
  apply Finset.sum_subset (Finset.range_mono (Nat.le_add_right a b))
  intro j _ hj
  exact hz j (by simpa using hj)


/-- Step A, packaged: the count is a fixed combination of binomial coefficients. -/
theorem hl_poly (L : ℕ) (Q : List ℕ → Prop) [DecidablePred Q]
    (hinv : ∀ g : ℕ → ℕ, StrictMono g → ∀ l : List ℕ, (Q (l.map g) ↔ Q l)) :
    ∃ c : ℕ → ℕ, ∀ m : ℕ,
      ((Fintype.piFinset fun _ : Fin L => Finset.range m).filter
          (fun v => Q (List.ofFn v))).card =
        ∑ j ∈ Finset.range (L + 1), m.choose j * c j := by
  refine ⟨fun j => ((Fintype.piFinset fun _ : Fin L => Finset.range j).filter
      (fun w => Q (List.ofFn w) ∧ ∀ i ∈ List.range j, i ∈ List.ofFn w)).card, fun m => ?_⟩
  beta_reduce
  rw [hl_decomp L Q hinv m]
  rw [hl_sum_trim _ (m + 1) (L + 1) (fun j hj => by
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.zero_mul])]
  rw [show m + 1 + (L + 1) = L + 1 + (m + 1) by ring]
  rw [← hl_sum_trim _ (L + 1) (m + 1) (fun j hj => Nat.mul_eq_zero.mpr (Or.inr
    (hl_c_zero L j Q (by omega))))]

/-- Acceptance of a list by an automaton with two registers. -/
def hl_run (st : Option ℕ × Option ℕ → ℕ → Option (Option ℕ × Option ℕ)) :
    Option ℕ × Option ℕ → List ℕ → Bool
  | _, [] => true
  | s, x :: t =>
    match st s x with
    | none => false
    | some s' => hl_run st s' t

/-- The number of accepted lists of length L over 0..m-1, by direct recursion. -/
def hl_cnt (st : Option ℕ × Option ℕ → ℕ → Option (Option ℕ × Option ℕ)) (m : ℕ) :
    ℕ → Option ℕ × Option ℕ → ℕ
  | 0, _ => 1
  | L + 1, s =>
    ((List.range m).map (fun x =>
      match st s x with
      | none => 0
      | some s' => hl_cnt st m L s')).sum

theorem hl_cnt_eq (st : Option ℕ × Option ℕ → ℕ → Option (Option ℕ × Option ℕ)) (m : ℕ) :
    ∀ (L : ℕ) (s : Option ℕ × Option ℕ),
      hl_cnt st m L s = ((hl_lists m L).filter (fun l => hl_run st s l)).length
  | 0, s => by
      have h0 : hl_run st s [] = true := rfl
      simp [hl_cnt, hl_lists, h0]
  | L + 1, s => by
      simp only [hl_cnt, hl_lists, List.filter_flatMap, List.length_flatMap]
      congr 1
      apply List.map_congr_left
      intro x _
      rw [List.filter_map, List.length_map]
      have hc : ∀ l : List ℕ, ((fun l => hl_run st s l) ∘ fun l => x :: l) l =
          (match st s x with
            | none => false
            | some s' => hl_run st s' l) := fun l => rfl
      rw [List.filter_congr (fun l _ => hc l)]
      cases h : st s x with
      | none => simp
      | some s' => exact hl_cnt_eq st m L s'

theorem hl_count (L m : ℕ) (Q : List ℕ → Prop) [DecidablePred Q]
    (st : Option ℕ × Option ℕ → ℕ → Option (Option ℕ × Option ℕ))
    (hrun : ∀ l, Q l ↔ hl_run st (none, none) l = true) :
    ((Fintype.piFinset fun _ : Fin L => Finset.range m).filter
        (fun v => Q (List.ofFn v))).card = hl_cnt st m L (none, none) := by
  rw [hl_bridge m L Q, hl_cnt_eq]
  congr 1
  apply List.filter_congr
  intro l _
  simp only [hrun l, Bool.decide_eq_true]

theorem hl_gf_shift (s j : ℕ) (hj : s ≤ j) :
    (PowerSeries.mk fun n => (((n + s).choose j : ℕ) : ℚ)) * (1 - X) ^ (j + 1) = X ^ (j - s) := by
  have e : (PowerSeries.mk fun n => (((n + s).choose j : ℕ) : ℚ)) =
      X ^ (j - s) * (PowerSeries.mk fun n => (((j + n).choose j : ℕ) : ℚ)) := by
    ext n
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul']
    split_ifs with h
    · rw [PowerSeries.coeff_mk]
      congr 2
      omega
    · rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
  rw [e, mul_assoc, PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one, mul_one]

theorem hl_gf_one :
    (PowerSeries.mk fun n => (((n + 2).choose 1 : ℕ) : ℚ)) * (1 - X) ^ 2 = 2 - X := by
  have e : (PowerSeries.mk fun n => (((n + 2).choose 1 : ℕ) : ℚ)) =
      (PowerSeries.mk fun n => (((1 + n).choose 1 : ℕ) : ℚ)) +
        (PowerSeries.mk fun n => (((0 + n).choose 0 : ℕ) : ℚ)) := by
    ext n
    simp only [PowerSeries.coeff_mk, map_add, Nat.choose_one_right, Nat.choose_zero_right]
    push_cast
    ring
  have h1 := PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one (S := ℚ) (d := 1)
  have h0 := PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one (S := ℚ) (d := 0)
  rw [e, add_mul]
  have h0' : (PowerSeries.mk fun n => (((0 + n).choose 0 : ℕ) : ℚ)) * (1 - X) ^ 2 = 1 - X := by
    rw [show (1 - X : ℚ⟦X⟧) ^ 2 = (1 - X) ^ (0 + 1) * (1 - X) by ring, ← mul_assoc, h0, one_mul]
  rw [h0', show (1 - X : ℚ⟦X⟧) ^ 2 = (1 - X) ^ (1 + 1) by norm_num, h1]
  ring

theorem a269439_repVals_map (g : ℕ → ℕ) (hg : Function.Injective g) :
    ∀ l : List ℕ, OMA.S_oeis_a269439.repVals (l.map g) = (OMA.S_oeis_a269439.repVals l).map g
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
      have ih := a269439_repVals_map g hg (b :: t)
      simp only [List.map_cons] at ih ⊢
      simp only [OMA.S_oeis_a269439.repVals]
      rw [ih]
      by_cases h : b = a
      · subst h
        simp
      · have h' : g b ≠ g a := fun e => h (hg e)
        simp [h, h']

theorem a269439_inv (g : ℕ → ℕ) (hg : StrictMono g) (l : List ℕ) :
    ((OMA.S_oeis_a269439.repVals (l.map g)).IsChain (· ≥ ·) ↔ (OMA.S_oeis_a269439.repVals l).IsChain (· ≥ ·)) := by
  rw [a269439_repVals_map g hg.injective, List.isChain_map]
  simp only [ge_iff_le, hg.le_iff_le]

/-- Registers: the previous entry and the last repeated value. -/
def a269439_st : Option ℕ × Option ℕ → ℕ → Option (Option ℕ × Option ℕ)
  | (none, r), x => some (some x, r)
  | (some p, none), x => if x = p then some (some x, some x) else some (some x, none)
  | (some p, some r), x =>
    if x = p then (if x ≤ r then some (some x, some x) else none) else some (some x, some r)

theorem a269439_run_aux : ∀ (l : List ℕ) (p : ℕ) (r : Option ℕ),
    hl_run a269439_st (some p, r) l = true ↔ (r.toList ++ OMA.S_oeis_a269439.repVals (p :: l)).IsChain (· ≥ ·)
  | [], p, r => by
      cases r <;> simp [hl_run, OMA.S_oeis_a269439.repVals]
  | x :: t, p, r => by
      cases r with
      | none =>
        by_cases hxp : x = p
        · have ih := a269439_run_aux t x (some x)
          simp only [hl_run, a269439_st, if_pos hxp]
          rw [ih]
          subst hxp
          simp [OMA.S_oeis_a269439.repVals]
        · have ih := a269439_run_aux t x none
          simp only [hl_run, a269439_st, if_neg hxp]
          rw [ih]
          simp [OMA.S_oeis_a269439.repVals, hxp]
      | some r =>
        by_cases hxp : x = p
        · by_cases ht : x ≤ r
          · have ih := a269439_run_aux t x (some x)
            simp only [hl_run, a269439_st, if_pos hxp, if_pos ht]
            rw [ih]
            subst hxp
            simp [OMA.S_oeis_a269439.repVals, List.isChain_cons_cons, ht]
          · simp only [hl_run, a269439_st, if_pos hxp, if_neg ht]
            subst hxp
            simp [OMA.S_oeis_a269439.repVals, List.isChain_cons_cons, ht]
        · have ih := a269439_run_aux t x (some r)
          simp only [hl_run, a269439_st, if_neg hxp]
          rw [ih]
          simp [OMA.S_oeis_a269439.repVals, hxp]

theorem a269439_run (l : List ℕ) :
    (OMA.S_oeis_a269439.repVals l).IsChain (· ≥ ·) ↔ hl_run a269439_st (none, none) l = true := by
  cases l with
  | nil => simp [hl_run, OMA.S_oeis_a269439.repVals]
  | cons x t =>
    have h := a269439_run_aux t x none
    simp only [hl_run, a269439_st]
    rw [h]
    simp

theorem a269439_v0 : hl_cnt a269439_st 0 7 (none, none) = 0 := by decide +kernel
theorem a269439_v1 : hl_cnt a269439_st 1 7 (none, none) = 1 := by decide +kernel
theorem a269439_v2 : hl_cnt a269439_st 2 7 (none, none) = 92 := by decide +kernel
theorem a269439_v3 : hl_cnt a269439_st 3 7 (none, none) = 1722 := by decide +kernel
theorem a269439_v4 : hl_cnt a269439_st 4 7 (none, none) = 13868 := by decide +kernel
theorem a269439_v5 : hl_cnt a269439_st 5 7 (none, none) = 69235 := by decide +kernel
theorem a269439_v6 : hl_cnt a269439_st 6 7 (none, none) = 255576 := by decide +kernel
theorem a269439_v7 : hl_cnt a269439_st 7 7 (none, none) = 767172 := by decide +kernel

/-- The closed form of the sequence. -/
theorem a269439_formula : ∀ n : ℕ, OMA.S_oeis_a269439.a n = (n + 1).choose 1 + 90 * (n + 1).choose 2 + 1449 * (n + 1).choose 3 + 7528 * (n + 1).choose 4 + 16200 * (n + 1).choose 5 + 15120 * (n + 1).choose 6 + 5040 * (n + 1).choose 7 := by
  obtain ⟨c, hc⟩ := hl_poly 7 (fun l : List ℕ => (OMA.S_oeis_a269439.repVals l).IsChain (· ≥ ·)) a269439_inv
  have e0 := hc 0
  have e1 := hc 1
  have e2 := hc 2
  have e3 := hc 3
  have e4 := hc 4
  have e5 := hc 5
  have e6 := hc 6
  have e7 := hc 7
  rw [hl_count 7 0 (fun l : List ℕ => (OMA.S_oeis_a269439.repVals l).IsChain (· ≥ ·)) a269439_st a269439_run, a269439_v0] at e0
  rw [hl_count 7 1 (fun l : List ℕ => (OMA.S_oeis_a269439.repVals l).IsChain (· ≥ ·)) a269439_st a269439_run, a269439_v1] at e1
  rw [hl_count 7 2 (fun l : List ℕ => (OMA.S_oeis_a269439.repVals l).IsChain (· ≥ ·)) a269439_st a269439_run, a269439_v2] at e2
  rw [hl_count 7 3 (fun l : List ℕ => (OMA.S_oeis_a269439.repVals l).IsChain (· ≥ ·)) a269439_st a269439_run, a269439_v3] at e3
  rw [hl_count 7 4 (fun l : List ℕ => (OMA.S_oeis_a269439.repVals l).IsChain (· ≥ ·)) a269439_st a269439_run, a269439_v4] at e4
  rw [hl_count 7 5 (fun l : List ℕ => (OMA.S_oeis_a269439.repVals l).IsChain (· ≥ ·)) a269439_st a269439_run, a269439_v5] at e5
  rw [hl_count 7 6 (fun l : List ℕ => (OMA.S_oeis_a269439.repVals l).IsChain (· ≥ ·)) a269439_st a269439_run, a269439_v6] at e6
  rw [hl_count 7 7 (fun l : List ℕ => (OMA.S_oeis_a269439.repVals l).IsChain (· ≥ ·)) a269439_st a269439_run, a269439_v7] at e7
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at e0 e1 e2 e3 e4 e5 e6 e7
  norm_num [Nat.choose] at e0 e1 e2 e3 e4 e5 e6 e7
  have c0 : c 0 = 0 := by omega
  have c1 : c 1 = 1 := by omega
  have c2 : c 2 = 90 := by omega
  have c3 : c 3 = 1449 := by omega
  have c4 : c 4 = 7528 := by omega
  have c5 : c 5 = 16200 := by omega
  have c6 : c 6 = 15120 := by omega
  have c7 : c 7 = 5040 := by omega
  intro n
  unfold OMA.S_oeis_a269439.a
  rw [hc (n + 1)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c0, c1, c2, c3, c4, c5, c6, c7]
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a269439.main := by
  have key : (PowerSeries.mk fun n => (OMA.S_oeis_a269439.a (n + 1) : ℚ)) =
      (PowerSeries.mk fun n => (((n + 2).choose 1 : ℕ) : ℚ)) +
      90 • (PowerSeries.mk fun n => (((n + 2).choose 2 : ℕ) : ℚ)) +
      1449 • (PowerSeries.mk fun n => (((n + 2).choose 3 : ℕ) : ℚ)) +
      7528 • (PowerSeries.mk fun n => (((n + 2).choose 4 : ℕ) : ℚ)) +
      16200 • (PowerSeries.mk fun n => (((n + 2).choose 5 : ℕ) : ℚ)) +
      15120 • (PowerSeries.mk fun n => (((n + 2).choose 6 : ℕ) : ℚ)) +
      5040 • (PowerSeries.mk fun n => (((n + 2).choose 7 : ℕ) : ℚ)) := by
    ext n
    simp only [map_add, map_nsmul, PowerSeries.coeff_mk]
    rw [a269439_formula (n + 1)]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  have g1 := hl_gf_one
  have g2 := hl_gf_shift 2 2 (by norm_num)
  have g3 := hl_gf_shift 2 3 (by norm_num)
  have g4 := hl_gf_shift 2 4 (by norm_num)
  have g5 := hl_gf_shift 2 5 (by norm_num)
  have g6 := hl_gf_shift 2 6 (by norm_num)
  have g7 := hl_gf_shift 2 7 (by norm_num)
  norm_num at g2 g3 g4 g5 g6 g7
  rw [key]
  generalize (PowerSeries.mk fun n => (((n + 2).choose 1 : ℕ) : ℚ)) = G1 at g1 ⊢
  generalize (PowerSeries.mk fun n => (((n + 2).choose 2 : ℕ) : ℚ)) = G2 at g2 ⊢
  generalize (PowerSeries.mk fun n => (((n + 2).choose 3 : ℕ) : ℚ)) = G3 at g3 ⊢
  generalize (PowerSeries.mk fun n => (((n + 2).choose 4 : ℕ) : ℚ)) = G4 at g4 ⊢
  generalize (PowerSeries.mk fun n => (((n + 2).choose 5 : ℕ) : ℚ)) = G5 at g5 ⊢
  generalize (PowerSeries.mk fun n => (((n + 2).choose 6 : ℕ) : ℚ)) = G6 at g6 ⊢
  generalize (PowerSeries.mk fun n => (((n + 2).choose 7 : ℕ) : ℚ)) = G7 at g7 ⊢
  have e : (G1 + 90 • G2 + 1449 • G3 + 7528 • G4 + 16200 • G5 + 15120 • G6 + 5040 • G7) * (1 - X) ^ 8 =
      (G1 * (1 - X) ^ 2) * (1 - X) ^ 6 +
      90 * ((G2 * (1 - X) ^ 3) * (1 - X) ^ 5) +
      1449 * ((G3 * (1 - X) ^ 4) * (1 - X) ^ 4) +
      7528 * ((G4 * (1 - X) ^ 5) * (1 - X) ^ 3) +
      16200 * ((G5 * (1 - X) ^ 6) * (1 - X) ^ 2) +
      15120 * ((G6 * (1 - X) ^ 7) * (1 - X) ^ 1) +
      5040 * ((G7 * (1 - X) ^ 8)) := by
    simp only [nsmul_eq_mul]
    push_cast
    ring
  rw [e, g1, g2, g3, g4, g5, g6, g7]
  ring
