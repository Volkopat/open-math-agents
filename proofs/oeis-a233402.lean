import OMAStatements.S_oeis_a233402

namespace OMA.S_oeis_a233402

open PowerSeries Finset




/-- The row sum. -/
def rs (r : Fin 2 → Fin 3) : ℕ := (r 0).val + (r 1).val

/-- The contribution of a row to the difference of the column sums. -/
def dl (w : Fin 2 → Fin 3) : ℤ := (w 1).val - (w 0).val

/-- Row w below row r: different entries in both columns, row sum not smaller. -/
def okv (r w : Fin 2 → Fin 3) : Prop := r 0 ≠ w 0 ∧ r 1 ≠ w 1 ∧ rs r ≤ rs w

/-- Row w may follow row r: w has distinct entries and lies validly below r. -/
def step (r w : Fin 2 → Fin 3) : Prop := w 0 ≠ w 1 ∧ okv r w

instance (r w : Fin 2 → Fin 3) : Decidable (step r w) := by unfold step okv; infer_instance

/-- Consecutive elements related by P. -/
def chain {m : ℕ} (P : (Fin 2 → Fin 3) → (Fin 2 → Fin 3) → Prop) (g : Fin m → Fin 2 → Fin 3) : Prop :=
  ∀ t t' : Fin m, t'.val = t.val + 1 → P (g t) (g t')

lemma chain_cons {m : ℕ} (P : (Fin 2 → Fin 3) → (Fin 2 → Fin 3) → Prop) (v : Fin 2 → Fin 3)
    (g : Fin m → Fin 2 → Fin 3) :
    chain P (Fin.cons v g : Fin (m + 1) → Fin 2 → Fin 3) ↔
      (∀ t : Fin m, t.val = 0 → P v (g t)) ∧ chain P g := by
  unfold chain
  constructor
  · intro h
    refine ⟨fun t ht => ?_, fun t t' ht => ?_⟩
    · simpa using h 0 t.succ (by simp [ht])
    · simpa using h t.succ t'.succ (by simp [ht])
  · rintro ⟨h0, h1⟩ t t' ht
    induction t using Fin.cases with
    | zero =>
      induction t' using Fin.cases with
      | zero => simp at ht
      | succ t' => simpa using h0 t' (by simpa using ht)
    | succ t =>
      induction t' using Fin.cases with
      | zero => simp at ht
      | succ t' => simpa using h1 t t' (by simpa using ht)

/-- A valid continuation by the rows g after the row r with column-sum difference d. -/
def V (r : Fin 2 → Fin 3) (d : ℤ) {m : ℕ} (g : Fin m → Fin 2 → Fin 3) : Prop :=
  (∀ t : Fin m, t.val = 0 → step r (g t)) ∧ chain step g ∧ 0 ≤ d + ∑ t, dl (g t)

instance (r : Fin 2 → Fin 3) (d : ℤ) {m : ℕ} : DecidablePred (@V r d m) := fun g => by
  unfold V chain; infer_instance

lemma V_cons (r : Fin 2 → Fin 3) (d : ℤ) {m : ℕ} (w : Fin 2 → Fin 3) (h : Fin m → Fin 2 → Fin 3) :
    V r d (Fin.cons w h : Fin (m + 1) → Fin 2 → Fin 3) ↔ step r w ∧ V w (d + dl w) h := by
  unfold V
  rw [chain_cons, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  constructor
  · rintro ⟨h0, ⟨h1, h2⟩, hs⟩
    exact ⟨by simpa using h0 0 rfl, h1, h2, by linarith⟩
  · rintro ⟨hw, h1, h2, hs⟩
    refine ⟨fun t ht => ?_, ⟨h1, h2⟩, by linarith⟩
    have e : t = 0 := Fin.ext ht
    subst e
    simpa using hw

/-- W(m, r, d): the valid continuations by m rows. -/
def W (m : ℕ) (r : Fin 2 → Fin 3) (d : ℤ) : ℕ :=
  ((univ : Finset (Fin m → Fin 2 → Fin 3)).filter (V r d)).card

lemma W_zero (r : Fin 2 → Fin 3) (d : ℤ) : W 0 r d = if 0 ≤ d then 1 else 0 := by
  have e : ∀ g : Fin 0 → Fin 2 → Fin 3, V r d g ↔ 0 ≤ d := by
    intro g
    simp [V, chain]
  unfold W
  simp only [e]
  split_ifs with hd <;> simp [hd]

lemma W_succ (m : ℕ) (r : Fin 2 → Fin 3) (d : ℤ) :
    W (m + 1) r d = ∑ w : Fin 2 → Fin 3, if step r w then W m w (d + dl w) else 0 := by
  unfold W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  split_ifs with hw
  · refine Finset.card_bij' (fun g _ => Fin.tail g) (fun g' _ => Fin.cons w g') ?_ ?_ ?_ ?_
    · intro g hg
      simp only [mem_filter, mem_univ, true_and] at hg ⊢
      have e : g = Fin.cons w (Fin.tail g) := by
        rw [← hg.2]
        exact (Fin.cons_self_tail g).symm
      have h1 := hg.1
      rw [e, V_cons] at h1
      exact h1.2
    · intro g' hg'
      simp only [mem_filter, mem_univ, true_and] at hg' ⊢
      exact ⟨(V_cons r d w g').2 ⟨hw, hg'⟩, by simp⟩
    · intro g hg
      simp only [mem_filter, mem_univ, true_and] at hg
      rw [← hg.2]
      exact Fin.cons_self_tail g
    · intro g' _
      simp
  · rw [Finset.card_eq_zero]
    ext g
    simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
    intro hg h0
    have e : g = Fin.cons w (Fin.tail g) := by
      rw [← h0]
      exact (Fin.cons_self_tail g).symm
    rw [e, V_cons] at hg
    exact hw hg.1

lemma good_cons {n : ℕ} (v : Fin 2 → Fin 3) (g : Fin n → Fin 2 → Fin 3) :
    good (Fin.cons v g : Fin (n + 1) → Fin 2 → Fin 3) ↔ v 0 ≠ v 1 ∧ V v (dl v) g := by
  have hs : ∀ f : Fin (n + 1) → Fin 2 → Fin 3,
      ((∑ i, (f i 0).val ≤ ∑ i, (f i 1).val) ↔ 0 ≤ ∑ i, dl (f i)) := by
    intro f
    unfold dl
    rw [Finset.sum_sub_distrib]
    constructor
    · intro h
      have : ((∑ i, (f i 0).val : ℕ) : ℤ) ≤ ((∑ i, (f i 1).val : ℕ) : ℤ) := by exact_mod_cast h
      push_cast at this
      linarith
    · intro h
      have : ((∑ i, (f i 0).val : ℕ) : ℤ) ≤ ((∑ i, (f i 1).val : ℕ) : ℤ) := by push_cast; linarith
      exact_mod_cast this
  have hgood : ∀ f : Fin (n + 1) → Fin 2 → Fin 3, good f ↔
      (∀ i, f i 0 ≠ f i 1) ∧ chain okv f ∧ 0 ≤ ∑ i, dl (f i) := by
    intro f
    unfold good chain okv rs
    rw [← hs f]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨fun i => h3 i 0 1 rfl, fun i i' hi => ⟨h4 i i' 0 hi, h4 i i' 1 hi, h1 i i' hi⟩,
        h2 0 1 rfl⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨fun i i' hi => (h2 i i' hi).2.2, fun j j' hj => ?_, fun i j j' hj => ?_,
        fun i i' j hi => ?_⟩
      · fin_cases j <;> fin_cases j' <;> simp_all
      · fin_cases j <;> fin_cases j' <;> simp_all
      · fin_cases j
        · exact (h2 i i' hi).1
        · exact (h2 i i' hi).2.1
  rw [hgood]
  unfold V
  rw [Fin.forall_fin_succ, chain_cons, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  unfold chain step
  constructor
  · rintro ⟨⟨hv, hg⟩, ⟨h0, h1⟩, hsum⟩
    refine ⟨hv, fun t ht => ⟨hg t, h0 t ht⟩, fun t t' ht => ⟨hg t', h1 t t' ht⟩, hsum⟩
  · rintro ⟨hv, h0, h1, hsum⟩
    refine ⟨⟨hv, fun t => ?_⟩, ⟨fun t ht => (h0 t ht).2, fun t t' ht => (h1 t t' ht).2⟩, hsum⟩
    by_cases ht : t.val = 0
    · exact (h0 t ht).1
    · obtain ⟨u, hu⟩ : ∃ u : Fin n, u.val + 1 = t.val := ⟨⟨t.val - 1, by omega⟩, by simp; omega⟩
      exact (h1 u t hu.symm).1

lemma a_eq (n : ℕ) : a n = ∑ v : Fin 2 → Fin 3, if v 0 ≠ v 1 then W n v (dl v) else 0 := by
  unfold a W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => f 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  split_ifs with hv
  · refine Finset.card_bij' (fun f _ => Fin.tail f) (fun g _ => Fin.cons v g) ?_ ?_ ?_ ?_
    · intro f hf
      simp only [mem_filter, mem_univ, true_and] at hf ⊢
      have e : f = Fin.cons v (Fin.tail f) := by
        rw [← hf.2]
        exact (Fin.cons_self_tail f).symm
      have h1 := hf.1
      rw [e, good_cons] at h1
      exact h1.2
    · intro g hg
      simp only [mem_filter, mem_univ, true_and] at hg ⊢
      exact ⟨(good_cons v g).2 ⟨hv, hg⟩, by simp⟩
    · intro f hf
      simp only [mem_filter, mem_univ, true_and] at hf
      rw [← hf.2]
      exact Fin.cons_self_tail f
    · intro g _
      simp
  · rw [Finset.card_eq_zero]
    ext f
    simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
    intro hf h0
    have e : f = Fin.cons v (Fin.tail f) := by
      rw [← h0]
      exact (Fin.cons_self_tail f).symm
    rw [e, good_cons] at hf
    exact hv hf.1

/-- The reachable states (r, d) with d in -2..2, indexed by r 0, r 1 and d + 2. -/
def reach : Fin 3 → Fin 3 → Fin 5 → Bool :=
  ![![![false, false, false, false, false], ![false, false, true, true, false], ![false, false, true, true, true]], ![![false, true, true, false, false], ![false, false, false, false, false], ![false, true, true, true, true]], ![![true, true, true, false, false], ![true, true, true, true, false], ![false, false, false, false, false]]]

/-- The index d + 2 of a difference d in -2..2. -/
def dfin (d : ℤ) : Fin 5 := ⟨(d + 2).toNat % 5, Nat.mod_lt _ (by norm_num)⟩

/-- Reachability as a Boolean, for the kernel. -/
def Rb (x y : Fin 3) (d : ℤ) : Bool := decide (-2 ≤ d ∧ d ≤ 2) && reach x y (dfin d)

/-- Reachable states. -/
def R (r : Fin 2 → Fin 3) (d : ℤ) : Prop := ∃ e : Fin 5, d = ((e : ℕ) : ℤ) - 2 ∧ reach (r 0) (r 1) e = true

lemma Rb_spec (r : Fin 2 → Fin 3) (d : ℤ) (h : Rb (r 0) (r 1) d = true) : R r d := by
  unfold Rb at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨dfin d, ?_, h3⟩
  unfold dfin
  simp only [Fin.val_mk]
  omega

def tab1 : Fin 3 → Fin 3 → Fin 5 → ℕ :=
  ![![![0, 0, 0, 0, 0], ![0, 0, 1, 2, 0], ![0, 0, 0, 1, 2]], ![![0, 2, 2, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 1]], ![![1, 2, 2, 0, 0], ![0, 1, 1, 1, 0], ![0, 0, 0, 0, 0]]]

def tab2 : Fin 3 → Fin 3 → Fin 5 → ℕ :=
  ![![![0, 0, 0, 0, 0], ![0, 0, 4, 5, 0], ![0, 0, 2, 3, 3]], ![![0, 2, 5, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 1, 1]], ![![0, 1, 3, 0, 0], ![0, 0, 1, 1, 0], ![0, 0, 0, 0, 0]]]

def tab3 : Fin 3 → Fin 3 → Fin 5 → ℕ :=
  ![![![0, 0, 0, 0, 0], ![0, 0, 3, 7, 0], ![0, 0, 0, 2, 4]], ![![0, 7, 8, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 1]], ![![2, 4, 4, 0, 0], ![0, 1, 1, 1, 0], ![0, 0, 0, 0, 0]]]

def tab4 : Fin 3 → Fin 3 → Fin 5 → ℕ :=
  ![![![0, 0, 0, 0, 0], ![0, 0, 10, 13, 0], ![0, 0, 3, 5, 5]], ![![0, 5, 12, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 1, 1, 1]], ![![0, 2, 5, 0, 0], ![0, 0, 1, 1, 0], ![0, 0, 0, 0, 0]]]

def tab5 : Fin 3 → Fin 3 → Fin 5 → ℕ :=
  ![![![0, 0, 0, 0, 0], ![0, 0, 6, 15, 0], ![0, 0, 0, 3, 6]], ![![0, 15, 18, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 1, 1]], ![![3, 6, 6, 0, 0], ![0, 1, 1, 1, 0], ![0, 0, 0, 0, 0]]]

def T1 (x y : Fin 3) (d : ℤ) : ℕ := tab1 x y (dfin d)
def T2 (x y : Fin 3) (d : ℤ) : ℕ := tab2 x y (dfin d)
def T3 (x y : Fin 3) (d : ℤ) : ℕ := tab3 x y (dfin d)
def T4 (x y : Fin 3) (d : ℤ) : ℕ := tab4 x y (dfin d)
def T5 (x y : Fin 3) (d : ℤ) : ℕ := tab5 x y (dfin d)

lemma sum_cons {j : ℕ} (G : (Fin (j + 1) → Fin 3) → ℕ) :
    ∑ v, G v = ∑ x : Fin 3, ∑ w : Fin j → Fin 3, G (Fin.cons x w) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 3) _ _ (fun p => rfl)).symm

/-- The sum over Fin 3 written out, for cheap kernel evaluation. -/
def sum3 (g : Fin 3 → ℕ) : ℕ := g 0 + g 1 + g 2

lemma sum3_eq (g : Fin 3 → ℕ) : sum3 g = ∑ x, g x := by
  unfold sum3
  rw [Fin.sum_univ_three]

/-- The sum over all rows of length j, entry by entry. -/
def nest : (j : ℕ) → ((Fin j → Fin 3) → ℕ) → ℕ
  | 0, F => F Fin.elim0
  | j + 1, F => sum3 fun x => nest j (fun w => F (Fin.cons x w))

lemma ssum_nest : ∀ (j : ℕ) (F : (Fin j → Fin 3) → ℕ), (∑ v, F v) = nest j F := by
  intro j
  induction j with
  | zero =>
    intro F
    rw [Fintype.sum_unique]
    exact congrArg F (Subsingleton.elim _ _)
  | succ j ih =>
    intro F
    rw [sum_cons]
    simp only [nest]
    rw [sum3_eq]
    exact Finset.sum_congr rfl (fun x _ => ih _)

lemma vec_eta (r : Fin 2 → Fin 3) : r = ![r 0, r 1] := by
  ext j
  fin_cases j <;> rfl

set_option maxHeartbeats 4000000 in
/-- Every kernel computation in one theorem: the closure of the reachable states, the tables
W(1), ..., W(5), and the base relation W(6) + 3 W(2) = W(0) + 3 W(4). -/
lemma check_all : ∀ (x y : Fin 3) (e : Fin 5), reach x y e = true →
    (nest 2 (fun w => if step ![x, y] w then (if Rb (w 0) (w 1) (((e : ℕ) : ℤ) - 2 + dl w) = true then 0 else 1) else 0) = 0) ∧
    (nest 2 (fun w => if step ![x, y] w then (if 0 ≤ ((e : ℕ) : ℤ) - 2 + dl w then 1 else 0) else 0) = T1 x y (((e : ℕ) : ℤ) - 2)) ∧
    (nest 2 (fun w => if step ![x, y] w then T1 (w 0) (w 1) (((e : ℕ) : ℤ) - 2 + dl w) else 0) = T2 x y (((e : ℕ) : ℤ) - 2)) ∧
    (nest 2 (fun w => if step ![x, y] w then T2 (w 0) (w 1) (((e : ℕ) : ℤ) - 2 + dl w) else 0) = T3 x y (((e : ℕ) : ℤ) - 2)) ∧
    (nest 2 (fun w => if step ![x, y] w then T3 (w 0) (w 1) (((e : ℕ) : ℤ) - 2 + dl w) else 0) = T4 x y (((e : ℕ) : ℤ) - 2)) ∧
    (nest 2 (fun w => if step ![x, y] w then T4 (w 0) (w 1) (((e : ℕ) : ℤ) - 2 + dl w) else 0) = T5 x y (((e : ℕ) : ℤ) - 2)) ∧
    (nest 2 (fun w => if step ![x, y] w then T5 (w 0) (w 1) (((e : ℕ) : ℤ) - 2 + dl w) else 0) + 3 * T2 x y (((e : ℕ) : ℤ) - 2) = (if 0 ≤ ((e : ℕ) : ℤ) - 2 then 1 else 0) + 3 * T4 x y (((e : ℕ) : ℤ) - 2)) := by
  decide +kernel

lemma R_nxt (r : Fin 2 → Fin 3) (d : ℤ) (w : Fin 2 → Fin 3) (hR : R r d) (hw : step r w) :
    R w (d + dl w) := by
  obtain ⟨e, rfl, he⟩ := hR
  have h := (check_all (r 0) (r 1) e he).1
  rw [← ssum_nest, ← vec_eta r] at h
  have h' := (Finset.sum_eq_zero_iff.mp h) w (Finset.mem_univ w)
  rw [if_pos hw] at h'
  apply Rb_spec
  by_contra hc
  rw [if_neg hc] at h'
  exact one_ne_zero h'

lemma W_succ_R (m : ℕ) (r : Fin 2 → Fin 3) (d : ℤ) (F : (Fin 2 → Fin 3) → ℤ → ℕ)
    (hF : ∀ w d', R w d' → W m w d' = F w d') (hR : R r d) :
    W (m + 1) r d = nest 2 (fun w => if step r w then F w (d + dl w) else 0) := by
  rw [W_succ, ← ssum_nest]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  split_ifs with hw
  · exact hF _ _ (R_nxt r d w hR hw)
  · rfl

lemma W1 (r : Fin 2 → Fin 3) (d : ℤ) (hR : R r d) : W 1 r d = T1 (r 0) (r 1) d := by
  rw [W_succ_R 0 r d (fun w d' => if 0 ≤ d' then 1 else 0) (fun w d' _ => W_zero w d') hR]
  obtain ⟨e, rfl, he⟩ := hR
  rw [vec_eta r]
  exact (check_all _ _ e he).2.1

lemma W2 (r : Fin 2 → Fin 3) (d : ℤ) (hR : R r d) : W 2 r d = T2 (r 0) (r 1) d := by
  rw [W_succ_R 1 r d (fun w d' => T1 (w 0) (w 1) d') W1 hR]
  obtain ⟨e, rfl, he⟩ := hR
  rw [vec_eta r]
  exact (check_all _ _ e he).2.2.1

lemma W3 (r : Fin 2 → Fin 3) (d : ℤ) (hR : R r d) : W 3 r d = T3 (r 0) (r 1) d := by
  rw [W_succ_R 2 r d (fun w d' => T2 (w 0) (w 1) d') W2 hR]
  obtain ⟨e, rfl, he⟩ := hR
  rw [vec_eta r]
  exact (check_all _ _ e he).2.2.2.1

lemma W4 (r : Fin 2 → Fin 3) (d : ℤ) (hR : R r d) : W 4 r d = T4 (r 0) (r 1) d := by
  rw [W_succ_R 3 r d (fun w d' => T3 (w 0) (w 1) d') W3 hR]
  obtain ⟨e, rfl, he⟩ := hR
  rw [vec_eta r]
  exact (check_all _ _ e he).2.2.2.2.1

lemma W5 (r : Fin 2 → Fin 3) (d : ℤ) (hR : R r d) : W 5 r d = T5 (r 0) (r 1) d := by
  rw [W_succ_R 4 r d (fun w d' => T4 (w 0) (w 1) d') W4 hR]
  obtain ⟨e, rfl, he⟩ := hR
  rw [vec_eta r]
  exact (check_all _ _ e he).2.2.2.2.2.1

lemma W_rec (n : ℕ) (r : Fin 2 → Fin 3) (d : ℤ) (hR : R r d) :
    W (n + 6) r d + 3 * W (n + 2) r d = W n r d + 3 * W (n + 4) r d := by
  induction n generalizing r d with
  | zero =>
    rw [show (0 : ℕ) + 6 = 5 + 1 from rfl, W_succ_R 5 r d (fun w d' => T5 (w 0) (w 1) d') W5 hR,
      show (0 : ℕ) + 2 = 2 from rfl, W2 r d hR, W_zero, show (0 : ℕ) + 4 = 4 from rfl, W4 r d hR]
    obtain ⟨e, rfl, he⟩ := hR
    rw [vec_eta r]
    exact (check_all _ _ e he).2.2.2.2.2.2
  | succ n ih =>
    rw [W_succ (n + 6), W_succ (n + 2), W_succ n, W_succ (n + 4)]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    by_cases hw : step r w
    · simp only [if_pos hw]
      exact ih _ _ (R_nxt r d w hR hw)
    · simp [hw]

lemma start_Rb : ∀ x y : Fin 3, x ≠ y → Rb x y (dl ![x, y]) = true := by
  decide

lemma start_R (v : Fin 2 → Fin 3) (hv : v 0 ≠ v 1) : R v (dl v) := by
  apply Rb_spec
  have h := start_Rb (v 0) (v 1) hv
  rwa [← vec_eta v] at h

lemma a_rec (n : ℕ) : a (n + 6) + 3 * a (n + 2) = a n + 3 * a (n + 4) := by
  rw [a_eq, a_eq, a_eq, a_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  split_ifs with hv
  · exact W_rec n v (dl v) (start_R v hv)
  · rfl

lemma a_0 : a 0 = 3 := by
  rw [a_eq, show (∑ v : Fin 2 → Fin 3, if v 0 ≠ v 1 then W 0 v (dl v) else 0) =
      ∑ v : Fin 2 → Fin 3, (if v 0 ≠ v 1 then (if 0 ≤ dl v then 1 else 0) else 0) from
    Finset.sum_congr rfl (fun v _ => by
      by_cases hv : v 0 ≠ v 1
      · rw [if_pos hv, if_pos hv, W_zero]
      · rw [if_neg hv, if_neg hv])]
  decide +kernel

lemma a_1 : a 1 = 9 := by
  rw [a_eq, show (∑ v : Fin 2 → Fin 3, if v 0 ≠ v 1 then W 1 v (dl v) else 0) =
      ∑ v : Fin 2 → Fin 3, (if v 0 ≠ v 1 then T1 (v 0) (v 1) (dl v) else 0) from
    Finset.sum_congr rfl (fun v _ => by
      by_cases hv : v 0 ≠ v 1
      · rw [if_pos hv, if_pos hv, W1 v _ (start_R v hv)]
      · rw [if_neg hv, if_neg hv])]
  decide +kernel

lemma a_2 : a 2 = 11 := by
  rw [a_eq, show (∑ v : Fin 2 → Fin 3, if v 0 ≠ v 1 then W 2 v (dl v) else 0) =
      ∑ v : Fin 2 → Fin 3, (if v 0 ≠ v 1 then T2 (v 0) (v 1) (dl v) else 0) from
    Finset.sum_congr rfl (fun v _ => by
      by_cases hv : v 0 ≠ v 1
      · rw [if_pos hv, if_pos hv, W2 v _ (start_R v hv)]
      · rw [if_neg hv, if_neg hv])]
  decide +kernel

lemma a_3 : a 3 = 22 := by
  rw [a_eq, show (∑ v : Fin 2 → Fin 3, if v 0 ≠ v 1 then W 3 v (dl v) else 0) =
      ∑ v : Fin 2 → Fin 3, (if v 0 ≠ v 1 then T3 (v 0) (v 1) (dl v) else 0) from
    Finset.sum_congr rfl (fun v _ => by
      by_cases hv : v 0 ≠ v 1
      · rw [if_pos hv, if_pos hv, W3 v _ (start_R v hv)]
      · rw [if_neg hv, if_neg hv])]
  decide +kernel

lemma a_4 : a 4 = 24 := by
  rw [a_eq, show (∑ v : Fin 2 → Fin 3, if v 0 ≠ v 1 then W 4 v (dl v) else 0) =
      ∑ v : Fin 2 → Fin 3, (if v 0 ≠ v 1 then T4 (v 0) (v 1) (dl v) else 0) from
    Finset.sum_congr rfl (fun v _ => by
      by_cases hv : v 0 ≠ v 1
      · rw [if_pos hv, if_pos hv, W4 v _ (start_R v hv)]
      · rw [if_neg hv, if_neg hv])]
  decide +kernel

lemma a_5 : a 5 = 41 := by
  rw [a_eq, show (∑ v : Fin 2 → Fin 3, if v 0 ≠ v 1 then W 5 v (dl v) else 0) =
      ∑ v : Fin 2 → Fin 3, (if v 0 ≠ v 1 then T5 (v 0) (v 1) (dl v) else 0) from
    Finset.sum_congr rfl (fun v _ => by
      by_cases hv : v 0 ≠ v 1
      · rw [if_pos hv, if_pos hv, W5 v _ (start_R v hv)]
      · rw [if_neg hv, if_neg hv])]
  decide +kernel

lemma a_6 : a 6 = 42 := by
  have h := a_rec 0
  simp only [Nat.zero_add, a_0, a_2, a_4] at h
  omega

/-- The closed form of the entry, as a rational function of n. -/
def c (n : ℕ) : ℚ :=
  (62 - 14 * (-1) ^ n + (50 - 6 * (-1) ^ n) * n + (11 + (-1) ^ (1 + n)) * n ^ 2) / 16

lemma c_rec (n : ℕ) : c (n + 6) + 3 * c (n + 2) = c n + 3 * c (n + 4) := by
  unfold c
  push_cast
  ring

theorem closed_all (n : ℕ) : (a n : ℚ) = c n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 6 with hn | hn
    · interval_cases n
      · rw [a_0]; unfold c; norm_num
      · rw [a_1]; unfold c; norm_num
      · rw [a_2]; unfold c; norm_num
      · rw [a_3]; unfold c; norm_num
      · rw [a_4]; unfold c; norm_num
      · rw [a_5]; unfold c; norm_num
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 6 := ⟨n - 6, by omega⟩
      have h := a_rec j
      have hq : (a (j + 6) : ℚ) + 3 * a (j + 2) = a j + 3 * a (j + 4) := by exact_mod_cast h
      have e2 := ih (j + 2) (by omega)
      have e0 := ih j (by omega)
      have e4 := ih (j + 4) (by omega)
      linear_combination hq - 3 * e2 + e0 + 3 * e4 - c_rec j

/-- Barker's closed form, for every n >= 1. -/
theorem closed_form (n : ℕ) (_hn : 1 ≤ n) : (a n : ℚ) =
    (62 - 14 * (-1) ^ n + (50 - 6 * (-1) ^ n) * n + (11 + (-1) ^ (1 + n)) * n ^ 2) / 16 :=
  closed_all n

/-- Barker's g.f. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) ^ 3 * (1 + X) ^ 3) = X * (9 + 11 * X - 5 * X ^ 2 - 9 * X ^ 3 + 2 * X ^ 4 + 3 * X ^ 5) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) ^ 3 * (1 + X) ^ 3) = A - A * X ^ 2 * C 3 + A * X ^ 4 * C 3 - A * X ^ 6 := by
    rw [show (C (3 : ℚ) : ℚ⟦X⟧) = 3 from map_ofNat C 3]
    ring
  have e2 : (X * (9 + 11 * X - 5 * X ^ 2 - 9 * X ^ 3 + 2 * X ^ 4 + 3 * X ^ 5) : ℚ⟦X⟧) =
      X ^ 1 * C 9 + X ^ 2 * C 11 - X ^ 3 * C 5 - X ^ 4 * C 9 + X ^ 5 * C 2 + X ^ 6 * C 3 := by
    rw [show (C (9 : ℚ) : ℚ⟦X⟧) = 9 from map_ofNat C 9, show (C (11 : ℚ) : ℚ⟦X⟧) = 11 from map_ofNat C 11,
      show (C (5 : ℚ) : ℚ⟦X⟧) = 5 from map_ofNat C 5, show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2,
      show (C (3 : ℚ) : ℚ⟦X⟧) = 3 from map_ofNat C 3]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | _ | _ | n
  · simp
  · simp [a_1]
  · simp [a_1, a_2]
  · simp [a_1, a_2, a_3]
    norm_num
  · simp [a_1, a_2, a_3, a_4]
    norm_num
  · simp [a_1, a_2, a_3, a_4, a_5]
    norm_num
  · simp [a_1, a_2, a_3, a_4, a_5, a_6]
    norm_num
  · have h := a_rec (n + 1)
    have hq : (a (n + 1 + 6) : ℚ) + 3 * a (n + 1 + 2) = a (n + 1) + 3 * a (n + 1 + 4) := by
      exact_mod_cast h
    simp only [show n + 1 + 6 = n + 7 by omega, show n + 1 + 2 = n + 3 by omega,
      show n + 1 + 4 = n + 5 by omega] at hq
    simp only [if_false, if_true, show ¬ (n + 7 = 0) by omega,
      show 2 ≤ n + 7 by omega, show ¬ (n + 7 - 2 = 0) by omega, show n + 7 - 2 = n + 5 by omega,
      show ¬ (n + 5 = 0) by omega,
      show 4 ≤ n + 7 by omega, show ¬ (n + 7 - 4 = 0) by omega, show n + 7 - 4 = n + 3 by omega,
      show ¬ (n + 3 = 0) by omega,
      show 6 ≤ n + 7 by omega, show ¬ (n + 7 - 6 = 0) by omega, show n + 7 - 6 = n + 1 by omega,
      show ¬ (n + 1 = 0) by omega,
      show ¬ (n + 7 = 1) by omega, show ¬ (n + 7 = 2) by omega, show ¬ (n + 7 = 3) by omega,
      show ¬ (n + 7 = 4) by omega, show ¬ (n + 7 = 5) by omega, show ¬ (n + 7 = 6) by omega]
    linear_combination hq

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) ^ 3 * (1 + X) ^ 3) = X * (9 + 11 * X - 5 * X ^ 2 - 9 * X ^ 3 + 2 * X ^ 4 + 3 * X ^ 5) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℚ) =
      (62 - 14 * (-1) ^ n + (50 - 6 * (-1) ^ n) * n + (11 + (-1) ^ (1 + n)) * n ^ 2) / 16 :=
  ⟨gf, closed_form⟩

end OMA.S_oeis_a233402

theorem OMA.solution : type_of% @OMA.S_oeis_a233402.main :=
  OMA.S_oeis_a233402.conjecture
