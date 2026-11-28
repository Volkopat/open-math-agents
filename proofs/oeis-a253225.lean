import OMAStatements.S_oeis_a253225

namespace OMA.S_oeis_a253225

open PowerSeries Finset


/-! ## Rows, the conditions on pairs and triples of rows -/

/-- A row. -/
abbrev Row := Fin 3 → Fin 2

/-- The conditions between two consecutive rows r (above) and s (below). -/
def Qpair (r s : Row) : Prop :=
  (∀ j j' j'' : Fin 3, j'.val = j.val + 1 → j''.val = j'.val + 1 → (min ((r j).val : ℤ) ((s j').val : ℤ) - min ((r j').val : ℤ) ((s j).val : ℤ) ≤
          min ((r j').val : ℤ) ((s j'').val : ℤ) - min ((r j'').val : ℤ) ((s j').val : ℤ)))

/-- The conditions on three consecutive rows r, s, t. -/
def Ttrip (r s t : Row) : Prop :=
  (∀ j j' : Fin 3, j'.val = j.val + 1 → (max ((r j).val : ℤ) ((s j').val : ℤ) - max ((r j').val : ℤ) ((s j).val : ℤ) ≤
          max ((s j).val : ℤ) ((t j').val : ℤ) - max ((s j').val : ℤ) ((t j).val : ℤ)))

instance : DecidableRel Qpair := fun r s => by unfold Qpair; infer_instance

instance (r s t : Row) : Decidable (Ttrip r s t) := by unfold Ttrip; infer_instance

/-- Consecutive pairs and triples of rows satisfy the conditions. -/
def Valid {m : ℕ} (x : Fin m → Row) : Prop :=
  (∀ i i' : Fin m, i'.val = i.val + 1 → Qpair (x i) (x i')) ∧
    ∀ i i' i'' : Fin m, i'.val = i.val + 1 → i''.val = i'.val + 1 → Ttrip (x i) (x i') (x i'')

instance {m : ℕ} : DecidablePred (@Valid m) := fun x => by unfold Valid; infer_instance

/-- The number of valid arrays with n + 1 rows. -/
def cnt (n : ℕ) : ℕ := ((univ : Finset (Fin (n + 1) → Row)).filter Valid).card

lemma a_eq (n : ℕ) : a n = cnt n := by
  unfold a cnt
  exact congrArg Finset.card (Finset.filter_congr (fun x _ => Iff.rfl))

lemma pair_cons {m : ℕ} (r : Row) (g : Fin (m + 1) → Row) :
    (∀ i i' : Fin (m + 2), i'.val = i.val + 1 →
      Qpair ((Fin.cons r g : Fin (m + 2) → Row) i) ((Fin.cons r g : Fin (m + 2) → Row) i')) ↔
      Qpair r (g 0) ∧ ∀ i i' : Fin (m + 1), i'.val = i.val + 1 → Qpair (g i) (g i') := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h 0 1 (by simp)
      simpa using this
    · intro i j hij
      have := h i.succ j.succ (by simp [hij])
      simpa using this
  · rintro ⟨h0, hg⟩ i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        have hj : j = 0 := by ext; simp at hij; omega
        subst hj
        simpa using h0
    | succ i =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        simp only [Fin.cons_succ]
        exact hg i j (by simp at hij; omega)

lemma trip_cons {m : ℕ} (r : Row) (g : Fin (m + 2) → Row) :
    (∀ i i' i'' : Fin (m + 3), i'.val = i.val + 1 → i''.val = i'.val + 1 →
      Ttrip ((Fin.cons r g : Fin (m + 3) → Row) i) ((Fin.cons r g : Fin (m + 3) → Row) i')
        ((Fin.cons r g : Fin (m + 3) → Row) i'')) ↔
      Ttrip r (g 0) (g 1) ∧ ∀ i i' i'' : Fin (m + 2), i'.val = i.val + 1 → i''.val = i'.val + 1 →
        Ttrip (g i) (g i') (g i'') := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h 0 (Fin.succ 0) (Fin.succ (Fin.succ 0))
        (by simp only [Fin.val_succ, Fin.val_zero]) (by simp only [Fin.val_succ, Fin.val_zero])
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.succ_zero_eq_one] at this
      exact this
    · intro i i' i'' h1 h2
      have := h i.succ i'.succ i''.succ (by simp [h1]) (by simp [h2])
      simpa using this
  · rintro ⟨h0, hg⟩ i i' i'' h1 h2
    induction i using Fin.cases with
    | zero =>
      have e1 : i' = Fin.succ 0 := Fin.ext (by simp only [Fin.val_succ, Fin.val_zero] at h1 ⊢; omega)
      have e2 : i'' = Fin.succ (Fin.succ 0) := Fin.ext (by
        rw [e1] at h2; simp only [Fin.val_succ, Fin.val_zero] at h2 ⊢; omega)
      rw [e1, e2]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.succ_zero_eq_one]
      exact h0
    | succ i =>
      induction i' using Fin.cases with
      | zero => simp at h1
      | succ i' =>
        induction i'' using Fin.cases with
        | zero => simp at h2
        | succ i'' =>
          simp only [Fin.cons_succ]
          exact hg i i' i'' (by simp at h1; omega) (by simp at h2; omega)

lemma valid_cons {m : ℕ} (r : Row) (g : Fin (m + 2) → Row) :
    Valid (Fin.cons r g : Fin (m + 3) → Row) ↔ Qpair r (g 0) ∧ Ttrip r (g 0) (g 1) ∧ Valid g := by
  unfold Valid
  rw [pair_cons, trip_cons]
  tauto

/-- W(n, r, s): valid arrays with n + 2 rows whose first two rows are r, s. -/
def W (n : ℕ) (r s : Row) : ℕ :=
  ((univ : Finset (Fin (n + 2) → Row)).filter (fun x => Valid x ∧ x 0 = r ∧ x 1 = s)).card

lemma W_zero (r s : Row) : W 0 r s = if Qpair r s then 1 else 0 := by
  unfold W
  split_ifs with hq
  · rw [Finset.card_eq_one]
    refine ⟨![r, s], ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h0, h1⟩
      funext i
      fin_cases i
      · simpa using h0
      · simpa using h1
    · rintro rfl
      refine ⟨⟨?_, ?_⟩, rfl, rfl⟩
      · intro i i' h
        fin_cases i <;> fin_cases i' <;> simp at h ⊢
        exact hq
      · intro i i' i'' h1 h2
        have := i''.isLt
        omega
  · rw [Finset.card_eq_zero]
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨hp, _⟩, h0, h1⟩
    have := hp 0 1 rfl
    rw [h0, h1] at this
    exact hq this

/-- Prepending the row r. -/
def consEmb (n : ℕ) (r : Row) : (Fin (n + 2) → Row) ↪ (Fin (n + 3) → Row) where
  toFun g := Fin.cons r g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (r : Row) (g : Fin (n + 2) → Row) :
    consEmb n r g = Fin.cons r g := rfl

lemma W_succ (n : ℕ) (r s : Row) :
    W (n + 1) r s = if Qpair r s then ∑ t : Row, (if Ttrip r s t then W n s t else 0) else 0 := by
  have e : ((univ : Finset (Fin (n + 3) → Row)).filter (fun x => Valid x ∧ x 0 = r ∧ x 1 = s)) =
      (((univ : Finset (Fin (n + 2) → Row)).filter
        (fun y => (Qpair r (y 0) ∧ Ttrip r (y 0) (y 1)) ∧ (Valid y ∧ y 0 = s))).map
          (consEmb n r)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, consEmb_apply]
    constructor
    · rintro ⟨hv, h0, h1⟩
      refine ⟨Fin.tail x, ?_, ?_⟩
      · have hx : x = Fin.cons r (Fin.tail x) := by
          rw [← h0]; exact (Fin.cons_self_tail x).symm
        rw [hx, valid_cons] at hv
        have hs : Fin.tail x 0 = s := by
          rw [← h1]; rfl
        exact ⟨⟨hv.1, hv.2.1⟩, hv.2.2, hs⟩
      · rw [← h0]; exact Fin.cons_self_tail x
    · rintro ⟨y, ⟨⟨hq, ht⟩, hv, hy0⟩, rfl⟩
      exact ⟨(valid_cons r y).2 ⟨hq, ht, hv⟩, by simp, by simpa using hy0⟩
  unfold W
  rw [e, Finset.card_map]
  split_ifs with hq
  · rw [Finset.card_eq_sum_card_fiberwise (f := fun y => y 1) (t := univ) (by simp)]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    split_ifs with ht
    · congr 1
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨_, hv, h0⟩, h1⟩
        exact ⟨hv, h0, h1⟩
      · rintro ⟨hv, h0, h1⟩
        exact ⟨⟨⟨by rw [h0]; exact hq, by rw [h0, h1]; exact ht⟩, hv, h0⟩, h1⟩
    · rw [Finset.card_eq_zero]
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨⟨⟨_, ht'⟩, _, h0⟩, h1⟩
      rw [h0, h1] at ht'
      exact ht ht'
  · rw [Finset.card_eq_zero]
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨hq', _⟩, _, h0⟩
    rw [h0] at hq'
    exact hq hq'

lemma cnt_sum (n : ℕ) : cnt (n + 1) = ∑ r : Row, ∑ s : Row, W n r s := by
  unfold cnt W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => x 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => x 1) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  congr 1
  ext x
  simp [and_assoc]

lemma sum_cons {m : ℕ} (f : (Fin (m + 1) → Fin 2) → ℕ) :
    ∑ s : Fin (m + 1) → Fin 2, f s = ∑ x : Fin 2, ∑ t : Fin m → Fin 2, f (Fin.cons x t) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 2).symm _ _
    (fun s => by simp [Fin.consEquiv, Fin.cons_self_tail])

lemma sum_row (f : Row → ℕ) :
    ∑ s : Row, f s = ∑ x0 : Fin 2, ∑ x1 : Fin 2, ∑ x2 : Fin 2, f ![x0, x1, x2] := by
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x0 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x1 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x2 _ => ?_)
  rw [Fintype.sum_unique]
  exact congrArg f (by funext j; fin_cases j <;> rfl)

/-! ## The kernel's numeric form -/

/-- The H3 condition on numbers, as a bit of a mask. -/
def gH3 (a b c d e f : ℕ) : Bool := Nat.beq (12969015850307630079 >>> (((((a * 2 + b) * 2 + c) * 2 + d) * 2 + e) * 2 + f) % 2) 1

lemma H3_iff : ∀ a b c d e f : Fin 2, ((min (a.val : ℤ) (e.val : ℤ) - min (b.val : ℤ) (d.val : ℤ) ≤
          min (b.val : ℤ) (f.val : ℤ) - min (c.val : ℤ) (e.val : ℤ))) ↔ gH3 a.val b.val c.val d.val e.val f.val = true := by
  decide +kernel

/-- The V2 condition on numbers, as a bit of a mask. -/
def gV2 (a b c d e f : ℕ) : Bool := Nat.beq (18423099089033887499 >>> (((((a * 2 + b) * 2 + c) * 2 + d) * 2 + e) * 2 + f) % 2) 1

lemma V2_iff : ∀ a b c d e f : Fin 2, ((max (a.val : ℤ) (d.val : ℤ) - max (b.val : ℤ) (c.val : ℤ) ≤
          max (c.val : ℤ) (f.val : ℤ) - max (d.val : ℤ) (e.val : ℤ))) ↔ gV2 a.val b.val c.val d.val e.val f.val = true := by
  decide +kernel

lemma Qpair_explicit (r s : Row) : Qpair r s ↔ ((min ((r 0).val : ℤ) ((s 1).val : ℤ) - min ((r 1).val : ℤ) ((s 0).val : ℤ) ≤
          min ((r 1).val : ℤ) ((s 2).val : ℤ) - min ((r 2).val : ℤ) ((s 1).val : ℤ))) := by
  unfold Qpair
  constructor
  · intro h0
    exact h0 0 1 2 rfl rfl
  · intro k0
    intro j j' j'' hj hj'
    rcases j with ⟨j, hj0⟩; rcases j' with ⟨j', hj1⟩; rcases j'' with ⟨j'', hj2⟩
    simp only at hj hj'; subst hj; subst hj'
    have hjw : j < 1 := by omega
    interval_cases j
    · exact k0

/-- Qpair on the entries of the two rows. -/
def QB (r0 r1 r2 s0 s1 s2 : ℕ) : Bool := gH3 r0 r1 r2 s0 s1 s2

lemma Q_iff (r s : Row) : Qpair r s ↔ QB (r 0).val (r 1).val (r 2).val (s 0).val (s 1).val (s 2).val = true := by
  rw [Qpair_explicit]
  simp only [QB, Bool.and_eq_true, and_assoc, H3_iff]

lemma Ttrip_explicit (r s t : Row) : Ttrip r s t ↔ ((max ((r 0).val : ℤ) ((s 1).val : ℤ) - max ((r 1).val : ℤ) ((s 0).val : ℤ) ≤
          max ((s 0).val : ℤ) ((t 1).val : ℤ) - max ((s 1).val : ℤ) ((t 0).val : ℤ))) ∧ ((max ((r 1).val : ℤ) ((s 2).val : ℤ) - max ((r 2).val : ℤ) ((s 1).val : ℤ) ≤
          max ((s 1).val : ℤ) ((t 2).val : ℤ) - max ((s 2).val : ℤ) ((t 1).val : ℤ))) := by
  unfold Ttrip
  constructor
  · intro h0
    exact ⟨h0 0 1 rfl, h0 1 2 rfl⟩
  · rintro ⟨k0, k1⟩
    intro j j' hj
    rcases j with ⟨j, hj0⟩; rcases j' with ⟨j', hj1⟩
    simp only at hj; subst hj
    have hjw : j < 2 := by omega
    interval_cases j
    · exact k0
    · exact k1

/-- The sum of f over 0, ..., 1. -/
def sumK (f : ℕ → ℕ) : ℕ := f 0 + f 1

lemma sumK_fin (f : ℕ → ℕ) : ∑ x : Fin 2, f x.val = sumK f := by
  rw [Fin.sum_univ_eq_sum_range (fun x => f x) 2]
  simp [Finset.sum_range_succ, sumK]

/-- The concatenation of f over 0, ..., 1. -/
def catK (f : ℕ → List ℕ) : List ℕ := f 0 ++ f 1

/-- The code of a row: its entries as base-K digits, r 0 the most significant. -/
def code (r : Row) : ℕ := ((r 0).val * 2 + (r 1).val) * 2 + (r 2).val

lemma code_lt (r : Row) : code r < 8 := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; omega

lemma dig0 (r : Row) : code r / 4 % 2 = (r 0).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; omega

lemma dig1 (r : Row) : code r / 2 % 2 = (r 1).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; omega

lemma dig2 (r : Row) : code r % 2 = (r 2).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; omega

/-- The sum of g over all row codes. -/
def Ts (g : ℕ → ℕ) : ℕ := sumK (fun x0 => sumK (fun x1 => sumK (fun x2 => g ((x0 * 2 + x1) * 2 + x2))))

lemma total (g : ℕ → ℕ) : (∑ s : Row, g (code s)) = Ts g := by
  rw [sum_row]
  simp only [code, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ]
  unfold Ts
  simp only [← sumK_fin]

def N2 (g : ℕ → ℕ) (r0 r1 r2 s0 s1 s2 : ℕ) (p2 p1 acc : ℕ) : ℕ :=
  sumK (fun x => bif gV2 r1 r2 s1 s2 p1 x then g (acc * 2 + x) else 0)

def N1 (g : ℕ → ℕ) (r0 r1 r2 s0 s1 s2 : ℕ) (p2 p1 acc : ℕ) : ℕ :=
  sumK (fun x => bif gV2 r0 r1 s0 s1 p1 x then N2 g r0 r1 r2 s0 s1 s2 p1 x (acc * 2 + x) else 0)

def M2 (r0 r1 r2 s0 s1 s2 : ℕ) (p2 p1 acc : ℕ) : List ℕ :=
  catK (fun x => bif gV2 r1 r2 s1 s2 p1 x then [acc * 2 + x] else [])

def M1 (r0 r1 r2 s0 s1 s2 : ℕ) (p2 p1 acc : ℕ) : List ℕ :=
  catK (fun x => bif gV2 r0 r1 s0 s1 p1 x then M2 r0 r1 r2 s0 s1 s2 p1 x (acc * 2 + x) else [])

/-- The sum of g over the codes of the rows t with T r s t. -/
def Tn (g : ℕ → ℕ) (r0 r1 r2 s0 s1 s2 : ℕ) : ℕ := sumK (fun x => N1 g r0 r1 r2 s0 s1 s2 0 x x)

/-- The codes of the rows t with T r s t. -/
def Tl (r0 r1 r2 s0 s1 s2 : ℕ) : List ℕ := catK (fun x => M1 r0 r1 r2 s0 s1 s2 0 x x)

lemma N2_list (g : ℕ → ℕ) (r0 r1 r2 s0 s1 s2 p2 p1 acc : ℕ) :
    N2 g r0 r1 r2 s0 s1 s2 p2 p1 acc = ((M2 r0 r1 r2 s0 s1 s2 p2 p1 acc).map g).sum := by
  unfold N2 M2 sumK catK
  simp only [Bool.cond_eq_ite, List.map_append, List.sum_append, apply_ite (List.map g), apply_ite List.sum, List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, add_zero]

lemma N1_list (g : ℕ → ℕ) (r0 r1 r2 s0 s1 s2 p2 p1 acc : ℕ) :
    N1 g r0 r1 r2 s0 s1 s2 p2 p1 acc = ((M1 r0 r1 r2 s0 s1 s2 p2 p1 acc).map g).sum := by
  unfold N1 M1 sumK catK
  simp only [Bool.cond_eq_ite, List.map_append, List.sum_append, apply_ite (List.map g), apply_ite List.sum, List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, add_zero, N2_list]

lemma Tn_list (g : ℕ → ℕ) (r0 r1 r2 s0 s1 s2 : ℕ) : Tn g r0 r1 r2 s0 s1 s2 = ((Tl r0 r1 r2 s0 s1 s2).map g).sum := by
  unfold Tn Tl sumK catK
  simp only [List.map_append, List.sum_append, N1_list]

lemma bridge (g : ℕ → ℕ) (r s : Row) :
    (∑ t : Row, if Ttrip r s t then g (code t) else 0) = Tn g (r 0).val (r 1).val (r 2).val (s 0).val (s 1).val (s 2).val := by
  rw [sum_row]
  simp only [Ttrip_explicit, V2_iff, code, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ]
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
  unfold Tn N1 N2
  simp only [Bool.cond_eq_ite, ← sumK_fin]

/-- The code of a pair of rows. -/
def pc (r s : Row) : ℕ := code r * 8 + code s

lemma pc_lt (r s : Row) : pc r s < 64 := by
  unfold pc; have := code_lt r; have := code_lt s; nlinarith

lemma pc_div (r s : Row) : pc r s / 8 = code r := by
  unfold pc; have := code_lt s; omega

lemma pc_mod (r s : Row) : pc r s % 8 = code s := by
  unfold pc; have := code_lt s; omega

lemma total2 (g : ℕ → ℕ) :
    (∑ r : Row, ∑ s : Row, g (code r * 8 + code s)) = Ts (fun x => Ts (fun y => g (x * 8 + y))) := by
  have h : ∀ r : Row, (∑ s : Row, g (code r * 8 + code s)) = Ts (fun y => g (code r * 8 + y)) :=
    fun r => total (fun y => g (code r * 8 + y))
  simp only [h]
  exact total (fun x => Ts (fun y => g (x * 8 + y)))

/-- W(0, r, s), by the pair code. -/
def L0 : List ℕ := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1,
    1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1,
    1, 0, 1]

def tab0 (c : ℕ) : ℕ := L0.getD c 0

def t0 (r s : Row) : ℕ := tab0 (pc r s)

/-- W(1, r, s), by the pair code. -/
def L1 : List ℕ := [4, 0, 0, 0, 4, 0, 7, 5, 6, 1, 0, 0, 4, 2, 0, 0, 2, 0, 4, 3, 2, 0, 7, 5, 6, 2, 0, 3, 4, 2, 7,
    5, 1, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 4, 2, 0, 0, 1, 0, 0, 3, 2, 0, 7, 5, 4, 1, 0, 0, 4,
    2, 0, 5]

def tab1 (c : ℕ) : ℕ := L1.getD c 0

def t1 (r s : Row) : ℕ := tab1 (pc r s)

/-- W(2, r, s), by the pair code. -/
def L2 : List ℕ := [9, 0, 0, 0, 5, 0, 18, 16, 16, 1, 0, 0, 5, 2, 0, 0, 0, 0, 19, 15, 0, 0, 18, 16, 13, 3, 0, 15,
    5, 2, 18, 16, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 5, 2, 0, 0, 0, 0, 0, 15, 0, 0, 18, 16, 9,
    1, 0, 0, 5, 2, 0, 16]

def tab2 (c : ℕ) : ℕ := L2.getD c 0

def t2 (r s : Row) : ℕ := tab2 (pc r s)

/-- W(3, r, s), by the pair code. -/
def L3 : List ℕ := [25, 0, 0, 0, 5, 0, 49, 33, 43, 1, 0, 0, 5, 2, 0, 0, 0, 0, 68, 49, 0, 0, 49, 33, 30, 3, 0, 49,
    5, 2, 49, 33, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 5, 2, 0, 0, 0, 0, 0, 49, 0, 0, 49, 33,
    25, 1, 0, 0, 5, 2, 0, 33]

def tab3 (c : ℕ) : ℕ := L3.getD c 0

def t3 (r s : Row) : ℕ := tab3 (pc r s)

/-- W(4, r, s), by the pair code. -/
def L4 : List ℕ := [58, 0, 0, 0, 5, 0, 131, 66, 107, 1, 0, 0, 5, 2, 0, 0, 0, 0, 199, 131, 0, 0, 131, 66, 63, 3, 0,
    131, 5, 2, 131, 66, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 5, 2, 0, 0, 0, 0, 0, 131, 0, 0,
    131, 66, 58, 1, 0, 0, 5, 2, 0, 66]

def tab4 (c : ℕ) : ℕ := L4.getD c 0

def t4 (r s : Row) : ℕ := tab4 (pc r s)

/-- W(5, r, s), by the pair code. -/
def L5 : List ℕ := [124, 0, 0, 0, 5, 0, 328, 132, 255, 1, 0, 0, 5, 2, 0, 0, 0, 0, 527, 328, 0, 0, 328, 132, 129,
    3, 0, 328, 5, 2, 328, 132, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 5, 2, 0, 0, 0, 0, 0, 328, 0,
    0, 328, 132, 124, 1, 0, 0, 5, 2, 0, 132]

def tab5 (c : ℕ) : ℕ := L5.getD c 0

def t5 (r s : Row) : ℕ := tab5 (pc r s)

/-- W(6, r, s), by the pair code. -/
def L6 : List ℕ := [256, 0, 0, 0, 5, 0, 788, 264, 584, 1, 0, 0, 5, 2, 0, 0, 0, 0, 1315, 788, 0, 0, 788, 264, 261,
    3, 0, 788, 5, 2, 788, 264, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 5, 2, 0, 0, 0, 0, 0, 788, 0,
    0, 788, 264, 256, 1, 0, 0, 5, 2, 0, 264]

def tab6 (c : ℕ) : ℕ := L6.getD c 0

def t6 (r s : Row) : ℕ := tab6 (pc r s)

def step0 (c : ℕ) : Bool := tab0 c == (bif QB (c / 8 / 4 % 2) (c / 8 / 2 % 2) (c / 8 % 2) (c % 8 / 4 % 2) (c % 8 / 2 % 2) (c % 8 % 2) then 1 else 0)

def step1 (c : ℕ) : Bool := tab1 c ==
  (bif QB (c / 8 / 4 % 2) (c / 8 / 2 % 2) (c / 8 % 2) (c % 8 / 4 % 2) (c % 8 / 2 % 2) (c % 8 % 2) then ((Tl (c / 8 / 4 % 2) (c / 8 / 2 % 2) (c / 8 % 2) (c % 8 / 4 % 2) (c % 8 / 2 % 2) (c % 8 % 2)).map (fun t => tab0 (c % 8 * 8 + t))).sum else 0)

def step2 (c : ℕ) : Bool := tab2 c ==
  (bif QB (c / 8 / 4 % 2) (c / 8 / 2 % 2) (c / 8 % 2) (c % 8 / 4 % 2) (c % 8 / 2 % 2) (c % 8 % 2) then ((Tl (c / 8 / 4 % 2) (c / 8 / 2 % 2) (c / 8 % 2) (c % 8 / 4 % 2) (c % 8 / 2 % 2) (c % 8 % 2)).map (fun t => tab1 (c % 8 * 8 + t))).sum else 0)

def step3 (c : ℕ) : Bool := tab3 c ==
  (bif QB (c / 8 / 4 % 2) (c / 8 / 2 % 2) (c / 8 % 2) (c % 8 / 4 % 2) (c % 8 / 2 % 2) (c % 8 % 2) then ((Tl (c / 8 / 4 % 2) (c / 8 / 2 % 2) (c / 8 % 2) (c % 8 / 4 % 2) (c % 8 / 2 % 2) (c % 8 % 2)).map (fun t => tab2 (c % 8 * 8 + t))).sum else 0)

def step4 (c : ℕ) : Bool := tab4 c ==
  (bif QB (c / 8 / 4 % 2) (c / 8 / 2 % 2) (c / 8 % 2) (c % 8 / 4 % 2) (c % 8 / 2 % 2) (c % 8 % 2) then ((Tl (c / 8 / 4 % 2) (c / 8 / 2 % 2) (c / 8 % 2) (c % 8 / 4 % 2) (c % 8 / 2 % 2) (c % 8 % 2)).map (fun t => tab3 (c % 8 * 8 + t))).sum else 0)

def step5 (c : ℕ) : Bool := tab5 c ==
  (bif QB (c / 8 / 4 % 2) (c / 8 / 2 % 2) (c / 8 % 2) (c % 8 / 4 % 2) (c % 8 / 2 % 2) (c % 8 % 2) then ((Tl (c / 8 / 4 % 2) (c / 8 / 2 % 2) (c / 8 % 2) (c % 8 / 4 % 2) (c % 8 / 2 % 2) (c % 8 % 2)).map (fun t => tab4 (c % 8 * 8 + t))).sum else 0)

def step6 (c : ℕ) : Bool := tab6 c ==
  (bif QB (c / 8 / 4 % 2) (c / 8 / 2 % 2) (c / 8 % 2) (c % 8 / 4 % 2) (c % 8 / 2 % 2) (c % 8 % 2) then ((Tl (c / 8 / 4 % 2) (c / 8 / 2 % 2) (c / 8 % 2) (c % 8 / 4 % 2) (c % 8 / 2 % 2) (c % 8 % 2)).map (fun t => tab5 (c % 8 * 8 + t))).sum else 0)

/-- The relation on the tables at the pair code c. -/
def relB (c : ℕ) : Bool := (bif QB (c / 8 / 4 % 2) (c / 8 / 2 % 2) (c / 8 % 2) (c % 8 / 4 % 2) (c % 8 / 2 % 2) (c % 8 % 2) then ((Tl (c / 8 / 4 % 2) (c / 8 / 2 % 2) (c / 8 % 2) (c % 8 / 4 % 2) (c % 8 / 2 % 2) (c % 8 % 2)).map (fun t => tab6 ((c % 8) * 8 + t))).sum else 0) + 8 * tab5 c == 5 * tab6 c + 4 * tab4 c

def rowB (c : ℕ) : Bool := step0 c && step1 c && step2 c && step3 c && step4 c && step5 c && step6 c && relB c

lemma chunk0_ok : (List.range' 0 64).all rowB = true := by
  decide +kernel

def allB : Bool := (Ts (fun x => Ts (fun y => tab0 (x * 8 + y))) == 47) && (Ts (fun x => Ts (fun y => tab1 (x * 8 + y))) == 132) && (Ts (fun x => Ts (fun y => tab2 (x * 8 + y))) == 306) && (Ts (fun x => Ts (fun y => tab3 (x * 8 + y))) == 742) && (Ts (fun x => Ts (fun y => tab4 (x * 8 + y))) == 1775) && (Ts (fun x => Ts (fun y => tab5 (x * 8 + y))) == 4158) && (Ts (fun x => Ts (fun y => tab6 (x * 8 + y))) == 9551)

lemma all_ok : allB = true := by
  decide +kernel

lemma all_parts : (Ts (fun x => Ts (fun y => tab0 (x * 8 + y))) == 47) = true ∧ (Ts (fun x => Ts (fun y => tab1 (x * 8 + y))) == 132) = true ∧ (Ts (fun x => Ts (fun y => tab2 (x * 8 + y))) == 306) = true ∧ (Ts (fun x => Ts (fun y => tab3 (x * 8 + y))) == 742) = true ∧ (Ts (fun x => Ts (fun y => tab4 (x * 8 + y))) == 1775) = true ∧ (Ts (fun x => Ts (fun y => tab5 (x * 8 + y))) == 4158) = true ∧ (Ts (fun x => Ts (fun y => tab6 (x * 8 + y))) == 9551) = true := by
  have h := all_ok
  unfold allB at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

lemma row_ok (c : ℕ) (hc : c < 64) : step0 c = true ∧ step1 c = true ∧ step2 c = true ∧ step3 c = true ∧ step4 c = true ∧ step5 c = true ∧ step6 c = true ∧ relB c = true := by
  have h : rowB c = true := by
    by_cases h0 : c < 64
    · exact List.all_eq_true.mp chunk0_ok c (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    omega
  unfold rowB at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

lemma pc_digits (r s : Row) :
    (pc r s / 8 / 4 % 2) = (r 0).val ∧ (pc r s / 8 / 2 % 2) = (r 1).val ∧ (pc r s / 8 % 2) = (r 2).val ∧ (pc r s % 8 / 4 % 2) = (s 0).val ∧ (pc r s % 8 / 2 % 2) = (s 1).val ∧ (pc r s % 8 % 2) = (s 2).val := by
  rw [pc_div, pc_mod]
  exact ⟨dig0 r, dig1 r, dig2 r, dig0 s, dig1 s, dig2 s⟩

lemma W0f (r s : Row) : W 0 r s = t0 r s := by
  rw [W_zero]
  have h := (row_ok (pc r s) (pc_lt r s)).1
  unfold step0 at h
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := pc_digits r s
  rw [e0, e1, e2, e3, e4, e5] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W1f (r s : Row) : W 1 r s = t1 r s := by
  rw [W_succ]
  simp only [W0f, t0, pc]
  rw [bridge (fun t => tab0 (code s * 8 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.1
  unfold step1 at h
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := pc_digits r s
  rw [e0, e1, e2, e3, e4, e5, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W2f (r s : Row) : W 2 r s = t2 r s := by
  rw [W_succ]
  simp only [W1f, t1, pc]
  rw [bridge (fun t => tab1 (code s * 8 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.1
  unfold step2 at h
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := pc_digits r s
  rw [e0, e1, e2, e3, e4, e5, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W3f (r s : Row) : W 3 r s = t3 r s := by
  rw [W_succ]
  simp only [W2f, t2, pc]
  rw [bridge (fun t => tab2 (code s * 8 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.1
  unfold step3 at h
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := pc_digits r s
  rw [e0, e1, e2, e3, e4, e5, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W4f (r s : Row) : W 4 r s = t4 r s := by
  rw [W_succ]
  simp only [W3f, t3, pc]
  rw [bridge (fun t => tab3 (code s * 8 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.2.1
  unfold step4 at h
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := pc_digits r s
  rw [e0, e1, e2, e3, e4, e5, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W5f (r s : Row) : W 5 r s = t5 r s := by
  rw [W_succ]
  simp only [W4f, t4, pc]
  rw [bridge (fun t => tab4 (code s * 8 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.2.2.1
  unfold step5 at h
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := pc_digits r s
  rw [e0, e1, e2, e3, e4, e5, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W6f (r s : Row) : W 6 r s = t6 r s := by
  rw [W_succ]
  simp only [W5f, t5, pc]
  rw [bridge (fun t => tab5 (code s * 8 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.2.2.2.1
  unfold step6 at h
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := pc_digits r s
  rw [e0, e1, e2, e3, e4, e5, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma rel_at (r s : Row) : (if QB (r 0).val (r 1).val (r 2).val (s 0).val (s 1).val (s 2).val = true then ((Tl (r 0).val (r 1).val (r 2).val (s 0).val (s 1).val (s 2).val).map (fun t => tab6 ((code s) * 8 + t))).sum else 0) + 8 * tab5 (pc r s) = 5 * tab6 (pc r s) + 4 * tab4 (pc r s) := by
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.2.2.2.2
  unfold relB at h
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := pc_digits r s
  rw [e0, e1, e2, e3, e4, e5, pc_mod] at h
  simp only [Bool.cond_eq_ite] at h
  exact beq_iff_eq.mp h

lemma W_rec (k : ℕ) : ∀ r s : Row, W (k + 7) r s + 8 * W (k + 5) r s = 5 * W (k + 6) r s + 4 * W (k + 4) r s := by
  induction k with
  | zero =>
    intro r s
    simp only [Nat.zero_add, W4f, W5f, W6f, t4, t5, t6]
    rw [W_succ]
    simp only [W6f, t6, pc]
    rw [bridge (fun t => tab6 (code s * 8 + t)) r s, Tn_list]
    simp only [Q_iff]
    exact rel_at r s
  | succ k ih =>
    intro r s
    rw [show k + 1 + 4 = (k + 4) + 1 from rfl, show k + 1 + 5 = (k + 5) + 1 from rfl, show k + 1 + 6 = (k + 6) + 1 from rfl, show k + 1 + 7 = (k + 7) + 1 from rfl]
    rw [W_succ (k + 4), W_succ (k + 5), W_succ (k + 6), W_succ (k + 7)]
    split_ifs with hq
    · simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      split_ifs
      · exact ih s t
      · simp
    · simp

lemma cnt_rec (k : ℕ) : cnt (k + 8) + 8 * cnt (k + 6) = 5 * cnt (k + 7) + 4 * cnt (k + 5) := by
  rw [show k + 5 = (k + 4) + 1 from rfl, show k + 6 = (k + 5) + 1 from rfl, show k + 7 = (k + 6) + 1 from rfl, show k + 8 = (k + 7) + 1 from rfl]
  simp only [cnt_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ => ?_))
  exact W_rec k r s

lemma cnt1 : cnt 1 = 47 := by
  rw [cnt_sum]
  simp only [W0f, t0, pc]
  rw [total2 tab0]
  exact beq_iff_eq.mp all_parts.1

lemma cnt2 : cnt 2 = 132 := by
  rw [cnt_sum]
  simp only [W1f, t1, pc]
  rw [total2 tab1]
  exact beq_iff_eq.mp all_parts.2.1

lemma cnt3 : cnt 3 = 306 := by
  rw [cnt_sum]
  simp only [W2f, t2, pc]
  rw [total2 tab2]
  exact beq_iff_eq.mp all_parts.2.2.1

lemma cnt4 : cnt 4 = 742 := by
  rw [cnt_sum]
  simp only [W3f, t3, pc]
  rw [total2 tab3]
  exact beq_iff_eq.mp all_parts.2.2.2.1

lemma cnt5 : cnt 5 = 1775 := by
  rw [cnt_sum]
  simp only [W4f, t4, pc]
  rw [total2 tab4]
  exact beq_iff_eq.mp all_parts.2.2.2.2.1

lemma cnt6 : cnt 6 = 4158 := by
  rw [cnt_sum]
  simp only [W5f, t5, pc]
  rw [total2 tab5]
  exact beq_iff_eq.mp all_parts.2.2.2.2.2.1

lemma cnt7 : cnt 7 = 9551 := by
  rw [cnt_sum]
  simp only [W6f, t6, pc]
  rw [total2 tab6]
  exact beq_iff_eq.mp all_parts.2.2.2.2.2.2

lemma cnt8 : cnt 8 = 21591 := by
  have h := cnt_rec 0
  simp only [Nat.zero_add] at h
  rw [cnt5, cnt6, cnt7] at h
  generalize cnt 8 = x at h ⊢
  omega

lemma a_cast (n : ℕ) : (a n : ℚ) = (cnt n : ℚ) := by
  rw [a_eq]

lemma a_rec (k : ℕ) : (a (k + 8) : ℚ) + 8 * (a (k + 6) : ℚ) = 5 * (a (k + 7) : ℚ) + 4 * (a (k + 5) : ℚ) := by
  simp only [a_cast]
  have h : cnt (k + 8) + 8 * cnt (k + 6) = 5 * cnt (k + 7) + 4 * cnt (k + 5) := by simpa only [Nat.add_assoc, Nat.reduceAdd] using cnt_rec (k + 0)
  have h' : ((cnt (k + 8) : ℕ) : ℚ) + 8 * ((cnt (k + 6) : ℕ) : ℚ) = 5 * ((cnt (k + 7) : ℕ) : ℚ) + 4 * ((cnt (k + 5) : ℕ) : ℚ) := by exact_mod_cast h
  linear_combination h'

lemma a1 : (a 1 : ℚ) = 47 := by
  rw [a_cast, cnt1]
  norm_num

lemma a2 : (a 2 : ℚ) = 132 := by
  rw [a_cast, cnt2]
  norm_num

lemma a3 : (a 3 : ℚ) = 306 := by
  rw [a_cast, cnt3]
  norm_num

lemma a4 : (a 4 : ℚ) = 742 := by
  rw [a_cast, cnt4]
  norm_num

lemma a5 : (a 5 : ℚ) = 1775 := by
  rw [a_cast, cnt5]
  norm_num

lemma a6 : (a 6 : ℚ) = 4158 := by
  rw [a_cast, cnt6]
  norm_num

lemma a7 : (a 7 : ℚ) = 9551 := by
  rw [a_cast, cnt7]
  norm_num

lemma a8 : (a 8 : ℚ) = 21591 := by
  rw [a_cast, cnt8]
  norm_num

/-- The g.f. as stated. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) * (1 - 2 * X) ^ 2) =
      X * (47 - 103 * X + 22 * X ^ 2 + 80 * X ^ 3 - 15 * X ^ 4 - 5 * X ^ 5 - 7 * X ^ 6) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) * (1 - 2 * X) ^ 2) = A - C (5 : ℚ) * (A * X ^ 1) + C (8 : ℚ) * (A * X ^ 2) - C (4 : ℚ) * (A * X ^ 3) := by
    rw [show (C (4 : ℚ) : ℚ⟦X⟧) = 4 from map_ofNat C 4, show (C (5 : ℚ) : ℚ⟦X⟧) = 5 from map_ofNat C 5, show (C (8 : ℚ) : ℚ⟦X⟧) = 8 from map_ofNat C 8]
    ring
  have e2 : (X * (47 - 103 * X + 22 * X ^ 2 + 80 * X ^ 3 - 15 * X ^ 4 - 5 * X ^ 5 - 7 * X ^ 6) : ℚ⟦X⟧) = C (47 : ℚ) * X ^ 1 - C (103 : ℚ) * X ^ 2 + C (22 : ℚ) * X ^ 3 + C (80 : ℚ) * X ^ 4 - C (15 : ℚ) * X ^ 5 - C (5 : ℚ) * X ^ 6 - C (7 : ℚ) * X ^ 7 := by
    rw [show (C (5 : ℚ) : ℚ⟦X⟧) = 5 from map_ofNat C 5, show (C (7 : ℚ) : ℚ⟦X⟧) = 7 from map_ofNat C 7, show (C (15 : ℚ) : ℚ⟦X⟧) = 15 from map_ofNat C 15, show (C (22 : ℚ) : ℚ⟦X⟧) = 22 from map_ofNat C 22, show (C (47 : ℚ) : ℚ⟦X⟧) = 47 from map_ofNat C 47, show (C (80 : ℚ) : ℚ⟦X⟧) = 80 from map_ofNat C 80, show (C (103 : ℚ) : ℚ⟦X⟧) = 103 from map_ofNat C 103]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_C, hA,
    coeff_mk]
  rcases Nat.lt_or_ge n 8 with hn | hn
  · interval_cases n <;> norm_num only [a1, a2, a3, a4, a5, a6, a7, if_true, if_false]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
    have h' := (show (a (k + 8) : ℚ) + 8 * (a (k + 6) : ℚ) = 5 * (a (k + 7) : ℚ) + 4 * (a (k + 5) : ℚ) by simpa only [Nat.add_assoc, Nat.reduceAdd] using a_rec (k + 0))
    simp only [show k + 8 - 1 = k + 7 by omega, show k + 8 - 2 = k + 6 by omega, show k + 8 - 3 = k + 5 by omega, show k + 8 - 4 = k + 4 by omega, show k + 8 - 5 = k + 3 by omega, show k + 8 - 6 = k + 2 by omega, show k + 8 - 7 = k + 1 by omega, show ¬ (k + 8 = 0) by omega, show ¬ (k + 7 = 0) by omega, show ¬ (k + 6 = 0) by omega, show ¬ (k + 5 = 0) by omega, show ¬ (k + 4 = 0) by omega, show ¬ (k + 3 = 0) by omega, show ¬ (k + 2 = 0) by omega, show ¬ (k + 1 = 0) by omega, show 1 ≤ k + 8 by omega, show 2 ≤ k + 8 by omega, show 3 ≤ k + 8 by omega, show 4 ≤ k + 8 by omega, show 5 ≤ k + 8 by omega, show 6 ≤ k + 8 by omega, show 7 ≤ k + 8 by omega, show ¬ (k + 8 = 0) by omega, show ¬ (k + 8 = 1) by omega, show ¬ (k + 8 = 2) by omega, show ¬ (k + 8 = 3) by omega, show ¬ (k + 8 = 4) by omega, show ¬ (k + 8 = 5) by omega, show ¬ (k + 8 = 6) by omega, show ¬ (k + 8 = 7) by omega, if_true, if_false]
    linear_combination h'

def closed_Q (n : ℕ) : ℚ := 19 + 377 * 2 ^ n / 64 + 627 * 2 ^ n * n / 64

lemma closed_Q_rec (m : ℕ) : closed_Q (m + 3) - 5 * closed_Q (m + 2) + 8 * closed_Q (m + 1) - 4 * closed_Q (m + 0) = 0 := by
  unfold closed_Q
  push_cast
  ring

lemma closed_key (n : ℕ) (hn : 5 ≤ n) : (a n : ℚ) = closed_Q n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 8 with h | h
    · interval_cases n
      · have hk : (a 5 : ℚ) = 1775 := by exact_mod_cast a5
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 6 : ℚ) = 4158 := by exact_mod_cast a6
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 7 : ℚ) = 9551 := by exact_mod_cast a7
        rw [hk]
        unfold closed_Q
        norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
      have hR := (show (a (m + 8) : ℚ) + 8 * (a (m + 6) : ℚ) = 5 * (a (m + 7) : ℚ) + 4 * (a (m + 5) : ℚ) by simpa only [Nat.add_assoc, Nat.reduceAdd] using a_rec (m + 0))
      have hR' : (a (m + 8) : ℚ) + 8 * (a (m + 6) : ℚ) = 5 * (a (m + 7) : ℚ) + 4 * (a (m + 5) : ℚ) := by exact_mod_cast hR
      have h1 := ih (m + 7) (by omega) (by omega)
      have h2 := ih (m + 6) (by omega) (by omega)
      have h3 := ih (m + 5) (by omega) (by omega)
      have hG := closed_Q_rec (m + 5)
      simp only [show m + 5 + 3 = m + 8 from rfl, show m + 5 + 2 = m + 7 from rfl, show m + 5 + 1 = m + 6 from rfl, show m + 5 + 0 = m + 5 from rfl] at hG
      linear_combination hR' + (-(-5 : ℚ)) * h1 + (-(8 : ℚ)) * h2 + (-(-4 : ℚ)) * h3 + (-1 : ℚ) * hG

theorem closed : ∀ n : ℕ, 4 < n → (a n : ℚ) = 19 + 377 * 2 ^ ((n : ℤ) - 6) + 627 * 2 ^ ((n : ℤ) - 6) * n := by
  intro n hn
  rw [closed_key n (by omega)]
  unfold closed_Q
  rw [zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast,
    show (2 : ℚ) ^ (6 : ℤ) = 64 by norm_num]
  ring

/-- Controls: the entry's data. -/
theorem controls : a 1 = 47 ∧ a 2 = 132 ∧ a 3 = 306 ∧ a 4 = 742 ∧ a 5 = 1775 ∧ a 6 = 4158 ∧ a 7 = 9551 ∧ a 8 = 21591 ∧ a 9 = 48179 ∧ a 10 = 106371 ∧ a 11 = 232787 ∧ a 12 = 505683 ∧ a 13 = 1091603 ∧ a 14 = 2343699 ∧ a 15 = 5008403 ∧ a 16 = 10658835 ∧ a 17 = 22601747 ∧ a 18 = 47771667 ∧ a 19 = 100679699 ∧ a 20 = 211632147 ∧ a 21 = 443809811 ∧ a 22 = 928710675 ∧ a 23 = 1939603475 ∧ a 24 = 4043571219 ∧ a 25 = 8415870995 ∧ a 26 = 17489199123 := by
  have v9 : (a 9 : ℚ) = 48179 := by
    have h := a_rec 1
    simp only [Nat.reduceAdd] at h
    rw [a6, a7, a8] at h
    linarith
  have v10 : (a 10 : ℚ) = 106371 := by
    have h := a_rec 2
    simp only [Nat.reduceAdd] at h
    rw [a7, a8, v9] at h
    linarith
  have v11 : (a 11 : ℚ) = 232787 := by
    have h := a_rec 3
    simp only [Nat.reduceAdd] at h
    rw [a8, v9, v10] at h
    linarith
  have v12 : (a 12 : ℚ) = 505683 := by
    have h := a_rec 4
    simp only [Nat.reduceAdd] at h
    rw [v9, v10, v11] at h
    linarith
  have v13 : (a 13 : ℚ) = 1091603 := by
    have h := a_rec 5
    simp only [Nat.reduceAdd] at h
    rw [v10, v11, v12] at h
    linarith
  have v14 : (a 14 : ℚ) = 2343699 := by
    have h := a_rec 6
    simp only [Nat.reduceAdd] at h
    rw [v11, v12, v13] at h
    linarith
  have v15 : (a 15 : ℚ) = 5008403 := by
    have h := a_rec 7
    simp only [Nat.reduceAdd] at h
    rw [v12, v13, v14] at h
    linarith
  have v16 : (a 16 : ℚ) = 10658835 := by
    have h := a_rec 8
    simp only [Nat.reduceAdd] at h
    rw [v13, v14, v15] at h
    linarith
  have v17 : (a 17 : ℚ) = 22601747 := by
    have h := a_rec 9
    simp only [Nat.reduceAdd] at h
    rw [v14, v15, v16] at h
    linarith
  have v18 : (a 18 : ℚ) = 47771667 := by
    have h := a_rec 10
    simp only [Nat.reduceAdd] at h
    rw [v15, v16, v17] at h
    linarith
  have v19 : (a 19 : ℚ) = 100679699 := by
    have h := a_rec 11
    simp only [Nat.reduceAdd] at h
    rw [v16, v17, v18] at h
    linarith
  have v20 : (a 20 : ℚ) = 211632147 := by
    have h := a_rec 12
    simp only [Nat.reduceAdd] at h
    rw [v17, v18, v19] at h
    linarith
  have v21 : (a 21 : ℚ) = 443809811 := by
    have h := a_rec 13
    simp only [Nat.reduceAdd] at h
    rw [v18, v19, v20] at h
    linarith
  have v22 : (a 22 : ℚ) = 928710675 := by
    have h := a_rec 14
    simp only [Nat.reduceAdd] at h
    rw [v19, v20, v21] at h
    linarith
  have v23 : (a 23 : ℚ) = 1939603475 := by
    have h := a_rec 15
    simp only [Nat.reduceAdd] at h
    rw [v20, v21, v22] at h
    linarith
  have v24 : (a 24 : ℚ) = 4043571219 := by
    have h := a_rec 16
    simp only [Nat.reduceAdd] at h
    rw [v21, v22, v23] at h
    linarith
  have v25 : (a 25 : ℚ) = 8415870995 := by
    have h := a_rec 17
    simp only [Nat.reduceAdd] at h
    rw [v22, v23, v24] at h
    linarith
  have v26 : (a 26 : ℚ) = 17489199123 := by
    have h := a_rec 18
    simp only [Nat.reduceAdd] at h
    rw [v23, v24, v25] at h
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast a1
  · exact_mod_cast a2
  · exact_mod_cast a3
  · exact_mod_cast a4
  · exact_mod_cast a5
  · exact_mod_cast a6
  · exact_mod_cast a7
  · exact_mod_cast a8
  · exact_mod_cast v9
  · exact_mod_cast v10
  · exact_mod_cast v11
  · exact_mod_cast v12
  · exact_mod_cast v13
  · exact_mod_cast v14
  · exact_mod_cast v15
  · exact_mod_cast v16
  · exact_mod_cast v17
  · exact_mod_cast v18
  · exact_mod_cast v19
  · exact_mod_cast v20
  · exact_mod_cast v21
  · exact_mod_cast v22
  · exact_mod_cast v23
  · exact_mod_cast v24
  · exact_mod_cast v25
  · exact_mod_cast v26

/-- The conjunction stated as `main`. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 2 * X) ^ 2) =
        X * (47 - 103 * X + 22 * X ^ 2 + 80 * X ^ 3 - 15 * X ^ 4 - 5 * X ^ 5 - 7 * X ^ 6) ∧
      ∀ n : ℕ, 4 < n → (a n : ℚ) = 19 + 377 * 2 ^ ((n : ℤ) - 6) + 627 * 2 ^ ((n : ℤ) - 6) * n :=
  ⟨gf, closed⟩

end OMA.S_oeis_a253225

theorem OMA.solution : type_of% @OMA.S_oeis_a253225.main :=
  OMA.S_oeis_a253225.conjecture
