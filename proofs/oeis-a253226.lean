import OMAStatements.S_oeis_a253226

namespace OMA.S_oeis_a253226

open PowerSeries Finset


/-! ## Rows, the conditions on pairs and triples of rows -/

/-- A row. -/
abbrev Row := Fin 4 → Fin 2

/-- The conditions between two consecutive rows r (above) and s (below). -/
def Qpair (r s : Row) : Prop :=
  (∀ j j' j'' : Fin 4, j'.val = j.val + 1 → j''.val = j'.val + 1 → (min ((r j).val : ℤ) ((s j').val : ℤ) - min ((r j').val : ℤ) ((s j).val : ℤ) ≤
          min ((r j').val : ℤ) ((s j'').val : ℤ) - min ((r j'').val : ℤ) ((s j').val : ℤ)))

/-- The conditions on three consecutive rows r, s, t. -/
def Ttrip (r s t : Row) : Prop :=
  (∀ j j' : Fin 4, j'.val = j.val + 1 → (max ((r j).val : ℤ) ((s j').val : ℤ) - max ((r j').val : ℤ) ((s j).val : ℤ) ≤
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
    ∑ s : Row, f s = ∑ x0 : Fin 2, ∑ x1 : Fin 2, ∑ x2 : Fin 2, ∑ x3 : Fin 2, f ![x0, x1, x2, x3] := by
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x0 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x1 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x2 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x3 _ => ?_)
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
          min ((r 1).val : ℤ) ((s 2).val : ℤ) - min ((r 2).val : ℤ) ((s 1).val : ℤ))) ∧ ((min ((r 1).val : ℤ) ((s 2).val : ℤ) - min ((r 2).val : ℤ) ((s 1).val : ℤ) ≤
          min ((r 2).val : ℤ) ((s 3).val : ℤ) - min ((r 3).val : ℤ) ((s 2).val : ℤ))) := by
  unfold Qpair
  constructor
  · intro h0
    exact ⟨h0 0 1 2 rfl rfl, h0 1 2 3 rfl rfl⟩
  · rintro ⟨k0, k1⟩
    intro j j' j'' hj hj'
    rcases j with ⟨j, hj0⟩; rcases j' with ⟨j', hj1⟩; rcases j'' with ⟨j'', hj2⟩
    simp only at hj hj'; subst hj; subst hj'
    have hjw : j < 2 := by omega
    interval_cases j
    · exact k0
    · exact k1

/-- Qpair on the entries of the two rows. -/
def QB (r0 r1 r2 r3 s0 s1 s2 s3 : ℕ) : Bool := gH3 r0 r1 r2 s0 s1 s2 && gH3 r1 r2 r3 s1 s2 s3

lemma Q_iff (r s : Row) : Qpair r s ↔ QB (r 0).val (r 1).val (r 2).val (r 3).val (s 0).val (s 1).val (s 2).val (s 3).val = true := by
  rw [Qpair_explicit]
  simp only [QB, Bool.and_eq_true, and_assoc, H3_iff]

lemma Ttrip_explicit (r s t : Row) : Ttrip r s t ↔ ((max ((r 0).val : ℤ) ((s 1).val : ℤ) - max ((r 1).val : ℤ) ((s 0).val : ℤ) ≤
          max ((s 0).val : ℤ) ((t 1).val : ℤ) - max ((s 1).val : ℤ) ((t 0).val : ℤ))) ∧ ((max ((r 1).val : ℤ) ((s 2).val : ℤ) - max ((r 2).val : ℤ) ((s 1).val : ℤ) ≤
          max ((s 1).val : ℤ) ((t 2).val : ℤ) - max ((s 2).val : ℤ) ((t 1).val : ℤ))) ∧ ((max ((r 2).val : ℤ) ((s 3).val : ℤ) - max ((r 3).val : ℤ) ((s 2).val : ℤ) ≤
          max ((s 2).val : ℤ) ((t 3).val : ℤ) - max ((s 3).val : ℤ) ((t 2).val : ℤ))) := by
  unfold Ttrip
  constructor
  · intro h0
    exact ⟨h0 0 1 rfl, h0 1 2 rfl, h0 2 3 rfl⟩
  · rintro ⟨k0, k1, k2⟩
    intro j j' hj
    rcases j with ⟨j, hj0⟩; rcases j' with ⟨j', hj1⟩
    simp only at hj; subst hj
    have hjw : j < 3 := by omega
    interval_cases j
    · exact k0
    · exact k1
    · exact k2

/-- The sum of f over 0, ..., 1. -/
def sumK (f : ℕ → ℕ) : ℕ := f 0 + f 1

lemma sumK_fin (f : ℕ → ℕ) : ∑ x : Fin 2, f x.val = sumK f := by
  rw [Fin.sum_univ_eq_sum_range (fun x => f x) 2]
  simp [Finset.sum_range_succ, sumK]

/-- The concatenation of f over 0, ..., 1. -/
def catK (f : ℕ → List ℕ) : List ℕ := f 0 ++ f 1

/-- The code of a row: its entries as base-K digits, r 0 the most significant. -/
def code (r : Row) : ℕ := (((r 0).val * 2 + (r 1).val) * 2 + (r 2).val) * 2 + (r 3).val

lemma code_lt (r : Row) : code r < 16 := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; omega

lemma dig0 (r : Row) : code r / 8 % 2 = (r 0).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; omega

lemma dig1 (r : Row) : code r / 4 % 2 = (r 1).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; omega

lemma dig2 (r : Row) : code r / 2 % 2 = (r 2).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; omega

lemma dig3 (r : Row) : code r % 2 = (r 3).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; omega

/-- The sum of g over all row codes. -/
def Ts (g : ℕ → ℕ) : ℕ := sumK (fun x0 => sumK (fun x1 => sumK (fun x2 => sumK (fun x3 => g (((x0 * 2 + x1) * 2 + x2) * 2 + x3)))))

lemma total (g : ℕ → ℕ) : (∑ s : Row, g (code s)) = Ts g := by
  rw [sum_row]
  simp only [code, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ]
  unfold Ts
  simp only [← sumK_fin]

def N3 (g : ℕ → ℕ) (r0 r1 r2 r3 s0 s1 s2 s3 : ℕ) (p2 p1 acc : ℕ) : ℕ :=
  sumK (fun x => bif gV2 r2 r3 s2 s3 p1 x then g (acc * 2 + x) else 0)

def N2 (g : ℕ → ℕ) (r0 r1 r2 r3 s0 s1 s2 s3 : ℕ) (p2 p1 acc : ℕ) : ℕ :=
  sumK (fun x => bif gV2 r1 r2 s1 s2 p1 x then N3 g r0 r1 r2 r3 s0 s1 s2 s3 p1 x (acc * 2 + x) else 0)

def N1 (g : ℕ → ℕ) (r0 r1 r2 r3 s0 s1 s2 s3 : ℕ) (p2 p1 acc : ℕ) : ℕ :=
  sumK (fun x => bif gV2 r0 r1 s0 s1 p1 x then N2 g r0 r1 r2 r3 s0 s1 s2 s3 p1 x (acc * 2 + x) else 0)

def M3 (r0 r1 r2 r3 s0 s1 s2 s3 : ℕ) (p2 p1 acc : ℕ) : List ℕ :=
  catK (fun x => bif gV2 r2 r3 s2 s3 p1 x then [acc * 2 + x] else [])

def M2 (r0 r1 r2 r3 s0 s1 s2 s3 : ℕ) (p2 p1 acc : ℕ) : List ℕ :=
  catK (fun x => bif gV2 r1 r2 s1 s2 p1 x then M3 r0 r1 r2 r3 s0 s1 s2 s3 p1 x (acc * 2 + x) else [])

def M1 (r0 r1 r2 r3 s0 s1 s2 s3 : ℕ) (p2 p1 acc : ℕ) : List ℕ :=
  catK (fun x => bif gV2 r0 r1 s0 s1 p1 x then M2 r0 r1 r2 r3 s0 s1 s2 s3 p1 x (acc * 2 + x) else [])

/-- The sum of g over the codes of the rows t with T r s t. -/
def Tn (g : ℕ → ℕ) (r0 r1 r2 r3 s0 s1 s2 s3 : ℕ) : ℕ := sumK (fun x => N1 g r0 r1 r2 r3 s0 s1 s2 s3 0 x x)

/-- The codes of the rows t with T r s t. -/
def Tl (r0 r1 r2 r3 s0 s1 s2 s3 : ℕ) : List ℕ := catK (fun x => M1 r0 r1 r2 r3 s0 s1 s2 s3 0 x x)

lemma N3_list (g : ℕ → ℕ) (r0 r1 r2 r3 s0 s1 s2 s3 p2 p1 acc : ℕ) :
    N3 g r0 r1 r2 r3 s0 s1 s2 s3 p2 p1 acc = ((M3 r0 r1 r2 r3 s0 s1 s2 s3 p2 p1 acc).map g).sum := by
  unfold N3 M3 sumK catK
  simp only [Bool.cond_eq_ite, List.map_append, List.sum_append, apply_ite (List.map g), apply_ite List.sum, List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, add_zero]

lemma N2_list (g : ℕ → ℕ) (r0 r1 r2 r3 s0 s1 s2 s3 p2 p1 acc : ℕ) :
    N2 g r0 r1 r2 r3 s0 s1 s2 s3 p2 p1 acc = ((M2 r0 r1 r2 r3 s0 s1 s2 s3 p2 p1 acc).map g).sum := by
  unfold N2 M2 sumK catK
  simp only [Bool.cond_eq_ite, List.map_append, List.sum_append, apply_ite (List.map g), apply_ite List.sum, List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, add_zero, N3_list]

lemma N1_list (g : ℕ → ℕ) (r0 r1 r2 r3 s0 s1 s2 s3 p2 p1 acc : ℕ) :
    N1 g r0 r1 r2 r3 s0 s1 s2 s3 p2 p1 acc = ((M1 r0 r1 r2 r3 s0 s1 s2 s3 p2 p1 acc).map g).sum := by
  unfold N1 M1 sumK catK
  simp only [Bool.cond_eq_ite, List.map_append, List.sum_append, apply_ite (List.map g), apply_ite List.sum, List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, add_zero, N2_list]

lemma Tn_list (g : ℕ → ℕ) (r0 r1 r2 r3 s0 s1 s2 s3 : ℕ) : Tn g r0 r1 r2 r3 s0 s1 s2 s3 = ((Tl r0 r1 r2 r3 s0 s1 s2 s3).map g).sum := by
  unfold Tn Tl sumK catK
  simp only [List.map_append, List.sum_append, N1_list]

lemma bridge (g : ℕ → ℕ) (r s : Row) :
    (∑ t : Row, if Ttrip r s t then g (code t) else 0) = Tn g (r 0).val (r 1).val (r 2).val (r 3).val (s 0).val (s 1).val (s 2).val (s 3).val := by
  rw [sum_row]
  simp only [Ttrip_explicit, V2_iff, code, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ]
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
  unfold Tn N1 N2 N3
  simp only [Bool.cond_eq_ite, ← sumK_fin]

/-- The code of a pair of rows. -/
def pc (r s : Row) : ℕ := code r * 16 + code s

lemma pc_lt (r s : Row) : pc r s < 256 := by
  unfold pc; have := code_lt r; have := code_lt s; nlinarith

lemma pc_div (r s : Row) : pc r s / 16 = code r := by
  unfold pc; have := code_lt s; omega

lemma pc_mod (r s : Row) : pc r s % 16 = code s := by
  unfold pc; have := code_lt s; omega

lemma total2 (g : ℕ → ℕ) :
    (∑ r : Row, ∑ s : Row, g (code r * 16 + code s)) = Ts (fun x => Ts (fun y => g (x * 16 + y))) := by
  have h : ∀ r : Row, (∑ s : Row, g (code r * 16 + code s)) = Ts (fun y => g (code r * 16 + y)) :=
    fun r => total (fun y => g (code r * 16 + y))
  simp only [h]
  exact total (fun x => Ts (fun y => g (x * 16 + y)))

/-- W(0, r, s) for every pair, packed: base 2^1 digit number pc r s. -/
def L0 : ℕ := 0x8303cb0b330333030b0b0f0f03030f0fb383fbcb333333330b0b0f0f3333ffff

def tab0 (c : ℕ) : ℕ := L0 / 2 ^ (1 * c) % 2 ^ 1

def t0 (r s : Row) : ℕ := tab0 (pc r s)

/-- W(1, r, s) for every pair, packed: base 2^4 digit number pc r s. -/
def L1 : ℕ := 0x5000002600000015580020020000100100360004000000020006000200000001000020260000001300002402000000010000002800000002000000060000000150360026400000285803200246002002003600040024000400060002000400020000202600001039000024020000120300360028000000185806000600000005

def tab1 (c : ℕ) : ℕ := L1 / 2 ^ (4 * c) % 2 ^ 4

def t1 (r s : Row) : ℕ := tab1 (pc r s)

/-- W(2, r, s) for every pair, packed: base 2^5 digit number pc r s. -/
def L2 : ℕ := 0x9800000047000000002a9cc00100000000008000000690000000000000000000900000000000000000000100470000000000000001180000000000000000000047000000000000000000070000000000980690004790000000709cc001000096800180000006900000000aa0000000009000000000a000000000010047000000809000000118000000008c00000690004700000000329cc0900007000000000a

def tab2 (c : ℕ) : ℕ := L2 / 2 ^ (5 * c) % 2 ^ 5

def t2 (r s : Row) : ℕ := tab2 (pc r s)

/-- W(3, r, s) for every pair, packed: base 2^7 digit number pc r s. -/
def L3 : ℕ := 0x4e0000000001070000000000009d4ea40000400000000000002000000000189000000000000000000000000000900000000000000000000000000000400107000000000000000000000042000000000000000000000000000001070000000000000000000000000007000000000000004e001890000107620000000001a44ea4000040000063480000600000000018900000000000413000000000000090000000000001300000000000000040010700000000200226000000004200000000000021000000001890000107000000000000b04ea400900000070000000000001d

def tab3 (c : ℕ) : ℕ := L3 / 2 ^ (7 * c) % 2 ^ 7

def t3 (r s : Row) : ℕ := tab3 (pc r s)

/-- W(4, r, s) for every pair, packed: base 2^8 digit number pc r s. -/
def L4 : ℕ := 0x4e0000000000020700000000000001444e53000002000000000000000100000000000309000000000000000000000000000000090000000000000000000000000000000002000207000000000000000000000000020a0000000000000000000000000000000002070000000000000000000000000000000700000000000000004e00030900000207640000000000034b4e5300000200000064d3000003000000000003090000000000000b1c0000000000000009000000000000001c000000000000000002000207000000000100044d00000000020a000000000000010500000000030900000207000000000000016d4e530009000000070000000000000044

def tab4 (c : ℕ) : ℕ := L4 / 2 ^ (8 * c) % 2 ^ 8

def t4 (r s : Row) : ℕ := tab4 (pc r s)

/-- W(5, r, s) for every pair, packed: base 2^9 digit number pc r s. -/
def L5 : ℕ := 0x4e00000000000004070000000000000002924e29000000100000000000000000080000000000006090000000000000000000000000000000000090000000000000000000000000000000000000100004070000000000000000000000000000103000000000000000000000000000000000000004070000000000000000000000000000000000070000000000000000004e00006090000004075f00000000000006994e29000000100000005f7600000018000000000000609000000000000001c2500000000000000000900000000000000002500000000000000000001000040700000000000800089b0000000000103000000000000000081800000000006090000004070000000000000002e54e2900009000000007000000000000000092

def tab5 (c : ℕ) : ℕ := L5 / 2 ^ (9 * c) % 2 ^ 9

def t5 (r s : Row) : ℕ := tab5 (pc r s)

/-- W(6, r, s) for every pair, packed: base 2^10 digit number pc r s. -/
def L6 : ℕ := 0x4e0000000000000008070000000000000000052e4e143000000080000000000000000000400000000000000c090000000000000000000000000000000000000009000000000000000000000000000000000000000000800008070000000000000000000000000000000080e0000000000000000000000000000000000000000008070000000000000000000000000000000000000007000000000000000000004e00000c09000000080759800000000000000d354e14300000008000000059bd60000000c00000000000000c090000000000000000442e000000000000000000090000000000000000002e0000000000000000000000800008070000000000004000113700000000000080e00000000000000000407000000000000c090000000807000000000000000005d24e1430000900000000070000000000000000012e

def tab6 (c : ℕ) : ℕ := L6 / 2 ^ (10 * c) % 2 ^ 10

def t6 (r s : Row) : ℕ := tab6 (pc r s)

/-- W(7, r, s) for every pair, packed: base 2^11 digit number pc r s. -/
def L7 : ℕ := 0x4e000000000000000010070000000000000000000a664e09f8000000040000000000000000000002000000000000000180900000000000000000000000000000000000000000009000000000000000000000000000000000000000000000040000100700000000000000000000000000000000000404000000000000000000000000000000000000000000000010070000000000000000000000000000000000000000000700000000000000000000004e000001809000000010075540000000000000001a6d4e09f80000000400000000555edc000000060000000000000001809000000000000000000a03700000000000000000000090000000000000000000037000000000000000000000000400001007000000000000020000226f0000000000000404000000000000000000020200000000000001809000000010070000000000000000000ba94e09f800009000000000070000000000000000000266

def tab7 (c : ℕ) : ℕ := L7 / 2 ^ (11 * c) % 2 ^ 11

def t7 (r s : Row) : ℕ := tab7 (pc r s)

def step0 (c : ℕ) : Bool := tab0 c == (bif QB (c / 16 / 8 % 2) (c / 16 / 4 % 2) (c / 16 / 2 % 2) (c / 16 % 2) (c % 16 / 8 % 2) (c % 16 / 4 % 2) (c % 16 / 2 % 2) (c % 16 % 2) then 1 else 0)

def step1 (c : ℕ) : Bool := tab1 c ==
  (bif QB (c / 16 / 8 % 2) (c / 16 / 4 % 2) (c / 16 / 2 % 2) (c / 16 % 2) (c % 16 / 8 % 2) (c % 16 / 4 % 2) (c % 16 / 2 % 2) (c % 16 % 2) then ((Tl (c / 16 / 8 % 2) (c / 16 / 4 % 2) (c / 16 / 2 % 2) (c / 16 % 2) (c % 16 / 8 % 2) (c % 16 / 4 % 2) (c % 16 / 2 % 2) (c % 16 % 2)).map (fun t => tab0 (c % 16 * 16 + t))).sum else 0)

def step2 (c : ℕ) : Bool := tab2 c ==
  (bif QB (c / 16 / 8 % 2) (c / 16 / 4 % 2) (c / 16 / 2 % 2) (c / 16 % 2) (c % 16 / 8 % 2) (c % 16 / 4 % 2) (c % 16 / 2 % 2) (c % 16 % 2) then ((Tl (c / 16 / 8 % 2) (c / 16 / 4 % 2) (c / 16 / 2 % 2) (c / 16 % 2) (c % 16 / 8 % 2) (c % 16 / 4 % 2) (c % 16 / 2 % 2) (c % 16 % 2)).map (fun t => tab1 (c % 16 * 16 + t))).sum else 0)

def step3 (c : ℕ) : Bool := tab3 c ==
  (bif QB (c / 16 / 8 % 2) (c / 16 / 4 % 2) (c / 16 / 2 % 2) (c / 16 % 2) (c % 16 / 8 % 2) (c % 16 / 4 % 2) (c % 16 / 2 % 2) (c % 16 % 2) then ((Tl (c / 16 / 8 % 2) (c / 16 / 4 % 2) (c / 16 / 2 % 2) (c / 16 % 2) (c % 16 / 8 % 2) (c % 16 / 4 % 2) (c % 16 / 2 % 2) (c % 16 % 2)).map (fun t => tab2 (c % 16 * 16 + t))).sum else 0)

def step4 (c : ℕ) : Bool := tab4 c ==
  (bif QB (c / 16 / 8 % 2) (c / 16 / 4 % 2) (c / 16 / 2 % 2) (c / 16 % 2) (c % 16 / 8 % 2) (c % 16 / 4 % 2) (c % 16 / 2 % 2) (c % 16 % 2) then ((Tl (c / 16 / 8 % 2) (c / 16 / 4 % 2) (c / 16 / 2 % 2) (c / 16 % 2) (c % 16 / 8 % 2) (c % 16 / 4 % 2) (c % 16 / 2 % 2) (c % 16 % 2)).map (fun t => tab3 (c % 16 * 16 + t))).sum else 0)

def step5 (c : ℕ) : Bool := tab5 c ==
  (bif QB (c / 16 / 8 % 2) (c / 16 / 4 % 2) (c / 16 / 2 % 2) (c / 16 % 2) (c % 16 / 8 % 2) (c % 16 / 4 % 2) (c % 16 / 2 % 2) (c % 16 % 2) then ((Tl (c / 16 / 8 % 2) (c / 16 / 4 % 2) (c / 16 / 2 % 2) (c / 16 % 2) (c % 16 / 8 % 2) (c % 16 / 4 % 2) (c % 16 / 2 % 2) (c % 16 % 2)).map (fun t => tab4 (c % 16 * 16 + t))).sum else 0)

def step6 (c : ℕ) : Bool := tab6 c ==
  (bif QB (c / 16 / 8 % 2) (c / 16 / 4 % 2) (c / 16 / 2 % 2) (c / 16 % 2) (c % 16 / 8 % 2) (c % 16 / 4 % 2) (c % 16 / 2 % 2) (c % 16 % 2) then ((Tl (c / 16 / 8 % 2) (c / 16 / 4 % 2) (c / 16 / 2 % 2) (c / 16 % 2) (c % 16 / 8 % 2) (c % 16 / 4 % 2) (c % 16 / 2 % 2) (c % 16 % 2)).map (fun t => tab5 (c % 16 * 16 + t))).sum else 0)

def step7 (c : ℕ) : Bool := tab7 c ==
  (bif QB (c / 16 / 8 % 2) (c / 16 / 4 % 2) (c / 16 / 2 % 2) (c / 16 % 2) (c % 16 / 8 % 2) (c % 16 / 4 % 2) (c % 16 / 2 % 2) (c % 16 % 2) then ((Tl (c / 16 / 8 % 2) (c / 16 / 4 % 2) (c / 16 / 2 % 2) (c / 16 % 2) (c % 16 / 8 % 2) (c % 16 / 4 % 2) (c % 16 / 2 % 2) (c % 16 % 2)).map (fun t => tab6 (c % 16 * 16 + t))).sum else 0)

/-- The relation on the tables at the pair code c. -/
def relB (c : ℕ) : Bool := (bif QB (c / 16 / 8 % 2) (c / 16 / 4 % 2) (c / 16 / 2 % 2) (c / 16 % 2) (c % 16 / 8 % 2) (c % 16 / 4 % 2) (c % 16 / 2 % 2) (c % 16 % 2) then ((Tl (c / 16 / 8 % 2) (c / 16 / 4 % 2) (c / 16 / 2 % 2) (c / 16 % 2) (c % 16 / 8 % 2) (c % 16 / 4 % 2) (c % 16 / 2 % 2) (c % 16 % 2)).map (fun t => tab7 ((c % 16) * 16 + t))).sum else 0) + 9 * tab6 c + 2 * tab4 c == 5 * tab7 c + 7 * tab5 c

def rowB (c : ℕ) : Bool := step0 c && step1 c && step2 c && step3 c && step4 c && step5 c && step6 c && step7 c && relB c

lemma chunk0_ok : (List.range' 0 256).all rowB = true := by
  decide +kernel

def allB : Bool := (Ts (fun x => Ts (fun y => tab0 (x * 16 + y))) == 125) && (Ts (fun x => Ts (fun y => tab1 (x * 16 + y))) == 306) && (Ts (fun x => Ts (fun y => tab2 (x * 16 + y))) == 494) && (Ts (fun x => Ts (fun y => tab3 (x * 16 + y))) == 914) && (Ts (fun x => Ts (fun y => tab4 (x * 16 + y))) == 1709) && (Ts (fun x => Ts (fun y => tab5 (x * 16 + y))) == 3241) && (Ts (fun x => Ts (fun y => tab6 (x * 16 + y))) == 6231) && (Ts (fun x => Ts (fun y => tab7 (x * 16 + y))) == 12122)

lemma all_ok : allB = true := by
  decide +kernel

lemma all_parts : (Ts (fun x => Ts (fun y => tab0 (x * 16 + y))) == 125) = true ∧ (Ts (fun x => Ts (fun y => tab1 (x * 16 + y))) == 306) = true ∧ (Ts (fun x => Ts (fun y => tab2 (x * 16 + y))) == 494) = true ∧ (Ts (fun x => Ts (fun y => tab3 (x * 16 + y))) == 914) = true ∧ (Ts (fun x => Ts (fun y => tab4 (x * 16 + y))) == 1709) = true ∧ (Ts (fun x => Ts (fun y => tab5 (x * 16 + y))) == 3241) = true ∧ (Ts (fun x => Ts (fun y => tab6 (x * 16 + y))) == 6231) = true ∧ (Ts (fun x => Ts (fun y => tab7 (x * 16 + y))) == 12122) = true := by
  have h := all_ok
  unfold allB at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

lemma row_ok (c : ℕ) (hc : c < 256) : step0 c = true ∧ step1 c = true ∧ step2 c = true ∧ step3 c = true ∧ step4 c = true ∧ step5 c = true ∧ step6 c = true ∧ step7 c = true ∧ relB c = true := by
  have h : rowB c = true := by
    by_cases h0 : c < 256
    · exact List.all_eq_true.mp chunk0_ok c (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    omega
  unfold rowB at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

lemma pc_digits (r s : Row) :
    (pc r s / 16 / 8 % 2) = (r 0).val ∧ (pc r s / 16 / 4 % 2) = (r 1).val ∧ (pc r s / 16 / 2 % 2) = (r 2).val ∧ (pc r s / 16 % 2) = (r 3).val ∧ (pc r s % 16 / 8 % 2) = (s 0).val ∧ (pc r s % 16 / 4 % 2) = (s 1).val ∧ (pc r s % 16 / 2 % 2) = (s 2).val ∧ (pc r s % 16 % 2) = (s 3).val := by
  rw [pc_div, pc_mod]
  exact ⟨dig0 r, dig1 r, dig2 r, dig3 r, dig0 s, dig1 s, dig2 s, dig3 s⟩

lemma W0f (r s : Row) : W 0 r s = t0 r s := by
  rw [W_zero]
  have h := (row_ok (pc r s) (pc_lt r s)).1
  unfold step0 at h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := pc_digits r s
  rw [e0, e1, e2, e3, e4, e5, e6, e7] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W1f (r s : Row) : W 1 r s = t1 r s := by
  rw [W_succ]
  simp only [W0f, t0, pc]
  rw [bridge (fun t => tab0 (code s * 16 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.1
  unfold step1 at h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := pc_digits r s
  rw [e0, e1, e2, e3, e4, e5, e6, e7, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W2f (r s : Row) : W 2 r s = t2 r s := by
  rw [W_succ]
  simp only [W1f, t1, pc]
  rw [bridge (fun t => tab1 (code s * 16 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.1
  unfold step2 at h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := pc_digits r s
  rw [e0, e1, e2, e3, e4, e5, e6, e7, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W3f (r s : Row) : W 3 r s = t3 r s := by
  rw [W_succ]
  simp only [W2f, t2, pc]
  rw [bridge (fun t => tab2 (code s * 16 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.1
  unfold step3 at h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := pc_digits r s
  rw [e0, e1, e2, e3, e4, e5, e6, e7, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W4f (r s : Row) : W 4 r s = t4 r s := by
  rw [W_succ]
  simp only [W3f, t3, pc]
  rw [bridge (fun t => tab3 (code s * 16 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.2.1
  unfold step4 at h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := pc_digits r s
  rw [e0, e1, e2, e3, e4, e5, e6, e7, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W5f (r s : Row) : W 5 r s = t5 r s := by
  rw [W_succ]
  simp only [W4f, t4, pc]
  rw [bridge (fun t => tab4 (code s * 16 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.2.2.1
  unfold step5 at h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := pc_digits r s
  rw [e0, e1, e2, e3, e4, e5, e6, e7, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W6f (r s : Row) : W 6 r s = t6 r s := by
  rw [W_succ]
  simp only [W5f, t5, pc]
  rw [bridge (fun t => tab5 (code s * 16 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.2.2.2.1
  unfold step6 at h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := pc_digits r s
  rw [e0, e1, e2, e3, e4, e5, e6, e7, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W7f (r s : Row) : W 7 r s = t7 r s := by
  rw [W_succ]
  simp only [W6f, t6, pc]
  rw [bridge (fun t => tab6 (code s * 16 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.2.2.2.2.1
  unfold step7 at h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := pc_digits r s
  rw [e0, e1, e2, e3, e4, e5, e6, e7, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma rel_at (r s : Row) : (if QB (r 0).val (r 1).val (r 2).val (r 3).val (s 0).val (s 1).val (s 2).val (s 3).val = true then ((Tl (r 0).val (r 1).val (r 2).val (r 3).val (s 0).val (s 1).val (s 2).val (s 3).val).map (fun t => tab7 ((code s) * 16 + t))).sum else 0) + 9 * tab6 (pc r s) + 2 * tab4 (pc r s) = 5 * tab7 (pc r s) + 7 * tab5 (pc r s) := by
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.2.2.2.2.2
  unfold relB at h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := pc_digits r s
  rw [e0, e1, e2, e3, e4, e5, e6, e7, pc_mod] at h
  simp only [Bool.cond_eq_ite] at h
  exact beq_iff_eq.mp h

lemma W_rec (k : ℕ) : ∀ r s : Row, W (k + 8) r s + 9 * W (k + 6) r s + 2 * W (k + 4) r s = 5 * W (k + 7) r s + 7 * W (k + 5) r s := by
  induction k with
  | zero =>
    intro r s
    simp only [Nat.zero_add, W4f, W5f, W6f, W7f, t4, t5, t6, t7]
    rw [W_succ]
    simp only [W7f, t7, pc]
    rw [bridge (fun t => tab7 (code s * 16 + t)) r s, Tn_list]
    simp only [Q_iff]
    exact rel_at r s
  | succ k ih =>
    intro r s
    rw [show k + 1 + 4 = (k + 4) + 1 from rfl, show k + 1 + 5 = (k + 5) + 1 from rfl, show k + 1 + 6 = (k + 6) + 1 from rfl, show k + 1 + 7 = (k + 7) + 1 from rfl, show k + 1 + 8 = (k + 8) + 1 from rfl]
    rw [W_succ (k + 4), W_succ (k + 5), W_succ (k + 6), W_succ (k + 7), W_succ (k + 8)]
    split_ifs with hq
    · simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      split_ifs
      · exact ih s t
      · simp
    · simp

lemma cnt_rec (k : ℕ) : cnt (k + 9) + 9 * cnt (k + 7) + 2 * cnt (k + 5) = 5 * cnt (k + 8) + 7 * cnt (k + 6) := by
  rw [show k + 5 = (k + 4) + 1 from rfl, show k + 6 = (k + 5) + 1 from rfl, show k + 7 = (k + 6) + 1 from rfl, show k + 8 = (k + 7) + 1 from rfl, show k + 9 = (k + 8) + 1 from rfl]
  simp only [cnt_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ => ?_))
  exact W_rec k r s

lemma cnt1 : cnt 1 = 125 := by
  rw [cnt_sum]
  simp only [W0f, t0, pc]
  rw [total2 tab0]
  exact beq_iff_eq.mp all_parts.1

lemma cnt2 : cnt 2 = 306 := by
  rw [cnt_sum]
  simp only [W1f, t1, pc]
  rw [total2 tab1]
  exact beq_iff_eq.mp all_parts.2.1

lemma cnt3 : cnt 3 = 494 := by
  rw [cnt_sum]
  simp only [W2f, t2, pc]
  rw [total2 tab2]
  exact beq_iff_eq.mp all_parts.2.2.1

lemma cnt4 : cnt 4 = 914 := by
  rw [cnt_sum]
  simp only [W3f, t3, pc]
  rw [total2 tab3]
  exact beq_iff_eq.mp all_parts.2.2.2.1

lemma cnt5 : cnt 5 = 1709 := by
  rw [cnt_sum]
  simp only [W4f, t4, pc]
  rw [total2 tab4]
  exact beq_iff_eq.mp all_parts.2.2.2.2.1

lemma cnt6 : cnt 6 = 3241 := by
  rw [cnt_sum]
  simp only [W5f, t5, pc]
  rw [total2 tab5]
  exact beq_iff_eq.mp all_parts.2.2.2.2.2.1

lemma cnt7 : cnt 7 = 6231 := by
  rw [cnt_sum]
  simp only [W6f, t6, pc]
  rw [total2 tab6]
  exact beq_iff_eq.mp all_parts.2.2.2.2.2.2.1

lemma cnt8 : cnt 8 = 12122 := by
  rw [cnt_sum]
  simp only [W7f, t7, pc]
  rw [total2 tab7]
  exact beq_iff_eq.mp all_parts.2.2.2.2.2.2.2

lemma cnt9 : cnt 9 = 23800 := by
  have h := cnt_rec 0
  simp only [Nat.zero_add] at h
  rw [cnt5, cnt6, cnt7, cnt8] at h
  generalize cnt 9 = x at h ⊢
  omega

lemma a_cast (n : ℕ) : (a n : ℚ) = (cnt n : ℚ) := by
  rw [a_eq]

lemma a_rec (k : ℕ) : (a (k + 9) : ℚ) + 9 * (a (k + 7) : ℚ) + 2 * (a (k + 5) : ℚ) = 5 * (a (k + 8) : ℚ) + 7 * (a (k + 6) : ℚ) := by
  simp only [a_cast]
  have h : cnt (k + 9) + 9 * cnt (k + 7) + 2 * cnt (k + 5) = 5 * cnt (k + 8) + 7 * cnt (k + 6) := by simpa only [Nat.add_assoc, Nat.reduceAdd] using cnt_rec (k + 0)
  have h' : ((cnt (k + 9) : ℕ) : ℚ) + 9 * ((cnt (k + 7) : ℕ) : ℚ) + 2 * ((cnt (k + 5) : ℕ) : ℚ) = 5 * ((cnt (k + 8) : ℕ) : ℚ) + 7 * ((cnt (k + 6) : ℕ) : ℚ) := by exact_mod_cast h
  linear_combination h'

lemma a1 : (a 1 : ℚ) = 125 := by
  rw [a_cast, cnt1]
  norm_num

lemma a2 : (a 2 : ℚ) = 306 := by
  rw [a_cast, cnt2]
  norm_num

lemma a3 : (a 3 : ℚ) = 494 := by
  rw [a_cast, cnt3]
  norm_num

lemma a4 : (a 4 : ℚ) = 914 := by
  rw [a_cast, cnt4]
  norm_num

lemma a5 : (a 5 : ℚ) = 1709 := by
  rw [a_cast, cnt5]
  norm_num

lemma a6 : (a 6 : ℚ) = 3241 := by
  rw [a_cast, cnt6]
  norm_num

lemma a7 : (a 7 : ℚ) = 6231 := by
  rw [a_cast, cnt7]
  norm_num

lemma a8 : (a 8 : ℚ) = 12122 := by
  rw [a_cast, cnt8]
  norm_num

lemma a9 : (a 9 : ℚ) = 23800 := by
  rw [a_cast, cnt9]
  norm_num

/-- The g.f. as stated. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) ^ 3 * (1 - 2 * X)) =
      X * (125 - 319 * X + 89 * X ^ 2 + 323 * X ^ 3 - 307 * X ^ 4 + 76 * X ^ 5 - 3 * X ^ 6 + X ^ 7) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) ^ 3 * (1 - 2 * X)) = A - C (5 : ℚ) * (A * X ^ 1) + C (9 : ℚ) * (A * X ^ 2) - C (7 : ℚ) * (A * X ^ 3) + C (2 : ℚ) * (A * X ^ 4) := by
    rw [show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2, show (C (5 : ℚ) : ℚ⟦X⟧) = 5 from map_ofNat C 5, show (C (7 : ℚ) : ℚ⟦X⟧) = 7 from map_ofNat C 7, show (C (9 : ℚ) : ℚ⟦X⟧) = 9 from map_ofNat C 9]
    ring
  have e2 : (X * (125 - 319 * X + 89 * X ^ 2 + 323 * X ^ 3 - 307 * X ^ 4 + 76 * X ^ 5 - 3 * X ^ 6 + X ^ 7) : ℚ⟦X⟧) = C (125 : ℚ) * X ^ 1 - C (319 : ℚ) * X ^ 2 + C (89 : ℚ) * X ^ 3 + C (323 : ℚ) * X ^ 4 - C (307 : ℚ) * X ^ 5 + C (76 : ℚ) * X ^ 6 - C (3 : ℚ) * X ^ 7 + X ^ 8 := by
    rw [show (C (3 : ℚ) : ℚ⟦X⟧) = 3 from map_ofNat C 3, show (C (76 : ℚ) : ℚ⟦X⟧) = 76 from map_ofNat C 76, show (C (89 : ℚ) : ℚ⟦X⟧) = 89 from map_ofNat C 89, show (C (125 : ℚ) : ℚ⟦X⟧) = 125 from map_ofNat C 125, show (C (307 : ℚ) : ℚ⟦X⟧) = 307 from map_ofNat C 307, show (C (319 : ℚ) : ℚ⟦X⟧) = 319 from map_ofNat C 319, show (C (323 : ℚ) : ℚ⟦X⟧) = 323 from map_ofNat C 323]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_C, hA,
    coeff_mk]
  rcases Nat.lt_or_ge n 9 with hn | hn
  · interval_cases n <;> norm_num only [a1, a2, a3, a4, a5, a6, a7, a8, if_true, if_false]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
    have h' := (show (a (k + 9) : ℚ) + 9 * (a (k + 7) : ℚ) + 2 * (a (k + 5) : ℚ) = 5 * (a (k + 8) : ℚ) + 7 * (a (k + 6) : ℚ) by simpa only [Nat.add_assoc, Nat.reduceAdd] using a_rec (k + 0))
    simp only [show k + 9 - 1 = k + 8 by omega, show k + 9 - 2 = k + 7 by omega, show k + 9 - 3 = k + 6 by omega, show k + 9 - 4 = k + 5 by omega, show k + 9 - 5 = k + 4 by omega, show k + 9 - 6 = k + 3 by omega, show k + 9 - 7 = k + 2 by omega, show k + 9 - 8 = k + 1 by omega, show ¬ (k + 9 = 0) by omega, show ¬ (k + 8 = 0) by omega, show ¬ (k + 7 = 0) by omega, show ¬ (k + 6 = 0) by omega, show ¬ (k + 5 = 0) by omega, show ¬ (k + 4 = 0) by omega, show ¬ (k + 3 = 0) by omega, show ¬ (k + 2 = 0) by omega, show ¬ (k + 1 = 0) by omega, show 1 ≤ k + 9 by omega, show 2 ≤ k + 9 by omega, show 3 ≤ k + 9 by omega, show 4 ≤ k + 9 by omega, show 5 ≤ k + 9 by omega, show 6 ≤ k + 9 by omega, show 7 ≤ k + 9 by omega, show 8 ≤ k + 9 by omega, show ¬ (k + 9 = 0) by omega, show ¬ (k + 9 = 1) by omega, show ¬ (k + 9 = 2) by omega, show ¬ (k + 9 = 3) by omega, show ¬ (k + 9 = 4) by omega, show ¬ (k + 9 = 5) by omega, show ¬ (k + 9 = 6) by omega, show ¬ (k + 9 = 7) by omega, show ¬ (k + 9 = 8) by omega, if_true, if_false]
    linear_combination h'

def closed_Q (n : ℕ) : ℚ := 46 + 1443 * 2 ^ n / 32 + (13 * n) / 2 + (15 * n ^ 2) / 2

lemma closed_Q_rec (m : ℕ) : closed_Q (m + 4) - 5 * closed_Q (m + 3) + 9 * closed_Q (m + 2) - 7 * closed_Q (m + 1) + 2 * closed_Q (m + 0) = 0 := by
  unfold closed_Q
  push_cast
  ring

lemma closed_key (n : ℕ) (hn : 5 ≤ n) : (a n : ℚ) = closed_Q n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 9 with h | h
    · interval_cases n
      · have hk : (a 5 : ℚ) = 1709 := by exact_mod_cast a5
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 6 : ℚ) = 3241 := by exact_mod_cast a6
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 7 : ℚ) = 6231 := by exact_mod_cast a7
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 8 : ℚ) = 12122 := by exact_mod_cast a8
        rw [hk]
        unfold closed_Q
        norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
      have hR := (show (a (m + 9) : ℚ) + 9 * (a (m + 7) : ℚ) + 2 * (a (m + 5) : ℚ) = 5 * (a (m + 8) : ℚ) + 7 * (a (m + 6) : ℚ) by simpa only [Nat.add_assoc, Nat.reduceAdd] using a_rec (m + 0))
      have hR' : (a (m + 9) : ℚ) + 9 * (a (m + 7) : ℚ) + 2 * (a (m + 5) : ℚ) = 5 * (a (m + 8) : ℚ) + 7 * (a (m + 6) : ℚ) := by exact_mod_cast hR
      have h1 := ih (m + 8) (by omega) (by omega)
      have h2 := ih (m + 7) (by omega) (by omega)
      have h3 := ih (m + 6) (by omega) (by omega)
      have h4 := ih (m + 5) (by omega) (by omega)
      have hG := closed_Q_rec (m + 5)
      simp only [show m + 5 + 4 = m + 9 from rfl, show m + 5 + 3 = m + 8 from rfl, show m + 5 + 2 = m + 7 from rfl, show m + 5 + 1 = m + 6 from rfl, show m + 5 + 0 = m + 5 from rfl] at hG
      linear_combination hR' + (-(-5 : ℚ)) * h1 + (-(9 : ℚ)) * h2 + (-(-7 : ℚ)) * h3 + (-(2 : ℚ)) * h4 + (-1 : ℚ) * hG

theorem closed : ∀ n : ℕ, 4 < n → (a n : ℚ) = 46 + 1443 * 2 ^ (n - 5) + (13 * n) / 2 + (15 * n ^ 2) / 2 := by
  intro n hn
  rw [closed_key n (by omega)]
  unfold closed_Q
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 5 = m by omega]
  push_cast
  ring

/-- Controls: the entry's data. -/
theorem controls : a 1 = 125 ∧ a 2 = 306 ∧ a 3 = 494 ∧ a 4 = 914 ∧ a 5 = 1709 ∧ a 6 = 3241 ∧ a 7 = 6231 ∧ a 8 = 12122 ∧ a 9 = 23800 ∧ a 10 = 47037 ∧ a 11 = 93377 ∧ a 12 = 185908 ∧ a 13 = 370806 ∧ a 14 = 740423 ∧ a 15 = 1479463 ∧ a 16 = 2957334 ∧ a 17 = 5912852 ∧ a 18 = 11823649 ∧ a 19 = 23644989 ∧ a 20 = 47287400 ∧ a 21 = 94571938 ∧ a 22 = 189140715 ∧ a 23 = 378277955 ∧ a 24 = 756552106 ∧ a 25 = 1513100064 ∧ a 26 = 3026195621 ∧ a 27 = 6052386361 := by
  have v10 : (a 10 : ℚ) = 47037 := by
    have h := a_rec 1
    simp only [Nat.reduceAdd] at h
    rw [a6, a7, a8, a9] at h
    linarith
  have v11 : (a 11 : ℚ) = 93377 := by
    have h := a_rec 2
    simp only [Nat.reduceAdd] at h
    rw [a7, a8, a9, v10] at h
    linarith
  have v12 : (a 12 : ℚ) = 185908 := by
    have h := a_rec 3
    simp only [Nat.reduceAdd] at h
    rw [a8, a9, v10, v11] at h
    linarith
  have v13 : (a 13 : ℚ) = 370806 := by
    have h := a_rec 4
    simp only [Nat.reduceAdd] at h
    rw [a9, v10, v11, v12] at h
    linarith
  have v14 : (a 14 : ℚ) = 740423 := by
    have h := a_rec 5
    simp only [Nat.reduceAdd] at h
    rw [v10, v11, v12, v13] at h
    linarith
  have v15 : (a 15 : ℚ) = 1479463 := by
    have h := a_rec 6
    simp only [Nat.reduceAdd] at h
    rw [v11, v12, v13, v14] at h
    linarith
  have v16 : (a 16 : ℚ) = 2957334 := by
    have h := a_rec 7
    simp only [Nat.reduceAdd] at h
    rw [v12, v13, v14, v15] at h
    linarith
  have v17 : (a 17 : ℚ) = 5912852 := by
    have h := a_rec 8
    simp only [Nat.reduceAdd] at h
    rw [v13, v14, v15, v16] at h
    linarith
  have v18 : (a 18 : ℚ) = 11823649 := by
    have h := a_rec 9
    simp only [Nat.reduceAdd] at h
    rw [v14, v15, v16, v17] at h
    linarith
  have v19 : (a 19 : ℚ) = 23644989 := by
    have h := a_rec 10
    simp only [Nat.reduceAdd] at h
    rw [v15, v16, v17, v18] at h
    linarith
  have v20 : (a 20 : ℚ) = 47287400 := by
    have h := a_rec 11
    simp only [Nat.reduceAdd] at h
    rw [v16, v17, v18, v19] at h
    linarith
  have v21 : (a 21 : ℚ) = 94571938 := by
    have h := a_rec 12
    simp only [Nat.reduceAdd] at h
    rw [v17, v18, v19, v20] at h
    linarith
  have v22 : (a 22 : ℚ) = 189140715 := by
    have h := a_rec 13
    simp only [Nat.reduceAdd] at h
    rw [v18, v19, v20, v21] at h
    linarith
  have v23 : (a 23 : ℚ) = 378277955 := by
    have h := a_rec 14
    simp only [Nat.reduceAdd] at h
    rw [v19, v20, v21, v22] at h
    linarith
  have v24 : (a 24 : ℚ) = 756552106 := by
    have h := a_rec 15
    simp only [Nat.reduceAdd] at h
    rw [v20, v21, v22, v23] at h
    linarith
  have v25 : (a 25 : ℚ) = 1513100064 := by
    have h := a_rec 16
    simp only [Nat.reduceAdd] at h
    rw [v21, v22, v23, v24] at h
    linarith
  have v26 : (a 26 : ℚ) = 3026195621 := by
    have h := a_rec 17
    simp only [Nat.reduceAdd] at h
    rw [v22, v23, v24, v25] at h
    linarith
  have v27 : (a 27 : ℚ) = 6052386361 := by
    have h := a_rec 18
    simp only [Nat.reduceAdd] at h
    rw [v23, v24, v25, v26] at h
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast a1
  · exact_mod_cast a2
  · exact_mod_cast a3
  · exact_mod_cast a4
  · exact_mod_cast a5
  · exact_mod_cast a6
  · exact_mod_cast a7
  · exact_mod_cast a8
  · exact_mod_cast a9
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
  · exact_mod_cast v27

/-- The conjunction stated as `main`. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) ^ 3 * (1 - 2 * X)) =
        X * (125 - 319 * X + 89 * X ^ 2 + 323 * X ^ 3 - 307 * X ^ 4 + 76 * X ^ 5 - 3 * X ^ 6 + X ^ 7) ∧
      ∀ n : ℕ, 4 < n → (a n : ℚ) = 46 + 1443 * 2 ^ (n - 5) + (13 * n) / 2 + (15 * n ^ 2) / 2 :=
  ⟨gf, closed⟩

end OMA.S_oeis_a253226

theorem OMA.solution : type_of% @OMA.S_oeis_a253226.main :=
  OMA.S_oeis_a253226.conjecture
