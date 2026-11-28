import OMAStatements.S_oeis_a253227

namespace OMA.S_oeis_a253227

open PowerSeries Finset


/-! ## Rows, the conditions on pairs and triples of rows -/

/-- A row. -/
abbrev Row := Fin 5 → Fin 2

/-- The conditions between two consecutive rows r (above) and s (below). -/
def Qpair (r s : Row) : Prop :=
  (∀ j j' j'' : Fin 5, j'.val = j.val + 1 → j''.val = j'.val + 1 → (min ((r j).val : ℤ) ((s j').val : ℤ) - min ((r j').val : ℤ) ((s j).val : ℤ) ≤
          min ((r j').val : ℤ) ((s j'').val : ℤ) - min ((r j'').val : ℤ) ((s j').val : ℤ)))

/-- The conditions on three consecutive rows r, s, t. -/
def Ttrip (r s t : Row) : Prop :=
  (∀ j j' : Fin 5, j'.val = j.val + 1 → (max ((r j).val : ℤ) ((s j').val : ℤ) - max ((r j').val : ℤ) ((s j).val : ℤ) ≤
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
    ∑ s : Row, f s = ∑ x0 : Fin 2, ∑ x1 : Fin 2, ∑ x2 : Fin 2, ∑ x3 : Fin 2, ∑ x4 : Fin 2, f ![x0, x1, x2, x3, x4] := by
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x0 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x1 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x2 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x3 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x4 _ => ?_)
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
          min ((r 2).val : ℤ) ((s 3).val : ℤ) - min ((r 3).val : ℤ) ((s 2).val : ℤ))) ∧ ((min ((r 2).val : ℤ) ((s 3).val : ℤ) - min ((r 3).val : ℤ) ((s 2).val : ℤ) ≤
          min ((r 3).val : ℤ) ((s 4).val : ℤ) - min ((r 4).val : ℤ) ((s 3).val : ℤ))) := by
  unfold Qpair
  constructor
  · intro h0
    exact ⟨h0 0 1 2 rfl rfl, h0 1 2 3 rfl rfl, h0 2 3 4 rfl rfl⟩
  · rintro ⟨k0, k1, k2⟩
    intro j j' j'' hj hj'
    rcases j with ⟨j, hj0⟩; rcases j' with ⟨j', hj1⟩; rcases j'' with ⟨j'', hj2⟩
    simp only at hj hj'; subst hj; subst hj'
    have hjw : j < 3 := by omega
    interval_cases j
    · exact k0
    · exact k1
    · exact k2

/-- Qpair on the entries of the two rows. -/
def QB (r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 : ℕ) : Bool := gH3 r0 r1 r2 s0 s1 s2 && gH3 r1 r2 r3 s1 s2 s3 && gH3 r2 r3 r4 s2 s3 s4

lemma Q_iff (r s : Row) : Qpair r s ↔ QB (r 0).val (r 1).val (r 2).val (r 3).val (r 4).val (s 0).val (s 1).val (s 2).val (s 3).val (s 4).val = true := by
  rw [Qpair_explicit]
  simp only [QB, Bool.and_eq_true, and_assoc, H3_iff]

lemma Ttrip_explicit (r s t : Row) : Ttrip r s t ↔ ((max ((r 0).val : ℤ) ((s 1).val : ℤ) - max ((r 1).val : ℤ) ((s 0).val : ℤ) ≤
          max ((s 0).val : ℤ) ((t 1).val : ℤ) - max ((s 1).val : ℤ) ((t 0).val : ℤ))) ∧ ((max ((r 1).val : ℤ) ((s 2).val : ℤ) - max ((r 2).val : ℤ) ((s 1).val : ℤ) ≤
          max ((s 1).val : ℤ) ((t 2).val : ℤ) - max ((s 2).val : ℤ) ((t 1).val : ℤ))) ∧ ((max ((r 2).val : ℤ) ((s 3).val : ℤ) - max ((r 3).val : ℤ) ((s 2).val : ℤ) ≤
          max ((s 2).val : ℤ) ((t 3).val : ℤ) - max ((s 3).val : ℤ) ((t 2).val : ℤ))) ∧ ((max ((r 3).val : ℤ) ((s 4).val : ℤ) - max ((r 4).val : ℤ) ((s 3).val : ℤ) ≤
          max ((s 3).val : ℤ) ((t 4).val : ℤ) - max ((s 4).val : ℤ) ((t 3).val : ℤ))) := by
  unfold Ttrip
  constructor
  · intro h0
    exact ⟨h0 0 1 rfl, h0 1 2 rfl, h0 2 3 rfl, h0 3 4 rfl⟩
  · rintro ⟨k0, k1, k2, k3⟩
    intro j j' hj
    rcases j with ⟨j, hj0⟩; rcases j' with ⟨j', hj1⟩
    simp only at hj; subst hj
    have hjw : j < 4 := by omega
    interval_cases j
    · exact k0
    · exact k1
    · exact k2
    · exact k3

/-- The sum of f over 0, ..., 1. -/
def sumK (f : ℕ → ℕ) : ℕ := f 0 + f 1

lemma sumK_fin (f : ℕ → ℕ) : ∑ x : Fin 2, f x.val = sumK f := by
  rw [Fin.sum_univ_eq_sum_range (fun x => f x) 2]
  simp [Finset.sum_range_succ, sumK]

/-- The concatenation of f over 0, ..., 1. -/
def catK (f : ℕ → List ℕ) : List ℕ := f 0 ++ f 1

/-- The code of a row: its entries as base-K digits, r 0 the most significant. -/
def code (r : Row) : ℕ := ((((r 0).val * 2 + (r 1).val) * 2 + (r 2).val) * 2 + (r 3).val) * 2 + (r 4).val

lemma code_lt (r : Row) : code r < 32 := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; have h4 := (r 4).isLt; omega

lemma dig0 (r : Row) : code r / 16 % 2 = (r 0).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; have h4 := (r 4).isLt; omega

lemma dig1 (r : Row) : code r / 8 % 2 = (r 1).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; have h4 := (r 4).isLt; omega

lemma dig2 (r : Row) : code r / 4 % 2 = (r 2).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; have h4 := (r 4).isLt; omega

lemma dig3 (r : Row) : code r / 2 % 2 = (r 3).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; have h4 := (r 4).isLt; omega

lemma dig4 (r : Row) : code r % 2 = (r 4).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; have h4 := (r 4).isLt; omega

/-- The sum of g over all row codes. -/
def Ts (g : ℕ → ℕ) : ℕ := sumK (fun x0 => sumK (fun x1 => sumK (fun x2 => sumK (fun x3 => sumK (fun x4 => g ((((x0 * 2 + x1) * 2 + x2) * 2 + x3) * 2 + x4))))))

lemma total (g : ℕ → ℕ) : (∑ s : Row, g (code s)) = Ts g := by
  rw [sum_row]
  simp only [code, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ]
  unfold Ts
  simp only [← sumK_fin]

def N4 (g : ℕ → ℕ) (r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 : ℕ) (p2 p1 acc : ℕ) : ℕ :=
  sumK (fun x => bif gV2 r3 r4 s3 s4 p1 x then g (acc * 2 + x) else 0)

def N3 (g : ℕ → ℕ) (r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 : ℕ) (p2 p1 acc : ℕ) : ℕ :=
  sumK (fun x => bif gV2 r2 r3 s2 s3 p1 x then N4 g r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 p1 x (acc * 2 + x) else 0)

def N2 (g : ℕ → ℕ) (r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 : ℕ) (p2 p1 acc : ℕ) : ℕ :=
  sumK (fun x => bif gV2 r1 r2 s1 s2 p1 x then N3 g r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 p1 x (acc * 2 + x) else 0)

def N1 (g : ℕ → ℕ) (r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 : ℕ) (p2 p1 acc : ℕ) : ℕ :=
  sumK (fun x => bif gV2 r0 r1 s0 s1 p1 x then N2 g r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 p1 x (acc * 2 + x) else 0)

def M4 (r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 : ℕ) (p2 p1 acc : ℕ) : List ℕ :=
  catK (fun x => bif gV2 r3 r4 s3 s4 p1 x then [acc * 2 + x] else [])

def M3 (r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 : ℕ) (p2 p1 acc : ℕ) : List ℕ :=
  catK (fun x => bif gV2 r2 r3 s2 s3 p1 x then M4 r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 p1 x (acc * 2 + x) else [])

def M2 (r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 : ℕ) (p2 p1 acc : ℕ) : List ℕ :=
  catK (fun x => bif gV2 r1 r2 s1 s2 p1 x then M3 r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 p1 x (acc * 2 + x) else [])

def M1 (r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 : ℕ) (p2 p1 acc : ℕ) : List ℕ :=
  catK (fun x => bif gV2 r0 r1 s0 s1 p1 x then M2 r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 p1 x (acc * 2 + x) else [])

/-- The sum of g over the codes of the rows t with T r s t. -/
def Tn (g : ℕ → ℕ) (r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 : ℕ) : ℕ := sumK (fun x => N1 g r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 0 x x)

/-- The codes of the rows t with T r s t. -/
def Tl (r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 : ℕ) : List ℕ := catK (fun x => M1 r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 0 x x)

lemma N4_list (g : ℕ → ℕ) (r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 p2 p1 acc : ℕ) :
    N4 g r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 p2 p1 acc = ((M4 r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 p2 p1 acc).map g).sum := by
  unfold N4 M4 sumK catK
  simp only [Bool.cond_eq_ite, List.map_append, List.sum_append, apply_ite (List.map g), apply_ite List.sum, List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, add_zero]

lemma N3_list (g : ℕ → ℕ) (r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 p2 p1 acc : ℕ) :
    N3 g r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 p2 p1 acc = ((M3 r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 p2 p1 acc).map g).sum := by
  unfold N3 M3 sumK catK
  simp only [Bool.cond_eq_ite, List.map_append, List.sum_append, apply_ite (List.map g), apply_ite List.sum, List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, add_zero, N4_list]

lemma N2_list (g : ℕ → ℕ) (r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 p2 p1 acc : ℕ) :
    N2 g r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 p2 p1 acc = ((M2 r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 p2 p1 acc).map g).sum := by
  unfold N2 M2 sumK catK
  simp only [Bool.cond_eq_ite, List.map_append, List.sum_append, apply_ite (List.map g), apply_ite List.sum, List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, add_zero, N3_list]

lemma N1_list (g : ℕ → ℕ) (r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 p2 p1 acc : ℕ) :
    N1 g r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 p2 p1 acc = ((M1 r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 p2 p1 acc).map g).sum := by
  unfold N1 M1 sumK catK
  simp only [Bool.cond_eq_ite, List.map_append, List.sum_append, apply_ite (List.map g), apply_ite List.sum, List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, add_zero, N2_list]

lemma Tn_list (g : ℕ → ℕ) (r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 : ℕ) : Tn g r0 r1 r2 r3 r4 s0 s1 s2 s3 s4 = ((Tl r0 r1 r2 r3 r4 s0 s1 s2 s3 s4).map g).sum := by
  unfold Tn Tl sumK catK
  simp only [List.map_append, List.sum_append, N1_list]

lemma bridge (g : ℕ → ℕ) (r s : Row) :
    (∑ t : Row, if Ttrip r s t then g (code t) else 0) = Tn g (r 0).val (r 1).val (r 2).val (r 3).val (r 4).val (s 0).val (s 1).val (s 2).val (s 3).val (s 4).val := by
  rw [sum_row]
  simp only [Ttrip_explicit, V2_iff, code, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ]
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
  unfold Tn N1 N2 N3 N4
  simp only [Bool.cond_eq_ite, ← sumK_fin]

/-- The code of a pair of rows. -/
def pc (r s : Row) : ℕ := code r * 32 + code s

lemma pc_lt (r s : Row) : pc r s < 1024 := by
  unfold pc; have := code_lt r; have := code_lt s; nlinarith

lemma pc_div (r s : Row) : pc r s / 32 = code r := by
  unfold pc; have := code_lt s; omega

lemma pc_mod (r s : Row) : pc r s % 32 = code s := by
  unfold pc; have := code_lt s; omega

lemma total2 (g : ℕ → ℕ) :
    (∑ r : Row, ∑ s : Row, g (code r * 32 + code s)) = Ts (fun x => Ts (fun y => g (x * 32 + y))) := by
  have h : ∀ r : Row, (∑ s : Row, g (code r * 32 + code s)) = Ts (fun y => g (code r * 32 + y)) :=
    fun r => total (fun y => g (code r * 32 + y))
  simp only [h]
  exact total (fun x => Ts (fun y => g (x * 32 + y)))

/-- W(0, r, s) for every pair, packed: base 2^1 digit number pc r s. -/
def L0 : ℕ := 0x80030003c00b000b30030003300300030b0b000b0f0f000f030300030f0f000f0083008300cb00cb0033003300330033000b000b000f000f0033003300ff00ff83038003cb0bc00b33033003330330030b0b0b0b0f0f0f0f030303030f0f0f0f0083008300cb00cb00330033003300330b0b0b0b0f0f0f0f33333333ffffffff

def tab0 (c : ℕ) : ℕ := L0 / 2 ^ (1 * c) % 2 ^ 1

def t0 (r s : Row) : ℕ := tab0 (pc r s)

/-- W(1, r, s) for every pair, packed: base 2^4 digit number pc r s. -/
def L1 : ℕ := 0x5000000000000028000000000000001658000000000020020000000000001001003600000000000400000000000000020006000000000002000000000000000100003039000000260000000000000013000036030000000200000000000000010000003c0000000400000000000000020000000900000002000000000000000100000000200000280000000000000014000000002400200200000000000010010000000000240004000000000000000200000000000400020000000000000001000000000000204c000000000000001300000000000024040000000000000001000000000000002c0000000000000002000000000000000800000000000000015000003900000028400000000000002a58003003000020024700000000002002003600060000000400360000000000040006000300000002000600000000000200003039000000260000202600000026000036030000000200002402000000020000003c000000040000002800000004000000090000000200000006000000020000000020000028000000001000003c000000002400200200000000120030030000000000240004000000000012000600000000000400020000000000020003000030390000204c000000000000104c000036030000240400000000000012040036003c0000002c000000000000001a58060009000000080000000000000006

def tab1 (c : ℕ) : ℕ := L1 / 2 ^ (4 * c) % 2 ^ 4

def t1 (r s : Row) : ℕ := tab1 (pc r s)

/-- W(2, r, s) for every pair, packed: base 2^5 digit number pc r s. -/
def L2 : ℕ := 0xb00000000000000000490000000000000000002bb4c000000000000100000000000000000000800000069000000000000000000000000000000000000000900000000000000000000000000000000000000001806c000000000000000000000000000000000001a400000000000000000000000000000000000000006c000000000000000000000000000000000000000c00000000000000000000000000000000000000001000000049000000000000000000000000000000118001000000000000000000000000000000000000044000000000000000000000000000000000000000400000000000000000000000000000000000000001004900000000000000000000000000000000000118000000000000000000000000000000000000000049000000000000000000000000000000000000000900000000000000000000b00000006c0000000049a8000000000000000073b4c00180000000010000af80000000000001800000069000000000000000000cf000000000000000000090000000000000000000f000000000000000000001806c000000000000000280af0000000000000001a4000000000000000002bc000000000000000000006c000000000000000000af0000000000000000000c0000000000000000000f0000000000000000000010000000490000000000080000009400000000001180010000000000000008c002000000000000000004400000000000000000022000000000000000000040000000000000000000200000000001806c000001004900000000000000008091000001a400000001180000000000000000008c00000690006c000000004900000000000000000033b4c090000c00000000090000000000000000000b

def tab2 (c : ℕ) : ℕ := L2 / 2 ^ (5 * c) % 2 ^ 5

def t2 (r s : Row) : ℕ := tab2 (pc r s)

/-- W(3, r, s) for every pair, packed: base 2^7 digit number pc r s. -/
def L3 : ℕ := 0x5a0000000000000000000000010900000000000000000000000000a15ab0000000000000000000400000000000000000000000000020000000001890000000000000000000000000000000000000000000000000000000900000000000000000000000000000000000000000000000000000000060018c000000000000000000000000000000000000000000000000006300000000000000000000000000000000000000000000000000000000018c0000000000000000000000000000000000000000000000000000000c00000000000000000000000000000000000000000000000000000000040000000001090000000000000000000000000000000000000000000420000040000000000000000000000000000000000000000000000000001040000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000040010900000000000000000000000000000000000000000000000000420000000000000000000000000000000000000000000000000000000001090000000000000000000000000000000000000000000000000000000900000000000000000000000000005a00000000018c0000000000010974000000000000000000000001aa5ab0000060000000000000400000757c00000000000000000060000000001890000000000000000000000000498000000000000000000000000000900000000000000000000000000180000000000000000000000000000060018c000000000000000000000100041b00000000000000000000006300000000000000000000000001080000000000000000000000000000018c000000000000000000000000041b000000000000000000000000000c000000000000000000000000001b000000000000000000000000000004000000000109000000000000000200000000022d0000000000000004200000400000000000000000000210000080000000000000000000000010400000000000000000000000000820000000000000000000000000004000000000000000000000000000200000000000000060018c00000000400109000000000000000000000020022a000000006300000000000042000000000000000000000000002100000000189000018c0000000000010900000000000000000000000000b45ab0009000000c000000000000090000000000000000000000000021

def tab3 (c : ℕ) : ℕ := L3 / 2 ^ (7 * c) % 2 ^ 7

def t3 (r s : Row) : ℕ := tab3 (pc r s)

/-- W(4, r, s) for every pair, packed: base 2^8 digit number pc r s. -/
def L4 : ℕ := 0x5a0000000000000000000000000002090000000000000000000000000000014e5a5c00000000000000000000020000000000000000000000000000000100000000000309000000000000000000000000000000000000000000000000000000000000000900000000000000000000000000000000000000000000000000000000000000000300030c00000000000000000000000000000000000000000000000000000000030f0000000000000000000000000000000000000000000000000000000000000000030c000000000000000000000000000000000000000000000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000200000000000209000000000000000000000000000000000000000000000000020a00000200000000000000000000000000000000000000000000000000000000000204000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000200020900000000000000000000000000000000000000000000000000000000020a000000000000000000000000000000000000000000000000000000000000000002090000000000000000000000000000000000000000000000000000000000000009000000000000000000000000000000005a0000000000030c0000000000000209760000000000000000000000000003575a5c000003000000000000000200000076f500000000000000000000030000000000030900000000000000000000000000000c210000000000000000000000000000000900000000000000000000000000000021000000000000000000000000000000000300030c0000000000000000000000000b000b27000000000000000000000000030f00000000000000000000000000000b3700000000000000000000000000000000030c00000000000000000000000000000b270000000000000000000000000000000c000000000000000000000000000000270000000000000000000000000000000002000000000002090000000000000000010000000000045a0000000000000000020a0000020000000000000000000000010500000400000000000000000000000000020400000000000000000000000000000102000000000000000000000000000000040000000000000000000000000000000200000000000000000300030c00000000020002090000000000000000000000000100045700000000030f000000000000020a000000000000000000000000000001050000000003090000030c00000000000002090000000000000000000000000000017a5a5c00090000000c00000000000000090000000000000000000000000000004e

def tab4 (c : ℕ) : ℕ := L4 / 2 ^ (8 * c) % 2 ^ 8

def t4 (r s : Row) : ℕ := tab4 (pc r s)

/-- W(5, r, s) for every pair, packed: base 2^10 digit number pc r s. -/
def L5 : ℕ := 0x2d0000000000000000000000000000000000080900000000000000000000000000000000000004a82d0b90000000000000000000000000008000000000000000000000000000000000000000400000000000000c09000000000000000000000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000c0c000000000000000000000000000000000000000000000000000000000000000000000000c120000000000000000000000000000000000000000000000000000000000000000000000000000000000c0c0000000000000000000000000000000000000000000000000000000000000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000008090000000000000000000000000000000000000000000000000000000000000080c00000008000000000000000000000000000000000000000000000000000000000000000000000000008040000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000008000080900000000000000000000000000000000000000000000000000000000000000000000000080c00000000000000000000000000000000000000000000000000000000000000000000000000000000008090000000000000000000000000000000000000000000000000000000000000000000000000000000900000000000000000000000000000000000000002d000000000000000c0c0000000000000000080937c0000000000000000000000000000000000cb12d0b90000000c00000000000000000008000000037e24000000000000000000000000000c00000000000000c090000000000000000000000000000000000003c2a0000000000000000000000000000000000000009000000000000000000000000000000000000002a000000000000000000000000000000000000000000c0000c0c000000000000000000000000000000038000383300000000000000000000000000000000c120000000000000000000000000000000000003854000000000000000000000000000000000000000000c0c0000000000000000000000000000000000003833000000000000000000000000000000000000000c000000000000000000000000000000000000003300000000000000000000000000000000000000000080000000000000080900000000000000000000004000000000000010b4000000000000000000000080c00000008000000000000000000000000000004060000001000000000000000000000000000000000008040000000000000000000000000000000000000402000000000000000000000000000000000000000400000000000000000000000000000000000000020000000000000000000000c0000c0c0000000000008000080900000000000000000000000000000000400010b1000000000000c120000000000000000080c0000000000000000000000000000000000000406000000000000c090000000c0c0000000000000000080900000000000000000000000000000000000005042d0b900009000000000c0000000000000000000900000000000000000000000000000000000000a8

def tab5 (c : ℕ) : ℕ := L5 / 2 ^ (10 * c) % 2 ^ 10

def t5 (r s : Row) : ℕ := tab5 (pc r s)

/-- W(6, r, s) for every pair, packed: base 2^11 digit number pc r s. -/
def L6 : ℕ := 0x2d0000000000000000000000000000000000000010090000000000000000000000000000000000000000095c2d05c0000000000000000000000000000004000000000000000000000000000000000000000000020000000000000001809000000000000000000000000000000000000000000000000000000000000000000000000000000000000000900000000000000000000000000000000000000000000000000000000000000000000000000000000000000000060000180c0000000000000000000000000000000000000000000000000000000000000000000000000000000605400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000180c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000010090000000000000000000000000000000000000000000000000000000000000000000040380000000400000000000000000000000000000000000000000000000000000000000000000000000000000000010040000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400001009000000000000000000000000000000000000000000000000000000000000000000000000000000040380000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010090000000000000000000000000000000000000000000000000000000000000000000000000000000000000009000000000000000000000000000000000000000000002d0000000000000000180c0000000000000000001009344000000000000000000000000000000000000019652d05c0000000060000000000000000000004000000003451cc0000000000000000000000000000060000000000000001809000000000000000000000000000000000000000090330000000000000000000000000000000000000000000900000000000000000000000000000000000000000033000000000000000000000000000000000000000000000060000180c0000000000000000000000000000000000220000883f000000000000000000000000000000000006054000000000000000000000000000000000000000221dc000000000000000000000000000000000000000000000180c0000000000000000000000000000000000000000883f0000000000000000000000000000000000000000000c0000000000000000000000000000000000000000003f0000000000000000000000000000000000000000000000400000000000000010090000000000000000000000002000000000000000216800000000000000000000000040380000000400000000000000000000000000000000201c000000080000000000000000000000000000000000000100400000000000000000000000000000000000000000802000000000000000000000000000000000000000000040000000000000000000000000000000000000000000200000000000000000000000060000180c0000000000000400001009000000000000000000000000000000000002000021650000000000000605400000000000000000040380000000000000000000000000000000000000000201c00000000000018090000000180c000000000000000000100900000000000000000000000000000000000000000a152d05c0000090000000000c00000000000000000000090000000000000000000000000000000000000000015c

def tab6 (c : ℕ) : ℕ := L6 / 2 ^ (11 * c) % 2 ^ 11

def t6 (r s : Row) : ℕ := tab6 (pc r s)

/-- W(7, r, s) for every pair, packed: base 2^12 digit number pc r s. -/
def L7 : ℕ := 0x2d00000000000000000000000000000000000000000020090000000000000000000000000000000000000000000012c42d02db00000000000000000000000000000000200000000000000000000000000000000000000000000000100000000000000000300900000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000900000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000300c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000301800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000020090000000000000000000000000000000000000000000000000000000000000000000000000020100000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000020090000000000000000000000000000000000000000000000000000000000000000000000000000000000000020100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020090000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000002d000000000000000000300c0000000000000000000020093190000000000000000000000000000000000000000032cd2d02db0000000030000000000000000000000020000000003198f000000000000000000000000000000000300000000000000000300900000000000000000000000000000000000000000001503c00000000000000000000000000000000000000000000000900000000000000000000000000000000000000000000003c00000000000000000000000000000000000000000000000000300000300c00000000000000000000000000000000000001400001404b0000000000000000000000000000000000000030180000000000000000000000000000000000000000000140a000000000000000000000000000000000000000000000000000300c00000000000000000000000000000000000000000001404b00000000000000000000000000000000000000000000000c00000000000000000000000000000000000000000000004b0000000000000000000000000000000000000000000000000020000000000000000020090000000000000000000000000010000000000000000042d000000000000000000000000000201000000000200000000000000000000000000000000000100800000000400000000000000000000000000000000000000000200400000000000000000000000000000000000000000000100200000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000200000000000000000000000000300000300c0000000000000020000020090000000000000000000000000000000000000010000042cd00000000000000301800000000000000000000201000000000000000000000000000000000000000000000100800000000000000300900000000300c0000000000000000000020090000000000000000000000000000000000000000000014342d02db00000900000000000c0000000000000000000000090000000000000000000000000000000000000000000002c4

def tab7 (c : ℕ) : ℕ := L7 / 2 ^ (12 * c) % 2 ^ 12

def t7 (r s : Row) : ℕ := tab7 (pc r s)

def step0 (c : ℕ) : Bool := tab0 c == (bif QB (c / 32 / 16 % 2) (c / 32 / 8 % 2) (c / 32 / 4 % 2) (c / 32 / 2 % 2) (c / 32 % 2) (c % 32 / 16 % 2) (c % 32 / 8 % 2) (c % 32 / 4 % 2) (c % 32 / 2 % 2) (c % 32 % 2) then 1 else 0)

def step1 (c : ℕ) : Bool := tab1 c ==
  (bif QB (c / 32 / 16 % 2) (c / 32 / 8 % 2) (c / 32 / 4 % 2) (c / 32 / 2 % 2) (c / 32 % 2) (c % 32 / 16 % 2) (c % 32 / 8 % 2) (c % 32 / 4 % 2) (c % 32 / 2 % 2) (c % 32 % 2) then ((Tl (c / 32 / 16 % 2) (c / 32 / 8 % 2) (c / 32 / 4 % 2) (c / 32 / 2 % 2) (c / 32 % 2) (c % 32 / 16 % 2) (c % 32 / 8 % 2) (c % 32 / 4 % 2) (c % 32 / 2 % 2) (c % 32 % 2)).map (fun t => tab0 (c % 32 * 32 + t))).sum else 0)

def step2 (c : ℕ) : Bool := tab2 c ==
  (bif QB (c / 32 / 16 % 2) (c / 32 / 8 % 2) (c / 32 / 4 % 2) (c / 32 / 2 % 2) (c / 32 % 2) (c % 32 / 16 % 2) (c % 32 / 8 % 2) (c % 32 / 4 % 2) (c % 32 / 2 % 2) (c % 32 % 2) then ((Tl (c / 32 / 16 % 2) (c / 32 / 8 % 2) (c / 32 / 4 % 2) (c / 32 / 2 % 2) (c / 32 % 2) (c % 32 / 16 % 2) (c % 32 / 8 % 2) (c % 32 / 4 % 2) (c % 32 / 2 % 2) (c % 32 % 2)).map (fun t => tab1 (c % 32 * 32 + t))).sum else 0)

def step3 (c : ℕ) : Bool := tab3 c ==
  (bif QB (c / 32 / 16 % 2) (c / 32 / 8 % 2) (c / 32 / 4 % 2) (c / 32 / 2 % 2) (c / 32 % 2) (c % 32 / 16 % 2) (c % 32 / 8 % 2) (c % 32 / 4 % 2) (c % 32 / 2 % 2) (c % 32 % 2) then ((Tl (c / 32 / 16 % 2) (c / 32 / 8 % 2) (c / 32 / 4 % 2) (c / 32 / 2 % 2) (c / 32 % 2) (c % 32 / 16 % 2) (c % 32 / 8 % 2) (c % 32 / 4 % 2) (c % 32 / 2 % 2) (c % 32 % 2)).map (fun t => tab2 (c % 32 * 32 + t))).sum else 0)

def step4 (c : ℕ) : Bool := tab4 c ==
  (bif QB (c / 32 / 16 % 2) (c / 32 / 8 % 2) (c / 32 / 4 % 2) (c / 32 / 2 % 2) (c / 32 % 2) (c % 32 / 16 % 2) (c % 32 / 8 % 2) (c % 32 / 4 % 2) (c % 32 / 2 % 2) (c % 32 % 2) then ((Tl (c / 32 / 16 % 2) (c / 32 / 8 % 2) (c / 32 / 4 % 2) (c / 32 / 2 % 2) (c / 32 % 2) (c % 32 / 16 % 2) (c % 32 / 8 % 2) (c % 32 / 4 % 2) (c % 32 / 2 % 2) (c % 32 % 2)).map (fun t => tab3 (c % 32 * 32 + t))).sum else 0)

def step5 (c : ℕ) : Bool := tab5 c ==
  (bif QB (c / 32 / 16 % 2) (c / 32 / 8 % 2) (c / 32 / 4 % 2) (c / 32 / 2 % 2) (c / 32 % 2) (c % 32 / 16 % 2) (c % 32 / 8 % 2) (c % 32 / 4 % 2) (c % 32 / 2 % 2) (c % 32 % 2) then ((Tl (c / 32 / 16 % 2) (c / 32 / 8 % 2) (c / 32 / 4 % 2) (c / 32 / 2 % 2) (c / 32 % 2) (c % 32 / 16 % 2) (c % 32 / 8 % 2) (c % 32 / 4 % 2) (c % 32 / 2 % 2) (c % 32 % 2)).map (fun t => tab4 (c % 32 * 32 + t))).sum else 0)

def step6 (c : ℕ) : Bool := tab6 c ==
  (bif QB (c / 32 / 16 % 2) (c / 32 / 8 % 2) (c / 32 / 4 % 2) (c / 32 / 2 % 2) (c / 32 % 2) (c % 32 / 16 % 2) (c % 32 / 8 % 2) (c % 32 / 4 % 2) (c % 32 / 2 % 2) (c % 32 % 2) then ((Tl (c / 32 / 16 % 2) (c / 32 / 8 % 2) (c / 32 / 4 % 2) (c / 32 / 2 % 2) (c / 32 % 2) (c % 32 / 16 % 2) (c % 32 / 8 % 2) (c % 32 / 4 % 2) (c % 32 / 2 % 2) (c % 32 % 2)).map (fun t => tab5 (c % 32 * 32 + t))).sum else 0)

def step7 (c : ℕ) : Bool := tab7 c ==
  (bif QB (c / 32 / 16 % 2) (c / 32 / 8 % 2) (c / 32 / 4 % 2) (c / 32 / 2 % 2) (c / 32 % 2) (c % 32 / 16 % 2) (c % 32 / 8 % 2) (c % 32 / 4 % 2) (c % 32 / 2 % 2) (c % 32 % 2) then ((Tl (c / 32 / 16 % 2) (c / 32 / 8 % 2) (c / 32 / 4 % 2) (c / 32 / 2 % 2) (c / 32 % 2) (c % 32 / 16 % 2) (c % 32 / 8 % 2) (c % 32 / 4 % 2) (c % 32 / 2 % 2) (c % 32 % 2)).map (fun t => tab6 (c % 32 * 32 + t))).sum else 0)

/-- The relation on the tables at the pair code c. -/
def relB (c : ℕ) : Bool := (bif QB (c / 32 / 16 % 2) (c / 32 / 8 % 2) (c / 32 / 4 % 2) (c / 32 / 2 % 2) (c / 32 % 2) (c % 32 / 16 % 2) (c % 32 / 8 % 2) (c % 32 / 4 % 2) (c % 32 / 2 % 2) (c % 32 % 2) then ((Tl (c / 32 / 16 % 2) (c / 32 / 8 % 2) (c / 32 / 4 % 2) (c / 32 / 2 % 2) (c / 32 % 2) (c % 32 / 16 % 2) (c % 32 / 8 % 2) (c % 32 / 4 % 2) (c % 32 / 2 % 2) (c % 32 % 2)).map (fun t => tab7 ((c % 32) * 32 + t))).sum else 0) + 9 * tab6 c + 2 * tab4 c == 5 * tab7 c + 7 * tab5 c

def rowB (c : ℕ) : Bool := step0 c && step1 c && step2 c && step3 c && step4 c && step5 c && step6 c && step7 c && relB c

lemma chunk0_ok : (List.range' 0 1024).all rowB = true := by
  decide +kernel

def allB : Bool := (Ts (fun x => Ts (fun y => tab0 (x * 32 + y))) == 335) && (Ts (fun x => Ts (fun y => tab1 (x * 32 + y))) == 742) && (Ts (fun x => Ts (fun y => tab2 (x * 32 + y))) == 914) && (Ts (fun x => Ts (fun y => tab3 (x * 32 + y))) == 1498) && (Ts (fun x => Ts (fun y => tab4 (x * 32 + y))) == 2543) && (Ts (fun x => Ts (fun y => tab5 (x * 32 + y))) == 4490) && (Ts (fun x => Ts (fun y => tab6 (x * 32 + y))) == 8216) && (Ts (fun x => Ts (fun y => tab7 (x * 32 + y))) == 15476)

lemma all_ok : allB = true := by
  decide +kernel

lemma all_parts : (Ts (fun x => Ts (fun y => tab0 (x * 32 + y))) == 335) = true ∧ (Ts (fun x => Ts (fun y => tab1 (x * 32 + y))) == 742) = true ∧ (Ts (fun x => Ts (fun y => tab2 (x * 32 + y))) == 914) = true ∧ (Ts (fun x => Ts (fun y => tab3 (x * 32 + y))) == 1498) = true ∧ (Ts (fun x => Ts (fun y => tab4 (x * 32 + y))) == 2543) = true ∧ (Ts (fun x => Ts (fun y => tab5 (x * 32 + y))) == 4490) = true ∧ (Ts (fun x => Ts (fun y => tab6 (x * 32 + y))) == 8216) = true ∧ (Ts (fun x => Ts (fun y => tab7 (x * 32 + y))) == 15476) = true := by
  have h := all_ok
  unfold allB at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

lemma row_ok (c : ℕ) (hc : c < 1024) : step0 c = true ∧ step1 c = true ∧ step2 c = true ∧ step3 c = true ∧ step4 c = true ∧ step5 c = true ∧ step6 c = true ∧ step7 c = true ∧ relB c = true := by
  have h : rowB c = true := by
    by_cases h0 : c < 1024
    · exact List.all_eq_true.mp chunk0_ok c (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    omega
  unfold rowB at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

lemma pc_digits (r s : Row) :
    (pc r s / 32 / 16 % 2) = (r 0).val ∧ (pc r s / 32 / 8 % 2) = (r 1).val ∧ (pc r s / 32 / 4 % 2) = (r 2).val ∧ (pc r s / 32 / 2 % 2) = (r 3).val ∧ (pc r s / 32 % 2) = (r 4).val ∧ (pc r s % 32 / 16 % 2) = (s 0).val ∧ (pc r s % 32 / 8 % 2) = (s 1).val ∧ (pc r s % 32 / 4 % 2) = (s 2).val ∧ (pc r s % 32 / 2 % 2) = (s 3).val ∧ (pc r s % 32 % 2) = (s 4).val := by
  rw [pc_div, pc_mod]
  exact ⟨dig0 r, dig1 r, dig2 r, dig3 r, dig4 r, dig0 s, dig1 s, dig2 s, dig3 s, dig4 s⟩

lemma W0f (r s : Row) : W 0 r s = t0 r s := by
  rw [W_zero]
  have h := (row_ok (pc r s) (pc_lt r s)).1
  unfold step0 at h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := pc_digits r s
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W1f (r s : Row) : W 1 r s = t1 r s := by
  rw [W_succ]
  simp only [W0f, t0, pc]
  rw [bridge (fun t => tab0 (code s * 32 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.1
  unfold step1 at h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := pc_digits r s
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W2f (r s : Row) : W 2 r s = t2 r s := by
  rw [W_succ]
  simp only [W1f, t1, pc]
  rw [bridge (fun t => tab1 (code s * 32 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.1
  unfold step2 at h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := pc_digits r s
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W3f (r s : Row) : W 3 r s = t3 r s := by
  rw [W_succ]
  simp only [W2f, t2, pc]
  rw [bridge (fun t => tab2 (code s * 32 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.1
  unfold step3 at h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := pc_digits r s
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W4f (r s : Row) : W 4 r s = t4 r s := by
  rw [W_succ]
  simp only [W3f, t3, pc]
  rw [bridge (fun t => tab3 (code s * 32 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.2.1
  unfold step4 at h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := pc_digits r s
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W5f (r s : Row) : W 5 r s = t5 r s := by
  rw [W_succ]
  simp only [W4f, t4, pc]
  rw [bridge (fun t => tab4 (code s * 32 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.2.2.1
  unfold step5 at h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := pc_digits r s
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W6f (r s : Row) : W 6 r s = t6 r s := by
  rw [W_succ]
  simp only [W5f, t5, pc]
  rw [bridge (fun t => tab5 (code s * 32 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.2.2.2.1
  unfold step6 at h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := pc_digits r s
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W7f (r s : Row) : W 7 r s = t7 r s := by
  rw [W_succ]
  simp only [W6f, t6, pc]
  rw [bridge (fun t => tab6 (code s * 32 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.2.2.2.2.1
  unfold step7 at h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := pc_digits r s
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma rel_at (r s : Row) : (if QB (r 0).val (r 1).val (r 2).val (r 3).val (r 4).val (s 0).val (s 1).val (s 2).val (s 3).val (s 4).val = true then ((Tl (r 0).val (r 1).val (r 2).val (r 3).val (r 4).val (s 0).val (s 1).val (s 2).val (s 3).val (s 4).val).map (fun t => tab7 ((code s) * 32 + t))).sum else 0) + 9 * tab6 (pc r s) + 2 * tab4 (pc r s) = 5 * tab7 (pc r s) + 7 * tab5 (pc r s) := by
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.2.2.2.2.2
  unfold relB at h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := pc_digits r s
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, pc_mod] at h
  simp only [Bool.cond_eq_ite] at h
  exact beq_iff_eq.mp h

lemma W_rec (k : ℕ) : ∀ r s : Row, W (k + 8) r s + 9 * W (k + 6) r s + 2 * W (k + 4) r s = 5 * W (k + 7) r s + 7 * W (k + 5) r s := by
  induction k with
  | zero =>
    intro r s
    simp only [Nat.zero_add, W4f, W5f, W6f, W7f, t4, t5, t6, t7]
    rw [W_succ]
    simp only [W7f, t7, pc]
    rw [bridge (fun t => tab7 (code s * 32 + t)) r s, Tn_list]
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

lemma cnt1 : cnt 1 = 335 := by
  rw [cnt_sum]
  simp only [W0f, t0, pc]
  rw [total2 tab0]
  exact beq_iff_eq.mp all_parts.1

lemma cnt2 : cnt 2 = 742 := by
  rw [cnt_sum]
  simp only [W1f, t1, pc]
  rw [total2 tab1]
  exact beq_iff_eq.mp all_parts.2.1

lemma cnt3 : cnt 3 = 914 := by
  rw [cnt_sum]
  simp only [W2f, t2, pc]
  rw [total2 tab2]
  exact beq_iff_eq.mp all_parts.2.2.1

lemma cnt4 : cnt 4 = 1498 := by
  rw [cnt_sum]
  simp only [W3f, t3, pc]
  rw [total2 tab3]
  exact beq_iff_eq.mp all_parts.2.2.2.1

lemma cnt5 : cnt 5 = 2543 := by
  rw [cnt_sum]
  simp only [W4f, t4, pc]
  rw [total2 tab4]
  exact beq_iff_eq.mp all_parts.2.2.2.2.1

lemma cnt6 : cnt 6 = 4490 := by
  rw [cnt_sum]
  simp only [W5f, t5, pc]
  rw [total2 tab5]
  exact beq_iff_eq.mp all_parts.2.2.2.2.2.1

lemma cnt7 : cnt 7 = 8216 := by
  rw [cnt_sum]
  simp only [W6f, t6, pc]
  rw [total2 tab6]
  exact beq_iff_eq.mp all_parts.2.2.2.2.2.2.1

lemma cnt8 : cnt 8 = 15476 := by
  rw [cnt_sum]
  simp only [W7f, t7, pc]
  rw [total2 tab7]
  exact beq_iff_eq.mp all_parts.2.2.2.2.2.2.2

lemma cnt9 : cnt 9 = 29780 := by
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

lemma a1 : (a 1 : ℚ) = 335 := by
  rw [a_cast, cnt1]
  norm_num

lemma a2 : (a 2 : ℚ) = 742 := by
  rw [a_cast, cnt2]
  norm_num

lemma a3 : (a 3 : ℚ) = 914 := by
  rw [a_cast, cnt3]
  norm_num

lemma a4 : (a 4 : ℚ) = 1498 := by
  rw [a_cast, cnt4]
  norm_num

lemma a5 : (a 5 : ℚ) = 2543 := by
  rw [a_cast, cnt5]
  norm_num

lemma a6 : (a 6 : ℚ) = 4490 := by
  rw [a_cast, cnt6]
  norm_num

lemma a7 : (a 7 : ℚ) = 8216 := by
  rw [a_cast, cnt7]
  norm_num

lemma a8 : (a 8 : ℚ) = 15476 := by
  rw [a_cast, cnt8]
  norm_num

lemma a9 : (a 9 : ℚ) = 29780 := by
  rw [a_cast, cnt9]
  norm_num

/-- The g.f. as stated. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) ^ 3 * (1 - 2 * X)) =
      X * (335 - 933 * X + 219 * X ^ 2 + 1261 * X ^ 3 - 1245 * X ^ 4 + 343 * X ^ 5 - 5 * X ^ 6 + X ^ 7) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) ^ 3 * (1 - 2 * X)) = A - C (5 : ℚ) * (A * X ^ 1) + C (9 : ℚ) * (A * X ^ 2) - C (7 : ℚ) * (A * X ^ 3) + C (2 : ℚ) * (A * X ^ 4) := by
    rw [show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2, show (C (5 : ℚ) : ℚ⟦X⟧) = 5 from map_ofNat C 5, show (C (7 : ℚ) : ℚ⟦X⟧) = 7 from map_ofNat C 7, show (C (9 : ℚ) : ℚ⟦X⟧) = 9 from map_ofNat C 9]
    ring
  have e2 : (X * (335 - 933 * X + 219 * X ^ 2 + 1261 * X ^ 3 - 1245 * X ^ 4 + 343 * X ^ 5 - 5 * X ^ 6 + X ^ 7) : ℚ⟦X⟧) = C (335 : ℚ) * X ^ 1 - C (933 : ℚ) * X ^ 2 + C (219 : ℚ) * X ^ 3 + C (1261 : ℚ) * X ^ 4 - C (1245 : ℚ) * X ^ 5 + C (343 : ℚ) * X ^ 6 - C (5 : ℚ) * X ^ 7 + X ^ 8 := by
    rw [show (C (5 : ℚ) : ℚ⟦X⟧) = 5 from map_ofNat C 5, show (C (219 : ℚ) : ℚ⟦X⟧) = 219 from map_ofNat C 219, show (C (335 : ℚ) : ℚ⟦X⟧) = 335 from map_ofNat C 335, show (C (343 : ℚ) : ℚ⟦X⟧) = 343 from map_ofNat C 343, show (C (933 : ℚ) : ℚ⟦X⟧) = 933 from map_ofNat C 933, show (C (1245 : ℚ) : ℚ⟦X⟧) = 1245 from map_ofNat C 1245, show (C (1261 : ℚ) : ℚ⟦X⟧) = 1261 from map_ofNat C 1261]
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

def closed_Q (n : ℕ) : ℚ := 188 + 1755 * 2 ^ n / 32 + 60 * n + 12 * n ^ 2

lemma closed_Q_rec (m : ℕ) : closed_Q (m + 4) - 5 * closed_Q (m + 3) + 9 * closed_Q (m + 2) - 7 * closed_Q (m + 1) + 2 * closed_Q (m + 0) = 0 := by
  unfold closed_Q
  push_cast
  ring

lemma closed_key (n : ℕ) (hn : 5 ≤ n) : (a n : ℚ) = closed_Q n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 9 with h | h
    · interval_cases n
      · have hk : (a 5 : ℚ) = 2543 := by exact_mod_cast a5
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 6 : ℚ) = 4490 := by exact_mod_cast a6
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 7 : ℚ) = 8216 := by exact_mod_cast a7
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 8 : ℚ) = 15476 := by exact_mod_cast a8
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

theorem closed : ∀ n : ℕ, 4 < n → (a n : ℚ) = 188 + 1755 * 2 ^ (n - 5) + 60 * n + 12 * n ^ 2 := by
  intro n hn
  rw [closed_key n (by omega)]
  unfold closed_Q
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 5 = m by omega]
  push_cast
  ring

/-- Controls: the entry's data. -/
theorem controls : a 1 = 335 ∧ a 2 = 742 ∧ a 3 = 914 ∧ a 4 = 1498 ∧ a 5 = 2543 ∧ a 6 = 4490 ∧ a 7 = 8216 ∧ a 8 = 15476 ∧ a 9 = 29780 ∧ a 10 = 58148 ∧ a 11 = 114620 ∧ a 12 = 227276 ∧ a 13 = 452276 ∧ a 14 = 901940 ∧ a 15 = 1800908 ∧ a 16 = 3598460 ∧ a 17 = 7193156 ∧ a 18 = 14382116 ∧ a 19 = 28759580 ∧ a 20 = 57514028 ∧ a 21 = 115022420 ∧ a 22 = 230038676 ∧ a 23 = 460070636 ∧ a 24 = 920133980 ∧ a 25 = 1840260068 ∧ a 26 = 3680511620 ∧ a 27 = 7361014076 := by
  have v10 : (a 10 : ℚ) = 58148 := by
    have h := a_rec 1
    simp only [Nat.reduceAdd] at h
    rw [a6, a7, a8, a9] at h
    linarith
  have v11 : (a 11 : ℚ) = 114620 := by
    have h := a_rec 2
    simp only [Nat.reduceAdd] at h
    rw [a7, a8, a9, v10] at h
    linarith
  have v12 : (a 12 : ℚ) = 227276 := by
    have h := a_rec 3
    simp only [Nat.reduceAdd] at h
    rw [a8, a9, v10, v11] at h
    linarith
  have v13 : (a 13 : ℚ) = 452276 := by
    have h := a_rec 4
    simp only [Nat.reduceAdd] at h
    rw [a9, v10, v11, v12] at h
    linarith
  have v14 : (a 14 : ℚ) = 901940 := by
    have h := a_rec 5
    simp only [Nat.reduceAdd] at h
    rw [v10, v11, v12, v13] at h
    linarith
  have v15 : (a 15 : ℚ) = 1800908 := by
    have h := a_rec 6
    simp only [Nat.reduceAdd] at h
    rw [v11, v12, v13, v14] at h
    linarith
  have v16 : (a 16 : ℚ) = 3598460 := by
    have h := a_rec 7
    simp only [Nat.reduceAdd] at h
    rw [v12, v13, v14, v15] at h
    linarith
  have v17 : (a 17 : ℚ) = 7193156 := by
    have h := a_rec 8
    simp only [Nat.reduceAdd] at h
    rw [v13, v14, v15, v16] at h
    linarith
  have v18 : (a 18 : ℚ) = 14382116 := by
    have h := a_rec 9
    simp only [Nat.reduceAdd] at h
    rw [v14, v15, v16, v17] at h
    linarith
  have v19 : (a 19 : ℚ) = 28759580 := by
    have h := a_rec 10
    simp only [Nat.reduceAdd] at h
    rw [v15, v16, v17, v18] at h
    linarith
  have v20 : (a 20 : ℚ) = 57514028 := by
    have h := a_rec 11
    simp only [Nat.reduceAdd] at h
    rw [v16, v17, v18, v19] at h
    linarith
  have v21 : (a 21 : ℚ) = 115022420 := by
    have h := a_rec 12
    simp only [Nat.reduceAdd] at h
    rw [v17, v18, v19, v20] at h
    linarith
  have v22 : (a 22 : ℚ) = 230038676 := by
    have h := a_rec 13
    simp only [Nat.reduceAdd] at h
    rw [v18, v19, v20, v21] at h
    linarith
  have v23 : (a 23 : ℚ) = 460070636 := by
    have h := a_rec 14
    simp only [Nat.reduceAdd] at h
    rw [v19, v20, v21, v22] at h
    linarith
  have v24 : (a 24 : ℚ) = 920133980 := by
    have h := a_rec 15
    simp only [Nat.reduceAdd] at h
    rw [v20, v21, v22, v23] at h
    linarith
  have v25 : (a 25 : ℚ) = 1840260068 := by
    have h := a_rec 16
    simp only [Nat.reduceAdd] at h
    rw [v21, v22, v23, v24] at h
    linarith
  have v26 : (a 26 : ℚ) = 3680511620 := by
    have h := a_rec 17
    simp only [Nat.reduceAdd] at h
    rw [v22, v23, v24, v25] at h
    linarith
  have v27 : (a 27 : ℚ) = 7361014076 := by
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
        X * (335 - 933 * X + 219 * X ^ 2 + 1261 * X ^ 3 - 1245 * X ^ 4 + 343 * X ^ 5 - 5 * X ^ 6 + X ^ 7) ∧
      ∀ n : ℕ, 4 < n → (a n : ℚ) = 188 + 1755 * 2 ^ (n - 5) + 60 * n + 12 * n ^ 2 :=
  ⟨gf, closed⟩

end OMA.S_oeis_a253227

theorem OMA.solution : type_of% @OMA.S_oeis_a253227.main :=
  OMA.S_oeis_a253227.conjecture
