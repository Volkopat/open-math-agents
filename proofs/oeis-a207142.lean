import OMAStatements.S_oeis_a207142

namespace OMA.S_oeis_a207142

open PowerSeries Finset


/-! ## Rows, the conditions on pairs and triples of rows -/

/-- A row. -/
abbrev Row := Fin 2 → Fin 3

/-- The conditions between two consecutive rows r (above) and s (below). -/
def Qpair (r s : Row) : Prop :=
  (∀ j j' : Fin 2, j'.val = j.val + 1 → (((r j).val : ℤ) * ((s j').val : ℤ) - ((r j').val : ℤ) * ((s j).val : ℤ) ≠ 0))

/-- The conditions on three consecutive rows r, s, t. -/
def Ttrip (r s t : Row) : Prop :=
  (∀ j j' : Fin 2, j'.val = j.val + 1 → (!![((r j).val : ℤ), ((r j').val : ℤ); ((s j).val : ℤ), ((s j').val : ℤ)] * !![((s j).val : ℤ), ((s j').val : ℤ); ((t j).val : ℤ), ((t j').val : ℤ)] =
          !![((s j).val : ℤ), ((s j').val : ℤ); ((t j).val : ℤ), ((t j').val : ℤ)] * !![((r j).val : ℤ), ((r j').val : ℤ); ((s j).val : ℤ), ((s j').val : ℤ)]))

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

lemma sum_cons {m : ℕ} (f : (Fin (m + 1) → Fin 3) → ℕ) :
    ∑ s : Fin (m + 1) → Fin 3, f s = ∑ x : Fin 3, ∑ t : Fin m → Fin 3, f (Fin.cons x t) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 3).symm _ _
    (fun s => by simp [Fin.consEquiv, Fin.cons_self_tail])

lemma sum_row (f : Row → ℕ) :
    ∑ s : Row, f s = ∑ x0 : Fin 3, ∑ x1 : Fin 3, f ![x0, x1] := by
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x0 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x1 _ => ?_)
  rw [Fintype.sum_unique]
  exact congrArg f (by funext j; fin_cases j <;> rfl)

/-! ## The kernel's numeric form -/

/-- The H2 condition on numbers, as a bit of a mask. -/
def gH2 (a b c d : ℕ) : Bool := Nat.beq (1127454458182145251995648 >>> (((a * 3 + b) * 3 + c) * 3 + d) % 2) 1

lemma H2_iff : ∀ a b c d : Fin 3, (((a.val : ℤ) * (d.val : ℤ) - (b.val : ℤ) * (c.val : ℤ) ≠ 0)) ↔ gH2 a.val b.val c.val d.val = true := by
  decide +kernel

/-- The V2 condition on numbers, as a bit of a mask. -/
def gV2 (a b c d e f : ℕ) : Bool := Nat.beq (1412007064173800474776790482904415833040583014717808413060940493194073867094833409140944189952658597031119474057482456135144007083854013397288677333695902575154397939826493321222474497196316822977870755395212204419580415 >>> (((((a * 3 + b) * 3 + c) * 3 + d) * 3 + e) * 3 + f) % 2) 1

lemma V2_iff : ∀ a b c d e f : Fin 3, ((!![(a.val : ℤ), (b.val : ℤ); (c.val : ℤ), (d.val : ℤ)] * !![(c.val : ℤ), (d.val : ℤ); (e.val : ℤ), (f.val : ℤ)] =
          !![(c.val : ℤ), (d.val : ℤ); (e.val : ℤ), (f.val : ℤ)] * !![(a.val : ℤ), (b.val : ℤ); (c.val : ℤ), (d.val : ℤ)])) ↔ gV2 a.val b.val c.val d.val e.val f.val = true := by
  decide +kernel

lemma Qpair_explicit (r s : Row) : Qpair r s ↔ ((((r 0).val : ℤ) * ((s 1).val : ℤ) - ((r 1).val : ℤ) * ((s 0).val : ℤ) ≠ 0)) := by
  unfold Qpair
  constructor
  · intro h0
    exact h0 0 1 rfl
  · intro k0
    intro j j' hj
    rcases j with ⟨j, hj0⟩; rcases j' with ⟨j', hj1⟩
    simp only at hj; subst hj
    have hjw : j < 1 := by omega
    interval_cases j
    · exact k0

/-- Qpair on the entries of the two rows. -/
def QB (r0 r1 s0 s1 : ℕ) : Bool := gH2 r0 r1 s0 s1

lemma Q_iff (r s : Row) : Qpair r s ↔ QB (r 0).val (r 1).val (s 0).val (s 1).val = true := by
  rw [Qpair_explicit]
  simp only [QB, Bool.and_eq_true, and_assoc, H2_iff]

lemma Ttrip_explicit (r s t : Row) : Ttrip r s t ↔ ((!![((r 0).val : ℤ), ((r 1).val : ℤ); ((s 0).val : ℤ), ((s 1).val : ℤ)] * !![((s 0).val : ℤ), ((s 1).val : ℤ); ((t 0).val : ℤ), ((t 1).val : ℤ)] =
          !![((s 0).val : ℤ), ((s 1).val : ℤ); ((t 0).val : ℤ), ((t 1).val : ℤ)] * !![((r 0).val : ℤ), ((r 1).val : ℤ); ((s 0).val : ℤ), ((s 1).val : ℤ)])) := by
  unfold Ttrip
  constructor
  · intro h0
    exact h0 0 1 rfl
  · intro k0
    intro j j' hj
    rcases j with ⟨j, hj0⟩; rcases j' with ⟨j', hj1⟩
    simp only at hj; subst hj
    have hjw : j < 1 := by omega
    interval_cases j
    · exact k0

/-- The sum of f over 0, ..., 2. -/
def sumK (f : ℕ → ℕ) : ℕ := f 0 + f 1 + f 2

lemma sumK_fin (f : ℕ → ℕ) : ∑ x : Fin 3, f x.val = sumK f := by
  rw [Fin.sum_univ_eq_sum_range (fun x => f x) 3]
  simp [Finset.sum_range_succ, sumK]

/-- The concatenation of f over 0, ..., 2. -/
def catK (f : ℕ → List ℕ) : List ℕ := f 0 ++ f 1 ++ f 2

/-- The code of a row: its entries as base-K digits, r 0 the most significant. -/
def code (r : Row) : ℕ := (r 0).val * 3 + (r 1).val

lemma code_lt (r : Row) : code r < 9 := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; omega

lemma dig0 (r : Row) : code r / 3 % 3 = (r 0).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; omega

lemma dig1 (r : Row) : code r % 3 = (r 1).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; omega

/-- The sum of g over all row codes. -/
def Ts (g : ℕ → ℕ) : ℕ := sumK (fun x0 => sumK (fun x1 => g (x0 * 3 + x1)))

lemma total (g : ℕ → ℕ) : (∑ s : Row, g (code s)) = Ts g := by
  rw [sum_row]
  simp only [code, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ]
  unfold Ts
  simp only [← sumK_fin]

def N1 (g : ℕ → ℕ) (r0 r1 s0 s1 : ℕ) (p2 p1 acc : ℕ) : ℕ :=
  sumK (fun x => bif gV2 r0 r1 s0 s1 p1 x then g (acc * 3 + x) else 0)

def M1 (r0 r1 s0 s1 : ℕ) (p2 p1 acc : ℕ) : List ℕ :=
  catK (fun x => bif gV2 r0 r1 s0 s1 p1 x then [acc * 3 + x] else [])

/-- The sum of g over the codes of the rows t with T r s t. -/
def Tn (g : ℕ → ℕ) (r0 r1 s0 s1 : ℕ) : ℕ := sumK (fun x => N1 g r0 r1 s0 s1 0 x x)

/-- The codes of the rows t with T r s t. -/
def Tl (r0 r1 s0 s1 : ℕ) : List ℕ := catK (fun x => M1 r0 r1 s0 s1 0 x x)

lemma N1_list (g : ℕ → ℕ) (r0 r1 s0 s1 p2 p1 acc : ℕ) :
    N1 g r0 r1 s0 s1 p2 p1 acc = ((M1 r0 r1 s0 s1 p2 p1 acc).map g).sum := by
  unfold N1 M1 sumK catK
  simp only [Bool.cond_eq_ite, List.map_append, List.sum_append, apply_ite (List.map g), apply_ite List.sum, List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, add_zero]

lemma Tn_list (g : ℕ → ℕ) (r0 r1 s0 s1 : ℕ) : Tn g r0 r1 s0 s1 = ((Tl r0 r1 s0 s1).map g).sum := by
  unfold Tn Tl sumK catK
  simp only [List.map_append, List.sum_append, N1_list]

lemma bridge (g : ℕ → ℕ) (r s : Row) :
    (∑ t : Row, if Ttrip r s t then g (code t) else 0) = Tn g (r 0).val (r 1).val (s 0).val (s 1).val := by
  rw [sum_row]
  simp only [Ttrip_explicit, V2_iff, code, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ]
  try simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
  unfold Tn N1
  simp only [Bool.cond_eq_ite, ← sumK_fin]

/-- The code of a pair of rows. -/
def pc (r s : Row) : ℕ := code r * 9 + code s

lemma pc_lt (r s : Row) : pc r s < 81 := by
  unfold pc; have := code_lt r; have := code_lt s; nlinarith

lemma pc_div (r s : Row) : pc r s / 9 = code r := by
  unfold pc; have := code_lt s; omega

lemma pc_mod (r s : Row) : pc r s % 9 = code s := by
  unfold pc; have := code_lt s; omega

lemma total2 (g : ℕ → ℕ) :
    (∑ r : Row, ∑ s : Row, g (code r * 9 + code s)) = Ts (fun x => Ts (fun y => g (x * 9 + y))) := by
  have h : ∀ r : Row, (∑ s : Row, g (code r * 9 + code s)) = Ts (fun y => g (code r * 9 + y)) :=
    fun r => total (fun y => g (code r * 9 + y))
  simp only [h]
  exact total (fun x => Ts (fun y => g (x * 9 + y)))

/-- W(0, r, s), by the pair code. -/
def L0 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0,
    1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0,
    1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0]

def tab0 (c : ℕ) : ℕ := L0.getD c 0

def t0 (r s : Row) : ℕ := tab0 (pc r s)

/-- W(1, r, s), by the pair code. -/
def L1 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 6, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 6, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0]

def tab1 (c : ℕ) : ℕ := L1.getD c 0

def t1 (r s : Row) : ℕ := tab1 (pc r s)

/-- W(2, r, s), by the pair code. -/
def L2 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 6, 0, 0, 0, 0, 0, 6, 0, 0, 6, 0, 0, 0, 3, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 6, 0, 0, 0, 0, 0, 6, 0, 0, 6, 1, 0, 0, 0, 2, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 6, 1, 1, 6, 0, 0, 0, 0, 0, 6, 0, 0, 6, 0, 0]

def tab2 (c : ℕ) : ℕ := L2.getD c 0

def t2 (r s : Row) : ℕ := tab2 (pc r s)

/-- W(3, r, s), by the pair code. -/
def L3 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 12, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 2, 1, 0, 0, 0, 12, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 3, 6, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0, 2, 0, 0]

def tab3 (c : ℕ) : ℕ := L3.getD c 0

def t3 (r s : Row) : ℕ := tab3 (pc r s)

/-- W(4, r, s), by the pair code. -/
def L4 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 12, 0, 0, 0, 0, 0, 12, 0, 0, 12, 0, 0, 0, 5, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 12, 0, 0, 0, 0, 0, 12, 0, 0, 12, 1, 0, 0, 0, 5, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 12, 3, 1, 12, 0, 0, 0, 0, 0, 12, 0, 0, 12, 0, 0]

def tab4 (c : ℕ) : ℕ := L4.getD c 0

def t4 (r s : Row) : ℕ := tab4 (pc r s)

/-- W(5, r, s), by the pair code. -/
def L5 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 5, 0, 0, 0, 0, 0, 5, 0, 0, 5, 0, 0, 0, 24, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 5, 0, 0, 0, 0, 0, 5, 0, 0, 5, 1, 0, 0, 0, 24, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 5, 12, 1, 5, 0, 0, 0, 0, 0, 5, 0, 0, 5, 0, 0]

def tab5 (c : ℕ) : ℕ := L5.getD c 0

def t5 (r s : Row) : ℕ := tab5 (pc r s)

/-- W(6, r, s), by the pair code. -/
def L6 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 24, 0, 0, 0, 0, 0, 24, 0, 0, 24, 0, 0, 0, 10, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 24, 0, 0, 0, 0, 0, 24, 0, 0, 24, 1, 0, 0, 0, 10, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 24, 5, 1, 24, 0, 0, 0, 0, 0, 24, 0, 0, 24, 0, 0]

def tab6 (c : ℕ) : ℕ := L6.getD c 0

def t6 (r s : Row) : ℕ := tab6 (pc r s)

/-- W(7, r, s), by the pair code. -/
def L7 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 10, 0, 0, 0, 0, 0, 10, 0, 0, 10, 0, 0, 0, 48, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 10, 0, 0, 0, 0, 0, 10, 0, 0, 10, 1, 0, 0, 0, 48, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 10, 24, 1, 10, 0, 0, 0, 0, 0, 10, 0, 0, 10, 0, 0]

def tab7 (c : ℕ) : ℕ := L7.getD c 0

def t7 (r s : Row) : ℕ := tab7 (pc r s)

def step0 (c : ℕ) : Bool := tab0 c == (bif QB (c / 9 / 3 % 3) (c / 9 % 3) (c % 9 / 3 % 3) (c % 9 % 3) then 1 else 0)

def step1 (c : ℕ) : Bool := tab1 c ==
  (bif QB (c / 9 / 3 % 3) (c / 9 % 3) (c % 9 / 3 % 3) (c % 9 % 3) then ((Tl (c / 9 / 3 % 3) (c / 9 % 3) (c % 9 / 3 % 3) (c % 9 % 3)).map (fun t => tab0 (c % 9 * 9 + t))).sum else 0)

def step2 (c : ℕ) : Bool := tab2 c ==
  (bif QB (c / 9 / 3 % 3) (c / 9 % 3) (c % 9 / 3 % 3) (c % 9 % 3) then ((Tl (c / 9 / 3 % 3) (c / 9 % 3) (c % 9 / 3 % 3) (c % 9 % 3)).map (fun t => tab1 (c % 9 * 9 + t))).sum else 0)

def step3 (c : ℕ) : Bool := tab3 c ==
  (bif QB (c / 9 / 3 % 3) (c / 9 % 3) (c % 9 / 3 % 3) (c % 9 % 3) then ((Tl (c / 9 / 3 % 3) (c / 9 % 3) (c % 9 / 3 % 3) (c % 9 % 3)).map (fun t => tab2 (c % 9 * 9 + t))).sum else 0)

def step4 (c : ℕ) : Bool := tab4 c ==
  (bif QB (c / 9 / 3 % 3) (c / 9 % 3) (c % 9 / 3 % 3) (c % 9 % 3) then ((Tl (c / 9 / 3 % 3) (c / 9 % 3) (c % 9 / 3 % 3) (c % 9 % 3)).map (fun t => tab3 (c % 9 * 9 + t))).sum else 0)

def step5 (c : ℕ) : Bool := tab5 c ==
  (bif QB (c / 9 / 3 % 3) (c / 9 % 3) (c % 9 / 3 % 3) (c % 9 % 3) then ((Tl (c / 9 / 3 % 3) (c / 9 % 3) (c % 9 / 3 % 3) (c % 9 % 3)).map (fun t => tab4 (c % 9 * 9 + t))).sum else 0)

def step6 (c : ℕ) : Bool := tab6 c ==
  (bif QB (c / 9 / 3 % 3) (c / 9 % 3) (c % 9 / 3 % 3) (c % 9 % 3) then ((Tl (c / 9 / 3 % 3) (c / 9 % 3) (c % 9 / 3 % 3) (c % 9 % 3)).map (fun t => tab5 (c % 9 * 9 + t))).sum else 0)

def step7 (c : ℕ) : Bool := tab7 c ==
  (bif QB (c / 9 / 3 % 3) (c / 9 % 3) (c % 9 / 3 % 3) (c % 9 % 3) then ((Tl (c / 9 / 3 % 3) (c / 9 % 3) (c % 9 / 3 % 3) (c % 9 % 3)).map (fun t => tab6 (c % 9 * 9 + t))).sum else 0)

/-- The relation on the tables at the pair code c. -/
def relB (c : ℕ) : Bool := (bif QB (c / 9 / 3 % 3) (c / 9 % 3) (c % 9 / 3 % 3) (c % 9 % 3) then ((Tl (c / 9 / 3 % 3) (c / 9 % 3) (c % 9 / 3 % 3) (c % 9 % 3)).map (fun t => tab7 ((c % 9) * 9 + t))).sum else 0) + 2 * tab5 c == tab7 c + 2 * tab6 c

def rowB (c : ℕ) : Bool := step0 c && step1 c && step2 c && step3 c && step4 c && step5 c && step6 c && step7 c && relB c

lemma chunk0_ok : (List.range' 0 81).all rowB = true := by
  decide +kernel

def allB : Bool := (Ts (fun x => Ts (fun y => tab0 (x * 9 + y))) == 50) && (Ts (fun x => Ts (fun y => tab1 (x * 9 + y))) == 30) && (Ts (fun x => Ts (fun y => tab2 (x * 9 + y))) == 80) && (Ts (fun x => Ts (fun y => tab3 (x * 9 + y))) == 62) && (Ts (fun x => Ts (fun y => tab4 (x * 9 + y))) == 159) && (Ts (fun x => Ts (fun y => tab5 (x * 9 + y))) == 122) && (Ts (fun x => Ts (fun y => tab6 (x * 9 + y))) == 315) && (Ts (fun x => Ts (fun y => tab7 (x * 9 + y))) == 242)

lemma all_ok : allB = true := by
  decide +kernel

lemma all_parts : (Ts (fun x => Ts (fun y => tab0 (x * 9 + y))) == 50) = true ∧ (Ts (fun x => Ts (fun y => tab1 (x * 9 + y))) == 30) = true ∧ (Ts (fun x => Ts (fun y => tab2 (x * 9 + y))) == 80) = true ∧ (Ts (fun x => Ts (fun y => tab3 (x * 9 + y))) == 62) = true ∧ (Ts (fun x => Ts (fun y => tab4 (x * 9 + y))) == 159) = true ∧ (Ts (fun x => Ts (fun y => tab5 (x * 9 + y))) == 122) = true ∧ (Ts (fun x => Ts (fun y => tab6 (x * 9 + y))) == 315) = true ∧ (Ts (fun x => Ts (fun y => tab7 (x * 9 + y))) == 242) = true := by
  have h := all_ok
  unfold allB at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

lemma row_ok (c : ℕ) (hc : c < 81) : step0 c = true ∧ step1 c = true ∧ step2 c = true ∧ step3 c = true ∧ step4 c = true ∧ step5 c = true ∧ step6 c = true ∧ step7 c = true ∧ relB c = true := by
  have h : rowB c = true := by
    by_cases h0 : c < 81
    · exact List.all_eq_true.mp chunk0_ok c (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    omega
  unfold rowB at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

lemma pc_digits (r s : Row) :
    (pc r s / 9 / 3 % 3) = (r 0).val ∧ (pc r s / 9 % 3) = (r 1).val ∧ (pc r s % 9 / 3 % 3) = (s 0).val ∧ (pc r s % 9 % 3) = (s 1).val := by
  rw [pc_div, pc_mod]
  exact ⟨dig0 r, dig1 r, dig0 s, dig1 s⟩

lemma W0f (r s : Row) : W 0 r s = t0 r s := by
  rw [W_zero]
  have h := (row_ok (pc r s) (pc_lt r s)).1
  unfold step0 at h
  obtain ⟨e0, e1, e2, e3⟩ := pc_digits r s
  rw [e0, e1, e2, e3] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W1f (r s : Row) : W 1 r s = t1 r s := by
  rw [W_succ]
  simp only [W0f, t0, pc]
  rw [bridge (fun t => tab0 (code s * 9 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.1
  unfold step1 at h
  obtain ⟨e0, e1, e2, e3⟩ := pc_digits r s
  rw [e0, e1, e2, e3, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W2f (r s : Row) : W 2 r s = t2 r s := by
  rw [W_succ]
  simp only [W1f, t1, pc]
  rw [bridge (fun t => tab1 (code s * 9 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.1
  unfold step2 at h
  obtain ⟨e0, e1, e2, e3⟩ := pc_digits r s
  rw [e0, e1, e2, e3, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W3f (r s : Row) : W 3 r s = t3 r s := by
  rw [W_succ]
  simp only [W2f, t2, pc]
  rw [bridge (fun t => tab2 (code s * 9 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.1
  unfold step3 at h
  obtain ⟨e0, e1, e2, e3⟩ := pc_digits r s
  rw [e0, e1, e2, e3, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W4f (r s : Row) : W 4 r s = t4 r s := by
  rw [W_succ]
  simp only [W3f, t3, pc]
  rw [bridge (fun t => tab3 (code s * 9 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.2.1
  unfold step4 at h
  obtain ⟨e0, e1, e2, e3⟩ := pc_digits r s
  rw [e0, e1, e2, e3, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W5f (r s : Row) : W 5 r s = t5 r s := by
  rw [W_succ]
  simp only [W4f, t4, pc]
  rw [bridge (fun t => tab4 (code s * 9 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.2.2.1
  unfold step5 at h
  obtain ⟨e0, e1, e2, e3⟩ := pc_digits r s
  rw [e0, e1, e2, e3, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W6f (r s : Row) : W 6 r s = t6 r s := by
  rw [W_succ]
  simp only [W5f, t5, pc]
  rw [bridge (fun t => tab5 (code s * 9 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.2.2.2.1
  unfold step6 at h
  obtain ⟨e0, e1, e2, e3⟩ := pc_digits r s
  rw [e0, e1, e2, e3, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W7f (r s : Row) : W 7 r s = t7 r s := by
  rw [W_succ]
  simp only [W6f, t6, pc]
  rw [bridge (fun t => tab6 (code s * 9 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.2.2.2.2.1
  unfold step7 at h
  obtain ⟨e0, e1, e2, e3⟩ := pc_digits r s
  rw [e0, e1, e2, e3, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma rel_at (r s : Row) : (if QB (r 0).val (r 1).val (s 0).val (s 1).val = true then ((Tl (r 0).val (r 1).val (s 0).val (s 1).val).map (fun t => tab7 ((code s) * 9 + t))).sum else 0) + 2 * tab5 (pc r s) = tab7 (pc r s) + 2 * tab6 (pc r s) := by
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.2.2.2.2.2
  unfold relB at h
  obtain ⟨e0, e1, e2, e3⟩ := pc_digits r s
  rw [e0, e1, e2, e3, pc_mod] at h
  simp only [Bool.cond_eq_ite] at h
  exact beq_iff_eq.mp h

lemma W_rec (k : ℕ) : ∀ r s : Row, W (k + 8) r s + 2 * W (k + 5) r s = W (k + 7) r s + 2 * W (k + 6) r s := by
  induction k with
  | zero =>
    intro r s
    simp only [Nat.zero_add, W5f, W6f, W7f, t5, t6, t7]
    rw [W_succ]
    simp only [W7f, t7, pc]
    rw [bridge (fun t => tab7 (code s * 9 + t)) r s, Tn_list]
    simp only [Q_iff]
    exact rel_at r s
  | succ k ih =>
    intro r s
    rw [show k + 1 + 5 = (k + 5) + 1 from rfl, show k + 1 + 6 = (k + 6) + 1 from rfl, show k + 1 + 7 = (k + 7) + 1 from rfl, show k + 1 + 8 = (k + 8) + 1 from rfl]
    rw [W_succ (k + 5), W_succ (k + 6), W_succ (k + 7), W_succ (k + 8)]
    split_ifs with hq
    · simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      split_ifs
      · exact ih s t
      · simp
    · simp

lemma cnt_rec (k : ℕ) : cnt (k + 9) + 2 * cnt (k + 6) = cnt (k + 8) + 2 * cnt (k + 7) := by
  rw [show k + 6 = (k + 5) + 1 from rfl, show k + 7 = (k + 6) + 1 from rfl, show k + 8 = (k + 7) + 1 from rfl, show k + 9 = (k + 8) + 1 from rfl]
  simp only [cnt_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ => ?_))
  exact W_rec k r s

lemma cnt1 : cnt 1 = 50 := by
  rw [cnt_sum]
  simp only [W0f, t0, pc]
  rw [total2 tab0]
  exact beq_iff_eq.mp all_parts.1

lemma cnt2 : cnt 2 = 30 := by
  rw [cnt_sum]
  simp only [W1f, t1, pc]
  rw [total2 tab1]
  exact beq_iff_eq.mp all_parts.2.1

lemma cnt3 : cnt 3 = 80 := by
  rw [cnt_sum]
  simp only [W2f, t2, pc]
  rw [total2 tab2]
  exact beq_iff_eq.mp all_parts.2.2.1

lemma cnt4 : cnt 4 = 62 := by
  rw [cnt_sum]
  simp only [W3f, t3, pc]
  rw [total2 tab3]
  exact beq_iff_eq.mp all_parts.2.2.2.1

lemma cnt5 : cnt 5 = 159 := by
  rw [cnt_sum]
  simp only [W4f, t4, pc]
  rw [total2 tab4]
  exact beq_iff_eq.mp all_parts.2.2.2.2.1

lemma cnt6 : cnt 6 = 122 := by
  rw [cnt_sum]
  simp only [W5f, t5, pc]
  rw [total2 tab5]
  exact beq_iff_eq.mp all_parts.2.2.2.2.2.1

lemma cnt7 : cnt 7 = 315 := by
  rw [cnt_sum]
  simp only [W6f, t6, pc]
  rw [total2 tab6]
  exact beq_iff_eq.mp all_parts.2.2.2.2.2.2.1

lemma cnt8 : cnt 8 = 242 := by
  rw [cnt_sum]
  simp only [W7f, t7, pc]
  rw [total2 tab7]
  exact beq_iff_eq.mp all_parts.2.2.2.2.2.2.2

lemma cnt9 : cnt 9 = 628 := by
  have h := cnt_rec 0
  simp only [Nat.zero_add] at h
  rw [cnt6, cnt7, cnt8] at h
  generalize cnt 9 = x at h ⊢
  omega

lemma a_cast (n : ℕ) : (a n : ℚ) = (cnt n : ℚ) := by
  rw [a_eq]

lemma a_rec (k : ℕ) : (a (k + 9) : ℚ) + 2 * (a (k + 6) : ℚ) = (a (k + 8) : ℚ) + 2 * (a (k + 7) : ℚ) := by
  simp only [a_cast]
  have h : cnt (k + 9) + 2 * cnt (k + 6) = cnt (k + 8) + 2 * cnt (k + 7) := by simpa only [Nat.add_assoc, Nat.reduceAdd] using cnt_rec (k + 0)
  have h' : ((cnt (k + 9) : ℕ) : ℚ) + 2 * ((cnt (k + 6) : ℕ) : ℚ) = ((cnt (k + 8) : ℕ) : ℚ) + 2 * ((cnt (k + 7) : ℕ) : ℚ) := by exact_mod_cast h
  linear_combination h'

lemma a1 : (a 1 : ℚ) = 50 := by
  rw [a_cast, cnt1]
  norm_num

lemma a2 : (a 2 : ℚ) = 30 := by
  rw [a_cast, cnt2]
  norm_num

lemma a3 : (a 3 : ℚ) = 80 := by
  rw [a_cast, cnt3]
  norm_num

lemma a4 : (a 4 : ℚ) = 62 := by
  rw [a_cast, cnt4]
  norm_num

lemma a5 : (a 5 : ℚ) = 159 := by
  rw [a_cast, cnt5]
  norm_num

lemma a6 : (a 6 : ℚ) = 122 := by
  rw [a_cast, cnt6]
  norm_num

lemma a7 : (a 7 : ℚ) = 315 := by
  rw [a_cast, cnt7]
  norm_num

lemma a8 : (a 8 : ℚ) = 242 := by
  rw [a_cast, cnt8]
  norm_num

lemma a9 : (a 9 : ℚ) = 628 := by
  rw [a_cast, cnt9]
  norm_num

/-- The g.f. as stated. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) * (1 - 2 * X ^ 2)) =
      X * (50 - 20 * X - 50 * X ^ 2 + 22 * X ^ 3 - 3 * X ^ 4 - X ^ 5 - X ^ 6 + X ^ 7) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) * (1 - 2 * X ^ 2)) = A - (A * X ^ 1) - C (2 : ℚ) * (A * X ^ 2) + C (2 : ℚ) * (A * X ^ 3) := by
    rw [show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2]
    ring
  have e2 : (X * (50 - 20 * X - 50 * X ^ 2 + 22 * X ^ 3 - 3 * X ^ 4 - X ^ 5 - X ^ 6 + X ^ 7) : ℚ⟦X⟧) = C (50 : ℚ) * X ^ 1 - C (20 : ℚ) * X ^ 2 - C (50 : ℚ) * X ^ 3 + C (22 : ℚ) * X ^ 4 - C (3 : ℚ) * X ^ 5 - X ^ 6 - X ^ 7 + X ^ 8 := by
    rw [show (C (3 : ℚ) : ℚ⟦X⟧) = 3 from map_ofNat C 3, show (C (20 : ℚ) : ℚ⟦X⟧) = 20 from map_ofNat C 20, show (C (22 : ℚ) : ℚ⟦X⟧) = 22 from map_ofNat C 22, show (C (50 : ℚ) : ℚ⟦X⟧) = 50 from map_ofNat C 50]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_C, hA,
    coeff_mk]
  rcases Nat.lt_or_ge n 9 with hn | hn
  · interval_cases n <;> norm_num only [a1, a2, a3, a4, a5, a6, a7, a8, if_true, if_false]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
    have h' := (show (a (k + 9) : ℚ) + 2 * (a (k + 6) : ℚ) = (a (k + 8) : ℚ) + 2 * (a (k + 7) : ℚ) by simpa only [Nat.add_assoc, Nat.reduceAdd] using a_rec (k + 0))
    simp only [show k + 9 - 1 = k + 8 by omega, show k + 9 - 2 = k + 7 by omega, show k + 9 - 3 = k + 6 by omega, show k + 9 - 4 = k + 5 by omega, show k + 9 - 5 = k + 4 by omega, show k + 9 - 6 = k + 3 by omega, show k + 9 - 7 = k + 2 by omega, show k + 9 - 8 = k + 1 by omega, show ¬ (k + 9 = 0) by omega, show ¬ (k + 8 = 0) by omega, show ¬ (k + 7 = 0) by omega, show ¬ (k + 6 = 0) by omega, show ¬ (k + 5 = 0) by omega, show ¬ (k + 4 = 0) by omega, show ¬ (k + 3 = 0) by omega, show ¬ (k + 2 = 0) by omega, show ¬ (k + 1 = 0) by omega, show 1 ≤ k + 9 by omega, show 2 ≤ k + 9 by omega, show 3 ≤ k + 9 by omega, show 4 ≤ k + 9 by omega, show 5 ≤ k + 9 by omega, show 6 ≤ k + 9 by omega, show 7 ≤ k + 9 by omega, show 8 ≤ k + 9 by omega, show ¬ (k + 9 = 0) by omega, show ¬ (k + 9 = 1) by omega, show ¬ (k + 9 = 2) by omega, show ¬ (k + 9 = 3) by omega, show ¬ (k + 9 = 4) by omega, show ¬ (k + 9 = 5) by omega, show ¬ (k + 9 = 6) by omega, show ¬ (k + 9 = 7) by omega, show ¬ (k + 9 = 8) by omega, if_true, if_false]
    linear_combination h'

noncomputable def closed_Q (n : ℕ) : ℝ := if n % 2 = 0 then 15 * 2 ^ (n / 2) + 2 else 313 * 2 ^ ((n - 7) / 2) + 2

lemma closed_Q_rec (m : ℕ) (hm : 6 ≤ m) : closed_Q (m + 3) - 1 * closed_Q (m + 2) - 2 * closed_Q (m + 1) + 2 * closed_Q (m + 0) = 0 := by
  obtain ⟨t, rfl | rfl⟩ : ∃ t, m = 2 * t + 6 ∨ m = 2 * t + 7 := ⟨(m - 6) / 2, by omega⟩
  · unfold closed_Q
    rw [if_neg (show (2 * t + 6 + 3) % 2 ≠ 0 by omega), if_pos (show (2 * t + 6 + 2) % 2 = 0 by omega), if_neg (show (2 * t + 6 + 1) % 2 ≠ 0 by omega), if_pos (show (2 * t + 6 + 0) % 2 = 0 by omega)]
    rw [show (2 * t + 6 + 3 - 7) / 2 = t + 1 by omega, show (2 * t + 6 + 2) / 2 = t + 4 by omega, show (2 * t + 6 + 1 - 7) / 2 = t + 0 by omega, show (2 * t + 6 + 0) / 2 = t + 3 by omega]
    push_cast
    ring
  · unfold closed_Q
    rw [if_pos (show (2 * t + 7 + 3) % 2 = 0 by omega), if_neg (show (2 * t + 7 + 2) % 2 ≠ 0 by omega), if_pos (show (2 * t + 7 + 1) % 2 = 0 by omega), if_neg (show (2 * t + 7 + 0) % 2 ≠ 0 by omega)]
    rw [show (2 * t + 7 + 3) / 2 = t + 5 by omega, show (2 * t + 7 + 2 - 7) / 2 = t + 1 by omega, show (2 * t + 7 + 1) / 2 = t + 4 by omega, show (2 * t + 7 + 0 - 7) / 2 = t + 0 by omega]
    push_cast
    ring

lemma closed_key (n : ℕ) (hn : 6 ≤ n) : (a n : ℝ) = closed_Q n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 9 with h | h
    · interval_cases n
      · have hk : (a 6 : ℝ) = 122 := by exact_mod_cast a6
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 7 : ℝ) = 315 := by exact_mod_cast a7
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 8 : ℝ) = 242 := by exact_mod_cast a8
        rw [hk]
        unfold closed_Q
        norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
      have hR := (show (a (m + 9) : ℚ) + 2 * (a (m + 6) : ℚ) = (a (m + 8) : ℚ) + 2 * (a (m + 7) : ℚ) by simpa only [Nat.add_assoc, Nat.reduceAdd] using a_rec (m + 0))
      have hR' : (a (m + 9) : ℝ) + 2 * (a (m + 6) : ℝ) = (a (m + 8) : ℝ) + 2 * (a (m + 7) : ℝ) := by exact_mod_cast hR
      have h1 := ih (m + 8) (by omega) (by omega)
      have h2 := ih (m + 7) (by omega) (by omega)
      have h3 := ih (m + 6) (by omega) (by omega)
      have hG := closed_Q_rec (m + 6) (by omega)
      simp only [show m + 6 + 3 = m + 9 from rfl, show m + 6 + 2 = m + 8 from rfl, show m + 6 + 1 = m + 7 from rfl, show m + 6 + 0 = m + 6 from rfl] at hG
      linear_combination hR' + (-(-1 : ℝ)) * h1 + (-(-2 : ℝ)) * h2 + (-(2 : ℝ)) * h3 + (-1 : ℝ) * hG

theorem closed_even : ∀ n : ℕ, 5 < n → n % 2 = 0 → (a n : ℝ) = 15 * (2 : ℝ) ^ ((n : ℝ) / 2) + 2 := by
  intro n hn hp
  rw [closed_key n (by omega), closed_Q, if_pos (by omega)]
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
  rw [show 2 * m / 2 = m by omega,
    show ((2 * m : ℕ) : ℝ) / 2 = ((m : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]

theorem closed_odd : ∀ n : ℕ, 5 < n → n % 2 = 1 → (a n : ℝ) = 313 * (2 : ℝ) ^ (((n : ℝ) - 7) / 2) + 2 := by
  intro n hn hp
  rw [closed_key n (by omega), closed_Q, if_neg (by omega)]
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 7 := ⟨(n - 7) / 2, by omega⟩
  rw [show (2 * m + 7 - 7) / 2 = m by omega,
    show (((2 * m + 7 : ℕ) : ℝ) - 7) / 2 = ((m : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]

/-- Controls: the entry's data. -/
theorem controls : a 1 = 50 ∧ a 2 = 30 ∧ a 3 = 80 ∧ a 4 = 62 ∧ a 5 = 159 ∧ a 6 = 122 ∧ a 7 = 315 ∧ a 8 = 242 ∧ a 9 = 628 ∧ a 10 = 482 ∧ a 11 = 1254 ∧ a 12 = 962 ∧ a 13 = 2506 ∧ a 14 = 1922 ∧ a 15 = 5010 ∧ a 16 = 3842 ∧ a 17 = 10018 ∧ a 18 = 7682 ∧ a 19 = 20034 ∧ a 20 = 15362 ∧ a 21 = 40066 ∧ a 22 = 30722 ∧ a 23 = 80130 ∧ a 24 = 61442 ∧ a 25 = 160258 ∧ a 26 = 122882 ∧ a 27 = 320514 ∧ a 28 = 245762 ∧ a 29 = 641026 ∧ a 30 = 491522 ∧ a 31 = 1282050 ∧ a 32 = 983042 ∧ a 33 = 2564098 ∧ a 34 = 1966082 ∧ a 35 = 5128194 ∧ a 36 = 3932162 ∧ a 37 = 10256386 := by
  have v10 : (a 10 : ℚ) = 482 := by
    have h := a_rec 1
    simp only [Nat.reduceAdd] at h
    rw [a7, a8, a9] at h
    linarith
  have v11 : (a 11 : ℚ) = 1254 := by
    have h := a_rec 2
    simp only [Nat.reduceAdd] at h
    rw [a8, a9, v10] at h
    linarith
  have v12 : (a 12 : ℚ) = 962 := by
    have h := a_rec 3
    simp only [Nat.reduceAdd] at h
    rw [a9, v10, v11] at h
    linarith
  have v13 : (a 13 : ℚ) = 2506 := by
    have h := a_rec 4
    simp only [Nat.reduceAdd] at h
    rw [v10, v11, v12] at h
    linarith
  have v14 : (a 14 : ℚ) = 1922 := by
    have h := a_rec 5
    simp only [Nat.reduceAdd] at h
    rw [v11, v12, v13] at h
    linarith
  have v15 : (a 15 : ℚ) = 5010 := by
    have h := a_rec 6
    simp only [Nat.reduceAdd] at h
    rw [v12, v13, v14] at h
    linarith
  have v16 : (a 16 : ℚ) = 3842 := by
    have h := a_rec 7
    simp only [Nat.reduceAdd] at h
    rw [v13, v14, v15] at h
    linarith
  have v17 : (a 17 : ℚ) = 10018 := by
    have h := a_rec 8
    simp only [Nat.reduceAdd] at h
    rw [v14, v15, v16] at h
    linarith
  have v18 : (a 18 : ℚ) = 7682 := by
    have h := a_rec 9
    simp only [Nat.reduceAdd] at h
    rw [v15, v16, v17] at h
    linarith
  have v19 : (a 19 : ℚ) = 20034 := by
    have h := a_rec 10
    simp only [Nat.reduceAdd] at h
    rw [v16, v17, v18] at h
    linarith
  have v20 : (a 20 : ℚ) = 15362 := by
    have h := a_rec 11
    simp only [Nat.reduceAdd] at h
    rw [v17, v18, v19] at h
    linarith
  have v21 : (a 21 : ℚ) = 40066 := by
    have h := a_rec 12
    simp only [Nat.reduceAdd] at h
    rw [v18, v19, v20] at h
    linarith
  have v22 : (a 22 : ℚ) = 30722 := by
    have h := a_rec 13
    simp only [Nat.reduceAdd] at h
    rw [v19, v20, v21] at h
    linarith
  have v23 : (a 23 : ℚ) = 80130 := by
    have h := a_rec 14
    simp only [Nat.reduceAdd] at h
    rw [v20, v21, v22] at h
    linarith
  have v24 : (a 24 : ℚ) = 61442 := by
    have h := a_rec 15
    simp only [Nat.reduceAdd] at h
    rw [v21, v22, v23] at h
    linarith
  have v25 : (a 25 : ℚ) = 160258 := by
    have h := a_rec 16
    simp only [Nat.reduceAdd] at h
    rw [v22, v23, v24] at h
    linarith
  have v26 : (a 26 : ℚ) = 122882 := by
    have h := a_rec 17
    simp only [Nat.reduceAdd] at h
    rw [v23, v24, v25] at h
    linarith
  have v27 : (a 27 : ℚ) = 320514 := by
    have h := a_rec 18
    simp only [Nat.reduceAdd] at h
    rw [v24, v25, v26] at h
    linarith
  have v28 : (a 28 : ℚ) = 245762 := by
    have h := a_rec 19
    simp only [Nat.reduceAdd] at h
    rw [v25, v26, v27] at h
    linarith
  have v29 : (a 29 : ℚ) = 641026 := by
    have h := a_rec 20
    simp only [Nat.reduceAdd] at h
    rw [v26, v27, v28] at h
    linarith
  have v30 : (a 30 : ℚ) = 491522 := by
    have h := a_rec 21
    simp only [Nat.reduceAdd] at h
    rw [v27, v28, v29] at h
    linarith
  have v31 : (a 31 : ℚ) = 1282050 := by
    have h := a_rec 22
    simp only [Nat.reduceAdd] at h
    rw [v28, v29, v30] at h
    linarith
  have v32 : (a 32 : ℚ) = 983042 := by
    have h := a_rec 23
    simp only [Nat.reduceAdd] at h
    rw [v29, v30, v31] at h
    linarith
  have v33 : (a 33 : ℚ) = 2564098 := by
    have h := a_rec 24
    simp only [Nat.reduceAdd] at h
    rw [v30, v31, v32] at h
    linarith
  have v34 : (a 34 : ℚ) = 1966082 := by
    have h := a_rec 25
    simp only [Nat.reduceAdd] at h
    rw [v31, v32, v33] at h
    linarith
  have v35 : (a 35 : ℚ) = 5128194 := by
    have h := a_rec 26
    simp only [Nat.reduceAdd] at h
    rw [v32, v33, v34] at h
    linarith
  have v36 : (a 36 : ℚ) = 3932162 := by
    have h := a_rec 27
    simp only [Nat.reduceAdd] at h
    rw [v33, v34, v35] at h
    linarith
  have v37 : (a 37 : ℚ) = 10256386 := by
    have h := a_rec 28
    simp only [Nat.reduceAdd] at h
    rw [v34, v35, v36] at h
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · exact_mod_cast v28
  · exact_mod_cast v29
  · exact_mod_cast v30
  · exact_mod_cast v31
  · exact_mod_cast v32
  · exact_mod_cast v33
  · exact_mod_cast v34
  · exact_mod_cast v35
  · exact_mod_cast v36
  · exact_mod_cast v37

/-- The conjunction stated as `main`. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 2 * X ^ 2)) =
        X * (50 - 20 * X - 50 * X ^ 2 + 22 * X ^ 3 - 3 * X ^ 4 - X ^ 5 - X ^ 6 + X ^ 7) ∧
      (∀ n : ℕ, 5 < n → n % 2 = 0 → (a n : ℝ) = 15 * (2 : ℝ) ^ ((n : ℝ) / 2) + 2) ∧
      (∀ n : ℕ, 5 < n → n % 2 = 1 → (a n : ℝ) = 313 * (2 : ℝ) ^ (((n : ℝ) - 7) / 2) + 2) :=
  ⟨gf, closed_even, closed_odd⟩

end OMA.S_oeis_a207142

theorem OMA.solution : type_of% @OMA.S_oeis_a207142.main :=
  OMA.S_oeis_a207142.conjecture
