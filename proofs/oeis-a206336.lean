import OMAStatements.S_oeis_a206336

namespace OMA.S_oeis_a206336

open PowerSeries Finset


/-! ## Rows, the conditions on pairs and triples of rows -/

/-- A row. -/
abbrev Row := Fin 2 → Fin 4

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

lemma sum_cons {m : ℕ} (f : (Fin (m + 1) → Fin 4) → ℕ) :
    ∑ s : Fin (m + 1) → Fin 4, f s = ∑ x : Fin 4, ∑ t : Fin m → Fin 4, f (Fin.cons x t) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 4).symm _ _
    (fun s => by simp [Fin.consEquiv, Fin.cons_self_tail])

lemma sum_row (f : Row → ℕ) :
    ∑ s : Row, f s = ∑ x0 : Fin 4, ∑ x1 : Fin 4, f ![x0, x1] := by
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x0 _ => ?_)
  rw [sum_cons]
  refine Finset.sum_congr rfl (fun x1 _ => ?_)
  rw [Fintype.sum_unique]
  exact congrArg f (by funext j; fin_cases j <;> rfl)

/-! ## The kernel's numeric form -/

/-- Two 2 X 2 integer matrices sharing a row commute iff four entry equations hold. -/
lemma comm_iff (a b c d e f : ℤ) :
    !![a, b; c, d] * !![c, d; e, f] = !![c, d; e, f] * !![a, b; c, d] ↔
      a * c + b * e = c * a + d * c ∧ a * d + b * f = c * b + d * d ∧
        c * c + d * e = e * a + f * c ∧ c * d + d * f = e * b + f * d := by
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  constructor
  · intro h
    have h11 := congrFun (congrFun h 0) 0
    have h12 := congrFun (congrFun h 0) 1
    have h21 := congrFun (congrFun h 1) 0
    have h22 := congrFun (congrFun h 1) 1
    simp at h11 h12 h21 h22
    exact ⟨h11, h12, h21, h22⟩
  · rintro ⟨h11, h12, h21, h22⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h11, h12, h21, h22]

/-- The H2 condition on numbers, as a bit of a mask. -/
def gH2 (a b c d : ℕ) : Bool := Nat.beq (56028045529090772077795964601257853033323769988544797420047835138797599719424 >>> (((a * 4 + b) * 4 + c) * 4 + d) % 2) 1

lemma H2_iff : ∀ a b c d : Fin 4, (((a.val : ℤ) * (d.val : ℤ) - (b.val : ℤ) * (c.val : ℤ) ≠ 0)) ↔ gH2 a.val b.val c.val d.val = true := by
  decide +kernel

/-- The V2 condition on numbers, as a bit of a mask. -/
def gV2 (a b c d e f : ℕ) : Bool := Nat.beq (522194440706576253799692464809753519791871328201338565155470429349869677151929189852091932081322952995741560936475761351691441617451562053741550767023354620283432097681608984933822535408406489510355616629526471134087999051980290973359767949977074588642660143438896823361292765047659414738833296189169629016544823628895999833443075811858743806819556971199659537309354691548439155914064862696420386621394807494231713497289208176978193043833074440767628730396962400327039672092803849001679195736653196240995973255734834733661109362682475741212040344366265439424470765271900894788816359302163573290505291492187440850380702274883438845648024845149520361667280197139790385543506529741308373153109561362709359257907330146991772114624325090156754060730617153401885422914723334006184487367028693527350683055181832436854156765744855993672980056150042145805120935336489726897593871091076270842732069853110523451273222668795772826410050371436175610431062988158917505431792549232089207423179913197639242820191123432120474251198388000700015690472591305635028533886155377210033429806899274924472041086758982219193424755024836459369755502600759993737836011292572976446919395032449986875682551879246512550278431189568425454570814660137175252805419007 >>> (((((a * 4 + b) * 4 + c) * 4 + d) * 4 + e) * 4 + f) % 2) 1

lemma V2_iff : ∀ a b c d e f : Fin 4, ((!![(a.val : ℤ), (b.val : ℤ); (c.val : ℤ), (d.val : ℤ)] * !![(c.val : ℤ), (d.val : ℤ); (e.val : ℤ), (f.val : ℤ)] =
          !![(c.val : ℤ), (d.val : ℤ); (e.val : ℤ), (f.val : ℤ)] * !![(a.val : ℤ), (b.val : ℤ); (c.val : ℤ), (d.val : ℤ)])) ↔ gV2 a.val b.val c.val d.val e.val f.val = true := by
  intro a b c d e f
  rw [comm_iff]
  revert a b c d e f
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

/-- The sum of f over 0, ..., 3. -/
def sumK (f : ℕ → ℕ) : ℕ := f 0 + f 1 + f 2 + f 3

lemma sumK_fin (f : ℕ → ℕ) : ∑ x : Fin 4, f x.val = sumK f := by
  rw [Fin.sum_univ_eq_sum_range (fun x => f x) 4]
  simp [Finset.sum_range_succ, sumK]

/-- The concatenation of f over 0, ..., 3. -/
def catK (f : ℕ → List ℕ) : List ℕ := f 0 ++ f 1 ++ f 2 ++ f 3

/-- The code of a row: its entries as base-K digits, r 0 the most significant. -/
def code (r : Row) : ℕ := (r 0).val * 4 + (r 1).val

lemma code_lt (r : Row) : code r < 16 := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; omega

lemma dig0 (r : Row) : code r / 4 % 4 = (r 0).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; omega

lemma dig1 (r : Row) : code r % 4 = (r 1).val := by
  unfold code; have h0 := (r 0).isLt; have h1 := (r 1).isLt; omega

/-- The sum of g over all row codes. -/
def Ts (g : ℕ → ℕ) : ℕ := sumK (fun x0 => sumK (fun x1 => g (x0 * 4 + x1)))

lemma total (g : ℕ → ℕ) : (∑ s : Row, g (code s)) = Ts g := by
  rw [sum_row]
  simp only [code, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ]
  unfold Ts
  simp only [← sumK_fin]

def N1 (g : ℕ → ℕ) (r0 r1 s0 s1 : ℕ) (p2 p1 acc : ℕ) : ℕ :=
  sumK (fun x => bif gV2 r0 r1 s0 s1 p1 x then g (acc * 4 + x) else 0)

def M1 (r0 r1 s0 s1 : ℕ) (p2 p1 acc : ℕ) : List ℕ :=
  catK (fun x => bif gV2 r0 r1 s0 s1 p1 x then [acc * 4 + x] else [])

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
def L0 : ℕ := 0x7bdebffedffeeeeef7fe7bdefdfeeeeeff7effbe7bdeeeeefff0fff0fff00000

def tab0 (c : ℕ) : ℕ := L0 / 2 ^ (1 * c) % 2 ^ 1

def t0 (r s : Row) : ℕ := tab0 (pc r s)

/-- W(1, r, s) for every pair, packed: base 2^4 digit number pc r s. -/
def L1 : ℕ := 0x110011001000000011111010100000001001110010000000000000000c0000101000110010000010100010101000000110001011100000000000000000c0000110001000100000001011100010000001100110101000000000000000000c00001000100010000000100010101000000010011001100000000000000000000

def tab1 (c : ℕ) : ℕ := L1 / 2 ^ (4 * c) % 2 ^ 4

def t1 (r s : Row) : ℕ := tab1 (pc r s)

/-- W(2, r, s) for every pair, packed: base 2^4 digit number pc r s. -/
def L2 : ℕ := 0xc000c000c0000000c101c010c0000000c001c100c00000000000000003000010c000c000c0000000c000c000c0000000c000c011c00000000000000000400001c000c000c0000000c001c000c0000000c000c000c00000000000000000050000c000c000c0000000c000c000c0000000c000c001c00000000000000000000

def tab2 (c : ℕ) : ℕ := L2 / 2 ^ (4 * c) % 2 ^ 4

def t2 (r s : Row) : ℕ := tab2 (pc r s)

/-- W(3, r, s) for every pair, packed: base 2^6 digit number pc r s. -/
def L3 : ℕ := 0x300000400000500000000000304004400c005000000000003000304040005000000000000000000000000900000001003000004000005000000000003000004000005000000000003000004001305000000000000000000000000024000000043000004000005000000000003000044000005000000000003000004000005000000000000000000000000000940000003000004000005000000000003000004000005000000000003000004000005000000000000000000000000000000

def tab3 (c : ℕ) : ℕ := L3 / 2 ^ (6 * c) % 2 ^ 6

def t3 (r s : Row) : ℕ := tab3 (pc r s)

/-- W(4, r, s) for every pair, packed: base 2^6 digit number pc r s. -/
def L4 : ℕ := 0x2400002400002500000000002404032400502500000000002400012404002500000000000000000000000030000000102400002400002500000000002400002400002500000000002400002400116500000000000000000000000000c000000064000024000025000000000024000064000025000000000024000024000025000000000000000000000000000300000024000024000025000000000024000024000025000000000024000024000025000000000000000000000000000000

def tab4 (c : ℕ) : ℕ := L4 / 2 ^ (6 * c) % 2 ^ 6

def t4 (r s : Row) : ℕ := tab4 (pc r s)

/-- W(5, r, s) for every pair, packed: base 2^7 digit number pc r s. -/
def L5 : ℕ := 0xc000000c000000c0000000000000c020028c009400c0000000000000c000120c020000c0000000000000000000000000000da00000000400c000000c000000c0000000000000c000000c000000c0000000000000c000000c000528c000000000000000000000000000001b4000000008c000000c000000c0000000000000c000008c000000c0000000000000c000000c000000c00000000000000000000000000000003680000000c000000c000000c0000000000000c000000c000000c0000000000000c000000c000000c00000000000000000000000000000000000

def tab5 (c : ℕ) : ℕ := L5 / 2 ^ (7 * c) % 2 ^ 7

def t5 (r s : Row) : ℕ := tab5 (pc r s)

/-- W(6, r, s) for every pair, packed: base 2^7 digit number pc r s. -/
def L6 : ℕ := 0x6d000006d000006d0000000000006d02012ed003006d0000000000006d000066d020006d00000000000000000000000000004800000000406d000006d000006d0000000000006d000006d000006d0000000000006d000006d000466d0000000000000000000000000000009000000000ed000006d000006d0000000000006d00000ed000006d0000000000006d000006d000006d00000000000000000000000000000001200000006d000006d000006d0000000000006d000006d000006d0000000000006d000006d000006d00000000000000000000000000000000000

def tab6 (c : ℕ) : ℕ := L6 / 2 ^ (7 * c) % 2 ^ 7

def t6 (r s : Row) : ℕ := tab6 (pc r s)

/-- W(7, r, s) for every pair, packed: base 2^9 digit number pc r s. -/
def L7 : ℕ := 0x24000000024000000024000000000000000024008001824001b4002400000000000000002400000da24008000024000000000000000000000000000000000000a3800000000004002400000002400000002400000000000000002400000002400000002400000000000000002400000002400004da240000000000000000000000000000000000000051c0000000000224000000024000000024000000000000000024000000224000000024000000000000000024000000024000000024000000000000000000000000000000000000000028e00000000024000000024000000024000000000000000024000000024000000024000000000000000024000000024000000024000000000000000000000000000000000000000000000

def tab7 (c : ℕ) : ℕ := L7 / 2 ^ (9 * c) % 2 ^ 9

def t7 (r s : Row) : ℕ := tab7 (pc r s)

/-- W(8, r, s) for every pair, packed: base 2^9 digit number pc r s. -/
def L8 : ℕ := 0x14700000014700000014700000000000000014700800db47000900147000000000000000147000004947008000147000000000000000000000000000000000000360000000000040147000000147000000147000000000000000147000000147000000147000000000000000147000000147000044947000000000000000000000000000000000000001b0000000000034700000014700000014700000000000000014700000034700000014700000000000000014700000014700000014700000000000000000000000000000000000000000d800000000147000000147000000147000000000000000147000000147000000147000000000000000147000000147000000147000000000000000000000000000000000000000000000

def tab8 (c : ℕ) : ℕ := L8 / 2 ^ (9 * c) % 2 ^ 9

def t8 (r s : Row) : ℕ := tab8 (pc r s)

/-- W(9, r, s) for every pair, packed: base 2^10 digit number pc r s. -/
def L9 : ℕ := 0x6c000000006c000000006c0000000000000000006c004000906c001470006c0000000000000000006c0000051c6c004000006c0000000000000000000000000000000000000000f540000000000010006c000000006c000000006c0000000000000000006c000000006c000000006c0000000000000000006c000000006c0000151c6c0000000000000000000000000000000000000000003d500000000000046c000000006c000000006c0000000000000000006c000000046c000000006c0000000000000000006c000000006c000000006c000000000000000000000000000000000000000000000f5400000000006c000000006c000000006c0000000000000000006c000000006c000000006c0000000000000000006c000000006c000000006c00000000000000000000000000000000000000000000000000

def tab9 (c : ℕ) : ℕ := L9 / 2 ^ (10 * c) % 2 ^ 10

def t9 (r s : Row) : ℕ := tab9 (pc r s)

def step0 (c : ℕ) : Bool := tab0 c == (bif QB (c / 16 / 4 % 4) (c / 16 % 4) (c % 16 / 4 % 4) (c % 16 % 4) then 1 else 0)

def step1 (c : ℕ) : Bool := tab1 c ==
  (bif QB (c / 16 / 4 % 4) (c / 16 % 4) (c % 16 / 4 % 4) (c % 16 % 4) then ((Tl (c / 16 / 4 % 4) (c / 16 % 4) (c % 16 / 4 % 4) (c % 16 % 4)).map (fun t => tab0 (c % 16 * 16 + t))).sum else 0)

def step2 (c : ℕ) : Bool := tab2 c ==
  (bif QB (c / 16 / 4 % 4) (c / 16 % 4) (c % 16 / 4 % 4) (c % 16 % 4) then ((Tl (c / 16 / 4 % 4) (c / 16 % 4) (c % 16 / 4 % 4) (c % 16 % 4)).map (fun t => tab1 (c % 16 * 16 + t))).sum else 0)

def step3 (c : ℕ) : Bool := tab3 c ==
  (bif QB (c / 16 / 4 % 4) (c / 16 % 4) (c % 16 / 4 % 4) (c % 16 % 4) then ((Tl (c / 16 / 4 % 4) (c / 16 % 4) (c % 16 / 4 % 4) (c % 16 % 4)).map (fun t => tab2 (c % 16 * 16 + t))).sum else 0)

def step4 (c : ℕ) : Bool := tab4 c ==
  (bif QB (c / 16 / 4 % 4) (c / 16 % 4) (c % 16 / 4 % 4) (c % 16 % 4) then ((Tl (c / 16 / 4 % 4) (c / 16 % 4) (c % 16 / 4 % 4) (c % 16 % 4)).map (fun t => tab3 (c % 16 * 16 + t))).sum else 0)

def step5 (c : ℕ) : Bool := tab5 c ==
  (bif QB (c / 16 / 4 % 4) (c / 16 % 4) (c % 16 / 4 % 4) (c % 16 % 4) then ((Tl (c / 16 / 4 % 4) (c / 16 % 4) (c % 16 / 4 % 4) (c % 16 % 4)).map (fun t => tab4 (c % 16 * 16 + t))).sum else 0)

def step6 (c : ℕ) : Bool := tab6 c ==
  (bif QB (c / 16 / 4 % 4) (c / 16 % 4) (c % 16 / 4 % 4) (c % 16 % 4) then ((Tl (c / 16 / 4 % 4) (c / 16 % 4) (c % 16 / 4 % 4) (c % 16 % 4)).map (fun t => tab5 (c % 16 * 16 + t))).sum else 0)

def step7 (c : ℕ) : Bool := tab7 c ==
  (bif QB (c / 16 / 4 % 4) (c / 16 % 4) (c % 16 / 4 % 4) (c % 16 % 4) then ((Tl (c / 16 / 4 % 4) (c / 16 % 4) (c % 16 / 4 % 4) (c % 16 % 4)).map (fun t => tab6 (c % 16 * 16 + t))).sum else 0)

def step8 (c : ℕ) : Bool := tab8 c ==
  (bif QB (c / 16 / 4 % 4) (c / 16 % 4) (c % 16 / 4 % 4) (c % 16 % 4) then ((Tl (c / 16 / 4 % 4) (c / 16 % 4) (c % 16 / 4 % 4) (c % 16 % 4)).map (fun t => tab7 (c % 16 * 16 + t))).sum else 0)

def step9 (c : ℕ) : Bool := tab9 c ==
  (bif QB (c / 16 / 4 % 4) (c / 16 % 4) (c % 16 / 4 % 4) (c % 16 % 4) then ((Tl (c / 16 / 4 % 4) (c / 16 % 4) (c % 16 / 4 % 4) (c % 16 % 4)).map (fun t => tab8 (c % 16 * 16 + t))).sum else 0)

/-- The relation on the tables at the pair code c. -/
def relB (c : ℕ) : Bool := (bif QB (c / 16 / 4 % 4) (c / 16 % 4) (c % 16 / 4 % 4) (c % 16 % 4) then ((Tl (c / 16 / 4 % 4) (c / 16 % 4) (c % 16 / 4 % 4) (c % 16 % 4)).map (fun t => tab9 ((c % 16) * 16 + t))).sum else 0) + 3 * tab7 c == tab9 c + 3 * tab8 c

def rowB (c : ℕ) : Bool := step0 c && step1 c && step2 c && step3 c && step4 c && step5 c && step6 c && step7 c && step8 c && step9 c && relB c

lemma chunk0_ok : (List.range' 0 256).all rowB = true := by
  decide +kernel

def allB : Bool := (Ts (fun x => Ts (fun y => tab0 (x * 16 + y))) == 192) && (Ts (fun x => Ts (fun y => tab1 (x * 16 + y))) == 96) && (Ts (fun x => Ts (fun y => tab2 (x * 16 + y))) == 455) && (Ts (fun x => Ts (fun y => tab3 (x * 16 + y))) == 296) && (Ts (fun x => Ts (fun y => tab4 (x * 16 + y))) == 1376) && (Ts (fun x => Ts (fun y => tab5 (x * 16 + y))) == 880) && (Ts (fun x => Ts (fun y => tab6 (x * 16 + y))) == 4111) && (Ts (fun x => Ts (fun y => tab7 (x * 16 + y))) == 2622) && (Ts (fun x => Ts (fun y => tab8 (x * 16 + y))) == 12319) && (Ts (fun x => Ts (fun y => tab9 (x * 16 + y))) == 7854)

lemma all_ok : allB = true := by
  decide +kernel

lemma all_parts : (Ts (fun x => Ts (fun y => tab0 (x * 16 + y))) == 192) = true ∧ (Ts (fun x => Ts (fun y => tab1 (x * 16 + y))) == 96) = true ∧ (Ts (fun x => Ts (fun y => tab2 (x * 16 + y))) == 455) = true ∧ (Ts (fun x => Ts (fun y => tab3 (x * 16 + y))) == 296) = true ∧ (Ts (fun x => Ts (fun y => tab4 (x * 16 + y))) == 1376) = true ∧ (Ts (fun x => Ts (fun y => tab5 (x * 16 + y))) == 880) = true ∧ (Ts (fun x => Ts (fun y => tab6 (x * 16 + y))) == 4111) = true ∧ (Ts (fun x => Ts (fun y => tab7 (x * 16 + y))) == 2622) = true ∧ (Ts (fun x => Ts (fun y => tab8 (x * 16 + y))) == 12319) = true ∧ (Ts (fun x => Ts (fun y => tab9 (x * 16 + y))) == 7854) = true := by
  have h := all_ok
  unfold allB at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

lemma row_ok (c : ℕ) (hc : c < 256) : step0 c = true ∧ step1 c = true ∧ step2 c = true ∧ step3 c = true ∧ step4 c = true ∧ step5 c = true ∧ step6 c = true ∧ step7 c = true ∧ step8 c = true ∧ step9 c = true ∧ relB c = true := by
  have h : rowB c = true := by
    by_cases h0 : c < 256
    · exact List.all_eq_true.mp chunk0_ok c (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    omega
  unfold rowB at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

lemma pc_digits (r s : Row) :
    (pc r s / 16 / 4 % 4) = (r 0).val ∧ (pc r s / 16 % 4) = (r 1).val ∧ (pc r s % 16 / 4 % 4) = (s 0).val ∧ (pc r s % 16 % 4) = (s 1).val := by
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
  rw [bridge (fun t => tab0 (code s * 16 + t)) r s, Tn_list]
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
  rw [bridge (fun t => tab1 (code s * 16 + t)) r s, Tn_list]
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
  rw [bridge (fun t => tab2 (code s * 16 + t)) r s, Tn_list]
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
  rw [bridge (fun t => tab3 (code s * 16 + t)) r s, Tn_list]
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
  rw [bridge (fun t => tab4 (code s * 16 + t)) r s, Tn_list]
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
  rw [bridge (fun t => tab5 (code s * 16 + t)) r s, Tn_list]
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
  rw [bridge (fun t => tab6 (code s * 16 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.2.2.2.2.1
  unfold step7 at h
  obtain ⟨e0, e1, e2, e3⟩ := pc_digits r s
  rw [e0, e1, e2, e3, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W8f (r s : Row) : W 8 r s = t8 r s := by
  rw [W_succ]
  simp only [W7f, t7, pc]
  rw [bridge (fun t => tab7 (code s * 16 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.2.2.2.2.2.1
  unfold step8 at h
  obtain ⟨e0, e1, e2, e3⟩ := pc_digits r s
  rw [e0, e1, e2, e3, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma W9f (r s : Row) : W 9 r s = t9 r s := by
  rw [W_succ]
  simp only [W8f, t8, pc]
  rw [bridge (fun t => tab8 (code s * 16 + t)) r s, Tn_list]
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.2.2.2.2.2.2.1
  unfold step9 at h
  obtain ⟨e0, e1, e2, e3⟩ := pc_digits r s
  rw [e0, e1, e2, e3, pc_mod] at h
  rw [Bool.cond_eq_ite] at h
  simp only [Q_iff]
  exact (beq_iff_eq.mp h).symm

lemma rel_at (r s : Row) : (if QB (r 0).val (r 1).val (s 0).val (s 1).val = true then ((Tl (r 0).val (r 1).val (s 0).val (s 1).val).map (fun t => tab9 ((code s) * 16 + t))).sum else 0) + 3 * tab7 (pc r s) = tab9 (pc r s) + 3 * tab8 (pc r s) := by
  have h := (row_ok (pc r s) (pc_lt r s)).2.2.2.2.2.2.2.2.2.2
  unfold relB at h
  obtain ⟨e0, e1, e2, e3⟩ := pc_digits r s
  rw [e0, e1, e2, e3, pc_mod] at h
  simp only [Bool.cond_eq_ite] at h
  exact beq_iff_eq.mp h

lemma W_rec (k : ℕ) : ∀ r s : Row, W (k + 10) r s + 3 * W (k + 7) r s = W (k + 9) r s + 3 * W (k + 8) r s := by
  induction k with
  | zero =>
    intro r s
    simp only [Nat.zero_add, W7f, W8f, W9f, t7, t8, t9]
    rw [W_succ]
    simp only [W9f, t9, pc]
    rw [bridge (fun t => tab9 (code s * 16 + t)) r s, Tn_list]
    simp only [Q_iff]
    exact rel_at r s
  | succ k ih =>
    intro r s
    rw [show k + 1 + 7 = (k + 7) + 1 from rfl, show k + 1 + 8 = (k + 8) + 1 from rfl, show k + 1 + 9 = (k + 9) + 1 from rfl, show k + 1 + 10 = (k + 10) + 1 from rfl]
    rw [W_succ (k + 7), W_succ (k + 8), W_succ (k + 9), W_succ (k + 10)]
    split_ifs with hq
    · simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      split_ifs
      · exact ih s t
      · simp
    · simp

lemma cnt_rec (k : ℕ) : cnt (k + 11) + 3 * cnt (k + 8) = cnt (k + 10) + 3 * cnt (k + 9) := by
  rw [show k + 8 = (k + 7) + 1 from rfl, show k + 9 = (k + 8) + 1 from rfl, show k + 10 = (k + 9) + 1 from rfl, show k + 11 = (k + 10) + 1 from rfl]
  simp only [cnt_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ => ?_))
  exact W_rec k r s

lemma cnt1 : cnt 1 = 192 := by
  rw [cnt_sum]
  simp only [W0f, t0, pc]
  rw [total2 tab0]
  exact beq_iff_eq.mp all_parts.1

lemma cnt2 : cnt 2 = 96 := by
  rw [cnt_sum]
  simp only [W1f, t1, pc]
  rw [total2 tab1]
  exact beq_iff_eq.mp all_parts.2.1

lemma cnt3 : cnt 3 = 455 := by
  rw [cnt_sum]
  simp only [W2f, t2, pc]
  rw [total2 tab2]
  exact beq_iff_eq.mp all_parts.2.2.1

lemma cnt4 : cnt 4 = 296 := by
  rw [cnt_sum]
  simp only [W3f, t3, pc]
  rw [total2 tab3]
  exact beq_iff_eq.mp all_parts.2.2.2.1

lemma cnt5 : cnt 5 = 1376 := by
  rw [cnt_sum]
  simp only [W4f, t4, pc]
  rw [total2 tab4]
  exact beq_iff_eq.mp all_parts.2.2.2.2.1

lemma cnt6 : cnt 6 = 880 := by
  rw [cnt_sum]
  simp only [W5f, t5, pc]
  rw [total2 tab5]
  exact beq_iff_eq.mp all_parts.2.2.2.2.2.1

lemma cnt7 : cnt 7 = 4111 := by
  rw [cnt_sum]
  simp only [W6f, t6, pc]
  rw [total2 tab6]
  exact beq_iff_eq.mp all_parts.2.2.2.2.2.2.1

lemma cnt8 : cnt 8 = 2622 := by
  rw [cnt_sum]
  simp only [W7f, t7, pc]
  rw [total2 tab7]
  exact beq_iff_eq.mp all_parts.2.2.2.2.2.2.2.1

lemma cnt9 : cnt 9 = 12319 := by
  rw [cnt_sum]
  simp only [W8f, t8, pc]
  rw [total2 tab8]
  exact beq_iff_eq.mp all_parts.2.2.2.2.2.2.2.2.1

lemma cnt10 : cnt 10 = 7854 := by
  rw [cnt_sum]
  simp only [W9f, t9, pc]
  rw [total2 tab9]
  exact beq_iff_eq.mp all_parts.2.2.2.2.2.2.2.2.2

lemma cnt11 : cnt 11 = 36945 := by
  have h := cnt_rec 0
  simp only [Nat.zero_add] at h
  rw [cnt8, cnt9, cnt10] at h
  generalize cnt 11 = x at h ⊢
  omega

lemma a_cast (n : ℕ) : (a n : ℚ) = (cnt n : ℚ) := by
  rw [a_eq]

lemma a_rec (k : ℕ) : (a (k + 11) : ℚ) + 3 * (a (k + 8) : ℚ) = (a (k + 10) : ℚ) + 3 * (a (k + 9) : ℚ) := by
  simp only [a_cast]
  have h : cnt (k + 11) + 3 * cnt (k + 8) = cnt (k + 10) + 3 * cnt (k + 9) := by simpa only [Nat.add_assoc, Nat.reduceAdd] using cnt_rec (k + 0)
  have h' : ((cnt (k + 11) : ℕ) : ℚ) + 3 * ((cnt (k + 8) : ℕ) : ℚ) = ((cnt (k + 10) : ℕ) : ℚ) + 3 * ((cnt (k + 9) : ℕ) : ℚ) := by exact_mod_cast h
  linear_combination h'

lemma a1 : (a 1 : ℚ) = 192 := by
  rw [a_cast, cnt1]
  norm_num

lemma a2 : (a 2 : ℚ) = 96 := by
  rw [a_cast, cnt2]
  norm_num

lemma a3 : (a 3 : ℚ) = 455 := by
  rw [a_cast, cnt3]
  norm_num

lemma a4 : (a 4 : ℚ) = 296 := by
  rw [a_cast, cnt4]
  norm_num

lemma a5 : (a 5 : ℚ) = 1376 := by
  rw [a_cast, cnt5]
  norm_num

lemma a6 : (a 6 : ℚ) = 880 := by
  rw [a_cast, cnt6]
  norm_num

lemma a7 : (a 7 : ℚ) = 4111 := by
  rw [a_cast, cnt7]
  norm_num

lemma a8 : (a 8 : ℚ) = 2622 := by
  rw [a_cast, cnt8]
  norm_num

lemma a9 : (a 9 : ℚ) = 12319 := by
  rw [a_cast, cnt9]
  norm_num

lemma a10 : (a 10 : ℚ) = 7854 := by
  rw [a_cast, cnt10]
  norm_num

lemma a11 : (a 11 : ℚ) = 36945 := by
  rw [a_cast, cnt11]
  norm_num

/-- The g.f. as stated. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) * (1 - 3 * X ^ 2)) =
      X * (192 - 96 * X - 217 * X ^ 2 + 129 * X ^ 3 + 3 * X ^ 4 - 19 * X ^ 5 - 9 * X ^ 6 - X ^ 7 +
        4 * X ^ 8 + 2 * X ^ 9) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) * (1 - 3 * X ^ 2)) = A - (A * X ^ 1) - C (3 : ℚ) * (A * X ^ 2) + C (3 : ℚ) * (A * X ^ 3) := by
    rw [show (C (3 : ℚ) : ℚ⟦X⟧) = 3 from map_ofNat C 3]
    ring
  have e2 : (X * (192 - 96 * X - 217 * X ^ 2 + 129 * X ^ 3 + 3 * X ^ 4 - 19 * X ^ 5 - 9 * X ^ 6 - X ^ 7 +
        4 * X ^ 8 + 2 * X ^ 9) : ℚ⟦X⟧) = C (192 : ℚ) * X ^ 1 - C (96 : ℚ) * X ^ 2 - C (217 : ℚ) * X ^ 3 + C (129 : ℚ) * X ^ 4 + C (3 : ℚ) * X ^ 5 - C (19 : ℚ) * X ^ 6 - C (9 : ℚ) * X ^ 7 - X ^ 8 + C (4 : ℚ) * X ^ 9 + C (2 : ℚ) * X ^ 10 := by
    rw [show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2, show (C (3 : ℚ) : ℚ⟦X⟧) = 3 from map_ofNat C 3, show (C (4 : ℚ) : ℚ⟦X⟧) = 4 from map_ofNat C 4, show (C (9 : ℚ) : ℚ⟦X⟧) = 9 from map_ofNat C 9, show (C (19 : ℚ) : ℚ⟦X⟧) = 19 from map_ofNat C 19, show (C (96 : ℚ) : ℚ⟦X⟧) = 96 from map_ofNat C 96, show (C (129 : ℚ) : ℚ⟦X⟧) = 129 from map_ofNat C 129, show (C (192 : ℚ) : ℚ⟦X⟧) = 192 from map_ofNat C 192, show (C (217 : ℚ) : ℚ⟦X⟧) = 217 from map_ofNat C 217]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_C, hA,
    coeff_mk]
  rcases Nat.lt_or_ge n 11 with hn | hn
  · interval_cases n <;> norm_num only [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, if_true, if_false]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 11 := ⟨n - 11, by omega⟩
    have h' := (show (a (k + 11) : ℚ) + 3 * (a (k + 8) : ℚ) = (a (k + 10) : ℚ) + 3 * (a (k + 9) : ℚ) by simpa only [Nat.add_assoc, Nat.reduceAdd] using a_rec (k + 0))
    simp only [show k + 11 - 1 = k + 10 by omega, show k + 11 - 2 = k + 9 by omega, show k + 11 - 3 = k + 8 by omega, show k + 11 - 4 = k + 7 by omega, show k + 11 - 5 = k + 6 by omega, show k + 11 - 6 = k + 5 by omega, show k + 11 - 7 = k + 4 by omega, show k + 11 - 8 = k + 3 by omega, show k + 11 - 9 = k + 2 by omega, show k + 11 - 10 = k + 1 by omega, show ¬ (k + 11 = 0) by omega, show ¬ (k + 10 = 0) by omega, show ¬ (k + 9 = 0) by omega, show ¬ (k + 8 = 0) by omega, show ¬ (k + 7 = 0) by omega, show ¬ (k + 6 = 0) by omega, show ¬ (k + 5 = 0) by omega, show ¬ (k + 4 = 0) by omega, show ¬ (k + 3 = 0) by omega, show ¬ (k + 2 = 0) by omega, show ¬ (k + 1 = 0) by omega, show 1 ≤ k + 11 by omega, show 2 ≤ k + 11 by omega, show 3 ≤ k + 11 by omega, show 4 ≤ k + 11 by omega, show 5 ≤ k + 11 by omega, show 6 ≤ k + 11 by omega, show 7 ≤ k + 11 by omega, show 8 ≤ k + 11 by omega, show 9 ≤ k + 11 by omega, show 10 ≤ k + 11 by omega, show ¬ (k + 11 = 0) by omega, show ¬ (k + 11 = 1) by omega, show ¬ (k + 11 = 2) by omega, show ¬ (k + 11 = 3) by omega, show ¬ (k + 11 = 4) by omega, show ¬ (k + 11 = 5) by omega, show ¬ (k + 11 = 6) by omega, show ¬ (k + 11 = 7) by omega, show ¬ (k + 11 = 8) by omega, show ¬ (k + 11 = 9) by omega, show ¬ (k + 11 = 10) by omega, if_true, if_false]
    linear_combination h'

noncomputable def closed_Q (n : ℕ) : ℝ := if n % 2 = 0 then 872 * 3 ^ ((n - 6) / 2) + 6 else 12313 * 3 ^ ((n - 9) / 2) + 6

lemma closed_Q_rec (m : ℕ) (hm : 8 ≤ m) : closed_Q (m + 3) - 1 * closed_Q (m + 2) - 3 * closed_Q (m + 1) + 3 * closed_Q (m + 0) = 0 := by
  obtain ⟨t, rfl | rfl⟩ : ∃ t, m = 2 * t + 8 ∨ m = 2 * t + 9 := ⟨(m - 8) / 2, by omega⟩
  · unfold closed_Q
    rw [if_neg (show (2 * t + 8 + 3) % 2 ≠ 0 by omega), if_pos (show (2 * t + 8 + 2) % 2 = 0 by omega), if_neg (show (2 * t + 8 + 1) % 2 ≠ 0 by omega), if_pos (show (2 * t + 8 + 0) % 2 = 0 by omega)]
    rw [show (2 * t + 8 + 3 - 9) / 2 = t + 1 by omega, show (2 * t + 8 + 2 - 6) / 2 = t + 2 by omega, show (2 * t + 8 + 1 - 9) / 2 = t + 0 by omega, show (2 * t + 8 + 0 - 6) / 2 = t + 1 by omega]
    push_cast
    ring
  · unfold closed_Q
    rw [if_pos (show (2 * t + 9 + 3) % 2 = 0 by omega), if_neg (show (2 * t + 9 + 2) % 2 ≠ 0 by omega), if_pos (show (2 * t + 9 + 1) % 2 = 0 by omega), if_neg (show (2 * t + 9 + 0) % 2 ≠ 0 by omega)]
    rw [show (2 * t + 9 + 3 - 6) / 2 = t + 3 by omega, show (2 * t + 9 + 2 - 9) / 2 = t + 1 by omega, show (2 * t + 9 + 1 - 6) / 2 = t + 2 by omega, show (2 * t + 9 + 0 - 9) / 2 = t + 0 by omega]
    push_cast
    ring

lemma closed_key (n : ℕ) (hn : 8 ≤ n) : (a n : ℝ) = closed_Q n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 11 with h | h
    · interval_cases n
      · have hk : (a 8 : ℝ) = 2622 := by exact_mod_cast a8
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 9 : ℝ) = 12319 := by exact_mod_cast a9
        rw [hk]
        unfold closed_Q
        norm_num
      · have hk : (a 10 : ℝ) = 7854 := by exact_mod_cast a10
        rw [hk]
        unfold closed_Q
        norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
      have hR := (show (a (m + 11) : ℚ) + 3 * (a (m + 8) : ℚ) = (a (m + 10) : ℚ) + 3 * (a (m + 9) : ℚ) by simpa only [Nat.add_assoc, Nat.reduceAdd] using a_rec (m + 0))
      have hR' : (a (m + 11) : ℝ) + 3 * (a (m + 8) : ℝ) = (a (m + 10) : ℝ) + 3 * (a (m + 9) : ℝ) := by exact_mod_cast hR
      have h1 := ih (m + 10) (by omega) (by omega)
      have h2 := ih (m + 9) (by omega) (by omega)
      have h3 := ih (m + 8) (by omega) (by omega)
      have hG := closed_Q_rec (m + 8) (by omega)
      simp only [show m + 8 + 3 = m + 11 from rfl, show m + 8 + 2 = m + 10 from rfl, show m + 8 + 1 = m + 9 from rfl, show m + 8 + 0 = m + 8 from rfl] at hG
      linear_combination hR' + (-(-1 : ℝ)) * h1 + (-(-3 : ℝ)) * h2 + (-(3 : ℝ)) * h3 + (-1 : ℝ) * hG

theorem closed_even : ∀ n : ℕ, 7 < n → n % 2 = 0 → (a n : ℝ) =
      872 * (3 : ℝ) ^ (((n : ℝ) - 9) / 2 + 3 / 2) + 6 := by
  intro n hn hp
  rw [closed_key n (by omega), closed_Q, if_pos (by omega)]
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
  rw [show (2 * m - 6) / 2 = m - 3 by omega,
    show (((2 * m : ℕ) : ℝ) - 9) / 2 + 3 / 2 = ((m - 3 : ℕ) : ℝ) by
      rw [Nat.cast_sub (by omega)]; push_cast; ring,
    Real.rpow_natCast]

theorem closed_odd : ∀ n : ℕ, 7 < n → n % 2 = 1 → (a n : ℝ) = 12313 * (3 : ℝ) ^ (((n : ℝ) - 9) / 2) + 6 := by
  intro n hn hp
  rw [closed_key n (by omega), closed_Q, if_neg (by omega)]
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 9 := ⟨(n - 9) / 2, by omega⟩
  rw [show (2 * m + 9 - 9) / 2 = m by omega,
    show (((2 * m + 9 : ℕ) : ℝ) - 9) / 2 = ((m : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]

/-- Controls: the entry's data. -/
theorem controls : a 1 = 192 ∧ a 2 = 96 ∧ a 3 = 455 ∧ a 4 = 296 ∧ a 5 = 1376 ∧ a 6 = 880 ∧ a 7 = 4111 ∧ a 8 = 2622 ∧ a 9 = 12319 ∧ a 10 = 7854 ∧ a 11 = 36945 ∧ a 12 = 23550 ∧ a 13 = 110823 ∧ a 14 = 70638 ∧ a 15 = 332457 ∧ a 16 = 211902 ∧ a 17 = 997359 ∧ a 18 = 635694 ∧ a 19 = 2992065 ∧ a 20 = 1907070 := by
  have v12 : (a 12 : ℚ) = 23550 := by
    have h := a_rec 1
    simp only [Nat.reduceAdd] at h
    rw [a9, a10, a11] at h
    linarith
  have v13 : (a 13 : ℚ) = 110823 := by
    have h := a_rec 2
    simp only [Nat.reduceAdd] at h
    rw [a10, a11, v12] at h
    linarith
  have v14 : (a 14 : ℚ) = 70638 := by
    have h := a_rec 3
    simp only [Nat.reduceAdd] at h
    rw [a11, v12, v13] at h
    linarith
  have v15 : (a 15 : ℚ) = 332457 := by
    have h := a_rec 4
    simp only [Nat.reduceAdd] at h
    rw [v12, v13, v14] at h
    linarith
  have v16 : (a 16 : ℚ) = 211902 := by
    have h := a_rec 5
    simp only [Nat.reduceAdd] at h
    rw [v13, v14, v15] at h
    linarith
  have v17 : (a 17 : ℚ) = 997359 := by
    have h := a_rec 6
    simp only [Nat.reduceAdd] at h
    rw [v14, v15, v16] at h
    linarith
  have v18 : (a 18 : ℚ) = 635694 := by
    have h := a_rec 7
    simp only [Nat.reduceAdd] at h
    rw [v15, v16, v17] at h
    linarith
  have v19 : (a 19 : ℚ) = 2992065 := by
    have h := a_rec 8
    simp only [Nat.reduceAdd] at h
    rw [v16, v17, v18] at h
    linarith
  have v20 : (a 20 : ℚ) = 1907070 := by
    have h := a_rec 9
    simp only [Nat.reduceAdd] at h
    rw [v17, v18, v19] at h
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast a1
  · exact_mod_cast a2
  · exact_mod_cast a3
  · exact_mod_cast a4
  · exact_mod_cast a5
  · exact_mod_cast a6
  · exact_mod_cast a7
  · exact_mod_cast a8
  · exact_mod_cast a9
  · exact_mod_cast a10
  · exact_mod_cast a11
  · exact_mod_cast v12
  · exact_mod_cast v13
  · exact_mod_cast v14
  · exact_mod_cast v15
  · exact_mod_cast v16
  · exact_mod_cast v17
  · exact_mod_cast v18
  · exact_mod_cast v19
  · exact_mod_cast v20

/-- The conjunction stated as `main`. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 3 * X ^ 2)) =
        X * (192 - 96 * X - 217 * X ^ 2 + 129 * X ^ 3 + 3 * X ^ 4 - 19 * X ^ 5 - 9 * X ^ 6 - X ^ 7 +
            4 * X ^ 8 + 2 * X ^ 9) ∧
      (∀ n : ℕ, 7 < n → n % 2 = 0 → (a n : ℝ) =
          872 * (3 : ℝ) ^ (((n : ℝ) - 9) / 2 + 3 / 2) + 6) ∧
      (∀ n : ℕ, 7 < n → n % 2 = 1 → (a n : ℝ) = 12313 * (3 : ℝ) ^ (((n : ℝ) - 9) / 2) + 6) :=
  ⟨gf, closed_even, closed_odd⟩

end OMA.S_oeis_a206336

theorem OMA.solution : type_of% @OMA.S_oeis_a206336.main :=
  OMA.S_oeis_a206336.conjecture
