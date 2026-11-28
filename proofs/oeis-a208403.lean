import OMAStatements.S_oeis_a208403
/-!
Proof of Barker's two conjectures for A208403. The arrays are counted row by row from the top: V m q c is
the number of good arrays with m rows below the row q (none at the top), with c values already
introduced. V (m + 1) q c is a sum over the next row, and V m satisfies Barker's recurrence
entrywise from m = 2 on, checked on tables of V 0 .. V 4 by the kernel; the g.f. and the closed
form follow. The lemmas on values introduced in row major order (RGSfrom, rowRgs, newc and their
cons lemmas) are adapted from the merged proof of oeis-a205220 by @jleguina, as is the pattern of
the g.f. step (from the merged proof of oeis-a202456 by @jleguina).
-/

namespace OMA.S_oeis_a208403

open PowerSeries Finset

abbrev Row := Fin 3 → Fin 4

/-! ## Values introduced in row major order (adapted from @jleguina, oeis-a205220) -/

/-- The values below c count as introduced before the array; every other value below an entry
occurs at an earlier position in row major order. -/
def RGSfrom {R C K : ℕ} (c : ℕ) (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i j, ∀ u : Fin K, u < x i j → u.val < c ∨ ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ x i' j' = u

instance {R C K : ℕ} (c : ℕ) : DecidablePred (@RGSfrom R C K c) := fun x => by
  unfold RGSfrom; infer_instance

/-- The same for one row. -/
def rowRgs {C K : ℕ} (c : ℕ) (r : Fin C → Fin K) : Prop :=
  ∀ j, ∀ u : Fin K, u < r j → u.val < c ∨ ∃ j', j' < j ∧ r j' = u

instance {C K : ℕ} (c : ℕ) : DecidablePred (@rowRgs C K c) := fun r => by
  unfold rowRgs; infer_instance

/-- The number of values introduced after the row r, when c were introduced before it. -/
def newc {C K : ℕ} (c : ℕ) (r : Fin C → Fin K) : ℕ := max c (univ.sup fun j => (r j).val + 1)

lemma lt_newc {C K : ℕ} (c : ℕ) (r : Fin C → Fin K) (u : ℕ) :
    u < newc c r ↔ u < c ∨ ∃ j, u ≤ (r j).val := by
  unfold newc
  rw [lt_max_iff, Finset.lt_sup_iff]
  simp

lemma newc_le {C K : ℕ} (c : ℕ) (hc : c ≤ K) (r : Fin C → Fin K) : newc c r ≤ K :=
  max_le hc (Finset.sup_le fun j _ => (r j).isLt)

lemma rmn_iff {R C K : ℕ} (x : Fin R → Fin C → Fin K) : RowMajorNew x ↔ RGSfrom 0 x := by
  unfold RowMajorNew RGSfrom
  simp only [Nat.not_lt_zero, false_or]

lemma RGSfrom_zero {C K : ℕ} (c : ℕ) (f : Fin 0 → Fin C → Fin K) : RGSfrom c f := fun i => i.elim0

lemma RGSfrom_cons {n C K : ℕ} (c : ℕ) (r : Fin C → Fin K) (h : Fin n → Fin C → Fin K) :
    RGSfrom c (Fin.cons r h : Fin (n + 1) → Fin C → Fin K) ↔
      rowRgs c r ∧ RGSfrom (newc c r) h := by
  constructor
  · intro H
    refine ⟨fun j u hu => ?_, fun i j u hu => ?_⟩
    · rcases H 0 j u (by simpa using hu) with h1 | ⟨i', j', hb, he⟩
      · exact Or.inl h1
      · right
        rcases hb with hb | ⟨rfl, hj⟩
        · exact absurd hb (Fin.not_lt_zero _)
        · exact ⟨j', hj, by simpa using he⟩
    · rcases H i.succ j u (by simpa using hu) with h1 | ⟨i', j', hb, he⟩
      · left
        rw [lt_newc]
        exact Or.inl h1
      · induction i' using Fin.cases with
        | zero =>
          left
          rw [lt_newc]
          right
          refine ⟨j', ?_⟩
          simp only [Fin.cons_zero] at he
          rw [he]
        | succ i'' =>
          right
          refine ⟨i'', j', ?_, by simpa using he⟩
          rcases hb with hb | ⟨hb, hj⟩
          · exact Or.inl (Fin.succ_lt_succ_iff.mp hb)
          · exact Or.inr ⟨Fin.succ_injective _ hb, hj⟩
  · rintro ⟨H0, H⟩ i j u hu
    induction i using Fin.cases with
    | zero =>
      rcases H0 j u (by simpa using hu) with h1 | ⟨j', hj, he⟩
      · exact Or.inl h1
      · exact Or.inr ⟨0, j', Or.inr ⟨rfl, hj⟩, by simpa using he⟩
    | succ i =>
      rcases H i j u (by simpa using hu) with h1 | ⟨i', j', hb, he⟩
      · rw [lt_newc] at h1
        rcases h1 with h1 | ⟨j', hj'⟩
        · exact Or.inl h1
        · rcases Nat.lt_or_eq_of_le hj' with hlt | heq
          · rcases H0 j' u hlt with h2 | ⟨j'', _, he⟩
            · exact Or.inl h2
            · exact Or.inr ⟨0, j'', Or.inl (Fin.succ_pos _), by simpa using he⟩
          · exact Or.inr ⟨0, j', Or.inl (Fin.succ_pos _), by simpa using (Fin.ext heq).symm⟩
      · right
        refine ⟨i'.succ, j', ?_, by simpa using he⟩
        rcases hb with hb | ⟨rfl, hj⟩
        · exact Or.inl (Fin.succ_lt_succ_iff.mpr hb)
        · exact Or.inr ⟨rfl, hj⟩

/-! ## The neighbor condition row by row -/

/-- For a row r with the row q above it (none for the first row): the number of the leftward,
upward and right-upward neighbors of r j that are equal to it. -/
def cnt (q : Option Row) (r : Row) (j : Fin 3) : ℕ :=
  (if ∃ j' : Fin 3, j'.val + 1 = j.val ∧ r j' = r j then 1 else 0) +
  (match q with
   | none => 0
   | some p => (if p j = r j then 1 else 0) +
      (if ∃ j' : Fin 3, j'.val = j.val + 1 ∧ p j' = r j then 1 else 0))

def rowOK (q : Option Row) (r : Row) : Prop := ∀ j, cnt q r j ≤ 2

instance (q : Option Row) (r : Row) : Decidable (rowOK q r) := by unfold rowOK; infer_instance

/-- The row above row i of x: q for the first row. -/
def prevRow {m : ℕ} (q : Option Row) (x : Fin m → Row) (i : Fin m) : Option Row :=
  match i with
  | ⟨0, _⟩ => q
  | ⟨k + 1, h⟩ => some (x ⟨k, by omega⟩)

def CondA {m : ℕ} (q : Option Row) (x : Fin m → Row) : Prop := ∀ i, rowOK (prevRow q x i) (x i)

instance {m : ℕ} (q : Option Row) : DecidablePred (@CondA m q) := fun x => by
  unfold CondA; infer_instance

theorem condA_cons {m : ℕ} (q : Option Row) (r : Row) (g : Fin m → Row) :
    CondA q (Fin.cons r g : Fin (m + 1) → Row) ↔ rowOK q r ∧ CondA (some r) g := by
  unfold CondA
  rw [Fin.forall_fin_succ]
  have hs : ∀ i : Fin m, prevRow q (Fin.cons r g : Fin (m + 1) → Row) i.succ = prevRow (some r) g i := by
    rintro ⟨i, hi⟩
    cases i with
    | zero => rfl
    | succ k => rfl
  simp only [hs, Fin.cons_zero, Fin.cons_succ]
  rfl

theorem eqNbrs_eq {m : ℕ} (x : Fin m → Row) (i : Fin m) (j : Fin 3) :
    eqNbrs x i j = cnt (prevRow none x i) (x i) j := by
  obtain ⟨i, hi⟩ := i
  cases i with
  | zero =>
    have h1 : ¬ ∃ i' : Fin m, i'.val + 1 = 0 ∧ x i' j = x ⟨0, hi⟩ j := by
      rintro ⟨i', h, _⟩; omega
    have h2 : ¬ ∃ i' : Fin m, ∃ j' : Fin 3, i'.val + 1 = 0 ∧ j'.val = j.val + 1 ∧ x i' j' = x ⟨0, hi⟩ j := by
      rintro ⟨i', j', h, _⟩; omega
    unfold eqNbrs cnt
    rw [if_neg h1, if_neg h2]
    rfl
  | succ k =>
    have h1 : (∃ i' : Fin m, i'.val + 1 = k + 1 ∧ x i' j = x ⟨k + 1, hi⟩ j) ↔
        x ⟨k, by omega⟩ j = x ⟨k + 1, hi⟩ j := by
      constructor
      · rintro ⟨i', h, he⟩
        have : i' = ⟨k, by omega⟩ := Fin.ext (by simp only; omega)
        rw [← this]; exact he
      · intro he; exact ⟨⟨k, by omega⟩, rfl, he⟩
    have h2 : (∃ i' : Fin m, ∃ j' : Fin 3, i'.val + 1 = k + 1 ∧ j'.val = j.val + 1 ∧ x i' j' = x ⟨k + 1, hi⟩ j) ↔
        ∃ j' : Fin 3, j'.val = j.val + 1 ∧ x ⟨k, by omega⟩ j' = x ⟨k + 1, hi⟩ j := by
      constructor
      · rintro ⟨i', j', h, hj, he⟩
        have : i' = ⟨k, by omega⟩ := Fin.ext (by simp only; omega)
        rw [← this]; exact ⟨j', hj, he⟩
      · rintro ⟨j', hj, he⟩; exact ⟨⟨k, by omega⟩, j', rfl, hj, he⟩
    unfold eqNbrs cnt
    simp only [h1, h2]
    rw [add_assoc]
    rfl

theorem nbr_iff {m : ℕ} (x : Fin m → Row) : NbrCond x ↔ CondA none x := by
  unfold NbrCond CondA rowOK
  simp only [eqNbrs_eq]

/-! ## The transfer -/

/-- V m q c: arrays with m rows below the row q, satisfying the neighbor condition, with values
introduced in row major order after the values below c. -/
def V (m : ℕ) (q : Option Row) (c : ℕ) : ℕ :=
  ((univ : Finset (Fin m → Row)).filter (fun g => CondA q g ∧ RGSfrom c g)).card

theorem V_zero (q : Option Row) (c : ℕ) : V 0 q c = 1 := by
  unfold V
  rw [Finset.filter_true_of_mem (fun g _ => ⟨fun i => i.elim0, RGSfrom_zero c g⟩)]
  rfl

theorem V_succ (m : ℕ) (q : Option Row) (c : ℕ) :
    V (m + 1) q c = ∑ r : Row, if rowOK q r ∧ rowRgs c r then V m (some r) (newc c r) else 0 := by
  unfold V
  rw [Finset.card_filter]
  rw [← (Fin.consEquiv fun _ => Row).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.card_filter]
  split_ifs with hr
  · refine Finset.sum_congr rfl (fun g _ => ?_)
    have e : (CondA q (Fin.cons r g : Fin (m + 1) → Row) ∧ RGSfrom c (Fin.cons r g : Fin (m + 1) → Row)) ↔
        (CondA (some r) g ∧ RGSfrom (newc c r) g) := by
      rw [condA_cons, RGSfrom_cons]; tauto
    exact if_congr e rfl rfl
  · refine Finset.sum_eq_zero (fun g _ => ?_)
    rw [if_neg]
    intro h
    have h1 := (condA_cons q r g).1 h.1
    have h2 := (RGSfrom_cons c r g).1 h.2
    exact hr ⟨h1.1, h2.1⟩

theorem a_V (n : ℕ) : a n = V n none 0 := by
  unfold a V
  congr 1
  apply Finset.filter_congr
  intro x _
  rw [nbr_iff, rmn_iff]

theorem sum_cons' {m : ℕ} (f : (Fin (m + 1) → Fin 4) → ℕ) :
    ∑ x, f x = ∑ b : Fin 4, ∑ y : Fin m → Fin 4, f (Fin.cons b y) := by
  rw [← (Fin.consEquiv fun _ => Fin 4).sum_comp, Fintype.sum_prod_type]
  rfl

theorem sum_row (f : Row → ℕ) :
    ∑ r : Row, f r = ∑ a0 : Fin 4, ∑ a1 : Fin 4, ∑ a2 : Fin 4, f ![a0, a1, a2] := by
  rw [sum_cons']
  refine Finset.sum_congr rfl (fun a0 _ => ?_)
  rw [sum_cons']
  refine Finset.sum_congr rfl (fun a1 _ => ?_)
  rw [sum_cons']
  refine Finset.sum_congr rfl (fun a2 _ => ?_)
  rw [Fintype.sum_unique]
  all_goals first | rfl | (congr 1; funext j; fin_cases j <;> rfl)

theorem row_eta (r : Row) : r = ![r 0, r 1, r 2] := by
  funext j
  fin_cases j <;> rfl

theorem V_step (m : ℕ) (T : Row → ℕ → ℕ) (hT : ∀ r c, c < 5 → V m (some r) c = T r c)
    (q : Option Row) (c : ℕ) (hc : c < 5) :
    V (m + 1) q c = ∑ r : Row, if rowOK q r ∧ rowRgs c r then T r (newc c r) else 0 := by
  rw [V_succ]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  split_ifs
  · exact hT r _ (by have := newc_le c (by omega) r; omega)
  · rfl

/-- The index of a row. -/
def idx (r : Row) : ℕ := (r 0).val * 16 + (r 1).val * 4 + (r 2).val

/-- A table lookup. -/
def look (t : List (List ℕ)) (r : Row) (c : ℕ) : ℕ := (t.getD (idx r) []).getD c 0

/-- The table of V 0. -/
def tb0 : List (List ℕ) :=
  [[1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1]]

/-- The table of V 1. -/
def tb1 : List (List ℕ) :=
  [[3, 13, 33, 60, 60], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 12, 33, 60, 60], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 32, 60, 60], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 60, 60], [3, 13, 33, 60, 60], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 12, 33, 60, 60], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 32, 60, 60], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 60, 60], [3, 13, 33, 60, 60], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 12, 33, 60, 60], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 32, 60, 60], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 60, 60], [3, 13, 33, 60, 60], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 12, 33, 60, 60], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 32, 60, 60], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 64, 64], [5, 15, 36, 60, 60]]

/-- The table of V 2. -/
def tb2 : List (List ℕ) :=
  [[133, 651, 1911, 3780, 3780], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 567, 1911, 3780, 3780], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 1792, 3780, 3780], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 3780, 3780], [133, 651, 1911, 3780, 3780], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 567, 1911, 3780, 3780], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 1792, 3780, 3780], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 3780, 3780], [133, 651, 1911, 3780, 3780], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 567, 1911, 3780, 3780], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 1792, 3780, 3780], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 3780, 3780], [133, 651, 1911, 3780, 3780], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 567, 1911, 3780, 3780], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 1792, 3780, 3780], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 4032, 4032], [182, 700, 2044, 3780, 3780]]

/-- The table of V 3. -/
def tb3 : List (List ℕ) :=
  [[7987, 39837, 119217, 238140, 238140], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 34545, 119217, 238140, 238140], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 111328, 238140, 238140], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 238140, 238140], [7987, 39837, 119217, 238140, 238140], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 34545, 119217, 238140, 238140], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 111328, 238140, 238140], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 238140, 238140], [7987, 39837, 119217, 238140, 238140], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 34545, 119217, 238140, 238140], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 111328, 238140, 238140], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 238140, 238140], [7987, 39837, 119217, 238140, 238140], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 34545, 119217, 238140, 238140], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 111328, 238140, 238140], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 254016, 254016], [10682, 42532, 127204, 238140, 238140]]

/-- The table of V 4. -/
def tb4 : List (List ℕ) :=
  [[500437, 2501499, 7502439, 15002820, 15002820], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2168103, 7502439, 15002820, 15002820], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 7002688, 15002820, 15002820], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 15002820, 15002820], [500437, 2501499, 7502439, 15002820, 15002820], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2168103, 7502439, 15002820, 15002820], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 7002688, 15002820, 15002820], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 15002820, 15002820], [500437, 2501499, 7502439, 15002820, 15002820], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2168103, 7502439, 15002820, 15002820], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 7002688, 15002820, 15002820], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 15002820, 15002820], [500437, 2501499, 7502439, 15002820, 15002820], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2168103, 7502439, 15002820, 15002820], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 7002688, 15002820, 15002820], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 16003008, 16003008], [667478, 2668540, 8002876, 15002820, 15002820]]

theorem VT0 : ∀ r : Row, ∀ c, c < 5 → V 0 (some r) c = look tb0 r c := by
  intro r c hc
  rw [V_zero, row_eta r]
  generalize r 0 = a0
  generalize r 1 = a1
  generalize r 2 = a2
  revert c
  revert a0 a1 a2
  decide +kernel

theorem VT1 : ∀ r : Row, ∀ c, c < 5 → V 1 (some r) c = look tb1 r c := by
  intro r c hc
  rw [V_step 0 (look tb0) VT0 _ c hc, sum_row, row_eta r]
  generalize r 0 = a0
  generalize r 1 = a1
  generalize r 2 = a2
  revert c
  revert a0 a1 a2
  decide +kernel

theorem VT2 : ∀ r : Row, ∀ c, c < 5 → V 2 (some r) c = look tb2 r c := by
  intro r c hc
  rw [V_step 1 (look tb1) VT1 _ c hc, sum_row, row_eta r]
  generalize r 0 = a0
  generalize r 1 = a1
  generalize r 2 = a2
  revert c
  revert a0 a1 a2
  decide +kernel

theorem VT3 : ∀ r : Row, ∀ c, c < 5 → V 3 (some r) c = look tb3 r c := by
  intro r c hc
  rw [V_step 2 (look tb2) VT2 _ c hc, sum_row, row_eta r]
  generalize r 0 = a0
  generalize r 1 = a1
  generalize r 2 = a2
  revert c
  revert a0 a1 a2
  decide +kernel

theorem VT4 : ∀ r : Row, ∀ c, c < 5 → V 4 (some r) c = look tb4 r c := by
  intro r c hc
  rw [V_step 3 (look tb3) VT3 _ c hc, sum_row, row_eta r]
  generalize r 0 = a0
  generalize r 1 = a1
  generalize r 2 = a2
  revert c
  revert a0 a1 a2
  decide +kernel

theorem V_rec (m : ℕ) : ∀ r : Row, ∀ c, c < 5 → (V (m + 4) (some r) c : ℤ) = 70 * (V (m + 3) (some r) c : ℤ) - 441 * (V (m + 2) (some r) c : ℤ) := by
  induction m with
  | zero =>
    intro r c hc
    simp only [Nat.zero_add]
    rw [VT4 r c hc, VT3 r c hc, VT2 r c hc, row_eta r]
    generalize r 0 = a0
    generalize r 1 = a1
    generalize r 2 = a2
    revert c
    revert a0 a1 a2
    decide +kernel
  | succ m ih =>
    intro r c hc
    rw [show m + 1 + 4 = m + 4 + 1 from rfl, show m + 1 + 3 = m + 3 + 1 from rfl, show m + 1 + 2 = m + 2 + 1 from rfl]
    rw [V_succ (m + 4), V_succ (m + 3), V_succ (m + 2)]
    push_cast
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun r' _ => ?_)
    split_ifs
    · exact ih r' _ (by have := newc_le c (by omega) r'; omega)
    · simp

theorem a_rec_big (n : ℕ) (hn : 5 ≤ n) : (a n : ℤ) = 70 * (a (n - 1) : ℤ) - 441 * (a (n - 2) : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  rw [show k + 5 - 1 = (k + 3) + 1 from by omega, show k + 5 - 2 = (k + 2) + 1 from by omega]
  rw [show k + 5 = (k + 4) + 1 from rfl]
  simp only [a_V]
  rw [V_succ (k + 4) none 0, V_succ (k + 3) none 0, V_succ (k + 2) none 0]
  push_cast
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  split_ifs
  · exact V_rec k r _ (by have := newc_le 0 (by omega) r; omega)
  · simp

theorem val1 : a 1 = 5 := by
  rw [a_V, V_step 0 (look tb0) VT0 none 0 (by norm_num), sum_row]
  decide +kernel

theorem val2 : a 2 = 182 := by
  rw [a_V, V_step 1 (look tb1) VT1 none 0 (by norm_num), sum_row]
  decide +kernel

theorem val3 : a 3 = 10682 := by
  rw [a_V, V_step 2 (look tb2) VT2 none 0 (by norm_num), sum_row]
  decide +kernel

theorem val4 : a 4 = 667478 := by
  rw [a_V, V_step 3 (look tb3) VT3 none 0 (by norm_num), sum_row]
  decide +kernel

theorem a_rec (n : ℕ) (hn : 4 ≤ n) : (a n : ℤ) = 70 * (a (n - 1) : ℤ) - 441 * (a (n - 2) : ℤ) := by
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n
    · rw [show (4 : ℕ) - 1 = 3 from rfl, show (4 : ℕ) - 2 = 2 from rfl]
      rw [val4, val3, val2]
      norm_num
  · exact a_rec_big n h

theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - 7 * X) * (1 - 63 * X)) =
    X * (5 - 168 * X + 147 * X ^ 2) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - 7 * X) * (1 - 63 * X)) = A - C 70 * (A * X ^ 1) + C 441 * (A * X ^ 2) := by
    simp only [map_ofNat]; ring
  have e2 : (X * (5 - 168 * X + 147 * X ^ 2) : ℚ⟦X⟧) = X ^ 1 * C 5 - X ^ 2 * C 168 + X ^ 3 * C 147 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℚ) else (a k : ℚ) := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> simp [val1, val2, val3] <;> norm_num
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 4 := ⟨n - 4, by omega⟩
    have hr := a_rec (q + 4) (by omega)
    have hr' : (a (q + 4) : ℚ) = 70 * (a (q + 3) : ℚ) - 441 * (a (q + 2) : ℚ) := by
      simp only [show q + 4 - 1 = q + 3 by omega, show q + 4 - 2 = q + 2 by omega] at hr
      exact_mod_cast hr
    simp only [show q + 4 - 1 = q + 3 by omega, show q + 4 - 2 = q + 2 by omega]
    simp only [show ¬ q + 1 = 0 by omega, show ¬ q + 2 = 0 by omega, show ¬ q + 3 = 0 by omega, show ¬ q + 4 = 0 by omega, show 1 ≤ q + 4 by omega, show 2 ≤ q + 4 by omega, show ¬ q + 4 = 0 by omega, show ¬ q + 4 = 1 by omega, show ¬ q + 4 = 2 by omega, show ¬ q + 4 = 3 by omega, if_true, if_false]
    rw [hr']
    ring

theorem closed : ∀ n : ℕ, 1 < n → (a n : ℚ) = 2 / 27 * 7 ^ (n - 1) * (27 + 4 * 9 ^ n) := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 4 with h4 | h4
    · interval_cases n
      · rw [val2]; norm_num
      · rw [val3]; norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      have hr := a_rec (k + 4) (by omega)
      have hr' : (a (k + 4) : ℚ) = 70 * a (k + 3) - 441 * a (k + 2) := by
        simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega] at hr
        exact_mod_cast hr
      rw [hr', ih (k + 3) (by omega) (by omega), ih (k + 2) (by omega) (by omega)]
      simp only [show k + 4 - 1 = k + 3 by omega, show k + 3 - 1 = k + 2 by omega, show k + 2 - 1 = k + 1 by omega]
      ring

theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - 7 * X) * (1 - 63 * X)) =
      X * (5 - 168 * X + 147 * X ^ 2) ∧
    ∀ n : ℕ, 1 < n → (a n : ℚ) = 2 / 27 * 7 ^ (n - 1) * (27 + 4 * 9 ^ n) :=
  ⟨gf, closed⟩

end OMA.S_oeis_a208403

theorem OMA.solution : type_of% @OMA.S_oeis_a208403.main :=
  OMA.S_oeis_a208403.conjecture
