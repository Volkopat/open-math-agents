import OMAStatements.S_oeis_a223773
import Mathlib

/-!
# oeis-a223773: counting the n X 4 arrays with unimodal rows and columns and nondecreasing antidiagonals

For 0..1 entries, unimodality is recognised by a three-state automaton reading the sequence:
state 0 (no 1 seen yet, `Unimodal`), state 1 (inside the block of 1s, nonincreasing) and state 2
(after the block, all 0). The lemmas `U_cons0`, `U_cons1`, `D_cons0`, `D_cons1`, `Z_cons0` and
`Z_cons1` are its transitions. An array is a list of rows; reading the rows one by one updates the
states of the 4 columns, and the antidiagonal condition links consecutive rows. The number
f(c, n, r) of valid continuations of a top row r by n rows from column states c satisfies a linear
recursion over the next row. For n >= 3 it is an explicit polynomial, checked by induction over the
109 states (c, r) whose top row is allowed, from exact values at n = 1..3. Summing gives a
polynomial for a(n), n >= 1, and the generating function and the recurrence follow from it.

Source: OEIS A223773, https://oeis.org/A223773.
-/
namespace OMA.P_oeis_a223773

open OMA.S_oeis_a223773

def adj (r s : Fin 4 → Fin 2) : Prop := ∀ j : Fin 3, r j.succ ≤ s j.castSucc

instance (r s : Fin 4 → Fin 2) : Decidable (adj r s) := by unfold adj; infer_instance

/-! ### Unimodal 0..1 sequences -/

def Z (l : List ℕ) : Prop := ∀ y ∈ l, y = 0
def D (l : List ℕ) : Prop := l.Pairwise (· ≥ ·)

lemma pw_const {l : List ℕ} {c : ℕ} (R : ℕ → ℕ → Prop) (hR : R c c) (h : ∀ y ∈ l, y = c) :
    l.Pairwise R := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons x l ih =>
    rw [List.pairwise_cons]
    refine ⟨fun y hy => ?_, ih fun y hy => h y (List.mem_cons_of_mem _ hy)⟩
    rw [h x (List.mem_cons_self), h y (List.mem_cons_of_mem _ hy)]; exact hR

lemma Z_D {l : List ℕ} (h : Z l) : D l := pw_const _ (le_refl 0) h

lemma U_nil : Unimodal [] := ⟨0, by simp, by simp⟩

lemma U_cons0 (l : List ℕ) : Unimodal (0 :: l) ↔ Unimodal l := by
  constructor
  · rintro ⟨m, h1, h2⟩
    cases m with
    | zero =>
      simp only [List.drop_zero] at h2
      exact ⟨0, by simp, by simpa only [List.drop_zero] using (List.pairwise_cons.mp h2).2⟩
    | succ m =>
      simp only [List.take_succ_cons, List.drop_succ_cons] at h1 h2
      exact ⟨m, (List.pairwise_cons.mp h1).2, h2⟩
  · rintro ⟨m, h1, h2⟩
    refine ⟨m + 1, ?_, by simpa only [List.drop_succ_cons] using h2⟩
    simp only [List.take_succ_cons]
    exact List.pairwise_cons.mpr ⟨fun y _ => Nat.zero_le y, h1⟩

lemma U_cons1 (l : List ℕ) (hl : ∀ y ∈ l, y ≤ 1) : Unimodal (1 :: l) ↔ D l := by
  constructor
  · rintro ⟨m, h1, h2⟩
    cases m with
    | zero =>
      simp only [List.drop_zero] at h2
      exact (List.pairwise_cons.mp h2).2
    | succ m =>
      simp only [List.take_succ_cons, List.drop_succ_cons] at h1 h2
      have hA : ∀ y ∈ l.take m, y = 1 := fun y hy =>
        le_antisymm (hl y (List.mem_of_mem_take hy)) ((List.pairwise_cons.mp h1).1 y hy)
      unfold D
      rw [← List.take_append_drop m l, List.pairwise_append]
      refine ⟨pw_const _ (le_refl 1) hA, h2, fun x hx y hy => ?_⟩
      rw [hA x hx]; exact hl y (List.mem_of_mem_drop hy)
  · intro h
    refine ⟨1, by simp, ?_⟩
    simp only [List.drop_succ_cons, List.drop_zero]
    exact h

lemma D_cons1 (l : List ℕ) (hl : ∀ y ∈ l, y ≤ 1) : D (1 :: l) ↔ D l := by
  unfold D; rw [List.pairwise_cons]
  exact ⟨fun h => h.2, fun h => ⟨fun y hy => hl y hy, h⟩⟩

lemma D_cons0 (l : List ℕ) : D (0 :: l) ↔ Z l := by
  unfold D; rw [List.pairwise_cons]
  exact ⟨fun h y hy => Nat.le_zero.mp (h.1 y hy), fun h => ⟨fun y hy => (h y hy).le, Z_D h⟩⟩

lemma Z_cons0 (l : List ℕ) : Z (0 :: l) ↔ Z l := by simp [Z]

lemma Z_cons1 (l : List ℕ) : ¬ Z (1 :: l) := by simp [Z]

/-- The automaton: state, transition and acceptance. -/
def St (s : Fin 3) (l : List ℕ) : Prop := if s = 0 then Unimodal l else if s = 1 then D l else Z l

def dl : Fin 3 → Fin 2 → Fin 3 := ![![0, 1], ![2, 1], ![2, 2]]

def okb : Fin 3 → Fin 2 → Bool := ![![true, true], ![true, true], ![true, false]]

lemma dl00 : dl 0 0 = 0 := rfl
lemma dl01 : dl 0 1 = 1 := rfl
lemma dl10 : dl 1 0 = 2 := rfl
lemma dl11 : dl 1 1 = 1 := rfl
lemma dl20 : dl 2 0 = 2 := rfl
lemma dl21 : dl 2 1 = 2 := rfl

def Acc : Fin 3 → List (Fin 2) → Bool
  | _, [] => true
  | s, b :: L => okb s b && Acc (dl s b) L

lemma bin (L : List (Fin 2)) : ∀ y ∈ L.map (fun x : Fin 2 => (x : ℕ)), y ≤ 1 := by
  intro y hy
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
  exact Nat.lt_succ_iff.mp x.isLt

lemma accSt (s : Fin 3) (L : List (Fin 2)) : St s (L.map (fun x : Fin 2 => (x : ℕ))) ↔ Acc s L = true := by
  induction L generalizing s with
  | nil => fin_cases s <;> simp [St, Acc, U_nil, D, Z]
  | cons b L ih =>
    rw [List.map_cons, Acc, Bool.and_eq_true, ← ih]
    have hl := bin L
    fin_cases s <;> fin_cases b <;>
      simp [St, dl, okb, U_cons0, U_cons1 _ hl, D_cons0, D_cons1 _ hl, Z_cons0, Z_cons1]

lemma uniAcc (L : List (Fin 2)) : Unimodal (L.map (fun x : Fin 2 => (x : ℕ))) ↔ Acc 0 L = true := by
  rw [← accSt]; simp [St]

/-! ### Arrays as lists of rows -/

abbrev R := Fin 4 → Fin 2

lemma sumk {M : Type*} [AddCommMonoid M] (g : R → M) : ∑ s : R, g s = ∑ y0 : Fin 2, ∑ y1 : Fin 2, ∑ y2 : Fin 2, ∑ y3 : Fin 2, g ![y0, y1, y2, y3] := by
  let e : Fin 2 × Fin 2 × Fin 2 × Fin 2 ≃ R :=
    ⟨fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2], fun f => (f 0, f 1, f 2, f 3), fun p => by simp,
      fun f => by ext i; fin_cases i <;> rfl⟩
  rw [← e.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

/-- The condition on the first row from column states `c`. -/
def okT (c : Fin 4 → Fin 3) (r : R) : Prop := Acc 0 (List.ofFn r) = true ∧ ∀ j, okb (c j) (r j) = true

instance (c : Fin 4 → Fin 3) (r : R) : Decidable (okT c r) := by unfold okT; infer_instance

open Classical

def Q (c : Fin 4 → Fin 3) (l : List R) : Prop :=
  ((∀ r ∈ l, Acc 0 (List.ofFn r) = true) ∧ ∀ j, Acc (c j) (l.map (· j)) = true) ∧ l.IsChain adj

lemma rowUni (r : R) : Unimodal (List.ofFn fun j => (r j : ℕ)) ↔ Acc 0 (List.ofFn r) = true := by
  rw [← uniAcc, List.map_ofFn]; rfl

lemma colUni (l : List R) (j : Fin 4) :
    Unimodal (l.map fun r => (r j : ℕ)) ↔ Acc 0 (l.map (· j)) = true := by
  rw [← uniAcc, List.map_map]; rfl

lemma isSol_iff (l : List R) : IsSolution l ↔ Q (fun _ => 0) l := by
  unfold IsSolution Q adj
  simp only [rowUni, colUni, and_assoc]

lemma Q_single (c : Fin 4 → Fin 3) (r : R) : Q c [r] ↔ okT c r := by
  unfold Q okT
  simp [Acc]

lemma Q_cons (c : Fin 4 → Fin 3) (r s : R) (l : List R) :
    Q c (r :: s :: l) ↔ (okT c r ∧ adj r s) ∧ Q (fun j => dl (c j) (r j)) (s :: l) := by
  unfold Q okT
  simp only [List.mem_cons, forall_eq_or_imp, List.map_cons, Acc, Bool.and_eq_true, forall_and,
    List.isChain_cons_cons]
  tauto

def LL : ℕ → Finset (List R)
  | 0 => {[]}
  | n + 1 => ((Finset.univ : Finset R) ×ˢ LL n).image (fun p => p.1 :: p.2)

lemma mem_LL (n : ℕ) (l : List R) : l ∈ LL n ↔ l.length = n := by
  induction n generalizing l with
  | zero => simp [LL]
  | succ n ih =>
    cases l with
    | nil => simp [LL]
    | cons x m => simp [LL, ih]

lemma card_cons (n : ℕ) (P : List R → Prop) [DecidablePred P] :
    ((LL (n + 1)).filter P).card = ∑ s : R, ((LL n).filter (fun m => P (s :: m))).card := by
  rw [LL, Finset.filter_image, Finset.card_image_of_injective _ (by
    intro p q h; simp only [List.cons.injEq] at h; exact Prod.ext h.1 h.2)]
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.card_filter]

noncomputable def f (c : Fin 4 → Fin 3) (n : ℕ) (r : R) : ℕ := ((LL n).filter (fun l => Q c (r :: l))).card

lemma a_succ (n : ℕ) : a (n + 1) = ∑ r : R, f (fun _ => 0) n r := by
  have e : {l : List R // l.length = n + 1 ∧ IsSolution l} ≃
      {l // l ∈ (LL (n + 1)).filter (Q fun _ => 0)} :=
    Equiv.subtypeEquivRight (fun l => by simp [mem_LL, isSol_iff])
  rw [a, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, card_cons]
  rfl

lemma f_zero (c : Fin 4 → Fin 3) (r : R) : f c 0 r = if okT c r then 1 else 0 := by
  unfold f; simp only [LL]; rw [Finset.filter_singleton]
  by_cases h : okT c r
  · rw [if_pos ((Q_single c r).mpr h), if_pos h]; rfl
  · rw [if_neg (fun h' => h ((Q_single c r).mp h')), if_neg h]; rfl

lemma f_succ (c : Fin 4 → Fin 3) (n : ℕ) (r : R) :
    f c (n + 1) r = ∑ s : R, if okT c r ∧ adj r s then f ![dl (c 0) (r 0), dl (c 1) (r 1), dl (c 2) (r 2), dl (c 3) (r 3)] n s else 0 := by
  unfold f
  rw [card_cons]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hv : (fun j => dl (c j) (r j)) = ![dl (c 0) (r 0), dl (c 1) (r 1), dl (c 2) (r 2), dl (c 3) (r 3)] := by ext j; fin_cases j <;> rfl
  simp only [Q_cons, ← hv]
  split_ifs with h
  · congr 1; ext m; simp [h]
  · simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro m _ hm; exact h hm.1

lemma f_dead (c : Fin 4 → Fin 3) (n : ℕ) (r : R) (h : ¬ okT c r) : f c n r = 0 := by
  cases n with
  | zero => rw [f_zero, if_neg h]
  | succ n => rw [f_succ]; simp [h]

lemma f_succ_v (c0 c1 c2 c3 : Fin 3) (r0 r1 r2 r3 : Fin 2) (n : ℕ) :
    (f ![c0, c1, c2, c3] (n + 1) ![r0, r1, r2, r3] : ℤ) = ∑ s : R,
      if okT ![c0, c1, c2, c3] ![r0, r1, r2, r3] ∧ adj ![r0, r1, r2, r3] s then
        (f ![dl c0 r0, dl c1 r1, dl c2 r2, dl c3 r3] n s : ℤ) else 0 := by
  rw [f_succ]; push_cast; rfl

lemma f_succ_q (c0 c1 c2 c3 : Fin 3) (r0 r1 r2 r3 : Fin 2) (n : ℕ) :
    (f ![c0, c1, c2, c3] (n + 1) ![r0, r1, r2, r3] : ℚ) = ∑ s : R,
      if okT ![c0, c1, c2, c3] ![r0, r1, r2, r3] ∧ adj ![r0, r1, r2, r3] s then
        (f ![dl c0 r0, dl c1 r1, dl c2 r2, dl c3 r3] n s : ℚ) else 0 := by
  rw [f_succ]; push_cast; rfl

lemma fv1_0 : (f ![0, 0, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 11 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_648 : (f ![0, 0, 0, 0] 1 ![0, 0, 0, 1] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_324 : (f ![0, 0, 0, 0] 1 ![0, 0, 1, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_972 : (f ![0, 0, 0, 0] 1 ![0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_162 : (f ![0, 0, 0, 0] 1 ![0, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_486 : (f ![0, 0, 0, 0] 1 ![0, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1134 : (f ![0, 0, 0, 0] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_81 : (f ![0, 0, 0, 0] 1 ![1, 0, 0, 0] : ℤ) = 11 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_243 : (f ![0, 0, 0, 0] 1 ![1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_567 : (f ![0, 0, 0, 0] 1 ![1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1215 : (f ![0, 0, 0, 0] 1 ![1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_351 : (f ![0, 0, 0, 1] 1 ![0, 0, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_999 : (f ![0, 0, 0, 1] 1 ![0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_513 : (f ![0, 0, 0, 1] 1 ![0, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1161 : (f ![0, 0, 0, 1] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_594 : (f ![0, 0, 0, 1] 1 ![1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1242 : (f ![0, 0, 0, 1] 1 ![1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_171 : (f ![0, 0, 1, 0] 1 ![0, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_495 : (f ![0, 0, 1, 0] 1 ![0, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1143 : (f ![0, 0, 1, 0] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_252 : (f ![0, 0, 1, 0] 1 ![1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_576 : (f ![0, 0, 1, 0] 1 ![1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1224 : (f ![0, 0, 1, 0] 1 ![1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_522 : (f ![0, 0, 1, 1] 1 ![0, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1170 : (f ![0, 0, 1, 1] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_603 : (f ![0, 0, 1, 1] 1 ![1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1251 : (f ![0, 0, 1, 1] 1 ![1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_225 : (f ![0, 0, 1, 2] 1 ![0, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_549 : (f ![0, 0, 1, 2] 1 ![0, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_306 : (f ![0, 0, 1, 2] 1 ![1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_630 : (f ![0, 0, 1, 2] 1 ![1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_84 : (f ![0, 1, 0, 0] 1 ![1, 0, 0, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_246 : (f ![0, 1, 0, 0] 1 ![1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_570 : (f ![0, 1, 0, 0] 1 ![1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1218 : (f ![0, 1, 0, 0] 1 ![1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_255 : (f ![0, 1, 1, 0] 1 ![1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_579 : (f ![0, 1, 1, 0] 1 ![1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1227 : (f ![0, 1, 1, 0] 1 ![1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_606 : (f ![0, 1, 1, 1] 1 ![1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1254 : (f ![0, 1, 1, 1] 1 ![1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_309 : (f ![0, 1, 1, 2] 1 ![1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_633 : (f ![0, 1, 1, 2] 1 ![1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_102 : (f ![0, 1, 2, 0] 1 ![1, 0, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_264 : (f ![0, 1, 2, 0] 1 ![1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_156 : (f ![0, 1, 2, 2] 1 ![1, 0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_318 : (f ![0, 1, 2, 2] 1 ![1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1 : (f ![1, 0, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_649 : (f ![1, 0, 0, 0] 1 ![0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_325 : (f ![1, 0, 0, 0] 1 ![0, 0, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_973 : (f ![1, 0, 0, 0] 1 ![0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_163 : (f ![1, 0, 0, 0] 1 ![0, 1, 0, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_487 : (f ![1, 0, 0, 0] 1 ![0, 1, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1135 : (f ![1, 0, 0, 0] 1 ![0, 1, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_82 : (f ![1, 0, 0, 0] 1 ![1, 0, 0, 0] : ℤ) = 11 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_244 : (f ![1, 0, 0, 0] 1 ![1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_568 : (f ![1, 0, 0, 0] 1 ![1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1216 : (f ![1, 0, 0, 0] 1 ![1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_85 : (f ![1, 1, 0, 0] 1 ![1, 0, 0, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_247 : (f ![1, 1, 0, 0] 1 ![1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_571 : (f ![1, 1, 0, 0] 1 ![1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1219 : (f ![1, 1, 0, 0] 1 ![1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_256 : (f ![1, 1, 1, 0] 1 ![1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_580 : (f ![1, 1, 1, 0] 1 ![1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1228 : (f ![1, 1, 1, 0] 1 ![1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_607 : (f ![1, 1, 1, 1] 1 ![1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1255 : (f ![1, 1, 1, 1] 1 ![1, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_310 : (f ![1, 1, 1, 2] 1 ![1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_634 : (f ![1, 1, 1, 2] 1 ![1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_103 : (f ![1, 1, 2, 0] 1 ![1, 0, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_265 : (f ![1, 1, 2, 0] 1 ![1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_157 : (f ![1, 1, 2, 2] 1 ![1, 0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_319 : (f ![1, 1, 2, 2] 1 ![1, 1, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_7 : (f ![1, 2, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_655 : (f ![1, 2, 0, 0] 1 ![0, 0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_331 : (f ![1, 2, 0, 0] 1 ![0, 0, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_979 : (f ![1, 2, 0, 0] 1 ![0, 0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_88 : (f ![1, 2, 0, 0] 1 ![1, 0, 0, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_25 : (f ![1, 2, 2, 0] 1 ![0, 0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_673 : (f ![1, 2, 2, 0] 1 ![0, 0, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_106 : (f ![1, 2, 2, 0] 1 ![1, 0, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_79 : (f ![1, 2, 2, 2] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_160 : (f ![1, 2, 2, 2] 1 ![1, 0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_2 : (f ![2, 0, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_650 : (f ![2, 0, 0, 0] 1 ![0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_326 : (f ![2, 0, 0, 0] 1 ![0, 0, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_974 : (f ![2, 0, 0, 0] 1 ![0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_164 : (f ![2, 0, 0, 0] 1 ![0, 1, 0, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_488 : (f ![2, 0, 0, 0] 1 ![0, 1, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1136 : (f ![2, 0, 0, 0] 1 ![0, 1, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_353 : (f ![2, 0, 0, 1] 1 ![0, 0, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1001 : (f ![2, 0, 0, 1] 1 ![0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_515 : (f ![2, 0, 0, 1] 1 ![0, 1, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1163 : (f ![2, 0, 0, 1] 1 ![0, 1, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_173 : (f ![2, 0, 1, 0] 1 ![0, 1, 0, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_497 : (f ![2, 0, 1, 0] 1 ![0, 1, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1145 : (f ![2, 0, 1, 0] 1 ![0, 1, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_524 : (f ![2, 0, 1, 1] 1 ![0, 1, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1172 : (f ![2, 0, 1, 1] 1 ![0, 1, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_227 : (f ![2, 0, 1, 2] 1 ![0, 1, 0, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_551 : (f ![2, 0, 1, 2] 1 ![0, 1, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_8 : (f ![2, 2, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_656 : (f ![2, 2, 0, 0] 1 ![0, 0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_332 : (f ![2, 2, 0, 0] 1 ![0, 0, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_980 : (f ![2, 2, 0, 0] 1 ![0, 0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_359 : (f ![2, 2, 0, 1] 1 ![0, 0, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1007 : (f ![2, 2, 0, 1] 1 ![0, 0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_26 : (f ![2, 2, 2, 0] 1 ![0, 0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_674 : (f ![2, 2, 2, 0] 1 ![0, 0, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_80 : (f ![2, 2, 2, 2] 1 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv2_0 : (f ![0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 56 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, fv1_0, fv1_648, fv1_324, fv1_972, fv1_162, fv1_486, fv1_1134, fv1_81, fv1_243, fv1_567, fv1_1215, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_648 : (f ![0, 0, 0, 0] 2 ![0, 0, 0, 1] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_351, fv1_999, fv1_513, fv1_1161, fv1_594, fv1_1242, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_324 : (f ![0, 0, 0, 0] 2 ![0, 0, 1, 0] : ℤ) = 14 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_171, fv1_495, fv1_1143, fv1_252, fv1_576, fv1_1224, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_972 : (f ![0, 0, 0, 0] 2 ![0, 0, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_522, fv1_1170, fv1_603, fv1_1251, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_162 : (f ![0, 0, 0, 0] 2 ![0, 1, 0, 0] : ℤ) = 14 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_84, fv1_246, fv1_570, fv1_1218, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_486 : (f ![0, 0, 0, 0] 2 ![0, 1, 1, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_255, fv1_579, fv1_1227, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1134 : (f ![0, 0, 0, 0] 2 ![0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_606, fv1_1254, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_81 : (f ![0, 0, 0, 0] 2 ![1, 0, 0, 0] : ℤ) = 36 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_1, fv1_649, fv1_325, fv1_973, fv1_163, fv1_487, fv1_1135, fv1_82, fv1_244, fv1_568, fv1_1216, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_243 : (f ![0, 0, 0, 0] 2 ![1, 1, 0, 0] : ℤ) = 14 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_85, fv1_247, fv1_571, fv1_1219, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_567 : (f ![0, 0, 0, 0] 2 ![1, 1, 1, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_256, fv1_580, fv1_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1215 : (f ![0, 0, 0, 0] 2 ![1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv1_607, fv1_1255, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_351 : (f ![0, 0, 0, 1] 2 ![0, 0, 1, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_225, fv1_549, fv1_306, fv1_630, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_999 : (f ![0, 0, 0, 1] 2 ![0, 0, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_522, fv1_1170, fv1_603, fv1_1251, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_513 : (f ![0, 0, 0, 1] 2 ![0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_309, fv1_633, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1161 : (f ![0, 0, 0, 1] 2 ![0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_606, fv1_1254, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_594 : (f ![0, 0, 0, 1] 2 ![1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, fv1_310, fv1_634, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1242 : (f ![0, 0, 0, 1] 2 ![1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_607, fv1_1255, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_171 : (f ![0, 0, 1, 0] 2 ![0, 1, 0, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_102, fv1_264, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_495 : (f ![0, 0, 1, 0] 2 ![0, 1, 1, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_255, fv1_579, fv1_1227, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1143 : (f ![0, 0, 1, 0] 2 ![0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_606, fv1_1254, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_252 : (f ![0, 0, 1, 0] 2 ![1, 1, 0, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_103, fv1_265, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_576 : (f ![0, 0, 1, 0] 2 ![1, 1, 1, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_256, fv1_580, fv1_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1224 : (f ![0, 0, 1, 0] 2 ![1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_607, fv1_1255, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_522 : (f ![0, 0, 1, 1] 2 ![0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_309, fv1_633, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1170 : (f ![0, 0, 1, 1] 2 ![0, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_606, fv1_1254, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_603 : (f ![0, 0, 1, 1] 2 ![1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, fv1_310, fv1_634, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1251 : (f ![0, 0, 1, 1] 2 ![1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_607, fv1_1255, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_225 : (f ![0, 0, 1, 2] 2 ![0, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv1_156, fv1_318, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_549 : (f ![0, 0, 1, 2] 2 ![0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_309, fv1_633, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_306 : (f ![0, 0, 1, 2] 2 ![1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, fv1_157, fv1_319, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_630 : (f ![0, 0, 1, 2] 2 ![1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, fv1_310, fv1_634, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_84 : (f ![0, 1, 0, 0] 2 ![1, 0, 0, 0] : ℤ) = 11 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_7, fv1_655, fv1_331, fv1_979, fv1_88, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_246 : (f ![0, 1, 0, 0] 2 ![1, 1, 0, 0] : ℤ) = 14 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_85, fv1_247, fv1_571, fv1_1219, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_570 : (f ![0, 1, 0, 0] 2 ![1, 1, 1, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_256, fv1_580, fv1_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1218 : (f ![0, 1, 0, 0] 2 ![1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_607, fv1_1255, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_255 : (f ![0, 1, 1, 0] 2 ![1, 1, 0, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv1_103, fv1_265, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_579 : (f ![0, 1, 1, 0] 2 ![1, 1, 1, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_256, fv1_580, fv1_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1227 : (f ![0, 1, 1, 0] 2 ![1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_607, fv1_1255, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_606 : (f ![0, 1, 1, 1] 2 ![1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, fv1_310, fv1_634, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1254 : (f ![0, 1, 1, 1] 2 ![1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_607, fv1_1255, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_309 : (f ![0, 1, 1, 2] 2 ![1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, dl20, fv1_157, fv1_319, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_633 : (f ![0, 1, 1, 2] 2 ![1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, fv1_310, fv1_634, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_102 : (f ![0, 1, 2, 0] 2 ![1, 0, 0, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv1_25, fv1_673, fv1_106, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_264 : (f ![0, 1, 2, 0] 2 ![1, 1, 0, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_103, fv1_265, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_156 : (f ![0, 1, 2, 2] 2 ![1, 0, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, fv1_79, fv1_160, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_318 : (f ![0, 1, 2, 2] 2 ![1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, fv1_157, fv1_319, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1 : (f ![1, 0, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, fv1_2, fv1_650, fv1_326, fv1_974, fv1_164, fv1_488, fv1_1136, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_649 : (f ![1, 0, 0, 0] 2 ![0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_353, fv1_1001, fv1_515, fv1_1163, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_325 : (f ![1, 0, 0, 0] 2 ![0, 0, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_173, fv1_497, fv1_1145, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_973 : (f ![1, 0, 0, 0] 2 ![0, 0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_524, fv1_1172, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_163 : (f ![1, 0, 0, 0] 2 ![0, 1, 0, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_487 : (f ![1, 0, 0, 0] 2 ![0, 1, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1135 : (f ![1, 0, 0, 0] 2 ![0, 1, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_82 : (f ![1, 0, 0, 0] 2 ![1, 0, 0, 0] : ℤ) = 36 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, fv1_1, fv1_649, fv1_325, fv1_973, fv1_163, fv1_487, fv1_1135, fv1_82, fv1_244, fv1_568, fv1_1216, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_244 : (f ![1, 0, 0, 0] 2 ![1, 1, 0, 0] : ℤ) = 14 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_85, fv1_247, fv1_571, fv1_1219, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_568 : (f ![1, 0, 0, 0] 2 ![1, 1, 1, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_256, fv1_580, fv1_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1216 : (f ![1, 0, 0, 0] 2 ![1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_607, fv1_1255, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_85 : (f ![1, 1, 0, 0] 2 ![1, 0, 0, 0] : ℤ) = 11 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl11, fv1_7, fv1_655, fv1_331, fv1_979, fv1_88, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_247 : (f ![1, 1, 0, 0] 2 ![1, 1, 0, 0] : ℤ) = 14 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, fv1_85, fv1_247, fv1_571, fv1_1219, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_571 : (f ![1, 1, 0, 0] 2 ![1, 1, 1, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_256, fv1_580, fv1_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1219 : (f ![1, 1, 0, 0] 2 ![1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_607, fv1_1255, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_256 : (f ![1, 1, 1, 0] 2 ![1, 1, 0, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl11, fv1_103, fv1_265, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_580 : (f ![1, 1, 1, 0] 2 ![1, 1, 1, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, fv1_256, fv1_580, fv1_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1228 : (f ![1, 1, 1, 0] 2 ![1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_607, fv1_1255, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_607 : (f ![1, 1, 1, 1] 2 ![1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl10, dl11, fv1_310, fv1_634, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1255 : (f ![1, 1, 1, 1] 2 ![1, 1, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl11, fv1_607, fv1_1255, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_310 : (f ![1, 1, 1, 2] 2 ![1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl10, dl11, dl20, fv1_157, fv1_319, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_634 : (f ![1, 1, 1, 2] 2 ![1, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl11, dl20, fv1_310, fv1_634, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_103 : (f ![1, 1, 2, 0] 2 ![1, 0, 0, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl11, dl20, fv1_25, fv1_673, fv1_106, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_265 : (f ![1, 1, 2, 0] 2 ![1, 1, 0, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, dl20, fv1_103, fv1_265, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_157 : (f ![1, 1, 2, 2] 2 ![1, 0, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl10, dl11, dl20, fv1_79, fv1_160, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_319 : (f ![1, 1, 2, 2] 2 ![1, 1, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl11, dl20, fv1_157, fv1_319, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_7 : (f ![1, 2, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv1_8, fv1_656, fv1_332, fv1_980, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_655 : (f ![1, 2, 0, 0] 2 ![0, 0, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv1_359, fv1_1007, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_331 : (f ![1, 2, 0, 0] 2 ![0, 0, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_979 : (f ![1, 2, 0, 0] 2 ![0, 0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_88 : (f ![1, 2, 0, 0] 2 ![1, 0, 0, 0] : ℤ) = 11 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, dl20, fv1_7, fv1_655, fv1_331, fv1_979, fv1_88, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_25 : (f ![1, 2, 2, 0] 2 ![0, 0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv1_26, fv1_674, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_673 : (f ![1, 2, 2, 0] 2 ![0, 0, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_106 : (f ![1, 2, 2, 0] 2 ![1, 0, 0, 0] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, dl20, fv1_25, fv1_673, fv1_106, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_79 : (f ![1, 2, 2, 2] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl10, dl20, fv1_80, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_160 : (f ![1, 2, 2, 2] 2 ![1, 0, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl11, dl20, fv1_79, fv1_160, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_2 : (f ![2, 0, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv1_2, fv1_650, fv1_326, fv1_974, fv1_164, fv1_488, fv1_1136, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_650 : (f ![2, 0, 0, 0] 2 ![0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, fv1_353, fv1_1001, fv1_515, fv1_1163, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_326 : (f ![2, 0, 0, 0] 2 ![0, 0, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, fv1_173, fv1_497, fv1_1145, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_974 : (f ![2, 0, 0, 0] 2 ![0, 0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, fv1_524, fv1_1172, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_164 : (f ![2, 0, 0, 0] 2 ![0, 1, 0, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_488 : (f ![2, 0, 0, 0] 2 ![0, 1, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1136 : (f ![2, 0, 0, 0] 2 ![0, 1, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_353 : (f ![2, 0, 0, 1] 2 ![0, 0, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv1_227, fv1_551, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1001 : (f ![2, 0, 0, 1] 2 ![0, 0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv1_524, fv1_1172, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_515 : (f ![2, 0, 0, 1] 2 ![0, 1, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1163 : (f ![2, 0, 0, 1] 2 ![0, 1, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_173 : (f ![2, 0, 1, 0] 2 ![0, 1, 0, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_497 : (f ![2, 0, 1, 0] 2 ![0, 1, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1145 : (f ![2, 0, 1, 0] 2 ![0, 1, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_524 : (f ![2, 0, 1, 1] 2 ![0, 1, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1172 : (f ![2, 0, 1, 1] 2 ![0, 1, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_227 : (f ![2, 0, 1, 2] 2 ![0, 1, 0, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_551 : (f ![2, 0, 1, 2] 2 ![0, 1, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_8 : (f ![2, 2, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv1_8, fv1_656, fv1_332, fv1_980, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_656 : (f ![2, 2, 0, 0] 2 ![0, 0, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, fv1_359, fv1_1007, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_332 : (f ![2, 2, 0, 0] 2 ![0, 0, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_980 : (f ![2, 2, 0, 0] 2 ![0, 0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_359 : (f ![2, 2, 0, 1] 2 ![0, 0, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1007 : (f ![2, 2, 0, 1] 2 ![0, 0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_26 : (f ![2, 2, 2, 0] 2 ![0, 0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv1_26, fv1_674, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_674 : (f ![2, 2, 2, 0] 2 ![0, 0, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_80 : (f ![2, 2, 2, 2] 2 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl20, fv1_80, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_0 : (f ![0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℤ) = 180 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, fv2_0, fv2_648, fv2_324, fv2_972, fv2_162, fv2_486, fv2_1134, fv2_81, fv2_243, fv2_567, fv2_1215, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_648 : (f ![0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℤ) = 32 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_351, fv2_999, fv2_513, fv2_1161, fv2_594, fv2_1242, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_324 : (f ![0, 0, 0, 0] 3 ![0, 0, 1, 0] : ℤ) = 32 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_171, fv2_495, fv2_1143, fv2_252, fv2_576, fv2_1224, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_972 : (f ![0, 0, 0, 0] 3 ![0, 0, 1, 1] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_522, fv2_1170, fv2_603, fv2_1251, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_162 : (f ![0, 0, 0, 0] 3 ![0, 1, 0, 0] : ℤ) = 36 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_84, fv2_246, fv2_570, fv2_1218, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_486 : (f ![0, 0, 0, 0] 3 ![0, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_255, fv2_579, fv2_1227, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1134 : (f ![0, 0, 0, 0] 3 ![0, 1, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_606, fv2_1254, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_81 : (f ![0, 0, 0, 0] 3 ![1, 0, 0, 0] : ℤ) = 81 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_1, fv2_649, fv2_325, fv2_973, fv2_163, fv2_487, fv2_1135, fv2_82, fv2_244, fv2_568, fv2_1216, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_243 : (f ![0, 0, 0, 0] 3 ![1, 1, 0, 0] : ℤ) = 36 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_85, fv2_247, fv2_571, fv2_1219, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_567 : (f ![0, 0, 0, 0] 3 ![1, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv2_256, fv2_580, fv2_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1215 : (f ![0, 0, 0, 0] 3 ![1, 1, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv2_607, fv2_1255, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_351 : (f ![0, 0, 0, 1] 3 ![0, 0, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv2_225, fv2_549, fv2_306, fv2_630, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_999 : (f ![0, 0, 0, 1] 3 ![0, 0, 1, 1] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_522, fv2_1170, fv2_603, fv2_1251, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_513 : (f ![0, 0, 0, 1] 3 ![0, 1, 1, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv2_309, fv2_633, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1161 : (f ![0, 0, 0, 1] 3 ![0, 1, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_606, fv2_1254, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_594 : (f ![0, 0, 0, 1] 3 ![1, 1, 1, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, fv2_310, fv2_634, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1242 : (f ![0, 0, 0, 1] 3 ![1, 1, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_607, fv2_1255, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_171 : (f ![0, 0, 1, 0] 3 ![0, 1, 0, 0] : ℤ) = 10 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv2_102, fv2_264, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_495 : (f ![0, 0, 1, 0] 3 ![0, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_255, fv2_579, fv2_1227, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1143 : (f ![0, 0, 1, 0] 3 ![0, 1, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_606, fv2_1254, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_252 : (f ![0, 0, 1, 0] 3 ![1, 1, 0, 0] : ℤ) = 10 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv2_103, fv2_265, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_576 : (f ![0, 0, 1, 0] 3 ![1, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_256, fv2_580, fv2_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1224 : (f ![0, 0, 1, 0] 3 ![1, 1, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_607, fv2_1255, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_522 : (f ![0, 0, 1, 1] 3 ![0, 1, 1, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_309, fv2_633, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1170 : (f ![0, 0, 1, 1] 3 ![0, 1, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_606, fv2_1254, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_603 : (f ![0, 0, 1, 1] 3 ![1, 1, 1, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, fv2_310, fv2_634, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1251 : (f ![0, 0, 1, 1] 3 ![1, 1, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_607, fv2_1255, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_225 : (f ![0, 0, 1, 2] 3 ![0, 1, 0, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv2_156, fv2_318, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_549 : (f ![0, 0, 1, 2] 3 ![0, 1, 1, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_309, fv2_633, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_306 : (f ![0, 0, 1, 2] 3 ![1, 1, 0, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, fv2_157, fv2_319, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_630 : (f ![0, 0, 1, 2] 3 ![1, 1, 1, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, fv2_310, fv2_634, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_84 : (f ![0, 1, 0, 0] 3 ![1, 0, 0, 0] : ℤ) = 17 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv2_7, fv2_655, fv2_331, fv2_979, fv2_88, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_246 : (f ![0, 1, 0, 0] 3 ![1, 1, 0, 0] : ℤ) = 36 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_85, fv2_247, fv2_571, fv2_1219, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_570 : (f ![0, 1, 0, 0] 3 ![1, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_256, fv2_580, fv2_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1218 : (f ![0, 1, 0, 0] 3 ![1, 1, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_607, fv2_1255, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_255 : (f ![0, 1, 1, 0] 3 ![1, 1, 0, 0] : ℤ) = 10 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl11, fv2_103, fv2_265, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_579 : (f ![0, 1, 1, 0] 3 ![1, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_256, fv2_580, fv2_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1227 : (f ![0, 1, 1, 0] 3 ![1, 1, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_607, fv2_1255, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_606 : (f ![0, 1, 1, 1] 3 ![1, 1, 1, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, fv2_310, fv2_634, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1254 : (f ![0, 1, 1, 1] 3 ![1, 1, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_607, fv2_1255, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_309 : (f ![0, 1, 1, 2] 3 ![1, 1, 0, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, dl20, fv2_157, fv2_319, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_633 : (f ![0, 1, 1, 2] 3 ![1, 1, 1, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, fv2_310, fv2_634, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_102 : (f ![0, 1, 2, 0] 3 ![1, 0, 0, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv2_25, fv2_673, fv2_106, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_264 : (f ![0, 1, 2, 0] 3 ![1, 1, 0, 0] : ℤ) = 10 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_103, fv2_265, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_156 : (f ![0, 1, 2, 2] 3 ![1, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, fv2_79, fv2_160, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_318 : (f ![0, 1, 2, 2] 3 ![1, 1, 0, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, fv2_157, fv2_319, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1 : (f ![1, 0, 0, 0] 3 ![0, 0, 0, 0] : ℤ) = 20 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, fv2_2, fv2_650, fv2_326, fv2_974, fv2_164, fv2_488, fv2_1136, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_649 : (f ![1, 0, 0, 0] 3 ![0, 0, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv2_353, fv2_1001, fv2_515, fv2_1163, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_325 : (f ![1, 0, 0, 0] 3 ![0, 0, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv2_173, fv2_497, fv2_1145, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_973 : (f ![1, 0, 0, 0] 3 ![0, 0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv2_524, fv2_1172, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_163 : (f ![1, 0, 0, 0] 3 ![0, 1, 0, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_487 : (f ![1, 0, 0, 0] 3 ![0, 1, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1135 : (f ![1, 0, 0, 0] 3 ![0, 1, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_82 : (f ![1, 0, 0, 0] 3 ![1, 0, 0, 0] : ℤ) = 81 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, fv2_1, fv2_649, fv2_325, fv2_973, fv2_163, fv2_487, fv2_1135, fv2_82, fv2_244, fv2_568, fv2_1216, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_244 : (f ![1, 0, 0, 0] 3 ![1, 1, 0, 0] : ℤ) = 36 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_85, fv2_247, fv2_571, fv2_1219, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_568 : (f ![1, 0, 0, 0] 3 ![1, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_256, fv2_580, fv2_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1216 : (f ![1, 0, 0, 0] 3 ![1, 1, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_607, fv2_1255, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_85 : (f ![1, 1, 0, 0] 3 ![1, 0, 0, 0] : ℤ) = 17 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl11, fv2_7, fv2_655, fv2_331, fv2_979, fv2_88, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_247 : (f ![1, 1, 0, 0] 3 ![1, 1, 0, 0] : ℤ) = 36 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, fv2_85, fv2_247, fv2_571, fv2_1219, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_571 : (f ![1, 1, 0, 0] 3 ![1, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv2_256, fv2_580, fv2_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1219 : (f ![1, 1, 0, 0] 3 ![1, 1, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_607, fv2_1255, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_256 : (f ![1, 1, 1, 0] 3 ![1, 1, 0, 0] : ℤ) = 10 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl11, fv2_103, fv2_265, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_580 : (f ![1, 1, 1, 0] 3 ![1, 1, 1, 0] : ℤ) = 16 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, fv2_256, fv2_580, fv2_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1228 : (f ![1, 1, 1, 0] 3 ![1, 1, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv2_607, fv2_1255, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_607 : (f ![1, 1, 1, 1] 3 ![1, 1, 1, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl10, dl11, fv2_310, fv2_634, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1255 : (f ![1, 1, 1, 1] 3 ![1, 1, 1, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl11, fv2_607, fv2_1255, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_310 : (f ![1, 1, 1, 2] 3 ![1, 1, 0, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl10, dl11, dl20, fv2_157, fv2_319, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_634 : (f ![1, 1, 1, 2] 3 ![1, 1, 1, 0] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl11, dl20, fv2_310, fv2_634, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_103 : (f ![1, 1, 2, 0] 3 ![1, 0, 0, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl11, dl20, fv2_25, fv2_673, fv2_106, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_265 : (f ![1, 1, 2, 0] 3 ![1, 1, 0, 0] : ℤ) = 10 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, dl20, fv2_103, fv2_265, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_157 : (f ![1, 1, 2, 2] 3 ![1, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl10, dl11, dl20, fv2_79, fv2_160, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_319 : (f ![1, 1, 2, 2] 3 ![1, 1, 0, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl11, dl20, fv2_157, fv2_319, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_7 : (f ![1, 2, 0, 0] 3 ![0, 0, 0, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv2_8, fv2_656, fv2_332, fv2_980, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_655 : (f ![1, 2, 0, 0] 3 ![0, 0, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv2_359, fv2_1007, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_331 : (f ![1, 2, 0, 0] 3 ![0, 0, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_979 : (f ![1, 2, 0, 0] 3 ![0, 0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_88 : (f ![1, 2, 0, 0] 3 ![1, 0, 0, 0] : ℤ) = 17 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, dl20, fv2_7, fv2_655, fv2_331, fv2_979, fv2_88, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_25 : (f ![1, 2, 2, 0] 3 ![0, 0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl10, dl20, fv2_26, fv2_674, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_673 : (f ![1, 2, 2, 0] 3 ![0, 0, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_106 : (f ![1, 2, 2, 0] 3 ![1, 0, 0, 0] : ℤ) = 7 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl11, dl20, fv2_25, fv2_673, fv2_106, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_79 : (f ![1, 2, 2, 2] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl10, dl20, fv2_80, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_160 : (f ![1, 2, 2, 2] 3 ![1, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl11, dl20, fv2_79, fv2_160, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_2 : (f ![2, 0, 0, 0] 3 ![0, 0, 0, 0] : ℤ) = 20 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv2_2, fv2_650, fv2_326, fv2_974, fv2_164, fv2_488, fv2_1136, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_650 : (f ![2, 0, 0, 0] 3 ![0, 0, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, fv2_353, fv2_1001, fv2_515, fv2_1163, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_326 : (f ![2, 0, 0, 0] 3 ![0, 0, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, fv2_173, fv2_497, fv2_1145, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_974 : (f ![2, 0, 0, 0] 3 ![0, 0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, fv2_524, fv2_1172, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_164 : (f ![2, 0, 0, 0] 3 ![0, 1, 0, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_488 : (f ![2, 0, 0, 0] 3 ![0, 1, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1136 : (f ![2, 0, 0, 0] 3 ![0, 1, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_353 : (f ![2, 0, 0, 1] 3 ![0, 0, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, fv2_227, fv2_551, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1001 : (f ![2, 0, 0, 1] 3 ![0, 0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, fv2_524, fv2_1172, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_515 : (f ![2, 0, 0, 1] 3 ![0, 1, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1163 : (f ![2, 0, 0, 1] 3 ![0, 1, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_173 : (f ![2, 0, 1, 0] 3 ![0, 1, 0, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_497 : (f ![2, 0, 1, 0] 3 ![0, 1, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1145 : (f ![2, 0, 1, 0] 3 ![0, 1, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_524 : (f ![2, 0, 1, 1] 3 ![0, 1, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1172 : (f ![2, 0, 1, 1] 3 ![0, 1, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_227 : (f ![2, 0, 1, 2] 3 ![0, 1, 0, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_551 : (f ![2, 0, 1, 2] 3 ![0, 1, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_8 : (f ![2, 2, 0, 0] 3 ![0, 0, 0, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv2_8, fv2_656, fv2_332, fv2_980, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_656 : (f ![2, 2, 0, 0] 3 ![0, 0, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, fv2_359, fv2_1007, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_332 : (f ![2, 2, 0, 0] 3 ![0, 0, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_980 : (f ![2, 2, 0, 0] 3 ![0, 0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_359 : (f ![2, 2, 0, 1] 3 ![0, 0, 1, 0] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_1007 : (f ![2, 2, 0, 1] 3 ![0, 0, 1, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_26 : (f ![2, 2, 2, 0] 3 ![0, 0, 0, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl20, fv2_26, fv2_674, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_674 : (f ![2, 2, 2, 0] 3 ![0, 0, 0, 1] : ℤ) = 0 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl20, f_dead]
  simp +decide only []
  try norm_num

lemma fv3_80 : (f ![2, 2, 2, 2] 3 ![0, 0, 0, 0] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl20, fv2_80, f_dead]
  simp +decide only []
  try norm_num

set_option maxRecDepth 100000 in
def cs : Fin 109 → Fin 4 → Fin 3 := ![![0, 0, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0], ![1, 2, 0, 0], ![2, 2, 0, 0], ![1, 2, 2, 0], ![2, 2, 2, 0], ![1, 2, 2, 2], ![2, 2, 2, 2], ![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0], ![1, 2, 0, 0], ![0, 1, 2, 0], ![1, 1, 2, 0], ![1, 2, 2, 0], ![0, 1, 2, 2], ![1, 1, 2, 2], ![1, 2, 2, 2], ![0, 0, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 1, 0], ![2, 0, 1, 0], ![0, 0, 1, 2], ![2, 0, 1, 2], ![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0], ![0, 0, 1, 0], ![0, 1, 1, 0], ![1, 1, 1, 0], ![0, 1, 2, 0], ![1, 1, 2, 0], ![0, 0, 1, 2], ![0, 1, 1, 2], ![1, 1, 1, 2], ![0, 1, 2, 2], ![1, 1, 2, 2], ![0, 0, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0], ![1, 2, 0, 0], ![2, 2, 0, 0], ![0, 0, 0, 1], ![2, 0, 0, 1], ![2, 2, 0, 1], ![0, 0, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 1, 0], ![2, 0, 1, 0], ![0, 0, 0, 1], ![2, 0, 0, 1], ![0, 0, 1, 1], ![2, 0, 1, 1], ![0, 0, 1, 2], ![2, 0, 1, 2], ![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0], ![0, 0, 1, 0], ![0, 1, 1, 0], ![1, 1, 1, 0], ![0, 0, 0, 1], ![0, 0, 1, 1], ![0, 1, 1, 1], ![1, 1, 1, 1], ![0, 0, 1, 2], ![0, 1, 1, 2], ![1, 1, 1, 2], ![0, 0, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0], ![1, 2, 0, 0], ![2, 2, 0, 0], ![1, 2, 2, 0], ![2, 2, 2, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0], ![1, 2, 0, 0], ![2, 2, 0, 0], ![0, 0, 0, 1], ![2, 0, 0, 1], ![2, 2, 0, 1], ![0, 0, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0], ![0, 0, 1, 0], ![2, 0, 1, 0], ![0, 0, 0, 1], ![2, 0, 0, 1], ![0, 0, 1, 1], ![2, 0, 1, 1], ![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0], ![0, 0, 1, 0], ![0, 1, 1, 0], ![1, 1, 1, 0], ![0, 0, 0, 1], ![0, 0, 1, 1], ![0, 1, 1, 1], ![1, 1, 1, 1]]

set_option maxRecDepth 100000 in
def rs : Fin 109 → R := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 1, 0], ![0, 0, 1, 0], ![0, 0, 1, 0], ![0, 0, 1, 0], ![0, 0, 1, 0], ![0, 0, 1, 0], ![0, 0, 1, 0], ![0, 1, 1, 0], ![0, 1, 1, 0], ![0, 1, 1, 0], ![0, 1, 1, 0], ![0, 1, 1, 0], ![0, 1, 1, 0], ![0, 1, 1, 0], ![0, 1, 1, 0], ![0, 1, 1, 0], ![0, 1, 1, 0], ![0, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 0], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1]]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
def PP : Fin 109 → ℕ → ℚ := ![fun n => ((1 : ℚ) / 40320) * (n : ℚ) ^ 8 + ((1 : ℚ) / 1120) * (n : ℚ) ^ 7 + ((11 : ℚ) / 576) * (n : ℚ) ^ 6 + ((13 : ℚ) / 48) * (n : ℚ) ^ 5 + ((15047 : ℚ) / 5760) * (n : ℚ) ^ 4 + ((8021 : ℚ) / 480) * (n : ℚ) ^ 3 + ((152951 : ℚ) / 2016) * (n : ℚ) ^ 2 + ((10389 : ℚ) / 56) * (n : ℚ) ^ 1 + (180 : ℚ) * (n : ℚ) ^ 0, fun n => (20 : ℚ) * (n : ℚ) ^ 0, fun n => (20 : ℚ) * (n : ℚ) ^ 0, fun n => (6 : ℚ) * (n : ℚ) ^ 0, fun n => (6 : ℚ) * (n : ℚ) ^ 0, fun n => (2 : ℚ) * (n : ℚ) ^ 0, fun n => (2 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 5040) * (n : ℚ) ^ 7 + ((1 : ℚ) / 240) * (n : ℚ) ^ 6 + ((43 : ℚ) / 720) * (n : ℚ) ^ 5 + ((25 : ℚ) / 48) * (n : ℚ) ^ 4 + ((1421 : ℚ) / 360) * (n : ℚ) ^ 3 + ((679 : ℚ) / 40) * (n : ℚ) ^ 2 + ((8189 : ℚ) / 140) * (n : ℚ) ^ 1 + (81 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 5040) * (n : ℚ) ^ 7 + ((1 : ℚ) / 240) * (n : ℚ) ^ 6 + ((43 : ℚ) / 720) * (n : ℚ) ^ 5 + ((25 : ℚ) / 48) * (n : ℚ) ^ 4 + ((1421 : ℚ) / 360) * (n : ℚ) ^ 3 + ((679 : ℚ) / 40) * (n : ℚ) ^ 2 + ((8189 : ℚ) / 140) * (n : ℚ) ^ 1 + (81 : ℚ) * (n : ℚ) ^ 0, fun n => (6 : ℚ) * (n : ℚ) ^ 1 + (17 : ℚ) * (n : ℚ) ^ 0, fun n => (6 : ℚ) * (n : ℚ) ^ 1 + (17 : ℚ) * (n : ℚ) ^ 0, fun n => (6 : ℚ) * (n : ℚ) ^ 1 + (17 : ℚ) * (n : ℚ) ^ 0, fun n => (2 : ℚ) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => (2 : ℚ) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => (2 : ℚ) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 720) * (n : ℚ) ^ 6 + ((1 : ℚ) / 48) * (n : ℚ) ^ 5 + ((35 : ℚ) / 144) * (n : ℚ) ^ 4 + ((25 : ℚ) / 16) * (n : ℚ) ^ 3 + ((833 : ℚ) / 90) * (n : ℚ) ^ 2 + ((359 : ℚ) / 12) * (n : ℚ) ^ 1 + (36 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => ((1 : ℚ) / 720) * (n : ℚ) ^ 6 + ((1 : ℚ) / 48) * (n : ℚ) ^ 5 + ((35 : ℚ) / 144) * (n : ℚ) ^ 4 + ((25 : ℚ) / 16) * (n : ℚ) ^ 3 + ((833 : ℚ) / 90) * (n : ℚ) ^ 2 + ((359 : ℚ) / 12) * (n : ℚ) ^ 1 + (36 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 720) * (n : ℚ) ^ 6 + ((1 : ℚ) / 48) * (n : ℚ) ^ 5 + ((35 : ℚ) / 144) * (n : ℚ) ^ 4 + ((25 : ℚ) / 16) * (n : ℚ) ^ 3 + ((833 : ℚ) / 90) * (n : ℚ) ^ 2 + ((359 : ℚ) / 12) * (n : ℚ) ^ 1 + (36 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 720) * (n : ℚ) ^ 6 + ((1 : ℚ) / 48) * (n : ℚ) ^ 5 + ((35 : ℚ) / 144) * (n : ℚ) ^ 4 + ((25 : ℚ) / 16) * (n : ℚ) ^ 3 + ((833 : ℚ) / 90) * (n : ℚ) ^ 2 + ((359 : ℚ) / 12) * (n : ℚ) ^ 1 + (36 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 720) * (n : ℚ) ^ 6 + ((1 : ℚ) / 48) * (n : ℚ) ^ 5 + ((35 : ℚ) / 144) * (n : ℚ) ^ 4 + ((25 : ℚ) / 16) * (n : ℚ) ^ 3 + ((833 : ℚ) / 90) * (n : ℚ) ^ 2 + ((359 : ℚ) / 12) * (n : ℚ) ^ 1 + (36 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 60) * (n : ℚ) ^ 5 + ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((19 : ℚ) / 12) * (n : ℚ) ^ 3 + ((53 : ℚ) / 6) * (n : ℚ) ^ 2 + ((127 : ℚ) / 5) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => 0, fun n => 0, fun n => 0, fun n => ((1 : ℚ) / 3) * (n : ℚ) ^ 3 + (3 : ℚ) * (n : ℚ) ^ 2 + ((32 : ℚ) / 3) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => 0, fun n => ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((19 : ℚ) / 24) * (n : ℚ) ^ 3 + ((53 : ℚ) / 12) * (n : ℚ) ^ 2 + ((127 : ℚ) / 10) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => 0, fun n => ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((19 : ℚ) / 24) * (n : ℚ) ^ 3 + ((53 : ℚ) / 12) * (n : ℚ) ^ 2 + ((127 : ℚ) / 10) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((19 : ℚ) / 24) * (n : ℚ) ^ 3 + ((53 : ℚ) / 12) * (n : ℚ) ^ 2 + ((127 : ℚ) / 10) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((19 : ℚ) / 24) * (n : ℚ) ^ 3 + ((53 : ℚ) / 12) * (n : ℚ) ^ 2 + ((127 : ℚ) / 10) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((19 : ℚ) / 24) * (n : ℚ) ^ 3 + ((53 : ℚ) / 12) * (n : ℚ) ^ 2 + ((127 : ℚ) / 10) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((19 : ℚ) / 24) * (n : ℚ) ^ 3 + ((53 : ℚ) / 12) * (n : ℚ) ^ 2 + ((127 : ℚ) / 10) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((19 : ℚ) / 24) * (n : ℚ) ^ 3 + ((53 : ℚ) / 12) * (n : ℚ) ^ 2 + ((127 : ℚ) / 10) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((19 : ℚ) / 24) * (n : ℚ) ^ 3 + ((53 : ℚ) / 12) * (n : ℚ) ^ 2 + ((127 : ℚ) / 10) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((19 : ℚ) / 24) * (n : ℚ) ^ 3 + ((53 : ℚ) / 12) * (n : ℚ) ^ 2 + ((127 : ℚ) / 10) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((5 : ℚ) / 3) * (n : ℚ) ^ 3 + ((47 : ℚ) / 6) * (n : ℚ) ^ 2 + ((67 : ℚ) / 3) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => 0, fun n => 0, fun n => 0, fun n => 0, fun n => 0, fun n => ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((5 : ℚ) / 6) * (n : ℚ) ^ 3 + ((47 : ℚ) / 12) * (n : ℚ) ^ 2 + ((67 : ℚ) / 6) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => 0, fun n => 0, fun n => 0, fun n => ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((5 : ℚ) / 6) * (n : ℚ) ^ 3 + ((47 : ℚ) / 12) * (n : ℚ) ^ 2 + ((67 : ℚ) / 6) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0]

set_option maxRecDepth 100000 in
lemma pp_0 (n : ℕ) : PP 0 n = ((1 : ℚ) / 40320) * (n : ℚ) ^ 8 + ((1 : ℚ) / 1120) * (n : ℚ) ^ 7 + ((11 : ℚ) / 576) * (n : ℚ) ^ 6 + ((13 : ℚ) / 48) * (n : ℚ) ^ 5 + ((15047 : ℚ) / 5760) * (n : ℚ) ^ 4 + ((8021 : ℚ) / 480) * (n : ℚ) ^ 3 + ((152951 : ℚ) / 2016) * (n : ℚ) ^ 2 + ((10389 : ℚ) / 56) * (n : ℚ) ^ 1 + (180 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_1 (n : ℕ) : PP 1 n = (20 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_2 (n : ℕ) : PP 2 n = (20 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_3 (n : ℕ) : PP 3 n = (6 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_4 (n : ℕ) : PP 4 n = (6 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_5 (n : ℕ) : PP 5 n = (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_6 (n : ℕ) : PP 6 n = (2 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_7 (n : ℕ) : PP 7 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_8 (n : ℕ) : PP 8 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_9 (n : ℕ) : PP 9 n = ((1 : ℚ) / 5040) * (n : ℚ) ^ 7 + ((1 : ℚ) / 240) * (n : ℚ) ^ 6 + ((43 : ℚ) / 720) * (n : ℚ) ^ 5 + ((25 : ℚ) / 48) * (n : ℚ) ^ 4 + ((1421 : ℚ) / 360) * (n : ℚ) ^ 3 + ((679 : ℚ) / 40) * (n : ℚ) ^ 2 + ((8189 : ℚ) / 140) * (n : ℚ) ^ 1 + (81 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_10 (n : ℕ) : PP 10 n = ((1 : ℚ) / 5040) * (n : ℚ) ^ 7 + ((1 : ℚ) / 240) * (n : ℚ) ^ 6 + ((43 : ℚ) / 720) * (n : ℚ) ^ 5 + ((25 : ℚ) / 48) * (n : ℚ) ^ 4 + ((1421 : ℚ) / 360) * (n : ℚ) ^ 3 + ((679 : ℚ) / 40) * (n : ℚ) ^ 2 + ((8189 : ℚ) / 140) * (n : ℚ) ^ 1 + (81 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_11 (n : ℕ) : PP 11 n = (6 : ℚ) * (n : ℚ) ^ 1 + (17 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_12 (n : ℕ) : PP 12 n = (6 : ℚ) * (n : ℚ) ^ 1 + (17 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_13 (n : ℕ) : PP 13 n = (6 : ℚ) * (n : ℚ) ^ 1 + (17 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_14 (n : ℕ) : PP 14 n = (2 : ℚ) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_15 (n : ℕ) : PP 15 n = (2 : ℚ) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_16 (n : ℕ) : PP 16 n = (2 : ℚ) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_17 (n : ℕ) : PP 17 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_18 (n : ℕ) : PP 18 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_19 (n : ℕ) : PP 19 n = (1 : ℚ) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_20 (n : ℕ) : PP 20 n = ((1 : ℚ) / 720) * (n : ℚ) ^ 6 + ((1 : ℚ) / 48) * (n : ℚ) ^ 5 + ((35 : ℚ) / 144) * (n : ℚ) ^ 4 + ((25 : ℚ) / 16) * (n : ℚ) ^ 3 + ((833 : ℚ) / 90) * (n : ℚ) ^ 2 + ((359 : ℚ) / 12) * (n : ℚ) ^ 1 + (36 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_21 (n : ℕ) : PP 21 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_22 (n : ℕ) : PP 22 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_23 (n : ℕ) : PP 23 n = (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_24 (n : ℕ) : PP 24 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_25 (n : ℕ) : PP 25 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_26 (n : ℕ) : PP 26 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_27 (n : ℕ) : PP 27 n = ((1 : ℚ) / 720) * (n : ℚ) ^ 6 + ((1 : ℚ) / 48) * (n : ℚ) ^ 5 + ((35 : ℚ) / 144) * (n : ℚ) ^ 4 + ((25 : ℚ) / 16) * (n : ℚ) ^ 3 + ((833 : ℚ) / 90) * (n : ℚ) ^ 2 + ((359 : ℚ) / 12) * (n : ℚ) ^ 1 + (36 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_28 (n : ℕ) : PP 28 n = ((1 : ℚ) / 720) * (n : ℚ) ^ 6 + ((1 : ℚ) / 48) * (n : ℚ) ^ 5 + ((35 : ℚ) / 144) * (n : ℚ) ^ 4 + ((25 : ℚ) / 16) * (n : ℚ) ^ 3 + ((833 : ℚ) / 90) * (n : ℚ) ^ 2 + ((359 : ℚ) / 12) * (n : ℚ) ^ 1 + (36 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_29 (n : ℕ) : PP 29 n = ((1 : ℚ) / 720) * (n : ℚ) ^ 6 + ((1 : ℚ) / 48) * (n : ℚ) ^ 5 + ((35 : ℚ) / 144) * (n : ℚ) ^ 4 + ((25 : ℚ) / 16) * (n : ℚ) ^ 3 + ((833 : ℚ) / 90) * (n : ℚ) ^ 2 + ((359 : ℚ) / 12) * (n : ℚ) ^ 1 + (36 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_30 (n : ℕ) : PP 30 n = ((1 : ℚ) / 720) * (n : ℚ) ^ 6 + ((1 : ℚ) / 48) * (n : ℚ) ^ 5 + ((35 : ℚ) / 144) * (n : ℚ) ^ 4 + ((25 : ℚ) / 16) * (n : ℚ) ^ 3 + ((833 : ℚ) / 90) * (n : ℚ) ^ 2 + ((359 : ℚ) / 12) * (n : ℚ) ^ 1 + (36 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_31 (n : ℕ) : PP 31 n = (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_32 (n : ℕ) : PP 32 n = (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_33 (n : ℕ) : PP 33 n = (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_34 (n : ℕ) : PP 34 n = (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_35 (n : ℕ) : PP 35 n = (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_36 (n : ℕ) : PP 36 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_37 (n : ℕ) : PP 37 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_38 (n : ℕ) : PP 38 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_39 (n : ℕ) : PP 39 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_40 (n : ℕ) : PP 40 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (7 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_41 (n : ℕ) : PP 41 n = ((1 : ℚ) / 60) * (n : ℚ) ^ 5 + ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((19 : ℚ) / 12) * (n : ℚ) ^ 3 + ((53 : ℚ) / 6) * (n : ℚ) ^ 2 + ((127 : ℚ) / 5) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_42 (n : ℕ) : PP 42 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_43 (n : ℕ) : PP 43 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_44 (n : ℕ) : PP 44 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_45 (n : ℕ) : PP 45 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_46 (n : ℕ) : PP 46 n = ((1 : ℚ) / 3) * (n : ℚ) ^ 3 + (3 : ℚ) * (n : ℚ) ^ 2 + ((32 : ℚ) / 3) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_47 (n : ℕ) : PP 47 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_48 (n : ℕ) : PP 48 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_49 (n : ℕ) : PP 49 n = ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((19 : ℚ) / 24) * (n : ℚ) ^ 3 + ((53 : ℚ) / 12) * (n : ℚ) ^ 2 + ((127 : ℚ) / 10) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_50 (n : ℕ) : PP 50 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_51 (n : ℕ) : PP 51 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_52 (n : ℕ) : PP 52 n = ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((19 : ℚ) / 24) * (n : ℚ) ^ 3 + ((53 : ℚ) / 12) * (n : ℚ) ^ 2 + ((127 : ℚ) / 10) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_53 (n : ℕ) : PP 53 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_54 (n : ℕ) : PP 54 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_55 (n : ℕ) : PP 55 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_56 (n : ℕ) : PP 56 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_57 (n : ℕ) : PP 57 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_58 (n : ℕ) : PP 58 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_59 (n : ℕ) : PP 59 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_60 (n : ℕ) : PP 60 n = ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((19 : ℚ) / 24) * (n : ℚ) ^ 3 + ((53 : ℚ) / 12) * (n : ℚ) ^ 2 + ((127 : ℚ) / 10) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_61 (n : ℕ) : PP 61 n = ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((19 : ℚ) / 24) * (n : ℚ) ^ 3 + ((53 : ℚ) / 12) * (n : ℚ) ^ 2 + ((127 : ℚ) / 10) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_62 (n : ℕ) : PP 62 n = ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((19 : ℚ) / 24) * (n : ℚ) ^ 3 + ((53 : ℚ) / 12) * (n : ℚ) ^ 2 + ((127 : ℚ) / 10) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_63 (n : ℕ) : PP 63 n = ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((19 : ℚ) / 24) * (n : ℚ) ^ 3 + ((53 : ℚ) / 12) * (n : ℚ) ^ 2 + ((127 : ℚ) / 10) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_64 (n : ℕ) : PP 64 n = ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((19 : ℚ) / 24) * (n : ℚ) ^ 3 + ((53 : ℚ) / 12) * (n : ℚ) ^ 2 + ((127 : ℚ) / 10) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_65 (n : ℕ) : PP 65 n = ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((19 : ℚ) / 24) * (n : ℚ) ^ 3 + ((53 : ℚ) / 12) * (n : ℚ) ^ 2 + ((127 : ℚ) / 10) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_66 (n : ℕ) : PP 66 n = ((1 : ℚ) / 120) * (n : ℚ) ^ 5 + ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((19 : ℚ) / 24) * (n : ℚ) ^ 3 + ((53 : ℚ) / 12) * (n : ℚ) ^ 2 + ((127 : ℚ) / 10) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_67 (n : ℕ) : PP 67 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_68 (n : ℕ) : PP 68 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_69 (n : ℕ) : PP 69 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_70 (n : ℕ) : PP 70 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_71 (n : ℕ) : PP 71 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_72 (n : ℕ) : PP 72 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_73 (n : ℕ) : PP 73 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + ((3 : ℚ) / 2) * (n : ℚ) ^ 2 + ((16 : ℚ) / 3) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_74 (n : ℕ) : PP 74 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 4 + ((5 : ℚ) / 3) * (n : ℚ) ^ 3 + ((47 : ℚ) / 6) * (n : ℚ) ^ 2 + ((67 : ℚ) / 3) * (n : ℚ) ^ 1 + (32 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_75 (n : ℕ) : PP 75 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_76 (n : ℕ) : PP 76 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_77 (n : ℕ) : PP 77 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_78 (n : ℕ) : PP 78 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_79 (n : ℕ) : PP 79 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_80 (n : ℕ) : PP 80 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_81 (n : ℕ) : PP 81 n = ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((5 : ℚ) / 6) * (n : ℚ) ^ 3 + ((47 : ℚ) / 12) * (n : ℚ) ^ 2 + ((67 : ℚ) / 6) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_82 (n : ℕ) : PP 82 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_83 (n : ℕ) : PP 83 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_84 (n : ℕ) : PP 84 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_85 (n : ℕ) : PP 85 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_86 (n : ℕ) : PP 86 n = ((1 : ℚ) / 12) * (n : ℚ) ^ 4 + ((5 : ℚ) / 6) * (n : ℚ) ^ 3 + ((47 : ℚ) / 12) * (n : ℚ) ^ 2 + ((67 : ℚ) / 6) * (n : ℚ) ^ 1 + (16 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_87 (n : ℕ) : PP 87 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_88 (n : ℕ) : PP 88 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_89 (n : ℕ) : PP 89 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_90 (n : ℕ) : PP 90 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_91 (n : ℕ) : PP 91 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_92 (n : ℕ) : PP 92 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_93 (n : ℕ) : PP 93 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_94 (n : ℕ) : PP 94 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_95 (n : ℕ) : PP 95 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_96 (n : ℕ) : PP 96 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_97 (n : ℕ) : PP 97 n = 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_98 (n : ℕ) : PP 98 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_99 (n : ℕ) : PP 99 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_100 (n : ℕ) : PP 100 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_101 (n : ℕ) : PP 101 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_102 (n : ℕ) : PP 102 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_103 (n : ℕ) : PP 103 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_104 (n : ℕ) : PP 104 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_105 (n : ℕ) : PP 105 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_106 (n : ℕ) : PP 106 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_107 (n : ℕ) : PP 107 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_108 (n : ℕ) : PP 108 n = ((1 : ℚ) / 24) * (n : ℚ) ^ 4 + ((5 : ℚ) / 12) * (n : ℚ) ^ 3 + ((47 : ℚ) / 24) * (n : ℚ) ^ 2 + ((67 : ℚ) / 12) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma st_0 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 0 (n + 1) := by
  have h0 : (f ![0, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 0 n := ih 0
  have h74 : (f ![0, 0, 0, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 74 n := ih 74
  have h41 : (f ![0, 0, 0, 0] (n + 3) ![0, 0, 1, 0] : ℚ) = PP 41 n := ih 41
  have h81 : (f ![0, 0, 0, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 81 n := ih 81
  have h20 : (f ![0, 0, 0, 0] (n + 3) ![0, 1, 0, 0] : ℚ) = PP 20 n := ih 20
  have h49 : (f ![0, 0, 0, 0] (n + 3) ![0, 1, 1, 0] : ℚ) = PP 49 n := ih 49
  have h89 : (f ![0, 0, 0, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 89 n := ih 89
  have h9 : (f ![0, 0, 0, 0] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 9 n := ih 9
  have h27 : (f ![0, 0, 0, 0] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 27 n := ih 27
  have h60 : (f ![0, 0, 0, 0] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 60 n := ih 60
  have h98 : (f ![0, 0, 0, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 98 n := ih 98
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, h0, h74, h41, h81, h20, h49, h89, h9, h27, h60, h98, f_dead, pp_0, pp_0, pp_74, pp_41, pp_81, pp_20, pp_49, pp_89, pp_9, pp_27, pp_60, pp_98]
  try (push_cast; ring)

lemma b_0 : (f ![0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 0 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = 180 := by exact_mod_cast fv3_0
  rw [h, pp_0]; try norm_num

set_option maxRecDepth 100000 in
lemma st_1 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 1 (n + 1) := by
  have h2 : (f ![2, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 2 n := ih 2
  have h76 : (f ![2, 0, 0, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 76 n := ih 76
  have h43 : (f ![2, 0, 0, 0] (n + 3) ![0, 0, 1, 0] : ℚ) = PP 43 n := ih 43
  have h83 : (f ![2, 0, 0, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 83 n := ih 83
  have h22 : (f ![2, 0, 0, 0] (n + 3) ![0, 1, 0, 0] : ℚ) = PP 22 n := ih 22
  have h51 : (f ![2, 0, 0, 0] (n + 3) ![0, 1, 1, 0] : ℚ) = PP 51 n := ih 51
  have h91 : (f ![2, 0, 0, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 91 n := ih 91
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, h2, h76, h43, h83, h22, h51, h91, f_dead, pp_1, pp_2, pp_76, pp_43, pp_83, pp_22, pp_51, pp_91]
  try (push_cast; ring)

lemma b_1 : (f ![1, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 1 0 := by
  have h : (f ![1, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = 20 := by exact_mod_cast fv3_1
  rw [h, pp_1]; try norm_num

set_option maxRecDepth 100000 in
lemma st_2 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 2 (n + 1) := by
  have h2 : (f ![2, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 2 n := ih 2
  have h76 : (f ![2, 0, 0, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 76 n := ih 76
  have h43 : (f ![2, 0, 0, 0] (n + 3) ![0, 0, 1, 0] : ℚ) = PP 43 n := ih 43
  have h83 : (f ![2, 0, 0, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 83 n := ih 83
  have h22 : (f ![2, 0, 0, 0] (n + 3) ![0, 1, 0, 0] : ℚ) = PP 22 n := ih 22
  have h51 : (f ![2, 0, 0, 0] (n + 3) ![0, 1, 1, 0] : ℚ) = PP 51 n := ih 51
  have h91 : (f ![2, 0, 0, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 91 n := ih 91
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h2, h76, h43, h83, h22, h51, h91, f_dead, pp_2, pp_2, pp_76, pp_43, pp_83, pp_22, pp_51, pp_91]
  try (push_cast; ring)

lemma b_2 : (f ![2, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 2 0 := by
  have h : (f ![2, 0, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = 20 := by exact_mod_cast fv3_2
  rw [h, pp_2]; try norm_num

set_option maxRecDepth 100000 in
lemma st_3 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 2, 0, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 3 (n + 1) := by
  have h4 : (f ![2, 2, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 4 n := ih 4
  have h78 : (f ![2, 2, 0, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 78 n := ih 78
  have h45 : (f ![2, 2, 0, 0] (n + 3) ![0, 0, 1, 0] : ℚ) = PP 45 n := ih 45
  have h85 : (f ![2, 2, 0, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 85 n := ih 85
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h4, h78, h45, h85, f_dead, pp_3, pp_4, pp_78, pp_45, pp_85]
  try (push_cast; ring)

lemma b_3 : (f ![1, 2, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 3 0 := by
  have h : (f ![1, 2, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = 6 := by exact_mod_cast fv3_7
  rw [h, pp_3]; try norm_num

set_option maxRecDepth 100000 in
lemma st_4 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 0, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 4 (n + 1) := by
  have h4 : (f ![2, 2, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 4 n := ih 4
  have h78 : (f ![2, 2, 0, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 78 n := ih 78
  have h45 : (f ![2, 2, 0, 0] (n + 3) ![0, 0, 1, 0] : ℚ) = PP 45 n := ih 45
  have h85 : (f ![2, 2, 0, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 85 n := ih 85
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h4, h78, h45, h85, f_dead, pp_4, pp_4, pp_78, pp_45, pp_85]
  try (push_cast; ring)

lemma b_4 : (f ![2, 2, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 4 0 := by
  have h : (f ![2, 2, 0, 0] 3 ![0, 0, 0, 0] : ℚ) = 6 := by exact_mod_cast fv3_8
  rw [h, pp_4]; try norm_num

set_option maxRecDepth 100000 in
lemma st_5 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 2, 2, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 5 (n + 1) := by
  have h6 : (f ![2, 2, 2, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 6 n := ih 6
  have h80 : (f ![2, 2, 2, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 80 n := ih 80
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl20, h6, h80, f_dead, pp_5, pp_6, pp_80]
  try (push_cast; ring)

lemma b_5 : (f ![1, 2, 2, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 5 0 := by
  have h : (f ![1, 2, 2, 0] 3 ![0, 0, 0, 0] : ℚ) = 2 := by exact_mod_cast fv3_25
  rw [h, pp_5]; try norm_num

set_option maxRecDepth 100000 in
lemma st_6 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 2, 0] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 6 (n + 1) := by
  have h6 : (f ![2, 2, 2, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 6 n := ih 6
  have h80 : (f ![2, 2, 2, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 80 n := ih 80
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl20, h6, h80, f_dead, pp_6, pp_6, pp_80]
  try (push_cast; ring)

lemma b_6 : (f ![2, 2, 2, 0] 3 ![0, 0, 0, 0] : ℚ) = PP 6 0 := by
  have h : (f ![2, 2, 2, 0] 3 ![0, 0, 0, 0] : ℚ) = 2 := by exact_mod_cast fv3_26
  rw [h, pp_6]; try norm_num

set_option maxRecDepth 100000 in
lemma st_7 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 2, 2, 2] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 7 (n + 1) := by
  have h8 : (f ![2, 2, 2, 2] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 8 n := ih 8
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl10, dl20, h8, f_dead, pp_7, pp_8]
  try (push_cast; ring)

lemma b_7 : (f ![1, 2, 2, 2] 3 ![0, 0, 0, 0] : ℚ) = PP 7 0 := by
  have h : (f ![1, 2, 2, 2] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_79
  rw [h, pp_7]; try norm_num

set_option maxRecDepth 100000 in
lemma st_8 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 2, 2] (n + 3 + 1) ![0, 0, 0, 0] : ℚ) = PP 8 (n + 1) := by
  have h8 : (f ![2, 2, 2, 2] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 8 n := ih 8
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl20, h8, f_dead, pp_8, pp_8]
  try (push_cast; ring)

lemma b_8 : (f ![2, 2, 2, 2] 3 ![0, 0, 0, 0] : ℚ) = PP 8 0 := by
  have h : (f ![2, 2, 2, 2] 3 ![0, 0, 0, 0] : ℚ) = 1 := by exact_mod_cast fv3_80
  rw [h, pp_8]; try norm_num

set_option maxRecDepth 100000 in
lemma st_9 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![1, 0, 0, 0] : ℚ) = PP 9 (n + 1) := by
  have h1 : (f ![1, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 1 n := ih 1
  have h75 : (f ![1, 0, 0, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 75 n := ih 75
  have h42 : (f ![1, 0, 0, 0] (n + 3) ![0, 0, 1, 0] : ℚ) = PP 42 n := ih 42
  have h82 : (f ![1, 0, 0, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 82 n := ih 82
  have h21 : (f ![1, 0, 0, 0] (n + 3) ![0, 1, 0, 0] : ℚ) = PP 21 n := ih 21
  have h50 : (f ![1, 0, 0, 0] (n + 3) ![0, 1, 1, 0] : ℚ) = PP 50 n := ih 50
  have h90 : (f ![1, 0, 0, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 90 n := ih 90
  have h10 : (f ![1, 0, 0, 0] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 10 n := ih 10
  have h28 : (f ![1, 0, 0, 0] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 28 n := ih 28
  have h61 : (f ![1, 0, 0, 0] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 61 n := ih 61
  have h99 : (f ![1, 0, 0, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 99 n := ih 99
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h1, h75, h42, h82, h21, h50, h90, h10, h28, h61, h99, f_dead, pp_9, pp_1, pp_75, pp_42, pp_82, pp_21, pp_50, pp_90, pp_10, pp_28, pp_61, pp_99]
  try (push_cast; ring)

lemma b_9 : (f ![0, 0, 0, 0] 3 ![1, 0, 0, 0] : ℚ) = PP 9 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![1, 0, 0, 0] : ℚ) = 81 := by exact_mod_cast fv3_81
  rw [h, pp_9]; try norm_num

set_option maxRecDepth 100000 in
lemma st_10 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0] (n + 3 + 1) ![1, 0, 0, 0] : ℚ) = PP 10 (n + 1) := by
  have h1 : (f ![1, 0, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 1 n := ih 1
  have h75 : (f ![1, 0, 0, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 75 n := ih 75
  have h42 : (f ![1, 0, 0, 0] (n + 3) ![0, 0, 1, 0] : ℚ) = PP 42 n := ih 42
  have h82 : (f ![1, 0, 0, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 82 n := ih 82
  have h21 : (f ![1, 0, 0, 0] (n + 3) ![0, 1, 0, 0] : ℚ) = PP 21 n := ih 21
  have h50 : (f ![1, 0, 0, 0] (n + 3) ![0, 1, 1, 0] : ℚ) = PP 50 n := ih 50
  have h90 : (f ![1, 0, 0, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 90 n := ih 90
  have h10 : (f ![1, 0, 0, 0] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 10 n := ih 10
  have h28 : (f ![1, 0, 0, 0] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 28 n := ih 28
  have h61 : (f ![1, 0, 0, 0] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 61 n := ih 61
  have h99 : (f ![1, 0, 0, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 99 n := ih 99
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl11, h1, h75, h42, h82, h21, h50, h90, h10, h28, h61, h99, f_dead, pp_10, pp_1, pp_75, pp_42, pp_82, pp_21, pp_50, pp_90, pp_10, pp_28, pp_61, pp_99]
  try (push_cast; ring)

lemma b_10 : (f ![1, 0, 0, 0] 3 ![1, 0, 0, 0] : ℚ) = PP 10 0 := by
  have h : (f ![1, 0, 0, 0] 3 ![1, 0, 0, 0] : ℚ) = 81 := by exact_mod_cast fv3_82
  rw [h, pp_10]; try norm_num

set_option maxRecDepth 100000 in
lemma st_11 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0] (n + 3 + 1) ![1, 0, 0, 0] : ℚ) = PP 11 (n + 1) := by
  have h3 : (f ![1, 2, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 3 n := ih 3
  have h77 : (f ![1, 2, 0, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 77 n := ih 77
  have h44 : (f ![1, 2, 0, 0] (n + 3) ![0, 0, 1, 0] : ℚ) = PP 44 n := ih 44
  have h84 : (f ![1, 2, 0, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 84 n := ih 84
  have h13 : (f ![1, 2, 0, 0] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 13 n := ih 13
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h3, h77, h44, h84, h13, f_dead, pp_11, pp_3, pp_77, pp_44, pp_84, pp_13]
  try (push_cast; ring)

lemma b_11 : (f ![0, 1, 0, 0] 3 ![1, 0, 0, 0] : ℚ) = PP 11 0 := by
  have h : (f ![0, 1, 0, 0] 3 ![1, 0, 0, 0] : ℚ) = 17 := by exact_mod_cast fv3_84
  rw [h, pp_11]; try norm_num

set_option maxRecDepth 100000 in
lemma st_12 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0] (n + 3 + 1) ![1, 0, 0, 0] : ℚ) = PP 12 (n + 1) := by
  have h3 : (f ![1, 2, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 3 n := ih 3
  have h77 : (f ![1, 2, 0, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 77 n := ih 77
  have h44 : (f ![1, 2, 0, 0] (n + 3) ![0, 0, 1, 0] : ℚ) = PP 44 n := ih 44
  have h84 : (f ![1, 2, 0, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 84 n := ih 84
  have h13 : (f ![1, 2, 0, 0] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 13 n := ih 13
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl11, h3, h77, h44, h84, h13, f_dead, pp_12, pp_3, pp_77, pp_44, pp_84, pp_13]
  try (push_cast; ring)

lemma b_12 : (f ![1, 1, 0, 0] 3 ![1, 0, 0, 0] : ℚ) = PP 12 0 := by
  have h : (f ![1, 1, 0, 0] 3 ![1, 0, 0, 0] : ℚ) = 17 := by exact_mod_cast fv3_85
  rw [h, pp_12]; try norm_num

set_option maxRecDepth 100000 in
lemma st_13 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 2, 0, 0] (n + 3 + 1) ![1, 0, 0, 0] : ℚ) = PP 13 (n + 1) := by
  have h3 : (f ![1, 2, 0, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 3 n := ih 3
  have h77 : (f ![1, 2, 0, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 77 n := ih 77
  have h44 : (f ![1, 2, 0, 0] (n + 3) ![0, 0, 1, 0] : ℚ) = PP 44 n := ih 44
  have h84 : (f ![1, 2, 0, 0] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 84 n := ih 84
  have h13 : (f ![1, 2, 0, 0] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 13 n := ih 13
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl11, dl20, h3, h77, h44, h84, h13, f_dead, pp_13, pp_3, pp_77, pp_44, pp_84, pp_13]
  try (push_cast; ring)

lemma b_13 : (f ![1, 2, 0, 0] 3 ![1, 0, 0, 0] : ℚ) = PP 13 0 := by
  have h : (f ![1, 2, 0, 0] 3 ![1, 0, 0, 0] : ℚ) = 17 := by exact_mod_cast fv3_88
  rw [h, pp_13]; try norm_num

set_option maxRecDepth 100000 in
lemma st_14 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 2, 0] (n + 3 + 1) ![1, 0, 0, 0] : ℚ) = PP 14 (n + 1) := by
  have h5 : (f ![1, 2, 2, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 5 n := ih 5
  have h79 : (f ![1, 2, 2, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 79 n := ih 79
  have h16 : (f ![1, 2, 2, 0] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 16 n := ih 16
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h5, h79, h16, f_dead, pp_14, pp_5, pp_79, pp_16]
  try (push_cast; ring)

lemma b_14 : (f ![0, 1, 2, 0] 3 ![1, 0, 0, 0] : ℚ) = PP 14 0 := by
  have h : (f ![0, 1, 2, 0] 3 ![1, 0, 0, 0] : ℚ) = 7 := by exact_mod_cast fv3_102
  rw [h, pp_14]; try norm_num

set_option maxRecDepth 100000 in
lemma st_15 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 2, 0] (n + 3 + 1) ![1, 0, 0, 0] : ℚ) = PP 15 (n + 1) := by
  have h5 : (f ![1, 2, 2, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 5 n := ih 5
  have h79 : (f ![1, 2, 2, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 79 n := ih 79
  have h16 : (f ![1, 2, 2, 0] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 16 n := ih 16
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl11, dl20, h5, h79, h16, f_dead, pp_15, pp_5, pp_79, pp_16]
  try (push_cast; ring)

lemma b_15 : (f ![1, 1, 2, 0] 3 ![1, 0, 0, 0] : ℚ) = PP 15 0 := by
  have h : (f ![1, 1, 2, 0] 3 ![1, 0, 0, 0] : ℚ) = 7 := by exact_mod_cast fv3_103
  rw [h, pp_15]; try norm_num

set_option maxRecDepth 100000 in
lemma st_16 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 2, 2, 0] (n + 3 + 1) ![1, 0, 0, 0] : ℚ) = PP 16 (n + 1) := by
  have h5 : (f ![1, 2, 2, 0] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 5 n := ih 5
  have h79 : (f ![1, 2, 2, 0] (n + 3) ![0, 0, 0, 1] : ℚ) = PP 79 n := ih 79
  have h16 : (f ![1, 2, 2, 0] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 16 n := ih 16
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl11, dl20, h5, h79, h16, f_dead, pp_16, pp_5, pp_79, pp_16]
  try (push_cast; ring)

lemma b_16 : (f ![1, 2, 2, 0] 3 ![1, 0, 0, 0] : ℚ) = PP 16 0 := by
  have h : (f ![1, 2, 2, 0] 3 ![1, 0, 0, 0] : ℚ) = 7 := by exact_mod_cast fv3_106
  rw [h, pp_16]; try norm_num

set_option maxRecDepth 100000 in
lemma st_17 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 2, 2] (n + 3 + 1) ![1, 0, 0, 0] : ℚ) = PP 17 (n + 1) := by
  have h7 : (f ![1, 2, 2, 2] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 7 n := ih 7
  have h19 : (f ![1, 2, 2, 2] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 19 n := ih 19
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl20, h7, h19, f_dead, pp_17, pp_7, pp_19]
  try (push_cast; ring)

lemma b_17 : (f ![0, 1, 2, 2] 3 ![1, 0, 0, 0] : ℚ) = PP 17 0 := by
  have h : (f ![0, 1, 2, 2] 3 ![1, 0, 0, 0] : ℚ) = 4 := by exact_mod_cast fv3_156
  rw [h, pp_17]; try norm_num

set_option maxRecDepth 100000 in
lemma st_18 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 2, 2] (n + 3 + 1) ![1, 0, 0, 0] : ℚ) = PP 18 (n + 1) := by
  have h7 : (f ![1, 2, 2, 2] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 7 n := ih 7
  have h19 : (f ![1, 2, 2, 2] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 19 n := ih 19
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl10, dl11, dl20, h7, h19, f_dead, pp_18, pp_7, pp_19]
  try (push_cast; ring)

lemma b_18 : (f ![1, 1, 2, 2] 3 ![1, 0, 0, 0] : ℚ) = PP 18 0 := by
  have h : (f ![1, 1, 2, 2] 3 ![1, 0, 0, 0] : ℚ) = 4 := by exact_mod_cast fv3_157
  rw [h, pp_18]; try norm_num

set_option maxRecDepth 100000 in
lemma st_19 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 2, 2, 2] (n + 3 + 1) ![1, 0, 0, 0] : ℚ) = PP 19 (n + 1) := by
  have h7 : (f ![1, 2, 2, 2] (n + 3) ![0, 0, 0, 0] : ℚ) = PP 7 n := ih 7
  have h19 : (f ![1, 2, 2, 2] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 19 n := ih 19
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl11, dl20, h7, h19, f_dead, pp_19, pp_7, pp_19]
  try (push_cast; ring)

lemma b_19 : (f ![1, 2, 2, 2] 3 ![1, 0, 0, 0] : ℚ) = PP 19 0 := by
  have h : (f ![1, 2, 2, 2] 3 ![1, 0, 0, 0] : ℚ) = 4 := by exact_mod_cast fv3_160
  rw [h, pp_19]; try norm_num

set_option maxRecDepth 100000 in
lemma st_20 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![0, 1, 0, 0] : ℚ) = PP 20 (n + 1) := by
  have h11 : (f ![0, 1, 0, 0] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 11 n := ih 11
  have h29 : (f ![0, 1, 0, 0] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 29 n := ih 29
  have h62 : (f ![0, 1, 0, 0] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 62 n := ih 62
  have h100 : (f ![0, 1, 0, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 100 n := ih 100
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h11, h29, h62, h100, f_dead, pp_20, pp_11, pp_29, pp_62, pp_100]
  try (push_cast; ring)

lemma b_20 : (f ![0, 0, 0, 0] 3 ![0, 1, 0, 0] : ℚ) = PP 20 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![0, 1, 0, 0] : ℚ) = 36 := by exact_mod_cast fv3_162
  rw [h, pp_20]; try norm_num

set_option maxRecDepth 100000 in
lemma st_21 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0] (n + 3 + 1) ![0, 1, 0, 0] : ℚ) = PP 21 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, f_dead, pp_21]
  try (push_cast; ring)

lemma b_21 : (f ![1, 0, 0, 0] 3 ![0, 1, 0, 0] : ℚ) = PP 21 0 := by
  have h : (f ![1, 0, 0, 0] 3 ![0, 1, 0, 0] : ℚ) = 0 := by exact_mod_cast fv3_163
  rw [h, pp_21]; try norm_num

set_option maxRecDepth 100000 in
lemma st_22 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 0, 0] (n + 3 + 1) ![0, 1, 0, 0] : ℚ) = PP 22 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl20, f_dead, pp_22]
  try (push_cast; ring)

lemma b_22 : (f ![2, 0, 0, 0] 3 ![0, 1, 0, 0] : ℚ) = PP 22 0 := by
  have h : (f ![2, 0, 0, 0] 3 ![0, 1, 0, 0] : ℚ) = 0 := by exact_mod_cast fv3_164
  rw [h, pp_22]; try norm_num

set_option maxRecDepth 100000 in
lemma st_23 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0] (n + 3 + 1) ![0, 1, 0, 0] : ℚ) = PP 23 (n + 1) := by
  have h14 : (f ![0, 1, 2, 0] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 14 n := ih 14
  have h34 : (f ![0, 1, 2, 0] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 34 n := ih 34
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h14, h34, f_dead, pp_23, pp_14, pp_34]
  try (push_cast; ring)

lemma b_23 : (f ![0, 0, 1, 0] 3 ![0, 1, 0, 0] : ℚ) = PP 23 0 := by
  have h : (f ![0, 0, 1, 0] 3 ![0, 1, 0, 0] : ℚ) = 10 := by exact_mod_cast fv3_171
  rw [h, pp_23]; try norm_num

set_option maxRecDepth 100000 in
lemma st_24 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 1, 0] (n + 3 + 1) ![0, 1, 0, 0] : ℚ) = PP 24 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, f_dead, pp_24]
  try (push_cast; ring)

lemma b_24 : (f ![2, 0, 1, 0] 3 ![0, 1, 0, 0] : ℚ) = PP 24 0 := by
  have h : (f ![2, 0, 1, 0] 3 ![0, 1, 0, 0] : ℚ) = 0 := by exact_mod_cast fv3_173
  rw [h, pp_24]; try norm_num

set_option maxRecDepth 100000 in
lemma st_25 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 2] (n + 3 + 1) ![0, 1, 0, 0] : ℚ) = PP 25 (n + 1) := by
  have h17 : (f ![0, 1, 2, 2] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 17 n := ih 17
  have h39 : (f ![0, 1, 2, 2] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 39 n := ih 39
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h17, h39, f_dead, pp_25, pp_17, pp_39]
  try (push_cast; ring)

lemma b_25 : (f ![0, 0, 1, 2] 3 ![0, 1, 0, 0] : ℚ) = PP 25 0 := by
  have h : (f ![0, 0, 1, 2] 3 ![0, 1, 0, 0] : ℚ) = 7 := by exact_mod_cast fv3_225
  rw [h, pp_25]; try norm_num

set_option maxRecDepth 100000 in
lemma st_26 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 1, 2] (n + 3 + 1) ![0, 1, 0, 0] : ℚ) = PP 26 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl20, f_dead, pp_26]
  try (push_cast; ring)

lemma b_26 : (f ![2, 0, 1, 2] 3 ![0, 1, 0, 0] : ℚ) = PP 26 0 := by
  have h : (f ![2, 0, 1, 2] 3 ![0, 1, 0, 0] : ℚ) = 0 := by exact_mod_cast fv3_227
  rw [h, pp_26]; try norm_num

set_option maxRecDepth 100000 in
lemma st_27 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![1, 1, 0, 0] : ℚ) = PP 27 (n + 1) := by
  have h12 : (f ![1, 1, 0, 0] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 12 n := ih 12
  have h30 : (f ![1, 1, 0, 0] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 30 n := ih 30
  have h63 : (f ![1, 1, 0, 0] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 63 n := ih 63
  have h101 : (f ![1, 1, 0, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 101 n := ih 101
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h12, h30, h63, h101, f_dead, pp_27, pp_12, pp_30, pp_63, pp_101]
  try (push_cast; ring)

lemma b_27 : (f ![0, 0, 0, 0] 3 ![1, 1, 0, 0] : ℚ) = PP 27 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![1, 1, 0, 0] : ℚ) = 36 := by exact_mod_cast fv3_243
  rw [h, pp_27]; try norm_num

set_option maxRecDepth 100000 in
lemma st_28 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0] (n + 3 + 1) ![1, 1, 0, 0] : ℚ) = PP 28 (n + 1) := by
  have h12 : (f ![1, 1, 0, 0] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 12 n := ih 12
  have h30 : (f ![1, 1, 0, 0] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 30 n := ih 30
  have h63 : (f ![1, 1, 0, 0] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 63 n := ih 63
  have h101 : (f ![1, 1, 0, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 101 n := ih 101
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h12, h30, h63, h101, f_dead, pp_28, pp_12, pp_30, pp_63, pp_101]
  try (push_cast; ring)

lemma b_28 : (f ![1, 0, 0, 0] 3 ![1, 1, 0, 0] : ℚ) = PP 28 0 := by
  have h : (f ![1, 0, 0, 0] 3 ![1, 1, 0, 0] : ℚ) = 36 := by exact_mod_cast fv3_244
  rw [h, pp_28]; try norm_num

set_option maxRecDepth 100000 in
lemma st_29 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0] (n + 3 + 1) ![1, 1, 0, 0] : ℚ) = PP 29 (n + 1) := by
  have h12 : (f ![1, 1, 0, 0] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 12 n := ih 12
  have h30 : (f ![1, 1, 0, 0] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 30 n := ih 30
  have h63 : (f ![1, 1, 0, 0] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 63 n := ih 63
  have h101 : (f ![1, 1, 0, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 101 n := ih 101
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h12, h30, h63, h101, f_dead, pp_29, pp_12, pp_30, pp_63, pp_101]
  try (push_cast; ring)

lemma b_29 : (f ![0, 1, 0, 0] 3 ![1, 1, 0, 0] : ℚ) = PP 29 0 := by
  have h : (f ![0, 1, 0, 0] 3 ![1, 1, 0, 0] : ℚ) = 36 := by exact_mod_cast fv3_246
  rw [h, pp_29]; try norm_num

set_option maxRecDepth 100000 in
lemma st_30 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0] (n + 3 + 1) ![1, 1, 0, 0] : ℚ) = PP 30 (n + 1) := by
  have h12 : (f ![1, 1, 0, 0] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 12 n := ih 12
  have h30 : (f ![1, 1, 0, 0] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 30 n := ih 30
  have h63 : (f ![1, 1, 0, 0] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 63 n := ih 63
  have h101 : (f ![1, 1, 0, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 101 n := ih 101
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl11, h12, h30, h63, h101, f_dead, pp_30, pp_12, pp_30, pp_63, pp_101]
  try (push_cast; ring)

lemma b_30 : (f ![1, 1, 0, 0] 3 ![1, 1, 0, 0] : ℚ) = PP 30 0 := by
  have h : (f ![1, 1, 0, 0] 3 ![1, 1, 0, 0] : ℚ) = 36 := by exact_mod_cast fv3_247
  rw [h, pp_30]; try norm_num

set_option maxRecDepth 100000 in
lemma st_31 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0] (n + 3 + 1) ![1, 1, 0, 0] : ℚ) = PP 31 (n + 1) := by
  have h15 : (f ![1, 1, 2, 0] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 15 n := ih 15
  have h35 : (f ![1, 1, 2, 0] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 35 n := ih 35
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h15, h35, f_dead, pp_31, pp_15, pp_35]
  try (push_cast; ring)

lemma b_31 : (f ![0, 0, 1, 0] 3 ![1, 1, 0, 0] : ℚ) = PP 31 0 := by
  have h : (f ![0, 0, 1, 0] 3 ![1, 1, 0, 0] : ℚ) = 10 := by exact_mod_cast fv3_252
  rw [h, pp_31]; try norm_num

set_option maxRecDepth 100000 in
lemma st_32 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 0] (n + 3 + 1) ![1, 1, 0, 0] : ℚ) = PP 32 (n + 1) := by
  have h15 : (f ![1, 1, 2, 0] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 15 n := ih 15
  have h35 : (f ![1, 1, 2, 0] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 35 n := ih 35
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h15, h35, f_dead, pp_32, pp_15, pp_35]
  try (push_cast; ring)

lemma b_32 : (f ![0, 1, 1, 0] 3 ![1, 1, 0, 0] : ℚ) = PP 32 0 := by
  have h : (f ![0, 1, 1, 0] 3 ![1, 1, 0, 0] : ℚ) = 10 := by exact_mod_cast fv3_255
  rw [h, pp_32]; try norm_num

set_option maxRecDepth 100000 in
lemma st_33 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 0] (n + 3 + 1) ![1, 1, 0, 0] : ℚ) = PP 33 (n + 1) := by
  have h15 : (f ![1, 1, 2, 0] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 15 n := ih 15
  have h35 : (f ![1, 1, 2, 0] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 35 n := ih 35
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl10, dl11, h15, h35, f_dead, pp_33, pp_15, pp_35]
  try (push_cast; ring)

lemma b_33 : (f ![1, 1, 1, 0] 3 ![1, 1, 0, 0] : ℚ) = PP 33 0 := by
  have h : (f ![1, 1, 1, 0] 3 ![1, 1, 0, 0] : ℚ) = 10 := by exact_mod_cast fv3_256
  rw [h, pp_33]; try norm_num

set_option maxRecDepth 100000 in
lemma st_34 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 2, 0] (n + 3 + 1) ![1, 1, 0, 0] : ℚ) = PP 34 (n + 1) := by
  have h15 : (f ![1, 1, 2, 0] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 15 n := ih 15
  have h35 : (f ![1, 1, 2, 0] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 35 n := ih 35
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h15, h35, f_dead, pp_34, pp_15, pp_35]
  try (push_cast; ring)

lemma b_34 : (f ![0, 1, 2, 0] 3 ![1, 1, 0, 0] : ℚ) = PP 34 0 := by
  have h : (f ![0, 1, 2, 0] 3 ![1, 1, 0, 0] : ℚ) = 10 := by exact_mod_cast fv3_264
  rw [h, pp_34]; try norm_num

set_option maxRecDepth 100000 in
lemma st_35 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 2, 0] (n + 3 + 1) ![1, 1, 0, 0] : ℚ) = PP 35 (n + 1) := by
  have h15 : (f ![1, 1, 2, 0] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 15 n := ih 15
  have h35 : (f ![1, 1, 2, 0] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 35 n := ih 35
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl11, dl20, h15, h35, f_dead, pp_35, pp_15, pp_35]
  try (push_cast; ring)

lemma b_35 : (f ![1, 1, 2, 0] 3 ![1, 1, 0, 0] : ℚ) = PP 35 0 := by
  have h : (f ![1, 1, 2, 0] 3 ![1, 1, 0, 0] : ℚ) = 10 := by exact_mod_cast fv3_265
  rw [h, pp_35]; try norm_num

set_option maxRecDepth 100000 in
lemma st_36 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 2] (n + 3 + 1) ![1, 1, 0, 0] : ℚ) = PP 36 (n + 1) := by
  have h18 : (f ![1, 1, 2, 2] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 18 n := ih 18
  have h40 : (f ![1, 1, 2, 2] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 40 n := ih 40
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl20, h18, h40, f_dead, pp_36, pp_18, pp_40]
  try (push_cast; ring)

lemma b_36 : (f ![0, 0, 1, 2] 3 ![1, 1, 0, 0] : ℚ) = PP 36 0 := by
  have h : (f ![0, 0, 1, 2] 3 ![1, 1, 0, 0] : ℚ) = 7 := by exact_mod_cast fv3_306
  rw [h, pp_36]; try norm_num

set_option maxRecDepth 100000 in
lemma st_37 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 2] (n + 3 + 1) ![1, 1, 0, 0] : ℚ) = PP 37 (n + 1) := by
  have h18 : (f ![1, 1, 2, 2] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 18 n := ih 18
  have h40 : (f ![1, 1, 2, 2] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 40 n := ih 40
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl11, dl20, h18, h40, f_dead, pp_37, pp_18, pp_40]
  try (push_cast; ring)

lemma b_37 : (f ![0, 1, 1, 2] 3 ![1, 1, 0, 0] : ℚ) = PP 37 0 := by
  have h : (f ![0, 1, 1, 2] 3 ![1, 1, 0, 0] : ℚ) = 7 := by exact_mod_cast fv3_309
  rw [h, pp_37]; try norm_num

set_option maxRecDepth 100000 in
lemma st_38 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 2] (n + 3 + 1) ![1, 1, 0, 0] : ℚ) = PP 38 (n + 1) := by
  have h18 : (f ![1, 1, 2, 2] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 18 n := ih 18
  have h40 : (f ![1, 1, 2, 2] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 40 n := ih 40
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl10, dl11, dl20, h18, h40, f_dead, pp_38, pp_18, pp_40]
  try (push_cast; ring)

lemma b_38 : (f ![1, 1, 1, 2] 3 ![1, 1, 0, 0] : ℚ) = PP 38 0 := by
  have h : (f ![1, 1, 1, 2] 3 ![1, 1, 0, 0] : ℚ) = 7 := by exact_mod_cast fv3_310
  rw [h, pp_38]; try norm_num

set_option maxRecDepth 100000 in
lemma st_39 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 2, 2] (n + 3 + 1) ![1, 1, 0, 0] : ℚ) = PP 39 (n + 1) := by
  have h18 : (f ![1, 1, 2, 2] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 18 n := ih 18
  have h40 : (f ![1, 1, 2, 2] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 40 n := ih 40
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, dl20, h18, h40, f_dead, pp_39, pp_18, pp_40]
  try (push_cast; ring)

lemma b_39 : (f ![0, 1, 2, 2] 3 ![1, 1, 0, 0] : ℚ) = PP 39 0 := by
  have h : (f ![0, 1, 2, 2] 3 ![1, 1, 0, 0] : ℚ) = 7 := by exact_mod_cast fv3_318
  rw [h, pp_39]; try norm_num

set_option maxRecDepth 100000 in
lemma st_40 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 2, 2] (n + 3 + 1) ![1, 1, 0, 0] : ℚ) = PP 40 (n + 1) := by
  have h18 : (f ![1, 1, 2, 2] (n + 3) ![1, 0, 0, 0] : ℚ) = PP 18 n := ih 18
  have h40 : (f ![1, 1, 2, 2] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 40 n := ih 40
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl11, dl20, h18, h40, f_dead, pp_40, pp_18, pp_40]
  try (push_cast; ring)

lemma b_40 : (f ![1, 1, 2, 2] 3 ![1, 1, 0, 0] : ℚ) = PP 40 0 := by
  have h : (f ![1, 1, 2, 2] 3 ![1, 1, 0, 0] : ℚ) = 7 := by exact_mod_cast fv3_319
  rw [h, pp_40]; try norm_num

set_option maxRecDepth 100000 in
lemma st_41 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![0, 0, 1, 0] : ℚ) = PP 41 (n + 1) := by
  have h23 : (f ![0, 0, 1, 0] (n + 3) ![0, 1, 0, 0] : ℚ) = PP 23 n := ih 23
  have h52 : (f ![0, 0, 1, 0] (n + 3) ![0, 1, 1, 0] : ℚ) = PP 52 n := ih 52
  have h92 : (f ![0, 0, 1, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 92 n := ih 92
  have h31 : (f ![0, 0, 1, 0] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 31 n := ih 31
  have h64 : (f ![0, 0, 1, 0] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 64 n := ih 64
  have h102 : (f ![0, 0, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 102 n := ih 102
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h23, h52, h92, h31, h64, h102, f_dead, pp_41, pp_23, pp_52, pp_92, pp_31, pp_64, pp_102]
  try (push_cast; ring)

lemma b_41 : (f ![0, 0, 0, 0] 3 ![0, 0, 1, 0] : ℚ) = PP 41 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![0, 0, 1, 0] : ℚ) = 32 := by exact_mod_cast fv3_324
  rw [h, pp_41]; try norm_num

set_option maxRecDepth 100000 in
lemma st_42 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0] (n + 3 + 1) ![0, 0, 1, 0] : ℚ) = PP 42 (n + 1) := by
  have h24 : (f ![2, 0, 1, 0] (n + 3) ![0, 1, 0, 0] : ℚ) = PP 24 n := ih 24
  have h53 : (f ![2, 0, 1, 0] (n + 3) ![0, 1, 1, 0] : ℚ) = PP 53 n := ih 53
  have h93 : (f ![2, 0, 1, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 93 n := ih 93
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h24, h53, h93, f_dead, pp_42, pp_24, pp_53, pp_93]
  try (push_cast; ring)

lemma b_42 : (f ![1, 0, 0, 0] 3 ![0, 0, 1, 0] : ℚ) = PP 42 0 := by
  have h : (f ![1, 0, 0, 0] 3 ![0, 0, 1, 0] : ℚ) = 0 := by exact_mod_cast fv3_325
  rw [h, pp_42]; try norm_num

set_option maxRecDepth 100000 in
lemma st_43 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 0, 0] (n + 3 + 1) ![0, 0, 1, 0] : ℚ) = PP 43 (n + 1) := by
  have h24 : (f ![2, 0, 1, 0] (n + 3) ![0, 1, 0, 0] : ℚ) = PP 24 n := ih 24
  have h53 : (f ![2, 0, 1, 0] (n + 3) ![0, 1, 1, 0] : ℚ) = PP 53 n := ih 53
  have h93 : (f ![2, 0, 1, 0] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 93 n := ih 93
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl20, h24, h53, h93, f_dead, pp_43, pp_24, pp_53, pp_93]
  try (push_cast; ring)

lemma b_43 : (f ![2, 0, 0, 0] 3 ![0, 0, 1, 0] : ℚ) = PP 43 0 := by
  have h : (f ![2, 0, 0, 0] 3 ![0, 0, 1, 0] : ℚ) = 0 := by exact_mod_cast fv3_326
  rw [h, pp_43]; try norm_num

set_option maxRecDepth 100000 in
lemma st_44 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 2, 0, 0] (n + 3 + 1) ![0, 0, 1, 0] : ℚ) = PP 44 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, f_dead, pp_44]
  try (push_cast; ring)

lemma b_44 : (f ![1, 2, 0, 0] 3 ![0, 0, 1, 0] : ℚ) = PP 44 0 := by
  have h : (f ![1, 2, 0, 0] 3 ![0, 0, 1, 0] : ℚ) = 0 := by exact_mod_cast fv3_331
  rw [h, pp_44]; try norm_num

set_option maxRecDepth 100000 in
lemma st_45 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 0, 0] (n + 3 + 1) ![0, 0, 1, 0] : ℚ) = PP 45 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl20, f_dead, pp_45]
  try (push_cast; ring)

lemma b_45 : (f ![2, 2, 0, 0] 3 ![0, 0, 1, 0] : ℚ) = PP 45 0 := by
  have h : (f ![2, 2, 0, 0] 3 ![0, 0, 1, 0] : ℚ) = 0 := by exact_mod_cast fv3_332
  rw [h, pp_45]; try norm_num

set_option maxRecDepth 100000 in
lemma st_46 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1] (n + 3 + 1) ![0, 0, 1, 0] : ℚ) = PP 46 (n + 1) := by
  have h25 : (f ![0, 0, 1, 2] (n + 3) ![0, 1, 0, 0] : ℚ) = PP 25 n := ih 25
  have h58 : (f ![0, 0, 1, 2] (n + 3) ![0, 1, 1, 0] : ℚ) = PP 58 n := ih 58
  have h36 : (f ![0, 0, 1, 2] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 36 n := ih 36
  have h71 : (f ![0, 0, 1, 2] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 71 n := ih 71
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h25, h58, h36, h71, f_dead, pp_46, pp_25, pp_58, pp_36, pp_71]
  try (push_cast; ring)

lemma b_46 : (f ![0, 0, 0, 1] 3 ![0, 0, 1, 0] : ℚ) = PP 46 0 := by
  have h : (f ![0, 0, 0, 1] 3 ![0, 0, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_351
  rw [h, pp_46]; try norm_num

set_option maxRecDepth 100000 in
lemma st_47 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 0, 1] (n + 3 + 1) ![0, 0, 1, 0] : ℚ) = PP 47 (n + 1) := by
  have h26 : (f ![2, 0, 1, 2] (n + 3) ![0, 1, 0, 0] : ℚ) = PP 26 n := ih 26
  have h59 : (f ![2, 0, 1, 2] (n + 3) ![0, 1, 1, 0] : ℚ) = PP 59 n := ih 59
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h26, h59, f_dead, pp_47, pp_26, pp_59]
  try (push_cast; ring)

lemma b_47 : (f ![2, 0, 0, 1] 3 ![0, 0, 1, 0] : ℚ) = PP 47 0 := by
  have h : (f ![2, 0, 0, 1] 3 ![0, 0, 1, 0] : ℚ) = 0 := by exact_mod_cast fv3_353
  rw [h, pp_47]; try norm_num

set_option maxRecDepth 100000 in
lemma st_48 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 0, 1] (n + 3 + 1) ![0, 0, 1, 0] : ℚ) = PP 48 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl20, f_dead, pp_48]
  try (push_cast; ring)

lemma b_48 : (f ![2, 2, 0, 1] 3 ![0, 0, 1, 0] : ℚ) = PP 48 0 := by
  have h : (f ![2, 2, 0, 1] 3 ![0, 0, 1, 0] : ℚ) = 0 := by exact_mod_cast fv3_359
  rw [h, pp_48]; try norm_num

set_option maxRecDepth 100000 in
lemma st_49 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 0] : ℚ) = PP 49 (n + 1) := by
  have h32 : (f ![0, 1, 1, 0] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 32 n := ih 32
  have h65 : (f ![0, 1, 1, 0] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 65 n := ih 65
  have h103 : (f ![0, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 103 n := ih 103
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h32, h65, h103, f_dead, pp_49, pp_32, pp_65, pp_103]
  try (push_cast; ring)

lemma b_49 : (f ![0, 0, 0, 0] 3 ![0, 1, 1, 0] : ℚ) = PP 49 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![0, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_486
  rw [h, pp_49]; try norm_num

set_option maxRecDepth 100000 in
lemma st_50 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 0] : ℚ) = PP 50 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, f_dead, pp_50]
  try (push_cast; ring)

lemma b_50 : (f ![1, 0, 0, 0] 3 ![0, 1, 1, 0] : ℚ) = PP 50 0 := by
  have h : (f ![1, 0, 0, 0] 3 ![0, 1, 1, 0] : ℚ) = 0 := by exact_mod_cast fv3_487
  rw [h, pp_50]; try norm_num

set_option maxRecDepth 100000 in
lemma st_51 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 0] : ℚ) = PP 51 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl20, f_dead, pp_51]
  try (push_cast; ring)

lemma b_51 : (f ![2, 0, 0, 0] 3 ![0, 1, 1, 0] : ℚ) = PP 51 0 := by
  have h : (f ![2, 0, 0, 0] 3 ![0, 1, 1, 0] : ℚ) = 0 := by exact_mod_cast fv3_488
  rw [h, pp_51]; try norm_num

set_option maxRecDepth 100000 in
lemma st_52 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0] (n + 3 + 1) ![0, 1, 1, 0] : ℚ) = PP 52 (n + 1) := by
  have h32 : (f ![0, 1, 1, 0] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 32 n := ih 32
  have h65 : (f ![0, 1, 1, 0] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 65 n := ih 65
  have h103 : (f ![0, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 103 n := ih 103
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h32, h65, h103, f_dead, pp_52, pp_32, pp_65, pp_103]
  try (push_cast; ring)

lemma b_52 : (f ![0, 0, 1, 0] 3 ![0, 1, 1, 0] : ℚ) = PP 52 0 := by
  have h : (f ![0, 0, 1, 0] 3 ![0, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_495
  rw [h, pp_52]; try norm_num

set_option maxRecDepth 100000 in
lemma st_53 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 1, 0] (n + 3 + 1) ![0, 1, 1, 0] : ℚ) = PP 53 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, f_dead, pp_53]
  try (push_cast; ring)

lemma b_53 : (f ![2, 0, 1, 0] 3 ![0, 1, 1, 0] : ℚ) = PP 53 0 := by
  have h : (f ![2, 0, 1, 0] 3 ![0, 1, 1, 0] : ℚ) = 0 := by exact_mod_cast fv3_497
  rw [h, pp_53]; try norm_num

set_option maxRecDepth 100000 in
lemma st_54 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1] (n + 3 + 1) ![0, 1, 1, 0] : ℚ) = PP 54 (n + 1) := by
  have h37 : (f ![0, 1, 1, 2] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 37 n := ih 37
  have h72 : (f ![0, 1, 1, 2] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 72 n := ih 72
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h37, h72, f_dead, pp_54, pp_37, pp_72]
  try (push_cast; ring)

lemma b_54 : (f ![0, 0, 0, 1] 3 ![0, 1, 1, 0] : ℚ) = PP 54 0 := by
  have h : (f ![0, 0, 0, 1] 3 ![0, 1, 1, 0] : ℚ) = 8 := by exact_mod_cast fv3_513
  rw [h, pp_54]; try norm_num

set_option maxRecDepth 100000 in
lemma st_55 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 0, 1] (n + 3 + 1) ![0, 1, 1, 0] : ℚ) = PP 55 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl20, f_dead, pp_55]
  try (push_cast; ring)

lemma b_55 : (f ![2, 0, 0, 1] 3 ![0, 1, 1, 0] : ℚ) = PP 55 0 := by
  have h : (f ![2, 0, 0, 1] 3 ![0, 1, 1, 0] : ℚ) = 0 := by exact_mod_cast fv3_515
  rw [h, pp_55]; try norm_num

set_option maxRecDepth 100000 in
lemma st_56 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 1] (n + 3 + 1) ![0, 1, 1, 0] : ℚ) = PP 56 (n + 1) := by
  have h37 : (f ![0, 1, 1, 2] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 37 n := ih 37
  have h72 : (f ![0, 1, 1, 2] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 72 n := ih 72
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl11, h37, h72, f_dead, pp_56, pp_37, pp_72]
  try (push_cast; ring)

lemma b_56 : (f ![0, 0, 1, 1] 3 ![0, 1, 1, 0] : ℚ) = PP 56 0 := by
  have h : (f ![0, 0, 1, 1] 3 ![0, 1, 1, 0] : ℚ) = 8 := by exact_mod_cast fv3_522
  rw [h, pp_56]; try norm_num

set_option maxRecDepth 100000 in
lemma st_57 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 1, 1] (n + 3 + 1) ![0, 1, 1, 0] : ℚ) = PP 57 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl11, dl20, f_dead, pp_57]
  try (push_cast; ring)

lemma b_57 : (f ![2, 0, 1, 1] 3 ![0, 1, 1, 0] : ℚ) = PP 57 0 := by
  have h : (f ![2, 0, 1, 1] 3 ![0, 1, 1, 0] : ℚ) = 0 := by exact_mod_cast fv3_524
  rw [h, pp_57]; try norm_num

set_option maxRecDepth 100000 in
lemma st_58 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 2] (n + 3 + 1) ![0, 1, 1, 0] : ℚ) = PP 58 (n + 1) := by
  have h37 : (f ![0, 1, 1, 2] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 37 n := ih 37
  have h72 : (f ![0, 1, 1, 2] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 72 n := ih 72
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h37, h72, f_dead, pp_58, pp_37, pp_72]
  try (push_cast; ring)

lemma b_58 : (f ![0, 0, 1, 2] 3 ![0, 1, 1, 0] : ℚ) = PP 58 0 := by
  have h : (f ![0, 0, 1, 2] 3 ![0, 1, 1, 0] : ℚ) = 8 := by exact_mod_cast fv3_549
  rw [h, pp_58]; try norm_num

set_option maxRecDepth 100000 in
lemma st_59 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 1, 2] (n + 3 + 1) ![0, 1, 1, 0] : ℚ) = PP 59 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, dl20, f_dead, pp_59]
  try (push_cast; ring)

lemma b_59 : (f ![2, 0, 1, 2] 3 ![0, 1, 1, 0] : ℚ) = PP 59 0 := by
  have h : (f ![2, 0, 1, 2] 3 ![0, 1, 1, 0] : ℚ) = 0 := by exact_mod_cast fv3_551
  rw [h, pp_59]; try norm_num

set_option maxRecDepth 100000 in
lemma st_60 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 0] : ℚ) = PP 60 (n + 1) := by
  have h33 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 33 n := ih 33
  have h66 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 66 n := ih 66
  have h104 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 104 n := ih 104
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h33, h66, h104, f_dead, pp_60, pp_33, pp_66, pp_104]
  try (push_cast; ring)

lemma b_60 : (f ![0, 0, 0, 0] 3 ![1, 1, 1, 0] : ℚ) = PP 60 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![1, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_567
  rw [h, pp_60]; try norm_num

set_option maxRecDepth 100000 in
lemma st_61 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 0] : ℚ) = PP 61 (n + 1) := by
  have h33 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 33 n := ih 33
  have h66 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 66 n := ih 66
  have h104 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 104 n := ih 104
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h33, h66, h104, f_dead, pp_61, pp_33, pp_66, pp_104]
  try (push_cast; ring)

lemma b_61 : (f ![1, 0, 0, 0] 3 ![1, 1, 1, 0] : ℚ) = PP 61 0 := by
  have h : (f ![1, 0, 0, 0] 3 ![1, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_568
  rw [h, pp_61]; try norm_num

set_option maxRecDepth 100000 in
lemma st_62 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0] (n + 3 + 1) ![1, 1, 1, 0] : ℚ) = PP 62 (n + 1) := by
  have h33 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 33 n := ih 33
  have h66 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 66 n := ih 66
  have h104 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 104 n := ih 104
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h33, h66, h104, f_dead, pp_62, pp_33, pp_66, pp_104]
  try (push_cast; ring)

lemma b_62 : (f ![0, 1, 0, 0] 3 ![1, 1, 1, 0] : ℚ) = PP 62 0 := by
  have h : (f ![0, 1, 0, 0] 3 ![1, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_570
  rw [h, pp_62]; try norm_num

set_option maxRecDepth 100000 in
lemma st_63 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0] (n + 3 + 1) ![1, 1, 1, 0] : ℚ) = PP 63 (n + 1) := by
  have h33 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 33 n := ih 33
  have h66 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 66 n := ih 66
  have h104 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 104 n := ih 104
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h33, h66, h104, f_dead, pp_63, pp_33, pp_66, pp_104]
  try (push_cast; ring)

lemma b_63 : (f ![1, 1, 0, 0] 3 ![1, 1, 1, 0] : ℚ) = PP 63 0 := by
  have h : (f ![1, 1, 0, 0] 3 ![1, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_571
  rw [h, pp_63]; try norm_num

set_option maxRecDepth 100000 in
lemma st_64 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0] (n + 3 + 1) ![1, 1, 1, 0] : ℚ) = PP 64 (n + 1) := by
  have h33 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 33 n := ih 33
  have h66 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 66 n := ih 66
  have h104 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 104 n := ih 104
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h33, h66, h104, f_dead, pp_64, pp_33, pp_66, pp_104]
  try (push_cast; ring)

lemma b_64 : (f ![0, 0, 1, 0] 3 ![1, 1, 1, 0] : ℚ) = PP 64 0 := by
  have h : (f ![0, 0, 1, 0] 3 ![1, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_576
  rw [h, pp_64]; try norm_num

set_option maxRecDepth 100000 in
lemma st_65 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 0] (n + 3 + 1) ![1, 1, 1, 0] : ℚ) = PP 65 (n + 1) := by
  have h33 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 33 n := ih 33
  have h66 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 66 n := ih 66
  have h104 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 104 n := ih 104
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h33, h66, h104, f_dead, pp_65, pp_33, pp_66, pp_104]
  try (push_cast; ring)

lemma b_65 : (f ![0, 1, 1, 0] 3 ![1, 1, 1, 0] : ℚ) = PP 65 0 := by
  have h : (f ![0, 1, 1, 0] 3 ![1, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_579
  rw [h, pp_65]; try norm_num

set_option maxRecDepth 100000 in
lemma st_66 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 0] (n + 3 + 1) ![1, 1, 1, 0] : ℚ) = PP 66 (n + 1) := by
  have h33 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 33 n := ih 33
  have h66 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 66 n := ih 66
  have h104 : (f ![1, 1, 1, 0] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 104 n := ih 104
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl11, h33, h66, h104, f_dead, pp_66, pp_33, pp_66, pp_104]
  try (push_cast; ring)

lemma b_66 : (f ![1, 1, 1, 0] 3 ![1, 1, 1, 0] : ℚ) = PP 66 0 := by
  have h : (f ![1, 1, 1, 0] 3 ![1, 1, 1, 0] : ℚ) = 16 := by exact_mod_cast fv3_580
  rw [h, pp_66]; try norm_num

set_option maxRecDepth 100000 in
lemma st_67 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1] (n + 3 + 1) ![1, 1, 1, 0] : ℚ) = PP 67 (n + 1) := by
  have h38 : (f ![1, 1, 1, 2] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 38 n := ih 38
  have h73 : (f ![1, 1, 1, 2] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 73 n := ih 73
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, h38, h73, f_dead, pp_67, pp_38, pp_73]
  try (push_cast; ring)

lemma b_67 : (f ![0, 0, 0, 1] 3 ![1, 1, 1, 0] : ℚ) = PP 67 0 := by
  have h : (f ![0, 0, 0, 1] 3 ![1, 1, 1, 0] : ℚ) = 8 := by exact_mod_cast fv3_594
  rw [h, pp_67]; try norm_num

set_option maxRecDepth 100000 in
lemma st_68 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 1] (n + 3 + 1) ![1, 1, 1, 0] : ℚ) = PP 68 (n + 1) := by
  have h38 : (f ![1, 1, 1, 2] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 38 n := ih 38
  have h73 : (f ![1, 1, 1, 2] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 73 n := ih 73
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl11, h38, h73, f_dead, pp_68, pp_38, pp_73]
  try (push_cast; ring)

lemma b_68 : (f ![0, 0, 1, 1] 3 ![1, 1, 1, 0] : ℚ) = PP 68 0 := by
  have h : (f ![0, 0, 1, 1] 3 ![1, 1, 1, 0] : ℚ) = 8 := by exact_mod_cast fv3_603
  rw [h, pp_68]; try norm_num

set_option maxRecDepth 100000 in
lemma st_69 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 1] (n + 3 + 1) ![1, 1, 1, 0] : ℚ) = PP 69 (n + 1) := by
  have h38 : (f ![1, 1, 1, 2] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 38 n := ih 38
  have h73 : (f ![1, 1, 1, 2] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 73 n := ih 73
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl11, h38, h73, f_dead, pp_69, pp_38, pp_73]
  try (push_cast; ring)

lemma b_69 : (f ![0, 1, 1, 1] 3 ![1, 1, 1, 0] : ℚ) = PP 69 0 := by
  have h : (f ![0, 1, 1, 1] 3 ![1, 1, 1, 0] : ℚ) = 8 := by exact_mod_cast fv3_606
  rw [h, pp_69]; try norm_num

set_option maxRecDepth 100000 in
lemma st_70 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 1] (n + 3 + 1) ![1, 1, 1, 0] : ℚ) = PP 70 (n + 1) := by
  have h38 : (f ![1, 1, 1, 2] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 38 n := ih 38
  have h73 : (f ![1, 1, 1, 2] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 73 n := ih 73
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl10, dl11, h38, h73, f_dead, pp_70, pp_38, pp_73]
  try (push_cast; ring)

lemma b_70 : (f ![1, 1, 1, 1] 3 ![1, 1, 1, 0] : ℚ) = PP 70 0 := by
  have h : (f ![1, 1, 1, 1] 3 ![1, 1, 1, 0] : ℚ) = 8 := by exact_mod_cast fv3_607
  rw [h, pp_70]; try norm_num

set_option maxRecDepth 100000 in
lemma st_71 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 2] (n + 3 + 1) ![1, 1, 1, 0] : ℚ) = PP 71 (n + 1) := by
  have h38 : (f ![1, 1, 1, 2] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 38 n := ih 38
  have h73 : (f ![1, 1, 1, 2] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 73 n := ih 73
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, dl20, h38, h73, f_dead, pp_71, pp_38, pp_73]
  try (push_cast; ring)

lemma b_71 : (f ![0, 0, 1, 2] 3 ![1, 1, 1, 0] : ℚ) = PP 71 0 := by
  have h : (f ![0, 0, 1, 2] 3 ![1, 1, 1, 0] : ℚ) = 8 := by exact_mod_cast fv3_630
  rw [h, pp_71]; try norm_num

set_option maxRecDepth 100000 in
lemma st_72 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 2] (n + 3 + 1) ![1, 1, 1, 0] : ℚ) = PP 72 (n + 1) := by
  have h38 : (f ![1, 1, 1, 2] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 38 n := ih 38
  have h73 : (f ![1, 1, 1, 2] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 73 n := ih 73
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, dl20, h38, h73, f_dead, pp_72, pp_38, pp_73]
  try (push_cast; ring)

lemma b_72 : (f ![0, 1, 1, 2] 3 ![1, 1, 1, 0] : ℚ) = PP 72 0 := by
  have h : (f ![0, 1, 1, 2] 3 ![1, 1, 1, 0] : ℚ) = 8 := by exact_mod_cast fv3_633
  rw [h, pp_72]; try norm_num

set_option maxRecDepth 100000 in
lemma st_73 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 2] (n + 3 + 1) ![1, 1, 1, 0] : ℚ) = PP 73 (n + 1) := by
  have h38 : (f ![1, 1, 1, 2] (n + 3) ![1, 1, 0, 0] : ℚ) = PP 38 n := ih 38
  have h73 : (f ![1, 1, 1, 2] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 73 n := ih 73
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl11, dl20, h38, h73, f_dead, pp_73, pp_38, pp_73]
  try (push_cast; ring)

lemma b_73 : (f ![1, 1, 1, 2] 3 ![1, 1, 1, 0] : ℚ) = PP 73 0 := by
  have h : (f ![1, 1, 1, 2] 3 ![1, 1, 1, 0] : ℚ) = 8 := by exact_mod_cast fv3_634
  rw [h, pp_73]; try norm_num

set_option maxRecDepth 100000 in
lemma st_74 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 1] : ℚ) = PP 74 (n + 1) := by
  have h46 : (f ![0, 0, 0, 1] (n + 3) ![0, 0, 1, 0] : ℚ) = PP 46 n := ih 46
  have h86 : (f ![0, 0, 0, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 86 n := ih 86
  have h54 : (f ![0, 0, 0, 1] (n + 3) ![0, 1, 1, 0] : ℚ) = PP 54 n := ih 54
  have h94 : (f ![0, 0, 0, 1] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 94 n := ih 94
  have h67 : (f ![0, 0, 0, 1] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 67 n := ih 67
  have h105 : (f ![0, 0, 0, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 105 n := ih 105
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h46, h86, h54, h94, h67, h105, f_dead, pp_74, pp_46, pp_86, pp_54, pp_94, pp_67, pp_105]
  try (push_cast; ring)

lemma b_74 : (f ![0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℚ) = PP 74 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![0, 0, 0, 1] : ℚ) = 32 := by exact_mod_cast fv3_648
  rw [h, pp_74]; try norm_num

set_option maxRecDepth 100000 in
lemma st_75 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 1] : ℚ) = PP 75 (n + 1) := by
  have h47 : (f ![2, 0, 0, 1] (n + 3) ![0, 0, 1, 0] : ℚ) = PP 47 n := ih 47
  have h87 : (f ![2, 0, 0, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 87 n := ih 87
  have h55 : (f ![2, 0, 0, 1] (n + 3) ![0, 1, 1, 0] : ℚ) = PP 55 n := ih 55
  have h95 : (f ![2, 0, 0, 1] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 95 n := ih 95
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h47, h87, h55, h95, f_dead, pp_75, pp_47, pp_87, pp_55, pp_95]
  try (push_cast; ring)

lemma b_75 : (f ![1, 0, 0, 0] 3 ![0, 0, 0, 1] : ℚ) = PP 75 0 := by
  have h : (f ![1, 0, 0, 0] 3 ![0, 0, 0, 1] : ℚ) = 0 := by exact_mod_cast fv3_649
  rw [h, pp_75]; try norm_num

set_option maxRecDepth 100000 in
lemma st_76 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 0, 0] (n + 3 + 1) ![0, 0, 0, 1] : ℚ) = PP 76 (n + 1) := by
  have h47 : (f ![2, 0, 0, 1] (n + 3) ![0, 0, 1, 0] : ℚ) = PP 47 n := ih 47
  have h87 : (f ![2, 0, 0, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 87 n := ih 87
  have h55 : (f ![2, 0, 0, 1] (n + 3) ![0, 1, 1, 0] : ℚ) = PP 55 n := ih 55
  have h95 : (f ![2, 0, 0, 1] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 95 n := ih 95
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl20, h47, h87, h55, h95, f_dead, pp_76, pp_47, pp_87, pp_55, pp_95]
  try (push_cast; ring)

lemma b_76 : (f ![2, 0, 0, 0] 3 ![0, 0, 0, 1] : ℚ) = PP 76 0 := by
  have h : (f ![2, 0, 0, 0] 3 ![0, 0, 0, 1] : ℚ) = 0 := by exact_mod_cast fv3_650
  rw [h, pp_76]; try norm_num

set_option maxRecDepth 100000 in
lemma st_77 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 2, 0, 0] (n + 3 + 1) ![0, 0, 0, 1] : ℚ) = PP 77 (n + 1) := by
  have h48 : (f ![2, 2, 0, 1] (n + 3) ![0, 0, 1, 0] : ℚ) = PP 48 n := ih 48
  have h88 : (f ![2, 2, 0, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 88 n := ih 88
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, dl20, h48, h88, f_dead, pp_77, pp_48, pp_88]
  try (push_cast; ring)

lemma b_77 : (f ![1, 2, 0, 0] 3 ![0, 0, 0, 1] : ℚ) = PP 77 0 := by
  have h : (f ![1, 2, 0, 0] 3 ![0, 0, 0, 1] : ℚ) = 0 := by exact_mod_cast fv3_655
  rw [h, pp_77]; try norm_num

set_option maxRecDepth 100000 in
lemma st_78 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 0, 0] (n + 3 + 1) ![0, 0, 0, 1] : ℚ) = PP 78 (n + 1) := by
  have h48 : (f ![2, 2, 0, 1] (n + 3) ![0, 0, 1, 0] : ℚ) = PP 48 n := ih 48
  have h88 : (f ![2, 2, 0, 1] (n + 3) ![0, 0, 1, 1] : ℚ) = PP 88 n := ih 88
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl20, h48, h88, f_dead, pp_78, pp_48, pp_88]
  try (push_cast; ring)

lemma b_78 : (f ![2, 2, 0, 0] 3 ![0, 0, 0, 1] : ℚ) = PP 78 0 := by
  have h : (f ![2, 2, 0, 0] 3 ![0, 0, 0, 1] : ℚ) = 0 := by exact_mod_cast fv3_656
  rw [h, pp_78]; try norm_num

set_option maxRecDepth 100000 in
lemma st_79 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 2, 2, 0] (n + 3 + 1) ![0, 0, 0, 1] : ℚ) = PP 79 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl20, f_dead, pp_79]
  try (push_cast; ring)

lemma b_79 : (f ![1, 2, 2, 0] 3 ![0, 0, 0, 1] : ℚ) = PP 79 0 := by
  have h : (f ![1, 2, 2, 0] 3 ![0, 0, 0, 1] : ℚ) = 0 := by exact_mod_cast fv3_673
  rw [h, pp_79]; try norm_num

set_option maxRecDepth 100000 in
lemma st_80 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 2, 0] (n + 3 + 1) ![0, 0, 0, 1] : ℚ) = PP 80 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl20, f_dead, pp_80]
  try (push_cast; ring)

lemma b_80 : (f ![2, 2, 2, 0] 3 ![0, 0, 0, 1] : ℚ) = PP 80 0 := by
  have h : (f ![2, 2, 2, 0] 3 ![0, 0, 0, 1] : ℚ) = 0 := by exact_mod_cast fv3_674
  rw [h, pp_80]; try norm_num

set_option maxRecDepth 100000 in
lemma st_81 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![0, 0, 1, 1] : ℚ) = PP 81 (n + 1) := by
  have h56 : (f ![0, 0, 1, 1] (n + 3) ![0, 1, 1, 0] : ℚ) = PP 56 n := ih 56
  have h96 : (f ![0, 0, 1, 1] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 96 n := ih 96
  have h68 : (f ![0, 0, 1, 1] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 68 n := ih 68
  have h106 : (f ![0, 0, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 106 n := ih 106
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h56, h96, h68, h106, f_dead, pp_81, pp_56, pp_96, pp_68, pp_106]
  try (push_cast; ring)

lemma b_81 : (f ![0, 0, 0, 0] 3 ![0, 0, 1, 1] : ℚ) = PP 81 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![0, 0, 1, 1] : ℚ) = 16 := by exact_mod_cast fv3_972
  rw [h, pp_81]; try norm_num

set_option maxRecDepth 100000 in
lemma st_82 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0] (n + 3 + 1) ![0, 0, 1, 1] : ℚ) = PP 82 (n + 1) := by
  have h57 : (f ![2, 0, 1, 1] (n + 3) ![0, 1, 1, 0] : ℚ) = PP 57 n := ih 57
  have h97 : (f ![2, 0, 1, 1] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 97 n := ih 97
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h57, h97, f_dead, pp_82, pp_57, pp_97]
  try (push_cast; ring)

lemma b_82 : (f ![1, 0, 0, 0] 3 ![0, 0, 1, 1] : ℚ) = PP 82 0 := by
  have h : (f ![1, 0, 0, 0] 3 ![0, 0, 1, 1] : ℚ) = 0 := by exact_mod_cast fv3_973
  rw [h, pp_82]; try norm_num

set_option maxRecDepth 100000 in
lemma st_83 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 0, 0] (n + 3 + 1) ![0, 0, 1, 1] : ℚ) = PP 83 (n + 1) := by
  have h57 : (f ![2, 0, 1, 1] (n + 3) ![0, 1, 1, 0] : ℚ) = PP 57 n := ih 57
  have h97 : (f ![2, 0, 1, 1] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 97 n := ih 97
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl20, h57, h97, f_dead, pp_83, pp_57, pp_97]
  try (push_cast; ring)

lemma b_83 : (f ![2, 0, 0, 0] 3 ![0, 0, 1, 1] : ℚ) = PP 83 0 := by
  have h : (f ![2, 0, 0, 0] 3 ![0, 0, 1, 1] : ℚ) = 0 := by exact_mod_cast fv3_974
  rw [h, pp_83]; try norm_num

set_option maxRecDepth 100000 in
lemma st_84 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 2, 0, 0] (n + 3 + 1) ![0, 0, 1, 1] : ℚ) = PP 84 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl20, f_dead, pp_84]
  try (push_cast; ring)

lemma b_84 : (f ![1, 2, 0, 0] 3 ![0, 0, 1, 1] : ℚ) = PP 84 0 := by
  have h : (f ![1, 2, 0, 0] 3 ![0, 0, 1, 1] : ℚ) = 0 := by exact_mod_cast fv3_979
  rw [h, pp_84]; try norm_num

set_option maxRecDepth 100000 in
lemma st_85 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 0, 0] (n + 3 + 1) ![0, 0, 1, 1] : ℚ) = PP 85 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl20, f_dead, pp_85]
  try (push_cast; ring)

lemma b_85 : (f ![2, 2, 0, 0] 3 ![0, 0, 1, 1] : ℚ) = PP 85 0 := by
  have h : (f ![2, 2, 0, 0] 3 ![0, 0, 1, 1] : ℚ) = 0 := by exact_mod_cast fv3_980
  rw [h, pp_85]; try norm_num

set_option maxRecDepth 100000 in
lemma st_86 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1] (n + 3 + 1) ![0, 0, 1, 1] : ℚ) = PP 86 (n + 1) := by
  have h56 : (f ![0, 0, 1, 1] (n + 3) ![0, 1, 1, 0] : ℚ) = PP 56 n := ih 56
  have h96 : (f ![0, 0, 1, 1] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 96 n := ih 96
  have h68 : (f ![0, 0, 1, 1] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 68 n := ih 68
  have h106 : (f ![0, 0, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 106 n := ih 106
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h56, h96, h68, h106, f_dead, pp_86, pp_56, pp_96, pp_68, pp_106]
  try (push_cast; ring)

lemma b_86 : (f ![0, 0, 0, 1] 3 ![0, 0, 1, 1] : ℚ) = PP 86 0 := by
  have h : (f ![0, 0, 0, 1] 3 ![0, 0, 1, 1] : ℚ) = 16 := by exact_mod_cast fv3_999
  rw [h, pp_86]; try norm_num

set_option maxRecDepth 100000 in
lemma st_87 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 0, 1] (n + 3 + 1) ![0, 0, 1, 1] : ℚ) = PP 87 (n + 1) := by
  have h57 : (f ![2, 0, 1, 1] (n + 3) ![0, 1, 1, 0] : ℚ) = PP 57 n := ih 57
  have h97 : (f ![2, 0, 1, 1] (n + 3) ![0, 1, 1, 1] : ℚ) = PP 97 n := ih 97
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, dl20, h57, h97, f_dead, pp_87, pp_57, pp_97]
  try (push_cast; ring)

lemma b_87 : (f ![2, 0, 0, 1] 3 ![0, 0, 1, 1] : ℚ) = PP 87 0 := by
  have h : (f ![2, 0, 0, 1] 3 ![0, 0, 1, 1] : ℚ) = 0 := by exact_mod_cast fv3_1001
  rw [h, pp_87]; try norm_num

set_option maxRecDepth 100000 in
lemma st_88 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 0, 1] (n + 3 + 1) ![0, 0, 1, 1] : ℚ) = PP 88 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, dl20, f_dead, pp_88]
  try (push_cast; ring)

lemma b_88 : (f ![2, 2, 0, 1] 3 ![0, 0, 1, 1] : ℚ) = PP 88 0 := by
  have h : (f ![2, 2, 0, 1] 3 ![0, 0, 1, 1] : ℚ) = 0 := by exact_mod_cast fv3_1007
  rw [h, pp_88]; try norm_num

set_option maxRecDepth 100000 in
lemma st_89 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 1] : ℚ) = PP 89 (n + 1) := by
  have h69 : (f ![0, 1, 1, 1] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 69 n := ih 69
  have h107 : (f ![0, 1, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 107 n := ih 107
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h69, h107, f_dead, pp_89, pp_69, pp_107]
  try (push_cast; ring)

lemma b_89 : (f ![0, 0, 0, 0] 3 ![0, 1, 1, 1] : ℚ) = PP 89 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![0, 1, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1134
  rw [h, pp_89]; try norm_num

set_option maxRecDepth 100000 in
lemma st_90 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 1] : ℚ) = PP 90 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, f_dead, pp_90]
  try (push_cast; ring)

lemma b_90 : (f ![1, 0, 0, 0] 3 ![0, 1, 1, 1] : ℚ) = PP 90 0 := by
  have h : (f ![1, 0, 0, 0] 3 ![0, 1, 1, 1] : ℚ) = 0 := by exact_mod_cast fv3_1135
  rw [h, pp_90]; try norm_num

set_option maxRecDepth 100000 in
lemma st_91 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 0, 0] (n + 3 + 1) ![0, 1, 1, 1] : ℚ) = PP 91 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl20, f_dead, pp_91]
  try (push_cast; ring)

lemma b_91 : (f ![2, 0, 0, 0] 3 ![0, 1, 1, 1] : ℚ) = PP 91 0 := by
  have h : (f ![2, 0, 0, 0] 3 ![0, 1, 1, 1] : ℚ) = 0 := by exact_mod_cast fv3_1136
  rw [h, pp_91]; try norm_num

set_option maxRecDepth 100000 in
lemma st_92 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0] (n + 3 + 1) ![0, 1, 1, 1] : ℚ) = PP 92 (n + 1) := by
  have h69 : (f ![0, 1, 1, 1] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 69 n := ih 69
  have h107 : (f ![0, 1, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 107 n := ih 107
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h69, h107, f_dead, pp_92, pp_69, pp_107]
  try (push_cast; ring)

lemma b_92 : (f ![0, 0, 1, 0] 3 ![0, 1, 1, 1] : ℚ) = PP 92 0 := by
  have h : (f ![0, 0, 1, 0] 3 ![0, 1, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1143
  rw [h, pp_92]; try norm_num

set_option maxRecDepth 100000 in
lemma st_93 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 1, 0] (n + 3 + 1) ![0, 1, 1, 1] : ℚ) = PP 93 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, dl20, f_dead, pp_93]
  try (push_cast; ring)

lemma b_93 : (f ![2, 0, 1, 0] 3 ![0, 1, 1, 1] : ℚ) = PP 93 0 := by
  have h : (f ![2, 0, 1, 0] 3 ![0, 1, 1, 1] : ℚ) = 0 := by exact_mod_cast fv3_1145
  rw [h, pp_93]; try norm_num

set_option maxRecDepth 100000 in
lemma st_94 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1] (n + 3 + 1) ![0, 1, 1, 1] : ℚ) = PP 94 (n + 1) := by
  have h69 : (f ![0, 1, 1, 1] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 69 n := ih 69
  have h107 : (f ![0, 1, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 107 n := ih 107
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h69, h107, f_dead, pp_94, pp_69, pp_107]
  try (push_cast; ring)

lemma b_94 : (f ![0, 0, 0, 1] 3 ![0, 1, 1, 1] : ℚ) = PP 94 0 := by
  have h : (f ![0, 0, 0, 1] 3 ![0, 1, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1161
  rw [h, pp_94]; try norm_num

set_option maxRecDepth 100000 in
lemma st_95 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 0, 1] (n + 3 + 1) ![0, 1, 1, 1] : ℚ) = PP 95 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, dl20, f_dead, pp_95]
  try (push_cast; ring)

lemma b_95 : (f ![2, 0, 0, 1] 3 ![0, 1, 1, 1] : ℚ) = PP 95 0 := by
  have h : (f ![2, 0, 0, 1] 3 ![0, 1, 1, 1] : ℚ) = 0 := by exact_mod_cast fv3_1163
  rw [h, pp_95]; try norm_num

set_option maxRecDepth 100000 in
lemma st_96 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 1] (n + 3 + 1) ![0, 1, 1, 1] : ℚ) = PP 96 (n + 1) := by
  have h69 : (f ![0, 1, 1, 1] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 69 n := ih 69
  have h107 : (f ![0, 1, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 107 n := ih 107
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h69, h107, f_dead, pp_96, pp_69, pp_107]
  try (push_cast; ring)

lemma b_96 : (f ![0, 0, 1, 1] 3 ![0, 1, 1, 1] : ℚ) = PP 96 0 := by
  have h : (f ![0, 0, 1, 1] 3 ![0, 1, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1170
  rw [h, pp_96]; try norm_num

set_option maxRecDepth 100000 in
lemma st_97 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![2, 0, 1, 1] (n + 3 + 1) ![0, 1, 1, 1] : ℚ) = PP 97 (n + 1) := by
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, dl20, f_dead, pp_97]
  try (push_cast; ring)

lemma b_97 : (f ![2, 0, 1, 1] 3 ![0, 1, 1, 1] : ℚ) = PP 97 0 := by
  have h : (f ![2, 0, 1, 1] 3 ![0, 1, 1, 1] : ℚ) = 0 := by exact_mod_cast fv3_1172
  rw [h, pp_97]; try norm_num

set_option maxRecDepth 100000 in
lemma st_98 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 1] : ℚ) = PP 98 (n + 1) := by
  have h70 : (f ![1, 1, 1, 1] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 70 n := ih 70
  have h108 : (f ![1, 1, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 108 n := ih 108
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, h70, h108, f_dead, pp_98, pp_70, pp_108]
  try (push_cast; ring)

lemma b_98 : (f ![0, 0, 0, 0] 3 ![1, 1, 1, 1] : ℚ) = PP 98 0 := by
  have h : (f ![0, 0, 0, 0] 3 ![1, 1, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1215
  rw [h, pp_98]; try norm_num

set_option maxRecDepth 100000 in
lemma st_99 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0] (n + 3 + 1) ![1, 1, 1, 1] : ℚ) = PP 99 (n + 1) := by
  have h70 : (f ![1, 1, 1, 1] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 70 n := ih 70
  have h108 : (f ![1, 1, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 108 n := ih 108
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h70, h108, f_dead, pp_99, pp_70, pp_108]
  try (push_cast; ring)

lemma b_99 : (f ![1, 0, 0, 0] 3 ![1, 1, 1, 1] : ℚ) = PP 99 0 := by
  have h : (f ![1, 0, 0, 0] 3 ![1, 1, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1216
  rw [h, pp_99]; try norm_num

set_option maxRecDepth 100000 in
lemma st_100 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0] (n + 3 + 1) ![1, 1, 1, 1] : ℚ) = PP 100 (n + 1) := by
  have h70 : (f ![1, 1, 1, 1] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 70 n := ih 70
  have h108 : (f ![1, 1, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 108 n := ih 108
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h70, h108, f_dead, pp_100, pp_70, pp_108]
  try (push_cast; ring)

lemma b_100 : (f ![0, 1, 0, 0] 3 ![1, 1, 1, 1] : ℚ) = PP 100 0 := by
  have h : (f ![0, 1, 0, 0] 3 ![1, 1, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1218
  rw [h, pp_100]; try norm_num

set_option maxRecDepth 100000 in
lemma st_101 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0] (n + 3 + 1) ![1, 1, 1, 1] : ℚ) = PP 101 (n + 1) := by
  have h70 : (f ![1, 1, 1, 1] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 70 n := ih 70
  have h108 : (f ![1, 1, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 108 n := ih 108
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h70, h108, f_dead, pp_101, pp_70, pp_108]
  try (push_cast; ring)

lemma b_101 : (f ![1, 1, 0, 0] 3 ![1, 1, 1, 1] : ℚ) = PP 101 0 := by
  have h : (f ![1, 1, 0, 0] 3 ![1, 1, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1219
  rw [h, pp_101]; try norm_num

set_option maxRecDepth 100000 in
lemma st_102 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0] (n + 3 + 1) ![1, 1, 1, 1] : ℚ) = PP 102 (n + 1) := by
  have h70 : (f ![1, 1, 1, 1] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 70 n := ih 70
  have h108 : (f ![1, 1, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 108 n := ih 108
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h70, h108, f_dead, pp_102, pp_70, pp_108]
  try (push_cast; ring)

lemma b_102 : (f ![0, 0, 1, 0] 3 ![1, 1, 1, 1] : ℚ) = PP 102 0 := by
  have h : (f ![0, 0, 1, 0] 3 ![1, 1, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1224
  rw [h, pp_102]; try norm_num

set_option maxRecDepth 100000 in
lemma st_103 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 0] (n + 3 + 1) ![1, 1, 1, 1] : ℚ) = PP 103 (n + 1) := by
  have h70 : (f ![1, 1, 1, 1] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 70 n := ih 70
  have h108 : (f ![1, 1, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 108 n := ih 108
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h70, h108, f_dead, pp_103, pp_70, pp_108]
  try (push_cast; ring)

lemma b_103 : (f ![0, 1, 1, 0] 3 ![1, 1, 1, 1] : ℚ) = PP 103 0 := by
  have h : (f ![0, 1, 1, 0] 3 ![1, 1, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1227
  rw [h, pp_103]; try norm_num

set_option maxRecDepth 100000 in
lemma st_104 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 0] (n + 3 + 1) ![1, 1, 1, 1] : ℚ) = PP 104 (n + 1) := by
  have h70 : (f ![1, 1, 1, 1] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 70 n := ih 70
  have h108 : (f ![1, 1, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 108 n := ih 108
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h70, h108, f_dead, pp_104, pp_70, pp_108]
  try (push_cast; ring)

lemma b_104 : (f ![1, 1, 1, 0] 3 ![1, 1, 1, 1] : ℚ) = PP 104 0 := by
  have h : (f ![1, 1, 1, 0] 3 ![1, 1, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1228
  rw [h, pp_104]; try norm_num

set_option maxRecDepth 100000 in
lemma st_105 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 1] (n + 3 + 1) ![1, 1, 1, 1] : ℚ) = PP 105 (n + 1) := by
  have h70 : (f ![1, 1, 1, 1] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 70 n := ih 70
  have h108 : (f ![1, 1, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 108 n := ih 108
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h70, h108, f_dead, pp_105, pp_70, pp_108]
  try (push_cast; ring)

lemma b_105 : (f ![0, 0, 0, 1] 3 ![1, 1, 1, 1] : ℚ) = PP 105 0 := by
  have h : (f ![0, 0, 0, 1] 3 ![1, 1, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1242
  rw [h, pp_105]; try norm_num

set_option maxRecDepth 100000 in
lemma st_106 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 1] (n + 3 + 1) ![1, 1, 1, 1] : ℚ) = PP 106 (n + 1) := by
  have h70 : (f ![1, 1, 1, 1] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 70 n := ih 70
  have h108 : (f ![1, 1, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 108 n := ih 108
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h70, h108, f_dead, pp_106, pp_70, pp_108]
  try (push_cast; ring)

lemma b_106 : (f ![0, 0, 1, 1] 3 ![1, 1, 1, 1] : ℚ) = PP 106 0 := by
  have h : (f ![0, 0, 1, 1] 3 ![1, 1, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1251
  rw [h, pp_106]; try norm_num

set_option maxRecDepth 100000 in
lemma st_107 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 1] (n + 3 + 1) ![1, 1, 1, 1] : ℚ) = PP 107 (n + 1) := by
  have h70 : (f ![1, 1, 1, 1] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 70 n := ih 70
  have h108 : (f ![1, 1, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 108 n := ih 108
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h70, h108, f_dead, pp_107, pp_70, pp_108]
  try (push_cast; ring)

lemma b_107 : (f ![0, 1, 1, 1] 3 ![1, 1, 1, 1] : ℚ) = PP 107 0 := by
  have h : (f ![0, 1, 1, 1] 3 ![1, 1, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1254
  rw [h, pp_107]; try norm_num

set_option maxRecDepth 100000 in
lemma st_108 (n : ℕ) (ih : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 1] (n + 3 + 1) ![1, 1, 1, 1] : ℚ) = PP 108 (n + 1) := by
  have h70 : (f ![1, 1, 1, 1] (n + 3) ![1, 1, 1, 0] : ℚ) = PP 70 n := ih 70
  have h108 : (f ![1, 1, 1, 1] (n + 3) ![1, 1, 1, 1] : ℚ) = PP 108 n := ih 108
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl11, h70, h108, f_dead, pp_108, pp_70, pp_108]
  try (push_cast; ring)

lemma b_108 : (f ![1, 1, 1, 1] 3 ![1, 1, 1, 1] : ℚ) = PP 108 0 := by
  have h : (f ![1, 1, 1, 1] 3 ![1, 1, 1, 1] : ℚ) = 8 := by exact_mod_cast fv3_1255
  rw [h, pp_108]; try norm_num

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem f_closed (n : ℕ) : ∀ k : Fin 109, (f (cs k) (n + 3) (rs k) : ℚ) = PP k n := by
  induction n with
  | zero =>
    intro k; fin_cases k
    exacts [b_0, b_1, b_2, b_3, b_4, b_5, b_6, b_7, b_8, b_9, b_10, b_11, b_12, b_13, b_14, b_15, b_16, b_17, b_18, b_19, b_20, b_21, b_22, b_23, b_24, b_25, b_26, b_27, b_28, b_29, b_30, b_31, b_32, b_33, b_34, b_35, b_36, b_37, b_38, b_39, b_40, b_41, b_42, b_43, b_44, b_45, b_46, b_47, b_48, b_49, b_50, b_51, b_52, b_53, b_54, b_55, b_56, b_57, b_58, b_59, b_60, b_61, b_62, b_63, b_64, b_65, b_66, b_67, b_68, b_69, b_70, b_71, b_72, b_73, b_74, b_75, b_76, b_77, b_78, b_79, b_80, b_81, b_82, b_83, b_84, b_85, b_86, b_87, b_88, b_89, b_90, b_91, b_92, b_93, b_94, b_95, b_96, b_97, b_98, b_99, b_100, b_101, b_102, b_103, b_104, b_105, b_106, b_107, b_108]
  | succ n ih =>
    intro k; fin_cases k
    exacts [st_0 n ih, st_1 n ih, st_2 n ih, st_3 n ih, st_4 n ih, st_5 n ih, st_6 n ih, st_7 n ih, st_8 n ih, st_9 n ih, st_10 n ih, st_11 n ih, st_12 n ih, st_13 n ih, st_14 n ih, st_15 n ih, st_16 n ih, st_17 n ih, st_18 n ih, st_19 n ih, st_20 n ih, st_21 n ih, st_22 n ih, st_23 n ih, st_24 n ih, st_25 n ih, st_26 n ih, st_27 n ih, st_28 n ih, st_29 n ih, st_30 n ih, st_31 n ih, st_32 n ih, st_33 n ih, st_34 n ih, st_35 n ih, st_36 n ih, st_37 n ih, st_38 n ih, st_39 n ih, st_40 n ih, st_41 n ih, st_42 n ih, st_43 n ih, st_44 n ih, st_45 n ih, st_46 n ih, st_47 n ih, st_48 n ih, st_49 n ih, st_50 n ih, st_51 n ih, st_52 n ih, st_53 n ih, st_54 n ih, st_55 n ih, st_56 n ih, st_57 n ih, st_58 n ih, st_59 n ih, st_60 n ih, st_61 n ih, st_62 n ih, st_63 n ih, st_64 n ih, st_65 n ih, st_66 n ih, st_67 n ih, st_68 n ih, st_69 n ih, st_70 n ih, st_71 n ih, st_72 n ih, st_73 n ih, st_74 n ih, st_75 n ih, st_76 n ih, st_77 n ih, st_78 n ih, st_79 n ih, st_80 n ih, st_81 n ih, st_82 n ih, st_83 n ih, st_84 n ih, st_85 n ih, st_86 n ih, st_87 n ih, st_88 n ih, st_89 n ih, st_90 n ih, st_91 n ih, st_92 n ih, st_93 n ih, st_94 n ih, st_95 n ih, st_96 n ih, st_97 n ih, st_98 n ih, st_99 n ih, st_100 n ih, st_101 n ih, st_102 n ih, st_103 n ih, st_104 n ih, st_105 n ih, st_106 n ih, st_107 n ih, st_108 n ih]

set_option maxRecDepth 100000 in
lemma aBig (m : ℕ) : (a (m + 4) : ℚ) = ((1 : ℚ) / 40320) * (m : ℚ) ^ 8 + ((11 : ℚ) / 10080) * (m : ℚ) ^ 7 + ((5 : ℚ) / 192) * (m : ℚ) ^ 6 + ((73 : ℚ) / 180) * (m : ℚ) ^ 5 + ((2743 : ℚ) / 640) * (m : ℚ) ^ 4 + ((43607 : ℚ) / 1440) * (m : ℚ) ^ 3 + ((291691 : ℚ) / 2016) * (m : ℚ) ^ 2 + ((111807 : ℚ) / 280) * (m : ℚ) ^ 1 + (461 : ℚ) * (m : ℚ) ^ 0 := by
  have g0 : (f ![0, 0, 0, 0] (m + 3) ![0, 0, 0, 0] : ℚ) = PP 0 m := f_closed m 0
  have g74 : (f ![0, 0, 0, 0] (m + 3) ![0, 0, 0, 1] : ℚ) = PP 74 m := f_closed m 74
  have g41 : (f ![0, 0, 0, 0] (m + 3) ![0, 0, 1, 0] : ℚ) = PP 41 m := f_closed m 41
  have g81 : (f ![0, 0, 0, 0] (m + 3) ![0, 0, 1, 1] : ℚ) = PP 81 m := f_closed m 81
  have g20 : (f ![0, 0, 0, 0] (m + 3) ![0, 1, 0, 0] : ℚ) = PP 20 m := f_closed m 20
  have g49 : (f ![0, 0, 0, 0] (m + 3) ![0, 1, 1, 0] : ℚ) = PP 49 m := f_closed m 49
  have g89 : (f ![0, 0, 0, 0] (m + 3) ![0, 1, 1, 1] : ℚ) = PP 89 m := f_closed m 89
  have g9 : (f ![0, 0, 0, 0] (m + 3) ![1, 0, 0, 0] : ℚ) = PP 9 m := f_closed m 9
  have g27 : (f ![0, 0, 0, 0] (m + 3) ![1, 1, 0, 0] : ℚ) = PP 27 m := f_closed m 27
  have g60 : (f ![0, 0, 0, 0] (m + 3) ![1, 1, 1, 0] : ℚ) = PP 60 m := f_closed m 60
  have g98 : (f ![0, 0, 0, 0] (m + 3) ![1, 1, 1, 1] : ℚ) = PP 98 m := f_closed m 98
  rw [show m + 4 = (m + 3) + 1 by omega, a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 4 => (0 : Fin 3)) = ![0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  simp (disch := decide) only [g0, g74, g41, g81, g20, g49, g89, g9, g27, g60, g98, f_dead, Nat.cast_zero]
  simp only [pp_0, pp_74, pp_41, pp_81, pp_20, pp_49, pp_89, pp_9, pp_27, pp_60, pp_98]
  ring

lemma aS1 : (a 1 : ℚ) = 11 := by
  rw [a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 4 => (0 : Fin 3)) = ![0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  simp +decide only [f_zero, Nat.cast_one, Nat.cast_zero, if_true, if_false]
  norm_num

lemma aS2 : (a 2 : ℚ) = 56 := by
  rw [a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 4 => (0 : Fin 3)) = ![0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  have h : ∀ (c : Fin 4 → Fin 3) (r : R), (f c 1 r : ℚ) = ((f c 1 r : ℤ) : ℚ) := fun _ _ => rfl
  simp (disch := decide) only [h, f_dead, Nat.cast_zero, fv1_0, fv1_648, fv1_324, fv1_972, fv1_162, fv1_486, fv1_1134, fv1_81, fv1_243, fv1_567, fv1_1215]
  norm_num

lemma aS3 : (a 3 : ℚ) = 180 := by
  rw [a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 4 => (0 : Fin 3)) = ![0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  have h : ∀ (c : Fin 4 → Fin 3) (r : R), (f c 2 r : ℚ) = ((f c 2 r : ℤ) : ℚ) := fun _ _ => rfl
  simp (disch := decide) only [h, f_dead, Nat.cast_zero, fv2_0, fv2_648, fv2_324, fv2_972, fv2_162, fv2_486, fv2_1134, fv2_81, fv2_243, fv2_567, fv2_1215]
  norm_num

lemma av (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = ((1 : ℚ) / 40320) * (n : ℚ) ^ 8 + ((1 : ℚ) / 3360) * (n : ℚ) ^ 7 + ((19 : ℚ) / 2880) * (n : ℚ) ^ 6 + ((7 : ℚ) / 120) * (n : ℚ) ^ 5 + ((2447 : ℚ) / 5760) * (n : ℚ) ^ 4 + ((259 : ℚ) / 160) * (n : ℚ) ^ 3 + ((126691 : ℚ) / 10080) * (n : ℚ) ^ 2 + ((-12329 : ℚ) / 840) * (n : ℚ) ^ 1 + (13 : ℚ) * (n : ℚ) ^ 0 := by
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n <;> simp only [aS2, aS3] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [aBig]; push_cast; ring

set_option maxHeartbeats 4000000 in
open PowerSeries in
theorem full :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 9 =
      11 - 43 * X + 72 * X ^ 2 - 67 * X ^ 3 + 53 * X ^ 4 - 50 * X ^ 5 + 34 * X ^ 6 - 6 * X ^ 7 - 5 * X ^ 8 + 2 * X ^ 9) ∧
    (∀ n > 10, (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9)) := by
  refine ⟨?_, fun n hn => ?_⟩
  · have hX : (PowerSeries.mk fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 9 =
        C (1 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 0) + C (-9 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 1) + C (36 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 2) + C (-84 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 3) + C (126 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 4) + C (-126 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 5) + C (84 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 6) + C (-36 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 7) + C (9 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 8) + C (-1 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 9) := by
      simp only [map_neg, map_ofNat, map_one, neg_mul, one_mul]; ring
    rw [hX, show (11 - 43 * X + 72 * X ^ 2 - 67 * X ^ 3 + 53 * X ^ 4 - 50 * X ^ 5 + 34 * X ^ 6 - 6 * X ^ 7 - 5 * X ^ 8 + 2 * X ^ 9 : PowerSeries ℚ) =
        C (11 : ℚ) * X ^ 0 + C (-43 : ℚ) * X ^ 1 + C (72 : ℚ) * X ^ 2 + C (-67 : ℚ) * X ^ 3 + C (53 : ℚ) * X ^ 4 + C (-50 : ℚ) * X ^ 5 + C (34 : ℚ) * X ^ 6 + C (-6 : ℚ) * X ^ 7 + C (-5 : ℚ) * X ^ 8 + C (2 : ℚ) * X ^ 9 by
      simp only [map_neg, map_ofNat, pow_zero, mul_one]; ring]
    ext c
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    have e1 : (a 1 : ℚ) = 11 := aS1
    have e2 : (a 2 : ℚ) = 56 := aS2
    have e3 : (a 3 : ℚ) = 180 := aS3
    have e4 : (a 4 : ℚ) = 461 := by rw [av 4 (by norm_num)]; norm_num
    have e5 : (a 5 : ℚ) = 1040 := by rw [av 5 (by norm_num)]; norm_num
    have e6 : (a 6 : ℚ) = 2164 := by rw [av 6 (by norm_num)]; norm_num
    have e7 : (a 7 : ℚ) = 4246 := by rw [av 7 (by norm_num)]; norm_num
    have e8 : (a 8 : ℚ) = 7950 := by rw [av 8 (by norm_num)]; norm_num
    have e9 : (a 9 : ℚ) = 14308 := by rw [av 9 (by norm_num)]; norm_num
    have e10 : (a 10 : ℚ) = 24877 := by rw [av 10 (by norm_num)]; norm_num
    rcases Nat.lt_or_ge c 10 with h | h
    · interval_cases c <;> simp [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, c = m + 10 := ⟨c - 10, by omega⟩
      simp only [show m + 10 - 0 = m + 10 by omega, show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega, show m + 10 - 3 = m + 7 by omega, show m + 10 - 4 = m + 6 by omega, show m + 10 - 5 = m + 5 by omega, show m + 10 - 6 = m + 4 by omega, show m + 10 - 7 = m + 3 by omega, show m + 10 - 8 = m + 2 by omega, show m + 10 - 9 = m + 1 by omega, show 0 ≤ m + 10 by omega, show 1 ≤ m + 10 by omega, show 2 ≤ m + 10 by omega, show 3 ≤ m + 10 by omega, show 4 ≤ m + 10 by omega, show 5 ≤ m + 10 by omega, show 6 ≤ m + 10 by omega, show 7 ≤ m + 10 by omega, show 8 ≤ m + 10 by omega, show 9 ≤ m + 10 by omega, if_true]
      simp only [coeff_C, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, one_ne_zero, and_false, ↓reduceIte, add_zero]
      rw [av (m + 10 + 1) (by omega), av (m + 9 + 1) (by omega), av (m + 8 + 1) (by omega), av (m + 7 + 1) (by omega), av (m + 6 + 1) (by omega), av (m + 5 + 1) (by omega), av (m + 4 + 1) (by omega), av (m + 3 + 1) (by omega), av (m + 2 + 1) (by omega), av (m + 1 + 1) (by omega)]
      push_cast; ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
    simp only [show m + 11 - 1 = m + 10 by omega, show m + 11 - 2 = m + 9 by omega, show m + 11 - 3 = m + 8 by omega, show m + 11 - 4 = m + 7 by omega, show m + 11 - 5 = m + 6 by omega, show m + 11 - 6 = m + 5 by omega, show m + 11 - 7 = m + 4 by omega, show m + 11 - 8 = m + 3 by omega, show m + 11 - 9 = m + 2 by omega]
    qify
    rw [av (m + 11) (by omega), av (m + 10) (by omega), av (m + 9) (by omega), av (m + 8) (by omega), av (m + 7) (by omega), av (m + 6) (by omega), av (m + 5) (by omega), av (m + 4) (by omega), av (m + 3) (by omega), av (m + 2) (by omega)]
    push_cast; ring

end OMA.P_oeis_a223773

theorem OMA.solution : type_of% @OMA.S_oeis_a223773.main := OMA.P_oeis_a223773.full
