import OMAStatements.S_oeis_a224142
import Mathlib

/-!
# oeis-a224142: counting the n X 4 arrays with unimodal and monotone lines

For 0..1 entries, unimodality is recognised by a three-state automaton reading the sequence:
state 0 (no 1 seen yet, `Unimodal`), state 1 (inside the block of 1s, nonincreasing) and state 2
(after the block, all 0). The lemmas `U_cons0`, `U_cons1`, `D_cons0`, `D_cons1`, `Z_cons0` and
`Z_cons1` are its transitions. An array is a list of rows; reading the rows one by one updates the
states of the 4 columns, and the antidiagonal condition links consecutive rows. The number
f(c, n, r) of valid continuations of a top row r by n rows from column states c satisfies a linear
recursion over the next row. For n >= 2 it is an explicit polynomial, checked by induction over the
46 states (c, r) whose top row is allowed, from exact values at n = 1..2. Summing gives a
polynomial for a(n), n >= 1, and the generating function and the recurrence follow from it.

Source: OEIS A224142, https://oeis.org/A224142.
-/
namespace OMA.P_oeis_a224142

open OMA.S_oeis_a224142

def adj (r s : Fin 4 → Fin 2) : Prop := ∀ j : Fin 4, r j ≤ s j

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

def adiagF : List R → ℕ → List (Fin 2)
  | [], _ => []
  | r :: l, j => if h : j < 4 then r ⟨j, h⟩ :: (if j = 0 then [] else adiagF l (j - 1)) else []

lemma adiag_map (l : List R) (j : ℕ) :
    adiagFrom l j = (adiagF l j).map (fun x : Fin 2 => (x : ℕ)) := by
  induction l generalizing j with
  | nil => simp [adiagFrom, adiagF]
  | cons r l ih => unfold adiagFrom adiagF; split_ifs <;> simp [ih]

lemma adiagF_nil (j : ℕ) : adiagF [] j = [] := rfl

lemma ad_cons0 (r : R) (l : List R) : adiagF (r :: l) 0 = [r 0] := by
  simp [adiagF]

lemma ad_cons1 (r : R) (l : List R) : adiagF (r :: l) 1 = r 1 :: adiagF l 0 := by
  simp [adiagF]

lemma ad_cons2 (r : R) (l : List R) : adiagF (r :: l) 2 = r 2 :: adiagF l 1 := by
  simp [adiagF]

lemma ad_cons3 (r : R) (l : List R) : adiagF (r :: l) 3 = r 3 :: adiagF l 2 := by
  simp [adiagF]

lemma forall_drop (P : List R → Prop) (l : List R) :
    (∀ i, P (l.drop i)) ↔ P l ∧ ∀ i, P (l.drop (i + 1)) := by
  constructor
  · intro h; exact ⟨h 0, fun i => h (i + 1)⟩
  · rintro ⟨h0, h⟩ i; cases i with
    | zero => exact h0
    | succ i => exact h i

lemma fdrop (l : List R) : (∀ i, Acc 0 (adiagF (l.drop i) 3) = true) ↔
    Acc 0 (adiagF l 3) = true ∧ ∀ i, Acc 0 (adiagF (l.drop (i + 1)) 3) = true :=
  forall_drop (fun L => Acc 0 (adiagF L 3) = true) l

lemma ltK (P : ℕ → Prop) : (∀ j < 4, P j) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 := by
  constructor
  · intro h; exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num)⟩
  · rintro ⟨h0, h1, h2, h3⟩ j hj
    interval_cases j <;> assumption

lemma rowUni (r : R) : Unimodal (List.ofFn fun j => (r j : ℕ)) ↔ Acc 0 (List.ofFn r) = true := by
  rw [← uniAcc, List.map_ofFn]; rfl

lemma colUni (l : List R) (j : Fin 4) :
    Unimodal (l.map fun r => (r j : ℕ)) ↔ Acc 0 (l.map (· j)) = true := by
  rw [← uniAcc, List.map_map]; rfl

/-- The condition on the first row from line states `c`. -/
def okT (c : Fin 4 → Fin 3) (r : R) : Prop := Acc 0 (List.ofFn r) = true ∧ okb (c 0) (r 0) = true ∧ okb (c 1) (r 1) = true ∧ okb (c 2) (r 2) = true ∧ okb (c 3) (r 3) = true

instance (c : Fin 4 → Fin 3) (r : R) : Decidable (okT c r) := by unfold okT; infer_instance

open Classical

def Q (c : Fin 4 → Fin 3) (l : List R) : Prop :=
  (∀ r ∈ l, Acc 0 (List.ofFn r) = true) ∧ Acc (c 0) (adiagF l 0) = true ∧ Acc (c 1) (adiagF l 1) = true ∧ Acc (c 2) (adiagF l 2) = true ∧ Acc (c 3) (adiagF l 3) = true ∧ (∀ i, Acc 0 (adiagF (l.drop (i + 1)) 3) = true) ∧ l.IsChain adj

lemma chain_true (l : List R) : l.IsChain (fun _ _ => True) := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.isChain_cons]; exact ⟨fun _ _ => trivial, ih⟩

lemma isSol_iff (l : List R) : IsSolution l ↔ Q (fun _ => 0) l := by
  unfold IsSolution Q adj
  rw [show (∀ i, Unimodal (adiagFrom (l.drop i) 3)) ↔ ∀ i, Acc 0 (adiagF (l.drop i) 3) = true by simp only [adiag_map, uniAcc], fdrop]
  simp only [rowUni, adiag_map, uniAcc, ltK, Fin.forall_fin_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, Fin.isValue, IsEmpty.forall_iff, and_true,
    ]
  tauto

lemma Q_single (c : Fin 4 → Fin 3) (r : R) : Q c [r] ↔ okT c r := by
  unfold Q okT
  simp [Acc, adiagF]

lemma Q_cons (c : Fin 4 → Fin 3) (r s : R) (l : List R) :
    Q c (r :: s :: l) ↔ (okT c r ∧ adj r s) ∧ Q ![dl (c 1) (r 1), dl (c 2) (r 2), dl (c 3) (r 3), 0] (s :: l) := by
  unfold Q okT
  simp only [List.mem_cons, forall_eq_or_imp, Acc, Bool.and_eq_true,
    List.isChain_cons_cons, ad_cons0, ad_cons1, ad_cons2, ad_cons3, List.drop_succ_cons, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue]
  rw [fdrop (s :: l)]
  simp only [ad_cons3, Acc, Bool.and_eq_true, Matrix.cons_val_zero, Fin.isValue, okb]
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
    f c (n + 1) r = ∑ s : R, if okT c r ∧ adj r s then f ![dl (c 1) (r 1), dl (c 2) (r 2), dl (c 3) (r 3), 0] n s else 0 := by
  unfold f
  rw [card_cons]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Q_cons]
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
        (f ![dl (c1) (r1), dl (c2) (r2), dl (c3) (r3), 0] n s : ℤ) else 0 := by
  rw [f_succ]; push_cast; rfl

lemma f_succ_q (c0 c1 c2 c3 : Fin 3) (r0 r1 r2 r3 : Fin 2) (n : ℕ) :
    (f ![c0, c1, c2, c3] (n + 1) ![r0, r1, r2, r3] : ℚ) = ∑ s : R,
      if okT ![c0, c1, c2, c3] ![r0, r1, r2, r3] ∧ adj ![r0, r1, r2, r3] s then
        (f ![dl (c1) (r1), dl (c2) (r2), dl (c3) (r3), 0] n s : ℚ) else 0 := by
  rw [f_succ]; push_cast; rfl

lemma fv1_0 : (f ![0, 0, 0, 0] 1 ![0, 0, 0, 0] : ℤ) = 11 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_648 : (f ![0, 0, 0, 0] 1 ![0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_324 : (f ![0, 0, 0, 0] 1 ![0, 0, 1, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_972 : (f ![0, 0, 0, 0] 1 ![0, 0, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_162 : (f ![0, 0, 0, 0] 1 ![0, 1, 0, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_486 : (f ![0, 0, 0, 0] 1 ![0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1134 : (f ![0, 0, 0, 0] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_81 : (f ![0, 0, 0, 0] 1 ![1, 0, 0, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_243 : (f ![0, 0, 0, 0] 1 ![1, 1, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_567 : (f ![0, 0, 0, 0] 1 ![1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1215 : (f ![0, 0, 0, 0] 1 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_657 : (f ![0, 0, 1, 0] 1 ![0, 0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_981 : (f ![0, 0, 1, 0] 1 ![0, 0, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1143 : (f ![0, 0, 1, 0] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1224 : (f ![0, 0, 1, 0] 1 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_327 : (f ![0, 1, 0, 0] 1 ![0, 0, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_975 : (f ![0, 1, 0, 0] 1 ![0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_489 : (f ![0, 1, 0, 0] 1 ![0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1137 : (f ![0, 1, 0, 0] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_570 : (f ![0, 1, 0, 0] 1 ![1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1218 : (f ![0, 1, 0, 0] 1 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_984 : (f ![0, 1, 1, 0] 1 ![0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1146 : (f ![0, 1, 1, 0] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1227 : (f ![0, 1, 1, 0] 1 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_663 : (f ![0, 2, 1, 0] 1 ![0, 0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_987 : (f ![0, 2, 1, 0] 1 ![0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_163 : (f ![1, 0, 0, 0] 1 ![0, 1, 0, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_487 : (f ![1, 0, 0, 0] 1 ![0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1135 : (f ![1, 0, 0, 0] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_244 : (f ![1, 0, 0, 0] 1 ![1, 1, 0, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_568 : (f ![1, 0, 0, 0] 1 ![1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1216 : (f ![1, 0, 0, 0] 1 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_490 : (f ![1, 1, 0, 0] 1 ![0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1138 : (f ![1, 1, 0, 0] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_571 : (f ![1, 1, 0, 0] 1 ![1, 1, 1, 0] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1219 : (f ![1, 1, 0, 0] 1 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1147 : (f ![1, 1, 1, 0] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1228 : (f ![1, 1, 1, 0] 1 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_329 : (f ![2, 1, 0, 0] 1 ![0, 0, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_977 : (f ![2, 1, 0, 0] 1 ![0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_491 : (f ![2, 1, 0, 0] 1 ![0, 1, 1, 0] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1139 : (f ![2, 1, 0, 0] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_986 : (f ![2, 1, 1, 0] 1 ![0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_1148 : (f ![2, 1, 1, 0] 1 ![0, 1, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_665 : (f ![2, 2, 1, 0] 1 ![0, 0, 0, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv1_989 : (f ![2, 2, 1, 0] 1 ![0, 0, 1, 1] : ℤ) = 2 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, f_zero]
  simp +decide only []
  try norm_num

lemma fv2_0 : (f ![0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℤ) = 46 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, fv1_0, fv1_648, fv1_324, fv1_972, fv1_162, fv1_486, fv1_1134, fv1_81, fv1_243, fv1_567, fv1_1215, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_648 : (f ![0, 0, 0, 0] 2 ![0, 0, 0, 1] : ℤ) = 8 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_657, fv1_981, fv1_1143, fv1_1224, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_324 : (f ![0, 0, 0, 0] 2 ![0, 0, 1, 0] : ℤ) = 15 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_327, fv1_975, fv1_489, fv1_1137, fv1_570, fv1_1218, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_972 : (f ![0, 0, 0, 0] 2 ![0, 0, 1, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_984, fv1_1146, fv1_1227, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_162 : (f ![0, 0, 0, 0] 2 ![0, 1, 0, 0] : ℤ) = 18 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_163, fv1_487, fv1_1135, fv1_244, fv1_568, fv1_1216, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_486 : (f ![0, 0, 0, 0] 2 ![0, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_490, fv1_1138, fv1_571, fv1_1219, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1134 : (f ![0, 0, 0, 0] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv1_1147, fv1_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_81 : (f ![0, 0, 0, 0] 2 ![1, 0, 0, 0] : ℤ) = 10 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, fv1_81, fv1_243, fv1_567, fv1_1215, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_243 : (f ![0, 0, 0, 0] 2 ![1, 1, 0, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_244, fv1_568, fv1_1216, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_567 : (f ![0, 0, 0, 0] 2 ![1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_571, fv1_1219, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1215 : (f ![0, 0, 0, 0] 2 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv1_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_657 : (f ![0, 0, 1, 0] 2 ![0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_663, fv1_987, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_981 : (f ![0, 0, 1, 0] 2 ![0, 0, 1, 1] : ℤ) = 5 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_984, fv1_1146, fv1_1227, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1143 : (f ![0, 0, 1, 0] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1147, fv1_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1224 : (f ![0, 0, 1, 0] 2 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_327 : (f ![0, 1, 0, 0] 2 ![0, 0, 1, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_329, fv1_977, fv1_491, fv1_1139, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_975 : (f ![0, 1, 0, 0] 2 ![0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, fv1_986, fv1_1148, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_489 : (f ![0, 1, 0, 0] 2 ![0, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_490, fv1_1138, fv1_571, fv1_1219, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1137 : (f ![0, 1, 0, 0] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1147, fv1_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_570 : (f ![0, 1, 0, 0] 2 ![1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_571, fv1_1219, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1218 : (f ![0, 1, 0, 0] 2 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_984 : (f ![0, 1, 1, 0] 2 ![0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, fv1_986, fv1_1148, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1146 : (f ![0, 1, 1, 0] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1147, fv1_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1227 : (f ![0, 1, 1, 0] 2 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_663 : (f ![0, 2, 1, 0] 2 ![0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, fv1_665, fv1_989, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_987 : (f ![0, 2, 1, 0] 2 ![0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, fv1_986, fv1_1148, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_163 : (f ![1, 0, 0, 0] 2 ![0, 1, 0, 0] : ℤ) = 18 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_163, fv1_487, fv1_1135, fv1_244, fv1_568, fv1_1216, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_487 : (f ![1, 0, 0, 0] 2 ![0, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_490, fv1_1138, fv1_571, fv1_1219, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1135 : (f ![1, 0, 0, 0] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv1_1147, fv1_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_244 : (f ![1, 0, 0, 0] 2 ![1, 1, 0, 0] : ℤ) = 6 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_244, fv1_568, fv1_1216, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_568 : (f ![1, 0, 0, 0] 2 ![1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, fv1_571, fv1_1219, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1216 : (f ![1, 0, 0, 0] 2 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, fv1_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_490 : (f ![1, 1, 0, 0] 2 ![0, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_490, fv1_1138, fv1_571, fv1_1219, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1138 : (f ![1, 1, 0, 0] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1147, fv1_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_571 : (f ![1, 1, 0, 0] 2 ![1, 1, 1, 0] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_571, fv1_1219, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1219 : (f ![1, 1, 0, 0] 2 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1147 : (f ![1, 1, 1, 0] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1147, fv1_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1228 : (f ![1, 1, 1, 0] 2 ![1, 1, 1, 1] : ℤ) = 1 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_329 : (f ![2, 1, 0, 0] 2 ![0, 0, 1, 0] : ℤ) = 12 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl10, fv1_329, fv1_977, fv1_491, fv1_1139, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_977 : (f ![2, 1, 0, 0] 2 ![0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, fv1_986, fv1_1148, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_491 : (f ![2, 1, 0, 0] 2 ![0, 1, 1, 0] : ℤ) = 9 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl00, dl01, dl11, fv1_490, fv1_1138, fv1_571, fv1_1219, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1139 : (f ![2, 1, 0, 0] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1147, fv1_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_986 : (f ![2, 1, 1, 0] 2 ![0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl11, fv1_986, fv1_1148, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_1148 : (f ![2, 1, 1, 0] 2 ![0, 1, 1, 1] : ℤ) = 3 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, fv1_1147, fv1_1228, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_665 : (f ![2, 2, 1, 0] 2 ![0, 0, 0, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl10, dl20, fv1_665, fv1_989, f_dead]
  simp +decide only []
  try norm_num

lemma fv2_989 : (f ![2, 2, 1, 0] 2 ![0, 0, 1, 1] : ℤ) = 4 := by
  rw [f_succ_v, sumk]
  simp (disch := decide) only [Fin.sum_univ_two, dl01, dl11, dl20, fv1_986, fv1_1148, f_dead]
  simp +decide only []
  try norm_num

set_option maxRecDepth 100000 in
def cs : Fin 46 → Fin 4 → Fin 3 := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 1, 0, 0], ![2, 1, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0], ![2, 1, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0], ![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 2, 1, 0], ![2, 2, 1, 0], ![0, 0, 0, 0], ![0, 1, 0, 0], ![2, 1, 0, 0], ![0, 0, 1, 0], ![0, 1, 1, 0], ![2, 1, 1, 0], ![0, 2, 1, 0], ![2, 2, 1, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0], ![2, 1, 0, 0], ![0, 0, 1, 0], ![0, 1, 1, 0], ![1, 1, 1, 0], ![2, 1, 1, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0], ![0, 0, 1, 0], ![0, 1, 1, 0], ![1, 1, 1, 0]]

set_option maxRecDepth 100000 in
def rs : Fin 46 → R := ![![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 1, 0], ![0, 0, 1, 0], ![0, 1, 1, 0], ![0, 1, 1, 0], ![0, 1, 1, 0], ![0, 1, 1, 0], ![0, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 0], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1]]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
def PP : Fin 46 → ℕ → ℚ := ![fun n => ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + (4 : ℚ) * (n : ℚ) ^ 3 + ((62 : ℚ) / 3) * (n : ℚ) ^ 2 + (53 : ℚ) * (n : ℚ) ^ 1 + (46 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (2 : ℚ) * (n : ℚ) ^ 2 + ((47 : ℚ) / 6) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (5 : ℚ) * (n : ℚ) ^ 2 + ((33 : ℚ) / 2) * (n : ℚ) ^ 1 + (18 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (5 : ℚ) * (n : ℚ) ^ 2 + ((33 : ℚ) / 2) * (n : ℚ) ^ 1 + (18 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (6 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (6 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((25 : ℚ) / 2) * (n : ℚ) ^ 1 + (15 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((23 : ℚ) / 2) * (n : ℚ) ^ 1 + (12 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((23 : ℚ) / 2) * (n : ℚ) ^ 1 + (12 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (9 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (9 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (9 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (9 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (9 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((23 : ℚ) / 6) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (5 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (5 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0, fun n => (1 : ℚ) * (n : ℚ) ^ 0]

set_option maxRecDepth 100000 in
lemma pp_0 (n : ℕ) : PP 0 n = ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + (4 : ℚ) * (n : ℚ) ^ 3 + ((62 : ℚ) / 3) * (n : ℚ) ^ 2 + (53 : ℚ) * (n : ℚ) ^ 1 + (46 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_1 (n : ℕ) : PP 1 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (2 : ℚ) * (n : ℚ) ^ 2 + ((47 : ℚ) / 6) * (n : ℚ) ^ 1 + (10 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_2 (n : ℕ) : PP 2 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (5 : ℚ) * (n : ℚ) ^ 2 + ((33 : ℚ) / 2) * (n : ℚ) ^ 1 + (18 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_3 (n : ℕ) : PP 3 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (5 : ℚ) * (n : ℚ) ^ 2 + ((33 : ℚ) / 2) * (n : ℚ) ^ 1 + (18 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_4 (n : ℕ) : PP 4 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (6 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_5 (n : ℕ) : PP 5 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((7 : ℚ) / 2) * (n : ℚ) ^ 1 + (6 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_6 (n : ℕ) : PP 6 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((25 : ℚ) / 2) * (n : ℚ) ^ 1 + (15 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_7 (n : ℕ) : PP 7 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((23 : ℚ) / 2) * (n : ℚ) ^ 1 + (12 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_8 (n : ℕ) : PP 8 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + ((23 : ℚ) / 2) * (n : ℚ) ^ 1 + (12 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_9 (n : ℕ) : PP 9 n = (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (9 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_10 (n : ℕ) : PP 10 n = (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (9 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_11 (n : ℕ) : PP 11 n = (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (9 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_12 (n : ℕ) : PP 12 n = (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (9 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_13 (n : ℕ) : PP 13 n = (1 : ℚ) * (n : ℚ) ^ 2 + (6 : ℚ) * (n : ℚ) ^ 1 + (9 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_14 (n : ℕ) : PP 14 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_15 (n : ℕ) : PP 15 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_16 (n : ℕ) : PP 16 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_17 (n : ℕ) : PP 17 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_18 (n : ℕ) : PP 18 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((23 : ℚ) / 6) * (n : ℚ) ^ 1 + (8 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_19 (n : ℕ) : PP 19 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_20 (n : ℕ) : PP 20 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_21 (n : ℕ) : PP 21 n = ((1 : ℚ) / 6) * (n : ℚ) ^ 3 + (1 : ℚ) * (n : ℚ) ^ 2 + ((17 : ℚ) / 6) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_22 (n : ℕ) : PP 22 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (5 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_23 (n : ℕ) : PP 23 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_24 (n : ℕ) : PP 24 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_25 (n : ℕ) : PP 25 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (5 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_26 (n : ℕ) : PP 26 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_27 (n : ℕ) : PP 27 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_28 (n : ℕ) : PP 28 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_29 (n : ℕ) : PP 29 n = ((1 : ℚ) / 2) * (n : ℚ) ^ 2 + ((5 : ℚ) / 2) * (n : ℚ) ^ 1 + (4 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_30 (n : ℕ) : PP 30 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_31 (n : ℕ) : PP 31 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_32 (n : ℕ) : PP 32 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_33 (n : ℕ) : PP 33 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_34 (n : ℕ) : PP 34 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_35 (n : ℕ) : PP 35 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_36 (n : ℕ) : PP 36 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_37 (n : ℕ) : PP 37 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_38 (n : ℕ) : PP 38 n = (1 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_39 (n : ℕ) : PP 39 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_40 (n : ℕ) : PP 40 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_41 (n : ℕ) : PP 41 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_42 (n : ℕ) : PP 42 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_43 (n : ℕ) : PP 43 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_44 (n : ℕ) : PP 44 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

set_option maxRecDepth 100000 in
lemma pp_45 (n : ℕ) : PP 45 n = (1 : ℚ) * (n : ℚ) ^ 0 := rfl

lemma st_0 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 2 + 1) ![0, 0, 0, 0] : ℚ) = PP 0 (n + 1) := by
  have h0 : (f ![0, 0, 0, 0] (n + 2) ![0, 0, 0, 0] : ℚ) = PP 0 n := ih 0
  have h18 : (f ![0, 0, 0, 0] (n + 2) ![0, 0, 0, 1] : ℚ) = PP 18 n := ih 18
  have h6 : (f ![0, 0, 0, 0] (n + 2) ![0, 0, 1, 0] : ℚ) = PP 6 n := ih 6
  have h22 : (f ![0, 0, 0, 0] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 22 n := ih 22
  have h2 : (f ![0, 0, 0, 0] (n + 2) ![0, 1, 0, 0] : ℚ) = PP 2 n := ih 2
  have h9 : (f ![0, 0, 0, 0] (n + 2) ![0, 1, 1, 0] : ℚ) = PP 9 n := ih 9
  have h30 : (f ![0, 0, 0, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 30 n := ih 30
  have h1 : (f ![0, 0, 0, 0] (n + 2) ![1, 0, 0, 0] : ℚ) = PP 1 n := ih 1
  have h4 : (f ![0, 0, 0, 0] (n + 2) ![1, 1, 0, 0] : ℚ) = PP 4 n := ih 4
  have h14 : (f ![0, 0, 0, 0] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 14 n := ih 14
  have h39 : (f ![0, 0, 0, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 39 n := ih 39
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, h0, h18, h6, h22, h2, h9, h30, h1, h4, h14, h39, f_dead, pp_0, pp_0, pp_18, pp_6, pp_22, pp_2, pp_9, pp_30, pp_1, pp_4, pp_14, pp_39]
  try (push_cast; ring)

lemma b_0 : (f ![0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℚ) = PP 0 0 := by
  have h : (f ![0, 0, 0, 0] 2 ![0, 0, 0, 0] : ℚ) = 46 := by exact_mod_cast fv2_0
  rw [h, pp_0]; try norm_num

lemma st_1 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 2 + 1) ![1, 0, 0, 0] : ℚ) = PP 1 (n + 1) := by
  have h1 : (f ![0, 0, 0, 0] (n + 2) ![1, 0, 0, 0] : ℚ) = PP 1 n := ih 1
  have h4 : (f ![0, 0, 0, 0] (n + 2) ![1, 1, 0, 0] : ℚ) = PP 4 n := ih 4
  have h14 : (f ![0, 0, 0, 0] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 14 n := ih 14
  have h39 : (f ![0, 0, 0, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 39 n := ih 39
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, h1, h4, h14, h39, f_dead, pp_1, pp_1, pp_4, pp_14, pp_39]
  try (push_cast; ring)

lemma b_1 : (f ![0, 0, 0, 0] 2 ![1, 0, 0, 0] : ℚ) = PP 1 0 := by
  have h : (f ![0, 0, 0, 0] 2 ![1, 0, 0, 0] : ℚ) = 10 := by exact_mod_cast fv2_81
  rw [h, pp_1]; try norm_num

lemma st_2 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 2 + 1) ![0, 1, 0, 0] : ℚ) = PP 2 (n + 1) := by
  have h3 : (f ![1, 0, 0, 0] (n + 2) ![0, 1, 0, 0] : ℚ) = PP 3 n := ih 3
  have h10 : (f ![1, 0, 0, 0] (n + 2) ![0, 1, 1, 0] : ℚ) = PP 10 n := ih 10
  have h31 : (f ![1, 0, 0, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 31 n := ih 31
  have h5 : (f ![1, 0, 0, 0] (n + 2) ![1, 1, 0, 0] : ℚ) = PP 5 n := ih 5
  have h15 : (f ![1, 0, 0, 0] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 15 n := ih 15
  have h40 : (f ![1, 0, 0, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 40 n := ih 40
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h3, h10, h31, h5, h15, h40, f_dead, pp_2, pp_3, pp_10, pp_31, pp_5, pp_15, pp_40]
  try (push_cast; ring)

lemma b_2 : (f ![0, 0, 0, 0] 2 ![0, 1, 0, 0] : ℚ) = PP 2 0 := by
  have h : (f ![0, 0, 0, 0] 2 ![0, 1, 0, 0] : ℚ) = 18 := by exact_mod_cast fv2_162
  rw [h, pp_2]; try norm_num

lemma st_3 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0] (n + 2 + 1) ![0, 1, 0, 0] : ℚ) = PP 3 (n + 1) := by
  have h3 : (f ![1, 0, 0, 0] (n + 2) ![0, 1, 0, 0] : ℚ) = PP 3 n := ih 3
  have h10 : (f ![1, 0, 0, 0] (n + 2) ![0, 1, 1, 0] : ℚ) = PP 10 n := ih 10
  have h31 : (f ![1, 0, 0, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 31 n := ih 31
  have h5 : (f ![1, 0, 0, 0] (n + 2) ![1, 1, 0, 0] : ℚ) = PP 5 n := ih 5
  have h15 : (f ![1, 0, 0, 0] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 15 n := ih 15
  have h40 : (f ![1, 0, 0, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 40 n := ih 40
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h3, h10, h31, h5, h15, h40, f_dead, pp_3, pp_3, pp_10, pp_31, pp_5, pp_15, pp_40]
  try (push_cast; ring)

lemma b_3 : (f ![1, 0, 0, 0] 2 ![0, 1, 0, 0] : ℚ) = PP 3 0 := by
  have h : (f ![1, 0, 0, 0] 2 ![0, 1, 0, 0] : ℚ) = 18 := by exact_mod_cast fv2_163
  rw [h, pp_3]; try norm_num

lemma st_4 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 2 + 1) ![1, 1, 0, 0] : ℚ) = PP 4 (n + 1) := by
  have h5 : (f ![1, 0, 0, 0] (n + 2) ![1, 1, 0, 0] : ℚ) = PP 5 n := ih 5
  have h15 : (f ![1, 0, 0, 0] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 15 n := ih 15
  have h40 : (f ![1, 0, 0, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 40 n := ih 40
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h5, h15, h40, f_dead, pp_4, pp_5, pp_15, pp_40]
  try (push_cast; ring)

lemma b_4 : (f ![0, 0, 0, 0] 2 ![1, 1, 0, 0] : ℚ) = PP 4 0 := by
  have h : (f ![0, 0, 0, 0] 2 ![1, 1, 0, 0] : ℚ) = 6 := by exact_mod_cast fv2_243
  rw [h, pp_4]; try norm_num

lemma st_5 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0] (n + 2 + 1) ![1, 1, 0, 0] : ℚ) = PP 5 (n + 1) := by
  have h5 : (f ![1, 0, 0, 0] (n + 2) ![1, 1, 0, 0] : ℚ) = PP 5 n := ih 5
  have h15 : (f ![1, 0, 0, 0] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 15 n := ih 15
  have h40 : (f ![1, 0, 0, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 40 n := ih 40
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h5, h15, h40, f_dead, pp_5, pp_5, pp_15, pp_40]
  try (push_cast; ring)

lemma b_5 : (f ![1, 0, 0, 0] 2 ![1, 1, 0, 0] : ℚ) = PP 5 0 := by
  have h : (f ![1, 0, 0, 0] 2 ![1, 1, 0, 0] : ℚ) = 6 := by exact_mod_cast fv2_244
  rw [h, pp_5]; try norm_num

lemma st_6 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 2 + 1) ![0, 0, 1, 0] : ℚ) = PP 6 (n + 1) := by
  have h7 : (f ![0, 1, 0, 0] (n + 2) ![0, 0, 1, 0] : ℚ) = PP 7 n := ih 7
  have h23 : (f ![0, 1, 0, 0] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 23 n := ih 23
  have h11 : (f ![0, 1, 0, 0] (n + 2) ![0, 1, 1, 0] : ℚ) = PP 11 n := ih 11
  have h32 : (f ![0, 1, 0, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 32 n := ih 32
  have h16 : (f ![0, 1, 0, 0] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 16 n := ih 16
  have h41 : (f ![0, 1, 0, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 41 n := ih 41
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h7, h23, h11, h32, h16, h41, f_dead, pp_6, pp_7, pp_23, pp_11, pp_32, pp_16, pp_41]
  try (push_cast; ring)

lemma b_6 : (f ![0, 0, 0, 0] 2 ![0, 0, 1, 0] : ℚ) = PP 6 0 := by
  have h : (f ![0, 0, 0, 0] 2 ![0, 0, 1, 0] : ℚ) = 15 := by exact_mod_cast fv2_324
  rw [h, pp_6]; try norm_num

lemma st_7 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0] (n + 2 + 1) ![0, 0, 1, 0] : ℚ) = PP 7 (n + 1) := by
  have h8 : (f ![2, 1, 0, 0] (n + 2) ![0, 0, 1, 0] : ℚ) = PP 8 n := ih 8
  have h24 : (f ![2, 1, 0, 0] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 24 n := ih 24
  have h13 : (f ![2, 1, 0, 0] (n + 2) ![0, 1, 1, 0] : ℚ) = PP 13 n := ih 13
  have h34 : (f ![2, 1, 0, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 34 n := ih 34
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h8, h24, h13, h34, f_dead, pp_7, pp_8, pp_24, pp_13, pp_34]
  try (push_cast; ring)

lemma b_7 : (f ![0, 1, 0, 0] 2 ![0, 0, 1, 0] : ℚ) = PP 7 0 := by
  have h : (f ![0, 1, 0, 0] 2 ![0, 0, 1, 0] : ℚ) = 12 := by exact_mod_cast fv2_327
  rw [h, pp_7]; try norm_num

lemma st_8 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 0, 0] (n + 2 + 1) ![0, 0, 1, 0] : ℚ) = PP 8 (n + 1) := by
  have h8 : (f ![2, 1, 0, 0] (n + 2) ![0, 0, 1, 0] : ℚ) = PP 8 n := ih 8
  have h24 : (f ![2, 1, 0, 0] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 24 n := ih 24
  have h13 : (f ![2, 1, 0, 0] (n + 2) ![0, 1, 1, 0] : ℚ) = PP 13 n := ih 13
  have h34 : (f ![2, 1, 0, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 34 n := ih 34
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h8, h24, h13, h34, f_dead, pp_8, pp_8, pp_24, pp_13, pp_34]
  try (push_cast; ring)

lemma b_8 : (f ![2, 1, 0, 0] 2 ![0, 0, 1, 0] : ℚ) = PP 8 0 := by
  have h : (f ![2, 1, 0, 0] 2 ![0, 0, 1, 0] : ℚ) = 12 := by exact_mod_cast fv2_329
  rw [h, pp_8]; try norm_num

lemma st_9 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 2 + 1) ![0, 1, 1, 0] : ℚ) = PP 9 (n + 1) := by
  have h12 : (f ![1, 1, 0, 0] (n + 2) ![0, 1, 1, 0] : ℚ) = PP 12 n := ih 12
  have h33 : (f ![1, 1, 0, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 33 n := ih 33
  have h17 : (f ![1, 1, 0, 0] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 17 n := ih 17
  have h42 : (f ![1, 1, 0, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 42 n := ih 42
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h12, h33, h17, h42, f_dead, pp_9, pp_12, pp_33, pp_17, pp_42]
  try (push_cast; ring)

lemma b_9 : (f ![0, 0, 0, 0] 2 ![0, 1, 1, 0] : ℚ) = PP 9 0 := by
  have h : (f ![0, 0, 0, 0] 2 ![0, 1, 1, 0] : ℚ) = 9 := by exact_mod_cast fv2_486
  rw [h, pp_9]; try norm_num

lemma st_10 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0] (n + 2 + 1) ![0, 1, 1, 0] : ℚ) = PP 10 (n + 1) := by
  have h12 : (f ![1, 1, 0, 0] (n + 2) ![0, 1, 1, 0] : ℚ) = PP 12 n := ih 12
  have h33 : (f ![1, 1, 0, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 33 n := ih 33
  have h17 : (f ![1, 1, 0, 0] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 17 n := ih 17
  have h42 : (f ![1, 1, 0, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 42 n := ih 42
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h12, h33, h17, h42, f_dead, pp_10, pp_12, pp_33, pp_17, pp_42]
  try (push_cast; ring)

lemma b_10 : (f ![1, 0, 0, 0] 2 ![0, 1, 1, 0] : ℚ) = PP 10 0 := by
  have h : (f ![1, 0, 0, 0] 2 ![0, 1, 1, 0] : ℚ) = 9 := by exact_mod_cast fv2_487
  rw [h, pp_10]; try norm_num

lemma st_11 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0] (n + 2 + 1) ![0, 1, 1, 0] : ℚ) = PP 11 (n + 1) := by
  have h12 : (f ![1, 1, 0, 0] (n + 2) ![0, 1, 1, 0] : ℚ) = PP 12 n := ih 12
  have h33 : (f ![1, 1, 0, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 33 n := ih 33
  have h17 : (f ![1, 1, 0, 0] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 17 n := ih 17
  have h42 : (f ![1, 1, 0, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 42 n := ih 42
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h12, h33, h17, h42, f_dead, pp_11, pp_12, pp_33, pp_17, pp_42]
  try (push_cast; ring)

lemma b_11 : (f ![0, 1, 0, 0] 2 ![0, 1, 1, 0] : ℚ) = PP 11 0 := by
  have h : (f ![0, 1, 0, 0] 2 ![0, 1, 1, 0] : ℚ) = 9 := by exact_mod_cast fv2_489
  rw [h, pp_11]; try norm_num

lemma st_12 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0] (n + 2 + 1) ![0, 1, 1, 0] : ℚ) = PP 12 (n + 1) := by
  have h12 : (f ![1, 1, 0, 0] (n + 2) ![0, 1, 1, 0] : ℚ) = PP 12 n := ih 12
  have h33 : (f ![1, 1, 0, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 33 n := ih 33
  have h17 : (f ![1, 1, 0, 0] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 17 n := ih 17
  have h42 : (f ![1, 1, 0, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 42 n := ih 42
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h12, h33, h17, h42, f_dead, pp_12, pp_12, pp_33, pp_17, pp_42]
  try (push_cast; ring)

lemma b_12 : (f ![1, 1, 0, 0] 2 ![0, 1, 1, 0] : ℚ) = PP 12 0 := by
  have h : (f ![1, 1, 0, 0] 2 ![0, 1, 1, 0] : ℚ) = 9 := by exact_mod_cast fv2_490
  rw [h, pp_12]; try norm_num

lemma st_13 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 0, 0] (n + 2 + 1) ![0, 1, 1, 0] : ℚ) = PP 13 (n + 1) := by
  have h12 : (f ![1, 1, 0, 0] (n + 2) ![0, 1, 1, 0] : ℚ) = PP 12 n := ih 12
  have h33 : (f ![1, 1, 0, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 33 n := ih 33
  have h17 : (f ![1, 1, 0, 0] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 17 n := ih 17
  have h42 : (f ![1, 1, 0, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 42 n := ih 42
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h12, h33, h17, h42, f_dead, pp_13, pp_12, pp_33, pp_17, pp_42]
  try (push_cast; ring)

lemma b_13 : (f ![2, 1, 0, 0] 2 ![0, 1, 1, 0] : ℚ) = PP 13 0 := by
  have h : (f ![2, 1, 0, 0] 2 ![0, 1, 1, 0] : ℚ) = 9 := by exact_mod_cast fv2_491
  rw [h, pp_13]; try norm_num

lemma st_14 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 2 + 1) ![1, 1, 1, 0] : ℚ) = PP 14 (n + 1) := by
  have h17 : (f ![1, 1, 0, 0] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 17 n := ih 17
  have h42 : (f ![1, 1, 0, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 42 n := ih 42
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h17, h42, f_dead, pp_14, pp_17, pp_42]
  try (push_cast; ring)

lemma b_14 : (f ![0, 0, 0, 0] 2 ![1, 1, 1, 0] : ℚ) = PP 14 0 := by
  have h : (f ![0, 0, 0, 0] 2 ![1, 1, 1, 0] : ℚ) = 3 := by exact_mod_cast fv2_567
  rw [h, pp_14]; try norm_num

lemma st_15 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0] (n + 2 + 1) ![1, 1, 1, 0] : ℚ) = PP 15 (n + 1) := by
  have h17 : (f ![1, 1, 0, 0] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 17 n := ih 17
  have h42 : (f ![1, 1, 0, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 42 n := ih 42
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h17, h42, f_dead, pp_15, pp_17, pp_42]
  try (push_cast; ring)

lemma b_15 : (f ![1, 0, 0, 0] 2 ![1, 1, 1, 0] : ℚ) = PP 15 0 := by
  have h : (f ![1, 0, 0, 0] 2 ![1, 1, 1, 0] : ℚ) = 3 := by exact_mod_cast fv2_568
  rw [h, pp_15]; try norm_num

lemma st_16 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0] (n + 2 + 1) ![1, 1, 1, 0] : ℚ) = PP 16 (n + 1) := by
  have h17 : (f ![1, 1, 0, 0] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 17 n := ih 17
  have h42 : (f ![1, 1, 0, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 42 n := ih 42
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h17, h42, f_dead, pp_16, pp_17, pp_42]
  try (push_cast; ring)

lemma b_16 : (f ![0, 1, 0, 0] 2 ![1, 1, 1, 0] : ℚ) = PP 16 0 := by
  have h : (f ![0, 1, 0, 0] 2 ![1, 1, 1, 0] : ℚ) = 3 := by exact_mod_cast fv2_570
  rw [h, pp_16]; try norm_num

lemma st_17 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0] (n + 2 + 1) ![1, 1, 1, 0] : ℚ) = PP 17 (n + 1) := by
  have h17 : (f ![1, 1, 0, 0] (n + 2) ![1, 1, 1, 0] : ℚ) = PP 17 n := ih 17
  have h42 : (f ![1, 1, 0, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 42 n := ih 42
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h17, h42, f_dead, pp_17, pp_17, pp_42]
  try (push_cast; ring)

lemma b_17 : (f ![1, 1, 0, 0] 2 ![1, 1, 1, 0] : ℚ) = PP 17 0 := by
  have h : (f ![1, 1, 0, 0] 2 ![1, 1, 1, 0] : ℚ) = 3 := by exact_mod_cast fv2_571
  rw [h, pp_17]; try norm_num

lemma st_18 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 2 + 1) ![0, 0, 0, 1] : ℚ) = PP 18 (n + 1) := by
  have h19 : (f ![0, 0, 1, 0] (n + 2) ![0, 0, 0, 1] : ℚ) = PP 19 n := ih 19
  have h25 : (f ![0, 0, 1, 0] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 25 n := ih 25
  have h35 : (f ![0, 0, 1, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 35 n := ih 35
  have h43 : (f ![0, 0, 1, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 43 n := ih 43
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h19, h25, h35, h43, f_dead, pp_18, pp_19, pp_25, pp_35, pp_43]
  try (push_cast; ring)

lemma b_18 : (f ![0, 0, 0, 0] 2 ![0, 0, 0, 1] : ℚ) = PP 18 0 := by
  have h : (f ![0, 0, 0, 0] 2 ![0, 0, 0, 1] : ℚ) = 8 := by exact_mod_cast fv2_648
  rw [h, pp_18]; try norm_num

lemma st_19 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0] (n + 2 + 1) ![0, 0, 0, 1] : ℚ) = PP 19 (n + 1) := by
  have h20 : (f ![0, 2, 1, 0] (n + 2) ![0, 0, 0, 1] : ℚ) = PP 20 n := ih 20
  have h28 : (f ![0, 2, 1, 0] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 28 n := ih 28
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl10, h20, h28, f_dead, pp_19, pp_20, pp_28]
  try (push_cast; ring)

lemma b_19 : (f ![0, 0, 1, 0] 2 ![0, 0, 0, 1] : ℚ) = PP 19 0 := by
  have h : (f ![0, 0, 1, 0] 2 ![0, 0, 0, 1] : ℚ) = 4 := by exact_mod_cast fv2_657
  rw [h, pp_19]; try norm_num

lemma st_20 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 0] (n + 2 + 1) ![0, 0, 0, 1] : ℚ) = PP 20 (n + 1) := by
  have h21 : (f ![2, 2, 1, 0] (n + 2) ![0, 0, 0, 1] : ℚ) = PP 21 n := ih 21
  have h29 : (f ![2, 2, 1, 0] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 29 n := ih 29
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl20, h21, h29, f_dead, pp_20, pp_21, pp_29]
  try (push_cast; ring)

lemma b_20 : (f ![0, 2, 1, 0] 2 ![0, 0, 0, 1] : ℚ) = PP 20 0 := by
  have h : (f ![0, 2, 1, 0] 2 ![0, 0, 0, 1] : ℚ) = 4 := by exact_mod_cast fv2_663
  rw [h, pp_20]; try norm_num

lemma st_21 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 0] (n + 2 + 1) ![0, 0, 0, 1] : ℚ) = PP 21 (n + 1) := by
  have h21 : (f ![2, 2, 1, 0] (n + 2) ![0, 0, 0, 1] : ℚ) = PP 21 n := ih 21
  have h29 : (f ![2, 2, 1, 0] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 29 n := ih 29
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl20, h21, h29, f_dead, pp_21, pp_21, pp_29]
  try (push_cast; ring)

lemma b_21 : (f ![2, 2, 1, 0] 2 ![0, 0, 0, 1] : ℚ) = PP 21 0 := by
  have h : (f ![2, 2, 1, 0] 2 ![0, 0, 0, 1] : ℚ) = 4 := by exact_mod_cast fv2_665
  rw [h, pp_21]; try norm_num

lemma st_22 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 2 + 1) ![0, 0, 1, 1] : ℚ) = PP 22 (n + 1) := by
  have h26 : (f ![0, 1, 1, 0] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 26 n := ih 26
  have h36 : (f ![0, 1, 1, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 36 n := ih 36
  have h44 : (f ![0, 1, 1, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 44 n := ih 44
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, h26, h36, h44, f_dead, pp_22, pp_26, pp_36, pp_44]
  try (push_cast; ring)

lemma b_22 : (f ![0, 0, 0, 0] 2 ![0, 0, 1, 1] : ℚ) = PP 22 0 := by
  have h : (f ![0, 0, 0, 0] 2 ![0, 0, 1, 1] : ℚ) = 5 := by exact_mod_cast fv2_972
  rw [h, pp_22]; try norm_num

lemma st_23 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0] (n + 2 + 1) ![0, 0, 1, 1] : ℚ) = PP 23 (n + 1) := by
  have h27 : (f ![2, 1, 1, 0] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 27 n := ih 27
  have h38 : (f ![2, 1, 1, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 38 n := ih 38
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, h27, h38, f_dead, pp_23, pp_27, pp_38]
  try (push_cast; ring)

lemma b_23 : (f ![0, 1, 0, 0] 2 ![0, 0, 1, 1] : ℚ) = PP 23 0 := by
  have h : (f ![0, 1, 0, 0] 2 ![0, 0, 1, 1] : ℚ) = 4 := by exact_mod_cast fv2_975
  rw [h, pp_23]; try norm_num

lemma st_24 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 0, 0] (n + 2 + 1) ![0, 0, 1, 1] : ℚ) = PP 24 (n + 1) := by
  have h27 : (f ![2, 1, 1, 0] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 27 n := ih 27
  have h38 : (f ![2, 1, 1, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 38 n := ih 38
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, h27, h38, f_dead, pp_24, pp_27, pp_38]
  try (push_cast; ring)

lemma b_24 : (f ![2, 1, 0, 0] 2 ![0, 0, 1, 1] : ℚ) = PP 24 0 := by
  have h : (f ![2, 1, 0, 0] 2 ![0, 0, 1, 1] : ℚ) = 4 := by exact_mod_cast fv2_977
  rw [h, pp_24]; try norm_num

lemma st_25 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0] (n + 2 + 1) ![0, 0, 1, 1] : ℚ) = PP 25 (n + 1) := by
  have h26 : (f ![0, 1, 1, 0] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 26 n := ih 26
  have h36 : (f ![0, 1, 1, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 36 n := ih 36
  have h44 : (f ![0, 1, 1, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 44 n := ih 44
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl00, dl01, dl11, h26, h36, h44, f_dead, pp_25, pp_26, pp_36, pp_44]
  try (push_cast; ring)

lemma b_25 : (f ![0, 0, 1, 0] 2 ![0, 0, 1, 1] : ℚ) = PP 25 0 := by
  have h : (f ![0, 0, 1, 0] 2 ![0, 0, 1, 1] : ℚ) = 5 := by exact_mod_cast fv2_981
  rw [h, pp_25]; try norm_num

lemma st_26 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 0] (n + 2 + 1) ![0, 0, 1, 1] : ℚ) = PP 26 (n + 1) := by
  have h27 : (f ![2, 1, 1, 0] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 27 n := ih 27
  have h38 : (f ![2, 1, 1, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 38 n := ih 38
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl11, h27, h38, f_dead, pp_26, pp_27, pp_38]
  try (push_cast; ring)

lemma b_26 : (f ![0, 1, 1, 0] 2 ![0, 0, 1, 1] : ℚ) = PP 26 0 := by
  have h : (f ![0, 1, 1, 0] 2 ![0, 0, 1, 1] : ℚ) = 4 := by exact_mod_cast fv2_984
  rw [h, pp_26]; try norm_num

lemma st_27 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 1, 0] (n + 2 + 1) ![0, 0, 1, 1] : ℚ) = PP 27 (n + 1) := by
  have h27 : (f ![2, 1, 1, 0] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 27 n := ih 27
  have h38 : (f ![2, 1, 1, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 38 n := ih 38
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl10, dl11, h27, h38, f_dead, pp_27, pp_27, pp_38]
  try (push_cast; ring)

lemma b_27 : (f ![2, 1, 1, 0] 2 ![0, 0, 1, 1] : ℚ) = PP 27 0 := by
  have h : (f ![2, 1, 1, 0] 2 ![0, 0, 1, 1] : ℚ) = 4 := by exact_mod_cast fv2_986
  rw [h, pp_27]; try norm_num

lemma st_28 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 2, 1, 0] (n + 2 + 1) ![0, 0, 1, 1] : ℚ) = PP 28 (n + 1) := by
  have h27 : (f ![2, 1, 1, 0] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 27 n := ih 27
  have h38 : (f ![2, 1, 1, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 38 n := ih 38
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, dl20, h27, h38, f_dead, pp_28, pp_27, pp_38]
  try (push_cast; ring)

lemma b_28 : (f ![0, 2, 1, 0] 2 ![0, 0, 1, 1] : ℚ) = PP 28 0 := by
  have h : (f ![0, 2, 1, 0] 2 ![0, 0, 1, 1] : ℚ) = 4 := by exact_mod_cast fv2_987
  rw [h, pp_28]; try norm_num

lemma st_29 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![2, 2, 1, 0] (n + 2 + 1) ![0, 0, 1, 1] : ℚ) = PP 29 (n + 1) := by
  have h27 : (f ![2, 1, 1, 0] (n + 2) ![0, 0, 1, 1] : ℚ) = PP 27 n := ih 27
  have h38 : (f ![2, 1, 1, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 38 n := ih 38
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, dl20, h27, h38, f_dead, pp_29, pp_27, pp_38]
  try (push_cast; ring)

lemma b_29 : (f ![2, 2, 1, 0] 2 ![0, 0, 1, 1] : ℚ) = PP 29 0 := by
  have h : (f ![2, 2, 1, 0] 2 ![0, 0, 1, 1] : ℚ) = 4 := by exact_mod_cast fv2_989
  rw [h, pp_29]; try norm_num

lemma st_30 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 2 + 1) ![0, 1, 1, 1] : ℚ) = PP 30 (n + 1) := by
  have h37 : (f ![1, 1, 1, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 37 n := ih 37
  have h45 : (f ![1, 1, 1, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, h37, h45, f_dead, pp_30, pp_37, pp_45]
  try (push_cast; ring)

lemma b_30 : (f ![0, 0, 0, 0] 2 ![0, 1, 1, 1] : ℚ) = PP 30 0 := by
  have h : (f ![0, 0, 0, 0] 2 ![0, 1, 1, 1] : ℚ) = 3 := by exact_mod_cast fv2_1134
  rw [h, pp_30]; try norm_num

lemma st_31 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0] (n + 2 + 1) ![0, 1, 1, 1] : ℚ) = PP 31 (n + 1) := by
  have h37 : (f ![1, 1, 1, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 37 n := ih 37
  have h45 : (f ![1, 1, 1, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, h37, h45, f_dead, pp_31, pp_37, pp_45]
  try (push_cast; ring)

lemma b_31 : (f ![1, 0, 0, 0] 2 ![0, 1, 1, 1] : ℚ) = PP 31 0 := by
  have h : (f ![1, 0, 0, 0] 2 ![0, 1, 1, 1] : ℚ) = 3 := by exact_mod_cast fv2_1135
  rw [h, pp_31]; try norm_num

lemma st_32 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0] (n + 2 + 1) ![0, 1, 1, 1] : ℚ) = PP 32 (n + 1) := by
  have h37 : (f ![1, 1, 1, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 37 n := ih 37
  have h45 : (f ![1, 1, 1, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h37, h45, f_dead, pp_32, pp_37, pp_45]
  try (push_cast; ring)

lemma b_32 : (f ![0, 1, 0, 0] 2 ![0, 1, 1, 1] : ℚ) = PP 32 0 := by
  have h : (f ![0, 1, 0, 0] 2 ![0, 1, 1, 1] : ℚ) = 3 := by exact_mod_cast fv2_1137
  rw [h, pp_32]; try norm_num

lemma st_33 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0] (n + 2 + 1) ![0, 1, 1, 1] : ℚ) = PP 33 (n + 1) := by
  have h37 : (f ![1, 1, 1, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 37 n := ih 37
  have h45 : (f ![1, 1, 1, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h37, h45, f_dead, pp_33, pp_37, pp_45]
  try (push_cast; ring)

lemma b_33 : (f ![1, 1, 0, 0] 2 ![0, 1, 1, 1] : ℚ) = PP 33 0 := by
  have h : (f ![1, 1, 0, 0] 2 ![0, 1, 1, 1] : ℚ) = 3 := by exact_mod_cast fv2_1138
  rw [h, pp_33]; try norm_num

lemma st_34 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 0, 0] (n + 2 + 1) ![0, 1, 1, 1] : ℚ) = PP 34 (n + 1) := by
  have h37 : (f ![1, 1, 1, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 37 n := ih 37
  have h45 : (f ![1, 1, 1, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h37, h45, f_dead, pp_34, pp_37, pp_45]
  try (push_cast; ring)

lemma b_34 : (f ![2, 1, 0, 0] 2 ![0, 1, 1, 1] : ℚ) = PP 34 0 := by
  have h : (f ![2, 1, 0, 0] 2 ![0, 1, 1, 1] : ℚ) = 3 := by exact_mod_cast fv2_1139
  rw [h, pp_34]; try norm_num

lemma st_35 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0] (n + 2 + 1) ![0, 1, 1, 1] : ℚ) = PP 35 (n + 1) := by
  have h37 : (f ![1, 1, 1, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 37 n := ih 37
  have h45 : (f ![1, 1, 1, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h37, h45, f_dead, pp_35, pp_37, pp_45]
  try (push_cast; ring)

lemma b_35 : (f ![0, 0, 1, 0] 2 ![0, 1, 1, 1] : ℚ) = PP 35 0 := by
  have h : (f ![0, 0, 1, 0] 2 ![0, 1, 1, 1] : ℚ) = 3 := by exact_mod_cast fv2_1143
  rw [h, pp_35]; try norm_num

lemma st_36 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 0] (n + 2 + 1) ![0, 1, 1, 1] : ℚ) = PP 36 (n + 1) := by
  have h37 : (f ![1, 1, 1, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 37 n := ih 37
  have h45 : (f ![1, 1, 1, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h37, h45, f_dead, pp_36, pp_37, pp_45]
  try (push_cast; ring)

lemma b_36 : (f ![0, 1, 1, 0] 2 ![0, 1, 1, 1] : ℚ) = PP 36 0 := by
  have h : (f ![0, 1, 1, 0] 2 ![0, 1, 1, 1] : ℚ) = 3 := by exact_mod_cast fv2_1146
  rw [h, pp_36]; try norm_num

lemma st_37 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 0] (n + 2 + 1) ![0, 1, 1, 1] : ℚ) = PP 37 (n + 1) := by
  have h37 : (f ![1, 1, 1, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 37 n := ih 37
  have h45 : (f ![1, 1, 1, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h37, h45, f_dead, pp_37, pp_37, pp_45]
  try (push_cast; ring)

lemma b_37 : (f ![1, 1, 1, 0] 2 ![0, 1, 1, 1] : ℚ) = PP 37 0 := by
  have h : (f ![1, 1, 1, 0] 2 ![0, 1, 1, 1] : ℚ) = 3 := by exact_mod_cast fv2_1147
  rw [h, pp_37]; try norm_num

lemma st_38 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![2, 1, 1, 0] (n + 2 + 1) ![0, 1, 1, 1] : ℚ) = PP 38 (n + 1) := by
  have h37 : (f ![1, 1, 1, 0] (n + 2) ![0, 1, 1, 1] : ℚ) = PP 37 n := ih 37
  have h45 : (f ![1, 1, 1, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h37, h45, f_dead, pp_38, pp_37, pp_45]
  try (push_cast; ring)

lemma b_38 : (f ![2, 1, 1, 0] 2 ![0, 1, 1, 1] : ℚ) = PP 38 0 := by
  have h : (f ![2, 1, 1, 0] 2 ![0, 1, 1, 1] : ℚ) = 3 := by exact_mod_cast fv2_1148
  rw [h, pp_38]; try norm_num

lemma st_39 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 0, 0] (n + 2 + 1) ![1, 1, 1, 1] : ℚ) = PP 39 (n + 1) := by
  have h45 : (f ![1, 1, 1, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, h45, f_dead, pp_39, pp_45]
  try (push_cast; ring)

lemma b_39 : (f ![0, 0, 0, 0] 2 ![1, 1, 1, 1] : ℚ) = PP 39 0 := by
  have h : (f ![0, 0, 0, 0] 2 ![1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv2_1215
  rw [h, pp_39]; try norm_num

lemma st_40 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 0, 0, 0] (n + 2 + 1) ![1, 1, 1, 1] : ℚ) = PP 40 (n + 1) := by
  have h45 : (f ![1, 1, 1, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, h45, f_dead, pp_40, pp_45]
  try (push_cast; ring)

lemma b_40 : (f ![1, 0, 0, 0] 2 ![1, 1, 1, 1] : ℚ) = PP 40 0 := by
  have h : (f ![1, 0, 0, 0] 2 ![1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv2_1216
  rw [h, pp_40]; try norm_num

lemma st_41 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 0, 0] (n + 2 + 1) ![1, 1, 1, 1] : ℚ) = PP 41 (n + 1) := by
  have h45 : (f ![1, 1, 1, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h45, f_dead, pp_41, pp_45]
  try (push_cast; ring)

lemma b_41 : (f ![0, 1, 0, 0] 2 ![1, 1, 1, 1] : ℚ) = PP 41 0 := by
  have h : (f ![0, 1, 0, 0] 2 ![1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv2_1218
  rw [h, pp_41]; try norm_num

lemma st_42 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 0, 0] (n + 2 + 1) ![1, 1, 1, 1] : ℚ) = PP 42 (n + 1) := by
  have h45 : (f ![1, 1, 1, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h45, f_dead, pp_42, pp_45]
  try (push_cast; ring)

lemma b_42 : (f ![1, 1, 0, 0] 2 ![1, 1, 1, 1] : ℚ) = PP 42 0 := by
  have h : (f ![1, 1, 0, 0] 2 ![1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv2_1219
  rw [h, pp_42]; try norm_num

lemma st_43 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 0, 1, 0] (n + 2 + 1) ![1, 1, 1, 1] : ℚ) = PP 43 (n + 1) := by
  have h45 : (f ![1, 1, 1, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h45, f_dead, pp_43, pp_45]
  try (push_cast; ring)

lemma b_43 : (f ![0, 0, 1, 0] 2 ![1, 1, 1, 1] : ℚ) = PP 43 0 := by
  have h : (f ![0, 0, 1, 0] 2 ![1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv2_1224
  rw [h, pp_43]; try norm_num

lemma st_44 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![0, 1, 1, 0] (n + 2 + 1) ![1, 1, 1, 1] : ℚ) = PP 44 (n + 1) := by
  have h45 : (f ![1, 1, 1, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h45, f_dead, pp_44, pp_45]
  try (push_cast; ring)

lemma b_44 : (f ![0, 1, 1, 0] 2 ![1, 1, 1, 1] : ℚ) = PP 44 0 := by
  have h : (f ![0, 1, 1, 0] 2 ![1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv2_1227
  rw [h, pp_44]; try norm_num

lemma st_45 (n : ℕ) (ih : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n) :
    (f ![1, 1, 1, 0] (n + 2 + 1) ![1, 1, 1, 1] : ℚ) = PP 45 (n + 1) := by
  have h45 : (f ![1, 1, 1, 0] (n + 2) ![1, 1, 1, 1] : ℚ) = PP 45 n := ih 45
  rw [f_succ_q, sumk]
  simp +decide only [Fin.sum_univ_two, adj]
  simp (disch := decide) only [dl01, dl11, h45, f_dead, pp_45, pp_45]
  try (push_cast; ring)

lemma b_45 : (f ![1, 1, 1, 0] 2 ![1, 1, 1, 1] : ℚ) = PP 45 0 := by
  have h : (f ![1, 1, 1, 0] 2 ![1, 1, 1, 1] : ℚ) = 1 := by exact_mod_cast fv2_1228
  rw [h, pp_45]; try norm_num

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem f_closed (n : ℕ) : ∀ k : Fin 46, (f (cs k) (n + 2) (rs k) : ℚ) = PP k n := by
  induction n with
  | zero =>
    intro k; fin_cases k
    exacts [b_0, b_1, b_2, b_3, b_4, b_5, b_6, b_7, b_8, b_9, b_10, b_11, b_12, b_13, b_14, b_15, b_16, b_17, b_18, b_19, b_20, b_21, b_22, b_23, b_24, b_25, b_26, b_27, b_28, b_29, b_30, b_31, b_32, b_33, b_34, b_35, b_36, b_37, b_38, b_39, b_40, b_41, b_42, b_43, b_44, b_45]
  | succ n ih =>
    intro k; fin_cases k
    exacts [st_0 n ih, st_1 n ih, st_2 n ih, st_3 n ih, st_4 n ih, st_5 n ih, st_6 n ih, st_7 n ih, st_8 n ih, st_9 n ih, st_10 n ih, st_11 n ih, st_12 n ih, st_13 n ih, st_14 n ih, st_15 n ih, st_16 n ih, st_17 n ih, st_18 n ih, st_19 n ih, st_20 n ih, st_21 n ih, st_22 n ih, st_23 n ih, st_24 n ih, st_25 n ih, st_26 n ih, st_27 n ih, st_28 n ih, st_29 n ih, st_30 n ih, st_31 n ih, st_32 n ih, st_33 n ih, st_34 n ih, st_35 n ih, st_36 n ih, st_37 n ih, st_38 n ih, st_39 n ih, st_40 n ih, st_41 n ih, st_42 n ih, st_43 n ih, st_44 n ih, st_45 n ih]

lemma aBig (m : ℕ) : (a (m + 3) : ℚ) = ((1 : ℚ) / 3) * (m : ℚ) ^ 4 + ((16 : ℚ) / 3) * (m : ℚ) ^ 3 + ((104 : ℚ) / 3) * (m : ℚ) ^ 2 + ((323 : ℚ) / 3) * (m : ℚ) ^ 1 + (124 : ℚ) * (m : ℚ) ^ 0 := by
  have g0 : (f ![0, 0, 0, 0] (m + 2) ![0, 0, 0, 0] : ℚ) = PP 0 m := f_closed m 0
  have g18 : (f ![0, 0, 0, 0] (m + 2) ![0, 0, 0, 1] : ℚ) = PP 18 m := f_closed m 18
  have g6 : (f ![0, 0, 0, 0] (m + 2) ![0, 0, 1, 0] : ℚ) = PP 6 m := f_closed m 6
  have g22 : (f ![0, 0, 0, 0] (m + 2) ![0, 0, 1, 1] : ℚ) = PP 22 m := f_closed m 22
  have g2 : (f ![0, 0, 0, 0] (m + 2) ![0, 1, 0, 0] : ℚ) = PP 2 m := f_closed m 2
  have g9 : (f ![0, 0, 0, 0] (m + 2) ![0, 1, 1, 0] : ℚ) = PP 9 m := f_closed m 9
  have g30 : (f ![0, 0, 0, 0] (m + 2) ![0, 1, 1, 1] : ℚ) = PP 30 m := f_closed m 30
  have g1 : (f ![0, 0, 0, 0] (m + 2) ![1, 0, 0, 0] : ℚ) = PP 1 m := f_closed m 1
  have g4 : (f ![0, 0, 0, 0] (m + 2) ![1, 1, 0, 0] : ℚ) = PP 4 m := f_closed m 4
  have g14 : (f ![0, 0, 0, 0] (m + 2) ![1, 1, 1, 0] : ℚ) = PP 14 m := f_closed m 14
  have g39 : (f ![0, 0, 0, 0] (m + 2) ![1, 1, 1, 1] : ℚ) = PP 39 m := f_closed m 39
  rw [show m + 3 = (m + 2) + 1 by omega, a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 4 => (0 : Fin 3)) = ![0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  simp (disch := decide) only [g0, g18, g6, g22, g2, g9, g30, g1, g4, g14, g39, f_dead, Nat.cast_zero]
  simp only [pp_0, pp_18, pp_6, pp_22, pp_2, pp_9, pp_30, pp_1, pp_4, pp_14, pp_39]
  ring

lemma aS1 : (a 1 : ℚ) = 11 := by
  rw [a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 4 => (0 : Fin 3)) = ![0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  simp +decide only [f_zero, Nat.cast_one, Nat.cast_zero, if_true, if_false]
  norm_num

lemma aS2 : (a 2 : ℚ) = 46 := by
  rw [a_succ]; push_cast; rw [sumk]; simp only [Fin.sum_univ_two]
  have hz : (fun _ : Fin 4 => (0 : Fin 3)) = ![0, 0, 0, 0] := by ext j; fin_cases j <;> rfl
  rw [hz]
  have h : ∀ (c : Fin 4 → Fin 3) (r : R), (f c 1 r : ℚ) = ((f c 1 r : ℤ) : ℚ) := fun _ _ => rfl
  simp (disch := decide) only [h, f_dead, Nat.cast_zero, fv1_0, fv1_648, fv1_324, fv1_972, fv1_162, fv1_486, fv1_1134, fv1_81, fv1_243, fv1_567, fv1_1215]
  norm_num

lemma av (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = ((1 : ℚ) / 3) * (n : ℚ) ^ 4 + ((4 : ℚ) / 3) * (n : ℚ) ^ 3 + ((14 : ℚ) / 3) * (n : ℚ) ^ 2 + ((23 : ℚ) / 3) * (n : ℚ) ^ 1 + (-4 : ℚ) * (n : ℚ) ^ 0 := by
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> simp only [aS2] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [aBig]; push_cast; ring

set_option maxHeartbeats 4000000 in
open PowerSeries in
theorem full :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 5 =
      11 - 9 * X + 4 * X ^ 2 + 2 * X ^ 3 + X ^ 4 - X ^ 5) ∧
    (∀ n > 6, (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)) := by
  refine ⟨?_, fun n hn => ?_⟩
  · have hX : (PowerSeries.mk fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 5 =
        C (1 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 0) + C (-5 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 1) + C (10 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 2) + C (-10 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 3) + C (5 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 4) + C (-1 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 5) := by
      simp only [map_neg, map_ofNat, map_one, neg_mul, one_mul]; ring
    rw [hX, show (11 - 9 * X + 4 * X ^ 2 + 2 * X ^ 3 + X ^ 4 - X ^ 5 : PowerSeries ℚ) =
        C (11 : ℚ) * X ^ 0 + C (-9 : ℚ) * X ^ 1 + C (4 : ℚ) * X ^ 2 + C (2 : ℚ) * X ^ 3 + C (1 : ℚ) * X ^ 4 + C (-1 : ℚ) * X ^ 5 by
      simp only [map_neg, map_ofNat, map_one, pow_zero, mul_one, one_mul]; ring]
    ext c
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    have e1 : (a 1 : ℚ) = 11 := aS1
    have e2 : (a 2 : ℚ) = 46 := aS2
    have e3 : (a 3 : ℚ) = 124 := by rw [av 3 (by norm_num)]; norm_num
    have e4 : (a 4 : ℚ) = 272 := by rw [av 4 (by norm_num)]; norm_num
    have e5 : (a 5 : ℚ) = 526 := by rw [av 5 (by norm_num)]; norm_num
    have e6 : (a 6 : ℚ) = 930 := by rw [av 6 (by norm_num)]; norm_num
    rcases Nat.lt_or_ge c 6 with h | h
    · interval_cases c <;> simp [e1, e2, e3, e4, e5, e6] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, c = m + 6 := ⟨c - 6, by omega⟩
      simp only [show m + 6 - 0 = m + 6 by omega, show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega, show 0 ≤ m + 6 by omega, show 1 ≤ m + 6 by omega, show 2 ≤ m + 6 by omega, show 3 ≤ m + 6 by omega, show 4 ≤ m + 6 by omega, show 5 ≤ m + 6 by omega, if_true]
      simp only [coeff_C, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, one_ne_zero, and_false, ↓reduceIte, add_zero]
      rw [av (m + 6 + 1) (by omega), av (m + 5 + 1) (by omega), av (m + 4 + 1) (by omega), av (m + 3 + 1) (by omega), av (m + 2 + 1) (by omega), av (m + 1 + 1) (by omega)]
      push_cast; ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    simp only [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega, show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega, show m + 7 - 5 = m + 2 by omega]
    qify
    rw [av (m + 7) (by omega), av (m + 6) (by omega), av (m + 5) (by omega), av (m + 4) (by omega), av (m + 3) (by omega), av (m + 2) (by omega)]
    push_cast; ring

end OMA.P_oeis_a224142

theorem OMA.solution : type_of% @OMA.S_oeis_a224142.main := OMA.P_oeis_a224142.full
