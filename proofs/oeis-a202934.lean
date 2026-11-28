import OMAStatements.S_oeis_a202934
import Mathlib

/-!
Proof of Barker's conjectures for A202934 ((n+3) X 6 binary arrays whose rows and columns have
nondecreasing consecutive windows of four bits).

A line has nondecreasing windows iff every 1 at a position i with i + 4 < L is followed by four
1s (windowsOK_iff934, then windowsOK_ofFn). A row of width 6 is good iff a 1 in column 0 forces
columns 1..4 and a 1 in column 1 forces columns 2..5 (18 such rows). Putting a row r on top of an
array X with m rows only adds the first window pair of each column, which exists iff m ≥ 4. The
state of an array is the set of columns whose first four entries (padded with 1s) are 1; V m T
counts valid arrays with m rows and state T. For m < 4 the state of the new array is r ∩ S, and for
m ≥ 4 it is r, with S ⊇ r required. On codes 0..63 these steps are Psi934 and Phi934. The tables
tv934 (m ≤ 4) and tw934 (j ≤ 6) satisfy Psi934 (tv m) = tv (m+1), tw 0 = tv 4 and
Phi934 (tw j) = tw j + tw (j+1), tw 7 = 0 (kernel checks), so V (m + 4) = Sum_j C(m, j) tw j and
a (n + 1) = 104976 + 48898 n + 23086 C(n,2) + 9925 C(n,3) + 3014 C(n,4) + 468 C(n,5) + 24 C(n,6).
The recurrence and the generating function follow.
-/

namespace OMA.Helpers

open OMA.S_oeis_a202934 Finset

/-- A row of the array (6 entries), or a set of columns given by its indicator. -/
abbrev Row934 := Fin 6 → Bool

/-- Two consecutive windows of four bits: the first is at most the second iff a leading 1
forces the next four bits to be 1. -/
theorem win_le_iff934 (c0 c1 c2 c3 c4 : Bool) :
    8 * c0.toNat + 4 * c1.toNat + 2 * c2.toNat + c3.toNat ≤
      8 * c1.toNat + 4 * c2.toNat + 2 * c3.toNat + c4.toNat ↔
    (c0 = true → c1 = true ∧ c2 = true ∧ c3 = true ∧ c4 = true) := by
  revert c0 c1 c2 c3 c4
  decide

/-- The window condition at position i of a padded line f. -/
def Q934 (f : ℕ → Bool) (i : ℕ) : Prop :=
  f i = true → f (i + 1) = true ∧ f (i + 2) = true ∧ f (i + 3) = true ∧ f (i + 4) = true

theorem windowsOK_iff934 : ∀ l : List Bool,
    windowsOK l = true ↔ ∀ i, i + 4 < l.length → Q934 (fun k => l.getD k true) i
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => by
    have ih := windowsOK_iff934 (b1 :: b2 :: b3 :: b4 :: rest)
    rw [windowsOK, Bool.and_eq_true, decide_eq_true_iff, ih]
    constructor
    · rintro ⟨h0, h⟩ i hi
      cases i with
      | zero => exact (win_le_iff934 b0 b1 b2 b3 b4).mp h0
      | succ k => exact h k (by simp only [List.length_cons] at hi ⊢; omega)
    · intro h
      refine ⟨(win_le_iff934 b0 b1 b2 b3 b4).mpr (h 0 (by simp)), fun k hk => h (k + 1) ?_⟩
      simp only [List.length_cons] at hk ⊢
      omega
  | [] => by simp [windowsOK]
  | [_] => by simp [windowsOK]
  | [_, _] => by simp [windowsOK]
  | [_, _, _] => by simp [windowsOK]
  | [_, _, _, _] => by simp [windowsOK]

/-- The entries of a line, padded with true beyond its end. -/
def pb934 {L : ℕ} (line : Fin L → Bool) (k : ℕ) : Bool := if h : k < L then line ⟨k, h⟩ else true

theorem pb934_of_lt {L : ℕ} (line : Fin L → Bool) (k : ℕ) (h : k < L) :
    pb934 line k = line ⟨k, h⟩ := dif_pos h

theorem pb934_of_ge {L : ℕ} (line : Fin L → Bool) (k : ℕ) (h : L ≤ k) : pb934 line k = true :=
  dif_neg (by omega)

theorem getD_ofFn934 {L : ℕ} (line : Fin L → Bool) (k : ℕ) :
    (List.ofFn line).getD k true = pb934 line k := by
  by_cases h : k < L
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn, pb934_of_lt _ _ h]
  · rw [List.getD_eq_default _ _ (by simp; omega), pb934_of_ge _ _ (by omega)]

/-- A line has nondecreasing windows (padded form). -/
def LineQ {L : ℕ} (line : Fin L → Bool) : Prop := ∀ i, i + 4 < L → Q934 (pb934 line) i

theorem windowsOK_ofFn {L : ℕ} (line : Fin L → Bool) :
    windowsOK (List.ofFn line) = true ↔ LineQ line := by
  rw [windowsOK_iff934, List.length_ofFn]
  unfold LineQ
  have e : (fun k => (List.ofFn line).getD k true) = pb934 line := funext (getD_ofFn934 line)
  rw [e]

/-- Put a bit in front of a padded line. -/
def consF934 (x : Bool) (f : ℕ → Bool) : ℕ → Bool
  | 0 => x
  | k + 1 => f k

theorem pb934_cons {L : ℕ} (x : Bool) (u : Fin L → Bool) :
    pb934 (Fin.cons x u : Fin (L + 1) → Bool) = consF934 x (pb934 u) := by
  funext k
  cases k with
  | zero => simp [pb934, consF934]
  | succ k =>
    show pb934 (Fin.cons x u : Fin (L + 1) → Bool) (k + 1) = pb934 u k
    by_cases h : k < L
    · rw [pb934_of_lt _ _ (by omega), pb934_of_lt _ _ h]
      show (Fin.cons x u : Fin (L + 1) → Bool) (Fin.succ ⟨k, h⟩) = u ⟨k, h⟩
      rw [Fin.cons_succ]
    · rw [pb934_of_ge _ _ (by omega), pb934_of_ge _ _ (by omega)]

theorem LineQ_cons {L : ℕ} (x : Bool) (u : Fin L → Bool) :
    LineQ (Fin.cons x u : Fin (L + 1) → Bool) ↔
      (4 ≤ L → Q934 (consF934 x (pb934 u)) 0) ∧ LineQ u := by
  unfold LineQ
  rw [pb934_cons]
  constructor
  · intro h
    exact ⟨fun _ => h 0 (by omega), fun i hi => h (i + 1) (by omega)⟩
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => exact h0 (by omega)
    | succ k => exact h k (by omega)

/-- A row of width 6 has nondecreasing windows iff a 1 in column 0 forces columns 1..4 to be 1
and a 1 in column 1 forces columns 2..5 to be 1. -/
def RowOK934 (r : Row934) : Prop :=
  (r 0 = true → r 1 = true ∧ r 2 = true ∧ r 3 = true ∧ r 4 = true) ∧
    (r 1 = true → r 2 = true ∧ r 3 = true ∧ r 4 = true ∧ r 5 = true)

instance (r : Row934) : Decidable (RowOK934 r) := by
  unfold RowOK934
  infer_instance

theorem LineQ_row (r : Row934) : LineQ r ↔ RowOK934 r := by
  unfold LineQ RowOK934 Q934
  constructor
  · intro h
    have h0 := h 0 (by norm_num)
    have h1 := h 1 (by norm_num)
    simp only [pb934_of_lt r _ (show (0 : ℕ) < 6 by norm_num), pb934_of_lt r _ (show 0 + 1 < 6 by norm_num),
      pb934_of_lt r _ (show 0 + 2 < 6 by norm_num), pb934_of_lt r _ (show 0 + 3 < 6 by norm_num),
      pb934_of_lt r _ (show 0 + 4 < 6 by norm_num)] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩ i hi
    have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl
    · simp only [pb934_of_lt r _ (show (0 : ℕ) < 6 by norm_num), pb934_of_lt r _ (show 0 + 1 < 6 by norm_num),
        pb934_of_lt r _ (show 0 + 2 < 6 by norm_num), pb934_of_lt r _ (show 0 + 3 < 6 by norm_num),
        pb934_of_lt r _ (show 0 + 4 < 6 by norm_num)]
      exact h0
    · simp only [pb934_of_lt r _ (show 1 + 1 < 6 by norm_num),
        pb934_of_lt r _ (show 1 + 2 < 6 by norm_num), pb934_of_lt r _ (show 1 + 3 < 6 by norm_num),
        pb934_of_lt r _ (show 1 + 4 < 6 by norm_num), pb934_of_lt r _ (show (1 : ℕ) < 6 by norm_num)]
      exact h1

/-- An array with m rows and 6 columns. -/
abbrev Grid934 (m : ℕ) := Fin m → Fin 6 → Bool

/-- Validity in padded form: every row and every column has nondecreasing windows. -/
def IsValid934 {m : ℕ} (g : Grid934 m) : Prop :=
  (∀ i : Fin m, LineQ (g i)) ∧ (∀ j : Fin 6, LineQ (fun i => g i j))

theorem good_iff {m : ℕ} (g : Grid934 m) : good g = true ↔ IsValid934 g := by
  unfold good IsValid934
  rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
  simp only [windowsOK_ofFn]

instance {m : ℕ} (g : Grid934 m) : Decidable (IsValid934 g) :=
  decidable_of_iff _ (good_iff g)

/-- Column j of the array X, read from top to bottom. -/
def col934 {m : ℕ} (X : Grid934 m) (j : Fin 6) : Fin m → Bool := fun i => X i j

theorem col934_cons {m : ℕ} (r : Row934) (X : Grid934 m) (j : Fin 6) :
    col934 (Fin.cons r X : Grid934 (m + 1)) j = Fin.cons (r j) (col934 X j) := by
  funext i
  cases i using Fin.cases <;> rfl

/-- The state of an array: the columns whose first four entries (padded with true) are 1. -/
def st934 {m : ℕ} (X : Grid934 m) (j : Fin 6) : Bool :=
  pb934 (col934 X j) 0 && pb934 (col934 X j) 1 && pb934 (col934 X j) 2 && pb934 (col934 X j) 3

theorem st934_cons {m : ℕ} (r : Row934) (X : Grid934 m) (j : Fin 6) :
    st934 (Fin.cons r X : Grid934 (m + 1)) j =
      (r j && pb934 (col934 X j) 0 && pb934 (col934 X j) 1 && pb934 (col934 X j) 2) := by
  unfold st934
  rw [col934_cons, pb934_cons]
  rfl

theorem Q934_consF_zero (x : Bool) (f : ℕ → Bool) :
    Q934 (consF934 x f) 0 ↔ (x = true → (f 0 && f 1 && f 2 && f 3) = true) := by
  simp only [Bool.and_eq_true]
  unfold Q934
  constructor
  · intro h hx
    obtain ⟨h0, h1, h2, h3⟩ := h hx
    exact ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
  · intro h hx
    obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h hx
    exact ⟨h0, h1, h2, h3⟩

theorem IsValid934_cons {m : ℕ} (r : Row934) (X : Grid934 m) :
    IsValid934 (Fin.cons r X : Grid934 (m + 1)) ↔
      RowOK934 r ∧ IsValid934 X ∧ (4 ≤ m → ∀ j, r j = true → st934 X j = true) := by
  unfold IsValid934
  rw [Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have hc : ∀ j, LineQ (fun i => (Fin.cons r X : Grid934 (m + 1)) i j) ↔
      (4 ≤ m → (r j = true → st934 X j = true)) ∧ LineQ (col934 X j) := by
    intro j
    have e : (fun i => (Fin.cons r X : Grid934 (m + 1)) i j) = Fin.cons (r j) (col934 X j) :=
      col934_cons r X j
    rw [e, LineQ_cons, Q934_consF_zero]
    rfl
  simp only [hc, LineQ_row]
  constructor
  · rintro ⟨⟨hr, hrows⟩, hcols⟩
    exact ⟨hr, ⟨hrows, fun j => (hcols j).2⟩, fun hm j hj => (hcols j).1 hm hj⟩
  · rintro ⟨hr, ⟨hrows, hcols⟩, h4⟩
    exact ⟨⟨hr, hrows⟩, fun j => ⟨fun hm => h4 hm j, hcols j⟩⟩

theorem key934_ge {m : ℕ} (hm : 4 ≤ m) (r : Row934) (X : Grid934 m) (T : Row934) :
    (IsValid934 (Fin.cons r X : Grid934 (m + 1)) ∧ st934 (Fin.cons r X : Grid934 (m + 1)) = T) ↔
      (RowOK934 r ∧ (∀ j, r j = true → st934 X j = true) ∧ T = r) ∧ IsValid934 X := by
  rw [IsValid934_cons]
  have hst : (∀ j, r j = true → st934 X j = true) → st934 (Fin.cons r X : Grid934 (m + 1)) = r := by
    intro hsub
    funext j
    rw [st934_cons]
    cases hrj : r j
    · simp
    · have h := hsub j hrj
      unfold st934 at h
      simp only [Bool.and_eq_true] at h
      simp [h.1.1.1, h.1.1.2, h.1.2]
  constructor
  · rintro ⟨⟨hr, hX, h4⟩, hT⟩
    exact ⟨⟨hr, h4 hm, by rw [← hT, hst (h4 hm)]⟩, hX⟩
  · rintro ⟨⟨hr, hsub, rfl⟩, hX⟩
    exact ⟨⟨hr, hX, fun _ => hsub⟩, hst hsub⟩

theorem key934_lt {m : ℕ} (hm : m < 4) (r : Row934) (X : Grid934 m) (T : Row934) :
    (IsValid934 (Fin.cons r X : Grid934 (m + 1)) ∧ st934 (Fin.cons r X : Grid934 (m + 1)) = T) ↔
      (RowOK934 r ∧ ∀ j, T j = (r j && st934 X j)) ∧ IsValid934 X := by
  rw [IsValid934_cons]
  have hst : ∀ j, st934 (Fin.cons r X : Grid934 (m + 1)) j = (r j && st934 X j) := by
    intro j
    rw [st934_cons]
    unfold st934
    rw [pb934_of_ge (col934 X j) 3 (by omega), Bool.and_true]
    simp only [Bool.and_assoc]
  constructor
  · rintro ⟨⟨hr, hX, -⟩, hT⟩
    exact ⟨⟨hr, fun j => by rw [← hT, hst]⟩, hX⟩
  · rintro ⟨⟨hr, hT⟩, hX⟩
    exact ⟨⟨hr, hX, fun h => absurd h (by omega)⟩, funext fun j => by rw [hst, hT]⟩

/-- The number of valid arrays with m rows and state T. -/
def V934 (m : ℕ) (T : Row934) : ℕ := ∑ X : Grid934 m, if IsValid934 X ∧ st934 X = T then 1 else 0

theorem sum_fiber934 {m : ℕ} (P : Row934 → Prop) [DecidablePred P] :
    (∑ X : Grid934 m, if P (st934 X) ∧ IsValid934 X then 1 else 0) =
      ∑ S : Row934, if P S then V934 m S else 0 := by
  unfold V934
  have h : ∀ X : Grid934 m, (if P (st934 X) ∧ IsValid934 X then 1 else 0) =
      ∑ S : Row934, if P S then (if IsValid934 X ∧ st934 X = S then 1 else 0) else 0 := by
    intro X
    rw [Finset.sum_eq_single (st934 X)]
    · by_cases hP : P (st934 X) <;> by_cases hv : IsValid934 X <;> simp [hP, hv]
    · intro S _ hS
      have : st934 X ≠ S := fun h => hS h.symm
      simp [this]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl (fun X _ => h X), Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hP : P S
  · simp only [hP, if_true]
  · simp only [hP, if_false, Finset.sum_const_zero]

theorem V934_succ_ge {m : ℕ} (hm : 4 ≤ m) (T : Row934) :
    V934 (m + 1) T = if RowOK934 T then
      ∑ S : Row934, (if (∀ j, T j = true → S j = true) then V934 m S else 0) else 0 := by
  have h1 : V934 (m + 1) T = ∑ r : Row934, ∑ X : Grid934 m,
      if (RowOK934 r ∧ (∀ j, r j = true → st934 X j = true) ∧ T = r) ∧ IsValid934 X then 1 else 0 := by
    unfold V934
    rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row934).symm _
      (fun x => if IsValid934 (Fin.cons x.1 x.2 : Grid934 (m + 1)) ∧
        st934 (Fin.cons x.1 x.2 : Grid934 (m + 1)) = T then 1 else 0) (fun X => by simp),
      Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun r _ =>
      Finset.sum_congr rfl fun X _ => if_congr (key934_ge hm r X T) rfl rfl
  rw [h1, Finset.sum_congr rfl (fun r _ => sum_fiber934 (m := m)
    (fun S => RowOK934 r ∧ (∀ j, r j = true → S j = true) ∧ T = r))]
  rw [Finset.sum_eq_single T]
  · by_cases hT : RowOK934 T
    · rw [if_pos hT]
      exact Finset.sum_congr rfl fun S _ => if_congr (by simp [hT]) rfl rfl
    · rw [if_neg hT]
      exact Finset.sum_eq_zero fun S _ => if_neg (by tauto)
  · intro r _ hr
    refine Finset.sum_eq_zero fun S _ => if_neg ?_
    rintro ⟨-, -, h⟩
    exact hr h.symm
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem V934_succ_lt {m : ℕ} (hm : m < 4) (T : Row934) :
    V934 (m + 1) T = ∑ r : Row934, ∑ S : Row934,
      if RowOK934 r ∧ (∀ j, T j = (r j && S j)) then V934 m S else 0 := by
  have h1 : V934 (m + 1) T = ∑ r : Row934, ∑ X : Grid934 m,
      if (RowOK934 r ∧ ∀ j, T j = (r j && st934 X j)) ∧ IsValid934 X then 1 else 0 := by
    unfold V934
    rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row934).symm _
      (fun x => if IsValid934 (Fin.cons x.1 x.2 : Grid934 (m + 1)) ∧
        st934 (Fin.cons x.1 x.2 : Grid934 (m + 1)) = T then 1 else 0) (fun X => by simp),
      Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun r _ =>
      Finset.sum_congr rfl fun X _ => if_congr (key934_lt hm r X T) rfl rfl
  rw [h1]
  exact Finset.sum_congr rfl fun r _ =>
    sum_fiber934 (m := m) (fun S => RowOK934 r ∧ ∀ j, T j = (r j && S j))

theorem V934_zero (T : Row934) : V934 0 T = if (∀ j, T j = true) then 1 else 0 := by
  have hall : ∀ X : Grid934 0, (IsValid934 X ∧ st934 X = T) ↔ ∀ j, T j = true := by
    intro X
    have hv : IsValid934 X := ⟨fun i => Fin.elim0 i, fun j i hi => absurd hi (by omega)⟩
    have hs : st934 X = fun _ => true := by
      funext j
      unfold st934
      rw [pb934_of_ge _ 0 (by omega), pb934_of_ge _ 1 (by omega), pb934_of_ge _ 2 (by omega),
        pb934_of_ge _ 3 (by omega)]
      rfl
    rw [hs]
    constructor
    · rintro ⟨-, h⟩ j
      rw [← h]
    · intro h
      exact ⟨hv, funext fun j => (h j).symm⟩
  unfold V934
  rw [Fintype.sum_unique]
  exact if_congr (hall _) rfl rfl

theorem card_eq_sum_V934 (m : ℕ) :
    (Finset.univ.filter (fun g : Grid934 m => IsValid934 g)).card = ∑ T : Row934, V934 m T := by
  rw [Finset.card_filter]
  have := sum_fiber934 (m := m) (fun _ => True)
  simp only [true_and, if_true] at this
  rw [← this]

/-- The row (or set of columns) with code u: the entry of column j is bit j of u. -/
def row934 (u : Fin 64) : Row934 := fun j => Nat.testBit u.val j.val

theorem row934_injective : Function.Injective row934 := by
  decide +kernel

theorem row934_bijective : Function.Bijective row934 := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row934_injective, by simp⟩

theorem sum_row934 (F : Row934 → ℕ) : ∑ r : Row934, F r = ∑ u : Fin 64, F (row934 u) :=
  (Fintype.sum_bijective row934 row934_bijective _ _ (fun _ => rfl)).symm

theorem and_iff_land (t e s : Fin 64) :
    (∀ j, row934 t j = (row934 e j && row934 s j)) ↔ t.val = e.val &&& s.val := by
  unfold row934
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    by_cases hi : i < 6
    · exact h ⟨i, hi⟩
    · have p6 : (64 : ℕ) ≤ 2 ^ i := by
        calc (64 : ℕ) = 2 ^ 6 := by norm_num
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le t.isLt p6),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le e.isLt p6), Bool.false_and]
  · intro h j
    rw [h, Nat.testBit_and]

theorem sub_iff_land (t s : Fin 64) :
    (∀ j, row934 t j = true → row934 s j = true) ↔ t.val &&& s.val = t.val := by
  unfold row934
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    by_cases hi : i < 6
    · have := h ⟨i, hi⟩
      cases ht : t.val.testBit i
      · simp
      · simp [this ht]
    · have p6 : (64 : ℕ) ≤ 2 ^ i := by
        calc (64 : ℕ) = 2 ^ 6 := by norm_num
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le t.isLt p6), Bool.false_and]
  · intro h j hj
    have := congrArg (fun x => Nat.testBit x j.val) h
    simp only [Nat.testBit_and, hj, Bool.true_and] at this
    exact this

/-- One step of the state recursion on codes while the array has fewer than 4 rows. -/
def Psi934 (f : Fin 64 → ℕ) (t : Fin 64) : ℕ :=
  ∑ e : Fin 64, if RowOK934 (row934 e) then
    ∑ s : Fin 64, (if t.val = e.val &&& s.val then f s else 0) else 0

/-- One step of the state recursion on codes once the array has at least 4 rows. -/
def Phi934 (f : Fin 64 → ℕ) (t : Fin 64) : ℕ :=
  if RowOK934 (row934 t) then
    ∑ s : Fin 64, (if t.val &&& s.val = t.val then f s else 0) else 0

theorem v934_succ_lt {m : ℕ} (hm : m < 4) (t : Fin 64) :
    V934 (m + 1) (row934 t) = Psi934 (fun s => V934 m (row934 s)) t := by
  rw [V934_succ_lt hm, sum_row934]
  unfold Psi934
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [sum_row934]
  by_cases he : RowOK934 (row934 e)
  · rw [if_pos he]
    exact Finset.sum_congr rfl fun s _ => if_congr (by rw [and_iff_land]; simp [he]) rfl rfl
  · rw [if_neg he]
    exact Finset.sum_eq_zero fun s _ => if_neg (by tauto)

theorem v934_succ_ge {m : ℕ} (hm : 4 ≤ m) (t : Fin 64) :
    V934 (m + 1) (row934 t) = Phi934 (fun s => V934 m (row934 s)) t := by
  rw [V934_succ_ge hm, sum_row934]
  unfold Phi934
  by_cases ht : RowOK934 (row934 t)
  · rw [if_pos ht, if_pos ht]
    exact Finset.sum_congr rfl fun s _ => if_congr (sub_iff_land t s) rfl rfl
  · rw [if_neg ht, if_neg ht]

/-- The state counts V m for m ≤ 4, on codes. -/
def TV934 : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
   [1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1],
   [85, 0, 0, 0, 31, 0, 0, 0, 31, 0, 0, 0, 13, 0, 0, 0, 31, 0, 0, 0, 13, 0, 0, 0, 13, 0, 0, 0, 7, 0, 0, 0, 31, 0, 0, 0, 13, 0, 0, 0, 13, 0, 0, 0, 7, 0, 0, 0, 13, 0, 0, 0, 7, 0, 0, 0, 7, 0, 0, 0, 5, 0, 3, 1],
   [2899, 0, 0, 0, 517, 0, 0, 0, 517, 0, 0, 0, 115, 0, 0, 0, 517, 0, 0, 0, 115, 0, 0, 0, 115, 0, 0, 0, 37, 0, 0, 0, 517, 0, 0, 0, 115, 0, 0, 0, 115, 0, 0, 0, 37, 0, 0, 0, 115, 0, 0, 0, 37, 0, 0, 0, 37, 0, 0, 0, 19, 0, 7, 1],
   [71809, 0, 0, 0, 6799, 0, 0, 0, 6799, 0, 0, 0, 865, 0, 0, 0, 6799, 0, 0, 0, 865, 0, 0, 0, 865, 0, 0, 0, 175, 0, 0, 0, 6799, 0, 0, 0, 865, 0, 0, 0, 865, 0, 0, 0, 175, 0, 0, 0, 865, 0, 0, 0, 175, 0, 0, 0, 175, 0, 0, 0, 65, 0, 15, 1]]

def tv934 (m : ℕ) (u : Fin 64) : ℕ := (TV934.getD m []).getD u.val 0

/-- The coefficients w j of V (m + 4) = Sum_j C(m, j) w j, on codes. -/
def WT934 : List (List ℕ) :=
  [[71809, 0, 0, 0, 6799, 0, 0, 0, 6799, 0, 0, 0, 865, 0, 0, 0, 6799, 0, 0, 0, 865, 0, 0, 0, 865, 0, 0, 0, 175, 0, 0, 0, 6799, 0, 0, 0, 865, 0, 0, 0, 865, 0, 0, 0, 175, 0, 0, 0, 865, 0, 0, 0, 175, 0, 0, 0, 175, 0, 0, 0, 65, 0, 15, 1],
   [33167, 0, 0, 0, 3201, 0, 0, 0, 3201, 0, 0, 0, 431, 0, 0, 0, 3201, 0, 0, 0, 431, 0, 0, 0, 431, 0, 0, 0, 81, 0, 0, 0, 3201, 0, 0, 0, 431, 0, 0, 0, 431, 0, 0, 0, 81, 0, 0, 0, 431, 0, 0, 0, 81, 0, 0, 0, 81, 0, 0, 0, 16, 0, 1, 0],
   [15731, 0, 0, 0, 1553, 0, 0, 0, 1553, 0, 0, 0, 179, 0, 0, 0, 1553, 0, 0, 0, 179, 0, 0, 0, 179, 0, 0, 0, 17, 0, 0, 0, 1553, 0, 0, 0, 179, 0, 0, 0, 179, 0, 0, 0, 17, 0, 0, 0, 179, 0, 0, 0, 17, 0, 0, 0, 17, 0, 0, 0, 1, 0, 0, 0],
   [7355, 0, 0, 0, 589, 0, 0, 0, 589, 0, 0, 0, 35, 0, 0, 0, 589, 0, 0, 0, 35, 0, 0, 0, 35, 0, 0, 0, 1, 0, 0, 0, 589, 0, 0, 0, 35, 0, 0, 0, 35, 0, 0, 0, 1, 0, 0, 0, 35, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
   [2570, 0, 0, 0, 108, 0, 0, 0, 108, 0, 0, 0, 2, 0, 0, 0, 108, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 108, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [444, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def tw934 (j : ℕ) (u : Fin 64) : ℕ := (WT934.getD j []).getD u.val 0

theorem tv934_zero : ∀ u : Fin 64, tv934 0 u = if (∀ j, row934 u j = true) then 1 else 0 := by
  decide +kernel

theorem tv934_step0 : ∀ u : Fin 64, Psi934 (tv934 0) u = tv934 1 u := by
  decide +kernel

theorem tv934_step1 : ∀ u : Fin 64, Psi934 (tv934 1) u = tv934 2 u := by
  decide +kernel

theorem tv934_step2 : ∀ u : Fin 64, Psi934 (tv934 2) u = tv934 3 u := by
  decide +kernel

theorem tv934_step3 : ∀ u : Fin 64, Psi934 (tv934 3) u = tv934 4 u := by
  decide +kernel

theorem tv934_step (m : ℕ) (hm : m < 4) (u : Fin 64) : Psi934 (tv934 m) u = tv934 (m + 1) u := by
  interval_cases m
  · exact tv934_step0 u
  · exact tv934_step1 u
  · exact tv934_step2 u
  · exact tv934_step3 u

theorem tw934_zero : ∀ u : Fin 64, tw934 0 u = tv934 4 u := by
  decide +kernel

theorem tw934_step : ∀ j < 7, ∀ u : Fin 64, Phi934 (tw934 j) u = tw934 j u + tw934 (j + 1) u := by
  decide +kernel

theorem tw934_seven (u : Fin 64) : tw934 7 u = 0 := rfl

theorem tw934_sums : (∑ u, tw934 0 u) = 104976 ∧ (∑ u, tw934 1 u) = 48898 ∧
    (∑ u, tw934 2 u) = 23086 ∧ (∑ u, tw934 3 u) = 9925 ∧ (∑ u, tw934 4 u) = 3014 ∧
    (∑ u, tw934 5 u) = 468 ∧ (∑ u, tw934 6 u) = 24 := by
  decide +kernel

theorem V934_small (m : ℕ) (hm : m ≤ 4) (u : Fin 64) : V934 m (row934 u) = tv934 m u := by
  induction m generalizing u with
  | zero => rw [V934_zero, tv934_zero]
  | succ m ih =>
    have e : (fun s => V934 m (row934 s)) = tv934 m := funext fun s => ih (by omega) s
    rw [v934_succ_lt (by omega), e, tv934_step m (by omega) u]

theorem Phi934_lin (S : Finset ℕ) (w : ℕ → ℕ) (F : ℕ → Fin 64 → ℕ) (t : Fin 64) :
    Phi934 (fun s => ∑ j ∈ S, w j * F j s) t = ∑ j ∈ S, w j * Phi934 (F j) t := by
  unfold Phi934
  split_ifs with h
  · simp only [Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs <;> simp
  · simp

theorem V934_big (m : ℕ) :
    ∀ u : Fin 64, V934 (m + 4) (row934 u) = ∑ j ∈ range 7, m.choose j * tw934 j u := by
  induction m with
  | zero =>
    intro u
    rw [Nat.zero_add, V934_small 4 le_rfl u, ← tw934_zero u]
    simp [Finset.sum_range_succ]
  | succ m ih =>
    intro u
    rw [show m + 1 + 4 = (m + 4) + 1 by omega, v934_succ_ge (by omega)]
    rw [show (fun s => V934 (m + 4) (row934 s)) = fun s => ∑ j ∈ range 7, m.choose j * tw934 j s from
      funext ih, Phi934_lin]
    rw [Finset.sum_congr rfl (fun j hj => by rw [tw934_step j (Finset.mem_range.mp hj) u])]
    have h7 := tw934_seven u
    have p1 : (m + 1).choose 1 = m.choose 0 + m.choose 1 := Nat.choose_succ_succ m 0
    have p2 : (m + 1).choose 2 = m.choose 1 + m.choose 2 := Nat.choose_succ_succ m 1
    have p3 : (m + 1).choose 3 = m.choose 2 + m.choose 3 := Nat.choose_succ_succ m 2
    have p4 : (m + 1).choose 4 = m.choose 3 + m.choose 4 := Nat.choose_succ_succ m 3
    have p5 : (m + 1).choose 5 = m.choose 4 + m.choose 5 := Nat.choose_succ_succ m 4
    have p6 : (m + 1).choose 6 = m.choose 5 + m.choose 6 := Nat.choose_succ_succ m 5
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, p1, p2, p3, p4, p5, p6,
      Nat.choose_zero_right, h7]
    ring

theorem a934_closed (n : ℕ) :
    (a (n + 1) : ℤ) = 104976 + 48898 * (n : ℤ) + 23086 * (n.choose 2 : ℤ) +
      9925 * (n.choose 3 : ℤ) + 3014 * (n.choose 4 : ℤ) + 468 * (n.choose 5 : ℤ) +
      24 * (n.choose 6 : ℤ) := by
  have h1 : a (n + 1) = (Finset.univ.filter (fun g : Grid934 (n + 4) => IsValid934 g)).card := by
    unfold a
    exact congrArg Finset.card (Finset.filter_congr (fun g _ => good_iff g))
  rw [h1, card_eq_sum_V934, sum_row934]
  simp only [V934_big n]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  obtain ⟨c0, c1, c2, c3, c4, c5, c6⟩ := tw934_sums
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c0, c1, c2, c3, c4, c5, c6,
    Nat.choose_zero_right, Nat.choose_one_right]
  push_cast
  ring

theorem choose2_934 (m : ℕ) : (m.choose 2 : ℚ) = m * (m - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, Nat.choose_one_right]
    push_cast
    ring

theorem choose3_934 (m : ℕ) : (m.choose 3 : ℚ) = m * (m - 1) * (m - 2) / 6 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, choose2_934]
    push_cast
    ring

theorem choose4_934 (m : ℕ) : (m.choose 4 : ℚ) = m * (m - 1) * (m - 2) * (m - 3) / 24 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, choose3_934]
    push_cast
    ring

theorem choose5_934 (m : ℕ) :
    (m.choose 5 : ℚ) = m * (m - 1) * (m - 2) * (m - 3) * (m - 4) / 120 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, choose4_934]
    push_cast
    ring

theorem choose6_934 (m : ℕ) :
    (m.choose 6 : ℚ) = m * (m - 1) * (m - 2) * (m - 3) * (m - 4) * (m - 5) / 720 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, choose5_934]
    push_cast
    ring

/-- The closed form of a (n + 1) as a polynomial in n. -/
def P934 (x : ℚ) : ℚ :=
  104976 + 48898 * x + 23086 * (x * (x - 1) / 2) + 9925 * (x * (x - 1) * (x - 2) / 6) +
    3014 * (x * (x - 1) * (x - 2) * (x - 3) / 24) +
    468 * (x * (x - 1) * (x - 2) * (x - 3) * (x - 4) / 120) +
    24 * (x * (x - 1) * (x - 2) * (x - 3) * (x - 4) * (x - 5) / 720)

theorem closedQ934 (n : ℕ) : ((a (n + 1) : ℤ) : ℚ) = P934 n := by
  rw [a934_closed]
  push_cast
  rw [choose2_934, choose3_934, choose4_934, choose5_934, choose6_934]
  rfl

theorem recurrence934 (n : ℕ) (hn : 7 < n) :
    (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) +
      21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
  rw [show k + 8 - 1 = (k + 6) + 1 by omega, show k + 8 - 2 = (k + 5) + 1 by omega,
    show k + 8 - 3 = (k + 4) + 1 by omega, show k + 8 - 4 = (k + 3) + 1 by omega,
    show k + 8 - 5 = (k + 2) + 1 by omega, show k + 8 - 6 = (k + 1) + 1 by omega,
    show k + 8 - 7 = k + 1 by omega, show k + 8 = (k + 7) + 1 by omega]
  have h : (((a ((k + 7) + 1) : ℤ)) : ℚ) = ((7 * (a ((k + 6) + 1) : ℤ) - 21 * a ((k + 5) + 1) +
      35 * a ((k + 4) + 1) - 35 * a ((k + 3) + 1) + 21 * a ((k + 2) + 1) - 7 * a ((k + 1) + 1) +
      a (k + 1) : ℤ) : ℚ) := by
    push_cast
    rw [← Int.cast_natCast, ← Int.cast_natCast (a ((k + 6) + 1)), ← Int.cast_natCast (a ((k + 5) + 1)),
      ← Int.cast_natCast (a ((k + 4) + 1)), ← Int.cast_natCast (a ((k + 3) + 1)),
      ← Int.cast_natCast (a ((k + 2) + 1)), ← Int.cast_natCast (a ((k + 1) + 1)),
      ← Int.cast_natCast (a (k + 1))]
    rw [closedQ934, closedQ934, closedQ934, closedQ934, closedQ934, closedQ934, closedQ934,
      closedQ934]
    unfold P934
    push_cast
    ring
  exact_mod_cast h

/-- The sequence with the constant term 0, as in the generating function. -/
def bs934 (n : ℕ) : ℤ := if n = 0 then 0 else (a n : ℤ)

theorem bs934_succ (n : ℕ) : bs934 (n + 1) = (a (n + 1) : ℤ) := by
  unfold bs934
  simp

theorem bs934_vals : bs934 0 = 0 ∧ bs934 1 = 104976 ∧ bs934 2 = 153874 ∧ bs934 3 = 225858 ∧
    bs934 4 = 330853 ∧ bs934 5 = 481798 ∧ bs934 6 = 695114 ∧ bs934 7 = 991196 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [bs934_succ, a934_closed]
    norm_num [Nat.choose]
  · rw [bs934_succ, a934_closed]
    norm_num [Nat.choose]
  · rw [bs934_succ, a934_closed]
    norm_num [Nat.choose]
  · rw [bs934_succ, a934_closed]
    norm_num [Nat.choose]
  · rw [bs934_succ, a934_closed]
    norm_num [Nat.choose]
  · rw [bs934_succ, a934_closed]
    norm_num [Nat.choose]
  · rw [bs934_succ, a934_closed]
    norm_num [Nat.choose]

theorem bs934_rec (j : ℕ) :
    bs934 (j + 8) = 7 * bs934 (j + 7) - 21 * bs934 (j + 6) + 35 * bs934 (j + 5) -
      35 * bs934 (j + 4) + 21 * bs934 (j + 3) - 7 * bs934 (j + 2) + bs934 (j + 1) := by
  have h := recurrence934 (j + 8) (by omega)
  simp only [show j + 8 - 1 = j + 7 by omega, show j + 8 - 2 = j + 6 by omega,
    show j + 8 - 3 = j + 5 by omega, show j + 8 - 4 = j + 4 by omega,
    show j + 8 - 5 = j + 3 by omega, show j + 8 - 6 = j + 2 by omega,
    show j + 8 - 7 = j + 1 by omega] at h
  rw [show j + 8 = (j + 7) + 1 by omega, show j + 7 = (j + 6) + 1 by omega,
    show j + 6 = (j + 5) + 1 by omega, show j + 5 = (j + 4) + 1 by omega,
    show j + 4 = (j + 3) + 1 by omega, show j + 3 = (j + 2) + 1 by omega,
    show j + 2 = (j + 1) + 1 by omega] at h ⊢
  simp only [bs934_succ]
  exact h

open PowerSeries in
theorem gen_fun934 :
    PowerSeries.mk bs934 * (1 - X) ^ 7 =
      X * (104976 - 580958 * X + 1353236 * X ^ 2 - 1692959 * X ^ 3 + 1197415 * X ^ 4 -
        453495 * X ^ 5 + 71809 * X ^ 6) := by
  have key : PowerSeries.mk bs934 * (1 - X) ^ 7 =
      C 1 * (PowerSeries.mk bs934 * X ^ 0) - C 7 * (PowerSeries.mk bs934 * X ^ 1) +
        C 21 * (PowerSeries.mk bs934 * X ^ 2) - C 35 * (PowerSeries.mk bs934 * X ^ 3) +
        C 35 * (PowerSeries.mk bs934 * X ^ 4) - C 21 * (PowerSeries.mk bs934 * X ^ 5) +
        C 7 * (PowerSeries.mk bs934 * X ^ 6) - C 1 * (PowerSeries.mk bs934 * X ^ 7) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℤ⟦X⟧) * (104976 - 580958 * X + 1353236 * X ^ 2 - 1692959 * X ^ 3 +
      1197415 * X ^ 4 - 453495 * X ^ 5 + 71809 * X ^ 6) =
      C 104976 * X ^ 1 - C 580958 * X ^ 2 + C 1353236 * X ^ 3 - C 1692959 * X ^ 4 +
        C 1197415 * X ^ 5 - C 453495 * X ^ 6 + C 71809 * X ^ 7 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := bs934_vals
  by_cases hk : k < 8
  · interval_cases k <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 8 := ⟨k - 8, by omega⟩
    have hr := bs934_rec j
    simp only [show 0 ≤ j + 8 by omega, show 1 ≤ j + 8 by omega, show 2 ≤ j + 8 by omega,
      show 3 ≤ j + 8 by omega, show 4 ≤ j + 8 by omega, show 5 ≤ j + 8 by omega,
      show 6 ≤ j + 8 by omega, show 7 ≤ j + 8 by omega,
      show j + 8 - 0 = j + 8 by omega, show j + 8 - 1 = j + 7 by omega,
      show j + 8 - 2 = j + 6 by omega, show j + 8 - 3 = j + 5 by omega,
      show j + 8 - 4 = j + 4 by omega, show j + 8 - 5 = j + 3 by omega,
      show j + 8 - 6 = j + 2 by omega, show j + 8 - 7 = j + 1 by omega,
      show ¬ (j + 8 = 1) by omega, show ¬ (j + 8 = 2) by omega, show ¬ (j + 8 = 3) by omega,
      show ¬ (j + 8 = 4) by omega, show ¬ (j + 8 = 5) by omega, show ¬ (j + 8 = 6) by omega,
      show ¬ (j + 8 = 7) by omega, if_true, if_false]
    linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a202934.main :=
  ⟨OMA.Helpers.gen_fun934, OMA.Helpers.recurrence934⟩
