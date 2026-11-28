import OMAStatements.S_oeis_a202935
import Mathlib

/-!
Proof of Barker's conjectures for A202935 ((n+3) X 7 binary arrays whose rows and columns have
nondecreasing consecutive windows of four bits).

Windows. The window `c0 c1 c2 c3` is at most `c1 c2 c3 c4` iff `c0 = 1` forces
`c1 = c2 = c3 = c4 = 1`. Hence a line has nondecreasing windows iff every 1 at a position `i`
with `i + 4 < L` is followed by four 1s (`bridge`, by induction on the list).

Adding a row on top. Only the first pair of windows of each column is new, and it exists iff the
array below has at least 4 rows (`IsValid_cons`). The state of an array is the set of columns
whose first four entries (padded with 1s) are 1. With `V m T` the number of valid arrays with
`m` rows and state `T`, `V (m + 1)` is `Psi (V m)` for `m < 4` and `Phi (V m)` for `m ≥ 4`.

Codes. States are coded by `0, ..., 127` (bit `j` is column `j`); on codes the two steps are
`PsiC` and `PhiC`, written with bitwise operations so that the kernel checks the tables fast.
The tables `tvf m` (`m ≤ 4`) and `twf j` (`j ≤ 7`) satisfy `PsiC (tvf m) = tvf (m + 1)`,
`twf 0 = tvf 4`, `PhiC (twf j) = twf j + twf (j + 1)` and `twf 8 = 0`, so that
`V (m + 4) = Sum_{j ≤ 7} C(m, j) twf j` and `a (n + 1)` is a polynomial of degree 7 in `n`.
The recurrence follows by substitution, and the generating function by comparing coefficients.
-/

namespace OMA.Helpers.A202935

open OMA.S_oeis_a202935 Finset

/-- A row of the array (7 entries), or a set of columns given by its indicator. -/
abbrev Row := Fin 7 → Bool

/-- An array with `m` rows and 7 columns. -/
abbrev Grid (m : ℕ) := Fin m → Fin 7 → Bool

/-- Two consecutive windows `c0 c1 c2 c3` and `c1 c2 c3 c4`: the first is at most the second iff
`c0 = 1` forces `c1 = c2 = c3 = c4 = 1`. -/
theorem win_le_iff (c0 c1 c2 c3 c4 : Bool) :
    win c0 c1 c2 c3 ≤ win c1 c2 c3 c4 ↔
      (c0 = true → c1 = true ∧ c2 = true ∧ c3 = true ∧ c4 = true) := by
  revert c0 c1 c2 c3 c4
  decide

/-- The entries of a line, padded with `true` beyond its end. -/
def pb {L : ℕ} (line : Fin L → Bool) (k : ℕ) : Bool := if h : k < L then line ⟨k, h⟩ else true

theorem pb_of_lt {L : ℕ} (line : Fin L → Bool) (k : ℕ) (h : k < L) : pb line k = line ⟨k, h⟩ :=
  dif_pos h

theorem pb_of_ge {L : ℕ} (line : Fin L → Bool) (k : ℕ) (h : L ≤ k) : pb line k = true :=
  dif_neg (by omega)

/-- Put a bit in front of a padded line. -/
def consF (x : Bool) (f : ℕ → Bool) : ℕ → Bool
  | 0 => x
  | k + 1 => f k

theorem pb_cons {L : ℕ} (x : Bool) (u : Fin L → Bool) :
    pb (Fin.cons x u : Fin (L + 1) → Bool) = consF x (pb u) := by
  funext k
  cases k with
  | zero => simp [pb, consF]
  | succ k =>
    show pb (Fin.cons x u : Fin (L + 1) → Bool) (k + 1) = pb u k
    by_cases h : k < L
    · rw [pb_of_lt _ _ (by omega), pb_of_lt _ _ h]
      show (Fin.cons x u : Fin (L + 1) → Bool) (Fin.succ ⟨k, h⟩) = u ⟨k, h⟩
      rw [Fin.cons_succ]
    · rw [pb_of_ge _ _ (by omega), pb_of_ge _ _ (by omega)]

/-- The window condition at position `i` of a padded line `f`. -/
def Q (f : ℕ → Bool) (i : ℕ) : Prop :=
  f i = true → f (i + 1) = true ∧ f (i + 2) = true ∧ f (i + 3) = true ∧ f (i + 4) = true

/-- A line whose every 1 at a position `i` with `i + 4 < L` is followed by four 1s. -/
def LOK {L : ℕ} (line : Fin L → Bool) : Prop := ∀ i, i + 4 < L → Q (pb line) i

theorem wok_short (l : List Bool) (h : l.length ≤ 4) : windowsOK l = true := by
  match l, h with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl
  | [_, _, _, _], _ => rfl
  | _ :: _ :: _ :: _ :: _ :: _, h =>
    simp only [List.length_cons] at h
    omega

theorem wok_cons (x : Bool) (l : List Bool) :
    windowsOK (x :: l) = true ↔
      (4 ≤ l.length → x = true → l.getD 0 true = true ∧ l.getD 1 true = true ∧
        l.getD 2 true = true ∧ l.getD 3 true = true) ∧ windowsOK l = true := by
  match l with
  | b1 :: b2 :: b3 :: b4 :: rest =>
    simp only [windowsOK, Bool.and_eq_true, decide_eq_true_eq, win_le_iff, List.length_cons,
      List.getD_cons_zero, List.getD_cons_succ]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun _ => h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1 (by omega), h2⟩
  | [] => simp [wok_short]
  | [_] => simp [wok_short]
  | [_, _] => simp [wok_short]
  | [_, _, _] => simp [wok_short]

theorem getD_ofFn {L : ℕ} (u : Fin L → Bool) (k : ℕ) : (List.ofFn u).getD k true = pb u k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  unfold pb
  split_ifs <;> rfl

theorem ofFn_cons' {L : ℕ} (x : Bool) (u : Fin L → Bool) :
    List.ofFn (Fin.cons x u : Fin (L + 1) → Bool) = x :: List.ofFn u := by
  rw [List.ofFn_succ]
  simp

theorem LOK_cons {L : ℕ} (x : Bool) (u : Fin L → Bool) :
    LOK (Fin.cons x u : Fin (L + 1) → Bool) ↔ (4 ≤ L → Q (consF x (pb u)) 0) ∧ LOK u := by
  unfold LOK
  rw [pb_cons]
  constructor
  · intro h
    exact ⟨fun _ => h 0 (by omega), fun i hi => h (i + 1) (by omega)⟩
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => exact h0 (by omega)
    | succ k => exact h k (by omega)

/-- The window condition of the statement, on a line given as a function. -/
theorem bridge : ∀ (L : ℕ) (line : Fin L → Bool), windowsOK (List.ofFn line) = true ↔ LOK line
  | 0, line => by
    simp only [List.ofFn_zero]
    exact ⟨fun _ i hi => absurd hi (by omega), fun _ => rfl⟩
  | L + 1, line => by
    rw [← Fin.cons_self_tail line, ofFn_cons', wok_cons, bridge L, LOK_cons, List.length_ofFn,
      getD_ofFn, getD_ofFn, getD_ofFn, getD_ofFn]
    exact Iff.rfl

instance (L : ℕ) (line : Fin L → Bool) : Decidable (LOK line) :=
  decidable_of_iff _ (bridge L line)

/-- Every row and every column of `X` satisfies the window condition. -/
def IsValid {m : ℕ} (X : Grid m) : Prop := (∀ i, LOK (X i)) ∧ ∀ j, LOK (fun i => X i j)

instance {m : ℕ} (X : Grid m) : Decidable (IsValid X) := by
  unfold IsValid
  infer_instance

theorem good_iff {m : ℕ} (X : Grid m) : good X = true ↔ IsValid X := by
  unfold good IsValid
  simp only [Bool.and_eq_true, decide_eq_true_eq, bridge]


/-- Column `j` of the array `X`, read from top to bottom. -/
def col {m : ℕ} (X : Grid m) (j : Fin 7) : Fin m → Bool := fun i => X i j

theorem col_cons {m : ℕ} (r : Row) (X : Grid m) (j : Fin 7) :
    col (Fin.cons r X : Grid (m + 1)) j = Fin.cons (r j) (col X j) := by
  funext i
  cases i using Fin.cases <;> rfl

/-- The state of an array: the columns whose first four entries (padded with `true`) are 1. -/
def st {m : ℕ} (X : Grid m) (j : Fin 7) : Bool :=
  pb (col X j) 0 && pb (col X j) 1 && pb (col X j) 2 && pb (col X j) 3

theorem st_cons {m : ℕ} (r : Row) (X : Grid m) (j : Fin 7) :
    st (Fin.cons r X : Grid (m + 1)) j =
      (r j && pb (col X j) 0 && pb (col X j) 1 && pb (col X j) 2) := by
  unfold st
  rw [col_cons, pb_cons]
  rfl

theorem Q_consF_zero (x : Bool) (f : ℕ → Bool) :
    Q (consF x f) 0 ↔ (x = true → (f 0 && f 1 && f 2 && f 3) = true) := by
  simp only [Bool.and_eq_true]
  unfold Q
  constructor
  · intro h hx
    obtain ⟨h0, h1, h2, h3⟩ := h hx
    exact ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
  · intro h hx
    obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h hx
    exact ⟨h0, h1, h2, h3⟩

theorem IsValid_cons {m : ℕ} (r : Row) (X : Grid m) :
    IsValid (Fin.cons r X : Grid (m + 1)) ↔
      LOK r ∧ IsValid X ∧ (4 ≤ m → ∀ j, r j = true → st X j = true) := by
  unfold IsValid
  rw [Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have hc : ∀ j, LOK (fun i => (Fin.cons r X : Grid (m + 1)) i j) ↔
      (4 ≤ m → (r j = true → st X j = true)) ∧ LOK (col X j) := by
    intro j
    have e : (fun i => (Fin.cons r X : Grid (m + 1)) i j) = Fin.cons (r j) (col X j) :=
      col_cons r X j
    rw [e, LOK_cons, Q_consF_zero]
    rfl
  simp only [hc]
  constructor
  · rintro ⟨⟨hr, hrows⟩, hcols⟩
    exact ⟨hr, ⟨hrows, fun j => (hcols j).2⟩, fun hm j hj => (hcols j).1 hm hj⟩
  · rintro ⟨hr, ⟨hrows, hcols⟩, h4⟩
    exact ⟨⟨hr, hrows⟩, fun j => ⟨fun hm => h4 hm j, hcols j⟩⟩

theorem key_ge {m : ℕ} (hm : 4 ≤ m) (r : Row) (X : Grid m) (T : Row) :
    (IsValid (Fin.cons r X : Grid (m + 1)) ∧ st (Fin.cons r X : Grid (m + 1)) = T) ↔
      (LOK r ∧ (∀ j, r j = true → st X j = true) ∧ T = r) ∧ IsValid X := by
  rw [IsValid_cons]
  have hst : (∀ j, r j = true → st X j = true) → st (Fin.cons r X : Grid (m + 1)) = r := by
    intro hsub
    funext j
    rw [st_cons]
    cases hrj : r j
    · simp
    · have h := hsub j hrj
      unfold st at h
      simp only [Bool.and_eq_true] at h
      simp [h.1.1.1, h.1.1.2, h.1.2]
  constructor
  · rintro ⟨⟨hr, hX, h4⟩, hT⟩
    exact ⟨⟨hr, h4 hm, by rw [← hT, hst (h4 hm)]⟩, hX⟩
  · rintro ⟨⟨hr, hsub, rfl⟩, hX⟩
    exact ⟨⟨hr, hX, fun _ => hsub⟩, hst hsub⟩

theorem key_lt {m : ℕ} (hm : m < 4) (r : Row) (X : Grid m) (T : Row) :
    (IsValid (Fin.cons r X : Grid (m + 1)) ∧ st (Fin.cons r X : Grid (m + 1)) = T) ↔
      (LOK r ∧ ∀ j, T j = (r j && st X j)) ∧ IsValid X := by
  rw [IsValid_cons]
  have hst : ∀ j, st (Fin.cons r X : Grid (m + 1)) j = (r j && st X j) := by
    intro j
    rw [st_cons]
    unfold st
    rw [pb_of_ge (col X j) 3 (by omega), Bool.and_true]
    simp only [Bool.and_assoc]
  constructor
  · rintro ⟨⟨hr, hX, -⟩, hT⟩
    exact ⟨⟨hr, fun j => by rw [← hT, hst]⟩, hX⟩
  · rintro ⟨⟨hr, hT⟩, hX⟩
    exact ⟨⟨hr, hX, fun h => absurd h (by omega)⟩, funext fun j => by rw [hst, hT]⟩

/-- The number of valid arrays with `m` rows and state `T`. -/
def V (m : ℕ) (T : Row) : ℕ := ∑ X : Grid m, if IsValid X ∧ st X = T then 1 else 0

theorem sum_fiber {m : ℕ} (P : Row → Prop) [DecidablePred P] :
    (∑ X : Grid m, if P (st X) ∧ IsValid X then 1 else 0) =
      ∑ S : Row, if P S then V m S else 0 := by
  unfold V
  have h : ∀ X : Grid m, (if P (st X) ∧ IsValid X then 1 else 0) =
      ∑ S : Row, if P S then (if IsValid X ∧ st X = S then 1 else 0) else 0 := by
    intro X
    rw [Finset.sum_eq_single (st X)]
    · by_cases hP : P (st X) <;> by_cases hv : IsValid X <;> simp [hP, hv]
    · intro S _ hS
      have : st X ≠ S := fun h => hS h.symm
      simp [this]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl (fun X _ => h X), Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hP : P S
  · simp only [hP, if_true]
  · simp only [hP, if_false, Finset.sum_const_zero]

theorem V_succ_ge {m : ℕ} (hm : 4 ≤ m) (T : Row) :
    V (m + 1) T = if LOK T then
      ∑ S : Row, (if (∀ j, T j = true → S j = true) then V m S else 0) else 0 := by
  have h1 : V (m + 1) T = ∑ r : Row, ∑ X : Grid m,
      if (LOK r ∧ (∀ j, r j = true → st X j = true) ∧ T = r) ∧ IsValid X then 1 else 0 := by
    unfold V
    rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
      (fun x => if IsValid (Fin.cons x.1 x.2 : Grid (m + 1)) ∧
        st (Fin.cons x.1 x.2 : Grid (m + 1)) = T then 1 else 0) (fun X => by simp),
      Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun r _ =>
      Finset.sum_congr rfl fun X _ => if_congr (key_ge hm r X T) rfl rfl
  rw [h1, Finset.sum_congr rfl (fun r _ => sum_fiber (m := m)
    (fun S => LOK r ∧ (∀ j, r j = true → S j = true) ∧ T = r))]
  rw [Finset.sum_eq_single T]
  · by_cases hT : LOK T
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

theorem V_succ_lt {m : ℕ} (hm : m < 4) (T : Row) :
    V (m + 1) T = ∑ r : Row, ∑ S : Row,
      if LOK r ∧ (∀ j, T j = (r j && S j)) then V m S else 0 := by
  have h1 : V (m + 1) T = ∑ r : Row, ∑ X : Grid m,
      if (LOK r ∧ ∀ j, T j = (r j && st X j)) ∧ IsValid X then 1 else 0 := by
    unfold V
    rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
      (fun x => if IsValid (Fin.cons x.1 x.2 : Grid (m + 1)) ∧
        st (Fin.cons x.1 x.2 : Grid (m + 1)) = T then 1 else 0) (fun X => by simp),
      Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun r _ =>
      Finset.sum_congr rfl fun X _ => if_congr (key_lt hm r X T) rfl rfl
  rw [h1]
  exact Finset.sum_congr rfl fun r _ =>
    sum_fiber (m := m) (fun S => LOK r ∧ ∀ j, T j = (r j && S j))

theorem V_zero (T : Row) : V 0 T = if (∀ j, T j = true) then 1 else 0 := by
  have hall : ∀ X : Grid 0, (IsValid X ∧ st X = T) ↔ ∀ j, T j = true := by
    intro X
    have hv : IsValid X := ⟨fun i => Fin.elim0 i, fun j i hi => absurd hi (by omega)⟩
    have hs : st X = fun _ => true := by
      funext j
      unfold st
      rw [pb_of_ge _ 0 (by omega), pb_of_ge _ 1 (by omega), pb_of_ge _ 2 (by omega),
        pb_of_ge _ 3 (by omega)]
      rfl
    rw [hs]
    constructor
    · rintro ⟨-, h⟩ j
      rw [← h]
    · intro h
      exact ⟨hv, funext fun j => (h j).symm⟩
  unfold V
  rw [Fintype.sum_unique]
  exact if_congr (hall _) rfl rfl

theorem card_eq_sum_V (m : ℕ) :
    (Finset.univ.filter (fun g : Grid m => IsValid g)).card = ∑ T : Row, V m T := by
  rw [Finset.card_filter]
  have := sum_fiber (m := m) (fun _ => True)
  simp only [true_and, if_true] at this
  rw [← this]

theorem a_eq_card (n : ℕ) : a n = (Finset.univ.filter (fun g : Grid (n + 3) => IsValid g)).card := by
  unfold a
  congr 1
  exact Finset.filter_congr fun x _ => good_iff x


/-- The row (or the set of columns) whose entry in column `j` is bit `j` of `n`. -/
def rowN (n : ℕ) : Row := fun j => Nat.testBit n j.val

/-- The row with code `u`. -/
def row (u : Fin 128) : Row := rowN u.val

theorem two_pow_ge {j : ℕ} (hj : ¬ j < 7) : 128 ≤ 2 ^ j :=
  calc 128 = 2 ^ 7 := by norm_num
    _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem row_injective : Function.Injective row := by
  intro u v h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 7
  · exact congrFun h ⟨j, hj⟩
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le u.isLt (two_pow_ge hj)),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le v.isLt (two_pow_ge hj))]

theorem row_bijective : Function.Bijective row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective, by simp⟩

theorem sum_row (F : Row → ℕ) : ∑ r : Row, F r = ∑ u : Fin 128, F (row u) :=
  (Fintype.sum_bijective row row_bijective _ _ (fun _ => rfl)).symm

theorem bits_and (t e s : ℕ) (ht : t < 128) (he : e < 128) :
    (∀ j : Fin 7, rowN t j = (rowN e j && rowN s j)) ↔ t = e &&& s := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_land]
    by_cases hj : j < 7
    · exact h ⟨j, hj⟩
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ht (two_pow_ge hj)),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le he (two_pow_ge hj)), Bool.false_and]
  · rintro rfl j
    simp only [rowN, Nat.testBit_land]

theorem bits_sub (t s : ℕ) (ht : t < 128) :
    (∀ j : Fin 7, rowN t j = true → rowN s j = true) ↔ t &&& s = t := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_land]
    by_cases hj : j < 7
    · have hj' := h ⟨j, hj⟩
      simp only [rowN] at hj'
      cases htj : t.testBit j
      · simp
      · simp [hj' htj]
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ht (two_pow_ge hj)), Bool.false_and]
  · intro h j hj
    have h' := congrArg (fun n => Nat.testBit n j.val) h
    simp only [Nat.testBit_land] at h'
    simp only [rowN] at hj ⊢
    rw [hj] at h'
    simpa using h'

/-- The sum of `f i` over `i < n`, by recursion. -/
def rs (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => rs f n + f n

theorem rs_eq (f : ℕ → ℕ) (n : ℕ) : rs f n = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rs, ih, sum_range_succ]

theorem rs_congr (f g : ℕ → ℕ) (n : ℕ) (h : ∀ i < n, f i = g i) : rs f n = rs g n := by
  rw [rs_eq, rs_eq]
  exact sum_congr rfl fun i hi => h i (mem_range.mp hi)

theorem sum_fin (f : ℕ → ℕ) : ∑ u : Fin 128, f u.val = rs f 128 := by
  rw [rs_eq, Fin.sum_univ_eq_sum_range]

/-- The window condition of a row of width 7, on its code. -/
def goodc (e : ℕ) : Bool :=
  (!(e.testBit 0) || (e >>> 1) &&& 15 == 15) && (!(e.testBit 1) || (e >>> 2) &&& 15 == 15) &&
    (!(e.testBit 2) || (e >>> 3) &&& 15 == 15)

theorem goodc_iff_fin : ∀ u : Fin 128, (LOK (row u) ↔ goodc u.val = true) := by
  decide +kernel

theorem goodc_iff (t : ℕ) (ht : t < 128) : LOK (rowN t) ↔ goodc t = true :=
  goodc_iff_fin ⟨t, ht⟩

/-- One step of the state recursion on codes while the array has fewer than 4 rows. -/
def PsiC (f : ℕ → ℕ) (t : ℕ) : ℕ :=
  rs (fun e => if goodc e then rs (fun s => if t = e &&& s then f s else 0) 128 else 0) 128

/-- One step of the state recursion on codes once the array has at least 4 rows. -/
def PhiC (f : ℕ → ℕ) (t : ℕ) : ℕ :=
  if goodc t then rs (fun s => if t &&& s = t then f s else 0) 128 else 0

theorem PsiC_congr (f g : ℕ → ℕ) (t : ℕ) (h : ∀ s < 128, f s = g s) : PsiC f t = PsiC g t := by
  unfold PsiC
  refine rs_congr _ _ _ fun e _ => ?_
  split_ifs
  · exact rs_congr _ _ _ fun s hs => by split_ifs <;> simp [h s hs]
  · rfl

theorem PhiC_congr (f g : ℕ → ℕ) (t : ℕ) (h : ∀ s < 128, f s = g s) : PhiC f t = PhiC g t := by
  unfold PhiC
  split_ifs
  · exact rs_congr _ _ _ fun s hs => by split_ifs <;> simp [h s hs]
  · rfl

theorem v_succ_lt {m : ℕ} (hm : m < 4) (t : ℕ) (ht : t < 128) :
    V (m + 1) (rowN t) = PsiC (fun s => V m (rowN s)) t := by
  have h1 : ∀ e : Fin 128, (∑ S : Row,
      if LOK (row e) ∧ (∀ j, rowN t j = (row e j && S j)) then V m S else 0) =
      if goodc e.val then rs (fun s => if t = e.val &&& s then V m (rowN s) else 0) 128
        else 0 := by
    intro e
    rw [sum_row]
    by_cases hg : goodc e.val = true
    · rw [if_pos hg, ← sum_fin]
      have hL : LOK (row e) := (goodc_iff_fin e).2 hg
      refine sum_congr rfl fun s _ => ?_
      exact if_congr ⟨fun h => (bits_and t e.val s.val ht e.isLt).1 h.2,
        fun h => ⟨hL, (bits_and t e.val s.val ht e.isLt).2 h⟩⟩ rfl rfl
    · rw [if_neg hg]
      refine sum_eq_zero fun s _ => if_neg ?_
      rintro ⟨hL, -⟩
      exact hg ((goodc_iff_fin e).1 hL)
  rw [V_succ_lt hm, sum_row]
  unfold PsiC
  rw [← sum_fin]
  exact sum_congr rfl fun e _ => h1 e

theorem v_succ_ge {m : ℕ} (hm : 4 ≤ m) (t : ℕ) (ht : t < 128) :
    V (m + 1) (rowN t) = PhiC (fun s => V m (rowN s)) t := by
  rw [V_succ_ge hm]
  unfold PhiC
  have hg := goodc_iff t ht
  by_cases h : goodc t = true
  · rw [if_pos (hg.2 h), if_pos h, sum_row, ← sum_fin]
    refine sum_congr rfl fun s _ => ?_
    exact if_congr (bits_sub t s.val ht) rfl rfl
  · rw [if_neg (fun h' => h (hg.1 h')), if_neg h]

theorem PhiC_lin (S : Finset ℕ) (w : ℕ → ℕ) (F : ℕ → ℕ → ℕ) (t : ℕ) :
    PhiC (fun s => ∑ j ∈ S, w j * F j s) t = ∑ j ∈ S, w j * PhiC (F j) t := by
  unfold PhiC
  split_ifs with h
  · simp only [rs_eq, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun s _ => ?_
    split_ifs <;> simp
  · simp

/-- The state counts `V m` for `m ≤ 4`, on codes. -/
def TV : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1],
   [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0,
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
    1, 0, 0, 0, 1, 0, 1, 1],
   [87, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0,
    0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 9, 0,
    0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0,
    0, 9, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0,
    0, 0, 0, 7, 0, 0, 0, 5, 0, 3, 1],
   [3157, 0, 0, 0, 0, 0, 0, 0, 613, 0, 0, 0, 0, 0, 0, 0, 613, 0, 0, 0, 0, 0, 0, 0, 157, 0, 0,
    0, 0, 0, 0, 0, 613, 0, 0, 0, 0, 0, 0, 0, 157, 0, 0, 0, 0, 0, 0, 0, 157, 0, 0, 0, 0, 0, 0,
    0, 61, 0, 0, 0, 0, 0, 0, 0, 613, 0, 0, 0, 0, 0, 0, 0, 157, 0, 0, 0, 0, 0, 0, 0, 157, 0, 0,
    0, 0, 0, 0, 0, 61, 0, 0, 0, 0, 0, 0, 0, 157, 0, 0, 0, 0, 0, 0, 0, 61, 0, 0, 0, 0, 0, 0, 0,
    61, 0, 0, 0, 0, 0, 0, 0, 37, 0, 0, 0, 19, 0, 7, 1],
   [83919, 0, 0, 0, 0, 0, 0, 0, 9057, 0, 0, 0, 0, 0, 0, 0, 9057, 0, 0, 0, 0, 0, 0, 0, 1407, 0,
    0, 0, 0, 0, 0, 0, 9057, 0, 0, 0, 0, 0, 0, 0, 1407, 0, 0, 0, 0, 0, 0, 0, 1407, 0, 0, 0, 0,
    0, 0, 0, 369, 0, 0, 0, 0, 0, 0, 0, 9057, 0, 0, 0, 0, 0, 0, 0, 1407, 0, 0, 0, 0, 0, 0, 0,
    1407, 0, 0, 0, 0, 0, 0, 0, 369, 0, 0, 0, 0, 0, 0, 0, 1407, 0, 0, 0, 0, 0, 0, 0, 369, 0, 0,
    0, 0, 0, 0, 0, 369, 0, 0, 0, 0, 0, 0, 0, 175, 0, 0, 0, 65, 0, 15, 1]]

def tvf (m n : ℕ) : ℕ := (TV.getD m []).getD n 0

/-- The coefficients `w j` of `V (m + 4) = Sum_j C(m, j) w j`, on codes. -/
def WT : List (List ℕ) :=
  [[83919, 0, 0, 0, 0, 0, 0, 0, 9057, 0, 0, 0, 0, 0, 0, 0, 9057, 0, 0, 0, 0, 0, 0, 0, 1407, 0,
    0, 0, 0, 0, 0, 0, 9057, 0, 0, 0, 0, 0, 0, 0, 1407, 0, 0, 0, 0, 0, 0, 0, 1407, 0, 0, 0, 0,
    0, 0, 0, 369, 0, 0, 0, 0, 0, 0, 0, 9057, 0, 0, 0, 0, 0, 0, 0, 1407, 0, 0, 0, 0, 0, 0, 0,
    1407, 0, 0, 0, 0, 0, 0, 0, 369, 0, 0, 0, 0, 0, 0, 0, 1407, 0, 0, 0, 0, 0, 0, 0, 369, 0, 0,
    0, 0, 0, 0, 0, 369, 0, 0, 0, 0, 0, 0, 0, 175, 0, 0, 0, 65, 0, 15, 1],
   [46402, 0, 0, 0, 0, 0, 0, 0, 5584, 0, 0, 0, 0, 0, 0, 0, 5584, 0, 0, 0, 0, 0, 0, 0, 994, 0,
    0, 0, 0, 0, 0, 0, 5584, 0, 0, 0, 0, 0, 0, 0, 994, 0, 0, 0, 0, 0, 0, 0, 994, 0, 0, 0, 0, 0,
    0, 0, 256, 0, 0, 0, 0, 0, 0, 0, 5584, 0, 0, 0, 0, 0, 0, 0, 994, 0, 0, 0, 0, 0, 0, 0, 994,
    0, 0, 0, 0, 0, 0, 0, 256, 0, 0, 0, 0, 0, 0, 0, 994, 0, 0, 0, 0, 0, 0, 0, 256, 0, 0, 0, 0,
    0, 0, 0, 256, 0, 0, 0, 0, 0, 0, 0, 81, 0, 0, 0, 16, 0, 1, 0],
   [29422, 0, 0, 0, 0, 0, 0, 0, 3848, 0, 0, 0, 0, 0, 0, 0, 3848, 0, 0, 0, 0, 0, 0, 0, 610, 0,
    0, 0, 0, 0, 0, 0, 3848, 0, 0, 0, 0, 0, 0, 0, 610, 0, 0, 0, 0, 0, 0, 0, 610, 0, 0, 0, 0, 0,
    0, 0, 98, 0, 0, 0, 0, 0, 0, 0, 3848, 0, 0, 0, 0, 0, 0, 0, 610, 0, 0, 0, 0, 0, 0, 0, 610, 0,
    0, 0, 0, 0, 0, 0, 98, 0, 0, 0, 0, 0, 0, 0, 610, 0, 0, 0, 0, 0, 0, 0, 98, 0, 0, 0, 0, 0, 0,
    0, 98, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 1, 0, 0, 0],
   [19462, 0, 0, 0, 0, 0, 0, 0, 2142, 0, 0, 0, 0, 0, 0, 0, 2142, 0, 0, 0, 0, 0, 0, 0, 214, 0,
    0, 0, 0, 0, 0, 0, 2142, 0, 0, 0, 0, 0, 0, 0, 214, 0, 0, 0, 0, 0, 0, 0, 214, 0, 0, 0, 0, 0,
    0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 2142, 0, 0, 0, 0, 0, 0, 0, 214, 0, 0, 0, 0, 0, 0, 0, 214, 0,
    0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 214, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0,
    0, 18, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
   [9925, 0, 0, 0, 0, 0, 0, 0, 697, 0, 0, 0, 0, 0, 0, 0, 697, 0, 0, 0, 0, 0, 0, 0, 37, 0, 0,
    0, 0, 0, 0, 0, 697, 0, 0, 0, 0, 0, 0, 0, 37, 0, 0, 0, 0, 0, 0, 0, 37, 0, 0, 0, 0, 0, 0, 0,
    1, 0, 0, 0, 0, 0, 0, 0, 697, 0, 0, 0, 0, 0, 0, 0, 37, 0, 0, 0, 0, 0, 0, 0, 37, 0, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 37, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [3014, 0, 0, 0, 0, 0, 0, 0, 114, 0, 0, 0, 0, 0, 0, 0, 114, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0,
    0, 0, 0, 0, 114, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 114, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [468, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0],
   [24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]]

def twf (j n : ℕ) : ℕ := (WT.getD j []).getD n 0

theorem tv_zero : ∀ t < 128, tvf 0 t = if (∀ j, rowN t j = true) then 1 else 0 := by
  decide +kernel

theorem tv_step0 : ∀ t < 128, PsiC (tvf 0) t = tvf 1 t := by
  decide +kernel

theorem tv_step1 : ∀ t < 128, PsiC (tvf 1) t = tvf 2 t := by
  decide +kernel

theorem tv_step2 : ∀ t < 128, PsiC (tvf 2) t = tvf 3 t := by
  decide +kernel

theorem tv_step3 : ∀ t < 128, PsiC (tvf 3) t = tvf 4 t := by
  decide +kernel

theorem tv_step (m : ℕ) (hm : m < 4) (t : ℕ) (ht : t < 128) : PsiC (tvf m) t = tvf (m + 1) t := by
  interval_cases m
  · exact tv_step0 t ht
  · exact tv_step1 t ht
  · exact tv_step2 t ht
  · exact tv_step3 t ht

theorem tw_zero : ∀ t < 128, twf 0 t = tvf 4 t := by
  decide +kernel

theorem tw_step : ∀ j < 8, ∀ t < 128, PhiC (twf j) t = twf j t + twf (j + 1) t := by
  decide +kernel

theorem tw_eight (t : ℕ) : twf 8 t = 0 := by
  unfold twf
  rfl

theorem tw_sums : rs (twf 0) 128 = 130321 ∧ rs (twf 1) 128 = 75824 ∧ rs (twf 2) 128 = 48884 ∧
    rs (twf 3) 128 = 29387 ∧ rs (twf 4) 128 = 12939 ∧ rs (twf 5) 128 = 3482 ∧
    rs (twf 6) 128 = 492 ∧ rs (twf 7) 128 = 24 := by
  decide +kernel

theorem V_small (m : ℕ) (hm : m ≤ 4) (t : ℕ) (ht : t < 128) : V m (rowN t) = tvf m t := by
  induction m generalizing t with
  | zero => rw [V_zero, tv_zero t ht]
  | succ m ih =>
    rw [v_succ_lt (by omega) t ht,
      PsiC_congr _ (tvf m) t (fun s hs => ih (by omega) s hs), tv_step m (by omega) t ht]

theorem V_big (m : ℕ) : ∀ t < 128, V (m + 4) (rowN t) = ∑ j ∈ range 8, m.choose j * twf j t := by
  induction m with
  | zero =>
    intro t ht
    rw [Nat.zero_add, V_small 4 le_rfl t ht, ← tw_zero t ht]
    simp [Finset.sum_range_succ]
  | succ m ih =>
    intro t ht
    rw [show m + 1 + 4 = (m + 4) + 1 by omega, v_succ_ge (by omega) t ht,
      PhiC_congr _ (fun s => ∑ j ∈ range 8, m.choose j * twf j s) t (fun s hs => ih s hs),
      PhiC_lin]
    rw [Finset.sum_congr rfl (fun j hj => by rw [tw_step j (Finset.mem_range.mp hj) t ht])]
    have h8 := tw_eight t
    have p1 : (m + 1).choose 1 = m.choose 0 + m.choose 1 := Nat.choose_succ_succ m 0
    have p2 : (m + 1).choose 2 = m.choose 1 + m.choose 2 := Nat.choose_succ_succ m 1
    have p3 : (m + 1).choose 3 = m.choose 2 + m.choose 3 := Nat.choose_succ_succ m 2
    have p4 : (m + 1).choose 4 = m.choose 3 + m.choose 4 := Nat.choose_succ_succ m 3
    have p5 : (m + 1).choose 5 = m.choose 4 + m.choose 5 := Nat.choose_succ_succ m 4
    have p6 : (m + 1).choose 6 = m.choose 5 + m.choose 6 := Nat.choose_succ_succ m 5
    have p7 : (m + 1).choose 7 = m.choose 6 + m.choose 7 := Nat.choose_succ_succ m 6
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, p1, p2, p3, p4, p5, p6, p7,
      Nat.choose_zero_right, h8]
    ring

theorem a_closed (n : ℕ) :
    (a (n + 1) : ℤ) = 130321 + 75824 * (n : ℤ) + 48884 * (n.choose 2 : ℤ) +
      29387 * (n.choose 3 : ℤ) + 12939 * (n.choose 4 : ℤ) + 3482 * (n.choose 5 : ℤ) +
      492 * (n.choose 6 : ℤ) + 24 * (n.choose 7 : ℤ) := by
  have h1 : a (n + 1) = ∑ u : Fin 128, V (n + 4) (row u) := by
    rw [a_eq_card, card_eq_sum_V, sum_row]
  have h2 : a (n + 1) = ∑ j ∈ range 8, n.choose j * rs (twf j) 128 := by
    rw [h1, Finset.sum_congr rfl fun u _ => V_big n u.val u.isLt, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, sum_fin (fun t => twf j t)]
  rw [h2]
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := tw_sums
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c0, c1, c2, c3, c4, c5, c6, c7,
    Nat.choose_zero_right, Nat.choose_one_right]
  push_cast
  ring

theorem choose2 (m : ℕ) : (m.choose 2 : ℚ) = m * (m - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, Nat.choose_one_right]
    push_cast
    ring

theorem choose3 (m : ℕ) : (m.choose 3 : ℚ) = m * (m - 1) * (m - 2) / 6 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, choose2]
    push_cast
    ring

theorem choose4 (m : ℕ) : (m.choose 4 : ℚ) = m * (m - 1) * (m - 2) * (m - 3) / 24 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, choose3]
    push_cast
    ring

theorem choose5 (m : ℕ) :
    (m.choose 5 : ℚ) = m * (m - 1) * (m - 2) * (m - 3) * (m - 4) / 120 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, choose4]
    push_cast
    ring

theorem choose6 (m : ℕ) :
    (m.choose 6 : ℚ) = m * (m - 1) * (m - 2) * (m - 3) * (m - 4) * (m - 5) / 720 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, choose5]
    push_cast
    ring

theorem choose7 (m : ℕ) :
    (m.choose 7 : ℚ) = m * (m - 1) * (m - 2) * (m - 3) * (m - 4) * (m - 5) * (m - 6) / 5040 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, choose6]
    push_cast
    ring

/-- The closed form of `a (n + 1)` as a polynomial in `n`. -/
def P (x : ℚ) : ℚ :=
  130321 + 75824 * x + 48884 * (x * (x - 1) / 2) + 29387 * (x * (x - 1) * (x - 2) / 6) +
    12939 * (x * (x - 1) * (x - 2) * (x - 3) / 24) +
    3482 * (x * (x - 1) * (x - 2) * (x - 3) * (x - 4) / 120) +
    492 * (x * (x - 1) * (x - 2) * (x - 3) * (x - 4) * (x - 5) / 720) +
    24 * (x * (x - 1) * (x - 2) * (x - 3) * (x - 4) * (x - 5) * (x - 6) / 5040)

theorem closedQ (n : ℕ) : ((a (n + 1) : ℕ) : ℚ) = P n := by
  rw [show ((a (n + 1) : ℕ) : ℚ) = (((a (n + 1) : ℤ)) : ℚ) from (Int.cast_natCast _).symm,
    a_closed]
  push_cast
  rw [choose2, choose3, choose4, choose5, choose6, choose7]
  rfl

theorem recurrence (n : ℕ) (hn : 8 < n) :
    (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) +
      56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
  rw [show k + 9 - 1 = (k + 7) + 1 by omega, show k + 9 - 2 = (k + 6) + 1 by omega,
    show k + 9 - 3 = (k + 5) + 1 by omega, show k + 9 - 4 = (k + 4) + 1 by omega,
    show k + 9 - 5 = (k + 3) + 1 by omega, show k + 9 - 6 = (k + 2) + 1 by omega,
    show k + 9 - 7 = (k + 1) + 1 by omega, show k + 9 - 8 = k + 1 by omega,
    show k + 9 = (k + 8) + 1 by omega]
  have h : (((a ((k + 8) + 1) : ℤ)) : ℚ) = ((8 * (a ((k + 7) + 1) : ℤ) - 28 * a ((k + 6) + 1) +
      56 * a ((k + 5) + 1) - 70 * a ((k + 4) + 1) + 56 * a ((k + 3) + 1) -
      28 * a ((k + 2) + 1) + 8 * a ((k + 1) + 1) - a (k + 1) : ℤ) : ℚ) := by
    push_cast
    rw [closedQ, closedQ, closedQ, closedQ, closedQ, closedQ, closedQ, closedQ, closedQ]
    unfold P
    push_cast
    ring
  exact_mod_cast h

theorem a_vals : (a 1 : ℤ) = 130321 ∧ (a 2 : ℤ) = 206145 ∧ (a 3 : ℤ) = 330853 ∧
    (a 4 : ℤ) = 533832 ∧ (a 5 : ℤ) = 857408 ∧ (a 6 : ℤ) = 1360328 ∧ (a 7 : ℤ) = 2121734 ∧
    (a 8 : ℤ) = 3245653 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [a_closed]
    norm_num [Nat.choose]

open PowerSeries in
/-- The generating function, for any sequence with the right initial values and recurrence. -/
theorem gen_fun_of (f : ℕ → ℤ) (h0 : f 0 = 0) (h1 : f 1 = 130321) (h2 : f 2 = 206145)
    (h3 : f 3 = 330853) (h4 : f 4 = 533832) (h5 : f 5 = 857408) (h6 : f 6 = 1360328)
    (h7 : f 7 = 2121734) (h8 : f 8 = 3245653)
    (hrec : ∀ n, 8 < n → f n = 8 * f (n - 1) - 28 * f (n - 2) + 56 * f (n - 3) -
      70 * f (n - 4) + 56 * f (n - 5) - 28 * f (n - 6) + 8 * f (n - 7) - f (n - 8)) :
    PowerSeries.mk f * (1 - X) ^ 8 =
      X * (130321 - 836423 * X + 2330681 * X ^ 2 - 3638908 * X ^ 3 + 3428986 * X ^ 4 -
        1947234 * X ^ 5 + 616520 * X ^ 6 - 83919 * X ^ 7) := by
  have key : PowerSeries.mk f * (1 - X) ^ 8 =
      C 1 * (PowerSeries.mk f * X ^ 0) - C 8 * (PowerSeries.mk f * X ^ 1) +
        C 28 * (PowerSeries.mk f * X ^ 2) - C 56 * (PowerSeries.mk f * X ^ 3) +
        C 70 * (PowerSeries.mk f * X ^ 4) - C 56 * (PowerSeries.mk f * X ^ 5) +
        C 28 * (PowerSeries.mk f * X ^ 6) - C 8 * (PowerSeries.mk f * X ^ 7) +
        C 1 * (PowerSeries.mk f * X ^ 8) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℤ⟦X⟧) * (130321 - 836423 * X + 2330681 * X ^ 2 - 3638908 * X ^ 3 +
      3428986 * X ^ 4 - 1947234 * X ^ 5 + 616520 * X ^ 6 - 83919 * X ^ 7) =
      C 130321 * X ^ 1 - C 836423 * X ^ 2 + C 2330681 * X ^ 3 - C 3638908 * X ^ 4 +
        C 3428986 * X ^ 5 - C 1947234 * X ^ 6 + C 616520 * X ^ 7 - C 83919 * X ^ 8 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 9
  · interval_cases k <;> norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 9 := ⟨k - 9, by omega⟩
    have hr := hrec (j + 9) (by omega)
    simp only [show j + 9 - 1 = j + 8 by omega, show j + 9 - 2 = j + 7 by omega,
      show j + 9 - 3 = j + 6 by omega, show j + 9 - 4 = j + 5 by omega,
      show j + 9 - 5 = j + 4 by omega, show j + 9 - 6 = j + 3 by omega,
      show j + 9 - 7 = j + 2 by omega, show j + 9 - 8 = j + 1 by omega] at hr
    simp only [show 0 ≤ j + 9 by omega, show 1 ≤ j + 9 by omega, show 2 ≤ j + 9 by omega,
      show 3 ≤ j + 9 by omega, show 4 ≤ j + 9 by omega, show 5 ≤ j + 9 by omega,
      show 6 ≤ j + 9 by omega, show 7 ≤ j + 9 by omega, show 8 ≤ j + 9 by omega,
      show j + 9 - 0 = j + 9 by omega, show j + 9 - 1 = j + 8 by omega,
      show j + 9 - 2 = j + 7 by omega, show j + 9 - 3 = j + 6 by omega,
      show j + 9 - 4 = j + 5 by omega, show j + 9 - 5 = j + 4 by omega,
      show j + 9 - 6 = j + 3 by omega, show j + 9 - 7 = j + 2 by omega,
      show j + 9 - 8 = j + 1 by omega,
      show ¬ (j + 9 = 1) by omega, show ¬ (j + 9 = 2) by omega, show ¬ (j + 9 = 3) by omega,
      show ¬ (j + 9 = 4) by omega, show ¬ (j + 9 = 5) by omega, show ¬ (j + 9 = 6) by omega,
      show ¬ (j + 9 = 7) by omega, show ¬ (j + 9 = 8) by omega,
      if_true, if_false]
    linarith

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 8 =
      X * (130321 - 836423 * X + 2330681 * X ^ 2 - 3638908 * X ^ 3 + 3428986 * X ^ 4 -
        1947234 * X ^ 5 + 616520 * X ^ 6 - 83919 * X ^ 7) := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := a_vals
  refine gen_fun_of _ (if_pos rfl) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [if_neg (by norm_num)]
    exact v1
  · rw [if_neg (by norm_num)]
    exact v2
  · rw [if_neg (by norm_num)]
    exact v3
  · rw [if_neg (by norm_num)]
    exact v4
  · rw [if_neg (by norm_num)]
    exact v5
  · rw [if_neg (by norm_num)]
    exact v6
  · rw [if_neg (by norm_num)]
    exact v7
  · rw [if_neg (by norm_num)]
    exact v8
  · intro n hn
    rw [if_neg (show n ≠ 0 by omega), if_neg (show n - 1 ≠ 0 by omega),
      if_neg (show n - 2 ≠ 0 by omega), if_neg (show n - 3 ≠ 0 by omega),
      if_neg (show n - 4 ≠ 0 by omega), if_neg (show n - 5 ≠ 0 by omega),
      if_neg (show n - 6 ≠ 0 by omega), if_neg (show n - 7 ≠ 0 by omega),
      if_neg (show n - 8 ≠ 0 by omega)]
    exact recurrence n hn

end OMA.Helpers.A202935

theorem OMA.solution : type_of% @OMA.S_oeis_a202935.main :=
  ⟨OMA.Helpers.A202935.gen_fun, OMA.Helpers.A202935.recurrence⟩
