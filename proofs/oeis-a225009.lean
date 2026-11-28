import OMAStatements.S_oeis_a225009

/-!
Proof of the three formulas for A225009 (n X 7 0..1 arrays with unimodal rows and nondecreasing
columns).

Rows. A row `r` has the code `rc225 r < 128` (bit `j` is the entry in column `j`). It is
unimodal iff a three-state automaton reading 0...0 1...1 0...0 accepts its bits (`lineOK_iff`, a
finite check over the 128 codes). Two rows satisfy `BlockOK u v` iff every bit of the code of
`u` is at most the corresponding bit of the code of `v` (`block_iff`).

States. The state of an array with `m` rows is the code of its last row (the zero row if
`m = 0`) when the array is good, and 128 (dead) otherwise. Appending a row with code `c` changes
the state `s` to `tau225 s c` (`st_snoc`), and an array is good iff its state is below 128.

Counting. `N m s` is the number of arrays with `m` rows in state `s`. `N 0` is the indicator of
the state 0, and `N (m + 1) t` is the sum of `N m s` over the predecessors `s` of `t` (the codes
whose bits lie below those of `t`, when `t` is a unimodal row). Eight vectors `K 0, ..., K 7`
with `K 0` the indicator of the state 0, `M (K j) = K j + K (j + 1)` and `K 8 = 0` (finite
checks) give `N k = Sum_{j < 8} C(k, j) K j` for all `k`, hence
`a k = 1 + 28 k + 182 C(k,2) + 532 C(k,3) + 833 C(k,4) + 728 C(k,5) + 336 C(k,6) + 64 C(k,7)`,
which is Hardin's polynomial. The recurrence and the generating function follow from it.
-/

namespace OMA.Helpers

open OMA.S_oeis_a225009 Finset

/-! ### Rows and their codes -/

/-- A row of an n X 7 array. -/
abbrev Row225 := Fin 7 → Fin 2

/-- The code of a row: bit `j` is the entry in column `j`. -/
def rc225 (r : Row225) : ℕ :=
  (r 0).val + 2 * (r 1).val + 4 * (r 2).val + 8 * (r 3).val + 16 * (r 4).val +
    32 * (r 5).val + 64 * (r 6).val

/-- The row with code `c < 128`. -/
def rowOf225 (c : ℕ) : Row225 := fun j => ⟨c / 2 ^ j.val % 2, Nat.mod_lt _ (by norm_num)⟩

theorem rc225_lt (r : Row225) : rc225 r < 128 := by
  unfold rc225
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  have h2 := (r 2).isLt
  have h3 := (r 3).isLt
  have h4 := (r 4).isLt
  have h5 := (r 5).isLt
  have h6 := (r 6).isLt
  omega

theorem rowOf225_rc (r : Row225) : rowOf225 (rc225 r) = r := by
  funext j
  apply Fin.ext
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  have h2 := (r 2).isLt
  have h3 := (r 3).isLt
  have h4 := (r 4).isLt
  have h5 := (r 5).isLt
  have h6 := (r 6).isLt
  fin_cases j <;> (simp [rowOf225, rc225]; try omega)

theorem rc225_bits (x : Row225) : rc225 x % 2 = (x 0).val ∧ rc225 x / 2 % 2 = (x 1).val ∧
    rc225 x / 4 % 2 = (x 2).val ∧ rc225 x / 8 % 2 = (x 3).val ∧
    rc225 x / 16 % 2 = (x 4).val ∧ rc225 x / 32 % 2 = (x 5).val ∧
    rc225 x / 64 % 2 = (x 6).val := by
  unfold rc225
  have h0 := (x 0).isLt
  have h1 := (x 1).isLt
  have h2 := (x 2).isLt
  have h3 := (x 3).isLt
  have h4 := (x 4).isLt
  have h5 := (x 5).isLt
  have h6 := (x 6).isLt
  omega

instance lineOKDec225 (u : Row225) : Decidable (LineOK u) :=
  inferInstanceAs (Decidable (∃ k : Fin 7, (∀ i j : Fin 7, i ≤ j → j ≤ k → u i ≤ u j) ∧
    (∀ i j : Fin 7, k ≤ i → i ≤ j → u j ≤ u i)))

/-- One step of the automaton for the words 0...0 1...1 0...0 (state 3 rejects). -/
def uniStep (d x : ℕ) : ℕ :=
  if d = 0 then (if x = 0 then 0 else 1)
  else if d = 1 then (if x = 1 then 1 else 2)
  else if d = 2 then (if x = 0 then 2 else 3)
  else 3

/-- The automaton state reached on the seven bits of the code `c`. -/
def rowRun225 (c : ℕ) : ℕ :=
  uniStep (uniStep (uniStep (uniStep (uniStep (uniStep (uniStep 0 (c % 2)) (c / 2 % 2))
    (c / 4 % 2)) (c / 8 % 2)) (c / 16 % 2)) (c / 32 % 2)) (c / 64 % 2)

theorem lineOK_check : ∀ c < 128, (LineOK (rowOf225 c) ↔ rowRun225 c < 3) := by
  decide +kernel

theorem lineOK_iff (r : Row225) : LineOK r ↔ rowRun225 (rc225 r) < 3 := by
  have h := lineOK_check (rc225 r) (rc225_lt r)
  rwa [rowOf225_rc] at h

/-- Every bit of `s` is at most the corresponding bit of `c` (seven bits). -/
def BitsLe (s c : ℕ) : Prop :=
  s % 2 ≤ c % 2 ∧ s / 2 % 2 ≤ c / 2 % 2 ∧ s / 4 % 2 ≤ c / 4 % 2 ∧ s / 8 % 2 ≤ c / 8 % 2 ∧
    s / 16 % 2 ≤ c / 16 % 2 ∧ s / 32 % 2 ≤ c / 32 % 2 ∧ s / 64 % 2 ≤ c / 64 % 2

instance bitsLeDec (s c : ℕ) : Decidable (BitsLe s c) :=
  inferInstanceAs (Decidable (s % 2 ≤ c % 2 ∧ s / 2 % 2 ≤ c / 2 % 2 ∧ s / 4 % 2 ≤ c / 4 % 2 ∧
    s / 8 % 2 ≤ c / 8 % 2 ∧ s / 16 % 2 ≤ c / 16 % 2 ∧ s / 32 % 2 ≤ c / 32 % 2 ∧
    s / 64 % 2 ≤ c / 64 % 2))

theorem forall_fin_seven (P : Fin 7 → Prop) :
    (∀ j, P j) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 ∧ P 5 ∧ P 6 := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩ j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6

theorem block_iff (u v : Row225) : BlockOK u v ↔ BitsLe (rc225 u) (rc225 v) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := rc225_bits u
  obtain ⟨b0, b1, b2, b3, b4, b5, b6⟩ := rc225_bits v
  unfold BlockOK BitsLe
  rw [a0, a1, a2, a3, a4, a5, a6, b0, b1, b2, b3, b4, b5, b6, forall_fin_seven]
  simp only [Fin.le_iff_val_le_val]

/-! ### Appending a row -/

/-- The last row of an array, or the zero row if there is none. -/
def lastRow225 {m : ℕ} (A : Fin m → Row225) : Row225 :=
  if h : 0 < m then A ⟨m - 1, by omega⟩ else fun _ => 0

theorem lastRow225_snoc {m : ℕ} (A : Fin m → Row225) (x : Row225) :
    lastRow225 (Fin.snoc A x : Fin (m + 1) → Row225) = x := by
  unfold lastRow225
  rw [dif_pos (Nat.succ_pos m)]
  have e : (⟨m + 1 - 1, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp)
  rw [e, Fin.snoc_last]

theorem rows_snoc225 {m : ℕ} (A : Fin m → Row225) (x : Row225) :
    (∀ i, LineOK ((Fin.snoc A x : Fin (m + 1) → Row225) i)) ↔
      (∀ i, LineOK (A i)) ∧ LineOK x := by
  rw [Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem blocks_snoc225 {m : ℕ} (A : Fin m → Row225) (x : Row225) :
    (∀ i j : Fin (m + 1), (j : ℕ) = i + 1 →
      BlockOK ((Fin.snoc A x : Fin (m + 1) → Row225) i)
        ((Fin.snoc A x : Fin (m + 1) → Row225) j)) ↔
      (∀ i j : Fin m, (j : ℕ) = i + 1 → BlockOK (A i) (A j)) ∧ BlockOK (lastRow225 A) x := by
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, ?_⟩
    · have := h i.castSucc j.castSucc (by simp [hij])
      rwa [Fin.snoc_castSucc, Fin.snoc_castSucc] at this
    · unfold lastRow225
      split_ifs with hm
      · have := h (Fin.castSucc ⟨m - 1, by omega⟩) (Fin.last m) (by simp; omega)
        rwa [Fin.snoc_castSucc, Fin.snoc_last] at this
      · intro j
        exact Fin.zero_le _
  · rintro ⟨hA, hx⟩ i j hij
    cases j using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last]
      cases i using Fin.lastCases with
      | last => simp at hij
      | cast i =>
        rw [Fin.snoc_castSucc]
        have hm : 0 < m := Fin.pos i
        have hi : i = ⟨m - 1, by omega⟩ := Fin.ext (by simp at hij ⊢; omega)
        unfold lastRow225 at hx
        rw [dif_pos hm] at hx
        rw [hi]
        exact hx
    | cast j =>
      cases i using Fin.lastCases with
      | last =>
        simp at hij
        omega
      | cast i =>
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact hA i j (by simpa using hij)

theorem good_snoc225 {m : ℕ} (A : Fin m → Row225) (x : Row225) :
    Good (Fin.snoc A x : Fin (m + 1) → Row225) ↔
      Good A ∧ LineOK x ∧ BlockOK (lastRow225 A) x := by
  unfold Good
  rw [rows_snoc225 A x, blocks_snoc225 A x]
  tauto

/-! ### The array automaton -/

/-- The state of an array: the code of its last row if it is good, 128 otherwise. -/
noncomputable def st225 {m : ℕ} (A : Fin m → Row225) : ℕ := by
  classical
  exact if Good A then rc225 (lastRow225 A) else 128

/-- The transition on the row with code `c` (128 is the dead state). -/
def tau225 (s c : ℕ) : ℕ := if s < 128 ∧ rowRun225 c < 3 ∧ BitsLe s c then c else 128

theorem st225_snoc {m : ℕ} (A : Fin m → Row225) (x : Row225) :
    st225 (Fin.snoc A x : Fin (m + 1) → Row225) = tau225 (st225 A) (rc225 x) := by
  classical
  unfold st225
  rw [lastRow225_snoc]
  by_cases hG : Good A
  · rw [if_pos hG]
    unfold tau225
    by_cases hc : LineOK x ∧ BlockOK (lastRow225 A) x
    · rw [if_pos ((good_snoc225 A x).mpr ⟨hG, hc⟩),
        if_pos ⟨rc225_lt _, (lineOK_iff x).mp hc.1, (block_iff _ _).mp hc.2⟩]
    · rw [if_neg (fun h => hc ((good_snoc225 A x).mp h).2),
        if_neg (fun h => hc ⟨(lineOK_iff x).mpr h.2.1, (block_iff _ _).mpr h.2.2⟩)]
  · rw [if_neg hG, if_neg (fun h => hG ((good_snoc225 A x).mp h).1)]
    unfold tau225
    rw [if_neg (fun h => absurd h.1 (lt_irrefl _))]

theorem good_iff225 {m : ℕ} (A : Fin m → Row225) : Good A ↔ st225 A < 128 := by
  classical
  unfold st225
  by_cases h : Good A
  · rw [if_pos h]
    exact ⟨fun _ => rc225_lt _, fun _ => h⟩
  · rw [if_neg h]
    exact ⟨fun h' => absurd h' h, fun h' => absurd h' (lt_irrefl _)⟩

theorem st225_lt {m : ℕ} (A : Fin m → Row225) : st225 A < 129 := by
  classical
  unfold st225
  have := rc225_lt (lastRow225 A)
  split_ifs <;> omega

theorem st225_zero (A : Fin 0 → Row225) : st225 A = 0 := by
  classical
  unfold st225
  rw [if_pos ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩]
  unfold lastRow225
  rw [dif_neg (lt_irrefl 0)]
  rfl

/-! ### Counting -/

open Classical in
theorem a_sum225 (m : ℕ) : a m = ∑ A : Fin m → Row225, if Good A then 1 else 0 := by
  classical
  unfold a
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]

theorem sum_snoc225 (m : ℕ) (F : (Fin m → Row225) → Row225 → ℕ) :
    ∑ B : Fin (m + 1) → Row225, F (Fin.init B) (B (Fin.last m)) =
      ∑ β : Fin m → Row225, ∑ γ : Row225, F β γ := by
  calc ∑ B : Fin (m + 1) → Row225, F (Fin.init B) (B (Fin.last m))
      = ∑ p : Row225 × (Fin m → Row225), F p.2 p.1 :=
        (Fintype.sum_equiv (Fin.snocEquiv (fun _ => Row225)) (fun p => F p.2 p.1) _
          (fun p => by
            rw [show (Fin.snocEquiv (fun _ => Row225)) p = Fin.snoc p.2 p.1 from rfl,
              Fin.init_snoc, Fin.snoc_last])).symm
    _ = ∑ γ : Row225, ∑ β : Fin m → Row225, F β γ := Fintype.sum_prod_type' (fun γ β => F β γ)
    _ = ∑ β : Fin m → Row225, ∑ γ : Row225, F β γ := Finset.sum_comm

theorem sum_row225 (F : ℕ → ℕ) : ∑ γ : Row225, F (rc225 γ) = ∑ c ∈ range 128, F c := by
  refine Finset.sum_nbij' rc225 rowOf225 (fun γ _ => Finset.mem_range.mpr (rc225_lt γ))
    (fun _ _ => Finset.mem_univ _) (fun γ _ => rowOf225_rc γ) (fun c hc => ?_) (fun _ _ => rfl)
  have hc' := Finset.mem_range.mp hc
  unfold rc225 rowOf225
  simp
  omega

theorem sum_fiber225 {X : Type*} [Fintype X] (r : X → ℕ) (hr : ∀ x, r x < 129) (h : ℕ → ℕ) :
    ∑ x, h (r x) = ∑ s ∈ range 129, (∑ x, if r x = s then 1 else 0) * h s := by
  simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (hr x))]

/-- The number of rows leading from the state `s` to the state `t`. -/
def cnt225 (s t : ℕ) : ℕ := ∑ c ∈ range 128, if tau225 s c = t then 1 else 0

/-- The number of arrays with `m` rows in the state `s`. -/
noncomputable def N225 (m s : ℕ) : ℕ := ∑ A : Fin m → Row225, if st225 A = s then 1 else 0

/-- One step of the counts of the live states. -/
def Mop225 (f : ℕ → ℕ) (t : ℕ) : ℕ := ∑ s ∈ range 128, f s * cnt225 s t

/-- The total count of the live states. -/
def Aop225 (f : ℕ → ℕ) : ℕ := ∑ s ∈ range 128, f s

theorem cnt225_eq (s t : ℕ) (hs : s < 128) (ht : t < 128) :
    cnt225 s t = if rowRun225 t < 3 ∧ BitsLe s t then 1 else 0 := by
  unfold cnt225
  rw [Finset.sum_eq_single t]
  · unfold tau225
    by_cases hc : rowRun225 t < 3 ∧ BitsLe s t
    · rw [if_pos (show s < 128 ∧ rowRun225 t < 3 ∧ BitsLe s t from ⟨hs, hc⟩), if_pos rfl,
        if_pos hc]
    · rw [if_neg (show ¬ (s < 128 ∧ rowRun225 t < 3 ∧ BitsLe s t) from fun h => hc h.2),
        if_neg hc, if_neg (show (128 : ℕ) ≠ t by omega)]
  · intro c _ hct
    unfold tau225
    split_ifs with h1 h2 <;> first | rfl | exact absurd h2 hct | omega
  · intro h
    exact absurd (Finset.mem_range.mpr ht) h

theorem cnt225_dead (t : ℕ) (ht : t < 128) : cnt225 128 t = 0 := by
  unfold cnt225
  refine Finset.sum_eq_zero fun c _ => if_neg ?_
  unfold tau225
  rw [if_neg (fun h => absurd h.1 (lt_irrefl _))]
  omega

theorem a_eq225 (m : ℕ) : a m = Aop225 (N225 m) := by
  classical
  have h1 : a m = ∑ A : Fin m → Row225, if st225 A < 128 then 1 else 0 := by
    rw [a_sum225]
    exact Finset.sum_congr rfl fun A _ => if_congr (good_iff225 A) rfl rfl
  rw [h1]
  unfold Aop225 N225
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.sum_ite_eq]
  by_cases h : st225 A < 128
  · rw [if_pos h, if_pos (Finset.mem_range.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (Finset.mem_range.mp h'))]

theorem N225_zero (s : ℕ) : N225 0 s = if s = 0 then 1 else 0 := by
  unfold N225
  rw [Fintype.sum_unique, st225_zero]
  by_cases h : s = 0
  · subst h
    rfl
  · rw [if_neg (Ne.symm h), if_neg h]

theorem N225_succ (m t : ℕ) (ht : t < 128) : N225 (m + 1) t = Mop225 (N225 m) t := by
  have h0 : N225 (m + 1) t = ∑ B : Fin (m + 1) → Row225,
      if tau225 (st225 (Fin.init B)) (rc225 (B (Fin.last m))) = t then 1 else 0 := by
    unfold N225
    refine Finset.sum_congr rfl fun B _ => ?_
    have h := st225_snoc (Fin.init B) (B (Fin.last m))
    rw [Fin.snoc_init_self] at h
    rw [h]
  have h3 : ∀ β : Fin m → Row225,
      (∑ γ : Row225, if tau225 (st225 β) (rc225 γ) = t then 1 else 0) = cnt225 (st225 β) t :=
    fun β => sum_row225 (fun c => if tau225 (st225 β) c = t then 1 else 0)
  rw [h0, sum_snoc225 m (fun β γ => if tau225 (st225 β) (rc225 γ) = t then 1 else 0),
    Finset.sum_congr rfl (fun β _ => h3 β),
    sum_fiber225 (fun β : Fin m → Row225 => st225 β) st225_lt (fun s => cnt225 s t),
    Finset.sum_range_succ, cnt225_dead t ht, mul_zero, add_zero]
  rfl

/-! ### Predecessor lists -/

/-- The number of occurrences of `s` in a list. -/
def occ225 : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: L, s => (if p = s then 1 else 0) + occ225 L s

/-- The sum of `f` over the entries of a list. -/
def lsum225 : List ℕ → (ℕ → ℕ) → ℕ
  | [], _ => 0
  | p :: L, f => f p + lsum225 L f

theorem sum_occ225 (f : ℕ → ℕ) (L : List ℕ) (h : ∀ p ∈ L, p < 128) :
    ∑ s ∈ range 128, f s * occ225 L s = lsum225 L f := by
  induction L with
  | nil => simp [occ225, lsum225]
  | cons p L ih =>
    have ih' := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have hp : p < 128 := h p (List.mem_cons.mpr (Or.inl rfl))
    have h1 : ∑ s ∈ range 128, f s * (if p = s then 1 else 0) = f p := by
      rw [Finset.sum_eq_single p]
      · rw [if_pos rfl, mul_one]
      · intro b _ hb
        rw [if_neg (Ne.symm hb), mul_zero]
      · intro hn
        exact absurd (Finset.mem_range.mpr hp) hn
    simp only [occ225, lsum225, mul_add, Finset.sum_add_distrib, ih', h1]

def kTab225 : List (List ℕ) :=
  [[
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [
    0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1],
   [
    0, 0, 0, 2, 0, 0, 2, 5, 0, 0, 0, 0, 2, 0, 5, 9, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 5, 0, 9, 14,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 9, 0, 14,
    20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 14, 0,
    20, 27],
   [
    0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 4, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 16,
    41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 16, 0,
    41, 85, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0,
    41, 0, 85, 155],
   [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 44,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 44,
    146, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 44, 0,
    146, 377],
   [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16,
    112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0,
    112, 456],
   [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32,
    272],
   [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64]]

def predTab225 : List (List ℕ) :=
  [[0],
   [0, 1],
   [0, 2],
   [0, 1, 2, 3],
   [0, 4],
   [],
   [0, 2, 4, 6],
   [0, 1, 2, 3, 4, 5, 6, 7],
   [0, 8],
   [],
   [],
   [],
   [0, 4, 8, 12],
   [],
   [0, 2, 4, 6, 8, 10, 12, 14],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
   [0, 16],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [0, 8, 16, 24],
   [],
   [],
   [],
   [0, 4, 8, 12, 16, 20, 24, 28],
   [],
   [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 31],
   [0, 32],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [0, 16, 32, 48],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [0, 8, 16, 24, 32, 40, 48, 56],
   [],
   [],
   [],
   [0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60],
   [],
   [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48,
    50, 52, 54, 56, 58, 60, 62],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
    50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63],
   [0, 64],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [0, 32, 64, 96],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [0, 16, 32, 48, 64, 80, 96, 112],
   [],
   [],
   [],
   [],
   [],
   [],
   [],
   [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104, 112, 120],
   [],
   [],
   [],
   [0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 68, 72, 76, 80, 84, 88, 92, 96,
    100, 104, 108, 112, 116, 120, 124],
   [],
   [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48,
    50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94, 96,
    98, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 120, 122, 124, 126],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
    50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73,
    74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97,
    98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116,
    117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]]

/-- The predecessor list of the state `t`. -/
def pred225 (t : ℕ) : List ℕ := predTab225.getD t []

theorem pred225_check : ∀ t < 128, ∀ s < 128,
    (if rowRun225 t < 3 ∧ BitsLe s t then 1 else 0) = occ225 (pred225 t) s := by
  decide +kernel

theorem pred225_lt : ∀ t < 128, ∀ p ∈ pred225 t, p < 128 := by
  decide +kernel

/-- One step of the counts, through the predecessor lists. -/
def Mq225 (f : ℕ → ℕ) (t : ℕ) : ℕ := lsum225 (pred225 t) f

theorem Mop225_eq (f : ℕ → ℕ) (t : ℕ) (ht : t < 128) : Mop225 f t = Mq225 f t := by
  unfold Mop225 Mq225
  rw [← sum_occ225 f (pred225 t) (pred225_lt t ht)]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' := Finset.mem_range.mp hs
  rw [cnt225_eq s t hs' ht, pred225_check t ht s hs']

/-! ### The closed form -/

/-- The vector `K j` on the live states (0 for `j ≥ 8`). -/
def K225 (j s : ℕ) : ℕ := (kTab225.getD j []).getD s 0

theorem K225_zero_check : ∀ s < 128, K225 0 s = if s = 0 then 1 else 0 := by
  decide +kernel

theorem K225_step_check : ∀ j < 8, ∀ s < 128, Mq225 (K225 j) s = K225 j s + K225 (j + 1) s := by
  decide +kernel

theorem K225_sum_check : Aop225 (K225 0) = 1 ∧ Aop225 (K225 1) = 28 ∧ Aop225 (K225 2) = 182 ∧
    Aop225 (K225 3) = 532 ∧ Aop225 (K225 4) = 833 ∧ Aop225 (K225 5) = 728 ∧
    Aop225 (K225 6) = 336 ∧ Aop225 (K225 7) = 64 := by
  decide +kernel

theorem K225_eight (s : ℕ) : K225 8 s = 0 := rfl

theorem Mop225_congr {f g : ℕ → ℕ} (h : ∀ s < 128, f s = g s) (t : ℕ) :
    Mop225 f t = Mop225 g t := by
  unfold Mop225
  exact Finset.sum_congr rfl fun s hs => by rw [h s (Finset.mem_range.mp hs)]

theorem Aop225_congr {f g : ℕ → ℕ} (h : ∀ s < 128, f s = g s) : Aop225 f = Aop225 g := by
  unfold Aop225
  exact Finset.sum_congr rfl fun s hs => by rw [h s (Finset.mem_range.mp hs)]

theorem Mop225_lin (S : Finset ℕ) (c : ℕ → ℕ) (F : ℕ → ℕ → ℕ) (t : ℕ) :
    Mop225 (fun s => ∑ j ∈ S, c j * F j s) t = ∑ j ∈ S, c j * Mop225 (F j) t := by
  unfold Mop225
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem Aop225_lin (S : Finset ℕ) (c : ℕ → ℕ) (F : ℕ → ℕ → ℕ) :
    Aop225 (fun s => ∑ j ∈ S, c j * F j s) = ∑ j ∈ S, c j * Aop225 (F j) := by
  unfold Aop225
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

theorem N225_closed (k : ℕ) : ∀ s < 128, N225 k s = ∑ j ∈ range 8, k.choose j * K225 j s := by
  induction k with
  | zero =>
    intro s hs
    rw [N225_zero, ← K225_zero_check s hs]
    simp [Finset.sum_range_succ]
  | succ k ih =>
    intro s hs
    rw [N225_succ k s hs, Mop225_congr (g := fun s => ∑ j ∈ range 8, k.choose j * K225 j s) ih,
      Mop225_lin]
    rw [Finset.sum_congr rfl (fun j hj => by
      rw [Mop225_eq _ s hs, K225_step_check j (Finset.mem_range.mp hj) s hs])]
    have h8 := K225_eight s
    have p1 : (k + 1).choose 1 = k.choose 0 + k.choose 1 := Nat.choose_succ_succ k 0
    have p2 : (k + 1).choose 2 = k.choose 1 + k.choose 2 := Nat.choose_succ_succ k 1
    have p3 : (k + 1).choose 3 = k.choose 2 + k.choose 3 := Nat.choose_succ_succ k 2
    have p4 : (k + 1).choose 4 = k.choose 3 + k.choose 4 := Nat.choose_succ_succ k 3
    have p5 : (k + 1).choose 5 = k.choose 4 + k.choose 5 := Nat.choose_succ_succ k 4
    have p6 : (k + 1).choose 6 = k.choose 5 + k.choose 6 := Nat.choose_succ_succ k 5
    have p7 : (k + 1).choose 7 = k.choose 6 + k.choose 7 := Nat.choose_succ_succ k 6
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, p1, p2, p3, p4, p5, p6, p7,
      Nat.choose_zero_right, h8]
    ring

theorem a225_closed (k : ℕ) : a k = 1 + 28 * k + 182 * k.choose 2 + 532 * k.choose 3 +
    833 * k.choose 4 + 728 * k.choose 5 + 336 * k.choose 6 + 64 * k.choose 7 := by
  rw [a_eq225, Aop225_congr (g := fun s => ∑ j ∈ range 8, k.choose j * K225 j s) (N225_closed k),
    Aop225_lin]
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := K225_sum_check
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c0, c1, c2, c3, c4, c5, c6, c7,
    Nat.choose_zero_right, Nat.choose_one_right]
  ring

theorem choose2_q (m : ℕ) : (m.choose 2 : ℚ) = m * (m - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, Nat.choose_one_right]
    push_cast
    ring

theorem choose3_q (m : ℕ) : (m.choose 3 : ℚ) = m * (m - 1) * (m - 2) / 6 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, choose2_q]
    push_cast
    ring

theorem choose4_q (m : ℕ) : (m.choose 4 : ℚ) = m * (m - 1) * (m - 2) * (m - 3) / 24 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, choose3_q]
    push_cast
    ring

theorem choose5_q (m : ℕ) :
    (m.choose 5 : ℚ) = m * (m - 1) * (m - 2) * (m - 3) * (m - 4) / 120 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, choose4_q]
    push_cast
    ring

theorem choose6_q (m : ℕ) :
    (m.choose 6 : ℚ) = m * (m - 1) * (m - 2) * (m - 3) * (m - 4) * (m - 5) / 720 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, choose5_q]
    push_cast
    ring

theorem choose7_q (m : ℕ) : (m.choose 7 : ℚ) =
    m * (m - 1) * (m - 2) * (m - 3) * (m - 4) * (m - 5) * (m - 6) / 5040 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, choose6_q]
    push_cast
    ring

/-- Hardin's polynomial, for every `n` (also `n = 0`). -/
theorem a225_closedQ (n : ℕ) : (a n : ℚ) =
    (4 / 315) * (n : ℚ) ^ 7 + (1 / 5) * (n : ℚ) ^ 6 + (58 / 45) * (n : ℚ) ^ 5 +
      (35 / 8) * (n : ℚ) ^ 4 + (1507 / 180) * (n : ℚ) ^ 3 + (357 / 40) * (n : ℚ) ^ 2 +
      (2027 / 420) * (n : ℚ) + 1 := by
  rw [a225_closed]
  push_cast
  rw [choose2_q, choose3_q, choose4_q, choose5_q, choose6_q, choose7_q]
  ring

theorem a225_recurrence (n : ℕ) (hn : 9 ≤ n) :
    (a n : ℤ) = 8 * (a (n - 1) : ℤ) - 28 * (a (n - 2) : ℤ) + 56 * (a (n - 3) : ℤ) -
      70 * (a (n - 4) : ℤ) + 56 * (a (n - 5) : ℤ) - 28 * (a (n - 6) : ℤ) +
      8 * (a (n - 7) : ℤ) - (a (n - 8) : ℤ) := by
  have h : ((a n : ℤ) : ℚ) = ((8 * (a (n - 1) : ℤ) - 28 * (a (n - 2) : ℤ) +
      56 * (a (n - 3) : ℤ) - 70 * (a (n - 4) : ℤ) + 56 * (a (n - 5) : ℤ) -
      28 * (a (n - 6) : ℤ) + 8 * (a (n - 7) : ℤ) - (a (n - 8) : ℤ) : ℤ) : ℚ) := by
    push_cast
    rw [a225_closedQ n, a225_closedQ (n - 1), a225_closedQ (n - 2), a225_closedQ (n - 3),
      a225_closedQ (n - 4), a225_closedQ (n - 5), a225_closedQ (n - 6), a225_closedQ (n - 7),
      a225_closedQ (n - 8)]
    push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega,
      show 8 ≤ n by omega]
    ring
  exact_mod_cast h

open PowerSeries in
theorem a225_gen_fun_mul :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 8 =
        X * (29 + 7 * X + 63 * X ^ 2 - 70 * X ^ 3 + 56 * X ^ 4 - 28 * X ^ 5 + 8 * X ^ 6 -
          X ^ 7) := by
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hF
  have key : PowerSeries.mk F * (1 - X) ^ 8 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 8 * (PowerSeries.mk F * X ^ 1) +
        C 28 * (PowerSeries.mk F * X ^ 2) - C 56 * (PowerSeries.mk F * X ^ 3) +
        C 70 * (PowerSeries.mk F * X ^ 4) - C 56 * (PowerSeries.mk F * X ^ 5) +
        C 28 * (PowerSeries.mk F * X ^ 6) - C 8 * (PowerSeries.mk F * X ^ 7) +
        C 1 * (PowerSeries.mk F * X ^ 8) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (29 + 7 * X + 63 * X ^ 2 - 70 * X ^ 3 + 56 * X ^ 4 - 28 * X ^ 5 +
      8 * X ^ 6 - X ^ 7) =
      C 29 * X ^ 1 + C 7 * X ^ 2 + C 63 * X ^ 3 - C 70 * X ^ 4 + C 56 * X ^ 5 -
        C 28 * X ^ 6 + C 8 * X ^ 7 - C 1 * X ^ 8 := by
    simp only [map_one, map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  have v1 : (a 1 : ℚ) = 29 := by
    rw [a225_closedQ 1]
    norm_num
  have v2 : (a 2 : ℚ) = 239 := by
    rw [a225_closedQ 2]
    norm_num
  have v3 : (a 3 : ℚ) = 1163 := by
    rw [a225_closedQ 3]
    norm_num
  have v4 : (a 4 : ℚ) = 4166 := by
    rw [a225_closedQ 4]
    norm_num
  have v5 : (a 5 : ℚ) = 12174 := by
    rw [a225_closedQ 5]
    norm_num
  have v6 : (a 6 : ℚ) = 30738 := by
    rw [a225_closedQ 6]
    norm_num
  have v7 : (a 7 : ℚ) = 69498 := by
    rw [a225_closedQ 7]
    norm_num
  have v8 : (a 8 : ℚ) = 144111 := by
    rw [a225_closedQ 8]
    norm_num
  by_cases hk : k < 9
  · interval_cases k <;> norm_num [hF, v1, v2, v3, v4, v5, v6, v7, v8]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 9 := ⟨k - 9, by omega⟩
    simp only [show 0 ≤ j + 9 by omega, show 1 ≤ j + 9 by omega, show 2 ≤ j + 9 by omega,
      show 3 ≤ j + 9 by omega, show 4 ≤ j + 9 by omega, show 5 ≤ j + 9 by omega,
      show 6 ≤ j + 9 by omega, show 7 ≤ j + 9 by omega, show 8 ≤ j + 9 by omega,
      show j + 9 - 0 = j + 9 by omega, show j + 9 - 1 = j + 8 by omega,
      show j + 9 - 2 = j + 7 by omega, show j + 9 - 3 = j + 6 by omega,
      show j + 9 - 4 = j + 5 by omega, show j + 9 - 5 = j + 4 by omega,
      show j + 9 - 6 = j + 3 by omega, show j + 9 - 7 = j + 2 by omega,
      show j + 9 - 8 = j + 1 by omega, show ¬ (j + 9 = 0) by omega,
      show ¬ (j + 9 = 1) by omega, show ¬ (j + 9 = 2) by omega, show ¬ (j + 9 = 3) by omega,
      show ¬ (j + 9 = 4) by omega, show ¬ (j + 9 = 5) by omega, show ¬ (j + 9 = 6) by omega,
      show ¬ (j + 9 = 7) by omega, show ¬ (j + 9 = 8) by omega, show ¬ (j + 1 = 0) by omega,
      show ¬ (j + 2 = 0) by omega, show ¬ (j + 3 = 0) by omega, show ¬ (j + 4 = 0) by omega,
      show ¬ (j + 5 = 0) by omega, show ¬ (j + 6 = 0) by omega, show ¬ (j + 7 = 0) by omega,
      show ¬ (j + 8 = 0) by omega, if_true, if_false, hF]
    rw [a225_closedQ (j + 9), a225_closedQ (j + 8), a225_closedQ (j + 7), a225_closedQ (j + 6),
      a225_closedQ (j + 5), a225_closedQ (j + 4), a225_closedQ (j + 3), a225_closedQ (j + 2),
      a225_closedQ (j + 1)]
    push_cast
    ring

theorem a225_gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  unfold G
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  exact a225_gen_fun_mul

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a225009.main :=
  ⟨OMA.Helpers.a225_recurrence, OMA.Helpers.a225_gen_fun,
    fun n _ => OMA.Helpers.a225_closedQ n⟩
