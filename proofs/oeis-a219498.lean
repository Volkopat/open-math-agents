import OMAStatements.S_oeis_a219498

/-!
Proof of Hardin's formula and of Barker's g.f. and recurrence for A219498 (distinct arrays
obtained from a sorted 0..1 n X 4 array by taking the minimum of each entry and its horizontal
and vertical neighbours).

1. Sorted arrays are staircases. In a sorted array a one is never followed by a zero further down
   its column (`col_up`, by strong induction on the column: such a pair in column `j` gives,
   through the row order and then the column order, such a pair in an earlier column), and a one
   has only ones to its left (`row_prefix`). Hence `A = stairArr m`, where row `i` has ones
   exactly in its first `m i` columns and `m : Fin n → Fin 5` is monotone (`sorted_stairArr`).
   Conversely every such staircase is sorted (`stairArr_sorted`), and `stairArr` is injective.
2. Taking neighbourhood minima maps `stairArr m` to `stairArr (psiT 4 m)`: row `i` keeps
   `min (m (i - 1)) (fv (m i))` ones, the row above the top row counting as full, where
   `fv = (0, 0, 1, 2, 4)` accounts for the right neighbour (`nbhdMin_stairArr`). So `a n` is the
   number of words `psiT 4 m` with `m` monotone.
3. These words are recognised by an automaton reading the rows from the top, whose state is the
   set of row lengths `m i` still possible (`allowed`, 8 states including the empty set). Its
   transitions `autNext` are checked against the definition by `decide`. Splitting off the
   first letter with `Fin.cons` gives `accCount (L + 1) q = Sum_c accCount L (autNext q c)`,
   where `accCount L q` counts the words of length `L` accepted from state `q`, and
   `a (L + 1) = Sum_c accCount L (autStart c)` (`a_succ`).
4. For `L ≥ 2`, six times `accCount L q` is a cubic polynomial in `L` with coefficients given by
   a table (`statePoly`): the induction step is a finite check of four coefficient identities
   per state (`step_facts`) and the case `L = 2` is computed. Summing over the first letter gives
   `6 a(n) = n^3 + 6 n^2 + 23 n - 42` for `n ≥ 3`, which is Hardin's formula. With `a 1 = 4` and
   `a 2 = 7`, the g.f. follows by comparing coefficients and the recurrence by substitution.
-/

namespace OMA.Helpers

open OMA.S_oeis_a219498 Finset

theorem fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

theorem fin2_lt : ∀ x y : Fin 2, x < y ↔ x = 0 ∧ y = 1 := by decide

theorem fin2_one_le : ∀ x : Fin 2, 1 ≤ x ↔ x = 1 := by decide

theorem fin2_ne : (0 : Fin 2) ≠ 1 := by decide

theorem lex_lt_iff' {m : ℕ} (x y : Fin m → Fin 2) :
    toLex x < toLex y ↔ ∃ i, (∀ j, j < i → x j = y j) ∧ x i < y i := Iff.rfl

/-- Columns of a sorted array are closed downwards: a one in column `j` stays a one further
down. -/
theorem col_up {n : ℕ} {A : Fin n → Fin 4 → Fin 2} (hA : Sorted A) :
    ∀ (j : Fin 4) (i i' : Fin n), i < i' → A i j = 1 → A i' j = 1 := by
  intro j
  induction j using WellFoundedLT.induction with
  | _ j ih =>
  intro i i' hii' hij
  by_contra hne
  have h0 : A i' j = 0 := (fin2_cases _).resolve_right hne
  have hrow : toLex (A i) ≤ toLex (A i') := hA.1 hii'.le
  have hne' : A i ≠ A i' := by
    intro h
    rw [h, h0] at hij
    exact fin2_ne hij
  obtain ⟨j0, hj0eq, hj0lt⟩ :=
    (lex_lt_iff' _ _).mp (lt_of_le_of_ne hrow (fun h => hne' (toLex_inj.mp h)))
  have hA0 : A i j0 = 0 ∧ A i' j0 = 1 := (fin2_lt _ _).mp hj0lt
  have hj0j : j0 < j := by
    rcases lt_trichotomy j0 j with h | h | h
    · exact h
    · subst h
      rw [hij] at hA0
      exact absurd hA0.1.symm fin2_ne
    · have : A i j = A i' j := hj0eq j h
      rw [hij, h0] at this
      exact absurd this.symm fin2_ne
  have hcol : toLex (fun l => A l j) ≤ toLex (fun l => A l j0) := hA.2 hj0j.le
  have hne2 : (fun l => A l j) ≠ (fun l => A l j0) := by
    intro h
    have : A i j = A i j0 := congrFun h i
    rw [hij, hA0.1] at this
    exact fin2_ne this.symm
  obtain ⟨i1, hi1eq, hi1lt⟩ :=
    (lex_lt_iff' _ _).mp (lt_of_le_of_ne hcol (fun h => hne2 (toLex_inj.mp h)))
  have hB : A i1 j = 0 ∧ A i1 j0 = 1 := (fin2_lt _ _).mp hi1lt
  have hi1i : i1 < i := by
    rcases lt_trichotomy i1 i with h | h | h
    · exact h
    · subst h
      rw [hij] at hB
      exact (fin2_ne hB.1.symm).elim
    · have : A i j = A i j0 := hi1eq i h
      rw [hij, hA0.1] at this
      exact (fin2_ne this.symm).elim
  have := ih j0 hj0j i1 i hi1i hB.2
  rw [hA0.1] at this
  exact fin2_ne this

/-- Rows of a sorted array are closed to the left: a one in column `j` has ones to its left. -/
theorem row_prefix {n : ℕ} {A : Fin n → Fin 4 → Fin 2} (hA : Sorted A) :
    ∀ (i : Fin n) (j j' : Fin 4), j' < j → A i j = 1 → A i j' = 1 := by
  intro i j j' hjj' hij
  by_contra hne
  have h0 : A i j' = 0 := (fin2_cases _).resolve_right hne
  have hcol : toLex (fun l => A l j) ≤ toLex (fun l => A l j') := hA.2 hjj'.le
  have hne2 : (fun l => A l j) ≠ (fun l => A l j') := by
    intro h
    have : A i j = A i j' := congrFun h i
    rw [hij, h0] at this
    exact fin2_ne this.symm
  obtain ⟨i1, hi1eq, hi1lt⟩ :=
    (lex_lt_iff' _ _).mp (lt_of_le_of_ne hcol (fun h => hne2 (toLex_inj.mp h)))
  have hB : A i1 j = 0 ∧ A i1 j' = 1 := (fin2_lt _ _).mp hi1lt
  have hi1i : i1 < i := by
    rcases lt_trichotomy i1 i with h | h | h
    · exact h
    · subst h
      rw [hij] at hB
      exact (fin2_ne hB.1.symm).elim
    · have : A i j = A i j' := hi1eq i h
      rw [hij, h0] at this
      exact (fin2_ne this.symm).elim
  have := col_up hA j' i1 i hi1i hB.2
  rw [h0] at this
  exact fin2_ne this

/-- The staircase array whose row `i` has ones exactly in its first `m i` columns. -/
def stairArr {n : ℕ} (m : Fin n → Fin 5) : Fin n → Fin 4 → Fin 2 :=
  fun i j => if j.val < (m i).val then 1 else 0

/-- The number of ones in a row. -/
def rowOnes (r : Fin 4 → Fin 2) : Fin 5 :=
  ⟨(r 0).val + (r 1).val + (r 2).val + (r 3).val, by
    have := (r 0).isLt; have := (r 1).isLt; have := (r 2).isLt; have := (r 3).isLt; omega⟩

theorem row_stairArr : ∀ r : Fin 4 → Fin 2,
    (∀ j j' : Fin 4, j' < j → r j = 1 → r j' = 1) →
      ∀ j : Fin 4, r j = if j.val < (rowOnes r).val then 1 else 0 := by
  decide

theorem rowOnes_mono : ∀ r r' : Fin 4 → Fin 2, (∀ j, r j = 1 → r' j = 1) →
    rowOnes r ≤ rowOnes r' := by
  decide

theorem sorted_stairArr {n : ℕ} {A : Fin n → Fin 4 → Fin 2} (hA : Sorted A) :
    ∃ m : Fin n → Fin 5, Monotone m ∧ A = stairArr m := by
  refine ⟨fun i => rowOnes (A i), ?_, ?_⟩
  · intro i i' h
    rcases h.lt_or_eq with h | h
    · exact rowOnes_mono _ _ (fun j => col_up hA j i i' h)
    · rw [h]
  · funext i j
    exact row_stairArr (A i) (row_prefix hA i) j

theorem stairArr_sorted {n : ℕ} {m : Fin n → Fin 5} (hm : Monotone m) :
    Sorted (stairArr m) := by
  constructor
  · intro i i' h
    show toLex (stairArr m i) ≤ toLex (stairArr m i')
    apply Pi.toLex_monotone
    intro j
    have := Fin.le_def.mp (hm h)
    simp only [stairArr]
    split_ifs with h1 h2 h2
    · exact le_rfl
    · omega
    · exact Fin.zero_le _
    · exact le_rfl
  · intro j j' h
    show toLex (fun i => stairArr m i j') ≤ toLex (fun i => stairArr m i j)
    apply Pi.toLex_monotone
    intro i
    have := Fin.le_def.mp h
    simp only [stairArr]
    split_ifs with h1 h2 h2
    · exact le_rfl
    · omega
    · exact Fin.zero_le _
    · exact le_rfl

theorem stairArr_injective : ∀ x y : Fin 5,
    (∀ j : Fin 4, (if j.val < x.val then (1 : Fin 2) else 0) =
      (if j.val < y.val then (1 : Fin 2) else 0)) → x = y := by
  decide

theorem stairArr_inj {n : ℕ} {m m' : Fin n → Fin 5} (h : stairArr m = stairArr m') :
    m = m' := by
  funext i
  exact stairArr_injective (m i) (m' i) (fun j => congrFun (congrFun h i) j)

/-- Length of an eroded row: `fv x` ones remain of a row with `x` leading ones. -/
def fv : Fin 5 → Fin 5 := ![0, 0, 1, 2, 4]

theorem fv_spec : ∀ (x : Fin 5) (j : Fin 4),
    j.val < (fv x).val ↔ (j.val < x.val ∧ (j.val = 3 ∨ j.val + 1 < x.val)) := by
  decide

/-- The eroded staircase: row `i` keeps `min (m (i - 1)) (fv (m i))` ones, where the row above
row 0 is taken to have length `t`. -/
def psiT {n : ℕ} (t : Fin 5) (m : Fin n → Fin 5) (i : Fin n) : Fin 5 :=
  min ((Fin.cons t m : Fin (n + 1) → Fin 5) (Fin.castSucc i)) (fv (m i))

theorem nbhdMin_eq_one {n : ℕ} (A : Fin n → Fin 4 → Fin 2) (i : Fin n) (j : Fin 4) :
    nbhdMin A i j = 1 ↔ ∀ p : Fin n × Fin 4, Near i j p → A p.1 p.2 = 1 := by
  unfold nbhdMin
  rw [← fin2_one_le, Finset.le_inf_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, fin2_one_le]

theorem stairArr_eq_one {n : ℕ} (m : Fin n → Fin 5) (i : Fin n) (j : Fin 4) :
    stairArr m i j = 1 ↔ j.val < (m i).val := by
  unfold stairArr
  split_ifs with h
  · simp [h]
  · simp [h]

theorem erode_iff {n : ℕ} {m : Fin n → Fin 5} (hm : Monotone m) (i : Fin n) (j : Fin 4) :
    (∀ p : Fin n × Fin 4, Near i j p → p.2.val < (m p.1).val) ↔
      j.val < (psiT 4 m i).val := by
  unfold psiT
  rw [Fin.coe_min, lt_min_iff]
  constructor
  · intro h
    have hself : j.val < (m i).val := h (i, j) (Or.inl ⟨rfl, rfl⟩)
    have hright : j.val = 3 ∨ j.val + 1 < (m i).val := by
      by_cases h3 : j.val = 3
      · exact Or.inl h3
      · right
        have := h (i, ⟨j.val + 1, by omega⟩) (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩))
        simpa using this
    refine ⟨?_, ?_⟩
    · by_cases hi : i.val = 0
      · have : (Fin.castSucc i : Fin (n + 1)) = 0 := Fin.ext (by simp [hi])
        rw [this, Fin.cons_zero]
        exact j.isLt
      · have hp := h (⟨i.val - 1, by omega⟩, j)
          (Or.inr (Or.inr ⟨rfl, Or.inl (by simp; omega)⟩))
        have : (Fin.castSucc i : Fin (n + 1)) = Fin.succ ⟨i.val - 1, by omega⟩ :=
          Fin.ext (by simp; omega)
        rw [this, Fin.cons_succ]
        simpa using hp
    · exact (fv_spec (m i) j).mpr ⟨hself, hright⟩
  · rintro ⟨hprev, hfv⟩
    obtain ⟨hself, hright⟩ := (fv_spec (m i) j).mp hfv
    intro p hp
    unfold Near at hp
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
    · rw [h1, h2]
      exact hself
    · rw [h1]
      omega
    · rw [h1]
      have := p.2.isLt
      omega
    · have : (Fin.castSucc i : Fin (n + 1)) = Fin.succ p.1 := Fin.ext (by simp; omega)
      rw [this, Fin.cons_succ] at hprev
      rw [h1]
      exact hprev
    · have hle : m i ≤ m p.1 := hm (Fin.le_def.mpr (by omega))
      have := Fin.le_def.mp hle
      rw [h1]
      omega

theorem nbhdMin_stairArr {n : ℕ} {m : Fin n → Fin 5} (hm : Monotone m) :
    nbhdMin (stairArr m) = stairArr (psiT 4 m) := by
  funext i j
  have key : nbhdMin (stairArr m) i j = 1 ↔ stairArr (psiT 4 m) i j = 1 := by
    rw [nbhdMin_eq_one, stairArr_eq_one, ← erode_iff hm]
    simp only [stairArr_eq_one]
  rcases fin2_cases (nbhdMin (stairArr m) i j) with h | h <;>
    rcases fin2_cases (stairArr (psiT 4 m) i j) with h' | h'
  · rw [h, h']
  · rw [h'] at key
    rw [key.mpr rfl] at h
    exact absurd h.symm fin2_ne
  · rw [h] at key
    rw [key.mp rfl] at h'
    exact absurd h' fin2_ne.symm
  · rw [h, h']

theorem psiT_cons {L : ℕ} (t s : Fin 5) (m : Fin L → Fin 5) :
    psiT t (Fin.cons s m : Fin (L + 1) → Fin 5) = Fin.cons (min t (fv s)) (psiT s m) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [psiT]
  | succ k => simp only [psiT, Fin.cons_succ, Fin.castSucc_succ]

theorem mono_cons {β : Type*} [Preorder β] {n : ℕ} (x : β) (f : Fin n → β) :
    Monotone (Fin.cons x f : Fin (n + 1) → β) ↔ (∀ i, x ≤ f i) ∧ Monotone f := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · simpa using h (Fin.zero_le i.succ)
    · simpa using h (Fin.succ_le_succ_iff.mpr hij)
  · rintro ⟨h1, h2⟩ i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact le_rfl
      | succ j => simpa using h1 j
    | succ i =>
      cases j using Fin.cases with
      | zero => exact absurd hij (by simp)
      | succ j => simpa using h2 (Fin.succ_le_succ_iff.mp hij)

theorem mono_cons2 {L : ℕ} (t s : Fin 5) (m : Fin L → Fin 5) :
    Monotone (Fin.cons t (Fin.cons s m : Fin (L + 1) → Fin 5) : Fin (L + 2) → Fin 5) ↔
      t ≤ s ∧ Monotone (Fin.cons s m : Fin (L + 1) → Fin 5) := by
  rw [mono_cons]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by simpa using h1 0, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, h2⟩
    have := h2 (Fin.zero_le i)
    rw [Fin.cons_zero] at this
    exact le_trans h1 this

/-- The states of the automaton: which last row lengths are still possible. -/
def allowed : Fin 8 → Fin 5 → Bool := ![
  ![false, false, true, false, false],
  ![false, false, false, true, false],
  ![false, false, false, false, true],
  ![true, true, false, false, false],
  ![false, false, false, true, true],
  ![false, false, true, true, true],
  ![true, true, true, true, true],
  ![false, false, false, false, false]]

/-- The transitions of the automaton. -/
def autNext : Fin 8 → Fin 5 → Fin 8 := ![
  ![7, 0, 4, 7, 7],
  ![7, 7, 1, 2, 7],
  ![7, 7, 7, 7, 2],
  ![6, 5, 7, 7, 7],
  ![7, 7, 1, 2, 2],
  ![7, 0, 4, 2, 2],
  ![6, 5, 4, 2, 2],
  ![7, 7, 7, 7, 7]]

/-- The state after reading the first eroded row length. -/
def autStart : Fin 5 → Fin 8 := ![3, 0, 1, 7, 2]

theorem autNext_spec : ∀ (q : Fin 8) (c s : Fin 5),
    allowed (autNext q c) s = true ↔
      ∃ t, allowed q t = true ∧ t ≤ s ∧ min t (fv s) = c := by
  decide

theorem autStart_spec : ∀ c s : Fin 5, allowed (autStart c) s = true ↔ fv s = c := by
  decide

theorem nonempty_spec : ∀ q : Fin 8, (∃ t, allowed q t = true) ↔ q ≠ 7 := by
  decide

theorem min_four : ∀ x : Fin 5, min 4 x = x := by decide

/-- `w` is the eroded continuation of some monotone continuation of a row length allowed by
state `q`. -/
def Accepts {L : ℕ} (q : Fin 8) (w : Fin L → Fin 5) : Prop :=
  ∃ t, allowed q t = true ∧
    ∃ m : Fin L → Fin 5, Monotone (Fin.cons t m : Fin (L + 1) → Fin 5) ∧ psiT t m = w

theorem accepts_cons {L : ℕ} (q : Fin 8) (c : Fin 5) (w : Fin L → Fin 5) :
    Accepts q (Fin.cons c w : Fin (L + 1) → Fin 5) ↔ Accepts (autNext q c) w := by
  unfold Accepts
  constructor
  · rintro ⟨t, ht, m, hmono, hpsi⟩
    rw [← Fin.cons_self_tail m] at hmono hpsi
    rw [psiT_cons, Fin.cons_inj] at hpsi
    rw [mono_cons2] at hmono
    exact ⟨m 0, (autNext_spec q c (m 0)).mpr ⟨t, ht, hmono.1, hpsi.1⟩, Fin.tail m, hmono.2,
      hpsi.2⟩
  · rintro ⟨s, hs, m', hmono, hpsi⟩
    obtain ⟨t, ht, hts, hc⟩ := (autNext_spec q c s).mp hs
    refine ⟨t, ht, Fin.cons s m', (mono_cons2 t s m').mpr ⟨hts, hmono⟩, ?_⟩
    rw [psiT_cons, hc, hpsi]

theorem accepts_nil (q : Fin 8) (w : Fin 0 → Fin 5) : Accepts q w ↔ q ≠ 7 := by
  rw [← nonempty_spec]
  unfold Accepts
  constructor
  · rintro ⟨t, ht, -⟩
    exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩
    refine ⟨t, ht, w, ?_, funext (fun i => Fin.elim0 i)⟩
    intro x y _
    have hx := x.isLt
    have hy := y.isLt
    rw [show x = y from Fin.ext (by omega)]

theorem image_iff {L : ℕ} (b : Fin (L + 1) → Fin 5) :
    (∃ m : Fin (L + 1) → Fin 5, Monotone m ∧ psiT 4 m = b) ↔
      Accepts (autStart (b 0)) (Fin.tail b) := by
  constructor
  · rintro ⟨m, hmono, hpsi⟩
    rw [← Fin.cons_self_tail m] at hmono hpsi
    rw [← Fin.cons_self_tail b, psiT_cons, Fin.cons_inj, min_four] at hpsi
    exact ⟨m 0, (autStart_spec _ _).mpr hpsi.1, Fin.tail m, hmono, hpsi.2⟩
  · rintro ⟨s, hs, m', hmono, hpsi⟩
    refine ⟨Fin.cons s m', hmono, ?_⟩
    rw [psiT_cons, hpsi, min_four, (autStart_spec _ _).mp hs, Fin.cons_self_tail]

/-- The number of words of length `L` accepted from state `q`. -/
noncomputable def accCount (L : ℕ) (q : Fin 8) : ℕ := by
  classical
  exact ∑ w : Fin L → Fin 5, if Accepts q w then 1 else 0

theorem accCount_zero (q : Fin 8) : accCount 0 q = if q = 7 then 0 else 1 := by
  classical
  unfold accCount
  rw [Fintype.sum_unique]
  by_cases h : q = 7
  · rw [if_pos h, if_neg]
    rw [accepts_nil]
    exact fun h' => h' h
  · rw [if_neg h, if_pos]
    rw [accepts_nil]
    exact h

theorem accCount_succ (L : ℕ) (q : Fin 8) :
    accCount (L + 1) q = ∑ c : Fin 5, accCount L (autNext q c) := by
  classical
  unfold accCount
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 5).symm _
    (fun x => if Accepts q (Fin.cons x.1 x.2 : Fin (L + 1) → Fin 5) then 1 else 0)
    (fun w => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun w _ => ?_
  exact if_congr (accepts_cons q c w) rfl rfl

theorem stairArr_mem {n : ℕ} (b : Fin n → Fin 5) (hb : ∃ m, Monotone m ∧ psiT 4 m = b) :
    ∃ A, Sorted A ∧ nbhdMin A = stairArr b := by
  obtain ⟨m, hm, rfl⟩ := hb
  exact ⟨stairArr m, stairArr_sorted hm, nbhdMin_stairArr hm⟩

theorem a_succ (L : ℕ) : a (L + 1) = ∑ c : Fin 5, accCount L (autStart c) := by
  classical
  have h1 : a (L + 1) =
      Fintype.card {b : Fin (L + 1) → Fin 5 // ∃ m, Monotone m ∧ psiT 4 m = b} := by
    unfold a
    apply Fintype.card_congr
    refine (Equiv.ofBijective (fun b => ⟨stairArr b.1, stairArr_mem b.1 b.2⟩) ⟨?_, ?_⟩).symm
    · intro x y hxy
      exact Subtype.ext (stairArr_inj (congrArg Subtype.val hxy))
    · rintro ⟨B, A, hA, hB⟩
      obtain ⟨m, hm, rfl⟩ := sorted_stairArr hA
      exact ⟨⟨psiT 4 m, m, hm, rfl⟩,
        Subtype.ext (show stairArr (psiT 4 m) = B by rw [← hB, nbhdMin_stairArr hm])⟩
  rw [h1, Fintype.card_subtype, Finset.card_filter]
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 5).symm _
    (fun x => if Accepts (autStart x.1) x.2 then 1 else 0)
    (fun b => by
      simp only [Fin.consEquiv, Equiv.coe_fn_symm_mk]
      exact if_congr (image_iff b) rfl rfl), Fintype.sum_prod_type]
  rfl

/-- The same counts, computed by the automaton recursion. -/
def wordCount : ℕ → Fin 8 → ℕ
  | 0, q => if q = 7 then 0 else 1
  | L + 1, q => ∑ c : Fin 5, wordCount L (autNext q c)

theorem accCount_eq (L : ℕ) : ∀ q, accCount L q = wordCount L q := by
  induction L with
  | zero => intro q; rw [accCount_zero]; rfl
  | succ L ih => intro q; rw [accCount_succ]; simp only [wordCount, ih]

/-- Coefficient of `L ^ 3` in six times the number of words of length `L ≥ 2` accepted from
each state. -/
def cf3 : Fin 8 → ℤ := ![0, 0, 0, 1, 0, 0, 1, 0]

/-- Coefficient of `L ^ 2`. -/
def cf2 : Fin 8 → ℤ := ![3, 0, 0, 6, 0, 3, 6, 0]

/-- Coefficient of `L`. -/
def cf1 : Fin 8 → ℤ := ![9, 6, 0, 23, 6, 9, 29, 0]

/-- Constant coefficient. -/
def cf0 : Fin 8 → ℤ := ![0, 6, 6, -24, 12, 12, -6, 0]

/-- Six times the number of words of length `L ≥ 2` accepted from state `q`. -/
def statePoly (q : Fin 8) (L : ℤ) : ℤ := cf3 q * L ^ 3 + cf2 q * L ^ 2 + cf1 q * L + cf0 q

theorem step_facts : ∀ q : Fin 8,
    (∑ c : Fin 5, cf3 (autNext q c)) = cf3 q ∧
    (∑ c : Fin 5, cf2 (autNext q c)) = 3 * cf3 q + cf2 q ∧
    (∑ c : Fin 5, cf1 (autNext q c)) = 3 * cf3 q + 2 * cf2 q + cf1 q ∧
    (∑ c : Fin 5, cf0 (autNext q c)) = cf3 q + cf2 q + cf1 q + cf0 q := by
  decide +kernel

theorem base_facts : ∀ q : Fin 8, 6 * (wordCount 2 q : ℤ) = statePoly q 2 := by
  decide +kernel

theorem wordCount_closed (L : ℕ) (hL : 2 ≤ L) :
    ∀ q : Fin 8, 6 * (wordCount L q : ℤ) = statePoly q L := by
  induction L, hL using Nat.le_induction with
  | base => exact base_facts
  | succ L hL ih =>
    intro q
    have hsum : 6 * (wordCount (L + 1) q : ℤ) =
        ∑ c : Fin 5, statePoly (autNext q c) L := by
      simp only [wordCount]
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => ih (autNext q c)
    rw [hsum]
    simp only [statePoly, Finset.sum_add_distrib, ← Finset.sum_mul]
    obtain ⟨h3, h2, h1, h0⟩ := step_facts q
    rw [h3, h2, h1, h0]
    push_cast
    ring

theorem sum_facts :
    (∑ c : Fin 5, cf3 (autStart c)) = 1 ∧ (∑ c : Fin 5, cf2 (autStart c)) = 9 ∧
    (∑ c : Fin 5, cf1 (autStart c)) = 38 ∧ (∑ c : Fin 5, cf0 (autStart c)) = -12 := by
  decide +kernel

theorem a_closed6 (L : ℕ) (hL : 2 ≤ L) :
    6 * (a (L + 1) : ℤ) = (L : ℤ) ^ 3 + 9 * L ^ 2 + 38 * L - 12 := by
  rw [a_succ]
  push_cast
  rw [Finset.mul_sum]
  simp only [accCount_eq, wordCount_closed L hL]
  simp only [statePoly, Finset.sum_add_distrib, ← Finset.sum_mul]
  obtain ⟨h3, h2, h1, h0⟩ := sum_facts
  rw [h3, h2, h1, h0]
  ring

theorem closedQ (n : ℕ) (hn : 2 < n) :
    (a n : ℚ) = (1 / 6) * (n : ℚ) ^ 3 + 1 * (n : ℚ) ^ 2 + (23 / 6) * (n : ℚ) - 7 := by
  obtain ⟨L, rfl⟩ : ∃ L, n = L + 1 := ⟨n - 1, by omega⟩
  have h : ((6 * (a (L + 1) : ℤ) : ℤ) : ℚ) =
      (((L : ℤ) ^ 3 + 9 * L ^ 2 + 38 * L - 12 : ℤ) : ℚ) := by
    rw [a_closed6 L (by omega)]
  push_cast at h ⊢
  linear_combination (1 / 6 : ℚ) * h

theorem a_one : a 1 = 4 := by
  rw [a_succ]
  simp only [accCount_eq]
  decide

theorem a_two : a 2 = 7 := by
  rw [a_succ]
  simp only [accCount_eq]
  decide

theorem recurrence (n : ℕ) (hn : 6 < n) :
    (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  have h : ((a n : ℤ) : ℚ) =
      ((4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) : ℤ) : ℚ) := by
    push_cast
    rw [closedQ n (by omega), closedQ (n - 1) (by omega), closedQ (n - 2) (by omega),
      closedQ (n - 3) (by omega), closedQ (n - 4) (by omega)]
    push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega]
    ring
  exact_mod_cast h

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 4 =
      X * (4 - 9 * X + 14 * X ^ 2 - 11 * X ^ 3 + 2 * X ^ 4 + X ^ 5) := by
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hF
  have key : PowerSeries.mk F * (1 - X) ^ 4 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 4 * (PowerSeries.mk F * X ^ 1) +
        C 6 * (PowerSeries.mk F * X ^ 2) - C 4 * (PowerSeries.mk F * X ^ 3) +
        C 1 * (PowerSeries.mk F * X ^ 4) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (4 - 9 * X + 14 * X ^ 2 - 11 * X ^ 3 + 2 * X ^ 4 + X ^ 5) =
      C 4 * X ^ 1 - C 9 * X ^ 2 + C 14 * X ^ 3 - C 11 * X ^ 4 + C 2 * X ^ 5 + C 1 * X ^ 6 := by
    simp only [map_one, map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 7
  · interval_cases k <;> norm_num [hF, a_one, a_two, closedQ]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 7 := ⟨k - 7, by omega⟩
    simp only [show 0 ≤ j + 7 by omega, show 1 ≤ j + 7 by omega, show 2 ≤ j + 7 by omega,
      show 3 ≤ j + 7 by omega, show 4 ≤ j + 7 by omega,
      show j + 7 - 0 = j + 7 by omega, show j + 7 - 1 = j + 6 by omega,
      show j + 7 - 2 = j + 5 by omega, show j + 7 - 3 = j + 4 by omega,
      show j + 7 - 4 = j + 3 by omega,
      show ¬ (j + 7 = 1) by omega, show ¬ (j + 7 = 2) by omega, show ¬ (j + 7 = 3) by omega,
      show ¬ (j + 7 = 4) by omega, show ¬ (j + 7 = 5) by omega, show ¬ (j + 7 = 6) by omega,
      show ¬ (j + 7 = 0) by omega, show ¬ (j + 6 = 0) by omega, show ¬ (j + 5 = 0) by omega,
      show ¬ (j + 4 = 0) by omega, show ¬ (j + 3 = 0) by omega, if_true, if_false, hF]
    rw [closedQ (j + 7) (by omega), closedQ (j + 6) (by omega), closedQ (j + 5) (by omega),
      closedQ (j + 4) (by omega), closedQ (j + 3) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a219498.main :=
  ⟨fun n hn => OMA.Helpers.closedQ n hn, OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
