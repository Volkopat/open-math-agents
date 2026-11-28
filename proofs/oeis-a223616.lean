import OMAStatements.S_oeis_a223616

/-!
Proof of Barker's g.f. and recurrence for A223616 (n X 4 0..1 arrays whose rows and columns are
unimodal).

Words. For a word `t` with entries in 0..1, `NoGap t` says that no entry 0 lies between two
entries 1. A word of length at least 1 is unimodal iff `NoGap t` holds (`unimodal_iff`): a peak is
any position of an entry 1, or any position if there is none. The state `cs t` of a word is 0 if
it is 0...0, 1 if it is 0...01...1 with an entry 1, 2 if it is 0...01...10...0 with an entry 1
and last entry 0, and 3 if `NoGap t` fails. Appending a letter `x` changes it to
`cstep (cs t) x` (`cs_snoc`, from `allZ_snoc`, `up_snoc` and `noGap_snoc`), and `cs t < 3` iff
`NoGap t` (`cs_lt_three`).

Arrays. A row `r` has the code `rc r < 16`; it is unimodal iff the automaton accepts its entries
(`unimodal_row`, a finite check). The state `st A` of an array `A` is the code
`d0 + 3 d1 + 9 d2 + 27 d3 < 81` of the states of its four columns if all its rows are unimodal
and no column state is 3, and 81 (dead) otherwise. Adding a row `x` at the bottom changes it to
`tau (st A) (rc x)` (`st_snoc`, with the finite check `chk_tau`), and an array with at least one
row is counted by `a` iff its state is below 81 (`good_iff`).

Counting. Let `N m s` be the number of arrays with `m` rows in the state `s`. Then `N 0` is the
indicator of the state 0 (`N_zero`), `N (m + 1) = Mop (N m)` on the live states (`N_succ`), and
`a (m + 1)` is the sum of `N (m + 1)` over the 81 live states (`a_eq`). The transfer counts
`cnt s t` are read off predecessor lists (`chk_pl`, `Mop_eq`). Vectors `K 0, ..., K 8` with
`K 0` the indicator of the state 0, `Mop (K j) = K j + K (j + 1)` and `K 9 = 0` (finite checks)
give, by induction with Pascal's rule, `N k = Sum_{j < 9} C(k, j) K j` for every `k`
(`N_closed`). Summing over the live states, for `n ≥ 1`
`a n = 1 + 10 n + 100 C(n, 2) + 545 C(n, 3) + 1645 C(n, 4) + 2868 C(n, 5) + 2894 C(n, 6) +
1576 C(n, 7) + 360 C(n, 8)` (`a_closed`), which is Hardin's octic (`closedQ`). The recurrence
for `n > 9` follows by substituting it (all of `n - 9, ..., n` are at least 1), and the
generating function by comparing coefficients: those of x^0, ..., x^9 from the values
a(1), ..., a(9), the higher ones vanish as ninth differences of a polynomial of degree 8.
Model. The proof works with arrays as functions `Fin n → Fin 4 → Fin 2` and the count `aW n`
of those whose rows and columns have a peak position (`UniW`, `GoodA`). The statement counts
lists of rows instead, with unimodality of a list of naturals given by a split point. For a word
with entries in 0..1 that list condition is again `NoGap` (`listU_iff`), so `List.ofFn` is a
bijection between the arrays counted by `aW n` and the lists counted by the statement for every
`n ≥ 1` (`isSol_iff`, `a_bridge`). The statement's g.f. is the series of `a (n + 1)`, obtained
from ours by cancelling the factor `x`.
-/

namespace OMA.Helpers

open Finset

/-! ### Array model: arrays as functions, peaks as positions -/

/-- The word `s` with entries in 0..1 has a peak position `k`: it is weakly increasing up to `k`
and weakly decreasing from `k` on. -/
def UniW {m : ℕ} (s : Fin m → Fin 2) : Prop :=
  ∃ k : Fin m, (∀ i j : Fin m, i ≤ j → j ≤ k → s i ≤ s j) ∧
    (∀ i j : Fin m, k ≤ i → i ≤ j → s j ≤ s i)

/-- Every row and every column of the array `A` (rows `A i`) has a peak position. -/
def GoodA {n : ℕ} (A : Fin n → Fin 4 → Fin 2) : Prop :=
  (∀ i, UniW (A i)) ∧ ∀ j, UniW (fun i => A i j)

/-- The number of such arrays with `n` rows. -/
noncomputable def aW (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun A : Fin n → Fin 4 → Fin 2 => GoodA A)).card

/-! ### Words with entries in 0..1 -/

/-- All entries of the word `t` are 0. -/
def AllZ {m : ℕ} (t : Fin m → Fin 2) : Prop := ∀ i, t i = 0

/-- After an entry 1 of `t`, every later entry is 1 (the word is 0...01...1). -/
def Up {m : ℕ} (t : Fin m → Fin 2) : Prop := ∀ i j, i < j → t i = 1 → t j = 1

/-- No entry 0 of `t` lies between two entries 1. -/
def NoGap {m : ℕ} (t : Fin m → Fin 2) : Prop :=
  ∀ i j k, i < j → j < k → t i = 1 → t k = 1 → t j = 1

theorem fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem fin2_ne_one {x : Fin 2} (h : x ≠ 1) : x = 0 := (fin2_cases x).resolve_right h

theorem fin2_ne_zero {x : Fin 2} (h : x ≠ 0) : x = 1 := (fin2_cases x).resolve_left h

theorem fin2_zero_le (x : Fin 2) : 0 ≤ x := by
  rcases fin2_cases x with rfl | rfl <;> decide

theorem fin2_le_one (x : Fin 2) : x ≤ 1 := by
  rcases fin2_cases x with rfl | rfl <;> decide

theorem fin2_eq_one_of_le {x : Fin 2} (h : 1 ≤ x) : x = 1 := le_antisymm (fin2_le_one x) h

theorem allZ_up {m : ℕ} {t : Fin m → Fin 2} (h : AllZ t) : Up t := by
  intro i j _ hi
  rw [h i] at hi
  exact absurd hi (by decide)

theorem allZ_noGap {m : ℕ} {t : Fin m → Fin 2} (h : AllZ t) : NoGap t := by
  intro i j k _ _ hi _
  rw [h i] at hi
  exact absurd hi (by decide)

theorem allZ_snoc {m : ℕ} (t : Fin m → Fin 2) (x : Fin 2) :
    AllZ (Fin.snoc t x : Fin (m + 1) → Fin 2) ↔ AllZ t ∧ x = 0 := by
  unfold AllZ
  rw [Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem up_snoc {m : ℕ} (t : Fin m → Fin 2) (x : Fin 2) :
    Up (Fin.snoc t x : Fin (m + 1) → Fin 2) ↔ Up t ∧ (x = 0 → AllZ t) := by
  constructor
  · intro h
    refine ⟨fun i j hij hi => ?_, fun hx i => ?_⟩
    · have := h i.castSucc j.castSucc (Fin.castSucc_lt_castSucc_iff.mpr hij)
        (by rw [Fin.snoc_castSucc]; exact hi)
      rwa [Fin.snoc_castSucc] at this
    · by_contra hne
      have := h i.castSucc (Fin.last m) (Fin.castSucc_lt_last i)
        (by rw [Fin.snoc_castSucc]; exact fin2_ne_zero hne)
      rw [Fin.snoc_last, hx] at this
      exact absurd this (by decide)
  · rintro ⟨hU, hZ⟩ i j hij hi
    cases j using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last]
      cases i using Fin.lastCases with
      | last => exact absurd hij (lt_irrefl _)
      | cast i =>
        rw [Fin.snoc_castSucc] at hi
        rcases fin2_cases x with rfl | rfl
        · rw [hZ rfl i] at hi
          exact absurd hi (by decide)
        · rfl
    | cast j =>
      rw [Fin.snoc_castSucc]
      cases i using Fin.lastCases with
      | last => exact absurd hij (not_lt.mpr (Fin.le_last _))
      | cast i =>
        rw [Fin.snoc_castSucc] at hi
        exact hU i j (Fin.castSucc_lt_castSucc_iff.mp hij) hi

theorem noGap_snoc {m : ℕ} (t : Fin m → Fin 2) (x : Fin 2) :
    NoGap (Fin.snoc t x : Fin (m + 1) → Fin 2) ↔ NoGap t ∧ (x = 1 → Up t) := by
  constructor
  · intro h
    refine ⟨fun i j k hij hjk hi hk => ?_, fun hx i j hij hi => ?_⟩
    · have := h i.castSucc j.castSucc k.castSucc (Fin.castSucc_lt_castSucc_iff.mpr hij)
        (Fin.castSucc_lt_castSucc_iff.mpr hjk) (by rw [Fin.snoc_castSucc]; exact hi)
        (by rw [Fin.snoc_castSucc]; exact hk)
      rwa [Fin.snoc_castSucc] at this
    · have := h i.castSucc j.castSucc (Fin.last m) (Fin.castSucc_lt_castSucc_iff.mpr hij)
        (Fin.castSucc_lt_last j) (by rw [Fin.snoc_castSucc]; exact hi)
        (by rw [Fin.snoc_last]; exact hx)
      rwa [Fin.snoc_castSucc] at this
  · rintro ⟨hN, hU⟩ i j k hij hjk hi hk
    cases j using Fin.lastCases with
    | last => exact absurd hjk (not_lt.mpr (Fin.le_last _))
    | cast j =>
      cases i using Fin.lastCases with
      | last => exact absurd (hij.trans (Fin.castSucc_lt_last j)) (lt_irrefl _)
      | cast i =>
        rw [Fin.snoc_castSucc] at hi ⊢
        have hij' := Fin.castSucc_lt_castSucc_iff.mp hij
        cases k using Fin.lastCases with
        | last =>
          rw [Fin.snoc_last] at hk
          exact hU hk i j hij' hi
        | cast k =>
          rw [Fin.snoc_castSucc] at hk
          exact hN i j k hij' (Fin.castSucc_lt_castSucc_iff.mp hjk) hi hk

theorem unimodal_iff {m : ℕ} (t : Fin (m + 1) → Fin 2) : UniW t ↔ NoGap t := by
  constructor
  · rintro ⟨k, hinc, hdec⟩ i j l hij hjl hi hl
    rcases le_total j k with hjk | hkj
    · have := hinc i j hij.le hjk
      rw [hi] at this
      exact fin2_eq_one_of_le this
    · have := hdec j l hkj hjl.le
      rw [hl] at this
      exact fin2_eq_one_of_le this
  · intro h
    by_cases hz : ∃ p, t p = 1
    · obtain ⟨p, hp⟩ := hz
      refine ⟨p, fun i j hij hjp => ?_, fun i j hpi hij => ?_⟩
      · rcases fin2_cases (t i) with h0 | h1
        · rw [h0]
          exact fin2_zero_le _
        · rcases eq_or_lt_of_le hij with rfl | hij'
          · exact le_rfl
          · rcases eq_or_lt_of_le hjp with rfl | hjp'
            · rw [h1, hp]
            · rw [h1, h i j p hij' hjp' h1 hp]
      · rcases fin2_cases (t j) with h0 | h1
        · rw [h0]
          exact fin2_zero_le _
        · rcases eq_or_lt_of_le hij with rfl | hij'
          · exact le_rfl
          · rcases eq_or_lt_of_le hpi with rfl | hpi'
            · rw [h1, hp]
            · rw [h1, h p i j hpi' hij' hp h1]
    · simp only [not_exists] at hz
      refine ⟨0, fun i j _ _ => ?_, fun i j _ _ => ?_⟩
      · rw [fin2_ne_one (hz i)]
        exact fin2_zero_le _
      · rw [fin2_ne_one (hz j)]
        exact fin2_zero_le _

/-! ### The column automaton -/

/-- The state of a word: 0 if it is 0...0, 1 if it is 0...01...1 with at least one 1, 2 if it is
0...01...10...0 with at least one 1 and ending with 0, and 3 if some entry 0 lies between two
entries 1. -/
noncomputable def cs {m : ℕ} (t : Fin m → Fin 2) : ℕ := by
  classical
  exact if NoGap t then (if AllZ t then 0 else if Up t then 1 else 2) else 3

/-- One step of the automaton reading the letter `x`. -/
def cstep (d x : ℕ) : ℕ :=
  if d = 0 then (if x = 0 then 0 else 1)
  else if d = 1 then (if x = 1 then 1 else 2)
  else if d = 2 then (if x = 0 then 2 else 3)
  else 3

theorem cs_snoc {m : ℕ} (t : Fin m → Fin 2) (x : Fin 2) :
    cs (Fin.snoc t x : Fin (m + 1) → Fin 2) = cstep (cs t) x.val := by
  classical
  unfold cs
  simp only [noGap_snoc, allZ_snoc, up_snoc]
  have hZU : AllZ t → Up t := allZ_up
  have hZN : AllZ t → NoGap t := allZ_noGap
  by_cases hN : NoGap t <;> by_cases hZ : AllZ t <;> by_cases hU : Up t <;>
    rcases fin2_cases x with rfl | rfl <;> simp_all [cstep]

theorem cs_lt_four {m : ℕ} (t : Fin m → Fin 2) : cs t < 4 := by
  classical
  unfold cs
  split_ifs <;> norm_num

theorem cs_lt_three {m : ℕ} (t : Fin m → Fin 2) : cs t < 3 ↔ NoGap t := by
  classical
  unfold cs
  split_ifs with h1 h2 h3 <;> simp_all

theorem cs_zero (t : Fin 0 → Fin 2) : cs t = 0 := by
  classical
  unfold cs
  rw [if_pos (show NoGap t from fun i => Fin.elim0 i),
    if_pos (show AllZ t from fun i => Fin.elim0 i)]

/-! ### Rows and the array automaton -/

/-- A row of an n X 4 array. -/
abbrev Row := Fin 4 → Fin 2

/-- The code `r 0 + 2 r 1 + 4 r 2 + 8 r 3` of the row `r`. -/
def rc (r : Row) : ℕ := (r 0).val + 2 * (r 1).val + 4 * (r 2).val + 8 * (r 3).val

/-- The row with code `c < 16`. -/
def rowOf (c : ℕ) : Row := fun j => ⟨c / 2 ^ j.val % 2, Nat.mod_lt _ (by norm_num)⟩

theorem rc_lt (r : Row) : rc r < 16 := by
  unfold rc
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  have h2 := (r 2).isLt
  have h3 := (r 3).isLt
  omega

theorem rowOf_rc (r : Row) : rowOf (rc r) = r := by
  funext j
  apply Fin.ext
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  have h2 := (r 2).isLt
  have h3 := (r 3).isLt
  fin_cases j <;> (simp [rowOf, rc]; try omega)

theorem rc_rowOf (c : ℕ) (hc : c < 16) : rc (rowOf c) = c := by
  unfold rc rowOf
  simp
  omega

theorem rc_bits (x : Row) : rc x % 2 = (x 0).val ∧ rc x / 2 % 2 = (x 1).val ∧
    rc x / 4 % 2 = (x 2).val ∧ rc x / 8 = (x 3).val := by
  unfold rc
  have h0 := (x 0).isLt
  have h1 := (x 1).isLt
  have h2 := (x 2).isLt
  have h3 := (x 3).isLt
  omega

instance unimodalDec {m : ℕ} (s : Fin m → Fin 2) : Decidable (UniW s) :=
  inferInstanceAs (Decidable (∃ k : Fin m, (∀ i j : Fin m, i ≤ j → j ≤ k → s i ≤ s j) ∧
    (∀ i j : Fin m, k ≤ i → i ≤ j → s j ≤ s i)))

/-- The automaton state reached on the entries of the row with code `c`. -/
def rowDFA (c : ℕ) : ℕ :=
  cstep (cstep (cstep (cstep 0 (c % 2)) (c / 2 % 2)) (c / 4 % 2)) (c / 8 % 2)

theorem row_check : ∀ c < 16, (UniW (rowOf c) ↔ rowDFA c < 3) := by
  decide +kernel

theorem unimodal_row (r : Row) : UniW r ↔ rowDFA (rc r) < 3 := by
  have h := row_check (rc r) (rc_lt r)
  rwa [rowOf_rc] at h

/-- Column `j` of the array `A`, read top to bottom. -/
def col {m : ℕ} (A : Fin m → Row) (j : Fin 4) : Fin m → Fin 2 := fun i => A i j

theorem col_snoc {m : ℕ} (A : Fin m → Row) (x : Row) (j : Fin 4) :
    col (Fin.snoc A x : Fin (m + 1) → Row) j = Fin.snoc (col A j) (x j) := by
  funext i
  cases i using Fin.lastCases with
  | last => simp [col]
  | cast i => simp [col]

/-- The code of four column states, or 81 if one of them is 3. -/
def enc (d0 d1 d2 d3 : ℕ) : ℕ :=
  if d0 < 3 ∧ d1 < 3 ∧ d2 < 3 ∧ d3 < 3 then d0 + 3 * d1 + 9 * d2 + 27 * d3 else 81

/-- The state of an array: the code `enc` of its four column states (81 if one of them is 3) if
all its rows are unimodal, and 81 otherwise. -/
noncomputable def st {m : ℕ} (A : Fin m → Row) : ℕ := by
  classical
  exact if ∀ i, UniW (A i) then
    enc (cs (col A 0)) (cs (col A 1)) (cs (col A 2)) (cs (col A 3)) else 81

/-- The transition of the array automaton on the row with code `c` (81 is the dead state). -/
def tau (s c : ℕ) : ℕ :=
  if s < 81 ∧ rowDFA c < 3 then
    enc (cstep (s % 3) (c % 2)) (cstep (s / 3 % 3) (c / 2 % 2)) (cstep (s / 9 % 3) (c / 4 % 2))
      (cstep (s / 27) (c / 8))
  else 81

theorem chk_tau : ∀ d0 < 4, ∀ d1 < 4, ∀ d2 < 4, ∀ d3 < 4, ∀ c < 16,
    (if rowDFA c < 3 then
      enc (cstep d0 (c % 2)) (cstep d1 (c / 2 % 2)) (cstep d2 (c / 4 % 2)) (cstep d3 (c / 8))
     else 81) = tau (enc d0 d1 d2 d3) c := by
  decide +kernel

theorem rows_snoc {m : ℕ} (A : Fin m → Row) (x : Row) :
    (∀ i, UniW ((Fin.snoc A x : Fin (m + 1) → Row) i)) ↔
      (∀ i, UniW (A i)) ∧ UniW x := by
  rw [Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem st_snoc {m : ℕ} (A : Fin m → Row) (x : Row) :
    st (Fin.snoc A x : Fin (m + 1) → Row) = tau (st A) (rc x) := by
  classical
  unfold st
  simp only [col_snoc, cs_snoc]
  by_cases hR : ∀ i, UniW (A i)
  · rw [if_pos hR]
    obtain ⟨b0, b1, b2, b3⟩ := rc_bits x
    have key := chk_tau _ (cs_lt_four (col A 0)) _ (cs_lt_four (col A 1)) _
      (cs_lt_four (col A 2)) _ (cs_lt_four (col A 3)) (rc x) (rc_lt x)
    rw [b0, b1, b2, b3] at key
    rw [← key]
    by_cases hx : UniW x
    · rw [if_pos ((rows_snoc A x).mpr ⟨hR, hx⟩), if_pos ((unimodal_row x).mp hx)]
    · rw [if_neg (fun h => hx ((rows_snoc A x).mp h).2),
        if_neg (fun h => hx ((unimodal_row x).mpr h))]
  · rw [if_neg hR, if_neg (fun h => hR ((rows_snoc A x).mp h).1)]
    unfold tau
    rw [if_neg (by omega)]

theorem forall_fin4 (P : Fin 4 → Prop) : (∀ j, P j) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩
  · rintro ⟨h0, h1, h2, h3⟩ j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3

theorem enc_lt (d0 d1 d2 d3 : ℕ) :
    enc d0 d1 d2 d3 < 81 ↔ d0 < 3 ∧ d1 < 3 ∧ d2 < 3 ∧ d3 < 3 := by
  unfold enc
  split_ifs with h
  · constructor
    · intro _
      exact h
    · intro _
      omega
  · constructor
    · intro h'
      omega
    · intro h'
      exact absurd h' h

theorem good_iff {m : ℕ} (A : Fin (m + 1) → Row) : GoodA A ↔ st A < 81 := by
  classical
  unfold GoodA st
  by_cases hR : ∀ i, UniW (A i)
  · rw [if_pos hR, enc_lt, cs_lt_three, cs_lt_three, cs_lt_three, cs_lt_three, forall_fin4]
    rw [unimodal_iff (fun i => A i 0), unimodal_iff (fun i => A i 1),
      unimodal_iff (fun i => A i 2), unimodal_iff (fun i => A i 3)]
    exact ⟨fun h => h.2, fun h => ⟨hR, h⟩⟩
  · rw [if_neg hR]
    exact ⟨fun h => absurd h.1 hR, fun h => absurd h (lt_irrefl _)⟩

theorem st_lt {m : ℕ} (A : Fin m → Row) : st A < 82 := by
  classical
  unfold st enc
  split_ifs <;> omega

theorem st_zero (A : Fin 0 → Row) : st A = 0 := by
  classical
  unfold st
  rw [if_pos (fun i => Fin.elim0 i), cs_zero, cs_zero, cs_zero, cs_zero]
  rfl

/-! ### Counting -/

theorem sum_snoc (m : ℕ) (F : (Fin m → Row) → Row → ℕ) :
    ∑ B : Fin (m + 1) → Row, F (Fin.init B) (B (Fin.last m)) =
      ∑ β : Fin m → Row, ∑ γ : Row, F β γ := by
  calc ∑ B : Fin (m + 1) → Row, F (Fin.init B) (B (Fin.last m))
      = ∑ p : Row × (Fin m → Row), F p.2 p.1 :=
        (Fintype.sum_equiv (Fin.snocEquiv (fun _ => Row)) (fun p => F p.2 p.1) _
          (fun p => by
            rw [show (Fin.snocEquiv (fun _ => Row)) p = Fin.snoc p.2 p.1 from rfl,
              Fin.init_snoc, Fin.snoc_last])).symm
    _ = ∑ γ : Row, ∑ β : Fin m → Row, F β γ := Fintype.sum_prod_type' (fun γ β => F β γ)
    _ = ∑ β : Fin m → Row, ∑ γ : Row, F β γ := Finset.sum_comm

theorem sum_row (F : ℕ → ℕ) : ∑ γ : Row, F (rc γ) = ∑ c ∈ range 16, F c :=
  Finset.sum_nbij' rc rowOf (fun γ _ => Finset.mem_range.mpr (rc_lt γ))
    (fun _ _ => Finset.mem_univ _) (fun γ _ => rowOf_rc γ)
    (fun c hc => rc_rowOf c (Finset.mem_range.mp hc)) (fun _ _ => rfl)

theorem sum_fiber {X : Type*} [Fintype X] (r : X → ℕ) (hr : ∀ x, r x < 82) (h : ℕ → ℕ) :
    ∑ x, h (r x) = ∑ s ∈ range 82, (∑ x, if r x = s then 1 else 0) * h s := by
  simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (hr x))]

/-- The number of rows leading from the state `s` to the state `s'`. -/
def cnt (s s' : ℕ) : ℕ := ∑ c ∈ range 16, if tau s c = s' then 1 else 0

/-- The number of arrays with `m` rows in the state `s`. -/
noncomputable def N (m s : ℕ) : ℕ := ∑ A : Fin m → Row, if st A = s then 1 else 0

/-- One step of the counts of the live states. -/
def Mop (f : ℕ → ℕ) (s' : ℕ) : ℕ := ∑ s ∈ range 81, f s * cnt s s'

/-- The total count of the live states. -/
def Aop (f : ℕ → ℕ) : ℕ := ∑ s ∈ range 81, f s

theorem cnt_dead (s' : ℕ) (hs' : s' < 81) : cnt 81 s' = 0 := by
  unfold cnt
  refine Finset.sum_eq_zero fun c _ => if_neg ?_
  unfold tau
  rw [if_neg (by omega)]
  omega

theorem a_eq (m : ℕ) : aW (m + 1) = Aop (N (m + 1)) := by
  classical
  have h1 : aW (m + 1) = ∑ A : Fin (m + 1) → Row, if st A < 81 then 1 else 0 := by
    unfold aW
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl fun A _ => if_congr (good_iff A) rfl rfl
  rw [h1]
  unfold Aop N
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.sum_ite_eq]
  by_cases h : st A < 81
  · rw [if_pos h, if_pos (Finset.mem_range.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (Finset.mem_range.mp h'))]

theorem N_zero (s : ℕ) : N 0 s = if s = 0 then 1 else 0 := by
  unfold N
  rw [Fintype.sum_unique, st_zero]
  by_cases h : s = 0
  · subst h
    rfl
  · rw [if_neg (Ne.symm h), if_neg h]

theorem N_succ (m s' : ℕ) (hs' : s' < 81) : N (m + 1) s' = Mop (N m) s' := by
  have h0 : N (m + 1) s' = ∑ B : Fin (m + 1) → Row,
      if tau (st (Fin.init B)) (rc (B (Fin.last m))) = s' then 1 else 0 := by
    unfold N
    refine Finset.sum_congr rfl fun B _ => ?_
    have h := st_snoc (Fin.init B) (B (Fin.last m))
    rw [Fin.snoc_init_self] at h
    rw [h]
  have h3 : ∀ β : Fin m → Row, (∑ γ : Row, if tau (st β) (rc γ) = s' then 1 else 0) =
      cnt (st β) s' := fun β => sum_row (fun c => if tau (st β) c = s' then 1 else 0)
  rw [h0, sum_snoc m (fun β γ => if tau (st β) (rc γ) = s' then 1 else 0),
    Finset.sum_congr rfl (fun β _ => h3 β),
    sum_fiber (fun β : Fin m → Row => st β) st_lt (fun s => cnt s s'),
    Finset.sum_range_succ, cnt_dead s' hs', mul_zero, add_zero]
  rfl

/-! ### The transfer counts through predecessor lists -/

/-- The total multiplicity of the state `s` in a list of pairs (state, multiplicity). -/
def pc : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | p :: L, s => (if p.1 = s then p.2 else 0) + pc L s

/-- The sum of `m * f s` over the pairs `(s, m)` of a list. -/
def ls : List (ℕ × ℕ) → (ℕ → ℕ) → ℕ
  | [], _ => 0
  | p :: L, f => p.2 * f p.1 + ls L f

theorem sum_pc (f : ℕ → ℕ) (L : List (ℕ × ℕ)) (h : ∀ p ∈ L, p.1 < 81) :
    ∑ s ∈ range 81, f s * pc L s = ls L f := by
  induction L with
  | nil => simp [pc, ls]
  | cons p L ih =>
    have ih' := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have hp : p.1 < 81 := h p (List.mem_cons.mpr (Or.inl rfl))
    have h1 : ∑ s ∈ range 81, f s * (if p.1 = s then p.2 else 0) = p.2 * f p.1 := by
      rw [Finset.sum_eq_single p.1]
      · rw [if_pos rfl, mul_comm]
      · intro b _ hb
        rw [if_neg (Ne.symm hb), mul_zero]
      · intro hn
        exact absurd (Finset.mem_range.mpr hp) hn
    simp only [pc, ls, mul_add, Finset.sum_add_distrib, ih', h1]

/-- The vectors `K j` (`j < 9`) on the 81 live states. -/
def KT : List (List ℕ) :=
  [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 1, 0, 2, 2, 1, 2, 1, 0, 0, 1, 2, 5, 3, 2, 0, 2, 1, 1, 0, 2, 3, 1, 1, 2, 1, 0, 0, 1, 0, 0,
    0, 1, 0, 1, 2, 0, 1, 5, 9, 4, 3, 0, 3, 2, 0, 0, 0, 0, 0, 2, 0, 2, 1, 1, 0, 1, 1, 0, 0, 0, 0, 2,
    0, 0, 3, 4, 1, 1, 0, 1, 1, 1, 0, 2, 3, 1, 1, 2, 1],
   [0, 0, 0, 0, 0, 3, 0, 3, 6, 0, 0, 1, 0, 4, 11, 3, 0, 15, 0, 1, 2, 3, 11, 13, 6, 15, 16, 0, 0, 1,
    0, 0, 0, 1, 0, 7, 0, 0, 3, 4, 16, 25, 11, 0, 31, 3, 0, 3, 0, 0, 0, 15, 0, 33, 0, 1, 2, 1, 3, 3,
    2, 3, 2, 3, 0, 3, 11, 25, 21, 13, 0, 23, 6, 7, 2, 15, 31, 23, 16, 33, 30],
   [0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 8, 0, 0, 27, 0, 0, 2, 0, 8, 30, 6, 27, 69, 0, 0, 0, 0,
    0, 0, 0, 0, 12, 0, 0, 2, 0, 8, 39, 8, 0, 90, 0, 0, 7, 0, 0, 0, 27, 0, 157, 0, 0, 2, 0, 2, 7, 2,
    7, 16, 0, 0, 7, 8, 39, 82, 30, 0, 136, 6, 12, 16, 27, 90, 136, 69, 157, 261],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 18, 0, 14, 100, 0, 0, 0,
    0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 18, 0, 0, 100, 0, 0, 4, 0, 0, 0, 14, 0, 306, 0, 0, 0, 0, 0, 4,
    0, 4, 28, 0, 0, 4, 0, 18, 106, 18, 0, 302, 0, 6, 28, 14, 100, 302, 100, 306, 934],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 46, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38, 0, 0, 0, 0, 0, 0, 0, 0, 264, 0, 0, 0, 0, 0, 0, 0, 0, 14,
    0, 0, 0, 0, 0, 44, 0, 0, 284, 0, 0, 14, 0, 38, 284, 46, 264, 1558],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 96, 0, 0, 0, 0, 0, 96, 0, 84, 1216],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 360]]

/-- For each live state `t`, the list of pairs `(s, cnt s t)` with `cnt s t > 0`. -/
def PL : List (List (ℕ × ℕ)) :=
  [[(0, 1)],
   [(0, 1), (1, 1)],
   [(1, 1), (2, 1)],
   [(0, 1), (3, 1)],
   [(0, 1), (1, 1), (3, 1), (4, 1)],
   [(1, 1), (2, 1), (4, 1), (5, 1)],
   [(3, 1), (6, 1)],
   [(3, 1), (4, 1), (6, 1), (7, 1)],
   [(4, 1), (5, 1), (7, 1), (8, 1)],
   [(0, 1), (9, 1)],
   [],
   [(1, 1), (2, 1), (10, 1), (11, 1)],
   [(0, 1), (3, 1), (9, 1), (12, 1)],
   [(0, 1), (1, 1), (3, 1), (4, 1), (9, 1), (10, 1), (12, 1), (13, 1)],
   [(1, 1), (2, 1), (4, 1), (5, 1), (10, 1), (11, 1), (13, 1), (14, 1)],
   [(3, 1), (6, 1), (12, 1), (15, 1)],
   [],
   [(4, 1), (5, 1), (7, 1), (8, 1), (13, 1), (14, 1), (16, 1), (17, 1)],
   [(9, 1), (18, 1)],
   [(9, 1), (10, 1), (18, 1), (19, 1)],
   [(10, 1), (11, 1), (19, 1), (20, 1)],
   [(9, 1), (12, 1), (18, 1), (21, 1)],
   [(9, 1), (10, 1), (12, 1), (13, 1), (18, 1), (19, 1), (21, 1), (22, 1)],
   [(10, 1), (11, 1), (13, 1), (14, 1), (19, 1), (20, 1), (22, 1), (23, 1)],
   [(12, 1), (15, 1), (21, 1), (24, 1)],
   [(12, 1), (13, 1), (15, 1), (16, 1), (21, 1), (22, 1), (24, 1), (25, 1)],
   [(13, 1), (14, 1), (16, 1), (17, 1), (22, 1), (23, 1), (25, 1), (26, 1)],
   [(0, 1), (27, 1)],
   [],
   [(1, 1), (2, 1), (28, 1), (29, 1)],
   [],
   [],
   [],
   [(3, 1), (6, 1), (30, 1), (33, 1)],
   [],
   [(4, 1), (5, 1), (7, 1), (8, 1), (31, 1), (32, 1), (34, 1), (35, 1)],
   [(0, 1), (9, 1), (27, 1), (36, 1)],
   [],
   [(1, 1), (2, 1), (10, 1), (11, 1), (28, 1), (29, 1), (37, 1), (38, 1)],
   [(0, 1), (3, 1), (9, 1), (12, 1), (27, 1), (30, 1), (36, 1), (39, 1)],
   [(0, 1), (1, 1), (3, 1), (4, 1), (9, 1), (10, 1), (12, 1), (13, 1), (27, 1), (28, 1), (30, 1),
    (31, 1), (36, 1), (37, 1), (39, 1), (40, 1)],
   [(1, 1), (2, 1), (4, 1), (5, 1), (10, 1), (11, 1), (13, 1), (14, 1), (28, 1), (29, 1), (31, 1),
    (32, 1), (37, 1), (38, 1), (40, 1), (41, 1)],
   [(3, 1), (6, 1), (12, 1), (15, 1), (30, 1), (33, 1), (39, 1), (42, 1)],
   [],
   [(4, 1), (5, 1), (7, 1), (8, 1), (13, 1), (14, 1), (16, 1), (17, 1), (31, 1), (32, 1), (34, 1),
    (35, 1), (40, 1), (41, 1), (43, 1), (44, 1)],
   [(9, 1), (18, 1), (36, 1), (45, 1)],
   [],
   [(10, 1), (11, 1), (19, 1), (20, 1), (37, 1), (38, 1), (46, 1), (47, 1)],
   [],
   [],
   [],
   [(12, 1), (15, 1), (21, 1), (24, 1), (39, 1), (42, 1), (48, 1), (51, 1)],
   [],
   [(13, 1), (14, 1), (16, 1), (17, 1), (22, 1), (23, 1), (25, 1), (26, 1), (40, 1), (41, 1), (43,
    1), (44, 1), (49, 1), (50, 1), (52, 1), (53, 1)],
   [(27, 1), (54, 1)],
   [(27, 1), (28, 1), (54, 1), (55, 1)],
   [(28, 1), (29, 1), (55, 1), (56, 1)],
   [(27, 1), (30, 1), (54, 1), (57, 1)],
   [(27, 1), (28, 1), (30, 1), (31, 1), (54, 1), (55, 1), (57, 1), (58, 1)],
   [(28, 1), (29, 1), (31, 1), (32, 1), (55, 1), (56, 1), (58, 1), (59, 1)],
   [(30, 1), (33, 1), (57, 1), (60, 1)],
   [(30, 1), (31, 1), (33, 1), (34, 1), (57, 1), (58, 1), (60, 1), (61, 1)],
   [(31, 1), (32, 1), (34, 1), (35, 1), (58, 1), (59, 1), (61, 1), (62, 1)],
   [(27, 1), (36, 1), (54, 1), (63, 1)],
   [],
   [(28, 1), (29, 1), (37, 1), (38, 1), (55, 1), (56, 1), (64, 1), (65, 1)],
   [(27, 1), (30, 1), (36, 1), (39, 1), (54, 1), (57, 1), (63, 1), (66, 1)],
   [(27, 1), (28, 1), (30, 1), (31, 1), (36, 1), (37, 1), (39, 1), (40, 1), (54, 1), (55, 1), (57,
    1), (58, 1), (63, 1), (64, 1), (66, 1), (67, 1)],
   [(28, 1), (29, 1), (31, 1), (32, 1), (37, 1), (38, 1), (40, 1), (41, 1), (55, 1), (56, 1), (58,
    1), (59, 1), (64, 1), (65, 1), (67, 1), (68, 1)],
   [(30, 1), (33, 1), (39, 1), (42, 1), (57, 1), (60, 1), (66, 1), (69, 1)],
   [],
   [(31, 1), (32, 1), (34, 1), (35, 1), (40, 1), (41, 1), (43, 1), (44, 1), (58, 1), (59, 1), (61,
    1), (62, 1), (67, 1), (68, 1), (70, 1), (71, 1)],
   [(36, 1), (45, 1), (63, 1), (72, 1)],
   [(36, 1), (37, 1), (45, 1), (46, 1), (63, 1), (64, 1), (72, 1), (73, 1)],
   [(37, 1), (38, 1), (46, 1), (47, 1), (64, 1), (65, 1), (73, 1), (74, 1)],
   [(36, 1), (39, 1), (45, 1), (48, 1), (63, 1), (66, 1), (72, 1), (75, 1)],
   [(36, 1), (37, 1), (39, 1), (40, 1), (45, 1), (46, 1), (48, 1), (49, 1), (63, 1), (64, 1), (66,
    1), (67, 1), (72, 1), (73, 1), (75, 1), (76, 1)],
   [(37, 1), (38, 1), (40, 1), (41, 1), (46, 1), (47, 1), (49, 1), (50, 1), (64, 1), (65, 1), (67,
    1), (68, 1), (73, 1), (74, 1), (76, 1), (77, 1)],
   [(39, 1), (42, 1), (48, 1), (51, 1), (66, 1), (69, 1), (75, 1), (78, 1)],
   [(39, 1), (40, 1), (42, 1), (43, 1), (48, 1), (49, 1), (51, 1), (52, 1), (66, 1), (67, 1), (69,
    1), (70, 1), (75, 1), (76, 1), (78, 1), (79, 1)],
   [(40, 1), (41, 1), (43, 1), (44, 1), (49, 1), (50, 1), (52, 1), (53, 1), (67, 1), (68, 1), (70,
    1), (71, 1), (76, 1), (77, 1), (79, 1), (80, 1)]]

/-- The predecessor list of the state `t`. -/
def pl (t : ℕ) : List (ℕ × ℕ) := PL.getD t []

/-- The sum of `g c` over `c < 16`, written out. -/
def sum16 (g : ℕ → ℕ) : ℕ :=
  g 0 + g 1 + g 2 + g 3 + g 4 + g 5 + g 6 + g 7 + g 8 + g 9 + g 10 + g 11 + g 12 + g 13 + g 14 +
    g 15

theorem sum16_eq (g : ℕ → ℕ) : sum16 g = ∑ c ∈ range 16, g c := by
  simp only [sum16, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

theorem chk_pl : ∀ t < 81, ∀ s < 81,
    sum16 (fun c => if tau s c = t then 1 else 0) = pc (pl t) s := by
  decide +kernel

theorem chk_pl_lt : ∀ t < 81, ∀ p ∈ pl t, p.1 < 81 := by
  decide +kernel

/-- One step of the counts, through the predecessor lists. -/
def Mq (f : ℕ → ℕ) (t : ℕ) : ℕ := ls (pl t) f

theorem Mop_eq (f : ℕ → ℕ) (t : ℕ) (ht : t < 81) : Mop f t = Mq f t := by
  unfold Mop Mq
  rw [← sum_pc f (pl t) (chk_pl_lt t ht)]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [← chk_pl t ht s (Finset.mem_range.mp hs), sum16_eq]
  rfl

/-! ### The closed form -/

/-- The vector `K j` on the live states (0 for `j ≥ 9`). -/
def K (j s : ℕ) : ℕ := (KT.getD j []).getD s 0

theorem chk_K0 : ∀ s < 81, K 0 s = if s = 0 then 1 else 0 := by
  decide +kernel

theorem chk_K : ∀ j < 9, ∀ s < 81, Mq (K j) s = K j s + K (j + 1) s := by
  decide +kernel

theorem chk_AK : Aop (K 0) = 1 ∧ Aop (K 1) = 10 ∧ Aop (K 2) = 100 ∧ Aop (K 3) = 545 ∧
    Aop (K 4) = 1645 ∧ Aop (K 5) = 2868 ∧ Aop (K 6) = 2894 ∧ Aop (K 7) = 1576 ∧
    Aop (K 8) = 360 := by
  decide +kernel

theorem K_nine (s : ℕ) : K 9 s = 0 := rfl

theorem Mop_congr {f g : ℕ → ℕ} (h : ∀ s < 81, f s = g s) (s' : ℕ) : Mop f s' = Mop g s' := by
  unfold Mop
  exact Finset.sum_congr rfl fun s hs => by rw [h s (Finset.mem_range.mp hs)]

theorem Aop_congr {f g : ℕ → ℕ} (h : ∀ s < 81, f s = g s) : Aop f = Aop g := by
  unfold Aop
  exact Finset.sum_congr rfl fun s hs => by rw [h s (Finset.mem_range.mp hs)]

theorem Mop_lin (S : Finset ℕ) (c : ℕ → ℕ) (F : ℕ → ℕ → ℕ) (s' : ℕ) :
    Mop (fun s => ∑ j ∈ S, c j * F j s) s' = ∑ j ∈ S, c j * Mop (F j) s' := by
  unfold Mop
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem Aop_lin (S : Finset ℕ) (c : ℕ → ℕ) (F : ℕ → ℕ → ℕ) :
    Aop (fun s => ∑ j ∈ S, c j * F j s) = ∑ j ∈ S, c j * Aop (F j) := by
  unfold Aop
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

theorem N_closed (k : ℕ) : ∀ s < 81, N k s = ∑ j ∈ range 9, k.choose j * K j s := by
  induction k with
  | zero =>
    intro s hs
    rw [N_zero, ← chk_K0 s hs]
    simp [Finset.sum_range_succ]
  | succ k ih =>
    intro s hs
    rw [N_succ k s hs, Mop_congr (g := fun s => ∑ j ∈ range 9, k.choose j * K j s) ih, Mop_lin]
    rw [Finset.sum_congr rfl (fun j hj => by
      rw [Mop_eq _ s hs, chk_K j (Finset.mem_range.mp hj) s hs])]
    have h9 := K_nine s
    have p1 : (k + 1).choose 1 = k.choose 0 + k.choose 1 := Nat.choose_succ_succ k 0
    have p2 : (k + 1).choose 2 = k.choose 1 + k.choose 2 := Nat.choose_succ_succ k 1
    have p3 : (k + 1).choose 3 = k.choose 2 + k.choose 3 := Nat.choose_succ_succ k 2
    have p4 : (k + 1).choose 4 = k.choose 3 + k.choose 4 := Nat.choose_succ_succ k 3
    have p5 : (k + 1).choose 5 = k.choose 4 + k.choose 5 := Nat.choose_succ_succ k 4
    have p6 : (k + 1).choose 6 = k.choose 5 + k.choose 6 := Nat.choose_succ_succ k 5
    have p7 : (k + 1).choose 7 = k.choose 6 + k.choose 7 := Nat.choose_succ_succ k 6
    have p8 : (k + 1).choose 8 = k.choose 7 + k.choose 8 := Nat.choose_succ_succ k 7
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, p1, p2, p3, p4, p5, p6, p7, p8,
      Nat.choose_zero_right, h9]
    ring

theorem a_closed (k : ℕ) : aW (k + 1) = 1 + 10 * (k + 1) + 100 * (k + 1).choose 2 +
    545 * (k + 1).choose 3 + 1645 * (k + 1).choose 4 + 2868 * (k + 1).choose 5 +
    2894 * (k + 1).choose 6 + 1576 * (k + 1).choose 7 + 360 * (k + 1).choose 8 := by
  rw [a_eq, Aop_congr (g := fun s => ∑ j ∈ range 9, (k + 1).choose j * K j s) (N_closed (k + 1)),
    Aop_lin]
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩ := chk_AK
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c0, c1, c2, c3, c4, c5, c6, c7, c8,
    Nat.choose_zero_right, Nat.choose_one_right]
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

theorem choose7 (m : ℕ) : (m.choose 7 : ℚ) =
    m * (m - 1) * (m - 2) * (m - 3) * (m - 4) * (m - 5) * (m - 6) / 5040 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, choose6]
    push_cast
    ring

theorem choose8 (m : ℕ) : (m.choose 8 : ℚ) =
    m * (m - 1) * (m - 2) * (m - 3) * (m - 4) * (m - 5) * (m - 6) * (m - 7) / 40320 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, choose7]
    push_cast
    ring

/-- Hardin's octic: `a n` for every `n ≥ 1`. -/
theorem closedQ (n : ℕ) (hn : 1 ≤ n) : (aW n : ℚ) =
    (1 / 112) * (n : ℚ) ^ 8 + (79 / 1260) * (n : ℚ) ^ 7 + (59 / 180) * (n : ℚ) ^ 6 +
      (299 / 360) * (n : ℚ) ^ 5 + (259 / 144) * (n : ℚ) ^ 4 + (821 / 360) * (n : ℚ) ^ 3 +
      (7219 / 2520) * (n : ℚ) ^ 2 + (767 / 420) * (n : ℚ) + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [a_closed]
  push_cast
  rw [choose2, choose3, choose4, choose5, choose6, choose7, choose8]
  push_cast
  ring

theorem recurrence (n : ℕ) (hn : 9 < n) :
    (aW n : ℤ) = 9 * aW (n - 1) - 36 * aW (n - 2) + 84 * aW (n - 3) - 126 * aW (n - 4) +
      126 * aW (n - 5) - 84 * aW (n - 6) + 36 * aW (n - 7) - 9 * aW (n - 8) + aW (n - 9) := by
  have h : ((aW n : ℤ) : ℚ) = ((9 * aW (n - 1) - 36 * aW (n - 2) + 84 * aW (n - 3) -
      126 * aW (n - 4) + 126 * aW (n - 5) - 84 * aW (n - 6) + 36 * aW (n - 7) - 9 * aW (n - 8) +
      aW (n - 9) : ℤ) : ℚ) := by
    push_cast
    rw [closedQ n (by omega), closedQ (n - 1) (by omega), closedQ (n - 2) (by omega),
      closedQ (n - 3) (by omega), closedQ (n - 4) (by omega), closedQ (n - 5) (by omega),
      closedQ (n - 6) (by omega), closedQ (n - 7) (by omega), closedQ (n - 8) (by omega),
      closedQ (n - 9) (by omega)]
    push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega,
      show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega, show 8 ≤ n by omega,
      show 9 ≤ n by omega]
    ring
  exact_mod_cast h

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (aW n : ℚ)) * (1 - X) ^ 9 =
        X * (11 + 22 * X + 183 * X ^ 2 + 14 * X ^ 3 + 158 * X ^ 4 - 56 * X ^ 5 + 35 * X ^ 6 -
          8 * X ^ 7 + X ^ 8) := by
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (aW n : ℚ) with hF
  have key : PowerSeries.mk F * (1 - X) ^ 9 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 9 * (PowerSeries.mk F * X ^ 1) +
        C 36 * (PowerSeries.mk F * X ^ 2) - C 84 * (PowerSeries.mk F * X ^ 3) +
        C 126 * (PowerSeries.mk F * X ^ 4) - C 126 * (PowerSeries.mk F * X ^ 5) +
        C 84 * (PowerSeries.mk F * X ^ 6) - C 36 * (PowerSeries.mk F * X ^ 7) +
        C 9 * (PowerSeries.mk F * X ^ 8) - C 1 * (PowerSeries.mk F * X ^ 9) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (11 + 22 * X + 183 * X ^ 2 + 14 * X ^ 3 + 158 * X ^ 4 -
      56 * X ^ 5 + 35 * X ^ 6 - 8 * X ^ 7 + X ^ 8) =
      C 11 * X ^ 1 + C 22 * X ^ 2 + C 183 * X ^ 3 + C 14 * X ^ 4 + C 158 * X ^ 5 -
        C 56 * X ^ 6 + C 35 * X ^ 7 - C 8 * X ^ 8 + C 1 * X ^ 9 := by
    simp only [map_one, map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  have v1 : (aW 1 : ℚ) = 11 := by
    rw [closedQ 1 (by norm_num)]
    norm_num
  have v2 : (aW 2 : ℚ) = 121 := by
    rw [closedQ 2 (by norm_num)]
    norm_num
  have v3 : (aW 3 : ℚ) = 876 := by
    rw [closedQ 3 (by norm_num)]
    norm_num
  have v4 : (aW 4 : ℚ) = 4466 := by
    rw [closedQ 4 (by norm_num)]
    norm_num
  have v5 : (aW 5 : ℚ) = 17594 := by
    rw [closedQ 5 (by norm_num)]
    norm_num
  have v6 : (aW 6 : ℚ) = 57238 := by
    rw [closedQ 6 (by norm_num)]
    norm_num
  have v7 : (aW 7 : ℚ) = 160883 := by
    rw [closedQ 7 (by norm_num)]
    norm_num
  have v8 : (aW 8 : ℚ) = 403159 := by
    rw [closedQ 8 (by norm_num)]
    norm_num
  have v9 : (aW 9 : ℚ) = 921181 := by
    rw [closedQ 9 (by norm_num)]
    norm_num
  by_cases hk : k < 10
  · interval_cases k <;> norm_num [hF, v1, v2, v3, v4, v5, v6, v7, v8, v9]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 10 := ⟨k - 10, by omega⟩
    simp only [show 0 ≤ j + 10 by omega, show 1 ≤ j + 10 by omega, show 2 ≤ j + 10 by omega,
      show 3 ≤ j + 10 by omega, show 4 ≤ j + 10 by omega, show 5 ≤ j + 10 by omega,
      show 6 ≤ j + 10 by omega, show 7 ≤ j + 10 by omega, show 8 ≤ j + 10 by omega,
      show 9 ≤ j + 10 by omega, show j + 10 - 0 = j + 10 by omega,
      show j + 10 - 1 = j + 9 by omega, show j + 10 - 2 = j + 8 by omega,
      show j + 10 - 3 = j + 7 by omega, show j + 10 - 4 = j + 6 by omega,
      show j + 10 - 5 = j + 5 by omega, show j + 10 - 6 = j + 4 by omega,
      show j + 10 - 7 = j + 3 by omega, show j + 10 - 8 = j + 2 by omega,
      show j + 10 - 9 = j + 1 by omega, show ¬ (j + 10 = 0) by omega, show ¬ (j + 10 = 1) by omega,
      show ¬ (j + 10 = 2) by omega, show ¬ (j + 10 = 3) by omega, show ¬ (j + 10 = 4) by omega,
      show ¬ (j + 10 = 5) by omega, show ¬ (j + 10 = 6) by omega, show ¬ (j + 10 = 7) by omega,
      show ¬ (j + 10 = 8) by omega, show ¬ (j + 10 = 9) by omega, show ¬ (j + 1 = 0) by omega,
      show ¬ (j + 2 = 0) by omega, show ¬ (j + 3 = 0) by omega, show ¬ (j + 4 = 0) by omega,
      show ¬ (j + 5 = 0) by omega, show ¬ (j + 6 = 0) by omega, show ¬ (j + 7 = 0) by omega,
      show ¬ (j + 8 = 0) by omega, show ¬ (j + 9 = 0) by omega, if_true, if_false, hF]
    rw [closedQ (j + 10) (by omega), closedQ (j + 9) (by omega), closedQ (j + 8) (by omega),
      closedQ (j + 7) (by omega), closedQ (j + 6) (by omega), closedQ (j + 5) (by omega),
      closedQ (j + 4) (by omega), closedQ (j + 3) (by omega), closedQ (j + 2) (by omega),
      closedQ (j + 1) (by omega)]
    push_cast
    ring


/-! ### Bridge to the list model of the statement -/

theorem listU_iff {m : ℕ} (t : Fin m → Fin 2) :
    OMA.S_oeis_a223616.Unimodal (List.ofFn fun i => ((t i : Fin 2) : ℕ)) ↔ NoGap t := by
  constructor
  · rintro ⟨k, h1, h2⟩ i j l hij hjl hi hl
    rw [List.pairwise_iff_getElem] at h1 h2
    have hij' : i.val < j.val := hij
    have hjl' : j.val < l.val := hjl
    apply Fin.ext
    have hj2 := (t j).isLt
    by_cases hjk : j.val < k
    · have := h1 i.val j.val (by simp; omega) (by simp; omega) hij'
      simp only [List.getElem_take, List.getElem_ofFn, Fin.eta] at this
      rw [hi] at this
      simp only [Fin.val_one] at this ⊢
      omega
    · have := h2 (j.val - k) (l.val - k) (by simp; omega) (by simp; omega) (by omega)
      simp only [List.getElem_drop, List.getElem_ofFn] at this
      have e1 : k + (j.val - k) = j.val := by omega
      have e2 : k + (l.val - k) = l.val := by omega
      simp only [e1, e2, Fin.eta] at this
      rw [hl] at this
      simp only [Fin.val_one, ge_iff_le] at this ⊢
      omega
  · intro h
    cases m with
    | zero => exact ⟨0, by simp, by simp⟩
    | succ m =>
      obtain ⟨p, hinc, hdec⟩ := (unimodal_iff t).mpr h
      refine ⟨p.val, ?_, ?_⟩
      · rw [List.pairwise_iff_getElem]
        intro i j hi hj hij
        simp only [List.length_take, List.length_ofFn] at hi hj
        simp only [List.getElem_take, List.getElem_ofFn]
        exact hinc ⟨i, by omega⟩ ⟨j, by omega⟩ (Fin.mk_le_mk.mpr hij.le)
          (Fin.mk_le_mk.mpr (by omega))
      · rw [List.pairwise_iff_getElem]
        intro i j hi hj hij
        simp only [List.length_drop, List.length_ofFn] at hi hj
        simp only [List.getElem_drop, List.getElem_ofFn]
        exact hdec ⟨p.val + i, by omega⟩ ⟨p.val + j, by omega⟩ (Fin.mk_le_mk.mpr (by omega))
          (Fin.mk_le_mk.mpr (by omega))

theorem isSol_iff {m : ℕ} (A : Fin (m + 1) → Row) :
    OMA.S_oeis_a223616.IsSolution (List.ofFn A) ↔ GoodA A := by
  unfold OMA.S_oeis_a223616.IsSolution GoodA
  rw [List.forall_mem_ofFn_iff]
  simp only [List.map_ofFn]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => (unimodal_iff (m := 3) (A i)).mpr ((listU_iff (A i)).mp (h1 i)),
      fun j => (unimodal_iff (fun i => A i j)).mpr ((listU_iff (fun i => A i j)).mp (h2 j))⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => (listU_iff (A i)).mpr ((unimodal_iff (m := 3) (A i)).mp (h1 i)),
      fun j => (listU_iff (fun i => A i j)).mpr ((unimodal_iff (fun i => A i j)).mp (h2 j))⟩

theorem a_bridge (n : ℕ) (hn : 1 ≤ n) : OMA.S_oeis_a223616.a n = aW n := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let f : {A : Fin (m + 1) → Row // GoodA A} →
      {l : List Row // l.length = m + 1 ∧ OMA.S_oeis_a223616.IsSolution l} :=
    fun A => ⟨List.ofFn A.1, List.length_ofFn, (isSol_iff A.1).mpr A.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro A B hAB
      apply Subtype.ext
      have := congrArg Subtype.val hAB
      exact List.ofFn_injective this
    · rintro ⟨l, hl, hs⟩
      let B : Fin (m + 1) → Row := fun i => l[i.val]'(by rw [hl]; exact i.isLt)
      have hB : List.ofFn B = l := by
        apply List.ext_getElem
        · rw [List.length_ofFn, hl]
        · intro i h1 h2
          simp only [List.getElem_ofFn, B]
      refine ⟨⟨B, (isSol_iff B).mp (hB ▸ hs)⟩, ?_⟩
      apply Subtype.ext
      exact hB
  unfold OMA.S_oeis_a223616.a aW
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_subtype]

open PowerSeries in
theorem gen_fun' :
    PowerSeries.mk (fun n => (OMA.S_oeis_a223616.a (n + 1) : ℚ)) * (1 - X) ^ 9 =
      11 + 22 * X ^ 1 + 183 * X ^ 2 + 14 * X ^ 3 + 158 * X ^ 4 - 56 * X ^ 5 + 35 * X ^ 6 -
        8 * X ^ 7 + X ^ 8 := by
  have hG : (fun n => (OMA.S_oeis_a223616.a (n + 1) : ℚ)) = fun n => (aW (n + 1) : ℚ) := by
    funext n
    rw [a_bridge (n + 1) (by omega)]
  have hX : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (aW n : ℚ)) =
      X * PowerSeries.mk (fun n => (aW (n + 1) : ℚ)) := by
    ext k
    rcases k with _ | k
    · simp
    · rw [coeff_succ_X_mul]
      simp
  have h := gen_fun
  rw [hX, mul_assoc] at h
  rw [hG, mul_left_cancel₀ X_ne_zero h]
  ring

theorem recurrence' (n : ℕ) (hn : n > 9) :
    (OMA.S_oeis_a223616.a n : ℤ) = 9 * OMA.S_oeis_a223616.a (n - 1) -
      36 * OMA.S_oeis_a223616.a (n - 2) + 84 * OMA.S_oeis_a223616.a (n - 3) -
      126 * OMA.S_oeis_a223616.a (n - 4) + 126 * OMA.S_oeis_a223616.a (n - 5) -
      84 * OMA.S_oeis_a223616.a (n - 6) + 36 * OMA.S_oeis_a223616.a (n - 7) -
      9 * OMA.S_oeis_a223616.a (n - 8) + OMA.S_oeis_a223616.a (n - 9) := by
  rw [a_bridge n (by omega), a_bridge (n - 1) (by omega), a_bridge (n - 2) (by omega),
    a_bridge (n - 3) (by omega), a_bridge (n - 4) (by omega), a_bridge (n - 5) (by omega),
    a_bridge (n - 6) (by omega), a_bridge (n - 7) (by omega), a_bridge (n - 8) (by omega),
    a_bridge (n - 9) (by omega)]
  exact recurrence n hn

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a223616.main :=
  ⟨OMA.Helpers.gen_fun', OMA.Helpers.recurrence'⟩
