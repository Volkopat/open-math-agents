import OMAStatements.S_oeis_a220198

/-!
Proof of Hardin's formula and of Barker's g.f. and recurrence for A220198 (n X 2 arrays of the
minima of each element and its horizontal, vertical and diagonal neighbours, over the n X 2 0..3
arrays with lexicographically nondecreasing rows and lexicographically nonincreasing columns).

Rows. A row `(x, y)` has the code `4 x + y < 16` (`rc`, inverse `rowOf`); the lexicographic order
of rows is the order of the codes (`rowle_iff`).

The filter. Row `i` of the array of minima depends only on the rows `i - 1, i, i + 1` of `A`:
it is `G (prv A i) (A i) (pad A (i + 1))` (`M_eq`), where a missing row is replaced by the
padding row `(3, 3)`, which does not change any minimum. The left entry of row `i` is the minimum
of both entries of row `i`, of the left entry above it and of both entries below it (the cell
below on the right is its diagonal neighbour); the right entry is the minimum of both entries of
row `i`, of both entries above it (the cell above on the left is its diagonal neighbour) and of
the right entry below it. On codes, `G` is `gm` (`rc_G`, a finite check).

Sorted arrays. The rows are nondecreasing iff consecutive rows are. The column condition is
followed by the state `cs A`: 0 if the two columns are equal, 1 if the right one is
lexicographically smaller, 2 otherwise; adding a row `x` at the bottom changes it to
`fstep (cs A) (rc x)` (`cs_snoc`). So `Fin.snoc A x` is sorted iff `A` is sorted, the last row
of `A` is at most `x`, and the new column state is at most 1 (`sorted_snoc`).

The automaton. For an array `A` with `m + 1` rows let `P A` be its array of minima without the
last row, and let its tail `tl A` be the code of (row above the last row, last row, column state).
Adding a row `x` to `A` appends the letter `G (row above, last row, x)` to `P A` (`P_snoc`), and
the last row of the array of minima of `A` is `G (row above, last row, padding)` (`M_last`). Let
`T(β)` be the set of tails of the sorted arrays `A` with `P A = β`. The reachable sets `T(β)` are
the 24 lists `tails s` of a deterministic automaton (`tau`, state 24 is dead; `run` reads a word):
* soundness: `tl A ∈ tails (run m (P A))` for every sorted `A` (`sound`);
* completeness: every tail in `tails (run m β)` is the tail of a sorted `A` with `P A = β`
  (`complete`).
Both are inductions on the number of rows whose steps are finite checks on codes (`chk_init_a`,
`chk_init_b`, `chk_fwd`, `chk_bwd`, by `decide +kernel`). Hence an array `B` with `m + 1` rows is
an array of minima iff its last row is `G (p, b, padding)` for a tail `(p, b, f)` in the state
reached by its first `m` rows (`mem_image_iff`), and `a (m + 1) = Sum_s N m s * w s`, where
`N m s` counts the words of length `m` leading to the live state `s` and `w s` is the number of
possible last rows (`a_succ`).

Counting. `N (m + 1) = Mop (N m)` (`N_succ`) for the 24 x 24 transfer counts `cnt`. Tables
`nv m` (`m ≤ 4`) and `K j` (`j ≤ 8`) satisfy `nv 0 = N 0`, `Mop (nv m) = nv (m + 1)`, `K 0 = nv 4`,
`Mop (K j) = K j + K (j + 1)` and `K 9 = 0` (finite checks). By induction with Pascal's rule
`N (k + 4) = Sum_{j < 9} C(k, j) K j`, hence
`a (k + 5) = 245 + 302 k + 319 C(k, 2) + 287 C(k, 3) + 209 C(k, 4) + 122 C(k, 5) + 55 C(k, 6)
+ 16 C(k, 7) + 2 C(k, 8)`, while `a 1, a 2, a 3, a 4 = 4, 10, 38, 103`. So
`20160 a(n) = n^8 - 4 n^7 - 42 n^6 + 2996 n^5 - 24171 n^4 + 124544 n^3 - 217708 n^2 + 255504 n
- 141120` for `n ≥ 2` (`closedQ`), which is Hardin's formula. The recurrence for `n > 10` follows
by substituting it (all of `n - 9, ..., n` are at least 2), and the generating function by
comparing coefficients (the coefficients of x^0..x^10 from the values
`0, 4, 10, 38, 103, 245, 547, 1168, 2395, 4724, 8982`, the higher ones vanish as ninth
differences of a polynomial of degree 8).
-/

namespace OMA.Helpers

open OMA.S_oeis_a220198 Finset

/-- A row of an n X 2 array. -/
abbrev Row := Fin 2 → Fin 4

/-- The padding row `(3, 3)`. -/
def topR : Row := fun _ => 3

/-- The code `4 x + y` of the row `(x, y)`. -/
def rc (r : Row) : ℕ := 4 * (r 0).val + (r 1).val

/-- The row with code `c < 16`. -/
def rowOf (c : ℕ) : Row :=
  fun j => ⟨(if j.val = 0 then c / 4 else c) % 4, Nat.mod_lt _ (by norm_num)⟩

theorem rc_lt (r : Row) : rc r < 16 := by
  unfold rc
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  omega

theorem rowOf_rc (r : Row) : rowOf (rc r) = r := by
  funext j
  apply Fin.ext
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  fin_cases j <;> (simp [rowOf, rc]; try omega)

theorem rc_rowOf (c : ℕ) (hc : c < 16) : rc (rowOf c) = c := by
  unfold rc rowOf
  simp
  omega

theorem rc_inj {r s : Row} (h : rc r = rc s) : r = s := by
  rw [← rowOf_rc r, ← rowOf_rc s, h]

theorem rc_topR : rc topR = 15 := rfl

/-- The minimum filter on one row, from the row above `p`, the row `c` and the row below `q`.
The left entry is the minimum of `c 0`, `c 1` (the entry and its horizontal neighbour), `p 0`,
`q 0` (its vertical neighbours) and `q 1` (its diagonal neighbour, down-right); the right entry
is the minimum of `c 0`, `c 1`, `p 0` (its diagonal neighbour, up-left), `p 1` and `q 1`. -/
def G (p c q : Row) : Row :=
  ![c 0 ⊓ c 1 ⊓ p 0 ⊓ q 0 ⊓ q 1, c 0 ⊓ c 1 ⊓ p 0 ⊓ p 1 ⊓ q 1]

/-- The function `G` on codes. -/
def gm (p c q : ℕ) : ℕ :=
  4 * min (min (min (min (c / 4) (c % 4)) (p / 4)) (q / 4)) (q % 4) +
    min (min (min (min (c / 4) (c % 4)) (p / 4)) (p % 4)) (q % 4)

theorem gm_check : ∀ a < 16, ∀ b < 16, ∀ c < 16,
    rc (G (rowOf a) (rowOf b) (rowOf c)) = gm a b c := by
  decide +kernel

theorem rc_G (p c q : Row) : rc (G p c q) = gm (rc p) (rc c) (rc q) := by
  have := gm_check (rc p) (rc_lt p) (rc c) (rc_lt c) (rc q) (rc_lt q)
  rwa [rowOf_rc, rowOf_rc, rowOf_rc] at this

theorem lexlt_iff {k : ℕ} (x y : Fin k → Fin 4) :
    toLex x < toLex y ↔ ∃ i, (∀ j, j < i → x j = y j) ∧ x i < y i := Iff.rfl

theorem row_eq_iff (r s : Row) : r = s ↔ r 0 = s 0 ∧ r 1 = s 1 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩
    funext j
    fin_cases j
    · exact h0
    · exact h1

theorem rowlt_iff (r s : Row) : toLex r < toLex s ↔ r 0 < s 0 ∨ (r 0 = s 0 ∧ r 1 < s 1) := by
  rw [lexlt_iff]
  constructor
  · rintro ⟨i, hi, hlt⟩
    fin_cases i
    · exact Or.inl hlt
    · exact Or.inr ⟨hi 0 (by decide), hlt⟩
  · rintro (h | ⟨h0, h1⟩)
    · exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), h⟩
    · refine ⟨1, fun j hj => ?_, h1⟩
      fin_cases j
      · exact h0
      · exact absurd hj (lt_irrefl _)

theorem lexle_iff' {k : ℕ} (x y : Fin k → Fin 4) :
    toLex x ≤ toLex y ↔ toLex x < toLex y ∨ x = y := by
  rw [le_iff_lt_or_eq, toLex_inj]
  exact Iff.rfl

theorem lexlt_irrefl {k : ℕ} (x : Fin k → Fin 4) : ¬ (toLex x < toLex x) := lt_irrefl _

theorem rowle_iff (r s : Row) : toLex r ≤ toLex s ↔ rc r ≤ rc s := by
  rw [lexle_iff', rowlt_iff, row_eq_iff]
  unfold rc
  simp only [Fin.lt_def, Fin.ext_iff]
  have := (r 0).isLt
  have := (r 1).isLt
  have := (s 0).isLt
  have := (s 1).isLt
  omega

theorem lex_snoc_lt {k : ℕ} (u v : Fin k → Fin 4) (a b : Fin 4) :
    toLex (Fin.snoc u a : Fin (k + 1) → Fin 4) < toLex (Fin.snoc v b : Fin (k + 1) → Fin 4) ↔
      toLex u < toLex v ∨ (u = v ∧ a < b) := by
  rw [lexlt_iff, lexlt_iff]
  constructor
  · rintro ⟨i, hi, hlt⟩
    cases i using Fin.lastCases with
    | last =>
      refine Or.inr ⟨funext fun j => ?_, by simpa using hlt⟩
      simpa using hi j.castSucc (Fin.castSucc_lt_last j)
    | cast i =>
      refine Or.inl ⟨i, fun j hj => ?_, by simpa using hlt⟩
      simpa using hi j.castSucc (Fin.castSucc_lt_castSucc_iff.mpr hj)
  · rintro (⟨i, hi, hlt⟩ | ⟨rfl, h⟩)
    · refine ⟨i.castSucc, fun j hj => ?_, by simpa using hlt⟩
      cases j using Fin.lastCases with
      | last => exact absurd hj (not_lt.mpr (Fin.le_last _))
      | cast j => simpa using hi j (Fin.castSucc_lt_castSucc_iff.mp hj)
    · refine ⟨Fin.last k, fun j hj => ?_, by simpa using h⟩
      cases j using Fin.lastCases with
      | last => exact absurd hj (lt_irrefl _)
      | cast j => simp

/-- The state of the comparison of the two columns: 0 if they are equal, 1 if the right one is
lexicographically smaller, 2 otherwise. -/
noncomputable def cs {n : ℕ} (A : Fin n → Row) : ℕ := by
  classical
  exact if (fun i => A i 0) = (fun i => A i 1) then 0
    else if toLex (fun i => A i 1) < toLex (fun i => A i 0) then 1 else 2

/-- The column state after adding a row with code `x` to an array with column state `f`. -/
def fstep (f x : ℕ) : ℕ :=
  if f = 0 then (if x / 4 = x % 4 then 0 else if x % 4 < x / 4 then 1 else 2) else f

theorem col_snoc {m : ℕ} (A : Fin m → Row) (x : Row) (j : Fin 2) :
    (fun i => (Fin.snoc A x : Fin (m + 1) → Row) i j) = Fin.snoc (fun i => A i j) (x j) := by
  funext i
  cases i using Fin.lastCases with
  | last => simp
  | cast i => simp

theorem cs_snoc {m : ℕ} (A : Fin m → Row) (x : Row) :
    cs (Fin.snoc A x : Fin (m + 1) → Row) = fstep (cs A) (rc x) := by
  classical
  unfold cs
  rw [col_snoc A x 0, col_snoc A x 1]
  have e3 : rc x / 4 = (x 0).val := by
    unfold rc
    have := (x 1).isLt
    omega
  have e4 : rc x % 4 = (x 1).val := by
    unfold rc
    have := (x 1).isLt
    omega
  unfold fstep
  rw [e3, e4]
  generalize (fun i => A i 0) = u
  generalize (fun i => A i 1) = v
  by_cases huv : u = v
  · subst huv
    simp only [Fin.snoc_inj, true_and, lex_snoc_lt, lexlt_irrefl, false_or, if_true]
    by_cases h1 : x 0 = x 1
    · rw [if_pos h1, if_pos (congrArg Fin.val h1)]
    · rw [if_neg h1, if_neg (fun h => h1 (Fin.ext h))]
      by_cases h2 : x 1 < x 0
      · rw [if_pos h2, if_pos (show (x 1).val < (x 0).val from h2)]
      · rw [if_neg h2, if_neg (show ¬ (x 1).val < (x 0).val from h2)]
  · have hvu : ¬ v = u := fun h => huv h.symm
    simp only [Fin.snoc_inj, huv, hvu, false_and, if_false, lex_snoc_lt, or_false]
    split_ifs <;> simp_all

theorem anti2_iff {α : Type*} [Preorder α] (f : Fin 2 → α) : Antitone f ↔ f 1 ≤ f 0 := by
  rw [Fin.antitone_iff_succ_le]
  constructor
  · intro h
    exact h 0
  · intro h i
    fin_cases i
    exact h

theorem colsAnti_iff {n : ℕ} (A : Fin n → Row) :
    Antitone (fun j => toLex (fun i => A i j)) ↔ cs A ≤ 1 := by
  classical
  rw [anti2_iff]
  show toLex (fun i => A i 1) ≤ toLex (fun i => A i 0) ↔ cs A ≤ 1
  rw [lexle_iff']
  unfold cs
  split_ifs with ha hb
  · exact ⟨fun _ => by norm_num, fun _ => Or.inr ha.symm⟩
  · exact ⟨fun _ => by norm_num, fun _ => Or.inl hb⟩
  · constructor
    · rintro (h | h)
      · exact absurd h hb
      · exact absurd h.symm ha
    · intro h
      omega

theorem rowsMono_snoc {m : ℕ} (A : Fin (m + 1) → Row) (x : Row) :
    Monotone (fun i => toLex ((Fin.snoc A x : Fin (m + 2) → Row) i)) ↔
      Monotone (fun i => toLex (A i)) ∧ toLex (A (Fin.last m)) ≤ toLex x := by
  rw [Fin.monotone_iff_le_succ, Fin.monotone_iff_le_succ, Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, Fin.succ_castSucc]

theorem sorted_snoc {m : ℕ} (A : Fin (m + 1) → Row) (x : Row) :
    Sorted (Fin.snoc A x : Fin (m + 2) → Row) ↔
      Sorted A ∧ rc (A (Fin.last m)) ≤ rc x ∧ fstep (cs A) (rc x) ≤ 1 := by
  unfold Sorted
  rw [rowsMono_snoc, colsAnti_iff, colsAnti_iff, cs_snoc, rowle_iff]
  have : fstep (cs A) (rc x) ≤ 1 → cs A ≤ 1 := by
    unfold fstep
    split_ifs <;> omega
  tauto

theorem cs_zero (A : Fin 0 → Row) : cs A = 0 := by
  unfold cs
  rw [if_pos (funext fun i => Fin.elim0 i)]

theorem cs_one (A : Fin 1 → Row) : cs A = fstep 0 (rc (A 0)) := by
  have h := cs_snoc (Fin.init A) (A (Fin.last 0))
  rw [Fin.snoc_init_self, cs_zero] at h
  exact h

theorem sorted_one (A : Fin 1 → Row) : Sorted A ↔ cs A ≤ 1 := by
  unfold Sorted
  rw [colsAnti_iff]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun i j _ => ?_, h⟩
    rw [Subsingleton.elim i j]

/-- Row `k` of `A`, or the padding row `(3, 3)` if there is no such row. -/
def pad {n : ℕ} (A : Fin n → Row) (k : ℕ) : Row := if h : k < n then A ⟨k, h⟩ else topR

/-- The row above row `i`, or the padding row if `i` is the first row. -/
def prv {n : ℕ} (A : Fin n → Row) (i : Fin n) : Row :=
  if i.val = 0 then topR else pad A (i.val - 1)

/-- The array of minima. -/
noncomputable def M {n : ℕ} (A : Fin n → Row) : Fin n → Row := fun i j => minNbr A (i, j)

theorem le_topR (v : Fin 4) (j : Fin 2) : v ≤ topR j := Fin.le_last v

theorem isNbr_iff {n : ℕ} (p q : Fin n × Fin 2) : IsNbr p q ↔
    (((q.1 : ℤ) - p.1 = 0 ∧ (q.2 : ℤ) - p.2 = 0) ∨ ((q.1 : ℤ) - p.1 = 0 ∧ (q.2 : ℤ) - p.2 = 1) ∨
     ((q.1 : ℤ) - p.1 = 0 ∧ (q.2 : ℤ) - p.2 = -1) ∨ ((q.1 : ℤ) - p.1 = 1 ∧ (q.2 : ℤ) - p.2 = 0) ∨
     ((q.1 : ℤ) - p.1 = -1 ∧ (q.2 : ℤ) - p.2 = 0) ∨
     ((q.1 : ℤ) - p.1 = -1 ∧ (q.2 : ℤ) - p.2 = -1) ∨
     ((q.1 : ℤ) - p.1 = 1 ∧ (q.2 : ℤ) - p.2 = 1)) := by
  unfold IsNbr
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]

theorem inf_le_cell {n : ℕ} (A : Fin n → Row) (p q : Fin n × Fin 2) (h : IsNbr p q) :
    minNbr A p ≤ A q.1 q.2 := by
  classical
  unfold minNbr
  exact Finset.inf_le (f := fun q => A q.1 q.2) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

theorem le_minNbr {n : ℕ} (A : Fin n → Row) (p : Fin n × Fin 2) (v : Fin 4)
    (h : ∀ q, IsNbr p q → v ≤ A q.1 q.2) : v ≤ minNbr A p := by
  classical
  unfold minNbr
  exact Finset.le_inf fun q hq => h q (Finset.mem_filter.mp hq).2

theorem prv_eq {n : ℕ} (A : Fin n → Row) (i q : Fin n) (h : (q : ℤ) - i = -1) : prv A i = A q := by
  unfold prv pad
  rw [if_neg (by omega), dif_pos (by omega)]
  congr 1
  exact Fin.ext (by simp only; omega)

theorem pad_eq {n : ℕ} (A : Fin n → Row) (i q : Fin n) (h : (q : ℤ) - i = 1) :
    pad A (i.val + 1) = A q := by
  unfold pad
  rw [dif_pos (by omega)]
  congr 1
  exact Fin.ext (by simp only; omega)

theorem minNbr_zero {n : ℕ} (A : Fin n → Row) (i : Fin n) :
    minNbr A (i, 0) =
      A i 0 ⊓ A i 1 ⊓ prv A i 0 ⊓ pad A (i.val + 1) 0 ⊓ pad A (i.val + 1) 1 := by
  have hi := i.isLt
  apply le_antisymm
  · refine le_inf (le_inf (le_inf (le_inf ?_ ?_) ?_) ?_) ?_
    · exact inf_le_cell A (i, 0) (i, 0) (by rw [isNbr_iff]; simp)
    · exact inf_le_cell A (i, 0) (i, 1) (by rw [isNbr_iff]; simp)
    · unfold prv
      split_ifs with h0
      · exact le_topR _ _
      · have h' : i.val - 1 < n := by omega
        unfold pad
        rw [dif_pos h']
        exact inf_le_cell A (i, 0) (⟨i.val - 1, h'⟩, 0) (by rw [isNbr_iff]; simp; omega)
    · unfold pad
      split_ifs with h'
      · exact inf_le_cell A (i, 0) (⟨i.val + 1, h'⟩, 0) (by rw [isNbr_iff]; simp)
      · exact le_topR _ _
    · unfold pad
      split_ifs with h'
      · exact inf_le_cell A (i, 0) (⟨i.val + 1, h'⟩, 1) (by rw [isNbr_iff]; simp)
      · exact le_topR _ _
  · apply le_minNbr
    rintro ⟨q1, q2⟩ hq
    rw [isNbr_iff] at hq
    simp only [Fin.val_zero, Nat.cast_zero, sub_zero] at hq
    show _ ≤ A q1 q2
    have h1 := q1.isLt
    have h2 := q2.isLt
    rcases hq with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · obtain rfl : q1 = i := Fin.ext (by omega)
      obtain rfl : q2 = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
      simp
    · obtain rfl : q1 = i := Fin.ext (by omega)
      obtain rfl : q2 = 1 := Fin.ext (by rw [Fin.val_one]; omega)
      simp
    · omega
    · obtain rfl : q2 = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
      rw [pad_eq A i q1 ha]
      simp
    · obtain rfl : q2 = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
      rw [prv_eq A i q1 ha]
      simp
    · omega
    · obtain rfl : q2 = 1 := Fin.ext (by rw [Fin.val_one]; omega)
      rw [pad_eq A i q1 ha]
      simp

theorem minNbr_one {n : ℕ} (A : Fin n → Row) (i : Fin n) :
    minNbr A (i, 1) = A i 0 ⊓ A i 1 ⊓ prv A i 0 ⊓ prv A i 1 ⊓ pad A (i.val + 1) 1 := by
  have hi := i.isLt
  apply le_antisymm
  · refine le_inf (le_inf (le_inf (le_inf ?_ ?_) ?_) ?_) ?_
    · exact inf_le_cell A (i, 1) (i, 0) (by rw [isNbr_iff]; simp)
    · exact inf_le_cell A (i, 1) (i, 1) (by rw [isNbr_iff]; simp)
    · unfold prv
      split_ifs with h0
      · exact le_topR _ _
      · have h' : i.val - 1 < n := by omega
        unfold pad
        rw [dif_pos h']
        exact inf_le_cell A (i, 1) (⟨i.val - 1, h'⟩, 0) (by rw [isNbr_iff]; simp; omega)
    · unfold prv
      split_ifs with h0
      · exact le_topR _ _
      · have h' : i.val - 1 < n := by omega
        unfold pad
        rw [dif_pos h']
        exact inf_le_cell A (i, 1) (⟨i.val - 1, h'⟩, 1) (by rw [isNbr_iff]; simp; omega)
    · unfold pad
      split_ifs with h'
      · exact inf_le_cell A (i, 1) (⟨i.val + 1, h'⟩, 1) (by rw [isNbr_iff]; simp)
      · exact le_topR _ _
  · apply le_minNbr
    rintro ⟨q1, q2⟩ hq
    rw [isNbr_iff] at hq
    simp only [Fin.val_one, Nat.cast_one] at hq
    show _ ≤ A q1 q2
    have h1 := q1.isLt
    have h2 := q2.isLt
    rcases hq with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · obtain rfl : q1 = i := Fin.ext (by omega)
      obtain rfl : q2 = 1 := Fin.ext (by rw [Fin.val_one]; omega)
      simp
    · omega
    · obtain rfl : q1 = i := Fin.ext (by omega)
      obtain rfl : q2 = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
      simp
    · obtain rfl : q2 = 1 := Fin.ext (by rw [Fin.val_one]; omega)
      rw [pad_eq A i q1 ha]
      simp
    · obtain rfl : q2 = 1 := Fin.ext (by rw [Fin.val_one]; omega)
      rw [prv_eq A i q1 ha]
      simp
    · obtain rfl : q2 = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
      rw [prv_eq A i q1 ha]
      simp
    · omega

theorem M_eq {n : ℕ} (A : Fin n → Row) (i : Fin n) :
    M A i = G (prv A i) (A i) (pad A (i.val + 1)) := by
  funext j
  fin_cases j
  · exact minNbr_zero A i
  · exact minNbr_one A i

/-! ### Adding a row at the bottom -/

theorem pad_snoc_lt {m : ℕ} (A : Fin (m + 1) → Row) (x : Row) (k : ℕ) (hk : k < m + 1) :
    pad (Fin.snoc A x : Fin (m + 2) → Row) k = pad A k := by
  unfold pad
  rw [dif_pos (by omega), dif_pos hk]
  exact Fin.snoc_castSucc (α := fun _ => Row) (i := ⟨k, hk⟩) (p := A) (x := x)

theorem pad_snoc_last {m : ℕ} (A : Fin (m + 1) → Row) (x : Row) :
    pad (Fin.snoc A x : Fin (m + 2) → Row) (m + 1) = x := by
  unfold pad
  rw [dif_pos (by omega)]
  exact Fin.snoc_last (α := fun _ => Row) (p := A) (x := x)

theorem prv_snoc_cast {m : ℕ} (A : Fin (m + 1) → Row) (x : Row) (i : Fin (m + 1)) :
    prv (Fin.snoc A x : Fin (m + 2) → Row) i.castSucc = prv A i := by
  have hi := i.isLt
  unfold prv
  simp only [Fin.val_castSucc]
  split_ifs with h
  · rfl
  · exact pad_snoc_lt A x _ (by omega)

theorem prv_snoc_last {m : ℕ} (A : Fin (m + 1) → Row) (x : Row) :
    prv (Fin.snoc A x : Fin (m + 2) → Row) (Fin.last (m + 1)) = A (Fin.last m) := by
  unfold prv
  simp only [Fin.val_last]
  rw [if_neg (by omega), show m + 1 - 1 = m by omega, pad_snoc_lt A x m (by omega)]
  unfold pad
  rw [dif_pos (by omega)]
  rfl

/-- The array of minima without its last row. -/
noncomputable def P {m : ℕ} (A : Fin (m + 1) → Row) : Fin m → Row := Fin.init (M A)

theorem P_snoc {m : ℕ} (A : Fin (m + 1) → Row) (x : Row) :
    P (Fin.snoc A x : Fin (m + 2) → Row) =
      Fin.snoc (P A) (G (prv A (Fin.last m)) (A (Fin.last m)) x) := by
  funext i
  unfold P
  cases i using Fin.lastCases with
  | last =>
    rw [Fin.snoc_last]
    show M (Fin.snoc A x : Fin (m + 2) → Row) (Fin.last m).castSucc = _
    rw [M_eq, prv_snoc_cast, Fin.snoc_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [pad_snoc_last]
  | cast i =>
    rw [Fin.snoc_castSucc]
    show M (Fin.snoc A x : Fin (m + 2) → Row) i.castSucc.castSucc = M A i.castSucc
    have hi := i.isLt
    rw [M_eq, M_eq, prv_snoc_cast, Fin.snoc_castSucc]
    simp only [Fin.val_castSucc]
    rw [pad_snoc_lt A x _ (by omega)]

theorem M_last {m : ℕ} (A : Fin (m + 1) → Row) :
    M A (Fin.last m) = G (prv A (Fin.last m)) (A (Fin.last m)) topR := by
  rw [M_eq]
  congr 1
  unfold pad
  rw [dif_neg (by simp)]

/-! ### The automaton -/

/-- The code of a tail: the row above the last row (`p`, the padding row 15 if there is none),
the last row (`b`) and the column state (`f`). -/
def tc (p b f : ℕ) : ℕ := 2 * (16 * p + b) + f

theorem tc_dec (p b f : ℕ) (hb : b < 16) (hf : f ≤ 1) :
    tc p b f / 32 = p ∧ tc p b f / 2 % 16 = b ∧ tc p b f % 2 = f := by
  unfold tc
  omega

/-- The tail of an array with at least one row. -/
noncomputable def tl {m : ℕ} (A : Fin (m + 1) → Row) : ℕ :=
  tc (rc (prv A (Fin.last m))) (rc (A (Fin.last m))) (cs A)

theorem tl_snoc {m : ℕ} (A : Fin (m + 1) → Row) (x : Row) :
    tl (Fin.snoc A x : Fin (m + 2) → Row) =
      tc (rc (A (Fin.last m))) (rc x) (fstep (cs A) (rc x)) := by
  unfold tl
  rw [prv_snoc_last, Fin.snoc_last, cs_snoc]

theorem tl_one (A : Fin 1 → Row) : tl A = tc 15 (rc (A 0)) (fstep 0 (rc (A 0))) := by
  unfold tl
  rw [cs_one]
  have : prv A (Fin.last 0) = topR := by
    unfold prv
    rw [if_pos (Fin.val_last 0)]
  rw [this, rc_topR]
  rfl

theorem cs_le_of_sorted {n : ℕ} (A : Fin n → Row) (h : Sorted A) : cs A ≤ 1 :=
  (colsAnti_iff A).mp h.2

/-- The tails of the 24 live states. -/
def TS : List (List ℕ) :=
  [[480, 489, 490, 497, 499, 500, 505, 507, 509, 510],
   [0, 9, 10, 17, 19, 20, 25, 27, 29, 30, 137, 139, 141, 143, 145, 147, 149, 151, 153, 155, 157,
    159, 177, 185, 273, 275, 277, 279, 281, 283, 285, 287, 313, 345, 409, 411, 413, 415],
   [170, 179, 180, 187, 189, 190, 307, 309, 311, 315, 317, 319, 347, 443, 445, 447],
   [340, 349, 350, 477, 479],
   [510],
   [0, 9, 10, 17, 19, 20, 25, 27, 29, 30, 137, 139, 141, 143, 145, 147, 149, 151, 153, 155, 157,
    159, 170, 177, 179, 180, 185, 187, 189, 190, 209, 217, 241, 249, 273, 275, 277, 279, 281, 283,
    285, 287, 307, 309, 311, 313, 315, 317, 319, 340, 345, 347, 349, 350, 377, 409, 411, 413, 415,
    443, 445, 447, 477, 479, 510],
   [171, 173, 175, 179, 181, 183, 187, 189, 191, 205, 207, 211, 213, 215, 219, 221, 223, 239, 243,
    245, 247, 251, 253, 255, 307, 309, 311, 315, 317, 319, 341, 343, 347, 349, 351, 375, 379, 381,
    383, 443, 445, 447, 477, 479, 511],
   [341, 343, 349, 351, 375, 381, 383, 477, 479, 511],
   [511],
   [177, 185, 313, 345, 377],
   [170, 179, 180, 187, 189, 190, 307, 309, 311, 315, 317, 319, 340, 347, 349, 350, 379, 443, 445,
    447, 477, 479, 510],
   [345],
   [347],
   [340, 349, 350, 477, 479, 510],
   [177, 185, 209, 217, 241, 249, 313, 345, 377],
   [345, 377],
   [347, 379],
   [273, 275, 277, 279, 281, 283, 285, 287, 409, 411, 413, 415],
   [409, 411, 413, 415],
   [443, 445, 447],
   [273, 275, 277, 279, 281, 283, 285, 287, 313, 345, 377, 409, 411, 413, 415],
   [307, 309, 311, 315, 317, 319, 347, 379, 443, 445, 447],
   [477, 479],
   [313, 345, 377]]

/-- The tails of the state `s` (none for the dead state 24). -/
def tails (s : ℕ) : List ℕ := if s < 24 then TS.getD s [] else []

/-- The transitions of the 24 live states on the letters 0..15. -/
def TT : List (List ℕ) :=
  [[1, 24, 24, 24, 24, 2, 24, 24, 24, 24, 3, 24, 24, 24, 24, 4],
   [5, 24, 24, 24, 6, 24, 24, 24, 7, 24, 24, 24, 8, 24, 24, 24],
   [9, 24, 24, 24, 24, 10, 24, 24, 24, 7, 24, 24, 24, 8, 24, 24],
   [11, 24, 24, 24, 24, 12, 24, 24, 24, 24, 13, 24, 24, 24, 8, 24],
   [24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 4],
   [5, 24, 24, 24, 6, 10, 24, 24, 7, 7, 13, 24, 8, 8, 8, 4],
   [14, 24, 24, 24, 24, 6, 24, 24, 24, 7, 7, 24, 24, 8, 8, 8],
   [15, 24, 24, 24, 24, 16, 24, 24, 24, 24, 7, 24, 24, 24, 8, 8],
   [24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 8],
   [17, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24],
   [9, 24, 24, 24, 24, 10, 24, 24, 24, 7, 13, 24, 24, 8, 8, 4],
   [18, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24],
   [24, 24, 24, 24, 24, 19, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24],
   [11, 24, 24, 24, 24, 12, 24, 24, 24, 24, 13, 24, 24, 24, 8, 4],
   [17, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24],
   [18, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24],
   [24, 24, 24, 24, 24, 19, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24],
   [20, 24, 24, 24, 21, 24, 24, 24, 7, 24, 24, 24, 8, 24, 24, 24],
   [18, 24, 24, 24, 19, 24, 24, 24, 22, 24, 24, 24, 8, 24, 24, 24],
   [24, 24, 24, 24, 24, 19, 24, 24, 24, 22, 24, 24, 24, 8, 24, 24],
   [20, 24, 24, 24, 21, 24, 24, 24, 7, 24, 24, 24, 8, 24, 24, 24],
   [23, 24, 24, 24, 24, 21, 24, 24, 24, 7, 24, 24, 24, 8, 24, 24],
   [24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 22, 24, 24, 24, 8, 24],
   [18, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24]]

/-- The transition of the automaton (24 is the dead state). -/
def tau (s g : ℕ) : ℕ := if s < 24 ∧ g < 16 then (TT.getD s []).getD g 24 else 24

/-- The automaton read on the word `β` of rows of the array of minima. -/
def run : (m : ℕ) → (Fin m → Row) → ℕ
  | 0, _ => 0
  | m + 1, β => tau (run m (Fin.init β)) (rc (β (Fin.last m)))

theorem run_snoc {m : ℕ} (β : Fin m → Row) (γ : Row) :
    run (m + 1) (Fin.snoc β γ) = tau (run m β) (rc γ) := by
  show tau (run m (Fin.init (Fin.snoc β γ : Fin (m + 1) → Row)))
    (rc ((Fin.snoc β γ : Fin (m + 1) → Row) (Fin.last m))) = _
  rw [Fin.init_snoc, Fin.snoc_last]

theorem chk_init_a : ∀ r < 16, fstep 0 r ≤ 1 → tc 15 r (fstep 0 r) ∈ tails 0 := by
  decide +kernel

theorem chk_init_b : ∀ t ∈ tails 0,
    t / 32 = 15 ∧ fstep 0 (t / 2 % 16) ≤ 1 ∧ t % 2 = fstep 0 (t / 2 % 16) := by
  decide +kernel

theorem chk_fwd : ∀ s < 24, ∀ t ∈ tails s, ∀ x < 16, t / 2 % 16 ≤ x → fstep (t % 2) x ≤ 1 →
    tc (t / 2 % 16) x (fstep (t % 2) x) ∈ tails (tau s (gm (t / 32) (t / 2 % 16) x)) := by
  decide +kernel

theorem chk_bwd : ∀ s < 24, ∀ g < 16, ∀ u ∈ tails (tau s g), ∃ t ∈ tails s,
    t / 2 % 16 ≤ u / 2 % 16 ∧ fstep (t % 2) (u / 2 % 16) ≤ 1 ∧
      gm (t / 32) (t / 2 % 16) (u / 2 % 16) = g ∧
      u = tc (t / 2 % 16) (u / 2 % 16) (fstep (t % 2) (u / 2 % 16)) := by
  decide +kernel

theorem lt24_of_mem {s t : ℕ} (h : t ∈ tails s) : s < 24 := by
  by_contra hs
  unfold tails at h
  rw [if_neg hs] at h
  exact absurd h List.not_mem_nil

theorem sound : ∀ (m : ℕ) (A : Fin (m + 1) → Row), Sorted A → tl A ∈ tails (run m (P A)) := by
  intro m
  induction m with
  | zero =>
    intro A hA
    rw [sorted_one, cs_one] at hA
    rw [tl_one]
    exact chk_init_a (rc (A 0)) (rc_lt _) hA
  | succ m ih =>
    intro A hA
    obtain ⟨A0, x, rfl⟩ : ∃ (A0 : Fin (m + 1) → Row) (x : Row), A = Fin.snoc A0 x :=
      ⟨Fin.init A, A (Fin.last _), (Fin.snoc_init_self A).symm⟩
    rw [sorted_snoc] at hA
    obtain ⟨hA0, hle, hf⟩ := hA
    have ih' := ih A0 hA0
    rw [P_snoc, run_snoc, tl_snoc, rc_G]
    have key := chk_fwd _ (lt24_of_mem ih') (tl A0) ih' (rc x) (rc_lt x)
    obtain ⟨d1, d2, d3⟩ := tc_dec (rc (prv A0 (Fin.last m))) (rc (A0 (Fin.last m))) (cs A0)
      (rc_lt _) (cs_le_of_sorted A0 hA0)
    unfold tl at key
    rw [d1, d2, d3] at key
    exact key hle hf

theorem complete : ∀ (m : ℕ) (β : Fin m → Row) (t : ℕ), t ∈ tails (run m β) →
    ∃ A : Fin (m + 1) → Row, Sorted A ∧ P A = β ∧ tl A = t := by
  intro m
  induction m with
  | zero =>
    intro β t ht
    obtain ⟨h1, h2, h3⟩ := chk_init_b t ht
    have hr : t / 2 % 16 < 16 := Nat.mod_lt _ (by norm_num)
    refine ⟨fun _ => rowOf (t / 2 % 16), ?_, ?_, ?_⟩
    · rw [sorted_one, cs_one, rc_rowOf _ hr]
      exact h2
    · funext i
      exact Fin.elim0 i
    · rw [tl_one, rc_rowOf _ hr]
      unfold tc
      omega
  | succ m ih =>
    intro β u hu
    obtain ⟨β0, γ, rfl⟩ : ∃ (β0 : Fin m → Row) (γ : Row), β = Fin.snoc β0 γ :=
      ⟨Fin.init β, β (Fin.last _), (Fin.snoc_init_self β).symm⟩
    rw [run_snoc] at hu
    have hs : run m β0 < 24 := by
      by_contra h
      have : tau (run m β0) (rc γ) = 24 := by
        unfold tau
        rw [if_neg (by omega)]
      rw [this] at hu
      exact absurd (lt24_of_mem hu) (lt_irrefl _)
    obtain ⟨t, ht, c1, c2, c3, c4⟩ := chk_bwd _ hs (rc γ) (rc_lt γ) u hu
    obtain ⟨A0, hA0, hP, htl⟩ := ih β0 t ht
    obtain ⟨d1, d2, d3⟩ := tc_dec (rc (prv A0 (Fin.last m))) (rc (A0 (Fin.last m))) (cs A0)
      (rc_lt _) (cs_le_of_sorted A0 hA0)
    unfold tl at htl
    rw [htl] at d1 d2 d3
    have hx : u / 2 % 16 < 16 := Nat.mod_lt _ (by norm_num)
    refine ⟨Fin.snoc A0 (rowOf (u / 2 % 16)), ?_, ?_, ?_⟩
    · rw [sorted_snoc, rc_rowOf _ hx]
      refine ⟨hA0, ?_, ?_⟩
      · rw [← d2]
        exact c1
      · rw [← d3]
        exact c2
    · rw [P_snoc, hP]
      congr 1
      apply rc_inj
      rw [rc_G, rc_rowOf _ hx, ← d1, ← d2]
      exact c3
    · rw [tl_snoc, rc_rowOf _ hx, ← d2, ← d3]
      exact c4.symm

/-- The letter `g` (a row code) can end a word that leads to the state `s`. -/
def finOK (s g : ℕ) : Prop := ∃ t ∈ tails s, gm (t / 32) (t / 2 % 16) 15 = g

instance (s g : ℕ) : Decidable (finOK s g) := by
  unfold finOK
  infer_instance

theorem mem_image_iff (m : ℕ) [DecidablePred fun A : Fin (m + 1) → Fin 2 → Fin 4 => Sorted A]
    [DecidableEq (Fin (m + 1) → Fin 2 → Fin 4)] (B : Fin (m + 1) → Row) :
    B ∈ (Finset.univ.filter (fun A : Fin (m + 1) → Fin 2 → Fin 4 => Sorted A)).image
      (fun A => fun i j => minNbr A (i, j)) ↔
      finOK (run m (Fin.init B)) (rc (B (Fin.last m))) := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨A, hA, rfl⟩
    have hA' := (Finset.mem_filter.mp hA).2
    refine ⟨tl A, sound m A hA', ?_⟩
    obtain ⟨d1, d2, d3⟩ := tc_dec (rc (prv A (Fin.last m))) (rc (A (Fin.last m))) (cs A)
      (rc_lt _) (cs_le_of_sorted A hA')
    unfold tl
    rw [d1, d2]
    show gm _ _ 15 = rc (M A (Fin.last m))
    rw [M_last, rc_G, rc_topR]
  · rintro ⟨t, ht, hg⟩
    obtain ⟨A, hA, hP, htl⟩ := complete m (Fin.init B) t ht
    refine ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩, ?_⟩
    show M A = B
    obtain ⟨d1, d2, d3⟩ := tc_dec (rc (prv A (Fin.last m))) (rc (A (Fin.last m))) (cs A)
      (rc_lt _) (cs_le_of_sorted A hA)
    unfold tl at htl
    rw [htl] at d1 d2 d3
    rw [← Fin.snoc_init_self (M A), ← Fin.snoc_init_self B]
    congr 1
    apply rc_inj
    rw [M_last, rc_G, rc_topR, ← d1, ← d2]
    exact hg

/-! ### Counting -/

theorem card_eq_sum {α : Type*} [Fintype α] [DecidableEq α] (I : Finset α) :
    I.card = ∑ x, if x ∈ I then 1 else 0 := by
  rw [← Finset.card_filter, Finset.filter_univ_mem]

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

theorem sum_fiber {X : Type*} [Fintype X] (r : X → ℕ) (hr : ∀ x, r x < 25) (h : ℕ → ℕ) :
    ∑ x, h (r x) = ∑ s ∈ range 25, (∑ x, if r x = s then 1 else 0) * h s := by
  simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (hr x))]

theorem chk_tau : ∀ s < 24, ∀ g < 16, (TT.getD s []).getD g 24 < 25 := by
  decide +kernel

theorem tau_lt (s g : ℕ) : tau s g < 25 := by
  unfold tau
  split_ifs with h
  · exact chk_tau s h.1 g h.2
  · norm_num

theorem run_lt : ∀ (m : ℕ) (β : Fin m → Row), run m β < 25
  | 0, _ => by
    show 0 < 25
    norm_num
  | _ + 1, _ => tau_lt _ _

/-- The number of letters that can end a word leading to the state `s`. -/
def w (s : ℕ) : ℕ := ∑ c ∈ range 16, if finOK s c then 1 else 0

/-- The number of letters leading from the state `s` to the state `s'`. -/
def cnt (s s' : ℕ) : ℕ := ∑ c ∈ range 16, if tau s c = s' then 1 else 0

/-- The number of words of length `m` leading to the state `s`. -/
def N (m s : ℕ) : ℕ := ∑ β : Fin m → Row, if run m β = s then 1 else 0

/-- One step of the counts of the live states. -/
def Mop (f : ℕ → ℕ) (s' : ℕ) : ℕ := ∑ s ∈ range 24, f s * cnt s s'

/-- The number of arrays of minima from the counts of the live states. -/
def Aop (f : ℕ → ℕ) : ℕ := ∑ s ∈ range 24, f s * w s

theorem w_dead : w 24 = 0 := by
  unfold w
  refine Finset.sum_eq_zero fun c _ => if_neg ?_
  rintro ⟨t, ht, -⟩
  exact absurd (lt24_of_mem ht) (lt_irrefl _)

theorem cnt_dead (s' : ℕ) (hs' : s' < 24) : cnt 24 s' = 0 := by
  unfold cnt
  refine Finset.sum_eq_zero fun c _ => if_neg ?_
  unfold tau
  rw [if_neg (by omega)]
  omega

theorem a_succ (m : ℕ) : a (m + 1) = Aop (N m) := by
  classical
  have h1 : a (m + 1) = ∑ B : Fin (m + 1) → Row,
      if finOK (run m (Fin.init B)) (rc (B (Fin.last m))) then 1 else 0 := by
    unfold a
    rw [card_eq_sum]
    exact Finset.sum_congr rfl fun B _ => if_congr (mem_image_iff m B) rfl rfl
  have h2 : (∑ B : Fin (m + 1) → Row,
      if finOK (run m (Fin.init B)) (rc (B (Fin.last m))) then 1 else 0) =
      ∑ β : Fin m → Row, ∑ γ : Row, if finOK (run m β) (rc γ) then 1 else 0 :=
    sum_snoc m (fun β γ => if finOK (run m β) (rc γ) then 1 else 0)
  have h3 : ∀ β : Fin m → Row, (∑ γ : Row, if finOK (run m β) (rc γ) then 1 else 0) =
      w (run m β) := fun β => sum_row (fun c => if finOK (run m β) c then 1 else 0)
  rw [h1, h2, Finset.sum_congr rfl (fun β _ => h3 β),
    sum_fiber (fun β : Fin m → Row => run m β) (run_lt m) w, Finset.sum_range_succ, w_dead,
    mul_zero, add_zero]
  rfl

theorem N_zero (s : ℕ) : N 0 s = if s = 0 then 1 else 0 := by
  unfold N
  rw [Fintype.sum_unique]
  show (if 0 = s then 1 else 0) = _
  by_cases h : s = 0
  · subst h
    rfl
  · rw [if_neg (Ne.symm h), if_neg h]

theorem N_succ (m s' : ℕ) (hs' : s' < 24) : N (m + 1) s' = Mop (N m) s' := by
  have h1 : N (m + 1) s' = ∑ β : Fin m → Row, ∑ γ : Row,
      if tau (run m β) (rc γ) = s' then 1 else 0 :=
    sum_snoc m (fun β γ => if tau (run m β) (rc γ) = s' then 1 else 0)
  have h3 : ∀ β : Fin m → Row, (∑ γ : Row, if tau (run m β) (rc γ) = s' then 1 else 0) =
      cnt (run m β) s' := fun β => sum_row (fun c => if tau (run m β) c = s' then 1 else 0)
  rw [h1, Finset.sum_congr rfl (fun β _ => h3 β),
    sum_fiber (fun β : Fin m → Row => run m β) (run_lt m) (fun s => cnt s s'),
    Finset.sum_range_succ, cnt_dead s' hs', mul_zero, add_zero]
  rfl

/-- The counts `N m` of the live states for `m ≤ 4`. -/
def NV : List (List ℕ) :=
  [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 4, 1, 2, 7, 16, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 0, 0, 0, 0],
   [0, 0, 0, 0, 10, 1, 3, 16, 49, 2, 3, 3, 3, 6, 2, 7, 7, 2, 4, 5, 1, 1, 2, 0]]

/-- The table of the counts `N m s` for `m ≤ 4`. -/
def nv (m s : ℕ) : ℕ := (NV.getD m []).getD s 0

/-- The coefficients `K j` of `N (k + 4) = Sum_j C(k, j) K j`. -/
def KT : List (List ℕ) :=
  [[0, 0, 0, 0, 10, 1, 3, 16, 49, 2, 3, 3, 3, 6, 2, 7, 7, 2, 4, 5, 1, 1, 2, 0],
   [0, 0, 0, 0, 10, 0, 1, 15, 71, 1, 1, 3, 3, 4, 1, 9, 9, 2, 10, 14, 2, 3, 9, 1],
   [0, 0, 0, 0, 5, 0, 0, 10, 79, 0, 0, 1, 1, 1, 0, 6, 6, 0, 13, 22, 2, 4, 24, 2],
   [0, 0, 0, 0, 1, 0, 0, 6, 86, 0, 0, 0, 0, 0, 0, 4, 4, 0, 9, 20, 0, 2, 35, 2],
   [0, 0, 0, 0, 0, 0, 0, 2, 78, 0, 0, 0, 0, 0, 0, 2, 2, 0, 6, 13, 0, 0, 29, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 8, 0, 0, 19, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 29, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 10, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The table of the coefficients `K j s`. -/
def K (j s : ℕ) : ℕ := (KT.getD j []).getD s 0

theorem chk_nv0 : ∀ s < 24, nv 0 s = if s = 0 then 1 else 0 := by
  decide +kernel

theorem chk_nv : ∀ m < 4, ∀ s < 24, Mop (nv m) s = nv (m + 1) s := by
  decide +kernel

theorem chk_K0 : ∀ s < 24, K 0 s = nv 4 s := by
  decide +kernel

theorem chk_K : ∀ j < 9, ∀ s < 24, Mop (K j) s = K j s + K (j + 1) s := by
  decide +kernel

theorem chk_A : Aop (nv 0) = 4 ∧ Aop (nv 1) = 10 ∧ Aop (nv 2) = 38 ∧ Aop (nv 3) = 103 := by
  decide +kernel

theorem chk_AK : Aop (K 0) = 245 ∧ Aop (K 1) = 302 ∧ Aop (K 2) = 319 ∧ Aop (K 3) = 287 ∧
    Aop (K 4) = 209 ∧ Aop (K 5) = 122 ∧ Aop (K 6) = 55 ∧ Aop (K 7) = 16 ∧ Aop (K 8) = 2 := by
  decide +kernel

theorem K_nine (s : ℕ) : K 9 s = 0 := rfl

theorem Mop_congr {f g : ℕ → ℕ} (h : ∀ s < 24, f s = g s) (s' : ℕ) : Mop f s' = Mop g s' := by
  unfold Mop
  exact Finset.sum_congr rfl fun s hs => by rw [h s (Finset.mem_range.mp hs)]

theorem Aop_congr {f g : ℕ → ℕ} (h : ∀ s < 24, f s = g s) : Aop f = Aop g := by
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
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem N_small : ∀ m ≤ 4, ∀ s < 24, N m s = nv m s := by
  intro m
  induction m with
  | zero =>
    intro _ s hs
    rw [N_zero, chk_nv0 s hs]
  | succ m ih =>
    intro hm s hs
    rw [N_succ m s hs, Mop_congr (g := nv m) (fun s' hs' => ih (by omega) s' hs') s,
      chk_nv m (by omega) s hs]

theorem N_big (k : ℕ) : ∀ s < 24, N (k + 4) s = ∑ j ∈ range 9, k.choose j * K j s := by
  induction k with
  | zero =>
    intro s hs
    rw [Nat.zero_add, N_small 4 le_rfl s hs, ← chk_K0 s hs]
    simp [Finset.sum_range_succ]
  | succ k ih =>
    intro s hs
    rw [show k + 1 + 4 = (k + 4) + 1 by omega, N_succ _ s hs,
      Mop_congr (g := fun s => ∑ j ∈ range 9, k.choose j * K j s) ih, Mop_lin]
    rw [Finset.sum_congr rfl (fun j hj => by rw [chk_K j (Finset.mem_range.mp hj) s hs])]
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

theorem a_small : a 1 = 4 ∧ a 2 = 10 ∧ a 3 = 38 ∧ a 4 = 103 := by
  obtain ⟨h0, h1, h2, h3⟩ := chk_A
  refine ⟨?_, ?_, ?_, ?_⟩
  · show a (0 + 1) = 4
    rw [a_succ, Aop_congr (fun s hs => N_small 0 (by norm_num) s hs), h0]
  · show a (1 + 1) = 10
    rw [a_succ, Aop_congr (fun s hs => N_small 1 (by norm_num) s hs), h1]
  · show a (2 + 1) = 38
    rw [a_succ, Aop_congr (fun s hs => N_small 2 (by norm_num) s hs), h2]
  · show a (3 + 1) = 103
    rw [a_succ, Aop_congr (fun s hs => N_small 3 (by norm_num) s hs), h3]

theorem a_big (k : ℕ) :
    a (k + 5) = 245 + 302 * k + 319 * k.choose 2 + 287 * k.choose 3 + 209 * k.choose 4 +
      122 * k.choose 5 + 55 * k.choose 6 + 16 * k.choose 7 + 2 * k.choose 8 := by
  rw [show k + 5 = (k + 4) + 1 by omega, a_succ,
    Aop_congr (g := fun s => ∑ j ∈ range 9, k.choose j * K j s) (N_big k), Aop_lin]
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

theorem choose7 (m : ℕ) :
    (m.choose 7 : ℚ) = m * (m - 1) * (m - 2) * (m - 3) * (m - 4) * (m - 5) * (m - 6) / 5040 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, choose6]
    push_cast
    ring

theorem choose8 (m : ℕ) :
    (m.choose 8 : ℚ) =
      m * (m - 1) * (m - 2) * (m - 3) * (m - 4) * (m - 5) * (m - 6) * (m - 7) / 40320 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, choose7]
    push_cast
    ring

theorem closedQ (n : ℕ) (hn : 2 ≤ n) :
    (a n : ℚ) = ((n : ℚ) ^ 8 - 4 * (n : ℚ) ^ 7 - 42 * (n : ℚ) ^ 6 + 2996 * (n : ℚ) ^ 5
      - 24171 * (n : ℚ) ^ 4 + 124544 * (n : ℚ) ^ 3 - 217708 * (n : ℚ) ^ 2 + 255504 * (n : ℚ)
      - 141120) / 20160 := by
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n
    · rw [a_small.2.1]
      norm_num
    · rw [a_small.2.2.1]
      norm_num
    · rw [a_small.2.2.2]
      norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
    rw [a_big]
    push_cast
    rw [choose2, choose3, choose4, choose5, choose6, choose7, choose8]
    ring

theorem hardin (n : ℕ) (hn : 1 < n) :
    (a n : ℚ) = (1 / 20160) * (n : ℚ) ^ 8 - (1 / 5040) * (n : ℚ) ^ 7 - (1 / 480) * (n : ℚ) ^ 6
      + (107 / 720) * (n : ℚ) ^ 5 - (1151 / 960) * (n : ℚ) ^ 4 + (278 / 45) * (n : ℚ) ^ 3
      - (54427 / 5040) * (n : ℚ) ^ 2 + (5323 / 420) * (n : ℚ) - 7 := by
  rw [closedQ n hn]
  ring

theorem recurrence (n : ℕ) (hn : 10 < n) :
    (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) -
      126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) +
      a (n - 9) := by
  have h : ((a n : ℤ) : ℚ) = ((9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) -
      126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) +
      a (n - 9) : ℤ) : ℚ) := by
    push_cast
    rw [closedQ n (by omega), closedQ (n - 1) (by omega), closedQ (n - 2) (by omega),
      closedQ (n - 3) (by omega), closedQ (n - 4) (by omega), closedQ (n - 5) (by omega),
      closedQ (n - 6) (by omega), closedQ (n - 7) (by omega), closedQ (n - 8) (by omega),
      closedQ (n - 9) (by omega)]
    push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega,
      show 8 ≤ n by omega, show 9 ≤ n by omega]
    ring
  exact_mod_cast h

theorem a_mid : a 5 = 245 ∧ a 6 = 547 ∧ a 7 = 1168 ∧ a 8 = 2395 ∧ a 9 = 4724 ∧
    a 10 = 8982 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := a_big 0
    norm_num [Nat.choose] at h
    exact h
  · have h := a_big 1
    norm_num [Nat.choose] at h
    exact h
  · have h := a_big 2
    norm_num [Nat.choose] at h
    exact h
  · have h := a_big 3
    norm_num [Nat.choose] at h
    exact h
  · have h := a_big 4
    norm_num [Nat.choose] at h
    exact h
  · have h := a_big 5
    norm_num [Nat.choose] at h
    exact h

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
        X * (4 - 26 * X + 92 * X ^ 2 - 215 * X ^ 3 + 350 * X ^ 4 - 386 * X ^ 5 + 277 * X ^ 6
          - 119 * X ^ 7 + 29 * X ^ 8 - 4 * X ^ 9) := by
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hF
  have key : PowerSeries.mk F * (1 - X) ^ 9 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 9 * (PowerSeries.mk F * X ^ 1) +
        C 36 * (PowerSeries.mk F * X ^ 2) - C 84 * (PowerSeries.mk F * X ^ 3) +
        C 126 * (PowerSeries.mk F * X ^ 4) - C 126 * (PowerSeries.mk F * X ^ 5) +
        C 84 * (PowerSeries.mk F * X ^ 6) - C 36 * (PowerSeries.mk F * X ^ 7) +
        C 9 * (PowerSeries.mk F * X ^ 8) - C 1 * (PowerSeries.mk F * X ^ 9) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (4 - 26 * X + 92 * X ^ 2 - 215 * X ^ 3 + 350 * X ^ 4 - 386 * X ^ 5
      + 277 * X ^ 6 - 119 * X ^ 7 + 29 * X ^ 8 - 4 * X ^ 9) =
      C 4 * X ^ 1 - C 26 * X ^ 2 + C 92 * X ^ 3 - C 215 * X ^ 4 + C 350 * X ^ 5 -
        C 386 * X ^ 6 + C 277 * X ^ 7 - C 119 * X ^ 8 + C 29 * X ^ 9 - C 4 * X ^ 10 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  obtain ⟨v1, v2, v3, v4⟩ := a_small
  obtain ⟨v5, v6, v7, v8, v9, v10⟩ := a_mid
  by_cases hk : k < 11
  · interval_cases k <;> norm_num [hF, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 11 := ⟨k - 11, by omega⟩
    simp only [show 0 ≤ j + 11 by omega, show 1 ≤ j + 11 by omega, show 2 ≤ j + 11 by omega,
      show 3 ≤ j + 11 by omega, show 4 ≤ j + 11 by omega, show 5 ≤ j + 11 by omega,
      show 6 ≤ j + 11 by omega, show 7 ≤ j + 11 by omega, show 8 ≤ j + 11 by omega,
      show 9 ≤ j + 11 by omega,
      show j + 11 - 0 = j + 11 by omega, show j + 11 - 1 = j + 10 by omega,
      show j + 11 - 2 = j + 9 by omega, show j + 11 - 3 = j + 8 by omega,
      show j + 11 - 4 = j + 7 by omega, show j + 11 - 5 = j + 6 by omega,
      show j + 11 - 6 = j + 5 by omega, show j + 11 - 7 = j + 4 by omega,
      show j + 11 - 8 = j + 3 by omega, show j + 11 - 9 = j + 2 by omega,
      show ¬ (j + 11 = 1) by omega, show ¬ (j + 11 = 2) by omega, show ¬ (j + 11 = 3) by omega,
      show ¬ (j + 11 = 4) by omega, show ¬ (j + 11 = 5) by omega, show ¬ (j + 11 = 6) by omega,
      show ¬ (j + 11 = 7) by omega, show ¬ (j + 11 = 8) by omega, show ¬ (j + 11 = 9) by omega,
      show ¬ (j + 11 = 10) by omega,
      show ¬ (j + 11 = 0) by omega, show ¬ (j + 10 = 0) by omega, show ¬ (j + 9 = 0) by omega,
      show ¬ (j + 8 = 0) by omega, show ¬ (j + 7 = 0) by omega, show ¬ (j + 6 = 0) by omega,
      show ¬ (j + 5 = 0) by omega, show ¬ (j + 4 = 0) by omega, show ¬ (j + 3 = 0) by omega,
      show ¬ (j + 2 = 0) by omega,
      if_true, if_false, hF]
    rw [closedQ (j + 11) (by omega), closedQ (j + 10) (by omega), closedQ (j + 9) (by omega),
      closedQ (j + 8) (by omega), closedQ (j + 7) (by omega), closedQ (j + 6) (by omega),
      closedQ (j + 5) (by omega), closedQ (j + 4) (by omega), closedQ (j + 3) (by omega),
      closedQ (j + 2) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a220198.main :=
  ⟨OMA.Helpers.hardin, OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
