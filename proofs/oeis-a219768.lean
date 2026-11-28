import OMAStatements.S_oeis_a219768

/-!
Proof of Barker's g.f. and recurrence for A219768 (n X 3 arrays of the minima of each element
and its horizontal and antidiagonal neighbours, over the sorted n X 3 0..1 arrays).

Rows. A row `(x, y, z)` has the code `4 x + 2 y + z < 8` (`rc`, inverse `rowOf`); the
lexicographic order of rows is the order of the codes (`rowle_iff`).

The filter. Row `i` of the array of minima depends only on the rows `i - 1, i, i + 1` of `A`:
it is `G (prv A i) (A i) (pad A (i + 1))` (`M_eq`), where a missing row is replaced by the
padding row `(1, 1, 1)`, which does not change any minimum. On codes, `G` is `gm` (`rc_G`, a
finite check).

Sorted arrays. The rows are nondecreasing iff consecutive rows are. Two words `u, v` have the
comparison state `ps u v`: 0 if they are equal, 1 if `u` is lexicographically smaller, 2
otherwise; appending letters `a, b` changes it to `pstep (ps u v) a b` (`ps_snoc`). The columns
are nondecreasing iff the states of the column pairs (0, 1) and (1, 2) are at most 1; the column
state `cs A` packs these two states into `0..3`, with 4 for a violated pair, and adding a row `x`
at the bottom changes it to `fstep (cs A) (rc x)` (`cs_snoc`). So `Fin.snoc A x` is sorted iff
`A` is sorted, the last row of `A` is at most `x`, and the new column state is at most 3
(`sorted_snoc`).

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
`nv m` (`m ≤ 4`) and `K j` (`j ≤ 4`) satisfy `nv 0 = N 0`, `Mop (nv m) = nv (m + 1)`, `K 0 = nv 4`,
`Mop (K j) = K j + K (j + 1)` and `K 5 = 0` (finite checks). By induction with Pascal's rule
`N (k + 4) = Sum_{j < 5} C(k, j) K j`, hence
`a (k + 5) = 56 + 45 k + 25 C(k, 2) + 8 C(k, 3) + C(k, 4)`, while
`a 1, ..., a 4 = 3, 6, 14, 29`. So `24 a(n) = n^4 + 6 n^3 - 25 n^2 + 138 n - 96` for `n ≥ 2`
(`closedQ`). The recurrence for `n > 6` follows by substituting it (all of `n - 5, ..., n` are at
least 2), and the generating function by comparing coefficients (the coefficients of x^0..x^6 from
the values `0, 3, 6, 14, 29, 56, 101`, the higher ones vanish as fifth differences of a
polynomial of degree 4).
-/

namespace OMA.Helpers

open OMA.S_oeis_a219768 Finset

/-- A row of an n X 3 array. -/
abbrev Row := Fin 3 → Fin 2

/-- The padding row `(1, 1, 1)`. -/
def topR : Row := fun _ => 1

/-- The code `4 x + 2 y + z` of the row `(x, y, z)`. -/
def rc (r : Row) : ℕ := 4 * (r 0).val + 2 * (r 1).val + (r 2).val

/-- The row with code `c < 8`. -/
def rowOf (c : ℕ) : Row :=
  fun j => ⟨(if j.val = 0 then c / 4 else if j.val = 1 then c / 2 else c) % 2,
    Nat.mod_lt _ (by norm_num)⟩

theorem rc_lt (r : Row) : rc r < 8 := by
  unfold rc
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  have h2 := (r 2).isLt
  omega

theorem rowOf_rc (r : Row) : rowOf (rc r) = r := by
  funext j
  apply Fin.ext
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  have h2 := (r 2).isLt
  fin_cases j <;> (simp [rowOf, rc]; try omega)

theorem rc_rowOf (c : ℕ) (hc : c < 8) : rc (rowOf c) = c := by
  unfold rc rowOf
  simp
  omega

theorem rc_inj {r s : Row} (h : rc r = rc s) : r = s := by
  rw [← rowOf_rc r, ← rowOf_rc s, h]

theorem rc_topR : rc topR = 7 := rfl

/-- The minimum filter on one row, from the row above `p`, the row `c` and the row below `q`. -/
def G (p c q : Row) : Row :=
  ![c 0 ⊓ c 1 ⊓ p 1, c 0 ⊓ c 1 ⊓ c 2 ⊓ p 2 ⊓ q 0, c 1 ⊓ c 2 ⊓ q 1]

/-- The function `G` on codes. -/
def gm (p c q : ℕ) : ℕ :=
  4 * min (min (c / 4) (c / 2 % 2)) (p / 2 % 2) +
    2 * min (min (min (min (c / 4) (c / 2 % 2)) (c % 2)) (p % 2)) (q / 4) +
    min (min (c / 2 % 2) (c % 2)) (q / 2 % 2)

theorem gm_check : ∀ a < 8, ∀ b < 8, ∀ c < 8, rc (G (rowOf a) (rowOf b) (rowOf c)) = gm a b c := by
  decide +kernel

theorem rc_G (p c q : Row) : rc (G p c q) = gm (rc p) (rc c) (rc q) := by
  have := gm_check (rc p) (rc_lt p) (rc c) (rc_lt c) (rc q) (rc_lt q)
  rwa [rowOf_rc, rowOf_rc, rowOf_rc] at this

theorem lexlt_iff {k : ℕ} (x y : Fin k → Fin 2) :
    toLex x < toLex y ↔ ∃ i, (∀ j, j < i → x j = y j) ∧ x i < y i := Iff.rfl

theorem row_eq_iff (r s : Row) : r = s ↔ r 0 = s 0 ∧ r 1 = s 1 ∧ r 2 = s 2 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2⟩
    funext j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2

theorem rowlt_iff (r s : Row) : toLex r < toLex s ↔
    r 0 < s 0 ∨ (r 0 = s 0 ∧ r 1 < s 1) ∨ (r 0 = s 0 ∧ r 1 = s 1 ∧ r 2 < s 2) := by
  rw [lexlt_iff]
  constructor
  · rintro ⟨i, hi, hlt⟩
    fin_cases i
    · exact Or.inl hlt
    · exact Or.inr (Or.inl ⟨hi 0 (by decide), hlt⟩)
    · exact Or.inr (Or.inr ⟨hi 0 (by decide), hi 1 (by decide), hlt⟩)
  · rintro (h | ⟨h0, h1⟩ | ⟨h0, h1, h2⟩)
    · exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), h⟩
    · refine ⟨1, fun j hj => ?_, h1⟩
      fin_cases j
      · exact h0
      · exact absurd hj (lt_irrefl _)
      · exact absurd hj (by decide)
    · refine ⟨2, fun j hj => ?_, h2⟩
      fin_cases j
      · exact h0
      · exact h1
      · exact absurd hj (lt_irrefl _)

theorem lexle_iff' {k : ℕ} (x y : Fin k → Fin 2) :
    toLex x ≤ toLex y ↔ toLex x < toLex y ∨ x = y := by
  rw [le_iff_lt_or_eq, toLex_inj]
  exact Iff.rfl

theorem lexlt_irrefl {k : ℕ} (x : Fin k → Fin 2) : ¬ (toLex x < toLex x) := lt_irrefl _

theorem rowle_iff (r s : Row) : toLex r ≤ toLex s ↔ rc r ≤ rc s := by
  rw [lexle_iff', rowlt_iff, row_eq_iff]
  unfold rc
  simp only [Fin.lt_def, Fin.ext_iff]
  have := (r 0).isLt
  have := (r 1).isLt
  have := (r 2).isLt
  have := (s 0).isLt
  have := (s 1).isLt
  have := (s 2).isLt
  omega

theorem lex_snoc_lt {k : ℕ} (u v : Fin k → Fin 2) (a b : Fin 2) :
    toLex (Fin.snoc u a : Fin (k + 1) → Fin 2) < toLex (Fin.snoc v b : Fin (k + 1) → Fin 2) ↔
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

/-! ### Column states -/

/-- The comparison state of two words: 0 if they are equal, 1 if the first one is
lexicographically smaller, 2 otherwise. -/
noncomputable def ps {m : ℕ} (u v : Fin m → Fin 2) : ℕ := by
  classical
  exact if u = v then 0 else if toLex u < toLex v then 1 else 2

/-- The comparison state after appending the letters `a` and `b` to words in state `f`. -/
def pstep (f a b : ℕ) : ℕ :=
  if f = 0 then (if a = b then 0 else if a < b then 1 else 2) else f

theorem ps_snoc {m : ℕ} (u v : Fin m → Fin 2) (a b : Fin 2) :
    ps (Fin.snoc u a : Fin (m + 1) → Fin 2) (Fin.snoc v b) = pstep (ps u v) a.val b.val := by
  classical
  unfold ps pstep
  by_cases huv : u = v
  · subst huv
    simp only [Fin.snoc_inj, true_and, lex_snoc_lt, lexlt_irrefl, false_or, if_true]
    by_cases h1 : a = b
    · rw [if_pos h1, if_pos (congrArg Fin.val h1)]
    · rw [if_neg h1, if_neg (fun h => h1 (Fin.ext h))]
      by_cases h2 : a < b
      · rw [if_pos h2, if_pos (show a.val < b.val from h2)]
      · rw [if_neg h2, if_neg (show ¬ a.val < b.val from h2)]
  · simp only [Fin.snoc_inj, huv, false_and, if_false, lex_snoc_lt, or_false]
    split_ifs <;> simp_all

theorem ps_lt {m : ℕ} (u v : Fin m → Fin 2) : ps u v < 3 := by
  unfold ps
  split_ifs <;> norm_num

theorem pair_le_iff {m : ℕ} (u v : Fin m → Fin 2) : toLex u ≤ toLex v ↔ ps u v ≤ 1 := by
  classical
  rw [lexle_iff']
  unfold ps
  split_ifs with ha hb
  · exact ⟨fun _ => by norm_num, fun _ => Or.inr ha⟩
  · exact ⟨fun _ => by norm_num, fun _ => Or.inl hb⟩
  · constructor
    · rintro (h | h)
      · exact absurd h hb
      · exact absurd h ha
    · intro h
      omega

theorem ps_zero (u v : Fin 0 → Fin 2) : ps u v = 0 := by
  unfold ps
  rw [if_pos (funext fun i => Fin.elim0 i)]

/-- The two comparison states of the column pairs (0, 1) and (1, 2), packed into `0..3`, or 4 if
one of them is 2. -/
def fcomb (a b : ℕ) : ℕ := if a ≤ 1 ∧ b ≤ 1 then a + 2 * b else 4

/-- The column state of `A`. -/
noncomputable def cs {n : ℕ} (A : Fin n → Row) : ℕ :=
  fcomb (ps (fun i => A i 0) (fun i => A i 1)) (ps (fun i => A i 1) (fun i => A i 2))

/-- The column state after adding a row with code `x` to an array with column state `f`. -/
def fstep (f x : ℕ) : ℕ :=
  if f < 4 then fcomb (pstep (f % 2) (x / 4) (x / 2 % 2)) (pstep (f / 2) (x / 2 % 2) (x % 2))
  else 4

theorem fstep_check : ∀ p < 3, ∀ q < 3, ∀ a < 2, ∀ b < 2, ∀ c < 2,
    fcomb (pstep p a b) (pstep q b c) = fstep (fcomb p q) (4 * a + 2 * b + c) := by
  decide +kernel

theorem col_snoc {m : ℕ} (A : Fin m → Row) (x : Row) (j : Fin 3) :
    (fun i => (Fin.snoc A x : Fin (m + 1) → Row) i j) = Fin.snoc (fun i => A i j) (x j) := by
  funext i
  cases i using Fin.lastCases with
  | last => simp
  | cast i => simp

theorem cs_snoc {m : ℕ} (A : Fin m → Row) (x : Row) :
    cs (Fin.snoc A x : Fin (m + 1) → Row) = fstep (cs A) (rc x) := by
  unfold cs
  rw [col_snoc A x 0, col_snoc A x 1, col_snoc A x 2, ps_snoc, ps_snoc]
  exact fstep_check _ (ps_lt _ _) _ (ps_lt _ _) _ (x 0).isLt _ (x 1).isLt _ (x 2).isLt

theorem mono3_iff {α : Type*} [Preorder α] (f : Fin 3 → α) :
    Monotone f ↔ f 0 ≤ f 1 ∧ f 1 ≤ f 2 := by
  rw [Fin.monotone_iff_le_succ]
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · rintro ⟨h0, h1⟩ i
    fin_cases i
    · exact h0
    · exact h1

theorem colsMono_iff {n : ℕ} (A : Fin n → Row) :
    Monotone (fun j => toLex (fun i => A i j)) ↔ cs A ≤ 3 := by
  rw [mono3_iff]
  show toLex (fun i => A i 0) ≤ toLex (fun i => A i 1) ∧
      toLex (fun i => A i 1) ≤ toLex (fun i => A i 2) ↔ cs A ≤ 3
  rw [pair_le_iff, pair_le_iff]
  unfold cs fcomb
  split_ifs with h
  · exact ⟨fun _ => by omega, fun _ => h⟩
  · exact ⟨fun h' => absurd h' h, fun h' => absurd h' (by norm_num)⟩

theorem rowsMono_snoc {m : ℕ} (A : Fin (m + 1) → Row) (x : Row) :
    Monotone (fun i => toLex ((Fin.snoc A x : Fin (m + 2) → Row) i)) ↔
      Monotone (fun i => toLex (A i)) ∧ toLex (A (Fin.last m)) ≤ toLex x := by
  rw [Fin.monotone_iff_le_succ, Fin.monotone_iff_le_succ, Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, Fin.succ_castSucc]

theorem sorted_snoc {m : ℕ} (A : Fin (m + 1) → Row) (x : Row) :
    Sorted (Fin.snoc A x : Fin (m + 2) → Row) ↔
      Sorted A ∧ rc (A (Fin.last m)) ≤ rc x ∧ fstep (cs A) (rc x) ≤ 3 := by
  unfold Sorted
  rw [rowsMono_snoc, colsMono_iff, colsMono_iff, cs_snoc, rowle_iff]
  have : fstep (cs A) (rc x) ≤ 3 → cs A ≤ 3 := by
    unfold fstep
    split_ifs <;> omega
  tauto

theorem cs_zero (A : Fin 0 → Row) : cs A = 0 := by
  unfold cs
  rw [ps_zero, ps_zero]
  rfl

theorem cs_one (A : Fin 1 → Row) : cs A = fstep 0 (rc (A 0)) := by
  have h := cs_snoc (Fin.init A) (A (Fin.last 0))
  rw [Fin.snoc_init_self, cs_zero] at h
  exact h

theorem sorted_one (A : Fin 1 → Row) : Sorted A ↔ cs A ≤ 3 := by
  unfold Sorted
  rw [colsMono_iff]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun i j _ => ?_, h⟩
    rw [Subsingleton.elim i j]

/-! ### The filter -/

/-- Row `k` of `A`, or the padding row `(1, 1, 1)` if there is no such row. -/
def pad {n : ℕ} (A : Fin n → Row) (k : ℕ) : Row := if h : k < n then A ⟨k, h⟩ else topR

/-- The row above row `i`, or the padding row if `i` is the first row. -/
def prv {n : ℕ} (A : Fin n → Row) (i : Fin n) : Row :=
  if i.val = 0 then topR else pad A (i.val - 1)

/-- The array of minima. -/
noncomputable def M {n : ℕ} (A : Fin n → Row) : Fin n → Row := fun i j => minNbr A (i, j)

theorem le_topR (v : Fin 2) (j : Fin 3) : v ≤ topR j := Fin.le_last v

theorem isNbr_iff {n : ℕ} (p q : Fin n × Fin 3) : IsNbr p q ↔
    (((q.1 : ℤ) - p.1 = 0 ∧ (q.2 : ℤ) - p.2 = 0) ∨ ((q.1 : ℤ) - p.1 = 0 ∧ (q.2 : ℤ) - p.2 = 1) ∨
     ((q.1 : ℤ) - p.1 = 0 ∧ (q.2 : ℤ) - p.2 = -1) ∨ ((q.1 : ℤ) - p.1 = -1 ∧ (q.2 : ℤ) - p.2 = 1) ∨
     ((q.1 : ℤ) - p.1 = 1 ∧ (q.2 : ℤ) - p.2 = -1)) := by
  unfold IsNbr
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]

theorem inf_le_cell {n : ℕ} (A : Fin n → Row) (p q : Fin n × Fin 3) (h : IsNbr p q) :
    minNbr A p ≤ A q.1 q.2 := by
  classical
  unfold minNbr
  exact Finset.inf_le (f := fun q => A q.1 q.2) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

theorem le_minNbr {n : ℕ} (A : Fin n → Row) (p : Fin n × Fin 3) (v : Fin 2)
    (h : ∀ q, IsNbr p q → v ≤ A q.1 q.2) : v ≤ minNbr A p := by
  classical
  unfold minNbr
  exact Finset.le_inf fun q hq => h q (Finset.mem_filter.mp hq).2

theorem prv_eq {n : ℕ} (A : Fin n → Row) (i q : Fin n) (h : (q : ℤ) - i = -1) :
    prv A i = A q := by
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
    minNbr A (i, 0) = A i 0 ⊓ A i 1 ⊓ prv A i 1 := by
  have hi := i.isLt
  apply le_antisymm
  · refine le_inf (le_inf ?_ ?_) ?_
    · exact inf_le_cell A (i, 0) (i, 0) (by rw [isNbr_iff]; simp)
    · exact inf_le_cell A (i, 0) (i, 1) (by rw [isNbr_iff]; simp)
    · unfold prv
      split_ifs with h0
      · exact le_topR _ _
      · have h' : i.val - 1 < n := by omega
        unfold pad
        rw [dif_pos h']
        exact inf_le_cell A (i, 0) (⟨i.val - 1, h'⟩, 1) (by rw [isNbr_iff]; simp; omega)
  · apply le_minNbr
    rintro ⟨q1, q2⟩ hq
    rw [isNbr_iff] at hq
    simp only [Fin.val_zero, Nat.cast_zero, sub_zero] at hq
    show _ ≤ A q1 q2
    have h1 := q1.isLt
    have h2 := q2.isLt
    rcases hq with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · obtain rfl : q1 = i := Fin.ext (by omega)
      obtain rfl : q2 = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
      simp
    · obtain rfl : q1 = i := Fin.ext (by omega)
      obtain rfl : q2 = 1 := Fin.ext (by rw [Fin.val_one]; omega)
      simp
    · omega
    · obtain rfl : q2 = 1 := Fin.ext (by rw [Fin.val_one]; omega)
      rw [prv_eq A i q1 ha]
      simp
    · omega

theorem minNbr_one {n : ℕ} (A : Fin n → Row) (i : Fin n) :
    minNbr A (i, 1) = A i 0 ⊓ A i 1 ⊓ A i 2 ⊓ prv A i 2 ⊓ pad A (i.val + 1) 0 := by
  have hi := i.isLt
  apply le_antisymm
  · refine le_inf (le_inf (le_inf (le_inf ?_ ?_) ?_) ?_) ?_
    · exact inf_le_cell A (i, 1) (i, 0) (by rw [isNbr_iff]; simp)
    · exact inf_le_cell A (i, 1) (i, 1) (by rw [isNbr_iff]; simp)
    · exact inf_le_cell A (i, 1) (i, 2) (by rw [isNbr_iff]; simp)
    · unfold prv
      split_ifs with h0
      · exact le_topR _ _
      · have h' : i.val - 1 < n := by omega
        unfold pad
        rw [dif_pos h']
        exact inf_le_cell A (i, 1) (⟨i.val - 1, h'⟩, 2) (by rw [isNbr_iff]; simp; omega)
    · unfold pad
      split_ifs with h'
      · exact inf_le_cell A (i, 1) (⟨i.val + 1, h'⟩, 0) (by rw [isNbr_iff]; simp)
      · exact le_topR _ _
  · apply le_minNbr
    rintro ⟨q1, q2⟩ hq
    rw [isNbr_iff] at hq
    simp only [Fin.val_one, Nat.cast_one] at hq
    show _ ≤ A q1 q2
    have h1 := q1.isLt
    have h2 := q2.isLt
    rcases hq with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · obtain rfl : q1 = i := Fin.ext (by omega)
      obtain rfl : q2 = 1 := Fin.ext (by rw [Fin.val_one]; omega)
      simp
    · obtain rfl : q1 = i := Fin.ext (by omega)
      obtain rfl : q2 = 2 := Fin.ext (by rw [Fin.val_two]; omega)
      simp
    · obtain rfl : q1 = i := Fin.ext (by omega)
      obtain rfl : q2 = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
      simp
    · obtain rfl : q2 = 2 := Fin.ext (by rw [Fin.val_two]; omega)
      rw [prv_eq A i q1 ha]
      simp
    · obtain rfl : q2 = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
      rw [pad_eq A i q1 ha]
      simp

theorem minNbr_two {n : ℕ} (A : Fin n → Row) (i : Fin n) :
    minNbr A (i, 2) = A i 1 ⊓ A i 2 ⊓ pad A (i.val + 1) 1 := by
  have hi := i.isLt
  apply le_antisymm
  · refine le_inf (le_inf ?_ ?_) ?_
    · exact inf_le_cell A (i, 2) (i, 1) (by rw [isNbr_iff]; simp)
    · exact inf_le_cell A (i, 2) (i, 2) (by rw [isNbr_iff]; simp)
    · unfold pad
      split_ifs with h'
      · exact inf_le_cell A (i, 2) (⟨i.val + 1, h'⟩, 1) (by rw [isNbr_iff]; simp)
      · exact le_topR _ _
  · apply le_minNbr
    rintro ⟨q1, q2⟩ hq
    rw [isNbr_iff] at hq
    simp only [Fin.val_two, Nat.cast_ofNat] at hq
    show _ ≤ A q1 q2
    have h1 := q1.isLt
    have h2 := q2.isLt
    rcases hq with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · obtain rfl : q1 = i := Fin.ext (by omega)
      obtain rfl : q2 = 2 := Fin.ext (by rw [Fin.val_two]; omega)
      simp
    · omega
    · obtain rfl : q1 = i := Fin.ext (by omega)
      obtain rfl : q2 = 1 := Fin.ext (by rw [Fin.val_one]; omega)
      simp
    · omega
    · obtain rfl : q2 = 1 := Fin.ext (by rw [Fin.val_one]; omega)
      rw [pad_eq A i q1 ha]
      simp

theorem M_eq {n : ℕ} (A : Fin n → Row) (i : Fin n) :
    M A i = G (prv A i) (A i) (pad A (i.val + 1)) := by
  funext j
  fin_cases j
  · exact minNbr_zero A i
  · exact minNbr_one A i
  · exact minNbr_two A i

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

/-- The code of a tail: the row above the last row (`p`, the padding row 7 if there is none),
the last row (`b`) and the column state (`f`). -/
def tc (p b f : ℕ) : ℕ := 4 * (8 * p + b) + f

theorem tc_dec (p b f : ℕ) (hb : b < 8) (hf : f ≤ 3) :
    tc p b f / 32 = p ∧ tc p b f / 4 % 8 = b ∧ tc p b f % 4 = f := by
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

theorem tl_one (A : Fin 1 → Row) : tl A = tc 7 (rc (A 0)) (fstep 0 (rc (A 0))) := by
  unfold tl
  rw [cs_one]
  have : prv A (Fin.last 0) = topR := by
    unfold prv
    rw [if_pos (Fin.val_last 0)]
  rw [this, rc_topR]
  rfl

theorem cs_le_of_sorted {n : ℕ} (A : Fin n → Row) (h : Sorted A) : cs A ≤ 3 :=
  (colsMono_iff A).mp h.2

/-- The tails of the 24 live states. -/
def TS : List (List ℕ) :=
  [[224, 230, 237, 252],
   [0, 6, 13, 28, 38, 43, 47, 58, 62, 113, 119],
   [109, 125],
   [252],
   [0, 6, 13, 28, 38, 43, 47, 58, 62, 75, 79, 83, 87, 91, 95, 113, 115, 119, 145, 151, 157, 183,
    187, 191, 218, 222],
   [109, 111, 123, 125, 127, 252],
   [254],
   [113, 119],
   [253],
   [0, 6, 13, 28, 38, 43, 47, 58, 62, 75, 79, 83, 87, 91, 95, 113, 115, 119, 145, 147, 151, 155,
    157, 159, 183, 187, 191, 218, 219, 222, 223],
   [109, 111, 123, 125, 127, 252, 253],
   [254, 255],
   [218, 219, 222, 223],
   [113, 115, 119],
   [109, 111, 123, 125, 127],
   [219, 223],
   [252, 253, 255],
   [145, 151, 157, 183, 187, 191],
   [109, 111, 123, 125, 127, 252, 253, 255],
   [145, 147, 151, 155, 157, 159, 183, 187, 191],
   [253, 255],
   [255],
   [145, 151, 157, 183, 187, 191, 219, 223],
   [145, 147, 151, 155, 157, 159, 183, 187, 191, 219, 223]]

/-- The tails of the state `s` (none for the dead state 24). -/
def tails (s : ℕ) : List ℕ := if s < 24 then TS.getD s [] else []

/-- The transitions of the 24 live states on the letters 0..7. -/
def TT : List (List ℕ) :=
  [[1, 2, 24, 24, 24, 24, 24, 3],
   [4, 5, 24, 6, 24, 24, 24, 24],
   [7, 2, 24, 24, 24, 24, 24, 8],
   [24, 24, 24, 24, 24, 24, 24, 3],
   [9, 10, 24, 11, 12, 11, 24, 24],
   [13, 14, 24, 24, 15, 24, 24, 16],
   [24, 24, 24, 24, 24, 24, 24, 6],
   [17, 24, 24, 24, 24, 24, 24, 24],
   [24, 24, 24, 24, 24, 24, 24, 8],
   [9, 18, 24, 11, 12, 11, 24, 24],
   [13, 14, 24, 24, 15, 24, 24, 16],
   [24, 24, 24, 24, 24, 24, 24, 11],
   [24, 24, 24, 24, 12, 11, 24, 24],
   [19, 24, 24, 24, 24, 24, 24, 24],
   [13, 14, 24, 24, 15, 24, 24, 20],
   [24, 24, 24, 24, 15, 21, 24, 24],
   [24, 24, 24, 24, 24, 24, 24, 16],
   [22, 8, 24, 21, 24, 24, 24, 24],
   [13, 14, 24, 24, 15, 24, 24, 16],
   [23, 20, 24, 21, 24, 24, 24, 24],
   [24, 24, 24, 24, 24, 24, 24, 20],
   [24, 24, 24, 24, 24, 24, 24, 21],
   [22, 8, 24, 21, 15, 21, 24, 24],
   [23, 20, 24, 21, 15, 21, 24, 24]]

/-- The transition of the automaton (24 is the dead state). -/
def tau (s g : ℕ) : ℕ := if s < 24 ∧ g < 8 then (TT.getD s []).getD g 24 else 24

/-- The automaton read on the word `β` of rows of the array of minima. -/
def run : (m : ℕ) → (Fin m → Row) → ℕ
  | 0, _ => 0
  | m + 1, β => tau (run m (Fin.init β)) (rc (β (Fin.last m)))

theorem run_snoc {m : ℕ} (β : Fin m → Row) (γ : Row) :
    run (m + 1) (Fin.snoc β γ) = tau (run m β) (rc γ) := by
  show tau (run m (Fin.init (Fin.snoc β γ : Fin (m + 1) → Row)))
    (rc ((Fin.snoc β γ : Fin (m + 1) → Row) (Fin.last m))) = _
  rw [Fin.init_snoc, Fin.snoc_last]

theorem chk_init_a : ∀ r < 8, fstep 0 r ≤ 3 → tc 7 r (fstep 0 r) ∈ tails 0 := by
  decide +kernel

theorem chk_init_b : ∀ t ∈ tails 0,
    t / 32 = 7 ∧ fstep 0 (t / 4 % 8) ≤ 3 ∧ t % 4 = fstep 0 (t / 4 % 8) := by
  decide +kernel

theorem chk_fwd : ∀ s < 24, ∀ t ∈ tails s, ∀ x < 8, t / 4 % 8 ≤ x → fstep (t % 4) x ≤ 3 →
    tc (t / 4 % 8) x (fstep (t % 4) x) ∈ tails (tau s (gm (t / 32) (t / 4 % 8) x)) := by
  decide +kernel

theorem chk_bwd : ∀ s < 24, ∀ g < 8, ∀ u ∈ tails (tau s g), ∃ t ∈ tails s,
    t / 4 % 8 ≤ u / 4 % 8 ∧ fstep (t % 4) (u / 4 % 8) ≤ 3 ∧
      gm (t / 32) (t / 4 % 8) (u / 4 % 8) = g ∧
      u = tc (t / 4 % 8) (u / 4 % 8) (fstep (t % 4) (u / 4 % 8)) := by
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
    have hr : t / 4 % 8 < 8 := Nat.mod_lt _ (by norm_num)
    refine ⟨fun _ => rowOf (t / 4 % 8), ?_, ?_, ?_⟩
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
    have hx : u / 4 % 8 < 8 := Nat.mod_lt _ (by norm_num)
    refine ⟨Fin.snoc A0 (rowOf (u / 4 % 8)), ?_, ?_, ?_⟩
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
def finOK (s g : ℕ) : Prop := ∃ t ∈ tails s, gm (t / 32) (t / 4 % 8) 7 = g

instance (s g : ℕ) : Decidable (finOK s g) := by
  unfold finOK
  infer_instance

theorem mem_image_iff (m : ℕ) [DecidablePred fun A : Fin (m + 1) → Fin 3 → Fin 2 => Sorted A]
    [DecidableEq (Fin (m + 1) → Fin 3 → Fin 2)] (B : Fin (m + 1) → Row) :
    B ∈ (Finset.univ.filter (fun A : Fin (m + 1) → Fin 3 → Fin 2 => Sorted A)).image
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
    show gm _ _ 7 = rc (M A (Fin.last m))
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

theorem sum_row (F : ℕ → ℕ) : ∑ γ : Row, F (rc γ) = ∑ c ∈ range 8, F c :=
  Finset.sum_nbij' rc rowOf (fun γ _ => Finset.mem_range.mpr (rc_lt γ))
    (fun _ _ => Finset.mem_univ _) (fun γ _ => rowOf_rc γ)
    (fun c hc => rc_rowOf c (Finset.mem_range.mp hc)) (fun _ _ => rfl)

theorem sum_fiber {X : Type*} [Fintype X] (r : X → ℕ) (hr : ∀ x, r x < 25) (h : ℕ → ℕ) :
    ∑ x, h (r x) = ∑ s ∈ range 25, (∑ x, if r x = s then 1 else 0) * h s := by
  simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (hr x))]

theorem chk_tau : ∀ s < 24, ∀ g < 8, (TT.getD s []).getD g 24 < 25 := by
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
def w (s : ℕ) : ℕ := ∑ c ∈ range 8, if finOK s c then 1 else 0

/-- The number of letters leading from the state `s` to the state `s'`. -/
def cnt (s s' : ℕ) : ℕ := ∑ c ∈ range 8, if tau s c = s' then 1 else 0

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
   [0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 1, 1, 0, 0, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0],
   [0, 0, 1, 1, 0, 0, 1, 1, 4, 1, 0, 5, 2, 2, 2, 3, 2, 1, 1, 1, 1, 2, 1, 0]]

def nv (m s : ℕ) : ℕ := (NV.getD m []).getD s 0

/-- The coefficients `K j` of `N (k + 4) = Sum_j C(k, j) K j`. -/
def KT : List (List ℕ) :=
  [[0, 0, 1, 1, 0, 0, 1, 1, 4, 1, 0, 5, 2, 2, 2, 3, 2, 1, 1, 1, 1, 2, 1, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 4, 1, 1, 1, 4, 1, 0, 0, 1, 3, 7, 1, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 3, 9, 0, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 5, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]]

def K (j s : ℕ) : ℕ := (KT.getD j []).getD s 0

theorem chk_nv0 : ∀ s < 24, nv 0 s = if s = 0 then 1 else 0 := by
  decide +kernel

theorem chk_nv : ∀ m < 4, ∀ s < 24, Mop (nv m) s = nv (m + 1) s := by
  decide +kernel

theorem chk_K0 : ∀ s < 24, K 0 s = nv 4 s := by
  decide +kernel

theorem chk_K : ∀ j < 5, ∀ s < 24, Mop (K j) s = K j s + K (j + 1) s := by
  decide +kernel

theorem chk_A : Aop (nv 0) = 3 ∧ Aop (nv 1) = 6 ∧ Aop (nv 2) = 14 ∧ Aop (nv 3) = 29 := by
  decide +kernel

theorem chk_AK : Aop (K 0) = 56 ∧ Aop (K 1) = 45 ∧ Aop (K 2) = 25 ∧ Aop (K 3) = 8 ∧
    Aop (K 4) = 1 := by
  decide +kernel

theorem K_five (s : ℕ) : K 5 s = 0 := rfl

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

theorem N_big (k : ℕ) : ∀ s < 24, N (k + 4) s = ∑ j ∈ range 5, k.choose j * K j s := by
  induction k with
  | zero =>
    intro s hs
    rw [Nat.zero_add, N_small 4 le_rfl s hs, ← chk_K0 s hs]
    simp [Finset.sum_range_succ]
  | succ k ih =>
    intro s hs
    rw [show k + 1 + 4 = (k + 4) + 1 by omega, N_succ _ s hs,
      Mop_congr (g := fun s => ∑ j ∈ range 5, k.choose j * K j s) ih, Mop_lin]
    rw [Finset.sum_congr rfl (fun j hj => by rw [chk_K j (Finset.mem_range.mp hj) s hs])]
    have h5 := K_five s
    have p1 : (k + 1).choose 1 = k.choose 0 + k.choose 1 := Nat.choose_succ_succ k 0
    have p2 : (k + 1).choose 2 = k.choose 1 + k.choose 2 := Nat.choose_succ_succ k 1
    have p3 : (k + 1).choose 3 = k.choose 2 + k.choose 3 := Nat.choose_succ_succ k 2
    have p4 : (k + 1).choose 4 = k.choose 3 + k.choose 4 := Nat.choose_succ_succ k 3
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, p1, p2, p3, p4,
      Nat.choose_zero_right, h5]
    ring

theorem a_small : a 1 = 3 ∧ a 2 = 6 ∧ a 3 = 14 ∧ a 4 = 29 := by
  obtain ⟨h0, h1, h2, h3⟩ := chk_A
  refine ⟨?_, ?_, ?_, ?_⟩
  · show a (0 + 1) = 3
    rw [a_succ, Aop_congr (fun s hs => N_small 0 (by norm_num) s hs), h0]
  · show a (1 + 1) = 6
    rw [a_succ, Aop_congr (fun s hs => N_small 1 (by norm_num) s hs), h1]
  · show a (2 + 1) = 14
    rw [a_succ, Aop_congr (fun s hs => N_small 2 (by norm_num) s hs), h2]
  · show a (3 + 1) = 29
    rw [a_succ, Aop_congr (fun s hs => N_small 3 (by norm_num) s hs), h3]

theorem a_big (k : ℕ) :
    a (k + 5) = 56 + 45 * k + 25 * k.choose 2 + 8 * k.choose 3 + k.choose 4 := by
  rw [show k + 5 = (k + 4) + 1 by omega, a_succ,
    Aop_congr (g := fun s => ∑ j ∈ range 5, k.choose j * K j s) (N_big k), Aop_lin]
  obtain ⟨c0, c1, c2, c3, c4⟩ := chk_AK
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c0, c1, c2, c3, c4,
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

theorem closedQ (n : ℕ) (hn : 2 ≤ n) :
    (a n : ℚ) =
      ((n : ℚ) ^ 4 + 6 * (n : ℚ) ^ 3 - 25 * (n : ℚ) ^ 2 + 138 * (n : ℚ) - 96) / 24 := by
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
    rw [choose2, choose3, choose4]
    ring

theorem recurrence (n : ℕ) (hn : 6 < n) :
    (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) -
      5 * a (n - 4) + a (n - 5) := by
  have h : ((a n : ℤ) : ℚ) = ((5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) -
      5 * a (n - 4) + a (n - 5) : ℤ) : ℚ) := by
    push_cast
    rw [closedQ n (by omega), closedQ (n - 1) (by omega), closedQ (n - 2) (by omega),
      closedQ (n - 3) (by omega), closedQ (n - 4) (by omega), closedQ (n - 5) (by omega)]
    push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega, show 5 ≤ n by omega]
    ring
  exact_mod_cast h

theorem a_mid : a 5 = 56 ∧ a 6 = 101 := by
  refine ⟨?_, ?_⟩
  · have h := a_big 0
    norm_num [Nat.choose] at h
    exact h
  · have h := a_big 1
    norm_num [Nat.choose] at h
    exact h

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
        X * (1 - 2 * X + 2 * X ^ 2) * (3 - 3 * X + 2 * X ^ 2 - X ^ 3) := by
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hF
  have key : PowerSeries.mk F * (1 - X) ^ 5 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 5 * (PowerSeries.mk F * X ^ 1) +
        C 10 * (PowerSeries.mk F * X ^ 2) - C 10 * (PowerSeries.mk F * X ^ 3) +
        C 5 * (PowerSeries.mk F * X ^ 4) - C 1 * (PowerSeries.mk F * X ^ 5) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (1 - 2 * X + 2 * X ^ 2) * (3 - 3 * X + 2 * X ^ 2 - X ^ 3) =
      C 3 * X ^ 1 - C 9 * X ^ 2 + C 14 * X ^ 3 - C 11 * X ^ 4 + C 6 * X ^ 5 - C 2 * X ^ 6 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  obtain ⟨v1, v2, v3, v4⟩ := a_small
  obtain ⟨v5, v6⟩ := a_mid
  by_cases hk : k < 7
  · interval_cases k <;> norm_num [hF, v1, v2, v3, v4, v5, v6]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 7 := ⟨k - 7, by omega⟩
    simp only [show 0 ≤ j + 7 by omega, show 1 ≤ j + 7 by omega, show 2 ≤ j + 7 by omega,
      show 3 ≤ j + 7 by omega, show 4 ≤ j + 7 by omega, show 5 ≤ j + 7 by omega,
      show j + 7 - 0 = j + 7 by omega, show j + 7 - 1 = j + 6 by omega,
      show j + 7 - 2 = j + 5 by omega, show j + 7 - 3 = j + 4 by omega,
      show j + 7 - 4 = j + 3 by omega, show j + 7 - 5 = j + 2 by omega,
      show ¬ (j + 7 = 1) by omega, show ¬ (j + 7 = 2) by omega, show ¬ (j + 7 = 3) by omega,
      show ¬ (j + 7 = 4) by omega, show ¬ (j + 7 = 5) by omega, show ¬ (j + 7 = 6) by omega,
      show ¬ (j + 7 = 0) by omega,
      show ¬ (j + 6 = 0) by omega, show ¬ (j + 5 = 0) by omega, show ¬ (j + 4 = 0) by omega,
      show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega, if_true, if_false, hF]
    rw [closedQ (j + 7) (by omega), closedQ (j + 6) (by omega), closedQ (j + 5) (by omega),
      closedQ (j + 4) (by omega), closedQ (j + 3) (by omega), closedQ (j + 2) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a219768.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
