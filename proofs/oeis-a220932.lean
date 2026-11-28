import OMAStatements.S_oeis_a220932

/-!
Proof of Barker's g.f. and closed forms for A220932 (n X 3 equals-two maps for the horizontal
and antidiagonal neighbours).

Row-local form. For an array `A` with rows `A i`, the number of neighbours of `(i, j)` equal to
`A i j` is computed explicitly (`card_nbr`): the horizontal neighbours lie in row `i`, the
up-right neighbour `(i - 1, j + 1)` in row `i - 1` and the down-left neighbour `(i + 1, j - 1)`
in row `i + 1`. The two antidiagonal pairs between consecutive rows `r` (above) and `s` (below),
namely `r 1 ~ s 0` and `r 2 ~ s 1`, are summarised by the edge code `ec r s < 4`
(bit 0: `r 1 = s 0`, bit 1: `r 2 = s 1`). So row `i` of the binary array is
`G (A i) (upc A i) (dnc A i)` (`M_eq`), where `upc A i` is the edge code with the row above
(0 if there is none) and `dnc A i` the edge code with the row below (0 if there is none); a
missing neighbour counts like an unequal one.

The automaton. For an array `A` with `m + 1` rows let `P A` be its binary array without the last
row and `tl A = 4 c + u` its tail (`c` the code of the last row, `u` its up edge code). Adding a
row `x` at the bottom appends the letter `G (last row, u, ec (last row) x)` to `P A` (`P_snoc`) and
changes the tail to `4 (code of x) + ec (last row) x` (`tl_snoc`); the last row of the binary
array of `A` is `G (last row, u, 0)` (`M_last`). The sets of tails reachable with a given `P A`
are the 8 lists `tails s` of a deterministic automaton (`tau`, state 8 is dead), the subset
construction of this nondeterministic step:
* soundness: `tl A ∈ tails (runFrom 0 m (P A))` (`sound`);
* completeness: every tail in `tails (runFrom 0 m β)` is the tail of some `A` with `P A = β`
  (`complete`).
Both are inductions on the number of rows whose steps are finite checks (`chk_init_a`,
`chk_init_b`, `chk_fwd`, `chk_bwd`, by `decide +kernel`). Hence a binary array `B` with `m + 1`
rows is a map iff its last row is `G (c, u, 0)` for a tail `4 c + u` of the state reached by its
first `m` rows (`mem_image_iff`), and `a (m + 1) = acc 0 m`, the number of words with `m + 1`
letters accepted from the start state (`a_succ`).

Counting. Splitting off the first letter gives `acc s (m + 1) = Sum_g acc (tau s g) m`
(`acc_succ`), and `acc s 0 = w s` is the number of possible last letters. Tables `alpha`, `beta`
satisfy `Sum_g alpha (tau s g) = 6 alpha s`, `Sum_g beta (tau s g) = - beta s` and
`7 w s = 6 alpha s - beta s` (finite checks), so by induction
`7 acc s m = alpha s 6^(m+1) + beta s (-1)^(m+1)` (`closed`). With `alpha 0 = 3`, `beta 0 = 4`:
`7 a(n) = 3 * 6^n + 4 * (-1)^n` for `n ≥ 1` (`closedQ`), which gives the formulas for even and odd
`n` (as `3 * 6^n = 2^n * 3^(n+1)`) and the generating function (`a(1) = 2`, `a(2) = 16`, and
`a(k) - 5 a(k-1) - 6 a(k-2) = 0` for `k ≥ 3`).
-/

namespace OMA.Helpers

open OMA.S_oeis_a220932 Finset

abbrev Row := Fin 3 → Fin 3
abbrev BRow := Fin 3 → Bool

/-- `1` if `p` holds, `0` otherwise. -/
def eqI (p : Prop) [Decidable p] : ℕ := if p then 1 else 0

theorem eqI_comm {α : Type*} [DecidableEq α] (x y : α) : eqI (x = y) = eqI (y = x) := by
  unfold eqI
  by_cases h : x = y
  · subst h
    rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- The code `r 0 + 3 r 1 + 9 r 2 < 27` of a row. -/
def rc (r : Row) : ℕ := (r 0).val + 3 * (r 1).val + 9 * (r 2).val

/-- The row with code `c < 27`. -/
def rowOf (c : ℕ) : Row := fun j => ⟨c / 3 ^ j.val % 3, Nat.mod_lt _ (by norm_num)⟩

theorem rc_lt (r : Row) : rc r < 27 := by
  unfold rc
  have := (r 0).isLt
  have := (r 1).isLt
  have := (r 2).isLt
  omega

theorem rowOf_rc (r : Row) : rowOf (rc r) = r := by
  funext j
  apply Fin.ext
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  have h2 := (r 2).isLt
  fin_cases j <;> simp [rowOf, rc] <;> omega

theorem rc_rowOf (c : ℕ) (hc : c < 27) : rc (rowOf c) = c := by
  unfold rc rowOf
  simp
  omega

/-- The code `b 0 + 2 b 1 + 4 b 2 < 8` of a binary row. -/
def bc (b : BRow) : ℕ := (b 0).toNat + 2 * (b 1).toNat + 4 * (b 2).toNat

/-- The binary row with code `g < 8`. -/
def browOf (g : ℕ) : BRow := fun j => decide (g / 2 ^ j.val % 2 = 1)

theorem browOf_bc : ∀ b : BRow, browOf (bc b) = b := by
  decide +kernel

theorem bc_browOf : ∀ g < 8, bc (browOf g) = g := by
  decide +kernel

theorem toNat_le_one (x : Bool) : x.toNat ≤ 1 := by
  cases x <;> decide

theorem bc_lt (b : BRow) : bc b < 8 := by
  unfold bc
  have := toNat_le_one (b 0)
  have := toNat_le_one (b 1)
  have := toNat_le_one (b 2)
  omega

theorem bc_inj {b b' : BRow} (h : bc b = bc b') : b = b' := by
  rw [← browOf_bc b, ← browOf_bc b', h]

/-- Edge code between an upper row `r` and the row `s` below it. -/
def ec (r s : Row) : ℕ := eqI (r 1 = s 0) + 2 * eqI (r 2 = s 1)

theorem ec_mod (r s : Row) : ec r s % 2 = eqI (r 1 = s 0) := by
  unfold ec eqI
  split_ifs <;> norm_num

theorem ec_div (r s : Row) : ec r s / 2 = eqI (r 2 = s 1) := by
  unfold ec eqI
  split_ifs <;> norm_num

theorem ec_lt (r s : Row) : ec r s < 4 := by
  unfold ec eqI
  split_ifs <;> norm_num

/-- The numbers of equal neighbours in a row `c`, given the up and down edge codes. -/
def nc (c : Row) (u d : ℕ) (j : Fin 3) : ℕ :=
  if j.val = 0 then eqI (c 1 = c 0) + u % 2
  else if j.val = 1 then eqI (c 0 = c 1) + eqI (c 2 = c 1) + u / 2 + d % 2
  else eqI (c 1 = c 2) + d / 2

/-- The row of the binary array from the row `c` and its edge codes. -/
def G (c : Row) (u d : ℕ) : BRow := fun j => decide (nc c u d j = 2)

/-- The edge code of row `i` with the row above it (0 for the first row). -/
def upc {n : ℕ} (A : Fin n → Row) (i : Fin n) : ℕ :=
  if h : i.val = 0 then 0 else ec (A ⟨i.val - 1, by omega⟩) (A i)

/-- The edge code of row `i` with the row below it (0 for the last row). -/
def dnc {n : ℕ} (A : Fin n → Row) (i : Fin n) : ℕ :=
  if h : i.val + 1 < n then ec (A i) (A ⟨i.val + 1, h⟩) else 0

/-- Equal neighbours of `(i, j)` in a row `r` with row offset 0 (`c` is row `i`). -/
def sX (j : Fin 3) (r c : Row) : ℕ :=
  if j.val = 0 then eqI (r 1 = c 0)
  else if j.val = 1 then eqI (r 0 = c 1) + eqI (r 2 = c 1)
  else eqI (r 1 = c 2)

/-- Equal neighbours of `(i, j)` in a row `r` with row offset -1 (`c` is row `i`). -/
def sY (j : Fin 3) (r c : Row) : ℕ :=
  if j.val = 0 then eqI (r 1 = c 0)
  else if j.val = 1 then eqI (r 2 = c 1)
  else 0

/-- Equal neighbours of `(i, j)` in a row `r` with row offset 1 (`c` is row `i`). -/
def sZ (j : Fin 3) (r c : Row) : ℕ :=
  if j.val = 0 then 0
  else if j.val = 1 then eqI (r 0 = c 1)
  else eqI (r 1 = c 2)

theorem row_split {n : ℕ} (A : Fin n → Row) (i x : Fin n) (j : Fin 3)
    [DecidablePred fun q : Fin n × Fin 3 => IsNbr (i, j) q ∧ A q.1 q.2 = A i j] :
    ((if IsNbr (i, j) (x, 0) ∧ A x 0 = A i j then 1 else 0) +
      (if IsNbr (i, j) (x, 1) ∧ A x 1 = A i j then 1 else 0) +
      (if IsNbr (i, j) (x, 2) ∧ A x 2 = A i j then 1 else 0) : ℕ) =
    (if (x : ℤ) - i = 0 then sX j (A x) (A i) else 0) +
      (if (x : ℤ) - i = -1 then sY j (A x) (A i) else 0) +
      (if (x : ℤ) - i = 1 then sZ j (A x) (A i) else 0) := by
  obtain h | h | h | h : (x : ℤ) - i = 0 ∨ (x : ℤ) - i = -1 ∨ (x : ℤ) - i = 1 ∨
      ((x : ℤ) - i ≠ 0 ∧ (x : ℤ) - i ≠ -1 ∧ (x : ℤ) - i ≠ 1) := by omega
  all_goals fin_cases j
  all_goals simp [IsNbr, h, sX, sY, sZ, eqI]

theorem sum_d0 {n : ℕ} (i : Fin n) (f : Fin n → ℕ) :
    ∑ x : Fin n, (if (x : ℤ) - i = 0 then f x else 0) = f i := by
  rw [Fintype.sum_eq_single i]
  · simp
  · intro x hx
    rw [if_neg]
    intro h
    exact hx (Fin.ext (by omega))

theorem sum_dm1 {n : ℕ} (i : Fin n) (f : Fin n → ℕ) :
    ∑ x : Fin n, (if (x : ℤ) - i = -1 then f x else 0) =
      if h : i.val = 0 then 0 else f ⟨i.val - 1, by omega⟩ := by
  split_ifs with h0
  · apply Finset.sum_eq_zero
    intro x _
    rw [if_neg]
    omega
  · rw [Fintype.sum_eq_single ⟨i.val - 1, by omega⟩]
    · rw [if_pos]
      simp only
      omega
    · intro x hx
      rw [if_neg]
      intro h
      exact hx (Fin.ext (by simp only; omega))

theorem sum_dp1 {n : ℕ} (i : Fin n) (f : Fin n → ℕ) :
    ∑ x : Fin n, (if (x : ℤ) - i = 1 then f x else 0) =
      if h : i.val + 1 < n then f ⟨i.val + 1, h⟩ else 0 := by
  split_ifs with h1
  · rw [Fintype.sum_eq_single ⟨i.val + 1, h1⟩]
    · rw [if_pos]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    · intro x hx
      rw [if_neg]
      intro h
      exact hx (Fin.ext (by simp only; omega))
  · apply Finset.sum_eq_zero
    intro x _
    rw [if_neg]
    have := x.isLt
    omega

theorem card_nbr {n : ℕ} (A : Fin n → Row) (i : Fin n) (j : Fin 3)
    [DecidablePred fun q : Fin n × Fin 3 => IsNbr (i, j) q ∧ A q.1 q.2 = A i j] :
    (univ.filter (fun q : Fin n × Fin 3 => IsNbr (i, j) q ∧ A q.1 q.2 = A i j)).card =
      nc (A i) (upc A i) (dnc A i) j := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_three]
  rw [Finset.sum_congr rfl (fun x _ => row_split A i x j)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_d0, sum_dm1, sum_dp1]
  unfold upc dnc nc
  by_cases h1 : i.val + 1 < n <;> simp only [h1, ↓reduceDIte] <;>
    by_cases h0 : i.val = 0 <;> fin_cases j <;> simp [h0, sX, sY, sZ, ec_mod, ec_div, eqI_comm]


/-- The binary array of `A`. -/
noncomputable def M {n : ℕ} (A : Fin n → Row) : Fin n → BRow := fun i j => eqTwo A (i, j)

theorem M_eq {n : ℕ} (A : Fin n → Row) (i : Fin n) : M A i = G (A i) (upc A i) (dnc A i) := by
  funext j
  show eqTwo A (i, j) = decide (nc (A i) (upc A i) (dnc A i) j = 2)
  unfold eqTwo
  simp only [card_nbr]

theorem snoc_lt {m : ℕ} (A : Fin (m + 1) → Row) (x : Row) (k : ℕ) (hk : k < m + 1) :
    (Fin.snoc A x : Fin (m + 2) → Row) ⟨k, by omega⟩ = A ⟨k, hk⟩ :=
  Fin.snoc_castSucc (α := fun _ => Row) (i := ⟨k, hk⟩) (p := A) (x := x)

theorem snoc_at_last {m : ℕ} (A : Fin (m + 1) → Row) (x : Row) :
    (Fin.snoc A x : Fin (m + 2) → Row) ⟨m + 1, by omega⟩ = x :=
  Fin.snoc_last (α := fun _ => Row) (p := A) (x := x)

theorem upc_snoc_cast {m : ℕ} (A : Fin (m + 1) → Row) (x : Row) (i : Fin (m + 1)) :
    upc (Fin.snoc A x : Fin (m + 2) → Row) i.castSucc = upc A i := by
  have hi := i.isLt
  unfold upc
  simp only [Fin.val_castSucc]
  split_ifs with h
  · rfl
  · rw [snoc_lt A x _ (by omega), Fin.snoc_castSucc]

theorem upc_snoc_last {m : ℕ} (A : Fin (m + 1) → Row) (x : Row) :
    upc (Fin.snoc A x : Fin (m + 2) → Row) (Fin.last (m + 1)) = ec (A (Fin.last m)) x := by
  unfold upc
  rw [dif_neg (by simp), Fin.snoc_last]
  congr 1
  simp only [Fin.val_last, Nat.add_sub_cancel]
  exact snoc_lt A x m (by omega)

theorem dnc_snoc_cast {m : ℕ} (A : Fin (m + 1) → Row) (x : Row) (i : Fin m) :
    dnc (Fin.snoc A x : Fin (m + 2) → Row) i.castSucc.castSucc = dnc A i.castSucc := by
  have hi := i.isLt
  unfold dnc
  simp only [Fin.val_castSucc]
  rw [dif_pos (by omega), dif_pos (by omega), Fin.snoc_castSucc, snoc_lt A x _ (by omega)]

theorem dnc_snoc_last {m : ℕ} (A : Fin (m + 1) → Row) (x : Row) :
    dnc (Fin.snoc A x : Fin (m + 2) → Row) (Fin.last m).castSucc = ec (A (Fin.last m)) x := by
  unfold dnc
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [dif_pos (by omega), Fin.snoc_castSucc, snoc_at_last]

theorem dnc_last {m : ℕ} (A : Fin (m + 1) → Row) : dnc A (Fin.last m) = 0 := by
  unfold dnc
  rw [dif_neg (by simp)]

theorem upc_lt {n : ℕ} (A : Fin n → Row) (i : Fin n) : upc A i < 4 := by
  unfold upc
  split_ifs
  · norm_num
  · exact ec_lt _ _

/-- The binary array of `A` without its last row. -/
noncomputable def P {m : ℕ} (A : Fin (m + 1) → Row) : Fin m → BRow := Fin.init (M A)

theorem P_snoc {m : ℕ} (A : Fin (m + 1) → Row) (x : Row) :
    P (Fin.snoc A x : Fin (m + 2) → Row) =
      Fin.snoc (P A) (G (A (Fin.last m)) (upc A (Fin.last m)) (ec (A (Fin.last m)) x)) := by
  funext i
  unfold P
  cases i using Fin.lastCases with
  | last =>
    rw [Fin.snoc_last]
    show M (Fin.snoc A x : Fin (m + 2) → Row) (Fin.last m).castSucc = _
    rw [M_eq, upc_snoc_cast, dnc_snoc_last, Fin.snoc_castSucc]
  | cast i =>
    rw [Fin.snoc_castSucc]
    show M (Fin.snoc A x : Fin (m + 2) → Row) i.castSucc.castSucc = M A i.castSucc
    rw [M_eq, M_eq, upc_snoc_cast, dnc_snoc_cast, Fin.snoc_castSucc]

theorem M_last {m : ℕ} (A : Fin (m + 1) → Row) :
    M A (Fin.last m) = G (A (Fin.last m)) (upc A (Fin.last m)) 0 := by
  rw [M_eq, dnc_last]

/-- A tail: the code of the last row and of its up edge. -/
def tc (c u : ℕ) : ℕ := 4 * c + u

theorem tc_div (c u : ℕ) (hu : u < 4) : tc c u / 4 = c := by
  unfold tc
  omega

theorem tc_mod (c u : ℕ) (hu : u < 4) : tc c u % 4 = u := by
  unfold tc
  omega

/-- The tail of an array with at least one row. -/
noncomputable def tl {m : ℕ} (A : Fin (m + 1) → Row) : ℕ :=
  tc (rc (A (Fin.last m))) (upc A (Fin.last m))

theorem tl_snoc {m : ℕ} (A : Fin (m + 1) → Row) (x : Row) :
    tl (Fin.snoc A x : Fin (m + 2) → Row) = tc (rc x) (ec (A (Fin.last m)) x) := by
  unfold tl
  rw [upc_snoc_last, Fin.snoc_last]

theorem tl_one (A : Fin 1 → Row) : tl A = tc (rc (A 0)) 0 := by
  unfold tl upc
  rfl


/-! ### The automaton -/

/-- The tails of the 8 live states (a tail `4 c + u`: last row code `c`, up edge code `u`). -/
def TS : List (List ℕ) :=
  [[0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 68, 72, 76, 80, 84, 88,
    92, 96, 100, 104],
   [0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26,
    27, 28, 29, 30, 31, 32, 33, 34, 36, 37, 38, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50,
    51, 52, 53, 54, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 72, 73, 74,
    76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 92, 93, 94, 95, 96, 97, 98,
    99, 100, 101, 102, 103, 104, 105, 106],
   [0, 1, 4, 5, 7, 8, 9, 11, 12, 13, 15, 16, 17, 20, 21, 23, 24, 25, 27, 28, 29, 31, 32, 33,
    36, 37, 40, 41, 43, 44, 45, 47, 48, 49, 51, 52, 53, 56, 57, 59, 60, 61, 63, 64, 65, 67,
    68, 69, 72, 73, 76, 77, 79, 80, 81, 83, 84, 85, 87, 88, 89, 92, 93, 95, 96, 97, 99, 100,
    101, 103, 104, 105],
   [3, 6, 10, 14, 19, 22, 26, 30, 35, 39, 42, 46, 50, 55, 58, 62, 66, 71, 75, 78, 82, 86, 91,
    94, 98, 102, 107],
   [0, 2, 4, 5, 6, 8, 9, 10, 12, 13, 14, 16, 18, 20, 21, 22, 24, 25, 26, 28, 29, 30, 32, 34,
    36, 38, 40, 41, 42, 44, 45, 46, 48, 49, 50, 52, 54, 56, 57, 58, 60, 61, 62, 64, 65, 66,
    68, 70, 72, 74, 76, 77, 78, 80, 81, 82, 84, 85, 86, 88, 90, 92, 93, 94, 96, 97, 98, 100,
    101, 102, 104, 106],
   [3, 19, 35, 39, 55, 71, 75, 91, 107],
   [6, 10, 14, 22, 26, 30, 42, 46, 50, 58, 62, 66, 78, 82, 86, 94, 98, 102],
   [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46,
    48, 50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90,
    92, 94, 96, 98, 100, 102, 104, 106]]

/-- The tails of the state `s` (none for the dead state 8). -/
def tails (s : ℕ) : List ℕ := if s < 8 then TS.getD s [] else []

/-- The transitions of the 8 live states on the letters 0..7. -/
def TT : List (List ℕ) :=
  [[1, 8, 2, 8, 3, 8, 3, 8],
   [1, 4, 1, 2, 3, 5, 3, 6],
   [1, 4, 2, 2, 3, 5, 3, 6],
   [4, 2, 2, 7, 5, 3, 6, 8],
   [1, 8, 1, 8, 3, 8, 3, 8],
   [8, 2, 8, 7, 8, 3, 8, 8],
   [4, 8, 2, 8, 5, 8, 6, 8],
   [1, 8, 1, 8, 3, 8, 3, 8]]

/-- The transition of the automaton (8 is the dead state). -/
def tau (s g : ℕ) : ℕ := if s < 8 ∧ g < 8 then (TT.getD s []).getD g 8 else 8

/-- The edge code on row codes. -/
def ecm (c x : ℕ) : ℕ := ec (rowOf c) (rowOf x)

/-- The binary row code from a row code and two edge codes. -/
def gb (c u d : ℕ) : ℕ := bc (G (rowOf c) u d)

theorem ec_code (r s : Row) : ec r s = ecm (rc r) (rc s) := by
  unfold ecm
  rw [rowOf_rc, rowOf_rc]

theorem bc_G (r : Row) (u d : ℕ) : bc (G r u d) = gb (rc r) u d := by
  unfold gb
  rw [rowOf_rc]

/-- The automaton started in the state `s`, read on the word `β` of binary rows. -/
def runFrom (s : ℕ) : (m : ℕ) → (Fin m → BRow) → ℕ
  | 0, _ => s
  | m + 1, β => tau (runFrom s m (Fin.init β)) (bc (β (Fin.last m)))

theorem runFrom_snoc (s : ℕ) {m : ℕ} (β : Fin m → BRow) (γ : BRow) :
    runFrom s (m + 1) (Fin.snoc β γ) = tau (runFrom s m β) (bc γ) := by
  show tau (runFrom s m (Fin.init (Fin.snoc β γ : Fin (m + 1) → BRow)))
    (bc ((Fin.snoc β γ : Fin (m + 1) → BRow) (Fin.last m))) = _
  rw [Fin.init_snoc, Fin.snoc_last]

theorem chk_init_a : ∀ c < 27, tc c 0 ∈ tails 0 := by
  decide +kernel

theorem chk_init_b : ∀ t ∈ tails 0, t % 4 = 0 ∧ t / 4 < 27 := by
  decide +kernel

theorem chk_fwd : ∀ s < 8, ∀ t ∈ tails s, ∀ x < 27,
    tc x (ecm (t / 4) x) ∈ tails (tau s (gb (t / 4) (t % 4) (ecm (t / 4) x))) := by
  decide +kernel

theorem chk_bwd : ∀ s < 8, ∀ g < 8, ∀ u ∈ tails (tau s g), u / 4 < 27 ∧
    ∃ t ∈ tails s, gb (t / 4) (t % 4) (ecm (t / 4) (u / 4)) = g ∧
      u % 4 = ecm (t / 4) (u / 4) := by
  decide +kernel

theorem lt8_of_mem {s t : ℕ} (h : t ∈ tails s) : s < 8 := by
  by_contra hs
  unfold tails at h
  rw [if_neg hs] at h
  exact absurd h List.not_mem_nil

theorem sound : ∀ (m : ℕ) (A : Fin (m + 1) → Row), tl A ∈ tails (runFrom 0 m (P A)) := by
  intro m
  induction m with
  | zero =>
    intro A
    rw [tl_one]
    exact chk_init_a (rc (A 0)) (rc_lt _)
  | succ m ih =>
    intro A
    obtain ⟨A0, x, rfl⟩ : ∃ (A0 : Fin (m + 1) → Row) (x : Row), A = Fin.snoc A0 x :=
      ⟨Fin.init A, A (Fin.last _), (Fin.snoc_init_self A).symm⟩
    have ih' := ih A0
    rw [P_snoc, runFrom_snoc, tl_snoc, bc_G, ec_code]
    have key := chk_fwd _ (lt8_of_mem ih') (tl A0) ih' (rc x) (rc_lt x)
    unfold tl at key
    rw [tc_div _ _ (upc_lt _ _), tc_mod _ _ (upc_lt _ _)] at key
    exact key

theorem complete : ∀ (m : ℕ) (β : Fin m → BRow) (t : ℕ), t ∈ tails (runFrom 0 m β) →
    ∃ A : Fin (m + 1) → Row, P A = β ∧ tl A = t := by
  intro m
  induction m with
  | zero =>
    intro β t ht
    obtain ⟨h1, h2⟩ := chk_init_b t ht
    refine ⟨fun _ => rowOf (t / 4), ?_, ?_⟩
    · funext i
      exact Fin.elim0 i
    · rw [tl_one, rc_rowOf _ h2]
      unfold tc
      omega
  | succ m ih =>
    intro β u hu
    obtain ⟨β0, γ, rfl⟩ : ∃ (β0 : Fin m → BRow) (γ : BRow), β = Fin.snoc β0 γ :=
      ⟨Fin.init β, β (Fin.last _), (Fin.snoc_init_self β).symm⟩
    rw [runFrom_snoc] at hu
    have hs : runFrom 0 m β0 < 8 := by
      by_contra h
      have : tau (runFrom 0 m β0) (bc γ) = 8 := by
        unfold tau
        rw [if_neg (by omega)]
      rw [this] at hu
      exact absurd (lt8_of_mem hu) (lt_irrefl _)
    obtain ⟨hx, t, ht, c1, c2⟩ := chk_bwd _ hs (bc γ) (bc_lt γ) u hu
    obtain ⟨A0, hP, htl⟩ := ih β0 t ht
    have d1 : t / 4 = rc (A0 (Fin.last m)) := by
      rw [← htl]
      exact tc_div _ _ (upc_lt _ _)
    have d2 : t % 4 = upc A0 (Fin.last m) := by
      rw [← htl]
      exact tc_mod _ _ (upc_lt _ _)
    refine ⟨Fin.snoc A0 (rowOf (u / 4)), ?_, ?_⟩
    · rw [P_snoc, hP]
      congr 1
      apply bc_inj
      rw [bc_G, ec_code, rc_rowOf _ hx, ← d1, ← d2]
      exact c1
    · rw [tl_snoc, ec_code, rc_rowOf _ hx, ← d1, ← c2]
      unfold tc
      omega

/-- The letter `g` (a binary row code) can end a word that leads to the state `s`. -/
def finOK (s g : ℕ) : Prop := ∃ t ∈ tails s, gb (t / 4) (t % 4) 0 = g

instance (s g : ℕ) : Decidable (finOK s g) := by
  unfold finOK
  infer_instance

theorem mem_image_iff (m : ℕ) [DecidableEq (Fin (m + 1) → Fin 3 → Bool)]
    (B : Fin (m + 1) → BRow) :
    B ∈ Finset.univ.image
        (fun A : Fin (m + 1) → Fin 3 → Fin 3 => fun i j => eqTwo A (i, j)) ↔
      finOK (runFrom 0 m (Fin.init B)) (bc (B (Fin.last m))) := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨A, -, rfl⟩
    refine ⟨tl A, sound m A, ?_⟩
    unfold tl
    rw [tc_div _ _ (upc_lt _ _), tc_mod _ _ (upc_lt _ _)]
    show gb _ _ 0 = bc (M A (Fin.last m))
    rw [M_last, bc_G]
  · rintro ⟨t, ht, hg⟩
    obtain ⟨A, hP, htl⟩ := complete m (Fin.init B) t ht
    refine ⟨A, Finset.mem_univ _, ?_⟩
    show M A = B
    have d1 : t / 4 = rc (A (Fin.last m)) := by
      rw [← htl]
      exact tc_div _ _ (upc_lt _ _)
    have d2 : t % 4 = upc A (Fin.last m) := by
      rw [← htl]
      exact tc_mod _ _ (upc_lt _ _)
    rw [← Fin.snoc_init_self (M A), ← Fin.snoc_init_self B]
    have hP' : Fin.init (M A) = Fin.init B := hP
    rw [hP']
    congr 1
    apply bc_inj
    rw [M_last, bc_G, ← d1, ← d2]
    exact hg


/-! ### Counting -/

theorem card_eq_sum {α : Type*} [Fintype α] [DecidableEq α] (I : Finset α) :
    I.card = ∑ x, if x ∈ I then 1 else 0 := by
  rw [← Finset.card_filter, Finset.filter_univ_mem]

theorem sum_brow (F : ℕ → ℕ) : ∑ γ : BRow, F (bc γ) = ∑ g ∈ range 8, F g :=
  Finset.sum_nbij' bc browOf (fun γ _ => Finset.mem_range.mpr (bc_lt γ))
    (fun _ _ => Finset.mem_univ _) (fun γ _ => browOf_bc γ)
    (fun g hg => bc_browOf g (Finset.mem_range.mp hg)) (fun _ _ => rfl)

theorem init_cons_eq {m : ℕ} (γ : BRow) (B : Fin (m + 1) → BRow) :
    Fin.init (Fin.cons γ B : Fin (m + 2) → BRow) = Fin.cons γ (Fin.init B) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · rfl
  · simp only [Fin.init, Fin.cons_succ]
    rw [← Fin.succ_castSucc, Fin.cons_succ]

theorem runFrom_cons : ∀ (m s : ℕ) (γ : BRow) (β : Fin m → BRow),
    runFrom s (m + 1) (Fin.cons γ β) = runFrom (tau s (bc γ)) m β := by
  intro m
  induction m with
  | zero =>
    intro s γ β
    rfl
  | succ m ih =>
    intro s γ β
    show tau (runFrom s (m + 1) (Fin.init (Fin.cons γ β : Fin (m + 2) → BRow)))
      (bc ((Fin.cons γ β : Fin (m + 2) → BRow) (Fin.last (m + 1)))) = _
    rw [init_cons_eq, ih, Fin.cons_last]
    rfl

/-- The number of words with `m + 1` letters accepted from the state `s`. -/
def acc (s m : ℕ) : ℕ :=
  ∑ B : Fin (m + 1) → BRow,
    if finOK (runFrom s m (Fin.init B)) (bc (B (Fin.last m))) then 1 else 0

/-- The number of letters that can end a word leading to the state `s`. -/
def w (s : ℕ) : ℕ := ∑ g ∈ range 8, if finOK s g then 1 else 0

theorem acc_zero (s : ℕ) : acc s 0 = w s := by
  unfold acc w
  rw [← sum_brow (fun g => if finOK s g then 1 else 0)]
  exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) BRow) _ _ (fun B => rfl)

theorem acc_succ (s m : ℕ) : acc s (m + 1) = ∑ g ∈ range 8, acc (tau s g) m := by
  unfold acc
  rw [← sum_brow (fun g => ∑ B : Fin (m + 1) → BRow,
    if finOK (runFrom (tau s g) m (Fin.init B)) (bc (B (Fin.last m))) then 1 else 0)]
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ => BRow))
    (fun p => if finOK (runFrom s (m + 1) (Fin.init (Fin.cons p.1 p.2 : Fin (m + 2) → BRow)))
      (bc ((Fin.cons p.1 p.2 : Fin (m + 2) → BRow) (Fin.last (m + 1)))) then 1 else 0) _
    (fun p => rfl)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun γ _ => Finset.sum_congr rfl (fun B _ => ?_))
  simp only
  rw [init_cons_eq, runFrom_cons, Fin.cons_last]

/-- The table of `alpha`. -/
def AL : List ℤ := [3, 5, 5, 4, 3, 2, 2, 3, 0]

/-- The table of `beta`. -/
def BE : List ℤ := [4, 2, 2, -4, 4, -2, -2, 4, 0]

/-- The coefficient of `6 ^ (m + 1)` in `7 acc s m`. -/
def alpha (s : ℕ) : ℤ := AL.getD s 0

/-- The coefficient of `(-1) ^ (m + 1)` in `7 acc s m`. -/
def beta (s : ℕ) : ℤ := BE.getD s 0

theorem chk_rec : ∀ s < 9, (∑ g ∈ range 8, alpha (tau s g)) = 6 * alpha s ∧
    (∑ g ∈ range 8, beta (tau s g)) = - beta s := by
  decide +kernel

theorem chk_w : ∀ s < 9, 7 * (w s : ℤ) = 6 * alpha s - beta s := by
  decide +kernel

theorem chk_tau : ∀ s < 8, ∀ g < 8, (TT.getD s []).getD g 8 < 9 := by
  decide +kernel

theorem tau_lt (s g : ℕ) : tau s g < 9 := by
  unfold tau
  split_ifs with h
  · exact chk_tau s h.1 g h.2
  · norm_num

theorem closed : ∀ (m s : ℕ), s < 9 →
    7 * (acc s m : ℤ) = alpha s * 6 ^ (m + 1) + beta s * (-1) ^ (m + 1) := by
  intro m
  induction m with
  | zero =>
    intro s hs
    rw [acc_zero, chk_w s hs]
    ring
  | succ m ih =>
    intro s hs
    rw [acc_succ]
    push_cast
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun g _ => ih (tau s g) (tau_lt s g)),
      Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, (chk_rec s hs).1,
      (chk_rec s hs).2]
    ring

theorem a_succ (m : ℕ) : a (m + 1) = acc 0 m := by
  classical
  unfold a acc
  rw [card_eq_sum]
  exact Finset.sum_congr rfl fun B _ => if_congr (mem_image_iff m B) rfl rfl

theorem closedQ (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = (3 * 6 ^ n + 4 * (-1) ^ n) / 7 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := closed m 0 (by norm_num)
  rw [← a_succ] at h
  have h' : (7 * (a (m + 1) : ℚ)) = 3 * 6 ^ (m + 1) + 4 * (-1) ^ (m + 1) := by
    have h2 : ((7 * (a (m + 1) : ℤ) : ℤ) : ℚ) =
        ((alpha 0 * 6 ^ (m + 1) + beta 0 * (-1) ^ (m + 1) : ℤ) : ℚ) := by
      rw [h]
    push_cast at h2
    rw [h2, show alpha 0 = 3 from rfl, show beta 0 = 4 from rfl]
    push_cast
    ring
  linarith

theorem even_case (n : ℕ) (hn : 1 ≤ n) (he : Even n) :
    (a n : ℚ) = (2 ^ n * 3 ^ (n + 1) + 4) / 7 := by
  rw [closedQ n hn, he.neg_one_pow]
  have h6 : (6 : ℚ) ^ n = 2 ^ n * 3 ^ n := by
    rw [← mul_pow]
    norm_num
  rw [h6]
  ring

theorem odd_case (n : ℕ) (hn : 1 ≤ n) (ho : Odd n) :
    (a n : ℚ) = (2 ^ n * 3 ^ (n + 1) - 4) / 7 := by
  rw [closedQ n hn, ho.neg_one_pow]
  have h6 : (6 : ℚ) ^ n = 2 ^ n * 3 ^ n := by
    rw [← mul_pow]
    norm_num
  rw [h6]
  ring

open PowerSeries in
theorem gf_generic (f : ℕ → ℚ)
    (hf : ∀ n, 1 ≤ n → f n = (3 * 6 ^ n + 4 * (-1) ^ n) / 7) :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else f n) * ((1 + X) * (1 - 6 * X)) =
        2 * X * (1 + 3 * X) := by
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else f n with hF
  have key : PowerSeries.mk F * ((1 + X) * (1 - 6 * X)) =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 5 * (PowerSeries.mk F * X ^ 1) -
        C 6 * (PowerSeries.mk F * X ^ 2) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (2 * X * (1 + 3 * X) : ℚ⟦X⟧) = C 2 * X ^ 1 + C 6 * X ^ 2 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  have v1 := hf 1 le_rfl
  have v2 := hf 2 (by norm_num)
  by_cases hk : k < 3
  · interval_cases k <;> norm_num [hF, v1, v2]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    simp only [show 0 ≤ j + 3 by omega, show 1 ≤ j + 3 by omega, show 2 ≤ j + 3 by omega,
      show j + 3 - 0 = j + 3 by omega, show j + 3 - 1 = j + 2 by omega,
      show j + 3 - 2 = j + 1 by omega, show ¬ (j + 3 = 1) by omega, show ¬ (j + 3 = 2) by omega,
      show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega, show ¬ (j + 1 = 0) by omega,
      if_true, if_false, hF]
    rw [hf (j + 3) (by omega), hf (j + 2) (by omega), hf (j + 1) (by omega)]
    ring

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 + X) * (1 - 6 * X)) =
        2 * X * (1 + 3 * X) :=
  gf_generic (fun n => (a n : ℚ)) closedQ

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a220932.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.even_case, OMA.Helpers.odd_case⟩
