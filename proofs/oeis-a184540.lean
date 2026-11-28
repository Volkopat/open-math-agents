import OMAStatements.S_oeis_a184540

/-!
Proof of Barker's conjectures for A184540 ((n+2) X 3 binary arrays all of whose 3 X 3 subblocks
have their rows and columns in lexicographically nondecreasing order).

With 3 columns, the 3 X 3 subblocks are exactly the blocks of 3 consecutive rows, so an array is
good iff every three consecutive rows `x, y, z` satisfy a condition `V x y z` (`good_iff`).
Removing the first row (`chain_cons`) gives a transfer recursion: if `T m x y` counts the ways to
continue the rows `x, y` by `m` more rows, then `T 0 x y = 1`,
`T (m + 1) x y = Sum_{z with V x y z} T m y z`, and `a n = Sum_{x, y} T n x y`.

Rows are coded by the numbers 0, ..., 7 (bits read left to right, most significant first). On
codes, `V` becomes a Boolean test `Vt` (rows, and columns, compare as their codes do), checked
once against `V` on all 512 triples of rows. `G` is the same recursion on codes.

Group the 64 pairs of codes into types (`typ`):
  type 1: (0, 0); type 2: (0, 1), (1, 1); type 3: (0, 3), (1, 3), (3, 3);
  type 4: (0, 7), (1, 7), (3, 7), (7, 7); type 0: all other pairs.
For `n ≥ 2`, six times the number of continuations by `n` rows is `P (typ u v) n`, where
  `P 1 n = n^3 + 30 n^2 + 17 n - 78`, `P 2 n = 3 n^2 + 57 n - 12`, `P 3 n = 6 n + 54`,
  `P 4 n = 6`, `P 0 n = 0`.
This is proved by induction from `n = 2` (a finite check). A pair of type `t ≥ 1` has exactly one
continuation of each type `u ≥ t`, the others being of type 0, and `P t (n + 1)` is the sum of
the `P u n` for `u ≥ t`; in the proof this is a finite check of four identities between
coefficients for each pair (`step_facts`). Summing over the 64 pairs gives
`6 a(n) = n^3 + 36 n^2 + 149 n + 84` for `n ≥ 2`, and also for `n = 1` since `a 1 = 45`. The
recurrence and the generating function follow by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a184540 Finset

/-- A row of the array. -/
abbrev Row := Fin 3 → Fin 2

instance decLexLE (x y : Row) : Decidable (LexLE x y) := by
  unfold LexLE
  infer_instance

/-- The condition of the statement on one 3 X 3 block. -/
def BlockOK (B : Fin 3 → Fin 3 → Fin 2) : Prop :=
  LexLE (B 0) (B 1) ∧ LexLE (B 1) (B 2) ∧
    LexLE (fun r => B r 0) (fun r => B r 1) ∧ LexLE (fun r => B r 1) (fun r => B r 2)

/-- The condition on three consecutive rows `x, y, z`. -/
def V (x y z : Row) : Prop := BlockOK ![x, y, z]

instance decV (x y z : Row) : Decidable (V x y z) := by
  unfold V BlockOK
  infer_instance

/-- Every three consecutive rows of `A` satisfy `V`. -/
def Chain {m : ℕ} (A : Fin m → Row) : Prop :=
  ∀ (i : ℕ) (h : i + 2 < m), V (A ⟨i, by omega⟩) (A ⟨i + 1, by omega⟩) (A ⟨i + 2, h⟩)

/-- With 3 columns there is a single column of 3 X 3 blocks. -/
theorem good_iff {m : ℕ} (A : Fin m → Row) : Good A ↔ Chain A := by
  have key : ∀ (i : ℕ) (hi : i + 2 < m),
      BlockOK (fun r c =>
        A ⟨i + r, by have := r.isLt; omega⟩ ⟨0 + c, by have := c.isLt; omega⟩) ↔
        V (A ⟨i, by omega⟩) (A ⟨i + 1, by omega⟩) (A ⟨i + 2, hi⟩) := by
    intro i hi
    have e : (fun r c => A ⟨i + r, by have := r.isLt; omega⟩ ⟨0 + c, by have := c.isLt; omega⟩ :
        Fin 3 → Fin 3 → Fin 2) = ![A ⟨i, by omega⟩, A ⟨i + 1, by omega⟩, A ⟨i + 2, hi⟩] := by
      funext r c
      fin_cases r <;> fin_cases c <;> rfl
    exact Iff.of_eq (congrArg BlockOK e)
  constructor
  · intro h i hi
    exact (key i hi).1 (h i 0 hi (by norm_num))
  · intro h i j hi hj
    obtain rfl : j = 0 := by omega
    exact (key i hi).2 (h i hi)

theorem chain_cons {m : ℕ} (x : Row) (B : Fin (m + 2) → Row) :
    Chain (Fin.cons x B : Fin (m + 3) → Row) ↔
      V x (B ⟨0, by omega⟩) (B ⟨1, by omega⟩) ∧ Chain B := by
  constructor
  · intro h
    have h0 := h 0 (by omega)
    exact ⟨h0, fun i hi => h (i + 1) (by omega)⟩
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => exact h0
    | succ i => exact h i (by omega)

/-- The number of ways to continue the rows `x, y` by `m` more rows so that every three
consecutive rows satisfy `V`. -/
noncomputable def T (m : ℕ) (x y : Row) : ℕ := by
  classical
  exact ∑ B : Fin m → Row,
    if Chain (Fin.cons x (Fin.cons y B) : Fin (m + 2) → Row) then 1 else 0

theorem T_zero (x y : Row) : T 0 x y = 1 := by
  classical
  unfold T
  rw [Fintype.sum_unique, if_pos]
  intro i hi
  omega

theorem T_succ (m : ℕ) (x y : Row) :
    T (m + 1) x y = ∑ z : Row, if V x y z then T m y z else 0 := by
  classical
  unfold T
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun p => if Chain (Fin.cons x (Fin.cons y (Fin.cons p.1 p.2)) : Fin (m + 3) → Row)
      then 1 else 0) (fun B => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hv : V x y z
  · rw [if_pos hv]
    refine Finset.sum_congr rfl fun B _ => if_congr ?_ rfl rfl
    rw [chain_cons]
    exact and_iff_right hv
  · rw [if_neg hv]
    refine Finset.sum_eq_zero fun B _ => if_neg ?_
    rw [chain_cons]
    exact fun h => hv h.1

theorem a_eq (n : ℕ) : a n = ∑ x : Row, ∑ y : Row, T n x y := by
  classical
  have h1 : a n = ∑ A : Fin (n + 2) → Row, if Chain A then 1 else 0 := by
    unfold a
    rw [Fintype.card_subtype, Finset.card_filter]
    exact Finset.sum_congr rfl fun A _ => if_congr (good_iff A) rfl rfl
  rw [h1, Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun p => if Chain (Fin.cons p.1 p.2 : Fin (n + 2) → Row) then 1 else 0) (fun A => by simp),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun p => if Chain (Fin.cons x (Fin.cons p.1 p.2) : Fin (n + 2) → Row) then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  rfl

/-- The row with code `c`: the bits of `c`, most significant first. -/
def row (c : Fin 8) : Row := fun j => ⟨c.val / 2 ^ (2 - j.val) % 2, Nat.mod_lt _ (by norm_num)⟩

theorem row_injective : Function.Injective row := by
  decide

theorem row_bijective : Function.Bijective row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective, by simp⟩

/-- Bit `j` of `x`, the most significant of three bits first. -/
def bt (x j : ℕ) : ℕ := x / 2 ^ (2 - j) % 2

/-- The code of column `j` of the block whose rows have codes `u, v, w`. -/
def col (u v w j : ℕ) : ℕ := 4 * bt u j + 2 * bt v j + bt w j

/-- `V` on codes: rows, and columns, compare as their codes do. -/
def Vt (u v w : Fin 8) : Bool :=
  decide (u.val ≤ v.val) && decide (v.val ≤ w.val) && decide (col u v w 0 ≤ col u v w 1) &&
    decide (col u v w 1 ≤ col u v w 2)

theorem V_iff : ∀ u v w : Fin 8, V (row u) (row v) (row w) ↔ Vt u v w = true := by
  decide +kernel

/-- The transfer recursion on codes. -/
def G : ℕ → Fin 8 → Fin 8 → ℕ
  | 0, _, _ => 1
  | m + 1, u, v => ∑ w : Fin 8, if Vt u v w then G m v w else 0

theorem T_eq_G (m : ℕ) : ∀ u v : Fin 8, T m (row u) (row v) = G m u v := by
  induction m with
  | zero => intro u v; rw [T_zero]; rfl
  | succ m ih =>
    intro u v
    rw [T_succ, ← row_bijective.sum_comp]
    simp only [G]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ih v w]
    exact if_congr (V_iff u v w) rfl rfl

theorem a_eq_G (n : ℕ) : a n = ∑ u : Fin 8, ∑ v : Fin 8, G n u v := by
  rw [a_eq, ← row_bijective.sum_comp]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← row_bijective.sum_comp]
  exact Finset.sum_congr rfl fun v _ => T_eq_G n u v

/-- The type of the pair of codes `(u, v)` of two consecutive rows. -/
def typ (u v : Fin 8) : ℕ :=
  if u.val = 0 ∧ v.val = 0 then 1
  else if (u.val = 0 ∨ u.val = 1) ∧ v.val = 1 then 2
  else if (u.val = 0 ∨ u.val = 1 ∨ u.val = 3) ∧ v.val = 3 then 3
  else if (u.val = 0 ∨ u.val = 1 ∨ u.val = 3 ∨ u.val = 7) ∧ v.val = 7 then 4
  else 0

/-- Coefficient of `n ^ 3` in `P t n`. -/
def c3 (t : ℕ) : ℤ := if t = 1 then 1 else 0

/-- Coefficient of `n ^ 2` in `P t n`. -/
def c2 (t : ℕ) : ℤ := if t = 1 then 30 else if t = 2 then 3 else 0

/-- Coefficient of `n` in `P t n`. -/
def c1 (t : ℕ) : ℤ := if t = 1 then 17 else if t = 2 then 57 else if t = 3 then 6 else 0

/-- Constant coefficient of `P t n`. -/
def c0 (t : ℕ) : ℤ :=
  if t = 1 then -78 else if t = 2 then -12 else if t = 3 then 54 else if t = 4 then 6 else 0

/-- Six times the number of continuations by `n ≥ 2` rows of a pair of type `t`. -/
def P (t : ℕ) (n : ℤ) : ℤ := c3 t * n ^ 3 + c2 t * n ^ 2 + c1 t * n + c0 t

/-- The induction step of `G_closed`, coefficient by coefficient. -/
theorem step_facts : ∀ u v : Fin 8,
    (∑ w : Fin 8, if Vt u v w then c3 (typ v w) else 0) = c3 (typ u v) ∧
    (∑ w : Fin 8, if Vt u v w then c2 (typ v w) else 0) = 3 * c3 (typ u v) + c2 (typ u v) ∧
    (∑ w : Fin 8, if Vt u v w then c1 (typ v w) else 0) =
      3 * c3 (typ u v) + 2 * c2 (typ u v) + c1 (typ u v) ∧
    (∑ w : Fin 8, if Vt u v w then c0 (typ v w) else 0) =
      c3 (typ u v) + c2 (typ u v) + c1 (typ u v) + c0 (typ u v) := by
  decide +kernel

theorem base_facts : ∀ u v : Fin 8, 6 * (G 2 u v : ℤ) = P (typ u v) 2 := by
  decide +kernel

theorem G_closed (n : ℕ) (hn : 2 ≤ n) :
    ∀ u v : Fin 8, 6 * (G n u v : ℤ) = P (typ u v) n := by
  induction n, hn using Nat.le_induction with
  | base => exact base_facts
  | succ n hn ih =>
    intro u v
    have hsum : 6 * (G (n + 1) u v : ℤ) =
        ∑ w : Fin 8, if Vt u v w then P (typ v w) n else 0 := by
      rw [G]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      split_ifs
      · exact ih v w
      · simp
    rw [hsum]
    have hP : ∀ w : Fin 8, (if Vt u v w then P (typ v w) n else 0) =
        (if Vt u v w then c3 (typ v w) else 0) * (n : ℤ) ^ 3 +
        (if Vt u v w then c2 (typ v w) else 0) * (n : ℤ) ^ 2 +
        (if Vt u v w then c1 (typ v w) else 0) * (n : ℤ) +
        (if Vt u v w then c0 (typ v w) else 0) := by
      intro w
      split_ifs <;> simp [P]
    simp only [hP, Finset.sum_add_distrib, ← Finset.sum_mul]
    obtain ⟨h3, h2, h1, h0⟩ := step_facts u v
    rw [h3, h2, h1, h0]
    unfold P
    push_cast
    ring

theorem sum_facts :
    (∑ u : Fin 8, ∑ v : Fin 8, c3 (typ u v)) = 1 ∧
    (∑ u : Fin 8, ∑ v : Fin 8, c2 (typ u v)) = 36 ∧
    (∑ u : Fin 8, ∑ v : Fin 8, c1 (typ u v)) = 149 ∧
    (∑ u : Fin 8, ∑ v : Fin 8, c0 (typ u v)) = 84 := by
  decide +kernel

theorem a_one : a 1 = 45 := by
  rw [a_eq_G]
  decide +kernel

theorem closed (n : ℕ) (hn : 1 ≤ n) :
    6 * (a n : ℤ) = (n : ℤ) ^ 3 + 36 * n ^ 2 + 149 * n + 84 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [a_one]
    norm_num
  · rw [a_eq_G]
    push_cast
    simp only [Finset.mul_sum, G_closed n h]
    simp only [P, Finset.sum_add_distrib, ← Finset.sum_mul]
    obtain ⟨h3, h2, h1, h0⟩ := sum_facts
    rw [h3, h2, h1, h0]
    ring

theorem closedQ (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = ((n : ℚ) ^ 3 + 36 * n ^ 2 + 149 * n + 84) / 6 := by
  have h : ((6 * (a n : ℤ) : ℤ) : ℚ) =
      (((n : ℤ) ^ 3 + 36 * n ^ 2 + 149 * n + 84 : ℤ) : ℚ) := by
    rw [closed n hn]
  push_cast at h
  linarith

theorem recurrence (n : ℕ) (hn : 4 < n) :
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
      X * (45 - 91 * X + 61 * X ^ 2 - 14 * X ^ 3) := by
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hF
  have key : PowerSeries.mk F * (1 - X) ^ 4 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 4 * (PowerSeries.mk F * X ^ 1) +
        C 6 * (PowerSeries.mk F * X ^ 2) - C 4 * (PowerSeries.mk F * X ^ 3) +
        C 1 * (PowerSeries.mk F * X ^ 4) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (45 - 91 * X + 61 * X ^ 2 - 14 * X ^ 3) =
      C 45 * X ^ 1 - C 91 * X ^ 2 + C 61 * X ^ 3 - C 14 * X ^ 4 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 5
  · interval_cases k <;> norm_num [hF, closedQ]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 5 := ⟨k - 5, by omega⟩
    simp only [show 0 ≤ j + 5 by omega, show 1 ≤ j + 5 by omega, show 2 ≤ j + 5 by omega,
      show 3 ≤ j + 5 by omega, show 4 ≤ j + 5 by omega,
      show j + 5 - 0 = j + 5 by omega, show j + 5 - 1 = j + 4 by omega,
      show j + 5 - 2 = j + 3 by omega, show j + 5 - 3 = j + 2 by omega,
      show j + 5 - 4 = j + 1 by omega,
      show ¬ (j + 5 = 1) by omega, show ¬ (j + 5 = 2) by omega, show ¬ (j + 5 = 3) by omega,
      show ¬ (j + 5 = 4) by omega, show ¬ (j + 5 = 0) by omega, show ¬ (j + 4 = 0) by omega,
      show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega, show ¬ (j + 1 = 0) by omega,
      if_true, if_false, hF]
    rw [closedQ (j + 5) (by omega), closedQ (j + 4) (by omega), closedQ (j + 3) (by omega),
      closedQ (j + 2) (by omega), closedQ (j + 1) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a184540.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
