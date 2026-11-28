import OMAStatements.S_oeis_a208283

/-!
# Four-column binary arrays avoiding horizontal and vertical triples

This proves Colin Barker's recurrence and generating function for
R. H. Hardin's OEIS A208283 (https://oeis.org/A208283). Once two
successive rows are fixed, the earlier row imposes only a columnwise
restriction on the next row. There are 16 possible rows. Six explicit
16-by-16 integer tables certify that the fifth finite difference vanishes
in every continuation state. The same linear recurrence for all later
lengths follows by induction under the row transfer. Summing over the
first two rows recovers the original array count. We also prove its
quartic closed form for every positive number of rows.
-/

namespace Rows208

abbrev Row := Fin 4 → Fin 2

/-- A horizontal forbidden triple begins with two zeroes. -/
def horiz (r : Row) : Bool :=
  decide ((r 0 ≠ 0 ∨ r 1 ≠ 0) ∧ (r 1 ≠ 0 ∨ r 2 ≠ 0))

/-- In a column, two consecutive equal bits force the following bit. -/
def vert (u v w : Row) : Bool :=
  decide (∀ j : Fin 4, u j=v j → v j=w j)

/-- Count continuations after the two specified rows. -/
def D : ℕ → Row → Row → ℤ
  | 0, u, v => if horiz u && horiz v then 1 else 0
  | t+1, u, v => if horiz u then ∑ w : Row, if vert u v w then D t v w else 0 else 0

def total (t : ℕ) : ℤ := ∑ u : Row, ∑ v : Row, D t u v

end Rows208

namespace Rows208

open OMA.S_oeis_a208283

private def rowValue (u : Row) (j : ℕ) : ℕ :=
  if h : j < 4 then (u ⟨j,h⟩).val else 0

private theorem get_rowValue {r i : ℕ} (x : Fin r → Row) (hi : i < r) (j : ℕ) :
    get x i j = rowValue (x ⟨i,hi⟩) j := by
  by_cases h : j < 4 <;> simp [OMA.S_oeis_a208283.get, rowValue, hi, h]

private theorem horiz_bits : ∀ a b c : Fin 2,
    ((a.val,b.val,c.val) ≠ (0,0,0) ∧ (a.val,b.val,c.val) ≠ (0,0,1)) ↔
      a ≠ 0 ∨ b ≠ 0 := by decide

private theorem vert_bits : ∀ a b c : Fin 2,
    ((a.val,b.val,c.val) ≠ (0,0,1) ∧ (a.val,b.val,c.val) ≠ (1,1,0)) ↔
      (a = b → b = c) := by decide

private theorem horiz_windows (u : Row) :
    horiz u = true ↔ ∀ j < 2,
      (rowValue u j, rowValue u (j+1), rowValue u (j+2)) ≠ (0,0,0) ∧
      (rowValue u j, rowValue u (j+1), rowValue u (j+2)) ≠ (0,0,1) := by
  simp only [horiz, decide_eq_true_eq]
  constructor
  · intro h j hj
    interval_cases j
    · exact (horiz_bits (u 0) (u 1) (u 2)).mpr h.1
    · exact (horiz_bits (u 1) (u 2) (u 3)).mpr h.2
  · intro h
    exact ⟨(horiz_bits (u 0) (u 1) (u 2)).mp (h 0 (by decide)),
      (horiz_bits (u 1) (u 2) (u 3)).mp (h 1 (by decide))⟩

private theorem vert_windows (u v w : Row) :
    vert u v w = true ↔ ∀ j < 4,
      (rowValue u j, rowValue v j, rowValue w j) ≠ (0,0,1) ∧
      (rowValue u j, rowValue v j, rowValue w j) ≠ (1,1,0) := by
  simp only [vert, decide_eq_true_eq]
  constructor
  · intro h j hj
    simpa only [rowValue, dif_pos hj] using
      (vert_bits (u ⟨j,hj⟩) (v ⟨j,hj⟩) (w ⟨j,hj⟩)).mpr (h ⟨j,hj⟩)
  · intro h j
    apply (vert_bits (u j) (v j) (w j)).mp
    simpa only [rowValue, dif_pos j.isLt] using h j.val j.isLt

private theorem avoids_windows {r : ℕ} (x : Fin r → Row) :
    avoids x = true ↔
      (∀ i : Fin r, horiz (x i) = true) ∧
      (∀ (i : ℕ) (hi : i + 2 < r), vert (x ⟨i,by omega⟩)
        (x ⟨i+1,by omega⟩) (x ⟨i+2,hi⟩) = true) := by
  simp only [avoids, decide_eq_true_eq]
  constructor
  · rintro ⟨hh,hv⟩
    constructor
    · intro i
      apply (horiz_windows _).mpr
      simpa only [get_rowValue x i.isLt] using hh i.val i.isLt
    · intro i hi
      apply (vert_windows _ _ _).mpr
      simpa only [get_rowValue x (show i < r by omega),
        get_rowValue x (show i+1 < r by omega), get_rowValue x hi] using
        hv i (by omega)
  · rintro ⟨hh,hv⟩
    constructor
    · intro i hi
      simpa only [get_rowValue x hi] using (horiz_windows _).mp (hh ⟨i,hi⟩)
    · intro i hi
      have h2 : i+2 < r := by omega
      simpa only [get_rowValue x (show i < r by omega),
        get_rowValue x (show i+1 < r by omega), get_rowValue x h2] using
        (vert_windows _ _ _).mp (hv i h2)

theorem avoids_cons {t : ℕ} (u : Row) (x : Fin (t+2) → Row) :
    avoids (Fin.cons u x) = true ↔
      horiz u = true ∧ vert u (x 0) (x 1) = true ∧ avoids x = true := by
  have hone : (1 : Fin (t+2)) = ⟨1, by omega⟩ := by
    apply Fin.ext
    change 1 % (t + 2) = 1
    exact Nat.mod_eq_of_lt (by omega)
  rw [hone, avoids_windows, avoids_windows]
  constructor
  · rintro ⟨hh,hv⟩
    refine ⟨hh 0, ?_, ?_, ?_⟩
    · have top := hv 0 (by omega)
      exact top
    · intro i
      exact hh i.succ
    · intro i hi
      exact hv (i+1) (by omega)
  · rintro ⟨hu, ht, hh, hv⟩
    constructor
    · exact Fin.forall_fin_succ.mpr ⟨hu,hh⟩
    · rintro (_|i) hi
      · exact ht
      · exact hv i (by omega)

theorem avoids_two (u v : Row) :
    avoids ![u,v] = true ↔ horiz u = true ∧ horiz v = true := by
  rw [avoids_windows]
  constructor
  · intro h
    exact ⟨h.1 0, h.1 1⟩
  · rintro ⟨hu,hv⟩
    constructor
    · intro i
      fin_cases i <;> assumption
    · intro i hi
      omega

theorem avoids_one (u : Row) : avoids ![u] = true ↔ horiz u = true := by
  rw [avoids_windows]
  constructor
  · exact fun h => h.1 0
  · intro hu
    constructor
    · intro i
      fin_cases i
      exact hu
    · intro i hi
      omega

end Rows208

namespace Rows208
open Finset

theorem sum_cons_rows {t : ℕ} (f : (Fin (t+1) → Row) → ℤ) :
    ∑ x,f x = ∑ u : Row,∑ y : Fin t → Row,f (Fin.cons u y) := by
  rw [←(Fin.consEquiv (fun _ : Fin (t+1) => Row)).sum_comp f,Fintype.sum_prod_type]
  rfl

/-- The sums over all continuations of two prescribed rows agree with the
finite-state recurrence whenever the two local decomposition laws hold. -/
theorem count_continuations (P : {r : ℕ} → (Fin r → Row) → Bool)
    (step : ∀ {t : ℕ} (u : Row) (x : Fin (t+2) → Row), P (Fin.cons u x) = true ↔
      horiz u=true ∧ vert u (x 0) (x 1)=true ∧ P x=true)
    (pair : ∀ u v : Row, P ![u,v]=true ↔ horiz u=true ∧ horiz v=true)
    (t : ℕ) (u v : Row) :
    (∑ y : Fin t → Row, if P (Fin.cons u (Fin.cons v y)) then (1:ℤ) else 0)=D t u v := by
  induction t generalizing u v with
  | zero =>
    have he (y : Fin 0 → Row) : Fin.cons u (Fin.cons v y) = ![u,v] := by
      funext i; fin_cases i <;> rfl
    simp only [he,pair,D,Bool.and_eq_true]
    simp
  | succ t ih =>
    rw [sum_cons_rows,D]
    have eqv (w : Row) (y : Fin t → Row) : P (Fin.cons u (Fin.cons v (Fin.cons w y)))=true ↔
        horiz u=true ∧ vert u v w=true ∧ P (Fin.cons v (Fin.cons w y))=true := by
      simpa only [Fin.cons_zero,show (1 : Fin (t+2))=Fin.succ 0 by rfl,Fin.cons_succ] using
        step u (Fin.cons v (Fin.cons w y))
    simp only [eqv]
    by_cases hu : horiz u=true
    · simp only [hu,true_and,if_true]
      apply sum_congr rfl
      intro w _
      by_cases hw : vert u v w=true
      · simpa only [hw,if_true,true_and] using ih v w
      · simp [hw]
    · simp [hu]

theorem count_all_rows (P : {r : ℕ} → (Fin r → Row) → Bool)
    (step : ∀ {t : ℕ} (u : Row) (x : Fin (t+2) → Row), P (Fin.cons u x) = true ↔
      horiz u=true ∧ vert u (x 0) (x 1)=true ∧ P x=true)
    (pair : ∀ u v : Row, P ![u,v]=true ↔ horiz u=true ∧ horiz v=true)
    (t : ℕ) : (↑((univ.filter fun x : Fin (t+2) → Row => P x).card):ℤ) = total t := by
  have base : (↑((univ.filter fun x : Fin (t+2) → Row => P x).card):ℤ) =
      ∑ x : Fin (t+2) → Row,if P x then (1:ℤ) else 0 := by
    rw [card_filter]; simp
  rw [base,sum_cons_rows]
  unfold total
  apply sum_congr rfl
  intro u _
  rw [sum_cons_rows]
  exact sum_congr rfl (fun v _ => count_continuations P step pair t u v)

theorem count_one_row (P : (Fin 1 → Row) → Bool)
    (one : ∀ u : Row, P ![u]=true ↔ horiz u=true) :
    (↑((univ.filter fun x : Fin 1 → Row => P x).card):ℤ) = 10 := by
  have base : (↑((univ.filter fun x : Fin 1 → Row => P x).card):ℤ) =
    ∑ x : Fin 1 → Row,if P x then (1:ℤ) else 0 := by
    rw [card_filter]; simp
  rw [base,sum_cons_rows]
  have he (u : Row) (y : Fin 0 → Row) : Fin.cons u y = ![u] := by
    funext i; fin_cases i; rfl
  simp only [he,one]
  have h : (∑ u : Row,if horiz u then (1:ℤ) else 0)=10 := by decide +kernel
  simpa using h

end Rows208

namespace Rows208

/-- Encode a row with its leftmost bit in the least significant position. -/
private def rowCode (r : Row) : ℕ :=
  (r 0).val + 2*(r 1).val + 4*(r 2).val + 8*(r 3).val

/-- The transfer counts for zero through five extension steps, indexed by two row masks. -/
private def tabData : Array (Array ℕ) := #[
  #[
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1,
    0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1,
    0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1,
    0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1,
    0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1,
    0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1,
    0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1
  ],
  #[
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1, 2, 0, 5, 2, 4, 0, 0, 2, 4, 0, 10, 4, 8,
    0, 0, 2, 1, 0, 3, 4, 2, 0, 0, 4, 2, 0, 6, 8, 4,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 5, 3, 0, 1, 3, 2, 0, 0, 10, 6, 0, 2, 6, 4,
    0, 0, 2, 4, 0, 3, 1, 2, 0, 0, 4, 8, 0, 6, 2, 4,
    0, 0, 4, 2, 0, 2, 2, 1, 0, 0, 8, 4, 0, 4, 4, 2,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 2, 4, 0, 10, 4, 8, 0, 0, 1, 2, 0, 5, 2, 4,
    0, 0, 4, 2, 0, 6, 8, 4, 0, 0, 2, 1, 0, 3, 4, 2,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 10, 6, 0, 2, 6, 4, 0, 0, 5, 3, 0, 1, 3, 2,
    0, 0, 4, 8, 0, 6, 2, 4, 0, 0, 2, 4, 0, 3, 1, 2,
    0, 0, 8, 4, 0, 4, 4, 2, 0, 0, 4, 2, 0, 2, 2, 1
  ],
  #[
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1, 3, 0, 14, 3, 9, 0, 0, 3, 9, 0, 42, 9, 27,
    0, 0, 3, 1, 0, 6, 9, 3, 0, 0, 9, 3, 0, 18, 27, 9,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 14, 6, 0, 1, 6, 3, 0, 0, 42, 18, 0, 3, 18, 9,
    0, 0, 3, 9, 0, 6, 1, 3, 0, 0, 9, 27, 0, 18, 3, 9,
    0, 0, 9, 3, 0, 3, 3, 1, 0, 0, 27, 9, 0, 9, 9, 3,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 3, 9, 0, 42, 9, 27, 0, 0, 1, 3, 0, 14, 3, 9,
    0, 0, 9, 3, 0, 18, 27, 9, 0, 0, 3, 1, 0, 6, 9, 3,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 42, 18, 0, 3, 18, 9, 0, 0, 14, 6, 0, 1, 6, 3,
    0, 0, 9, 27, 0, 18, 3, 9, 0, 0, 3, 9, 0, 6, 1, 3,
    0, 0, 27, 9, 0, 9, 9, 3, 0, 0, 9, 3, 0, 3, 3, 1
  ],
  #[
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1, 4, 0, 30, 4, 16, 0, 0, 4, 16, 0, 120, 16, 64,
    0, 0, 4, 1, 0, 10, 16, 4, 0, 0, 16, 4, 0, 40, 64, 16,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 30, 10, 0, 1, 10, 4, 0, 0, 120, 40, 0, 4, 40, 16,
    0, 0, 4, 16, 0, 10, 1, 4, 0, 0, 16, 64, 0, 40, 4, 16,
    0, 0, 16, 4, 0, 4, 4, 1, 0, 0, 64, 16, 0, 16, 16, 4,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 4, 16, 0, 120, 16, 64, 0, 0, 1, 4, 0, 30, 4, 16,
    0, 0, 16, 4, 0, 40, 64, 16, 0, 0, 4, 1, 0, 10, 16, 4,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 120, 40, 0, 4, 40, 16, 0, 0, 30, 10, 0, 1, 10, 4,
    0, 0, 16, 64, 0, 40, 4, 16, 0, 0, 4, 16, 0, 10, 1, 4,
    0, 0, 64, 16, 0, 16, 16, 4, 0, 0, 16, 4, 0, 4, 4, 1
  ],
  #[
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1, 5, 0, 55, 5, 25, 0, 0, 5, 25, 0, 275, 25, 125,
    0, 0, 5, 1, 0, 15, 25, 5, 0, 0, 25, 5, 0, 75, 125, 25,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 55, 15, 0, 1, 15, 5, 0, 0, 275, 75, 0, 5, 75, 25,
    0, 0, 5, 25, 0, 15, 1, 5, 0, 0, 25, 125, 0, 75, 5, 25,
    0, 0, 25, 5, 0, 5, 5, 1, 0, 0, 125, 25, 0, 25, 25, 5,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 5, 25, 0, 275, 25, 125, 0, 0, 1, 5, 0, 55, 5, 25,
    0, 0, 25, 5, 0, 75, 125, 25, 0, 0, 5, 1, 0, 15, 25, 5,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 275, 75, 0, 5, 75, 25, 0, 0, 55, 15, 0, 1, 15, 5,
    0, 0, 25, 125, 0, 75, 5, 25, 0, 0, 5, 25, 0, 15, 1, 5,
    0, 0, 125, 25, 0, 25, 25, 5, 0, 0, 25, 5, 0, 5, 5, 1
  ],
  #[
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1, 6, 0, 91, 6, 36, 0, 0, 6, 36, 0, 546, 36, 216,
    0, 0, 6, 1, 0, 21, 36, 6, 0, 0, 36, 6, 0, 126, 216, 36,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 91, 21, 0, 1, 21, 6, 0, 0, 546, 126, 0, 6, 126, 36,
    0, 0, 6, 36, 0, 21, 1, 6, 0, 0, 36, 216, 0, 126, 6, 36,
    0, 0, 36, 6, 0, 6, 6, 1, 0, 0, 216, 36, 0, 36, 36, 6,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 6, 36, 0, 546, 36, 216, 0, 0, 1, 6, 0, 91, 6, 36,
    0, 0, 36, 6, 0, 126, 216, 36, 0, 0, 6, 1, 0, 21, 36, 6,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 546, 126, 0, 6, 126, 36, 0, 0, 91, 21, 0, 1, 21, 6,
    0, 0, 36, 216, 0, 126, 6, 36, 0, 0, 6, 36, 0, 21, 1, 6,
    0, 0, 216, 36, 0, 36, 36, 6, 0, 0, 36, 6, 0, 6, 6, 1
  ]
]

private def tab (t : ℕ) (u v : Row) : ℤ :=
  ((tabData[t]?.getD #[])[16*rowCode u+rowCode v]?.getD 0 : ℕ)

private lemma tab_zero : ∀ u v : Row, tab 0 u v = D 0 u v := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
private lemma tab_step_0 : ∀ u v : Row, tab 1 u v =
    (if horiz u then ∑ w : Row, if vert u v w then tab 0 v w else 0 else 0) := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
private lemma tab_step_1 : ∀ u v : Row, tab 2 u v =
    (if horiz u then ∑ w : Row, if vert u v w then tab 1 v w else 0 else 0) := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
private lemma tab_step_2 : ∀ u v : Row, tab 3 u v =
    (if horiz u then ∑ w : Row, if vert u v w then tab 2 v w else 0 else 0) := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
private lemma tab_step_3 : ∀ u v : Row, tab 4 u v =
    (if horiz u then ∑ w : Row, if vert u v w then tab 3 v w else 0 else 0) := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
private lemma tab_step_4 : ∀ u v : Row, tab 5 u v =
    (if horiz u then ∑ w : Row, if vert u v w then tab 4 v w else 0 else 0) := by decide +kernel

private lemma tab_recurrence : ∀ u v : Row, tab 5 u v =
    5*tab 4 u v - 10*tab 3 u v + 10*tab 2 u v - 5*tab 1 u v + tab 0 u v := by decide +kernel

private lemma tab_values :
    (∑ u : Row, ∑ v : Row, tab 0 u v) = 100 ∧
    (∑ u : Row, ∑ v : Row, tab 1 u v) = 378 ∧
    (∑ u : Row, ∑ v : Row, tab 2 u v) = 984 ∧
    (∑ u : Row, ∑ v : Row, tab 3 u v) = 2090 ∧
    (∑ u : Row, ∑ v : Row, tab 4 u v) = 3900 := by decide +kernel

private lemma tab_eq_1 (u v : Row) : tab 1 u v = D 1 u v := by
  rw [tab_step_0, D]
  simp only [tab_zero]

private lemma tab_eq_2 (u v : Row) : tab 2 u v = D 2 u v := by
  rw [tab_step_1, D]
  simp only [tab_eq_1]

private lemma tab_eq_3 (u v : Row) : tab 3 u v = D 3 u v := by
  rw [tab_step_2, D]
  simp only [tab_eq_2]

private lemma tab_eq_4 (u v : Row) : tab 4 u v = D 4 u v := by
  rw [tab_step_3, D]
  simp only [tab_eq_3]

private lemma tab_eq_5 (u v : Row) : tab 5 u v = D 5 u v := by
  rw [tab_step_4, D]
  simp only [tab_eq_4]

private def evolve (f : Row → Row → ℤ) (u v : Row) : ℤ :=
  if horiz u then ∑ w : Row, if vert u v w then f v w else 0 else 0

theorem state_recurrence (t : ℕ) (u v : Row) :
    D (t+5) u v = 5*D (t+4) u v - 10*D (t+3) u v + 10*D (t+2) u v - 5*D (t+1) u v + D t u v := by
  induction t generalizing u v with
  | zero => simpa only [Nat.zero_add, tab_eq_5, tab_eq_4, tab_eq_3, tab_eq_2, tab_eq_1, tab_zero] using tab_recurrence u v
  | succ t ih =>
    change evolve (D (t+5)) u v =
      5*evolve (D (t+4)) u v - 10*evolve (D (t+3)) u v +
      10*evolve (D (t+2)) u v - 5*evolve (D (t+1)) u v + evolve (D t) u v
    unfold evolve
    by_cases hu : horiz u
    · simp only [hu, if_true]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro w _
      by_cases hw : vert u v w
      · simpa only [hw, if_true] using ih v w
      · simp [hw]
    · simp [hu]

theorem total_recurrence (t : ℕ) :
    total (t+5) = 5*total (t+4) - 10*total (t+3) + 10*total (t+2) - 5*total (t+1) + total t := by
  simp only [total, state_recurrence t, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem total_initial : total 0=100 ∧ total 1=378 ∧ total 2=984 ∧ total 3=2090 ∧ total 4=3900 := by
  simpa only [total,tab_eq_4,tab_eq_3,tab_eq_2,tab_eq_1,tab_zero] using tab_values

end Rows208

namespace Rows208
open PowerSeries

theorem finish (a : ℕ → ℤ)
    (h1 : a 1=10) (h2 : a 2=100) (h3 : a 3=378) (h4 : a 4=984) (h5 : a 5=2090)
    (rec : ∀ n : ℕ, 6≤n → a n = 5*a (n-1)-10*a (n-2)+10*a (n-3)-5*a (n-4)+a (n-5)) :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) *
      ((1 - X)^5 : PowerSeries ℚ) = 2*X*(5+25*X-11*X^2-3*X^3)) ∧
    (∀ n : ℕ, 6 ≤ n → (a n : ℚ) = 5*a (n-1)-10*a (n-2)+10*a (n-3)-5*a (n-4)+a (n-5)) := by
  have hq (n : ℕ) (hn : 6≤n) : (a n : ℚ) =
      5*a (n-1)-10*a (n-2)+10*a (n-3)-5*a (n-4)+a (n-5) := by
    exact_mod_cast rec n hn
  refine ⟨?_,hq⟩
  let S : PowerSeries ℚ := PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ))
  have vals (n : ℕ) : coeff n S = if n<1 then 0 else (a n:ℚ) := coeff_mk _ _
  have left : S*(1-X)^5 =
      S-C (5:ℚ)*(S*X^1)+C (10:ℚ)*(S*X^2)-C (10:ℚ)*(S*X^3)+C (5:ℚ)*(S*X^4)-S*X^5 := by
    simp only [map_ofNat]; ring
  have right : 2*X*(5+25*X-11*X^2-3*X^3 : PowerSeries ℚ) =
      C (10:ℚ)*X^1+C (50:ℚ)*X^2-C (22:ℚ)*X^3-C (6:ℚ)*X^4 := by
    simp only [map_ofNat]; ring
  change S*_ = _
  rw [left,right]
  ext n
  simp only [map_add,map_sub,coeff_C_mul,coeff_mul_X_pow',coeff_C,vals]
  by_cases h : n<6
  · interval_cases n <;> norm_num [h1,h2,h3,h4,h5]
  · simp (disch := omega) only [if_pos,if_neg]
    linarith [hq n (by omega)]

theorem closed_form (a : ℕ → ℤ)
    (h1 : a 1=10) (h2 : a 2=100) (h3 : a 3=378) (h4 : a 4=984) (h5 : a 5=2090)
    (rec : ∀ n : ℕ, 6≤n → a n = 5*a (n-1)-10*a (n-2)+10*a (n-3)-5*a (n-4)+a (n-5))
    (n : ℕ) (hn : 1≤n) : 3*a n = 4*(n:ℤ)^4 + 30*(n:ℤ)^3 + 2*(n:ℤ)^2 - 6*(n:ℤ) := by
  let P (x : ℤ) := 4*x^4+30*x^3+2*x^2-6*x
  change 3*a n=P n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hs : n<6
    · interval_cases n <;> norm_num [P,h1,h2,h3,h4,h5]
    have step (d : ℕ) (lo : 1≤d) (hi : d≤5) : 3*a (n-d)=P ((n:ℤ)-d) := by
      rw [← Nat.cast_sub (by omega : d≤n)]
      exact ih (n-d) (by omega) (by omega)
    calc
      3*a n = 5*(3*a (n-1))-10*(3*a (n-2))+10*(3*a (n-3))-5*(3*a (n-4))+3*a (n-5) := by
        rw [rec n (by omega)]; ring
      _ = P n := by
        rw [step 1 (by decide) (by decide),step 2 (by decide) (by decide),step 3 (by decide) (by decide),
          step 4 (by decide) (by decide),step 5 (by decide) (by decide)]
        dsimp [P]; ring

end Rows208

namespace Rows208
open OMA.S_oeis_a208283

theorem count_eq_total (t : ℕ) : a (t+2)=total t := by
  exact count_all_rows (fun x => avoids x) avoids_cons avoids_two t

theorem count_initial : a 1=10 ∧ a 2=100 ∧ a 3=378 ∧ a 4=984 ∧ a 5=2090 ∧ a 6=3900 := by
  obtain ⟨t0,t1,t2,t3,t4⟩ := total_initial
  exact ⟨count_one_row (fun x => avoids x) avoids_one,
    (count_eq_total 0).trans t0,(count_eq_total 1).trans t1,(count_eq_total 2).trans t2,
    (count_eq_total 3).trans t3,(count_eq_total 4).trans t4⟩

theorem count_recurrence (n : ℕ) (hn : 6≤n) :
    a n=5*a (n-1)-10*a (n-2)+10*a (n-3)-5*a (n-4)+a (n-5) := by
  by_cases he : n=6
  · obtain ⟨h1,h2,h3,h4,h5,h6⟩ := count_initial
    subst n
    norm_num [h1,h2,h3,h4,h5,h6]
  obtain ⟨t,rfl⟩ : ∃ t : ℕ, n=t+7 := ⟨n-7,by omega⟩
  have tr := total_recurrence t
  rw [←count_eq_total (t+5),←count_eq_total (t+4),←count_eq_total (t+3),
    ←count_eq_total (t+2),←count_eq_total (t+1),←count_eq_total t] at tr
  rw [show t+7-1=t+4+2 by omega,show t+7-2=t+3+2 by omega,
    show t+7-3=t+2+2 by omega,show t+7-4=t+1+2 by omega,show t+7-5=t+2 by omega]
  exact tr

theorem row_array_quartic (n : ℕ) (hn : 1≤n) :
    3*a n=4*(n:ℤ)^4+30*(n:ℤ)^3+2*(n:ℤ)^2-6*(n:ℤ) := by
  obtain ⟨h1,h2,h3,h4,h5,_⟩ := count_initial
  exact closed_form a h1 h2 h3 h4 h5 count_recurrence n hn

end Rows208

theorem OMA.solution : type_of% @OMA.S_oeis_a208283.main := by
  obtain ⟨h1,h2,h3,h4,h5,_⟩ := Rows208.count_initial
  exact Rows208.finish OMA.S_oeis_a208283.a h1 h2 h3 h4 h5 Rows208.count_recurrence
