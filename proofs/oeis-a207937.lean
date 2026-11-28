import OMAStatements.S_oeis_a207937
import Mathlib

/-! # The two enumeration formulas for OEIS A207937

A valid row has one of 35 seven-bit masks. In any three consecutive rows,
every column that changes on the second transition must have changed on the
first. The transfer recursion therefore acts on ordered pairs of legal rows.
We certify its action on eight forward differences, which determine the
number of extensions of every row pair at all heights. -/

open Finset OMA.S_oeis_a207937

abbrev arRow := Fin 7 → Fin 2

def arLegal (r : arRow) : Bool := decide (∀ j : Fin 5,
  let t := ((r ⟨j.val, by omega⟩).val, (r ⟨j.val+1, by omega⟩).val,
    (r ⟨j.val+2, by omega⟩).val)
  t ≠ (0,0,1) ∧ t ≠ (1,0,0))

def arCompat (u v w : arRow) : Bool := decide (∀ j : Fin 7,
  let t := ((u j).val,(v j).val,(w j).val)
  t ≠ (0,0,1) ∧ t ≠ (1,1,0))

def arWays : ℕ → arRow → arRow → ℕ
  | 0, _, _ => 1
  | t+1, u, v => ∑ w : arRow, if arLegal w && arCompat u v w then arWays t v w else 0

private lemma ar_valid_iff {n : ℕ} (x : Fin n → arRow) :
    avoids x = true ↔
      (∀ i : Fin n, arLegal (x i) = true) ∧
      (∀ (i : ℕ) (hi : i+2 < n),
       arCompat (x ⟨i,by omega⟩) (x ⟨i+1,by omega⟩) (x ⟨i+2,hi⟩) = true) := by
  simp only [avoids, arLegal, arCompat, decide_eq_true_eq]
  constructor
  · rintro ⟨h,v⟩
    constructor
    · intro i j
      specialize h i.val i.isLt j.val j.isLt
      simpa [OMA.S_oeis_a207937.get, i.isLt,
        show j.val < 7 by omega, show j.val+1 < 7 by omega, show j.val+2 < 7 by omega] using h
    · intro i hi j
      specialize v i (by omega) j.val j.isLt
      simpa [OMA.S_oeis_a207937.get, j.isLt, hi, show i < n by omega, show i+1 < n by omega] using v
  · rintro ⟨h,v⟩
    constructor
    · intro i hi j hj
      have hj' : j < 5 := hj
      simpa [OMA.S_oeis_a207937.get, hi, show j < 7 by omega,
        show j+1 < 7 by omega, show j+2 < 7 by omega] using h ⟨i,hi⟩ ⟨j,hj'⟩
    · intro i hi j hj
      have hi' : i+2 < n := by omega
      simpa [OMA.S_oeis_a207937.get, hj, hi', show i < n by omega, show i+1 < n by omega]
        using v i hi' ⟨j,hj⟩

private lemma ar_avoids_cons3 {k : ℕ} (u v w : arRow) (x : Fin k → arRow) :
    avoids (Fin.cons u (Fin.cons v (Fin.cons w x))) = true ↔
      arLegal u = true ∧ arCompat u v w = true ∧ avoids (Fin.cons v (Fin.cons w x)) = true := by
  rw [ar_valid_iff, ar_valid_iff]
  constructor
  · rintro ⟨hr,hc⟩
    refine ⟨hr 0, ?_, (fun i => ?_), (fun i hi => ?_)⟩
    · exact hc 0 (by omega)
    · exact hr i.succ
    · exact hc (i+1) (by omega)
  · rintro ⟨hu, huv, hr, hc⟩
    constructor
    · intro i
      exact Fin.cases hu (fun j => hr j) i
    · intro i hi
      cases i with
      | zero => exact huv
      | succ i => exact hc i (by omega)

private lemma ar_avoids_cons2 (u v : arRow) (x : Fin 0 → arRow) :
    avoids (Fin.cons u (Fin.cons v x)) = true ↔ arLegal u = true ∧ arLegal v = true := by
  rw [ar_valid_iff]
  constructor
  · rintro ⟨h,_⟩
    exact ⟨h 0, h 1⟩
  · rintro ⟨hu,hv⟩
    exact ⟨by intro i; fin_cases i <;> assumption, by intro i hi; omega⟩

private lemma ar_sum_cons {k : ℕ} (f : (Fin (k+1) → arRow) → ℕ) :
    (∑ s, f s) = ∑ u : arRow, ∑ x : Fin k → arRow, f (Fin.cons u x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (k+1) => arRow)).sum_comp f, Fintype.sum_prod_type]
  rfl

private lemma ar_tail_count (k : ℕ) (u v : arRow) :
    (∑ x : Fin k → arRow, if avoids (Fin.cons u (Fin.cons v x)) then 1 else 0) =
      if arLegal u && arLegal v then arWays k u v else 0 := by
  induction k generalizing u v with
  | zero =>
    simp only [ar_avoids_cons2, arWays, Bool.and_eq_true]
    simp
  | succ k IH =>
    rw [ar_sum_cons]
    simp only [ar_avoids_cons3, arWays, Bool.and_eq_true]
    by_cases hu : arLegal u = true
    · simp only [hu, true_and]
      by_cases hv : arLegal v = true
      · simp only [hv, if_true]
        apply Finset.sum_congr rfl
        intro w _
        by_cases hc : arCompat u v w = true
        · simpa [hc, hv] using IH v w
        · simp [hc]
      · simp only [hv]
        apply Finset.sum_eq_zero
        intro w _
        by_cases hc : arCompat u v w = true
        · simpa [hc, hv] using IH v w
        · simp [hc]
    · simp [hu]

private theorem ar_count (k : ℕ) :
    a (k+2) = ↑(∑ u : arRow, ∑ v : arRow, if arLegal u && arLegal v then arWays k u v else 0 : ℕ) := by
  unfold a
  apply congrArg (fun m : ℕ => (m : ℤ))
  rw [Finset.card_filter, ar_sum_cons]
  apply Finset.sum_congr rfl
  intro u _
  rw [ar_sum_cons]
  apply Finset.sum_congr rfl
  intro v _
  exact ar_tail_count k u v

private lemma ar_count_one :
    a 1 = ↑(∑ u : arRow, if arLegal u then 1 else 0 : ℕ) := by
  unfold a
  apply congrArg (fun m : ℕ => (m : ℤ))
  rw [Finset.card_filter, ar_sum_cons]
  apply Finset.sum_congr rfl
  intro u _
  have h (x : Fin 0 → arRow) : avoids (Fin.cons u x) = true ↔ arLegal u = true := by
    rw [ar_valid_iff]
    constructor
    · rintro ⟨h,_⟩
      exact h 0
    · intro hu
      exact ⟨by intro i; fin_cases i; exact hu, by intro i hi; omega⟩
  simp [h]

private lemma ar_sum_legal (e : Fin 35 ≃ {r : arRow // arLegal r = true}) (f : arRow → ℕ) :
    (∑ r : arRow, if arLegal r then f r else 0) = ∑ i : Fin 35, f (e i).val := by
  calc
    _ = ∑ r ∈ Finset.univ.filter (fun r : arRow => arLegal r = true), f r :=
      (Finset.sum_filter _ _).symm
    _ = ∑ r : {r : arRow // arLegal r = true}, f r.val :=
      Finset.sum_subtype _ (by simp) _
    _ = _ := (Equiv.sum_comp e (fun r => f r.val)).symm

private theorem ar_count_compressed
    (e : Fin 35 ≃ {r : arRow // arLegal r = true})
    (allowed : Fin 35 → Fin 35 → Fin 35 → Bool)
    (ext : ℕ → Fin 35 → Fin 35 → ℕ)
    (hc : ∀ i j l, arCompat (e i).val (e j).val (e l).val = allowed i j l)
    (h0 : ∀ i j, ext 0 i j = 1)
    (hs : ∀ k i j, ext (k+1) i j = ∑ l : Fin 35, if allowed i j l then ext k j l else 0) :
    a 1 = 35 ∧ ∀ k : ℕ, a (k+2) = ↑(∑ i : Fin 35, ∑ j : Fin 35, ext k i j : ℕ) := by
  have ways (k : ℕ) (i j : Fin 35) : arWays k (e i).val (e j).val = ext k i j := by
    induction k generalizing i j with
    | zero => exact (h0 i j).symm
    | succ k IH =>
      rw [arWays, hs]
      simp only [Bool.and_eq_true, ite_and]
      rw [ar_sum_legal e]
      simp only [hc, IH]
  constructor
  · rw [ar_count_one, ar_sum_legal e (fun _ => 1)]
    norm_num
  · intro k
    rw [ar_count]
    apply congrArg (fun m : ℕ => (m : ℤ))
    simp only [Bool.and_eq_true, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [ar_sum_legal e]
    apply Finset.sum_congr rfl
    intro i _
    rw [ar_sum_legal e]
    simp only [ways]

namespace A207937

def code (i : Fin 35) : ℕ :=
  (#[0,42,43,45,46,47,53,54,55,58,59,61,62,63,85,86,87,90,91,93,94,95,106,107,109,110,111,117,118,119,122,123,125,126,127] : Array ℕ)[i.val]'(by exact i.isLt)

def row (i : Fin 35) (j : Fin 7) : Fin 2 :=
  ⟨(code i / 2^j.val)%2, by omega⟩

def allowed (i j l : Fin 35) : Bool :=
  (((code i ^^^ code j) &&& (code j ^^^ code l)) == (code j ^^^ code l))

def ext : ℕ → Fin 35 → Fin 35 → ℕ
  | 0, _, _ => 1
  | k+1, i, j => ∑ l : Fin 35, if allowed i j l then ext k j l else 0

-- CERTIFICATE

/-- Forward differences at zero of the total number of completions of a row pair. -/
def coef (t : Fin 8) : ℕ :=
  (#[1225, 7752, 21478, 32398, 28746, 15100, 4380, 544] : Array ℕ)[t.val]'(by decide +revert)

/-- Index of the forward-difference vector of each possible pair of rows. -/
private def profileIndex : Array (Array ℕ) := #[
  #[0, 1, 2, 1, 2, 3, 1, 1, 4, 2, 5, 4, 3, 6, 1, 1, 4, 1, 2, 2, 4, 7, 2, 5, 2, 5, 8, 4, 4, 9, 3, 8, 7, 6, 10],
  #[1, 0, 1, 5, 1, 4, 11, 5, 12, 1, 4, 12, 4, 13, 14, 11, 15, 5, 12, 16, 12, 17, 1, 4, 12, 4, 13, 15, 12, 17, 4, 13, 17, 13, 18],
  #[2, 1, 0, 2, 4, 1, 19, 12, 5, 4, 1, 20, 13, 4, 21, 15, 11, 12, 5, 22, 17, 12, 4, 1, 20, 13, 4, 23, 17, 12, 13, 4, 24, 18, 13],
  #[1, 5, 2, 0, 2, 1, 2, 25, 20, 12, 20, 1, 20, 4, 19, 26, 23, 16, 22, 5, 22, 12, 12, 20, 1, 20, 4, 20, 27, 24, 17, 24, 4, 24, 13],
  #[2, 1, 4, 2, 0, 1, 25, 2, 20, 4, 13, 20, 1, 4, 26, 19, 23, 12, 17, 22, 5, 12, 4, 13, 20, 1, 4, 27, 20, 24, 13, 18, 24, 4, 13],
  #[3, 4, 1, 1, 1, 0, 20, 20, 2, 13, 4, 4, 4, 1, 23, 23, 19, 17, 12, 12, 12, 5, 13, 4, 4, 4, 1, 24, 24, 20, 18, 13, 13, 13, 4],
  #[1, 11, 19, 2, 25, 20, 0, 2, 1, 19, 5, 1, 20, 4, 2, 25, 20, 26, 22, 20, 27, 24, 15, 23, 20, 27, 24, 1, 20, 4, 23, 12, 4, 24, 13],
  #[1, 5, 12, 25, 2, 20, 2, 0, 1, 2, 20, 20, 1, 4, 25, 2, 20, 25, 27, 27, 20, 24, 12, 17, 27, 20, 24, 20, 1, 4, 20, 24, 24, 4, 13],
  #[4, 12, 5, 20, 20, 2, 1, 1, 0, 20, 2, 4, 4, 1, 20, 20, 2, 27, 25, 24, 24, 20, 17, 12, 24, 24, 20, 4, 4, 1, 24, 20, 13, 13, 4],
  #[2, 1, 4, 12, 4, 13, 19, 2, 20, 0, 1, 5, 1, 4, 26, 25, 27, 2, 20, 22, 20, 24, 4, 13, 17, 13, 18, 23, 20, 24, 1, 4, 12, 4, 13],
  #[5, 4, 1, 20, 13, 4, 5, 20, 2, 1, 0, 2, 4, 1, 22, 27, 25, 20, 2, 25, 24, 20, 13, 4, 24, 18, 13, 12, 24, 20, 4, 1, 20, 13, 4],
  #[4, 12, 20, 1, 20, 4, 1, 20, 4, 5, 2, 0, 2, 1, 20, 27, 24, 22, 25, 2, 25, 20, 17, 24, 4, 24, 13, 4, 24, 13, 12, 20, 1, 20, 4],
  #[3, 4, 13, 20, 1, 4, 20, 1, 4, 1, 4, 2, 0, 1, 27, 20, 24, 20, 24, 25, 2, 20, 13, 18, 24, 4, 13, 24, 4, 13, 4, 13, 20, 1, 4],
  #[6, 13, 4, 4, 4, 1, 4, 4, 1, 4, 1, 1, 1, 0, 24, 24, 20, 24, 20, 20, 20, 2, 18, 13, 13, 13, 4, 13, 13, 4, 13, 4, 4, 4, 1],
  #[1, 14, 21, 19, 26, 23, 2, 25, 20, 26, 22, 20, 27, 24, 0, 2, 1, 19, 5, 1, 20, 4, 21, 11, 5, 22, 12, 1, 20, 4, 23, 12, 4, 24, 13],
  #[1, 11, 15, 26, 19, 23, 25, 2, 20, 25, 27, 27, 20, 24, 2, 0, 1, 2, 20, 20, 1, 4, 19, 23, 22, 5, 12, 20, 1, 4, 20, 24, 24, 4, 13],
  #[4, 15, 11, 23, 23, 19, 20, 20, 2, 27, 25, 24, 24, 20, 1, 1, 0, 20, 2, 4, 4, 1, 23, 19, 12, 12, 5, 4, 4, 1, 24, 20, 13, 13, 4],
  #[1, 5, 12, 16, 12, 17, 26, 25, 27, 2, 20, 22, 20, 24, 19, 2, 20, 0, 1, 5, 1, 4, 2, 20, 22, 20, 24, 23, 20, 24, 1, 4, 12, 4, 13],
  #[2, 12, 5, 22, 17, 12, 22, 27, 25, 20, 2, 25, 24, 20, 5, 20, 2, 1, 0, 2, 4, 1, 20, 2, 25, 24, 20, 12, 24, 20, 4, 1, 20, 13, 4],
  #[2, 16, 22, 5, 22, 12, 20, 27, 24, 22, 25, 2, 25, 20, 1, 20, 4, 5, 2, 0, 2, 1, 22, 25, 2, 25, 20, 4, 24, 13, 12, 20, 1, 20, 4],
  #[4, 12, 17, 22, 5, 12, 27, 20, 24, 20, 24, 25, 2, 20, 20, 1, 4, 1, 4, 2, 0, 1, 20, 24, 25, 2, 20, 24, 4, 13, 4, 13, 20, 1, 4],
  #[7, 17, 12, 12, 12, 5, 24, 24, 20, 24, 20, 20, 20, 2, 4, 4, 1, 4, 1, 1, 1, 0, 24, 20, 20, 20, 2, 13, 13, 4, 13, 4, 4, 4, 1],
  #[2, 1, 4, 12, 4, 13, 15, 12, 17, 4, 13, 17, 13, 18, 21, 19, 23, 2, 20, 22, 20, 24, 0, 1, 5, 1, 4, 11, 5, 12, 1, 4, 12, 4, 13],
  #[5, 4, 1, 20, 13, 4, 23, 17, 12, 13, 4, 24, 18, 13, 11, 23, 19, 20, 2, 25, 24, 20, 1, 0, 2, 4, 1, 19, 12, 5, 4, 1, 20, 13, 4],
  #[2, 12, 20, 1, 20, 4, 20, 27, 24, 17, 24, 4, 24, 13, 5, 22, 12, 22, 25, 2, 25, 20, 5, 2, 0, 2, 1, 2, 25, 20, 12, 20, 1, 20, 4],
  #[5, 4, 13, 20, 1, 4, 27, 20, 24, 13, 18, 24, 4, 13, 22, 5, 12, 20, 24, 25, 2, 20, 1, 4, 2, 0, 1, 25, 2, 20, 4, 13, 20, 1, 4],
  #[8, 13, 4, 4, 4, 1, 24, 24, 20, 18, 13, 13, 13, 4, 12, 12, 5, 24, 20, 20, 20, 2, 4, 1, 1, 1, 0, 20, 20, 2, 13, 4, 4, 4, 1],
  #[4, 15, 23, 20, 27, 24, 1, 20, 4, 23, 12, 4, 24, 13, 1, 20, 4, 23, 12, 4, 24, 13, 11, 19, 2, 25, 20, 0, 2, 1, 19, 5, 1, 20, 4],
  #[4, 12, 17, 27, 20, 24, 20, 1, 4, 20, 24, 24, 4, 13, 20, 1, 4, 20, 24, 24, 4, 13, 5, 12, 25, 2, 20, 2, 0, 1, 2, 20, 20, 1, 4],
  #[9, 17, 12, 24, 24, 20, 4, 4, 1, 24, 20, 13, 13, 4, 4, 4, 1, 24, 20, 13, 13, 4, 12, 5, 20, 20, 2, 1, 1, 0, 20, 2, 4, 4, 1],
  #[3, 4, 13, 17, 13, 18, 23, 20, 24, 1, 4, 12, 4, 13, 23, 20, 24, 1, 4, 12, 4, 13, 1, 4, 12, 4, 13, 19, 2, 20, 0, 1, 5, 1, 4],
  #[8, 13, 4, 24, 18, 13, 12, 24, 20, 4, 1, 20, 13, 4, 12, 24, 20, 4, 1, 20, 13, 4, 4, 1, 20, 13, 4, 5, 20, 2, 1, 0, 2, 4, 1],
  #[7, 17, 24, 4, 24, 13, 4, 24, 13, 12, 20, 1, 20, 4, 4, 24, 13, 12, 20, 1, 20, 4, 12, 20, 1, 20, 4, 1, 20, 4, 5, 2, 0, 2, 1],
  #[6, 13, 18, 24, 4, 13, 24, 4, 13, 4, 13, 20, 1, 4, 24, 4, 13, 4, 13, 20, 1, 4, 4, 13, 20, 1, 4, 20, 1, 4, 1, 4, 2, 0, 1],
  #[10, 18, 13, 13, 13, 4, 13, 13, 4, 13, 4, 4, 4, 1, 13, 13, 4, 13, 4, 4, 4, 1, 13, 4, 4, 4, 1, 4, 4, 1, 4, 1, 1, 1, 0]]

/-- Forward differences of degrees zero through seven for each profile. -/
private def profiles : Array (Array ℕ) := #[
  #[1, 0, 0, 0, 0, 0, 0, 0],
  #[1, 1, 0, 0, 0, 0, 0, 0],
  #[1, 2, 1, 0, 0, 0, 0, 0],
  #[1, 5, 6, 2, 0, 0, 0, 0],
  #[1, 3, 2, 0, 0, 0, 0, 0],
  #[1, 4, 5, 2, 0, 0, 0, 0],
  #[1, 13, 30, 24, 6, 0, 0, 0],
  #[1, 8, 13, 6, 0, 0, 0, 0],
  #[1, 10, 23, 20, 6, 0, 0, 0],
  #[1, 9, 16, 8, 0, 0, 0, 0],
  #[1, 34, 137, 200, 120, 24, 0, 0],
  #[1, 12, 45, 74, 56, 16, 0, 0],
  #[1, 9, 23, 23, 8, 0, 0, 0],
  #[1, 7, 12, 6, 0, 0, 0, 0],
  #[1, 34, 287, 1079, 2107, 2234, 1224, 272],
  #[1, 25, 159, 431, 576, 376, 96, 0],
  #[1, 24, 147, 386, 502, 320, 80, 0],
  #[1, 19, 87, 161, 132, 40, 0, 0],
  #[1, 15, 50, 60, 24, 0, 0, 0],
  #[1, 7, 16, 15, 5, 0, 0, 0],
  #[1, 5, 7, 3, 0, 0, 0, 0],
  #[1, 20, 116, 298, 384, 244, 61, 0],
  #[1, 14, 55, 92, 70, 20, 0, 0],
  #[1, 15, 62, 108, 85, 25, 0, 0],
  #[1, 11, 31, 33, 12, 0, 0, 0],
  #[1, 8, 19, 18, 6, 0, 0, 0],
  #[1, 23, 139, 363, 471, 300, 75, 0],
  #[1, 17, 73, 129, 102, 30, 0, 0]]

private def weight (i j : Fin 35) (t : ℕ) : ℕ :=
  let c := (profileIndex.getD i.val #[]).getD j.val 0
  (profiles.getD c #[]).getD t 0

private lemma eval_pascal (k r : ℕ) (w : ℕ → ℕ) :
    (∑ t ∈ Finset.range r, k.choose t * (w t + w (t+1))) + k.choose r * w r =
      ∑ t ∈ Finset.range (r+1), (k+1).choose t * w t := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ _ r, Finset.sum_range_succ _ (r+1), ← ih,
      Nat.choose_succ_succ']
    ring

private lemma eval_shift (k : ℕ) (w : ℕ → ℕ) (hw : w 8 = 0) :
    (∑ t : Fin 8, k.choose t.val * (w t.val + w (t.val+1))) =
      ∑ t : Fin 8, (k+1).choose t.val * w t.val := by
  rw [Fin.sum_univ_eq_sum_range (fun t => k.choose t * (w t + w (t+1))),
    Fin.sum_univ_eq_sum_range (fun t => (k+1).choose t * w t)]
  have he := eval_pascal k 8 w
  rw [Finset.sum_range_succ _ 8, hw] at he
  simpa using he

private lemma total_from_weights
    (hstep : ∀ (i j : Fin 35) (t : Fin 8),
      (∑ l : Fin 35, if allowed i j l then weight j l t.val else 0) =
        weight i j t.val + weight i j (t.val+1))
    (hzero : ∀ i j, weight i j 0 = 1)
    (hstop : ∀ i j, weight i j 8 = 0)
    (htotal : ∀ t : Fin 8, (∑ i : Fin 35, ∑ j : Fin 35, weight i j t.val) = coef t)
    (k : ℕ) : (∑ i : Fin 35, ∑ j : Fin 35, ext k i j) =
      ∑ t : Fin 8, k.choose t.val * coef t := by
  have he (m : ℕ) (i j : Fin 35) : ext m i j =
      ∑ t : Fin 8, m.choose t.val * weight i j t.val := by
    induction m generalizing i j with
    | zero =>
      simp [ext, Fin.sum_univ_succ, hzero, Nat.choose_zero_succ]
    | succ m ih =>
      rw [ext, ← eval_shift m (weight i j) (hstop i j)]
      simp_rw [← hstep, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      by_cases h : allowed i j l <;> simp [h, ih]
  simp_rw [he, ← htotal, Finset.mul_sum]
  rw [Finset.sum_comm (γ := Fin 8)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]

private def checkRow (i : Fin 35) : Prop := ∀ (j : Fin 35) (t : Fin 8),
    (∑ l : Fin 35, if allowed i j l then weight j l t.val else 0) =
      weight i j t.val + weight i j (t.val+1)

private instance (i : Fin 35) : Decidable (checkRow i) :=
  inferInstanceAs (Decidable (∀ (j : Fin 35) (t : Fin 8),
    (∑ l : Fin 35, if allowed i j l then weight j l t.val else 0) =
      weight i j t.val + weight i j (t.val+1)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
private lemma weight_step (i : Fin 35) : checkRow i := by
  fin_cases i <;> as_aux_lemma => decide +kernel

set_option maxHeartbeats 2000000 in
private lemma weight_zero : ∀ i j, weight i j 0 = 1 := by decide

set_option maxHeartbeats 2000000 in
private lemma weight_stop : ∀ i j, weight i j 8 = 0 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private lemma weight_total : ∀ t : Fin 8,
    (∑ i : Fin 35, ∑ j : Fin 35, weight i j t.val) = coef t := by decide

theorem transfer_total (k : ℕ) : (∑ i : Fin 35, ∑ j : Fin 35, ext k i j) =
    ∑ t : Fin 8, k.choose t.val * coef t :=
  total_from_weights weight_step weight_zero weight_stop weight_total k

end A207937

private theorem ar_coded_legal : ∀ i : Fin 35, arLegal (A207937.row i) = true := by
  decide +kernel

private theorem ar_coded_inj :
    ∀ i j : Fin 35, A207937.row i = A207937.row j → i = j := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3500000 in
private theorem ar_coded_complete :
    ∀ r : arRow, arLegal r = true → ∃ i : Fin 35, A207937.row i = r := by
  decide +kernel

private noncomputable def arRowEquiv : Fin 35 ≃ {r : arRow // arLegal r = true} :=
  Equiv.ofBijective (fun i => ⟨A207937.row i, ar_coded_legal i⟩)
    ⟨fun _ _ h => ar_coded_inj _ _ (congrArg Subtype.val h), by
      rintro ⟨r,hr⟩
      obtain ⟨i,hi⟩ := ar_coded_complete r hr
      exact ⟨i,Subtype.ext hi⟩⟩

private theorem ar_allowed_table :
    ∀ i j l : Fin 35, arCompat (A207937.row i) (A207937.row j) (A207937.row l) =
      A207937.allowed i j l := by
  have localRule : ∀ a b c : Fin 2,
      ((a.val,b.val,c.val) ≠ (0,0,1) ∧ (a.val,b.val,c.val) ≠ (1,1,0)) ↔
      (((decide (a.val=1) ^^ decide (b.val=1)) && (decide (b.val=1) ^^ decide (c.val=1))) =
        (decide (b.val=1) ^^ decide (c.val=1))) := by decide
  have small : ∀ i : Fin 35, A207937.code i < 2^7 := by decide
  have bits (i : Fin 35) (j : Fin 7) :
      decide ((A207937.row i j).val = 1) = (A207937.code i).testBit j.val :=
    Nat.testBit_eq_decide_div_mod_eq.symm
  intro i j l
  rw [Bool.eq_iff_iff, arCompat, A207937.allowed, decide_eq_true_eq, beq_iff_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    simp only [Nat.testBit_and, Nat.testBit_xor]
    by_cases hk : k < 7
    · let t : Fin 7 := ⟨k,hk⟩
      simpa only [bits, t] using (localRule _ _ _).mp (h t)
    · have zero (u : Fin 35) : (A207937.code u).testBit k = false :=
        Nat.testBit_lt_two_pow ((small u).trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [zero]
  · intro h t
    apply (localRule _ _ _).mpr
    simpa only [bits, Nat.testBit_and, Nat.testBit_xor] using congrArg (fun w : ℕ => w.testBit t.val) h

open OMA.S_oeis_a207937 PowerSeries

set_option maxHeartbeats 3000000 in
private lemma arr207937_gf
    (h : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) =
      (1260 + 4974*(n:ℚ) - 32165*(n:ℚ)^2 - 6041*(n:ℚ)^3 + 51940*(n:ℚ)^4 +
        21091*(n:ℚ)^5 + 2905*(n:ℚ)^6 + 136*(n:ℚ)^7) / 1260) :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1-X)^8 : PowerSeries ℚ) =
      X * (35 + 945*X + 157*X^2 - 1269*X^3 + 863*X^4 - 191*X^5 + 5*X^6 - X^7) := by
  let P (x : ℚ) := (1260 + 4974*x - 32165*x^2 - 6041*x^3 +
    51940*x^4 + 21091*x^5 + 2905*x^6 + 136*x^7)/1260
  let b (n : ℕ) : ℚ := if n < 1 then 0 else (a n : ℚ)
  have hb (n : ℕ) : b n = if n = 0 then 0 else P n := by
    cases n with
    | zero => simp [b]
    | succ n => simpa only [b, show ¬ n + 1 < 1 by omega, if_false, Nat.succ_ne_zero] using h (n+1) (by omega)
  let A := PowerSeries.mk b
  have L : A*(1-X)^8 = A - C 8*(A*X^1) + C 28*(A*X^2) - C 56*(A*X^3) +
      C 70*(A*X^4) - C 56*(A*X^5) + C 28*(A*X^6) - C 8*(A*X^7) + A*X^8 := by
    norm_num [map_ofNat]
    ring
  have R : X * (35 + 945*X + 157*X^2 - 1269*X^3 + 863*X^4 - 191*X^5 + 5*X^6 - X^7) =
      C (35:ℚ)*X^1 + C 945*X^2 + C 157*X^3 - C 1269*X^4 +
        C 863*X^5 - C 191*X^6 + C 5*X^7 - X^8 := by
    norm_num [map_ofNat]
    ring
  change A*(1-X)^8 = _
  rw [L, R]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk, coeff_X_pow, coeff_C]
  by_cases large : 9 ≤ n
  · simp (disch := omega) only [if_pos, if_neg, hb]
    dsimp only [P]
    push_cast [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_sub (by omega : 4 ≤ n), Nat.cast_sub (by omega : 5 ≤ n), Nat.cast_sub (by omega : 6 ≤ n), Nat.cast_sub (by omega : 7 ≤ n), Nat.cast_sub (by omega : 8 ≤ n)]
    ring
  · interval_cases n <;> norm_num [hb,P]

private lemma arr207937_poly
    (one : a 1 = 35)
    (counts : ∀ k : ℕ, a (k+2) = (↑(∑ t : Fin 8, k.choose t.val *
      (#[1225,7752,21478,32398,28746,15100,4380,544] : Array ℕ)[t.val]'(by simp)) : ℤ)) :
    ∀ n : ℕ, 1 ≤ n → (a n : ℚ) =
      (1260 + 4974*(n:ℚ) - 32165*(n:ℚ)^2 - 6041*(n:ℚ)^3 + 51940*(n:ℚ)^4 +
        21091*(n:ℚ)^5 + 2905*(n:ℚ)^6 + 136*(n:ℚ)^7) / 1260 := by
  rintro (_ | (_ | k)) hn
  · omega
  · norm_num [one]
  rw [counts]
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  change (((k.choose 0*1225 + (k.choose 1*7752 + (k.choose 2*21478 + (k.choose 3*32398 +
    (k.choose 4*28746 + (k.choose 5*15100 + (k.choose 6*4380 + k.choose 7*544))))))) : ℕ) : ℚ) = _
  have castChoose (j : ℕ) : (k.choose j : ℚ) = (k.descFactorial j : ℚ) / (j.factorial : ℚ) := by
    rw [eq_div_iff (by exact_mod_cast j.factorial_ne_zero), mul_comm]
    exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose k j).symm
  by_cases hk : 7 ≤ k
  · push_cast
    simp only [castChoose]
    norm_num [Nat.descFactorial, Nat.factorial]
    push_cast [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_sub (by omega : 2 ≤ k),
      Nat.cast_sub (by omega : 3 ≤ k), Nat.cast_sub (by omega : 4 ≤ k),
      Nat.cast_sub (by omega : 5 ≤ k), Nat.cast_sub (by omega : 6 ≤ k)]
    ring
  · interval_cases k <;> norm_num [Nat.choose]

theorem OMA.solution : type_of% @OMA.S_oeis_a207937.main := by
  obtain ⟨one, count⟩ := ar_count_compressed arRowEquiv A207937.allowed A207937.ext
    ar_allowed_table (fun _ _ => rfl) (fun _ _ _ => rfl)
  have poly := arr207937_poly one (fun k => (count k).trans
    (congrArg (fun m : ℕ => (m : ℤ)) (A207937.transfer_total k)))
  exact ⟨arr207937_gf poly, poly⟩
