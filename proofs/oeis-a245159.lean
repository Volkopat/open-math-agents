import OMAStatements.S_oeis_a245159
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OMA.A245159Counting

open OMA.S_oeis_a245159
open Finset

private abbrev Marks := Fin 4 → Bool
private abbrev State := Fin 6 × Marks

private def start : State := (0, fun _ => false)

private def advance (s : State) (b : Fin 5) : State :=
  (⟨max s.1.val (b.val + 1), by have := s.1.isLt; have := b.isLt; omega⟩,
    fun v => decide (v.val < b.val ∨ (s.2 v = true ∧ b.val ≠ v.val)))

private def occurs {n : ℕ} (v : Fin 4) (w : Fin n → Fin 5) : Prop :=
  ∃ i : Fin n, (w i).val = v.val

private def leftOK {n : ℕ} (seen : ℕ) (w : Fin n → Fin 5) : Prop :=
  ∀ i : Fin n, ∀ v : Fin 4, v.val < (w i).val →
    v.val < seen ∨ ∃ j : Fin n, j < i ∧ (w j).val = v.val

private def rightOK {n : ℕ} (w : Fin n → Fin 5) : Prop :=
  ∀ i : Fin n, ∀ v : Fin 4, v.val < (w i).val →
    ∃ j : Fin n, i < j ∧ (w j).val = v.val

private def needed {n : ℕ} (marks : Marks) (w : Fin n → Fin 5) : Prop :=
  ∀ v : Fin 4, marks v = true → occurs v w

private def good {n : ℕ} (s : State) (w : Fin n → Fin 5) : Prop :=
  leftOK s.1.val w ∧ rightOK w ∧ needed s.2 w

private instance {n : ℕ} (s : State) (w : Fin n → Fin 5) : Decidable (good s w) := by
  unfold good leftOK rightOK needed occurs
  infer_instance

private lemma occurs_cons {n : ℕ} (b : Fin 5) (w : Fin n → Fin 5) (v : Fin 4) :
    occurs v (Fin.cons b w) ↔ b.val = v.val ∨ occurs v w := by
  simp only [occurs, Fin.exists_fin_succ, Fin.cons_zero, Fin.cons_succ]

private lemma earlier_cons {n : ℕ} (b : Fin 5) (w : Fin n → Fin 5) (i : Fin n) (v : Fin 4) :
    (∃ j : Fin (n + 1), j < i.succ ∧ (Fin.cons (α := fun _ => Fin 5) b w j).val = v.val) ↔
      b.val = v.val ∨ ∃ j : Fin n, j < i ∧ (w j).val = v.val := by
  simp [Fin.exists_fin_succ]

private lemma left_cons {n : ℕ} (seen : ℕ) (b : Fin 5) (w : Fin n → Fin 5) :
    leftOK seen (Fin.cons b w) ↔ b.val ≤ seen ∧ leftOK (max seen (b.val + 1)) w := by
  have allowed : (∀ v : Fin 4, v.val < b.val → v.val < seen) ↔ b.val ≤ seen := by
    constructor
    · intro h
      by_contra! hb
      let v : Fin 4 := ⟨seen, by have := b.isLt; omega⟩
      exact (Nat.lt_irrefl seen) (h v hb)
    · intro h v hv
      exact lt_of_lt_of_le hv h
  unfold leftOK
  rw [Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.not_lt_zero, false_and, exists_false,
    or_false, earlier_cons, allowed]
  refine and_congr_right fun hb => ?_
  have seen_iff (v : Fin 4) : v.val < max seen (b.val + 1) ↔ v.val < seen ∨ b.val = v.val := by
    omega
  simp only [seen_iff, or_assoc]

private lemma right_cons {n : ℕ} (b : Fin 5) (w : Fin n → Fin 5) :
    rightOK (Fin.cons b w) ↔ rightOK w ∧ (∀ v : Fin 4, v.val < b.val → occurs v w) := by
  unfold rightOK occurs
  rw [Fin.forall_fin_succ, and_comm]
  simp [Fin.exists_fin_succ]

private lemma good_cons {n : ℕ} (s : State) (b : Fin 5) (w : Fin n → Fin 5) :
    good s (Fin.cons b w) ↔ b.val ≤ s.1.val ∧ good (advance s b) w := by
  unfold good
  rw [left_cons, right_cons]
  constructor
  · rintro ⟨⟨hb, hl⟩, ⟨hr, hhead⟩, hmarks⟩
    refine ⟨hb, hl, hr, ?_⟩
    intro v hv
    change decide (v.val < b.val ∨ (s.2 v = true ∧ b.val ≠ v.val)) = true at hv
    rcases of_decide_eq_true hv with h | ⟨hv, hbv⟩
    · exact hhead v h
    · exact ((occurs_cons b w v).mp (hmarks v hv)).resolve_left hbv
  · rintro ⟨hb, hl, hr, hmarks⟩
    refine ⟨⟨hb, hl⟩, ⟨hr, ?_⟩, ?_⟩
    · intro v hv
      exact hmarks v (by simp [advance, hv])
    · intro v hv
      rw [occurs_cons]
      by_cases he : b.val = v.val
      · exact Or.inl he
      · exact Or.inr (hmarks v (by simp [advance, hv, he]))

private lemma good_start {n : ℕ} (w : Fin n → Fin 5) :
    good start w ↔ InOrderBothEnds w := by
  constructor
  · rintro ⟨hl, hr, _⟩ i v hv
    let u : Fin 4 := ⟨v.val, by have := (w i).isLt; change v.val < (w i).val at hv; omega⟩
    have hleft := (hl i u hv).resolve_left (Nat.not_lt_zero _)
    obtain ⟨j, hj, hval⟩ := hleft
    obtain ⟨k, hk, hkval⟩ := hr i u hv
    exact ⟨⟨j, hj, Fin.ext hval⟩, ⟨k, hk, Fin.ext hkval⟩⟩
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i v hv
      let u : Fin 5 := ⟨v.val, by have := v.isLt; omega⟩
      obtain ⟨j, hj, he⟩ := (h i u hv).1
      exact Or.inr ⟨j, hj, congrArg Fin.val he⟩
    · intro i v hv
      let u : Fin 5 := ⟨v.val, by have := v.isLt; omega⟩
      obtain ⟨j, hj, he⟩ := (h i u hv).2
      exact ⟨j, hj, congrArg Fin.val he⟩
    · simp [needed, start]

private def G (n : ℕ) (s : State) : ℤ :=
  ∑ w : Fin n → Fin 5, if good s w then 1 else 0

private def T (f : State → ℤ) (s : State) : ℤ :=
  ∑ b : Fin 5, if b.val ≤ s.1.val then f (advance s b) else 0

private lemma G_succ (n : ℕ) (s : State) : G (n + 1) s = T (G n) s := by
  unfold G T
  calc
    _ = ∑ p : Fin 5 × (Fin n → Fin 5), if good s (Fin.cons p.1 p.2) then (1 : ℤ) else 0 := by
      symm
      apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 5))
      intro p
      have e : (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 5)) p = Fin.cons p.1 p.2 := rfl
      rw [e]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro b _
      simp only [good_cons]
      by_cases h : b.val ≤ s.1.val <;> simp [h]

private lemma G_start (n : ℕ) : G n start = (a n : ℤ) := by
  unfold G a
  rw [← Finset.sum_filter]
  simp only [good_start, Finset.sum_const, nsmul_eq_mul, Int.mul_one]

private lemma G_zero (s : State) :
    G 0 s = if ∀ v, s.2 v = false then 1 else 0 := by
  have h (w : Fin 0 → Fin 5) : good s w ↔ ∀ v, s.2 v = false := by
    simp [good, leftOK, rightOK, needed, occurs]
  simp [G, h]

private def slot (s : State) : ℕ :=
  16 * s.1.val + (if s.2 0 then 1 else 0) + (if s.2 1 then 2 else 0) +
    (if s.2 2 then 4 else 0) + (if s.2 3 then 8 else 0)

/-- Counts after zero through nine steps, indexed by the number of introduced symbols
and the four pending obligation bits. -/
private def rows : Array (Array ℤ) := #[
  #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[2, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5, 4, 4, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5, 4, 4, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5, 4, 4, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5, 4, 4, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  #[4, 4, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 8, 8, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 14, 14, 13, 13, 6, 6, 6, 6, 0, 0, 0, 0, 0, 0, 0, 0, 15, 15, 14, 14, 7, 7, 7, 7, 1, 1, 1, 1, 1, 1, 1, 1, 15, 15, 14, 14, 7, 7, 7, 7, 1, 1, 1, 1, 1, 1, 1, 1, 15, 15, 14, 14, 7, 7, 7, 7, 1, 1, 1, 1, 1, 1, 1, 1],
  #[9, 9, 8, 8, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 23, 23, 22, 22, 7, 7, 7, 7, 0, 0, 0, 0, 0, 0, 0, 0, 42, 42, 41, 41, 26, 26, 26, 26, 1, 1, 1, 1, 1, 1, 1, 1, 51, 51, 50, 50, 35, 35, 35, 35, 10, 10, 10, 10, 10, 10, 10, 10, 52, 52, 51, 51, 36, 36, 36, 36, 11, 11, 11, 11, 11, 11, 11, 11, 52, 52, 51, 51, 36, 36, 36, 36, 11, 11, 11, 11, 11, 11, 11, 11],
  #[23, 23, 22, 22, 7, 7, 7, 7, 0, 0, 0, 0, 0, 0, 0, 0, 65, 65, 64, 64, 33, 33, 33, 33, 1, 1, 1, 1, 1, 1, 1, 1, 134, 134, 133, 133, 102, 102, 102, 102, 12, 12, 12, 12, 12, 12, 12, 12, 188, 188, 187, 187, 156, 156, 156, 156, 66, 66, 66, 66, 66, 66, 66, 66, 202, 202, 201, 201, 170, 170, 170, 170, 80, 80, 80, 80, 80, 80, 80, 80, 202, 202, 201, 201, 170, 170, 170, 170, 80, 80, 80, 80, 80, 80, 80, 80],
  #[65, 65, 64, 64, 33, 33, 33, 33, 1, 1, 1, 1, 1, 1, 1, 1, 199, 199, 198, 198, 135, 135, 135, 135, 13, 13, 13, 13, 13, 13, 13, 13, 455, 455, 454, 454, 391, 391, 391, 391, 90, 90, 90, 90, 90, 90, 90, 90, 733, 733, 732, 732, 669, 669, 669, 669, 368, 368, 368, 368, 368, 368, 368, 368, 855, 855, 854, 854, 791, 791, 791, 791, 490, 490, 490, 490, 490, 490, 490, 490, 855, 855, 854, 854, 791, 791, 791, 791, 490, 490, 490, 490, 490, 490, 490, 490],
  #[199, 199, 198, 198, 135, 135, 135, 135, 13, 13, 13, 13, 13, 13, 13, 13, 654, 654, 653, 653, 526, 526, 526, 526, 103, 103, 103, 103, 103, 103, 103, 103, 1642, 1642, 1641, 1641, 1514, 1514, 1514, 1514, 548, 548, 548, 548, 548, 548, 548, 548, 2989, 2989, 2988, 2988, 2861, 2861, 2861, 2861, 1895, 1895, 1895, 1895, 1895, 1895, 1895, 1895, 3845, 3845, 3844, 3844, 3717, 3717, 3717, 3717, 2751, 2751, 2751, 2751, 2751, 2751, 2751, 2751, 3845, 3845, 3844, 3844, 3717, 3717, 3717, 3717, 2751, 2751, 2751, 2751, 2751, 2751, 2751, 2751],
  #[654, 654, 653, 653, 526, 526, 526, 526, 103, 103, 103, 103, 103, 103, 103, 103, 2296, 2296, 2295, 2295, 2040, 2040, 2040, 2040, 651, 651, 651, 651, 651, 651, 651, 651, 6272, 6272, 6271, 6271, 6016, 6016, 6016, 6016, 2991, 2991, 2991, 2991, 2991, 2991, 2991, 2991, 12683, 12683, 12682, 12682, 12427, 12427, 12427, 12427, 9402, 9402, 9402, 9402, 9402, 9402, 9402, 9402, 18002, 18002, 18001, 18001, 17746, 17746, 17746, 17746, 14721, 14721, 14721, 14721, 14721, 14721, 14721, 14721, 18002, 18002, 18001, 18001, 17746, 17746, 17746, 17746, 14721, 14721, 14721, 14721, 14721, 14721, 14721, 14721]
 ]


private def row (k : Fin 10) (s : State) : ℤ := (rows.getD k.val #[]).getD (slot s) 0

set_option maxHeartbeats 3000000 in
private lemma row_zero : ∀ s : State,
    row 0 s = if ∀ v, s.2 v = false then 1 else 0 := by
  decide +kernel

set_option maxHeartbeats 6000000 in
private lemma row_step (k : Fin 9) : ∀ s : State,
    row k.succ s = T (row k.castSucc) s := by
  fin_cases k <;> decide +kernel

private lemma row_eq (n : ℕ) (hn : n < 10) (s : State) : G n s = row ⟨n, hn⟩ s := by
  induction n generalizing s with
  | zero => exact (G_zero s).trans (row_zero s).symm
  | succ n ih =>
    let k : Fin 9 := ⟨n, by omega⟩
    have eq : G n = row k.castSucc := funext fun t => ih (by omega) t
    rw [G_succ, eq]
    exact (row_step k s).symm

private def residual (n : ℕ) (s : State) : ℤ :=
  G (n+9) s - 17 * G (n+8) s + 118 * G (n+7) s - 434 * G (n+6) s +
    913 * G (n+5) s - 1097 * G (n+4) s + 696 * G (n+3) s - 180 * G (n+2) s

set_option maxHeartbeats 3000000 in
private lemma row_residual : ∀ s : State,
    row 9 s - 17 * row 8 s + 118 * row 7 s - 434 * row 6 s +
      913 * row 5 s - 1097 * row 4 s + 696 * row 3 s - 180 * row 2 s = 0 := by
  decide +kernel

private lemma residual_step (n : ℕ) (s : State) : residual (n+1) s = T (residual n) s := by
  unfold residual
  simp only [Nat.add_right_comm n 1]
  rw [G_succ (n+9), G_succ (n+8), G_succ (n+7), G_succ (n+6), G_succ (n+5),
    G_succ (n+4), G_succ (n+3), G_succ (n+2)]
  simp only [T, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : b.val ≤ s.1.val <;> simp [h]

private lemma residual_zero (n : ℕ) (s : State) : residual n s = 0 := by
  induction n generalizing s with
  | zero =>
    unfold residual
    simp only [Nat.zero_add]
    rw [row_eq 9 (by decide), row_eq 8 (by decide), row_eq 7 (by decide),
      row_eq 6 (by decide), row_eq 5 (by decide), row_eq 4 (by decide),
      row_eq 3 (by decide), row_eq 2 (by decide)]
    exact row_residual s
  | succ n ih =>
    rw [residual_step]
    simp [T, ih]

theorem count_initial (k : Fin 9) :
    (a k.val : ℤ) = ![1, 1, 1, 2, 4, 9, 23, 65, 199] k := by
  rw [← G_start, row_eq _ (by have := k.isLt; omega)]
  fin_cases k <;> decide

theorem count_recurrence (n : ℕ) :
    (a (n+9) : ℤ) = 17*a (n+8) - 118*a (n+7) + 434*a (n+6) - 913*a (n+5) +
      1097*a (n+4) - 696*a (n+3) + 180*a (n+2) := by
  have h := residual_zero n start
  simp only [residual, G_start] at h
  omega

end OMA.A245159Counting

namespace A245159Algebra

open PowerSeries

theorem gf_from_recur (f : ℕ → ℚ) (h0 : f 0 = 0) (h1 : f 1 = 1) (h2 : f 2 = 1)
    (h3 : f 3 = 2) (h4 : f 4 = 4) (h5 : f 5 = 9) (h6 : f 6 = 23) (h7 : f 7 = 65)
    (h8 : f 8 = 199)
    (hr : ∀ n, f (n + 9) = 17 * f (n + 8) - 118 * f (n + 7) + 434 * f (n + 6) -
      913 * f (n + 5) + 1097 * f (n + 4) - 696 * f (n + 3) + 180 * f (n + 2)) :
    mk f * ((1 - X) ^ 2 * (1 - 2 * X) ^ 2 * (1 - 3 * X) ^ 2 * (1 - 5 * X)) =
      X * (1 - 16 * X + 103 * X ^ 2 - 346 * X ^ 3 + 656 * X ^ 4 - 710 * X ^ 5 +
        425 * X ^ 6 - 124 * X ^ 7) := by
  set F := mk f
  have denominator : F * ((1 - X) ^ 2 * (1 - 2 * X) ^ 2 * (1 - 3 * X) ^ 2 * (1 - 5 * X)) =
      F - C (17 : ℚ) * (X ^ 1 * F) + C (118 : ℚ) * (X ^ 2 * F) -
        C (434 : ℚ) * (X ^ 3 * F) + C (913 : ℚ) * (X ^ 4 * F) -
        C (1097 : ℚ) * (X ^ 5 * F) + C (696 : ℚ) * (X ^ 6 * F) -
        C (180 : ℚ) * (X ^ 7 * F) := by
    simp only [map_ofNat]
    ring
  have numerator : (X * (1 - 16 * X + 103 * X ^ 2 - 346 * X ^ 3 + 656 * X ^ 4 -
      710 * X ^ 5 + 425 * X ^ 6 - 124 * X ^ 7) : PowerSeries ℚ) =
      X ^ 1 - C (16 : ℚ) * X ^ 2 + C (103 : ℚ) * X ^ 3 - C (346 : ℚ) * X ^ 4 +
        C (656 : ℚ) * X ^ 5 - C (710 : ℚ) * X ^ 6 + C (425 : ℚ) * X ^ 7 -
        C (124 : ℚ) * X ^ 8 := by
    simp only [map_ofNat]
    ring
  rw [denominator, numerator]
  ext n
  simp only [F, map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
  rcases Nat.lt_or_ge n 9 with h | h
  · interval_cases n <;> norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  · have recurrence := hr (n - 9)
    have shift (k : ℕ) (hk : k ≤ 9) : n - 9 + k = n - (9 - k) := by omega
    simp (disch := omega) only [shift] at recurrence
    norm_num at recurrence
    simp (disch := omega) only [if_pos, if_neg, mul_zero, add_zero, sub_zero]
    linear_combination recurrence

end A245159Algebra

namespace A245159Closed

open OMA.S_oeis_a245159 PowerSeries

private def closed (n : ℕ) : ℚ :=
  if n = 0 then 0 else if n = 1 then 1 else
    (-3375 - 525 * 2 ^ (4 + n) - 1300 * 3 ^ n + 3 * 5 ^ n
      + 100 * (297 + 9 * 2 ^ (2 + n) + 2 * 3 ^ n) * n) / 43200

private noncomputable def den : PowerSeries ℚ :=
  (1 - X) ^ 2 * (1 - 2 * X) ^ 2 * (1 - 3 * X) ^ 2 * (1 - 5 * X)

private noncomputable def num : PowerSeries ℚ :=
  X * (1 - 16 * X + 103 * X ^ 2 - 346 * X ^ 3 + 656 * X ^ 4 - 710 * X ^ 5 +
    425 * X ^ 6 - 124 * X ^ 7)

private lemma closed_gf : mk closed * den = num := by
  have hmul : mk closed * den =
      mk closed - C 17 * (mk closed * X ^ 1) + C 118 * (mk closed * X ^ 2) -
      C 434 * (mk closed * X ^ 3) + C 913 * (mk closed * X ^ 4) -
      C 1097 * (mk closed * X ^ 5) + C 696 * (mk closed * X ^ 6) -
      C 180 * (mk closed * X ^ 7) := by
    simp only [den, map_ofNat]
    ring
  have hnum : num =
      X ^ 1 - C 16 * X ^ 2 + C 103 * X ^ 3 - C 346 * X ^ 4 +
      C 656 * X ^ 5 - C 710 * X ^ 6 + C 425 * X ^ 7 - C 124 * X ^ 8 := by
    simp only [num, map_ofNat]
    ring
  rw [hmul, hnum]
  apply PowerSeries.ext
  intro n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_mk]
  by_cases h : n < 9
  · interval_cases n <;> norm_num [closed]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 9 ≤ n by omega)
    rw [Nat.add_comm 9 k]
    simp (disch := omega) [closed, Nat.add_sub_assoc, pow_add]
    ring

lemma closed_from_gf
    (h : mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - X) ^ 2 * (1 - 2 * X) ^ 2 * (1 - 3 * X) ^ 2 * (1 - 5 * X)) =
      X * (1 - 16 * X + 103 * X ^ 2 - 346 * X ^ 3 + 656 * X ^ 4 - 710 * X ^ 5 +
        425 * X ^ 6 - 124 * X ^ 7)) :
    ∀ n : ℕ, 1 < n →
      (a n : ℚ) = (-3375 - 525 * 2 ^ (4 + n) - 1300 * 3 ^ n + 3 * 5 ^ n
        + 100 * (297 + 9 * 2 ^ (2 + n) + 2 * 3 ^ n) * n) / 43200 := by
  change mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * den = num at h
  have hden : den ≠ 0 := by
    intro hd
    simpa [den] using congrArg (constantCoeff (R := ℚ)) hd
  have he := mul_right_cancel₀ hden (h.trans closed_gf.symm)
  intro n hn
  simpa [closed, show n ≠ 0 by omega, show n ≠ 1 by omega] using congrArg (coeff n) he

end A245159Closed

open OMA.S_oeis_a245159 OMA.A245159Counting in
theorem OMA.solution : type_of% @OMA.S_oeis_a245159.main := by
  let f : ℕ → ℚ := fun n => if n = 0 then 0 else a n
  have base (k : Fin 9) (hk : k.val ≠ 0) :
      f k.val = ((![1, 1, 1, 2, 4, 9, 23, 65, 199] k : ℤ) : ℚ) := by
    simp only [f, if_neg hk]
    exact_mod_cast count_initial k
  have hr (n : ℕ) :
      f (n + 9) = 17 * f (n + 8) - 118 * f (n + 7) + 434 * f (n + 6) -
        913 * f (n + 5) + 1097 * f (n + 4) - 696 * f (n + 3) + 180 * f (n + 2) := by
    have h := congrArg (Int.cast : ℤ → ℚ) (count_recurrence n)
    push_cast at h
    simpa (disch := omega) only [f, if_neg] using h
  have hgf := A245159Algebra.gf_from_recur f (by simp [f])
    (base 1 (by decide)) (base 2 (by decide)) (base 3 (by decide))
    (base 4 (by decide)) (base 5 (by decide)) (base 6 (by decide))
    (base 7 (by decide)) (base 8 (by decide)) hr
  exact ⟨hgf, A245159Closed.closed_from_gf hgf⟩
