import OMAStatements.S_oeis_a208377
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
The admissible width-six rows form a finite ordered set. The vertical
rule makes all rows after the first a weakly decreasing chain. The
transfer matrix for these chains is the identity plus a nilpotent
strict part. Its powers give the recurrence and generating function.
-/

namespace OMA.Oeis208377Rows

abbrev Row := Fin 6 → Fin 2

def RowGood (u : Row) : Prop :=
  ∀ j : Fin 4,
    (u ⟨j.val, by omega⟩, u ⟨j.val + 1, by omega⟩, u ⟨j.val + 2, by omega⟩) ≠ (0, 0, 0) ∧
    (u ⟨j.val, by omega⟩, u ⟨j.val + 1, by omega⟩, u ⟨j.val + 2, by omega⟩) ≠ (1, 1, 1)

instance (u : Row) : Decidable (RowGood u) := by
  unfold RowGood
  infer_instance

abbrev GoodRow := {u : Row // RowGood u}

end OMA.Oeis208377Rows

namespace OMA.Oeis208377Rows

open OMA.S_oeis_a208377
open scoped BigOperators

private theorem horizontal_indices {n : ℕ} (x : Fin n → Row) (i : Fin n) (j : Fin 4) :
    ((get x i.val j.val, get x i.val (j.val + 1), get x i.val (j.val + 2)) ≠ (0, 0, 0) ∧
      (get x i.val j.val, get x i.val (j.val + 1), get x i.val (j.val + 2)) ≠ (1, 1, 1)) ↔
    ((x i ⟨j.val, by omega⟩, x i ⟨j.val + 1, by omega⟩, x i ⟨j.val + 2, by omega⟩) ≠ (0, 0, 0) ∧
      (x i ⟨j.val, by omega⟩, x i ⟨j.val + 1, by omega⟩, x i ⟨j.val + 2, by omega⟩) ≠ (1, 1, 1)) := by
  have h₀ : j.val < 6 := by omega
  have h₁ : j.val + 1 < 6 := by omega
  have h₂ : j.val + 2 < 6 := by omega
  unfold S_oeis_a208377.get
  simp only [dif_pos (show i.val < n ∧ j.val < 6 from ⟨i.isLt, h₀⟩),
    dif_pos (show i.val < n ∧ j.val + 1 < 6 from ⟨i.isLt, h₁⟩),
    dif_pos (show i.val < n ∧ j.val + 2 < 6 from ⟨i.isLt, h₂⟩)]
  simp only [ne_eq, Prod.mk.injEq, Fin.ext_iff, Fin.val_zero, Fin.val_one]

private theorem horizontal_iff {n : ℕ} (x : Fin n → Row) :
    (∀ i < n, ∀ j < 6 - 2,
      (get x i j, get x i (j + 1), get x i (j + 2)) ≠ (0, 0, 0) ∧
      (get x i j, get x i (j + 1), get x i (j + 2)) ≠ (1, 1, 1)) ↔
    ∀ i : Fin n, RowGood (x i) := by
  constructor
  · intro h i j
    exact (horizontal_indices x i j).mp (h i.val i.isLt j.val j.isLt)
  · intro h i hi j hj
    exact (horizontal_indices x ⟨i, hi⟩ ⟨j, hj⟩).mpr (h ⟨i, hi⟩ ⟨j, hj⟩)

private theorem vertical_test : ∀ u v w : Fin 2,
    ((u.val, v.val, w.val) ≠ (0, 0, 1) ∧
      (u.val, v.val, w.val) ≠ (1, 0, 1)) ↔ w ≤ v := by decide

private theorem vertical_indices {k : ℕ} (x : Fin (k + 2) → Row) (i : Fin k) (j : Fin 6) :
    ((get x i.val j.val, get x (i.val + 1) j.val, get x (i.val + 2) j.val) ≠ (0, 0, 1) ∧
      (get x i.val j.val, get x (i.val + 1) j.val, get x (i.val + 2) j.val) ≠ (1, 0, 1)) ↔
    Fin.tail x i.succ j ≤ Fin.tail x i.castSucc j := by
  have h₀ : i.val < k + 2 := by omega
  have h₁ : i.val + 1 < k + 2 := by omega
  have h₂ : i.val + 2 < k + 2 := by omega
  unfold S_oeis_a208377.get
  simp only [dif_pos (show i.val < k + 2 ∧ j.val < 6 from ⟨h₀, j.isLt⟩),
    dif_pos (show i.val + 1 < k + 2 ∧ j.val < 6 from ⟨h₁, j.isLt⟩),
    dif_pos (show i.val + 2 < k + 2 ∧ j.val < 6 from ⟨h₂, j.isLt⟩)]
  exact vertical_test (x ⟨i.val, h₀⟩ j) (Fin.tail x i.castSucc j) (Fin.tail x i.succ j)

/-- The first row is free of vertical constraints. The remaining rows are
coordinatewise weakly decreasing. -/
theorem avoids_iff_rows {k : ℕ} (x : Fin (k + 2) → Row) :
    avoids x = true ↔ (∀ i : Fin (k + 2), RowGood (x i)) ∧
      ∀ i : Fin k, Fin.tail x i.succ ≤ Fin.tail x i.castSucc := by
  rw [avoids, decide_eq_true_eq, horizontal_iff]
  apply and_congr_right'
  constructor
  · intro h i j
    exact (vertical_indices x i j).mp (h i.val (by omega) j.val j.isLt)
  · intro h i hi j hj
    exact (vertical_indices x ⟨i, by omega⟩ ⟨j, hj⟩).mpr (h ⟨i, by omega⟩ ⟨j, hj⟩)

private theorem avoids_iff_one (x : Fin 1 → Row) :
    avoids x = true ↔ RowGood (x 0) := by
  rw [avoids, decide_eq_true_eq, horizontal_iff]
  simp

abbrev ValidArray (n : ℕ) := {x : Fin n → Row // avoids x = true}

abbrev WeakChain (k : ℕ) :=
  {f : Fin (k + 1) → GoodRow // ∀ i : Fin k, (f i.succ).val ≤ (f i.castSucc).val}

abbrev ChainFrom (k : ℕ) (u : GoodRow) := {f : WeakChain k // f.val 0 = u}

private def validEquiv (k : ℕ) : ValidArray (k + 2) ≃ GoodRow × WeakChain k where
  toFun x := by
    have h := (avoids_iff_rows x.val).mp x.property
    exact (⟨x.val 0, h.1 0⟩, ⟨fun i => ⟨Fin.tail x.val i, h.1 i.succ⟩, h.2⟩)
  invFun p := by
    let x : Fin (k + 2) → Row := Fin.cons p.1.val (fun i => (p.2.val i).val)
    refine ⟨x, (avoids_iff_rows x).mpr ⟨?_, ?_⟩⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [x, Fin.cons_zero] using p.1.property
      · simpa only [x, Fin.cons_succ] using (p.2.val j).property
    · simpa only [x, Fin.tail_cons] using p.2.property
  left_inv x := Subtype.ext (Fin.cons_self_tail x.val)
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact Fin.cons_zero (α := fun _ => Row) p.1.val (fun i => (p.2.val i).val)
    · apply Subtype.ext
      funext i
      apply Subtype.ext
      change Fin.tail (Fin.cons (α := fun _ => Row) p.1.val (fun j => (p.2.val j).val)) i = (p.2.val i).val
      rw [Fin.tail_cons]

private def validOneEquiv : ValidArray 1 ≃ GoodRow where
  toFun x := ⟨x.val 0, (avoids_iff_one x.val).mp x.property⟩
  invFun u := ⟨fun _ => u.val, (avoids_iff_one _).mpr u.property⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    rw [Subsingleton.elim i 0]
  right_inv _ := rfl

theorem a_eq_card_valid (n : ℕ) : a n = (Nat.card (ValidArray n) : ℤ) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

theorem a_one_eq_card_goodRow : a 1 = (Nat.card GoodRow : ℤ) := by
  rw [a_eq_card_valid, Nat.card_congr validOneEquiv]

/-- Counting valid arrays separates the first row from the descending chain. -/
theorem a_succ_succ_eq_card (k : ℕ) :
    a (k + 2) = (Nat.card GoodRow : ℤ) * (Nat.card (WeakChain k) : ℤ) := by
  rw [a_eq_card_valid, Nat.card_congr (validEquiv k), Nat.card_prod, Nat.cast_mul]

private def tailChain {k : ℕ} (f : WeakChain (k + 1)) : WeakChain k :=
  ⟨Fin.tail f.val, fun i => by
    simpa only [Fin.tail, Fin.succ_castSucc] using f.property i.succ⟩

private def consChain {k : ℕ} (u : GoodRow) (f : WeakChain k)
    (h : (f.val 0).val ≤ u.val) : WeakChain (k + 1) :=
  ⟨Fin.cons u f.val, fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.succ_zero_eq_one, Fin.castSucc_zero, Fin.cons_one, Fin.cons_zero] using h
    · simpa only [← Fin.succ_castSucc, Fin.cons_succ] using f.property j⟩

private def tagChain {k : ℕ} (u : GoodRow)
    (f : {f : WeakChain k // (f.val 0).val ≤ u.val}) :
    Σ v : GoodRow, {_g : ChainFrom k v // v.val ≤ u.val} :=
  ⟨f.val.val 0, ⟨⟨f.val, rfl⟩, f.property⟩⟩

private def headStepEquiv (k : ℕ) (u : GoodRow) :
    ChainFrom (k + 1) u ≃ Σ v : GoodRow, {_f : ChainFrom k v // v.val ≤ u.val} where
  toFun f := by
    refine tagChain u ⟨tailChain f.val, ?_⟩
    have h := f.val.property (0 : Fin (k + 1))
    simpa only [tailChain, Fin.tail, Fin.castSucc_zero, f.property] using h
  invFun q := by
    have h : (q.2.val.val.val 0).val ≤ u.val := by rw [q.2.val.property]; exact q.2.property
    refine ⟨consChain u q.2.val.val h, ?_⟩
    change Fin.cons (α := fun _ => GoodRow) u q.2.val.val.val 0 = u
    exact Fin.cons_zero _ _
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    change Fin.cons u (Fin.tail f.val.val) = f.val.val
    calc
      _ = Fin.cons (f.val.val 0) (Fin.tail f.val.val) :=
        congrArg (fun w => Fin.cons w (Fin.tail f.val.val)) f.property.symm
      _ = _ := Fin.cons_self_tail _
  right_inv q := by
    rcases q with ⟨v, ⟨⟨f, hf⟩, hv⟩⟩
    subst v
    have ht : tailChain (consChain u f hv) = f := by
      apply Subtype.ext
      change Fin.tail (Fin.cons (α := fun _ => GoodRow) u f.val) = f.val
      exact Fin.tail_cons (α := fun _ => GoodRow) u f.val
    have htail : ((tailChain (consChain u f hv)).val 0).val ≤ u.val := ht.symm ▸ hv
    change tagChain u ⟨tailChain (consChain u f hv), htail⟩ = tagChain u ⟨f, hv⟩
    exact congrArg (tagChain u) (Subtype.ext ht)

theorem card_chainFrom_zero (u : GoodRow) : Nat.card (ChainFrom 0 u) = 1 := by
  let elem : ChainFrom 0 u := ⟨⟨fun _ => u, fun i => Fin.elim0 i⟩, rfl⟩
  let _ : Unique (ChainFrom 0 u) := ⟨⟨elem⟩, fun f => by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    rw [Subsingleton.elim (α := Fin 1) i 0]
    exact f.property⟩
  exact Nat.card_unique

theorem card_chainFrom_succ (k : ℕ) (u : GoodRow) :
    Nat.card (ChainFrom (k + 1) u) =
      ∑ v : GoodRow, if ∀ i : Fin 6, v.val i ≤ u.val i then Nat.card (ChainFrom k v) else 0 := by
  classical
  rw [Nat.card_congr (headStepEquiv k u), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : ∀ i : Fin 6, v.val i ≤ u.val i
  · rw [if_pos h]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => h))
  · rw [if_neg h]
    let _ : IsEmpty {_f : ChainFrom k v // v.val ≤ u.val} := ⟨fun f => h f.property⟩
    exact Nat.card_of_isEmpty

theorem card_weakChain_eq_sum (k : ℕ) :
    Nat.card (WeakChain k) = ∑ u : GoodRow, Nat.card (ChainFrom k u) := by
  rw [← Nat.card_sigma]
  exact Nat.card_congr (Equiv.sigmaFiberEquiv (fun f : WeakChain k => f.val 0)).symm

theorem card_chainFrom_matrix (M : Matrix GoodRow GoodRow ℤ)
    (hM : ∀ u v, M u v = if ∀ i : Fin 6, v.val i ≤ u.val i then 1 else 0) (k : ℕ) (u : GoodRow) :
    (Nat.card (ChainFrom k u) : ℤ) = ∑ v : GoodRow, (M ^ k) u v := by
  classical
  induction k generalizing u with
  | zero =>
    rw [card_chainFrom_zero]
    simp [Matrix.one_apply]
  | succ k ih =>
    calc
      _ = ∑ v : GoodRow, ∑ w : GoodRow, M u v * (M ^ k) v w := by
        rw [card_chainFrom_succ]
        push_cast
        apply Finset.sum_congr rfl
        intro v _
        rw [← Finset.mul_sum, ← ih v, hM]
        split_ifs <;> simp
      _ = ∑ w : GoodRow, ∑ v : GoodRow, M u v * (M ^ k) v w := Finset.sum_comm
      _ = _ := by simp only [pow_succ', Matrix.mul_apply]

theorem a_succ_succ_matrix (M : Matrix GoodRow GoodRow ℤ)
    (hM : ∀ u v, M u v = if ∀ i : Fin 6, v.val i ≤ u.val i then 1 else 0) (k : ℕ) :
    a (k + 2) = (Nat.card GoodRow : ℤ) * ∑ u : GoodRow, ∑ v : GoodRow, (M ^ k) u v := by
  rw [a_succ_succ_eq_card, card_weakChain_eq_sum, Nat.cast_sum]
  simp_rw [card_chainFrom_matrix M hM]

end OMA.Oeis208377Rows

namespace OMA.Oeis208377Rows

open Finset

/-- Transitions that lower each coordinate weakly. -/
def weak : Matrix GoodRow GoodRow ℤ :=
  fun u v => if ∀ i, v.val i ≤ u.val i then 1 else 0

/-- Transitions that lower at least one coordinate strictly and never increase. -/
def strict : Matrix GoodRow GoodRow ℤ :=
  fun u v => if (∀ i, v.val i ≤ u.val i) ∧ v ≠ u then 1 else 0

theorem weak_eq_one_add_strict : weak = 1 + strict := by
  ext u v
  by_cases huv : u = v
  · subst v
    simp [weak, strict]
  · simp [weak, strict, huv, Ne.symm huv]

private def weight (u : GoodRow) : ℕ := ∑ i : Fin 6, (u.val i).val

private theorem triple_weight :
    ∀ a b c : Fin 2, (a,b,c) ≠ (0,0,0) → (a,b,c) ≠ (1,1,1) →
      1 ≤ a.val+b.val+c.val ∧ a.val+b.val+c.val ≤ 2 := by
  decide +kernel

private theorem weight_bounds (u : GoodRow) : 2 ≤ weight u ∧ weight u ≤ 4 := by
  have h₁ := u.property 0
  have h₂ := u.property 3
  have hb₁ := triple_weight _ _ _ h₁.1 h₁.2
  have hb₂ := triple_weight _ _ _ h₂.1 h₂.2
  change 1 ≤ (u.val 0).val + (u.val 1).val + (u.val 2).val ∧
    (u.val 0).val + (u.val 1).val + (u.val 2).val ≤ 2 at hb₁
  change 1 ≤ (u.val 3).val + (u.val 4).val + (u.val 5).val ∧
    (u.val 3).val + (u.val 4).val + (u.val 5).val ≤ 2 at hb₂
  have hw : weight u = (u.val 0).val + (u.val 1).val + (u.val 2).val +
      (u.val 3).val + (u.val 4).val + (u.val 5).val := by
    simp only [weight, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change (u.val 0).val + ((u.val 1).val + ((u.val 2).val + ((u.val 3).val +
      ((u.val 4).val + (u.val 5).val)))) = _
    omega
  omega

private theorem weight_lt_of_strict {u v : GoodRow}
    (h : (∀ i, v.val i ≤ u.val i) ∧ v ≠ u) : weight v < weight u := by
  have hn : ¬ ∀ i, v.val i = u.val i := fun hp => h.2 (Subtype.ext (funext hp))
  obtain ⟨i, hi⟩ := not_forall.mp hn
  exact sum_lt_sum (fun j _ => h.1 j)
    ⟨i, mem_univ _, lt_of_le_of_ne (h.1 i) (fun he => hi (Fin.ext he))⟩

theorem strict_cube : strict ^ 3 = 0 := by
  rw [show (3 : ℕ) = 2 + 1 by decide, pow_succ, pow_two]
  ext u w
  simp only [Matrix.mul_apply, Matrix.zero_apply, sum_mul]
  apply sum_eq_zero
  intro v _
  apply sum_eq_zero
  intro z _
  by_cases huz : (∀ i, z.val i ≤ u.val i) ∧ z ≠ u
  · by_cases hzv : (∀ i, v.val i ≤ z.val i) ∧ v ≠ z
    · by_cases hvw : (∀ i, w.val i ≤ v.val i) ∧ w ≠ v
      · have h₁ := weight_lt_of_strict huz
        have h₂ := weight_lt_of_strict hzv
        have h₃ := weight_lt_of_strict hvw
        have hu := (weight_bounds u).2
        have hw := (weight_bounds w).1
        omega
      · simp [strict, hvw]
    · simp [strict, hzv]
  · simp [strict, huz]

private def decodeRow (code : Fin 64) : Row :=
  fun i => if code.val.testBit i.val then 1 else 0

private def encodeRow (u : Row) : Fin 64 :=
  ⟨∑ j : Fin 6, (u j).val * 2 ^ j.val, by
    have h : (∑ j : Fin 6, (u j).val * 2 ^ j.val) ≤ ∑ j : Fin 6, 2 ^ j.val := by
      apply sum_le_sum
      intro j _
      simpa only [one_mul] using
        Nat.mul_le_mul_right (2 ^ j.val) (show (u j).val ≤ 1 from Nat.le_of_lt_succ (u j).isLt)
    exact h.trans_lt (by decide)⟩

private theorem decode_encode_explicit :
    ∀ a b c d e f : Fin 2,
      decodeRow (encodeRow ![a,b,c,d,e,f]) = ![a,b,c,d,e,f] := by
  decide +kernel

private theorem decode_encode (u : Row) : decodeRow (encodeRow u) = u := by
  have h : u = ![u 0,u 1,u 2,u 3,u 4,u 5] := by
    funext i
    fin_cases i <;> rfl
  conv =>
    lhs
    arg 1
    arg 1
    rw [h]
  exact (decode_encode_explicit _ _ _ _ _ _).trans h.symm

private theorem encode_decode :
    ∀ code : Fin 64, encodeRow (decodeRow code) = code := by
  decide +kernel

private def CodeGood := {c : Fin 64 // RowGood (decodeRow c)}

private instance : Fintype CodeGood :=
  inferInstanceAs (Fintype {c : Fin 64 // RowGood (decodeRow c)})

private def codeEquiv : CodeGood ≃ GoodRow where
  toFun c := ⟨decodeRow c.val, c.property⟩
  invFun u := ⟨encodeRow u.val, by rw [decode_encode]; exact u.property⟩
  left_inv c := Subtype.ext (encode_decode c.val)
  right_inv u := Subtype.ext (decode_encode u.val)

private theorem sum_reindex (f : GoodRow → ℤ) :
    (∑ u : GoodRow, f u) = ∑ c : CodeGood, f (codeEquiv c) :=
  (Equiv.sum_comp codeEquiv f).symm

theorem card_goodRow : Fintype.card GoodRow = 26 := by
  rw [← Fintype.card_congr codeEquiv]
  decide +kernel

theorem sum_strict : (∑ u : GoodRow, ∑ v : GoodRow, strict u v) = 54 := by
  simp_rw [sum_reindex]
  decide +kernel

private theorem sum_square_by_middle :
    (∑ u : GoodRow, ∑ w : GoodRow, (strict ^ 2) u w) =
      ∑ v : GoodRow, (∑ u : GoodRow, strict u v) * (∑ w : GoodRow, strict v w) := by
  simp only [pow_two, Matrix.mul_apply]
  calc
    _ = ∑ u : GoodRow, ∑ v : GoodRow, ∑ w : GoodRow, strict u v * strict v w := by
      apply sum_congr rfl
      intro u _
      rw [sum_comm]
    _ = ∑ v : GoodRow, ∑ u : GoodRow, ∑ w : GoodRow, strict u v * strict v w :=
      sum_comm
    _ = _ := by simp_rw [← mul_sum, ← sum_mul]

set_option maxRecDepth 5000 in
set_option maxHeartbeats 3000000 in
theorem sum_strict_sq : (∑ u : GoodRow, ∑ v : GoodRow, (strict ^ 2) u v) = 28 := by
  rw [sum_square_by_middle]
  simp_rw [sum_reindex]
  decide +kernel

private theorem choose_two_succ (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  rw [show (2 : ℕ) = 1 + 1 by decide, Nat.choose_succ_succ, Nat.choose_one_right, add_comm]

private theorem nsmul_mul_matrix (n : ℕ) (A B : Matrix GoodRow GoodRow ℤ) :
    (n • A) * B = n • (A * B) := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, add_mul, ih, succ_nsmul]

theorem weak_pow (n : ℕ) : weak ^ n = 1 + n • strict + n.choose 2 • strict ^ 2 := by
  have hc : strict ^ 2 * strict = 0 := by rw [← pow_succ]; exact strict_cube
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, weak_eq_one_add_strict, choose_two_succ]
    simp only [add_mul, mul_add, mul_one, one_mul, add_nsmul, succ_nsmul, nsmul_mul_matrix,
      ← pow_two strict, hc, nsmul_zero, add_zero]
    ac_rfl

private theorem nsmul_apply_exact (n : ℕ) (A : Matrix GoodRow GoodRow ℤ) (u v : GoodRow) :
    (n • A) u v = (n : ℤ) * A u v := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, Matrix.add_apply, ih, Nat.cast_succ, add_mul, one_mul]

theorem sum_weak_pow (n : ℕ) :
    (∑ u : GoodRow, ∑ v : GoodRow, (weak ^ n) u v) =
      26 + 54 * n + 28 * (n.choose 2 : ℤ) := by
  have hOne : (∑ u : GoodRow, ∑ v : GoodRow, (1 : Matrix GoodRow GoodRow ℤ) u v) = 26 := by
    simp [Matrix.one_apply, card_goodRow]
  rw [weak_pow]
  simp only [Matrix.add_apply, nsmul_apply_exact, sum_add_distrib, ← mul_sum, hOne, sum_strict,
    sum_strict_sq]
  rw [mul_comm (n : ℤ) 54, mul_comm (n.choose 2 : ℤ) 28]

end OMA.Oeis208377Rows

namespace OMA.Oeis208377Rows

private theorem choose_two_step (k : ℕ) :
    (((k + 1).choose 2 : ℕ) : ℤ) = (k.choose 2 : ℤ) + (k : ℤ) := by
  rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right, Nat.cast_add, add_comm]

theorem initial_and_recurrence (a : ℕ → ℤ) (hone : a 1 = 26)
    (h : ∀ k : ℕ, a (k + 2) = 26 * (26 + 54 * (k : ℤ) + 28 * (k.choose 2 : ℤ))) :
    a 1 = 26 ∧ a 2 = 676 ∧ a 3 = 2080 ∧ a 4 = 4212 ∧
      ∀ n : ℕ, 5 ≤ n →
        (a n : ℚ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  have h₂ : a 2 = 676 := by
    have heq := h 0
    simpa [Nat.choose] using heq
  have h₃ : a 3 = 2080 := by
    have heq := h 1
    simpa [Nat.choose] using heq
  have h₄ : a 4 = 4212 := by
    have heq := h 2
    simpa [Nat.choose] using heq
  refine ⟨hone, h₂, h₃, h₄, ?_⟩
  intro n hn
  have hInt : a n = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
    let k := n - 5
    have h₀ : n = (k + 3) + 2 := by dsimp [k]; omega
    have h₁ : n - 1 = (k + 2) + 2 := by dsimp [k]; omega
    have h₂ : n - 2 = (k + 1) + 2 := by dsimp [k]; omega
    have h₃ : n - 3 = k + 2 := by dsimp [k]; omega
    rw [h₃, h₂, h₁, h₀, h (k + 3), h (k + 2), h (k + 1), h k]
    simp only [choose_two_step, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring
  exact_mod_cast hInt

end OMA.Oeis208377Rows

namespace OMA.A208377Series

open PowerSeries

theorem series_of_recurrence (a : ℕ → ℤ) (h₁ : a 1 = 26) (h₂ : a 2 = 676)
    (h₃ : a 3 = 2080) (h₄ : a 4 = 4212)
    (hr : ∀ n : ℕ, 5 ≤ n → (a n : ℚ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 3 : PowerSeries ℚ) =
      26 * X * (1 + 23 * X + 5 * X ^ 2 - X ^ 3) := by
  let b := fun n : ℕ => if n < 1 then 0 else (a n : ℚ)
  let F := PowerSeries.mk b
  change F * _ = _
  have denom : (1 - X) ^ 3 = (1 - C 3 * X ^ 1 + C 3 * X ^ 2 - X ^ 3 : PowerSeries ℚ) := by
    simp only [map_ofNat]
    ring
  have numer : 26 * X * (1 + 23 * X + 5 * X ^ 2 - X ^ 3) =
      (C 26 * X ^ 1 + C 598 * X ^ 2 + C 130 * X ^ 3 - C 26 * X ^ 4 : PowerSeries ℚ) := by
    simp only [map_ofNat]
    ring
  rw [denom, numer]
  ext n
  simp only [mul_sub, mul_add, mul_one, ← mul_assoc F, map_sub, map_add,
    coeff_mul_X_pow', coeff_mul_C, F, coeff_mk]
  by_cases hn : 5 ≤ n
  · have hleft : ¬ n < 1 := by omega
    have h₁' : ¬ n - 1 < 1 := by omega
    have h₂' : ¬ n - 2 < 1 := by omega
    have h₃' : ¬ n - 3 < 1 := by omega
    have hn₁ : 1 ≤ n := by omega
    have hn₂ : 2 ≤ n := by omega
    have hn₃ : 3 ≤ n := by omega
    have hn₄ : 4 ≤ n := by omega
    have hshift : n - 1 ≠ 0 ∧ n - 2 ≠ 0 ∧ n - 3 ≠ 0 ∧ n - 4 ≠ 0 := by omega
    simp only [hn₁, hn₂, hn₃, hn₄, if_true, coeff_C,
      hshift.1, hshift.2.1, hshift.2.2.1, hshift.2.2.2, if_false, b, hleft, h₁', h₂', h₃']
    linarith only [hr n hn]
  · interval_cases n <;> norm_num [b, h₁, h₂, h₃, h₄, coeff_C]

end OMA.A208377Series

namespace OMA.Oeis208377Rows

open OMA.S_oeis_a208377
open PowerSeries

private theorem a_closed (k : ℕ) :
    a (k + 2) = 26 * (26 + 54 * (k : ℤ) + 28 * (k.choose 2 : ℤ)) := by
  rw [a_succ_succ_matrix weak (fun _ _ => rfl),
    Nat.card_eq_fintype_card, card_goodRow, sum_weak_pow]
  norm_num

theorem full_result :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 3 : PowerSeries ℚ) =
      26 * X * (1 + 23 * X + 5 * X ^ 2 - X ^ 3)) ∧
    (∀ n : ℕ, 5 ≤ n → (a n : ℚ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) := by
  have ha : a 1 = 26 := by
    rw [a_one_eq_card_goodRow, Nat.card_eq_fintype_card, card_goodRow]
    norm_num
  obtain ⟨h₁, h₂, h₃, h₄, hr⟩ := initial_and_recurrence a ha a_closed
  exact ⟨OMA.A208377Series.series_of_recurrence a h₁ h₂ h₃ h₄ hr, hr⟩

end OMA.Oeis208377Rows

theorem OMA.solution : type_of% @OMA.S_oeis_a208377.main :=
  OMA.Oeis208377Rows.full_result
