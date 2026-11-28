import OMAStatements.S_oeis_a208141
import Mathlib

namespace OMA.Arrays208141

open OMA.S_oeis_a208141
open PowerSeries

private abbrev Row := Fin 7 → Fin 2

private def legal (r : Row) : Prop := ∀ j : Fin 5,
  let t := ((r ⟨j, by omega⟩).val, (r ⟨j+1, by omega⟩).val, (r ⟨j+2, by omega⟩).val)
  t ≠ (0,0,1) ∧ t ≠ (0,1,1)

private instance (r : Row) : Decidable (legal r) := by unfold legal; infer_instance

private def good {n : ℕ} (u : Row) (x : Fin n → Row) : Prop :=
  (∀ i, legal (x i)) ∧ (∀ i, x i ≤ u) ∧ Antitone x

private def high : Row := fun _ => 1

private theorem le_high (r : Row) : r ≤ high := fun j => by
  change r j ≤ (1 : Fin 2)
  omega

private theorem bits (a b c : Fin 2) :
    (((a.val,b.val,c.val) ≠ (0,0,1) ∧ (a.val,b.val,c.val) ≠ (1,0,1)) ↔ c ≤ b) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

private theorem horizontal {n : ℕ} (x : Fin n → Row) :
    (∀ i < n, ∀ j < 7-2,
      (get x i j, get x i (j+1), get x i (j+2)) ≠ (0,0,1) ∧
      (get x i j, get x i (j+1), get x i (j+2)) ≠ (0,1,1)) ↔ ∀ i, legal (x i) := by
  constructor
  · intro h i j
    simpa [OMA.S_oeis_a208141.get, i.isLt, show j.val < 7 by omega, show j.val+1 < 7 by omega,
      show j.val+2 < 7 by omega] using h i i.isLt j j.isLt
  · intro h i hi j hj
    simpa [OMA.S_oeis_a208141.get, hi, show j < 7 by omega, show j+1 < 7 by omega, show j+2 < 7 by omega]
      using h ⟨i,hi⟩ ⟨j,hj⟩

private theorem vertical {n : ℕ} (x : Fin (n+1) → Row) :
    (∀ i < n+1-2, ∀ j < 7,
      (get x i j, get x (i+1) j, get x (i+2) j) ≠ (0,0,1) ∧
      (get x i j, get x (i+1) j, get x (i+2) j) ≠ (1,0,1)) ↔
    Antitone (fun i : Fin n => x i.succ) := by
  cases n with
  | zero => simp [Antitone]
  | succ n =>
    rw [Fin.antitone_iff_succ_le]
    constructor
    · intro h i j
      change x ⟨i.val+2,by omega⟩ j ≤ x ⟨i.val+1,by omega⟩ j
      apply (bits (x ⟨i,by omega⟩ j) _ _).mp
      simpa [OMA.S_oeis_a208141.get, j.isLt, show i.val < n+1+1 by omega,
        show i.val+1 < n+1+1 by omega, show i.val+2 < n+1+1 by omega]
        using h i (by omega) j j.isLt
    · intro h i hi j hj
      have hh := (bits (x ⟨i,by omega⟩ ⟨j,hj⟩) _ _).mpr (h ⟨i,by omega⟩ ⟨j,hj⟩)
      simpa [OMA.S_oeis_a208141.get, hj, show i < n+1+1 by omega, show i+1 < n+1+1 by omega,
        show i+2 < n+1+1 by omega] using hh

private theorem array_iff {n : ℕ} (x : Fin (n+1) → Row) :
    avoids x = true ↔ legal (x 0) ∧ good high (fun i => x i.succ) := by
  simp only [avoids, decide_eq_true_eq, horizontal, vertical, good, Fin.forall_fin_succ]
  exact ⟨fun ⟨⟨a,b⟩,c⟩ => ⟨a,b,fun i => le_high _,c⟩, fun ⟨a,b,_,c⟩ => ⟨⟨a,b⟩,c⟩⟩

private theorem split_good {n : ℕ} (u : Row) (x : Fin (n+1) → Row) :
    good u x ↔ (legal (x 0) ∧ x 0 ≤ u) ∧ good (x 0) (fun i => x i.succ) := by
  constructor
  · intro ⟨hl,hb,ha⟩
    exact ⟨⟨hl 0,hb 0⟩,fun i => hl _,fun i => ha (Fin.zero_le _),
      fun i j hij => ha (Fin.succ_le_succ_iff.mpr hij)⟩
  · intro ⟨⟨h0,hu⟩,hl,hb,ha⟩
    refine ⟨Fin.forall_fin_succ.mpr ⟨h0,hl⟩, Fin.forall_fin_succ.mpr
      ⟨hu,fun i => (hb i).trans hu⟩,?_⟩
    rw [Fin.antitone_iff_succ_le]
    intro i
    cases n with
    | zero => exact Fin.elim0 i
    | succ n => exact Fin.cases (hb 0) (fun j => ha (Fin.castSucc_le_succ j)) i


private abbrev Chain (n : ℕ) (u : Row) := {x : Fin n → Row // good u x}

private noncomputable instance (n : ℕ) (u : Row) : Fintype (Chain n u) :=
  Fintype.ofFinite _

private def splitChain (n : ℕ) (u : Row) :
    Chain (n+1) u ≃ (Σ r : {r : Row // legal r ∧ r ≤ u}, Chain n r.val) where
  toFun x :=
    let h := (split_good u x.val).mp x.property
    ⟨⟨x.val 0,h.1⟩, ⟨fun i => x.val i.succ,h.2⟩⟩
  invFun y := ⟨Fin.cons y.1.val y.2.val, (split_good _ _).mpr (by
    simpa only [Fin.cons_zero,Fin.cons_succ] using And.intro y.1.property y.2.property)⟩
  left_inv x := Subtype.ext (Fin.cons_self_tail _)
  right_inv y := by rcases y with ⟨⟨r,hr⟩,⟨x,hx⟩⟩; rfl

private def splitArray (n : ℕ) :
    {x : Fin (n+1) → Row // avoids x = true} ≃ {r : Row // legal r} × Chain n high where
  toFun x :=
    let h := (array_iff x.val).mp x.property
    (⟨x.val 0,h.1⟩,⟨fun i => x.val i.succ,h.2⟩)
  invFun y := ⟨Fin.cons y.1.val y.2.val, (array_iff _).mpr (by
    simpa only [Fin.cons_zero,Fin.cons_succ] using And.intro y.1.property y.2.property)⟩
  left_inv x := Subtype.ext (Fin.cons_self_tail _)
  right_inv y := by rcases y with ⟨⟨r,hr⟩,⟨x,hx⟩⟩; rfl

private noncomputable def v (n : ℕ) (u : Row) : ℤ := Fintype.card (Chain n u)

private instance (r u : Row) : Decidable (r ≤ u) :=
  inferInstanceAs (Decidable (∀ j, r j ≤ u j))

private def step (f : Row → ℤ) (u : Row) : ℤ := ∑ r : {r : Row // legal r ∧ r ≤ u}, f r.val

private theorem succ_v (n : ℕ) : v (n+1) = step (v n) := by
  funext u
  simp [v,step,Fintype.card_congr (splitChain n u),Fintype.card_sigma]

private theorem zero_v : v 0 = fun _ => 1 := by
  funext u
  have : Unique (Chain 0 u) :=
    { default := ⟨Fin.elim0, fun i => i.elim0,fun i => i.elim0,fun i => i.elim0⟩
      uniq := fun x => Subtype.ext (funext fun i => i.elim0) }
  simp [v]

private theorem value (n : ℕ) : a (n+1) = 20 * v n high := by
  have rows : Fintype.card {r : Row // legal r} = 20 := by decide +kernel
  have h := Fintype.card_congr (splitArray n)
  rw [Fintype.card_prod,rows] at h
  unfold a
  rw [← Fintype.card_subtype, h]
  push_cast
  rfl

private def rowIndex (r : Row) : Fin 128 :=
  ⟨64*(r 0).val + 32*(r 1).val + 16*(r 2).val + 8*(r 3).val + 4*(r 4).val + 2*(r 5).val + 1*(r 6).val, by omega⟩

private def table : Fin 9 → Fin 128 → ℤ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 4, 4, 3, 3, 4, 4, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 4, 4, 3, 3, 4, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 4, 5, 4, 5, 3, 3, 3, 3, 4, 5, 4, 5, 4, 4, 4, 4, 4, 4, 4, 4, 6, 6, 8, 8, 6, 6, 8, 8, 6, 6, 6, 6, 8, 10, 8, 10, 9, 9, 12, 12, 12, 15, 16, 20],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 3, 3, 3, 6, 6, 10, 10, 6, 6, 10, 10, 3, 3, 3, 3, 3, 3, 3, 3, 6, 6, 10, 10, 6, 6, 10, 10, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 6, 6, 6, 6, 10, 15, 10, 15, 6, 6, 6, 6, 10, 15, 10, 15, 9, 9, 9, 9, 9, 9, 9, 9, 18, 18, 30, 30, 18, 18, 30, 30, 18, 18, 18, 18, 30, 45, 30, 45, 36, 36, 60, 60, 60, 90, 100, 150],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 4, 4, 4, 4, 4, 10, 10, 20, 20, 10, 10, 20, 20, 4, 4, 4, 4, 4, 4, 4, 4, 10, 10, 20, 20, 10, 10, 20, 20, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 10, 10, 10, 10, 20, 35, 20, 35, 10, 10, 10, 10, 20, 35, 20, 35, 16, 16, 16, 16, 16, 16, 16, 16, 40, 40, 80, 80, 40, 40, 80, 80, 40, 40, 40, 40, 80, 140, 80, 140, 100, 100, 200, 200, 200, 350, 400, 700],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 5, 5, 5, 5, 5, 5, 15, 15, 35, 35, 15, 15, 35, 35, 5, 5, 5, 5, 5, 5, 5, 5, 15, 15, 35, 35, 15, 15, 35, 35, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 15, 15, 15, 15, 35, 70, 35, 70, 15, 15, 15, 15, 35, 70, 35, 70, 25, 25, 25, 25, 25, 25, 25, 25, 75, 75, 175, 175, 75, 75, 175, 175, 75, 75, 75, 75, 175, 350, 175, 350, 225, 225, 525, 525, 525, 1050, 1225, 2450],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 6, 6, 6, 6, 6, 6, 21, 21, 56, 56, 21, 21, 56, 56, 6, 6, 6, 6, 6, 6, 6, 6, 21, 21, 56, 56, 21, 21, 56, 56, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 21, 21, 21, 21, 56, 126, 56, 126, 21, 21, 21, 21, 56, 126, 56, 126, 36, 36, 36, 36, 36, 36, 36, 36, 126, 126, 336, 336, 126, 126, 336, 336, 126, 126, 126, 126, 336, 756, 336, 756, 441, 441, 1176, 1176, 1176, 2646, 3136, 7056],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 7, 7, 7, 7, 7, 7, 7, 28, 28, 84, 84, 28, 28, 84, 84, 7, 7, 7, 7, 7, 7, 7, 7, 28, 28, 84, 84, 28, 28, 84, 84, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 28, 28, 28, 28, 84, 210, 84, 210, 28, 28, 28, 28, 84, 210, 84, 210, 49, 49, 49, 49, 49, 49, 49, 49, 196, 196, 588, 588, 196, 196, 588, 588, 196, 196, 196, 196, 588, 1470, 588, 1470, 784, 784, 2352, 2352, 2352, 5880, 7056, 17640],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 8, 8, 8, 8, 8, 8, 8, 36, 36, 120, 120, 36, 36, 120, 120, 8, 8, 8, 8, 8, 8, 8, 8, 36, 36, 120, 120, 36, 36, 120, 120, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 36, 36, 36, 36, 120, 330, 120, 330, 36, 36, 36, 36, 120, 330, 120, 330, 64, 64, 64, 64, 64, 64, 64, 64, 288, 288, 960, 960, 288, 288, 960, 960, 288, 288, 288, 288, 960, 2640, 960, 2640, 1296, 1296, 4320, 4320, 4320, 11880, 14400, 39600],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 9, 9, 9, 9, 9, 9, 9, 45, 45, 165, 165, 45, 45, 165, 165, 9, 9, 9, 9, 9, 9, 9, 9, 45, 45, 165, 165, 45, 45, 165, 165, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 45, 45, 45, 45, 165, 495, 165, 495, 45, 45, 45, 45, 165, 495, 165, 495, 81, 81, 81, 81, 81, 81, 81, 81, 405, 405, 1485, 1485, 405, 405, 1485, 1485, 405, 405, 405, 405, 1485, 4455, 1485, 4455, 2025, 2025, 7425, 7425, 7425, 22275, 27225, 81675]]

private def initial (k : Fin 9) (r : Row) : ℤ := table k (rowIndex r)

private theorem table_step : ∀ k : Fin 8, ∀ u : Row,
    initial k.succ u = step (initial k.castSucc) u := by decide +kernel

private theorem initial_eq (k : Fin 9) : v k.val = initial k := by
  induction k using Fin.induction with
  | zero =>
    rw [Fin.val_zero,zero_v]
    exact funext ((by decide +kernel) : ∀ u : Row, 1 = initial 0 u)
  | succ k ih =>
    rw [Fin.val_succ,succ_v]
    change step (v k.castSucc.val) = initial k.succ
    rw [ih]
    exact funext fun u => (table_step k u).symm

private theorem differences (n : ℕ) : ∀ u : Row, legal u →
    v (n+8) u = 8*v (n+7) u - 28*v (n+6) u + 56*v (n+5) u - 70*v (n+4) u + 56*v (n+3) u - 28*v (n+2) u + 8*v (n+1) u - v n u := by
  induction n with
  | zero =>
    have e0 : v 0 = initial 0 := initial_eq 0
    have e1 : v 1 = initial 1 := initial_eq 1
    have e2 : v 2 = initial 2 := initial_eq 2
    have e3 : v 3 = initial 3 := initial_eq 3
    have e4 : v 4 = initial 4 := initial_eq 4
    have e5 : v 5 = initial 5 := initial_eq 5
    have e6 : v 6 = initial 6 := initial_eq 6
    have e7 : v 7 = initial 7 := initial_eq 7
    have e8 : v 8 = initial 8 := initial_eq 8
    simp only [Nat.zero_add,e0,e1,e2,e3,e4,e5,e6,e7,e8]
    decide +kernel
  | succ n ih =>
    intro u hu
    change v ((n+8)+1) u = _
    rw [succ_v (n+8)]
    change (∑ r : {r : Row // legal r ∧ r ≤ u}, v (n+8) r.val) = _
    rw [Finset.sum_congr rfl (fun (r : {r : Row // legal r ∧ r ≤ u}) _ => ih r.val r.property.1)]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
    have sum_v (t : ℕ) : (∑ r : {r : Row // legal r ∧ r ≤ u}, v t r.val) = v (t+1) u :=
      (congrFun (succ_v t) u).symm
    simp only [sum_v]

private theorem recurrence (n : ℕ) (hn : 9 ≤ n) :
    (a n : ℚ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  obtain ⟨m,rfl⟩ : ∃ m, n=m+9 := ⟨n-9,by omega⟩
  have h := differences m high (by decide +kernel)
  exact_mod_cast (show a (m+9) = _ from by simp [value]; linarith)

private theorem generating :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 8 : PowerSeries ℚ) = 20 * X * (1 + 12 * X + 18 * X ^ 2 + 4 * X ^ 3) := by
  let S := mk (fun n => if n < 1 then 0 else (a n : ℚ))
  change S * _ = _
  have lhs : S*(1-X)^8 = S - (8:ℕ) • (S*X^1) + (28:ℕ) • (S*X^2) - (56:ℕ) • (S*X^3) + (70:ℕ) • (S*X^4) - (56:ℕ) • (S*X^5) + (28:ℕ) • (S*X^6) - (8:ℕ) • (S*X^7) + (S*X^8) := by simp only [nsmul_eq_mul]; ring
  have rhs : (20 * X * (1 + 12 * X + 18 * X ^ 2 + 4 * X ^ 3) : PowerSeries ℚ) = (20:ℕ) • X^1 + (240:ℕ) • X^2 + (360:ℕ) • X^3 + (80:ℕ) • X^4 := by simp only [nsmul_eq_mul]; ring
  rw [lhs,rhs]
  ext n
  simp only [map_add,map_sub,map_nsmul,coeff_mul_X_pow',coeff_X_pow,S,coeff_mk]
  by_cases h : 9 ≤ n
  · have recn := recurrence n h
    simp only [nsmul_eq_mul, if_pos (show 1 ≤ n by omega),
      if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega),
      if_pos (show 4 ≤ n by omega),
      if_pos (show 5 ≤ n by omega),
      if_pos (show 6 ≤ n by omega),
      if_pos (show 7 ≤ n by omega),
      if_pos (show 8 ≤ n by omega),
      if_neg (show ¬ n < 1 by omega),
      if_neg (show ¬ n-1 < 1 by omega),
      if_neg (show ¬ n-2 < 1 by omega),
      if_neg (show ¬ n-3 < 1 by omega),
      if_neg (show ¬ n-4 < 1 by omega),
      if_neg (show ¬ n-5 < 1 by omega),
      if_neg (show ¬ n-6 < 1 by omega),
      if_neg (show ¬ n-7 < 1 by omega),
      if_neg (show ¬ n-8 < 1 by omega),
      if_neg (show n ≠ 1 by omega),
      if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 3 by omega),
      if_neg (show n ≠ 4 by omega)]
    norm_num
    linarith
  · have e1 : a 1 = 20 := (value 0).trans (by rw [show v 0 = _ from initial_eq 0]; decide +kernel)
    have e2 : a 2 = 400 := (value 1).trans (by rw [show v 1 = _ from initial_eq 1]; decide +kernel)
    have e3 : a 3 = 3000 := (value 2).trans (by rw [show v 2 = _ from initial_eq 2]; decide +kernel)
    have e4 : a 4 = 14000 := (value 3).trans (by rw [show v 3 = _ from initial_eq 3]; decide +kernel)
    have e5 : a 5 = 49000 := (value 4).trans (by rw [show v 4 = _ from initial_eq 4]; decide +kernel)
    have e6 : a 6 = 141120 := (value 5).trans (by rw [show v 5 = _ from initial_eq 5]; decide +kernel)
    have e7 : a 7 = 352800 := (value 6).trans (by rw [show v 6 = _ from initial_eq 6]; decide +kernel)
    have e8 : a 8 = 792000 := (value 7).trans (by rw [show v 7 = _ from initial_eq 7]; decide +kernel)
    interval_cases n <;> norm_num [e1,e2,e3,e4,e5,e6,e7,e8]

theorem result : type_of% @OMA.S_oeis_a208141.main := ⟨generating,recurrence⟩

end OMA.Arrays208141

theorem OMA.solution : type_of% @OMA.S_oeis_a208141.main := OMA.Arrays208141.result
