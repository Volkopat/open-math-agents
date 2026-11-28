import OMAStatements.S_oeis_a207064
import Mathlib

namespace OMA.Arrays207064

open OMA.S_oeis_a207064
open PowerSeries

private abbrev Row := Fin 4 → Fin 2

private def legal (r : Row) : Prop := ∀ j : Fin 2,
  let t := ((r ⟨j, by omega⟩).val, (r ⟨j+1, by omega⟩).val, (r ⟨j+2, by omega⟩).val)
  t ≠ (0,0,1) ∧ t ≠ (0,1,0)

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
    (∀ i < n, ∀ j < 4-2,
      (get x i j, get x i (j+1), get x i (j+2)) ≠ (0,0,1) ∧
      (get x i j, get x i (j+1), get x i (j+2)) ≠ (0,1,0)) ↔ ∀ i, legal (x i) := by
  constructor
  · intro h i j
    simpa [OMA.S_oeis_a207064.get, i.isLt, show j.val < 4 by omega, show j.val+1 < 4 by omega,
      show j.val+2 < 4 by omega] using h i i.isLt j j.isLt
  · intro h i hi j hj
    simpa [OMA.S_oeis_a207064.get, hi, show j < 4 by omega, show j+1 < 4 by omega, show j+2 < 4 by omega]
      using h ⟨i,hi⟩ ⟨j,hj⟩

private theorem vertical {n : ℕ} (x : Fin (n+1) → Row) :
    (∀ i < n+1-2, ∀ j < 4,
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
      simpa [OMA.S_oeis_a207064.get, j.isLt, show i.val < n+1+1 by omega,
        show i.val+1 < n+1+1 by omega, show i.val+2 < n+1+1 by omega]
        using h i (by omega) j j.isLt
    · intro h i hi j hj
      have hh := (bits (x ⟨i,by omega⟩ ⟨j,hj⟩) _ _).mpr (h ⟨i,by omega⟩ ⟨j,hj⟩)
      simpa [OMA.S_oeis_a207064.get, hj, show i < n+1+1 by omega, show i+1 < n+1+1 by omega,
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

private theorem value (n : ℕ) : a (n+1) = 9 * v n high := by
  have rows : Fintype.card {r : Row // legal r} = 9 := by decide +kernel
  have h := Fintype.card_congr (splitArray n)
  rw [Fintype.card_prod,rows] at h
  unfold a
  rw [← Fintype.card_subtype, h]
  push_cast
  rfl

private def rowIndex (r : Row) : Fin 16 :=
  ⟨8*(r 0).val + 4*(r 1).val + 2*(r 2).val + (r 3).val, by omega⟩

private def table : Fin 6 → Fin 16 → ℤ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 4, 5, 9],
    ![1, 1, 1, 1, 1, 1, 3, 6, 3, 3, 3, 6, 6, 10, 13, 32],
    ![1, 1, 1, 1, 1, 1, 4, 10, 4, 4, 4, 10, 10, 20, 26, 80],
    ![1, 1, 1, 1, 1, 1, 5, 15, 5, 5, 5, 15, 15, 35, 45, 165],
    ![1, 1, 1, 1, 1, 1, 6, 21, 6, 6, 6, 21, 21, 56, 71, 301]]

private def initial (k : Fin 6) (r : Row) : ℤ := table k (rowIndex r)

private theorem table_step : ∀ k : Fin 5, ∀ u : Row,
    initial k.succ u = step (initial k.castSucc) u := by decide +kernel

private theorem initial_eq (k : Fin 6) : v k.val = initial k := by
  induction k using Fin.induction with
  | zero =>
    rw [Fin.val_zero,zero_v]
    exact funext ((by decide +kernel) : ∀ u : Row, 1 = initial 0 u)
  | succ k ih =>
    rw [Fin.val_succ,succ_v]
    change step (v k.castSucc.val) = initial k.succ
    rw [ih]
    exact funext fun u => (table_step k u).symm

private theorem differences (n : ℕ) :
    v (n+5) = (5:ℕ) • v (n+4) - (10:ℕ) • v (n+3) + (10:ℕ) • v (n+2)
      - (5:ℕ) • v (n+1) + v n := by
  induction n with
  | zero =>
    have e0 : v 0 = initial 0 := initial_eq 0
    have e1 : v 1 = initial 1 := initial_eq 1
    have e2 : v 2 = initial 2 := initial_eq 2
    have e3 : v 3 = initial 3 := initial_eq 3
    have e4 : v 4 = initial 4 := initial_eq 4
    have e5 : v 5 = initial 5 := initial_eq 5
    simp only [Nat.zero_add,e0,e1,e2,e3,e4,e5]
    exact funext ((by decide +kernel) : ∀ u : Row, _)
  | succ n ih =>
    have lin (f g h i j : Row → ℤ) :
        step ((5:ℕ) • f - (10:ℕ) • g + (10:ℕ) • h - (5:ℕ) • i + j) =
        (5:ℕ) • step f - (10:ℕ) • step g + (10:ℕ) • step h - (5:ℕ) • step i + step j := by
      funext u
      simp [step,Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum,nsmul_eq_mul]
    apply Eq.trans (succ_v (n+5))
    conv_lhs => rw [ih,lin]
    simp only [← succ_v]

private theorem recurrence (n : ℕ) (hn : 6 ≤ n) :
    (a n : ℚ) = 5*a (n-1)-10*a (n-2)+10*a (n-3)-5*a (n-4)+a (n-5) := by
  obtain ⟨m,rfl⟩ : ∃ m, n=m+6 := ⟨n-6,by omega⟩
  have h := congrFun (differences m) high
  norm_num [Pi.add_apply,Pi.sub_apply,nsmul_eq_mul,Pi.mul_apply] at h
  exact_mod_cast (show a (m+6) = _ from by simp [value]; linarith)

private theorem generating :
    mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1-X)^5 : PowerSeries ℚ) =
    9*X*(1+4*X-3*X^2) := by
  let S := mk (fun n => if n < 1 then 0 else (a n : ℚ))
  change S * _ = _
  have lhs : S*(1-X)^5 = S - (5:ℕ) • (S*X^1) + (10:ℕ) • (S*X^2) -
      (10:ℕ) • (S*X^3) + (5:ℕ) • (S*X^4) - S*X^5 := by simp only [nsmul_eq_mul]; ring
  have rhs : (9*X*(1+4*X-3*X^2) : PowerSeries ℚ) =
      (9:ℕ) • X^1 + (36:ℕ) • X^2 - (27:ℕ) • X^3 := by simp only [nsmul_eq_mul]; ring
  rw [lhs,rhs]
  ext n
  simp only [map_add,map_sub,map_nsmul,coeff_mul_X_pow',coeff_X_pow,S,coeff_mk]
  by_cases h : 6 ≤ n
  · have recn := recurrence n h
    simp only [nsmul_eq_mul, if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega),if_pos (show 4 ≤ n by omega),if_pos (show 5 ≤ n by omega),
      if_neg (show ¬ n < 1 by omega),if_neg (show ¬ n-1 < 1 by omega),
      if_neg (show ¬ n-2 < 1 by omega),if_neg (show ¬ n-3 < 1 by omega),
      if_neg (show ¬ n-4 < 1 by omega),if_neg (show ¬ n-5 < 1 by omega),
      if_neg (show n ≠ 1 by omega),if_neg (show n ≠ 2 by omega),if_neg (show n ≠ 3 by omega)]
    norm_num
    linarith
  · have e1 : a 1 = 9 := (value 0).trans (by rw [show v 0 = _ from initial_eq 0]; decide +kernel)
    have e2 : a 2 = 81 := (value 1).trans (by rw [show v 1 = _ from initial_eq 1]; decide +kernel)
    have e3 : a 3 = 288 := (value 2).trans (by rw [show v 2 = _ from initial_eq 2]; decide +kernel)
    have e4 : a 4 = 720 := (value 3).trans (by rw [show v 3 = _ from initial_eq 3]; decide +kernel)
    have e5 : a 5 = 1485 := (value 4).trans (by rw [show v 4 = _ from initial_eq 4]; decide +kernel)
    interval_cases n <;> norm_num [e1,e2,e3,e4,e5]

theorem result : type_of% @OMA.S_oeis_a207064.main := ⟨generating,recurrence⟩

end OMA.Arrays207064

theorem OMA.solution : type_of% @OMA.S_oeis_a207064.main := OMA.Arrays207064.result
