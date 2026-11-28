import OMAStatements.S_oeis_a207256
import Mathlib

namespace OMA.Arrays207256

open OMA.S_oeis_a207256
open PowerSeries

private abbrev Row := Fin 5 → Fin 2

private def legal (r : Row) : Prop := ∀ j : Fin 3,
  let t := ((r ⟨j, by omega⟩).val, (r ⟨j+1, by omega⟩).val, (r ⟨j+2, by omega⟩).val)
  t ≠ (0,1,0) ∧ t ≠ (1,0,1)

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
    (∀ i < n, ∀ j < 5-2,
      (get x i j, get x i (j+1), get x i (j+2)) ≠ (0,1,0) ∧
      (get x i j, get x i (j+1), get x i (j+2)) ≠ (1,0,1)) ↔ ∀ i, legal (x i) := by
  constructor
  · intro h i j
    simpa [OMA.S_oeis_a207256.get, i.isLt, show j.val < 5 by omega, show j.val+1 < 5 by omega,
      show j.val+2 < 5 by omega] using h i i.isLt j j.isLt
  · intro h i hi j hj
    simpa [OMA.S_oeis_a207256.get, hi, show j < 5 by omega, show j+1 < 5 by omega, show j+2 < 5 by omega]
      using h ⟨i,hi⟩ ⟨j,hj⟩

private theorem vertical {n : ℕ} (x : Fin (n+1) → Row) :
    (∀ i < n+1-2, ∀ j < 5,
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
      simpa [OMA.S_oeis_a207256.get, j.isLt, show i.val < n+1+1 by omega,
        show i.val+1 < n+1+1 by omega, show i.val+2 < n+1+1 by omega]
        using h i (by omega) j j.isLt
    · intro h i hi j hj
      have hh := (bits (x ⟨i,by omega⟩ ⟨j,hj⟩) _ _).mpr (h ⟨i,by omega⟩ ⟨j,hj⟩)
      simpa [OMA.S_oeis_a207256.get, hj, show i < n+1+1 by omega, show i+1 < n+1+1 by omega,
        show i+2 < n+1+1 by omega] using hh

private def flip {r c : ℕ} (x : Fin r → Fin c → Fin 2) : Fin c → Fin r → Fin 2 :=
  fun i j => x j i

private theorem get_flip {r c : ℕ} (x : Fin r → Fin c → Fin 2) (i j : ℕ) :
    OMA.S_oeis_a207256.get (flip x) i j = OMA.S_oeis_a207256.get x j i := by
  by_cases hi : i < c <;> by_cases hj : j < r <;> simp [OMA.S_oeis_a207256.get,hi,hj,flip]

private def fits {n : ℕ} (x : Fin n → Row) : Bool := avoids (flip x)

private theorem array_iff {n : ℕ} (x : Fin (n+1) → Row) :
    fits x = true ↔ legal (x 0) ∧ good high (fun i => x i.succ) := by
  unfold fits avoids
  simp only [decide_eq_true_eq,get_flip]
  rw [← and_comm]
  conv_lhs =>
    congr
    · rw [show (∀ j < 5-2, ∀ i < n+1, _) ↔ (∀ i < n+1, ∀ j < 5-2, _) from
        ⟨fun h i hi j hj => h j hj i hi, fun h j hj i hi => h i hi j hj⟩]
    · rw [show (∀ j < 5, ∀ i < n+1-2, _) ↔ (∀ i < n+1-2, ∀ j < 5, _) from
        ⟨fun h i hi j hj => h j hj i hi, fun h j hj i hi => h i hi j hj⟩]
  simp only [horizontal,vertical,good,Fin.forall_fin_succ]
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
    {x : Fin (n+1) → Row // fits x = true} ≃ {r : Row // legal r} × Chain n high where
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

private theorem value (n : ℕ) : a (n+1) = 16 * v n high := by
  have rows : Fintype.card {r : Row // legal r} = 16 := by decide +kernel
  let transpose : {x : Fin 5 → Fin (n+1) → Fin 2 // avoids x = true} ≃
      {x : Fin (n+1) → Row // fits x = true} :=
    ⟨fun x => ⟨flip x.val,x.property⟩,fun x => ⟨flip x.val,x.property⟩,
      fun _ => rfl,fun _ => rfl⟩
  have h := Fintype.card_congr (transpose.trans (splitArray n))
  rw [Fintype.card_prod,rows] at h
  unfold a
  rw [← Fintype.card_subtype, h]
  push_cast
  rfl

private def rowIndex (r : Row) : Fin 32 :=
  ⟨16*(r 0).val + 8*(r 1).val + 4*(r 2).val + 2*(r 3).val + 1*(r 4).val, by omega⟩

private def table : Fin 7 → Fin 32 → ℤ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 2, 1, 3, 1, 2, 2, 5, 1, 2, 1, 3, 2, 3, 4, 8, 2, 4, 2, 6, 2, 4, 3, 8, 3, 6, 3, 8, 5, 8, 8, 16],
    ![1, 3, 1, 6, 1, 3, 3, 13, 1, 3, 1, 6, 3, 5, 9, 27, 3, 9, 3, 18, 3, 9, 5, 25, 6, 18, 6, 27, 13, 25, 27, 77],
    ![1, 4, 1, 10, 1, 4, 4, 26, 1, 4, 1, 10, 4, 7, 16, 65, 4, 16, 4, 40, 4, 16, 7, 56, 10, 40, 10, 64, 26, 56, 65, 236],
    ![1, 5, 1, 15, 1, 5, 5, 45, 1, 5, 1, 15, 5, 9, 25, 130, 5, 25, 5, 75, 5, 25, 9, 105, 15, 75, 15, 125, 45, 105, 130, 567],
    ![1, 6, 1, 21, 1, 6, 6, 71, 1, 6, 1, 21, 6, 11, 36, 231, 6, 36, 6, 126, 6, 36, 11, 176, 21, 126, 21, 216, 71, 176, 231, 1168],
    ![1, 7, 1, 28, 1, 7, 7, 105, 1, 7, 1, 28, 7, 13, 49, 378, 7, 49, 7, 196, 7, 49, 13, 273, 28, 196, 28, 343, 105, 273, 378, 2163]]

private def initial (k : Fin 7) (r : Row) : ℤ := table k (rowIndex r)

private theorem table_step : ∀ k : Fin 6, ∀ u : Row,
    initial k.succ u = step (initial k.castSucc) u := by decide +kernel

private theorem initial_eq (k : Fin 7) : v k.val = initial k := by
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
    v (n+6) u = 6*v (n+5) u - 15*v (n+4) u + 20*v (n+3) u - 15*v (n+2) u + 6*v (n+1) u - v n u := by
  induction n with
  | zero =>
    have e0 : v 0 = initial 0 := initial_eq 0
    have e1 : v 1 = initial 1 := initial_eq 1
    have e2 : v 2 = initial 2 := initial_eq 2
    have e3 : v 3 = initial 3 := initial_eq 3
    have e4 : v 4 = initial 4 := initial_eq 4
    have e5 : v 5 = initial 5 := initial_eq 5
    have e6 : v 6 = initial 6 := initial_eq 6
    simp only [Nat.zero_add,e0,e1,e2,e3,e4,e5,e6]
    decide +kernel
  | succ n ih =>
    intro u hu
    change v ((n+6)+1) u = _
    rw [succ_v (n+6)]
    change (∑ r : {r : Row // legal r ∧ r ≤ u}, v (n+6) r.val) = _
    rw [Finset.sum_congr rfl (fun (r : {r : Row // legal r ∧ r ≤ u}) _ => ih r.val r.property.1)]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
    have sum_v (t : ℕ) : (∑ r : {r : Row // legal r ∧ r ≤ u}, v t r.val) = v (t+1) u :=
      (congrFun (succ_v t) u).symm
    simp only [sum_v]

private theorem recurrence (n : ℕ) (hn : 7 ≤ n) :
    (a n : ℚ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  obtain ⟨m,rfl⟩ : ∃ m, n=m+7 := ⟨n-7,by omega⟩
  have h := differences m high (by decide +kernel)
  exact_mod_cast (show a (m+7) = _ from by simp [value]; linarith)

private theorem generating :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 6 : PowerSeries ℚ) = 16 * X * (1 + 10 * X - 4 * X ^ 2 - 6 * X ^ 3 + X ^ 4) := by
  let S := mk (fun n => if n < 1 then 0 else (a n : ℚ))
  change S * _ = _
  have lhs : S*(1-X)^6 = S - (6:ℕ) • (S*X^1) + (15:ℕ) • (S*X^2) - (20:ℕ) • (S*X^3) + (15:ℕ) • (S*X^4) - (6:ℕ) • (S*X^5) + (S*X^6) := by simp only [nsmul_eq_mul]; ring
  have rhs : (16 * X * (1 + 10 * X - 4 * X ^ 2 - 6 * X ^ 3 + X ^ 4) : PowerSeries ℚ) = (16:ℕ) • X^1 + (160:ℕ) • X^2 - (64:ℕ) • X^3 - (96:ℕ) • X^4 + (16:ℕ) • X^5 := by simp only [nsmul_eq_mul]; ring
  rw [lhs,rhs]
  ext n
  simp only [map_add,map_sub,map_nsmul,coeff_mul_X_pow',coeff_X_pow,S,coeff_mk]
  by_cases h : 7 ≤ n
  · have recn := recurrence n h
    simp only [nsmul_eq_mul, if_pos (show 1 ≤ n by omega),
      if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega),
      if_pos (show 4 ≤ n by omega),
      if_pos (show 5 ≤ n by omega),
      if_pos (show 6 ≤ n by omega),
      if_neg (show ¬ n < 1 by omega),
      if_neg (show ¬ n-1 < 1 by omega),
      if_neg (show ¬ n-2 < 1 by omega),
      if_neg (show ¬ n-3 < 1 by omega),
      if_neg (show ¬ n-4 < 1 by omega),
      if_neg (show ¬ n-5 < 1 by omega),
      if_neg (show ¬ n-6 < 1 by omega),
      if_neg (show n ≠ 1 by omega),
      if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 3 by omega),
      if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 5 by omega)]
    norm_num
    linarith
  · have e1 : a 1 = 16 := (value 0).trans (by rw [show v 0 = _ from initial_eq 0]; decide +kernel)
    have e2 : a 2 = 256 := (value 1).trans (by rw [show v 1 = _ from initial_eq 1]; decide +kernel)
    have e3 : a 3 = 1232 := (value 2).trans (by rw [show v 2 = _ from initial_eq 2]; decide +kernel)
    have e4 : a 4 = 3776 := (value 3).trans (by rw [show v 3 = _ from initial_eq 3]; decide +kernel)
    have e5 : a 5 = 9072 := (value 4).trans (by rw [show v 4 = _ from initial_eq 4]; decide +kernel)
    have e6 : a 6 = 18688 := (value 5).trans (by rw [show v 5 = _ from initial_eq 5]; decide +kernel)
    interval_cases n <;> norm_num [e1,e2,e3,e4,e5,e6]

theorem result : type_of% @OMA.S_oeis_a207256.main := ⟨generating,recurrence⟩

end OMA.Arrays207256

theorem OMA.solution : type_of% @OMA.S_oeis_a207256.main := OMA.Arrays207256.result
