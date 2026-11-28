import OMAStatements.S_oeis_a207935
import Mathlib

namespace OMA.Arrays207935

open OMA.S_oeis_a207935
open PowerSeries

private abbrev Row := Fin 5 → Fin 2

private def legal (r : Row) : Prop := ∀ j : Fin 3,
  let t := ((r ⟨j, by omega⟩).val, (r ⟨j+1, by omega⟩).val, (r ⟨j+2, by omega⟩).val)
  t ≠ (0,0,1) ∧ t ≠ (1,0,0)

private instance (r : Row) : Decidable (legal r) := by unfold legal; infer_instance

private theorem horizontal {n : ℕ} (x : Fin n → Row) :
    (∀ i < n, ∀ j < 5-2,
      (get x i j, get x i (j+1), get x i (j+2)) ≠ (0,0,1) ∧
      (get x i j, get x i (j+1), get x i (j+2)) ≠ (1,0,0)) ↔ ∀ i, legal (x i) := by
  constructor
  · intro h i j
    simpa [OMA.S_oeis_a207935.get, i.isLt, show j.val < 5 by omega, show j.val+1 < 5 by omega,
      show j.val+2 < 5 by omega] using h i i.isLt j j.isLt
  · intro h i hi j hj
    simpa [OMA.S_oeis_a207935.get, hi, show j < 5 by omega, show j+1 < 5 by omega, show j+2 < 5 by omega]
      using h ⟨i,hi⟩ ⟨j,hj⟩

private def next (p q r : Row) : Prop := ∀ j, p j = q j → q j = r j

private instance (p q r : Row) : Decidable (next p q r) := by unfold next; infer_instance

private theorem bits (a b c : Fin 2) :
    (((a.val,b.val,c.val) ≠ (0,0,1) ∧ (a.val,b.val,c.val) ≠ (1,1,0)) ↔ (a = b → b = c)) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

private def good {n : ℕ} (p q : Row) (x : Fin n → Row) : Prop :=
  (∀ i, legal (x i)) ∧ (∀ i : Fin n,
    let y : Fin (n+2) → Row := Fin.cons p (Fin.cons q x)
    next (y i.castSucc.castSucc) (y i.castSucc.succ) (x i))

private theorem vertical {n : ℕ} (x : Fin (n+2) → Row) :
    (∀ i < n+2-2, ∀ j < 5,
      (get x i j, get x (i+1) j, get x (i+2) j) ≠ (0,0,1) ∧
      (get x i j, get x (i+1) j, get x (i+2) j) ≠ (1,1,0)) ↔
    ∀ i : Fin n, next (x i.castSucc.castSucc) (x i.castSucc.succ) (x i.succ.succ) := by
  constructor
  · intro h i j
    change x ⟨i.val,by omega⟩ j = x ⟨i.val+1,by omega⟩ j →
      x ⟨i.val+1,by omega⟩ j = x ⟨i.val+2,by omega⟩ j
    apply (bits _ _ _).mp
    simpa [OMA.S_oeis_a207935.get,j.isLt,show i.val < n+2 by omega,
      show i.val+1 < n+2 by omega,show i.val+2 < n+2 by omega] using h i (by omega) j j.isLt
  · intro h i hi j hj
    have hh := (bits _ _ _).mpr (h ⟨i,by omega⟩ ⟨j,hj⟩)
    simpa [OMA.S_oeis_a207935.get,hj,show i < n+2 by omega,
      show i+1 < n+2 by omega,show i+2 < n+2 by omega] using hh

private theorem array_iff {n : ℕ} (x : Fin (n+2) → Row) :
    avoids x = true ↔ legal (x 0) ∧ legal (x 1) ∧ good (x 0) (x 1) (fun i => x i.succ.succ) := by
  have reconstruct : Fin.cons (x 0) (Fin.cons (x 1) (fun i : Fin n => x i.succ.succ)) = x := by
    funext j
    refine Fin.cases rfl (fun i => ?_) j
    exact Fin.cases rfl (fun _ => rfl) i
  simp only [avoids,decide_eq_true_eq,horizontal,vertical,good,reconstruct]
  constructor
  · intro ⟨a,b⟩
    exact ⟨a 0,a 1,fun i => a _,b⟩
  · intro ⟨a,b,c,h⟩
    exact ⟨Fin.forall_fin_succ.mpr ⟨a,Fin.forall_fin_succ.mpr ⟨b,c⟩⟩,h⟩

private theorem split_good {n : ℕ} (p q : Row) (x : Fin (n+1) → Row) :
    good p q x ↔ (legal (x 0) ∧ next p q (x 0)) ∧ good q (x 0) (fun i => x i.succ) := by
  simp only [good,Fin.forall_fin_succ]
  have reconstruct : Fin.cons (x 0) (fun i => x i.succ) = x := Fin.cons_self_tail _
  rw [reconstruct]
  constructor
  · intro ⟨⟨a,b⟩,c,h⟩
    exact ⟨⟨a,c⟩,b,h⟩
  · intro ⟨⟨a,c⟩,b,h⟩
    exact ⟨⟨a,b⟩,c,h⟩

private abbrev Chain (n : ℕ) (p q : Row) := {x : Fin n → Row // good p q x}

private noncomputable instance (n : ℕ) (p q : Row) : Fintype (Chain n p q) := Fintype.ofFinite _

private def splitChain (n : ℕ) (p q : Row) :
    Chain (n+1) p q ≃ (Σ r : {r : Row // legal r ∧ next p q r}, Chain n q r.val) where
  toFun x :=
    let h := (split_good p q x.val).mp x.property
    ⟨⟨x.val 0,h.1⟩,⟨fun i => x.val i.succ,h.2⟩⟩
  invFun y := ⟨Fin.cons y.1.val y.2.val,(split_good _ _ _).mpr (by
    simpa only [Fin.cons_zero,Fin.cons_succ] using And.intro y.1.property y.2.property)⟩
  left_inv x := Subtype.ext (Fin.cons_self_tail _)
  right_inv y := by rcases y with ⟨⟨r,hr⟩,⟨x,hx⟩⟩; rfl

private abbrev Legal := {r : Row // legal r}

private def splitArray (n : ℕ) :
    {x : Fin (n+2) → Row // avoids x = true} ≃
      (Σ p : Legal, Σ q : Legal, Chain n p.val q.val) where
  toFun x :=
    let h := (array_iff x.val).mp x.property
    ⟨⟨x.val 0,h.1⟩,⟨x.val 1,h.2.1⟩,⟨fun i => x.val i.succ.succ,h.2.2⟩⟩
  invFun y := ⟨Fin.cons y.1.val (Fin.cons y.2.1.val y.2.2.val),(array_iff _).mpr (by
    exact ⟨y.1.property,y.2.1.property,y.2.2.property⟩)⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun _ => rfl) j
  right_inv y := by rcases y with ⟨⟨p,hp⟩,⟨q,hq⟩,⟨x,hx⟩⟩; rfl

private noncomputable def v (n : ℕ) (p q : Row) : ℤ := Fintype.card (Chain n p q)

private def step (f : Row → Row → ℤ) (p q : Row) : ℤ :=
  ∑ r : {r : Row // legal r ∧ next p q r}, f q r.val

private theorem succ_v (n : ℕ) : v (n+1) = step (v n) := by
  funext p q
  simp [step,v,Fintype.card_congr (splitChain n p q),Fintype.card_sigma]

private theorem zero_v : v 0 = fun _ _ => 1 := by
  funext p q
  have : Unique (Chain 0 p q) :=
    { default := ⟨Fin.elim0,fun i => i.elim0,fun i => i.elim0⟩
      uniq := fun _ => Subtype.ext (funext fun i => i.elim0) }
  simp [v]

private def total (f : Row → Row → ℤ) : ℤ := ∑ p : Legal, ∑ q : Legal, f p.val q.val

private theorem value (n : ℕ) : a (n+2) = total (v n) := by
  have h := Fintype.card_congr (splitArray n)
  simp only [Fintype.card_sigma] at h
  unfold a total v
  rw [← Fintype.card_subtype,h]
  push_cast
  rfl

private def rowIndex (r : Row) : Fin 32 :=
  ⟨16*(r 0).val + 8*(r 1).val + 4*(r 2).val + 2*(r 3).val + 1*(r 4).val, by omega⟩

private def code (r : Row) : Fin 14 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 3, 4, 5, 0, 0, 0, 0, 0, 6, 7, 8, 0, 0, 9, 10, 0, 11, 12, 13] (rowIndex r)

private def table : Fin 7 → Fin 14 → Fin 14 → ℤ :=
  ![![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]],
    ![![1, 2, 3, 2, 3, 6, 2, 2, 4, 3, 5, 4, 6, 14],
      ![2, 1, 2, 5, 2, 4, 14, 5, 10, 2, 4, 10, 4, 8],
      ![3, 2, 1, 3, 4, 2, 8, 10, 5, 4, 2, 6, 8, 4],
      ![2, 5, 3, 1, 3, 2, 3, 9, 6, 10, 6, 2, 6, 4],
      ![3, 2, 4, 3, 1, 2, 9, 3, 6, 4, 8, 6, 2, 4],
      ![6, 4, 2, 2, 2, 1, 6, 6, 3, 8, 4, 4, 4, 2],
      ![2, 14, 8, 3, 9, 6, 1, 3, 2, 8, 5, 2, 6, 4],
      ![2, 5, 10, 9, 3, 6, 3, 1, 2, 3, 6, 6, 2, 4],
      ![4, 10, 5, 6, 6, 3, 2, 2, 1, 6, 3, 4, 4, 2],
      ![3, 2, 4, 10, 4, 8, 8, 3, 6, 1, 2, 5, 2, 4],
      ![5, 4, 2, 6, 8, 4, 5, 6, 3, 2, 1, 3, 4, 2],
      ![4, 10, 6, 2, 6, 4, 2, 6, 4, 5, 3, 1, 3, 2],
      ![6, 4, 8, 6, 2, 4, 6, 2, 4, 2, 4, 3, 1, 2],
      ![14, 8, 4, 4, 4, 2, 4, 4, 2, 4, 2, 2, 2, 1]],
    ![![1, 3, 6, 3, 6, 17, 3, 3, 9, 6, 14, 9, 17, 57],
      ![3, 1, 3, 14, 3, 9, 73, 14, 42, 3, 9, 42, 9, 27],
      ![6, 3, 1, 6, 9, 3, 31, 42, 14, 9, 3, 18, 27, 9],
      ![3, 14, 6, 1, 6, 3, 6, 36, 18, 42, 18, 3, 18, 9],
      ![6, 3, 9, 6, 1, 3, 36, 6, 18, 9, 27, 18, 3, 9],
      ![17, 9, 3, 3, 3, 1, 18, 18, 6, 27, 9, 9, 9, 3],
      ![3, 73, 31, 6, 36, 18, 1, 6, 3, 31, 14, 3, 18, 9],
      ![3, 14, 42, 36, 6, 18, 6, 1, 3, 6, 18, 18, 3, 9],
      ![9, 42, 14, 18, 18, 6, 3, 3, 1, 18, 6, 9, 9, 3],
      ![6, 3, 9, 42, 9, 27, 31, 6, 18, 1, 3, 14, 3, 9],
      ![14, 9, 3, 18, 27, 9, 14, 18, 6, 3, 1, 6, 9, 3],
      ![9, 42, 18, 3, 18, 9, 3, 18, 9, 14, 6, 1, 6, 3],
      ![17, 9, 27, 18, 3, 9, 18, 3, 9, 3, 9, 6, 1, 3],
      ![57, 27, 9, 9, 9, 3, 9, 9, 3, 9, 3, 3, 3, 1]],
    ![![1, 4, 10, 4, 10, 36, 4, 4, 16, 10, 30, 16, 36, 154],
      ![4, 1, 4, 30, 4, 16, 252, 30, 120, 4, 16, 120, 16, 64],
      ![10, 4, 1, 10, 16, 4, 85, 120, 30, 16, 4, 40, 64, 16],
      ![4, 30, 10, 1, 10, 4, 10, 100, 40, 120, 40, 4, 40, 16],
      ![10, 4, 16, 10, 1, 4, 100, 10, 40, 16, 64, 40, 4, 16],
      ![36, 16, 4, 4, 4, 1, 40, 40, 10, 64, 16, 16, 16, 4],
      ![4, 252, 85, 10, 100, 40, 1, 10, 4, 85, 30, 4, 40, 16],
      ![4, 30, 120, 100, 10, 40, 10, 1, 4, 10, 40, 40, 4, 16],
      ![16, 120, 30, 40, 40, 10, 4, 4, 1, 40, 10, 16, 16, 4],
      ![10, 4, 16, 120, 16, 64, 85, 10, 40, 1, 4, 30, 4, 16],
      ![30, 16, 4, 40, 64, 16, 30, 40, 10, 4, 1, 10, 16, 4],
      ![16, 120, 40, 4, 40, 16, 4, 40, 16, 30, 10, 1, 10, 4],
      ![36, 16, 64, 40, 4, 16, 40, 4, 16, 4, 16, 10, 1, 4],
      ![154, 64, 16, 16, 16, 4, 16, 16, 4, 16, 4, 4, 4, 1]],
    ![![1, 5, 15, 5, 15, 65, 5, 5, 25, 15, 55, 25, 65, 335],
      ![5, 1, 5, 55, 5, 25, 681, 55, 275, 5, 25, 275, 25, 125],
      ![15, 5, 1, 15, 25, 5, 190, 275, 55, 25, 5, 75, 125, 25],
      ![5, 55, 15, 1, 15, 5, 15, 225, 75, 275, 75, 5, 75, 25],
      ![15, 5, 25, 15, 1, 5, 225, 15, 75, 25, 125, 75, 5, 25],
      ![65, 25, 5, 5, 5, 1, 75, 75, 15, 125, 25, 25, 25, 5],
      ![5, 681, 190, 15, 225, 75, 1, 15, 5, 190, 55, 5, 75, 25],
      ![5, 55, 275, 225, 15, 75, 15, 1, 5, 15, 75, 75, 5, 25],
      ![25, 275, 55, 75, 75, 15, 5, 5, 1, 75, 15, 25, 25, 5],
      ![15, 5, 25, 275, 25, 125, 190, 15, 75, 1, 5, 55, 5, 25],
      ![55, 25, 5, 75, 125, 25, 55, 75, 15, 5, 1, 15, 25, 5],
      ![25, 275, 75, 5, 75, 25, 5, 75, 25, 55, 15, 1, 15, 5],
      ![65, 25, 125, 75, 5, 25, 75, 5, 25, 5, 25, 15, 1, 5],
      ![335, 125, 25, 25, 25, 5, 25, 25, 5, 25, 5, 5, 5, 1]],
    ![![1, 6, 21, 6, 21, 106, 6, 6, 36, 21, 91, 36, 106, 636],
      ![6, 1, 6, 91, 6, 36, 1562, 91, 546, 6, 36, 546, 36, 216],
      ![21, 6, 1, 21, 36, 6, 371, 546, 91, 36, 6, 126, 216, 36],
      ![6, 91, 21, 1, 21, 6, 21, 441, 126, 546, 126, 6, 126, 36],
      ![21, 6, 36, 21, 1, 6, 441, 21, 126, 36, 216, 126, 6, 36],
      ![106, 36, 6, 6, 6, 1, 126, 126, 21, 216, 36, 36, 36, 6],
      ![6, 1562, 371, 21, 441, 126, 1, 21, 6, 371, 91, 6, 126, 36],
      ![6, 91, 546, 441, 21, 126, 21, 1, 6, 21, 126, 126, 6, 36],
      ![36, 546, 91, 126, 126, 21, 6, 6, 1, 126, 21, 36, 36, 6],
      ![21, 6, 36, 546, 36, 216, 371, 21, 126, 1, 6, 91, 6, 36],
      ![91, 36, 6, 126, 216, 36, 91, 126, 21, 6, 1, 21, 36, 6],
      ![36, 546, 126, 6, 126, 36, 6, 126, 36, 91, 21, 1, 21, 6],
      ![106, 36, 216, 126, 6, 36, 126, 6, 36, 6, 36, 21, 1, 6],
      ![636, 216, 36, 36, 36, 6, 36, 36, 6, 36, 6, 6, 6, 1]],
    ![![1, 7, 28, 7, 28, 161, 7, 7, 49, 28, 140, 49, 161, 1099],
      ![7, 1, 7, 140, 7, 49, 3185, 140, 980, 7, 49, 980, 49, 343],
      ![28, 7, 1, 28, 49, 7, 658, 980, 140, 49, 7, 196, 343, 49],
      ![7, 140, 28, 1, 28, 7, 28, 784, 196, 980, 196, 7, 196, 49],
      ![28, 7, 49, 28, 1, 7, 784, 28, 196, 49, 343, 196, 7, 49],
      ![161, 49, 7, 7, 7, 1, 196, 196, 28, 343, 49, 49, 49, 7],
      ![7, 3185, 658, 28, 784, 196, 1, 28, 7, 658, 140, 7, 196, 49],
      ![7, 140, 980, 784, 28, 196, 28, 1, 7, 28, 196, 196, 7, 49],
      ![49, 980, 140, 196, 196, 28, 7, 7, 1, 196, 28, 49, 49, 7],
      ![28, 7, 49, 980, 49, 343, 658, 28, 196, 1, 7, 140, 7, 49],
      ![140, 49, 7, 196, 343, 49, 140, 196, 28, 7, 1, 28, 49, 7],
      ![49, 980, 196, 7, 196, 49, 7, 196, 49, 140, 28, 1, 28, 7],
      ![161, 49, 343, 196, 7, 49, 196, 7, 49, 7, 49, 28, 1, 7],
      ![1099, 343, 49, 49, 49, 7, 49, 49, 7, 49, 7, 7, 7, 1]]]

private def initial (k : Fin 7) (p q : Row) : ℤ := table k (code p) (code q)

private theorem table_step : ∀ k : Fin 6, ∀ p q : Legal,
    initial k.succ p.val q.val = step (initial k.castSucc) p.val q.val := by decide +kernel

private theorem initial_eq (k : Fin 7) : ∀ p q : Legal,
    v k.val p.val q.val = initial k p.val q.val := by
  induction k using Fin.induction with
  | zero =>
    rw [Fin.val_zero,zero_v]
    decide +kernel
  | succ k ih =>
    intro p q
    rw [Fin.val_succ,succ_v,table_step]
    apply Finset.sum_congr rfl
    intro r _
    exact ih q ⟨r.val,r.property.1⟩

private theorem differences (n : ℕ) : ∀ p q : Legal,
    v (n+6) p.val q.val = 6*v (n+5) p.val q.val - 15*v (n+4) p.val q.val + 20*v (n+3) p.val q.val - 15*v (n+2) p.val q.val + 6*v (n+1) p.val q.val - v n p.val q.val := by
  induction n with
  | zero =>
    intro p q
    have e0 : v 0 p.val q.val = initial 0 p.val q.val := initial_eq 0 p q
    have e1 : v 1 p.val q.val = initial 1 p.val q.val := initial_eq 1 p q
    have e2 : v 2 p.val q.val = initial 2 p.val q.val := initial_eq 2 p q
    have e3 : v 3 p.val q.val = initial 3 p.val q.val := initial_eq 3 p q
    have e4 : v 4 p.val q.val = initial 4 p.val q.val := initial_eq 4 p q
    have e5 : v 5 p.val q.val = initial 5 p.val q.val := initial_eq 5 p q
    have e6 : v 6 p.val q.val = initial 6 p.val q.val := initial_eq 6 p q
    simp only [Nat.zero_add,e0,e1,e2,e3,e4,e5,e6]
    clear e0 e1 e2 e3 e4 e5 e6
    revert p q
    decide +kernel
  | succ n ih =>
    intro p q
    change v ((n+6)+1) p.val q.val = _
    rw [succ_v (n+6)]
    unfold step
    rw [Finset.sum_congr rfl (fun r _ => ih q ⟨r.val,r.property.1⟩)]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
    have sum_v (t : ℕ) :
        (∑ r : {r : Row // legal r ∧ next p.val q.val r}, v t q.val r.val) =
          v (t+1) p.val q.val := (congrFun (congrFun (succ_v t) p.val) q.val).symm
    simp only [sum_v]

private theorem initial_total (k : Fin 7) :
    total (v k.val) = total (initial k) := by
  unfold total
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  exact fun q _ => initial_eq k p q

private theorem counts : ∀ k : Fin 7, total (initial k) =
    ![196, 844, 2422, 5594, 11256, 20568, 34986] k := by decide +kernel

private theorem first : a 1 = 14 := by decide +kernel

private theorem term2 : a 2 = 196 :=
  (value 0).trans ((initial_total 0).trans (counts 0))

private theorem term3 : a 3 = 844 :=
  (value 1).trans ((initial_total 1).trans (counts 1))

private theorem term4 : a 4 = 2422 :=
  (value 2).trans ((initial_total 2).trans (counts 2))

private theorem term5 : a 5 = 5594 :=
  (value 3).trans ((initial_total 3).trans (counts 3))

private theorem term6 : a 6 = 11256 :=
  (value 4).trans ((initial_total 4).trans (counts 4))

private theorem term7 : a 7 = 20568 :=
  (value 5).trans ((initial_total 5).trans (counts 5))

private theorem recurrence (n : ℕ) (hn : 7 ≤ n) :
    (a n : ℚ) = 6*(a (n-1) : ℚ) - 15*(a (n-2) : ℚ) + 20*(a (n-3) : ℚ) - 15*(a (n-4) : ℚ) + 6*(a (n-5) : ℚ) - (a (n-6) : ℚ) := by
  by_cases he : n = 7
  · subst n
    norm_num [first,term2,term3,term4,term5,term6,term7]
  obtain ⟨m,rfl⟩ : ∃ m, n = m+8 := ⟨n-8,by omega⟩
  have h : total (v (m+6)) = 6*total (v (m+5)) - 15*total (v (m+4)) + 20*total (v (m+3)) - 15*total (v (m+2)) + 6*total (v (m+1)) - total (v m) := by
    unfold total
    conv_lhs =>
      enter [2,p,2,q]
      rw [differences m p q]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum]
  exact_mod_cast (show a (m+8) = _ from by simpa [value] using h)

private theorem generating :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 6 : PowerSeries ℚ) = 2 * X * (7 + 56 * X - 61 * X ^ 2 + 9 * X ^ 3 + 6 * X ^ 4 - X ^ 5) := by
  let S := mk (fun n => if n < 1 then 0 else (a n : ℚ))
  change S * _ = _
  have lhs : S*(1-X)^6 = S - (6:ℕ) • (S*X^1) + (15:ℕ) • (S*X^2) - (20:ℕ) • (S*X^3) + (15:ℕ) • (S*X^4) - (6:ℕ) • (S*X^5) + (S*X^6) := by simp only [nsmul_eq_mul]; ring
  have rhs : (2 * X * (7 + 56 * X - 61 * X ^ 2 + 9 * X ^ 3 + 6 * X ^ 4 - X ^ 5) : PowerSeries ℚ) = (14:ℕ) • X^1 + (112:ℕ) • X^2 - (122:ℕ) • X^3 + (18:ℕ) • X^4 + (12:ℕ) • X^5 - (2:ℕ) • X^6 := by simp only [nsmul_eq_mul]; ring
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
      if_neg (show n ≠ 5 by omega),
      if_neg (show n ≠ 6 by omega)]
    norm_num
    linarith
  · interval_cases n <;> norm_num [first,term2,term3,term4,term5,term6]

private theorem formula (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = (30 - 149 * (n : ℚ) + 10 * (n : ℚ) ^ 2 + 250 * (n : ℚ) ^ 3 + 65 * (n : ℚ) ^ 4 + 4 * (n : ℚ) ^ 5) / 15 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n ≤ 6
    · interval_cases n <;> norm_num [first,term2,term3,term4,term5,term6]
    rw [recurrence n (by omega),ih (n-1) (by omega) (by omega),
      ih (n-2) (by omega) (by omega),
      ih (n-3) (by omega) (by omega),
      ih (n-4) (by omega) (by omega),
      ih (n-5) (by omega) (by omega),
      ih (n-6) (by omega) (by omega)]
    obtain ⟨m,rfl⟩ : ∃ m, n=m+7 := ⟨n-7,by omega⟩
    simp only [show m+7-1 = m+6 by omega,show m+7-2 = m+5 by omega,show m+7-3 = m+4 by omega,show m+7-4 = m+3 by omega,show m+7-5 = m+2 by omega,show m+7-6 = m+1 by omega]
    push_cast
    ring

theorem result : type_of% @OMA.S_oeis_a207935.main := ⟨generating,formula⟩

end OMA.Arrays207935

theorem OMA.solution : type_of% @OMA.S_oeis_a207935.main := OMA.Arrays207935.result
