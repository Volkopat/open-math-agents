import OMAStatements.S_oeis_a207388
import Mathlib

namespace OMA.Arrays207388

open OMA.S_oeis_a207388
open PowerSeries

private abbrev Row := Fin 5 → Fin 2

private def legal (r : Row) : Prop := ∀ j : Fin 3,
  let t := ((r ⟨j, by omega⟩).val, (r ⟨j+1, by omega⟩).val, (r ⟨j+2, by omega⟩).val)
  t ≠ (0,0,1) ∧ t ≠ (0,1,0)

private instance (r : Row) : Decidable (legal r) := by unfold legal; infer_instance

private theorem horizontal {n : ℕ} (x : Fin n → Row) :
    (∀ i < n, ∀ j < 5-2,
      (get x i j, get x i (j+1), get x i (j+2)) ≠ (0,0,1) ∧
      (get x i j, get x i (j+1), get x i (j+2)) ≠ (0,1,0)) ↔ ∀ i, legal (x i) := by
  constructor
  · intro h i j
    simpa [OMA.S_oeis_a207388.get, i.isLt, show j.val < 5 by omega, show j.val+1 < 5 by omega,
      show j.val+2 < 5 by omega] using h i i.isLt j j.isLt
  · intro h i hi j hj
    simpa [OMA.S_oeis_a207388.get, hi, show j < 5 by omega, show j+1 < 5 by omega, show j+2 < 5 by omega]
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
    simpa [OMA.S_oeis_a207388.get,j.isLt,show i.val < n+2 by omega,
      show i.val+1 < n+2 by omega,show i.val+2 < n+2 by omega] using h i (by omega) j j.isLt
  · intro h i hi j hj
    have hh := (bits _ _ _).mpr (h ⟨i,by omega⟩ ⟨j,hj⟩)
    simpa [OMA.S_oeis_a207388.get,hj,show i < n+2 by omega,
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
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 0, 0, 0, 0, 0, 6, 7, 8, 0, 0, 9, 10, 11, 12, 13] (rowIndex r)

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
    ![![1, 2, 3, 3, 5, 2, 3, 4, 3, 4, 5, 7, 8, 14],
      ![2, 1, 2, 2, 4, 5, 5, 10, 3, 10, 2, 4, 4, 8],
      ![3, 2, 1, 4, 2, 7, 10, 5, 5, 5, 4, 2, 8, 4],
      ![3, 2, 4, 1, 2, 8, 3, 6, 5, 5, 4, 8, 2, 4],
      ![5, 4, 2, 2, 1, 14, 6, 3, 10, 3, 8, 4, 4, 2],
      ![2, 5, 7, 8, 14, 1, 2, 3, 2, 3, 3, 4, 5, 9],
      ![3, 5, 10, 3, 6, 2, 1, 2, 5, 5, 3, 6, 2, 4],
      ![4, 10, 5, 6, 3, 3, 2, 1, 9, 3, 6, 3, 4, 2],
      ![3, 3, 5, 5, 10, 2, 5, 9, 1, 2, 2, 3, 3, 6],
      ![4, 10, 5, 5, 3, 3, 5, 3, 2, 1, 6, 3, 3, 2],
      ![5, 2, 4, 4, 8, 3, 3, 6, 2, 6, 1, 2, 2, 4],
      ![7, 4, 2, 8, 4, 4, 6, 3, 3, 3, 2, 1, 4, 2],
      ![8, 4, 8, 2, 4, 5, 2, 4, 3, 3, 2, 4, 1, 2],
      ![14, 8, 4, 4, 2, 9, 4, 2, 6, 2, 4, 2, 2, 1]],
    ![![1, 3, 6, 6, 14, 3, 6, 10, 6, 10, 13, 23, 27, 64],
      ![3, 1, 3, 3, 9, 13, 14, 42, 6, 40, 3, 9, 9, 27],
      ![6, 3, 1, 9, 3, 24, 42, 14, 14, 14, 9, 3, 27, 9],
      ![6, 3, 9, 1, 3, 28, 6, 18, 14, 14, 9, 27, 3, 9],
      ![14, 9, 3, 3, 1, 68, 18, 6, 40, 6, 27, 9, 9, 3],
      ![3, 13, 24, 28, 68, 1, 3, 6, 3, 6, 6, 10, 13, 32],
      ![6, 14, 42, 6, 18, 3, 1, 3, 13, 14, 6, 18, 3, 9],
      ![10, 42, 14, 18, 6, 6, 3, 1, 33, 6, 18, 6, 9, 3],
      ![6, 6, 14, 14, 40, 3, 13, 33, 1, 3, 3, 6, 6, 17],
      ![10, 40, 14, 14, 6, 6, 14, 6, 3, 1, 17, 6, 6, 3],
      ![13, 3, 9, 9, 27, 6, 6, 18, 3, 17, 1, 3, 3, 9],
      ![23, 9, 3, 27, 9, 10, 18, 6, 6, 6, 3, 1, 9, 3],
      ![27, 9, 27, 3, 9, 13, 3, 9, 6, 6, 3, 9, 1, 3],
      ![64, 27, 9, 9, 3, 32, 9, 3, 17, 3, 9, 3, 3, 1]],
    ![![1, 4, 10, 10, 30, 4, 10, 20, 10, 20, 26, 55, 65, 192],
      ![4, 1, 4, 4, 16, 26, 30, 120, 10, 110, 4, 16, 16, 64],
      ![10, 4, 1, 16, 4, 60, 120, 30, 30, 30, 16, 4, 64, 16],
      ![10, 4, 16, 1, 4, 70, 10, 40, 30, 30, 16, 64, 4, 16],
      ![30, 16, 4, 4, 1, 216, 40, 10, 110, 10, 64, 16, 16, 4],
      ![4, 26, 60, 70, 216, 1, 4, 10, 4, 10, 10, 20, 26, 80],
      ![10, 30, 120, 10, 40, 4, 1, 4, 26, 30, 10, 40, 4, 16],
      ![20, 120, 30, 40, 10, 10, 4, 1, 85, 10, 40, 10, 16, 4],
      ![10, 10, 30, 30, 110, 4, 26, 85, 1, 4, 4, 10, 10, 36],
      ![20, 110, 30, 30, 10, 10, 30, 10, 4, 1, 36, 10, 10, 4],
      ![26, 4, 16, 16, 64, 10, 10, 40, 4, 36, 1, 4, 4, 16],
      ![55, 16, 4, 64, 16, 20, 40, 10, 10, 10, 4, 1, 16, 4],
      ![65, 16, 64, 4, 16, 26, 4, 16, 10, 10, 4, 16, 1, 4],
      ![192, 64, 16, 16, 4, 80, 16, 4, 36, 4, 16, 4, 4, 1]],
    ![![1, 5, 15, 15, 55, 5, 15, 35, 15, 35, 45, 110, 130, 457],
      ![5, 1, 5, 5, 25, 45, 55, 275, 15, 245, 5, 25, 25, 125],
      ![15, 5, 1, 25, 5, 125, 275, 55, 55, 55, 25, 5, 125, 25],
      ![15, 5, 25, 1, 5, 145, 15, 75, 55, 55, 25, 125, 5, 25],
      ![55, 25, 5, 5, 1, 541, 75, 15, 245, 15, 125, 25, 25, 5],
      ![5, 45, 125, 145, 541, 1, 5, 15, 5, 15, 15, 35, 45, 165],
      ![15, 55, 275, 15, 75, 5, 1, 5, 45, 55, 15, 75, 5, 25],
      ![35, 275, 55, 75, 15, 15, 5, 1, 180, 15, 75, 15, 25, 5],
      ![15, 15, 55, 55, 245, 5, 45, 180, 1, 5, 5, 15, 15, 65],
      ![35, 245, 55, 55, 15, 15, 55, 15, 5, 1, 65, 15, 15, 5],
      ![45, 5, 25, 25, 125, 15, 15, 75, 5, 65, 1, 5, 5, 25],
      ![110, 25, 5, 125, 25, 35, 75, 15, 15, 15, 5, 1, 25, 5],
      ![130, 25, 125, 5, 25, 45, 5, 25, 15, 15, 5, 25, 1, 5],
      ![457, 125, 25, 25, 5, 165, 25, 5, 65, 5, 25, 5, 5, 1]],
    ![![1, 6, 21, 21, 91, 6, 21, 56, 21, 56, 71, 196, 231, 938],
      ![6, 1, 6, 6, 36, 71, 91, 546, 21, 476, 6, 36, 36, 216],
      ![21, 6, 1, 36, 6, 231, 546, 91, 91, 91, 36, 6, 216, 36],
      ![21, 6, 36, 1, 6, 266, 21, 126, 91, 91, 36, 216, 6, 36],
      ![91, 36, 6, 6, 1, 1162, 126, 21, 476, 21, 216, 36, 36, 6],
      ![6, 71, 231, 266, 1162, 1, 6, 21, 6, 21, 21, 56, 71, 301],
      ![21, 91, 546, 21, 126, 6, 1, 6, 71, 91, 21, 126, 6, 36],
      ![56, 546, 91, 126, 21, 21, 6, 1, 336, 21, 126, 21, 36, 6],
      ![21, 21, 91, 91, 476, 6, 71, 336, 1, 6, 6, 21, 21, 106],
      ![56, 476, 91, 91, 21, 21, 91, 21, 6, 1, 106, 21, 21, 6],
      ![71, 6, 36, 36, 216, 21, 21, 126, 6, 106, 1, 6, 6, 36],
      ![196, 36, 6, 216, 36, 56, 126, 21, 21, 21, 6, 1, 36, 6],
      ![231, 36, 216, 6, 36, 71, 6, 36, 21, 21, 6, 36, 1, 6],
      ![938, 216, 36, 36, 6, 301, 36, 6, 106, 6, 36, 6, 6, 1]],
    ![![1, 7, 28, 28, 140, 7, 28, 84, 28, 84, 105, 322, 378, 1736],
      ![7, 1, 7, 7, 49, 105, 140, 980, 28, 840, 7, 49, 49, 343],
      ![28, 7, 1, 49, 7, 392, 980, 140, 140, 140, 49, 7, 343, 49],
      ![28, 7, 49, 1, 7, 448, 28, 196, 140, 140, 49, 343, 7, 49],
      ![140, 49, 7, 7, 1, 2240, 196, 28, 840, 28, 343, 49, 49, 7],
      ![7, 105, 392, 448, 2240, 1, 7, 28, 7, 28, 28, 84, 105, 504],
      ![28, 140, 980, 28, 196, 7, 1, 7, 105, 140, 28, 196, 7, 49],
      ![84, 980, 140, 196, 28, 28, 7, 1, 574, 28, 196, 28, 49, 7],
      ![28, 28, 140, 140, 840, 7, 105, 574, 1, 7, 7, 28, 28, 161],
      ![84, 840, 140, 140, 28, 28, 140, 28, 7, 1, 161, 28, 28, 7],
      ![105, 7, 49, 49, 343, 28, 28, 196, 7, 161, 1, 7, 7, 49],
      ![322, 49, 7, 343, 49, 84, 196, 28, 28, 28, 7, 1, 49, 7],
      ![378, 49, 343, 7, 49, 105, 7, 49, 28, 28, 7, 49, 1, 7],
      ![1736, 343, 49, 49, 7, 504, 49, 7, 161, 7, 49, 7, 7, 1]]]

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
    ![196, 834, 2356, 5348, 10570, 18972, 31710] k := by decide +kernel

private theorem first : a 1 = 14 := by decide +kernel

private theorem term2 : a 2 = 196 :=
  (value 0).trans ((initial_total 0).trans (counts 0))

private theorem term3 : a 3 = 834 :=
  (value 1).trans ((initial_total 1).trans (counts 1))

private theorem term4 : a 4 = 2356 :=
  (value 2).trans ((initial_total 2).trans (counts 2))

private theorem term5 : a 5 = 5348 :=
  (value 3).trans ((initial_total 3).trans (counts 3))

private theorem term6 : a 6 = 10570 :=
  (value 4).trans ((initial_total 4).trans (counts 4))

private theorem term7 : a 7 = 18972 :=
  (value 5).trans ((initial_total 5).trans (counts 5))

private theorem recurrence (n : ℕ) (hn : 7 ≤ n) :
    (a n : ℚ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
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
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 6 : PowerSeries ℚ) = 2 * X * (7 + 56 * X - 66 * X ^ 2 + 6 * X ^ 3 + 6 * X ^ 4 - X ^ 5) := by
  let S := mk (fun n => if n < 1 then 0 else (a n : ℚ))
  change S * _ = _
  have lhs : S*(1-X)^6 = S - (6:ℕ) • (S*X^1) + (15:ℕ) • (S*X^2) - (20:ℕ) • (S*X^3) + (15:ℕ) • (S*X^4) - (6:ℕ) • (S*X^5) + (S*X^6) := by simp only [nsmul_eq_mul]; ring
  have rhs : (2 * X * (7 + 56 * X - 66 * X ^ 2 + 6 * X ^ 3 + 6 * X ^ 4 - X ^ 5) : PowerSeries ℚ) = (14:ℕ) • X^1 + (112:ℕ) • X^2 - (132:ℕ) • X^3 + (12:ℕ) • X^4 + (12:ℕ) • X^5 - (2:ℕ) • X^6 := by simp only [nsmul_eq_mul]; ring
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

theorem result : type_of% @OMA.S_oeis_a207388.main := ⟨generating,recurrence⟩

end OMA.Arrays207388

theorem OMA.solution : type_of% @OMA.S_oeis_a207388.main := OMA.Arrays207388.result
