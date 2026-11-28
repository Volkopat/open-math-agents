import OMAStatements.S_oeis_a207700
import Mathlib

namespace OMA.Arrays207700

open OMA.S_oeis_a207700
open PowerSeries

private abbrev Row := Fin 5 → Fin 2

private def legal (r : Row) : Prop := ∀ j : Fin 3,
  let t := ((r ⟨j, by omega⟩).val, (r ⟨j+1, by omega⟩).val, (r ⟨j+2, by omega⟩).val)
  t ≠ (0,0,0) ∧ t ≠ (0,1,0)

private instance (r : Row) : Decidable (legal r) := by unfold legal; infer_instance

private theorem horizontal {n : ℕ} (x : Fin n → Row) :
    (∀ i < n, ∀ j < 5-2,
      (get x i j, get x i (j+1), get x i (j+2)) ≠ (0,0,0) ∧
      (get x i j, get x i (j+1), get x i (j+2)) ≠ (0,1,0)) ↔ ∀ i, legal (x i) := by
  constructor
  · intro h i j
    simpa [OMA.S_oeis_a207700.get, i.isLt, show j.val < 5 by omega, show j.val+1 < 5 by omega,
      show j.val+2 < 5 by omega] using h i i.isLt j j.isLt
  · intro h i hi j hj
    simpa [OMA.S_oeis_a207700.get, hi, show j < 5 by omega, show j+1 < 5 by omega, show j+2 < 5 by omega]
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
    simpa [OMA.S_oeis_a207700.get,j.isLt,show i.val < n+2 by omega,
      show i.val+1 < n+2 by omega,show i.val+2 < n+2 by omega] using h i (by omega) j j.isLt
  · intro h i hi j hj
    have hh := (bits _ _ _).mpr (h ⟨i,by omega⟩ ⟨j,hj⟩)
    simpa [OMA.S_oeis_a207700.get,hj,show i < n+2 by omega,
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

private def code (r : Row) : Fin 15 :=
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 3, 4, 5, 0, 0, 0, 6, 0, 0, 7, 8, 0, 9, 0, 10, 11, 12, 13, 14] (rowIndex r)

private def table : Fin 7 → Fin 15 → Fin 15 → ℤ :=
  ![![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]],
    ![![1, 2, 3, 6, 2, 4, 5, 2, 4, 15, 10, 6, 12, 4, 8],
      ![2, 1, 6, 3, 4, 2, 3, 4, 2, 9, 6, 12, 6, 8, 4],
      ![3, 6, 1, 2, 2, 4, 15, 6, 12, 5, 10, 2, 4, 4, 8],
      ![6, 3, 2, 1, 4, 2, 9, 12, 6, 3, 6, 4, 2, 8, 4],
      ![2, 4, 2, 4, 1, 2, 10, 4, 8, 10, 5, 4, 8, 2, 4],
      ![4, 2, 4, 2, 2, 1, 6, 8, 4, 6, 3, 8, 4, 4, 2],
      ![5, 3, 15, 9, 10, 6, 1, 3, 2, 3, 2, 9, 6, 6, 4],
      ![2, 4, 6, 12, 4, 8, 3, 1, 2, 9, 6, 3, 6, 2, 4],
      ![4, 2, 12, 6, 8, 4, 2, 2, 1, 6, 4, 6, 3, 4, 2],
      ![15, 9, 5, 3, 10, 6, 3, 9, 6, 1, 2, 3, 2, 6, 4],
      ![10, 6, 10, 6, 5, 3, 2, 6, 4, 2, 1, 6, 4, 3, 2],
      ![6, 12, 2, 4, 4, 8, 9, 3, 6, 3, 6, 1, 2, 2, 4],
      ![12, 6, 4, 2, 8, 4, 6, 6, 3, 2, 4, 2, 1, 4, 2],
      ![4, 8, 4, 8, 2, 4, 6, 2, 4, 6, 3, 2, 4, 1, 2],
      ![8, 4, 8, 4, 4, 2, 4, 4, 2, 4, 2, 4, 2, 2, 1]],
    ![![1, 3, 6, 18, 3, 9, 14, 3, 9, 84, 42, 18, 54, 9, 27],
      ![3, 1, 18, 6, 9, 3, 6, 9, 3, 36, 18, 54, 18, 27, 9],
      ![6, 18, 1, 3, 3, 9, 84, 18, 54, 14, 42, 3, 9, 9, 27],
      ![18, 6, 3, 1, 9, 3, 36, 54, 18, 6, 18, 9, 3, 27, 9],
      ![3, 9, 3, 9, 1, 3, 42, 9, 27, 42, 14, 9, 27, 3, 9],
      ![9, 3, 9, 3, 3, 1, 18, 27, 9, 18, 6, 27, 9, 9, 3],
      ![14, 6, 84, 36, 42, 18, 1, 6, 3, 6, 3, 36, 18, 18, 9],
      ![3, 9, 18, 54, 9, 27, 6, 1, 3, 36, 18, 6, 18, 3, 9],
      ![9, 3, 54, 18, 27, 9, 3, 3, 1, 18, 9, 18, 6, 9, 3],
      ![84, 36, 14, 6, 42, 18, 6, 36, 18, 1, 3, 6, 3, 18, 9],
      ![42, 18, 42, 18, 14, 6, 3, 18, 9, 3, 1, 18, 9, 6, 3],
      ![18, 54, 3, 9, 9, 27, 36, 6, 18, 6, 18, 1, 3, 3, 9],
      ![54, 18, 9, 3, 27, 9, 18, 18, 6, 3, 9, 3, 1, 9, 3],
      ![9, 27, 9, 27, 3, 9, 18, 3, 9, 18, 6, 3, 9, 1, 3],
      ![27, 9, 27, 9, 9, 3, 9, 9, 3, 9, 3, 9, 3, 3, 1]],
    ![![1, 4, 10, 40, 4, 16, 30, 4, 16, 300, 120, 40, 160, 16, 64],
      ![4, 1, 40, 10, 16, 4, 10, 16, 4, 100, 40, 160, 40, 64, 16],
      ![10, 40, 1, 4, 4, 16, 300, 40, 160, 30, 120, 4, 16, 16, 64],
      ![40, 10, 4, 1, 16, 4, 100, 160, 40, 10, 40, 16, 4, 64, 16],
      ![4, 16, 4, 16, 1, 4, 120, 16, 64, 120, 30, 16, 64, 4, 16],
      ![16, 4, 16, 4, 4, 1, 40, 64, 16, 40, 10, 64, 16, 16, 4],
      ![30, 10, 300, 100, 120, 40, 1, 10, 4, 10, 4, 100, 40, 40, 16],
      ![4, 16, 40, 160, 16, 64, 10, 1, 4, 100, 40, 10, 40, 4, 16],
      ![16, 4, 160, 40, 64, 16, 4, 4, 1, 40, 16, 40, 10, 16, 4],
      ![300, 100, 30, 10, 120, 40, 10, 100, 40, 1, 4, 10, 4, 40, 16],
      ![120, 40, 120, 40, 30, 10, 4, 40, 16, 4, 1, 40, 16, 10, 4],
      ![40, 160, 4, 16, 16, 64, 100, 10, 40, 10, 40, 1, 4, 4, 16],
      ![160, 40, 16, 4, 64, 16, 40, 40, 10, 4, 16, 4, 1, 16, 4],
      ![16, 64, 16, 64, 4, 16, 40, 4, 16, 40, 10, 4, 16, 1, 4],
      ![64, 16, 64, 16, 16, 4, 16, 16, 4, 16, 4, 16, 4, 4, 1]],
    ![![1, 5, 15, 75, 5, 25, 55, 5, 25, 825, 275, 75, 375, 25, 125],
      ![5, 1, 75, 15, 25, 5, 15, 25, 5, 225, 75, 375, 75, 125, 25],
      ![15, 75, 1, 5, 5, 25, 825, 75, 375, 55, 275, 5, 25, 25, 125],
      ![75, 15, 5, 1, 25, 5, 225, 375, 75, 15, 75, 25, 5, 125, 25],
      ![5, 25, 5, 25, 1, 5, 275, 25, 125, 275, 55, 25, 125, 5, 25],
      ![25, 5, 25, 5, 5, 1, 75, 125, 25, 75, 15, 125, 25, 25, 5],
      ![55, 15, 825, 225, 275, 75, 1, 15, 5, 15, 5, 225, 75, 75, 25],
      ![5, 25, 75, 375, 25, 125, 15, 1, 5, 225, 75, 15, 75, 5, 25],
      ![25, 5, 375, 75, 125, 25, 5, 5, 1, 75, 25, 75, 15, 25, 5],
      ![825, 225, 55, 15, 275, 75, 15, 225, 75, 1, 5, 15, 5, 75, 25],
      ![275, 75, 275, 75, 55, 15, 5, 75, 25, 5, 1, 75, 25, 15, 5],
      ![75, 375, 5, 25, 25, 125, 225, 15, 75, 15, 75, 1, 5, 5, 25],
      ![375, 75, 25, 5, 125, 25, 75, 75, 15, 5, 25, 5, 1, 25, 5],
      ![25, 125, 25, 125, 5, 25, 75, 5, 25, 75, 15, 5, 25, 1, 5],
      ![125, 25, 125, 25, 25, 5, 25, 25, 5, 25, 5, 25, 5, 5, 1]],
    ![![1, 6, 21, 126, 6, 36, 91, 6, 36, 1911, 546, 126, 756, 36, 216],
      ![6, 1, 126, 21, 36, 6, 21, 36, 6, 441, 126, 756, 126, 216, 36],
      ![21, 126, 1, 6, 6, 36, 1911, 126, 756, 91, 546, 6, 36, 36, 216],
      ![126, 21, 6, 1, 36, 6, 441, 756, 126, 21, 126, 36, 6, 216, 36],
      ![6, 36, 6, 36, 1, 6, 546, 36, 216, 546, 91, 36, 216, 6, 36],
      ![36, 6, 36, 6, 6, 1, 126, 216, 36, 126, 21, 216, 36, 36, 6],
      ![91, 21, 1911, 441, 546, 126, 1, 21, 6, 21, 6, 441, 126, 126, 36],
      ![6, 36, 126, 756, 36, 216, 21, 1, 6, 441, 126, 21, 126, 6, 36],
      ![36, 6, 756, 126, 216, 36, 6, 6, 1, 126, 36, 126, 21, 36, 6],
      ![1911, 441, 91, 21, 546, 126, 21, 441, 126, 1, 6, 21, 6, 126, 36],
      ![546, 126, 546, 126, 91, 21, 6, 126, 36, 6, 1, 126, 36, 21, 6],
      ![126, 756, 6, 36, 36, 216, 441, 21, 126, 21, 126, 1, 6, 6, 36],
      ![756, 126, 36, 6, 216, 36, 126, 126, 21, 6, 36, 6, 1, 36, 6],
      ![36, 216, 36, 216, 6, 36, 126, 6, 36, 126, 21, 6, 36, 1, 6],
      ![216, 36, 216, 36, 36, 6, 36, 36, 6, 36, 6, 36, 6, 6, 1]],
    ![![1, 7, 28, 196, 7, 49, 140, 7, 49, 3920, 980, 196, 1372, 49, 343],
      ![7, 1, 196, 28, 49, 7, 28, 49, 7, 784, 196, 1372, 196, 343, 49],
      ![28, 196, 1, 7, 7, 49, 3920, 196, 1372, 140, 980, 7, 49, 49, 343],
      ![196, 28, 7, 1, 49, 7, 784, 1372, 196, 28, 196, 49, 7, 343, 49],
      ![7, 49, 7, 49, 1, 7, 980, 49, 343, 980, 140, 49, 343, 7, 49],
      ![49, 7, 49, 7, 7, 1, 196, 343, 49, 196, 28, 343, 49, 49, 7],
      ![140, 28, 3920, 784, 980, 196, 1, 28, 7, 28, 7, 784, 196, 196, 49],
      ![7, 49, 196, 1372, 49, 343, 28, 1, 7, 784, 196, 28, 196, 7, 49],
      ![49, 7, 1372, 196, 343, 49, 7, 7, 1, 196, 49, 196, 28, 49, 7],
      ![3920, 784, 140, 28, 980, 196, 28, 784, 196, 1, 7, 28, 7, 196, 49],
      ![980, 196, 980, 196, 140, 28, 7, 196, 49, 7, 1, 196, 49, 28, 7],
      ![196, 1372, 7, 49, 49, 343, 784, 28, 196, 28, 196, 1, 7, 7, 49],
      ![1372, 196, 49, 7, 343, 49, 196, 196, 28, 7, 49, 7, 1, 49, 7],
      ![49, 343, 49, 343, 7, 49, 196, 7, 49, 196, 28, 7, 49, 1, 7],
      ![343, 49, 343, 49, 49, 7, 49, 49, 7, 49, 7, 49, 7, 7, 1]]]

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
    ![225, 1071, 3321, 8151, 17225, 32775, 57681] k := by decide +kernel

private theorem first : a 1 = 15 := by decide +kernel

private theorem term2 : a 2 = 225 :=
  (value 0).trans ((initial_total 0).trans (counts 0))

private theorem term3 : a 3 = 1071 :=
  (value 1).trans ((initial_total 1).trans (counts 1))

private theorem term4 : a 4 = 3321 :=
  (value 2).trans ((initial_total 2).trans (counts 2))

private theorem term5 : a 5 = 8151 :=
  (value 3).trans ((initial_total 3).trans (counts 3))

private theorem term6 : a 6 = 17225 :=
  (value 4).trans ((initial_total 4).trans (counts 4))

private theorem term7 : a 7 = 32775 :=
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
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 6 : PowerSeries ℚ) = X * (15 + 135 * X - 54 * X ^ 2 - 30 * X ^ 3 + 15 * X ^ 4 - X ^ 5) := by
  let S := mk (fun n => if n < 1 then 0 else (a n : ℚ))
  change S * _ = _
  have lhs : S*(1-X)^6 = S - (6:ℕ) • (S*X^1) + (15:ℕ) • (S*X^2) - (20:ℕ) • (S*X^3) + (15:ℕ) • (S*X^4) - (6:ℕ) • (S*X^5) + (S*X^6) := by simp only [nsmul_eq_mul]; ring
  have rhs : (X * (15 + 135 * X - 54 * X ^ 2 - 30 * X ^ 3 + 15 * X ^ 4 - X ^ 5) : PowerSeries ℚ) = (15:ℕ) • X^1 + (135:ℕ) • X^2 - (54:ℕ) • X^3 - (30:ℕ) • X^4 + (15:ℕ) • X^5 - X^6 := by simp only [nsmul_eq_mul]; ring
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

private theorem formula (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = (3 - 10 * (n : ℚ) - 15 * (n : ℚ) ^ 2 + 44 * (n : ℚ) ^ 3 + 21 * (n : ℚ) ^ 4 + 2 * (n : ℚ) ^ 5) / 3 := by
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

theorem result : type_of% @OMA.S_oeis_a207700.main := ⟨generating,formula⟩

end OMA.Arrays207700

theorem OMA.solution : type_of% @OMA.S_oeis_a207700.main := OMA.Arrays207700.result
