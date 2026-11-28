import OMAStatements.S_oeis_a207400
import Mathlib

/-!
# Proof of OMA.S_oeis_a207400.main

Transfer matrix on pairs of consecutive lines of the array: the number of ways to complete
an array below two given legal lines satisfies, entrywise, the linear recurrence of the
denominator of the generating function; kernel-checked tables give the first values, and
the stated identities follow by induction.
The structure (chain decomposition, tables, entrywise differences) is adapted from
roshanasingh4 merged proof of oeis-a207701 in lefttosolve2/open-math-agents.
-/

namespace OMA.Arr_oeis_a207400

open OMA.S_oeis_a207400
open PowerSeries

private abbrev Row := Fin 5 → Fin 2

private def legal (r : Row) : Prop := ∀ j : Fin 3,
  (((r ⟨j, by omega⟩).val, (r ⟨j+1, by omega⟩).val, (r ⟨j+2, by omega⟩).val) ≠ (0, 0, 1) ∧
   ((r ⟨j, by omega⟩).val, (r ⟨j+1, by omega⟩).val, (r ⟨j+2, by omega⟩).val) ≠ (0, 1, 1))

private instance (r : Row) : Decidable (legal r) := by unfold legal; infer_instance

private def next (p q r : Row) : Prop := ∀ j,
  ((p j).val, (q j).val, (r j).val) ≠ (0, 0, 1) ∧ ((p j).val, (q j).val, (r j).val) ≠ (1, 1, 0)

private instance (p q r : Row) : Decidable (next p q r) := by unfold next; infer_instance

private theorem within {n : ℕ} (x : Fin n → Row) :
    (∀ i < n, ∀ j < 5 - 2,
      (get x i j, get x i (j + 1), get x i (j + 2)) ≠ (0, 0, 1) ∧
      (get x i j, get x i (j + 1), get x i (j + 2)) ≠ (0, 1, 1)) ↔ ∀ i, legal (x i) := by
  constructor
  · intro h i j
    simpa [OMA.S_oeis_a207400.get, i.isLt, show j.val < 5 by omega, show j.val+1 < 5 by omega,
      show j.val+2 < 5 by omega] using h i i.isLt j (by omega)
  · intro h i hi j hj
    simpa [OMA.S_oeis_a207400.get, hi, show j < 5 by omega, show j+1 < 5 by omega, show j+2 < 5 by omega]
      using h ⟨i,hi⟩ ⟨j,by omega⟩

private theorem across {n : ℕ} (x : Fin (n+2) → Row) :
    (∀ i < n+2-2, ∀ j < 5,
      (get x i j, get x (i + 1) j, get x (i + 2) j) ≠ (0, 0, 1) ∧
      (get x i j, get x (i + 1) j, get x (i + 2) j) ≠ (1, 1, 0)) ↔
    ∀ i : Fin n, next (x i.castSucc.castSucc) (x i.castSucc.succ) (x i.succ.succ) := by
  constructor
  · intro h i j
    show ((x ⟨i.val,by omega⟩ j).val, (x ⟨i.val+1,by omega⟩ j).val, (x ⟨i.val+2,by omega⟩ j).val) ≠ (0, 0, 1) ∧
      ((x ⟨i.val,by omega⟩ j).val, (x ⟨i.val+1,by omega⟩ j).val, (x ⟨i.val+2,by omega⟩ j).val) ≠ (1, 1, 0)
    simpa [OMA.S_oeis_a207400.get,j.isLt,show i.val < n+2 by omega,
      show i.val+1 < n+2 by omega,show i.val+2 < n+2 by omega] using h i (by omega) j j.isLt
  · intro h i hi j hj
    have hh := h ⟨i,by omega⟩ ⟨j,hj⟩
    simpa [OMA.S_oeis_a207400.get,hj,show i < n+2 by omega,
      show i+1 < n+2 by omega,show i+2 < n+2 by omega] using hh

private def good {n : ℕ} (p q : Row) (x : Fin n → Row) : Prop :=
  (∀ i, legal (x i)) ∧ (∀ i : Fin n,
    let y : Fin (n+2) → Row := Fin.cons p (Fin.cons q x)
    next (y i.castSucc.castSucc) (y i.castSucc.succ) (x i))

private abbrev Arr (m : ℕ) := Fin m → Row

private def ok {m : ℕ} (x : Arr m) : Bool := avoids x

private theorem array_iff {n : ℕ} (x : Arr (n+2)) :
    ok x = true ↔ legal (x 0) ∧ legal (x 1) ∧ good (x 0) (x 1) (fun i => x i.succ.succ) := by
  have reconstruct : Fin.cons (x 0) (Fin.cons (x 1) (fun i : Fin n => x i.succ.succ)) = x := by
    funext j
    refine Fin.cases rfl (fun i => ?_) j
    exact Fin.cases rfl (fun _ => rfl) i
  simp only [ok,avoids,decide_eq_true_eq,within,across,good,reconstruct]
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
    {x : Arr (n+2) // ok x = true} ≃
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

private theorem card_ok (m : ℕ) : a m = Fintype.card {x : Arr m // ok x = true} := by
  unfold a
  rw [← Fintype.card_subtype]
  rfl

private theorem value (n : ℕ) : a (n+2) = total (v n) := by
  have h := Fintype.card_congr (splitArray n)
  simp only [Fintype.card_sigma] at h
  rw [card_ok, h]
  unfold total v
  push_cast
  rfl

private def rowIndex (r : Row) : Fin 32 :=
  ⟨16*(r 0).val + 8*(r 1).val + 4*(r 2).val + 2*(r 3).val + 1*(r 4).val, by omega⟩

private def code (r : Row) : Fin 12 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 4, 5, 0, 0, 6, 0, 7, 0, 8, 9, 10, 11] (rowIndex r)

private noncomputable def table : Fin 7 → Fin 12 → Fin 12 → ℤ :=
  ![![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]],
    ![![1, 2, 3, 2, 3, 4, 4, 6, 6, 8, 9, 12],
      ![2, 1, 2, 4, 6, 8, 2, 4, 3, 4, 6, 8],
      ![3, 2, 1, 6, 9, 12, 4, 2, 6, 8, 3, 4],
      ![2, 4, 6, 1, 2, 3, 2, 3, 4, 6, 6, 9],
      ![3, 6, 9, 2, 1, 2, 4, 6, 2, 4, 3, 6],
      ![4, 8, 12, 3, 2, 1, 6, 9, 4, 2, 6, 3],
      ![4, 2, 4, 2, 4, 6, 1, 2, 2, 3, 4, 6],
      ![6, 4, 2, 3, 6, 9, 2, 1, 4, 6, 2, 3],
      ![6, 3, 6, 4, 2, 4, 2, 4, 1, 2, 2, 4],
      ![8, 4, 8, 6, 4, 2, 3, 6, 2, 1, 4, 2],
      ![9, 6, 3, 6, 3, 6, 4, 2, 2, 4, 1, 2],
      ![12, 8, 4, 9, 6, 3, 6, 3, 4, 2, 2, 1]],
    ![![1, 3, 6, 3, 6, 10, 9, 18, 18, 30, 36, 60],
      ![3, 1, 3, 9, 18, 30, 3, 9, 6, 10, 18, 30],
      ![6, 3, 1, 18, 36, 60, 9, 3, 18, 30, 6, 10],
      ![3, 9, 18, 1, 3, 6, 3, 6, 9, 18, 18, 36],
      ![6, 18, 36, 3, 1, 3, 9, 18, 3, 9, 6, 18],
      ![10, 30, 60, 6, 3, 1, 18, 36, 9, 3, 18, 6],
      ![9, 3, 9, 3, 9, 18, 1, 3, 3, 6, 9, 18],
      ![18, 9, 3, 6, 18, 36, 3, 1, 9, 18, 3, 6],
      ![18, 6, 18, 9, 3, 9, 3, 9, 1, 3, 3, 9],
      ![30, 10, 30, 18, 9, 3, 6, 18, 3, 1, 9, 3],
      ![36, 18, 6, 18, 6, 18, 9, 3, 3, 9, 1, 3],
      ![60, 30, 10, 36, 18, 6, 18, 6, 9, 3, 3, 1]],
    ![![1, 4, 10, 4, 10, 20, 16, 40, 40, 80, 100, 200],
      ![4, 1, 4, 16, 40, 80, 4, 16, 10, 20, 40, 80],
      ![10, 4, 1, 40, 100, 200, 16, 4, 40, 80, 10, 20],
      ![4, 16, 40, 1, 4, 10, 4, 10, 16, 40, 40, 100],
      ![10, 40, 100, 4, 1, 4, 16, 40, 4, 16, 10, 40],
      ![20, 80, 200, 10, 4, 1, 40, 100, 16, 4, 40, 10],
      ![16, 4, 16, 4, 16, 40, 1, 4, 4, 10, 16, 40],
      ![40, 16, 4, 10, 40, 100, 4, 1, 16, 40, 4, 10],
      ![40, 10, 40, 16, 4, 16, 4, 16, 1, 4, 4, 16],
      ![80, 20, 80, 40, 16, 4, 10, 40, 4, 1, 16, 4],
      ![100, 40, 10, 40, 10, 40, 16, 4, 4, 16, 1, 4],
      ![200, 80, 20, 100, 40, 10, 40, 10, 16, 4, 4, 1]],
    ![![1, 5, 15, 5, 15, 35, 25, 75, 75, 175, 225, 525],
      ![5, 1, 5, 25, 75, 175, 5, 25, 15, 35, 75, 175],
      ![15, 5, 1, 75, 225, 525, 25, 5, 75, 175, 15, 35],
      ![5, 25, 75, 1, 5, 15, 5, 15, 25, 75, 75, 225],
      ![15, 75, 225, 5, 1, 5, 25, 75, 5, 25, 15, 75],
      ![35, 175, 525, 15, 5, 1, 75, 225, 25, 5, 75, 15],
      ![25, 5, 25, 5, 25, 75, 1, 5, 5, 15, 25, 75],
      ![75, 25, 5, 15, 75, 225, 5, 1, 25, 75, 5, 15],
      ![75, 15, 75, 25, 5, 25, 5, 25, 1, 5, 5, 25],
      ![175, 35, 175, 75, 25, 5, 15, 75, 5, 1, 25, 5],
      ![225, 75, 15, 75, 15, 75, 25, 5, 5, 25, 1, 5],
      ![525, 175, 35, 225, 75, 15, 75, 15, 25, 5, 5, 1]],
    ![![1, 6, 21, 6, 21, 56, 36, 126, 126, 336, 441, 1176],
      ![6, 1, 6, 36, 126, 336, 6, 36, 21, 56, 126, 336],
      ![21, 6, 1, 126, 441, 1176, 36, 6, 126, 336, 21, 56],
      ![6, 36, 126, 1, 6, 21, 6, 21, 36, 126, 126, 441],
      ![21, 126, 441, 6, 1, 6, 36, 126, 6, 36, 21, 126],
      ![56, 336, 1176, 21, 6, 1, 126, 441, 36, 6, 126, 21],
      ![36, 6, 36, 6, 36, 126, 1, 6, 6, 21, 36, 126],
      ![126, 36, 6, 21, 126, 441, 6, 1, 36, 126, 6, 21],
      ![126, 21, 126, 36, 6, 36, 6, 36, 1, 6, 6, 36],
      ![336, 56, 336, 126, 36, 6, 21, 126, 6, 1, 36, 6],
      ![441, 126, 21, 126, 21, 126, 36, 6, 6, 36, 1, 6],
      ![1176, 336, 56, 441, 126, 21, 126, 21, 36, 6, 6, 1]],
    ![![1, 7, 28, 7, 28, 84, 49, 196, 196, 588, 784, 2352],
      ![7, 1, 7, 49, 196, 588, 7, 49, 28, 84, 196, 588],
      ![28, 7, 1, 196, 784, 2352, 49, 7, 196, 588, 28, 84],
      ![7, 49, 196, 1, 7, 28, 7, 28, 49, 196, 196, 784],
      ![28, 196, 784, 7, 1, 7, 49, 196, 7, 49, 28, 196],
      ![84, 588, 2352, 28, 7, 1, 196, 784, 49, 7, 196, 28],
      ![49, 7, 49, 7, 49, 196, 1, 7, 7, 28, 49, 196],
      ![196, 49, 7, 28, 196, 784, 7, 1, 49, 196, 7, 28],
      ![196, 28, 196, 49, 7, 49, 7, 49, 1, 7, 7, 49],
      ![588, 84, 588, 196, 49, 7, 28, 196, 7, 1, 49, 7],
      ![784, 196, 28, 196, 28, 196, 49, 7, 7, 49, 1, 7],
      ![2352, 588, 84, 784, 196, 28, 196, 28, 49, 7, 7, 1]]]

private noncomputable def initial (k : Fin 7) (p q : Row) : ℤ := table k (code p) (code q)

private theorem table_step0 : ∀ p q : Legal,
    initial 1 p.val q.val = step (initial 0) p.val q.val := by decide +kernel

private theorem table_step1 : ∀ p q : Legal,
    initial 2 p.val q.val = step (initial 1) p.val q.val := by decide +kernel

private theorem table_step2 : ∀ p q : Legal,
    initial 3 p.val q.val = step (initial 2) p.val q.val := by decide +kernel

private theorem table_step3 : ∀ p q : Legal,
    initial 4 p.val q.val = step (initial 3) p.val q.val := by decide +kernel

private theorem table_step4 : ∀ p q : Legal,
    initial 5 p.val q.val = step (initial 4) p.val q.val := by decide +kernel

private theorem table_step5 : ∀ p q : Legal,
    initial 6 p.val q.val = step (initial 5) p.val q.val := by decide +kernel

private theorem table_step (k : Fin 6) : ∀ p q : Legal,
    initial k.succ p.val q.val = step (initial k.castSucc) p.val q.val := by
  fin_cases k
  · exact table_step0
  · exact table_step1
  · exact table_step2
  · exact table_step3
  · exact table_step4
  · exact table_step5

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
    v (n+6) p.val q.val = 6*v (n+5) p.val q.val - 15*v (n+4) p.val q.val + 20*v (n+3) p.val q.val - 15*v (n+2) p.val q.val + 6*v (n+1) p.val q.val - 1*v (n+0) p.val q.val := by
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
    ![144, 612, 1782, 4212, 8692, 16284, 28362] k := by decide +kernel

private theorem term1 : a 1 = 12 := by
  rw [card_ok]
  decide +kernel

private theorem term2 : a 2 = 144 :=
  (value 0).trans ((initial_total 0).trans (counts 0))

private theorem term3 : a 3 = 612 :=
  (value 1).trans ((initial_total 1).trans (counts 1))

private theorem term4 : a 4 = 1782 :=
  (value 2).trans ((initial_total 2).trans (counts 2))

private theorem term5 : a 5 = 4212 :=
  (value 3).trans ((initial_total 3).trans (counts 3))

private theorem term6 : a 6 = 8692 :=
  (value 4).trans ((initial_total 4).trans (counts 4))

private theorem term7 : a 7 = 16284 :=
  (value 5).trans ((initial_total 5).trans (counts 5))

private theorem term8 : a 8 = 28362 :=
  (value 6).trans ((initial_total 6).trans (counts 6))

private theorem recurrence (n : ℕ) (hn : 7 ≤ n) :
    (a n : ℚ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  by_cases hs : n < 8
  · interval_cases n <;> norm_num [term1,term2,term3,term4,term5,term6,term7,term8]
  obtain ⟨m,rfl⟩ : ∃ m, n = m+8 := ⟨n-8,by omega⟩
  have h : total (v (m+6)) = 6*total (v (m+5)) - 15*total (v (m+4)) + 20*total (v (m+3)) - 15*total (v (m+2)) + 6*total (v (m+1)) - 1*total (v (m+0)) := by
    unfold total
    conv_lhs =>
      enter [2,p,2,q]
      rw [differences m p q]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum]
  have h2 : a (m+8) = 6*a (m+7) - 15*a (m+6) + 20*a (m+5) - 15*a (m+4) + 6*a (m+3) - a (m+2) := by
    simpa [value] using h
  simp only [show m+8-1 = m+7 by omega, show m+8-2 = m+6 by omega, show m+8-3 = m+5 by omega, show m+8-4 = m+4 by omega, show m+8-5 = m+3 by omega, show m+8-6 = m+2 by omega]
  exact_mod_cast h2

private theorem generating :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 6 : PowerSeries ℚ) = 2 * X * (6 + 36 * X - 36 * X ^ 2 + 15 * X ^ 3 - X ^ 5) := by
  let S := mk (fun n => if n < 1 then 0 else (a n : ℚ))
  change S * _ = _
  have lhs : S*((1 - X) ^ 6) = S - (6:ℕ) • (S*X^1) + (15:ℕ) • (S*X^2) - (20:ℕ) • (S*X^3) + (15:ℕ) • (S*X^4) - (6:ℕ) • (S*X^5) + (1:ℕ) • (S*X^6) := by simp only [nsmul_eq_mul]; ring
  have rhs : (2 * X * (6 + 36 * X - 36 * X ^ 2 + 15 * X ^ 3 - X ^ 5) : PowerSeries ℚ) = (12:ℕ) • X^1 + (72:ℕ) • X^2 - (72:ℕ) • X^3 + (30:ℕ) • X^4 - (2:ℕ) • X^6 := by simp only [nsmul_eq_mul]; ring
  rw [lhs,rhs]
  ext n
  simp only [map_add,map_sub,map_nsmul,coeff_mul_X_pow',coeff_X_pow,S,coeff_mk]
  by_cases h : 7 ≤ n
  · have recn := recurrence n (by omega)
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
      if_neg (show n ≠ 6 by omega)]
    norm_num
    linarith
  · interval_cases n <;> norm_num [term1,term2,term3,term4,term5,term6,term7,term8]

private theorem claim1 :
    ∀ n : ℕ, 7 ≤ n → (a n : ℚ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := fun n hn => recurrence n (by omega)

theorem result : type_of% @OMA.S_oeis_a207400.main := ⟨generating,claim1⟩

end OMA.Arr_oeis_a207400

theorem OMA.solution : type_of% @OMA.S_oeis_a207400.main := OMA.Arr_oeis_a207400.result
