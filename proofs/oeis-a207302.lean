import OMAStatements.S_oeis_a207302
import Mathlib

namespace OMA.Arrays207302

open OMA.S_oeis_a207302
open PowerSeries

private abbrev Row := Fin 5 → Fin 2

private def legal (r : Row) : Prop := ∀ j : Fin 3,
  let t := ((r ⟨j, by omega⟩).val, (r ⟨j+1, by omega⟩).val, (r ⟨j+2, by omega⟩).val)
  t ≠ (0,0,0) ∧ t ≠ (1,0,1)

private instance (r : Row) : Decidable (legal r) := by unfold legal; infer_instance

private theorem horizontal {n : ℕ} (x : Fin n → Row) :
    (∀ i < n, ∀ j < 5-2,
      (get x i j, get x i (j+1), get x i (j+2)) ≠ (0,0,0) ∧
      (get x i j, get x i (j+1), get x i (j+2)) ≠ (1,0,1)) ↔ ∀ i, legal (x i) := by
  constructor
  · intro h i j
    simpa [OMA.S_oeis_a207302.get, i.isLt, show j.val < 5 by omega, show j.val+1 < 5 by omega,
      show j.val+2 < 5 by omega] using h i i.isLt j j.isLt
  · intro h i hi j hj
    simpa [OMA.S_oeis_a207302.get, hi, show j < 5 by omega, show j+1 < 5 by omega, show j+2 < 5 by omega]
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
    simpa [OMA.S_oeis_a207302.get,j.isLt,show i.val < n+2 by omega,
      show i.val+1 < n+2 by omega,show i.val+2 < n+2 by omega] using h i (by omega) j j.isLt
  · intro h i hi j hj
    have hh := (bits _ _ _).mpr (h ⟨i,by omega⟩ ⟨j,hj⟩)
    simpa [OMA.S_oeis_a207302.get,hj,show i < n+2 by omega,
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

private def code (r : Row) : Fin 13 :=
  ![0, 0, 0, 0, 0, 0, 1, 2, 0, 3, 0, 0, 4, 0, 5, 6, 0, 0, 7, 8, 0, 0, 0, 0, 0, 9, 0, 0, 10, 0, 11, 12] (rowIndex r)

private def table : Fin 6 → Fin 13 → Fin 13 → ℤ :=
  ![![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]],
    ![![1, 2, 3, 3, 2, 4, 6, 3, 5, 5, 3, 6, 9],
      ![2, 1, 2, 7, 4, 2, 4, 2, 4, 13, 6, 3, 6],
      ![3, 2, 1, 3, 6, 4, 2, 4, 2, 6, 9, 6, 3],
      ![3, 7, 3, 1, 2, 4, 2, 4, 3, 2, 4, 8, 4],
      ![2, 4, 6, 2, 1, 2, 3, 7, 13, 4, 2, 4, 6],
      ![4, 2, 4, 4, 2, 1, 2, 4, 8, 8, 4, 2, 4],
      ![6, 4, 2, 2, 3, 2, 1, 8, 4, 4, 6, 4, 2],
      ![3, 2, 4, 4, 7, 4, 8, 1, 2, 3, 3, 2, 4],
      ![5, 4, 2, 3, 13, 8, 4, 2, 1, 2, 6, 4, 2],
      ![5, 13, 6, 2, 4, 8, 4, 3, 2, 1, 2, 4, 2],
      ![3, 6, 9, 4, 2, 4, 6, 3, 6, 2, 1, 2, 3],
      ![6, 3, 6, 8, 4, 2, 4, 2, 4, 4, 2, 1, 2],
      ![9, 6, 3, 4, 6, 4, 2, 4, 2, 2, 3, 2, 1]],
    ![![1, 3, 6, 6, 3, 9, 18, 6, 14, 14, 6, 18, 36],
      ![3, 1, 3, 22, 9, 3, 9, 3, 9, 56, 18, 6, 18],
      ![6, 3, 1, 6, 18, 9, 3, 9, 3, 17, 36, 18, 6],
      ![6, 22, 6, 1, 3, 9, 3, 10, 6, 3, 9, 27, 9],
      ![3, 9, 18, 3, 1, 3, 6, 22, 56, 9, 3, 9, 18],
      ![9, 3, 9, 9, 3, 1, 3, 9, 27, 27, 9, 3, 9],
      ![18, 9, 3, 3, 6, 3, 1, 27, 9, 9, 18, 9, 3],
      ![6, 3, 9, 10, 22, 9, 27, 1, 3, 6, 6, 3, 9],
      ![14, 9, 3, 6, 56, 27, 9, 3, 1, 3, 17, 9, 3],
      ![14, 56, 17, 3, 9, 27, 9, 6, 3, 1, 3, 9, 3],
      ![6, 18, 36, 9, 3, 9, 18, 6, 17, 3, 1, 3, 6],
      ![18, 6, 18, 27, 9, 3, 9, 3, 9, 9, 3, 1, 3],
      ![36, 18, 6, 9, 18, 9, 3, 9, 3, 3, 6, 3, 1]],
    ![![1, 4, 10, 10, 4, 16, 40, 10, 30, 30, 10, 40, 100],
      ![4, 1, 4, 50, 16, 4, 16, 4, 16, 160, 40, 10, 40],
      ![10, 4, 1, 10, 40, 16, 4, 16, 4, 36, 100, 40, 10],
      ![10, 50, 10, 1, 4, 16, 4, 20, 10, 4, 16, 64, 16],
      ![4, 16, 40, 4, 1, 4, 10, 50, 160, 16, 4, 16, 40],
      ![16, 4, 16, 16, 4, 1, 4, 16, 64, 64, 16, 4, 16],
      ![40, 16, 4, 4, 10, 4, 1, 64, 16, 16, 40, 16, 4],
      ![10, 4, 16, 20, 50, 16, 64, 1, 4, 10, 10, 4, 16],
      ![30, 16, 4, 10, 160, 64, 16, 4, 1, 4, 36, 16, 4],
      ![30, 160, 36, 4, 16, 64, 16, 10, 4, 1, 4, 16, 4],
      ![10, 40, 100, 16, 4, 16, 40, 10, 36, 4, 1, 4, 10],
      ![40, 10, 40, 64, 16, 4, 16, 4, 16, 16, 4, 1, 4],
      ![100, 40, 10, 16, 40, 16, 4, 16, 4, 4, 10, 4, 1]],
    ![![1, 5, 15, 15, 5, 25, 75, 15, 55, 55, 15, 75, 225],
      ![5, 1, 5, 95, 25, 5, 25, 5, 25, 365, 75, 15, 75],
      ![15, 5, 1, 15, 75, 25, 5, 25, 5, 65, 225, 75, 15],
      ![15, 95, 15, 1, 5, 25, 5, 35, 15, 5, 25, 125, 25],
      ![5, 25, 75, 5, 1, 5, 15, 95, 365, 25, 5, 25, 75],
      ![25, 5, 25, 25, 5, 1, 5, 25, 125, 125, 25, 5, 25],
      ![75, 25, 5, 5, 15, 5, 1, 125, 25, 25, 75, 25, 5],
      ![15, 5, 25, 35, 95, 25, 125, 1, 5, 15, 15, 5, 25],
      ![55, 25, 5, 15, 365, 125, 25, 5, 1, 5, 65, 25, 5],
      ![55, 365, 65, 5, 25, 125, 25, 15, 5, 1, 5, 25, 5],
      ![15, 75, 225, 25, 5, 25, 75, 15, 65, 5, 1, 5, 15],
      ![75, 15, 75, 125, 25, 5, 25, 5, 25, 25, 5, 1, 5],
      ![225, 75, 15, 25, 75, 25, 5, 25, 5, 5, 15, 5, 1]],
    ![![1, 6, 21, 21, 6, 36, 126, 21, 91, 91, 21, 126, 441],
      ![6, 1, 6, 161, 36, 6, 36, 6, 36, 721, 126, 21, 126],
      ![21, 6, 1, 21, 126, 36, 6, 36, 6, 106, 441, 126, 21],
      ![21, 161, 21, 1, 6, 36, 6, 56, 21, 6, 36, 216, 36],
      ![6, 36, 126, 6, 1, 6, 21, 161, 721, 36, 6, 36, 126],
      ![36, 6, 36, 36, 6, 1, 6, 36, 216, 216, 36, 6, 36],
      ![126, 36, 6, 6, 21, 6, 1, 216, 36, 36, 126, 36, 6],
      ![21, 6, 36, 56, 161, 36, 216, 1, 6, 21, 21, 6, 36],
      ![91, 36, 6, 21, 721, 216, 36, 6, 1, 6, 106, 36, 6],
      ![91, 721, 106, 6, 36, 216, 36, 21, 6, 1, 6, 36, 6],
      ![21, 126, 441, 36, 6, 36, 126, 21, 106, 6, 1, 6, 21],
      ![126, 21, 126, 216, 36, 6, 36, 6, 36, 36, 6, 1, 6],
      ![441, 126, 21, 36, 126, 36, 6, 36, 6, 6, 21, 6, 1]]]

private def initial (k : Fin 6) (p q : Row) : ℤ := table k (code p) (code q)

private theorem table_step : ∀ k : Fin 5, ∀ p q : Legal,
    initial k.succ p.val q.val = step (initial k.castSucc) p.val q.val := by decide +kernel

private theorem initial_eq (k : Fin 6) : ∀ p q : Legal,
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
    v (n+5) p.val q.val = 5*v (n+4) p.val q.val - 10*v (n+3) p.val q.val + 10*v (n+2) p.val q.val - 5*v (n+1) p.val q.val + v n p.val q.val := by
  induction n with
  | zero =>
    intro p q
    have e0 : v 0 p.val q.val = initial 0 p.val q.val := initial_eq 0 p q
    have e1 : v 1 p.val q.val = initial 1 p.val q.val := initial_eq 1 p q
    have e2 : v 2 p.val q.val = initial 2 p.val q.val := initial_eq 2 p q
    have e3 : v 3 p.val q.val = initial 3 p.val q.val := initial_eq 3 p q
    have e4 : v 4 p.val q.val = initial 4 p.val q.val := initial_eq 4 p q
    have e5 : v 5 p.val q.val = initial 5 p.val q.val := initial_eq 5 p q
    simp only [Nat.zero_add,e0,e1,e2,e3,e4,e5]
    clear e0 e1 e2 e3 e4 e5
    revert p q
    decide +kernel
  | succ n ih =>
    intro p q
    change v ((n+5)+1) p.val q.val = _
    rw [succ_v (n+5)]
    unfold step
    rw [Finset.sum_congr rfl (fun r _ => ih q ⟨r.val,r.property.1⟩)]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
    have sum_v (t : ℕ) :
        (∑ r : {r : Row // legal r ∧ next p.val q.val r}, v t q.val r.val) =
          v (t+1) p.val q.val := (congrFun (congrFun (succ_v t) p.val) q.val).symm
    simp only [sum_v]

private theorem initial_total (k : Fin 6) :
    total (v k.val) = total (initial k) := by
  unfold total
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  exact fun q _ => initial_eq k p q

private theorem counts : ∀ k : Fin 6, total (initial k) =
    ![169, 665, 1759, 3773, 7093, 12169] k := by decide +kernel

private theorem first : a 1 = 13 := by decide +kernel

private theorem term2 : a 2 = 169 :=
  (value 0).trans ((initial_total 0).trans (counts 0))

private theorem term3 : a 3 = 665 :=
  (value 1).trans ((initial_total 1).trans (counts 1))

private theorem term4 : a 4 = 1759 :=
  (value 2).trans ((initial_total 2).trans (counts 2))

private theorem term5 : a 5 = 3773 :=
  (value 3).trans ((initial_total 3).trans (counts 3))

private theorem term6 : a 6 = 7093 :=
  (value 4).trans ((initial_total 4).trans (counts 4))

private theorem recurrence (n : ℕ) (hn : 6 ≤ n) :
    (a n : ℚ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  by_cases he : n = 6
  · subst n
    norm_num [first,term2,term3,term4,term5,term6]
  obtain ⟨m,rfl⟩ : ∃ m, n = m+7 := ⟨n-7,by omega⟩
  have h : total (v (m+5)) = 5*total (v (m+4)) - 10*total (v (m+3)) + 10*total (v (m+2)) - 5*total (v (m+1)) + total (v m) := by
    unfold total
    conv_lhs =>
      enter [2,p,2,q]
      rw [differences m p q]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum]
  exact_mod_cast (show a (m+7) = _ from by simpa [value] using h)

private theorem generating :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 5 : PowerSeries ℚ) = X * (13 + 104 * X - 50 * X ^ 2 - 6 * X ^ 3 + 3 * X ^ 4) := by
  let S := mk (fun n => if n < 1 then 0 else (a n : ℚ))
  change S * _ = _
  have lhs : S*(1-X)^5 = S - (5:ℕ) • (S*X^1) + (10:ℕ) • (S*X^2) - (10:ℕ) • (S*X^3) + (5:ℕ) • (S*X^4) - (S*X^5) := by simp only [nsmul_eq_mul]; ring
  have rhs : (X * (13 + 104 * X - 50 * X ^ 2 - 6 * X ^ 3 + 3 * X ^ 4) : PowerSeries ℚ) = (13:ℕ) • X^1 + (104:ℕ) • X^2 - (50:ℕ) • X^3 - (6:ℕ) • X^4 + (3:ℕ) • X^5 := by simp only [nsmul_eq_mul]; ring
  rw [lhs,rhs]
  ext n
  simp only [map_add,map_sub,map_nsmul,coeff_mul_X_pow',coeff_X_pow,S,coeff_mk]
  by_cases h : 6 ≤ n
  · have recn := recurrence n h
    simp only [nsmul_eq_mul, if_pos (show 1 ≤ n by omega),
      if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega),
      if_pos (show 4 ≤ n by omega),
      if_pos (show 5 ≤ n by omega),
      if_neg (show ¬ n < 1 by omega),
      if_neg (show ¬ n-1 < 1 by omega),
      if_neg (show ¬ n-2 < 1 by omega),
      if_neg (show ¬ n-3 < 1 by omega),
      if_neg (show ¬ n-4 < 1 by omega),
      if_neg (show ¬ n-5 < 1 by omega),
      if_neg (show n ≠ 1 by omega),
      if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 3 by omega),
      if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 5 by omega)]
    norm_num
    linarith
  · interval_cases n <;> norm_num [first,term2,term3,term4,term5]

theorem result : type_of% @OMA.S_oeis_a207302.main := ⟨generating,recurrence⟩

end OMA.Arrays207302

theorem OMA.solution : type_of% @OMA.S_oeis_a207302.main := OMA.Arrays207302.result
