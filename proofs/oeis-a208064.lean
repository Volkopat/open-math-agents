import OMAStatements.S_oeis_a208064
import Mathlib

/-!
# Proof of OMA.S_oeis_a208064.main

Transfer matrix on pairs of consecutive lines of the array: the number of ways to complete
an array below two given legal lines satisfies, entrywise, the linear recurrence of the
denominator of the generating function; kernel-checked tables give the first values, and
the stated identities follow by induction.
The structure (chain decomposition, tables, entrywise differences) is adapted from
roshanasingh4 merged proof of oeis-a207701 in lefttosolve2/open-math-agents.
-/

namespace OMA.Arr_oeis_a208064

open OMA.S_oeis_a208064
open PowerSeries

private abbrev Row := Fin 3 → Fin 2

private def legal (r : Row) : Prop := ∀ j : Fin 1,
  (((r ⟨j, by omega⟩).val, (r ⟨j+1, by omega⟩).val, (r ⟨j+2, by omega⟩).val) ≠ (0, 0, 0) ∧
   ((r ⟨j, by omega⟩).val, (r ⟨j+1, by omega⟩).val, (r ⟨j+2, by omega⟩).val) ≠ (1, 1, 1))

private instance (r : Row) : Decidable (legal r) := by unfold legal; infer_instance

private def next (p q r : Row) : Prop := ∀ j,
  ((p j).val, (q j).val, (r j).val) ≠ (0, 0, 1) ∧ ((p j).val, (q j).val, (r j).val) ≠ (0, 1, 1)

private instance (p q r : Row) : Decidable (next p q r) := by unfold next; infer_instance

private theorem within {n : ℕ} (x : Fin n → Row) :
    (∀ i < n, ∀ j < 3 - 2,
      (get x i j, get x i (j + 1), get x i (j + 2)) ≠ (0, 0, 0) ∧
      (get x i j, get x i (j + 1), get x i (j + 2)) ≠ (1, 1, 1)) ↔ ∀ i, legal (x i) := by
  constructor
  · intro h i j
    simpa [OMA.S_oeis_a208064.get, i.isLt, show j.val < 3 by omega, show j.val+1 < 3 by omega,
      show j.val+2 < 3 by omega] using h i i.isLt j (by omega)
  · intro h i hi j hj
    simpa [OMA.S_oeis_a208064.get, hi, show j < 3 by omega, show j+1 < 3 by omega, show j+2 < 3 by omega]
      using h ⟨i,hi⟩ ⟨j,by omega⟩

private theorem across {n : ℕ} (x : Fin (n+2) → Row) :
    (∀ i < n+2-2, ∀ j < 3,
      (get x i j, get x (i + 1) j, get x (i + 2) j) ≠ (0, 0, 1) ∧
      (get x i j, get x (i + 1) j, get x (i + 2) j) ≠ (0, 1, 1)) ↔
    ∀ i : Fin n, next (x i.castSucc.castSucc) (x i.castSucc.succ) (x i.succ.succ) := by
  constructor
  · intro h i j
    show ((x ⟨i.val,by omega⟩ j).val, (x ⟨i.val+1,by omega⟩ j).val, (x ⟨i.val+2,by omega⟩ j).val) ≠ (0, 0, 1) ∧
      ((x ⟨i.val,by omega⟩ j).val, (x ⟨i.val+1,by omega⟩ j).val, (x ⟨i.val+2,by omega⟩ j).val) ≠ (0, 1, 1)
    simpa [OMA.S_oeis_a208064.get,j.isLt,show i.val < n+2 by omega,
      show i.val+1 < n+2 by omega,show i.val+2 < n+2 by omega] using h i (by omega) j j.isLt
  · intro h i hi j hj
    have hh := h ⟨i,by omega⟩ ⟨j,hj⟩
    simpa [OMA.S_oeis_a208064.get,hj,show i < n+2 by omega,
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

private def rowIndex (r : Row) : Fin 8 :=
  ⟨4*(r 0).val + 2*(r 1).val + 1*(r 2).val, by omega⟩

private def code (r : Row) : Fin 6 :=
  ![0, 0, 1, 2, 3, 4, 5, 0] (rowIndex r)

private noncomputable def table : Fin 5 → Fin 6 → Fin 6 → ℤ :=
  ![![![1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1]],
    ![![1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1],
      ![3, 3, 3, 3, 3, 3],
      ![1, 1, 1, 1, 1, 1],
      ![3, 3, 3, 3, 3, 3],
      ![3, 3, 3, 3, 3, 3]],
    ![![1, 1, 3, 1, 3, 3],
      ![1, 1, 3, 1, 3, 3],
      ![3, 3, 9, 3, 9, 9],
      ![1, 1, 3, 1, 3, 3],
      ![3, 3, 9, 3, 9, 9],
      ![3, 3, 9, 3, 9, 9]],
    ![![1, 1, 3, 1, 3, 3],
      ![1, 1, 3, 1, 3, 3],
      ![5, 5, 15, 5, 15, 15],
      ![1, 1, 3, 1, 3, 3],
      ![5, 5, 15, 5, 15, 15],
      ![5, 5, 15, 5, 15, 15]],
    ![![1, 1, 5, 1, 5, 5],
      ![1, 1, 5, 1, 5, 5],
      ![5, 5, 25, 5, 25, 25],
      ![1, 1, 5, 1, 5, 5],
      ![5, 5, 25, 5, 25, 25],
      ![5, 5, 25, 5, 25, 25]]]

private noncomputable def initial (k : Fin 5) (p q : Row) : ℤ := table k (code p) (code q)

private theorem table_step0 : ∀ p q : Legal,
    initial 1 p.val q.val = step (initial 0) p.val q.val := by decide +kernel

private theorem table_step1 : ∀ p q : Legal,
    initial 2 p.val q.val = step (initial 1) p.val q.val := by decide +kernel

private theorem table_step2 : ∀ p q : Legal,
    initial 3 p.val q.val = step (initial 2) p.val q.val := by decide +kernel

private theorem table_step3 : ∀ p q : Legal,
    initial 4 p.val q.val = step (initial 3) p.val q.val := by decide +kernel

private theorem table_step (k : Fin 4) : ∀ p q : Legal,
    initial k.succ p.val q.val = step (initial k.castSucc) p.val q.val := by
  fin_cases k
  · exact table_step0
  · exact table_step1
  · exact table_step2
  · exact table_step3

private theorem initial_eq (k : Fin 5) : ∀ p q : Legal,
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
    v (n+4) p.val q.val = 2*v (n+3) p.val q.val - 2*v (n+1) p.val q.val + 1*v (n+0) p.val q.val := by
  induction n with
  | zero =>
    intro p q
    have e0 : v 0 p.val q.val = initial 0 p.val q.val := initial_eq 0 p q
    have e1 : v 1 p.val q.val = initial 1 p.val q.val := initial_eq 1 p q
    have e2 : v 2 p.val q.val = initial 2 p.val q.val := initial_eq 2 p q
    have e3 : v 3 p.val q.val = initial 3 p.val q.val := initial_eq 3 p q
    have e4 : v 4 p.val q.val = initial 4 p.val q.val := initial_eq 4 p q
    simp only [Nat.zero_add,e0,e1,e2,e3,e4]
    clear e0 e1 e2 e3 e4
    revert p q
    decide +kernel
  | succ n ih =>
    intro p q
    change v ((n+4)+1) p.val q.val = _
    rw [succ_v (n+4)]
    unfold step
    rw [Finset.sum_congr rfl (fun r _ => ih q ⟨r.val,r.property.1⟩)]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
    have sum_v (t : ℕ) :
        (∑ r : {r : Row // legal r ∧ next p.val q.val r}, v t q.val r.val) =
          v (t+1) p.val q.val := (congrFun (congrFun (succ_v t) p.val) q.val).symm
    simp only [sum_v]

private theorem initial_total (k : Fin 5) :
    total (v k.val) = total (initial k) := by
  unfold total
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  exact fun q _ => initial_eq k p q

private theorem counts : ∀ k : Fin 5, total (initial k) =
    ![36, 72, 144, 216, 324] k := by decide +kernel

private theorem term1 : a 1 = 6 := by
  rw [card_ok]
  decide +kernel

private theorem term2 : a 2 = 36 :=
  (value 0).trans ((initial_total 0).trans (counts 0))

private theorem term3 : a 3 = 72 :=
  (value 1).trans ((initial_total 1).trans (counts 1))

private theorem term4 : a 4 = 144 :=
  (value 2).trans ((initial_total 2).trans (counts 2))

private theorem term5 : a 5 = 216 :=
  (value 3).trans ((initial_total 3).trans (counts 3))

private theorem term6 : a 6 = 324 :=
  (value 4).trans ((initial_total 4).trans (counts 4))

private theorem recurrence (n : ℕ) (hn : 6 ≤ n) :
    (a n : ℚ) = 2 * a (n - 1) - 2 * a (n - 3) + a (n - 4) := by
  obtain ⟨m,rfl⟩ : ∃ m, n = m+6 := ⟨n-6,by omega⟩
  have h : total (v (m+4)) = 2*total (v (m+3)) - 2*total (v (m+1)) + 1*total (v (m+0)) := by
    unfold total
    conv_lhs =>
      enter [2,p,2,q]
      rw [differences m p q]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum]
  have h2 : a (m+6) = 2*a (m+5) - 2*a (m+3) + a (m+2) := by
    simpa [value] using h
  simp only [show m+6-1 = m+5 by omega, show m+6-2 = m+4 by omega, show m+6-3 = m+3 by omega, show m+6-4 = m+2 by omega]
  exact_mod_cast h2

private theorem generating :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 3 * (1 + X) : PowerSeries ℚ) = 6 * X * (1 + 4 * X + 2 * X ^ 3 - X ^ 4) := by
  let S := mk (fun n => if n < 1 then 0 else (a n : ℚ))
  change S * _ = _
  have lhs : S*((1 - X) ^ 3 * (1 + X)) = S - (2:ℕ) • (S*X^1) + (2:ℕ) • (S*X^3) - (1:ℕ) • (S*X^4) := by simp only [nsmul_eq_mul]; ring
  have rhs : (6 * X * (1 + 4 * X + 2 * X ^ 3 - X ^ 4) : PowerSeries ℚ) = (6:ℕ) • X^1 + (24:ℕ) • X^2 + (12:ℕ) • X^4 - (6:ℕ) • X^5 := by simp only [nsmul_eq_mul]; ring
  rw [lhs,rhs]
  ext n
  simp only [map_add,map_sub,map_nsmul,coeff_mul_X_pow',coeff_X_pow,S,coeff_mk]
  by_cases h : 6 ≤ n
  · have recn := recurrence n (by omega)
    simp only [nsmul_eq_mul, if_pos (show 1 ≤ n by omega),
      if_pos (show 3 ≤ n by omega),
      if_pos (show 4 ≤ n by omega),
      if_neg (show ¬ n < 1 by omega),
      if_neg (show ¬ n-1 < 1 by omega),
      if_neg (show ¬ n-3 < 1 by omega),
      if_neg (show ¬ n-4 < 1 by omega),
      if_neg (show n ≠ 1 by omega),
      if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 5 by omega)]
    norm_num
    linarith
  · interval_cases n <;> norm_num [term1,term2,term3,term4,term5,term6]

private def g (n : ℕ) : ℚ := ((9 * (n : ℚ) ^ 2) + (9 * (n : ℚ) ^ 2 - 9)) / 2 + (-1 : ℚ) ^ n * (((9 * (n : ℚ) ^ 2) - (9 * (n : ℚ) ^ 2 - 9)) / 2)

private theorem closed (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = g n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n < 6
    · interval_cases n <;> norm_num [g,term1,term2,term3,term4,term5,term6]
    rw [recurrence n (by omega),ih (n-1) (by omega) (by omega),
      ih (n-3) (by omega) (by omega),
      ih (n-4) (by omega) (by omega)]
    obtain ⟨m,rfl⟩ : ∃ m, n=m+6 := ⟨n-6,by omega⟩
    simp only [show m+6-1 = m+5 by omega,show m+6-2 = m+4 by omega,show m+6-3 = m+3 by omega,show m+6-4 = m+2 by omega]
    unfold g
    push_cast
    ring

private theorem claim1 :
    ∀ n : ℕ, 2 ≤ n → Even n → (a n : ℚ) = 9 * (n : ℚ) ^ 2 := fun n hn he => by rw [closed n hn]; unfold g; rw [he.neg_one_pow]; ring

private theorem claim2 :
    ∀ n : ℕ, 2 ≤ n → Odd n → (a n : ℚ) = 9 * (n : ℚ) ^ 2 - 9 := fun n hn ho => by rw [closed n hn]; unfold g; rw [ho.neg_one_pow]; ring

theorem result : type_of% @OMA.S_oeis_a208064.main := ⟨generating,claim1,claim2⟩

end OMA.Arr_oeis_a208064

theorem OMA.solution : type_of% @OMA.S_oeis_a208064.main := OMA.Arr_oeis_a208064.result
