import OMAStatements.S_oeis_a269271

-- Problem: A269271: Number of n X 3 0..3 arrays with some element plus some horizontally or antidiagonally adjacent neighbor totalling three exactly o
-- Upstream: formal-conjectures statements/oeis-a269271.lean:0 (declaration OMA.S_oeis_a269271.main)
-- Credit: @lettucrisp (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/- Transfer matrix on states (last row or column, number of qualifying pairs so far, 0 or 1).
`G m` is the state vector after m + 1 rows; its entries are tabulated and each step is checked
by `decide`. The vectors satisfy a fixed linear relation (checked on the tables, propagated by
linearity of the step `T`), which gives the recurrence, the g.f. and the closed form. -/

namespace OMA.Pa269271
open OMA.S_oeis_a269271 Finset

abbrev Row := Fin 4 × Fin 4 × Fin 4
abbrev RF := Fin 3 → Fin 4
def toRow (r : RF) : Row := (r 0, r 1, r 2)
def rowEquiv : RF ≃ Row where
  toFun := toRow
  invFun := fun r => ![r.1, r.2.1, r.2.2]
  left_inv := by
    intro r; funext i; fin_cases i <;> rfl
  right_inv := by
    intro r; rfl

def h (r : Row) : ℕ := (if (r.1 : ℕ) + r.2.1 = 3 then 1 else 0) + (if (r.2.1 : ℕ) + r.2.2 = 3 then 1 else 0)
def ad (r s : Row) : ℕ := (if (r.2.1 : ℕ) + s.1 = 3 then 1 else 0) + (if (r.2.2 : ℕ) + s.2.1 = 3 then 1 else 0)

def tot (m : ℕ) (x : Fin (m + 1) → RF) : ℕ :=
  (∑ i : Fin (m + 1), h (toRow (x i))) + ∑ i : Fin m, ad (toRow (x i.castSucc)) (toRow (x i.succ))

lemma pairs_eq (m : ℕ) (x : Fin (m + 1) → RF) : pairsTotallingThree m x = tot m x := by
  unfold pairsTotallingThree tot
  simp only [Finset.card_filter, Fintype.sum_prod_type, Fin.sum_univ_two, h, ad, toRow,
    Finset.sum_add_distrib]
  first | ac_rfl | (simp only [← add_assoc]; rfl) | (simp only [← add_assoc]; congr 1 <;> (try congr 1) <;> (try congr 1) <;> (try congr 1) <;> rfl)

lemma tot_snoc (m : ℕ) (x : Fin (m + 1) → RF) (z : RF) :
    tot (m + 1) (Fin.snoc (α := fun _ => RF) x z) =
      tot m x + ad (toRow (x (Fin.last m))) (toRow z) + h (toRow z) := by
  unfold tot
  rw [Fin.sum_univ_castSucc (fun i : Fin (m + 2) =>
      h (toRow (Fin.snoc (α := fun _ => RF) x z i))),
    Fin.sum_univ_castSucc (fun i : Fin (m + 1) =>
      ad (toRow (Fin.snoc (α := fun _ => RF) x z i.castSucc))
        (toRow (Fin.snoc (α := fun _ => RF) x z i.succ)))]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.succ_last, Fin.succ_castSucc]
  ring

def cnt (m : ℕ) (s : Row) (f : ℕ) : ℕ :=
  ∑ x : Fin (m + 1) → RF, if toRow (x (Fin.last m)) = s ∧ tot m x = f then 1 else 0

lemma sum_row (g : Row → ℕ) : ∑ z : RF, g (toRow z) = ∑ r : Row, g r :=
  rowEquiv.sum_comp g

lemma cnt_zero (s : Row) (f : ℕ) : cnt 0 s f = if h s = f then 1 else 0 := by
  unfold cnt
  rw [← (Equiv.funUnique (Fin 1) RF).symm.sum_comp]
  have : ∀ z : RF, tot 0 ((Equiv.funUnique (Fin 1) RF).symm z) = h (toRow z) := by
    intro z; simp [tot]
  have h1 : ∀ z : RF, ((Equiv.funUnique (Fin 1) RF).symm z) (Fin.last 0) = z := fun z => rfl
  simp only [this, h1]
  rw [sum_row (fun r => if r = s ∧ h r = f then 1 else 0)]
  rw [Finset.sum_eq_single s]
  · simp
  · intro b _ hb; simp [hb]
  · simp

lemma cnt_succ (m : ℕ) (s' : Row) (f' : ℕ) :
    cnt (m + 1) s' f' = ∑ s : Row,
      if ad s s' + h s' ≤ f' then cnt m s (f' - (ad s s' + h s')) else 0 := by
  unfold cnt
  rw [← (Fin.snocEquiv (fun _ => RF)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.snoc_last, tot_snoc]
  have inner : ∀ x : Fin (m + 1) → RF,
      (∑ z : RF, if toRow z = s' ∧
        tot m x + ad (toRow (x (Fin.last m))) (toRow z) + h (toRow z) = f' then 1 else 0) =
      ∑ s : Row, if toRow (x (Fin.last m)) = s then
        (if ad s s' + h s' ≤ f' ∧ tot m x = f' - (ad s s' + h s') then 1 else 0) else 0 := by
    intro x
    rw [sum_row (fun r => if r = s' ∧ tot m x + ad (toRow (x (Fin.last m))) r + h r = f'
      then 1 else 0)]
    rw [Finset.sum_eq_single s', Finset.sum_ite_eq]
    · simp only [Finset.mem_univ, if_true, true_and]
      split_ifs <;> omega
    · intro b _ hb; simp [hb]
    · simp
  simp only [inner]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro s _
  split_ifs with hc
  · apply Finset.sum_congr rfl; intro x _
    split_ifs <;> simp_all
  · apply Finset.sum_eq_zero; intro x _
    split_ifs <;> simp_all

def T (G : Row → ℕ × ℕ) (s : Row) : ℕ × ℕ :=
  (∑ r : Row, if ad r s + h s = 0 then (G r).1 else 0,
   ∑ r : Row, ((if ad r s + h s = 1 then (G r).1 else 0) +
     (if ad r s + h s = 0 then (G r).2 else 0)))

def F0 (s : Row) : ℕ × ℕ := (if h s = 0 then 1 else 0, if h s = 1 then 1 else 0)

def G : ℕ → Row → ℕ × ℕ
  | 0 => F0
  | n + 1 => T (G n)

lemma T_fst (P : Row → ℕ × ℕ) (s : Row) :
    (T P s).1 = ∑ r : Row, if ad r s + h s = 0 then (P r).1 else 0 := rfl
lemma T_snd (P : Row → ℕ × ℕ) (s : Row) :
    (T P s).2 = ∑ r : Row, ((if ad r s + h s = 1 then (P r).1 else 0) +
      (if ad r s + h s = 0 then (P r).2 else 0)) := rfl

lemma cnt_eq (m : ℕ) (s : Row) : cnt m s 0 = (G m s).1 ∧ cnt m s 1 = (G m s).2 := by
  induction m generalizing s with
  | zero => simp [cnt_zero, F0, G]
  | succ m ih =>
    show cnt (m + 1) s 0 = (T (G m) s).1 ∧ cnt (m + 1) s 1 = (T (G m) s).2
    rw [T_fst, T_snd, cnt_succ, cnt_succ]
    constructor
    · refine Finset.sum_congr rfl (fun r _ => ?_)
      have h0 := (ih r).1
      generalize ad r s + h s = c
      rcases c with _ | c
      · simpa using h0
      · simp
    · refine Finset.sum_congr rfl (fun r _ => ?_)
      have h0 := (ih r).1
      have h1 := (ih r).2
      generalize ad r s + h s = c
      rcases c with _ | _ | c
      · simpa using h1
      · simpa using h0
      · simp

lemma a_eq (m : ℕ) : a (m + 1) = ∑ s : Row, (G m s).2 := by
  rw [show (∑ s : Row, (G m s).2) = ∑ s : Row, cnt m s 1 from
    Finset.sum_congr rfl (fun s _ => by simp only [(cnt_eq m s).1, (cnt_eq m s).2])]
  show (Finset.univ.filter (fun x : Fin (m + 1) → Fin 3 → Fin 4 => pairsTotallingThree m x = 1)).card = _
  rw [Finset.card_filter]
  simp only [pairs_eq]
  unfold cnt
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  simp only [ite_and]
  rw [Finset.sum_ite_eq]
  simp

def idx (s : Row) : ℕ := s.1.val * 16 + s.2.1.val * 4 + s.2.2.val
def L0 : List (ℕ × ℕ) := [(1, 0), (1, 0), (1, 0), (0, 1), (1, 0), (1, 0), (0, 1), (1, 0), (1, 0), (0, 1), (1, 0), (1, 0), (0, 0), (0, 1), (0, 1), (0, 1), (1, 0), (1, 0), (1, 0), (0, 1), (1, 0), (1, 0), (0, 1), (1, 0), (0, 1), (0, 0), (0, 1), (0, 1), (0, 1), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (0, 1), (0, 1), (0, 1), (0, 0), (0, 1), (1, 0), (0, 1), (1, 0), (1, 0), (0, 1), (1, 0), (1, 0), (1, 0), (0, 1), (0, 1), (0, 1), (0, 0), (1, 0), (1, 0), (0, 1), (1, 0), (1, 0), (0, 1), (1, 0), (1, 0), (0, 1), (1, 0), (1, 0), (1, 0)]
def tab0 (s : Row) : ℕ × ℕ := L0.getD (idx s) (0, 0)
def L1 : List (ℕ × ℕ) := [(21, 25), (21, 25), (21, 25), (0, 21), (21, 25), (21, 25), (0, 21), (21, 25), (21, 25), (0, 21), (21, 25), (21, 25), (0, 0), (0, 18), (0, 18), (0, 18), (21, 25), (21, 25), (21, 25), (0, 21), (21, 25), (21, 25), (0, 21), (21, 25), (0, 18), (0, 0), (0, 18), (0, 18), (0, 21), (21, 25), (21, 25), (21, 25), (21, 25), (21, 25), (21, 25), (0, 21), (0, 18), (0, 18), (0, 0), (0, 18), (21, 25), (0, 21), (21, 25), (21, 25), (0, 21), (21, 25), (21, 25), (21, 25), (0, 18), (0, 18), (0, 18), (0, 0), (21, 25), (21, 25), (0, 21), (21, 25), (21, 25), (0, 21), (21, 25), (21, 25), (0, 21), (21, 25), (21, 25), (21, 25)]
def tab1 (s : Row) : ℕ × ℕ := L1.getD (idx s) (0, 0)
def L2 : List (ℕ × ℕ) := [(441, 1029), (441, 1029), (441, 1029), (0, 441), (441, 1029), (441, 1029), (0, 441), (441, 1029), (441, 1029), (0, 441), (441, 1029), (441, 1029), (0, 0), (0, 378), (0, 378), (0, 378), (441, 1029), (441, 1029), (441, 1029), (0, 441), (441, 1029), (441, 1029), (0, 441), (441, 1029), (0, 378), (0, 0), (0, 378), (0, 378), (0, 441), (441, 1029), (441, 1029), (441, 1029), (441, 1029), (441, 1029), (441, 1029), (0, 441), (0, 378), (0, 378), (0, 0), (0, 378), (441, 1029), (0, 441), (441, 1029), (441, 1029), (0, 441), (441, 1029), (441, 1029), (441, 1029), (0, 378), (0, 378), (0, 378), (0, 0), (441, 1029), (441, 1029), (0, 441), (441, 1029), (441, 1029), (0, 441), (441, 1029), (441, 1029), (0, 441), (441, 1029), (441, 1029), (441, 1029)]
def tab2 (s : Row) : ℕ × ℕ := L2.getD (idx s) (0, 0)
def L3 : List (ℕ × ℕ) := [(9261, 32193), (9261, 32193), (9261, 32193), (0, 9261), (9261, 32193), (9261, 32193), (0, 9261), (9261, 32193), (9261, 32193), (0, 9261), (9261, 32193), (9261, 32193), (0, 0), (0, 7938), (0, 7938), (0, 7938), (9261, 32193), (9261, 32193), (9261, 32193), (0, 9261), (9261, 32193), (9261, 32193), (0, 9261), (9261, 32193), (0, 7938), (0, 0), (0, 7938), (0, 7938), (0, 9261), (9261, 32193), (9261, 32193), (9261, 32193), (9261, 32193), (9261, 32193), (9261, 32193), (0, 9261), (0, 7938), (0, 7938), (0, 0), (0, 7938), (9261, 32193), (0, 9261), (9261, 32193), (9261, 32193), (0, 9261), (9261, 32193), (9261, 32193), (9261, 32193), (0, 7938), (0, 7938), (0, 7938), (0, 0), (9261, 32193), (9261, 32193), (0, 9261), (9261, 32193), (9261, 32193), (0, 9261), (9261, 32193), (9261, 32193), (0, 9261), (9261, 32193), (9261, 32193), (9261, 32193)]
def tab3 (s : Row) : ℕ × ℕ := L3.getD (idx s) (0, 0)

set_option maxRecDepth 200000 in
lemma G0 : G 0 = tab0 := by
  funext s; revert s; decide +kernel

set_option maxRecDepth 200000 in
lemma T0 : ∀ s, T tab0 s = tab1 s := by decide +kernel
lemma G1 : G 1 = tab1 := by
  funext s; show T (G 0) s = _; rw [G0]; exact T0 s

set_option maxRecDepth 200000 in
lemma T1 : ∀ s, T tab1 s = tab2 s := by decide +kernel
lemma G2 : G 2 = tab2 := by
  funext s; show T (G 1) s = _; rw [G1]; exact T1 s

set_option maxRecDepth 200000 in
lemma T2 : ∀ s, T tab2 s = tab3 s := by decide +kernel
lemma G3 : G 3 = tab3 := by
  funext s; show T (G 2) s = _; rw [G2]; exact T2 s

def Rel (V0 V1 V2 V3 : Row → ℕ × ℕ) : Prop :=
  ∀ s, (V3 s).1 + 441 * (V1 s).1 = 42 * (V2 s).1 ∧ (V3 s).2 + 441 * (V1 s).2 = 42 * (V2 s).2

lemma rel_T {V0 V1 V2 V3 : Row → ℕ × ℕ} (H : Rel V0 V1 V2 V3) : Rel (T V0) (T V1) (T V2) (T V3) := by
  intro s
  simp only [T_fst, T_snd]
  constructor
  · simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro r _
    have := H r
    split_ifs <;> omega
  · simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro r _
    have := H r
    split_ifs <;> omega

set_option maxRecDepth 200000 in
lemma rel_tab : Rel tab0 tab1 tab2 tab3 := by
  unfold Rel; decide +kernel

lemma rel_base : Rel (G 0) (G 1) (G 2) (G 3) := by
  rw [G0, G1, G2, G3]; exact rel_tab

lemma rel_all (k : ℕ) : Rel (G k) (G (k + 1)) (G (k + 2)) (G (k + 3)) := by
  induction k with
  | zero => exact rel_base
  | succ k ih =>
    show Rel (T (G k)) (T (G (k + 1))) (T (G (k + 2))) (T (G (k + 3)))
    exact rel_T ih

lemma v0 : a 0 = 0 := rfl
set_option maxRecDepth 200000 in
lemma v1 : a 1 = 24 := by
  rw [a_eq, G0]; decide +kernel
set_option maxRecDepth 200000 in
lemma v2 : a 2 = 1368 := by
  rw [a_eq, G1]; decide +kernel
set_option maxRecDepth 200000 in
lemma v3 : a 3 = 46872 := by
  rw [a_eq, G2]; decide +kernel
set_option maxRecDepth 200000 in
lemma v4 : a 4 = 1365336 := by
  rw [a_eq, G3]; decide +kernel

lemma rec (k : ℕ) : a (k + 4) + 441 * a (k + 2) = 42 * a (k + 3) := by
  simp only [a_eq, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro s _
  have := rel_all k s
  omega

lemma recS (k : ℕ) : a (k + 3) + 441 * a (k + 1) = 42 * a (k + 2) := by
  cases k with
  | zero => simp only [zero_add, v1, v2, v3]
  | succ k =>
    have := rec k
    ring_nf at this ⊢
    omega

def cf (n : ℕ) : ℚ := 8 * 3 ^ n * 7 ^ ((n : ℤ) - 2) * (12 * n - 5)

lemma cfrel (k : ℕ) : cf (k + 3) + 441 * cf (k + 1) = 42 * cf (k + 2) := by
  simp only [cf]
  simp only [zpow_sub₀ (by norm_num : (7 : ℚ) ≠ 0), zpow_natCast, zpow_ofNat]
  push_cast
  ring

lemma closed (k : ℕ) : (a (k + 1) : ℚ) = cf (k + 1) ∧ (a (k + 2) : ℚ) = cf (k + 2) := by
  induction k with
  | zero =>
    simp only [zero_add, cf, v0, v1, v2, v3, v4]
    simp only [zpow_sub₀ (by norm_num : (7 : ℚ) ≠ 0), zpow_natCast, zpow_ofNat]
    norm_num
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    rw [show k + 1 + 1 = k + 2 by omega, show k + 1 + 2 = k + 3 by omega]
    refine ⟨h1, ?_⟩
    have rr := congrArg (Nat.cast : ℕ → ℚ) (recS k)
    push_cast at rr
    
    have cr := cfrel k
    linarith

end OMA.Pa269271

open OMA.Pa269271 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a269271.main := by
  have key : PowerSeries.mk (fun n => (OMA.S_oeis_a269271.a n : ℚ)) * (C (1 : ℚ) + C (-42 : ℚ) * X ^ 1 + C (441 : ℚ) * X ^ 2) = C (24 : ℚ) * X ^ 1 + C (360 : ℚ) * X ^ 2 := by
    ext n
    simp only [mul_add, map_add, mul_left_comm _ (C _), coeff_C_mul, coeff_mul_C,
      mul_comm (PowerSeries.mk _) (X ^ _), PowerSeries.coeff_X_pow_mul', coeff_mk, coeff_C_mul_X_pow,
      coeff_C, coeff_X_pow]
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n <;> simp [v0, v1, v2] <;> norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      have rr := congrArg (Nat.cast : ℕ → ℚ) (recS k)
      push_cast at rr
      simp only [show 1 ≤ k + 3 by omega, show ¬ (k + 3 = 1) by omega, show k + 3 - 1 = k + 2 by omega, show 2 ≤ k + 3 by omega, show ¬ (k + 3 = 2) by omega, show k + 3 - 2 = k + 1 by omega, show ¬ (k + 3 = 0) by omega, if_true, if_false, Nat.sub_zero]
      linarith
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    have rr := congrArg (Nat.cast : ℕ → ℤ) (recS k)
    push_cast at rr
    simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega]
    linarith
  · convert key using 2 <;> (try simp only [map_neg, map_ofNat, map_one, map_zero]) <;> ring
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact (closed k).1
