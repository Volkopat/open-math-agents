import OMAStatements.S_oeis_a268899

-- Problem: A268899: Number of n X 3 0..2 arrays with some element plus some horizontally or antidiagonally adjacent neighbor totalling two exactly once.
-- Upstream: formal-conjectures statements/oeis-a268899.lean:0 (declaration OMA.S_oeis_a268899.main)
-- Credit: @lettucrisp (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/- Transfer matrix on states (last row, number of pairs totalling two so far, 0 or 1).
`G m` is the state vector after m + 1 rows, so a(m+1) = sum of its flag-1 part.
The vectors satisfy G(k+3) + 36 G(k+1) = 12 G(k+2): checked by `decide` for k = 0 and
propagated by linearity of the step `T`. The recurrence gives the g.f. and the closed form. -/

namespace OMA.A268899Proof
open OMA.S_oeis_a268899 Finset

abbrev Row := Fin 3 × Fin 3 × Fin 3

def toRow (r : Fin 3 → Fin 3) : Row := (r 0, r 1, r 2)

def rowEquiv : (Fin 3 → Fin 3) ≃ Row where
  toFun := toRow
  invFun := fun r => ![r.1, r.2.1, r.2.2]
  left_inv := by
    intro r; funext i; fin_cases i <;> rfl
  right_inv := by
    intro r; rfl

def h (r : Row) : ℕ :=
  (if (r.1 : ℕ) + r.2.1 = 2 then 1 else 0) + (if (r.2.1 : ℕ) + r.2.2 = 2 then 1 else 0)

def ad (r s : Row) : ℕ :=
  (if (r.2.1 : ℕ) + s.1 = 2 then 1 else 0) + (if (r.2.2 : ℕ) + s.2.1 = 2 then 1 else 0)

def tot (m : ℕ) (x : Fin (m + 1) → Fin 3 → Fin 3) : ℕ :=
  (∑ i : Fin (m + 1), h (toRow (x i))) + ∑ i : Fin m, ad (toRow (x i.castSucc)) (toRow (x i.succ))

lemma pairs_eq (m : ℕ) (x : Fin (m + 1) → Fin 3 → Fin 3) : pairsTotallingTwo m x = tot m x := by
  unfold pairsTotallingTwo tot
  rw [Finset.card_filter, Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
  congr 1
  all_goals (apply Finset.sum_congr rfl; intro i _; simp [Fin.sum_univ_two, h, ad, toRow])

lemma tot_snoc (m : ℕ) (x : Fin (m + 1) → Fin 3 → Fin 3) (z : Fin 3 → Fin 3) :
    tot (m + 1) (Fin.snoc (α := fun _ => Fin 3 → Fin 3) x z) =
      tot m x + ad (toRow (x (Fin.last m))) (toRow z) + h (toRow z) := by
  unfold tot
  rw [Fin.sum_univ_castSucc (fun i : Fin (m + 2) =>
      h (toRow (Fin.snoc (α := fun _ => Fin 3 → Fin 3) x z i))),
    Fin.sum_univ_castSucc (fun i : Fin (m + 1) =>
      ad (toRow (Fin.snoc (α := fun _ => Fin 3 → Fin 3) x z i.castSucc))
        (toRow (Fin.snoc (α := fun _ => Fin 3 → Fin 3) x z i.succ)))]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.succ_last, Fin.succ_castSucc]
  ring

def cnt (m : ℕ) (s : Row) (f : ℕ) : ℕ :=
  ∑ x : Fin (m + 1) → Fin 3 → Fin 3, if toRow (x (Fin.last m)) = s ∧ tot m x = f then 1 else 0

lemma sum_row (g : Row → ℕ) : ∑ z : Fin 3 → Fin 3, g (toRow z) = ∑ r : Row, g r :=
  rowEquiv.sum_comp g

lemma cnt_zero (s : Row) (f : ℕ) : cnt 0 s f = if h s = f then 1 else 0 := by
  unfold cnt
  rw [← (Equiv.funUnique (Fin 1) (Fin 3 → Fin 3)).symm.sum_comp]
  have : ∀ z : Fin 3 → Fin 3, tot 0 ((Equiv.funUnique (Fin 1) (Fin 3 → Fin 3)).symm z) =
      h (toRow z) := by
    intro z; simp [tot]
  have h1 : ∀ z : Fin 3 → Fin 3,
      ((Equiv.funUnique (Fin 1) (Fin 3 → Fin 3)).symm z) (Fin.last 0) = z := fun z => rfl
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
  rw [← (Fin.snocEquiv (fun _ => Fin 3 → Fin 3)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.snoc_last, tot_snoc]
  have inner : ∀ x : Fin (m + 1) → Fin 3 → Fin 3,
      (∑ z : Fin 3 → Fin 3, if toRow z = s' ∧
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
    Finset.sum_congr rfl (fun s _ => ((cnt_eq m s).2).symm)]
  show (Finset.univ.filter (fun x : Fin (m + 1) → Fin 3 → Fin 3 =>
    pairsTotallingTwo m x = 1)).card = _
  rw [Finset.card_filter]
  unfold cnt
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  rw [pairs_eq]
  simp only [ite_and]
  rw [Finset.sum_ite_eq]
  simp

def Rel (P Q R : Row → ℕ × ℕ) : Prop :=
  ∀ s, (P s).1 + 36 * (Q s).1 = 12 * (R s).1 ∧ (P s).2 + 36 * (Q s).2 = 12 * (R s).2

lemma rel_T {P Q R : Row → ℕ × ℕ} (H : Rel P Q R) : Rel (T P) (T Q) (T R) := by
  intro s
  rw [T_fst, T_fst, T_fst, T_snd, T_snd, T_snd]
  constructor
  · rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro r _
    have := H r
    split_ifs <;> omega
  · rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro r _
    have := H r
    split_ifs <;> omega

set_option maxRecDepth 100000 in
lemma rel_base : Rel (G 3) (G 1) (G 2) := by
  unfold Rel; decide +kernel

lemma rel_all (k : ℕ) : Rel (G (k + 3)) (G (k + 1)) (G (k + 2)) := by
  induction k with
  | zero => exact rel_base
  | succ k ih =>
    show Rel (T (G (k + 3))) (T (G (k + 1))) (T (G (k + 2)))
    exact rel_T ih

lemma a_rec (k : ℕ) : a (k + 4) + 36 * a (k + 2) = 12 * a (k + 3) := by
  rw [a_eq, a_eq, a_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro s _
  exact (rel_all k s).2

lemma a0 : a 0 = 0 := rfl
set_option maxRecDepth 100000 in
lemma a1 : a 1 = 12 := by rw [a_eq]; decide +kernel
set_option maxRecDepth 100000 in
lemma a2 : a 2 = 168 := by rw [a_eq]; decide +kernel
set_option maxRecDepth 100000 in
lemma a3 : a 3 = 1584 := by rw [a_eq]; decide +kernel

lemma rec3 (k : ℕ) : a (k + 3) + 36 * a (k + 1) = 12 * a (k + 2) := by
  cases k with
  | zero => rw [a1, a2, a3]
  | succ k => exact a_rec k

def c (n : ℕ) : ℚ := 2 ^ (n + 1) * 3 ^ (n - 1) * (4 * n - 1)

lemma closed (k : ℕ) : (a (k + 1) : ℚ) = c (k + 1) ∧ (a (k + 2) : ℚ) = c (k + 2) := by
  induction k with
  | zero => simp [a1, a2, c]; norm_num
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have r : ((a (k + 3) + 36 * a (k + 1) : ℕ) : ℚ) = ((12 * a (k + 2) : ℕ) : ℚ) := by
      rw [rec3]
    push_cast at r
    rw [show k + 1 + 2 = k + 3 by ring]
    have e : (a (k + 3) : ℚ) = 12 * a (k + 2) - 36 * a (k + 1) := by linarith
    rw [e, ih.1, ih.2]
    simp only [c, show k + 3 - 1 = k + 2 by omega, show k + 2 - 1 = k + 1 by omega,
      show k + 1 - 1 = k by omega]
    push_cast
    ring

end OMA.A268899Proof

open OMA.A268899Proof PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a268899.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    have r : ((OMA.S_oeis_a268899.a (k + 3) + 36 * OMA.S_oeis_a268899.a (k + 1) : ℕ) : ℤ) =
        ((12 * OMA.S_oeis_a268899.a (k + 2) : ℕ) : ℤ) := by rw [rec3]
    push_cast at r
    simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega]
    linarith
  · ext n
    have e1 : ((1 - 6 * X) ^ 2 : PowerSeries ℚ) = 1 - C 12 * X ^ 1 + C 36 * X ^ 2 := by
      have h12 : (12 : PowerSeries ℚ) = C 12 := (map_ofNat C 12).symm
      have h36 : (36 : PowerSeries ℚ) = C 36 := (map_ofNat C 36).symm
      have h6 : (6 : PowerSeries ℚ) = C 6 := (map_ofNat C 6).symm
      rw [← h12, ← h36]; ring
    have e2 : (12 * X * (1 + 2 * X) : PowerSeries ℚ) = C 12 * X ^ 1 + C 24 * X ^ 2 := by
      have h12 : (12 : PowerSeries ℚ) = C 12 := (map_ofNat C 12).symm
      have h24 : (24 : PowerSeries ℚ) = C 24 := (map_ofNat C 24).symm
      rw [← h12, ← h24]; ring
    rw [e1, e2]
    simp only [mul_add, mul_sub, mul_one, map_add, map_sub, mul_left_comm _ (C _), coeff_C_mul,
      mul_comm (PowerSeries.mk _) (X ^ _), PowerSeries.coeff_X_pow_mul', coeff_mk, coeff_one,
      coeff_X_pow, coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n <;> simp [a0, a1, a2] <;> norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      have r : ((OMA.S_oeis_a268899.a (k + 3) + 36 * OMA.S_oeis_a268899.a (k + 1) : ℕ) : ℚ) =
          ((12 * OMA.S_oeis_a268899.a (k + 2) : ℕ) : ℚ) := by rw [rec3]
      push_cast at r
      simp only [show ¬ (k + 3 = 0) by omega, show ¬ (k + 3 = 1) by omega,
        show ¬ (k + 3 = 2) by omega, if_false, show 1 ≤ k + 3 by omega,
        show 2 ≤ k + 3 by omega, if_true,
        show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega]
      linarith
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [(closed k).1]; rfl
