import OMAStatements.S_oeis_a203829
import Mathlib

/-!
# oeis-a203829: counting the (n+1) X 3 arrays

Split an array (a list of rows) into its top row and the rest. The subblock condition is a chain
condition on consecutive rows, so the numbers f(n, r) of valid arrays with top row r satisfy a
linear recursion over the next row. The defect g(n, r) of the conjectured recurrence satisfies the
same recursion, and it vanishes for n = 0 (the kernel computes the first values of f for all 27
top rows), so it vanishes identically. Summing over r gives the recurrence for a(n), and the
generating function follows by comparing coefficients. The closed form satisfies the same
recurrence (an identity modulo sqrt 73 ^ 2 = 73), and agrees with a(n) for the first values, hence for all n >= 1.

Source: OEIS A203829, https://oeis.org/A203829.
-/
namespace OMA.P_oeis_a203829

open OMA.S_oeis_a203829 Real

abbrev R := Fin 3 → Fin 3

lemma sumk {M : Type*} [AddCommMonoid M] (g : R → M) : ∑ s : R, g s = ∑ y0 : Fin 3, ∑ y1 : Fin 3, ∑ y2 : Fin 3, g ![y0, y1, y2] := by
  let e : Fin 3 × Fin 3 × Fin 3 ≃ R :=
    ⟨fun p => ![p.1, p.2.1, p.2.2], fun f => (f 0, f 1, f 2), fun p => by simp,
      fun f => by ext i; fin_cases i <;> rfl⟩
  rw [← e.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

def rowOK (_r : R) : Prop := True

def adj (r s : R) : Prop := ∀ j : Fin 2, r j.castSucc = s j.succ ∨ r j.succ = s j.castSucc

instance : DecidablePred rowOK := fun r => by unfold rowOK; infer_instance
instance (r s : R) : Decidable (adj r s) := by unfold adj; infer_instance

open Classical

def Pall (l : List R) : Prop := (∀ r ∈ l, rowOK r) ∧ l.IsChain adj

lemma isSol_iff (l : List R) : IsSolution l ↔ Pall l := by
  unfold IsSolution Pall rowOK adj
  first | exact Iff.rfl | simp only [implies_true, true_and]

lemma pall_cons_nil (r : R) : Pall [r] ↔ rowOK r := by
  simp [Pall]

lemma pall_cons_cons (r s : R) (m : List R) :
    Pall (r :: s :: m) ↔ (rowOK r ∧ adj r s) ∧ Pall (s :: m) := by
  unfold Pall
  rw [List.isChain_cons]
  simp only [List.mem_cons, forall_eq_or_imp, List.head?_cons, Option.mem_def,
    Option.some.injEq, forall_eq']
  tauto

def LL : ℕ → Finset (List R)
  | 0 => {[]}
  | n + 1 => ((Finset.univ : Finset R) ×ˢ LL n).image (fun p => p.1 :: p.2)

lemma mem_LL (n : ℕ) (l : List R) : l ∈ LL n ↔ l.length = n := by
  induction n generalizing l with
  | zero => simp [LL]
  | succ n ih =>
    cases l with
    | nil => simp [LL]
    | cons x m => simp [LL, ih]

lemma card_cons (n : ℕ) (Q : List R → Prop) [DecidablePred Q] :
    ((LL (n + 1)).filter Q).card = ∑ s : R, ((LL n).filter (fun m => Q (s :: m))).card := by
  rw [LL, Finset.filter_image, Finset.card_image_of_injective _ (by
    intro p q h; simp only [List.cons.injEq] at h; exact Prod.ext h.1 h.2)]
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.card_filter]

noncomputable def f (n : ℕ) (r : R) : ℕ := ((LL n).filter (fun l => Pall (r :: l))).card

lemma a_eq (n : ℕ) : a n = ∑ r : R, f n r := by
  have e : {l : List R // l.length = n + 1 ∧ IsSolution l} ≃
      {l // l ∈ (LL (n + 1)).filter Pall} :=
    Equiv.subtypeEquivRight (fun l => by simp [mem_LL, isSol_iff])
  rw [a, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, card_cons]
  rfl

lemma f_zero (r : R) : f 0 r = if rowOK r then 1 else 0 := by
  unfold f; simp only [LL]; rw [Finset.filter_singleton]
  by_cases h : rowOK r
  · rw [if_pos ((pall_cons_nil r).mpr h), if_pos h]; rfl
  · rw [if_neg (fun h' => h ((pall_cons_nil r).mp h')), if_neg h]; rfl

lemma f_succ (n : ℕ) (r : R) :
    f (n + 1) r = ∑ s : R, if rowOK r ∧ adj r s then f n s else 0 := by
  unfold f
  rw [card_cons]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [pall_cons_cons]
  split_ifs with h
  · congr 1; ext m; simp [h]
  · simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro m _ hm; exact h hm.1

def V0 : Fin 3 → Fin 3 → Fin 3 → ℤ :=
  ![![![1, 1, 1], ![1, 1, 1], ![1, 1, 1]], ![![1, 1, 1], ![1, 1, 1], ![1, 1, 1]], ![![1, 1, 1], ![1, 1, 1], ![1, 1, 1]]]

def V1 : Fin 3 → Fin 3 → Fin 3 → ℤ :=
  ![![![11, 7, 7], ![11, 7, 7], ![11, 7, 7]], ![![7, 11, 7], ![7, 11, 7], ![7, 11, 7]], ![![7, 7, 11], ![7, 7, 11], ![7, 7, 11]]]

def V2 : Fin 3 → Fin 3 → Fin 3 → ℤ :=
  ![![![97, 61, 61], ![97, 61, 61], ![97, 61, 61]], ![![61, 97, 61], ![61, 97, 61], ![61, 97, 61]], ![![61, 61, 97], ![61, 61, 97], ![61, 61, 97]]]

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
lemma fv0 : ∀ (i0 i1 i2 : Fin 3), (f 0 ![i0, i1, i2] : ℤ) = V0 i0 i1 i2 := by
  intro i0 i1 i2; rw [f_zero]
  fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;> simp +decide [V0, rowOK]

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
lemma fv1 : ∀ (i0 i1 i2 : Fin 3), (f 1 ![i0, i1, i2] : ℤ) = V1 i0 i1 i2 := by
  intro i0 i1 i2; rw [f_succ]; push_cast
  rw [sumk]
  simp only [Fin.sum_univ_three]
  fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;>
    simp +decide only [rowOK, adj, if_true, if_false, add_zero, zero_add] <;>
    (try simp only [fv0]) <;>
    simp [V0, V1]

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
lemma fv2 : ∀ (i0 i1 i2 : Fin 3), (f 2 ![i0, i1, i2] : ℤ) = V2 i0 i1 i2 := by
  intro i0 i1 i2; rw [f_succ]; push_cast
  rw [sumk]
  simp only [Fin.sum_univ_three]
  fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;>
    simp +decide only [rowOK, adj, if_true, if_false, add_zero, zero_add] <;>
    (try simp only [fv1]) <;>
    simp [V1, V2]

/-- The defect of the recurrence for the counts with a given top row. -/
noncomputable def g (n : ℕ) (r : R) : ℤ := (f (n + 2) r : ℤ) - ((9 : ℤ) * (f (n + 1) r : ℤ) + (-2 : ℤ) * (f (n + 0) r : ℤ))

lemma g_succ (n : ℕ) (r : R) : g (n + 1) r = ∑ s : R, if rowOK r ∧ adj r s then g n s else 0 := by
  unfold g
  rw [show n + 1 + 2 = (n + 2) + 1 by omega, show n + 1 + 1 = (n + 1) + 1 by omega, show n + 1 + 0 = (n + 0) + 1 by omega]
  rw [f_succ (n + 2), f_succ (n + 1), f_succ (n + 0)]
  push_cast
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> ring

set_option maxHeartbeats 4000000 in
lemma g_zero : ∀ (i0 i1 i2 : Fin 3), g 0 ![i0, i1, i2] = 0 := by
  intro i0 i1 i2
  unfold g
  simp only [zero_add, fv2, fv1, fv0]
  fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;> simp [V0, V1, V2]

lemma g_all (n : ℕ) : ∀ r, g n r = 0 := by
  induction n with
  | zero =>
    intro r
    have h := g_zero (r 0) (r 1) (r 2)
    have hr : (![r 0, r 1, r 2] : R) = r := by ext j; fin_cases j <;> rfl
    rw [show (![r 0, r 1, r 2] : R) = r from hr] at h
    exact h
  | succ n ih => intro r; rw [g_succ]; simp [ih]

theorem a_rec (n : ℕ) : (a (n + 2) : ℤ) = (9 : ℤ) * (a (n + 1) : ℤ) + (-2 : ℤ) * (a (n + 0) : ℤ) := by
  simp only [a_eq]; push_cast
  have hf : ∀ r, (f (n + 2) r : ℤ) = (9 : ℤ) * (f (n + 1) r : ℤ) + (-2 : ℤ) * (f (n + 0) r : ℤ) := fun r => by
    have := g_all n r; unfold g at this; linarith
  simp only [hf, Finset.sum_add_distrib, ← Finset.mul_sum]

lemma a0 : (a 0 : ℤ) = 27 := by
  rw [a_eq]; push_cast; rw [sumk]; simp only [Fin.sum_univ_three, fv0]; simp [V0]

lemma a1 : (a 1 : ℤ) = 225 := by
  rw [a_eq]; push_cast; rw [sumk]; simp only [Fin.sum_univ_three, fv1]; simp [V1]

lemma a2 : (a 2 : ℤ) = 1971 := by
  rw [a_eq]; push_cast; rw [sumk]; simp only [Fin.sum_univ_three, fv2]; simp [V2]

lemma zA (n : ℕ) : (2 : ℝ) ^ (-1 - (n : ℤ)) = (1 / 2) * (1 / 2) ^ n := by
  rw [show (-1 - (n : ℤ)) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  rw [pow_succ, mul_inv, one_div, inv_pow, mul_comm]

lemma dv (x : ℝ) : x / √73 = x * √73 / 73 := by
  have h : (√73) ^ 2 = 73 := Real.sq_sqrt (by norm_num)
  have h0 : √73 ≠ 0 := by positivity
  field_simp
  linear_combination (-x) * h

noncomputable def S (n : ℕ) : ℝ := 9 * (2 : ℝ) ^ (-1 - (n : ℤ)) * ((9 - √73) ^ n * (-23 + 3 * √73) + (9 + √73) ^ n * (23 + 3 * √73)) / √73

lemma hs : (√73) ^ 2 = 73 := Real.sq_sqrt (by norm_num)

lemma S_rec (n : ℕ) : S (n + 2) = (9 : ℝ) * S (n + 1) + (-2 : ℝ) * S (n + 0) := by
  unfold S
  simp only [zA, dv]
  linear_combination (27*((1 / 2 : ℝ) ^ n)*((9 - √73) ^ n)*(√73)^2/584 - 207*((1 / 2 : ℝ) ^ n)*((9 - √73) ^ n)*(√73)/584 + 27*((1 / 2 : ℝ) ^ n)*((9 + √73) ^ n)*(√73)^2/584 + 207*((1 / 2 : ℝ) ^ n)*((9 + √73) ^ n)*(√73)/584) * hs

lemma S1 : S 1 = 225 := by
  unfold S
  simp only [zA, dv]
  linear_combination (225/73) * hs

lemma S2 : S 2 = 1971 := by
  unfold S
  simp only [zA, dv]
  linear_combination (27*(√73)^2/292 + 27) * hs


theorem binet (n : ℕ) (hn : 1 ≤ n) : (a n : ℝ) = S n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n <;> first | (rw [S1]; exact_mod_cast a1) | (rw [S2]; exact_mod_cast a2)
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      have hr := a_rec (m + 1)
      have hr' : (a (m + 3) : ℝ) = (9 : ℝ) * (a (m + 2) : ℝ) + (-2 : ℝ) * (a (m + 1) : ℝ) := by
        have := congrArg (fun z : ℤ => (z : ℝ)) hr
        simp only [show m + 1 + 2 = m + 3 by omega, show m + 1 + 1 = m + 2 by omega, show m + 1 + 0 = m + 1 by omega] at this
        push_cast at this
        linarith
      rw [hr', show m + 3 = (m + 1) + 2 by omega, S_rec]
      rw [ih (m + 2) (by omega) (by omega), ih (m + 1) (by omega) (by omega)]
      try simp only [show m + 1 + 1 = m + 2 by omega, show m + 1 + 0 = m + 1 by omega]

open PowerSeries in
theorem full :
    (∀ n > 2, (a n : ℤ) = 9 * a (n - 1) - 2 * a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - 9 * X + 2 * X ^ 2) = 9 * (25 - 6 * X)) ∧
    (∀ n ≥ 1, (a n : ℝ) = 9 * (2 : ℝ) ^ (-1 - (n : ℤ)) * ((9 - √73) ^ n * (-23 + 3 * √73) +
      (9 + √73) ^ n * (23 + 3 * √73)) / √73) := by
  refine ⟨fun n hn => ?_, ?_, fun n hn => binet n hn⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have hr := a_rec (m + 1)
    simp only [show m + 1 + 2 = m + 3 by omega, show m + 1 + 1 = m + 2 by omega, show m + 1 + 0 = m + 1 by omega] at hr
    simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
    rw [hr]; ring
  · have hX : (PowerSeries.mk fun n => (a (n + 1) : ℚ)) * (1 - 9 * X + 2 * X ^ 2) =
        PowerSeries.mk (fun n => (a (n + 1) : ℚ)) + C (-9 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 1) + C (2 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 2) := by
      simp only [map_neg, map_ofNat, map_one, neg_mul, one_mul]; ring
    rw [hX, show (9 * (25 - 6 * X) : PowerSeries ℚ) = C (225 : ℚ) * X ^ 0 + C (-54 : ℚ) * X ^ 1 by
      simp only [map_neg, map_ofNat, map_one, neg_mul, one_mul, pow_zero, mul_one]; ring]
    ext c
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge c 2 with h | h
    · have e : ∀ t : ℕ, t ≤ 2 → True := fun _ _ => trivial
      interval_cases c <;> simp [show (a 1 : ℚ) = 225 by exact_mod_cast a1, show (a 2 : ℚ) = 1971 by exact_mod_cast a2] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, c = m + 2 := ⟨c - 2, by omega⟩
      simp only [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m + 0 by omega, show 1 ≤ m + 2 by omega, show 2 ≤ m + 2 by omega, if_true, show m + 2 ≠ 0 by omega, show m + 2 ≠ 1 by omega, if_false, coeff_C]
      have hr := a_rec (m + 1)
      simp only [show m + 1 + 2 = m + 2 + 1 by omega, show m + 1 + 1 = m + 1 + 1 by omega, show m + 1 + 0 = m + 0 + 1 by omega] at hr
      have hq := congrArg (fun z : ℤ => (z : ℚ)) hr
      push_cast at hq
      first | (simp; linarith) | linarith | (push_cast; linarith)

end OMA.P_oeis_a203829

theorem OMA.solution : type_of% @OMA.S_oeis_a203829.main := OMA.P_oeis_a203829.full
