import OMAStatements.S_oeis_a183635
import Mathlib

/-!
# oeis-a183635: counting the (n+1) X 3 arrays

Split an array (a list of rows) into its top row and the rest. The subblock condition is a chain
condition on consecutive rows, so the number of valid arrays with a given top row satisfies a
linear recursion over the next row. Its explicit closed forms (combinations of 1, 2^n, 3^n and 4^n)
are checked by induction over the 64 possible top rows. Summing them gives Barker's closed form, and
the generating function and the recurrence follow from it.

Source: OEIS A183635, https://oeis.org/A183635.
-/
namespace OMA.P_oeis_a183635

open OMA.S_oeis_a183635

abbrev R := Fin 3 → Fin 4

lemma sumk (g : R → ℚ) : ∑ s : R, g s = ∑ y0 : Fin 4, ∑ y1 : Fin 4, ∑ y2 : Fin 4, g ![y0, y1, y2] := by
  let e : Fin 4 × Fin 4 × Fin 4 ≃ R :=
    ⟨fun p => ![p.1, p.2.1, p.2.2], fun f => (f 0, f 1, f 2), fun p => by simp,
      fun f => by ext i; fin_cases i <;> rfl⟩
  rw [← e.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

def rowOK (_r : R) : Prop := True

def adj (r s : R) : Prop := ∀ j : Fin 2, (r j.castSucc : ℕ) + r j.succ + s j.castSucc + s j.succ = 6

instance : DecidablePred rowOK := fun r => by unfold rowOK; infer_instance
instance (r s : R) : Decidable (adj r s) := by unfold adj; infer_instance

open Classical

def Pall (l : List R) : Prop := (∀ r ∈ l, rowOK r) ∧ l.IsChain adj

lemma isSol_iff (l : List R) : IsSolution l ↔ Pall l := by
  unfold IsSolution Pall rowOK adj
  first | exact Iff.rfl | simp only [implies_true, true_and] | simp only [Fin.forall_fin_succ, Fin.forall_fin_one, IsEmpty.forall_iff, Fin.succ_zero_eq_one,
    Fin.castSucc_zero, Fin.succ_one_eq_two, Fin.castSucc_one, Fin.reduceSucc, Fin.reduceCastSucc]

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

def T : Fin 4 → Fin 4 → Fin 4 → ℕ → ℚ :=
  ![![![(fun n : ℕ => ((1 : ℚ) * (n : ℚ) ^ 0)), (fun n : ℕ => ((1 : ℚ) * (n : ℚ) ^ 0)), (fun n : ℕ => ((1 : ℚ) * (n : ℚ) ^ 0)), (fun n : ℕ => ((1 : ℚ) * (n : ℚ) ^ 0))], ![(fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (2 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (2 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (2 : ℚ) ^ n), (fun n : ℕ => ((1 : ℚ) * (n : ℚ) ^ 0))], ![(fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (3 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (3 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (2 : ℚ) ^ n), (fun n : ℕ => ((1 : ℚ) * (n : ℚ) ^ 0))], ![(fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (4 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (3 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (2 : ℚ) ^ n), (fun n : ℕ => ((1 : ℚ) * (n : ℚ) ^ 0))]], ![![(fun n : ℕ => ((1 : ℚ) * (n : ℚ) ^ 0)), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (2 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (2 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (2 : ℚ) ^ n)], ![(fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (2 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (3 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (3 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (2 : ℚ) ^ n)], ![(fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (3 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (4 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (3 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (2 : ℚ) ^ n)], ![(fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (3 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (3 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (2 : ℚ) ^ n), (fun n : ℕ => ((1 : ℚ) * (n : ℚ) ^ 0))]], ![![(fun n : ℕ => ((1 : ℚ) * (n : ℚ) ^ 0)), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (2 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (3 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (3 : ℚ) ^ n)], ![(fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (2 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (3 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (4 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (3 : ℚ) ^ n)], ![(fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (2 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (3 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (3 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (2 : ℚ) ^ n)], ![(fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (2 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (2 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (2 : ℚ) ^ n), (fun n : ℕ => ((1 : ℚ) * (n : ℚ) ^ 0))]], ![![(fun n : ℕ => ((1 : ℚ) * (n : ℚ) ^ 0)), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (2 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (3 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (4 : ℚ) ^ n)], ![(fun n : ℕ => ((1 : ℚ) * (n : ℚ) ^ 0)), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (2 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (3 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (3 : ℚ) ^ n)], ![(fun n : ℕ => ((1 : ℚ) * (n : ℚ) ^ 0)), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (2 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (2 : ℚ) ^ n), (fun n : ℕ => (0) + ((1 : ℚ) * (n : ℚ) ^ 0) * (2 : ℚ) ^ n)], ![(fun n : ℕ => ((1 : ℚ) * (n : ℚ) ^ 0)), (fun n : ℕ => ((1 : ℚ) * (n : ℚ) ^ 0)), (fun n : ℕ => ((1 : ℚ) * (n : ℚ) ^ 0)), (fun n : ℕ => ((1 : ℚ) * (n : ℚ) ^ 0))]]]

set_option maxHeartbeats 40000000 in
theorem f_closed (n : ℕ) : ∀ (i0 i1 i2 : Fin 4), (f n ![i0, i1, i2] : ℚ) = T i0 i1 i2 n := by
  induction n with
  | zero =>
    intro i0 i1 i2; rw [f_zero]
    fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;> simp +decide [T, rowOK] <;> norm_num
  | succ n ih =>
    intro i0 i1 i2; rw [f_succ]; push_cast
    rw [sumk]
    simp only [Fin.sum_univ_four]
    fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;>
      simp +decide only [rowOK, adj, if_true, if_false, add_zero, zero_add] <;>
      (try simp only [ih]) <;>
      simp [T] <;> ring

set_option maxHeartbeats 4000000 in
theorem a_closed (n : ℕ) : (a n : ℚ) = 18 + 3 * 2 ^ (3 + n) + 2 * 3 ^ (2 + n) + 4 ^ (1 + n) := by
  rw [a_eq]; push_cast
  rw [sumk]
  simp only [Fin.sum_univ_four, f_closed]
  simp [T]
  ring

open PowerSeries in
theorem full :
    (∀ n > 4, (a n : ℤ) = 10 * a (n - 1) - 35 * a (n - 2) + 50 * a (n - 3) - 24 * a (n - 4)) ∧
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) *
        ((1 - X) * (1 - 2 * X) * (1 - 3 * X) * (1 - 4 * X)) =
      4 * (34 - 255 * X + 578 * X ^ 2 - 384 * X ^ 3)) ∧
    (∀ n ≥ 1, (a n : ℚ) = 18 + 3 * 2 ^ (3 + n) + 2 * 3 ^ (2 + n) + 4 ^ (1 + n)) := by
  refine ⟨fun n hn => ?_, ?_, fun n hn => by rw [a_closed n]⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
    qify
    simp only [a_closed]; push_cast; ring
  · have hX : (PowerSeries.mk fun n => (a (n + 1) : ℚ)) * ((1 - X) * (1 - 2 * X) * (1 - 3 * X) * (1 - 4 * X)) =
        PowerSeries.mk (fun n => (a (n + 1) : ℚ)) + C (-10 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 1) + C (35 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 2) + C (-50 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 3) + C (24 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 4) := by
      simp only [map_neg, map_ofNat, map_one, neg_mul, one_mul]; ring
    rw [hX, show (4 * (34 - 255 * X + 578 * X ^ 2 - 384 * X ^ 3) : PowerSeries ℚ) = C (136 : ℚ) * X ^ 0 + C (-1020 : ℚ) * X ^ 1 + C (2312 : ℚ) * X ^ 2 + C (-1536 : ℚ) * X ^ 3 by
      simp only [map_neg, map_ofNat, map_one, neg_mul, one_mul, pow_zero, mul_one]; ring]
    ext c
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge c 4 with h | h
    · interval_cases c <;> simp [a_closed] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, c = m + 4 := ⟨c - 4, by omega⟩
      simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m + 0 by omega, show 1 ≤ m + 4 by omega, show 2 ≤ m + 4 by omega, show 3 ≤ m + 4 by omega, show 4 ≤ m + 4 by omega, if_true, show m + 4 ≠ 0 by omega, show m + 4 ≠ 1 by omega, show m + 4 ≠ 2 by omega, show m + 4 ≠ 3 by omega, if_false, coeff_C, a_closed]
      first | (push_cast; ring) | (simp; push_cast; ring) | simp

end OMA.P_oeis_a183635

theorem OMA.solution : type_of% @OMA.S_oeis_a183635.main := OMA.P_oeis_a183635.full
