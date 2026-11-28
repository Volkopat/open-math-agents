import OMAStatements.S_oeis_a188557
import Mathlib

/-!
# oeis-a188557: counting the 6 X n arrays

Split an array (a list of columns) into its first column and the rest. All the conditions are a
condition on each column and a chain condition on consecutive columns, so the number of valid
arrays with a given first column satisfies a linear recursion over the next column. Its explicit
polynomial closed forms are checked by induction over the 64 possible first columns. Summing them
gives Hardin's polynomial, and the generating function and Barker's recurrence follow from it.

Source: OEIS A188557, https://oeis.org/A188557.
-/
namespace OMA.P_oeis_a188557

open OMA.S_oeis_a188557

abbrev R := Fin 6 → Fin 2

lemma sumk (g : R → ℚ) : ∑ s : R, g s = ∑ y0 : Fin 2, ∑ y1 : Fin 2, ∑ y2 : Fin 2, ∑ y3 : Fin 2, ∑ y4 : Fin 2, ∑ y5 : Fin 2, g ![y0, y1, y2, y3, y4, y5] := by
  let e : Fin 2 × Fin 2 × Fin 2 × Fin 2 × Fin 2 × Fin 2 ≃ R :=
    ⟨fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2], fun f => (f 0, f 1, f 2, f 3, f 4, f 5), fun p => by simp,
      fun f => by ext i; fin_cases i <;> rfl⟩
  rw [← e.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

def rowOK (c : R) : Prop := ∀ i : Fin 5, ¬ (c i.castSucc = 0 ∧ c i.succ = 1)

def adj (c d : R) : Prop := (∀ i, ¬ (c i = 0 ∧ d i = 1)) ∧
  ∀ i : Fin 5, ¬ (c i.castSucc = 0 ∧ d i.succ = 1) ∧ ¬ (d i.castSucc = 0 ∧ c i.succ = 1)

instance : DecidablePred rowOK := fun r => by unfold rowOK; infer_instance
instance (r s : R) : Decidable (adj r s) := by unfold adj; infer_instance

open Classical

def Pall (l : List R) : Prop := (∀ r ∈ l, rowOK r) ∧ l.IsChain adj

lemma isSol_iff (l : List R) : IsSolution l ↔ Pall l := by
  unfold IsSolution Pall rowOK adj
  first | exact Iff.rfl | simp only [Fin.forall_fin_succ, Fin.forall_fin_one, IsEmpty.forall_iff, Fin.succ_zero_eq_one,
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

lemma a_succ (n : ℕ) : a (n + 1) = ∑ r : R, f n r := by
  have e : {l : List R // l.length = n + 1 ∧ IsSolution l} ≃
      {l // l ∈ (LL (n + 1)).filter Pall} :=
    Equiv.subtypeEquivRight (fun l => by simp [mem_LL, isSol_iff])
  rw [a, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, card_cons]
  rfl

lemma a_zero : a 0 = 1 := by
  have e : {l : List R // l.length = 0 ∧ IsSolution l} ≃ {l // l ∈ (LL 0).filter Pall} :=
    Equiv.subtypeEquivRight (fun l => by simp [mem_LL, isSol_iff])
  rw [a, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  simp only [LL]
  rw [Finset.filter_singleton, if_pos (by simp [Pall])]
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

def v : Fin 7 → R := ![![0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0], ![1, 1, 1, 1, 0, 0], ![1, 1, 1, 1, 1, 0], ![1, 1, 1, 1, 1, 1]]

lemma cover (s : R) (hs : rowOK s) : s ∈ (Finset.univ : Finset (Fin 7)).image v := by
  rw [Finset.mem_image]
  have hs' : s = ![s 0, s 1, s 2, s 3, s 4, s 5] := by ext i; fin_cases i <;> rfl
  rw [hs'] at hs ⊢
  generalize s 0 = y0, s 1 = y1, s 2 = y2, s 3 = y3, s 4 = y4, s 5 = y5 at hs ⊢
  fin_cases y0 <;> fin_cases y1 <;> fin_cases y2 <;> fin_cases y3 <;> fin_cases y4 <;> fin_cases y5 <;>
    first | exact absurd hs (by decide) | (simp only [Finset.mem_univ, true_and]; decide)

lemma v_inj : Function.Injective v := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

lemma red (h : R → ℚ) (hz : ∀ s, ¬ rowOK s → h s = 0) : ∑ s : R, h s = ∑ j : Fin 7, h (v j) := by
  rw [← Finset.sum_image (fun i _ j _ e => v_inj e)]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun s _ hs => hz s fun h' => hs (cover s h')

lemma v_ok (j : Fin 7) : rowOK (v j) := by fin_cases j <;> decide

lemma f_bad (n : ℕ) (s : R) (hs : ¬ rowOK s) : f n s = 0 := by
  unfold f
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro l _ h; exact hs (h.1 s (by simp))

lemma f_succ' (n : ℕ) (j : Fin 7) :
    (f (n + 1) (v j) : ℚ) = ∑ i : Fin 7, if adj (v j) (v i) then (f n (v i) : ℚ) else 0 := by
  rw [f_succ]; push_cast
  rw [red]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [v_ok j, true_and]; try (split_ifs <;> simp)
  · intro s hs; split_ifs <;> simp [f_bad n s hs]

def T : Fin 7 → ℚ → ℚ := ![(fun x : ℚ => ((1 : ℚ) / 1) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 1) * x ^ 1 + ((1 : ℚ) / 1) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 2) * x ^ 2 + ((1 : ℚ) / 2) * x ^ 1 + ((1 : ℚ) / 1) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 6) * x ^ 3 + ((5 : ℚ) / 6) * x ^ 1 + ((1 : ℚ) / 1) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 24) * x ^ 4 + ((-1 : ℚ) / 12) * x ^ 3 + ((11 : ℚ) / 24) * x ^ 2 + ((7 : ℚ) / 12) * x ^ 1 + ((1 : ℚ) / 1) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 120) * x ^ 5 + ((-1 : ℚ) / 24) * x ^ 4 + ((5 : ℚ) / 24) * x ^ 3 + ((1 : ℚ) / 24) * x ^ 2 + ((47 : ℚ) / 60) * x ^ 1 + ((1 : ℚ) / 1) * x ^ 0), (fun x : ℚ => ((1 : ℚ) / 720) * x ^ 6 + ((-1 : ℚ) / 80) * x ^ 5 + ((11 : ℚ) / 144) * x ^ 4 + ((-5 : ℚ) / 48) * x ^ 3 + ((19 : ℚ) / 45) * x ^ 2 + ((37 : ℚ) / 60) * x ^ 1 + ((1 : ℚ) / 1) * x ^ 0)]

set_option maxHeartbeats 4000000 in
theorem f_closed (n : ℕ) : ∀ j : Fin 7, (f n (v j) : ℚ) = T j n := by
  induction n with
  | zero =>
    intro j; rw [f_zero, if_pos (v_ok j)]
    fin_cases j <;> simp [T]
  | succ n ih =>
    intro j; rw [f_succ']
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, ih]
    fin_cases j <;> simp +decide only [if_true, if_false, add_zero, zero_add] <;> simp [T] <;> ring

set_option maxHeartbeats 4000000 in
theorem a_closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = ((1 : ℚ) / 720) * (n : ℚ) ^ 6 + ((-1 : ℚ) / 80) * (n : ℚ) ^ 5 + ((17 : ℚ) / 144) * (n : ℚ) ^ 4 + ((-3 : ℚ) / 16) * (n : ℚ) ^ 3 + ((497 : ℚ) / 360) * (n : ℚ) ^ 2 + ((17 : ℚ) / 10) * (n : ℚ) ^ 1 + (4 : ℚ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a_succ]; push_cast
  rw [red _ (fun s hs => by simp [f_bad m s hs])]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, f_closed]
  simp [T]
  ring

lemma av (j : ℕ) : (a (j + 1) : ℚ) = ((1 : ℚ) / 720) * ((j : ℚ) + 1) ^ 6 + ((-1 : ℚ) / 80) * ((j : ℚ) + 1) ^ 5 + ((17 : ℚ) / 144) * ((j : ℚ) + 1) ^ 4 + ((-3 : ℚ) / 16) * ((j : ℚ) + 1) ^ 3 + ((497 : ℚ) / 360) * ((j : ℚ) + 1) ^ 2 + ((17 : ℚ) / 10) * ((j : ℚ) + 1) ^ 1 + (4 : ℚ) := by
  rw [a_closed (j + 1) (by omega)]; push_cast; ring

open PowerSeries in
theorem full :
    (∀ n ≥ 1, (a n : ℚ) = (1 / 720) * n ^ 6 - (1 / 80) * n ^ 5 + (17 / 144) * n ^ 4 - (3 / 16) * n ^ 3 + (497 / 360) * n ^ 2 + (17 / 10) * n + 4) ∧
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 7 =
      7 - 36 * X + 80 * X ^ 2 - 96 * X ^ 3 + 66 * X ^ 4 - 24 * X ^ 5 + 4 * X ^ 6) ∧
    (∀ n > 7, (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + 1 * a (n - 7)) := by
  refine ⟨fun n hn => by rw [a_closed n hn]; ring, ?_, fun n hn => ?_⟩
  · have hX : (PowerSeries.mk (fun n => (a (n + 1) : ℚ))) * (1 - X) ^ 7 =
        PowerSeries.mk (fun n => (a (n + 1) : ℚ)) + C (-7 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 1) + C (21 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 2) + C (-35 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 3) + C (35 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 4) + C (-21 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 5) + C (7 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 6) + C (-1 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 7) := by
      simp only [map_neg, map_ofNat, map_one, neg_mul, one_mul]; ring
    rw [hX, show (7 - 36 * X + 80 * X ^ 2 - 96 * X ^ 3 + 66 * X ^ 4 - 24 * X ^ 5 + 4 * X ^ 6 : PowerSeries ℚ) = C (7 : ℚ) * X ^ 0 + C (-36 : ℚ) * X ^ 1 + C (80 : ℚ) * X ^ 2 + C (-96 : ℚ) * X ^ 3 + C (66 : ℚ) * X ^ 4 + C (-24 : ℚ) * X ^ 5 + C (4 : ℚ) * X ^ 6 by
      simp only [map_neg, map_ofNat, map_one, neg_mul, one_mul, pow_zero, mul_one]; ring]
    ext c
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge c 7 with h | h
    · interval_cases c <;> simp [av] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, c = m + 7 := ⟨c - 7, by omega⟩
      simp only [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega, show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega, show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega, show m + 7 - 7 = m + 0 by omega, show 1 ≤ m + 7 by omega, show 2 ≤ m + 7 by omega, show 3 ≤ m + 7 by omega, show 4 ≤ m + 7 by omega, show 5 ≤ m + 7 by omega, show 6 ≤ m + 7 by omega, show 7 ≤ m + 7 by omega, if_true, show m + 7 ≠ 0 by omega, show m + 7 ≠ 1 by omega, show m + 7 ≠ 2 by omega, show m + 7 ≠ 3 by omega, show m + 7 ≠ 4 by omega, show m + 7 ≠ 5 by omega, show m + 7 ≠ 6 by omega, if_false, coeff_C]
      simp only [av]
      first | (push_cast; ring) | (simp; push_cast; ring) | simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    simp only [show m + 8 - 1 = m + 6 + 1 by omega, show m + 8 - 2 = m + 5 + 1 by omega, show m + 8 - 3 = m + 4 + 1 by omega, show m + 8 - 4 = m + 3 + 1 by omega, show m + 8 - 5 = m + 2 + 1 by omega, show m + 8 - 6 = m + 1 + 1 by omega, show m + 8 - 7 = m + 0 + 1 by omega, show m + 8 = m + 7 + 1 by omega]
    qify
    simp only [av]; push_cast; ring

end OMA.P_oeis_a188557

theorem OMA.solution : type_of% @OMA.S_oeis_a188557.main := OMA.P_oeis_a188557.full
