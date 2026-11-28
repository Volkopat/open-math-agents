import OMAStatements.S_oeis_a229439
import Mathlib

/-!
# oeis-a229439: counting the n X 2 arrays

Split an array (a list of rows) into its top row and the rest. The row and vertical conditions
are a chain condition, so the number of valid arrays with a given top row satisfies a linear
recursion over the next row; the column condition (left column lexicographically at most the
right one) only adds the case split on whether the top row is diagonal. Both counts have explicit
polynomial closed forms, checked by induction over the nine possible top rows. Summing them gives
Hardin's quartic, and the generating function and Barker's recurrence follow from it.

Source: OEIS A229439, https://oeis.org/A229439.
-/
namespace OMA.P_oeis_a229439

open OMA.S_oeis_a229439

abbrev R := Fin 3 × Fin 3

def rowOK (r : R) : Prop := ((r.2 : ℤ) - r.1) % 3 ≠ 1

def adj (r s : R) : Prop :=
  ((s.1 : ℤ) - r.1) % 3 ≠ 2 ∧ ((s.2 : ℤ) - r.2) % 3 ≠ 2 ∧ toLex r ≤ toLex s

instance : DecidablePred rowOK := fun r => by unfold rowOK; infer_instance
instance (r s : R) : Decidable (adj r s) := by unfold adj; infer_instance

open Classical

/-- Rows and vertical conditions only. -/
def Pall (l : List R) : Prop := (∀ r ∈ l, rowOK r) ∧ l.IsChain adj

lemma isSol_iff (l : List R) : IsSolution l ↔ Pall l ∧ l.map Prod.fst ≤ l.map Prod.snd := by
  unfold IsSolution Pall rowOK adj; tauto

lemma pall_cons_nil (r : R) : Pall [r] ↔ rowOK r := by
  simp [Pall]

lemma pall_cons_cons (r s : R) (m : List R) :
    Pall (r :: s :: m) ↔ rowOK r ∧ adj r s ∧ Pall (s :: m) := by
  unfold Pall
  rw [List.isChain_cons]
  simp only [List.mem_cons, forall_eq_or_imp, List.head?_cons, Option.mem_def,
    Option.some.injEq, forall_eq']
  tauto

lemma col_cons (r : R) (l : List R) :
    (r :: l).map Prod.fst ≤ (r :: l).map Prod.snd ↔
      r.1 < r.2 ∨ (r.1 = r.2 ∧ l.map Prod.fst ≤ l.map Prod.snd) := by
  simp only [List.map_cons]
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq]
  change (List.Lex (· < ·) _ _ ∨ _) ↔ (_ ∨ _ ∧ (List.Lex (· < ·) _ _ ∨ _))
  rw [List.cons_lex_cons_iff, List.cons.injEq]
  tauto

/-- The lists of length `n`. -/
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

noncomputable def fa (n : ℕ) (r : R) : ℕ := ((LL n).filter (fun l => Pall (r :: l))).card
noncomputable def fc (n : ℕ) (r : R) : ℕ :=
  ((LL n).filter (fun l => IsSolution (r :: l))).card

lemma a_succ (n : ℕ) : a (n + 1) = ∑ r : R, fc n r := by
  have e : {l : List R // l.length = n + 1 ∧ IsSolution l} ≃
      {l // l ∈ (LL (n + 1)).filter IsSolution} :=
    Equiv.subtypeEquivRight (fun l => by simp [mem_LL])
  rw [a, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, card_cons]
  rfl

lemma fa_zero (r : R) : fa 0 r = if rowOK r then 1 else 0 := by
  unfold fa; simp only [LL]; rw [Finset.filter_singleton]; split_ifs with h1 h2 h2 <;>
    simp_all [pall_cons_nil]

lemma fc_zero (r : R) : fc 0 r = if rowOK r ∧ r.1 ≤ r.2 then 1 else 0 := by
  unfold fc; simp only [LL]; rw [Finset.filter_singleton]
  have : IsSolution [r] ↔ rowOK r ∧ r.1 ≤ r.2 := by
    rw [isSol_iff, pall_cons_nil, col_cons]
    simp only [List.map_nil, le_refl, and_true]
    constructor
    · rintro ⟨h, h' | h'⟩ <;> [exact ⟨h, h'.le⟩; exact ⟨h, h'.le⟩]
    · rintro ⟨h, h'⟩; exact ⟨h, lt_or_eq_of_le h'⟩
  by_cases h : rowOK r ∧ r.1 ≤ r.2
  · rw [if_pos (this.mpr h), if_pos h]; rfl
  · rw [if_neg (fun h' => h (this.mp h')), if_neg h]; rfl

lemma fa_succ (n : ℕ) (r : R) :
    fa (n + 1) r = ∑ s : R, if rowOK r ∧ adj r s then fa n s else 0 := by
  unfold fa
  rw [card_cons]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [pall_cons_cons]
  split_ifs with h
  · congr 1; ext m; simp [h]
  · simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro m _ hm; exact h ⟨hm.1, hm.2.1⟩

lemma fc_succ (n : ℕ) (r : R) :
    fc (n + 1) r = ∑ s : R, if rowOK r ∧ adj r s then
      (if r.1 < r.2 then fa n s else if r.1 = r.2 then fc n s else 0) else 0 := by
  unfold fc fa
  rw [card_cons]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [isSol_iff, pall_cons_cons, col_cons]
  split_ifs with h h1 h2
  · congr 1; ext m; simp only [Finset.mem_filter]; constructor
    · rintro ⟨hm, hp, _⟩; exact ⟨hm, hp.2.2⟩
    · rintro ⟨hm, hp⟩; exact ⟨hm, ⟨h.1, h.2, hp⟩, Or.inl h1⟩
  · congr 1; ext m; simp only [Finset.mem_filter, isSol_iff]; constructor
    · rintro ⟨hm, hp, hc | hc⟩
      · exact absurd hc h1
      · exact ⟨hm, hp.2.2, hc.2⟩
    · rintro ⟨hm, hp, hc⟩; exact ⟨hm, ⟨h.1, h.2, hp⟩, Or.inr ⟨h2, hc⟩⟩
  · simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro m _ ⟨_, hc | hc⟩
    · exact h1 hc
    · exact h2 hc.1
  · simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro m _ ⟨hp, _⟩; exact h ⟨hp.1, hp.2.1⟩


/-- Closed forms of `fa n r`. -/
def PA (r : R) (x : ℚ) : ℚ :=
  if r = (0, 0) then (x + 1) * (x ^ 3 + 9 * x ^ 2 + 2 * x + 24) / 24
  else if r = (0, 2) then (x + 1) * (x ^ 3 + 5 * x ^ 2 - 6 * x + 24) / 24
  else if r = (1, 0) then (x ^ 3 + 6 * x ^ 2 + 5 * x + 6) / 6
  else if r = (1, 1) then (x + 1) * (x + 2) / 2
  else if r = (2, 1) then x + 1
  else if r = (2, 2) then 1
  else 0

/-- Closed forms of `fc n r`. -/
def PC (r : R) (x : ℚ) : ℚ :=
  if r = (0, 0) then (x ^ 2 + x + 2) / 2
  else if r = (0, 2) then (x + 1) * (x ^ 3 + 5 * x ^ 2 - 6 * x + 24) / 24
  else if r = (1, 1) then x + 1
  else if r = (2, 2) then 1
  else 0

theorem fa_closed (n : ℕ) : ∀ r, (fa n r : ℚ) = PA r n := by
  induction n with
  | zero =>
    intro r; rw [fa_zero]
    fin_cases r <;> simp +decide [PA]
  | succ n ih =>
    intro r; rw [fa_succ]; push_cast
    simp only [Fintype.sum_prod_type, Fin.sum_univ_three]
    fin_cases r <;> simp +decide only [ih, if_true, if_false] <;>
      simp +decide [PA] <;> ring

theorem fc_closed (n : ℕ) : ∀ r, (fc n r : ℚ) = PC r n := by
  induction n with
  | zero =>
    intro r; rw [fc_zero]
    fin_cases r <;> simp +decide [PC, PA]
  | succ n ih =>
    intro r; rw [fc_succ]; push_cast
    simp only [Fintype.sum_prod_type, Fin.sum_univ_three]
    fin_cases r <;> simp +decide only [ih, fa_closed, if_true, if_false] <;>
      simp +decide [PC, PA] <;> ring

theorem a_closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = (1 / 24) * n ^ 4 + (1 / 12) * n ^ 3 -
    (1 / 24) * n ^ 2 + (23 / 12) * n + 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a_succ]; push_cast
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, fc_closed]
  simp +decide [PC, PA]
  ring


lemma av (k : ℕ) : (a (k + 1) : ℚ) = (1 / 24) * ((k : ℚ) + 1) ^ 4 + (1 / 12) * ((k : ℚ) + 1) ^ 3 -
    (1 / 24) * ((k : ℚ) + 1) ^ 2 + (23 / 12) * ((k : ℚ) + 1) + 2 := by
  rw [a_closed (k + 1) (by omega)]; push_cast; ring

open PowerSeries in
theorem full :
    (∀ n ≥ 1, (a n : ℚ) = (1 / 24) * n ^ 4 + (1 / 12) * n ^ 3 - (1 / 24) * n ^ 2 +
      (23 / 12) * n + 2) ∧
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 5 =
      4 - 13 * X + 18 * X ^ 2 - 10 * X ^ 3 + 2 * X ^ 4) ∧
    (∀ n > 5, (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) +
      a (n - 5)) := by
  refine ⟨fun n hn => a_closed n hn, ?_, fun n hn => ?_⟩
  · have hX : (PowerSeries.mk fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 5 =
        PowerSeries.mk (fun n => (a (n + 1) : ℚ))
          - C (5 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 1)
          + C (10 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 2)
          - C (10 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 3)
          + C (5 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 4)
          - PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 5 := by
      simp only [map_ofNat]; ring
    rw [hX, show (4 - 13 * X + 18 * X ^ 2 - 10 * X ^ 3 + 2 * X ^ 4 : PowerSeries ℚ) =
      C (4 : ℚ) - C (13 : ℚ) * X ^ 1 + C (18 : ℚ) * X ^ 2 - C (10 : ℚ) * X ^ 3 +
        C (2 : ℚ) * X ^ 4 by simp only [map_ofNat]; ring]
    ext k
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_C,
      coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge k 5 with h | h
    · interval_cases k <;> simp [av] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 5 := ⟨k - 5, by omega⟩
      simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
        show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega,
        show m + 5 - 5 = m by omega, show 1 ≤ m + 5 by omega, show 2 ≤ m + 5 by omega,
        show 3 ≤ m + 5 by omega, show 4 ≤ m + 5 by omega, show 5 ≤ m + 5 by omega, if_true,
        show m + 5 ≠ 0 by omega, show m + 5 ≠ 1 by omega, show m + 5 ≠ 2 by omega,
        show m + 5 ≠ 3 by omega, show m + 5 ≠ 4 by omega, if_false, av]
      push_cast; ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    simp only [show m + 6 - 1 = m + 4 + 1 by omega, show m + 6 - 2 = m + 3 + 1 by omega,
      show m + 6 - 3 = m + 2 + 1 by omega, show m + 6 - 4 = m + 1 + 1 by omega,
      show m + 6 - 5 = m + 1 by omega, show m + 6 = m + 5 + 1 by omega]
    have : ((a (m + 5 + 1) : ℤ) : ℚ) = 5 * (a (m + 4 + 1) : ℚ) - 10 * (a (m + 3 + 1) : ℚ) +
        10 * (a (m + 2 + 1) : ℚ) - 5 * (a (m + 1 + 1) : ℚ) + (a (m + 1) : ℚ) := by
      push_cast; rw [av, av, av, av, av, av]; push_cast; ring
    exact_mod_cast this

end OMA.P_oeis_a229439

theorem OMA.solution : type_of% @OMA.S_oeis_a229439.main := OMA.P_oeis_a229439.full
