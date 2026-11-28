import OMAStatements.S_oeis_a183682
import Mathlib

namespace OMA.A183682Proof

open OMA.S_oeis_a183682 PowerSeries

/-- A row of the array. -/
abbrev Row := Fin 3 → Fin 2

/-- Two consecutive rows whose two 2 X 2 blocks are both nonsingular. -/
def Ok (r s : Row) : Prop :=
  ∀ j : Fin 2, ((r j.castSucc).val : ℤ) * (s j.succ).val - ((r j.succ).val : ℤ) * (s j.castSucc).val ≠ 0

instance (r s : Row) : Decidable (Ok r s) := by
  unfold Ok
  infer_instance

/-- 0/1 indicator of `Ok`. -/
def c (r s : Row) : ℕ := if Ok r s then 1 else 0

theorem valid_cons {n : ℕ} (g : Grid (n + 1)) :
    IsValid g ↔ Ok (g 0) (Fin.tail g 0) ∧ IsValid (Fin.tail g) := by
  unfold IsValid Ok
  rw [Fin.forall_fin_succ]
  apply and_congr
  · rfl
  · apply forall_congr'
    intro i
    simp only [Fin.tail]
    rw [← Fin.succ_castSucc]

/-- Valid arrays of n+1 rows with first row r. -/
def h (n : ℕ) (r : Row) : ℕ := (Finset.univ.filter (fun g : Grid n => IsValid g ∧ g 0 = r)).card

theorem h_zero (r : Row) : h 0 r = 1 := by
  rw [h, Finset.card_eq_one]
  refine ⟨fun _ => r, ?_⟩
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨_, h0⟩
    funext i
    rw [Fin.fin_one_eq_zero i, h0]
  · rintro rfl
    exact ⟨fun i => i.elim0, rfl⟩

theorem h_succ (n : ℕ) (r : Row) : h (n + 1) r = ∑ s : Row, c r s * h n s := by
  have e1 : h (n + 1) r =
      (Finset.univ.filter (fun t : Grid n => Ok r (t 0) ∧ IsValid t)).card := by
    rw [h]
    apply Finset.card_nbij' (fun g => Fin.tail g) (fun t => Fin.cons r t)
    · intro g hg
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hg ⊢
      rw [valid_cons] at hg
      rw [← hg.2]
      exact hg.1
    · intro t ht
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
      refine ⟨?_, Fin.cons_zero _ _⟩
      rw [valid_cons]
      simp only [Fin.cons_zero, Fin.tail_cons]
      exact ht
    · intro g hg
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hg
      rw [← hg.2]
      exact Fin.cons_self_tail g
    · intro t _
      exact Fin.tail_cons _ _
  rw [e1, Finset.card_eq_sum_card_fiberwise (f := fun t : Grid n => t 0) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.filter_filter, c, h]
  split_ifs with hc
  · rw [one_mul]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, hv⟩, h0⟩
      exact ⟨hv, h0⟩
    · rintro ⟨hv, h0⟩
      exact ⟨⟨h0 ▸ hc, hv⟩, h0⟩
  · rw [zero_mul, Finset.card_eq_zero]
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
      not_and]
    intro hct h0
    exact hc (h0 ▸ hct.1)

theorem a_succ (n : ℕ) : a (n + 1) = ((∑ r : Row, h (n + 1) r : ℕ) : ℤ) := by
  show ((Finset.univ.filter (fun g : Grid (n + 1) => IsValid g)).card : ℤ) = _
  congr 1
  rw [Finset.card_eq_sum_card_fiberwise (f := fun t : Grid (n + 1) => t 0) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.filter_filter, h]

/-- In-degree weights (Ok is symmetric, so this is also the out-degree). -/
def d (t : Row) : ℕ := ∑ r : Row, c r t

/-- Paths of length two ending at t. -/
def e (t : Row) : ℕ := ∑ r : Row, ∑ s : Row, c r s * c s t

theorem weights : ∀ t : Row, (∃ s, Ok t s) → e t = d t + 4 := by decide

theorem a1v : ∑ r : Row, ∑ s : Row, c r s = 12 := by decide

theorem a2v : ∑ r : Row, ∑ s : Row, c r s * ∑ t : Row, c s t = 32 := by decide

theorem sum_one (H : Row → ℕ) : ∑ r : Row, ∑ s : Row, c r s * H s = ∑ s : Row, d s * H s := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [d, Finset.sum_mul]

theorem sum_two (H : Row → ℕ) :
    ∑ r : Row, ∑ s : Row, c r s * ∑ t : Row, c s t * H t = ∑ t : Row, e t * H t := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun r _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [e, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem h_bad (n : ℕ) (t : Row) (ht : ¬ ∃ s, Ok t s) : h (n + 1) t = 0 := by
  rw [h_succ]
  apply Finset.sum_eq_zero
  intro s _
  rw [c, if_neg (fun hc => ht ⟨s, hc⟩), zero_mul]

theorem rec (k : ℕ) : a (k + 3) = a (k + 2) + 4 * a (k + 1) := by
  rw [a_succ, a_succ, a_succ]
  have e3 : ∑ r : Row, h (k + 3) r = ∑ t : Row, e t * h (k + 1) t := by
    simp_rw [h_succ (k + 2), h_succ (k + 1)]
    rw [sum_two]
  have e2 : ∑ r : Row, h (k + 2) r = ∑ t : Row, d t * h (k + 1) t := by
    simp_rw [h_succ (k + 1)]
    rw [sum_one]
  have key : ∀ t : Row, e t * h (k + 1) t = d t * h (k + 1) t + 4 * h (k + 1) t := by
    intro t
    by_cases ht : ∃ s, Ok t s
    · rw [weights t ht]; ring
    · rw [h_bad k t ht]; ring
  rw [e3, e2, Finset.sum_congr rfl (fun t _ => key t), Finset.sum_add_distrib, ← Finset.mul_sum]
  push_cast
  ring

theorem a1 : a 1 = 12 := by
  rw [a_succ]
  simp_rw [h_succ 0, h_zero, mul_one]
  rw [a1v]
  rfl

theorem a2 : a 2 = 32 := by
  rw [a_succ]
  simp_rw [h_succ 1, h_succ 0, h_zero, mul_one]
  rw [a2v]
  rfl

end OMA.A183682Proof

namespace OMA.A183682Proof

open OMA.S_oeis_a183682

/-- Barker's closed form, rewritten with the roots of x^2 = x + 4. -/
noncomputable def psi (n : ℕ) : ℝ :=
  ((1 - Real.sqrt 17) / 2) ^ n * ((-19 + 5 * Real.sqrt 17) / (2 * Real.sqrt 17)) +
    ((1 + Real.sqrt 17) / 2) ^ n * ((19 + 5 * Real.sqrt 17) / (2 * Real.sqrt 17))

theorem sq17 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)

theorem s17_ne : Real.sqrt 17 ≠ 0 := by positivity

theorem psi_rec (n : ℕ) : psi (n + 2) = psi (n + 1) + 4 * psi n := by
  have hb : ((1 - Real.sqrt 17) / 2) ^ 2 = (1 - Real.sqrt 17) / 2 + 4 := by
    linear_combination (1 / 4 : ℝ) * sq17
  have ha : ((1 + Real.sqrt 17) / 2) ^ 2 = (1 + Real.sqrt 17) / 2 + 4 := by
    linear_combination (1 / 4 : ℝ) * sq17
  simp only [psi, pow_succ]
  linear_combination
    ((1 - Real.sqrt 17) / 2) ^ n * ((-19 + 5 * Real.sqrt 17) / (2 * Real.sqrt 17)) * hb +
    ((1 + Real.sqrt 17) / 2) ^ n * ((19 + 5 * Real.sqrt 17) / (2 * Real.sqrt 17)) * ha

theorem psi1 : psi 1 = 12 := by
  have h := s17_ne
  simp only [psi, pow_one]
  field_simp
  linear_combination (-24 : ℝ) * sq17 + 24 * sq17 + 0 * sq17

theorem psi2 : psi 2 = 32 := by
  have h := s17_ne
  simp only [psi]
  field_simp
  ring_nf
  have h3 : Real.sqrt 17 ^ 3 = 17 * Real.sqrt 17 := by
    rw [pow_succ, sq17]
  rw [h3]
  ring

theorem closed_psi (k : ℕ) : (a (k + 1) : ℝ) = psi (k + 1) ∧ (a (k + 2) : ℝ) = psi (k + 2) := by
  induction k with
  | zero => exact ⟨by rw [a1, psi1]; norm_num, by rw [a2, psi2]; norm_num⟩
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [show k + 1 + 2 = k + 3 by omega, rec k, show k + 3 = (k + 1) + 2 by omega, psi_rec]
    push_cast
    rw [ih.1, ih.2]

theorem psi_eq (n : ℕ) : psi n = (2 : ℝ) ^ (-1 - (n : ℤ)) *
    ((1 - Real.sqrt 17) ^ n * (-19 + 5 * Real.sqrt 17) +
      (1 + Real.sqrt 17) ^ n * (19 + 5 * Real.sqrt 17)) / Real.sqrt 17 := by
  have h2 : (2 : ℝ) ^ (-1 - (n : ℤ)) = (1 / 2) * (1 / 2) ^ n := by
    rw [zpow_sub₀ two_ne_zero, zpow_neg_one, zpow_natCast, one_div_pow]
    ring
  have h := s17_ne
  have hX : (2 : ℝ) ^ n * (1 / 2) ^ n = 1 := by rw [← mul_pow]; norm_num
  rw [h2, psi, div_pow, div_pow]
  field_simp
  linear_combination (-((1 - Real.sqrt 17) ^ n * (-19 + Real.sqrt 17 * 5) +
    (1 + Real.sqrt 17) ^ n * (19 + Real.sqrt 17 * 5))) * hX

end OMA.A183682Proof

open OMA.S_oeis_a183682 OMA.A183682Proof PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a183682.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega]
    exact rec k
  · ext k
    have e1 : ∀ A : PowerSeries ℤ, A * (1 - X - 4 * X ^ 2) =
        A - C (1 : ℤ) * (A * X ^ 1) - C (4 : ℤ) * (A * X ^ 2) := by
      intro A
      rw [map_one, show (C (4 : ℤ) : PowerSeries ℤ) = 4 from map_ofNat C 4]
      ring
    have e2 : (4 * X * (3 + 5 * X) : PowerSeries ℤ) =
        C (12 : ℤ) * X ^ 1 + C (20 : ℤ) * X ^ 2 := by
      rw [show (C (12 : ℤ) : PowerSeries ℤ) = 12 from map_ofNat C 12,
        show (C (20 : ℤ) : PowerSeries ℤ) = 20 from map_ofNat C 20]
      ring
    rw [e1, e2]
    simp only [map_add, map_sub, coeff_mul_X_pow', coeff_C_mul, coeff_C, coeff_mk]
    rcases (show k ≤ 2 ∨ 3 ≤ k by omega) with hk | hk
    · have v0 : a 0 = 0 := rfl
      interval_cases k <;> simp [v0, a1, a2]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
      simp only [show j + 3 - 1 = j + 2 by omega, show j + 3 - 2 = j + 1 by omega,
        if_pos (show 1 ≤ j + 3 by omega), if_pos (show 2 ≤ j + 3 by omega),
        if_neg (show j + 2 ≠ 0 by omega), if_neg (show j + 1 ≠ 0 by omega), rec j]
      ring
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [(closed_psi k).1, psi_eq]
