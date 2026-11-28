import OMAStatements.S_oeis_a002467
import Mathlib

namespace OMA.A002467Proof

open Finset

lemma der_eq (n : ℕ) : (numDerangements n : ℝ)
    = (n.factorial : ℝ) * ∑ m ∈ range (n + 1), (-1 : ℝ) ^ m / (m.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h := numDerangements_succ k
    have h' : (numDerangements (k + 1) : ℝ)
        = ((k : ℝ) + 1) * (numDerangements k : ℝ) - (-1) ^ k := by exact_mod_cast h
    have hk : (k.factorial : ℝ) ≠ 0 := by positivity
    rw [h', ih, Finset.sum_range_succ _ (k + 1), Nat.factorial_succ]
    push_cast
    field_simp
    ring

lemma der_le (n : ℕ) : numDerangements n ≤ n.factorial := by
  have h := card_derangements_eq_numDerangements (Fin n)
  rw [Fintype.card_fin] at h
  rw [← h]
  calc Fintype.card (derangements (Fin n)) ≤ Fintype.card (Equiv.Perm (Fin n)) :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = n.factorial := by rw [Fintype.card_perm, Fintype.card_fin]

lemma key (k : ℕ) :
    |(numDerangements (k + 2) : ℝ) - ((k + 2).factorial : ℝ) * Real.exp (-1)| < 1 / 2 := by
  have hb := Real.exp_bound (x := -1) (by norm_num) (n := k + 3) (by omega)
  have hF : (0 : ℝ) < ((k + 2).factorial : ℝ) := by positivity
  rw [der_eq]
  have e : ((k + 2).factorial : ℝ) * ∑ m ∈ range (k + 2 + 1), (-1 : ℝ) ^ m / (m.factorial : ℝ)
      - (k + 2).factorial * Real.exp (-1)
      = -((k + 2).factorial * (Real.exp (-1) - ∑ m ∈ range (k + 3), (-1 : ℝ) ^ m / (m.factorial : ℝ))) := by
    ring
  rw [e, abs_neg, abs_mul, abs_of_pos hF]
  have hb' : |Real.exp (-1) - ∑ m ∈ range (k + 3), (-1 : ℝ) ^ m / (m.factorial : ℝ)|
      ≤ ((k : ℝ) + 4) / (((k : ℝ) + 3) * ((k + 2).factorial : ℝ) * ((k : ℝ) + 3)) := by
    refine hb.trans (le_of_eq ?_)
    rw [Nat.factorial_succ (k + 2)]
    simp only [abs_neg, abs_one, one_pow, one_mul]
    push_cast
    ring
  calc ((k + 2).factorial : ℝ) * |Real.exp (-1) - ∑ m ∈ range (k + 3), (-1 : ℝ) ^ m / (m.factorial : ℝ)|
      ≤ ((k + 2).factorial : ℝ) * (((k : ℝ) + 4) / (((k : ℝ) + 3) * ((k + 2).factorial : ℝ) * ((k : ℝ) + 3))) :=
        mul_le_mul_of_nonneg_left hb' hF.le
    _ = ((k : ℝ) + 4) / (((k : ℝ) + 3) * ((k : ℝ) + 3)) := by field_simp
    _ < 1 / 2 := by
        have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
        nlinarith

end OMA.A002467Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a002467.main := by
  intro n hn
  have hcast : ∀ m : ℕ, ((OMA.S_oeis_a002467.a m : ℤ) : ℝ)
      = (m.factorial : ℝ) - (numDerangements m : ℝ) := by
    intro m
    unfold OMA.S_oeis_a002467.a
    push_cast [Nat.cast_sub (OMA.A002467Proof.der_le m)]
    rfl
  have he : (1 : ℝ) / Real.exp 1 = Real.exp (-1) := by rw [Real.exp_neg, one_div]
  rw [he, round_eq, eq_comm, Int.floor_eq_iff, hcast]
  rcases n with _ | _ | k
  · omega
  · have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have hpos : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
    have hle : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
    norm_num [numDerangements]
    constructor <;> linarith
  · have h := abs_lt.mp (OMA.A002467Proof.key k)
    constructor <;> linarith [h.1, h.2]
