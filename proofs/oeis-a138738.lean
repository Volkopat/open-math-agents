import OMAStatements.S_oeis_a138738
import Mathlib

open OMA.S_oeis_a138738

namespace P138738

lemma E_zero (m : ℕ) : E m 0 = 1 := by rw [E]

lemma Q (k m : ℕ) (h : m ≤ k) : (k + 1).factorial / (k - m).factorial = (k + 1).descFactorial (m + 1) := by
  have := Nat.factorial_mul_descFactorial (show m + 1 ≤ k + 1 by omega)
  rw [show k + 1 - (m + 1) = k - m by omega] at this
  rw [← this, Nat.mul_div_cancel_left _ (Nat.factorial_pos _)]

lemma A (m n : ℕ) (hm : 2 ≤ m) : 6 ∣ E m (n + 1) := by
  rw [E]
  apply Finset.dvd_sum
  intro k _
  split_ifs with h
  · apply dvd_mul_of_dvd_left
    apply dvd_mul_of_dvd_left
    apply dvd_mul_of_dvd_right
    rw [Q _ _ h]
    exact (show 6 ∣ (3 : ℕ).factorial by decide).trans
      ((Nat.factorial_dvd_factorial (show 3 ≤ m + 1 by omega)).trans (Nat.factorial_dvd_descFactorial _ _))
  · exact dvd_zero _

lemma A' (m n : ℕ) (hm : 2 ≤ m) : ((E m (n + 1) : ℕ) : ZMod 6) = 0 :=
  (ZMod.natCast_eq_zero_iff _ 6).mpr (A m n hm)

lemma E11 : E 1 1 = 0 := by rw [E]; simp

lemma B (n : ℕ) : ((E 1 (n + 2) : ℕ) : ZMod 6) = 2 * (n + 1) * (E 1 n : ZMod 6) := by
  rw [E, Fin.sum_univ_succ, Fin.sum_univ_succ]
  have hr : ∑ i : Fin n, (if 1 ≤ ((i.succ.succ : Fin (n + 2)) : ℕ) then
      (n + 1).choose ((i.succ.succ : Fin (n + 2)) : ℕ) *
        ((((i.succ.succ : Fin (n + 2)) : ℕ) + 1).factorial / (((i.succ.succ : Fin (n + 2)) : ℕ) - 1).factorial) *
        E (1 + 1) (((i.succ.succ : Fin (n + 2)) : ℕ) - 1) * E 1 (n + 1 - ((i.succ.succ : Fin (n + 2)) : ℕ))
      else 0) = 6 * ∑ i : Fin n, (if 1 ≤ ((i.succ.succ : Fin (n + 2)) : ℕ) then
      (n + 1).choose ((i.succ.succ : Fin (n + 2)) : ℕ) *
        ((((i.succ.succ : Fin (n + 2)) : ℕ) + 1).factorial / (((i.succ.succ : Fin (n + 2)) : ℕ) - 1).factorial) *
        (E (1 + 1) (((i.succ.succ : Fin (n + 2)) : ℕ) - 1) / 6) * E 1 (n + 1 - ((i.succ.succ : Fin (n + 2)) : ℕ))
      else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs
    · obtain ⟨c, hc⟩ := A (1 + 1) i (le_refl _)
      simp only [Fin.val_succ, show (i : ℕ) + 1 + 1 - 1 = i + 1 by omega]
      rw [hc, Nat.mul_div_cancel_left c (by norm_num)]; ring
    · simp
  rw [hr]
  push_cast
  simp only [Fin.val_zero, Fin.succ_zero_eq_one, Fin.val_one, nonpos_iff_eq_zero, one_ne_zero,
    if_false, le_refl, if_true, Nat.sub_self, E_zero, show n + 1 - 1 = n by omega, Nat.choose_one_right]
  have h6 : ((6 : ℕ) : ZMod 6) = 0 := by decide
  push_cast at h6
  rw [h6]
  norm_num [Nat.factorial]
  ring

lemma E12 : ((E 1 2 : ℕ) : ZMod 6) = 2 := by
  have h : ((E 1 2 : ℕ) : ZMod 6) = 2 * ((0 : ℕ) + 1) * (E 1 0 : ZMod 6) := B 0
  rw [h, E_zero]; simp

lemma F2 : ∀ k, ((E 1 (k + 3) : ℕ) : ZMod 6) = 0 ∧ ((E 1 (k + 4) : ℕ) : ZMod 6) = 0
  | 0 => by
    have h1 : ((E 1 3 : ℕ) : ZMod 6) = 2 * ((1 : ℕ) + 1) * (E 1 1 : ZMod 6) := B 1
    have h2 : ((E 1 4 : ℕ) : ZMod 6) = 2 * ((2 : ℕ) + 1) * (E 1 2 : ZMod 6) := B 2
    refine ⟨?_, ?_⟩
    · show ((E 1 3 : ℕ) : ZMod 6) = 0
      rw [h1, E11]; simp
    · show ((E 1 4 : ℕ) : ZMod 6) = 0
      rw [h2, E12]; decide
  | k + 1 => by
    have h : ((E 1 (k + 1 + 4) : ℕ) : ZMod 6) = 2 * ((k + 3 : ℕ) + 1) * (E 1 (k + 3) : ZMod 6) :=
      B (k + 3)
    exact ⟨(F2 k).2, by rw [h, (F2 k).1, mul_zero]⟩

lemma main0 (n : ℕ) : ((E 0 (n + 1) : ℕ) : ZMod 6) = E 0 n := by
  rw [E]
  push_cast
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp [E_zero]
  · intro b _ hb
    obtain ⟨v, hv⟩ := b
    have hv0 : v ≠ 0 := fun h => hb (Fin.ext h)
    simp only [zero_le, if_true, Nat.sub_zero, zero_add]
    rcases v with _ | _ | _ | k
    · exact absurd rfl hv0
    · rw [E11]; simp
    · simp only [zero_add, Nat.reduceAdd]
      rw [E12, show Nat.factorial 3 / Nat.factorial 2 = 3 by decide]
      calc ((n.choose 2 : ℕ) : ZMod 6) * ((3 : ℕ) : ZMod 6) * 2 * ((E 0 (n - 2) : ℕ) : ZMod 6)
          = (n.choose 2 : ℕ) * (E 0 (n - 2) : ℕ) * (6 : ZMod 6) := by push_cast; ring
        _ = 0 := by rw [show (6 : ZMod 6) = 0 by decide, mul_zero]
    · rw [(F2 k).1]; simp
  · simp

end P138738

theorem OMA.solution : type_of% @OMA.S_oeis_a138738.main := by
  intro n
  rw [a, ← ZMod.natCast_eq_natCast_iff]
  induction n with
  | zero => rw [P138738.E_zero]
  | succ n ih => rw [P138738.main0, ih]
