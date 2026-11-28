import OMAStatements.S_oeis_a052379
import Mathlib

namespace OMA.P052379
open OMA.S_oeis_a052379 Finset

abbrev good (k : ℕ) : Prop := ∀ d ∈ Nat.digits 10 k, d ≠ 0 ∧ d ≠ 1

def H (m : ℕ) : Finset ℕ := (range (10 ^ m)).filter good

lemma H_succ (m : ℕ) : H (m + 1) = insert 0 ((H m ×ˢ Icc 2 9).image (fun p => p.2 + 10 * p.1)) := by
  ext k
  simp only [H, mem_insert, mem_filter, mem_range, mem_image, mem_product, mem_Icc, Prod.exists]
  constructor
  · rintro ⟨hk, hg⟩
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact Or.inl rfl
    rw [good, Nat.digits_def' (by norm_num) hpos] at hg
    simp at hg
    exact .inr ⟨k / 10, k % 10, ⟨⟨by rw [pow_succ] at hk; omega, hg.2⟩, by omega, by omega⟩, by omega⟩
  · rintro (rfl | ⟨q, r, ⟨⟨hq, hg⟩, h2, h9⟩, rfl⟩)
    · simp [good]
    · rw [good, Nat.digits_add 10 (by norm_num) r q (by omega) (.inl (by omega))]
      simp [pow_succ]
      exact ⟨by omega, ⟨by omega, by omega⟩, hg⟩

lemma H_card (m : ℕ) : 7 * (H m).card + 1 = 8 ^ (m + 1) := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [H_succ, card_insert_of_notMem (by simp), card_image_of_injOn, card_product]
    · simp; rw [pow_succ]; omega
    · rintro ⟨q1, r1⟩ h1 ⟨q2, r2⟩ h2 he
      simp at h1 h2 he
      ext <;> simp <;> omega

end OMA.P052379

open OMA.P052379 OMA.S_oeis_a052379 Finset in
theorem OMA.solution : type_of% @OMA.S_oeis_a052379.main := by
  intro n
  obtain h : 7 * _ + 1 = 8 ^ (n + 2) := H_card (n + 1)
  rw [a, A023001, show Icc 1 (10 ^ (n + 1) - 1) = (range (10 ^ (n + 1))).erase 0 by ext; simp; omega,
    filter_erase, card_erase_of_mem (by simp)]
  change (H (n + 1)).card - 1 = _
  omega
