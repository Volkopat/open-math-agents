import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R1
import Mathlib

namespace E142W

open Finset

theorem count_shift {p : ℕ} [NeZero p] (A : Finset (ZMod p)) (c : ZMod p) :
    (∑ x : ZMod p, if x + c ∈ A then 1 else 0) = A.card := by
  rw [Fintype.sum_equiv (Equiv.addRight c) (fun x => if x + c ∈ A then 1 else 0)
    (fun x => if x ∈ A then 1 else 0) (fun x => rfl)]
  rw [Finset.sum_boole]
  simp

theorem sum_count {p : ℕ} [NeZero p] (A : Finset (ZMod p)) (M : ℕ) :
    ∑ u ∈ (univ : Finset (ZMod p)) ×ˢ (univ.erase (0 : ZMod p)),
      ((Icc 1 M).filter fun j : ℕ => u.1 + (j : ZMod p) * u.2 ∈ A).card
    = M * ((p - 1) * A.card) := by
  simp only [Finset.card_filter]
  rw [Finset.sum_product, Finset.sum_comm]
  have h1 : ∀ y : ZMod p, (∑ x : ZMod p, ∑ j ∈ Icc 1 M,
      (if x + (j : ZMod p) * y ∈ A then 1 else 0)) = M * A.card := by
    intro y
    rw [Finset.sum_comm]
    simp only [count_shift, Finset.sum_const, Nat.card_Icc, smul_eq_mul]
    simp
  rw [Finset.sum_congr rfl (fun y _ => h1 y)]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    ZMod.card, smul_eq_mul]
  ring

end E142W

open Finset
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R1.H2 := by
  intro k M p hp _inst hk hM hMp α A hα hA hAP
  have : Fact p.Prime := ⟨hp⟩
  set T := (Finset.univ.filter fun u : ZMod p × ZMod p =>
          u.2 ≠ 0 ∧ ∀ i : Fin k, u.1 + (i.val : ZMod p) * u.2 ∈ A) with hTdef
  set Q := (univ : Finset (ZMod p)) ×ˢ (univ.erase (0 : ZMod p)) with hQdef
  set Sf : ZMod p × ZMod p → Finset ℕ :=
    fun u => (Icc 1 M).filter fun j : ℕ => u.1 + (j : ZMod p) * u.2 ∈ A with hSf
  set G := Q.filter fun u => (α / 2) * (M : ℝ) < ((Sf u).card : ℝ) with hGdef
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  -- covering
  have hcover : G ⊆ (T ×ˢ (Icc 1 M ×ˢ Icc 1 M)).image (fun w : (ZMod p × ZMod p) × ℕ × ℕ =>
      (w.1.1 - (w.2.1 : ZMod p) * (w.1.2 * (w.2.2 : ZMod p)⁻¹),
        w.1.2 * (w.2.2 : ZMod p)⁻¹)) := by
    intro u hu
    obtain ⟨x, y⟩ := u
    rw [hGdef, Finset.mem_filter, hQdef, Finset.mem_product] at hu
    obtain ⟨⟨_, hy⟩, hgood⟩ := hu
    have hy0 : y ≠ 0 := Finset.ne_of_mem_erase hy
    obtain ⟨a, d, hd, hS⟩ := hAP (Sf (x, y)) (Finset.filter_subset _ _) hgood
    have hmem : ∀ i < k, a + i * d ∈ Icc 1 M ∧
        x + ((a + i * d : ℕ) : ZMod p) * y ∈ A := by
      intro i hi
      have := hS i hi
      rw [hSf, Finset.mem_filter] at this
      exact this
    have h0 := (hmem 0 (by omega)).1
    have h1 := (hmem 1 (by omega)).1
    simp only [Finset.mem_Icc] at h0 h1
    have hdp : (d : ZMod p) ≠ 0 := by
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      have := Nat.le_of_dvd hd h
      omega
    rw [Finset.mem_image]
    refine ⟨((x + (a : ZMod p) * y, (d : ZMod p) * y), a, d), ?_, ?_⟩
    · rw [Finset.mem_product, hTdef, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, mul_ne_zero hdp hy0, ?_⟩, ?_⟩
      · intro i
        have := (hmem i.val i.isLt).2
        convert this using 1
        push_cast
        ring
      · simp only [Finset.mem_product, Finset.mem_Icc]
        omega
    · have : (d : ZMod p) * y * (d : ZMod p)⁻¹ = y := by
        field_simp
      simp only [this]
      simp
  have hGT : (G.card : ℝ) ≤ (M : ℝ) ^ 2 * (T.card : ℝ) := by
    have := (Finset.card_le_card hcover).trans (Finset.card_image_le)
    rw [Finset.card_product, Finset.card_product, Nat.card_Icc] at this
    have h' : (G.card : ℝ) ≤ ((T.card * ((M + 1 - 1) * (M + 1 - 1)) : ℕ) : ℝ) := by
      exact_mod_cast this
    simp only [Nat.add_sub_cancel] at h'
    push_cast at h'
    nlinarith
  -- double counting
  have hsum : (∑ u ∈ Q, ((Sf u).card : ℝ)) = (M : ℝ) * (((p : ℝ) - 1) * (A.card : ℝ)) := by
    have := E142W.sum_count A M
    have h' : ((∑ u ∈ Q, (Sf u).card : ℕ) : ℝ) = ((M * ((p - 1) * A.card) : ℕ) : ℝ) := by
      rw [this]
    push_cast [Nat.cast_sub hp1] at h'
    exact h'
  have hbound : ∀ u ∈ Q, ((Sf u).card : ℝ) ≤
      (α / 2) * (M : ℝ) + (if (α / 2) * (M : ℝ) < ((Sf u).card : ℝ) then (M : ℝ) else 0) := by
    intro u _
    split_ifs with h
    · have : (Sf u).card ≤ M := by
        have := Finset.card_le_card (Finset.filter_subset
          (fun j : ℕ => u.1 + (j : ZMod p) * u.2 ∈ A) (Icc 1 M))
        simpa using this
      have : ((Sf u).card : ℝ) ≤ M := by exact_mod_cast this
      nlinarith
    · linarith [not_lt.mp h]
  have hle := Finset.sum_le_sum hbound
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
    nsmul_eq_mul, nsmul_eq_mul, hsum] at hle
  have hQc : (Q.card : ℝ) = (p : ℝ) * ((p : ℝ) - 1) := by
    rw [hQdef, Finset.card_product, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card]
    push_cast [Nat.cast_sub hp1]
    ring
  rw [hQc, ← hGdef] at hle
  have hp1r : (0 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp1
    linarith
  have hkey : (α / 2) * (p : ℝ) * ((p : ℝ) - 1) * M ≤ (G.card : ℝ) * M := by
    have : (M : ℝ) * (((p : ℝ) - 1) * (α * p)) ≤ (M : ℝ) * (((p : ℝ) - 1) * (A.card : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hMpos.le
      exact mul_le_mul_of_nonneg_left hA hp1r
    nlinarith
  have := le_of_mul_le_mul_right hkey hMpos
  linarith
