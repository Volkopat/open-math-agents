import OMAStatements.S_oeis_a352446
import Mathlib

open OMA.S_oeis_a352446

lemma cs_formula (m L : ℕ) : consecSum m L * 2 + L = L * (2 * m + L) := by
  induction L with
  | zero => simp [consecSum]
  | succ L ih =>
    unfold consecSum at *
    rw [Finset.sum_range_succ]
    nlinarith [ih]

theorem OMA.solution : type_of% @OMA.S_oeis_a352446.main := by
  intro n hn
  have hL : a n = ∑ p ∈ ((Finset.Icc 1 n) ×ˢ (Finset.Icc 1 n)).filter
      (fun p : ℕ × ℕ => Even p.2 ∧ consecSum p.1 p.2 = n), p.2 := by
    rw [a, Finset.sum_filter, Finset.sum_product]
    simp only [Finset.sum_filter]
  have hR : (∑ k ∈ Finset.Icc 1 n, ∑ j ∈ Finset.range (n + 1),
      if k * (2 * k + 1) + 2 * k * j = n then 2 * k else 0) =
      ∑ p ∈ ((Finset.Icc 1 n) ×ˢ (Finset.range (n + 1))).filter
      (fun p : ℕ × ℕ => p.1 * (2 * p.1 + 1) + 2 * p.1 * p.2 = n), 2 * p.1 := by
    rw [Finset.sum_filter, Finset.sum_product]
  rw [hL, hR]
  apply Finset.sum_nbij' (fun p => (p.2 / 2, p.1 - 1)) (fun q => (q.2 + 1, 2 * q.1))
  · rintro ⟨m, L⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hp
    obtain ⟨⟨⟨hm1, hmn⟩, hL1, hLn⟩, ⟨k, rfl⟩, hcs⟩ := hp
    have hf := cs_formula m (k + k)
    rw [hcs] at hf
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
    refine ⟨⟨⟨by omega, by omega⟩, by omega⟩, ?_⟩
    have hk : (k + k) / 2 = k := by omega
    rw [hk, show m' + 1 - 1 = m' by omega]
    nlinarith [hf]
  · rintro ⟨k, j⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hp
    obtain ⟨⟨⟨hk1, hkn⟩, hjn⟩, he⟩ := hp
    have hf := cs_formula (j + 1) (2 * k)
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
    have hcs : consecSum (j + 1) (2 * k) = n := by nlinarith [hf, he]
    refine ⟨⟨⟨by omega, ?_⟩, by omega, ?_⟩, ⟨k, by ring⟩, hcs⟩
    · nlinarith [he]
    · nlinarith [he]
  · rintro ⟨m, L⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hp
    obtain ⟨⟨⟨hm1, hmn⟩, hL1, hLn⟩, ⟨k, rfl⟩, hcs⟩ := hp
    simp only [Prod.mk.injEq]
    omega
  · rintro ⟨k, j⟩ hp
    simp only [Prod.mk.injEq]
    omega
  · rintro ⟨m, L⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hp
    obtain ⟨⟨⟨hm1, hmn⟩, hL1, hLn⟩, ⟨k, rfl⟩, hcs⟩ := hp
    simp only
    omega

