import OMAStatements.S_mo_397958
import Mathlib

-- Problem: mo-397958, is every finite symmetric arithmetic set a union of arithmetic
-- progressions containing both -1 and 1?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. A = {-1, -1/2, -1/4, 0, 1/4, 1/2, 1} is an arithmetic set: -1/2 = (-1 + 0)/2,
-- -1/4 = (-1/2 + 0)/2, 0 = (-1 + 1)/2, 1/4 = (0 + 1/2)/2, 1/2 = (0 + 1)/2. A progression
-- -1 + 2 i / n containing 1/4 has 8 i = 5 n; its second point -1 + 2/n lies in A only for
-- n = 1, 2, 4, and none of these satisfies 8 i = 5 n.

namespace MO397958

open OMA.S_mo_397958

noncomputable def A : Finset ℝ := {-1, -1 / 2, -1 / 4, 0, 1 / 4, 1 / 2, 1}

theorem mem_A (x : ℝ) : x ∈ A ↔
    x = -1 ∨ x = -1 / 2 ∨ x = -1 / 4 ∨ x = 0 ∨ x = 1 / 4 ∨ x = 1 / 2 ∨ x = 1 := by
  unfold A
  simp only [Finset.mem_insert, Finset.mem_singleton]

theorem neg_mem (a : ℝ) (ha : a ∈ A) : -a ∈ A := by
  rw [mem_A] at ha ⊢
  rcases ha with h | h | h | h | h | h | h
  · right; right; right; right; right; right
    rw [h]; norm_num
  · right; right; right; right; right; left
    rw [h]; norm_num
  · right; right; right; right; left
    rw [h]; norm_num
  · right; right; right; left
    rw [h]; norm_num
  · right; right; left
    rw [h]; norm_num
  · right; left
    rw [h]; norm_num
  · left
    rw [h]

theorem arith : ArithmeticSet A := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [mem_A] at ha
    rcases ha with h | h | h | h | h | h | h <;> rw [h] <;> norm_num
  · rw [mem_A]
    left
    rfl
  · rw [mem_A]
    right; right; right; right; right; right
    rfl
  · intro a
    constructor
    · exact neg_mem a
    · intro h
      have h2 := neg_mem (-a) h
      rw [neg_neg] at h2
      exact h2
  · intro a ha h1 h2
    rw [mem_A] at ha
    rcases ha with h | h | h | h | h | h | h
    · exact absurd h h1
    · refine ⟨-1, ?_, 0, ?_, ?_, ?_⟩
      · rw [mem_A]; left; rfl
      · rw [mem_A]; right; right; right; left; rfl
      · norm_num
      · rw [h]; norm_num
    · refine ⟨-1 / 2, ?_, 0, ?_, ?_, ?_⟩
      · rw [mem_A]; right; left; rfl
      · rw [mem_A]; right; right; right; left; rfl
      · norm_num
      · rw [h]; norm_num
    · refine ⟨-1, ?_, 1, ?_, ?_, ?_⟩
      · rw [mem_A]; left; rfl
      · rw [mem_A]; right; right; right; right; right; right; rfl
      · norm_num
      · rw [h]; norm_num
    · refine ⟨0, ?_, 1 / 2, ?_, ?_, ?_⟩
      · rw [mem_A]; right; right; right; left; rfl
      · rw [mem_A]; right; right; right; right; right; left; rfl
      · norm_num
      · rw [h]; norm_num
    · refine ⟨0, ?_, 1, ?_, ?_, ?_⟩
      · rw [mem_A]; right; right; right; left; rfl
      · rw [mem_A]; right; right; right; right; right; right; rfl
      · norm_num
      · rw [h]; norm_num
    · exact absurd h h2

theorem mem_AP (n : ℕ) (x : ℝ) :
    x ∈ endpointAP n ↔ ∃ i : ℕ, i < n + 1 ∧ -1 + 2 * (i : ℝ) / n = x := by
  unfold endpointAP
  simp only [Finset.mem_image, Finset.mem_range]

theorem no_cover (n i : ℕ) (hn : 0 < n) (h8 : 8 * i = 5 * n)
    (hx : -1 + 2 * ((1 : ℕ) : ℝ) / n ∈ A) : False := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have e : ∀ c : ℝ, -1 + 2 * ((1 : ℕ) : ℝ) / n = c → (c + 1) * n = 2 := by
    intro c hc
    rw [← hc]
    push_cast
    field_simp
    ring
  rw [mem_A] at hx
  rcases hx with h | h | h | h | h | h | h
  · have h3 := e _ h
    norm_num at h3
  · have h3 := e _ h
    have h4 : (n : ℝ) = 4 := by linarith
    have h5 : n = 4 := by exact_mod_cast h4
    omega
  · have h3 := e _ h
    have h4 : ((3 * n : ℕ) : ℝ) = (8 : ℕ) := by
      push_cast
      linarith
    have h5 : 3 * n = 8 := by exact_mod_cast h4
    omega
  · have h3 := e _ h
    have h4 : (n : ℝ) = 2 := by linarith
    have h5 : n = 2 := by exact_mod_cast h4
    omega
  · have h3 := e _ h
    have h4 : ((5 * n : ℕ) : ℝ) = (8 : ℕ) := by
      push_cast
      linarith
    have h5 : 5 * n = 8 := by exact_mod_cast h4
    omega
  · have h3 := e _ h
    have h4 : ((3 * n : ℕ) : ℝ) = (4 : ℕ) := by
      push_cast
      linarith
    have h5 : 3 * n = 4 := by exact_mod_cast h4
    omega
  · have h3 := e _ h
    have h4 : (n : ℝ) = 1 := by linarith
    have h5 : n = 1 := by exact_mod_cast h4
    omega

end MO397958

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_397958.main) := by
  intro h
  have hq : (1 / 4 : ℝ) ∈ MO397958.A := by
    rw [MO397958.mem_A]
    right; right; right; right; left
    rfl
  obtain ⟨n, hn, hmem, hsub⟩ := h MO397958.A MO397958.arith (1 / 4) hq
  rw [MO397958.mem_AP] at hmem
  obtain ⟨i, _, hie⟩ := hmem
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h8r : ((8 * i : ℕ) : ℝ) = ((5 * n : ℕ) : ℝ) := by
    push_cast
    have h2 : 2 * (i : ℝ) / n = 5 / 4 := by linarith
    rw [div_eq_iff hnpos.ne'] at h2
    linarith
  have h8 : 8 * i = 5 * n := by exact_mod_cast h8r
  have h1 : -1 + 2 * ((1 : ℕ) : ℝ) / n ∈ OMA.S_mo_397958.endpointAP n := by
    rw [MO397958.mem_AP]
    exact ⟨1, by omega, rfl⟩
  exact MO397958.no_cover n i hn h8 (hsub h1)
