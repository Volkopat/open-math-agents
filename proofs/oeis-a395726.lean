import OMAStatements.S_oeis_a395726
import Mathlib

namespace OMA.A395726Proof

open OMA.S_oeis_a395726

/-- Triangular numbers. -/
def tri : ℕ → ℕ
  | 0 => 0
  | g + 1 => tri g + (g + 1)

theorem two_tri (g : ℕ) : 2 * tri g = g * g + g := by
  induction g with
  | zero => rfl
  | succ g ih =>
    simp only [tri]
    nlinarith

theorem f_tri (g r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ g + 1) : f (tri g + r) = g + 1 := by
  have ht := two_tri g
  have hlo : 2 * g + 1 ≤ Nat.sqrt (8 * (tri g + r) - 7) := by
    apply Nat.le_sqrt.mpr
    have : (2 * g + 1) * (2 * g + 1) = 4 * (g * g) + 4 * g + 1 := by ring
    omega
  have hhi : Nat.sqrt (8 * (tri g + r) - 7) < 2 * g + 3 := by
    apply Nat.sqrt_lt.mpr
    have : (2 * g + 3) * (2 * g + 3) = 4 * (g * g) + 12 * g + 9 := by ring
    omega
  unfold f
  omega

theorem A_zero (k : ℕ) : A 0 k = 1 := by
  rw [A]

theorem A_succ_zero (n : ℕ) : A (n + 1) 0 = 0 := by
  rw [A]

theorem A_succ_succ (n k : ℕ) :
    A (n + 1) (k + 1) = A (n + 1) (k + 1 - f (k + 1)) + f (k + 1) * A n (k + 1) := by
  rw [A]

theorem key : ∀ n g r : ℕ, r ≤ g + 1 →
    A n (tri g + r) = Nat.stirlingSecond (n + g) g + r * Nat.stirlingSecond (n + g) (g + 1) := by
  intro n
  induction n with
  | zero =>
    intro g r _
    rw [A_zero, Nat.zero_add, Nat.stirlingSecond_self,
      Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self g), Nat.mul_zero]
  | succ n ihn =>
    intro g
    induction g with
    | zero =>
      intro r hr
      have hr' : r = 0 ∨ r = 1 := by omega
      rcases hr' with rfl | rfl
      · simp [tri, A_succ_zero]
      · have hf : f 1 = 1 := f_tri 0 1 le_rfl le_rfl
        have h1 := ihn 0 1 le_rfl
        simp only [tri, Nat.zero_add, Nat.add_zero] at h1 ⊢
        rw [A_succ_succ n 0]
        simp only [Nat.zero_add, hf, Nat.sub_self, A_succ_zero, h1,
          Nat.stirlingSecond_succ_succ, Nat.stirlingSecond_succ_zero]
        ring
    | succ g ihg =>
      intro r hr
      rcases r with _ | r
      · have h := ihg (g + 1) le_rfl
        have e : tri (g + 1) + 0 = tri g + (g + 1) := rfl
        rw [e, h]
        have e2 : n + 1 + (g + 1) = (n + 1 + g) + 1 := by ring
        rw [e2, Nat.stirlingSecond_succ_succ]
        ring
      · have hf : f (tri (g + 1) + (r + 1)) = g + 2 := f_tri (g + 1) (r + 1) (by omega) hr
        have e : tri (g + 1) + (r + 1) = (tri (g + 1) + r) + 1 := rfl
        have hsub : tri (g + 1) + r + 1 - (g + 2) = tri g + r := by
          simp only [tri]
          omega
        have h1 := ihg r (by omega)
        have h2 := ihn (g + 1) (r + 1) hr
        rw [e] at hf h2 ⊢
        rw [A_succ_succ, hf, hsub, h1, h2]
        have e2 : n + 1 + (g + 1) = (n + 1 + g) + 1 := by ring
        have e3 : n + (g + 1) = n + 1 + g := by ring
        rw [e2, e3, Nat.stirlingSecond_succ_succ (n + 1 + g) g,
          Nat.stirlingSecond_succ_succ (n + 1 + g) (g + 1)]
        ring

theorem decomp : ∀ k : ℕ, 1 ≤ k → ∃ g r : ℕ, 1 ≤ r ∧ r ≤ g + 1 ∧ k = tri g + r := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact ⟨0, 1, le_rfl, le_rfl, rfl⟩
    · obtain ⟨g, r, h1, h2, rfl⟩ := ih hk0
      rcases Nat.lt_or_ge r (g + 1) with h | h
      · exact ⟨g, r + 1, by omega, by omega, rfl⟩
      · refine ⟨g + 1, 1, le_rfl, by omega, ?_⟩
        simp only [tri]
        omega

theorem main' : ∀ n k : ℕ, 0 < n →
    A n k = ∑ j ∈ Finset.Icc 1 k, Nat.stirlingSecond (n + f j - 1) (f j) := by
  intro n k hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  induction k with
  | zero => simp [A_succ_zero]
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← ih]
    obtain ⟨g, r, h1, h2, hk⟩ := decomp (k + 1) (by omega)
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    have hk' : k = tri g + s := by omega
    have hf : f (k + 1) = g + 1 := by rw [hk]; exact f_tri g (s + 1) h1 h2
    rw [hf, hk, key (m + 1) g (s + 1) h2, hk', key (m + 1) g s (by omega)]
    have e : m + 1 + (g + 1) - 1 = m + 1 + g := by omega
    rw [e]
    ring

end OMA.A395726Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a395726.main :=
  OMA.A395726Proof.main'
