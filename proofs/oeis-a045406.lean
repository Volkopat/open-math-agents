import OMAStatements.S_oeis_a045406
import Mathlib

-- Proof of R. J. Mathar's conjecture in OEIS A045406 (statement by @ivillar).
-- Idea: for G_V(m) = Sum_j V(j)*s(m+1,j) the triangle recurrence s(m+2,j+1) = s(m+1,j) - (m+1)*s(m+1,j+1)
-- gives G_V(m+1) + m*G_V(m) = G_(V(j+1) - V(j))(m). Cloitre's formula is a(n) = G_V(n-2) with V(j) = j^2,
-- whose second difference is the constant 2, and the row sums Sum_j s(m,j) vanish for m ≥ 2. So the
-- operator F(m) -> F(m+1) + m*F(m), applied twice, kills G_V from m = 1 on; expanded, that is the
-- recurrence for n ≥ 5.

namespace OMAA045406Helpers

open OMA.S_oeis_a045406

/-- G V m = Σ_{j ≤ m+1} V j * s(m+1, j). -/
def G (V : ℕ → ℤ) (m : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (m + 2), V j * s (m + 1) j

/-- The difference operator V ↦ V(j+1) - V(j) on weights. -/
def Δ (V : ℕ → ℤ) : ℕ → ℤ := fun j => V (j + 1) - V j

/-- The operator F ↦ F(m+1) + m F(m) on sequences. -/
def L (F : ℕ → ℤ) : ℕ → ℤ := fun m => F (m + 1) + (m : ℤ) * F m

theorem s_succ_succ (n k : ℕ) : s (n + 1) (k + 1) = s n k - n * s n (k + 1) := by
  unfold s
  rw [Nat.stirlingFirst_succ_succ]
  push_cast
  ring

theorem s_succ_zero (n : ℕ) : s (n + 1) 0 = 0 := by
  simp [s, Nat.stirlingFirst_succ_zero]

theorem s_lt (n k : ℕ) (h : n < k) : s n k = 0 := by
  simp [s, Nat.stirlingFirst_eq_zero_of_lt h]

theorem G_step (V : ℕ → ℤ) (m : ℕ) :
    G V (m + 1) = G (fun j => V (j + 1)) m - ((m : ℤ) + 1) * G V m := by
  have e1 : ∑ j ∈ Finset.range (m + 2), V j * s (m + 1) j =
      ∑ j ∈ Finset.range (m + 2), V (j + 1) * s (m + 1) (j + 1) := by
    rw [Finset.sum_range_succ' (fun j => V j * s (m + 1) j) (m + 1),
      Finset.sum_range_succ (fun j => V (j + 1) * s (m + 1) (j + 1)) (m + 1),
      s_lt (m + 1) (m + 1 + 1) (by omega), s_succ_zero]
    simp
  unfold G
  rw [Finset.sum_range_succ' (fun j => V j * s (m + 1 + 1) j) (m + 2), s_succ_zero, e1,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [s_succ_succ, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

theorem G_lin (V : ℕ → ℤ) (m : ℕ) : G (Δ V) m = L (G V) m := by
  have h : G (Δ V) m = G (fun j => V (j + 1)) m - G V m := by
    unfold G Δ
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [L]
  rw [h, G_step]
  ring

theorem G_iter (d : ℕ) : ∀ V : ℕ → ℤ, G (Δ^[d] V) = L^[d] (G V) := by
  induction d with
  | zero => intro V; rfl
  | succ d ih =>
    intro V
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    congr 1
    funext m
    exact G_lin V m

/-- Row sums of the signed Stirling numbers vanish from row 2 on. -/
theorem G_one (m : ℕ) : G (fun _ => 1) (m + 1) = 0 := by
  induction m with
  | zero => rw [G_step]; ring
  | succ m ih => rw [G_step, ih]; ring

theorem V_kill : Δ^[2] (fun j : ℕ => (j : ℤ) ^ 2) = fun _ => 2 := by
  funext j
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, Δ]
  push_cast
  ring

theorem G_two (m : ℕ) : G (fun _ => 2) (m + 1) = 0 := by
  have h : G (fun _ => 2) (m + 1) = 2 * G (fun _ => 1) (m + 1) := by
    unfold G
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h, G_one, mul_zero]

theorem ha (k : ℕ) : a (k + 2) = G (fun j : ℕ => (j : ℤ) ^ 2) k := by
  unfold a G
  have hI : Finset.Icc 1 (k + 1) = Finset.Ico 1 (k + 2) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [show k + 2 - 1 = k + 1 by omega, hI, Finset.sum_Ico_eq_sum_range,
    Finset.sum_range_succ' (fun j => ((j : ℕ) : ℤ) ^ 2 * s (k + 1) j) (k + 1)]
  simp only [show k + 1 + 1 - 1 = k + 1 by omega, Nat.cast_zero, zero_pow two_ne_zero, zero_mul,
    add_zero]
  apply Finset.sum_congr rfl
  intro j _
  rw [add_comm 1 j]

end OMAA045406Helpers

open OMA.S_oeis_a045406 OMAA045406Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a045406.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  simp only [show k + 5 - 1 = k + 2 + 2 by omega, show k + 5 - 2 = k + 1 + 2 by omega,
    show k + 5 = k + 3 + 2 by omega, ha]
  have hz : L^[2] (G (fun j : ℕ => (j : ℤ) ^ 2)) (k + 1) = 0 := by
    rw [← G_iter, V_kill, G_two]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, L] at hz
  linear_combination (norm := (push_cast; ring_nf)) hz
