import OMAStatements.S_oeis_a001712
import Mathlib

-- Proof of R. J. Mathar's conjecture in OEIS A001712 (statement by @ivillar).
-- Idea: by Crstici's formula, 3^2 * a(n) = Sum_j binomial(j,2)*3^j*c(n+2,j) with c the unsigned
-- Stirling numbers of the first kind. For B_V(m) = Sum_j V(j)*c(m+1,j), the triangle recurrence
-- c(m+2,j+1) = (m+1)*c(m+1,j+1) + c(m+1,j) gives B_V(m+1) - (m+1+r)*B_V(m) = B_(V(j+1) - r*V(j))(m).
-- The weight binomial(j,2)*3^j is killed by 3 applications of V(j) -> V(j+1) - 3*V(j), so the
-- operator F(m) -> F(m+1) - (m+1+3)*F(m), applied 3 times, kills B_W; expanded, that is the recurrence.

namespace OMAA001712Helpers

open OMA.S_oeis_a001712

/-- B V m = Σ_{j ≤ m+1} V j * c(m+1, j). -/
def B (V : ℕ → ℤ) (m : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (m + 2), V j * (Nat.stirlingFirst (m + 1) j : ℤ)

/-- The difference operator V ↦ V(j+1) - r V(j) on weights. -/
def Δ (r : ℤ) (V : ℕ → ℤ) : ℕ → ℤ := fun j => V (j + 1) - r * V j

/-- The operator F ↦ F(m+1) - (m+1+r) F(m) on sequences. -/
def L (r : ℤ) (F : ℕ → ℤ) : ℕ → ℤ := fun m => F (m + 1) - ((m : ℤ) + 1 + r) * F m

theorem B_step (V : ℕ → ℤ) (m : ℕ) :
    B V (m + 1) = ((m : ℤ) + 1) * B V m + B (fun j => V (j + 1)) m := by
  have hlast : (Nat.stirlingFirst (m + 1) (m + 2) : ℤ) = 0 := by
    rw [Nat.stirlingFirst_eq_zero_of_lt (by omega)]; simp
  have e1 : ∑ j ∈ Finset.range (m + 2), V j * (Nat.stirlingFirst (m + 1) j : ℤ) =
      ∑ j ∈ Finset.range (m + 2), V (j + 1) * (Nat.stirlingFirst (m + 1) (j + 1) : ℤ) := by
    rw [Finset.sum_range_succ' (fun j => V j * (Nat.stirlingFirst (m + 1) j : ℤ)) (m + 1),
      Finset.sum_range_succ (fun j => V (j + 1) * (Nat.stirlingFirst (m + 1) (j + 1) : ℤ)) (m + 1),
      hlast, Nat.stirlingFirst_succ_zero]
    simp
  unfold B
  rw [Finset.sum_range_succ' (fun j => V j * (Nat.stirlingFirst (m + 1 + 1) j : ℤ)) (m + 2),
    Nat.stirlingFirst_succ_zero, e1, Finset.mul_sum, ← Finset.sum_add_distrib]
  simp only [Nat.stirlingFirst_succ_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_zero, mul_zero,
    add_zero, Nat.cast_one]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

theorem B_lin (r : ℤ) (V : ℕ → ℤ) (m : ℕ) : B (Δ r V) m = L r (B V) m := by
  have h : B (Δ r V) m = B (fun j => V (j + 1)) m - r * B V m := by
    unfold B Δ
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [L]
  rw [h, B_step]
  ring

theorem B_iter (r : ℤ) (d : ℕ) : ∀ V : ℕ → ℤ, B ((Δ r)^[d] V) = (L r)^[d] (B V) := by
  induction d with
  | zero => intro V; rfl
  | succ d ih =>
    intro V
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    congr 1
    funext m
    exact B_lin r V m

theorem B_zero (m : ℕ) : B (fun _ => 0) m = 0 := by simp [B]

/-- The weight binomial(j, 2) * 3^j. -/
def W (j : ℕ) : ℤ := (Nat.choose j 2 : ℤ) * 3 ^ j

theorem W_kill : (Δ 3)^[3] W = fun _ => 0 := by
  have c2 : ∀ n : ℕ, (n + 1).choose 2 = n + n.choose 2 := fun n => by
    have h := Nat.choose_succ_succ' n 1
    rw [Nat.choose_one_right] at h
    exact h
  funext j
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, Δ, W, c2]
  push_cast
  ring

theorem ha (i : ℕ) : (9 : ℤ) * a i = B W (i + 1) := by
  unfold B a W
  conv_rhs => rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [zero_add, Nat.reduceAdd, show Nat.choose 0 2 = 0 by decide, show Nat.choose 1 2 = 0 by decide, Nat.cast_zero, zero_mul, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hs : (-1 : ℤ) ^ (i + k) * (-1) ^ (i + 2 + (k + 2)) = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨i + k + 2, by ring⟩
  unfold s
  simp only [add_assoc, Nat.reduceAdd]
  linear_combination (9 * (Nat.choose (k + 2) 2 : ℤ) * 3 ^ k * (Nat.stirlingFirst (i + 2) (k + 2) : ℤ)) * hs

end OMAA001712Helpers

open OMA.S_oeis_a001712 OMAA001712Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a001712.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega, show k + 3 - 3 = k by omega]
  have hz : (L 3)^[3] (B W) (k + 1) = 0 := by rw [← B_iter, W_kill, B_zero]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, L, add_assoc,
    Nat.reduceAdd] at hz
  have e0 : (9 : ℤ) * a (k + 3) = B W (k + 4) := ha _
  have e1 : (9 : ℤ) * a (k + 2) = B W (k + 3) := ha _
  have e2 : (9 : ℤ) * a (k + 1) = B W (k + 2) := ha _
  have e3 : (9 : ℤ) * a (k) = B W (k + 1) := ha _
  apply mul_left_cancel₀ (show (9 : ℤ) ≠ 0 by norm_num)
  linear_combination (norm := (push_cast; ring)) e0 + 3 * (-((k + 3 : ℕ) : ℤ) - 3) * e1 + (3 * ((k + 3 : ℕ) : ℤ) ^ 2 + 15 * ((k + 3 : ℕ) : ℤ) + 19) * e2 + (-(((k + 3 : ℕ) : ℤ) + 2) ^ 3) * e3 + hz
