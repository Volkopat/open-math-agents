import OMAStatements.S_oeis_a001724
import Mathlib

-- Proof of R. J. Mathar's conjecture in OEIS A001724 (statement by @ivillar).
-- Idea: by Crstici's formula, 5^4 * a(n) = Sum_j binomial(j,4)*5^j*c(n+4,j) with c the unsigned
-- Stirling numbers of the first kind. For B_V(m) = Sum_j V(j)*c(m+1,j), the triangle recurrence
-- c(m+2,j+1) = (m+1)*c(m+1,j+1) + c(m+1,j) gives B_V(m+1) - (m+1+r)*B_V(m) = B_(V(j+1) - r*V(j))(m).
-- The weight binomial(j,4)*5^j is killed by 5 applications of V(j) -> V(j+1) - 5*V(j), so the
-- operator F(m) -> F(m+1) - (m+1+5)*F(m), applied 5 times, kills B_W; expanded, that is the recurrence.

namespace OMAA001724Helpers

open OMA.S_oeis_a001724

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

/-- The weight binomial(j, 4) * 5^j. -/
def W (j : ℕ) : ℤ := (Nat.choose j 4 : ℤ) * 5 ^ j

theorem W_kill : (Δ 5)^[5] W = fun _ => 0 := by
  have c2 : ∀ n : ℕ, (n + 1).choose 2 = n + n.choose 2 := fun n => by
    have h := Nat.choose_succ_succ' n 1
    rw [Nat.choose_one_right] at h
    exact h
  have c3 : ∀ n : ℕ, (n + 1).choose 3 = n.choose 2 + n.choose 3 := fun n =>
    Nat.choose_succ_succ' n 2
  have c4 : ∀ n : ℕ, (n + 1).choose 4 = n.choose 3 + n.choose 4 := fun n =>
    Nat.choose_succ_succ' n 3
  funext j
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, Δ, W, c4, c3, c2]
  push_cast
  ring

theorem ha (i : ℕ) : (625 : ℤ) * a i = B W (i + 3) := by
  unfold B a W
  conv_rhs => rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [zero_add, Nat.reduceAdd, show Nat.choose 0 4 = 0 by decide, show Nat.choose 1 4 = 0 by decide, show Nat.choose 2 4 = 0 by decide, show Nat.choose 3 4 = 0 by decide, Nat.cast_zero, zero_mul, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hs : (-1 : ℤ) ^ (i + k) * (-1) ^ (i + 4 + (k + 4)) = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨i + k + 4, by ring⟩
  unfold s
  simp only [add_assoc, Nat.reduceAdd]
  linear_combination (625 * (Nat.choose (k + 4) 4 : ℤ) * 5 ^ k * (Nat.stirlingFirst (i + 4) (k + 4) : ℤ)) * hs

end OMAA001724Helpers

open OMA.S_oeis_a001724 OMAA001724Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a001724.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega, show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega, show k + 5 - 5 = k by omega]
  have hz : (L 5)^[5] (B W) (k + 3) = 0 := by rw [← B_iter, W_kill, B_zero]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, L, add_assoc,
    Nat.reduceAdd] at hz
  have e0 : (625 : ℤ) * a (k + 5) = B W (k + 8) := ha _
  have e1 : (625 : ℤ) * a (k + 4) = B W (k + 7) := ha _
  have e2 : (625 : ℤ) * a (k + 3) = B W (k + 6) := ha _
  have e3 : (625 : ℤ) * a (k + 2) = B W (k + 5) := ha _
  have e4 : (625 : ℤ) * a (k + 1) = B W (k + 4) := ha _
  have e5 : (625 : ℤ) * a (k) = B W (k + 3) := ha _
  apply mul_left_cancel₀ (show (625 : ℤ) ≠ 0 by norm_num)
  linear_combination (norm := (push_cast; ring)) e0 + 5 * (-((k + 5 : ℕ) : ℤ) - 6) * e1 + 5 * (2 * ((k + 5 : ℕ) : ℤ) ^ 2 + 22 * ((k + 5 : ℕ) : ℤ) + 61) * e2 + (-5 * (((k + 5 : ℕ) : ℤ) + 5) * (2 * ((k + 5 : ℕ) : ℤ) ^ 2 + 20 * ((k + 5 : ℕ) : ℤ) + 51)) * e3 + (5 * ((k + 5 : ℕ) : ℤ) ^ 4 + 90 * ((k + 5 : ℕ) : ℤ) ^ 3 + 610 * ((k + 5 : ℕ) : ℤ) ^ 2 + 1845 * ((k + 5 : ℕ) : ℤ) + 2101) * e4 + (-(((k + 5 : ℕ) : ℤ) + 4) ^ 5) * e5 + hz
