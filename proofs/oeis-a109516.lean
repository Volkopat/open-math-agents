import OMAStatements.S_oeis_a109516
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Ring

/-! Schulte's formula for OEIS A109516.

Write `M = matA109516 (n + 1) = [[0, 1], [n, n]]` and `u m = (M ^ m) 0 1`. Since
`M ^ (m + 1) = M * M ^ m`, `u (m + 2) = n * u (m + 1) + n * u m`, with `u 1 = 1`, `u 2 = n`.
The antidiagonal sums `G m = ∑_{i + k = m} C(i, k) n ^ i` satisfy the same recurrence by Pascal's
rule, with `G 0 = 1` and `G 1 = n`, so `u (m + 1) = G m`. Read along `k`, `G n` is
`∑_{k ≤ n} C(n - k, k) n ^ (n - k)`, and the terms with `k > n / 2` vanish. -/

namespace OpenMath.A109516

open Finset OMA.S_oeis_a109516

/-- `G c m = ∑_{i + k = m} C(i, k) c ^ i`. -/
private def G (c m : ℕ) : ℕ := ∑ p ∈ antidiagonal m, p.1.choose p.2 * c ^ p.1

private theorem G_zero (c : ℕ) : G c 0 = 1 := by
  simp [G]

private theorem G_one (c : ℕ) : G c 1 = c := by
  show ∑ p ∈ antidiagonal (0 + 1), p.1.choose p.2 * c ^ p.1 = c
  rw [Finset.Nat.sum_antidiagonal_succ]
  simp

private theorem G_rec (c m : ℕ) : G c (m + 1 + 1) = c * G c (m + 1) + c * G c m := by
  have hL : G c (m + 1 + 1) = c ^ (m + 1 + 1) +
      ∑ p ∈ antidiagonal m, (p.1.choose p.2 * c ^ (p.1 + 1) +
        p.1.choose (p.2 + 1) * c ^ (p.1 + 1)) := by
    unfold G
    rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ']
    simp only [Nat.choose_zero_succ, zero_mul, zero_add, Nat.choose_zero_right, one_mul,
      Nat.choose_succ_succ', add_mul]
  have hA : c * G c (m + 1) = c ^ (m + 1 + 1) +
      ∑ p ∈ antidiagonal m, p.1.choose (p.2 + 1) * c ^ (p.1 + 1) := by
    unfold G
    rw [Finset.Nat.sum_antidiagonal_succ', mul_add, Finset.mul_sum]
    dsimp only
    rw [Nat.choose_zero_right, one_mul, ← pow_succ']
    congr 1
    exact Finset.sum_congr rfl fun p _ => by ring
  have hB : c * G c m = ∑ p ∈ antidiagonal m, p.1.choose p.2 * c ^ (p.1 + 1) := by
    unfold G
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hL, hA, hB, Finset.sum_add_distrib]
  ring

/-- The entries `(0, 1)` and `(1, 1)` of `M ^ (m + 1) = M * M ^ m`. -/
private theorem pow_entries (n m : ℕ) :
    (matA109516 (n + 1) ^ (m + 1)) 0 1 = (matA109516 (n + 1) ^ m) 1 1 ∧
    (matA109516 (n + 1) ^ (m + 1)) 1 1 =
      n * (matA109516 (n + 1) ^ m) 0 1 + n * (matA109516 (n + 1) ^ m) 1 1 := by
  rw [pow_succ']
  simp [Matrix.mul_apply, Fin.sum_univ_two, matA109516]

private theorem u_eq (n m : ℕ) :
    (matA109516 (n + 1) ^ (m + 1)) 0 1 = G n m ∧
    (matA109516 (n + 1) ^ (m + 1 + 1)) 0 1 = G n (m + 1) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [(pow_entries n 0).1, pow_zero, G_zero]
      simp
    · rw [(pow_entries n (0 + 1)).1, (pow_entries n 0).2, pow_zero,
        show (0 : ℕ) + 1 = 1 from rfl, G_one]
      simp
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    rw [(pow_entries n (m + 1 + 1)).1, (pow_entries n (m + 1)).2,
      ← (pow_entries n (m + 1)).1, ih.1, ih.2, G_rec]
    ring

private theorem G_eq_range (c n : ℕ) :
    G c n = ∑ k ∈ range (n + 1), (n - k).choose k * c ^ (n - k) := by
  unfold G
  rw [← Finset.Nat.sum_antidiagonal_swap, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rfl

theorem main :
    ∀ n : ℕ, a109516 (n + 1) =
      ∑ k ∈ Finset.range (n / 2 + 1), Nat.choose (n - k) k * n ^ (n - k) := by
  intro n
  rw [show a109516 (n + 1) = (matA109516 (n + 1) ^ (n + 1)) 0 1 from rfl, (u_eq n n).1,
    G_eq_range]
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk hk'
    simp only [Finset.mem_range] at hk hk'
    rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]

end OpenMath.A109516

theorem OMA.solution : type_of% @OMA.S_oeis_a109516.main := OpenMath.A109516.main
