import OMAStatements.S_oeis_a163774
import Mathlib

-- Problem: A163774, row sums of the central coefficients triangle A163771.
-- Upstream: formal-conjectures statements/oeis-a163774.lean (declaration OMA.S_oeis_a163774.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: (2i)$ = C(2i, i); exchanging the two sums, the inner sum over k is
-- sum_{k <= i} C(n-k, n-i) = C(n+1, i) by the hockey-stick identity.

namespace OMA.P_oeis_a163774

open OMA.S_oeis_a163774

theorem swing_two_mul (i : ℕ) : swing (2 * i) = (2 * i).choose i := by
  unfold swing
  rw [Nat.choose_eq_factorial_div_factorial (by omega), show 2 * i / 2 = i by omega,
    show 2 * i - i = i by omega, sq]

theorem inner (n i : ℕ) (hi : i ≤ n) :
    ∑ k ∈ Finset.range (i + 1), ((n - k).choose (n - i) : ℤ) = ((n + 1).choose i : ℤ) := by
  have h1 : ∑ k ∈ Finset.range (i + 1), (n - k).choose (n - i) =
      ∑ m ∈ Finset.Icc (n - i) n, m.choose (n - i) := by
    apply Finset.sum_nbij' (fun k => n - k) (fun m => n - m)
    · intro k hk; simp at hk ⊢; omega
    · intro m hm; simp at hm ⊢; omega
    · intro k hk; simp at hk; omega
    · intro m hm; simp at hm; omega
    · intro k hk; rfl
  have h2 := Nat.sum_Icc_choose n (n - i)
  rw [← Nat.cast_sum, h1, h2, show n - i + 1 = n + 1 - i by omega, Nat.choose_symm (by omega)]

theorem main' : ∀ n : ℕ, a n = ∑ k ∈ Finset.range (n + 1),
      (-1) ^ (n - k) * ((n + 1).choose k : ℤ) * ((2 * k).choose k : ℤ) := by
  intro n
  unfold a T
  rw [Finset.sum_comm' (t' := Finset.range (n + 1)) (s' := fun i => Finset.range (i + 1))]
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ n := by simp at hi; omega
    rw [← inner n i hi', Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [swing_two_mul]
  · intro k i
    simp only [Finset.mem_range, Finset.mem_Icc]
    omega

end OMA.P_oeis_a163774

theorem OMA.solution : type_of% @OMA.S_oeis_a163774.main := OMA.P_oeis_a163774.main'
