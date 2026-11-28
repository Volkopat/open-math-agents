import OMAStatements.S_oeis_a105595

/-!
# A105595: the row sums of A105594 are odd

Source: https://oeis.org/A105595

`T n k = (∑ j ≤ n, |μ(C(n,j))| * (C(j,k) mod 2)) mod 2` and `a n = ∑ k ≤ n, T n k`.
Reducing the whole double sum modulo 2 gives
`a n ≡ ∑ j ≤ n, |μ(C(n,j))| * ∑ k ≤ n, C(j,k) ≡ ∑ j ≤ n, |μ(C(n,j))| * 2^j (mod 2)`,
and every term with `j ≥ 1` is even, while the `j = 0` term is `|μ 1| = 1`. Hence `a n` is odd.
(The same argument is recorded in the OEIS entry: Bing Gao, Sep 22 2026.)
-/

open OMA.S_oeis_a105595

theorem OMA.solution : type_of% @OMA.S_oeis_a105595.main := by
  intro n
  have hcast : ∀ x : ℤ, ((x % 2 : ℤ) : ZMod 2) = (x : ZMod 2) := by
    intro x
    rw [ZMod.intCast_eq_intCast_iff']
    exact Int.emod_eq_of_lt (Int.emod_nonneg x (by norm_num)) (Int.emod_lt_of_pos x (by norm_num))
  have hsum : ∀ j : ℕ, j ≤ n →
      ∑ k ∈ Finset.range (n + 1), ((j.choose k : ℤ) : ZMod 2) = (2 : ZMod 2) ^ j := by
    intro j hj
    have h1 : ∑ k ∈ Finset.range (n + 1), ((j.choose k : ℤ) : ZMod 2)
        = ((∑ k ∈ Finset.range (n + 1), j.choose k : ℕ) : ZMod 2) := by
      rw [Nat.cast_sum]
      simp
    rw [h1]
    have h2 : ∑ k ∈ Finset.range (n + 1), j.choose k = 2 ^ j := by
      rw [← Nat.sum_range_choose j]
      exact (Finset.sum_subset (s₁ := Finset.range (j + 1)) (s₂ := Finset.range (n + 1))
        (by
          intro x hx
          exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega))
        (by
          intro x hx hx2
          exact Nat.choose_eq_zero_of_lt (by
            have h2 : ¬ x < j + 1 := fun h => hx2 (Finset.mem_range.mpr h)
            omega))).symm
    rw [h2]
    simp
  have hmain : ((a n : ℤ) : ZMod 2) = 1 := by
    rw [a, Int.cast_sum]
    have step1 : ∀ k ∈ Finset.range (n + 1),
        ((T n k : ℤ) : ZMod 2) =
          ∑ j ∈ Finset.range (n + 1),
            ((|ArithmeticFunction.moebius (n.choose j)| : ℤ) : ZMod 2) *
              ((j.choose k : ℤ) : ZMod 2) := by
      intro k _
      rw [T]
      rw [hcast]
      rw [Int.cast_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [Int.cast_mul, hcast]
    rw [Finset.sum_congr rfl step1]
    rw [Finset.sum_comm]
    have step3 : ∀ j ∈ Finset.range (n + 1),
        ∑ k ∈ Finset.range (n + 1),
            ((|ArithmeticFunction.moebius (n.choose j)| : ℤ) : ZMod 2) *
              ((j.choose k : ℤ) : ZMod 2)
          = ((|ArithmeticFunction.moebius (n.choose j)| : ℤ) : ZMod 2) * (2 : ZMod 2) ^ j := by
      intro j hj
      rw [← Finset.mul_sum]
      rw [hsum j (by simpa [Finset.mem_range] using hj)]
    rw [Finset.sum_congr rfl step3]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [h2, zero_pow hj, mul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h
  exact ZMod.intCast_eq_one_iff_odd.mp hmain
