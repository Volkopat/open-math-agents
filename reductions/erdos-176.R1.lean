import OMAStatements.S_erdos_176
import Mathlib

/-!
Reduction erdos-176.R1: split by the size of the required discrepancy `c k`.

H1 is the classical regime `ℓ = 1`: every `±1` colouring of `{1, …, N}` with `N ≥ k ^ 2` has a
`k`-term progression with nonzero sum, so `N(k, 1) ≤ k ^ 2` (Spencer 1973 found the exact value
`N(k, 1) = 2 ^ t (k - 1) + 1` for `k = 2 ^ t m`, `m` odd). It settles every pair `(c, k)` with
`c k ≤ 1`, taking `C ≥ 4`. This is a known case, not progress on the problem.
H2 is the open remainder: the pairs with `c k > 1`.
-/

namespace OMA.R_erdos_176_R1

/-- `N(k, 1) ≤ k ^ 2`: a `k`-term progression with nonzero sum in every colouring. -/
def H1 : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ N : ℕ, k ^ 2 ≤ N → ∀ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) →
    ∃ a d : ℕ, 1 ≤ a ∧ 1 ≤ d ∧ a + (k - 1) * d ≤ N ∧
      (∑ i ∈ Finset.range k, f (a + i * d)) ≠ 0

/-- The open remainder: the bound `N(k, c k) ≤ C ^ k` for the lengths `k` with `c k > 1`. -/
def H2 : Prop :=
  ∀ c : ℝ, 0 < c → c < 1 → ∃ C : ℝ, 1 < C ∧ ∀ k : ℕ, 1 ≤ k → 1 < c * k →
    ∀ N : ℕ, C ^ k ≤ N →
      ∀ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) →
        ∃ a d : ℕ, 1 ≤ a ∧ 1 ≤ d ∧ a + (k - 1) * d ≤ N ∧
          c * k ≤ |((∑ i ∈ Finset.range k, f (a + i * d) : ℤ) : ℝ)|

lemma sq_le_four_pow (k : ℕ) : k ^ 2 ≤ 4 ^ k := by
  have h := Nat.lt_two_pow_self (n := k)
  calc k ^ 2 ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left h.le 2
    _ = 4 ^ k := by rw [← pow_mul, mul_comm, pow_mul]; norm_num

theorem main : H1 → H2 → type_of% @OMA.S_erdos_176.main := by
  intro h1 h2 c hc0 hc1
  obtain ⟨C, hC, hC2⟩ := h2 c hc0 hc1
  refine ⟨max C 4, lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
  intro k hk N hN f hf
  by_cases hck : c * k ≤ 1
  · have hpow : ((4 : ℝ)) ^ k ≤ N :=
      le_trans (pow_le_pow_left₀ (by norm_num) (le_max_right C 4) k) hN
    have hkN : k ^ 2 ≤ N := by
      have h4 : ((k ^ 2 : ℕ) : ℝ) ≤ ((4 ^ k : ℕ) : ℝ) := by exact_mod_cast sq_le_four_pow k
      have : ((k ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) := by
        refine le_trans h4 ?_
        push_cast
        exact hpow
      exact_mod_cast this
    obtain ⟨a, d, ha, hd, hle, hne⟩ := h1 k hk N hkN f hf
    refine ⟨a, d, ha, hd, hle, le_trans hck ?_⟩
    have : (1 : ℤ) ≤ |∑ i ∈ Finset.range k, f (a + i * d)| := Int.one_le_abs hne
    rw [← Int.cast_abs]
    exact_mod_cast this
  · push Not at hck
    exact hC2 k hk hck N
      (le_trans (pow_le_pow_left₀ (by linarith) (le_max_left C 4) k) hN) f hf

end OMA.R_erdos_176_R1
