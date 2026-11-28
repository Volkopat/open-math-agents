import FormalConjectures.ErdosProblems.«396»

-- Reduction Erdos396.erdos_396.R1 of Erdős problem 396
-- Credit: @marcusbuffett

/-!
# Erdős 396: the cases `k ≤ 4` by explicit witnesses, and the open rest

The problem asks whether for every `k` there is an `n` such that `n (n - 1) ⋯ (n - k)` divides
the central binomial coefficient `C(2n, n)`.

* `H1`: this holds for `k ≤ 4`, with the least witnesses `n = 1, 2, 2480, 8178, 45153`.
* `H2`: it holds for every `k ≥ 5`. This is open in general (witnesses are known for a few more
  values of `k`; they are too large for the method used here).
-/

namespace OMA.R_Erdos396_erdos_396_R1

/-- The cases with small explicit witnesses. -/
def H1 : Prop :=
  ∀ k : ℕ, k ≤ 4 → ∃ n : ℕ, Nat.descFactorial n (k + 1) ∣ Nat.centralBinom n

/-- The open part. -/
def H2 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∃ n : ℕ, Nat.descFactorial n (k + 1) ∣ Nat.centralBinom n

theorem main : H1 → H2 → type_of% @Erdos396.erdos_396 := by
  intro h1 h2 k
  by_cases h : k ≤ 4
  · exact h1 k h
  · exact h2 k (by omega)

end OMA.R_Erdos396_erdos_396_R1
