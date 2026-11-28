import Mathlib

/-!
# A006946: Independence number of de Bruijn graph of order n on two symbols

Source: https://oeis.org/A006946
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

## Problem Statement
Let `a(n)` be the independence number of the underlying simple graph of the binary de Bruijn
graph of order `n` (vertices are binary words of length `n`, with distinct vertices `u ≠ v`
adjacent iff `u` shifts to `v` or `v` shifts to `u`).
Let `A000031(n) = (1/n) * ∑_{d | n} φ(d) * 2^(n/d)` be the number of binary necklaces of
length `n`.

Conjecture: For every `n ≥ 1`, equality holds in Lichiardopol's bounds:
- for odd `n`: `a(n) = 2^(n - 1) - A000031(n) / 2 + 1`, i.e., `2 * a(n) + A000031(n) = 2^n + 2`;
- for even `n`: `a(n) = 2^(n - 1) - A000031(n + 1) / 4 + 1`, i.e., `4 * a(n) + A000031(n + 1) = 2^(n + 1) + 4`.
-/

namespace OMA.S_oeis_a006946

/-- Directed shift edge in the binary de Bruijn graph of order `n`. -/
def shiftsTo {n : ℕ} (u v : Fin n → Bool) : Prop :=
  ∀ i : ℕ, (h : i + 1 < n) → u ⟨i + 1, h⟩ = v ⟨i, Nat.lt_of_succ_lt h⟩

/-- Adjacency in the underlying simple graph of the binary de Bruijn graph of order `n`. -/
def deBruijnAdj {n : ℕ} (u v : Fin n → Bool) : Prop :=
  u ≠ v ∧ (shiftsTo u v ∨ shiftsTo v u)

/-- A set of vertices is independent if no two vertices in it are adjacent. -/
def isIndependent {n : ℕ} (S : Finset (Fin n → Bool)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬ deBruijnAdj u v

/-- Independence number of the binary de Bruijn graph of order `n`. -/
noncomputable def indepNum (n : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ S : Finset (Fin n → Bool), isIndependent S ∧ S.card = k }

/-- Number of binary necklaces of length `n` (A000031). -/
def binaryNecklaces (n : ℕ) : ℕ :=
  (∑ d ∈ n.divisors, Nat.totient d * 2 ^ (n / d)) / n

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (Odd n → 2 * indepNum n + binaryNecklaces n = 2 ^ n + 2) ∧
      (Even n → 4 * indepNum n + binaryNecklaces (n + 1) = 2 ^ (n + 1) + 4) := by
  sorry

end OMA.S_oeis_a006946
