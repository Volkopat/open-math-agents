import Mathlib

/-!
# A001013: Jordan–Pólya numbers

Source: https://oeis.org/A001013
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Jordan–Pólya numbers are the products of factorials (A001013). A034878 lists the `k` such that
`k!` is a product of smaller factorials. OEIS conjecture: except for the numbers `2`, `9` and
`10`, the two sequences are the same.

## Encoding

* Factors `0! = 1! = 1` are irrelevant, so products range over multisets of integers `≥ 2`
  (the empty product `1` is a Jordan–Pólya number).
* `k` is in A034878 if `k! = ∏ j!` for a multiset of integers `j` with `2 ≤ j < k`.
* The exceptions: `2` is Jordan–Pólya but `2! = 2` is not a product of smaller factorials
  `≥ 2!`; `9! = 7!·3!·3!·2!` and `10! = 7!·6!` while `9, 10` are not products of factorials.
  The statement is about `k ≥ 1`: `k ∉ {2, 9, 10}` implies (`k` Jordan–Pólya iff `k ∈ A034878`).
  The value `k = 1` (`1! = ` empty product) is in both sequences under this encoding.
-/

namespace OMA.S_oeis_a001013

/-- `n` is a product of factorials of integers `≥ 2`. -/
def IsJordanPolya (n : ℕ) : Prop :=
  ∃ s : Multiset ℕ, (∀ j ∈ s, 2 ≤ j) ∧ (s.map Nat.factorial).prod = n

/-- `k!` is a product of factorials of integers `j` with `2 ≤ j < k` (A034878). -/
def FactorialOfSmaller (k : ℕ) : Prop :=
  ∃ s : Multiset ℕ, (∀ j ∈ s, 2 ≤ j ∧ j < k) ∧ (s.map Nat.factorial).prod = k.factorial

theorem main :
    ∀ k : ℕ, 1 ≤ k → k ∉ ({2, 9, 10} : Set ℕ) → (IsJordanPolya k ↔ FactorialOfSmaller k) := by
  sorry

end OMA.S_oeis_a001013
