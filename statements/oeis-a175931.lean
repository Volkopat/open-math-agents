import Mathlib

/-!
# A175931: Numbers n such that A129363(n-1) = A129363(n) = A129363(n+1).

Source: https://oeis.org/A175931
Credit: @luciusacarr

Data: 8, 9, 48, 54, 198, 201, 258, 348, 393, 453, 558, 573, 633, 678, 1623, 2103.
No further term between 2103 and 26000 (R. J. Mathar).

Conjecture (from the entry): the sequence is finite and complete with last term 2103. `main`
states it.

Reading of the source:
* A129363(n) is the number of partitions of 2n into the sum of two twin primes: the number of
  unordered pairs `p ≤ q` with `p + q = 2n` and `p`, `q` both members of twin prime pairs
  (A001097: primes `p` with `p - 2` or `p + 2` prime). Equal parts are allowed
  (394 = 197 + 197). It is counted here as the number of `p ≤ n` with `p` and `2n - p` twin
  prime members.
* A129363 has offset 1, so `n - 1 ≥ 1`: `n` ranges over `n ≥ 2`.
* With this reading the terms below 26000 are exactly the sixteen listed (checked numerically),
  so "finite and complete" is stated as the equality of the set of terms with the listed set.
-/

namespace OMA.S_oeis_a175931

/-- `p` is a member of a pair of twin primes (A001097). -/
def IsTwinPrimeMember (p : ℕ) : Prop := p.Prime ∧ ((p + 2).Prime ∨ (2 ≤ p ∧ (p - 2).Prime))

/-- A129363(n): the number of partitions of `2n` into two twin prime members. -/
noncomputable def A129363 (n : ℕ) : ℕ :=
  open Classical in
  ((Finset.range (n + 1)).filter
    (fun p => IsTwinPrimeMember p ∧ IsTwinPrimeMember (2 * n - p))).card

/-- The terms of A175931. -/
def S : Set ℕ := {n | 2 ≤ n ∧ A129363 (n - 1) = A129363 n ∧ A129363 n = A129363 (n + 1)}

theorem main :
    -- The sequence is finite and complete, with last term 2103.
    S = {8, 9, 48, 54, 198, 201, 258, 348, 393, 453, 558, 573, 633, 678, 1623, 2103} := by
  sorry

end OMA.S_oeis_a175931
