import Mathlib

/-!
# A168019: Square array A(n,k) read by antidiagonals, in which row n lists the number of partitions of n into parts divisible by k+1

Source: https://oeis.org/A168019
Credit: @xor2k

Formalizes the OEIS A168019 conjecture (Omar E. Pol): Let A(n,k) denote the number of
partitions of n into parts divisible by k+1. Let p(n) denote the number of partitions of n.
If k+1 is a divisor of n then A(n,k) = p(n/(k+1)) otherwise A(n,k) = 0.

Conventions:
* Offset 0 for both indices: `n k : ℕ`, matching the OEIS array (which starts with A(0,0) = 1).
* Partitions of `n` are Mathlib's `Nat.Partition n` (finite multisets of positive parts summing
  to `n`; `n = 0` has exactly the empty partition). `A n k` counts those all of whose parts are
  divisible by `k + 1`, and `p(m) = Fintype.card (Nat.Partition m)`.
* `n / (k + 1)` is natural-number division; it is exact in the branch where `k + 1 ∣ n`.
-/

namespace OMA.S_oeis_a168019

/-- `A(n, k)`: the number of partitions of `n` into parts divisible by `k + 1`. -/
def A (n k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter (fun p => ∀ i ∈ p.parts, k + 1 ∣ i)).card

/-- `A(n, k) = p(n / (k + 1))` if `k + 1 ∣ n`, and `A(n, k) = 0` otherwise. -/
theorem main :
    ∀ n k : ℕ, A n k = if k + 1 ∣ n then Fintype.card (Nat.Partition (n / (k + 1))) else 0 := by
  sorry

end OMA.S_oeis_a168019
