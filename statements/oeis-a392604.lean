import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Defs

/-!
Antti Karttunen's OEIS A392604 (https://oeis.org/A392604), CC BY-SA 4.0.
The 1-bit positions of k select distinct primes, whose product is A019565(k).
For this squarefree product N, A380459(N) is the product of A276086(N/p) over
the selected primes p. In A276086(x) the exponent of the j-th prime is the
j-th primorial digit of x. Thus excluding all prime powers p^p as divisors is
exactly the column inequality below. The conjectured bound is on the binary
weight of *every* such k. The first prime has index zero.
-/

namespace OMA.S_oeis_a392604

noncomputable def radix (j : ℕ) : ℕ := Nat.nth Nat.Prime j

noncomputable def place : ℕ → ℕ
  | 0 => 1
  | j + 1 => place j * radix j

noncomputable def digit (x j : ℕ) : ℕ := x / place j % radix j

noncomputable def selected (k : ℕ) : List ℕ := k.bitIndices.map radix

def qualifies (k : ℕ) : Prop :=
  ∀ j, ((selected k).map (fun p => digit ((selected k).prod / p) j)).sum < radix j

theorem main : ∀ k : ℕ, qualifies k → k.bitIndices.length ≤ 4 := by
  sorry

end OMA.S_oeis_a392604
