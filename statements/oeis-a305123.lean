import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Combinatorics.Enumerative.Partition.Basic

namespace OMA.S_oeis_a305123

/-!
OEIS A305123: G.f. A(x) = (Sum_{k>=1} x^(2*k-1) / (1 + x^(2*k-1))) * Product_{k>=1} 1/(1 - x^k).
Here Product_{k>=1} 1/(1 - x^k) = Sum_{n>=0} p(n) * x^n is the partition generating function,
and for any degree n, terms with k > n have 2*k - 1 > n and contribute 0 to [x^n].
Conjecture: a(n) is odd iff n is in A067567, i.e. n is odd and p(n) is odd.
-/

theorem main : ∀ (A : PowerSeries ℤ),
    (∀ n : ℕ, PowerSeries.coeff n A =
      PowerSeries.coeff n
        ((∑ k ∈ Finset.Icc 1 n,
            PowerSeries.X ^ (2 * k - 1) * Ring.inverse (1 + PowerSeries.X ^ (2 * k - 1))) *
          PowerSeries.mk (fun m => (Fintype.card (Nat.Partition m) : ℤ)))) →
    ∀ n : ℕ, Odd (PowerSeries.coeff n A) ↔ Odd n ∧ Odd (Fintype.card (Nat.Partition n)) := by
  sorry

end OMA.S_oeis_a305123
