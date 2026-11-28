import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi

/-!
# Two partitions counted by A054390

R. J. Mathar conjectured that the number of partitions into powers of 3 used
at most three times each equals the number into distinct parts of A038754.
That sequence consists of the pairs 3^j and 2·3^j for j ≥ 0.

Sources: https://oeis.org/A054390 and https://oeis.org/A038754
Credit: @wtho704
-/

namespace OMA.S_oeis_a054390

/-- Sum of a multiset of weights, each given its multiplicity in {0,1,2,3}. -/
def boundedWeight {ι : Type*} [Fintype ι] (w : ι → ℕ) (d : ι → Fin 4) : ℕ :=
  ∑ i, (d i : ℕ) * w i

/-- Sum of a subset of the parts. The false label denotes w(i), and the true
label denotes 2·w(i). For w(i)=3^i all the labelled parts are distinct. -/
def distinctWeight {ι : Type*} (w : ι → ℕ) (s : Finset (ι × Bool)) : ℕ :=
  ∑ p ∈ s, if p.2 then 2 * w p.1 else w p.1

/-- Exponents below n suffice because 3^j > j. At n=0 both sides count the
empty partition. Counts are over multiplicity functions and unordered subsets. -/
theorem main : ∀ n : ℕ,
    Fintype.card {d : Fin n → Fin 4 // boundedWeight (fun i : Fin n => 3 ^ (i : ℕ)) d = n} =
    Fintype.card {s : Finset (Fin n × Bool) // distinctWeight (fun i : Fin n => 3 ^ (i : ℕ)) s = n} := by
  sorry

end OMA.S_oeis_a054390
