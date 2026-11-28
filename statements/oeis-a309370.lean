import Mathlib

/-!
# OEIS A309370: maximum size of a Sidon subset of the binary cube

Source: https://oeis.org/A309370 (Asier Calbet Rípodas, OEIS Foundation, CC BY-SA 4.0)
Credit: @Medrov
-/

namespace OMA.S_oeis_a309370

/-- Equal coordinatewise sums determine the two binary vectors up to swapping them.
    Coordinates are added in `ℕ`, so a pair of ones has sum two. -/
def IsSidon {n : ℕ} (S : Finset (Fin n → Fin 2)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    (∀ i, (a i : ℕ) + (b i : ℕ) = (c i : ℕ) + (d i : ℕ)) →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c)

instance {n : ℕ} (S : Finset (Fin n → Fin 2)) : Decidable (IsSidon S) := by
  unfold IsSidon
  infer_instance

/-- The largest cardinality among all Sidon subsets of the `n`-dimensional binary cube. -/
def maxSidonSize (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin 2)).powerset.filter IsSidon).sup Finset.card

open scoped Asymptotics

/-- OEIS conjectures that `a(n)` is asymptotic to `2^(n/2 + 1)` as `n` tends to infinity. -/
theorem main :
    (fun n : ℕ => (maxSidonSize n : ℝ)) ~[Filter.atTop]
      (fun n : ℕ => (2 : ℝ) ^ ((n : ℝ) / 2 + 1)) := by
  sorry

end OMA.S_oeis_a309370
