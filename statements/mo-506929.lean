import Mathlib

/-!
# An alternating sum over ordered multiplicative factorizations

Source: Glacier, https://mathoverflow.net/questions/506929 (CC BY-SA 4.0).
Credit: @connoranderson.

The nonempty list a gives the positive multiplicities of the distinct primes
of n. With j ordered slots allowing trivial factors, each prime independently
distributes its r copies in multichoose(j,r) ways. Inclusion-exclusion on the
empty slots gives the number of ordered factorizations into k factors > 1.
The Bernoulli numbers here use B₁ = −1/2. The source also asks whether the
alternating sum always belongs to [−1,1] for mixed prime factorizations.
-/

namespace OMA.S_mo_506929
open Polynomial Finset
noncomputable section

def orderedCount (a : List ℕ) (k : ℕ) : ℚ :=
  ∑ j ∈ range (k+1), (-1:ℚ)^(k-j)*(k.choose j:ℚ)*
    (a.map (fun r => (Nat.multichoose j r:ℚ))).prod

def value (a : List ℕ) : ℚ :=
  ∑ k ∈ range a.sum, (-1:ℚ)^k * orderedCount a (k+1) / (k+2)

def slotPoly (a : List ℕ) : ℚ[X] :=
  (a.map (fun r => C (r.factorial:ℚ)⁻¹ * ascPochhammer ℚ r)).prod

theorem main :
    (∀ a : List ℕ, a ≠ [] → (∀ r ∈ a, 0<r) →
      value a = -(∑ j ∈ range (a.sum+1), (slotPoly a).coeff j * _root_.bernoulli j)) ∧
    (∀ r : ℕ, value (2::List.replicate r 1) =
      -(_root_.bernoulli (r+2)+_root_.bernoulli (r+1))/2) ∧
    (1 < value (2::List.replicate 14 1) ∧ value (2::List.replicate 16 1) < -1) := by
  sorry

end
end OMA.S_mo_506929
