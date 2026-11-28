import Mathlib

/-!
# Finite-time uniform mixing by permutations

Source: Joseph Van Name, https://mathoverflow.net/questions/396352 (CC BY-SA 4.0).
Credit: @connoranderson.

The source asks whether the least number of permutations whose convex combination has
a positive power equal to the uniform matrix is the product of the distinct primes
dividing the number of states. A four-permutation witness on six states disproves this.
Four permutations are necessary when the mixing time is exactly two steps on six states.
The final clause gives a necessary condition for two-permutation mixing after arbitrarily
many steps. In particular it rules out such a witness on six states.
-/

namespace OMA.S_mo_396352
open Matrix

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
noncomputable def uniform (n : ℕ) : Mat n := of fun _ _ => (n : ℝ)⁻¹
noncomputable def mix {n r : ℕ} (p : Fin r → Equiv.Perm (Fin n)) (w : Fin r → ℝ) : Mat n :=
  ∑ a, w a • (p a).permMatrix ℝ

theorem main :
    (∃ (p : Fin 4 → Equiv.Perm (Fin 6)) (w : Fin 4 → ℝ),
      Function.Injective p ∧ (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧
        (mix p w)^2 = uniform 6) ∧
    (∀ (p : Fin 3 → Equiv.Perm (Fin 6)) (w : Fin 3 → ℝ),
      (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 → (mix p w)^2 ≠ uniform 6) ∧
    ∀ (n k : ℕ), 2 ≤ n → 0 < k → ∀ (p q : Equiv.Perm (Fin n)) (a : ℝ),
      0 ≤ a → a ≤ 1 → (a • p.permMatrix ℝ + (1-a) • q.permMatrix ℝ)^k = uniform n →
      a = 1/2 ∧ n ∣ 2^k := by
  sorry

end OMA.S_mo_396352
