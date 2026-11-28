import Mathlib

/-!
# Sycamore's greedy sequence with a prescribed radical

Source: https://oeis.org/A358971 (David James Sycamore, 2022).
Positive integers have the same radical exactly when their sets of prime divisors agree.
Credit: @frido22
-/

namespace OMA.S_oeis_a358971

structure History where
  last : ℕ
  seen : Finset ℕ

noncomputable def state : ℕ → History
  | 0 => ⟨0, {0}⟩
  | 1 => ⟨1, {0, 1}⟩
  | j+2 =>
    let s := state (j+1)
    let k := sInf {k : ℕ | 0 < k ∧ k ≠ j+2 ∧ k ∉ s.seen ∧ k.primeFactors = (j+2).primeFactors}
    ⟨k, insert k s.seen⟩

noncomputable def a (i : ℕ) : ℕ := (state i).last

/-- A strict local minimum among the positive-indexed terms. -/
def localMinimum (i : ℕ) : Prop := 1 < i ∧ a i < a (i-1) ∧ a i < a (i+1)

/-- A term larger than every earlier positive-indexed term. -/
def record (i : ℕ) : Prop := 0 < i ∧ ∀ j : ℕ, 0 < j → j < i → a j < a i

/-- The terms permute the positive integers. Prime values appear in increasing order
and are local minima. One and the squares of primes appear as records. -/
theorem main :
    Set.BijOn a (Set.Ici 1) (Set.Ici 1) ∧
    (∀ i j : ℕ, 0 < i → i < j → (a i).Prime → (a j).Prime → a i < a j) ∧
    (∀ i : ℕ, 0 < i → (a i).Prime → localMinimum i) ∧
    record 1 ∧
    (∀ p : ℕ, p.Prime → ∃ i : ℕ, record i ∧ a i = p^2) := by
  sorry

end OMA.S_oeis_a358971
