import Mathlib

/-!
# Random stable roommates

Source: https://www.openproblemgarden.org/op/random_stable_roommates
Credit: @ishaanzee

**Conjecture** (S. Mertens). The probability that a random instance of the stable roommates problem
on `n ∈ 2ℕ` people admits a solution is `Θ(n^(-1/4))`.

A system of preferences on the complete graph `K_n` gives every person `v` a linear ordering of the
other `n - 1` people. A perfect matching `M` is stable if there do not exist `uv, u'v' ∈ M` such that
`u` prefers `v'` to `v` and `v'` prefers `u` to `u'`. A random instance chooses every person's
ordering uniformly and independently.

Formalization:
* People are `Fin n`. The preference order of `v` is a bijection `{u // u ≠ v} ≃ Fin (n - 1)` giving
  each other person a rank (rank `0` is the most preferred). An instance is a choice of such a
  bijection for every `v`; the uniform random instance makes `Pₙ` the number of instances that admit
  a stable perfect matching divided by the number of all instances.
* A perfect matching is a fixed-point-free involution `m : Fin n → Fin n` (`m v` is the partner of
  `v`). It is stable when there are no two people `u ≠ w`, not matched together, such that `u` ranks
  `w` above `m u` and `w` ranks `u` above `m w`.
* `Θ(n^(-1/4))` over even `n`: constants `0 < c, C` with `c n^(-1/4) ≤ Pₙ ≤ C n^(-1/4)` for every
  even `n ≥ 2`.
-/

namespace OMA.S_opg_random_stable_roommates

/-- A stable roommates instance on `n` people: each person's ranking of the others. -/
abbrev Instance (n : ℕ) : Type := (v : Fin n) → ({u : Fin n // u ≠ v} ≃ Fin (n - 1))

/-- In instance `I`, person `v` prefers `a` to `b`. -/
def Prefers {n : ℕ} (I : Instance n) (v a b : Fin n) : Prop :=
  ∃ (ha : a ≠ v) (hb : b ≠ v), I v ⟨a, ha⟩ < I v ⟨b, hb⟩

/-- `m` is a stable perfect matching for `I`. -/
def IsStableMatching {n : ℕ} (I : Instance n) (m : Fin n → Fin n) : Prop :=
  (∀ v, m (m v) = v) ∧ (∀ v, m v ≠ v) ∧
    ¬ ∃ u w : Fin n, u ≠ w ∧ m u ≠ w ∧ Prefers I u w (m u) ∧ Prefers I w u (m w)

/-- `Pₙ`: the probability that a uniformly random instance on `n` people admits a stable matching. -/
noncomputable def solvableProb (n : ℕ) : ℝ :=
  (Nat.card {I : Instance n // ∃ m, IsStableMatching I m} : ℝ) / (Nat.card (Instance n) : ℝ)

/-- **Mertens' conjecture**: `Pₙ = Θ(n^(-1/4))` for even `n`. -/
theorem main : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n → Even n →
    c * (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤ solvableProb n ∧
      solvableProb n ≤ C * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
  sorry

end OMA.S_opg_random_stable_roommates
