import Mathlib

/-!
# OEIS A222001

Number of `n × 3` arrays with each row a permutation of `1..3` having at least as many
downsteps as the preceding row, with rows in lexicographically nonincreasing order.

Conjectured by Colin Barker (Aug 14 2018):
* `a(n) = 2 + (1 + n) * (2 + n) * (3 + n) / 6` for all `n ≥ 1`.
-/

namespace OMA.S_oeis_a222001

/-- Number of downsteps (`r (j+1) < r j`) in a row of length 3. -/
def downsteps (r : Fin 3 → Fin 3) : ℕ :=
  (if r 1 < r 0 then 1 else 0) + (if r 2 < r 1 then 1 else 0)

/-- Lexicographical `≥` on length-3 rows. -/
def lexGE (r s : Fin 3 → Fin 3) : Prop :=
  s 0 < r 0 ∨ (r 0 = s 0 ∧ (s 1 < r 1 ∨ (r 1 = s 1 ∧ s 2 ≤ r 2)))

/-- An `n × 3` array of permutations of `Fin 3` is valid if each row has at least as many
downsteps as the preceding row and rows are in lexicographically nonincreasing order. -/
def isValid (n : ℕ) (A : Fin n → Fin 3 → Fin 3) : Prop :=
  (∀ i : Fin n, Function.Bijective (A i)) ∧
  (∀ (i : Fin n) (h : i.1 + 1 < n), downsteps (A i) ≤ downsteps (A ⟨i.1 + 1, h⟩)) ∧
  (∀ (i : Fin n) (h : i.1 + 1 < n), lexGE (A i) (A ⟨i.1 + 1, h⟩))

/-- `a(n)` is the number of valid `n × 3` arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {A : Fin n → Fin 3 → Fin 3 // isValid n A}

theorem main :
    ∀ n : ℕ, 1 ≤ n → a n = 2 + (1 + n) * (2 + n) * (3 + n) / 6 := by
  sorry

end OMA.S_oeis_a222001
