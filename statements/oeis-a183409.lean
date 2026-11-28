import Mathlib

/-!
# OEIS A183409

Number of `n × 2` binary arrays with each prefix sum `a(1..i, 1..j)` no greater than `i * j / 2`,
and rows and columns in lexicographically nondecreasing order.

Conjectured by Luce ETIENNE (Nov 18 2014):
* `32 * a(n) = 2 * n^3 + 11 * n^2 + 31 * n + 27 + (n^2 + n + 5) * (-1)^n` for all `n ≥ 1`.
-/

namespace OMA.S_oeis_a183409

/-- An `n × 2` binary array `A : Fin n → Fin 2 → Fin 2` is valid if:
1. rows are in lexicographically nondecreasing order,
2. columns are in lexicographically nondecreasing order (column 0 ≤_lex column 1),
3. every `i × 1` prefix sum satisfies `2 * ∑_{r < i} A r 0 ≤ i`,
4. every `i × 2` prefix sum satisfies `∑_{r < i} (A r 0 + A r 1) ≤ i`. -/
def isValid (n : ℕ) (A : Fin n → Fin 2 → Fin 2) : Prop :=
  (∀ (i : Fin n) (h : i.1 + 1 < n),
    A i 0 < A ⟨i.1 + 1, h⟩ 0 ∨ (A i 0 = A ⟨i.1 + 1, h⟩ 0 ∧ A i 1 ≤ A ⟨i.1 + 1, h⟩ 1)) ∧
  ((∀ i : Fin n, A i 0 = A i 1) ∨
    (∃ i : Fin n, (∀ k : Fin n, k.1 < i.1 → A k 0 = A k 1) ∧ A i 0 < A i 1)) ∧
  (∀ i : ℕ, i ≤ n → 2 * (∑ r ∈ Finset.univ.filter (fun r : Fin n => r.1 < i), (A r 0).1) ≤ i) ∧
  (∀ i : ℕ, i ≤ n →
    (∑ r ∈ Finset.univ.filter (fun r : Fin n => r.1 < i), ((A r 0).1 + (A r 1).1)) ≤ i)

/-- `a(n)` is the number of valid `n × 2` binary arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {A : Fin n → Fin 2 → Fin 2 // isValid n A}

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      32 * (a n : ℤ) =
        2 * (n : ℤ) ^ 3 + 11 * (n : ℤ) ^ 2 + 31 * (n : ℤ) + 27 +
          ((n : ℤ) ^ 2 + (n : ℤ) + 5) * (-1 : ℤ) ^ n := by
  sorry

end OMA.S_oeis_a183409
