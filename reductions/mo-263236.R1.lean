import OMAStatements.S_mo_263236
import Mathlib

/-!
# Reduction of MathOverflow 263236: three infinite families and the core

`H n k` is the `k`-th elementary symmetric function of `1/1, …, 1/n`. The question asks whether
only finitely many `H n k` with `1 ≤ k ≤ n` are `2`-adic integers.

* `H1` (classical, three infinite families): along the extreme rows `k = 1`, `k = n - 1` and
  `k = n`, a `2`-adic integer occurs only for `n ≤ 3`. For `k = 1`, `H n 1` is the harmonic number
  and has `2`-adic valuation `-⌊log₂ n⌋` (Theisinger's argument); for `k = n`, `H n n = 1 / n!`; for
  `k = n - 1`, `H n (n - 1) = (1 + ⋯ + n) / n! = (n + 1) / (2 (n - 1)!)`, whose valuation is
  negative for `n ≥ 4` because `2 ^ v₂(n + 1)` divides `(n - 1)!`. The only exceptions are
  `H 1 1 = 1` and `H 3 2 = 1`.
* `H2` (the open core): the pairs with `2 ≤ k ≤ n - 2` giving a `2`-adic integer form a finite set.

This is a classical partial case, not progress on the open question.
-/

namespace OMA.R_mo_263236_R1

/-- The rows `k = 1`, `k = n - 1`, `k = n` contain `2`-adic integers only for `n ≤ 3`. -/
def H1 : Prop :=
  ∀ n k : ℕ, 1 ≤ k → k ≤ n → (k = 1 ∨ k + 1 = n ∨ k = n) →
    0 ≤ padicValRat 2 (OMA.S_mo_263236.H n k) → n ≤ 3

/-- The open core: the interior rows `2 ≤ k ≤ n - 2` contain only finitely many `2`-adic
integers. -/
def H2 : Prop :=
  {p : ℕ × ℕ | 2 ≤ p.2 ∧ p.2 + 2 ≤ p.1 ∧ 0 ≤ padicValRat 2 (OMA.S_mo_263236.H p.1 p.2)}.Finite

theorem main : H1 → H2 → type_of% @OMA.S_mo_263236.main := by
  intro h1 h2
  apply (h2.union ((Set.finite_Iic (3 : ℕ)).prod (Set.finite_Iic (3 : ℕ)))).subset
  rintro ⟨n, k⟩ ⟨hk1, hkn, hv⟩
  simp only at hk1 hkn hv
  by_cases hin : 2 ≤ k ∧ k + 2 ≤ n
  · exact Or.inl ⟨hin.1, hin.2, hv⟩
  · right
    have hcase : k = 1 ∨ k + 1 = n ∨ k = n := by omega
    have hn := h1 n k hk1 hkn hcase hv
    exact ⟨Set.mem_Iic.mpr hn, Set.mem_Iic.mpr (by omega)⟩

end OMA.R_mo_263236_R1
