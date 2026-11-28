import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a396805

/-- Divided power `[x^n / n!] (G(x)^k / k!)` for an e.g.f. `G` with `G 0 = 0`. -/
def egfDivPow (G : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, n => if n = 0 then 1 else 0
  | _ + 1, 0 => 0
  | k + 1, n + 1 =>
    ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℤ) * G (j + 1) * egfDivPow G k (n - j)

/-- Exponential generating function composition `(F ∘ G)(x) = ∑_{k≥0} F[k] * G(x)^k / k!`. -/
def egfComp (F G : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), F k * egfDivPow G k n

/-- `k`-th compositional iterate of an e.g.f. `F` with `F 0 = 0`. -/
def egfIter (F : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0 => fun n => if n = 1 then 1 else 0
  | k + 1 => egfComp (egfIter F k) F

/-- Exponential `[x^n / n!] exp(F(x))` for an e.g.f. `F` with `F 0 = 0`. -/
def egfExp (F : ℕ → ℤ) : ℕ → ℤ
  | 0 => 1
  | n + 1 =>
    ∑ j : Fin (n + 1), (Nat.choose n j.1 : ℤ) * F (j.1 + 1) * egfExp F (n - j.1)
termination_by n => n

/-- OEIS A396805: e.g.f. `A(x) = ∑_{n≥1} a(n) x^n / n!` satisfying `A(x) = x * exp(A^5(x))`,
where `A^5(x)` is the 5th compositional iterate of `A`. -/
def a : ℕ → ℤ
  | 0 => 0
  | n + 1 =>
    let trunc : ℕ → ℤ := fun m => if _ : m < n + 1 then a m else 0
    ((n + 1 : ℕ) : ℤ) * egfExp (egfIter trunc 5) n
termination_by n => n

/-- OEIS A396805 conjecture: `a(n) ≡ [1, 2, 3, 4, 0]` repeating `(mod 5)` for all `n ≥ 1`
(i.e. `a(n) ≡ n (mod 5)`). -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n ≡ (n : ℤ) [ZMOD 5] := by
  sorry

end OMA.S_oeis_a396805
