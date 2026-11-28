import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic

namespace OMA.S_oeis_a383505

/-- OEIS A383505 conjecture: for every prime `p`, letting `n = p ^ 2` (a term of A000430),
the least `k : ℕ` such that `Nat.choose (k * n) (k + 1) ≡ n - 1 [MOD n]` is `k = n - 1`. -/
theorem main :
    ∀ p : ℕ, p.Prime →
      Nat.choose ((p ^ 2 - 1) * p ^ 2) (p ^ 2) ≡ p ^ 2 - 1 [MOD p ^ 2] ∧
      ∀ k < p ^ 2 - 1, ¬ (Nat.choose (k * p ^ 2) (k + 1) ≡ p ^ 2 - 1 [MOD p ^ 2]) := by
  sorry

end OMA.S_oeis_a383505
