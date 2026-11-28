import Mathlib

/-!
# A015126: Least k such that phi(k) = phi(n)

Source: https://oeis.org/A015126
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture (Jianing Song, Nov 11 2022):
Let `a(n)` be the least natural number `k` such that `φ(k) = φ(n)`.
Then `a(n)` is always odd whenever `n` is odd.

Conventions:
- `Nat.totient` is Euler's totient function `φ`.
- For odd `n`, `n ≥ 1` so `φ(n) ≥ 1`, hence `k = 0` (with `φ(0) = 0`) never achieves `φ(n)`.
-/

namespace OMA.S_oeis_a015126

noncomputable def aSeq (n : ℕ) : ℕ :=
  Nat.find (⟨n, rfl⟩ : ∃ k : ℕ, Nat.totient k = Nat.totient n)

theorem main : ∀ n : ℕ, Odd n → Odd (aSeq n) := by
  sorry

end OMA.S_oeis_a015126
