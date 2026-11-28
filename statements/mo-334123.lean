import Mathlib

/-!
# MathOverflow 334123: strong uniqueness of Euler's totient function

Source: https://mathoverflow.net/questions/334123 (CC BY-SA 4.0).

For `f : ℕ → ℂ` let `φ_f(n) = ∑_{k ≤ n, (k, n) = 1} f(k)`, the sum of `f` over the totatives of
`n` (so `φ_1 = φ` and `φ_{δ₁} = 1`). Call `g` eventually multiplicative if some multiplicative
`G` has `g(n) = G(n)` for all large enough `n`. Question: is it true that if `f` is completely
multiplicative and `φ_f` is eventually multiplicative then `f = δ₁` or `f = 1`? `main` states
the affirmative. (The post first notes, from computations, the version with `φ_f` multiplicative;
the question asked is the eventual one stated here.)

Conventions: arithmetic functions live on the positive integers, so values at `0` play no role.
Completely multiplicative means `f 1 = 1` and `f (m n) = f m · f n` for all `m, n ≥ 1`;
multiplicative means `G 1 = 1` and `G (m n) = G m · G n` for coprime `m, n ≥ 1`. Totatives `k`
of `n` range over `1 ≤ k ≤ n` with `gcd(k, n) = 1`.
-/

namespace OMA.S_mo_334123

/-- `φ_f(n)`: the sum of `f` over the totatives of `n`. -/
noncomputable def phiF (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ (Finset.Icc 1 n).filter (fun k => Nat.Coprime k n), f k

theorem main : ∀ f : ℕ → ℂ,
    f 1 = 1 → (∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n) →
    (∃ G : ℕ → ℂ, G 1 = 1 ∧
      (∀ m n : ℕ, 0 < m → 0 < n → Nat.Coprime m n → G (m * n) = G m * G n) ∧
      ∃ N : ℕ, ∀ n ≥ N, phiF f n = G n) →
    (∀ n : ℕ, 0 < n → f n = if n = 1 then 1 else 0) ∨ (∀ n : ℕ, 0 < n → f n = 1) := by
  sorry

end OMA.S_mo_334123
