import OMAStatements.S_mse_468037
import Mathlib

-- Reduction mse-468037.R1 of Math.SE 468037 (can an odd perfect number be divisible by 101?)
-- Credit: @marcusbuffett

/-!
# Odd perfect numbers divisible by 101: Euler's form, and the open rest

The question asks whether an odd perfect number can be divisible by `101`; `main` states that it
cannot. This separates the classical theorem of Euler from the open part. It is a classical
structural result, not progress on the question itself.

* `H1` (Euler): every odd perfect number is `q^k m^2` with `q` prime, `q ≡ k ≡ 1 (mod 4)` and
  `gcd(q, m) = 1`. Proof: `σ(N) = 2N` with `N` odd, so `σ(N) ≡ 2 (mod 4)`; for an odd prime `p`,
  `σ(p^a) = 1 + p + ⋯ + p^a` is odd exactly when `a` is even, and is `≡ 2 (mod 4)` exactly when
  `p ≡ a ≡ 1 (mod 4)`; multiplicativity of `σ` over coprime factors then gives the form.
* `H2`: no odd perfect number in Euler's form is divisible by `101`. This is the open question.
-/

namespace OMA.R_mse_468037_R1

/-- Euler's theorem on the form of odd perfect numbers. -/
def H1 : Prop :=
  ∀ N : ℕ, Odd N → Nat.Perfect N →
    ∃ q k m : ℕ, q.Prime ∧ q % 4 = 1 ∧ k % 4 = 1 ∧ q.Coprime m ∧ N = q ^ k * m ^ 2

/-- The open part: an odd perfect number in Euler's form is not divisible by `101`. -/
def H2 : Prop :=
  ∀ N q k m : ℕ, Odd N → Nat.Perfect N → q.Prime → q % 4 = 1 → k % 4 = 1 → q.Coprime m →
    N = q ^ k * m ^ 2 → ¬ 101 ∣ N

theorem main : H1 → H2 → type_of% @OMA.S_mse_468037.main := by
  intro h1 h2 N hN hp
  obtain ⟨q, k, m, hq, hq4, hk4, hqm, hNe⟩ := h1 N hN hp
  exact h2 N q k m hN hp hq hq4 hk4 hqm hNe

end OMA.R_mse_468037_R1
