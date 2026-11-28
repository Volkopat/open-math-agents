import Mathlib

/-!
# A057368: Number of Gaussian primes (in the first half-quadrant; i.e., 0 to 45 degrees) with real part = n.

Source: https://oeis.org/A057368
Credit: @keiichisince1986-bot

A057368 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 0.

Conventions:
- A Gaussian prime is a prime element of the Gaussian integers `ℤ[i]` (Mathlib's `GaussianInt`).
- For real part `n > 0`, the Gaussian integer `n + b i` lies in the first half-quadrant (argument
  from 0 to 45 degrees, inclusive) exactly when `0 ≤ b ≤ n`; this inclusive reading matches the
  data.
- `a(n) > 0` means that `n + b i` is a Gaussian prime for some integer `0 ≤ b ≤ n`.
-/

namespace OMA.S_oeis_a057368

theorem main :
    ∀ n : ℕ, 0 < n → ∃ b : ℤ, 0 ≤ b ∧ b ≤ n ∧ Prime (⟨n, b⟩ : GaussianInt) := by
  sorry

end OMA.S_oeis_a057368
