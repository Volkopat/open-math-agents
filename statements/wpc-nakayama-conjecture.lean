import Mathlib

/-!
# Nakayama conjecture

Source: https://en.wikipedia.org/wiki/Nakayama%27s_conjecture
Let `A` be a finite-dimensional algebra over a field. If every term of the minimal injective
resolution `0 → A → I₀ → I₁ → ⋯` of `A` as a module over itself is projective (`A` has
infinite dominant dimension), then `A` is self-injective.

Conventions. Modules are left `A`-modules. Instead of the minimal injective resolution we
quantify over all injective resolutions whose terms are also projective: the minimal
resolution is a termwise direct summand of every injective resolution, so its terms are all
projective exactly when some injective resolution has projective terms.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_wpc_nakayama_conjecture

theorem main :
    ∀ (k A : Type) [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
      (I : ℕ → Type) [∀ n, AddCommGroup (I n)] [∀ n, Module A (I n)]
      [∀ n, Module.Injective A (I n)] [∀ n, Module.Projective A (I n)]
      (d₀ : A →ₗ[A] I 0) (d : ∀ n, I n →ₗ[A] I (n + 1)),
      Function.Injective d₀ →
      LinearMap.range d₀ = LinearMap.ker (d 0) →
      (∀ n, LinearMap.range (d n) = LinearMap.ker (d (n + 1))) →
      Module.Injective A A := by
  sorry

end OMA.S_wpc_nakayama_conjecture
