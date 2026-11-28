import Mathlib

/-!
# An identity of products of differences of roots of unity

Source: https://mathoverflow.net/questions/503314
Credit: @koolkao

Question (emiliocba, MathOverflow 503314, 2025; CC BY-SA 4.0). Let `m, d` be positive integers with
`gcd(m, d) = 1` and `ξ = e^{2πi/m}`. Let `r₁, r₂` be integers of multiplicative order exactly `d`
modulo `m` with `gcd(rᵢ - 1, m) = 1`, such that for every integer `k`
`∏_{u=1}^{d-1} (ξ^k - ξ^{k r₁^u})(ξ^k - ξ^{-k r₁^u}) = ∏_{u=1}^{d-1} (ξ^k - ξ^{k r₂^u})(ξ^k - ξ^{-k r₂^u})`.
The asker conjectures that if `d` is odd, then `r₁^c ≡ r₂ (mod m)` for some `c`, i.e. `r₁` and `r₂`
generate the same subgroup of `(ℤ/m)ˣ` (for even `d` the asker lists counterexamples).

`main` states the conjecture for odd `d`. A disproof is such a pair `r₁, r₂` (for some odd `d`) with
`r₂` not a power of `r₁` modulo `m`.

Translation choices:
* `ξ^a` is written `cexp (2 * π * I * a / m)` with `π = Real.pi` and the exponent `a` an integer
  (`k`, `k * rᵢ ^ u` or `-(k * rᵢ ^ u)`), so no complex powers are involved;
* "order exactly `d` modulo `m`" is `orderOf (rᵢ : ZMod m) = d`, and `gcd(rᵢ - 1, m) = 1` is
  `Int.gcd (rᵢ - 1) m = 1`; `m` is a positive natural number, `d` an odd natural number;
* the identity is required for every `k : ℤ`, as in the source;
* the conclusion `r₁^c ≡ r₂ (mod m)` is an equation in `ZMod m` with `c : ℕ`;
* the even-`d` table and the link with lens spaces in the source are not stated.
-/

open Complex Real

namespace OMA.S_mo_503314

/-- For odd `d`, the product identity for all `k` forces `r₂` to be a power of `r₁` modulo `m`. -/
theorem main :
    ∀ (m d : ℕ), 0 < m → Odd d → Nat.Coprime m d → ∀ (r₁ r₂ : ℤ),
      orderOf (r₁ : ZMod m) = d → orderOf (r₂ : ZMod m) = d →
      Int.gcd (r₁ - 1) m = 1 → Int.gcd (r₂ - 1) m = 1 →
      (∀ k : ℤ,
        (∏ u ∈ Finset.Icc 1 (d - 1),
          (cexp (2 * π * I * k / m) - cexp (2 * π * I * (k * r₁ ^ u) / m)) *
          (cexp (2 * π * I * k / m) - cexp (2 * π * I * (-(k * r₁ ^ u)) / m))) =
        ∏ u ∈ Finset.Icc 1 (d - 1),
          (cexp (2 * π * I * k / m) - cexp (2 * π * I * (k * r₂ ^ u) / m)) *
          (cexp (2 * π * I * k / m) - cexp (2 * π * I * (-(k * r₂ ^ u)) / m))) →
      ∃ c : ℕ, (r₁ : ZMod m) ^ c = (r₂ : ZMod m) := by
  sorry

end OMA.S_mo_503314
