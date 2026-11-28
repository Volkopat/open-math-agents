import Mathlib

/-!
# The discrete uncertainty principle and entropy

Source: https://mathoverflow.net/questions/490919
Credit: @koolkao

Question (Marcel K. Goh, MathOverflow 490919, 2025; CC BY-SA 4.0). If `G` is a finite abelian
group, `f : G → ℂ` is a function, and `f̂` is its Fourier transform, then
`|supp(f)| · |supp(f̂)| ≥ |G|` (1). This is the discrete Fourier uncertainty principle. Is there a
corresponding inequality for entropies of random variables that would imply the above? If `μ` is a
probability distribution on `G`, and `μ̂` its Fourier transform, then sampling `X` and `Y`
independently with `P{X = a} = μ(a)` and `P{Y = b} = |μ̂(b)| / ‖μ̂‖₁` for all `a, b ∈ G`, I believe
the inequality `H{X} + H{Y} = H{X, Y} ≥ log |G|` (2) would imply the discrete uncertainty principle
(by scaling `f` to be a probability distribution first). But I am not sure if this inequality is
true or not. […] Edit. […] I would still like to know if (2) holds, as some (admittedly small)
computer experiments seem to indicate that it does. Essentially, does one have to define `X` and
`Y` by taking squares of `f(x)` and `f̂(x)` for something like (2) to hold, or does it hold in and
of itself?

`main` states that (2) holds for every finite abelian group `G` and every probability distribution
`μ` on `G`; a disproof is a counterexample.

Translation choices:
* `G` is a finite abelian group written additively (`AddCommGroup`, `Fintype`) in `Type`; every
  finite abelian group is isomorphic to one in `Type`, and (2) is invariant under isomorphism;
* a probability distribution on `G` is a vector of nonnegative weights `μ : G → ℝ` summing to `1`;
* the Fourier transform is `μ̂(ψ) = ∑ₓ μ(x) ψ(x)` for `ψ` in the dual group `AddChar G ℂ` (the
  homomorphisms from `G` to the multiplicative group of `ℂ`; their values lie on the unit circle).
  The source indexes `Y` by `b ∈ G`, that is, it identifies the dual group with `G` by some
  isomorphism; that identification only relabels the values of `Y` and leaves `H{Y}` unchanged, so
  `Y` is indexed by the characters directly. The other sign convention `∑ₓ μ(x) ψ(-x)` also only
  relabels them (`ψ ↦ ψ⁻¹`), and a constant factor in front of `μ̂` (such as `1/|G|`) cancels in
  `|μ̂(b)| / ‖μ̂‖₁`;
* `‖μ̂‖₁ = ∑_ψ |μ̂(ψ)|`. It is at least `|μ̂(0)| = ∑ₓ μ(x) = 1` (`0` is the trivial character), so
  `Y` is a probability distribution and no division by zero occurs;
* `H` is Shannon entropy `-∑ p log p` with `0 log 0 = 0` (`Real.negMulLog`) and the natural
  logarithm. Any base greater than `1` gives an equivalent inequality, since both sides scale by the
  same factor;
* `H{X} + H{Y} = H{X, Y}` in (2) is the identity for independent `X` and `Y`; the question is the
  inequality `H{X} + H{Y} ≥ log |G|`, which involves only the two distributions, and that is what
  `main` states;
* not stated: the implication (2) ⇒ (1), which the source gives as motivation, and the open-ended
  request for "an entropy reason" for (1).

Status: MathOverflow 490919 had no answers in November 2026. (2) can be derived from known
uncertainty principles: from the bound `‖f‖₁ ‖f̂‖₁ ≥ |G| ‖f‖_∞ ‖f̂‖_∞` together with the fact that
Shannon entropy is at least min-entropy, or from the entropic uncertainty principle of
Maassen–Uffink (1988) and Dembo–Cover–Thomas (1991) applied to `μ / ‖μ‖₂`.
-/

namespace OMA.S_mo_490919

/-- Shannon entropy `H(p) = -∑ᵢ p(i) log p(i)` (natural logarithm, `0 log 0 = 0`). -/
noncomputable def entropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

/-- The Fourier transform `μ̂(ψ) = ∑ₓ μ(x) ψ(x)` of `μ : G → ℝ` at a character `ψ` of `G`. -/
noncomputable def fourierHat {G : Type*} [AddCommGroup G] [Fintype G] (μ : G → ℝ)
    (ψ : AddChar G ℂ) : ℂ :=
  ∑ x, (μ x : ℂ) * ψ x

/-- Inequality (2): for `X ~ μ` and `Y ~ |μ̂| / ‖μ̂‖₁`, `H{X} + H{Y} ≥ log |G|`. -/
theorem main :
    ∀ (G : Type) [AddCommGroup G] [Fintype G] (μ : G → ℝ), (∀ x, 0 ≤ μ x) → ∑ x, μ x = 1 →
      Real.log (Fintype.card G) ≤
        entropy μ +
          entropy (fun ψ : AddChar G ℂ =>
            ‖fourierHat μ ψ‖ / ∑ χ : AddChar G ℂ, ‖fourierHat μ χ‖) := by
  sorry

end OMA.S_mo_490919
