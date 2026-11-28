import Mathlib

/-!
# A filtered map between filtered spaces with expansions inducing an isomorphism on `gr`

Source: https://mathoverflow.net/questions/273275
Credit: @koolkao

Question (Joel Kamnitzer, MathOverflow 273275, 2017; CC BY-SA 4.0). Let `V` be a vector space with
a decreasing filtration `V = F_0 V ⊇ F_1 V ⊇ F_2 V ⊇ ⋯`, and `gr V := ⊕_k F_k V / F_{k+1} V`.
We say that `V` admits an expansion if there are subspaces `W_k ⊆ F_k V` such that
`F_k V = W_k ⊕ F_{k+1} V` and `V = ⊕_k W_k`. Let `V`, `W` be two filtered vector spaces which
admit expansions. Suppose that `φ : V → W` is a filtration-preserving map such that
`gr φ : gr V → gr W` is an isomorphism. Can I conclude that `φ` is an isomorphism?

`main` states that the answer is yes. A disproof is such a pair of filtered spaces with
expansions and a filtration-preserving linear map inducing an isomorphism on `gr` that is not
bijective.

Translation choices:
* the spaces are modules over a field `K` (types in `Type`); a filtration is an antitone family
  `F : ℕ → Submodule K V` with `F 0 = ⊤`;
* "admits an expansion" is the source's equivalent form: subspaces `E k ≤ F k` with
  `E k ⊔ F (k + 1) = F k` and `Disjoint (E k) (F (k + 1))` (the direct sum
  `F_k V = W_k ⊕ F_{k+1} V`) and `DirectSum.IsInternal E` (`V = ⊕_k W_k`);
* `φ` is `K`-linear and filtration-preserving (`φ (F_k V) ⊆ F_k W`);
* `gr φ` is an isomorphism exactly when each graded piece
  `F_k V / F_{k+1} V → F_k W / F_{k+1} W` is bijective; this is stated elementwise:
  `v ∈ F_k V` and `φ v ∈ F_{k+1} W` imply `v ∈ F_{k+1} V` (injectivity), and every
  `w ∈ F_k W` is `φ v` modulo `F_{k+1} W` for some `v ∈ F_k V` (surjectivity);
* "`φ` is an isomorphism" is `Function.Bijective φ`; the source's first question (other names
  for the property) is not stated.
-/

namespace OMA.S_mo_273275

/-- A filtration-preserving linear map between filtered vector spaces admitting expansions,
whose associated graded map is an isomorphism, is bijective. -/
theorem main :
    ∀ (K V W : Type) [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
      (FV : ℕ → Submodule K V) (FW : ℕ → Submodule K W),
      FV 0 = ⊤ → Antitone FV → FW 0 = ⊤ → Antitone FW →
      (∃ E : ℕ → Submodule K V, (∀ k, E k ≤ FV k ∧ E k ⊔ FV (k + 1) = FV k ∧
        Disjoint (E k) (FV (k + 1))) ∧ DirectSum.IsInternal E) →
      (∃ E : ℕ → Submodule K W, (∀ k, E k ≤ FW k ∧ E k ⊔ FW (k + 1) = FW k ∧
        Disjoint (E k) (FW (k + 1))) ∧ DirectSum.IsInternal E) →
      ∀ φ : V →ₗ[K] W, (∀ k, ∀ v ∈ FV k, φ v ∈ FW k) →
        (∀ k, ∀ v ∈ FV k, φ v ∈ FW (k + 1) → v ∈ FV (k + 1)) →
        (∀ k, ∀ w ∈ FW k, ∃ v ∈ FV k, w - φ v ∈ FW (k + 1)) →
        Function.Bijective φ := by
  sorry

end OMA.S_mo_273275
