import Mathlib

/-!
# Few subsequence sums in Z_n x Z_n

Source: https://www.openproblemgarden.org/op/limiting_subsequence_sums_in_z_n_x_z_n
Credit: @ishaanzee

**Conjecture** (B. Bollobás, I. Leader). For every `0 ≤ t ≤ n - 1`, the sequence in `ℤ_n²`
consisting of `n - 1` copies of `(1, 0)` and `t` copies of `(0, 1)` has the fewest number of
distinct subsequence sums over all zero-free sequences from `ℤ_n²` of length `n - 1 + t`.

Definition: given a sequence `a` of elements of an additive abelian group, a subsequence sum is
any group element expressible as the sum of some nontrivial (nonempty) subsequence of `a`; `a` is
zero-free if `0` is not a subsequence sum.

Formalization: `n ≥ 1`; a sequence of length `ℓ = n - 1 + t` is `a : Fin ℓ → ZMod n × ZMod n`, its
nonempty subsequences are the nonempty `I : Finset (Fin ℓ)`, and its set of subsequence sums is
the image of `I ↦ ∑ i ∈ I, a i`. The special sequence takes the value `(1, 0)` at the first
`n - 1` positions and `(0, 1)` at the remaining `t`. (It is itself zero-free.)
-/

namespace OMA.S_opg_limiting_subsequence_sums_in_z_n_x_z_n

/-- The set of subsequence sums (sums over nonempty sets of positions) of `a`. -/
def subseqSums {G : Type*} [AddCommMonoid G] [DecidableEq G] {ℓ : ℕ} (a : Fin ℓ → G) : Finset G :=
  (Finset.univ.powerset.filter fun I : Finset (Fin ℓ) => I.Nonempty).image fun I => ∑ i ∈ I, a i

/-- The sequence of `n - 1` copies of `(1, 0)` followed by `t` copies of `(0, 1)`. -/
def special (n t : ℕ) : Fin (n - 1 + t) → ZMod n × ZMod n :=
  fun i => if (i : ℕ) < n - 1 then (1, 0) else (0, 1)

/-- **Bollobás–Leader conjecture**: among zero-free sequences of length `n - 1 + t` in `ℤ_n²`,
the special sequence has the fewest distinct subsequence sums. -/
theorem main : ∀ n t : ℕ, 1 ≤ n → t ≤ n - 1 → ∀ a : Fin (n - 1 + t) → ZMod n × ZMod n,
    0 ∉ subseqSums a → (subseqSums (special n t)).card ≤ (subseqSums a).card := by
  sorry

end OMA.S_opg_limiting_subsequence_sums_in_z_n_x_z_n
