import Mathlib

/-!
# A challenging problem on disjoint cosets

Zhi-Wei Sun, MathOverflow 316709 (2018): Conjecture 1.2 of Z.-W. Sun, Internat. J. Math. 17 (2006).
Source: https://mathoverflow.net/questions/316709
Credit: @JamesSlash

Conjecture (as stated in the source). Let `G₁, …, G_k` (`k > 1`) be subgroups of a group `G` with all the
indices `[G : Gᵢ]` finite. If the left cosets `a₁G₁, …, a_kG_k` are pairwise disjoint for some
`a₁, …, a_k ∈ G`, then `gcd([G : Gᵢ], [G : Gⱼ]) ≥ k` for some `1 ≤ i < j ≤ k`.

Conventions of this translation:
* the subgroups and the elements are indexed by `Fin k` (the subgroups need not be distinct, as in the source);
* `Subgroup.index H` is `[G : H]`; Mathlib sets it to `0` when the index is infinite, so finite index is
  `(H i).index ≠ 0`;
* the left coset `aH` is the pointwise translate `a • (H : Set G)`;
* pairwise disjointness is `Pairwise` disjointness of these sets (for `i ≠ j`).
-/

namespace OMA.S_mo_316709

open scoped Pointwise

universe u

/-- Sun's disjoint-coset conjecture: among `k > 1` pairwise disjoint left cosets of finite-index subgroups,
two of the indices have greatest common divisor at least `k`. -/
theorem main :
    ∀ (G : Type u) [Group G] (k : ℕ), 1 < k →
      ∀ (H : Fin k → Subgroup G) (a : Fin k → G),
        (∀ i, (H i).index ≠ 0) →
        Pairwise (fun i j => Disjoint (a i • (H i : Set G)) (a j • (H j : Set G))) →
        ∃ i j : Fin k, i < j ∧ k ≤ Nat.gcd (H i).index (H j).index := by
  sorry

end OMA.S_mo_316709
