import FormalConjectures.ErdosProblems.«680»
import Mathlib

-- Reduction Erdos680.erdos_680.parts.i.R1 of Erdős Problem 680 — i
-- Credit: @rickmanelius
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 680 (i): the two residue classes left after the shifts `1` and `2`

The target asks that every large `n` have a shift `k ≥ 1` such that every prime factor of `n + k`
exceeds `k^2 + 1`.

Proved below, with no hypothesis:

* `witness_bound`: a witness `k` for `n` satisfies `k^2 + 1 < n + k`, and when `n + k` is
  composite even `(k^2 + 1)^2 < n + k`. A witness is therefore a prime `n + k` with `k` below about
  `√n`, or a composite `n + k` with `k` below about `n^(1/4)`.
* `even_case`: for even `n ≥ 2` the shift `1` works, since `n + 1` is odd.
* `odd_case`: for odd `n` with `n + 2` prime to `3` and to `5` the shift `2` works, since then
  `n + 2` has no prime factor up to `5 = 2^2 + 1`.

Every `n` outside two residue classes is covered: for odd `n`, the shift `2` fails exactly when
`3 ∣ n + 2` (that is `n ≡ 1 (mod 6)`) or `5 ∣ n + 2` (that is `n ≡ 3 (mod 10)`). Both hypotheses
are special cases of the target, one per class. A direct search up to `10^6` (reported to
`5 × 10^6` on the desk) finds exactly eight `n` without a witness: `1, 7, 13, 31, 115` in the
class `1 mod 6` and `3, 13, 23, 113` in the class `3 mod 10` (`13` lies in both).

* `H1`: every large `n ≡ 1 (mod 6)` has a witness.
* `H2`: every large `n ≡ 3 (mod 10)` has a witness.
-/

namespace OMA.R_Erdos680_erdos_680_parts_i_R1

open Filter

/-- Every large `n ≡ 1 (mod 6)` has a shift `k ≥ 1` with every prime factor of `n + k` above
`k^2 + 1`. -/
def H1 : Prop :=
  ∀ᶠ n : ℕ in atTop, n % 6 = 1 → ∃ k ≠ 0, (n + k).minFac > k ^ 2 + 1

/-- Every large `n ≡ 3 (mod 10)` has a shift `k ≥ 1` with every prime factor of `n + k` above
`k^2 + 1`. -/
def H2 : Prop :=
  ∀ᶠ n : ℕ in atTop, n % 10 = 3 → ∃ k ≠ 0, (n + k).minFac > k ^ 2 + 1

/-- The shape of a witness: `k^2 + 1 < n + k`, and `(k^2 + 1)^2 < n + k` when `n + k` is
composite. -/
lemma witness_bound {n k : ℕ} (hk : 0 < k) (h : (n + k).minFac > k ^ 2 + 1) :
    k ^ 2 + 1 < n + k ∧ (¬ (n + k).Prime → (k ^ 2 + 1) ^ 2 < n + k) := by
  have hpos : 0 < n + k := by omega
  have hle : (n + k).minFac ≤ n + k := Nat.minFac_le hpos
  refine ⟨by omega, fun hc => ?_⟩
  have hsq : (n + k).minFac ^ 2 ≤ n + k := Nat.minFac_sq_le_self hpos hc
  have h2 : (k ^ 2 + 1) ^ 2 < (n + k).minFac ^ 2 := Nat.pow_lt_pow_left h (by norm_num)
  omega

/-- A number prime to `2`, `3` and `5`, other than `1`, has least prime factor above `5`. -/
lemma minFac_gt_five {m : ℕ} (hm : m ≠ 1) (h2 : m % 2 = 1) (h3 : m % 3 ≠ 0) (h5 : m % 5 ≠ 0) :
    5 < m.minFac := by
  have hp := Nat.minFac_prime hm
  have hd := Nat.minFac_dvd m
  by_contra hle
  push Not at hle
  have h2le := hp.two_le
  interval_cases hq : m.minFac
  · omega
  · omega
  · exact absurd hp (by norm_num)
  · omega

/-- For even `n ≥ 2` the shift `1` is a witness. -/
lemma even_case {n : ℕ} (hn : 2 ≤ n) (he : n % 2 = 0) : (n + 1).minFac > 1 ^ 2 + 1 := by
  have hp := Nat.minFac_prime (show n + 1 ≠ 1 by omega)
  have hd := Nat.minFac_dvd (n + 1)
  have h2le := hp.two_le
  by_contra hle
  push Not at hle
  have h2 : (n + 1).minFac = 2 := by simp at hle; omega
  rw [h2] at hd
  omega

/-- For odd `n` with `n + 2` prime to `3` and to `5`, the shift `2` is a witness. -/
lemma odd_case {n : ℕ} (ho : n % 2 = 1) (h3 : (n + 2) % 3 ≠ 0) (h5 : (n + 2) % 5 ≠ 0) :
    (n + 2).minFac > 2 ^ 2 + 1 := by
  have := minFac_gt_five (m := n + 2) (by omega) (by omega) h3 h5
  norm_num
  exact this

theorem main : H1 → H2 → type_of% @Erdos680.erdos_680.parts.i := by
  intro h1 h2
  filter_upwards [h1, h2, eventually_ge_atTop 2] with n hn1 hn2 hn
  rcases Nat.even_or_odd n with he | ho
  · exact ⟨1, one_ne_zero, even_case hn (Nat.even_iff.1 he)⟩
  · have ho' : n % 2 = 1 := Nat.odd_iff.1 ho
    by_cases h6 : n % 6 = 1
    · exact hn1 h6
    by_cases h10 : n % 10 = 3
    · exact hn2 h10
    refine ⟨2, two_ne_zero, odd_case ho' ?_ ?_⟩
    · omega
    · omega

end OMA.R_Erdos680_erdos_680_parts_i_R1
