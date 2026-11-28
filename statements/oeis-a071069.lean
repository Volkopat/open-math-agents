import Mathlib

/-!
# A071069: a(n) = min { A070923(k) | n^3 < k < (n+1)^3 }.

Source: https://oeis.org/A071069
Credit: @ceejcake

Formalizes the Strong Conjecture of OEIS A071069 (offset 1):
For all `n > 12`, `n^2 / 2 < a(n) < n^2`.

Note on truth value:
As already noted in the OEIS comments (Lambert Klasen, Dec 17 2004), this strong conjecture is
false as written: the first counterexample is `n = 23`, where `a(23) = 63` (attained at
`k = 13537`, `568^3 - 13537^2 = 63`), whereas `23^2 / 2 = 264.5`. (The entry also mentions a
separate weak conjecture `a(n) > n`.)

Conventions:
* `a070923 k` is OEIS A070923 (offset 0): the smallest nonnegative value of `x^3 - k^2` over
  `x : ℕ`. Since `k^2 ≤ k^3` for all `k : ℕ` (with `0^2 = 0^3`), the minimum is always attained
  at some `x ≤ k`.
* `a n` (for `n ≥ 1`, offset 1) is the minimum of `a070923 k` over `n^3 < k < (n + 1)^3`.
* Initial values match OEIS A071069 DATA:
  `a(1)..a(12) = 2, 4, 11, 13, 7, 28, 47, 49, 74, 76, 60, 109`, and `a(23) = 63`.
-/

namespace OMA.S_oeis_a071069

/-- OEIS A070923: the smallest value `x^3 - k^2 ≥ 0` over `x : ℕ`. -/
def a070923 (k : ℕ) : ℕ :=
  (((Finset.range (k + 1)).filter (fun x => k ^ 2 ≤ x ^ 3)).image (fun x => x ^ 3 - k ^ 2)).min'
    (by
      refine Finset.Nonempty.image ?_ _
      refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_self k), ?_⟩⟩
      rcases k with _ | k
      · simp
      · exact Nat.pow_le_pow_right (Nat.succ_pos k) (by decide))

/-- OEIS A071069 (offset 1): `a(n) = min { A070923(k) | n^3 < k < (n + 1)^3 }`. -/
def a (n : ℕ) : ℕ :=
  if h : 1 ≤ n then
    ((Finset.Ioo (n ^ 3) ((n + 1) ^ 3)).image a070923).min'
      (by
        refine Finset.Nonempty.image ?_ _
        refine ⟨n ^ 3 + 1, Finset.mem_Ioo.mpr ⟨Nat.lt_succ_self _, ?_⟩⟩
        nlinarith)
  else 0

/-- Strong conjecture of OEIS A071069: for all `n > 12`, `n^2 / 2 < a(n) < n^2`. -/
theorem main : ∀ n : ℕ, 12 < n → (n : ℚ) ^ 2 / 2 < (a n : ℚ) ∧ (a n : ℚ) < (n : ℚ) ^ 2 := by
  sorry

end OMA.S_oeis_a071069
