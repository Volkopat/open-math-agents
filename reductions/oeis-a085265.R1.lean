import OMAStatements.S_oeis_a085265

-- Reduction oeis-a085265.R1 of A085265: Numbers that can be written as sum of a positive squarefree number and a positive square.
-- Credit: @luiscampozano
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# A085265: only 1 and 13 are not a positive square plus a positive squarefree number

This file proves outright everything except the two genuinely hard pieces:

* the easy direction: `1` and `13` are not terms (for `13` the only candidates are
  `12 + 1`, `9 + 4`, `4 + 9`, and `12`, `9`, `4` are not squarefree);
* every `n` with `2 ≤ n ≤ 12` is a term, by an explicit witness.

What is left splits into two different kinds of difficulty:

* `H1` is a finite verification, `14 ≤ n < 10 ^ 6`. Numerically the smallest working square
  is tiny (up to `2 · 10 ^ 6` it never needs `k > 14`), so a certificate listing one `k` per `n`
  plus a kernel-checkable squarefreeness test suffices; the difficulty is engineering, since
  `native_decide` is not allowed.
* `H2` is the analytic core, `n ≥ 10 ^ 6`. The smallest working `k` is unbounded (by the
  Chinese remainder theorem one can force `p ^ 2 ∣ n - k ^ 2` for many small `k` at once), so
  this needs a sieve with explicit constants, in the spirit of Estermann (1931): count the
  `k ≤ √(n - 1)` for which some `p ^ 2` divides `n - k ^ 2`, and show this count is smaller than
  the number of all such `k`. If the explicit sieve only works above a larger bound, `H2` can
  itself be split again into a finite range and a tail.

*References:*
- [A085265](https://oeis.org/A085265)
- T. Estermann, Einige Sätze über quadratfreie Zahlen, Math. Ann. 105 (1931).
-/

namespace OMA.R_oeis_a085265_R1

open OMA.S_oeis_a085265

/-- The finite range: every `n` with `14 ≤ n < 10 ^ 6` is a positive squarefree number plus a
positive square. -/
def H1 : Prop :=
  ∀ n : ℕ, 14 ≤ n → n < 10 ^ 6 → IsTerm n

/-- The tail: every `n ≥ 10 ^ 6` is a positive squarefree number plus a positive square. -/
def H2 : Prop :=
  ∀ n : ℕ, 10 ^ 6 ≤ n → IsTerm n

theorem not_squarefree_of_sq_dvd {m p : ℕ} (hp : 2 ≤ p) (h : p * p ∣ m) : ¬ Squarefree m := by
  intro hm
  have hu := hm p h
  rw [Nat.isUnit_iff] at hu
  omega

theorem not_term_one : ¬ IsTerm 1 := by
  rintro ⟨s, k, hs, -, hk, h⟩
  nlinarith

theorem not_term_thirteen : ¬ IsTerm 13 := by
  rintro ⟨s, k, hs, hsq, hk, h⟩
  have hk3 : k ≤ 3 := by nlinarith
  interval_cases k
  · have hs12 : s = 12 := by omega
    subst hs12
    exact not_squarefree_of_sq_dvd (p := 2) le_rfl ⟨3, rfl⟩ hsq
  · have hs9 : s = 9 := by omega
    subst hs9
    exact not_squarefree_of_sq_dvd (p := 3) (by norm_num) ⟨1, rfl⟩ hsq
  · have hs4 : s = 4 := by omega
    subst hs4
    exact not_squarefree_of_sq_dvd (p := 2) le_rfl ⟨1, rfl⟩ hsq

theorem small (n : ℕ) (h2 : 2 ≤ n) (h12 : n ≤ 12) : IsTerm n := by
  interval_cases n
  · exact ⟨1, 1, le_rfl, squarefree_one, le_rfl, rfl⟩
  · exact ⟨2, 1, by norm_num, Nat.prime_two.squarefree, le_rfl, rfl⟩
  · exact ⟨3, 1, by norm_num, Nat.prime_three.squarefree, le_rfl, rfl⟩
  · exact ⟨1, 2, le_rfl, squarefree_one, by norm_num, rfl⟩
  · exact ⟨5, 1, by norm_num, (by norm_num : Nat.Prime 5).squarefree, le_rfl, rfl⟩
  · exact ⟨3, 2, by norm_num, Nat.prime_three.squarefree, by norm_num, rfl⟩
  · exact ⟨7, 1, by norm_num, (by norm_num : Nat.Prime 7).squarefree, le_rfl, rfl⟩
  · exact ⟨5, 2, by norm_num, (by norm_num : Nat.Prime 5).squarefree, by norm_num, rfl⟩
  · exact ⟨1, 3, le_rfl, squarefree_one, by norm_num, rfl⟩
  · exact ⟨2, 3, by norm_num, Nat.prime_two.squarefree, by norm_num, rfl⟩
  · exact ⟨11, 1, by norm_num, (by norm_num : Nat.Prime 11).squarefree, le_rfl, rfl⟩

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a085265.main := by
  intro h1 h2 n hn
  constructor
  · intro ht
    refine ⟨?_, ?_⟩
    · rintro rfl
      exact not_term_one ht
    · rintro rfl
      exact not_term_thirteen ht
  · rintro ⟨hn1, hn13⟩
    by_cases hbig : 14 ≤ n
    · by_cases hb : n < 10 ^ 6
      · exact h1 n hbig hb
      · exact h2 n (by omega)
    · exact small n (by omega) (by omega)

end OMA.R_oeis_a085265_R1
