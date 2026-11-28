import FormalConjectures.OEIS.«72200»

-- Reduction OeisA72200.conjecture.R1 of Smallest factorial containing exactly $n$ 6's
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Factorials with exactly 24 sixes: the searched range and the open tail

`a n` is the least `k` with exactly `n` sixes among the base-10 digits of `k!`, and `0` when there is
no such `k`. The conjecture is `a 24 = 0`: no `k!` has exactly `24` sixes in its decimal expansion.

The number of sixes in `k!` is not monotone, so the only access to the statement is a search over `k`.
The OEIS entry A072200 says exactly how far that search went: no factorial below `10000` has just
`24` sixes, which is why the entry proposes `a(24) = 0`. Beyond that finite search nothing is known:
the count grows like `k log k / 10`, so `24` sixes is reached early and then passed, and the question
is whether the value `24` is simply skipped.

So the statement splits at the end of the searched range:

* `H1` (searched range): no `k <= 10000` has exactly `24` sixes in `k!`. Finite.
* `H2` (the open tail): no `k > 10000` has exactly `24` sixes in `k!`. Nothing is known here.

Neither hypothesis mentions the target, the other one, or `main`. Since `a` is defined as the least
`k` with the property (and `0` when none exists), `main` is not a plain case split: it shows that no
`k` has the property at all, and then that the `Nat.find` of an empty set is `0`, which is the
`dif_neg` branch of the definition. No upstream lemma is used, so nothing depends on a `decide`-style
proof of an upstream statement.
-/

namespace OMA.R_OeisA72200_conjecture_R1

/-- The searched range: no `k <= 10000` has exactly `24` sixes among the digits of `k!`
(OEIS A072200: no factorial below `10000` contains just `24` sixes). -/
def H1 : Prop :=
  ∀ k : ℕ, k ≤ 10000 → (Nat.digits 10 k.factorial).count 6 ≠ 24

/-- The open tail: no `k > 10000` has exactly `24` sixes among the digits of `k!`. The number of
sixes in `k!` is not monotone, so a skip of the value `24` cannot be ruled out. -/
def H2 : Prop :=
  ∀ k : ℕ, 10000 < k → (Nat.digits 10 k.factorial).count 6 ≠ 24

theorem main : H1 → H2 → type_of% @OeisA72200.conjecture := by
  intro h1 h2
  classical
  have h : ¬ ∃ k : ℕ, (Nat.digits 10 k.factorial).count 6 = 24 := by
    rintro ⟨k, hk⟩
    by_cases hk' : k ≤ 10000
    · exact h1 k hk' hk
    · exact h2 k (Nat.lt_of_not_le hk') hk
  unfold OeisA72200.a
  exact dif_neg h

end OMA.R_OeisA72200_conjecture_R1
