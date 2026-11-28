import FormalConjectures.OEIS.«7918»

-- Reduction OeisA7918.conjecture1.R1 of Least prime ≥ n — conjecture1
-- Credit: @mbilenko03

/-!
# Least prime `≥ n` as the start of the earliest `n`-term prime progression

Write `S n` for the set of first terms `p₀` of `n`-term arithmetic progressions of primes with
positive difference. The conjecture says `a n = sInf (S n)`.

* `H1` (elementary): every `p₀ ∈ S n` is at least `a n`. Indeed `p₀` is prime (the term `k = 0`),
  and if `p₀ < n` then the term `k = p₀` equals `p₀ * (1 + d)`, which is not prime; so
  `n ≤ p₀` and `a n ≤ p₀`.
* `H2` (open core): for every `n > 0` there is an `n`-term progression of primes with positive
  difference that starts at `a n`, the least prime `≥ n`. This follows from the prime
  `k`-tuples conjecture; the Green–Tao theorem does not fix the first term.

`main` combines the two with `csInf`.
-/

namespace OMA.R_OeisA7918_conjecture1_R1

open OeisA7918

/-- Elementary: a first term of an `n`-term prime progression with positive difference is at
least the least prime `≥ n`. -/
def H1 : Prop :=
  ∀ n p0 d : ℕ, 0 < n → isApOfNPrimes n p0 d → a n ≤ p0

/-- Open core: the least prime `≥ n` starts an `n`-term progression of primes with positive
difference. -/
def H2 : Prop :=
  ∀ n : ℕ, 0 < n → ∃ d : ℕ, isApOfNPrimes n (a n) d

theorem main : H1 → H2 → type_of% @OeisA7918.conjecture1 := by
  intro h1 h2 n hn
  obtain ⟨d, hd⟩ := h2 n hn
  apply le_antisymm
  · refine le_csInf (s := {p0 : ℕ | ∃ d : ℕ, isApOfNPrimes n p0 d}) ⟨a n, d, hd⟩ ?_
    rintro p0 ⟨d', hd'⟩
    exact h1 n p0 d' hn hd'
  · exact Nat.sInf_le ⟨d, hd⟩

end OMA.R_OeisA7918_conjecture1_R1
