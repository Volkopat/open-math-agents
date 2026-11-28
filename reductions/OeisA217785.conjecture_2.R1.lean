import FormalConjectures.OEIS.«217785»

/-!
Reduction OeisA217785.conjecture_2.R1 of Smallest integer s > n such that
1 + 2s + 3s^2 + ... + n s^{n-1} is prime, conjecture 2.

The target asks, for every n ≥ 2, for some m < 12 n² with a n = some m. The two stages are
independent:

* H1 is the transfer lemma through the `Option`/`sInf` encoding: once a witness s > n with
  `polyP n s` prime and s < 12 n² is given, the least such witness is at most s, so `a n` is
  `some m` with m < 12 n².
* H2 is the open arithmetic core: for every n ≥ 2 there is a prime value `polyP n s` with
  n < s < 12 n².

The main proof only passes the H2 witness to H1.
-/

namespace OMA.R_OeisA217785_conjecture_2_R1

open OeisA217785

/-- Transfer lemma: a witness s > n with `polyP n s` prime and s < 12 n² yields a value
m < 12 n² with `a n = some m`, via the least-witness `sInf`. -/
def H1 : Prop :=
  ∀ (n s : ℕ), 2 ≤ n → n < s → Nat.Prime (polyP n s) → s < 12 * n ^ 2 →
    ∃ m < 12 * n ^ 2, a n = some m

/-- Open arithmetic core: for every n ≥ 2, `polyP n s` is prime for some s with
n < s < 12 n². -/
def H2 : Prop :=
  ∀ (n : ℕ), 2 ≤ n →
    ∃ s : ℕ, n < s ∧ s < 12 * n ^ 2 ∧ Nat.Prime (polyP n s)

theorem main : H1 → H2 → type_of% @OeisA217785.conjecture_2 := by
  intro h1 h2 n hn
  obtain ⟨s, hns, hbound, hprime⟩ := h2 n hn
  exact h1 n s hn hns hprime hbound

end OMA.R_OeisA217785_conjecture_2_R1
