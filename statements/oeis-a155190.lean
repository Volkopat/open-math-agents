import Mathlib

/-!
# A155190: Non-triangular numbers having a unique representation as p + t, where p is prime and t is a triangular number.

Source: https://oeis.org/A155190
Credit: @darealpandaboi

Conjecture: the sequence is finite.

Translation notes.
* Triangular numbers are k(k+1)/2 for k >= 0, so 0 is triangular (2 = 2 + 0 is a term).
  A representation is a pair (p, t), p prime, t triangular, p + t = n; since t determines p, the
  representations correspond to the triangular t <= n with n - t prime.
* This reproduces all 41 listed terms 2, 4, 7, ..., 6210, 8316 and finds no other term up to
  200000 (checked by computer).
-/

namespace OMA.S_oeis_a155190

/-- t is a triangular number k(k+1)/2, k >= 0. -/
def IsTriangular (t : ℕ) : Prop := ∃ k : ℕ, t = k * (k + 1) / 2

theorem main :
    {n : ℕ | ¬ IsTriangular n ∧
      ∃! t : ℕ, IsTriangular t ∧ t ≤ n ∧ (n - t).Prime}.Finite := by
  sorry

end OMA.S_oeis_a155190
