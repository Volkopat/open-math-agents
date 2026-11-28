import FormalConjectures.Wikipedia.Gilbreath

-- Reduction Gilbreath.gilbreath_conjecture.R1 of Gilbreath's conjecture
-- Credit: @marcusbuffett

/-!
# Gilbreath's conjecture: the first 500 rows, and the open rest

Start with the primes and repeatedly take absolute differences of neighbours; the conjecture
says that every row after the first begins with `1`.

* `H1`: rows `1` to `500` begin with `1`. Checked inside the Lean kernel from a verified table of
  the first 501 primes.
* `H2`: every later row begins with `1`. This is the open conjecture (Odlyzko verified it for
  about `3.4 * 10 ^ 11` rows; the range here is only what is cheap in the kernel).
-/

namespace OMA.R_Gilbreath_gilbreath_conjecture_R1

/-- The verified range. -/
def H1 : Prop :=
  ∀ k : ℕ+, (k : ℕ) ≤ 500 → Gilbreath.d k 0 = 1

/-- The open part. -/
def H2 : Prop :=
  ∀ k : ℕ+, 500 < (k : ℕ) → Gilbreath.d k 0 = 1

theorem main : H1 → H2 → type_of% @Gilbreath.gilbreath_conjecture := by
  intro h1 h2 k
  by_cases h : (k : ℕ) ≤ 500
  · exact h1 k h
  · exact h2 k (by omega)

end OMA.R_Gilbreath_gilbreath_conjecture_R1
