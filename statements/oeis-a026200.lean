import Mathlib

/-!
# A026200: a(n) = (s(n) + 2)/3, where s(n) is the n-th number congruent to 1 mod 3 in A026166.

Source: https://oeis.org/A026200
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

The entry (offset 1) states:
  Conjectures from Colin Barker, Oct 14 2019: (Start)
  G.f.: x*(1 + 2*x + 4*x^2 + 6*x^3 + x^4 + 4*x^5 + 2*x^6) / ((1 - x)^2*(1 + x)^2*(1 + x^2)^2).
  a(n) = 2*a(n-4) - a(n-8) for n>8.
  (End)

A026166 (offset 1) is defined there by: a(1) = 1; for n >= 2, let h = floor((n-1)/2),
L = n - h, R = n + h; then a(L) = n if a(L) not yet defined, otherwise a(R) = n.

Modelling choices:
* The process is modelled step by step. `state n` is the partial sequence after the numbers
  1, ..., n have been placed, as a function ℕ → ℕ with 0 meaning not yet defined (all placed
  values are positive). Step n (n >= 2) sets position L to n if it is still 0, otherwise sets
  position R to n (`Function.update`).
* A026166(p) is read off as `state (2 * p) p`. This is the final value at position p: a step n
  writes only at L = n - floor((n-1)/2) >= (n+1)/2 or at R = n + floor((n-1)/2) >= n, so no step
  n >= 2p touches position p.
* s(n), the n-th term of A026166 congruent to 1 mod 3 (in the order of A026166), is
  A026166(p) where p is the n-th position (counting from 1) with A026166(p) ≡ 1 (mod 3); this
  uses `Nat.nth` on the set of positions p >= 1 with A026166(p) % 3 = 1, which is indexed from 0.
  Then a(n) = (s(n) + 2)/3 with natural-number division (s(n) ≡ 1 mod 3, so it is exact).
* The g.f. is stated as an identity of formal power series over ℚ for Sum_{n>=1} a(n) x^n
  (offset 1, so the coefficient of x^0 is 0), multiplied out by the denominator. The recurrence is
  stated for n > 8 in ℤ (it has a minus sign).
-/

namespace OMA.S_oeis_a026200

/-- The partial sequence before any step: only a(1) = 1 is defined (0 means undefined). -/
def init : ℕ → ℕ := fun p => if p = 1 then 1 else 0

/-- Step n of the A026166 process applied to the partial sequence f: with h = floor((n-1)/2),
put n at position n - h if that position is still undefined, otherwise at position n + h. -/
def step (n : ℕ) (f : ℕ → ℕ) : ℕ → ℕ :=
  if f (n - (n - 1) / 2) = 0 then Function.update f (n - (n - 1) / 2) n
  else Function.update f (n + (n - 1) / 2) n

/-- The partial sequence after the numbers 1, ..., n have been placed. -/
def state : ℕ → ℕ → ℕ
  | 0 => init
  | 1 => init
  | n + 2 => step (n + 2) (state (n + 1))

/-- A026166(p) for p >= 1 (no step after 2p - 1 changes position p). -/
def A026166 (p : ℕ) : ℕ := state (2 * p) p

/-- s(n): the n-th term (n >= 1) of A026166 that is congruent to 1 mod 3, in the order of
A026166. -/
noncomputable def s (n : ℕ) : ℕ :=
  A026166 (Nat.nth (fun p => 1 ≤ p ∧ A026166 p % 3 = 1) (n - 1))

/-- A026200: a(n) = (s(n) + 2)/3. -/
noncomputable def a (n : ℕ) : ℕ := (s n + 2) / 3

/-- Barker's conjectured g.f. and recurrence for A026200. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) ^ 2 * (1 + PowerSeries.X ^ 2) ^ 2) =
      PowerSeries.X * (1 + 2 * PowerSeries.X + 4 * PowerSeries.X ^ 2 + 6 * PowerSeries.X ^ 3 +
        PowerSeries.X ^ 4 + 4 * PowerSeries.X ^ 5 + 2 * PowerSeries.X ^ 6) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 2 * a (n - 4) - a (n - 8) := by
  sorry

end OMA.S_oeis_a026200
