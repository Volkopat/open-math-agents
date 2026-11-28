import Mathlib

/-!
# A218263: Mathar's recurrence

Source: https://oeis.org/A218263
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A218263 (offset 3): number of standard Young tableaux of n cells and height >= 3;
data 1, 4, 16, 56, 197, 694, 2494, 9244, 35234, 139228, 566788, 2387048, ...

Conjecture (R. J. Mathar, Jan 04 2017):
(n-6)*(n-3)*(n+1)*a(n) +(-n^3+6*n^2+11*n-36)*a(n-1) -(n-1)*(n^3-4*n^2-21*n+76)*a(n-2)
+2*(n-1)*(n-2)*(3*n-19)*a(n-3) +4*(n-5)*(n-1)*(n-2)*(n-3)*a(n-4) = 0.

Formalization: the entry gives the formula a(n) = A000085(n) - A001405(n), and this formula is used as
the definition here. A001405(n) = binomial(n, floor(n/2)) (its definition; `n / 2` is the floor
division of natural numbers), and A000085 (the number of involutions of n elements) is given in its
entry by a(0) = a(1) = 1, a(n) = a(n-1) + (n-1)*a(n-2) for n > 1. `main` is stated for every
I : ℕ → ℚ with I(0) = I(1) = 1 and this recurrence (these conditions determine I = A000085), for
a(n) = I(n) - binomial(n, floor(n/2)); this gives a(0) = a(1) = a(2) = 0 and a(3) = 1. The sequence has
offset 3 and the recurrence involves a(n-4), so every index is at least the offset for n ≥ 7. `main`
is stated for n ≥ 4, with a(0) = a(1) = a(2) = 0 as given by the formula; this includes every n ≥ 7.
It is checked by the data, for example at n = 7:
(32)*(197) + (-8)*(56) + (-456)*(16) + (120)*(4) + (960)*(1) = 0.
-/

namespace OMA.S_oeis_a218263

/-- Mathar's conjectured recurrence for A218263, a(n) = A000085(n) - A001405(n), for n ≥ 4. -/
theorem main : ∀ I : ℕ → ℚ, I 0 = 1 →
    I 1 = 1 →
    (∀ n : ℕ, 2 ≤ n → I n = I (n - 1) + ((n : ℚ) - 1) * I (n - 2)) →
    ∀ a : ℕ → ℚ, (∀ n : ℕ, a n = I n - (n.choose (n / 2) : ℚ)) →
    ∀ n : ℕ, 4 ≤ n →
      ((n : ℚ) - 6) * ((n : ℚ) - 3) * ((n : ℚ) + 1) * a n +
        (-(n : ℚ) ^ 3 + 6 * (n : ℚ) ^ 2 + 11 * (n : ℚ) - 36) * a (n - 1) -
        ((n : ℚ) - 1) * ((n : ℚ) ^ 3 - 4 * (n : ℚ) ^ 2 - 21 * (n : ℚ) + 76) * a (n - 2) +
        2 * ((n : ℚ) - 1) * ((n : ℚ) - 2) * (3 * (n : ℚ) - 19) * a (n - 3) +
        4 * ((n : ℚ) - 5) * ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a218263
