import Mathlib

/-!
# A093726: Given the infinite continued fraction (1+i)+1/((1+i)+1/((1+i)+...)), where i is the square root of (-1), this is the numerator of the imaginary part of the convergents.

Source: https://oeis.org/A093726
Credit: @agchua

Zhuorui He (Jun 16 2026), in the formula section of A093726:
  Conjecture: a(n)/A093727(n) = A317974(n+1)/A138573(n).

The n-th convergent (n >= 1) of the continued fraction is the value with n partial quotients
1+i, so c(1) = 1+i and c(n+1) = (1+i) + 1/c(n) (examples in the entry: c(2) = (3+i)/2,
c(3) = (8+4i)/5, c(4) = (6+3i)/4, c(5) = (23+11i)/15). Below this is `conv n`, a complex number;
the value `conv 0` is not used. The entry's program takes a(n) as the imaginary part of the
numerator of c(n), and A093727(n) is the denominator of c(n); so c(n) = (A093725(n) +
a(n)*i)/A093727(n) with integers and A093727(n) > 0, and a(n)/A093727(n) is the imaginary part
of c(n). The theorem states the conjecture for every such representation c(n) = (x + y*i)/d with
integers x, y and a positive integer d (y/d is the same for all of them).

A317974 (offset 0): a(n) = 2*(a(n-1)+a(n-2)+a(n-3))-a(n-4) for n >= 4, with initial terms 0,0,1,1.
A138573 (offset 0): a(n) = 2*a(n-1) + 2*a(n-2) + 2*a(n-3) - a(n-4); a(0)=0, a(1)=1, a(2)=2, a(3)=5.
A093726 and A093727 have offset 1, so the claim is for n >= 1.
-/

namespace OMA.S_oeis_a093726

/-- The convergents: conv 1 = 1 + i and conv (n+1) = (1 + i) + 1/conv n; conv 0 is unused. -/
noncomputable def conv : ℕ → ℂ
  | 0 => 0
  | 1 => 1 + Complex.I
  | (n + 2) => (1 + Complex.I) + 1 / conv (n + 1)

/-- A317974: 0, 0, 1, 1, and a(n) = 2*(a(n-1)+a(n-2)+a(n-3))-a(n-4) for n >= 4. -/
def A317974 : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | (n + 4) => 2 * (A317974 (n + 3) + A317974 (n + 2) + A317974 (n + 1)) - A317974 n

/-- A138573: 0, 1, 2, 5, and a(n) = 2*a(n-1) + 2*a(n-2) + 2*a(n-3) - a(n-4) for n >= 4. -/
def A138573 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | (n + 4) => 2 * A138573 (n + 3) + 2 * A138573 (n + 2) + 2 * A138573 (n + 1) - A138573 n

/-- He's conjecture: if c(n) = (x + y*i)/d with d > 0, then y/d = A317974(n+1)/A138573(n). -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∀ (x y : ℤ) (d : ℕ), 0 < d →
    conv n = ((x : ℂ) + (y : ℂ) * Complex.I) / (d : ℂ) →
    (y : ℝ) / (d : ℝ) = (A317974 (n + 1) : ℝ) / (A138573 n : ℝ) := by
  sorry

end OMA.S_oeis_a093726
