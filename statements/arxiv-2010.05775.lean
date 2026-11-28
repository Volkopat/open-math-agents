import Mathlib

/-!
# Sun's 4-4-2-2 Conjecture: $r = aw^4 + bx^4 + y^2 + z^2$ over $\mathbb{Q}$

Source: Z.-W. Sun, *Sums of four rational squares with certain restrictions*,
https://arxiv.org/abs/2010.05775 (Conjecture 6.1, the "4-4-2-2 Conjecture")
Credit: @SulkBash

## The problem (as the source states it)

Conjecture 6.1 (4-4-2-2 Conjecture). Let $a, b \in \mathbb{Z}^+$ with $\gcd(a,b) = 1$. Then each
$r \in \mathbb{Q}_{\ge 0}$ can be written as $aw^4 + bx^4 + y^2 + z^2$ with
$w, x, y, z \in \mathbb{Q}$.

This first assertion is the form quoted in the paper's abstract and in this problem's catalogue
entry. Conjecture 6.1 goes on with a "Moreover" clause on integer representations,
$m^4 n = 2^{4w} + x^4 + y^2 + z^2$ with $m < 2(a+b)$. As printed, that clause omits $a$ and $b$;
Remark 6.1 writes $a 2^{4w} + b x^4 + y^2 + z^2$ instead. `main` states only the first
assertion, which is unambiguous.

## Formalization notes

* $a, b$ range over positive integers with `Nat.Coprime a b`. They are cast to `ℚ` in the
  representation.
* $r$ ranges over nonnegative rationals: `r : ℚ` with `0 ≤ r`.
* The unknowns $w, x, y, z$ are arbitrary rationals, of any sign, as in the source. Signs do not
  matter, since only even powers occur.
* The square terms alone do not suffice: for example $3$ is not a sum of two rational squares, so
  the fourth powers are needed.
-/

namespace OMA.S_arxiv_2010_05775

/-- Sun's 4-4-2-2 Conjecture: for coprime positive integers `a, b`, every nonnegative rational is
`a w⁴ + b x⁴ + y² + z²` with rational `w, x, y, z`. -/
theorem main :
    ∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b →
      ∀ r : ℚ, 0 ≤ r → ∃ w x y z : ℚ, r = a * w ^ 4 + b * x ^ 4 + y ^ 2 + z ^ 2 := by
  sorry

end OMA.S_arxiv_2010_05775
