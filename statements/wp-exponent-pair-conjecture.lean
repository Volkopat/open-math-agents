import Mathlib

/-!
# Exponent pair conjecture

Source: https://en.wikipedia.org/wiki/Van_der_Corput's_method#Exponent_pairs
Credit: @mwhuss

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source defines: fix parameters $N$, $R$, $T$, $s$, $\delta$; consider functions $f$ on $[N, 2N]$
which are $R$ times continuously differentiable, satisfying
$|f^{(r+1)}(x) - (-1)^r s(s+1)\cdots(s+r) T x^{-s-r}| \le \delta\, s(s+1)\cdots(s+r) T x^{-s-r}$
uniformly on the interval for $0 \le r < R$. A pair $(k, l)$ with $0 \le k \le 1/2 \le l \le 1$ is an
*exponent pair* if for each $\sigma > 0$ there exists $\delta$ and $R$ depending on $k, l, \sigma$
such that $|\sum_{n=a}^{b} e(f(n))| \ll (T/N^{\sigma})^k N^l$ uniformly in $f$, where $e(x) = e^{2\pi i x}$.
The exponent pair conjecture: for all $\varepsilon > 0$, the pair $(\varepsilon, 1/2 + \varepsilon)$
is an exponent pair. Since the definition requires $k \le 1/2 \le l$, the content is $0 < \varepsilon \le 1/2$.
-/

namespace OMA.S_wp_exponent_pair_conjecture

open scoped BigOperators
open Finset Set

noncomputable section

/-- $s(s+1)\cdots(s+r)$, the product appearing in the source's derivative bounds. -/
def rising (s : ℝ) (r : ℕ) : ℝ := ∏ i ∈ Finset.range (r + 1), (s + i)

/-- $e(x) = \exp(2\pi i x)$, as in the source. -/
def e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/--
The class of phase functions the source fixes: $f$ is $R$ times continuously differentiable on
$[N, 2N]$ and for every $x \in [N, 2N]$ and every $r < R$,
$|f^{(r+1)}(x) - (-1)^r \cdot s(s+1)\cdots(s+r) \cdot T \cdot x^{-s-r}|
\le \delta \cdot s(s+1)\cdots(s+r) \cdot T \cdot x^{-s-r}$.
-/
def Admissible (R : ℕ) (s T δ N : ℝ) (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ R f (Icc N (2 * N)) ∧
  ∀ x ∈ Icc N (2 * N), ∀ r : ℕ, r < R →
    ‖iteratedDeriv (r + 1) f x - (-1 : ℝ) ^ r * rising s r * T * x ^ (-s - (r : ℝ))‖ ≤
      δ * rising s r * T * x ^ (-s - (r : ℝ))

/--
The source's definition of exponent pair: $0 \le k \le 1/2 \le l \le 1$ and for each $\sigma > 0$
there exist $\delta$ and $R$ (depending on $k, l, \sigma$) such that
$|\sum_{n=a}^{b} e(f(n))| \ll (T/N^{\sigma})^k N^l$ uniformly in $f$ — written out: there is a
constant $C > 0$ such that for all $N \ge 1$, $T \ge 1$, $s > 0$, all integer intervals
$[a, b] \subseteq [N, 2N]$ and all admissible $f$, the bound holds.
-/
def IsExponentPair (k l : ℝ) : Prop :=
  0 ≤ k ∧ k ≤ 1/2 ∧ (1 / 2 : ℝ) ≤ l ∧ l ≤ 1 ∧
  ∀ σ : ℝ, 0 < σ →
    ∃ δ : ℝ, 0 < δ ∧ ∃ R : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (N T s : ℝ) (a b : ℤ) (f : ℝ → ℝ),
        1 ≤ N → 1 ≤ T → 0 < s →
        N ≤ (a : ℝ) → (b : ℝ) ≤ 2 * N → a ≤ b →
        Admissible R s T δ N f →
        ‖∑ n ∈ Finset.Icc a b, e (f n)‖ ≤ C * (T / N ^ σ) ^ k * N ^ l

/--
The exponent pair conjecture (source): "for all $\varepsilon > 0$, the pair
$(\varepsilon, 1/2 + \varepsilon)$ is an exponent pair". The definition of exponent pair
requires $0 \le k \le 1/2 \le l \le 1$, so the statement ranges over $0 < \varepsilon \le 1/2$.
-/
theorem main : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → IsExponentPair ε (1 / 2 + ε) := by
  sorry

end

end OMA.S_wp_exponent_pair_conjecture
