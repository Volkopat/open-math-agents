import Mathlib

/-!
# Is `n^{n-1} + (-1)^{n+1} (n-1)^{n-1}` a squarefree number?

Source: https://mathoverflow.net/questions/261486
Credit: @koolkao

Question (user6671, MathOverflow 261486, 2017; CC BY-SA 3.0). I am trying to prove that
`f(x) = x^n + nx + n` has Galois group `S_n` over the rationals. The discriminant of this
polynomial is `Δ = (-1)^{n(n-1)/2} n^n (-(n-1)^{n-1} + (-1)^n n^{n-1})`. […] It seems that the factor
`d = n^{n-1} + (-1)^{n+1}(n-1)^{n-1}` of the discriminant is always a squarefree number, hence the
question. […] Edit: As it turns out when asking questions, I found a counterexample for `n = 29`
and `n = 47`. In this cases `d` is nearly a squarefree number, meaning that there is a prime `q`
with `v_q(d) = 2`. Hence my modified questions are: 1) Does the argument of Serre imply that
`v_q(d) ≤ 2` for each prime `q` dividing `d`? 2) How does one prove, that the `Gal(f) = S_n` over
the rationals?

The original question (is `d` always squarefree?) is answered negatively in the question itself,
by the asker's counterexamples `n = 29` and `n = 47`. `main` states the mathematical claim behind
modified question 1: for every `n ≥ 2` and every prime `q`, `v_q(d) ≤ 2`. A disproof is a
counterexample.

Translation choices:
* `d(n) = n^{n-1} + (-1)^{n+1}(n-1)^{n-1}` is computed in `ℤ`, for `n ≥ 2` (the source is about
  polynomials `x^n + nx + n` of degree at least `2`);
* `v_q(d) ≤ 2` is stated as `¬ q^3 ∣ d(n)`. These agree because `d(n) ≠ 0` (one of `n^{n-1}` and
  `(n-1)^{n-1}` is even and the other odd);
* not formalized: whether Serre's inertia argument "implies" the bound (a question about an
  argument rather than a mathematical statement; `main` states the bound itself), and question 2
  (how to prove that the Galois group is `S_n`).
-/

namespace OMA.S_mo_261486

/-- `d(n) = n^{n-1} + (-1)^{n+1} (n-1)^{n-1}`. -/
def d (n : ℕ) : ℤ := (n : ℤ) ^ (n - 1) + (-1) ^ (n + 1) * ((n : ℤ) - 1) ^ (n - 1)

/-- For every `n ≥ 2` and every prime `q`, `v_q(d(n)) ≤ 2`, i.e. `q^3 ∤ d(n)`. -/
theorem main : ∀ n : ℕ, 2 ≤ n → ∀ q : ℕ, q.Prime → ¬ ((q : ℤ) ^ 3 ∣ d n) := by
  sorry

end OMA.S_mo_261486
