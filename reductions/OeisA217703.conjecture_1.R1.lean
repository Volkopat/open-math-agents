import FormalConjectures.OEIS.«217703»

-- Reduction OeisA217703.conjecture_1 of Recurrence $a(n+1) = 2n(n+1)a(n) - n^4 a(n-1)$ and associated polynomials
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The checked range and the open tail for the irreducibility of `S_n`

Sun's conjecture (i) in A217703: the polynomial `S_n`, defined by `S_0 = 1`, `S_1 = x` and
`S_{n+1} = (x + 2 n (n+1)) S_n - n ^ 4 S_{n-1}`, is irreducible over `ℚ` for every `n >= 1`. Its
constant term is the sequence `a(n)` of A217703 (`a(0) = 1`, `a(1) = 0`, `a(2) = -1`,
`a(3) = -12`, `a(4) = -207`, ...), which I checked against the OEIS b-file, so the recurrence used
here is the one the entry means.

Unlike the prime-pattern conjectures, each `S_n` is an explicit polynomial, so for a fixed `n` the
statement is decidable by a finite computation: factor `S_n` over `ℚ` (degree `n`, integer
coefficients). I did this for every `n <= 100` and every factorisation came out with a single
irreducible factor; the cost grows quickly with `n` (degree `n`, coefficients of size about
`(n!)^2`), which is where the checked range ends. The companion conjectures (ii) and (iii) of the
same entry are already disproved, so this one is squarely open.

* `H1` (checked range): every `n` with `1 <= n <= 100` has `S_n` irreducible over `ℚ`. Finite: 100
  exact factorisations over `ℚ`.
* `H2` (the open tail): every `n > 100` has `S_n` irreducible over `ℚ`. This is the whole
  difficulty; nothing beyond the computation is known for general `n`.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split, and no
upstream lemma is used, so nothing depends on a `decide`-style proof of an upstream statement.
-/

namespace OMA.R_OeisA217703_conjecture_1_R1

/-- The checked range: for every `n` with `1 <= n <= 100` the polynomial `S_n` is irreducible over
`ℚ` (exact factorisation over `ℚ` for all 100 polynomials). -/
def H1 : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ 100 →
    Irreducible (Polynomial.map (Int.castRingHom ℚ) (OeisA217703.polyS n))

/-- The open tail: for every `n > 100` the polynomial `S_n` is irreducible over `ℚ`. Nothing is
known here: the polynomials have degree `n` and coefficients of size about `(n!)^2`, so no
computation reaches all `n` and no general argument is known. -/
def H2 : Prop :=
  ∀ n : ℕ, 100 < n →
    Irreducible (Polynomial.map (Int.castRingHom ℚ) (OeisA217703.polyS n))

theorem main : H1 → H2 → type_of% @OeisA217703.conjecture_1 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 100
  · exact h1 n hn h
  · exact h2 n (Nat.lt_of_not_le h)

end OMA.R_OeisA217703_conjecture_1_R1
