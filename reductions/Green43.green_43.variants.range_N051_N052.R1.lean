import FormalConjectures.GreensOpenProblems.«43»

-- Reduction Green43.green_43.variants.range_N051_N052.R1 of Green's Problem 43, the range variant
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Green 43 for primes in `[N ^ 0.51, N ^ 0.52)`: only colliding residue classes matter

Sieve `[1, N]` by one residue class `a p` modulo each prime `p` with `N ^ 0.51 ≤ p < N ^ 0.52`.
The target says that the union of these classes has at least `N ^ (1 - ε)` points in `[1, N]`,
for every choice of the classes.

Call a pair of sieving primes `p < q` *colliding* if the classes `a p (mod p)` and `a q (mod q)`
have a common point in `[1, N]`. Since `p * q > N`, they have at most one common point there.

* `H1` is the second moment bound, which is elementary. Let `r n` be the number of sieving primes
  `p` with `n ≡ a p (mod p)`. Then `∑ r n ≥ N ^ (1 - o(1))` by Chebyshev's bound for the number
  of primes, and `∑ (r n) ^ 2` is `∑ r n` plus twice the number of colliding pairs. So by
  Cauchy–Schwarz, if at most `N ^ (1 + ε)` pairs collide, then the union has at least
  `N ^ (1 - 3 * ε)` points. Without the assumption there can be up to `N ^ 1.04` colliding pairs
  and this argument only gives `N ^ 0.96`, which is the known bound.
* `H2` is the open core: the target for those choices of classes with more than `N ^ (1 + ε)`
  colliding pairs. It is a special case of the target, and it is empty for `ε ≥ 0.04`. Classes
  such as `a p = 0` for every `p` have no colliding pair at all, so `H2` leaves out the generic
  choices and keeps the structured ones.

`main` applies both with `ε / 3` and splits on the number of colliding pairs.

Source: B. Green, *100 open problems*, comments to Problem 43.
-/

namespace OMA.R_Green43_green_43_variants_range_N051_N052_R1

open Filter

/-- Second moment bound: with at most `N ^ (1 + ε)` colliding pairs of sieving primes, the sieved
set has at least `N ^ (1 - 3 * ε)` points. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ a : ℕ → ℤ,
    (({pq : ℕ × ℕ | pq.1.Prime ∧ pq.2.Prime ∧ pq.1 < pq.2 ∧
        (N : ℝ) ^ (0.51 : ℝ) ≤ (pq.1 : ℝ) ∧ (pq.2 : ℝ) < (N : ℝ) ^ (0.52 : ℝ) ∧
        ∃ n : ℤ, 1 ≤ n ∧ n ≤ (N : ℤ) ∧ (pq.1 : ℤ) ∣ n - a pq.1 ∧
          (pq.2 : ℤ) ∣ n - a pq.2}.ncard : ℝ) ≤ (N : ℝ) ^ (1 + ε)) →
      (N : ℝ) ^ (1 - 3 * ε) ≤
        Green43.sievedCard N a ((N : ℝ) ^ (0.51 : ℝ)) ((N : ℝ) ^ (0.52 : ℝ))

/-- The open core: the target for classes with more than `N ^ (1 + ε)` colliding pairs. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ a : ℕ → ℤ,
    ((N : ℝ) ^ (1 + ε) < ({pq : ℕ × ℕ | pq.1.Prime ∧ pq.2.Prime ∧ pq.1 < pq.2 ∧
        (N : ℝ) ^ (0.51 : ℝ) ≤ (pq.1 : ℝ) ∧ (pq.2 : ℝ) < (N : ℝ) ^ (0.52 : ℝ) ∧
        ∃ n : ℤ, 1 ≤ n ∧ n ≤ (N : ℤ) ∧ (pq.1 : ℤ) ∣ n - a pq.1 ∧
          (pq.2 : ℤ) ∣ n - a pq.2}.ncard : ℝ)) →
      (N : ℝ) ^ (1 - ε) ≤
        Green43.sievedCard N a ((N : ℝ) ^ (0.51 : ℝ)) ((N : ℝ) ^ (0.52 : ℝ))

theorem main : H1 → H2 → type_of% @Green43.green_43.variants.range_N051_N052 := by
  intro h1 h2 ε hε
  have hε3 : 0 < ε / 3 := by positivity
  filter_upwards [h1 (ε / 3) hε3, h2 (ε / 3) hε3, eventually_ge_atTop 1] with N hN1 hN2 hN a
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  by_cases hE : (({pq : ℕ × ℕ | pq.1.Prime ∧ pq.2.Prime ∧ pq.1 < pq.2 ∧
        (N : ℝ) ^ (0.51 : ℝ) ≤ (pq.1 : ℝ) ∧ (pq.2 : ℝ) < (N : ℝ) ^ (0.52 : ℝ) ∧
        ∃ n : ℤ, 1 ≤ n ∧ n ≤ (N : ℤ) ∧ (pq.1 : ℤ) ∣ n - a pq.1 ∧
          (pq.2 : ℤ) ∣ n - a pq.2}.ncard : ℝ) ≤ (N : ℝ) ^ (1 + ε / 3))
  · have h := hN1 a hE
    have he : 1 - 3 * (ε / 3) = 1 - ε := by ring
    rw [he] at h
    exact h
  · have h := hN2 a (not_le.mp hE)
    refine le_trans ?_ h
    exact Real.rpow_le_rpow_of_exponent_le hN' (by linarith)

end OMA.R_Green43_green_43_variants_range_N051_N052_R1
