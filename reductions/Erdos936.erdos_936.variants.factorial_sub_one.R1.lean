import FormalConjectures.ErdosProblems.«936»

-- Reduction Erdos936.erdos_936.variants.factorial_sub_one.R1 of Erdős Problem 936 (n! - 1 case)
-- Source: Cushing and Pascoe, Powerful numbers and the ABC-conjecture, arXiv:1611.01192
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# n! - 1 is powerful only finitely often, from an abc estimate

The factorial-minus-one case of the conditional argument of Cushing and Pascoe, Theorem 4.1 of
*Powerful numbers and the ABC-conjecture* (arXiv:1611.01192). It mirrors the merged reduction
`Erdos936.erdos_936.variants.factorial_add_one.R1` (by @dk8827).

* `H1` (elementary): the square of the radical divides each positive powerful number. This is
  word for word `H1` of `Erdos936.erdos_936.variants.factorial_add_one.R1`.
* `H2` (elementary): factorials eventually dominate every fixed power of the primorial. This is
  word for word `H2` of `Erdos936.erdos_936.variants.factorial_add_one.R1`.
* `H3` (open core): the abc inequality with exponent 3/2 for the triples `(1, n! - 1, n!)`,
  whose radical is `primorial n * rad (n! - 1)`. It is a special case of the abc conjecture with
  `ε = 1/2`, written with integer powers.

`main`: if `c = n! - 1` is powerful then `rad c ^ 2 ≤ c < n!` by `H1`. Squaring `H3` gives
`(n!)^4 ≤ C^2 (primorial n)^6 (rad c)^6 ≤ C^2 (primorial n)^6 (n!)^3`, so
`n! ≤ C^2 (primorial n)^6`, which fails for large `n` by `H2`.
-/

open Finset Filter Nat

namespace OMA.R_Erdos936_erdos_936_variants_factorial_sub_one_R1

/-- The square of the radical divides each positive powerful number. -/
def H1 : Prop :=
  ∀ c : ℕ, 0 < c → c.Powerful → (∏ p ∈ c.primeFactors, p) ^ 2 ∣ c

/-- Factorials eventually dominate every fixed power of the primorial. -/
def H2 : Prop :=
  ∀ C e : ℕ, ∀ᶠ n : ℕ in atTop, C * (primorial n) ^ e < n.factorial

/-- The abc estimate with exponent 3/2 for the triples `(1, n! - 1, n!)`, written with
integer powers. -/
def H3 : Prop :=
  ∃ C : ℕ, ∀ n : ℕ,
    let c := n.factorial - 1
    n.factorial ^ 2 ≤ C * (primorial n * (∏ p ∈ c.primeFactors, p)) ^ 3

theorem main : H1 → H2 → H3 → type_of% @Erdos936.erdos_936.variants.factorial_sub_one := by
  intro radicalSquare growth ⟨C, hABC⟩
  change ∀ᶠ n : ℕ in atTop, ¬ (n.factorial - 1).Powerful
  filter_upwards [growth (C ^ 2) 6, eventually_ge_atTop 2] with n hn hn2
  intro hpower
  let m := n.factorial
  let c := n.factorial - 1
  let r := ∏ p ∈ c.primeFactors, p
  have hm : 0 < m := n.factorial_pos
  have hm2 : 2 ≤ m := hn2.trans n.self_le_factorial
  have hc : 0 < c := by dsimp [c]; omega
  have hcm : c ≤ m := Nat.sub_le _ _
  have hr : r ^ 2 ≤ m := (Nat.le_of_dvd hc (radicalSquare c hc hpower)).trans hcm
  have hABCn : m ^ 2 ≤ C * (primorial n * r) ^ 3 := hABC n
  have hbound : m * m ^ 3 ≤ (C ^ 2 * (primorial n) ^ 6) * m ^ 3 := by
    calc
      m * m ^ 3 = (m ^ 2) ^ 2 := by ring
      _ ≤ (C * (primorial n * r) ^ 3) ^ 2 := Nat.pow_le_pow_left hABCn 2
      _ = (C ^ 2 * (primorial n) ^ 6) * (r ^ 2) ^ 3 := by ring
      _ ≤ (C ^ 2 * (primorial n) ^ 6) * m ^ 3 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hr 3)
  have hcancel := Nat.le_of_mul_le_mul_right hbound (Nat.pow_pos hm)
  exact (not_le_of_gt hn) hcancel

end OMA.R_Erdos936_erdos_936_variants_factorial_sub_one_R1
