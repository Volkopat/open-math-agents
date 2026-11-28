import OMAStatements.S_oeis_a365416

-- Reduction oeis-a365416.R1 of A365416: Numbers k such that 2*k-1 and 2*k+1 are both prime powers (A246655).
-- Credit: @jarrettbranch
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a365416_R1

/-- `2k - 1` a prime square and `2k + 1` a prime power with exponent `≥ 3` forces `k = 13`. -/
def H1 : Prop :=
  ∀ k p q b : ℕ, 1 ≤ k → p.Prime → q.Prime → 3 ≤ b →
    2 * k - 1 = p ^ 2 → 2 * k + 1 = q ^ b → k = 13

/-- `2k - 1` a prime power with exponent `≥ 3` and `2k + 1` a proper prime power forces `k = 13`. -/
def H2 : Prop :=
  ∀ k p a q b : ℕ, 1 ≤ k → p.Prime → q.Prime → 3 ≤ a → 2 ≤ b →
    2 * k - 1 = p ^ a → 2 * k + 1 = q ^ b → k = 13

/-- Two squares never differ by `2`. -/
theorem sq_add_two_ne_sq (p q : ℕ) (hp : 2 ≤ p) (h : p ^ 2 + 2 = q ^ 2) : False := by
  have hlt : p < q := by nlinarith
  have : (p + 1) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hlt 2
  nlinarith

/-- `k = 13` works (`25 = 5^2`, `27 = 3^3`), and both exponents equal to `2` is impossible since
squares never differ by `2`. The remaining exponent patterns are `H1` and `H2`. -/
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a365416.main := by
  intro h1 h2 k hk
  constructor
  · rintro ⟨⟨p, a, hp, ha, hpa⟩, ⟨q, b, hq, hb, hqb⟩⟩
    rcases (show a = 2 ∨ 3 ≤ a by omega) with rfl | ha3
    · rcases (show b = 2 ∨ 3 ≤ b by omega) with rfl | hb3
      · exact (sq_add_two_ne_sq p q hp.two_le (by omega)).elim
      · exact h1 k p q b hk hp hq hb3 hpa hqb
    · exact h2 k p a q b hk hp hq ha3 hb hpa hqb
  · rintro rfl
    exact ⟨⟨5, 2, by norm_num, le_refl _, by norm_num⟩, ⟨3, 3, by norm_num, by norm_num, by norm_num⟩⟩

end OMA.R_oeis_a365416_R1
