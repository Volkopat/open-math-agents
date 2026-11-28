import OMAStatements.S_oeis_a230563
import Mathlib.Tactic

-- Credit: @FransDevelopment
-- Every exponent at least seven is a multiple of a minimal exponent.
-- Powering each base transfers ordered triples injectively to that exponent.
namespace OMA.R_oeis_a230563_R1

/-- Uniqueness at prime exponents at least seven. -/
def H1 : Prop := ∀ p : ℕ, p.Prime → 7 ≤ p → ∀ x y z u v w : ℕ,
    0 < x → x ≤ y → y ≤ z → 0 < u → u ≤ v → v ≤ w →
    x ^ p + y ^ p + z ^ p = u ^ p + v ^ p + w ^ p → (x, y, z) = (u, v, w)

/-- Uniqueness at the six composite exponents whose proper divisors are all below seven. -/
def H2 : Prop := ∀ d ∈ ([8, 9, 10, 12, 15, 25] : List ℕ), ∀ x y z u v w : ℕ,
    0 < x → x ≤ y → y ≤ z → 0 < u → u ≤ v → v ≤ w →
    x ^ d + y ^ d + z ^ d = u ^ d + v ^ d + w ^ d → (x, y, z) = (u, v, w)

theorem exponent_divisor (n : ℕ) (hn : 7 ≤ n) :
    ∃ d, d ∣ n ∧ ((d.Prime ∧ 7 ≤ d) ∨ d ∈ ([8, 9, 10, 12, 15, 25] : List ℕ)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n ≤ 36
    · have table : ∀ k : Fin 37, 7 ≤ k.val → ∃ j : Fin 37, j.val ∣ k.val ∧
          ((j.val.Prime ∧ 7 ≤ j.val) ∨ j.val ∈ ([8, 9, 10, 12, 15, 25] : List ℕ)) := by decide
      obtain ⟨j, hj⟩ := table ⟨n, by omega⟩ hn
      exact ⟨j.val, hj⟩
    by_cases prime : n.Prime
    · exact ⟨n, dvd_refl _, Or.inl ⟨prime, hn⟩⟩
    obtain ⟨a, b, ha, hb, hab⟩ := (Nat.not_prime_iff_exists_mul_eq (by omega : 2 ≤ n)).mp prime
    by_cases large : 7 ≤ a
    · obtain ⟨d, hd, hkind⟩ := ih a ha large
      exact ⟨d, dvd_trans hd ⟨b, hab.symm⟩, hkind⟩
    have lb : 7 ≤ b := by
      by_contra! h
      have := Nat.mul_le_mul (by omega : a ≤ 6) (by omega : b ≤ 6)
      omega
    obtain ⟨d, hd, hkind⟩ := ih b hb lb
    exact ⟨d, dvd_trans hd ⟨a, by simpa [Nat.mul_comm] using hab.symm⟩, hkind⟩

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a230563.main := by
  intro primes composites n hn x y z u v w hx hxy hyz hu huv hvw he
  obtain ⟨d, ⟨k, hk⟩, hkind⟩ := exponent_divisor n hn
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; omega
  have lift : (x ^ k) ^ d + (y ^ k) ^ d + (z ^ k) ^ d =
      (u ^ k) ^ d + (v ^ k) ^ d + (w ^ k) ^ d := by
    simpa only [← pow_mul, Nat.mul_comm k d, ← hk] using he
  have at_d : ∀ a b c f g h : ℕ, 0 < a → a ≤ b → b ≤ c → 0 < f → f ≤ g → g ≤ h →
      a ^ d + b ^ d + c ^ d = f ^ d + g ^ d + h ^ d → (a, b, c) = (f, g, h) := by
    rcases hkind with ⟨hp, h7⟩ | hs
    · exact primes d hp h7
    · exact composites d hs
  have tuples := at_d _ _ _ _ _ _ (pow_pos hx _) (Nat.pow_le_pow_left hxy _)
    (Nat.pow_le_pow_left hyz _) (pow_pos hu _) (Nat.pow_le_pow_left huv _)
    (Nat.pow_le_pow_left hvw _) lift
  simpa only [Prod.mk.injEq, Nat.pow_left_inj hk0] using tuples

end OMA.R_oeis_a230563_R1
