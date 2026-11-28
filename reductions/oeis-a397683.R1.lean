import OMAStatements.S_oeis_a397683
import Mathlib

-- Reduction oeis-a397683.R1 of step oeis-a397683
-- Credit: @Ciphore
-- The two directions of the conjectured equivalence are independent mathematics, and the
-- witness-existence direction itself splits by the prime structure of the modulus:
-- prime powers (cyclic-group combinatorics), moduli with two distinct primes (CRT lifting),
-- and the two obstructed prime powers 3^k and 7^k.

namespace OMA.R_oeis_a397683_R1

open OMA.S_oeis_a397683

/-- The prime-power witness core: for every odd prime `p` other than `3` and `7` and every
    exponent `a ≥ 1`, some pair of consecutive units modulo `p^a` has equal multiplicative
    orders. This is the cyclic-group heart of the problem. -/
def H1 : Prop := ∀ p a : ℕ, p.Prime → Odd p → p ≠ 3 → p ≠ 7 → 1 ≤ a → f (p ^ a) ≠ 0

/-- The composite-modulus witness core: whenever two distinct primes divide the odd modulus,
    consecutive equal-order units exist. This is the independent CRT-lifting heart. -/
def H2 : Prop := ∀ m : ℕ, Odd m →
  (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ m ∧ q ∣ m) → f m ≠ 0

/-- The `3`-power obstruction: no consecutive units modulo `3^k` share a multiplicative order. -/
def H3 : Prop := ∀ k : ℕ, 1 ≤ k → f (3 ^ k) = 0

/-- The `7`-power obstruction: no consecutive units modulo `7^k` share a multiplicative order. -/
def H4 : Prop := ∀ k : ℕ, 1 ≤ k → f (7 ^ k) = 0

/-- Every natural number `m > 1` with no two distinct prime divisors is a prime power. -/
theorem prime_power_of_one_prime (m : ℕ) (hm : 1 < m)
    (h : ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ m ∧ q ∣ m) :
    ∃ p a : ℕ, p.Prime ∧ 1 ≤ a ∧ m = p ^ a := by
  have hm0 : m ≠ 0 := by omega
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  have ha : 1 ≤ m.factorization p :=
    Nat.succ_le_of_lt (hp.factorization_pos_of_dvd hm0 hpm)
  set a := m.factorization p with ha_def
  have hpa_dvd : p ^ a ∣ m := (hp.pow_dvd_iff_le_factorization hm0).mpr (le_refl a)
  set s := m / p ^ a with hs_def
  have hdecomp : m = p ^ a * s := (Nat.mul_div_cancel' hpa_dvd).symm
  have hs0 : 0 < s := by
    apply Nat.div_pos (Nat.le_of_dvd (by omega) hpa_dvd) (pow_pos hp.pos a)
  by_cases hs1 : s = 1
  · exact ⟨p, a, hp, ha, by rw [hdecomp, hs1, mul_one]⟩
  · exfalso
    have hs2 : 1 < s := by omega
    obtain ⟨q, hq, hqs⟩ := Nat.exists_prime_and_dvd (by omega : s ≠ 1)
    have hqm : q ∣ m := hqs.trans (Nat.div_dvd_of_dvd hpa_dvd)
    by_cases hpq : p = q
    · subst hpq
      have hpdvd : p ^ (a + 1) ∣ m := by
        obtain ⟨t, ht⟩ := hqs
        rw [hdecomp, ht]
        use t
        ring_nf
      have hle : a + 1 ≤ m.factorization p :=
        (hp.pow_dvd_iff_le_factorization hm0).mp hpdvd
      omega
    · exact h ⟨p, q, hp, hq, hpq, hpm, hqm⟩

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a397683.main := by
  intro h1 h2 h3 h4 m hom
  obtain ⟨w, hw⟩ := hom
  constructor
  · intro hf0
    by_cases hm1 : m = 1
    · exfalso
      subst hm1
      rw [show f 1 = 1 from rfl] at hf0
      exact Nat.one_ne_zero hf0
    · by_cases htwo : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ m ∧ q ∣ m
      · exact absurd (h2 m ⟨w, hw⟩ htwo) (not_not.mpr hf0)
      · have hm2 : 1 < m := by omega
        obtain ⟨p, a, hp, ha, hm⟩ := prime_power_of_one_prime m hm2 htwo
        subst hm
        rcases hp.eq_two_or_odd with hp2 | hpodd
        · exfalso
          subst hp2
          have hdvd : 2 ∣ 2 ^ a := dvd_pow_self 2 (by omega)
          rw [hw] at hdvd
          omega
        · have hpodd' : Odd p := ⟨p / 2, by omega⟩
          by_cases hp3 : p = 3
          · exact ⟨a, ha, Or.inl (by rw [hp3])⟩
          · by_cases hp7 : p = 7
            · exact ⟨a, ha, Or.inr (by rw [hp7])⟩
            · exact absurd (h1 p a hp hpodd' hp3 hp7 ha) (not_not.mpr hf0)
  · rintro ⟨k, hk, rfl | rfl⟩
    · exact h3 k hk
    · exact h4 k hk

end OMA.R_oeis_a397683_R1
