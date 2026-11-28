import FormalConjectures.ErdosProblems.«203»
import Mathlib

namespace OMA.R_Erdos203_erdos_203_R1

-- The hard open core: a finite covering system of residue classes, each equipped with a prime
-- certificate modulo which the relevant power is periodic with the given modulus.
-- The period clauses are equivalent (for primes not dividing 6) to the order of 2 resp. 3
-- dividing the modulus, and are included as data so that the bridge stays elementary.
def H1 : Prop :=
  ∃ (n : ℕ) (p : Fin n → ℕ) (a : Fin n → ℕ) (b : Fin n → ℕ)
      (alpha : Fin n → ℕ) (beta : Fin n → ℕ),
    (∀ i, (p i).Prime) ∧
    (∀ i, ¬ p i ∣ 6) ∧
    Function.Injective p ∧
    (∀ i, 0 < a i) ∧
    (∀ i, 0 < b i) ∧
    (∀ i, ∀ k : ℕ, k ≡ alpha i [MOD a i] → 2 ^ k ≡ 2 ^ alpha i [MOD p i]) ∧
    (∀ i, ∀ l : ℕ, l ≡ beta i [MOD b i] → 3 ^ l ≡ 3 ^ beta i [MOD p i]) ∧
    (∀ k l : ℕ, ∃ i : Fin n, k ≡ alpha i [MOD a i] ∧ l ≡ beta i [MOD b i])

-- Elementary CRT realisation: distinct primes outside 6 allow one m, coprime to 6 and larger
-- than every p i, satisfying all the required congruences at once.
def H2 : Prop :=
  ∀ (n : ℕ) (p : Fin n → ℕ) (alpha : Fin n → ℕ) (beta : Fin n → ℕ),
    (∀ i, (p i).Prime) →
    (∀ i, ¬ p i ∣ 6) →
    Function.Injective p →
    ∃ m : ℕ, m.Coprime 6 ∧
      (∀ i, p i < m) ∧
      (∀ i, p i ∣ 2 ^ alpha i * 3 ^ beta i * m + 1)

theorem main : H1 → H2 → type_of% @Erdos203.erdos_203 := by
  rintro ⟨n, p, a, b, alpha, beta, hp, hp6, hinj, ha, hb, hper2, hper3, hcov⟩ h2
  rcases h2 n p alpha beta hp hp6 hinj with ⟨m, hm6, hmgt, hdiv⟩
  refine ⟨m, hm6, ?_⟩
  intro k l hNprime
  rcases hcov k l with ⟨i, hk, hl⟩
  have h2m : 2 ^ k * 3 ^ l * m ≡ 2 ^ alpha i * 3 ^ beta i * m [MOD p i] := by
    exact ((hper2 i k hk).mul (hper3 i l hl)).mul_right m
  have hs : 2 ^ k * 3 ^ l * m + 1 ≡ 2 ^ alpha i * 3 ^ beta i * m + 1 [MOD p i] :=
    h2m.add_right 1
  have hz : (2 ^ alpha i * 3 ^ beta i * m + 1) % p i = 0 :=
    (Nat.dvd_iff_mod_eq_zero).mp (hdiv i)
  have hz' : (2 ^ k * 3 ^ l * m + 1) % p i = 0 := by
    change (2 ^ k * 3 ^ l * m + 1) % p i = (2 ^ alpha i * 3 ^ beta i * m + 1) % p i at hs
    rw [hs, hz]
  have hdvd : p i ∣ 2 ^ k * 3 ^ l * m + 1 := (Nat.dvd_iff_mod_eq_zero).mpr hz'
  have hcases : p i = 1 ∨ p i = 2 ^ k * 3 ^ l * m + 1 := (Nat.dvd_prime hNprime).mp hdvd
  rcases hcases with hione | hEq
  · have hpone := (hp i).one_lt
    omega
  · have hlt_m : m < 2 ^ k * 3 ^ l * m + 1 := by
      have h2ge : 1 ≤ 2 ^ k := by
        have h : 0 < 2 ^ k := by positivity
        omega
      have h3ge : 1 ≤ 3 ^ l := by
        have h : 0 < 3 ^ l := by positivity
        omega
      have hprod : 1 ≤ 2 ^ k * 3 ^ l := Nat.mul_le_mul h2ge h3ge
      have hle : m ≤ 2 ^ k * 3 ^ l * m := by
        have := Nat.mul_le_mul_right m hprod
        simpa using this
      omega
    have hlt : p i < 2 ^ k * 3 ^ l * m + 1 := lt_trans (hmgt i) hlt_m
    omega

end OMA.R_Erdos203_erdos_203_R1
