import FormalConjectures.OEIS.«245212»

-- Credit: @JaviSoto
-- Give every fixed odd divisor count an explicit finite search. No uniform
-- bound on the count itself is assumed. This applies to both odd and even n.
namespace OMA.R_OeisA245212_conjecture_R2
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Height theorem: the dyadic exponent and odd core are bounded without any
prior bound on a prime factor or its multiplicity. -/
def H1 : Prop := ∀ a m : ℕ, Odd m → 1 < m →
    OeisA245212.a (2^a*m)=(σ 1 (2^a*m):ℤ) →
    let t := m.divisors.card
    a < t*(2*Nat.log 2 (8*t^3)+2) ∧ m ≤ ((2^(a+1)-1)*(a+2)*t^2)^(t-1)

/-- For each divisor count the remaining no-solution test has finite ranges
for both variables. The count t is the only unbounded index. -/
def H2 : Prop := ∀ t : ℕ, ∀ a < t*(2*Nat.log 2 (8*t^3)+2),
    ∀ m ≤ ((2^(a+1)-1)*(a+2)*t^2)^(t-1), Odd m → 1 < m → m.divisors.card=t →
      OeisA245212.a (2^a*m)≠(σ 1 (2^a*m):ℤ)

-- Reuse the backward implication proved in the first reduction by @BetAdmin237.
lemma a_prime_pow (p : ℕ) (hp : p.Prime) (k : ℕ) :
    OeisA245212.a (p ^ k) =
      (p : ℤ) ^ k * (k + 1) - ∑ j ∈ range k, (p : ℤ) ^ j * (j + 1) := by
  unfold OeisA245212.a
  rw [Nat.divisors_prime_pow hp, card_map, card_range, Nat.properDivisors_prime_pow hp,
    sum_map]
  simp only [Function.Embedding.coeFn_mk, Nat.divisors_prime_pow hp, card_map, card_range]
  push_cast
  ring

lemma sigma_prime_pow (p : ℕ) (hp : p.Prime) (k : ℕ) :
    (σ 1 (p ^ k) : ℤ) = ∑ j ∈ range (k + 1), (p : ℤ) ^ j := by
  rw [ArithmeticFunction.sigma_apply_prime_pow hp]
  push_cast
  apply sum_congr rfl
  intro j _
  rw [mul_one]

lemma two_pow_sum (k : ℕ) :
    ∑ j ∈ range k, (2 : ℤ) ^ j * (j + 1) + 2 ^ (k + 1) = (k + 1) * 2 ^ k + 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    push_cast
    have e : (2 : ℤ) ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
    rw [e]
    have e2 : (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [e2] at ih ⊢
    nlinarith [ih]

lemma geom_two (k : ℕ) : ∑ j ∈ range (k + 1), (2 : ℤ) ^ j = 2 ^ (k + 1) - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    ring

lemma two_pow_holds (k : ℕ) : OeisA245212.a (2 ^ k) = (σ 1 (2 ^ k) : ℤ) := by
  rw [a_prime_pow 2 Nat.prime_two k, sigma_prime_pow 2 Nat.prime_two k]
  push_cast
  rw [geom_two]
  have := two_pow_sum k
  linarith

theorem main : H1 → H2 → type_of% @OeisA245212.conjecture := by
  intro height finiteSearch n hn
  constructor
  · intro eqn
    obtain ⟨a,m,nd,rep⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 2 (by decide)
    subst n
    have odd := Nat.not_even_iff_odd.mp (fun h => nd (even_iff_two_dvd.mp h))
    by_cases one : m=1
    · exact ⟨a,by simp [one]⟩
    have hm : 1 < m := by have := odd.pos; omega
    obtain ⟨ha,mb⟩ := height a m odd hm eqn
    exact (finiteSearch m.divisors.card a ha m mb odd hm rfl eqn).elim
  · rintro ⟨a,rfl⟩
    exact two_pow_holds a
end OMA.R_OeisA245212_conjecture_R2
