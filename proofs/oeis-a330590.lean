import OMAStatements.S_oeis_a330590
import Mathlib

/-! Fixed divisors of power differences, following @caa1982 (#23263).
Use the standard prime-factor divisor count and power/order congruence APIs.
The classification of fixed divisors and the final counting argument remain
unchanged. -/

open OMA.S_oeis_a330590


/-- The primes p with p - 1 dividing n - 1. -/
def PP (n : ℕ) : Finset ℕ := ((Nat.divisors (n - 1)).filter fun d => (d + 1).Prime).image (· + 1)

theorem mem_PP (n : ℕ) (hn : 2 ≤ n) (p : ℕ) : p ∈ PP n ↔ p.Prime ∧ (p - 1) ∣ (n - 1) := by
  unfold PP
  simp only [Finset.mem_image, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨d, ⟨⟨hd, -⟩, hp⟩, rfl⟩
    exact ⟨hp, by simpa using hd⟩
  · rintro ⟨hp, hd⟩
    have h2 := hp.two_le
    refine ⟨p - 1, ⟨⟨hd, by omega⟩, by rwa [Nat.sub_add_cancel (by omega)]⟩, by omega⟩

theorem card_PP (n : ℕ) : (PP n).card = A067513 (n - 1) := by
  unfold PP A067513
  exact Finset.card_image_of_injective _ (add_left_injective 1)

theorem prime_of_PP (n : ℕ) (hn : 2 ≤ n) : ∀ p ∈ PP n, p.Prime := fun p hp => ((mem_PP n hn p).1 hp).1

theorem card_div_prod (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (Nat.divisors (∏ p ∈ s, p)).card = 2 ^ s.card := by
  have hn : ∀ p ∈ s, p ≠ 0 := fun p hp => (hs p hp).ne_zero
  rw [Nat.card_divisors (Finset.prod_ne_zero_iff.mpr hn), Nat.primeFactors_prod hs,
    ← Finset.prod_const]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.factorization_prod_apply hn, Finset.sum_eq_single p]
  · simp [(hs p hp).factorization]
  · intro q hq hqp
    simp [(hs q hq).factorization, Ne.symm hqp]
  · exact fun h => (h hp).elim

theorem prime_dvd_pow_sub (n : ℕ) (hn : 2 ≤ n) (p : ℕ) (hp : p.Prime) (hd : (p - 1) ∣ (n - 1))
    (x : ℤ) : (p : ℤ) ∣ x ^ n - x := by
  have := Fact.mk hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  by_cases hx : (x : ZMod p) = 0
  · rw [hx, zero_pow (by omega)]; ring
  · obtain ⟨k, hk⟩ := hd
    have : n = (p - 1) * k + 1 := by omega
    rw [this, pow_succ, pow_mul, ZMod.pow_card_sub_one_eq_one hx, one_pow, one_mul, sub_self]

theorem dvd_of_PP (n : ℕ) (hn : 2 ≤ n) (x : ℤ) : ((∏ p ∈ PP n, p : ℕ) : ℤ) ∣ x ^ n - x := by
  push_cast
  apply Finset.prod_dvd_of_coprime
  · intro p hp q hq hpq
    exact Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (prime_of_PP n hn p hp)
      (prime_of_PP n hn q hq)).2 hpq)
  · intro p hp
    obtain ⟨hpp, hd⟩ := (mem_PP n hn p).1 hp
    exact prime_dvd_pow_sub n hn p hpp hd x

theorem sq_not_dvd (n : ℕ) (hn : 2 ≤ n) (p : ℕ) (hp : p.Prime) (h : ∀ x : ℤ, ((p * p : ℕ) : ℤ) ∣ x ^ n - x) :
    False := by
  have h1 := h p
  have e : (p : ℤ) ^ n - p = p * ((p : ℤ) ^ (n - 1) - 1) := by
    rw [mul_sub, ← pow_succ', Nat.sub_add_cancel (by omega)]; ring
  rw [e] at h1
  push_cast at h1
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h2 : (p : ℤ) ∣ (p : ℤ) ^ (n - 1) - 1 := (mul_dvd_mul_iff_left hp0).1 h1
  have h3 : (p : ℤ) ∣ (p : ℤ) ^ (n - 1) := dvd_pow_self _ (by omega)
  have h4 : (p : ℤ) ∣ 1 := by
    have := dvd_sub h3 h2
    simpa using this
  have : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos h4
  have := hp.two_le
  omega

theorem order_dvd (n : ℕ) (hn : 2 ≤ n) (p : ℕ) (hp : p.Prime) (h : ∀ x : ℤ, (p : ℤ) ∣ x ^ n - x) :
    (p - 1) ∣ (n - 1) := by
  have := Fact.mk hp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  rw [← hord]
  have hx := h ((g : ZMod p).val : ℤ)
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hx
  push_cast at hx
  rw [ZMod.natCast_zmod_val] at hx
  have e : g ^ n = g ^ 1 := Units.ext (by simpa using sub_eq_zero.mp hx)
  exact (Nat.modEq_iff_dvd' (by omega : 1 ≤ n)).mp (pow_eq_pow_iff_modEq.mp e).symm

theorem dvd_prod_of_good (n : ℕ) (hn : 2 ≤ n) (m : ℕ) (hm : 0 < m) (h : ∀ x : ℤ, (m : ℤ) ∣ x ^ n - x) :
    m ∣ ∏ p ∈ PP n, p := by
  have hsq : Squarefree m := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hpm
    exact sq_not_dvd n hn p hp fun x => (Int.natCast_dvd_natCast.2 hpm).trans (h x)
  rw [← Nat.prod_primeFactors_of_squarefree hsq]
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpm := Nat.dvd_of_mem_primeFactors hp
  rw [mem_PP n hn]
  exact ⟨hpp, order_dvd n hn p hpp fun x => (Int.natCast_dvd_natCast.2 hpm).trans (h x)⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a330590.main := by
  intro n hn
  have hM : (∏ p ∈ PP n, p) ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp => (prime_of_PP n hn p hp).ne_zero
  have hset : {m : ℕ | 0 < m ∧ ∀ x : ℤ, (m : ℤ) ∣ x ^ n - x ^ 1} =
      ((Nat.divisors (∏ p ∈ PP n, p) : Finset ℕ) : Set ℕ) := by
    ext m
    simp only [pow_one, Set.mem_ofPred_eq, Finset.mem_coe, Nat.mem_divisors]
    constructor
    · rintro ⟨hm, h⟩
      exact ⟨dvd_prod_of_good n hn m hm h, hM⟩
    · rintro ⟨hd, -⟩
      refine ⟨Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hM), fun x => ?_⟩
      exact (Int.natCast_dvd_natCast.2 hd).trans (dvd_of_PP n hn x)
  unfold T
  rw [hset, Set.ncard_coe_finset, card_div_prod _ (prime_of_PP n hn), card_PP]
