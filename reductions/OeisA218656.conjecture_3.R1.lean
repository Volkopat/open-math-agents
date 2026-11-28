import FormalConjectures.OEIS.«218656»
import Mathlib

-- Reduction OeisA218656.conjecture_3.R1
-- Credit: @studer

/-!
For an admissible partition of 2n+1, a composite sum of eighth powers has a prime
factor at most (2n+1)^4, while a prime sum is strictly larger than this threshold.
Every positive n admits a primitive partition with least prime factor greater
than floor(log₄ n), by the cyclotomic sieve below. The open large-n step asks
for a primitive partition reaching the quartic threshold.

Thomas Ordowski proposed the conjecture in 2012. Mauro Fiorentini reported
the six exceptions after checking all odd totals through 10^6 in 2023.
Source: https://oeis.org/A218656
-/

namespace OMA.R_OeisA218656_conjecture_3_R1

/-- For a primitive pair of opposite parity, every prime divisor of x⁸+y⁸ is
1 modulo 16, and divides neither x nor x+y. -/
theorem factor (n x y p : ℕ) (hs : x+y=2*n+1) (hc : x.Coprime (2*n+1))
    (hp : p.Prime) (hf : p ∣ x^8+y^8) :
    ¬p∣x ∧ ¬p∣2*n+1 ∧ 16 ∣ p-1 := by
  have hp2 : p≠2 := by
    rintro rfl
    have hm := Nat.mod_eq_zero_of_dvd hf
    rw [Nat.add_mod, Nat.pow_mod, Nat.pow_mod y] at hm
    have e := Nat.mod_lt x (by decide : 0<2)
    have f := Nat.mod_lt y (by decide : 0<2)
    interval_cases hx : x%2 <;> interval_cases hy : y%2 <;> norm_num [hx,hy] at hm <;> omega
  let : Fact p.Prime := ⟨hp⟩
  have hz : (x : ZMod p)^8 + (y : ZMod p)^8 = 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).2 hf
  have hx : (x : ZMod p) ≠ 0 := by
    intro hx
    simp [hx] at hz
    have xdiv := (ZMod.natCast_eq_zero_iff x p).1 hx
    have ydiv := (ZMod.natCast_eq_zero_iff y p).1 hz
    have hg : p ∣ x.gcd (2*n+1) := Nat.dvd_gcd xdiv (hs ▸ dvd_add xdiv ydiv)
    rw [hc.gcd_eq_one] at hg
    exact hp.not_dvd_one hg
  have hy : (y : ZMod p) ≠ 0 := by
    intro hy
    simp [hy] at hz
    exact hx hz
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  have hsum : ¬p ∣ 2*n+1 := by
    intro h
    rw [← hs] at h
    have he : (x : ZMod p)+(y : ZMod p)=0 := by
      exact_mod_cast (ZMod.natCast_eq_zero_iff (x+y) p).2 h
    have he' : (y : ZMod p) = -x := by linear_combination he
    rw [he'] at hz
    have hz' : (2 : ZMod p)*(x : ZMod p)^8=0 := by linear_combination hz
    exact (mul_ne_zero htwo (pow_ne_zero _ hx)) hz'
  let z : ZMod p := x / y
  have hz8 : z^8 = -1 := by
    dsimp [z]
    rw [div_pow, div_eq_iff (pow_ne_zero _ hy)]
    linear_combination hz
  have hz16 : z^16=1 := by calc
    z^16 = (z^8)^2 := by ring
    _ = 1 := by rw [hz8]; ring
  have h8 : z^8≠1 := by
    rw [hz8]
    intro h
    exact htwo (by linear_combination -h)
  have ho : orderOf z=16 := orderOf_eq_prime_pow (p:=2) (n:=3) h8 hz16
  refine ⟨fun h => hx ((ZMod.natCast_eq_zero_iff x p).2 h), hsum, ?_⟩
  rw [← ho]
  exact ZMod.orderOf_dvd_card_sub_one (div_ne_zero hx hy)

/-- For any fixed bound, every sufficiently large odd total admits a primitive
partition whose sum of eighth powers avoids all primes up to the bound. -/
theorem avoid (B n : ℕ) (hn : (∏ p ∈ (Finset.range (B+1)).filter (fun p => p.Prime ∧ 16∣p-1), p) ≤ n) :
    ∃ x : ℕ, 1≤x ∧ x≤n ∧ x.Coprime (2*n+1) ∧
      ∀ p : ℕ, p.Prime → p ∣ x^8+(2*n+1-x)^8 → B<p := by
  let P := (Finset.range (B+1)).filter (fun p => p.Prime ∧ 16∣p-1)
  let Q := P.filter (fun p => ¬p ∣ 2*n+1)
  let x := ∏ p ∈ Q, p
  have hP {p : ℕ} (h : p∈P) : p.Prime ∧ 16∣p-1 := (Finset.mem_filter.mp h).2
  have hpos : 0<∏ p ∈ P, p := Finset.prod_pos fun p hp => (hP hp).1.pos
  have hxpos : 0<x := Finset.prod_pos fun p hp => (hP (Finset.mem_filter.mp hp).1).1.pos
  have hxn : x≤n := by
    have hd := Finset.prod_dvd_prod_of_subset Q P id (Finset.filter_subset ..)
    exact (Nat.le_of_dvd hpos hd).trans hn
  have hcop : x.Coprime (2*n+1) := by
    apply Nat.coprime_prod_left_iff.mpr
    intro p hp
    exact (hP (Finset.mem_filter.mp hp).1).1.coprime_iff_not_dvd.mpr (Finset.mem_filter.mp hp).2
  refine ⟨x,hxpos,hxn,hcop,?_⟩
  intro p hp hf
  by_contra! h
  obtain ⟨hx,hs,ho⟩ := factor n x (2*n+1-x) p (by omega) hcop hp hf
  have hmem : p∈Q := Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp,ho⟩,hs⟩
  exact hx (Finset.dvd_prod_of_mem (fun q => q) hmem)


theorem candidate_bounds (n x : ℕ) (hx : 1≤x) (hxn : x≤n) :
    (2*n+1)^4 < x^8+(2*n+1-x)^8 ∧ x^8+(2*n+1-x)^8 ≤ (2*n+1)^8 := by
  let y := 2*n+1-x
  have hy : n+1≤y := by dsimp [y]; omega
  have hsum : x+y=2*n+1 := by dsimp [y]; omega
  have h₂ : 2*n+1<y^2 := by nlinarith [Nat.mul_self_le_mul_self hy, Nat.mul_self_le_mul_self (hx.trans hxn)]
  constructor
  · change _ < x^8+y^8
    have hh : (2*n+1)^4 < (y^2)^4 := Nat.pow_lt_pow_left h₂ (by decide)
    rw [← pow_mul] at hh
    norm_num1 at hh
    omega
  · change x^8+y^8 ≤ _
    rw [← hsum]
    ring_nf
    omega

/-- A split is prime exactly when its smallest prime factor exceeds this uniform
quartic threshold. The threshold depends only on the sum of the two parts. -/
theorem prime_iff_threshold (n x : ℕ) (hx : 1≤x) (hxn : x≤n) :
    Nat.Prime (x^8+(2*n+1-x)^8) ↔
      (2*n+1)^4 < Nat.minFac (x^8+(2*n+1-x)^8) := by
  obtain ⟨hlo,hhi⟩ := candidate_bounds n x hx hxn
  constructor
  · intro hp
    rwa [hp.minFac_eq]
  · intro h
    by_contra hn
    have hl := Nat.minFac_sq_le_self (by omega) hn
    have hh := Nat.pow_lt_pow_left h (show 2≠0 by decide)
    rw [← pow_mul] at hh
    norm_num1 at hh
    omega

/-- Every odd total, with its smaller part positive and bounded by n, admits
a primitive split whose smallest prime factor strictly exceeds floor(log₄ n). -/
theorem logarithmic_bound (n : ℕ) (hn : 1≤n) :
    ∃ x : ℕ, 1≤x ∧ x≤n ∧ x.Coprime (2*n+1) ∧
      Nat.log 4 n < Nat.minFac (x^8+(2*n+1-x)^8) := by
  let B := Nat.log 4 n
  have hmod : (∏ p ∈ (Finset.range (B+1)).filter (fun p => p.Prime ∧ 16∣p-1), p) ≤ primorial B := by
    apply Nat.le_of_dvd (primorial_pos _)
    apply Finset.prod_dvd_prod_of_subset _ _ id
    intro p hp
    obtain ⟨hr,hp,-⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hr,hp⟩
  have hB : (∏ p ∈ (Finset.range (B+1)).filter (fun p => p.Prime ∧ 16∣p-1), p) ≤ n := hmod.trans
    ((primorial_le_four_pow B).trans (Nat.pow_log_le_self 4 (by omega)))
  obtain ⟨x,hx,hxn,hcop,hall⟩ := avoid B n hB
  have hval := (candidate_bounds n x hx hxn).1
  have hpow : 0<(2*n+1)^4 := by positivity
  exact ⟨x,hx,hxn,hcop,hall _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd _)⟩


/-- Primality forces the primitive condition in the large-n step. -/
theorem primitive_of_prime (n x : ℕ) (hx : 1≤x) (hxn : x≤n)
    (hp : Nat.Prime (x^8+(2*n+1-x)^8)) : x.Coprime (2*n+1) := by
  by_contra h
  obtain ⟨q,hq,hqx,hqs⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hqy := Nat.dvd_sub hqs hqx
  have hf : q ∣ x^8+(2*n+1-x)^8 := dvd_add
    (hqx.trans (dvd_pow_self _ (by decide))) (hqy.trans (dvd_pow_self _ (by decide)))
  have he := (Nat.prime_dvd_prime_iff_eq hq hp).mp hf
  have hb := (candidate_bounds n x hx hxn).1
  have hle := Nat.le_of_dvd hx hqx
  have hl : 2*n+1 ≤ (2*n+1)^4 := Nat.le_pow (by decide)
  omega

/-- The positive prime witnesses in the initial range. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ 64 → n ∉ ({3,4,27,36,37,52} : Set ℕ) →
    ∃ x : ℕ, 1 ≤ x ∧ x ≤ n ∧ Nat.Prime (x^8+(2*n+1-x)^8)

/-- Find a primitive partition attaining the quartic least-factor threshold
above the finite range. -/
def H2 : Prop :=
  ∀ n : ℕ, 64 < n →
    ∃ x : ℕ, 1 ≤ x ∧ x ≤ n ∧ x.Coprime (2*n+1) ∧
      (2*n+1)^4 < Nat.minFac (x^8+(2*n+1-x)^8)

theorem main : H1 → H2 → type_of% @OeisA218656.conjecture_3 := by
  intro small large n hn exc
  by_cases h : n ≤ 64
  · exact small n hn h exc
  · obtain ⟨x, hx, hxn, _, hmin⟩ := large n (by omega)
    exact ⟨x, hx, hxn, (prime_iff_threshold n x hx hxn).mpr hmin⟩

end OMA.R_OeisA218656_conjecture_3_R1
