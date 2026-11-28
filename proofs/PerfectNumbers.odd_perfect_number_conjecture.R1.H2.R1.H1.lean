import OMAReductions.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H2_R1
import Mathlib

-- Step PerfectNumbers.odd_perfect_number_conjecture.R1.H2.R1.H1: hypothesis H1 of reduction PerfectNumbers.odd_perfect_number_conjecture.R1.H2.R1
-- Credit: @ivillar. If every prime factor of an odd n is >= 5 and there are at most 5 of them, sigma(n)/n < prod p/(p-1) <= (5/4)(7/6)(9/8)(11/10)(13/12) < 2, so n is not perfect. Abundancy lemmas adapted from our (P7) OeisA17666 step.

/-! Step PerfectNumbers.odd_perfect_number_conjecture.R1.H2.R1.H1. -/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace P8OPNFew

/-- `c r = (5/4)(7/6)⋯((2r+3)/(2r+2))`. -/
def c (r : ℕ) : ℚ := ∏ i ∈ Finset.range r, ((2 * i + 5 : ℚ) / (2 * i + 4))

lemma c_succ (r : ℕ) : c (r + 1) = c r * ((2 * r + 5 : ℚ) / (2 * r + 4)) := by
  simp only [c, Finset.prod_range_succ]

lemma c_nonneg (r : ℕ) : 0 ≤ c r := by
  unfold c
  apply Finset.prod_nonneg
  intro i _
  positivity

lemma c_mono {r s : ℕ} (h : r ≤ s) : c r ≤ c s := by
  induction s, h using Nat.le_induction with
  | base => exact le_rfl
  | succ s _ ih =>
    rw [c_succ]
    have h1 : (1 : ℚ) ≤ (2 * s + 5 : ℚ) / (2 * s + 4) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    nlinarith [c_nonneg s]

/-- The product of `p/(p-1)` over a set of distinct odd numbers `≥ 5` is at most `c` of its size. -/
lemma prod_le_c (S : Finset ℕ) (hS : ∀ x ∈ S, Odd x ∧ 5 ≤ x) :
    ∏ x ∈ S, ((x : ℚ) / ((x : ℚ) - 1)) ≤ c S.card := by
  induction S using Finset.induction_on_max with
  | empty => simp [c]
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, c_succ]
    have hs : ∀ x ∈ s, Odd x ∧ 5 ≤ x := fun x hx => hS x (Finset.mem_insert_of_mem hx)
    have ih' := ih hs
    obtain ⟨hao, ha3⟩ := hS a (Finset.mem_insert_self a s)
    have hcard : (insert a s).card ≤ (a - 3) / 2 := by
      have : (insert a s).card ≤ (Finset.Icc 1 ((a - 3) / 2)).card := by
        apply Finset.card_le_card_of_injOn (fun x => (x - 3) / 2)
        · intro x hx
          have hx' := Finset.mem_insert.mp hx
          have hxo : Odd x ∧ 5 ≤ x := hS x hx
          have hxa : x ≤ a := by
            rcases hx' with rfl | h
            · exact le_rfl
            · exact (hlt x h).le
          simp only [Finset.coe_Icc, Set.mem_Icc]
          omega
        · intro x hx y hy hxy
          obtain ⟨⟨u, rfl⟩, hx5⟩ := hS x hx
          obtain ⟨⟨v, rfl⟩, hy5⟩ := hS y hy
          simp only at hxy
          omega
      simpa using this
    rw [Finset.card_insert_of_notMem ha] at hcard
    obtain ⟨u, rfl⟩ := hao
    have hr : s.card + 2 ≤ u := by omega
    have hpos : (0 : ℚ) < ((2 * u + 1 : ℕ) : ℚ) - 1 := by push_cast; linarith [show (1 : ℚ) ≤ u by exact_mod_cast (show 1 ≤ u by omega)]
    have hfac : ((2 * u + 1 : ℕ) : ℚ) / (((2 * u + 1 : ℕ) : ℚ) - 1) ≤
        (2 * s.card + 5 : ℚ) / (2 * s.card + 4) := by
      rw [div_le_div_iff₀ hpos (by positivity)]
      have : (s.card : ℚ) + 2 ≤ u := by exact_mod_cast hr
      push_cast
      nlinarith
    have hprod_nonneg : 0 ≤ ∏ x ∈ s, ((x : ℚ) / ((x : ℚ) - 1)) := by
      apply Finset.prod_nonneg
      intro x hx
      have h3 : (3 : ℚ) ≤ x := by
        have h5 := (hs x hx).2
        exact_mod_cast (show 3 ≤ x by omega)
      apply div_nonneg <;> linarith
    calc ((2 * u + 1 : ℕ) : ℚ) / (((2 * u + 1 : ℕ) : ℚ) - 1) * ∏ x ∈ s, ((x : ℚ) / ((x : ℚ) - 1))
        ≤ (2 * s.card + 5 : ℚ) / (2 * s.card + 4) * c s.card := by
          apply mul_le_mul hfac ih' hprod_nonneg (by positivity)
      _ = c s.card * ((2 * s.card + 5 : ℚ) / (2 * s.card + 4)) := by ring

/-- `σ(p^e) / p^e < p / (p - 1)` for a prime `p`. -/
lemma sigma_pp_lt {p e : ℕ} (hp : p.Prime) :
    ((σ 1 (p ^ e) : ℕ) : ℚ) / ((p ^ e : ℕ) : ℚ) < (p : ℚ) / ((p : ℚ) - 1) := by
  have hp2 : (2 : ℚ) ≤ p := by exact_mod_cast hp.two_le
  rw [sigma_one_apply_prime_pow hp]
  set S := ∑ i ∈ Finset.range (e + 1), p ^ i with hSdef
  have hgeo : S * (p - 1) + 1 = p ^ (e + 1) := by
    have := geom_sum_mul_add (p - 1) (e + 1)
    rwa [Nat.sub_add_cancel hp.one_le] at this
  have hq : (S : ℚ) * ((p : ℚ) - 1) + 1 = (p : ℚ) ^ e * p := by
    have h := congrArg (Nat.cast : ℕ → ℚ) hgeo
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_pow, Nat.cast_one, pow_succ] at h
    exact h
  have hpe : (0 : ℚ) < (p : ℚ) ^ e := by positivity
  rw [Nat.cast_pow, div_lt_div_iff₀ hpe (by linarith)]
  nlinarith

/-- `σ(n)/n < ∏ p/(p-1)` over the prime factors, for `n > 1`. -/
lemma abundancy_lt (n : ℕ) (hn : 1 < n) :
    ((σ 1 n : ℕ) : ℚ) / (n : ℚ) < ∏ p ∈ n.primeFactors, ((p : ℚ) / ((p : ℚ) - 1)) := by
  have hn0 : n ≠ 0 := by omega
  have hs := isMultiplicative_sigma.multiplicative_factorization (σ 1) hn0
  have hn' := Nat.prod_factorization_pow_eq_self hn0
  have key : ((σ 1 n : ℕ) : ℚ) / (n : ℚ) =
      ∏ p ∈ n.primeFactors, (((σ 1 (p ^ n.factorization p) : ℕ) : ℚ) / ((p ^ n.factorization p : ℕ) : ℚ)) := by
    rw [Finset.prod_div_distrib]
    congr 1
    · rw [hs, Nat.cast_finsuppProd]
      rfl
    · conv_lhs => rw [← hn']
      rw [Nat.cast_finsuppProd]
      rfl
  rw [key]
  apply Finset.prod_lt_prod_of_nonempty
  · intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have h1 : 0 < σ 1 (p ^ n.factorization p) := by
      rw [sigma_one_apply_prime_pow hpp]
      exact Finset.sum_pos (fun i _ => pow_pos hpp.pos i) ⟨0, by simp⟩
    have h2 : 0 < p ^ n.factorization p := pow_pos hpp.pos _
    exact div_pos (by exact_mod_cast h1) (by exact_mod_cast h2)
  · intro p hp
    exact sigma_pp_lt (Nat.prime_of_mem_primeFactors hp)
  · exact Nat.nonempty_primeFactors.mpr hn

theorem opn_few_factors : ∀ n : ℕ, Nat.Perfect n → Odd n → n.primeFactors.card ≤ 5 →
    Nat.minFac n ∉ ({5, 7, 11, 13, 17} : Set ℕ) := by
  intro n hperf hodd hcard hmin
  have hn0 : n ≠ 0 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hodd
    omega
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmin
  have h5 : 5 ≤ n.minFac := by omega
  have hn1 : 1 < n := by
    by_contra h
    have : n = 1 := by omega
    rw [this, Nat.minFac_one] at h5
    omega
  have hσ : σ 1 n = 2 * n := by
    rw [sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul (Nat.pos_of_ne_zero hn0)).mp hperf
  have hb := abundancy_lt n hn1
  have hprod := prod_le_c n.primeFactors (by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hle : n.minFac ≤ p := Nat.minFac_le_of_dvd hpp.two_le hpd
    have hp2 : p ≠ 2 := by omega
    exact ⟨hpp.odd_of_ne_two hp2, by omega⟩)
  have hc5 : c n.primeFactors.card ≤ c 5 := c_mono hcard
  have hlt : c 5 < 2 := by norm_num [c, Finset.prod_range_succ]
  rw [hσ] at hb
  have hn0' : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  push_cast at hb
  rw [mul_div_assoc, div_self hn0'.ne', mul_one] at hb
  linarith

end P8OPNFew

theorem OMA.solution : OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H2_R1.H1 :=
  P8OPNFew.opn_few_factors
