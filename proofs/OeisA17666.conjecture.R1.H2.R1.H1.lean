import OMAReductions.R_OeisA17666_conjecture_R1_H2_R1
import Mathlib

-- Step OeisA17666.conjecture.R1.H2.R1.H1: hypothesis H1 of reduction OeisA17666.conjecture.R1.H2.R1
-- Credit: @ivillar. An odd b > 1 with at most six prime factors has sigma(b)/b < prod p/(p-1) <= (3/2)(5/4)...(13/12) < 3.

/-! Odd multiply perfect numbers of abundancy at least three have at least seven prime factors. -/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace P7A17666H2R1H1

/-- `c r = (3/2)(5/4)⋯((2r+1)/(2r))`. -/
def c (r : ℕ) : ℚ := ∏ i ∈ Finset.range r, ((2 * i + 3 : ℚ) / (2 * i + 2))

lemma c_succ (r : ℕ) : c (r + 1) = c r * ((2 * r + 3 : ℚ) / (2 * r + 2)) := by
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
    have h1 : (1 : ℚ) ≤ (2 * s + 3 : ℚ) / (2 * s + 2) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    nlinarith [c_nonneg s]

/-- The product of `p/(p-1)` over a set of distinct odd numbers `≥ 3` is at most `c` of its size. -/
lemma prod_le_c (S : Finset ℕ) (hS : ∀ x ∈ S, Odd x ∧ 3 ≤ x) :
    ∏ x ∈ S, ((x : ℚ) / ((x : ℚ) - 1)) ≤ c S.card := by
  induction S using Finset.induction_on_max with
  | empty => simp [c]
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, c_succ]
    have hs : ∀ x ∈ s, Odd x ∧ 3 ≤ x := fun x hx => hS x (Finset.mem_insert_of_mem hx)
    have ih' := ih hs
    obtain ⟨hao, ha3⟩ := hS a (Finset.mem_insert_self a s)
    -- `a ≥ 2 * card + 3`
    have hcard : (insert a s).card ≤ (a - 1) / 2 := by
      have : (insert a s).card ≤ (Finset.Icc 1 ((a - 1) / 2)).card := by
        apply Finset.card_le_card_of_injOn (fun x => (x - 1) / 2)
        · intro x hx
          have hx' := Finset.mem_insert.mp hx
          have hxo : Odd x ∧ 3 ≤ x := hS x hx
          have hxa : x ≤ a := by
            rcases hx' with rfl | h
            · exact le_rfl
            · exact (hlt x h).le
          simp only [Finset.coe_Icc, Set.mem_Icc]
          omega
        · intro x hx y hy hxy
          have hxo := (hS x hx).1
          have hyo := (hS y hy).1
          obtain ⟨u, rfl⟩ := hxo
          obtain ⟨v, rfl⟩ := hyo
          simp only at hxy
          omega
      simpa using this
    rw [Finset.card_insert_of_notMem ha] at hcard
    obtain ⟨u, rfl⟩ := hao
    have hr : s.card + 1 ≤ u := by omega
    have hpos : (0 : ℚ) < ((2 * u + 1 : ℕ) : ℚ) - 1 := by push_cast; linarith [show (1 : ℚ) ≤ u by exact_mod_cast (show 1 ≤ u by omega)]
    have hfac : ((2 * u + 1 : ℕ) : ℚ) / (((2 * u + 1 : ℕ) : ℚ) - 1) ≤
        (2 * s.card + 3 : ℚ) / (2 * s.card + 2) := by
      rw [div_le_div_iff₀ hpos (by positivity)]
      have : (s.card : ℚ) + 1 ≤ u := by exact_mod_cast hr
      push_cast
      nlinarith
    have hprod_nonneg : 0 ≤ ∏ x ∈ s, ((x : ℚ) / ((x : ℚ) - 1)) := by
      apply Finset.prod_nonneg
      intro x hx
      have h3 : (3 : ℚ) ≤ x := by exact_mod_cast (hs x hx).2
      apply div_nonneg <;> linarith
    calc ((2 * u + 1 : ℕ) : ℚ) / (((2 * u + 1 : ℕ) : ℚ) - 1) * ∏ x ∈ s, ((x : ℚ) / ((x : ℚ) - 1))
        ≤ (2 * s.card + 3 : ℚ) / (2 * s.card + 2) * c s.card := by
          apply mul_le_mul hfac ih' hprod_nonneg (by positivity)
      _ = c s.card * ((2 * s.card + 3 : ℚ) / (2 * s.card + 2)) := by ring

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

lemma odd_bound (b : ℕ) (hb : 1 < b) (hodd : Odd b) :
    ((σ 1 b : ℕ) : ℚ) / (b : ℚ) < c b.primeFactors.card := by
  refine lt_of_lt_of_le (abundancy_lt b hb) (prod_le_c _ ?_)
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpd)
  exact ⟨hpp.odd_of_ne_two hp2, by have := hpp.two_le; omega⟩

end P7A17666H2R1H1

open P7A17666H2R1H1

theorem OMA.solution : OMA.R_OeisA17666_conjecture_R1_H2_R1.H1 := by
  unfold OMA.R_OeisA17666_conjecture_R1_H2_R1.H1
  intro b k hb hodd hk hcard heq
  have h := odd_bound b hb hodd
  rw [heq] at h
  have hb0 : (0 : ℚ) < b := by exact_mod_cast (show 0 < b by omega)
  push_cast at h
  rw [mul_div_assoc, div_self hb0.ne', mul_one] at h
  have hc6 : c b.primeFactors.card ≤ c 6 := c_mono hcard
  have : c 6 < 3 := by norm_num [c, Finset.prod_range_succ]
  have hk' : (3 : ℚ) ≤ k := by exact_mod_cast hk
  linarith
