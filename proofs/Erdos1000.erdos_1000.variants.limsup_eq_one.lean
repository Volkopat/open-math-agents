import FormalConjectures.ErdosProblems.«1000»
import Mathlib.NumberTheory.Primorial

/-!
At the first denominator divisible by a prime p, every numerator coprime to p
gives a new fraction. A uniform bound on the prime factors of the denominators
would give a positive lower bound on the fraction of new terms, by the totient
formula and the primorial of that bound.
-/

open Erdos1000 Filter Finset

namespace NewFractions

private lemma first_prime_count (n : ℕ → ℕ) {k p : ℕ} (hp : p.Prime)
    (hpk : p ∣ n k) (hfirst : ∀ j < k, ¬ p ∣ n j) : n k - n k / p ≤ phiSeq n k := by
  let N := n k
  have hcount := card_filter_add_card_filter_not (s := Ioc 0 N) (fun m => p ∣ m)
  rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.card_Ioc, Nat.sub_zero] at hcount
  calc
    N - N / p = ((Ioc 0 N).filter (fun m => ¬ p ∣ m)).card := by omega
    _ ≤ phiSeq n k := by
      apply card_le_card
      intro m hm
      obtain ⟨hm, hmd⟩ := mem_filter.mp hm
      refine mem_filter.mpr ⟨hm, fun j hj hd => hfirst j hj ?_⟩
      have hprod : p ∣ N / Nat.gcd m N * Nat.gcd m N := by
        rwa [Nat.div_mul_cancel (Nat.gcd_dvd_right m N)]
      have hgcd : ¬ p ∣ Nat.gcd m N := fun h => hmd (h.trans (Nat.gcd_dvd_left m N))
      exact ((hp.dvd_mul.mp hprod).resolve_right hgcd).trans hd

private lemma totient_primorial_bound {m B : ℕ} (h : ∀ p ∈ m.primeFactors, p ≤ B) :
    m ≤ m.totient * primorial B := by
  have hpos : 0 < ∏ p ∈ m.primeFactors, (p - 1) :=
    prod_pos fun p hp => Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt
  have hsub : m.primeFactors ⊆ Nat.primesLE B := fun p hp =>
    Nat.mem_primesLE.mpr ⟨h p hp, Nat.prime_of_mem_primeFactors hp⟩
  have hprod : (∏ p ∈ m.primeFactors, p) ∣ primorial B := by
    rw [primorial_eq_prod_primesLE]
    exact prod_dvd_prod_of_subset _ _ id hsub
  calc
    m ≤ m * ∏ p ∈ m.primeFactors, (p - 1) := Nat.le_mul_of_pos_right _ hpos
    _ = m.totient * ∏ p ∈ m.primeFactors, p := (Nat.totient_mul_prod_primeFactors m).symm
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_of_dvd (primorial_pos B) hprod)

end NewFractions

theorem OMA.solution : type_of% @Erdos1000.erdos_1000.variants.limsup_eq_one := by
  classical
  intro n hn hn0 hlim
  let r (k : ℕ) : ℝ := (phiSeq n k : ℝ) / (n k : ℝ)
  change atTop.liminf r = 0 at hlim
  change atTop.limsup r = 1
  have hnpos (k : ℕ) : 0 < n k := hn0.trans_le (hn.monotone (Nat.zero_le k))
  have hnposR (k : ℕ) : (0 : ℝ) < n k := by exact_mod_cast hnpos k
  have r_le (k : ℕ) : r k ≤ 1 := by
    apply (div_le_one (hnposR k)).mpr
    have hcard : phiSeq n k ≤ n k := (card_filter_le _ _).trans (by simp)
    exact_mod_cast hcard
  have r_nonneg (k : ℕ) : 0 ≤ r k := by dsimp [r]; positivity
  have large_prime (B : ℕ) : ∃ k p, p ∈ (n k).primeFactors ∧ B < p := by
    by_contra! hB
    have hpos : (0 : ℝ) < primorial B := by exact_mod_cast primorial_pos B
    have lower (k : ℕ) : 1 / (primorial B : ℝ) ≤ r k := by
      change _ ≤ (phiSeq n k : ℝ) / (n k : ℝ)
      rw [div_le_div_iff₀ hpos (hnposR k), one_mul]
      exact_mod_cast (NewFractions.totient_primorial_bound (hB k)).trans
        (Nat.mul_le_mul_right _ (erdos_1000.variants.totient_le n hn hn0 k))
    have hle := le_liminf_of_le (isCoboundedUnder_ge_of_le atTop r_le) (.of_forall lower)
    rw [hlim] at hle
    exact (not_le_of_gt (one_div_pos.mpr hpos)) hle
  apply le_antisymm (limsup_le_of_le (isCoboundedUnder_le_of_le atTop r_nonneg) (.of_forall r_le))
  apply le_of_forall_sub_le
  intro ε hε
  refine le_limsup_of_frequently_le (frequently_atTop.mpr fun K => ?_)
    (isBoundedUnder_of ⟨1, r_le⟩)
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / ε)
  obtain ⟨j, p, hpj, hpbig⟩ := large_prime (max (n K) M)
  have hp := Nat.prime_of_mem_primeFactors hpj
  have hex : ∃ k, p ∣ n k := ⟨j, Nat.dvd_of_mem_primeFactors hpj⟩
  let k := Nat.find hex
  have hpk : p ∣ n k := Nat.find_spec hex
  have hk : K ≤ k := by
    by_contra! h
    have hle := (Nat.le_of_dvd (hnpos k) hpk).trans (hn.monotone h.le)
    omega
  refine ⟨k, hk, ?_⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hMp : (M : ℝ) < p := by exact_mod_cast (le_max_right (n K) M).trans_lt hpbig
  have hinv : 1 / (p : ℝ) ≤ ε := (div_le_iff₀ hpR).mpr (by
    exact ((div_lt_iff₀ hε).mp (hM.trans hMp)).le.trans_eq (mul_comm _ _))
  have hdiv : ((n k / p : ℕ) : ℝ) ≤ (n k : ℝ) * ε := by
    calc
      _ ≤ (n k : ℝ) / p := Nat.cast_div_le
      _ = (n k : ℝ) * (1 / (p : ℝ)) := by simp [div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg _)
  have hcount := NewFractions.first_prime_count n hp hpk (fun _ hj => Nat.find_min hex hj)
  have hcast : ((n k - n k / p : ℕ) : ℝ) ≤ (phiSeq n k : ℝ) := by exact_mod_cast hcount
  rw [Nat.cast_sub (Nat.div_le_self _ _)] at hcast
  change 1 - ε ≤ (phiSeq n k : ℝ) / (n k : ℝ)
  rw [le_div_iff₀ (hnposR k)]
  linarith
