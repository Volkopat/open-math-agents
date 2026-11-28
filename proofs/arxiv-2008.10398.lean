import OMAStatements.S_arxiv_2008_10398
import Mathlib

/-! # Ample numbers avoiding arbitrarily many initial primes
Thomas Fink, "Recursively abundant and recursively perfect numbers",
Conjecture 1 (arXiv:2008.10398).

Credit: @rleshner. -/

namespace AmpleNumbers

open OMA.S_arxiv_2008_10398

private theorem recurrence (n : ℕ) :
    recursiveDivisors n = 1 + ∑ d ∈ n.properDivisors, recursiveDivisors d := by
  rw [recursiveDivisors, Finset.sum_attach]

private noncomputable def mass (P t : ℕ) : ℝ :=
  ∑ n ∈ (P^t).divisors, (recursiveDivisors n : ℝ) / n

/-- Each pair consisting of a chosen prime and an old divisor extends the
divisor tree at their product. Distinct pairs give distinct tree edges. -/
private theorem mass_step (S : Finset ℕ) (P t : ℕ) (hP : P ≠ 0)
    (hs : ∀ p ∈ S, 1 < p ∧ p ∣ P) :
    (∑ p ∈ S, (1 / (p : ℝ))) * mass P t ≤ mass P (t+1) := by
  classical
  let domain := S ×ˢ (P^t).divisors
  let edges := (P^(t+1)).divisors.sigma Nat.properDivisors
  let f (x : ℕ × ℕ) : Σ _ : ℕ, ℕ := ⟨x.1*x.2,x.2⟩
  let w (e : Σ _ : ℕ, ℕ) : ℝ := (recursiveDivisors e.2 : ℝ) / e.1
  have inj : Set.InjOn f (domain : Set (ℕ × ℕ)) := by
    rintro ⟨p,d⟩ hx ⟨q,e⟩ hy he
    have h₁ : p*d = q*e := congrArg Sigma.fst he
    have h₂ : d = e := congrArg (fun z : Σ _ : ℕ, ℕ => z.2) he
    subst e
    have hd := Nat.pos_of_mem_divisors (Finset.mem_product.mp hx).2
    have hp : p = q := Nat.eq_of_mul_eq_mul_right hd h₁
    simp [hp]
  have sub : domain.image f ⊆ edges := by
    intro e he
    obtain ⟨⟨p,d⟩,hpd,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hp,hd⟩ := Finset.mem_product.mp hpd
    apply Finset.mem_sigma.mpr
    constructor
    · apply Nat.mem_divisors.mpr
      rw [pow_succ, mul_comm (P ^ t) P]
      exact ⟨Nat.mul_dvd_mul (hs _ hp).2 (Nat.mem_divisors.mp hd).1,
        Nat.mul_ne_zero hP (pow_ne_zero _ hP)⟩
    · apply Nat.mem_properDivisors.mpr
      exact ⟨Nat.dvd_mul_left d p,
        lt_mul_of_one_lt_left (Nat.pos_of_mem_divisors hd) (hs _ hp).1⟩
  calc
    _ = ∑ x ∈ domain, w (f x) := by
      rw [mass, Finset.sum_mul_sum, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro d hd
      simp only [w, f, Nat.cast_mul, div_eq_mul_inv, mul_inv_rev, one_mul]
      ring
    _ = ∑ e ∈ domain.image f, w e := (Finset.sum_image inj).symm
    _ ≤ ∑ e ∈ edges, w e :=
      Finset.sum_le_sum_of_subset_of_nonneg sub (by intro e _ _; dsimp [w]; positivity)
    _ = ∑ n ∈ (P^(t+1)).divisors, ∑ d ∈ n.properDivisors,
        (recursiveDivisors d : ℝ) / n := by
      exact (Finset.sum_sigma' (P^(t+1)).divisors Nat.properDivisors
        (fun (n d : ℕ) => (recursiveDivisors d : ℝ) / (n : ℝ))).symm
    _ ≤ mass P (t+1) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [← Finset.sum_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [← Nat.cast_sum]
      exact_mod_cast (Nat.le_add_left _ 1).trans_eq (recurrence n).symm



theorem ample_prime_tail (k : ℕ) : ∃ S : Finset ℕ,
    (∀ p ∈ S, Nat.Prime p ∧ k < p) ∧ 1 < ∑ p ∈ S, (1 / (p : ℝ)) := by
  classical
  by_contra! h
  apply not_summable_one_div_on_primes
  let f := Set.indicator {p : ℕ | Nat.Prime p} (fun p : ℕ ↦ (1 : ℝ) / p)
  have nonneg (p : ℕ) : 0 ≤ f p := Set.indicator_nonneg (fun _ _ ↦ by positivity) _
  apply summable_of_sum_le (c := (∑ p ∈ Finset.range (k+1), f p) + 1) nonneg
  intro t
  change ∑ p ∈ t, f p ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not t (fun p ↦ p ≤ k)]
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun p _ _ ↦ nonneg p)
    intro p hp
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hp).2)
  · let S := (t.filter (fun p ↦ ¬ p ≤ k)).filter Nat.Prime
    have hS : ∀ p ∈ S, Nat.Prime p ∧ k < p := by
      intro p hp
      obtain ⟨ht,hp'⟩ := Finset.mem_filter.mp hp
      exact ⟨hp', Nat.lt_of_not_ge (Finset.mem_filter.mp ht).2⟩
    calc
      _ = ∑ p ∈ S, (1 / (p : ℝ)) := by simp [S, f, Set.indicator_apply, Finset.sum_filter]
      _ ≤ 1 := h S hS


open Filter
open scoped Topology

theorem ample_divisors_growth (P : ℕ) (hP : P ≠ 0) (R : ℝ) (hR : 1 < R) :
    ∃ t : ℕ, ((P ^ t).divisors.card : ℝ) < R ^ t := by
  let d := P.primeFactors.card
  have hpos : 0 < (P : ℝ) ^ d := by exact_mod_cast (pow_pos (Nat.pos_of_ne_zero hP) d)
  have lim := (tendsto_pow_const_div_const_pow_of_one_lt d hR).eventually_lt_const
    (show 0 < 1 / ((P : ℝ) ^ d) by positivity)
  obtain ⟨t, h, ht⟩ := (lim.and (eventually_ge_atTop 1)).exists
  have hcnt : (P ^ t).divisors.card ≤ (t * P) ^ d := by
    rw [Nat.card_divisors (pow_ne_zero _ hP), Nat.primeFactors_pow P (by omega : t ≠ 0)]
    calc
      _ ≤ ∏ _p ∈ P.primeFactors, (t * P) := by
        apply Finset.prod_le_prod'
        intro p _
        simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
        have hpp := Nat.factorization_lt p hP
        nlinarith
      _ = _ := by simp [d]
  have hc : ((P ^ t).divisors.card : ℝ) ≤ (t : ℝ) ^ d * (P : ℝ) ^ d := by
    exact_mod_cast (by simpa only [mul_pow] using hcnt : (P ^ t).divisors.card ≤ t ^ d * P ^ d)
  refine ⟨t, hc.trans_lt ?_⟩
  have hpow : 0 < R ^ t := pow_pos (by linarith) _
  change (t : ℝ) ^ d / R ^ t < 1 / (P : ℝ) ^ d at h
  simpa only [one_mul] using (div_lt_div_iff₀ hpow hpos).mp h

/-- For every bound on the primes to exclude, some positive ample number
has no prime factor at or below that bound (Fink's Conjecture 1). -/
theorem exists_rough_ample (k : ℕ) : ∃ n : ℕ, 0 < n ∧ n < recursiveDivisors n ∧
    ∀ p : ℕ, Nat.Prime p → p ≤ k → ¬ p ∣ n := by
  classical
  obtain ⟨S,hS,hR⟩ := ample_prime_tail k
  let P := ∏ p ∈ S, p
  let R := ∑ p ∈ S, (1 / (p : ℝ))
  have hP : 0 < P := Finset.prod_pos (fun p hp => (hS p hp).1.pos)
  have hs (p) (hp : p ∈ S) : 1 < p ∧ p ∣ P :=
    ⟨(hS p hp).1.one_lt, Finset.dvd_prod_of_mem id hp⟩
  have grow (t : ℕ) : R^t ≤ mass P t := by
    induction t with
    | zero => simp [mass, recurrence 1]
    | succ t ih =>
      rw [pow_succ, mul_comm]
      exact (mul_le_mul_of_nonneg_left ih (le_trans zero_le_one (le_of_lt hR))).trans
        (mass_step S P t hP.ne' hs)
  obtain ⟨t,ht⟩ := ample_divisors_growth P hP.ne' R hR
  have ex : ∃ n ∈ (P^t).divisors, n < recursiveDivisors n := by
    by_contra! h
    have hm : mass P t ≤ ((P^t).divisors.card : ℝ) := calc
      _ ≤ ∑ _n ∈ (P^t).divisors, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        apply (div_le_one (by exact_mod_cast Nat.pos_of_mem_divisors hn)).mpr
        exact_mod_cast h n hn
      _ = _ := by simp
    exact (not_lt_of_ge ((grow t).trans hm)) ht
  obtain ⟨n,hn,ha⟩ := ex
  refine ⟨n,Nat.pos_of_mem_divisors hn,ha,?_⟩
  intro p hp hk hd
  have hpP := hp.dvd_of_dvd_pow (dvd_trans hd (Nat.mem_divisors.mp hn).1)
  obtain ⟨q,hq,hpq⟩ := (hp.prime.dvd_finsetProd_iff id).mp hpP
  have he : p = q := (Nat.prime_dvd_prime_iff_eq hp (hS q hq).1).mp hpq
  exact (not_lt_of_ge hk) (he ▸ (hS q hq).2)

end AmpleNumbers

theorem OMA.solution : type_of% @OMA.S_arxiv_2008_10398.main :=
  AmpleNumbers.exists_rough_ample
