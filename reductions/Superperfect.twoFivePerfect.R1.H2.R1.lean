import OMAReductions.R_Superperfect_twoFivePerfect_R1

/-! Local divisor sums constrain the radical or remove an entire prime power. -/
-- Reduction Superperfect.twoFivePerfect.R1.H2.R1 of step Superperfect.twoFivePerfect.R1.H2
-- Credit: @lettucrisp

namespace OMA.R_Superperfect_twoFivePerfect_R1_H2_R1

open ArithmeticFunction ArithmeticFunction.sigma
private lemma self_le_sigma (n : ℕ) (hn : 0 < n) : n ≤ σ 1 n := by
  rw [sigma_one_apply]
  exact Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) (Nat.mem_divisors_self _ hn.ne')

private lemma geom_lt_double {p : ℕ} (hp : 2 ≤ p) (e : ℕ) :
    ∑ i ∈ Finset.range (e+1), p^i < 2*p^e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith [Nat.mul_le_mul_left (p^e) hp]

theorem prime_sigma_lt_double (n : ℕ) (hp : (σ 1 n).Prime) : σ 1 n < 2*n := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => exact (Nat.not_prime_zero (by simpa only [ArithmeticFunction.map_zero] using hp)).elim
  | prime_pow p e pp =>
    rw [sigma_one_apply_prime_pow pp]
    exact geom_lt_double pp.two_le e
  | coprime a b ha hb hab _ _ =>
    rw [isMultiplicative_sigma.map_mul_of_coprime hab] at hp
    have h₁ := self_le_sigma a (by omega)
    have h₂ := self_le_sigma b (by omega)
    exact (Nat.not_prime_mul (by omega) (by omega) hp).elim

theorem prime_intermediate_excluded (p : ℕ) (hp : p.Prime) :
    σ 1 ((σ 1 (p^1) / 5) * σ 1 1) ≠ p^1 * 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp only [sigma_one, mul_one, pow_one, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, pow_zero]
  intro h
  have hlt := prime_sigma_lt_double ((1+p)/5) (h.symm ▸ hp)
  omega


-- Every local divisor sum contains p. The radical then obeys an extra congruence.
def H1 : Prop := ∀ p e u : ℕ, p.Prime → p.Coprime u → 0 < u →
  (p : ZMod 5) = 4 → 2 ∣ e+1 → (e ≠ 1 ∨ u ≠ 1) →
  let n := (σ 1 (p^e) / 5) * σ 1 u
  (∀ q ∈ n.primeFactors, p ∣ σ 1 (q ^ n.factorization q)) →
  (σ 1 u : ZMod p) * ∏ q ∈ n.primeFactors, (q : ZMod p) = 5 →
  σ 1 n ≠ p^e*u

-- A local divisor sum prime to p can be stripped from u and its prime power from n.
def H2 : Prop := ∀ p e u q : ℕ, p.Prime → p.Coprime u → 0 < u →
  (p : ZMod 5) = 4 → 2 ∣ e+1 →
  let n := (σ 1 (p^e) / 5) * σ 1 u
  let a := n.factorization q
  let s := σ 1 (q^a)
  q ∈ n.primeFactors → ¬ p ∣ s → s ∣ u →
  σ 1 (n / q^a) ≠ p^e*(u/s)

private lemma geom_mod {p q a : ℕ} (hq : q.Prime) (h : p ∣ σ 1 (q^a)) :
    (q : ZMod p)^a * q = 1 := by
  rw [sigma_one_apply_prime_pow hq] at h
  have hz := (ZMod.natCast_eq_zero_iff _ _).mpr h
  push_cast at hz
  have hg := geom_sum_mul (q : ZMod p) (a+1)
  rw [hz, zero_mul, pow_succ] at hg
  exact sub_eq_zero.mp hg.symm

theorem main : H1 → H2 → OMA.R_Superperfect_twoFivePerfect_R1.H2 := by
  intro good bad p e u pp hcop hu hres hev heq
  let n := (σ 1 (p^e) / 5) * σ 1 u
  change σ 1 n = p^e*u at heq
  have hn : n ≠ 0 := by
    intro h
    rw [h, ArithmeticFunction.map_zero] at heq
    exact (Nat.mul_ne_zero (pow_ne_zero _ pp.ne_zero) hu.ne') heq.symm
  by_cases allp : ∀ q ∈ n.primeFactors, p ∣ σ 1 (q^n.factorization q)
  · apply good p e u pp hcop hu hres hev _ allp _ heq
    · by_contra! h
      obtain ⟨rfl, rfl⟩ := h
      exact prime_intermediate_excluded p pp heq
    · have hd : 5 ∣ σ 1 (p^e) := by
        rw [sigma_one_apply_prime_pow pp]
        apply (ZMod.natCast_eq_zero_iff _ _).mp
        push_cast
        have hm : (p : ZMod 5) = -1 := hres.trans (by decide)
        rw [hm, neg_one_geom_sum, if_pos (even_iff_two_dvd.mpr hev)]
      have h5 : 5*n = σ 1 (p^e) * σ 1 u := by
        dsimp [n]
        rw [← Nat.mul_assoc, Nat.mul_div_cancel' hd]
      have hcast := congrArg (fun x : ℕ => (x : ZMod p)) h5
      rw [sigma_one_apply_prime_pow pp] at hcast
      push_cast at hcast
      have hz : (p : ZMod p) = 0 := ZMod.natCast_self p
      rw [hz, geom_sum_succ'] at hcast
      have he : e ≠ 0 := by omega
      simp [he] at hcast
      have hprod : (n : ZMod p) * ∏ q ∈ n.primeFactors, (q : ZMod p) = 1 := by
        have hfac := congrArg (fun x : ℕ => (x : ZMod p)) (Nat.prod_primeFactors_pow_factorization hn)
        push_cast at hfac
        rw [hfac, ← Finset.prod_mul_distrib]
        exact Finset.prod_eq_one fun q hq => geom_mod (Nat.prime_of_mem_primeFactors hq) (allp q hq)
      change (σ 1 u : ZMod p) * ∏ q ∈ n.primeFactors, (q : ZMod p) = 5
      rw [← hcast, mul_assoc, hprod, mul_one]
  · push Not at allp
    obtain ⟨q, hq, hexc⟩ := allp
    let a := n.factorization q
    let s := σ 1 (q^a)
    have qprime := Nat.prime_of_mem_primeFactors hq
    have hfac : q^a * (n/q^a) = n := Nat.ordProj_mul_ordCompl_eq_self n q
    have hsplit : s * σ 1 (n/q^a) = p^e*u := by
      calc
        _ = σ 1 (q^a * (n/q^a)) :=
          (isMultiplicative_sigma.map_mul_of_coprime ((Nat.coprime_ordCompl qprime hn).pow_left a)).symm
        _ = _ := (congrArg (σ 1) hfac).trans heq
    have hd : s ∣ p^e*u := ⟨_, hsplit.symm⟩
    have hsu : s ∣ u := ((pp.coprime_iff_not_dvd.mpr hexc).symm.pow_right e).dvd_of_dvd_mul_left hd
    apply bad p e u q pp hcop hu hres hev hq hexc hsu
    change σ 1 (n/q^a) = p^e*(u/s)
    apply Nat.eq_of_mul_eq_mul_left (n := s) (sigma_pos 1 _ (pow_ne_zero _ qprime.ne_zero))
    rw [hsplit, Nat.mul_left_comm, Nat.mul_div_cancel' hsu]

end OMA.R_Superperfect_twoFivePerfect_R1_H2_R1
