import OMAStatements.S_mo_499750
import Mathlib

-- Credit: @Pixelstorm44

namespace OMA.R_mo_499750_R3

/-- If p divides k+a, the units digit is p-a and the next quotient increases by one. -/
private theorem shifted_digits {k a p : ℕ} (ha : 0 < a) (hap : a < p)
    (hd : p ∣ k+a) : k % p + a = p ∧ (k+a)/p = k/p + 1 := by
  have hp : 0 < p := by omega
  have hr := Nat.mod_lt k hp
  have hz := Nat.mod_eq_zero_of_dvd hd
  rw [Nat.add_mod, Nat.mod_eq_of_lt hap] at hz
  have hle : p ≤ k % p + a := by
    by_contra! hh
    rw [Nat.mod_eq_of_lt hh] at hz
    omega
  rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega)] at hz
  have hsum : k % p + a = p := by omega
  refine ⟨hsum, ?_⟩
  have he : k + a = (k / p + 1) * p := by
    have ht := Nat.mod_add_div k p
    rw [Nat.add_mul, one_mul, Nat.mul_comm (k/p) p]
    omega
  rw [he, Nat.mul_div_cancel _ hp]

/-- Failure restricts the prime cofactor of every small shift, including for even k+a. -/
theorem cofactor_range {k a p : ℕ} (ha : 0 < a) (hap : a < p)
    (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ k+a) (hn : ¬ (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≤ k % p + k / p % p)) :
    1 ≤ (k+a)/p % p ∧ (k+a)/p % p ≤ a := by
  obtain ⟨hs, hq⟩ := shifted_digits ha hap hd
  have hf : k % p + k / p % p < p := by
    by_contra! h
    exact hn ⟨p, hp, hp2, h⟩
  rw [hq, Nat.add_mod, Nat.mod_eq_of_lt hp.one_lt, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem squarefree_of_ranges {n : ℕ}
    (h : ∀ p, p.Prime → p ∣ n → 1 ≤ n / p % p) : Squarefree n := by
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro p hp hs
  obtain ⟨t, ht⟩ := hs
  have hd : p ∣ n := dvd_trans (dvd_mul_right p p) ⟨t, ht⟩
  have hpos := h p hp hd
  rw [ht, Nat.mul_assoc, Nat.mul_div_cancel_left _ hp.pos, Nat.mul_mod_right] at hpos
  omega

private theorem weighted_local (c : ℕ → ℕ) {p n : ℕ} (hp : p ∈ n.primeFactors) :
    (∑ q ∈ n.primeFactors, c q * (n/q)) ≡ c p * (n/p) [MOD p] := by
  apply Nat.sum_modEq_single (by simp [hp])
  intro q hq hne
  apply Nat.modEq_zero_iff_dvd.mpr
  have pp := Nat.prime_of_mem_primeFactors hp
  have qp := Nat.prime_of_mem_primeFactors hq
  have hc := (Nat.coprime_primes pp qp).mpr hne.symm
  obtain ⟨t, ht⟩ := hc.mul_dvd_of_dvd_of_dvd
    (Nat.dvd_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hq)
  apply dvd_mul_of_dvd_right _ _
  exact ⟨t, by rw [ht, Nat.mul_comm p q, Nat.mul_assoc, Nat.mul_div_cancel_left _ qp.pos]⟩

private theorem weight_local {p n : ℕ} (hp : p ∈ n.primeFactors) :
    (∑ p ∈ n.primeFactors, n/p) ≡ n/p [MOD p] := by
  simpa using weighted_local (fun _ => 1) hp

private theorem combine {n x y : ℕ} (hsq : Squarefree n)
    (h : ∀ p ∈ n.primeFactors, x ≡ y [MOD p]) : x ≡ y [MOD n] := by
  have aux (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ x ≡ y [MOD p]) :
      x ≡ y [MOD ∏ p ∈ s, p] := by
    induction s using Finset.induction_on with
    | empty => simp [Nat.ModEq]; omega
    | @insert p s hout ih =>
      have hsub q (hq : q ∈ s) := hs q (Finset.mem_insert_of_mem hq)
      obtain ⟨hp, hpx⟩ := hs p (Finset.mem_insert_self p s)
      have hc : p.Coprime (∏ q ∈ s, q) := Nat.Coprime.prod_right fun q hq =>
        (Nat.coprime_primes hp (hsub q hq).1).mpr (fun he => hout (he ▸ hq))
      rw [Finset.prod_insert hout, ← Nat.modEq_and_modEq_iff_modEq_mul hc]
      exact ⟨hpx, ih hsub⟩
  simpa only [Nat.prod_primeFactors_of_squarefree hsq] using
    aux n.primeFactors (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, h p hp⟩)

private theorem odd_factor_ne_two {n p : ℕ} (hn : Odd n) (hd : p ∣ n) : p ≠ 2 := by
  rintro rfl
  obtain ⟨t, ht⟩ := hn
  omega

/-- This discharges the first implication in the published Giuga reduction. -/
theorem first_shift {k : ℕ} (ho : Odd (k+1)) (hf : ¬ (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≤ k % p + k / p % p)) :
    Squarefree (k+1) ∧ (∑ p ∈ (k+1).primeFactors, (k+1)/p) ≡ 1 [MOD k+1] := by
  have h p (hp : p.Prime) (hd : p ∣ k+1) : (k+1)/p % p = 1 := by
    obtain ⟨h1,h2⟩ := cofactor_range (by decide : 0 < 1) hp.one_lt hp
      (odd_factor_ne_two ho hd) hd hf
    omega
  have hs := squarefree_of_ranges (n := k+1) fun p hp hd => (h p hp hd).ge
  refine ⟨hs, combine hs fun p hp => (weight_local hp).trans ?_⟩
  exact (h p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)).trans
    (Nat.mod_eq_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt).symm

/-- The two allowed cofactor residues give the polynomial (X-1)(X-2) modulo k+2. -/
theorem second_shift {k : ℕ} (ho : Odd (k+2)) (hf : ¬ (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≤ k % p + k / p % p)) :
    Squarefree (k+2) ∧ ((∑ p ∈ (k+2).primeFactors, (k+2)/p))^2 + 2 ≡ 3 * (∑ p ∈ (k+2).primeFactors, (k+2)/p) [MOD k+2] := by
  have h p (hp : p.Prime) (hd : p ∣ k+2) := by
    have hn := odd_factor_ne_two ho hd
    exact cofactor_range (by decide : 0 < 2) (by have := hp.two_le; omega : 2 < p) hp hn hd hf
  have hs := squarefree_of_ranges (n := k+2) fun p hp hd => (h p hp hd).1
  refine ⟨hs, combine hs fun p hp => ?_⟩
  have pp := Nat.prime_of_mem_primeFactors hp
  obtain ⟨ha, hb⟩ := h p pp (Nat.dvd_of_mem_primeFactors hp)
  have he : (k+2)/p % p = 1 ∨ (k+2)/p % p = 2 := by omega
  have calcPoly (r : ℕ) (hr : (∑ p ∈ (k+2).primeFactors, (k+2)/p) ≡ r [MOD p]) (heq : r^2+2 = 3*r) :
      ((∑ p ∈ (k+2).primeFactors, (k+2)/p))^2 + 2 ≡ 3 * (∑ p ∈ (k+2).primeFactors, (k+2)/p) [MOD p] := by
    exact ((hr.pow 2).add_right 2).trans (heq ▸ (hr.mul_left 3).symm)
  have hw := (weight_local hp).trans (Nat.mod_modEq ((k+2)/p) p).symm
  rcases he with hh | hh
  · exact calcPoly 1 (hw.trans (by rw [hh])) (by decide)
  · exact calcPoly 2 (hw.trans (by rw [hh])) (by decide)

/-- With residue 1 use coefficient two, and with residue 2 use coefficient one.
Every local weighted cofactor then has residue two. -/
private theorem weight_bounds (n : ℕ) :
    let S := ∑ p ∈ n.primeFactors, n / p
    let T := ∑ p ∈ n.primeFactors, (if n / p % p = 1 then 2 else 1) * (n / p)
    S ≤ T ∧ T ≤ 2 * S := by
  dsimp only
  rw [Finset.mul_sum]
  constructor <;> apply Finset.sum_le_sum <;> intro p _ <;> split <;> omega

private theorem composite_weight {n : ℕ} (hn : 2 < n) (ho : Odd n) (hc : ¬ n.Prime) :
    2 < (∑ p ∈ n.primeFactors, n/p) := by
  have hp := Nat.minFac_prime (show n ≠ 1 by omega)
  have hd := Nat.minFac_dvd n
  have hm : n.minFac ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hd, by omega⟩
  have hne := odd_factor_ne_two ho hd
  have hbig := Nat.minFac_le_div (by omega : 0 < n) hc
  have hsum : n/n.minFac ≤ (∑ p ∈ n.primeFactors, n/p) := Finset.single_le_sum
    (f := fun p => n/p) (fun _ _ => Nat.zero_le _) hm
  have := hp.two_le
  omega

private theorem add_modulus_le {n t r : ℕ} (hn : r < n) (ht : r < t) (he : t ≡ r [MOD n]) :
    n + r ≤ t := by
  change t % n = r % n at he
  rw [Nat.mod_eq_of_lt hn] at he
  by_contra! h
  by_cases htn : t < n
  · rw [Nat.mod_eq_of_lt htn] at he
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at he
    omega

private theorem second_density {k : ℕ} (hk : 0 < k) (ho : Odd (k+2)) (hf : ¬ (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≤ k % p + k / p % p))
    (hs : Squarefree (k+2)) (hc : ¬ (k+2).Prime) : k+2+2 ≤ 2 * (∑ p ∈ (k+2).primeFactors, (k+2)/p) := by
  let n := k+2
  have hz : (∑ p ∈ n.primeFactors, (if n/p % p = 1 then 2 else 1) * (n/p)) ≡ 2 [MOD n] := by
    apply combine hs
    intro p hm
    have pp := Nat.prime_of_mem_primeFactors hm
    have hd := Nat.dvd_of_mem_primeFactors hm
    have hne := odd_factor_ne_two ho hd
    have hp : 2 < p := by have := pp.two_le; omega
    obtain ⟨ha, hb⟩ := cofactor_range (by decide : 0 < 2) hp pp hne hd hf
    apply (weighted_local (fun q => if n/q % q = 1 then 2 else 1) hm).trans
    change 1 ≤ n/p % p at ha
    change n/p % p ≤ 2 at hb
    have hr : n/p % p = 1 ∨ n/p % p = 2 := by omega
    rcases hr with hr | hr
    · have hmod : n/p ≡ 1 [MOD p] := hr.trans (Nat.mod_eq_of_lt pp.one_lt).symm
      simpa [hr] using hmod.mul_left 2
    · have hmod : n/p ≡ 2 [MOD p] := hr.trans (Nat.mod_eq_of_lt hp).symm
      simpa [hr] using hmod
  have hn : 2 < n := by dsimp [n]; omega
  have hgt := composite_weight hn ho hc
  exact (add_modulus_le hn (lt_of_lt_of_le hgt (weight_bounds n).1) hz).trans (weight_bounds n).2

/-- Odd k+1 with the Giuga congruence, large cofactor sum if composite,
and all odd prime cofactors of k+2 in the two allowed residue classes. -/
def H1 : Prop := ∀ k : ℕ, 78 < k →
  let n := k + 1
  let S := ∑ p ∈ n.primeFactors, n / p
  Odd n → Squarefree n → S ≡ 1 [MOD n] → (n.Prime ∨ n + 1 ≤ S) →
  (∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ k + 2 →
    1 ≤ (k + 2) / p % p ∧ (k + 2) / p % p ≤ 2) →
  ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≤ k % p + k / p % p

/-- For odd k+2, the cofactor sum satisfies a quadratic congruence. If k+2 is
composite, the sum of the reciprocals of its prime factors is at least
1/2 + 1/(k+2). The odd prime cofactors of k+1 have residue one. -/
def H2 : Prop := ∀ k : ℕ, 78 < k →
  let n := k + 2
  let S := ∑ p ∈ n.primeFactors, n / p
  Odd n → Squarefree n → S ^ 2 + 2 ≡ 3 * S [MOD n] → (n.Prime ∨ n + 2 ≤ 2 * S) →
  (∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ k + 1 → (k + 1) / p % p = 1) →
  ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≤ k % p + k / p % p

theorem main : H1 → H2 → type_of% @OMA.S_mo_499750.main := by
  intro h₁ h₂ k hk
  by_contra hf
  rcases Nat.even_or_odd (k+1) with he | ho
  · have ho : Odd (k+2) := by obtain ⟨t, ht⟩ := he; exact ⟨t, by omega⟩
    obtain ⟨hs, hpoly⟩ := second_shift ho hf
    apply hf (h₂ k hk ho hs hpoly (or_iff_not_imp_left.mpr (second_density (by omega) ho hf hs)) ?_)
    intro p pp hn hd
    obtain ⟨ha,hb⟩ := cofactor_range (by decide : 0 < 1) pp.one_lt pp hn hd hf
    omega
  · obtain ⟨hs, hsum⟩ := first_shift ho hf
    have hlarge : (k+1).Prime ∨ k+1+1 ≤ (∑ p ∈ (k+1).primeFactors, (k+1)/p) := by
      apply or_iff_not_imp_left.mpr
      intro hc
      have hgt := composite_weight (by omega : 2 < k+1) ho hc
      exact add_modulus_le (by omega) (by omega) hsum
    apply hf (h₁ k hk ho hs hsum hlarge ?_)
    intro p pp hn hd
    exact cofactor_range (by decide : 0 < 2) (by have := pp.two_le; omega) pp hn hd hf

end OMA.R_mo_499750_R3
