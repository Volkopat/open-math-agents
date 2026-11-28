import FormalConjectures.OEIS.«38552»

open NumberField OeisA38552

namespace OMA.R_OeisA38552_largestEven_lt_largestOdd_negFundDisc_R1

private theorem exact_of_prime_dvd {p h : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdiv : p ∣ h) (he : Even h) (hpos : 0 < h) (hlt : h < 4 * p) :
    h = 2 * p := by
  have hc : Nat.Coprime 2 p := Nat.prime_two.coprime_iff_not_dvd.mpr
    (fun hd ↦ (hp.eq_one_or_self_of_dvd 2 hd).elim (by decide) hp2.symm)
  have hd : 2 * p ∣ h := hc.mul_dvd_of_dvd_of_dvd (even_iff_two_dvd.mp he) hdiv
  obtain ⟨t, ht⟩ := hd
  have ht0 : 0 < t := by
    by_contra h
    have : t = 0 := by omega
    simp [this] at ht
    omega
  have ht1 : t = 1 := by
    by_contra hh
    have hh2 : 2 ≤ t := by omega
    have hle := Nat.mul_le_mul_left (2 * p) hh2
    omega
  simpa [ht1] using ht

/-- Finite-class-number comparison. The archived odd witnesses and even exclusions cover
the positive even levels in this range. -/
def H1 : Prop :=
  ∀ n e : ℕ, n ≤ 30256 → Even n → Even e → IsFundamentalDiscr (-(e : ℤ)) →
    classNumberOfDiscriminant (-(e : ℤ)) = n →
    (∃ a : ℕ, Odd a ∧ IsFundamentalDiscr (-(a : ℤ)) ∧
      classNumberOfDiscriminant (-(a : ℤ)) = n) →
    ∃ d : ℕ, e < d ∧ Odd d ∧ IsFundamentalDiscr (-(d : ℤ)) ∧
      classNumberOfDiscriminant (-(d : ℤ)) = n

/-- Primitive prime-power norm implies prime torsion. The split ideal above q is
nonprincipal because d > 4q rules out an algebraic integer of norm q. -/
def H2 : Prop :=
  ∀ p q d : ℕ, p.Prime → q.Prime → 2 < q → Odd d → IsFundamentalDiscr (-(d : ℤ)) →
    4 * q < d →
    ∀ x y : ℤ, ¬ (q : ℤ) ∣ x →
      x ^ 2 + (d : ℤ) * y ^ 2 = 4 * (q : ℤ) ^ p →
      p ∣ classNumberOfDiscriminant (-(d : ℤ))

/-- The prime-half case asks for a single primitive norm witness with an even,
positive class number below 4p. The same d must satisfy both tests. -/
def H3 : Prop :=
  ∀ p e : ℕ, 30256 < 2 * p → p.Prime → Even e → IsFundamentalDiscr (-(e : ℤ)) →
    classNumberOfDiscriminant (-(e : ℤ)) = 2 * p →
    IsGreatest {m : ℕ | Even m ∧ IsFundamentalDiscr (-(m : ℤ)) ∧
      classNumberOfDiscriminant (-(m : ℤ)) = 2 * p} e →
    (∃ a : ℕ, Odd a ∧ IsFundamentalDiscr (-(a : ℤ)) ∧
      classNumberOfDiscriminant (-(a : ℤ)) = 2 * p) →
    ∃ (d q : ℕ) (x y : ℤ), e < d ∧ Odd d ∧ IsFundamentalDiscr (-(d : ℤ)) ∧
      q.Prime ∧ 2 < q ∧ 4 * q < d ∧ ¬ (q : ℤ) ∣ x ∧
      x ^ 2 + (d : ℤ) * y ^ 2 = 4 * (q : ℤ) ^ p ∧
      Even (classNumberOfDiscriminant (-(d : ℤ))) ∧
      0 < classNumberOfDiscriminant (-(d : ℤ)) ∧
      classNumberOfDiscriminant (-(d : ℤ)) < 4 * p

/-- Larger even class numbers whose half is not prime. Unlike the prime-half case,
one must account for all prime powers in the odd part of the class number. -/
def H4 : Prop :=
  ∀ n e : ℕ, 30256 < n → Even n → ¬ (n / 2).Prime → Even e →
    IsFundamentalDiscr (-(e : ℤ)) → classNumberOfDiscriminant (-(e : ℤ)) = n →
    IsGreatest {m : ℕ | Even m ∧ IsFundamentalDiscr (-(m : ℤ)) ∧
      classNumberOfDiscriminant (-(m : ℤ)) = n} e →
    (∃ a : ℕ, Odd a ∧ IsFundamentalDiscr (-(a : ℤ)) ∧
      classNumberOfDiscriminant (-(a : ℤ)) = n) →
    ∃ d : ℕ, e < d ∧ Odd d ∧ IsFundamentalDiscr (-(d : ℤ)) ∧
      classNumberOfDiscriminant (-(d : ℤ)) = n

theorem main : H1 → H2 → H3 → H4 →
    type_of% @OeisA38552.largestEven_lt_largestOdd_negFundDisc := by
  intro hsmall harr hprime hrest n k e hn hk he
  have hex : ∃ a : ℕ, Odd a ∧ IsFundamentalDiscr (-(a : ℤ)) ∧
      classNumberOfDiscriminant (-(a : ℤ)) = n := ⟨k, hk.1⟩
  obtain ⟨hev, hfund, hclass⟩ := he.1
  have hw : ∃ d : ℕ, e < d ∧ Odd d ∧ IsFundamentalDiscr (-(d : ℤ)) ∧
      classNumberOfDiscriminant (-(d : ℤ)) = n := by
    by_cases hs : n ≤ 30256
    · exact hsmall n e hs hn hev hfund hclass hex
    · by_cases hp : (n / 2).Prime
      · let p := n / 2
        have hnp : n = 2 * p := by have := even_iff_two_dvd.mp hn; dsimp [p]; omega
        rw [hnp] at hclass he hex ⊢
        obtain ⟨d, q, x, y, hd, ho, hf, hq, hq2, hheight, hcop, hnorm,
          hdEven, hdpos, hdlt⟩ := hprime p e (by omega) hp hev hfund hclass he hex
        have hp2 : p ≠ 2 := by omega
        exact ⟨d, hd, ho, hf,
          exact_of_prime_dvd hp hp2 (harr p q d hp hq hq2 ho hf hheight x y hcop hnorm)
            hdEven hdpos hdlt⟩
      · exact hrest n e (by omega) hn hp hev hfund hclass he hex
  obtain ⟨d, hd, ho, hf, hc⟩ := hw
  exact hd.trans_le (hk.2 (show Odd d ∧ IsFundamentalDiscr (-(d : ℤ)) ∧
    classNumberOfDiscriminant (-(d : ℤ)) = n from ⟨ho, hf, hc⟩))

end OMA.R_OeisA38552_largestEven_lt_largestOdd_negFundDisc_R1
