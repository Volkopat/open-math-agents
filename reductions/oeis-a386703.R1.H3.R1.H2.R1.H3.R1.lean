import OMAReductions.R_oeis_a386703_R1_H3_R1_H2_R1

/-!
The residue-four cases in Corollary 5 of K. Ono and D. Penniston,
"The 2-adic behavior of the number of partitions into distinct parts",
https://uva.theopenscholar.com/files/ken-ono/files/052.pdf,
give two disjoint families of discriminants. Parameterizing their square
parts makes each remaining problem a search for an odd prime power
obstructing the partition congruence. Credit: @AlfredMelson.
-/
namespace OMA.R_oeis_a386703_R1_H3_R1_H2_R1_H3_R1
open OMA.S_oeis_a386703

/-- The necessity direction of the residue-four classification in Corollary 5. -/
def H1 : Prop := ∀ n : ℕ, q n % 8 = 4 →
  let D := 24*n+1
  (∃ l s : ℕ, l.Prime ∧ D = l*s^2 ∧ D.factorization l % 8 = 3) ∨
  (∃ l r s : ℕ, l.Prime ∧ r.Prime ∧ l ≠ r ∧ l%24 = r%24 ∧
    (l%24 = 1 ∨ l%24 = 5) ∧ D = l*r*s^2 ∧
    D.factorization l % 4 = 1 ∧ D.factorization r % 4 = 1)

/-- A prime to exponent three modulo eight, times a coprime square. -/
def H2 : Prop := ∀ l e s : ℕ, l.Prime → l%24 = 1 → s.Coprime l →
  ∀ n : ℕ, 24*n+1 = l^(8*e+3)*s^2 →
  4096 < n → p n % 4 = 1 →
    ∃ t k : ℕ, t.Prime ∧ t ≠ 2 ∧ t^k ∣ q n ∧ ¬ t^k ∣ p n - 1

/-- Two distinct primes with exponents one modulo four, times a coprime square. -/
def H3 : Prop := ∀ l r e f s : ℕ, l.Prime → r.Prime → l ≠ r →
  l%24 = r%24 → (l%24 = 1 ∨ l%24 = 5) → s.Coprime (l*r) →
  ∀ n : ℕ, 24*n+1 = l^(4*e+1)*r^(4*f+1)*s^2 →
  4096 < n → p n % 4 = 1 →
    ∃ t k : ℕ, t.Prime ∧ t ≠ 2 ∧ t^k ∣ q n ∧ ¬ t^k ∣ p n - 1

lemma square_residue {n l s : ℕ} (h : 24*n+1 = l*s^2) : l%24 = 1 := by
  -- The unit-square test also occurs in PartitionDivisorShape.progression_prime_times_square.
  have units : ∀ a b : ZMod 24, a*b^2 = 1 → a = 1 := by decide +kernel
  have hmod : (l : ZMod 24)*(s : ZMod 24)^2 = 1 := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, ← h]
    norm_num
    rw [show (24 : ZMod 24) = 0 by decide, zero_mul]
  exact (ZMod.natCast_eq_natCast_iff' l 1 24).mp (by simpa using units _ _ hmod)

lemma extract_one {D l s : ℕ} (hp : l.Prime) (hd : D ≠ 0)
    (hs : D = l*s^2) (hv : D.factorization l % 8 = 3) :
    ∃ e t : ℕ, t.Coprime l ∧ D = l^(8*e+3)*t^2 := by
  have sn : s ≠ 0 := by rintro rfl; simp_all
  obtain ⟨a,t,ht,hst⟩ := Nat.exists_eq_pow_mul_and_not_dvd sn l hp.ne_one
  have tn : t ≠ 0 := by rintro rfl; simp_all
  have eq : D = l^(2*a+1)*t^2 := by rw [hs,hst]; simp only [pow_succ, pow_mul, mul_pow]; ring
  have he : D.factorization l = 2*a+1 := by
    rw [eq, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ tn)]
    simp [hp.factorization_pow, Nat.factorization_pow, Nat.factorization_eq_zero_of_not_dvd ht]
  refine ⟨(2*a+1)/8, t, (hp.coprime_iff_not_dvd.mpr ht).symm, ?_⟩
  rwa [show 8*((2*a+1)/8)+3 = 2*a+1 by omega]

lemma extract_two {D l r s : ℕ} (pl : l.Prime) (pr : r.Prime) (hne : l ≠ r)
    (hd : D ≠ 0) (hs : D = l*r*s^2) (hl : D.factorization l % 4 = 1)
    (hr : D.factorization r % 4 = 1) :
    ∃ e f t : ℕ, t.Coprime (l*r) ∧ D = l^(4*e+1)*r^(4*f+1)*t^2 := by
  have sn : s ≠ 0 := by rintro rfl; simp_all
  obtain ⟨a,w,hw,hsw⟩ := Nat.exists_eq_pow_mul_and_not_dvd sn l pl.ne_one
  have wn : w ≠ 0 := by rintro rfl; simp_all
  obtain ⟨b,t,ht,hwt⟩ := Nat.exists_eq_pow_mul_and_not_dvd wn r pr.ne_one
  have tn : t ≠ 0 := by rintro rfl; simp_all
  have hlt : ¬l ∣ t := fun h => hw (hwt ▸ dvd_mul_of_dvd_right h _)
  have eq : D = l^(2*a+1)*r^(2*b+1)*t^2 := by
    rw [hs,hsw,hwt]; simp only [pow_succ, pow_mul, mul_pow]; ring
  have lpos := pl.pos
  have rpos := pr.pos
  have tpos := Nat.pos_of_ne_zero tn
  have he : D.factorization = (Finsupp.single l (2*a+1) + Finsupp.single r (2*b+1)) + 2 • t.factorization := by
    rw [eq,Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul (by positivity) (by positivity),pl.factorization_pow,pr.factorization_pow,
      Nat.factorization_pow]
  rw [he] at hl hr
  simp [hne, hne.symm, Nat.factorization_eq_zero_of_not_dvd hlt,
    Nat.factorization_eq_zero_of_not_dvd ht] at hl hr
  refine ⟨(2*a+1)/4,(2*b+1)/4,t,
    (pl.coprime_iff_not_dvd.mpr hlt).symm.mul_right (pr.coprime_iff_not_dvd.mpr ht).symm,?_⟩
  rwa [show 4*((2*a+1)/4)+1 = 2*a+1 by omega, show 4*((2*b+1)/4)+1 = 2*b+1 by omega]

/-- Divisibility fails precisely when an odd prime power detects the failure. -/
lemma odd_prime_power_iff {A B : ℕ} (ha : A%4 = 1) (hb : B%8 = 4) :
    (¬B ∣ A-1) ↔ ∃ t k : ℕ, t.Prime ∧ t ≠ 2 ∧ t^k ∣ B ∧ ¬t^k ∣ A-1 := by
  constructor
  · intro h
    have nz : A-1 ≠ 0 := by intro hz; exact h (hz ▸ dvd_zero _)
    have bz : B ≠ 0 := by omega
    rw [←Nat.factorization_prime_le_iff_dvd bz nz] at h
    push Not at h
    obtain ⟨t,pt,hlt⟩ := h
    let k := (A-1).factorization t + 1
    have hd : t^k ∣ B := (pt.pow_dvd_iff_le_factorization bz).mpr hlt
    have hm : ¬t^k ∣ A-1 := fun e => (Nat.not_succ_le_self _) ((pt.pow_dvd_iff_le_factorization nz).mp e)
    refine ⟨t,k,pt,?_,hd,hm⟩
    rintro rfl
    by_cases hk : 3 ≤ k
    · have h8 : 8 ∣ B := (pow_dvd_pow 2 hk).trans hd
      omega
    · have h4 : 4 ∣ A-1 := by omega
      exact hm ((pow_dvd_pow 2 (show k ≤ 2 by omega)).trans h4)
  · rintro ⟨_,_,_,_,hd,hm⟩ h
    exact hm (hd.trans h)

theorem main : H1 → H2 → H3 → OMA.R_oeis_a386703_R1_H3_R1_H2_R1.H3 := by
  intro classification single pair n hn _ hp hq _ hdiv
  have full : q n ∣ p n - 1 := by
    obtain ⟨j,hj⟩ := hdiv
    refine ⟨j,?_⟩
    calc p n-1 = 4*((p n-1)/4) := by omega
         _ = 4*(q n/4)*j := by rw [hj]; ring
         _ = q n*j := by rw [show 4*(q n/4) = q n by omega]
  suffices witness : ∃ t k : ℕ, t.Prime ∧ t ≠ 2 ∧ t^k ∣ q n ∧ ¬ t^k ∣ p n-1 by
    exact (odd_prime_power_iff hp hq).mpr witness full
  rcases classification n hq with ⟨l,s,pl,eq,hv⟩ | ⟨l,r,s,pl,pr,ne,modEq,modOr,eq,hl,hr⟩
  · obtain ⟨e,t,copr,he⟩ := extract_one pl (by omega) eq hv
    exact single l e t pl (square_residue eq) copr n he hn hp
  · obtain ⟨e,f,t,copr,he⟩ := extract_two pl pr ne (by omega) eq hl hr
    exact pair l r e f t pl pr ne modEq modOr copr n he hn hp

end OMA.R_oeis_a386703_R1_H3_R1_H2_R1_H3_R1
