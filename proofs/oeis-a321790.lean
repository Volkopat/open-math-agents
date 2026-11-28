import OMAStatements.S_oeis_a321790
import Mathlib

namespace OMA.A321790Proof

open OMA.S_oeis_a321790

/-- A modulus `k > 1` with `2 ^ (k - 1) ≡ 1 [MOD k]` is odd. -/
lemma odd_of_two_pow (k : ℕ) (hk : 1 < k) (h : 2 ^ (k - 1) ≡ 1 [MOD k]) : Odd k := by
  rcases Nat.even_or_odd k with he | ho
  · exfalso
    have h3 : 2 ^ (k - 1) % 2 = 1 % 2 := Nat.ModEq.of_dvd (even_iff_two_dvd.mp he) h
    have h4 : 2 ^ (k - 1) % 2 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
    omega
  · exact ho

/-- Case `k = p * q` with primes `p < q`: some base `b` with `2 < b < p` is a Fermat witness for `k`.
If all of `1, ..., p - 1` were liars, then together with `q - 1` they would give `p` distinct roots of
`X ^ d - 1` in `ZMod q`, where `d = gcd (k - 1) (q - 1)` divides `p - 1`. -/
lemma witness_pq (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (h2 : 2 ^ (p * q - 1) ≡ 1 [MOD p * q]) :
    ∃ b, 2 < b ∧ b < p ∧ ¬ b ^ (p * q - 1) ≡ 1 [MOD p * q] := by
  by_contra hcon0
  have hcon : ∀ b, 2 < b → b < p → b ^ (p * q - 1) ≡ 1 [MOD p * q] := by
    intro b hb1 hb2
    by_contra hb3
    exact hcon0 ⟨b, hb1, hb2, hb3⟩
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hpq1 : p * 1 ≤ p * q := Nat.mul_le_mul (le_refl p) hq.one_le
  have hk1 : 1 < p * q := by omega
  have hodd : (p * q) % 2 = 1 := Nat.odd_iff.mp (odd_of_two_pow _ hk1 h2)
  have heven : Even (p * q - 1) := Nat.even_iff.mpr (by omega)
  have : Fact q.Prime := ⟨hq⟩
  set d := Nat.gcd (p * q - 1) (q - 1) with hd
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_right _ (by omega)
  have hdle : d ≤ p - 1 := by
    have h1 : d ∣ p * q - 1 := Nat.gcd_dvd_left _ _
    have h3 : d ∣ q - 1 := Nat.gcd_dvd_right _ _
    have heq : p * q - 1 = p * (q - 1) + (p - 1) := by
      rw [Nat.mul_sub_one]
      omega
    rw [heq] at h1
    exact Nat.le_of_dvd (by omega) ((Nat.dvd_add_right (h3.mul_left p)).mp h1)
  have hroot : ∀ x : ZMod q, x ^ (p * q - 1) = 1 →
      x ∈ (Polynomial.nthRoots d (1 : ZMod q)).toFinset := by
    intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega)] at hx
      exact zero_ne_one hx
    have hxq : x ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx0
    have hxd : x ^ d = 1 := orderOf_dvd_iff_pow_eq_one.mp
      (Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hx) (orderOf_dvd_of_pow_eq_one hxq))
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_nthRoots hdpos).mpr hxd)
  have hqT : q - 1 ∉ Finset.Icc 1 (p - 1) := by
    rw [Finset.mem_Icc]
    omega
  have hcardT : (insert (q - 1) (Finset.Icc 1 (p - 1))).card = p := by
    rw [Finset.card_insert_of_notMem hqT, Nat.card_Icc]
    omega
  have hTlt : ∀ t ∈ insert (q - 1) (Finset.Icc 1 (p - 1)), t < q := by
    intro t ht
    rw [Finset.mem_insert, Finset.mem_Icc] at ht
    omega
  have hinj : Set.InjOn (fun t : ℕ => (t : ZMod q))
      ((insert (q - 1) (Finset.Icc 1 (p - 1)) : Finset ℕ) : Set ℕ) := by
    intro a ha b hb hab
    have hab' : a % q = b % q := (ZMod.natCast_eq_natCast_iff' a b q).mp hab
    rwa [Nat.mod_eq_of_lt (hTlt a (Finset.mem_coe.mp ha)),
      Nat.mod_eq_of_lt (hTlt b (Finset.mem_coe.mp hb))] at hab'
  have hsub : (insert (q - 1) (Finset.Icc 1 (p - 1))).image (fun t : ℕ => (t : ZMod q)) ⊆
      (Polynomial.nthRoots d (1 : ZMod q)).toFinset := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    apply hroot
    show ((t : ℕ) : ZMod q) ^ (p * q - 1) = 1
    rw [Finset.mem_insert, Finset.mem_Icc] at ht
    rcases ht with rfl | ⟨ht1, ht2⟩
    · rw [Nat.cast_sub hq.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub]
      exact heven.neg_one_pow
    · have hmod : t ^ (p * q - 1) ≡ 1 [MOD p * q] := by
        rcases (show t = 1 ∨ t = 2 ∨ 2 < t by omega) with rfl | rfl | ht3
        · show 1 ^ (p * q - 1) % (p * q) = 1 % (p * q)
          rw [one_pow]
        · exact h2
        · exact hcon t ht3 (by omega)
      have hz := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.ModEq.of_mul_left p hmod)
      push_cast at hz
      exact hz
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, hcardT] at hcard
  have h4 : (Polynomial.nthRoots d (1 : ZMod q)).toFinset.card ≤ d :=
    (Multiset.toFinset_card_le (Polynomial.nthRoots d (1 : ZMod q))).trans
      (Polynomial.card_nthRoots d (1 : ZMod q))
  omega

/-- Case `k = p * p`: the base `p - 1` is a Fermat witness, as `(p - 1) ^ (p ^ 2 - 1) ≡ 1 + p (mod p ^ 2)`;
`p = 3` is excluded since `2 ^ 8` is `4` modulo `9`, so `p ≥ 5` and `2 < p - 1 < p`. -/
lemma witness_sq (p : ℕ) (hp : p.Prime) (h2 : 2 ^ (p * p - 1) ≡ 1 [MOD p * p]) :
    ∃ b, 2 < b ∧ b < p ∧ ¬ b ^ (p * p - 1) ≡ 1 [MOD p * p] := by
  have hp2 := hp.two_le
  have hpp1 : 2 * 2 ≤ p * p := Nat.mul_le_mul hp2 hp2
  have hk1 : 1 < p * p := by omega
  have hodd : (p * p) % 2 = 1 := Nat.odd_iff.mp (odd_of_two_pow _ hk1 h2)
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (Nat.odd_mul.mp (Nat.odd_iff.mpr hodd)).1
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact absurd h2 (by decide)
  have hp5 : 5 ≤ p := by omega
  have h5p : 5 * p ≤ p * p := Nat.mul_le_mul hp5 (le_refl p)
  refine ⟨p - 1, by omega, by omega, ?_⟩
  intro h
  have hz := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  simp only [Nat.cast_pow, Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one] at hz
  have hpp : (p : ZMod (p * p)) ^ 2 = 0 := by
    rw [sq, ← Nat.cast_mul, ZMod.natCast_self]
  have hn : ((p * p - 1 : ℕ) : ZMod (p * p)) = -1 := by
    rw [Nat.cast_sub (show 1 ≤ p * p by omega), ZMod.natCast_self, Nat.cast_one, zero_sub]
  have he : Even (p * p - 1) := Nat.even_iff.mpr (by omega)
  have ho : Odd (p * p - 1 - 1) := Nat.odd_iff.mpr (by omega)
  have hdiv := sq_dvd_add_pow_sub_sub (p : ZMod (p * p)) (-1) (p * p - 1)
  rw [hpp, zero_dvd_iff, hn, he.neg_one_pow, ho.neg_one_pow] at hdiv
  have hrw : (-1 + (p : ZMod (p * p))) = (p : ZMod (p * p)) - 1 := by ring
  rw [hrw, hz] at hdiv
  have hp0 : (p : ZMod (p * p)) = 0 := by linear_combination -hdiv
  rw [ZMod.natCast_eq_zero_iff] at hp0
  have := Nat.le_of_dvd hp.pos hp0
  omega

/-- The claim for `k = p * q` with primes `p ≤ q`. -/
lemma core (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≤ q) (hpsp : Nat.FermatPsp (p * q) 2) :
    leastBase (p * q) < (p * q).minFac := by
  have h2 : 2 ^ (p * q - 1) ≡ 1 [MOD p * q] :=
    (Nat.probablePrime_iff_modEq (p * q) (by norm_num)).mp hpsp.1
  obtain ⟨b, hb2, hbp, hb⟩ : ∃ b, 2 < b ∧ b < p ∧ ¬ b ^ (p * q - 1) ≡ 1 [MOD p * q] := by
    rcases lt_or_eq_of_le hpq with hlt | heq
    · exact witness_pq p q hp hq hlt h2
    · rw [← heq] at h2 ⊢
      exact witness_sq p hp h2
  have hle : leastBase (p * q) ≤ b := by
    unfold leastBase
    exact Nat.sInf_le (show b ∈ {b : ℕ | 2 < b ∧ ¬ b ^ (p * q - 1) ≡ 1 [MOD p * q]} from ⟨hb2, hb⟩)
  have hmin : p ≤ (p * q).minFac := by
    have hne : p * q ≠ 1 := by
      have := Nat.mul_le_mul hp.two_le hq.two_le
      omega
    have hmp : (p * q).minFac.Prime := Nat.minFac_prime hne
    rcases (Nat.Prime.dvd_mul hmp).mp (Nat.minFac_dvd (p * q)) with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hmp hp).mp h
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hmp hq).mp h
      omega
  omega

end OMA.A321790Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a321790.main := by
  intro k hpsp hlen
  obtain ⟨p, q, hl⟩ := List.length_eq_two.mp hlen
  have hk0 : k ≠ 0 := by
    have := hpsp.2.2
    omega
  have hpm : p ∈ k.primeFactorsList := by
    rw [hl]
    simp
  have hqm : q ∈ k.primeFactorsList := by
    rw [hl]
    simp
  have hp : p.Prime := Nat.prime_of_mem_primeFactorsList hpm
  have hq : q.Prime := Nat.prime_of_mem_primeFactorsList hqm
  have hprod : k = p * q := by
    have := Nat.prod_primeFactorsList hk0
    rw [hl] at this
    simpa using this.symm
  subst hprod
  rcases le_total p q with h | h
  · exact OMA.A321790Proof.core p q hp hq h hpsp
  · rw [mul_comm p q] at hpsp ⊢
    exact OMA.A321790Proof.core q p hq hp h hpsp
