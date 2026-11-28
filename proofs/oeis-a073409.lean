import OMAStatements.S_oeis_a073409
import Mathlib

/-!
# Proof of the conjecture in OEIS A073409 (Thomas Ordowski, May 17 2020)

`a(n)` is the largest prime factor of the denominator of the Bernoulli number `B(2n)`. Claim: for
`n > 0`, `a(n)` is the largest prime `p <= 2n+1` with `p * num(B(2n)) == - den(B(2n)) (mod p^2)`.

The claim is a corollary of the von Staudt-Clausen theorem, which is in Mathlib
(`Bernoulli.vonStaudt_clausen`). Let `S` be the set of primes `q <= 2n+1` with `(q-1) | 2n`, `P` the
product of `S`, and `c(q)` the product of `S` without `q`.
1. `B(2n) + sum_{q in S} 1/q = I` is an integer, so `B(2n) = M / P` with `M = I*P - sum_{q in S} c(q)`.
2. A prime `q` in `S` divides `P` and every `c(r)` with `r != q`, but not `c(q)`; so it does not divide
   `M`. Hence `M / P` is in lowest terms: `num(B(2n)) = M` and `den(B(2n)) = P`.
3. For `p` in `S`: `p*M + P = p*I*P - p * sum_{r != p} c(r)` because `p*c(p) = P`, and `p^2` divides
   every term on the right. So `p` satisfies the congruence.
4. The prime factors of `P` are the members of `S`; `S` contains `2`, so `a(n)` is a member of `S`:
   it is a prime `<= 2n+1` and satisfies the congruence.
5. Conversely a prime `p` with `p^2 | p*num + den` divides `den`, so it is at most `a(n)`.
-/

namespace A073409

/-- The cofactor of `q` in the product of `S`. -/
private def cof (S : Finset ℕ) (q : ℕ) : ℕ := ∏ r ∈ S.erase q, r

private lemma mul_cof {S : Finset ℕ} {q : ℕ} (hq : q ∈ S) : q * cof S q = ∏ r ∈ S, r :=
  Finset.mul_prod_erase S (fun r => r) hq

private lemma dvd_cof {S : Finset ℕ} {q r : ℕ} (hq : q ∈ S) (hne : q ≠ r) : q ∣ cof S r :=
  Finset.dvd_prod_of_mem (fun r => r) (Finset.mem_erase.mpr ⟨hne, hq⟩)

private lemma not_dvd_cof {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) {q : ℕ} (hq : q ∈ S) :
    ¬ q ∣ cof S q := by
  intro h
  obtain ⟨r, hr, hqr⟩ := (Prime.dvd_finsetProd_iff (hS q hq).prime _).mp h
  have hr' := Finset.mem_erase.mp hr
  exact hr'.1 ((Nat.prime_dvd_prime_iff_eq (hS q hq) (hS r hr'.2)).mp hqr).symm

/-- The numerator of `I - ∑ q ∈ S, 1 / q` over the common denominator `∏ r ∈ S, r`. -/
private def numer (S : Finset ℕ) (I : ℤ) : ℤ :=
  I * ((∏ r ∈ S, r : ℕ) : ℤ) - ∑ q ∈ S, (cof S q : ℤ)

private lemma sum_cof_split {S : Finset ℕ} {p : ℕ} (hp : p ∈ S) :
    ∃ t : ℤ, ∑ q ∈ S, (cof S q : ℤ) = cof S p + p * t := by
  rw [← Finset.add_sum_erase S _ hp]
  have h : (p : ℤ) ∣ ∑ q ∈ S.erase p, (cof S q : ℤ) := by
    apply Finset.dvd_sum
    intro q hq
    exact Int.natCast_dvd_natCast.mpr (dvd_cof hp (Finset.mem_erase.mp hq).1.symm)
  obtain ⟨t, ht⟩ := h
  exact ⟨t, by rw [ht]⟩

private lemma prod_eq_cast {S : Finset ℕ} {p : ℕ} (hp : p ∈ S) :
    ((∏ r ∈ S, r : ℕ) : ℤ) = p * cof S p := by
  rw [← mul_cof hp]
  push_cast
  ring

private lemma not_dvd_numer {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) (I : ℤ) {q : ℕ} (hq : q ∈ S) :
    ¬ (q : ℤ) ∣ numer S I := by
  intro h
  obtain ⟨t, ht⟩ := sum_cof_split hq
  have hP := prod_eq_cast hq
  apply not_dvd_cof hS hq
  have h1 : (q : ℤ) ∣ I * (q * cof S q) - q * t - numer S I :=
    dvd_sub (dvd_sub ⟨I * cof S q, by ring⟩ (dvd_mul_right _ _)) h
  have h2 : I * ((q : ℤ) * cof S q) - q * t - numer S I = cof S q := by
    unfold numer
    rw [ht, hP]
    ring
  rw [h2] at h1
  exact Int.natCast_dvd_natCast.mp h1

private lemma sq_dvd {S : Finset ℕ} (I : ℤ) {p : ℕ} (hp : p ∈ S) :
    (p : ℤ) ^ 2 ∣ p * numer S I + ((∏ r ∈ S, r : ℕ) : ℤ) := by
  obtain ⟨t, ht⟩ := sum_cof_split hp
  have hP := prod_eq_cast hp
  refine ⟨I * cof S p - t, ?_⟩
  unfold numer
  rw [ht, hP]
  ring

private lemma rat_eq {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) (I : ℤ) (B : ℚ)
    (h : B + ∑ q ∈ S, (1 : ℚ) / q = I) :
    B = (numer S I : ℚ) / ((∏ r ∈ S, r : ℕ) : ℤ) := by
  have hP0 : ((∏ r ∈ S, r : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun q hq => (hS q hq).ne_zero)
  have hsum : ∑ q ∈ S, (1 : ℚ) / q = (∑ q ∈ S, (cof S q : ℚ)) / ((∏ r ∈ S, r : ℕ) : ℚ) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hS q hq).ne_zero
    rw [div_eq_div_iff hq0 hP0, one_mul, ← mul_cof hq]
    push_cast
    ring
  have hnum : (numer S I : ℚ) = I * ((∏ r ∈ S, r : ℕ) : ℚ) - ∑ q ∈ S, (cof S q : ℚ) := by
    unfold numer
    rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_sum]
    simp only [Int.cast_natCast]
  have hB : B = I - ∑ q ∈ S, (1 : ℚ) / q := by linarith
  rw [hB, hsum, hnum, Int.cast_natCast, sub_div, mul_div_assoc, div_self hP0, mul_one]

private lemma num_den {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) (I : ℤ) (B : ℚ)
    (h : B + ∑ q ∈ S, (1 : ℚ) / q = I) :
    B.num = numer S I ∧ B.den = ∏ r ∈ S, r := by
  have hPpos : (0 : ℤ) < ((∏ r ∈ S, r : ℕ) : ℤ) :=
    Int.natCast_pos.mpr (Finset.prod_pos fun q hq => (hS q hq).pos)
  have hcop : Nat.Coprime (numer S I).natAbs ((∏ r ∈ S, r : ℕ) : ℤ).natAbs := by
    rw [Int.natAbs_natCast]
    refine Nat.Coprime.prod_right fun q hq => ?_
    rw [Nat.coprime_comm, (hS q hq).coprime_iff_not_dvd, ← Int.natCast_dvd]
    exact not_dvd_numer hS I hq
  rw [rat_eq hS I B h]
  refine ⟨Rat.num_div_eq_of_coprime hPpos hcop, ?_⟩
  exact Int.natCast_inj.mp (Rat.den_div_eq_of_coprime hPpos hcop)

private lemma core {n : ℕ} (hn : 0 < n) (S : Finset ℕ)
    (hmem : ∀ q, q ∈ S ↔ q < 2 * n + 2 ∧ q.Prime ∧ (q - 1) ∣ 2 * n)
    (I : ℤ) (hI : bernoulli (2 * n) + ∑ q ∈ S, (1 : ℚ) / q = I) :
    IsGreatest
      {p : ℕ | p.Prime ∧ p ≤ 2 * n + 1 ∧
        (p : ℤ) * (bernoulli (2 * n)).num ≡ -((bernoulli (2 * n)).den : ℤ) [ZMOD (p : ℤ) ^ 2]}
      (OMA.S_oeis_a073409.a n) := by
  have hS : ∀ q ∈ S, q.Prime := fun q hq => ((hmem q).mp hq).2.1
  obtain ⟨hnum, hden⟩ := num_den hS I (bernoulli (2 * n)) hI
  have h2 : 2 ∈ S := (hmem 2).mpr ⟨by omega, Nat.prime_two, one_dvd _⟩
  constructor
  · obtain ⟨p, hpS, hp⟩ := Finset.exists_mem_eq_sup S ⟨2, h2⟩ id
    have ha : OMA.S_oeis_a073409.a n = p := by
      unfold OMA.S_oeis_a073409.a
      rw [hden, Nat.primeFactors_prod hS, hp]
      rfl
    rw [ha]
    refine ⟨hS p hpS, by have := ((hmem p).mp hpS).1; omega, ?_⟩
    rw [hnum, hden, Int.modEq_iff_dvd]
    have h3 := sq_dvd I hpS
    have h4 : -((∏ r ∈ S, r : ℕ) : ℤ) - (p : ℤ) * numer S I =
        -((p : ℤ) * numer S I + ((∏ r ∈ S, r : ℕ) : ℤ)) := by ring
    rw [h4]
    exact (dvd_neg).mpr h3
  · rintro p ⟨hp, -, hcong⟩
    have h1 : (p : ℤ) ∣ -((bernoulli (2 * n)).den : ℤ) - (p : ℤ) * (bernoulli (2 * n)).num :=
      dvd_trans (dvd_pow_self _ two_ne_zero) (Int.modEq_iff_dvd.mp hcong)
    have h3 : (p : ℤ) ∣ (p : ℤ) * (-(bernoulli (2 * n)).num) -
        (-((bernoulli (2 * n)).den : ℤ) - (p : ℤ) * (bernoulli (2 * n)).num) :=
      dvd_sub (dvd_mul_right _ _) h1
    have h4 : (p : ℤ) * (-(bernoulli (2 * n)).num) -
        (-((bernoulli (2 * n)).den : ℤ) - (p : ℤ) * (bernoulli (2 * n)).num) =
        ((bernoulli (2 * n)).den : ℤ) := by ring
    rw [h4] at h3
    have h5 : p ∈ (bernoulli (2 * n)).den.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, Int.natCast_dvd_natCast.mp h3, (bernoulli (2 * n)).den_ne_zero⟩
    exact Finset.le_sup (f := id) h5

end A073409

theorem OMA.solution : type_of% @OMA.S_oeis_a073409.main := by
  intro n hn
  obtain ⟨I, hI⟩ := Bernoulli.vonStaudt_clausen n
  exact A073409.core hn _ (fun q => by simp [Finset.mem_filter]) I hI.symm
