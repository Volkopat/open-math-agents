import OMAReductions.R_oeis_a327943_R1

-- Step oeis-a327943.R1.H1: hypothesis H1 of reduction oeis-a327943.R1
-- Credit: @mburv
-- Per prime power p^e of m: Hensel-type lifting (dvd_sub_pow_of_dvd_sub) and Fermat, then CRT.

namespace OMA_A327943

theorem fermat_int {p : ℕ} (hp : p.Prime) (c : ℤ) : c ^ p ≡ c [ZMOD (p : ℤ)] := by
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  have := Fact.mk hp
  exact ZMod.pow_card _

theorem fermat_iter {p : ℕ} (hp : p.Prime) (c : ℤ) (k : ℕ) : c ^ (p ^ k) ≡ c [ZMOD (p : ℤ)] := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul]
    exact (ih.pow p).trans (fermat_int hp c)

theorem lift {p : ℕ} {x y : ℤ} (h : x ≡ y [ZMOD (p : ℤ)]) (k : ℕ) :
    x ^ (p ^ k) ≡ y ^ (p ^ k) [ZMOD (p : ℤ) ^ (k + 1)] := by
  have h' : (p : ℤ) ∣ y - x := Int.modEq_iff_dvd.mp h
  exact Int.modEq_iff_dvd.mpr (dvd_sub_pow_of_dvd_sub h' k)

theorem stable {p e : ℕ} {b : ℤ} (hb : b ^ p ≡ b [ZMOD (p : ℤ) ^ e]) (k : ℕ) :
    b ^ (p ^ k) ≡ b [ZMOD (p : ℤ) ^ e] := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul]
    exact (ih.pow p).trans hb

theorem local_iff {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (c b : ℤ) :
    c ^ (p ^ e) ≡ b [ZMOD (p : ℤ) ^ e] ↔
      (c ≡ b [ZMOD (p : ℤ)] ∧ b ^ p ≡ b [ZMOD (p : ℤ) ^ e]) := by
  have hdvd : (p : ℤ) ∣ (p : ℤ) ^ e := dvd_pow_self _ (by omega)
  constructor
  · intro h
    refine ⟨(fermat_iter hp c e).symm.trans (h.of_dvd hdvd), ?_⟩
    have h1 : (c ^ p) ^ (p ^ e) ≡ c ^ (p ^ e) [ZMOD (p : ℤ) ^ e] :=
      (lift (fermat_int hp c) e).of_dvd (pow_dvd_pow _ (by omega))
    have h2 : (c ^ p) ^ (p ^ e) = (c ^ (p ^ e)) ^ p := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    rw [h2] at h1
    exact (h.symm.pow p).trans (h1.trans h)
  · rintro ⟨h1, h2⟩
    have h3 : c ^ (p ^ e) ≡ b ^ (p ^ e) [ZMOD (p : ℤ) ^ e] :=
      (lift h1 e).of_dvd (pow_dvd_pow _ (by omega))
    exact h3.trans (stable h2 e)

theorem global_iff (a b : ℤ) (m : ℕ) (hm : 0 < m) :
    a ^ m ≡ b [ZMOD (m : ℤ)] ↔
      ∀ p ∈ m.primeFactors, a ^ m ≡ b [ZMOD (p : ℤ) ^ (m.factorization p)] := by
  constructor
  · intro h p _
    have hd : ((p ^ m.factorization p : ℕ) : ℤ) ∣ (m : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.ordProj_dvd m p)
    push_cast at hd
    exact h.of_dvd hd
  · intro h
    have hprod : (m : ℤ) = ∏ p ∈ m.primeFactors, (p : ℤ) ^ (m.factorization p) := by
      have := Nat.prod_factorization_pow_eq_self (n := m) (by omega)
      rw [Finsupp.prod, Nat.support_factorization] at this
      conv_lhs => rw [← this]
      push_cast
      rfl
    apply Int.modEq_iff_dvd.mpr
    rw [hprod]
    apply Finset.prod_dvd_of_coprime
    · intro p hp q hq hpq
      simp only [Function.onFun]
      have hp' := Nat.prime_of_mem_primeFactors hp
      have hq' := Nat.prime_of_mem_primeFactors hq
      have hc : Nat.Coprime (p ^ m.factorization p) (q ^ m.factorization q) :=
        ((Nat.coprime_primes hp' hq').mpr hpq).pow _ _
      have := Nat.isCoprime_iff_coprime.mpr hc
      push_cast at this
      exact this
    · intro p hp
      exact Int.modEq_iff_dvd.mp (h p hp)

theorem criterion : ∀ (a b : ℤ) (m : ℕ), 0 < m →
    (a ^ m ≡ b [ZMOD (m : ℤ)] ↔ ∀ p ∈ m.primeFactors,
      a ^ (m / p ^ (m.factorization p)) ≡ b [ZMOD (p : ℤ)] ∧
      b ^ p ≡ b [ZMOD (p : ℤ) ^ (m.factorization p)]) := by
  intro a b m hm
  rw [global_iff a b m hm]
  apply forall₂_congr
  intro p hp
  have hp' := Nat.prime_of_mem_primeFactors hp
  have he : 1 ≤ m.factorization p :=
    (Nat.Prime.factorization_pos_of_dvd hp' (by omega) (Nat.dvd_of_mem_primeFactors hp))
  have hm' : a ^ m = (a ^ (m / p ^ (m.factorization p))) ^ (p ^ (m.factorization p)) := by
    rw [← pow_mul, Nat.div_mul_cancel (Nat.ordProj_dvd m p)]
  rw [hm']
  exact local_iff hp' he _ b

end OMA_A327943

theorem OMA.solution : OMA.R_oeis_a327943_R1.H1 := OMA_A327943.criterion
