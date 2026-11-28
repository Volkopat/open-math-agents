import OMAStatements.S_oeis_a045473
import Mathlib

open Polynomial UniqueFactorizationMonoid OMA.S_oeis_a045473

private lemma shift_cyclo (p : ℕ) [Fact p.Prime] :
    taylor (1 : ZMod p) (cyclotomic 7 (ZMod p)) = shiftedQuotient p := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  rw [cyclotomic_prime]
  simp [Finset.sum_range_succ, shiftedQuotient, C_ofNat, taylor_X] <;> ring

private lemma order_two {p : ℕ} (hc : p.Coprime 7) :
    orderOf (ZMod.unitOfCoprime p hc) = 2 ↔ p % 7 = 6 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  rw [← orderOf_units, ZMod.coe_unitOfCoprime, CharP.orderOf_eq_two_iff 7 (by decide)]
  change ((p : ZMod 7) = -1) ↔ _
  rw [← (ZMod.val_injective 7).eq_iff, ZMod.val_natCast]
  rfl

private lemma factor_degree {p : ℕ} [Fact p.Prime] (hc : p.Coprime 7)
    {f : Polynomial (ZMod p)} (hd : f ∣ cyclotomic 7 (ZMod p)) (hi : Irreducible f) :
    f.natDegree = orderOf (ZMod.unitOfCoprime p hc) := by
  simpa using natDegree_of_dvd_cyclotomic_of_irreducible
    (p := p) (f := 1) (by simp) hc hd hi

private lemma transfer_factor {K : Type*} [Field K] (a : K) {f : Polynomial K}
    (hm : f.Monic) (hi : Irreducible f) (hd : f.natDegree = 2) :
    (taylor a f).Monic ∧ Irreducible (taylor a f) ∧ (taylor a f).natDegree = 2 := by
  exact ⟨by simpa [Monic, leadingCoeff_taylor] using hm,
    (MulEquiv.irreducible_iff (taylorEquiv a)).2 hi, (natDegree_taylor _ _).trans hd⟩

private lemma char_seven : shiftedQuotient 7 = X ^ 6 := by
  have h7 : (7 : ZMod 7) = 0 := by decide
  have h21 : (21 : ZMod 7) = 0 := by decide
  have h35 : (35 : ZMod 7) = 0 := by decide
  simp [shiftedQuotient, h7, h21, h35]

theorem OMA.solution : type_of% @OMA.S_oeis_a045473.main := by
  classical
  intro p hp
  constructor
  · intro hmod
    have hc : p.Coprime 7 := (Nat.coprime_primes hp.out (by decide)).2 (by omega)
    let c := cyclotomic 7 (ZMod p)
    have hprod : (normalizedFactors c).prod = c :=
      (prod_normalizedFactors_eq (cyclotomic_ne_zero 7 (ZMod p))).trans (cyclotomic.monic 7 (ZMod p)).normalize_eq_self
    have hdeg (f) (hf : f ∈ normalizedFactors c) : f.natDegree = 2 :=
      (factor_degree hc (dvd_of_mem_normalizedFactors hf)
        (irreducible_of_normalized_factor _ hf)).trans ((order_two hc).2 hmod)
    have hcard : (normalizedFactors c).card = 3 := by
      have h := congrArg natDegree hprod
      rw [natDegree_multiset_prod _ (zero_notMem_normalizedFactors _),
        Multiset.map_congr rfl hdeg, Multiset.map_const', Multiset.sum_replicate,
        smul_eq_mul] at h
      change _ = (cyclotomic 7 (ZMod p)).natDegree at h
      rw [natDegree_cyclotomic] at h
      have : Nat.totient 7 = 6 := by decide
      omega
    rcases Multiset.card_eq_three.mp hcard with ⟨f, g, h, hlist⟩
    have props (u) (hu : u ∈ normalizedFactors c) :=
      transfer_factor (1 : ZMod p)
        ((normalize_eq_self_iff_monic (irreducible_of_normalized_factor u hu).ne_zero).1
          (normalize_normalized_factor u hu)) (irreducible_of_normalized_factor u hu) (hdeg u hu)
    obtain ⟨fm, fi, fd⟩ := props f (by simp [hlist])
    obtain ⟨gm, gi, gd⟩ := props g (by simp [hlist])
    obtain ⟨hm, hi, hd⟩ := props h (by simp [hlist])
    refine ⟨_, _, _, fm, gm, hm, fi, gi, hi, fd, gd, hd, ?_⟩
    rw [← taylor_mul, ← taylor_mul, ← shift_cyclo]
    apply congrArg
    simpa [hlist, mul_assoc] using hprod
  · rintro ⟨f, g, h, fm, gm, hm, fi, gi, hi, fd, gd, hd, heq⟩
    have dvdQ : f ∣ shiftedQuotient p := ⟨g*h, by simpa [mul_assoc] using heq.symm⟩
    by_cases h7 : p = 7
    · subst p
      rw [char_seven] at dvdQ
      have hfX := fi.prime.dvd_of_dvd_pow dvdQ
      have hle := natDegree_le_of_dvd hfX (X_ne_zero (R := ZMod 7))
      simp [fd] at hle
    · have hc := (Nat.coprime_primes hp.out (show Nat.Prime 7 by decide)).2 h7
      obtain ⟨u, hu⟩ := dvdQ
      have hu' := congrArg (taylor (-1 : ZMod p)) hu
      rw [← shift_cyclo, taylor_taylor, neg_add_cancel, taylor_zero, taylor_mul] at hu'
      have hi' : Irreducible (taylor (-1 : ZMod p) f) :=
        (MulEquiv.irreducible_iff (taylorEquiv _)).2 fi
      have H := factor_degree hc ⟨_, hu'⟩ hi'
      rw [natDegree_taylor, fd] at H
      exact (order_two hc).1 H.symm
