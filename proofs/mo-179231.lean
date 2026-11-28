import OMAStatements.S_mo_179231
import Mathlib

namespace OMA.S_mo_179231_Proof

open Polynomial
open scoped Polynomial

private lemma exists_pow_eq_complex (n : ℕ) (hn : 1 ≤ n) (w : ℂ) :
    ∃ z : ℂ, z ^ n = w := by
  have hdeg : (X ^ n - C w : ℂ[X]).degree ≠ 0 := by
    have hmon : (X ^ n - C w : ℂ[X]).Monic := Polynomial.monic_X_pow_sub_C w (by omega)
    rw [Polynomial.degree_eq_natDegree hmon.ne_zero, Polynomial.natDegree_X_pow_sub_C]
    exact_mod_cast (show n ≠ 0 by omega)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (X ^ n - C w : ℂ[X]) hdeg
  refine ⟨z, ?_⟩
  rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, sub_eq_zero] at hz
  exact hz

private lemma forward_dir (m : ℕ) (hm : 2 ≤ m) (g : ℂ[X])
    (hirr : Irreducible (X ^ m - C g : (ℂ[X])[X])) :
    ∀ p : ℕ, p.Prime → p ∣ m → ∀ b : ℂ[X], b ^ p ≠ g := by
  intro p hp hpm b hb
  rcases hpm with ⟨k, rfl⟩
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk' : k = 0 := by omega
    subst hk'
    omega
  have hp2 : 2 ≤ p := hp.two_le
  let q : (ℂ[X])[X] := ∑ j ∈ Finset.range p, (X ^ k) ^ j * (C b) ^ (p - 1 - j)
  have hfac : (X ^ (p * k) - C g : (ℂ[X])[X]) = (X ^ k - C b) * q := by
    rw [← hb, mul_comm p k, pow_mul, map_pow]
    have hgeom : (X ^ k - C b) * ∑ j ∈ Finset.range p, (X ^ k) ^ j * (C b) ^ (p - 1 - j) =
        (X ^ k) ^ p - (C b) ^ p := by
      simpa [mul_comm] using geom_sum₂_mul (X ^ k : (ℂ[X])[X]) (C b) p
    exact hgeom.symm
  have hdeg1 : (X ^ k - C b : (ℂ[X])[X]).natDegree = k :=
    Polynomial.natDegree_X_pow_sub_C
  have hmon1 : (X ^ k - C b : (ℂ[X])[X]).Monic :=
    Polynomial.monic_X_pow_sub_C b (by omega)
  have hmonP : (X ^ (p * k) - C g : (ℂ[X])[X]).Monic :=
    Polynomial.monic_X_pow_sub_C g (by nlinarith)
  have hdegP : (X ^ (p * k) - C g : (ℂ[X])[X]).natDegree = p * k :=
    Polynomial.natDegree_X_pow_sub_C
  have hq0 : q ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hfac
    exact hmonP.ne_zero hfac
  have hdeg_add : (X ^ k - C b : (ℂ[X])[X]).natDegree + q.natDegree = p * k := by
    rw [← Polynomial.natDegree_mul hmon1.ne_zero hq0, ← hfac, hdegP]
  have hdegq : q.natDegree = (p - 1) * k := by
    rw [hdeg1] at hdeg_add
    have : p * k = k + (p - 1) * k := by
      cases p with
      | zero => omega
      | succ p' => simp [Nat.succ_mul]; omega
    omega
  rcases hirr.isUnit_or_isUnit hfac with hu1 | hu2
  · have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu1
    omega
  · have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu2
    have hqpos : 0 < (p - 1) * k := Nat.mul_pos (by omega) (by omega)
    omega

private lemma monic_divisor_gives_pow_eq (m : ℕ) (hm : 2 ≤ m) (g : ℂ[X]) (hg : g ≠ 0)
    (A : (ℂ[X])[X]) (hA_mon : A.Monic) (hdvd : A ∣ (X ^ m - C g)) :
    ∃ c : ℂ[X], c ^ m = g ^ A.natDegree := by
  let K := FractionRing ℂ[X]
  let L := AlgebraicClosure K
  let φ : ℂ[X] →+* L := (algebraMap K L).comp (algebraMap ℂ[X] K)
  have hφ_inj : Function.Injective φ :=
    (algebraMap K L).injective.comp (IsFractionRing.injective ℂ[X] K)
  let AL : L[X] := A.map φ
  have hAL_mon : AL.Monic := hA_mon.map φ
  have hAL_deg : AL.natDegree = A.natDegree := hA_mon.natDegree_map φ
  have hAL_dvd : AL ∣ (X ^ m - C (φ g)) := by
    rcases hdvd with ⟨B, hB⟩
    refine ⟨B.map φ, ?_⟩
    have hmap := congrArg (Polynomial.map φ) hB
    simpa [AL, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      Polynomial.map_mul] using hmap
  have hsplits : AL.Splits := IsAlgClosed.splits AL
  have hAL_prod : AL = (AL.roots.map fun r => X - C r).prod :=
    hsplits.eq_prod_roots_of_monic hAL_mon
  have hroots_card : AL.roots.card = A.natDegree := by
    rw [← hAL_deg]
    exact Polynomial.splits_iff_card_roots.mp hsplits
  have hroot_pow : ∀ r ∈ AL.roots, r ^ m = φ g := by
    intro r hr
    have hr_root : AL.IsRoot r := (Polynomial.mem_roots hAL_mon.ne_zero).mp hr
    have hP_root : (X ^ m - C (φ g) : L[X]).IsRoot r := by
      rcases hAL_dvd with ⟨Q, hQ⟩
      rw [Polynomial.IsRoot.def, hQ, Polynomial.eval_mul, hr_root, zero_mul]
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, sub_eq_zero] at hP_root
    exact hP_root
  have heval0 : φ (A.coeff 0) = (AL.roots.map fun r => -r).prod := by
    have h1 : AL.eval 0 = φ (A.coeff 0) := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map]
    rw [← h1]
    conv_lhs => rw [hAL_prod]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl fun r _ => by simp
  have hpowL : φ ((A.coeff 0) ^ m) = φ (C ((-1 : ℂ) ^ (m * A.natDegree)) * g ^ A.natDegree) := by
    rw [map_pow, heval0, ← Multiset.prod_map_pow]
    have hterm : (AL.roots.map fun r => (-r) ^ m) =
        AL.roots.map (fun _ => (-1 : L) ^ m * φ g) := by
      refine Multiset.map_congr rfl fun r hr => ?_
      rw [neg_eq_neg_one_mul, mul_pow, hroot_pow r hr]
    rw [hterm, Multiset.map_const', Multiset.prod_replicate, hroots_card, mul_pow, ← pow_mul]
    have hneg1 : φ (C (-1 : ℂ)) = (-1 : L) := by
      have : (C (-1 : ℂ) : ℂ[X]) = -1 := by simp
      rw [this, map_neg, map_one]
    simp only [map_mul, map_pow, hneg1]
  have hpowC : (A.coeff 0) ^ m = C ((-1 : ℂ) ^ (m * A.natDegree)) * g ^ A.natDegree :=
    hφ_inj hpowL
  obtain ⟨u, hu⟩ := exists_pow_eq_complex m (by omega) ((-1 : ℂ) ^ (m * A.natDegree))
  have hu_ne : u ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : m ≠ 0)] at hu
    have hpow_ne : ((-1 : ℂ) ^ (m * A.natDegree)) ≠ 0 := pow_ne_zero _ (by norm_num)
    exact hpow_ne hu.symm
  refine ⟨C u⁻¹ * A.coeff 0, ?_⟩
  rw [mul_pow, ← map_pow, hpowC, ← mul_assoc, ← map_mul, inv_pow, hu, inv_mul_cancel₀
    (pow_ne_zero _ (by norm_num)), map_one, one_mul]

private lemma exists_prime_root_of_pow_eq (m d : ℕ) (hd1 : 1 ≤ d) (hdm : d < m)
    (g c : ℂ[X]) (hg : g ≠ 0) (heq : c ^ m = g ^ d) :
    ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ ∃ b : ℂ[X], b ^ p = g := by
  have hc : c ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : m ≠ 0)] at heq
    exact pow_ne_zero d hg heq.symm
  let r := Nat.gcd d m
  have hr_pos : 0 < r := Nat.gcd_pos_of_pos_left m (by omega)
  have hr_le : r ≤ d := Nat.gcd_le_left m (by omega)
  let m' := m / r
  let d' := d / r
  have hm_eq : m = r * m' := (Nat.mul_div_cancel' (Nat.gcd_dvd_right d m)).symm
  have hd_eq : d = r * d' := (Nat.mul_div_cancel' (Nat.gcd_dvd_left d m)).symm
  have hm'_ge2 : 2 ≤ m' := by nlinarith
  have hcop : Nat.Coprime d' m' := Nat.coprime_div_gcd_div_gcd hr_pos
  let p := m'.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpm' : p ∣ m' := Nat.minFac_dvd m'
  have hpm : p ∣ m := dvd_trans hpm' ⟨r, by linarith⟩
  have hpd'_cop : Nat.Coprime p d' := (hcop.coprime_dvd_right hpm').symm
  have hmult_dvd : ∀ z : ℂ, p ∣ g.rootMultiplicity z := by
    intro z
    have hrm := congrArg (fun f : ℂ[X] => Multiset.count z f.roots) heq
    rw [Polynomial.roots_pow, Polynomial.roots_pow, Multiset.count_nsmul, Multiset.count_nsmul,
      Polynomial.count_roots, Polynomial.count_roots] at hrm
    rw [hm_eq, hd_eq, mul_assoc, mul_assoc] at hrm
    have hcancel : m' * c.rootMultiplicity z = d' * g.rootMultiplicity z :=
      Nat.eq_of_mul_eq_mul_left hr_pos hrm
    have hpdvd : p ∣ d' * g.rootMultiplicity z := by
      rw [← hcancel]
      exact dvd_mul_of_dvd_left hpm' _
    exact hpd'_cop.dvd_of_dvd_mul_left hpdvd
  obtain ⟨μ, hμ⟩ := exists_pow_eq_complex p (by have := hp.two_le; omega) g.leadingCoeff
  let M : Multiset ℂ :=
    g.roots.toFinset.val.bind fun z => Multiset.replicate (g.rootMultiplicity z / p) z
  have hM_eq : p • M = g.roots := by
    ext z
    rw [Multiset.count_nsmul, Multiset.count_bind]
    have hcount_M : (g.roots.toFinset.val.map fun w =>
        Multiset.count z (Multiset.replicate (g.rootMultiplicity w / p) w)).sum =
        g.rootMultiplicity z / p := by
      have hsum : (g.roots.toFinset.val.map fun w =>
          Multiset.count z (Multiset.replicate (g.rootMultiplicity w / p) w)).sum =
          ∑ w ∈ g.roots.toFinset, Multiset.count z (Multiset.replicate (g.rootMultiplicity w / p) w) := rfl
      rw [hsum]
      by_cases hz : z ∈ g.roots.toFinset
      · rw [Finset.sum_eq_single z]
        · simp
        · intro w _ hwz
          rw [Multiset.count_replicate, if_neg hwz]
        · intro h
          exact absurd hz h
      · have hrm0 : g.rootMultiplicity z = 0 := by
          rw [← Polynomial.count_roots g]
          exact Multiset.count_eq_zero.mpr (fun h => hz (Multiset.mem_toFinset.mpr h))
        rw [hrm0, Nat.zero_div]
        refine Finset.sum_eq_zero fun w hw => ?_
        have hwz : w ≠ z := fun h => hz (h ▸ hw)
        rw [Multiset.count_replicate, if_neg hwz]
    rw [hcount_M, Nat.mul_div_cancel' (hmult_dvd z), Polynomial.count_roots]
  refine ⟨p, hp, hpm, C μ * (M.map fun z => X - C z).prod, ?_⟩
  have hsplits : g.Splits := IsAlgClosed.splits g
  have hg_prod := hsplits.eq_prod_roots
  rw [mul_pow, ← map_pow, hμ, ← Multiset.prod_nsmul, ← Multiset.map_nsmul, hM_eq]
  exact hg_prod.symm

private lemma backward_dir (m : ℕ) (hm : 2 ≤ m) (g : ℂ[X])
    (hno : ∀ p : ℕ, p.Prime → p ∣ m → ∀ b : ℂ[X], b ^ p ≠ g) :
    Irreducible (X ^ m - C g : (ℂ[X])[X]) := by
  have hg0 : g ≠ 0 := by
    intro h0
    let p := m.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hpm : p ∣ m := Nat.minFac_dvd m
    exact hno p hp hpm 0 (by rw [zero_pow hp.ne_zero, h0])
  have hmonP : (X ^ m - C g : (ℂ[X])[X]).Monic := Polynomial.monic_X_pow_sub_C g (by omega)
  have hdegP : (X ^ m - C g : (ℂ[X])[X]).natDegree = m := Polynomial.natDegree_X_pow_sub_C
  refine ⟨?_, ?_⟩
  · intro hu
    have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  · intro A B hAB
    have hA0 : A ≠ 0 := fun h => hmonP.ne_zero (by rw [hAB, h, zero_mul])
    have hB0 : B ≠ 0 := fun h => hmonP.ne_zero (by rw [hAB, h, mul_zero])
    have hdeg_add : A.natDegree + B.natDegree = m := by
      rw [← Polynomial.natDegree_mul hA0 hB0, ← hAB, hdegP]
    have hlc : A.leadingCoeff * B.leadingCoeff = 1 := by
      rw [← Polynomial.leadingCoeff_mul, ← hAB, hmonP.leadingCoeff]
    have huA_lc : IsUnit A.leadingCoeff := isUnit_iff_exists_inv.mpr ⟨B.leadingCoeff, hlc⟩
    have huB_lc : IsUnit B.leadingCoeff :=
      isUnit_iff_exists_inv.mpr ⟨A.leadingCoeff, by rw [mul_comm, hlc]⟩
    by_cases hAd : A.natDegree = 0
    · left
      rw [Polynomial.eq_C_of_natDegree_eq_zero hAd]
      have hcoeff0 : A.coeff 0 = A.leadingCoeff := by
        rw [Polynomial.leadingCoeff, hAd]
      rw [hcoeff0]
      exact huA_lc.map C
    · by_cases hBd : B.natDegree = 0
      · right
        rw [Polynomial.eq_C_of_natDegree_eq_zero hBd]
        have hcoeff0 : B.coeff 0 = B.leadingCoeff := by
          rw [Polynomial.leadingCoeff, hBd]
        rw [hcoeff0]
        exact huB_lc.map C
      · exfalso
        rcases huA_lc with ⟨u, hu⟩
        let A' : (ℂ[X])[X] := C (↑u⁻¹ : ℂ[X]) * A
        have hA'_mon : A'.Monic := by
          rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, ← hu]
          exact u.inv_mul
        have hA'_deg : A'.natDegree = A.natDegree := by
          dsimp only [A']
          rw [Polynomial.natDegree_C_mul (Units.ne_zero u⁻¹)]
        have hA'_dvd : A' ∣ (X ^ m - C g) := by
          refine ⟨C (↑u : ℂ[X]) * B, ?_⟩
          dsimp only [A']
          calc X ^ m - C g = A * B := hAB
            _ = (C (↑u⁻¹ : ℂ[X]) * C (↑u : ℂ[X])) * (A * B) := by
                rw [← map_mul, u.inv_mul, map_one, one_mul]
            _ = C (↑u⁻¹ : ℂ[X]) * A * (C (↑u : ℂ[X]) * B) := by ring
        obtain ⟨c, hc⟩ := monic_divisor_gives_pow_eq m hm g hg0 A' hA'_mon hA'_dvd
        rw [hA'_deg] at hc
        obtain ⟨p, hp, hpm, b, hb⟩ :=
          exists_prime_root_of_pow_eq m A.natDegree (by omega) (by omega) g c hg0 hc
        exact hno p hp hpm b hb

end OMA.S_mo_179231_Proof

theorem OMA.solution : type_of% @OMA.S_mo_179231.main := by
  intro m hm g
  exact ⟨OMA.S_mo_179231_Proof.forward_dir m hm g, OMA.S_mo_179231_Proof.backward_dir m hm g⟩
