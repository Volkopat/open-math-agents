import OMAReductions.R_Green93_green_93_variants_bskk_large_R1
import Mathlib

/-!
# Proof of `Green93.green_93.variants.bskk_large.R1.H1`

Elementary self-contained bound on monic integer polynomials of degree `n` with coefficients in
`{0, ..., M}` (`M >= 34`, `(log M)^3 <= n`, `a_0 != 0`) admitting a divisor `g in Z[X]` with
`1 <= deg g <= n^(1/10)`:

1. **Quantitative Kronecker theorem (`quant_kronecker`):** Using Bertrand's postulate (`4d < p <= 8d`),
   Freshman's dream on power sums in `MvPolynomial (Fin d) Z`, `MvPolynomial.esymmAlgEquiv`, and
   Newton's identities (`MvPolynomial.mul_esymm_eq_sum`), every monic `G in Z[X]` of degree `d >= 1`
   with `G(0) != 0` either has all complex roots of unity or has a complex root `|z| > 2^(1/(8d^2))`.
2. **Sparse-coefficient fiber bound (`card_roots_le_of_large_norm`):** For fixed `z` with
   `|z|^q >= M + 1`, freezing coefficients outside multiples of `q` gives unique completion,
   so `#{a | F_a(z) = 0} <= (M + 1)^(n - ceil(n/q))`.
3. **Non-cyclotomic union bound (`card_noncyclotomic_le`):** Cauchy's root bound `|z| <= M + 1`
   bounds every coefficient of a monic factor `G` of degree `<= D = floor(n^(1/10))` by `(M + 2)^D`.
   Taking stride `q = 8 D^2 (clog 2 (M + 1) + 1)` cancels `log(M + 1)` and yields `exp(O(n^(8/15)) - Omega(n^(4/5)))`.
4. **Root-of-unity factors (`card_cyclotomic_le`):** Irreducibility of `cyclotomic m Q` forces
   `totient m <= D`, hence `m <= 2 D^2`. Freezing coordinates not divisible by `m` fixes the sum of
   `L = ceil(n/m)` uniform digits in `{0, ..., M}`, bounded uniformly by `(2 / sqrt L) (M + 1)^L`
   via `(b + eps) mod (M + 1)` double counting and the central binomial bound `C(r, r/2) / 2^r <= 1/sqrt r`.
   Summing over `m <= 2 D^2` gives `O(n^(-1/5))`, yielding `H1` with `c = 1/20`.
-/

namespace OMA.P_Green93_green_93_variants_bskk_large_R1_H1

open Polynomial Finset Classical

/-! ### Section 1: Symmetric Polynomials, Newton Identities, and Quantitative Kronecker -/

private lemma monic_int_complex_roots {G : ℤ[X]} (hG : G.Monic) :
    ∃ z : Fin G.natDegree → ℂ,
      G.map (Int.castRingHom ℂ) = ∏ i : Fin G.natDegree, (X - C (z i)) := by
  set Gc : ℂ[X] := G.map (Int.castRingHom ℂ)
  have hGc_monic : Gc.Monic := hG.map _
  have hdeg : Gc.natDegree = G.natDegree := hG.natDegree_map _
  have hsplits : Gc.Splits := IsAlgClosed.splits Gc
  have hcard : Gc.roots.card = G.natDegree := by
    rw [← hdeg]
    exact Polynomial.splits_iff_card_roots.mp hsplits
  have hprod : Gc = (Gc.roots.map fun r => X - C r).prod := by
    have h := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hGc_monic
      (Polynomial.splits_iff_card_roots.mp hsplits)
    exact h.symm
  let L := Gc.roots.toList
  have hLlen : L.length = G.natDegree := by
    rw [Multiset.length_toList, hcard]
  refine ⟨fun i => L.get (i.cast hLlen.symm), ?_⟩
  rw [hprod]
  have hms : Gc.roots = Multiset.ofList L := (Multiset.coe_toList _).symm
  rw [hms, Multiset.map_coe, Multiset.prod_coe]
  have hofFn : L.map (fun r => X - C r) =
      List.ofFn (fun i : Fin G.natDegree => X - C (L.get (i.cast hLlen.symm))) := by
    apply List.ext_get (by simp [hLlen])
    intro i h1 h2
    simp [List.get_eq_getElem]
  rw [hofFn, List.prod_ofFn]

private lemma multiset_esymm_map_univ {d : ℕ} (z : Fin d → ℂ) (k : ℕ) :
    ((Finset.univ : Finset (Fin d)).val.map z).esymm k =
      MvPolynomial.aeval z (MvPolynomial.esymm (Fin d) ℤ k) := by
  rw [Multiset.esymm, MvPolynomial.esymm, map_sum, Finset.sum_eq_multiset_sum]
  simp only [map_prod, MvPolynomial.aeval_X, Finset.prod_eq_multiset_prod]
  rw [Multiset.powersetCard_map, Multiset.map_map]
  have hval : ((Finset.univ : Finset (Fin d)).powersetCard k).val.map Finset.val =
      (Finset.univ : Finset (Fin d)).val.powersetCard k := by
    simp [Finset.powersetCard, Multiset.map_pmap, Multiset.pmap_eq_map]
  rw [← hval, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun s _ => ?_
  simp [map_multiset_prod, Multiset.map_map, Function.comp_def]

private lemma aeval_esymm_roots {d : ℕ} (G : ℤ[X]) (hG : G.Monic) (hd : G.natDegree = d)
    (z : Fin d → ℂ) (hz : G.map (Int.castRingHom ℂ) = ∏ i : Fin d, (X - C (z i)))
    (k : ℕ) (hk : k ≤ d) :
    MvPolynomial.aeval z (MvPolynomial.esymm (Fin d) ℤ k) =
      (((-1 : ℤ) ^ k * G.coeff (d - k) : ℤ) : ℂ) := by
  set Gc : ℂ[X] := G.map (Int.castRingHom ℂ)
  have hGc_monic : Gc.Monic := hG.map _
  have hGc_deg : Gc.natDegree = d := (hG.natDegree_map _).trans hd
  have hroots : Gc.roots = (Finset.univ : Finset (Fin d)).val.map z := by
    rw [show Gc = ∏ i : Fin d, (X - C (z i)) from hz]
    have hne : (∏ i : Fin d, (X - C (z i)) : ℂ[X]) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _
    rw [Polynomial.roots_prod (f := fun i : Fin d => (X - C (z i) : ℂ[X])) Finset.univ hne]
    simp [Polynomial.roots_X_sub_C]
  have hcard : Gc.roots.card = Gc.natDegree := by
    rw [hroots, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin, hGc_deg]
  have hvieta := Polynomial.coeff_eq_esymm_roots_of_card hcard (k := d - k) (by omega)
  rw [hGc_deg, hGc_monic.leadingCoeff, one_mul, Nat.sub_sub_self hk] at hvieta
  have hcoeff : Gc.coeff (d - k) = (G.coeff (d - k) : ℂ) := by
    simp [Gc, Polynomial.coeff_map]
  rw [hcoeff] at hvieta
  have hes : Gc.roots.esymm k = MvPolynomial.aeval z (MvPolynomial.esymm (Fin d) ℤ k) := by
    rw [hroots]; exact multiset_esymm_map_univ z k
  rw [← hes]
  have hsign : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
    rw [← mul_pow]; norm_num
  have hmul := congrArg (fun x : ℂ => (-1 : ℂ) ^ k * x) hvieta
  rw [← mul_assoc, hsign, one_mul] at hmul
  push_cast
  exact hmul.symm

private lemma eval_symmetric_int {d : ℕ} (G : ℤ[X]) (hG : G.Monic) (hd : G.natDegree = d)
    (z : Fin d → ℂ) (hz : G.map (Int.castRingHom ℂ) = ∏ i : Fin d, (X - C (z i)))
    (P : MvPolynomial (Fin d) ℤ) (hP : P.IsSymmetric) :
    ∃ m : ℤ, MvPolynomial.aeval z P = (m : ℂ) := by
  let e := MvPolynomial.esymmAlgEquiv (Fin d) ℤ (Fintype.card_fin d)
  let Q : MvPolynomial (Fin d) ℤ := e.symm ⟨P, hP⟩
  have hPQ : (e Q).val = P := congrArg Subtype.val (e.apply_symm_apply ⟨P, hP⟩)
  let vals : Fin d → ℤ := fun k => (-1 : ℤ) ^ (k.val + 1) * G.coeff (d - (k.val + 1))
  refine ⟨MvPolynomial.eval vals Q, ?_⟩
  rw [← hPQ]
  have happly : ∀ R : MvPolynomial (Fin d) ℤ,
      MvPolynomial.aeval z (e R).val = ((MvPolynomial.eval vals R : ℤ) : ℂ) := by
    intro R
    induction R using MvPolynomial.induction_on with
    | C a =>
      have : (e (MvPolynomial.C a)).val = MvPolynomial.C a := by
        change ((e (algebraMap ℤ (MvPolynomial (Fin d) ℤ) a)).val) = _
        rw [AlgEquiv.commutes]
        rfl
      rw [this, MvPolynomial.aeval_C, MvPolynomial.eval_C]
      rfl
    | add f g ihf ihg =>
      rw [map_add, Subalgebra.coe_add, map_add, map_add, Int.cast_add, ihf, ihg]
    | mul_X f k ihf =>
      rw [map_mul, Subalgebra.coe_mul, map_mul, map_mul, Int.cast_mul, ihf]
      congr 1
      have hX : (e (MvPolynomial.X k)).val = MvPolynomial.esymm (Fin d) ℤ (k.val + 1) := by
        rw [MvPolynomial.esymmAlgEquiv_apply]
        simp [MvPolynomial.esymmAlgHom]
      rw [hX, MvPolynomial.eval_X]
      exact aeval_esymm_roots G hG hd z hz (k.val + 1) (by omega)
  exact happly Q

private lemma finset_sum_pow_char {R : Type*} [CommSemiring R] {ι : Type*}
    (p : ℕ) [Fact p.Prime] [CharP R p] (s : Finset ι) (f : ι → R) :
    (∑ i ∈ s, f i) ^ p = ∑ i ∈ s, (f i) ^ p := by
  induction s using Finset.induction_on with
  | empty => simp [(Fact.out : p.Prime).ne_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_pow_char, ih]

private lemma psum_prime_mul_sub_pow {d p h : ℕ} (hp : p.Prime) :
    ∃ Q : MvPolynomial (Fin d) ℤ, Q.IsSymmetric ∧
      MvPolynomial.psum (Fin d) ℤ (p * h) - (MvPolynomial.psum (Fin d) ℤ h) ^ p =
        MvPolynomial.C (p : ℤ) * Q := by
  have : Fact p.Prime := ⟨hp⟩
  set F : MvPolynomial (Fin d) ℤ :=
    MvPolynomial.psum (Fin d) ℤ (p * h) - (MvPolynomial.psum (Fin d) ℤ h) ^ p
  have hF_symm : F.IsSymmetric := by
    intro σ
    have h1 := MvPolynomial.psum_isSymmetric (Fin d) ℤ (p * h) σ
    have h2 := MvPolynomial.psum_isSymmetric (Fin d) ℤ h σ
    simp only [F, map_sub, map_pow, h1, h2]
  have hmap_zero : MvPolynomial.map (Int.castRingHom (ZMod p)) F = 0 := by
    simp only [F, map_sub, map_pow]
    have hp1 : MvPolynomial.map (Int.castRingHom (ZMod p)) (MvPolynomial.psum (Fin d) ℤ (p * h)) =
        ∑ i : Fin d, (MvPolynomial.X i : MvPolynomial (Fin d) (ZMod p)) ^ (p * h) := by
      simp [MvPolynomial.psum, map_sum, map_pow]
    have hp2 : MvPolynomial.map (Int.castRingHom (ZMod p)) (MvPolynomial.psum (Fin d) ℤ h) =
        ∑ i : Fin d, (MvPolynomial.X i : MvPolynomial (Fin d) (ZMod p)) ^ h := by
      simp [MvPolynomial.psum, map_sum, map_pow]
    rw [hp1, hp2, finset_sum_pow_char p]
    have heq : ∀ i : Fin d,
        ((MvPolynomial.X i : MvPolynomial (Fin d) (ZMod p)) ^ h) ^ p =
          (MvPolynomial.X i : MvPolynomial (Fin d) (ZMod p)) ^ (p * h) := fun i => by
      rw [← pow_mul, Nat.mul_comm]
    simp_rw [heq]
    exact sub_self _
  have hdvd_coeff : ∀ m : Fin d →₀ ℕ, (p : ℤ) ∣ F.coeff m := by
    intro m
    have h0 : MvPolynomial.coeff m (MvPolynomial.map (Int.castRingHom (ZMod p)) F) = 0 := by
      rw [hmap_zero, MvPolynomial.coeff_zero]
    rw [MvPolynomial.coeff_map] at h0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (F.coeff m) p).mp h0
  let Q : MvPolynomial (Fin d) ℤ :=
    ∑ m ∈ F.support, MvPolynomial.monomial m (F.coeff m / (p : ℤ))
  have hFQ : F = MvPolynomial.C (p : ℤ) * Q := by
    ext m
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    by_cases hm : m ∈ F.support
    · rw [if_pos hm]
      exact (Int.mul_ediv_cancel' (hdvd_coeff m)).symm
    · rw [if_neg hm, mul_zero]
      exact MvPolynomial.notMem_support_iff.mp hm
  have hQ_symm : Q.IsSymmetric := by
    intro σ
    have h1 : MvPolynomial.C (p : ℤ) * MvPolynomial.rename σ Q = MvPolynomial.C (p : ℤ) * Q := by
      calc MvPolynomial.C (p : ℤ) * MvPolynomial.rename σ Q
          = MvPolynomial.rename σ (MvPolynomial.C (p : ℤ)) * MvPolynomial.rename σ Q := by
              rw [MvPolynomial.rename_C]
        _ = MvPolynomial.rename σ (MvPolynomial.C (p : ℤ) * Q) := (map_mul _ _ _).symm
        _ = MvPolynomial.rename σ F := by rw [← hFQ]
        _ = F := hF_symm σ
        _ = MvPolynomial.C (p : ℤ) * Q := hFQ
    have hp0 : (MvPolynomial.C (p : ℤ) : MvPolynomial (Fin d) ℤ) ≠ 0 := by
      intro hc
      have h0 := congrArg (MvPolynomial.coeff 0) hc
      rw [MvPolynomial.coeff_C, if_pos rfl, MvPolynomial.coeff_zero] at h0
      exact hp.ne_zero (Int.natCast_eq_zero.mp h0)
    exact mul_left_cancel₀ hp0 h1
  exact ⟨Q, hQ_symm, hFQ⟩

private lemma aeval_esymm_eq_of_psum_eq {d : ℕ} (u v : Fin d → ℂ)
    (hsum : ∀ h : ℕ, 1 ≤ h → h ≤ d → ∑ i : Fin d, u i ^ h = ∑ i : Fin d, v i ^ h) :
    ∀ k : ℕ, k ≤ d →
      MvPolynomial.aeval u (MvPolynomial.esymm (Fin d) ℤ k) =
      MvPolynomial.aeval v (MvPolynomial.esymm (Fin d) ℤ k) := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp [MvPolynomial.esymm_zero]
    | succ m =>
      have hm1 : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
      have hnewt := MvPolynomial.mul_esymm_eq_sum (Fin d) ℤ (m + 1)
      have hu := congrArg (MvPolynomial.aeval u) hnewt
      have hv := congrArg (MvPolynomial.aeval v) hnewt
      simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum] at hu hv
      apply mul_left_cancel₀ hm1
      rw [hu, hv]
      congr 1
      refine Finset.sum_congr rfl fun a ha => ?_
      have ha1 : a.1 < m + 1 := (Finset.mem_filter.mp ha).2
      have ha_sum : a.1 + a.2 = m + 1 := by
        simpa [Finset.mem_antidiagonal] using (Finset.mem_filter.mp ha).1
      have ha2_pos : 1 ≤ a.2 := by omega
      have ha2_le : a.2 ≤ d := by omega
      have hes : MvPolynomial.aeval u (MvPolynomial.esymm (Fin d) ℤ a.1) =
          MvPolynomial.aeval v (MvPolynomial.esymm (Fin d) ℤ a.1) := ih a.1 ha1 (by omega)
      have hps : MvPolynomial.aeval u (MvPolynomial.psum (Fin d) ℤ a.2) =
          MvPolynomial.aeval v (MvPolynomial.psum (Fin d) ℤ a.2) := by
        simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X]
        exact hsum a.2 ha2_pos ha2_le
      rw [hes, hps]

private lemma prod_X_sub_C_eq_of_esymm_eq {d : ℕ} (u v : Fin d → ℂ)
    (hes : ∀ k : ℕ, k ≤ d →
      MvPolynomial.aeval u (MvPolynomial.esymm (Fin d) ℤ k) =
      MvPolynomial.aeval v (MvPolynomial.esymm (Fin d) ℤ k)) :
    (∏ i : Fin d, (X - C (u i)) : ℂ[X]) = ∏ i : Fin d, (X - C (v i)) := by
  set Pu : ℂ[X] := ∏ i : Fin d, (X - C (u i))
  set Pv : ℂ[X] := ∏ i : Fin d, (X - C (v i))
  have hPu_monic : Pu.Monic := Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hPv_monic : Pv.Monic := Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hPu_deg : Pu.natDegree = d := by
    rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _]
    simp
  have hPv_deg : Pv.natDegree = d := by
    rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _]
    simp
  have hPu_roots : Pu.roots = (Finset.univ : Finset (Fin d)).val.map u := by
    rw [Polynomial.roots_prod (f := fun i : Fin d => (X - C (u i) : ℂ[X])) Finset.univ
      (Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _)]
    simp [Polynomial.roots_X_sub_C]
  have hPv_roots : Pv.roots = (Finset.univ : Finset (Fin d)).val.map v := by
    rw [Polynomial.roots_prod (f := fun i : Fin d => (X - C (v i) : ℂ[X])) Finset.univ
      (Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _)]
    simp [Polynomial.roots_X_sub_C]
  have hPu_card : Pu.roots.card = Pu.natDegree := by
    rw [hPu_roots, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin, hPu_deg]
  have hPv_card : Pv.roots.card = Pv.natDegree := by
    rw [hPv_roots, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin, hPv_deg]
  ext k
  by_cases hk : k ≤ d
  · rw [Polynomial.coeff_eq_esymm_roots_of_card hPu_card (hPu_deg ▸ hk),
      Polynomial.coeff_eq_esymm_roots_of_card hPv_card (hPv_deg ▸ hk),
      hPu_deg, hPv_deg, hPu_monic.leadingCoeff, hPv_monic.leadingCoeff]
    congr 1
    have h1 : Pu.roots.esymm (d - k) = MvPolynomial.aeval u (MvPolynomial.esymm (Fin d) ℤ (d - k)) := by
      rw [hPu_roots]; exact multiset_esymm_map_univ u (d - k)
    have h2 : Pv.roots.esymm (d - k) = MvPolynomial.aeval v (MvPolynomial.esymm (Fin d) ℤ (d - k)) := by
      rw [hPv_roots]; exact multiset_esymm_map_univ v (d - k)
    rw [h1, h2]
    exact hes (d - k) (by omega)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/-- Quantitative Kronecker theorem: every monic `G ∈ ℤ[X]` of degree `d ≥ 1` with `G.coeff 0 ≠ 0`
either has a complex root `z` with `‖z‖ > 2 ^ (1 / (8 * d ^ 2))`, or every complex root of `G`
is a root of unity. -/
private lemma quant_kronecker {G : ℤ[X]} (hG : G.Monic) (hd : 1 ≤ G.natDegree)
    (h0 : G.coeff 0 ≠ 0) :
    (∃ z : ℂ, (G.map (Int.castRingHom ℂ)).eval z = 0 ∧
      (2 : ℝ) ^ ((1 : ℝ) / (8 * (G.natDegree : ℝ) ^ 2)) < ‖z‖) ∨
    (∃ z : ℂ, (G.map (Int.castRingHom ℂ)).eval z = 0 ∧ ∃ m : ℕ, 1 ≤ m ∧ z ^ m = 1) := by
  set d := G.natDegree
  obtain ⟨z, hz⟩ := monic_int_complex_roots hG
  by_cases hbig : ∃ i : Fin d, (2 : ℝ) ^ ((1 : ℝ) / (8 * (d : ℝ) ^ 2)) < ‖z i‖
  · obtain ⟨i, hi⟩ := hbig
    left
    refine ⟨z i, ?_, hi⟩
    rw [hz, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  · push_neg at hbig
    right
    obtain ⟨p, hp, hp_gt, hp_le⟩ := Nat.exists_prime_lt_and_le_two_mul (4 * d) (by omega)
    have hsum_eq : ∀ h : ℕ, 1 ≤ h → h ≤ d → ∑ i : Fin d, (z i ^ p) ^ h = ∑ i : Fin d, z i ^ h := by
      intro h hh1 hhd
      have heq_pow : ∑ i : Fin d, (z i ^ p) ^ h = ∑ i : Fin d, z i ^ (p * h) :=
        Finset.sum_congr rfl fun i _ => by rw [← pow_mul]
      rw [heq_pow]
      obtain ⟨Sh, hSh⟩ := eval_symmetric_int G hG rfl z hz
        (MvPolynomial.psum (Fin d) ℤ h) (MvPolynomial.psum_isSymmetric _ _ _)
      obtain ⟨Sph, hSph⟩ := eval_symmetric_int G hG rfl z hz
        (MvPolynomial.psum (Fin d) ℤ (p * h)) (MvPolynomial.psum_isSymmetric _ _ _)
      obtain ⟨Q, hQ_symm, hFQ⟩ := psum_prime_mul_sub_pow (d := d) (h := h) hp
      obtain ⟨mQ, hmQ⟩ := eval_symmetric_int G hG rfl z hz Q hQ_symm
      have hSh_eq : ∑ i : Fin d, z i ^ h = (Sh : ℂ) := by
        simpa [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X] using hSh
      have hSph_eq : ∑ i : Fin d, z i ^ (p * h) = (Sph : ℂ) := by
        simpa [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X] using hSph
      have hdiff_c : ((Sph - Sh ^ p : ℤ) : ℂ) = ((p * mQ : ℤ) : ℂ) := by
        have h := congrArg (MvPolynomial.aeval z) hFQ
        simp only [map_sub, map_pow, map_mul, MvPolynomial.aeval_C, map_intCast, map_natCast,
          eq_intCast, Int.cast_natCast] at h
        rw [hSph, hSh, hmQ] at h
        push_cast
        exact h
      have hdiff_int : Sph - Sh ^ p = (p : ℤ) * mQ := Int.cast_injective hdiff_c
      have hfermat : (p : ℤ) ∣ Sh ^ p - Sh := (Int.ModEq.pow_prime_eq_self hp Sh).symm.dvd
      have hdvd : (p : ℤ) ∣ Sph - Sh := by
        have hadd := dvd_add (⟨mQ, hdiff_int⟩ : (p : ℤ) ∣ Sph - Sh ^ p) hfermat
        rwa [show Sph - Sh ^ p + (Sh ^ p - Sh) = Sph - Sh by ring] at hadd
      -- Bound |Sh| < 2d and |Sph| <= 2d
      have hnorm_bound : ∀ k : ℕ, k ≤ 8 * d ^ 2 → ‖∑ i : Fin d, z i ^ k‖ ≤ 2 * (d : ℝ) := by
        intro k hk
        calc ‖∑ i : Fin d, z i ^ k‖
            ≤ ∑ i : Fin d, ‖z i ^ k‖ := norm_sum_le _ _
          _ = ∑ i : Fin d, ‖z i‖ ^ k := Finset.sum_congr rfl fun i _ => norm_pow _ _
          _ ≤ ∑ _i : Fin d, ((2 : ℝ) ^ ((1 : ℝ) / (8 * (d : ℝ) ^ 2))) ^ k :=
              Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hbig i) k
          _ = (d : ℝ) * (2 : ℝ) ^ ((k : ℝ) / (8 * (d : ℝ) ^ 2)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
                ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
              congr 2; ring
          _ ≤ (d : ℝ) * (2 : ℝ) ^ (1 : ℝ) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
              rw [div_le_one (by positivity)]
              exact_mod_cast hk
          _ = 2 * (d : ℝ) := by rw [Real.rpow_one]; ring
      have hSh_le : |(Sh : ℝ)| ≤ 2 * (d : ℝ) := by
        have hb := hnorm_bound h (by nlinarith)
        rw [hSh_eq, Complex.norm_intCast] at hb
        exact hb
      have hSph_le : |(Sph : ℝ)| ≤ 2 * (d : ℝ) := by
        have hb := hnorm_bound (p * h) (by nlinarith)
        rw [hSph_eq, Complex.norm_intCast] at hb
        exact hb
      have habs_lt : |(Sph - Sh : ℤ)| < (p : ℤ) := by
        have hr : (|(Sph - Sh : ℤ)| : ℝ) < (p : ℝ) := by
          have hp_r : (4 * (d : ℝ)) < (p : ℝ) := by exact_mod_cast hp_gt
          have htri : |(Sph : ℝ) - (Sh : ℝ)| ≤ |(Sph : ℝ)| + |(Sh : ℝ)| := abs_sub _ _
          push_cast
          linarith
        exact_mod_cast hr
      have heq_int : Sph - Sh = 0 := by
        obtain ⟨c, hc⟩ := hdvd
        by_contra hne
        have hc0 : c ≠ 0 := fun h0 => hne (by simp [hc, h0])
        have h1 : (p : ℤ) ≤ |(Sph - Sh : ℤ)| := by
          rw [hc, abs_mul, abs_of_pos (by exact_mod_cast hp.pos : (0 : ℤ) < p)]
          have : 1 ≤ |c| := Int.one_le_abs hc0
          nlinarith
        omega
      rw [hSph_eq, hSh_eq]
      have : Sph = Sh := sub_eq_zero.mp heq_int
      rw [this]
    have hpoly_eq : (∏ i : Fin d, (X - C (z i ^ p)) : ℂ[X]) = ∏ i : Fin d, (X - C (z i)) :=
      prod_X_sub_C_eq_of_esymm_eq (fun i => z i ^ p) z
        (aeval_esymm_eq_of_psum_eq (fun i => z i ^ p) z hsum_eq)
    have hpow_mem : ∀ w ∈ Finset.univ.image z, w ^ p ∈ Finset.univ.image z := by
      intro w hw
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
      have hroot : (∏ j : Fin d, (X - C (z j)) : ℂ[X]).eval (z i ^ p) = 0 := by
        rw [← hpoly_eq, Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
      rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hroot
      obtain ⟨j, _, hj⟩ := hroot
      have heq : z i ^ p = z j := sub_eq_zero.mp (by simpa using hj)
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, heq.symm⟩
    let i0 : Fin d := ⟨0, hd⟩
    have hz0_ne : z i0 ≠ 0 := by
      intro hz0
      have hev : (G.map (Int.castRingHom ℂ)).eval 0 = 0 := by
        rw [hz, Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ i0) (by simp [hz0])
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map] at hev
      exact h0 (by simpa using hev)
    have hiter : ∀ k : ℕ, z i0 ^ (p ^ k) ∈ Finset.univ.image z := by
      intro k
      induction k with
      | zero => simp [Finset.mem_image_of_mem z (Finset.mem_univ i0)]
      | succ k ih =>
        rw [pow_succ, pow_mul]
        exact hpow_mem _ ih
    have hnotinj : ¬ Set.InjOn (fun k : ℕ => z i0 ^ (p ^ k)) (Finset.range (d + 1) : Set ℕ) := by
      intro hinj
      have hcard_le : (Finset.range (d + 1)).card ≤ (Finset.univ.image z).card :=
        Finset.card_le_card_of_injOn (fun k => z i0 ^ (p ^ k)) (fun k _ => Finset.mem_coe.mpr (hiter k)) hinj
      have him_le : (Finset.univ.image z).card ≤ d := by
        exact Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin])
      rw [Finset.card_range] at hcard_le
      omega
    unfold Set.InjOn at hnotinj
    push_neg at hnotinj
    obtain ⟨a, _, b, _, hab_eq, hab_ne⟩ := hnotinj
    have hlt_or : a < b ∨ b < a := Nat.lt_or_gt_of_ne hab_ne
    have hex_m : ∃ m : ℕ, 1 ≤ m ∧ z i0 ^ m = 1 := by
      rcases hlt_or with hlt | hlt
      · have hpow_lt : p ^ a < p ^ b := Nat.pow_lt_pow_right hp.one_lt hlt
        refine ⟨p ^ b - p ^ a, by omega, ?_⟩
        have hmul : z i0 ^ (p ^ a) * z i0 ^ (p ^ b - p ^ a) = z i0 ^ (p ^ a) * 1 := by
          rw [← pow_add, Nat.add_sub_of_le hpow_lt.le, mul_one, hab_eq]
        exact mul_left_cancel₀ (pow_ne_zero _ hz0_ne) hmul
      · have hpow_lt : p ^ b < p ^ a := Nat.pow_lt_pow_right hp.one_lt hlt
        refine ⟨p ^ a - p ^ b, by omega, ?_⟩
        have hmul : z i0 ^ (p ^ b) * z i0 ^ (p ^ a - p ^ b) = z i0 ^ (p ^ b) * 1 := by
          rw [← pow_add, Nat.add_sub_of_le hpow_lt.le, mul_one, hab_eq.symm]
        exact mul_left_cancel₀ (pow_ne_zero _ hz0_ne) hmul
    refine ⟨z i0, ?_, hex_m⟩
    rw [hz, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i0) (by simp)

/-! ### Section 2: Sparse-Coefficient Fiber Bound -/

private lemma card_div_indices (n q : ℕ) (hq : 1 ≤ q) :
    ((Finset.univ : Finset (Fin n)).filter fun j : Fin n => q ∣ j.val).card =
      (n + q - 1) / q := by
  have hbij : ((Finset.univ : Finset (Fin n)).filter fun j : Fin n => q ∣ j.val).card =
      (Finset.range ((n + q - 1) / q)).card := by
    refine Finset.card_bij (fun j _ => j.val / q) ?_ ?_ ?_
    · intro j hj
      have hjlt : j.val < n := j.isLt
      have hdvd : q ∣ j.val := (Finset.mem_filter.mp hj).2
      rw [Finset.mem_range]
      obtain ⟨k, hk⟩ := hdvd
      rw [hk, Nat.mul_div_cancel_left _ hq]
      have hkq_lt : k * q < n := by nlinarith [Nat.mul_comm k q]
      exact (Nat.lt_div_iff_mul_lt (by omega : 0 < q)).mpr (by omega)
    · intro j₁ hj₁ j₂ hj₂ hdiv
      have h1 : q ∣ j₁.val := (Finset.mem_filter.mp hj₁).2
      have h2 : q ∣ j₂.val := (Finset.mem_filter.mp hj₂).2
      apply Fin.ext
      rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, hdiv]
    · intro k hk
      rw [Finset.mem_range] at hk
      have hkq : k * q < n := by
        have h1 := (Nat.lt_div_iff_mul_lt (by omega : 0 < q)).mp hk
        omega
      refine ⟨⟨k * q, hkq⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, dvd_mul_left q k⟩, ?_⟩
      exact Nat.mul_div_cancel k hq
  rw [hbij, Finset.card_range]

private lemma eval_monicPoly_complex {n : ℕ} (a : Fin n → ℕ) (z : ℂ) :
    ((Green93.monicPoly a).map (Int.castRingHom ℂ)).eval z =
      z ^ n + ∑ j : Fin n, (a j : ℂ) * z ^ j.val := by
  simp [Green93.monicPoly, Polynomial.eval_map, Polynomial.eval₂_add, Polynomial.eval₂_finset_sum]

/-- For fixed `z ∈ ℂ` and stride `q ≥ 1` with `‖z‖ ^ q ≥ M + 1`, freezing coefficients outside
multiples of `q` uniquely determines the remaining coefficients, bounding the zero-set size. -/
private lemma card_roots_le_of_large_norm {M n q : ℕ} (hM : 1 ≤ M) (hq : 1 ≤ q)
    (z : ℂ) (hz : (M + 1 : ℝ) ≤ ‖z‖ ^ q) :
    ((Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
      ((Green93.monicPoly fun j => (a j : ℕ)).map (Int.castRingHom ℂ)).eval z = 0).card ≤
      (M + 1) ^ (n - (n + q - 1) / q) := by
  let S : Finset (Fin n) := Finset.univ.filter fun j => q ∣ j.val
  let T : Finset (Fin n) := Sᶜ
  have hS : S.card = (n + q - 1) / q := card_div_indices n q hq
  have hT : T.card = n - (n + q - 1) / q := by
    rw [Finset.card_compl, Fintype.card_fin, hS]
  let bad := (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
    ((Green93.monicPoly fun j => (a j : ℕ)).map (Int.castRingHom ℂ)).eval z = 0
  have hinj : Set.InjOn (fun (a : Fin n → Fin (M + 1)) (j : T) => a j.val) (bad : Set _) := by
    intro a ha b hb hagree
    by_contra hne
    have hdiff_ne : (Finset.univ.filter fun j : Fin n => a j ≠ b j).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      apply hne; funext j
      by_contra hj
      have : j ∈ Finset.univ.filter fun j : Fin n => a j ≠ b j :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
      rw [hempty] at this; exact Finset.notMem_empty j this
    have hsubS : (Finset.univ.filter fun j : Fin n => a j ≠ b j) ⊆ S := by
      intro j hj
      by_contra hjS
      have hjT : j ∈ T := Finset.mem_compl.mpr hjS
      have heq := congr_fun hagree ⟨j, hjT⟩
      exact (Finset.mem_filter.mp hj).2 heq
    let Dset := Finset.univ.filter fun j : Fin n => a j ≠ b j
    let j0 := Dset.max' hdiff_ne
    have hj0_mem : j0 ∈ Dset := Finset.max'_mem Dset hdiff_ne
    have hj0_S : j0 ∈ S := hsubS hj0_mem
    have hj0_dvd : q ∣ j0.val := (Finset.mem_filter.mp hj0_S).2
    obtain ⟨h, hh⟩ := hj0_dvd
    have ha0 := (Finset.mem_filter.mp ha).2
    have hb0 := (Finset.mem_filter.mp hb).2
    rw [eval_monicPoly_complex] at ha0 hb0
    have hsub_zero : ∑ j ∈ Dset, ((a j : ℂ) - (b j : ℂ)) * z ^ j.val = 0 := by
      have hdiff : ∑ j : Fin n, ((a j : ℂ) - (b j : ℂ)) * z ^ j.val = 0 := by
        have h1 : ∑ j : Fin n, (a j : ℂ) * z ^ j.val = ∑ j : Fin n, (b j : ℂ) * z ^ j.val := by
          linear_combination ha0 - hb0
        calc ∑ j : Fin n, ((a j : ℂ) - (b j : ℂ)) * z ^ j.val
            = ∑ j : Fin n, ((a j : ℂ) * z ^ j.val - (b j : ℂ) * z ^ j.val) :=
                Finset.sum_congr rfl fun j _ => sub_mul _ _ _
          _ = ∑ j : Fin n, (a j : ℂ) * z ^ j.val - ∑ j : Fin n, (b j : ℂ) * z ^ j.val :=
                Finset.sum_sub_distrib _ _
          _ = 0 := sub_eq_zero.mpr h1
      rw [← hdiff]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hjD
      have hab : a j = b j := by
        by_contra hne'; exact hjD (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne'⟩)
      simp [hab]
    have hsplit : ((a j0 : ℂ) - (b j0 : ℂ)) * z ^ j0.val =
        - ∑ j ∈ Dset.erase j0, ((a j : ℂ) - (b j : ℂ)) * z ^ j.val := by
      have h1 := Finset.add_sum_erase _ (fun j : Fin n => ((a j : ℂ) - (b j : ℂ)) * z ^ j.val) hj0_mem
      exact eq_neg_of_add_eq_zero_left (h1.trans hsub_zero)
    set r : ℝ := ‖z‖ ^ q
    have hr_ge : (M + 1 : ℝ) ≤ r := hz
    have hr_gt1 : (1 : ℝ) < r := by
      have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      linarith
    have hcoeff_ge1 : (1 : ℝ) ≤ ‖(a j0 : ℂ) - (b j0 : ℂ)‖ := by
      have hab_ne : (a j0 : ℕ) ≠ (b j0 : ℕ) := fun e => (Finset.mem_filter.mp hj0_mem).2 (Fin.ext e)
      have hz_ne : ((a j0 : ℤ) - (b j0 : ℤ)) ≠ 0 := by omega
      have h1 : (1 : ℤ) ≤ |(a j0 : ℤ) - (b j0 : ℤ)| := Int.one_le_abs hz_ne
      have hcast : ((a j0 : ℂ) - (b j0 : ℂ)) = (((a j0 : ℤ) - (b j0 : ℤ) : ℤ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.norm_intCast]
      exact_mod_cast h1
    have hLHS : r ^ h ≤ ‖((a j0 : ℂ) - (b j0 : ℂ)) * z ^ j0.val‖ := by
      rw [norm_mul, norm_pow, hh, pow_mul]
      calc r ^ h = 1 * r ^ h := (one_mul _).symm
        _ ≤ ‖(a j0 : ℂ) - (b j0 : ℂ)‖ * r ^ h := mul_le_mul_of_nonneg_right hcoeff_ge1 (by positivity)
    have hRHS : ‖- ∑ j ∈ Dset.erase j0, ((a j : ℂ) - (b j : ℂ)) * z ^ j.val‖ ≤ r ^ h - 1 := by
      rw [norm_neg]
      have h1 : ‖∑ j ∈ Dset.erase j0, ((a j : ℂ) - (b j : ℂ)) * z ^ j.val‖ ≤
          ∑ j ∈ Dset.erase j0, (M : ℝ) * r ^ (j.val / q) := by
        calc ‖∑ j ∈ Dset.erase j0, ((a j : ℂ) - (b j : ℂ)) * z ^ j.val‖
            ≤ ∑ j ∈ Dset.erase j0, ‖((a j : ℂ) - (b j : ℂ)) * z ^ j.val‖ := norm_sum_le _ _
          _ ≤ ∑ j ∈ Dset.erase j0, (M : ℝ) * r ^ (j.val / q) := by
              refine Finset.sum_le_sum fun j hj => ?_
              have hjD : j ∈ Dset := Finset.mem_of_mem_erase hj
              have hjdvd : q ∣ j.val := (Finset.mem_filter.mp (hsubS hjD)).2
              rw [norm_mul, norm_pow]
              have hpow : ‖z‖ ^ j.val = r ^ (j.val / q) := by
                rw [show r = ‖z‖ ^ q from rfl, ← pow_mul, Nat.mul_div_cancel' hjdvd]
              rw [hpow]
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              have hcast : ((a j : ℂ) - (b j : ℂ)) = (((a j : ℤ) - (b j : ℤ) : ℤ) : ℂ) := by push_cast; ring
              rw [hcast, Complex.norm_intCast]
              have ha_le : (a j : ℕ) ≤ M := Nat.lt_succ_iff.mp (a j).isLt
              have hb_le : (b j : ℕ) ≤ M := Nat.lt_succ_iff.mp (b j).isLt
              have habs : |(a j : ℤ) - (b j : ℤ)| ≤ M := by rw [abs_le]; omega
              exact_mod_cast habs
      have h2 : ∑ j ∈ Dset.erase j0, (M : ℝ) * r ^ (j.val / q) ≤
          ∑ i ∈ Finset.range h, (M : ℝ) * r ^ i := by
        have hmap : ∑ j ∈ Dset.erase j0, (M : ℝ) * r ^ (j.val / q) =
            ∑ i ∈ (Dset.erase j0).image (fun j : Fin n => j.val / q), (M : ℝ) * r ^ i := by
          symm
          apply Finset.sum_image
          intro j₁ hj₁ j₂ hj₂ heq
          dsimp only at heq
          have hd₁ : q ∣ j₁.val := (Finset.mem_filter.mp (hsubS (Finset.mem_of_mem_erase hj₁))).2
          have hd₂ : q ∣ j₂.val := (Finset.mem_filter.mp (hsubS (Finset.mem_of_mem_erase hj₂))).2
          apply Fin.ext
          rw [← Nat.mul_div_cancel' hd₁, ← Nat.mul_div_cancel' hd₂, heq]
        rw [hmap]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
          rw [Finset.mem_range]
          have hj_le : j ≤ j0 := Finset.le_max' Dset j (Finset.mem_of_mem_erase hj)
          have hj_ne : j ≠ j0 := Finset.ne_of_mem_erase hj
          have hj_lt : j.val < j0.val := lt_of_le_of_ne hj_le (fun e => hj_ne (Fin.ext e))
          have hjdvd : q ∣ j.val := (Finset.mem_filter.mp (hsubS (Finset.mem_of_mem_erase hj))).2
          rw [hh] at hj_lt
          have := Nat.mul_div_cancel' hjdvd
          nlinarith
        · intro i _ _; positivity
      have hgeom : ∑ i ∈ Finset.range h, (M : ℝ) * r ^ i = (M : ℝ) * ((r ^ h - 1) / (r - 1)) := by
        rw [← Finset.mul_sum, geom_sum_eq hr_gt1.ne']
      have h3 : (M : ℝ) * ((r ^ h - 1) / (r - 1)) ≤ r ^ h - 1 := by
        have hr1 : 0 < r - 1 := by linarith
        have hrM : (M : ℝ) ≤ r - 1 := by linarith
        have hrpow : 0 ≤ r ^ h - 1 := by
          have : (1 : ℝ) ≤ r ^ h := one_le_pow₀ (by linarith)
          linarith
        calc (M : ℝ) * ((r ^ h - 1) / (r - 1))
            ≤ (r - 1) * ((r ^ h - 1) / (r - 1)) :=
              mul_le_mul_of_nonneg_right hrM (div_nonneg hrpow hr1.le)
          _ = r ^ h - 1 := mul_div_cancel₀ _ hr1.ne'
      linarith
    rw [hsplit] at hLHS
    linarith
  have hcard := Finset.card_le_card_of_injOn (fun (a : Fin n → Fin (M + 1)) (j : T) => a j.val)
    (fun _ _ => Finset.mem_univ _) hinj
  simpa [Fintype.card_fun, Fintype.card_fin, hT] using hcard

/-! ### Section 3: Cauchy Root Bound and Non-Cyclotomic Factor Union Bound -/

private lemma cauchy_root_bound {M n : ℕ} (hM : 1 ≤ M) (a : Fin n → Fin (M + 1))
    (z : ℂ) (hz : ((Green93.monicPoly fun j => (a j : ℕ)).map (Int.castRingHom ℂ)).eval z = 0) :
    ‖z‖ ≤ (M + 1 : ℝ) := by
  by_contra hgt
  push_neg at hgt
  rw [eval_monicPoly_complex] at hz
  have hzn : z ^ n = - ∑ j : Fin n, (a j : ℂ) * z ^ j.val := eq_neg_of_add_eq_zero_left hz
  have h1 : ‖z‖ ^ n = ‖- ∑ j : Fin n, (a j : ℂ) * z ^ j.val‖ := by
    rw [← norm_pow, hzn]
  have hr1 : (1 : ℝ) < ‖z‖ := by
    have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have h2 : ‖- ∑ j : Fin n, (a j : ℂ) * z ^ j.val‖ ≤ ‖z‖ ^ n - 1 := by
    rw [norm_neg]
    calc ‖∑ j : Fin n, (a j : ℂ) * z ^ j.val‖
        ≤ ∑ j : Fin n, ‖(a j : ℂ) * z ^ j.val‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin n, (M : ℝ) * ‖z‖ ^ j.val := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul, norm_pow, Complex.norm_natCast]
          have : ((a j : ℕ) : ℝ) ≤ M := by exact_mod_cast Nat.lt_succ_iff.mp (a j).isLt
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ = (M : ℝ) * ∑ i ∈ Finset.range n, ‖z‖ ^ i := by
          rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => ‖z‖ ^ i) n]
      _ = (M : ℝ) * ((‖z‖ ^ n - 1) / (‖z‖ - 1)) := by rw [geom_sum_eq hr1.ne']
      _ ≤ ‖z‖ ^ n - 1 := by
          have hz1 : 0 < ‖z‖ - 1 := by linarith
          have hzM : (M : ℝ) ≤ ‖z‖ - 1 := by linarith
          have hzn1 : 0 ≤ ‖z‖ ^ n - 1 := by
            have : (1 : ℝ) ≤ ‖z‖ ^ n := one_le_pow₀ (by linarith)
            linarith
          calc (M : ℝ) * ((‖z‖ ^ n - 1) / (‖z‖ - 1))
              ≤ (‖z‖ - 1) * ((‖z‖ ^ n - 1) / (‖z‖ - 1)) :=
                mul_le_mul_of_nonneg_right hzM (div_nonneg hzn1 hz1.le)
            _ = ‖z‖ ^ n - 1 := mul_div_cancel₀ _ hz1.ne'
  linarith

private lemma monic_coeff_bound_of_roots {G : ℤ[X]} (hG : G.Monic) (B : ℕ)
    (hroots : ∀ z : ℂ, (G.map (Int.castRingHom ℂ)).eval z = 0 → ‖z‖ ≤ (B : ℝ)) :
    ∀ k : ℕ, k < G.natDegree → |G.coeff k| ≤ ((B + 1 : ℕ) ^ G.natDegree : ℤ) := by
  set d := G.natDegree
  obtain ⟨z, hz⟩ := monic_int_complex_roots hG
  intro k hk
  have hz_le : ∀ i : Fin d, ‖z i‖ ≤ (B : ℝ) := fun i => by
    apply hroots (z i)
    rw [hz, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hes := aeval_esymm_roots G hG rfl z hz (d - k) (by omega)
  rw [Nat.sub_sub_self hk.le] at hes
  have hnorm : |(G.coeff k : ℝ)| ≤ (Nat.choose d (d - k) : ℝ) * (B : ℝ) ^ (d - k) := by
    have h1 : ‖(((-1 : ℤ) ^ (d - k) * G.coeff k : ℤ) : ℂ)‖ = |(G.coeff k : ℝ)| := by
      rw [Complex.norm_intCast]
      push_cast
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [← h1, ← hes, MvPolynomial.esymm, map_sum]
    calc ‖∑ t ∈ (Finset.univ : Finset (Fin d)).powersetCard (d - k),
            MvPolynomial.aeval z (∏ i ∈ t, MvPolynomial.X i)‖
        ≤ ∑ t ∈ (Finset.univ : Finset (Fin d)).powersetCard (d - k),
            ‖MvPolynomial.aeval z (∏ i ∈ t, MvPolynomial.X i)‖ := norm_sum_le _ _
      _ ≤ ∑ _t ∈ (Finset.univ : Finset (Fin d)).powersetCard (d - k), (B : ℝ) ^ (d - k) := by
          refine Finset.sum_le_sum fun t ht => ?_
          rw [map_prod, norm_prod]
          have hcard_t : t.card = d - k := (Finset.mem_powersetCard.mp ht).2
          calc ∏ i ∈ t, ‖MvPolynomial.aeval z (MvPolynomial.X i)‖
              ≤ ∏ _i ∈ t, (B : ℝ) := Finset.prod_le_prod (fun _ _ => norm_nonneg _)
                  fun i _ => by simpa using hz_le i
            _ = (B : ℝ) ^ (d - k) := by rw [Finset.prod_const, hcard_t]
      _ = (Nat.choose d (d - k) : ℝ) * (B : ℝ) ^ (d - k) := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hbinom : (Nat.choose d (d - k) : ℝ) * (B : ℝ) ^ (d - k) ≤ ((B : ℝ) + 1) ^ d := by
    have hsum : ((B : ℝ) + 1) ^ d = ∑ j ∈ Finset.range (d + 1), (B : ℝ) ^ j * (1 : ℝ) ^ (d - j) * (Nat.choose d j : ℝ) := by
      rw [add_pow]
    rw [hsum]
    have hmem : d - k ∈ Finset.range (d + 1) := Finset.mem_range.mpr (by omega)
    have hle := Finset.single_le_sum (f := fun j => (B : ℝ) ^ j * (1 : ℝ) ^ (d - j) * (Nat.choose d j : ℝ))
      (fun j _ => by positivity) hmem
    simpa [mul_comm] using hle
  have hr : (|G.coeff k| : ℝ) ≤ (((B + 1 : ℕ) ^ d : ℤ) : ℝ) := by
    push_cast
    exact hnorm.trans hbinom
  exact_mod_cast hr

private noncomputable def monicBoundedFamily (D B : ℕ) : Finset ℤ[X] :=
  (Finset.Icc 1 D).biUnion fun d =>
    (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(B : ℤ)) (B : ℤ)).image fun c =>
      X ^ d + ∑ j : Fin d, C (c j) * X ^ j.val

private lemma mem_monicBoundedFamily {D B : ℕ} {G : ℤ[X]} (hG : G.Monic)
    (hd1 : 1 ≤ G.natDegree) (hdD : G.natDegree ≤ D)
    (hcoeff : ∀ k < G.natDegree, |G.coeff k| ≤ (B : ℤ)) :
    G ∈ monicBoundedFamily D B := by
  rw [monicBoundedFamily, Finset.mem_biUnion]
  refine ⟨G.natDegree, Finset.mem_Icc.mpr ⟨hd1, hdD⟩, Finset.mem_image.mpr ?_⟩
  refine ⟨fun j : Fin G.natDegree => G.coeff j.val, ?_, ?_⟩
  · rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_Icc]
    exact abs_le.mp (hcoeff j.val j.isLt)
  · ext k
    rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finset_sum_coeff]
    by_cases hkd : k < G.natDegree
    · rw [if_neg hkd.ne, zero_add]
      rw [Finset.sum_eq_single (⟨k, hkd⟩ : Fin G.natDegree)]
      · simp
      · intro j _ hjk
        rw [Polynomial.coeff_C_mul_X_pow, if_neg (fun e => hjk (Fin.ext e.symm))]
      · intro h; exact (h (Finset.mem_univ _)).elim
    · have hsum0 : ∑ j : Fin G.natDegree, (C (G.coeff j.val) * X ^ j.val).coeff k = 0 :=
        Finset.sum_eq_zero fun j _ => by
          rw [Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
      rw [hsum0, add_zero]
      by_cases hkeq : k = G.natDegree
      · rw [if_pos hkeq, hkeq]; exact hG.leadingCoeff.symm
      · rw [if_neg hkeq]
        exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

private lemma card_monicBoundedFamily_le (D B : ℕ) :
    (monicBoundedFamily D B).card ≤ D * (2 * B + 1) ^ D := by
  calc (monicBoundedFamily D B).card
      ≤ ∑ d ∈ Finset.Icc 1 D,
          ((Fintype.piFinset fun _ : Fin d => Finset.Icc (-(B : ℤ)) (B : ℤ)).image fun c =>
            X ^ d + ∑ j : Fin d, C (c j) * X ^ j.val).card := Finset.card_biUnion_le
    _ ≤ ∑ d ∈ Finset.Icc 1 D, (2 * B + 1) ^ d := by
        refine Finset.sum_le_sum fun d _ => Finset.card_image_le.trans ?_
        rw [Fintype.card_piFinset]
        simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        have : ((B : ℤ) + 1 - -(B : ℤ)).toNat = 2 * B + 1 := by omega
        rw [this]
    _ ≤ ∑ _d ∈ Finset.Icc 1 D, (2 * B + 1) ^ D :=
        Finset.sum_le_sum fun d hd => Nat.pow_le_pow_right (by omega) (Finset.mem_Icc.mp hd).2
    _ = D * (2 * B + 1) ^ D := by simp

/-- If `g ∣ f` with `f` monic in `ℤ[X]`, then there is a monic divisor `G ∣ f` of the same degree
(since `g.leadingCoeff ∣ 1`, so `g.leadingCoeff = ±1`). -/
private lemma exists_monic_dvd_of_dvd_monic {f g : ℤ[X]} (hf : f.Monic) (hdvd : g ∣ f) :
    ∃ G : ℤ[X], G.Monic ∧ G ∣ f ∧ G.natDegree = g.natDegree := by
  obtain ⟨h, hgh⟩ := hdvd
  have hlc : g.leadingCoeff * h.leadingCoeff = 1 := by
    have := congrArg Polynomial.leadingCoeff hgh
    rw [hf.leadingCoeff, Polynomial.leadingCoeff_mul] at this
    exact this.symm
  have hg_unit : g.leadingCoeff = 1 ∨ g.leadingCoeff = -1 := Int.mul_eq_one_iff_eq_one_or_neg_one.mp hlc |>.imp And.left And.left
  rcases hg_unit with h1 | hm1
  · exact ⟨g, h1, ⟨h, hgh⟩, rfl⟩
  · refine ⟨-g, ?_, ⟨-h, by rw [hgh]; ring⟩, Polynomial.natDegree_neg g⟩
    rw [Polynomial.Monic, Polynomial.leadingCoeff_neg, hm1]; norm_num

private lemma card_noncyclotomic_le {M n : ℕ} (hM : 34 ≤ M) (hn : 10 ^ 12 ≤ n)
    (hlog : (Real.log (M : ℝ)) ^ 3 ≤ (n : ℝ)) :
    let D := Nat.floor ((n : ℝ) ^ (1 / 10 : ℝ))
    let noncyc := (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
      ∃ G : ℤ[X], G.Monic ∧ G ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧
        1 ≤ G.natDegree ∧ G.natDegree ≤ D ∧
        ∃ z : ℂ, (G.map (Int.castRingHom ℂ)).eval z = 0 ∧
          (2 : ℝ) ^ ((1 : ℝ) / (8 * (G.natDegree : ℝ) ^ 2)) < ‖z‖
    (noncyc.card : ℝ) ≤ (1 / (n : ℝ)) * ((M + 1 : ℝ) ^ n) := by
  intro D noncyc
  have hD_pos : 1 ≤ D := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega)) (by norm_num)
    exact Nat.le_floor (by simpa using h1)
  have hD_le : (D : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ) := Nat.floor_le (by positivity)
  set B := (M + 2) ^ D
  set q := 8 * D ^ 2 * (Nat.clog 2 (M + 1) + 1)
  have hq_pos : 1 ≤ q := by dsimp [q]; nlinarith
  -- Every a ∈ noncyc has a monic divisor G ∈ monicBoundedFamily D B with a large root
  let Fset := (monicBoundedFamily D B).filter fun G =>
    ∃ z : ℂ, (G.map (Int.castRingHom ℂ)).eval z = 0 ∧
      (2 : ℝ) ^ ((1 : ℝ) / (8 * (D : ℝ) ^ 2)) < ‖z‖
  have hsub : noncyc ⊆ Fset.biUnion fun G =>
      (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
        G ∣ Green93.monicPoly (fun j => (a j : ℕ)) := by
    intro a ha
    obtain ⟨_, G, hG_monic, hG_dvd, hG_d1, hG_dD, z, hz_root, hz_norm⟩ := Finset.mem_filter.mp ha
    rw [Finset.mem_biUnion]
    have hG_mem : G ∈ monicBoundedFamily D B := by
      apply mem_monicBoundedFamily hG_monic hG_d1 hG_dD
      intro k hk
      have hroot_le : ∀ w : ℂ, (G.map (Int.castRingHom ℂ)).eval w = 0 → ‖w‖ ≤ (M + 1 : ℝ) := by
        intro w hw
        obtain ⟨Q, hQ⟩ := hG_dvd
        apply cauchy_root_bound (by omega) a w
        rw [hQ, Polynomial.map_mul, Polynomial.eval_mul, hw, zero_mul]
      have hcb := monic_coeff_bound_of_roots hG_monic (M + 1) (by simpa using hroot_le) k hk
      have hpow_le : ((M + 2 : ℕ) ^ G.natDegree : ℤ) ≤ ((M + 2 : ℕ) ^ D : ℤ) := by
        exact_mod_cast Nat.pow_le_pow_right (by omega) hG_dD
      exact hcb.trans hpow_le
    have hz_norm' : (2 : ℝ) ^ ((1 : ℝ) / (8 * (D : ℝ) ^ 2)) < ‖z‖ := by
      refine lt_of_le_of_lt ?_ hz_norm
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have : (G.natDegree : ℝ) ≤ (D : ℝ) := by exact_mod_cast hG_dD
      nlinarith
    exact ⟨G, Finset.mem_filter.mpr ⟨hG_mem, z, hz_root, hz_norm'⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ a, hG_dvd⟩⟩
  have hfiber : ∀ G ∈ Fset,
      ((Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
        G ∣ Green93.monicPoly (fun j => (a j : ℕ))).card ≤
        (M + 1) ^ (n - (n + q - 1) / q) := by
    intro G hG
    obtain ⟨_, z, hz_root, hz_norm⟩ := Finset.mem_filter.mp hG
    have hz_pow : (M + 1 : ℝ) ≤ ‖z‖ ^ q := by
      have h1 : (2 : ℝ) ^ (Nat.clog 2 (M + 1) + 1) ≤ ‖z‖ ^ q := by
        have hstep : ((2 : ℝ) ^ ((1 : ℝ) / (8 * (D : ℝ) ^ 2))) ^ q ≤ ‖z‖ ^ q :=
          pow_le_pow_left₀ (by positivity) hz_norm.le q
        refine le_trans ?_ hstep
        rw [← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / (8 * (D : ℝ) ^ 2))),
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        have hexp : (1 : ℝ) / (8 * (D : ℝ) ^ 2) * (q : ℝ) = ((Nat.clog 2 (M + 1) + 1 : ℕ) : ℝ) := by
          dsimp [q]; push_cast; field_simp
        rw [hexp, Real.rpow_natCast]
      have h2 : (M + 1 : ℕ) ≤ 2 ^ (Nat.clog 2 (M + 1) + 1) :=
        (Nat.le_pow_clog (by decide : 1 < 2) (M + 1)).trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
      exact (by exact_mod_cast h2 : (M + 1 : ℝ) ≤ (2 : ℝ) ^ (Nat.clog 2 (M + 1) + 1)).trans h1
    refine (Finset.card_le_card ?_).trans (card_roots_le_of_large_norm (by omega) hq_pos z hz_pow)
    intro a ha
    obtain ⟨_, Q, hQ⟩ := Finset.mem_filter.mp ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ a, ?_⟩
    rw [hQ, Polynomial.map_mul, Polynomial.eval_mul, hz_root, zero_mul]
  have hcard_nat : noncyc.card ≤ (D * (2 * B + 1) ^ D) * (M + 1) ^ (n - (n + q - 1) / q) := by
    calc noncyc.card
        ≤ (Fset.biUnion fun G => (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
            G ∣ Green93.monicPoly (fun j => (a j : ℕ))).card := Finset.card_le_card hsub
      _ ≤ ∑ G ∈ Fset, ((Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
            G ∣ Green93.monicPoly (fun j => (a j : ℕ))).card := Finset.card_biUnion_le
      _ ≤ ∑ _G ∈ Fset, (M + 1) ^ (n - (n + q - 1) / q) := Finset.sum_le_sum hfiber
      _ = Fset.card * (M + 1) ^ (n - (n + q - 1) / q) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (D * (2 * B + 1) ^ D) * (M + 1) ^ (n - (n + q - 1) / q) :=
          Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans (card_monicBoundedFamily_le D B))
  -- Analytic comparison via Real.log
  set k := (n + q - 1) / q
  have hk_le : k ≤ n := by
    dsimp [k]
    have h3 : n + q - 1 ≤ q * n := by
      have : 1 ≤ n := by omega
      have : n + q ≤ q * n + 1 := by nlinarith
      omega
    exact Nat.div_le_of_le_mul h3
  have hM1_pos : (0 : ℝ) < (M + 1 : ℝ) := by positivity
  have hM1_gt1 : (1 : ℝ) < (M + 1 : ℝ) := by exact_mod_cast (show 1 < M + 1 by omega)
  have hlogM1_ge : (3 : ℝ) ≤ Real.log (M + 1 : ℝ) := by
    have h35 : (Real.exp 3 : ℝ) ≤ (M + 1 : ℝ) := by
      have he3 : Real.exp 3 < 21 := by
        have h1 : Real.exp 1 < 2.72 := Real.exp_one_lt_d9.trans (by norm_num)
        have h3 : Real.exp 3 = (Real.exp 1) ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        rw [h3]; nlinarith [Real.exp_pos 1, sq_nonneg (Real.exp 1)]
      have : (35 : ℝ) ≤ (M + 1 : ℝ) := by exact_mod_cast (show 35 ≤ M + 1 by omega)
      linarith
    exact (Real.le_log_iff_exp_le hM1_pos).mpr h35
  have hlogM2_le : Real.log (M + 2 : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 3 : ℝ) := by
    have hM2_le : (M + 2 : ℝ) ≤ (M : ℝ) ^ 2 := by
      have : (34 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      nlinarith
    have h1 : Real.log (M + 2 : ℝ) ≤ 2 * Real.log (M : ℝ) := by
      calc Real.log (M + 2 : ℝ) ≤ Real.log ((M : ℝ) ^ 2) := Real.log_le_log (by positivity) hM2_le
        _ = 2 * Real.log (M : ℝ) := by rw [Real.log_pow]; ring
    have hlogM_le : Real.log (M : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
      have hnn : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
      calc Real.log (M : ℝ) = ((Real.log (M : ℝ)) ^ 3) ^ (1 / 3 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]; norm_num
        _ ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) hlog (by norm_num)
    linarith
  have hq_le : (q : ℝ) ≤ 24 * (D : ℝ) ^ 2 * Real.log (M + 1 : ℝ) := by
    have hclog : (Nat.clog 2 (M + 1) : ℝ) ≤ Real.log (M + 1 : ℝ) / Real.log 2 + 1 := by
      by_cases h1 : M + 1 ≤ 1
      · omega
      · have hprev : 2 ^ (Nat.clog 2 (M + 1) - 1) < M + 1 :=
          Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (by omega)
        have hprevR : (2 : ℝ) ^ (Nat.clog 2 (M + 1) - 1) ≤ (M + 1 : ℝ) := by exact_mod_cast hprev.le
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have h2 : ((Nat.clog 2 (M + 1) - 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log (M + 1 : ℝ) := by
          rw [← Real.log_pow]; exact Real.log_le_log (by positivity) hprevR
        have hcpos : 1 ≤ Nat.clog 2 (M + 1) := by
          have : 0 < Nat.clog 2 (M + 1) := Nat.clog_pos (by decide) (by omega)
          omega
        have hsub : ((Nat.clog 2 (M + 1) - 1 : ℕ) : ℝ) = (Nat.clog 2 (M + 1) : ℝ) - 1 := by
          rw [Nat.cast_sub hcpos, Nat.cast_one]
        rw [hsub] at h2
        have h3 := (le_div_iff₀ hlog2).mpr h2
        linarith
    have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have : Real.exp (1 / 2 : ℝ) ≤ 2 := by
        have h := Real.exp_one_lt_d9
        have hsq : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
          rw [← Real.exp_nat_mul]; norm_num
        nlinarith [Real.exp_pos (1 / 2 : ℝ)]
      exact (Real.le_log_iff_exp_le (by norm_num)).mpr this
    have hdiv : Real.log (M + 1 : ℝ) / Real.log 2 ≤ 2 * Real.log (M + 1 : ℝ) := by
      rw [div_le_iff₀ (Real.log_pos (by norm_num))]
      nlinarith
    have hclog_le : (Nat.clog 2 (M + 1) : ℝ) + 1 ≤ 3 * Real.log (M + 1 : ℝ) := by
      linarith
    dsimp [q]
    push_cast
    nlinarith [sq_nonneg (D : ℝ)]
  have hk_ge : (n : ℝ) / (24 * (D : ℝ) ^ 2 * Real.log (M + 1 : ℝ)) ≤ (k : ℝ) := by
    have h1 : (n : ℝ) ≤ (k : ℝ) * (q : ℝ) := by
      have : n ≤ k * q := by
        have hdiv := Nat.div_add_mod (n + q - 1) q
        have hmod := Nat.mod_lt (n + q - 1) hq_pos
        have hmul : q * ((n + q - 1) / q) = k * q := Nat.mul_comm _ _
        omega
      exact_mod_cast this
    have hq_posR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
    calc (n : ℝ) / (24 * (D : ℝ) ^ 2 * Real.log (M + 1 : ℝ))
        ≤ (n : ℝ) / (q : ℝ) := div_le_div_of_nonneg_left (by positivity) hq_posR hq_le
      _ ≤ (k : ℝ) := (div_le_iff₀ hq_posR).mpr h1
  -- Show (D * (2 * B + 1)^D) * n <= (M + 1)^k by taking logs
  have hlog_ineq : Real.log ((D : ℝ) * (2 * (B : ℝ) + 1) ^ D * (n : ℝ)) ≤
      (k : ℝ) * Real.log (M + 1 : ℝ) := by
    have h2B1 : 2 * (B : ℝ) + 1 ≤ (M + 2 : ℝ) ^ (D + 1) := by
      dsimp [B]; push_cast
      rw [pow_succ]
      have hM2 : (3 : ℝ) ≤ (M + 2 : ℝ) := by exact_mod_cast (show 3 ≤ M + 2 by omega)
      have hpow1 : (1 : ℝ) ≤ (M + 2 : ℝ) ^ D := one_le_pow₀ (by linarith)
      nlinarith
    have hprod_le : (D : ℝ) * (2 * (B : ℝ) + 1) ^ D * (n : ℝ) ≤
        (n : ℝ) ^ 2 * (M + 2 : ℝ) ^ ((D + 1) * D) := by
      have hDn : (D : ℝ) ≤ (n : ℝ) := by
        have : (n : ℝ) ^ (1 / 10 : ℝ) ≤ (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ n by omega)) (by norm_num)
        rw [Real.rpow_one] at this
        exact hD_le.trans this
      calc (D : ℝ) * (2 * (B : ℝ) + 1) ^ D * (n : ℝ)
          ≤ (n : ℝ) * ((M + 2 : ℝ) ^ (D + 1)) ^ D * (n : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul hDn (pow_le_pow_left₀ (by positivity) h2B1 D) (by positivity) (by positivity)
        _ = (n : ℝ) ^ 2 * (M + 2 : ℝ) ^ ((D + 1) * D) := by rw [← pow_mul]; ring
    have hLHS_log : Real.log ((D : ℝ) * (2 * (B : ℝ) + 1) ^ D * (n : ℝ)) ≤
        2 * Real.log (n : ℝ) + ((D : ℝ) + 1) * (D : ℝ) * Real.log (M + 2 : ℝ) := by
      calc Real.log ((D : ℝ) * (2 * (B : ℝ) + 1) ^ D * (n : ℝ))
          ≤ Real.log ((n : ℝ) ^ 2 * (M + 2 : ℝ) ^ ((D + 1) * D)) :=
            Real.log_le_log (by positivity) hprod_le
        _ = Real.log ((n : ℝ) ^ 2) + Real.log ((M + 2 : ℝ) ^ ((D + 1) * D)) :=
            Real.log_mul (by positivity) (by positivity)
        _ = 2 * Real.log (n : ℝ) + ((D : ℝ) + 1) * (D : ℝ) * Real.log (M + 2 : ℝ) := by
            rw [Real.log_pow, Real.log_pow]; push_cast; ring
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hD2_le : (D : ℝ) ^ 2 ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
      calc (D : ℝ) ^ 2 ≤ ((n : ℝ) ^ (1 / 10 : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hD_le 2
        _ = (n : ℝ) ^ (1 / 5 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]; norm_num
    have hD1D_le : ((D : ℝ) + 1) * (D : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 5 : ℝ) := by
      have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD_pos
      nlinarith
    have hRHS_log : (n : ℝ) ^ (4 / 5 : ℝ) / 24 ≤ (k : ℝ) * Real.log (M + 1 : ℝ) := by
      have h1 : (n : ℝ) / (24 * (D : ℝ) ^ 2) ≤ (k : ℝ) * Real.log (M + 1 : ℝ) := by
        have := mul_le_mul_of_nonneg_right hk_ge (by linarith : (0 : ℝ) ≤ Real.log (M + 1 : ℝ))
        have hsimp : (n : ℝ) / (24 * (D : ℝ) ^ 2 * Real.log (M + 1 : ℝ)) * Real.log (M + 1 : ℝ) =
            (n : ℝ) / (24 * (D : ℝ) ^ 2) := by
          have hl : Real.log (M + 1 : ℝ) ≠ 0 := by linarith
          field_simp
        rwa [hsimp] at this
      refine le_trans ?_ h1
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      calc (n : ℝ) ^ (4 / 5 : ℝ) * (24 * (D : ℝ) ^ 2)
          ≤ (n : ℝ) ^ (4 / 5 : ℝ) * (24 * (n : ℝ) ^ (1 / 5 : ℝ)) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = (n : ℝ) * 24 := by
            rw [mul_comm (24 : ℝ), ← mul_assoc, ← Real.rpow_add hn_pos]; norm_num
    have hlogn_le : Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
      have h1 : Real.log ((n : ℝ) ^ (1 / 5 : ℝ)) ≤ (n : ℝ) ^ (1 / 5 : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_rpow hn_pos] at h1
      have : (n : ℝ) ^ (1 / 5 : ℝ) ≥ 1 := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega)) (by norm_num)
      -- actually log n <= 5 * n^(1/5) is enough!
      have h2 : Real.log (n : ℝ) ≤ 5 * (n : ℝ) ^ (1 / 5 : ℝ) := by linarith
      -- tighten using 1/10: log n <= 10 * n^(1/10) <= n^(1/5) since n^(1/10) >= 10^(12/10) > 10!
      have h10 : Real.log ((n : ℝ) ^ (1 / 10 : ℝ)) ≤ (n : ℝ) ^ (1 / 10 : ℝ) :=
        (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
      rw [Real.log_rpow hn_pos] at h10
      have hn10 : (10 : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ) := by
        have h10_10 : (10 : ℝ) ^ (10 : ℕ) ≤ (n : ℝ) := by exact_mod_cast (show 10 ^ 10 ≤ n by omega)
        calc (10 : ℝ) = ((10 : ℝ) ^ (10 : ℕ)) ^ (1 / 10 : ℝ) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
          _ ≤ (n : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_le_rpow (by positivity) h10_10 (by norm_num)
      have hprod10 : (n : ℝ) ^ (1 / 10 : ℝ) * (n : ℝ) ^ (1 / 10 : ℝ) = (n : ℝ) ^ (1 / 5 : ℝ) := by
        rw [← Real.rpow_add hn_pos]; norm_num
      nlinarith
    have hprod_exp : (n : ℝ) ^ (1 / 5 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) = (n : ℝ) ^ (8 / 15 : ℝ) := by
      rw [← Real.rpow_add hn_pos]; norm_num
    have hgap : (100 : ℝ) ≤ (n : ℝ) ^ (4 / 15 : ℝ) := by
      have h100 : (100 : ℝ) ^ (15 : ℕ) ≤ (n : ℝ) ^ (4 : ℕ) := by
        have h1 : (10 : ℕ) ^ 30 ≤ (10 ^ 12 : ℕ) ^ 4 := by norm_num
        have h2 : (10 ^ 12 : ℕ) ^ 4 ≤ n ^ 4 := Nat.pow_le_pow_left hn 4
        have h3 : (100 : ℕ) ^ 15 = 10 ^ 30 := by norm_num
        exact_mod_cast h3.le.trans (h1.trans h2)
      calc (100 : ℝ) = ((100 : ℝ) ^ (15 : ℕ)) ^ (1 / 15 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
        _ ≤ ((n : ℝ) ^ (4 : ℕ)) ^ (1 / 15 : ℝ) := Real.rpow_le_rpow (by positivity) h100 (by norm_num)
        _ = (n : ℝ) ^ (4 / 15 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]; norm_num
    have h815_45 : (n : ℝ) ^ (8 / 15 : ℝ) * (n : ℝ) ^ (4 / 15 : ℝ) = (n : ℝ) ^ (4 / 5 : ℝ) := by
      rw [← Real.rpow_add hn_pos]; norm_num
    have h15_815 : (n : ℝ) ^ (1 / 5 : ℝ) ≤ (n : ℝ) ^ (8 / 15 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ n by omega)) (by norm_num)
    have hterm2 : ((D : ℝ) + 1) * (D : ℝ) * Real.log (M + 2 : ℝ) ≤ 4 * (n : ℝ) ^ (8 / 15 : ℝ) := by
      calc ((D : ℝ) + 1) * (D : ℝ) * Real.log (M + 2 : ℝ)
          ≤ (2 * (n : ℝ) ^ (1 / 5 : ℝ)) * (2 * (n : ℝ) ^ (1 / 3 : ℝ)) :=
            mul_le_mul hD1D_le hlogM2_le (Real.log_nonneg (by exact_mod_cast (show 1 ≤ M + 2 by omega))) (by positivity)
        _ = 4 * (n : ℝ) ^ (8 / 15 : ℝ) := by linarith [hprod_exp]
    have h6 : 6 * (n : ℝ) ^ (8 / 15 : ℝ) ≤ (n : ℝ) ^ (4 / 5 : ℝ) / 24 := by
      have h144 : (144 : ℝ) ≤ (n : ℝ) ^ (4 / 15 : ℝ) := by
        have h144_pow : (144 : ℝ) ^ (15 : ℕ) ≤ (n : ℝ) ^ (4 : ℕ) := by
          have h1 : (144 : ℕ) ^ 15 ≤ (10 ^ 12 : ℕ) ^ 4 := by norm_num
          have h2 : (10 ^ 12 : ℕ) ^ 4 ≤ n ^ 4 := Nat.pow_le_pow_left hn 4
          exact_mod_cast h1.trans h2
        calc (144 : ℝ) = ((144 : ℝ) ^ (15 : ℕ)) ^ (1 / 15 : ℝ) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
          _ ≤ ((n : ℝ) ^ (4 : ℕ)) ^ (1 / 15 : ℝ) := Real.rpow_le_rpow (by positivity) h144_pow (by norm_num)
          _ = (n : ℝ) ^ (4 / 15 : ℝ) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]; norm_num
      have h144' : (n : ℝ) ^ (8 / 15 : ℝ) * 144 ≤ (n : ℝ) ^ (4 / 5 : ℝ) := by
        rw [← h815_45]
        exact mul_le_mul_of_nonneg_left h144 (by positivity)
      linarith
    linarith
  have hexp_ineq : (D : ℝ) * (2 * (B : ℝ) + 1) ^ D * (n : ℝ) ≤ (M + 1 : ℝ) ^ k := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < (D : ℝ) * (2 * (B : ℝ) + 1) ^ D * (n : ℝ)),
      ← Real.exp_log (by positivity : (0 : ℝ) < (M + 1 : ℝ) ^ k), Real.log_pow]
    exact Real.exp_le_exp.mpr hlog_ineq
  have hcard_R : (noncyc.card : ℝ) ≤ ((D : ℝ) * (2 * (B : ℝ) + 1) ^ D) * (M + 1 : ℝ) ^ (n - k) := by
    exact_mod_cast hcard_nat
  have hpow_split : (M + 1 : ℝ) ^ n = (M + 1 : ℝ) ^ k * (M + 1 : ℝ) ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_of_le hk_le]
  rw [hpow_split]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  calc (noncyc.card : ℝ)
      ≤ ((D : ℝ) * (2 * (B : ℝ) + 1) ^ D) * (M + 1 : ℝ) ^ (n - k) := hcard_R
    _ = (1 / (n : ℝ)) * (((D : ℝ) * (2 * (B : ℝ) + 1) ^ D * (n : ℝ)) * (M + 1 : ℝ) ^ (n - k)) := by
        field_simp
    _ ≤ (1 / (n : ℝ)) * ((M + 1 : ℝ) ^ k * (M + 1 : ℝ) ^ (n - k)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hexp_ineq (by positivity)

/-! ### Section 4: Root-of-Unity Factors and Uniform Binomial Anti-Concentration -/

private lemma order_le_two_mul_totient_sq (m : ℕ) (hm : 1 ≤ m) :
    m ≤ 2 * (m.totient) ^ 2 := by
  -- Prove odd part `u` satisfies `u ≤ u.totient ^ 2`, and 2-part `2^a` satisfies `2^a ≤ 2 * (2^a).totient ^ 2`
  have hodd_sq : ∀ u : ℕ, 1 ≤ u → Odd u → u ≤ (u.totient) ^ 2 := by
    intro u
    induction u using Nat.strong_induction_on with
    | h u ih =>
      intro hu1 hodd
      by_cases hu : u = 1
      · subst hu; simp
      · obtain ⟨p, hp, hpu⟩ := Nat.exists_prime_and_dvd hu
        have hp_odd : p ≠ 2 := by
          intro h2; subst h2
          obtain ⟨k, hk⟩ := hodd
          obtain ⟨t, ht⟩ := hpu
          omega
        have hp3 : 3 ≤ p := by have := hp.two_le; omega
        -- Factor out p^e || u
        let e := padicValNat p u
        have he_pos : 1 ≤ e := by
          have : Fact p.Prime := ⟨hp⟩
          exact one_le_padicValNat_of_dvd (by omega) hpu
        have hpe_dvd : p ^ e ∣ u := pow_padicValNat_dvd
        obtain ⟨v, hv⟩ := hpe_dvd
        have hv_pos : 1 ≤ v := by
          by_contra hv0; simp [show v = 0 by omega] at hv; omega
        have hcop : (p ^ e).Coprime v := by
          refine Nat.Coprime.pow_left e ?_
          rw [hp.coprime_iff_not_dvd]
          intro hpv
          have : Fact p.Prime := ⟨hp⟩
          have h1 : p ^ (e + 1) ∣ u := by
            rw [hv, pow_succ]
            exact mul_dvd_mul_left (p ^ e) hpv
          have h2 : e + 1 ≤ padicValNat p u := (padicValNat_dvd_iff_le (by omega)).mp h1
          omega
        have hv_lt : v < u := by
          have hpe_gt1 : 1 < p ^ e := one_lt_pow₀ hp.one_lt (by omega)
          nlinarith
        have hv_odd : Odd v := by
          obtain ⟨k, hk⟩ := hodd
          by_contra heven
          rw [Nat.not_odd_iff_even] at heven
          obtain ⟨t, ht⟩ := heven
          have : 2 ∣ u := ⟨p ^ e * t, by rw [hv, ht]; ring⟩
          omega
        have ihv : v ≤ v.totient ^ 2 := ih v hv_lt hv_pos hv_odd
        have hpe_le : p ^ e ≤ (p ^ e).totient ^ 2 := by
          rw [Nat.totient_prime_pow hp (by omega)]
          have h1 : p ^ (e - 1) * (p - 1) ≥ p ^ (e - 1) * 2 := Nat.mul_le_mul_left _ (by omega)
          have h2 : (p ^ (e - 1) * (p - 1)) ^ 2 = p ^ (2 * (e - 1)) * (p - 1) ^ 2 := by ring
          rw [h2]
          have h3 : p ≤ (p - 1) ^ 2 := by
            have hp_sub : (p - 1) + 1 = p := Nat.sub_add_cancel (by omega)
            nlinarith
          have h4 : p ^ (e - 1) ≤ p ^ (2 * (e - 1)) := Nat.pow_le_pow_right hp.pos (by omega)
          calc p ^ e = p ^ (e - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel he_pos]
            _ ≤ p ^ (2 * (e - 1)) * (p - 1) ^ 2 := Nat.mul_le_mul h4 h3
        rw [hv, Nat.totient_mul hcop, mul_pow]
        exact Nat.mul_le_mul hpe_le ihv
  let a := padicValNat 2 m
  have h2a_dvd : 2 ^ a ∣ m := pow_padicValNat_dvd
  obtain ⟨u, hu⟩ := h2a_dvd
  have hu_pos : 1 ≤ u := by
    by_contra hu0; simp [show u = 0 by omega] at hu; omega
  have hu_odd : Odd u := by
    rw [Nat.odd_iff]
    by_contra hev
    have h2u : 2 ∣ u := Nat.dvd_of_mod_eq_zero (by omega)
    have h1 : 2 ^ (a + 1) ∣ m := by rw [hu, pow_succ]; exact mul_dvd_mul_left (2 ^ a) h2u
    have h2 : a + 1 ≤ padicValNat 2 m := (padicValNat_dvd_iff_le (by omega)).mp h1
    omega
  have hcop : (2 ^ a).Coprime u := by
    refine Nat.Coprime.pow_left a ?_
    rw [Nat.prime_two.coprime_iff_not_dvd]
    intro h2u
    obtain ⟨k, hk⟩ := hu_odd
    obtain ⟨t, ht⟩ := h2u
    omega
  have h2a_le : 2 ^ a ≤ 2 * (2 ^ a).totient ^ 2 := by
    cases a with
    | zero => simp
    | succ k =>
      rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
      simp only [Nat.add_sub_cancel, Nat.sub_self, mul_one]
      have : 2 ^ k ≤ (2 ^ k) ^ 2 := by nlinarith [Nat.one_le_two_pow (n := k)]
      rw [pow_succ]; linarith
  have hu_le : u ≤ u.totient ^ 2 := hodd_sq u hu_pos hu_odd
  rw [hu, Nat.totient_mul hcop, mul_pow]
  have hmul := Nat.mul_le_mul h2a_le hu_le
  linarith

private lemma central_binom_bound (r : ℕ) (hr : 1 ≤ r) :
    (Nat.choose r (r / 2) : ℝ) / (2 : ℝ) ^ r ≤ 1 / Real.sqrt (r : ℝ) := by
  have heven : ∀ h : ℕ, ((Nat.choose (2 * h) h : ℝ) / (4 : ℝ) ^ h) ^ 2 ≤ 1 / (2 * (h : ℝ) + 1) := by
    intro h
    induction h with
    | zero => norm_num
    | succ h ih =>
      have hrec : (Nat.choose (2 * (h + 1)) (h + 1) : ℝ) * (h + 1 : ℝ) =
          (Nat.choose (2 * h) h : ℝ) * (2 * (2 * h + 1) : ℝ) := by
        have hnat : Nat.choose (2 * (h + 1)) (h + 1) * (h + 1) =
            Nat.choose (2 * h) h * (2 * (2 * h + 1)) := by
          have h3 : 2 * (h + 1) = 2 * h + 2 := by omega
          rw [h3]
          have hf1 := Nat.choose_mul_factorial_mul_factorial (show h + 1 ≤ 2 * h + 2 by omega)
          have hf2 := Nat.choose_mul_factorial_mul_factorial (show h ≤ 2 * h by omega)
          rw [show 2 * h + 2 - (h + 1) = h + 1 by omega] at hf1
          rw [show 2 * h - h = h by omega] at hf2
          have hfac : (2 * h + 2).factorial = (2 * h + 2) * ((2 * h + 1) * (2 * h).factorial) := by
            rw [Nat.factorial_succ, Nat.factorial_succ]
          have hfac2 : (h + 1).factorial = (h + 1) * h.factorial := Nat.factorial_succ h
          have hpos : 0 < h.factorial * h.factorial * (h + 1) := by positivity
          apply Nat.eq_of_mul_eq_mul_right hpos
          calc Nat.choose (2 * h + 2) (h + 1) * (h + 1) * (h.factorial * h.factorial * (h + 1))
              = Nat.choose (2 * h + 2) (h + 1) * ((h + 1) * h.factorial) * ((h + 1) * h.factorial) := by ring
            _ = (2 * h + 2).factorial := by rw [← hfac2, hf1]
            _ = (2 * h + 2) * ((2 * h + 1) * (2 * h).factorial) := hfac
            _ = (2 * h + 2) * ((2 * h + 1) * (Nat.choose (2 * h) h * h.factorial * h.factorial)) := by rw [← hf2]
            _ = Nat.choose (2 * h) h * (2 * (2 * h + 1)) * (h.factorial * h.factorial * (h + 1)) := by ring
        exact_mod_cast hnat
      have hstep : (Nat.choose (2 * (h + 1)) (h + 1) : ℝ) / (4 : ℝ) ^ (h + 1) =
          ((2 * (h : ℝ) + 1) / (2 * (h : ℝ) + 2)) * ((Nat.choose (2 * h) h : ℝ) / (4 : ℝ) ^ h) := by
        rw [pow_succ]
        have hh1 : (h : ℝ) + 1 ≠ 0 := by positivity
        have h4 : (4 : ℝ) ^ h ≠ 0 := by positivity
        field_simp
        nlinarith [hrec]
      rw [hstep, mul_pow]
      calc ((2 * (h : ℝ) + 1) / (2 * (h : ℝ) + 2)) ^ 2 * ((Nat.choose (2 * h) h : ℝ) / (4 : ℝ) ^ h) ^ 2
          ≤ ((2 * (h : ℝ) + 1) / (2 * (h : ℝ) + 2)) ^ 2 * (1 / (2 * (h : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left ih (by positivity)
        _ ≤ 1 / (2 * ((h + 1 : ℕ) : ℝ) + 1) := by
            push_cast
            rw [div_pow, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
  have hsq : ((Nat.choose r (r / 2) : ℝ) / (2 : ℝ) ^ r) ^ 2 ≤ 1 / (r : ℝ) := by
    rcases Nat.even_or_odd r with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · have h2 : h + h = 2 * h := by omega
      rw [h2, Nat.mul_div_cancel_left h (by decide : 0 < 2)]
      have h4 : (2 : ℝ) ^ (2 * h) = (4 : ℝ) ^ h := by rw [pow_mul]; norm_num
      rw [h4]
      refine (heven h).trans ?_
      apply div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast (show 0 < 2 * h by omega))
      push_cast; linarith
    · have hdiv : (2 * h + 1) / 2 = h := by omega
      rw [hdiv]
      have hrec : (Nat.choose (2 * h + 1) h : ℝ) / (2 : ℝ) ^ (2 * h + 1) ≤
          (Nat.choose (2 * h) h : ℝ) / (4 : ℝ) ^ h := by
        have hnat : Nat.choose (2 * h + 1) h * (h + 1) = Nat.choose (2 * h) h * (2 * h + 1) := by
          have hf1 := Nat.choose_mul_factorial_mul_factorial (show h ≤ 2 * h + 1 by omega)
          have hf2 := Nat.choose_mul_factorial_mul_factorial (show h ≤ 2 * h by omega)
          rw [show 2 * h + 1 - h = h + 1 by omega] at hf1
          rw [show 2 * h - h = h by omega] at hf2
          have hpos : 0 < h.factorial * h.factorial := by positivity
          apply Nat.eq_of_mul_eq_mul_right hpos
          calc Nat.choose (2 * h + 1) h * (h + 1) * (h.factorial * h.factorial)
              = Nat.choose (2 * h + 1) h * h.factorial * ((h + 1) * h.factorial) := by ring
            _ = (2 * h + 1).factorial := by rw [← Nat.factorial_succ, hf1]
            _ = (2 * h + 1) * (2 * h).factorial := Nat.factorial_succ _
            _ = (2 * h + 1) * (Nat.choose (2 * h) h * h.factorial * h.factorial) := by rw [← hf2]
            _ = Nat.choose (2 * h) h * (2 * h + 1) * (h.factorial * h.factorial) := by ring
        have hR : (Nat.choose (2 * h + 1) h : ℝ) * ((h : ℝ) + 1) =
            (Nat.choose (2 * h) h : ℝ) * (2 * (h : ℝ) + 1) := by exact_mod_cast hnat
        have h2pow : (2 : ℝ) ^ (2 * h + 1) = 2 * (4 : ℝ) ^ h := by
          rw [pow_succ, pow_mul]; norm_num; ring
        rw [h2pow, div_le_div_iff₀ (by positivity) (by positivity)]
        have hle : (2 * (h : ℝ) + 1) ≤ 2 * ((h : ℝ) + 1) := by linarith
        nlinarith [hR, show (0 : ℝ) ≤ (Nat.choose (2 * h) h : ℝ) by positivity,
          show (0 : ℝ) < (4 : ℝ) ^ h by positivity]
      have hsq1 : ((Nat.choose (2 * h + 1) h : ℝ) / (2 : ℝ) ^ (2 * h + 1)) ^ 2 ≤
          ((Nat.choose (2 * h) h : ℝ) / (4 : ℝ) ^ h) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hrec 2
      exact hsq1.trans (by push_cast; exact heven h)
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (by positivity), Real.sqrt_div (by norm_num), Real.sqrt_one] at hsqrt
  exact hsqrt

/-- Uniform anti-concentration for the sum of `L` independent uniform digits in `Fin N` (`N ≥ 2`),
proved via `(b + ε) mod N` double-counting and the central binomial bound. -/
private lemma card_sum_eq_le {L N : ℕ} (hL : 1 ≤ L) (hN : 2 ≤ N) (t : ℕ) :
    (((Finset.univ : Finset (Fin L → Fin N)).filter fun x => ∑ k : Fin L, (x k).val = t).card : ℝ) ≤
      (2 / Real.sqrt (L : ℝ)) * (N : ℝ) ^ L := by
  let Xset := (Finset.univ : Finset (Fin L → Fin N)).filter fun x => ∑ k : Fin L, (x k).val = t
  let stepFn (b : Fin L → Fin N) (ε : Fin L → Bool) : Fin L → Fin N :=
    fun k => ⟨((b k).val + if ε k then 1 else 0) % N, Nat.mod_lt _ (by omega)⟩
  let Pset := (Finset.univ : Finset ((Fin L → Fin N) × (Fin L → Bool))).filter fun p =>
    ∑ k : Fin L, (stepFn p.1 p.2 k).val = t
  -- Lower bound: Pset.card = 2^L * Xset.card
  have hlower : 2 ^ L * Xset.card = Pset.card := by
    have hbij : Pset.card = (Xset ×ˢ (Finset.univ : Finset (Fin L → Bool))).card := by
      refine Finset.card_bij (fun p _ => (stepFn p.1 p.2, p.2)) ?_ ?_ ?_
      · intro p hp
        exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩,
          Finset.mem_univ _⟩
      · intro p₁ _ p₂ _ heq
        have ⟨hx, hε⟩ := Prod.mk.inj heq
        ext : 1
        · funext k
          have hk := congrArg Fin.val (congr_fun hx k)
          dsimp [stepFn] at hk
          rw [hε] at hk
          have h1 : (p₁.1 k).val < N := (p₁.1 k).isLt
          have h2 : (p₂.1 k).val < N := (p₂.1 k).isLt
          apply Fin.ext
          cases hbool : p₂.2 k
          · simp only [hbool, Bool.false_eq_true, ↓reduceIte, add_zero] at hk
            rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hk; exact hk
          · simp only [hbool, ↓reduceIte] at hk
            by_cases h1' : (p₁.1 k).val + 1 = N <;> by_cases h2' : (p₂.1 k).val + 1 = N
            · omega
            · rw [h1', Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hk; omega
            · rw [h2', Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hk; omega
            · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hk; omega
        · exact hε
      · intro q hq
        obtain ⟨hx, _⟩ := Finset.mem_product.mp hq
        let b : Fin L → Fin N := fun k =>
          ⟨((q.1 k).val + N - if q.2 k then 1 else 0) % N, Nat.mod_lt _ (by omega)⟩
        have hstep : stepFn b q.2 = q.1 := by
          funext k
          apply Fin.ext
          dsimp [stepFn, b]
          have hq1 : (q.1 k).val < N := (q.1 k).isLt
          cases q.2 k
          · simp [Nat.add_mod, Nat.mod_eq_of_lt hq1]
          · simp only [↓reduceIte]
            by_cases h0 : (q.1 k).val = 0
            · rw [h0]; simp [Nat.mod_eq_of_lt (show N - 1 < N by omega), Nat.sub_add_cancel (by omega : 1 ≤ N)]
            · have : ((q.1 k).val + N - 1) % N = (q.1 k).val - 1 := by
                rw [show (q.1 k).val + N - 1 = ((q.1 k).val - 1) + N by omega,
                  Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              rw [this, Nat.sub_add_cancel (by omega : 1 ≤ (q.1 k).val), Nat.mod_eq_of_lt hq1]
        refine ⟨(b, q.2), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Prod.ext hstep rfl⟩
        simpa [hstep] using (Finset.mem_filter.mp hx).2
    rw [hbij, Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Nat.mul_comm]
  -- Upper bound: for each fixed b, at least (L + 1) / 2 coordinates have the same nonzero step
  have hfiber : ∀ b : Fin L → Fin N,
      (((Finset.univ : Finset (Fin L → Bool)).filter fun ε =>
          ∑ k : Fin L, (stepFn b ε k).val = t).card : ℝ) ≤
        (2 / Real.sqrt (L : ℝ)) * (2 : ℝ) ^ L := by
    intro b
    let A : Finset (Fin L) := Finset.univ.filter fun k => (b k).val + 1 < N
    let B : Finset (Fin L) := Aᶜ
    have hAB : A.card + B.card = L := by
      have h1 : A.card + Aᶜ.card = Fintype.card (Fin L) := by
        rw [Finset.card_compl]; exact Nat.add_sub_of_le (Finset.card_le_univ A)
      simpa [B] using h1
    -- Choose I ∈ {A, B} with I.card ≥ (L + 1) / 2 and constant nonzero integer step
    have hex_I : ∃ (I : Finset (Fin L)) (δ : ℤ), δ ≠ 0 ∧ (L + 1) / 2 ≤ I.card ∧
        ∀ k ∈ I, ∀ e : Bool,
          (((stepFn b (fun j => if j = k then e else false) k).val : ℤ)) =
            (b k).val + if e then δ else 0 := by
      by_cases hA : (L + 1) / 2 ≤ A.card
      · refine ⟨A, 1, by omega, hA, fun k hk e => ?_⟩
        have hlt : (b k).val + 1 < N := (Finset.mem_filter.mp hk).2
        cases e <;> simp [stepFn, Nat.mod_eq_of_lt (b k).isLt, Nat.mod_eq_of_lt hlt]
      · refine ⟨B, -((N : ℤ) - 1), by omega, by omega, fun k hk e => ?_⟩
        have hge : ¬ ((b k).val + 1 < N) := by
          intro h; exact (Finset.mem_compl.mp hk) (Finset.mem_filter.mpr ⟨Finset.mem_univ k, h⟩)
        have heqN : (b k).val + 1 = N := by have := (b k).isLt; omega
        cases e
        · simp [stepFn, Nat.mod_eq_of_lt (b k).isLt]
        · simp only [stepFn, ↓reduceIte, heqN, Nat.mod_self, Nat.cast_zero]
          omega
    obtain ⟨I, δ, hδ_ne, hI_ge, hI_step⟩ := hex_I
    set r := I.card
    have hr_pos : 1 ≤ r := by omega
    let Eset := (Finset.univ : Finset (Fin L → Bool)).filter fun ε =>
      ∑ k : Fin L, (stepFn b ε k).val = t
    -- Split Eset by restriction of ε to Iᶜ
    have hE_le : Eset.card ≤ 2 ^ (L - r) * Nat.choose r (r / 2) := by
      let rest (ε : Fin L → Bool) : (↥(Iᶜ : Finset (Fin L)) → Bool) := fun k => ε k.val
      have hcard_Ic : (Iᶜ : Finset (Fin L)).card = L - r := by
        rw [Finset.card_compl, Fintype.card_fin]
      calc Eset.card
          = ∑ g : (↥(Iᶜ : Finset (Fin L)) → Bool), (Eset.filter fun ε => rest ε = g).card := by
              rw [← Finset.card_biUnion]
              · congr 1; ext ε; simp [rest]
              · intro g₁ _ g₂ _ hne
                exact Finset.disjoint_filter.mpr fun ε _ h1 h2 => hne (h1.symm.trans h2)
        _ ≤ ∑ _g : (↥(Iᶜ : Finset (Fin L)) → Bool), Nat.choose r (r / 2) := by
            refine Finset.sum_le_sum fun g _ => ?_
            -- On this fiber, all ε have the same number of true coordinates in I!
            let Fg := Eset.filter fun ε => rest ε = g
            by_cases hFg : Fg.Nonempty
            · obtain ⟨ε0, hε0⟩ := hFg
              let s := (I.filter fun k => ε0 k = true).card
              have hsame_card : ∀ ε ∈ Fg, (I.filter fun k => ε k = true).card = s := by
                intro ε hε
                have ht1 : (∑ k : Fin L, ((stepFn b ε k).val : ℤ)) = (t : ℤ) := by
                  exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp hε).1).2
                have ht0 : (∑ k : Fin L, ((stepFn b ε0 k).val : ℤ)) = (t : ℤ) := by
                  exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp hε0).1).2
                have hIc_eq : ∑ k ∈ Iᶜ, ((stepFn b ε k).val : ℤ) = ∑ k ∈ Iᶜ, ((stepFn b ε0 k).val : ℤ) := by
                  refine Finset.sum_congr rfl fun k hk => ?_
                  have he : ε k = ε0 k := by
                    have h1 := congr_fun (Finset.mem_filter.mp hε).2 ⟨k, hk⟩
                    have h2 := congr_fun (Finset.mem_filter.mp hε0).2 ⟨k, hk⟩
                    exact h1.trans h2.symm
                  simp [stepFn, he]
                have hI_eq : ∑ k ∈ I, ((stepFn b ε k).val : ℤ) = ∑ k ∈ I, ((stepFn b ε0 k).val : ℤ) := by
                  have hsplit1 := Finset.sum_add_sum_compl I (fun k => ((stepFn b ε k).val : ℤ))
                  have hsplit0 := Finset.sum_add_sum_compl I (fun k => ((stepFn b ε0 k).val : ℤ))
                  linarith
                have hlin : ∀ f : Fin L → Bool,
                    ∑ k ∈ I, ((stepFn b f k).val : ℤ) =
                      (∑ k ∈ I, ((b k).val : ℤ)) + ((I.filter fun k => f k = true).card : ℤ) * δ := by
                  intro f
                  have hterm : ∀ k ∈ I, ((stepFn b f k).val : ℤ) =
                      ((b k).val : ℤ) + if f k = true then δ else 0 := fun k hk => by
                    simpa [stepFn] using hI_step k hk (f k)
                  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite,
                    Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
                rw [hlin ε, hlin ε0] at hI_eq
                have hmul : (((I.filter fun k => ε k = true).card : ℤ) - (s : ℤ)) * δ = 0 := by
                  linarith
                have hsub : ((I.filter fun k => ε k = true).card : ℤ) = (s : ℤ) :=
                  sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hδ_ne)
                exact_mod_cast hsub
              have hinj : Set.InjOn (fun ε : Fin L → Bool => I.filter fun k => ε k = true) (Fg : Set _) := by
                intro ε₁ h₁ ε₂ h₂ heq
                funext k
                by_cases hk : k ∈ I
                · have hiff : (ε₁ k = true) ↔ (ε₂ k = true) := by
                    have h1 := Finset.ext_iff.mp heq k
                    simpa [hk] using h1
                  cases h1 : ε₁ k <;> cases h2 : ε₂ k <;> simp_all
                · have hk' : k ∈ Iᶜ := Finset.mem_compl.mpr hk
                  exact (congr_fun (Finset.mem_filter.mp h₁).2 ⟨k, hk'⟩).trans
                    (congr_fun (Finset.mem_filter.mp h₂).2 ⟨k, hk'⟩).symm
              have hcard_le := Finset.card_le_card_of_injOn
                (fun ε : Fin L → Bool => I.filter fun k => ε k = true)
                (fun ε hε => Finset.mem_coe.mpr (Finset.mem_powersetCard.mpr ⟨Finset.filter_subset _ I, hsame_card ε hε⟩))
                hinj
              rw [Finset.card_powersetCard] at hcard_le
              exact hcard_le.trans (Nat.choose_le_middle s r)
            · rw [Finset.not_nonempty_iff_eq_empty] at hFg
              change Fg.card ≤ _
              rw [hFg]
              simp
        _ = 2 ^ (L - r) * Nat.choose r (r / 2) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
              Fintype.card_coe, hcard_Ic, smul_eq_mul]
    have hE_R : (Eset.card : ℝ) ≤ (2 : ℝ) ^ (L - r) * (Nat.choose r (r / 2) : ℝ) := by
      exact_mod_cast hE_le
    have hr_le : r ≤ L := by exact (Finset.card_le_univ I).trans (by simp)
    have h2split : (2 : ℝ) ^ L = (2 : ℝ) ^ (L - r) * (2 : ℝ) ^ r := by
      rw [← pow_add, Nat.sub_add_cancel hr_le]
    have hcb := central_binom_bound r hr_pos
    have hsqrt_le : 1 / Real.sqrt (r : ℝ) ≤ 2 / Real.sqrt (L : ℝ) := by
      rw [div_le_div_iff₀ (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr (by positivity))]
      have h1 : (L : ℝ) ≤ 4 * (r : ℝ) := by exact_mod_cast (show L ≤ 4 * r by omega)
      calc 1 * Real.sqrt (L : ℝ) = Real.sqrt (L : ℝ) := one_mul _
        _ ≤ Real.sqrt (4 * (r : ℝ)) := Real.sqrt_le_sqrt h1
        _ = 2 * Real.sqrt (r : ℝ) := by rw [Real.sqrt_mul (by norm_num)]; norm_num
    calc (Eset.card : ℝ)
        ≤ (2 : ℝ) ^ (L - r) * (Nat.choose r (r / 2) : ℝ) := hE_R
      _ = ((Nat.choose r (r / 2) : ℝ) / (2 : ℝ) ^ r) * (2 : ℝ) ^ L := by
          rw [h2split]; field_simp
      _ ≤ (1 / Real.sqrt (r : ℝ)) * (2 : ℝ) ^ L := mul_le_mul_of_nonneg_right hcb (by positivity)
      _ ≤ (2 / Real.sqrt (L : ℝ)) * (2 : ℝ) ^ L := mul_le_mul_of_nonneg_right hsqrt_le (by positivity)
  -- Sum hfiber over all b : Fin L → Fin N
  have hP_card : (Pset.card : ℝ) =
      ∑ b : Fin L → Fin N,
        (((Finset.univ : Finset (Fin L → Bool)).filter fun ε =>
            ∑ k : Fin L, (stepFn b ε k).val = t).card : ℝ) := by
    have hnat : Pset.card = ∑ b : Fin L → Fin N,
        ((Finset.univ : Finset (Fin L → Bool)).filter fun ε =>
            ∑ k : Fin L, (stepFn b ε k).val = t).card := by
      have hcard_img : ∀ b : Fin L → Fin N,
          (((Finset.univ : Finset (Fin L → Bool)).filter fun ε =>
              ∑ k : Fin L, (stepFn b ε k).val = t).image fun ε => (b, ε)).card =
          ((Finset.univ : Finset (Fin L → Bool)).filter fun ε =>
              ∑ k : Fin L, (stepFn b ε k).val = t).card := fun b =>
        Finset.card_image_of_injective _ fun _ _ h => congrArg Prod.snd h
      simp_rw [← hcard_img]
      rw [← Finset.card_biUnion]
      · congr 1; ext ⟨b, ε⟩
        simp only [Pset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
          Finset.mem_image, Prod.mk.injEq]
        exact ⟨fun h => ⟨b, ε, h, rfl, rfl⟩, fun ⟨_, _, h, rfl, rfl⟩ => h⟩
      · intro b₁ _ b₂ _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro p hp1 hp2
        obtain ⟨ε₁, _, rfl⟩ := Finset.mem_image.mp hp1
        obtain ⟨ε₂, _, h2⟩ := Finset.mem_image.mp hp2
        exact hne (congrArg Prod.fst h2).symm
    exact_mod_cast hnat
  have hP_le : (Pset.card : ℝ) ≤ (2 / Real.sqrt (L : ℝ)) * (2 : ℝ) ^ L * (N : ℝ) ^ L := by
    rw [hP_card]
    calc ∑ b : Fin L → Fin N,
            (((Finset.univ : Finset (Fin L → Bool)).filter fun ε =>
                ∑ k : Fin L, (stepFn b ε k).val = t).card : ℝ)
        ≤ ∑ _b : Fin L → Fin N, (2 / Real.sqrt (L : ℝ)) * (2 : ℝ) ^ L :=
          Finset.sum_le_sum fun b _ => hfiber b
      _ = (N : ℝ) ^ L * ((2 / Real.sqrt (L : ℝ)) * (2 : ℝ) ^ L) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
          push_cast; rfl
      _ = (2 / Real.sqrt (L : ℝ)) * (2 : ℝ) ^ L * (N : ℝ) ^ L := by ring
  have hlowerR : (2 : ℝ) ^ L * (Xset.card : ℝ) = (Pset.card : ℝ) := by exact_mod_cast hlower
  have h2L : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  nlinarith

/-- For a fixed `m`-th root of unity `ζ` (`1 ≤ m ≤ n`), freezing coordinates not divisible by `m`
fixes the sum of `L = ⌈n/m⌉` uniform digits, bounding `#{a | F_a(ζ) = 0}` by `2 √(m/n) (M+1)^n`. -/
private lemma card_root_of_unity_le {M n m : ℕ} (hM : 1 ≤ M) (hm1 : 1 ≤ m) (hmn : m ≤ n)
    (ζ : ℂ) (hζ : ζ ^ m = 1) :
    (((Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
      ((Green93.monicPoly fun j => (a j : ℕ)).map (Int.castRingHom ℂ)).eval ζ = 0).card : ℝ) ≤
      (2 * Real.sqrt ((m : ℝ) / (n : ℝ))) * ((M + 1 : ℝ) ^ n) := by
  let S : Finset (Fin n) := Finset.univ.filter fun j => m ∣ j.val
  let T : Finset (Fin n) := Sᶜ
  set L := (n + m - 1) / m
  have hS_card : S.card = L := card_div_indices n m hm1
  have hT_card : T.card = n - L := by rw [Finset.card_compl, Fintype.card_fin, hS_card]
  have hL_pos : 1 ≤ L := by
    dsimp [L]
    exact Nat.div_pos (by omega) hm1
  have hL_le : L ≤ n := by
    dsimp [L]
    have hmn1 : n + m - 1 ≤ m * n := by
      have : 1 ≤ n := le_trans hm1 hmn
      have : n + m ≤ m * n + 1 := by nlinarith
      omega
    exact Nat.div_le_of_le_mul hmn1
  let bad := (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
    ((Green93.monicPoly fun j => (a j : ℕ)).map (Int.castRingHom ℂ)).eval ζ = 0
  let rest (a : Fin n → Fin (M + 1)) : (↥T → Fin (M + 1)) := fun j => a j.val
  have hbad_sum : (bad.card : ℝ) = ∑ g : (↥T → Fin (M + 1)), ((bad.filter fun a => rest a = g).card : ℝ) := by
    have hnat : bad.card = ∑ g : (↥T → Fin (M + 1)), (bad.filter fun a => rest a = g).card := by
      rw [← Finset.card_biUnion]
      · congr 1; ext a; simp [rest]
      · intro g₁ _ g₂ _ hne
        exact Finset.disjoint_filter.mpr fun a _ h1 h2 => hne (h1.symm.trans h2)
    exact_mod_cast hnat
  have hfiber : ∀ g : (↥T → Fin (M + 1)),
      ((bad.filter fun a => rest a = g).card : ℝ) ≤ (2 / Real.sqrt (L : ℝ)) * ((M + 1 : ℝ) ^ L) := by
    intro g
    let Fg := bad.filter fun a => rest a = g
    by_cases hne : Fg.Nonempty
    · obtain ⟨a0, ha0⟩ := hne
      let t := ∑ j ∈ S, (a0 j : ℕ)
      have hsame_sum : ∀ a ∈ Fg, ∑ j ∈ S, (a j : ℕ) = t := by
        intro a ha
        have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
        have h0 := (Finset.mem_filter.mp (Finset.mem_filter.mp ha0).1).2
        rw [eval_monicPoly_complex] at h1 h0
        have hT_eq : ∑ j ∈ T, (a j : ℂ) * ζ ^ j.val = ∑ j ∈ T, (a0 j : ℂ) * ζ ^ j.val := by
          refine Finset.sum_congr rfl fun j hj => ?_
          have he : a j = a0 j :=
            (congr_fun (Finset.mem_filter.mp ha).2 ⟨j, hj⟩).trans
              (congr_fun (Finset.mem_filter.mp ha0).2 ⟨j, hj⟩).symm
          rw [he]
        have hS_eq : ∑ j ∈ S, (a j : ℂ) * ζ ^ j.val = ∑ j ∈ S, (a0 j : ℂ) * ζ ^ j.val := by
          have hs1 := Finset.sum_add_sum_compl S (fun j : Fin n => (a j : ℂ) * ζ ^ j.val)
          have hs0 := Finset.sum_add_sum_compl S (fun j : Fin n => (a0 j : ℂ) * ζ ^ j.val)
          change ∑ j ∈ S, (a j : ℂ) * ζ ^ j.val + ∑ j ∈ T, (a j : ℂ) * ζ ^ j.val = _ at hs1
          change ∑ j ∈ S, (a0 j : ℂ) * ζ ^ j.val + ∑ j ∈ T, (a0 j : ℂ) * ζ ^ j.val = _ at hs0
          linear_combination h1 - h0 + hs1 - hs0 - hT_eq
        have hpow1 : ∀ j ∈ S, ζ ^ j.val = 1 := fun j hj => by
          obtain ⟨q, hq⟩ := (Finset.mem_filter.mp hj).2
          rw [hq, pow_mul, hζ, one_pow]
        have hsum1 : ∑ j ∈ S, (a j : ℂ) * ζ ^ j.val = ((∑ j ∈ S, (a j : ℕ) : ℕ) : ℂ) := by
          push_cast
          exact Finset.sum_congr rfl fun j hj => by rw [hpow1 j hj, mul_one]
        have hsum0 : ∑ j ∈ S, (a0 j : ℂ) * ζ ^ j.val = (t : ℂ) := by
          dsimp [t]; push_cast
          exact Finset.sum_congr rfl fun j hj => by rw [hpow1 j hj, mul_one]
        rw [hsum1, hsum0] at hS_eq
        exact Nat.cast_injective hS_eq
      -- Biject S ≃ Fin L
      let eS : Fin L ≃ ↥S := (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hS_card])).symm
      have hinj : Set.InjOn (fun (a : Fin n → Fin (M + 1)) (k : Fin L) => a (eS k).val) (Fg : Set _) := by
        intro a₁ h₁ a₂ h₂ heq
        funext j
        by_cases hj : j ∈ S
        · have hk := congr_fun heq (eS.symm ⟨j, hj⟩)
          simpa using hk
        · have hj' : j ∈ T := Finset.mem_compl.mpr hj
          exact (congr_fun (Finset.mem_filter.mp h₁).2 ⟨j, hj'⟩).trans
            (congr_fun (Finset.mem_filter.mp h₂).2 ⟨j, hj'⟩).symm
      have hcard_le : Fg.card ≤
          ((Finset.univ : Finset (Fin L → Fin (M + 1))).filter fun x => ∑ k : Fin L, (x k).val = t).card := by
        refine Finset.card_le_card_of_injOn (fun a k => a (eS k).val) ?_ hinj
        intro a ha
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have hsum_e : ∑ k : Fin L, (a (eS k).val).val = ∑ j ∈ S, (a j).val := by
          rw [← Finset.sum_coe_sort S (fun j => (a j).val)]
          exact Fintype.sum_equiv eS (fun k => (a (eS k).val).val) (fun j => (a j.val).val) fun _ => rfl
        rw [hsum_e]
        exact hsame_sum a ha
      have hcard_R : (Fg.card : ℝ) ≤
          (((Finset.univ : Finset (Fin L → Fin (M + 1))).filter fun x => ∑ k : Fin L, (x k).val = t).card : ℝ) := by
        exact_mod_cast hcard_le
      exact hcard_R.trans (by simpa using card_sum_eq_le hL_pos (by omega : 2 ≤ M + 1) t)
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      simp [Fg, hne]
      positivity
  have hsqrt_cmp : 2 / Real.sqrt (L : ℝ) ≤ 2 * Real.sqrt ((m : ℝ) / (n : ℝ)) := by
    have hn_pos : 0 < n := by omega
    have hL_ge : (n : ℝ) / (m : ℝ) ≤ (L : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      have : n ≤ L * m := by
        have hdiv := Nat.div_add_mod (n + m - 1) m
        have hmod := Nat.mod_lt (n + m - 1) hm1
        have hmul : m * ((n + m - 1) / m) = L * m := Nat.mul_comm _ _
        omega
      exact_mod_cast this
    have hsq1 : Real.sqrt ((n : ℝ) / (m : ℝ)) ≤ Real.sqrt (L : ℝ) := Real.sqrt_le_sqrt hL_ge
    rw [Real.sqrt_div (by positivity)] at hsq1 ⊢
    rw [div_le_iff₀ (Real.sqrt_pos.mpr (by positivity))]
    calc (2 : ℝ) = 2 * (Real.sqrt (m : ℝ) / Real.sqrt (n : ℝ)) * (Real.sqrt (n : ℝ) / Real.sqrt (m : ℝ)) := by
          have hm0 : Real.sqrt (m : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
          have hn0 : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
          field_simp
      _ ≤ 2 * (Real.sqrt (m : ℝ) / Real.sqrt (n : ℝ)) * Real.sqrt (L : ℝ) :=
          mul_le_mul_of_nonneg_left hsq1 (by positivity)
  rw [hbad_sum]
  calc ∑ g : (↥T → Fin (M + 1)), ((bad.filter fun a => rest a = g).card : ℝ)
      ≤ ∑ _g : (↥T → Fin (M + 1)), (2 / Real.sqrt (L : ℝ)) * ((M + 1 : ℝ) ^ L) :=
        Finset.sum_le_sum fun g _ => hfiber g
    _ = ((M + 1 : ℝ) ^ (n - L)) * ((2 / Real.sqrt (L : ℝ)) * ((M + 1 : ℝ) ^ L)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin,
          hT_card, nsmul_eq_mul]
        push_cast; rfl
    _ = (2 / Real.sqrt (L : ℝ)) * ((M + 1 : ℝ) ^ n) := by
        have hpow : (M + 1 : ℝ) ^ (n - L) * (M + 1 : ℝ) ^ L = (M + 1 : ℝ) ^ n := by
          rw [← pow_add, Nat.sub_add_cancel hL_le]
        rw [← hpow]; ring
    _ ≤ (2 * Real.sqrt ((m : ℝ) / (n : ℝ))) * ((M + 1 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_right hsqrt_cmp (by positivity)

private lemma card_cyclotomic_le {M n : ℕ} (hM : 34 ≤ M) (hn : 10 ^ 12 ≤ n) :
    let D := Nat.floor ((n : ℝ) ^ (1 / 10 : ℝ))
    let cyc := (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
      ∃ G : ℤ[X], G.Monic ∧ G ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧
        1 ≤ G.natDegree ∧ G.natDegree ≤ D ∧
        ∃ z : ℂ, (G.map (Int.castRingHom ℂ)).eval z = 0 ∧ ∃ m : ℕ, 1 ≤ m ∧ z ^ m = 1
    (cyc.card : ℝ) ≤ (6 * (n : ℝ) ^ (-1 / 5 : ℝ)) * ((M + 1 : ℝ) ^ n) := by
  intro D cyc
  have hD_le : (D : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ) := Nat.floor_le (by positivity)
  have h2D2_le : 2 * D ^ 2 ≤ n := by
    have h1 : (2 * (D : ℝ) ^ 2) ≤ 2 * (n : ℝ) ^ (1 / 5 : ℝ) := by
      have : (D : ℝ) ^ 2 ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
        calc (D : ℝ) ^ 2 ≤ ((n : ℝ) ^ (1 / 10 : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hD_le 2
          _ = (n : ℝ) ^ (1 / 5 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      linarith
    have h2 : 2 * (n : ℝ) ^ (1 / 5 : ℝ) ≤ (n : ℝ) := by
      have h15 : (n : ℝ) ^ (1 / 5 : ℝ) * 2 ≤ (n : ℝ) ^ (1 / 5 : ℝ) * (n : ℝ) ^ (4 / 5 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : (2 : ℝ) ≤ (n : ℝ) ^ (4 / 5 : ℝ) := by
          have h2_5 : (2 : ℝ) ^ (5 : ℕ) ≤ (n : ℝ) ^ (4 : ℕ) := by
            have h1 : (2 : ℕ) ^ 5 ≤ (10 ^ 12 : ℕ) ^ 4 := by norm_num
            have h2 : (10 ^ 12 : ℕ) ^ 4 ≤ n ^ 4 := Nat.pow_le_pow_left hn 4
            exact_mod_cast h1.trans h2
          calc (2 : ℝ) = ((2 : ℝ) ^ (5 : ℕ)) ^ (1 / 5 : ℝ) := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
            _ ≤ ((n : ℝ) ^ (4 : ℕ)) ^ (1 / 5 : ℝ) := Real.rpow_le_rpow (by positivity) h2_5 (by norm_num)
            _ = (n : ℝ) ^ (4 / 5 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
        exact this
      have hadd : (n : ℝ) ^ (1 / 5 : ℝ) * (n : ℝ) ^ (4 / 5 : ℝ) = (n : ℝ) := by
        rw [← Real.rpow_add (by positivity)]; norm_num
      linarith
    exact_mod_cast h1.trans h2
  -- Every a ∈ cyc vanishes at ζ_m = exp(2πi/m) for some 1 ≤ m ≤ 2 D^2
  let ζ : ℕ → ℂ := fun m => Complex.exp (2 * Real.pi * Complex.I / (m : ℂ))
  have hsub : cyc ⊆ (Finset.Icc 1 (2 * D ^ 2)).biUnion fun m =>
      (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
        ((Green93.monicPoly fun j => (a j : ℕ)).map (Int.castRingHom ℂ)).eval (ζ m) = 0 := by
    intro a ha
    obtain ⟨_, G, hG_monic, hG_dvd, _, hG_dD, z, hz_root, m, hm1, hzm⟩ := Finset.mem_filter.mp ha
    -- Let m0 be the least positive m with z^m = 1, so z is a primitive m0-th root of unity
    let m0 := Nat.find (⟨m, hm1, hzm⟩ : ∃ k : ℕ, 1 ≤ k ∧ z ^ k = 1)
    have hm0_spec : 1 ≤ m0 ∧ z ^ m0 = 1 := Nat.find_spec (⟨m, hm1, hzm⟩ : ∃ k : ℕ, 1 ≤ k ∧ z ^ k = 1)
    have hm0_prim : IsPrimitiveRoot z m0 := by
      refine IsPrimitiveRoot.iff_def z m0 |>.mpr ⟨hm0_spec.2, fun l hl => ?_⟩
      by_contra hndvd
      have hmod_pos : 1 ≤ l % m0 := by
        have := Nat.dvd_iff_mod_eq_zero.not.mp hndvd; omega
      have hmod_lt : l % m0 < m0 := Nat.mod_lt l hm0_spec.1
      have hz_mod : z ^ (l % m0) = 1 := by
        have hdiv := Nat.div_add_mod l m0
        have h1 : z ^ l = (z ^ m0) ^ (l / m0) * z ^ (l % m0) := by
          rw [← pow_mul, ← pow_add, hdiv]
        rw [hl, hm0_spec.2, one_pow, one_mul] at h1
        exact h1.symm
      exact Nat.find_min (⟨m, hm1, hzm⟩ : ∃ k : ℕ, 1 ≤ k ∧ z ^ k = 1) hmod_lt ⟨hmod_pos, hz_mod⟩
    -- cyclotomic m0 ℚ is irreducible and has z as root, so it divides G_Q and F_a_Q
    have hcyc_irr : Irreducible (Polynomial.cyclotomic m0 ℚ) :=
      Polynomial.cyclotomic.irreducible_rat hm0_spec.1
    have hcyc_root : Polynomial.aeval z (Polynomial.cyclotomic m0 ℚ) = 0 := by
      have h1 : (Polynomial.cyclotomic m0 ℂ).IsRoot z := hm0_prim.isRoot_cyclotomic hm0_spec.1
      have hmap : (Polynomial.cyclotomic m0 ℚ).map (algebraMap ℚ ℂ) = Polynomial.cyclotomic m0 ℂ :=
        Polynomial.map_cyclotomic m0 (algebraMap ℚ ℂ)
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, hmap]
      exact h1
    have hmin_eq : minpoly ℚ z = Polynomial.cyclotomic m0 ℚ := by
      have hmonic : (Polynomial.cyclotomic m0 ℚ).Monic := Polynomial.cyclotomic.monic m0 ℚ
      exact (minpoly.eq_of_irreducible_of_monic hcyc_irr hcyc_root hmonic).symm
    have hG_Q_root : Polynomial.aeval z (G.map (Int.castRingHom ℚ)) = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_map]
      have hcomp : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := by
        ext; simp
      rw [hcomp]; exact hz_root
    have hcyc_dvd_G : Polynomial.cyclotomic m0 ℚ ∣ G.map (Int.castRingHom ℚ) := by
      rw [← hmin_eq]; exact minpoly.dvd ℚ z hG_Q_root
    have htot_le : m0.totient ≤ D := by
      have hG_Q_ne : G.map (Int.castRingHom ℚ) ≠ 0 := (hG_monic.map _).ne_zero
      have h1 := Polynomial.natDegree_le_of_dvd hcyc_dvd_G hG_Q_ne
      rw [Polynomial.natDegree_cyclotomic, hG_monic.natDegree_map] at h1
      exact h1.trans hG_dD
    have hm0_le : m0 ≤ 2 * D ^ 2 :=
      (order_le_two_mul_totient_sq m0 hm0_spec.1).trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left htot_le 2))
    -- Also ζ m0 is a root of cyclotomic m0 ℚ, hence a root of G, hence a root of F_a!
    have hζ_prim : IsPrimitiveRoot (ζ m0) m0 := Complex.isPrimitiveRoot_exp m0 (by omega)
    have hζ_cyc : Polynomial.aeval (ζ m0) (Polynomial.cyclotomic m0 ℚ) = 0 := by
      have h1 : (Polynomial.cyclotomic m0 ℂ).IsRoot (ζ m0) := hζ_prim.isRoot_cyclotomic hm0_spec.1
      have hmap : (Polynomial.cyclotomic m0 ℚ).map (algebraMap ℚ ℂ) = Polynomial.cyclotomic m0 ℂ :=
        Polynomial.map_cyclotomic m0 (algebraMap ℚ ℂ)
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, hmap]
      exact h1
    have hζ_G : (G.map (Int.castRingHom ℂ)).eval (ζ m0) = 0 := by
      obtain ⟨Q, hQ⟩ := hcyc_dvd_G
      have h1 := congrArg (Polynomial.aeval (ζ m0)) hQ
      rw [map_mul, hζ_cyc, zero_mul] at h1
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_map] at h1
      have hcomp : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := by
        ext; simp
      rwa [hcomp] at h1
    obtain ⟨Q, hQ⟩ := hG_dvd
    rw [Finset.mem_biUnion]
    refine ⟨m0, Finset.mem_Icc.mpr ⟨hm0_spec.1, hm0_le⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ?_⟩⟩
    rw [hQ, Polynomial.map_mul, Polynomial.eval_mul, hζ_G, zero_mul]
  let I : Finset ℕ := Finset.Icc 1 (2 * D ^ 2)
  have hcard_le : (cyc.card : ℝ) ≤
      ∑ m ∈ I, (2 * Real.sqrt ((m : ℝ) / (n : ℝ))) * ((M + 1 : ℝ) ^ n) := by
    calc (cyc.card : ℝ)
        ≤ (I.biUnion fun m =>
            (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
              ((Green93.monicPoly fun j => (a j : ℕ)).map (Int.castRingHom ℂ)).eval (ζ m) = 0).card := by
            exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ m ∈ I,
            (((Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
              ((Green93.monicPoly fun j => (a j : ℕ)).map (Int.castRingHom ℂ)).eval (ζ m) = 0).card : ℝ) := by
            have hnat := Finset.card_biUnion_le (s := I)
              (t := fun m => (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
                ((Green93.monicPoly fun j => (a j : ℕ)).map (Int.castRingHom ℂ)).eval (ζ m) = 0)
            have hR : ((I.biUnion fun m =>
                (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
                  ((Green93.monicPoly fun j => (a j : ℕ)).map (Int.castRingHom ℂ)).eval (ζ m) = 0).card : ℝ) ≤
                ((∑ m ∈ I,
                  ((Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
                    ((Green93.monicPoly fun j => (a j : ℕ)).map (Int.castRingHom ℂ)).eval (ζ m) = 0).card : ℕ) : ℝ) := by
              exact_mod_cast hnat
            simpa using hR
      _ ≤ ∑ m ∈ I, (2 * Real.sqrt ((m : ℝ) / (n : ℝ))) * ((M + 1 : ℝ) ^ n) := by
            refine Finset.sum_le_sum fun m hm => ?_
            have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
            have hmn : m ≤ n := (Finset.mem_Icc.mp hm).2.trans h2D2_le
            have hζm : (ζ m) ^ m = 1 := (Complex.isPrimitiveRoot_exp m (by omega)).pow_eq_one
            exact card_root_of_unity_le (by omega) hm1 hmn (ζ m) hζm
  have hsum_le : ∑ m ∈ I, (2 * Real.sqrt ((m : ℝ) / (n : ℝ))) ≤
      6 * (n : ℝ) ^ (-1 / 5 : ℝ) := by
    calc ∑ m ∈ I, (2 * Real.sqrt ((m : ℝ) / (n : ℝ)))
        ≤ ∑ _m ∈ I, (2 * Real.sqrt ((2 * (D : ℝ) ^ 2) / (n : ℝ))) := by
          refine Finset.sum_le_sum fun m hm => ?_
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Real.sqrt_le_sqrt
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact_mod_cast (Finset.mem_Icc.mp hm).2
      _ = (2 * (D : ℝ) ^ 2) * (2 * Real.sqrt ((2 * (D : ℝ) ^ 2) / (n : ℝ))) := by
          dsimp [I]
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; push_cast; rfl
      _ ≤ (2 * (n : ℝ) ^ (1 / 5 : ℝ)) * (2 * Real.sqrt ((2 * (n : ℝ) ^ (1 / 5 : ℝ)) / (n : ℝ))) := by
          have hD2 : (D : ℝ) ^ 2 ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
            calc (D : ℝ) ^ 2 ≤ ((n : ℝ) ^ (1 / 10 : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hD_le 2
              _ = (n : ℝ) ^ (1 / 5 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
          apply mul_le_mul (by linarith) _ (by positivity) (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Real.sqrt_le_sqrt
          exact div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = (4 * Real.sqrt 2) * (n : ℝ) ^ (-1 / 5 : ℝ) := by
          have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
          have hrat : (2 * (n : ℝ) ^ (1 / 5 : ℝ)) / (n : ℝ) = 2 * (n : ℝ) ^ (-4 / 5 : ℝ) := by
            rw [mul_div_assoc, ← Real.rpow_sub_one hn_pos.ne']; norm_num
          rw [hrat, Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow ((n : ℝ) ^ (-4 / 5 : ℝ)),
            ← Real.rpow_mul hn_pos.le]
          have hcombine : (n : ℝ) ^ (1 / 5 : ℝ) * (n : ℝ) ^ ((-4 / 5 : ℝ) * (1 / 2 : ℝ)) =
              (n : ℝ) ^ (-1 / 5 : ℝ) := by
            rw [← Real.rpow_add hn_pos]; norm_num
          calc (2 * (n : ℝ) ^ (1 / 5 : ℝ)) * (2 * (Real.sqrt 2 * (n : ℝ) ^ ((-4 / 5 : ℝ) * (1 / 2 : ℝ))))
              = (4 * Real.sqrt 2) * ((n : ℝ) ^ (1 / 5 : ℝ) * (n : ℝ) ^ ((-4 / 5 : ℝ) * (1 / 2 : ℝ))) := by ring
            _ = (4 * Real.sqrt 2) * (n : ℝ) ^ (-1 / 5 : ℝ) := by rw [hcombine]
      _ ≤ 6 * (n : ℝ) ^ (-1 / 5 : ℝ) := by
          have h4s2 : 4 * Real.sqrt 2 ≤ 6 := by
            have : Real.sqrt 2 ≤ 3 / 2 := by
              rw [Real.sqrt_le_left (by norm_num)]; norm_num
            linarith
          exact mul_le_mul_of_nonneg_right h4s2 (by positivity)
  rw [← Finset.sum_mul] at hcard_le
  exact hcard_le.trans (mul_le_mul_of_nonneg_right hsum_le (by positivity))

/-! ### Section 5: Final Assembly -/

private lemma card_eligible {M n : ℕ} (hn : 1 ≤ n) :
    ((Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
      (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0).card =
      M * (M + 1) ^ (n - 1) := by
  let i0 : Fin n := ⟨0, hn⟩
  have hiff : ∀ a : Fin n → Fin (M + 1),
      (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0 ↔ (a i0).val ≠ 0 := fun a => by
    have hc := OMA.R_Green93_green_93_variants_bskk_large_R1.green93_coeff_below (fun j => (a j : ℕ)) i0
    change (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 = ((a i0).val : ℤ) at hc
    rw [hc]
    exact Nat.cast_ne_zero
  have hfilt : ((Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
      (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0) =
      Finset.univ.filter fun a : Fin n → Fin (M + 1) => (a i0).val ≠ 0 := by
    ext a; simp [hiff]
  rw [hfilt]
  have hpi : (Finset.univ.filter fun a : Fin n → Fin (M + 1) => (a i0).val ≠ 0) =
      Fintype.piFinset fun j : Fin n =>
        if j = i0 then (Finset.univ : Finset (Fin (M + 1))).filter (fun x => x.val ≠ 0)
        else Finset.univ := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h j; split_ifs with hj
      · subst hj; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      · exact Finset.mem_univ _
    · intro h
      have := h i0
      simp only [↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
  rw [hpi, Fintype.card_piFinset]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0)]
  simp only [↓reduceIte]
  have hcard0 : ((Finset.univ : Finset (Fin (M + 1))).filter fun x : Fin (M + 1) => x.val ≠ 0).card = M := by
    have hcomp : ((Finset.univ : Finset (Fin (M + 1))).filter fun x : Fin (M + 1) => x.val ≠ 0) =
        Finset.univ.erase (0 : Fin (M + 1)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
      exact ⟨fun h heq => h (congrArg Fin.val heq), fun h hv => h (Fin.ext hv)⟩
    rw [hcomp, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  rw [hcard0]
  congr 1
  have hprod : ∏ j ∈ Finset.univ.erase i0,
      (if j = i0 then (Finset.univ : Finset (Fin (M + 1))).filter (fun x => x.val ≠ 0) else Finset.univ).card =
      ∏ _j ∈ Finset.univ.erase i0, (M + 1) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [if_neg (Finset.ne_of_mem_erase hj), Finset.card_univ, Fintype.card_fin]
  rw [hprod, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

end OMA.P_Green93_green_93_variants_bskk_large_R1_H1

open Polynomial in
theorem OMA.solution : OMA.R_Green93_green_93_variants_bskk_large_R1.H1 := by
  classical
  refine ⟨(1 : ℝ) / 20, by norm_num, 10 ^ 12, ?_⟩
  intro M n hM hn hlog
  dsimp only
  set eligible := (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
    (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0
  set bad := eligible.filter fun a =>
    ∃ g : ℤ[X], g ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧
      0 < g.natDegree ∧ (g.natDegree : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ)
  set D := Nat.floor ((n : ℝ) ^ (1 / 10 : ℝ))
  set noncyc := (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
    ∃ G : ℤ[X], G.Monic ∧ G ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧
      1 ≤ G.natDegree ∧ G.natDegree ≤ D ∧
      ∃ z : ℂ, (G.map (Int.castRingHom ℂ)).eval z = 0 ∧
        (2 : ℝ) ^ ((1 : ℝ) / (8 * (G.natDegree : ℝ) ^ 2)) < ‖z‖
  set cyc := (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
    ∃ G : ℤ[X], G.Monic ∧ G ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧
      1 ≤ G.natDegree ∧ G.natDegree ≤ D ∧
      ∃ z : ℂ, (G.map (Int.castRingHom ℂ)).eval z = 0 ∧ ∃ m : ℕ, 1 ≤ m ∧ z ^ m = 1
  have hsub : bad ⊆ noncyc ∪ cyc := by
    intro a ha
    obtain ⟨ha_el, g, hg_dvd, hg_pos, hg_le⟩ := Finset.mem_filter.mp ha
    have hf_monic : (Green93.monicPoly fun j => (a j : ℕ)).Monic :=
      (OMA.R_Green93_green_93_variants_bskk_large_R1.green93_monic_of_degree _).monic
    obtain ⟨G, hG_monic, hG_dvd, hG_deg⟩ :=
      OMA.P_Green93_green_93_variants_bskk_large_R1_H1.exists_monic_dvd_of_dvd_monic hf_monic hg_dvd
    have hG_d1 : 1 ≤ G.natDegree := by omega
    have hG_dD : G.natDegree ≤ D := Nat.le_floor (by rwa [hG_deg])
    have hG_c0 : G.coeff 0 ≠ 0 := by
      obtain ⟨Q, hQ⟩ := hG_dvd
      have hf0 : (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0 := (Finset.mem_filter.mp ha_el).2
      intro h0
      apply hf0
      rw [hQ, Polynomial.mul_coeff_zero, h0, zero_mul]
    rcases OMA.P_Green93_green_93_variants_bskk_large_R1_H1.quant_kronecker hG_monic hG_d1 hG_c0 with
      ⟨z, hz_root, hz_norm⟩ | ⟨z, hz_root, m, hm1, hzm⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ a, G, hG_monic, hG_dvd, hG_d1, hG_dD, z, hz_root, hz_norm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ a, G, hG_monic, hG_dvd, hG_d1, hG_dD, z, hz_root, m, hm1, hzm⟩)
  have hbad_le : (bad.card : ℝ) ≤ (noncyc.card : ℝ) + (cyc.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le noncyc cyc)
  have hnc := OMA.P_Green93_green_93_variants_bskk_large_R1_H1.card_noncyclotomic_le hM hn hlog
  have hcy := OMA.P_Green93_green_93_variants_bskk_large_R1_H1.card_cyclotomic_le hM hn
  have helig : (M + 1 : ℝ) ^ n ≤ (35 / 34 : ℝ) * (eligible.card : ℝ) := by
    have hce : (eligible.card : ℝ) = (M : ℝ) * (M + 1 : ℝ) ^ (n - 1) := by
      exact_mod_cast OMA.P_Green93_green_93_variants_bskk_large_R1_H1.card_eligible (M := M) (by omega : 1 ≤ n)
    rw [hce]
    have hpow : (M + 1 : ℝ) ^ n = (M + 1 : ℝ) * (M + 1 : ℝ) ^ (n - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ n)]
    rw [hpow]
    have hM34 : (34 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hrat : (M + 1 : ℝ) ≤ (35 / 34 : ℝ) * (M : ℝ) := by linarith
    nlinarith [show (0 : ℝ) ≤ (M + 1 : ℝ) ^ (n - 1) by positivity]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hinv_le : 1 / (n : ℝ) ≤ (n : ℝ) ^ (-1 / 5 : ℝ) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ n by omega)) (by norm_num)
  have hsum_coef : (1 / (n : ℝ) + 6 * (n : ℝ) ^ (-1 / 5 : ℝ)) * (35 / 34 : ℝ) ≤
      (n : ℝ) ^ (-(1 / 20 : ℝ)) / 2 := by
    have h15 : (16 : ℝ) ≤ (n : ℝ) ^ (3 / 20 : ℝ) := by
      have h16_20 : (16 : ℝ) ^ (20 : ℕ) ≤ (n : ℝ) ^ (3 : ℕ) := by
        have h1 : (16 : ℕ) ^ 20 ≤ (10 ^ 12 : ℕ) ^ 3 := by norm_num
        have h2 : (10 ^ 12 : ℕ) ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hn 3
        exact_mod_cast h1.trans h2
      calc (16 : ℝ) = ((16 : ℝ) ^ (20 : ℕ)) ^ (1 / 20 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
        _ ≤ ((n : ℝ) ^ (3 : ℕ)) ^ (1 / 20 : ℝ) := Real.rpow_le_rpow (by positivity) h16_20 (by norm_num)
        _ = (n : ℝ) ^ (3 / 20 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]; norm_num
    have hprod : (n : ℝ) ^ (-1 / 5 : ℝ) * (n : ℝ) ^ (3 / 20 : ℝ) = (n : ℝ) ^ (-(1 / 20 : ℝ)) := by
      rw [← Real.rpow_add hn_pos]; norm_num
    have h16' : 16 * (n : ℝ) ^ (-1 / 5 : ℝ) ≤ (n : ℝ) ^ (-(1 / 20 : ℝ)) := by
      rw [← hprod, mul_comm]
      exact mul_le_mul_of_nonneg_left h15 (by positivity)
    linarith [show (0 : ℝ) ≤ (n : ℝ) ^ (-1 / 5 : ℝ) by positivity]
  calc (bad.card : ℝ)
      ≤ (noncyc.card : ℝ) + (cyc.card : ℝ) := hbad_le
    _ ≤ (1 / (n : ℝ) + 6 * (n : ℝ) ^ (-1 / 5 : ℝ)) * (M + 1 : ℝ) ^ n := by linarith
    _ ≤ (1 / (n : ℝ) + 6 * (n : ℝ) ^ (-1 / 5 : ℝ)) * ((35 / 34 : ℝ) * (eligible.card : ℝ)) :=
        mul_le_mul_of_nonneg_left helig (by positivity)
    _ = ((1 / (n : ℝ) + 6 * (n : ℝ) ^ (-1 / 5 : ℝ)) * (35 / 34 : ℝ)) * (eligible.card : ℝ) := by ring
    _ ≤ ((n : ℝ) ^ (-(1 / 20 : ℝ)) / 2) * (eligible.card : ℝ) :=
        mul_le_mul_of_nonneg_right hsum_coef (by positivity)
