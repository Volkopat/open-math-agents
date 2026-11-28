import FormalConjectures.Wikipedia.NoetherProblem
import Mathlib

/-!
# Swan (1969) Counterexample to the Noether Problem (`n = 47`)

Proves that `ℚ(X_0, ..., X_46)^{C_47}` is not purely transcendental over `ℚ`, following
Richard G. Swan, *Invariant rational functions and a problem of Steenrod*, Invent. Math. 7 (1969), 148–158.
-/

namespace OMA.Noether47

section Part12
open Polynomial

private noncomputable abbrev Φ23 : ℤ[X] := Polynomial.cyclotomic 23 ℤ

/-- `Λ = ℤ[ζ_23] = ℤ[X] / (Φ_23(X))`. -/
abbrev Λ : Type := AdjoinRoot Φ23

/-- The primitive 23rd root of unity `ζ_23 ∈ Λ`. -/
noncomputable def ζ23 : Λ := AdjoinRoot.root Φ23

private lemma prime_23 : Nat.Prime 23 := by norm_num
private lemma prime_47 : Nat.Prime 47 := by norm_num

private instance : Fact (Nat.Prime 23) := ⟨prime_23⟩

private lemma Φ23_monic : Φ23.Monic := Polynomial.cyclotomic.monic 23 ℤ

private lemma Φ23_natDegree : Φ23.natDegree = 22 := by
  rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime prime_23]

private lemma Φ23_eq_sum : Φ23 = ∑ i ∈ Finset.range 23, (X : ℤ[X]) ^ i :=
  Polynomial.cyclotomic_prime ℤ 23

private lemma sum_ζ23_eq_zero : ∑ i ∈ Finset.range 23, ζ23 ^ i = 0 := by
  have h0 : Polynomial.eval₂ (Int.castRingHom Λ) ζ23 (∑ i ∈ Finset.range 23, (X : ℤ[X]) ^ i) = 0 := by
    rw [← Φ23_eq_sum]
    exact AdjoinRoot.eval₂_root Φ23
  simpa [Polynomial.eval₂_finsetSum, Polynomial.eval₂_pow, Polynomial.eval₂_X] using h0

private lemma ζ23_pow_23 : ζ23 ^ 23 = 1 := by
  have h1 : (ζ23 - 1) * ∑ i ∈ Finset.range 23, ζ23 ^ i = ζ23 ^ 23 - 1 := by
    have := geom_sum_mul ζ23 23
    linear_combination this
  rw [sum_ζ23_eq_zero, mul_zero] at h1
  exact sub_eq_zero.mp h1.symm

private lemma ζ23_pow_mod (n : ℕ) : ζ23 ^ n = ζ23 ^ (n % 23) := by
  conv_lhs => rw [← Nat.div_add_mod n 23]
  rw [pow_add, pow_mul, ζ23_pow_23, one_pow, one_mul]

/-- The 23rd cyclotomic field over `ℚ`. -/
private noncomputable abbrev E23 : Type := AdjoinRoot (Polynomial.cyclotomic 23 ℚ)

private instance : Fact (Irreducible (Polynomial.cyclotomic 23 ℚ)) :=
  ⟨Polynomial.cyclotomic.irreducible_rat (by norm_num)⟩

private noncomputable instance : Field E23 := AdjoinRoot.instField

/-- Canonical ring homomorphism `Λ →+* E23`. -/
private noncomputable def toE23 : Λ →+* E23 :=
  AdjoinRoot.lift (Int.castRingHom E23) (AdjoinRoot.root (Polynomial.cyclotomic 23 ℚ)) (by
    have hmap : Polynomial.map (Int.castRingHom E23) Φ23 =
        Polynomial.map (algebraMap ℚ E23) (Polynomial.cyclotomic 23 ℚ) := by
      rw [Polynomial.map_cyclotomic, Polynomial.map_cyclotomic]
    rw [Polynomial.eval₂_eq_eval_map, hmap, ← Polynomial.eval₂_eq_eval_map]
    exact AdjoinRoot.eval₂_root _)

private lemma toE23_injective : Function.Injective toE23 := by
  intro x y hxy
  let pbZ := AdjoinRoot.powerBasis' Φ23_monic
  let pbQ := AdjoinRoot.powerBasis (Polynomial.cyclotomic.monic 23 ℚ).ne_zero
  have hdimZ : pbZ.dim = 22 := by
    change Φ23.natDegree = 22
    exact Φ23_natDegree
  have hdimQ : pbQ.dim = 22 := by
    change (Polynomial.cyclotomic 23 ℚ).natDegree = 22
    rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime prime_23]
  have hsub : toE23 (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  set z := x - y
  have hz : z = ∑ i : Fin pbZ.dim, (pbZ.basis.repr z i : Λ) * ζ23 ^ (i : ℕ) := by
    have h1 := (pbZ.basis.sum_repr z).symm
    refine h1.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [pbZ.basis_eq_pow, zsmul_eq_mul]
    rfl
  have hzE : toE23 z = ∑ i : Fin pbZ.dim, ((pbZ.basis.repr z i : ℤ) : ℚ) •
      (AdjoinRoot.root (Polynomial.cyclotomic 23 ℚ)) ^ (i : ℕ) := by
    conv_lhs => rw [hz]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow]
    have h1 : toE23 (pbZ.basis.repr z i : Λ) = algebraMap ℚ E23 (pbZ.basis.repr z i : ℚ) := by
      simp [toE23]
    have h2 : toE23 ζ23 = AdjoinRoot.root (Polynomial.cyclotomic 23 ℚ) := by
      simp [toE23, ζ23]
    rw [h1, h2, Algebra.smul_def]
  rw [hsub] at hzE
  have hlin : ∀ i : Fin pbZ.dim, ((pbZ.basis.repr z i : ℤ) : ℚ) = 0 := by
    let eFin : Fin pbZ.dim ≃ Fin pbQ.dim := finCongr (hdimZ.trans hdimQ.symm)
    have hsumQ : ∑ j : Fin pbQ.dim, ((pbZ.basis.repr z (eFin.symm j) : ℤ) : ℚ) • pbQ.basis j = 0 := by
      rw [hzE]
      refine (Fintype.sum_equiv eFin _ _ fun i => ?_).symm
      rw [Equiv.symm_apply_apply, pbQ.basis_eq_pow]
      rfl
    have hall := Fintype.linearIndependent_iff.mp pbQ.basis.linearIndependent _ hsumQ
    intro i
    simpa [eFin] using hall (eFin i)
  have hz0 : z = 0 := by
    rw [hz]
    apply Finset.sum_eq_zero
    intro i _
    have hi : pbZ.basis.repr z i = 0 := by exact_mod_cast hlin i
    simp [hi]
  exact sub_eq_zero.mp hz0

instance instIsDomainΛ : IsDomain Λ :=
  Function.Injective.isDomain toE23 toE23_injective

private lemma ζ23_pow_ne_one {k : ℕ} (hk0 : 0 < k) (hk23 : k < 23) : ζ23 ^ k ≠ 1 := by
  intro h
  let hpb := AdjoinRoot.powerBasis' Φ23_monic
  have hdim : hpb.dim = 22 := by
    change Φ23.natDegree = 22
    exact Φ23_natDegree
  by_cases hk22 : k < 22
  · have hlin := Fintype.linearIndependent_iff.mp hpb.basis.linearIndependent
    let hk_fin : Fin hpb.dim := ⟨k, by omega⟩
    let h0_fin : Fin hpb.dim := ⟨0, by omega⟩
    let f : Fin hpb.dim → ℤ := fun i =>
      if i = hk_fin then 1 else if i = h0_fin then -1 else 0
    have hne : hk_fin ≠ h0_fin := by
      intro heq
      have := congrArg Fin.val heq
      change k = 0 at this
      omega
    have hsum : ∑ i : Fin hpb.dim, f i • hpb.basis i = 0 := by
      have hcalc : ∑ i : Fin hpb.dim, f i • hpb.basis i = hpb.basis hk_fin - hpb.basis h0_fin := by
        rw [Finset.sum_eq_add hk_fin h0_fin hne]
        · simp [f, hne.symm, sub_eq_add_neg]
        · intro c _ hc
          simp [f, hc.1, hc.2]
        · intro hmem; exact absurd (Finset.mem_univ hk_fin) hmem
        · intro hmem; exact absurd (Finset.mem_univ h0_fin) hmem
      rw [hcalc, hpb.basis_eq_pow, hpb.basis_eq_pow]
      change ζ23 ^ k - ζ23 ^ 0 = 0
      rw [h, pow_zero, sub_self]
    have hf0 := hlin f hsum hk_fin
    simp [f] at hf0
  · have hk_eq : k = 22 := by omega
    subst hk_eq
    have h1 : ζ23 = 1 := by
      have h23 := ζ23_pow_23
      rw [show (23 : ℕ) = 22 + 1 by rfl, pow_succ, h, one_mul] at h23
      exact h23
    have hsum := sum_ζ23_eq_zero
    simp only [h1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hsum
    have hE := congrArg toE23 hsum
    rw [map_natCast, map_zero] at hE
    norm_num at hE

/-- Ring endomorphism `τ_k : Λ →+* Λ` sending `ζ23 ↦ ζ23 ^ k` for `0 < k < 23`. -/
noncomputable def τ (k : ℕ) (hk0 : 0 < k) (hk23 : k < 23) : Λ →+* Λ :=
  AdjoinRoot.lift (Int.castRingHom Λ) (ζ23 ^ k) (by
    have h0 : Polynomial.eval₂ (Int.castRingHom Λ) (ζ23 ^ k) (∑ i ∈ Finset.range 23, (X : ℤ[X]) ^ i) = 0 := by
      rw [Polynomial.eval₂_finsetSum]
      have hmul : (ζ23 ^ k - 1) * ∑ i ∈ Finset.range 23, (ζ23 ^ k) ^ i = (ζ23 ^ k) ^ 23 - 1 := by
        have := geom_sum_mul (ζ23 ^ k) 23
        linear_combination this
      have hpow : (ζ23 ^ k) ^ 23 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, ζ23_pow_23, one_pow]
      rw [hpow, sub_self] at hmul
      have hne : ζ23 ^ k - 1 ≠ 0 := sub_ne_zero.mpr (ζ23_pow_ne_one hk0 hk23)
      have hzero : ∑ i ∈ Finset.range 23, (ζ23 ^ k) ^ i = 0 :=
        (mul_eq_zero.mp hmul).resolve_left hne
      simpa [Polynomial.eval₂_pow, Polynomial.eval₂_X] using hzero
    rwa [← Φ23_eq_sum] at h0)

/-- Automorphism `τU u : Λ →+* Λ` indexed by `u : (ZMod 23)ˣ`. -/
noncomputable def τU (u : (ZMod 23)ˣ) : Λ →+* Λ :=
  τ (u : ZMod 23).val (by
    have hne : (u : ZMod 23) ≠ 0 := u.ne_zero
    exact Nat.pos_of_ne_zero (fun h => hne (by rw [← ZMod.natCast_zmod_val (u : ZMod 23), h]; simp)))
    (ZMod.val_lt (u : ZMod 23))

private lemma τU_ζ23 (u : (ZMod 23)ˣ) : τU u ζ23 = ζ23 ^ (u : ZMod 23).val := by
  simp [τU, τ, ζ23]

lemma τU_mul (u v : (ZMod 23)ˣ) (x : Λ) : τU (u * v) x = τU u (τU v x) := by
  have heq : τU (u * v) = (τU u).comp (τU v) := by
    apply AdjoinRoot.ringHom_ext
    · ext; simp
    · simp only [RingHom.comp_apply]
      change τU (u * v) ζ23 = τU u (τU v ζ23)
      rw [τU_ζ23, τU_ζ23, map_pow, τU_ζ23, ← pow_mul, Units.val_mul, ZMod.val_mul, mul_comm,
        ← ζ23_pow_mod]
  exact congrArg (fun f : Λ →+* Λ => f x) heq

lemma τU_one (x : Λ) : τU 1 x = x := by
  have heq : τU 1 = RingHom.id Λ := by
    apply AdjoinRoot.ringHom_ext
    · ext; simp
    · change τU 1 ζ23 = ζ23
      rw [τU_ζ23]
      have h1 : ((1 : (ZMod 23)ˣ) : ZMod 23).val = 1 := by decide
      rw [h1, pow_one]
  exact congrArg (fun f : Λ →+* Λ => f x) heq

noncomputable def τUEquiv (u : (ZMod 23)ˣ) : Λ ≃+* Λ where
  toFun := τU u
  invFun := τU u⁻¹
  left_inv x := by rw [← τU_mul, inv_mul_cancel, τU_one]
  right_inv x := by rw [← τU_mul, mul_inv_cancel, τU_one]
  map_mul' := map_mul (τU u)
  map_add' := map_add (τU u)

lemma intCast_injective_Λ : Function.Injective (Int.cast : ℤ → Λ) := by
  intro a b hab
  have hE := congrArg toE23 hab
  have h1 : toE23 (a : Λ) = (a : E23) := map_intCast toE23 a
  have h2 : toE23 (b : Λ) = (b : E23) := map_intCast toE23 b
  rw [h1, h2] at hE
  exact Int.cast_injective hE

/-- Explicit `ℤ`-basis representation of any `x ∈ Λ` in `{ζ23^1, ..., ζ23^22}`. -/
private lemma exists_unique_coords_1_22 (x : Λ) :
    ∃! c : Fin 22 → ℤ, x = ∑ i : Fin 22, (c i : Λ) * ζ23 ^ ((i : ℕ) + 1) := by
  let pb := AdjoinRoot.powerBasis' Φ23_monic
  have hdim : pb.dim = 22 := by
    change Φ23.natDegree = 22
    exact Φ23_natDegree
  have hex : ∃ c : Fin 22 → ℤ, x = ∑ i : Fin 22, (c i : Λ) * ζ23 ^ ((i : ℕ) + 1) := by
    let a : Fin 22 → ℤ := fun j => pb.basis.repr x (j.cast hdim.symm)
    have hx : x = ∑ j : Fin 22, (a j : Λ) * ζ23 ^ (j : ℕ) := by
      have h1 := (pb.basis.sum_repr x).symm
      rw [h1]
      refine Fintype.sum_equiv (finCongr hdim) _ _ fun j => ?_
      rw [pb.basis_eq_pow, zsmul_eq_mul]
      simp [a, ζ23, pb]
    have hone : (1 : Λ) = - ∑ i : Fin 22, ζ23 ^ ((i : ℕ) + 1) := by
      have h := sum_ζ23_eq_zero
      rw [Finset.sum_range_succ'] at h
      simp only [pow_zero] at h
      have h2 : ∑ i : Fin 22, ζ23 ^ ((i : ℕ) + 1) = ∑ k ∈ Finset.range 22, ζ23 ^ (k + 1) :=
        Fin.sum_univ_eq_sum_range (fun k => ζ23 ^ (k + 1)) 22
      rw [h2]
      linear_combination h
    refine ⟨fun i => (if h : (i : ℕ) < 21 then a ⟨(i : ℕ) + 1, by omega⟩ else 0) - a 0, ?_⟩
    rw [hx, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
    rw [show (a 0 : Λ) = (a 0 : Λ) * 1 by ring, hone]
    simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib, mul_neg, Finset.mul_sum]
    have hsplit : ∑ i : Fin 22, ((if h : (i : ℕ) < 21 then a ⟨(i : ℕ) + 1, by omega⟩ else 0 : ℤ) : Λ) *
        ζ23 ^ ((i : ℕ) + 1) = ∑ i : Fin 21, (a i.succ : Λ) * ζ23 ^ ((i : ℕ) + 1) := by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.is_lt, ↓reduceDIte, Fin.val_last, lt_self_iff_false,
        Int.cast_zero, zero_mul, add_zero]
      rfl
    rw [hsplit]
    ring
  obtain ⟨c, hc⟩ := hex
  refine ⟨c, hc, fun d hd => ?_⟩
  have hdiff : ∑ i : Fin 22, ((c i - d i : ℤ) : Λ) * ζ23 ^ ((i : ℕ) + 1) = 0 := by
    simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
    rw [← hc, ← hd, sub_self]
  have hshift : ∑ i : Fin 22, ((c i - d i : ℤ) : Λ) * ζ23 ^ (i : ℕ) = 0 := by
    have hmul := congrArg (· * ζ23 ^ 22) hdiff
    simp only [zero_mul, Finset.sum_mul] at hmul
    rw [← hmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, ← pow_add, show (i : ℕ) + 1 + 22 = (i : ℕ) + 23 by omega, pow_add, ζ23_pow_23,
      mul_one]
  have hlin : ∀ i : Fin 22, c i - d i = 0 := by
    have hsum : ∑ j : Fin pb.dim, (c (j.cast hdim) - d (j.cast hdim)) • pb.basis j = 0 := by
      rw [← hshift]
      refine Fintype.sum_equiv (finCongr hdim) _ _ fun j => ?_
      rw [pb.basis_eq_pow, zsmul_eq_mul]
      rfl
    have hall := Fintype.linearIndependent_iff.mp pb.basis.linearIndependent _ hsum
    intro i
    simpa using hall (i.cast hdim.symm)
  funext i
  exact (sub_eq_zero.mp (hlin i)).symm

/-- Quadratic residues mod 23 in `{1, ..., 22}`. -/
private def Q23 : Finset ℕ := {1, 2, 3, 4, 6, 8, 9, 12, 13, 16, 18}

/-- Quadratic non-residues mod 23 in `{1, ..., 22}`. -/
private def N23 : Finset ℕ := {5, 7, 10, 11, 14, 15, 17, 19, 20, 21, 22}

private noncomputable def θ23 : Λ := ∑ q ∈ Q23, ζ23 ^ q
private noncomputable def θ23bar : Λ := ∑ r ∈ N23, ζ23 ^ r

private lemma θ23_add_bar : θ23 + θ23bar = -1 := by
  have h1 : Q23 ∪ N23 = Finset.Icc 1 22 := by decide
  have hdisj : Disjoint Q23 N23 := by decide
  have hsum : θ23 + θ23bar = ∑ i ∈ Finset.Icc 1 22, ζ23 ^ i := by
    rw [θ23, θ23bar, ← Finset.sum_union hdisj, h1]
  have h2 := sum_ζ23_eq_zero
  rw [Finset.sum_range_succ'] at h2
  have h3 : ∑ k ∈ Finset.range 22, ζ23 ^ (k + 1) = ∑ i ∈ Finset.Icc 1 22, ζ23 ^ i := by
    refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_range] at hk; simp only [Finset.mem_Icc]; omega
    · intro a _ b _ h; omega
    · intro b hb; simp only [Finset.mem_Icc] at hb; exact ⟨b - 1, by simp; omega, by omega⟩
    · intro k _; rfl
  rw [h3] at h2
  rw [hsum]
  linear_combination h2

private lemma θ23_sq : θ23 ^ 2 + θ23 + 6 = 0 := by
  have hmul : θ23 ^ 2 = ∑ a ∈ Q23, ∑ b ∈ Q23, ζ23 ^ ((a + b) % 23) := by
    rw [sq, θ23, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← pow_add, ζ23_pow_mod]
  have hgroup : ∑ a ∈ Q23, ∑ b ∈ Q23, ζ23 ^ ((a + b) % 23) =
      ∑ r ∈ Finset.range 23,
        (((Q23 ×ˢ Q23).filter (fun p => (p.1 + p.2) % 23 = r)).card : Λ) * ζ23 ^ r := by
    rw [← Finset.sum_product']
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => (p.1 + p.2) % 23)
      (t := Finset.range 23) (fun p _ => Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num)))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2]]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcount : ∀ r ∈ Finset.range 23,
      ((Q23 ×ˢ Q23).filter (fun p => (p.1 + p.2) % 23 = r)).card =
      if r = 0 then 0 else if r ∈ Q23 then 5 else 6 := by decide
  rw [hmul, hgroup]
  have hrewrite : ∑ r ∈ Finset.range 23,
      (((Q23 ×ˢ Q23).filter (fun p => (p.1 + p.2) % 23 = r)).card : Λ) * ζ23 ^ r =
      5 * θ23 + 6 * θ23bar := by
    rw [Finset.sum_congr rfl fun r hr => by rw [hcount r hr]]
    rw [Finset.sum_range_succ']
    simp only [↓reduceIte, Nat.cast_zero, zero_mul, add_zero]
    have hsplit : Finset.Icc 1 22 = Q23 ∪ N23 := by decide
    have hdisj : Disjoint Q23 N23 := by decide
    have hbij : ∑ k ∈ Finset.range 22,
        ((if k + 1 = 0 then 0 else if k + 1 ∈ Q23 then 5 else 6 : ℕ) : Λ) * ζ23 ^ (k + 1) =
        ∑ r ∈ Finset.Icc 1 22,
          ((if r ∈ Q23 then 5 else 6 : ℕ) : Λ) * ζ23 ^ r := by
      refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
      · intro k hk; simp only [Finset.mem_range] at hk; simp only [Finset.mem_Icc]; omega
      · intro a _ b _ h; omega
      · intro b hb; simp only [Finset.mem_Icc] at hb; exact ⟨b - 1, by simp; omega, by omega⟩
      · intro k _; simp
    rw [hbij, hsplit, Finset.sum_union hdisj]
    have hQ : ∑ r ∈ Q23, ((if r ∈ Q23 then 5 else 6 : ℕ) : Λ) * ζ23 ^ r = 5 * θ23 := by
      rw [θ23, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r hr => by simp [hr]
    have hN : ∑ r ∈ N23, ((if r ∈ Q23 then 5 else 6 : ℕ) : Λ) * ζ23 ^ r = 6 * θ23bar := by
      rw [θ23bar, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r hr => ?_
      have hnot : r ∉ Q23 := Finset.disjoint_right.mp hdisj hr
      simp [hnot]
    rw [hQ, hN]
  rw [hrewrite]
  linear_combination 6 * θ23_add_bar

private lemma τU_neg_one_θ23 : τU (-1 : (ZMod 23)ˣ) θ23 = θ23bar := by
  rw [θ23, θ23bar, map_sum]
  refine Finset.sum_bij (fun q _ => (22 * q) % 23) ?_ ?_ ?_ ?_
  · intro q hq; revert q hq; decide
  · intro a ha b hb hab; revert a ha b hb hab; decide
  · intro r hr; revert r hr; decide
  · intro q _
    rw [map_pow, τU_ζ23, ← pow_mul, ζ23_pow_mod]
    have hval : ((-1 : (ZMod 23)ˣ) : ZMod 23).val = 22 := by decide
    rw [hval]

/-- The subgroup of squares in `(ZMod 23)ˣ` (order 11). -/
private def Q23Units : Finset (ZMod 23)ˣ :=
  Finset.univ.image (fun u : (ZMod 23)ˣ => u ^ 2)

private lemma mem_Q23Units_iff (u : (ZMod 23)ˣ) : u ∈ Q23Units ↔ ∃ v : (ZMod 23)ˣ, v ^ 2 = u := by
  simp [Q23Units]

private lemma Q23Units_mul_mem {u v : (ZMod 23)ˣ} (hu : u ∈ Q23Units) (hv : v ∈ Q23Units) :
    u * v ∈ Q23Units := by
  rw [mem_Q23Units_iff] at hu hv ⊢
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := hv
  exact ⟨a * b, mul_pow a b 2⟩

private lemma Q23Units_inv_mem {u : (ZMod 23)ˣ} (hu : u ∈ Q23Units) :
    u⁻¹ ∈ Q23Units := by
  rw [mem_Q23Units_iff] at hu ⊢
  obtain ⟨a, rfl⟩ := hu
  exact ⟨a⁻¹, inv_pow a 2⟩

private lemma neg_one_not_mem_Q23Units : (-1 : (ZMod 23)ˣ) ∉ Q23Units := by
  rw [mem_Q23Units_iff]
  rintro ⟨v, hv⟩
  have h1 : (v : ZMod 23) ^ 2 = (-1 : ZMod 23) := by
    have := congrArg Units.val hv
    simpa using this
  have h2 : ∀ x : ZMod 23, x ^ 2 ≠ -1 := by decide
  exact h2 (v : ZMod 23) h1

private lemma Q23Units_disj_neg : Disjoint Q23Units (Q23Units.image ((-1 : (ZMod 23)ˣ) * ·)) := by
  rw [Finset.disjoint_left]
  intro u hu hneg
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hneg
  have hmem := Q23Units_mul_mem hu (Q23Units_inv_mem hq)
  rw [mul_assoc, mul_inv_cancel, mul_one] at hmem
  exact neg_one_not_mem_Q23Units hmem

private lemma Q23Units_val_iff (u : (ZMod 23)ˣ) : u ∈ Q23Units ↔ (u : ZMod 23).val ∈ Q23 := by
  have hiff : ∀ x : ZMod 23, x ≠ 0 → ((∃ y : ZMod 23, y ^ 2 = x) ↔ x.val ∈ Q23) := by decide
  rw [mem_Q23Units_iff, ← hiff (u : ZMod 23) u.ne_zero]
  constructor
  · rintro ⟨v, rfl⟩; exact ⟨v, by simp⟩
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by intro h; rw [h, zero_pow (by norm_num)] at hy; exact u.ne_zero hy.symm
    exact ⟨Units.mk0 y hy0, by ext; simpa using hy⟩

private lemma Q23Units_union_neg :
    Q23Units ∪ Q23Units.image ((-1 : (ZMod 23)ˣ) * ·) = Finset.univ := by
  ext u
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, iff_true]
  by_cases hu : u ∈ Q23Units
  · exact Or.inl hu
  · refine Or.inr ⟨-u, ?_, by simp⟩
    rw [Q23Units_val_iff] at hu ⊢
    have h1 : ∀ x : ZMod 23, x ≠ 0 → x.val ∉ Q23 → (-x).val ∈ Q23 := by decide
    exact h1 (u : ZMod 23) u.ne_zero hu

/-- Bijection between `Fin 22` and `(ZMod 23)ˣ` sending `i ↦ (i + 1 : ZMod 23)`. -/
private def fin22ToZMod23Units (i : Fin 22) : (ZMod 23)ˣ :=
  Units.mk0 (((i : ℕ) + 1 : ℕ) : ZMod 23) (by
    intro h
    have hval : (((i : ℕ) + 1 : ℕ) : ZMod 23).val = 0 := by rw [h]; rfl
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at hval
    omega)

private def zmod23UnitsToFin22 (u : (ZMod 23)ˣ) : Fin 22 :=
  ⟨(u : ZMod 23).val - 1, by have := ZMod.val_lt (u : ZMod 23); omega⟩

private lemma fin22ToZMod23Units_val (i : Fin 22) :
    ((fin22ToZMod23Units i : (ZMod 23)ˣ) : ZMod 23).val = (i : ℕ) + 1 := by
  change (((i : ℕ) + 1 : ℕ) : ZMod 23).val = (i : ℕ) + 1
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

private lemma zmod23UnitsToFin22_val (u : (ZMod 23)ˣ) :
    (zmod23UnitsToFin22 u : ℕ) + 1 = (u : ZMod 23).val := by
  have hne : (u : ZMod 23) ≠ 0 := u.ne_zero
  have hpos : 0 < (u : ZMod 23).val :=
    Nat.pos_of_ne_zero (fun h => hne (by rw [← ZMod.natCast_zmod_val (u : ZMod 23), h]; simp))
  change (u : ZMod 23).val - 1 + 1 = (u : ZMod 23).val
  omega

private lemma fin22_units_left_inv (i : Fin 22) : zmod23UnitsToFin22 (fin22ToZMod23Units i) = i := by
  ext
  change ((fin22ToZMod23Units i : (ZMod 23)ˣ) : ZMod 23).val - 1 = (i : ℕ)
  rw [fin22ToZMod23Units_val]; omega

private lemma fin22_units_right_inv (u : (ZMod 23)ˣ) : fin22ToZMod23Units (zmod23UnitsToFin22 u) = u := by
  ext
  change (((zmod23UnitsToFin22 u : ℕ) + 1 : ℕ) : ZMod 23) = (u : ZMod 23)
  rw [zmod23UnitsToFin22_val, ZMod.natCast_zmod_val]

/-- An element of `Λ` fixed by all `τU q` for `q ∈ Q23Units` lies in `ℤ[θ23]`. -/
private lemma fixed_by_Q23_eq (β : Λ) (hfix : ∀ q ∈ Q23Units, τU q β = β) :
    ∃ x y : ℤ, β = (y : Λ) + (x : Λ) * θ23 := by
  obtain ⟨c, hc, huniq⟩ := exists_unique_coords_1_22 β
  have hc_eq : ∀ (u v : (ZMod 23)ˣ), u ∈ Q23Units →
      c (zmod23UnitsToFin22 v) = c (zmod23UnitsToFin22 (u * v)) := by
    intro u v hu
    have hτ : τU u β = ∑ k : Fin 22, (c k : Λ) * ζ23 ^ ((u * fin22ToZMod23Units k : (ZMod 23)ˣ) : ZMod 23).val := by
      rw [hc, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, map_intCast, map_pow, τU_ζ23, ← pow_mul, ζ23_pow_mod]
      congr 2
      rw [Units.val_mul, ZMod.val_mul, fin22ToZMod23Units_val]
    let d : Fin 22 → ℤ := fun m => c (zmod23UnitsToFin22 (u⁻¹ * fin22ToZMod23Units m))
    have hd : β = ∑ m : Fin 22, (d m : Λ) * ζ23 ^ ((m : ℕ) + 1) := by
      rw [← hfix u hu, hτ]
      refine Finset.sum_bij (fun k _ => zmod23UnitsToFin22 (u * fin22ToZMod23Units k)) ?_ ?_ ?_ ?_
      · intro k _; exact Finset.mem_univ _
      · intro a _ b _ hab
        have h1 := congrArg fin22ToZMod23Units hab
        rw [fin22_units_right_inv, fin22_units_right_inv] at h1
        have h2 := mul_left_cancel h1
        have h3 := congrArg zmod23UnitsToFin22 h2
        rwa [fin22_units_left_inv, fin22_units_left_inv] at h3
      · intro m _
        refine ⟨zmod23UnitsToFin22 (u⁻¹ * fin22ToZMod23Units m), Finset.mem_univ _, ?_⟩
        rw [fin22_units_right_inv, mul_inv_cancel_left, fin22_units_left_inv]
      · intro k _
        dsimp [d]
        rw [fin22_units_right_inv, inv_mul_cancel_left, fin22_units_left_inv, zmod23UnitsToFin22_val,
          Units.val_mul]
    have hcd : d = c := huniq d hd
    have hval := congrFun hcd (zmod23UnitsToFin22 (u * v))
    dsimp [d] at hval
    rw [fin22_units_right_inv, inv_mul_cancel_left] at hval
    exact hval
  have hQ_const : ∀ u : (ZMod 23)ˣ, u ∈ Q23Units →
      c (zmod23UnitsToFin22 u) = c (zmod23UnitsToFin22 1) := by
    intro u hu
    have h := hc_eq u 1 hu
    rw [mul_one] at h
    exact h.symm
  have hN_const : ∀ u : (ZMod 23)ˣ, u ∉ Q23Units →
      c (zmod23UnitsToFin22 u) = c (zmod23UnitsToFin22 (-1)) := by
    intro u hu
    have hneg : -u ∈ Q23Units := by
      have hun := Finset.mem_univ u
      rw [← Q23Units_union_neg, Finset.mem_union] at hun
      rcases hun with h | h
      · exact absurd h hu
      · obtain ⟨q, hq, hqu⟩ := Finset.mem_image.mp h
        have : -u = q := by rw [← hqu]; simp
        rwa [this]
    have h := hc_eq (-u) (-1) hneg
    have hmul : (-u) * (-1 : (ZMod 23)ˣ) = u := by simp
    rw [hmul] at h
    exact h.symm
  set a : ℤ := c (zmod23UnitsToFin22 1)
  set b : ℤ := c (zmod23UnitsToFin22 (-1))
  refine ⟨a - b, -b, ?_⟩
  have hβ_ab : β = (a : Λ) * θ23 + (b : Λ) * θ23bar := by
    rw [hc]
    have hbijU : ∑ i : Fin 22, (c i : Λ) * ζ23 ^ ((i : ℕ) + 1) =
        ∑ u : (ZMod 23)ˣ, (c (zmod23UnitsToFin22 u) : Λ) * ζ23 ^ (u : ZMod 23).val := by
      refine Finset.sum_bij (fun i _ => fin22ToZMod23Units i) ?_ ?_ ?_ ?_
      · intro i _; exact Finset.mem_univ _
      · intro i _ j _ hij
        have := congrArg zmod23UnitsToFin22 hij
        rwa [fin22_units_left_inv, fin22_units_left_inv] at this
      · intro u _; exact ⟨zmod23UnitsToFin22 u, Finset.mem_univ _, fin22_units_right_inv u⟩
      · intro i _; rw [fin22_units_left_inv, fin22ToZMod23Units_val]
    rw [hbijU, ← Q23Units_union_neg, Finset.sum_union Q23Units_disj_neg]
    refine congrArg₂ (· + ·) ?_ ?_
    · rw [θ23, Finset.mul_sum]
      refine Finset.sum_bij (fun u _ => (u : ZMod 23).val) ?_ ?_ ?_ ?_
      · intro u hu; exact (Q23Units_val_iff u).mp hu
      · intro u _ v _ huv; ext; exact ZMod.val_injective 23 huv
      · intro q hq
        have hq' : 1 ≤ q ∧ q ≤ 22 := by revert q hq; decide
        let u := fin22ToZMod23Units ⟨q - 1, by omega⟩
        have huval : (u : ZMod 23).val = q := by
          rw [fin22ToZMod23Units_val]; dsimp; omega
        exact ⟨u, (Q23Units_val_iff u).mpr (by rwa [huval]), huval⟩
      · intro u hu; rw [hQ_const u hu]
    · rw [θ23bar, Finset.mul_sum]
      refine Finset.sum_bij (fun u _ => (u : ZMod 23).val) ?_ ?_ ?_ ?_
      · intro u hu
        have hnotQ : u ∉ Q23Units := Finset.disjoint_right.mp Q23Units_disj_neg hu
        have h1 : (u : ZMod 23).val ∈ Finset.Icc 1 22 := by
          have hlt := ZMod.val_lt (u : ZMod 23)
          have hne : (u : ZMod 23) ≠ 0 := u.ne_zero
          have hpos : 0 < (u : ZMod 23).val :=
            Nat.pos_of_ne_zero (fun h => hne (by rw [← ZMod.natCast_zmod_val (u : ZMod 23), h]; simp))
          exact Finset.mem_Icc.mpr ⟨hpos, by omega⟩
        have h2 : Finset.Icc 1 22 = Q23 ∪ N23 := by decide
        rw [h2, Finset.mem_union] at h1
        exact h1.resolve_left (fun hq => hnotQ ((Q23Units_val_iff u).mpr hq))
      · intro u _ v _ huv; ext; exact ZMod.val_injective 23 huv
      · intro r hr
        have hr' : 1 ≤ r ∧ r ≤ 22 := by revert r hr; decide
        let u := fin22ToZMod23Units ⟨r - 1, by omega⟩
        have huval : (u : ZMod 23).val = r := by
          rw [fin22ToZMod23Units_val]; dsimp; omega
        have hnotQ : u ∉ Q23Units := by
          intro hq
          have h1 : r ∈ Q23 := by rw [← huval]; exact (Q23Units_val_iff u).mp hq
          have hdisj : Disjoint Q23 N23 := by decide
          exact Finset.disjoint_left.mp hdisj h1 hr
        have hun := Finset.mem_univ u
        rw [← Q23Units_union_neg, Finset.mem_union] at hun
        exact ⟨u, hun.resolve_left hnotQ, huval⟩
      · intro u hu
        have hnotQ : u ∉ Q23Units := Finset.disjoint_right.mp Q23Units_disj_neg hu
        rw [hN_const u hnotQ]
  rw [hβ_ab]
  push_cast
  linear_combination (b : Λ) * θ23_add_bar

/-- **Part 1 Norm Integrality**: The norm of any `α ∈ Λ` is an integer. -/
theorem norm_eq_int (α : Λ) : ∃ m : ℤ, (∏ u : (ZMod 23)ˣ, τU u α) = (m : Λ) := by
  let β : Λ := ∏ q ∈ Q23Units, τU q α
  have hfix : ∀ u ∈ Q23Units, τU u β = β := by
    intro u hu
    rw [map_prod]
    refine Finset.prod_bij (fun q _ => u * q) ?_ ?_ ?_ ?_
    · intro q hq; exact Q23Units_mul_mem hu hq
    · intro a _ b _ h; exact mul_left_cancel h
    · intro r hr
      exact ⟨u⁻¹ * r, Q23Units_mul_mem (Q23Units_inv_mem hu) hr, by simp⟩
    · intro q _; exact (τU_mul u q α).symm
  obtain ⟨x, y, hβ⟩ := fixed_by_Q23_eq β hfix
  have hprod : (∏ u : (ZMod 23)ˣ, τU u α) = β * τU (-1 : (ZMod 23)ˣ) β := by
    rw [← Q23Units_union_neg, Finset.prod_union Q23Units_disj_neg]
    refine congrArg₂ (· * ·) rfl ?_
    rw [Finset.prod_image (fun a _ b _ h => mul_left_cancel h), map_prod]
    refine Finset.prod_congr rfl fun q _ => τU_mul (-1) q α
  have hβbar : τU (-1 : (ZMod 23)ˣ) β = (y : Λ) + (x : Λ) * θ23bar := by
    rw [hβ, map_add, map_mul, map_intCast, map_intCast, τU_neg_one_θ23]
  refine ⟨y ^ 2 - x * y + 6 * x ^ 2, ?_⟩
  rw [hprod, hβbar, hβ]
  push_cast
  linear_combination (x : Λ) * (y : Λ) * θ23_add_bar - (x : Λ) ^ 2 * θ23_sq +
    (x : Λ) ^ 2 * θ23 * θ23_add_bar

/-- **Part 1 Main Theorem**: No element of `Λ = ℤ[ζ_23]` has norm `±47`. -/
theorem no_elem_norm_47 (α : Λ) :
    (∏ u : (ZMod 23)ˣ, τU u α) ≠ 47 ∧ (∏ u : (ZMod 23)ˣ, τU u α) ≠ -47 := by
  let β : Λ := ∏ q ∈ Q23Units, τU q α
  have hfix : ∀ u ∈ Q23Units, τU u β = β := by
    intro u hu
    rw [map_prod]
    refine Finset.prod_bij (fun q _ => u * q) ?_ ?_ ?_ ?_
    · intro q hq; exact Q23Units_mul_mem hu hq
    · intro a _ b _ h; exact mul_left_cancel h
    · intro r hr
      exact ⟨u⁻¹ * r, Q23Units_mul_mem (Q23Units_inv_mem hu) hr, by simp⟩
    · intro q _; exact (τU_mul u q α).symm
  obtain ⟨x, y, hβ⟩ := fixed_by_Q23_eq β hfix
  have hprod : (∏ u : (ZMod 23)ˣ, τU u α) = β * τU (-1 : (ZMod 23)ˣ) β := by
    rw [← Q23Units_union_neg, Finset.prod_union Q23Units_disj_neg]
    refine congrArg₂ (· * ·) rfl ?_
    rw [Finset.prod_image (fun a _ b _ h => mul_left_cancel h), map_prod]
    refine Finset.prod_congr rfl fun q _ => τU_mul (-1) q α
  have hβbar : τU (-1 : (ZMod 23)ˣ) β = (y : Λ) + (x : Λ) * θ23bar := by
    rw [hβ, map_add, map_mul, map_intCast, map_intCast, τU_neg_one_θ23]
  have hnorm_eq : (∏ u : (ZMod 23)ˣ, τU u α) = ((y ^ 2 - x * y + 6 * x ^ 2 : ℤ) : Λ) := by
    rw [hprod, hβbar, hβ]
    push_cast
    linear_combination (x : Λ) * (y : Λ) * θ23_add_bar - (x : Λ) ^ 2 * θ23_sq +
      (x : Λ) ^ 2 * θ23 * θ23_add_bar
  constructor <;> intro h
  · rw [hnorm_eq] at h
    have heq : y ^ 2 - x * y + 6 * x ^ 2 = 47 := intCast_injective_Λ h
    have h4 : (2 * y - x) ^ 2 + 23 * x ^ 2 = 188 := by linarith
    have hx1 : -2 ≤ x := by nlinarith [sq_nonneg (2 * y - x)]
    have hx2 : x ≤ 2 := by nlinarith [sq_nonneg (2 * y - x)]
    interval_cases x <;>
    · have hy1 : -10 ≤ y := by nlinarith
      have hy2 : y ≤ 10 := by nlinarith
      interval_cases y <;> norm_num at h4
  · rw [hnorm_eq] at h
    have heq : y ^ 2 - x * y + 6 * x ^ 2 = -47 := intCast_injective_Λ (by simpa using h)
    have h4 : (2 * y - x) ^ 2 + 23 * x ^ 2 = -188 := by linarith
    nlinarith [sq_nonneg (2 * y - x), sq_nonneg x]


abbrev Γ47 : Type := (ZMod 47)ˣ

/-- The Swan ideal `I = { f : Γ47 → ℤ | ∑ a : Γ47, (f a : ZMod 47) * (a : ZMod 47) = 0 }`. -/
def SwanIdeal : AddSubgroup (Γ47 → ℤ) where
  carrier := { f | ∑ a : Γ47, (f a : ZMod 47) * (a : ZMod 47) = 0 }
  zero_mem' := by simp
  add_mem' := fun {f g} hf hg => by
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
    rw [hf, hg, add_zero]
  neg_mem' := fun {f} hf => by
    simp only [Set.mem_ofPred_eq, Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
    rw [hf, neg_zero]

def swanAct (g : Γ47) (u : SwanIdeal) : SwanIdeal :=
  ⟨fun a => u.1 (g⁻¹ * a), by
    change ∑ a : Γ47, (u.1 (g⁻¹ * a) : ZMod 47) * (a : ZMod 47) = 0
    have hbij : ∑ a : Γ47, (u.1 (g⁻¹ * a) : ZMod 47) * (a : ZMod 47) =
        (g : ZMod 47) * ∑ b : Γ47, (u.1 b : ZMod 47) * (b : ZMod 47) := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun a _ => g⁻¹ * a) ?_ ?_ ?_ ?_
      · intro a _; exact Finset.mem_univ _
      · intro a _ b _ h; exact mul_left_cancel h
      · intro b _; exact ⟨g * b, Finset.mem_univ _, by simp⟩
      · intro a _
        have hg : ((g : ZMod 47) * ((g⁻¹ * a : Γ47) : ZMod 47)) = (a : ZMod 47) := by
          rw [Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
        rw [← hg]; ring
    rw [hbij, u.2, mul_zero]⟩

def permAct {X : Type*} [MulAction Γ47 X] (g : Γ47) (f : X → ℤ) : X → ℤ :=
  fun x => f (g⁻¹ • x)

private lemma swanAct_one (u : SwanIdeal) : swanAct 1 u = u := by
  ext a; simp [swanAct]

private lemma swanAct_mul (g h : Γ47) (u : SwanIdeal) :
    swanAct (g * h) u = swanAct g (swanAct h u) := by
  ext a; simp [swanAct, mul_assoc]

private lemma swanAct_add (g : Γ47) (u v : SwanIdeal) :
    swanAct g (u + v) = swanAct g u + swanAct g v := by
  ext a; rfl

private lemma permAct_one {X : Type*} [MulAction Γ47 X] (f : X → ℤ) : permAct 1 f = f := by
  ext x; simp [permAct]

private lemma permAct_mul {X : Type*} [MulAction Γ47 X] (g h : Γ47) (f : X → ℤ) :
    permAct (g * h) f = permAct g (permAct h f) := by
  ext x; simp [permAct, mul_smul]

private lemma permAct_add {X : Type*} [MulAction Γ47 X] (g : Γ47) (f₁ f₂ : X → ℤ) :
    permAct g (f₁ + f₂) = permAct g f₁ + permAct g f₂ := by
  ext x; rfl

private lemma permAct_zsmul {X : Type*} [MulAction Γ47 X] (g : Γ47) (n : ℤ) (f : X → ℤ) :
    permAct g (n • f) = n • permAct g f := by
  ext x; rfl

private def swanActHom (g : Γ47) : SwanIdeal →+ SwanIdeal where
  toFun := swanAct g
  map_zero' := by ext a; rfl
  map_add' := swanAct_add g

private def dualAct (g : Γ47) (φ : SwanIdeal →+ ℤ) : SwanIdeal →+ ℤ :=
  φ.comp (swanActHom g⁻¹)

private lemma dualAct_apply (g : Γ47) (φ : SwanIdeal →+ ℤ) (u : SwanIdeal) :
    dualAct g φ u = φ (swanAct g⁻¹ u) := rfl

private lemma dualAct_mul (g h : Γ47) (φ : SwanIdeal →+ ℤ) :
    dualAct (g * h) φ = dualAct g (dualAct h φ) := by
  ext u
  simp [dualAct_apply, ← swanAct_mul]

private def δ47 (g : Γ47) : SwanIdeal :=
  ⟨fun a => if a = g then 47 else 0, by
    refine Finset.sum_eq_zero fun a _ => ?_
    have h47 : (47 : ZMod 47) = 0 := by decide
    by_cases h : a = g <;> simp [h, h47]⟩

private lemma swanAct_δ47 (h g : Γ47) : swanAct h (δ47 g) = δ47 (h * g) := by
  ext a
  change (if h⁻¹ * a = g then (47 : ℤ) else 0) = (if a = h * g then 47 else 0)
  have hiff : h⁻¹ * a = g ↔ a = h * g := by
    constructor
    · intro h1; rw [← h1, mul_inv_cancel_left]
    · intro h1; rw [h1, inv_mul_cancel_left]
  simp [hiff]

private lemma sum_δ47_eq (u : SwanIdeal) :
    ∑ g : Γ47, u.1 g • δ47 g = (47 : ℤ) • u := by
  ext a
  rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  change ∑ g : Γ47, u.1 g * (if a = g then (47 : ℤ) else 0) = 47 * u.1 a
  rw [Finset.sum_eq_single a]
  · simp [mul_comm]
  · intro g _ hga; simp [Ne.symm hga]
  · intro ha; exact absurd (Finset.mem_univ a) ha

private lemma card_Γ47 : Fintype.card Γ47 = 46 := by decide

/- ### Step 2.1: Explicit `Γ47`-equivariant splitting `S = S₂ - S₁` and retraction `r` -/

section Splitting

variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [MulAction Γ47 X] [MulAction Γ47 Y]
  (ι : SwanIdeal →+ (X → ℤ)) (π : (X → ℤ) →+ (Y → ℤ))

omit [MulAction Γ47 Y] in
private lemma exists_swan_retraction
    (hι : Function.Injective ι)
    (hπ : Function.Surjective π)
    (hexact : ∀ v, π v = 0 ↔ ∃ u, ι u = v)
    (hι_eq : ∀ g u, ι (swanAct g u) = permAct g (ι u)) :
    ∃ r : (X → ℤ) →+ SwanIdeal,
      (∀ u, r (ι u) = u) ∧ (∀ g v, r (permAct g v) = swanAct g (r v)) := by
  -- Step 1: `ℤ`-linear section of `π` and `ℤ`-linear retraction `ret₀` of `ι`
  choose pre hpre using fun y : Y => hπ (Pi.single y 1)
  let secπ : (Y → ℤ) →+ (X → ℤ) :=
    { toFun := fun w => ∑ y : Y, w y • pre y
      map_zero' := by simp
      map_add' := fun w₁ w₂ => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib] }
  have hπ_sec : ∀ w, π (secπ w) = w := by
    intro w
    dsimp [secπ]
    rw [map_sum]
    ext y
    simp only [Finset.sum_apply, map_zsmul, Pi.smul_apply, smul_eq_mul, hpre]
    rw [Finset.sum_eq_single y]
    · simp
    · intro y' _ hy'; simp [Pi.single_eq_of_ne (Ne.symm hy')]
    · intro hy; exact absurd (Finset.mem_univ y) hy
  have hker : ∀ v : X → ℤ, ∃ u : SwanIdeal, ι u = v - secπ (π v) := fun v =>
    (hexact _).mp (by rw [map_sub, hπ_sec, sub_self])
  choose ret₀Fun hret₀Fun using hker
  let ret₀ : (X → ℤ) →+ SwanIdeal :=
    { toFun := ret₀Fun
      map_zero' := hι (by rw [hret₀Fun, map_zero, map_zero, map_zero, sub_self])
      map_add' := fun v₁ v₂ => hι (by
        rw [map_add, hret₀Fun, hret₀Fun, hret₀Fun, map_add, map_add]
        abel) }
  have hret₀_ι : ∀ u, ret₀ (ι u) = u := fun u => hι (by
    change ι (ret₀Fun (ι u)) = ι u
    rw [hret₀Fun, (hexact (ι u)).mpr ⟨u, rfl⟩, map_zero, sub_zero])
  -- Step 2: Dual pairing `q : (X → ℤ) →+ (SwanIdeal →+ ℤ)` and `ℤ`-linear section `s₀`
  let q : (X → ℤ) →+ (SwanIdeal →+ ℤ) :=
    { toFun := fun w =>
        { toFun := fun u => ∑ x : X, w x * ι u x
          map_zero' := by simp
          map_add' := fun u₁ u₂ => by
            simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib] }
      map_zero' := by ext u; simp
      map_add' := fun w₁ w₂ => by
        ext u
        simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply, Pi.add_apply,
          add_mul, Finset.sum_add_distrib] }
  have hq_eq : ∀ g w, q (permAct g w) = dualAct g (q w) := by
    intro g w
    ext u
    change ∑ x : X, w (g⁻¹ • x) * ι u x = ∑ x : X, w x * ι (swanAct g⁻¹ u) x
    refine Finset.sum_bij (fun x _ => g⁻¹ • x) ?_ ?_ ?_ ?_
    · intro x _; exact Finset.mem_univ _
    · intro a _ b _ hab
      have := congrArg (g • ·) hab
      simpa [smul_smul] using this
    · intro y _; exact ⟨g • y, Finset.mem_univ _, by simp [smul_smul]⟩
    · intro x _
      rw [hι_eq]
      simp [permAct, smul_smul]
  let s₀ : (SwanIdeal →+ ℤ) →+ (X → ℤ) :=
    { toFun := fun φ x => φ (ret₀ (Pi.single x 1))
      map_zero' := by ext x; simp
      map_add' := fun φ₁ φ₂ => by ext x; simp }
  have hq_s₀ : ∀ φ, q (s₀ φ) = φ := by
    intro φ
    ext u
    change ∑ x : X, φ (ret₀ (Pi.single x 1)) * ι u x = φ u
    have hsum : ∑ x : X, ι u x • Pi.single x (1 : ℤ) = ι u := by
      ext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single x]
      · simp
      · intro x' _ hx'; simp [Pi.single_eq_of_ne (Ne.symm hx')]
      · intro hx; exact absurd (Finset.mem_univ x) hx
    calc ∑ x : X, φ (ret₀ (Pi.single x 1)) * ι u x
        = ∑ x : X, φ (ret₀ (ι u x • Pi.single x 1)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [map_zsmul, map_zsmul, smul_eq_mul, mul_comm]
      _ = φ (ret₀ (∑ x : X, ι u x • Pi.single x 1)) := by rw [map_sum, map_sum]
      _ = φ (ret₀ (ι u)) := by rw [hsum]
      _ = φ u := by rw [hret₀_ι]
  -- Step 3: Averaging `S₁` with `q (S₁ φ) = 46 • φ`
  let S₁ : (SwanIdeal →+ ℤ) →+ (X → ℤ) :=
    { toFun := fun φ => ∑ g : Γ47, permAct g (s₀ (dualAct g⁻¹ φ))
      map_zero' := by
        refine Finset.sum_eq_zero fun g _ => ?_
        have h0 : dualAct g⁻¹ (0 : SwanIdeal →+ ℤ) = 0 := by ext u; rfl
        rw [h0, map_zero]; ext x; rfl
      map_add' := fun φ₁ φ₂ => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun g _ => ?_
        have hadd : dualAct g⁻¹ (φ₁ + φ₂) = dualAct g⁻¹ φ₁ + dualAct g⁻¹ φ₂ := by ext u; rfl
        rw [hadd, map_add, permAct_add] }
  have hS₁_eq : ∀ h φ, S₁ (dualAct h φ) = permAct h (S₁ φ) := by
    intro h φ
    dsimp [S₁]
    have hperm_sum : ∀ f : Γ47 → (X → ℤ), permAct h (∑ g : Γ47, f g) = ∑ g : Γ47, permAct h (f g) := by
      intro f; ext x; simp [permAct, Finset.sum_apply]
    rw [hperm_sum]
    refine Finset.sum_bij (fun g _ => h⁻¹ * g) ?_ ?_ ?_ ?_
    · intro g _; exact Finset.mem_univ _
    · intro a _ b _ hab; exact mul_left_cancel hab
    · intro g _; exact ⟨h * g, Finset.mem_univ _, by simp⟩
    · intro g _
      rw [← dualAct_mul, ← permAct_mul]
      have h1 : g⁻¹ * h = (h⁻¹ * g)⁻¹ := by simp
      have h2 : h * (h⁻¹ * g) = g := by simp
      rw [h1, h2]
  have hq_S₁ : ∀ φ u, q (S₁ φ) u = 46 * φ u := by
    intro φ u
    dsimp [S₁]
    rw [map_sum]
    simp only [AddMonoidHom.finsetSum_apply]
    have hterm : ∀ g : Γ47, q (permAct g (s₀ (dualAct g⁻¹ φ))) u = φ u := by
      intro g
      rw [hq_eq, dualAct_apply, hq_s₀, dualAct_apply, inv_inv, ← swanAct_mul, mul_inv_cancel,
        swanAct_one]
    simp only [hterm, Finset.sum_const, Finset.card_univ, card_Γ47, nsmul_eq_mul]
    norm_cast
  -- Step 4: `S₂` with `q (S₂ φ) = 47 • φ`
  let r₁ : SwanIdeal →+ ℤ :=
    { toFun := fun u => u.1 1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let x₁ : X → ℤ := s₀ r₁
  have hqx₁ : ∀ u, q x₁ u = u.1 1 := fun u => congrArg (fun f : SwanIdeal →+ ℤ => f u) (hq_s₀ r₁)
  let S₂ : (SwanIdeal →+ ℤ) →+ (X → ℤ) :=
    { toFun := fun φ => ∑ g : Γ47, φ (δ47 g) • permAct g x₁
      map_zero' := by simp
      map_add' := fun φ₁ φ₂ => by
        simp only [AddMonoidHom.add_apply, add_smul, Finset.sum_add_distrib] }
  have hS₂_eq : ∀ h φ, S₂ (dualAct h φ) = permAct h (S₂ φ) := by
    intro h φ
    dsimp [S₂]
    have hperm_sum : ∀ f : Γ47 → (X → ℤ), permAct h (∑ g : Γ47, f g) = ∑ g : Γ47, permAct h (f g) := by
      intro f; ext x; simp [permAct, Finset.sum_apply]
    rw [hperm_sum]
    refine Finset.sum_bij (fun g _ => h⁻¹ * g) ?_ ?_ ?_ ?_
    · intro g _; exact Finset.mem_univ _
    · intro a _ b _ hab; exact mul_left_cancel hab
    · intro g _; exact ⟨h * g, Finset.mem_univ _, by simp⟩
    · intro g _
      rw [dualAct_apply, swanAct_δ47, permAct_zsmul, ← permAct_mul, mul_inv_cancel_left]
  have hq_S₂ : ∀ φ u, q (S₂ φ) u = 47 * φ u := by
    intro φ u
    dsimp [S₂]
    rw [map_sum]
    simp only [AddMonoidHom.finsetSum_apply]
    have hterm : ∀ g : Γ47, q (φ (δ47 g) • permAct g x₁) u = φ (u.1 g • δ47 g) := by
      intro g
      rw [map_zsmul, AddMonoidHom.smul_apply, smul_eq_mul, hq_eq, dualAct_apply, hqx₁, map_zsmul,
        smul_eq_mul]
      have h1 : (swanAct g⁻¹ u).1 1 = u.1 g := by simp [swanAct]
      rw [h1, mul_comm]
    calc ∑ g : Γ47, q (φ (δ47 g) • permAct g x₁) u
        = ∑ g : Γ47, φ (u.1 g • δ47 g) := Finset.sum_congr rfl fun g _ => hterm g
      _ = φ (∑ g : Γ47, u.1 g • δ47 g) := (map_sum φ _ _).symm
      _ = φ ((47 : ℤ) • u) := by rw [sum_δ47_eq]
      _ = 47 * φ u := by rw [map_zsmul, smul_eq_mul]
  -- Step 5: `S = S₂ - S₁` splits `q` equivariantly
  let S : (SwanIdeal →+ ℤ) →+ (X → ℤ) := S₂ - S₁
  have hS_eq : ∀ h φ, S (dualAct h φ) = permAct h (S φ) := by
    intro h φ
    change S₂ (dualAct h φ) - S₁ (dualAct h φ) = permAct h (S₂ φ - S₁ φ)
    rw [hS₂_eq, hS₁_eq]
    ext x; simp [permAct]
  have hq_S : ∀ φ u, q (S φ) u = φ u := by
    intro φ u
    change q (S₂ φ - S₁ φ) u = φ u
    rw [map_sub, AddMonoidHom.sub_apply, hq_S₂, hq_S₁]
    omega
  -- Step 6: Dualize `S` back to `r : (X → ℤ) →+ SwanIdeal`
  let evalAt : Γ47 → (SwanIdeal →+ ℤ) := fun a =>
    { toFun := fun u => u.1 a
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have heval_eq : ∀ g a, dualAct g⁻¹ (evalAt a) = evalAt (g⁻¹ * a) := by
    intro g a
    ext u
    simp [dualAct_apply, evalAt, swanAct]
  -- Show `∑ a, (a.val : ℤ) • S (evalAt a) = 47 • S ψ₀`
  have hdvd : ∀ u : SwanIdeal, (47 : ℤ) ∣ ∑ a : Γ47, ((a : ZMod 47).val : ℤ) * u.1 a := by
    intro u
    change ((47 : ℕ) : ℤ) ∣ ∑ a : Γ47, ((a : ZMod 47).val : ℤ) * u.1 a
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    have h1 : ∑ a : Γ47, ((a : ZMod 47).val : ZMod 47) * (u.1 a : ZMod 47) =
        ∑ a : Γ47, (u.1 a : ZMod 47) * (a : ZMod 47) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [ZMod.natCast_zmod_val, mul_comm]
    rw [h1]
    exact u.2
  let ψ₀ : SwanIdeal →+ ℤ :=
    { toFun := fun u => (∑ a : Γ47, ((a : ZMod 47).val : ℤ) * u.1 a) / 47
      map_zero' := by simp
      map_add' := fun u₁ u₂ => by
        have h1 := Int.mul_ediv_cancel' (hdvd u₁)
        have h2 := Int.mul_ediv_cancel' (hdvd u₂)
        have h12 := Int.mul_ediv_cancel' (hdvd (u₁ + u₂))
        have hsum : ∑ a : Γ47, ((a : ZMod 47).val : ℤ) * (u₁ + u₂).1 a =
            (∑ a : Γ47, ((a : ZMod 47).val : ℤ) * u₁.1 a) +
            (∑ a : Γ47, ((a : ZMod 47).val : ℤ) * u₂.1 a) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun a _ => by
            change ((a : ZMod 47).val : ℤ) * (u₁.1 a + u₂.1 a) = _
            ring
        linarith }
  have hsum_eval : ∑ a : Γ47, ((a : ZMod 47).val : ℤ) • evalAt a = (47 : ℤ) • ψ₀ := by
    ext u
    simp only [AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply, smul_eq_mul]
    exact (Int.mul_ediv_cancel' (hdvd u)).symm
  have hS_mod47 : ∀ x : X, ∑ a : Γ47, (S (evalAt a) x : ZMod 47) * (a : ZMod 47) = 0 := by
    intro x
    have h1 := congrArg (fun φ => S φ x) hsum_eval
    rw [map_sum, map_zsmul, Finset.sum_apply] at h1
    have h1' : ∑ a : Γ47, ((a : ZMod 47).val : ℤ) * S (evalAt a) x = 47 * S ψ₀ x := by
      have hterm : ∀ a : Γ47, S (((a : ZMod 47).val : ℤ) • evalAt a) x =
          ((a : ZMod 47).val : ℤ) * S (evalAt a) x := fun a => by
        rw [map_zsmul, Pi.smul_apply, smul_eq_mul]
      simpa [hterm, Pi.smul_apply, smul_eq_mul] using h1
    have h2 := congrArg (Int.cast : ℤ → ZMod 47) h1'
    push_cast at h2
    have h3 : ∑ a : Γ47, (S (evalAt a) x : ZMod 47) * (a : ZMod 47) =
        ∑ a : Γ47, (((a : ZMod 47).val : ZMod 47)) * (S (evalAt a) x : ZMod 47) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [ZMod.natCast_zmod_val, mul_comm]
    have h47 : (47 : ZMod 47) = 0 := by decide
    rw [h3, h2, h47, zero_mul]
  let r : (X → ℤ) →+ SwanIdeal :=
    { toFun := fun v =>
        ⟨fun a => ∑ x : X, v x * S (evalAt a) x, by
          change ∑ a : Γ47, ((∑ x : X, v x * S (evalAt a) x : ℤ) : ZMod 47) * (a : ZMod 47) = 0
          push_cast
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_eq_zero fun x _ => ?_
          have hfac : ∑ a : Γ47, (v x : ZMod 47) * (S (evalAt a) x : ZMod 47) * (a : ZMod 47) =
              (v x : ZMod 47) * ∑ a : Γ47, (S (evalAt a) x : ZMod 47) * (a : ZMod 47) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => by ring
          rw [hfac, hS_mod47 x, mul_zero]⟩
      map_zero' := by ext a; simp
      map_add' := fun v₁ v₂ => by
        ext a
        change ∑ x : X, (v₁ x + v₂ x) * S (evalAt a) x =
          (∑ x : X, v₁ x * S (evalAt a) x) + (∑ x : X, v₂ x * S (evalAt a) x)
        simp_rw [add_mul, Finset.sum_add_distrib] }
  refine ⟨r, ?_, ?_⟩
  · intro u
    ext a
    change ∑ x : X, ι u x * S (evalAt a) x = u.1 a
    have hcomm : ∑ x : X, ι u x * S (evalAt a) x = q (S (evalAt a)) u := by
      change ∑ x : X, ι u x * S (evalAt a) x = ∑ x : X, S (evalAt a) x * ι u x
      refine Finset.sum_congr rfl fun x _ => mul_comm _ _
    rw [hcomm, hq_S]
    rfl
  · intro g v
    ext a
    change ∑ x : X, v (g⁻¹ • x) * S (evalAt a) x = ∑ x : X, v x * S (evalAt (g⁻¹ * a)) x
    refine Finset.sum_bij (fun x _ => g⁻¹ • x) ?_ ?_ ?_ ?_
    · intro x _; exact Finset.mem_univ _
    · intro x₁ _ x₂ _ h12
      have := congrArg (g • ·) h12
      simpa [smul_smul] using this
    · intro y _; exact ⟨g • y, Finset.mem_univ _, by simp [smul_smul]⟩
    · intro x _
      congr 1
      have h1 : S (evalAt a) x = permAct g⁻¹ (S (evalAt a)) (g⁻¹ • x) := by
        simp [permAct, smul_smul]
      rw [h1, ← hS_eq, heval_eq]

private lemma exists_prod_equiv
    (hι : Function.Injective ι)
    (hπ : Function.Surjective π)
    (hexact : ∀ v, π v = 0 ↔ ∃ u, ι u = v)
    (hι_eq : ∀ g u, ι (swanAct g u) = permAct g (ι u))
    (hπ_eq : ∀ g v, π (permAct g v) = permAct g (π v)) :
    ∃ e : (X → ℤ) ≃+ (Y → ℤ) × SwanIdeal,
      ∀ g v, e (permAct g v) = (permAct g (e v).1, swanAct g (e v).2) := by
  obtain ⟨r, hr_ι, hr_eq⟩ := exists_swan_retraction ι π hι hπ hexact hι_eq
  choose pre hpre using fun y : Y => hπ (Pi.single y 1)
  let secπ : (Y → ℤ) →+ (X → ℤ) :=
    { toFun := fun w => ∑ y : Y, w y • pre y
      map_zero' := by simp
      map_add' := fun w₁ w₂ => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib] }
  have hπ_sec : ∀ w, π (secπ w) = w := by
    intro w; dsimp [secπ]; rw [map_sum]; ext y
    simp only [Finset.sum_apply, map_zsmul, Pi.smul_apply, smul_eq_mul, hpre]
    rw [Finset.sum_eq_single y]
    · simp
    · intro y' _ hy'; simp [Pi.single_eq_of_ne (Ne.symm hy')]
    · intro hy; exact absurd (Finset.mem_univ y) hy
  let toFun : (X → ℤ) →+ (Y → ℤ) × SwanIdeal :=
    { toFun := fun v => (π v, r v)
      map_zero' := by simp
      map_add' := fun v₁ v₂ => by simp }
  let invFun : (Y → ℤ) × SwanIdeal →+ (X → ℤ) :=
    { toFun := fun p => secπ p.1 - ι (r (secπ p.1)) + ι p.2
      map_zero' := by simp
      map_add' := fun p₁ p₂ => by simp; abel }
  have hleft : Function.LeftInverse invFun toFun := by
    intro v
    dsimp [toFun, invFun]
    have hdiff : π (v - secπ (π v)) = 0 := by rw [map_sub, hπ_sec, sub_self]
    obtain ⟨u, hu⟩ := (hexact _).mp hdiff
    have hru : r (v - secπ (π v)) = u := by rw [← hu, hr_ι]
    rw [map_sub] at hru
    have h1 : ι (r v) - ι (r (secπ (π v))) = v - secπ (π v) := by
      rw [← map_sub, hru, hu]
    abel_nf at h1 ⊢
    linear_combination h1
  have hright : Function.RightInverse invFun toFun := by
    intro p
    dsimp [toFun, invFun]
    ext1
    · simp [map_add, map_sub, hπ_sec, (hexact (ι _)).mpr ⟨_, rfl⟩]
    · simp [map_add, map_sub, hr_ι]
  refine ⟨⟨⟨toFun, invFun, hleft, hright⟩, toFun.map_add'⟩, ?_⟩
  intro g v
  change (π (permAct g v), r (permAct g v)) = (permAct g (π v), swanAct g (r v))
  rw [hπ_eq, hr_eq]

end Splitting


/-- Generator `5` of `Γ47 = (ZMod 47)ˣ`. -/
private def g5 : Γ47 := ⟨5, 19, by decide, by decide⟩

/-- Discrete logarithm base 5 in `Γ47 = (ZMod 47)ˣ`. -/
private def dlog5Aux (g : Γ47) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if g5 ^ n = g then n else dlog5Aux g n

private def dlog5 (g : Γ47) : ℕ := dlog5Aux g 46

private lemma dlog5_lt (g : Γ47) : dlog5 g < 46 := by revert g; decide
private lemma dlog5_pow (g : Γ47) : g5 ^ dlog5 g = g := by revert g; decide
private lemma g5_pow_46 : g5 ^ 46 = 1 := by decide
private lemma g5_pow_eq_one_iff : ∀ k : Fin 46, g5 ^ (k : ℕ) = 1 → (k : ℕ) = 0 := by decide
private lemma dlog5_one : dlog5 1 = 0 := by decide
private lemma dlog5_five : dlog5 g5 = 1 := by decide

private lemma dlog5_mul (g h : Γ47) : dlog5 (g * h) = (dlog5 g + dlog5 h) % 46 := by
  have h1 : g5 ^ dlog5 (g * h) = g5 ^ ((dlog5 g + dlog5 h) % 46) := by
    conv_lhs => rw [dlog5_pow, ← dlog5_pow g, ← dlog5_pow h, ← pow_add]
    conv_lhs => rw [← Nat.div_add_mod (dlog5 g + dlog5 h) 46]
    rw [pow_add, pow_mul, g5_pow_46, one_pow, one_mul]
  set a := dlog5 (g * h)
  set b := (dlog5 g + dlog5 h) % 46
  have ha : a < 46 := dlog5_lt (g * h)
  have hb : b < 46 := Nat.mod_lt _ (by norm_num)
  by_cases hab : a ≤ b
  · have hdiff : g5 ^ (b - a) = 1 := by
      have h2 : g5 ^ a * g5 ^ (b - a) = g5 ^ a * 1 := by
        rw [← pow_add, Nat.add_sub_cancel' hab, mul_one, h1]
      exact mul_left_cancel h2
    have h0 := g5_pow_eq_one_iff ⟨b - a, by omega⟩ hdiff
    dsimp at h0; omega
  · have hdiff : g5 ^ (a - b) = 1 := by
      have h2 : g5 ^ b * g5 ^ (a - b) = g5 ^ b * 1 := by
        rw [← pow_add, Nat.add_sub_cancel' (by omega), mul_one, ← h1]
      exact mul_left_cancel h2
    have h0 := g5_pow_eq_one_iff ⟨a - b, by omega⟩ hdiff
    dsimp at h0; omega

private lemma neg_ζ23_pow_46 : (-ζ23) ^ 46 = 1 := by
  rw [show (46 : ℕ) = 23 * 2 by rfl, pow_mul, neg_pow, show (-1 : Λ) ^ 23 = -1 by norm_num,
    ζ23_pow_23, mul_one]
  ring

private lemma neg_ζ23_pow_mod (n : ℕ) : (-ζ23) ^ n = (-ζ23) ^ (n % 46) := by
  conv_lhs => rw [← Nat.div_add_mod n 46]
  rw [pow_add, pow_mul, neg_ζ23_pow_46, one_pow, one_mul]

/-- Character `χ : Γ47 →* Λ` sending `g5 ↦ -ζ23`. -/
private noncomputable def χ : Γ47 →* Λ where
  toFun g := (-ζ23) ^ dlog5 g
  map_one' := by simp [dlog5_one]
  map_mul' g h := by
    rw [dlog5_mul, ← neg_ζ23_pow_mod, pow_add]

private lemma χ_five : χ g5 = -ζ23 := by simp [χ, dlog5_five]

private lemma χ_eq_one_iff (g : Γ47) : χ g = 1 ↔ g = 1 := by
  constructor
  · intro h
    set k := dlog5 g
    have hk : k < 46 := dlog5_lt g
    have hpow : (-ζ23) ^ k = 1 := h
    have hsq : ζ23 ^ (2 * k) = 1 := by
      have h2 : ((-ζ23) ^ k) ^ 2 = 1 := by rw [hpow, one_pow]
      rw [← pow_mul, mul_comm, pow_mul, neg_sq, ← pow_mul] at h2
      exact h2
    have hdvd23 : 23 ∣ 2 * k := by
      by_contra hndvd
      have hmod0 : 0 < (2 * k) % 23 := Nat.pos_of_ne_zero (fun h0 => hndvd (Nat.dvd_of_mod_eq_zero h0))
      have hmod23 : (2 * k) % 23 < 23 := Nat.mod_lt _ (by norm_num)
      have h1 : ζ23 ^ ((2 * k) % 23) = 1 := by
        have hdiv := Nat.div_add_mod (2 * k) 23
        rw [← hdiv, pow_add, pow_mul, ζ23_pow_23, one_pow, one_mul] at hsq
        exact hsq
      exact ζ23_pow_ne_one hmod0 hmod23 h1
    have hdvd : 23 ∣ k := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr (by norm_num) |>.dvd_of_dvd_mul_left hdvd23
    have hk_cases : k = 0 ∨ k = 23 := by
      obtain ⟨m, hm⟩ := hdvd
      omega
    rcases hk_cases with hk0 | hk23
    · rw [← dlog5_pow g]
      change g5 ^ k = 1
      rw [hk0, pow_zero]
    · rw [hk23, neg_pow, show (-1 : Λ) ^ 23 = -1 by norm_num, ζ23_pow_23, mul_one] at hpow
      have hE := congrArg toE23 hpow
      rw [map_neg, map_one] at hE
      norm_num at hE
  · rintro rfl; exact map_one χ

/- ### Step 2.3: `HomΓ X ≃ₗ[Λ] (O_X → Λ)` and `HomΓ_I ≃ₗ[Λ] q` -/

private noncomputable def HomΓ (X : Type) [MulAction Γ47 X] : Submodule Λ ((X → ℤ) → Λ) where
  carrier := { f | (∀ v₁ v₂, f (v₁ + v₂) = f v₁ + f v₂) ∧ (∀ g v, f (permAct g v) = χ g * f v) }
  add_mem' := fun {f₁ f₂} ⟨ha₁, he₁⟩ ⟨ha₂, he₂⟩ =>
    ⟨fun v₁ v₂ => by simp [ha₁, ha₂]; ring, fun g v => by simp [he₁, he₂]; ring⟩
  zero_mem' := ⟨fun _ _ => by simp, fun _ _ => by simp⟩
  smul_mem' := fun c {f} ⟨ha, he⟩ =>
    ⟨fun v₁ v₂ => by simp [ha, mul_add], fun g v => by simp [he]; ring⟩

private noncomputable def HomΓI : Submodule Λ (SwanIdeal → Λ) where
  carrier := { f | (∀ u₁ u₂, f (u₁ + u₂) = f u₁ + f u₂) ∧ (∀ g u, f (swanAct g u) = χ g * f u) }
  add_mem' := fun {f₁ f₂} ⟨ha₁, he₁⟩ ⟨ha₂, he₂⟩ =>
    ⟨fun u₁ u₂ => by simp [ha₁, ha₂]; ring, fun g u => by simp [he₁, he₂]; ring⟩
  zero_mem' := ⟨fun _ _ => by simp, fun _ _ => by simp⟩
  smul_mem' := fun c {f} ⟨ha, he⟩ =>
    ⟨fun u₁ u₂ => by simp [ha, mul_add], fun g u => by simp [he]; ring⟩

private lemma homΓ_toAddHom {X : Type} [MulAction Γ47 X] (φ : HomΓ X) :
    ∃ f : (X → ℤ) →+ Λ, ∀ v, f v = φ.1 v :=
  ⟨{ toFun := φ.1
     map_zero' := by
       have h := φ.2.1 0 0
       rw [add_zero] at h
       linear_combination -h
     map_add' := φ.2.1 }, fun _ => rfl⟩

private lemma homΓI_toAddHom (φ : HomΓI) :
    ∃ f : SwanIdeal →+ Λ, ∀ u, f u = φ.1 u :=
  ⟨{ toFun := φ.1
     map_zero' := by
       have h := φ.2.1 0 0
       rw [add_zero] at h
       linear_combination -h
     map_add' := φ.2.1 }, fun _ => rfl⟩

private lemma homΓ_equiv_free_orbits (X : Type) [Fintype X] [DecidableEq X] [MulAction Γ47 X] :
    ∃ m : ℕ, Nonempty (HomΓ X ≃ₗ[Λ] (Fin m → Λ)) := by
  classical
  let Xfree : Type := { x : X // ∀ g : Γ47, g • x = x → g = 1 }
  let : MulAction Γ47 Xfree :=
    { smul := fun g x => ⟨g • x.1, fun h hh => by
        have h1 : (g⁻¹ * h * g) • x.1 = x.1 := by
          rw [mul_smul, mul_smul, hh, inv_smul_smul]
        have h2 := x.2 (g⁻¹ * h * g) h1
        have h3 : h = g * (g⁻¹ * h * g) * g⁻¹ := by group
        rw [h2] at h3; simpa using h3⟩
      one_smul := fun x => Subtype.ext (one_smul Γ47 x.1)
      mul_smul := fun g h x => Subtype.ext (mul_smul g h x.1) }
  let O := Quotient (MulAction.orbitRel Γ47 Xfree)
  let : Fintype O := Quotient.fintype (MulAction.orbitRel Γ47 Xfree)
  let rep : O → Xfree := Quotient.out
  have hrep_mk : ∀ o : O, Quotient.mk (MulAction.orbitRel Γ47 Xfree) (rep o) = o :=
    Quotient.out_eq
  let toFun : HomΓ X →ₗ[Λ] (O → Λ) :=
    { toFun := fun φ o => φ.1 (Pi.single (rep o).1 1)
      map_add' := fun φ₁ φ₂ => by ext o; rfl
      map_smul' := fun c φ => by ext o; rfl }
  let invFun : (O → Λ) →ₗ[Λ] HomΓ X :=
    { toFun := fun f =>
        ⟨fun v => ∑ o : O, ∑ g : Γ47, (v (g • (rep o).1) : Λ) * χ g * f o,
         ⟨fun v₁ v₂ => by
            simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib],
          fun h v => by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun o _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_bij (fun g _ => h⁻¹ * g) ?_ ?_ ?_ ?_
            · intro g _; exact Finset.mem_univ _
            · intro a _ b _ hab; exact mul_left_cancel hab
            · intro g _; exact ⟨h * g, Finset.mem_univ _, by simp⟩
            · intro g _
              have hact : permAct h v (g • (rep o).1) = v ((h⁻¹ * g) • (rep o).1) := by
                simp [permAct, mul_smul]
              rw [hact]
              have hχ : χ g = χ h * χ (h⁻¹ * g) := by
                rw [← map_mul, mul_inv_cancel_left]
              rw [hχ]; ring⟩⟩
      map_add' := fun f₁ f₂ => by
        ext v
        change ∑ o : O, ∑ g : Γ47, (v (g • (rep o).1) : Λ) * χ g * (f₁ o + f₂ o) =
          (∑ o : O, ∑ g : Γ47, (v (g • (rep o).1) : Λ) * χ g * f₁ o) +
          (∑ o : O, ∑ g : Γ47, (v (g • (rep o).1) : Λ) * χ g * f₂ o)
        simp only [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c f => by
        ext v
        change ∑ o : O, ∑ g : Γ47, (v (g • (rep o).1) : Λ) * χ g * (c * f o) =
          c * ∑ o : O, ∑ g : Γ47, (v (g • (rep o).1) : Λ) * χ g * f o
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun o _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun g _ => by ring }
  have hsingle_act : ∀ (g : Γ47) (x : X), permAct g (Pi.single x (1 : ℤ)) = Pi.single (g • x) 1 := by
    intro g x; ext y
    simp only [permAct, Pi.single_apply]
    have hiff : g⁻¹ • y = x ↔ y = g • x := by
      constructor
      · intro h; rw [← h, smul_inv_smul]
      · intro h; rw [h, inv_smul_smul]
    simp [hiff]
  have hleft : Function.LeftInverse invFun toFun := by
    intro φ
    obtain ⟨φAdd, hφAdd⟩ := homΓ_toAddHom φ
    obtain ⟨invAdd, hinvAdd⟩ := homΓ_toAddHom (invFun (toFun φ))
    ext v
    rw [← hφAdd, ← hinvAdd]
    have hbasis : v = ∑ x : X, v x • Pi.single x 1 := by
      ext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single x]
      · simp
      · intro x' _ hx'; simp [Pi.single_eq_of_ne (Ne.symm hx')]
      · intro hx; exact absurd (Finset.mem_univ x) hx
    have h1 : ∀ x : X, (invFun (toFun φ)).1 (Pi.single x 1) = φ.1 (Pi.single x 1) := by
      intro x
      by_cases hfree : ∀ g : Γ47, g • x = x → g = 1
      · let xf : Xfree := ⟨x, hfree⟩
        let ox : O := Quotient.mk (MulAction.orbitRel Γ47 Xfree) xf
        have hrel : MulAction.orbitRel Γ47 Xfree xf (rep ox) :=
          Quotient.exact (hrep_mk ox).symm
        obtain ⟨gx, hgx⟩ := hrel
        have hgx1 : gx • (rep ox).1 = x := congrArg Subtype.val hgx
        dsimp [invFun, toFun]
        rw [Finset.sum_eq_single ox]
        · rw [Finset.sum_eq_single gx]
          · rw [hgx1, Pi.single_eq_same, Int.cast_one, one_mul, ← φ.2.2 gx, hsingle_act, hgx1]
          · intro g _ hne
            have hne' : g • (rep ox).1 ≠ x := by
              intro heq
              have h2 : (gx⁻¹ * g) • (rep ox).1 = (rep ox).1 := by
                rw [mul_smul, heq, ← hgx1, inv_smul_smul]
              have h3 := (rep ox).2 (gx⁻¹ * g) h2
              exact hne (by have := congrArg (gx * ·) h3; simpa using this)
            simp [Pi.single_eq_of_ne hne']
          · intro hg; exact absurd (Finset.mem_univ gx) hg
        · intro o _ ho
          refine Finset.sum_eq_zero fun g _ => ?_
          have hne : g • (rep o).1 ≠ x := by
            intro heq
            have hmk : Quotient.mk (MulAction.orbitRel Γ47 Xfree) (rep o) = ox :=
              (Quotient.sound (s := MulAction.orbitRel Γ47 Xfree) ⟨g, Subtype.ext heq⟩).symm
            rw [hrep_mk] at hmk
            exact ho hmk
          simp [Pi.single_eq_of_ne hne]
        · intro hox; exact absurd (Finset.mem_univ ox) hox
      · push Not at hfree
        obtain ⟨g, hgx, hgne⟩ := hfree
        have hφ0 : φ.1 (Pi.single x 1) = 0 := by
          have h1 := φ.2.2 g (Pi.single x 1)
          rw [hsingle_act, hgx] at h1
          have h2 : (χ g - 1) * φ.1 (Pi.single x 1) = 0 := by linear_combination -h1
          have hχne : χ g - 1 ≠ 0 := sub_ne_zero.mpr (mt (χ_eq_one_iff g).mp hgne)
          exact (mul_eq_zero.mp h2).resolve_left hχne
        rw [hφ0]
        dsimp [invFun]
        refine Finset.sum_eq_zero fun o _ => Finset.sum_eq_zero fun h _ => ?_
        have hne : h • (rep o).1 ≠ x := by
          intro heq
          have h2 : (h⁻¹ * g * h) • (rep o).1 = (rep o).1 := by
            rw [mul_smul, mul_smul, heq, hgx, ← heq, inv_smul_smul]
          have h3 := (rep o).2 (h⁻¹ * g * h) h2
          exact hgne (by have := congrArg (fun z => h * z * h⁻¹) h3; simpa using this)
        simp [Pi.single_eq_of_ne hne]
    conv_lhs => rw [hbasis]
    conv_rhs => rw [hbasis]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_zsmul, map_zsmul, hinvAdd, hφAdd, h1 x]
  have hright : Function.RightInverse invFun toFun := by
    intro f
    ext o
    dsimp [toFun, invFun]
    rw [Finset.sum_eq_single o]
    · rw [Finset.sum_eq_single (1 : Γ47)]
      · simp
      · intro g _ hg
        have hne : g • (rep o).1 ≠ (rep o).1 := fun heq => hg ((rep o).2 g heq)
        simp [Pi.single_eq_of_ne hne]
      · intro h1; exact absurd (Finset.mem_univ (1 : Γ47)) h1
    · intro o' _ ho'
      refine Finset.sum_eq_zero fun g _ => ?_
      have hne : g • (rep o').1 ≠ (rep o).1 := by
        intro heq
        have hmk : Quotient.mk (MulAction.orbitRel Γ47 Xfree) (rep o') =
            Quotient.mk (MulAction.orbitRel Γ47 Xfree) (rep o) :=
          (Quotient.sound (s := MulAction.orbitRel Γ47 Xfree) ⟨g, Subtype.ext heq⟩).symm
        rw [hrep_mk, hrep_mk] at hmk
        exact ho' hmk
      simp [Pi.single_eq_of_ne hne]
    · intro ho; exact absurd (Finset.mem_univ o) ho
  let eO : HomΓ X ≃ₗ[Λ] (O → Λ) := LinearEquiv.ofLinearMap toFun invFun
    (LinearMap.ext hright) (LinearMap.ext hleft)
  let eFin : O ≃ Fin (Fintype.card O) := Fintype.equivFin O
  exact ⟨Fintype.card O, ⟨eO.trans (LinearEquiv.funCongrLeft Λ Λ eFin.symm)⟩⟩

/-- Evaluation `Λ →+* ZMod 47` sending `ζ23 ↦ -5`. -/
private noncomputable def evNeg5 : Λ →+* ZMod 47 :=
  AdjoinRoot.lift (Int.castRingHom (ZMod 47)) (-5 : ZMod 47) (by
    rw [Φ23_eq_sum, Polynomial.eval₂_finsetSum]
    simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X]
    decide)

private lemma evNeg5_ζ23 : evNeg5 ζ23 = -5 := by simp [evNeg5, ζ23]

private lemma evNeg5_χ (g : Γ47) : evNeg5 (χ g) = (g : ZMod 47) := by
  dsimp [χ]
  rw [map_pow, map_neg, evNeg5_ζ23]
  have h5 : -(-5 : ZMod 47) = (g5 : ZMod 47) := by decide
  rw [h5, ← Units.val_pow_eq_pow_val, dlog5_pow]

private lemma ker_evNeg5_iff (z : Λ) :
    evNeg5 z = 0 ↔ ∃ a b : Λ, z = 47 * a + (ζ23 + 5) * b := by
  constructor
  · intro hz
    induction z using AdjoinRoot.induction_on with
    | ih P =>
      have hdvd : (X - C (-5 : ℤ)) ∣ (P - C (P.eval (-5))) :=
        Polynomial.dvd_iff_isRoot.mpr (by simp [Polynomial.IsRoot])
      obtain ⟨Q, hQ⟩ := hdvd
      have hP : P = (X + 5) * Q + C (P.eval (-5)) := by
        have h1 : X - C (-5 : ℤ) = X + 5 := by simp [sub_eq_add_neg]
        rw [h1] at hQ
        linear_combination hQ
      have hz_eq : AdjoinRoot.mk Φ23 P =
          (ζ23 + 5) * AdjoinRoot.mk Φ23 Q + ((P.eval (-5) : ℤ) : Λ) := by
        conv_lhs => rw [hP]
        simp [map_add, map_mul, map_ofNat, ζ23, AdjoinRoot.mk_X]
      rw [hz_eq, map_add, map_mul, map_add, evNeg5_ζ23, map_ofNat, map_intCast] at hz
      have hzero : (-5 + 5 : ZMod 47) = 0 := by ring
      rw [hzero, zero_mul, zero_add] at hz
      have h47 : ((47 : ℕ) : ℤ) ∣ P.eval (-5) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
      obtain ⟨k, hk⟩ := h47
      refine ⟨(k : Λ), AdjoinRoot.mk Φ23 Q, ?_⟩
      rw [hz_eq, hk]
      push_cast; ring
  · rintro ⟨a, b, rfl⟩
    rw [map_add, map_mul, map_mul, map_add, evNeg5_ζ23, map_ofNat, map_ofNat]
    have h1 : (47 : ZMod 47) = 0 := by decide
    have h2 : (-5 + 5 : ZMod 47) = 0 := by ring
    rw [h1, h2, zero_mul, zero_mul, add_zero]

/-- The ideal `q = { c ∈ Λ | 47 ∣ (ζ23 + 5) * c }`. -/
private def qIdeal : Ideal Λ where
  carrier := { c : Λ | ∃ y : Λ, (47 : Λ) * y = (ζ23 + 5) * c }
  add_mem' := fun {a b} ⟨ya, hya⟩ ⟨yb, hyb⟩ => ⟨ya + yb, by linear_combination hya + hyb⟩
  zero_mem' := ⟨0, by ring⟩
  smul_mem' := fun r {a} ⟨y, hy⟩ => ⟨r * y, by linear_combination r * hy⟩

private lemma fortySeven_ne_zero_Λ : (47 : Λ) ≠ 0 := by
  intro h
  have := intCast_injective_Λ (by simpa using h : ((47 : ℤ) : Λ) = ((0 : ℤ) : Λ))
  norm_num at this

private lemma fortySeven_mem_qIdeal : (47 : Λ) ∈ qIdeal :=
  ⟨ζ23 + 5, by ring⟩

private noncomputable def ψMap : (Γ47 → ℤ) →+ Λ where
  toFun f := ∑ g : Γ47, (f g : Λ) * χ g
  map_zero' := by simp
  map_add' f₁ f₂ := by
    simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]

private lemma ψMap_swanAct (h : Γ47) (u : SwanIdeal) :
    ψMap (swanAct h u).1 = χ h * ψMap u.1 := by
  dsimp [ψMap]
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun g _ => h⁻¹ * g) ?_ ?_ ?_ ?_
  · intro g _; exact Finset.mem_univ _
  · intro a _ b _ hab; exact mul_left_cancel hab
  · intro g _; exact ⟨h * g, Finset.mem_univ _, by simp⟩
  · intro g _
    have hχ : χ g = χ h * χ (h⁻¹ * g) := by rw [← map_mul, mul_inv_cancel_left]
    rw [hχ]; simp [swanAct]; ring

private lemma evNeg5_ψMap (u : SwanIdeal) : evNeg5 (ψMap u.1) = 0 := by
  dsimp [ψMap]
  rw [map_sum]
  have h1 : ∑ g : Γ47, evNeg5 ((u.1 g : Λ) * χ g) =
      ∑ g : Γ47, (u.1 g : ZMod 47) * (g : ZMod 47) := by
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_mul, map_intCast, evNeg5_χ]
  rw [h1]
  exact u.2

private noncomputable def homΓI_equiv_qIdeal : HomΓI ≃ₗ[Λ] qIdeal := by
  classical
  have hmul47 : ∀ (φ : HomΓI) (u : SwanIdeal), 47 * φ.1 u = ψMap u.1 * φ.1 (δ47 1) := by
    intro φ u
    obtain ⟨φAdd, hφAdd⟩ := homΓI_toAddHom φ
    rw [← hφAdd, ← hφAdd]
    have h1 : 47 * φAdd u = φAdd ((47 : ℤ) • u) := by
      rw [map_zsmul, zsmul_eq_mul]; norm_cast
    rw [h1, ← sum_δ47_eq, map_sum]
    dsimp [ψMap]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_zsmul, zsmul_eq_mul, hφAdd, hφAdd]
    have hδ : δ47 g = swanAct g (δ47 1) := by rw [swanAct_δ47, mul_one]
    rw [hδ, φ.2.2]
    ring
  let u₀ : SwanIdeal := ⟨fun a => (if a = g5 then 1 else 0) - (if a = 1 then 5 else 0), by
    show ∑ a : Γ47, (((if a = g5 then (1 : ℤ) else 0) - (if a = 1 then 5 else 0)) : ZMod 47) * (a : ZMod 47) = 0
    decide⟩
  have hψu₀ : ψMap u₀.1 = -(ζ23 + 5) := by
    dsimp [ψMap, u₀]
    simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
    have h1 : ∑ g : Γ47, (((if g = g5 then (1 : ℤ) else 0) : ℤ) : Λ) * χ g = -ζ23 := by
      rw [Finset.sum_eq_single g5]
      · simp [χ_five]
      · intro g _ hg; simp [hg]
      · intro h5; exact absurd (Finset.mem_univ g5) h5
    have h2 : ∑ g : Γ47, (((if g = 1 then (5 : ℤ) else 0) : ℤ) : Λ) * χ g = 5 := by
      rw [Finset.sum_eq_single (1 : Γ47)]
      · simp
      · intro g _ hg; simp [hg]
      · intro h1'; exact absurd (Finset.mem_univ (1 : Γ47)) h1'
    rw [h1, h2]; ring
  let toFun : HomΓI →ₗ[Λ] qIdeal :=
    { toFun := fun φ => ⟨φ.1 (δ47 1), ⟨-φ.1 u₀, by
        have h := hmul47 φ u₀
        rw [hψu₀] at h
        linear_combination -h⟩⟩
      map_add' := fun φ₁ φ₂ => by ext; rfl
      map_smul' := fun c φ => by ext; rfl }
  have hex : ∀ (c : qIdeal) (u : SwanIdeal), ∃ z : Λ, 47 * z = ψMap u.1 * c.1 := by
    intro c u
    obtain ⟨y, hy⟩ := c.2
    obtain ⟨a, b, hab⟩ := (ker_evNeg5_iff (ψMap u.1)).mp (evNeg5_ψMap u)
    refine ⟨a * c.1 + b * y, ?_⟩
    rw [hab]
    linear_combination b * hy
  choose invAux hinvAux using hex
  let invFun : qIdeal →ₗ[Λ] HomΓI :=
    { toFun := fun c =>
        ⟨fun u => invAux c u,
         ⟨fun u₁ u₂ => by
            have h := hinvAux c (u₁ + u₂)
            have h1 := hinvAux c u₁
            have h2 := hinvAux c u₂
            have hadd : ψMap (u₁ + u₂).1 = ψMap u₁.1 + ψMap u₂.1 := map_add ψMap u₁.1 u₂.1
            rw [hadd] at h
            have hsub : (47 : Λ) * (invAux c (u₁ + u₂) - (invAux c u₁ + invAux c u₂)) = 0 := by
              linear_combination h - h1 - h2
            exact sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_left fortySeven_ne_zero_Λ),
          fun g u => by
            have h := hinvAux c (swanAct g u)
            have h1 := hinvAux c u
            rw [ψMap_swanAct] at h
            have hsub : (47 : Λ) * (invAux c (swanAct g u) - χ g * invAux c u) = 0 := by
              linear_combination h - χ g * h1
            exact sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_left fortySeven_ne_zero_Λ)⟩⟩
      map_add' := fun c₁ c₂ => by
        ext u
        have h := hinvAux (c₁ + c₂) u
        have h1 := hinvAux c₁ u
        have h2 := hinvAux c₂ u
        have hsub : (47 : Λ) * (invAux (c₁ + c₂) u - (invAux c₁ u + invAux c₂ u)) = 0 := by
          have hc : (c₁ + c₂).1 = c₁.1 + c₂.1 := rfl
          rw [hc] at h
          linear_combination h - h1 - h2
        exact sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_left fortySeven_ne_zero_Λ)
      map_smul' := fun r c => by
        ext u
        have h := hinvAux (r • c) u
        have h1 := hinvAux c u
        have hsub : (47 : Λ) * (invAux (r • c) u - r * invAux c u) = 0 := by
          have hc : (r • c).1 = r * c.1 := rfl
          rw [hc] at h
          linear_combination h - r * h1
        exact sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_left fortySeven_ne_zero_Λ) }
  have hleft : Function.LeftInverse invFun toFun := by
    intro φ
    ext u
    have h := hinvAux (toFun φ) u
    have h1 := hmul47 φ u
    have hsub : (47 : Λ) * (invAux (toFun φ) u - φ.1 u) = 0 := by
      linear_combination h - h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_left fortySeven_ne_zero_Λ)
  have hright : Function.RightInverse invFun toFun := by
    intro c
    ext
    dsimp [toFun, invFun]
    have h := hinvAux c (δ47 1)
    have hψδ : ψMap (δ47 1).1 = 47 := by
      dsimp [ψMap, δ47]
      rw [Finset.sum_eq_single (1 : Γ47)]
      · simp
      · intro g _ hg; simp [hg]
      · intro h1; exact absurd (Finset.mem_univ (1 : Γ47)) h1
    rw [hψδ] at h
    have hsub : (47 : Λ) * (invAux c (δ47 1) - c.1) = 0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_left fortySeven_ne_zero_Λ)
  exact LinearEquiv.ofLinearMap toFun invFun (LinearMap.ext hright) (LinearMap.ext hleft)

/- ### Step 2.4: Rank equality `m = n + 1` and Cramer's rule (`qIdeal` is principal) -/

private lemma rank_eq_succ {m n : ℕ} (e : (Fin m → Λ) ≃ₗ[Λ] (Fin n → Λ) × qIdeal) :
    m = n + 1 := by
  let f : (Fin m → Λ) →ₗ[Λ] (Fin (n + 1) → Λ) :=
    { toFun := fun v => Fin.snoc (α := fun _ => Λ) (e v).1 ((e v).2 : Λ)
      map_add' := fun v₁ v₂ => by
        rw [map_add]; ext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      map_smul' := fun r v => by
        rw [map_smul]; ext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp }
  let g : (Fin (n + 1) → Λ) →ₗ[Λ] (Fin m → Λ) :=
    { toFun := fun w => e.symm (fun j => 47 * w j.castSucc,
        ⟨47 * w (Fin.last n), ⟨(ζ23 + 5) * w (Fin.last n), by ring⟩⟩)
      map_add' := fun w₁ w₂ => by
        rw [← map_add]; congr 1
        refine Prod.ext (by ext j; simp [mul_add]) (by ext; simp [mul_add])
      map_smul' := fun r w => by
        rw [← map_smul]; congr 1
        refine Prod.ext (by ext j; simp; ring) (by ext; simp; ring) }
  have hfg : ∀ w, f (g w) = (47 : Λ) • w := by
    intro w; dsimp [f, g]
    rw [LinearEquiv.apply_symm_apply]
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  have hgf : ∀ v, g (f v) = (47 : Λ) • v := by
    intro v; dsimp [f, g]
    have hpair : (fun j : Fin n => 47 * Fin.snoc (α := fun _ => Λ) (e v).1 ((e v).2 : Λ) j.castSucc,
        (⟨47 * Fin.snoc (α := fun _ => Λ) (e v).1 ((e v).2 : Λ) (Fin.last n),
          ⟨(ζ23 + 5) * Fin.snoc (α := fun _ => Λ) (e v).1 ((e v).2 : Λ) (Fin.last n), by ring⟩⟩ : qIdeal)) =
        (47 : Λ) • e v := by
      refine Prod.ext (by ext j; simp) (by ext; simp)
    rw [hpair, map_smul, LinearEquiv.symm_apply_apply]
  let M : Matrix (Fin (n + 1)) (Fin m) Λ := Matrix.of fun i j => f (Pi.single j 1) i
  let N : Matrix (Fin m) (Fin (n + 1)) Λ := Matrix.of fun j i => g (Pi.single i 1) j
  have hMN : M * N = (47 : Λ) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Λ) := by
    ext i k
    simp only [Matrix.mul_apply, M, N, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    have hsum : ∑ j : Fin m, f (Pi.single j 1) i * g (Pi.single k 1) j = f (g (Pi.single k 1)) i := by
      have hvec : g (Pi.single k 1) = ∑ j : Fin m, g (Pi.single k 1) j • Pi.single j 1 := by
        ext j; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_eq_single j]
        · simp
        · intro j' _ hj'; simp [Pi.single_eq_of_ne (Ne.symm hj')]
        · intro hj; exact absurd (Finset.mem_univ j) hj
      conv_rhs => rw [hvec, map_sum]
      simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [hsum, hfg]
    simp [Pi.single_apply]
  have hNM : N * M = (47 : Λ) • (1 : Matrix (Fin m) (Fin m) Λ) := by
    ext j l
    simp only [Matrix.mul_apply, M, N, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    have hsum : ∑ i : Fin (n + 1), g (Pi.single i 1) j * f (Pi.single l 1) i = g (f (Pi.single l 1)) j := by
      have hvec : f (Pi.single l 1) = ∑ i : Fin (n + 1), f (Pi.single l 1) i • Pi.single i 1 := by
        ext i; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_eq_single i]
        · simp
        · intro i' _ hi'; simp [Pi.single_eq_of_ne (Ne.symm hi')]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      conv_rhs => rw [hvec, map_sum]
      simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [hsum, hgf]
    simp [Pi.single_apply]
  have htr : Matrix.trace (M * N) = Matrix.trace (N * M) := Matrix.trace_mul_comm M N
  rw [hMN, hNM, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one, Matrix.trace_one,
    Fintype.card_fin, Fintype.card_fin] at htr
  simp only [smul_eq_mul] at htr
  have hsub : (47 : Λ) * ((n + 1 : ℕ) - (m : ℕ) : Λ) = 0 := by
    push_cast at htr ⊢; linear_combination htr
  have heqΛ : ((n + 1 : ℕ) : Λ) = (m : Λ) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_left fortySeven_ne_zero_Λ)
  have heqE := congrArg toE23 heqΛ
  rw [map_natCast, map_natCast] at heqE
  exact (Nat.cast_injective heqE).symm

/-- Cramer's rule: if `Λ^(n+1) ≃ Λ^n × qIdeal`, then `qIdeal` is principal. -/
private lemma qIdeal_principal_of_equiv {n : ℕ}
    (e : (Fin (n + 1) → Λ) ≃ₗ[Λ] (Fin n → Λ) × qIdeal) :
    ∃ β : Λ, qIdeal = Ideal.span {β} := by
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) Λ :=
    Matrix.of fun i j => Fin.snoc (α := fun _ => Λ) (e (Pi.single j 1)).1 ((e (Pi.single j 1)).2 : Λ) i
  let M : qIdeal → Matrix (Fin (n + 1)) (Fin (n + 1)) Λ := fun x =>
    Matrix.of fun j k => Fin.lastCases (e.symm (0, x) j) (fun l => e.symm (Pi.single l 1, 0) j) k
  have hBM : ∀ x : qIdeal, B * M x =
      Matrix.diagonal (Fin.snoc (α := fun _ => Λ) (fun _ : Fin n => (1 : Λ)) (x : Λ)) := by
    intro x
    ext i k
    simp only [Matrix.mul_apply, B, M, Matrix.of_apply, Matrix.diagonal_apply]
    have hvec : ∀ v : Fin (n + 1) → Λ,
        ∑ j : Fin (n + 1), Fin.snoc (α := fun _ => Λ) (e (Pi.single j 1)).1 ((e (Pi.single j 1)).2 : Λ) i * v j =
        Fin.snoc (α := fun _ => Λ) (e v).1 ((e v).2 : Λ) i := by
      intro v
      have hv : v = ∑ j : Fin (n + 1), v j • Pi.single j 1 := by
        ext j; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_eq_single j]
        · simp
        · intro j' _ hj'; simp [Pi.single_eq_of_ne (Ne.symm hj')]
        · intro hj; exact absurd (Finset.mem_univ j) hj
      conv_rhs => rw [hv, map_sum]
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · simp only [Fin.snoc_last, Prod.snd_sum, map_smul, Prod.smul_snd]
        rw [AddSubmonoidClass.coe_finsetSum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [SetLike.val_smul, smul_eq_mul, mul_comm]
      · simp only [Fin.snoc_castSucc, Prod.fst_sum, Finset.sum_apply, map_smul, Prod.smul_fst,
          Pi.smul_apply, smul_eq_mul, mul_comm]
    refine Fin.lastCases ?_ (fun l => ?_) k
    · simp only [Fin.lastCases_last]
      rw [hvec, LinearEquiv.apply_symm_apply]
      refine Fin.lastCases ?_ (fun i' => ?_) i <;> simp
    · simp only [Fin.lastCases_castSucc]
      rw [hvec, LinearEquiv.apply_symm_apply]
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · simp [(Fin.castSucc_ne_last l).symm]
      · simp [Pi.single_apply]
  have hdet_mul : ∀ x : qIdeal, B.det * (M x).det = (x : Λ) := by
    intro x
    rw [← Matrix.det_mul, hBM x, Matrix.det_diagonal, Fin.prod_univ_castSucc]
    simp
  have hBdet_mem : B.det ∈ qIdeal := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    refine qIdeal.sum_mem fun σ _ => ?_
    have hprod_mem : ∏ i : Fin (n + 1), B.transpose (σ i) i ∈ qIdeal := by
      rw [Fin.prod_univ_castSucc]
      refine qIdeal.mul_mem_left _ ?_
      change B (Fin.last n) (σ (Fin.last n)) ∈ qIdeal
      dsimp [B]
      rw [Fin.snoc_last]
      exact (e (Pi.single (σ (Fin.last n)) 1)).2.2
    exact qIdeal.smul_mem _ hprod_mem
  refine ⟨B.det, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem qIdeal).mpr hBdet_mem)⟩
  intro x hx
  rw [Ideal.mem_span_singleton]
  exact ⟨(M ⟨x, hx⟩).det, (hdet_mul ⟨x, hx⟩).symm⟩

/- ### Step 2.5: Quotient cardinalities and norm contradiction -/

private lemma natCard_quot_intCast (k : ℤ) (hk : k ≠ 0) :
    Nat.card (Λ ⧸ Ideal.span {(k : Λ)}) = k.natAbs ^ 22 := by
  let pb := AdjoinRoot.powerBasis' Φ23_monic
  have hdim : pb.dim = 22 := Φ23_natDegree
  let e1 : Λ ≃+ (Fin pb.dim → ℤ) := pb.basis.equivFun.toAddEquiv
  let e2 : (Fin pb.dim → ℤ) ≃+ (Fin 22 → ℤ) :=
    { toFun := fun f i => f (i.cast hdim.symm)
      invFun := fun f j => f (j.cast hdim)
      left_inv := fun f => by ext j; simp
      right_inv := fun f => by ext i; simp
      map_add' := fun _ _ => rfl }
  let eΛ : Λ ≃+ (Fin 22 → ℤ) := e1.trans e2
  let qMap : Λ →+ (Fin 22 → ZMod k.natAbs) :=
    { toFun := fun x i => (eΛ x i : ZMod k.natAbs)
      map_zero' := by ext i; simp
      map_add' := fun x y => by ext i; simp }
  have hsurj : Function.Surjective qMap := by
    intro f
    refine ⟨eΛ.symm (fun i => ((f i).val : ℤ)), ?_⟩
    ext i
    dsimp [qMap]
    rw [AddEquiv.apply_symm_apply]
    have : NeZero k.natAbs := ⟨Int.natAbs_ne_zero.mpr hk⟩
    simp
  have hker : ∀ x : Λ, qMap x = 0 ↔ x ∈ Ideal.span {(k : Λ)} := by
    intro x
    rw [Ideal.mem_span_singleton]
    constructor
    · intro hx
      have hdvd : ∀ i : Fin 22, k ∣ eΛ x i := fun i => by
        have hi : (eΛ x i : ZMod k.natAbs) = 0 := congrFun hx i
        exact Int.natAbs_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hi)
      choose c hc using hdvd
      refine ⟨eΛ.symm c, ?_⟩
      apply eΛ.injective
      ext i
      have hmul : eΛ ((k : Λ) * eΛ.symm c) = k • eΛ (eΛ.symm c) := by
        rw [← zsmul_eq_mul, map_zsmul]
      rw [hmul, AddEquiv.apply_symm_apply]
      exact hc i
    · rintro ⟨y, rfl⟩
      ext i
      dsimp [qMap]
      have hmul : eΛ ((k : Λ) * y) = k • eΛ y := by rw [← zsmul_eq_mul, map_zsmul]
      rw [hmul, Pi.smul_apply, zsmul_eq_mul]
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact Int.natAbs_dvd.mpr (dvd_mul_right k _)
  have hker_eq : qMap.ker = (Ideal.span {(k : Λ)}).toAddSubgroup := by
    ext x; exact hker x
  let qEquiv : (Λ ⧸ Ideal.span {(k : Λ)}) ≃+ (Fin 22 → ZMod k.natAbs) :=
    (QuotientAddGroup.quotientAddEquivOfEq hker_eq.symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective qMap hsurj)
  rw [Nat.card_congr qEquiv.toEquiv]
  have : NeZero k.natAbs := ⟨Int.natAbs_ne_zero.mpr hk⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]

private lemma natCard_quot_qIdeal : Nat.card (Λ ⧸ qIdeal) = 47 ^ 21 := by
  let I47 : Ideal Λ := Ideal.span {(47 : Λ)}
  let pIdeal : Ideal Λ := RingHom.ker evNeg5
  have hI47_le_p : I47 ≤ pIdeal := by
    rw [Ideal.span_singleton_le_iff_mem]
    change evNeg5 47 = 0
    rw [map_ofNat]; decide
  -- `Nat.card (Λ ⧸ pIdeal) = 47`
  have hp_surj : Function.Surjective evNeg5 := by
    intro y
    refine ⟨(y.val : Λ), ?_⟩
    rw [map_natCast, ZMod.natCast_zmod_val]
  have hcard_p : Nat.card (Λ ⧸ pIdeal) = 47 := by
    let e := RingHom.quotientKerEquivOfSurjective hp_surj
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card]
  -- `Nat.card (Λ ⧸ I47) = 47 ^ 22`
  have hcard_47 : Nat.card (Λ ⧸ I47) = 47 ^ 22 := by
    simpa using natCard_quot_intCast 47 (by norm_num)
  -- `Λ ⧸ qIdeal ≃+ pIdeal / I47` via multiplication by `ζ23 + 5`
  let pMod : AddSubgroup (Λ ⧸ I47) := pIdeal.toAddSubgroup.map (Ideal.Quotient.mk I47).toAddMonoidHom
  let μ : Λ →+ pMod :=
    { toFun := fun x => ⟨Ideal.Quotient.mk I47 ((ζ23 + 5) * x), by
        refine ⟨(ζ23 + 5) * x, ?_, rfl⟩
        change evNeg5 ((ζ23 + 5) * x) = 0
        rw [map_mul, map_add, evNeg5_ζ23, map_ofNat]
        have h0 : (-5 + 5 : ZMod 47) = 0 := by ring
        rw [h0, zero_mul]⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [mul_add] }
  have hμ_surj : Function.Surjective μ := by
    rintro ⟨z, hz⟩
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨a, b, rfl⟩ := (ker_evNeg5_iff w).mp hw
    refine ⟨b, ?_⟩
    ext
    dsimp [μ]
    rw [Ideal.Quotient.eq]
    change (ζ23 + 5) * b - (47 * a + (ζ23 + 5) * b) ∈ I47
    rw [show (ζ23 + 5) * b - (47 * a + (ζ23 + 5) * b) = 47 * (-a) by ring]
    exact Ideal.mem_span_singleton.mpr ⟨-a, rfl⟩
  have hμ_ker : μ.ker = qIdeal.toAddSubgroup := by
    ext x
    rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, Subtype.ext_iff]
    change Ideal.Quotient.mk I47 ((ζ23 + 5) * x) = 0 ↔ ∃ y : Λ, (47 : Λ) * y = (ζ23 + 5) * x
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩
  let eμ : (Λ ⧸ qIdeal) ≃+ pMod :=
    (QuotientAddGroup.quotientAddEquivOfEq hμ_ker.symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective μ hμ_surj)
  -- Quotient of `Λ ⧸ I47` by `pMod` is `Λ ⧸ pIdeal`
  let proj : (Λ ⧸ I47) →+ (Λ ⧸ pIdeal) :=
    (Ideal.Quotient.factor hI47_le_p).toAddMonoidHom
  have hproj_surj : Function.Surjective proj := Ideal.Quotient.factor_surjective hI47_le_p
  have hproj_ker : proj.ker = pMod := by
    ext z
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    change Ideal.Quotient.mk pIdeal w = 0 ↔ ∃ u ∈ pIdeal, Ideal.Quotient.mk I47 u = Ideal.Quotient.mk I47 w
    rw [Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro hw; exact ⟨w, hw, rfl⟩
    · rintro ⟨u, hu, heq⟩
      have hdiff : u - w ∈ I47 := Ideal.Quotient.eq.mp heq
      have hsub := pIdeal.sub_mem hu (hI47_le_p hdiff)
      simpa using hsub
  have hcard_mul : Nat.card pMod * Nat.card (Λ ⧸ pIdeal) = Nat.card (Λ ⧸ I47) := by
    have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup pMod
    have h2 : Nat.card ((Λ ⧸ I47) ⧸ pMod) = Nat.card (Λ ⧸ pIdeal) := by
      let e := (QuotientAddGroup.quotientAddEquivOfEq hproj_ker.symm).trans
        (QuotientAddGroup.quotientKerEquivOfSurjective proj hproj_surj)
      exact Nat.card_congr e.toEquiv
    rw [h1, h2, mul_comm]
  rw [Nat.card_congr eμ.toEquiv]
  rw [hcard_p, hcard_47] at hcard_mul
  have : Nat.card pMod * 47 = 47 ^ 21 * 47 := by rw [hcard_mul]; ring
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) this

private lemma natCard_quot_mul (x y : Λ) (hx : x ≠ 0) :
    Nat.card (Λ ⧸ Ideal.span {x * y}) =
    Nat.card (Λ ⧸ Ideal.span {x}) * Nat.card (Λ ⧸ Ideal.span {y}) := by
  let Ixy : Ideal Λ := Ideal.span {x * y}
  let Ix : Ideal Λ := Ideal.span {x}
  let Iy : Ideal Λ := Ideal.span {y}
  have hle : Ixy ≤ Ix := (Ideal.span_singleton_le_iff_mem Ix).mpr (Ideal.mem_span_singleton.mpr ⟨y, rfl⟩)
  let proj : (Λ ⧸ Ixy) →+ (Λ ⧸ Ix) := (Ideal.Quotient.factor hle).toAddMonoidHom
  have hsurj : Function.Surjective proj := Ideal.Quotient.factor_surjective hle
  let mulX : Λ →+ proj.ker :=
    { toFun := fun a => ⟨Ideal.Quotient.mk Ixy (x * a), by
        change Ideal.Quotient.mk Ix (x * a) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_span_singleton.mpr ⟨a, rfl⟩⟩
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp [mul_add] }
  have hmulX_surj : Function.Surjective mulX := by
    rintro ⟨z, hz⟩
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    change Ideal.Quotient.mk Ix w = 0 at hz
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hz
    obtain ⟨a, rfl⟩ := hz
    exact ⟨a, rfl⟩
  have hmulX_ker : mulX.ker = Iy.toAddSubgroup := by
    ext a
    rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, Subtype.ext_iff]
    change Ideal.Quotient.mk Ixy (x * a) = 0 ↔ a ∈ Iy
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩
      have h1 : x * a = x * (y * c) := by linear_combination hc
      exact ⟨c, mul_left_cancel₀ hx h1⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c, by ring⟩
  let eKer : (Λ ⧸ Iy) ≃+ proj.ker :=
    (QuotientAddGroup.quotientAddEquivOfEq hmulX_ker.symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective mulX hmulX_surj)
  let eQuot : ((Λ ⧸ Ixy) ⧸ proj.ker) ≃+ (Λ ⧸ Ix) :=
    QuotientAddGroup.quotientKerEquivOfSurjective proj hsurj
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup proj.ker
  rw [h1, Nat.card_congr eQuot.toEquiv, ← Nat.card_congr eKer.toEquiv]

private lemma natCard_quot_ringEquiv (e : Λ ≃+* Λ) (x : Λ) :
    Nat.card (Λ ⧸ Ideal.span {e x}) = Nat.card (Λ ⧸ Ideal.span {x}) := by
  let f : (Λ ⧸ Ideal.span {x}) ≃+* (Λ ⧸ Ideal.span {e x}) :=
    Ideal.quotientEquiv (Ideal.span {x}) (Ideal.span {e x}) e (by
      rw [Ideal.map_span, Set.image_singleton]; rfl)
  exact (Nat.card_congr f.toEquiv).symm

/-- **Part 2 Main Theorem**: No exact sequence `0 → SwanIdeal → (X → ℤ) → (Y → ℤ) → 0`
of `Γ47`-modules exists (given Part 1's `norm_eq_int` and `no_elem_norm_47`). -/
theorem no_swan_exact_seq_of_part1
    (τU' : (ZMod 23)ˣ → (Λ ≃+* Λ))
    (hnorm_int : ∀ α : Λ, ∃ m : ℤ, (∏ u : (ZMod 23)ˣ, τU' u α) = (m : Λ))
    (hno47 : ∀ α : Λ, (∏ u : (ZMod 23)ˣ, τU' u α) ≠ 47 ∧ (∏ u : (ZMod 23)ˣ, τU' u α) ≠ -47)
    (X Y : Type) [Fintype X] [Fintype Y] [MulAction Γ47 X] [MulAction Γ47 Y]
    (ι : SwanIdeal →+ (X → ℤ)) (π : (X → ℤ) →+ (Y → ℤ))
    (hι : Function.Injective ι)
    (hπ : Function.Surjective π)
    (hexact : ∀ v, π v = 0 ↔ ∃ u, ι u = v)
    (hι_eq : ∀ g u, ι (swanAct g u) = permAct g (ι u))
    (hπ_eq : ∀ g v, π (permAct g v) = permAct g (π v)) :
    False := by
  classical
  obtain ⟨eProd, heProd⟩ := exists_prod_equiv ι π hι hπ hexact hι_eq hπ_eq
  -- Induce `HomΓ X ≃ₗ[Λ] HomΓ Y × HomΓI`
  let eHom : HomΓ X ≃ₗ[Λ] HomΓ Y × HomΓI :=
    { toFun := fun φ =>
        (⟨fun w => φ.1 (eProd.symm (w, 0)),
          ⟨fun w₁ w₂ => by
             dsimp only
             have h : (w₁ + w₂, (0 : SwanIdeal)) = (w₁, 0) + (w₂, 0) := by ext <;> simp
             rw [h, map_add, φ.2.1],
           fun g w => by
             dsimp only
             have h1 : eProd.symm (permAct g w, 0) = permAct g (eProd.symm (w, 0)) := by
               apply eProd.injective
               rw [eProd.apply_symm_apply, heProd, eProd.apply_symm_apply]
               ext <;> simp [swanAct]
             rw [h1, φ.2.2]⟩⟩,
         ⟨fun u => φ.1 (eProd.symm (0, u)),
          ⟨fun u₁ u₂ => by
             dsimp only
             have h : ((0 : Y → ℤ), u₁ + u₂) = (0, u₁) + (0, u₂) := by ext <;> simp
             rw [h, map_add, φ.2.1],
           fun g u => by
             dsimp only
             have h1 : eProd.symm (0, swanAct g u) = permAct g (eProd.symm (0, u)) := by
               apply eProd.injective
               rw [eProd.apply_symm_apply, heProd, eProd.apply_symm_apply]
               ext <;> simp [permAct]
             rw [h1, φ.2.2]⟩⟩)
      invFun := fun p =>
        ⟨fun v => p.1.1 (eProd v).1 + p.2.1 (eProd v).2,
         ⟨fun v₁ v₂ => by
            dsimp only
            rw [map_add, Prod.fst_add, Prod.snd_add, p.1.2.1, p.2.2.1]; ring,
          fun g v => by
            dsimp only
            rw [heProd, p.1.2.2, p.2.2.2]; ring⟩⟩
      left_inv := fun φ => by
        ext v
        change φ.1 (eProd.symm ((eProd v).1, 0)) + φ.1 (eProd.symm (0, (eProd v).2)) = φ.1 v
        rw [← φ.2.1, ← map_add]
        have h1 : ((eProd v).1, (0 : SwanIdeal)) + (0, (eProd v).2) = eProd v := by
          ext <;> simp
        rw [h1, eProd.symm_apply_apply]
      right_inv := fun p => by
        obtain ⟨f₁, hf₁⟩ := homΓ_toAddHom p.1
        obtain ⟨f₂, hf₂⟩ := homΓI_toAddHom p.2
        refine Prod.ext (by ext w; simp [← hf₂]) (by ext u; simp [← hf₁])
      map_add' := fun φ₁ φ₂ => by refine Prod.ext (by ext w; rfl) (by ext u; rfl)
      map_smul' := fun c φ => by refine Prod.ext (by ext w; rfl) (by ext u; rfl) }
  obtain ⟨m, ⟨eX⟩⟩ := homΓ_equiv_free_orbits X
  obtain ⟨n, ⟨eY⟩⟩ := homΓ_equiv_free_orbits Y
  let eMain : (Fin m → Λ) ≃ₗ[Λ] (Fin n → Λ) × qIdeal :=
    eX.symm.trans (eHom.trans (LinearEquiv.prodCongr eY homΓI_equiv_qIdeal))
  have hm : m = n + 1 := rank_eq_succ eMain
  subst hm
  obtain ⟨β, hqβ⟩ := qIdeal_principal_of_equiv eMain
  have h47mem : (47 : Λ) ∈ Ideal.span {β} := hqβ ▸ fortySeven_mem_qIdeal
  obtain ⟨α, hαβ⟩ := Ideal.mem_span_singleton.mp h47mem
  have hβne : β ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hαβ; exact fortySeven_ne_zero_Λ hαβ
  have hαne : α ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hαβ; exact fortySeven_ne_zero_Λ hαβ
  -- Compute `Nat.card (Λ ⧸ Ideal.span {∏ u, τU' u β})`
  have hprod_card : ∀ (s : Finset (ZMod 23)ˣ),
      Nat.card (Λ ⧸ Ideal.span {∏ u ∈ s, τU' u β}) = (47 ^ 21) ^ s.card := by
    intro s
    induction s using Finset.cons_induction with
    | empty =>
      simp only [Finset.prod_empty, Finset.card_empty, pow_zero]
      have htop : Ideal.span {(1 : Λ)} = ⊤ := Ideal.span_singleton_one
      rw [htop]
      have : Subsingleton (Λ ⧸ (⊤ : Ideal Λ)) := Submodule.Quotient.subsingleton_iff.mpr rfl
      exact Nat.card_unique
    | cons u s hu ih =>
      rw [Finset.prod_cons, Finset.card_cons, pow_succ', natCard_quot_mul]
      · rw [natCard_quot_ringEquiv, ← hqβ, natCard_quot_qIdeal, ih]
      · intro h0
        have := (τU' u).injective (h0.trans (map_zero (τU' u)).symm)
        exact hβne this
  obtain ⟨kβ, hkβ⟩ := hnorm_int β
  obtain ⟨kα, hkα⟩ := hnorm_int α
  have hcard_β : Nat.card (Λ ⧸ Ideal.span {(kβ : Λ)}) = (47 ^ 21) ^ 22 := by
    rw [← hkβ, hprod_card]
    have hcard23 : (Finset.univ : Finset (ZMod 23)ˣ).card = 22 := by decide
    rw [hcard23]
  have hkβ_ne : kβ ≠ 0 := by
    intro h0
    have hprod0 : (∏ u : (ZMod 23)ˣ, τU' u β) = 0 := by rw [hkβ, h0, Int.cast_zero]
    obtain ⟨u, _, hu0⟩ := Finset.prod_eq_zero_iff.mp hprod0
    exact hβne ((τU' u).injective (hu0.trans (map_zero (τU' u)).symm))
  rw [natCard_quot_intCast kβ hkβ_ne] at hcard_β
  have hkβ_abs : kβ.natAbs = 47 ^ 21 := by
    have hpow := hcard_β
    exact Nat.pow_left_injective (by norm_num : 22 ≠ 0) hpow
  -- Norm of `47 = β * α` gives `kβ * kα = 47 ^ 22`
  have hnorm47 : (∏ u : (ZMod 23)ˣ, τU' u (47 : Λ)) = ((47 ^ 22 : ℤ) : Λ) := by
    have h1 : ∀ u : (ZMod 23)ˣ, τU' u (47 : Λ) = 47 := fun u => map_ofNat (τU' u) 47
    simp only [h1, Finset.prod_const]
    have hcard23 : (Finset.univ : Finset (ZMod 23)ˣ).card = 22 := by decide
    rw [hcard23]; norm_cast
  have hprod_mul : (∏ u : (ZMod 23)ˣ, τU' u β) * (∏ u : (ZMod 23)ˣ, τU' u α) =
      ((47 ^ 22 : ℤ) : Λ) := by
    rw [← Finset.prod_mul_distrib]
    have h2 : ∀ u : (ZMod 23)ˣ, τU' u β * τU' u α = τU' u (47 : Λ) := fun u => by
      rw [← map_mul, ← hαβ]
    simp only [h2, hnorm47]
  rw [hkβ, hkα, ← Int.cast_mul] at hprod_mul
  have hk_mul : kβ * kα = 47 ^ 22 := intCast_injective_Λ hprod_mul
  have hkα_abs : kα.natAbs = 47 := by
    have h1 : kβ.natAbs * kα.natAbs = 47 ^ 22 := by
      have := congrArg Int.natAbs hk_mul
      rw [Int.natAbs_mul] at this
      simpa using this
    rw [hkβ_abs] at h1
    have h2 : 47 ^ 21 * kα.natAbs = 47 ^ 21 * 47 := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h2
  have hkα_cases : kα = 47 ∨ kα = -47 := Int.natAbs_eq_iff.mp hkα_abs
  rcases hkα_cases with rfl | rfl
  · exact (hno47 α).1 (by simpa using hkα)
  · exact (hno47 α).2 (by simpa using hkα)

/-- **Parts 1 + 2 Combined Theorem**: No exact sequence `0 → SwanIdeal → (X → ℤ) → (Y → ℤ) → 0`
of `Γ47`-modules exists. -/
theorem no_swan_exact_seq
    (X Y : Type) [Fintype X] [Fintype Y] [MulAction Γ47 X] [MulAction Γ47 Y]
    (ι : SwanIdeal →+ (X → ℤ)) (π : (X → ℤ) →+ (Y → ℤ))
    (hι : Function.Injective ι)
    (hπ : Function.Surjective π)
    (hexact : ∀ v, π v = 0 ↔ ∃ u, ι u = v)
    (hι_eq : ∀ g u, ι (swanAct g u) = permAct g (ι u))
    (hπ_eq : ∀ g v, π (permAct g v) = permAct g (π v)) :
    False :=
  no_swan_exact_seq_of_part1 τUEquiv norm_eq_int no_elem_norm_47
    X Y ι π hι hπ hexact hι_eq hπ_eq
end Part12

section Part3

open scoped BigOperators

instance instIsRationalExtensionRat(ι : Type*) :
    NoetherProblem.IsRationalExtension ℚ (FractionRing (MvPolynomial ι ℚ)) ι :=
  ⟨⟨@AlgEquiv.mk ℚ (FractionRing (MvPolynomial ι ℚ)) (FractionRing (MvPolynomial ι ℚ)) _ _ _
      DivisionRing.toRatAlgebra OreLocalization.instAlgebra
      (Equiv.refl _) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun r => RingHom.congr_fun (Subsingleton.elim _ _) r)⟩⟩

/- Helper for FractionRing elements -/

private lemma frac_mk_eq_div {R : Type*} [CommRing R] [IsDomain R]
    (p : R) (q : nonZeroDivisors R) :
    Localization.mk p q =
      algebraMap R (FractionRing R) p / algebraMap R (FractionRing R) q := by
  have hq : algebraMap R (FractionRing R) (q : R) ≠ 0 := by
    intro h0
    exact nonZeroDivisors.ne_zero q.2
      (IsFractionRing.injective R (FractionRing R) (by rw [h0, map_zero]))
  rw [eq_div_iff hq, mul_comm, Localization.mk_eq_mk']
  exact IsLocalization.mk'_spec' (FractionRing R) p q

private lemma fracAlgEquiv_algebraMap {R A : Type*} [CommRing R] [CommRing A] [IsDomain A]
    [Algebra R A] (e : A ≃ₐ[R] A) (p : A) :
    IsFractionRing.algEquivOfAlgEquiv e (algebraMap A (FractionRing A) p) =
      algebraMap A (FractionRing A) (e p) := by
  have hM : Submonoid.map e.toRingEquiv.toMonoidHom (nonZeroDivisors A) = nonZeroDivisors A := by
    ext x
    simp only [Submonoid.mem_map, mem_nonZeroDivisors_iff_ne_zero]
    constructor
    · rintro ⟨y, hy, rfl⟩ h0
      change e y = 0 at h0
      exact hy (e.injective (by rw [h0, map_zero]))
    · intro hx
      exact ⟨e.symm x, fun h0 => hx (by rw [← e.apply_symm_apply x, h0, map_zero]), e.apply_symm_apply x⟩
  exact IsLocalization.ringEquivOfRingEquiv_eq hM p

/- Section 1: Explicit ℤ-basis of SwanIdeal -/

private lemma swan_sum_split (f : Γ47 → ℤ) :
    ∑ a : Γ47, (f a : ZMod 47) * (a : ZMod 47) =
      (f 1 : ZMod 47) + ∑ a ∈ Finset.univ.erase (1 : Γ47), (f a : ZMod 47) * (a : ZMod 47) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Γ47))]
  simp

private def swanEquiv : (Γ47 → ℤ) ≃+ SwanIdeal where
  toFun c :=
    ⟨fun a => if a = 1 then
        47 * c 1 - ∑ b ∈ Finset.univ.erase (1 : Γ47), c b * ((b : ZMod 47).val : ℤ)
      else c a, by
      change ∑ a : Γ47, _ = 0
      rw [swan_sum_split]
      simp only [↓reduceIte, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_sum,
        Int.cast_natCast, ZMod.natCast_zmod_val]
      have h47 : (47 : ZMod 47) = 0 := by decide
      rw [h47, zero_mul, zero_sub]
      have hsum : ∑ a ∈ Finset.univ.erase (1 : Γ47),
          ((if a = 1 then 47 * c 1 - ∑ b ∈ Finset.univ.erase (1 : Γ47), c b * ((b : ZMod 47).val : ℤ)
            else c a : ℤ) : ZMod 47) * (a : ZMod 47) =
          ∑ a ∈ Finset.univ.erase (1 : Γ47), (c a : ZMod 47) * (a : ZMod 47) := by
        refine Finset.sum_congr rfl fun a ha => ?_
        have hne : a ≠ 1 := (Finset.mem_erase.mp ha).1
        simp [hne]
      rw [hsum, neg_add_cancel]⟩
  invFun u a :=
    if a = 1 then
      (u.1 1 + ∑ b ∈ Finset.univ.erase (1 : Γ47), u.1 b * ((b : ZMod 47).val : ℤ)) / 47
    else u.1 a
  left_inv c := by
    ext a
    by_cases ha : a = 1
    · subst ha
      simp only [↓reduceIte]
      have hsum : ∑ b ∈ Finset.univ.erase (1 : Γ47),
          (if b = 1 then 47 * c 1 - ∑ b' ∈ Finset.univ.erase (1 : Γ47), c b' * ((b' : ZMod 47).val : ℤ)
            else c b) * ((b : ZMod 47).val : ℤ) =
          ∑ b ∈ Finset.univ.erase (1 : Γ47), c b * ((b : ZMod 47).val : ℤ) := by
        refine Finset.sum_congr rfl fun b hb => ?_
        simp [(Finset.mem_erase.mp hb).1]
      rw [hsum, sub_add_cancel]
      omega
    · simp [ha]
  right_inv u := by
    ext a
    by_cases ha : a = 1
    · subst ha
      simp only [↓reduceIte]
      have hsum : ∑ b ∈ Finset.univ.erase (1 : Γ47),
          (if b = 1 then
            (u.1 1 + ∑ b' ∈ Finset.univ.erase (1 : Γ47), u.1 b' * ((b' : ZMod 47).val : ℤ)) / 47
          else u.1 b) * ((b : ZMod 47).val : ℤ) =
          ∑ b ∈ Finset.univ.erase (1 : Γ47), u.1 b * ((b : ZMod 47).val : ℤ) := by
        refine Finset.sum_congr rfl fun b hb => ?_
        simp [(Finset.mem_erase.mp hb).1]
      rw [hsum]
      set S : ℤ := ∑ b ∈ Finset.univ.erase (1 : Γ47), u.1 b * ((b : ZMod 47).val : ℤ)
      have hz : ((u.1 1 + S : ℤ) : ZMod 47) = 0 := by
        have hu := u.2
        change ∑ b : Γ47, (u.1 b : ZMod 47) * (b : ZMod 47) = 0 at hu
        rw [swan_sum_split] at hu
        simpa [S, ZMod.natCast_zmod_val] using hu
      have hdvd : (47 : ℤ) ∣ u.1 1 + S := (ZMod.intCast_zmod_eq_zero_iff_dvd (u.1 1 + S) 47).mp hz
      have hmul : 47 * ((u.1 1 + S) / 47) = u.1 1 + S := Int.mul_ediv_cancel' hdvd
      linarith
    · simp [ha]
  map_add' c₁ c₂ := by
    ext a
    by_cases ha : a = 1
    · subst ha
      simp only [↓reduceIte, AddSubgroup.coe_add, Pi.add_apply, mul_add, add_mul,
        Finset.sum_add_distrib]
      ring
    · simp [ha]

private def swanBasis (b : Γ47) : SwanIdeal := swanEquiv (Pi.single b 1)

private lemma swanEquiv_eq_sum (c : Γ47 → ℤ) :
    swanEquiv c = ∑ b : Γ47, c b • swanBasis b := by
  have hc : c = ∑ b : Γ47, c b • Pi.single b (1 : ℤ) := by
    ext a
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hc]
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_zsmul]
  rfl

/- Section 2: Cyclotomic field F47 = ℚ(ζ_47) and its Γ47-action -/

local instance instPrime47 : Fact (Nat.Prime 47) := ⟨by decide⟩

local instance instIrredCyclotomic47 : Fact (Irreducible (Polynomial.cyclotomic 47 ℚ)) :=
  ⟨Polynomial.cyclotomic.irreducible_rat (by norm_num)⟩

private abbrev F47 : Type := AdjoinRoot (Polynomial.cyclotomic 47 ℚ)

private noncomputable def ζ47 : F47 := AdjoinRoot.root (Polynomial.cyclotomic 47 ℚ)

private lemma cyclotomic47_eq_geom :
    Polynomial.cyclotomic 47 ℚ = ∑ i ∈ Finset.range 47, Polynomial.X ^ i :=
  Polynomial.cyclotomic_prime ℚ 47

private lemma aeval_ζ47_cyclotomic :
    Polynomial.aeval ζ47 (Polynomial.cyclotomic 47 ℚ) = 0 :=
  AdjoinRoot.eval₂_root (Polynomial.cyclotomic 47 ℚ)

private lemma sum_ζ47_pow : ∑ i ∈ Finset.range 47, ζ47 ^ i = 0 := by
  have h := congr_arg (Polynomial.aeval ζ47) cyclotomic47_eq_geom
  rw [aeval_ζ47_cyclotomic, map_sum] at h
  simpa using h.symm

private lemma ζ47_pow_47 : ζ47 ^ 47 = 1 := by
  have h := geom_sum_mul ζ47 47
  rw [sum_ζ47_pow, zero_mul] at h
  exact sub_eq_zero.mp h.symm

private lemma ζ47_ne_one : ζ47 ≠ 1 := by
  intro h
  have hsum := sum_ζ47_pow
  rw [h] at hsum
  simp at hsum

private lemma ζ47_orderOf : orderOf ζ47 = 47 := by
  have hdvd : orderOf ζ47 ∣ 47 := orderOf_dvd_of_pow_eq_one ζ47_pow_47
  rcases (Nat.dvd_prime (by decide : Nat.Prime 47)).mp hdvd with h1 | h47
  · exfalso
    exact ζ47_ne_one (orderOf_eq_one_iff.mp h1)
  · exact h47

private noncomputable def zpow47 (a : ZMod 47) : F47 := ζ47 ^ a.val

private lemma zpow47_zero : zpow47 0 = 1 := by
  simp [zpow47]

private lemma zpow47_pow_nat (n : ℕ) : zpow47 (n : ZMod 47) = ζ47 ^ n := by
  simp only [zpow47, ZMod.val_natCast]
  have h : ζ47 ^ (n % orderOf ζ47) = ζ47 ^ n := pow_mod_orderOf ζ47 n
  rwa [ζ47_orderOf] at h

private lemma zpow47_add (a b : ZMod 47) : zpow47 (a + b) = zpow47 a * zpow47 b := by
  have h : (a + b) = ((a.val + b.val : ℕ) : ZMod 47) := by simp
  rw [h, zpow47_pow_nat, pow_add]
  rfl

private lemma zpow47_neg (a : ZMod 47) : zpow47 (-a) = (zpow47 a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← zpow47_add, neg_add_cancel, zpow47_zero]

private lemma zpow47_ne_zero (a : ZMod 47) : zpow47 a ≠ 0 := by
  intro h
  have h1 : (zpow47 a) ^ 47 = 1 := by
    dsimp [zpow47]
    rw [← pow_mul, mul_comm, pow_mul, ζ47_pow_47, one_pow]
  rw [h, zero_pow (by norm_num)] at h1
  exact zero_ne_one h1

private lemma zpow47_eq_one_iff (a : ZMod 47) : zpow47 a = 1 ↔ a = 0 := by
  constructor
  · intro h
    have hdvd : orderOf ζ47 ∣ a.val := orderOf_dvd_of_pow_eq_one h
    rw [ζ47_orderOf] at hdvd
    have hv : a.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd a.val_lt
    exact (ZMod.val_eq_zero a).mp hv
  · rintro rfl
    exact zpow47_zero

private lemma zpow47_zpow (a : ZMod 47) (n : ℤ) :
    (zpow47 a) ^ n = zpow47 ((n : ZMod 47) * a) := by
  induction n with
  | zero => simp [zpow47_zero]
  | succ k ih =>
    rw [zpow_add_one₀ (zpow47_ne_zero a), ih, ← zpow47_add]
    congr 1; push_cast; ring
  | pred k ih =>
    rw [zpow_sub_one₀ (zpow47_ne_zero a), ih, ← zpow47_neg, ← zpow47_add]
    congr 1; push_cast; ring

private lemma sum_zpow47_mul (a : ZMod 47) :
    ∑ i : ZMod 47, zpow47 (a * i) = if a = 0 then (47 : F47) else 0 := by
  by_cases ha : a = 0
  · subst ha
    simp [zpow47_zero]
  · simp only [ha, ↓reduceIte]
    have hmul : zpow47 a * ∑ i : ZMod 47, zpow47 (a * i) = ∑ i : ZMod 47, zpow47 (a * i) := by
      rw [Finset.mul_sum]
      calc ∑ i : ZMod 47, zpow47 a * zpow47 (a * i)
          = ∑ i : ZMod 47, zpow47 (a * (i + 1)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← zpow47_add]
            congr 1; ring
        _ = ∑ j : ZMod 47, zpow47 (a * j) :=
            Fintype.sum_equiv (Equiv.addRight (1 : ZMod 47)) _ _ (fun _ => rfl)
    have hsub : (zpow47 a - 1) * ∑ i : ZMod 47, zpow47 (a * i) = 0 := by
      rw [sub_mul, one_mul, hmul, sub_self]
    have hne : zpow47 a - 1 ≠ 0 := sub_ne_zero.mpr (mt (zpow47_eq_one_iff a).mp ha)
    exact (mul_eq_zero.mp hsub).resolve_left hne

private lemma aeval_zpow47_cyclotomic (g : Γ47) :
    Polynomial.eval₂ (Algebra.ofId ℚ F47) (zpow47 (g : ZMod 47)) (Polynomial.cyclotomic 47 ℚ) = 0 := by
  have h := congr_arg (Polynomial.aeval (zpow47 (g : ZMod 47))) cyclotomic47_eq_geom
  change Polynomial.aeval (zpow47 (g : ZMod 47)) (Polynomial.cyclotomic 47 ℚ) = 0
  rw [h, map_sum]
  simp only [map_pow, Polynomial.aeval_X]
  have hne : zpow47 (g : ZMod 47) - 1 ≠ 0 :=
    sub_ne_zero.mpr (mt (zpow47_eq_one_iff _).mp g.ne_zero)
  have hmul : (∑ i ∈ Finset.range 47, zpow47 (g : ZMod 47) ^ i) * (zpow47 (g : ZMod 47) - 1) = 0 := by
    rw [geom_sum_mul]
    have hpow : zpow47 (g : ZMod 47) ^ 47 = 1 := by
      dsimp [zpow47]
      rw [← pow_mul, mul_comm, pow_mul, ζ47_pow_47, one_pow]
    rw [hpow, sub_self]
  exact (mul_eq_zero.mp hmul).resolve_right hne

private noncomputable def σ47Hom (g : Γ47) : F47 →ₐ[ℚ] F47 :=
  AdjoinRoot.liftAlgHom (Polynomial.cyclotomic 47 ℚ) (Algebra.ofId ℚ F47)
    (zpow47 (g : ZMod 47)) (aeval_zpow47_cyclotomic g)

private lemma σ47Hom_ζ47 (g : Γ47) : σ47Hom g ζ47 = zpow47 (g : ZMod 47) :=
  AdjoinRoot.liftAlgHom_root (Polynomial.cyclotomic 47 ℚ) (Algebra.ofId ℚ F47)
    (zpow47 (g : ZMod 47)) (aeval_zpow47_cyclotomic g)

private lemma σ47Hom_zpow47 (g : Γ47) (a : ZMod 47) :
    σ47Hom g (zpow47 a) = zpow47 ((g : ZMod 47) * a) := by
  simp only [zpow47, map_pow, σ47Hom_ζ47]
  rw [← pow_mul, ← zpow47_pow_nat]
  congr 1

private lemma σ47Hom_one : σ47Hom 1 = AlgHom.id ℚ F47 := by
  apply AdjoinRoot.algHom_ext
  change σ47Hom 1 ζ47 = ζ47
  rw [σ47Hom_ζ47]
  simp only [Units.val_one, zpow47]
  have h1 : (1 : ZMod 47).val = 1 := by decide
  rw [h1, pow_one]

private lemma σ47Hom_mul (g₁ g₂ : Γ47) : σ47Hom (g₁ * g₂) = (σ47Hom g₁).comp (σ47Hom g₂) := by
  apply AdjoinRoot.algHom_ext
  change σ47Hom (g₁ * g₂) ζ47 = σ47Hom g₁ (σ47Hom g₂ ζ47)
  rw [σ47Hom_ζ47, σ47Hom_ζ47, σ47Hom_zpow47, Units.val_mul]

private noncomputable def σ47Equiv : Γ47 →* (F47 ≃ₐ[ℚ] F47) where
  toFun g :=
    AlgEquiv.ofAlgHom (σ47Hom g) (σ47Hom g⁻¹)
      (by rw [← σ47Hom_mul, mul_inv_cancel, σ47Hom_one])
      (by rw [← σ47Hom_mul, inv_mul_cancel, σ47Hom_one])
  map_one' := by
    ext x
    exact AlgHom.congr_fun σ47Hom_one x
  map_mul' g₁ g₂ := by
    ext x
    exact AlgHom.congr_fun (σ47Hom_mul g₁ g₂) x

private noncomputable def basisF47 :
    Module.Basis (Fin (Polynomial.cyclotomic 47 ℚ).natDegree) ℚ F47 :=
  AdjoinRoot.powerBasisAux (Polynomial.cyclotomic_ne_zero 47 ℚ)

/- Section 3: Base change via explicit basis expansion (zero TensorProduct!) -/

private noncomputable def fracMapToF47 (ι : Type) :
    FractionRing (MvPolynomial ι ℚ) →ₐ[ℚ] FractionRing (MvPolynomial ι F47) :=
  let hle : nonZeroDivisors (MvPolynomial ι ℚ) ≤
      Submonoid.comap (MvPolynomial.mapAlgHom (Algebra.ofId ℚ F47)).toRingHom
        (nonZeroDivisors (MvPolynomial ι F47)) := by
    intro x hx
    change MvPolynomial.map (algebraMap ℚ F47) x ∈ nonZeroDivisors (MvPolynomial ι F47)
    rw [mem_nonZeroDivisors_iff_ne_zero] at hx ⊢
    intro h0
    apply hx
    exact MvPolynomial.map_injective _ (algebraMap ℚ F47).injective (by simpa using h0)
  let f : FractionRing (MvPolynomial ι ℚ) →+* FractionRing (MvPolynomial ι F47) :=
    IsLocalization.map (FractionRing (MvPolynomial ι F47))
      (MvPolynomial.mapAlgHom (Algebra.ofId ℚ F47)).toRingHom hle
  { f with
    commutes' := fun r => by
      have h1 : algebraMap ℚ (FractionRing (MvPolynomial ι ℚ)) r =
          algebraMap (MvPolynomial ι ℚ) (FractionRing (MvPolynomial ι ℚ)) (MvPolynomial.C r) :=
        IsScalarTower.algebraMap_apply ℚ (MvPolynomial ι ℚ) (FractionRing (MvPolynomial ι ℚ)) r
      have h2 : algebraMap ℚ (FractionRing (MvPolynomial ι F47)) r =
          algebraMap (MvPolynomial ι F47) (FractionRing (MvPolynomial ι F47))
            (MvPolynomial.C (algebraMap ℚ F47 r)) := by
        rw [IsScalarTower.algebraMap_apply ℚ (MvPolynomial ι F47) (FractionRing (MvPolynomial ι F47)) r,
          IsScalarTower.algebraMap_apply ℚ F47 (MvPolynomial ι F47) r]
        rfl
      change f (algebraMap ℚ _ r) = algebraMap ℚ _ r
      rw [h1, h2]
      exact (IsLocalization.map_eq hle (MvPolynomial.C r)).trans (by simp) }

private lemma fracMapToF47_algebraMap (ι : Type) (p : MvPolynomial ι ℚ) :
    fracMapToF47 ι (algebraMap (MvPolynomial ι ℚ) (FractionRing (MvPolynomial ι ℚ)) p) =
      algebraMap (MvPolynomial ι F47) (FractionRing (MvPolynomial ι F47))
        (MvPolynomial.map (algebraMap ℚ F47) p) := by
  dsimp only [fracMapToF47, AlgHom.coe_mk, RingHom.coe_mk]
  exact IsLocalization.map_eq _ p

private noncomputable def actPoly (ι : Type) (g : Γ47) :
    MvPolynomial ι F47 ≃ₐ[ℚ] MvPolynomial ι F47 :=
  { MvPolynomial.mapEquiv ι (σ47Equiv g).toRingEquiv with
    commutes' := fun r => by
      change MvPolynomial.map (σ47Equiv g).toRingHom (MvPolynomial.C (algebraMap ℚ F47 r)) =
        MvPolynomial.C (algebraMap ℚ F47 r)
      simp }

private lemma actPoly_frac_algebraMap (ι : Type) (g : Γ47) (p : MvPolynomial ι F47) :
    IsFractionRing.algEquivOfAlgEquiv (actPoly ι g)
      (algebraMap (MvPolynomial ι F47) (FractionRing (MvPolynomial ι F47)) p) =
      algebraMap (MvPolynomial ι F47) (FractionRing (MvPolynomial ι F47))
        (MvPolynomial.map (σ47Equiv g).toRingHom p) :=
  fracAlgEquiv_algebraMap (actPoly ι g) p

private noncomputable def actFrac (ι : Type) :
    Γ47 →* (FractionRing (MvPolynomial ι F47) ≃ₐ[ℚ] FractionRing (MvPolynomial ι F47)) where
  toFun g := IsFractionRing.algEquivOfAlgEquiv (actPoly ι g)
  map_one' := by
    ext x
    induction x using Localization.induction_on with
    | H a =>
      rcases a with ⟨p, q⟩
      rw [frac_mk_eq_div, map_div₀, actPoly_frac_algebraMap, actPoly_frac_algebraMap]
      have h1 : ∀ r : MvPolynomial ι F47, MvPolynomial.map (σ47Equiv 1).toRingHom r = r := by
        intro r
        have hid : (σ47Equiv 1).toRingHom = RingHom.id F47 := RingHom.ext fun c => by simp
        rw [hid, MvPolynomial.map_id]
      rw [h1 p, h1 q]; rfl
  map_mul' g₁ g₂ := by
    ext x
    induction x using Localization.induction_on with
    | H a =>
      rcases a with ⟨p, q⟩
      rw [frac_mk_eq_div, AlgEquiv.mul_apply, map_div₀, map_div₀, map_div₀,
        actPoly_frac_algebraMap, actPoly_frac_algebraMap,
        actPoly_frac_algebraMap, actPoly_frac_algebraMap,
        actPoly_frac_algebraMap, actPoly_frac_algebraMap]
      have hcomp : (σ47Equiv (g₁ * g₂)).toRingHom =
          (σ47Equiv g₁).toRingHom.comp (σ47Equiv g₂).toRingHom :=
        RingHom.ext fun c => by simp
      congr 1 <;>
      · congr 1
        rw [MvPolynomial.map_map, hcomp]

private lemma actFrac_algebraMap_poly (ι : Type) (g : Γ47) (p : MvPolynomial ι F47) :
    actFrac ι g (algebraMap (MvPolynomial ι F47) (FractionRing (MvPolynomial ι F47)) p) =
      algebraMap (MvPolynomial ι F47) (FractionRing (MvPolynomial ι F47))
        (MvPolynomial.map (σ47Equiv g).toRingHom p) :=
  actPoly_frac_algebraMap ι g p

private lemma actFrac_algebraMap_F47 (ι : Type) (g : Γ47) (c : F47) :
    actFrac ι g (algebraMap F47 (FractionRing (MvPolynomial ι F47)) c) =
      algebraMap F47 (FractionRing (MvPolynomial ι F47)) (σ47Equiv g c) := by
  have h := actFrac_algebraMap_poly ι g (MvPolynomial.C c)
  rw [MvPolynomial.map_C] at h
  exact h

private lemma actFrac_fracMapToF47 (ι : Type) (g : Γ47) (a : FractionRing (MvPolynomial ι ℚ)) :
    actFrac ι g (fracMapToF47 ι a) = fracMapToF47 ι a := by
  induction a using Localization.induction_on with
  | H x =>
    rcases x with ⟨p, q⟩
    rw [frac_mk_eq_div, map_div₀, map_div₀, fracMapToF47_algebraMap, fracMapToF47_algebraMap,
      actFrac_algebraMap_poly, actFrac_algebraMap_poly]
    have hcomp : (σ47Equiv g).toRingHom.comp (algebraMap ℚ F47) = algebraMap ℚ F47 := by
      ext r; simp
    congr 1 <;>
    · congr 1
      rw [MvPolynomial.map_map, hcomp]

private noncomputable abbrev deg47 : ℕ := (Polynomial.cyclotomic 47 ℚ).natDegree

private noncomputable def expandF47 (ι : Type) (v : Fin deg47 → FractionRing (MvPolynomial ι ℚ)) :
    FractionRing (MvPolynomial ι F47) :=
  ∑ k : Fin deg47, algebraMap F47 (FractionRing (MvPolynomial ι F47)) (basisF47 k) *
    fracMapToF47 ι (v k)

private lemma expandF47_add (ι : Type) (v w : Fin deg47 → FractionRing (MvPolynomial ι ℚ)) :
    expandF47 ι (v + w) = expandF47 ι v + expandF47 ι w := by
  simp only [expandF47, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

private lemma expandF47_injective (ι : Type) : Function.Injective (expandF47 ι) := by
  classical
  intro v w hvw
  have hzero : expandF47 ι (v - w) = 0 := by
    have h1 : expandF47 ι (v - w) + expandF47 ι w = expandF47 ι v := by
      rw [← expandF47_add, sub_add_cancel]
    rw [hvw] at h1
    exact add_right_cancel (b := expandF47 ι w) (by simpa using h1)
  set m := v - w
  obtain ⟨q, hq⟩ := IsLocalization.exist_integer_multiples (S := FractionRing (MvPolynomial ι ℚ))
    (nonZeroDivisors (MvPolynomial ι ℚ)) (Finset.univ.image m) id
  have hp : ∀ k, ∃ p : MvPolynomial ι ℚ,
      algebraMap (MvPolynomial ι ℚ) (FractionRing (MvPolynomial ι ℚ)) p =
        (q : MvPolynomial ι ℚ) • m k := fun k => hq (m k) (Finset.mem_image_of_mem m (Finset.mem_univ k))
  choose p hp using hp
  have hpoly : ∑ k : Fin deg47, MvPolynomial.C (basisF47 k) * MvPolynomial.map (algebraMap ℚ F47) (p k) = 0 := by
    apply IsFractionRing.injective (MvPolynomial ι F47) (FractionRing (MvPolynomial ι F47))
    rw [map_zero, map_sum]
    have hq_mul : (algebraMap (MvPolynomial ι F47) (FractionRing (MvPolynomial ι F47))
        (MvPolynomial.map (algebraMap ℚ F47) (q : MvPolynomial ι ℚ))) *
        expandF47 ι m = 0 := by
      rw [hzero, mul_zero]
    rw [expandF47, Finset.mul_sum] at hq_mul
    rw [← hq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, ← fracMapToF47_algebraMap, hp k, Algebra.smul_def, map_mul,
      fracMapToF47_algebraMap]
    change algebraMap F47 _ (basisF47 k) * _ = _
    ring
  have hp0 : ∀ k, p k = 0 := by
    intro k
    ext μ
    have hμ := congr_arg (MvPolynomial.coeff μ) hpoly
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_map] at hμ
    have hlin : ∑ k' : Fin deg47, (MvPolynomial.coeff μ (p k')) • (basisF47 k') = 0 := by
      simpa [Algebra.smul_def, mul_comm] using hμ
    exact Fintype.linearIndependent_iff.mp basisF47.linearIndependent _ hlin k
  have hm0 : ∀ k, m k = 0 := by
    intro k
    have h1 := hp k
    rw [hp0 k, map_zero, Algebra.smul_def] at h1
    have hq0 : algebraMap (MvPolynomial ι ℚ) (FractionRing (MvPolynomial ι ℚ)) (q : MvPolynomial ι ℚ) ≠ 0 := by
      intro h0
      exact nonZeroDivisors.ne_zero q.2
        (IsFractionRing.injective (MvPolynomial ι ℚ) _ (by rw [h0, map_zero]))
    exact (mul_eq_zero.mp h1.symm).resolve_left hq0
  ext k
  exact sub_eq_zero.mp (hm0 k)

private lemma expandF47_mul (ι : Type) (v w : Fin deg47 → FractionRing (MvPolynomial ι ℚ)) :
    expandF47 ι v * expandF47 ι w =
      expandF47 ι (fun k => ∑ i : Fin deg47, ∑ j : Fin deg47,
        algebraMap ℚ (FractionRing (MvPolynomial ι ℚ)) (basisF47.repr (basisF47 i * basisF47 j) k) * (v i * w j)) := by
  simp only [expandF47]
  rw [Finset.sum_mul]
  calc ∑ i : Fin deg47, algebraMap F47 _ (basisF47 i) * fracMapToF47 ι (v i) *
        ∑ j : Fin deg47, algebraMap F47 _ (basisF47 j) * fracMapToF47 ι (w j)
      = ∑ i : Fin deg47, ∑ j : Fin deg47,
          algebraMap F47 _ (basisF47 i * basisF47 j) * fracMapToF47 ι (v i * w j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, map_mul]; ring
    _ = ∑ i : Fin deg47, ∑ j : Fin deg47,
          ∑ k : Fin deg47, algebraMap F47 _ (basisF47 k) *
            fracMapToF47 ι (algebraMap ℚ _ (basisF47.repr (basisF47 i * basisF47 j) k) * (v i * w j)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        conv_lhs => rw [← basisF47.sum_repr (basisF47 i * basisF47 j)]
        rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Algebra.smul_def, map_mul (algebraMap F47 _)]
        conv_rhs => rw [map_mul, (fracMapToF47 ι).commutes]
        have hq : algebraMap ℚ (FractionRing (MvPolynomial ι F47))
            (basisF47.repr (basisF47 i * basisF47 j) k) =
            algebraMap F47 (FractionRing (MvPolynomial ι F47))
              (algebraMap ℚ F47 (basisF47.repr (basisF47 i * basisF47 j) k)) :=
          IsScalarTower.algebraMap_apply ℚ F47 (FractionRing (MvPolynomial ι F47)) _
        rw [hq]; ring
    _ = ∑ k : Fin deg47, algebraMap F47 _ (basisF47 k) *
          fracMapToF47 ι (∑ i : Fin deg47, ∑ j : Fin deg47,
            algebraMap ℚ _ (basisF47.repr (basisF47 i * basisF47 j) k) * (v i * w j)) := by
        have hswap : ∀ f : Fin deg47 → Fin deg47 → Fin deg47 → FractionRing (MvPolynomial ι F47),
            ∑ i : Fin deg47, ∑ j : Fin deg47, ∑ k : Fin deg47, f i j k =
              ∑ k : Fin deg47, ∑ i : Fin deg47, ∑ j : Fin deg47, f i j k := fun f => by
          calc ∑ i, ∑ j, ∑ k, f i j k
              = ∑ i, ∑ k, ∑ j, f i j k := Finset.sum_congr rfl fun i _ => Finset.sum_comm
            _ = ∑ k, ∑ i, ∑ j, f i j k := Finset.sum_comm
        rw [hswap]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_sum, Finset.mul_sum]

private lemma expandF47_algebraMap (ι : Type) (c : F47) :
    algebraMap F47 (FractionRing (MvPolynomial ι F47)) c =
      expandF47 ι (fun k => algebraMap ℚ (FractionRing (MvPolynomial ι ℚ)) (basisF47.repr c k)) := by
  simp only [expandF47]
  conv_lhs => rw [← basisF47.sum_repr c]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def, map_mul, (fracMapToF47 ι).commutes]
  have hq : algebraMap ℚ (FractionRing (MvPolynomial ι F47)) (basisF47.repr c k) =
      algebraMap F47 (FractionRing (MvPolynomial ι F47)) (algebraMap ℚ F47 (basisF47.repr c k)) :=
    IsScalarTower.algebraMap_apply ℚ F47 (FractionRing (MvPolynomial ι F47)) _
  rw [hq, mul_comm]

private lemma expandF47_surjective (ι : Type) : Function.Surjective (expandF47 ι) := by
  set M0 := FractionRing (MvPolynomial ι ℚ)
  set MF := FractionRing (MvPolynomial ι F47)
  have hmul : ∀ v w : Fin deg47 → M0, ∃ u, expandF47 ι u = expandF47 ι v * expandF47 ι w :=
    fun v w => ⟨_, (expandF47_mul ι v w).symm⟩
  have hinv : ∀ v : Fin deg47 → M0, expandF47 ι v ≠ 0 → ∃ w, expandF47 ι v * expandF47 ι w = 1 := by
    intro v hv
    let prodVec (w : Fin deg47 → M0) : Fin deg47 → M0 := fun k =>
      ∑ i : Fin deg47, ∑ j : Fin deg47,
        algebraMap ℚ M0 (basisF47.repr (basisF47 i * basisF47 j) k) * (v i * w j)
    let Lmul : (Fin deg47 → M0) →ₗ[M0] (Fin deg47 → M0) :=
      { toFun := prodVec
        map_add' := fun w₁ w₂ => by
          ext k
          dsimp only [prodVec, Pi.add_apply]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
        map_smul' := fun a w => by
          ext k
          dsimp only [prodVec, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring }
    have hLmul_inj : Function.Injective Lmul := by
      intro w₁ w₂ hw
      have h1 : expandF47 ι v * expandF47 ι w₁ = expandF47 ι v * expandF47 ι w₂ := by
        rw [expandF47_mul, expandF47_mul]
        exact congr_arg (expandF47 ι) hw
      exact expandF47_injective ι (mul_left_cancel₀ hv h1)
    have h1_mem : ∃ u1 : Fin deg47 → M0, expandF47 ι u1 = 1 :=
      ⟨fun k => algebraMap ℚ M0 (basisF47.repr 1 k), by rw [← expandF47_algebraMap, map_one]⟩
    rcases h1_mem with ⟨u1, hu1⟩
    obtain ⟨w, hw⟩ := LinearMap.surjective_of_injective hLmul_inj u1
    exact ⟨w, by rw [expandF47_mul]; exact (congr_arg (expandF47 ι) hw).trans hu1⟩
  have hpoly : ∀ p : MvPolynomial ι F47,
      ∃ v, expandF47 ι v = algebraMap (MvPolynomial ι F47) MF p := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
      exact ⟨fun k => algebraMap ℚ M0 (basisF47.repr c k), (expandF47_algebraMap ι c).symm⟩
    | add p₁ p₂ h₁ h₂ =>
      rcases h₁ with ⟨v₁, hv₁⟩
      rcases h₂ with ⟨v₂, hv₂⟩
      exact ⟨v₁ + v₂, by rw [expandF47_add, hv₁, hv₂, map_add]⟩
    | mul_X p i hp =>
      rcases hp with ⟨v, hv⟩
      have hX : ∃ u, expandF47 ι u = algebraMap (MvPolynomial ι F47) MF (MvPolynomial.X i) := by
        refine ⟨fun k => algebraMap ℚ M0 (basisF47.repr 1 k) *
            algebraMap (MvPolynomial ι ℚ) M0 (MvPolynomial.X i), ?_⟩
        have h1 := expandF47_algebraMap ι (1 : F47)
        rw [map_one] at h1
        have hfx : fracMapToF47 ι (algebraMap (MvPolynomial ι ℚ) M0 (MvPolynomial.X i)) =
            algebraMap (MvPolynomial ι F47) MF (MvPolynomial.X i) := by
          rw [fracMapToF47_algebraMap, MvPolynomial.map_X]
        simp only [expandF47, map_mul, hfx] at h1 ⊢
        calc ∑ k : Fin deg47, algebraMap F47 MF (basisF47 k) *
              (fracMapToF47 ι (algebraMap ℚ M0 (basisF47.repr 1 k)) *
                algebraMap (MvPolynomial ι F47) MF (MvPolynomial.X i))
            = (∑ k : Fin deg47, algebraMap F47 MF (basisF47 k) *
                fracMapToF47 ι (algebraMap ℚ M0 (basisF47.repr 1 k))) *
                algebraMap (MvPolynomial ι F47) MF (MvPolynomial.X i) := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun k _ => by ring
          _ = 1 * algebraMap (MvPolynomial ι F47) MF (MvPolynomial.X i) := by rw [← h1]
          _ = algebraMap (MvPolynomial ι F47) MF (MvPolynomial.X i) := one_mul _
      rcases hX with ⟨u, hu⟩
      rcases hmul v u with ⟨w, hw⟩
      exact ⟨w, by rw [hw, hv, hu, map_mul]⟩
  intro z
  induction z using Localization.induction_on with
  | H a =>
    rcases a with ⟨p, q⟩
    rw [frac_mk_eq_div]
    rcases hpoly p with ⟨vp, hvp⟩
    rcases hpoly q with ⟨vq, hvq⟩
    have hvq0 : expandF47 ι vq ≠ 0 := by
      rw [hvq]
      intro h0
      exact nonZeroDivisors.ne_zero q.2 (IsFractionRing.injective _ _ (by rw [h0, map_zero]))
    rcases hinv vq hvq0 with ⟨wq, hwq⟩
    rcases hmul vp wq with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    have hwq' : expandF47 ι wq = (algebraMap (MvPolynomial ι F47) MF q)⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      rw [← hvq, hwq]
    rw [hu, hvp, hwq', div_eq_mul_inv]

private noncomputable def expandEquiv (ι : Type) :
    (Fin deg47 → FractionRing (MvPolynomial ι ℚ)) ≃ FractionRing (MvPolynomial ι F47) :=
  Equiv.ofBijective (expandF47 ι) ⟨expandF47_injective ι, expandF47_surjective ι⟩

private lemma actFrac_expandF47 (ι : Type) (g : Γ47)
    (v : Fin deg47 → FractionRing (MvPolynomial ι ℚ)) :
    actFrac ι g (expandF47 ι v) =
      expandF47 ι (fun k => ∑ i : Fin deg47,
        algebraMap ℚ (FractionRing (MvPolynomial ι ℚ)) (basisF47.repr (σ47Equiv g (basisF47 i)) k) * v i) := by
  have hlhs : actFrac ι g (expandF47 ι v) =
      ∑ i : Fin deg47, algebraMap F47 _ (σ47Equiv g (basisF47 i)) * fracMapToF47 ι (v i) := by
    simp only [expandF47, map_sum, map_mul, actFrac_algebraMap_F47, actFrac_fracMapToF47]
  rw [hlhs]
  calc ∑ i : Fin deg47, algebraMap F47 _ (σ47Equiv g (basisF47 i)) * fracMapToF47 ι (v i)
      = ∑ i : Fin deg47, ∑ k : Fin deg47, algebraMap F47 _ (basisF47 k) *
          fracMapToF47 ι (algebraMap ℚ _ (basisF47.repr (σ47Equiv g (basisF47 i)) k) * v i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        conv_lhs => rw [← basisF47.sum_repr (σ47Equiv g (basisF47 i))]
        rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Algebra.smul_def, map_mul (algebraMap F47 _)]
        conv_rhs => rw [map_mul, (fracMapToF47 ι).commutes]
        have hq : algebraMap ℚ (FractionRing (MvPolynomial ι F47))
            (basisF47.repr (σ47Equiv g (basisF47 i)) k) =
            algebraMap F47 (FractionRing (MvPolynomial ι F47))
              (algebraMap ℚ F47 (basisF47.repr (σ47Equiv g (basisF47 i)) k)) :=
          IsScalarTower.algebraMap_apply ℚ F47 (FractionRing (MvPolynomial ι F47)) _
        rw [hq]; ring
    _ = ∑ k : Fin deg47, algebraMap F47 _ (basisF47 k) *
          ∑ i : Fin deg47, fracMapToF47 ι (algebraMap ℚ _ (basisF47.repr (σ47Equiv g (basisF47 i)) k) * v i) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ k : Fin deg47, algebraMap F47 _ (basisF47 k) *
          fracMapToF47 ι (∑ i : Fin deg47, algebraMap ℚ _ (basisF47.repr (σ47Equiv g (basisF47 i)) k) * v i) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_sum]

/- Section 4: Shift group H, fixed field E = L_F^H, and Γ47-equivariant Φ : E ≃ₐ[F47] M_F -/

private abbrev L0 : Type := FractionRing (MvPolynomial (ZMod 47) ℚ)
private abbrev LF : Type := FractionRing (MvPolynomial (ZMod 47) F47)

private noncomputable def shift0 (k : ZMod 47) : L0 ≃ₐ[ℚ] L0 :=
  IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv ℚ (Equiv.addRight k))

private lemma shift0_algebraMap (k : ZMod 47) (p : MvPolynomial (ZMod 47) ℚ) :
    shift0 k (algebraMap (MvPolynomial (ZMod 47) ℚ) L0 p) =
      algebraMap (MvPolynomial (ZMod 47) ℚ) L0 (MvPolynomial.rename (Equiv.addRight k) p) :=
  fracAlgEquiv_algebraMap (MvPolynomial.renameEquiv ℚ (Equiv.addRight k)) p

private noncomputable def shift0Hom : Multiplicative (ZMod 47) →* (L0 ≃ₐ[ℚ] L0) where
  toFun k := shift0 (Multiplicative.toAdd k)
  map_one' := by
    ext x
    induction x using Localization.induction_on with
    | H a =>
      rcases a with ⟨p, q⟩
      rw [frac_mk_eq_div, map_div₀, shift0_algebraMap, shift0_algebraMap]
      have h1 : ∀ r : MvPolynomial (ZMod 47) ℚ,
          MvPolynomial.rename (Equiv.addRight (Multiplicative.toAdd (1 : Multiplicative (ZMod 47)))) r = r := by
        intro r
        have heq : (Equiv.addRight (Multiplicative.toAdd (1 : Multiplicative (ZMod 47))) : ZMod 47 → ZMod 47) = id := by
          ext i; simp
        rw [heq, MvPolynomial.rename_id]; rfl
      rw [h1 p, h1 q]; rfl
  map_mul' k₁ k₂ := by
    ext x
    induction x using Localization.induction_on with
    | H a =>
      rcases a with ⟨p, q⟩
      rw [frac_mk_eq_div, AlgEquiv.mul_apply, map_div₀, map_div₀, map_div₀,
        shift0_algebraMap, shift0_algebraMap, shift0_algebraMap, shift0_algebraMap,
        shift0_algebraMap, shift0_algebraMap]
      have hcomp : ∀ r : MvPolynomial (ZMod 47) ℚ,
          MvPolynomial.rename (Equiv.addRight (Multiplicative.toAdd (k₁ * k₂))) r =
            MvPolynomial.rename (Equiv.addRight (Multiplicative.toAdd k₁))
              (MvPolynomial.rename (Equiv.addRight (Multiplicative.toAdd k₂)) r) := by
        intro r
        rw [MvPolynomial.rename_rename]
        congr 1; ext i; simp [add_comm]
      rw [hcomp p, hcomp q]

private noncomputable def H0 : Subgroup (L0 ≃ₐ[ℚ] L0) := shift0Hom.range

private noncomputable def shiftF (k : ZMod 47) : LF ≃ₐ[F47] LF :=
  IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv F47 (Equiv.addRight k))

private lemma shiftF_algebraMap_poly (k : ZMod 47) (p : MvPolynomial (ZMod 47) F47) :
    shiftF k (algebraMap (MvPolynomial (ZMod 47) F47) LF p) =
      algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.rename (Equiv.addRight k) p) :=
  fracAlgEquiv_algebraMap (MvPolynomial.renameEquiv F47 (Equiv.addRight k)) p

private noncomputable def shiftFHom : Multiplicative (ZMod 47) →* (LF ≃ₐ[F47] LF) where
  toFun k := shiftF (Multiplicative.toAdd k)
  map_one' := by
    ext x
    induction x using Localization.induction_on with
    | H a =>
      rcases a with ⟨p, q⟩
      rw [frac_mk_eq_div, map_div₀, shiftF_algebraMap_poly, shiftF_algebraMap_poly]
      have h1 : ∀ r : MvPolynomial (ZMod 47) F47,
          MvPolynomial.rename (Equiv.addRight (Multiplicative.toAdd (1 : Multiplicative (ZMod 47)))) r = r := by
        intro r
        have heq : (Equiv.addRight (Multiplicative.toAdd (1 : Multiplicative (ZMod 47))) : ZMod 47 → ZMod 47) = id := by
          ext i; simp
        rw [heq, MvPolynomial.rename_id]; rfl
      rw [h1 p, h1 q]; rfl
  map_mul' k₁ k₂ := by
    ext x
    induction x using Localization.induction_on with
    | H a =>
      rcases a with ⟨p, q⟩
      rw [frac_mk_eq_div, AlgEquiv.mul_apply, map_div₀, map_div₀, map_div₀,
        shiftF_algebraMap_poly, shiftF_algebraMap_poly,
        shiftF_algebraMap_poly, shiftF_algebraMap_poly,
        shiftF_algebraMap_poly, shiftF_algebraMap_poly]
      have hcomp : ∀ r : MvPolynomial (ZMod 47) F47,
          MvPolynomial.rename (Equiv.addRight (Multiplicative.toAdd (k₁ * k₂))) r =
            MvPolynomial.rename (Equiv.addRight (Multiplicative.toAdd k₁))
              (MvPolynomial.rename (Equiv.addRight (Multiplicative.toAdd k₂)) r) := by
        intro r
        rw [MvPolynomial.rename_rename]
        congr 1; ext i; simp [add_comm]
      rw [hcomp p, hcomp q]

private noncomputable def HF : Subgroup (LF ≃ₐ[F47] LF) := shiftFHom.range

private noncomputable def EField : IntermediateField F47 LF := IntermediateField.fixedField HF

private lemma actFrac_comm_shiftF (g : Γ47) (k : ZMod 47) (x : LF) :
    actFrac (ZMod 47) g (shiftF k x) = shiftF k (actFrac (ZMod 47) g x) := by
  induction x using Localization.induction_on with
  | H a =>
    rcases a with ⟨p, q⟩
    rw [frac_mk_eq_div, map_div₀, map_div₀, map_div₀, map_div₀,
      shiftF_algebraMap_poly, shiftF_algebraMap_poly,
      actFrac_algebraMap_poly, actFrac_algebraMap_poly,
      actFrac_algebraMap_poly, actFrac_algebraMap_poly,
      shiftF_algebraMap_poly, shiftF_algebraMap_poly]
    congr 1 <;>
    · congr 1
      rw [MvPolynomial.map_rename]

private lemma actFrac_mem_EField (g : Γ47) (x : LF) (hx : x ∈ EField) :
    actFrac (ZMod 47) g x ∈ EField := by
  intro ⟨h, hh⟩
  rcases hh with ⟨k, rfl⟩
  change shiftF (Multiplicative.toAdd k) (actFrac (ZMod 47) g x) = actFrac (ZMod 47) g x
  rw [← actFrac_comm_shiftF]
  have hx' : shiftF (Multiplicative.toAdd k) x = x := hx ⟨shiftFHom k, ⟨k, rfl⟩⟩
  rw [hx']

private noncomputable def actE : Γ47 →* (EField ≃ₐ[ℚ] EField) where
  toFun g :=
    { toFun := fun x => ⟨actFrac (ZMod 47) g x.1, actFrac_mem_EField g x.1 x.2⟩
      invFun := fun x => ⟨actFrac (ZMod 47) g⁻¹ x.1, actFrac_mem_EField g⁻¹ x.1 x.2⟩
      left_inv := fun x => Subtype.ext (by
        change actFrac (ZMod 47) g⁻¹ (actFrac (ZMod 47) g x.1) = x.1
        rw [← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgEquiv.one_apply])
      right_inv := fun x => Subtype.ext (by
        change actFrac (ZMod 47) g (actFrac (ZMod 47) g⁻¹ x.1) = x.1
        rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply])
      map_mul' := fun x y => Subtype.ext (map_mul (actFrac (ZMod 47) g) x.1 y.1)
      map_add' := fun x y => Subtype.ext (map_add (actFrac (ZMod 47) g) x.1 y.1)
      commutes' := fun r => Subtype.ext ((actFrac (ZMod 47) g).commutes r) }
  map_one' := by ext x; simp
  map_mul' g₁ g₂ := by ext x; simp

private lemma shiftF_expandF47 (m : ZMod 47) (v : Fin deg47 → L0) :
    shiftF m (expandF47 (ZMod 47) v) = expandF47 (ZMod 47) (fun k => shift0 m (v k)) := by
  simp only [expandF47, map_sum, map_mul, (shiftF m).commutes]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  induction h : v k using Localization.induction_on with
  | H a =>
    rcases a with ⟨p, q⟩
    rw [frac_mk_eq_div, map_div₀, map_div₀, map_div₀, map_div₀,
      fracMapToF47_algebraMap, fracMapToF47_algebraMap,
      shiftF_algebraMap_poly, shiftF_algebraMap_poly,
      shift0_algebraMap, shift0_algebraMap,
      fracMapToF47_algebraMap, fracMapToF47_algebraMap]
    congr 1 <;>
    · congr 1
      rw [MvPolynomial.map_rename]

private lemma mem_EField_iff_expand (v : Fin deg47 → L0) :
    expandF47 (ZMod 47) v ∈ EField ↔ ∀ k, v k ∈ IntermediateField.fixedField H0 := by
  constructor
  · intro hv k ⟨h, hh⟩
    rcases hh with ⟨m, rfl⟩
    have hfix : shiftF (Multiplicative.toAdd m) (expandF47 (ZMod 47) v) = expandF47 (ZMod 47) v :=
      hv ⟨shiftFHom m, ⟨m, rfl⟩⟩
    rw [shiftF_expandF47] at hfix
    exact congr_fun (expandF47_injective (ZMod 47) hfix) k
  · intro hv ⟨h, hh⟩
    rcases hh with ⟨m, rfl⟩
    change shiftF (Multiplicative.toAdd m) (expandF47 (ZMod 47) v) = expandF47 (ZMod 47) v
    rw [shiftF_expandF47]
    congr 1; ext k
    exact hv k ⟨shift0Hom m, ⟨m, rfl⟩⟩

private noncomputable def baseChangeEquiv {ι' : Type}
    (e0 : IntermediateField.fixedField H0 ≃ₐ[ℚ] FractionRing (MvPolynomial ι' ℚ)) :
    { Φ : EField ≃ₐ[F47] FractionRing (MvPolynomial ι' F47) //
      ∀ g x, Φ (actE g x) = actFrac ι' g (Φ x) } := by
  set K0 := IntermediateField.fixedField H0
  set M0 := FractionRing (MvPolynomial ι' ℚ)
  set MF := FractionRing (MvPolynomial ι' F47)
  have hmemK0 : ∀ x : EField, ∀ k : Fin deg47, (expandEquiv (ZMod 47)).symm x.1 k ∈ K0 := by
    intro x
    rw [← mem_EField_iff_expand]
    have h1 : expandF47 (ZMod 47) ((expandEquiv (ZMod 47)).symm x.1) = x.1 :=
      (expandEquiv (ZMod 47)).apply_symm_apply x.1
    rw [h1]
    exact x.2
  let toFun : EField → MF := fun x =>
    expandF47 ι' (fun k => e0 ⟨(expandEquiv (ZMod 47)).symm x.1 k, hmemK0 x k⟩)
  let invFun : MF → EField := fun y =>
    ⟨expandF47 (ZMod 47) (fun k => (e0.symm ((expandEquiv ι').symm y k) : L0)),
      (mem_EField_iff_expand _).mpr fun k => (e0.symm ((expandEquiv ι').symm y k)).2⟩
  have hleft : ∀ x : EField, invFun (toFun x) = x := by
    intro x
    apply Subtype.ext
    change expandF47 (ZMod 47) _ = x.1
    have h1 : ∀ k, (expandEquiv ι').symm (toFun x) k =
        e0 ⟨(expandEquiv (ZMod 47)).symm x.1 k, hmemK0 x k⟩ := fun k => by
      change (expandEquiv ι').symm (expandEquiv ι' _) k = _
      rw [Equiv.symm_apply_apply]
    simp_rw [h1, AlgEquiv.symm_apply_apply]
    exact (expandEquiv (ZMod 47)).apply_symm_apply x.1
  have hright : ∀ y : MF, toFun (invFun y) = y := by
    intro y
    dsimp [toFun, invFun]
    have h1 : ∀ k, (expandEquiv (ZMod 47)).symm
        (expandF47 (ZMod 47) (fun k => (e0.symm ((expandEquiv ι').symm y k) : L0))) k =
        (e0.symm ((expandEquiv ι').symm y k) : L0) := fun k => by
      change (expandEquiv (ZMod 47)).symm (expandEquiv (ZMod 47) _) k = _
      rw [Equiv.symm_apply_apply]
    have h2 : (fun k => e0 ⟨(expandEquiv (ZMod 47)).symm
        (expandF47 (ZMod 47) (fun k => (e0.symm ((expandEquiv ι').symm y k) : L0))) k,
        hmemK0 (invFun y) k⟩) =
        (expandEquiv ι').symm y := by
      ext k
      have hsub : (⟨(expandEquiv (ZMod 47)).symm
          (expandF47 (ZMod 47) (fun k => (e0.symm ((expandEquiv ι').symm y k) : L0))) k,
          hmemK0 (invFun y) k⟩ : K0) = e0.symm ((expandEquiv ι').symm y k) :=
        Subtype.ext (h1 k)
      rw [hsub, AlgEquiv.apply_symm_apply]
    rw [h2]
    exact (expandEquiv ι').apply_symm_apply y
  have hcoord_eq : ∀ (x : EField) (v : Fin deg47 → K0),
      x.1 = expandF47 (ZMod 47) (fun k => (v k : L0)) →
      toFun x = expandF47 ι' (fun k => e0 (v k)) := by
    intro x v hv
    dsimp [toFun]
    congr 1; ext k
    congr 1; apply Subtype.ext
    have h1 : (expandEquiv (ZMod 47)).symm x.1 = fun k => (v k : L0) := by
      apply (expandEquiv (ZMod 47)).injective
      rw [Equiv.apply_symm_apply]
      exact hv
    exact congr_fun h1 k
  let Φ : EField ≃ₐ[F47] MF :=
    { toFun := toFun
      invFun := invFun
      left_inv := hleft
      right_inv := hright
      map_add' := fun x y => by
        set vx : Fin deg47 → K0 := fun k => ⟨(expandEquiv (ZMod 47)).symm x.1 k, hmemK0 x k⟩
        set vy : Fin deg47 → K0 := fun k => ⟨(expandEquiv (ZMod 47)).symm y.1 k, hmemK0 y k⟩
        have hx : x.1 = expandF47 (ZMod 47) (fun k => (vx k : L0)) :=
          ((expandEquiv (ZMod 47)).apply_symm_apply x.1).symm
        have hy : y.1 = expandF47 (ZMod 47) (fun k => (vy k : L0)) :=
          ((expandEquiv (ZMod 47)).apply_symm_apply y.1).symm
        have hxy : (x + y).1 = expandF47 (ZMod 47) (fun k => ((vx k + vy k : K0) : L0)) := by
          change x.1 + y.1 = _
          rw [hx, hy, ← expandF47_add]; rfl
        rw [hcoord_eq (x + y) (fun k => vx k + vy k) hxy, hcoord_eq x vx hx, hcoord_eq y vy hy,
          ← expandF47_add]
        congr 1; ext k; exact map_add e0 (vx k) (vy k)
      map_mul' := fun x y => by
        set vx : Fin deg47 → K0 := fun k => ⟨(expandEquiv (ZMod 47)).symm x.1 k, hmemK0 x k⟩
        set vy : Fin deg47 → K0 := fun k => ⟨(expandEquiv (ZMod 47)).symm y.1 k, hmemK0 y k⟩
        have hx : x.1 = expandF47 (ZMod 47) (fun k => (vx k : L0)) :=
          ((expandEquiv (ZMod 47)).apply_symm_apply x.1).symm
        have hy : y.1 = expandF47 (ZMod 47) (fun k => (vy k : L0)) :=
          ((expandEquiv (ZMod 47)).apply_symm_apply y.1).symm
        let vxy : Fin deg47 → K0 := fun k =>
          ∑ i : Fin deg47, ∑ j : Fin deg47,
            algebraMap ℚ K0 (basisF47.repr (basisF47 i * basisF47 j) k) * (vx i * vy j)
        have hxy : (x * y).1 = expandF47 (ZMod 47) (fun k => (vxy k : L0)) := by
          change x.1 * y.1 = _
          rw [hx, hy, expandF47_mul]
          congr 1; ext k
          dsimp [vxy]
          simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul]
          rfl
        rw [hcoord_eq (x * y) vxy hxy, hcoord_eq x vx hx, hcoord_eq y vy hy, expandF47_mul]
        congr 1; ext k
        dsimp [vxy]
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul e0, e0.commutes, map_mul e0]
      commutes' := fun c => by
        let vc : Fin deg47 → K0 := fun k => algebraMap ℚ K0 (basisF47.repr c k)
        have hc : (algebraMap F47 EField c : LF) = expandF47 (ZMod 47) (fun k => (vc k : L0)) := by
          exact expandF47_algebraMap (ZMod 47) c
        rw [hcoord_eq (algebraMap F47 EField c) vc hc, expandF47_algebraMap ι' c]
        congr 1; ext k
        exact e0.commutes _ }
  refine ⟨Φ, fun g x => ?_⟩
  set vx : Fin deg47 → K0 := fun k => ⟨(expandEquiv (ZMod 47)).symm x.1 k, hmemK0 x k⟩
  have hx : x.1 = expandF47 (ZMod 47) (fun k => (vx k : L0)) :=
    ((expandEquiv (ZMod 47)).apply_symm_apply x.1).symm
  let vgx : Fin deg47 → K0 := fun k =>
    ∑ i : Fin deg47, algebraMap ℚ K0 (basisF47.repr (σ47Equiv g (basisF47 i)) k) * vx i
  have hgx : (actE g x).1 = expandF47 (ZMod 47) (fun k => (vgx k : L0)) := by
    change actFrac (ZMod 47) g x.1 = _
    rw [hx, actFrac_expandF47]
    congr 1; ext k
    dsimp [vgx]
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul]
    rfl
  change toFun (actE g x) = actFrac ι' g (toFun x)
  rw [hcoord_eq (actE g x) vgx hgx, hcoord_eq x vx hx, actFrac_expandF47]
  congr 1; ext k
  dsimp [vgx]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul e0, e0.commutes]

/- Section 5: Lagrange resolvents, Fourier equivalence, ring B, Frac(B) = E, and Bˣ -/

private noncomputable def yPoly (a : ZMod 47) : MvPolynomial (ZMod 47) F47 :=
  ∑ i : ZMod 47, MvPolynomial.C (zpow47 (-(a * i))) * MvPolynomial.X i

private noncomputable def yElem (a : ZMod 47) : LF :=
  algebraMap (MvPolynomial (ZMod 47) F47) LF (yPoly a)

private lemma fourier_inv_poly (j : ZMod 47) :
    ∑ a : ZMod 47, MvPolynomial.C (zpow47 (a * j)) * yPoly a =
      MvPolynomial.C (47 : F47) * MvPolynomial.X j := by
  simp only [yPoly, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc ∑ i : ZMod 47, ∑ a : ZMod 47,
        MvPolynomial.C (zpow47 (a * j)) * (MvPolynomial.C (zpow47 (-(a * i))) * MvPolynomial.X i)
      = ∑ i : ZMod 47, (∑ a : ZMod 47, MvPolynomial.C (zpow47 ((j - i) * a))) * MvPolynomial.X i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← mul_assoc, ← map_mul, ← zpow47_add]
        congr 2; ring
    _ = ∑ i : ZMod 47, (MvPolynomial.C (if j - i = 0 then (47 : F47) else 0)) * MvPolynomial.X i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← map_sum, sum_zpow47_mul]
    _ = MvPolynomial.C (47 : F47) * MvPolynomial.X j := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro i _ hij
          have hne : j - i ≠ 0 := sub_ne_zero.mpr (Ne.symm hij)
          simp [hne]
        · intro h; exact absurd (Finset.mem_univ j) h

private noncomputable def fourierTo :
    MvPolynomial (ZMod 47) F47 →ₐ[F47] MvPolynomial (ZMod 47) F47 :=
  MvPolynomial.aeval yPoly

private noncomputable def fourierInv :
    MvPolynomial (ZMod 47) F47 →ₐ[F47] MvPolynomial (ZMod 47) F47 :=
  MvPolynomial.aeval (fun j => MvPolynomial.C ((47 : F47)⁻¹) *
    ∑ a : ZMod 47, MvPolynomial.C (zpow47 (a * j)) * MvPolynomial.X a)

private lemma fourierInv_comp_fourierTo :
    fourierInv.comp fourierTo = AlgHom.id F47 _ := by
  apply MvPolynomial.algHom_ext
  intro a
  simp only [AlgHom.comp_apply, AlgHom.id_apply, fourierTo, MvPolynomial.aeval_X, yPoly,
    map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, fourierInv]
  have h47 : (47 : F47) ≠ 0 := by norm_num
  have hstep : ∀ i : ZMod 47, MvPolynomial.C (zpow47 (-(a * i))) *
      (MvPolynomial.C (47 : F47)⁻¹ * ∑ b : ZMod 47, MvPolynomial.C (zpow47 (b * i)) * MvPolynomial.X b) =
      ∑ b : ZMod 47, MvPolynomial.C (47 : F47)⁻¹ *
        (MvPolynomial.C (zpow47 ((b - a) * i)) * MvPolynomial.X b) := by
    intro i
    rw [← mul_assoc, mul_comm (MvPolynomial.C (zpow47 (-(a * i)))), mul_assoc,
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_assoc (MvPolynomial.C (zpow47 (-(a * i)))), ← map_mul, ← zpow47_add]
    congr 3; ring
  simp_rw [hstep]
  rw [Finset.sum_comm]
  calc ∑ b : ZMod 47, ∑ i : ZMod 47,
        MvPolynomial.C (47 : F47)⁻¹ * (MvPolynomial.C (zpow47 ((b - a) * i)) * MvPolynomial.X b)
      = MvPolynomial.C (47 : F47)⁻¹ *
          ∑ b : ZMod 47, (∑ i : ZMod 47, MvPolynomial.C (zpow47 ((b - a) * i))) * MvPolynomial.X b := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_mul, Finset.mul_sum]
    _ = MvPolynomial.C (47 : F47)⁻¹ *
          ∑ b : ZMod 47, MvPolynomial.C (if b = a then (47 : F47) else 0) * MvPolynomial.X b := by
        apply congr_arg (MvPolynomial.C (47 : F47)⁻¹ * ·)
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← map_sum, sum_zpow47_mul]
        simp only [sub_eq_zero]
    _ = MvPolynomial.X a := by
        have hsum : ∑ b : ZMod 47, MvPolynomial.C (if b = a then (47 : F47) else 0) * MvPolynomial.X b =
            MvPolynomial.C (47 : F47) * MvPolynomial.X a := by
          rw [Finset.sum_eq_single a]
          · rw [if_pos rfl]
          · intro b _ hba; rw [if_neg hba, map_zero, zero_mul]
          · intro h; exact absurd (Finset.mem_univ a) h
        rw [hsum, ← mul_assoc, ← map_mul, inv_mul_cancel₀ h47, map_one, one_mul]

private lemma fourierTo_comp_fourierInv :
    fourierTo.comp fourierInv = AlgHom.id F47 _ := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, AlgHom.id_apply, fourierInv, MvPolynomial.aeval_X,
    map_mul, map_sum, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, fourierTo]
  rw [fourier_inv_poly, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (by norm_num : (47 : F47) ≠ 0),
    map_one, one_mul]

private noncomputable def fourierEquiv :
    MvPolynomial (ZMod 47) F47 ≃ₐ[F47] MvPolynomial (ZMod 47) F47 :=
  AlgEquiv.ofAlgHom fourierTo fourierInv fourierTo_comp_fourierInv fourierInv_comp_fourierTo

private noncomputable def fourierFracEquiv : LF ≃ₐ[F47] LF :=
  IsFractionRing.algEquivOfAlgEquiv fourierEquiv

private lemma fourierFracEquiv_X (a : ZMod 47) :
    fourierFracEquiv (algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X a)) = yElem a :=
  (fracAlgEquiv_algebraMap fourierEquiv (MvPolynomial.X a)).trans (by
    simp [fourierEquiv, fourierTo, yElem])

private lemma yPoly_ne_zero (a : ZMod 47) : yPoly a ≠ 0 := by
  intro h
  have h0 : fourierEquiv (MvPolynomial.X a) = 0 := by simpa [fourierEquiv, fourierTo] using h
  have hX : (MvPolynomial.X a : MvPolynomial (ZMod 47) F47) = 0 :=
    fourierEquiv.injective (by rw [h0, map_zero])
  exact MvPolynomial.X_ne_zero a hX

private lemma yElem_ne_zero (a : ZMod 47) : yElem a ≠ 0 := by
  intro h
  exact yPoly_ne_zero a (IsFractionRing.injective (MvPolynomial (ZMod 47) F47) LF (by rw [← yElem, h, map_zero]))

private lemma shiftF_yPoly (k a : ZMod 47) :
    MvPolynomial.rename (Equiv.addRight k) (yPoly a) =
      MvPolynomial.C (zpow47 (a * k)) * yPoly a := by
  simp only [yPoly, map_sum, map_mul, MvPolynomial.rename_C, MvPolynomial.rename_X, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight k) _ _ fun i => ?_
  rw [← mul_assoc, ← map_mul, ← zpow47_add]
  congr 2
  congr 1
  change -(a * i) = a * k + -(a * (i + k))
  ring

private lemma shiftF_yElem (k a : ZMod 47) :
    shiftF k (yElem a) = algebraMap F47 LF (zpow47 (a * k)) * yElem a := by
  simp only [yElem, shiftF_algebraMap_poly, shiftF_yPoly, map_mul]
  rfl

private lemma actFrac_yPoly (g : Γ47) (a : ZMod 47) :
    MvPolynomial.map (σ47Equiv g).toRingHom (yPoly a) = yPoly ((g : ZMod 47) * a) := by
  simp only [yPoly, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  change σ47Hom g (zpow47 (-(a * i))) = zpow47 (-((g : ZMod 47) * a * i))
  rw [σ47Hom_zpow47]
  congr 1; ring

private lemma actFrac_yElem (g : Γ47) (a : ZMod 47) :
    actFrac (ZMod 47) g (yElem a) = yElem ((g : ZMod 47) * a) := by
  simp only [yElem, actFrac_algebraMap_poly, actFrac_yPoly]

private lemma yElem_zero_mem_E : yElem 0 ∈ EField := by
  intro ⟨h, hh⟩
  rcases hh with ⟨k, rfl⟩
  change shiftF (Multiplicative.toAdd k) (yElem 0) = yElem 0
  rw [shiftF_yElem, zero_mul, zpow47_zero, map_one, one_mul]

private noncomputable def y0E : EField := ⟨yElem 0, yElem_zero_mem_E⟩

private lemma actE_y0E (g : Γ47) : actE g y0E = y0E := by
  apply Subtype.ext
  change actFrac (ZMod 47) g (yElem 0) = yElem 0
  rw [actFrac_yElem, mul_zero]

private noncomputable def monomL (u : SwanIdeal) : LF :=
  ∏ a : Γ47, (yElem (a : ZMod 47)) ^ (u.1 a)

private lemma monomL_mem_E (u : SwanIdeal) : monomL u ∈ EField := by
  intro ⟨h, hh⟩
  rcases hh with ⟨k, rfl⟩
  change shiftF (Multiplicative.toAdd k) (monomL u) = monomL u
  simp only [monomL, map_prod, map_zpow₀, shiftF_yElem, mul_zpow, Finset.prod_mul_distrib]
  have hprod : ∏ a : Γ47, (algebraMap F47 LF (zpow47 ((a : ZMod 47) * Multiplicative.toAdd k))) ^ (u.1 a) = 1 := by
    have h1 : ∀ a : Γ47, (algebraMap F47 LF (zpow47 ((a : ZMod 47) * Multiplicative.toAdd k))) ^ (u.1 a) =
        algebraMap F47 LF (zpow47 (((u.1 a : ZMod 47) * (a : ZMod 47)) * Multiplicative.toAdd k)) := by
      intro a
      rw [← map_zpow₀, zpow47_zpow]
      congr 2; ring
    simp_rw [h1]
    rw [← map_prod]
    have h2 : ∏ a : Γ47, zpow47 (((u.1 a : ZMod 47) * (a : ZMod 47)) * Multiplicative.toAdd k) =
        zpow47 (∑ a : Γ47, ((u.1 a : ZMod 47) * (a : ZMod 47)) * Multiplicative.toAdd k) := by
      induction (Finset.univ : Finset Γ47) using Finset.cons_induction with
      | empty => simp [zpow47_zero]
      | cons a s ha ih =>
        rw [Finset.prod_cons, Finset.sum_cons, zpow47_add, ih]
    rw [h2, ← Finset.sum_mul, u.2, zero_mul, zpow47_zero, map_one]
  rw [hprod, one_mul]

private noncomputable def monomE (u : SwanIdeal) : EField := ⟨monomL u, monomL_mem_E u⟩

private lemma monomE_ne_zero (u : SwanIdeal) : monomE u ≠ 0 := by
  intro h
  have h1 : monomL u = 0 := congr_arg Subtype.val h
  simp only [monomL, Finset.prod_eq_zero_iff] at h1
  rcases h1 with ⟨a, _, ha⟩
  exact zpow_ne_zero _ (yElem_ne_zero (a : ZMod 47)) ha

private lemma monomE_zero : monomE 0 = 1 := by
  apply Subtype.ext
  change ∏ a : Γ47, (yElem (a : ZMod 47)) ^ (0 : ℤ) = 1
  simp

private lemma monomE_add (u v : SwanIdeal) : monomE (u + v) = monomE u * monomE v := by
  apply Subtype.ext
  change ∏ a : Γ47, (yElem (a : ZMod 47)) ^ (u.1 a + v.1 a) =
    (∏ a : Γ47, (yElem (a : ZMod 47)) ^ (u.1 a)) * (∏ a : Γ47, (yElem (a : ZMod 47)) ^ (v.1 a))
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  exact zpow_add₀ (yElem_ne_zero (a : ZMod 47)) _ _

private lemma monomE_neg (u : SwanIdeal) : monomE (-u) = (monomE u)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← monomE_add, neg_add_cancel, monomE_zero]

set_option maxRecDepth 4096 in
private lemma actE_monomE (g : Γ47) (u : SwanIdeal) : actE g (monomE u) = monomE (swanAct g u) := by
  apply Subtype.ext
  change actFrac (ZMod 47) g (∏ a : Γ47, (yElem (a : ZMod 47)) ^ (u.1 a)) =
    ∏ b : Γ47, (yElem (b : ZMod 47)) ^ (u.1 (g⁻¹ * b))
  simp only [map_prod, map_zpow₀, actFrac_yElem]
  refine Fintype.prod_equiv (Equiv.mulLeft g) _ _ fun a => ?_
  simp [Units.val_mul]

private abbrev PB : Type := MvPolynomial (Option Γ47) F47

private noncomputable def tB : PB := ∏ b : Γ47, MvPolynomial.X (some b)

private noncomputable def φB : PB →ₐ[F47] EField :=
  MvPolynomial.aeval (fun o => Option.rec y0E (fun b => monomE (swanBasis b)) o)

private lemma φB_X_none : φB (MvPolynomial.X none) = y0E := by simp [φB]
private lemma φB_X_some (b : Γ47) : φB (MvPolynomial.X (some b)) = monomE (swanBasis b) := by simp [φB]

private lemma φB_tB_ne_zero : φB tB ≠ 0 := by
  simp only [tB, map_prod, φB_X_some]
  exact Finset.prod_ne_zero_iff.mpr fun b _ => monomE_ne_zero (swanBasis b)

set_option maxRecDepth 4096 in
private lemma φB_injective : Function.Injective φB := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have hpL : fourierFracEquiv.symm (φB p : LF) = 0 := by
    rw [hp, ZeroMemClass.coe_zero, map_zero]
  let expVec (d : Option Γ47 →₀ ℕ) : ZMod 47 → ℤ := fun a =>
    if ha : a = 0 then (d none : ℤ)
    else (swanEquiv (fun b => (d (some b) : ℤ))).1 (Units.mk0 a ha)
  have hexp_inj : Function.Injective expVec := by
    intro d₁ d₂ h
    ext o
    cases o with
    | none =>
      have h0 := congr_fun h 0
      simp only [expVec, ↓reduceDIte] at h0
      exact Int.ofNat.inj h0
    | some b =>
      have hu : swanEquiv (fun b' => (d₁ (some b') : ℤ)) =
          swanEquiv (fun b' => (d₂ (some b') : ℤ)) := by
        ext a
        have ha := congr_fun h (a : ZMod 47)
        simp only [expVec, a.ne_zero, ↓reduceDIte, Units.mk0_val] at ha
        exact ha
      have hc := congr_fun (swanEquiv.injective hu) b
      exact Int.ofNat.inj hc
  have hmon : ∀ d : Option Γ47 →₀ ℕ,
      fourierFracEquiv.symm (φB (MvPolynomial.monomial d 1) : LF) =
        ∏ a : ZMod 47, (algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X a)) ^ (expVec d a) := by
    intro d
    rw [MvPolynomial.monomial_eq, map_mul, map_one, map_one, one_mul, Finsupp.prod, map_prod]
    rw [SubmonoidClass.coe_finsetProd, map_prod]
    simp_rw [map_pow, SubmonoidClass.coe_pow, map_pow]
    have hprod_split : (∏ x ∈ d.support, fourierFracEquiv.symm (φB (MvPolynomial.X x) : LF) ^ d x) =
        (fourierFracEquiv.symm (y0E : LF)) ^ d none *
          ∏ b : Γ47, (fourierFracEquiv.symm (monomE (swanBasis b) : LF)) ^ d (some b) := by
      have hfull : (∏ x ∈ d.support, fourierFracEquiv.symm (φB (MvPolynomial.X x) : LF) ^ d x) =
          ∏ x : Option Γ47, fourierFracEquiv.symm (φB (MvPolynomial.X x) : LF) ^ d x := by
        apply Finset.prod_subset (Finset.subset_univ _)
        intro x _ hx
        rw [Finsupp.notMem_support_iff.mp hx, pow_zero]
      rw [hfull, Fintype.prod_option]
      simp [φB_X_none, φB_X_some]
    rw [hprod_split]
    have hy0 : fourierFracEquiv.symm (y0E : LF) =
        algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X 0) := by
      change fourierFracEquiv.symm (yElem 0) = _
      rw [← fourierFracEquiv_X 0, AlgEquiv.symm_apply_apply]
    have hmb : ∀ b : Γ47, fourierFracEquiv.symm (monomE (swanBasis b) : LF) =
        ∏ a : Γ47, (algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X (a : ZMod 47))) ^
          ((swanBasis b).1 a) := by
      intro b
      change fourierFracEquiv.symm (∏ a : Γ47, (yElem (a : ZMod 47)) ^ ((swanBasis b).1 a)) = _
      simp only [map_prod, map_zpow₀]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [← fourierFracEquiv_X (a : ZMod 47), AlgEquiv.symm_apply_apply]
    rw [hy0]
    simp_rw [hmb]
    have hXne : ∀ a : ZMod 47, algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X a) ≠ 0 := by
      intro a h0
      exact MvPolynomial.X_ne_zero a (IsFractionRing.injective _ _ (by rw [h0, map_zero]))
    have hprod_b : ∏ b : Γ47, (∏ a : Γ47,
        (algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X (a : ZMod 47))) ^
          ((swanBasis b).1 a)) ^ d (some b) =
        ∏ a : Γ47, (algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X (a : ZMod 47))) ^
          ((swanEquiv (fun b => (d (some b) : ℤ))).1 a) := by
      simp_rw [← Finset.prod_pow]
      rw [Finset.prod_comm]
      refine Finset.prod_congr rfl fun a _ => ?_
      have h1 : ∀ b : Γ47, ((algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X (a : ZMod 47))) ^
          ((swanBasis b).1 a)) ^ d (some b) =
          (algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X (a : ZMod 47))) ^
            ((d (some b) : ℤ) * (swanBasis b).1 a) := by
        intro b
        rw [← zpow_natCast, ← zpow_mul, mul_comm]
      simp_rw [h1]
      have h2 : ∀ s : Finset Γ47, ∏ b ∈ s,
          (algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X (a : ZMod 47))) ^
            ((d (some b) : ℤ) * (swanBasis b).1 a) =
          (algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X (a : ZMod 47))) ^
            (∑ b ∈ s, (d (some b) : ℤ) * (swanBasis b).1 a) := by
        intro s
        induction s using Finset.cons_induction with
        | empty => simp
        | cons b s hb ih =>
          rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ (hXne _)]
      rw [h2]
      congr 1
      have heq := swanEquiv_eq_sum (fun b => (d (some b) : ℤ))
      have hval := congr_arg (fun u : SwanIdeal => u.1 a) heq
      simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, AddSubgroup.coe_zsmul, Pi.smul_apply,
        smul_eq_mul] at hval
      exact hval.symm
    rw [hprod_b]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (0 : ZMod 47))]
    simp only [expVec, ↓reduceDIte, zpow_natCast]
    apply congr_arg ((algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X 0)) ^ d none * ·)
    refine Finset.prod_bij (fun (b : Γ47) _ => (b : ZMod 47))
      (fun b _ => Finset.mem_erase.mpr ⟨b.ne_zero, Finset.mem_univ _⟩)
      (fun b₁ _ b₂ _ h => Units.ext h)
      (fun a ha => ⟨Units.mk0 a (Finset.mem_erase.mp ha).1, Finset.mem_univ _, rfl⟩)
      (fun b _ => by simp [b.ne_zero])
  let N : ℕ := p.support.sup (fun d => Finset.univ.sup (fun a : ZMod 47 => (expVec d a).natAbs))
  have hN : ∀ d ∈ p.support, ∀ a : ZMod 47, 0 ≤ expVec d a + (N : ℤ) := by
    intro d hd a
    have hle : (expVec d a).natAbs ≤ N :=
      le_trans (Finset.le_sup (f := fun a : ZMod 47 => (expVec d a).natAbs) (Finset.mem_univ a))
        (Finset.le_sup (f := fun d => Finset.univ.sup (fun a : ZMod 47 => (expVec d a).natAbs)) hd)
    omega
  let shiftMon (d : Option Γ47 →₀ ℕ) : ZMod 47 →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm (fun a => (expVec d a + (N : ℤ)).toNat)
  have hshift_apply : ∀ d a, shiftMon d a = (expVec d a + (N : ℤ)).toNat := fun _ _ => rfl
  have hshift_inj : ∀ d₁ ∈ p.support, ∀ d₂ ∈ p.support, shiftMon d₁ = shiftMon d₂ → d₁ = d₂ := by
    intro d₁ hd₁ d₂ hd₂ h
    apply hexp_inj
    ext a
    have ha : (expVec d₁ a + (N : ℤ)).toNat = (expVec d₂ a + (N : ℤ)).toNat :=
      congr_arg (fun f : ZMod 47 →₀ ℕ => f a) h
    have h1 := Int.toNat_of_nonneg (hN d₁ hd₁ a)
    have h2 := Int.toNat_of_nonneg (hN d₂ hd₂ a)
    omega
  have hpoly0 : ∑ d ∈ p.support, MvPolynomial.monomial (shiftMon d) (MvPolynomial.coeff d p) = 0 := by
    apply IsFractionRing.injective (MvPolynomial (ZMod 47) F47) LF
    rw [map_zero, map_sum]
    have hmul0 : (∏ a : ZMod 47, (algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X a)) ^ N) *
        fourierFracEquiv.symm (φB p : LF) = 0 := by
      rw [hpL, mul_zero]
    rw [← hmul0]
    conv_rhs => rw [MvPolynomial.as_sum p]
    rw [map_sum, AddSubmonoidClass.coe_finsetSum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hmon_c : MvPolynomial.monomial d (MvPolynomial.coeff d p) =
        MvPolynomial.C (MvPolynomial.coeff d p) * MvPolynomial.monomial d 1 := by
      rw [MvPolynomial.C_mul_monomial, mul_one]
    rw [hmon_c, map_mul, Subalgebra.coe_mul, map_mul]
    have hC : fourierFracEquiv.symm (φB (MvPolynomial.C (MvPolynomial.coeff d p)) : LF) =
        algebraMap F47 LF (MvPolynomial.coeff d p) := by
      have : φB (MvPolynomial.C (MvPolynomial.coeff d p)) = algebraMap F47 EField (MvPolynomial.coeff d p) :=
        φB.commutes _
      rw [this]
      exact fourierFracEquiv.symm.commutes _
    rw [hC, hmon d]
    rw [MvPolynomial.monomial_eq, map_mul, Finsupp.prod, map_prod]
    have hXne : ∀ a : ZMod 47, algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X a) ≠ 0 := by
      intro a h0
      exact MvPolynomial.X_ne_zero a (IsFractionRing.injective _ _ (by rw [h0, map_zero]))
    have hprod_eq : ∏ x ∈ (shiftMon d).support,
        (algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X x)) ^ (shiftMon d x) =
        (∏ a : ZMod 47, (algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X a)) ^ N) *
          (∏ a : ZMod 47, (algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X a)) ^ (expVec d a)) := by
      have hfull : ∏ x ∈ (shiftMon d).support,
          (algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X x)) ^ (shiftMon d x) =
          ∏ a : ZMod 47, (algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X a)) ^ (shiftMon d a) := by
        apply Finset.prod_subset (Finset.subset_univ _)
        intro a _ ha
        rw [Finsupp.notMem_support_iff.mp ha, pow_zero]
      rw [hfull, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hXne a)]
      congr 1
      rw [hshift_apply]
      have hnn := Int.toNat_of_nonneg (hN d hd a)
      linarith
    simp only [map_pow] at hprod_eq ⊢
    rw [hprod_eq]
    change algebraMap F47 LF (MvPolynomial.coeff d p) * _ = _
    ring
  ext d
  rw [MvPolynomial.coeff_zero]
  by_cases hd : d ∈ p.support
  · have hcoeff := congr_arg (MvPolynomial.coeff (shiftMon d)) hpoly0
    rw [MvPolynomial.coeff_zero, MvPolynomial.coeff_sum] at hcoeff
    rw [Finset.sum_eq_single d] at hcoeff
    · simpa [MvPolynomial.coeff_monomial] using hcoeff
    · intro d' hd' hne
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro heq
      exact hne (hshift_inj d' hd' d hd heq)
    · intro h; exact absurd hd h
  · exact MvPolynomial.notMem_support_iff.mp hd

private noncomputable def ringB : Subalgebra F47 EField where
  carrier := { x : EField | ∃ (p : PB) (k : ℕ), x = φB p / (φB tB) ^ k }
  mul_mem' := by
    rintro _ _ ⟨p₁, k₁, rfl⟩ ⟨p₂, k₂, rfl⟩
    refine ⟨p₁ * p₂, k₁ + k₂, ?_⟩
    rw [map_mul, pow_add, div_mul_div_comm]
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨p₁, k₁, rfl⟩ ⟨p₂, k₂, rfl⟩
    refine ⟨p₁ * tB ^ k₂ + p₂ * tB ^ k₁, k₁ + k₂, ?_⟩
    have ht1 : (φB tB) ^ k₁ ≠ 0 := pow_ne_zero k₁ φB_tB_ne_zero
    have ht2 : (φB tB) ^ k₂ ≠ 0 := pow_ne_zero k₂ φB_tB_ne_zero
    rw [map_add, map_mul, map_mul, map_pow, map_pow, pow_add]
    field_simp
  zero_mem' := ⟨0, 0, by simp⟩
  algebraMap_mem' c := ⟨MvPolynomial.C c, 0, by simp⟩

private lemma y0E_mem_ringB : y0E ∈ ringB :=
  ⟨MvPolynomial.X none, 0, by simp [φB_X_none]⟩

set_option maxRecDepth 4096 in
private lemma monomE_mem_ringB (u : SwanIdeal) : monomE u ∈ ringB := by
  set c := swanEquiv.symm u
  let N : ℕ := Finset.univ.sup (fun b : Γ47 => (c b).natAbs)
  have hN : ∀ b : Γ47, 0 ≤ c b + (N : ℤ) := by
    intro b
    have hle : (c b).natAbs ≤ N :=
      Finset.le_sup (f := fun b : Γ47 => (c b).natAbs) (Finset.mem_univ b)
    omega
  refine ⟨∏ b : Γ47, (MvPolynomial.X (some b)) ^ (c b + (N : ℤ)).toNat, N, ?_⟩
  simp only [map_prod, map_pow, φB_X_some, tB]
  rw [← Finset.prod_pow, ← Finset.prod_div_distrib]
  have hu : u = ∑ b : Γ47, c b • swanBasis b := by
    simpa [c] using swanEquiv_eq_sum c
  have hmon : monomE u = ∏ b : Γ47, (monomE (swanBasis b)) ^ (c b) := by
    rw [hu]
    have hsum : ∀ s : Finset Γ47,
        monomE (∑ b ∈ s, c b • swanBasis b) = ∏ b ∈ s, (monomE (swanBasis b)) ^ (c b) := by
      intro s
      induction s using Finset.cons_induction with
      | empty => simp [monomE_zero]
      | cons b s hb ih =>
        rw [Finset.sum_cons, Finset.prod_cons, monomE_add, ih]
        congr 1
        have hz : ∀ n : ℤ, monomE (n • swanBasis b) = (monomE (swanBasis b)) ^ n := by
          intro n
          induction n with
          | zero => simp [monomE_zero]
          | succ k ihk =>
            rw [add_smul, one_smul, monomE_add, ihk, zpow_add_one₀ (monomE_ne_zero _)]
          | pred k ihk =>
            rw [sub_smul, one_smul, sub_eq_add_neg, monomE_add, monomE_neg, ihk,
              zpow_sub_one₀ (monomE_ne_zero _)]
        exact hz (c b)
    exact hsum Finset.univ
  rw [hmon]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ (monomE_ne_zero _)]
  congr 1
  have hnn := Int.toNat_of_nonneg (hN b)
  linarith

private lemma actE_mem_ringB (g : Γ47) (x : EField) (hx : x ∈ ringB) : actE g x ∈ ringB := by
  rcases hx with ⟨p, k, rfl⟩
  rw [map_div₀, map_pow]
  have hφ_mem : ∀ q : PB, actE g (φB q) ∈ ringB := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c =>
      have : φB (MvPolynomial.C c) = algebraMap F47 EField c := φB.commutes c
      rw [this]
      have hact : actE g (algebraMap F47 EField c) = algebraMap F47 EField (σ47Equiv g c) := by
        apply Subtype.ext
        exact actFrac_algebraMap_F47 (ZMod 47) g c
      rw [hact]
      exact ringB.algebraMap_mem _
    | add q₁ q₂ h₁ h₂ =>
      rw [map_add, map_add]
      exact ringB.add_mem h₁ h₂
    | mul_X q o hq =>
      rw [map_mul, map_mul]
      refine ringB.mul_mem hq ?_
      cases o with
      | none =>
        rw [φB_X_none, actE_y0E]
        exact y0E_mem_ringB
      | some b =>
        rw [φB_X_some, actE_monomE]
        exact monomE_mem_ringB _
  have hinv_mem : (actE g (φB tB))⁻¹ ∈ ringB := by
    simp only [tB, map_prod, φB_X_some, actE_monomE]
    rw [← Finset.prod_inv_distrib]
    exact ringB.prod_mem fun b _ => by
      rw [← monomE_neg]
      exact monomE_mem_ringB _
  rw [div_eq_mul_inv, ← inv_pow]
  exact ringB.mul_mem (hφ_mem p) (ringB.pow_mem hinv_mem k)

private lemma finrank_le_of_span_range_eq_top {K L : Type*} [DivisionRing K] [AddCommGroup L]
    [Module K L] {n : ℕ} (v : Fin n → L) (h : Submodule.span K (Set.range v) = ⊤) :
    Module.finrank K L ≤ n := by
  classical
  have h1 : Module.finrank K (Submodule.span K (Set.range v)) ≤ (Finset.image v Finset.univ).card := by
    simpa using finrank_span_le_card (R := K) (Set.range v)
  rw [h, finrank_top] at h1
  exact le_trans h1 (by simpa using Finset.card_image_le (f := v) (s := Finset.univ))

private lemma intermediateField_le_of_finrank_le {F L : Type*} [Field F] [Field L] [Algebra F L]
    {K E : IntermediateField F L} (hKE : K ≤ E) [Module.Finite K L]
    (hfin : Module.finrank K L ≤ Module.finrank E L) (hposE : 0 < Module.finrank E L) :
    E ≤ K := by
  let : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  have : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite K E := Module.Finite.left K E L
  have : Module.Finite E L := Module.Finite.right K E L
  have htower := Module.finrank_mul_finrank K E L
  have hposKE : 0 < Module.finrank K E := Module.finrank_pos
  have hfinKE : Module.finrank K E = 1 := by nlinarith
  intro x hx
  have hspan : Submodule.span K {(1 : E)} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_singleton (one_ne_zero : (1 : E) ≠ 0), hfinKE]
  have hmem : (⟨x, hx⟩ : E) ∈ Submodule.span K {(1 : E)} := by
    rw [hspan]; trivial
  rw [Submodule.mem_span_singleton] at hmem
  rcases hmem with ⟨c, hc⟩
  have hval := congr_arg Subtype.val hc
  change (c : L) * 1 = x at hval
  rw [mul_one] at hval
  exact hval ▸ c.2

set_option maxRecDepth 4096 in
private lemma ringB_isFractionRing :
    ∀ x : EField, ∃ a b : ringB, b ≠ 0 ∧ x = (a : EField) / (b : EField) := by
  let KB : IntermediateField F47 LF :=
    IntermediateField.adjoin F47 ((Subtype.val : EField → LF) '' (ringB : Set EField))
  have hKB_le_E : KB ≤ EField := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hy1_47 : (yElem 1) ^ 47 ∈ KB := by
    have hmem : monomE (swanBasis 1) ∈ ringB := monomE_mem_ringB (swanBasis 1)
    have hval : (monomE (swanBasis 1) : LF) = (yElem 1) ^ 47 := by
      change ∏ a : Γ47, (yElem (a : ZMod 47)) ^ ((swanBasis 1).1 a) = (yElem 1) ^ 47
      rw [Finset.prod_eq_single (1 : Γ47)]
      · have h1 : (swanBasis 1).1 1 = 47 := by
          simp only [swanBasis, swanEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk, ↓reduceIte,
            Pi.single_eq_same, mul_one]
          have : ∑ b ∈ Finset.univ.erase (1 : Γ47), ((Pi.single (1 : Γ47) (1 : ℤ) : Γ47 → ℤ) b) * ((b : ZMod 47).val : ℤ) = 0 := by
            refine Finset.sum_eq_zero fun b hb => ?_
            simp [(Finset.mem_erase.mp hb).1]
          linarith
        rw [h1]
        simp
      · intro a _ ha
        have h0 : (swanBasis 1).1 a = 0 := by
          simp [swanBasis, swanEquiv, ha, Pi.single_apply]
        rw [h0, zpow_zero]
      · intro h; exact absurd (Finset.mem_univ 1) h
    rw [← hval]
    exact IntermediateField.subset_adjoin F47 _ ⟨monomE (swanBasis 1), hmem, rfl⟩
  have hyb_div : ∀ b : Γ47, b ≠ 1 → yElem (b : ZMod 47) / (yElem 1) ^ (b : ZMod 47).val ∈ KB := by
    intro b hb
    have hmem : monomE (swanBasis b) ∈ ringB := monomE_mem_ringB (swanBasis b)
    have hval : (monomE (swanBasis b) : LF) = yElem (b : ZMod 47) / (yElem 1) ^ (b : ZMod 47).val := by
      change ∏ a : Γ47, (yElem (a : ZMod 47)) ^ ((swanBasis b).1 a) = _
      have hb1 : (swanBasis b).1 1 = -((b : ZMod 47).val : ℤ) := by
        simp only [swanBasis, swanEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk, ↓reduceIte,
          Pi.single_apply, Ne.symm hb, mul_zero, zero_sub]
        rw [Finset.sum_eq_single b]
        · simp
        · intro a _ hab; simp [hab]
        · intro h; exact absurd (Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩) h
      have hbb : (swanBasis b).1 b = 1 := by
        simp [swanBasis, swanEquiv, hb, Pi.single_apply]
      have hother : ∀ a : Γ47, a ≠ 1 → a ≠ b → (swanBasis b).1 a = 0 := by
        intro a ha1 hab
        simp [swanBasis, swanEquiv, ha1, hab, Pi.single_apply]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (1 : Γ47))]
      rw [Finset.prod_eq_single b]
      · rw [hb1, hbb, zpow_one, zpow_neg, zpow_natCast, Units.val_one, mul_comm, div_eq_mul_inv]
      · intro a ha hab
        rw [hother a (Finset.mem_erase.mp ha).1 hab, zpow_zero]
      · intro h; exact absurd (Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩) h
    rw [← hval]
    exact IntermediateField.subset_adjoin F47 _ ⟨monomE (swanBasis b), hmem, rfl⟩
  let W : Submodule KB LF := Submodule.span KB (Set.range (fun k : Fin 47 => (yElem 1) ^ k.val))
  have hW_fin : Module.Finite KB W :=
    Module.Finite.span_of_finite KB (Set.finite_range _)
  have hW_pow : ∀ n : ℕ, (yElem 1) ^ n ∈ W := by
    intro n
    have hdiv : n = 47 * (n / 47) + n % 47 := (Nat.div_add_mod n 47).symm
    rw [hdiv, pow_add, pow_mul]
    have hmem : ((yElem 1) ^ 47) ^ (n / 47) ∈ KB := KB.toSubalgebra.pow_mem hy1_47 (n / 47)
    have hrem : (yElem 1) ^ (n % 47) ∈ W :=
      Submodule.subset_span ⟨⟨n % 47, Nat.mod_lt n (by norm_num)⟩, rfl⟩
    exact W.smul_mem ⟨_, hmem⟩ hrem
  have hW_mul : ∀ x ∈ W, ∀ y ∈ W, x * y ∈ W := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩ y hy
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨j, rfl⟩
        rw [← pow_add]
        exact hW_pow (i.val + j.val)
      · rw [mul_zero]; exact W.zero_mem
      · intro a b _ _ ha hb; rw [mul_add]; exact W.add_mem ha hb
      · intro c a _ ha
        change (yElem 1) ^ i.val * ((c : LF) * a) ∈ W
        rw [mul_left_comm]
        exact W.smul_mem c ha
    · intro y _; rw [zero_mul]; exact W.zero_mem
    · intro a b _ _ ha hb y hy; rw [add_mul]; exact W.add_mem (ha y hy) (hb y hy)
    · intro c a _ ha y hy
      change ((c : LF) * a) * y ∈ W
      rw [mul_assoc]
      exact W.smul_mem c (ha y hy)
  have hW_one : (1 : LF) ∈ W := by simpa using hW_pow 0
  have hW_inv : ∀ x ∈ W, x⁻¹ ∈ W := by
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    · let Lmul : W →ₗ[KB] W :=
        { toFun := fun w => ⟨x * w.1, hW_mul x hx w.1 w.2⟩
          map_add' := fun w₁ w₂ => Subtype.ext (mul_add x w₁.1 w₂.1)
          map_smul' := fun c w => Subtype.ext (by
            change x * ((c : LF) * w.1) = (c : LF) * (x * w.1); ring) }
      have hinj : Function.Injective Lmul := by
        intro w₁ w₂ hw
        exact Subtype.ext (mul_left_cancel₀ hx0 (congr_arg Subtype.val hw))
      have hsurj : Function.Surjective Lmul :=
        LinearMap.surjective_of_injective hinj
      obtain ⟨w, hw⟩ := hsurj ⟨1, hW_one⟩
      have hxw : x * w.1 = 1 := congr_arg Subtype.val hw
      have hinv : x⁻¹ = w.1 := inv_eq_of_mul_eq_one_right hxw
      rw [hinv]
      exact w.2
  have hW_yElem : ∀ a : ZMod 47, yElem a ∈ W := by
    intro a
    by_cases ha0 : a = 0
    · subst ha0
      have h0 : yElem 0 ∈ KB := IntermediateField.subset_adjoin F47 _ ⟨y0E, y0E_mem_ringB, rfl⟩
      have hm := W.smul_mem ⟨yElem 0, h0⟩ hW_one
      change (yElem 0) * 1 ∈ W at hm
      rwa [mul_one] at hm
    · let b : Γ47 := Units.mk0 a ha0
      by_cases hb1 : b = 1
      · have : a = 1 := by simpa [b] using congr_arg Units.val hb1
        subst this
        simpa using hW_pow 1
      · have hdiv := hyb_div b hb1
        have hpow := hW_pow (b : ZMod 47).val
        have heq : yElem a = (yElem (b : ZMod 47) / (yElem 1) ^ (b : ZMod 47).val) *
            (yElem 1) ^ (b : ZMod 47).val := by
          rw [div_mul_cancel₀ _ (pow_ne_zero _ (yElem_ne_zero 1))]
          rfl
        rw [heq]
        exact W.smul_mem ⟨_, hdiv⟩ hpow
  have hW_X : ∀ i : ZMod 47, algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X i) ∈ W := by
    intro i
    have hinv := congr_arg (algebraMap (MvPolynomial (ZMod 47) F47) LF) (fourier_inv_poly i)
    simp only [map_sum, map_mul] at hinv
    have hX : algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X i) =
        (algebraMap F47 LF (47 : F47)⁻¹) *
          ∑ a : ZMod 47, algebraMap F47 LF (zpow47 (a * i)) * yElem a := by
      have hinv' : ∑ a : ZMod 47, algebraMap F47 LF (zpow47 (a * i)) * yElem a =
          algebraMap F47 LF (47 : F47) * algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X i) := hinv
      rw [hinv', ← mul_assoc, ← map_mul, inv_mul_cancel₀ (by norm_num : (47 : F47) ≠ 0), map_one, one_mul]
    rw [hX]
    refine W.smul_mem ⟨_, KB.algebraMap_mem _⟩ (W.sum_mem fun a _ => ?_)
    exact W.smul_mem ⟨_, KB.algebraMap_mem _⟩ (hW_yElem a)
  have hW_poly : ∀ p : MvPolynomial (ZMod 47) F47,
      algebraMap (MvPolynomial (ZMod 47) F47) LF p ∈ W := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
      have hm := W.smul_mem ⟨algebraMap F47 LF c, KB.algebraMap_mem c⟩ hW_one
      change algebraMap F47 LF c * 1 ∈ W at hm
      rw [mul_one] at hm
      exact hm
    | add p₁ p₂ h₁ h₂ =>
      rw [map_add]; exact W.add_mem h₁ h₂
    | mul_X p i hp =>
      rw [map_mul]; exact hW_mul _ hp _ (hW_X i)
  have hW_top : W = ⊤ := by
    rw [eq_top_iff]
    intro z _
    induction z using Localization.induction_on with
    | H a =>
      rcases a with ⟨p, q⟩
      rw [frac_mk_eq_div, div_eq_mul_inv]
      exact hW_mul _ (hW_poly p) _ (hW_inv _ (hW_poly q))
  have hfin_KB_LF : Module.finrank KB LF ≤ 47 :=
    finrank_le_of_span_range_eq_top (fun k : Fin 47 => (yElem 1) ^ k.val) hW_top
  have hinj_shift : Function.Injective shiftFHom := by
    intro k₁ k₂ hk
    have hy := AlgEquiv.congr_fun hk (yElem 1)
    simp only [shiftFHom, MonoidHom.coe_mk, OneHom.coe_mk, shiftF_yElem, one_mul] at hy
    have hz := mul_right_cancel₀ (yElem_ne_zero 1) hy
    have hz' : zpow47 (Multiplicative.toAdd k₁) = zpow47 (Multiplicative.toAdd k₂) :=
      (algebraMap F47 LF).injective hz
    have hsub : zpow47 (Multiplicative.toAdd k₁ - Multiplicative.toAdd k₂) = 1 := by
      rw [sub_eq_add_neg, zpow47_add, zpow47_neg, hz', mul_inv_cancel₀ (zpow47_ne_zero _)]
    have heq := sub_eq_zero.mp ((zpow47_eq_one_iff _).mp hsub)
    exact Multiplicative.toAdd.injective heq
  have hequiv_HF : Multiplicative (ZMod 47) ≃ HF := Equiv.ofBijective
    (fun k => ⟨shiftFHom k, ⟨k, rfl⟩⟩)
    ⟨fun k₁ k₂ h => hinj_shift (congr_arg Subtype.val h), fun ⟨_, k, hk⟩ => ⟨k, Subtype.ext hk⟩⟩
  let : Fintype HF := Fintype.ofEquiv (Multiplicative (ZMod 47)) hequiv_HF
  have hHF_card : Fintype.card HF = 47 := by
    rw [← Fintype.card_congr hequiv_HF]
    simp [ZMod.card]
  have hfin_E_LF : Module.finrank EField LF = 47 := by
    have h := FixedPoints.finrank_eq_card HF LF
    rw [hHF_card] at h
    exact h
  have : Module.Finite KB LF :=
    Module.Finite.of_fg_top (hW_top ▸ Submodule.fg_span (Set.finite_range _))
  have hE_le_KB : EField ≤ KB :=
    intermediateField_le_of_finrank_le hKB_le_E (by linarith) (by linarith)
  let FracB : IntermediateField F47 LF :=
    { carrier := { z : LF | ∃ a b : ringB, b ≠ 0 ∧ z = (a : LF) / (b : LF) }
      mul_mem' := by
        rintro _ _ ⟨a₁, b₁, hb₁, rfl⟩ ⟨a₂, b₂, hb₂, rfl⟩
        exact ⟨a₁ * a₂, b₁ * b₂, mul_ne_zero hb₁ hb₂, by simp [div_mul_div_comm]⟩
      one_mem' := ⟨1, 1, one_ne_zero, by simp⟩
      add_mem' := by
        rintro _ _ ⟨a₁, b₁, hb₁, rfl⟩ ⟨a₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂, mul_ne_zero hb₁ hb₂, ?_⟩
        have hb1' : (b₁ : LF) ≠ 0 := fun h => hb₁ (Subtype.ext (Subtype.ext h))
        have hb2' : (b₂ : LF) ≠ 0 := fun h => hb₂ (Subtype.ext (Subtype.ext h))
        simp only [Subalgebra.coe_add, Subalgebra.coe_mul, IntermediateField.coe_add,
          IntermediateField.coe_mul]
        field_simp
      zero_mem' := ⟨0, 1, one_ne_zero, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, b, hb, rfl⟩
        by_cases ha : a = 0
        · subst ha; exact ⟨0, 1, one_ne_zero, by simp⟩
        · exact ⟨b, a, ha, by simp [inv_div]⟩
      algebraMap_mem' := fun c => ⟨algebraMap F47 ringB c, 1, one_ne_zero, by simp⟩ }
  have hKB_le_FracB : KB ≤ FracB := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, 1, one_ne_zero, by simp⟩
  intro x
  have hxKB : (x : LF) ∈ KB := hE_le_KB x.2
  rcases hKB_le_FracB hxKB with ⟨a, b, hb, hval⟩
  exact ⟨a, b, hb, Subtype.ext hval⟩

set_option maxRecDepth 4096 in
private lemma ringB_unit_decomp (u : ringBˣ) :
    ∃ (c : F47ˣ) (w : SwanIdeal), (u : EField) = algebraMap F47 EField c * monomE w := by
  rcases u.1.2 with ⟨p, k, hp⟩
  rcases u.2.2 with ⟨q, n, hq⟩
  have h1 : (u.1 : EField) * (u.2 : EField) = 1 :=
    congr_arg (fun z : ringB => (z : EField)) u.mul_inv
  rw [hp, hq] at h1
  have ht_ne : (φB tB) ^ k ≠ 0 := pow_ne_zero k φB_tB_ne_zero
  have ht_ne2 : (φB tB) ^ n ≠ 0 := pow_ne_zero n φB_tB_ne_zero
  have hpq : φB (p * q) = φB (tB ^ (k + n)) := by
    rw [map_mul, map_pow, pow_add]
    have h2 : φB p * φB q / ((φB tB) ^ k * (φB tB) ^ n) = 1 := by
      simpa [div_mul_div_comm] using h1
    exact (div_eq_one_iff_eq (mul_ne_zero ht_ne ht_ne2)).mp h2
  have hpq' : p * q = tB ^ (k + n) := φB_injective hpq
  have hdvd : p ∣ ∏ b : Γ47, (MvPolynomial.X (some b) : PB) ^ (k + n) := by
    refine ⟨q, ?_⟩
    rw [hpq', tB, Finset.prod_pow]
  have hp0 : p ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hpq'
    have : φB (tB ^ (k + n)) = 0 := by rw [← hpq', map_zero]
    rw [map_pow] at this
    exact pow_ne_zero (k + n) φB_tB_ne_zero this
  have hX_prime : ∀ b : Γ47, Prime (MvPolynomial.X (some b) : PB) := by
    intro b
    have hker : ∀ r s : PB, (MvPolynomial.X (some b) : PB) ∣ r * s →
        (MvPolynomial.X (some b) : PB) ∣ r ∨ (MvPolynomial.X (some b) : PB) ∣ s := by
      intro r s hrs
      let ev : PB →ₐ[F47] PB := MvPolynomial.aeval (fun o => if o = some b then 0 else MvPolynomial.X o)
      have hev_dvd : ∀ f : PB, (MvPolynomial.X (some b) : PB) ∣ f ↔ ev f = 0 := by
        intro f
        constructor
        · rintro ⟨g, rfl⟩
          simp [ev]
        · intro hf0
          have hzero : ∀ d : Option Γ47 →₀ ℕ, d (some b) = 0 → MvPolynomial.coeff d f = 0 := by
            intro d hd0
            have hcoeff := congr_arg (MvPolynomial.coeff d) hf0
            rw [MvPolynomial.coeff_zero] at hcoeff
            have hev_f : MvPolynomial.coeff d (ev f) = MvPolynomial.coeff d f := by
              conv_lhs => rw [MvPolynomial.as_sum f]
              rw [map_sum, MvPolynomial.coeff_sum]
              rw [Finset.sum_eq_single d]
              · by_cases hds : d ∈ f.support
                · rw [MvPolynomial.monomial_eq, map_mul, Finsupp.prod, map_prod]
                  have hprod : ∏ x ∈ d.support, (ev (MvPolynomial.X x)) ^ d x =
                      ∏ x ∈ d.support, (MvPolynomial.X x : PB) ^ d x := by
                    refine Finset.prod_congr rfl fun x hx => ?_
                    have hne : x ≠ some b := by
                      intro heq; subst heq
                      exact (Finsupp.mem_support_iff.mp hx) hd0
                    simp [ev, hne]
                  simp only [map_pow] at hprod ⊢
                  rw [hprod, show ev (MvPolynomial.C (MvPolynomial.coeff d f)) =
                    MvPolynomial.C (MvPolynomial.coeff d f) from ev.commutes _,
                    ← Finsupp.prod, ← MvPolynomial.monomial_eq, MvPolynomial.coeff_monomial,
                    if_pos rfl]
                · simp [MvPolynomial.notMem_support_iff.mp hds]
              · intro d' hd' hne
                rw [MvPolynomial.monomial_eq, map_mul, Finsupp.prod, map_prod]
                by_cases hb' : some b ∈ d'.support
                · have h0 : ∏ x ∈ d'.support, (ev (MvPolynomial.X x)) ^ d' x = 0 := by
                    apply Finset.prod_eq_zero hb'
                    simp [ev, zero_pow (Finsupp.mem_support_iff.mp hb')]
                  simp [map_pow, h0]
                · have hprod : ∏ x ∈ d'.support, (ev (MvPolynomial.X x)) ^ d' x =
                      ∏ x ∈ d'.support, (MvPolynomial.X x : PB) ^ d' x := by
                    refine Finset.prod_congr rfl fun x hx => ?_
                    have hne' : x ≠ some b := fun heq => hb' (heq ▸ hx)
                    simp [ev, hne']
                  simp only [map_pow] at hprod ⊢
                  rw [hprod, show ev (MvPolynomial.C (MvPolynomial.coeff d' f)) =
                    MvPolynomial.C (MvPolynomial.coeff d' f) from ev.commutes _,
                    ← Finsupp.prod, ← MvPolynomial.monomial_eq, MvPolynomial.coeff_monomial,
                    if_neg hne]
              · intro h
                simp [MvPolynomial.notMem_support_iff.mp h]
            rw [← hev_f, hcoeff]
          refine ⟨∑ d ∈ f.support, MvPolynomial.monomial (d - Finsupp.single (some b) 1) (MvPolynomial.coeff d f), ?_⟩
          rw [Finset.mul_sum]
          conv_lhs => rw [MvPolynomial.as_sum f]
          refine Finset.sum_congr rfl fun d hd => ?_
          have hpos : 0 < d (some b) := Nat.pos_of_ne_zero fun h0 =>
            (MvPolynomial.mem_support_iff.mp hd) (hzero d h0)
          rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]
          have hd_eq : d = Finsupp.single (some b) 1 + (d - Finsupp.single (some b) 1) := by
            ext o
            by_cases ho : o = some b
            · subst ho; simp; omega
            · simp [ho]
          rw [← hd_eq]
      rw [hev_dvd, map_mul, mul_eq_zero] at hrs
      rw [hev_dvd, hev_dvd]
      exact hrs
    refine ⟨MvPolynomial.X_ne_zero _, ?_, hker⟩
    intro hu
    rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced] at hu
    rcases hu with ⟨c, _, hc⟩
    have h1 := congr_arg (MvPolynomial.coeff (Finsupp.single (some b) 1)) hc
    rw [MvPolynomial.coeff_X, MvPolynomial.coeff_C, if_pos rfl, if_neg] at h1
    · exact one_ne_zero h1
    · intro h0
      have := congr_arg (fun f : Option Γ47 →₀ ℕ => f (some b)) h0
      simp at this
  have hexp : ∃ e : Γ47 → ℕ, Associated p (∏ b : Γ47, (MvPolynomial.X (some b) : PB) ^ (e b)) := by
    have hfac : Associated (UniqueFactorizationMonoid.factors p).prod p :=
      UniqueFactorizationMonoid.factors_prod hp0
    have hmem : ∀ q ∈ UniqueFactorizationMonoid.factors p,
        ∃ b : Γ47, Associated q (MvPolynomial.X (some b) : PB) := by
      intro q hq
      have hq_irred : Irreducible q := UniqueFactorizationMonoid.irreducible_of_factor q hq
      have hq_prime : Prime q := UniqueFactorizationMonoid.irreducible_iff_prime.mp hq_irred
      have hq_dvd_p : q ∣ p :=
        dvd_trans (Multiset.dvd_prod hq) hfac.dvd
      have hq_dvd : q ∣ ∏ b : Γ47, (MvPolynomial.X (some b) : PB) ^ (k + n) :=
        dvd_trans hq_dvd_p hdvd
      obtain ⟨b, _, hqb⟩ := hq_prime.dvd_finsetProd_iff _ |>.mp hq_dvd
      have hqb' : q ∣ MvPolynomial.X (some b) := hq_prime.dvd_of_dvd_pow hqb
      exact ⟨b, associated_of_dvd_dvd hqb' (hq_irred.dvd_symm (hX_prime b).irreducible hqb')⟩
    have hms : ∀ s : Multiset PB, (∀ q ∈ s, ∃ b : Γ47, Associated q (MvPolynomial.X (some b) : PB)) →
        ∃ e : Γ47 → ℕ, Associated s.prod (∏ b : Γ47, (MvPolynomial.X (some b) : PB) ^ (e b)) := by
      intro s
      induction s using Multiset.induction with
      | empty =>
        intro _
        exact ⟨0, by simp⟩
      | cons q s ih =>
        intro hs
        obtain ⟨b₀, hb₀⟩ := hs q (Multiset.mem_cons_self q s)
        obtain ⟨e, he⟩ := ih fun r hr => hs r (Multiset.mem_cons_of_mem hr)
        let e' : Γ47 → ℕ := fun b => if b = b₀ then e b + 1 else e b
        refine ⟨e', ?_⟩
        rw [Multiset.prod_cons]
        have hprod : ∏ b : Γ47, (MvPolynomial.X (some b) : PB) ^ (e' b) =
            (MvPolynomial.X (some b₀) : PB) * ∏ b : Γ47, (MvPolynomial.X (some b) : PB) ^ (e b) := by
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ b₀),
            ← Finset.mul_prod_erase _ _ (Finset.mem_univ b₀), ← mul_assoc]
          congr 1
          · simp [e', pow_succ']
          · refine Finset.prod_congr rfl fun b hb => ?_
            simp [e', (Finset.mem_erase.mp hb).1]
        rw [hprod]
        exact hb₀.mul_mul he
    obtain ⟨e, he⟩ := hms (UniqueFactorizationMonoid.factors p) hmem
    exact ⟨e, hfac.symm.trans he⟩
  rcases hexp with ⟨e, he⟩
  rcases he with ⟨up, hup⟩
  have hup_unit : IsUnit (up : PB) := up.isUnit
  rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced] at hup_unit
  rcases hup_unit with ⟨c0, hc0_unit, hc0⟩
  rcases hc0_unit with ⟨c, rfl⟩
  refine ⟨c⁻¹, swanEquiv (fun b => (e b : ℤ) - (k : ℤ)), ?_⟩
  have hp_eq : p = MvPolynomial.C ((c⁻¹ : F47ˣ) : F47) * ∏ b : Γ47, (MvPolynomial.X (some b) : PB) ^ (e b) := by
    have h1 : p * MvPolynomial.C (c : F47) = ∏ b : Γ47, (MvPolynomial.X (some b) : PB) ^ (e b) := by
      simpa [← hc0] using hup
    calc p = p * (MvPolynomial.C (c : F47) * MvPolynomial.C ((c⁻¹ : F47ˣ) : F47)) := by
          rw [← map_mul, Units.mul_inv, map_one, mul_one]
      _ = (p * MvPolynomial.C (c : F47)) * MvPolynomial.C ((c⁻¹ : F47ˣ) : F47) := by ring
      _ = MvPolynomial.C ((c⁻¹ : F47ˣ) : F47) * ∏ b : Γ47, (MvPolynomial.X (some b) : PB) ^ (e b) := by
          rw [h1, mul_comm]
  have hφC : φB (MvPolynomial.C ((c⁻¹ : F47ˣ) : F47)) = algebraMap F47 EField (c⁻¹ : F47ˣ) :=
    φB.commutes _
  rw [hp, hp_eq, map_mul, hφC, mul_div_assoc]
  congr 1
  simp only [map_prod, map_pow, φB_X_some, tB]
  rw [← Finset.prod_pow, ← Finset.prod_div_distrib]
  have hmon : monomE (swanEquiv (fun b => (e b : ℤ) - (k : ℤ))) =
      ∏ b : Γ47, (monomE (swanBasis b)) ^ ((e b : ℤ) - (k : ℤ)) := by
    rw [swanEquiv_eq_sum]
    have hsum : ∀ s : Finset Γ47,
        monomE (∑ b ∈ s, ((e b : ℤ) - (k : ℤ)) • swanBasis b) =
          ∏ b ∈ s, (monomE (swanBasis b)) ^ ((e b : ℤ) - (k : ℤ)) := by
      intro s
      induction s using Finset.cons_induction with
      | empty => simp [monomE_zero]
      | cons b s hb ih =>
        rw [Finset.sum_cons, Finset.prod_cons, monomE_add, ih]
        congr 1
        have hz : ∀ m : ℤ, monomE (m • swanBasis b) = (monomE (swanBasis b)) ^ m := by
          intro m
          induction m with
          | zero => simp [monomE_zero]
          | succ j ihj => rw [add_smul, one_smul, monomE_add, ihj, zpow_add_one₀ (monomE_ne_zero _)]
          | pred j ihj =>
            rw [sub_smul, one_smul, sub_eq_add_neg, monomE_add, monomE_neg, ihj,
              zpow_sub_one₀ (monomE_ne_zero _)]
        exact hz _
    exact hsum Finset.univ
  rw [hmon]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, zpow_sub₀ (monomE_ne_zero _)]

private lemma monomE_eq_algebraMap_iff (u : SwanIdeal) (c : F47) :
    monomE u = algebraMap F47 EField c → u = 0 := by
  intro h
  have hL : fourierFracEquiv.symm (monomL u) = algebraMap F47 LF c := by
    have hval : monomL u = algebraMap F47 LF c := congr_arg Subtype.val h
    rw [hval]
    exact fourierFracEquiv.symm.commutes c
  have hmonL : fourierFracEquiv.symm (monomL u) =
      ∏ a : Γ47, (algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X (a : ZMod 47))) ^ (u.1 a) := by
    simp only [monomL, map_prod, map_zpow₀]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← fourierFracEquiv_X (a : ZMod 47), AlgEquiv.symm_apply_apply]
  rw [hmonL] at hL
  let N : ℕ := Finset.univ.sup (fun a : Γ47 => (u.1 a).natAbs)
  have hN : ∀ a : Γ47, 0 ≤ u.1 a + (N : ℤ) := fun a => by
    have hle : (u.1 a).natAbs ≤ N :=
      Finset.le_sup (f := fun a : Γ47 => (u.1 a).natAbs) (Finset.mem_univ a)
    omega
  have hXne : ∀ a : ZMod 47, algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X a) ≠ 0 := by
    intro a h0
    exact MvPolynomial.X_ne_zero a (IsFractionRing.injective _ _ (by rw [h0, map_zero]))
  let d1 : ZMod 47 →₀ ℕ := Finsupp.equivFunOnFinite.symm
    (fun a => if ha : a = 0 then 0 else (u.1 (Units.mk0 a ha) + (N : ℤ)).toNat)
  let d2 : ZMod 47 →₀ ℕ := Finsupp.equivFunOnFinite.symm
    (fun a => if a = 0 then 0 else N)
  have hd1_app : ∀ a, d1 a = if ha : a = 0 then 0 else (u.1 (Units.mk0 a ha) + (N : ℤ)).toNat := fun _ => rfl
  have hd2_app : ∀ a, d2 a = if a = 0 then 0 else N := fun _ => rfl
  have hpoly : MvPolynomial.monomial d1 (1 : F47) = MvPolynomial.monomial d2 c := by
    apply IsFractionRing.injective (MvPolynomial (ZMod 47) F47) LF
    have hmul := congr_arg (fun z =>
      (∏ a : Γ47, (algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X (a : ZMod 47))) ^ N) * z) hL
    have h1 : algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.monomial d1 1) =
        (∏ a : Γ47, (algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X (a : ZMod 47))) ^ N) *
          ∏ a : Γ47, (algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X (a : ZMod 47))) ^ (u.1 a) := by
      rw [MvPolynomial.monomial_eq, map_mul, map_one, map_one, one_mul, Finsupp.prod, map_prod]
      have hfull : ∏ x ∈ d1.support, (algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X x)) ^ d1 x =
          ∏ a : ZMod 47, (algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X a)) ^ d1 a := by
        apply Finset.prod_subset (Finset.subset_univ _)
        intro a _ ha
        rw [Finsupp.notMem_support_iff.mp ha, pow_zero]
      simp only [map_pow]
      rw [hfull, ← Finset.mul_prod_erase _ _ (Finset.mem_univ (0 : ZMod 47))]
      have hd10 : d1 0 = 0 := by rw [hd1_app]; simp
      rw [hd10, pow_zero, one_mul, ← Finset.prod_mul_distrib]
      symm
      refine Finset.prod_bij (fun (b : Γ47) _ => (b : ZMod 47))
        (fun b _ => Finset.mem_erase.mpr ⟨b.ne_zero, Finset.mem_univ _⟩)
        (fun b₁ _ b₂ _ h => Units.ext h)
        (fun a ha => ⟨Units.mk0 a (Finset.mem_erase.mp ha).1, Finset.mem_univ _, rfl⟩)
        (fun b _ => ?_)
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hXne _)]
      congr 1
      rw [hd1_app]
      simp only [b.ne_zero, ↓reduceDIte, Units.mk0_val]
      have hnn := Int.toNat_of_nonneg (hN b)
      linarith
    have h2 : algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.monomial d2 c) =
        (∏ a : Γ47, (algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X (a : ZMod 47))) ^ N) *
          algebraMap F47 LF c := by
      rw [MvPolynomial.monomial_eq, map_mul, Finsupp.prod, map_prod, mul_comm]
      congr 1
      have hfull : ∏ x ∈ d2.support, (algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X x)) ^ d2 x =
          ∏ a : ZMod 47, (algebraMap (MvPolynomial (ZMod 47) F47) LF (MvPolynomial.X a)) ^ d2 a := by
        apply Finset.prod_subset (Finset.subset_univ _)
        intro a _ ha
        rw [Finsupp.notMem_support_iff.mp ha, pow_zero]
      simp only [map_pow]
      rw [hfull, ← Finset.mul_prod_erase _ _ (Finset.mem_univ (0 : ZMod 47))]
      have hd20 : d2 0 = 0 := by rw [hd2_app]; simp
      rw [hd20, pow_zero, one_mul]
      symm
      refine Finset.prod_bij (fun (b : Γ47) _ => (b : ZMod 47))
        (fun b _ => Finset.mem_erase.mpr ⟨b.ne_zero, Finset.mem_univ _⟩)
        (fun b₁ _ b₂ _ h => Units.ext h)
        (fun a ha => ⟨Units.mk0 a (Finset.mem_erase.mp ha).1, Finset.mem_univ _, rfl⟩)
        (fun b _ => by rw [hd2_app]; simp [b.ne_zero])
    rw [h1, h2]
    exact hmul
  have hd12 : d1 = d2 := by
    by_contra hne
    have h1 := congr_arg (MvPolynomial.coeff d1) hpoly
    simp [MvPolynomial.coeff_monomial, Ne.symm hne] at h1
  ext a
  have ha := congr_arg (fun f : ZMod 47 →₀ ℕ => f (a : ZMod 47)) hd12
  rw [hd1_app, hd2_app] at ha
  simp only [a.ne_zero, ↓reduceDIte, ↓reduceIte, Units.mk0_val] at ha
  have hnn := Int.toNat_of_nonneg (hN a)
  change u.1 a = 0
  omega

private lemma ringB_ufm : UniqueFactorizationMonoid ringB := by
  apply UniqueFactorizationMonoid.of_exists_prime_factors
  intro x hx
  rcases x.2 with ⟨p, k, hp⟩
  have hp0 : p ≠ 0 := by
    intro h0
    apply hx
    apply Subtype.ext
    rw [hp, h0, map_zero, zero_div]
    rfl
  let emb : PB →+* ringB :=
    { toFun := fun q => ⟨φB q, q, 0, by simp⟩
      map_one' := Subtype.ext (map_one φB)
      map_mul' := fun q₁ q₂ => Subtype.ext (map_mul φB q₁ q₂)
      map_zero' := Subtype.ext (map_zero φB)
      map_add' := fun q₁ q₂ => Subtype.ext (map_add φB q₁ q₂) }
  have hemb_inj : Function.Injective emb := fun q₁ q₂ h =>
    φB_injective (congr_arg Subtype.val h)
  have ht_unit : IsUnit (emb tB) := by
    refine ⟨⟨emb tB, ⟨(φB tB)⁻¹, 1, 1, by simp⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext; exact mul_inv_cancel₀ φB_tB_ne_zero
    · apply Subtype.ext; exact inv_mul_cancel₀ φB_tB_ne_zero
  have hprime_stay : ∀ q : PB, Prime q → ¬ q ∣ tB → Prime (emb q) := by
    intro q hq hndvd
    refine ⟨fun h0 => hq.ne_zero (hemb_inj (by simpa using h0)), ?_, ?_⟩
    · intro hunit
      rcases hunit with ⟨u, hu⟩
      rcases u.2.2 with ⟨r, m, hr⟩
      have h1 : φB q * (φB r / (φB tB) ^ m) = 1 := by
        have hmul := congr_arg (fun z : ringB => (z : EField)) u.mul_inv
        change (u.1 : EField) * (u.2 : EField) = 1 at hmul
        rw [hu, hr] at hmul
        exact hmul
      have h2 : φB (q * r) = φB (tB ^ m) := by
        rw [map_mul, map_pow]
        rw [← mul_div_assoc] at h1
        exact (div_eq_one_iff_eq (pow_ne_zero m φB_tB_ne_zero)).mp h1
      have hqdvd : q ∣ tB ^ m := ⟨r, (φB_injective h2).symm⟩
      exact hndvd (hq.dvd_of_dvd_pow hqdvd)
    · intro a b hab
      rcases a.2 with ⟨pa, ka, ha⟩
      rcases b.2 with ⟨pb, kb, hb⟩
      rcases hab with ⟨c, hc⟩
      rcases c.2 with ⟨pc, kc, hcv⟩
      have hval := congr_arg Subtype.val hc
      change (a : EField) * (b : EField) = φB q * (c : EField) at hval
      rw [ha, hb, hcv] at hval
      have hne1 : (φB tB) ^ ka ≠ 0 := pow_ne_zero ka φB_tB_ne_zero
      have hne2 : (φB tB) ^ kb ≠ 0 := pow_ne_zero kb φB_tB_ne_zero
      have hne3 : (φB tB) ^ kc ≠ 0 := pow_ne_zero kc φB_tB_ne_zero
      have heqE : φB (pa * pb * tB ^ kc) = φB (q * pc * tB ^ (ka + kb)) := by
        simp only [map_mul, map_pow, pow_add]
        have h3 : φB pa * φB pb / ((φB tB) ^ ka * (φB tB) ^ kb) =
            φB q * φB pc / (φB tB) ^ kc := by
          simpa [div_mul_div_comm, mul_div_assoc] using hval
        have h4 : φB pa * φB pb * (φB tB) ^ kc =
            φB q * φB pc * ((φB tB) ^ ka * (φB tB) ^ kb) := by
          field_simp at h3
          linear_combination h3
        exact h4
      have hqdvd : q ∣ pa * pb * tB ^ kc := ⟨pc * tB ^ (ka + kb), by
        have h5 := φB_injective heqE
        rw [h5]; ring⟩
      have hqdvd' : q ∣ pa * pb := by
        rcases hq.dvd_or_dvd hqdvd with h1 | h2
        · exact h1
        · exact absurd (hq.dvd_of_dvd_pow h2) hndvd
      rcases hq.dvd_or_dvd hqdvd' with ⟨r, rfl⟩ | ⟨r, rfl⟩
      · left
        refine ⟨⟨φB r / (φB tB) ^ ka, r, ka, rfl⟩, Subtype.ext ?_⟩
        change (a : EField) = φB q * (φB r / (φB tB) ^ ka)
        rw [ha, map_mul, mul_div_assoc]
      · right
        refine ⟨⟨φB r / (φB tB) ^ kb, r, kb, rfl⟩, Subtype.ext ?_⟩
        change (b : EField) = φB q * (φB r / (φB tB) ^ kb)
        rw [hb, map_mul, mul_div_assoc]
  let f := UniqueFactorizationMonoid.factors p
  have hf_prod : Associated f.prod p := UniqueFactorizationMonoid.factors_prod hp0
  classical
  let f' := f.filter (fun q => ¬ q ∣ tB)
  refine ⟨f'.map emb, ?_, ?_⟩
  · intro r hr
    rcases Multiset.mem_map.mp hr with ⟨q, hq, rfl⟩
    have hq_mem : q ∈ f := (Multiset.mem_filter.mp hq).1
    have hq_ndvd : ¬ q ∣ tB := (Multiset.mem_filter.mp hq).2
    have hq_prime : Prime q :=
      UniqueFactorizationMonoid.irreducible_iff_prime.mp
        (UniqueFactorizationMonoid.irreducible_of_factor q hq_mem)
    exact hprime_stay q hq_prime hq_ndvd
  · have hsplit : f = f' + f.filter (fun q => q ∣ tB) := by
      simpa [f'] using (Multiset.filter_add_not (fun q : PB => ¬ q ∣ tB) f).symm
    have hunit_rest : IsUnit (emb (f.filter (fun q => q ∣ tB)).prod) := by
      rw [map_multiset_prod]
      have hprod_u : ∀ s : Multiset ringB, (∀ r ∈ s, IsUnit r) → IsUnit s.prod := by
        intro s
        induction s using Multiset.induction with
        | empty => intro _; exact isUnit_one
        | cons r s ih =>
          intro hs
          rw [Multiset.prod_cons]
          exact (hs r (Multiset.mem_cons_self r s)).mul (ih fun z hz => hs z (Multiset.mem_cons_of_mem hz))
      apply hprod_u
      intro r hr
      rcases Multiset.mem_map.mp hr with ⟨q, hq, rfl⟩
      exact isUnit_of_dvd_unit (map_dvd emb (Multiset.mem_filter.mp hq).2) ht_unit
    have h1 : Associated (f'.map emb).prod (emb f.prod) := by
      rw [← map_multiset_prod, hsplit, Multiset.prod_add, map_mul]
      exact associated_mul_unit_right (emb f'.prod) _ hunit_rest
    have h2 : Associated (emb f.prod) (emb p) := hf_prod.map emb.toMonoidHom
    have h3 : Associated (emb p) x := by
      have hpow_unit : IsUnit ((emb tB) ^ k) := ht_unit.pow k
      rcases hpow_unit with ⟨u, hu⟩
      refine ⟨u⁻¹, Subtype.ext ?_⟩
      change φB p * ((u⁻¹ : ringBˣ) : EField) = (x : EField)
      have huE : (u : EField) = (φB tB) ^ k := by
        have := congr_arg (fun z : ringB => (z : EField)) hu
        simpa [emb] using this
      have huinv : ((u⁻¹ : ringBˣ) : EField) = ((φB tB) ^ k)⁻¹ := by
        apply eq_inv_of_mul_eq_one_right
        rw [← huE]
        exact congr_arg (fun z : ringB => (z : EField)) u.mul_inv
      rw [huinv, ← div_eq_mul_inv, ← hp]
    exact (h1.trans h2).trans h3

/- Section 6: Finite ι', ring A, and common Γ47-invariant localization A[s⁻¹] = B[r'⁻¹] -/

private lemma aeval_zero_eq_self_of_notMem_vars {K ι' : Type*} [CommSemiring K] [DecidableEq ι']
    (j : ι') (r : MvPolynomial ι' K) (hr : j ∉ r.vars) :
    MvPolynomial.aeval (fun i => if i = j then (0 : MvPolynomial ι' K) else MvPolynomial.X i) r = r := by
  conv_lhs => rw [MvPolynomial.as_sum r]
  conv_rhs => rw [MvPolynomial.as_sum r]
  rw [map_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [MvPolynomial.monomial_eq, map_mul, Finsupp.prod, map_prod, MvPolynomial.aeval_C]
  refine congr_arg₂ (· * ·) rfl ?_
  refine Finset.prod_congr rfl fun i hi => ?_
  have hij : i ≠ j := by
    intro h; subst i
    exact hr ((MvPolynomial.mem_vars_iff_mem_support j).mpr ⟨d, hd, hi⟩)
  rw [map_pow, MvPolynomial.aeval_X, if_neg hij]

private lemma mem_finset_of_X_eq_div {K : Type*} [Field K] {ι' : Type*}
    (S : Finset ι') (j : ι') (p q : MvPolynomial ι' K) (hq : q ≠ 0)
    (hpv : p.vars ⊆ S)
    (hXj : algebraMap (MvPolynomial ι' K) (FractionRing (MvPolynomial ι' K)) (MvPolynomial.X j) =
      algebraMap (MvPolynomial ι' K) _ p / algebraMap (MvPolynomial ι' K) _ q) :
    j ∈ S := by
  classical
  by_contra hj
  have hq0 : algebraMap (MvPolynomial ι' K) (FractionRing (MvPolynomial ι' K)) q ≠ 0 := fun h0 =>
    hq (IsFractionRing.injective _ _ (by rw [h0, map_zero]))
  have hmul : MvPolynomial.X j * q = p := by
    apply IsFractionRing.injective (MvPolynomial ι' K) (FractionRing (MvPolynomial ι' K))
    rw [map_mul, hXj, div_mul_cancel₀ _ hq0]
  have hp_fix : MvPolynomial.aeval (R := K) (fun i => if i = j then (0 : MvPolynomial ι' K) else MvPolynomial.X i) p = p :=
    aeval_zero_eq_self_of_notMem_vars j p (fun h => hj (hpv h))
  have hevX : MvPolynomial.aeval (R := K) (fun i => if i = j then (0 : MvPolynomial ι' K) else MvPolynomial.X i) (MvPolynomial.X j) = 0 := by
    rw [MvPolynomial.aeval_X, if_pos rfl]
  have h0 : p = 0 := by
    rw [← hp_fix, ← hmul, map_mul, hevX, zero_mul]
  rw [h0] at hmul
  exact hq ((mul_eq_zero.mp hmul).resolve_left (MvPolynomial.X_ne_zero j))

private lemma finite_of_finset_gen {K : Type} [Field K] {ι' : Type}
    (gens : Finset (FractionRing (MvPolynomial ι' K)))
    (hgen : ∀ (L : IntermediateField K (FractionRing (MvPolynomial ι' K))),
      (∀ x ∈ gens, x ∈ L) → ∀ z, z ∈ L) : Finite ι' := by
  classical
  have hrep : ∀ g : FractionRing (MvPolynomial ι' K), ∃ p q : MvPolynomial ι' K, q ≠ 0 ∧
      g = algebraMap (MvPolynomial ι' K) _ p / algebraMap (MvPolynomial ι' K) _ q := by
    intro g
    induction g using Localization.induction_on with
    | H a =>
      rcases a with ⟨p, q⟩
      exact ⟨p, q, nonZeroDivisors.ne_zero q.2, frac_mk_eq_div p q⟩
  choose pG qG hqG hΦG using hrep
  let S : Finset ι' := gens.biUnion (fun g => (pG g).vars ∪ (qG g).vars)
  let KS : IntermediateField K (FractionRing (MvPolynomial ι' K)) :=
    { carrier := { z | ∃ p q : MvPolynomial ι' K, q ≠ 0 ∧ p.vars ⊆ S ∧ q.vars ⊆ S ∧
        z = algebraMap (MvPolynomial ι' K) _ p / algebraMap (MvPolynomial ι' K) _ q }
      mul_mem' := by
        rintro _ _ ⟨p₁, q₁, hq₁, hp₁, hq₁v, rfl⟩ ⟨p₂, q₂, hq₂, hp₂, hq₂v, rfl⟩
        exact ⟨p₁ * p₂, q₁ * q₂, mul_ne_zero hq₁ hq₂,
          Finset.Subset.trans (MvPolynomial.vars_mul _ _) (Finset.union_subset hp₁ hp₂),
          Finset.Subset.trans (MvPolynomial.vars_mul _ _) (Finset.union_subset hq₁v hq₂v),
          by simp [div_mul_div_comm]⟩
      one_mem' := ⟨1, 1, one_ne_zero, by simp, by simp, by simp⟩
      add_mem' := by
        rintro _ _ ⟨p₁, q₁, hq₁, hp₁, hq₁v, rfl⟩ ⟨p₂, q₂, hq₂, hp₂, hq₂v, rfl⟩
        refine ⟨p₁ * q₂ + p₂ * q₁, q₁ * q₂, mul_ne_zero hq₁ hq₂, ?_, ?_, ?_⟩
        · exact Finset.Subset.trans (MvPolynomial.vars_add_subset _ _)
            (Finset.union_subset
              (Finset.Subset.trans (MvPolynomial.vars_mul _ _) (Finset.union_subset hp₁ hq₂v))
              (Finset.Subset.trans (MvPolynomial.vars_mul _ _) (Finset.union_subset hp₂ hq₁v)))
        · exact Finset.Subset.trans (MvPolynomial.vars_mul _ _) (Finset.union_subset hq₁v hq₂v)
        · have h1 : algebraMap (MvPolynomial ι' K) (FractionRing (MvPolynomial ι' K)) q₁ ≠ 0 := fun h0 =>
            hq₁ (IsFractionRing.injective (MvPolynomial ι' K) (FractionRing (MvPolynomial ι' K))
              (by rw [h0, map_zero]))
          have h2 : algebraMap (MvPolynomial ι' K) (FractionRing (MvPolynomial ι' K)) q₂ ≠ 0 := fun h0 =>
            hq₂ (IsFractionRing.injective (MvPolynomial ι' K) (FractionRing (MvPolynomial ι' K))
              (by rw [h0, map_zero]))
          simp only [map_add, map_mul]
          field_simp
      zero_mem' := ⟨0, 1, one_ne_zero, by simp, by simp, by simp⟩
      inv_mem' := by
        rintro _ ⟨p, q, hq, hpv, hqv, rfl⟩
        by_cases hp0 : p = 0
        · subst hp0; exact ⟨0, 1, one_ne_zero, by simp, by simp, by simp⟩
        · exact ⟨q, p, hp0, hqv, hpv, by simp [inv_div]⟩
      algebraMap_mem' := fun c => ⟨MvPolynomial.C c, 1, one_ne_zero, by simp, by simp, by
        rw [map_one, div_one]
        exact IsScalarTower.algebraMap_apply K (MvPolynomial ι' K) (FractionRing (MvPolynomial ι' K)) c⟩ }
  have hgens_mem : ∀ g ∈ gens, g ∈ KS := by
    intro g hg
    refine ⟨pG g, qG g, hqG g, ?_, ?_, hΦG g⟩
    · exact Finset.Subset.trans Finset.subset_union_left
        (Finset.subset_biUnion_of_mem (fun g => (pG g).vars ∪ (qG g).vars) hg)
    · exact Finset.Subset.trans Finset.subset_union_right
        (Finset.subset_biUnion_of_mem (fun g => (pG g).vars ∪ (qG g).vars) hg)
  have hKS_top : ∀ z, z ∈ KS := hgen KS hgens_mem
  have hall : ∀ j : ι', j ∈ S := by
    intro j
    obtain ⟨p, q, hq, hpv, _, hXj⟩ := hKS_top (algebraMap (MvPolynomial ι' K) _ (MvPolynomial.X j))
    exact mem_finset_of_X_eq_div S j p q hq hpv hXj
  exact @Finite.of_fintype ι' ⟨S, hall⟩

set_option maxRecDepth 4096 in
private lemma finite_index_of_fin_gen {ι' : Type}
    (Φ : EField ≃ₐ[F47] FractionRing (MvPolynomial ι' F47)) : Finite ι' := by
  classical
  let gensE : Finset EField :=
    {y0E} ∪ (Finset.univ.image (fun b : Γ47 => monomE (swanBasis b))) ∪
      (Finset.univ.image (fun b : Γ47 => (monomE (swanBasis b))⁻¹))
  refine finite_of_finset_gen (gensE.image Φ) fun L hL z => ?_
  have hgens_mem : ∀ g ∈ gensE, Φ g ∈ L := fun g hg =>
    hL (Φ g) (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
  have hB_mem : ∀ x : ringB, Φ x.1 ∈ L := by
    rintro ⟨x, hx⟩
    rcases hx with ⟨p, k, rfl⟩
    change Φ (φB p / (φB tB) ^ k) ∈ L
    rw [map_div₀, map_pow]
    have hφ_mem : ∀ q : PB, Φ (φB q) ∈ L := by
      intro q
      induction q using MvPolynomial.induction_on with
      | C c =>
        have hC : φB (MvPolynomial.C c) = algebraMap F47 EField c := φB.commutes c
        rw [hC, Φ.commutes]
        exact L.algebraMap_mem c
      | add q₁ q₂ h₁ h₂ => rw [map_add, map_add]; exact L.add_mem h₁ h₂
      | mul_X q o hq =>
        rw [map_mul, map_mul]
        refine L.mul_mem hq ?_
        cases o with
        | none => rw [φB_X_none]; exact hgens_mem y0E (by simp [gensE])
        | some b => rw [φB_X_some]; exact hgens_mem (monomE (swanBasis b)) (by simp [gensE])
    exact L.div_mem (hφ_mem p) (L.pow_mem (hφ_mem tB) k)
  obtain ⟨a, b, _, hab⟩ := ringB_isFractionRing (Φ.symm z)
  have hz : z = Φ a.1 / Φ b.1 := by
    rw [← map_div₀, ← hab, Φ.apply_symm_apply]
  rw [hz]
  exact L.div_mem (hB_mem a) (hB_mem b)

private noncomputable def locSubalg {F E : Type} [Field F] [Field E] [Algebra F E]
    (D : Subalgebra F E) (s : D) : Subalgebra F E where
  carrier := { x : E | ∃ (a : D) (k : ℕ), x = (a : E) / (s : E) ^ k }
  mul_mem' := by
    rintro _ _ ⟨a₁, k₁, rfl⟩ ⟨a₂, k₂, rfl⟩
    exact ⟨a₁ * a₂, k₁ + k₂, by simp [pow_add, div_mul_div_comm]⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a₁, k₁, rfl⟩ ⟨a₂, k₂, rfl⟩
    by_cases hs : (s : E) = 0
    · by_cases hk1 : k₁ = 0 <;> by_cases hk2 : k₂ = 0
      · subst hk1 hk2; exact ⟨a₁ + a₂, 0, by simp⟩
      · subst hk1; exact ⟨a₁, 0, by simp [hs, zero_pow hk2]⟩
      · subst hk2; exact ⟨a₂, 0, by simp [hs, zero_pow hk1]⟩
      · exact ⟨0, 0, by simp [hs, zero_pow hk1, zero_pow hk2]⟩
    · refine ⟨a₁ * s ^ k₂ + a₂ * s ^ k₁, k₁ + k₂, ?_⟩
      simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_pow, pow_add]
      field_simp
  zero_mem' := ⟨0, 0, by simp⟩
  algebraMap_mem' c := ⟨algebraMap F D c, 0, by simp⟩

/- Section 7: General UFD localization units lemma -/

private noncomputable def assocMap {D : Type} [CommRing D] [IsDomain D] (f : D →+* D) :
    Associates D →* Associates D where
  toFun q := Quotient.liftOn q (fun d => Associates.mk (f d)) fun a b hab => by
    rw [Associates.mk_eq_mk_iff_associated]
    exact hab.map f.toMonoidHom
  map_one' := by
    change Associates.mk (f 1) = 1
    rw [map_one, Associates.mk_one]
  map_mul' q₁ q₂ := by
    obtain ⟨a, rfl⟩ := Associates.mk_surjective q₁
    obtain ⟨b, rfl⟩ := Associates.mk_surjective q₂
    change Associates.mk (f (a * b)) = Associates.mk (f a) * Associates.mk (f b)
    rw [map_mul, Associates.mk_mul_mk]

private noncomputable def assocAct {D : Type} [CommRing D] [IsDomain D]
    (act : Γ47 →* (D ≃+* D)) (g : Γ47) : Associates D ≃* Associates D where
  toFun := assocMap (act g).toRingHom
  invFun := assocMap (act g⁻¹).toRingHom
  left_inv q := by
    obtain ⟨d, rfl⟩ := Associates.mk_surjective q
    change Associates.mk ((act g⁻¹ * act g) d) = Associates.mk d
    rw [← map_mul, inv_mul_cancel, map_one]; rfl
  right_inv q := by
    obtain ⟨d, rfl⟩ := Associates.mk_surjective q
    change Associates.mk ((act g * act g⁻¹) d) = Associates.mk d
    rw [← map_mul, mul_inv_cancel, map_one]; rfl
  map_mul' q₁ q₂ := map_mul (assocMap (act g).toRingHom) q₁ q₂

private lemma assocAct_mk {D : Type} [CommRing D] [IsDomain D]
    (act : Γ47 →* (D ≃+* D)) (g : Γ47) (d : D) :
    assocAct act g (Associates.mk d) = Associates.mk (act g d) := rfl

private lemma assocAct_one {D : Type} [CommRing D] [IsDomain D]
    (act : Γ47 →* (D ≃+* D)) (q : Associates D) :
    assocAct act 1 q = q := by
  obtain ⟨d, rfl⟩ := Associates.mk_surjective q
  simp [assocAct_mk]

private lemma assocAct_mul {D : Type} [CommRing D] [IsDomain D]
    (act : Γ47 →* (D ≃+* D)) (g₁ g₂ : Γ47) (q : Associates D) :
    assocAct act (g₁ * g₂) q = assocAct act g₁ (assocAct act g₂ q) := by
  obtain ⟨d, rfl⟩ := Associates.mk_surjective q
  simp [assocAct_mk]

private lemma mulEquiv_irreducible {α β : Type*} [Monoid α] [Monoid β]
    (e : α ≃* β) {a : α} (ha : Irreducible a) : Irreducible (e a) := by
  refine ⟨fun hu => ha.not_isUnit (by simpa using hu.map e.symm.toMonoidHom), fun x y hxy => ?_⟩
  have h1 : a = e.symm x * e.symm y := by
    apply e.injective
    simp [hxy]
  rcases ha.isUnit_or_isUnit h1 with hx | hy
  · left; simpa using hx.map e.toMonoidHom
  · right; simpa using hy.map e.toMonoidHom

private lemma multiset_count_map_of_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (s : Multiset α) (a : α) :
    (s.map f).count (f a) = s.count a := by
  induction s using Multiset.induction with
  | empty => simp
  | cons x s ih =>
    rw [Multiset.map_cons, Multiset.count_cons, Multiset.count_cons, ih]
    by_cases h : x = a
    · subst h; simp
    · have hne : f x ≠ f a := fun heq => h (hf heq)
      simp [Ne.symm h, Ne.symm hne]

private lemma prime_dvd_multiset_prod {α : Type*} [CommMonoidWithZero α] {p : α} (hp : Prime p)
    {s : Multiset α} (h : p ∣ s.prod) : ∃ r ∈ s, p ∣ r := by
  induction s using Multiset.induction with
  | empty =>
    rw [Multiset.prod_zero] at h
    exact absurd (isUnit_of_dvd_one h) hp.not_isUnit
  | cons x s ih =>
    rw [Multiset.prod_cons] at h
    rcases hp.dvd_or_dvd h with hx | hs
    · exact ⟨x, Multiset.mem_cons_self x s, hx⟩
    · obtain ⟨r, hr, hpr⟩ := ih hs
      exact ⟨r, Multiset.mem_cons_of_mem hr, hpr⟩

private lemma multiset_rel_associated_eq {α : Type*} [CommMonoid α]
    {s t : Multiset (Associates α)} (h : Multiset.Rel Associated s t) : s = t := by
  induction h with
  | zero => rfl
  | cons h1 _ ih => rw [associated_iff_eq.mp h1, ih]

private lemma factors_associates_mul {D : Type} [CommRing D] [IsDomain D]
    [UniqueFactorizationMonoid D] {a b : Associates D} (ha : a ≠ 0) (hb : b ≠ 0) :
    UniqueFactorizationMonoid.factors (a * b) =
      UniqueFactorizationMonoid.factors a + UniqueFactorizationMonoid.factors b :=
  multiset_rel_associated_eq (UniqueFactorizationMonoid.factors_mul ha hb)

private lemma factors_associates_map {D : Type} [CommRing D] [IsDomain D]
    [UniqueFactorizationMonoid D] (e : Associates D ≃* Associates D) {a : Associates D} (ha : a ≠ 0) :
    UniqueFactorizationMonoid.factors (e a) = (UniqueFactorizationMonoid.factors a).map e := by
  have he0 : e a ≠ 0 := fun h => ha (e.injective (by rw [h, map_zero]))
  have hrel : Multiset.Rel Associated (UniqueFactorizationMonoid.factors (e a))
      ((UniqueFactorizationMonoid.factors a).map e) :=
    UniqueFactorizationMonoid.factors_unique
      (fun q hq => UniqueFactorizationMonoid.irreducible_of_factor q hq)
      (fun q hq => by
        rcases Multiset.mem_map.mp hq with ⟨r, hr, rfl⟩
        exact mulEquiv_irreducible e (UniqueFactorizationMonoid.irreducible_of_factor r hr))
      (by
        rw [← map_multiset_prod]
        have h1 := UniqueFactorizationMonoid.factors_prod he0
        have h2 := (UniqueFactorizationMonoid.factors_prod ha).map e.toMonoidHom
        exact h1.trans h2.symm)
  exact multiset_rel_associated_eq hrel

private lemma ufd_loc_units
    {F E : Type} [Field F] [Field E] [Algebra F E]
    (actE : Γ47 →* (E ≃+* E))
    (D : Subalgebra F E)
    [UniqueFactorizationMonoid D]
    (hD_act : ∀ g (x : E), x ∈ D → actE g x ∈ D)
    (s : D) (hs0 : s ≠ 0) (hs_fix : ∀ g, actE g (s : E) = (s : E)) :
    ∃ (X : Type) (_ : Fintype X) (_ : MulAction Γ47 X)
      (val : (locSubalg D s)ˣ → (X → ℤ)),
      (∀ u v, val (u * v) = val u + val v) ∧
      (val 1 = 0) ∧
      Function.Surjective val ∧
      (∀ u, val u = 0 ↔ (u : E) ∈ D ∧ ((u⁻¹ : (locSubalg D s)ˣ) : E) ∈ D) ∧
      (∀ g (u : (locSubalg D s)ˣ) (u' : (locSubalg D s)ˣ),
        (u' : E) = actE g (u : E) → val u' = permAct g (val u)) := by
  classical
  let actD : Γ47 →* (D ≃+* D) :=
    { toFun := fun g =>
        { toFun := fun d => ⟨actE g d.1, hD_act g d.1 d.2⟩
          invFun := fun d => ⟨actE g⁻¹ d.1, hD_act g⁻¹ d.1 d.2⟩
          left_inv := fun d => Subtype.ext (by
            change (actE g⁻¹ * actE g) d.1 = d.1
            rw [← map_mul, inv_mul_cancel, map_one]; rfl)
          right_inv := fun d => Subtype.ext (by
            change (actE g * actE g⁻¹) d.1 = d.1
            rw [← map_mul, mul_inv_cancel, map_one]; rfl)
          map_mul' := fun d₁ d₂ => Subtype.ext (map_mul (actE g) d₁.1 d₂.1)
          map_add' := fun d₁ d₂ => Subtype.ext (map_add (actE g) d₁.1 d₂.1) }
      map_one' := by ext d; simp
      map_mul' := fun g₁ g₂ => by ext d; simp }
  have hs_actD : ∀ g, actD g s = s := fun g => Subtype.ext (hs_fix g)
  let X : Type := { q : Associates D // Irreducible q ∧ q ∣ Associates.mk s }
  have hs_mk0 : Associates.mk s ≠ 0 := Associates.mk_ne_zero.mpr hs0
  have hX_sub : ∀ q : X, q.1 ∈ (UniqueFactorizationMonoid.factors (Associates.mk s)).toFinset := by
    intro ⟨q, hq_irred, hq_dvd⟩
    rw [Multiset.mem_toFinset]
    have hq_prime : Prime q := UniqueFactorizationMonoid.irreducible_iff_prime.mp hq_irred
    have hprod : Associated (UniqueFactorizationMonoid.factors (Associates.mk s)).prod (Associates.mk s) :=
      UniqueFactorizationMonoid.factors_prod hs_mk0
    have hdvd_prod : q ∣ (UniqueFactorizationMonoid.factors (Associates.mk s)).prod :=
      dvd_trans hq_dvd hprod.symm.dvd
    obtain ⟨r, hr_mem, hqr⟩ := prime_dvd_multiset_prod hq_prime hdvd_prod
    have hr_irred : Irreducible r := UniqueFactorizationMonoid.irreducible_of_factor r hr_mem
    have heq : q = r := associated_iff_eq.mp (associated_of_dvd_dvd hqr (hq_irred.dvd_symm hr_irred hqr))
    exact heq ▸ hr_mem
  let instFinX : Fintype X := Fintype.ofInjective
    (fun q : X => (⟨q.1, hX_sub q⟩ : { r // r ∈ (UniqueFactorizationMonoid.factors (Associates.mk s)).toFinset }))
    (fun q₁ q₂ h => Subtype.ext (congr_arg (fun z : { r // r ∈ (UniqueFactorizationMonoid.factors (Associates.mk s)).toFinset } => z.1) h))
  let gAct (g : Γ47) (q : X) : X :=
    ⟨assocAct actD g q.1,
      mulEquiv_irreducible (assocAct actD g) q.2.1,
      by
        have h : assocAct actD g q.1 ∣ assocAct actD g (Associates.mk s) :=
          map_dvd (assocAct actD g).toMonoidHom q.2.2
        rwa [assocAct_mk, hs_actD] at h⟩
  let instActX : MulAction Γ47 X :=
    { smul := gAct
      one_smul := fun q => Subtype.ext (assocAct_one actD q.1)
      mul_smul := fun g₁ g₂ q => Subtype.ext (assocAct_mul actD g₁ g₂ q.1) }
  let mult (q : X) (d : D) : ℕ := (UniqueFactorizationMonoid.factors (Associates.mk d)).count q.1
  have hmult_mul : ∀ (q : X) {a b : D}, a ≠ 0 → b ≠ 0 → mult q (a * b) = mult q a + mult q b := by
    intro q a b ha hb
    dsimp only [mult]
    rw [← Associates.mk_mul_mk,
      factors_associates_mul (Associates.mk_ne_zero.mpr ha) (Associates.mk_ne_zero.mpr hb),
      Multiset.count_add]
  have hmult_pow : ∀ (q : X) {a : D}, a ≠ 0 → ∀ k : ℕ, mult q (a ^ k) = k * mult q a := by
    intro q a ha k
    induction k with
    | zero =>
      simp only [pow_zero, zero_mul, mult]
      have h1 : UniqueFactorizationMonoid.factors (Associates.mk (1 : D)) = 0 := by
        rw [Associates.mk_one]
        exact UniqueFactorizationMonoid.factors_one
      rw [h1, Multiset.count_zero]
    | succ k ih =>
      rw [pow_succ, hmult_mul q (pow_ne_zero k ha) ha, ih, add_mul, one_mul]
  have hmult_act : ∀ (g : Γ47) (q : X) {a : D}, a ≠ 0 →
      mult q (actD g a) = mult (gAct g⁻¹ q) a := by
    intro g q a ha
    dsimp only [mult]
    rw [← assocAct_mk actD g a,
      factors_associates_map (assocAct actD g) (Associates.mk_ne_zero.mpr ha)]
    have hq_eq : q.1 = assocAct actD g (gAct g⁻¹ q).1 := by
      change q.1 = assocAct actD g (assocAct actD g⁻¹ q.1)
      rw [← assocAct_mul, mul_inv_cancel, assocAct_one]
    conv_lhs => rw [hq_eq]
    exact multiset_count_map_of_injective (assocAct actD g) (assocAct actD g).injective _ _
  have hrep : ∀ u : (locSubalg D s)ˣ, ∃ (a : D) (k : ℕ), a ≠ 0 ∧ (u : E) = (a : E) / (s : E) ^ k := by
    intro u
    rcases u.1.2 with ⟨a, k, ha⟩
    have ha0 : a ≠ 0 := by
      intro h0
      have hu0 : (u : E) = 0 := by rw [ha, h0, ZeroMemClass.coe_zero, zero_div]
      have h1 := congr_arg (fun z : locSubalg D s => (z : E)) u.mul_inv
      rw [Subalgebra.coe_mul, hu0, zero_mul] at h1
      exact zero_ne_one h1
    exact ⟨a, k, ha0, ha⟩
  choose repA repK hrepA0 hrepEq using hrep
  have hsE0 : (s : E) ≠ 0 := fun h => hs0 (Subtype.ext h)
  have hval_wd : ∀ (q : X) {a₁ a₂ : D} {k₁ k₂ : ℕ}, a₁ ≠ 0 → a₂ ≠ 0 →
      (a₁ : E) / (s : E) ^ k₁ = (a₂ : E) / (s : E) ^ k₂ →
      (mult q a₁ : ℤ) - (k₁ : ℤ) * (mult q s : ℤ) = (mult q a₂ : ℤ) - (k₂ : ℤ) * (mult q s : ℤ) := by
    intro q a₁ a₂ k₁ k₂ ha₁ ha₂ heq
    have hmulE : (a₁ : E) * (s : E) ^ k₂ = (a₂ : E) * (s : E) ^ k₁ := by
      have h1 := pow_ne_zero k₁ hsE0
      have h2 := pow_ne_zero k₂ hsE0
      field_simp at heq
      linear_combination heq
    have hmulD : a₁ * s ^ k₂ = a₂ * s ^ k₁ := Subtype.ext (by simpa using hmulE)
    have hm := congr_arg (mult q) hmulD
    rw [hmult_mul q ha₁ (pow_ne_zero k₂ hs0), hmult_mul q ha₂ (pow_ne_zero k₁ hs0),
      hmult_pow q hs0 k₂, hmult_pow q hs0 k₁] at hm
    omega
  let val : (locSubalg D s)ˣ → (X → ℤ) := fun u q =>
    (mult q (repA u) : ℤ) - (repK u : ℤ) * (mult q s : ℤ)
  have hval_eq : ∀ (u : (locSubalg D s)ˣ) (a : D) (k : ℕ), a ≠ 0 →
      (u : E) = (a : E) / (s : E) ^ k →
      ∀ q : X, val u q = (mult q a : ℤ) - (k : ℤ) * (mult q s : ℤ) := by
    intro u a k ha heq q
    exact hval_wd q (hrepA0 u) ha ((hrepEq u).symm.trans heq)
  refine ⟨X, instFinX, instActX, val, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v
    ext q
    have huv : ((u * v : (locSubalg D s)ˣ) : E) =
        ((repA u * repA v : D) : E) / (s : E) ^ (repK u + repK v) := by
      change (u : E) * (v : E) = _
      rw [hrepEq u, hrepEq v, Subalgebra.coe_mul, pow_add, div_mul_div_comm]
    rw [hval_eq (u * v) (repA u * repA v) (repK u + repK v) (mul_ne_zero (hrepA0 u) (hrepA0 v)) huv q]
    rw [hmult_mul q (hrepA0 u) (hrepA0 v)]
    simp only [Pi.add_apply, val, Nat.cast_add]
    ring
  · ext q
    rw [hval_eq 1 1 0 one_ne_zero (by simp) q]
    have h1 : mult q 1 = 0 := by
      simp only [mult, Associates.mk_one, UniqueFactorizationMonoid.factors_one, Multiset.count_zero]
    simp [h1]
  · intro f
    have hpick : ∀ q : X, ∃ p : D, Associates.mk p = q.1 := fun q => Associates.mk_surjective q.1
    choose pRep hpRep using hpick
    have hpRep_unit : ∀ q : X, ∃ u : (locSubalg D s)ˣ, (u : E) = (pRep q : E) := by
      intro q
      have hdvd : pRep q ∣ s := by
        rw [← Associates.mk_dvd_mk, hpRep q]
        exact q.2.2
      rcases hdvd with ⟨c, hc⟩
      refine ⟨⟨⟨(pRep q : E), pRep q, 0, by simp⟩,
        ⟨(c : E) / (s : E), c, 1, by simp⟩, ?_, ?_⟩, rfl⟩
      · apply Subtype.ext
        change (pRep q : E) * ((c : E) / (s : E)) = 1
        have hcE : (s : E) = (pRep q : E) * (c : E) := congr_arg Subtype.val hc
        rw [← mul_div_assoc, ← hcE, div_self hsE0]
      · apply Subtype.ext
        change ((c : E) / (s : E)) * (pRep q : E) = 1
        have hcE : (s : E) = (pRep q : E) * (c : E) := congr_arg Subtype.val hc
        rw [div_mul_eq_mul_div, mul_comm, ← hcE, div_self hsE0]
    choose uRep huRep using hpRep_unit
    have hval_uRep : ∀ q : X, val (uRep q) = Pi.single q 1 := by
      intro q
      ext r
      have hp0 : pRep q ≠ 0 := by
        intro h0
        have : q.1 = 0 := by rw [← hpRep q, h0, Associates.mk_zero]
        exact q.2.1.ne_zero this
      rw [hval_eq (uRep q) (pRep q) 0 hp0 (by simp [huRep q]) r]
      simp only [Nat.cast_zero, zero_mul, sub_zero, mult, hpRep q]
      have hfac : UniqueFactorizationMonoid.factors q.1 = {q.1} := by
        have hrel : Multiset.Rel Associated (UniqueFactorizationMonoid.factors q.1) {q.1} :=
          UniqueFactorizationMonoid.factors_unique
            (fun a ha => UniqueFactorizationMonoid.irreducible_of_factor a ha)
            (fun a ha => by rw [Multiset.mem_singleton.mp ha]; exact q.2.1)
            (by rw [Multiset.prod_singleton]; exact UniqueFactorizationMonoid.factors_prod q.2.1.ne_zero)
        exact multiset_rel_associated_eq hrel
      rw [hfac, Multiset.count_singleton]
      by_cases hqr : r = q
      · subst hqr; simp
      · have hne : r.1 ≠ q.1 := fun h => hqr (Subtype.ext h)
        simp [hqr, hne]
    have hval_hom : ∀ u v, val (u * v) = val u + val v := by
      intro u v; ext q
      have huv : ((u * v : (locSubalg D s)ˣ) : E) =
          ((repA u * repA v : D) : E) / (s : E) ^ (repK u + repK v) := by
        change (u : E) * (v : E) = _
        rw [hrepEq u, hrepEq v, Subalgebra.coe_mul, pow_add, div_mul_div_comm]
      rw [hval_eq (u * v) (repA u * repA v) (repK u + repK v) (mul_ne_zero (hrepA0 u) (hrepA0 v)) huv q,
        hmult_mul q (hrepA0 u) (hrepA0 v)]
      simp only [Pi.add_apply, val, Nat.cast_add]; ring
    have hval_one : val 1 = 0 := by
      ext q
      rw [hval_eq 1 1 0 one_ne_zero (by simp) q]
      simp [mult, Associates.mk_one]
    have hval_zpow : ∀ (u : (locSubalg D s)ˣ) (n : ℤ), val (u ^ n) = n • val u := by
      intro u n
      induction n with
      | zero => simp [hval_one]
      | succ k ih => rw [zpow_add_one, hval_hom, ih, add_smul, one_smul]
      | pred k ih =>
        have hinv : val u⁻¹ = -val u := by
          apply eq_neg_of_add_eq_zero_left
          rw [← hval_hom, inv_mul_cancel, hval_one]
        rw [zpow_sub_one, hval_hom, ih, hinv, sub_smul, one_smul, sub_eq_add_neg]
    refine ⟨∏ q : X, (uRep q) ^ (f q), ?_⟩
    have hprod_val : ∀ t : Finset X, val (∏ q ∈ t, (uRep q) ^ (f q)) = ∑ q ∈ t, f q • val (uRep q) := by
      intro t
      induction t using Finset.cons_induction with
      | empty => simp [hval_one]
      | cons q t hqt ih =>
        rw [Finset.prod_cons, Finset.sum_cons, hval_hom, hval_zpow, ih]
    rw [hprod_val]
    ext r
    simp only [hval_uRep, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite,
      mul_one, mul_zero]
    rw [Finset.sum_eq_single r]
    · simp
    · intro x _ hxr; simp [Ne.symm hxr]
    · intro h; exact absurd (Finset.mem_univ r) h
  · intro u
    constructor
    · intro hval0
      set a := repA u
      set k := repK u
      set b := repA u⁻¹
      set m := repK u⁻¹
      have habE : (a : E) * (b : E) = (s : E) ^ (k + m) := by
        have h1 : (u : E) * ((u⁻¹ : (locSubalg D s)ˣ) : E) = 1 :=
          congr_arg (fun z : locSubalg D s => (z : E)) u.mul_inv
        rw [hrepEq u, hrepEq u⁻¹, div_mul_div_comm, ← pow_add] at h1
        exact (div_eq_one_iff_eq (pow_ne_zero (k + m) hsE0)).mp h1
      have habD : a * b = s ^ (k + m) := Subtype.ext (by simpa using habE)
      have hfac_eq : UniqueFactorizationMonoid.factors (Associates.mk a) =
          UniqueFactorizationMonoid.factors (Associates.mk (s ^ k)) := by
        ext r
        by_cases hr : Irreducible r ∧ r ∣ Associates.mk s
        · let q : X := ⟨r, hr⟩
          have hq0 : (mult q a : ℤ) - (k : ℤ) * (mult q s : ℤ) = 0 := congr_fun hval0 q
          have hmk : mult q (s ^ k) = k * mult q s := hmult_pow q hs0 k
          change mult q a = mult q (s ^ k)
          rw [hmk]
          omega
        · refine Eq.trans (b := 0) ?_ (Eq.symm ?_)
          · rw [Multiset.count_eq_zero]
            intro hmem
            apply hr
            have hirr : Irreducible r := UniqueFactorizationMonoid.irreducible_of_factor r hmem
            have hp : Prime r := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
            have hdvd_a : r ∣ Associates.mk a :=
              dvd_trans (Multiset.dvd_prod hmem) (UniqueFactorizationMonoid.factors_prod (Associates.mk_ne_zero.mpr (hrepA0 u))).dvd
            have hmk_pow : Associates.mk (s ^ (k + m)) = Associates.mk s ^ (k + m) := Associates.mk_pow s (k + m)
            have hdvd_s : r ∣ Associates.mk s ^ (k + m) := by
              rw [← hmk_pow, ← habD, ← Associates.mk_mul_mk]
              exact dvd_mul_of_dvd_left hdvd_a _
            exact ⟨hirr, hp.dvd_of_dvd_pow hdvd_s⟩
          · rw [Multiset.count_eq_zero]
            intro hmem
            apply hr
            have hirr : Irreducible r := UniqueFactorizationMonoid.irreducible_of_factor r hmem
            have hp : Prime r := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
            have hmk_pow : Associates.mk (s ^ k) = Associates.mk s ^ k := Associates.mk_pow s k
            have hdvd_sk : r ∣ Associates.mk s ^ k := by
              rw [← hmk_pow]
              exact dvd_trans (Multiset.dvd_prod hmem)
                (UniqueFactorizationMonoid.factors_prod (Associates.mk_ne_zero.mpr (pow_ne_zero k hs0))).dvd
            exact ⟨hirr, hp.dvd_of_dvd_pow hdvd_sk⟩
      have hassoc : Associated a (s ^ k) := by
        rw [← Associates.mk_eq_mk_iff_associated]
        have h1 := UniqueFactorizationMonoid.factors_prod (Associates.mk_ne_zero.mpr (hrepA0 u))
        have h2 := UniqueFactorizationMonoid.factors_prod (Associates.mk_ne_zero.mpr (pow_ne_zero k hs0))
        rw [hfac_eq] at h1
        exact associated_iff_eq.mp (h1.symm.trans h2)
      rcases hassoc with ⟨d, hd⟩
      have huD : (u : E) = ((d⁻¹ : Dˣ) : E) := by
        have hdE : (a : E) * ((d : D) : E) = (s : E) ^ k :=
          congr_arg Subtype.val hd
        have hdinv : ((d⁻¹ : Dˣ) : E) = ((d : D) : E)⁻¹ := by
          apply eq_inv_of_mul_eq_one_right
          exact congr_arg (fun z : D => (z : E)) d.mul_inv
        rw [hrepEq u, hdinv, ← hdE]
        change (a : E) / ((a : E) * ((d : D) : E)) = ((d : D) : E)⁻¹
        rw [div_mul_eq_div_div, div_self (fun h => hrepA0 u (Subtype.ext h)), one_div]
      have huinvD : ((u⁻¹ : (locSubalg D s)ˣ) : E) = ((d : D) : E) := by
        have h1 : (u : E) * ((u⁻¹ : (locSubalg D s)ˣ) : E) = 1 :=
          congr_arg (fun z : locSubalg D s => (z : E)) u.mul_inv
        have h2 : ((d⁻¹ : Dˣ) : E) * ((d : D) : E) = 1 :=
          congr_arg (fun z : D => (z : E)) d.inv_mul
        rw [huD] at h1
        have hne : ((d⁻¹ : Dˣ) : E) ≠ 0 := by
          intro h0; rw [h0, zero_mul] at h2; exact zero_ne_one h2
        exact mul_left_cancel₀ hne (h1.trans h2.symm)
      exact ⟨by rw [huD]; exact ((d⁻¹ : Dˣ) : D).2, by rw [huinvD]; exact (d : D).2⟩
    · rintro ⟨huD, huinvD⟩
      let d : D := ⟨(u : E), huD⟩
      let dinv : D := ⟨((u⁻¹ : (locSubalg D s)ˣ) : E), huinvD⟩
      have hd_unit : IsUnit d := by
        refine ⟨⟨d, dinv, ?_, ?_⟩, rfl⟩
        · exact Subtype.ext (congr_arg (fun z : locSubalg D s => (z : E)) u.mul_inv)
        · exact Subtype.ext (congr_arg (fun z : locSubalg D s => (z : E)) u.inv_mul)
      have hd0 : d ≠ 0 := hd_unit.ne_zero
      ext q
      rw [hval_eq u d 0 hd0 (by simp [d]) q]
      have hmk1 : Associates.mk d = 1 := Associates.mk_eq_one.mpr hd_unit
      simp [mult, hmk1]
  · intro g u u' hu'
    ext q
    have hu'rep : (u' : E) = ((actD g (repA u) : D) : E) / (s : E) ^ (repK u) := by
      rw [hu', hrepEq u, map_div₀, map_pow, hs_fix g]
      rfl
    have hact0 : actD g (repA u) ≠ 0 := by
      intro h0
      exact hrepA0 u ((actD g).injective (by rw [h0, map_zero]))
    rw [hval_eq u' (actD g (repA u)) (repK u) hact0 hu'rep q]
    rw [hmult_act g q (hrepA0 u)]
    have hs_mult : mult q s = mult (gAct g⁻¹ q) s := by
      conv_lhs => rw [← hs_actD g]
      exact hmult_act g q hs0
    rw [hs_mult]
    rfl

/- Section 8: Main Theorem -/

private lemma exists_common_localization
    {F E : Type} [Field F] [Field E] [Algebra F E]
    (actE : Γ47 →* (E ≃+* E))
    (ringA ringB : Subalgebra F E)
    (gensA gensB : Finset E)
    (hA_gen : ∀ D : Subalgebra F E, (∀ x ∈ gensA, x ∈ D) → ringA ≤ D)
    (hB_gen : ∀ D : Subalgebra F E, (∀ x ∈ gensB, x ∈ D) → ringB ≤ D)
    (hA_act : ∀ g (x : E), x ∈ ringA → actE g x ∈ ringA)
    (hB_act : ∀ g (x : E), x ∈ ringB → actE g x ∈ ringB)
    (hA_frac : ∀ x : E, ∃ a b : ringA, b ≠ 0 ∧ x = (a : E) / (b : E))
    (hB_frac : ∀ x : E, ∃ a b : ringB, b ≠ 0 ∧ x = (a : E) / (b : E)) :
    ∃ (s : ringA) (r' : ringB),
      s ≠ 0 ∧ (∀ g, actE g (s : E) = (s : E)) ∧
      r' ≠ 0 ∧ (∀ g, actE g (r' : E) = (r' : E)) ∧
      locSubalg ringA s = locSubalg ringB r' := by
  classical
  have hle_loc : ∀ (D₁ D₂ : Subalgebra F E) (gens₂ : Finset E),
      (∀ D : Subalgebra F E, (∀ x ∈ gens₂, x ∈ D) → D₂ ≤ D) →
      (∀ g (x : E), x ∈ D₁ → actE g x ∈ D₁) →
      (∀ x : E, ∃ a b : D₁, b ≠ 0 ∧ x = (a : E) / (b : E)) →
      ∃ s₁ : D₁, s₁ ≠ 0 ∧ (∀ g, actE g (s₁ : E) = (s₁ : E)) ∧ D₂ ≤ locSubalg D₁ s₁ := by
    intro D₁ D₂ gens₂ h₂_gen h₁_act h₁_frac
    choose aGen dGen hdGen0 hGen using h₁_frac
    let s0 : D₁ := ∏ g ∈ gens₂, dGen g
    have hs0_ne : s0 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun g _ => hdGen0 g
    let act₁ : Γ47 → D₁ → D₁ := fun γ x => ⟨actE γ x.1, h₁_act γ x.1 x.2⟩
    let s1 : D₁ := ∏ γ : Γ47, act₁ γ s0
    have hs1_ne : s1 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun γ _ h0 =>
      hs0_ne (Subtype.ext ((actE γ).injective (by simpa [act₁] using congr_arg Subtype.val h0)))
    have hs1_fix : ∀ g : Γ47, actE g (s1 : E) = (s1 : E) := by
      intro g
      dsimp only [s1]
      rw [SubmonoidClass.coe_finsetProd, map_prod]
      refine Fintype.prod_equiv (Equiv.mulLeft g) _ _ fun γ => ?_
      change (actE g * actE γ) (s0 : E) = actE (g * γ) (s0 : E)
      rw [← map_mul]
    have hs0_dvd : s0 ∣ s1 := by
      have h1 : act₁ 1 s0 = s0 := Subtype.ext (by change actE 1 (s0 : E) = s0; simp)
      simpa only [h1] using Finset.dvd_prod_of_mem (fun γ => act₁ γ s0) (Finset.mem_univ (1 : Γ47))
    rcases hs0_dvd with ⟨c0, hc0⟩
    refine ⟨s1, hs1_ne, hs1_fix, h₂_gen (locSubalg D₁ s1) fun g hg => ?_⟩
    have hd_dvd : dGen g ∣ s0 := Finset.dvd_prod_of_mem _ hg
    rcases hd_dvd with ⟨c1, hc1⟩
    refine ⟨aGen g * c1 * c0, 1, ?_⟩
    have hs1E : (s1 : E) = (dGen g : E) * (c1 : E) * (c0 : E) := by
      have h1 := congr_arg Subtype.val hc0
      have h2 := congr_arg Subtype.val hc1
      simpa [h2, mul_assoc] using h1
    have hs1E0 : (s1 : E) ≠ 0 := fun h => hs1_ne (Subtype.ext h)
    have hc10 : (c1 : E) ≠ 0 := fun h => hs1E0 (by simp [hs1E, h])
    have hc00 : (c0 : E) ≠ 0 := fun h => hs1E0 (by simp [hs1E, h])
    conv_lhs => rw [hGen g]
    rw [pow_one, Subalgebra.coe_mul, Subalgebra.coe_mul, hs1E]
    field_simp
  obtain ⟨s1, hs1_ne, hs1_fix, hB_le_As1⟩ := hle_loc ringA ringB gensB hB_gen hA_act hA_frac
  obtain ⟨r1, hr1_ne, hr1_fix, hA_le_Br1⟩ := hle_loc ringB ringA gensA hA_gen hB_act hB_frac
  obtain ⟨a', k1, ha'⟩ := hB_le_As1 r1.2
  have ha'_ne : a' ≠ 0 := by
    intro h0
    apply hr1_ne
    apply Subtype.ext
    rw [ha', h0, ZeroMemClass.coe_zero, zero_div]
    rfl
  have ha'_fix : ∀ g : Γ47, actE g (a' : E) = (a' : E) := by
    intro g
    have hs1E0 : (s1 : E) ≠ 0 := fun h => hs1_ne (Subtype.ext h)
    have ha'E : (a' : E) = (r1 : E) * (s1 : E) ^ k1 := by
      rw [ha', div_mul_cancel₀ _ (pow_ne_zero k1 hs1E0)]
    rw [ha'E, map_mul, map_pow, hr1_fix g, hs1_fix g]
  let s : ringA := s1 * a'
  have hs_ne : s ≠ 0 := mul_ne_zero hs1_ne ha'_ne
  have hs_fix : ∀ g : Γ47, actE g (s : E) = (s : E) := fun g => by
    simp only [s, Subalgebra.coe_mul, map_mul, hs1_fix g, ha'_fix g]
  obtain ⟨b', m1, hb'⟩ := hA_le_Br1 s.2
  have hb'_ne : b' ≠ 0 := by
    intro h0
    apply hs_ne
    apply Subtype.ext
    rw [hb', h0, ZeroMemClass.coe_zero, zero_div]
    rfl
  have hb'_fix : ∀ g : Γ47, actE g (b' : E) = (b' : E) := by
    intro g
    have hr1E0 : (r1 : E) ≠ 0 := fun h => hr1_ne (Subtype.ext h)
    have hb'E : (b' : E) = (s : E) * (r1 : E) ^ m1 := by
      rw [hb', div_mul_cancel₀ _ (pow_ne_zero m1 hr1E0)]
    rw [hb'E, map_mul, map_pow, hs_fix g, hr1_fix g]
  let r' : ringB := r1 * b'
  have hr'_ne : r' ≠ 0 := mul_ne_zero hr1_ne hb'_ne
  have hr'_fix : ∀ g : Γ47, actE g (r' : E) = (r' : E) := fun g => by
    simp only [r', Subalgebra.coe_mul, map_mul, hr1_fix g, hb'_fix g]
  refine ⟨s, r', hs_ne, hs_fix, hr'_ne, hr'_fix, ?_⟩
  have hs1E0 : (s1 : E) ≠ 0 := fun h => hs1_ne (Subtype.ext h)
  have ha'E0 : (a' : E) ≠ 0 := fun h => ha'_ne (Subtype.ext h)
  have hr1E0 : (r1 : E) ≠ 0 := fun h => hr1_ne (Subtype.ext h)
  have hb'E0 : (b' : E) ≠ 0 := fun h => hb'_ne (Subtype.ext h)
  have hsE0 : (s : E) ≠ 0 := fun h => hs_ne (Subtype.ext h)
  apply le_antisymm
  · rintro _ ⟨a, k, rfl⟩
    have ha_mem : (a : E) ∈ locSubalg ringB r' := by
      obtain ⟨b0, k0, hb0⟩ := hA_le_Br1 a.2
      refine ⟨b0 * b' ^ k0, k0, ?_⟩
      rw [hb0, Subalgebra.coe_mul, Subalgebra.coe_pow]
      change (b0 : E) / (r1 : E) ^ k0 =
        ((b0 : E) * (b' : E) ^ k0) / ((r1 : E) * (b' : E)) ^ k0
      rw [mul_pow]
      field_simp
    have hs_inv : ((s : E))⁻¹ ∈ locSubalg ringB r' := by
      refine ⟨r1 ^ (m1 + 1), 1, ?_⟩
      have hb'E : (b' : E) = (s : E) * (r1 : E) ^ m1 := by
        rw [hb', div_mul_cancel₀ _ (pow_ne_zero m1 hr1E0)]
      change ((s : E))⁻¹ = (r1 : E) ^ (m1 + 1) / ((r1 : E) * (b' : E)) ^ 1
      rw [pow_one, hb'E, pow_succ']
      field_simp
    rw [div_eq_mul_inv, ← inv_pow]
    exact (locSubalg ringB r').mul_mem ha_mem ((locSubalg ringB r').pow_mem hs_inv k)
  · rintro _ ⟨b, k, rfl⟩
    have hb_mem : (b : E) ∈ locSubalg ringA s := by
      obtain ⟨a0, k0, ha0⟩ := hB_le_As1 b.2
      refine ⟨a0 * a' ^ k0, k0, ?_⟩
      rw [ha0, Subalgebra.coe_mul, Subalgebra.coe_pow]
      change (a0 : E) / (s1 : E) ^ k0 =
        ((a0 : E) * (a' : E) ^ k0) / ((s1 : E) * (a' : E)) ^ k0
      rw [mul_pow]
      field_simp
    have hr'_inv : ((r' : E))⁻¹ ∈ locSubalg ringA s := by
      refine ⟨s1 ^ (k1 * (m1 + 1) + (m1 + 1)), m1 + 2, ?_⟩
      have hb'E : (b' : E) = (s : E) * (r1 : E) ^ m1 := by
        rw [hb', div_mul_cancel₀ _ (pow_ne_zero m1 hr1E0)]
      have hr'E : (r' : E) = (s : E) * (r1 : E) ^ (m1 + 1) := by
        change (r1 : E) * (b' : E) = _
        rw [hb'E, pow_succ']; ring
      rw [hr'E, ha', div_pow]
      change ((s : E) * ((a' : E) ^ (m1 + 1) / ((s1 : E) ^ k1) ^ (m1 + 1)))⁻¹ =
        (s1 : E) ^ (k1 * (m1 + 1) + (m1 + 1)) / ((s1 : E) * (a' : E)) ^ (m1 + 2)
      have hs_eq : (s : E) = (s1 : E) * (a' : E) := rfl
      rw [hs_eq, ← pow_mul, mul_pow, pow_add, show m1 + 2 = 2 + m1 by omega, pow_add]
      field_simp
      rw [pow_add]
      ring
    rw [div_eq_mul_inv, ← inv_pow]
    exact (locSubalg ringA s).mul_mem hb_mem ((locSubalg ringA s).pow_mem hr'_inv k)

private lemma swan_exact_of_common_localization
    {F E : Type} [Field F] [Field E] [Algebra F E]
    (actE : Γ47 →* (E ≃+* E))
    (ringA ringB : Subalgebra F E)
    [UniqueFactorizationMonoid ringA]
    [UniqueFactorizationMonoid ringB]
    (hA_act : ∀ g (x : E), x ∈ ringA → actE g x ∈ ringA)
    (hB_act : ∀ g (x : E), x ∈ ringB → actE g x ∈ ringB)
    (s : ringA) (r' : ringB)
    (hs_ne : s ≠ 0) (hs_fix : ∀ g, actE g (s : E) = (s : E))
    (hr'_ne : r' ≠ 0) (hr'_fix : ∀ g, actE g (r' : E) = (r' : E))
    (hR_eq : locSubalg ringA s = locSubalg ringB r')
    (hA_units : ∀ u : E, u ≠ 0 → u ∈ ringA → u⁻¹ ∈ ringA → ∃ c : Fˣ, u = algebraMap F E c)
    (monomE : SwanIdeal → E)
    (hmonom_zero : monomE 0 = 1)
    (hmonom_add : ∀ u v, monomE (u + v) = monomE u * monomE v)
    (hmonom_ne : ∀ u, monomE u ≠ 0)
    (hmonom_mem : ∀ u, monomE u ∈ ringB)
    (hmonom_act : ∀ g u, actE g (monomE u) = monomE (swanAct g u))
    (hmonom_alg : ∀ (u : SwanIdeal) (c : Fˣ), monomE u = algebraMap F E c → u = 0)
    (hB_decomp : ∀ u : ringBˣ, ∃ (c : Fˣ) (v : SwanIdeal), (u : E) = algebraMap F E c * monomE v) :
    ∃ (X Y : Type) (_ : Fintype X) (_ : Fintype Y) (_ : MulAction Γ47 X) (_ : MulAction Γ47 Y)
      (ι : SwanIdeal →+ (X → ℤ)) (π : (X → ℤ) →+ (Y → ℤ)),
      Function.Injective ι ∧
      Function.Surjective π ∧
      (∀ v, π v = 0 ↔ ∃ u, ι u = v) ∧
      (∀ g u, ι (swanAct g u) = permAct g (ι u)) ∧
      (∀ g v, π (permAct g v) = permAct g (π v)) := by
  obtain ⟨X, hX_fin, hX_act, valA, hvalA_mul, hvalA_one, hvalA_surj, hvalA_ker, hvalA_act⟩ :=
    ufd_loc_units actE ringA hA_act s hs_ne hs_fix
  obtain ⟨Y, hY_fin, hY_act, valB, hvalB_mul, hvalB_one, hvalB_surj, hvalB_ker, hvalB_act⟩ :=
    ufd_loc_units actE ringB hB_act r' hr'_ne hr'_fix
  let eqR : (locSubalg ringA s)ˣ ≃* (locSubalg ringB r')ˣ :=
    { toFun := fun u =>
        ⟨⟨u.1.1, hR_eq ▸ u.1.2⟩, ⟨u.2.1, hR_eq ▸ u.2.2⟩,
          Subtype.ext (congr_arg (fun z : locSubalg ringA s => (z : E)) u.mul_inv),
          Subtype.ext (congr_arg (fun z : locSubalg ringA s => (z : E)) u.inv_mul)⟩
      invFun := fun u =>
        ⟨⟨u.1.1, hR_eq.symm ▸ u.1.2⟩, ⟨u.2.1, hR_eq.symm ▸ u.2.2⟩,
          Subtype.ext (congr_arg (fun z : locSubalg ringB r' => (z : E)) u.mul_inv),
          Subtype.ext (congr_arg (fun z : locSubalg ringB r' => (z : E)) u.inv_mul)⟩
      left_inv := fun _ => Units.ext (Subtype.ext rfl)
      right_inv := fun _ => Units.ext (Subtype.ext rfl)
      map_mul' := fun _ _ => Units.ext (Subtype.ext rfl) }
  have heqR_val : ∀ u : (locSubalg ringA s)ˣ, ((eqR u : locSubalg ringB r') : E) = (u : E) :=
    fun _ => rfl
  have heqR_inv_val : ∀ u : (locSubalg ringA s)ˣ,
      (((eqR u)⁻¹ : (locSubalg ringB r')ˣ) : E) = ((u⁻¹ : (locSubalg ringA s)ˣ) : E) :=
    fun _ => rfl
  let mUnit (u : SwanIdeal) : (locSubalg ringA s)ˣ :=
    ⟨⟨monomE u, hR_eq ▸ ⟨⟨monomE u, hmonom_mem u⟩, 0, by simp⟩⟩,
     ⟨monomE (-u), hR_eq ▸ ⟨⟨monomE (-u), hmonom_mem (-u)⟩, 0, by simp⟩⟩,
     Subtype.ext (by change monomE u * monomE (-u) = 1; rw [← hmonom_add, add_neg_cancel, hmonom_zero]),
     Subtype.ext (by change monomE (-u) * monomE u = 1; rw [← hmonom_add, neg_add_cancel, hmonom_zero])⟩
  have hmUnit_mul : ∀ u v, mUnit (u + v) = mUnit u * mUnit v := fun u v =>
    Units.ext (Subtype.ext (hmonom_add u v))
  have hmUnit_zero : mUnit 0 = 1 := Units.ext (Subtype.ext hmonom_zero)
  let ι : SwanIdeal →+ (X → ℤ) :=
    { toFun := fun u => valA (mUnit u)
      map_zero' := by rw [hmUnit_zero, hvalA_one]
      map_add' := fun u v => by rw [hmUnit_mul, hvalA_mul] }
  have hvalB_eq_of_valA_eq : ∀ u₁ u₂ : (locSubalg ringA s)ˣ,
      valA u₁ = valA u₂ → valB (eqR u₁) = valB (eqR u₂) := by
    intro u₁ u₂ heq
    have hdiff : valA (u₁ * u₂⁻¹) = 0 := by
      have hinv : valA u₂⁻¹ = -valA u₂ := by
        apply eq_neg_of_add_eq_zero_left
        rw [← hvalA_mul, inv_mul_cancel, hvalA_one]
      rw [hvalA_mul, hinv, heq, add_neg_cancel]
    have hA_mem := (hvalA_ker (u₁ * u₂⁻¹)).mp hdiff
    have hne0 : ((u₁ * u₂⁻¹ : (locSubalg ringA s)ˣ) : E) ≠ 0 := by
      intro h0
      have h1 := congr_arg (fun z : locSubalg ringA s => (z : E)) (u₁ * u₂⁻¹).mul_inv
      rw [Subalgebra.coe_mul, h0, zero_mul] at h1
      exact zero_ne_one h1
    have hinv_eq : (((u₁ * u₂⁻¹)⁻¹ : (locSubalg ringA s)ˣ) : E) =
        (((u₁ * u₂⁻¹ : (locSubalg ringA s)ˣ) : E))⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      exact congr_arg (fun z : locSubalg ringA s => (z : E)) (u₁ * u₂⁻¹).mul_inv
    obtain ⟨c, hc⟩ := hA_units _ hne0 hA_mem.1 (hinv_eq ▸ hA_mem.2)
    have hB_mem : ((eqR (u₁ * u₂⁻¹) : locSubalg ringB r') : E) ∈ ringB ∧
        (((eqR (u₁ * u₂⁻¹))⁻¹ : (locSubalg ringB r')ˣ) : E) ∈ ringB := by
      rw [heqR_val, heqR_inv_val, hinv_eq, hc]
      refine ⟨ringB.algebraMap_mem _, ?_⟩
      rw [← map_inv₀]
      exact ringB.algebraMap_mem _
    have hB0 : valB (eqR (u₁ * u₂⁻¹)) = 0 := (hvalB_ker _).mpr hB_mem
    rw [map_mul, map_inv, hvalB_mul] at hB0
    have hinvB : valB (eqR u₂)⁻¹ = -valB (eqR u₂) := by
      apply eq_neg_of_add_eq_zero_left
      rw [← hvalB_mul, inv_mul_cancel, hvalB_one]
    rw [hinvB] at hB0
    exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg] using hB0)
  have hvalA_surj' := hvalA_surj
  choose secA hsecA using hvalA_surj'
  let π : (X → ℤ) →+ (Y → ℤ) :=
    { toFun := fun v => valB (eqR (secA v))
      map_zero' := by
        have h := hvalB_eq_of_valA_eq (secA 0) 1 (by rw [hsecA, hvalA_one])
        rw [h, map_one, hvalB_one]
      map_add' := fun v₁ v₂ => by
        have h := hvalB_eq_of_valA_eq (secA (v₁ + v₂)) (secA v₁ * secA v₂)
          (by rw [hsecA, hvalA_mul, hsecA, hsecA])
        rw [h, map_mul, hvalB_mul] }
  have hπ_valA : ∀ u : (locSubalg ringA s)ˣ, π (valA u) = valB (eqR u) := fun u =>
    hvalB_eq_of_valA_eq (secA (valA u)) u (hsecA (valA u))
  refine ⟨X, Y, hX_fin, hY_fin, hX_act, hY_act, ι, π, ?_, ?_, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro u hu
    have hA_mem := (hvalA_ker (mUnit u)).mp hu
    have hinv_eq : (((mUnit u)⁻¹ : (locSubalg ringA s)ˣ) : E) = (monomE u)⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      exact congr_arg (fun z : locSubalg ringA s => (z : E)) (mUnit u).mul_inv
    obtain ⟨c, hc⟩ := hA_units (monomE u) (hmonom_ne u) hA_mem.1 (hinv_eq ▸ hA_mem.2)
    exact hmonom_alg u c hc
  · intro w
    obtain ⟨v, hv⟩ := hvalB_surj w
    exact ⟨valA (eqR.symm v), by rw [hπ_valA, MulEquiv.apply_symm_apply, hv]⟩
  · intro v
    obtain ⟨w, rfl⟩ := hvalA_surj v
    rw [hπ_valA, hvalB_ker]
    constructor
    · rintro ⟨hwB, hwinvB⟩
      rw [heqR_val] at hwB
      rw [heqR_inv_val] at hwinvB
      let uB : ringBˣ :=
        ⟨⟨(w : E), hwB⟩, ⟨((w⁻¹ : (locSubalg ringA s)ˣ) : E), hwinvB⟩,
         Subtype.ext (congr_arg (fun z : locSubalg ringA s => (z : E)) w.mul_inv),
         Subtype.ext (congr_arg (fun z : locSubalg ringA s => (z : E)) w.inv_mul)⟩
      obtain ⟨c, u, hu⟩ := hB_decomp uB
      refine ⟨u, ?_⟩
      let cUnit : (locSubalg ringA s)ˣ :=
        ⟨algebraMap F _ (c : F), algebraMap F _ ((c : F)⁻¹),
         by rw [← map_mul, mul_inv_cancel₀ c.ne_zero, map_one],
         by rw [← map_mul, inv_mul_cancel₀ c.ne_zero, map_one]⟩
      have hw_eq : w = cUnit * mUnit u := Units.ext (Subtype.ext hu)
      have hc0 : valA cUnit = 0 := (hvalA_ker cUnit).mpr
        ⟨ringA.algebraMap_mem _, ringA.algebraMap_mem _⟩
      rw [hw_eq, hvalA_mul, hc0, zero_add]
      rfl
    · rintro ⟨u, hu⟩
      have hB0 : valB (eqR (mUnit u)) = 0 := (hvalB_ker _).mpr
        ⟨by rw [heqR_val]; exact hmonom_mem u,
         by rw [heqR_inv_val]; exact hmonom_mem (-u)⟩
      have hBw : valB (eqR w) = 0 := (hvalB_eq_of_valA_eq w (mUnit u) hu.symm).trans hB0
      exact (hvalB_ker (eqR w)).mp hBw
  · intro g u
    exact hvalA_act g (mUnit u) (mUnit (swanAct g u)) (hmonom_act g u).symm
  · intro g v
    obtain ⟨w, rfl⟩ := hvalA_surj v
    have hact_mem : ∀ z : locSubalg ringA s, actE g z.1 ∈ locSubalg ringA s := by
      rintro ⟨_, a, k, rfl⟩
      refine ⟨⟨actE g a.1, hA_act g a.1 a.2⟩, k, ?_⟩
      rw [map_div₀, map_pow, hs_fix g]
    let wg : (locSubalg ringA s)ˣ :=
      ⟨⟨actE g (w : E), hact_mem w.1⟩,
       ⟨actE g ((w⁻¹ : (locSubalg ringA s)ˣ) : E), hact_mem w.2⟩,
       Subtype.ext (by
         change actE g (w : E) * actE g ((w⁻¹ : (locSubalg ringA s)ˣ) : E) = 1
         rw [← map_mul, show (w : E) * ((w⁻¹ : (locSubalg ringA s)ˣ) : E) = 1 from
           congr_arg (fun z : locSubalg ringA s => (z : E)) w.mul_inv, map_one]),
       Subtype.ext (by
         change actE g ((w⁻¹ : (locSubalg ringA s)ˣ) : E) * actE g (w : E) = 1
         rw [← map_mul, show ((w⁻¹ : (locSubalg ringA s)ˣ) : E) * (w : E) = 1 from
           congr_arg (fun z : locSubalg ringA s => (z : E)) w.inv_mul, map_one])⟩
    have hwgA : valA wg = permAct g (valA w) := hvalA_act g w wg rfl
    rw [← hwgA, hπ_valA, hπ_valA]
    exact hvalB_act g (eqR w) (eqR wg) (by rw [heqR_val, heqR_val])

private lemma poly_subalg_props
    {F E : Type} [Field F] [Field E] [Algebra F E]
    {ι' : Type} [Fintype ι']
    (actE : Γ47 →* (E ≃+* E))
    (σF : Γ47 →* (F ≃+* F))
    (Φ : E ≃ₐ[F] FractionRing (MvPolynomial ι' F))
    (hΦ_poly : ∀ g (p : MvPolynomial ι' F),
      Φ (actE g (Φ.symm (algebraMap (MvPolynomial ι' F) _ p))) =
        algebraMap (MvPolynomial ι' F) _ (MvPolynomial.map (σF g).toRingHom p)) :
    ∃ (ringA : Subalgebra F E) (_ : UniqueFactorizationMonoid ringA) (gensA : Finset E),
      (∀ D : Subalgebra F E, (∀ x ∈ gensA, x ∈ D) → ringA ≤ D) ∧
      (∀ g (x : E), x ∈ ringA → actE g x ∈ ringA) ∧
      (∀ x : E, ∃ a b : ringA, b ≠ 0 ∧ x = (a : E) / (b : E)) ∧
      (∀ u : E, u ≠ 0 → u ∈ ringA → u⁻¹ ∈ ringA → ∃ c : Fˣ, u = algebraMap F E c) := by
  classical
  let ringA : Subalgebra F E :=
    (IsScalarTower.toAlgHom F (MvPolynomial ι' F) (FractionRing (MvPolynomial ι' F))).range.comap
      Φ.toAlgHom
  have hA_iso : ringA ≃ₐ[F] MvPolynomial ι' F := by
    let toA : MvPolynomial ι' F →ₐ[F] ringA :=
      { toFun := fun p => ⟨Φ.symm (algebraMap (MvPolynomial ι' F) _ p), ⟨p, by simp⟩⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun p₁ p₂ => Subtype.ext (by simp)
        map_zero' := Subtype.ext (by simp)
        map_add' := fun p₁ p₂ => Subtype.ext (by simp)
        commutes' := fun c => Subtype.ext (by
          change Φ.symm (algebraMap F _ c) = algebraMap F E c
          exact Φ.symm.commutes c) }
    have hbij : Function.Bijective toA := by
      constructor
      · intro p₁ p₂ hp
        have h1 := Φ.symm.injective (congr_arg Subtype.val hp)
        exact IsFractionRing.injective (MvPolynomial ι' F) _ h1
      · rintro ⟨x, p, hp⟩
        refine ⟨p, Subtype.ext ?_⟩
        change Φ.symm (algebraMap (MvPolynomial ι' F) _ p) = x
        have hp' : algebraMap (MvPolynomial ι' F) _ p = Φ x := hp
        rw [hp', Φ.symm_apply_apply]
    exact (AlgEquiv.ofBijective toA hbij).symm
  let instUFM : UniqueFactorizationMonoid ringA :=
    MulEquiv.uniqueFactorizationMonoid hA_iso.symm.toMulEquiv inferInstance
  let gensA : Finset E := Finset.univ.image (fun i : ι' => (hA_iso.symm (MvPolynomial.X i) : E))
  refine ⟨ringA, instUFM, gensA, ?_, ?_, ?_, ?_⟩
  · intro D hD x hx
    set p := hA_iso ⟨x, hx⟩
    have hxp : x = (hA_iso.symm p : E) := by simp [p]
    rw [hxp]
    induction p using MvPolynomial.induction_on with
    | C c =>
      have hC : (hA_iso.symm (MvPolynomial.C c) : E) = algebraMap F E c :=
        congr_arg Subtype.val (hA_iso.symm.commutes c)
      rw [hC]; exact D.algebraMap_mem c
    | add p₁ p₂ h₁ h₂ => rw [map_add, Subalgebra.coe_add]; exact D.add_mem h₁ h₂
    | mul_X p i hp =>
      rw [map_mul, Subalgebra.coe_mul]
      exact D.mul_mem hp (hD _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  · rintro g x ⟨p, hp⟩
    refine ⟨MvPolynomial.map (σF g).toRingHom p, ?_⟩
    have hx : x = Φ.symm (algebraMap (MvPolynomial ι' F) _ p) := by
      apply Φ.injective
      rw [Φ.apply_symm_apply]
      exact hp.symm
    change algebraMap (MvPolynomial ι' F) _ _ = Φ (actE g x)
    rw [hx, hΦ_poly g p]
  · intro x
    induction h : Φ x using Localization.induction_on with
    | H y =>
      rcases y with ⟨p, q⟩
      have hq0 : (q : MvPolynomial ι' F) ≠ 0 := nonZeroDivisors.ne_zero q.2
      refine ⟨⟨Φ.symm (algebraMap (MvPolynomial ι' F) _ p), ⟨p, by simp⟩⟩,
        ⟨Φ.symm (algebraMap (MvPolynomial ι' F) _ (q : MvPolynomial ι' F)), ⟨(q : MvPolynomial ι' F), by simp⟩⟩, ?_, ?_⟩
      · intro h0
        apply hq0
        exact IsFractionRing.injective (MvPolynomial ι' F) _
          (Φ.symm.injective (by simpa using congr_arg Subtype.val h0))
      · apply Φ.injective
        rw [map_div₀, Φ.apply_symm_apply, Φ.apply_symm_apply, h, frac_mk_eq_div]
  · intro u hu0 hu huinv
    let d : ringA := ⟨u, hu⟩
    let dinv : ringA := ⟨u⁻¹, huinv⟩
    have hd_unit : IsUnit d := by
      refine ⟨⟨d, dinv, Subtype.ext (mul_inv_cancel₀ hu0), Subtype.ext (inv_mul_cancel₀ hu0)⟩, rfl⟩
    have hp_unit : IsUnit (hA_iso d) := hd_unit.map hA_iso.toMonoidHom
    rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced] at hp_unit
    rcases hp_unit with ⟨c0, ⟨c, rfl⟩, hc⟩
    refine ⟨c, ?_⟩
    have h1 : d = algebraMap F ringA c := by
      apply hA_iso.injective
      rw [hA_iso.commutes]
      exact hc
    exact congr_arg Subtype.val h1

private noncomputable def actERing : Γ47 →* (EField ≃+* EField) where
  toFun g := (actE g).toRingEquiv
  map_one' := by ext x; simp
  map_mul' g₁ g₂ := by ext x; simp

private noncomputable def σ47Ring : Γ47 →* (F47 ≃+* F47) where
  toFun g := (σ47Equiv g).toRingEquiv
  map_one' := by ext x; simp
  map_mul' g₁ g₂ := by ext x; simp

private lemma ringB_le_of_gens :
    ∃ gensB : Finset EField,
      ∀ D : Subalgebra F47 EField, (∀ x ∈ gensB, x ∈ D) → ringB ≤ D := by
  classical
  let gensB : Finset EField :=
    {y0E} ∪ (Finset.univ.image (fun b : Γ47 => monomE (swanBasis b))) ∪
      (Finset.univ.image (fun b : Γ47 => (monomE (swanBasis b))⁻¹))
  refine ⟨gensB, fun D hD => ?_⟩
  rintro _ ⟨p, k, rfl⟩
  have hφ_mem : ∀ q : PB, φB q ∈ D := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c =>
      have hC : φB (MvPolynomial.C c) = algebraMap F47 EField c := φB.commutes c
      rw [hC]; exact D.algebraMap_mem c
    | add q₁ q₂ h₁ h₂ => rw [map_add]; exact D.add_mem h₁ h₂
    | mul_X q o hq =>
      rw [map_mul]
      refine D.mul_mem hq ?_
      cases o with
      | none => rw [φB_X_none]; exact hD y0E (by simp [gensB])
      | some b => rw [φB_X_some]; exact hD (monomE (swanBasis b)) (by simp [gensB])
  have htinv : (φB tB)⁻¹ ∈ D := by
    simp only [tB, map_prod, φB_X_some]
    rw [← Finset.prod_inv_distrib]
    exact D.prod_mem fun b _ => hD (monomE (swanBasis b))⁻¹ (by simp [gensB])
  rw [div_eq_mul_inv, ← inv_pow]
  exact D.mul_mem (hφ_mem p) (D.pow_mem htinv k)

private lemma swan_exact_of_equiv {ι' : Type}
    (Φ : EField ≃ₐ[F47] FractionRing (MvPolynomial ι' F47))
    (hΦ_act : ∀ g x, Φ (actE g x) = actFrac ι' g (Φ x)) :
    ∃ (X Y : Type) (_ : Fintype X) (_ : Fintype Y) (_ : MulAction Γ47 X) (_ : MulAction Γ47 Y)
      (ι : SwanIdeal →+ (X → ℤ)) (π : (X → ℤ) →+ (Y → ℤ)),
      Function.Injective ι ∧
      Function.Surjective π ∧
      (∀ v, π v = 0 ↔ ∃ u, ι u = v) ∧
      (∀ g u, ι (swanAct g u) = permAct g (ι u)) ∧
      (∀ g v, π (permAct g v) = permAct g (π v)) := by
  have : Finite ι' := finite_index_of_fin_gen Φ
  have : Fintype ι' := Fintype.ofFinite ι'
  have hΦ_poly : ∀ g (p : MvPolynomial ι' F47),
      Φ (actERing g (Φ.symm (algebraMap (MvPolynomial ι' F47) _ p))) =
        algebraMap (MvPolynomial ι' F47) _ (MvPolynomial.map (σ47Ring g).toRingHom p) := by
    intro g p
    change Φ (actE g (Φ.symm (algebraMap (MvPolynomial ι' F47) _ p))) = _
    rw [hΦ_act, Φ.apply_symm_apply]
    exact actFrac_algebraMap_poly ι' g p
  obtain ⟨ringA, hUFM_A, gensA, hA_gen, hA_act, hA_frac, hA_units⟩ :=
    poly_subalg_props actERing σ47Ring Φ hΦ_poly
  obtain ⟨gensB, hB_gen⟩ := ringB_le_of_gens
  have : UniqueFactorizationMonoid ringA := hUFM_A
  have : UniqueFactorizationMonoid ringB := ringB_ufm
  have hB_act : ∀ g (x : EField), x ∈ ringB → actERing g x ∈ ringB :=
    fun g x hx => actE_mem_ringB g x hx
  obtain ⟨s, r', hs_ne, hs_fix, hr'_ne, hr'_fix, hR_eq⟩ :=
    exists_common_localization actERing ringA ringB gensA gensB hA_gen hB_gen hA_act hB_act hA_frac
      ringB_isFractionRing
  exact swan_exact_of_common_localization actERing ringA ringB hA_act hB_act
    s r' hs_ne hs_fix hr'_ne hr'_fix hR_eq hA_units
    monomE monomE_zero monomE_add monomE_ne_zero monomE_mem_ringB
    (fun g u => actE_monomE g u) (fun u c hc => monomE_eq_algebraMap_iff u c hc) ringB_unit_decomp

theorem hasNoetherProperty_implies_swan_exact
    (h : NoetherProblem.HasNoetherProperty ℚ (FractionRing (MvPolynomial (ZMod 47) ℚ)) (ZMod 47)) :
    ∃ (X Y : Type) (_ : Fintype X) (_ : Fintype Y) (_ : MulAction Γ47 X) (_ : MulAction Γ47 Y)
      (ι : SwanIdeal →+ (X → ℤ)) (π : (X → ℤ) →+ (Y → ℤ)),
      Function.Injective ι ∧
      Function.Surjective π ∧
      (∀ v, π v = 0 ↔ ∃ u, ι u = v) ∧
      (∀ g u, ι (swanAct g u) = permAct g (ι u)) ∧
      (∀ g v, π (permAct g v) = permAct g (π v)) := by
  let eRat : @AlgEquiv ℚ L0 L0 _ _ _ DivisionRing.toRatAlgebra OreLocalization.instAlgebra :=
    @AlgEquiv.mk ℚ L0 L0 _ _ _ DivisionRing.toRatAlgebra OreLocalization.instAlgebra
      (Equiv.refl _) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun r => RingHom.congr_fun (Subsingleton.elim _ _) r)
  obtain ⟨ι', hrat⟩ := h eRat H0 (by
    rintro _ ⟨k, rfl⟩
    exact ⟨Equiv.addRight (Multiplicative.toAdd k), by ext x; rfl⟩)
  obtain ⟨⟨e0_eq, e0_mul, e0_add, e0_comm⟩⟩ := hrat.pure_transcendental
  let e0' : (IntermediateField.fixedField H0) ≃ₐ[ℚ] FractionRing (MvPolynomial ι' ℚ) :=
    { toEquiv := e0_eq
      map_mul' := e0_mul
      map_add' := e0_add
      commutes' := fun r => by
        have h1 : algebraMap ℚ (IntermediateField.fixedField H0) r =
            @algebraMap ℚ (IntermediateField.fixedField H0) _ _ (IntermediateField.fixedField H0).algebra' r :=
          RingHom.congr_fun (Subsingleton.elim _ _) r
        have h2 : algebraMap ℚ (FractionRing (MvPolynomial ι' ℚ)) r =
            @algebraMap ℚ (FractionRing (MvPolynomial ι' ℚ)) _ _ OreLocalization.instAlgebra r :=
          RingHom.congr_fun (Subsingleton.elim _ _) r
        rw [h1, h2]
        exact e0_comm r }
  obtain ⟨Φ, hΦ_act⟩ := baseChangeEquiv e0'
  exact swan_exact_of_equiv Φ hΦ_act
end Part3

theorem not_hasNoetherProperty_47 :
    ¬ NoetherProblem.HasNoetherProperty ℚ (FractionRing (MvPolynomial (ZMod 47) ℚ)) (ZMod 47) := by
  intro h
  obtain ⟨X, Y, _, _, _, _, ι, π, hι, hπ, hexact, hι_eq, hπ_eq⟩ :=
    hasNoetherProperty_implies_swan_exact h
  exact no_swan_exact_seq X Y ι π hι hπ hexact hι_eq hπ_eq

end OMA.Noether47

theorem OMA.solution : type_of% @NoetherProblem.noether_problem.variants.forty_seven :=
  ⟨ℚ, FractionRing (MvPolynomial (ZMod 47) ℚ), ZMod 47,
    inferInstance, inferInstance, inferInstance, inferInstance,
    OMA.Noether47.instIsRationalExtensionRat (ZMod 47),
    by simp, OMA.Noether47.not_hasNoetherProperty_47⟩
