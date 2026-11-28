import OMAReductions.R_Green100_green_100_variants_operator_norm_R1_H3_R1
import Mathlib

/-!
# Proof of `Green100.green_100.variants.operator_norm.R1.H3.R1.H2`

Given a countable group `G`, a subgroup `Γ ≤ G` with Property (FH), an element `t : G` with
`t Γ t⁻¹ ⊆ Γ`, a unital C*-algebra `A`, and a unitary representation `σ : G →* unitary A`,
we construct the Kazhdan projections `p, q ∈ A`:

1. **(FH) → (T)** (Delorme–Guichardet): via an `ℓ²`-direct sum `lp E 2` of counterexample
   representations and a 1-cocycle `c(g)_k = k (ρ_k(g) ξ_k - ξ_k)`, obtain a finite Kazhdan
   set `F ⊆ Γ` and constant `ε > 0`.
2. **Spectral gap of the Markov operator**: set `S = F ∪ F⁻¹ ∪ {1}` and
   `h = (1/2) (1 + (1/|S|) ∑_{g ∈ S} σ(g)) ∈ A`. In every Hilbert space *-representation `π`,
   `π(h)` fixes the `Γ`-invariant subspace `E₀` and satisfies `Re ⟪π(h) v, v⟫ ≤ (1 - δ) ‖v‖²`
   on `E₀ᗮ`, as well as `0 ≤ Re ⟪π(h) v, v⟫ ≤ ‖v‖²` everywhere.
3. **States & GNS**: every `λ ∈ spectrum ℝ a` of a self-adjoint element `a ∈ A` is attained by a
   state `f : A →ₚ[ℂ] ℂ` (via `isometry_cfcHom` and complex Hahn–Banach `exists_extension_norm_eq`),
   making `λ` an eigenvalue of `f.gnsStarAlgHom a`. Hence `spectrum ℝ h ⊆ [0, 1 - δ] ∪ {1}`.
4. **Kazhdan projection `p`**: by `cfc` on `h`, `p = cfc χ h = lim_{k → ∞} h^k` is a self-adjoint
   projection acting as the orthogonal projection onto `E₀` in every Hilbert space representation.
   By the same state/GNS argument, `σ(g) * p = p` for every `g ∈ Γ`.
5. **Conjugate projection `q = σ(t) * p * σ(t)⁻¹`**: since `t Γ t⁻¹ ⊆ Γ`, `q_h * p = p` where
   `q_h = σ(t) * h * σ(t)⁻¹`, whence `q * p = p` and (by taking `star`) `p * q = p`.
-/

namespace OMA.R_Green100_H3_R1_H2_Proof

open Filter Finset ContinuousLinearMap
open scoped Topology BigOperators ComplexOrder InnerProductSpace

/-! ### Part 1: Property (FH) implies Kazhdan Property (T) for countable groups -/

private lemma property_T_of_FH {Γ : Type} [Group Γ] [Countable Γ]
    (hFH : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (ρ : Γ →* E ≃ₗᵢ[ℂ] E) (c : Γ → E),
      (∀ g h, c (g * h) = c g + ρ g (c h)) → ∃ v : E, ∀ g, c g = ρ g v - v) :
    ∃ (F : Finset Γ) (ε : ℝ), 0 < ε ∧
      ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
        (ρ : Γ →* E ≃ₗᵢ[ℂ] E),
        (∀ v : E, (∀ g : Γ, ρ g v = v) → v = 0) →
        ∀ v : E, ∃ g ∈ F, ε * ‖v‖ ≤ ‖ρ g v - v‖ := by
  classical
  have hne : Nonempty Γ := ⟨1⟩
  obtain ⟨enum, henum⟩ := exists_surjective_nat Γ
  let F_seq : ℕ → Finset Γ := fun k => (Finset.range (k + 1)).image enum
  by_contra hno
  push Not at hno
  have hbad : ∀ k : ℕ, ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E)
      (_ : CompleteSpace E) (ρ : Γ →* E ≃ₗᵢ[ℂ] E),
      (∀ v : E, (∀ g : Γ, ρ g v = v) → v = 0) ∧
      ∃ ξ : E, ‖ξ‖ = 1 ∧ ∀ g ∈ F_seq k, ‖ρ g ξ - ξ‖ < (1 / 2 : ℝ) ^ k := by
    intro k
    obtain ⟨E, inst1, inst2, inst3, ρ, hnofix, v, hv⟩ :=
      hno (F_seq k) ((1 / 2 : ℝ) ^ k) (by positivity)
    have hv_ne : v ≠ 0 := by
      intro h0
      have hmem : enum 0 ∈ F_seq k :=
        Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ k), rfl⟩
      have := hv (enum 0) hmem
      simp [h0] at this
    have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
    refine ⟨E, inst1, inst2, inst3, ρ, hnofix, (‖v‖⁻¹ : ℂ) • v, ?_, fun g hg => ?_⟩
    · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg v)]
      exact inv_mul_cancel₀ (ne_of_gt hv_pos)
    · have hlin : ρ g ((‖v‖⁻¹ : ℂ) • v) - (‖v‖⁻¹ : ℂ) • v = (‖v‖⁻¹ : ℂ) • (ρ g v - v) := by
        rw [map_smul, smul_sub]
      rw [hlin, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg v)]
      have hlt := hv g hg
      calc ‖v‖⁻¹ * ‖ρ g v - v‖ < ‖v‖⁻¹ * ((1 / 2 : ℝ) ^ k * ‖v‖) :=
            mul_lt_mul_of_pos_left hlt (inv_pos.mpr hv_pos)
        _ = (1 / 2 : ℝ) ^ k := by field_simp [ne_of_gt hv_pos]
  let Ek : ℕ → Type := fun k => (hbad k).choose
  letI instNorm : ∀ k, NormedAddCommGroup (Ek k) := fun k => (hbad k).choose_spec.choose
  letI instIPS : ∀ k, InnerProductSpace ℂ (Ek k) := fun k => (hbad k).choose_spec.choose_spec.choose
  letI instComp : ∀ k, CompleteSpace (Ek k) :=
    fun k => (hbad k).choose_spec.choose_spec.choose_spec.choose
  let ρk : ∀ k, Γ →* Ek k ≃ₗᵢ[ℂ] Ek k :=
    fun k => (hbad k).choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hnofix : ∀ k (v : Ek k), (∀ g : Γ, ρk k g v = v) → v = 0 :=
    fun k => (hbad k).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1
  let ξk : ∀ k, Ek k :=
    fun k => (hbad k).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.choose
  have hξ_norm : ∀ k, ‖ξk k‖ = 1 :=
    fun k => (hbad k).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.choose_spec.1
  have hξ_approx : ∀ k, ∀ g ∈ F_seq k, ‖ρk k g (ξk k) - ξk k‖ < (1 / 2 : ℝ) ^ k :=
    fun k => (hbad k).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.choose_spec.2
  -- Build the `ℓ²`-direct sum `E := lp Ek 2` and diagonal unitary representation `ρ`
  let E := lp Ek 2
  have hmem_ρ : ∀ (g : Γ) (x : E), Memℓp (fun k => ρk k g (x k)) 2 := fun g x => by
    have hx := lp.memℓp x
    rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)] at hx ⊢
    simpa [LinearIsometryEquiv.norm_map] using hx
  let ρ_fun : Γ → E ≃ₗᵢ[ℂ] E := fun g =>
    { toFun := fun x => ⟨fun k => ρk k g (x k), hmem_ρ g x⟩
      invFun := fun x => ⟨fun k => (ρk k g).symm (x k), by
        have hx := lp.memℓp x
        change Memℓp (fun k => (ρk k g).symm (x k)) 2
        rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)] at hx ⊢
        simpa [LinearIsometryEquiv.norm_map] using hx⟩
      map_add' := fun x y => by ext k; exact map_add (ρk k g) (x k) (y k)
      map_smul' := fun a x => by ext k; exact map_smul (ρk k g) a (x k)
      left_inv := fun x => by ext k; exact (ρk k g).symm_apply_apply (x k)
      right_inv := fun x => by ext k; exact (ρk k g).apply_symm_apply (x k)
      norm_map' := fun x => by
        rw [lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal),
          lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
        congr 1; refine tsum_congr fun k => ?_
        change ‖ρk k g (x k)‖ ^ (2 : ENNReal).toReal = ‖x k‖ ^ (2 : ENNReal).toReal
        rw [LinearIsometryEquiv.norm_map] }
  let ρ : Γ →* E ≃ₗᵢ[ℂ] E :=
    { toFun := ρ_fun
      map_one' := by ext x k; change ρk k 1 (x k) = x k; simp
      map_mul' := fun g h => by
        ext x k; change ρk k (g * h) (x k) = ρk k g (ρk k h (x k)); simp }
  -- Build the 1-cocycle `c g k = (k : ℂ) • (ρk k g (ξk k) - ξk k)` in `lp Ek 2`
  have hc_mem : ∀ g : Γ, Memℓp (fun k => ((k : ℕ) : ℂ) • (ρk k g (ξk k) - ξk k)) 2 := fun g => by
    rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
    obtain ⟨K, hK⟩ := henum g
    have hbase : Summable (fun k : ℕ => (3 / 4 : ℝ) ^ k) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    refine Summable.of_norm_bounded_eventually_nat (g := fun k : ℕ => (3 / 4 : ℝ) ^ k) hbase ?_
    filter_upwards [eventually_ge_atTop (max K 4)] with k hk
    have hkK : K ≤ k := le_trans (le_max_left _ _) hk
    have hg_mem : g ∈ F_seq k :=
      Finset.mem_image.mpr ⟨K, Finset.mem_range.mpr (Nat.lt_succ_of_le hkK), hK⟩
    have hlt : ‖ρk k g (ξk k) - ξk k‖ < (1 / 2 : ℝ) ^ k := hξ_approx k g hg_mem
    have hnorm : ‖((k : ℕ) : ℂ) • (ρk k g (ξk k) - ξk k)‖ ≤ (k : ℝ) * (1 / 2 : ℝ) ^ k := by
      rw [norm_smul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left (le_of_lt hlt) (Nat.cast_nonneg k)
    have hto2 : (2 : ENNReal).toReal = (2 : ℝ) := by norm_num
    rw [Real.norm_of_nonneg (by positivity), hto2]
    have hpow_le : ‖((k : ℕ) : ℂ) • (ρk k g (ξk k) - ξk k)‖ ^ (2 : ℝ) ≤
        ((k : ℝ) * (1 / 2 : ℝ) ^ k) ^ (2 : ℝ) :=
      Real.rpow_le_rpow (norm_nonneg _) hnorm (by norm_num)
    have hsq : ((k : ℝ) * (1 / 2 : ℝ) ^ k) ^ (2 : ℝ) = (k : ℝ) ^ 2 * (1 / 4 : ℝ) ^ k := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, mul_pow, ← pow_mul,
        mul_comm k 2, pow_mul]
      norm_num
    have hk3 : k ^ 2 ≤ 3 ^ k := by
      clear hk hkK hg_mem hlt hnorm hpow_le hsq hbase
      induction k with
      | zero => norm_num
      | succ m ih =>
        rcases m with _ | _ | m
        · norm_num
        · norm_num
        · have h1 : (m + 2) ^ 2 ≤ 3 ^ (m + 2) := ih
          have h2 : 2 * (m + 2) + 1 ≤ 2 * (m + 2) ^ 2 := by nlinarith
          calc (m + 3) ^ 2 = (m + 2) ^ 2 + (2 * (m + 2) + 1) := by ring
            _ ≤ (m + 2) ^ 2 + 2 * (m + 2) ^ 2 := by omega
            _ = 3 * (m + 2) ^ 2 := by ring
            _ ≤ 3 * 3 ^ (m + 2) := by omega
            _ = 3 ^ (m + 3) := by ring
    have hk3' : (k : ℝ) ^ 2 ≤ (3 : ℝ) ^ k := by exact_mod_cast hk3
    calc ‖((k : ℕ) : ℂ) • (ρk k g (ξk k) - ξk k)‖ ^ (2 : ℝ)
        ≤ ((k : ℝ) * (1 / 2 : ℝ) ^ k) ^ (2 : ℝ) := hpow_le
      _ = (k : ℝ) ^ 2 * (1 / 4 : ℝ) ^ k := hsq
      _ ≤ (3 : ℝ) ^ k * (1 / 4 : ℝ) ^ k := mul_le_mul_of_nonneg_right hk3' (by positivity)
      _ = (3 / 4 : ℝ) ^ k := by rw [← mul_pow]; norm_num
  let c : Γ → E := fun g => ⟨fun k => ((k : ℕ) : ℂ) • (ρk k g (ξk k) - ξk k), hc_mem g⟩
  have hc_cocycle : ∀ g h : Γ, c (g * h) = c g + ρ g (c h) := by
    intro g h
    ext k
    change ((k : ℕ) : ℂ) • (ρk k (g * h) (ξk k) - ξk k) =
      ((k : ℕ) : ℂ) • (ρk k g (ξk k) - ξk k) +
        ρk k g (((k : ℕ) : ℂ) • (ρk k h (ξk k) - ξk k))
    rw [map_smul, map_sub, map_mul]
    change ((k : ℕ) : ℂ) • (ρk k g (ρk k h (ξk k)) - ξk k) =
      ((k : ℕ) : ℂ) • (ρk k g (ξk k) - ξk k) +
        ((k : ℕ) : ℂ) • (ρk k g (ρk k h (ξk k)) - ρk k g (ξk k))
    rw [← smul_add]
    congr 1
    abel
  obtain ⟨v, hv⟩ := hFH E ρ c hc_cocycle
  have hv_eq : ∀ k : ℕ, v k = ((k : ℕ) : ℂ) • ξk k := by
    intro k
    have hfix : ∀ g : Γ, ρk k g (v k - ((k : ℕ) : ℂ) • ξk k) = v k - ((k : ℕ) : ℂ) • ξk k := by
      intro g
      have hgk := congrArg (fun x : E => x k) (hv g)
      change ((k : ℕ) : ℂ) • (ρk k g (ξk k) - ξk k) = ρk k g (v k) - v k at hgk
      rw [smul_sub] at hgk
      rw [map_sub, map_smul]
      -- `k • ρ g ξ - k • ξ = ρ g v - v` ⇒ `ρ g v - k • ρ g ξ = v - k • ξ`
      calc ρk k g (v k) - ((k : ℕ) : ℂ) • ρk k g (ξk k)
          = (ρk k g (v k) - v k) + v k - ((k : ℕ) : ℂ) • ρk k g (ξk k) := by abel
        _ = (((k : ℕ) : ℂ) • ρk k g (ξk k) - ((k : ℕ) : ℂ) • ξk k) + v k -
              ((k : ℕ) : ℂ) • ρk k g (ξk k) := by rw [← hgk]
        _ = v k - ((k : ℕ) : ℂ) • ξk k := by abel
    exact sub_eq_zero.mp (hnofix k _ hfix)
  -- Contradiction: `v ∈ lp Ek 2` implies `‖v k‖ ^ 2 → 0`, yet `‖v k‖ = k`!
  have hv_mem := lp.memℓp v
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)] at hv_mem
  have hlim : Tendsto (fun k : ℕ => ‖v k‖ ^ (2 : ENNReal).toReal) atTop (𝓝 0) :=
    hv_mem.tendsto_atTop_zero
  have hev := (tendsto_order.mp hlim).2 (1 : ℝ) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have h1 := hN (max N 1) (le_max_left N 1)
  have hge1 : 1 ≤ max N 1 := le_max_right N 1
  have hnorm_v : ‖v (max N 1)‖ = ((max N 1 : ℕ) : ℝ) := by
    rw [hv_eq, norm_smul, Complex.norm_natCast, hξ_norm, mul_one]
  rw [hnorm_v, show (2 : ENNReal).toReal = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h1
  have hge1' : (1 : ℝ) ≤ ((max N 1 : ℕ) : ℝ) := by exact_mod_cast hge1
  nlinarith

/-! ### Part 2: Contractivity of *-homomorphisms, states, and GNS eigenvectors -/

private lemma starAlgHom_norm_le {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (π : A →⋆ₐ[ℂ] B) (a : A) : ‖π a‖ ≤ ‖a‖ := by
  by_cases hnt : Nontrivial A
  · have ha : IsSelfAdjoint (star a * a) := IsSelfAdjoint.star_mul_self a
    have hπa : IsSelfAdjoint (π (star a * a)) := ha.map π
    have hsub : spectrum ℝ (π (star a * a)) ⊆ spectrum ℝ (star a * a) :=
      AlgHom.spectrum_apply_subset (π.restrictScalars ℝ) (star a * a)
    have hsr : spectralRadius ℝ (π (star a * a)) ≤ spectralRadius ℝ (star a * a) := by
      simp only [spectralRadius]
      exact iSup₂_le fun x hx => le_iSup₂_of_le x (hsub hx) le_rfl
    have hfin : spectralRadius ℝ (star a * a) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top (spectrum.spectralRadius_le_nnnorm (star a * a))
    have hsq : ‖π a‖ ^ 2 ≤ ‖a‖ ^ 2 := by
      rw [sq, sq, ← CStarRing.norm_star_mul_self (x := π a), ← CStarRing.norm_star_mul_self (x := a),
        ← map_star, ← map_mul, ← hπa.toReal_spectralRadius_eq_norm, ← ha.toReal_spectralRadius_eq_norm]
      exact ENNReal.toReal_mono hfin hsr
    nlinarith [norm_nonneg (π a), norm_nonneg a]
  · rw [not_nontrivial_iff_subsingleton] at hnt
    rw [Subsingleton.elim a 0]
    simp

/-- A contractive functional `g : StrongDual ℂ A` with `g 1 = 1` on a unital C*-algebra is a
positive linear map (a state). -/
private noncomputable def stateOfNormLeOne {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
    (g : StrongDual ℂ A) (hg_norm : ‖g‖ ≤ 1) (hg_one : g 1 = 1) : A →ₚ[ℂ] ℂ := by
  have him_zero : ∀ x : A, IsSelfAdjoint x → (g x).im = 0 := by
    intro x hx
    set u := (g x).re
    set v := (g x).im
    by_contra hv
    let t : ℝ := ((‖x‖ ^ 2 + 1) * v) / (2 * v ^ 2)
    let y : A := x + ((t : ℂ) * Complex.I) • (1 : A)
    have hstar_y : star y * y = x * x + ((t ^ 2 : ℝ) : ℂ) • (1 : A) := by
      have hst : star y = x - ((t : ℂ) * Complex.I) • (1 : A) := by
        simp only [y, star_add, star_smul, hx.star_eq, star_one, star_mul',
          Complex.star_def, Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_smul, sub_eq_add_neg]
      rw [hst]
      have hcomm : x * (((t : ℂ) * Complex.I) • (1 : A)) =
          (((t : ℂ) * Complex.I) • (1 : A)) * x := by
        simp [smul_mul_assoc]
      have hsqI : (((t : ℂ) * Complex.I) • (1 : A)) * (((t : ℂ) * Complex.I) • (1 : A)) =
          -(((t ^ 2 : ℝ) : ℂ) • (1 : A)) := by
        rw [smul_mul_smul_comm, mul_one, ← neg_smul]
        congr 1
        push_cast
        ring_nf
        rw [Complex.I_sq]
        ring
      calc (x - ((t : ℂ) * Complex.I) • (1 : A)) * (x + ((t : ℂ) * Complex.I) • (1 : A))
          = x * x + x * (((t : ℂ) * Complex.I) • (1 : A)) -
              (((t : ℂ) * Complex.I) • (1 : A)) * x -
              (((t : ℂ) * Complex.I) • (1 : A)) * (((t : ℂ) * Complex.I) • (1 : A)) := by
            simp only [sub_mul, mul_add]
            abel
        _ = x * x - -(((t ^ 2 : ℝ) : ℂ) • (1 : A)) := by rw [hcomm, hsqI]; abel
        _ = x * x + ((t ^ 2 : ℝ) : ℂ) • (1 : A) := by abel
    have hy_sq : ‖y‖ ^ 2 ≤ ‖x‖ ^ 2 + t ^ 2 := by
      rw [sq, ← CStarRing.norm_star_mul_self, hstar_y]
      have h1_le : ‖(1 : A)‖ ≤ 1 := by
        by_cases hnt : Nontrivial A
        · rw [norm_one]
        · rw [not_nontrivial_iff_subsingleton] at hnt
          rw [Subsingleton.elim (1 : A) 0, norm_zero]; norm_num
      calc ‖x * x + ((t ^ 2 : ℝ) : ℂ) • (1 : A)‖
          ≤ ‖x * x‖ + ‖((t ^ 2 : ℝ) : ℂ) • (1 : A)‖ := norm_add_le _ _
        _ ≤ ‖x‖ * ‖x‖ + ‖((t ^ 2 : ℝ) : ℂ)‖ * ‖(1 : A)‖ := by
            gcongr; exact norm_mul_le x x; rw [norm_smul]
        _ ≤ ‖x‖ ^ 2 + t ^ 2 * 1 := by
            rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg t), ← sq]
            gcongr
        _ = ‖x‖ ^ 2 + t ^ 2 := by ring
    have hgy : g y = g x + (t : ℂ) * Complex.I := by
      simp [y, map_add, map_smul, hg_one]
    have hgy_norm : u ^ 2 + (v + t) ^ 2 ≤ ‖y‖ ^ 2 := by
      have hle : ‖g y‖ ≤ ‖y‖ :=
        (g.le_opNorm y).trans (by nlinarith [norm_nonneg y])
      have hsq_le : ‖g y‖ ^ 2 ≤ ‖y‖ ^ 2 :=
        sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hle
      have hns : ‖g y‖ ^ 2 = u ^ 2 + (v + t) ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hgy]
        simp [u, v, sq]
      linarith
    have h2vt : 2 * v * t = ‖x‖ ^ 2 + 1 := by
      dsimp only [t]
      have hv2 : (2 * v ^ 2 : ℝ) ≠ 0 := by positivity
      field_simp [hv]
    nlinarith [sq_nonneg u, sq_nonneg v]
  have hnonneg : ∀ a : A, 0 ≤ a → 0 ≤ g a := by
    intro a ha
    have hsa : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha
    have him : (g a).im = 0 := him_zero a hsa
    -- `‖‖a‖ • 1 - a‖ ≤ ‖a‖` by `norm_cfc_le` since `spectrum ℝ a ⊆ [0, ‖a‖]`
    have hdiff_eq : (‖a‖ : ℝ) • (1 : A) - a = cfc (fun x : ℝ => ‖a‖ - x) a := by
      rw [cfc_sub (fun _ => ‖a‖) (fun x : ℝ => x) a, cfc_const ‖a‖ a hsa, cfc_id' ℝ a,
        Algebra.algebraMap_eq_smul_one]
    have hdiff_le : ‖(‖a‖ : ℝ) • (1 : A) - a‖ ≤ ‖a‖ := by
      by_cases hnt : Nontrivial A
      · rw [hdiff_eq]
        refine norm_cfc_le (norm_nonneg a) fun x hx => ?_
        have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg ha hx
        have hxn : x ≤ ‖a‖ := by
          have := spectrum.norm_le_norm_of_mem hx
          rw [Real.norm_eq_abs] at this
          exact le_trans (le_abs_self x) this
        rw [Real.norm_of_nonneg (by linarith)]
        linarith
      · rw [not_nontrivial_iff_subsingleton] at hnt
        rw [Subsingleton.elim ((‖a‖ : ℝ) • (1 : A) - a) 0, norm_zero]
        exact norm_nonneg a
    have hgd : ‖(‖a‖ : ℂ) - g a‖ ≤ ‖a‖ := by
      have h1 : g ((‖a‖ : ℝ) • (1 : A) - a) = (‖a‖ : ℂ) - g a := by
        rw [map_sub, ← Complex.coe_smul, map_smul, hg_one, smul_eq_mul, mul_one]
      rw [← h1]
      exact (g.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hg_norm).trans hdiff_le)
    have hre_le : |‖a‖ - (g a).re| ≤ ‖a‖ := by
      have hsub_eq : (‖a‖ : ℂ) - g a = ((‖a‖ - (g a).re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [him]
      rw [hsub_eq, Complex.norm_real, Real.norm_eq_abs] at hgd
      exact hgd
    have hre : 0 ≤ (g a).re := by linarith [(abs_le.mp hre_le).2]
    exact RCLike.nonneg_iff.mpr ⟨hre, him⟩
  exact
    { toFun := g
      map_add' := g.map_add
      map_smul' := g.map_smul
      monotone' := fun a b hab => by
        have h0 : 0 ≤ b - a := sub_nonneg.mpr hab
        have h1 : 0 ≤ g (b - a) := hnonneg (b - a) h0
        rw [map_sub] at h1
        exact sub_nonneg.mp h1 }

/-- For any self-adjoint element `a` in a unital C*-algebra `A` and `λ ∈ spectrum ℝ a`, there
exists a state `f : A →ₚ[ℂ] ℂ` with `f 1 = 1`, `f a = λ`, `f (a * a) = λ²`, so that `λ` is an
actual eigenvalue of `f.gnsStarAlgHom a` with unit eigenvector `ζ = f.toPreGNS 1`. -/
private lemma exists_state_gns_eigenvector {A : Type} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
    {a : A} (ha : IsSelfAdjoint a) {lam : ℝ} (hlam : lam ∈ spectrum ℝ a) :
    ∃ (f : A →ₚ[ℂ] ℂ), f 1 = 1 ∧ f a = (lam : ℂ) ∧ f (a * a) = ((lam ^ 2 : ℝ) : ℂ) ∧
      ∃ ζ : f.GNS, ‖ζ‖ = 1 ∧ f.gnsStarAlgHom a ζ = (lam : ℂ) • ζ := by
  classical
  have hnorm_a : IsStarNormal a := ha.isStarNormal
  have hlamC : (lam : ℂ) ∈ spectrum ℂ a := by
    simpa using (spectrum.algebraMap_mem ℂ hlam : algebraMap ℝ ℂ lam ∈ spectrum ℂ a)
  let ψ : C(spectrum ℂ a, ℂ) →⋆ₐ[ℂ] A := cfcHom (R := ℂ) hnorm_a
  have hψ_iso : Isometry ψ := isometry_cfcHom a hnorm_a
  have hψ_inj : Function.Injective ψ := hψ_iso.injective
  let P : Subspace ℂ A := LinearMap.range ψ.toLinearMap
  let invP : P → C(spectrum ℂ a, ℂ) := fun y => y.2.choose
  have hψ_invP : ∀ y : P, ψ (invP y) = y.1 := fun y => y.2.choose_spec
  have hinvP_ψ : ∀ φ : C(spectrum ℂ a, ℂ), invP ⟨ψ φ, ⟨φ, rfl⟩⟩ = φ := fun φ =>
    hψ_inj (hψ_invP ⟨ψ φ, ⟨φ, rfl⟩⟩)
  have hinvP_add : ∀ y₁ y₂ : P, invP (y₁ + y₂) = invP y₁ + invP y₂ := fun y₁ y₂ =>
    hψ_inj (by rw [hψ_invP, map_add, hψ_invP, hψ_invP]; rfl)
  have hinvP_smul : ∀ (c : ℂ) (y : P), invP (c • y) = c • invP y := fun c y =>
    hψ_inj (by rw [hψ_invP, map_smul, hψ_invP]; rfl)
  have hinvP_norm : ∀ y : P, ‖invP y‖ = ‖y‖ := fun y => by
    have := hψ_iso.norm_map_of_map_zero (map_zero ψ) (invP y)
    rw [hψ_invP] at this
    exact this.symm
  let pt : spectrum ℂ a := ⟨(lam : ℂ), hlamC⟩
  let φ₀_lin : P →ₗ[ℂ] ℂ :=
    { toFun := fun y => invP y pt
      map_add' := fun y₁ y₂ => by rw [hinvP_add]; rfl
      map_smul' := fun c y => by rw [hinvP_smul]; rfl }
  let φ₀ : StrongDual ℂ P := φ₀_lin.mkContinuous 1 fun y => by
    rw [one_mul, ← hinvP_norm y]
    exact ContinuousMap.norm_coe_le_norm (invP y) pt
  have hφ₀_norm : ‖φ₀‖ ≤ 1 := φ₀_lin.mkContinuous_norm_le (by norm_num) _
  obtain ⟨g, hg_ext, hg_norm_eq⟩ := exists_extension_norm_eq P φ₀
  have hg_norm : ‖g‖ ≤ 1 := hg_norm_eq.le.trans hφ₀_norm
  have h1_mem : (1 : A) ∈ P := ⟨1, map_one ψ⟩
  have hg_one : g 1 = 1 := by
    have := hg_ext ⟨1, h1_mem⟩
    change g 1 = invP ⟨1, h1_mem⟩ pt at this
    have hinv1 : invP ⟨1, h1_mem⟩ = 1 := hψ_inj (by rw [hψ_invP, map_one])
    rw [this, hinv1]
    rfl
  let idC : C(spectrum ℂ a, ℂ) := ContinuousMap.restrict (spectrum ℂ a) (ContinuousMap.id ℂ)
  have hψ_id : ψ idC = a := cfcHom_id (R := ℂ) hnorm_a
  have ha_mem : a ∈ P := ⟨idC, hψ_id⟩
  have hg_a : g a = (lam : ℂ) := by
    have := hg_ext ⟨a, ha_mem⟩
    change g a = invP ⟨a, ha_mem⟩ pt at this
    have hinva : invP ⟨a, ha_mem⟩ = idC := hψ_inj (by rw [hψ_invP, hψ_id])
    rw [this, hinva]
    rfl
  have haa_mem : a * a ∈ P := ⟨idC * idC, by show ψ (idC * idC) = a * a; rw [map_mul, hψ_id]⟩
  have hg_aa : g (a * a) = ((lam ^ 2 : ℝ) : ℂ) := by
    have := hg_ext ⟨a * a, haa_mem⟩
    change g (a * a) = invP ⟨a * a, haa_mem⟩ pt at this
    have hinvaa : invP ⟨a * a, haa_mem⟩ = idC * idC :=
      hψ_inj (by rw [hψ_invP, map_mul, hψ_id])
    rw [this, hinvaa]
    change (lam : ℂ) * (lam : ℂ) = ((lam ^ 2 : ℝ) : ℂ)
    push_cast; ring
  let f : A →ₚ[ℂ] ℂ := stateOfNormLeOne g hg_norm hg_one
  have hf_eq : ∀ x : A, f x = g x := fun _ => rfl
  let ζ : f.GNS := (f.toPreGNS 1 : f.PreGNS)
  have hζ_norm : ‖ζ‖ = 1 := by
    have hsq : ‖f.toPreGNS 1‖ ^ 2 = 1 := by
      have h1 := f.preGNS_norm_sq (f.toPreGNS 1)
      simp only [PositiveLinearMap.ofPreGNS_toPreGNS, star_one, mul_one, hf_eq, hg_one] at h1
      rw [← Complex.ofReal_pow] at h1
      exact_mod_cast h1
    rw [UniformSpace.Completion.norm_coe]
    nlinarith [norm_nonneg (f.toPreGNS 1)]
  have hζ_eig : f.gnsStarAlgHom a ζ = (lam : ℂ) • ζ := by
    rw [← sub_eq_zero, ← norm_eq_zero]
    have hsub : f.gnsStarAlgHom a ζ - (lam : ℂ) • ζ =
        ((f.toPreGNS (a - (lam : ℂ) • 1) : f.PreGNS) : f.GNS) := by
      have hact : f.gnsStarAlgHom a ζ = ((f.leftMulMapPreGNS a (f.toPreGNS 1) : f.PreGNS) : f.GNS) :=
        PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe f
      rw [hact]
      change ((f.leftMulMapPreGNS a (f.toPreGNS 1) : f.PreGNS) : f.GNS) -
        (lam : ℂ) • ((f.toPreGNS 1 : f.PreGNS) : f.GNS) = _
      rw [← UniformSpace.Completion.coe_smul, ← UniformSpace.Completion.coe_sub]
      congr 1
      have hmul1 : f.leftMulMapPreGNS a (f.toPreGNS 1) = f.toPreGNS a := by
        apply f.ofPreGNS.injective
        simp [PositiveLinearMap.leftMulMapPreGNS]
      rw [hmul1, ← map_smul, ← map_sub]
    rw [hsub, UniformSpace.Completion.norm_coe]
    have hsq0 : ‖f.toPreGNS (a - (lam : ℂ) • 1)‖ ^ 2 = 0 := by
      have h1 := f.preGNS_norm_sq (f.toPreGNS (a - (lam : ℂ) • 1))
      simp only [PositiveLinearMap.ofPreGNS_toPreGNS] at h1
      have hexp : star (a - (lam : ℂ) • (1 : A)) * (a - (lam : ℂ) • (1 : A)) =
          a * a - ((2 * lam : ℝ) : ℂ) • a + ((lam ^ 2 : ℝ) : ℂ) • (1 : A) := by
        rw [star_sub, ha.star_eq, star_smul, star_one, Complex.star_def, Complex.conj_ofReal]
        have h1' : (a - (lam : ℂ) • (1 : A)) * (a - (lam : ℂ) • (1 : A)) =
            a * a - (lam : ℂ) • a - (lam : ℂ) • a + ((lam : ℂ) * (lam : ℂ)) • (1 : A) := by
          rw [sub_mul, mul_sub, mul_sub, smul_mul_assoc, one_mul, mul_smul_comm, mul_one,
            smul_mul_smul_comm, one_mul]
          abel
        rw [h1']
        have h2 : ((2 * lam : ℝ) : ℂ) • a = (lam : ℂ) • a + (lam : ℂ) • a := by
          rw [← add_smul]; congr 1; push_cast; ring
        have h3 : ((lam ^ 2 : ℝ) : ℂ) • (1 : A) = ((lam : ℂ) * (lam : ℂ)) • (1 : A) := by
          congr 1; push_cast; ring
        rw [h2, h3]; abel
      rw [hexp, hf_eq] at h1
      have hg_eval : g (a * a - ((2 * lam : ℝ) : ℂ) • a + ((lam ^ 2 : ℝ) : ℂ) • (1 : A)) =
          ((lam ^ 2 : ℝ) : ℂ) - ((2 * lam : ℝ) : ℂ) * (lam : ℂ) + ((lam ^ 2 : ℝ) : ℂ) := by
        rw [map_add, map_sub, map_smul, map_smul, hg_aa, hg_a, hg_one]
        simp [smul_eq_mul]
      rw [hg_eval] at h1
      rw [← Complex.ofReal_pow] at h1
      have hre := congrArg Complex.re h1
      simp only [Complex.ofReal_re, Complex.add_re, Complex.sub_re,
        Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero] at hre
      linarith
    nlinarith [norm_nonneg (f.toPreGNS (a - (lam : ℂ) • 1))]
  exact ⟨f, by rw [hf_eq, hg_one], by rw [hf_eq, hg_a], by rw [hf_eq, hg_aa], ζ, hζ_norm, hζ_eig⟩

/-! ### Part 3: Unitary action helpers and Markov operator quadratic form -/

private lemma starAlgHom_unitary_norm {G A E : Type*} [Group G] [CStarAlgebra A]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (σ : G →* unitary A) (π : A →⋆ₐ[ℂ] (E →L[ℂ] E)) (g : G) (v : E) :
    ‖π (σ g : A) v‖ = ‖v‖ := by
  have h1 : ⟪π (σ g : A) v, π (σ g : A) v⟫_ℂ = ⟪v, v⟫_ℂ := by
    have hadj : ⟪π (σ g : A) v, π (σ g : A) v⟫_ℂ =
        ⟪v, (ContinuousLinearMap.adjoint (π (σ g : A)) * π (σ g : A)) v⟫_ℂ := by
      rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.adjoint_inner_right]
    rw [hadj, ← ContinuousLinearMap.star_eq_adjoint, ← map_star, ← map_mul]
    have hu : star (σ g : A) * (σ g : A) = 1 := Unitary.coe_star_mul_self (σ g)
    rw [hu, map_one, one_apply_eq_self]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
  have hsq : ‖π (σ g : A) v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast h1
  nlinarith [norm_nonneg (π (σ g : A) v), norm_nonneg v]

private lemma starAlgHom_unitary_inv {G A : Type*} [Group G] [CStarAlgebra A]
    (σ : G →* unitary A) (g : G) :
    star (σ g : A) = (σ g⁻¹ : A) := by
  have h1 : σ g⁻¹ = (σ g)⁻¹ := map_inv σ g
  rw [h1, ← Unitary.star_eq_inv]
  rfl

private lemma norm_sub_sq_unitary {G A E : Type*} [Group G] [CStarAlgebra A]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (σ : G →* unitary A) (π : A →⋆ₐ[ℂ] (E →L[ℂ] E)) (g : G) (v : E) :
    (⟪π (σ g : A) v, v⟫_ℂ).re = ‖v‖ ^ 2 - (1 / 2 : ℝ) * ‖π (σ g : A) v - v‖ ^ 2 := by
  have h := norm_sub_sq (𝕜 := ℂ) (π (σ g : A) v) v
  rw [starAlgHom_unitary_norm σ π g v] at h
  change ‖π (σ g : A) v - v‖ ^ 2 = ‖v‖ ^ 2 - 2 * (⟪π (σ g : A) v, v⟫_ℂ).re + ‖v‖ ^ 2 at h
  linarith

/-! ### Part 4: Main theorem (`OMA.solution`) -/

private theorem main_proof :
    OMA.R_Green100_green_100_variants_operator_norm_R1_H3_R1.H2 := by
  classical
  intro G _ _ Γ hFH t hsub A _ σ
  -- Trivial degenerate case: `Subsingleton A`
  by_cases hsubA : Subsingleton A
  · refine ⟨0, 0, by simp, by simp, by simp, ⟨1, by simp⟩, ?_⟩
    intro E _ _ _ π v
    have h01 : (0 : A) = 1 := Subsingleton.elim 0 1
    have hπ0 : π 0 = 1 := by rw [h01, map_one]
    have hπall : ∀ x : A, π x = 1 := fun x => by rw [Subsingleton.elim x 1, map_one]
    constructor
    · constructor
      · intro _ g _; rw [hπall, one_apply_eq_self]
      · intro _; rw [hπ0, one_apply_eq_self]
    · constructor
      · intro _ g _; rw [hπall, one_apply_eq_self]
      · intro _; rw [hπ0, one_apply_eq_self]
  haveI : Nontrivial A := not_subsingleton_iff_nontrivial.mp hsubA
  -- Step 1: Extract Kazhdan pair `(F, ε)` for `Γ` from Property (FH)
  obtain ⟨F, ε, hε_pos, hKaz⟩ := property_T_of_FH hFH
  let S : Finset Γ := F ∪ F.image (·⁻¹) ∪ {1}
  have h1_mem_S : (1 : Γ) ∈ S := by simp [S]
  have hS_pos : (0 : ℝ) < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, h1_mem_S⟩
  have hS_ne : (S.card : ℝ) ≠ 0 := ne_of_gt hS_pos
  have hF_sub_S : F ⊆ S := fun g hg => by simp [S, hg]
  have hS_inv : ∀ g : Γ, g ∈ S ↔ g⁻¹ ∈ S := by
    intro g
    simp only [S, Finset.mem_union, Finset.mem_image, Finset.mem_singleton, inv_eq_one]
    constructor
    · rintro ((hg | ⟨x, hx, rfl⟩) | rfl)
      · exact Or.inl (Or.inr ⟨g, hg, rfl⟩)
      · rw [inv_inv]; exact Or.inl (Or.inl hx)
      · exact Or.inr rfl
    · rintro ((hg | ⟨x, hx, hxinv⟩) | rfl)
      · exact Or.inl (Or.inr ⟨g⁻¹, hg, inv_inv g⟩)
      · have : g = x := by rw [← inv_inv g, ← hxinv, inv_inv]
        subst this; exact Or.inl (Or.inl hx)
      · exact Or.inr rfl
  -- Step 2: Define the symmetric Markov operator `h ∈ A`
  let h : A := ((1 / 2 : ℝ) : ℂ) •
    ((1 : A) + (((S.card : ℝ)⁻¹ : ℝ) : ℂ) • ∑ g ∈ S, (σ (g : G) : A))
  have hh_sa : IsSelfAdjoint h := by
    rw [IsSelfAdjoint]
    simp only [h, star_smul, star_add, star_one, star_sum, Complex.star_def, Complex.conj_ofReal]
    congr 2
    congr 1
    have hsum : ∑ g ∈ S, star (σ (g : G) : A) = ∑ g ∈ S, (σ (g : G) : A) := by
      refine Finset.sum_bij (fun g _ => g⁻¹) ?_ ?_ ?_ ?_
      · intro g hg; exact (hS_inv g).mp hg
      · intro g₁ _ g₂ _ heq; exact inv_injective heq
      · intro g hg; exact ⟨g⁻¹, (hS_inv g).mp hg, inv_inv g⟩
      · intro g _; exact starAlgHom_unitary_inv σ (g : G)
    exact hsum
  -- Step 3: Quadratic form estimates for `π h` in ANY Hilbert space representation `π`
  let δ : ℝ := min (1 / 2 : ℝ) (ε ^ 2 / (4 * (S.card : ℝ)))
  have hδ_pos : 0 < δ :=
    lt_min (by norm_num) (div_pos (pow_pos hε_pos 2) (mul_pos (by norm_num) hS_pos))
  have hδ_le_half : δ ≤ 1 / 2 := min_le_left _ _
  have hδ_le_gap : δ ≤ ε ^ 2 / (4 * (S.card : ℝ)) := min_le_right _ _
  have hquad_eq : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (π : A →⋆ₐ[ℂ] (E →L[ℂ] E)) (v : E),
      (⟪π h v, v⟫_ℂ).re =
        ‖v‖ ^ 2 - (1 / (4 * (S.card : ℝ))) * ∑ g ∈ S, ‖π (σ (g : G) : A) v - v‖ ^ 2 := by
    intro E _ _ _ π v
    have hπh : π h v = ((1 / 2 : ℝ) : ℂ) •
        (v + (((S.card : ℝ)⁻¹ : ℝ) : ℂ) • ∑ g ∈ S, π (σ (g : G) : A) v) := by
      simp only [h, map_smul, map_add, map_one, map_sum, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.add_apply, one_apply_eq_self, ContinuousLinearMap.sum_apply]
    rw [hπh, inner_smul_left, inner_add_left, inner_smul_left, sum_inner]
    have hvv_re : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := by
      have h1 : ⟪v, v⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
      rw [h1, Complex.ofReal_re]
    simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.add_re, Complex.re_sum, hvv_re]
    have hsum : ∑ g ∈ S, (⟪π (σ (g : G) : A) v, v⟫_ℂ).re =
        (S.card : ℝ) * ‖v‖ ^ 2 - (1 / 2 : ℝ) * ∑ g ∈ S, ‖π (σ (g : G) : A) v - v‖ ^ 2 := by
      have h1 : ∀ g ∈ S, (⟪π (σ (g : G) : A) v, v⟫_ℂ).re =
          ‖v‖ ^ 2 - (1 / 2 : ℝ) * ‖π (σ (g : G) : A) v - v‖ ^ 2 :=
        fun g _ => norm_sub_sq_unitary σ π (g : G) v
      rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Finset.mul_sum]
    rw [hsum]
    field_simp [hS_ne]
    ring
  have hquad_nonneg : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (π : A →⋆ₐ[ℂ] (E →L[ℂ] E)) (v : E), 0 ≤ (⟪π h v, v⟫_ℂ).re := by
    intro E _ _ _ π v
    rw [hquad_eq π v]
    have hterm : ∀ g ∈ S, ‖π (σ (g : G) : A) v - v‖ ^ 2 ≤ 4 * ‖v‖ ^ 2 := by
      intro g _
      have h1 : ‖π (σ (g : G) : A) v - v‖ ≤ 2 * ‖v‖ := by
        calc ‖π (σ (g : G) : A) v - v‖
            ≤ ‖π (σ (g : G) : A) v‖ + ‖v‖ := norm_sub_le _ _
          _ = ‖v‖ + ‖v‖ := by rw [starAlgHom_unitary_norm]
          _ = 2 * ‖v‖ := by ring
      nlinarith [norm_nonneg (π (σ (g : G) : A) v - v), norm_nonneg v]
    have hsum_le : ∑ g ∈ S, ‖π (σ (g : G) : A) v - v‖ ^ 2 ≤ (S.card : ℝ) * (4 * ‖v‖ ^ 2) := by
      calc ∑ g ∈ S, ‖π (σ (g : G) : A) v - v‖ ^ 2
          ≤ ∑ _g ∈ S, (4 * ‖v‖ ^ 2) := Finset.sum_le_sum hterm
        _ = (S.card : ℝ) * (4 * ‖v‖ ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
    have hmul : (1 / (4 * (S.card : ℝ))) * ∑ g ∈ S, ‖π (σ (g : G) : A) v - v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
      calc (1 / (4 * (S.card : ℝ))) * ∑ g ∈ S, ‖π (σ (g : G) : A) v - v‖ ^ 2
          ≤ (1 / (4 * (S.card : ℝ))) * ((S.card : ℝ) * (4 * ‖v‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hsum_le
              (div_nonneg zero_le_one (mul_nonneg (by norm_num) hS_pos.le))
        _ = ‖v‖ ^ 2 := by field_simp [hS_ne]
    linarith
  have hquad_perp : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (π : A →⋆ₐ[ℂ] (E →L[ℂ] E)) (v : E),
      (∀ w : E, (∀ g : Γ, π (σ (g : G) : A) w = w) → ⟪w, v⟫_ℂ = 0) →
      (⟪π h v, v⟫_ℂ).re ≤ (1 - δ) * ‖v‖ ^ 2 := by
    intro E _ _ _ π v hv_perp
    -- Define the closed `Γ`-invariant subspace `E₀` and work on `E₀ᗮ`
    let E₀ : Submodule ℂ E :=
      { carrier := {w : E | ∀ g : Γ, π (σ (g : G) : A) w = w}
        add_mem' := fun {x y} hx hy g => by rw [map_add, hx g, hy g]
        zero_mem' := fun g => map_zero _
        smul_mem' := fun c x hx g => by rw [map_smul, hx g] }
    have hE₀_closed : IsClosed (E₀ : Set E) := by
      have heq : (E₀ : Set E) = ⋂ g : Γ, {w : E | π (σ (g : G) : A) w = w} := by
        ext w; simp [E₀]
      rw [heq]
      exact isClosed_iInter fun g => isClosed_eq (π (σ (g : G) : A)).continuous continuous_id
    have hE₀_perp_closed : IsClosed (E₀ᗮ : Set E) := E₀.isClosed_orthogonal
    haveI : CompleteSpace (E₀ᗮ : Type) := hE₀_perp_closed.completeSpace_coe
    have hinv_perp : ∀ (g : Γ) (u : E₀ᗮ), π (σ (g : G) : A) u.1 ∈ E₀ᗮ := by
      intro g u
      rw [Submodule.mem_orthogonal]
      intro w hw
      have hadj : ⟪w, π (σ (g : G) : A) u.1⟫_ℂ =
          ⟪ContinuousLinearMap.adjoint (π (σ (g : G) : A)) w, u.1⟫_ℂ :=
        (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
      rw [hadj, ← ContinuousLinearMap.star_eq_adjoint, ← map_star,
        starAlgHom_unitary_inv σ (g : G)]
      have hwinv : π (σ ((g⁻¹ : Γ) : G) : A) w = w := hw g⁻¹
      rw [show (g : G)⁻¹ = ((g⁻¹ : Γ) : G) from rfl, hwinv]
      exact (Submodule.mem_orthogonal E₀ u.1).mp u.2 w hw
    let ρp_fun : Γ → (E₀ᗮ ≃ₗᵢ[ℂ] E₀ᗮ) := fun g =>
      { toFun := fun u => ⟨π (σ (g : G) : A) u.1, hinv_perp g u⟩
        invFun := fun u => ⟨π (σ ((g⁻¹ : Γ) : G) : A) u.1, hinv_perp g⁻¹ u⟩
        map_add' := fun u₁ u₂ => by ext; exact map_add _ u₁.1 u₂.1
        map_smul' := fun c u => by ext; exact map_smul _ c u.1
        left_inv := fun u => by
          ext; change π (σ ((g⁻¹ : Γ) : G) : A) (π (σ (g : G) : A) u.1) = u.1
          rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← Submonoid.coe_mul, ← map_mul,
            Subgroup.coe_inv, inv_mul_cancel, map_one, Submonoid.coe_one, map_one,
            one_apply_eq_self]
        right_inv := fun u => by
          ext; change π (σ (g : G) : A) (π (σ ((g⁻¹ : Γ) : G) : A) u.1) = u.1
          rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← Submonoid.coe_mul, ← map_mul,
            Subgroup.coe_inv, mul_inv_cancel, map_one, Submonoid.coe_one, map_one,
            one_apply_eq_self]
        norm_map' := fun u => starAlgHom_unitary_norm σ π (g : G) u.1 }
    let ρp : Γ →* (E₀ᗮ ≃ₗᵢ[ℂ] E₀ᗮ) :=
      { toFun := ρp_fun
        map_one' := by
          ext u; change π (σ (1 : G) : A) u.1 = u.1
          rw [map_one, Submonoid.coe_one, map_one, one_apply_eq_self]
        map_mul' := fun g₁ g₂ => by
          ext u
          change π (σ (((g₁ * g₂ : Γ) : G)) : A) u.1 =
            π (σ (g₁ : G) : A) (π (σ (g₂ : G) : A) u.1)
          rw [Subgroup.coe_mul, map_mul, Submonoid.coe_mul, map_mul, ContinuousLinearMap.mul_apply] }
    have hnofix_p : ∀ u : E₀ᗮ, (∀ g : Γ, ρp g u = u) → u = 0 := by
      intro u hu
      have hu0 : u.1 ∈ E₀ := fun g => congrArg Subtype.val (hu g)
      have hinner : ⟪u.1, u.1⟫_ℂ = 0 := u.2 u.1 hu0
      exact Subtype.ext (inner_self_eq_zero.mp hinner)
    have hv_mem : v ∈ E₀ᗮ := fun w hw => hv_perp w hw
    obtain ⟨g₀, hg₀F, hg₀_le⟩ := hKaz (E₀ᗮ) ρp hnofix_p ⟨v, hv_mem⟩
    have hg₀_norm : ε * ‖v‖ ≤ ‖π (σ (g₀ : G) : A) v - v‖ := hg₀_le
    have hg₀_sq : ε ^ 2 * ‖v‖ ^ 2 ≤ ‖π (σ (g₀ : G) : A) v - v‖ ^ 2 := by
      have := sq_le_sq₀ (mul_nonneg hε_pos.le (norm_nonneg v)) (norm_nonneg _) |>.mpr hg₀_norm
      linarith [mul_pow ε ‖v‖ 2]
    have hsum_ge : ε ^ 2 * ‖v‖ ^ 2 ≤ ∑ g ∈ S, ‖π (σ (g : G) : A) v - v‖ ^ 2 := by
      refine hg₀_sq.trans ?_
      exact Finset.single_le_sum (f := fun g : Γ => ‖π (σ (g : G) : A) v - v‖ ^ 2)
        (fun g _ => sq_nonneg _) (hF_sub_S hg₀F)
    rw [hquad_eq π v]
    have h1 : (ε ^ 2 / (4 * (S.card : ℝ))) * ‖v‖ ^ 2 ≤
        (1 / (4 * (S.card : ℝ))) * ∑ g ∈ S, ‖π (σ (g : G) : A) v - v‖ ^ 2 := by
      calc (ε ^ 2 / (4 * (S.card : ℝ))) * ‖v‖ ^ 2
          = (1 / (4 * (S.card : ℝ))) * (ε ^ 2 * ‖v‖ ^ 2) := by ring
        _ ≤ (1 / (4 * (S.card : ℝ))) * ∑ g ∈ S, ‖π (σ (g : G) : A) v - v‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hsum_ge
              (div_nonneg zero_le_one (mul_nonneg (by norm_num) hS_pos.le))
    have h2 : δ * ‖v‖ ^ 2 ≤ (ε ^ 2 / (4 * (S.card : ℝ))) * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hδ_le_gap (sq_nonneg _)
    linarith
  -- Step 4: Spectral gap `spectrum ℝ h ⊆ [0, 1 - δ] ∪ {1}` via states & GNS
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  haveI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hS_inv_mul : (((S.card : ℝ)⁻¹ : ℝ) : ℂ) * (S.card : ℂ) = 1 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, inv_mul_cancel₀ hS_ne, Complex.ofReal_one]
  have hspec_h : ∀ x ∈ spectrum ℝ h, 0 ≤ x ∧ (x ≤ 1 - δ ∨ x = 1) := by
    intro lam hlam
    obtain ⟨f, -, -, -, ζ, hζ_norm, hζ_eig⟩ := exists_state_gns_eigenvector hh_sa hlam
    have hre_eig : (⟪f.gnsStarAlgHom h ζ, ζ⟫_ℂ).re = lam := by
      rw [hζ_eig, inner_smul_left, inner_self_eq_norm_sq_to_K, hζ_norm]
      simp
    refine ⟨by rw [← hre_eig]; exact hquad_nonneg f.gnsStarAlgHom ζ, ?_⟩
    by_cases h1 : lam = 1
    · exact Or.inr h1
    · left
      have hperp : ∀ w : f.GNS, (∀ g : Γ, f.gnsStarAlgHom (σ (g : G) : A) w = w) → ⟪w, ζ⟫_ℂ = 0 := by
        intro w hw
        have hhw : f.gnsStarAlgHom h w = w := by
          simp only [h, map_smul, map_add, map_one, map_sum, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.add_apply, one_apply_eq_self, ContinuousLinearMap.sum_apply]
          have hsum_w : ∑ g ∈ S, f.gnsStarAlgHom (σ (g : G) : A) w = (S.card : ℂ) • w := by
            rw [Finset.sum_congr rfl fun g _ => hw g, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
          rw [hsum_w, smul_smul, hS_inv_mul, one_smul, ← two_smul ℂ w, smul_smul]
          norm_num
        have heq1 : ⟪w, f.gnsStarAlgHom h ζ⟫_ℂ = (lam : ℂ) * ⟪w, ζ⟫_ℂ := by
          rw [hζ_eig, inner_smul_right]
        have heq2 : ⟪w, f.gnsStarAlgHom h ζ⟫_ℂ = ⟪w, ζ⟫_ℂ := by
          have hadj : ⟪w, f.gnsStarAlgHom h ζ⟫_ℂ =
              ⟪ContinuousLinearMap.adjoint (f.gnsStarAlgHom h) w, ζ⟫_ℂ :=
            (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
          rw [hadj, ← ContinuousLinearMap.star_eq_adjoint, ← map_star, hh_sa.star_eq, hhw]
        have hdiff : ((lam : ℂ) - 1) * ⟪w, ζ⟫_ℂ = 0 := by linear_combination heq1.symm.trans heq2
        have hne : (lam : ℂ) - 1 ≠ 0 := by
          intro h0
          apply h1
          have := sub_eq_zero.mp h0
          exact_mod_cast this
        exact (mul_eq_zero.mp hdiff).resolve_left hne
      have hle := hquad_perp f.gnsStarAlgHom ζ hperp
      rw [hre_eig, hζ_norm] at hle
      linarith
  -- Step 5: Construct Kazhdan projection `p := cfc χ h` and prove `h ^ k → p`
  let χ : ℝ → ℝ := fun x => if 1 - δ / 2 ≤ x then 1 else 0
  have hχ_cont : ContinuousOn χ (spectrum ℝ h) := by
    intro x hx
    rcases (hspec_h x hx).2 with hle | rfl
    · have hopen : IsOpen (Set.Iio (1 - δ / 2)) := isOpen_Iio
      have hx_in : x ∈ Set.Iio (1 - δ / 2) := by change x < 1 - δ / 2; linarith
      have heq : Set.EqOn χ (fun _ => 0) (Set.Iio (1 - δ / 2)) := by
        intro y hy
        simp only [χ, if_neg (not_le.mpr (Set.mem_Iio.mp hy))]
      exact (continuousOn_const.congr heq).continuousAt (hopen.mem_nhds hx_in)
        |>.continuousWithinAt
    · have hopen : IsOpen (Set.Ioi (1 - δ / 2)) := isOpen_Ioi
      have hx_in : (1 : ℝ) ∈ Set.Ioi (1 - δ / 2) := by change 1 - δ / 2 < 1; linarith
      have heq : Set.EqOn χ (fun _ => 1) (Set.Ioi (1 - δ / 2)) := by
        intro y hy
        simp only [χ, if_pos (le_of_lt (Set.mem_Ioi.mp hy))]
      exact (continuousOn_const.congr heq).continuousAt (hopen.mem_nhds hx_in)
        |>.continuousWithinAt
  let p : A := cfc χ h
  have hp_idem : p * p = p := by
    dsimp only [p]
    rw [← cfc_mul χ χ h hχ_cont hχ_cont]
    refine cfc_congr fun x _ => ?_
    dsimp only [χ]
    split_ifs <;> norm_num
  have hp_sa : IsSelfAdjoint p := by
    rw [IsSelfAdjoint]
    dsimp only [p]
    rw [← cfc_star χ h]
    refine cfc_congr fun x _ => by simp
  have hhp : h * p = p := by
    dsimp only [p]
    nth_rw 1 [← cfc_id' ℝ h hh_sa]
    rw [← cfc_mul (fun x : ℝ => x) χ h continuousOn_id hχ_cont]
    refine cfc_congr fun x hx => ?_
    rcases (hspec_h x hx).2 with hle | rfl
    · simp only [χ, if_neg (by linarith : ¬ 1 - δ / 2 ≤ x), mul_zero]
    · simp only [χ, if_pos (by linarith : 1 - δ / 2 ≤ (1 : ℝ)), one_mul]
  have hpow_norm : ∀ k : ℕ, ‖h ^ k - p‖ ≤ (1 - δ) ^ k := by
    intro k
    have heq : h ^ k - p = cfc (fun x : ℝ => x ^ k - χ x) h := by
      dsimp only [p]
      rw [cfc_sub (fun x : ℝ => x ^ k) χ h (continuous_pow k).continuousOn hχ_cont,
        cfc_pow_id h k hh_sa]
    rw [heq]
    have h1δ : 0 ≤ 1 - δ := by linarith
    refine norm_cfc_le (pow_nonneg h1δ k) fun x hx => ?_
    rcases hspec_h x hx with ⟨hx0, hle | rfl⟩
    · simp only [χ, if_neg (by linarith : ¬ 1 - δ / 2 ≤ x), sub_zero,
        Real.norm_of_nonneg (pow_nonneg hx0 k)]
      exact pow_le_pow_left₀ hx0 hle k
    · simp only [χ, if_pos (by linarith : 1 - δ / 2 ≤ (1 : ℝ)), one_pow, sub_self, norm_zero]
      exact pow_nonneg h1δ k
  have hpow_tendsto : Tendsto (fun k : ℕ => h ^ k) atTop (𝓝 p) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) hpow_norm ?_
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  -- Step 6: Representation characterization of `p`
  have hp_rep : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (π : A →⋆ₐ[ℂ] (E →L[ℂ] E)) (v : E),
      π p v = v ↔ ∀ g ∈ Γ, π (σ g : A) v = v := by
    intro E _ _ _ π v
    constructor
    · intro hpv
      -- First `π h v = v` because `h * p = p`
      have hhv : π h v = v := by
        calc π h v = π h (π p v) := by rw [hpv]
          _ = π (h * p) v := by rw [map_mul, ContinuousLinearMap.mul_apply]
          _ = π p v := by rw [hhp]
          _ = v := hpv
      -- Decompose `v = v₀ + v₁` with `v₀ ∈ E₀`, `v₁ ∈ E₀ᗮ`
      let E₀ : Submodule ℂ E :=
        { carrier := {w : E | ∀ g : Γ, π (σ (g : G) : A) w = w}
          add_mem' := fun {x y} hx hy g => by rw [map_add, hx g, hy g]
          zero_mem' := fun g => map_zero _
          smul_mem' := fun c x hx g => by rw [map_smul, hx g] }
      have hE₀_closed : IsClosed (E₀ : Set E) := by
        have heq : (E₀ : Set E) = ⋂ g : Γ, {w : E | π (σ (g : G) : A) w = w} := by
          ext w; simp [E₀]
        rw [heq]
        exact isClosed_iInter fun g => isClosed_eq (π (σ (g : G) : A)).continuous continuous_id
      haveI : CompleteSpace E₀ := hE₀_closed.completeSpace_coe
      obtain ⟨v₀, hv₀, v₁, hv₁, hv_eq⟩ := E₀.exists_add_mem_mem_orthogonal v
      have hhv₀ : π h v₀ = v₀ := by
        simp only [h, map_smul, map_add, map_one, map_sum, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.add_apply, one_apply_eq_self, ContinuousLinearMap.sum_apply]
        have hsum_w : ∑ g ∈ S, π (σ (g : G) : A) v₀ = (S.card : ℂ) • v₀ := by
          rw [Finset.sum_congr rfl fun g _ => hv₀ g, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
        rw [hsum_w, smul_smul, hS_inv_mul, one_smul, ← two_smul ℂ v₀, smul_smul]
        norm_num
      have hhv₁ : π h v₁ = v₁ := by
        have hsub_eq : v₁ = v - v₀ := by rw [hv_eq]; abel
        rw [hsub_eq, map_sub, hhv, hhv₀]
      have hle := hquad_perp π v₁ (fun w hw => hv₁ w hw)
      have hre : (⟪π h v₁, v₁⟫_ℂ).re = ‖v₁‖ ^ 2 := by
        rw [hhv₁]
        have h1 : ⟪v₁, v₁⟫_ℂ = ((‖v₁‖ ^ 2 : ℝ) : ℂ) := by
          rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
        rw [h1, Complex.ofReal_re]
      rw [hre] at hle
      have hv₁_zero : v₁ = 0 := by
        have hprod : δ * ‖v₁‖ ^ 2 ≤ 0 := by linarith
        have hsq0 : ‖v₁‖ ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right hprod hδ_pos
        have hnorm0 : ‖v₁‖ = 0 := by nlinarith [norm_nonneg v₁]
        exact norm_eq_zero.mp hnorm0
      rw [hv_eq, hv₁_zero, add_zero]
      intro g hg
      exact hv₀ ⟨g, hg⟩
    · intro hfix
      have hhv : π h v = v := by
        simp only [h, map_smul, map_add, map_one, map_sum, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.add_apply, one_apply_eq_self, ContinuousLinearMap.sum_apply]
        have hsum_v : ∑ g ∈ S, π (σ (g : G) : A) v = (S.card : ℂ) • v := by
          rw [Finset.sum_congr rfl fun g _ => hfix g.1 g.2, Finset.sum_const,
            ← Nat.cast_smul_eq_nsmul ℂ]
        rw [hsum_v, smul_smul, hS_inv_mul, one_smul, ← two_smul ℂ v, smul_smul]
        norm_num
      have hpow_v : ∀ k : ℕ, π (h ^ k) v = v := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [pow_succ', map_mul, ContinuousLinearMap.mul_apply, ih, hhv]
      have hlim : Tendsto (fun k : ℕ => π (h ^ k) v) atTop (𝓝 (π p v)) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
          ((tendsto_iff_norm_sub_tendsto_zero.mp hpow_tendsto).mul_const ‖v‖
            |>.trans (by simp))
        have h1 : π (h ^ k) v - π p v = π (h ^ k - p) v := by
          rw [map_sub, ContinuousLinearMap.sub_apply]
        rw [h1]
        exact (ContinuousLinearMap.le_opNorm _ v).trans
          (mul_le_mul_of_nonneg_right (starAlgHom_norm_le π (h ^ k - p)) (norm_nonneg v))
      have hconst : Tendsto (fun k : ℕ => π (h ^ k) v) atTop (𝓝 v) := by
        simpa only [hpow_v] using tendsto_const_nhds
      exact tendsto_nhds_unique hlim hconst
  -- Step 7: Show `σ g * p = p` for every `g ∈ Γ` via GNS
  have hσp : ∀ g ∈ Γ, (σ g : A) * p = p := by
    intro g hg
    let d : A := ((σ g : A) - 1) * p
    let b : A := star d * d
    have hb_zero : b = 0 := by
      by_contra hne
      have hb_pos : 0 < ‖b‖ := norm_pos_iff.mpr hne
      have hb_sa : IsSelfAdjoint b := IsSelfAdjoint.star_mul_self d
      have hb_nonneg : 0 ≤ b := star_mul_self_nonneg d
      have hgr : IsGreatest ((fun x : ℝ => ‖x‖) '' spectrum ℝ b) ‖b‖ := by
        simpa [cfc_id ℝ b hb_sa] using IsGreatest.norm_cfc (id : ℝ → ℝ) b continuousOn_id hb_sa
      obtain ⟨lam, hlam_spec, hlam_norm⟩ := hgr.1
      dsimp only at hlam_norm
      have hlam_nonneg : 0 ≤ lam := spectrum_nonneg_of_nonneg hb_nonneg hlam_spec
      have hlam_pos : 0 < lam := by
        rw [Real.norm_of_nonneg hlam_nonneg] at hlam_norm
        linarith
      obtain ⟨f, -, hfb, -, -, -, -⟩ := exists_state_gns_eigenvector hb_sa hlam_spec
      let ζ₁ : f.GNS := ((f.toPreGNS 1 : f.PreGNS) : f.GNS)
      have hv_fix : f.gnsStarAlgHom p (f.gnsStarAlgHom p ζ₁) = f.gnsStarAlgHom p ζ₁ := by
        rw [← ContinuousLinearMap.mul_apply, ← map_mul, hp_idem]
      have hinv := (hp_rep f.GNS f.gnsStarAlgHom (f.gnsStarAlgHom p ζ₁)).mp hv_fix g hg
      have hd_zero : f.gnsStarAlgHom d ζ₁ = 0 := by
        dsimp only [d]
        rw [map_mul, map_sub, map_one, ContinuousLinearMap.mul_apply,
          ContinuousLinearMap.sub_apply, one_apply_eq_self, hinv, sub_self]
      -- Yet `‖f.gnsStarAlgHom d ζ₁‖ ^ 2 = (f b).re = lam > 0`!
      have hd_norm : ‖f.gnsStarAlgHom d ζ₁‖ ^ 2 = lam := by
        have h1 : f.gnsStarAlgHom d ζ₁ = ((f.toPreGNS d : f.PreGNS) : f.GNS) := by
          have hact : f.gnsStarAlgHom d ζ₁ = ((f.leftMulMapPreGNS d (f.toPreGNS 1) : f.PreGNS) : f.GNS) :=
            PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe f
          rw [hact]
          congr 1; apply f.ofPreGNS.injective; simp [PositiveLinearMap.leftMulMapPreGNS]
        rw [h1, UniformSpace.Completion.norm_coe]
        have hsq := f.preGNS_norm_sq (f.toPreGNS d)
        simp only [PositiveLinearMap.ofPreGNS_toPreGNS] at hsq
        rw [← Complex.ofReal_pow] at hsq
        change ((‖f.toPreGNS d‖ ^ 2 : ℝ) : ℂ) = f b at hsq
        rw [hfb] at hsq
        exact_mod_cast hsq
      rw [hd_zero, norm_zero, zero_pow (by norm_num)] at hd_norm
      linarith
    have hd_zero : d = 0 := by
      have hsq : ‖d‖ * ‖d‖ = 0 := by
        rw [← CStarRing.norm_star_mul_self, show star d * d = b from rfl, hb_zero, norm_zero]
      exact norm_eq_zero.mp (mul_self_eq_zero.mp hsq)
    have hsub0 : (σ g : A) * p - p = 0 := by
      simpa [d, sub_mul, one_mul] using hd_zero
    exact sub_eq_zero.mp hsub0
  -- Step 8: Define `u := Unitary.toUnits (σ t)` and `q := u * p * u⁻¹`
  let u : Aˣ := Unitary.toUnits (σ t)
  let q : A := (u : A) * p * (↑u⁻¹ : A)
  have hu_coe : (u : A) = (σ t : A) := rfl
  have hu_inv_coe : (↑u⁻¹ : A) = (σ t⁻¹ : A) := by
    change star (σ t : A) = (σ t⁻¹ : A)
    exact starAlgHom_unitary_inv σ t
  have hu_inv_star : (↑u⁻¹ : A) = star (u : A) := rfl
  have hq_sa : IsSelfAdjoint q := by
    rw [IsSelfAdjoint]
    dsimp only [q]
    rw [star_mul, star_mul, hu_inv_star, star_star, hp_sa.star_eq, mul_assoc]
  have hqh_p : ((u : A) * h * (↑u⁻¹ : A)) * p = p := by
    have hexp : (u : A) * h * (↑u⁻¹ : A) =
        ((1 / 2 : ℝ) : ℂ) •
          ((1 : A) + (((S.card : ℝ)⁻¹ : ℝ) : ℂ) • ∑ g ∈ S, (σ (t * (g : G) * t⁻¹) : A)) := by
      simp only [h, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, one_mul,
        Finset.mul_sum, Finset.sum_mul, hu_coe, hu_inv_coe]
      congr 2
      · rw [← Submonoid.coe_mul, ← map_mul, mul_inv_cancel, map_one, Submonoid.coe_one]
      · congr 1
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [← Submonoid.coe_mul, ← Submonoid.coe_mul, ← map_mul, ← map_mul]
    rw [hexp, smul_mul_assoc, add_mul, one_mul, smul_mul_assoc, Finset.sum_mul]
    have hsum_p : ∑ g ∈ S, (σ (t * (g : G) * t⁻¹) : A) * p = (S.card : ℂ) • p := by
      have hterm : ∀ g ∈ S, (σ (t * (g : G) * t⁻¹) : A) * p = p :=
        fun g _ => hσp (t * (g : G) * t⁻¹) (hsub g.1 g.2)
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
    rw [hsum_p, smul_smul, hS_inv_mul, one_smul, ← two_smul ℂ p, smul_smul]
    norm_num
  have hqh_pow_p : ∀ k : ℕ, ((u : A) * h ^ k * (↑u⁻¹ : A)) * p = p := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero, mul_one]
      rw [Units.mul_inv, one_mul]
    | succ k ih =>
      have hconj : (u : A) * h ^ (k + 1) * (↑u⁻¹ : A) =
          ((u : A) * h * (↑u⁻¹ : A)) * ((u : A) * h ^ k * (↑u⁻¹ : A)) := by
        rw [pow_succ']
        calc (u : A) * (h * h ^ k) * (↑u⁻¹ : A)
            = (u : A) * h * 1 * h ^ k * (↑u⁻¹ : A) := by simp [mul_assoc]
          _ = (u : A) * h * ((↑u⁻¹ : A) * (u : A)) * h ^ k * (↑u⁻¹ : A) := by
              rw [Units.inv_mul]
          _ = ((u : A) * h * (↑u⁻¹ : A)) * ((u : A) * h ^ k * (↑u⁻¹ : A)) := by
              simp only [mul_assoc]
      rw [hconj, mul_assoc, ih, hqh_p]
  have hqp : q * p = p := by
    have hlim : Tendsto (fun k : ℕ => ((u : A) * h ^ k * (↑u⁻¹ : A)) * p) atTop (𝓝 (q * p)) := by
      dsimp only [q]
      exact (((tendsto_const_nhds.mul hpow_tendsto).mul tendsto_const_nhds).mul tendsto_const_nhds)
    have hconst : Tendsto (fun k : ℕ => ((u : A) * h ^ k * (↑u⁻¹ : A)) * p) atTop (𝓝 p) := by
      simpa only [hqh_pow_p] using tendsto_const_nhds
    exact tendsto_nhds_unique hlim hconst
  have hpq : p * q = p := by
    have := congrArg star hqp
    rw [star_mul, hp_sa.star_eq, hq_sa.star_eq] at this
    exact this
  refine ⟨p, q, hp_idem, hpq, hqp, ⟨u, rfl⟩, ?_⟩
  intro E _ _ _ π v
  refine ⟨hp_rep E π v, ?_⟩
  have hinv_act : ∀ w : E, π (σ t : A) (π (σ t⁻¹ : A) w) = w := fun w => by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← Submonoid.coe_mul, ← map_mul,
      mul_inv_cancel, map_one, Submonoid.coe_one, map_one, ContinuousLinearMap.one_apply]
  have hinv_act' : ∀ w : E, π (σ t⁻¹ : A) (π (σ t : A) w) = w := fun w => by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← Submonoid.coe_mul, ← map_mul,
      inv_mul_cancel, map_one, Submonoid.coe_one, map_one, ContinuousLinearMap.one_apply]
  have hqv_iff : π q v = v ↔ π p (π (σ t⁻¹ : A) v) = π (σ t⁻¹ : A) v := by
    dsimp only [q]
    rw [hu_coe, hu_inv_coe, map_mul, map_mul, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.mul_apply]
    constructor
    · intro h1
      calc π p (π (σ t⁻¹ : A) v)
          = π (σ t⁻¹ : A) (π (σ t : A) (π p (π (σ t⁻¹ : A) v))) := (hinv_act' _).symm
        _ = π (σ t⁻¹ : A) v := by rw [h1]
    · intro h1
      rw [h1, hinv_act]
  rw [hqv_iff, hp_rep E π (π (σ t⁻¹ : A) v)]
  constructor
  · intro h1 g hg
    have hconj : (σ (t * g * t⁻¹) : A) = (σ t : A) * (σ g : A) * (σ t⁻¹ : A) := by
      rw [map_mul, map_mul, Submonoid.coe_mul, Submonoid.coe_mul]
    rw [hconj, map_mul, map_mul, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
      h1 g hg, hinv_act]
  · intro h1 g hg
    have hconj : (σ (t * g * t⁻¹) : A) = (σ t : A) * (σ g : A) * (σ t⁻¹ : A) := by
      rw [map_mul, map_mul, Submonoid.coe_mul, Submonoid.coe_mul]
    have h2 := h1 g hg
    rw [hconj, map_mul, map_mul, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply] at h2
    calc π (σ g : A) (π (σ t⁻¹ : A) v)
        = π (σ t⁻¹ : A) (π (σ t : A) (π (σ g : A) (π (σ t⁻¹ : A) v))) := (hinv_act' _).symm
      _ = π (σ t⁻¹ : A) v := by rw [h2]

end OMA.R_Green100_H3_R1_H2_Proof

theorem OMA.solution : OMA.R_Green100_green_100_variants_operator_norm_R1_H3_R1.H2 :=
  OMA.R_Green100_H3_R1_H2_Proof.main_proof
