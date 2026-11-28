import OMAReductions.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_solvable_R1_H1_R1
import Mathlib

/-!
# The primitive case with a nontrivial normal `3`-subgroup

Step `H2` of the reduction `ConjugacyClassSizes.conjClassSizes_iff_sym_three_solvable.R1.H1.R1`
of Gow's theorem.

A finite group `H` in which every element is conjugate to its inverse, acting faithfully and
irreducibly on a nonzero `𝔽_p`-space `V` with `p ∤ |H|`, has a nonzero invariant bilinear form
on `V` (compare the characters of `V` and of its dual after extending scalars to an algebraic
closure).  If every nonzero vector is conjugate to its double and `p ≥ 7`, this form is
alternating and nondegenerate, and the quadratic function `v ↦ B(v, a v)` attached to an
element `a` whose conjugates are `a` and `a⁻¹` vanishes identically; polarising gives `a² = 1`.
A generator of the centre of order `3` of a normal `3`-subgroup is such an element.
-/

namespace OMAGowForm

section InvariantForm

open Module

/-- Over an algebraically closed field whose characteristic does not divide `|H|`, a nonzero
finite-dimensional representation of a group in which every element is conjugate to its inverse
carries a nonzero invariant bilinear form. -/
theorem exists_invariant_bilin_of_isAlgClosed {K : Type*} [Field K] [IsAlgClosed K]
    {H : Type*} [Group H] [Fintype H] {M : Type*} [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] [Nontrivial M] (τ : Representation K H M)
    (hcard : (Nat.card H : K) ≠ 0) (hreal : ∀ h : H, IsConj h h⁻¹) :
    ∃ B : M →ₗ[K] M →ₗ[K] K, B ≠ 0 ∧ ∀ (h : H) (x y : M), B (τ h x) (τ h y) = B x y := by
  classical
  -- a nonzero invariant subspace of least dimension
  let P : ℕ → Prop := fun n => ∃ W : Submodule K M, W ≠ ⊥ ∧
    (∀ (h : H), ∀ w ∈ W, τ h w ∈ W) ∧ finrank K W = n
  have hP : ∃ n, P n := ⟨_, ⊤, top_ne_bot, fun _ _ _ => Submodule.mem_top, rfl⟩
  obtain ⟨W, hW0, hWinv, hWn⟩ := Nat.find_spec hP
  have hmin : ∀ W' : Submodule K M, W' ≠ ⊥ → (∀ (h : H), ∀ w ∈ W', τ h w ∈ W') →
      finrank K W ≤ finrank K W' := fun W' h0 hinv => by
    rw [hWn]; exact Nat.find_min' hP ⟨W', h0, hinv, rfl⟩
  -- the action on `W`
  let τW : H →* (W →ₗ[K] W) :=
    { toFun := fun h => (τ h).restrict (hWinv h)
      map_one' := by
        refine LinearMap.ext fun w => Subtype.ext ?_
        simp
      map_mul' := fun a b => by
        refine LinearMap.ext fun w => Subtype.ext ?_
        simp [map_mul] }
  have hτW : ∀ (h : H) (w : W), ((τW h w : W) : M) = τ h w := fun _ _ => rfl
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
  have hirr : Representation.IsIrreducible τW := by
    refine { exists_pair_ne := ⟨⊥, ⊤, fun e => ?_⟩, eq_bot_or_eq_top := fun σ => ?_ }
    · have : (⊥ : Submodule K W) = ⊤ := congrArg Subrepresentation.toSubmodule e
      exact bot_ne_top this
    · let W' : Submodule K M := σ.toSubmodule.map W.subtype
      have hW'le : W' ≤ W := by
        rintro _ ⟨u, -, rfl⟩
        exact u.2
      have hW'inv : ∀ (h : H), ∀ w ∈ W', τ h w ∈ W' := by
        rintro h _ ⟨u, hu, rfl⟩
        exact ⟨τW h u, σ.apply_mem_toSubmodule h hu, rfl⟩
      by_cases h0 : W' = ⊥
      · left
        apply Subrepresentation.toSubmodule_injective
        change σ.toSubmodule = ⊥
        rw [Submodule.eq_bot_iff]
        intro u hu
        have hu' : (u : M) ∈ W' := ⟨u, hu, rfl⟩
        rw [h0, Submodule.mem_bot] at hu'
        exact Subtype.ext hu'
      · right
        apply Subrepresentation.toSubmodule_injective
        have hEq : W' = W := Submodule.eq_of_le_of_finrank_le hW'le (hmin W' h0 hW'inv)
        change σ.toSubmodule = ⊤
        rw [Submodule.eq_top_iff']
        intro u
        have hu : (u : M) ∈ W' := by rw [hEq]; exact u.2
        obtain ⟨u', hu', e⟩ := hu
        have : u' = u := Subtype.ext e
        exact this ▸ hu'
  have hinvK : Invertible (Nat.card H : K) := invertibleOfNonzero hcard
  have hend : finrank K (Representation.IntertwiningMap τW τW) = 1 :=
    Representation.IsIrreducible.finrank_intertwiningMap_self τW
  have hχ : ∀ g : H, Representation.character τW g⁻¹ = Representation.character τW g := by
    intro g
    obtain ⟨c, hc⟩ := isConj_iff.mp (hreal g)
    rw [← hc, Representation.char_conj]
  have h1 := Representation.card_inv_mul_sum_char_mul_char_eq_finrank τW τW
  have h2 := Representation.card_inv_mul_sum_char_mul_char_eq_finrank τW
    (Representation.dual τW)
  have hsum : ∑ g : H, (Representation.dual τW).character g * Representation.character τW g⁻¹ =
      ∑ g : H, Representation.character τW g * Representation.character τW g⁻¹ := by
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Representation.char_dual, hχ g]
  have hdual : (finrank K (Representation.IntertwiningMap τW (Representation.dual τW)) : K) = 1 := by
    rw [← h2, hsum, h1, hend, Nat.cast_one]
  have hne : finrank K (Representation.IntertwiningMap τW (Representation.dual τW)) ≠ 0 := by
    intro e
    rw [e, Nat.cast_zero] at hdual
    exact zero_ne_one hdual
  obtain ⟨φ, hφ⟩ : ∃ φ : Representation.IntertwiningMap τW (Representation.dual τW), φ ≠ 0 := by
    by_contra! hall
    have : Subsingleton (Representation.IntertwiningMap τW (Representation.dual τW)) :=
      ⟨fun a b => (hall a).trans (hall b).symm⟩
    exact hne Module.finrank_zero_of_subsingleton
  -- the invariant form on `W`
  have hφinv : ∀ (h : H) (x y : W), φ (τW h x) (τW h y) = φ x y := by
    intro h x y
    have e := Representation.IntertwiningMap.isIntertwining τW (Representation.dual τW) φ h x
    rw [e, Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
      ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  obtain ⟨x₀, y₀, hxy⟩ : ∃ x₀ y₀ : W, φ x₀ y₀ ≠ 0 := by
    by_contra! hall
    apply hφ
    refine Representation.IntertwiningMap.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    exact hall x y
  obtain ⟨π₀, hπ₀⟩ := LinearMap.exists_leftInverse_of_injective W.subtype (Submodule.ker_subtype W)
  have hπW : ∀ w : W, π₀ (w : M) = w := fun w => by
    have := congrArg (fun f : W →ₗ[K] W => f w) hπ₀
    simpa using this
  let β₀ : M →ₗ[K] M →ₗ[K] K := (φ.toLinearMap).compl₁₂ π₀ π₀
  have hβ₀ : ∀ x y : M, β₀ x y = φ (π₀ x) (π₀ y) := fun _ _ => rfl
  refine ⟨∑ h : H, β₀.compl₁₂ (τ h) (τ h), ?_, ?_⟩
  · intro hB
    have e := congrArg (fun f : M →ₗ[K] M →ₗ[K] K => f (x₀ : M) (y₀ : M)) hB
    simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.zero_apply] at e
    have e2 : ∀ h : H, β₀ (τ h (x₀ : M)) (τ h (y₀ : M)) = φ x₀ y₀ := by
      intro h
      rw [hβ₀, ← hτW h x₀, ← hτW h y₀, hπW, hπW, hφinv]
    rw [Finset.sum_congr rfl (fun h _ => e2 h), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← Nat.card_eq_fintype_card] at e
    exact (mul_ne_zero hcard hxy) e
  · intro g x y
    simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply]
    have e : ∀ h : H, β₀ (τ h (τ g x)) (τ h (τ g y)) = β₀ (τ (h * g) x) (τ (h * g) y) := by
      intro h
      rw [map_mul]; rfl
    rw [Finset.sum_congr rfl (fun h _ => e h)]
    exact Equiv.sum_comp (Equiv.mulRight g) (fun h => β₀ (τ h x) (τ h y))

open TensorProduct in
/-- A nonzero finite-dimensional representation, over a field whose characteristic does not
divide `|H|`, of a group in which every element is conjugate to its inverse carries a nonzero
invariant bilinear form. -/
theorem exists_invariant_bilin {k : Type*} [Field k] {H : Type*} [Group H] [Fintype H]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (ρ : Representation k H V) (hcard : (Nat.card H : k) ≠ 0) (hreal : ∀ h : H, IsConj h h⁻¹) :
    ∃ B : V →ₗ[k] V →ₗ[k] k, B ≠ 0 ∧ ∀ (h : H) (v w : V), B (ρ h v) (ρ h w) = B v w := by
  classical
  let K := AlgebraicClosure k
  let τ : H →* ((K ⊗[k] V) →ₗ[K] (K ⊗[k] V)) :=
    { toFun := fun h => (ρ h).baseChange K
      map_one' := by
        rw [map_one, Module.End.one_eq_id, LinearMap.baseChange_id]; rfl
      map_mul' := fun a b => by
        rw [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp]; rfl }
  have hτ : ∀ (h : H) (c : K) (v : V), τ h (c ⊗ₜ[k] v) = c ⊗ₜ[k] ρ h v := fun h c v =>
    LinearMap.baseChange_tmul _ _ _
  have hcardK : (Nat.card H : K) ≠ 0 := by
    have : (Nat.card H : K) = algebraMap k K (Nat.card H : k) := (map_natCast _ _).symm
    rw [this]
    exact (map_ne_zero (algebraMap k K)).mpr hcard
  have : Nontrivial (K ⊗[k] V) := by
    apply Module.nontrivial_of_finrank_pos (R := K)
    rw [Module.finrank_baseChange]
    exact Module.finrank_pos
  obtain ⟨BK, hBK0, hBKinv⟩ := exists_invariant_bilin_of_isAlgClosed τ hcardK hreal
  let ι : V →ₗ[k] K ⊗[k] V := TensorProduct.mk k K V 1
  have hι : ∀ v : V, ι v = (1 : K) ⊗ₜ[k] v := fun _ => rfl
  have hιτ : ∀ (h : H) (v : V), τ h (ι v) = ι (ρ h v) := fun h v => hτ h 1 v
  -- the form does not vanish on `V`
  obtain ⟨v₀, w₀, hvw⟩ : ∃ v₀ w₀ : V, BK (ι v₀) (ι w₀) ≠ 0 := by
    by_contra! hall
    apply hBK0
    have h1 : ∀ (v : V) (y : K ⊗[k] V), BK (ι v) y = 0 := by
      intro v y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul c w =>
        have : c ⊗ₜ[k] w = c • ι w := by rw [hι, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this, map_smul, hall, smul_zero]
      | add y₁ y₂ h₁ h₂ => rw [map_add, h₁, h₂, add_zero]
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    change BK x y = 0
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v =>
      have : c ⊗ₜ[k] v = c • ι v := by rw [hι, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, map_smul, LinearMap.smul_apply, h1, smul_zero]
    | add x₁ x₂ h₁ h₂ => rw [map_add, LinearMap.add_apply, h₁, h₂, add_zero]
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual k K, ℓ (BK (ι v₀) (ι w₀)) ≠ 0 := by
    by_contra! hall
    exact hvw ((Module.forall_dual_apply_eq_zero_iff k _).mp hall)
  have hsmul : ∀ (c : k) (x : K ⊗[k] V), c • x = (algebraMap k K c) • x := fun c x =>
    (algebraMap_smul K c x).symm
  let B : V →ₗ[k] V →ₗ[k] k := LinearMap.mk₂ k (fun v w => ℓ (BK (ι v) (ι w)))
    (fun v₁ v₂ w => by rw [map_add, map_add, LinearMap.add_apply, map_add])
    (fun c v w => by
      rw [map_smul, hsmul, map_smul, LinearMap.smul_apply, smul_eq_mul, ← Algebra.smul_def,
        map_smul])
    (fun v w₁ w₂ => by rw [map_add, map_add, map_add])
    (fun c v w => by
      rw [map_smul, hsmul, map_smul, smul_eq_mul, ← Algebra.smul_def, map_smul])
  refine ⟨B, fun hB => ?_, fun h v w => ?_⟩
  · exact hℓ (congrArg (fun f : V →ₗ[k] V →ₗ[k] k => f v₀ w₀) hB)
  · change ℓ (BK (ι (ρ h v)) (ι (ρ h w))) = ℓ (BK (ι v) (ι w))
    rw [← hιτ, ← hιτ, hBKinv]

/-- **Symplectic form.** Let `H` be a finite group in which every element is conjugate to its
inverse, acting irreducibly on a nonzero finite-dimensional `𝔽_p`-space `V` with `p ∤ |H|`,
`p ≥ 7`, such that every nonzero vector is conjugate to its double.  Then `V` carries a
nondegenerate alternating `H`-invariant bilinear form. -/
theorem exists_symplectic_form {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p)
    {H : Type*} [Group H] [Fintype H] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V] [Nontrivial V] (ρ : Representation (ZMod p) H V)
    (hpH : ¬ p ∣ Nat.card H) (hreal : ∀ h : H, IsConj h h⁻¹)
    (hirr : ∀ W : Submodule (ZMod p) V, (∀ (h : H), ∀ w ∈ W, ρ h w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hSF : ∀ v : V, v ≠ 0 → ∃ h : H, ρ h v = (2 : ZMod p) • v) :
    ∃ B : V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p,
      (∀ (h : H) (v w : V), B (ρ h v) (ρ h w) = B v w) ∧ (∀ v : V, B v v = 0) ∧
      (∀ v : V, (∀ w : V, B v w = 0) → v = 0) := by
  have hcard : (Nat.card H : ZMod p) ≠ 0 := fun e => hpH ((ZMod.natCast_eq_zero_iff _ _).mp e)
  obtain ⟨B, hB0, hBinv⟩ := exists_invariant_bilin ρ hcard hreal
  refine ⟨B, hBinv, fun v => ?_, fun v hv => ?_⟩
  · by_cases hv : v = 0
    · rw [hv]; simp
    obtain ⟨h, hh⟩ := hSF v hv
    have e := hBinv h v v
    rw [hh, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at e
    have h3 : (3 : ZMod p) * B v v = 0 := by linear_combination e
    have h3' : (3 : ZMod p) ≠ 0 := by
      intro e3
      have : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast e3
      have hd := (ZMod.natCast_eq_zero_iff 3 p).mp this
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    exact (mul_eq_zero.mp h3).resolve_left h3'
  · let W : Submodule (ZMod p) V := LinearMap.ker B
    have hW : ∀ (h : H), ∀ w ∈ W, ρ h w ∈ W := by
      intro h w hw
      rw [LinearMap.mem_ker] at hw ⊢
      refine LinearMap.ext fun x => ?_
      have e := hBinv h w (ρ h⁻¹ x)
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply,
        hw] at e
      simpa using e
    rcases hirr W hW with hbot | htop
    · have : v ∈ W := LinearMap.mem_ker.mpr (LinearMap.ext fun w => by simpa using hv w)
      rw [hbot, Submodule.mem_bot] at this
      exact this
    · exact (hB0 (LinearMap.ker_eq_top.mp htop)).elim

/-- In the situation of `exists_symplectic_form` with a faithful action, an element whose
conjugates are itself and its inverse is an involution.  In particular the acting group has no
normal subgroup of order `3` and no cyclic normal subgroup of order `4`. -/
theorem sq_eq_one_of_conj_eq_self_or_inv {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p)
    {H : Type*} [Group H] [Fintype H] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V] [Nontrivial V] (ρ : Representation (ZMod p) H V)
    (hpH : ¬ p ∣ Nat.card H) (hreal : ∀ h : H, IsConj h h⁻¹) (hfaith : Function.Injective ρ)
    (hirr : ∀ W : Submodule (ZMod p) V, (∀ (h : H), ∀ w ∈ W, ρ h w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hSF : ∀ v : V, v ≠ 0 → ∃ h : H, ρ h v = (2 : ZMod p) • v)
    (a : H) (ha : ∀ h : H, h * a * h⁻¹ = a ∨ h * a * h⁻¹ = a⁻¹) : a ^ 2 = 1 := by
  obtain ⟨B, hBinv, hBalt, hBnd⟩ := exists_symplectic_form hp7 ρ hpH hreal hirr hSF
  have hanti : ∀ v w : V, B v w = -B w v := by
    intro v w
    have e := hBalt (v + w)
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hBalt v, hBalt w] at e
    linear_combination e
  have hmove : ∀ (h : H) (v w : V), B (ρ h v) w = B v (ρ h⁻¹ w) := by
    intro h v w
    have e := hBinv h v (ρ h⁻¹ w)
    rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at e
  -- the quadratic function `v ↦ B v (a v)` is invariant up to sign
  have hf : ∀ (h : H) (v : V), B (ρ h v) (ρ a (ρ h v)) = B v (ρ a v) ∨
      B (ρ h v) (ρ a (ρ h v)) = -B v (ρ a v) := by
    intro h v
    have e1 : B (ρ h v) (ρ a (ρ h v)) = B v (ρ (h⁻¹ * a * h) v) := by
      rw [hmove, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_assoc]
    rcases ha h⁻¹ with e | e
    · left
      rw [e1]
      rw [inv_inv] at e
      rw [e]
    · right
      rw [inv_inv] at e
      rw [e1, e, hanti, hmove, inv_inv]
  have hzero : ∀ v : V, B v (ρ a v) = 0 := by
    intro v
    by_cases hv : v = 0
    · rw [hv]; simp
    obtain ⟨h, hh⟩ := hSF v hv
    have hsq : B (ρ h v) (ρ a (ρ h v)) ^ 2 = B v (ρ a v) ^ 2 := by
      rcases hf h v with e | e <;> rw [e]
      ring
    rw [hh, map_smul, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at hsq
    have h15 : (15 : ZMod p) * B v (ρ a v) ^ 2 = 0 := by linear_combination hsq
    have h15' : (15 : ZMod p) ≠ 0 := by
      intro e15
      have : ((15 : ℕ) : ZMod p) = 0 := by exact_mod_cast e15
      have hd := (ZMod.natCast_eq_zero_iff 15 p).mp this
      have hp : p.Prime := Fact.out
      have : p ∣ 3 * 5 := hd
      rcases (Nat.Prime.dvd_mul hp).mp this with h3 | h5
      · have := Nat.le_of_dvd (by norm_num) h3; omega
      · have := Nat.le_of_dvd (by norm_num) h5; omega
    exact pow_eq_zero_iff (two_ne_zero) |>.mp ((mul_eq_zero.mp h15).resolve_left h15')
  -- polarisation
  have hpol : ∀ v w : V, B v (ρ a w) = B v (ρ a⁻¹ w) := by
    intro v w
    have e := hzero (v + w)
    rw [map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hzero v, hzero w] at e
    have e2 : B w (ρ a v) = -B (ρ a v) w := hanti _ _
    rw [e2, hmove] at e
    linear_combination e
  have hρ : ρ a = ρ a⁻¹ := by
    refine LinearMap.ext fun w => ?_
    have h0 : ρ a w - ρ a⁻¹ w = 0 := by
      apply hBnd
      intro x
      rw [hanti, map_sub, hpol x w, sub_self, neg_zero]
    exact sub_eq_zero.mp h0
  have := hfaith hρ
  rw [pow_two]
  nth_rewrite 2 [this]
  exact mul_inv_cancel a

/-- In a group with three elements every element is `1`, a given nonidentity element, or its
inverse. -/
theorem eq_one_or_eq_or_eq_inv_of_card_three {C : Type*} [Group C] (hC : Nat.card C = 3)
    {z : C} (hz : z ≠ 1) (w : C) : w = 1 ∨ w = z ∨ w = z⁻¹ := by
  classical
  have : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; norm_num)
  let _ := Fintype.ofFinite C
  have hz3 : z ^ 3 = 1 := by rw [← hC]; exact pow_card_eq_one'
  have hzinv : z ≠ z⁻¹ := by
    intro e
    have h2 : z ^ 2 = 1 := by rw [pow_two]; nth_rewrite 2 [e]; exact mul_inv_cancel z
    have : z = 1 := by
      calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
        _ = 1 := by rw [hz3, h2]; simp
    exact hz this
  by_contra hall
  push Not at hall
  obtain ⟨h1, h2, h3⟩ := hall
  have hcard : ({1, z, z⁻¹, w} : Finset C).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simpa using fun e => h3 e.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hzinv, fun e => h2 e.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun e => hz e.symm, fun e => hz (inv_eq_one.mp e.symm), fun e => h1 e.symm⟩
  have hle := Finset.card_le_univ ({1, z, z⁻¹, w} : Finset C)
  rw [hcard, ← Nat.card_eq_fintype_card, hC] at hle
  omega

end InvariantForm

end OMAGowForm

open OMAGowForm in
theorem OMA.solution : OMA.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_solvable_R1_H1_R1.H2 := by
  intro p _ hp7 _ d hd H _ _ _ hsmooth hrat _ hQ _ ρ hfaith hirr _ _ hjoint
  classical
  have hp : p.Prime := Fact.out
  -- the module is nonzero
  have hd0 : 0 < d := lt_of_lt_of_le (Nat.totient_pos.mpr (by omega)) hd
  have : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  have hpH : ¬ p ∣ Nat.card H := by
    intro hdvd
    rcases hsmooth p hp hdvd with rfl | rfl | rfl <;> omega
  have hreal : ∀ h : H, IsConj h h⁻¹ := by
    intro h
    have hpos : 0 < Nat.card H := Nat.card_pos
    have hco : (Nat.card H).Coprime (Nat.card H - 1) := by
      have e : Nat.card H = 1 + (Nat.card H - 1) := by omega
      nth_rewrite 1 [e]
      exact (Nat.coprime_add_self_right.mpr (Nat.coprime_one_right _)).symm
    have hpow : h ^ (Nat.card H - 1) = h⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ, Nat.sub_add_cancel hpos, pow_card_eq_one']
    exact hpow ▸ hrat h _ hco
  let ρ' : Representation (ZMod p) H (Fin d → ZMod p) :=
    { toFun := fun h => (ρ h : (Fin d → ZMod p) →ₗ[ZMod p] (Fin d → ZMod p))
      map_one' := by rw [map_one]; rfl
      map_mul' := fun a b => by rw [map_mul]; rfl }
  have hρ' : ∀ (h : H) (v : Fin d → ZMod p), ρ' h v = ρ h v := fun _ _ => rfl
  have hfaith' : Function.Injective ρ' := by
    intro a b hab
    apply hfaith
    exact LinearEquiv.toLinearMap_injective hab
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro e2
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast e2
    have hdv := (ZMod.natCast_eq_zero_iff 2 p).mp this
    have := Nat.le_of_dvd (by norm_num) hdv
    omega
  have hSF : ∀ v : Fin d → ZMod p, v ≠ 0 → ∃ h : H, ρ' h v = (2 : ZMod p) • v := by
    intro v hv
    obtain ⟨h, hh, -⟩ := hjoint v hv 1 (by simp) (Units.mk0 2 h2) 1 (Nat.coprime_one_right _)
    exact ⟨h, hh⟩
  obtain ⟨Q, hQn, -, -, hZ⟩ := hQ
  have : Nontrivial (Subgroup.center Q) := by
    have : Finite (Subgroup.center Q) := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
    exact Finite.one_lt_card_iff_nontrivial.mp (by rw [hZ]; norm_num)
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center Q)
  let a : H := ((z : Q) : H)
  have ha : ∀ h : H, h * a * h⁻¹ = a ∨ h * a * h⁻¹ = a⁻¹ := by
    intro h
    have hwQ : h * a * h⁻¹ ∈ Q := hQn.conj_mem _ (z : Q).2 h
    have hcen : (⟨h * a * h⁻¹, hwQ⟩ : Q) ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro q
      apply Subtype.ext
      have hq : h⁻¹ * (q : H) * h ∈ Q := by
        have := hQn.conj_mem _ q.2 h⁻¹
        rwa [inv_inv] at this
      have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨h⁻¹ * (q : H) * h, hq⟩)
      change h⁻¹ * (q : H) * h * a = a * (h⁻¹ * (q : H) * h) at hc
      change (q : H) * (h * a * h⁻¹) = h * a * h⁻¹ * (q : H)
      calc (q : H) * (h * a * h⁻¹) = h * (h⁻¹ * (q : H) * h * a) * h⁻¹ := by group
        _ = h * (a * (h⁻¹ * (q : H) * h)) * h⁻¹ := by rw [hc]
        _ = h * a * h⁻¹ * (q : H) := by group
    rcases eq_one_or_eq_or_eq_inv_of_card_three hZ hz ⟨⟨h * a * h⁻¹, hwQ⟩, hcen⟩ with e | e | e
    · exfalso
      have e' : h * a * h⁻¹ = 1 := congrArg (fun t : Subgroup.center Q => ((t : Q) : H)) e
      have : a = 1 := by
        calc a = h⁻¹ * (h * a * h⁻¹) * h := by group
          _ = 1 := by rw [e']; group
      exact hz (Subtype.ext (Subtype.ext this))
    · left
      exact congrArg (fun t : Subgroup.center Q => ((t : Q) : H)) e
    · right
      exact congrArg (fun t : Subgroup.center Q => ((t : Q) : H)) e
  have hsq := sq_eq_one_of_conj_eq_self_or_inv hp7 ρ' hpH hreal hfaith'
    (fun W hW => hirr W hW) hSF a ha
  -- but `a` has order three
  have ha3 : a ^ 3 = 1 := by
    have : z ^ 3 = 1 := by rw [← hZ]; exact pow_card_eq_one'
    exact congrArg (fun t : Subgroup.center Q => ((t : Q) : H)) this
  have ha1 : a = 1 := by
    calc a = a ^ 3 * (a ^ 2)⁻¹ := by group
      _ = 1 := by rw [ha3, hsq]; simp
  exact hz (Subtype.ext (Subtype.ext ha1))
