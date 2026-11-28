import OMAReductions.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_zero_mem_of_lt_R1

-- Reduction SymbolLengthMilnorKTheory.symbol_length_problem.variants.zero_mem_of_lt.R1.H1.R1 of step SymbolLengthMilnorKTheory.symbol_length_problem.variants.zero_mem_of_lt.R1.H1
-- Credit: @hyprspacecoyote
--
-- K_3(C(x, y))/p = 0 for odd p. Milnor's degree filtration on K_3(F(t))/p is proved here (the
-- generation half of Milnor's exact sequence, which needs no transfer): every symbol of polynomials
-- of degree <= d reduces, modulo lower degrees, to symbols {g_2, g_3, pi} with pi monic irreducible of
-- degree d and deg g_i < d; and {g_2, g_3, pi} = 0 whenever the class {g_2 mod pi, g_3 mod pi}
-- vanishes in K_2(F[t]/pi)/p (K_*(F[t]/pi) acts on the truncated piece through the unique lifts of
-- degree < d; the defect of multiplicativity is a lower-degree symbol by Steinberg's relation).
-- Applied to C(x) = C(t) (residue fields C, K_3(C)/p = 0) and then to C(x, y) = C(x)(t). The input left
-- as hypotheses is K_2 of the residue fields F[t]/pi of C(x)(t) mod p, split as
--   H1  Tsen: these function fields of curves are C_1 (forms of degree d in more than d variables
--       have a nontrivial zero);
--   H2  the Kummer norm relation {a, N(k)} = 0 in K_2/p over them.
-- From H1 and H2: b is a norm from kappa(a^(1/p)) (zero of N(x) - b y^p), so {a, b} = 0.

namespace OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_zero_mem_of_lt_R1_H1_R1

def H1 : Prop := ∀ (π : Polynomial (MvRatFunc (Fin 1) ℂ)) [Fact (Irreducible π)] (d N : ℕ)
    (Φ : MvPolynomial (Fin N) (AdjoinRoot π)), 0 < d → Φ.IsHomogeneous d → d < N →
    ∃ v : Fin N → AdjoinRoot π, v ≠ 0 ∧ MvPolynomial.eval v Φ = 0

def H2 : Prop := ∀ (π : Polynomial (MvRatFunc (Fin 1) ℂ)) [Fact (Irreducible π)] (p : ℕ), p.Prime →
    ∀ (a : (AdjoinRoot π)ˣ) (k : AdjoinRoot (Polynomial.X ^ p - Polynomial.C (a : AdjoinRoot π)))
      (hk : Algebra.norm (AdjoinRoot π) k ≠ 0),
    MilnorK.of p a * MilnorK.of p (Units.mk0 (Algebra.norm (AdjoinRoot π) k) hk : (AdjoinRoot π)ˣ) = 0


namespace MilnorGen

/-- Ring maps out of `MilnorK F ℓ`: an additive map from `Fˣ` into a ring that kills the
Steinberg relations and `ℓ`. -/
theorem exists_lift {F : Type*} [Field F] (ℓ : ℕ) {R : Type*} [Ring R] (f : Additive Fˣ →+ R)
    (hst : ∀ a b : Fˣ, (a : F) + (b : F) = 1 → f (Additive.ofMul a) * f (Additive.ofMul b) = 0)
    (hℓ : (ℓ : R) = 0) :
    ∃ θ : MilnorK F ℓ →+* R, ∀ a : Fˣ, θ (MilnorK.of ℓ a) = f (Additive.ofMul a) := by
  refine ⟨RingQuot.lift ⟨(TensorAlgebra.lift ℤ f.toIntLinearMap).toRingHom, ?_⟩, ?_⟩
  · intro x y h
    cases h with
    | steinberg a b h => simpa using hst a b h
    | natCast => simpa using hℓ
  · intro a
    simp [MilnorK.of, RingQuot.lift_mkRingHom_apply]

/-- The truncated action `v ↦ (0, g0 a v.1, g1 a v.2.1)` on `Q0 × Q1 × Q2`. -/
theorem exists_rep {M Q0 Q1 Q2 : Type*} [AddCommGroup M] [AddCommGroup Q0] [AddCommGroup Q1]
    [AddCommGroup Q2] (g0 : M →+ Q0 →+ Q1) (g1 : M →+ Q1 →+ Q2) :
    ∃ f : M →+ AddMonoid.End (Q0 × Q1 × Q2), ∀ a v, f a v = (0, g0 a v.1, g1 a v.2.1) := by
  refine ⟨AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun v => (0, g0 a v.1, g1 a v.2.1))
    (fun v w => by simp)) (fun a b => DFunLike.ext _ _ fun v => by
      show ((0 : Q0), g0 (a + b) v.1, g1 (a + b) v.2.1) =
        ((0 : Q0), g0 a v.1, g1 a v.2.1) + ((0 : Q0), g0 b v.1, g1 b v.2.1)
      simp), fun a v => rfl⟩

/-- The action lemma.  In a ring `A` with `p = 0`, let `c : κˣ → A` be additive only up to `J`
after multiplying `P`, killing `J`, and killing the Steinberg relations.  Then a relation
`{a, b} = 0` in `K_2(κ)/p` forces `c a * (c b * P) = 0`. -/
theorem action {κ A : Type*} [Field κ] [Ring A] (p : ℕ) (hp : (p : A) = 0) (c : κˣ → A) (P : A)
    (J : AddSubgroup A)
    (hadd1 : ∀ a b : κˣ, c (a * b) * P - (c a * P + c b * P) ∈ J)
    (hJ : ∀ a : κˣ, ∀ z ∈ J, c a * z = 0)
    (hadd2 : ∀ a b e : κˣ, c (a * b) * (c e * P) = c a * (c e * P) + c b * (c e * P))
    (hst : ∀ a b : κˣ, (a : κ) + (b : κ) = 1 → c a * c b = 0)
    (a b : κˣ) (hab : (MilnorK.of p a * MilnorK.of p b : MilnorK κ p) = 0) :
    c a * (c b * P) = 0 := by
  let G0 : AddSubgroup A := AddSubgroup.zmultiples P
  let G1 : AddSubgroup A := AddSubgroup.closure (Set.range fun e : κˣ ↦ c e * P)
  let Q1 := ↥G1 ⧸ J.addSubgroupOf G1
  have hmem0 : ∀ (e : κˣ) (v : A), v ∈ G0 → c e * v ∈ G1 := by
    rintro e v ⟨n, rfl⟩
    rw [mul_smul_comm]
    exact zsmul_mem (AddSubgroup.subset_closure (Set.mem_range_self e)) n
  -- g0 : a ↦ (v ↦ [c a * v])
  let g0' : κˣ → (↥G0 →+ Q1) := fun e ↦
    { toFun := fun v ↦ (QuotientAddGroup.mk (⟨c e * v, hmem0 e v v.2⟩ : ↥G1) : Q1)
      map_zero' := by
        show (QuotientAddGroup.mk (⟨c e * 0, _⟩ : ↥G1) : Q1) = 0
        rw [← QuotientAddGroup.mk_zero]; congr 1; ext; simp
      map_add' := fun v w ↦ by
        rw [← QuotientAddGroup.mk_add]; congr 1; ext; simp [mul_add] }
  have hg0add : ∀ a b : κˣ, g0' (a * b) = g0' a + g0' b := by
    intro a b
    ext ⟨v, n, rfl⟩
    show (QuotientAddGroup.mk (⟨c (a * b) * (n • P), _⟩ : ↥G1) : Q1) =
      QuotientAddGroup.mk (⟨c a * (n • P), _⟩ : ↥G1) + QuotientAddGroup.mk (⟨c b * (n • P), _⟩ : ↥G1)
    rw [← QuotientAddGroup.mk_add, QuotientAddGroup.eq]
    show -(⟨c (a * b) * (n • P), _⟩ : ↥G1) + (_ + _) ∈ J.addSubgroupOf G1
    rw [AddSubgroup.mem_addSubgroupOf]
    have : (↑(-(⟨c (a * b) * (n • P), hmem0 _ _ ⟨n, rfl⟩⟩ : ↥G1) +
        ((⟨c a * (n • P), hmem0 _ _ ⟨n, rfl⟩⟩ : ↥G1) + ⟨c b * (n • P), hmem0 _ _ ⟨n, rfl⟩⟩)) : A) =
        -(n • (c (a * b) * P - (c a * P + c b * P))) := by
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, mul_smul_comm]
      rw [smul_sub, smul_add]; abel
    rw [this]
    exact J.neg_mem (J.zsmul_mem (hadd1 a b) n)
  let g0 : Additive κˣ →+ (↥G0 →+ Q1) :=
    AddMonoidHom.mk' (fun e ↦ g0' e.toMul) (fun x y ↦ hg0add x.toMul y.toMul)
  -- g1 : a ↦ ([y] ↦ c a * y)
  have hJ1 : ∀ e : κˣ, J.addSubgroupOf G1 ≤
      (AddMonoidHom.ker ((AddMonoidHom.mulLeft (c e)).comp G1.subtype)) := by
    intro e y hy
    rw [AddSubgroup.mem_addSubgroupOf] at hy
    simp [hJ e _ hy]
  let g1' : κˣ → (Q1 →+ A) := fun e ↦
    QuotientAddGroup.lift _ ((AddMonoidHom.mulLeft (c e)).comp G1.subtype) (hJ1 e)
  have hG1add : ∀ a b : κˣ, ∀ y ∈ G1, c (a * b) * y = c a * y + c b * y := by
    intro a b y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy => obtain ⟨e, rfl⟩ := hy; exact hadd2 a b e
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, mul_add, mul_add, hx, hy]; abel
    | neg x _ hx => rw [mul_neg, mul_neg, mul_neg, hx, neg_add]
  have hg1add : ∀ a b : κˣ, g1' (a * b) = g1' a + g1' b := by
    intro a b
    refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun y ↦ ?_)
    show c (a * b) * (y : A) = c a * (y : A) + c b * (y : A)
    exact hG1add a b y y.2
  let g1 : Additive κˣ →+ (Q1 →+ A) :=
    AddMonoidHom.mk' (fun e ↦ g1' e.toMul) (fun x y ↦ hg1add x.toMul y.toMul)
  obtain ⟨f, hf⟩ := exists_rep (Q0 := ↥G0) (Q1 := Q1) (Q2 := A) g0 g1
  have hmul : ∀ u v : AddMonoid.End (↥G0 × Q1 × A), ∀ w, (u * v) w = u (v w) := fun _ _ _ ↦ rfl
  obtain ⟨θ, hθ⟩ := exists_lift (F := κ) (R := AddMonoid.End (↥G0 × Q1 × A)) p f (by
    intro a b hab
    refine DFunLike.ext _ _ fun v ↦ ?_
    rw [hmul, hf, hf, AddMonoid.End.zero_apply, map_zero]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    show c a * (c b * (v.1 : A)) = 0
    obtain ⟨n, hn⟩ := v.1.2
    rw [← hn, mul_smul_comm, mul_smul_comm, ← mul_assoc, hst a b hab, zero_mul, smul_zero]) (by
    refine DFunLike.ext _ _ fun v ↦ ?_
    rw [AddMonoid.End.natCast_apply, AddMonoid.End.zero_apply]
    have h0 : ∀ x : A, p • x = 0 := fun x ↦ by rw [nsmul_eq_mul, hp, zero_mul]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show p • v.1 = 0
      exact Subtype.ext (by simp [h0])
    · show p • v.2.1 = 0
      induction v.2.1 using QuotientAddGroup.induction_on with
      | H y =>
        rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
        have hy0 : p • y = 0 := Subtype.ext (by simp [h0])
        rw [hy0]; exact zero_mem _
    · show p • v.2.2 = 0
      exact h0 _)
  have key := congrArg (fun T ↦ T ((⟨P, 1, one_zsmul P⟩ : ↥G0), (0 : Q1), (0 : A))) (congrArg θ hab)
  simp only [map_mul, hθ, map_zero, AddMonoid.End.zero_apply] at key
  rw [hmul, hf, hf] at key
  have := congrArg (fun v : ↥G0 × Q1 × A ↦ v.2.2) key
  simp only [Prod.snd_zero] at this
  exact this

end MilnorGen
namespace MatzriN

open Polynomial

variable {F : Type*} [Field F] (p : ℕ)

/-- The norm form of `F[θ]/(θ^p - a)` in the power coordinates is a homogeneous polynomial of
degree `p`. -/
theorem exists_normPoly (hp : 0 < p) (a : F) : ∃ Φ : MvPolynomial (Fin p) F, Φ.IsHomogeneous p ∧
    ∀ c : Fin p → F, MvPolynomial.eval c Φ = Algebra.norm F
      (∑ l : Fin p, c l • (AdjoinRoot.root (X ^ p - C a)) ^ (l : ℕ)) := by
  set B := AdjoinRoot.powerBasis' (monic_X_pow_sub_C a hp.ne') with hB
  have hdim : B.dim = p := by
    rw [hB, AdjoinRoot.powerBasis'_dim, natDegree_X_pow_sub_C]
  set M : Matrix (Fin B.dim) (Fin B.dim) (MvPolynomial (Fin p) F) := Matrix.of fun i j ↦
    ∑ l : Fin p, MvPolynomial.X l * MvPolynomial.C (Algebra.leftMulMatrix B.basis
      ((AdjoinRoot.root (X ^ p - C a)) ^ (l : ℕ)) i j) with hM
  refine ⟨M.det, ?_, ?_⟩
  · have key : M.det.IsHomogeneous B.dim := by
      rw [Matrix.det_apply']
      apply MvPolynomial.IsHomogeneous.sum
      intro σ _
      have h0 : MvPolynomial.IsHomogeneous
          ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (Fin p) F)) 0 := by
        rw [← map_intCast (MvPolynomial.C : F →+* MvPolynomial (Fin p) F)]
        exact MvPolynomial.isHomogeneous_C _ _
      have h1 := MvPolynomial.IsHomogeneous.prod (s := Finset.univ)
        (φ := fun i : Fin B.dim ↦ M (σ i) i) (n := fun _ ↦ 1) (by
        intro i _
        simp only [hM, Matrix.of_apply]
        apply MvPolynomial.IsHomogeneous.sum
        intro l _
        simpa using (MvPolynomial.isHomogeneous_X F l).mul (MvPolynomial.isHomogeneous_C _ _))
      simpa using h0.mul h1
    convert key using 1
    exact hdim.symm
  · intro c
    rw [RingHom.map_det, Algebra.norm_eq_matrix_det B.basis]
    congr 1
    ext i j
    simp only [hM, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul,
      MvPolynomial.eval_X, MvPolynomial.eval_C, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    simp only [map_smul, Matrix.smul_apply, smul_eq_mul]

theorem norm_zero' (hp : 0 < p) (a : F) : Algebra.norm F
    (∑ l : Fin p, (0 : Fin p → F) l • (AdjoinRoot.root (X ^ p - C a)) ^ (l : ℕ)) = 0 := by
  set B := AdjoinRoot.powerBasis' (monic_X_pow_sub_C a hp.ne')
  have hdeg : (X ^ p - C a).degree ≠ 0 := by
    rw [degree_X_pow_sub_C hp]; exact_mod_cast hp.ne'
  haveI : Nontrivial (AdjoinRoot (X ^ p - C a)) := AdjoinRoot.nontrivial _ hdeg
  letI := Module.Free.of_basis B.basis
  letI := B.finite
  simp

/-- Over a non-`p`-th power, the norm vanishes only at `0`. -/
theorem norm_eq_zero' (hp : p.Prime) (a : F) (ha : ∀ b : F, b ^ p ≠ a) (c : Fin p → F)
    (h : Algebra.norm F (∑ l : Fin p, c l • (AdjoinRoot.root (X ^ p - C a)) ^ (l : ℕ)) = 0) :
    c = 0 := by
  haveI : Fact (Irreducible (X ^ p - C a)) := ⟨X_pow_sub_C_irreducible_of_prime hp ha⟩
  have hp0 := hp.pos
  set B := AdjoinRoot.powerBasis' (monic_X_pow_sub_C a hp0.ne') with hB
  letI := Module.Free.of_basis B.basis
  letI := B.finite
  have he := (Algebra.norm_eq_zero_iff).mp h
  have hli := B.basis.linearIndependent
  have hd : B.dim = p := by rw [hB, AdjoinRoot.powerBasis'_dim, natDegree_X_pow_sub_C]
  rw [Fintype.linearIndependent_iff] at hli
  funext l
  have := hli (fun i ↦ c (Fin.cast hd i)) (by
    rw [← he]
    refine Fintype.sum_equiv (finCongr hd) _ _ fun i ↦ ?_
    rw [PowerBasis.coe_basis]
    simp only [hB, AdjoinRoot.powerBasis'_gen]
    rfl)
  simpa using this (Fin.cast hd.symm l)

end MatzriN

namespace MilnorGen

open MilnorK Polynomial

variable {K : Type*} [Field K] (p : ℕ)

theorem of_add_of_inv (a : Kˣ) : of p a + of p a⁻¹ = 0 := by
  rw [← of_mul, mul_inv_cancel, of_one]

theorem of_mul_of_neg_self (a : Kˣ) : of p a * of p (-a) = 0 := by
  by_cases ha : a = 1
  · simp [ha]
  have h1 : (1 : K) - a ≠ 0 := by
    intro h; apply ha; apply Units.ext; show (a : K) = 1; linear_combination -h
  have h2 : (1 : K) - (a⁻¹ : Kˣ) ≠ 0 := by
    intro h; apply ha; apply Units.ext; show (a : K) = 1
    have : ((a⁻¹ : Kˣ) : K) = 1 := by linear_combination -h
    simpa using congrArg (fun z : K ↦ z⁻¹) this
  set b := Units.mk0 _ h1
  set c := Units.mk0 _ h2
  have hb : of p a * of p b = 0 := of_mul_of_eq_zero p a b (by simp [b])
  have hc : of p a⁻¹ * of p c = 0 := of_mul_of_eq_zero p a⁻¹ c (by simp [c])
  have hc' : of p a * of p c = 0 := by
    have := congrArg (· * of p c) (of_add_of_inv p a)
    simp only [add_mul, hc, add_zero, zero_mul] at this; exact this
  have hc'' : of p a * of p c⁻¹ = 0 := by
    have := congrArg (of p a * ·) (of_add_of_inv p c)
    simp only [mul_add, hc', zero_add, mul_zero] at this; exact this
  have hneg : -a = b * c⁻¹ := by
    have ha0 : (a : K) ≠ 0 := a.ne_zero
    ext
    simp only [Units.val_neg, Units.val_mul, b, c, Units.val_mk0, Units.val_inv_eq_inv_val]
    field_simp
    have : (a : K) - 1 ≠ 0 := by intro h; apply h1; linear_combination -h
    field_simp
    ring
  rw [hneg, of_mul, mul_add, hb, hc'', add_zero]

theorem of_anticomm (a b : Kˣ) : of p a * of p b + of p b * of p a = 0 := by
  have h := of_mul_of_neg_self p (a * b)
  rw [of_mul, add_mul] at h
  have e1 : -(a * b) = (-a) * b := by simp
  have e2 : -(a * b) = a * (-b) := by simp
  have t1 : of p a * of p (-(a * b)) = of p a * of p b := by
    rw [e1, of_mul, mul_add, of_mul_of_neg_self, zero_add]
  have t2 : of p b * of p (-(a * b)) = of p b * of p a := by
    rw [e2, of_mul, mul_add, of_mul_of_neg_self, add_zero]
  rw [t1, t2] at h; exact h

theorem swap12 (a b c : Kˣ) (h : of p a * of p b * of p c = 0) : of p b * of p a * of p c = 0 := by
  have := congrArg (· * of p c) (of_anticomm p a b)
  simp only [add_mul, zero_mul, h, zero_add] at this; exact this

theorem swap23 (a b c : Kˣ) (h : of p a * of p b * of p c = 0) : of p a * of p c * of p b = 0 := by
  have := congrArg (of p a * ·) (of_anticomm p b c)
  simp only [mul_add, mul_zero, ← mul_assoc, h, zero_add] at this; exact this

variable {F : Type*} [Field F] (φ : F[X] →+* K)

theorem φne (hφ : Function.Injective φ) {f : F[X]} (hf : f ≠ 0) : φ f ≠ 0 :=
  (map_ne_zero_iff φ hφ).mpr hf

/-- The step `(P)`: `{g₂, g₃, π} = 0` for `deg gᵢ < deg π`, given that all symbols of lower
degree polynomials vanish and `K_2(F[t]/π)/p = 0`. -/
theorem pstep (hφ : Function.Injective φ) (d : ℕ) (hd : 1 ≤ d) (π : F[X]) (hmon : π.Monic) (hdeg : π.natDegree = d)
    [Fact (Irreducible π)]
    (hp : ((p : ℕ) : MilnorK K p) = 0)
    (IH : ∀ u v w : Kˣ, (∃ f : F[X], f.natDegree ≤ d - 1 ∧ (u : K) = φ f) →
      (∃ f : F[X], f.natDegree ≤ d - 1 ∧ (v : K) = φ f) →
      (∃ f : F[X], f.natDegree ≤ d - 1 ∧ (w : K) = φ f) → of p u * of p v * of p w = 0)
    (hκ : ∀ a b : (AdjoinRoot π)ˣ, (MilnorK.of p a * MilnorK.of p b : MilnorK (AdjoinRoot π) p) = 0)
    (g2 g3 : F[X]) (h2 : g2 ≠ 0) (h3 : g3 ≠ 0) (d2 : g2.natDegree < d) (d3 : g3.natDegree < d) :
    of p (Units.mk0 _ (φne φ hφ h2)) * of p (Units.mk0 _ (φne φ hφ h3)) *
      of p (Units.mk0 _ (φne φ hφ hmon.ne_zero)) = 0 := by
  classical
  have hπ1 : π ≠ 1 := by intro h; rw [h, natDegree_one] at hdeg; omega
  -- canonical lifts
  let rep : AdjoinRoot π → F[X] := fun x ↦ Function.surjInv AdjoinRoot.mk_surjective x %ₘ π
  have hrep_mk : ∀ x, AdjoinRoot.mk π (rep x) = x := by
    intro x
    have h := modByMonic_add_div (Function.surjInv AdjoinRoot.mk_surjective x) π
    have hx := Function.surjInv_eq (f := AdjoinRoot.mk π) AdjoinRoot.mk_surjective x
    conv_rhs => rw [← hx, ← h]
    rw [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]
  have hrep_deg : ∀ x, (rep x).natDegree < d := fun x ↦ by
    rw [← hdeg]; exact natDegree_modByMonic_lt _ hmon hπ1
  have huniq : ∀ g : F[X], g.natDegree < d → ∀ x, AdjoinRoot.mk π g = x → g = rep x := by
    intro g hg x hx
    have hdvd : π ∣ g - rep x := by
      rw [← AdjoinRoot.mk_eq_zero, map_sub, hx, hrep_mk, sub_self]
    have hlt : (g - rep x).natDegree < π.natDegree := by
      rw [hdeg]; exact (natDegree_sub_le _ _).trans_lt (max_lt hg (hrep_deg x))
    exact sub_eq_zero.mp (eq_zero_of_dvd_of_natDegree_lt hdvd hlt)
  have hrep_ne : ∀ x : (AdjoinRoot π)ˣ, rep x ≠ 0 := by
    intro x h; apply x.ne_zero; rw [← hrep_mk x, h, map_zero]
  let U : ∀ x : (AdjoinRoot π)ˣ, Kˣ := fun x ↦ Units.mk0 _ (φne φ hφ (hrep_ne x))
  let c : (AdjoinRoot π)ˣ → MilnorK K p := fun x ↦ of p (U x)
  set Pπ := Units.mk0 _ (φne φ hφ hmon.ne_zero) with hPπ
  let J : AddSubgroup (MilnorK K p) := AddSubgroup.closure {z | ∃ u v : Kˣ,
    (∃ f : F[X], f.natDegree ≤ d - 1 ∧ (u : K) = φ f) ∧
    (∃ f : F[X], f.natDegree ≤ d - 1 ∧ (v : K) = φ f) ∧ z = of p u * of p v}
  have hlow : ∀ x : (AdjoinRoot π)ˣ, ∃ f : F[X], f.natDegree ≤ d - 1 ∧ ((U x : Kˣ) : K) = φ f :=
    fun x ↦ ⟨rep x, by have := hrep_deg x; omega, rfl⟩
  have hgen : ∀ u v : Kˣ, (∃ f : F[X], f.natDegree ≤ d - 1 ∧ (u : K) = φ f) →
      (∃ f : F[X], f.natDegree ≤ d - 1 ∧ (v : K) = φ f) → of p u * of p v ∈ J :=
    fun u v hu hv ↦ AddSubgroup.subset_closure ⟨u, v, hu, hv, rfl⟩
  have hJ : ∀ a : (AdjoinRoot π)ˣ, ∀ z ∈ J, c a * z = 0 := by
    intro a z hz
    have hle : J ≤ (AddMonoidHom.mulLeft (c a)).ker := by
      rw [AddSubgroup.closure_le]
      rintro _ ⟨u, v, hu, hv, rfl⟩
      show c a * (of p u * of p v) = 0
      rw [← mul_assoc]; exact IH _ _ _ (hlow a) hu hv
    exact hle hz
  -- the defect unit `w = rep a * rep b / rep (a b)`
  have hdefect : ∀ a b : (AdjoinRoot π)ˣ, ∃ W : Kˣ,
      of p W + of p (U (a * b)) = of p (U a) + of p (U b) ∧ of p W * of p Pπ ∈ J := by
    intro a b
    have hdvd : π ∣ rep a * rep b - rep (a * b) := by
      rw [← AdjoinRoot.mk_eq_zero, map_sub, map_mul, hrep_mk, hrep_mk, hrep_mk]
      exact sub_self _
    obtain ⟨h, hh⟩ := hdvd
    have hW0 : φ (rep a) * φ (rep b) / φ (rep (a * b)) ≠ 0 :=
      div_ne_zero (mul_ne_zero (φne φ hφ (hrep_ne a)) (φne φ hφ (hrep_ne b)))
        (φne φ hφ (hrep_ne (a * b)))
    set W := Units.mk0 _ hW0
    have hWU : W * U (a * b) = U a * U b := by
      ext
      show φ (rep a) * φ (rep b) / φ (rep (a * b)) * φ (rep (a * b)) = φ (rep a) * φ (rep b)
      exact div_mul_cancel₀ _ (φne φ hφ (hrep_ne (a * b)))
    have hof : of p W + of p (U (a * b)) = of p (U a) + of p (U b) := by
      rw [← of_mul, hWU, of_mul]
    refine ⟨W, hof, ?_⟩
    by_cases hh0 : h = 0
    · have hW1 : W = 1 := by
        ext; simp only [W, Units.val_mk0, Units.val_one]
        have : rep a * rep b = rep (a * b) := by rw [hh0, mul_zero, sub_eq_zero] at hh; exact hh
        rw [← map_mul, this]
        exact div_self (φne φ hφ (hrep_ne (a * b)))
      rw [hW1, of_one, zero_mul]; exact zero_mem _
    -- degree of h is at most d - 2
    have hdh : (-h).natDegree ≤ d - 1 := by
      rw [natDegree_neg]
      have h1 : (rep a * rep b - rep (a * b)).natDegree ≤ 2 * (d - 1) := by
        refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
        · refine natDegree_mul_le.trans ?_
          have := hrep_deg a; have := hrep_deg b; omega
        · have := hrep_deg (a * b); omega
      rw [hh, natDegree_mul hmon.ne_zero hh0, hdeg] at h1
      omega
    have hnh : -h ≠ 0 := neg_ne_zero.mpr hh0
    set H := Units.mk0 _ (φne φ hφ hnh)
    have hV0 : φ π * φ (-h) / φ (rep (a * b)) ≠ 0 :=
      div_ne_zero (mul_ne_zero (φne φ hφ hmon.ne_zero) (φne φ hφ hnh)) (φne φ hφ (hrep_ne (a * b)))
    set V := Units.mk0 _ hV0
    have hVU : V * U (a * b) = Pπ * H := by
      ext
      show φ π * φ (-h) / φ (rep (a * b)) * φ (rep (a * b)) = φ π * φ (-h)
      exact div_mul_cancel₀ _ (φne φ hφ (hrep_ne (a * b)))
    have hst : of p W * of p V = 0 := by
      apply of_mul_of_eq_zero
      show φ (rep a) * φ (rep b) / φ (rep (a * b)) + φ π * φ (-h) / φ (rep (a * b)) = 1
      have hr := φne φ hφ (hrep_ne (a * b))
      have hk' : rep a * rep b = rep (a * b) + π * h := by rw [← hh]; ring
      have hk := congrArg φ hk'
      simp only [map_mul, map_add] at hk
      rw [map_neg, ← add_div, hk, mul_neg, add_neg_cancel_right]
      exact div_self hr
    have hof2 : of p V + of p (U (a * b)) = of p Pπ + of p H := by
      rw [← of_mul, hVU, of_mul]
    -- of W * of Pπ = of W * of (U (a b)) - of W * of H
    have e : of p W * of p Pπ = of p W * of p (U (a * b)) - of p W * of p H := by
      have := congrArg (of p W * ·) hof2
      simp only [mul_add, hst, zero_add] at this
      rw [this]; abel
    have hWx : ∀ u : Kˣ, (∃ f : F[X], f.natDegree ≤ d - 1 ∧ (u : K) = φ f) →
        of p W * of p u ∈ J := by
      intro u hu
      have hWe : of p W = of p (U a) + of p (U b) - of p (U (a * b)) := eq_sub_of_add_eq hof
      rw [hWe, sub_mul, add_mul]
      exact J.sub_mem (J.add_mem (hgen _ _ (hlow a) hu) (hgen _ _ (hlow b) hu))
        (hgen _ _ (hlow (a * b)) hu)
    rw [e]
    exact J.sub_mem (hWx _ (hlow (a * b))) (hWx H ⟨-h, hdh, rfl⟩)
  have hadd1 : ∀ a b : (AdjoinRoot π)ˣ, c (a * b) * of p Pπ - (c a * of p Pπ + c b * of p Pπ) ∈ J := by
    intro a b
    obtain ⟨W, hof, hWPπ⟩ := hdefect a b
    have : c (a * b) * of p Pπ - (c a * of p Pπ + c b * of p Pπ) = -(of p W * of p Pπ) := by
      show of p (U (a * b)) * of p Pπ - (of p (U a) * of p Pπ + of p (U b) * of p Pπ) = _
      rw [← add_mul, ← hof, add_mul]; abel
    rw [this]; exact J.neg_mem hWPπ
  have hadd2 : ∀ a b e : (AdjoinRoot π)ˣ,
      c (a * b) * (c e * of p Pπ) = c a * (c e * of p Pπ) + c b * (c e * of p Pπ) := by
    intro a b e
    obtain ⟨W, hof, hWPπ⟩ := hdefect a b
    have h1 : of p W * (c e * of p Pπ) = 0 := by
      have hac := congrArg (· * of p Pπ) (of_anticomm p W (U e))
      simp only [add_mul, zero_mul] at hac
      have h2 : of p (U e) * of p W * of p Pπ = 0 := by
        rw [mul_assoc]; exact hJ e _ hWPπ
      rw [h2, add_zero] at hac
      rw [← mul_assoc]; exact hac
    show of p (U (a * b)) * (c e * of p Pπ) = of p (U a) * (c e * of p Pπ) + of p (U b) * (c e * of p Pπ)
    rw [← add_mul, ← hof, add_mul, h1, zero_add]
  have hstc : ∀ a b : (AdjoinRoot π)ˣ, (a : AdjoinRoot π) + (b : AdjoinRoot π) = 1 → c a * c b = 0 := by
    intro a b hab
    have hsum : rep a + rep b = 1 := by
      have := huniq (rep a + rep b) ((natDegree_add_le _ _).trans_lt
        (max_lt (hrep_deg a) (hrep_deg b))) 1 (by rw [map_add, hrep_mk, hrep_mk, hab])
      have h1 := huniq 1 (by rw [natDegree_one]; omega) 1 (map_one _)
      rw [this, ← h1]
    apply of_mul_of_eq_zero
    simp only [U, Units.val_mk0, ← map_add, hsum, map_one]
  -- apply the action lemma to the classes of `g2` and `g3`
  have hu : ∀ g : F[X], g ≠ 0 → g.natDegree < d → AdjoinRoot.mk π g ≠ 0 := by
    intro g hg hgd h0
    rw [AdjoinRoot.mk_eq_zero] at h0
    exact hg (eq_zero_of_dvd_of_natDegree_lt h0 (by rw [hdeg]; exact hgd))
  set A2 := Units.mk0 _ (hu g2 h2 d2)
  set A3 := Units.mk0 _ (hu g3 h3 d3)
  have key := action p hp c (of p Pπ) J hadd1 hJ hadd2 hstc A2 A3 (hκ A2 A3)
  have e2 : U A2 = Units.mk0 _ (φne φ hφ h2) := by
    ext; simp only [U, Units.val_mk0]; rw [← huniq g2 d2 A2 rfl]
  have e3 : U A3 = Units.mk0 _ (φne φ hφ h3) := by
    ext; simp only [U, Units.val_mk0]; rw [← huniq g3 d3 A3 rfl]
  have : c A2 * (c A3 * of p Pπ) = 0 := key
  simp only [c, e2, e3] at this
  rw [mul_assoc]; exact this

end MilnorGen

namespace MilnorGen

open MilnorK Polynomial

variable {K : Type*} [Field K] (p : ℕ) {F : Type*} [Field F] (φ : F[X] →+* K)

theorem trichotomy (hφ : Function.Injective φ) (d : ℕ) (hd : 1 ≤ d) (u : Kˣ)
    (hu : ∃ f : F[X], f.natDegree ≤ d ∧ (u : K) = φ f) :
    (∃ f : F[X], f.natDegree ≤ d - 1 ∧ (u : K) = φ f) ∨
    (∃ u1 u2 : Kˣ, u = u1 * u2 ∧ (∃ f : F[X], f.natDegree ≤ d - 1 ∧ (u1 : K) = φ f) ∧
      (∃ f : F[X], f.natDegree ≤ d - 1 ∧ (u2 : K) = φ f)) ∨
    (∃ (uc : Kˣ) (π : F[X]) (hπ : π.Monic), Irreducible π ∧ π.natDegree = d ∧
      (∃ f : F[X], f.natDegree ≤ d - 1 ∧ (uc : K) = φ f) ∧
      u = uc * Units.mk0 _ (φne φ hφ hπ.ne_zero)) := by
  classical
  obtain ⟨f, hfd, hf⟩ := hu
  by_cases hlow : f.natDegree ≤ d - 1
  · exact Or.inl ⟨f, hlow, hf⟩
  have hfdeg : f.natDegree = d := by omega
  have hf0 : f ≠ 0 := by intro h; apply u.ne_zero; rw [hf, h, map_zero]
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  set m := f * C f.leadingCoeff⁻¹ with hm
  have hmon : m.Monic := monic_mul_leadingCoeff_inv hf0
  have hmdeg : m.natDegree = d := by
    rw [hm, natDegree_mul_C (inv_ne_zero hlc), hfdeg]
  have hfm : f = C f.leadingCoeff * m := by
    rw [hm, mul_comm, mul_assoc, ← C_mul, inv_mul_cancel₀ hlc, C_1, mul_one]
  have hc0 : (C f.leadingCoeff : F[X]) ≠ 0 := C_ne_zero.mpr hlc
  by_cases hirr : Irreducible m
  · right; right
    refine ⟨Units.mk0 _ (φne φ hφ hc0), m, hmon, hirr, hmdeg, ⟨_, by simp, rfl⟩, ?_⟩
    ext
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0, hf, ← map_mul, ← hfm]
  · right; left
    have hnu : ¬IsUnit m := by
      intro h; rw [natDegree_eq_zero_of_isUnit h] at hmdeg; omega
    have : ∃ a b : F[X], m = a * b ∧ ¬IsUnit a ∧ ¬IsUnit b := by
      by_contra hcon
      push Not at hcon
      exact hirr ⟨hnu, fun a b h ↦ by
        by_contra hab; push Not at hab; exact hab.2 (hcon a b h hab.1)⟩
    obtain ⟨a, b, hab, ha, hb⟩ := this
    have ha0 : a ≠ 0 := by rintro rfl; rw [zero_mul] at hab; exact hmon.ne_zero hab
    have hb0 : b ≠ 0 := by rintro rfl; rw [mul_zero] at hab; exact hmon.ne_zero hab
    have hda : 0 < a.natDegree := natDegree_pos_iff_degree_pos.mpr
      (degree_pos_of_ne_zero_of_nonunit ha0 ha)
    have hdb : 0 < b.natDegree := natDegree_pos_iff_degree_pos.mpr
      (degree_pos_of_ne_zero_of_nonunit hb0 hb)
    have hsum : a.natDegree + b.natDegree = d := by
      rw [← hmdeg, hab, natDegree_mul ha0 hb0]
    have hca0 : C f.leadingCoeff * a ≠ 0 := mul_ne_zero hc0 ha0
    refine ⟨Units.mk0 _ (φne φ hφ hca0), Units.mk0 _ (φne φ hφ hb0), ?_,
      ⟨_, by rw [natDegree_C_mul hlc]; omega, rfl⟩, ⟨b, by omega, rfl⟩⟩
    ext
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0, hf, ← map_mul, mul_assoc, ← hab, ← hfm]

theorem of_sq_zero (hm1 : of p (-1 : Kˣ) = 0) (x : Kˣ) : of p x * of p x = 0 := by
  have h := of_mul_of_neg_self p x
  rw [show -x = (-1) * x by simp, of_mul, mul_add, hm1, mul_zero, zero_add] at h
  exact h

theorem two_pi (hφ : Function.Injective φ) (d : ℕ) (π π' : F[X]) (hπ : π.Monic) (hπ' : π'.Monic)
    (hd : π.natDegree = d) (hd' : π'.natDegree = d) (hne : π ≠ π') :
    ∃ R : Kˣ, (∃ f : F[X], f.natDegree ≤ d - 1 ∧ (R : K) = φ f) ∧
      of p (Units.mk0 _ (φne φ hφ hπ.ne_zero)) * of p (Units.mk0 _ (φne φ hφ hπ'.ne_zero)) =
        of p R * of p (Units.mk0 _ (φne φ hφ hπ'.ne_zero)) -
          of p R * of p (Units.mk0 _ (φne φ hφ hπ.ne_zero)) +
          of p (Units.mk0 _ (φne φ hφ hπ.ne_zero)) * of p (Units.mk0 _ (φne φ hφ hπ.ne_zero)) := by
  set r := π' - π with hr
  have hr0 : r ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hrd : r.natDegree ≤ d - 1 := by
    have hlt : r.degree < π'.degree := by
      rw [hr]
      exact degree_sub_lt (by rw [degree_eq_natDegree hπ'.ne_zero, degree_eq_natDegree hπ.ne_zero,
        hd, hd']) hπ'.ne_zero (by rw [hπ'.leadingCoeff, hπ.leadingCoeff])
    have := natDegree_lt_natDegree hr0 hlt
    omega
  have hnr : -r ≠ 0 := neg_ne_zero.mpr hr0
  set R := Units.mk0 _ (φne φ hφ hnr)
  refine ⟨R, ⟨-r, by rw [natDegree_neg]; exact hrd, rfl⟩, ?_⟩
  set P := Units.mk0 _ (φne φ hφ hπ.ne_zero)
  set P' := Units.mk0 _ (φne φ hφ hπ'.ne_zero)
  set S1 := R * P⁻¹
  set S2 := P' * P⁻¹
  have hS : (S1 : K) + S2 = 1 := by
    have hP := φne φ hφ hπ.ne_zero
    simp only [S1, S2, R, P, P', Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, map_neg, hr,
      map_sub]
    field_simp
    ring
  have hst := of_mul_of_eq_zero p S1 S2 hS
  simp only [S1, S2, of_mul] at hst
  have hinv : of p P⁻¹ = 0 - of p P := by
    rw [eq_sub_iff_add_eq, ← of_mul, inv_mul_cancel, of_one]
  rw [hinv] at hst
  have : of p P * of p P' = of p P * of p P' + (of p R + (0 - of p P)) * (of p P' + (0 - of p P)) := by
    rw [hst, add_zero]
  rw [this]
  simp only [add_mul, mul_add, sub_mul, mul_sub, zero_mul, mul_zero]
  abel

end MilnorGen

namespace MilnorGen

open MilnorK Polynomial

variable {K : Type*} [Field K] (p : ℕ) {F : Type*} [Field F] (φ : F[X] →+* K)

/-- Milnor's filtration argument in degree `3`: every symbol of polynomials vanishes. -/
theorem claim_all (hφ : Function.Injective φ) (hm1 : of p (-1 : Kˣ) = 0)
    (hp : ((p : ℕ) : MilnorK K p) = 0)
    (h0 : ∀ u v w : Kˣ, (∃ f : F[X], f.natDegree ≤ 0 ∧ (u : K) = φ f) →
      (∃ f : F[X], f.natDegree ≤ 0 ∧ (v : K) = φ f) →
      (∃ f : F[X], f.natDegree ≤ 0 ∧ (w : K) = φ f) → of p u * of p v * of p w = 0)
    (hκ : ∀ (π : F[X]) [Fact (Irreducible π)], π.Monic → 1 ≤ π.natDegree →
      ∀ a b : (AdjoinRoot π)ˣ, (MilnorK.of p a * MilnorK.of p b : MilnorK (AdjoinRoot π) p) = 0) :
    ∀ d, ∀ u v w : Kˣ, (∃ f : F[X], f.natDegree ≤ d ∧ (u : K) = φ f) →
      (∃ f : F[X], f.natDegree ≤ d ∧ (v : K) = φ f) →
      (∃ f : F[X], f.natDegree ≤ d ∧ (w : K) = φ f) → of p u * of p v * of p w = 0 := by
  intro d
  induction d with
  | zero => exact h0
  | succ d IH =>
    have hd1 : 1 ≤ d + 1 := by omega
    have up : ∀ u : Kˣ, (∃ f : F[X], f.natDegree ≤ d ∧ (u : K) = φ f) →
        (∃ f : F[X], f.natDegree ≤ d + 1 ∧ (u : K) = φ f) :=
      fun u ⟨f, hf, he⟩ ↦ ⟨f, by omega, he⟩
    have bigπ : ∀ (π : F[X]) (hπ : π.Monic), π.natDegree = d + 1 →
        ∃ f : F[X], f.natDegree ≤ d + 1 ∧
          ((Units.mk0 _ (φne φ hφ hπ.ne_zero) : Kˣ) : K) = φ f :=
      fun π hπ hdeg ↦ ⟨π, hdeg.le, rfl⟩
    -- one high slot (first), via (P)
    have hA : ∀ u v w : Kˣ, (∃ f : F[X], f.natDegree ≤ d + 1 ∧ (u : K) = φ f) →
        (∃ f : F[X], f.natDegree ≤ d ∧ (v : K) = φ f) →
        (∃ f : F[X], f.natDegree ≤ d ∧ (w : K) = φ f) → of p u * of p v * of p w = 0 := by
      intro u v w hu hv hw
      rcases trichotomy φ hφ (d + 1) hd1 u hu with hlow | ⟨u1, u2, rfl, h1, h2⟩ |
          ⟨uc, π, hπ, hirr, hdeg, hc, rfl⟩
      · exact IH u v w hlow hv hw
      · rw [of_mul, add_mul, add_mul, IH _ _ _ h1 hv hw, IH _ _ _ h2 hv hw, add_zero]
      · rw [of_mul, add_mul, add_mul, IH _ _ _ hc hv hw, zero_add]
        haveI : Fact (Irreducible π) := ⟨hirr⟩
        obtain ⟨g2, hg2d, hg2⟩ := hv
        obtain ⟨g3, hg3d, hg3⟩ := hw
        have h2 : g2 ≠ 0 := by intro h; apply v.ne_zero; rw [hg2, h, map_zero]
        have h3 : g3 ≠ 0 := by intro h; apply w.ne_zero; rw [hg3, h, map_zero]
        have key := pstep p φ hφ (d + 1) hd1 π hπ hdeg hp IH
          (hκ π hπ (by omega)) g2 g3 h2 h3 (by omega) (by omega)
        have ev : v = Units.mk0 _ (φne φ hφ h2) := by ext; exact hg2
        have ew : w = Units.mk0 _ (φne φ hφ h3) := by ext; exact hg3
        rw [← ev, ← ew] at key
        exact swap12 p _ _ _ (swap23 p _ _ _ key)
    -- two high slots (first two)
    have hB : ∀ u v w : Kˣ, (∃ f : F[X], f.natDegree ≤ d + 1 ∧ (u : K) = φ f) →
        (∃ f : F[X], f.natDegree ≤ d + 1 ∧ (v : K) = φ f) →
        (∃ f : F[X], f.natDegree ≤ d ∧ (w : K) = φ f) → of p u * of p v * of p w = 0 := by
      intro u v w hu hv hw
      have lowfirst : ∀ u' : Kˣ, (∃ f : F[X], f.natDegree ≤ d ∧ (u' : K) = φ f) →
          of p u' * of p v * of p w = 0 :=
        fun u' hu' ↦ swap12 p _ _ _ (hA v u' w hv hu' hw)
      rcases trichotomy φ hφ (d + 1) hd1 u hu with hlow | ⟨u1, u2, rfl, h1, h2⟩ |
          ⟨uc, π, hπ, hirr, hdeg, hc, rfl⟩
      · exact lowfirst u hlow
      · rw [of_mul, add_mul, add_mul, lowfirst _ h1, lowfirst _ h2, add_zero]
      · rw [of_mul, add_mul, add_mul, lowfirst _ hc, zero_add]
        set P := Units.mk0 _ (φne φ hφ hπ.ne_zero)
        have hP := bigπ π hπ hdeg
        rcases trichotomy φ hφ (d + 1) hd1 v hv with vlow | ⟨v1, v2, rfl, h1, h2⟩ |
            ⟨vc, π', hπ', hirr', hdeg', hc', rfl⟩
        · exact hA P v w hP vlow hw
        · rw [of_mul, mul_add, add_mul, hA P _ _ hP h1 hw, hA P _ _ hP h2 hw, add_zero]
        · rw [of_mul, mul_add, add_mul, hA P _ _ hP hc' hw, zero_add]
          by_cases he : π = π'
          · subst he; rw [of_sq_zero p hm1, zero_mul]
          · obtain ⟨R, hR, hid⟩ := two_pi p φ hφ (d + 1) π π' hπ hπ' hdeg hdeg' he
            rw [hid, add_mul, sub_mul, of_sq_zero p hm1, zero_mul, add_zero,
              swap12 p _ _ _ (hA _ R w (bigπ π' hπ' hdeg') hR hw),
              swap12 p _ _ _ (hA _ R w hP hR hw), sub_zero]
    -- three high slots
    intro u v w hu hv hw
    have lowlast : ∀ u' v' w' : Kˣ, (∃ f : F[X], f.natDegree ≤ d + 1 ∧ (u' : K) = φ f) →
        (∃ f : F[X], f.natDegree ≤ d + 1 ∧ (v' : K) = φ f) →
        (∃ f : F[X], f.natDegree ≤ d ∧ (w' : K) = φ f) → of p w' * of p u' * of p v' = 0 :=
      fun u' v' w' hu' hv' hw' ↦ swap12 p _ _ _ (swap23 p _ _ _ (hB u' v' w' hu' hv' hw'))
    have lowmid : ∀ u' v' w' : Kˣ, (∃ f : F[X], f.natDegree ≤ d + 1 ∧ (u' : K) = φ f) →
        (∃ f : F[X], f.natDegree ≤ d + 1 ∧ (v' : K) = φ f) →
        (∃ f : F[X], f.natDegree ≤ d ∧ (w' : K) = φ f) → of p u' * of p w' * of p v' = 0 :=
      fun u' v' w' hu' hv' hw' ↦ swap23 p _ _ _ (hB u' v' w' hu' hv' hw')
    rcases trichotomy φ hφ (d + 1) hd1 w hw with wlow | ⟨w1, w2, rfl, h1, h2⟩ |
        ⟨wc, π, hπ, hirr, hdeg, hc, rfl⟩
    · exact hB u v w hu hv wlow
    · rw [of_mul, mul_add, hB _ _ _ hu hv h1, hB _ _ _ hu hv h2, add_zero]
    · rw [of_mul, mul_add, hB _ _ _ hu hv hc, zero_add]
      set P := Units.mk0 _ (φne φ hφ hπ.ne_zero)
      have hP := bigπ π hπ hdeg
      rcases trichotomy φ hφ (d + 1) hd1 u hu with ulow | ⟨u1, u2, rfl, h1, h2⟩ |
          ⟨uc, π'', hπ'', hirr'', hdeg'', hc'', rfl⟩
      · exact lowlast v P u hv hP ulow
      · rw [of_mul, add_mul, add_mul, lowlast v P _ hv hP h1, lowlast v P _ hv hP h2, add_zero]
      · rw [of_mul, add_mul, add_mul, lowlast v P _ hv hP hc'', zero_add]
        set P'' := Units.mk0 _ (φne φ hφ hπ''.ne_zero)
        have hP'' := bigπ π'' hπ'' hdeg''
        rcases trichotomy φ hφ (d + 1) hd1 v hv with vlow | ⟨v1, v2, rfl, h1, h2⟩ |
            ⟨vc, π', hπ', hirr', hdeg', hc', rfl⟩
        · exact lowmid P'' P v hP'' hP vlow
        · rw [of_mul, mul_add, add_mul, lowmid P'' P _ hP'' hP h1, lowmid P'' P _ hP'' hP h2,
            add_zero]
        · rw [of_mul, mul_add, add_mul, lowmid P'' P _ hP'' hP hc', zero_add]
          by_cases he : π'' = π'
          · subst he; rw [of_sq_zero p hm1, zero_mul]
          · obtain ⟨R, hR, hid⟩ := two_pi p φ hφ (d + 1) π'' π' hπ'' hπ' hdeg'' hdeg' he
            rw [hid, add_mul, sub_mul, of_sq_zero p hm1, zero_mul, add_zero,
              lowlast _ P R (bigπ π' hπ' hdeg') hP hR, lowlast _ P R hP'' hP hR, sub_zero]

end MilnorGen

namespace MilnorGen

open MilnorK Polynomial

theorem symbol3 {E : Type*} [Field E] (p : ℕ) (s : Fin 3 → Eˣ) :
    MilnorK.symbol p s = of p (s 0) * of p (s 1) * of p (s 2) := by
  simp [MilnorK.symbol_succ, mul_assoc]

theorem grade3_bot_of {E : Type*} [Field E] (p : ℕ)
    (h : ∀ u v w : Eˣ, of p u * of p v * of p w = 0) : MilnorK.grade E p 3 = ⊥ := by
  rw [eq_bot_iff, MilnorK.grade, AddSubgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_bot, symbol3]
  exact h _ _ _

theorem sym3_of_grade3 {E : Type*} [Field E] (p : ℕ) (h : MilnorK.grade E p 3 = ⊥)
    (u v w : Eˣ) : of p u * of p v * of p w = 0 := by
  have := MilnorK.symbol_mem_grade E p ![u, v, w]
  rw [h, AddSubgroup.mem_bot, symbol3] at this
  simpa using this

/-- Functoriality of `K^M_*(-)/p` along a field embedding. -/
theorem exists_map {E E' : Type*} [Field E] [Field E'] (p : ℕ) (ψ : E →+* E') :
    ∃ Θ : MilnorK E p →+* MilnorK E' p, ∀ a : Eˣ, Θ (of p a) = of p (Units.map ψ.toMonoidHom a) := by
  obtain ⟨θ, hθ⟩ := exists_lift (F := E) (R := MilnorK E' p) p
    ((MilnorK.ofHom p).comp (MonoidHom.toAdditive (Units.map ψ.toMonoidHom)))
    (fun a b hab ↦ by
      apply MilnorK.of_mul_of_eq_zero
      show ψ (a : E) + ψ (b : E) = 1
      rw [← map_add, hab, map_one]) (MilnorK.natCast_eq_zero p)
  exact ⟨θ, fun a ↦ by rw [hθ]; rfl⟩

/-- Degree `3` vanishing for `F(t)` from vanishing for `F` and for `K_2` of the residue fields. -/
theorem grade3_vanish {K F : Type*} [Field K] [Field F] (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (φ : F[X] →+* K) (hφ : Function.Injective φ)
    (hfrac : ∀ x : K, ∃ f g : F[X], g ≠ 0 ∧ x * φ g = φ f)
    (hF : MilnorK.grade F p 3 = ⊥)
    (hκ : ∀ (π : F[X]) [Fact (Irreducible π)], π.Monic → 1 ≤ π.natDegree →
      ∀ a b : (AdjoinRoot π)ˣ, (MilnorK.of p a * MilnorK.of p b : MilnorK (AdjoinRoot π) p) = 0) :
    MilnorK.grade K p 3 = ⊥ := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hm1 : of p (-1 : Kˣ) = 0 := by
    have : (-1 : Kˣ) = (-1) ^ p := (hodd.neg_one_pow).symm
    rw [this, of_pow, nsmul_eq_mul, natCast_eq_zero, zero_mul]
  obtain ⟨Θ, hΘ⟩ := exists_map p (φ.comp C)
  have h0 : ∀ u v w : Kˣ, (∃ f : F[X], f.natDegree ≤ 0 ∧ (u : K) = φ f) →
      (∃ f : F[X], f.natDegree ≤ 0 ∧ (v : K) = φ f) →
      (∃ f : F[X], f.natDegree ≤ 0 ∧ (w : K) = φ f) → of p u * of p v * of p w = 0 := by
    have hc : ∀ u : Kˣ, (∃ f : F[X], f.natDegree ≤ 0 ∧ (u : K) = φ f) →
        ∃ c : Fˣ, u = Units.map (φ.comp C).toMonoidHom c := by
      rintro u ⟨f, hf, hu⟩
      rw [eq_C_of_natDegree_le_zero hf] at hu
      have hc0 : f.coeff 0 ≠ 0 := by
        intro h0; apply u.ne_zero; rw [hu, h0, C_0, map_zero]
      exact ⟨Units.mk0 _ hc0, by ext; simp [hu]⟩
    intro u v w hu hv hw
    obtain ⟨cu, rfl⟩ := hc u hu
    obtain ⟨cv, rfl⟩ := hc v hv
    obtain ⟨cw, rfl⟩ := hc w hw
    rw [← hΘ, ← hΘ, ← hΘ, ← map_mul, ← map_mul, sym3_of_grade3 p hF, map_zero]
  have hall := claim_all p φ hφ hm1 (MilnorK.natCast_eq_zero p) h0 hκ
  have hpoly : ∀ u v w : Kˣ, (∃ f : F[X], (u : K) = φ f) → (∃ f : F[X], (v : K) = φ f) →
      (∃ f : F[X], (w : K) = φ f) → of p u * of p v * of p w = 0 := by
    rintro u v w ⟨f1, h1⟩ ⟨f2, h2⟩ ⟨f3, h3⟩
    exact hall (f1.natDegree + f2.natDegree + f3.natDegree) u v w ⟨f1, by omega, h1⟩
      ⟨f2, by omega, h2⟩ ⟨f3, by omega, h3⟩
  apply grade3_bot_of
  have hdec : ∀ x : Kˣ, ∃ a b : Kˣ, (∃ f : F[X], (a : K) = φ f) ∧ (∃ f : F[X], (b : K) = φ f) ∧
      of p x + of p b = of p a := by
    intro x
    obtain ⟨f, g, hg, hfg⟩ := hfrac x
    have hφg := φne φ hφ hg
    have hφf : φ f ≠ 0 := by rw [← hfg]; exact mul_ne_zero x.ne_zero hφg
    refine ⟨Units.mk0 _ hφf, Units.mk0 _ hφg, ⟨f, rfl⟩, ⟨g, rfl⟩, ?_⟩
    rw [← of_mul]; congr 1; ext; simp [hfg]
  intro u v w
  obtain ⟨a1, b1, ha1, hb1, e1⟩ := hdec u
  obtain ⟨a2, b2, ha2, hb2, e2⟩ := hdec v
  obtain ⟨a3, b3, ha3, hb3, e3⟩ := hdec w
  rw [eq_sub_of_add_eq e1, eq_sub_of_add_eq e2, eq_sub_of_add_eq e3]
  simp only [sub_mul, mul_sub, hpoly _ _ _ ha1 ha2 ha3, hpoly _ _ _ ha1 ha2 hb3,
    hpoly _ _ _ ha1 hb2 ha3, hpoly _ _ _ ha1 hb2 hb3, hpoly _ _ _ hb1 ha2 ha3,
    hpoly _ _ _ hb1 ha2 hb3, hpoly _ _ _ hb1 hb2 ha3, hpoly _ _ _ hb1 hb2 hb3, sub_zero]

end MilnorGen

namespace MilnorGen

open MilnorK Polynomial

/-- `K_2(κ)/p = 0` for a `C_1` field `κ` with the Kummer norm relation. -/
theorem k2_vanish {κ : Type*} [Field κ] (p : ℕ) (hp : p.Prime)
    (hC1 : ∀ (d N : ℕ) (Φ : MvPolynomial (Fin N) κ), 0 < d → Φ.IsHomogeneous d → d < N →
      ∃ v : Fin N → κ, v ≠ 0 ∧ MvPolynomial.eval v Φ = 0)
    (hN : ∀ (a : κˣ) (k : AdjoinRoot (X ^ p - C (a : κ))) (hk : Algebra.norm κ k ≠ 0),
      of p a * of p (Units.mk0 _ hk) = 0)
    (a b : κˣ) : of p a * of p b = 0 := by
  classical
  by_cases hpw : ∃ u : κ, u ^ p = (a : κ)
  · obtain ⟨u, hu⟩ := hpw
    have hu0 : u ≠ 0 := by
      intro h0; apply a.ne_zero; rw [← hu, h0, zero_pow hp.pos.ne']
    have : a = (Units.mk0 u hu0) ^ p := by ext; simp [hu]
    rw [this, of_pow, nsmul_eq_mul, natCast_eq_zero, zero_mul, zero_mul]
  push Not at hpw
  obtain ⟨Ψ, hΨh, hΨe⟩ := MatzriN.exists_normPoly p hp.pos (a : κ)
  set Φ : MvPolynomial (Fin (p + 1)) κ := MvPolynomial.rename Fin.castSucc Ψ -
    MvPolynomial.C (b : κ) * MvPolynomial.X (Fin.last p) ^ p with hΦ
  have hΦh : Φ.IsHomogeneous p := by
    apply MvPolynomial.IsHomogeneous.sub (hΨh.rename_isHomogeneous)
    have := (MvPolynomial.isHomogeneous_C (Fin (p + 1)) (b : κ)).mul
      ((MvPolynomial.isHomogeneous_X κ (Fin.last p)).pow p)
    rwa [zero_add, one_mul] at this
  obtain ⟨v, hv0, hv⟩ := hC1 p (p + 1) Φ hp.pos hΦh (by omega)
  set c : Fin p → κ := v ∘ Fin.castSucc
  set y := v (Fin.last p)
  have heq : MvPolynomial.eval c Ψ = (b : κ) * y ^ p := by
    have := hv
    simp only [hΦ, map_sub, map_mul, map_pow, MvPolynomial.eval_rename, MvPolynomial.eval_C,
      MvPolynomial.eval_X] at this
    exact sub_eq_zero.mp this
  rw [hΨe] at heq
  have hy : y ≠ 0 := by
    intro hy0
    rw [hy0, zero_pow hp.pos.ne', mul_zero] at heq
    have hc := MatzriN.norm_eq_zero' p hp (a : κ) hpw c heq
    apply hv0
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · exact hy0
    · exact congrFun hc j
  have hk : Algebra.norm κ (∑ l : Fin p, c l • (AdjoinRoot.root (X ^ p - C (a : κ))) ^ (l : ℕ)) ≠ 0 := by
    rw [heq]; exact mul_ne_zero b.ne_zero (pow_ne_zero _ hy)
  have h := hN a _ hk
  have hu : Units.mk0 _ hk = b * (Units.mk0 y hy) ^ p := by ext; simp [heq]
  rw [hu, of_mul, of_pow, nsmul_eq_mul, natCast_eq_zero, zero_mul, add_zero] at h
  exact h

/-- Degree `3` over `ℂ(x)`. -/
theorem grade3_one (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    MilnorK.grade (MvRatFunc (Fin 1) ℂ) p 3 = ⊥ := by
  classical
  set σ0 : ℂ[X] ≃ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
    (MvPolynomial.pUnitAlgEquiv.{0, 0} ℂ).symm.trans
      (MvPolynomial.renameEquiv ℂ (Equiv.ofUnique PUnit.{1} (Fin 1)))
  set ι := algebraMap (MvPolynomial (Fin 1) ℂ) (MvRatFunc (Fin 1) ℂ)
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  set φ0 : ℂ[X] →+* MvRatFunc (Fin 1) ℂ := ι.comp σ0.toRingEquiv.toRingHom
  have hφ0 : Function.Injective φ0 := hι.comp σ0.injective
  refine grade3_vanish p hp hp2 φ0 hφ0 ?_ ?_ ?_
  · intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin 1) ℂ) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    refine ⟨σ0.symm a, σ0.symm b, by simpa using hb0, ?_⟩
    have e1 : φ0 (σ0.symm a) = ι a := by simp [φ0]
    have e2 : φ0 (σ0.symm b) = ι b := by simp [φ0]
    rw [e1, e2, div_mul_cancel₀ _ ((map_ne_zero_iff ι hι).mpr hb0)]
  · exact MilnorK.grade_eq_bot_of_forall_exists_pow_eq ℂ p (fun a ↦ by
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ) hp.pos
      have hz0 : z ≠ 0 := fun h ↦ a.ne_zero (by rw [← hz, h, zero_pow hp.pos.ne'])
      exact ⟨Units.mk0 z hz0, Units.ext (by simp [hz])⟩) (by norm_num)
  · intro π _ hmon hdeg a b
    have h1 : π.natDegree = 1 := by
      have := IsAlgClosed.degree_eq_one_of_irreducible ℂ (Fact.out : Irreducible π)
      rw [degree_eq_natDegree hmon.ne_zero] at this; exact_mod_cast this
    have hconst : ∀ x : AdjoinRoot π, ∃ c : ℂ, x = algebraMap ℂ (AdjoinRoot π) c := by
      intro x
      obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
      have hlt : (g %ₘ π).natDegree < 1 := by
        rw [← h1]; exact natDegree_modByMonic_lt _ hmon (by intro h; rw [h] at h1; simp at h1)
      refine ⟨(g %ₘ π).coeff 0, ?_⟩
      have hmod := modByMonic_add_div g π
      conv_lhs => rw [← hmod]
      rw [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero,
        eq_C_of_natDegree_le_zero (Nat.lt_one_iff.mp hlt).le, AdjoinRoot.mk_C]
      simp
    have hpow : ∀ x : (AdjoinRoot π)ˣ, of p x = 0 := by
      intro x
      obtain ⟨c, hc⟩ := hconst x
      have hc0 : c ≠ 0 := by intro h; apply x.ne_zero; rw [hc, h, map_zero]
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c hp.pos
      have hz0 : z ≠ 0 := fun h ↦ hc0 (by rw [← hz, h, zero_pow hp.pos.ne'])
      have hz1 : algebraMap ℂ (AdjoinRoot π) z ≠ 0 := by
        intro h; apply x.ne_zero; rw [hc, ← hz, map_pow, h, zero_pow hp.pos.ne']
      have : x = (Units.mk0 _ hz1) ^ p := by ext; simp [hc, ← hz]
      rw [this, of_pow, nsmul_eq_mul, natCast_eq_zero, zero_mul]
    rw [hpow a, zero_mul]

end MilnorGen

namespace MilnorGen

open MilnorK Polynomial

/-- Degree `3` over `ℂ(x, y)`, from `C_1` and the norm relation over the residue fields. -/
theorem grade3_two (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hC1 : ∀ (π : Polynomial (MvRatFunc (Fin 1) ℂ)) [Fact (Irreducible π)] (d N : ℕ)
      (Φ : MvPolynomial (Fin N) (AdjoinRoot π)), 0 < d → Φ.IsHomogeneous d → d < N →
      ∃ v : Fin N → AdjoinRoot π, v ≠ 0 ∧ MvPolynomial.eval v Φ = 0)
    (hN : ∀ (π : Polynomial (MvRatFunc (Fin 1) ℂ)) [Fact (Irreducible π)] (a : (AdjoinRoot π)ˣ)
      (k : AdjoinRoot (X ^ p - C (a : AdjoinRoot π))) (hk : Algebra.norm (AdjoinRoot π) k ≠ 0),
      of p a * of p (Units.mk0 (Algebra.norm (AdjoinRoot π) k) hk : (AdjoinRoot π)ˣ) = 0) :
    MilnorK.grade (MvRatFunc (Fin 2) ℂ) p 3 = ⊥ := by
  classical
  set A := MvPolynomial (Fin 1) ℂ
  set F1 := MvRatFunc (Fin 1) ℂ
  set K := MvRatFunc (Fin 2) ℂ
  set σ : Polynomial A ≃ₐ[ℂ] MvPolynomial (Fin 2) ℂ := (MvPolynomial.finSuccEquiv ℂ 1).symm
  set ι := algebraMap (MvPolynomial (Fin 2) ℂ) K
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  set g : A →+* K := ι.comp (σ.toRingEquiv.toRingHom.comp Polynomial.C)
  have hg : Function.Injective g :=
    hι.comp (σ.injective.comp Polynomial.C_injective)
  set ψ : F1 →+* K := IsFractionRing.lift hg
  set φ : Polynomial F1 →+* K := Polynomial.eval₂RingHom ψ (ι (MvPolynomial.X 0))
  have hσX : σ Polynomial.X = MvPolynomial.X 0 := by
    rw [AlgEquiv.symm_apply_eq]; exact (MvPolynomial.finSuccEquiv_X_zero).symm
  have key : ∀ q : Polynomial A, φ (q.map (algebraMap A F1)) = ι (σ q) := by
    have : φ.comp (Polynomial.mapRingHom (algebraMap A F1)) = ι.comp σ.toRingEquiv.toRingHom := by
      apply Polynomial.ringHom_ext
      · intro a
        simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C, φ,
          Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, ψ, IsFractionRing.lift_algebraMap]
        rfl
      · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X, φ,
          Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
        show ι (MvPolynomial.X 0) = ι (σ Polynomial.X)
        rw [hσX]
    intro q
    exact congrArg (fun h ↦ h q) this
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors A) f
    have hb0 : algebraMap A F1 (b : A) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A F1)).mpr (nonZeroDivisors.ne_zero b.2)
    have hsm : (b : A) • f = Polynomial.C (algebraMap A F1 (b : A)) * f := by
      rw [← Polynomial.smul_eq_C_mul, algebraMap_smul]
    have h1 : φ ((IsLocalization.integerNormalization (nonZeroDivisors A) f).map
        (algebraMap A F1)) = 0 := by
      rw [hb, hsm, map_mul, hf, mul_zero]
    rw [key, map_eq_zero_iff _ hι, map_eq_zero_iff _ σ.injective] at h1
    have h2 : (b : A) • f = 0 := by rw [← hb, h1, Polynomial.map_zero]
    rw [hsm] at h2
    exact (mul_eq_zero.mp h2).resolve_left (by simpa using hb0)
  refine grade3_vanish p hp hp2 φ hφ ?_ (grade3_one p hp hp2) ?_
  · intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin 2) ℂ) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    refine ⟨(σ.symm a).map (algebraMap A F1), (σ.symm b).map (algebraMap A F1), ?_, ?_⟩
    · intro h
      have := congrArg φ h
      rw [key, map_zero, AlgEquiv.apply_symm_apply, map_eq_zero_iff _ hι] at this
      exact hb0 this
    · rw [key, key, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply,
        div_mul_cancel₀ _ ((map_ne_zero_iff ι hι).mpr hb0)]
  · intro π _ _ _ a b
    exact k2_vanish p hp (hC1 π) (hN π) a b

end MilnorGen

theorem main : H1 → H2 → OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_zero_mem_of_lt_R1.H1 := by
  intro hC1 hN p hp hp2
  rw [MilnorK.zero_mem_symbolLengthBounds_iff]
  exact MilnorGen.grade3_two p hp hp2 hC1 (fun π _ a k hk ↦ hN π p hp a k hk)

end OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_zero_mem_of_lt_R1_H1_R1
