import OMAReductions.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_R1_H2_R1

-- Reduction SymbolLengthMilnorKTheory.symbol_length_problem.variants.degree_two.R1.H2.R1.H1.R1 of step SymbolLengthMilnorKTheory.symbol_length_problem.variants.degree_two.R1.H2.R1.H1
-- Credit: @hyprspacecoyote
--
-- Matzri's theorem for an odd prime p over C(x_1, ..., x_m): every class of K_2/p is a sum of
-- p^(m-1) - 1 symbols. The whole Kummer-space argument [Matzri 2016, Theorem 3.2 and Section 8] is
-- proved here; two inputs are left as hypotheses:
--   H1  the norm relation {a, N(k)} = 0 in K_2/p for k in F[theta]/(theta^p - a) (projection formula
--       for the Kummer extension; classical, but needs the transfer on Milnor K-theory);
--   H2  Tsen-Lang: a homogeneous form of degree d >= 1 in more than d^m variables over C(x_1, ..., x_m)
--       has a nontrivial zero (a complete Lean proof is ready as the step proof).
-- Proof. For symbols {a_1,b_1}, ..., {a_t,b_t} with no a_j a p-th power, the norm forms
--   N_0(f) = f^p,   N_j(v, k) = N_(j-1)(v) a_j + N(k) b_j   (k in F[theta]/(theta^p - a_j))
-- form a homogeneous form of degree p in tp + 1 variables (the norm is a determinant). If N_t(v) != 0,
-- N_t(v) is a slot (slot lemma, induction with {a,b} = {a+b, -b/a}, {a,b}+{c,d} = {a,b/d}+{ac,d} and
-- the norm relation); a nontrivial zero at the first level where one exists merges the last two
-- symbols into {y, -y} = 0 (zero lemma). With t = p^(m-1), tp + 1 > p^m, so Tsen-Lang gives the zero
-- and the sum shortens to p^(m-1) - 1 symbols; iterating bounds every class.

namespace OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_R1_H2_R1_H1_R1

def H1 : Prop := ∀ m p : ℕ, p.Prime → ∀ (a : (MvRatFunc (Fin m) ℂ)ˣ)
    (k : AdjoinRoot (Polynomial.X ^ p - Polynomial.C (a : MvRatFunc (Fin m) ℂ))),
    ∀ hk : Algebra.norm (MvRatFunc (Fin m) ℂ) k ≠ 0,
    MilnorK.of p a * MilnorK.of p (Units.mk0 _ hk) = 0

def H2 : Prop := ∀ m d N : ℕ, ∀ Φ : MvPolynomial (Fin N) (MvRatFunc (Fin m) ℂ),
    0 < d → Φ.IsHomogeneous d → d ^ m < N →
    ∃ v : Fin N → MvRatFunc (Fin m) ℂ, v ≠ 0 ∧ MvPolynomial.eval v Φ = 0

namespace MatzriK

open MilnorK

variable {F : Type*} [Field F] (ℓ : ℕ)

theorem nsmul_ell (x : MilnorK F ℓ) : ℓ • x = 0 := by
  rw [nsmul_eq_mul, natCast_eq_zero, zero_mul]

theorem of_pow_ell (u : Fˣ) : of ℓ (u ^ ℓ) = 0 := by
  rw [of_pow, nsmul_ell]

theorem of_add_of_inv (a : Fˣ) : of ℓ a + of ℓ a⁻¹ = 0 := by
  rw [← of_mul, mul_inv_cancel, of_one]

theorem mul_of_inv (x : MilnorK F ℓ) (a : Fˣ) : x * of ℓ a + x * of ℓ a⁻¹ = 0 := by
  rw [← mul_add, of_add_of_inv, mul_zero]

theorem of_inv_mul (x : MilnorK F ℓ) (a : Fˣ) : of ℓ a * x + of ℓ a⁻¹ * x = 0 := by
  rw [← add_mul, of_add_of_inv, zero_mul]

theorem eq_of_add_eq_zero' {x y z : MilnorK F ℓ} (h1 : x + y = 0) (h2 : y + z = 0) : x = z := by
  calc x = x + (y + z) := by rw [h2, add_zero]
    _ = (x + y) + z := by rw [add_assoc]
    _ = z := by rw [h1, zero_add]

theorem eq_zero_of_add_eq_zero_left' {x y : MilnorK F ℓ} (h1 : x + y = 0) (h2 : x = 0) : y = 0 := by
  rw [h2, zero_add] at h1; exact h1

/-- `{x, -x} = 0`. -/
theorem of_mul_of_neg_self (a : Fˣ) : of ℓ a * of ℓ (-a) = 0 := by
  by_cases ha : a = 1
  · simp [ha]
  have h1 : (1 : F) - a ≠ 0 := by
    intro h; apply ha; apply Units.ext; show (a : F) = 1; linear_combination -h
  have h2 : (1 : F) - (a⁻¹ : Fˣ) ≠ 0 := by
    intro h; apply ha; apply Units.ext; show (a : F) = 1
    have : ((a⁻¹ : Fˣ) : F) = 1 := by linear_combination -h
    simpa using congrArg (fun z : F ↦ z⁻¹) this
  set b := Units.mk0 _ h1
  set c := Units.mk0 _ h2
  have hb : of ℓ a * of ℓ b = 0 := of_mul_of_eq_zero ℓ a b (by simp [b])
  have hc : of ℓ a⁻¹ * of ℓ c = 0 := of_mul_of_eq_zero ℓ a⁻¹ c (by simp [c])
  have hc' : of ℓ a * of ℓ c = 0 := by
    have := of_inv_mul ℓ (of ℓ c) a
    rw [hc, add_zero] at this; exact this
  have hc'' : of ℓ a * of ℓ c⁻¹ = 0 :=
    eq_zero_of_add_eq_zero_left' ℓ (mul_of_inv ℓ (of ℓ a) c) hc'
  have hneg : -a = b * c⁻¹ := by
    have ha0 : (a : F) ≠ 0 := a.ne_zero
    ext
    simp only [Units.val_neg, Units.val_mul, b, c, Units.val_mk0, Units.val_inv_eq_inv_val]
    field_simp
    have : (a : F) - 1 ≠ 0 := by intro h; apply h1; linear_combination -h
    field_simp
    ring
  rw [hneg, of_mul, mul_add, hb, hc'', add_zero]

/-- Anticommutativity in degree one. -/
theorem of_anticomm (a b : Fˣ) : of ℓ a * of ℓ b + of ℓ b * of ℓ a = 0 := by
  have h := of_mul_of_neg_self ℓ (a * b)
  rw [of_mul, add_mul] at h
  have e1 : -(a * b) = (-a) * b := by simp
  have e2 : -(a * b) = a * (-b) := by simp
  have t1 : of ℓ a * of ℓ (-(a * b)) = of ℓ a * of ℓ b := by
    rw [e1, of_mul, mul_add, of_mul_of_neg_self, zero_add]
  have t2 : of ℓ b * of ℓ (-(a * b)) = of ℓ b * of ℓ a := by
    rw [e2, of_mul, mul_add, of_mul_of_neg_self, add_zero]
  rw [t1, t2] at h; exact h

/-- `{a, b} = {b, a⁻¹}`. -/
theorem of_swap (a b : Fˣ) : of ℓ a * of ℓ b = of ℓ b * of ℓ a⁻¹ :=
  eq_of_add_eq_zero' ℓ (of_anticomm ℓ a b) (mul_of_inv ℓ (of ℓ b) a)

/-- `{a, b} = {a + b, -a⁻¹ b}`. -/
theorem of_add_slot (a b e : Fˣ) (h : (a : F) + b = e) :
    of ℓ a * of ℓ b = of ℓ e * of ℓ (-a⁻¹ * b) := by
  have hu : (1 : F) + ((a⁻¹ * b : Fˣ) : F) ≠ 0 := by
    have : (1 : F) + ((a⁻¹ * b : Fˣ) : F) = (a : F)⁻¹ * e := by
      rw [← h]; simp only [Units.val_mul, Units.val_inv_eq_inv_val]; field_simp
    rw [this]; exact mul_ne_zero (inv_ne_zero a.ne_zero) e.ne_zero
  set u := Units.mk0 _ hu
  have he : e = a * u := by
    ext; simp only [u, Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, ← h]
    field_simp
  have hst : of ℓ u * of ℓ (-(a⁻¹ * b)) = 0 :=
    of_mul_of_eq_zero ℓ u _ (by simp [u])
  have e1 : -a⁻¹ * b = -(a⁻¹ * b) := by simp
  rw [he, e1, of_mul, add_mul, hst, add_zero]
  have e2 : -(a⁻¹ * b) = (-a)⁻¹ * b := by simp
  have h0 : of ℓ a * of ℓ (-a)⁻¹ = 0 :=
    eq_zero_of_add_eq_zero_left' ℓ (mul_of_inv ℓ (of ℓ a) (-a)) (of_mul_of_neg_self ℓ a)
  rw [e2, of_mul, mul_add, h0, zero_add]

/-- `{a, b} + {c, d} = {a, b d⁻¹} + {a c, d}`. -/
theorem of_shift (a b c d : Fˣ) :
    of ℓ a * of ℓ b + of ℓ c * of ℓ d = of ℓ a * of ℓ (b * d⁻¹) + of ℓ (a * c) * of ℓ d := by
  have h0 : of ℓ a * of ℓ d + of ℓ a * of ℓ d⁻¹ = 0 := mul_of_inv ℓ (of ℓ a) d
  rw [of_mul, of_mul, mul_add, add_mul]
  calc of ℓ a * of ℓ b + of ℓ c * of ℓ d
      = of ℓ a * of ℓ b + of ℓ c * of ℓ d + (of ℓ a * of ℓ d + of ℓ a * of ℓ d⁻¹) := by
        rw [h0, add_zero]
    _ = of ℓ a * of ℓ b + of ℓ a * of ℓ d⁻¹ + (of ℓ a * of ℓ d + of ℓ c * of ℓ d) := by abel

/-- `{c^ℓ a, b} = {a, b}`. -/
theorem of_pow_mul_left (u a : Fˣ) (b : MilnorK F ℓ) : of ℓ (u ^ ℓ * a) * b = of ℓ a * b := by
  rw [of_mul, of_pow_ell, zero_add]

end MatzriK

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

namespace MatzriR

open MilnorK MatzriK

variable {F : Type*} [Field F] (p : ℕ)

theorem SumLE_zero : ∃ l : List (Fˣ × Fˣ), l.length ≤ 0 ∧
    (0 : MilnorK F p) = (l.map fun q ↦ of p q.1 * of p q.2).sum := ⟨[], le_rfl, rfl⟩

theorem SumLE_mono {k k' : ℕ} {x : MilnorK F p}
    (h : ∃ l : List (Fˣ × Fˣ), l.length ≤ k ∧ x = (l.map fun q ↦ of p q.1 * of p q.2).sum)
    (hk : k ≤ k') :
    ∃ l : List (Fˣ × Fˣ), l.length ≤ k' ∧ x = (l.map fun q ↦ of p q.1 * of p q.2).sum :=
  let ⟨l, hl, hx⟩ := h; ⟨l, hl.trans hk, hx⟩

theorem SumLE_add {k k' : ℕ} {x y : MilnorK F p}
    (hx : ∃ l : List (Fˣ × Fˣ), l.length ≤ k ∧ x = (l.map fun q ↦ of p q.1 * of p q.2).sum)
    (hy : ∃ l : List (Fˣ × Fˣ), l.length ≤ k' ∧ y = (l.map fun q ↦ of p q.1 * of p q.2).sum) :
    ∃ l : List (Fˣ × Fˣ), l.length ≤ k + k' ∧ x + y = (l.map fun q ↦ of p q.1 * of p q.2).sum := by
  obtain ⟨l, hl, rfl⟩ := hx
  obtain ⟨l', hl', rfl⟩ := hy
  exact ⟨l ++ l', by rw [List.length_append]; omega, by simp⟩

theorem SumLE_add_sym {k : ℕ} {x : MilnorK F p}
    (hx : ∃ l : List (Fˣ × Fˣ), l.length ≤ k ∧ x = (l.map fun q ↦ of p q.1 * of p q.2).sum)
    (u v : Fˣ) : ∃ l : List (Fˣ × Fˣ), l.length ≤ k + 1 ∧
      x + of p u * of p v = (l.map fun q ↦ of p q.1 * of p q.2).sum :=
  SumLE_add p hx ⟨[(u, v)], le_rfl, by simp⟩

theorem S_SumLE (a b : ℕ → Fˣ) (t : ℕ) : ∃ l : List (Fˣ × Fˣ), l.length ≤ t ∧
    ∑ j ∈ Finset.range t, of p (a j) * of p (b j) = (l.map fun q ↦ of p q.1 * of p q.2).sum := by
  induction t with
  | zero => exact ⟨[], le_rfl, by simp⟩
  | succ t ih =>
    rw [Finset.sum_range_succ]
    exact SumLE_add_sym p ih _ _

theorem Ico_SumLE (a b : ℕ → Fˣ) (lo : ℕ) : ∀ hi, lo ≤ hi →
    ∃ l : List (Fˣ × Fˣ), l.length ≤ hi - lo ∧
      ∑ j ∈ Finset.Ico lo hi, of p (a j) * of p (b j) = (l.map fun q ↦ of p q.1 * of p q.2).sum := by
  intro hi hle
  induction hi, hle using Nat.le_induction with
  | base => exact ⟨[], by simp, by simp⟩
  | succ hi hle ih =>
    rw [Finset.sum_Ico_succ_top hle, show hi + 1 - lo = (hi - lo) + 1 by omega]
    exact SumLE_add_sym p ih _ _

theorem helper (hp : 0 < p) (f : F) (N : ℕ → F) (hN0 : N 0 = f ^ p) (t : ℕ)
    (x : MilnorK F p)
    (hx : ∃ l : List (Fˣ × Fˣ), l.length ≤ t - 1 ∧ x = (l.map fun q ↦ of p q.1 * of p q.2).sum)
    (h : N t ≠ 0) (z : Fˣ) : ∃ l : List (Fˣ × Fˣ), l.length ≤ t ∧
      x + of p (Units.mk0 _ h) * of p z = (l.map fun q ↦ of p q.1 * of p q.2).sum := by
  cases t with
  | zero =>
    have hf : f ≠ 0 := by
      intro hf; apply h; rw [hN0, hf, zero_pow hp.ne']
    have e : Units.mk0 (N 0) h = (Units.mk0 f hf) ^ p := by
      ext; simp [hN0]
    rw [e, of_pow_ell, zero_mul, add_zero]
    simpa using hx
  | succ s =>
    simpa using SumLE_add_sym p hx (Units.mk0 _ h) z

/-- Matzri's slot lemma: a nonzero value of the norm form is a slot. -/
theorem slot (hp : 0 < p) (nrm : F → (Fin p → F) → F)
    (hrel : ∀ (a : Fˣ) (c : Fin p → F) (h : nrm a c ≠ 0), of p a * of p (Units.mk0 _ h) = 0)
    (a b : ℕ → Fˣ) (f : F) (c : ℕ → Fin p → F) (N : ℕ → F) (hN0 : N 0 = f ^ p)
    (hNs : ∀ t, N (t + 1) = N t * a t + nrm (a t) (c t) * b t) :
    ∀ t (h : N t ≠ 0), ∃ x, (∃ l : List (Fˣ × Fˣ), l.length ≤ t - 1 ∧
        x = (l.map fun q ↦ of p q.1 * of p q.2).sum) ∧
      ∃ e : Fˣ, ∑ j ∈ Finset.range t, of p (a j) * of p (b j) =
        x + of p (Units.mk0 _ h) * of p e := by
  intro t
  induction t with
  | zero =>
    intro h
    exact ⟨0, ⟨[], le_rfl, rfl⟩, 1, by simp⟩
  | succ t ih =>
    intro h
    have hval := hNs t
    have hS : ∑ j ∈ Finset.range (t + 1), of p (a j) * of p (b j) =
        ∑ j ∈ Finset.range t, of p (a j) * of p (b j) + of p (a t) * of p (b t) :=
      Finset.sum_range_succ _ _
    by_cases hn : nrm (a t) (c t) = 0
    · have hN' : N t ≠ 0 := by
        intro h0; apply h; rw [hval, h0, hn]; ring
      obtain ⟨x', hx', e', he'⟩ := ih hN'
      have hu : Units.mk0 _ h = Units.mk0 _ hN' * a t := by
        ext; simp [hval, hn]
      refine ⟨x' + of p (Units.mk0 _ hN') * of p (e' * (b t)⁻¹), ?_, b t, ?_⟩
      · rw [Nat.add_sub_cancel]; exact helper p hp f N hN0 t x' hx' hN' _
      · rw [hS, he', add_assoc, of_shift, hu, add_assoc]
    · have hrel' : of p (a t) * of p (b t) = of p (a t) * of p (Units.mk0 _ hn * b t) := by
        rw [of_mul, mul_add, hrel (a t) (c t) hn, zero_add]
      set b' := Units.mk0 _ hn * b t with hb'
      by_cases hN0' : N t = 0
      · have hu : Units.mk0 _ h = b' := by
          ext; simp [hval, hN0', b']
        refine ⟨∑ j ∈ Finset.range t, of p (a j) * of p (b j), ?_, (a t)⁻¹, ?_⟩
        · rw [Nat.add_sub_cancel]; exact S_SumLE p a b t
        · rw [hS, hrel', of_swap, hu]
      · obtain ⟨x', hx', e', he'⟩ := ih hN0'
        have hsum : ((Units.mk0 _ hN0' * a t : Fˣ) : F) + b' = Units.mk0 _ h := by
          simp [hval, b']
        refine ⟨x' + of p (Units.mk0 _ hN0') * of p (e' * b'⁻¹), ?_,
          -(Units.mk0 _ hN0' * a t)⁻¹ * b', ?_⟩
        · rw [Nat.add_sub_cancel]; exact helper p hp f N hN0 t x' hx' hN0' _
        · rw [hS, he', hrel', add_assoc, of_shift, of_add_slot p _ _ _ hsum, add_assoc]

/-- Matzri's zero lemma: a nontrivial zero of the norm form shortens the sum. -/
theorem zero_reduce (hp : p.Prime) (nrm : F → (Fin p → F) → F)
    (hrel : ∀ (a : Fˣ) (c : Fin p → F) (h : nrm a c ≠ 0), of p a * of p (Units.mk0 _ h) = 0)
    (hzero : ∀ a : F, nrm a 0 = 0)
    (hnd : ∀ a : F, (∀ u : F, u ^ p ≠ a) → ∀ c, nrm a c = 0 → c = 0)
    (a b : ℕ → Fˣ) (t : ℕ) (hpow : ∀ j < t, ∀ u : F, u ^ p ≠ a j) (f : F) (c : ℕ → Fin p → F)
    (hnt : f ≠ 0 ∨ ∃ j < t, c j ≠ 0)
    (h0 : Nat.rec (motive := fun _ ↦ F) (f ^ p)
      (fun s acc ↦ acc * a s + nrm (a s) (c s) * b s) t = 0) :
    ∃ l : List (Fˣ × Fˣ), l.length ≤ t - 1 ∧
      ∑ j ∈ Finset.range t, of p (a j) * of p (b j) = (l.map fun q ↦ of p q.1 * of p q.2).sum := by
  classical
  have hp0 := hp.pos
  let Q : ℕ → Prop := fun s ↦ ∃ (f' : F) (c' : ℕ → Fin p → F),
    (f' ≠ 0 ∨ ∃ j < s, c' j ≠ 0) ∧ Nat.rec (motive := fun _ ↦ F) (f' ^ p)
      (fun s acc ↦ acc * a s + nrm (a s) (c' s) * b s) s = 0
  have hQ : ∃ s, Q s := ⟨t, f, c, hnt, h0⟩
  have hle : Nat.find hQ ≤ t := Nat.find_min' hQ ⟨f, c, hnt, h0⟩
  obtain ⟨f', c', hnt', h0'⟩ := Nat.find_spec hQ
  have ht'0 : Nat.find hQ ≠ 0 := by
    intro h; rw [h] at hnt' h0'
    rcases hnt' with hf | ⟨j, hj, _⟩
    · exact hf (pow_eq_zero_iff hp0.ne' |>.mp h0')
    · omega
  obtain ⟨u, hu⟩ := Nat.exists_eq_succ_of_ne_zero ht'0
  rw [hu] at hnt' h0'
  set N : ℕ → F := fun s ↦ Nat.rec (motive := fun _ ↦ F) (f' ^ p)
      (fun s acc ↦ acc * a s + nrm (a s) (c' s) * b s) s with hNdef
  have hN0 : N 0 = f' ^ p := rfl
  have hNs : ∀ s, N (s + 1) = N s * a s + nrm (a s) (c' s) * b s := fun _ ↦ rfl
  have h0u : N (u + 1) = 0 := h0'
  have hpu : ∀ v : F, v ^ p ≠ a u := hpow u (by omega)
  have htriv : ∀ s, (∀ j < s, c' j = 0) → f' = 0 → N s = 0 := by
    intro s
    induction s with
    | zero => intro _ hf; rw [hN0, hf, zero_pow hp0.ne']
    | succ s ih =>
      intro hc hf
      rw [hNs, ih (fun j hj ↦ hc j (by omega)) hf, hc s (by omega), hzero]; ring
  have hpre : f' ≠ 0 ∨ ∃ j < u, c' j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hf0, hc0⟩ := hcon
    have hz := htriv u hc0 hf0
    rw [hNs, hz, zero_mul, zero_add] at h0u
    have hn : nrm (a u) (c' u) = 0 := (mul_eq_zero.mp h0u).resolve_right (b u).ne_zero
    have hcu := hnd (a u) hpu _ hn
    rcases hnt' with hf | ⟨j, hj, hcj⟩
    · exact hf hf0
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
      · exact hcj (hc0 j hj')
      · exact hcj hcu
  have hNu : N u ≠ 0 := by
    intro hz
    exact Nat.find_min hQ (show u < Nat.find hQ by omega) ⟨f', c', hpre, hz⟩
  obtain ⟨x, hx, e, he⟩ := slot p hp0 nrm hrel a b f' c' N hN0 hNs u hNu
  have hn : nrm (a u) (c' u) ≠ 0 := by
    intro hn; rw [hNs, hn, zero_mul, add_zero] at h0u
    exact hNu ((mul_eq_zero.mp h0u).resolve_right (a u).ne_zero)
  have hrel' : of p (a u) * of p (b u) = of p (a u) * of p (Units.mk0 _ hn * b u) := by
    rw [of_mul, mul_add, hrel (a u) (c' u) hn, zero_add]
  have hneg : Units.mk0 _ hn * b u = -(Units.mk0 _ hNu * a u) := by
    ext
    have := h0u
    rw [hNs] at this
    simp only [Units.val_mul, Units.val_mk0, Units.val_neg]
    linear_combination this
  have hSu1 : ∑ j ∈ Finset.range (u + 1), of p (a j) * of p (b j) =
      x + of p (Units.mk0 _ hNu) * of p (e * (Units.mk0 _ hn * b u)⁻¹) := by
    rw [Finset.sum_range_succ, he, hrel', add_assoc, of_shift, hneg, of_mul_of_neg_self, add_zero]
  have hA := helper p hp0 f' N hN0 u x hx hNu (e * (Units.mk0 _ hn * b u)⁻¹)
  rw [← hSu1] at hA
  have hsplit : ∑ j ∈ Finset.range t, of p (a j) * of p (b j) =
      ∑ j ∈ Finset.range (u + 1), of p (a j) * of p (b j) +
      ∑ j ∈ Finset.Ico (u + 1) t, of p (a j) * of p (b j) := by
    rw [Finset.sum_range_add_sum_Ico _ (by omega)]
  rw [hsplit]
  exact SumLE_mono p (SumLE_add p hA (Ico_SumLE p a b (u + 1) t (by omega))) (by omega)

end MatzriR

namespace MatzriR

open MilnorK MatzriK

variable {F : Type*} [Field F] (p : ℕ)

theorem closed_form (a b : ℕ → Fˣ) (nrm : F → (Fin p → F) → F) (f : F) (c : ℕ → Fin p → F) :
    ∀ s, Nat.rec (motive := fun _ ↦ F) (f ^ p)
      (fun s acc ↦ acc * a s + nrm (a s) (c s) * b s) s =
      f ^ p * ∏ i ∈ Finset.range s, (a i : F) +
        ∑ j ∈ Finset.range s, nrm (a j) (c j) * b j * ∏ i ∈ Finset.Ico (j + 1) s, (a i : F) := by
  intro s
  induction s with
  | zero => simp
  | succ s ih =>
    show (Nat.rec (motive := fun _ ↦ F) (f ^ p)
      (fun s acc ↦ acc * a s + nrm (a s) (c s) * b s) s) * a s + nrm (a s) (c s) * b s = _
    rw [ih, Finset.prod_range_succ, Finset.sum_range_succ, Finset.Ico_self, Finset.prod_empty,
      add_mul, Finset.sum_mul]
    have : ∀ j ∈ Finset.range s, nrm (a j) (c j) * b j * (∏ i ∈ Finset.Ico (j + 1) s, (a i : F)) * a s =
        nrm (a j) (c j) * b j * ∏ i ∈ Finset.Ico (j + 1) (s + 1), (a i : F) := by
      intro j hj
      rw [Finset.prod_Ico_succ_top (by simp at hj; omega)]; ring
    rw [Finset.sum_congr rfl this]; ring

theorem count_reduce (hp : p.Prime) (m : ℕ) (nrm : F → (Fin p → F) → F)
    (hrel : ∀ (a : Fˣ) (c : Fin p → F) (h : nrm a c ≠ 0), of p a * of p (Units.mk0 _ h) = 0)
    (hzero : ∀ a : F, nrm a 0 = 0)
    (hnd : ∀ a : F, (∀ u : F, u ^ p ≠ a) → ∀ c, nrm a c = 0 → c = 0)
    (hpoly : ∀ a : F, ∃ Φ : MvPolynomial (Fin p) F, Φ.IsHomogeneous p ∧
      ∀ c, MvPolynomial.eval c Φ = nrm a c)
    (hT : ∀ (N : ℕ) (Φ : MvPolynomial (Fin N) F), Φ.IsHomogeneous p → p ^ m < N →
      ∃ v : Fin N → F, v ≠ 0 ∧ MvPolynomial.eval v Φ = 0)
    (a b : ℕ → Fˣ) (t : ℕ) (ht : p ^ m < t * p + 1) (hpow : ∀ j < t, ∀ u : F, u ^ p ≠ a j) :
    ∃ l : List (Fˣ × Fˣ), l.length ≤ t - 1 ∧
      ∑ j ∈ Finset.range t, of p (a j) * of p (b j) = (l.map fun q ↦ of p q.1 * of p q.2).sum := by
  classical
  choose Ψ hΨh hΨe using hpoly
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : MvPolynomial (Option (Fin t × Fin p)) F, Φ =
      MvPolynomial.C (∏ i ∈ Finset.range t, (a i : F)) * MvPolynomial.X none ^ p +
      ∑ j : Fin t, MvPolynomial.C ((b j : F) * ∏ i ∈ Finset.Ico ((j : ℕ) + 1) t, (a i : F)) *
        MvPolynomial.rename (fun l ↦ some (j, l)) (Ψ (a j : F)) := ⟨_, rfl⟩
  have h1 : (MvPolynomial.C (∏ i ∈ Finset.range t, (a i : F)) * MvPolynomial.X none ^ p :
      MvPolynomial (Option (Fin t × Fin p)) F).IsHomogeneous p := by
    have := (MvPolynomial.isHomogeneous_C (Option (Fin t × Fin p)) (∏ i ∈ Finset.range t, (a i : F))).mul
      ((MvPolynomial.isHomogeneous_X F (none : Option (Fin t × Fin p))).pow p)
    rwa [zero_add, one_mul] at this
  have h2 : (∑ j : Fin t, MvPolynomial.C ((b j : F) * ∏ i ∈ Finset.Ico ((j : ℕ) + 1) t, (a i : F)) *
      MvPolynomial.rename (fun l ↦ (some (j, l) : Option (Fin t × Fin p))) (Ψ (a j : F))).IsHomogeneous p := by
    apply MvPolynomial.IsHomogeneous.sum
    intro j _
    have := (MvPolynomial.isHomogeneous_C (Option (Fin t × Fin p))
      ((b j : F) * ∏ i ∈ Finset.Ico ((j : ℕ) + 1) t, (a i : F))).mul
      ((hΨh (a j : F)).rename_isHomogeneous (f := fun l ↦ (some (j, l) : Option (Fin t × Fin p))))
    rwa [zero_add] at this
  have hΦ : Φ.IsHomogeneous p := by rw [hΦdef]; exact h1.add h2
  set e := Fintype.equivFin (Option (Fin t × Fin p))
  have hcard : Fintype.card (Option (Fin t × Fin p)) = t * p + 1 := by simp
  obtain ⟨v, hv0, hv⟩ := hT _ (MvPolynomial.rename e Φ) hΦ.rename_isHomogeneous
    (by rw [hcard]; exact ht)
  rw [MvPolynomial.eval_rename] at hv
  set w : Option (Fin t × Fin p) → F := v ∘ e with hw
  set f := w none
  set c : ℕ → Fin p → F := fun j l ↦ if h : j < t then w (some (⟨j, h⟩, l)) else 0 with hc
  have hcj : ∀ j : Fin t, c j = fun l ↦ w (some (j, l)) := by
    intro j; funext l; simp [hc, j.isLt]
  have hval : Nat.rec (motive := fun _ ↦ F) (f ^ p)
      (fun s acc ↦ acc * a s + nrm (a s) (c s) * b s) t = 0 := by
    rw [closed_form, ← hv, hΦdef]
    simp only [map_add, map_mul, map_pow, map_sum, MvPolynomial.eval_C, MvPolynomial.eval_X,
      MvPolynomial.eval_rename, hΨe]
    rw [Finset.sum_range (fun j ↦ nrm (a j) (c j) * b j * ∏ i ∈ Finset.Ico (j + 1) t, (a i : F))]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [hcj j]
      simp only [Function.comp_def]
      ring
  have hnt : f ≠ 0 ∨ ∃ j < t, c j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hf, hc0⟩ := hcon
    apply hv0
    funext i
    obtain ⟨i', rfl⟩ := e.surjective i
    show w i' = 0
    rcases i' with _ | ⟨j, l⟩
    · exact hf
    · have := congrFun (hc0 j j.isLt) l
      rw [hcj j] at this
      exact this
  exact zero_reduce p hp nrm hrel hzero hnd a b t hpow f c hnt hval

end MatzriR

namespace MatzriR

open MilnorK MatzriK

variable {F : Type*} [Field F] (p : ℕ)

theorem list_sum_range (l : List (Fˣ × Fˣ)) :
    (l.map fun q ↦ of p q.1 * of p q.2).sum = ∑ j ∈ Finset.range l.length,
      of p (l.getD j (1, 1)).1 * of p (l.getD j (1, 1)).2 := by
  induction l with
  | nil => simp
  | cons q l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

theorem reduce_one (hp : p.Prime) (m : ℕ) (hm : 1 ≤ m) (nrm : F → (Fin p → F) → F)
    (hrel : ∀ (a : Fˣ) (c : Fin p → F) (h : nrm a c ≠ 0), of p a * of p (Units.mk0 _ h) = 0)
    (hzero : ∀ a : F, nrm a 0 = 0)
    (hnd : ∀ a : F, (∀ u : F, u ^ p ≠ a) → ∀ c, nrm a c = 0 → c = 0)
    (hpoly : ∀ a : F, ∃ Φ : MvPolynomial (Fin p) F, Φ.IsHomogeneous p ∧
      ∀ c, MvPolynomial.eval c Φ = nrm a c)
    (hT : ∀ (N : ℕ) (Φ : MvPolynomial (Fin N) F), Φ.IsHomogeneous p → p ^ m < N →
      ∃ v : Fin N → F, v ≠ 0 ∧ MvPolynomial.eval v Φ = 0)
    (l : List (Fˣ × Fˣ)) (hl : l.length = p ^ (m - 1)) :
    ∃ l' : List (Fˣ × Fˣ), l'.length ≤ p ^ (m - 1) - 1 ∧
      (l.map fun q ↦ of p q.1 * of p q.2).sum = (l'.map fun q ↦ of p q.1 * of p q.2).sum := by
  classical
  by_cases hpw : ∃ q ∈ l, ∃ u : F, u ^ p = q.1
  · obtain ⟨q, hq, u, hu⟩ := hpw
    have hu0 : u ≠ 0 := by
      intro h0; apply q.1.ne_zero; rw [← hu, h0, zero_pow hp.pos.ne']
    have hq0 : of p q.1 * of p q.2 = 0 := by
      have : q.1 = (Units.mk0 u hu0) ^ p := by ext; simp [hu]
      rw [this, of_pow_ell, zero_mul]
    refine ⟨l.erase q, by rw [List.length_erase_of_mem hq, hl], ?_⟩
    have hperm := ((List.perm_cons_erase hq).map fun q ↦ of p q.1 * of p q.2).sum_eq
    rw [hperm, List.map_cons, List.sum_cons, hq0, zero_add]
  · push Not at hpw
    have hpow : ∀ j < l.length, ∀ u : F, u ^ p ≠ (l.getD j (1, 1)).1 := by
      intro j hj u
      rw [List.getD_eq_getElem _ _ hj]
      exact hpw _ (List.getElem_mem hj) u
    have ht : p ^ m < l.length * p + 1 := by
      rw [hl, ← pow_succ, Nat.sub_add_cancel hm]; omega
    obtain ⟨l', hl', he⟩ := count_reduce p hp m nrm hrel hzero hnd hpoly hT
      (fun j ↦ (l.getD j (1, 1)).1) (fun j ↦ (l.getD j (1, 1)).2) l.length ht hpow
    refine ⟨l', by rw [← hl]; exact hl', ?_⟩
    rw [list_sum_range, he]

theorem main_bound (hp : p.Prime) (m : ℕ) (hm : 1 ≤ m) (nrm : F → (Fin p → F) → F)
    (hrel : ∀ (a : Fˣ) (c : Fin p → F) (h : nrm a c ≠ 0), of p a * of p (Units.mk0 _ h) = 0)
    (hzero : ∀ a : F, nrm a 0 = 0)
    (hnd : ∀ a : F, (∀ u : F, u ^ p ≠ a) → ∀ c, nrm a c = 0 → c = 0)
    (hpoly : ∀ a : F, ∃ Φ : MvPolynomial (Fin p) F, Φ.IsHomogeneous p ∧
      ∀ c, MvPolynomial.eval c Φ = nrm a c)
    (hT : ∀ (N : ℕ) (Φ : MvPolynomial (Fin N) F), Φ.IsHomogeneous p → p ^ m < N →
      ∃ v : Fin N → F, v ≠ 0 ∧ MvPolynomial.eval v Φ = 0) :
    ∀ n (l : List (Fˣ × Fˣ)), l.length = n → ∃ l' : List (Fˣ × Fˣ),
      l'.length ≤ p ^ (m - 1) - 1 ∧
      (l.map fun q ↦ of p q.1 * of p q.2).sum = (l'.map fun q ↦ of p q.1 * of p q.2).sum := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hl
    have hK : 1 ≤ p ^ (m - 1) := Nat.one_le_pow _ _ hp.pos
    by_cases hn : n ≤ p ^ (m - 1) - 1
    · exact ⟨l, by omega, rfl⟩
    · set K := p ^ (m - 1)
      have htake : (l.take K).length = K := by rw [List.length_take]; omega
      obtain ⟨l₁, hl₁, he₁⟩ := reduce_one p hp m hm nrm hrel hzero hnd hpoly hT (l.take K) htake
      have hlen : (l₁ ++ l.drop K).length < n := by
        rw [List.length_append, List.length_drop]; omega
      obtain ⟨l', hl', he'⟩ := ih _ hlen (l₁ ++ l.drop K) rfl
      refine ⟨l', hl', ?_⟩
      rw [← he', ← List.take_append_drop K l, List.map_append, List.sum_append, he₁,
        List.take_append_drop, List.map_append, List.sum_append]

theorem list_sum_neg (l : List (Fˣ × Fˣ)) :
    ((l.map fun q ↦ (q.1⁻¹, q.2)).map fun q ↦ of p q.1 * of p q.2).sum +
      (l.map fun q ↦ of p q.1 * of p q.2).sum = 0 := by
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 : of p q.1⁻¹ * of p q.2 + of p q.1 * of p q.2 = 0 := by
      rw [add_comm]; exact of_inv_mul p (of p q.2) q.1
    calc of p q.1⁻¹ * of p q.2 + ((l.map fun q ↦ (q.1⁻¹, q.2)).map fun q ↦ of p q.1 * of p q.2).sum +
          (of p q.1 * of p q.2 + (l.map fun q ↦ of p q.1 * of p q.2).sum)
        = (of p q.1⁻¹ * of p q.2 + of p q.1 * of p q.2) +
          (((l.map fun q ↦ (q.1⁻¹, q.2)).map fun q ↦ of p q.1 * of p q.2).sum +
            (l.map fun q ↦ of p q.1 * of p q.2).sum) := by abel
      _ = 0 := by rw [h1, ih, add_zero]

theorem grade_sum (x : MilnorK F p) (hx : x ∈ MilnorK.grade F p 2) :
    ∃ l : List (Fˣ × Fˣ), x = (l.map fun q ↦ of p q.1 * of p q.2).sum := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨s, rfl⟩ := hy
    exact ⟨[(s 0, s 1)], by simp [MilnorK.symbol, List.ofFn_succ]⟩
  | zero => exact ⟨[], by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨l, rfl⟩ := hy
    obtain ⟨l', rfl⟩ := hz
    exact ⟨l ++ l', by simp⟩
  | neg y _ hy =>
    obtain ⟨l, rfl⟩ := hy
    exact ⟨l.map fun q ↦ (q.1⁻¹, q.2), (eq_neg_of_add_eq_zero_left (list_sum_neg p l)).symm⟩

theorem list_sum_symbol (l : List (Fˣ × Fˣ)) :
    (l.map fun q ↦ of p q.1 * of p q.2).sum =
      ∑ i : Fin l.length, MilnorK.symbol p ![(l.get i).1, (l.get i).2] := by
  rw [← Fin.sum_univ_fun_getElem]
  simp [MilnorK.symbol_pair]

theorem bound_of (hp : p.Prime) (m : ℕ) (hm : 1 ≤ m) (nrm : F → (Fin p → F) → F)
    (hrel : ∀ (a : Fˣ) (c : Fin p → F) (h : nrm a c ≠ 0), of p a * of p (Units.mk0 _ h) = 0)
    (hzero : ∀ a : F, nrm a 0 = 0)
    (hnd : ∀ a : F, (∀ u : F, u ^ p ≠ a) → ∀ c, nrm a c = 0 → c = 0)
    (hpoly : ∀ a : F, ∃ Φ : MvPolynomial (Fin p) F, Φ.IsHomogeneous p ∧
      ∀ c, MvPolynomial.eval c Φ = nrm a c)
    (hT : ∀ (N : ℕ) (Φ : MvPolynomial (Fin N) F), Φ.IsHomogeneous p → p ^ m < N →
      ∃ v : Fin N → F, v ≠ 0 ∧ MvPolynomial.eval v Φ = 0) :
    p ^ (m - 1) - 1 ∈ MilnorK.symbolLengthBounds F p 2 := by
  intro x hx
  obtain ⟨l, rfl⟩ := grade_sum p x hx
  obtain ⟨l', hl', he⟩ := main_bound p hp m hm nrm hrel hzero hnd hpoly hT _ l rfl
  exact ⟨l'.length, hl', fun i ↦ ![(l'.get i).1, (l'.get i).2], by rw [he, list_sum_symbol]⟩

end MatzriR

theorem main : H1 → H2 → OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_R1_H2_R1.H1 := by
  intro hN hTL m hm p hp _
  have hp0 := hp.pos
  exact MatzriR.bound_of p hp m hm
    (fun a c ↦ Algebra.norm (MvRatFunc (Fin m) ℂ)
      (∑ l : Fin p, c l • (AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C a)) ^ (l : ℕ)))
    (fun a c h ↦ hN m p hp a _ h)
    (fun a ↦ MatzriN.norm_zero' p hp0 a)
    (fun a ha c h ↦ MatzriN.norm_eq_zero' p hp a ha c h)
    (fun a ↦ MatzriN.exists_normPoly p hp0 a)
    (fun N Φ hΦ hN' ↦ hTL m p N Φ hp0 hΦ hN')

end OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_R1_H2_R1_H1_R1
