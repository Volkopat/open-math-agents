import OMAStatements.S_arxiv_2607_15305
import Mathlib

namespace OMA.P_arxiv_2607_15305

open OMA.S_arxiv_2607_15305 Polynomial

instance : Fact (Nat.Prime 19) := ⟨by decide⟩

/-- The degree-3 irreducible polynomial `X^3 - 2` over `ZMod 19` defining `𝔽_{19^3}`. -/
noncomputable def Q0 : Polynomial (ZMod 19) := X ^ 3 - C 2

/-- The explicit degree-5 Carlitz–Wieferich prime `X^5 + 13 X^3 + 3 X^2 + 10 X + 15`
over `ZMod 19` (and over `𝔽_{19^3}`). -/
noncomputable def P0 : Polynomial (ZMod 19) :=
  X ^ 5 + C 13 * X ^ 3 + C 3 * X ^ 2 + C 10 * X + C 15

lemma Q0_natDegree : Q0.natDegree = 3 := by
  refine natDegree_eq_of_le_of_coeff_ne_zero (by unfold Q0; compute_degree!) ?_
  simp [Q0, coeff_X_pow]

lemma Q0_monic : Q0.Monic := by
  rw [Monic, leadingCoeff, Q0_natDegree]
  simp [Q0, coeff_X_pow]

lemma P0_natDegree : P0.natDegree = 5 := by
  refine natDegree_eq_of_le_of_coeff_ne_zero (by unfold P0; compute_degree!) ?_
  simp [P0, coeff_X_pow]

lemma P0_monic : P0.Monic := by
  rw [Monic, leadingCoeff, P0_natDegree]
  simp [P0, coeff_X_pow]

lemma Q0_no_root : ∀ x : ZMod 19, Q0.eval x ≠ 0 := by
  have hd : ∀ x : ZMod 19, x ^ 3 - 2 ≠ 0 := by decide
  intro x
  simpa [Q0, eval_sub, eval_pow, eval_X, eval_C] using hd x

lemma P0_no_root : ∀ x : ZMod 19, P0.eval x ≠ 0 := by
  have hd : ∀ x : ZMod 19, x ^ 5 + 13 * x ^ 3 + 3 * x ^ 2 + 10 * x + 15 ≠ 0 := by decide
  intro x
  simpa [P0, eval_add, eval_mul, eval_pow, eval_X, eval_C] using hd x

/-- Any degree-1 polynomial over a field has a root. -/
lemma exists_root_of_natDegree_eq_one {F : Type*} [Field F] {f : Polynomial F}
    (hf : f.natDegree = 1) : ∃ x : F, f.eval x = 0 := by
  have hne : f.leadingCoeff ≠ 0 := by
    intro h0
    rw [leadingCoeff_eq_zero] at h0
    simp [h0] at hf
  have h1 : f.coeff 1 = f.leadingCoeff := by rw [← hf]; rfl
  have heq : f = C (f.coeff 1) * X + C (f.coeff 0) := eq_X_add_C_of_natDegree_le_one (le_of_eq hf)
  set r : F := -(f.coeff 0) / f.leadingCoeff
  refine ⟨r, ?_⟩
  rw [heq]
  simp only [eval_add, eval_mul, eval_X, eval_C]
  rw [h1]
  dsimp [r]
  field_simp [hne]
  ring

lemma Q0_irred : Irreducible Q0 := by
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have := natDegree_eq_zero_of_isUnit hu
    rw [Q0_natDegree] at this; omega
  · have hQne : Q0 ≠ 0 := Q0_monic.ne_zero
    have ha0 : a ≠ 0 := fun h => hQne (by simp [hab, h])
    have hb0 : b ≠ 0 := fun h => hQne (by simp [hab, h])
    have hdeg : a.natDegree + b.natDegree = 3 := by
      rw [← natDegree_mul ha0 hb0, ← hab, Q0_natDegree]
    by_cases ha : a.natDegree = 0
    · left
      have hac : a = C (a.coeff 0) := eq_C_of_natDegree_eq_zero ha
      rw [hac]
      exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (fun h0 => ha0 (by rw [hac, h0, map_zero])))
    · by_cases hb : b.natDegree = 0
      · right
        have hbc : b = C (b.coeff 0) := eq_C_of_natDegree_eq_zero hb
        rw [hbc]
        exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (fun h0 => hb0 (by rw [hbc, h0, map_zero])))
      · exfalso
        have hone : a.natDegree = 1 ∨ b.natDegree = 1 := by omega
        rcases hone with h1 | h1
        · obtain ⟨x, hx⟩ := exists_root_of_natDegree_eq_one h1
          exact Q0_no_root x (by rw [hab, eval_mul, hx, zero_mul])
        · obtain ⟨x, hx⟩ := exists_root_of_natDegree_eq_one h1
          exact Q0_no_root x (by rw [hab, eval_mul, hx, mul_zero])

/-- Symbolic remainder of `P0` divided by a monic quadratic `X^2 + u X + v` over `ZMod 19`. -/
def rem1Quad (u v : ZMod 19) : ZMod 19 :=
  let q2 := -u
  let q1 := 13 + u ^ 2 - v
  let q0 := 3 - u * q1 - v * q2
  10 - u * q0 - v * q1

def rem0Quad (u v : ZMod 19) : ZMod 19 :=
  let q2 := -u
  let q1 := 13 + u ^ 2 - v
  let q0 := 3 - u * q1 - v * q2
  15 - v * q0

lemma P0_no_monic_quad : ∀ u v : ZMod 19, ¬ (rem1Quad u v = 0 ∧ rem0Quad u v = 0) := by decide

lemma P0_no_quad_dvd (a : Polynomial (ZMod 19)) (ha : a.natDegree = 2) (hdvd : a ∣ P0) : False := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hlc : a.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr ha0
  set m := C (a.leadingCoeff⁻¹) * a
  have hm_dvd : m ∣ P0 := by
    obtain ⟨c, hc⟩ := hdvd
    refine ⟨C a.leadingCoeff * c, ?_⟩
    rw [hc]
    calc a * c = (C (a.leadingCoeff⁻¹ * a.leadingCoeff) * a) * c := by
          rw [inv_mul_cancel₀ hlc, map_one, one_mul]
      _ = m * (C a.leadingCoeff * c) := by
          simp only [m, map_mul]; ring
  have hm_deg : m.natDegree = 2 := by
    rw [natDegree_C_mul (inv_ne_zero hlc), ha]
  have hm_monic : m.Monic := by
    rw [Monic, leadingCoeff_mul, leadingCoeff_C, inv_mul_cancel₀ hlc]
  set u := m.coeff 1
  set v := m.coeff 0
  have hm_eq : m = X ^ 2 + C u * X + C v := by
    ext n
    match n with
    | 0 => simp [v, coeff_X, coeff_C]
    | 1 => simp [u]
    | 2 =>
      have h2 : m.coeff 2 = 1 := by
        rw [← hm_deg]; exact hm_monic
      simp [h2]
    | n + 3 =>
      have hgt : m.natDegree < n + 3 := by omega
      rw [coeff_eq_zero_of_natDegree_lt hgt]
      simp [coeff_X_pow]
  set q2 : ZMod 19 := -u
  set q1 : ZMod 19 := 13 + u ^ 2 - v
  set q0 : ZMod 19 := 3 - u * q1 - v * q2
  have hdiv_id :
      P0 = (X ^ 2 + C u * X + C v) * (X ^ 3 + C q2 * X ^ 2 + C q1 * X + C q0) +
        (C (rem1Quad u v) * X + C (rem0Quad u v)) := by
    simp only [P0, rem1Quad, rem0Quad, q2, q1, q0, map_neg, map_add, map_sub, map_mul, map_pow,
      map_ofNat]
    ring
  have hr_dvd : m ∣ (C (rem1Quad u v) * X + C (rem0Quad u v)) := by
    rw [← hm_eq] at hdiv_id
    have h1 : C (rem1Quad u v) * X + C (rem0Quad u v) =
        P0 - m * (X ^ 3 + C q2 * X ^ 2 + C q1 * X + C q0) := by
      rw [hdiv_id]; ring
    rw [h1]
    exact dvd_sub hm_dvd (dvd_mul_right m _)
  have hr_zero : C (rem1Quad u v) * X + C (rem0Quad u v) = 0 := by
    by_contra hne
    have hle := natDegree_le_of_dvd hr_dvd hne
    have hlt : (C (rem1Quad u v) * X + C (rem0Quad u v)).natDegree ≤ 1 := by compute_degree!
    omega
  have hr1 : rem1Quad u v = 0 := by
    have := congrArg (fun p => p.coeff 1) hr_zero
    simpa [coeff_X, coeff_C] using this
  have hr0 : rem0Quad u v = 0 := by
    have := congrArg (fun p => p.coeff 0) hr_zero
    simpa [coeff_X, coeff_C] using this
  exact P0_no_monic_quad u v ⟨hr1, hr0⟩

lemma P0_irred : Irreducible P0 := by
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have := natDegree_eq_zero_of_isUnit hu
    rw [P0_natDegree] at this; omega
  · have hPne : P0 ≠ 0 := P0_monic.ne_zero
    have ha0 : a ≠ 0 := fun h => hPne (by simp [hab, h])
    have hb0 : b ≠ 0 := fun h => hPne (by simp [hab, h])
    have hdeg : a.natDegree + b.natDegree = 5 := by
      rw [← natDegree_mul ha0 hb0, ← hab, P0_natDegree]
    by_cases ha : a.natDegree = 0
    · left
      have hac : a = C (a.coeff 0) := eq_C_of_natDegree_eq_zero ha
      rw [hac]
      exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (fun h0 => ha0 (by rw [hac, h0, map_zero])))
    · by_cases hb : b.natDegree = 0
      · right
        have hbc : b = C (b.coeff 0) := eq_C_of_natDegree_eq_zero hb
        rw [hbc]
        exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (fun h0 => hb0 (by rw [hbc, h0, map_zero])))
      · exfalso
        have hcase : a.natDegree = 1 ∨ b.natDegree = 1 ∨ a.natDegree = 2 ∨ b.natDegree = 2 := by
          omega
        rcases hcase with h1 | h1 | h2 | h2
        · obtain ⟨x, hx⟩ := exists_root_of_natDegree_eq_one h1
          exact P0_no_root x (by rw [hab, eval_mul, hx, zero_mul])
        · obtain ⟨x, hx⟩ := exists_root_of_natDegree_eq_one h1
          exact P0_no_root x (by rw [hab, eval_mul, hx, mul_zero])
        · exact P0_no_quad_dvd a h2 ⟨b, hab⟩
        · exact P0_no_quad_dvd b h2 ⟨a, by rw [mul_comm]; exact hab⟩

/-! ### Field `K = 𝔽_{19^3} = (ZMod 19)[X] / (X^3 - 2)` and irreducibility of `P0` over `K` -/

abbrev K19 := AdjoinRoot Q0

instance : Fact (Irreducible Q0) := ⟨Q0_irred⟩
instance : Fact (Irreducible P0) := ⟨P0_irred⟩

noncomputable instance instFieldK19 : Field K19 := AdjoinRoot.instField

lemma finrank_K19 : Module.finrank (ZMod 19) K19 = 3 := by
  rw [(AdjoinRoot.powerBasis Q0_monic.ne_zero).finrank, AdjoinRoot.powerBasis_dim, Q0_natDegree]

noncomputable instance instFintypeK19 : Fintype K19 := by
  haveI : FiniteDimensional (ZMod 19) K19 :=
    Module.finite_of_finrank_pos (by rw [finrank_K19]; omega)
  haveI : Finite K19 := Module.finite_of_finite (ZMod 19)
  exact Fintype.ofFinite K19

lemma card_K19 : Fintype.card K19 = 6859 := by
  have h := Module.card_eq_pow_finrank (K := ZMod 19) (V := K19)
  rw [ZMod.card, finrank_K19] at h
  simpa using h

lemma charP_K19 : CharP K19 19 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 19) K19).injective 19

noncomputable def P_K : Polynomial K19 := P0.map (algebraMap (ZMod 19) K19)

lemma P_K_monic : P_K.Monic := P0_monic.map _

lemma P_K_natDegree : P_K.natDegree = 5 := by
  rw [P_K, P0_monic.natDegree_map, P0_natDegree]

lemma P_K_irred : Irreducible P_K := by
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have := natDegree_eq_zero_of_isUnit hu
    rw [P_K_natDegree] at this; omega
  · have hPne : P_K ≠ 0 := P_K_monic.ne_zero
    have ha0 : a ≠ 0 := fun h => hPne (by simp [hab, h])
    have hb0 : b ≠ 0 := fun h => hPne (by simp [hab, h])
    have hdeg : a.natDegree + b.natDegree = 5 := by
      rw [← natDegree_mul ha0 hb0, ← hab, P_K_natDegree]
    by_cases ha : a.natDegree = 0
    · left
      have hac : a = C (a.coeff 0) := eq_C_of_natDegree_eq_zero ha
      rw [hac]
      exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (fun h0 => ha0 (by rw [hac, h0, map_zero])))
    · by_cases hb : b.natDegree = 0
      · right
        have hbc : b = C (b.coeff 0) := eq_C_of_natDegree_eq_zero hb
        rw [hbc]
        exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (fun h0 => hb0 (by rw [hbc, h0, map_zero])))
      · exfalso
        have hnotu : ¬ IsUnit a := fun hu => ha (natDegree_eq_zero_of_isUnit hu)
        obtain ⟨R, hRirred, hRdvd_a⟩ := WfDvdMonoid.exists_irreducible_factor hnotu ha0
        have hRdvd_P : R ∣ P_K := dvd_trans hRdvd_a ⟨b, hab⟩
        have hRne : R ≠ 0 := hRirred.ne_zero
        have hRdeg_pos : 1 ≤ R.natDegree := by
          by_contra h0
          have h0' : R.natDegree = 0 := by omega
          apply hRirred.1
          rw [eq_C_of_natDegree_eq_zero h0']
          exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (fun h => hRne (by rw [eq_C_of_natDegree_eq_zero h0', h, map_zero])))
        have hRdeg_le : R.natDegree ≤ 4 := by
          have hle := natDegree_le_of_dvd hRdvd_a ha0
          omega
        -- Build L = K19[X]/(R), with [L : ZMod 19] = 3 * deg R, divisible by 5 = [AdjoinRoot P0 : ZMod 19]
        have : Fact (Irreducible R) := ⟨hRirred⟩
        let L := AdjoinRoot R
        let : Field L := AdjoinRoot.instField
        have hfrKL : Module.finrank K19 L = R.natDegree := by
          rw [(AdjoinRoot.powerBasis hRne).finrank, AdjoinRoot.powerBasis_dim]
        have : FiniteDimensional (ZMod 19) K19 :=
          Module.finite_of_finrank_pos (by rw [finrank_K19]; omega)
        have : FiniteDimensional K19 L :=
          Module.finite_of_finrank_pos (by rw [hfrKL]; omega)
        have hfr19L : Module.finrank (ZMod 19) L = 3 * R.natDegree := by
          rw [← Module.finrank_mul_finrank (ZMod 19) K19 L, finrank_K19, hfrKL]
        -- Root of R in L is a root of P0
        have hroot : Polynomial.eval₂ (algebraMap (ZMod 19) L) (AdjoinRoot.root R) P0 = 0 := by
          have h1 : Polynomial.aeval (AdjoinRoot.root R) P_K = 0 := by
            obtain ⟨c, hc⟩ := hRdvd_P
            rw [hc, map_mul, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul]
          rw [P_K, aeval_map_algebraMap, Polynomial.aeval_def] at h1
          exact h1
        let E := AdjoinRoot P0
        let : Field E := AdjoinRoot.instField
        let φ : E →+* L := AdjoinRoot.lift (algebraMap (ZMod 19) L) (AdjoinRoot.root R) hroot
        let : Algebra E L := φ.toAlgebra
        have : IsScalarTower (ZMod 19) E L :=
          IsScalarTower.of_algebraMap_eq (fun x => (AdjoinRoot.lift_of hroot).symm)
        have hfr19E : Module.finrank (ZMod 19) E = 5 := by
          rw [(AdjoinRoot.powerBasis P0_monic.ne_zero).finrank, AdjoinRoot.powerBasis_dim, P0_natDegree]
        have : FiniteDimensional (ZMod 19) E :=
          Module.finite_of_finrank_pos (by rw [hfr19E]; omega)
        have : FiniteDimensional (ZMod 19) L :=
          Module.finite_of_finrank_pos (by rw [hfr19L]; omega)
        have : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite (ZMod 19) E L
        have hmul5 : 5 * Module.finrank E L = 3 * R.natDegree := by
          rw [← hfr19E, Module.finrank_mul_finrank (ZMod 19) E L, hfr19L]
        omega

/-! ### Fast flat 10-tuple arithmetic modulo `P0^2` over `ZMod 19` -/

structure Vec10 where
  c0 : ZMod 19
  c1 : ZMod 19
  c2 : ZMod 19
  c3 : ZMod 19
  c4 : ZMod 19
  c5 : ZMod 19
  c6 : ZMod 19
  c7 : ZMod 19
  c8 : ZMod 19
  c9 : ZMod 19
  deriving DecidableEq

def zeroV : Vec10 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
def oneV : Vec10 := ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def addV (a b : Vec10) : Vec10 :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3, a.c4 + b.c4,
   a.c5 + b.c5, a.c6 + b.c6, a.c7 + b.c7, a.c8 + b.c8, a.c9 + b.c9⟩

def smulV (k : ZMod 19) (a : Vec10) : Vec10 :=
  ⟨k * a.c0, k * a.c1, k * a.c2, k * a.c3, k * a.c4,
   k * a.c5, k * a.c6, k * a.c7, k * a.c8, k * a.c9⟩

/-- Multiply by `X` modulo `P0^2`, using `X^10 ≡ 3 + 4X + 6X^3 + 16X^4 + 6X^5 + X^6 + 13X^7 + 12X^8`. -/
def mulXV (a : Vec10) : Vec10 :=
  let t := a.c9
  ⟨t * 3, a.c0 + t * 4, a.c1, a.c2 + t * 6, a.c3 + t * 16,
   a.c4 + t * 6, a.c5 + t, a.c6 + t * 13, a.c7 + t * 12, a.c8⟩

/-- Horner multiplication modulo `P0^2` (flat, zero recursion). -/
def mulV (a b : Vec10) : Vec10 :=
  let s9 := smulV b.c9 a
  let s8 := addV (mulXV s9) (smulV b.c8 a)
  let s7 := addV (mulXV s8) (smulV b.c7 a)
  let s6 := addV (mulXV s7) (smulV b.c6 a)
  let s5 := addV (mulXV s6) (smulV b.c5 a)
  let s4 := addV (mulXV s5) (smulV b.c4 a)
  let s3 := addV (mulXV s4) (smulV b.c3 a)
  let s2 := addV (mulXV s3) (smulV b.c2 a)
  let s1 := addV (mulXV s2) (smulV b.c1 a)
  addV (mulXV s1) (smulV b.c0 a)

def pow19Cert (x x2 x4 x8 x16 x18 y : Vec10) : Prop :=
  mulV x x = x2 ∧ mulV x2 x2 = x4 ∧ mulV x4 x4 = x8 ∧
  mulV x8 x8 = x16 ∧ mulV x16 x2 = x18 ∧ mulV x18 x = y

def rv1 : Vec10 := ⟨1, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩

def r1_1 : Vec10 := ⟨14, 18, 13, 11, 1, 17, 7, 13, 12, 3⟩
lemma cert_r1_1 : pow19Cert rv1 ⟨1, 2, 1, 0, 0, 0, 0, 0, 0, 0⟩ ⟨1, 4, 6, 4, 1, 0, 0, 0, 0, 0⟩ ⟨1, 8, 9, 18, 13, 18, 9, 8, 1, 0⟩ ⟨18, 18, 17, 13, 18, 7, 17, 17, 14, 4⟩ ⟨8, 2, 11, 7, 0, 5, 0, 6, 1, 2⟩ r1_1 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
def r1_2 : Vec10 := ⟨0, 1, 7, 14, 12, 13, 11, 8, 14, 5⟩
lemma cert_r1_2 : pow19Cert r1_1 ⟨6, 8, 5, 1, 11, 0, 7, 2, 14, 4⟩ ⟨12, 18, 16, 10, 13, 9, 8, 4, 14, 11⟩ ⟨7, 18, 1, 7, 8, 3, 15, 10, 0, 13⟩ ⟨1, 0, 14, 1, 15, 12, 15, 10, 9, 13⟩ ⟨18, 11, 15, 1, 6, 16, 5, 16, 10, 16⟩ r1_2 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
def r1_3 : Vec10 := ⟨7, 14, 5, 1, 7, 11, 10, 1, 2, 14⟩
lemma cert_r1_3 : pow19Cert r1_2 ⟨1, 2, 10, 7, 3, 10, 4, 17, 11, 18⟩ ⟨6, 10, 5, 8, 15, 13, 6, 15, 4, 11⟩ ⟨14, 3, 11, 14, 0, 17, 9, 3, 7, 15⟩ ⟨17, 15, 3, 3, 2, 16, 3, 18, 12, 10⟩ ⟨3, 7, 0, 16, 7, 4, 1, 16, 13, 0⟩ r1_3 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
def rv2 : Vec10 := ⟨7, 15, 6, 1, 7, 11, 10, 1, 2, 14⟩
lemma step_rv2 : addV (mulXV rv1) r1_3 = rv2 := by decide

def r2_1 : Vec10 := ⟨12, 4, 11, 12, 18, 7, 14, 12, 4, 18⟩
lemma cert_r2_1 : pow19Cert rv2 ⟨16, 0, 14, 0, 17, 12, 17, 6, 10, 8⟩ ⟨11, 8, 13, 14, 15, 17, 13, 10, 18, 8⟩ ⟨6, 11, 4, 4, 4, 12, 8, 12, 5, 0⟩ ⟨2, 5, 1, 10, 10, 4, 1, 14, 9, 9⟩ ⟨5, 7, 7, 11, 2, 9, 1, 5, 3, 0⟩ r2_1 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
def r2_2 : Vec10 := ⟨3, 11, 16, 2, 1, 8, 8, 2, 5, 12⟩
lemma cert_r2_2 : pow19Cert r2_1 ⟨1, 14, 0, 15, 17, 5, 12, 12, 8, 4⟩ ⟨15, 9, 3, 1, 3, 8, 9, 1, 4, 15⟩ ⟨14, 3, 6, 3, 1, 1, 0, 17, 10, 12⟩ ⟨14, 15, 2, 6, 10, 5, 12, 3, 0, 16⟩ ⟨6, 16, 14, 5, 8, 2, 3, 16, 17, 5⟩ r2_2 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
def r2_3 : Vec10 := ⟨3, 6, 0, 6, 2, 8, 6, 7, 10, 16⟩
lemma cert_r2_3 : pow19Cert r2_2 ⟨10, 18, 0, 12, 3, 2, 4, 2, 8, 10⟩ ⟨15, 16, 3, 18, 13, 17, 0, 11, 8, 1⟩ ⟨4, 7, 3, 7, 2, 18, 12, 4, 11, 1⟩ ⟨12, 16, 15, 3, 13, 17, 17, 1, 1, 5⟩ ⟨18, 2, 10, 15, 8, 12, 0, 7, 15, 1⟩ r2_3 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
def rv3 : Vec10 := ⟨7, 12, 15, 1, 18, 4, 12, 9, 8, 18⟩
lemma step_rv3 : addV (mulXV rv2) r2_3 = rv3 := by decide

def r3_1 : Vec10 := ⟨0, 10, 10, 18, 12, 3, 15, 16, 10, 11⟩
lemma cert_r3_1 : pow19Cert rv3 ⟨6, 12, 11, 15, 11, 6, 14, 17, 6, 7⟩ ⟨4, 0, 17, 15, 12, 2, 12, 12, 0, 10⟩ ⟨17, 9, 7, 14, 0, 13, 15, 14, 0, 14⟩ ⟨4, 7, 6, 9, 17, 0, 5, 13, 11, 1⟩ ⟨12, 16, 2, 9, 7, 7, 4, 8, 4, 12⟩ r3_1 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
def r3_2 : Vec10 := ⟨12, 6, 0, 13, 3, 7, 3, 13, 4, 11⟩
lemma cert_r3_2 : pow19Cert r3_1 ⟨9, 16, 13, 14, 9, 14, 12, 6, 8, 10⟩ ⟨16, 11, 3, 12, 10, 2, 1, 4, 15, 5⟩ ⟨11, 4, 0, 0, 0, 2, 7, 17, 11, 12⟩ ⟨11, 11, 6, 17, 3, 3, 8, 6, 1, 7⟩ ⟨8, 10, 7, 2, 5, 4, 4, 4, 9, 11⟩ r3_2 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
def r3_3 : Vec10 := ⟨14, 17, 6, 12, 3, 8, 4, 16, 15, 11⟩
lemma cert_r3_3 : pow19Cert r3_2 ⟨12, 7, 15, 10, 0, 11, 10, 9, 13, 2⟩ ⟨13, 0, 2, 15, 10, 11, 9, 8, 6, 0⟩ ⟨7, 1, 6, 8, 15, 8, 4, 17, 7, 10⟩ ⟨9, 7, 3, 2, 10, 4, 3, 13, 18, 3⟩ ⟨5, 3, 3, 5, 9, 18, 9, 2, 18, 5⟩ r3_3 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
def rv4 : Vec10 := ⟨11, 1, 18, 2, 7, 1, 7, 15, 12, 0⟩
lemma step_rv4 : addV (mulXV rv3) r3_3 = rv4 := by decide

def r4_1 : Vec10 := ⟨13, 5, 0, 0, 14, 3, 16, 0, 9, 5⟩
lemma cert_r4_1 : pow19Cert rv4 ⟨13, 0, 4, 7, 12, 2, 0, 12, 9, 7⟩ ⟨9, 9, 12, 7, 13, 15, 4, 1, 17, 17⟩ ⟨12, 13, 3, 15, 17, 11, 3, 11, 6, 17⟩ ⟨2, 12, 8, 4, 8, 13, 4, 17, 10, 15⟩ ⟨16, 6, 6, 15, 3, 1, 2, 1, 3, 7⟩ r4_1 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
def r4_2 : Vec10 := ⟨0, 12, 17, 9, 4, 3, 10, 4, 1, 2⟩
lemma cert_r4_2 : pow19Cert r4_1 ⟨13, 10, 15, 5, 4, 16, 13, 9, 14, 5⟩ ⟨7, 1, 13, 1, 17, 9, 2, 11, 3, 13⟩ ⟨12, 6, 15, 2, 13, 1, 8, 1, 11, 14⟩ ⟨1, 11, 0, 4, 14, 12, 2, 17, 18, 0⟩ ⟨2, 7, 2, 5, 0, 10, 2, 7, 6, 11⟩ r4_2 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
def r4_3 : Vec10 := ⟨16, 6, 14, 4, 9, 3, 3, 6, 8, 16⟩
lemma cert_r4_3 : pow19Cert r4_2 ⟨0, 17, 10, 14, 2, 11, 14, 7, 13, 16⟩ ⟨8, 4, 5, 5, 9, 8, 5, 6, 5, 3⟩ ⟨0, 10, 12, 17, 16, 2, 11, 4, 8, 15⟩ ⟨9, 9, 9, 10, 15, 4, 9, 6, 4, 15⟩ ⟨9, 1, 12, 2, 11, 4, 16, 12, 9, 12⟩ r4_3 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
def rv5 : Vec10 := ⟨16, 17, 15, 3, 11, 10, 4, 13, 4, 9⟩
lemma step_rv5 : addV (mulXV rv4) r4_3 = rv5 := by decide

def rhoPV : Vec10 :=
  addV (smulV 15 oneV)
    (addV (smulV 10 rv1)
      (addV (smulV 3 rv2)
        (addV (smulV 13 rv3) rv5)))

lemma rhoPV_eq_one : rhoPV = oneV := by decide

noncomputable def toPoly (v : Vec10) : Polynomial (ZMod 19) :=
  C v.c0 + C v.c1 * X + C v.c2 * X ^ 2 + C v.c3 * X ^ 3 + C v.c4 * X ^ 4 +
  C v.c5 * X ^ 5 + C v.c6 * X ^ 6 + C v.c7 * X ^ 7 + C v.c8 * X ^ 8 + C v.c9 * X ^ 9

lemma toPoly_oneV : toPoly oneV = 1 := by
  simp [toPoly, oneV]

lemma toPoly_addV (a b : Vec10) : toPoly (addV a b) = toPoly a + toPoly b := by
  simp only [toPoly, addV, map_add]; ring

lemma toPoly_smulV (c : ZMod 19) (a : Vec10) : toPoly (smulV c a) = C c * toPoly a := by
  simp only [toPoly, smulV, map_mul]; ring

lemma X10_sub_negP2 :
    X ^ 10 - (C 3 + C 4 * X + C 6 * X ^ 3 + C 16 * X ^ 4 + C 6 * X ^ 5 +
      X ^ 6 + C 13 * X ^ 7 + C 12 * X ^ 8) = P0 ^ 2 := by
  have h19 : (19 : Polynomial (ZMod 19)) = 0 := by
    rw [← map_ofNat C 19, show (19 : ZMod 19) = 0 by decide, map_zero]
  have hP : P0 = X ^ 5 + 13 * X ^ 3 + 3 * X ^ 2 + 10 * X + 15 := by
    unfold P0
    rw [map_ofNat C 13, map_ofNat C 3, map_ofNat C 10, map_ofNat C 15]
  rw [hP, map_ofNat C 3, map_ofNat C 4, map_ofNat C 6, map_ofNat C 16,
    map_ofNat C 13, map_ofNat C 12]
  linear_combination
    -(12 + 16 * X + 10 * X ^ 2 + 24 * X ^ 3 + 15 * X ^ 4 + 6 * X ^ 5 + 10 * X ^ 6 + X ^ 7 + 2 * X ^ 8) * h19

lemma mulXV_mod (a : Vec10) : P0 ^ 2 ∣ toPoly (mulXV a) - X * toPoly a := by
  have hid : toPoly (mulXV a) - X * toPoly a =
      -(C a.c9 * (X ^ 10 - (C 3 + C 4 * X + C 6 * X ^ 3 + C 16 * X ^ 4 + C 6 * X ^ 5 +
        X ^ 6 + C 13 * X ^ 7 + C 12 * X ^ 8))) := by
    simp only [toPoly, mulXV, map_add, map_mul]
    ring
  rw [hid, X10_sub_negP2]
  exact ⟨-C a.c9, by ring⟩

lemma dvd_sub_trans {R : Type*} [CommRing R] {m a b c : R}
    (h1 : m ∣ a - b) (h2 : m ∣ b - c) : m ∣ a - c := by
  have : a - c = (a - b) + (b - c) := by ring
  rw [this]; exact dvd_add h1 h2

lemma horner_step (acc a : Vec10) (k : ZMod 19) (target : Polynomial (ZMod 19))
    (h : P0 ^ 2 ∣ toPoly acc - target) :
    P0 ^ 2 ∣ toPoly (addV (mulXV acc) (smulV k a)) - (X * target + C k * toPoly a) := by
  rw [toPoly_addV, toPoly_smulV]
  have h1 : P0 ^ 2 ∣ toPoly (mulXV acc) - X * toPoly acc := mulXV_mod acc
  have h2 : P0 ^ 2 ∣ X * toPoly acc - X * target := by
    rw [← mul_sub]; exact dvd_mul_of_dvd_right h X
  have h12 := dvd_sub_trans h1 h2
  have hid : toPoly (mulXV acc) + C k * toPoly a - (X * target + C k * toPoly a) =
      toPoly (mulXV acc) - X * target := by ring
  rw [hid]; exact h12

lemma mulV_mod (a b : Vec10) : P0 ^ 2 ∣ toPoly (mulV a b) - toPoly a * toPoly b := by
  unfold mulV
  have h9 : P0 ^ 2 ∣ toPoly (smulV b.c9 a) - C b.c9 * toPoly a := by
    rw [toPoly_smulV, sub_self]; exact dvd_zero _
  have h8 := horner_step _ a b.c8 _ h9
  have h7 := horner_step _ a b.c7 _ h8
  have h6 := horner_step _ a b.c6 _ h7
  have h5 := horner_step _ a b.c5 _ h6
  have h4 := horner_step _ a b.c4 _ h5
  have h3 := horner_step _ a b.c3 _ h4
  have h2 := horner_step _ a b.c2 _ h3
  have h1 := horner_step _ a b.c1 _ h2
  have h0 := horner_step _ a b.c0 _ h1
  have hid :
      X * (X * (X * (X * (X * (X * (X * (X * (X * (C b.c9 * toPoly a) + C b.c8 * toPoly a) +
        C b.c7 * toPoly a) + C b.c6 * toPoly a) + C b.c5 * toPoly a) + C b.c4 * toPoly a) +
        C b.c3 * toPoly a) + C b.c2 * toPoly a) + C b.c1 * toPoly a) + C b.c0 * toPoly a =
      toPoly a * toPoly b := by
    simp only [toPoly]; ring
  rwa [hid] at h0

lemma dvd_pow_sub_pow {R : Type*} [CommRing R] {m a b : R} (h : m ∣ a - b) :
    ∀ e : ℕ, m ∣ a ^ e - b ^ e := by
  intro e
  induction e with
  | zero => simp
  | succ e ih =>
    have hid : a ^ (e + 1) - b ^ (e + 1) = (a - b) * a ^ e + b * (a ^ e - b ^ e) := by ring
    rw [hid]
    exact dvd_add (dvd_mul_of_dvd_left h _) (dvd_mul_of_dvd_right ih _)

lemma dvd_mul_sub_mul {R : Type*} [CommRing R] {m a a' b b' : R}
    (ha : m ∣ a - a') (hb : m ∣ b - b') : m ∣ a * b - a' * b' := by
  have hid : a * b - a' * b' = (a - a') * b + a' * (b - b') := by ring
  rw [hid]
  exact dvd_add (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right hb _)

lemma pow19Cert_mod {x x2 x4 x8 x16 x18 y : Vec10} (h : pow19Cert x x2 x4 x8 x16 x18 y) :
    P0 ^ 2 ∣ toPoly y - (toPoly x) ^ 19 := by
  rcases h with ⟨hx2, hx4, hx8, hx16, hx18, hy⟩
  have h2 : P0 ^ 2 ∣ toPoly x2 - (toPoly x) ^ 2 := by
    rw [← hx2]; simpa [pow_two] using mulV_mod x x
  have h4 : P0 ^ 2 ∣ toPoly x4 - (toPoly x) ^ 4 := by
    rw [← hx4]
    have hc := dvd_sub_trans (mulV_mod x2 x2) (dvd_mul_sub_mul h2 h2)
    simpa [show (toPoly x) ^ 2 * (toPoly x) ^ 2 = (toPoly x) ^ 4 by ring] using hc
  have h8 : P0 ^ 2 ∣ toPoly x8 - (toPoly x) ^ 8 := by
    rw [← hx8]
    have hc := dvd_sub_trans (mulV_mod x4 x4) (dvd_mul_sub_mul h4 h4)
    simpa [show (toPoly x) ^ 4 * (toPoly x) ^ 4 = (toPoly x) ^ 8 by ring] using hc
  have h16 : P0 ^ 2 ∣ toPoly x16 - (toPoly x) ^ 16 := by
    rw [← hx16]
    have hc := dvd_sub_trans (mulV_mod x8 x8) (dvd_mul_sub_mul h8 h8)
    simpa [show (toPoly x) ^ 8 * (toPoly x) ^ 8 = (toPoly x) ^ 16 by ring] using hc
  have h18 : P0 ^ 2 ∣ toPoly x18 - (toPoly x) ^ 18 := by
    rw [← hx18]
    have hc := dvd_sub_trans (mulV_mod x16 x2) (dvd_mul_sub_mul h16 h2)
    simpa [show (toPoly x) ^ 16 * (toPoly x) ^ 2 = (toPoly x) ^ 18 by ring] using hc
  rw [← hy]
  have hc := dvd_sub_trans (mulV_mod x18 x)
    (dvd_mul_sub_mul h18 (by rw [sub_self]; exact dvd_zero _ : P0 ^ 2 ∣ toPoly x - toPoly x))
  simpa [show (toPoly x) ^ 18 * toPoly x = (toPoly x) ^ 19 by ring] using hc

lemma powq_mod {a q : ℕ} (hq : q = a * a * a) {x y1 y2 y3 : Vec10}
    (h1 : P0 ^ 2 ∣ toPoly y1 - (toPoly x) ^ a)
    (h2 : P0 ^ 2 ∣ toPoly y2 - (toPoly y1) ^ a)
    (h3 : P0 ^ 2 ∣ toPoly y3 - (toPoly y2) ^ a) :
    P0 ^ 2 ∣ toPoly y3 - (toPoly x) ^ q := by
  have hb := dvd_sub_trans h2 (dvd_pow_sub_pow h1 a)
  have hc := dvd_sub_trans h3 (dvd_pow_sub_pow hb a)
  rw [hq, pow_mul, pow_mul]
  exact hc

lemma carlitz_step_mod {q : ℕ} {x y3 nxt : Vec10} {k : ℕ}
    (hx : P0 ^ 2 ∣ toPoly x - carlitzPow q k 1)
    (hp : P0 ^ 2 ∣ toPoly y3 - (toPoly x) ^ q)
    (hstep : addV (mulXV x) y3 = nxt) :
    P0 ^ 2 ∣ toPoly nxt - carlitzPow q (k + 1) 1 := by
  rw [← hstep, toPoly_addV, carlitzPow]
  have hA := dvd_sub_trans (mulXV_mod x) (by rw [← mul_sub]; exact dvd_mul_of_dvd_right hx X)
  have hB := dvd_sub_trans hp (dvd_pow_sub_pow hx q)
  have hid :
      toPoly (mulXV x) + toPoly y3 - (X * carlitzPow q k 1 + (carlitzPow q k 1) ^ q) =
      (toPoly (mulXV x) - X * carlitzPow q k 1) + (toPoly y3 - (carlitzPow q k 1) ^ q) := by
    ring
  rw [hid]
  exact dvd_add hA hB

lemma P0_wieferich (q : ℕ) (hq : q = 19 * 19 * 19) : P0 ^ 2 ∣ (carlitzEval q P0 1 - 1) := by
  have rv0_mod : P0 ^ 2 ∣ toPoly oneV - carlitzPow q 0 1 := by
    rw [carlitzPow, toPoly_oneV, sub_self]; exact dvd_zero _
  have rv1_mod : P0 ^ 2 ∣ toPoly rv1 - carlitzPow q 1 1 := by
    have h1 : toPoly rv1 = X + 1 := by simp [toPoly, rv1]; ring
    rw [carlitzPow, carlitzPow, one_pow, mul_one, h1, sub_self]
    exact dvd_zero _
  have rv2_mod : P0 ^ 2 ∣ toPoly rv2 - carlitzPow q 2 1 :=
    carlitz_step_mod rv1_mod
      (powq_mod hq (pow19Cert_mod cert_r1_1) (pow19Cert_mod cert_r1_2) (pow19Cert_mod cert_r1_3))
      step_rv2
  have rv3_mod : P0 ^ 2 ∣ toPoly rv3 - carlitzPow q 3 1 :=
    carlitz_step_mod rv2_mod
      (powq_mod hq (pow19Cert_mod cert_r2_1) (pow19Cert_mod cert_r2_2) (pow19Cert_mod cert_r2_3))
      step_rv3
  have rv4_mod : P0 ^ 2 ∣ toPoly rv4 - carlitzPow q 4 1 :=
    carlitz_step_mod rv3_mod
      (powq_mod hq (pow19Cert_mod cert_r3_1) (pow19Cert_mod cert_r3_2) (pow19Cert_mod cert_r3_3))
      step_rv4
  have rv5_mod : P0 ^ 2 ∣ toPoly rv5 - carlitzPow q 5 1 :=
    carlitz_step_mod rv4_mod
      (powq_mod hq (pow19Cert_mod cert_r4_1) (pow19Cert_mod cert_r4_2) (pow19Cert_mod cert_r4_3))
      step_rv5
  have heval : carlitzEval q P0 1 =
      C 15 * carlitzPow q 0 1 + C 10 * carlitzPow q 1 1 +
      C 3 * carlitzPow q 2 1 + C 13 * carlitzPow q 3 1 + carlitzPow q 5 1 := by
    unfold carlitzEval
    rw [P0_natDegree]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have hc0 : P0.coeff 0 = 15 := by simp [P0, coeff_X_pow]
    have hc1 : P0.coeff 1 = 10 := by simp [P0, coeff_X_pow]
    have hc2 : P0.coeff 2 = 3 := by simp [P0, coeff_X_pow]
    have hc3 : P0.coeff 3 = 13 := by simp [P0, coeff_X_pow]
    have hc4 : P0.coeff 4 = 0 := by simp [P0, coeff_X_pow]
    have hc5 : P0.coeff 5 = 1 := by simp [P0, coeff_X_pow]
    rw [hc0, hc1, hc2, hc3, hc4, hc5]
    simp only [map_zero, zero_mul, add_zero, map_one, one_mul]
  have h1 : toPoly rhoPV = 1 := by rw [rhoPV_eq_one, toPoly_oneV]
  have h2 : toPoly rhoPV =
      C 15 * toPoly oneV + C 10 * toPoly rv1 +
      C 3 * toPoly rv2 + C 13 * toPoly rv3 + toPoly rv5 := by
    simp only [rhoPV, toPoly_addV, toPoly_smulV]
    ring
  have hdiff : P0 ^ 2 ∣ toPoly rhoPV - carlitzEval q P0 1 := by
    rw [h2, heval]
    have hid :
        C 15 * toPoly oneV + C 10 * toPoly rv1 + C 3 * toPoly rv2 +
          C 13 * toPoly rv3 + toPoly rv5 -
        (C 15 * carlitzPow q 0 1 + C 10 * carlitzPow q 1 1 + C 3 * carlitzPow q 2 1 +
          C 13 * carlitzPow q 3 1 + carlitzPow q 5 1) =
        C 15 * (toPoly oneV - carlitzPow q 0 1) +
        C 10 * (toPoly rv1 - carlitzPow q 1 1) +
        C 3 * (toPoly rv2 - carlitzPow q 2 1) +
        C 13 * (toPoly rv3 - carlitzPow q 3 1) +
        (toPoly rv5 - carlitzPow q 5 1) := by ring
    rw [hid]
    exact dvd_add (dvd_add (dvd_add (dvd_add
      (dvd_mul_of_dvd_right rv0_mod _)
      (dvd_mul_of_dvd_right rv1_mod _))
      (dvd_mul_of_dvd_right rv2_mod _))
      (dvd_mul_of_dvd_right rv3_mod _))
      rv5_mod
  rw [h1] at hdiff
  obtain ⟨c, hc⟩ := hdiff
  exact ⟨-c, by rw [← neg_sub, hc]; ring⟩

lemma carlitzPow_map {A B : Type*} [Semiring A] [Semiring B] (f : A →+* B) (q : ℕ) :
    ∀ k x, carlitzPow q k (x.map f) = (carlitzPow q k x).map f := by
  intro k
  induction k with
  | zero => intro x; rfl
  | succ k ih =>
    intro x
    simp only [carlitzPow, ih, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X]

lemma carlitzEval_map {A B : Type*} [Semiring A] [Semiring B] (f : A →+* B) (q : ℕ)
    (P x : Polynomial A) (hdeg : (P.map f).natDegree = P.natDegree) :
    carlitzEval q (P.map f) (x.map f) = (carlitzEval q P x).map f := by
  simp only [carlitzEval, hdeg, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    coeff_map, carlitzPow_map]

lemma P_K_wieferich : P_K ^ 2 ∣ (carlitzEval (Fintype.card K19) P_K 1 - 1) := by
  have hq : Fintype.card K19 = 19 * 19 * 19 := card_K19
  obtain ⟨c, hc⟩ := P0_wieferich (Fintype.card K19) hq
  refine ⟨c.map (algebraMap (ZMod 19) K19), ?_⟩
  have h1 : (1 : Polynomial K19) = (1 : Polynomial (ZMod 19)).map (algebraMap (ZMod 19) K19) := by
    simp
  have hev : carlitzEval (Fintype.card K19) P_K 1 =
      (carlitzEval (Fintype.card K19) P0 1).map (algebraMap (ZMod 19) K19) := by
    rw [h1, P_K]
    exact carlitzEval_map (algebraMap (ZMod 19) K19) (Fintype.card K19) P0 1 (P0_monic.natDegree_map _)
  rw [hev, h1, ← Polynomial.map_sub, hc, Polynomial.map_mul, Polynomial.map_pow]
  rfl

end OMA.P_arxiv_2607_15305

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2607_15305.main) := by
  intro h
  have hdvd :=
    h OMA.P_arxiv_2607_15305.K19 19 (by decide) (by decide) OMA.P_arxiv_2607_15305.charP_K19
      OMA.P_arxiv_2607_15305.P_K
      OMA.P_arxiv_2607_15305.P_K_monic
      OMA.P_arxiv_2607_15305.P_K_irred
      OMA.P_arxiv_2607_15305.P_K_wieferich
  rw [OMA.P_arxiv_2607_15305.P_K_natDegree] at hdvd
  norm_num at hdvd
