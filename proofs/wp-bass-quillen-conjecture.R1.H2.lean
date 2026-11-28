import OMAReductions.R_wp_bass_quillen_conjecture_R1
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Tactic.NoncommRing

-- Proof of wp-bass-quillen-conjecture.R1.H2 (Univariate Quillen Patching Theorem)
-- Credit: @tongenspace

/-!
# Univariate Quillen Patching Theorem

Self-contained Lean 4.33.1 proof of `OMA.R_wp_bass_quillen_conjecture_R1.H2` (Quillen 1976,
Theorem 1) following the matrix-splitting formulation of Quillen's patching theorem:

1. `quillen_matrix_lift` and `quillen_matrix_split`: lifting and coprime-splitting of invertible
   polynomial matrices preserving an idempotent `e`.
2. `zariski_glue` / `mat_poly_zariski_glue`: two-open Zariski gluing over coprime elements `f, g`.
3. `matIsoOver_spread_out`: spreading out a matrix isomorphism from `R_m[X]` to `R_f[X]` for some
   `f ∉ m`.
4. `matIsoOver_atPrime_of_free` and `module_equiv_of_matIsoOver`: translating between projective
   `R[X]`-modules and idempotent matrices `E` vs. `E(0)`.
5. `matIsoOver_id_of_local`: assembling the patching ideal and showing it equals `⊤`.
-/

namespace OMA.H2QuillenPatching

open Polynomial Matrix
open scoped TensorProduct

section IdempotentHelpers

variable {α : Type*} [Ring α]

private lemma idem_comm_and_fix {e a : α} (he : e * e = e) (ha : a = 1 - e + e * a * e) :
    e * a = a * e ∧ (1 - e) * a = 1 - e := by
  have h1 : e * a = e * a * e := by
    calc e * a = e * (1 - e + e * a * e) := by conv_lhs => rw [ha]
      _ = e - e * e + (e * e) * a * e := by noncomm_ring
      _ = e * a * e := by rw [he]; abel
  have h2 : a * e = e * a * e := by
    calc a * e = (1 - e + e * a * e) * e := by conv_lhs => rw [ha]
      _ = e - e * e + e * a * (e * e) := by noncomm_ring
      _ = e * a * e := by rw [he]; abel
  have h3 : (1 - e) * a = 1 - e := by
    calc (1 - e) * a = (1 - e) * (1 - e + e * a * e) := by conv_lhs => rw [ha]
      _ = 1 - 2 * e + e * e + (e - e * e) * a * e := by noncomm_ring
      _ = 1 - e := by rw [he]; noncomm_ring
  exact ⟨h1.trans h2.symm, h3⟩

private lemma idem_mul_sub_one {e a b : α} (he : e * e = e)
    (ha : a = 1 - e + e * a * e) (hb : b = 1 - e + e * b * e) :
    e * (a * b - 1) * e = a * b - 1 := by
  obtain ⟨hac, haf⟩ := idem_comm_and_fix he ha
  obtain ⟨hbc, hbf⟩ := idem_comm_and_fix he hb
  have h1 : (1 - e) * (a * b) = 1 - e := by rw [← mul_assoc, haf, hbf]
  have h2 : e * (a * b) = a * b * e := by rw [← mul_assoc, hac, mul_assoc, hbc, ← mul_assoc]
  have h3 : a * b = e * (a * b) + (1 - e) * (a * b) := by noncomm_ring
  rw [h1] at h3
  calc e * (a * b - 1) * e = e * (a * b) * e - e * e := by noncomm_ring
    _ = a * b * e - e := by rw [h2, mul_assoc, he]
    _ = e * (a * b) - e := by rw [← h2]
    _ = a * b - 1 := by
      have h4 : a * b - 1 = e * (a * b) - e := by
        conv_lhs => rw [h3]
        abel
      exact h4.symm

private lemma idem_of_sub_one {e u : α} (he : e * e = e) (hu : e * (u - 1) * e = u - 1) :
    u = 1 - e + e * u * e := by
  calc u = 1 + (u - 1) := by abel
    _ = 1 + e * (u - 1) * e := by rw [hu]
    _ = 1 - e * e + e * u * e := by noncomm_ring
    _ = 1 - e + e * u * e := by rw [he]

private lemma matrix_map_sub_one {α β : Type*} [Ring α] [Ring β] {k : ℕ}
    {f : α → β} (hf1 : f 1 = 1) (hfadd : ∀ x y, f (x + y) = f x + f y)
    (M : Matrix (Fin k) (Fin k) α) : (M - 1).map f = M.map f - 1 := by
  have hf0 : f 0 = 0 := by
    have h := hfadd 0 0; rw [add_zero] at h
    exact add_right_cancel (h.symm.trans (zero_add (f 0)).symm)
  have hfsub : ∀ x y, f (x - y) = f x - f y := fun x y => by
    have h : f (x - y) + f y = f x := by rw [← hfadd, sub_add_cancel]
    exact eq_sub_of_add_eq h
  apply Matrix.ext; intro i j
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, hfsub]
  split_ifs <;> simp [hf0, hf1]

private lemma matrix_map_one_sub {α β : Type*} [Ring α] [Ring β] {k : ℕ}
    {f : α → β} (hf1 : f 1 = 1) (hfadd : ∀ x y, f (x + y) = f x + f y)
    (M : Matrix (Fin k) (Fin k) α) : (1 - M).map f = 1 - M.map f := by
  have hf0 : f 0 = 0 := by
    have h := hfadd 0 0; rw [add_zero] at h
    exact add_right_cancel (h.symm.trans (zero_add (f 0)).symm)
  have hfsub : ∀ x y, f (x - y) = f x - f y := fun x y => by
    have h : f (x - y) + f y = f x := by rw [← hfadd, sub_add_cancel]
    exact eq_sub_of_add_eq h
  apply Matrix.ext; intro i j
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, hfsub]
  split_ifs <;> simp [hf0, hf1]

private lemma matrix_map_mul {R T : Type*} [Semiring R] [Semiring T] {k : ℕ} (f : R →+* T)
    (M N : Matrix (Fin k) (Fin k) R) : (M * N).map f = M.map f * N.map f := by
  apply Matrix.ext; intro i j
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]

private lemma matrix_idem_map {R T : Type*} [Ring R] [Ring T] {k : ℕ}
    {f : R → T} (hf1 : f 1 = 1) (hfadd : ∀ x y, f (x + y) = f x + f y)
    (hfmul : ∀ x y, f (x * y) = f x * f y)
    {e M : Matrix (Fin k) (Fin k) R} (hM : M = 1 - e + e * M * e) :
    M.map f = 1 - e.map f + e.map f * M.map f * e.map f := by
  have hf0 : f 0 = 0 := by
    have h := hfadd 0 0; rw [add_zero] at h
    exact add_right_cancel (h.symm.trans (zero_add (f 0)).symm)
  have hmul : ∀ A B : Matrix (Fin k) (Fin k) R, (A * B).map f = A.map f * B.map f := by
    intro A B; apply Matrix.ext; intro i j
    simp only [Matrix.map_apply, Matrix.mul_apply]
    have hsum : ∀ (s : Finset (Fin k)) (g : Fin k → R),
        f (∑ t ∈ s, g t) = ∑ t ∈ s, f (g t) := by
      intro s g
      classical
      induction s using Finset.induction_on with
      | empty => simp [hf0]
      | insert a s ha ih => simp [Finset.sum_insert ha, hfadd, ih]
    rw [hsum]
    exact Finset.sum_congr rfl fun t _ => hfmul _ _
  have hadd : ∀ A B : Matrix (Fin k) (Fin k) R, (A + B).map f = A.map f + B.map f :=
    fun A B => Matrix.ext fun i j => hfadd _ _
  conv_lhs => rw [hM]
  rw [hadd, matrix_map_one_sub hf1 hfadd, hmul, hmul]

private lemma matrix_smul_mul_left {R : Type*} [CommSemiring R] {k : ℕ} (c : R)
    (M N : Matrix (Fin k) (Fin k) R) : (c • M) * N = c • (M * N) := by
  apply Matrix.ext; intro i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private lemma matrix_mul_smul_right {R : Type*} [CommSemiring R] {k : ℕ} (c : R)
    (M N : Matrix (Fin k) (Fin k) R) : M * (c • N) = c • (M * N) := by
  apply Matrix.ext; intro i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => by ring

private lemma mul_X_cancel {R : Type*} [Semiring R] {p q : Polynomial R}
    (h : Polynomial.X * p = Polynomial.X * q) : p = q := by
  ext d
  have := congrArg (fun r => r.coeff (d + 1)) h
  simpa only [Polynomial.coeff_X_mul] using this

end IdempotentHelpers

section PolyOps

variable {S : Type*} [CommRing S]

/-- `addY : S[X] →+* S[X][Y]` sends `f(X)` to `f(X + Y)`. -/
noncomputable def addY : Polynomial S →+* Polynomial (Polynomial S) :=
  Polynomial.eval₂RingHom (Polynomial.C.comp Polynomial.C) (Polynomial.C Polynomial.X + Polynomial.X)

/-- `scaleY s : S[X][Y] →+* S[X][Y]` sends `f(X, Y)` to `f(X, s * Y)`. -/
noncomputable def scaleY (s : S) : Polynomial (Polynomial S) →+* Polynomial (Polynomial S) :=
  Polynomial.eval₂RingHom Polynomial.C (Polynomial.C (Polynomial.C s) * Polynomial.X)

/-- `evalXY p q : S[X][Y] →+* S[T]` sends `f(X, Y)` to `f(p(T), q(T))`. -/
noncomputable def evalXY (p q : Polynomial S) : Polynomial (Polynomial S) →+* Polynomial S :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom Polynomial.C p) q

private lemma eval0_comp_addY :
    (Polynomial.evalRingHom (0 : Polynomial S)).comp (addY (S := S)) = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro a; simp [addY]
  · simp [addY]

private lemma eval0_comp_C :
    (Polynomial.evalRingHom (0 : Polynomial S)).comp Polynomial.C = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro a; simp
  · simp

private lemma scaleY_C (s : S) (p : Polynomial S) :
    scaleY s (Polynomial.C p) = Polynomial.C p := by
  simp [scaleY]

private lemma scaleY_X (s : S) :
    scaleY s Polynomial.X = Polynomial.C (Polynomial.C s) * Polynomial.X := by
  simp [scaleY]

private lemma scaleY_comp_scaleY (a b : S) :
    (scaleY a).comp (scaleY b) = scaleY (a * b) := by
  apply Polynomial.ringHom_ext
  · intro p
    change scaleY a (scaleY b (Polynomial.C p)) = scaleY (a * b) (Polynomial.C p)
    rw [scaleY_C, scaleY_C, scaleY_C]
  · change scaleY a (scaleY b Polynomial.X) = scaleY (a * b) Polynomial.X
    rw [scaleY_X, map_mul, scaleY_C, scaleY_X, scaleY_X, map_mul, map_mul]
    ring

private lemma coeff_scaleY (s : S) (q : Polynomial (Polynomial S)) (d : ℕ) :
    (scaleY s q).coeff d = (Polynomial.C s) ^ d * q.coeff d := by
  induction q using Polynomial.induction_on' with
  | add p₁ p₂ ih₁ ih₂ =>
    simp [map_add, Polynomial.coeff_add, ih₁, ih₂, mul_add]
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, scaleY_C, scaleY_X, mul_pow,
      ← Polynomial.C_pow, ← mul_assoc, mul_comm (Polynomial.C c), ← Polynomial.C_mul,
      Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.coeff_monomial, Polynomial.coeff_monomial]
    split_ifs with h
    · subst h; rfl
    · simp

private lemma scaleY_zero_of_killed (s : S) (K : ℕ) (q : Polynomial (Polynomial S))
    (h0 : q.coeff 0 = 0) (hk : ∀ d, Polynomial.C (s ^ K) * q.coeff d = 0) :
    scaleY (s ^ K) q = 0 := by
  ext d
  rw [coeff_scaleY, Polynomial.coeff_zero]
  cases d with
  | zero => simp [h0]
  | succ d =>
    rw [pow_succ, mul_assoc, ← Polynomial.C_pow, hk (d + 1), mul_zero]

private lemma map_comp_scaleY {T : Type*} [CommRing T] (φ : S →+* T) (s : S) :
    (Polynomial.mapRingHom (Polynomial.mapRingHom φ)).comp (scaleY s) =
      (scaleY (φ s)).comp (Polynomial.mapRingHom (Polynomial.mapRingHom φ)) := by
  apply Polynomial.ringHom_ext
  · intro p
    change (scaleY s (Polynomial.C p)).map (Polynomial.mapRingHom φ) =
      scaleY (φ s) ((Polynomial.C p).map (Polynomial.mapRingHom φ))
    rw [scaleY_C, Polynomial.map_C, scaleY_C]
  · change (scaleY s Polynomial.X).map (Polynomial.mapRingHom φ) =
      scaleY (φ s) (Polynomial.X.map (Polynomial.mapRingHom φ))
    rw [scaleY_X, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, scaleY_X]
    simp

private lemma evalXY_comp_C (p q : Polynomial S) :
    (evalXY p q).comp Polynomial.C = Polynomial.eval₂RingHom Polynomial.C p := by
  apply Polynomial.ringHom_ext
  · intro a; simp [evalXY]
  · simp [evalXY]

private lemma evalXY_comp_scaleY_addY (s : S) (p q : Polynomial S) :
    (evalXY p q).comp ((scaleY s).comp addY) =
      Polynomial.eval₂RingHom Polynomial.C (p + Polynomial.C s * q) := by
  apply Polynomial.ringHom_ext
  · intro a; simp [evalXY, scaleY, addY]
  · simp [evalXY, scaleY, addY]

private lemma map_comp_evalXY {T : Type*} [CommRing T] (φ : S →+* T) (p q : Polynomial S) :
    (Polynomial.mapRingHom φ).comp (evalXY p q) =
      (evalXY (p.map φ) (q.map φ)).comp (Polynomial.mapRingHom (Polynomial.mapRingHom φ)) := by
  apply Polynomial.ringHom_ext
  · intro r
    induction r using Polynomial.induction_on' with
    | add r₁ r₂ ih₁ ih₂ => simp [evalXY, map_add] at ih₁ ih₂ ⊢; rw [ih₁, ih₂]
    | monomial n c => simp [evalXY]
  · simp [evalXY]

end PolyOps

section ClearDenom

variable {S : Type*} [CommRing S] (s : S)

private lemma away_exists_pow_mul (x : Localization.Away s) :
    ∃ (n : ℕ) (a : S), algebraMap S (Localization.Away s) a =
      algebraMap S (Localization.Away s) (s ^ n) * x := by
  obtain ⟨⟨a, _, ⟨n, rfl⟩⟩, hx⟩ := IsLocalization.surj (Submonoid.powers s) x
  refine ⟨n, a, ?_⟩
  rw [mul_comm]
  exact hx.symm

private lemma poly_away_exists_pow_mul (p : Polynomial (Localization.Away s)) :
    ∃ (n : ℕ) (p₀ : Polynomial S),
      p₀.map (algebraMap S (Localization.Away s)) =
        Polynomial.C (algebraMap S (Localization.Away s) (s ^ n)) * p := by
  classical
  have hcoeff : ∀ d ∈ p.support, ∃ (n : ℕ) (a : S),
      algebraMap S (Localization.Away s) a =
        algebraMap S (Localization.Away s) (s ^ n) * p.coeff d := fun d _ =>
    away_exists_pow_mul s (p.coeff d)
  choose nf af haf using hcoeff
  let N : ℕ := p.support.sup fun d => if h : d ∈ p.support then nf d h else 0
  let p₀ : Polynomial S :=
    ∑ d ∈ p.support.attach,
      Polynomial.monomial d.1 (s ^ (N - nf d.1 d.2) * af d.1 d.2)
  refine ⟨N, p₀, ?_⟩
  ext d
  simp only [p₀, Polynomial.map_sum, Polynomial.finsetSum_coeff, Polynomial.map_monomial,
    Polynomial.coeff_monomial, Polynomial.coeff_C_mul]
  by_cases hd : d ∈ p.support
  · rw [Finset.sum_eq_single ⟨d, hd⟩]
    · simp only [↓reduceIte]
      have hle : nf d hd ≤ N := by
        have h1 := Finset.le_sup (f := fun k => if h : k ∈ p.support then nf k h else 0) hd
        rwa [dif_pos hd] at h1
      rw [map_mul, haf d hd, ← mul_assoc, ← map_mul, ← pow_add, Nat.sub_add_cancel hle]
    · intro b _ hb
      have : b.1 ≠ d := fun h => hb (Subtype.ext h)
      simp [this]
    · intro h; exact False.elim (h (Finset.mem_attach _ _))
  · rw [Finset.sum_eq_zero]
    · have : p.coeff d = 0 := Polynomial.notMem_support_iff.mp hd
      simp [this]
    · intro b _
      have : b.1 ≠ d := fun h => hd (h ▸ b.2)
      simp [this]

private lemma poly2_away_exists_pow_mul (q : Polynomial (Polynomial (Localization.Away s))) :
    ∃ (n : ℕ) (q₀ : Polynomial (Polynomial S)),
      q₀.map (Polynomial.mapRingHom (algebraMap S (Localization.Away s))) =
        Polynomial.C (Polynomial.C (algebraMap S (Localization.Away s) (s ^ n))) * q := by
  classical
  have hcoeff : ∀ d ∈ q.support, ∃ (n : ℕ) (p₀ : Polynomial S),
      p₀.map (algebraMap S (Localization.Away s)) =
        Polynomial.C (algebraMap S (Localization.Away s) (s ^ n)) * q.coeff d := fun d _ =>
    poly_away_exists_pow_mul s (q.coeff d)
  choose nf pf hpf using hcoeff
  let N : ℕ := q.support.sup fun d => if h : d ∈ q.support then nf d h else 0
  let q₀ : Polynomial (Polynomial S) :=
    ∑ d ∈ q.support.attach,
      Polynomial.monomial d.1 (Polynomial.C (s ^ (N - nf d.1 d.2)) * pf d.1 d.2)
  refine ⟨N, q₀, ?_⟩
  apply Polynomial.ext; intro d
  simp only [q₀, Polynomial.map_sum, Polynomial.finsetSum_coeff, Polynomial.map_monomial,
    Polynomial.coeff_monomial, Polynomial.coeff_C_mul]
  by_cases hd : d ∈ q.support
  · rw [Finset.sum_eq_single ⟨d, hd⟩]
    · simp only [↓reduceIte, Polynomial.coe_mapRingHom]
      have hle : nf d hd ≤ N := by
        have h1 := Finset.le_sup (f := fun k => if h : k ∈ q.support then nf k h else 0) hd
        rwa [dif_pos hd] at h1
      rw [Polynomial.map_mul, Polynomial.map_C, hpf d hd, ← mul_assoc, ← Polynomial.C_mul,
        ← map_mul, ← pow_add, Nat.sub_add_cancel hle]
    · intro b _ hb
      have : b.1 ≠ d := fun h => hb (Subtype.ext h)
      simp [this]
    · intro h; exact False.elim (h (Finset.mem_attach _ _))
  · rw [Finset.sum_eq_zero]
    · have : q.coeff d = 0 := Polynomial.notMem_support_iff.mp hd
      simp [this]
    · intro b _
      have : b.1 ≠ d := fun h => hd (h ▸ b.2)
      simp [this]

private lemma mat_poly2_away_exists_pow_mul {k : ℕ}
    (C : Matrix (Fin k) (Fin k) (Polynomial (Polynomial (Localization.Away s)))) :
    ∃ (n : ℕ) (D : Matrix (Fin k) (Fin k) (Polynomial (Polynomial S))),
      D.map (Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap S (Localization.Away s)))) =
        (Polynomial.C (Polynomial.C (algebraMap S (Localization.Away s) (s ^ n)))) • C := by
  classical
  have hentry : ∀ (i j : Fin k), ∃ (n : ℕ) (q₀ : Polynomial (Polynomial S)),
      q₀.map (Polynomial.mapRingHom (algebraMap S (Localization.Away s))) =
        Polynomial.C (Polynomial.C (algebraMap S (Localization.Away s) (s ^ n))) * C i j :=
    fun i j => poly2_away_exists_pow_mul s (C i j)
  choose nf qf hqf using hentry
  let N : ℕ := Finset.univ.sup fun p : Fin k × Fin k => nf p.1 p.2
  let D : Matrix (Fin k) (Fin k) (Polynomial (Polynomial S)) :=
    Matrix.of fun i j => Polynomial.C (Polynomial.C (s ^ (N - nf i j))) * qf i j
  refine ⟨N, D, ?_⟩
  apply Matrix.ext; intro i j
  have hle : nf i j ≤ N := Finset.le_sup (f := fun p : Fin k × Fin k => nf p.1 p.2)
    (Finset.mem_univ (i, j))
  change (Polynomial.C (Polynomial.C (s ^ (N - nf i j))) * qf i j).map
    (Polynomial.mapRingHom (algebraMap S (Localization.Away s))) =
    Polynomial.C (Polynomial.C (algebraMap S (Localization.Away s) (s ^ N))) * C i j
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.coe_mapRingHom, Polynomial.map_C,
    hqf i j, ← mul_assoc, ← Polynomial.C_mul, ← Polynomial.C_mul, ← map_mul, ← pow_add,
    Nat.sub_add_cancel hle]

private lemma poly_away_zero_exists_pow (p : Polynomial S)
    (hp : p.map (algebraMap S (Localization.Away s)) = 0) :
    ∃ K : ℕ, Polynomial.C (s ^ K) * p = 0 := by
  classical
  have hcoeff : ∀ d ∈ p.support, ∃ K : ℕ, s ^ K * p.coeff d = 0 := by
    intro d _
    have h0 : algebraMap S (Localization.Away s) (p.coeff d) = 0 := by
      have := congrArg (fun q => q.coeff d) hp
      simpa using this
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers s)
      (Localization.Away s) (p.coeff d)).mp h0
    exact ⟨n, hn⟩
  choose Kf hKf using hcoeff
  let K : ℕ := p.support.sup fun d => if h : d ∈ p.support then Kf d h else 0
  refine ⟨K, ?_⟩
  ext d
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_zero]
  by_cases hd : d ∈ p.support
  · have hle : Kf d hd ≤ K := by
      have h1 := Finset.le_sup (f := fun m => if h : m ∈ p.support then Kf m h else 0) hd
      rwa [dif_pos hd] at h1
    rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, hKf d hd, mul_zero]
  · rw [Polynomial.notMem_support_iff.mp hd, mul_zero]

private lemma poly2_away_zero_exists_pow (q : Polynomial (Polynomial S))
    (hq : q.map (Polynomial.mapRingHom (algebraMap S (Localization.Away s))) = 0) :
    ∃ K : ℕ, ∀ d, Polynomial.C (s ^ K) * q.coeff d = 0 := by
  classical
  have hcoeff : ∀ d ∈ q.support, ∃ K : ℕ, Polynomial.C (s ^ K) * q.coeff d = 0 := by
    intro d _
    have h0 : (q.coeff d).map (algebraMap S (Localization.Away s)) = 0 := by
      have := congrArg (fun r => r.coeff d) hq
      simpa using this
    exact poly_away_zero_exists_pow s (q.coeff d) h0
  choose Kf hKf using hcoeff
  let K : ℕ := q.support.sup fun d => if h : d ∈ q.support then Kf d h else 0
  refine ⟨K, fun d => ?_⟩
  by_cases hd : d ∈ q.support
  · have hle : Kf d hd ≤ K := by
      have h1 := Finset.le_sup (f := fun m => if h : m ∈ q.support then Kf m h else 0) hd
      rwa [dif_pos hd] at h1
    rw [← Nat.sub_add_cancel hle, pow_add, Polynomial.C_mul, mul_assoc, hKf d hd, mul_zero]
  · rw [Polynomial.notMem_support_iff.mp hd, mul_zero]

/-- Single-matrix denominator-clearing step for `quillen_matrix_lift`:
given `Ψ ∈ Mat_k(S_s[X][Y])` with `Ψ(X, 0) = 1` and `eLXY * (Ψ - 1) * eLXY = Ψ - 1`,
construct `N : ℕ` and `E ∈ Mat_k(S[X][Y])` with `E(X, 0) = 1`, `eXY * (E - 1) * eXY = E - 1`,
and `E.map φ₂ = Ψ.map (scaleY (φ (s ^ N)))`. -/
private lemma lift_one_poly2_matrix {k : ℕ} (e : Matrix (Fin k) (Fin k) S) (he : e * e = e)
    (Ψ : Matrix (Fin k) (Fin k) (Polynomial (Polynomial (Localization.Away s))))
    (hΨ0 : (Ψ - 1).map (Polynomial.evalRingHom 0) = 0)
    (hΨe : let eLXY := e.map (Polynomial.C.comp (Polynomial.C.comp (algebraMap S (Localization.Away s))));
      eLXY * (Ψ - 1) * eLXY = Ψ - 1) :
    ∃ (N : ℕ) (E : Matrix (Fin k) (Fin k) (Polynomial (Polynomial S))),
      E.map (Polynomial.evalRingHom 0) = 1 ∧
      (let eXY := e.map (Polynomial.C.comp Polynomial.C); eXY * (E - 1) * eXY = E - 1) ∧
      E.map (Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap S (Localization.Away s)))) =
        Ψ.map (scaleY (algebraMap S (Localization.Away s) (s ^ N))) := by
  classical
  let φ : S →+* Localization.Away s := algebraMap S (Localization.Away s)
  let φ₂ : Polynomial (Polynomial S) →+* Polynomial (Polynomial (Localization.Away s)) :=
    Polynomial.mapRingHom (Polynomial.mapRingHom φ)
  let eXY : Matrix (Fin k) (Fin k) (Polynomial (Polynomial S)) :=
    e.map (Polynomial.C.comp Polynomial.C)
  let eLXY : Matrix (Fin k) (Fin k) (Polynomial (Polynomial (Localization.Away s))) :=
    e.map (Polynomial.C.comp (Polynomial.C.comp φ))
  have heLXY_eq : eXY.map φ₂ = eLXY := by
    apply Matrix.ext; intro i j; simp [eXY, eLXY, φ₂]
  have heXY_idem : eXY * eXY = eXY := by
    have := congrArg (fun M => M.map (Polynomial.C.comp Polynomial.C)) he
    rwa [matrix_map_mul] at this
  let YL : Polynomial (Polynomial (Localization.Away s)) := Polynomial.X
  let YS : Polynomial (Polynomial S) := Polynomial.X
  let Cmat : Matrix (Fin k) (Fin k) (Polynomial (Polynomial (Localization.Away s))) :=
    Matrix.of fun i j => ((Ψ - 1) i j).divX
  have hΨ_eq : Ψ = 1 + YL • Cmat := by
    apply Matrix.ext; intro i j
    have hc0 : ((Ψ - 1) i j).coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact congrArg (fun M => M i j) hΨ0
    have hdiv := Polynomial.X_mul_divX_add ((Ψ - 1) i j)
    rw [hc0, map_zero, add_zero] at hdiv
    change Ψ i j = (1 : Matrix (Fin k) (Fin k) _) i j + Polynomial.X * ((Ψ - 1) i j).divX
    rw [hdiv, Matrix.sub_apply]
    abel
  have hCmat_e : eLXY * Cmat * eLXY = Cmat := by
    have hX : YL • (eLXY * Cmat * eLXY) = YL • Cmat := by
      have hsmul : YL • (eLXY * Cmat * eLXY) = eLXY * (YL • Cmat) * eLXY := by
        apply Matrix.ext; intro i j
        simp only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => by ring
      have hsub : YL • Cmat = Ψ - 1 := by rw [hΨ_eq]; abel
      rw [hsmul, hsub, hΨe]
    apply Matrix.ext; intro i j
    have hij := congrArg (fun M => M i j) hX
    simp only [Matrix.smul_apply, smul_eq_mul, YL] at hij
    exact mul_X_cancel hij
  obtain ⟨N, D_raw, hD_raw⟩ := mat_poly2_away_exists_pow_mul s Cmat
  let D := eXY * D_raw * eXY
  have hD : D.map φ₂ = (Polynomial.C (Polynomial.C (φ (s ^ N)))) • Cmat := by
    dsimp only [D]
    rw [matrix_map_mul, matrix_map_mul, heLXY_eq, hD_raw]
    have hsmul : eLXY * ((Polynomial.C (Polynomial.C (φ (s ^ N)))) • Cmat) * eLXY =
        (Polynomial.C (Polynomial.C (φ (s ^ N)))) • (eLXY * Cmat * eLXY) := by
      apply Matrix.ext; intro i j
      simp only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => by ring
    rw [hsmul, hCmat_e]
  have hDe : eXY * D * eXY = D := by
    calc eXY * (eXY * D_raw * eXY) * eXY
        = (eXY * eXY) * D_raw * (eXY * eXY) := by simp only [Matrix.mul_assoc]
      _ = eXY * D_raw * eXY := by rw [heXY_idem]
  have hscale_eXY : ∀ t : S, eXY.map (scaleY t) = eXY := fun t => by
    apply Matrix.ext; intro i j; simp [eXY, scaleY_C]
  let E := 1 + YS • D.map (scaleY (s ^ N))
  refine ⟨N, E, ?_, ?_, ?_⟩
  · apply Matrix.ext; intro i j
    simp only [E, YS, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      zero_mul, add_zero]
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  · change eXY * (E - 1) * eXY = E - 1
    have hEsub : E - 1 = YS • D.map (scaleY (s ^ N)) := by dsimp only [E]; abel
    rw [hEsub, matrix_mul_smul_right, matrix_smul_mul_left]
    refine congrArg (YS • ·) ?_
    have := congrArg (fun M => M.map (scaleY (s ^ N))) hDe
    rwa [matrix_map_mul, matrix_map_mul, hscale_eXY] at this
  · apply Matrix.ext; intro i j
    have hEij : E i j = (1 : Matrix (Fin k) (Fin k) (Polynomial (Polynomial S))) i j +
        Polynomial.X * scaleY (s ^ N) (D i j) := rfl
    have hΨij : Ψ i j = (1 : Matrix (Fin k) (Fin k) (Polynomial (Polynomial (Localization.Away s)))) i j +
        Polynomial.X * Cmat i j := by
      simpa [YL, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using congrArg (fun M => M i j) hΨ_eq
    rw [Matrix.map_apply, Matrix.map_apply, hEij, hΨij, map_add, map_add, map_mul, map_mul]
    have h1 : φ₂ ((1 : Matrix (Fin k) (Fin k) (Polynomial (Polynomial S))) i j) =
        scaleY (φ (s ^ N)) ((1 : Matrix (Fin k) (Fin k) _) i j) := by
      by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
    have hX : φ₂ Polynomial.X = Polynomial.X := by simp [φ₂]
    have hX2 : scaleY (φ (s ^ N)) Polynomial.X =
        Polynomial.C (Polynomial.C (φ (s ^ N))) * Polynomial.X := scaleY_X _
    have hcomm := congrArg (fun f => f (D i j)) (map_comp_scaleY φ (s ^ N))
    simp only [RingHom.comp_apply] at hcomm
    change φ₂ (scaleY (s ^ N) (D i j)) = scaleY (φ (s ^ N)) (φ₂ (D i j)) at hcomm
    have hDij : φ₂ (D i j) = Polynomial.C (Polynomial.C (φ (s ^ N))) * Cmat i j := by
      simpa [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] using congrArg (fun M => M i j) hD
    rw [h1, hX, hX2, hcomm, hDij, map_mul, scaleY_C]
    ring

/-- Quillen's core matrix lifting lemma (Quillen 1976, Lemma 1, matrix form). -/
lemma quillen_matrix_lift {k : ℕ} (e : Matrix (Fin k) (Fin k) S) (he : e * e = e)
    (A B : Matrix (Fin k) (Fin k) (Polynomial (Localization.Away s)))
    (hAB : A * B = 1) (hBA : B * A = 1)
    (hAe : let eL := e.map (Polynomial.C.comp (algebraMap S (Localization.Away s)));
      A = 1 - eL + eL * A * eL)
    (hBe : let eL := e.map (Polynomial.C.comp (algebraMap S (Localization.Away s)));
      B = 1 - eL + eL * B * eL) :
    ∃ (m : ℕ) (U V : Matrix (Fin k) (Fin k) (Polynomial (Polynomial S))),
      U * V = 1 ∧ V * U = 1 ∧
      (let eXY := e.map (Polynomial.C.comp Polynomial.C);
        U = 1 - eXY + eXY * U * eXY ∧ V = 1 - eXY + eXY * V * eXY) ∧
      U.map (Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap S (Localization.Away s)))) =
        A.map ((scaleY (algebraMap S (Localization.Away s) (s ^ m))).comp addY) *
          B.map Polynomial.C := by
  classical
  let φ : S →+* Localization.Away s := algebraMap S (Localization.Away s)
  let φ₂ : Polynomial (Polynomial S) →+* Polynomial (Polynomial (Localization.Away s)) :=
    Polynomial.mapRingHom (Polynomial.mapRingHom φ)
  let eL : Matrix (Fin k) (Fin k) (Polynomial (Localization.Away s)) :=
    e.map (Polynomial.C.comp φ)
  let eXY : Matrix (Fin k) (Fin k) (Polynomial (Polynomial S)) :=
    e.map (Polynomial.C.comp Polynomial.C)
  let eLXY : Matrix (Fin k) (Fin k) (Polynomial (Polynomial (Localization.Away s))) :=
    e.map (Polynomial.C.comp (Polynomial.C.comp φ))
  have heXY_idem : eXY * eXY = eXY := by
    have := congrArg (fun M => M.map (Polynomial.C.comp Polynomial.C)) he
    rwa [matrix_map_mul] at this
  have heLXY_idem : eLXY * eLXY = eLXY := by
    have := congrArg (fun M => M.map (Polynomial.C.comp (Polynomial.C.comp φ))) he
    rwa [matrix_map_mul] at this
  have heL_addY : eL.map addY = eLXY := by
    apply Matrix.ext; intro i j; simp [eL, eLXY, addY]
  have heL_C : eL.map Polynomial.C = eLXY := by
    apply Matrix.ext; intro i j; simp [eL, eLXY]
  let Ψ : Matrix (Fin k) (Fin k) (Polynomial (Polynomial (Localization.Away s))) :=
    A.map addY * B.map Polynomial.C
  let Ψ_inv : Matrix (Fin k) (Fin k) (Polynomial (Polynomial (Localization.Away s))) :=
    A.map Polynomial.C * B.map addY
  have hΨ_mul : Ψ * Ψ_inv = 1 := by
    dsimp only [Ψ, Ψ_inv]
    rw [mul_assoc, ← mul_assoc (B.map Polynomial.C), ← matrix_map_mul, hBA]
    have h1 : (1 : Matrix (Fin k) (Fin k) (Polynomial (Localization.Away s))).map Polynomial.C = 1 := by
      apply Matrix.ext; intro i j; simp only [Matrix.map_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [h1, one_mul, ← matrix_map_mul, hAB]
    apply Matrix.ext; intro i j; simp only [Matrix.map_apply, Matrix.one_apply]; split_ifs <;> simp
  have hΨ_inv_mul : Ψ_inv * Ψ = 1 := by
    dsimp only [Ψ, Ψ_inv]
    rw [mul_assoc, ← mul_assoc (B.map addY), ← matrix_map_mul, hBA]
    have h1 : (1 : Matrix (Fin k) (Fin k) (Polynomial (Localization.Away s))).map addY = 1 := by
      apply Matrix.ext; intro i j; simp only [Matrix.map_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [h1, one_mul, ← matrix_map_mul, hAB]
    apply Matrix.ext; intro i j; simp only [Matrix.map_apply, Matrix.one_apply]; split_ifs <;> simp
  have hΨ0 : (Ψ - 1).map (Polynomial.evalRingHom 0) = 0 := by
    rw [matrix_map_sub_one (f := Polynomial.evalRingHom (0 : Polynomial (Localization.Away s)))
      (by simp) (fun _ _ => by simp), matrix_map_mul]
    have h1 : (A.map addY).map (Polynomial.evalRingHom 0) = A := by
      apply Matrix.ext; intro i j
      change ((Polynomial.evalRingHom 0).comp addY) (A i j) = A i j
      rw [eval0_comp_addY]; rfl
    have h2 : (B.map Polynomial.C).map (Polynomial.evalRingHom 0) = B := by
      apply Matrix.ext; intro i j
      change ((Polynomial.evalRingHom 0).comp Polynomial.C) (B i j) = B i j
      rw [eval0_comp_C]; rfl
    rw [h1, h2, hAB, sub_self]
  have hΨinv0 : (Ψ_inv - 1).map (Polynomial.evalRingHom 0) = 0 := by
    rw [matrix_map_sub_one (f := Polynomial.evalRingHom (0 : Polynomial (Localization.Away s)))
      (by simp) (fun _ _ => by simp), matrix_map_mul]
    have h1 : (A.map Polynomial.C).map (Polynomial.evalRingHom 0) = A := by
      apply Matrix.ext; intro i j
      change ((Polynomial.evalRingHom 0).comp Polynomial.C) (A i j) = A i j
      rw [eval0_comp_C]; rfl
    have h2 : (B.map addY).map (Polynomial.evalRingHom 0) = B := by
      apply Matrix.ext; intro i j
      change ((Polynomial.evalRingHom 0).comp addY) (B i j) = B i j
      rw [eval0_comp_addY]; rfl
    rw [h1, h2, hAB, sub_self]
  have hΨe : eLXY * (Ψ - 1) * eLXY = Ψ - 1 := by
    have h1 := matrix_idem_map (f := addY) (by simp) (fun _ _ => by simp) (fun _ _ => by simp) hAe
    rw [heL_addY] at h1
    have h2 := matrix_idem_map (f := Polynomial.C) (by simp) (fun _ _ => by simp) (fun _ _ => by simp) hBe
    rw [heL_C] at h2
    exact idem_mul_sub_one heLXY_idem h1 h2
  have hΨinve : eLXY * (Ψ_inv - 1) * eLXY = Ψ_inv - 1 := by
    have h1 := matrix_idem_map (f := Polynomial.C) (by simp) (fun _ _ => by simp) (fun _ _ => by simp) hAe
    rw [heL_C] at h1
    have h2 := matrix_idem_map (f := addY) (by simp) (fun _ _ => by simp) (fun _ _ => by simp) hBe
    rw [heL_addY] at h2
    exact idem_mul_sub_one heLXY_idem h1 h2
  obtain ⟨N, E₁, hE₁0, hE₁e, hE₁map⟩ := lift_one_poly2_matrix s e he Ψ hΨ0 hΨe
  obtain ⟨N', F₁, hF₁0, hF₁e, hF₁map⟩ := lift_one_poly2_matrix s e he Ψ_inv hΨinv0 hΨinve
  let N₀ := max N N'
  let E := E₁.map (scaleY (s ^ (N₀ - N)))
  let F := F₁.map (scaleY (s ^ (N₀ - N')))
  have hscale_eXY : ∀ t : S, eXY.map (scaleY t) = eXY := fun t => by
    apply Matrix.ext; intro i j; simp [eXY, scaleY_C]
  have hscale_ev0 : ∀ (t : S) (M : Matrix (Fin k) (Fin k) (Polynomial (Polynomial S))),
      M.map (Polynomial.evalRingHom 0) = 1 →
      (M.map (scaleY t)).map (Polynomial.evalRingHom 0) = 1 := by
    intro t M hM
    have hcomp : (Polynomial.evalRingHom (0 : Polynomial S)).comp (scaleY t) =
        Polynomial.evalRingHom 0 := by
      apply Polynomial.ringHom_ext
      · intro p; simp [scaleY]
      · simp [scaleY]
    apply Matrix.ext; intro i j
    have hij := congrArg (fun f => f (M i j)) hcomp
    simp only [RingHom.comp_apply] at hij
    change ((Polynomial.evalRingHom 0) (scaleY t (M i j))) = _
    rw [hij]
    exact congrArg (fun X => X i j) hM
  have hE0 : E.map (Polynomial.evalRingHom 0) = 1 := hscale_ev0 _ E₁ hE₁0
  have hF0 : F.map (Polynomial.evalRingHom 0) = 1 := hscale_ev0 _ F₁ hF₁0
  have hE_map : E.map φ₂ = Ψ.map (scaleY (φ (s ^ N₀))) := by
    apply Matrix.ext; intro i j
    have hcomm := congrArg (fun f => f (E₁ i j)) (map_comp_scaleY φ (s ^ (N₀ - N)))
    simp only [RingHom.comp_apply] at hcomm
    change φ₂ (E i j) = scaleY (φ (s ^ (N₀ - N))) (φ₂ (E₁ i j)) at hcomm
    rw [Matrix.map_apply, hcomm]
    have h1 := congrArg (fun M => M i j) hE₁map
    simp only [Matrix.map_apply] at h1 ⊢
    rw [h1]
    have hcomp := congrArg (fun f => f (Ψ i j))
      (scaleY_comp_scaleY (φ (s ^ (N₀ - N))) (φ (s ^ N)))
    simp only [RingHom.comp_apply] at hcomp
    rw [hcomp, ← map_mul, ← pow_add, Nat.sub_add_cancel (le_max_left N N')]
  have hF_map : F.map φ₂ = Ψ_inv.map (scaleY (φ (s ^ N₀))) := by
    apply Matrix.ext; intro i j
    have hcomm := congrArg (fun f => f (F₁ i j)) (map_comp_scaleY φ (s ^ (N₀ - N')))
    simp only [RingHom.comp_apply] at hcomm
    change φ₂ (F i j) = scaleY (φ (s ^ (N₀ - N'))) (φ₂ (F₁ i j)) at hcomm
    rw [Matrix.map_apply, hcomm]
    have h1 := congrArg (fun M => M i j) hF₁map
    simp only [Matrix.map_apply] at h1 ⊢
    rw [h1]
    have hcomp := congrArg (fun f => f (Ψ_inv i j))
      (scaleY_comp_scaleY (φ (s ^ (N₀ - N'))) (φ (s ^ N')))
    simp only [RingHom.comp_apply] at hcomp
    rw [hcomp, ← map_mul, ← pow_add, Nat.sub_add_cancel (le_max_right N N')]
  have hEF_map : (E * F - 1).map φ₂ = 0 := by
    rw [matrix_map_sub_one (by simp) (fun _ _ => by simp), matrix_map_mul, hE_map, hF_map,
      ← matrix_map_mul, hΨ_mul]
    apply Matrix.ext; intro i j
    simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.one_apply, Matrix.zero_apply]
    split_ifs <;> simp
  have hFE_map : (F * E - 1).map φ₂ = 0 := by
    rw [matrix_map_sub_one (by simp) (fun _ _ => by simp), matrix_map_mul, hE_map, hF_map,
      ← matrix_map_mul, hΨ_inv_mul]
    apply Matrix.ext; intro i j
    simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.one_apply, Matrix.zero_apply]
    split_ifs <;> simp
  have hEF0 : (E * F - 1).map (Polynomial.evalRingHom 0) = 0 := by
    rw [matrix_map_sub_one (by simp) (fun _ _ => by simp), matrix_map_mul, hE0, hF0, mul_one,
      sub_self]
  have hFE0 : (F * E - 1).map (Polynomial.evalRingHom 0) = 0 := by
    rw [matrix_map_sub_one (by simp) (fun _ _ => by simp), matrix_map_mul, hE0, hF0, mul_one,
      sub_self]
  have hkill1 : ∀ (i j : Fin k), ∃ K : ℕ, ∀ d, Polynomial.C (s ^ K) * ((E * F - 1) i j).coeff d = 0 :=
    fun i j => poly2_away_zero_exists_pow s ((E * F - 1) i j) (congrArg (fun M => M i j) hEF_map)
  have hkill2 : ∀ (i j : Fin k), ∃ K : ℕ, ∀ d, Polynomial.C (s ^ K) * ((F * E - 1) i j).coeff d = 0 :=
    fun i j => poly2_away_zero_exists_pow s ((F * E - 1) i j) (congrArg (fun M => M i j) hFE_map)
  choose K1 hK1 using hkill1
  choose K2 hK2 using hkill2
  let K : ℕ := max (Finset.univ.sup fun p : Fin k × Fin k => K1 p.1 p.2)
                   (Finset.univ.sup fun p : Fin k × Fin k => K2 p.1 p.2)
  let U := E.map (scaleY (s ^ K))
  let V := F.map (scaleY (s ^ K))
  have hUV : U * V = 1 := by
    suffices h : U * V - 1 = 0 from sub_eq_zero.mp h
    have hmap : U * V - 1 = (E * F - 1).map (scaleY (s ^ K)) := by
      rw [matrix_map_sub_one (by simp) (fun _ _ => by simp), matrix_map_mul]
    rw [hmap]
    apply Matrix.ext; intro i j
    rw [Matrix.map_apply, Matrix.zero_apply]
    refine scaleY_zero_of_killed s K ((E * F - 1) i j) ?_ ?_
    · rw [Polynomial.coeff_zero_eq_eval_zero]
      exact congrArg (fun M => M i j) hEF0
    · intro d
      have hle : K1 i j ≤ K := le_trans
        (Finset.le_sup (f := fun p : Fin k × Fin k => K1 p.1 p.2) (Finset.mem_univ (i, j)))
        (le_max_left _ _)
      rw [← Nat.sub_add_cancel hle, pow_add, Polynomial.C_mul, mul_assoc, hK1 i j d, mul_zero]
  have hVU : V * U = 1 := by
    suffices h : V * U - 1 = 0 from sub_eq_zero.mp h
    have hmap : V * U - 1 = (F * E - 1).map (scaleY (s ^ K)) := by
      rw [matrix_map_sub_one (by simp) (fun _ _ => by simp), matrix_map_mul]
    rw [hmap]
    apply Matrix.ext; intro i j
    rw [Matrix.map_apply, Matrix.zero_apply]
    refine scaleY_zero_of_killed s K ((F * E - 1) i j) ?_ ?_
    · rw [Polynomial.coeff_zero_eq_eval_zero]
      exact congrArg (fun M => M i j) hFE0
    · intro d
      have hle : K2 i j ≤ K := le_trans
        (Finset.le_sup (f := fun p : Fin k × Fin k => K2 p.1 p.2) (Finset.mem_univ (i, j)))
        (le_max_right _ _)
      rw [← Nat.sub_add_cancel hle, pow_add, Polynomial.C_mul, mul_assoc, hK2 i j d, mul_zero]
  have hUe : U = 1 - eXY + eXY * U * eXY := by
    refine idem_of_sub_one heXY_idem ?_
    have h1 : eXY * (E - 1) * eXY = E - 1 := by
      rw [show E - 1 = (E₁ - 1).map (scaleY (s ^ (N₀ - N))) from
        (matrix_map_sub_one (by simp) (fun _ _ => by simp) _).symm]
      have := congrArg (fun M => M.map (scaleY (s ^ (N₀ - N)))) hE₁e
      rwa [matrix_map_mul, matrix_map_mul, hscale_eXY] at this
    rw [show U - 1 = (E - 1).map (scaleY (s ^ K)) from
      (matrix_map_sub_one (by simp) (fun _ _ => by simp) _).symm]
    have := congrArg (fun M => M.map (scaleY (s ^ K))) h1
    rwa [matrix_map_mul, matrix_map_mul, hscale_eXY] at this
  have hVe : V = 1 - eXY + eXY * V * eXY := by
    refine idem_of_sub_one heXY_idem ?_
    have h1 : eXY * (F - 1) * eXY = F - 1 := by
      rw [show F - 1 = (F₁ - 1).map (scaleY (s ^ (N₀ - N'))) from
        (matrix_map_sub_one (by simp) (fun _ _ => by simp) _).symm]
      have := congrArg (fun M => M.map (scaleY (s ^ (N₀ - N')))) hF₁e
      rwa [matrix_map_mul, matrix_map_mul, hscale_eXY] at this
    rw [show V - 1 = (F - 1).map (scaleY (s ^ K)) from
      (matrix_map_sub_one (by simp) (fun _ _ => by simp) _).symm]
    have := congrArg (fun M => M.map (scaleY (s ^ K))) h1
    rwa [matrix_map_mul, matrix_map_mul, hscale_eXY] at this
  refine ⟨N₀ + K, U, V, hUV, hVU, ⟨hUe, hVe⟩, ?_⟩
  apply Matrix.ext; intro i j
  have hcomm := congrArg (fun f => f (E i j)) (map_comp_scaleY φ (s ^ K))
  simp only [RingHom.comp_apply] at hcomm
  change φ₂ (U i j) = scaleY (φ (s ^ K)) (φ₂ (E i j)) at hcomm
  rw [Matrix.map_apply, hcomm]
  have h1 := congrArg (fun M => M i j) hE_map
  simp only [Matrix.map_apply] at h1
  rw [h1]
  have hcomp := congrArg (fun f => f (Ψ i j)) (scaleY_comp_scaleY (φ (s ^ K)) (φ (s ^ N₀)))
  simp only [RingHom.comp_apply] at hcomp
  rw [hcomp, ← map_mul, ← pow_add, add_comm K N₀]
  have hmul : Ψ.map (scaleY (φ (s ^ (N₀ + K)))) =
      A.map ((scaleY (φ (s ^ (N₀ + K)))).comp addY) * B.map Polynomial.C := by
    dsimp only [Ψ]
    rw [matrix_map_mul]
    congr 1
    apply Matrix.ext; intro a b; simp [scaleY_C]
  exact congrArg (fun M => M i j) hmul

end ClearDenom

section MatrixSplit

variable {R : Type*} [CommRing R]

/-- Canonical ring isomorphism `(R_f)_g ≃+* R_{fg}` compatible with `awayToAwayRight f g`. -/
private noncomputable def awayAwayEquivRight (f g : R) :
    Localization.Away (algebraMap R (Localization.Away f) g) ≃+* Localization.Away (f * g) := by
  let Rf := Localization.Away f
  let Rfg := Localization.Away (f * g)
  let ι : Rf →+* Rfg := IsLocalization.Away.awayToAwayRight f g
  letI : Algebra Rf Rfg := ι.toAlgebra
  have hloc : IsLocalization.Away (algebraMap R Rf g) Rfg := by
    refine IsLocalization.Away.mk (algebraMap R Rf g) ?_ ?_ ?_
    · change IsUnit (ι (algebraMap R Rf g))
      dsimp only [ι]
      rw [IsLocalization.Away.awayToAwayRight_eq]
      exact IsLocalization.Away.isUnit_of_dvd (f * g) (dvd_mul_left g f)
    · intro z
      obtain ⟨n, a, hz⟩ := IsLocalization.Away.surj (f * g) z
      let invf : Rf := IsLocalization.Away.invSelf (S := Rf) f
      refine ⟨n, algebraMap R Rf a * invf ^ n, ?_⟩
      change z * (ι (algebraMap R Rf g)) ^ n = ι (algebraMap R Rf a * invf ^ n)
      rw [show ι (algebraMap R Rf g) = algebraMap R Rfg g from IsLocalization.Away.awayToAwayRight_eq f g g,
        map_mul, map_pow,
        show ι (algebraMap R Rf a) = algebraMap R Rfg a from IsLocalization.Away.awayToAwayRight_eq f g a]
      have hfu : IsUnit (algebraMap R Rfg f) :=
        IsLocalization.Away.isUnit_of_dvd (f * g) (dvd_mul_right f g)
      have hinv : algebraMap R Rfg f * ι invf = 1 := by
        rw [← IsLocalization.Away.awayToAwayRight_eq (S := Rf) (P := Rfg) f g f]
        change ι (algebraMap R Rf f) * ι invf = 1
        rw [← map_mul, IsLocalization.Away.mul_invSelf (S := Rf) f, map_one]
      apply (hfu.pow n).mul_right_injective
      change (algebraMap R Rfg f) ^ n * (z * (algebraMap R Rfg g) ^ n) =
        (algebraMap R Rfg f) ^ n * (algebraMap R Rfg a * (ι invf) ^ n)
      calc (algebraMap R Rfg f) ^ n * (z * (algebraMap R Rfg g) ^ n)
          = z * ((algebraMap R Rfg f) * (algebraMap R Rfg g)) ^ n := by rw [mul_pow]; ring
        _ = z * (algebraMap R Rfg (f * g)) ^ n := by rw [map_mul]
        _ = algebraMap R Rfg a := hz
        _ = algebraMap R Rfg a * (algebraMap R Rfg f * ι invf) ^ n := by
            rw [hinv, one_pow, mul_one]
        _ = (algebraMap R Rfg f) ^ n * (algebraMap R Rfg a * (ι invf) ^ n) := by
            rw [mul_pow]; ring
    · intro x y hxy
      change ι x = ι y at hxy
      obtain ⟨nx, ax, hax⟩ := IsLocalization.Away.surj f x
      obtain ⟨ny, ay, hay⟩ := IsLocalization.Away.surj f y
      have hfg_eq : algebraMap R Rfg (ax * f ^ ny) = algebraMap R Rfg (ay * f ^ nx) := by
        simp only [map_mul, map_pow]
        have hx' : ι x * (algebraMap R Rfg f) ^ nx = algebraMap R Rfg ax := by
          have := congrArg ι hax
          simpa only [ι, map_mul, map_pow, IsLocalization.Away.awayToAwayRight_eq] using this
        have hy' : ι y * (algebraMap R Rfg f) ^ ny = algebraMap R Rfg ay := by
          have := congrArg ι hay
          simpa only [ι, map_mul, map_pow, IsLocalization.Away.awayToAwayRight_eq] using this
        rw [← hx', ← hy', hxy]
        ring
      obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq (f * g) hfg_eq
      refine ⟨m, ?_⟩
      have hf_unit : IsUnit (algebraMap R Rf f) := IsLocalization.Away.algebraMap_isUnit f
      apply (hf_unit.pow (m + nx + ny)).mul_left_injective
      change ((algebraMap R Rf g) ^ m * x) * (algebraMap R Rf f) ^ (m + nx + ny) =
        ((algebraMap R Rf g) ^ m * y) * (algebraMap R Rf f) ^ (m + nx + ny)
      have hm' := congrArg (algebraMap R Rf) hm
      simp only [map_mul, map_pow, mul_pow] at hm'
      have hx2 : algebraMap R Rf ax = x * (algebraMap R Rf f) ^ nx := hax.symm
      have hy2 : algebraMap R Rf ay = y * (algebraMap R Rf f) ^ ny := hay.symm
      rw [hx2, hy2] at hm'
      calc (algebraMap R Rf g) ^ m * x * (algebraMap R Rf f) ^ (m + nx + ny)
          = (algebraMap R Rf f) ^ m * (algebraMap R Rf g) ^ m *
              (x * (algebraMap R Rf f) ^ nx * (algebraMap R Rf f) ^ ny) := by
            rw [pow_add, pow_add]; ring
        _ = (algebraMap R Rf f) ^ m * (algebraMap R Rf g) ^ m *
              (y * (algebraMap R Rf f) ^ ny * (algebraMap R Rf f) ^ nx) := hm'
        _ = (algebraMap R Rf g) ^ m * y * (algebraMap R Rf f) ^ (m + nx + ny) := by
            rw [pow_add, pow_add]; ring
  exact (IsLocalization.algEquiv (Submonoid.powers (algebraMap R Rf g))
    (Localization.Away (algebraMap R Rf g)) Rfg).toRingEquiv

private lemma awayAwayEquivRight_algebraMap (f g : R) (x : Localization.Away f) :
    awayAwayEquivRight f g (algebraMap (Localization.Away f) _ x) =
      IsLocalization.Away.awayToAwayRight f g x := by
  let _ : Algebra (Localization.Away f) (Localization.Away (f * g)) :=
    (IsLocalization.Away.awayToAwayRight f g).toAlgebra
  dsimp only [awayAwayEquivRight]
  exact AlgEquiv.commutes _ x

/-- Canonical ring isomorphism `(R_g)_f ≃+* R_{fg}` compatible with `awayToAwayLeft g f`. -/
private noncomputable def awayAwayEquivLeft (f g : R) :
    Localization.Away (algebraMap R (Localization.Away g) f) ≃+* Localization.Away (f * g) := by
  have hassoc : Associated (g * f) (f * g) := by rw [mul_comm]
  letI : IsLocalization.Away (g * f) (Localization.Away (f * g)) :=
    IsLocalization.Away.of_associated hassoc.symm
  let e1 : Localization.Away (algebraMap R (Localization.Away g) f) ≃+* Localization.Away (g * f) :=
    awayAwayEquivRight g f
  let e2 : Localization.Away (g * f) ≃+* Localization.Away (f * g) :=
    (IsLocalization.algEquiv (Submonoid.powers (g * f))
      (Localization.Away (g * f)) (Localization.Away (f * g))).toRingEquiv
  exact e1.trans e2

private lemma awayAwayEquivLeft_algebraMap (f g : R) (x : Localization.Away g) :
    awayAwayEquivLeft f g (algebraMap (Localization.Away g) _ x) =
      IsLocalization.Away.awayToAwayLeft g f x := by
  have hassoc : Associated (g * f) (f * g) := by rw [mul_comm]
  let _ : IsLocalization.Away (g * f) (Localization.Away (f * g)) :=
    IsLocalization.Away.of_associated hassoc.symm
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g x
  have hgu : IsUnit (algebraMap R (Localization.Away (f * g)) g) :=
    IsLocalization.Away.isUnit_of_dvd (f * g) (dvd_mul_left g f)
  apply (hgu.pow n).mul_left_injective
  change awayAwayEquivLeft f g (algebraMap (Localization.Away g) _ x) *
      (algebraMap R (Localization.Away (f * g)) g) ^ n =
    IsLocalization.Away.awayToAwayLeft g f x * (algebraMap R (Localization.Away (f * g)) g) ^ n
  have h1 : ∀ y : R, awayAwayEquivLeft f g
      (algebraMap (Localization.Away g) _ (algebraMap R (Localization.Away g) y)) =
      algebraMap R (Localization.Away (f * g)) y := by
    intro y
    change (IsLocalization.algEquiv (Submonoid.powers (g * f))
      (Localization.Away (g * f)) (Localization.Away (f * g)))
      (awayAwayEquivRight g f (algebraMap (Localization.Away g) _ (algebraMap R _ y))) = _
    rw [awayAwayEquivRight_algebraMap, IsLocalization.Away.awayToAwayRight_eq]
    exact AlgEquiv.commutes _ y
  have hlhs : awayAwayEquivLeft f g (algebraMap (Localization.Away g) _ x) *
      (algebraMap R (Localization.Away (f * g)) g) ^ n =
      algebraMap R (Localization.Away (f * g)) a := by
    rw [← h1 g, ← map_pow, ← map_mul, ← map_pow, ← map_mul, ha, h1 a]
  have hrhs : IsLocalization.Away.awayToAwayLeft g f x *
      (algebraMap R (Localization.Away (f * g)) g) ^ n =
      algebraMap R (Localization.Away (f * g)) a := by
    have := congrArg (IsLocalization.Away.awayToAwayLeft g f (S := Localization.Away g)
      (P := Localization.Away (f * g))) ha
    simpa only [map_mul, map_pow, IsLocalization.Away.awayToAwayLeft_eq] using this
  exact hlhs.trans hrhs.symm

/-- Shared helper for `quillen_matrix_split`: transport `A, B` over `Rfg[X]` across an isomorphism
`(R_s)_t ≃+* Rfg` and apply `quillen_matrix_lift`. -/
private lemma quillen_lift_transport {k : ℕ} (e : Matrix (Fin k) (Fin k) R) (he : e * e = e)
    (s t : R) {Rfg : Type*} [CommRing Rfg] [Algebra R Rfg]
    (ι : Localization.Away s →+* Rfg)
    (hι : ∀ r : R, ι (algebraMap R (Localization.Away s) r) = algebraMap R Rfg r)
    (eqv : Localization.Away (algebraMap R (Localization.Away s) t) ≃+* Rfg)
    (heqv : ∀ x : Localization.Away s, eqv (algebraMap (Localization.Away s) _ x) = ι x)
    (A B : Matrix (Fin k) (Fin k) (Polynomial Rfg))
    (hAB : A * B = 1) (hBA : B * A = 1)
    (hAe : let efg := e.map (Polynomial.C.comp (algebraMap R Rfg)); A = 1 - efg + efg * A * efg)
    (hBe : let efg := e.map (Polynomial.C.comp (algebraMap R Rfg)); B = 1 - efg + efg * B * efg) :
    ∃ (m : ℕ) (U V : Matrix (Fin k) (Fin k) (Polynomial (Polynomial (Localization.Away s)))),
      U * V = 1 ∧ V * U = 1 ∧
      (let eXY := (e.map (algebraMap R (Localization.Away s))).map (Polynomial.C.comp Polynomial.C);
        U = 1 - eXY + eXY * U * eXY ∧ V = 1 - eXY + eXY * V * eXY) ∧
      U.map (Polynomial.mapRingHom (Polynomial.mapRingHom ι)) =
        A.map ((scaleY (algebraMap R Rfg (t ^ m))).comp addY) * B.map Polynomial.C := by
  let Rs := Localization.Away s
  let ts : Rs := algebraMap R Rs t
  let es0 : Matrix (Fin k) (Fin k) Rs := e.map (algebraMap R Rs)
  have hes0 : es0 * es0 = es0 := by
    have := congrArg (fun M => M.map (algebraMap R Rs)) he
    rwa [matrix_map_mul] at this
  let As := A.map (Polynomial.mapRingHom eqv.symm.toRingHom)
  let Bs := B.map (Polynomial.mapRingHom eqv.symm.toRingHom)
  have hAsBs : As * Bs = 1 := by
    rw [← matrix_map_mul, hAB]
    apply Matrix.ext; intro i j; simp only [Matrix.map_apply, Matrix.one_apply]; split_ifs <;> simp
  have hBsAs : Bs * As = 1 := by
    rw [← matrix_map_mul, hBA]
    apply Matrix.ext; intro i j; simp only [Matrix.map_apply, Matrix.one_apply]; split_ifs <;> simp
  have heqv_e : (e.map (Polynomial.C.comp (algebraMap R Rfg))).map
      (Polynomial.mapRingHom eqv.symm.toRingHom) =
      es0.map (Polynomial.C.comp (algebraMap Rs (Localization.Away ts))) := by
    apply Matrix.ext; intro i j
    simp only [es0, Matrix.map_apply, RingHom.comp_apply, Polynomial.coe_mapRingHom,
      Polynomial.map_C]
    congr 1
    apply eqv.injective
    change eqv (eqv.symm (algebraMap R Rfg (e i j))) = eqv (algebraMap Rs (Localization.Away ts) (algebraMap R Rs (e i j)))
    rw [RingEquiv.apply_symm_apply, heqv, hι]
  have hAse : let eL := es0.map (Polynomial.C.comp (algebraMap Rs (Localization.Away ts)));
      As = 1 - eL + eL * As * eL := by
    have h1 := matrix_idem_map (f := Polynomial.mapRingHom eqv.symm.toRingHom)
      (by simp) (fun _ _ => by simp) (fun _ _ => by simp) hAe
    rwa [heqv_e] at h1
  have hBse : let eL := es0.map (Polynomial.C.comp (algebraMap Rs (Localization.Away ts)));
      Bs = 1 - eL + eL * Bs * eL := by
    have h1 := matrix_idem_map (f := Polynomial.mapRingHom eqv.symm.toRingHom)
      (by simp) (fun _ _ => by simp) (fun _ _ => by simp) hBe
    rwa [heqv_e] at h1
  obtain ⟨m, U, V, hUV, hVU, ⟨hUe, hVe⟩, hUmap⟩ :=
    quillen_matrix_lift ts es0 hes0 As Bs hAsBs hBsAs hAse hBse
  refine ⟨m, U, V, hUV, hVU, ⟨hUe, hVe⟩, ?_⟩
  have hι_eq : ι = eqv.toRingHom.comp (algebraMap Rs (Localization.Away ts)) := by
    ext x; exact (heqv x).symm
  have hU_R := congrArg (fun M => M.map (Polynomial.mapRingHom (Polynomial.mapRingHom eqv.toRingHom))) hUmap
  have hcomp_map : (Polynomial.mapRingHom (Polynomial.mapRingHom eqv.toRingHom)).comp
      (Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap Rs (Localization.Away ts)))) =
      Polynomial.mapRingHom (Polynomial.mapRingHom ι) := by
    apply Polynomial.ringHom_ext
    · intro p
      change Polynomial.map (Polynomial.mapRingHom eqv.toRingHom)
        (Polynomial.map (Polynomial.mapRingHom (algebraMap Rs (Localization.Away ts))) (Polynomial.C p)) =
        Polynomial.map (Polynomial.mapRingHom ι) (Polynomial.C p)
      simp only [Polynomial.map_C, Polynomial.coe_mapRingHom, Polynomial.map_map]
      congr 1
      ext d
      simp only [Polynomial.coeff_map, RingHom.comp_apply]
      exact heqv (p.coeff d)
    · simp
  have hlhs : (U.map (Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap Rs (Localization.Away ts))))).map
      (Polynomial.mapRingHom (Polynomial.mapRingHom eqv.toRingHom)) =
      U.map (Polynomial.mapRingHom (Polynomial.mapRingHom ι)) := by
    apply Matrix.ext; intro i j
    exact congrArg (fun h => h (U i j)) hcomp_map
  rw [hlhs, matrix_map_mul] at hU_R
  rw [hU_R]
  congr 1
  · apply Matrix.ext; intro i j
    have hcomm := congrArg (fun h => h (addY (As i j)))
      (map_comp_scaleY eqv.toRingHom (algebraMap Rs (Localization.Away ts) (ts ^ m)))
    simp only [RingHom.comp_apply] at hcomm
    change (Polynomial.mapRingHom (Polynomial.mapRingHom eqv.toRingHom))
      (scaleY (algebraMap Rs (Localization.Away ts) (ts ^ m)) (addY (As i j))) = _
    rw [hcomm]
    have ht_eq : eqv.toRingHom (algebraMap Rs (Localization.Away ts) (ts ^ m)) =
        algebraMap R Rfg (t ^ m) := by
      change eqv (algebraMap Rs (Localization.Away ts) (ts ^ m)) = _
      rw [heqv, map_pow, hι, ← map_pow]
    rw [ht_eq]
    have haddY : (Polynomial.mapRingHom (Polynomial.mapRingHom eqv.toRingHom)).comp
        (addY.comp (Polynomial.mapRingHom eqv.symm.toRingHom)) = addY := by
      apply Polynomial.ringHom_ext
      · intro c; simp [addY]
      · simp [addY]
    exact congrArg (scaleY (algebraMap R Rfg (t ^ m))) (congrArg (fun h => h (A i j)) haddY)
  · apply Matrix.ext; intro i j
    have hC : (Polynomial.mapRingHom (Polynomial.mapRingHom eqv.toRingHom)).comp
        (Polynomial.C.comp (Polynomial.mapRingHom eqv.symm.toRingHom)) = Polynomial.C := by
      apply Polynomial.ringHom_ext
      · intro c; simp
      · simp
    exact congrArg (fun h => h (B i j)) hC

/-- Quillen's matrix splitting theorem over a coprime cover `D(f) ∪ D(g) = Spec R`. -/
lemma quillen_matrix_split {f g : R} (hcop : IsCoprime f g) {k : ℕ}
    (e : Matrix (Fin k) (Fin k) R) (he : e * e = e)
    (A B : Matrix (Fin k) (Fin k) (Polynomial (Localization.Away (f * g))))
    (hAB : A * B = 1) (hBA : B * A = 1)
    (hA0 : A.map (Polynomial.evalRingHom 0) = 1)
    (hAe : let efg := e.map (Polynomial.C.comp (algebraMap R (Localization.Away (f * g))));
      A = 1 - efg + efg * A * efg)
    (hBe : let efg := e.map (Polynomial.C.comp (algebraMap R (Localization.Away (f * g))));
      B = 1 - efg + efg * B * efg) :
    ∃ (A₁ B₁ : Matrix (Fin k) (Fin k) (Polynomial (Localization.Away f)))
      (A₂ B₂ : Matrix (Fin k) (Fin k) (Polynomial (Localization.Away g))),
      A₁ * B₁ = 1 ∧ B₁ * A₁ = 1 ∧
      A₂ * B₂ = 1 ∧ B₂ * A₂ = 1 ∧
      (let ef := e.map (Polynomial.C.comp (algebraMap R (Localization.Away f)));
        A₁ = 1 - ef + ef * A₁ * ef ∧ B₁ = 1 - ef + ef * B₁ * ef) ∧
      (let eg := e.map (Polynomial.C.comp (algebraMap R (Localization.Away g)));
        A₂ = 1 - eg + eg * A₂ * eg ∧ B₂ = 1 - eg + eg * B₂ * eg) ∧
      A₁.map (Polynomial.mapRingHom (IsLocalization.Away.awayToAwayRight f g)) *
        A₂.map (Polynomial.mapRingHom (IsLocalization.Away.awayToAwayLeft g f)) = A := by
  let Rf := Localization.Away f
  let Rg := Localization.Away g
  let Rfg := Localization.Away (f * g)
  let ιf : Rf →+* Rfg := IsLocalization.Away.awayToAwayRight f g
  let ιg : Rg →+* Rfg := IsLocalization.Away.awayToAwayLeft g f
  obtain ⟨m₁, U₁, V₁, hU₁V₁, hV₁U₁, ⟨hU₁e, hV₁e⟩, hU₁_fg⟩ :=
    quillen_lift_transport e he f g ιf (IsLocalization.Away.awayToAwayRight_eq f g)
      (awayAwayEquivRight f g) (awayAwayEquivRight_algebraMap f g) A B hAB hBA hAe hBe
  obtain ⟨m₂, U₂, V₂, hU₂V₂, hV₂U₂, ⟨hU₂e, hV₂e⟩, hU₂_fg⟩ :=
    quillen_lift_transport e he g f ιg (IsLocalization.Away.awayToAwayLeft_eq g f)
      (awayAwayEquivLeft f g) (awayAwayEquivLeft_algebraMap f g) A B hAB hBA hAe hBe
  obtain ⟨a, b, hab⟩ := hcop.pow (m := m₂) (n := m₁)
  let p₁ : Polynomial Rf := Polynomial.C (algebraMap R Rf (a * f ^ m₂)) * Polynomial.X
  let q₁ : Polynomial Rf := Polynomial.C (algebraMap R Rf b) * Polynomial.X
  let ev₁ : Polynomial (Polynomial Rf) →+* Polynomial Rf := evalXY p₁ q₁
  let p₂ : Polynomial Rg := 0
  let q₂ : Polynomial Rg := Polynomial.C (algebraMap R Rg a) * Polynomial.X
  let ev₂ : Polynomial (Polynomial Rg) →+* Polynomial Rg := evalXY p₂ q₂
  let A₁ := U₁.map ev₁
  let B₁ := V₁.map ev₁
  let A₂ := U₂.map ev₂
  let B₂ := V₂.map ev₂
  have hA₁B₁ : A₁ * B₁ = 1 := by
    rw [← matrix_map_mul, hU₁V₁]
    apply Matrix.ext; intro i j; simp only [Matrix.map_apply, Matrix.one_apply]; split_ifs <;> simp
  have hB₁A₁ : B₁ * A₁ = 1 := by
    rw [← matrix_map_mul, hV₁U₁]
    apply Matrix.ext; intro i j; simp only [Matrix.map_apply, Matrix.one_apply]; split_ifs <;> simp
  have hA₂B₂ : A₂ * B₂ = 1 := by
    rw [← matrix_map_mul, hU₂V₂]
    apply Matrix.ext; intro i j; simp only [Matrix.map_apply, Matrix.one_apply]; split_ifs <;> simp
  have hB₂A₂ : B₂ * A₂ = 1 := by
    rw [← matrix_map_mul, hV₂U₂]
    apply Matrix.ext; intro i j; simp only [Matrix.map_apply, Matrix.one_apply]; split_ifs <;> simp
  have hev₁_e : ((e.map (algebraMap R Rf)).map (Polynomial.C.comp Polynomial.C)).map ev₁ =
      e.map (Polynomial.C.comp (algebraMap R Rf)) := by
    apply Matrix.ext; intro i j; simp [ev₁, evalXY]
  have hev₂_e : ((e.map (algebraMap R Rg)).map (Polynomial.C.comp Polynomial.C)).map ev₂ =
      e.map (Polynomial.C.comp (algebraMap R Rg)) := by
    apply Matrix.ext; intro i j; simp [ev₂, evalXY]
  have hA₁e : let ef := e.map (Polynomial.C.comp (algebraMap R Rf)); A₁ = 1 - ef + ef * A₁ * ef := by
    have h1 := matrix_idem_map (f := ev₁) (by simp) (fun _ _ => by simp) (fun _ _ => by simp) hU₁e
    rwa [hev₁_e] at h1
  have hB₁e : let ef := e.map (Polynomial.C.comp (algebraMap R Rf)); B₁ = 1 - ef + ef * B₁ * ef := by
    have h1 := matrix_idem_map (f := ev₁) (by simp) (fun _ _ => by simp) (fun _ _ => by simp) hV₁e
    rwa [hev₁_e] at h1
  have hA₂e : let eg := e.map (Polynomial.C.comp (algebraMap R Rg)); A₂ = 1 - eg + eg * A₂ * eg := by
    have h1 := matrix_idem_map (f := ev₂) (by simp) (fun _ _ => by simp) (fun _ _ => by simp) hU₂e
    rwa [hev₂_e] at h1
  have hB₂e : let eg := e.map (Polynomial.C.comp (algebraMap R Rg)); B₂ = 1 - eg + eg * B₂ * eg := by
    have h1 := matrix_idem_map (f := ev₂) (by simp) (fun _ _ => by simp) (fun _ _ => by simp) hV₂e
    rwa [hev₂_e] at h1
  let r_poly : Polynomial Rfg := Polynomial.C (algebraMap R Rfg (a * f ^ m₂)) * Polynomial.X
  have hA₁_fg : A₁.map (Polynomial.mapRingHom ιf) =
      A * B.map (Polynomial.eval₂RingHom Polynomial.C r_poly) := by
    have hmap_ev₁ : A₁.map (Polynomial.mapRingHom ιf) =
        (U₁.map (Polynomial.mapRingHom (Polynomial.mapRingHom ιf))).map
          (evalXY (p₁.map ιf) (q₁.map ιf)) := by
      apply Matrix.ext; intro i j
      exact congrArg (fun h => h (U₁ i j)) (map_comp_evalXY ιf p₁ q₁)
    rw [hmap_ev₁, hU₁_fg, matrix_map_mul]
    have hp₁ : p₁.map ιf = r_poly := by
      simp [p₁, r_poly, ιf, IsLocalization.Away.awayToAwayRight_eq]
    have hq₁ : q₁.map ιf = Polynomial.C (algebraMap R Rfg b) * Polynomial.X := by
      simp [q₁, ιf, IsLocalization.Away.awayToAwayRight_eq]
    have hsum : p₁.map ιf + Polynomial.C (algebraMap R Rfg (g ^ m₁)) * q₁.map ιf = Polynomial.X := by
      rw [hp₁, hq₁]
      calc r_poly + Polynomial.C (algebraMap R Rfg (g ^ m₁)) * (Polynomial.C (algebraMap R Rfg b) * Polynomial.X)
          = Polynomial.C (algebraMap R Rfg (a * f ^ m₂ + b * g ^ m₁)) * Polynomial.X := by
            simp only [r_poly, map_add, map_mul]; ring
        _ = Polynomial.X := by rw [hab, map_one, map_one, one_mul]
    congr 1
    · apply Matrix.ext; intro i j
      simp only [Matrix.map_apply, RingHom.comp_apply]
      have h1 := congrArg (fun h => h (A i j))
        (evalXY_comp_scaleY_addY (algebraMap R Rfg (g ^ m₁)) (p₁.map ιf) (q₁.map ιf))
      simp only [RingHom.comp_apply] at h1
      rw [h1, hsum]
      exact Polynomial.eval₂_C_X
    · apply Matrix.ext; intro i j
      simp only [Matrix.map_apply]
      have h1 := congrArg (fun h => h (B i j)) (evalXY_comp_C (p₁.map ιf) (q₁.map ιf))
      simp only [RingHom.comp_apply] at h1
      rw [h1, hp₁]
  have hA₂_fg : A₂.map (Polynomial.mapRingHom ιg) =
      A.map (Polynomial.eval₂RingHom Polynomial.C r_poly) := by
    have hmap_ev₂ : A₂.map (Polynomial.mapRingHom ιg) =
        (U₂.map (Polynomial.mapRingHom (Polynomial.mapRingHom ιg))).map
          (evalXY (p₂.map ιg) (q₂.map ιg)) := by
      apply Matrix.ext; intro i j
      exact congrArg (fun h => h (U₂ i j)) (map_comp_evalXY ιg p₂ q₂)
    rw [hmap_ev₂, hU₂_fg, matrix_map_mul]
    have hp₂ : p₂.map ιg = 0 := by simp [p₂]
    have hq₂ : q₂.map ιg = Polynomial.C (algebraMap R Rfg a) * Polynomial.X := by
      simp [q₂, ιg, IsLocalization.Away.awayToAwayLeft_eq]
    have hsum : p₂.map ιg + Polynomial.C (algebraMap R Rfg (f ^ m₂)) * q₂.map ιg = r_poly := by
      rw [hp₂, hq₂, zero_add]
      simp only [r_poly, map_mul]; ring
    have hB0 : B.map (Polynomial.evalRingHom 0) = 1 := by
      have h1 : (A * B).map (Polynomial.evalRingHom 0) = 1 := by
        rw [hAB]; apply Matrix.ext; intro i j; simp only [Matrix.map_apply, Matrix.one_apply]; split_ifs <;> simp
      rw [matrix_map_mul, hA0, one_mul] at h1
      exact h1
    have hB_ev0 : (B.map Polynomial.C).map (evalXY (p₂.map ιg) (q₂.map ιg)) = 1 := by
      have h1 : (B.map Polynomial.C).map (evalXY (p₂.map ιg) (q₂.map ιg)) =
          (B.map (Polynomial.evalRingHom 0)).map Polynomial.C := by
        apply Matrix.ext; intro i j
        simp only [Matrix.map_apply]
        have hc := congrArg (fun h => h (B i j)) (evalXY_comp_C (p₂.map ιg) (q₂.map ιg))
        simp only [RingHom.comp_apply] at hc
        rw [hc, hp₂]
        have hce : Polynomial.eval₂RingHom Polynomial.C (0 : Polynomial Rfg) =
            Polynomial.C.comp (Polynomial.evalRingHom (0 : Rfg)) := by
          apply Polynomial.ringHom_ext
          · intro c; simp
          · simp
        exact congrArg (fun h => h (B i j)) hce
      rw [h1, hB0]
      apply Matrix.ext; intro i j; simp only [Matrix.map_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [hB_ev0, mul_one]
    apply Matrix.ext; intro i j
    simp only [Matrix.map_apply, RingHom.comp_apply]
    have h1 := congrArg (fun h => h (A i j))
      (evalXY_comp_scaleY_addY (algebraMap R Rfg (f ^ m₂)) (p₂.map ιg) (q₂.map ιg))
    simp only [RingHom.comp_apply] at h1
    rw [h1, hsum]
  refine ⟨A₁, B₁, A₂, B₂, hA₁B₁, hB₁A₁, hA₂B₂, hB₂A₂, ⟨hA₁e, hB₁e⟩, ⟨hA₂e, hB₂e⟩, ?_⟩
  rw [hA₁_fg, hA₂_fg, mul_assoc, ← matrix_map_mul, hBA]
  have h1 : (1 : Matrix (Fin k) (Fin k) (Polynomial Rfg)).map
      (Polynomial.eval₂RingHom Polynomial.C r_poly) = 1 := by
    apply Matrix.ext; intro i j; simp only [Matrix.map_apply, Matrix.one_apply]; split_ifs <;> simp
  rw [h1, mul_one]

end MatrixSplit

section MatrixAux

private lemma mat_map_mul {R T : Type*} [Semiring R] [Semiring T] {k : ℕ} (f : R →+* T)
    (M N : Matrix (Fin k) (Fin k) R) : (M * N).map f = M.map f * N.map f := by
  apply Matrix.ext; intro i j
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]

private lemma mat_map_mul_rect {R T : Type*} [Semiring R] [Semiring T] {m n p : ℕ} (f : R →+* T)
    (M : Matrix (Fin m) (Fin n) R) (N : Matrix (Fin n) (Fin p) R) :
    (M * N).map f = M.map f * N.map f := by
  apply Matrix.ext; intro i j
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]

private lemma mat_map_one {R T : Type*} [Semiring R] [Semiring T] {k : ℕ} (f : R →+* T) :
    (1 : Matrix (Fin k) (Fin k) R).map f = 1 := by
  apply Matrix.ext; intro i j
  simp only [Matrix.map_apply, Matrix.one_apply]
  split_ifs <;> simp

private lemma mat_map_zero {R T : Type*} [Semiring R] [Semiring T] {k : ℕ} (f : R →+* T) :
    (0 : Matrix (Fin k) (Fin k) R).map f = 0 := by
  apply Matrix.ext; intro i j; simp

private lemma mat_map_comp {α β γ : Type*} {m n : ℕ} (f : α → β) (g : β → γ)
    (M : Matrix (Fin m) (Fin n) α) : (M.map f).map g = M.map (g ∘ f) := by
  apply Matrix.ext; intro i j; rfl

end MatrixAux

section ZariskiGlue

variable {S : Type*} [CommRing S]

private lemma zariski_injective {f g : S} (hcop : IsCoprime f g) {x : S}
    (hf : algebraMap S (Localization.Away f) x = 0)
    (hg : algebraMap S (Localization.Away g) x = 0) : x = 0 := by
  rw [← map_zero (algebraMap S (Localization.Away f))] at hf
  rw [← map_zero (algebraMap S (Localization.Away g))] at hg
  obtain ⟨n₁, hn₁⟩ := IsLocalization.Away.exists_of_eq f hf
  obtain ⟨n₂, hn₂⟩ := IsLocalization.Away.exists_of_eq g hg
  rw [mul_zero] at hn₁ hn₂
  obtain ⟨a, b, hab⟩ := hcop.pow (m := n₁) (n := n₂)
  calc x = (a * f ^ n₁ + b * g ^ n₂) * x := by rw [hab, one_mul]
    _ = a * (f ^ n₁ * x) + b * (g ^ n₂ * x) := by ring
    _ = 0 := by rw [hn₁, hn₂]; ring

private lemma zariski_glue {f g : S} (hcop : IsCoprime f g)
    (xf : Localization.Away f) (xg : Localization.Away g)
    (heq : IsLocalization.Away.awayToAwayRight f g (P := Localization.Away (f * g)) xf =
      IsLocalization.Away.awayToAwayLeft g f (P := Localization.Away (f * g)) xg) :
    ∃ x : S, algebraMap S (Localization.Away f) x = xf ∧
      algebraMap S (Localization.Away g) x = xg := by
  let Rf := Localization.Away f
  let Rg := Localization.Away g
  let Rfg := Localization.Away (f * g)
  obtain ⟨n₁, a₁, ha₁⟩ := IsLocalization.Away.surj f xf
  obtain ⟨n₂, a₂, ha₂⟩ := IsLocalization.Away.surj g xg
  let n := max n₁ n₂
  let b₁ : S := f ^ (n - n₁) * a₁
  let b₂ : S := g ^ (n - n₂) * a₂
  have hb₁ : xf * (algebraMap S Rf f) ^ n = algebraMap S Rf b₁ := by
    dsimp only [b₁]
    rw [map_mul, map_pow, ← ha₁, ← mul_assoc, mul_comm _ xf, mul_assoc, ← pow_add,
      Nat.sub_add_cancel (le_max_left n₁ n₂)]
  have hb₂ : xg * (algebraMap S Rg g) ^ n = algebraMap S Rg b₂ := by
    dsimp only [b₂]
    rw [map_mul, map_pow, ← ha₂, ← mul_assoc, mul_comm _ xg, mul_assoc, ← pow_add,
      Nat.sub_add_cancel (le_max_right n₁ n₂)]
  have hfg : algebraMap S Rfg (b₁ * g ^ n) = algebraMap S Rfg (b₂ * f ^ n) := by
    have h1 := congrArg (IsLocalization.Away.awayToAwayRight f g (S := Rf) (P := Rfg)) hb₁
    have h2 := congrArg (IsLocalization.Away.awayToAwayLeft g f (S := Rg) (P := Rfg)) hb₂
    simp only [map_mul, map_pow, IsLocalization.Away.awayToAwayRight_eq,
      IsLocalization.Away.awayToAwayLeft_eq] at h1 h2
    simp only [map_mul, map_pow, ← h1, ← h2, heq]
    ring
  obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq (f * g) hfg
  let N := m + n
  let y₁ : S := f ^ m * b₁
  let y₂ : S := g ^ m * b₂
  have hy_eq : g ^ N * y₁ = f ^ N * y₂ := by
    dsimp only [N, y₁, y₂]
    rw [mul_pow] at hm
    calc g ^ (m + n) * (f ^ m * b₁)
        = f ^ m * g ^ m * (b₁ * g ^ n) := by rw [pow_add]; ring
      _ = f ^ m * g ^ m * (b₂ * f ^ n) := hm
      _ = f ^ (m + n) * (g ^ m * b₂) := by rw [pow_add]; ring
  obtain ⟨u, v, huv⟩ := hcop.pow (m := N) (n := N)
  refine ⟨u * y₁ + v * y₂, ?_, ?_⟩
  · have hfu : IsUnit (algebraMap S Rf f) := IsLocalization.Away.algebraMap_isUnit f
    apply (hfu.pow N).mul_right_injective
    change (algebraMap S Rf f) ^ N * algebraMap S Rf (u * y₁ + v * y₂) =
      (algebraMap S Rf f) ^ N * xf
    have hlhs : (algebraMap S Rf f) ^ N * algebraMap S Rf (u * y₁ + v * y₂) =
        algebraMap S Rf y₁ := by
      have hS : f ^ N * (u * y₁ + v * y₂) = y₁ := by
        calc f ^ N * (u * y₁ + v * y₂)
            = u * f ^ N * y₁ + v * (f ^ N * y₂) := by ring
          _ = u * f ^ N * y₁ + v * (g ^ N * y₁) := by rw [← hy_eq]
          _ = (u * f ^ N + v * g ^ N) * y₁ := by ring
          _ = y₁ := by rw [huv, one_mul]
      rw [← map_pow, ← map_mul, hS]
    rw [hlhs]
    dsimp only [N, y₁]
    rw [pow_add, map_mul, map_pow, ← hb₁]
    ring
  · have hgu : IsUnit (algebraMap S Rg g) := IsLocalization.Away.algebraMap_isUnit g
    apply (hgu.pow N).mul_right_injective
    change (algebraMap S Rg g) ^ N * algebraMap S Rg (u * y₁ + v * y₂) =
      (algebraMap S Rg g) ^ N * xg
    have hlhs : (algebraMap S Rg g) ^ N * algebraMap S Rg (u * y₁ + v * y₂) =
        algebraMap S Rg y₂ := by
      have hS : g ^ N * (u * y₁ + v * y₂) = y₂ := by
        calc g ^ N * (u * y₁ + v * y₂)
            = u * (g ^ N * y₁) + v * g ^ N * y₂ := by ring
          _ = u * (f ^ N * y₂) + v * g ^ N * y₂ := by rw [hy_eq]
          _ = (u * f ^ N + v * g ^ N) * y₂ := by ring
          _ = y₂ := by rw [huv, one_mul]
      rw [← map_pow, ← map_mul, hS]
    rw [hlhs]
    dsimp only [N, y₂]
    rw [pow_add, map_mul, map_pow, ← hb₂]
    ring

private lemma poly_zariski_injective {f g : S} (hcop : IsCoprime f g) {p : Polynomial S}
    (hf : p.map (algebraMap S (Localization.Away f)) = 0)
    (hg : p.map (algebraMap S (Localization.Away g)) = 0) : p = 0 := by
  ext d
  rw [Polynomial.coeff_zero]
  refine zariski_injective hcop ?_ ?_
  · have := congrArg (fun q => q.coeff d) hf
    simpa using this
  · have := congrArg (fun q => q.coeff d) hg
    simpa using this

private lemma poly_zariski_glue {f g : S} (hcop : IsCoprime f g)
    (pf : Polynomial (Localization.Away f)) (pg : Polynomial (Localization.Away g))
    (heq : pf.map (IsLocalization.Away.awayToAwayRight f g (P := Localization.Away (f * g))) =
      pg.map (IsLocalization.Away.awayToAwayLeft g f (P := Localization.Away (f * g)))) :
    ∃ p : Polynomial S, p.map (algebraMap S (Localization.Away f)) = pf ∧
      p.map (algebraMap S (Localization.Away g)) = pg := by
  classical
  have hcoeff : ∀ d : ℕ, ∃ c : S,
      algebraMap S (Localization.Away f) c = pf.coeff d ∧
      algebraMap S (Localization.Away g) c = pg.coeff d := by
    intro d
    refine zariski_glue hcop (pf.coeff d) (pg.coeff d) ?_
    have := congrArg (fun q => q.coeff d) heq
    simpa using this
  choose cf hcf using hcoeff
  let D : ℕ := max pf.natDegree pg.natDegree + 1
  let p : Polynomial S := ∑ d ∈ Finset.range D, Polynomial.monomial d (cf d)
  refine ⟨p, ?_, ?_⟩
  · ext d
    simp only [p, Polynomial.map_sum, Polynomial.finsetSum_coeff, Polynomial.map_monomial,
      Polynomial.coeff_monomial]
    by_cases hd : d < D
    · rw [Finset.sum_eq_single d]
      · simp [(hcf d).1]
      · intro b _ hbd; simp [hbd]
      · intro h; exact False.elim (h (Finset.mem_range.mpr hd))
    · rw [Finset.sum_eq_zero]
      · symm
        refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
        omega
      · intro b hb
        have hlt : b < D := Finset.mem_range.mp hb
        have hne : b ≠ d := by omega
        simp [hne]
  · ext d
    simp only [p, Polynomial.map_sum, Polynomial.finsetSum_coeff, Polynomial.map_monomial,
      Polynomial.coeff_monomial]
    by_cases hd : d < D
    · rw [Finset.sum_eq_single d]
      · simp [(hcf d).2]
      · intro b _ hbd; simp [hbd]
      · intro h; exact False.elim (h (Finset.mem_range.mpr hd))
    · rw [Finset.sum_eq_zero]
      · symm
        refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
        omega
      · intro b hb
        have hlt : b < D := Finset.mem_range.mp hb
        have hne : b ≠ d := by omega
        simp [hne]

private lemma mat_poly_zariski_injective {f g : S} (hcop : IsCoprime f g) {k : ℕ}
    {M : Matrix (Fin k) (Fin k) (Polynomial S)}
    (hf : M.map (Polynomial.mapRingHom (algebraMap S (Localization.Away f))) = 0)
    (hg : M.map (Polynomial.mapRingHom (algebraMap S (Localization.Away g))) = 0) : M = 0 := by
  apply Matrix.ext; intro i j
  exact poly_zariski_injective hcop
    (congrArg (fun X => X i j) hf)
    (congrArg (fun X => X i j) hg)

private lemma mat_poly_zariski_glue {f g : S} (hcop : IsCoprime f g) {k : ℕ}
    (Mf : Matrix (Fin k) (Fin k) (Polynomial (Localization.Away f)))
    (Mg : Matrix (Fin k) (Fin k) (Polynomial (Localization.Away g)))
    (heq : Mf.map (Polynomial.mapRingHom (IsLocalization.Away.awayToAwayRight f g (P := Localization.Away (f * g)))) =
      Mg.map (Polynomial.mapRingHom (IsLocalization.Away.awayToAwayLeft g f (P := Localization.Away (f * g))))) :
    ∃ M : Matrix (Fin k) (Fin k) (Polynomial S),
      M.map (Polynomial.mapRingHom (algebraMap S (Localization.Away f))) = Mf ∧
      M.map (Polynomial.mapRingHom (algebraMap S (Localization.Away g))) = Mg := by
  classical
  have hentry : ∀ (i j : Fin k), ∃ p : Polynomial S,
      p.map (algebraMap S (Localization.Away f)) = Mf i j ∧
      p.map (algebraMap S (Localization.Away g)) = Mg i j :=
    fun i j => poly_zariski_glue hcop (Mf i j) (Mg i j) (congrArg (fun X => X i j) heq)
  choose pf hpf using hentry
  refine ⟨Matrix.of fun i j => pf i j, ?_, ?_⟩
  · apply Matrix.ext; intro i j; exact (hpf i j).1
  · apply Matrix.ext; intro i j; exact (hpf i j).2

end ZariskiGlue

section MatIso

/-- Matrix formulation of 'the projective module `im(E)` is isomorphic to `im(E(0)) ⊗_R S[X]`
after base change along `φ : R →+* S`'. -/
def MatIsoOver {R S : Type*} [CommRing R] [CommRing S] {k : ℕ} (φ : R →+* S)
    (E : Matrix (Fin k) (Fin k) (Polynomial R)) : Prop :=
  let ES := E.map (Polynomial.mapRingHom φ)
  let eS := (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp φ)
  ∃ U V : Matrix (Fin k) (Fin k) (Polynomial S),
    eS * U * ES = U ∧ ES * V * eS = V ∧ U * V = eS ∧ V * U = ES

private lemma matIsoOver_map {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {k : ℕ}
    {φ : R →+* S} (ψ : S →+* T) {E : Matrix (Fin k) (Fin k) (Polynomial R)}
    (h : MatIsoOver φ E) : MatIsoOver (ψ.comp φ) E := by
  obtain ⟨U, V, h1, h2, h3, h4⟩ := h
  let ψX := Polynomial.mapRingHom ψ
  have hE : (E.map (Polynomial.mapRingHom φ)).map ψX = E.map (Polynomial.mapRingHom (ψ.comp φ)) := by
    apply Matrix.ext; intro i j
    simp [ψX, Polynomial.map_map]
  have he : ((E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp φ)).map ψX =
      (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp (ψ.comp φ)) := by
    apply Matrix.ext; intro i j
    simp [ψX]
  refine ⟨U.map ψX, V.map ψX, ?_, ?_, ?_, ?_⟩
  · have := congrArg (fun M => M.map ψX) h1
    rwa [mat_map_mul, mat_map_mul, hE, he] at this
  · have := congrArg (fun M => M.map ψX) h2
    rwa [mat_map_mul, mat_map_mul, hE, he] at this
  · have := congrArg (fun M => M.map ψX) h3
    rwa [mat_map_mul, he] at this
  · have := congrArg (fun M => M.map ψX) h4
    rwa [mat_map_mul, hE] at this

private lemma matIsoOver_of_subsingleton {R S : Type*} [CommRing R] [CommRing S] [Subsingleton S]
    {k : ℕ} (φ : R →+* S) (E : Matrix (Fin k) (Fin k) (Polynomial R)) : MatIsoOver φ E := by
  refine ⟨0, 0, ?_, ?_, ?_, ?_⟩ <;> exact Subsingleton.elim _ _

/-- Normalize `(U, V)` witnessing `MatIsoOver` so that `U(0) = e` and `V(0) = e`. -/
private lemma matIsoOver_normalize {R S : Type*} [CommRing R] [CommRing S] {k : ℕ}
    (φ : R →+* S) {E : Matrix (Fin k) (Fin k) (Polynomial R)} (hE : E * E = E)
    (h : MatIsoOver φ E) :
    let ES := E.map (Polynomial.mapRingHom φ)
    let eS := (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp φ)
    ∃ U V : Matrix (Fin k) (Fin k) (Polynomial S),
      eS * U * ES = U ∧ ES * V * eS = V ∧ U * V = eS ∧ V * U = ES ∧
      U.map (Polynomial.evalRingHom 0) = (E.map (Polynomial.evalRingHom 0)).map φ ∧
      V.map (Polynomial.evalRingHom 0) = (E.map (Polynomial.evalRingHom 0)).map φ := by
  obtain ⟨U, V, h1, h2, h3, h4⟩ := h
  let ES := E.map (Polynomial.mapRingHom φ)
  let e0 : Matrix (Fin k) (Fin k) S := (E.map (Polynomial.evalRingHom 0)).map φ
  let eS : Matrix (Fin k) (Fin k) (Polynomial S) := (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp φ)
  have heS_eq : eS = e0.map Polynomial.C := by apply Matrix.ext; intro i j; rfl
  have hES_ev0 : ES.map (Polynomial.evalRingHom 0) = e0 := by
    apply Matrix.ext; intro i j
    simp [ES, e0, Polynomial.eval_map, Polynomial.coeff_zero_eq_eval_zero]
  have heS_ev0 : eS.map (Polynomial.evalRingHom 0) = e0 := by
    apply Matrix.ext; intro i j
    simp [eS, e0]
  have he0_idem : e0 * e0 = e0 := by
    have h1 := congrArg (fun M => M.map (Polynomial.evalRingHom 0)) hE
    rw [mat_map_mul] at h1
    have h2 := congrArg (fun M => M.map φ) h1
    rwa [mat_map_mul] at h2
  have heS_idem : eS * eS = eS := by
    rw [heS_eq, ← mat_map_mul, he0_idem]
  let U0 := (U.map (Polynomial.evalRingHom 0)).map Polynomial.C
  let V0 := (V.map (Polynomial.evalRingHom 0)).map Polynomial.C
  change eS * U * ES = U at h1
  change ES * V * eS = V at h2
  change U * V = eS at h3
  change V * U = ES at h4
  have hU0V0 : U0 * V0 = eS := by
    rw [heS_eq, ← mat_map_mul, ← mat_map_mul, h3, heS_ev0]
  have hV0U0 : V0 * U0 = eS := by
    rw [heS_eq, ← mat_map_mul, ← mat_map_mul, h4, hES_ev0]
  have heU0e : eS * U0 * eS = U0 := by
    have := congrArg (fun M => (M.map (Polynomial.evalRingHom 0)).map Polynomial.C) h1
    rw [mat_map_mul, mat_map_mul, mat_map_mul, mat_map_mul, heS_ev0, hES_ev0, ← heS_eq] at this
    exact this
  have heV0e : eS * V0 * eS = V0 := by
    have := congrArg (fun M => (M.map (Polynomial.evalRingHom 0)).map Polynomial.C) h2
    rw [mat_map_mul, mat_map_mul, mat_map_mul, mat_map_mul, heS_ev0, hES_ev0, ← heS_eq] at this
    exact this
  have heV0 : eS * V0 = V0 := by
    calc eS * V0 = eS * (eS * V0 * eS) := by rw [heV0e]
      _ = (eS * eS) * V0 * eS := by simp only [Matrix.mul_assoc]
      _ = eS * V0 * eS := by rw [heS_idem]
      _ = V0 := heV0e
  have hU0e : U0 * eS = U0 := by
    calc U0 * eS = (eS * U0 * eS) * eS := by rw [heU0e]
      _ = eS * U0 * (eS * eS) := by simp only [Matrix.mul_assoc]
      _ = eS * U0 * eS := by rw [heS_idem]
      _ = U0 := heU0e
  have hUe : eS * U = U := by
    calc eS * U = eS * (eS * U * ES) := by rw [h1]
      _ = (eS * eS) * U * ES := by simp only [Matrix.mul_assoc]
      _ = eS * U * ES := by rw [heS_idem]
      _ = U := h1
  have hVe : V * eS = V := by
    calc V * eS = (ES * V * eS) * eS := by rw [h2]
      _ = ES * V * (eS * eS) := by simp only [Matrix.mul_assoc]
      _ = ES * V * eS := by rw [heS_idem]
      _ = V := h2
  have hUE : U * ES = U := by
    have hES_idem : ES * ES = ES := by
      have := congrArg (fun M => M.map (Polynomial.mapRingHom φ)) hE
      rwa [mat_map_mul] at this
    calc U * ES = (eS * U * ES) * ES := by rw [h1]
      _ = eS * U * (ES * ES) := by simp only [Matrix.mul_assoc]
      _ = eS * U * ES := by rw [hES_idem]
      _ = U := h1
  have hEV : ES * V = V := by
    have hES_idem : ES * ES = ES := by
      have := congrArg (fun M => M.map (Polynomial.mapRingHom φ)) hE
      rwa [mat_map_mul] at this
    calc ES * V = ES * (ES * V * eS) := by rw [h2]
      _ = (ES * ES) * V * eS := by simp only [Matrix.mul_assoc]
      _ = ES * V * eS := by rw [hES_idem]
      _ = V := h2
  refine ⟨V0 * U, V * U0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc eS * (V0 * U) * ES = (eS * V0) * (U * ES) := by simp only [Matrix.mul_assoc]
      _ = V0 * U := by rw [heV0, hUE]
  · calc ES * (V * U0) * eS = (ES * V) * (U0 * eS) := by simp only [Matrix.mul_assoc]
      _ = V * U0 := by rw [hEV, hU0e]
  · calc (V0 * U) * (V * U0) = V0 * (U * V) * U0 := by simp only [Matrix.mul_assoc]
      _ = (V0 * eS) * U0 := by rw [h3]
      _ = (eS * V0 * eS) * U0 := by rw [heV0]
      _ = V0 * U0 := by rw [heV0e]
      _ = eS := hV0U0
  · calc (V * U0) * (V0 * U) = V * (U0 * V0) * U := by simp only [Matrix.mul_assoc]
      _ = (V * eS) * U := by rw [hU0V0]
      _ = V * U := by rw [hVe]
      _ = ES := h4
  · rw [mat_map_mul]
    have hV0_ev : V0.map (Polynomial.evalRingHom 0) = V.map (Polynomial.evalRingHom 0) := by
      apply Matrix.ext; intro i j; simp [V0]
    rw [hV0_ev, ← mat_map_mul, h4, hES_ev0]
  · rw [mat_map_mul]
    have hU0_ev : U0.map (Polynomial.evalRingHom 0) = U.map (Polynomial.evalRingHom 0) := by
      apply Matrix.ext; intro i j; simp [U0]
    rw [hU0_ev, ← mat_map_mul, h4, hES_ev0]

/-- Spreading out `MatIsoOver` from `Localization.AtPrime m` to `Localization.Away f` for some `f ∉ m`. -/
private lemma matIsoOver_spread_out {R : Type*} [CommRing R] (m : Ideal R) [m.IsPrime] {k : ℕ}
    (E : Matrix (Fin k) (Fin k) (Polynomial R)) (hE : E * E = E)
    (hm : MatIsoOver (algebraMap R (Localization.AtPrime m)) E) :
    ∃ f : R, f ∉ m ∧ MatIsoOver (algebraMap R (Localization.Away f)) E := by
  classical
  let Rm := Localization.AtPrime m
  let φm : R →+* Rm := algebraMap R Rm
  let φmX : Polynomial R →+* Polynomial Rm := Polynomial.mapRingHom φm
  let eX : Matrix (Fin k) (Fin k) (Polynomial R) := (E.map (Polynomial.evalRingHom 0)).map Polynomial.C
  have heX_idem : eX * eX = eX := by
    have h1 := congrArg (fun M => (M.map (Polynomial.evalRingHom 0)).map Polynomial.C) hE
    simpa only [mat_map_mul] using h1
  have heX_map : eX.map φmX = (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp φm) := by
    apply Matrix.ext; intro i j; simp [eX, φmX]
  obtain ⟨U, V, h1, h2, h3, h4⟩ := hm
  -- Helper: clear denominators of a polynomial over Rm
  have clear_poly : ∀ p : Polynomial Rm, ∃ (s : m.primeCompl) (p₀ : Polynomial R),
      p₀.map φm = Polynomial.C (φm s.1) * p := by
    intro p
    have hc : ∀ d ∈ p.support, ∃ (s : m.primeCompl) (a : R), φm a = φm s.1 * p.coeff d := by
      intro d _
      obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj m.primeCompl (p.coeff d)
      refine ⟨s, a, ?_⟩
      rw [mul_comm]
      exact hs.symm
    choose sf af haf using hc
    let s : m.primeCompl := ∏ d ∈ p.support.attach, sf d.1 d.2
    let p₀ : Polynomial R :=
      ∑ d ∈ p.support.attach,
        Polynomial.monomial d.1 ((∏ d' ∈ p.support.attach.erase d, (sf d'.1 d'.2).1) * af d.1 d.2)
    refine ⟨s, p₀, ?_⟩
    ext d
    simp only [p₀, Polynomial.map_sum, Polynomial.finsetSum_coeff, Polynomial.map_monomial,
      Polynomial.coeff_monomial, Polynomial.coeff_C_mul]
    by_cases hd : d ∈ p.support
    · rw [Finset.sum_eq_single ⟨d, hd⟩]
      · simp only [↓reduceIte, map_mul, haf d hd]
        have hs_val : s.1 = (sf d hd).1 * ∏ d' ∈ p.support.attach.erase ⟨d, hd⟩, (sf d'.1 d'.2).1 := by
          have hmem : (⟨d, hd⟩ : {x // x ∈ p.support}) ∈ p.support.attach := Finset.mem_attach _ _
          have hprod := Finset.mul_prod_erase p.support.attach (fun x => (sf x.1 x.2).1) hmem
          have hcoe : s.1 = ∏ x ∈ p.support.attach, (sf x.1 x.2).1 := by
            simp [s]
          rw [hcoe, ← hprod]
        rw [hs_val, map_mul]
        ring
      · intro b _ hb
        have : b.1 ≠ d := fun h => hb (Subtype.ext h)
        simp [this]
      · intro h; exact False.elim (h (Finset.mem_attach _ _))
    · rw [Finset.sum_eq_zero]
      · rw [Polynomial.notMem_support_iff.mp hd, mul_zero]
      · intro b _
        have : b.1 ≠ d := fun h => hd (h ▸ b.2)
        simp [this]
  -- Helper: clear denominators of a matrix over Rm[X]
  have clear_mat : ∀ M : Matrix (Fin k) (Fin k) (Polynomial Rm),
      ∃ (s : m.primeCompl) (M₀ : Matrix (Fin k) (Fin k) (Polynomial R)),
        M₀.map φmX = (Polynomial.C (φm s.1)) • M := by
    intro M
    have he : ∀ i j : Fin k, ∃ (s : m.primeCompl) (p₀ : Polynomial R),
        p₀.map φm = Polynomial.C (φm s.1) * M i j := fun i j => clear_poly (M i j)
    choose sf pf hpf using he
    let s : m.primeCompl := ∏ p : Fin k × Fin k, sf p.1 p.2
    let M₀ : Matrix (Fin k) (Fin k) (Polynomial R) := Matrix.of fun i j =>
      Polynomial.C (∏ p ∈ Finset.univ.erase (i, j), (sf p.1 p.2).1) * pf i j
    refine ⟨s, M₀, ?_⟩
    apply Matrix.ext; intro i j
    change (Polynomial.C (∏ p ∈ Finset.univ.erase (i, j), (sf p.1 p.2).1) * pf i j).map φm =
      Polynomial.C (φm s.1) * M i j
    rw [Polynomial.map_mul, Polynomial.map_C, hpf i j]
    have hs_val : s.1 = (sf i j).1 * ∏ p ∈ Finset.univ.erase (i, j), (sf p.1 p.2).1 := by
      have hprod := Finset.mul_prod_erase (Finset.univ : Finset (Fin k × Fin k))
        (fun p => (sf p.1 p.2).1) (Finset.mem_univ (i, j))
      have hcoe : s.1 = ∏ p : Fin k × Fin k, (sf p.1 p.2).1 := by simp [s]
      rw [hcoe, ← hprod]
    rw [hs_val, map_mul, Polynomial.C_mul]
    ring
  -- Helper: annihilator in m.primeCompl of a matrix mapping to 0 over Rm[X]
  have kill_mat : ∀ M : Matrix (Fin k) (Fin k) (Polynomial R), M.map φmX = 0 →
      ∃ s : m.primeCompl, (Polynomial.C s.1) • M = 0 := by
    intro M hM
    have hp : ∀ (i j : Fin k), ∃ s : m.primeCompl, Polynomial.C s.1 * M i j = 0 := by
      intro i j
      have hij : (M i j).map φm = 0 := congrArg (fun X => X i j) hM
      have hc : ∀ d ∈ (M i j).support, ∃ s : m.primeCompl, s.1 * (M i j).coeff d = 0 := by
        intro d _
        have hd0 : φm ((M i j).coeff d) = 0 := by
          have := congrArg (fun q => q.coeff d) hij
          simpa using this
        exact (IsLocalization.map_eq_zero_iff m.primeCompl Rm _).mp hd0
      choose sf hsf using hc
      let s : m.primeCompl := ∏ d ∈ (M i j).support.attach, sf d.1 d.2
      refine ⟨s, ?_⟩
      ext d
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_zero]
      by_cases hd : d ∈ (M i j).support
      · have hs_val : s.1 = (sf d hd).1 * ∏ d' ∈ (M i j).support.attach.erase ⟨d, hd⟩, (sf d'.1 d'.2).1 := by
          have hmem : (⟨d, hd⟩ : {x // x ∈ (M i j).support}) ∈ (M i j).support.attach := Finset.mem_attach _ _
          have hprod := Finset.mul_prod_erase (M i j).support.attach (fun x => (sf x.1 x.2).1) hmem
          have hcoe : s.1 = ∏ x ∈ (M i j).support.attach, (sf x.1 x.2).1 := by simp [s]
          rw [hcoe, ← hprod]
        rw [hs_val]
        calc (sf d hd).1 * (∏ d' ∈ (M i j).support.attach.erase ⟨d, hd⟩, (sf d'.1 d'.2).1) *
              (M i j).coeff d
            = (∏ d' ∈ (M i j).support.attach.erase ⟨d, hd⟩, (sf d'.1 d'.2).1) *
              ((sf d hd).1 * (M i j).coeff d) := by ring
          _ = 0 := by rw [hsf d hd, mul_zero]
      · rw [Polynomial.notMem_support_iff.mp hd, mul_zero]
    choose sf hsf using hp
    let s : m.primeCompl := ∏ p : Fin k × Fin k, sf p.1 p.2
    refine ⟨s, ?_⟩
    apply Matrix.ext; intro i j
    change Polynomial.C s.1 * M i j = 0
    have hs_val : s.1 = (sf i j).1 * ∏ p ∈ Finset.univ.erase (i, j), (sf p.1 p.2).1 := by
      have hprod := Finset.mul_prod_erase (Finset.univ : Finset (Fin k × Fin k))
        (fun p => (sf p.1 p.2).1) (Finset.mem_univ (i, j))
      have hcoe : s.1 = ∏ p : Fin k × Fin k, (sf p.1 p.2).1 := by simp [s]
      rw [hcoe, ← hprod]
    rw [hs_val, Polynomial.C_mul]
    calc Polynomial.C (sf i j).1 * Polynomial.C (∏ p ∈ Finset.univ.erase (i, j), (sf p.1 p.2).1) *
          M i j
        = Polynomial.C (∏ p ∈ Finset.univ.erase (i, j), (sf p.1 p.2).1) *
          (Polynomial.C (sf i j).1 * M i j) := by ring
      _ = 0 := by rw [hsf i j, mul_zero]
  obtain ⟨s₁, U_raw, hU_raw⟩ := clear_mat U
  obtain ⟨s₂, V_raw, hV_raw⟩ := clear_mat V
  let s : m.primeCompl := s₁ * s₂
  let U₀ := eX * ((Polynomial.C s₂.1) • U_raw) * E
  let V₀ := E * ((Polynomial.C s₁.1) • V_raw) * eX
  have hU₀_e : eX * U₀ * E = U₀ := by
    calc eX * (eX * ((Polynomial.C s₂.1) • U_raw) * E) * E
        = (eX * eX) * ((Polynomial.C s₂.1) • U_raw) * (E * E) := by simp only [Matrix.mul_assoc]
      _ = U₀ := by rw [heX_idem, hE]
  have hV₀_e : E * V₀ * eX = V₀ := by
    calc E * (E * ((Polynomial.C s₁.1) • V_raw) * eX) * eX
        = (E * E) * ((Polynomial.C s₁.1) • V_raw) * (eX * eX) := by simp only [Matrix.mul_assoc]
      _ = V₀ := by rw [hE, heX_idem]
  have hU₀_map : U₀.map φmX = (Polynomial.C (φm s.1)) • U := by
    dsimp only [U₀, s]
    rw [mat_map_mul, mat_map_mul, heX_map]
    have hsm : ((Polynomial.C s₂.1) • U_raw).map φmX = (Polynomial.C (φm (s₁.1 * s₂.1))) • U := by
      apply Matrix.ext; intro i j
      have hUij : (U_raw i j).map φm = Polynomial.C (φm s₁.1) * U i j :=
        congrArg (fun X => X i j) hU_raw
      change (Polynomial.C s₂.1 * U_raw i j).map φm = Polynomial.C (φm (s₁.1 * s₂.1)) * U i j
      rw [Polynomial.map_mul, Polynomial.map_C, hUij, map_mul, Polynomial.C_mul]
      ring
    rw [hsm]
    have hpull : (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp φm) *
        (Polynomial.C (φm (s₁.1 * s₂.1))) • U * E.map φmX =
        (Polynomial.C (φm (s₁.1 * s₂.1))) •
          ((E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp φm) * U * E.map φmX) := by
      apply Matrix.ext; intro i j
      simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => by ring
    rw [hpull, h1]
    rfl
  have hV₀_map : V₀.map φmX = (Polynomial.C (φm s.1)) • V := by
    dsimp only [V₀, s]
    rw [mat_map_mul, mat_map_mul, heX_map]
    have hsm : ((Polynomial.C s₁.1) • V_raw).map φmX = (Polynomial.C (φm (s₁.1 * s₂.1))) • V := by
      apply Matrix.ext; intro i j
      have hVij : (V_raw i j).map φm = Polynomial.C (φm s₂.1) * V i j :=
        congrArg (fun X => X i j) hV_raw
      change (Polynomial.C s₁.1 * V_raw i j).map φm = Polynomial.C (φm (s₁.1 * s₂.1)) * V i j
      rw [Polynomial.map_mul, Polynomial.map_C, hVij, map_mul, Polynomial.C_mul]
      ring
    rw [hsm]
    have hpull : E.map φmX * (Polynomial.C (φm (s₁.1 * s₂.1))) • V *
        (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp φm) =
        (Polynomial.C (φm (s₁.1 * s₂.1))) •
          (E.map φmX * V * (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp φm)) := by
      apply Matrix.ext; intro i j
      simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => by ring
    rw [hpull, h2]
    rfl
  let D₁ := U₀ * V₀ - (Polynomial.C (s.1 * s.1)) • eX
  let D₂ := V₀ * U₀ - (Polynomial.C (s.1 * s.1)) • E
  have hD₁_map : D₁.map φmX = 0 := by
    apply Matrix.ext; intro i j
    have hmul : (U₀ * V₀).map φmX = (Polynomial.C (φm (s.1 * s.1))) • (U * V) := by
      rw [mat_map_mul, hU₀_map, hV₀_map]
      apply Matrix.ext; intro a b
      simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
      refine Finset.sum_congr rfl fun t _ => by ring
    change φmX ((U₀ * V₀) i j - Polynomial.C (s.1 * s.1) * eX i j) = 0
    rw [map_sub]
    have h1' : φmX ((U₀ * V₀) i j) = Polynomial.C (φm (s.1 * s.1)) * (U * V) i j :=
      congrArg (fun X => X i j) hmul
    have h2' : φmX (Polynomial.C (s.1 * s.1) * eX i j) =
        Polynomial.C (φm (s.1 * s.1)) * (eX.map φmX) i j := by
      simp [φmX]
    rw [h1', h2', heX_map, h3, sub_self]
  have hD₂_map : D₂.map φmX = 0 := by
    apply Matrix.ext; intro i j
    have hmul : (V₀ * U₀).map φmX = (Polynomial.C (φm (s.1 * s.1))) • (V * U) := by
      rw [mat_map_mul, hU₀_map, hV₀_map]
      apply Matrix.ext; intro a b
      simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
      refine Finset.sum_congr rfl fun t _ => by ring
    change φmX ((V₀ * U₀) i j - Polynomial.C (s.1 * s.1) * E i j) = 0
    rw [map_sub]
    have h1' : φmX ((V₀ * U₀) i j) = Polynomial.C (φm (s.1 * s.1)) * (V * U) i j :=
      congrArg (fun X => X i j) hmul
    have h2' : φmX (Polynomial.C (s.1 * s.1) * E i j) =
        Polynomial.C (φm (s.1 * s.1)) * (E.map φmX) i j := by
      simp [φmX]
    rw [h1', h2', h4, sub_self]
  obtain ⟨t₁, ht₁⟩ := kill_mat D₁ hD₁_map
  obtain ⟨t₂, ht₂⟩ := kill_mat D₂ hD₂_map
  let fsub : m.primeCompl := s * t₁ * t₂
  refine ⟨fsub.1, fsub.2, ?_⟩
  let Rf := Localization.Away fsub.1
  let φf : R →+* Rf := algebraMap R Rf
  let φfX : Polynomial R →+* Polynomial Rf := Polynomial.mapRingHom φf
  have hsu : IsUnit (φf s.1) := by
    refine IsLocalization.Away.isUnit_of_dvd fsub.1 ?_
    exact ⟨t₁.1 * t₂.1, by change s.1 * t₁.1 * t₂.1 = s.1 * (t₁.1 * t₂.1); ring⟩
  have ht₁u : IsUnit (φf t₁.1) := by
    refine IsLocalization.Away.isUnit_of_dvd fsub.1 ?_
    exact ⟨s.1 * t₂.1, by change s.1 * t₁.1 * t₂.1 = t₁.1 * (s.1 * t₂.1); ring⟩
  have ht₂u : IsUnit (φf t₂.1) := by
    refine IsLocalization.Away.isUnit_of_dvd fsub.1 ?_
    exact ⟨s.1 * t₁.1, by change s.1 * t₁.1 * t₂.1 = t₂.1 * (s.1 * t₁.1); ring⟩
  let sinv : Rf := ↑(hsu.unit⁻¹)
  have hsinv : sinv * φf s.1 = 1 := by
    change (↑(hsu.unit⁻¹) : Rf) * ↑hsu.unit = 1
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  let Uf := (Polynomial.C sinv) • U₀.map φfX
  let Vf := (Polynomial.C sinv) • V₀.map φfX
  have heX_f : eX.map φfX = (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp φf) := by
    apply Matrix.ext; intro i j; simp [eX, φfX]
  refine ⟨Uf, Vf, ?_, ?_, ?_, ?_⟩
  · have h1' := congrArg (fun M => M.map φfX) hU₀_e
    rw [mat_map_mul, mat_map_mul, heX_f] at h1'
    dsimp only [Uf]
    have hpull : (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp φf) *
        ((Polynomial.C sinv) • U₀.map φfX) * E.map φfX =
        (Polynomial.C sinv) •
          ((E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp φf) * U₀.map φfX * E.map φfX) := by
      apply Matrix.ext; intro i j
      simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => by ring
    rw [hpull, h1']
  · have h2' := congrArg (fun M => M.map φfX) hV₀_e
    rw [mat_map_mul, mat_map_mul, heX_f] at h2'
    dsimp only [Vf]
    have hpull : E.map φfX * ((Polynomial.C sinv) • V₀.map φfX) *
        (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp φf) =
        (Polynomial.C sinv) •
          (E.map φfX * V₀.map φfX * (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp φf)) := by
      apply Matrix.ext; intro i j
      simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => by ring
    rw [hpull, h2']
  · apply Matrix.ext; intro i j
    have hkill : Polynomial.C (φf t₁.1) * φfX (D₁ i j) = 0 := by
      have := congrArg (fun M => φfX (M i j)) ht₁
      simpa [φfX] using this
    have hD1f : φfX (D₁ i j) = 0 := by
      have hu : IsUnit (Polynomial.C (φf t₁.1)) := ht₁u.map Polynomial.C
      exact hu.mul_right_injective (by simpa using hkill)
    have hUVij : (U₀.map φfX * V₀.map φfX) i j =
        Polynomial.C (φf (s.1 * s.1)) * (eX.map φfX) i j := by
      have hsub : φfX ((U₀ * V₀) i j) - φfX (Polynomial.C (s.1 * s.1) * eX i j) = 0 := by
        simpa [D₁, map_sub] using hD1f
      have heq := sub_eq_zero.mp hsub
      rw [← mat_map_mul]
      simpa [φfX] using heq
    have hlhs : (Uf * Vf) i j = (Polynomial.C sinv * Polynomial.C sinv) * (U₀.map φfX * V₀.map φfX) i j := by
      simp only [Uf, Vf, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => by ring
    rw [hlhs, hUVij, heX_f, map_mul, Polynomial.C_mul]
    calc Polynomial.C sinv * Polynomial.C sinv *
          (Polynomial.C (φf s.1) * Polynomial.C (φf s.1) *
            ((E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp φf)) i j)
        = (Polynomial.C (sinv * φf s.1)) * (Polynomial.C (sinv * φf s.1)) *
            ((E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp φf)) i j := by
          simp only [Polynomial.C_mul]; ring
      _ = ((E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp φf)) i j := by
          rw [hsinv, map_one, one_mul, one_mul]
  · apply Matrix.ext; intro i j
    have hkill : Polynomial.C (φf t₂.1) * φfX (D₂ i j) = 0 := by
      have := congrArg (fun M => φfX (M i j)) ht₂
      simpa [φfX] using this
    have hD2f : φfX (D₂ i j) = 0 := by
      have hu : IsUnit (Polynomial.C (φf t₂.1)) := ht₂u.map Polynomial.C
      exact hu.mul_right_injective (by simpa using hkill)
    have hVUij : (V₀.map φfX * U₀.map φfX) i j =
        Polynomial.C (φf (s.1 * s.1)) * (E.map φfX) i j := by
      have hsub : φfX ((V₀ * U₀) i j) - φfX (Polynomial.C (s.1 * s.1) * E i j) = 0 := by
        simpa [D₂, map_sub] using hD2f
      have heq := sub_eq_zero.mp hsub
      rw [← mat_map_mul]
      simpa [φfX] using heq
    have hlhs : (Vf * Uf) i j = (Polynomial.C sinv * Polynomial.C sinv) * (V₀.map φfX * U₀.map φfX) i j := by
      simp only [Uf, Vf, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => by ring
    rw [hlhs, hVUij, map_mul, Polynomial.C_mul]
    calc Polynomial.C sinv * Polynomial.C sinv *
          (Polynomial.C (φf s.1) * Polynomial.C (φf s.1) * (E.map φfX) i j)
        = (Polynomial.C (sinv * φf s.1)) * (Polynomial.C (sinv * φf s.1)) * (E.map φfX) i j := by
          simp only [Polynomial.C_mul]; ring
      _ = (E.map φfX) i j := by rw [hsinv, map_one, one_mul, one_mul]

end MatIso

private lemma bridge_mat_map_mul_rect {R T : Type*} [Semiring R] [Semiring T] {m n p : ℕ} (f : R →+* T)
    (M : Matrix (Fin m) (Fin n) R) (N : Matrix (Fin n) (Fin p) R) :
    (M * N).map f = M.map f * N.map f := by
  apply Matrix.ext; intro i j
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]

private lemma bridge_mat_map_one {R T : Type*} [Semiring R] [Semiring T] {k : ℕ} (f : R →+* T) :
    (1 : Matrix (Fin k) (Fin k) R).map f = 1 := by
  apply Matrix.ext; intro i j
  simp only [Matrix.map_apply, Matrix.one_apply]
  split_ifs <;> simp

private noncomputable def finTensorEquiv (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (k : ℕ) : (Fin k → S) ≃ₗ[S] (S ⊗[R] (Fin k → R)) :=
  let invF : (S ⊗[R] (Fin k → R)) →ₗ[S] (Fin k → S) :=
    TensorProduct.AlgebraTensorModule.lift
      { toFun := fun s =>
          { toFun := fun w => fun i => s * algebraMap R S (w i)
            map_add' := fun w₁ w₂ => by funext i; simp [mul_add]
            map_smul' := fun r w => by
              funext i
              simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Algebra.smul_def, map_mul]
              ring }
        map_add' := fun s₁ s₂ => by apply LinearMap.ext; intro w; funext i; simp [add_mul]
        map_smul' := fun a s => by
          apply LinearMap.ext; intro w; funext i
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk,
            LinearMap.smul_apply, mul_assoc] }
  let toF : (Fin k → S) →ₗ[S] (S ⊗[R] (Fin k → R)) :=
    { toFun := fun v => ∑ i : Fin k, v i ⊗ₜ[R] Pi.single i (1 : R)
      map_add' := fun v w => by
        simp only [Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]
      map_smul' := fun a v => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [TensorProduct.smul_tmul']
        rfl }
  LinearEquiv.ofLinearMap toF invF
    (by
      apply LinearMap.ext; intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul s w =>
        have hinv : invF (s ⊗ₜ[R] w) = fun i => s * algebraMap R S (w i) := rfl
        change toF (invF (s ⊗ₜ[R] w)) = s ⊗ₜ[R] w
        rw [hinv]
        change ∑ i : Fin k, (s * algebraMap R S (w i)) ⊗ₜ[R] Pi.single i (1 : R) = s ⊗ₜ[R] w
        have hw : w = ∑ i : Fin k, w i • Pi.single i (1 : R) := by
          funext j; simp [Finset.sum_apply, Pi.single_apply]
        calc ∑ i : Fin k, (s * algebraMap R S (w i)) ⊗ₜ[R] Pi.single i (1 : R)
            = ∑ i : Fin k, s ⊗ₜ[R] (w i • Pi.single i (1 : R)) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_comm]
          _ = s ⊗ₜ[R] (∑ i : Fin k, w i • Pi.single i (1 : R)) := by rw [TensorProduct.tmul_sum]
          _ = s ⊗ₜ[R] w := by rw [← hw]
      | add x y ihx ihy =>
        simp only [LinearMap.comp_apply, LinearMap.id_apply, map_add] at ihx ihy ⊢
        rw [ihx, ihy])
    (by
      apply LinearMap.ext; intro v; funext j
      change (invF (∑ i : Fin k, v i ⊗ₜ[R] Pi.single i (1 : R))) j = v j
      rw [map_sum, Finset.sum_apply, Finset.sum_eq_single j]
      · have h1 : invF (v j ⊗ₜ[R] (Pi.single j (1 : R) : Fin k → R)) =
            fun i => v j * algebraMap R S ((Pi.single j (1 : R) : Fin k → R) i) := rfl
        rw [h1]; simp
      · intro i _ hij
        have h1 : invF (v i ⊗ₜ[R] (Pi.single i (1 : R) : Fin k → R)) =
            fun t => v i * algebraMap R S ((Pi.single i (1 : R) : Fin k → R) t) := rfl
        rw [h1]; simp [Pi.single_eq_of_ne (Ne.symm hij)]
      · intro h; exact False.elim (h (Finset.mem_univ j)))

private lemma finTensorEquiv_symm_tmul (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (k : ℕ) (s : S) (w : Fin k → R) (i : Fin k) :
    ((finTensorEquiv R S k).symm (s ⊗ₜ[R] w)) i = s * algebraMap R S (w i) := rfl

/-- Bridge 1: if `P` is a direct summand of `R[X]^k` with idempotent matrix `E`, and `P_m` is
free over `(R[X])_m`, then `E` is matrix-isomorphic to `E(0)` over `R_m[X]`. -/
lemma matIsoOver_atPrime_of_free {R : Type} [CommRing R]
    (P : Type) [AddCommGroup P] [Module (Polynomial R) P]
    {k : ℕ} (π : (Fin k → Polynomial R) →ₗ[Polynomial R] P)
    (ι : P →ₗ[Polynomial R] (Fin k → Polynomial R))
    (hπι : π ∘ₗ ι = LinearMap.id)
    (m : Ideal R) [m.IsMaximal]
    (hfree : Module.Free (Localization (Algebra.algebraMapSubmonoid (Polynomial R) m.primeCompl))
      (LocalizedModule (Algebra.algebraMapSubmonoid (Polynomial R) m.primeCompl) P)) :
    let E : Matrix (Fin k) (Fin k) (Polynomial R) := LinearMap.toMatrix' (ι ∘ₗ π)
    let φm := algebraMap R (Localization.AtPrime m)
    let Em := E.map (Polynomial.mapRingHom φm)
    let em := (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp φm)
    ∃ U V : Matrix (Fin k) (Fin k) (Polynomial (Localization.AtPrime m)),
      em * U * Em = U ∧ Em * V * em = V ∧ U * V = em ∧ V * U = Em := by
  classical
  let E : Matrix (Fin k) (Fin k) (Polynomial R) := LinearMap.toMatrix' (ι ∘ₗ π)
  let Rm := Localization.AtPrime m
  let RmX := Polynomial Rm
  let φm : R →+* Rm := algebraMap R Rm
  let φmX : Polynomial R →+* RmX := Polynomial.mapRingHom φm
  let Sm : Submonoid (Polynomial R) := Algebra.algebraMapSubmonoid (Polynomial R) m.primeCompl
  let Lm := Localization Sm
  let Pm := LocalizedModule Sm P
  let _ : Algebra (Polynomial R) RmX := φmX.toAlgebra
  have hSm : Sm = m.primeCompl.map Polynomial.C := rfl
  have _ : IsLocalization Sm RmX := by
    rw [hSm]
    exact Polynomial.isLocalization m.primeCompl Rm
  let eAlg : Lm ≃ₐ[Polynomial R] RmX := IsLocalization.algEquiv Sm Lm RmX
  let eqP : Pm ≃ₗ[Lm] (Lm ⊗[Polynomial R] P) := LocalizedModule.equivTensorProduct Sm P
  let eqF : (Fin k → Lm) ≃ₗ[Lm] (Lm ⊗[Polynomial R] (Fin k → Polynomial R)) :=
    finTensorEquiv (Polynomial R) Lm k
  let πm : (Fin k → Lm) →ₗ[Lm] Pm := eqP.symm.toLinearMap ∘ₗ (π.baseChange Lm) ∘ₗ eqF.toLinearMap
  let ιm : Pm →ₗ[Lm] (Fin k → Lm) := eqF.symm.toLinearMap ∘ₗ (ι.baseChange Lm) ∘ₗ eqP.toLinearMap
  have hπmιm : πm ∘ₗ ιm = LinearMap.id := by
    ext x
    change eqP.symm ((π.baseChange Lm) (eqF (eqF.symm ((ι.baseChange Lm) (eqP x))))) = x
    rw [LinearEquiv.apply_symm_apply]
    have hcomp : (π.baseChange Lm) ((ι.baseChange Lm) (eqP x)) = eqP x := by
      have h1 := LinearMap.congr_fun (by
        rw [← LinearMap.baseChange_comp, hπι, LinearMap.baseChange_id] :
          (π.baseChange Lm).comp (ι.baseChange Lm) = LinearMap.id) (eqP x)
      exact h1
    rw [hcomp, LinearEquiv.symm_apply_apply]
  have hιmπm_mat : LinearMap.toMatrix' (ιm ∘ₗ πm) = E.map (algebraMap (Polynomial R) Lm) := by
    apply Matrix.ext; intro i j
    rw [LinearMap.toMatrix'_apply, Matrix.map_apply]
    change (eqF.symm ((ι.baseChange Lm) (eqP (eqP.symm ((π.baseChange Lm) (eqF (Pi.single j 1))))))) i =
      algebraMap (Polynomial R) Lm (E i j)
    rw [LinearEquiv.apply_symm_apply]
    have hF : eqF (Pi.single j (1 : Lm)) = (1 : Lm) ⊗ₜ[Polynomial R] Pi.single j (1 : Polynomial R) := by
      change ∑ t : Fin k, (Pi.single j (1 : Lm) t) ⊗ₜ[Polynomial R] Pi.single t (1 : Polynomial R) = _
      rw [Finset.sum_eq_single j]
      · simp
      · intro t _ htj; simp [Pi.single_eq_of_ne htj]
      · intro h; exact False.elim (h (Finset.mem_univ j))
    rw [hF]
    change (eqF.symm ((1 : Lm) ⊗ₜ[Polynomial R] ι (π (Pi.single j (1 : Polynomial R))))) i = _
    rw [finTensorEquiv_symm_tmul, one_mul]
    rfl
  -- Pm is finite and free over Lm, so Pm ≃ₗ[Lm] (Fin r → Lm)
  have _ : Module.Finite Lm Pm :=
    Module.Finite.of_surjective πm (Function.RightInverse.surjective (LinearMap.congr_fun hπmιm))
  let b := Module.Free.chooseBasis Lm Pm
  let ι_b := Module.Free.ChooseBasisIndex Lm Pm
  let eFin : ι_b ≃ Fin (Fintype.card ι_b) := Fintype.equivFin ι_b
  let r := Fintype.card ι_b
  let α : Pm ≃ₗ[Lm] (Fin r → Lm) :=
    b.equivFun.trans (LinearEquiv.funCongrLeft Lm Lm eFin.symm)
  let gMap : (Fin k → Lm) →ₗ[Lm] (Fin r → Lm) := α.toLinearMap ∘ₗ πm
  let hMap : (Fin r → Lm) →ₗ[Lm] (Fin k → Lm) := ιm ∘ₗ α.symm.toLinearMap
  have hgh : gMap ∘ₗ hMap = LinearMap.id := by
    apply LinearMap.ext; intro x
    change α (πm (ιm (α.symm x))) = x
    have := LinearMap.congr_fun hπmιm (α.symm x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [this, LinearEquiv.apply_symm_apply]
  have hhg : hMap ∘ₗ gMap = ιm ∘ₗ πm := by
    apply LinearMap.ext; intro x
    change ιm (α.symm (α (πm x))) = ιm (πm x)
    rw [LinearEquiv.symm_apply_apply]
  let G : Matrix (Fin r) (Fin k) RmX := (LinearMap.toMatrix' gMap).map eAlg.toRingHom
  let H : Matrix (Fin k) (Fin r) RmX := (LinearMap.toMatrix' hMap).map eAlg.toRingHom
  have hGH : G * H = 1 := by
    rw [← bridge_mat_map_mul_rect, ← LinearMap.toMatrix'_comp, hgh, LinearMap.toMatrix'_id,
      bridge_mat_map_one]
  have hHG : H * G = E.map φmX := by
    rw [← bridge_mat_map_mul_rect, ← LinearMap.toMatrix'_comp, hhg, hιmπm_mat]
    apply Matrix.ext; intro i j
    simp only [Matrix.map_apply]
    exact eAlg.commutes (E i j)
  -- Evaluate at X = 0 to get G₀, H₀ over RmX
  let evC : RmX →+* RmX := Polynomial.C.comp (Polynomial.evalRingHom (0 : Rm))
  let G₀ : Matrix (Fin r) (Fin k) RmX := G.map evC
  let H₀ : Matrix (Fin k) (Fin r) RmX := H.map evC
  have hG₀H₀ : G₀ * H₀ = 1 := by
    rw [← bridge_mat_map_mul_rect, hGH, bridge_mat_map_one]
  have hH₀G₀ : H₀ * G₀ = (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp φm) := by
    rw [← bridge_mat_map_mul_rect, hHG]
    apply Matrix.ext; intro i j
    simp only [evC, φmX, Matrix.map_apply, RingHom.comp_apply]
    congr 1
    change Polynomial.eval 0 ((E i j).map φm) = φm (Polynomial.eval 0 (E i j))
    rw [Polynomial.eval_map, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero]
  refine ⟨H₀ * G, H * G₀, ?_, ?_, ?_, ?_⟩
  · calc (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp φm) * (H₀ * G) * E.map φmX
        = (H₀ * G₀) * (H₀ * G) * (H * G) := by rw [hH₀G₀, hHG]
      _ = H₀ * (G₀ * H₀) * (G * H) * G := by simp only [Matrix.mul_assoc]
      _ = H₀ * G := by rw [hG₀H₀, hGH, Matrix.mul_one, Matrix.mul_one]
  · calc E.map φmX * (H * G₀) * (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp φm)
        = (H * G) * (H * G₀) * (H₀ * G₀) := by rw [hH₀G₀, hHG]
      _ = H * (G * H) * (G₀ * H₀) * G₀ := by simp only [Matrix.mul_assoc]
      _ = H * G₀ := by rw [hGH, hG₀H₀, Matrix.mul_one, Matrix.mul_one]
  · calc (H₀ * G) * (H * G₀) = H₀ * (G * H) * G₀ := by simp only [Matrix.mul_assoc]
      _ = H₀ * G₀ := by rw [hGH, Matrix.mul_one]
      _ = (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp φm) := hH₀G₀
  · calc (H * G₀) * (H₀ * G) = H * (G₀ * H₀) * G := by simp only [Matrix.mul_assoc]
      _ = H * G := by rw [hG₀H₀, Matrix.mul_one]
      _ = E.map φmX := hHG

/-- Bridge 2: if `P` is a direct summand of `R[X]^k` with idempotent matrix `E`, and `E` is
matrix-isomorphic to `E(0)` over `R[X]`, then `P ≃ₗ[R[X]] R[X] ⊗[R] M` for a f.g. projective
`R`-module `M`. -/
lemma module_equiv_of_matIsoOver {R : Type} [CommRing R]
    (P : Type) [AddCommGroup P] [Module (Polynomial R) P]
    {k : ℕ} (π : (Fin k → Polynomial R) →ₗ[Polynomial R] P)
    (ι : P →ₗ[Polynomial R] (Fin k → Polynomial R))
    (hπι : π ∘ₗ ι = LinearMap.id)
    (hiso : let E : Matrix (Fin k) (Fin k) (Polynomial R) := LinearMap.toMatrix' (ι ∘ₗ π)
      let eX := (E.map (Polynomial.evalRingHom 0)).map Polynomial.C
      ∃ U V : Matrix (Fin k) (Fin k) (Polynomial R),
        eX * U * E = U ∧ E * V * eX = V ∧ U * V = eX ∧ V * U = E) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module R M),
      Module.Finite R M ∧ Module.Projective R M ∧
      Nonempty (P ≃ₗ[Polynomial R] Polynomial R ⊗[R] M) := by
  classical
  let E : Matrix (Fin k) (Fin k) (Polynomial R) := LinearMap.toMatrix' (ι ∘ₗ π)
  have hE : E * E = E := by
    dsimp only [E]
    rw [← LinearMap.toMatrix'_comp]
    congr 1
    apply LinearMap.ext; intro x
    change ι (π (ι (π x))) = ι (π x)
    have := LinearMap.congr_fun hπι (π x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [this]
  have hE_mulVec : ∀ v : Fin k → Polynomial R, E *ᵥ v = ι (π v) := fun v => by
    have := LinearMap.congr_fun (Matrix.toLin'_toMatrix' (ι ∘ₗ π)) v
    exact this
  let e : Matrix (Fin k) (Fin k) R := E.map (Polynomial.evalRingHom 0)
  have he : e * e = e := by
    have := congrArg (fun M => M.map (Polynomial.evalRingHom 0)) hE
    rwa [bridge_mat_map_mul_rect] at this
  let eX : Matrix (Fin k) (Fin k) (Polynomial R) := e.map Polynomial.C
  have heX : eX * eX = eX := by
    have := congrArg (fun M => M.map Polynomial.C) he
    rwa [bridge_mat_map_mul_rect] at this
  let M : Type := LinearMap.range (Matrix.toLin' e)
  let π₀ : (Fin k → R) →ₗ[R] M :=
    { toFun := fun v => ⟨e *ᵥ v, v, rfl⟩
      map_add' := fun v w => Subtype.ext (Matrix.mulVec_add e v w)
      map_smul' := fun r v => Subtype.ext (Matrix.mulVec_smul e r v) }
  let ι₀ : M →ₗ[R] (Fin k → R) := Submodule.subtype _
  have hπ₀ι₀ : π₀ ∘ₗ ι₀ = LinearMap.id := by
    ext ⟨_, v, rfl⟩ i
    change (e *ᵥ (e *ᵥ v)) i = (e *ᵥ v) i
    rw [Matrix.mulVec_mulVec, he]
  have hMproj : Module.Projective R M := Module.Projective.of_split ι₀ π₀ hπ₀ι₀
  have hMfin : Module.Finite R M :=
    Module.Finite.of_surjective π₀ (Function.RightInverse.surjective (LinearMap.congr_fun hπ₀ι₀))
  obtain ⟨U, V, h1, h2, h3, h4⟩ := hiso
  change eX * U * E = U at h1
  change E * V * eX = V at h2
  change U * V = eX at h3
  change V * U = E at h4
  have heXU : eX * U = U := by
    calc eX * U = eX * (eX * U * E) := by rw [h1]
      _ = (eX * eX) * U * E := by simp only [Matrix.mul_assoc]
      _ = eX * U * E := by rw [heX]
      _ = U := h1
  have hUE : U * E = U := by
    calc U * E = (eX * U * E) * E := by rw [h1]
      _ = eX * U * (E * E) := by simp only [Matrix.mul_assoc]
      _ = eX * U * E := by rw [hE]
      _ = U := h1
  let toF : P →ₗ[Polynomial R] (Polynomial R ⊗[R] M) :=
    { toFun := fun x => ∑ i : Fin k, ((U *ᵥ ι x) i) ⊗ₜ[R] π₀ (Pi.single i 1)
      map_add' := fun x y => by
        simp only [map_add, Matrix.mulVec_add, Pi.add_apply, TensorProduct.add_tmul,
          Finset.sum_add_distrib]
      map_smul' := fun p x => by
        simp only [map_smul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
          Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [TensorProduct.smul_tmul']
        rfl }
  let _ : Module R P := Module.compHom P Polynomial.C
  have _ : IsScalarTower R (Polynomial R) P :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let invF : (Polynomial R ⊗[R] M) →ₗ[Polynomial R] P :=
    TensorProduct.AlgebraTensorModule.lift
      { toFun := fun p =>
          { toFun := fun m => π (p • (V *ᵥ (fun j => Polynomial.C (m.1 j))))
            map_add' := fun m₁ m₂ => by
              have hC : (fun j => Polynomial.C ((m₁ + m₂).1 j)) =
                  (fun j => Polynomial.C (m₁.1 j)) + (fun j => Polynomial.C (m₂.1 j)) := by
                funext j; change Polynomial.C (m₁.1 j + m₂.1 j) = _; exact map_add Polynomial.C _ _
              rw [hC, Matrix.mulVec_add, smul_add, map_add]
            map_smul' := fun r m => by
              have hC : (fun j => Polynomial.C ((r • m).1 j)) =
                  Polynomial.C r • (fun j => Polynomial.C (m.1 j)) := by
                funext j; change Polynomial.C (r * m.1 j) = Polynomial.C r * Polynomial.C (m.1 j)
                exact map_mul Polynomial.C r (m.1 j)
              rw [hC, Matrix.mulVec_smul, smul_comm, map_smul]
              rfl }
        map_add' := fun p q => by apply LinearMap.ext; intro m; simp [add_smul, map_add]
        map_smul' := fun a p => by
          apply LinearMap.ext; intro m; change π ((a * p) • _) = a • π (p • _)
          rw [mul_smul, map_smul] }
  refine ⟨M, inferInstance, inferInstance, hMfin, hMproj, ⟨LinearEquiv.ofLinearMap toF invF ?_ ?_⟩⟩
  · apply LinearMap.ext; intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul p m =>
      change toF (π (p • (V *ᵥ (fun j => Polynomial.C (m.1 j))))) = p ⊗ₜ[R] m
      have hvec : U *ᵥ ι (π (p • (V *ᵥ (fun j => Polynomial.C (m.1 j))))) =
          p • (fun j => Polynomial.C (m.1 j)) := by
        rw [← hE_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
          Matrix.mulVec_mulVec, hUE, h3]
        congr 1
        obtain ⟨v, hv⟩ := m.2
        funext i
        have hm_eq : e *ᵥ m.1 = m.1 := by
          rw [← hv]
          change e *ᵥ (e *ᵥ v) = e *ᵥ v
          rw [Matrix.mulVec_mulVec, he]
        calc (eX *ᵥ (fun j => Polynomial.C (m.1 j))) i
            = ∑ j : Fin k, Polynomial.C (e i j) * Polynomial.C (m.1 j) := rfl
          _ = Polynomial.C (∑ j : Fin k, e i j * m.1 j) := by simp [map_sum, map_mul]
          _ = Polynomial.C ((e *ᵥ m.1) i) := rfl
          _ = Polynomial.C (m.1 i) := by rw [hm_eq]
      dsimp only [toF, LinearMap.coe_mk, AddHom.coe_mk]
      rw [hvec]
      calc ∑ i : Fin k, (p * Polynomial.C (m.1 i)) ⊗ₜ[R] π₀ (Pi.single i 1)
          = ∑ i : Fin k, p ⊗ₜ[R] (m.1 i • π₀ (Pi.single i 1)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_comm]
            rfl
        _ = p ⊗ₜ[R] (∑ i : Fin k, m.1 i • π₀ (Pi.single i 1)) := by rw [TensorProduct.tmul_sum]
        _ = p ⊗ₜ[R] π₀ (∑ i : Fin k, m.1 i • Pi.single i 1) := by simp [map_sum, map_smul]
        _ = p ⊗ₜ[R] m := by
          congr 1
          have hsum : (∑ i : Fin k, m.1 i • Pi.single i (1 : R)) = m.1 := by
            ext j; simp [Finset.sum_apply, Pi.single_apply]
          rw [hsum]
          exact LinearMap.congr_fun hπ₀ι₀ m
    | add x y ihx ihy => simp [map_add, ihx, ihy]
  · apply LinearMap.ext; intro x
    change invF (∑ i : Fin k, ((U *ᵥ ι x) i) ⊗ₜ[R] π₀ (Pi.single i 1)) = x
    rw [map_sum]
    have hterm : ∀ i : Fin k, invF (((U *ᵥ ι x) i) ⊗ₜ[R] π₀ (Pi.single i 1)) =
        π ((U *ᵥ ι x) i • (V *ᵥ fun j => Polynomial.C ((π₀ (Pi.single i 1)).1 j))) := fun _ => rfl
    simp_rw [hterm]
    rw [← map_sum]
    have hsum : (∑ i : Fin k, (U *ᵥ ι x) i • (V *ᵥ fun j => Polynomial.C ((π₀ (Pi.single i 1)).1 j))) =
        E *ᵥ ι x := by
      funext r
      have hcol : ∀ i j : Fin k, Polynomial.C ((π₀ (Pi.single i 1)).1 j) = eX j i := by
        intro i j
        change Polynomial.C ((e *ᵥ Pi.single i 1) j) = Polynomial.C (e j i)
        congr 1
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, hcol]
      calc ∑ i : Fin k, (U *ᵥ ι x) i * ∑ j : Fin k, V r j * eX j i
          = ∑ j : Fin k, V r j * ∑ i : Fin k, eX j i * (U *ᵥ ι x) i := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
        _ = (V *ᵥ (eX *ᵥ (U *ᵥ ι x))) r := rfl
        _ = ((V * (eX * U)) *ᵥ ι x) r := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = (E *ᵥ ι x) r := by rw [heXU, h4]
    rw [hsum, hE_mulVec]
    have h1 := LinearMap.congr_fun hπι x
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
    rw [h1, h1]

section PatchingFinale

private lemma evalRingHom_zero_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (p : Polynomial R) :
    Polynomial.evalRingHom 0 (p.map f) = f (Polynomial.evalRingHom 0 p) := by
  change Polynomial.eval 0 (p.map f) = f (Polynomial.eval 0 p)
  rw [Polynomial.eval_map, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero]

private lemma idem_transition_props {α : Type*} [Ring α] {e E u₁ v₁ u₂ v₂ : α}
    (he : e * e = e)
    (hu₁e : e * u₁ = u₁) (hu₁E : u₁ * E = u₁) (hv₁E : E * v₁ = v₁) (hv₁e : v₁ * e = v₁)
    (hu₂e : e * u₂ = u₂) (hu₂E : u₂ * E = u₂) (_hv₂E : E * v₂ = v₂) (hv₂e : v₂ * e = v₂)
    (huv₁ : u₁ * v₁ = e) (hvu₁ : v₁ * u₁ = E) (huv₂ : u₂ * v₂ = e) (hvu₂ : v₂ * u₂ = E) :
    let A := 1 - e + u₁ * v₂
    let B := 1 - e + u₂ * v₁
    A * B = 1 ∧ B * A = 1 ∧
    A = 1 - e + e * A * e ∧ B = 1 - e + e * B * e ∧
    A * u₂ = u₁ ∧ v₂ * B = v₁ := by
  have h1e_sq : (1 - e) * (1 - e) = 1 - e := by
    calc (1 - e) * (1 - e) = 1 - 2 * e + e * e := by noncomm_ring
      _ = 1 - e := by rw [he]; noncomm_ring
  have h1e_e : (1 - e) * e = 0 := by
    calc (1 - e) * e = e - e * e := by noncomm_ring
      _ = 0 := by rw [he, sub_self]
  have he_1e : e * (1 - e) = 0 := by
    calc e * (1 - e) = e - e * e := by noncomm_ring
      _ = 0 := by rw [he, sub_self]
  have h1e_u₂ : (1 - e) * u₂ = 0 := by rw [← hu₂e, ← mul_assoc, h1e_e, zero_mul]
  have h1e_u₁ : (1 - e) * u₁ = 0 := by rw [← hu₁e, ← mul_assoc, h1e_e, zero_mul]
  have hv₂_1e : v₂ * (1 - e) = 0 := by rw [← hv₂e, mul_assoc, he_1e, mul_zero]
  have hv₁_1e : v₁ * (1 - e) = 0 := by rw [← hv₁e, mul_assoc, he_1e, mul_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc (1 - e + u₁ * v₂) * (1 - e + u₂ * v₁)
        = (1 - e) * (1 - e) + ((1 - e) * u₂) * v₁ + u₁ * (v₂ * (1 - e)) +
            u₁ * (v₂ * u₂) * v₁ := by noncomm_ring
      _ = (1 - e) + 0 + 0 + u₁ * E * v₁ := by rw [h1e_sq, h1e_u₂, zero_mul, hv₂_1e, mul_zero, hvu₂]
      _ = (1 - e) + e := by rw [hu₁E, huv₁, add_zero, add_zero]
      _ = 1 := by abel
  · calc (1 - e + u₂ * v₁) * (1 - e + u₁ * v₂)
        = (1 - e) * (1 - e) + ((1 - e) * u₁) * v₂ + u₂ * (v₁ * (1 - e)) +
            u₂ * (v₁ * u₁) * v₂ := by noncomm_ring
      _ = (1 - e) + 0 + 0 + u₂ * E * v₂ := by rw [h1e_sq, h1e_u₁, zero_mul, hv₁_1e, mul_zero, hvu₁]
      _ = (1 - e) + e := by rw [hu₂E, huv₂, add_zero, add_zero]
      _ = 1 := by abel
  · have heAe : e * (1 - e + u₁ * v₂) * e = u₁ * v₂ := by
      calc e * (1 - e + u₁ * v₂) * e = (e * (1 - e)) * e + (e * u₁) * (v₂ * e) := by noncomm_ring
        _ = u₁ * v₂ := by rw [he_1e, zero_mul, zero_add, hu₁e, hv₂e]
    rw [heAe]
  · have heBe : e * (1 - e + u₂ * v₁) * e = u₂ * v₁ := by
      calc e * (1 - e + u₂ * v₁) * e = (e * (1 - e)) * e + (e * u₂) * (v₁ * e) := by noncomm_ring
        _ = u₂ * v₁ := by rw [he_1e, zero_mul, zero_add, hu₂e, hv₁e]
    rw [heBe]
  · calc (1 - e + u₁ * v₂) * u₂ = (1 - e) * u₂ + u₁ * (v₂ * u₂) := by noncomm_ring
      _ = u₁ := by rw [h1e_u₂, zero_add, hvu₂, hu₁E]
  · calc v₂ * (1 - e + u₂ * v₁) = v₂ * (1 - e) + (v₂ * u₂) * v₁ := by noncomm_ring
      _ = v₁ := by rw [hv₂_1e, zero_add, hvu₂, hv₁E]

private lemma idem_sides {α : Type*} [Ring α] {e E U V : α} (he : e * e = e) (hE : E * E = E)
    (h1 : e * U * E = U) (h2 : E * V * e = V) :
    e * U = U ∧ U * E = U ∧ E * V = V ∧ V * e = V := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc e * U = e * (e * U * E) := by rw [h1]
      _ = (e * e) * U * E := by noncomm_ring
      _ = U := by rw [he, h1]
  · calc U * E = (e * U * E) * E := by rw [h1]
      _ = e * U * (E * E) := by noncomm_ring
      _ = U := by rw [hE, h1]
  · calc E * V = E * (E * V * e) := by rw [h2]
      _ = (E * E) * V * e := by noncomm_ring
      _ = V := by rw [hE, h2]
  · calc V * e = (E * V * e) * e := by rw [h2]
      _ = E * V * (e * e) := by noncomm_ring
      _ = V := by rw [he, h2]

private lemma matIsoOver_glue_of_split {R : Type*} [CommRing R] {f g : R} (hcop : IsCoprime f g)
    {k : ℕ} (E : Matrix (Fin k) (Fin k) (Polynomial R)) (hE : E * E = E)
    (Uf Vf A₁ B₁ : Matrix (Fin k) (Fin k) (Polynomial (Localization.Away f)))
    (Ug Vg A₂ B₂ : Matrix (Fin k) (Fin k) (Polynomial (Localization.Away g)))
    (hUf1 : (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp (algebraMap R (Localization.Away f))) *
      Uf * E.map (Polynomial.mapRingHom (algebraMap R (Localization.Away f))) = Uf)
    (hVf1 : E.map (Polynomial.mapRingHom (algebraMap R (Localization.Away f))) * Vf *
      (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp (algebraMap R (Localization.Away f))) = Vf)
    (hUfVf : Uf * Vf = (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp (algebraMap R (Localization.Away f))))
    (hVfUf : Vf * Uf = E.map (Polynomial.mapRingHom (algebraMap R (Localization.Away f))))
    (hUg1 : (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp (algebraMap R (Localization.Away g))) *
      Ug * E.map (Polynomial.mapRingHom (algebraMap R (Localization.Away g))) = Ug)
    (hVg1 : E.map (Polynomial.mapRingHom (algebraMap R (Localization.Away g))) * Vg *
      (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp (algebraMap R (Localization.Away g))) = Vg)
    (hUgVg : Ug * Vg = (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp (algebraMap R (Localization.Away g))))
    (hVgUg : Vg * Ug = E.map (Polynomial.mapRingHom (algebraMap R (Localization.Away g))))
    (hA₁B₁ : A₁ * B₁ = 1) (hB₁A₁ : B₁ * A₁ = 1)
    (hA₂B₂ : A₂ * B₂ = 1) (hB₂A₂ : B₂ * A₂ = 1)
    (hA₁e : let ef := (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp (algebraMap R (Localization.Away f)));
      A₁ = 1 - ef + ef * A₁ * ef)
    (hB₁e : let ef := (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp (algebraMap R (Localization.Away f)));
      B₁ = 1 - ef + ef * B₁ * ef)
    (hA₂e : let eg := (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp (algebraMap R (Localization.Away g)));
      A₂ = 1 - eg + eg * A₂ * eg)
    (hB₂e : let eg := (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp (algebraMap R (Localization.Away g)));
      B₂ = 1 - eg + eg * B₂ * eg)
    (hU_eq : (B₁ * Uf).map (Polynomial.mapRingHom (IsLocalization.Away.awayToAwayRight f g (P := Localization.Away (f * g)))) =
      (A₂ * Ug).map (Polynomial.mapRingHom (IsLocalization.Away.awayToAwayLeft g f (P := Localization.Away (f * g)))))
    (hV_eq : (Vf * A₁).map (Polynomial.mapRingHom (IsLocalization.Away.awayToAwayRight f g (P := Localization.Away (f * g)))) =
      (Vg * B₂).map (Polynomial.mapRingHom (IsLocalization.Away.awayToAwayLeft g f (P := Localization.Away (f * g))))) :
    MatIsoOver (RingHom.id R) E := by
  let Rf := Localization.Away f
  let Rg := Localization.Away g
  let φf : R →+* Rf := algebraMap R Rf
  let φg : R →+* Rg := algebraMap R Rg
  let φfX := Polynomial.mapRingHom φf
  let φgX := Polynomial.mapRingHom φg
  let e_mat : Matrix (Fin k) (Fin k) R := E.map (Polynomial.evalRingHom 0)
  have he_mat : e_mat * e_mat = e_mat := by
    have := congrArg (fun M => M.map (Polynomial.evalRingHom 0)) hE
    rwa [matrix_map_mul] at this
  let ef := e_mat.map (Polynomial.C.comp φf)
  let eg := e_mat.map (Polynomial.C.comp φg)
  let Ef := E.map φfX
  let Eg := E.map φgX
  have hef_idem : ef * ef = ef := by
    have := congrArg (fun M => M.map (Polynomial.C.comp φf)) he_mat
    rwa [matrix_map_mul] at this
  have heg_idem : eg * eg = eg := by
    have := congrArg (fun M => M.map (Polynomial.C.comp φg)) he_mat
    rwa [matrix_map_mul] at this
  change ef * Uf * Ef = Uf at hUf1
  change Ef * Vf * ef = Vf at hVf1
  change Uf * Vf = ef at hUfVf
  change Vf * Uf = Ef at hVfUf
  change eg * Ug * Eg = Ug at hUg1
  change Eg * Vg * eg = Vg at hVg1
  change Ug * Vg = eg at hUgVg
  change Vg * Ug = Eg at hVgUg
  let U₁ := B₁ * Uf
  let V₁ := Vf * A₁
  let U₂ := A₂ * Ug
  let V₂ := Vg * B₂
  obtain ⟨U, hUf_map, hUg_map⟩ := mat_poly_zariski_glue hcop U₁ U₂ hU_eq
  obtain ⟨V, hVf_map, hVg_map⟩ := mat_poly_zariski_glue hcop V₁ V₂ hV_eq
  change U.map φfX = U₁ at hUf_map
  change U.map φgX = U₂ at hUg_map
  change V.map φfX = V₁ at hVf_map
  change V.map φgX = V₂ at hVg_map
  have hB₁c : ef * B₁ = B₁ * ef := (idem_comm_and_fix hef_idem hB₁e).1
  have hA₁c : ef * A₁ = A₁ * ef := (idem_comm_and_fix hef_idem hA₁e).1
  have hA₂c : eg * A₂ = A₂ * eg := (idem_comm_and_fix heg_idem hA₂e).1
  have hB₂c : eg * B₂ = B₂ * eg := (idem_comm_and_fix heg_idem hB₂e).1
  have hU₁1 : ef * U₁ * Ef = U₁ := by
    calc ef * (B₁ * Uf) * Ef = (ef * B₁) * Uf * Ef := by simp only [Matrix.mul_assoc]
      _ = B₁ * (ef * Uf * Ef) := by rw [hB₁c]; simp only [Matrix.mul_assoc]
      _ = B₁ * Uf := by rw [hUf1]
  have hV₁1 : Ef * V₁ * ef = V₁ := by
    calc Ef * (Vf * A₁) * ef = Ef * Vf * (A₁ * ef) := by simp only [Matrix.mul_assoc]
      _ = (Ef * Vf * ef) * A₁ := by rw [← hA₁c]; simp only [Matrix.mul_assoc]
      _ = Vf * A₁ := by rw [hVf1]
  have hU₁V₁ : U₁ * V₁ = ef := by
    calc (B₁ * Uf) * (Vf * A₁) = B₁ * (Uf * Vf) * A₁ := by simp only [Matrix.mul_assoc]
      _ = B₁ * (ef * A₁) := by rw [hUfVf]; simp only [Matrix.mul_assoc]
      _ = (B₁ * A₁) * ef := by rw [hA₁c]; simp only [Matrix.mul_assoc]
      _ = ef := by rw [hB₁A₁, one_mul]
  have hV₁U₁ : V₁ * U₁ = Ef := by
    calc (Vf * A₁) * (B₁ * Uf) = Vf * (A₁ * B₁) * Uf := by simp only [Matrix.mul_assoc]
      _ = Ef := by rw [hA₁B₁, mul_one, hVfUf]
  have hU₂1 : eg * U₂ * Eg = U₂ := by
    calc eg * (A₂ * Ug) * Eg = (eg * A₂) * Ug * Eg := by simp only [Matrix.mul_assoc]
      _ = A₂ * (eg * Ug * Eg) := by rw [hA₂c]; simp only [Matrix.mul_assoc]
      _ = A₂ * Ug := by rw [hUg1]
  have hV₂1 : Eg * V₂ * eg = V₂ := by
    calc Eg * (Vg * B₂) * eg = Eg * Vg * (B₂ * eg) := by simp only [Matrix.mul_assoc]
      _ = (Eg * Vg * eg) * B₂ := by rw [← hB₂c]; simp only [Matrix.mul_assoc]
      _ = Vg * B₂ := by rw [hVg1]
  have hU₂V₂ : U₂ * V₂ = eg := by
    calc (A₂ * Ug) * (Vg * B₂) = A₂ * (Ug * Vg) * B₂ := by simp only [Matrix.mul_assoc]
      _ = A₂ * (eg * B₂) := by rw [hUgVg]; simp only [Matrix.mul_assoc]
      _ = (A₂ * B₂) * eg := by rw [hB₂c]; simp only [Matrix.mul_assoc]
      _ = eg := by rw [hA₂B₂, one_mul]
  have hV₂U₂ : V₂ * U₂ = Eg := by
    calc (Vg * B₂) * (A₂ * Ug) = Vg * (B₂ * A₂) * Ug := by simp only [Matrix.mul_assoc]
      _ = Eg := by rw [hB₂A₂, mul_one, hVgUg]
  let eR := e_mat.map (Polynomial.C.comp (RingHom.id R))
  let ER := E.map (Polynomial.mapRingHom (RingHom.id R))
  have hER_f : ER.map φfX = Ef := by
    apply Matrix.ext; intro i j; simp [ER, Ef, φfX]
  have hER_g : ER.map φgX = Eg := by
    apply Matrix.ext; intro i j; simp [ER, Eg, φgX]
  have heR_f : eR.map φfX = ef := by
    apply Matrix.ext; intro i j; simp [eR, ef, φfX]
  have heR_g : eR.map φgX = eg := by
    apply Matrix.ext; intro i j; simp [eR, eg, φgX]
  have hmat_sub_f : ∀ (X Y : Matrix (Fin k) (Fin k) (Polynomial R)),
      (X - Y).map φfX = X.map φfX - Y.map φfX :=
    fun X Y => Matrix.ext fun i j => map_sub φfX _ _
  have hmat_sub_g : ∀ (X Y : Matrix (Fin k) (Fin k) (Polynomial R)),
      (X - Y).map φgX = X.map φgX - Y.map φgX :=
    fun X Y => Matrix.ext fun i j => map_sub φgX _ _
  refine ⟨U, V, ?_, ?_, ?_, ?_⟩
  · change eR * U * ER = U
    apply sub_eq_zero.mp
    refine mat_poly_zariski_injective hcop ?_ ?_
    · change (eR * U * ER - U).map φfX = 0
      rw [hmat_sub_f, matrix_map_mul, matrix_map_mul, heR_f, hUf_map, hER_f, hU₁1, sub_self]
    · change (eR * U * ER - U).map φgX = 0
      rw [hmat_sub_g, matrix_map_mul, matrix_map_mul, heR_g, hUg_map, hER_g, hU₂1, sub_self]
  · change ER * V * eR = V
    apply sub_eq_zero.mp
    refine mat_poly_zariski_injective hcop ?_ ?_
    · change (ER * V * eR - V).map φfX = 0
      rw [hmat_sub_f, matrix_map_mul, matrix_map_mul, hER_f, hVf_map, heR_f, hV₁1, sub_self]
    · change (ER * V * eR - V).map φgX = 0
      rw [hmat_sub_g, matrix_map_mul, matrix_map_mul, hER_g, hVg_map, heR_g, hV₂1, sub_self]
  · change U * V = eR
    apply sub_eq_zero.mp
    refine mat_poly_zariski_injective hcop ?_ ?_
    · change (U * V - eR).map φfX = 0
      rw [hmat_sub_f, matrix_map_mul, hUf_map, hVf_map, heR_f, hU₁V₁, sub_self]
    · change (U * V - eR).map φgX = 0
      rw [hmat_sub_g, matrix_map_mul, hUg_map, hVg_map, heR_g, hU₂V₂, sub_self]
  · change V * U = ER
    apply sub_eq_zero.mp
    refine mat_poly_zariski_injective hcop ?_ ?_
    · change (V * U - ER).map φfX = 0
      rw [hmat_sub_f, matrix_map_mul, hVf_map, hUf_map, hER_f, hV₁U₁, sub_self]
    · change (V * U - ER).map φgX = 0
      rw [hmat_sub_g, matrix_map_mul, hVg_map, hUg_map, hER_g, hV₂U₂, sub_self]

private lemma eval0_transition_one {S : Type*} [CommRing S] {k : ℕ}
    {e0 : Matrix (Fin k) (Fin k) S} (he0 : e0 * e0 = e0)
    {U V : Matrix (Fin k) (Fin k) (Polynomial S)}
    (hU : U.map (Polynomial.evalRingHom 0) = e0)
    (hV : V.map (Polynomial.evalRingHom 0) = e0) :
    (1 - e0.map Polynomial.C + U * V).map (Polynomial.evalRingHom 0) = 1 := by
  have heC : (e0.map Polynomial.C).map (Polynomial.evalRingHom 0) = e0 := by
    apply Matrix.ext; intro i j; simp
  have hadd : (1 - e0.map Polynomial.C + U * V).map (Polynomial.evalRingHom 0) =
      (1 - e0.map Polynomial.C).map (Polynomial.evalRingHom 0) +
        (U * V).map (Polynomial.evalRingHom 0) :=
    Matrix.ext fun i j => map_add (Polynomial.evalRingHom 0) _ _
  rw [hadd, matrix_map_one_sub (f := Polynomial.evalRingHom (0 : S)) (by simp)
    (fun _ _ => by simp), matrix_map_mul, heC, hU, hV, he0]
  abel

private lemma matIsoOver_of_coprime {R : Type*} [CommRing R] {f g : R} (hcop : IsCoprime f g)
    {k : ℕ} (E : Matrix (Fin k) (Fin k) (Polynomial R)) (hE : E * E = E)
    (hf : MatIsoOver (algebraMap R (Localization.Away f)) E)
    (hg : MatIsoOver (algebraMap R (Localization.Away g)) E) :
    MatIsoOver (RingHom.id R) E := by
  let Rf := Localization.Away f
  let Rg := Localization.Away g
  let Rfg := Localization.Away (f * g)
  let φf : R →+* Rf := algebraMap R Rf
  let φg : R →+* Rg := algebraMap R Rg
  let φfg : R →+* Rfg := algebraMap R Rfg
  let ιf : Rf →+* Rfg := IsLocalization.Away.awayToAwayRight f g
  let ιg : Rg →+* Rfg := IsLocalization.Away.awayToAwayLeft g f
  let φfX := Polynomial.mapRingHom φf
  let φgX := Polynomial.mapRingHom φg
  let φfgX := Polynomial.mapRingHom φfg
  let ιfX := Polynomial.mapRingHom ιf
  let ιgX := Polynomial.mapRingHom ιg
  let e_mat : Matrix (Fin k) (Fin k) R := E.map (Polynomial.evalRingHom 0)
  have he_mat : e_mat * e_mat = e_mat := by
    have := congrArg (fun M => M.map (Polynomial.evalRingHom 0)) hE
    rwa [matrix_map_mul] at this
  let ef := e_mat.map (Polynomial.C.comp φf)
  let eg := e_mat.map (Polynomial.C.comp φg)
  let efg := e_mat.map (Polynomial.C.comp φfg)
  let Ef := E.map φfX
  let Eg := E.map φgX
  let Efg := E.map φfgX
  have hefg_idem : efg * efg = efg := by
    have := congrArg (fun M => M.map (Polynomial.C.comp φfg)) he_mat
    rwa [matrix_map_mul] at this
  have hEfg_idem : Efg * Efg = Efg := by
    have := congrArg (fun M => M.map φfgX) hE
    rwa [matrix_map_mul] at this
  have hEf_ιf : Ef.map ιfX = Efg := by
    apply Matrix.ext; intro i j
    simp only [Ef, Efg, φfX, φfgX, ιfX, Matrix.map_apply, Polynomial.coe_mapRingHom,
      Polynomial.map_map]
    congr 1; ext r; exact IsLocalization.Away.awayToAwayRight_eq (S := Rf) (P := Rfg) f g r
  have hEg_ιg : Eg.map ιgX = Efg := by
    apply Matrix.ext; intro i j
    simp only [Eg, Efg, φgX, φfgX, ιgX, Matrix.map_apply, Polynomial.coe_mapRingHom,
      Polynomial.map_map]
    congr 1; ext r; exact IsLocalization.Away.awayToAwayLeft_eq (S := Rg) (P := Rfg) g f r
  have hef_ιf : ef.map ιfX = efg := by
    apply Matrix.ext; intro i j
    simp only [ef, efg, ιfX, Matrix.map_apply, RingHom.comp_apply, Polynomial.coe_mapRingHom,
      Polynomial.map_C]
    exact congrArg Polynomial.C (IsLocalization.Away.awayToAwayRight_eq (S := Rf) (P := Rfg) f g (e_mat i j))
  have heg_ιg : eg.map ιgX = efg := by
    apply Matrix.ext; intro i j
    simp only [eg, efg, ιgX, Matrix.map_apply, RingHom.comp_apply, Polynomial.coe_mapRingHom,
      Polynomial.map_C]
    exact congrArg Polynomial.C (IsLocalization.Away.awayToAwayLeft_eq (S := Rg) (P := Rfg) g f (e_mat i j))
  obtain ⟨Uf, Vf, hUf1, hVf1, hUfVf, hVfUf, hUf0, _⟩ := matIsoOver_normalize φf hE hf
  obtain ⟨Ug, Vg, hUg1, hVg1, hUgVg, hVgUg, _, hVg0⟩ := matIsoOver_normalize φg hE hg
  change ef * Uf * Ef = Uf at hUf1
  change Ef * Vf * ef = Vf at hVf1
  change Uf * Vf = ef at hUfVf
  change Vf * Uf = Ef at hVfUf
  change eg * Ug * Eg = Ug at hUg1
  change Eg * Vg * eg = Vg at hVg1
  change Ug * Vg = eg at hUgVg
  change Vg * Ug = Eg at hVgUg
  let Uf' := Uf.map ιfX
  let Vf' := Vf.map ιfX
  let Ug' := Ug.map ιgX
  let Vg' := Vg.map ιgX
  have hUf'1 : efg * Uf' * Efg = Uf' := by
    have := congrArg (fun M => M.map ιfX) hUf1
    rwa [matrix_map_mul, matrix_map_mul, hef_ιf, hEf_ιf] at this
  have hVf'1 : Efg * Vf' * efg = Vf' := by
    have := congrArg (fun M => M.map ιfX) hVf1
    rwa [matrix_map_mul, matrix_map_mul, hef_ιf, hEf_ιf] at this
  have hUf'Vf' : Uf' * Vf' = efg := by
    have := congrArg (fun M => M.map ιfX) hUfVf
    rwa [matrix_map_mul, hef_ιf] at this
  have hVf'Uf' : Vf' * Uf' = Efg := by
    have := congrArg (fun M => M.map ιfX) hVfUf
    rwa [matrix_map_mul, hEf_ιf] at this
  have hUg'1 : efg * Ug' * Efg = Ug' := by
    have := congrArg (fun M => M.map ιgX) hUg1
    rwa [matrix_map_mul, matrix_map_mul, heg_ιg, hEg_ιg] at this
  have hVg'1 : Efg * Vg' * efg = Vg' := by
    have := congrArg (fun M => M.map ιgX) hVg1
    rwa [matrix_map_mul, matrix_map_mul, heg_ιg, hEg_ιg] at this
  have hUg'Vg' : Ug' * Vg' = efg := by
    have := congrArg (fun M => M.map ιgX) hUgVg
    rwa [matrix_map_mul, heg_ιg] at this
  have hVg'Ug' : Vg' * Ug' = Efg := by
    have := congrArg (fun M => M.map ιgX) hVgUg
    rwa [matrix_map_mul, hEg_ιg] at this
  obtain ⟨hUf'e, hUf'E, hVf'E, hVf'e⟩ := idem_sides hefg_idem hEfg_idem hUf'1 hVf'1
  obtain ⟨hUg'e, hUg'E, hVg'E, hVg'e⟩ := idem_sides hefg_idem hEfg_idem hUg'1 hVg'1
  let A := 1 - efg + Uf' * Vg'
  let B := 1 - efg + Ug' * Vf'
  obtain ⟨hAB, hBA, hAe, hBe, hAUg', hVg'B⟩ := idem_transition_props hefg_idem
    hUf'e hUf'E hVf'E hVf'e hUg'e hUg'E hVg'E hVg'e hUf'Vf' hVf'Uf' hUg'Vg' hVg'Ug'
  have hA0 : A.map (Polynomial.evalRingHom 0) = 1 := by
    let e0 := e_mat.map φfg
    have he0_idem : e0 * e0 = e0 := by
      have := congrArg (fun M => M.map φfg) he_mat
      rwa [matrix_map_mul] at this
    have hUf'0 : Uf'.map (Polynomial.evalRingHom 0) = e0 := by
      apply Matrix.ext; intro i j
      have h1 : Polynomial.evalRingHom 0 (Uf i j) = φf (e_mat i j) := congrArg (fun M => M i j) hUf0
      change Polynomial.evalRingHom 0 ((Uf i j).map ιf) = φfg (e_mat i j)
      rw [evalRingHom_zero_map, h1]
      exact IsLocalization.Away.awayToAwayRight_eq (S := Rf) (P := Rfg) f g (e_mat i j)
    have hVg'0 : Vg'.map (Polynomial.evalRingHom 0) = e0 := by
      apply Matrix.ext; intro i j
      have h1 : Polynomial.evalRingHom 0 (Vg i j) = φg (e_mat i j) := congrArg (fun M => M i j) hVg0
      change Polynomial.evalRingHom 0 ((Vg i j).map ιg) = φfg (e_mat i j)
      rw [evalRingHom_zero_map, h1]
      exact IsLocalization.Away.awayToAwayLeft_eq (S := Rg) (P := Rfg) g f (e_mat i j)
    have hefg_eq : efg = e0.map Polynomial.C := by apply Matrix.ext; intro i j; rfl
    dsimp only [A]
    rw [hefg_eq]
    exact eval0_transition_one he0_idem hUf'0 hVg'0
  obtain ⟨A₁, B₁, A₂, B₂, hA₁B₁, hB₁A₁, hA₂B₂, hB₂A₂, ⟨hA₁e, hB₁e⟩, ⟨hA₂e, hB₂e⟩, hsplit⟩ :=
    quillen_matrix_split hcop e_mat he_mat A B hAB hBA hA0 hAe hBe
  have hU_eq : (B₁ * Uf).map ιfX = (A₂ * Ug).map ιgX := by
    rw [matrix_map_mul, matrix_map_mul]
    have hB₁A₁' : B₁.map ιfX * A₁.map ιfX = 1 := by
      rw [← matrix_map_mul, hB₁A₁, mat_map_one]
    calc B₁.map ιfX * Uf' = B₁.map ιfX * (A * Ug') := by rw [hAUg']
      _ = B₁.map ιfX * (A₁.map ιfX * A₂.map ιgX * Ug') := by rw [← hsplit]
      _ = (B₁.map ιfX * A₁.map ιfX) * (A₂.map ιgX * Ug') := by simp only [Matrix.mul_assoc]
      _ = A₂.map ιgX * Ug' := by rw [hB₁A₁', one_mul]
  have hV_eq : (Vf * A₁).map ιfX = (Vg * B₂).map ιgX := by
    rw [matrix_map_mul, matrix_map_mul]
    have hA₁B₁' : A₁.map ιfX * B₁.map ιfX = 1 := by
      rw [← matrix_map_mul, hA₁B₁, mat_map_one]
    have hB₁A₁' : B₁.map ιfX * A₁.map ιfX = 1 := by
      rw [← matrix_map_mul, hB₁A₁, mat_map_one]
    have hA₂B₂' : A₂.map ιgX * B₂.map ιgX = 1 := by
      rw [← matrix_map_mul, hA₂B₂, mat_map_one]
    have hB_split : B₂.map ιgX * B₁.map ιfX = B := by
      have hAB' : A * (B₂.map ιgX * B₁.map ιfX) = 1 := by
        rw [← hsplit]
        calc (A₁.map ιfX * A₂.map ιgX) * (B₂.map ιgX * B₁.map ιfX)
            = A₁.map ιfX * (A₂.map ιgX * B₂.map ιgX) * B₁.map ιfX := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hA₂B₂', mul_one, hA₁B₁']
      calc B₂.map ιgX * B₁.map ιfX = (B * A) * (B₂.map ιgX * B₁.map ιfX) := by rw [hBA, one_mul]
        _ = B * (A * (B₂.map ιgX * B₁.map ιfX)) := by simp only [Matrix.mul_assoc]
        _ = B := by rw [hAB', mul_one]
    calc Vf' * A₁.map ιfX = (Vg' * B) * A₁.map ιfX := by rw [hVg'B]
      _ = Vg' * (B₂.map ιgX * B₁.map ιfX) * A₁.map ιfX := by rw [← hB_split]
      _ = Vg' * B₂.map ιgX * (B₁.map ιfX * A₁.map ιfX) := by simp only [Matrix.mul_assoc]
      _ = Vg' * B₂.map ιgX := by rw [hB₁A₁', mul_one]
  exact matIsoOver_glue_of_split hcop E hE Uf Vf A₁ B₁ Ug Vg A₂ B₂
    hUf1 hVf1 hUfVf hVfUf hUg1 hVg1 hUgVg hVgUg hA₁B₁ hB₁A₁ hA₂B₂ hB₂A₂
    hA₁e hB₁e hA₂e hB₂e hU_eq hV_eq

private lemma matIsoOver_add {R : Type*} [CommRing R] {k : ℕ}
    (E : Matrix (Fin k) (Fin k) (Polynomial R)) (hE : E * E = E) {f g : R}
    (hf : MatIsoOver (algebraMap R (Localization.Away f)) E)
    (hg : MatIsoOver (algebraMap R (Localization.Away g)) E) :
    MatIsoOver (algebraMap R (Localization.Away (f + g))) E := by
  let R' := Localization.Away (f + g)
  let φ : R →+* R' := algebraMap R R'
  let E' : Matrix (Fin k) (Fin k) (Polynomial R') := E.map (Polynomial.mapRingHom φ)
  have hE' : E' * E' = E' := by
    have := congrArg (fun M => M.map (Polynomial.mapRingHom φ)) hE
    rwa [matrix_map_mul] at this
  let f' : R' := φ f
  let g' : R' := φ g
  have hcop' : IsCoprime f' g' := by
    have hu : IsUnit (φ (f + g)) := IsLocalization.Away.algebraMap_isUnit (f + g)
    let uinv : R' := ↑(hu.unit⁻¹)
    refine ⟨uinv, uinv, ?_⟩
    have hmul : uinv * φ (f + g) = 1 := by
      change (↑(hu.unit⁻¹) : R') * ↑hu.unit = 1
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hadd : f' + g' = φ (f + g) := (map_add φ f g).symm
    calc uinv * f' + uinv * g' = uinv * (f' + g') := by ring
      _ = uinv * φ (f + g) := by rw [hadd]
      _ = 1 := hmul
  have transport : ∀ {x : R}, MatIsoOver (algebraMap R (Localization.Away x)) E →
      MatIsoOver (algebraMap R' (Localization.Away (φ x))) E' := by
    intro x hx
    let ψ : Localization.Away x →+* Localization.Away (φ x) :=
      (awayAwayEquivRight (f + g) x).symm.toRingHom.comp (IsLocalization.Away.awayToAwayLeft x (f + g))
    have hcomp : ψ.comp (algebraMap R (Localization.Away x)) =
        (algebraMap R' (Localization.Away (φ x))).comp φ := by
      ext r
      change (awayAwayEquivRight (f + g) x).symm
        (IsLocalization.Away.awayToAwayLeft x (f + g) (algebraMap R (Localization.Away x) r)) =
        algebraMap R' (Localization.Away (φ x)) (φ r)
      apply (awayAwayEquivRight (f + g) x).injective
      rw [RingEquiv.apply_symm_apply, IsLocalization.Away.awayToAwayLeft_eq,
        awayAwayEquivRight_algebraMap, IsLocalization.Away.awayToAwayRight_eq]
    have h1 := matIsoOver_map ψ hx
    rw [hcomp] at h1
    obtain ⟨U, V, hu1, hv1, huv, hvu⟩ := h1
    have hE'eq : E'.map (Polynomial.mapRingHom (algebraMap R' (Localization.Away (φ x)))) =
        E.map (Polynomial.mapRingHom ((algebraMap R' (Localization.Away (φ x))).comp φ)) := by
      apply Matrix.ext; intro i j; simp [E', Polynomial.map_map]
    have he'eq : (E'.map (Polynomial.evalRingHom 0)).map
        (Polynomial.C.comp (algebraMap R' (Localization.Away (φ x)))) =
        (E.map (Polynomial.evalRingHom 0)).map
        (Polynomial.C.comp ((algebraMap R' (Localization.Away (φ x))).comp φ)) := by
      apply Matrix.ext; intro i j
      simp only [E', Matrix.map_apply, RingHom.comp_apply]
      congr 1
      change (algebraMap R' (Localization.Away (φ x))) (Polynomial.eval 0 ((E i j).map φ)) =
        (algebraMap R' (Localization.Away (φ x))) (φ (Polynomial.eval 0 (E i j)))
      congr 1
      rw [Polynomial.eval_map, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero]
    refine ⟨U, V, ?_, ?_, ?_, ?_⟩
    · rw [hE'eq, he'eq]; exact hu1
    · rw [hE'eq, he'eq]; exact hv1
    · rw [he'eq]; exact huv
    · rw [hE'eq]; exact hvu
  have hR' := matIsoOver_of_coprime hcop' E' hE' (transport hf) (transport hg)
  obtain ⟨U, V, hu1, hv1, huv, hvu⟩ := hR'
  have hE'id : E'.map (Polynomial.mapRingHom (RingHom.id R')) =
      E.map (Polynomial.mapRingHom (algebraMap R (Localization.Away (f + g)))) := by
    apply Matrix.ext; intro i j; simp [E', φ]; rfl
  have he'id : (E'.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp (RingHom.id R')) =
      (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp (algebraMap R (Localization.Away (f + g)))) := by
    apply Matrix.ext; intro i j
    simp only [E', Matrix.map_apply, RingHom.comp_apply, RingHom.id_apply]
    congr 1
    change Polynomial.eval 0 ((E i j).map φ) = φ (Polynomial.eval 0 (E i j))
    rw [Polynomial.eval_map, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero]
  refine ⟨U, V, ?_, ?_, ?_, ?_⟩
  · rw [hE'id, he'id] at hu1; exact hu1
  · rw [hE'id, he'id] at hv1; exact hv1
  · rw [he'id] at huv; exact huv
  · rw [hE'id] at hvu; exact hvu

private lemma matIsoOver_id_of_local {R : Type*} [CommRing R] {k : ℕ}
    (E : Matrix (Fin k) (Fin k) (Polynomial R)) (hE : E * E = E)
    (hloc : ∀ (m : Ideal R) [m.IsMaximal], MatIsoOver (algebraMap R (Localization.AtPrime m)) E) :
    MatIsoOver (RingHom.id R) E := by
  let I : Ideal R :=
    { carrier := {f : R | MatIsoOver (algebraMap R (Localization.Away f)) E}
      zero_mem' := by
        have h01 : (0 : Localization.Away (0 : R)) = 1 := by
          have hu : IsUnit (algebraMap R (Localization.Away (0 : R)) 0) :=
            IsLocalization.Away.algebraMap_isUnit 0
          rw [map_zero] at hu
          exact isUnit_zero_iff.mp hu
        have _ : Subsingleton (Localization.Away (0 : R)) := subsingleton_of_zero_eq_one h01
        exact matIsoOver_of_subsingleton _ _
      add_mem' := fun hf hg => matIsoOver_add E hE hf hg
      smul_mem' := fun r f hf => by
        have hcomp : (IsLocalization.Away.awayToAwayLeft f r
            (S := Localization.Away f) (P := Localization.Away (r * f))).comp
            (algebraMap R (Localization.Away f)) = algebraMap R (Localization.Away (r * f)) := by
          ext a; exact IsLocalization.Away.awayToAwayLeft_eq f r a
        have h := matIsoOver_map (IsLocalization.Away.awayToAwayLeft f r
          (S := Localization.Away f) (P := Localization.Away (r * f))) hf
        rwa [hcomp] at h }
  have hItop : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm_max, hIm⟩ := Ideal.exists_le_maximal I hne
    have _ : m.IsMaximal := hm_max
    obtain ⟨f, hfm, hfI⟩ := matIsoOver_spread_out m E hE (hloc m)
    exact hfm (hIm hfI)
  have h1 : (1 : R) ∈ I := by rw [hItop]; trivial
  have hu1 : IsUnit ((RingHom.id R) (1 : R)) := by simp
  let ψ : Localization.Away (1 : R) →+* R := IsLocalization.Away.lift (1 : R) hu1
  have hcomp : ψ.comp (algebraMap R (Localization.Away (1 : R))) = RingHom.id R :=
    IsLocalization.Away.lift_comp (1 : R) hu1
  have hres := matIsoOver_map ψ h1
  rwa [hcomp] at hres

end PatchingFinale

lemma univariate_quillen_patching :
    ∀ (R : Type) [CommRing R]
      (P : Type) [AddCommGroup P] [Module (Polynomial R) P]
      [Module.Finite (Polynomial R) P] [Module.Projective (Polynomial R) P],
      (∀ (m : Ideal R) [m.IsMaximal],
        Module.Free (Localization (Algebra.algebraMapSubmonoid (Polynomial R) m.primeCompl))
          (LocalizedModule (Algebra.algebraMapSubmonoid (Polynomial R) m.primeCompl) P)) →
      ∃ (M : Type) (_ : AddCommGroup M) (_ : Module R M),
        Module.Finite R M ∧ Module.Projective R M ∧
        Nonempty (P ≃ₗ[Polynomial R] Polynomial R ⊗[R] M) := by
  intro R _ P _ _ _ _ hloc
  obtain ⟨k, π, ι, _, _, hπι⟩ := Module.Finite.exists_comp_eq_id_of_projective (Polynomial R) P
  let E : Matrix (Fin k) (Fin k) (Polynomial R) := LinearMap.toMatrix' (ι ∘ₗ π)
  have hE : E * E = E := by
    dsimp only [E]
    rw [← LinearMap.toMatrix'_comp]
    congr 1
    apply LinearMap.ext; intro x
    change ι (π (ι (π x))) = ι (π x)
    have := LinearMap.congr_fun hπι (π x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [this]
  have hglobal : MatIsoOver (RingHom.id R) E :=
    matIsoOver_id_of_local E hE fun m _ => matIsoOver_atPrime_of_free P π ι hπι m (hloc m)
  obtain ⟨U, V, h1, h2, h3, h4⟩ := hglobal
  have hEid : E.map (Polynomial.mapRingHom (RingHom.id R)) = E := by
    apply Matrix.ext; intro i j; simp
  have heid : (E.map (Polynomial.evalRingHom 0)).map (Polynomial.C.comp (RingHom.id R)) =
      (E.map (Polynomial.evalRingHom 0)).map Polynomial.C := by
    apply Matrix.ext; intro i j; rfl
  rw [hEid, heid] at h1 h2
  rw [heid] at h3
  rw [hEid] at h4
  exact module_equiv_of_matIsoOver P π ι hπι ⟨U, V, h1, h2, h3, h4⟩

end OMA.H2QuillenPatching

theorem OMA.solution : OMA.R_wp_bass_quillen_conjecture_R1.H2 :=
  OMA.H2QuillenPatching.univariate_quillen_patching
