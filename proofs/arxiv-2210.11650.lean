import OMAStatements.S_arxiv_2210_11650
import Mathlib

namespace OMA.P_arxiv_2210_11650

open OMA.S_arxiv_2210_11650

/-! ### Part 1: Lemma 2.1 of arXiv:2210.11650 — Obstruction to linear soficity -/

private lemma finrank_sup_le_add {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    [Module.Finite F V] (p q : Submodule F V) :
    Module.finrank F ↥(p ⊔ q) ≤ Module.finrank F p + Module.finrank F q := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq p q
  omega

private lemma matrix_rank_add_le' {F : Type*} [Field F] {m : ℕ}
    (A B : Matrix (Fin m) (Fin m) F) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  have hsub : LinearMap.range (A.mulVecLin + B.mulVecLin) ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ v) (LinearMap.mem_range_self _ v)
  exact (Submodule.finrank_mono hsub).trans (finrank_sup_le_add _ _)

private lemma matrix_rank_mul_le_left' {F : Type*} [Field F] {m : ℕ}
    (A B : Matrix (Fin m) (Fin m) F) : (A * B).rank ≤ A.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_mul]
  exact Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)

/-- Core finite-dimensional linear algebra inequality (Claim + conclusion of Lemma 2.1):
given `n × n` matrices `X, Y, Z, A, B` over a field `F`, with
`T := X - Y * X * A` and `S := Z - X * B`, we have
`rk(Z) + rk(X) ≤ rk(X) + rk(S) + rk(Y * Z) + rk(T)` — wait, even cleaner:
`rk(Z) ≤ rk(S) + rk(Y * Z) + rk(T)`!
Wait: check that!!
1. `Z = X * B + S` ⟹ `Im(Z) ≤ Im(X) ⊔ Im(S)` ⟹ `dim(Im(Z) ⊓ Im(X)) + rk(S) ≥ rk(Z)`.
2. Pick a complement `W` of `Im(Z) ⊓ Im(X)` in `Im(X)`, so `dim W = rk(X) - dim(Im(Z) ⊓ Im(X))`.
3. `Y(Im(X)) ≤ Y(Im(Z) ⊓ Im(X)) ⊔ Y(W) ≤ Im(Y * Z) ⊔ Y(W)`, so
   `rk(Y * X) ≤ rk(Y * Z) + dim W = rk(Y * Z) + rk(X) - dim(Im(Z) ⊓ Im(X))`
   `≤ rk(Y * Z) + rk(X) - rk(Z) + rk(S)`!
4. `X = Y * X * A + T` ⟹ `rk(X) ≤ rk(Y * X) + rk(T)`.
5. Combining (3) and (4): **`rk(Z) ≤ rk(S) + rk(Y * Z) + rk(T)`**!!
WHOA!! `rk(X)` CANCELS OUT COMPLETELY!! WE DON'T EVEN NEED `α` FOR `rk(X)`!! -/
private lemma rank_obstruction {F : Type*} [Field F] {m : ℕ}
    (X Y Z A B : Matrix (Fin m) (Fin m) F) :
    Z.rank ≤ (Z - X * B).rank + (Y * Z).rank + (X - Y * X * A).rank := by
  set S : Matrix (Fin m) (Fin m) F := Z - X * B
  set T : Matrix (Fin m) (Fin m) F := X - Y * X * A
  -- Step 1: Im(Z) ≤ Im(X) ⊔ Im(S)
  have hZ_sub : LinearMap.range Z.mulVecLin ≤
      LinearMap.range X.mulVecLin ⊔ LinearMap.range S.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    have hZeq : Z = X * B + S := by simp only [S]; abel
    rw [hZeq, Matrix.mulVecLin_add, LinearMap.add_apply, Matrix.mulVecLin_mul, LinearMap.comp_apply]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ (B.mulVecLin v))
      (LinearMap.mem_range_self _ v)
  -- dim(Im(Z)) ≤ dim(Im(Z) ⊓ Im(X)) + dim(Im(S))
  have hstep1 : Z.rank ≤
      Module.finrank F ↥(LinearMap.range Z.mulVecLin ⊓ LinearMap.range X.mulVecLin) + S.rank := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.range Z.mulVecLin) (LinearMap.range X.mulVecLin)
    have hsup_le : LinearMap.range Z.mulVecLin ⊔ LinearMap.range X.mulVecLin ≤
        LinearMap.range X.mulVecLin ⊔ LinearMap.range S.mulVecLin :=
      sup_le hZ_sub le_sup_left
    have h2 : Module.finrank F ↥(LinearMap.range Z.mulVecLin ⊔ LinearMap.range X.mulVecLin) ≤
        X.rank + S.rank :=
      (Submodule.finrank_mono hsup_le).trans (finrank_sup_le_add _ _)
    unfold Matrix.rank at h2 ⊢
    omega
  -- Step 2: rk(Y * X) + dim(Im(Z) ⊓ Im(X)) ≤ rk(Y * Z) + rk(X)
  have hstep2 : (Y * X).rank +
      Module.finrank F ↥(LinearMap.range Z.mulVecLin ⊓ LinearMap.range X.mulVecLin) ≤
      (Y * Z).rank + X.rank := by
    set U : Submodule F (Fin m → F) := LinearMap.range Z.mulVecLin ⊓ LinearMap.range X.mulVecLin
    set V : Submodule F (Fin m → F) := LinearMap.range X.mulVecLin
    have hUV : U ≤ V := inf_le_right
    -- Pull back U to a submodule of V and pick a complement W in V
    let U' : Submodule F V := U.comap V.subtype
    obtain ⟨W', hW'⟩ := Submodule.exists_isCompl U'
    let W : Submodule F (Fin m → F) := W'.map V.subtype
    have hUW_sup : U ⊔ W = V := by
      have hmap : (U' ⊔ W').map V.subtype = (⊤ : Submodule F V).map V.subtype := by
        rw [hW'.sup_eq_top]
      rw [Submodule.map_sup, Submodule.map_top, Submodule.range_subtype] at hmap
      have hUmap : U'.map V.subtype = U := by
        rw [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.mpr hUV]
      rwa [hUmap] at hmap
    have hUW_inf : U ⊓ W = ⊥ := by
      ext v
      simp only [Submodule.mem_inf, Submodule.mem_bot, W, Submodule.mem_map, Submodule.coe_subtype]
      constructor
      · rintro ⟨hvU, ⟨⟨w, hwV⟩, hwW', rfl⟩⟩
        have hwU' : (⟨w, hwV⟩ : V) ∈ U' := hvU
        have hbot : (⟨w, hwV⟩ : V) ∈ U' ⊓ W' := ⟨hwU', hwW'⟩
        rw [hW'.inf_eq_bot, Submodule.mem_bot] at hbot
        exact congrArg Subtype.val hbot
      · rintro rfl
        exact ⟨Submodule.zero_mem U, ⟨0, Submodule.zero_mem W', rfl⟩⟩
    have hdim_sum : Module.finrank F U + Module.finrank F W = X.rank := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq U W
      rw [hUW_sup, hUW_inf, finrank_bot, add_zero] at h
      exact h.symm
    have hYX_range : LinearMap.range (Y * X).mulVecLin = V.map Y.mulVecLin := by
      rw [Matrix.mulVecLin_mul, LinearMap.range_comp]
    have hYZ_range : LinearMap.range (Y * Z).mulVecLin =
        (LinearMap.range Z.mulVecLin).map Y.mulVecLin := by
      rw [Matrix.mulVecLin_mul, LinearMap.range_comp]
    have hmap_le : V.map Y.mulVecLin ≤
        (LinearMap.range Z.mulVecLin).map Y.mulVecLin ⊔ W.map Y.mulVecLin := by
      rw [← hUW_sup, Submodule.map_sup]
      exact sup_le_sup_right (Submodule.map_mono inf_le_left) _
    have hfin_YX : (Y * X).rank ≤ (Y * Z).rank + Module.finrank F (W.map Y.mulVecLin) := by
      unfold Matrix.rank
      rw [hYX_range, hYZ_range]
      exact (Submodule.finrank_mono hmap_le).trans (finrank_sup_le_add _ _)
    have hfin_W : Module.finrank F (W.map Y.mulVecLin) ≤ Module.finrank F W :=
      Submodule.finrank_map_le Y.mulVecLin W
    omega
  -- Step 3: rk(X) ≤ rk(Y * X) + rk(T)
  have hstep3 : X.rank ≤ (Y * X).rank + T.rank := by
    have hXeq : X = (Y * X) * A + T := by simp only [T]; abel
    calc X.rank = ((Y * X) * A + T).rank := by rw [← hXeq]
      _ ≤ ((Y * X) * A).rank + T.rank := matrix_rank_add_le' _ _
      _ ≤ (Y * X).rank + T.rank := Nat.add_le_add_right (matrix_rank_mul_le_left' _ _) _
  omega

/-- Lemma 2.1 of arXiv:2210.11650: any `F`-algebra `A` containing `x, y, z, a, b` with
`z ≠ 0`, `x = y * x * a`, `z = x * b`, and `y * z = 0` is NOT linear sofic. -/
private lemma not_linearSofic_of_witness {F : Type*} [Field F] {A : Type*} [Ring A] [Algebra F A]
    (x y z a b : A) (hz : z ≠ 0) (hx : x = y * x * a) (hzx : z = x * b) (hyz : y * z = 0) :
    ¬ IsLinearSofic F A := by
  rintro ⟨U, n, _, _, hn_pos, Φ, hΦ_inj⟩
  -- Pick a lift φ : A → (∀ k, M_{n_k}(F)) of Φ
  let φ : A → (∀ k : ℕ, Matrix (Fin (n k)) (Fin (n k)) F) :=
    fun u => Quotient.out (Φ u)
  have hφ_mk : ∀ u : A, (rankRingCon F U n).mk' (φ u) = Φ u := fun u => Quotient.out_eq (Φ u)
  -- Since Φ z ≠ Φ 0 = 0, z is not in rankNull!
  have hz_not_null : ¬ rankNull F U n (φ z) := by
    intro hnull
    have hrel : rankRel F U n (φ z) 0 := by
      unfold rankRel; simpa using hnull
    have hq : (rankRingCon F U n).mk' (φ z) = (rankRingCon F U n).mk' 0 :=
      (RingCon.eq (rankRingCon F U n)).mpr hrel
    rw [hφ_mk z, map_zero] at hq
    exact hz (hΦ_inj (hq.trans (map_zero Φ).symm))
  -- Extract ε > 0 such that { k | ε * n_k < rk(φ z k) } ∈ U
  unfold rankNull at hz_not_null
  push Not at hz_not_null
  obtain ⟨ε, hε_pos, hnot_mem⟩ := hz_not_null
  have hgt_mem : { k : ℕ | ε * (n k : ℝ) < ((φ z k).rank : ℝ) } ∈ U := by
    have hcomp := (Ultrafilter.compl_mem_iff_notMem).mpr hnot_mem
    have heq : { k : ℕ | ((φ z k).rank : ℝ) ≤ ε * (n k : ℝ) }ᶜ =
        { k : ℕ | ε * (n k : ℝ) < ((φ z k).rank : ℝ) } := by
      ext k; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
    rwa [heq] at hcomp
  -- Algebraic identities in the quotient give rankNull for the 3 error terms!
  have hS_null : rankNull F U n (φ z - φ x * φ b) := by
    have hq : (rankRingCon F U n).mk' (φ z) = (rankRingCon F U n).mk' (φ x * φ b) := by
      rw [map_mul, hφ_mk z, hφ_mk x, hφ_mk b, ← map_mul, ← hzx]
    exact (RingCon.eq (rankRingCon F U n)).mp hq
  have hYZ_null : rankNull F U n (φ y * φ z) := by
    have hq : (rankRingCon F U n).mk' (φ y * φ z) = (rankRingCon F U n).mk' 0 := by
      rw [map_mul, hφ_mk y, hφ_mk z, ← map_mul, hyz, map_zero, map_zero]
    have hrel : rankNull F U n (φ y * φ z - 0) := (RingCon.eq (rankRingCon F U n)).mp hq
    simpa only [sub_zero] using hrel
  have hT_null : rankNull F U n (φ x - φ y * φ x * φ a) := by
    have hq : (rankRingCon F U n).mk' (φ x) = (rankRingCon F U n).mk' (φ y * φ x * φ a) := by
      rw [map_mul, map_mul, hφ_mk x, hφ_mk y, hφ_mk a, ← map_mul, ← map_mul, ← hx]
    exact (RingCon.eq (rankRingCon F U n)).mp hq
  have hS_mem := hS_null (ε / 4) (by linarith)
  have hYZ_mem := hYZ_null (ε / 4) (by linarith)
  have hT_mem := hT_null (ε / 4) (by linarith)
  have hinter : ({ k : ℕ | ε * (n k : ℝ) < ((φ z k).rank : ℝ) } ∩
      { k : ℕ | (((φ z - φ x * φ b) k).rank : ℝ) ≤ (ε / 4) * (n k : ℝ) } ∩
      { k : ℕ | (((φ y * φ z) k).rank : ℝ) ≤ (ε / 4) * (n k : ℝ) } ∩
      { k : ℕ | (((φ x - φ y * φ x * φ a) k).rank : ℝ) ≤ (ε / 4) * (n k : ℝ) }) ∈ U :=
    Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hgt_mem hS_mem) hYZ_mem) hT_mem
  obtain ⟨k, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩⟩ := U.nonempty_of_mem hinter
  simp only [Set.mem_ofPred_eq, Pi.sub_apply, Pi.mul_apply] at h1 h2 h3 h4
  have hob : ((φ z k).rank : ℝ) ≤
      ((φ z k - φ x k * φ b k).rank : ℝ) + ((φ y k * φ z k).rank : ℝ) +
      ((φ x k - φ y k * φ x k * φ a k).rank : ℝ) := by
    exact_mod_cast rank_obstruction (φ x k) (φ y k) (φ z k) (φ a k) (φ b k)
  have hnk : (0 : ℝ) < (n k : ℝ) := by exact_mod_cast hn_pos k
  nlinarith

/-! ### Part 2: Concrete 3×3 block upper-triangular `F`-algebra `U(F)` and subalgebra `A(F)` -/

/-- The 3×3 block upper-triangular `F`-algebra acting on
`V₁ ⊕ V₂ ⊕ V₃` where `V₁ = ℕ →₀ F`, `V₂ = ℤ →₀ F`, `V₃ = ℕ →₀ F`.
Elements are tuples `(d₁, d₂, d₃, u₁₂, u₂₃, u₁₃)` representing
```
[ d₁  u₁₂  u₁₃ ]
[  0   d₂  u₂₃ ]
[  0    0   d₃ ]
``` -/
private structure TriAlg (F : Type) [Field F] where
  d1 : (ℕ →₀ F) →ₗ[F] (ℕ →₀ F)
  d2 : (ℤ →₀ F) →ₗ[F] (ℤ →₀ F)
  d3 : (ℕ →₀ F) →ₗ[F] (ℕ →₀ F)
  u12 : (ℤ →₀ F) →ₗ[F] (ℕ →₀ F)
  u23 : (ℕ →₀ F) →ₗ[F] (ℤ →₀ F)
  u13 : (ℕ →₀ F) →ₗ[F] (ℕ →₀ F)

private lemma TriAlg.ext {F : Type} [Field F] {a b : TriAlg F}
    (h1 : a.d1 = b.d1) (h2 : a.d2 = b.d2) (h3 : a.d3 = b.d3)
    (h12 : a.u12 = b.u12) (h23 : a.u23 = b.u23) (h13 : a.u13 = b.u13) : a = b := by
  cases a; cases b; congr

private noncomputable instance {F : Type} [Field F] : Zero (TriAlg F) :=
  ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

private noncomputable instance {F : Type} [Field F] : One (TriAlg F) :=
  ⟨⟨LinearMap.id, LinearMap.id, LinearMap.id, 0, 0, 0⟩⟩

private noncomputable instance {F : Type} [Field F] : Add (TriAlg F) :=
  ⟨fun a b => ⟨a.d1 + b.d1, a.d2 + b.d2, a.d3 + b.d3,
               a.u12 + b.u12, a.u23 + b.u23, a.u13 + b.u13⟩⟩

private noncomputable instance {F : Type} [Field F] : Neg (TriAlg F) :=
  ⟨fun a => ⟨-a.d1, -a.d2, -a.d3, -a.u12, -a.u23, -a.u13⟩⟩

private noncomputable instance {F : Type} [Field F] : Sub (TriAlg F) :=
  ⟨fun a b => ⟨a.d1 - b.d1, a.d2 - b.d2, a.d3 - b.d3,
               a.u12 - b.u12, a.u23 - b.u23, a.u13 - b.u13⟩⟩

private noncomputable instance {F : Type} [Field F] : Mul (TriAlg F) :=
  ⟨fun a b => ⟨a.d1.comp b.d1, a.d2.comp b.d2, a.d3.comp b.d3,
               a.d1.comp b.u12 + a.u12.comp b.d2,
               a.d2.comp b.u23 + a.u23.comp b.d3,
               a.d1.comp b.u13 + a.u12.comp b.u23 + a.u13.comp b.d3⟩⟩

private noncomputable instance {F : Type} [Field F] : SMul F (TriAlg F) :=
  ⟨fun c a => ⟨c • a.d1, c • a.d2, c • a.d3, c • a.u12, c • a.u23, c • a.u13⟩⟩

private noncomputable instance {F : Type} [Field F] : Ring (TriAlg F) where
  add_assoc a b c := by
    apply TriAlg.ext
    · exact add_assoc a.d1 b.d1 c.d1
    · exact add_assoc a.d2 b.d2 c.d2
    · exact add_assoc a.d3 b.d3 c.d3
    · exact add_assoc a.u12 b.u12 c.u12
    · exact add_assoc a.u23 b.u23 c.u23
    · exact add_assoc a.u13 b.u13 c.u13
  zero_add a := by
    apply TriAlg.ext
    · exact zero_add a.d1
    · exact zero_add a.d2
    · exact zero_add a.d3
    · exact zero_add a.u12
    · exact zero_add a.u23
    · exact zero_add a.u13
  add_zero a := by
    apply TriAlg.ext
    · exact add_zero a.d1
    · exact add_zero a.d2
    · exact add_zero a.d3
    · exact add_zero a.u12
    · exact add_zero a.u23
    · exact add_zero a.u13
  add_comm a b := by
    apply TriAlg.ext
    · exact add_comm a.d1 b.d1
    · exact add_comm a.d2 b.d2
    · exact add_comm a.d3 b.d3
    · exact add_comm a.u12 b.u12
    · exact add_comm a.u23 b.u23
    · exact add_comm a.u13 b.u13
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by
    apply TriAlg.ext
    · exact neg_add_cancel a.d1
    · exact neg_add_cancel a.d2
    · exact neg_add_cancel a.d3
    · exact neg_add_cancel a.u12
    · exact neg_add_cancel a.u23
    · exact neg_add_cancel a.u13
  sub_eq_add_neg a b := by
    apply TriAlg.ext
    · exact sub_eq_add_neg a.d1 b.d1
    · exact sub_eq_add_neg a.d2 b.d2
    · exact sub_eq_add_neg a.d3 b.d3
    · exact sub_eq_add_neg a.u12 b.u12
    · exact sub_eq_add_neg a.u23 b.u23
    · exact sub_eq_add_neg a.u13 b.u13
  mul_assoc a b c := by
    apply TriAlg.ext
    · exact LinearMap.comp_assoc c.d1 b.d1 a.d1
    · exact LinearMap.comp_assoc c.d2 b.d2 a.d2
    · exact LinearMap.comp_assoc c.d3 b.d3 a.d3
    · change (a.d1.comp b.d1).comp c.u12 + (a.d1.comp b.u12 + a.u12.comp b.d2).comp c.d2 =
        a.d1.comp (b.d1.comp c.u12 + b.u12.comp c.d2) + a.u12.comp (b.d2.comp c.d2)
      simp only [LinearMap.comp_assoc, LinearMap.comp_add, LinearMap.add_comp, add_assoc]
    · change (a.d2.comp b.d2).comp c.u23 + (a.d2.comp b.u23 + a.u23.comp b.d3).comp c.d3 =
        a.d2.comp (b.d2.comp c.u23 + b.u23.comp c.d3) + a.u23.comp (b.d3.comp c.d3)
      simp only [LinearMap.comp_assoc, LinearMap.comp_add, LinearMap.add_comp, add_assoc]
    · change (a.d1.comp b.d1).comp c.u13 + (a.d1.comp b.u12 + a.u12.comp b.d2).comp c.u23 +
          (a.d1.comp b.u13 + a.u12.comp b.u23 + a.u13.comp b.d3).comp c.d3 =
        a.d1.comp (b.d1.comp c.u13 + b.u12.comp c.u23 + b.u13.comp c.d3) +
          a.u12.comp (b.d2.comp c.u23 + b.u23.comp c.d3) + a.u13.comp (b.d3.comp c.d3)
      simp only [LinearMap.comp_assoc, LinearMap.comp_add, LinearMap.add_comp]; abel
  one_mul a := by
    apply TriAlg.ext
    · exact LinearMap.id_comp a.d1
    · exact LinearMap.id_comp a.d2
    · exact LinearMap.id_comp a.d3
    · change LinearMap.id.comp a.u12 + (0 : _ →ₗ[F] _).comp a.d2 = a.u12
      simp only [LinearMap.id_comp, LinearMap.zero_comp, add_zero]
    · change LinearMap.id.comp a.u23 + (0 : _ →ₗ[F] _).comp a.d3 = a.u23
      simp only [LinearMap.id_comp, LinearMap.zero_comp, add_zero]
    · change LinearMap.id.comp a.u13 + (0 : _ →ₗ[F] _).comp a.u23 + (0 : _ →ₗ[F] _).comp a.d3 = a.u13
      simp only [LinearMap.id_comp, LinearMap.zero_comp, add_zero]
  mul_one a := by
    apply TriAlg.ext
    · exact LinearMap.comp_id a.d1
    · exact LinearMap.comp_id a.d2
    · exact LinearMap.comp_id a.d3
    · change a.d1.comp 0 + a.u12.comp LinearMap.id = a.u12
      simp only [LinearMap.comp_id, LinearMap.comp_zero, zero_add]
    · change a.d2.comp 0 + a.u23.comp LinearMap.id = a.u23
      simp only [LinearMap.comp_id, LinearMap.comp_zero, zero_add]
    · change a.d1.comp 0 + a.u12.comp 0 + a.u13.comp LinearMap.id = a.u13
      simp only [LinearMap.comp_id, LinearMap.comp_zero, zero_add]
  left_distrib a b c := by
    apply TriAlg.ext
    · exact LinearMap.comp_add b.d1 c.d1 a.d1
    · exact LinearMap.comp_add b.d2 c.d2 a.d2
    · exact LinearMap.comp_add b.d3 c.d3 a.d3
    · change a.d1.comp (b.u12 + c.u12) + a.u12.comp (b.d2 + c.d2) =
        (a.d1.comp b.u12 + a.u12.comp b.d2) + (a.d1.comp c.u12 + a.u12.comp c.d2)
      simp only [LinearMap.comp_add]; abel
    · change a.d2.comp (b.u23 + c.u23) + a.u23.comp (b.d3 + c.d3) =
        (a.d2.comp b.u23 + a.u23.comp b.d3) + (a.d2.comp c.u23 + a.u23.comp c.d3)
      simp only [LinearMap.comp_add]; abel
    · change a.d1.comp (b.u13 + c.u13) + a.u12.comp (b.u23 + c.u23) + a.u13.comp (b.d3 + c.d3) =
        (a.d1.comp b.u13 + a.u12.comp b.u23 + a.u13.comp b.d3) +
        (a.d1.comp c.u13 + a.u12.comp c.u23 + a.u13.comp c.d3)
      simp only [LinearMap.comp_add]; abel
  right_distrib a b c := by
    apply TriAlg.ext
    · exact LinearMap.add_comp c.d1 b.d1 a.d1
    · exact LinearMap.add_comp c.d2 b.d2 a.d2
    · exact LinearMap.add_comp c.d3 b.d3 a.d3
    · change (a.d1 + b.d1).comp c.u12 + (a.u12 + b.u12).comp c.d2 =
        (a.d1.comp c.u12 + a.u12.comp c.d2) + (b.d1.comp c.u12 + b.u12.comp c.d2)
      simp only [LinearMap.add_comp]; abel
    · change (a.d2 + b.d2).comp c.u23 + (a.u23 + b.u23).comp c.d3 =
        (a.d2.comp c.u23 + a.u23.comp c.d3) + (b.d2.comp c.u23 + b.u23.comp c.d3)
      simp only [LinearMap.add_comp]; abel
    · change (a.d1 + b.d1).comp c.u13 + (a.u12 + b.u12).comp c.u23 + (a.u13 + b.u13).comp c.d3 =
        (a.d1.comp c.u13 + a.u12.comp c.u23 + a.u13.comp c.d3) +
        (b.d1.comp c.u13 + b.u12.comp c.u23 + b.u13.comp c.d3)
      simp only [LinearMap.add_comp]; abel
  zero_mul a := by
    apply TriAlg.ext
    · exact LinearMap.zero_comp a.d1
    · exact LinearMap.zero_comp a.d2
    · exact LinearMap.zero_comp a.d3
    · change (0 : _ →ₗ[F] _).comp a.u12 + (0 : _ →ₗ[F] _).comp a.d2 = 0
      simp only [LinearMap.zero_comp, add_zero]
    · change (0 : _ →ₗ[F] _).comp a.u23 + (0 : _ →ₗ[F] _).comp a.d3 = 0
      simp only [LinearMap.zero_comp, add_zero]
    · change (0 : _ →ₗ[F] _).comp a.u13 + (0 : _ →ₗ[F] _).comp a.u23 + (0 : _ →ₗ[F] _).comp a.d3 = 0
      simp only [LinearMap.zero_comp, add_zero]
  mul_zero a := by
    apply TriAlg.ext
    · exact LinearMap.comp_zero a.d1
    · exact LinearMap.comp_zero a.d2
    · exact LinearMap.comp_zero a.d3
    · change a.d1.comp 0 + a.u12.comp 0 = 0
      simp only [LinearMap.comp_zero, add_zero]
    · change a.d2.comp 0 + a.u23.comp 0 = 0
      simp only [LinearMap.comp_zero, add_zero]
    · change a.d1.comp 0 + a.u12.comp 0 + a.u13.comp 0 = 0
      simp only [LinearMap.comp_zero, add_zero]

private noncomputable instance {F : Type} [Field F] : Algebra F (TriAlg F) where
  smul := (· • ·)
  algebraMap :=
    { toFun := fun c => ⟨c • LinearMap.id, c • LinearMap.id, c • LinearMap.id, 0, 0, 0⟩
      map_one' := by
        apply TriAlg.ext
        · exact one_smul F LinearMap.id
        · exact one_smul F LinearMap.id
        · exact one_smul F LinearMap.id
        · rfl
        · rfl
        · rfl
      map_mul' := fun c d => by
        apply TriAlg.ext
        · change (c * d) • LinearMap.id = (c • LinearMap.id).comp (d • LinearMap.id)
          simp only [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, mul_smul]
          rw [smul_comm]
        · change (c * d) • LinearMap.id = (c • LinearMap.id).comp (d • LinearMap.id)
          simp only [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, mul_smul]
          rw [smul_comm]
        · change (c * d) • LinearMap.id = (c • LinearMap.id).comp (d • LinearMap.id)
          simp only [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, mul_smul]
          rw [smul_comm]
        · change (0 : _ →ₗ[F] _) = (c • LinearMap.id).comp 0 + (0 : _ →ₗ[F] _).comp (d • LinearMap.id)
          simp only [LinearMap.comp_zero, LinearMap.zero_comp, add_zero]
        · change (0 : _ →ₗ[F] _) = (c • LinearMap.id).comp 0 + (0 : _ →ₗ[F] _).comp (d • LinearMap.id)
          simp only [LinearMap.comp_zero, LinearMap.zero_comp, add_zero]
        · change (0 : _ →ₗ[F] _) = (c • LinearMap.id).comp 0 + (0 : _ →ₗ[F] _).comp 0 +
            (0 : _ →ₗ[F] _).comp (d • LinearMap.id)
          simp only [LinearMap.comp_zero, LinearMap.zero_comp, add_zero]
      map_zero' := by
        apply TriAlg.ext
        · exact zero_smul F LinearMap.id
        · exact zero_smul F LinearMap.id
        · exact zero_smul F LinearMap.id
        · rfl
        · rfl
        · rfl
      map_add' := fun c d => by
        apply TriAlg.ext
        · exact add_smul c d LinearMap.id
        · exact add_smul c d LinearMap.id
        · exact add_smul c d LinearMap.id
        · exact (add_zero (0 : _ →ₗ[F] _)).symm
        · exact (add_zero (0 : _ →ₗ[F] _)).symm
        · exact (add_zero (0 : _ →ₗ[F] _)).symm }
  commutes' c a := by
    apply TriAlg.ext
    · change (c • LinearMap.id).comp a.d1 = a.d1.comp (c • LinearMap.id)
      simp only [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, LinearMap.comp_id]
    · change (c • LinearMap.id).comp a.d2 = a.d2.comp (c • LinearMap.id)
      simp only [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, LinearMap.comp_id]
    · change (c • LinearMap.id).comp a.d3 = a.d3.comp (c • LinearMap.id)
      simp only [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, LinearMap.comp_id]
    · change (c • LinearMap.id).comp a.u12 + (0 : _ →ₗ[F] _).comp a.d2 =
        a.d1.comp 0 + a.u12.comp (c • LinearMap.id)
      simp only [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, LinearMap.comp_id,
        LinearMap.zero_comp, LinearMap.comp_zero, add_zero, zero_add]
    · change (c • LinearMap.id).comp a.u23 + (0 : _ →ₗ[F] _).comp a.d3 =
        a.d2.comp 0 + a.u23.comp (c • LinearMap.id)
      simp only [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, LinearMap.comp_id,
        LinearMap.zero_comp, LinearMap.comp_zero, add_zero, zero_add]
    · change (c • LinearMap.id).comp a.u13 + (0 : _ →ₗ[F] _).comp a.u23 + (0 : _ →ₗ[F] _).comp a.d3 =
        a.d1.comp 0 + a.u12.comp 0 + a.u13.comp (c • LinearMap.id)
      simp only [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, LinearMap.comp_id,
        LinearMap.zero_comp, LinearMap.comp_zero, add_zero, zero_add]
  smul_def' c a := by
    apply TriAlg.ext
    · change c • a.d1 = (c • LinearMap.id).comp a.d1
      simp only [LinearMap.smul_comp, LinearMap.id_comp]
    · change c • a.d2 = (c • LinearMap.id).comp a.d2
      simp only [LinearMap.smul_comp, LinearMap.id_comp]
    · change c • a.d3 = (c • LinearMap.id).comp a.d3
      simp only [LinearMap.smul_comp, LinearMap.id_comp]
    · change c • a.u12 = (c • LinearMap.id).comp a.u12 + (0 : _ →ₗ[F] _).comp a.d2
      simp only [LinearMap.smul_comp, LinearMap.id_comp, LinearMap.zero_comp, add_zero]
    · change c • a.u23 = (c • LinearMap.id).comp a.u23 + (0 : _ →ₗ[F] _).comp a.d3
      simp only [LinearMap.smul_comp, LinearMap.id_comp, LinearMap.zero_comp, add_zero]
    · change c • a.u13 = (c • LinearMap.id).comp a.u13 + (0 : _ →ₗ[F] _).comp a.u23 +
        (0 : _ →ₗ[F] _).comp a.d3
      simp only [LinearMap.smul_comp, LinearMap.id_comp, LinearMap.zero_comp, add_zero]

/-- Diagonal projection `π : TriAlg F →+* End(V₁) × End(V₂) × End(V₃)`. -/
private noncomputable def diagHom (F : Type) [Field F] :
    TriAlg F →+* (Module.End F (ℕ →₀ F)) × (Module.End F (ℤ →₀ F)) × (Module.End F (ℕ →₀ F)) where
  toFun a := (a.d1, a.d2, a.d3)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private lemma triAlg_ker_cube_zero {F : Type} [Field F] (a b c : TriAlg F)
    (ha : diagHom F a = 0) (hb : diagHom F b = 0) (hc : diagHom F c = 0) :
    a * b * c = 0 := by
  have ha1 : a.d1 = 0 := congrArg Prod.fst ha
  have ha2 : a.d2 = 0 := congrArg (fun p => p.2.1) ha
  have ha3 : a.d3 = 0 := congrArg (fun p => p.2.2) ha
  have hb1 : b.d1 = 0 := congrArg Prod.fst hb
  have hb2 : b.d2 = 0 := congrArg (fun p => p.2.1) hb
  have hb3 : b.d3 = 0 := congrArg (fun p => p.2.2) hb
  have hc1 : c.d1 = 0 := congrArg Prod.fst hc
  have hc2 : c.d2 = 0 := congrArg (fun p => p.2.1) hc
  have hc3 : c.d3 = 0 := congrArg (fun p => p.2.2) hc
  apply TriAlg.ext
  · change (a.d1.comp b.d1).comp c.d1 = 0
    simp only [ha1, LinearMap.zero_comp]
  · change (a.d2.comp b.d2).comp c.d2 = 0
    simp only [ha2, LinearMap.zero_comp]
  · change (a.d3.comp b.d3).comp c.d3 = 0
    simp only [ha3, LinearMap.zero_comp]
  · change (a.d1.comp b.d1).comp c.u12 + (a.d1.comp b.u12 + a.u12.comp b.d2).comp c.d2 = 0
    simp only [ha1, hb2, hc2, LinearMap.zero_comp, LinearMap.comp_zero, add_zero]
  · change (a.d2.comp b.d2).comp c.u23 + (a.d2.comp b.u23 + a.u23.comp b.d3).comp c.d3 = 0
    simp only [ha2, hb3, hc3, LinearMap.zero_comp, LinearMap.comp_zero, add_zero]
  · change (a.d1.comp b.d1).comp c.u13 + (a.d1.comp b.u12 + a.u12.comp b.d2).comp c.u23 +
      (a.d1.comp b.u13 + a.u12.comp b.u23 + a.u13.comp b.d3).comp c.d3 = 0
    simp only [ha1, hb2, hc3, LinearMap.zero_comp, LinearMap.comp_zero, add_zero]

/-! ### Part 3: The two generators `X_gen` and `Y_gen` -/

private noncomputable def opL (F : Type) [Field F] : (ℕ →₀ F) →ₗ[F] (ℕ →₀ F) :=
  Finsupp.lsum F (fun n : ℕ =>
    match n with
    | 0 => 0
    | m + 1 => LinearMap.toSpanSingleton F (ℕ →₀ F) (Finsupp.single m 1))

private noncomputable def opS (F : Type) [Field F] : (ℤ →₀ F) →ₗ[F] (ℤ →₀ F) :=
  Finsupp.lsum F (fun k : ℤ => LinearMap.toSpanSingleton F (ℤ →₀ F) (Finsupp.single (k + 1) 1))

private noncomputable def opR (F : Type) [Field F] : (ℕ →₀ F) →ₗ[F] (ℕ →₀ F) :=
  Finsupp.lsum F (fun n : ℕ => LinearMap.toSpanSingleton F (ℕ →₀ F) (Finsupp.single (n + 1) 1))

private noncomputable def opA (F : Type) [Field F] : (ℤ →₀ F) →ₗ[F] (ℕ →₀ F) :=
  Finsupp.lsum F (fun k : ℤ =>
    if 0 ≤ k then LinearMap.toSpanSingleton F (ℕ →₀ F) (Finsupp.single k.toNat 1) else 0)

private noncomputable def opB (F : Type) [Field F] : (ℕ →₀ F) →ₗ[F] (ℤ →₀ F) :=
  Finsupp.lsum F (fun n : ℕ =>
    LinearMap.toSpanSingleton F (ℤ →₀ F) (Finsupp.single (-1 - (n : ℤ)) 1))

private lemma opL_single_zero (F : Type) [Field F] : opL F (Finsupp.single 0 1) = 0 := by
  simp [opL]

private lemma opL_single_succ (F : Type) [Field F] (m : ℕ) :
    opL F (Finsupp.single (m + 1) 1) = Finsupp.single m 1 := by
  simp [opL]

private lemma opS_single (F : Type) [Field F] (k : ℤ) :
    opS F (Finsupp.single k 1) = Finsupp.single (k + 1) 1 := by
  simp [opS]

private lemma opR_single (F : Type) [Field F] (n : ℕ) :
    opR F (Finsupp.single n 1) = Finsupp.single (n + 1) 1 := by
  simp [opR]

private lemma opA_single_nonneg (F : Type) [Field F] {k : ℤ} (hk : 0 ≤ k) :
    opA F (Finsupp.single k 1) = Finsupp.single k.toNat 1 := by
  simp [opA, hk]

private lemma opA_single_neg (F : Type) [Field F] {k : ℤ} (hk : k < 0) :
    opA F (Finsupp.single k 1) = 0 := by
  have hnot : ¬ (0 ≤ k) := not_le.mpr hk
  simp [opA, hnot]

private lemma opB_single (F : Type) [Field F] (n : ℕ) :
    opB F (Finsupp.single n 1) = Finsupp.single (-1 - (n : ℤ)) 1 := by
  simp [opB]

private lemma opL_comp_opA_comp_opS (F : Type) [Field F] :
    (opL F).comp ((opA F).comp (opS F)) = opA F := by
  apply Finsupp.lhom_ext'
  intro k
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, opS_single]
  by_cases hk : 0 ≤ k
  · have hk1 : 0 ≤ k + 1 := by omega
    rw [opA_single_nonneg F hk, opA_single_nonneg F hk1]
    have htn : (k + 1).toNat = k.toNat + 1 := by omega
    rw [htn, opL_single_succ]
  · push Not at hk
    rw [opA_single_neg F hk]
    by_cases hk1 : k = -1
    · subst hk1
      have h0 : (0 : ℤ) ≤ -1 + 1 := by omega
      rw [opA_single_nonneg F h0]
      simp [opL_single_zero]
    · have hlt : k + 1 < 0 := by omega
      rw [opA_single_neg F hlt, map_zero]

private lemma opS_comp_opB_comp_opR (F : Type) [Field F] :
    (opS F).comp ((opB F).comp (opR F)) = opB F := by
  apply Finsupp.lhom_ext'
  intro n
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, opR_single, opB_single, opS_single]
  congr 1; push_cast; ring

private lemma opA_comp_opB (F : Type) [Field F] :
    (opA F).comp (opB F) = 0 := by
  apply Finsupp.lhom_ext'
  intro n
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Finsupp.lsingle_apply, opB_single]
  exact opA_single_neg F (by omega)

private lemma opA_comp_opS_comp_opB_ne_zero (F : Type) [Field F] :
    (opA F).comp ((opS F).comp (opB F)) ≠ 0 := by
  intro h
  have h0 := congrArg (fun f => f (Finsupp.single 0 1)) h
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, opB_single, Nat.cast_zero, sub_zero,
    opS_single, neg_add_cancel] at h0
  rw [opA_single_nonneg F (le_refl 0)] at h0
  have h1 := congrArg (fun v : ℕ →₀ F => v 0) h0
  simp at h1

private noncomputable def Y_gen (F : Type) [Field F] : TriAlg F :=
  ⟨opL F, opS F, opR F, 0, 0, 0⟩

private noncomputable def X_gen (F : Type) [Field F] : TriAlg F :=
  ⟨0, 0, 0, opA F, opB F, 0⟩

private lemma YXY_eq_X (F : Type) [Field F] :
    Y_gen F * X_gen F * Y_gen F = X_gen F := by
  have hYX : Y_gen F * X_gen F = ⟨0, 0, 0, (opL F).comp (opA F), (opS F).comp (opB F), 0⟩ := by
    apply TriAlg.ext
    · exact LinearMap.comp_zero (opL F)
    · exact LinearMap.comp_zero (opS F)
    · exact LinearMap.comp_zero (opR F)
    · change (opL F).comp (opA F) + (0 : (ℤ →₀ F) →ₗ[F] (ℕ →₀ F)).comp 0 = (opL F).comp (opA F)
      simp only [LinearMap.comp_zero, add_zero]
    · change (opS F).comp (opB F) + (0 : (ℕ →₀ F) →ₗ[F] (ℤ →₀ F)).comp 0 = (opS F).comp (opB F)
      simp only [LinearMap.comp_zero, add_zero]
    · change (opL F).comp 0 + (0 : (ℤ →₀ F) →ₗ[F] (ℕ →₀ F)).comp (opB F) +
        (0 : (ℕ →₀ F) →ₗ[F] (ℕ →₀ F)).comp 0 = 0
      simp only [LinearMap.comp_zero, LinearMap.zero_comp, add_zero]
  rw [hYX]
  apply TriAlg.ext
  · exact LinearMap.zero_comp (opL F)
  · exact LinearMap.zero_comp (opS F)
  · exact LinearMap.zero_comp (opR F)
  · change (0 : (ℕ →₀ F) →ₗ[F] (ℕ →₀ F)).comp 0 + ((opL F).comp (opA F)).comp (opS F) = opA F
    simp only [LinearMap.zero_comp, zero_add, LinearMap.comp_assoc, opL_comp_opA_comp_opS]
  · change (0 : (ℤ →₀ F) →ₗ[F] (ℤ →₀ F)).comp 0 + ((opS F).comp (opB F)).comp (opR F) = opB F
    simp only [LinearMap.zero_comp, zero_add, LinearMap.comp_assoc, opS_comp_opB_comp_opR]
  · change (0 : (ℕ →₀ F) →ₗ[F] (ℕ →₀ F)).comp 0 + ((opL F).comp (opA F)).comp 0 +
      (0 : (ℕ →₀ F) →ₗ[F] (ℕ →₀ F)).comp (opR F) = 0
    simp only [LinearMap.zero_comp, LinearMap.comp_zero, add_zero]

private lemma X_sq_zero (F : Type) [Field F] :
    X_gen F * X_gen F = 0 := by
  apply TriAlg.ext
  · change (0 : (ℕ →₀ F) →ₗ[F] (ℕ →₀ F)).comp 0 = 0
    exact LinearMap.zero_comp 0
  · change (0 : (ℤ →₀ F) →ₗ[F] (ℤ →₀ F)).comp 0 = 0
    exact LinearMap.zero_comp 0
  · change (0 : (ℕ →₀ F) →ₗ[F] (ℕ →₀ F)).comp 0 = 0
    exact LinearMap.zero_comp 0
  · change (0 : (ℕ →₀ F) →ₗ[F] (ℕ →₀ F)).comp (opA F) + (opA F).comp 0 = 0
    simp only [LinearMap.zero_comp, LinearMap.comp_zero, add_zero]
  · change (0 : (ℤ →₀ F) →ₗ[F] (ℤ →₀ F)).comp (opB F) + (opB F).comp 0 = 0
    simp only [LinearMap.zero_comp, LinearMap.comp_zero, add_zero]
  · change (0 : (ℕ →₀ F) →ₗ[F] (ℕ →₀ F)).comp 0 + (opA F).comp (opB F) +
      (0 : (ℕ →₀ F) →ₗ[F] (ℕ →₀ F)).comp 0 = 0
    simp only [LinearMap.zero_comp, add_zero, opA_comp_opB]

private lemma XYX_ne_zero (F : Type) [Field F] :
    X_gen F * Y_gen F * X_gen F ≠ 0 := by
  have hXY : X_gen F * Y_gen F = ⟨0, 0, 0, (opA F).comp (opS F), (opB F).comp (opR F), 0⟩ := by
    apply TriAlg.ext
    · exact LinearMap.zero_comp (opL F)
    · exact LinearMap.zero_comp (opS F)
    · exact LinearMap.zero_comp (opR F)
    · change (0 : (ℕ →₀ F) →ₗ[F] (ℕ →₀ F)).comp 0 + (opA F).comp (opS F) = (opA F).comp (opS F)
      simp only [LinearMap.zero_comp, zero_add]
    · change (0 : (ℤ →₀ F) →ₗ[F] (ℤ →₀ F)).comp 0 + (opB F).comp (opR F) = (opB F).comp (opR F)
      simp only [LinearMap.zero_comp, zero_add]
    · change (0 : (ℕ →₀ F) →ₗ[F] (ℕ →₀ F)).comp 0 + (opA F).comp 0 +
        (0 : (ℕ →₀ F) →ₗ[F] (ℕ →₀ F)).comp (opR F) = 0
      simp only [LinearMap.zero_comp, LinearMap.comp_zero, add_zero]
  intro h
  rw [hXY] at h
  have h13 : (0 : (ℕ →₀ F) →ₗ[F] (ℕ →₀ F)).comp 0 + ((opA F).comp (opS F)).comp (opB F) +
      (0 : (ℕ →₀ F) →ₗ[F] (ℕ →₀ F)).comp 0 = 0 := congrArg TriAlg.u13 h
  simp only [LinearMap.zero_comp, zero_add, add_zero, LinearMap.comp_assoc] at h13
  exact opA_comp_opS_comp_opB_ne_zero F h13

/-- The finitely generated `F`-subalgebra `A(F) = F⟨X_gen, Y_gen⟩ ⊆ TriAlg F`. -/
private noncomputable def CounterAlg (F : Type) [Field F] : Subalgebra F (TriAlg F) :=
  Algebra.adjoin F ({X_gen F, Y_gen F} : Set (TriAlg F))

/-- `diagHom` maps `CounterAlg F` into a commutative subring (generated by `diagHom (Y_gen F)`). -/
private lemma diagHom_comm_on_CounterAlg (F : Type) [Field F] (a b : CounterAlg F) :
    diagHom F a.val * diagHom F b.val = diagHom F b.val * diagHom F a.val := by
  let D := (Module.End F (ℕ →₀ F)) × (Module.End F (ℤ →₀ F)) × (Module.End F (ℕ →₀ F))
  let yD : D := diagHom F (Y_gen F)
  let evalY : Polynomial F →ₐ[F] D := Polynomial.aeval yD
  have hmem : ∀ u : TriAlg F, u ∈ CounterAlg F → ∃ p : Polynomial F, diagHom F u = evalY p := by
    intro u hu
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hu
    · intro g hg
      rcases hg with rfl | rfl
      · refine ⟨0, ?_⟩
        simp [evalY, diagHom, X_gen]
      · refine ⟨Polynomial.X, ?_⟩
        simp [evalY, yD]
    · intro c
      refine ⟨Polynomial.C c, ?_⟩
      simp only [evalY, Polynomial.aeval_C]
      rfl
    · intro u1 u2 _ _ ⟨p1, hp1⟩ ⟨p2, hp2⟩
      exact ⟨p1 + p2, by rw [map_add, hp1, hp2, map_add]⟩
    · intro u1 u2 _ _ ⟨p1, hp1⟩ ⟨p2, hp2⟩
      exact ⟨p1 * p2, by rw [map_mul, hp1, hp2, map_mul]⟩
  obtain ⟨pa, hpa⟩ := hmem a.val a.property
  obtain ⟨pb, hpb⟩ := hmem b.val b.property
  rw [hpa, hpb, ← map_mul, mul_comm pa pb, map_mul]

private structure DiagImg (F : Type) [Field F] where
  val : (Module.End F (ℕ →₀ F)) × (Module.End F (ℤ →₀ F)) × (Module.End F (ℕ →₀ F))
  mem : ∃ a : CounterAlg F, diagHom F a.val = val

private lemma DiagImg.ext {F : Type} [Field F] {x y : DiagImg F} (h : x.val = y.val) : x = y := by
  cases x; cases y; cases h; rfl

private noncomputable instance (F : Type) [Field F] : Zero (DiagImg F) :=
  ⟨⟨0, ⟨0, map_zero _⟩⟩⟩

private noncomputable instance (F : Type) [Field F] : One (DiagImg F) :=
  ⟨⟨1, ⟨1, map_one _⟩⟩⟩

private noncomputable instance (F : Type) [Field F] : Add (DiagImg F) :=
  ⟨fun x y => ⟨x.val + y.val, by
    rcases x.mem with ⟨a, ha⟩; rcases y.mem with ⟨b, hb⟩
    exact ⟨a + b, by rw [Subalgebra.coe_add, map_add, ha, hb]⟩⟩⟩

private noncomputable instance (F : Type) [Field F] : Neg (DiagImg F) :=
  ⟨fun x => ⟨-x.val, by
    rcases x.mem with ⟨a, ha⟩
    exact ⟨-a, by rw [Subalgebra.coe_neg, map_neg, ha]⟩⟩⟩

private noncomputable instance (F : Type) [Field F] : Mul (DiagImg F) :=
  ⟨fun x y => ⟨x.val * y.val, by
    rcases x.mem with ⟨a, ha⟩; rcases y.mem with ⟨b, hb⟩
    exact ⟨a * b, by rw [Subalgebra.coe_mul, map_mul, ha, hb]⟩⟩⟩

private noncomputable instance (F : Type) [Field F] : CommRing (DiagImg F) where
  add_assoc x y z := DiagImg.ext (add_assoc x.val y.val z.val)
  zero_add x := DiagImg.ext (zero_add x.val)
  add_zero x := DiagImg.ext (add_zero x.val)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel x := DiagImg.ext (neg_add_cancel x.val)
  add_comm x y := DiagImg.ext (add_comm x.val y.val)
  mul_assoc x y z := DiagImg.ext (mul_assoc x.val y.val z.val)
  one_mul x := DiagImg.ext (one_mul x.val)
  mul_one x := DiagImg.ext (mul_one x.val)
  left_distrib x y z := DiagImg.ext (left_distrib x.val y.val z.val)
  right_distrib x y z := DiagImg.ext (right_distrib x.val y.val z.val)
  zero_mul x := DiagImg.ext (zero_mul x.val)
  mul_zero x := DiagImg.ext (mul_zero x.val)
  mul_comm x y := DiagImg.ext (by
    change x.val * y.val = y.val * x.val
    rcases x.mem with ⟨a, ha⟩; rcases y.mem with ⟨b, hb⟩
    rw [← ha, ← hb]
    exact diagHom_comm_on_CounterAlg F a b)

private noncomputable def diagToImg (F : Type) [Field F] : CounterAlg F →+* DiagImg F where
  toFun a := ⟨diagHom F a.val, ⟨a, rfl⟩⟩
  map_one' := DiagImg.ext (map_one _)
  map_mul' _ _ := DiagImg.ext (map_mul _ _ _)
  map_zero' := DiagImg.ext (map_zero _)
  map_add' _ _ := DiagImg.ext (map_add _ _ _)

private lemma counterAlg_diag_QP_eq_one {F : Type} [Field F] {n : ℕ}
    (P Q : Matrix (Fin n) (Fin n) (CounterAlg F)) (hPQ : P * Q = 1) :
    ∀ i j : Fin n, diagHom F ((1 - Q * P) i j).val = 0 := by
  let π := diagToImg F
  have hπ_PQ : P.map π * Q.map π = 1 := by
    rw [← Matrix.map_mul, hPQ, Matrix.map_one π (map_zero π) (map_one π)]
  have hdet : (P.map π).det * (Q.map π).det = 1 := by
    rw [← Matrix.det_mul, hπ_PQ, Matrix.det_one]
  have hdet_unit : IsUnit (P.map π).det :=
    ⟨⟨(P.map π).det, (Q.map π).det, hdet, mul_comm (P.map π).det (Q.map π).det ▸ hdet⟩, rfl⟩
  obtain ⟨U, hU⟩ := (Matrix.isUnit_iff_isUnit_det (P.map π)).mpr hdet_unit
  have hQ : Q.map π = (U⁻¹ : (Matrix (Fin n) (Fin n) (DiagImg F))ˣ) := by
    calc Q.map π = 1 * Q.map π := (one_mul _).symm
      _ = ((U⁻¹ : (Matrix (Fin n) (Fin n) (DiagImg F))ˣ) : Matrix (Fin n) (Fin n) (DiagImg F)) *
            (U : Matrix (Fin n) (Fin n) (DiagImg F)) * Q.map π := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      _ = ((U⁻¹ : (Matrix (Fin n) (Fin n) (DiagImg F))ˣ) : Matrix (Fin n) (Fin n) (DiagImg F)) *
            (P.map π * Q.map π) := by rw [hU, Matrix.mul_assoc]
      _ = ((U⁻¹ : (Matrix (Fin n) (Fin n) (DiagImg F))ˣ) : Matrix (Fin n) (Fin n) (DiagImg F)) := by
          rw [hπ_PQ, mul_one]
  have hπ_QP : Q.map π * P.map π = 1 := by
    rw [hQ, ← hU, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  intro i j
  have hij : ((1 - Q * P).map π) i j = 0 := by
    have hmap : (1 - Q * P).map π = 1 - Q.map π * P.map π := by
      rw [Matrix.map_sub π (map_sub π), Matrix.map_one π (map_zero π) (map_one π), Matrix.map_mul]
    rw [hmap, hπ_QP, sub_self]; rfl
  exact congrArg DiagImg.val hij

/-- Every element of `CounterAlg F` has `diagHom` commuting with all other elements of `CounterAlg F`,
so `diagHom` induces a ring hom to a commutative ring `S = diagHom '' CounterAlg F`! -/
private lemma counterAlg_stablyFinite (F : Type) [Field F] : IsStablyFinite (CounterAlg F) := by
  intro n P Q hPQ
  set N : Matrix (Fin n) (Fin n) (CounterAlg F) := 1 - Q * P
  have hN_ker : ∀ i j : Fin n, diagHom F (N i j).val = 0 :=
    counterAlg_diag_QP_eq_one P Q hPQ
  have hN_cube : N * N * N = 0 := by
    ext i l
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    rw [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_zero]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [Subalgebra.coe_mul, AddSubmonoidClass.coe_finsetSum, Finset.sum_mul]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [Subalgebra.coe_mul]
    exact triAlg_ker_cube_zero (N i j).val (N j k).val (N k l).val
      (hN_ker i j) (hN_ker j k) (hN_ker k l)
  have hQP_idem : (Q * P) * (Q * P) = Q * P := by
    calc (Q * P) * (Q * P) = Q * (P * Q) * P := by simp [Matrix.mul_assoc]
      _ = Q * 1 * P := by rw [hPQ]
      _ = Q * P := by simp
  have hQP_inv : (1 + N + N * N) * (Q * P) = 1 := by
    have hQP_eq : Q * P = 1 - N := by simp only [N]; abel
    rw [hQP_eq]
    calc (1 + N + N * N) * (1 - N)
        = (1 + N + N * N) - (1 + N + N * N) * N := by rw [mul_sub, mul_one]
      _ = (1 + N + N * N) - (N + N * N + N * N * N) := by simp only [add_mul, one_mul]
      _ = 1 - N * N * N := by abel
      _ = 1 - 0 := by rw [hN_cube]
      _ = 1 := sub_zero 1
  calc Q * P = 1 * (Q * P) := (one_mul _).symm
    _ = ((1 + N + N * N) * (Q * P)) * (Q * P) := by rw [hQP_inv]
    _ = (1 + N + N * N) * ((Q * P) * (Q * P)) := by rw [Matrix.mul_assoc]
    _ = (1 + N + N * N) * (Q * P) := by rw [hQP_idem]
    _ = 1 := hQP_inv

theorem main_proof :
    ∀ (F : Type) [Field F],
      ∃ (A : Type) (_ : Ring A) (_ : Algebra F A),
        Algebra.FiniteType F A ∧ IsStablyFinite A ∧ ¬ IsLinearSofic F A := by
  intro F _
  classical
  refine ⟨CounterAlg F, inferInstance, inferInstance, ?_, counterAlg_stablyFinite F, ?_⟩
  · -- Finitely generated by {X_gen F, Y_gen F}
    let xA : CounterAlg F := ⟨X_gen F, Algebra.subset_adjoin (by simp)⟩
    let yA : CounterAlg F := ⟨Y_gen F, Algebra.subset_adjoin (by simp)⟩
    refine ⟨⟨({xA, yA} : Finset (CounterAlg F)), ?_⟩⟩
    rw [eq_top_iff]
    rintro ⟨u, hu⟩ _
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hu
    · intro g hg
      rcases hg with rfl | rfl
      · exact Algebra.subset_adjoin (by simp [xA])
      · exact Algebra.subset_adjoin (by simp [yA])
    · intro c
      exact Subalgebra.algebraMap_mem _ c
    · intro u1 u2 _ _ ih1 ih2
      exact Subalgebra.add_mem _ ih1 ih2
    · intro u1 u2 _ _ ih1 ih2
      exact Subalgebra.mul_mem _ ih1 ih2
  · -- Not linear sofic via Lemma 2.1
    let xA : CounterAlg F := ⟨X_gen F, Algebra.subset_adjoin (by simp)⟩
    let yA : CounterAlg F := ⟨Y_gen F, Algebra.subset_adjoin (by simp)⟩
    let zA : CounterAlg F := xA * yA * xA
    refine not_linearSofic_of_witness xA yA zA yA (yA * xA) ?_ ?_ ?_ ?_
    · intro h
      exact XYX_ne_zero F (congrArg Subtype.val h)
    · exact Subtype.ext (YXY_eq_X F).symm
    · exact Subtype.ext (by simp [zA, mul_assoc])
    · refine Subtype.ext ?_
      change Y_gen F * (X_gen F * Y_gen F * X_gen F) = 0
      calc Y_gen F * (X_gen F * Y_gen F * X_gen F)
          = (Y_gen F * X_gen F * Y_gen F) * X_gen F := by simp [mul_assoc]
        _ = X_gen F * X_gen F := by rw [YXY_eq_X F]
        _ = 0 := X_sq_zero F

end OMA.P_arxiv_2210_11650

theorem OMA.solution : type_of% @OMA.S_arxiv_2210_11650.main :=
  OMA.P_arxiv_2210_11650.main_proof
