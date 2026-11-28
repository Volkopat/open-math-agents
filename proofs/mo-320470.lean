import OMAStatements.S_mo_320470

/-!
# Sun's divisibility conjecture for a Legendre-symbol determinant

On the nonzero residues the involution `t ↦ d/t` changes the sign of the
quadratic character of `t² + ct + d`. Homogeneity gives zero sums along
each row and each column of the nonzero block. Two determinant-preserving
additions then expose the two factors of `p - 1`.
-/

open scoped BigOperators

namespace LegendreDetDivisibility

private theorem zeroBlock_dvd {G : Type*} [Fintype G] [DecidableEq G]
    (g : G) (A : Matrix (Option G) (Option G) ℤ)
    (left : ∀ i, A (some i) none = 1) (top : ∀ j, A none (some j) = -1)
    (rows : ∀ i, ∑ j : G, A (some i) (some j) = 0)
    (cols : ∀ j, ∑ i : G, A (some i) (some j) = 0) :
    (Fintype.card G : ℤ) ^ 2 ∣ A.det := by
  classical
  let c : Option G → ℤ := fun i => i.elim 0 (fun _ => 1)
  let v : Option G → ℤ := fun i => i.elim 1 (fun _ => 0)
  let w : Option G → ℤ := fun i => i.elim (-1) (fun _ => 0)
  let N : ℤ := Fintype.card G
  have hsum : (∑ i : Option G, c i • A i) = N • v := by
    ext j
    cases j with
    | none => simp [Fintype.sum_option, Finset.sum_apply, c, v, N, left]
    | some j => simp [Fintype.sum_option, Finset.sum_apply, c, v, cols]
  let R := A.updateRow (some g) v
  have hR : A.det = N * R.det := by
    have h := A.det_updateRow_sum (some g) c
    rw [hsum, Matrix.det_updateRow_smul] at h
    simpa [R, c] using h.symm
  have hsum' : (fun k => ∑ i : Option G, c i • R k i) = N • w := by
    funext k
    cases k with
    | none => simp [Fintype.sum_option, c, R, v, w, N, top, Matrix.updateRow, Function.update]
    | some k =>
      by_cases h : k = g
      · subst k
        simp [Fintype.sum_option, c, R, v, w, Matrix.updateRow, Function.update]
      · simp [Fintype.sum_option, c, R, v, w, Matrix.updateRow, Function.update, h, rows]
  have hC := R.det_updateCol_sum (some g) c
  rw [hsum', Matrix.det_updateCol_smul] at hC
  refine ⟨(R.updateCol (some g) w).det, ?_⟩
  calc
    A.det = N * R.det := hR
    _ = N * (N * (R.updateCol (some g) w).det) := by
      congr 1
      simpa [c] using hC.symm
    _ = (Fintype.card G : ℤ) ^ 2 * (R.updateCol (some g) w).det := by dsimp [N]; ring

private def val {F : Type*} [Field F] : Option Fˣ → F
  | none => 0
  | some x => x

private noncomputable def valEquiv (F : Type*) [Field F] : Option Fˣ ≃ F :=
  Equiv.ofBijective val (by
    constructor
    · intro a b h
      cases a <;> cases b
      · rfl
      · exact absurd h.symm (Units.ne_zero _)
      · exact absurd h (Units.ne_zero _)
      · exact congrArg some (Units.ext h)
    · intro b
      by_cases h : b = 0
      · exact ⟨none, h.symm⟩
      · exact ⟨some (Units.mk0 b h), rfl⟩)

private def entry {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (c d : F) (x y : Option Fˣ) : ℤ :=
  quadraticChar F (val x ^ 2 + c * val x * val y + d * val y ^ 2)

private def f {F : Type*} [Field F] [Fintype F] [DecidableEq F] (c d : F) (x : Fˣ) : ℤ :=
  quadraticChar F ((x : F) ^ 2 + c * x + d)

private lemma sum_f {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (c d : F) (hd : quadraticChar F d = -1) :
    ∑ x : Fˣ, f c d x = 0 := by
  have hd0 : d ≠ 0 := by
    intro h
    simp [h] at hd
  let u := Units.mk0 d hd0
  have flip (t : Fˣ) : f c d (u / t) = -f c d t := by
    have e : ((u / t : Fˣ) : F) ^ 2 + c * ((u / t : Fˣ) : F) + d =
        d * ((t : F)⁻¹ ^ 2) * ((t : F) ^ 2 + c * t + d) := by
      simp only [Units.val_div_eq_div_val, u, Units.val_mk0]
      field_simp
      ring
    rw [f, e, map_mul, map_mul, hd, quadraticChar_sq_one' (inv_ne_zero t.ne_zero)]
    simp [f]
  have h := (Equiv.divLeft u).sum_comp (f c d)
  change (∑ t : Fˣ, f c d (u / t)) = ∑ t : Fˣ, f c d t at h
  simp_rw [flip, Finset.sum_neg_distrib] at h
  omega

private lemma core {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (c d : F) (x y : Fˣ) : entry c d (some x) (some y) = f c d (x / y) := by
  have h : (x : F) ^ 2 + c * x * y + d * (y : F) ^ 2 =
      (y : F) ^ 2 * (((x / y : Fˣ) : F) ^ 2 + c * ((x / y : Fˣ) : F) + d) := by
    simp only [Units.val_div_eq_div_val]
    field_simp
  change quadraticChar F _ = quadraticChar F _
  dsimp only [val]
  rw [h, map_mul, quadraticChar_sq_one' y.ne_zero, one_mul]


private lemma finValue (p : ℕ) [NeZero p] (i : Fin p) :
    ZMod.finEquiv p i = (i.val : ZMod p) := by
  have hv : (ZMod.finEquiv p i).val = i.val := by
    cases p with
    | zero => exact Fin.elim0 i
    | succ p => rfl
  rw [← hv, ZMod.natCast_zmod_val]

theorem result : type_of% @OMA.S_mo_320470.main := by
  intro p hp _ c d hd
  classical
  let F := ZMod p
  let A : Matrix (Option Fˣ) (Option Fˣ) ℤ := Matrix.of (entry (c : F) (d : F))
  have hchar : quadraticChar F (d : F) = -1 := hd
  have sum0 := sum_f (c : F) (d : F) hchar
  have top (j : Fˣ) : A none (some j) = -1 := by
    simp [A, entry, val, map_mul, quadraticChar_sq_one' j.ne_zero, hchar]
  have left (i : Fˣ) : A (some i) none = 1 := by
    simp [A, entry, val, quadraticChar_sq_one' i.ne_zero]
  have rows (i : Fˣ) : ∑ j : Fˣ, A (some i) (some j) = 0 := by
    change ∑ j : Fˣ, entry (c : F) (d : F) (some i) (some j) = 0
    simp_rw [core]
    exact ((Equiv.divLeft i).sum_comp (f (c : F) (d : F))).trans sum0
  have cols (j : Fˣ) : ∑ i : Fˣ, A (some i) (some j) = 0 := by
    change ∑ i : Fˣ, entry (c : F) (d : F) (some i) (some j) = 0
    simp_rw [core]
    exact ((Equiv.divRight j).sum_comp (f (c : F) (d : F))).trans sum0
  have hdet := zeroBlock_dvd (1 : Fˣ) A left top rows cols
  have hcard : (Fintype.card Fˣ : ℤ) = (p : ℤ) - 1 := by
    rw [Fintype.card_units, ZMod.card, Nat.cast_sub (Fact.out : p.Prime).one_lt.le]
    norm_num
  let e : Fin p ≃ Option Fˣ := (ZMod.finEquiv p).toEquiv.trans (valEquiv F).symm
  have he (i : Fin p) : val (e i) = (i.val : F) := by
    calc
      val (e i) = ZMod.finEquiv p i := (valEquiv F).apply_symm_apply _
      _ = (i.val : F) := finValue p i
  have hm : (Matrix.of (fun i j : Fin p =>
      legendreSym p (((i.val : ℤ)) ^ 2 + c * i.val * j.val + d * (j.val : ℤ) ^ 2))) =
      A.submatrix e e := by
    ext i j
    change legendreSym p _ = entry (c : F) (d : F) (e i) (e j)
    unfold legendreSym entry
    push_cast
    rw [he, he]
  rw [hm, Matrix.det_submatrix_equiv_self, ← hcard]
  exact hdet

end LegendreDetDivisibility

theorem OMA.solution : type_of% @OMA.S_mo_320470.main := LegendreDetDivisibility.result
