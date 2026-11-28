import OMAStatements.S_mo_35207

/-!
# A counterexample to the finite-spectrum implication in MO-35207

Lean formalization of a counterexample by @rifter0418 with Astra.
The operator-algebra construction follows the approach of Yang, Hou and Fang,
*Kadison's Open Problem and R*-Algebras*, arXiv:2611.20690, Section 4.
Here four unitaries encode each finite stage. Two phases recover each inner generator.
The accepted problem statement was contributed by @Dugongue.
-/

section

/-! Finite-dimensional growth under a proper matrix corner embedding. -/

namespace MO35207
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

variable {D : Type*} [Ring D] [Algebra ℂ D]

private def sandwich (V : Matrix m n D) (W : Matrix n m D) :
    Matrix n n D →ₗ[ℂ] Matrix m m D where
  toFun x := V*x*W
  map_add' x y := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c x := by simp

/-- It suffices to recover the old generators inside a proper corner. The next
generated algebra then has strictly larger dimension, without any irreducibility
or generation of every ambient matrix. -/
theorem dimension_grows_in_proper_corner [FiniteDimensional ℂ D] (V : Matrix m n D) (W : Matrix n m D)
    (hWV : W*V = 1) (hproper : V*W ≠ 1) (s : Set (Matrix n n D))
    (B : Subalgebra ℂ (Matrix m m D)) (hP : V*W ∈ B)
    (hs : ∀ x ∈ s, V*x*W ∈ B) :
    Module.finrank ℂ (Algebra.adjoin ℂ s) < Module.finrank ℂ B := by
  let θ := sandwich V W
  have hmul (x y : Matrix n n D) : θ (x*y) = θ x * θ y := by
    change V*(x*y)*W = (V*x*W)*(V*y*W)
    calc
      _ = V*x*(W*V)*y*W := by rw [hWV, Matrix.mul_one, Matrix.mul_assoc V x y]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hin (x : Matrix n n D) (hx : x ∈ Algebra.adjoin ℂ s) : θ x ∈ B := by
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hs _ hx
    | algebraMap c =>
      rw [Algebra.algebraMap_eq_smul_one, map_smul]
      exact B.smul_mem (by simpa [θ, sandwich] using hP) c
    | add x y _ _ hx hy => simpa using B.add_mem hx hy
    | mul x y _ _ hx hy => rw [hmul]; exact B.mul_mem hx hy
  let A := Algebra.adjoin ℂ s
  let f : A →ₗ[ℂ] B := (θ.comp A.val.toLinearMap).codRestrict B.toSubmodule (fun x => hin x x.property)
  have hretract (x : Matrix n n D) : W*(θ x)*V = x := by
    calc
      _ = (W*V)*x*(W*V) := by simp only [θ, sandwich, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_assoc]
      _ = x := by simp [hWV]
  have hfi : Function.Injective f := by
    intro x y h
    have he : θ x.val = θ y.val := congrArg Subtype.val h
    exact Subtype.ext ((hretract x).symm.trans ((congrArg (fun z => W*z*V) he).trans (hretract y)))
  have hnot : LinearMap.range f ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := LinearMap.range_eq_top.mp h (1 : B)
    have he : θ x.val = 1 := congrArg Subtype.val hx
    have hp' : θ x.val * (V*W) = θ x.val := by
      calc
        _ = V*x.val*(W*V)*W := by simp only [θ, sandwich, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_assoc]
        _ = _ := by rw [hWV, Matrix.mul_one]; rfl
    rw [he, Matrix.one_mul] at hp'
    exact hproper hp'
  exact (LinearMap.finrank_range_of_inj hfi).symm.trans_lt (Submodule.finrank_lt hnot)

/-- Two phase choices separate a generator from its adjoint in a compression. -/
theorem recover_from_two_phases {A : Type*} [Ring A] [Algebra ℂ A]
    (B : Subalgebra ℂ A) (x y : A)
    (h₁ : x + y ∈ B) (h₂ : Complex.I • (x - y) ∈ B) : x ∈ B := by
  have hi := B.smul_mem h₂ (-Complex.I)
  simp [smul_smul, Complex.I_mul_I] at hi
  have hsum := B.smul_mem (B.add_mem h₁ hi) ((2:ℂ)⁻¹)
  convert hsum using 1
  module

end
end MO35207

end

section

/-! Compression along a pair of cube vertices carrying a unitary and a scalar phase. -/

namespace MO35207
noncomputable section
variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Ring A] [StarRing A]
  [Algebra ℂ A] [StarModule ℂ A]

/-- Values of one column in the encoding map at the two distinguished vertices. -/
def endColumn (lo hi : ι) (x : A) : ι → A := Pi.single lo 1 + Pi.single hi x

omit [StarRing A] [StarModule ℂ A] in
private theorem contract_row (lo hi : ι) (x : A) (a : ι → ℂ) :
    (∑ j, a j • endColumn lo hi x j) = a lo • (1 : A) + a hi • x := by
  classical
  simp [endColumn, Pi.single_apply, smul_add, smul_ite, Finset.sum_add_distrib, eq_comm]

omit [StarModule ℂ A] in
/-- The four corners of the scalar background determine its entire compression
on these two columns, even when the inner coefficients do not commute. -/
theorem endpoint_compression (lo hi : ι) (x y : A) (M : Matrix ι ι ℂ) :
    (∑ i, star (endColumn lo hi x i) * ∑ j, M i j • endColumn lo hi y j) =
      M lo lo • (1 : A) + M lo hi • y +
        star x * (M hi lo • (1 : A) + M hi hi • y) := by
  classical
  simp_rw [contract_row]
  simp [endColumn, Pi.single_apply, apply_ite star, ite_mul, add_mul, Finset.sum_add_distrib, eq_comm]

omit [StarModule ℂ A] in
/-- An individual color contributes two identity copies to the column norm.
The factor comes from the two distinct endpoints and a unitary coefficient. -/
theorem endpoint_gram (lo hi : ι) (hne : lo ≠ hi) (u : A) (hu : star u * u = 1) :
    (∑ i, star (endColumn lo hi u i) * endColumn lo hi u i) = 1 + 1 := by
  classical
  have h := endpoint_compression lo hi u u (1 : Matrix ι ι ℂ)
  simpa [Matrix.one_apply, hne, Ne.symm hne, ite_smul, hu] using h

/-- Recover the encoded coefficient using two colors with phases 1 and i.
Only one of the two off-diagonal entries of the background connector needs
to be nonzero. -/
theorem recover_encoded_generator (lo hi : ι) (u : A) (M : Matrix ι ι ℂ)
    (hll : M lo lo = 0) (hhh : M hi hi = 0) (hlh : M lo hi ≠ 0)
    (B : Subalgebra ℂ A)
    (h₁ : (∑ i, star (endColumn lo hi u i) * ∑ j, M i j • endColumn lo hi u j) ∈ B)
    (hI : (∑ i, star (endColumn lo hi (Complex.I • u) i) *
      ∑ j, M i j • endColumn lo hi (Complex.I • u) j) ∈ B) : u ∈ B := by
  rw [endpoint_compression, hll, hhh] at h₁ hI
  simp only [zero_smul, zero_add, add_zero, mul_smul_comm, mul_one] at h₁ hI
  let x := M lo hi • u
  let y := M hi lo • star u
  have hsep : Complex.I • (x - y) ∈ B := by
    convert hI using 1
    simp only [x, y, star_smul, Complex.star_def, Complex.conj_I]
    module
  have h := recover_from_two_phases B x y h₁ hsep
  simpa [x, smul_smul, hlh] using B.smul_mem h (M lo hi)⁻¹

end
end MO35207

end

section

/-! The normalized columns and proper projection for one stage of the encoding. -/

namespace MO35207
noncomputable section
variable {C L I A : Type*} [Fintype C] [Fintype L] [Fintype I]
  [DecidableEq C] [DecidableEq L] [DecidableEq I]
  [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

/-- A column repeats the two endpoint components at each port of each color. -/
def encodingColumn (lo hi : I) (u : C → A) : Matrix (C × L × I) Unit A :=
  fun p _ => endColumn lo hi (u p.1) p.2.2

def encodingMultiplicity (C L : Type*) [Fintype C] [Fintype L] : ℂ :=
  2 * Fintype.card C * Fintype.card L

def encodingRow (lo hi : I) (u : C → A) : Matrix Unit (C × L × I) A :=
  (encodingMultiplicity C L)⁻¹ • (encodingColumn (L := L) lo hi u).conjTranspose

omit [DecidableEq C] [DecidableEq L] [StarModule ℂ A] in
theorem encoding_gram (lo hi : I) (hne : lo ≠ hi) (u : C → A)
    (hu : ∀ c, star (u c) * u c = 1) :
    (encodingColumn (L := L) lo hi u).conjTranspose * encodingColumn (L := L) lo hi u =
      encodingMultiplicity C L • (1 : Matrix Unit Unit A) := by
  apply Matrix.ext
  intro i j
  cases i
  cases j
  change (∑ p : C × L × I, star (endColumn lo hi (u p.1) p.2.2) *
    endColumn lo hi (u p.1) p.2.2) = encodingMultiplicity C L • (1 : A)
  simp only [Fintype.sum_prod_type, endpoint_gram lo hi hne _ (hu _),
    Finset.sum_const, Finset.card_univ]
  simp [encodingMultiplicity, mul_smul, two_smul, Nat.cast_smul_eq_nsmul, smul_add]

omit [DecidableEq C] [DecidableEq L] [StarModule ℂ A] in
theorem encoding_retract [Nonempty C] [Nonempty L] (lo hi : I) (hne : lo ≠ hi) (u : C → A)
    (hu : ∀ c, star (u c) * u c = 1) :
    encodingRow (L := L) lo hi u * encodingColumn (L := L) lo hi u = 1 := by
  have hN : encodingMultiplicity C L ≠ 0 := by
    unfold encodingMultiplicity
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  rw [encodingRow, Matrix.smul_mul, encoding_gram lo hi hne u hu, smul_smul, inv_mul_cancel₀ hN, one_smul]

omit [Fintype I] [StarModule ℂ A] in
/-- An unused cube vertex gives a diagonal zero in the image projection. -/
theorem encoding_proper [Nonempty C] [Nonempty L] [Nontrivial A] (lo hi spare : I)
    (hs₁ : spare ≠ lo) (hs₂ : spare ≠ hi) (u : C → A) :
    encodingColumn (L := L) lo hi u * encodingRow (L := L) lo hi u ≠ 1 := by
  classical
  intro h
  let p : C × L × I := (Classical.arbitrary C, Classical.arbitrary L, spare)
  have e := congrArg (fun M : Matrix (C × L × I) (C × L × I) A => M p p) h
  simp [Matrix.mul_apply, encodingColumn, endColumn, p, hs₁, hs₂] at e

omit [Fintype I] [DecidableEq C] [DecidableEq L] in
/-- A real multiple of V V* is self-adjoint. -/
theorem encoding_selfAdjoint (lo hi : I) (u : C → A) :
    IsSelfAdjoint (encodingColumn (L := L) lo hi u * encodingRow (L := L) lo hi u) := by
  change Matrix.conjTranspose (encodingColumn (L := L) lo hi u * encodingRow (L := L) lo hi u) = _
  simp [encodingRow, encodingMultiplicity, Matrix.mul_smul, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul]

omit [DecidableEq C] [DecidableEq L] [StarModule ℂ A] in
theorem encoding_squared [Nonempty C] [Nonempty L] (lo hi : I) (hne : lo ≠ hi) (u : C → A)
    (hu : ∀ c, star (u c) * u c = 1) :
    (encodingColumn (L := L) lo hi u * encodingRow (L := L) lo hi u) *
      (encodingColumn (L := L) lo hi u * encodingRow (L := L) lo hi u) = encodingColumn (L := L) lo hi u * encodingRow (L := L) lo hi u := by
  calc
    _ = encodingColumn (L := L) lo hi u * (encodingRow (L := L) lo hi u * encodingColumn (L := L) lo hi u) *
          encodingRow (L := L) lo hi u := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [encoding_retract lo hi hne u hu, Matrix.mul_one]

end
end MO35207

end

section

/-! Recovery of the inner algebra from compressed entries at particular ports. -/

namespace MO35207
noncomputable section

variable {r n A : Type*} [Fintype r] [Fintype n] [DecidableEq r] [DecidableEq n]
  [Ring A] [Algebra ℂ A]

/-- Pull the outer algebra back to a proper corner. Its unit there is V W. -/
def recoveredAlgebra (V : Matrix r n A) (W : Matrix n r A) (hWV : W*V = 1)
    (B : Subalgebra ℂ (Matrix r r A)) (hP : V*W ∈ B) : Subalgebra ℂ (Matrix n n A) where
  carrier := {x | V*x*W ∈ B}
  zero_mem' := by simp
  one_mem' := by simpa using hP
  add_mem' := by
    intro x y hx hy
    change V*(x+y)*W ∈ B
    simpa only [Matrix.mul_add, Matrix.add_mul] using B.add_mem hx hy
  mul_mem' := by
    intro x y hx hy
    have e : V*(x*y)*W = (V*x*W)*(V*y*W) := by
      calc
        _ = V*x*(W*V)*y*W := by rw [hWV, Matrix.mul_one, Matrix.mul_assoc V x y]
        _ = _ := by simp only [Matrix.mul_assoc]
    change V*(x*y)*W ∈ B
    rw [e]
    exact B.mul_mem hx hy
  algebraMap_mem' := by
    intro c
    change V*algebraMap ℂ (Matrix n n A) c*W ∈ B
    simpa only [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      using B.smul_mem hP c

theorem compressed_mem_recovered (V : Matrix r n A) (W : Matrix n r A) (hWV : W*V = 1)
    (B : Subalgebra ℂ (Matrix r r A)) (hP : V*W ∈ B) {Y : Matrix r r A} (hY : Y ∈ B) :
    W*Y*V ∈ recoveredAlgebra V W hWV B hP := by
  change V*(W*Y*V)*W ∈ B
  simpa only [Matrix.mul_assoc] using B.mul_mem (B.mul_mem hP hY) hP

variable {C L I : Type*} [Fintype C] [Fintype L] [Fintype I]
  [DecidableEq C] [DecidableEq L] [DecidableEq I] [StarRing A] [StarModule ℂ A]

/-- A lifted scalar matrix supported at a single color and port. -/
def portConnector (c : C) (l : L) (M : Matrix I I ℂ) : Matrix (C × L × I) (C × L × I) A :=
  fun p q => if p.1 = c ∧ p.2.1 = l ∧ q.1 = c ∧ q.2.1 = l then
    algebraMap ℂ A (M p.2.2 q.2.2) else 0

omit [StarModule ℂ A] in
theorem port_compression (lo hi : I) (u : C → A) (c : C) (l : L) (M : Matrix I I ℂ) :
    (encodingRow (L := L) lo hi u * portConnector (A := A) c l M * encodingColumn (L := L) lo hi u) () () =
      (encodingMultiplicity C L)⁻¹ •
        ∑ i, star (endColumn lo hi (u c) i) * ∑ j, M i j • endColumn lo hi (u c) j := by
  rw [Matrix.mul_assoc]
  simp [encodingRow, encodingColumn, portConnector, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply, ite_and, ite_mul, ← Algebra.smul_def, mul_ite,
    Finset.sum_ite_irrel, Matrix.smul_apply, ← Finset.smul_sum]

omit [StarModule ℂ A] in
/-- A compressed port connector recovers the unnormalized coefficient in the pulled-back
algebra, using the nonzero multiplicity of the color and port sets. -/
theorem endpoint_mem_recovered [Nonempty C] [Nonempty L] (lo hi : I) (hne : lo ≠ hi)
    (u : C → A) (hu : ∀ c, star (u c)*u c = 1) (c : C) (l : L) (M : Matrix I I ℂ)
    (B : Subalgebra ℂ (Matrix (C × L × I) (C × L × I) A))
    (hP : encodingColumn (L := L) lo hi u * encodingRow (L := L) lo hi u ∈ B)
    (hM : portConnector c l M ∈ B) :
    let R := recoveredAlgebra _ _ (encoding_retract (L := L) lo hi hne u hu) B hP
    (∑ i, star (endColumn lo hi (u c) i) * ∑ j, M i j • endColumn lo hi (u c) j) ∈
      R.comap (Matrix.scalarAlgHom Unit ℂ) := by
  let Q := ∑ i, star (endColumn lo hi (u c) i) * ∑ j, M i j • endColumn lo hi (u c) j
  let R := recoveredAlgebra _ _ (encoding_retract (L := L) lo hi hne u hu) B hP
  have h := compressed_mem_recovered _ _ (encoding_retract (L := L) lo hi hne u hu) B hP hM
  have he : encodingRow (L := L) lo hi u * portConnector (A := A) c l M * encodingColumn (L := L) lo hi u =
      Matrix.scalarAlgHom Unit ℂ ((encodingMultiplicity C L)⁻¹ • Q) := by
    apply Matrix.ext
    rintro ⟨⟩ ⟨⟩
    change _ = (encodingMultiplicity C L)⁻¹ • Q
    exact port_compression lo hi u c l M
  rw [he] at h
  change (encodingMultiplicity C L)⁻¹ • Q ∈ R.comap (Matrix.scalarAlgHom Unit ℂ) at h
  have hN : encodingMultiplicity C L ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  simpa [Q, smul_smul, hN] using (R.comap (Matrix.scalarAlgHom Unit ℂ)).smul_mem h (encodingMultiplicity C L)

/-- The second color records an independent phase of the same inner generator. -/
def phaseCopies (u : C → A) (p : C × Bool) : A := if p.2 then Complex.I • u p.1 else u p.1

omit [Fintype C] [DecidableEq C] in
theorem phaseCopies_isometry (u : C → A) (hu : ∀ c, star (u c)*u c = 1) (p : C × Bool) :
    star (phaseCopies u p) * phaseCopies u p = 1 := by
  rcases p with ⟨c, b⟩
  cases b <;> simp [phaseCopies, star_smul, smul_smul, Complex.I_mul_I, hu]

/-- For an outer algebra containing the projection and the two supported
connectors, the copy of the original generator lies in its proper corner. -/
theorem two_color_recovery [Nonempty C] [Nonempty L] (lo hi : I) (hne : lo ≠ hi)
    (u : C → A) (hu : ∀ c, star (u c)*u c = 1) (c : C) (l : L) (M : Matrix I I ℂ)
    (hll : M lo lo = 0) (hhh : M hi hi = 0) (hlh : M lo hi ≠ 0)
    (B : Subalgebra ℂ (Matrix ((C × Bool) × L × I) ((C × Bool) × L × I) A))
    (hP : encodingColumn (L := L) lo hi (phaseCopies u) * encodingRow (L := L) lo hi (phaseCopies u) ∈ B)
    (hM : ∀ b : Bool, portConnector (c,b) l M ∈ B) :
    let R := recoveredAlgebra _ _ (encoding_retract (L := L) lo hi hne (phaseCopies u)
      (phaseCopies_isometry u hu)) B hP
    u c ∈ R.comap (Matrix.scalarAlgHom Unit ℂ) := by
  dsimp only
  apply recover_encoded_generator lo hi _ M hll hhh hlh
  · simpa only [phaseCopies, Bool.false_eq_true, if_false] using
      endpoint_mem_recovered lo hi hne (phaseCopies u) (phaseCopies_isometry u hu)
        (c,false) l M B hP (hM false)
  · simpa only [phaseCopies, if_true] using
      endpoint_mem_recovered lo hi hne (phaseCopies u) (phaseCopies_isometry u hu)
        (c,true) l M B hP (hM true)

end
end MO35207

end

section

/-! Short-word spanning for generators satisfying scalar Clifford relations. -/

namespace MO35207
noncomputable section
variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- The span of products selected in order from the list, using each position at most once. -/
private def orderedSpan : List A → Submodule ℂ A
  | [] => Submodule.span ℂ {1}
  | a :: l => orderedSpan l ⊔ (orderedSpan l).map (LinearMap.mulLeft ℂ a)

private theorem one_mem_orderedSpan (l : List A) : 1 ∈ orderedSpan l := by
  induction l with
  | nil => exact Submodule.subset_span (Set.mem_singleton _)
  | cons a l ih => exact Submodule.mem_sup_left ih

private theorem orderedSpan_le_of_sublist (l : List A) (Q : Submodule ℂ A)
    (h : ∀ w : List A, w.Sublist l → w.prod ∈ Q) : orderedSpan l ≤ Q := by
  induction l generalizing Q with
  | nil =>
    apply Submodule.span_le.mpr
    simpa using h [] .slnil
  | cons a l ih =>
    refine sup_le (ih Q fun w hw => h w (hw.cons a)) ?_
    apply Submodule.map_le_iff_le_comap.mpr
    exact ih _ fun w hw => h (a :: w) (hw.cons_cons a)

private theorem gen_mul_orderedSpan (l : List A)
    (hsq : ∀ x ∈ l, ∃ c : ℂ, x * x = algebraMap ℂ A c)
    (hac : ∀ x ∈ l, ∀ y ∈ l, ∃ c : ℂ, x * y + y * x = algebraMap ℂ A c) :
    ∀ x ∈ l, ∀ b ∈ orderedSpan l, x * b ∈ orderedSpan l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hold := ih (fun x hx => hsq x (List.mem_cons_of_mem _ hx))
      (fun x hx y hy => hac x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
    intro x hx b hb
    obtain ⟨m, hm, _, ⟨t, ht, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hb
    change x * (m + a * t) ∈ orderedSpan (a :: l)
    rw [mul_add]
    rcases List.mem_cons.mp hx with rfl | hx
    · apply Submodule.add_mem
      · exact Submodule.mem_sup_right ⟨m, hm, rfl⟩
      · obtain ⟨c, hc⟩ := hsq x List.mem_cons_self
        rw [← mul_assoc, hc, ← Algebra.smul_def]
        exact Submodule.mem_sup_left ((orderedSpan l).smul_mem c ht)
    · apply Submodule.add_mem
      · exact Submodule.mem_sup_left (hold x hx m hm)
      · obtain ⟨c, hc⟩ := hac x (List.mem_cons_of_mem a hx) a List.mem_cons_self
        have h : x * (a * t) = c • t - a * (x * t) := by
          apply eq_sub_iff_add_eq.mpr
          rw [← mul_assoc, ← mul_assoc, ← add_mul, hc, Algebra.smul_def]
        rw [h]
        exact Submodule.sub_mem _ (Submodule.mem_sup_left ((orderedSpan l).smul_mem c ht))
          (Submodule.mem_sup_right ⟨x * t, hold x hx t ht, rfl⟩)

/-- In a complex algebra with scalar squares and scalar anticommutators, a
functional that vanishes on ordered subwords vanishes on the whole generated
algebra. No nondegeneracy of the induced quadratic form is required. -/
theorem clifford_functional_vanishes (l : List A)
    (hsq : ∀ x ∈ l, ∃ c : ℂ, x * x = algebraMap ℂ A c)
    (hac : ∀ x ∈ l, ∀ y ∈ l, ∃ c : ℂ, x * y + y * x = algebraMap ℂ A c)
    (L : A →ₗ[ℂ] ℂ) (hv : ∀ w : List A, w.Sublist l → L w.prod = 0)
    {x : A} (hx : x ∈ Algebra.adjoin ℂ {x | x ∈ l}) : L x = 0 := by
  let W := orderedSpan l
  have hpres (y : A) (hy : y ∈ Algebra.adjoin ℂ {x | x ∈ l}) :
      ∀ b ∈ W, y * b ∈ W := by
    induction hy using Algebra.adjoin_induction with
    | mem z hz => exact gen_mul_orderedSpan l hsq hac z hz
    | algebraMap r =>
      intro b hb
      rw [← Algebra.smul_def]
      exact W.smul_mem r hb
    | add y z _ _ hy hz =>
      intro b hb
      rw [add_mul]
      exact W.add_mem (hy b hb) (hz b hb)
    | mul y z _ _ hy hz =>
      intro b hb
      rw [mul_assoc]
      exact hy _ (hz b hb)
  have hxW : x ∈ W := by simpa using hpres x hx 1 (one_mem_orderedSpan l)
  exact orderedSpan_le_of_sublist l (LinearMap.ker L) hv hxW

end
end MO35207

end

section

/-! Signed flips on the Boolean cube give concrete finite Clifford matrices. -/

namespace MO35207.Cube
noncomputable section

abbrev Vertex (g : ℕ) := Fin g → Bool
abbrev Mat (g : ℕ) := Matrix (Vertex g) (Vertex g) ℂ
variable {g : ℕ}

def flip (i : Fin g) (s : Vertex g) : Vertex g := fun k => if k = i then !(s k) else s k

@[simp] theorem flip_twice (i : Fin g) (s : Vertex g) : flip i (flip i s) = s := by
  funext k
  by_cases h : k = i <;> simp [flip, h]

theorem flip_comm (i j : Fin g) (s : Vertex g) : flip i (flip j s) = flip j (flip i s) := by
  funext k
  by_cases hij : i = j
  · subst j
    rfl
  by_cases hi : k = i
  · subst k
    simp [flip, hij]
  by_cases hj : k = j
  · subst k
    simp [flip, Ne.symm hij]
  simp [flip, hi, hj]

private def bitSign (b : Bool) : ℂ := if b then -1 else 1

def sign (i : Fin g) (s : Vertex g) : ℂ := ∏ k ∈ Finset.Iio i, bitSign (s k)

theorem sign_square (i : Fin g) (s : Vertex g) : sign i s * sign i s = 1 := by
  simp only [sign, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro k _
  cases s k <;> norm_num [bitSign]

private theorem sign_star (i : Fin g) (s : Vertex g) : star (sign i s) = sign i s := by
  simp [sign, bitSign, apply_ite star]

theorem sign_flip (i j : Fin g) (s : Vertex g) :
    sign j (flip i s) = (if i < j then -1 else 1) * sign j s := by
  classical
  have h (k : Fin g) : bitSign (flip i s k) = (if k = i then -1 else 1) * bitSign (s k) := by
    by_cases hk : k = i
    · subst k
      cases hb : s i <;> norm_num [bitSign, flip, hb]
    · simp [flip, hk]
  simp only [sign, h, Finset.prod_mul_distrib]
  simp

def gamma (i : Fin g) : Mat g :=
  fun s t => if t = flip i s then sign i s else 0

theorem gamma_mul_apply (i : Fin g) (B : Mat g) (s t : Vertex g) :
    (gamma i * B) s t = sign i s * B (flip i s) t := by
  classical
  simp [Matrix.mul_apply, gamma, ite_mul]

theorem gamma_selfAdjoint (i : Fin g) : IsSelfAdjoint (gamma i) := by
  ext s t
  change star (gamma i t s) = gamma i s t
  by_cases h : t = flip i s
  · subst t
    simp [gamma, sign_flip, sign_star]
  · have h' : s ≠ flip i t := fun e => h (by rw [e, flip_twice])
    simp [gamma, h, h']

theorem gamma_square (i : Fin g) : gamma i * gamma i = 1 := by
  ext s t
  rw [gamma_mul_apply]
  by_cases h : s = t
  · subst t
    simp [gamma, sign_flip, sign_square]
  · simp [gamma, h, Ne.symm h]

theorem gamma_anticommute (i j : Fin g) (hne : i ≠ j) :
    gamma i * gamma j + gamma j * gamma i = 0 := by
  ext s t
  simp only [Matrix.add_apply, gamma_mul_apply, gamma, sign_flip, Matrix.zero_apply]
  rw [flip_comm i j]
  rcases lt_or_gt_of_ne hne with h | h
  · simp only [if_pos h, if_neg (not_lt_of_gt h)]
    split_ifs <;> ring
  · simp only [if_pos h, if_neg (not_lt_of_gt h)]
    split_ifs <;> ring

end
end MO35207.Cube

end

section

/-! The opposite corners of the cube are invisible to small spaces of Clifford generators. -/

namespace MO35207.Cube
noncomputable section
variable {g : ℕ}

/-- Number of differing coordinates. A signed flip traverses one cube edge. -/
def distance (s t : Vertex g) : ℕ := (Finset.univ.filter fun i => s i ≠ t i).card

theorem distance_flip (i : Fin g) (s t : Vertex g) :
    distance s t ≤ distance (flip i s) t + 1 := by
  apply (Finset.card_le_card (t := insert i (Finset.univ.filter fun k => flip i s k ≠ t k)) ?_).trans
    (Finset.card_insert_le _ _)
  intro k hk
  by_cases h : k = i
  · simp [h]
  · apply Finset.mem_insert_of_mem
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa [flip, h] using (Finset.mem_filter.mp hk).2⟩

abbrev vectors (g : ℕ) : Submodule ℂ (Mat g) := Submodule.span ℂ (Set.range (@gamma g))

private theorem anticommutator_scalar {x y : Mat g} (hx : x ∈ vectors g) (hy : y ∈ vectors g) :
    ∃ c : ℂ, x * y + y * x = algebraMap ℂ (Mat g) c := by
  let B := LinearMap.mul ℂ (Mat g) + (LinearMap.mul ℂ (Mat g)).flip
  let S := (⊥ : Subalgebra ℂ (Mat g)).toSubmodule
  have extend (f : Mat g →ₗ[ℂ] Mat g) (hf : ∀ i : Fin g, f (gamma i) ∈ S) :
      vectors g ≤ S.comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hf i
  have hb : B x y ∈ S := by
    apply extend (B.flip y) _ hx
    intro i
    apply extend (B (gamma i)) _ hy
    intro j
    change gamma i * gamma j + gamma j * gamma i ∈ S
    by_cases h : i = j
    · subst j
      rw [gamma_square]
      exact (⊥ : Subalgebra ℂ (Mat g)).add_mem (one_mem _) (one_mem _)
    · rw [gamma_anticommute i j h]
      exact S.zero_mem
  change ∃ c : ℂ, algebraMap ℂ (Mat g) c = x * y + y * x at hb
  obtain ⟨c, hc⟩ := hb
  exact ⟨c, hc.symm⟩

private theorem square_scalar {x : Mat g} (hx : x ∈ vectors g) :
    ∃ c : ℂ, x * x = algebraMap ℂ (Mat g) c := by
  obtain ⟨c, hc⟩ := anticommutator_scalar hx hx
  refine ⟨(2 : ℂ)⁻¹ * c, ?_⟩
  calc
    x * x = (2 : ℂ)⁻¹ • (x * x + x * x) := by module
    _ = algebraMap ℂ (Mat g) _ := by rw [hc, Algebra.smul_def, map_mul]

private theorem short_product_entry (w : List (Mat g)) (hw : ∀ x ∈ w, x ∈ vectors g)
    (s t : Vertex g) (hd : w.length < distance s t) : w.prod s t = 0 := by
  induction w generalizing s with
  | nil =>
    have hne : s ≠ t := by
      rintro rfl
      simp [distance] at hd
    simp [hne]
  | cons a w ih =>
    have ha := hw a List.mem_cons_self
    have hw' : ∀ x ∈ w, x ∈ vectors g := fun _ h => hw _ (List.mem_cons_of_mem _ h)
    clear hw
    change w.length + 1 < distance s t at hd
    change (a * w.prod) s t = 0
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have hstep := distance_flip i s t
      have hlen : w.length < distance (flip i s) t := by
        omega
      rw [gamma_mul_apply, ih hw' (flip i s) hlen, mul_zero]
    | zero => simp
    | add x y _ _ hx hy => simp [add_mul, hx, hy]
    | smul c x _ hx => simp [hx]

/-- Any algebra generated by h linear combinations of these matrices has
zero (s,t) entry when s and t differ in more than h positions. This applies
also to arbitrary complex, non-Hermitian linear combinations. -/
theorem corner_vanishes (l : List (Mat g)) (hl : ∀ x ∈ l, x ∈ vectors g)
    (s t : Vertex g) (hd : l.length < distance s t) {x : Mat g}
    (hx : x ∈ Algebra.adjoin ℂ {y | y ∈ l}) : x s t = 0 := by
  apply clifford_functional_vanishes l (fun a h => square_scalar (hl a h))
    (fun a h b k => anticommutator_scalar (hl a h) (hl b k))
    (Matrix.entryLinearMap ℂ ℂ s t) _ hx
  intro w hw
  exact short_product_entry w (fun y hy => hl y (hw.subset hy)) s t
    (lt_of_le_of_lt hw.length_le hd)

theorem opposite_corner_vanishes (l : List (Mat g)) (hl : ∀ x ∈ l, x ∈ vectors g)
    (h : l.length < g) {x : Mat g} (hx : x ∈ Algebra.adjoin ℂ {y | y ∈ l}) :
    x (fun _ => false) (fun _ => true) = 0 :=
  corner_vanishes l hl _ _ (by simpa [distance] using h) hx

end
end MO35207.Cube

end

section

/-! A full word connects the same two corners that small Clifford pencils cannot connect. -/

namespace MO35207.Cube
noncomputable section
variable {g : ℕ}

private def walk : List (Fin g) → Vertex g → Vertex g
  | [], s => s
  | i :: l, s => walk l (flip i s)

private theorem walk_bit (l : List (Fin g)) (hd : l.Nodup) (s : Vertex g) (i : Fin g) :
    walk l s i = if i ∈ l then !(s i) else s i := by
  induction l generalizing s with
  | nil => simp [walk]
  | cons j l ih =>
    obtain ⟨hj, hl⟩ := List.nodup_cons.mp hd
    rw [walk, ih hl]
    by_cases h : i = j
    · subst i
      simp [hj, flip]
    · simp [flip, h]

private theorem walk_coefficient (l : List (Fin g)) (s : Vertex g) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ t : Vertex g,
      (l.map gamma).prod s t = if t = walk l s then c else 0 := by
  induction l generalizing s with
  | nil =>
    exact ⟨1, one_ne_zero, fun t => by simp [walk, Matrix.one_apply, eq_comm]⟩
  | cons i l ih =>
    obtain ⟨c, hc, he⟩ := ih (flip i s)
    have hsign : sign i s ≠ 0 := by
      intro h
      simpa [h] using sign_square i s
    refine ⟨sign i s * c, mul_ne_zero hsign hc, fun t => ?_⟩
    by_cases h : t = walk l (flip i s) <;> simp [walk, gamma_mul_apply, he, h]

/-- This product lies in the full background algebra and crosses the cube in both directions. -/
theorem exists_corner_connector (g : ℕ) :
    ∃ x ∈ Algebra.adjoin ℂ (Set.range (@gamma g)),
      ∀ s : Vertex g, x s (fun i => !(s i)) ≠ 0 ∧
        ∀ t : Vertex g, t ≠ (fun i => !(s i)) → x s t = 0 := by
  classical
  let l := (Finset.univ : Finset (Fin g)).toList
  refine ⟨(l.map gamma).prod, ?_, ?_⟩
  · apply (Algebra.adjoin ℂ (Set.range (@gamma g))).list_prod_mem
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact Algebra.subset_adjoin ⟨i, rfl⟩
  · intro s
    have hw : walk l s = fun i => !(s i) := by
      funext i
      simp [walk_bit l (Finset.nodup_toList _) s i, l]
    obtain ⟨c, hc, he⟩ := walk_coefficient l s
    exact ⟨by simpa [he, hw] using hc, fun t ht => by simp [he, hw, ht]⟩

end
end MO35207.Cube

end

section

/-! Recovering coefficient-algebra entries within one color of a finite block background. -/

namespace MO35207
noncomputable section
open Polynomial

variable {I A : Type*} [Fintype I] [DecidableEq I] [Ring A] [Algebra ℂ A]

/-- Interpolation separates every port of a diagonal matrix with distinct scalar labels. -/
theorem scalar_diagonal_projectors (z : I → ℂ) (hz : Function.Injective z)
    (B : Subalgebra ℂ (Matrix I I A))
    (hD : Matrix.diagonal (fun i => algebraMap ℂ A (z i)) ∈ B) (i : I) :
    Matrix.single i i (1 : A) ∈ B := by
  classical
  let w : I → ℂ := Pi.single i 1
  let p := Lagrange.interpolate Finset.univ z w
  have heval (j : I) : p.eval (z j) = w j :=
    Lagrange.eval_interpolate_at_node w hz.injOn (Finset.mem_univ j)
  let a : I → A := fun j => algebraMap ℂ A (z j)
  let f : (I → A) →ₐ[ℂ] Matrix I I A := Matrix.diagonalAlgHom ℂ
  have hval : aeval (f a) p = Matrix.single i i (1 : A) := by
    rw [aeval_algHom_apply, ← Matrix.diagonal_single]
    apply congrArg (Matrix.diagonal (n := I))
    funext j
    change (aeval a p) j = (Pi.single i (1 : A) : I → A) j
    rw [aeval_pi_apply₂, show a j = algebraMap ℂ A (z j) from rfl,
      aeval_algebraMap_apply_eq_algebraMap_eval, heval]
    by_cases e : j = i <;> simp [w, e]
  rw [← hval]
  exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hD) (Polynomial.aeval_mem_adjoin_singleton _ _)

variable {C L : Type*} [Fintype C] [Fintype L] [DecidableEq C] [DecidableEq L]

def colorMixer : Matrix (C × L) (C × L) A :=
  fun p q => if p.1 = q.1 then 1 else 0

/-- Distinct scalar labels, within-color mixing, and the diagonal coefficient
matrices give independent access to the whole coefficient algebra in each color. -/
theorem colored_entry_mem (z : C × L → ℂ) (hz : Function.Injective z) (a : L → A)
    (B : Subalgebra ℂ (Matrix (C × L) (C × L) A))
    (hlabel : Matrix.diagonal (fun p => algebraMap ℂ A (z p)) ∈ B)
    (hmix : colorMixer ∈ B) (hdiag : Matrix.diagonal (fun p : C × L => a p.2) ∈ B)
    (c : C) {x : A} (hx : x ∈ Algebra.adjoin ℂ (Set.range a)) :
    ∀ i j : L, Matrix.single (c,i) (c,j) x ∈ B := by
  have hp := scalar_diagonal_projectors z hz B hlabel
  have he (i j : L) : Matrix.single (c,i) (c,j) (1 : A) ∈ B := by
    simpa [Matrix.single_mul_mul_single, colorMixer] using
      B.mul_mem (B.mul_mem (hp (c,i)) hmix) (hp (c,j))
  have hg (l : L) : Matrix.single (c,l) (c,l) (a l) ∈ B := by
    simpa [Matrix.single_mul_mul_single] using
      B.mul_mem (B.mul_mem (hp (c,l)) hdiag) (hp (c,l))
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨l, rfl⟩ := hx
    intro i j
    simpa only [Matrix.single_mul_single_same, one_mul, mul_one] using
      B.mul_mem (B.mul_mem (he i l) (hg l)) (he l j)
  | algebraMap r =>
    intro i j
    simpa only [Matrix.smul_single, Algebra.algebraMap_eq_smul_one] using B.smul_mem (he i j) r
  | add x y _ _ hx hy =>
    intro i j
    simpa only [Matrix.single_add] using B.add_mem (hx i j) (hy i j)
  | mul x y _ _ hx hy =>
    intro i j
    simpa only [Matrix.single_mul_single_same] using B.mul_mem (hx i i) (hy i j)

end
end MO35207

end

section

/-! Access to the specific full-word connector used in the encoding projection. -/

namespace MO35207
noncomputable section
variable {C L I A : Type*} [Fintype C] [Fintype L] [Fintype I]
  [DecidableEq C] [DecidableEq L] [DecidableEq I] [Ring A] [Algebra ℂ A]

/-- Write nested coefficient matrices in the same coordinates as the encoding column. -/
def flattenPorts : Matrix (C × L) (C × L) (Matrix I I A) ≃ₐ[ℂ]
    Matrix (C × L × I) (C × L × I) A :=
  (Matrix.compAlgEquiv (C × L) I A ℂ).trans (Matrix.reindexAlgEquiv ℂ A (Equiv.prodAssoc C L I))

private theorem flatten_single (c : C) (l : L) (M : Matrix I I ℂ) :
    flattenPorts (Matrix.single (c,l) (c,l) ((Algebra.ofId ℂ A).mapMatrix M)) =
      portConnector (A := A) c l M := by
  apply Matrix.ext
  rintro ⟨c₁,l₁,s⟩ ⟨c₂,l₂,t⟩
  change (if (c,l) = (c₁,l₁) ∧ (c,l) = (c₂,l₂) then
    (Algebra.ofId ℂ A).mapMatrix M else 0) s t = _
  by_cases h₁ : c₁ = c <;> by_cases h₂ : l₁ = l <;> by_cases h₃ : c₂ = c <;>
    by_cases h₄ : l₂ = l <;> simp_all [portConnector, eq_comm]

/-- The label, mixer and diagonal coefficient generators supply any word connector at a
chosen port. The coefficient matrices are first lifted to act identically on the inner space. -/
theorem connector_mem_background (z : C × L → ℂ) (hz : Function.Injective z)
    (a : L → Matrix I I ℂ) {M : Matrix I I ℂ} (hM : M ∈ Algebra.adjoin ℂ (Set.range a))
    (B : Subalgebra ℂ (Matrix (C × L × I) (C × L × I) A))
    (hlabel : flattenPorts (Matrix.diagonal fun p => algebraMap ℂ (Matrix I I A) (z p)) ∈ B)
    (hmix : flattenPorts (colorMixer : Matrix (C × L) (C × L) (Matrix I I A)) ∈ B)
    (hdiag : flattenPorts (Matrix.diagonal fun p : C × L => (Algebra.ofId ℂ A).mapMatrix (a p.2)) ∈ B)
    (c : C) (l : L) : portConnector (A := A) c l M ∈ B := by
  let φ : Matrix I I ℂ →ₐ[ℂ] Matrix I I A := (Algebra.ofId ℂ A).mapMatrix
  let B₀ := B.comap (flattenPorts (C := C) (L := L) (I := I) (A := A)).toAlgHom
  have hφ : φ M ∈ Algebra.adjoin ℂ (Set.range (φ ∘ a)) := by
    have hle : Algebra.adjoin ℂ (Set.range a) ≤ (Algebra.adjoin ℂ (Set.range (φ ∘ a))).comap φ := by
      apply Algebra.adjoin_le
      rintro _ ⟨i, rfl⟩
      exact Algebra.subset_adjoin ⟨i, rfl⟩
    exact hle hM
  rw [← flatten_single]
  exact colored_entry_mem z hz (φ ∘ a) B₀ hlabel hmix hdiag c hφ l l

end
end MO35207

end

section

/-! A complete dimension increase for one encoding using a word connector. -/

namespace MO35207
noncomputable section
variable {C L I A : Type*} [Fintype C] [Fintype L] [Fintype I]
  [DecidableEq C] [DecidableEq L] [DecidableEq I] [Nonempty C] [Nonempty L]
  [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [FiniteDimensional ℂ A] [Nontrivial A]

/-- The four pieces of the concrete background and encoding suffice to grow the dimension
of the inner generated algebra strictly. The two phases recover every old generator. -/
theorem stage_dimension_growth (lo hi spare : I) (hne : lo ≠ hi)
    (hs₁ : spare ≠ lo) (hs₂ : spare ≠ hi) (u : C → A) (hu : ∀ c, star (u c)*u c = 1)
    (z : (C × Bool) × L → ℂ) (hz : Function.Injective z) (a : L → Matrix I I ℂ)
    {M : Matrix I I ℂ} (hM : M ∈ Algebra.adjoin ℂ (Set.range a))
    (hll : M lo lo = 0) (hhh : M hi hi = 0) (hlh : M lo hi ≠ 0)
    (B : Subalgebra ℂ (Matrix ((C × Bool) × L × I) ((C × Bool) × L × I) A))
    (hlabel : flattenPorts (Matrix.diagonal fun p => algebraMap ℂ (Matrix I I A) (z p)) ∈ B)
    (hmix : flattenPorts (colorMixer : Matrix ((C × Bool) × L) ((C × Bool) × L) (Matrix I I A)) ∈ B)
    (hdiag : flattenPorts (Matrix.diagonal fun p : (C × Bool) × L => (Algebra.ofId ℂ A).mapMatrix (a p.2)) ∈ B)
    (hP : encodingColumn (L := L) lo hi (phaseCopies u) * encodingRow (L := L) lo hi (phaseCopies u) ∈ B) :
    Module.finrank ℂ (Algebra.adjoin ℂ (Set.range u)) < Module.finrank ℂ B := by
  classical
  let V := encodingColumn (L := L) lo hi (phaseCopies u)
  let W := encodingRow (L := L) lo hi (phaseCopies u)
  let σ : A →ₐ[ℂ] Matrix Unit Unit A := Matrix.scalarAlgHom Unit ℂ
  let T := Algebra.adjoin ℂ (Set.range (σ ∘ u))
  let A₀ := Algebra.adjoin ℂ (Set.range u)
  have hle : A₀ ≤ T.comap σ := by
    apply Algebra.adjoin_le
    rintro _ ⟨c, rfl⟩
    exact Algebra.subset_adjoin ⟨c, rfl⟩
  let f : A₀ →ₗ[ℂ] T := ((σ.comp A₀.val).codRestrict T (fun x => hle x.property)).toLinearMap
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun b : T => b.val () ()) h)
  apply (LinearMap.finrank_le_finrank_of_injective hf).trans_lt
  apply dimension_grows_in_proper_corner V W (encoding_retract lo hi hne _ (phaseCopies_isometry u hu))
    (encoding_proper lo hi spare hs₁ hs₂ _) (Set.range (σ ∘ u)) B hP
  rintro _ ⟨c, rfl⟩
  let l := Classical.arbitrary L
  exact two_color_recovery lo hi hne u hu c l M hll hhh hlh B hP
    (fun b => connector_mem_background z hz a hM B hlabel hmix hdiag (c,b) l)

/-- The signed cube supplies all of the connector data needed by the dimension theorem. -/
theorem cube_supplies_connector {g : ℕ} (hg : 2 ≤ g) :
    let lo : Cube.Vertex g := fun _ => false
    let hi : Cube.Vertex g := fun _ => true
    lo ≠ hi ∧ ∃ spare : Cube.Vertex g, spare ≠ lo ∧ spare ≠ hi ∧
      ∃ M ∈ Algebra.adjoin ℂ (Set.range (@Cube.gamma g)),
        M lo lo = 0 ∧ M hi hi = 0 ∧ M lo hi ≠ 0 := by
  dsimp only
  let i₀ : Fin g := ⟨0, by omega⟩
  let i₁ : Fin g := ⟨1, by omega⟩
  have hd : (fun _ : Fin g => false) ≠ (fun _ => true) := fun e => by
    simpa using congrFun e i₀
  refine ⟨hd, (fun i => decide (i = i₀)), ?_, ?_, ?_⟩
  · intro h
    simpa using congrFun h i₀
  · intro h
    have e := congrFun h i₁
    simp [i₁, i₀] at e
  · obtain ⟨M, hM, hc⟩ := Cube.exists_corner_connector g
    exact ⟨M, hM, (hc _).2 _ hd, (hc _).2 _ (Ne.symm hd), (hc _).1⟩

end
end MO35207

end

section

/-! Unitary choices for the labels, Clifford blocks, mixing, and encoding reflection. -/

namespace MO35207
noncomputable section

private def phaseLabel (r : ℝ) : ℂ := ((r : ℂ) + Complex.I) / ((r : ℂ) - Complex.I)

private theorem label_den (r : ℝ) : (r : ℂ) - Complex.I ≠ 0 := by
  intro h
  simpa using congrArg Complex.im h

private theorem label_num (r : ℝ) : (r : ℂ) + Complex.I ≠ 0 := by
  intro h
  simpa using congrArg Complex.im h

private theorem phaseLabel_injective : Function.Injective phaseLabel := by
  intro r s h
  have e := (div_eq_div_iff (label_den r) (label_den s)).mp h
  have him := congrArg Complex.im e
  simp [Complex.mul_im] at him
  linarith

private theorem phaseLabel_unitary (r : ℝ) : phaseLabel r ∈ unitary ℂ := by
  have hconj : star (phaseLabel r) = ((r : ℂ) - Complex.I) / ((r : ℂ) + Complex.I) := by
    simp [phaseLabel, sub_eq_add_neg]
  rw [Unitary.mem_iff, hconj]
  unfold phaseLabel
  constructor <;> field_simp [label_den, label_num]

/-- Distinct unitary labels exist for every finite set of ports. -/
theorem finite_unitary_labels (I : Type*) [Fintype I] :
    ∃ z : I → ℂ, Function.Injective z ∧ ∀ i, z i ∈ unitary ℂ := by
  let f (i : I) : ℝ := ((Fintype.equivFin I i).val : ℝ)
  have hf : Function.Injective f := by
    intro i j h
    apply (Fintype.equivFin I).injective
    apply Fin.ext
    dsimp [f] at h
    exact_mod_cast h
  exact ⟨phaseLabel ∘ f, phaseLabel_injective.comp hf, fun i => phaseLabel_unitary (f i)⟩

/-- The reflection in a self-adjoint idempotent is a self-adjoint unitary. -/
theorem reflection_unitary {D : Type*} [Ring D] [StarRing D] (P : D)
    (hsa : IsSelfAdjoint P) (hP : P*P = P) : P + P - 1 ∈ unitary D := by
  have hs : star (P + P - 1) = P + P - 1 := by simp [hsa.star_eq]
  have hsquare : (P+P-1)*(P+P-1) = 1 := by
    calc
      _ = 1 + (P*P-P) + (P*P-P) + (P*P-P) + (P*P-P) := by noncomm_ring
      _ = 1 := by simp [hP]
  rw [Unitary.mem_iff, hs]
  exact ⟨hsquare, hsquare⟩

variable {C L : Type*} [Fintype C] [Fintype L] [DecidableEq C] [DecidableEq L]

omit [DecidableEq L] in
private theorem colorMixer_square :
    (colorMixer : Matrix (C × L) (C × L) ℂ) * colorMixer = (Fintype.card L : ℂ) • colorMixer := by
  apply Matrix.ext
  rintro ⟨c,i⟩ ⟨d,j⟩
  by_cases h : c = d <;> simp [Matrix.mul_apply, colorMixer, Fintype.sum_prod_type, h,
    mul_ite, Matrix.smul_apply, eq_comm]

/-- Turning the uniform within-color mixing matrix into a reflection gives a unitary. -/
theorem mixer_reflection_unitary [Nonempty L] :
    let P := (Fintype.card L : ℂ)⁻¹ • (colorMixer : Matrix (C × L) (C × L) ℂ)
    P+P-1 ∈ unitary (Matrix (C × L) (C × L) ℂ) := by
  dsimp only
  apply reflection_unitary
  · apply Matrix.ext
    rintro ⟨c,i⟩ ⟨d,j⟩
    change star (_ * (if d = c then (1 : ℂ) else 0)) = _ * (if c = d then 1 else 0)
    by_cases h : c = d <;> simp [h, Ne.symm]
  · simp only [Matrix.smul_mul, Matrix.mul_smul, colorMixer_square, smul_smul]
    have hn : (Fintype.card L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [hn]

end
end MO35207

end

section

/-! The four operators of one concrete encoding stage. -/

namespace MO35207
noncomputable section

abbrev StageColors := Fin 4 × Bool
abbrev StageSpace (L I : Type*) := StageColors × L × I

variable {L I A : Type*} [Fintype L] [Fintype I] [DecidableEq L] [DecidableEq I]
  [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

private def labelMatrix (z : StageColors × L → ℂ) : Matrix (StageSpace L I) (StageSpace L I) A :=
  flattenPorts (Matrix.diagonal fun p => algebraMap ℂ (Matrix I I A) (z p))

private def mixingMatrix : Matrix (StageSpace L I) (StageSpace L I) A :=
  flattenPorts (colorMixer : Matrix (StageColors × L) (StageColors × L) (Matrix I I A))

private def coefficientMatrix (a : L → Matrix I I ℂ) : Matrix (StageSpace L I) (StageSpace L I) A :=
  flattenPorts (Matrix.diagonal fun p : StageColors × L => (Algebra.ofId ℂ A).mapMatrix (a p.2))

private def imageProjection (lo hi : I) (u : Fin 4 → A) : Matrix (StageSpace L I) (StageSpace L I) A :=
  encodingColumn (L := L) lo hi (phaseCopies u) * encodingRow (L := L) lo hi (phaseCopies u)

private def refl {D : Type*} [Ring D] (x : D) := x+x-1

/-- The label, mixing reflection, coefficient operator, and encoding reflection.
The tuple always has four entries, independent of the cube and the inner dimension. -/
def stageTuple (lo hi : I) (u : Fin 4 → A) (z : StageColors × L → ℂ) (a : L → Matrix I I ℂ) :
    Fin 4 → Matrix (StageSpace L I) (StageSpace L I) A :=
  ![labelMatrix z, refl ((Fintype.card L : ℂ)⁻¹ • mixingMatrix), coefficientMatrix a,
    refl (imageProjection lo hi u)]

private theorem mem_of_refl {D : Type*} [Ring D] [Algebra ℂ D]
    (B : Subalgebra ℂ D) (x : D) (h : refl x ∈ B) : x ∈ B := by
  have he : x+x ∈ B := by simpa [refl] using B.add_mem h B.one_mem
  have hhalf := B.smul_mem he ((2:ℂ)⁻¹)
  convert hhalf using 1
  module

/-- The explicitly generated four-operator algebra grows at one step. -/
theorem stageTuple_grows [Nonempty L] [FiniteDimensional ℂ A] [Nontrivial A]
    (lo hi spare : I) (hne : lo ≠ hi) (hs₁ : spare ≠ lo) (hs₂ : spare ≠ hi)
    (u : Fin 4 → A) (hu : ∀ c, star (u c)*u c = 1)
    (z : StageColors × L → ℂ) (hz : Function.Injective z) (a : L → Matrix I I ℂ)
    {M : Matrix I I ℂ} (hM : M ∈ Algebra.adjoin ℂ (Set.range a))
    (hll : M lo lo = 0) (hhh : M hi hi = 0) (hlh : M lo hi ≠ 0) :
    Module.finrank ℂ (Algebra.adjoin ℂ (Set.range u)) <
      Module.finrank ℂ (Algebra.adjoin ℂ (Set.range (stageTuple lo hi u z a))) := by
  let t := stageTuple lo hi u z a
  let B := Algebra.adjoin ℂ (Set.range t)
  have h (i : Fin 4) : t i ∈ B := Algebra.subset_adjoin ⟨i, rfl⟩
  have hm := mem_of_refl B _ (show refl ((Fintype.card L : ℂ)⁻¹ • mixingMatrix) ∈ B from h 1)
  have hn : (Fintype.card L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply stage_dimension_growth lo hi spare hne hs₁ hs₂ u hu z hz a hM hll hhh hlh B
  · exact h 0
  · simpa [smul_smul, hn, mixingMatrix] using B.smul_mem hm (Fintype.card L : ℂ)
  · exact h 2
  · exact mem_of_refl B _ (h 3)

private theorem unitary_map {D E : Type*} [Ring D] [StarRing D] [Algebra ℂ D]
    [Ring E] [StarRing E] [Algebra ℂ E] (φ : D →ₐ[ℂ] E) (hstar : ∀ x, star (φ x) = φ (star x))
    {x : D} (hx : x ∈ unitary D) : φ x ∈ unitary E := by
  rw [Unitary.mem_iff, hstar, ← map_mul, ← map_mul, hx.1, hx.2, map_one]
  exact ⟨rfl,rfl⟩

private theorem scalar_map_unitary {D : Type*} [Ring D] [StarRing D] [Algebra ℂ D] [StarModule ℂ D]
    {z : ℂ} (hz : z ∈ unitary ℂ) : algebraMap ℂ D z ∈ unitary D :=
  unitary_map (Algebra.ofId ℂ D) (fun z => (algebraMap_star_comm z (A := D)).symm) hz

private theorem scalar_matrix_map_unitary {J D : Type*} [Fintype J] [DecidableEq J]
    [Ring D] [StarRing D] [Algebra ℂ D] [StarModule ℂ D] {M : Matrix J J ℂ}
    (hM : M ∈ unitary (Matrix J J ℂ)) : (Algebra.ofId ℂ D).mapMatrix M ∈ unitary (Matrix J J D) := by
  apply unitary_map _ _ hM
  intro x
  apply Matrix.ext
  intro i j
  exact (algebraMap_star_comm (x j i) (A := D)).symm

private theorem diagonal_unitary {J D : Type*} [Fintype J] [DecidableEq J] [Ring D] [StarRing D]
    (x : J → D) (hx : ∀ j, x j ∈ unitary D) : Matrix.diagonal x ∈ unitary (Matrix J J D) := by
  rw [Unitary.mem_iff]
  change (Matrix.diagonal x).conjTranspose * Matrix.diagonal x = 1 ∧
    Matrix.diagonal x * (Matrix.diagonal x).conjTranspose = 1
  simp only [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  constructor
  · rw [← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext (fun j => (hx j).1))
  · rw [← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext (fun j => (hx j).2))

omit [StarModule ℂ A] in
private theorem flatten_unitary {x : Matrix (StageColors × L) (StageColors × L) (Matrix I I A)}
    (hx : x ∈ unitary _) : flattenPorts x ∈ unitary (Matrix (StageSpace L I) (StageSpace L I) A) :=
  unitary_map flattenPorts.toAlgHom (fun _ => rfl) hx

theorem stageTuple_unitary [Nonempty L] (lo hi : I) (hne : lo ≠ hi)
    (u : Fin 4 → A) (hu : ∀ c, u c ∈ unitary A) (z : StageColors × L → ℂ)
    (hz : ∀ p, z p ∈ unitary ℂ) (a : L → Matrix I I ℂ) (ha : ∀ l, a l ∈ unitary _) :
    ∀ i, stageTuple lo hi u z a i ∈ unitary _ := by
  intro i
  fin_cases i
  · exact flatten_unitary (diagonal_unitary _ (fun p => scalar_map_unitary (hz p)))
  · let N := Fintype.card L
    let f : Matrix (StageColors × L) (StageColors × L) ℂ →ₐ[ℂ]
        Matrix (StageColors × L) (StageColors × L) (Matrix I I A) :=
      (Algebra.ofId ℂ (Matrix I I A)).mapMatrix
    let B₀ : Matrix (StageColors × L) (StageColors × L) ℂ := colorMixer
    have hmap : f B₀ = colorMixer := by
      apply Matrix.ext
      intro p q
      change algebraMap ℂ (Matrix I I A) (if p.1 = q.1 then 1 else 0) = _
      by_cases hpq : p.1 = q.1 <;> simp [hpq, colorMixer]
    have hm : refl ((N : ℂ)⁻¹ • B₀) ∈ unitary _ := mixer_reflection_unitary
    have result := flatten_unitary (scalar_matrix_map_unitary (D := Matrix I I A) hm)
    change flattenPorts (f (refl ((N : ℂ)⁻¹ • B₀))) ∈ unitary _ at result
    change refl ((N : ℂ)⁻¹ • (mixingMatrix : Matrix (StageSpace L I) (StageSpace L I) A)) ∈ unitary _
    simpa only [refl, map_sub, map_add, map_smul, map_one, hmap, mixingMatrix] using result
  · exact flatten_unitary (diagonal_unitary _ (fun p => scalar_matrix_map_unitary (ha p.2)))
  · exact reflection_unitary _ (encoding_selfAdjoint lo hi (phaseCopies u))
      (encoding_squared lo hi hne (phaseCopies u) (phaseCopies_isometry u (fun c => (hu c).1)))

/-- The part of the four generators that is independent of the inner matrix model. -/
def stageBackground (z : StageColors × L → ℂ) (a : L → Matrix I I ℂ) :
    Fin 4 → Matrix (StageSpace L I) (StageSpace L I) ℂ :=
  ![labelMatrix z, refl ((Fintype.card L : ℂ)⁻¹ • mixingMatrix), coefficientMatrix a, -1]

/-- Entries of the scalar background before introducing the inner tuple. -/
theorem background_entries (z : StageColors × L → ℂ) (a : L → Matrix I I ℂ)
    (c d : StageColors) (l k : L) (s t : I) :
    let δ := (1 : Matrix I I ℂ) s t
    let same := (c,l) = (d,k)
    stageBackground z a 0 (c,l,s) (d,k,t) = (if same then z (c,l)*δ else 0) ∧
    stageBackground z a 1 (c,l,s) (d,k,t) =
      (2*(Fintype.card L : ℂ)⁻¹)*(if c=d then δ else 0) - (if same then δ else 0) ∧
    stageBackground z a 2 (c,l,s) (d,k,t) = (if same then a l s t else 0) ∧
    stageBackground z a 3 (c,l,s) (d,k,t) = -(if same then δ else 0) := by
  dsimp only
  have hl : labelMatrix (I := I) (A := ℂ) z (c,l,s) (d,k,t) =
      (if (c,l)=(d,k) then z (c,l)*(1 : Matrix I I ℂ) s t else 0) := by
    change (Matrix.diagonal (fun p => algebraMap ℂ (Matrix I I ℂ) (z p))) (c,l) (d,k) s t = _
    by_cases h : (c,l)=(d,k) <;> simp [h, Algebra.algebraMap_eq_smul_one]
  have hm : (mixingMatrix (A := ℂ) : Matrix (StageSpace L I) (StageSpace L I) ℂ)
      (c,l,s) (d,k,t) = (if c=d then (1 : Matrix I I ℂ) s t else 0) := by
    change ((if c=d then (1 : Matrix I I ℂ) else 0) s t) = _
    by_cases h : c=d <;> simp [h]
  have ha : coefficientMatrix (A := ℂ) a (c,l,s) (d,k,t) =
      (if (c,l)=(d,k) then a l s t else 0) := by
    change (Matrix.diagonal fun p : StageColors × L =>
      (Algebra.ofId ℂ ℂ).mapMatrix (a p.2)) (c,l) (d,k) s t = _
    by_cases h : (c,l)=(d,k)
    · have hlk : l=k := congrArg Prod.snd h
      have hcd : c=d := congrArg Prod.fst h
      subst d; subst k
      simp
    · simp [h]
  have h1 : (1 : Matrix (StageSpace L I) (StageSpace L I) ℂ) (c,l,s) (d,k,t) =
      (if (c,l)=(d,k) then (1 : Matrix I I ℂ) s t else 0) := by
    by_cases h : c=d <;> by_cases h' : l=k <;> simp [Matrix.one_apply, Prod.mk.injEq, h, h']
  refine ⟨hl, ?_, ha, ?_⟩
  · change _ + _ - (1 : Matrix (StageSpace L I) (StageSpace L I) ℂ) (c,l,s) (d,k,t) = _
    rw [h1]
    change (Fintype.card L : ℂ)⁻¹ * mixingMatrix (c,l,s) (d,k,t) +
      (Fintype.card L : ℂ)⁻¹ * mixingMatrix (c,l,s) (d,k,t) - _ = _
    rw [hm]
    ring
  · exact congrArg Neg.neg h1

omit [StarRing A] [StarModule ℂ A] in
private theorem lift_label (z : StageColors × L → ℂ) :
    (Algebra.ofId ℂ A).mapMatrix (labelMatrix (I := I) z) = labelMatrix z := by
  apply Matrix.ext
  rintro ⟨c,l,s⟩ ⟨d,k,t⟩
  change algebraMap ℂ A ((Matrix.diagonal (fun p => algebraMap ℂ (Matrix I I ℂ) (z p)))
    (c,l) (d,k) s t) = Matrix.diagonal (fun p => algebraMap ℂ (Matrix I I A) (z p)) (c,l) (d,k) s t
  by_cases h : (c,l) = (d,k) <;> by_cases h' : s=t <;>
    simp [h, h', Algebra.algebraMap_eq_smul_one]

omit [StarRing A] [StarModule ℂ A] in
private theorem lift_mixing :
    (Algebra.ofId ℂ A).mapMatrix (mixingMatrix (L := L) (I := I)) = mixingMatrix := by
  apply Matrix.ext
  rintro ⟨c,l,s⟩ ⟨d,k,t⟩
  change algebraMap ℂ A ((if c=d then (1 : Matrix I I ℂ) else 0) s t) =
    (if c=d then (1 : Matrix I I A) else 0) s t
  by_cases h : c=d <;> by_cases h' : s=t <;> simp [h, h', Matrix.one_apply]

omit [StarRing A] [StarModule ℂ A] in
private theorem lift_coefficient (a : L → Matrix I I ℂ) :
    (Algebra.ofId ℂ A).mapMatrix (coefficientMatrix a) = coefficientMatrix a := by
  apply Matrix.ext
  rintro ⟨c,l,s⟩ ⟨d,k,t⟩
  change algebraMap ℂ A ((Matrix.diagonal (fun p : StageColors × L =>
    (Algebra.ofId ℂ ℂ).mapMatrix (a p.2))) (c,l) (d,k) s t) =
    Matrix.diagonal (fun p : StageColors × L => (Algebra.ofId ℂ A).mapMatrix (a p.2)) (c,l) (d,k) s t
  by_cases h : (c,l) = (d,k) <;> simp [h, AlgHom.mapMatrix_apply]

omit [StarModule ℂ A] in
/-- Precisely the last generator differs from the scalar background, by twice the
encoding projection. -/
theorem stageTuple_background (lo hi : I) (u : Fin 4 → A) (z : StageColors × L → ℂ)
    (a : L → Matrix I I ℂ) (i : Fin 4) :
    stageTuple lo hi u z a i = (Algebra.ofId ℂ A).mapMatrix (stageBackground z a i) +
      (if i=3 then (2:ℂ) else 0) •
        (encodingColumn (L := L) lo hi (phaseCopies u) * encodingRow (L := L) lo hi (phaseCopies u)) := by
  fin_cases i
  · simpa [stageTuple, stageBackground] using (lift_label (I := I) (A := A) z).symm
  · change refl ((Fintype.card L : ℂ)⁻¹ • mixingMatrix) =
      (Algebra.ofId ℂ A).mapMatrix (refl ((Fintype.card L : ℂ)⁻¹ • mixingMatrix)) + (0:ℂ) • _
    simp only [refl, map_sub, map_add, map_smul, map_one, lift_mixing, zero_smul, add_zero]
  · simpa [stageTuple, stageBackground] using (lift_coefficient (A := A) a).symm
  · simp only [stageTuple, stageBackground, Matrix.cons_val,
      Fin.reduceFinMk, ite_true, map_neg, map_one, refl, imageProjection, two_smul]
    abel

end
end MO35207

end

section

/-! Algebraicity on an uncountable real pencil extends to its complex pencil. -/

namespace MO35207
open Polynomial
open scoped Polynomial

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- Scalar polynomial obtained from a power of a pencil by applying a linear functional.
The two coefficients of the pencil need not commute. -/
private noncomputable def pencilPower (u v : A) (L : A →ₗ[ℂ] ℂ) : ℕ → ℂ[X]
  | 0 => C (L 1)
  | n + 1 =>
    pencilPower u v (L.comp (LinearMap.mulRight ℂ u)) n +
    X * pencilPower u v (L.comp (LinearMap.mulRight ℂ v)) n

private theorem pencilPower_eval (u v : A) (L : A →ₗ[ℂ] ℂ) (n : ℕ) (z : ℂ) :
    (pencilPower u v L n).eval z = L ((u + z • v) ^ n) := by
  induction n generalizing L with
  | zero => simp [pencilPower]
  | succ n ih =>
    simp [pencilPower, ih, pow_succ, mul_add]

private theorem powers_not_independent {x : A} {p : ℂ[X]} (hp : p ≠ 0) (hz : aeval x p = 0) :
    ¬ LinearIndependent ℂ (fun i : Fin (p.natDegree + 1) => x ^ (i : ℕ)) := by
  intro h
  have hs : ∑ i : Fin (p.natDegree + 1), p.coeff i • x ^ (i : ℕ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => p.coeff i • x ^ i), ← aeval_eq_sum_range]
    exact hz
  have htop := Fintype.linearIndependent_iff.mp h (fun i => p.coeff i) hs (Fin.last p.natDegree)
  exact (leadingCoeff_ne_zero.mpr hp) htop

/-- If one complex specialization is transcendental, a nonzero scalar determinant
certifies independence of its first d powers and does so off a finite exceptional set. -/
private theorem pencil_minor (u v : A) (z₀ : ℂ) (ht : Transcendental ℂ (u + z₀ • v)) (d : ℕ) :
    ∃ q : ℂ[X], q ≠ 0 ∧ ∀ z : ℂ, q.eval z ≠ 0 →
      LinearIndependent ℂ (fun i : Fin d => (u + z • v) ^ (i : ℕ)) := by
  classical
  let x := u + z₀ • v
  let e := (aeval (R := ℂ) x).toLinearMap
  obtain ⟨g, hg⟩ := e.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp ht))
  let L (i : Fin d) := (lcoeff ℂ i).comp g
  let M : Matrix (Fin d) (Fin d) ℂ[X] := fun i j => pencilPower u v (L j) i
  have hentry (z : ℂ) (i j : Fin d) :
      (M.map (evalRingHom z)) i j = L j ((u + z • v) ^ (i : ℕ)) :=
    pencilPower_eval u v _ _ _
  have hidentity : M.map (evalRingHom z₀) = 1 := by
    ext i j
    rw [hentry]
    have hx : g (x ^ (i : ℕ)) = X ^ (i : ℕ) := by
      simpa [e] using DFunLike.congr_fun hg (X ^ (i : ℕ))
    change (g (x ^ (i : ℕ))).coeff j = _
    rw [hx, coeff_X_pow, Matrix.one_apply]
    simp [Fin.ext_iff, eq_comm]
  refine ⟨M.det, ?_, ?_⟩
  · intro h
    have hbad : evalRingHom z₀ M.det = (M.map (evalRingHom z₀)).det :=
      (evalRingHom z₀).map_det M
    rw [h, map_zero, hidentity, Matrix.det_one] at hbad
    exact zero_ne_one hbad
  · intro z hz
    have hdet : (M.map (evalRingHom z)).det ≠ 0 := by
      exact fun h => hz (((evalRingHom z).map_det M).trans h)
    apply LinearIndependent.of_comp (LinearMap.pi L)
    change LinearIndependent ℂ (fun (i j : Fin d) => L j ((u + z • v) ^ (i : ℕ)))
    simpa only [← hentry] using Matrix.linearIndependent_rows_of_det_ne_zero hdet

/-- Real specializations form an uncountable set. If they are all algebraic,
every complex specialization is algebraic, even in a noncommutative algebra. -/
theorem algebraic_complex_pencil (u v : A)
    (hr : ∀ r : ℝ, IsAlgebraic ℂ (u + (r : ℂ) • v)) (z₀ : ℂ) :
    IsAlgebraic ℂ (u + z₀ • v) := by
  classical
  by_contra ht
  choose q hq hli using pencil_minor u v z₀ ht
  let bad (d : ℕ) : Set ℝ := {r | (q d).IsRoot (r : ℂ)}
  have hcount : (⋃ d, bad d).Countable := Set.countable_iUnion fun d =>
    (finite_setOfPred_isRoot (hq d)).countable.preimage Complex.ofReal_injective
  apply (Set.not_countable_univ (α := ℝ))
  apply hcount.mono
  intro r _
  obtain ⟨p, hp, hz⟩ := hr r
  apply Set.mem_iUnion.mpr
  refine ⟨p.natDegree + 1, ?_⟩
  by_contra h
  exact powers_not_independent hp hz (hli _ _ h)

end MO35207

end

section

/-! Reductions for the published MO-35207 statement. -/

namespace MO35207

/-- A polynomial identity in the algebra bounds the spectrum by its scalar roots. -/
theorem finiteSpectrum_of_algebraic {A : Type*} [Ring A] [Algebra ℂ A]
    {x : A} (hx : IsAlgebraic ℂ x) : (spectrum ℂ x).Finite := by
  rcases subsingleton_or_nontrivial A with h | h
  · simp [spectrum.of_subsingleton]
  obtain ⟨p, hp, hzero⟩ := hx
  refine (Polynomial.finite_setOfPred_isRoot hp).subset ?_
  intro z hz
  have hmem := spectrum.subset_polynomial_aeval x p ⟨z, hz, rfl⟩
  rw [hzero, spectrum.zero_eq] at hmem
  exact hmem

/-- Taking the norm closure of an algebraic example gives the C*-algebra
quantified over by the board. All spectra in the conclusion are internal
to this closure. -/
theorem disproof_of_algebraic_adjoin {D : Type} [CStarAlgebra D]
    {n : ℕ} (a : Fin n → D) (hn : ∀ i, IsStarNormal (a i))
    (halg : ∀ b ∈ StarAlgebra.adjoin ℂ (Set.range a), IsAlgebraic ℂ b)
    (hinf : ¬ FiniteDimensional ℂ (StarAlgebra.adjoin ℂ (Set.range a))) :
    ¬ (type_of% @OMA.S_mo_35207.main) := by
  intro hmain
  let B := StarAlgebra.adjoin ℂ (Set.range a)
  let C := B.topologicalClosure
  let : IsClosed (C : Set D) := B.isClosed_topologicalClosure
  let g (i : Fin n) : C :=
    ⟨a i, B.le_topologicalClosure (StarAlgebra.subset_adjoin ℂ _ ⟨i, rfl⟩)⟩
  let S := StarAlgebra.adjoin ℂ (Set.range g)
  have himage : C.subtype '' (S : Set C) = (B : Set D) := by
    change ((S.map C.subtype : StarSubalgebra ℂ D) : Set D) = _
    congr 1
    change (StarAlgebra.adjoin ℂ (Set.range g)).map C.subtype = _
    rw [StarAlgHom.map_adjoin, ← Set.range_comp]
    rfl
  have hdense : closure (S : Set C) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    apply closure_subtype.mpr
    change (x : D) ∈ closure (C.subtype '' (S : Set C))
    rw [himage]
    exact x.property
  have hnormal (i : Fin n) : IsStarNormal (g i) :=
    ⟨Subtype.ext (hn i).star_comm_self.eq⟩
  have hspectrum (b : C) (hb : b ∈ S) : (spectrum ℂ b).Finite := by
    have hamb : (b : D) ∈ (B : Set D) := by
      rw [← himage]
      exact ⟨b, hb, rfl⟩
    apply finiteSpectrum_of_algebraic
    exact (isAlgebraic_algHom_iff C.subtype.toAlgHom Subtype.val_injective).mp (halg b hamb)
  let : FiniteDimensional ℂ C := hmain C n g hnormal hdense hspectrum
  exact hinf (FiniteDimensional.of_injective
    (StarSubalgebra.inclusion B.le_topologicalClosure).toAlgHom.toLinearMap
    (StarSubalgebra.inclusion_injective B.le_topologicalClosure))

/-- Surjective finite-dimensional images of unbounded dimension witness
that the algebraic star-subalgebra is infinite-dimensional. -/
theorem not_finiteDimensional_of_quotients {V : Type*} [AddCommGroup V] [Module ℂ V]
    {M : ℕ → Type*} [∀ j, AddCommGroup (M j)] [∀ j, Module ℂ (M j)]
    (q : (j : ℕ) → V →ₗ[ℂ] M j) (hsurj : ∀ j, Function.Surjective (q j))
    (hgrow : ∀ d : ℕ, ∃ j, d < Module.finrank ℂ (M j)) :
    ¬ FiniteDimensional ℂ V := by
  intro h
  obtain ⟨j, hj⟩ := hgrow (Module.finrank ℂ V)
  exact hj.not_ge (LinearMap.finrank_le_finrank_of_surjective (hsurj j))

end MO35207

end

section

/-! Evaluation in a bounded product of noncommutative C*-algebras. -/

open scoped ENNReal Polynomial
namespace MO35207

section
variable {D : Type*} [Ring D] [StarRing D] [Algebra ℂ D] [StarModule ℂ D]
variable {ι : Type*} {a : ι → D}

/-- For self-adjoint generators, ordinary noncommutative polynomials
already describe the entire algebraic star-subalgebra. -/
theorem adjoin_selfAdjoint_eq_range (ha : ∀ i, IsSelfAdjoint (a i)) :
    (StarAlgebra.adjoin ℂ (Set.range a)).toSubalgebra = (FreeAlgebra.lift ℂ a).range := by
  rw [StarAlgebra.adjoin_toSubalgebra]
  have h : star (Set.range a) = Set.range a := by
    ext x
    change star x ∈ Set.range a ↔ x ∈ Set.range a
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, (ha i).symm.trans (by simpa using congrArg star hi)⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, (ha i).symm⟩
  rw [h, Set.union_self, Algebra.adjoin_range_eq_range_freeAlgebra_lift]

/-- Ordinary free polynomials in generators and their adjoints represent star polynomials. -/
def withAdjoints (a : ι → D) : ι ⊕ ι → D := Sum.elim a (star ∘ a)

theorem adjoin_eq_range_withAdjoints (a : ι → D) :
    (StarAlgebra.adjoin ℂ (Set.range a)).toSubalgebra =
      (FreeAlgebra.lift ℂ (withAdjoints a)).range := by
  rw [StarAlgebra.adjoin_toSubalgebra, ← Algebra.adjoin_range_eq_range_freeAlgebra_lift]
  congr 1
  ext x
  constructor
  · rintro (⟨i, rfl⟩ | hx)
    · exact ⟨Sum.inl i, rfl⟩
    · obtain ⟨i, hi⟩ := (show star x ∈ Set.range a from hx)
      exact ⟨Sum.inr i, by simpa [withAdjoints] using congrArg star hi⟩
  · rintro ⟨i | i, rfl⟩
    · exact Or.inl ⟨i, rfl⟩
    · right
      change star (star (a i)) ∈ Set.range a
      simp
end

noncomputable section
variable {M : ℕ → Type} [∀ j, CStarAlgebra (M j)] [∀ j, Nontrivial (M j)]

/-- Point evaluation respects multiplication, scalars and adjoints in the bounded product. -/
def coordinate (j : ℕ) : lp M ∞ →⋆ₐ[ℂ] M j where
  toFun x := x j
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

theorem coordinate_lift {ι : Type*} (a : ι → lp M ∞) (j : ℕ)
    (p : FreeAlgebra ℂ ι) :
    coordinate j (FreeAlgebra.lift ℂ a p) = FreeAlgebra.lift ℂ (fun i => a i j) p := by
  have h : (coordinate j).toAlgHom.comp (FreeAlgebra.lift ℂ a) =
      FreeAlgebra.lift ℂ (fun i => a i j) := by
    apply FreeAlgebra.hom_ext
    funext i
    simp [Function.comp_apply, coordinate]
    rfl
  exact DFunLike.congr_fun h p

/-- One annihilator per noncommutative polynomial, shared by every
coordinate, suffices when the algebras generated at individual coordinates
have unbounded dimension. -/
theorem disproof_of_uniform_annihilators {n : ℕ} {ι : Type*}
    (g : Fin n → lp M ∞) (hn : ∀ i, IsStarNormal (g i)) (a : ι → lp M ∞)
    (hstar : (StarAlgebra.adjoin ℂ (Set.range g)).toSubalgebra = (FreeAlgebra.lift ℂ a).range)
    (hgrow : ∀ d : ℕ, ∃ j, d < Module.finrank ℂ (FreeAlgebra.lift ℂ (fun i => a i j)).range)
    (hpoly : ∀ p : FreeAlgebra ℂ ι, ∃ f : ℂ[X], f ≠ 0 ∧
      ∀ j, Polynomial.aeval (FreeAlgebra.lift ℂ (fun i => a i j) p) f = 0) :
    ¬ (type_of% @OMA.S_mo_35207.main) := by
  let : CStarAlgebra (lp M ∞) := {}
  apply disproof_of_algebraic_adjoin g hn
  · intro b hb
    change b ∈ (StarAlgebra.adjoin ℂ (Set.range g)).toSubalgebra at hb
    rw [hstar] at hb
    obtain ⟨p, rfl⟩ := hb
    obtain ⟨f, hf, hz⟩ := hpoly p
    refine ⟨f, hf, ?_⟩
    apply lp.ext
    funext j
    calc
      (coordinate j).toAlgHom (Polynomial.aeval (FreeAlgebra.lift ℂ a p) f) =
          Polynomial.aeval (coordinate j (FreeAlgebra.lift ℂ a p)) f :=
        (Polynomial.aeval_algHom_apply _ _ _).symm
      _ = 0 := by rw [coordinate_lift, hz]
  · let B := StarAlgebra.adjoin ℂ (Set.range g)
    let E (j : ℕ) := (FreeAlgebra.lift ℂ (fun i => a i j)).range
    have himage (j : ℕ) (x : B) : coordinate j x.val ∈ E j := by
      have hx : x.val ∈ (StarAlgebra.adjoin ℂ (Set.range g)).toSubalgebra := x.property
      rw [hstar] at hx
      obtain ⟨p, hp⟩ := hx
      exact ⟨p, (coordinate_lift a j p).symm.trans (congrArg (coordinate j) hp)⟩
    let q (j : ℕ) := (((coordinate j).comp B.subtype).toAlgHom.codRestrict (E j)
      (himage j)).toLinearMap
    apply not_finiteDimensional_of_quotients q _ hgrow
    intro j y
    obtain ⟨p, hp⟩ := y.property
    refine ⟨⟨FreeAlgebra.lift ℂ a p, ?_⟩, Subtype.ext ((coordinate_lift a j p).trans hp)⟩
    change FreeAlgebra.lift ℂ a p ∈ (StarAlgebra.adjoin ℂ (Set.range g)).toSubalgebra
    rw [hstar]
    exact ⟨p, rfl⟩

end
end MO35207

end

section

/-! Uniform spectra of real parts in finite-dimensional quotients suffice for MO-35207. -/

namespace MO35207
open Polynomial
open scoped Polynomial ENNReal

noncomputable section

/-- The real part expressed using only complex scalars. -/
def hermitianPart {A : Type*} [Add A] [Star A] [SMul ℂ A] (b : A) : A :=
  (2 : ℂ)⁻¹ • (b + star b)

private theorem hermitianPart_sa {A : Type*} [Ring A] [StarRing A]
    [Algebra ℂ A] [StarModule ℂ A] (b : A) : IsSelfAdjoint (hermitianPart b) := by
  simp [IsSelfAdjoint, hermitianPart, star_smul, add_comm]

private theorem hermitianPart_pencil {A : Type*} [Ring A] [StarRing A]
    [Algebra ℂ A] [StarModule ℂ A] (b : A) (r : ℝ) :
    hermitianPart b + (r : ℂ) • hermitianPart (-Complex.I • b) =
      hermitianPart ((1 - (r : ℂ) * Complex.I) • b) := by
  simp only [hermitianPart, star_smul, star_neg, Complex.star_def,
    Complex.conj_I, neg_neg, map_sub, map_one, map_mul, Complex.conj_ofReal]
  module

private theorem hermitianPart_recombine {A : Type*} [Ring A] [StarRing A]
    [Algebra ℂ A] [StarModule ℂ A] (b : A) :
    hermitianPart b + Complex.I • hermitianPart (-Complex.I • b) = b := by
  simp only [hermitianPart, star_smul, star_neg, Complex.star_def,
    Complex.conj_I, neg_neg]
  rw [smul_comm Complex.I ((2 : ℂ)⁻¹)]
  simp only [smul_add, smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul, neg_one_smul]
  module

variable {M : ℕ → Type} [∀ j, CStarAlgebra (M j)] [∀ j, Nontrivial (M j)]

/-- A single spectral set for a family of normal coordinates gives one
annihilator in the bounded product, independent of matrix size. -/
theorem algebraic_of_uniform_spectrum (b : lp M ∞)
    (hn : ∀ j, IsStarNormal (b j)) (S : Finset ℂ)
    (hs : ∀ j, spectrum ℂ (b j) ⊆ (S : Set ℂ)) : IsAlgebraic ℂ b := by
  classical
  let f : ℂ[X] := ∏ z ∈ S, (X - C z)
  refine ⟨f, (monic_prod_X_sub_C id S).ne_zero, ?_⟩
  apply lp.ext
  funext j
  change (coordinate j).toAlgHom (aeval b f) = 0
  rw [← aeval_algHom_apply]
  change aeval (b j) f = 0
  rw [← cfc_polynomial f (b j) (hn j), ← cfc_zero (R := ℂ) (b j)]
  apply cfc_congr
  intro z hz
  have hmem := hs j hz
  simp only [f, eval_prod, eval_sub, eval_X, eval_C, Pi.zero_apply]
  exact Finset.prod_eq_zero hmem (sub_self z)

/-- Finite spectra need only be controlled for the Hermitian parts of
ordinary noncommutative polynomials. This is the scalar-polynomial
specialization of the spectral estimate in Proposition 4.13 of
Yang, Hou and Fang, arXiv:2611.20690. -/
theorem disproof_of_presented_hermitian_spectra {n : ℕ} {ι : Type*}
    (g : Fin n → lp M ∞) (hn : ∀ i, IsStarNormal (g i)) (a : ι → lp M ∞)
    (hstar : (StarAlgebra.adjoin ℂ (Set.range g)).toSubalgebra = (FreeAlgebra.lift ℂ a).range)
    (hgrow : ∀ d : ℕ, ∃ j, d < Module.finrank ℂ (FreeAlgebra.lift ℂ (fun i => a i j)).range)
    (hspec : ∀ p : FreeAlgebra ℂ ι, ∃ S : Finset ℂ, ∀ j,
      spectrum ℂ (hermitianPart (FreeAlgebra.lift ℂ (fun i => a i j) p)) ⊆ (S : Set ℂ)) :
    ¬ (type_of% @OMA.S_mo_35207.main) := by
  apply disproof_of_uniform_annihilators g hn a hstar hgrow
  intro p
  let b := FreeAlgebra.lift ℂ a p
  have hpoly (p' : FreeAlgebra ℂ ι) :
      IsAlgebraic ℂ (hermitianPart (FreeAlgebra.lift ℂ a p')) := by
    obtain ⟨S, hS⟩ := hspec p'
    apply algebraic_of_uniform_spectrum _ (fun j => (hermitianPart_sa _).isStarNormal) S
    intro j
    change spectrum ℂ (hermitianPart (coordinate j (FreeAlgebra.lift ℂ a p'))) ⊆ _
    rw [coordinate_lift]
    exact hS j
  have hreal (r : ℝ) : IsAlgebraic ℂ
      (hermitianPart b + (r : ℂ) • hermitianPart (-Complex.I • b)) := by
    rw [hermitianPart_pencil]
    simpa [b] using hpoly ((1 - (r : ℂ) * Complex.I) • p)
  have h := algebraic_complex_pencil _ _ hreal Complex.I
  rw [hermitianPart_recombine] at h
  obtain ⟨f, hf, hzero⟩ := h
  refine ⟨f, hf, fun j => ?_⟩
  have heq := congrArg (coordinate j).toAlgHom hzero
  rw [map_zero, ← aeval_algHom_apply] at heq
  change aeval (coordinate j (FreeAlgebra.lift ℂ a p)) f = 0 at heq
  rwa [coordinate_lift] at heq

/-- The form used for the three self-adjoint generators in the preprint. -/
theorem disproof_of_uniform_hermitian_spectra {n : ℕ} (a : Fin n → lp M ∞)
    (ha : ∀ i j, IsSelfAdjoint (a i j))
    (hgrow : ∀ d : ℕ, ∃ j, d < Module.finrank ℂ (FreeAlgebra.lift ℂ (fun i => a i j)).range)
    (hspec : ∀ p : FreeAlgebra ℂ (Fin n), ∃ S : Finset ℂ, ∀ j,
      spectrum ℂ (hermitianPart (FreeAlgebra.lift ℂ (fun i => a i j) p)) ⊆ (S : Set ℂ)) :
    ¬ (type_of% @OMA.S_mo_35207.main) := by
  have hsa (i : Fin n) : IsSelfAdjoint (a i) := lp.ext (funext (ha i))
  exact disproof_of_presented_hermitian_spectra a (fun i => (hsa i).isStarNormal) a
    (adjoin_selfAdjoint_eq_range hsa) hgrow hspec

/-- Normal coordinates, including unitaries, can be used directly by adjoining their adjoints. -/
theorem disproof_of_normal_family {n : ℕ} (a : Fin n → lp M ∞)
    (hn : ∀ i j, IsStarNormal (a i j))
    (hgrow : ∀ d : ℕ, ∃ j, d < Module.finrank ℂ
      (FreeAlgebra.lift ℂ (fun i => withAdjoints a i j)).range)
    (hspec : ∀ p : FreeAlgebra ℂ (Fin n ⊕ Fin n), ∃ S : Finset ℂ, ∀ j,
      spectrum ℂ (hermitianPart (FreeAlgebra.lift ℂ (fun i => withAdjoints a i j) p)) ⊆
        (S : Set ℂ)) : ¬ (type_of% @OMA.S_mo_35207.main) := by
  have hnormal (i : Fin n) : IsStarNormal (a i) :=
    ⟨lp.ext (funext (fun j => (hn i j).star_comm_self.eq))⟩
  exact disproof_of_presented_hermitian_spectra a hnormal (withAdjoints a)
    (adjoin_eq_range_withAdjoints a) hgrow hspec

end
end MO35207

end

section

/-! Unit norm supplies boundedness of the coordinate family automatically. -/

namespace MO35207
noncomputable section
open scoped ENNReal
variable {M : ℕ → Type} [∀ j, CStarAlgebra (M j)] [∀ j, Nontrivial (M j)]

private def boundedUnitary (u : ∀ j, M j) (hu : ∀ j, u j ∈ unitary (M j)) : lp M ∞ :=
  ⟨u, memℓp_infty ⟨1, by
    rintro _ ⟨j, rfl⟩
    exact (CStarRing.norm_of_mem_unitary (hu j)).le⟩⟩

/-- A tower of finite matrix coordinates can be supplied directly. The coordinate algebras
must grow in dimension and each Hermitian part must have one common finite spectral set. -/
theorem disproof_of_unitary_coordinates {n : ℕ} (u : (j : ℕ) → Fin n → M j)
    (hu : ∀ j i, u j i ∈ unitary (M j))
    (hgrow : ∀ d : ℕ, ∃ j, d < Module.finrank ℂ (FreeAlgebra.lift ℂ (withAdjoints (u j))).range)
    (hspec : ∀ p : FreeAlgebra ℂ (Fin n ⊕ Fin n), ∃ S : Finset ℂ, ∀ j,
      spectrum ℂ (hermitianPart (FreeAlgebra.lift ℂ (withAdjoints (u j)) p)) ⊆ (S : Set ℂ)) :
    ¬ (type_of% @OMA.S_mo_35207.main) := by
  let a (i : Fin n) := boundedUnitary (fun j => u j i) (fun j => hu j i)
  have he (j : ℕ) : (fun i => withAdjoints a i j) = withAdjoints (u j) := by
    funext i
    cases i <;> rfl
  apply disproof_of_normal_family a
  · intro i j
    exact ⟨(hu j i).1.trans (hu j i).2.symm⟩
  · intro d
    obtain ⟨j, hj⟩ := hgrow d
    refine ⟨j, ?_⟩
    rw [he j]
    exact hj
  · intro p
    obtain ⟨S, hS⟩ := hspec p
    refine ⟨S, fun j => ?_⟩
    rw [he j]
    exact hS j

end
end MO35207

end

section

/-! Determinant identities used to compare finite truncations of the matrix tower. -/

namespace MO35207
noncomputable section
open Polynomial
open scoped Polynomial

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Inserting a low-rank coupling leaves a determinant of the size of the test pencil. -/
theorem determinant_update (D : (Matrix m m ℂ)ˣ) (V : Matrix m n ℂ)
    (K : Matrix n n ℂ) (U : Matrix n m ℂ) :
    ((D : Matrix m m ℂ) + V*K*U).det =
      (D : Matrix m m ℂ).det * (1 + K*U*(↑D⁻¹ : Matrix m m ℂ)*V).det := by
  have h : (D : Matrix m m ℂ) + V*K*U =
      (D : Matrix m m ℂ)*(1 + ((↑D⁻¹ : Matrix m m ℂ)*V)*(K*U)) := by
    rw [Matrix.mul_add, Matrix.mul_one]
    congr 1
    calc
      V*K*U = ((D : Matrix m m ℂ)*(↑D⁻¹ : Matrix m m ℂ))*V*(K*U) := by
        rw [Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [h, Matrix.det_mul, Matrix.det_one_add_mul_comm]
  simp only [Matrix.mul_assoc]

private def interpolatingPencil {r : Type*} [Fintype r] [DecidableEq r]
    (M : Matrix r r ℂ) : Matrix r r ℂ[X] := fun i j =>
  C ((1 : Matrix r r ℂ) i j) + X * C ((M-1) i j)

private theorem eval_interpolating_det {r : Type*} [Fintype r] [DecidableEq r]
    (M : Matrix r r ℂ) (t : ℂ) :
    (interpolatingPencil M).det.eval t = (1 + t • (M-1)).det := by
  change evalRingHom t (interpolatingPencil M).det = _
  rw [(evalRingHom t).map_det]
  congr 1
  apply Matrix.ext
  intro i j
  change (interpolatingPencil M i j).eval t = _
  simp [interpolatingPencil]

/-- A deformation starting at the identity can fail to be invertible at only finitely
many complex parameters. This applies simultaneously to all colors and ports. -/
theorem finite_singular_parameters (M : Matrix m m ℂ) :
    {t : ℂ | ¬ IsUnit (1+t • M)}.Finite := by
  let p := (interpolatingPencil (M+1)).det
  have he (t : ℂ) : p.eval t = (1+t • M).det := by
    have hsub : M+1-1 = M := by abel
    exact (eval_interpolating_det (M+1) t).trans
      (congrArg (fun Y : Matrix m m ℂ => (1+t • Y).det) hsub)
  have hp : p ≠ 0 := by
    intro h
    have bad := he 0
    simp [h] at bad
  apply (Polynomial.finite_setOfPred_isRoot hp).subset
  intro t ht
  change ¬ IsUnit (1+t • M) at ht
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at ht
  exact (he t).trans ht

theorem simultaneously_invertible {ι : Type*} [Finite ι] {v : ι → Type*}
    [∀ i, Fintype (v i)] [∀ i, DecidableEq (v i)] (M : (i : ι) → Matrix (v i) (v i) ℂ) :
    Set.Infinite {t : ℂ | ∀ i, IsUnit (1+t • M i)} := by
  have hf := Set.finite_iUnion (fun i => finite_singular_parameters (M i))
  apply hf.infinite_compl.mono
  intro t ht i
  by_contra hn
  exact ht (Set.mem_iUnion.mpr ⟨i,hn⟩)

/-- A determinant comparison near the identity suffices at any singular
specialization too. Infinitely many deformation parameters suffice. -/
theorem determinant_powers_at_specialization (M : Matrix m m ℂ) (N : Matrix n n ℂ)
    (a b : ℕ) (h : Set.Infinite {t : ℂ |
      (1 + t • (M-1)).det ^ a = (1 + t • (N-1)).det ^ b}) : M.det ^ a = N.det ^ b := by
  have heq : (interpolatingPencil M).det ^ a = (interpolatingPencil N).det ^ b := by
    apply eq_of_infinite_eval_eq
    simpa [eval_pow, eval_interpolating_det] using h
  simpa [eval_pow, eval_interpolating_det, add_comm] using congrArg (eval (1 : ℂ)) heq

theorem spectrum_eq_of_charpoly_powers (M : Matrix m m ℂ) (N : Matrix n n ℂ)
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : M.charpoly ^ a = N.charpoly ^ b) :
    spectrum ℂ M = spectrum ℂ N := by
  ext z
  rw [M.mem_spectrum_iff_isRoot_charpoly, N.mem_spectrum_iff_isRoot_charpoly]
  change M.charpoly.eval z = 0 ↔ N.charpoly.eval z = 0
  have hval := congrArg (eval z) h
  simp only [eval_pow] at hval
  constructor
  · intro hM
    apply eq_zero_of_pow_eq_zero (n := b)
    rw [← hval, hM, zero_pow ha]
  · intro hN
    apply eq_zero_of_pow_eq_zero (n := a)
    rw [hval, hN, zero_pow hb]

end
end MO35207

end

section

/-! A finite set of characteristic-polynomial comparisons suffices for the endpoint. -/

namespace MO35207
noncomputable section
open scoped Matrix.Norms.L2Operator
variable {I : ℕ → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]

/-- All exceptional truncations are retained. Beyond the cutoff, equal positive powers
of the characteristic polynomials give identical sets of roots. -/
theorem finite_spectral_set_of_stabilization (x : (j : ℕ) → Matrix (I j) (I j) ℂ) (J : ℕ)
    (h : ∀ j ≥ J, ∃ a b : ℕ, a ≠ 0 ∧ b ≠ 0 ∧ (x j).charpoly ^ a = (x J).charpoly ^ b) :
    ∃ S : Finset ℂ, ∀ j, spectrum ℂ (x j) ⊆ (S : Set ℂ) := by
  classical
  refine ⟨(Finset.range (J+1)).biUnion (fun j => (x j).charpoly.roots.toFinset), ?_⟩
  intro j z hz
  have hroot (m : ℕ) (hm : z ∈ spectrum ℂ (x m)) : z ∈ (x m).charpoly.roots.toFinset :=
    Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (x m).charpoly_monic.ne_zero).mpr
      ((x m).mem_spectrum_iff_isRoot_charpoly.mp hm))
  apply Finset.mem_biUnion.mpr
  by_cases hj : j < J
  · exact ⟨j, Finset.mem_range.mpr (by omega), hroot j hz⟩
  · obtain ⟨a,b,ha,hb,he⟩ := h j (by omega)
    rw [spectrum_eq_of_charpoly_powers _ _ ha hb he] at hz
    exact ⟨J, Finset.mem_range.mpr (by omega), hroot J hz⟩

variable [∀ j, Nonempty (I j)]

/-- A direct target for the tower construction. All remaining hypotheses concern its
finite, algebraic matrix models. The bounded product, its closure, and the original
universal C*-algebra statement are dealt with by the already checked reductions. -/
theorem disproof_of_matrix_tower {n : ℕ} (u : (j : ℕ) → Fin n → Matrix (I j) (I j) ℂ)
    (hu : ∀ j i, u j i ∈ unitary (Matrix (I j) (I j) ℂ))
    (hgrow : ∀ d : ℕ, ∃ j, d < Module.finrank ℂ (FreeAlgebra.lift ℂ (withAdjoints (u j))).range)
    (hstable : ∀ p : FreeAlgebra ℂ (Fin n ⊕ Fin n),
      let x (j : ℕ) := hermitianPart (FreeAlgebra.lift ℂ (withAdjoints (u j)) p)
      ∃ J, ∀ j ≥ J, ∃ a b : ℕ, a ≠ 0 ∧ b ≠ 0 ∧ (x j).charpoly ^ a = (x J).charpoly ^ b) :
    ¬ (type_of% @OMA.S_mo_35207.main) := by
  apply disproof_of_unitary_coordinates u hu hgrow
  intro p
  obtain ⟨J, hJ⟩ := hstable p
  exact finite_spectral_set_of_stabilization _ J hJ

end
end MO35207

end

section

/-! Finite truncations of the four-unitary construction, with increasing generated dimension. -/

namespace MO35207
noncomputable section

structure MatrixModel where
  Index : Type
  [finiteIndex : Fintype Index]
  [decidableIndex : DecidableEq Index]
  [nonemptyIndex : Nonempty Index]
  tuple : Fin 4 → Matrix Index Index ℂ
  isUnitary : ∀ i, tuple i ∈ unitary _

instance (m : MatrixModel) : Fintype m.Index := m.finiteIndex
instance (m : MatrixModel) : DecidableEq m.Index := m.decidableIndex
instance (m : MatrixModel) : Nonempty m.Index := m.nonemptyIndex

namespace MatrixModel

def dimension (m : MatrixModel) : ℕ := Module.finrank ℂ (Algebra.adjoin ℂ (Set.range m.tuple))

def labels (g : ℕ) : StageColors × Fin g → ℂ := (finite_unitary_labels _).choose

private def rawStep (g : ℕ) (m : MatrixModel) :=
  stageTuple (fun _ : Fin g => false) (fun _ : Fin g => true) m.tuple (labels g) (@Cube.gamma g)

private def flatten (g : ℕ) (m : MatrixModel) :=
  Matrix.compAlgEquiv (StageSpace (Fin g) (Cube.Vertex g)) m.Index ℂ ℂ

/-- A single outer cube. Its size depends on the position in the tower. -/
def step (j : ℕ) (m : MatrixModel) : MatrixModel where
  Index := StageSpace (Fin (j+2)) (Cube.Vertex (j+2)) × m.Index
  tuple i := flatten (j+2) m (rawStep (j+2) m i)
  isUnitary := by
    intro i
    let g := j+2
    have hs : ∀ l : Fin g, Cube.gamma l ∈ unitary _ := by
      intro l
      rw [Unitary.mem_iff, (Cube.gamma_selfAdjoint l).star_eq, Cube.gamma_square]
      exact ⟨rfl,rfl⟩
    have h := stageTuple_unitary _ _ (cube_supplies_connector (g := g) (by dsimp [g]; omega)).1
      m.tuple m.isUnitary (labels g) (finite_unitary_labels _).choose_spec.2 (@Cube.gamma g) hs i
    let e := flatten g m
    change rawStep g m i ∈ unitary _ at h
    have he : ∀ x, star (e x) = e (star x) := fun _ => rfl
    change e (rawStep g m i) ∈ unitary _
    rw [Unitary.mem_iff, he, ← map_mul, ← map_mul, h.1, h.2, map_one]
    exact ⟨rfl,rfl⟩

private theorem dimension_map_tuple {D E : Type*} [Ring D] [Ring E] [Algebra ℂ D] [Algebra ℂ E]
    (e : D ≃ₐ[ℂ] E) (u : Fin 4 → D) :
    Module.finrank ℂ (Algebra.adjoin ℂ (Set.range u)) =
      Module.finrank ℂ (Algebra.adjoin ℂ (Set.range (fun i => e (u i)))) := by
  let S := Algebra.adjoin ℂ (Set.range u)
  have he : S.map e.toAlgHom = Algebra.adjoin ℂ (Set.range (fun i => e (u i))) := by
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    rfl
  rw [← he]
  exact (Subalgebra.equivMapOfInjective S e.toAlgHom e.injective).toLinearEquiv.finrank_eq

theorem dimension_step (j : ℕ) (m : MatrixModel) : m.dimension < (step j m).dimension := by
  let g := j+2
  obtain ⟨hne, spare, hs₁, hs₂, M, hM, hll, hhh, hlh⟩ :=
    cube_supplies_connector (g := g) (by dsimp [g]; omega)
  apply lt_of_lt_of_eq _ (dimension_map_tuple (flatten g m) (rawStep g m))
  exact stageTuple_grows _ _ spare hne hs₁ hs₂ m.tuple (fun c => (m.isUnitary c).1)
    (labels g) (finite_unitary_labels _).choose_spec.1 (@Cube.gamma g) hM hll hhh hlh

private def base : MatrixModel where
  Index := Unit
  tuple _ := 1
  isUnitary _ := one_mem _

/-- The first stage is always at position j, independently of the truncation depth. -/
def truncation : (depth position : ℕ) → MatrixModel
  | 0, _ => base
  | depth+1, j => step j (truncation depth (j+1))

theorem dimension_truncation (depth j : ℕ) : depth ≤ (truncation depth j).dimension := by
  induction depth generalizing j with
  | zero => exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt ((ih (j+1)).trans_lt (dimension_step j _))

private theorem dimension_le_star_range (m : MatrixModel) :
    m.dimension ≤ Module.finrank ℂ (FreeAlgebra.lift ℂ (withAdjoints m.tuple)).range := by
  let S := Algebra.adjoin ℂ (Set.range m.tuple)
  let T := (FreeAlgebra.lift ℂ (withAdjoints m.tuple)).range
  have h : S ≤ T := by
    apply Algebra.adjoin_le
    rintro _ ⟨i,rfl⟩
    exact ⟨FreeAlgebra.ι ℂ (Sum.inl i), FreeAlgebra.lift_ι_apply _ _⟩
  exact LinearMap.finrank_le_finrank_of_injective (f := (Subalgebra.inclusion h).toLinearMap)
    (Subalgebra.inclusion_injective h)

theorem unbounded_star_range (d : ℕ) : ∃ j, d < Module.finrank ℂ
    (FreeAlgebra.lift ℂ (withAdjoints (truncation j 0).tuple)).range :=
  ⟨d+1, (Nat.lt_succ_self d).trans_le ((dimension_truncation (d+1) 0).trans
    (dimension_le_star_range _))⟩

/-- For these particular four unitaries only spectral stabilization remains to be proved. -/
theorem disproof_of_truncation_stabilization
    (hstable : ∀ p : FreeAlgebra ℂ (Fin 4 ⊕ Fin 4),
      let x (j : ℕ) := hermitianPart (FreeAlgebra.lift ℂ (withAdjoints (truncation j 0).tuple) p)
      ∃ J, ∀ j ≥ J, ∃ a b : ℕ, a ≠ 0 ∧ b ≠ 0 ∧ (x j).charpoly ^ a = (x J).charpoly ^ b) :
    ¬ (type_of% @OMA.S_mo_35207.main) := by
  apply disproof_of_matrix_tower (I := fun j => (truncation j 0).Index)
    (fun j => (truncation j 0).tuple) (fun j => (truncation j 0).isUnitary) unbounded_star_range hstable

end MatrixModel
end
end MO35207

end

section

/-! Linearizing a free polynomial using one vector variable per suffix of a word. -/

namespace MO35207
noncomputable section
open Matrix

variable {X : Type} [DecidableEq X]

structure WordSystem (X : Type) where
  words : Finset (List X)
  empty_mem : [] ∈ words
  tail_mem : ∀ {a w}, a :: w ∈ words → w ∈ words
  coeff : List X → ℂ

namespace WordSystem

abbrev State (s : WordSystem X) := ↥s.words

def base (s : WordSystem X) : s.State := ⟨[], s.empty_mem⟩

def wordValue {A : Type*} [Monoid A] (u : X → A) (w : List X) : A := (w.map u).prod

def value {A : Type*} [Ring A] [Algebra ℂ A] (s : WordSystem X) (u : X → A) : A :=
  ∑ w : s.State, s.coeff w.val • wordValue u w.val

private def closure (ws : Finset (List X)) : Finset (List X) :=
  insert [] (ws.biUnion (fun t => t.tails.toFinset))

private theorem self_mem_closure (ws : Finset (List X)) {w : List X} (hw : w ∈ ws) :
    w ∈ closure ws := by
  apply Finset.mem_insert_of_mem
  exact Finset.mem_biUnion.mpr ⟨w, hw, List.mem_toFinset.mpr ((List.mem_tails _ _).mpr ⟨[], by simp⟩)⟩

private theorem tail_mem_closure (ws : Finset (List X)) {a : X} {w : List X}
    (hw : a :: w ∈ closure ws) : w ∈ closure ws := by
  rcases Finset.mem_insert.mp hw with hn | h
  · contradiction
  · obtain ⟨t, ht, hst⟩ := Finset.mem_biUnion.mp h
    obtain ⟨p, rfl⟩ := (List.mem_tails _ _).mp (List.mem_toFinset.mp hst)
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    exact ⟨_, ht, List.mem_toFinset.mpr ((List.mem_tails _ _).mpr ⟨p ++ [a], by simp⟩)⟩

/-- One finite word system works in every complex algebra, for every choice of matrices. -/
theorem represents (p : FreeAlgebra ℂ X) :
    ∃ s : WordSystem X, ∀ {A : Type} [Ring A] [Algebra ℂ A] (u : X → A),
      FreeAlgebra.lift ℂ u p = s.value u := by
  classical
  let e := FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := X)
  let f := (e p).coeff
  let ws := f.support.image FreeMonoid.toList
  let s : WordSystem X := ⟨closure ws, Finset.mem_insert_self _ _, tail_mem_closure ws,
    fun w => f (FreeMonoid.ofList w)⟩
  refine ⟨s, ?_⟩
  intro A _ _ u
  have he := e.symm_apply_apply p
  change MonoidAlgebra.lift ℂ (FreeAlgebra ℂ X) (FreeMonoid X)
    (FreeMonoid.lift (FreeAlgebra.ι ℂ)) (e p) = p at he
  rw [MonoidAlgebra.lift_apply] at he
  change (∑ w ∈ f.support, f w • FreeMonoid.lift (FreeAlgebra.ι ℂ) w) = p at he
  rw [← he, map_sum]
  simp only [map_smul, FreeMonoid.lift_apply, map_list_prod, List.map_map]
  have hgen : (FreeAlgebra.lift ℂ u) ∘ FreeAlgebra.ι ℂ = u := by
    funext x
    exact FreeAlgebra.lift_ι_apply _ _
  rw [hgen]
  unfold value
  rw [Finset.sum_coe_sort s.words (fun w => s.coeff w • wordValue u w)]
  change _ = ∑ w ∈ closure ws, f (FreeMonoid.ofList w) • wordValue u w
  have hsub : ws ⊆ closure ws := fun _ h => self_mem_closure _ h
  rw [← Finset.sum_subset hsub (fun w _ hn => ?_)]
  · unfold ws
    rw [Finset.sum_image (fun _ _ _ _ he => FreeMonoid.toList.injective he)]
    simp [wordValue]
  · have hzero : f (FreeMonoid.ofList w) = 0 := by
      apply Finsupp.notMem_support_iff.mp
      intro hm
      exact hn (Finset.mem_image.mpr ⟨_, hm, FreeMonoid.toList_ofList _⟩)
    simp [hzero]

variable {N : Type} [Fintype N] [DecidableEq N]

/-- The auxiliary vector at a nonempty word is forced by its immediate suffix. -/
def Consistent (s : WordSystem X) (u : X → Matrix N N ℂ) (v : s.State → N → ℂ) : Prop :=
  ∀ a w (h : a :: w ∈ s.words), v ⟨a::w, h⟩ = (u a) *ᵥ v ⟨w, s.tail_mem h⟩

omit [DecidableEq X] in
theorem forced (s : WordSystem X) (u : X → Matrix N N ℂ) (v : s.State → N → ℂ)
    (hv : s.Consistent u v) (w : List X) (hw : w ∈ s.words) :
    v ⟨w,hw⟩ = wordValue u w *ᵥ v s.base := by
  induction w with
  | nil => simp [wordValue, base]
  | cons a w ih =>
    rw [hv a w hw, ih (s.tail_mem hw)]
    simp [wordValue, Matrix.mulVec_mulVec]

omit [DecidableEq X] in
/-- Every eigenvalue of the polynomial is detected by a finite system of affine equations,
with the same state set for every parameter and matrix dimension. -/
theorem eigenvalue_iff (s : WordSystem X) (u : X → Matrix N N ℂ) (z : ℂ) :
    z ∈ spectrum ℂ (s.value u) ↔ ∃ v : s.State → N → ℂ, v ≠ 0 ∧ s.Consistent u v ∧
      z • v s.base = ∑ w : s.State, s.coeff w.val • v w := by
  classical
  have hm : z ∈ spectrum ℂ (s.value u) ↔
      ∃ x : N → ℂ, x ≠ 0 ∧ (s.value u) *ᵥ x = z • x := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
    rw [← Matrix.charpoly_toLin', ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    rw [Module.End.hasEigenvalue_iff]
    simp only [Submodule.ne_bot_iff, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact exists_congr (fun _ => and_comm)
  rw [hm]
  have mult (x : N → ℂ) : (s.value u) *ᵥ x =
      ∑ w : s.State, s.coeff w.val • (wordValue u w.val *ᵥ x) := by
    simp [value, Matrix.sum_mulVec, Matrix.smul_mulVec]
  constructor
  · rintro ⟨x,hx,he⟩
    let v (w : s.State) := wordValue u w.val *ᵥ x
    have hbase : v s.base = x := by simp [v, base, wordValue]
    refine ⟨v, fun hz => hx (hbase.symm.trans (congrFun hz s.base)), ?_, ?_⟩
    · intro a w hw
      simp [v, wordValue, Matrix.mulVec_mulVec]
    · rw [hbase, ← he, mult]
  · rintro ⟨v, hv, hrec, hz⟩
    refine ⟨v s.base, ?_, ?_⟩
    · intro hzero
      apply hv
      funext w
      rw [s.forced u v hrec w.val w.property, hzero, Matrix.mulVec_zero]
      rfl
    · rw [mult, hz]
      exact Finset.sum_congr rfl (fun w _ => congrArg (s.coeff w.val • ·)
        (s.forced u v hrec w.val w.property).symm)

end WordSystem
end
end MO35207

end

section

/-! A single square affine matrix detects all spectral parameters of a free polynomial. -/

namespace MO35207
noncomputable section
open Matrix

variable {X J N : Type} [DecidableEq X] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]

def affineForms (X : Type) : Submodule ℂ (FreeAlgebra ℂ X) :=
  Submodule.span ℂ (insert 1 (Set.range (FreeAlgebra.ι ℂ : X → FreeAlgebra ℂ X)))

omit [DecidableEq X] in
theorem affine_scalar (c : ℂ) : algebraMap ℂ (FreeAlgebra ℂ X) c ∈ affineForms X := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (affineForms X).smul_mem _ (Submodule.subset_span (Set.mem_insert _ _))

/-- Flatten an evaluated affine matrix into an ordinary complex matrix. -/
def evalPencil (P : Matrix J J (FreeAlgebra ℂ X)) (u : X → Matrix N N ℂ) :
    Matrix (J × N) (J × N) ℂ :=
  Matrix.compAlgEquiv J N ℂ ℂ ((FreeAlgebra.lift ℂ u).mapMatrix P)

private theorem singular_iff (M : Matrix J J ℂ) :
    ¬ IsUnit M ↔ ∃ x : J → ℂ, x ≠ 0 ∧ M *ᵥ x = 0 := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  constructor
  · intro h
    obtain ⟨x,y,he,hne⟩ := Function.not_injective_iff.mp h
    exact ⟨x-y, sub_ne_zero.mpr hne, by rw [Matrix.mulVec_sub, he, sub_self]⟩
  · rintro ⟨x,hx,he⟩ hinj
    exact hx (hinj (he.trans (Matrix.mulVec_zero _).symm))

private theorem block_singular (B : Matrix J J (Matrix N N ℂ)) :
    ¬ IsUnit (Matrix.compAlgEquiv J N ℂ ℂ B) ↔ ∃ v : J → N → ℂ, v ≠ 0 ∧
      ∀ r, (∑ c, B r c *ᵥ v c) = 0 := by
  rw [singular_iff]
  have he (x : J × N → ℂ) (r : J) (i : N) :
      ((Matrix.compAlgEquiv J N ℂ ℂ B) *ᵥ x) (r,i) =
        (∑ c, B r c *ᵥ (fun k => x (c,k))) i := by
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Finset.sum_apply]
  constructor
  · rintro ⟨x, hx, hxker⟩
    refine ⟨fun c k => x (c,k), ?_, fun r => funext (fun i => ?_)⟩
    · intro hc
      exact hx (funext (fun ⟨r,i⟩ => congrFun (congrFun hc r) i))
    · exact (he x r i).symm.trans (congrFun hxker (r,i))
  · rintro ⟨v,hv,hker⟩
    refine ⟨fun p => v p.1 p.2, ?_, funext (fun ⟨r,i⟩ => ?_)⟩
    · intro hc
      exact hv (funext (fun r => funext (fun i => congrFun hc (r,i))))
    · exact (he _ r i).trans (congrFun (hker r) i)

namespace WordSystem

def entry {A : Type*} [Ring A] [Algebra ℂ A] (s : WordSystem X) (u : X → A) (z : ℂ) :
    Matrix s.State s.State A
  | ⟨[], _⟩, c => (if c = s.base then algebraMap ℂ A z else 0) - algebraMap ℂ A (s.coeff c.val)
  | ⟨a::w, h⟩, c => (if c = ⟨a::w,h⟩ then 1 else 0) - (if c = ⟨w,s.tail_mem h⟩ then u a else 0)

def pencil (s : WordSystem X) (z : ℂ) : Matrix s.State s.State (FreeAlgebra ℂ X) :=
  s.entry (FreeAlgebra.ι ℂ) z

theorem pencil_affine (s : WordSystem X) (z : ℂ) (r c : s.State) :
    s.pencil z r c ∈ affineForms X := by
  rcases r with ⟨_ | ⟨a,w⟩,hr⟩
  · apply Submodule.sub_mem
    · split
      · apply affine_scalar
      · exact Submodule.zero_mem _
    · apply affine_scalar
  · apply Submodule.sub_mem
    · split
      · exact Submodule.subset_span (Set.mem_insert _ _)
      · exact Submodule.zero_mem _
    · split
      · exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨a,rfl⟩)
      · exact Submodule.zero_mem _

private theorem map_pencil (s : WordSystem X) (z : ℂ) (u : X → Matrix N N ℂ) :
    (FreeAlgebra.lift ℂ u).mapMatrix (s.pencil z) = s.entry u z := by
  apply Matrix.ext
  intro r c
  change (FreeAlgebra.lift ℂ u) (s.entry (FreeAlgebra.ι ℂ) z r c) = s.entry u z r c
  rcases r with ⟨_ | ⟨a,w⟩,hr⟩ <;> simp only [entry] <;> split_ifs <;> simp

omit [DecidableEq N] in
private theorem sum_one_entry (v : J → N → ℂ) (c : J) (A : Matrix N N ℂ) :
    (∑ i, (if i = c then A else 0) *ᵥ v i) = A *ᵥ v c := by
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hn
    simp [hn]
  · simp

theorem spectrum_iff_singular (s : WordSystem X) (z : ℂ) (u : X → Matrix N N ℂ) :
    z ∈ spectrum ℂ (s.value u) ↔ ¬ IsUnit (evalPencil (s.pencil z) u) := by
  rw [evalPencil, s.map_pencil, block_singular, s.eigenvalue_iff]
  apply exists_congr
  intro v
  apply and_congr_right
  intro _
  have scalar (z : ℂ) (x : N → ℂ) : algebraMap ℂ (Matrix N N ℂ) z *ᵥ x = z • x := by
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  have root : (∑ c, s.entry u z s.base c *ᵥ v c) =
      z • v s.base - ∑ c, s.coeff c.val • v c := by
    simp only [base, entry, Matrix.sub_mulVec, Finset.sum_sub_distrib, scalar]
    exact congrArg (fun x => x - ∑ c, s.coeff c.val • v c)
      ((sum_one_entry v s.base (algebraMap ℂ (Matrix N N ℂ) z)).trans (scalar z _))
  have aux (a : X) (w : List X) (h : a::w ∈ s.words) :
      (∑ c, s.entry u z ⟨a::w,h⟩ c *ᵥ v c) = v ⟨a::w,h⟩ - u a *ᵥ v ⟨w,s.tail_mem h⟩ := by
    simp only [entry, Matrix.sub_mulVec, Finset.sum_sub_distrib, sum_one_entry, Matrix.one_mulVec]
  constructor
  · rintro ⟨rec,h⟩ ⟨_ | ⟨a,w⟩,hr⟩
    · exact root.trans (sub_eq_zero.mpr h)
    · exact (aux a w hr).trans (sub_eq_zero.mpr (rec a w hr))
  · intro h
    refine ⟨fun a w hw => sub_eq_zero.mp ((aux a w hw).symm.trans (h _)),
      sub_eq_zero.mp (root.symm.trans (h _))⟩

end WordSystem
end
end MO35207

end

section

/-! Propagation of normalized determinants through a common prefix of finite truncations. -/

namespace MO35207.MatrixModel
noncomputable section

abbrev Letters := Fin 4 ⊕ Fin 4
abbrev Pencil (J : Type) := Matrix J J (FreeAlgebra ℂ Letters)
abbrev order (m : MatrixModel) := Fintype.card m.Index

variable {J : Type} [Fintype J] [DecidableEq J]

def test (m : MatrixModel) (P : Pencil J) := evalPencil P (withAdjoints m.tuple)

def affine (P : Pencil J) : Prop := ∀ i j, P i j ∈ affineForms Letters

/-- Compare matrix sizes by raising each determinant to the other model's dimension. -/
def sameTests (J : Type) [Fintype J] [DecidableEq J] (m n : MatrixModel) : Prop :=
  ∀ P : Pencil J, affine P → (test m P).det ^ n.order = (test n P).det ^ m.order

/-- The finite one-stage factorization required of the concrete four generators.
The scalar factor and the smaller affine test are uniform in the inner model.
Once the cube exceeds the square of the test size, only scalar determinants remain. -/
def stageFactorization (J : Type) [Fintype J] [DecidableEq J] : Prop :=
  ∀ j (P : Pencil J), affine P → Set.Infinite {t : ℂ |
    ∃ (c : ℂ) (Q : Pencil J), affine Q ∧
      (∀ m : MatrixModel, (1 + t • (test (step j m) P - 1)).det =
        c ^ m.order * (test m Q).det) ∧
      (Fintype.card J ^ 2 < j+2 → ∃ z : ℂ, ∀ m : MatrixModel, (test m Q).det = z ^ m.order)}

private theorem powers_cross (c : ℂ) (a b : ℕ) : (c^a)^b = (c^b)^a := by
  simp only [← pow_mul, Nat.mul_comm a b]

private theorem compare_step (hstep : stageFactorization J) (j : ℕ) (m n : MatrixModel)
    (h : sameTests J m n ∨ Fintype.card J ^ 2 < j+2) : sameTests J (step j m) (step j n) := by
  intro P hP
  have he : (test (step j m) P).det ^ n.order = (test (step j n) P).det ^ m.order := by
    apply determinant_powers_at_specialization
    apply (hstep j P hP).mono
    rintro t ⟨c,Q,hQ,heq,hcut⟩
    change (1 + t • (test (step j m) P - 1)).det ^ n.order =
      (1 + t • (test (step j n) P - 1)).det ^ m.order
    rw [heq m, heq n, mul_pow, mul_pow, powers_cross c m.order n.order]
    congr 1
    rcases h with hinner | hwidth
    · exact hinner Q hQ
    · obtain ⟨z,hz⟩ := hcut hwidth
      rw [hz m, hz n, powers_cross]
  let factor := Fintype.card (StageSpace (Fin (j+2)) (Cube.Vertex (j+2)))
  have hs (x : MatrixModel) : (step j x).order = factor * x.order := Fintype.card_prod _ _
  rw [hs, hs, Nat.mul_comm factor n.order, Nat.mul_comm factor m.order, pow_mul, pow_mul, he]

private theorem compare_prefix (hstep : stageFactorization J) (r pos a b : ℕ)
    (width : Fintype.card J ^ 2 < pos+r+2) :
    sameTests J (truncation (r+1+a) pos) (truncation (r+1+b) pos) := by
  induction r generalizing pos with
  | zero =>
    rw [show 0+1+a = a+1 by omega, show 0+1+b = b+1 by omega]
    exact compare_step hstep pos _ _ (Or.inr (by simpa using width))
  | succ r ih =>
    rw [show r.succ+1+a = (r+1+a)+1 by omega, show r.succ+1+b = (r+1+b)+1 by omega]
    exact compare_step hstep pos _ _ (Or.inl (ih (pos+1) (by omega)))

theorem stable_tests (hstep : stageFactorization J) : ∃ K, ∀ d ≥ K,
    sameTests J (truncation d 0) (truncation K 0) := by
  let r := Fintype.card J ^ 2
  refine ⟨r+1, ?_⟩
  intro d hd
  have he := compare_prefix hstep r 0 (d-(r+1)) 0 (by dsimp [r]; omega)
  simpa only [show r+1+(d-(r+1)) = d by omega, Nat.add_zero] using he

theorem test_unit_iff {m n : MatrixModel} (h : sameTests J m n) (P : Pencil J) (hP : affine P) :
    IsUnit (test m P) ↔ IsUnit (test n P) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, isUnit_iff_ne_zero]
  have he := h P hP
  constructor
  · intro hm hn
    rw [hn, zero_pow (Fintype.card_ne_zero (α := m.Index))] at he
    exact (pow_ne_zero _ hm) he
  · intro hn hm
    rw [hm, zero_pow (Fintype.card_ne_zero (α := n.Index))] at he
    exact (pow_ne_zero _ hn) he.symm

end
end MO35207.MatrixModel

end

section

/-! How a model-independent background enters the determinant of an encoded stage. -/

namespace MO35207
noncomputable section
open scoped Kronecker

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
  [DecidableEq I] [DecidableEq J] [DecidableEq N]

def amplify (N : Type*) [Fintype N] [DecidableEq N] :
    Matrix I I ℂ →ₐ[ℂ] Matrix (I × N) (I × N) ℂ :=
  (Matrix.compAlgEquiv I N ℂ ℂ).toAlgHom.comp (Algebra.ofId ℂ (Matrix N N ℂ)).mapMatrix

theorem amplify_eq_kronecker (A : Matrix I I ℂ) :
    amplify N A = A ⊗ₖ (1 : Matrix N N ℂ) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  change (algebraMap ℂ (Matrix N N ℂ) (A i j)) a b = A i j * (1 : Matrix N N ℂ) a b
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

theorem amplify_det (A : Matrix I I ℂ) :
    (amplify N A).det = A.det ^ Fintype.card N := by
  simp [amplify_eq_kronecker, Matrix.det_kronecker]

theorem amplify_star (A : Matrix I I ℂ) :
    star (amplify N A) = amplify N (star A) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  exact congrArg (fun M : Matrix N N ℂ => M a b)
    ((algebraMap_star_comm (A j i) (A := Matrix N N ℂ)).symm)

/-- A background amplified by the inner dimension and a single low-rank update give
exactly the scalar power required by the normalized determinant comparison. -/
theorem amplified_update (D : (Matrix I I ℂ)ˣ)
    (V : Matrix (I × N) (J × N) ℂ) (K : Matrix (J × N) (J × N) ℂ)
    (W : Matrix (J × N) (I × N) ℂ) :
    (amplify N (D : Matrix I I ℂ) + V*K*W).det =
      (D : Matrix I I ℂ).det ^ Fintype.card N *
        (1 + K*W*amplify N (↑D⁻¹ : Matrix I I ℂ)*V).det := by
  let D' := Units.map (amplify (I := I) N).toMonoidHom D
  exact (determinant_update D' V K W).trans (by rw [← amplify_det (N := N)]; rfl)

end
end MO35207

end

section

/-! Removing an encoding projection from an arbitrary affine pencil. -/

namespace MO35207
noncomputable section
open scoped Kronecker

variable {X J : Type} [Fintype J] [DecidableEq J]

/-- Perturbing every input in a common direction changes an affine expression by a
scalar multiple of that direction. The scalar works in every complex algebra. -/
theorem affine_direction (p : FreeAlgebra ℂ X) (hp : p ∈ affineForms X) (d : X → ℂ) :
    ∃ c : ℂ, ∀ {A : Type} [Ring A] [Algebra ℂ A] (u : X → A) (Y : A),
      FreeAlgebra.lift ℂ (fun i => u i + d i • Y) p = FreeAlgebra.lift ℂ u p + c • Y := by
  induction hp using Submodule.span_induction with
  | mem a ha =>
    rcases ha with h | ⟨i,rfl⟩
    · subst a
      exact ⟨0, by intros; simp⟩
    · exact ⟨d i, by intros; simp⟩
  | zero => exact ⟨0, by intros; simp⟩
  | add p q _ _ hp hq =>
    obtain ⟨c,hc⟩ := hp
    obtain ⟨e,he⟩ := hq
    refine ⟨c+e, ?_⟩
    intro A _ _ u Y
    rw [map_add, map_add, hc, he, add_smul]
    abel
  | smul c p _ hp =>
    obtain ⟨e,he⟩ := hp
    refine ⟨c*e, ?_⟩
    intro A _ _ u Y
    rw [map_smul, map_smul, he, smul_add, smul_smul]

/-- The rank of the encoding update is the test width times the inner dimension.
Its coefficient matrix is independent of the inner model and its dimension. -/
theorem affine_rank_update (P : Matrix J J (FreeAlgebra ℂ X)) (hP : ∀ i j, P i j ∈ affineForms X)
    (d : X → ℂ) : ∃ C : Matrix J J ℂ,
    ∀ {H N : Type} [Fintype H] [Fintype N] [DecidableEq H] [DecidableEq N]
      (u : X → Matrix H H ℂ) (V : Matrix H N ℂ) (W : Matrix N H ℂ),
      evalPencil P (fun i => u i + d i • (V*W)) = evalPencil P u +
        ((1 : Matrix J J ℂ) ⊗ₖ V) * (C ⊗ₖ (1 : Matrix N N ℂ)) * ((1 : Matrix J J ℂ) ⊗ₖ W) := by
  choose C hC using fun i j => affine_direction (P i j) (hP i j) d
  let C₀ : Matrix J J ℂ := C
  refine ⟨C₀, ?_⟩
  intro H N _ _ _ _ u V W
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_one]
  ext ⟨i,a⟩ ⟨j,b⟩
  exact congrArg (fun M : Matrix H H ℂ => M a b) (hC i j u (V*W))

end
end MO35207

end

section

/-! Exact low-rank update for the concrete four generators of every truncation. -/

namespace MO35207.MatrixModel
noncomputable section
open scoped Kronecker

abbrev Outer (j : ℕ) := StageSpace (Fin (j+2)) (Cube.Vertex (j+2))

def background (j : ℕ) : Fin 4 → Matrix (Outer j) (Outer j) ℂ :=
  stageBackground (labels (j+2)) (@Cube.gamma (j+2))

private def rawColumn (j : ℕ) (m : MatrixModel) :=
  encodingColumn (L := Fin (j+2)) (fun _ : Fin (j+2) => false) (fun _ : Fin (j+2) => true)
    (phaseCopies m.tuple)

private def rawRow (j : ℕ) (m : MatrixModel) :=
  encodingRow (L := Fin (j+2)) (fun _ : Fin (j+2) => false) (fun _ : Fin (j+2) => true)
    (phaseCopies m.tuple)

def column (j : ℕ) (m : MatrixModel) : Matrix (Outer j × m.Index) m.Index ℂ :=
  fun p q => rawColumn j m p.1 () p.2 q

def row (j : ℕ) (m : MatrixModel) : Matrix m.Index (Outer j × m.Index) ℂ :=
  fun p q => rawRow j m () q.1 p q.2

private theorem flatten_projection (j : ℕ) (m : MatrixModel) :
    Matrix.compAlgEquiv (Outer j) m.Index ℂ ℂ (rawColumn j m * rawRow j m) = column j m * row j m := by
  ext ⟨b,p⟩ ⟨c,q⟩
  change ((rawColumn j m * rawRow j m) b c) p q = _
  simp [Matrix.mul_apply, column, row]

private theorem projection_star (j : ℕ) (m : MatrixModel) :
    star (column j m * row j m) = column j m * row j m := by
  let φ := Matrix.compAlgEquiv (Outer j) m.Index ℂ ℂ
  have hs : star (rawColumn j m * rawRow j m) = rawColumn j m * rawRow j m :=
    encoding_selfAdjoint _ _ _
  rw [← flatten_projection]
  exact congrArg φ hs

theorem step_tuple_update (j : ℕ) (m : MatrixModel) (i : Fin 4) :
    (step j m).tuple i = amplify m.Index (background j i) +
      (if i=3 then (2:ℂ) else 0) • (column j m * row j m) := by
  let φ := Matrix.compAlgEquiv (Outer j) m.Index ℂ ℂ
  have h := congrArg φ (stageTuple_background (fun _ : Fin (j+2) => false)
    (fun _ : Fin (j+2) => true) m.tuple (labels (j+2)) (@Cube.gamma (j+2)) i)
  rw [map_add, map_smul] at h
  rw [← flatten_projection]
  exact h

def direction (x : Letters) : ℂ := if Sum.elim id id x = (3:Fin 4) then 2 else 0

theorem step_letters (j : ℕ) (m : MatrixModel) (x : Letters) :
    withAdjoints (step j m).tuple x = amplify m.Index (withAdjoints (background j) x) +
      direction x • (column j m * row j m) := by
  cases x with
  | inl i => exact step_tuple_update j m i
  | inr i =>
    change star ((step j m).tuple i) = amplify m.Index (star (background j i)) +
      (if i=3 then (2:ℂ) else 0) • (column j m * row j m)
    rw [step_tuple_update]
    change star (amplify m.Index (background j i) +
      (if i=3 then (2:ℂ) else 0) • (column j m * row j m)) = _
    rw [star_add, star_smul, projection_star, amplify_star]
    by_cases h : i=3 <;> simp [h]

variable {J : Type} [Fintype J] [DecidableEq J]

/-- Removing the encoding projection from an actual stage leaves the test on the amplified
scalar background. Only the rectangular column and row retain the inner generators. -/
theorem concrete_rank_update (P : Pencil J) (hP : affine P) :
    ∃ C : Matrix J J ℂ, ∀ (j : ℕ) (m : MatrixModel), test (step j m) P =
      evalPencil P (fun x => amplify m.Index (withAdjoints (background j) x)) +
        ((1 : Matrix J J ℂ) ⊗ₖ column j m) * (C ⊗ₖ (1 : Matrix m.Index m.Index ℂ)) *
        ((1 : Matrix J J ℂ) ⊗ₖ row j m) := by
  obtain ⟨C,hC⟩ := affine_rank_update P hP direction
  refine ⟨C, fun j m => ?_⟩
  unfold test
  rw [funext (step_letters j m)]
  exact hC _ _ _

end
end MO35207.MatrixModel

end

section

/-! The scalar background of any affine test has only diagonal port blocks and one uniform coupling. -/

namespace MO35207
noncomputable section

variable {L I : Type} [Fintype L] [Fintype I] [DecidableEq L] [DecidableEq I]

abbrev PortData (L : Type) := (StageColors × L → ℂ) × (StageColors × L → ℂ) × (StageColors → ℂ)

def pattern (a : L → Matrix I I ℂ) (v : PortData L) :
    Matrix (StageSpace L I) (StageSpace L I) ℂ :=
  fun ⟨c,l,s⟩ ⟨d,k,t⟩ => if c=d then
    (if l=k then v.1 (c,l) * (1 : Matrix I I ℂ) s t + v.2.1 (c,l) * a l s t else 0) +
      v.2.2 c * (1 : Matrix I I ℂ) s t else 0

def patternMap (a : L → Matrix I I ℂ) :
    PortData L →ₗ[ℂ] Matrix (StageSpace L I) (StageSpace L I) ℂ where
  toFun := pattern a
  map_add' x y := by
    ext ⟨c,l,s⟩ ⟨d,k,t⟩
    by_cases hc : c=d <;> by_cases hl : l=k <;> simp [pattern, hc, hl] <;> ring
  map_smul' z x := by
    ext ⟨c,l,s⟩ ⟨d,k,t⟩
    by_cases hc : c=d <;> by_cases hl : l=k <;> simp [pattern, hc, hl] <;> ring

def scalarData (z : ℂ) : PortData L := ⟨fun _ => z, 0, 0⟩

omit [Fintype L] [Fintype I] in
theorem pattern_one (a : L → Matrix I I ℂ) : pattern a (scalarData 1) = 1 := by
  ext ⟨c,l,s⟩ ⟨d,k,t⟩
  by_cases hc : c=d <;> by_cases hl : l=k <;>
    simp [pattern, scalarData, hc, hl, Matrix.one_apply, Prod.mk.injEq]

omit [Fintype L] in
theorem pattern_star (a : L → Matrix I I ℂ) (ha : ∀ l, IsSelfAdjoint (a l))
    (v : PortData L) : star (pattern a v) =
      pattern a (⟨star v.1, star v.2.1, star v.2.2⟩ : PortData L) := by
  ext ⟨c,l,s⟩ ⟨d,k,t⟩
  change star (pattern a v (d,k,t) (c,l,s)) = _
  have hdelta : star ((1 : Matrix I I ℂ) t s) = (1 : Matrix I I ℂ) s t :=
    congrArg (fun M : Matrix I I ℂ => M s t) (star_one (R := Matrix I I ℂ))
  have hcoeff (l : L) : star (a l t s) = a l s t :=
    congrArg (fun M : Matrix I I ℂ => M s t) (ha l).star_eq
  by_cases hc : c=d <;> by_cases hl : l=k
  · subst d; subst k
    simp [pattern, hdelta, hcoeff, mul_comm]
  · subst d
    simp [pattern, hl, Ne.symm hl, hdelta, mul_comm]
  · simp [pattern, hc, Ne.symm hc]
  · simp [pattern, hc, Ne.symm hc]

def generatorData (z : StageColors × L → ℂ) : Fin 4 → PortData L :=
  ![⟨z,0,0⟩, ⟨fun _ => -1,0,fun _ => 2*(Fintype.card L : ℂ)⁻¹⟩,
    ⟨0,fun _ => 1,0⟩, scalarData (-1)]

theorem pattern_background (z : StageColors × L → ℂ) (a : L → Matrix I I ℂ) (i : Fin 4) :
    stageBackground z a i = pattern a (generatorData z i) := by
  ext ⟨c,l,s⟩ ⟨d,k,t⟩
  obtain ⟨h₀,h₁,h₂,h₃⟩ := background_entries z a c d l k s t
  fin_cases i
  · refine h₀.trans ?_
    by_cases hc : c=d <;> by_cases hl : l=k <;> simp [pattern, generatorData, hc, hl]
  · refine h₁.trans ?_
    by_cases hc : c=d <;> by_cases hl : l=k <;> simp [pattern, generatorData, hc, hl] <;> ring
  · refine h₂.trans ?_
    by_cases hc : c=d <;> by_cases hl : l=k <;> simp [pattern, generatorData, hc, hl]
  · refine h₃.trans ?_
    by_cases hc : c=d <;> by_cases hl : l=k <;> simp [pattern, generatorData, scalarData, hc, hl]

/-- Every affine entry of the background evaluates to a matrix with the prescribed
port structure. This includes the adjoints of all four generators. -/
theorem affine_background_pattern (z : StageColors × L → ℂ) (a : L → Matrix I I ℂ)
    (ha : ∀ l, IsSelfAdjoint (a l)) (p : FreeAlgebra ℂ MatrixModel.Letters)
    (hp : p ∈ affineForms MatrixModel.Letters) :
    ∃ v : PortData L, FreeAlgebra.lift ℂ (withAdjoints (stageBackground z a)) p = pattern a v := by
  let φ := FreeAlgebra.lift ℂ (withAdjoints (stageBackground z a))
  suffices hh : φ p ∈ (patternMap a).range by
    obtain ⟨v,hv⟩ := hh
    exact ⟨v,hv.symm⟩
  induction hp using Submodule.span_induction with
  | mem x hx =>
    rcases hx with hx | ⟨i,rfl⟩
    · subst x
      exact ⟨scalarData 1, (pattern_one a).trans (map_one φ).symm⟩
    · rw [show φ (FreeAlgebra.ι ℂ i) = withAdjoints (stageBackground z a) i from FreeAlgebra.lift_ι_apply _ _]
      cases i with
      | inl i => exact ⟨_, (pattern_background z a i).symm⟩
      | inr i =>
        change star (stageBackground z a i) ∈ _
        rw [pattern_background, pattern_star a ha]
        exact ⟨_,rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa using (patternMap a).range.add_mem hx hy
  | smul c x _ hx => simpa using (patternMap a).range.smul_mem c hx

end
end MO35207

end

section

/-! Finite matrix inverse compression for the Clifford cube. -/

namespace MO35207.Cube
noncomputable section

private theorem inverse_in_image {A D : Type*} [Ring A] [Ring D] [Algebra ℂ A] [Algebra ℂ D]
    [FiniteDimensional ℂ A] (f : A →ₐ[ℂ] D) (hf : Function.Injective f)
    (x : A) (u : Dˣ) (hu : f x = u) : ∃ y : A, f y = ↑u⁻¹ := by
  have hinj : Function.Injective (LinearMap.mulLeft ℂ x) := by
    intro y z h
    apply hf
    apply u.isUnit.isRegular.left
    change (u : D) * f y = (u : D) * f z
    rw [← hu, ← map_mul, ← map_mul]
    exact congrArg f h
  obtain ⟨y, hy⟩ := LinearMap.surjective_of_injective hinj 1
  have hprod : (u : D) * f y = 1 := by
    rw [← hu, ← map_mul, show x * y = 1 from hy, map_one]
  exact ⟨y, by calc
    f y = (↑u⁻¹ : D) * ((u : D) * f y) := by simp
    _ = ↑u⁻¹ := by rw [hprod, mul_one]⟩

/-- Inverses of finite matrices with entries in a common finite-dimensional
coefficient algebra still have entries in that same algebra. -/
theorem inverse_entries_mem {k : Type*} [Fintype k] [DecidableEq k]
    {D : Type*} [Ring D] [Algebra ℂ D] (B : Subalgebra ℂ D)
    [FiniteDimensional ℂ B] (u : (Matrix k k D)ˣ)
    (h : ∀ i j, (u : Matrix k k D) i j ∈ B) :
    ∀ i j, (↑u⁻¹ : Matrix k k D) i j ∈ B := by
  let x : Matrix k k B := fun i j => ⟨(u : Matrix k k D) i j, h i j⟩
  let f : Matrix k k B →ₐ[ℂ] Matrix k k D := B.val.mapMatrix
  have hf : Function.Injective f := by
    intro a b e
    ext i j
    exact congrArg (fun m : Matrix k k D => m i j) e
  have he : f x = u := by ext i j; rfl
  obtain ⟨y, hy⟩ := inverse_in_image f hf x u he
  intro i j
  rw [← hy]
  exact (y i j).property

/-- All entries of the pencil lie in one coefficient algebra in which
opposite-corner entries vanish. -/
theorem pencil_entry_algebra {g k : ℕ}
    (v : Fin k → Fin k → Mat g) (hv : ∀ i j, v i j ∈ vectors g)
    (c : Fin k → Fin k → ℂ) :
    ∃ B : Subalgebra ℂ (Mat g),
      (∀ i j, algebraMap ℂ (Mat g) (c i j) + v i j ∈ B) ∧
      ∀ x ∈ B, ∀ s t : Vertex g, k ^ 2 < distance s t → x s t = 0 := by
  classical
  let l := (Finset.univ : Finset (Fin k × Fin k)).toList.map (fun ij => v ij.1 ij.2)
  have hl : ∀ x ∈ l, x ∈ vectors g := by
    intro x hx
    obtain ⟨⟨i,j⟩, _, rfl⟩ := List.mem_map.mp hx
    exact hv i j
  let B := Algebra.adjoin ℂ {x | x ∈ l}
  refine ⟨B, ?_, ?_⟩
  · intro i j
    apply B.add_mem (B.algebraMap_mem _)
    apply Algebra.subset_adjoin
    exact List.mem_map.mpr ⟨(i,j), by simp, rfl⟩
  · intro x hx s t hst
    exact corner_vanishes l hl s t (by simpa [l, pow_two] using hst) hx

/-- If the entries of an invertible k-by-k block pencil are scalars plus
Clifford vectors, every inverse block has zero opposite-corner entry as
soon as k² < g. Scalar and matrix coefficients may be non-Hermitian. -/
theorem inverse_pencil_corner {g k : ℕ} (hk : k ^ 2 < g)
    (v : Fin k → Fin k → Mat g) (hv : ∀ i j, v i j ∈ vectors g)
    (c : Fin k → Fin k → ℂ) (u : (Matrix (Fin k) (Fin k) (Mat g))ˣ)
    (hu : ∀ i j, (u : Matrix (Fin k) (Fin k) (Mat g)) i j =
      algebraMap ℂ (Mat g) (c i j) + v i j) :
    ∀ i j, (↑u⁻¹ : Matrix (Fin k) (Fin k) (Mat g)) i j
      (fun _ => false) (fun _ => true) = 0 := by
  obtain ⟨B, hB, hvanish⟩ := pencil_entry_algebra v hv c
  intro i j
  apply hvanish _ (inverse_entries_mem B u (fun i j => (hu i j).symm ▸ hB i j) i j)
  simpa [distance] using hk

end
end MO35207.Cube

end

section

/-! A finite block-diagonal background with a common coupling between its blocks. -/

namespace MO35207.Cube
noncomputable section
variable {g k : ℕ}

private def oneDirection (i : Fin g) : Subalgebra ℂ (Mat g) where
  carrier := {x | ∃ a b : ℂ, x = a • (1 : Mat g) + b • gamma i}
  algebraMap_mem' c := ⟨c, 0, by simp [Algebra.algebraMap_eq_smul_one]⟩
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a + c, b + d, by simp only [add_smul]; abel⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a*c + b*d, a*d + b*c, ?_⟩
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_one, one_mul,
      gamma_square, add_smul]
    module

/-- Summing inverse blocks that each use only one Clifford direction produces a
matrix with entries in one common corner-vanishing algebra. -/
theorem sum_inverse_entry_algebra
    (d : Fin g → (Matrix (Fin k) (Fin k) (Mat g))ˣ)
    (hd : ∀ l i j, ∃ a b : ℂ, (d l : Matrix (Fin k) (Fin k) (Mat g)) i j =
      a • (1 : Mat g) + b • gamma l) :
    ∃ B : Subalgebra ℂ (Mat g),
      (∀ i j, (∑ l, (↑(d l)⁻¹ : Matrix (Fin k) (Fin k) (Mat g))) i j ∈ B) ∧
      ∀ x ∈ B, ∀ s t : Vertex g, k ^ 2 < distance s t → x s t = 0 := by
  classical
  have hi (l : Fin g) (i j : Fin k) : ∃ a b : ℂ,
      (↑(d l)⁻¹ : Matrix (Fin k) (Fin k) (Mat g)) i j = a • (1 : Mat g) + b • gamma l :=
    inverse_entries_mem (oneDirection l) (d l) (hd l) i j
  choose a b hab using hi
  let v (i j : Fin k) := ∑ l, b l i j • gamma l
  have hv i j : v i j ∈ vectors g := by
    apply Submodule.sum_mem
    intro l _
    exact (vectors g).smul_mem _ (Submodule.subset_span ⟨l, rfl⟩)
  obtain ⟨B, hB, hvanish⟩ := pencil_entry_algebra v hv (fun i j => ∑ l, a l i j)
  refine ⟨B, fun i j => ?_, hvanish⟩
  convert hB i j using 1
  simp [Matrix.sum_apply, hab, Finset.sum_add_distrib, Algebra.algebraMap_eq_smul_one, v]

/-- Compressing an inverse after a matrix update can be computed entirely in the
algebra generated by the old compression and the coupling matrix. The rectangular
matrices U,V may have different source and target sizes, and no adjoint hypothesis
is needed. -/
theorem compression_mem {h n : Type*} [Fintype h] [DecidableEq h]
    [Fintype n] [DecidableEq n] {A : Type*} [Ring A] [Algebra ℂ A]
    (B : Subalgebra ℂ A) [FiniteDimensional ℂ B]
    (D F : (Matrix h h A)ˣ) (U : Matrix n h A) (V : Matrix h n A) (K : Matrix n n A)
    (hF : (F : Matrix h h A) = (D : Matrix h h A) + V*K*U)
    (hR : ∀ i j, (U * (↑D⁻¹ : Matrix h h A) * V) i j ∈ B)
    (hK : ∀ i j, K i j ∈ B) :
    ∀ i j, (U * (↑F⁻¹ : Matrix h h A) * V) i j ∈ B := by
  let R := U * (↑D⁻¹ : Matrix h h A) * V
  let T := U * (↑F⁻¹ : Matrix h h A) * V
  have hid : (↑D⁻¹ : Matrix h h A) =
      (↑F⁻¹ : Matrix h h A) + (↑D⁻¹ : Matrix h h A) * (V*K*U) * (↑F⁻¹ : Matrix h h A) := by
    calc
      (↑D⁻¹ : Matrix h h A) = (↑D⁻¹ : Matrix h h A) * (F : Matrix h h A) * (↑F⁻¹ : Matrix h h A) := by
        rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [hF, Matrix.mul_add, Matrix.add_mul, Units.inv_mul, Matrix.one_mul]
  have hid' : (↑D⁻¹ : Matrix h h A) =
      (↑F⁻¹ : Matrix h h A) + (↑F⁻¹ : Matrix h h A) * (V*K*U) * (↑D⁻¹ : Matrix h h A) := by
    calc
      (↑D⁻¹ : Matrix h h A) = (↑F⁻¹ : Matrix h h A) * (F : Matrix h h A) * (↑D⁻¹ : Matrix h h A) := by
        rw [Units.inv_mul, Matrix.one_mul]
      _ = _ := by
        rw [Matrix.mul_assoc, hF, Matrix.add_mul, Units.mul_inv, Matrix.mul_add, Matrix.mul_one,
          Matrix.mul_assoc]
        simp only [Matrix.mul_assoc]
  have hr : R = T + R*K*T := by
    calc
      R = U * ((↑F⁻¹ : Matrix h h A) + (↑D⁻¹ : Matrix h h A) * (V*K*U) * (↑F⁻¹ : Matrix h h A)) * V := by
        exact congrArg (fun Y : Matrix h h A => U*Y*V) hid
      _ = _ := by simp only [R, T, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have hl : R = T + T*K*R := by
    calc
      R = U * ((↑F⁻¹ : Matrix h h A) + (↑F⁻¹ : Matrix h h A) * (V*K*U) * (↑D⁻¹ : Matrix h h A)) * V := by
        exact congrArg (fun Y : Matrix h h A => U*Y*V) hid'
      _ = _ := by simp only [R, T, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  let q : (Matrix n n A)ˣ :=
    ⟨1 + R*K, 1 - T*K, by
      calc
        _ = 1 + (R - (T + R*K*T))*K := by noncomm_ring
        _ = 1 := by rw [← hr]; simp,
     by
      calc
        _ = 1 + (R - (T + T*K*R))*K := by noncomm_ring
        _ = 1 := by rw [← hl]; simp⟩
  let S : Subring (Matrix n n A) := B.toSubring.matrix
  have hq : (q : Matrix n n A) ∈ S := S.add_mem S.one_mem (S.mul_mem hR hK)
  have hqi : (↑q⁻¹ : Matrix n n A) ∈ S := inverse_entries_mem B q hq
  have heq : (q : Matrix n n A)*T = R := by
    change (1+R*K)*T = R
    rw [add_mul, one_mul, ← hr]
  have ht : T = (↑q⁻¹ : Matrix n n A)*R := by
    rw [← heq, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  change T ∈ S
  rw [ht]
  exact S.mul_mem hqi hR

end
end MO35207.Cube

end

section

/-! Opposite-corner cancellation for a uniformly coupled family of Clifford blocks. -/

namespace MO35207.Cube
noncomputable section

abbrev Block (g k : ℕ) := Matrix (Fin k) (Fin k) (Mat g)
abbrev PortMatrix (g k : ℕ) := Matrix (Fin k × Fin g) (Fin k × Fin g) (Mat g)

def portRow (g k : ℕ) : Matrix (Fin k) (Fin k × Fin g) (Mat g) :=
  fun i p => if i = p.1 then 1 else 0

def portCol (g k : ℕ) : Matrix (Fin k × Fin g) (Fin k) (Mat g) :=
  fun p i => if p.1 = i then 1 else 0

private theorem diagonal_compression {g k : ℕ} (b : Fin g → Block g k) :
    portRow g k * Matrix.blockDiagonal b * portCol g k = ∑ l, b l := by
  classical
  apply Matrix.ext
  intro i j
  simp [Matrix.mul_apply, Matrix.blockDiagonal_apply, portRow, portCol, Fintype.sum_prod_type,
    ite_mul, mul_ite, Matrix.sum_apply]

/-- For an invertible uniform coupling of invertible Clifford blocks, the
compressed inverse vanishes between either pair of opposite corners whenever
the cube dimension exceeds the squared pencil size. -/
theorem coupled_inverse_corner {g k : ℕ} (hk : k ^ 2 < g)
    (d : Fin g → (Block g k)ˣ)
    (hd : ∀ l i j, ∃ a b : ℂ, (d l : Block g k) i j = a • (1 : Mat g) + b • gamma l)
    (K : Matrix (Fin k) (Fin k) ℂ)
    (F : (PortMatrix g k)ˣ)
    (hF : (F : PortMatrix g k) = Matrix.blockDiagonal (fun l => (d l : Block g k)) +
      portCol g k * K.map (algebraMap ℂ (Mat g)) * portRow g k) :
    ∀ i j (s : Vertex g),
      (portRow g k * (↑F⁻¹ : PortMatrix g k) * portCol g k) i j s (fun t => !(s t)) = 0 := by
  let du : (Fin g → Block g k)ˣ :=
    ⟨fun l => d l, fun l => ↑(d l)⁻¹, funext (fun l => (d l).val_inv),
      funext (fun l => (d l).inv_val)⟩
  let D := Units.map (Matrix.blockDiagonalRingHom (Fin k) (Fin g) (Mat g)).toMonoidHom du
  obtain ⟨B, hB, hvanish⟩ := sum_inverse_entry_algebra d hd
  have hR : ∀ i j, (portRow g k * (↑D⁻¹ : PortMatrix g k) * portCol g k) i j ∈ B := by
    change ∀ i j, (portRow g k * Matrix.blockDiagonal (fun l => (↑(d l)⁻¹ : Block g k)) *
      portCol g k) i j ∈ B
    rw [diagonal_compression]
    exact hB
  have hK : ∀ i j, K.map (algebraMap ℂ (Mat g)) i j ∈ B := fun i j => B.algebraMap_mem (K i j)
  have hout := compression_mem B D F (portRow g k) (portCol g k) _ hF hR hK
  intro i j s
  apply hvanish _ (hout i j)
  simpa [distance] using hk

end
end MO35207.Cube

end

section

/-! Independence of the inner unitary at a single stage above the cutoff. -/

namespace MO35207
noncomputable section
variable {I A : Type*} [Fintype I] [DecidableEq I] [Ring A] [StarRing A]
  [Algebra ℂ A]

/-- Below the cutoff the result is still affine in the same inner unitary and its adjoint. -/
theorem endpoint_pencil (lo hi : I) (u : A) (hu : star u * u = 1) (M : Matrix I I ℂ) :
    (∑ i, star (endColumn lo hi u i) * ∑ j, M i j • endColumn lo hi u j) =
      (M lo lo + M hi hi) • (1 : A) + M lo hi • u + M hi lo • star u := by
  rw [endpoint_compression]
  simp only [mul_add, mul_smul_comm, mul_one, hu, add_smul]
  abel

open _root_.MO35207.Cube in
/-- At a stage with g > k², the compressed background resolvent is a scalar
matrix tensored with the identity on the entire inner space. Its coefficients
are independent of the inner unitary and its dimension. -/
theorem coupled_stage_scalar {g k : ℕ} (hk : k ^ 2 < g)
    (d : Fin g → (Block g k)ˣ)
    (hd : ∀ l i j, ∃ a b : ℂ, (d l : Block g k) i j = a • (1 : Mat g) + b • gamma l)
    (K : Matrix (Fin k) (Fin k) ℂ) (F : (PortMatrix g k)ˣ)
    (hF : (F : PortMatrix g k) = Matrix.blockDiagonal (fun l => (d l : Block g k)) +
      portCol g k * K.map (algebraMap ℂ (Mat g)) * portRow g k) :
    ∃ Z : Matrix (Fin k) (Fin k) ℂ, ∀ (D : Type) [Ring D] [StarRing D] [Algebra ℂ D]
      (u : D), star u * u = 1 → ∀ i j,
      (∑ s : Vertex g, star (endColumn (fun _ => false) (fun _ => true) u s) *
        ∑ t : Vertex g, (portRow g k * (↑F⁻¹ : PortMatrix g k) * portCol g k) i j s t •
          endColumn (fun _ => false) (fun _ => true) u t) = algebraMap ℂ D (Z i j) := by
  let G := portRow g k * (↑F⁻¹ : PortMatrix g k) * portCol g k
  let lo : Vertex g := fun _ => false
  let hi : Vertex g := fun _ => true
  refine ⟨fun i j => G i j lo lo + G i j hi hi, ?_⟩
  intro D _ _ _ u hu i j
  have h01 : G i j lo hi = 0 := coupled_inverse_corner hk d hd K F hF i j lo
  have h10 : G i j hi lo = 0 := coupled_inverse_corner hk d hd K F hF i j hi
  change (∑ s, star (endColumn lo hi u s) * ∑ t, (G i j) s t • endColumn lo hi u t) = _
  rw [endpoint_pencil lo hi u hu (G i j), h01, h10]
  simp [Algebra.algebraMap_eq_smul_one]

end
end MO35207

end

section

/-! Collect the two corner terms from every color into one affine pencil, at the original width. -/

namespace MO35207
noncomputable section
open MatrixModel

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

private def phase (b : Bool) : ℂ := if b then Complex.I else 1

private theorem phase_eq {D : Type*} [Ring D] [Algebra ℂ D] (u : Fin 4 → D) (c : StageColors) :
    phaseCopies u c = phase c.2 • u c.1 := by
  rcases c with ⟨i,_ | _⟩ <;> simp [phase,phaseCopies]

def cornerForm (lo hi : I) (c : StageColors) (R : Matrix I I ℂ) : FreeAlgebra ℂ Letters :=
  algebraMap ℂ _ (R lo lo + R hi hi) +
    (R lo hi * phase c.2) • FreeAlgebra.ι ℂ (Sum.inl c.1) +
    (R hi lo * star (phase c.2)) • FreeAlgebra.ι ℂ (Sum.inr c.1)

private theorem letter_affine (x : Letters) : FreeAlgebra.ι ℂ x ∈ affineForms Letters :=
  Submodule.subset_span (Set.mem_insert_of_mem _ ⟨x,rfl⟩)

omit [Fintype I] [DecidableEq I] in
private theorem corner_affine (lo hi : I) (c : StageColors) (R : Matrix I I ℂ) :
    cornerForm lo hi c R ∈ affineForms Letters :=
  (affineForms _).add_mem ((affineForms _).add_mem (affine_scalar _) ((affineForms _).smul_mem _ (letter_affine _)))
    ((affineForms _).smul_mem _ (letter_affine _))

omit [Fintype J] [DecidableEq J] in
theorem evaluate_corner {D : Type} [Ring D] [StarRing D] [Algebra ℂ D] [StarModule ℂ D]
    (lo hi : I) (c : StageColors) (R : Matrix I I ℂ) (u : Fin 4 → D)
    (hu : ∀ i, star (u i)*u i = 1) :
    FreeAlgebra.lift ℂ (withAdjoints u) (cornerForm lo hi c R) =
      ∑ s, star (endColumn lo hi (phaseCopies u c) s) *
        ∑ t, R s t • endColumn lo hi (phaseCopies u c) t := by
  rw [endpoint_pencil _ _ _ (phaseCopies_isometry u hu c), phase_eq]
  simp [cornerForm, withAdjoints, Algebra.algebraMap_eq_smul_one, star_smul, smul_smul]

/-- The identity plus the scaled, left-multiplied sum of all compressed color blocks. -/
def innerTest (lo hi : I) (scale : ℂ) (K : Matrix J J ℂ)
    (R : StageColors → J → J → Matrix I I ℂ) : Pencil J := fun i j =>
  algebraMap ℂ _ ((1 : Matrix J J ℂ) i j) +
    ∑ k, (scale * K i k) • ∑ c, cornerForm lo hi c (R c k j)

omit [Fintype I] [DecidableEq I] in
theorem innerTest_affine (lo hi : I) (scale : ℂ) (K : Matrix J J ℂ)
    (R : StageColors → J → J → Matrix I I ℂ) : affine (innerTest lo hi scale K R) := by
  intro i j
  apply Submodule.add_mem _ (affine_scalar _)
  exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun c _ =>
    corner_affine lo hi c (R c k j))))

omit [Fintype I] [DecidableEq I] in
theorem innerTest_scalar (lo hi : I) (scale : ℂ) (K : Matrix J J ℂ)
    (R : StageColors → J → J → Matrix I I ℂ)
    (hcross : ∀ c i j, R c i j lo hi = 0 ∧ R c i j hi lo = 0) :
    ∃ B : Matrix J J ℂ, ∀ i j, innerTest lo hi scale K R i j =
      algebraMap ℂ (FreeAlgebra ℂ Letters) (B i j) := by
  refine ⟨fun i j => (1 : Matrix J J ℂ) i j +
    ∑ k, (scale * K i k) * ∑ c, ((R c k j) lo lo + (R c k j) hi hi), ?_⟩
  intro i j
  simp only [innerTest, cornerForm, (hcross _ _ _).1, (hcross _ _ _).2, zero_mul,
    map_zero, add_zero, map_add, map_sum, map_mul, Algebra.smul_def]

end
end MO35207

end

section

/-! Compressing a color-diagonal inverse by the repeated endpoint columns. -/

namespace MO35207
noncomputable section

variable {J L I D : Type} [Fintype J] [Fintype L] [Fintype I]
  [DecidableEq J] [DecidableEq L] [DecidableEq I] [Ring D] [StarRing D] [Algebra ℂ D]

abbrev ColorBlocks (J L I : Type) := StageColors → Matrix (J × L) (J × L) (Matrix I I ℂ)

def assembleColors (F : ColorBlocks J L I) :
    Matrix (J × StageSpace L I) (J × StageSpace L I) ℂ :=
  fun ⟨i,c,l,s⟩ ⟨j,d,k,t⟩ => if c=d then F c (i,l) (j,k) s t else 0

def uniformColumn (e : StageColors → I → D) : Matrix (J × StageSpace L I) J D :=
  fun ⟨j,c,_,s⟩ i => if j=i then e c s else 0

def uniformRow (e : StageColors → I → D) : Matrix J (J × StageSpace L I) D :=
  fun i ⟨j,c,_,s⟩ => if i=j then star (e c s) else 0

def portSum (F : ColorBlocks J L I) (c : StageColors) (i j : J) : Matrix I I ℂ :=
  fun s t => ∑ l, ∑ k, F c (i,l) (j,k) s t

/-- The test-space indices survive compression. The sums over the two ports enter only
through the corresponding compressed background block. -/
theorem color_compression (F : ColorBlocks J L I) (e : StageColors → I → D) (i j : J) :
    (uniformRow (J := J) (L := L) e * (Algebra.ofId ℂ D).mapMatrix (assembleColors F) *
      uniformColumn (J := J) (L := L) e) i j =
      ∑ c, ∑ s, star (e c s) * ∑ t, portSum F c i j s t • e c t := by
  classical
  rw [Matrix.mul_assoc]
  have hinner (c : StageColors) (l : L) (s : I) :
      (((Algebra.ofId ℂ D).mapMatrix (assembleColors F)) * uniformColumn (J := J) (L := L) e) (i,c,l,s) j =
        ∑ k, ∑ t, F c (i,l) (j,k) s t • e c t := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single j]
    · rw [Fintype.sum_prod_type, Finset.sum_eq_single c]
      · rw [Fintype.sum_prod_type]
        simp [uniformColumn, assembleColors, Algebra.smul_def]
      · intro d _ hdc
        apply Finset.sum_eq_zero
        rintro ⟨k,t⟩ _
        simp [assembleColors, Ne.symm hdc]
      · simp
    · intro b _ hbj
      apply Finset.sum_eq_zero
      rintro ⟨d,k,t⟩ _
      simp [uniformColumn, hbj]
    · simp
  have hrow : (uniformRow (J := J) (L := L) e *
      (((Algebra.ofId ℂ D).mapMatrix (assembleColors F)) * uniformColumn (J := J) (L := L) e)) i j =
      ∑ c, ∑ l, ∑ s, star (e c s) * ∑ k, ∑ t, F c (i,l) (j,k) s t • e c t := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single i]
    · rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro c _
      rw [Fintype.sum_prod_type]
      simp only [uniformRow, if_true, hinner]
    · intro b _ hbi
      apply Finset.sum_eq_zero
      rintro ⟨d,k,t⟩ _
      simp [uniformRow, Ne.symm hbi]
    · simp
  rw [hrow]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.mul_sum]
  congr 1
  simp only [portSum, Finset.sum_smul]
  calc
    _ = ∑ l, ∑ t, ∑ k, F c (i,l) (j,k) s t • e c t := by
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

open _root_.MO35207.Cube in
/-- These are precisely the entries to which the Clifford cancellation theorem applies. -/
theorem portSum_eq_compressed {g k : ℕ} (F : ColorBlocks (Fin k) (Fin g) (Cube.Vertex g))
    (c : StageColors) (i j : Fin k) :
    portSum F c i j = (portRow g k * F c * portCol g k) i j := by
  have hc (p : Fin k × Fin g) : (F c * portCol g k) p j = ∑ l, F c p (j,l) := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single j]
    · simp [portCol]
    · intro b _ hbj
      simp [portCol, hbj]
    · simp
  rw [Matrix.mul_assoc]
  have hr : (portRow g k * (F c * portCol g k)) i j = ∑ l, ∑ t, F c (i,l) (j,t) := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single i]
    · simp [portRow,hc]
    · intro b _ hbi
      simp [portRow, Ne.symm hbi]
    · simp
  rw [hr]
  ext s t
  simp [portSum, Matrix.sum_apply]

end
end MO35207

end

section

/-! The color-block embedding preserves products, scalar amplification, and inverses. -/

namespace MO35207
noncomputable section

variable {J L I : Type} [Fintype J] [Fintype L] [Fintype I]
  [DecidableEq J] [DecidableEq L] [DecidableEq I]

private def colorOrder : (((J × L) × StageColors) × I) ≃ (J × StageSpace L I) where
  toFun := fun ⟨⟨⟨j,l⟩,c⟩,s⟩ => (j,c,l,s)
  invFun := fun ⟨j,c,l,s⟩ => (((j,l),c),s)
  left_inv _ := rfl
  right_inv _ := rfl

private def assembleHom : ColorBlocks J L I →+* Matrix (J × StageSpace L I) (J × StageSpace L I) ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ colorOrder).toRingHom.comp
    ((Matrix.compAlgEquiv ((J × L) × StageColors) I ℂ ℂ).toRingHom.comp
      (Matrix.blockDiagonalRingHom (J × L) StageColors (Matrix I I ℂ)))

private theorem assembleHom_apply (F : ColorBlocks J L I) : assembleHom F = assembleColors F := by
  ext ⟨i,c,l,s⟩ ⟨j,d,k,t⟩
  change (if c=d then F c (i,l) (j,k) else 0) s t = if c=d then F c (i,l) (j,k) s t else 0
  by_cases h : c=d <;> simp [h]

def colorAssembly : ColorBlocks J L I →ₐ[ℂ] Matrix (J × StageSpace L I) (J × StageSpace L I) ℂ where
  __ := assembleHom
  commutes' z := by
    change assembleHom (algebraMap ℂ (ColorBlocks J L I) z) = _
    rw [assembleHom_apply]
    ext ⟨i,c,l,s⟩ ⟨j,d,k,t⟩
    change (if c=d then ((algebraMap ℂ (Matrix (J × L) (J × L) (Matrix I I ℂ)) z) (i,l) (j,k)) s t
      else 0) = algebraMap ℂ (Matrix (J × StageSpace L I) (J × StageSpace L I) ℂ) z (i,c,l,s) (j,d,k,t)
    by_cases hj : i=j <;> by_cases hc : c=d <;> by_cases hl : l=k <;> by_cases hs : s=t <;>
      simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply, Prod.mk.injEq, hj, hc, hl, hs]

theorem colorAssembly_apply (F : ColorBlocks J L I) : colorAssembly F = assembleColors F :=
  assembleHom_apply F

/-- The inverse of a block-diagonal background is assembled from the inverses of
the actual color blocks. -/
theorem colorAssembly_inverse (F : (c : StageColors) → (Matrix (J × L) (J × L) (Matrix I I ℂ))ˣ) :
    ∃ D : (Matrix (J × StageSpace L I) (J × StageSpace L I) ℂ)ˣ,
      ↑D = assembleColors (fun c => (F c).val) ∧
      ↑D⁻¹ = assembleColors (fun c => (F c).inv) := by
  let f : (ColorBlocks J L I)ˣ := ⟨fun c => (F c).val, fun c => (F c).inv,
    funext (fun c => (F c).val_inv), funext (fun c => (F c).inv_val)⟩
  let d := Units.map (colorAssembly (J := J) (L := L) (I := I)).toMonoidHom f
  exact ⟨d, colorAssembly_apply _, colorAssembly_apply _⟩

end
end MO35207

end

section

/-! Identify the actual scalar background with a uniform perturbation of Clifford port blocks. -/

namespace MO35207
noncomputable section
open _root_.MO35207.Cube

variable {g k : ℕ}

abbrev Table (g k : ℕ) := Fin k → Fin k → PortData (Fin g)

def portDiagonal (x : Table g k) (c : StageColors) (l : Fin g) : Block g k :=
  fun i j => (x i j).1 (c,l) • (1 : Mat g) + (x i j).2.1 (c,l) • gamma l

def uniformCoefficient (x : Table g k) (c : StageColors) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j => (x i j).2.2 c

def portPencil (x : Table g k) (c : StageColors) : PortMatrix g k :=
  Matrix.blockDiagonal (portDiagonal x c) + portCol g k *
    (uniformCoefficient x c).map (algebraMap ℂ (Mat g)) * portRow g k

theorem uniform_coupling_entry (K : Matrix (Fin k) (Fin k) ℂ) (i j : Fin k) (l h : Fin g) :
    (portCol g k * K.map (algebraMap ℂ (Mat g)) * portRow g k) (i,l) (j,h) =
      algebraMap ℂ (Mat g) (K i j) := by
  have hcol (r : Fin k) :
      (portCol g k * K.map (algebraMap ℂ (Mat g))) (i,l) r = algebraMap ℂ (Mat g) (K i r) := by
    simp [Matrix.mul_apply,portCol,ite_mul]
  rw [Matrix.mul_apply]
  simp [portRow, mul_ite, hcol]

theorem background_port_pencil (j : ℕ) (P : MatrixModel.Pencil (Fin k)) (hP : MatrixModel.affine P) :
    ∃ x : Table (j+2) k, evalPencil P (withAdjoints (MatrixModel.background j)) =
      assembleColors (portPencil x) := by
  choose x hx using fun r s => affine_background_pattern (MatrixModel.labels (j+2))
    (@gamma (j+2)) gamma_selfAdjoint (P r s) (hP r s)
  refine ⟨x, ?_⟩
  apply Matrix.ext
  rintro ⟨r,c,l,s⟩ ⟨v,d,h,t⟩
  apply (congrArg (fun M : Matrix (MatrixModel.Outer j) (MatrixModel.Outer j) ℂ =>
    M (c,l,s) (d,h,t)) (hx r v)).trans
  change pattern (@gamma (j+2)) (x r v) (c,l,s) (d,h,t) =
    (if c=d then (portPencil x c) (r,l) (v,h) s t else 0)
  by_cases hc : c=d <;> by_cases hl : l=h <;>
    simp [pattern, portPencil, uniform_coupling_entry, portDiagonal, uniformCoefficient,
      Matrix.blockDiagonal_apply, hc, hl, Algebra.algebraMap_eq_smul_one]

theorem deformed_port_pencil (x : Table g k) (c : StageColors) (t : ℂ) :
    1+t • (portPencil x c-1) =
      Matrix.blockDiagonal (fun l => 1+t • (portDiagonal x c l-1)) + portCol g k *
        (t • uniformCoefficient x c).map (algebraMap ℂ (Mat g)) * portRow g k := by
  ext ⟨i,l⟩ ⟨j,h⟩ s v
  by_cases hl : l=h <;> by_cases hi : i=j <;> by_cases hs : s=v <;>
    simp [portPencil, uniform_coupling_entry, Matrix.blockDiagonal_apply, Matrix.one_apply,
      Algebra.algebraMap_eq_smul_one, Prod.mk.injEq, hl, hi, hs] <;> ring

theorem deformed_one_direction (x : Table g k) (c : StageColors) (l : Fin g) (t : ℂ) (i j : Fin k) :
    ∃ a b : ℂ, (1+t • (portDiagonal x c l-1)) i j = a • (1 : Mat g) + b • gamma l := by
  let δ : ℂ := if i=j then 1 else 0
  refine ⟨δ+t*((x i j).1 (c,l)-δ),t*(x i j).2.1 (c,l), ?_⟩
  by_cases h : i=j <;> simp [δ, portDiagonal, h] <;> module

end
end MO35207

end

section

/-! Factor the determinant of the actual stage through the compressed inverse background. -/

namespace MO35207
noncomputable section
open scoped Kronecker

variable {X J B N : Type} [Fintype J] [Fintype B] [Fintype N]
  [DecidableEq J] [DecidableEq B] [DecidableEq N]

def groupedAmplify (N : Type) [Fintype N] [DecidableEq N] :
    Matrix (J × B) (J × B) ℂ →ₐ[ℂ] Matrix (J × B × N) (J × B × N) ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodAssoc J B N)).toAlgHom.comp (amplify N)

theorem groupedAmplify_det (D : Matrix (J × B) (J × B) ℂ) :
    (groupedAmplify N D).det = D.det ^ Fintype.card N := by
  change (Matrix.reindex (Equiv.prodAssoc J B N) (Equiv.prodAssoc J B N) (amplify N D)).det = _
  rw [Matrix.det_reindex_self, amplify_det]

theorem eval_amplified (P : Matrix J J (FreeAlgebra ℂ X)) (a : X → Matrix B B ℂ) :
    evalPencil P (fun x => amplify N (a x)) = groupedAmplify N (evalPencil P a) := by
  have he : (amplify N).comp (FreeAlgebra.lift ℂ a) = FreeAlgebra.lift ℂ (fun x => amplify N (a x)) := by
    ext x
    simp
  apply Matrix.ext
  rintro ⟨i,b,n⟩ ⟨j,c,n'⟩
  exact congrArg (fun M : Matrix (B × N) (B × N) ℂ => M (b,n) (c,n'))
    (DFunLike.congr_fun he.symm (P i j))

private theorem grouped_deformed_update (D : (Matrix (J × B) (J × B) ℂ)ˣ) (t : ℂ)
    (B₀ : Matrix (J × B) (J × B) ℂ) (A : Matrix (J × B × N) (J × B × N) ℂ)
    (V : Matrix (J × B × N) (J × N) ℂ) (K : Matrix (J × N) (J × N) ℂ)
    (W : Matrix (J × N) (J × B × N) ℂ) (hd : (D : Matrix (J × B) (J × B) ℂ) = 1+t • (B₀-1))
    (ha : A = groupedAmplify N B₀ + V*K*W) :
    (1+t • (A-1)).det = (D : Matrix (J × B) (J × B) ℂ).det ^ Fintype.card N *
      (1+(t • K)*W*groupedAmplify N (↑D⁻¹ : Matrix (J × B) (J × B) ℂ)*V).det := by
  let D' := Units.map (groupedAmplify (J := J) (B := B) N).toMonoidHom D
  have hbase : (D' : Matrix (J × B × N) (J × B × N) ℂ) = 1+t • (groupedAmplify N B₀-1) := by
    change groupedAmplify N (D : Matrix (J × B) (J × B) ℂ) = _
    rw [hd, map_add, map_smul, map_sub, map_one]
  have hsplit : 1+t • (A-1) = (D' : Matrix (J × B × N) (J × B × N) ℂ) + V*(t • K)*W := by
    rw [ha, hbase, Matrix.mul_smul, Matrix.smul_mul]
    module
  calc
    _ = ((D' : Matrix (J × B × N) (J × B × N) ℂ) + V*(t • K)*W).det :=
      congrArg Matrix.det hsplit
    _ = _ := (determinant_update D' V (t • K) W).trans (by
      exact congrArg (· * _) (groupedAmplify_det (N := N) (D : Matrix (J × B) (J × B) ℂ)))

namespace MatrixModel

/-- The determinant of the background is independent of the inner tuple. The only
remaining dependence is in the compression of its amplified inverse. -/
theorem concrete_determinant_factor (P : Pencil J) (hP : affine P) :
    ∃ C : Matrix J J ℂ, ∀ (j : ℕ) (t : ℂ) (D : (Matrix (J × Outer j) (J × Outer j) ℂ)ˣ),
      (D : Matrix (J × Outer j) (J × Outer j) ℂ) =
        1+t • (evalPencil P (withAdjoints (background j))-1) →
      ∀ m : MatrixModel, (1+t • (test (step j m) P-1)).det =
        (D : Matrix (J × Outer j) (J × Outer j) ℂ).det ^ m.order *
        (1 + (t • (C ⊗ₖ (1 : Matrix m.Index m.Index ℂ))) *
          ((1 : Matrix J J ℂ) ⊗ₖ row j m) *
          groupedAmplify m.Index (↑D⁻¹ : Matrix (J × Outer j) (J × Outer j) ℂ) *
          ((1 : Matrix J J ℂ) ⊗ₖ column j m)).det := by
  obtain ⟨C,hC⟩ := concrete_rank_update P hP
  refine ⟨C, ?_⟩
  intro j t D hD m
  have hx := hC j m
  rw [eval_amplified] at hx
  exact grouped_deformed_update (N := m.Index) D t _ _ _ _ _ hD hx

end MatrixModel
end
end MO35207

end

section

/-! Simultaneous regularity and the cutoff for the inverse of the actual stage background. -/

namespace MO35207
noncomputable section
open _root_.MO35207.Cube
open MatrixModel

private theorem bad_nested {H V : Type} [Fintype H] [Fintype V] [DecidableEq H] [DecidableEq V]
    (M : Matrix H H (Matrix V V ℂ)) : {t : ℂ | ¬ IsUnit (1+t • (M-1))}.Finite := by
  let e := Matrix.compAlgEquiv H V ℂ ℂ
  apply (finite_singular_parameters (e (M-1))).subset
  intro t ht hu
  apply ht
  have hh := hu.map e.symm.toMonoidHom
  change IsUnit (e.symm (1+t • e (M-1))) at hh
  simpa only [map_add, map_one, map_smul, AlgEquiv.symm_apply_apply] using hh

theorem regular_background {k : ℕ} (j : ℕ) (P : Pencil (Fin k)) (hP : affine P) :
    Set.Infinite {t : ℂ | ∃ (D : (Matrix (Fin k × Outer j) (Fin k × Outer j) ℂ)ˣ)
      (F : StageColors → (PortMatrix (j+2) k)ˣ),
      (D : Matrix (Fin k × Outer j) (Fin k × Outer j) ℂ) =
        1+t • (evalPencil P (withAdjoints (background j))-1) ∧
      (↑D⁻¹ : Matrix (Fin k × Outer j) (Fin k × Outer j) ℂ) =
        assembleColors (fun c => (F c).inv) ∧
      (k^2 < j+2 → ∀ c r s,
        let R := portSum (fun c => (F c).inv) c r s
        R (fun _ => false) (fun _ => true) = 0 ∧ R (fun _ => true) (fun _ => false) = 0)} := by
  obtain ⟨x,hx⟩ := background_port_pencil j P hP
  let badF := ⋃ c, {t : ℂ | ¬ IsUnit (1+t • (portPencil x c-1))}
  let badD := ⋃ c, ⋃ l, {t : ℂ | ¬ IsUnit (1+t • (portDiagonal x c l-1))}
  have hf : badF.Finite := Set.finite_iUnion (fun c => bad_nested (portPencil x c))
  have hd : badD.Finite := Set.finite_iUnion (fun c => Set.finite_iUnion (fun l => bad_nested (portDiagonal x c l)))
  apply (hf.union hd).infinite_compl.mono
  intro t ht
  have huF (c : StageColors) : IsUnit (1+t • (portPencil x c-1)) := by
    by_contra hn
    exact ht (Or.inl (Set.mem_iUnion.mpr ⟨c,hn⟩))
  have huD (c : StageColors) (l : Fin (j+2)) : IsUnit (1+t • (portDiagonal x c l-1)) := by
    by_contra hn
    exact ht (Or.inr (Set.mem_iUnion.mpr ⟨c,Set.mem_iUnion.mpr ⟨l,hn⟩⟩))
  choose F hF using huF
  choose d hD using huD
  obtain ⟨D,hval,hinv⟩ := colorAssembly_inverse F
  refine ⟨D,F,?_,hinv,?_⟩
  · have hfun : (fun c => (F c).val) = 1+t • (portPencil x-1) := funext hF
    calc
      _ = colorAssembly (fun c => (F c).val) := hval.trans (colorAssembly_apply _).symm
      _ = 1+t • (evalPencil P (withAdjoints (background j))-1) := by
        rw [hfun, map_add, map_one, map_smul, map_sub, map_one, colorAssembly_apply, hx]
  · intro hwidth c r s
    have hone (l : Fin (j+2)) (i v : Fin k) : ∃ a b : ℂ,
        (d c l).val i v = a • (1 : Mat (j+2)) + b • gamma l := by
      rw [hD c l]
      exact deformed_one_direction x c l t i v
    have hstructure : (F c).val =
        Matrix.blockDiagonal (fun l => (d c l).val) + portCol (j+2) k *
          (t • uniformCoefficient x c).map (algebraMap ℂ (Mat (j+2))) * portRow (j+2) k := by
      rw [hF c, deformed_port_pencil]
      simp only [hD]
    have h := coupled_inverse_corner hwidth (d c) hone _ (F c) hstructure r s
    dsimp only
    rw [portSum_eq_compressed]
    exact ⟨h (fun _ => false), h (fun _ => true)⟩

end
end MO35207

end

section

/-! Match the complex Kronecker-product compression with the matrix-valued endpoint calculation. -/

namespace MO35207
noncomputable section
open scoped Kronecker

variable {J B N : Type} [Fintype J] [Fintype B] [Fintype N]
  [DecidableEq J] [DecidableEq N]

private abbrev flat {H K : Type} (A : Matrix H K (Matrix N N ℂ)) := Matrix.comp H K N N ℂ A

private theorem flat_mul {H K E : Type} [Fintype K] (A : Matrix H K (Matrix N N ℂ))
    (B : Matrix K E (Matrix N N ℂ)) : flat A * flat B = flat (A*B) := by
  ext ⟨i,p⟩ ⟨j,q⟩
  simp [flat, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.sum_apply]

private theorem flat_sandwich [DecidableEq B]
    (W : Matrix J (J × B) (Matrix N N ℂ)) (G : Matrix (J × B) (J × B) ℂ)
    (V : Matrix (J × B) J (Matrix N N ℂ)) :
    let e := (Equiv.prodAssoc J B N).symm
    (flat W).submatrix id e * groupedAmplify N G * (flat V).submatrix e id =
      flat (W*(Algebra.ofId ℂ (Matrix N N ℂ)).mapMatrix G*V) := by
  let e := (Equiv.prodAssoc J B N).symm
  let F := (Algebra.ofId ℂ (Matrix N N ℂ)).mapMatrix G
  change (flat W).submatrix id e * (flat F).submatrix e e * (flat V).submatrix e id = _
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, flat_mul, flat_mul]

namespace MatrixModel

def endpoints (j : ℕ) (m : MatrixModel) (c : StageColors) :=
  endColumn (fun _ : Fin (j+2) => false) (fun _ : Fin (j+2) => true) (phaseCopies m.tuple c)

def rowScale (j : ℕ) : ℂ := (encodingMultiplicity StageColors (Fin (j+2)))⁻¹

private theorem flat_row (j : ℕ) (m : MatrixModel) :
    ((1 : Matrix J J ℂ) ⊗ₖ row j m) =
      (flat (rowScale j • uniformRow (J := J) (L := Fin (j+2)) (endpoints j m))).submatrix id
        (Equiv.prodAssoc J (Outer j) m.Index).symm := by
  ext ⟨i,p⟩ ⟨k,⟨c,l,s⟩,q⟩
  change (1 : Matrix J J ℂ) i k * (rowScale j * star (endpoints j m c s q p)) =
    rowScale j * ((if i=k then star (endpoints j m c s) else 0) p q)
  by_cases h : i=k <;> simp [Matrix.one_apply, h]

private theorem flat_col (j : ℕ) (m : MatrixModel) :
    ((1 : Matrix J J ℂ) ⊗ₖ column j m) =
      (flat (uniformColumn (J := J) (L := Fin (j+2)) (endpoints j m))).submatrix
        (Equiv.prodAssoc J (Outer j) m.Index).symm id := by
  ext ⟨k,⟨c,l,s⟩,p⟩ ⟨i,q⟩
  change (1 : Matrix J J ℂ) k i * endpoints j m c s p q =
    (if k=i then endpoints j m c s else 0) p q
  by_cases h : k=i <;> simp [Matrix.one_apply, h]

theorem explicit_compression (j : ℕ) (m : MatrixModel)
    (F : ColorBlocks J (Fin (j+2)) (Cube.Vertex (j+2))) (i k : J) (p q : m.Index) :
    (((1 : Matrix J J ℂ) ⊗ₖ row j m) * groupedAmplify m.Index (assembleColors F) *
      ((1 : Matrix J J ℂ) ⊗ₖ column j m)) (i,p) (k,q) =
      (rowScale j • (∑ c, ∑ s, star (endpoints j m c s) *
        ∑ t, portSum F c i k s t • endpoints j m c t)) p q := by
  rw [flat_row, flat_col, flat_sandwich, Matrix.smul_mul, Matrix.smul_mul]
  change (rowScale j • ((uniformRow (J := J) (L := Fin (j+2)) (endpoints j m) *
    (Algebra.ofId ℂ (Matrix m.Index m.Index ℂ)).mapMatrix (assembleColors F) *
    uniformColumn (J := J) (L := Fin (j+2)) (endpoints j m)) i k)) p q = _
  rw [color_compression]

end MatrixModel
end
end MO35207

end

section

/-! The compressed inverse in the determinant of the actual stage is the explicit affine inner test. -/

namespace MO35207.MatrixModel
noncomputable section
open scoped Kronecker
variable {J : Type} [Fintype J] [DecidableEq J]

def reduced (j : ℕ) (t : ℂ) (C : Matrix J J ℂ) (F : ColorBlocks J (Fin (j+2)) (Cube.Vertex (j+2))) :
    Pencil J :=
  innerTest (fun _ => false) (fun _ => true) (t*rowScale j) C (portSum F)

theorem evaluated_reduction (j : ℕ) (m : MatrixModel) (t : ℂ) (C : Matrix J J ℂ)
    (F : ColorBlocks J (Fin (j+2)) (Cube.Vertex (j+2))) :
    test m (reduced j t C F) = 1+(t • (C ⊗ₖ (1 : Matrix m.Index m.Index ℂ))) *
      ((1 : Matrix J J ℂ) ⊗ₖ row j m) * groupedAmplify m.Index (assembleColors F) *
      ((1 : Matrix J J ℂ) ⊗ₖ column j m) := by
  let e := Matrix.compAlgEquiv J m.Index ℂ ℂ
  let f := (Algebra.ofId ℂ (Matrix m.Index m.Index ℂ)).mapMatrix (m := J)
  let u := FreeAlgebra.lift ℂ (withAdjoints m.tuple)
  let Y := ((1 : Matrix J J ℂ) ⊗ₖ row j m) * groupedAmplify m.Index (assembleColors F) *
    ((1 : Matrix J J ℂ) ⊗ₖ column j m)
  let lo : Cube.Vertex (j+2) := fun _ => false
  let hi : Cube.Vertex (j+2) := fun _ => true
  have hy (i k : J) : (e.symm Y) i k =
      rowScale j • ∑ c, u (cornerForm lo hi c (portSum F c i k)) := by
    have hw (c : StageColors) : u (cornerForm lo hi c (portSum F c i k)) =
        ∑ s, star (endpoints j m c s) * ∑ v, portSum F c i k s v • endpoints j m c v :=
      evaluate_corner lo hi c (portSum F c i k) m.tuple (fun a => (m.isUnitary a).1)
    simp_rw [hw]
    exact Matrix.ext (fun p q => explicit_compression j m F i k p q)
  have hc : e (f C) = C ⊗ₖ (1 : Matrix m.Index m.Index ℂ) := amplify_eq_kronecker C
  have small : u.mapMatrix (reduced j t C F) = 1+(t • f C)*e.symm Y := by
    apply Matrix.ext
    intro i k
    change u (algebraMap ℂ _ ((1 : Matrix J J ℂ) i k) +
      ∑ v, ((t*rowScale j)*C i v) • ∑ c, cornerForm lo hi c (portSum F c v k)) =
      (1 : Matrix J J (Matrix m.Index m.Index ℂ)) i k +
        ∑ v, (t • (algebraMap ℂ (Matrix m.Index m.Index ℂ) (C i v))) * (e.symm Y) v k
    have h1 : algebraMap ℂ (Matrix m.Index m.Index ℂ) ((1 : Matrix J J ℂ) i k) =
        (1 : Matrix J J (Matrix m.Index m.Index ℂ)) i k := by
      by_cases h : i=k <;> simp [Matrix.one_apply,h]
    simp only [map_add, map_sum, map_smul, AlgHom.commutes, h1, hy]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    rw [Algebra.algebraMap_eq_smul_one, smul_smul, smul_mul_assoc, one_mul, smul_smul]
    rw [show (t*rowScale j)*C i v = (t*C i v)*rowScale j by ring]
  calc
    test m (reduced j t C F) = e (1+(t • f C)*e.symm Y) := congrArg e small
    _ = 1+(t • (C ⊗ₖ (1 : Matrix m.Index m.Index ℂ)))*Y := by
      rw [map_add,map_one,map_mul,map_smul,hc,AlgEquiv.apply_symm_apply]
    _ = _ := by simp only [Y, Matrix.mul_assoc]

theorem reduced_scalar_det (j : ℕ) (t : ℂ) (C : Matrix J J ℂ)
    (F : ColorBlocks J (Fin (j+2)) (Cube.Vertex (j+2)))
    (hzero : ∀ c i k, let R := portSum F c i k
      R (fun _ => false) (fun _ => true) = 0 ∧ R (fun _ => true) (fun _ => false) = 0) :
    ∃ z : ℂ, ∀ m : MatrixModel, (test m (reduced j t C F)).det = z ^ m.order := by
  obtain ⟨B,hB⟩ := innerTest_scalar (fun _ => false) (fun _ => true) (t*rowScale j) C (portSum F) hzero
  refine ⟨B.det, fun m => ?_⟩
  have he : test m (reduced j t C F) = amplify m.Index B := by
    apply Matrix.ext
    rintro ⟨i,p⟩ ⟨k,q⟩
    change (FreeAlgebra.lift ℂ (withAdjoints m.tuple) (innerTest _ _ _ _ _ i k)) p q =
      algebraMap ℂ (Matrix m.Index m.Index ℂ) (B i k) p q
    rw [hB, AlgHom.commutes]
  rw [he, amplify_det]

end
end MO35207.MatrixModel

end

section

/-! The single-stage affine determinant reduction suffices for the published board declaration. -/

namespace MO35207
noncomputable section
open scoped Matrix.Norms.L2Operator

private theorem adjoint_polynomial {X : Type} (p : FreeAlgebra ℂ (X ⊕ X)) :
    ∃ q : FreeAlgebra ℂ (X ⊕ X), ∀ {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
      [StarModule ℂ A] (u : X → A), FreeAlgebra.lift ℂ (withAdjoints u) q =
        star (FreeAlgebra.lift ℂ (withAdjoints u) p) := by
  induction p using FreeAlgebra.induction with
  | grade0 c =>
    refine ⟨algebraMap ℂ _ (star c), ?_⟩
    intro A _ _ _ _ u
    simp only [AlgHom.commutes, algebraMap_star_comm]
  | grade1 x =>
    cases x with
    | inl x =>
      refine ⟨FreeAlgebra.ι ℂ (Sum.inr x), ?_⟩
      intro A _ _ _ _ u
      simp [withAdjoints]
    | inr x =>
      refine ⟨FreeAlgebra.ι ℂ (Sum.inl x), ?_⟩
      intro A _ _ _ _ u
      simp [withAdjoints]
  | mul p r ih ir =>
    obtain ⟨q,hq⟩ := ih
    obtain ⟨s,hs⟩ := ir
    refine ⟨s*q, ?_⟩
    intro A _ _ _ _ u
    rw [map_mul, map_mul, star_mul, hs u, hq u]
  | add p r ih ir =>
    obtain ⟨q,hq⟩ := ih
    obtain ⟨s,hs⟩ := ir
    refine ⟨q+s, ?_⟩
    intro A _ _ _ _ u
    rw [map_add, map_add, star_add, hq u, hs u]

namespace MatrixModel

/-- This hypothesis is entirely about a single finite cube wrapped around an inner model.
Polynomial linearization, iteration through any number of cubes, and passage to the
infinite-dimensional C*-algebra are all included in the conclusion below. -/
theorem disproof_of_stage_factorization
    (hstep : ∀ (J : Type) [Fintype J] [DecidableEq J], stageFactorization J) :
    ¬ (type_of% @OMA.S_mo_35207.main) := by
  apply disproof_of_unitary_coordinates (M := fun j => Matrix (truncation j 0).Index (truncation j 0).Index ℂ)
    (fun j => (truncation j 0).tuple) (fun j => (truncation j 0).isUnitary) unbounded_star_range
  intro p
  classical
  obtain ⟨q,hq⟩ := adjoint_polynomial p
  obtain ⟨s,hs⟩ := WordSystem.represents ((2:ℂ)⁻¹ • (p+q))
  let u (d : ℕ) := withAdjoints (truncation d 0).tuple
  let A (d : ℕ) := s.value (u d)
  have he (d : ℕ) : hermitianPart (FreeAlgebra.lift ℂ (u d) p) = A d := by
    rw [show A d = FreeAlgebra.lift ℂ (u d) ((2:ℂ)⁻¹ • (p+q)) from (hs (u d)).symm,
      map_smul, map_add, show FreeAlgebra.lift ℂ (u d) q =
        star (FreeAlgebra.lift ℂ (u d) p) from hq _]
    rfl
  obtain ⟨K,hK⟩ := stable_tests (hstep s.State)
  have stable (d : ℕ) (hd : K ≤ d) (z : ℂ) : z ∈ spectrum ℂ (A d) ↔ z ∈ spectrum ℂ (A K) := by
    change z ∈ spectrum ℂ (s.value (u d)) ↔ z ∈ spectrum ℂ (s.value (u K))
    rw [s.spectrum_iff_singular, s.spectrum_iff_singular]
    exact not_congr (test_unit_iff (hK d hd) _ (s.pencil_affine z))
  refine ⟨(Finset.range (K+1)).biUnion (fun j => (A j).charpoly.roots.toFinset), ?_⟩
  intro d z hz
  rw [he] at hz
  have root (d : ℕ) (h : z ∈ spectrum ℂ (A d)) : z ∈ (A d).charpoly.roots.toFinset :=
    Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (A d).charpoly_monic.ne_zero).mpr
      ((A d).mem_spectrum_iff_isRoot_charpoly.mp h))
  apply Finset.mem_biUnion.mpr
  by_cases hd : d < K
  · exact ⟨d, Finset.mem_range.mpr (by omega), root d hz⟩
  · exact ⟨K, Finset.mem_range.mpr (by omega), root K ((stable d (by omega) z).mp hz)⟩

end MatrixModel
end
end MO35207

end

section

/-! A four-unitary counterexample for the accepted statement of MathOverflow 35207.
The construction is inspired by Yang, Hou and Fang, arXiv:2611.20690, Section 4.
The local construction uses two phases to recover each inner unitary. -/

namespace MO35207.MatrixModel
noncomputable section

theorem finite_stage_factorization (k : ℕ) : stageFactorization (Fin k) := by
  intro j P hP
  obtain ⟨C,hC⟩ := concrete_determinant_factor P hP
  apply (regular_background j P hP).mono
  rintro t ⟨D,F,hD,hInv,hcut⟩
  let G := fun c => (F c).inv
  refine ⟨D.val.det, reduced j t C G, innerTest_affine _ _ _ _ _, ?_, ?_⟩
  · intro m
    have he := hC j t D hD m
    rw [hInv] at he
    exact he.trans (congrArg (fun M : Matrix (Fin k × m.Index) (Fin k × m.Index) ℂ =>
      D.val.det ^ m.order * M.det) (evaluated_reduction j m t C G).symm)
  · exact fun hw => reduced_scalar_det j t C G (hcut (by simpa only [Fintype.card_fin] using hw))

variable {J K : Type} [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]

private theorem test_reindex (m : MatrixModel) (e : J ≃ K) (P : Pencil J) :
    test m (Matrix.reindex e e P) = Matrix.reindex (e.prodCongr (Equiv.refl m.Index))
      (e.prodCongr (Equiv.refl m.Index)) (test m P) := rfl

private theorem det_test_reindex (m : MatrixModel) (e : J ≃ K) (P : Pencil J) :
    (test m (Matrix.reindex e e P)).det = (test m P).det := by
  rw [test_reindex,Matrix.det_reindex_self]

private theorem deformed_reindex (m : MatrixModel) (e : J ≃ K) (P : Pencil J) (t : ℂ) :
    (1+t • (test m (Matrix.reindex e e P)-1)).det = (1+t • (test m P-1)).det := by
  let f := e.prodCongr (Equiv.refl m.Index)
  let h := Matrix.reindexAlgEquiv ℂ ℂ f
  have he : 1+t • (test m (Matrix.reindex e e P)-1) = h (1+t • (test m P-1)) := by
    rw [map_add,map_smul,map_sub,map_one]
    rfl
  rw [he]
  exact Matrix.det_reindex_self _ _

theorem transport_factorization (e : J ≃ K) (h : stageFactorization K) : stageFactorization J := by
  intro j P hP
  have ha : affine (Matrix.reindex e e P) := fun i s => hP (e.symm i) (e.symm s)
  apply (h j _ ha).mono
  rintro t ⟨c,Q,hQ,hfactor,hcut⟩
  refine ⟨c, Matrix.reindex e.symm e.symm Q, fun i s => hQ (e i) (e s), ?_, ?_⟩
  · intro m
    rw [det_test_reindex, ← deformed_reindex (step j m) e P t]
    exact hfactor m
  · intro hw
    obtain ⟨z,hz⟩ := hcut ((Fintype.card_congr e) ▸ hw)
    exact ⟨z, fun m => (det_test_reindex m e.symm Q).trans (hz m)⟩

end
end MO35207.MatrixModel

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_35207.main) := by
  apply MO35207.MatrixModel.disproof_of_stage_factorization
  intro J _ _
  exact MO35207.MatrixModel.transport_factorization (Fintype.equivFin J)
    (MO35207.MatrixModel.finite_stage_factorization (Fintype.card J))

end
