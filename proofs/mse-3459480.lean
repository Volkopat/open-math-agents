import OMAStatements.S_mse_3459480

open CategoryTheory

noncomputable def lts3459480_polyHomEquiv (R : Type) [CommRing R] :
    (Polynomial R →+* ZMod 2) ≃ (R →+* ZMod 2) × ZMod 2 where
  toFun f := (f.comp Polynomial.C, f Polynomial.X)
  invFun x := Polynomial.eval₂RingHom x.1 x.2
  left_inv f := by
    apply Polynomial.ringHom_ext'
    · exact Polynomial.eval₂RingHom_comp_C _ _
    · simp [Polynomial.coe_eval₂RingHom]
  right_inv x := by
    apply Prod.ext
    · exact Polynomial.eval₂RingHom_comp_C _ _
    · simp [Polynomial.coe_eval₂RingHom]

lemma lts3459480_polyHomCard (R : Type) [CommRing R] :
    Nat.card (Polynomial R →+* ZMod 2) = Nat.card (R →+* ZMod 2) * 2 := by
  rw [Nat.card_congr (lts3459480_polyHomEquiv R), Nat.card_prod, Nat.card_zmod]

lemma lts3459480_intHomCard : Nat.card (ℤ →+* ZMod 2) = 1 := by
  exact Nat.card_eq_one_iff_unique.mpr ⟨⟨RingHom.ext_int⟩, ⟨Int.castRingHom _⟩⟩

noncomputable def lts3459480_ringHomCongr {R S : Type} [CommRing R] [CommRing S]
    (e : R ≃+* S) : (R →+* ZMod 2) ≃ (S →+* ZMod 2) where
  toFun f := f.comp e.symm.toRingHom
  invFun f := f.comp e.toRingHom
  left_inv f := by
    apply RingHom.ext
    intro x
    simp
  right_inv f := by
    apply RingHom.ext
    intro x
    simp

theorem lts3459480_int_ne_poly :
    ¬ Nonempty (CommRingCat.of ℤ ≅ CommRingCat.of (Polynomial ℤ)) := by
  rintro ⟨e⟩
  have h := Nat.card_congr (lts3459480_ringHomCongr e.commRingCatIsoToRingEquiv)
  simp [lts3459480_polyHomCard, lts3459480_intHomCard] at h

theorem lts3459480_poly_ne_polyPoly :
    ¬ Nonempty (CommRingCat.of (Polynomial ℤ) ≅ CommRingCat.of (Polynomial (Polynomial ℤ))) := by
  rintro ⟨e⟩
  have h := Nat.card_congr (lts3459480_ringHomCongr e.commRingCatIsoToRingEquiv)
  simp [lts3459480_polyHomCard, lts3459480_intHomCard] at h

open CategoryTheory

theorem lts3459480_retract (S : CommRingCat.{0})
    (i : S ⟶ CommRingCat.of (Polynomial ℤ))
    (r : CommRingCat.of (Polynomial ℤ) ⟶ S) (hr : i ≫ r = 𝟙 S) :
    Nonempty (S ≅ CommRingCat.of ℤ) ∨ Nonempty (S ≅ CommRingCat.of (Polynomial ℤ)) := by
  let e : Polynomial ℤ →+* Polynomial ℤ := (r ≫ i).hom
  let p : Polynomial ℤ := e Polynomial.X
  have hri (s : S) : r (i s) = s := by
    simpa only [CommRingCat.comp_apply, CommRingCat.id_apply] using
      congrArg (fun f : S ⟶ S => f s) hr
  have hfix (s : S) : e (i s) = i s := by
    change i (r (i s)) = i s
    rw [hri]
  have hC (z : ℤ) : e (Polynomial.C z) = Polynomial.C z :=
    DFunLike.congr_fun ((e.comp Polynomial.C).ext_int Polynomial.C) z
  have hcomp (f : Polynomial ℤ) : e f = f.comp p := by
    have he : e = Polynomial.compRingHom p := by
      apply Polynomial.ringHom_ext
      · intro z
        change e (Polynomial.C z) = (Polynomial.C z).comp p
        rw [Polynomial.C_comp, hC]
      · change p = Polynomial.X.comp p
        rw [Polynomial.X_comp]
    exact DFunLike.congr_fun he f
  by_cases hp : p.natDegree = 0
  · have hc (f : Polynomial ℤ) : e f = Polynomial.C (f.eval (p.coeff 0)) := by
      calc
        e f = f.comp p := hcomp f
        _ = f.comp (Polynomial.C (p.coeff 0)) :=
          congrArg f.comp (Polynomial.eq_C_of_natDegree_eq_zero hp)
        _ = _ := Polynomial.comp_C
    left
    refine ⟨{
      hom := i ≫ CommRingCat.ofHom (Polynomial.evalRingHom (p.coeff 0))
      inv := CommRingCat.ofHom Polynomial.C ≫ r
      hom_inv_id := ?_
      inv_hom_id := ?_ }⟩
    · apply CommRingCat.hom_ext
      ext s
      change r (Polynomial.C ((i s).eval (p.coeff 0))) = s
      rw [← hc, hfix, hri]
    · apply CommRingCat.hom_ext
      ext z
      change (e (Polynomial.C z)).eval (p.coeff 0) = z
      rw [hcomp, Polynomial.C_comp, Polynomial.eval_C]
  · have hzero (f : Polynomial ℤ) (hf : e f = 0) : f = 0 := by
      have hd := congrArg Polynomial.natDegree hf
      rw [hcomp, Polynomial.natDegree_comp, Polynomial.natDegree_zero] at hd
      have hf0 := (mul_eq_zero.mp hd).resolve_right hp
      rw [Polynomial.eq_C_of_natDegree_eq_zero hf0, hC] at hf
      rwa [Polynomial.eq_C_of_natDegree_eq_zero hf0]
    have hinj : Function.Injective e := by
      intro f g hfg
      apply sub_eq_zero.mp (hzero (f - g) ?_)
      rw [map_sub, hfg, sub_self]
    have heid (f : Polynomial ℤ) : e f = f := hinj (hfix (r f))
    right
    exact ⟨{
      hom := i
      inv := r
      hom_inv_id := hr
      inv_hom_id := CommRingCat.hom_ext (RingHom.ext heid) }⟩

theorem lts3459480_disproof
    (hInt : ¬ Nonempty (CommRingCat.of ℤ ≅ CommRingCat.of (Polynomial ℤ)))
    (hPoly : ¬ Nonempty (CommRingCat.of (Polynomial ℤ) ≅
      CommRingCat.of (Polynomial (Polynomial ℤ)))) :
    ¬ ∃ F : CommRingCat.{0} ⥤ CommRingCat.{0},
      ∀ R : CommRingCat.{0}, Nonempty (F.obj (F.obj R) ≅ CommRingCat.of (Polynomial R)) := by
  rintro ⟨F, hF⟩
  let Z := CommRingCat.of ℤ
  let P := CommRingCat.of (Polynomial ℤ)
  let S := F.obj Z
  obtain ⟨α⟩ : Nonempty (F.obj S ≅ P) := hF Z
  let i : Z ⟶ S := CommRingCat.zIsInitial.to S
  let j : S ⟶ P := F.map i ≫ α.hom
  let q : S ⟶ Z := j ≫ CommRingCat.ofHom (Polynomial.evalRingHom (0 : ℤ))
  let r : P ⟶ S := α.inv ≫ F.map q
  have hiq : i ≫ q = 𝟙 Z := CommRingCat.zIsInitial.hom_ext _ _
  have hjr : j ≫ r = 𝟙 S := by
    dsimp [j, r]
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← F.map_comp, hiq, F.map_id]
  rcases lts3459480_retract S j r hjr with h | h
  · obtain ⟨σ⟩ := h
    exact hInt ⟨σ.symm ≪≫ (F.mapIso σ).symm ≪≫ α⟩
  · obtain ⟨σ⟩ := h
    let fp : F.obj P ≅ P := (F.mapIso σ).symm ≪≫ α
    obtain ⟨β⟩ := hF P
    exact hPoly ⟨fp.symm ≪≫ (F.mapIso fp).symm ≪≫ β⟩
theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_3459480.main) := by
  exact lts3459480_disproof lts3459480_int_ne_poly lts3459480_poly_ne_polyPoly
