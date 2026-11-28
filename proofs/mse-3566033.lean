import OMAStatements.S_mse_3566033

open Polynomial OMA.S_mse_3566033

noncomputable section

private def ev : ℤ[X] →+* ℤ × ℤ := (evalRingHom 0).prod (evalRingHom 2)
private abbrev S := ev.range
private def π : ℤ[X] →+* S := ev.rangeRestrict
private def M : Submonoid ℤ[X] := (IsUnit.submonoid S).comap π
private abbrev R := Localization M

private theorem denominators (d : M) : IsUnit (π d) := d.2

private noncomputable def φ : R →+* S := IsLocalization.lift denominators

private theorem integer_idempotent (a : ℤ) (h : a * a = a) : a = 0 ∨ a = 1 := by
  have hz : a * (a - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hz with ha | ha
  · exact Or.inl ha
  · exact Or.inr (by omega)

private theorem quotient_idempotent (e : S) (he : e * e = e) : e = 0 ∨ e = 1 := by
  have hleft := congrArg (fun a : S => a.1.1) he
  have hright := congrArg (fun a : S => a.1.2) he
  have hpar : (e.1.1 : ZMod 2) = (e.1.2 : ZMod 2) := by
    obtain ⟨p, hp⟩ := e.2
    rw [← hp]
    change Int.castRingHom (ZMod 2) (p.eval 0) = Int.castRingHom (ZMod 2) (p.eval 2)
    rw [← eval₂_at_apply (Int.castRingHom (ZMod 2)) 0,
      ← eval₂_at_apply (Int.castRingHom (ZMod 2)) 2]
    congr 1
  rcases integer_idempotent e.1.1 hleft with h0 | h1 <;>
    rcases integer_idempotent e.1.2 hright with h0' | h1'
  · exact Or.inl (Subtype.ext (Prod.ext h0 h0'))
  · norm_num [h0, h1'] at hpar
  · norm_num [h1, h0'] at hpar
  · exact Or.inr (Subtype.ext (Prod.ext h1 h1'))

private theorem reflect_units (z : R) (hz : IsUnit (φ z)) : IsUnit z := by
  obtain ⟨a, b, rfl⟩ := IsLocalization.exists_mk'_eq M z
  have hmap := (IsLocalization.lift_mk'_spec denominators a
    (φ (IsLocalization.mk' R a b)) b).mp rfl
  have ha : a ∈ M := by
    change IsUnit (π a)
    rw [hmap]
    exact (denominators b).mul hz
  apply isUnit_of_dvd_unit _ (IsLocalization.map_units R (⟨a, ha⟩ : M))
  exact ⟨algebraMap ℤ[X] R b, (IsLocalization.mk'_spec R a b).symm⟩

theorem OMA.solution : type_of% @OMA.S_mse_3566033.main := by
  have hM : M ≤ nonZeroDivisors ℤ[X] := by
    intro a ha
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro ha0
    change IsUnit (π a) at ha
    simp [ha0] at ha
  let _ : IsDomain R := IsLocalization.isDomain_localization hM
  refine ⟨R, S, inferInstance, inferInstance, φ, ?_, ?_, ?_⟩
  · intro X _
    by_cases hz : ∀ x ∈ X, x = 0
    · refine ⟨1, by simp, Set.ext fun a => ?_⟩
      change (∀ y ∈ X, y * a = 0) ↔ ∃ r : R, a = 1 * r
      exact ⟨fun _ => ⟨a, by simp⟩, fun _ y hy => by rw [hz y hy, zero_mul]⟩
    · push Not at hz
      obtain ⟨x, hx, hne⟩ := hz
      refine ⟨0, by simp, Set.ext fun a => ?_⟩
      change (∀ y ∈ X, y * a = 0) ↔ ∃ r : R, a = 0 * r
      simp only [zero_mul, exists_const]
      exact ⟨fun h => (mul_eq_zero.mp (h x hx)).resolve_left hne, fun h => by simp [h]⟩
  · constructor
    · intro y
      obtain ⟨p, hp⟩ := y.2
      exact ⟨algebraMap ℤ[X] R p, (IsLocalization.lift_eq denominators p).trans (Subtype.ext hp)⟩
    · intro x
      constructor
      · intro hx r
        apply reflect_units
        simp [hx]
      · intro h
        have hunit := (h 3).map φ
        rw [map_sub, map_one, map_mul, map_ofNat] at hunit
        let fst : S →+* ℤ := (RingHom.fst ℤ ℤ).comp ev.range.subtype
        let snd : S →+* ℤ := (RingHom.snd ℤ ℤ).comp ev.range.subtype
        have hl := (hunit.map fst)
        have hr := (hunit.map snd)
        rw [map_sub, map_one, map_mul, map_ofNat, Int.isUnit_iff] at hl hr
        apply Subtype.ext
        exact Prod.ext (show fst (φ x) = 0 by omega) (show snd (φ x) = 0 by omega)
  · intro h
    let x := π X
    let y := π (X - C 2)
    have hx : x ≠ 0 := by
      intro hzero
      have hcoord := congrArg (fun a : S => a.1.2) hzero
      change (X : ℤ[X]).eval 2 = 0 at hcoord
      norm_num at hcoord
    have hy : y ≠ 0 := by
      intro hzero
      have hcoord := congrArg (fun a : S => a.1.1) hzero
      change (X - C 2 : ℤ[X]).eval 0 = 0 at hcoord
      norm_num at hcoord
    have hxy : x * y = 0 := by
      apply Subtype.ext
      apply Prod.ext
      · change (X : ℤ[X]).eval 0 * (X - C 2 : ℤ[X]).eval 0 = 0
        simp
      · change (X : ℤ[X]).eval 2 * (X - C 2 : ℤ[X]).eval 2 = 0
        simp
    obtain ⟨e, he, hAnn⟩ := h {x} ⟨x, rfl⟩
    rcases quotient_idempotent e he with rfl | rfl
    · have hyAnn : y ∈ {a : S | ∀ z ∈ ({x} : Set S), z * a = 0} := by simpa using hxy
      rw [hAnn] at hyAnn
      exact hy (by simpa using hyAnn)
    · have hOne : (1 : S) ∈ {a : S | ∀ z ∈ ({x} : Set S), z * a = 0} := by
        rw [hAnn]
        exact ⟨1, by simp⟩
      exact hx (by simpa using hOne)

end