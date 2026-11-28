import OMAStatements.S_wp_harborth_s_conjecture

-- Reduction wp-harborth-s-conjecture.R1 of Harborth's conjecture
-- Credit: @matejpekar

namespace OMA.R_wp_harborth_s_conjecture_R1

open OMA.S_wp_harborth_s_conjecture
open scoped BigOperators

/-- Fáry's theorem for the graph and drawing definitions in the statement. -/
def H1 : Prop :=
  ∀ (V : Type) [Finite V] (G : SimpleGraph V), IsPlanar G →
    ∃ pos : V → Plane, IsPlaneStraightLineDrawing G pos

/-- Rational edge lengths for graphs maximal by edge inclusion among those on the
same vertices admitting a plane straight-line drawing. -/
def H2 : Prop :=
  ∀ (V : Type) [Finite V] (G : SimpleGraph V),
    (∃ pos : V → Plane, IsPlaneStraightLineDrawing G pos) →
    (∀ H : SimpleGraph V, G ≤ H →
      (∃ pos : V → Plane, IsPlaneStraightLineDrawing H pos) → H = G) →
    ∃ pos : V → Plane, IsPlaneStraightLineDrawing G pos ∧
      ∀ u v, G.Adj u v → ∃ q : ℚ, dist (pos u) (pos v) = (q : ℝ)

lemma scale_drawing {V : Type} {G : SimpleGraph V} {pos : V → Plane}
    (hpos : IsPlaneStraightLineDrawing G pos) {c : ℝ} (hc : c ≠ 0) :
    IsPlaneStraightLineDrawing G (fun v => c • pos v) := by
  let f : Plane →ᵃ[ℝ] Plane := (c • (LinearMap.id : Plane →ₗ[ℝ] Plane)).toAffineMap
  have hf (x : Plane) : f x = c • x := rfl
  have hinj : Function.Injective f := by
    intro x y hxy
    have h := congrArg (fun z : Plane => c⁻¹ • z) hxy
    simpa only [hf, smul_smul, inv_mul_cancel₀ hc, one_smul] using h
  obtain ⟨hvertices, hinterior, hdisjoint⟩ := hpos
  refine ⟨hinj.comp hvertices, ?_, ?_⟩
  · intro u v huv w hw
    change f (pos w) ∈ openSegment ℝ (f (pos u)) (f (pos v)) at hw
    rw [← image_openSegment] at hw
    obtain ⟨x, hx, heq⟩ := hw
    exact hinterior u v huv w (hinj heq ▸ hx)
  · intro u v x y huv hxy hne
    change Disjoint (openSegment ℝ (f (pos u)) (f (pos v)))
      (openSegment ℝ (f (pos x)) (f (pos y)))
    rw [← image_openSegment, ← image_openSegment]
    exact Set.disjoint_image_of_injective hinj (hdisjoint u v x y huv hxy hne)

lemma rational_to_integral {V : Type} [Finite V] {G : SimpleGraph V} {pos : V → Plane}
    (hpos : IsPlaneStraightLineDrawing G pos)
    (hlength : ∀ u v, G.Adj u v → ∃ q : ℚ, dist (pos u) (pos v) = (q : ℝ)) :
    ∃ pos' : V → Plane, IsPlaneStraightLineDrawing G pos' ∧
      ∀ u v, G.Adj u v → ∃ n : ℕ, dist (pos' u) (pos' v) = (n : ℝ) := by
  classical
  let := Fintype.ofFinite V
  have hall (u v : V) : ∃ q : ℚ, G.Adj u v → dist (pos u) (pos v) = (q : ℝ) := by
    by_cases huv : G.Adj u v
    · obtain ⟨q, hq⟩ := hlength u v huv
      exact ⟨q, fun _ => hq⟩
    · exact ⟨0, fun h => (huv h).elim⟩
  choose q hq using hall
  let d : ℕ := ∏ e : V × V, (q e.1 e.2).den
  have hd : 0 < d := Finset.prod_pos fun e _ => Nat.pos_of_ne_zero (q e.1 e.2).den_nz
  have hd' : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  refine ⟨fun v => (d : ℝ) • pos v, scale_drawing hpos hd'.ne', ?_⟩
  intro u v huv
  obtain ⟨m, hm⟩ : (q u v).den ∣ d :=
    Finset.dvd_prod_of_mem (fun e : V × V => (q e.1 e.2).den) (Finset.mem_univ (u, v))
  let z : ℤ := (q u v).num * (m : ℤ)
  have hdq : (d : ℝ) * (q u v : ℝ) = (z : ℝ) := by
    have hden : ((q u v).den : ℝ) ≠ 0 := by exact_mod_cast (q u v).den_nz
    rw [Rat.cast_def, hm, Nat.cast_mul]
    change (↑(q u v).den * (m : ℝ)) * (↑(q u v).num / ↑(q u v).den) =
      (((q u v).num * (m : ℤ) : ℤ) : ℝ)
    push_cast
    field_simp
  have hdist : dist ((d : ℝ) • pos u) ((d : ℝ) • pos v) = (z : ℝ) := by
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hd', hq u v huv, hdq]
  have hz : 0 ≤ z := by
    exact_mod_cast (hdist ▸ dist_nonneg : (0 : ℝ) ≤ (z : ℝ))
  exact ⟨z.toNat, hdist.trans (by exact_mod_cast (Int.toNat_of_nonneg hz).symm)⟩

theorem main : H1 → H2 → type_of% @OMA.S_wp_harborth_s_conjecture.main := by
  intro hFary hRational V _ G hG
  obtain ⟨H, hGH, hH⟩ := Finite.exists_le_maximal
    (p := fun K : SimpleGraph V => ∃ pos : V → Plane, IsPlaneStraightLineDrawing K pos)
    (hFary V G hG)
  obtain ⟨pos, ⟨hpos, hvertices, hdisjoint⟩, hlength⟩ := hRational V H hH.1
    (fun K hHK hK => le_antisymm (hH.2 hK hHK) hHK)
  refine rational_to_integral (G := G) (pos := pos) ⟨hpos, ?_, ?_⟩ ?_
  · exact fun u v huv => hvertices u v (hGH huv)
  · exact fun u v x y huv hxy => hdisjoint u v x y (hGH huv) (hGH hxy)
  · exact fun u v huv => hlength u v (hGH huv)

end OMA.R_wp_harborth_s_conjecture_R1
