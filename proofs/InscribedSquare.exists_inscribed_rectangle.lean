import FormalConjectures.Wikipedia.InscribedSquare
import Mathlib

/-!
# Inscribed Rectangle Theorem for Jordan Curves

Every Jordan curve in the plane admits an inscribed rectangle (Vaughan's Möbius-band argument,
capping to RP², complexification of the tautological line bundle over compact subsets of R³,
and the planar Borsuk–Ulam obstruction).

Adapts and combines the following merged open-math-agents contributions:
- @steveDOTdigital: `R1`, `R1.H2.R1`, and `R1.H2.R1.H2.R1` reductions
- @ivillar: `R1.H1` (chord parametrization of the Möbius strip)
- @Salofe: `R1.H2.R1.H1` (parametrization of the capped Möbius strip by S² / ±1 via Veronese map)
- @Genbox: `R1.H2.R1.H2.R1.H2` (zeros of odd complex functions on S² via stereographic logarithm)

Completes the final step `R1.H2.R1.H2.R1.H1` via an elementary 3D cubical cochain construction
(uniform continuity on a compact subset of R³, finite ℤ³ grid cover, integer 1-cochain and
2-cocycle elimination via path-flows on complement components, telescoping primitive on ℤ³,
and trilinear phase interpolation).
-/



/-
Vaughan's chord argument for an inscribed rectangle of unspecified aspect ratio.
Unordered chords form a Möbius band. The sum of the endpoints records twice
the midpoint, and the chord length records a nonnegative height. An additional
identification gives the two diagonals. Reflecting an embedded band across its
boundary plane would embed the closed Klein bottle in three-space.
-/

namespace OMA.InscribedR1

open Topology
open scoped unitInterval

/-- Parameterize unordered chords by a square with its vertical sides glued in
opposite directions. The two horizontal sides parameterize coincident endpoints. -/
def H1 : Prop :=
  let seam (p q : I × I) := p = q ∨
    (p.1 = 0 ∧ q.1 = 1 ∧ q.2 = unitInterval.symm p.2) ∨
    (p.1 = 1 ∧ q.1 = 0 ∧ p.2 = unitInterval.symm q.2)
  ∃ u v : I × I → Circle, Continuous u ∧ Continuous v ∧
    (∀ t : I, u (0,t) = v (1,unitInterval.symm t) ∧ v (0,t) = u (1,unitInterval.symm t)) ∧
    (∀ p : I × I, u p = v p ↔ p.2 = 0 ∨ p.2 = 1) ∧
    ∀ p q : I × I, ((u p = u q ∧ v p = v q) ∨ (u p = v q ∧ v p = u q)) → seam p q

/-- An upper-half-space map of the Möbius strip whose boundary is in the
horizontal plane must identify two points other than the prescribed seam. -/
def H2 : Prop :=
  let seam (p q : I × I) := p = q ∨
    (p.1 = 0 ∧ q.1 = 1 ∧ q.2 = unitInterval.symm p.2) ∨
    (p.1 = 1 ∧ q.1 = 0 ∧ p.2 = unitInterval.symm q.2)
  ∀ (f : I × I → EuclideanSpace ℝ (Fin 2)) (h : I × I → ℝ),
    Continuous f → Continuous h →
    (∀ t : I, f (0,t) = f (1,unitInterval.symm t) ∧ h (0,t) = h (1,unitInterval.symm t)) →
    (∀ p : I × I, 0 ≤ h p) → (∀ p : I × I, h p = 0 ↔ p.2 = 0 ∨ p.2 = 1) →
    ∃ p q : I × I, f p = f q ∧ h p = h q ∧ ¬ seam p q

theorem main : H1 → H2 → ∀ (γ : Circle → EuclideanSpace ℝ (Fin 2)), Topology.IsEmbedding γ → ∃ t₁ t₂ t₃ t₄ r, InscribedSquare.IsRectangle (γ t₁) (γ t₂) (γ t₃) (γ t₄) r := by
  intro chord collision γ hγ
  obtain ⟨u,v,hu,hv,glue,diagonal,unique⟩ := chord
  let f (p : I × I) := γ (u p) + γ (v p)
  let h (p : I × I) := dist (γ (u p)) (γ (v p))
  have hu' := hγ.continuous.comp hu
  have hv' := hγ.continuous.comp hv
  have edge (t : I) : f (0,t) = f (1,unitInterval.symm t) ∧ h (0,t) = h (1,unitInterval.symm t) := by
    obtain ⟨h₁,h₂⟩ := glue t
    simp only [f,h,h₁,h₂]
    exact ⟨add_comm _ _, dist_comm _ _⟩
  have zeroHeight (p : I × I) : h p = 0 ↔ p.2 = 0 ∨ p.2 = 1 := by
    rw [← diagonal p]
    exact dist_eq_zero.trans hγ.injective.eq_iff
  obtain ⟨p,q,hm,hd,hne⟩ := collision f h (hu'.add hv') (hu'.dist hv') edge
    (fun _ => dist_nonneg) zeroHeight
  change γ (u p) + γ (v p) = γ (u q) + γ (v q) at hm
  have hab : γ (u p) ≠ γ (u q) := by
    intro e
    have e' : γ (v p) = γ (v q) := add_left_cancel (e ▸ hm)
    exact hne (unique p q (.inl ⟨hγ.injective e,hγ.injective e'⟩))
  have hbc : γ (u q) ≠ γ (v p) := by
    intro e
    have hpair : γ (u p) + γ (v p) = γ (v q) + γ (v p) := by
      calc
        _ = γ (u q) + γ (v q) := hm
        _ = _ := by rw [e,add_comm]
    have e' := add_right_cancel hpair
    exact hne (unique p q (.inr ⟨hγ.injective e',hγ.injective e.symm⟩))
  exact ⟨u p,u q,v p,v q,_,hm,hd,hab,hbc,rfl⟩

end OMA.InscribedR1


/-
Step H1 of the InscribedSquare reduction: the explicit maps
u(s,t) = exp(i pi (s+t)) and v(s,t) = exp(i pi (s-t)) on the unit square.
-/

namespace OMA.P1InscribedSquareH1

theorem key (x y : ℝ) :
    Circle.exp (Real.pi * x) = Circle.exp (Real.pi * y) ↔ ∃ m : ℤ, x = y + 2 * m := by
  rw [Circle.exp_eq_exp]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have h : Real.pi * (x - (y + 2 * m)) = 0 := by linear_combination hm
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h Real.pi_ne_zero
    · linarith
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [hm]; ring⟩

end OMA.P1InscribedSquareH1

open OMA.P1InscribedSquareH1 in
theorem OMA.P1InscribedSquareH1.sol : OMA.InscribedR1.H1 := by
  unfold OMA.InscribedR1.H1
  intro seam
  refine ⟨fun p => Circle.exp (Real.pi * ((p.1 : ℝ) + (p.2 : ℝ))),
    fun p => Circle.exp (Real.pi * ((p.1 : ℝ) - (p.2 : ℝ))), ?_, ?_, ?_, ?_, ?_⟩
  · exact Circle.exp.continuous.comp (by fun_prop)
  · exact Circle.exp.continuous.comp (by fun_prop)
  · intro t
    constructor
    · rw [key]
      exact ⟨0, by simp [unitInterval.coe_symm_eq]⟩
    · rw [key]
      exact ⟨-1, by simp [unitInterval.coe_symm_eq]; ring⟩
  · intro p
    rw [key]
    have t0 := p.2.2.1
    have t1 := p.2.2.2
    constructor
    · rintro ⟨m, hm⟩
      have a0 : (0 : ℝ) ≤ m := by linarith
      have a1 : (m : ℝ) ≤ 1 := by linarith
      have b0 : (0 : ℤ) ≤ m := by exact_mod_cast a0
      have b1 : m ≤ (1 : ℤ) := by exact_mod_cast a1
      have hc : m = 0 ∨ m = 1 := by omega
      rcases hc with rfl | rfl
      · left
        exact Subtype.ext (show (p.2 : ℝ) = 0 by push_cast at hm; linarith)
      · right
        exact Subtype.ext (show (p.2 : ℝ) = 1 by push_cast at hm; linarith)
    · rintro (h | h)
      · exact ⟨0, by simp [h]⟩
      · exact ⟨1, by simp [h]; ring⟩
  · intro p q hpq
    simp only [seam]
    have s0 := p.1.2.1
    have s1 := p.1.2.2
    have t0 := p.2.2.1
    have t1 := p.2.2.2
    have s0' := q.1.2.1
    have s1' := q.1.2.2
    have t0' := q.2.2.1
    have t1' := q.2.2.2
    rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [key] at h1 h2
      obtain ⟨m, hm⟩ := h1
      obtain ⟨n, hn⟩ := h2
      have a1 : ((m + n : ℤ) : ℝ) ≤ 1 := by push_cast; linarith
      have a2 : (-1 : ℝ) ≤ ((m + n : ℤ) : ℝ) := by push_cast; linarith
      have a3 : ((m - n : ℤ) : ℝ) ≤ 1 := by push_cast; linarith
      have a4 : (-1 : ℝ) ≤ ((m - n : ℤ) : ℝ) := by push_cast; linarith
      have b1 : m + n ≤ 1 := by exact_mod_cast a1
      have b2 : -1 ≤ m + n := by exact_mod_cast a2
      have b3 : m - n ≤ 1 := by exact_mod_cast a3
      have b4 : -1 ≤ m - n := by exact_mod_cast a4
      have hc : (m = 0 ∧ n = 0) ∨ (m = 1 ∧ n = 0) ∨ (m = -1 ∧ n = 0) ∨
          (m = 0 ∧ n = 1) ∨ (m = 0 ∧ n = -1) := by omega
      rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        push_cast at hm hn <;>
        first
        | exact Or.inl (Prod.ext (Subtype.ext (by linarith)) (Subtype.ext (by linarith)))
        | exact Or.inr (Or.inl ⟨Subtype.ext (show (p.1 : ℝ) = 0 by linarith),
            Subtype.ext (show (q.1 : ℝ) = 1 by linarith),
            Subtype.ext (show (q.2 : ℝ) = 1 - (p.2 : ℝ) by linarith)⟩)
        | exact Or.inr (Or.inr ⟨Subtype.ext (show (p.1 : ℝ) = 1 by linarith),
            Subtype.ext (show (q.1 : ℝ) = 0 by linarith),
            Subtype.ext (show (p.2 : ℝ) = 1 - (q.2 : ℝ) by linarith)⟩)
    · rw [key] at h1 h2
      obtain ⟨m, hm⟩ := h1
      obtain ⟨n, hn⟩ := h2
      have a1 : ((m + n : ℤ) : ℝ) ≤ 1 := by push_cast; linarith
      have a2 : (-1 : ℝ) ≤ ((m + n : ℤ) : ℝ) := by push_cast; linarith
      have a3 : ((m - n : ℤ) : ℝ) ≤ 2 := by push_cast; linarith
      have a4 : (0 : ℝ) ≤ ((m - n : ℤ) : ℝ) := by push_cast; linarith
      have b1 : m + n ≤ 1 := by exact_mod_cast a1
      have b2 : -1 ≤ m + n := by exact_mod_cast a2
      have b3 : m - n ≤ 2 := by exact_mod_cast a3
      have b4 : 0 ≤ m - n := by exact_mod_cast a4
      have hc : (m = 0 ∧ n = 0) ∨ (m = 1 ∧ n = -1) ∨ (m = 1 ∧ n = 0) ∨
          (m = 0 ∧ n = -1) := by omega
      rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        push_cast at hm hn <;>
        first
        | exact Or.inl (Prod.ext (Subtype.ext (by linarith)) (Subtype.ext (by linarith)))
        | exact Or.inr (Or.inl ⟨Subtype.ext (show (p.1 : ℝ) = 0 by linarith),
            Subtype.ext (show (q.1 : ℝ) = 1 by linarith),
            Subtype.ext (show (q.2 : ℝ) = 1 - (p.2 : ℝ) by linarith)⟩)
        | exact Or.inr (Or.inr ⟨Subtype.ext (show (p.1 : ℝ) = 1 by linarith),
            Subtype.ext (show (q.1 : ℝ) = 0 by linarith),
            Subtype.ext (show (p.2 : ℝ) = 1 - (q.2 : ℝ) by linarith)⟩)


/-
Cap a Möbius band in the nonnegative half-space by a cone in the negative
half-space. Scaling the boundary by its cone radius makes the cap injective
off its apex. The quotient then embeds in three-space if the original band
has no additional identifications. This is the capping argument in Vaughan's
inscribed-rectangle theorem.
-/

namespace OMA.InscribedR1H2R1
open scoped unitInterval

/-- The capped strip is parametrized by a sphere with antipodal points identified. -/
def H1 : Prop :=
  let B := {p : I × I // p.2 = 0 ∨ p.2 = 1}
  let seam (p q : I × I) := p = q ∨
    (p.1 = 0 ∧ q.1 = 1 ∧ q.2 = unitInterval.symm p.2) ∨
    (p.1 = 1 ∧ q.1 = 0 ∧ p.2 = unitInterval.symm q.2)
  let glue : ((I × I) ⊕ (B × I)) → ((I × I) ⊕ (B × I)) → Prop := fun x y =>
    match x,y with
    | .inl p, .inl q => seam p q
    | .inl p, .inr w => w.2 = 1 ∧ seam p w.1.val
    | .inr w, .inl p => w.2 = 1 ∧ seam p w.1.val
    | .inr v, .inr w => v.2 = w.2 ∧ (v.2 = 0 ∨ seam v.1.val w.1.val)
  ∃ π : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → Quot glue,
    Continuous π ∧ ∀ x y, π x = π y ↔ x = y ∨ x.val = -y.val

/-- Every continuous antipodally invariant map of the two-sphere to real three-space
identifies a pair outside the same antipodal orbit. -/
def H2 : Prop :=
  ∀ g : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 2) × ℝ,
    Continuous g → (∀ x y, x.val = -y.val → g x = g y) →
    ∃ x y, g x = g y ∧ x ≠ y ∧ x.val ≠ -y.val

theorem main : H1 → H2 → OMA.InscribedR1.H2 := by
  intro chart obstruction f h hf hh hseam hnonneg hzero
  let B := {p : I × I // p.2 = 0 ∨ p.2 = 1}
  let seam (p q : I × I) := p = q ∨
    (p.1 = 0 ∧ q.1 = 1 ∧ q.2 = unitInterval.symm p.2) ∨
    (p.1 = 1 ∧ q.1 = 0 ∧ p.2 = unitInterval.symm q.2)
  let glue : ((I × I) ⊕ (B × I)) → ((I × I) ⊕ (B × I)) → Prop := fun x y =>
    match x,y with
    | .inl p, .inl q => seam p q
    | .inl p, .inr w => w.2 = 1 ∧ seam p w.1.val
    | .inr w, .inl p => w.2 = 1 ∧ seam p w.1.val
    | .inr v, .inr w => v.2 = w.2 ∧ (v.2 = 0 ∨ seam v.1.val w.1.val)
  by_contra hn
  let band (p : I × I) := (f p, h p)
  let cap (v : B × I) := ((v.2 : ℝ) • f v.1.val, (v.2 : ℝ) - 1)
  have hband (p q : I × I) : band p = band q ↔ seam p q := by
    constructor
    · intro he
      by_contra hne
      exact hn ⟨p,q,congrArg Prod.fst he,congrArg Prod.snd he,hne⟩
    · rintro (e | ⟨hs,hs',ht⟩ | ⟨hs,hs',ht⟩)
      · rw [e]
      · obtain ⟨s,t⟩ := p
        obtain ⟨s',t'⟩ := q
        change s = 0 at hs
        change s' = 1 at hs'
        change t' = unitInterval.symm t at ht
        subst s; subst s'; subst t'
        exact Prod.ext (hseam t).1 (hseam t).2
      · obtain ⟨s,t⟩ := p
        obtain ⟨s',t'⟩ := q
        change s = 1 at hs
        change s' = 0 at hs'
        change t = unitInterval.symm t' at ht
        subst s; subst s'; subst t
        exact Prod.ext (hseam t').1.symm (hseam t').2.symm
  have hbzero (b : B) : h b.val = 0 := (hzero b.val).2 b.property
  have base (b : B) : cap (b,1) = band b.val := by
    simp [cap,band,hbzero]
  have hmix (p : I × I) (w : B × I) : band p = cap w ↔ w.2 = 1 ∧ seam p w.1.val := by
    obtain ⟨b,t⟩ := w
    change band p = cap (b,t) ↔ t = 1 ∧ seam p b.val
    constructor
    · intro he
      have hd := congrArg Prod.snd he
      change h p = (t : ℝ) - 1 at hd
      have ht : t = 1 := Subtype.ext (by
        change (t : ℝ) = 1
        linarith [hnonneg p,t.property.2])
      subst t
      exact ⟨rfl,(hband p b.val).mp (he.trans (base b))⟩
    · rintro ⟨rfl,hs⟩
      exact ((hband p b.val).mpr hs).trans (base b).symm
  have hcap (v w : B × I) : cap v = cap w ↔
      v.2 = w.2 ∧ (v.2 = 0 ∨ seam v.1.val w.1.val) := by
    obtain ⟨a,t⟩ := v
    obtain ⟨b,u⟩ := w
    change cap (a,t) = cap (b,u) ↔ t = u ∧ (t = 0 ∨ seam a.val b.val)
    constructor
    · intro he
      have hd := congrArg Prod.snd he
      change (t : ℝ)-1 = (u : ℝ)-1 at hd
      have ht : t = u := Subtype.ext (by linarith)
      subst u
      refine ⟨rfl, ?_⟩
      by_cases hz : t = 0
      · exact Or.inl hz
      · right
        have he' := congrArg Prod.fst he
        have hs : (t : ℝ) ≠ 0 := fun e => hz (Subtype.ext e)
        have hab : f a.val = f b.val := smul_right_injective _ hs he'
        exact (hband _ _).mp (Prod.ext hab ((hbzero a).trans (hbzero b).symm))
    · rintro ⟨rfl,hx⟩
      rcases hx with rfl | hx
      · simp [cap]
      · have he := congrArg Prod.fst ((hband _ _).mpr hx)
        change f a.val = f b.val at he
        simp [cap,he]
  let F : (I × I) ⊕ (B × I) → EuclideanSpace ℝ (Fin 2) × ℝ := Sum.elim band cap
  have hF : Continuous F := by
    apply continuous_sum_dom.mpr
    constructor
    · exact hf.prodMk hh
    · change Continuous (fun v : B × I => ((v.2 : ℝ) • f v.1.val, (v.2 : ℝ) - 1))
      have hb : Continuous (fun v : B × I => v.1.val) := continuous_subtype_val.comp continuous_fst
      have ht : Continuous (fun v : B × I => (v.2 : ℝ)) := continuous_subtype_val.comp continuous_snd
      exact (ht.smul (hf.comp hb)).prodMk (ht.sub continuous_const)
  have hglue (x y) : F x = F y ↔ glue x y := by
    cases x with
    | inl p =>
      cases y with
      | inl q => exact hband p q
      | inr w => exact hmix p w
    | inr v =>
      cases y with
      | inl q => exact eq_comm.trans (hmix q v)
      | inr w => exact hcap v w
  let G : Quot glue → EuclideanSpace ℝ (Fin 2) × ℝ :=
    Quot.lift F (fun x y hxy => (hglue x y).mpr hxy)
  have hc : Continuous G := continuous_quot_lift _ hF
  have hi : Function.Injective G := by
    rintro ⟨x⟩ ⟨y⟩ he
    exact Quot.sound ((hglue x y).mp he)
  obtain ⟨π,hπ,horbit⟩ := chart
  obtain ⟨x,y,he,hne,hnneg⟩ := obstruction (G ∘ π) (hc.comp hπ)
    (fun x y hxy => congrArg G ((horbit x y).mpr (Or.inr hxy)))
  exact ((horbit x y).mp (hi he)).elim hne hnneg

end OMA.InscribedR1H2R1


/-
# Step H1 of the reduction InscribedSquare.exists_inscribed_rectangle.R1.H2.R1

The capped strip (a Moebius band whose boundary circle is coned off) is the real projective
plane. We parametrize it from the sphere through the Veronese map `v ↦ v vᵀ`, which identifies
exactly antipodal points of the sphere.

* The band point `(s, t)` is sent to the spherical point with longitude `π s` and latitude
  `π (2 t - 1) / 4`; the cap point `((s, t), u)` (with `t ∈ {0, 1}`) to longitude `π s` and
  latitude `π (2 t - 1) (1 / 2 - u / 4)`. The seam of the band and the cone vertex go to
  antipodal points, so this map `Ψ` (followed by the Veronese map) descends to the quotient.
* Two parameters with the same image are glued (a direct case analysis with injectivity of
  `sin` on `[-π/2, π/2]` and of `cos` on `[0, π]`), and every point of the sphere is hit up to
  sign (spherical coordinates via `Complex.arg` and `Real.arcsin`).
* The quotient is compact and the image is Hausdorff, so the induced continuous bijection is a
  homeomorphism; the parametrization is its inverse composed with the Veronese map.

Only upstream definitions are used, together with Mathlib and the helper lemmas below.
-/

namespace OMA.InscribedHelpers
open scoped unitInterval
open Real Set

/-- Spherical coordinates with longitude `θ` and latitude `φ`. -/
noncomputable def sphP (θ φ : ℝ) : Fin 3 → ℝ := ![cos φ * cos θ, cos φ * sin θ, sin φ]

/-- The Veronese map `v ↦ v vᵀ`, which identifies exactly the pairs `v, -v` of nonzero vectors. -/
def ver (v : Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ := fun i j => v i * v j

theorem continuous_ver : Continuous ver := by
  unfold ver
  fun_prop

theorem ver_neg (v : Fin 3 → ℝ) : ver (-v) = ver v := by
  funext i j
  simp [ver]

theorem ver_eq {v w : Fin 3 → ℝ} (hv : v ≠ 0) (h : ver v = ver w) : v = w ∨ v = -w := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  simp only [Pi.zero_apply] at hi
  have hii := congrFun (congrFun h i) i
  simp only [ver] at hii
  have hf : (v i - w i) * (v i + w i) = 0 := by linear_combination hii
  rcases mul_eq_zero.mp hf with h1 | h1
  · left
    funext j
    have hij := congrFun (congrFun h i) j
    simp only [ver] at hij
    have e : w i = v i := by linarith
    rw [e] at hij
    exact mul_left_cancel₀ hi hij
  · right
    funext j
    have hij := congrFun (congrFun h i) j
    simp only [ver] at hij
    have e : w i = - v i := by linarith
    rw [e] at hij
    have h2 : v i * v j = v i * (-w j) := by rw [hij]; ring
    simpa using mul_left_cancel₀ hi h2

theorem sphP_sq (θ φ : ℝ) :
    sphP θ φ 0 ^ 2 + sphP θ φ 1 ^ 2 + sphP θ φ 2 ^ 2 = 1 := by
  simp only [sphP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  linear_combination (cos φ ^ 2) * (sin_sq_add_cos_sq θ) + sin_sq_add_cos_sq φ

theorem sphP_ne_zero (θ φ : ℝ) : sphP θ φ ≠ 0 := by
  intro h
  have e := sphP_sq θ φ
  rw [h] at e
  simp at e

theorem sphP_pi_neg (ψ : ℝ) : sphP π (-ψ) = - sphP 0 ψ := by
  funext i
  fin_cases i <;> simp [sphP]

theorem seam_ver (c : ℝ) (p q : I × I)
    (h : p = q ∨ (p.1 = 0 ∧ q.1 = 1 ∧ q.2 = σ p.2) ∨ (p.1 = 1 ∧ q.1 = 0 ∧ p.2 = σ q.2)) :
    ver (sphP (π * p.1) (π * ((2 * p.2 - 1) * c))) =
      ver (sphP (π * q.1) (π * ((2 * q.2 - 1) * c))) := by
  rcases h with rfl | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rfl
  · rw [h1, h2, h3, unitInterval.coe_symm_eq]
    have e : π * ((2 * (1 - (p.2 : ℝ)) - 1) * c) = -(π * ((2 * p.2 - 1) * c)) := by ring
    rw [e]
    simp only [Icc.coe_zero, Icc.coe_one, mul_zero, mul_one]
    rw [sphP_pi_neg, ver_neg]
  · rw [h1, h2, h3, unitInterval.coe_symm_eq]
    have e : π * ((2 * (1 - (q.2 : ℝ)) - 1) * c) = -(π * ((2 * q.2 - 1) * c)) := by ring
    rw [e]
    simp only [Icc.coe_zero, Icc.coe_one, mul_zero, mul_one]
    rw [sphP_pi_neg, ver_neg]

theorem pole_ver (θ : ℝ) (t : I) (ht : t = 0 ∨ t = 1) :
    ver (sphP θ (π * ((2 * t - 1) * (1 / 2)))) = ver ![0, 0, 1] := by
  rcases ht with rfl | rfl
  · have e : sphP θ (π * ((2 * ((0 : I) : ℝ) - 1) * (1 / 2))) = -![0, 0, 1] := by
      have e2 : π * ((2 * ((0 : I) : ℝ) - 1) * (1 / 2)) = -(π / 2) := by simp; ring
      rw [e2]
      funext i
      fin_cases i <;> simp [sphP]
    rw [e, ver_neg]
  · have e : sphP θ (π * ((2 * ((1 : I) : ℝ) - 1) * (1 / 2))) = ![0, 0, 1] := by
      have e2 : π * ((2 * ((1 : I) : ℝ) - 1) * (1 / 2)) = π / 2 := by simp; ring
      rw [e2]
      funext i
      fin_cases i <;> simp [sphP]
    rw [e]

theorem sph_cases {θ θ' φ φ' : ℝ} (hθ : θ ∈ Icc 0 π) (hθ' : θ' ∈ Icc 0 π)
    (hφ : φ ∈ Icc (-(π / 2)) (π / 2)) (hφ' : φ' ∈ Icc (-(π / 2)) (π / 2))
    (h : sphP θ φ = sphP θ' φ' ∨ sphP θ φ = -sphP θ' φ') :
    (φ = φ' ∧ (cos φ = 0 ∨ θ = θ')) ∨
      (φ = -φ' ∧ (cos φ = 0 ∨ (θ = 0 ∧ θ' = π) ∨ (θ = π ∧ θ' = 0))) := by
  rcases h with h | h
  · have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [sphP] at h0 h1 h2
    have e : φ = φ' := injOn_sin hφ hφ' h2
    subst e
    left
    refine ⟨rfl, ?_⟩
    by_cases hc : cos φ = 0
    · exact Or.inl hc
    · exact Or.inr (injOn_cos hθ hθ' (mul_left_cancel₀ hc h0))
  · have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [sphP] at h0 h1 h2
    have hφ'' : -φ' ∈ Icc (-(π / 2)) (π / 2) := ⟨by linarith [hφ'.2], by linarith [hφ'.1]⟩
    have e : φ = -φ' := injOn_sin hφ hφ'' (by rw [sin_neg]; exact h2)
    subst e
    right
    refine ⟨rfl, ?_⟩
    by_cases hc : cos (-φ') = 0
    · exact Or.inl hc
    · right
      rw [cos_neg] at hc
      have hcos : cos θ = - cos θ' := by
        apply mul_left_cancel₀ hc
        rw [cos_neg] at h0
        linarith
      have hsin : sin θ = - sin θ' := by
        apply mul_left_cancel₀ hc
        rw [cos_neg] at h1
        linarith
      have s1 := sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
      have s2 := sin_nonneg_of_nonneg_of_le_pi hθ'.1 hθ'.2
      have hs : sin θ = 0 := by linarith
      have hc2 : (cos θ - 1) * (cos θ + 1) = 0 := by
        linear_combination (sin_sq_add_cos_sq θ) - sin θ * hs
      have h0m : (0 : ℝ) ∈ Icc 0 π := ⟨le_rfl, pi_pos.le⟩
      have hpm : π ∈ Icc 0 π := ⟨pi_pos.le, le_rfl⟩
      rcases mul_eq_zero.mp hc2 with k | k
      · left
        constructor
        · exact injOn_cos hθ h0m (by rw [cos_zero]; linarith)
        · exact injOn_cos hθ' hpm (by rw [cos_pi]; linarith)
      · right
        constructor
        · exact injOn_cos hθ hpm (by rw [cos_pi]; linarith)
        · exact injOn_cos hθ' h0m (by rw [cos_zero]; linarith)

theorem theta_mem (s : I) : π * (s : ℝ) ∈ Icc 0 π :=
  ⟨mul_nonneg pi_pos.le s.2.1, by nlinarith [s.2.2, pi_pos]⟩

theorem lat_mem {x : ℝ} (h1 : -(1 / 2) ≤ x) (h2 : x ≤ 1 / 2) : π * x ∈ Icc (-(π / 2)) (π / 2) :=
  ⟨by nlinarith [pi_pos], by nlinarith [pi_pos]⟩

theorem cos_ne_zero_of {x : ℝ} (h1 : -(1 / 2) < x) (h2 : x < 1 / 2) : cos (π * x) ≠ 0 :=
  (cos_pos_of_mem_Ioo ⟨by nlinarith [pi_pos], by nlinarith [pi_pos]⟩).ne'

theorem pi_mul_inj {a b : ℝ} (h : π * a = π * b) : a = b := mul_left_cancel₀ pi_ne_zero h

theorem lat_bound (t u : I) : -(1 / 2) ≤ (2 * (t : ℝ) - 1) * (1 / 2 - u / 4) ∧
    (2 * (t : ℝ) - 1) * (1 / 2 - u / 4) ≤ 1 / 2 := by
  have := t.2.1; have := t.2.2; have := u.2.1; have := u.2.2
  constructor <;> nlinarith

theorem coe_I_eq {a b : I} (h : (a : ℝ) = b) : a = b := Subtype.ext h

theorem zero_of_pi {s : I} (h : π * (s : ℝ) = 0) : s = 0 :=
  Subtype.ext (pi_mul_inj (by rw [h]; simp))

theorem one_of_pi {s : I} (h : π * (s : ℝ) = π) : s = 1 :=
  Subtype.ext (pi_mul_inj (by rw [h]; simp))

/-- The common parametrization of the band (left) and the cap (right). -/
abbrev Bd := {p : I × I // p.2 = 0 ∨ p.2 = 1}

noncomputable def psiL (p : I × I) : Fin 3 → ℝ :=
  sphP (π * p.1) (π * ((2 * (p.2 : ℝ) - 1) * (1 / 4)))

noncomputable def psiR (w : Bd × I) : Fin 3 → ℝ :=
  sphP (π * w.1.val.1) (π * ((2 * (w.1.val.2 : ℝ) - 1) * (1 / 2 - (w.2 : ℝ) / 4)))

noncomputable def psi0 : (I × I) ⊕ (Bd × I) → Fin 3 → ℝ := Sum.elim psiL psiR

theorem continuous_sphP : Continuous (fun x : ℝ × ℝ => sphP x.1 x.2) := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [sphP] <;> fun_prop

theorem continuous_sphP' {X : Type} [TopologicalSpace X] {f g : X → ℝ} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => sphP (f x) (g x) :=
  continuous_sphP.comp (hf.prodMk hg)

theorem continuous_psiL : Continuous psiL := by
  have c1 : Continuous fun p : I × I => (p.1 : ℝ) := continuous_subtype_val.comp continuous_fst
  have c2 : Continuous fun p : I × I => (p.2 : ℝ) := continuous_subtype_val.comp continuous_snd
  unfold psiL
  exact continuous_sphP' (continuous_const.mul c1)
    (continuous_const.mul (((continuous_const.mul c2).sub continuous_const).mul continuous_const))

theorem continuous_psiR : Continuous psiR := by
  have c0 : Continuous fun w : Bd × I => w.1.val :=
    continuous_subtype_val.comp continuous_fst
  have c1 : Continuous fun w : Bd × I => (w.1.val.1 : ℝ) :=
    continuous_subtype_val.comp (continuous_fst.comp c0)
  have c2 : Continuous fun w : Bd × I => (w.1.val.2 : ℝ) :=
    continuous_subtype_val.comp (continuous_snd.comp c0)
  have c3 : Continuous fun w : Bd × I => (w.2 : ℝ) := continuous_subtype_val.comp continuous_snd
  unfold psiR
  exact continuous_sphP' (continuous_const.mul c1)
    (continuous_const.mul (((continuous_const.mul c2).sub continuous_const).mul
      (continuous_const.sub (c3.div_const 4))))

theorem continuous_psi0 : Continuous psi0 := continuous_psiL.sumElim continuous_psiR

theorem inj_ll (p q : I × I) (h : ver (psi0 (Sum.inl p)) = ver (psi0 (Sum.inl q))) :
    p = q ∨ (p.1 = 0 ∧ q.1 = 1 ∧ q.2 = σ p.2) ∨ (p.1 = 1 ∧ q.1 = 0 ∧ p.2 = σ q.2) := by
  have hp := p.2.2; have hq := q.2.2
  have hc : cos (π * ((2 * (p.2 : ℝ) - 1) * (1 / 4))) ≠ 0 :=
    cos_ne_zero_of (by linarith [hp.1, hp.2]) (by linarith [hp.1, hp.2])
  rcases sph_cases (theta_mem p.1) (theta_mem q.1)
    (lat_mem (by linarith [hp.1, hp.2]) (by linarith [hp.1, hp.2]))
    (lat_mem (by linarith [hq.1, hq.2]) (by linarith [hq.1, hq.2]))
    (ver_eq (sphP_ne_zero _ _) h) with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rcases e2 with e2 | e2
    · exact absurd e2 hc
    left
    have a1 := pi_mul_inj e2
    have a2 := pi_mul_inj e1
    exact Prod.ext (Subtype.ext a1) (Subtype.ext (by linarith))
  · have a2 : π * ((2 * (p.2 : ℝ) - 1) * (1 / 4)) = π * (-((2 * (q.2 : ℝ) - 1) * (1 / 4))) := by
      rw [e1]; ring
    have a2 := pi_mul_inj a2
    rcases e2 with e2 | ⟨e3, e4⟩ | ⟨e3, e4⟩
    · exact absurd e2 hc
    · right; left
      refine ⟨zero_of_pi e3, one_of_pi e4, Subtype.ext ?_⟩
      rw [unitInterval.coe_symm_eq]; linarith
    · right; right
      refine ⟨one_of_pi e3, zero_of_pi e4, Subtype.ext ?_⟩
      rw [unitInterval.coe_symm_eq]; linarith

theorem u_one (p : I × I) (w : Bd × I) (h : ver (psi0 (Sum.inl p)) = ver (psi0 (Sum.inr w))) :
    w.2 = 1 := by
  obtain ⟨hp0, hp1⟩ := p.2.2
  obtain ⟨hu0, hu1⟩ := w.2.2
  have hb := lat_bound w.1.val.2 w.2
  have key : (w.2 : ℝ) = 1 := by
    rcases sph_cases (theta_mem p.1) (theta_mem w.1.val.1)
      (lat_mem (by linarith) (by linarith)) (lat_mem hb.1 hb.2)
      (ver_eq (sphP_ne_zero _ _) h) with ⟨e1, -⟩ | ⟨e1, -⟩
    · have a := pi_mul_inj e1
      rcases w.1.2 with ht | ht <;> rw [ht] at a <;> simp at a <;> linarith
    · have a : π * ((2 * (p.2 : ℝ) - 1) * (1 / 4)) =
          π * (-((2 * (w.1.val.2 : ℝ) - 1) * (1 / 2 - w.2 / 4))) := by rw [e1]; ring
      have a := pi_mul_inj a
      rcases w.1.2 with ht | ht <;> rw [ht] at a <;> simp at a <;> linarith
  exact coe_I_eq (key.trans Icc.coe_one.symm)

theorem inj_rr (v w : Bd × I) (h : ver (psi0 (Sum.inr v)) = ver (psi0 (Sum.inr w))) :
    v = w ∨ (v.2 = w.2 ∧ (v.2 = 0 ∨ (v.1.val = w.1.val ∨
      (v.1.val.1 = 0 ∧ w.1.val.1 = 1 ∧ w.1.val.2 = σ v.1.val.2) ∨
      (v.1.val.1 = 1 ∧ w.1.val.1 = 0 ∧ v.1.val.2 = σ w.1.val.2)))) := by
  obtain ⟨hu0, hu1⟩ := v.2.2
  obtain ⟨hu0', hu1'⟩ := w.2.2
  have hb := lat_bound v.1.val.2 v.2
  have hb' := lat_bound w.1.val.2 w.2
  rcases sph_cases (theta_mem v.1.val.1) (theta_mem w.1.val.1)
    (lat_mem hb.1 hb.2) (lat_mem hb'.1 hb'.2)
    (ver_eq (sphP_ne_zero _ _) h) with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have a := pi_mul_inj e1
    have huu : (v.2 : ℝ) = w.2 := by
      rcases v.1.2 with ht | ht <;> rcases w.1.2 with ht' | ht' <;> rw [ht, ht'] at a <;>
        simp only [Icc.coe_zero, Icc.coe_one] at a <;> linarith
    have hvw2 : v.2 = w.2 := Subtype.ext huu
    by_cases hz : (v.2 : ℝ) = 0
    · right
      exact ⟨hvw2, Or.inl (Subtype.ext hz)⟩
    · have hpos : 0 < (v.2 : ℝ) := lt_of_le_of_ne hu0 (Ne.symm hz)
      have htt : (v.1.val.2 : ℝ) = w.1.val.2 := by
        rcases v.1.2 with ht | ht <;> rcases w.1.2 with ht' | ht' <;> rw [ht, ht'] at a <;>
          rw [ht, ht'] <;> simp only [Icc.coe_zero, Icc.coe_one] at a ⊢ <;> linarith
      have hc : cos (π * ((2 * (v.1.val.2 : ℝ) - 1) * (1 / 2 - v.2 / 4))) ≠ 0 := by
        rcases v.1.2 with ht | ht <;> rw [ht] <;> simp <;>
          exact cos_ne_zero_of (by linarith) (by linarith)
      rcases e2 with e2 | e2
      · exact absurd e2 hc
      left
      have a1 := pi_mul_inj e2
      exact Prod.ext (Subtype.ext (Prod.ext (Subtype.ext a1) (Subtype.ext htt))) hvw2
  · have a : π * ((2 * (v.1.val.2 : ℝ) - 1) * (1 / 2 - v.2 / 4)) =
        π * (-((2 * (w.1.val.2 : ℝ) - 1) * (1 / 2 - w.2 / 4))) := by rw [e1]; ring
    have a := pi_mul_inj a
    have huu : (v.2 : ℝ) = w.2 := by
      rcases v.1.2 with ht | ht <;> rcases w.1.2 with ht' | ht' <;> rw [ht, ht'] at a <;>
        simp only [Icc.coe_zero, Icc.coe_one] at a <;> linarith
    have hvw2 : v.2 = w.2 := Subtype.ext huu
    right
    refine ⟨hvw2, ?_⟩
    by_cases hz : (v.2 : ℝ) = 0
    · exact Or.inl (Subtype.ext hz)
    · right
      right
      have hpos : 0 < (v.2 : ℝ) := lt_of_le_of_ne hu0 (Ne.symm hz)
      have htt : (w.1.val.2 : ℝ) = 1 - v.1.val.2 := by
        rcases v.1.2 with ht | ht <;> rcases w.1.2 with ht' | ht' <;> rw [ht, ht'] at a <;>
          rw [ht, ht'] <;> simp only [Icc.coe_zero, Icc.coe_one] at a ⊢ <;> linarith
      have hc : cos (π * ((2 * (v.1.val.2 : ℝ) - 1) * (1 / 2 - v.2 / 4))) ≠ 0 := by
        rcases v.1.2 with ht | ht <;> rw [ht] <;> simp <;>
          exact cos_ne_zero_of (by linarith) (by linarith)
      rcases e2 with e2 | ⟨e3, e4⟩ | ⟨e3, e4⟩
      · exact absurd e2 hc
      · left
        refine ⟨zero_of_pi e3, one_of_pi e4, Subtype.ext ?_⟩
        rw [unitInterval.coe_symm_eq]; linarith
      · right
        refine ⟨one_of_pi e3, zero_of_pi e4, Subtype.ext ?_⟩
        rw [unitInterval.coe_symm_eq]; linarith

theorem resp_lr (p : I × I) (w : Bd × I) (hw : w.2 = 1)
    (h : p = w.1.val ∨ (p.1 = 0 ∧ w.1.val.1 = 1 ∧ w.1.val.2 = σ p.2) ∨
      (p.1 = 1 ∧ w.1.val.1 = 0 ∧ p.2 = σ w.1.val.2)) :
    ver (psi0 (Sum.inl p)) = ver (psi0 (Sum.inr w)) := by
  have e : psi0 (Sum.inr w) = psiL w.1.val := by
    simp only [psi0, Sum.elim_inr, psiR, psiL, hw, Icc.coe_one]
    norm_num
  rw [e]
  exact seam_ver (1 / 4) p w.1.val h

theorem resp_rr (v w : Bd × I) (h1 : v.2 = w.2)
    (h2 : v.2 = 0 ∨ (v.1.val = w.1.val ∨
      (v.1.val.1 = 0 ∧ w.1.val.1 = 1 ∧ w.1.val.2 = σ v.1.val.2) ∨
      (v.1.val.1 = 1 ∧ w.1.val.1 = 0 ∧ v.1.val.2 = σ w.1.val.2))) :
    ver (psi0 (Sum.inr v)) = ver (psi0 (Sum.inr w)) := by
  rcases h2 with h0 | hs
  · have hw0 : w.2 = 0 := h1 ▸ h0
    simp only [psi0, Sum.elim_inr, psiR, h0, hw0, Icc.coe_zero, zero_div, sub_zero]
    rw [pole_ver _ _ v.1.2, pole_ver _ _ w.1.2]
  · simp only [psi0, Sum.elim_inr, psiR]
    rw [← h1]
    exact seam_ver _ _ _ hs

theorem surj_param (s x : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hx0 : -(1 / 2) ≤ x) (hx1 : x ≤ 1 / 2) :
    ∃ a, psi0 a = sphP (π * s) (π * x) := by
  by_cases hlo : x < -(1 / 4)
  · refine ⟨Sum.inr (⟨((⟨s, hs0, hs1⟩ : I), 0), Or.inl rfl⟩,
      ⟨4 * x + 2, by linarith, by linarith⟩), ?_⟩
    show sphP (π * s) (π * ((2 * ((0 : I) : ℝ) - 1) * (1 / 2 - (4 * x + 2) / 4))) = _
    rw [Icc.coe_zero]
    congr 2
    ring
  by_cases hhi : 1 / 4 < x
  · refine ⟨Sum.inr (⟨((⟨s, hs0, hs1⟩ : I), 1), Or.inr rfl⟩,
      ⟨2 - 4 * x, by linarith, by linarith⟩), ?_⟩
    show sphP (π * s) (π * ((2 * ((1 : I) : ℝ) - 1) * (1 / 2 - (2 - 4 * x) / 4))) = _
    rw [Icc.coe_one]
    congr 2
    ring
  · refine ⟨Sum.inl (⟨s, hs0, hs1⟩, ⟨2 * x + 1 / 2, by linarith, by linarith⟩), ?_⟩
    show sphP (π * s) (π * ((2 * (2 * x + 1 / 2) - 1) * (1 / 4))) = _
    congr 2
    ring

theorem surj_upper (v : Fin 3 → ℝ) (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) (h1 : 0 ≤ v 1) :
    ∃ a, psi0 a = v := by
  let z : ℂ := ⟨v 0, v 1⟩
  have hθ0 : 0 ≤ Complex.arg z := Complex.arg_nonneg_iff.mpr h1
  have hθ1 : Complex.arg z ≤ π := Complex.arg_le_pi z
  have hv2 : -1 ≤ v 2 ∧ v 2 ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  have hφ0 := neg_pi_div_two_le_arcsin (v 2)
  have hφ1 := arcsin_le_pi_div_two (v 2)
  have hnorm : ‖z‖ = cos (arcsin (v 2)) := by
    rw [cos_arcsin, Complex.norm_def, Complex.normSq_mk]
    congr 1
    linarith
  obtain ⟨a, ha⟩ := surj_param (Complex.arg z / π) (arcsin (v 2) / π)
    (div_nonneg hθ0 pi_pos.le) (by rw [div_le_one pi_pos]; exact hθ1)
    (by rw [le_div_iff₀ pi_pos]; linarith) (by rw [div_le_iff₀ pi_pos]; linarith)
  refine ⟨a, ha.trans ?_⟩
  have q1 : π * (Complex.arg z / π) = Complex.arg z := by field_simp
  have q2 : π * (arcsin (v 2) / π) = arcsin (v 2) := by field_simp
  rw [q1, q2]
  have e0 : cos (arcsin (v 2)) * cos (Complex.arg z) = v 0 := by
    rw [← hnorm, Complex.norm_mul_cos_arg]
  have e1 : cos (arcsin (v 2)) * sin (Complex.arg z) = v 1 := by
    rw [← hnorm, Complex.norm_mul_sin_arg]
  have e2 : sin (arcsin (v 2)) = v 2 := sin_arcsin hv2.1 hv2.2
  funext i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2

theorem surj (v : Fin 3 → ℝ) (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    ∃ a, ver (psi0 a) = ver v := by
  by_cases h1 : 0 ≤ v 1
  · obtain ⟨a, ha⟩ := surj_upper v hv h1
    exact ⟨a, by rw [ha]⟩
  · replace h1 : v 1 < 0 := lt_of_not_ge h1
    obtain ⟨a, ha⟩ := surj_upper (-v) (by simp only [Pi.neg_apply, neg_sq]; exact hv)
      (by simp only [Pi.neg_apply]; linarith)
    exact ⟨a, by rw [ha, ver_neg]⟩



theorem sol : OMA.InscribedR1H2R1.H1 := by
  unfold OMA.InscribedR1H2R1.H1
  intro B seam glue
  let Ψ : (I × I) ⊕ (B × I) → Fin 3 → Fin 3 → ℝ := fun a => ver (psi0 a)
  have hΨc : Continuous Ψ := continuous_ver.comp continuous_psi0
  have hresp : ∀ a b, glue a b → Ψ a = Ψ b := by
    rintro (p | v) (q | w) h
    · exact seam_ver (1 / 4) p q h
    · exact resp_lr p w h.1 h.2
    · exact (resp_lr q v h.1 h.2).symm
    · exact resp_rr v w h.1 h.2
  have hll : ∀ p q, Ψ (Sum.inl p) = Ψ (Sum.inl q) →
      Quot.mk glue (Sum.inl p) = Quot.mk glue (Sum.inl q) :=
    fun p q h => Quot.sound (inj_ll p q h)
  have hrl : ∀ w : B × I, w.2 = 1 → Quot.mk glue (Sum.inr w) = Quot.mk glue (Sum.inl w.1.val) :=
    fun w hw => (Quot.sound (show glue (Sum.inl w.1.val) (Sum.inr w) from ⟨hw, Or.inl rfl⟩)).symm
  have hΨrl : ∀ w : B × I, w.2 = 1 → Ψ (Sum.inr w) = Ψ (Sum.inl w.1.val) :=
    fun w hw => (hresp _ _ (show glue (Sum.inl w.1.val) (Sum.inr w) from ⟨hw, Or.inl rfl⟩)).symm
  have hinj : ∀ a b, Ψ a = Ψ b → Quot.mk glue a = Quot.mk glue b := by
    rintro (p | v) (q | w) h
    · exact hll p q h
    · have hw := u_one p w h
      rw [hrl w hw]
      exact hll p _ (h.trans (hΨrl w hw))
    · have hv := u_one q v h.symm
      rw [hrl v hv]
      exact hll _ q ((hΨrl v hv).symm.trans h)
    · rcases inj_rr v w h with rfl | h'
      · rfl
      · exact Quot.sound h'
  have hcB : IsCompact {p : I × I | p.2 = 0 ∨ p.2 = 1} :=
    ((isClosed_eq continuous_snd continuous_const).union
      (isClosed_eq continuous_snd continuous_const)).isCompact
  have : CompactSpace B := isCompact_iff_compactSpace.mp hcB
  let F : Quot glue → Set.range Ψ :=
    Quot.lift (fun a => ⟨Ψ a, a, rfl⟩) (fun a b h => Subtype.ext (hresp a b h))
  have hFc : Continuous F := continuous_quot_lift _ (hΨc.subtype_mk _)
  have hFi : Function.Injective F := by
    rintro ⟨a⟩ ⟨b⟩ h
    exact hinj a b (congrArg Subtype.val h)
  have hFs : Function.Surjective F := by
    rintro ⟨_, a, rfl⟩
    exact ⟨Quot.mk _ a, rfl⟩
  let e : Quot glue ≃ₜ Set.range Ψ :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F ⟨hFi, hFs⟩) hFc
  have hsq : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      (x.val 0) ^ 2 + (x.val 1) ^ 2 + (x.val 2) ^ 2 = 1 := by
    intro x
    have h1 : ‖x.val‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
    have h2 := EuclideanSpace.real_norm_sq_eq x.val
    rw [h1, Fin.sum_univ_three] at h2
    linarith
  have hne : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, (fun i => x.val i) ≠ 0 := by
    intro x h0
    have h := hsq x
    have a0 := congrFun h0 0
    have a1 := congrFun h0 1
    have a2 := congrFun h0 2
    simp only [Pi.zero_apply] at a0 a1 a2
    rw [a0, a1, a2] at h
    norm_num at h
  have hmem : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ver (fun i => x.val i) ∈ Set.range Ψ := fun x => surj _ (hsq x)
  refine ⟨fun x => e.symm ⟨ver (fun i => x.val i), hmem x⟩, ?_, ?_⟩
  · apply e.symm.continuous.comp
    apply Continuous.subtype_mk
    apply continuous_ver.comp
    exact continuous_pi fun i => (PiLp.continuous_apply 2 _ i).comp continuous_subtype_val
  · intro x y
    constructor
    · intro h
      have h2 := congrArg Subtype.val (e.symm.injective h)
      rcases ver_eq (hne x) h2 with h3 | h3
      · left
        apply Subtype.ext
        ext i
        exact congrFun h3 i
      · right
        ext i
        simpa using congrFun h3 i
    · rintro (rfl | h)
      · rfl
      · have h4 : (fun i => x.val i) = -(fun i => y.val i) := by
          funext i
          simp [h]
        have h5 : ver (fun i => x.val i) = ver (fun i => y.val i) := by
          rw [h4, ver_neg]
        show e.symm _ = e.symm _
        congr 1
        exact Subtype.ext h5
end OMA.InscribedHelpers



/-
An orbit-separating even map would realize the real tautological line on a
compact subset of three-space. For its complexification, a nonzero section
would give a nowhere-zero odd complex function on the sphere by pairing
the section with its real unit representative.

The first input is the line-bundle consequence of Alexander duality:
degree-two integral Čech cohomology of a compact subset of R³ is
torsion-free, and the complexification of a real line has tensor square
trivial. The second input is the planar Borsuk–Ulam obstruction.
-/
namespace OMA.InscribedR1H2R1H2R1

/-- A real rank-one orthogonal projection over a compact subset of three-space
has a nowhere-zero continuous section after complexification. -/
def H1 : Prop :=
  ∀ K : Set (EuclideanSpace ℝ (Fin 2) × ℝ), IsCompact K →
  ∀ P : K → Fin 3 → Fin 3 → ℝ, Continuous P →
  (∀ k, ∃ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
    ∀ i j, P k i j = x.val i * x.val j) →
  ∃ s : K → Fin 3 → ℂ, Continuous s ∧ ∀ k, s k ≠ 0 ∧
    ∀ i, ∑ j, (P k i j : ℂ) * s k j = s k i

/-- An odd continuous complex function on the two-sphere has a zero. -/
def H2 : Prop :=
  ∀ f : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℂ, Continuous f →
    (∀ x y, x.val = -y.val → f x = -f y) → ∃ x, f x=0

theorem main : H1 → H2 → OMA.InscribedR1H2R1.H2 := by
  classical
  intro hsphere hzero g hg heven
  by_contra hn
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
  let K := Set.range g
  let q : S → K := Set.rangeFactorization g
  have hq : Continuous q := hg.subtype_mk _
  have hsur : Function.Surjective q := Set.rangeFactorization_surjective
  have hcompact : IsCompact K := isCompact_range hg
  have hsep (x y : S) (h : g x=g y) : x=y ∨ x.val = -y.val := by
    by_cases hxy : x=y
    · exact Or.inl hxy
    · exact Or.inr (by by_contra h'; exact hn ⟨x,y,h,hxy,h'⟩)
  let rep (k : K) : S := k.property.choose
  have hrep (k : K) : g (rep k)=k.val := k.property.choose_spec
  let P (k : K) (i j : Fin 3) := (rep k).val i * (rep k).val j
  have hP (x : S) (i j : Fin 3) : P (q x) i j = x.val i * x.val j := by
    rcases hsep (rep (q x)) x (hrep _) with h|h
    · simp [P,h]
    · simp [P,h]
  have hPc : Continuous P := by
    apply (Topology.IsQuotientMap.of_surjective_continuous hsur hq).continuous_iff.mpr
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun x : S => P (q x) i j)
    simp only [hP]
    fun_prop
  obtain ⟨s,hsc,hs⟩ := hsphere K hcompact P hPc (fun k => ⟨rep k,fun _ _ => rfl⟩)
  let f (x : S) : ℂ := ∑ j, (x.val j : ℂ) * s (q x) j
  have hfc : Continuous f := by unfold f; fun_prop
  have hfodd (x y : S) (h : x.val = -y.val) : f x = -f y := by
    have hqxy : q x=q y := Subtype.ext (heven x y h)
    simp [f,hqxy,h,Finset.sum_neg_distrib]
  obtain ⟨x,hx⟩ := hzero f hfc hfodd
  apply (hs (q x)).1
  ext i
  change s (q x) i = 0
  calc
    s (q x) i = ∑ j, (P (q x) i j : ℂ)*s (q x) j := ((hs _).2 i).symm
    _ = (x.val i : ℂ)*f x := by
      unfold f
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hP,Complex.ofReal_mul,mul_assoc]
    _ = 0 := by rw [hx,mul_zero]

end OMA.InscribedR1H2R1H2R1


/- An odd complex-valued function on the two-sphere cannot be nowhere zero. -/

namespace OMA.HemisphereLog
open Set Metric Complex

private noncomputable def v (z : ℂ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![2 * z.re / (1 + normSq z), 2 * z.im / (1 + normSq z),
    (1 - normSq z) / (1 + normSq z)]

private theorem norm_v (z : ℂ) : ‖v z‖ = 1 := by
  have hd : 0 < 1 + normSq z := by linarith [normSq_nonneg z]
  have hsq : ‖v z‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    change (2 * z.re / (1 + normSq z))^2 +
      (2 * z.im / (1 + normSq z))^2 + ((1 - normSq z) / (1 + normSq z))^2 = 1
    field_simp
    rw [Complex.normSq_apply]
    ring
  nlinarith [norm_nonneg (v z)]

private noncomputable def spherePoint (z : ℂ) : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨v z, by simp [norm_v]⟩

private theorem point_continuous : Continuous spherePoint := by
  have hd : ∀ z : ℂ, 1 + normSq z ≠ 0 := fun z =>
    (by linarith [normSq_nonneg z] : 0 < 1 + normSq z).ne'
  apply Continuous.subtype_mk
  unfold v
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i <;> fun_prop (disch := exact hd _)

private theorem equator (z : ℂ) (hz : normSq z = 1) :
    (spherePoint (-z)).val = -(spherePoint z).val := by
  change v (-z) = -(v z)
  ext i
  fin_cases i <;>
    simp [v, Complex.normSq_neg, hz, neg_div, mul_neg]

theorem odd_zero (f : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℂ)
    (hc : Continuous f) (odd : ∀ x y, x.val = -y.val → f x = -f y) :
    ∃ x, f x = 0 := by
  by_contra! hnone
  let g : ℂ → ℂ := f ∘ spherePoint
  have hg : Continuous g := hc.comp point_continuous
  have hnonzero (z : ℂ) : g z ≠ 0 := hnone (spherePoint z)
  have hsc : IsSimplyConnected (univ : Set ℂ) := by
    change SimplyConnectedSpace (univ : Set ℂ)
    let _ : ContractibleSpace (univ : Set ℂ) :=
      (convex_univ : Convex ℝ (univ : Set ℂ)).contractibleSpace univ_nonempty
    infer_instance
  obtain ⟨L, hL, hLift⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc isOpen_univ
    hg.continuousOn (by simpa [Set.mem_image] using hnonzero)
  have hLc : Continuous L := continuousOn_univ.mp hL
  have he (z : ℂ) : Complex.exp (L z) = g z := hLift (mem_univ z)
  let ζ (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)
  have hζc : Continuous ζ := by unfold ζ; fun_prop
  have hζ (t : ℝ) : normSq (ζ t) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]
  have hex (t : ℝ) : Complex.exp (L (-ζ t) - L (ζ t)) = -1 := by
    have h := odd (spherePoint (-ζ t)) (spherePoint (ζ t)) (equator _ (hζ t))
    rw [Complex.exp_sub, he, he]
    change f (spherePoint (-ζ t)) / g (ζ t) = -1
    rw [h]
    change -g (ζ t) / g (ζ t) = -1
    rw [neg_div, div_self (hnonzero _)]
  let d (t : ℝ) : ℝ := (L (-ζ t) - L (ζ t)).im
  have hd : Continuous d := Complex.continuous_im.comp ((hLc.comp hζc.neg).sub (hLc.comp hζc))
  have h0 : ζ 0 = 1 := by simp [ζ]
  have hπ : ζ Real.pi = -1 := Complex.exp_pi_mul_I
  have flip : d Real.pi = -d 0 := by
    simp only [d, hπ, h0, neg_neg, Complex.sub_im]
    ring
  have hz : ∃ t, d t = 0 := by
    by_cases hh : d 0 ≤ 0
    · exact intermediate_value_univ 0 Real.pi hd (show (0 : ℝ) ∈ Icc (d 0) (d Real.pi) from
        ⟨hh, by rw [flip]; linarith⟩)
    · exact intermediate_value_univ Real.pi 0 hd (show (0 : ℝ) ∈ Icc (d Real.pi) (d 0) from
        ⟨by rw [flip]; linarith, by linarith⟩)
  obtain ⟨t, ht⟩ := hz
  have h := congrArg Complex.re (hex t)
  rw [Complex.exp_re, show (L (-ζ t) - L (ζ t)).im = 0 from ht,
    Real.cos_zero, mul_one, Complex.neg_re, Complex.one_re] at h
  linarith [Real.exp_pos (L (-ζ t) - L (ζ t)).re]

end OMA.HemisphereLog

/- Elementary cubical cochain proof of H1 for InscribedSquare.exists_inscribed_rectangle. -/

namespace OMA.InscribedH1

open Topology Set Metric Filter

private abbrev G := Fin 3 → ℤ

private def e (d : Fin 3) : G := Pi.single d 1

private def ax1 : Fin 3 → Fin 3
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 0

private def ax2 : Fin 3 → Fin 3
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 1

private def dot3 (x y : Fin 3 → ℝ) : ℝ := ∑ i, x i * y i

private def IsUnit3 (x : Fin 3 → ℝ) : Prop := dot3 x x = 1

private noncomputable def sgn (t : ℝ) : ℝ := if 0 ≤ t then 1 else -1

private lemma sgn_sq (t : ℝ) : sgn t ^ 2 = 1 := by
  unfold sgn; split_ifs <;> norm_num

private lemma sgn_mul_self (t : ℝ) : sgn t * sgn t = 1 := by
  unfold sgn; split_ifs <;> norm_num

private lemma sgn_ne_zero (t : ℝ) : sgn t ≠ 0 := by
  unfold sgn; split_ifs <;> norm_num

private lemma sgn_mul_eq_abs (t : ℝ) : sgn t * t = |t| := by
  unfold sgn
  split_ifs with h
  · rw [one_mul, abs_of_nonneg h]
  · rw [neg_one_mul, abs_of_neg (lt_of_not_ge h)]

private lemma sgn_eq_div_abs {t : ℝ} (ht : t ≠ 0) : sgn t = t / |t| := by
  have habs : |t| ≠ 0 := abs_ne_zero.mpr ht
  rw [eq_div_iff habs]
  have h := sgn_mul_eq_abs t
  have h1 := congrArg (fun z => sgn t * z) h
  rw [← mul_assoc, sgn_mul_self, one_mul] at h1
  exact h1.symm

private lemma proj_dist_sq {x y : Fin 3 → ℝ} (hx : IsUnit3 x) (hy : IsUnit3 y) :
    ∑ i : Fin 3, ∑ j : Fin 3, (x i * x j - y i * y j) ^ 2 = 2 - 2 * (dot3 x y) ^ 2 := by
  simp only [IsUnit3, dot3, Fin.sum_univ_three] at hx hy ⊢
  have hx2 : (x 0 * x 0 + x 1 * x 1 + x 2 * x 2) ^ 2 = 1 := by rw [hx]; norm_num
  have hy2 : (y 0 * y 0 + y 1 * y 1 + y 2 * y 2) ^ 2 = 1 := by rw [hy]; norm_num
  linear_combination hx2 + hy2

private lemma dot_sq_gt_of_proj_close {x y : Fin 3 → ℝ} (hx : IsUnit3 x) (hy : IsUnit3 y)
    (h : ∀ i j : Fin 3, |x i * x j - y i * y j| < 1 / 6) :
    (7 : ℝ) / 8 < (dot3 x y) ^ 2 := by
  have hsq : ∀ i j : Fin 3, (x i * x j - y i * y j) ^ 2 < 1 / 36 := by
    intro i j
    have h1 := h i j
    have h2 : |x i * x j - y i * y j| ^ 2 < (1 / 6 : ℝ) ^ 2 :=
      sq_lt_sq' (by linarith [abs_nonneg (x i * x j - y i * y j)]) h1
    rw [sq_abs] at h2
    linarith
  have hsum : ∑ i : Fin 3, ∑ j : Fin 3, (x i * x j - y i * y j) ^ 2 < 1 / 4 := by
    simp only [Fin.sum_univ_three]
    linarith [hsq 0 0, hsq 0 1, hsq 0 2, hsq 1 0, hsq 1 1, hsq 1 2, hsq 2 0, hsq 2 1, hsq 2 2]
  rw [proj_dist_sq hx hy] at hsum
  linarith

private lemma abs_dot_gt_of_sq {t : ℝ} (ht : (7 : ℝ) / 8 < t ^ 2) : (9 : ℝ) / 10 < |t| := by
  have h : ((9 : ℝ) / 10) ^ 2 < |t| ^ 2 := by rw [sq_abs]; linarith
  nlinarith [abs_nonneg t]

private lemma sgn_consistent {u v w : Fin 3 → ℝ}
    (hu : IsUnit3 u) (hv : IsUnit3 v) (hw : IsUnit3 w)
    (huv : (7 : ℝ) / 8 < (dot3 u v) ^ 2)
    (hvw : (7 : ℝ) / 8 < (dot3 v w) ^ 2)
    (huw : (7 : ℝ) / 8 < (dot3 u w) ^ 2) :
    sgn (dot3 u v) * sgn (dot3 v w) = sgn (dot3 u w) := by
  let su := sgn (dot3 u v)
  let sw := sgn (dot3 v w)
  let u' : Fin 3 → ℝ := fun i => su * u i
  let w' : Fin 3 → ℝ := fun i => sw * w i
  have hdu'v : (9 : ℝ) / 10 < dot3 u' v := by
    have : dot3 u' v = |dot3 u v| := by
      have hmul : dot3 u' v = sgn (dot3 u v) * dot3 u v := by
        simp only [dot3, u', su, Fin.sum_univ_three]; ring
      rw [hmul, sgn_mul_eq_abs]
    rw [this]; exact abs_dot_gt_of_sq huv
  have hdw'v : (9 : ℝ) / 10 < dot3 w' v := by
    have : dot3 w' v = |dot3 v w| := by
      have hmul : dot3 w' v = sgn (dot3 v w) * dot3 v w := by
        simp only [dot3, w', sw, Fin.sum_univ_three]; ring
      rw [hmul, sgn_mul_eq_abs]
    rw [this]; exact abs_dot_gt_of_sq hvw
  have hdu'w' : dot3 u' w' = su * sw * dot3 u w := by
    simp only [dot3, u', w', Fin.sum_univ_three]; ring
  have hu' : dot3 u' u' = 1 := by
    have hsu2 : su ^ 2 = 1 := sgn_sq _
    simp only [dot3, u', IsUnit3, Fin.sum_univ_three] at hu ⊢
    linear_combination su ^ 2 * hu + hsu2
  have hw' : dot3 w' w' = 1 := by
    have hsw2 : sw ^ 2 = 1 := sgn_sq _
    simp only [dot3, w', IsUnit3, Fin.sum_univ_three] at hw ⊢
    linear_combination sw ^ 2 * hw + hsw2
  have hpos : 0 < dot3 u' w' := by
    have h0 : 0 ≤ (u' 0 + w' 0 - 2 * v 0) ^ 2 + (u' 1 + w' 1 - 2 * v 1) ^ 2 +
        (u' 2 + w' 2 - 2 * v 2) ^ 2 := by positivity
    simp only [dot3, IsUnit3, Fin.sum_univ_three] at hu' hw' hv hdu'v hdw'v ⊢
    nlinarith
  rw [hdu'w'] at hpos
  have huw_ne : dot3 u w ≠ 0 := by intro h0; rw [h0] at huw; norm_num at huw
  unfold sgn
  by_cases h1 : 0 ≤ dot3 u v <;> by_cases h2 : 0 ≤ dot3 v w <;> by_cases h3 : 0 ≤ dot3 u w <;>
    simp only [su, sw, sgn, h1, h2, h3, ↓reduceIte] at hpos ⊢ <;> linarith

private lemma even_of_sgn_prod {a b c d : ℝ}
    (h : sgn a * sgn b = sgn c * sgn d) :
    2 ∣ ((if a < 0 then (1 : ℤ) else 0) + (if b < 0 then 1 else 0) -
         (if c < 0 then 1 else 0) - (if d < 0 then 1 else 0)) := by
  unfold sgn at h
  by_cases ha : a < 0 <;> by_cases hb : b < 0 <;> by_cases hc : c < 0 <;> by_cases hd : d < 0 <;>
    simp only [not_lt.symm, ha, hb, hc, hd, not_true_eq_false, not_false_eq_true, ↓reduceIte] at h ⊢
  all_goals norm_num at h
  all_goals decide

/- Cubical cochains on ℤ³ -/

private def d1 (α : G → Fin 3 → ℤ) (v : G) (k : Fin 3) : ℤ :=
  α v (ax1 k) + α (v + e (ax1 k)) (ax2 k) - α (v + e (ax2 k)) (ax1 k) - α v (ax2 k)

private def d2 (β : G → Fin 3 → ℤ) (c : G) : ℤ :=
  ∑ k : Fin 3, (β (c + e k) k - β c k)

private lemma d2_d1 (α : G → Fin 3 → ℤ) (c : G) : d2 (d1 α) c = 0 := by
  simp only [d2, d1, Fin.sum_univ_three, ax1, ax2]
  have h01 : c + e 0 + e 1 = c + e 1 + e 0 := add_right_comm c (e 0) (e 1)
  have h02 : c + e 0 + e 2 = c + e 2 + e 0 := add_right_comm c (e 0) (e 2)
  have h12 : c + e 1 + e 2 = c + e 2 + e 1 := add_right_comm c (e 1) (e 2)
  rw [h01, h02, h12]
  ring

private lemma d2_add (β₁ β₂ : G → Fin 3 → ℤ) (c : G) :
    d2 (fun v k => β₁ v k + β₂ v k) c = d2 β₁ c + d2 β₂ c := by
  simp only [d2, Fin.sum_univ_three]; ring

private lemma d2_sub (β₁ β₂ : G → Fin 3 → ℤ) (c : G) :
    d2 (fun v k => β₁ v k - β₂ v k) c = d2 β₁ c - d2 β₂ c := by
  simp only [d2, Fin.sum_univ_three]; ring

private lemma d2_smul (a : ℤ) (β : G → Fin 3 → ℤ) (c : G) :
    d2 (fun v k => a * β v k) c = a * d2 β c := by
  simp only [d2, Fin.sum_univ_three]; ring

private lemma d2_sum {ι : Type*} (s : Finset ι) (f : ι → G → Fin 3 → ℤ) (c : G) :
    d2 (fun v k => ∑ i ∈ s, f i v k) c = ∑ i ∈ s, d2 (f i) c := by
  classical
  induction s using Finset.induction with
  | empty => simp [d2]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [d2_add, ih]

private def stepFace (c₁ : G) (k : Fin 3) (v : G) (j : Fin 3) : ℤ :=
  if v = c₁ + e k ∧ j = k then 1 else 0

private lemma d2_stepFace (c₁ : G) (k : Fin 3) (x : G) :
    d2 (stepFace c₁ k) x = (if x = c₁ then 1 else 0) - (if x = c₁ + e k then 1 else 0) := by
  simp only [d2, stepFace]
  have hsum : ∀ (P : Fin 3 → ℤ), ∑ j : Fin 3, (if j = k then P j else 0) = P k := by
    intro P; simp
  have h1 : ∀ j : Fin 3,
      ((if x + e j = c₁ + e k ∧ j = k then (1 : ℤ) else 0) -
       (if x = c₁ + e k ∧ j = k then 1 else 0)) =
      if j = k then (if x + e k = c₁ + e k then 1 else 0) - (if x = c₁ + e k then 1 else 0)
      else 0 := by
    intro j
    by_cases hjk : j = k
    · subst hjk; simp
    · simp [hjk]
  simp_rw [h1, hsum]
  have hx : (x + e k = c₁ + e k) ↔ (x = c₁) := ⟨add_right_cancel, fun h => h ▸ rfl⟩
  simp [hx]

/- Path-flow elimination on V_out -/

private def adjIn (V : Finset G) (x y : G) : Prop :=
  x ∈ V ∧ y ∈ V ∧ ∃ k : Fin 3, y = x + e k ∨ x = y + e k

private lemma adjIn_symm {V : Finset G} {x y : G} (h : adjIn V x y) : adjIn V y x := by
  rcases h with ⟨hx, hy, k, hk | hk⟩
  · exact ⟨hy, hx, k, Or.inr hk⟩
  · exact ⟨hy, hx, k, Or.inl hk⟩

private lemma exists_flow_between (V : Finset G) {c₀ c : G}
    (h : Relation.ReflTransGen (adjIn V) c₀ c) :
    ∃ φ : G → Fin 3 → ℤ,
      (∀ v k, φ v k ≠ 0 → v ∈ V ∧ v - e k ∈ V) ∧
      (∀ x, d2 φ x = (if x = c then 1 else 0) - (if x = c₀ then 1 else 0)) := by
  induction h with
  | refl =>
    exact ⟨fun _ _ => 0, fun _ _ h0 => absurd rfl h0, fun x => by simp [d2]⟩
  | @tail b d _ hbd ih =>
    obtain ⟨φ₁, hsupp₁, hd₁⟩ := ih
    rcases hbd with ⟨hbV, hdV, k, rfl | hb_eq⟩
    · refine ⟨fun v j => φ₁ v j - stepFace b k v j, ?_, ?_⟩
      · intro v j hvj
        dsimp only at hvj
        by_cases h1 : φ₁ v j ≠ 0
        · exact hsupp₁ v j h1
        · push Not at h1
          rw [h1, zero_sub, neg_ne_zero] at hvj
          unfold stepFace at hvj
          split_ifs at hvj with hcond
          · rcases hcond with ⟨rfl, rfl⟩
            exact ⟨hdV, by simpa using hbV⟩
          · exact absurd rfl hvj
      · intro x
        rw [d2_sub, hd₁ x, d2_stepFace]
        ring
    · refine ⟨fun v j => φ₁ v j + stepFace d k v j, ?_, ?_⟩
      · intro v j hvj
        dsimp only at hvj
        by_cases h1 : φ₁ v j ≠ 0
        · exact hsupp₁ v j h1
        · push Not at h1
          rw [h1, zero_add] at hvj
          unfold stepFace at hvj
          split_ifs at hvj with hcond
          · rcases hcond with ⟨rfl, rfl⟩
            rw [hb_eq] at hbV
            exact ⟨hbV, by simpa using hdV⟩
          · exact absurd rfl hvj
      · intro x
        rw [d2_add, hd₁ x, d2_stepFace, ← hb_eq]
        ring

private lemma sum_d2_eq_zero_of_closed_comp (U : Finset G) (η : G → Fin 3 → ℤ)
    (hclosed : ∀ v k, η v k ≠ 0 → (v ∈ U ↔ v - e k ∈ U)) :
    ∑ c ∈ U, d2 η c = 0 := by
  classical
  unfold d2
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k _
  rw [Finset.sum_sub_distrib]
  suffices h : ∑ c ∈ U, η (c + e k) k = ∑ c ∈ U, η c k by linarith
  have h1 : ∑ c ∈ U, η (c + e k) k = ∑ c ∈ U.filter (fun c => η (c + e k) k ≠ 0), η (c + e k) k := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : η (c + e k) k = 0 <;> simp [hc]
  have h2 : ∑ c ∈ U, η c k = ∑ c ∈ U.filter (fun c => η c k ≠ 0), η c k := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : η c k = 0 <;> simp [hc]
  rw [h1, h2]
  refine Finset.sum_nbij (fun c => c + e k) ?_ ?_ ?_ ?_
  · intro c hc
    rw [Finset.mem_filter] at hc ⊢
    refine ⟨?_, hc.2⟩
    exact (hclosed (c + e k) k hc.2).mpr (by simpa using hc.1)
  · intro a _ b _ hab
    exact add_right_cancel hab
  · intro v hv
    rw [Finset.mem_coe, Finset.mem_filter] at hv
    refine ⟨v - e k, ?_, sub_add_cancel v (e k)⟩
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨(hclosed v k hv.2).mp hv.1, ?_⟩
    simpa [sub_add_cancel] using hv.2
  · intro _ _; rfl

/- Exactness of finitely supported 2-cocycles on ℤ³ -/

private def tailSum (N : ℤ) (f : ℤ → ℤ) (z : ℤ) : ℤ :=
  ∑ t ∈ Finset.range (N + 1 - z).toNat, f (z + (t : ℤ))

private lemma tailSum_sub (N : ℤ) (f : ℤ → ℤ) (hf : ∀ w, N < w → f w = 0) (z : ℤ) :
    tailSum N f z - tailSum N f (z + 1) = f z := by
  unfold tailSum
  by_cases hz : N < z
  · have h1 : (N + 1 - z).toNat = 0 := by omega
    have h2 : (N - z).toNat = 0 := by omega
    have h3 : N + 1 - (z + 1) = N - z := by omega
    rw [h3, h1, h2]
    simp [hf z hz]
  · have hm : (N + 1 - z).toNat = (N + 1 - (z + 1)).toNat + 1 := by omega
    rw [hm, Finset.sum_range_succ']
    have hcongr : ∑ x ∈ Finset.range (N + 1 - (z + 1)).toNat, f (z + ((x + 1 : ℕ) : ℤ)) =
        ∑ x ∈ Finset.range (N + 1 - (z + 1)).toNat, f (z + 1 + (x : ℤ)) := by
      apply Finset.sum_congr rfl
      intro x _
      congr 1; push_cast; ring
    rw [hcongr]
    simp

private lemma exists_primitive_d1 (N : ℤ) (β : G → Fin 3 → ℤ)
    (hclosed : ∀ c : G, d2 β c = 0)
    (hsupp : ∀ v k, β v k ≠ 0 → v 2 ≤ N) :
    ∃ γ : G → Fin 3 → ℤ, ∀ v k, d1 γ v k = β v k := by
  let γ : G → Fin 3 → ℤ := fun v d =>
    match d with
    | ⟨0, _⟩ => -tailSum N (fun z => β (Function.update v 2 z) 1) (v 2)
    | ⟨1, _⟩ => tailSum N (fun z => β (Function.update v 2 z) 0) (v 2)
    | ⟨2, _⟩ => 0
  refine ⟨γ, fun v k => ?_⟩
  have hzero (u : G) (j : Fin 3) (w : ℤ) (hw : N < w) : β (Function.update u 2 w) j = 0 := by
    by_contra hne
    have hle := hsupp _ j hne
    simp at hle
    omega
  have hupd2 : ∀ z : ℤ, Function.update (v + e 2) 2 z = Function.update v 2 z := by
    intro z; funext a
    by_cases ha : a = 2
    · subst ha; simp
    · simp [Function.update, ha, e]
  have hv2 : (v + e 2) 2 = v 2 + 1 := by simp [e]
  have hv0 : (v + e 0) 2 = v 2 := by simp [e]
  have hv1 : (v + e 1) 2 = v 2 := by simp [e]
  have hγ0 (u : G) : γ u 0 = -tailSum N (fun z => β (Function.update u 2 z) 1) (u 2) := rfl
  have hγ1 (u : G) : γ u 1 = tailSum N (fun z => β (Function.update u 2 z) 0) (u 2) := rfl
  have hγ2 (u : G) : γ u 2 = 0 := rfl
  fin_cases k
  · change d1 γ v 0 = β v 0
    simp only [d1, ax1, ax2, hγ1, hγ2, hupd2, hv2, add_zero, sub_zero]
    have h := tailSum_sub N (fun z => β (Function.update v 2 z) 0) (hzero v 0) (v 2)
    simpa [Function.update_eq_self] using h
  · change d1 γ v 1 = β v 1
    simp only [d1, ax1, ax2, hγ0, hγ2, hupd2, hv2, zero_add, sub_zero, sub_neg_eq_add]
    have h := tailSum_sub N (fun z => β (Function.update v 2 z) 1) (hzero v 1) (v 2)
    rw [add_comm, ← sub_eq_add_neg]
    simpa [Function.update_eq_self] using h
  · change d1 γ v 2 = β v 2
    simp only [d1, ax1, ax2, hγ0, hγ1, hv0, hv1, sub_neg_eq_add]
    have hsub := tailSum_sub N (fun z => β (Function.update v 2 z) 2) (hzero v 2) (v 2)
    rw [Function.update_eq_self] at hsub
    rw [← hsub]
    unfold tailSum
    have hcongr : ∀ t : ℕ,
        -β (Function.update v 2 (v 2 + t)) 1 +
          β (Function.update (v + e 0) 2 (v 2 + t)) 0 +
          β (Function.update (v + e 1) 2 (v 2 + t)) 1 -
          β (Function.update v 2 (v 2 + t)) 0 =
        β (Function.update v 2 (v 2 + t)) 2 -
          β (Function.update v 2 (v 2 + 1 + t)) 2 := by
      intro t
      let w : G := Function.update v 2 (v 2 + t)
      have hw0 : Function.update (v + e 0) 2 (v 2 + t) = w + e 0 := by
        funext a; fin_cases a <;> simp [w, e]
      have hw1 : Function.update (v + e 1) 2 (v 2 + t) = w + e 1 := by
        funext a; fin_cases a <;> simp [w, e]
      have hw2 : Function.update v 2 (v 2 + 1 + t) = w + e 2 := by
        funext a; fin_cases a <;> simp [w, e] <;> ring
      rw [hw0, hw1, hw2]
      have hcl := hclosed w
      simp only [d2, Fin.sum_univ_three] at hcl
      linarith
    have hrange : (N + 1 - v 2).toNat = (N + 1 - (v 2 + 1)).toNat + 1 ∨
        ((N + 1 - v 2).toNat = 0 ∧ (N + 1 - (v 2 + 1)).toNat = 0) := by omega
    have hcomb :
        -∑ t ∈ Finset.range (N + 1 - v 2).toNat, β (Function.update v 2 (v 2 + t)) 1 +
          ∑ t ∈ Finset.range (N + 1 - v 2).toNat, β (Function.update (v + e 0) 2 (v 2 + t)) 0 +
          ∑ t ∈ Finset.range (N + 1 - v 2).toNat, β (Function.update (v + e 1) 2 (v 2 + t)) 1 -
          ∑ t ∈ Finset.range (N + 1 - v 2).toNat, β (Function.update v 2 (v 2 + t)) 0 =
        ∑ t ∈ Finset.range (N + 1 - v 2).toNat,
          (β (Function.update v 2 (v 2 + t)) 2 - β (Function.update v 2 (v 2 + 1 + t)) 2) := by
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro t _
      exact hcongr t
    rw [hcomb, Finset.sum_sub_distrib]
    congr 1
    rcases hrange with hm | ⟨h0, h1⟩
    · rw [hm, Finset.sum_range_succ]
      have hlast : β (Function.update v 2 (v 2 + 1 + ((N + 1 - (v 2 + 1)).toNat : ℤ))) 2 = 0 := by
        apply hzero
        omega
      rw [hlast, add_zero]
    · rw [h0, h1]

/- Boxes, corners, and integer cochain lifting on M -/

private def box (R : ℤ) : Finset G :=
  Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-R) R

private lemma mem_box {R : ℤ} {c : G} : c ∈ box R ↔ ∀ a : Fin 3, -R ≤ c a ∧ c a ≤ R := by
  simp [box]

private def corners (c : G) : Finset G :=
  Fintype.piFinset fun a : Fin 3 => ({c a, c a + 1} : Finset ℤ)

private lemma mem_corners {c v : G} : v ∈ corners c ↔ ∀ a : Fin 3, v a = c a ∨ v a = c a + 1 := by
  simp [corners]

private lemma self_mem_corners (c : G) : c ∈ corners c :=
  mem_corners.mpr fun _ => Or.inl rfl

private lemma exists_cochain_lift (N : ℤ) (M : Finset G)
    (α : G → Fin 3 → ℤ)
    (hα_supp : ∀ v d, α v d ≠ 0 → v ∈ box (N - 2))
    (hd1_even : ∀ v k, (v ∈ M ∨ v - e k ∈ M) → 2 ∣ d1 α v k) :
    ∃ γ : G → Fin 3 → ℤ, ∀ v k, (v ∈ M ∨ v - e k ∈ M) → 2 * d1 γ v k = d1 α v k := by
  classical
  let isFace (v : G) (k : Fin 3) : Prop := v ∈ M ∨ v - e k ∈ M
  let β (v : G) (k : Fin 3) : ℤ := if isFace v k then d1 α v k / 2 else 0
  let ηc (v : G) (k : Fin 3) : ℤ := if isFace v k then 0 else d1 α v k
  have hdecomp : ∀ v k, 2 * β v k + ηc v k = d1 α v k := by
    intro v k
    by_cases h : isFace v k
    · simp only [β, ηc, h, ↓reduceIte, add_zero]
      exact Int.mul_ediv_cancel' (hd1_even v k h)
    · simp [β, ηc, h]
  have hd2_rel : ∀ c : G, 2 * d2 β c + d2 ηc c = 0 := by
    intro c
    rw [← d2_smul, ← d2_add]
    have : (fun v k => 2 * β v k + ηc v k) = d1 α := funext fun v => funext fun k => hdecomp v k
    rw [this, d2_d1]
  have hd1_supp : ∀ v k, d1 α v k ≠ 0 → v ∈ box (N - 1) := by
    intro v k hne
    have h1 : α v (ax1 k) ≠ 0 ∨ α (v + e (ax1 k)) (ax2 k) ≠ 0 ∨
        α (v + e (ax2 k)) (ax1 k) ≠ 0 ∨ α v (ax2 k) ≠ 0 := by
      by_contra hall
      push Not at hall
      rcases hall with ⟨h1, h2, h3, h4⟩
      exact hne (by simp [d1, h1, h2, h3, h4])
    rcases h1 with h | h | h | h
    · have hb := mem_box.mp (hα_supp v _ h)
      rw [mem_box]; intro a; have := hb a; omega
    · have hb := mem_box.mp (hα_supp (v + e (ax1 k)) _ h)
      rw [mem_box]; intro a; have := hb a
      by_cases ha : a = ax1 k
      · subst ha; simp [e] at this; omega
      · simp [e, ha] at this; omega
    · have hb := mem_box.mp (hα_supp (v + e (ax2 k)) _ h)
      rw [mem_box]; intro a; have := hb a
      by_cases ha : a = ax2 k
      · subst ha; simp [e] at this; omega
      · simp [e, ha] at this; omega
    · have hb := mem_box.mp (hα_supp v _ h)
      rw [mem_box]; intro a; have := hb a; omega
  let Vout : Finset G := box N \ M
  have hηc_supp : ∀ v k, ηc v k ≠ 0 → v ∈ Vout ∧ v - e k ∈ Vout := by
    intro v k hne
    have hnf : ¬ isFace v k := by
      intro hf; exact hne (by simp [ηc, hf])
    have hdne : d1 α v k ≠ 0 := by
      intro hd; exact hne (by simp [ηc, hnf, hd])
    have hvbox := mem_box.mp (hd1_supp v k hdne)
    have hvN : v ∈ box N := mem_box.mpr fun a => by have := hvbox a; omega
    have hvkN : v - e k ∈ box N := mem_box.mpr fun a => by
      have := hvbox a
      by_cases ha : a = k
      · subst ha; simp [e]; omega
      · simp [e, ha]; omega
    exact ⟨Finset.mem_sdiff.mpr ⟨hvN, fun h => hnf (Or.inl h)⟩,
      Finset.mem_sdiff.mpr ⟨hvkN, fun h => hnf (Or.inr h)⟩⟩
  have hd2β_supp : ∀ c : G, d2 β c ≠ 0 → c ∈ Vout := by
    intro c hne
    have hcnotM : c ∉ M := by
      intro hcM
      have hη0 : d2 ηc c = 0 := by
        simp only [d2]
        apply Finset.sum_eq_zero
        intro k _
        have hf1 : isFace (c + e k) k := Or.inr (by simpa using hcM)
        have hf2 : isFace c k := Or.inl hcM
        simp [ηc, hf1, hf2]
      have hrel := hd2_rel c
      omega
    have hβne : ∃ k : Fin 3, β (c + e k) k ≠ 0 ∨ β c k ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (by simp [d2, hall])
    obtain ⟨k, hk | hk⟩ := hβne
    · have hdne : d1 α (c + e k) k ≠ 0 := fun hd => hk (by simp [β, hd])
      have hb := mem_box.mp (hd1_supp (c + e k) k hdne)
      refine Finset.mem_sdiff.mpr ⟨mem_box.mpr fun a => ?_, hcnotM⟩
      have := hb a
      by_cases ha : a = k
      · subst ha; simp [e] at this; omega
      · simp [e, ha] at this; omega
    · have hdne : d1 α c k ≠ 0 := fun hd => hk (by simp [β, hd])
      have hb := mem_box.mp (hd1_supp c k hdne)
      refine Finset.mem_sdiff.mpr ⟨mem_box.mpr fun a => ?_, hcnotM⟩
      have := hb a; omega
  let Reach : G → G → Prop := Relation.ReflTransGen (adjIn Vout)
  have hReach_symm : ∀ {x y}, Reach x y → Reach y x := fun h => by
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head (adjIn_symm hbc) ih
  let comp (c : G) : Finset G := Vout.filter fun x => Reach c x
  have hcomp_eq : ∀ {c₁ c₂}, Reach c₁ c₂ → comp c₁ = comp c₂ := by
    intro c₁ c₂ h12
    ext x
    simp only [comp, Finset.mem_filter]
    exact ⟨fun ⟨hx, h1x⟩ => ⟨hx, (hReach_symm h12).trans h1x⟩,
           fun ⟨hx, h2x⟩ => ⟨hx, h12.trans h2x⟩⟩
  have hcomp_ne : ∀ c ∈ Vout, (comp c).Nonempty := fun c hc =>
    ⟨c, Finset.mem_filter.mpr ⟨hc, Relation.ReflTransGen.refl⟩⟩
  let pick (S : Finset G) : G := if h : S.Nonempty then h.choose else 0
  let base (c : G) : G := pick (comp c)
  have hbase_mem : ∀ c ∈ Vout, base c ∈ comp c := fun c hc => by
    simp only [base, pick, hcomp_ne c hc, ↓reduceDIte]
    exact (hcomp_ne c hc).choose_spec
  have hbase_reach : ∀ c ∈ Vout, Reach (base c) c := fun c hc =>
    hReach_symm (Finset.mem_filter.mp (hbase_mem c hc)).2
  have hbase_in : ∀ c ∈ Vout, base c ∈ Vout := fun c hc =>
    (Finset.mem_filter.mp (hbase_mem c hc)).1
  have hbase_eq : ∀ {c₁ c₂}, c₁ ∈ Vout → c₂ ∈ Vout → Reach c₁ c₂ → base c₁ = base c₂ := by
    intro c₁ c₂ _ _ h12
    exact congrArg pick (hcomp_eq h12)
  have hbase_idem : ∀ c ∈ Vout, base (base c) = base c := fun c hc =>
    hbase_eq (hbase_in c hc) hc (hbase_reach c hc)
  have hcomp_sum_β : ∀ c₀ ∈ Vout, ∑ c ∈ comp c₀, d2 β c = 0 := by
    intro c₀ _
    have hη_sum : ∑ c ∈ comp c₀, d2 ηc c = 0 := by
      apply sum_d2_eq_zero_of_closed_comp
      intro v k hne
      obtain ⟨hv, hvk⟩ := hηc_supp v k hne
      have hadj : adjIn Vout v (v - e k) := ⟨hv, hvk, k, Or.inr (sub_add_cancel v (e k)).symm⟩
      simp only [comp, Finset.mem_filter, hv, hvk, true_and]
      exact ⟨fun h => h.tail hadj, fun h => h.tail (adjIn_symm hadj)⟩
    have h2 : 2 * ∑ c ∈ comp c₀, d2 β c + ∑ c ∈ comp c₀, d2 ηc c = 0 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun c _ => hd2_rel c
    omega
  let φ_of (c : G) : G → Fin 3 → ℤ :=
    if hc : c ∈ Vout then (exists_flow_between Vout (hbase_reach c hc)).choose else fun _ _ => 0
  have hφ_supp : ∀ c ∈ Vout, ∀ v k, φ_of c v k ≠ 0 → v ∈ Vout ∧ v - e k ∈ Vout := by
    intro c hc v k hne
    simp only [φ_of, hc, ↓reduceDIte] at hne
    exact (exists_flow_between Vout (hbase_reach c hc)).choose_spec.1 v k hne
  have hφ_d2 : ∀ c ∈ Vout, ∀ x,
      d2 (φ_of c) x = (if x = c then 1 else 0) - (if x = base c then 1 else 0) := by
    intro c hc x
    simp only [φ_of, hc, ↓reduceDIte]
    exact (exists_flow_between Vout (hbase_reach c hc)).choose_spec.2 x
  let ζ (v : G) (k : Fin 3) : ℤ := ∑ c ∈ Vout, d2 β c * φ_of c v k
  have hζ_d2 : ∀ x : G, d2 ζ x = d2 β x := by
    intro x
    change d2 (fun v k => ∑ c ∈ Vout, d2 β c * φ_of c v k) x = d2 β x
    rw [d2_sum]
    have hterm : ∀ c ∈ Vout, d2 (fun v k => d2 β c * φ_of c v k) x =
        (if x = c then d2 β c else 0) - (if x = base c then d2 β c else 0) := by
      intro c hc
      rw [d2_smul, hφ_d2 c hc x]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
    have hfirst : (∑ c ∈ Vout, if x = c then d2 β c else 0) = d2 β x := by
      by_cases hx : x ∈ Vout
      · simp [hx]
      · have h0 : d2 β x = 0 := by
          by_contra hne
          exact hx (hd2β_supp x hne)
        rw [h0]
        apply Finset.sum_eq_zero
        intro c hc
        have : x ≠ c := fun h => hx (h ▸ hc)
        simp [this]
    have hsecond : (∑ c ∈ Vout, if x = base c then d2 β c else 0) = 0 := by
      by_cases hx : x ∈ Vout ∧ base x = x
      · have hfilt : Vout.filter (fun c => x = base c) = comp x := by
          ext c
          simp only [Finset.mem_filter, comp]
          constructor
          · rintro ⟨hc, hbc⟩
            exact ⟨hc, hbc ▸ hbase_reach c hc⟩
          · rintro ⟨hc, hxc⟩
            exact ⟨hc, (hx.2.symm.trans (hbase_eq hx.1 hc hxc))⟩
        rw [← Finset.sum_filter, hfilt]
        exact hcomp_sum_β x hx.1
      · apply Finset.sum_eq_zero
        intro c hc
        have hne : x ≠ base c := by
          intro hbc
          apply hx
          have hxV : x ∈ Vout := hbc ▸ hbase_in c hc
          exact ⟨hxV, by rw [hbc, hbase_idem c hc]⟩
        simp [hne]
    linarith
  let βhat (v : G) (k : Fin 3) : ℤ := β v k - ζ v k
  have hβhat_closed : ∀ c : G, d2 βhat c = 0 := by
    intro c
    change d2 (fun v k => β v k - ζ v k) c = 0
    rw [d2_sub, hζ_d2 c, sub_self]
  have hβhat_eq_β : ∀ v k, isFace v k → βhat v k = β v k := by
    intro v k hfk
    have hζ0 : ζ v k = 0 := by
      apply Finset.sum_eq_zero
      intro c hc
      have h0 : φ_of c v k = 0 := by
        by_contra hne
        obtain ⟨hv, hvk⟩ := hφ_supp c hc v k hne
        rcases hfk with h | h
        · exact (Finset.mem_sdiff.mp hv).2 h
        · exact (Finset.mem_sdiff.mp hvk).2 h
      rw [h0, mul_zero]
    simp [βhat, hζ0]
  have hβhat_supp : ∀ v k, βhat v k ≠ 0 → v 2 ≤ N := by
    intro v k hne
    by_cases hβ : β v k ≠ 0
    · have hdne : d1 α v k ≠ 0 := fun hd => hβ (by simp [β, hd])
      have hb := mem_box.mp (hd1_supp v k hdne) 2
      omega
    · push Not at hβ
      have hζne : ζ v k ≠ 0 := by intro h0; exact hne (by simp [βhat, hβ, h0])
      obtain ⟨c, hc, hcz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hζne
      have hφne : φ_of c v k ≠ 0 := right_ne_zero_of_mul hcz
      have hv := (hφ_supp c hc v k hφne).1
      exact (mem_box.mp (Finset.mem_sdiff.mp hv).1 2).2
  obtain ⟨γ, hγ⟩ := exists_primitive_d1 N βhat hβhat_closed hβhat_supp
  refine ⟨γ, fun v k hfk => ?_⟩
  rw [hγ v k, hβhat_eq_β v k hfk]
  have h := hdecomp v k
  simp only [ηc, isFace, hfk, ↓reduceIte, add_zero] at h
  exact h

/- Cubes, trilinear interpolation, and local potentials -/

private def cubeQ (δ : ℝ) (c : G) : Set (Fin 3 → ℝ) :=
  {p | ∀ a : Fin 3, δ * (c a : ℝ) ≤ p a ∧ p a ≤ δ * ((c a : ℝ) + 1)}

private lemma isClosed_cubeQ (δ : ℝ) (c : G) : IsClosed (cubeQ δ c) := by
  have : cubeQ δ c = ⋂ a : Fin 3,
      ({p : Fin 3 → ℝ | δ * (c a : ℝ) ≤ p a} ∩ {p : Fin 3 → ℝ | p a ≤ δ * ((c a : ℝ) + 1)}) := by
    ext p; simp [cubeQ]
  rw [this]
  refine isClosed_iInter fun a => (isClosed_le continuous_const (continuous_apply a)).inter
    (isClosed_le (continuous_apply a) continuous_const)

private noncomputable def wtAt (δ : ℝ) (c v : G) (p : Fin 3 → ℝ) : ℝ :=
  ∏ a : Fin 3, if v a = c a then 1 - (p a - δ * (c a : ℝ)) / δ
    else if v a = c a + 1 then (p a - δ * (c a : ℝ)) / δ else 0

private lemma continuous_wtAt (δ : ℝ) (c v : G) : Continuous (wtAt δ c v) := by
  unfold wtAt
  refine continuous_finsetProd _ fun a _ => ?_
  split_ifs <;> fun_prop

private lemma sum_wtAt (δ : ℝ) (c : G) (p : Fin 3 → ℝ) :
    ∑ v ∈ corners c, wtAt δ c v p = 1 := by
  classical
  let w (a : Fin 3) (z : ℤ) : ℝ :=
    if z = c a then 1 - (p a - δ * (c a : ℝ)) / δ
    else if z = c a + 1 then (p a - δ * (c a : ℝ)) / δ else 0
  change ∑ v ∈ Fintype.piFinset (fun a : Fin 3 => ({c a, c a + 1} : Finset ℤ)), ∏ a, w a (v a) = 1
  rw [← Finset.prod_univ_sum]
  apply Finset.prod_eq_one
  intro a _
  have hne : c a ≠ c a + 1 := by omega
  rw [Finset.sum_pair hne]
  simp only [w, ↓reduceIte, hne.symm]
  ring

private lemma wtAt_eq_of_mem_inter {δ : ℝ} (hδ : 0 < δ) {c₁ c₂ : G} {p : Fin 3 → ℝ}
    (hp₁ : p ∈ cubeQ δ c₁) (hp₂ : p ∈ cubeQ δ c₂) (v : G) :
    wtAt δ c₁ v p = wtAt δ c₂ v p := by
  unfold wtAt
  apply Finset.prod_congr rfl
  intro a _
  have h1 := hp₁ a
  have h2 := hp₂ a
  have hle1 : c₁ a ≤ c₂ a + 1 := by
    have : (c₁ a : ℝ) ≤ (c₂ a : ℝ) + 1 := by nlinarith
    exact_mod_cast this
  have hle2 : c₂ a ≤ c₁ a + 1 := by
    have : (c₂ a : ℝ) ≤ (c₁ a : ℝ) + 1 := by nlinarith
    exact_mod_cast this
  have hcases : c₂ a = c₁ a ∨ c₂ a = c₁ a + 1 ∨ c₁ a = c₂ a + 1 := by omega
  rcases hcases with h | h | h
  · rw [h]
  · have hp : p a = δ * ((c₁ a : ℝ) + 1) := by
      have hc : (c₂ a : ℝ) = (c₁ a : ℝ) + 1 := by exact_mod_cast h
      nlinarith
    have hd1 : (p a - δ * (c₁ a : ℝ)) / δ = 1 := by rw [hp]; field_simp [hδ.ne']; ring
    have hd2 : (p a - δ * (c₂ a : ℝ)) / δ = 0 := by
      have hc : (c₂ a : ℝ) = (c₁ a : ℝ) + 1 := by exact_mod_cast h
      rw [hp, hc]; field_simp [hδ.ne']; ring
    rw [hd1, hd2, h]
    by_cases hv : v a = c₁ a + 1
    · simp [hv]
    · by_cases hv0 : v a = c₁ a
      · simp [hv0, hv]
      · by_cases hv2 : v a = c₁ a + 1 + 1 <;> simp [hv, hv0, hv2]
  · have hp : p a = δ * ((c₂ a : ℝ) + 1) := by
      have hc : (c₁ a : ℝ) = (c₂ a : ℝ) + 1 := by exact_mod_cast h
      nlinarith
    have hd1 : (p a - δ * (c₁ a : ℝ)) / δ = 0 := by
      have hc : (c₁ a : ℝ) = (c₂ a : ℝ) + 1 := by exact_mod_cast h
      rw [hp, hc]; field_simp [hδ.ne']; ring
    have hd2 : (p a - δ * (c₂ a : ℝ)) / δ = 1 := by rw [hp]; field_simp [hδ.ne']; ring
    rw [hd1, hd2, h]
    by_cases hv : v a = c₂ a + 1
    · simp [hv]
    · by_cases hv0 : v a = c₂ a
      · simp [hv0, hv]
      · by_cases hv2 : v a = c₂ a + 1 + 1 <;> simp [hv, hv0, hv2]

private lemma wtAt_eq_zero_of_not_mem_corners (δ : ℝ) (c v : G) (p : Fin 3 → ℝ)
    (hv : v ∉ corners c) : wtAt δ c v p = 0 := by
  rw [mem_corners] at hv
  push Not at hv
  obtain ⟨a, ha1, ha2⟩ := hv
  unfold wtAt
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  simp [ha1, ha2]

private def stepX (c v : G) : G := Function.update c 0 (v 0)
private def stepXY (c v : G) : G := Function.update (stepX c v) 1 (v 1)

private def phiC (ω : G → Fin 3 → ℝ) (c v : G) : ℝ :=
  (if v 0 = c 0 + 1 then ω c 0 else 0) +
  (if v 1 = c 1 + 1 then ω (stepX c v) 1 else 0) +
  (if v 2 = c 2 + 1 then ω (stepXY c v) 2 else 0)

private lemma phiC_eval (ω : G → Fin 3 → ℝ) (c : G) :
    phiC ω c c = 0 ∧
    phiC ω c (c + e 0) = ω c 0 ∧
    phiC ω c (c + e 1) = ω c 1 ∧
    phiC ω c (c + e 2) = ω c 2 ∧
    phiC ω c (c + e 0 + e 1) = ω c 0 + ω (c + e 0) 1 ∧
    phiC ω c (c + e 0 + e 2) = ω c 0 + ω (c + e 0) 2 ∧
    phiC ω c (c + e 1 + e 2) = ω c 1 + ω (c + e 1) 2 ∧
    phiC ω c (c + e 0 + e 1 + e 2) = ω c 0 + ω (c + e 0) 1 + ω (c + e 0 + e 1) 2 := by
  have hne0 : c 0 ≠ c 0 + 1 := by omega
  have hne1 : c 1 ≠ c 1 + 1 := by omega
  have hne2 : c 2 ≠ c 2 + 1 := by omega
  have sx0 : stepX c (c + e 1) = c := by funext a; fin_cases a <;> simp [stepX, e]
  have sx1 : stepX c (c + e 0 + e 1) = c + e 0 := by funext a; fin_cases a <;> simp [stepX, e]
  have sx2 : stepX c (c + e 1 + e 2) = c := by funext a; fin_cases a <;> simp [stepX, e]
  have sx3 : stepX c (c + e 0 + e 1 + e 2) = c + e 0 := by funext a; fin_cases a <;> simp [stepX, e]
  have sxy0 : stepXY c (c + e 2) = c := by funext a; fin_cases a <;> simp [stepXY, stepX, e]
  have sxy1 : stepXY c (c + e 0 + e 2) = c + e 0 := by funext a; fin_cases a <;> simp [stepXY, stepX, e]
  have sxy2 : stepXY c (c + e 1 + e 2) = c + e 1 := by funext a; fin_cases a <;> simp [stepXY, stepX, e]
  have sxy3 : stepXY c (c + e 0 + e 1 + e 2) = c + e 0 + e 1 := by
    funext a; fin_cases a <;> simp [stepXY, stepX, e]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [phiC, hne0, hne1, hne2]
  · simp [phiC, e, hne1, hne2]
  · simp only [phiC, sx0]; simp [e, hne0, hne2]
  · simp only [phiC, sxy0]; simp [e, hne0, hne1]
  · simp only [phiC, sx1]; simp [e, hne2]
  · simp only [phiC, sxy1]; simp [e, hne1]
  · simp only [phiC, sx2, sxy2]; simp [e, hne0]
  · simp only [phiC, sx3, sxy3]; simp [e]

private lemma phiC_edge (ω : G → Fin 3 → ℝ) (c : G)
    (hflat : ∀ (w : G) (k : Fin 3), (w = c ∨ w = c + e k) →
      ω w (ax1 k) + ω (w + e (ax1 k)) (ax2 k) - ω (w + e (ax2 k)) (ax1 k) - ω w (ax2 k) = 0)
    (u : G) (hu : u ∈ corners c) (d : Fin 3) (hud : u + e d ∈ corners c) :
    phiC ω c (u + e d) - phiC ω c u = ω u d := by
  obtain ⟨h000, h100, h010, h001, h110, h101, h011, h111⟩ := phiC_eval ω c
  have hf0a := hflat c 0 (Or.inl rfl)
  have hf0b := hflat (c + e 0) 0 (Or.inr rfl)
  have hf1a := hflat c 1 (Or.inl rfl)
  have hf1b := hflat (c + e 1) 1 (Or.inr rfl)
  have hf2a := hflat c 2 (Or.inl rfl)
  have hf2b := hflat (c + e 2) 2 (Or.inr rfl)
  simp only [ax1, ax2] at hf0a hf0b hf1a hf1b hf2a hf2b
  have h01 : c + e 0 + e 1 = c + e 1 + e 0 := add_right_comm c (e 0) (e 1)
  have h02 : c + e 0 + e 2 = c + e 2 + e 0 := add_right_comm c (e 0) (e 2)
  have h12 : c + e 1 + e 2 = c + e 2 + e 1 := add_right_comm c (e 1) (e 2)
  rw [mem_corners] at hu hud
  have hu0 := hu 0; have hu1 := hu 1; have hu2 := hu 2
  have hud0 := hud 0; have hud1 := hud 1; have hud2 := hud 2
  fin_cases d
  · change phiC ω c (u + e 0) - phiC ω c u = ω u 0
    have huc : u 0 = c 0 := by
      rcases hu0 with h | h
      · exact h
      · simp [e] at hud0; omega
    rcases hu1 with h1 | h1 <;> rcases hu2 with h2 | h2
    · have hueq : u = c := by funext a; fin_cases a <;> assumption
      rw [hueq, h000, h100]; ring
    · have hueq : u = c + e 2 := by funext a; fin_cases a <;> simp [e, huc, h1, h2]
      rw [hueq, ← h02, h001, h101]; linarith
    · have hueq : u = c + e 1 := by funext a; fin_cases a <;> simp [e, huc, h1, h2]
      rw [hueq, ← h01, h010, h110]; linarith
    · have hueq : u = c + e 1 + e 2 := by funext a; fin_cases a <;> simp [e, huc, h1, h2]
      have hsum : c + e 1 + e 2 + e 0 = c + e 0 + e 1 + e 2 := by
        rw [add_right_comm (c + e 1) (e 2) (e 0), ← h01]
      rw [hueq, hsum, h011, h111]
      rw [← h01] at hf1b
      linarith
  · change phiC ω c (u + e 1) - phiC ω c u = ω u 1
    have huc : u 1 = c 1 := by
      rcases hu1 with h | h
      · exact h
      · simp [e] at hud1; omega
    rcases hu0 with h0 | h0 <;> rcases hu2 with h2 | h2
    · have hueq : u = c := by funext a; fin_cases a <;> assumption
      rw [hueq, h000, h010]; ring
    · have hueq : u = c + e 2 := by funext a; fin_cases a <;> simp [e, h0, huc, h2]
      rw [hueq, ← h12, h001, h011]; linarith
    · have hueq : u = c + e 0 := by funext a; fin_cases a <;> simp [e, h0, huc, h2]
      rw [hueq, h100, h110]; ring
    · have hueq : u = c + e 0 + e 2 := by funext a; fin_cases a <;> simp [e, h0, huc, h2]
      have hsum : c + e 0 + e 2 + e 1 = c + e 0 + e 1 + e 2 :=
        add_right_comm (c + e 0) (e 2) (e 1)
      rw [hueq, hsum, h101, h111]; linarith
  · change phiC ω c (u + e 2) - phiC ω c u = ω u 2
    have huc : u 2 = c 2 := by
      rcases hu2 with h | h
      · exact h
      · simp [e] at hud2; omega
    rcases hu0 with h0 | h0 <;> rcases hu1 with h1 | h1
    · have hueq : u = c := by funext a; fin_cases a <;> assumption
      rw [hueq, h000, h001]; ring
    · have hueq : u = c + e 1 := by funext a; fin_cases a <;> simp [e, h0, h1, huc]
      rw [hueq, h010, h011]; ring
    · have hueq : u = c + e 0 := by funext a; fin_cases a <;> simp [e, h0, h1, huc]
      rw [hueq, h100, h101]; ring
    · have hueq : u = c + e 0 + e 1 := by funext a; fin_cases a <;> simp [e, h0, h1, huc]
      rw [hueq, h110, h111]; ring

private lemma phiC_diff_const_on_inter (ω : G → Fin 3 → ℝ) {c₁ c₂ : G}
    (hflat₁ : ∀ (w : G) (k : Fin 3), (w = c₁ ∨ w = c₁ + e k) →
      ω w (ax1 k) + ω (w + e (ax1 k)) (ax2 k) - ω (w + e (ax2 k)) (ax1 k) - ω w (ax2 k) = 0)
    (hflat₂ : ∀ (w : G) (k : Fin 3), (w = c₂ ∨ w = c₂ + e k) →
      ω w (ax1 k) + ω (w + e (ax1 k)) (ax2 k) - ω (w + e (ax2 k)) (ax1 k) - ω w (ax2 k) = 0)
    {v₀ v : G} (hv₀₁ : v₀ ∈ corners c₁) (hv₀₂ : v₀ ∈ corners c₂)
    (hv₁ : v ∈ corners c₁) (hv₂ : v ∈ corners c₂) :
    phiC ω c₁ v - phiC ω c₂ v = phiC ω c₁ v₀ - phiC ω c₂ v₀ := by
  have hstep : ∀ (u : G) (d : Fin 3),
      u ∈ corners c₁ → u ∈ corners c₂ → u + e d ∈ corners c₁ → u + e d ∈ corners c₂ →
      phiC ω c₁ (u + e d) - phiC ω c₂ (u + e d) = phiC ω c₁ u - phiC ω c₂ u := by
    intro u d hu1 hu2 hud1 hud2
    have h1 := phiC_edge ω c₁ hflat₁ u hu1 d hud1
    have h2 := phiC_edge ω c₂ hflat₂ u hu2 d hud2
    linarith
  have hmove : ∀ (u : G) (d : Fin 3) (w : G),
      (∀ a ≠ d, w a = u a) →
      u ∈ corners c₁ → u ∈ corners c₂ → w ∈ corners c₁ → w ∈ corners c₂ →
      phiC ω c₁ w - phiC ω c₂ w = phiC ω c₁ u - phiC ω c₂ u := by
    intro u d w hother hu1 hu2 hw1 hw2
    have hu1d := (mem_corners.mp hu1) d
    have hw1d := (mem_corners.mp hw1) d
    by_cases hsame : w d = u d
    · have : w = u := by
        funext a
        by_cases ha : a = d
        · subst ha; exact hsame
        · exact hother a ha
      rw [this]
    · rcases hu1d with hu1d | hu1d <;> rcases hw1d with hw1d | hw1d
      · omega
      · have hw_eq : w = u + e d := by
          funext a
          by_cases ha : a = d
          · subst ha; simp [e]; omega
          · simp [e, ha, hother a ha]
        rw [hw_eq]
        exact hstep u d hu1 hu2 (hw_eq ▸ hw1) (hw_eq ▸ hw2)
      · have hu_eq : u = w + e d := by
          funext a
          by_cases ha : a = d
          · subst ha; simp [e]; omega
          · simp [e, ha, (hother a ha).symm]
        rw [hu_eq]
        exact (hstep w d hw1 hw2 (hu_eq ▸ hu1) (hu_eq ▸ hu2)).symm
      · omega
  let m1 : G := Function.update v₀ 0 (v 0)
  let m2 : G := Function.update m1 1 (v 1)
  have hm1_1 : m1 ∈ corners c₁ := mem_corners.mpr fun a => by
    fin_cases a
    · simpa [m1] using mem_corners.mp hv₁ 0
    · simpa [m1] using mem_corners.mp hv₀₁ 1
    · simpa [m1] using mem_corners.mp hv₀₁ 2
  have hm1_2 : m1 ∈ corners c₂ := mem_corners.mpr fun a => by
    fin_cases a
    · simpa [m1] using mem_corners.mp hv₂ 0
    · simpa [m1] using mem_corners.mp hv₀₂ 1
    · simpa [m1] using mem_corners.mp hv₀₂ 2
  have hm2_1 : m2 ∈ corners c₁ := mem_corners.mpr fun a => by
    fin_cases a
    · simpa [m2, m1] using mem_corners.mp hv₁ 0
    · simpa [m2] using mem_corners.mp hv₁ 1
    · simpa [m2, m1] using mem_corners.mp hv₀₁ 2
  have hm2_2 : m2 ∈ corners c₂ := mem_corners.mpr fun a => by
    fin_cases a
    · simpa [m2, m1] using mem_corners.mp hv₂ 0
    · simpa [m2] using mem_corners.mp hv₂ 1
    · simpa [m2, m1] using mem_corners.mp hv₀₂ 2
  have h1 := hmove v₀ 0 m1 (fun a ha => by simp [m1, ha]) hv₀₁ hv₀₂ hm1_1 hm1_2
  have h2 := hmove m1 1 m2 (fun a ha => by simp [m2, ha]) hm1_1 hm1_2 hm2_1 hm2_2
  have h3 := hmove m2 2 v (fun a ha => by fin_cases a <;> simp [m2, m1] at ha ⊢) hm2_1 hm2_2 hv₁ hv₂
  linarith

private lemma cexp_two_pi_I_int (m : ℤ) : Complex.exp (2 * Real.pi * Complex.I * (m : ℂ)) = 1 := by
  have h : 2 * Real.pi * Complex.I * (m : ℂ) = (m : ℂ) * (2 * Real.pi * Complex.I) := by ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

private lemma cexp_pi_I_zero_or_one (a : ℤ) (ha : a = 0 ∨ a = 1) :
    Complex.exp (2 * Real.pi * Complex.I * ((a : ℝ) / 2 : ℝ)) =
      if a = 1 then -1 else 1 := by
  rcases ha with rfl | rfl
  · simp
  · have h : (2 : ℂ) * Real.pi * Complex.I * (((1 : ℤ) : ℝ) / 2 : ℝ) = Real.pi * Complex.I := by
      push_cast; ring
    rw [h, Complex.exp_pi_mul_I]
    simp

private lemma overlap_combine {t1 t2 p1 p2 s1 s2 r1 r2 r0 x : ℝ}
    (ht : t1 - t2 = p1 - p2)
    (he1 : Complex.exp (2 * Real.pi * Complex.I * (p1 : ℂ)) = (s1 : ℂ))
    (he2 : Complex.exp (2 * Real.pi * Complex.I * (p2 : ℂ)) = (s2 : ℂ))
    (hs1 : s1 * r1 = r0) (hs2 : s2 * r2 = r0) (hs2sq : s2 * s2 = 1) :
    Complex.exp (2 * Real.pi * Complex.I * (t1 : ℂ)) * ((r1 * x : ℝ) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I * (t2 : ℂ)) * ((r2 * x : ℝ) : ℂ) := by
  have ht' : (t1 : ℂ) = (t2 : ℂ) + (p1 : ℂ) - (p2 : ℂ) := by
    exact_mod_cast (show t1 = t2 + p1 - p2 by linarith)
  have hmul : (2 : ℂ) * Real.pi * Complex.I * (t1 : ℂ) =
      2 * Real.pi * Complex.I * (t2 : ℂ) +
      2 * Real.pi * Complex.I * (p1 : ℂ) +
      -(2 * Real.pi * Complex.I * (p2 : ℂ)) := by rw [ht']; ring
  rw [hmul, Complex.exp_add, Complex.exp_add, Complex.exp_neg, he1, he2]
  have hinv : (s2 : ℂ)⁻¹ = (s2 : ℂ) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← Complex.ofReal_mul, hs2sq, Complex.ofReal_one]
  rw [hinv]
  have hr : s1 * s2 * r1 = r2 := by
    calc s1 * s2 * r1 = s2 * (s1 * r1) := by ring
      _ = s2 * r0 := by rw [hs1]
      _ = s2 * (s2 * r2) := by rw [hs2]
      _ = (s2 * s2) * r2 := by ring
      _ = r2 := by rw [hs2sq, one_mul]
  have hrc : (s1 : ℂ) * (s2 : ℂ) * (r1 : ℂ) = (r2 : ℂ) := by
    exact_mod_cast hr
  rw [Complex.ofReal_mul, Complex.ofReal_mul]
  calc Complex.exp (2 * Real.pi * Complex.I * (t2 : ℂ)) * (s1 : ℂ) * (s2 : ℂ) * ((r1 : ℂ) * (x : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I * (t2 : ℂ)) * (((s1 : ℂ) * (s2 : ℂ) * (r1 : ℂ)) * (x : ℂ)) := by ring
    _ = Complex.exp (2 * Real.pi * Complex.I * (t2 : ℂ)) * ((r2 : ℂ) * (x : ℂ)) := by rw [hrc]

private theorem H1_pi (K : Set (Fin 3 → ℝ)) (hK : IsCompact K)
    (P : K → Fin 3 → Fin 3 → ℝ) (hP : Continuous P)
    (hproj : ∀ k, ∃ x : Fin 3 → ℝ, IsUnit3 x ∧ ∀ i j, P k i j = x i * x j) :
    ∃ s : K → Fin 3 → ℂ, Continuous s ∧ ∀ k, s k ≠ 0 ∧
      ∀ i, ∑ j, (P k i j : ℂ) * s k j = s k i := by
  classical
  by_cases hKe : K = ∅
  · refine ⟨fun k => False.elim (by simpa [hKe] using k.2), ?_, fun k => False.elim (by simpa [hKe] using k.2)⟩
    rw [continuous_iff_isClosed]
    intro Z _
    have hempty : (fun k : K => False.elim (by simpa [hKe] using k.2) : K → Fin 3 → ℂ) ⁻¹' Z = ∅ :=
      Set.eq_empty_of_forall_notMem fun k _ => by simpa [hKe] using k.2
    rw [hempty]; exact isClosed_empty
  have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKe
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hPu : UniformContinuous P := CompactSpace.uniformContinuous_of_continuous hP
  obtain ⟨η, hη, hηP⟩ := Metric.uniformContinuous_iff.mp hPu (1 / 6) (by norm_num)
  let δ : ℝ := η / 4
  have hδ_eq : δ = η / 4 := rfl
  have hδ : 0 < δ := by positivity
  obtain ⟨B, hB⟩ := hK.isBounded.subset_closedBall (0 : Fin 3 → ℝ)
  have hBcoord : ∀ p ∈ K, ∀ a : Fin 3, |p a| ≤ B := by
    intro p hp a
    have h1 : dist p 0 ≤ B := Metric.mem_closedBall.mp (hB hp)
    have h2 : dist (p a) (0 : ℝ) ≤ dist p 0 := dist_le_pi_dist p 0 a
    simpa [Real.dist_eq] using h2.trans h1
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (max 0 B / δ + 5)
  let N : ℤ := (N₀ : ℤ)
  have hN_cast : (N : ℝ) = (N₀ : ℝ) := by simp [N]
  have hKbox : ∀ c : G, (cubeQ δ c ∩ K).Nonempty → c ∈ box (N - 3) := by
    intro c ⟨p, hpQ, hpK⟩
    rw [mem_box]
    intro a
    have hpa := hBcoord p hpK a
    have hpa' : |p a| ≤ max 0 B := hpa.trans (le_max_right _ _)
    have hqa := hpQ a
    have hle1 : (c a : ℝ) ≤ (N : ℝ) - 3 := by
      have h1 : δ * (c a : ℝ) ≤ max 0 B := hqa.1.trans ((le_abs_self _).trans hpa')
      have h2 : (c a : ℝ) ≤ max 0 B / δ := (le_div_iff₀' hδ).mpr h1
      linarith [hN₀, hN_cast]
    have hle2 : -((N : ℝ) - 3) ≤ (c a : ℝ) := by
      have h1 : -max 0 B ≤ δ * ((c a : ℝ) + 1) :=
        (by linarith [neg_abs_le (p a)] : -max 0 B ≤ p a).trans hqa.2
      have h2 : -(max 0 B / δ) ≤ (c a : ℝ) + 1 := by
        rw [← neg_div, div_le_iff₀' hδ]; linarith
      linarith [hN₀, hN_cast]
    exact ⟨by exact_mod_cast hle2, by exact_mod_cast hle1⟩
  let M : Finset G := (box (N - 3)).filter fun c => (cubeQ δ c ∩ K).Nonempty
  have hM_iff : ∀ c : G, c ∈ M ↔ (cubeQ δ c ∩ K).Nonempty := by
    intro c
    simp only [M, Finset.mem_filter]
    exact ⟨And.right, fun h => ⟨hKbox c h, h⟩⟩
  have hM_sub : ∀ c ∈ M, c ∈ box (N - 3) := fun c hc => (Finset.mem_filter.mp hc).1
  let VM : Finset G := M.biUnion corners
  have hVM_witness : ∀ v ∈ VM, ∃ c ∈ M, v ∈ corners c ∧ ∃ p ∈ K, p ∈ cubeQ δ c := by
    intro v hv
    obtain ⟨c, hcM, hvc⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨p, hpQ, hpK⟩ := (hM_iff c).mp hcM
    exact ⟨c, hcM, hvc, p, hpK, hpQ⟩
  let kv_val (v : G) : K :=
    if hv : v ∈ VM then
      let h := hVM_witness v hv
      ⟨h.choose_spec.2.2.choose, h.choose_spec.2.2.choose_spec.1⟩
    else ⟨hKne.choose, hKne.choose_spec⟩
  have hkv_close : ∀ v ∈ VM, ∀ a : Fin 3, |(kv_val v).val a - δ * (v a : ℝ)| ≤ δ := by
    intro v hv a
    have h := hVM_witness v hv
    let c := h.choose
    have hvc : v ∈ corners c := h.choose_spec.2.1
    have hpQ : (kv_val v).val ∈ cubeQ δ c := by
      simpa [kv_val, hv, c] using h.choose_spec.2.2.choose_spec.2
    have hqa := hpQ a
    rcases mem_corners.mp hvc a with hva | hva
    · rw [hva, abs_le]; constructor <;> linarith
    · rw [hva, Int.cast_add, Int.cast_one, abs_le]; constructor <;> linarith
  let repX (k : K) : Fin 3 → ℝ := (hproj k).choose
  have hrep_unit (k : K) : IsUnit3 (repX k) := (hproj k).choose_spec.1
  have hrep_proj (k : K) (i j : Fin 3) : P k i j = repX k i * repX k j := (hproj k).choose_spec.2 i j
  let xv (v : G) : Fin 3 → ℝ := repX (kv_val v)
  have hxv_unit (v : G) : IsUnit3 (xv v) := hrep_unit _
  have hpair_corners : ∀ c ∈ M, ∀ u ∈ corners c, ∀ v ∈ corners c,
      (7 : ℝ) / 8 < (dot3 (xv u) (xv v)) ^ 2 := by
    intro c hcM u hu v hv
    have huVM : u ∈ VM := Finset.mem_biUnion.mpr ⟨c, hcM, hu⟩
    have hvVM : v ∈ VM := Finset.mem_biUnion.mpr ⟨c, hcM, hv⟩
    have hdist : dist (kv_val u) (kv_val v) < η := by
      change dist (kv_val u).val (kv_val v).val < η
      rw [dist_pi_lt_iff hη]
      intro a
      rw [Real.dist_eq]
      have h1 := hkv_close u huVM a
      have h2 := hkv_close v hvVM a
      have h3 : |(u a : ℝ) - (v a : ℝ)| ≤ 1 := by
        rcases mem_corners.mp hu a with hua | hua <;> rcases mem_corners.mp hv a with hva | hva <;>
          simp [hua, hva]
      have h3' : |δ * (u a : ℝ) - δ * (v a : ℝ)| ≤ δ := by
        rw [← mul_sub, abs_mul, abs_of_pos hδ]
        nlinarith
      have htri : |(kv_val u).val a - (kv_val v).val a| ≤
          |(kv_val u).val a - δ * (u a : ℝ)| + |δ * (u a : ℝ) - δ * (v a : ℝ)| +
            |δ * (v a : ℝ) - (kv_val v).val a| := by
        calc |(kv_val u).val a - (kv_val v).val a|
            = |((kv_val u).val a - δ * (u a : ℝ)) + (δ * (u a : ℝ) - δ * (v a : ℝ)) +
                (δ * (v a : ℝ) - (kv_val v).val a)| := by ring_nf
          _ ≤ |((kv_val u).val a - δ * (u a : ℝ)) + (δ * (u a : ℝ) - δ * (v a : ℝ))| +
                |δ * (v a : ℝ) - (kv_val v).val a| := abs_add_le _ _
          _ ≤ _ := by linarith [abs_add_le ((kv_val u).val a - δ * (u a : ℝ)) (δ * (u a : ℝ) - δ * (v a : ℝ))]
      rw [abs_sub_comm (δ * (v a : ℝ))] at htri
      linarith [hδ_eq]
    have hPclose := hηP hdist
    apply dot_sq_gt_of_proj_close (hxv_unit u) (hxv_unit v)
    intro i j
    have hij : dist (P (kv_val u) i j) (P (kv_val v) i j) < 1 / 6 :=
      (dist_le_pi_dist _ _ j).trans_lt ((dist_le_pi_dist _ _ i).trans_lt hPclose)
    simpa [Real.dist_eq, hrep_proj] using hij
  have hpair_pt_corner : ∀ c ∈ M, ∀ k : K, k.val ∈ cubeQ δ c → ∀ v ∈ corners c,
      (7 : ℝ) / 8 < (dot3 (repX k) (xv v)) ^ 2 := by
    intro c hcM k hkQ v hv
    have hvVM : v ∈ VM := Finset.mem_biUnion.mpr ⟨c, hcM, hv⟩
    have hdist : dist k (kv_val v) < η := by
      change dist k.val (kv_val v).val < η
      rw [dist_pi_lt_iff hη]
      intro a
      rw [Real.dist_eq]
      have h2 := hkv_close v hvVM a
      have h1 : |k.val a - δ * (v a : ℝ)| ≤ δ := by
        have hqa := hkQ a
        rcases mem_corners.mp hv a with hva | hva
        · rw [hva, abs_le]; constructor <;> linarith
        · rw [hva, Int.cast_add, Int.cast_one, abs_le]; constructor <;> linarith
      have htri : |k.val a - (kv_val v).val a| ≤
          |k.val a - δ * (v a : ℝ)| + |δ * (v a : ℝ) - (kv_val v).val a| := by
        calc |k.val a - (kv_val v).val a|
            = |(k.val a - δ * (v a : ℝ)) + (δ * (v a : ℝ) - (kv_val v).val a)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      rw [abs_sub_comm (δ * (v a : ℝ))] at htri
      linarith [hδ_eq]
    have hPclose := hηP hdist
    apply dot_sq_gt_of_proj_close (hrep_unit k) (hxv_unit v)
    intro i j
    have hij : dist (P k i j) (P (kv_val v) i j) < 1 / 6 :=
      (dist_le_pi_dist _ _ j).trans_lt ((dist_le_pi_dist _ _ i).trans_lt hPclose)
    simpa [Real.dist_eq, hrep_proj] using hij
  let isEdgeOfM (v : G) (d : Fin 3) : Prop := ∃ c ∈ M, v ∈ corners c ∧ v + e d ∈ corners c
  let α (v : G) (d : Fin 3) : ℤ :=
    if isEdgeOfM v d then (if dot3 (xv v) (xv (v + e d)) < 0 then 1 else 0) else 0
  have hface_corners : ∀ v k, (v ∈ M ∨ v - e k ∈ M) →
      ∃ c ∈ M, v ∈ corners c ∧ v + e (ax1 k) ∈ corners c ∧
        v + e (ax2 k) ∈ corners c ∧ v + e (ax1 k) + e (ax2 k) ∈ corners c := by
    intro v k hfk
    rcases hfk with hvM | hvkM
    · refine ⟨v, hvM, self_mem_corners v, ?_, ?_, ?_⟩ <;>
      · rw [mem_corners]; intro a; fin_cases k <;> fin_cases a <;> simp [ax1, ax2, e]
    · refine ⟨v - e k, hvkM, ?_, ?_, ?_, ?_⟩ <;>
      · rw [mem_corners]; intro a; fin_cases k <;> fin_cases a <;> simp [ax1, ax2, e]
  have hd1_even : ∀ v k, (v ∈ M ∨ v - e k ∈ M) → 2 ∣ d1 α v k := by
    intro v k hfk
    obtain ⟨c, hcM, hv0, hv1, hv2, hv3⟩ := hface_corners v k hfk
    have he1 : isEdgeOfM v (ax1 k) := ⟨c, hcM, hv0, hv1⟩
    have he2 : isEdgeOfM (v + e (ax1 k)) (ax2 k) := ⟨c, hcM, hv1, hv3⟩
    have hv3' : v + e (ax2 k) + e (ax1 k) = v + e (ax1 k) + e (ax2 k) :=
      add_right_comm v (e (ax2 k)) (e (ax1 k))
    have he3 : isEdgeOfM (v + e (ax2 k)) (ax1 k) := ⟨c, hcM, hv2, hv3'.symm ▸ hv3⟩
    have he4 : isEdgeOfM v (ax2 k) := ⟨c, hcM, hv0, hv2⟩
    have hs1 := sgn_consistent (hxv_unit v) (hxv_unit (v + e (ax1 k)))
      (hxv_unit (v + e (ax1 k) + e (ax2 k)))
      (hpair_corners c hcM _ hv0 _ hv1) (hpair_corners c hcM _ hv1 _ hv3)
      (hpair_corners c hcM _ hv0 _ hv3)
    have hs2 := sgn_consistent (hxv_unit v) (hxv_unit (v + e (ax2 k)))
      (hxv_unit (v + e (ax1 k) + e (ax2 k)))
      (hpair_corners c hcM _ hv0 _ hv2) (hpair_corners c hcM _ hv2 _ hv3)
      (hpair_corners c hcM _ hv0 _ hv3)
    have hprod : sgn (dot3 (xv v) (xv (v + e (ax1 k)))) *
        sgn (dot3 (xv (v + e (ax1 k))) (xv (v + e (ax1 k) + e (ax2 k)))) =
        sgn (dot3 (xv v) (xv (v + e (ax2 k)))) *
        sgn (dot3 (xv (v + e (ax2 k))) (xv (v + e (ax2 k) + e (ax1 k)))) := by
      rw [hv3', hs1, hs2]
    have heq : d1 α v k =
        (if dot3 (xv v) (xv (v + e (ax1 k))) < 0 then (1 : ℤ) else 0) +
        (if dot3 (xv (v + e (ax1 k))) (xv (v + e (ax1 k) + e (ax2 k))) < 0 then 1 else 0) -
        (if dot3 (xv (v + e (ax2 k))) (xv (v + e (ax2 k) + e (ax1 k))) < 0 then 1 else 0) -
        (if dot3 (xv v) (xv (v + e (ax2 k))) < 0 then 1 else 0) := by
      simp only [d1, α, he1, he2, he3, he4, ↓reduceIte]
    rw [heq]
    exact even_of_sgn_prod (hprod.trans (mul_comm _ _))
  have hα_supp : ∀ v d, α v d ≠ 0 → v ∈ box (N - 2) := by
    intro v d hne
    have he : isEdgeOfM v d := by
      by_contra h
      exact hne (by simp [α, h])
    obtain ⟨c, hcM, hv, _⟩ := he
    have hc := mem_box.mp (hM_sub c hcM)
    rw [mem_box]
    intro a
    have hca := hc a
    rcases mem_corners.mp hv a with hva | hva <;> omega
  obtain ⟨γ, hγ⟩ := exists_cochain_lift N M α hα_supp hd1_even
  -- Real 1-cochain ω = α / 2 - γ
  let ω (v : G) (d : Fin 3) : ℝ := (α v d : ℝ) / 2 - (γ v d : ℝ)
  have hω_flat : ∀ v k, (v ∈ M ∨ v - e k ∈ M) →
      ω v (ax1 k) + ω (v + e (ax1 k)) (ax2 k) - ω (v + e (ax2 k)) (ax1 k) - ω v (ax2 k) = 0 := by
    intro v k hfk
    have h2 : (2 : ℝ) * (d1 γ v k : ℝ) = (d1 α v k : ℝ) := by exact_mod_cast hγ v k hfk
    simp only [ω]
    simp only [d1, Int.cast_add, Int.cast_sub] at h2
    linarith
  have hω_flat_cube : ∀ c ∈ M, ∀ (w : G) (k : Fin 3), (w = c ∨ w = c + e k) →
      ω w (ax1 k) + ω (w + e (ax1 k)) (ax2 k) - ω (w + e (ax2 k)) (ax1 k) - ω w (ax2 k) = 0 := by
    intro c hcM w k hw
    apply hω_flat
    rcases hw with rfl | rfl
    · exact Or.inl hcM
    · exact Or.inr (by simpa using hcM)
  have hcexp_ω : ∀ v d, isEdgeOfM v d →
      Complex.exp (2 * Real.pi * Complex.I * (ω v d : ℂ)) =
        (sgn (dot3 (xv v) (xv (v + e d))) : ℂ) := by
    intro v d hed
    have hsplit : (2 : ℂ) * Real.pi * Complex.I * (ω v d : ℂ) =
        2 * Real.pi * Complex.I * (((α v d : ℝ) / 2 : ℝ) : ℂ) +
        2 * Real.pi * Complex.I * ((-γ v d : ℤ) : ℂ) := by
      simp only [ω, Int.cast_neg, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_intCast,
        Complex.ofReal_ofNat]
      ring
    rw [hsplit, Complex.exp_add, cexp_two_pi_I_int, mul_one]
    have hα01 : α v d = 0 ∨ α v d = 1 := by
      simp only [α, hed, ↓reduceIte]; split_ifs <;> simp
    rw [cexp_pi_I_zero_or_one _ hα01]
    simp only [α, hed, ↓reduceIte, sgn]
    by_cases hneg : dot3 (xv v) (xv (v + e d)) < 0
    · have hnot : ¬ (0 ≤ dot3 (xv v) (xv (v + e d))) := not_le.mpr hneg
      simp [hneg, hnot]
    · have hge : 0 ≤ dot3 (xv v) (xv (v + e d)) := not_lt.mp hneg
      simp [hneg, hge]
  have hcexp_phiC : ∀ c ∈ M, ∀ v ∈ corners c,
      Complex.exp (2 * Real.pi * Complex.I * (phiC ω c v : ℂ)) =
        (sgn (dot3 (xv c) (xv v)) : ℂ) := by
    intro c hcM v hv
    let u1 : G := stepX c v
    let u2 : G := stepXY c v
    have hu1 : u1 ∈ corners c := mem_corners.mpr fun a => by
      fin_cases a
      · simpa [u1, stepX] using mem_corners.mp hv 0
      · simp [u1, stepX]
      · simp [u1, stepX]
    have hu2 : u2 ∈ corners c := mem_corners.mpr fun a => by
      fin_cases a
      · simpa [u2, u1, stepXY, stepX] using mem_corners.mp hv 0
      · simpa [u2, stepXY] using mem_corners.mp hv 1
      · simp [u2, stepXY, stepX]
    have hstep0 : Complex.exp (2 * Real.pi * Complex.I *
        ((if v 0 = c 0 + 1 then ω c 0 else 0 : ℝ) : ℂ)) = (sgn (dot3 (xv c) (xv u1)) : ℂ) := by
      rcases mem_corners.mp hv 0 with h0 | h0
      · have hne : v 0 ≠ c 0 + 1 := by omega
        have heq : u1 = c := by funext a; fin_cases a <;> simp [u1, stepX, h0]
        rw [if_neg hne, heq]
        have hdot : dot3 (xv c) (xv c) = 1 := hxv_unit c
        simp [hdot, sgn]
      · have heq : u1 = c + e 0 := by funext a; fin_cases a <;> simp [u1, stepX, e, h0]
        rw [if_pos h0, heq]
        exact hcexp_ω c 0 ⟨c, hcM, self_mem_corners c, heq ▸ hu1⟩
    have hstep1 : Complex.exp (2 * Real.pi * Complex.I *
        ((if v 1 = c 1 + 1 then ω u1 1 else 0 : ℝ) : ℂ)) = (sgn (dot3 (xv u1) (xv u2)) : ℂ) := by
      rcases mem_corners.mp hv 1 with h1 | h1
      · have hne : v 1 ≠ c 1 + 1 := by omega
        have heq : u2 = u1 := by funext a; fin_cases a <;> simp [u2, u1, stepXY, stepX, h1]
        rw [if_neg hne, heq]
        have hdot : dot3 (xv u1) (xv u1) = 1 := hxv_unit u1
        simp [hdot, sgn]
      · have heq : u2 = u1 + e 1 := by funext a; fin_cases a <;> simp [u2, u1, stepXY, stepX, e, h1]
        rw [if_pos h1, heq]
        exact hcexp_ω u1 1 ⟨c, hcM, hu1, heq ▸ hu2⟩
    have hstep2 : Complex.exp (2 * Real.pi * Complex.I *
        ((if v 2 = c 2 + 1 then ω u2 2 else 0 : ℝ) : ℂ)) = (sgn (dot3 (xv u2) (xv v)) : ℂ) := by
      rcases mem_corners.mp hv 2 with h2 | h2
      · have hne : v 2 ≠ c 2 + 1 := by omega
        have heq : v = u2 := by funext a; fin_cases a <;> simp [u2, stepXY, stepX, h2]
        rw [if_neg hne, heq]
        have hdot : dot3 (xv u2) (xv u2) = 1 := hxv_unit u2
        simp [hdot, sgn]
      · have heq : v = u2 + e 2 := by funext a; fin_cases a <;> simp [u2, stepXY, stepX, e, h2]
        rw [if_pos h2, heq]
        exact hcexp_ω u2 2 ⟨c, hcM, hu2, heq ▸ hv⟩
    have hexp : Complex.exp (2 * Real.pi * Complex.I * (phiC ω c v : ℂ)) =
        (sgn (dot3 (xv c) (xv u1)) : ℂ) * (sgn (dot3 (xv u1) (xv u2)) : ℂ) *
        (sgn (dot3 (xv u2) (xv v)) : ℂ) := by
      unfold phiC
      push_cast
      rw [mul_add, mul_add, Complex.exp_add, Complex.exp_add]
      exact congrArg₂ (· * ·) (congrArg₂ (· * ·) hstep0 hstep1) hstep2
    rw [hexp, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    have hc1 := sgn_consistent (hxv_unit c) (hxv_unit u1) (hxv_unit u2)
      (hpair_corners c hcM _ (self_mem_corners c) _ hu1)
      (hpair_corners c hcM _ hu1 _ hu2)
      (hpair_corners c hcM _ (self_mem_corners c) _ hu2)
    have hc2 := sgn_consistent (hxv_unit c) (hxv_unit u2) (hxv_unit v)
      (hpair_corners c hcM _ (self_mem_corners c) _ hu2)
      (hpair_corners c hcM _ hu2 _ hv)
      (hpair_corners c hcM _ (self_mem_corners c) _ hv)
    rw [hc1, hc2]
  -- Local sections on each cube c ∈ M
  let trilin (c : G) (p : Fin 3 → ℝ) : ℝ :=
    ∑ v ∈ corners c, wtAt δ c v p * phiC ω c v
  have htrilin_cont (c : G) : Continuous (trilin c) := by
    unfold trilin
    refine continuous_finsetSum _ fun v _ => (continuous_wtAt δ c v).mul continuous_const
  let vc (c : G) (k : K) (i : Fin 3) : ℝ := ∑ j, P k i j * xv c j
  let nc (c : G) (k : K) : ℝ := Real.sqrt (∑ i, (vc c k i) ^ 2)
  let sc (c : G) (k : K) (i : Fin 3) : ℂ :=
    Complex.exp (2 * Real.pi * Complex.I * (trilin c k.val : ℂ)) * ((vc c k i / nc c k : ℝ) : ℂ)
  have hvc_eq (c : G) (k : K) (i : Fin 3) :
      vc c k i = dot3 (repX k) (xv c) * repX k i := by
    simp only [vc, hrep_proj, dot3, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _; ring
  have hnc_eq (c : G) (k : K) : nc c k = |dot3 (repX k) (xv c)| := by
    unfold nc
    have hsum : ∑ i : Fin 3, (vc c k i) ^ 2 = (dot3 (repX k) (xv c)) ^ 2 := by
      simp_rw [hvc_eq, mul_pow, ← Finset.mul_sum]
      have hu : ∑ i : Fin 3, (repX k i) ^ 2 = 1 := by
        simpa [IsUnit3, dot3, sq] using hrep_unit k
      rw [hu, mul_one]
    rw [hsum, Real.sqrt_sq_eq_abs]
  have hsc_formula : ∀ c ∈ M, ∀ k : K, k.val ∈ cubeQ δ c → ∀ i : Fin 3,
      sc c k i = Complex.exp (2 * Real.pi * Complex.I * (trilin c k.val : ℂ)) *
        ((sgn (dot3 (repX k) (xv c)) * repX k i : ℝ) : ℂ) := by
    intro c hcM k hkQ i
    unfold sc
    congr 2
    rw [hvc_eq, hnc_eq]
    have hne : dot3 (repX k) (xv c) ≠ 0 := by
      have hsq := hpair_pt_corner c hcM k hkQ c (self_mem_corners c)
      intro h0; rw [h0] at hsq; norm_num at hsq
    rw [mul_div_right_comm, ← sgn_eq_div_abs hne]
  have hsc_cont : ∀ c ∈ M, ContinuousOn (sc c) {k : K | k.val ∈ cubeQ δ c} := by
    intro c hcM
    rw [continuousOn_pi]
    intro i
    have hvc_cont : Continuous (fun k : K => vc c k i) := by
      unfold vc
      refine continuous_finsetSum _ fun j _ => ?_
      exact ((continuous_apply j).comp ((continuous_apply i).comp hP)).mul continuous_const
    have hnc_cont : Continuous (fun k : K => nc c k) := by
      unfold nc
      refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i' _ => ?_)
      refine (Continuous.pow ?_ 2)
      unfold vc
      refine continuous_finsetSum _ fun j _ => ?_
      exact ((continuous_apply j).comp ((continuous_apply i').comp hP)).mul continuous_const
    have hnc_ne : ∀ k ∈ {k : K | k.val ∈ cubeQ δ c}, nc c k ≠ 0 := by
      intro k hkQ
      rw [hnc_eq]
      have hsq := hpair_pt_corner c hcM k hkQ c (self_mem_corners c)
      intro h0
      rw [abs_eq_zero] at h0
      rw [h0] at hsq; norm_num at hsq
    have h1 : Continuous (fun k : K => Complex.exp (2 * Real.pi * Complex.I * (trilin c k.val : ℂ))) :=
      Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp ((htrilin_cont c).comp continuous_subtype_val)))
    have h2 : ContinuousOn (fun k : K => ((vc c k i / nc c k : ℝ) : ℂ)) {k : K | k.val ∈ cubeQ δ c} :=
      Complex.continuous_ofReal.continuousOn.comp
        (hvc_cont.continuousOn.div hnc_cont.continuousOn hnc_ne) (mapsTo_univ _ _)
    exact h1.continuousOn.mul h2
  have hagree : ∀ c₁ ∈ M, ∀ c₂ ∈ M, ∀ k : K, k.val ∈ cubeQ δ c₁ → k.val ∈ cubeQ δ c₂ →
      sc c₁ k = sc c₂ k := by
    intro c₁ hc₁ c₂ hc₂ k hk₁ hk₂
    let v₀ : G := fun a => max (c₁ a) (c₂ a)
    have hv₀₁ : v₀ ∈ corners c₁ := mem_corners.mpr fun a => by
      have h1 := hk₁ a; have h2 := hk₂ a
      have hle : c₂ a ≤ c₁ a + 1 := by
        have : (c₂ a : ℝ) ≤ (c₁ a : ℝ) + 1 := by nlinarith
        exact_mod_cast this
      dsimp [v₀]
      rcases le_total (c₁ a) (c₂ a) with h | h
      · rw [max_eq_right h]; omega
      · rw [max_eq_left h]; exact Or.inl rfl
    have hv₀₂ : v₀ ∈ corners c₂ := mem_corners.mpr fun a => by
      have h1 := hk₁ a; have h2 := hk₂ a
      have hle : c₁ a ≤ c₂ a + 1 := by
        have : (c₁ a : ℝ) ≤ (c₂ a : ℝ) + 1 := by nlinarith
        exact_mod_cast this
      dsimp [v₀]
      rcases le_total (c₁ a) (c₂ a) with h | h
      · rw [max_eq_right h]; exact Or.inl rfl
      · rw [max_eq_left h]; omega
    have htrilin_diff : trilin c₁ k.val - trilin c₂ k.val = phiC ω c₁ v₀ - phiC ω c₂ v₀ := by
      let C : ℝ := phiC ω c₁ v₀ - phiC ω c₂ v₀
      have h1 : trilin c₁ k.val = ∑ v ∈ corners c₁ ∩ corners c₂, wtAt δ c₁ v k.val * phiC ω c₁ v := by
        unfold trilin
        symm
        apply Finset.sum_subset Finset.inter_subset_left
        intro v hv1 hnot
        have hv2 : v ∉ corners c₂ := fun h2 => hnot (Finset.mem_inter.mpr ⟨hv1, h2⟩)
        rw [wtAt_eq_of_mem_inter hδ hk₁ hk₂ v, wtAt_eq_zero_of_not_mem_corners δ c₂ v k.val hv2, zero_mul]
      have h2 : trilin c₂ k.val = ∑ v ∈ corners c₁ ∩ corners c₂, wtAt δ c₁ v k.val * phiC ω c₂ v := by
        unfold trilin
        symm
        calc ∑ v ∈ corners c₁ ∩ corners c₂, wtAt δ c₁ v k.val * phiC ω c₂ v
            = ∑ v ∈ corners c₁ ∩ corners c₂, wtAt δ c₂ v k.val * phiC ω c₂ v := by
              apply Finset.sum_congr rfl
              intro v _; rw [wtAt_eq_of_mem_inter hδ hk₁ hk₂ v]
          _ = ∑ v ∈ corners c₂, wtAt δ c₂ v k.val * phiC ω c₂ v := by
              apply Finset.sum_subset Finset.inter_subset_right
              intro v hv2 hnot
              have hv1 : v ∉ corners c₁ := fun h1 => hnot (Finset.mem_inter.mpr ⟨h1, hv2⟩)
              rw [← wtAt_eq_of_mem_inter hδ hk₁ hk₂ v, wtAt_eq_zero_of_not_mem_corners δ c₁ v k.val hv1, zero_mul]
      have hwt1 : ∑ v ∈ corners c₁ ∩ corners c₂, wtAt δ c₁ v k.val = 1 := by
        rw [← sum_wtAt δ c₁ k.val]
        apply Finset.sum_subset Finset.inter_subset_left
        intro v hv1 hnot
        have hv2 : v ∉ corners c₂ := fun h2 => hnot (Finset.mem_inter.mpr ⟨hv1, h2⟩)
        rw [wtAt_eq_of_mem_inter hδ hk₁ hk₂ v, wtAt_eq_zero_of_not_mem_corners δ c₂ v k.val hv2]
      rw [h1, h2, ← Finset.sum_sub_distrib]
      have hterm : ∀ v ∈ corners c₁ ∩ corners c₂,
          wtAt δ c₁ v k.val * phiC ω c₁ v - wtAt δ c₁ v k.val * phiC ω c₂ v =
          wtAt δ c₁ v k.val * C := by
        intro v hv
        obtain ⟨hv1, hv2⟩ := Finset.mem_inter.mp hv
        rw [← mul_sub]
        congr 1
        exact phiC_diff_const_on_inter ω (hω_flat_cube c₁ hc₁) (hω_flat_cube c₂ hc₂)
          hv₀₁ hv₀₂ hv1 hv2
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, hwt1, one_mul]
    funext i
    rw [hsc_formula c₁ hc₁ k hk₁ i, hsc_formula c₂ hc₂ k hk₂ i]
    have hs1 : sgn (dot3 (xv c₁) (xv v₀)) * sgn (dot3 (repX k) (xv c₁)) = sgn (dot3 (repX k) (xv v₀)) := by
      rw [mul_comm]
      exact sgn_consistent (hrep_unit k) (hxv_unit c₁) (hxv_unit v₀)
        (hpair_pt_corner c₁ hc₁ k hk₁ c₁ (self_mem_corners c₁))
        (hpair_corners c₁ hc₁ c₁ (self_mem_corners c₁) v₀ hv₀₁)
        (hpair_pt_corner c₁ hc₁ k hk₁ v₀ hv₀₁)
    have hs2 : sgn (dot3 (xv c₂) (xv v₀)) * sgn (dot3 (repX k) (xv c₂)) = sgn (dot3 (repX k) (xv v₀)) := by
      rw [mul_comm]
      exact sgn_consistent (hrep_unit k) (hxv_unit c₂) (hxv_unit v₀)
        (hpair_pt_corner c₂ hc₂ k hk₂ c₂ (self_mem_corners c₂))
        (hpair_corners c₂ hc₂ c₂ (self_mem_corners c₂) v₀ hv₀₂)
        (hpair_pt_corner c₂ hc₂ k hk₂ v₀ hv₀₂)
    exact overlap_combine htrilin_diff (hcexp_phiC c₁ hc₁ v₀ hv₀₁) (hcexp_phiC c₂ hc₂ v₀ hv₀₂)
      hs1 hs2 (sgn_mul_self _)
  have hcover : ∀ k : K, ∃ c ∈ M, k.val ∈ cubeQ δ c := by
    intro k
    let c : G := fun a => ⌊k.val a / δ⌋
    have hkQ : k.val ∈ cubeQ δ c := fun a => by
      have h1 : (⌊k.val a / δ⌋ : ℝ) ≤ k.val a / δ := Int.floor_le _
      have h2 : k.val a / δ < (⌊k.val a / δ⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      exact ⟨(le_div_iff₀' hδ).mp h1, ((div_lt_iff₀' hδ).mp h2).le⟩
    exact ⟨c, (hM_iff c).mpr ⟨k.val, hkQ, k.2⟩, hkQ⟩
  let s (k : K) : Fin 3 → ℂ := sc (hcover k).choose k
  have hs_eq : ∀ c ∈ M, ∀ k : K, k.val ∈ cubeQ δ c → s k = sc c k := by
    intro c hcM k hkQ
    exact hagree _ (hcover k).choose_spec.1 c hcM k (hcover k).choose_spec.2 hkQ
  refine ⟨s, ?_, ?_⟩
  · rw [continuous_iff_isClosed]
    intro Z hZ
    have hpre : s ⁻¹' Z = ⋃ c ∈ M, ({k : K | k.val ∈ cubeQ δ c} ∩ (sc c) ⁻¹' Z) := by
      ext k
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · intro hk
        obtain ⟨c, hcM, hkQ⟩ := hcover k
        exact ⟨c, hcM, hkQ, by rwa [← hs_eq c hcM k hkQ]⟩
      · rintro ⟨c, hcM, hkQ, hkZ⟩
        rwa [hs_eq c hcM k hkQ]
    rw [hpre]
    refine M.finite_toSet.isClosed_biUnion fun c hcM => ?_
    have hFc : IsClosed {k : K | k.val ∈ cubeQ δ c} :=
      (isClosed_cubeQ δ c).preimage continuous_subtype_val
    exact (hsc_cont c hcM).preimage_isClosed_of_isClosed hFc hZ
  · intro k
    obtain ⟨c, hcM, hkQ⟩ := hcover k
    have hsk : ∀ i, s k i = Complex.exp (2 * Real.pi * Complex.I * (trilin c k.val : ℂ)) *
        ((sgn (dot3 (repX k) (xv c)) * repX k i : ℝ) : ℂ) := fun i => by
      rw [hs_eq c hcM k hkQ, hsc_formula c hcM k hkQ i]
    constructor
    · intro h0
      have hxne : ∃ i : Fin 3, repX k i ≠ 0 := by
        by_contra hall
        push Not at hall
        have hu := hrep_unit k
        simp [IsUnit3, dot3, hall] at hu
      obtain ⟨i, hi⟩ := hxne
      have hi0 := congrFun h0 i
      rw [hsk i, Pi.zero_apply] at hi0
      have hne1 : Complex.exp (2 * Real.pi * Complex.I * (trilin c k.val : ℂ)) ≠ 0 :=
        Complex.exp_ne_zero _
      have hne2 : ((sgn (dot3 (repX k) (xv c)) * repX k i : ℝ) : ℂ) ≠ 0 := by
        rw [Complex.ofReal_ne_zero]
        exact mul_ne_zero (sgn_ne_zero _) hi
      exact mul_ne_zero hne1 hne2 hi0
    · intro i
      simp_rw [hsk, hrep_proj]
      let lam : ℂ := Complex.exp (2 * Real.pi * Complex.I * (trilin c k.val : ℂ)) *
        (sgn (dot3 (repX k) (xv c)) : ℂ)
      have hlhs : ∀ j : Fin 3, ((repX k i * repX k j : ℝ) : ℂ) *
          (Complex.exp (2 * Real.pi * Complex.I * (trilin c k.val : ℂ)) *
            ((sgn (dot3 (repX k) (xv c)) * repX k j : ℝ) : ℂ)) =
          lam * (repX k i : ℂ) * ((repX k j * repX k j : ℝ) : ℂ) := by
        intro j; simp only [lam]; push_cast; ring
      simp_rw [hlhs, ← Finset.mul_sum, ← Complex.ofReal_sum]
      have hu : ∑ j : Fin 3, repX k j * repX k j = 1 := hrep_unit k
      rw [hu, Complex.ofReal_one, mul_one]
      simp only [lam]; push_cast; ring

theorem H1_proved :
    ∀ K : Set (EuclideanSpace ℝ (Fin 2) × ℝ), IsCompact K →
    ∀ P : K → Fin 3 → Fin 3 → ℝ, Continuous P →
    (∀ k, ∃ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ∀ i j, P k i j = x.val i * x.val j) →
    ∃ s : K → Fin 3 → ℂ, Continuous s ∧ ∀ k, s k ≠ 0 ∧
      ∀ i, ∑ j, (P k i j : ℂ) * s k j = s k i := by
  intro K hK P hP hproj
  let toPi : EuclideanSpace ℝ (Fin 2) × ℝ → (Fin 3 → ℝ) := fun p => ![p.1 0, p.1 1, p.2]
  let fromPi : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 2) × ℝ :=
    fun v => (WithLp.toLp 2 ![v 0, v 1], v 2)
  have hleft : Function.LeftInverse fromPi toPi := by
    intro ⟨u, z⟩
    apply Prod.ext
    · ext i; fin_cases i <;> simp [fromPi, toPi]
    · simp [fromPi, toPi]
  have hright : Function.RightInverse fromPi toPi := by
    intro v
    funext i; fin_cases i <;> simp [fromPi, toPi]
  have htoC : Continuous toPi := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact (PiLp.continuous_apply 2 _ 0).comp continuous_fst
    · exact (PiLp.continuous_apply 2 _ 1).comp continuous_fst
    · exact continuous_snd
  have hfromC : Continuous fromPi := by
    refine Continuous.prodMk ?_ (continuous_apply 2)
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    fin_cases i <;> simp <;> exact continuous_apply _
  let e : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₜ (Fin 3 → ℝ) :=
    { toFun := toPi, invFun := fromPi, left_inv := hleft, right_inv := hright,
      continuous_toFun := htoC, continuous_invFun := hfromC }
  let K' : Set (Fin 3 → ℝ) := e '' K
  have hK' : IsCompact K' := hK.image e.continuous
  let eK : K ≃ₜ K' := e.image K
  let P' : K' → Fin 3 → Fin 3 → ℝ := fun k' => P (eK.symm k')
  have hP' : Continuous P' := hP.comp eK.symm.continuous
  have hproj' : ∀ k' : K', ∃ x : Fin 3 → ℝ, IsUnit3 x ∧ ∀ i j, P' k' i j = x i * x j := by
    intro k'
    obtain ⟨x, hx⟩ := hproj (eK.symm k')
    refine ⟨fun i => x.val i, ?_, hx⟩
    have hnorm : ‖x.val‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
    have hsq := EuclideanSpace.real_norm_sq_eq x.val
    rw [hnorm, one_pow] at hsq
    simpa [IsUnit3, dot3, sq] using hsq.symm
  obtain ⟨s', hs'c, hs'⟩ := H1_pi K' hK' P' hP' hproj'
  refine ⟨fun k => s' (eK k), hs'c.comp eK.continuous, fun k => ?_⟩
  have h := hs' (eK k)
  simpa [P', Homeomorph.symm_apply_apply] using h

end OMA.InscribedH1


theorem OMA.solution : type_of% @InscribedSquare.exists_inscribed_rectangle :=
  OMA.InscribedR1.main OMA.P1InscribedSquareH1.sol
    (OMA.InscribedR1H2R1.main OMA.InscribedHelpers.sol
      (OMA.InscribedR1H2R1H2R1.main OMA.InscribedH1.H1_proved OMA.HemisphereLog.odd_zero))

