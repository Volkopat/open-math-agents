import FormalConjectures.ErdosProblems.«1066»
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! The Swanepoel bound for separated planar point sets, reduced to the outer boundary arc
and its ordered second layer. See K. J. Swanepoel, Independence Numbers of Planar
Contact Graphs, Discrete Comput. Geom. 28 (2002), 649–670, Sections 3–4. -/

open Finset Real
open scoped EuclideanGeometry Topology
namespace OMA.R_Erdos1066_erdos_1066_variants_swanepoel_R2

/-- Swanepoel's nonconcave boundary arc (Lemmas 4–7). The boundary vertices
p 0,...,p 14 correspond to p₋₁,...,p₁₃ in the paper and t i is the turn at p (i+2).
The separated configuration satisfies the small-set expansion and cut conditions. -/
def H1 : Prop := by
  classical
  exact ∀ X : Finset ℝ²,
    let E := fun x y : ℝ² => dist x y = 1
    let D := fun x => (X.filter (E x)).card
    let K : Set ℝ² := {v | ∃ x ∈ X, ∃ y ∈ X, E x y ∧ v ∈ segment ℝ x y}
    (X : Set ℝ²).Pairwise (fun x y => 1 ≤ dist x y) →
    (∀ S ⊆ X, (S : Set ℝ²).Pairwise (fun x y => ¬ E x y) → S.card ≤ 8 →
      4*S.card ≤ (X.filter (fun x => x ∈ S ∨ ∃ y ∈ S, E y x)).card) →
    (∀ x ∈ X, 3 ≤ D x ∧ D x ≤ 6) →
    (∀ a b : ℝ², a ≠ b → (X.filter (fun v => E a v ∧ E b v)).card ≤ 2) →
    (∀ a ∈ X, ∀ b ∈ X, ∀ v ∈ X, E a b → v ∈ segment ℝ a b → v = a ∨ v = b) →
    (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, ∀ d ∈ X, E a b → E c d → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
      Disjoint (segment ℝ a b) (segment ℝ c d)) →
    X.Nonempty → (∀ A ⊆ X, ∀ B ⊆ X, A.Nonempty → B.Nonempty → Disjoint A B →
      (X \ (A ∪ B)).card ≤ 1 → ∃ x ∈ A, ∃ y ∈ B, E x y) →
    ∃ (p q : ℕ → ℝ²) (z : ℝ²),
    let U := connectedComponentIn Kᶜ z
    let t := fun i => (∠ (q i) (p (i+2)) (q (i+1))) - π/3
    (Bornology.IsBounded Uᶜ ∧ Set.InjOn p (Set.Iio 15) ∧ (∀ i < 15, p i ∈ X) ∧
      (∀ i < 14, E (p i) (p (i+1)) ∧ segment ℝ (p i) (p (i+1)) ⊆ frontier U) ∧
      (D (p 0) = 3 ∨ D (p 0) = 4 ∧ ∃ w ∈ X, E (p 0) w ∧ E (p 1) w) ∧
      D (p 1) = 3 ∧ (∀ i, 2 ≤ i → i < 15 → D (p i) = 4) ∧
      (∀ i < 13, q i ∈ X ∧ E (p (i+1)) (q i) ∧ E (p (i+2)) (q i)) ∧
      (∀ i < 12, 0 ≤ t i) ∧ (∑ i ∈ range 12, t i) < π/3)

/-- Swanepoel's second-layer extraction on that arc (Lemmas 8–9 and the
ray orders in Figures 7–9). The two outer neighbours r j, s j of the triangle tip
q (j+2) may coincide with upper neighbours of the adjacent tip. A failure j
means s j ≠ r (j+1). The angle equalities record the cyclic order about the
triangle tip and the subangles of the wedge between consecutive triangle tips. -/
def H2 : Prop := by
  classical
  exact ∀ X : Finset ℝ²,
    let E := fun x y : ℝ² => dist x y = 1
    let D := fun x => (X.filter (E x)).card
    let K : Set ℝ² := {v | ∃ x ∈ X, ∃ y ∈ X, E x y ∧ v ∈ segment ℝ x y}
    (X : Set ℝ²).Pairwise (fun x y => 1 ≤ dist x y) →
    (∀ S ⊆ X, (S : Set ℝ²).Pairwise (fun x y => ¬ E x y) → S.card ≤ 8 →
      4*S.card ≤ (X.filter (fun x => x ∈ S ∨ ∃ y ∈ S, E y x)).card) →
    (∀ x ∈ X, 3 ≤ D x ∧ D x ≤ 6) →
    (∀ a b : ℝ², a ≠ b → (X.filter (fun v => E a v ∧ E b v)).card ≤ 2) →
    X.Nonempty → (∀ A ⊆ X, ∀ B ⊆ X, A.Nonempty → B.Nonempty → Disjoint A B →
      (X \ (A ∪ B)).card ≤ 1 → ∃ x ∈ A, ∃ y ∈ B, E x y) →
    ∀ (p q : ℕ → ℝ²) (z : ℝ²),
    let U := connectedComponentIn Kᶜ z
    let t := fun i => (∠ (q i) (p (i+2)) (q (i+1))) - π/3
    (Bornology.IsBounded Uᶜ ∧ Set.InjOn p (Set.Iio 15) ∧ (∀ i < 15, p i ∈ X) ∧
      (∀ i < 14, E (p i) (p (i+1)) ∧ segment ℝ (p i) (p (i+1)) ⊆ frontier U) ∧
      (D (p 0) = 3 ∨ D (p 0) = 4 ∧ ∃ w ∈ X, E (p 0) w ∧ E (p 1) w) ∧
      D (p 1) = 3 ∧ (∀ i, 2 ≤ i → i < 15 → D (p i) = 4) ∧
      (∀ i < 13, q i ∈ X ∧ E (p (i+1)) (q i) ∧ E (p (i+2)) (q i)) ∧
      (∀ i < 12, 0 ≤ t i) ∧ (∑ i ∈ range 12, t i) < π/3) →
    ∃ r s : ℕ → ℝ²,
    let c := fun i => q (i+2)
    let x := fun i => p (i+3)
    let A := fun u v w : ℝ² => ∠ u v w
    let a := fun i => A (c i) (x i) (r i)
    let b := fun i => A (c i) (x (i+1)) (s i)
    (∀ i < 7, r i ∈ X ∧ s i ∈ X ∧ E (c i) (r i) ∧ E (c i) (s i) ∧
      r i ≠ s i ∧ r i ≠ x i ∧ s i ≠ x (i+1) ∧ r i ≠ q (i+1) ∧ s i ≠ q (i+3) ∧
      A (r i) (c i) (x i) + π/3 + A (x (i+1)) (c i) (s i) + A (s i) (c i) (r i) = 2*π ∧
      A (q (i+1)) (x i) (r i) + a i = t (i+1)+π/3 ∧
      A (q (i+3)) (x (i+1)) (s i) + b i = t (i+2)+π/3) ∧
    (∀ i < 6, s i ≠ r (i+1) → b i + A (s i) (x (i+1)) (r (i+1)) + a (i+1) = t (i+2)+π/3) ∧
    (∃ i < 3, s i ≠ r (i+1)) ∧ (∃ j, 3 ≤ j ∧ j < 6 ∧ s j ≠ r (j+1))

end OMA.R_Erdos1066_erdos_1066_variants_swanepoel_R2
open Real Finset
open scoped EuclideanGeometry
namespace Swanepoel.Hexagon

lemma cos_arg_difference {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (hzw : 1 ≤ ‖z - w‖) :
    cos (z.arg - w.arg) ≤ 1 / 2 := by
  have hnz : z ≠ 0 := fun e => by simp [e] at hz
  have hnw : w ≠ 0 := fun e => by simp [e] at hw
  rw [Real.cos_sub, Complex.cos_arg hnz, Complex.cos_arg hnw, Complex.sin_arg, Complex.sin_arg,
    hz, hw, div_one, div_one, div_one, div_one]
  have sz := Complex.sq_norm z
  have sw := Complex.sq_norm w
  have sd := Complex.sq_norm (z - w)
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hz, hw, one_pow] at sz sw sd
  nlinarith [sq_nonneg (‖z - w‖ - 1)]

/-- Six half-open sectors of angular width π/3 suffice for the whole unit circle. -/
theorem degree_le_six (X : Finset ℝ²) (hX : (X : Set ℝ²).Pairwise (fun x y => 1 ≤ dist x y))
    (c : ℝ²) : (X.filter (fun v => dist c v = 1)).card ≤ 6 := by
  classical
  let N := X.filter (fun v => dist c v = 1)
  let v (x : ℝ²) : ℂ := ⟨x 0 - c 0, x 1 - c 1⟩
  let angle (x : ℝ²) := π - (v x).arg
  let u (x : ℝ²) := angle x / (π/3)
  let bucket (x : ℝ²) := ⌊u x⌋₊
  have hθ (x : ℝ²) : 0 ≤ angle x ∧ angle x < 2*π := by
    dsimp [angle]
    constructor <;> linarith [Complex.arg_le_pi (v x), Complex.neg_pi_lt_arg (v x)]
  have hU (x : ℝ²) : 0 ≤ u x := div_nonneg (hθ x).1 (by positivity)
  have hdist (x y : ℝ²) : ‖v x-v y‖ = dist x y := by
    rw [Complex.norm_def, EuclideanSpace.dist_eq, Fin.sum_univ_two]
    congr 1
    simp [Complex.normSq_apply, v, Real.dist_eq, pow_two]
  have hz : v c = 0 := by simp [v]; rfl
  have hu (x : ℝ²) (hx : x ∈ N) : ‖v x‖ = 1 := by
    rw [← sub_zero (v x), ← hz, hdist, dist_comm]
    exact (mem_filter.mp hx).2
  have maps : Set.MapsTo bucket (N : Set ℝ²) (range 6 : Finset ℕ) := by
    intro x _
    change ⌊u x⌋₊ ∈ range 6
    rw [mem_range, Nat.floor_lt (hU x)]
    change angle x / (π/3) < (6 : ℝ)
    rw [div_lt_iff₀ (by positivity)]
    linarith [(hθ x).2]
  have inj : Set.InjOn bucket (N : Set ℝ²) := by
    intro x hx y hy same
    by_contra hxy
    have hnorm : 1 ≤ ‖v x - v y‖ := by
      rw [hdist]
      exact hX (mem_filter.mp hx).1 (mem_filter.mp hy).1 hxy
    have hg : π/3 ≤ |angle x-angle y| := by
      by_contra! hlt
      have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _)
        (by linarith [pi_pos] : π/3 ≤ π) hlt
      rw [Real.cos_pi_div_three, Real.cos_abs,
        show angle x-angle y = -((v x).arg-(v y).arg) by dsimp [angle]; ring, Real.cos_neg] at hcos
      linarith [cos_arg_difference (hu x hx) (hu y hy) hnorm]
    have h₁ := Nat.floor_le (hU x)
    have h₂ := Nat.lt_floor_add_one (u x)
    have h₃ := Nat.floor_le (hU y)
    have h₄ := Nat.lt_floor_add_one (u y)
    change ⌊u x⌋₊ = ⌊u y⌋₊ at same
    rw [same] at h₁ h₂
    have short : |u x-u y| < 1 := abs_lt.mpr ⟨by linarith,by linarith⟩
    change |angle x/(π/3) - angle y/(π/3)| < 1 at short
    rw [← sub_div, abs_div, abs_of_pos (by positivity : 0 < π/3),
      div_lt_one (by positivity)] at short
    linarith
  simpa using card_le_card_of_injOn bucket maps inj

/-- The singleton case of small-set expansion gives minimum degree three. -/
lemma three_le_degree (X : Finset ℝ²) (he : ∀ S ⊆ X,
    (S : Set ℝ²).Pairwise (fun x y => dist x y ≠ 1) → S.card ≤ 8 →
    4*S.card ≤ (X.filter (fun x => x ∈ S ∨ ∃ y ∈ S, dist y x = 1)).card)
    {x : ℝ²} (hx : x ∈ X) : 3 ≤ (X.filter (fun y => dist x y = 1)).card := by
  classical
  have h := he {x} (singleton_subset_iff.mpr hx) (by simp) (by simp)
  simp only [card_singleton, mul_one, mem_singleton, exists_eq_left] at h
  have eq : X.filter (fun y => y = x ∨ dist x y = 1) = insert x (X.filter (fun y => dist x y = 1)) := by
    ext y
    simp only [mem_filter, mem_insert]
    constructor
    · rintro ⟨hy, h | h⟩
      · exact Or.inl h
      · exact Or.inr ⟨hy,h⟩
    · rintro (rfl | ⟨hy,e⟩)
      · exact ⟨hx,Or.inl rfl⟩
      · exact ⟨hy,Or.inr e⟩
  rw [eq, card_insert_of_notMem (by simp)] at h
  omega

end Swanepoel.Hexagon
open Real Finset
open scoped EuclideanGeometry Topology
namespace Swanepoel.Embedding

/-- No third point of a separated configuration lies on a unit edge. -/
theorem vertex_on_edge {X : Finset ℝ²} (hX : (X : Set ℝ²).Pairwise (fun x y => 1 ≤ dist x y))
    {a b v : ℝ²} (ha : a ∈ X) (hb : b ∈ X) (hv : v ∈ X) (he : dist a b = 1)
    (hs : v ∈ segment ℝ a b) : v = a ∨ v = b := by
  by_contra! hn
  have h := dist_add_dist_of_mem_segment hs
  linarith [hX ha hv hn.1.symm, hX hv hb hn.2]

/-- Straight segments for disjoint contact edges do not intersect. -/
theorem edges_disjoint {X : Finset ℝ²} (hX : (X : Set ℝ²).Pairwise (fun x y => 1 ≤ dist x y))
    {a b c d : ℝ²} (ha : a ∈ X) (hb : b ∈ X) (hc : c ∈ X) (hd : d ∈ X)
    (hab : dist a b = 1) (hcd : dist c d = 1)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Disjoint (segment ℝ a b) (segment ℝ c d) := by
  refine Set.disjoint_left.mpr ?_
  intro w hw hw'
  have h1 := dist_add_dist_of_mem_segment hw
  have h2 := dist_add_dist_of_mem_segment hw'
  rw [dist_comm w b, hab] at h1
  rw [dist_comm w d, hcd] at h2
  have a₁ := hX ha hc hac
  have a₂ := hX ha hd had
  have b₁ := hX hb hc hbc
  have b₂ := hX hb hd hbd
  have t₁ := dist_triangle a w c
  have t₂ := dist_triangle a w d
  have t₃ := dist_triangle b w c
  have t₄ := dist_triangle b w d
  rw [dist_comm w c] at t₁ t₃
  rw [dist_comm w d] at t₂ t₄
  have mc : w = midpoint ℝ a c := eq_midpoint_of_dist_eq_half (by linarith)
    (by rw [dist_comm w c]; linarith)
  have md : w = midpoint ℝ a d := eq_midpoint_of_dist_eq_half (by linarith)
    (by rw [dist_comm w d]; linarith)
  have eq := (midpoint_eq_iff.mp mc.symm).symm.trans (midpoint_eq_iff.mp md.symm)
  simpa [eq] using hcd

/-- Two distinct points in the plane have at most two common unit neighbours. -/
theorem common_neighbours (X : Finset ℝ²) (a b : ℝ²) (hab : a ≠ b) :
    (X.filter (fun v => dist a v = 1 ∧ dist b v = 1)).card ≤ 2 := by
  classical
  let N := X.filter (fun v => dist a v = 1 ∧ dist b v = 1)
  change N.card ≤ 2
  by_cases small : N.card ≤ 1
  · omega
  obtain ⟨u,hu,v,hv,huv⟩ := one_lt_card.mp (by omega : 1 < N.card)
  have unit (x) (hx : x ∈ N) : dist x a = 1 ∧ dist x b = 1 := by
    obtain ⟨_,h,k⟩ := mem_filter.mp hx
    exact ⟨(dist_comm ..).trans h,(dist_comm ..).trans k⟩
  have sub : N ⊆ {u,v} := by
    intro x hx
    have two := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
      (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) hab huv
      (unit u hu).1 (unit v hv).1 (unit x hx).1 (unit u hu).2 (unit v hv).2 (unit x hx).2
    simpa only [mem_insert, mem_singleton] using two
  exact (card_le_card sub).trans card_le_two

end Swanepoel.Embedding

/- Euclidean charge estimates in the proof of Swanepoel's Lemma 10.
The radial description uses ordinary angles at the common boundary vertex.
No contact between successive inner triangle tips is required. -/

open Real
open scoped EuclideanGeometry

namespace Swanepoel.Charges

lemma radius_bounds {a : ℝ} (ha : 0 ≤ a) (hb : a ≤ π / 3) :
    1 ≤ 2 * cos a ∧ 2 * cos a ≤ 2 := by
  have h := Real.cos_le_cos_of_nonneg_of_le_pi ha (by linarith [Real.pi_pos]) hb
  rw [Real.cos_pi_div_three] at h
  constructor <;> linarith [Real.cos_le_one a]

lemma gap_of_test {u v θ t : ℝ} (hu : 0 < u) (hv : 0 < v) (hθ : 0 ≤ θ) (ht : t ≤ π)
    (hobs : 1 ≤ u^2 + v^2 - 2*u*v*cos θ)
    (htest : u^2 + v^2 - 2*u*v*cos t ≤ 1) : t ≤ θ := by
  by_contra! hlt
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi hθ ht hlt
  have h := mul_lt_mul_of_pos_left hc (mul_pos (mul_pos (by norm_num : 0 < (2:ℝ)) hu) hv)
  linarith

lemma sin_twice_lower {a : ℝ} (ha : π / 6 ≤ a) (hb : a ≤ π / 3) :
    √3 / 2 ≤ sin (2 * a) := by
  rw [← Real.sin_pi_div_three]
  by_cases hl : 2 * a ≤ π / 2
  · apply Real.sin_le_sin_of_le_of_le_pi_div_two _ hl <;> linarith [Real.pi_pos]
  · rw [← Real.sin_pi_sub (2 * a)]
    apply Real.sin_le_sin_of_le_of_le_pi_div_two <;> linarith [Real.pi_pos]

/-- At a fixed angle, squared distance is a convex quadratic in the radius v. -/
lemma annulus_test {u c v : ℝ} (h1 : 1 ≤ v) (h2 : v ≤ 2)
    (hleft : u^2 + 1 - 2*u*c ≤ 1) (hright : u^2 + 4 - 4*u*c ≤ 1) :
    u^2 + v^2 - 2*u*v*c ≤ 1 := by
  nlinarith only [mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr hleft),
    mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hright),
    mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

/-- Radial form of the angle comparison used for equation (6) in the paper. -/
lemma one_side {a θ v : ℝ} (ha : 0 ≤ a) (hau : a ≤ π / 3) (hθ : 0 ≤ θ)
    (hv : 1 ≤ v) (hvu : v ≤ 2)
    (hsep : 1 ≤ (2*cos a)^2 + v^2 - 2*(2*cos a)*v*cos θ) :
    min a (π / 3 - a) ≤ θ := by
  have rad := radius_bounds ha hau
  have cp : 0 < cos a := by linarith [rad.1]
  by_cases hs : a ≤ π / 6
  · rw [min_eq_left (by linarith)]
    apply gap_of_test (by linarith : 0 < 2*cos a) (by linarith) hθ (by linarith [pi_pos]) hsep
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi ha (by linarith [pi_pos]) hs
    rw [Real.cos_pi_div_six] at hc
    have hsq := mul_self_le_mul_self (by positivity : 0 ≤ √3 / 2) hc
    have ht : v + 1 ≤ 4 * (cos a)^2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hv) (sub_nonneg.mpr ht)]
  · rw [min_eq_right (by linarith)]
    apply gap_of_test (by linarith : 0 < 2*cos a) (by linarith) hθ (by linarith [pi_pos]) hsep
    apply annulus_test hv hvu
    · have hc := Real.cos_le_cos_of_nonneg_of_le_pi (sub_nonneg.mpr hau)
        (by linarith [pi_pos]) (by linarith : π/3 - a ≤ a)
      nlinarith only [mul_nonneg cp.le (sub_nonneg.mpr hc)]
    · have hh := mul_le_mul_of_nonneg_left (sin_twice_lower (le_of_not_ge hs) hau)
        (by positivity : 0 ≤ √3)
      rw [Real.sin_two_mul] at hh
      rw [Real.cos_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
      nlinarith only [hh, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]

/-- At a ray separation of 30 degrees the unit-distance comparison factors exactly. -/
lemma thirty_degree_factor (a b : ℝ) :
    (2*cos a)^2 + (2*cos b)^2 - 2*(2*cos a)*(2*cos b)*cos (π/6) - 1 =
      (2*cos (a+b) - √3) * (2*cos (a-b) - √3) := by
  symm
  calc
    _ = (2*cos a*cos b - √3)^2 - 4*(sin a)^2*(sin b)^2 := by
      rw [Real.cos_add, Real.cos_sub]
      ring
    _ = _ := by
      rw [show (sin a)^2 = 1-(cos a)^2 by nlinarith only [Real.sin_sq_add_cos_sq a],
        show (sin b)^2 = 1-(cos b)^2 by nlinarith only [Real.sin_sq_add_cos_sq b],
        Real.cos_pi_div_six]
      nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]

lemma central_gap {a b θ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hau : a ≤ π/6)
    (hbu : b ≤ π/6) (hsum : π/6 ≤ a+b) (hθ : 0 ≤ θ)
    (hsep : 1 ≤ (2*cos a)^2 + (2*cos b)^2 - 2*(2*cos a)*(2*cos b)*cos θ) :
    π/6 ≤ θ := by
  have pa := (radius_bounds ha (show a ≤ π/3 by linarith [pi_pos])).1
  have pb := (radius_bounds hb (show b ≤ π/3 by linarith [pi_pos])).1
  apply gap_of_test (by linarith) (by linarith) hθ (by linarith [pi_pos]) hsep
  have hplus := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [pi_pos])
    (by linarith [pi_pos]) hsum
  have ha' : |a-b| ≤ π/6 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hminus := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [pi_pos]) ha'
  rw [Real.cos_pi_div_six] at hplus
  rw [Real.cos_pi_div_six, Real.cos_abs] at hminus
  have ht := mul_nonpos_of_nonpos_of_nonneg (by linarith : 2*cos (a+b) - √3 ≤ 0)
    (by linarith : 0 ≤ 2*cos (a-b) - √3)
  linarith only [thirty_degree_factor a b, ht]

/-- Both one-sided estimates and equation (5), for an actual separated pair of tips.
Here l,m,r are the three consecutive boundary turns. -/
theorem seam_charges {a b θ l m r : ℝ}
    (ha : 0 ≤ a) (hau : a ≤ π/3) (hb : 0 ≤ b) (hbu : b ≤ π/3) (hθ : 0 ≤ θ)
    (hl : 0 ≤ l) (hm : 0 ≤ m) (hr : 0 ≤ r)
    (hl' : π/3-2*a ≤ l) (hr' : π/3-2*b ≤ r) (hmid : m = a+θ+b-π/3)
    (hsep : 1 ≤ (2*cos a)^2 + (2*cos b)^2 - 2*(2*cos a)*(2*cos b)*cos θ) :
    b ≤ l+m ∧ a ≤ m+r ∧ π/3 ≤ l+2*m+r := by
  have ra := radius_bounds ha hau
  have rb := radius_bounds hb hbu
  have hag := one_side ha hau hθ rb.1 rb.2 hsep
  have hbg := one_side hb hbu hθ ra.1 ra.2 (by linarith only [hsep])
  constructor
  · rcases le_total a (π/3-a) with h | h
    · rw [min_eq_left h] at hag; linarith
    · rw [min_eq_right h] at hag; linarith
  constructor
  · rcases le_total b (π/3-b) with h | h
    · rw [min_eq_left h] at hbg; linarith
    · rw [min_eq_right h] at hbg; linarith
  · by_cases h1 : a ≤ π/6
    · by_cases h2 : b ≤ π/6
      · by_cases h3 : π/6 ≤ a+b
        · linarith [central_gap ha hb h1 h2 h3 hθ hsep]
        · linarith
      · rw [min_eq_right (by linarith)] at hbg; linarith
    · rw [min_eq_right (by linarith)] at hag; linarith

/-- Law of cosines in the isosceles triangle formed by the boundary vertex, the
triangle tip, and an outer neighbour of that tip. -/
lemma isosceles_radius (p q s : ℝ²) (hpq : dist q p = 1) (hqs : dist q s = 1)
    (hps : 1 ≤ dist p s) : dist p s = 2 * cos (∠ q p s) := by
  have h := EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle q p s
  rw [hqs, hpq, dist_comm s p] at h
  have hf : dist p s * (dist p s - 2*cos (∠ q p s)) = 0 := by nlinarith only [h]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left (by linarith))

/-- The algebraic estimate specialized to Euclidean points and their ordinary angles. -/
theorem geometric_seam (p q q' s r : ℝ²) (l m u : ℝ)
    (hpq : dist q p = 1) (hpq' : dist q' p = 1)
    (hqs : dist q s = 1) (hqr : dist q' r = 1)
    (hps : 1 ≤ dist p s) (hpr : 1 ≤ dist p r) (hsr : 1 ≤ dist s r)
    (hl : 0 ≤ l) (hm : 0 ≤ m) (hu : 0 ≤ u)
    (hl' : π/3-2*(∠ q p s) ≤ l) (hu' : π/3-2*(∠ q' p r) ≤ u)
    (hmid : m = (∠ q p s) + (∠ s p r) + (∠ q' p r) - π/3) :
    (∠ q' p r) ≤ l+m ∧ (∠ q p s) ≤ m+u ∧ π/3 ≤ l+2*m+u := by
  have h1 := isosceles_radius p q s hpq hqs hps
  have h2 := isosceles_radius p q' r hpq' hqr hpr
  have bound (a d : ℝ) (ha : a ≤ π) (hd : 1 ≤ d) (he : d = 2*cos a) : a ≤ π/3 := by
    by_contra! h
    have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [pi_pos]) ha h
    rw [Real.cos_pi_div_three] at hc
    linarith
  have hs := EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle s p r
  rw [dist_comm s p, dist_comm r p, h1, h2] at hs
  exact seam_charges (EuclideanGeometry.angle_nonneg ..)
    (bound _ _ (EuclideanGeometry.angle_le_pi ..) hps h1) (EuclideanGeometry.angle_nonneg ..)
    (bound _ _ (EuclideanGeometry.angle_le_pi ..) hpr h2) (EuclideanGeometry.angle_nonneg ..)
    hl hm hu hl' hu' hmid (by nlinarith only [hs, hsr, sq_nonneg (dist s r - 1)])

end Swanepoel.Charges
open Real EuclideanGeometry
open scoped EuclideanGeometry
namespace Swanepoel.Charges

lemma apex_angle (c x v : ℝ²) (hc : dist c x = 1) (hv : dist c v = 1) :
    (∠ v c x) + 2*(∠ c x v) = π := by
  have hcx : x ≠ c := fun h => by simp [h] at hc
  have hs := EuclideanGeometry.angle_add_angle_add_angle_eq_pi v hcx
  have he := EuclideanGeometry.angle_eq_angle_of_dist_eq (hc.trans hv.symm)
  rw [EuclideanGeometry.angle_comm x v c] at hs
  linarith

/-- If an exterior point of the unit circle at x also lies on the unit circle about c,
its angle at x is bounded by its separation from a second unit neighbour y of x. -/
lemma wedge_side (c x v y : ℝ²) (hc : dist c x = 1) (hv : dist c v = 1)
    (hxy : dist y x = 1) (hxv : 1 ≤ dist x v) (hyv : 1 ≤ dist y v) :
    (∠ c x v) ≤ (∠ y x v) := by
  have hd := isosceles_radius x c v hc hv hxv
  have h := EuclideanGeometry.law_cos y x v
  rw [hxy, dist_comm v x] at h
  by_contra! hlt
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (EuclideanGeometry.angle_nonneg ..)
    (EuclideanGeometry.angle_le_pi ..) hlt
  have hprod := mul_lt_mul_of_pos_left hcos (by linarith : 0 < dist x v)
  have he : dist x v * cos (∠ c x v) = dist x v ^ 2 / 2 := by
    have eq := congrArg (fun u => u * dist x v) hd
    nlinarith only [eq]
  rw [he] at hprod
  nlinarith only [h, hprod, hyv, sq_nonneg (dist y v - 1)]

lemma separated_angle (c s r : ℝ²) (hs : dist c s = 1) (hr : dist c r = 1) (hd : 1 ≤ dist s r) :
    π/3 ≤ ∠ s c r := by
  have h := EuclideanGeometry.law_cos s c r
  rw [dist_comm s c, dist_comm r c, hs, hr] at h
  by_contra! hlt
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (EuclideanGeometry.angle_nonneg ..)
    (by linarith [pi_pos]) hlt
  rw [Real.cos_pi_div_three] at hc
  nlinarith only [h, hc, hd, sq_nonneg (dist s r - 1)]

/-- One actual inner hub of the broken lattice. The three angle sums just record the
cyclic order at c and the positions of r and s in the two boundary wedges. -/
theorem hub_angles (c x x' r s y y' : ℝ²) (t t' : ℝ)
    (hx : dist c x = 1) (hx' : dist c x' = 1) (hr : dist c r = 1) (hs : dist c s = 1)
    (hxy : dist y x = 1) (hxy' : dist y' x' = 1)
    (hrs : 1 ≤ dist s r) (hxr : 1 ≤ dist x r) (hxs : 1 ≤ dist x' s)
    (hyr : 1 ≤ dist y r) (hys : 1 ≤ dist y' s)
    (hcycle : (∠ r c x) + π/3 + (∠ x' c s) + (∠ s c r) = 2*π)
    (hleft : (∠ y x r) + (∠ c x r) = t + π/3)
    (hright : (∠ y' x' s) + (∠ c x' s) = t' + π/3) :
    π/3 ≤ (∠ c x r) + (∠ c x' s) ∧
    π/3 - 2*(∠ c x' s) ≤ t ∧ π/3 - 2*(∠ c x r) ≤ t' := by
  have left := apex_angle c x r hx hr
  have right := apex_angle c x' s hx' hs
  rw [EuclideanGeometry.angle_comm x' c s] at hcycle
  have both : π/3 ≤ (∠ c x r) + (∠ c x' s) := by
    linarith [separated_angle c s r hs hr hrs]
  refine ⟨both, ?_, ?_⟩
  · linarith [wedge_side c x r y hx hr hxy hxr hyr]
  · linarith [wedge_side c x' s y' hx' hs hxy' hxs hys]

end Swanepoel.Charges
open Real Finset
namespace Swanepoel.Charges

/-- Two failures in the two successive triples use up at least the entire turn budget.
There are only nine possible pairs of positions. -/
lemma two_triples (t : ℕ → ℝ) (f : ℕ → Prop) (hn : ∀ i < 12, 0 ≤ t i)
    (ht : (∑ i ∈ range 12, t i) < π/3)
    (single : ∀ i < 6, f i → π/3 ≤ t (i+1) + 2*t (i+2) + t (i+3))
    (adjacent : ∀ i < 5, f i → f (i+1) → π/3 ≤ t (i+1)+t (i+2)+t (i+3)+t (i+4))
    (first : ∃ i < 3, f i) (last : ∃ j, 3 ≤ j ∧ j < 6 ∧ f j) : False := by
  obtain ⟨i,hi,fi⟩ := first
  obtain ⟨j,hj,hj',fj⟩ := last
  have w₁ := single i (by omega) fi
  have w₂ := single j hj' fj
  norm_num [Finset.sum_range_succ] at ht
  have n0 := hn 0 (by decide)
  have n1 := hn 1 (by decide)
  have n2 := hn 2 (by decide)
  have n3 := hn 3 (by decide)
  have n4 := hn 4 (by decide)
  have n5 := hn 5 (by decide)
  have n6 := hn 6 (by decide)
  have n7 := hn 7 (by decide)
  have n8 := hn 8 (by decide)
  have n9 := hn 9 (by decide)
  have n10 := hn 10 (by decide)
  have n11 := hn 11 (by decide)
  by_cases h : j = i+1
  · have ei : i = 2 := by omega
    subst i
    subst j
    have hw := adjacent 2 (by decide) fi fj
    norm_num at hw
    linarith
  · interval_cases i <;> interval_cases j <;> first | omega | (norm_num at w₁ w₂; linarith)

end Swanepoel.Charges

/- Finite deletion and separation in Swanepoel, Lemmas 1–3.
All independent sets consist of actual points of the original configuration. -/

open Finset
open scoped EuclideanGeometry

namespace Swanepoel.Deletion

/-- Independent subsets on opposite sides of a separation can be combined. -/
lemma glue {X I J : Finset ℝ²} (hi : I ⊆ X) (hj : J ⊆ X) (hd : Disjoint I J)
    (ii : (I : Set ℝ²).Pairwise (fun x y => dist x y ≠ 1))
    (ij : (J : Set ℝ²).Pairwise (fun x y => dist x y ≠ 1))
    (hcross : ∀ x ∈ I, ∀ y ∈ J, dist x y ≠ 1)
    (hc : 8*X.card ≤ 31*(I.card + J.card)) :
    ∃ S ⊆ X, (S : Set ℝ²).Pairwise (fun x y => dist x y ≠ 1) ∧ 8*X.card ≤ 31*S.card := by
  classical
  refine ⟨I ∪ J, union_subset hi hj, ?_, by rwa [card_union_of_disjoint hd]⟩
  intro x hx y hy hn
  obtain hx | hx := mem_union.mp hx <;> obtain hy | hy := mem_union.mp hy
  · exact ii hx hy hn
  · exact hcross x hx y hy
  · rw [dist_comm]; exact hcross y hy x hx
  · exact ij hx hy hn

/-- In a smallest counterexample, the closed neighbourhood of an independent k-set
has at least 4k vertices whenever k ≤ 8. -/
theorem small_expansion (X : Finset ℝ²)
    (G : Finset ℝ² → Prop)
    (hG : ∀ Y, G Y ↔ ∃ I ⊆ Y, (I : Set ℝ²).Pairwise (fun x y => dist x y ≠ 1) ∧
      8*Y.card ≤ 31*I.card)
    (hbad : ¬ G X) (hmin : ∀ Y ⊆ X, Y.card < X.card → G Y)
    {S : Finset ℝ²} (hs : S ⊆ X) (hi : (S : Set ℝ²).Pairwise (fun x y => dist x y ≠ 1))
    (hk : S.card ≤ 8) : 4*S.card ≤ (X.filter (fun x => x ∈ S ∨ ∃ y ∈ S, dist y x = 1)).card := by
  classical
  let D := X.filter (fun x => x ∈ S ∨ ∃ y ∈ S, dist y x = 1)
  change 4*S.card ≤ D.card
  by_contra! hf
  have hsd : S ⊆ D := fun x hx => mem_filter.mpr ⟨hs hx, Or.inl hx⟩
  have hdx : D ⊆ X := filter_subset _ _
  have hsn : S.card ≤ D.card := card_le_card hsd
  have hdn : D.card ≤ X.card := card_le_card hdx
  have hcard := card_sdiff_of_subset hdx
  obtain ⟨I,hI,iI,hc⟩ := (hG _).mp (hmin (X \ D) sdiff_subset (by omega))
  have hcros (x) (hx : x ∈ S) (y) (hy : y ∈ I) : dist x y ≠ 1 := by
    intro e
    obtain ⟨hyX,hyD⟩ := mem_sdiff.mp (hI hy)
    exact hyD (mem_filter.mpr ⟨hyX, Or.inr ⟨x,hx,e⟩⟩)
  apply hbad
  apply (hG X).mpr
  apply glue hs (hI.trans sdiff_subset) _ hi iI hcros (by omega)
  exact disjoint_left.mpr (fun x hx hy => (mem_sdiff.mp (hI hy)).2 (hsd hx))

/-- A minimal counterexample admits no partition into two nonempty anticomplete parts
and at most one leftover point. This includes disconnected graphs and cut vertices. -/
theorem no_separator (X : Finset ℝ²)
    (G : Finset ℝ² → Prop)
    (hG : ∀ Y, G Y ↔ ∃ I ⊆ Y, (I : Set ℝ²).Pairwise (fun x y => dist x y ≠ 1) ∧
      8*Y.card ≤ 31*I.card)
    (hbad : ¬ G X) (hmin : ∀ Y ⊆ X, Y.card < X.card → G Y)
    {A B : Finset ℝ²} (ha : A ⊆ X) (hb : B ⊆ X) (hna : A.Nonempty) (hnb : B.Nonempty)
    (hab : Disjoint A B) (hrep : (X \ (A ∪ B)).card ≤ 1) :
    ∃ x ∈ A, ∃ y ∈ B, dist x y = 1 := by
  classical
  by_contra! hcross
  have hxA := card_sdiff_of_subset ha
  have hxB := card_sdiff_of_subset hb
  have hcnt := card_le_card (union_subset ha hb)
  rw [card_union_of_disjoint hab] at hcnt
  have hna' := card_pos.mpr hna
  have hnb' := card_pos.mpr hnb
  obtain ⟨I,hi,iI,hI⟩ := (hG _).mp (hmin (X \ B) sdiff_subset (by omega))
  obtain ⟨L,hl,iL,hL⟩ := (hG _).mp (hmin B hb (by omega))
  have hIcapL : Disjoint I L :=
    disjoint_left.mpr (fun x hx hy => (mem_sdiff.mp (hi hx)).2 (hl hy))
  apply hbad
  apply (hG X).mpr
  by_cases hsub : I ⊆ A
  · exact glue (hi.trans sdiff_subset) (hl.trans hb) hIcapL iI iL
      (fun x hx y hy => hcross x (hsub hx) y (hl hy)) (by omega)
  obtain ⟨v,hv,hva⟩ := not_subset.mp hsub
  have hvs := mem_sdiff.mp (hi hv)
  have hvC : v ∈ X \ (A ∪ B) := mem_sdiff.mpr ⟨hvs.1, fun e => (mem_union.mp e).elim hva hvs.2⟩
  have only_v {y : ℝ²} (h : y ∈ X \ (A ∪ B)) : y = v :=
    card_le_one.mp hrep y h v hvC
  obtain ⟨K,hk,iK,hK⟩ := (hG _).mp (hmin A ha (by omega))
  by_cases large : I.card ≤ K.card
  · exact glue (hk.trans ha) (hl.trans hb) (hab.mono hk hl) iK iL
      (fun x hx y hy => hcross x (hk hx) y (hl hy)) (by omega)
  obtain ⟨J,hj,iJ,hJ⟩ := (hG _).mp (hmin (X \ A) sdiff_subset (by omega))
  have haI : I.erase v ⊆ A := by
    intro x hx
    obtain ⟨hxv,hxi⟩ := mem_erase.mp hx
    obtain ⟨hxX,hxB⟩ := mem_sdiff.mp (hi hxi)
    by_contra h
    exact hxv (only_v (mem_sdiff.mpr ⟨hxX,fun e => (mem_union.mp e).elim h hxB⟩))
  have hcros : ∀ x ∈ I.erase v, ∀ y ∈ J, dist x y ≠ 1 := by
    intro x hx y hy
    obtain ⟨hyX,hyA⟩ := mem_sdiff.mp (hj hy)
    by_cases e : y ∈ B
    · exact hcross x (haI hx) y e
    · have hyv := only_v (mem_sdiff.mpr ⟨hyX,fun f => (mem_union.mp f).elim hyA e⟩)
      subst y
      exact iI (mem_erase.mp hx).2 hv (mem_erase.mp hx).1
  refine glue (haI.trans ha) (hj.trans sdiff_subset) ?_ ?_ iJ hcros ?_
  · exact disjoint_left.mpr (fun x hx hy => (mem_sdiff.mp (hj hy)).2 (haI hx))
  · exact iI.mono (by exact_mod_cast (erase_subset v I))
  · rw [card_erase_of_mem hv]
    omega

end Swanepoel.Deletion
open Finset
open scoped EuclideanGeometry
namespace OMA.R_Erdos1066_erdos_1066_variants_swanepoel_R2

/- The finite-set to supremum conversion is adapted from cipher-droid, pending reduction 10257. -/
lemma exact_config (n : ℕ) : ∃ X : Finset (EuclideanSpace ℝ (Fin 2)), X.card = n ∧
    (X : Set (EuclideanSpace ℝ (Fin 2))).Pairwise (fun x y ↦ 1 ≤ dist x y) := by
  classical
  let f : ℕ → (EuclideanSpace ℝ (Fin 2)) := fun t => EuclideanSpace.single 0 (t : ℝ)
  have hf : Function.Injective f := by
    intro a b h
    have hv := congrArg (fun z : (EuclideanSpace ℝ (Fin 2)) => z 0) h
    have hc : (a : ℝ) = (b : ℝ) := by simpa [f, PiLp.single_apply] using hv
    exact_mod_cast hc
  refine ⟨(range n).image f, by rw [card_image_of_injective _ hf, card_range], ?_⟩
  intro x hx y hy hn
  obtain ⟨a, _, rfl⟩ := mem_image.mp (Finset.mem_coe.mp hx)
  obtain ⟨b, _, rfl⟩ := mem_image.mp (Finset.mem_coe.mp hy)
  have hab : a ≠ b := fun h => hn (congrArg f h)
  change (1 : ℝ) ≤ dist (EuclideanSpace.single (0 : Fin 2) (a : ℝ))
    (EuclideanSpace.single (0 : Fin 2) (b : ℝ))
  rw [PiLp.dist_single_same, Real.dist_eq]
  rcases lt_or_gt_of_ne hab with h | h
  · have h' : (a : ℝ) + 1 ≤ b := by exact_mod_cast (Nat.succ_le_of_lt h)
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have h' : (b : ℝ) + 1 ≤ a := by exact_mod_cast (Nat.succ_le_of_lt h)
    rw [abs_of_nonneg (by linarith)]
    linarith

lemma graph_card_of_independent {X S : Finset (EuclideanSpace ℝ (Fin 2))} (hs : S ⊆ X)
    (hi : (S : Set (EuclideanSpace ℝ (Fin 2))).Pairwise (fun x y => dist x y ≠ 1)) :
    S.card ≤ (SimpleGraph.UnitDistancePlaneGraph (X : Set (EuclideanSpace ℝ (Fin 2)))).indepNum := by
  classical
  let T : Finset ((X : Set (EuclideanSpace ℝ (Fin 2)))) := S.subtype (fun p => p ∈ (X : Set (EuclideanSpace ℝ (Fin 2))))
  have hT : (SimpleGraph.UnitDistancePlaneGraph (X : Set (EuclideanSpace ℝ (Fin 2)))).IsIndepSet
      (T : Set ((X : Set (EuclideanSpace ℝ (Fin 2))))) := by
    intro a ha b hb hab h
    have ha' : (a : (EuclideanSpace ℝ (Fin 2))) ∈ S := by simpa [T] using ha
    have hb' : (b : (EuclideanSpace ℝ (Fin 2))) ∈ S := by simpa [T] using hb
    exact hi ha' hb' (fun he => hab (Subtype.ext he)) h
  have hcard : T.card = S.card := by
    rw [Finset.card_subtype]
    congr 1
    exact Finset.filter_true_of_mem (fun p hp => Finset.mem_coe.mpr (hs hp))
  rw [← hcard]
  exact hT.card_le_indepNum

lemma ratio_of_finite_sets
    (h : ∀ X : Finset (EuclideanSpace ℝ (Fin 2)), (X : Set (EuclideanSpace ℝ (Fin 2))).Pairwise (fun x y => 1 ≤ dist x y) →
      ∃ S ⊆ X, (S : Set (EuclideanSpace ℝ (Fin 2))).Pairwise (fun x y => dist x y ≠ 1) ∧ 8*X.card ≤ 31*S.card)
    (n : ℕ) : (8/31 : ℝ) * n ≤ Erdos1066.g n := by
  let V : Set ℕ := {m | ∀ X : Finset (EuclideanSpace ℝ (Fin 2)), X.card = n →
    (X : Set (EuclideanSpace ℝ (Fin 2))).Pairwise (fun x y => 1 ≤ dist x y) →
    m ≤ (SimpleGraph.UnitDistancePlaneGraph (X : Set (EuclideanSpace ℝ (Fin 2)))).indepNum}
  have hmem : (8*n+30)/31 ∈ V := by
    intro X hXn hx
    obtain ⟨S,hs,hi,hc⟩ := h X hx
    have hS := graph_card_of_independent hs hi
    omega
  have hbd : BddAbove V := by
    obtain ⟨X,hXn,hX⟩ := exact_config n
    exact ⟨_, fun m hm => hm X hXn hX⟩
  have hl : (8*n+30)/31 ≤ Erdos1066.g n := le_csSup hbd hmem
  have hnat : 8*n ≤ 31*Erdos1066.g n := by omega
  have hr : (8 : ℝ)*n ≤ 31*(Erdos1066.g n : ℝ) := by exact_mod_cast hnat
  linarith

end OMA.R_Erdos1066_erdos_1066_variants_swanepoel_R2

open Real Finset
open Swanepoel.Charges Swanepoel.Deletion
open scoped EuclideanGeometry Topology

namespace OMA.R_Erdos1066_erdos_1066_variants_swanepoel_R2

lemma exclude (h₁ : H1) (h₂ : H2) (X : Finset ℝ²)
    (hX : (X : Set ℝ²).Pairwise (fun x y => 1 ≤ dist x y))
    (hE : ∀ S ⊆ X, (S : Set ℝ²).Pairwise (fun x y => dist x y ≠ 1) → S.card ≤ 8 →
      4*S.card ≤ (X.filter (fun x => x ∈ S ∨ ∃ y ∈ S, dist y x = 1)).card)
    (hn : X.Nonempty) (hC : ∀ A ⊆ X, ∀ B ⊆ X, A.Nonempty → B.Nonempty → Disjoint A B →
      (X \ (A ∪ B)).card ≤ 1 → ∃ x ∈ A, ∃ y ∈ B, dist x y = 1) : False := by
  classical
  have degrees (v : ℝ²) (hv : v ∈ X) :=
    And.intro (Swanepoel.Hexagon.three_le_degree X hE hv) (Swanepoel.Hexagon.degree_le_six X hX v)
  have common := Swanepoel.Embedding.common_neighbours X
  obtain ⟨p,q,z,arc⟩ := h₁ X hX hE degrees common
    (fun _ ha _ hb _ hv => Swanepoel.Embedding.vertex_on_edge hX ha hb hv)
    (fun _ ha _ hb _ hc _ hd => Swanepoel.Embedding.edges_disjoint hX ha hb hc hd) hn hC
  obtain ⟨r,s,tips,between,first,last⟩ := h₂ X hX hE degrees common hn hC p q z arc
  obtain ⟨_,_,hp,_,_,_,_,hq,hnon,hbudget⟩ := arc
  let t (i : ℕ) := (∠ (q i) (p (i+2)) (q (i+1))) - π/3
  let c (i : ℕ) := q (i+2)
  let x (i : ℕ) := p (i+3)
  let a (i : ℕ) := ∠ (c i) (x i) (r i)
  let b (i : ℕ) := ∠ (c i) (x (i+1)) (s i)
  let f (i : ℕ) := s i ≠ r (i+1)
  have triangle (i : ℕ) (hi : i < 13) :
      q i ∈ X ∧ dist (q i) (p (i+1)) = 1 ∧ dist (q i) (p (i+2)) = 1 := by
    obtain ⟨m,l,u⟩ := hq i hi
    exact ⟨m,(dist_comm ..).trans l,(dist_comm ..).trans u⟩
  have hub (i : ℕ) (hi : i < 7) :
      π/3 ≤ a i + b i ∧ π/3 - 2*b i ≤ t (i+1) ∧ π/3 - 2*a i ≤ t (i+2) := by
    obtain ⟨rm,sm,ru,su,rs,rx,sx,ry,sy,cy,left,right⟩ := tips i hi
    have tl := triangle (i+1) (by omega)
    have tc := triangle (i+2) (by omega)
    have tr := triangle (i+3) (by omega)
    exact hub_angles (c i) (x i) (x (i+1)) (r i) (s i) (q (i+1)) (q (i+3))
      (t (i+1)) (t (i+2)) tc.2.1 tc.2.2 ru su tl.2.2 tr.2.1
      (hX sm rm rs.symm) (hX (hp (i+3) (by omega)) rm rx.symm)
      (hX (hp (i+4) (by omega)) sm sx.symm) (hX tl.1 rm ry.symm) (hX tr.1 sm sy.symm)
      cy left right
  have seam (i : ℕ) (hi : i < 6) (hf : f i) :
      a (i+1) ≤ t (i+1)+t (i+2) ∧ b i ≤ t (i+2)+t (i+3) ∧
      π/3 ≤ t (i+1)+2*t (i+2)+t (i+3) := by
    obtain ⟨_,sm,_,su,_,_,sx,_,_,_,_,_⟩ := tips i (by omega)
    obtain ⟨rm,_,ru,_,_,rx,_,_,_,_,_,_⟩ := tips (i+1) (by omega)
    have tc := triangle (i+2) (by omega)
    have td := triangle (i+3) (by omega)
    apply geometric_seam (x (i+1)) (c i) (c (i+1)) (s i) (r (i+1))
      (t (i+1)) (t (i+2)) (t (i+3)) tc.2.2 td.2.1 su ru
      (hX (hp (i+4) (by omega)) sm sx.symm) (hX (hp (i+4) (by omega)) rm rx.symm)
      (hX sm rm hf) (hnon (i+1) (by omega)) (hnon (i+2) (by omega)) (hnon (i+3) (by omega))
      (hub i (by omega)).2.1 (hub (i+1) (by omega)).2.2
    exact (eq_sub_iff_add_eq).mpr (between i hi hf).symm
  apply two_triples t f hnon hbudget (fun i hi hf => (seam i hi hf).2.2) _ first last
  intro i hi fi fj
  have left := (seam i (by omega) fi).1
  have right := (seam (i+1) (by omega) fj).2.1
  have center := (hub (i+1) (by omega)).1
  change b (i+1) ≤ t (i+3) + t (i+4) at right
  linarith

/-- Induction on the number of points. The residual statements receive the two
structural consequences of minimality, independent of the target bound. -/
theorem main : H1 → H2 → type_of% @Erdos1066.erdos_1066.variants.swanepoel := by
  classical
  intro h₁ h₂
  let G (Y : Finset ℝ²) := ∃ I ⊆ Y, (I : Set ℝ²).Pairwise (fun x y => dist x y ≠ 1) ∧
    8*Y.card ≤ 31*I.card
  have hG (Y) : G Y ↔ _ := Iff.rfl
  have all_good (n : ℕ) : ∀ X : Finset ℝ², X.card = n →
      (X : Set ℝ²).Pairwise (fun x y => 1 ≤ dist x y) → G X := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro X hcard hX
      by_contra hbad
      have hmin (Y : Finset ℝ²) (hy : Y ⊆ X) (hc : Y.card < X.card) : G Y :=
        ih Y.card (by omega) Y rfl (hX.mono (by exact_mod_cast hy))
      have hn : X.Nonempty := by
        by_contra! he
        subst X
        exact hbad ⟨∅,Subset.rfl,by simp,by simp⟩
      apply exclude h₁ h₂ X hX _ hn
      · intro A ha B hb hna hnb hab hc
        exact no_separator X G hG hbad hmin ha hb hna hnb hab hc
      · intro S hs hi hk
        exact small_expansion X G hG hbad hmin hs hi hk
  exact ratio_of_finite_sets (fun X hx => all_good X.card X rfl hx)

end OMA.R_Erdos1066_erdos_1066_variants_swanepoel_R2

