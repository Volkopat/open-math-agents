import OMAReductions.R_Erdos101_erdos_101_R2
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.Module.Prod
import Mathlib.Tactic.FieldSimp

/-!
# Bounded triangle ratios and addition

This reduction develops the bounded-triangle-ratio step of the four-point
reduction by @ubuwaits. Two applications of graph triangle removal find
common anchors. Their three ratio values determine homogeneous coordinates
on a positive-density subfamily. The remaining input follows from the
high-energy rich-line theorem of Mansfield and Passant, Combinatorica 44
(2024), Theorem 5.4, applied after generic planar projection. The separate
extraction step for arbitrary four-point lines remains open.
-/

namespace OMA.R_Erdos101_erdos_101_R2_H2_R1

open EuclideanGeometry SimpleGraph.TripartiteFromTriangles

/-- Two applications of triangle removal retain a positive-density subfamily and
give a common middle-role anchor and a common last-role anchor. -/
def H1 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ S : Finset ℝ², S.Nonempty →
    ∀ T : Finset (S × S × S), ExplicitDisjoint T → δ * (S.card : ℝ)^2 ≤ T.card →
    let shadow := fun x y z : S =>
      (∃ w, (x,y,w) ∈ T) ∧ (∃ w, (x,w,z) ∈ T) ∧ (∃ w, (w,y,z) ∈ T)
    ∃ (y z : S) (U : Finset (S × S × S)), U ⊆ T ∧ η * (S.card : ℝ)^2 ≤ U.card ∧
      ∀ t ∈ U, shadow t.1 y t.2.2 ∧ shadow t.1 t.2.1 z ∧ shadow t.1 y z

/-- Three scalar choices give three sets of homogeneous representatives of the
same capped projective point set. Their additive triples have zero quadratic density. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ S : Finset ℝ², N ≤ S.card →
    NonCollinearFor 5 (S : Set ℝ²) → ∀ sx sy sz : S → ℝˣ,
    ∀ U : Finset (S × S × S),
    (∀ t ∈ U, (sx t.1 : ℝ) • ((1 : ℝ),(t.1 : ℝ²)) +
      (sy t.2.1 : ℝ) • ((1 : ℝ),(t.2.1 : ℝ²)) =
      (sz t.2.2 : ℝ) • ((1 : ℝ),(t.2.2 : ℝ²))) →
      (U.card : ℝ) < ε * (S.card : ℝ)^2

/-- After two anchor extractions, bounded triangle ratios yield nonzero
vertex scalings and a single positive-size family of ordinary additive triples.
The bound is written as a natural-number product to retain its exact fiber size. -/
theorem balanced_additive_fiber {P V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : P → V) (T : Finset (P × P × P)) (hne : T.Nonempty)
    (a b d : P → P → ℝˣ) (K : Finset ℝˣ) (y₀ z₀ : P)
    (honest : ∀ t ∈ T, (a t.1 t.2.2 : ℝ) + (b t.2.1 t.2.2 : ℝ) = 1 ∧
      (a t.1 t.2.2 : ℝ) • p t.1 + (b t.2.1 t.2.2 : ℝ) • p t.2.1 = p t.2.2 ∧
      d t.1 t.2.1 = b t.2.1 t.2.2 / a t.1 t.2.2)
    (anchors : ∀ t ∈ T,
      a t.1 t.2.2 * d t.1 y₀ / b y₀ t.2.2 ∈ K ∧
      a t.1 z₀ * d t.1 t.2.1 / b t.2.1 z₀ ∈ K ∧
      a t.1 z₀ * d t.1 y₀ / b y₀ z₀ ∈ K) :
    ∃ (sx sy sz : P → ℝˣ) (U : Finset (P × P × P)), U ⊆ T ∧
      T.card ≤ K.card^3 * U.card ∧
      ∀ t ∈ U,
        (sx t.1 : ℝ) • ((1 : ℝ),p t.1) + (sy t.2.1 : ℝ) • ((1 : ℝ),p t.2.1) =
          (sz t.2.2 : ℝ) • ((1 : ℝ),p t.2.2) := by
  classical
  let colors := K ×ˢ (K ×ˢ K)
  let c : P × P × P → ℝˣ × ℝˣ × ℝˣ := fun t =>
    (a t.1 t.2.2 * d t.1 y₀ / b y₀ t.2.2,
     a t.1 z₀ * d t.1 t.2.1 / b t.2.1 z₀,
     a t.1 z₀ * d t.1 y₀ / b y₀ z₀)
  have hmap : ∀ t ∈ T, c t ∈ colors := by simpa [c,colors] using anchors
  obtain ⟨t₀, ht₀⟩ := hne
  have hcols : colors.Nonempty := ⟨_,hmap t₀ ht₀⟩
  let fiber (v : ℝˣ × ℝˣ × ℝˣ) := T.filter fun t => c t = v
  obtain ⟨v, hv, hmax⟩ := colors.exists_max_image (fun v => (fiber v).card) hcols
  have hcard : T.card ≤ colors.card * (fiber v).card := by
    calc
      T.card = ∑ w ∈ colors, (fiber w).card := Finset.card_eq_sum_card_fiberwise hmap
      _ ≤ ∑ _w ∈ colors, (fiber v).card := Finset.sum_le_sum hmax
      _ = _ := by simp
  let sx := fun x => v.1 / d x y₀
  let sy := fun y => (v.1*v.2.1/v.2.2) * (b y z₀/b y₀ z₀)
  let sz := fun z => (b y₀ z)⁻¹
  refine ⟨sx,sy,sz,fiber v,Finset.filter_subset _ _,?_,?_⟩
  · simpa [colors, pow_succ, Nat.mul_assoc] using hcard
  · intro t ht
    obtain ⟨hT, hc⟩ := Finset.mem_filter.mp ht
    obtain ⟨ha,hb,hd⟩ := honest t hT
    have hxa : sx t.1 = sz t.2.2 * a t.1 t.2.2 := by
      simp only [sx, sz, ←hc, c]
      apply Units.ext
      simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_inv_eq_inv_val]
      field_simp
    have hyb : sy t.2.1 = sz t.2.2 * b t.2.1 t.2.2 := by
      simp only [sy, sz, ←hc, c, hd]
      apply Units.ext
      simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_inv_eq_inv_val]
      field_simp
    have hw : (a t.1 t.2.2 : ℝ) • ((1:ℝ),p t.1) + (b t.2.1 t.2.2 : ℝ) • ((1:ℝ),p t.2.1)
        = ((1:ℝ),p t.2.2) := Prod.ext (by simpa using ha) hb
    rw [hxa,hyb,Units.val_mul,Units.val_mul,mul_smul,mul_smul,←smul_add,hw]


theorem main : H1 → H2 → OMA.R_Erdos101_erdos_101_R2.H2 := by
  intro hanchors hadd k δ hδ
  obtain ⟨η,hη,hkeep⟩ := hanchors δ hδ
  let m : ℝ := (k+1 : ℕ)^3
  have hm : 0 < m := by dsimp [m]; positivity
  obtain ⟨N,hN⟩ := hadd (η/m) (div_pos hη hm)
  refine ⟨max N 1, ?_⟩
  intro S hS hcap T hdisj a b d htrue K hk hcolors
  by_contra! hdense
  have hns : 0 < S.card := lt_of_lt_of_le (by decide : 0 < 1) ((le_max_right N 1).trans hS)
  obtain ⟨y,z,U,hsub,hlarge,hA⟩ := hkeep S (Finset.card_pos.mp hns) T hdisj hdense
  have hnR : (0:ℝ) < S.card := by exact_mod_cast hns
  have hUne : U.Nonempty := Finset.card_pos.mp (by
    exact_mod_cast ((mul_pos hη (sq_pos_of_pos hnR)).trans_le hlarge))
  obtain ⟨sx,sy,sz,V,hVU,hV,hbalanced⟩ := balanced_additive_fiber
    (fun x : S => (x : ℝ²)) U hUne a b d K y z (fun t ht => htrue t (hsub ht)) (by
      intro t ht
      obtain ⟨h₁,h₂,h₃⟩ := hA t ht
      exact ⟨hcolors _ _ _ h₁.1 h₁.2.1 h₁.2.2,
        hcolors _ _ _ h₂.1 h₂.2.1 h₂.2.2, hcolors _ _ _ h₃.1 h₃.2.1 h₃.2.2⟩)
  have hsmall := hN S ((le_max_left N 1).trans hS) hcap sx sy sz V hbalanced
  have hcoef : (K.card : ℝ)^3 ≤ m := by
    dsimp [m]
    exact_mod_cast Nat.pow_le_pow_left (hk.trans (Nat.le_succ k)) 3
  have hVr : (U.card : ℝ) ≤ (K.card : ℝ)^3 * V.card := by exact_mod_cast hV
  have hcontr : η * (S.card : ℝ)^2 < η * (S.card : ℝ)^2 := calc
    _ ≤ (U.card : ℝ) := hlarge
    _ ≤ (K.card : ℝ)^3 * V.card := hVr
    _ ≤ m * V.card := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)
    _ < m * ((η/m) * (S.card : ℝ)^2) := mul_lt_mul_of_pos_left hsmall hm
    _ = _ := by field_simp
  exact (lt_irrefl _ hcontr)

end OMA.R_Erdos101_erdos_101_R2_H2_R1
