import OMAReductions.R_Erdos1158_erdos_1158_R1
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.EquivFin
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
Use the bipartite distance graph over a prime field with the split form
xy + z² and a nonsquare radius. Polarization of a putative K₃,₃ gives
two perpendicular two-dimensional spaces in dimension three.

For each point, a nonzero first difference coordinate and any last
difference coordinate determine a unique middle coordinate. This gives
p⁴(p−1) edges on 2p³ vertices. Bertrand's postulate and a power estimate
then give the eventual bound.
-/

namespace OMA.Erdos1158Brown

abbrev Vec (F : Type*) := Fin 3 → F

variable {F : Type*} [Field F]

def qform (u : Vec F) : F := u 0 * u 1 + (u 2)^2

def polar (u d : Vec F) : F := u 0 * d 1 + u 1 * d 0 + 2 * u 2 * d 2

theorem qform_neg (u : Vec F) : qform (-u) = qform u := by
  simp [qform, pow_two]

theorem qform_add_smul (u d : Vec F) (t : F) :
    qform (u + t • d) = qform u + t * polar u d + t^2 * qform d := by
  simp only [qform, polar, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem square_of_isotropic_perp {u d : Vec F}
    (hd : d ≠ 0) (hq : qform d = 0) (hperp : polar u d = 0) : IsSquare (qform u) := by
  by_cases hx : d 0 = 0
  · have hz : d 2 = 0 := by
      have hzSq : (d 2)^2 = 0 := by simpa [qform, hx] using hq
      exact eq_zero_of_pow_eq_zero hzSq
    have hy : d 1 ≠ 0 := by
      intro hy
      apply hd
      funext i
      fin_cases i
      · exact hx
      · exact hy
      · exact hz
    have hu : u 0 = 0 := by
      have hxy : u 0 * d 1 = 0 := by simpa [polar, hx, hz] using hperp
      exact (mul_eq_zero.mp hxy).resolve_right hy
    exact ⟨u 2, by simp [qform, hu, pow_two]⟩
  · let w := d 2 / d 0
    have hw : w * d 0 = d 2 := div_mul_cancel₀ _ hx
    have hdy : d 1 = -(w^2 * d 0) := by
      apply mul_left_cancel₀ hx
      unfold qform at hq
      linear_combination hq + (w * d 0 + d 2) * hw
    have huy : u 1 = w^2 * u 0 - 2 * w * u 2 := by
      apply mul_left_cancel₀ hx
      unfold polar at hperp
      rw [hdy, ← hw] at hperp
      linear_combination hperp
    refine ⟨u 2 - w * u 0, ?_⟩
    rw [qform, huy]
    ring

theorem no_three_aligned {R : F} (hR : ¬ IsSquare R)
    {u d : Vec F} (hd : d ≠ 0) {t : F} (ht : t ≠ 0) (ht' : t ≠ 1)
    (h0 : qform u = R) (h1 : qform (u + d) = R) (h2 : qform (u + t • d) = R) :
    False := by
  have h1' : qform u + polar u d + qform d = R := by
    simpa only [one_smul, one_mul, one_pow] using
      (qform_add_smul u d (1 : F)).symm.trans (by simpa only [one_smul] using h1)
  rw [qform_add_smul] at h2
  have hprod : (t * (t - 1)) * qform d = 0 := by
    linear_combination h2 - t * h1' + (t - 1) * h0
  have hq : qform d = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero ht (sub_ne_zero.mpr ht'))
  have hperp : polar u d = 0 := by
    linear_combination h1' - h0 - hq
  exact hR (h0 ▸ square_of_isotropic_perp hd hq hperp)

theorem not_smul_of_three_on_sphere {R : F} (hR : ¬ IsSquare R)
    {a b c center : Vec F} (hba : b ≠ a) (hca : c ≠ a) (hcb : c ≠ b)
    (ha : qform (a - center) = R) (hb : qform (b - center) = R)
    (hc : qform (c - center) = R) (t : F) : t • (b - a) ≠ c - a := by
  intro h
  have h0 : t ≠ 0 := by
    intro ht
    apply hca
    exact sub_eq_zero.mp (by simpa only [ht, zero_smul] using h.symm)
  have h1 : t ≠ 1 := by
    intro ht
    apply hcb
    exact sub_left_inj.mp (by simpa only [ht, one_smul] using h.symm)
  refine no_three_aligned hR (sub_ne_zero.mpr hba) h0 h1 ha ?_ ?_
  · convert hb using 1
    congr 1
    abel
  · rw [h]
    convert hc using 1
    congr 1
    abel

theorem polar_of_four_edges {R : F} {x₀ x₁ y₀ y₁ : Vec F}
    (h00 : qform (y₀ - x₀) = R) (h01 : qform (y₁ - x₀) = R)
    (h10 : qform (y₀ - x₁) = R) (h11 : qform (y₁ - x₁) = R) :
    polar (x₁ - x₀) (y₁ - y₀) = 0 := by
  simp only [qform, polar, Pi.sub_apply] at *
  linear_combination -h11 + h10 + h01 - h00

end OMA.Erdos1158Brown

namespace OMA.Erdos1158Brown

open Matrix
open scoped Matrix

variable {F : Type*} [Field F]

private def twist (u : Vec F) : Vec F := ![u 1, u 0, 2 * u 2]

private theorem twist_injective (htwo : (2 : F) ≠ 0) :
    Function.Injective (twist : Vec F → Vec F) := by
  intro u v h
  funext i
  fin_cases i
  · exact congrFun h (1 : Fin 3)
  · exact congrFun h (0 : Fin 3)
  · exact mul_left_cancel₀ htwo (congrFun h (2 : Fin 3))

private theorem twist_smul (c : F) (u : Vec F) : twist (c • u) = c • twist u := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · change 2 * (c * u 2) = c * (2 * u 2)
    ring

private theorem twist_zero : twist (0 : Vec F) = 0 := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · change 2 * (0 : F) = 0
    rw [mul_zero]

private theorem twist_dot (u v : Vec F) : twist u ⬝ᵥ v = polar u v := by
  rw [vec3_dotProduct]
  change u 1 * v 0 + u 0 * v 1 + (2 * u 2) * v 2 = polar u v
  unfold polar
  ring

private theorem smul_of_two_perpendicular {u v x : Vec F} (hcross : u ⨯₃ v ≠ 0)
    (hu : u ⬝ᵥ x = 0) (hv : v ⬝ᵥ x = 0) : ∃ c : F, c • (u ⨯₃ v) = x := by
  by_contra! hn
  have hind : LinearIndependent F ![u ⨯₃ v, x] :=
    (LinearIndependent.pair_iff' hcross).mpr hn
  apply crossProduct_ne_zero_iff_linearIndependent.mpr hind
  rw [cross_cross_eq_smul_sub_smul, hu, hv, zero_smul, zero_smul, sub_self]

private theorem no_two_orthogonal_pairs (htwo : (2 : F) ≠ 0) {x x' y y' : Vec F}
    (hx : x ≠ 0) (hxx' : ∀ t : F, t • x ≠ x')
    (hy : y ≠ 0) (hyy' : ∀ t : F, t • y ≠ y')
    (h11 : polar x y = 0) (h12 : polar x y' = 0)
    (h21 : polar x' y = 0) (h22 : polar x' y' = 0) : False := by
  have hcross : y ⨯₃ y' ≠ 0 :=
    crossProduct_ne_zero_iff_linearIndependent.mpr ((LinearIndependent.pair_iff' hy).mpr hyy')
  have hConvert {u v : Vec F} (h : polar u v = 0) : v ⬝ᵥ twist u = 0 :=
    (dotProduct_comm _ _).trans ((twist_dot _ _).trans h)
  obtain ⟨c, hc⟩ := smul_of_two_perpendicular hcross (hConvert h11) (hConvert h12)
  obtain ⟨d, hd⟩ := smul_of_two_perpendicular hcross (hConvert h21) (hConvert h22)
  have hInj := twist_injective htwo
  have hc0 : c ≠ 0 := by
    intro hc0
    have hx0 : twist x = twist (0 : Vec F) := by
      rw [← hc, hc0, zero_smul, twist_zero]
    exact hx (hInj hx0)
  apply hxx' (d / c)
  apply hInj
  rw [twist_smul, ← hc, ← hd, smul_smul, div_mul_cancel₀ _ hc0]

/-- The split nonsquare-distance relation contains no two complete triples. -/
theorem no_bipartite_triples (htwo : (2 : F) ≠ 0) {R : F} (hR : ¬ IsSquare R)
    (a b : Fin 3 → Vec F) (ha : Function.Injective a) (hb : Function.Injective b)
    (h : ∀ i j, qform (b j - a i) = R) : False := by
  have hA (i : Fin 3) : qform (a i - b 0) = R := by
    rw [← qform_neg (a i - b 0), neg_sub]
    exact h i 0
  have ha10 : a 1 ≠ a 0 := ha.ne (by decide)
  have ha20 : a 2 ≠ a 0 := ha.ne (by decide)
  have ha21 : a 2 ≠ a 1 := ha.ne (by decide)
  have hb10 : b 1 ≠ b 0 := hb.ne (by decide)
  have hb20 : b 2 ≠ b 0 := hb.ne (by decide)
  have hb21 : b 2 ≠ b 1 := hb.ne (by decide)
  have hBilinear (i j : Fin 3) : polar (a i - a 0) (b j - b 0) = 0 :=
    polar_of_four_edges (h 0 0) (h 0 j) (h i 0) (h i j)
  exact no_two_orthogonal_pairs htwo (sub_ne_zero.mpr ha10)
    (not_smul_of_three_on_sphere hR ha10 ha20 ha21 (hA 0) (hA 1) (hA 2))
    (sub_ne_zero.mpr hb10)
    (not_smul_of_three_on_sphere hR hb10 hb20 hb21 (h 0 0) (h 0 1) (h 0 2))
    (hBilinear 1 1) (hBilinear 1 2) (hBilinear 2 1) (hBilinear 2 2)

end OMA.Erdos1158Brown

namespace OMA.Erdos1158Brown

open Finset

private abbrev Vertex (F : Type*) := Vec F ⊕ Vec F
private abbrev EdgeIndex (F : Type*) [Field F] := Vec F × (Fˣ × F)

variable {F W : Type*} [Field F]

/-- The first nonzero coordinate and the last coordinate determine the middle coordinate. -/
private def difference (r : F) (d : Fˣ × F) : Vec F :=
  ![(d.1 : F), (r - d.2 ^ 2) / (d.1 : F), d.2]

private theorem qform_difference (r : F) (d : Fˣ × F) : qform (difference r d) = r := by
  change (d.1 : F) * ((r - d.2 ^ 2) / (d.1 : F)) + d.2 ^ 2 = r
  rw [mul_div_cancel₀ _ d.1.ne_zero, sub_add_cancel]

private theorem difference_injective (r : F) : Function.Injective (difference r) := by
  intro d e he
  refine Prod.ext (Units.ext ?_) ?_
  · simpa [difference] using congrFun he 0
  · simpa [difference] using congrFun he 2

section

variable [DecidableEq W]

private def distanceEdge (e : Vertex F ↪ W) (r : F) (i : EdgeIndex F) : Finset W :=
  {e (Sum.inl i.1), e (Sum.inr (i.1 + difference r i.2))}

private def distanceEdges [Fintype F] [DecidableEq F] (e : Vertex F ↪ W) (r : F) : Finset (Finset W) :=
  univ.image (distanceEdge e r)

private theorem distanceEdge_injective (e : Vertex F ↪ W) (r : F) :
    Function.Injective (distanceEdge e r) := by
  intro i j he
  have hleft : e (Sum.inl i.1) ∈ distanceEdge e r j :=
    he ▸ (by simp [distanceEdge])
  have hright : e (Sum.inr (i.1 + difference r i.2)) ∈ distanceEdge e r j :=
    he ▸ (by simp [distanceEdge])
  simp only [distanceEdge, mem_insert, mem_singleton, e.injective.eq_iff, Sum.inr_ne_inl,
    Sum.inl_ne_inr, Sum.inl.injEq, Sum.inr.injEq, false_or, or_false] at hleft hright
  have hr : j.1 + difference r i.2 = j.1 + difference r j.2 := by
    rw [← hleft] at hright ⊢
    exact hright
  exact Prod.ext hleft (difference_injective r (add_left_cancel hr))

private theorem distanceEdges_uniform [Fintype F] [DecidableEq F] (e : Vertex F ↪ W) (r : F) :
    (distanceEdges e r).IsUniform 2 := by
  intro E hE
  obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hE
  exact Finset.card_pair (fun he => Sum.inl_ne_inr (e.injective he))

private theorem card_distanceEdges {p : ℕ} [Fact p.Prime] (e : Vertex (ZMod p) ↪ W)
    (r : ZMod p) : (distanceEdges e r).card = p ^ 4 * (p - 1) := by
  rw [distanceEdges, card_image_of_injective _ (distanceEdge_injective e r)]
  simp only [card_univ, EdgeIndex, Vec, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    ZMod.card, ZMod.card_units]
  ring

end

private def distanceIncident (e : Vertex F ↪ W) (r : F) (u v : W) : Prop :=
  (∃ x y : Vec F, u = e (Sum.inl x) ∧ v = e (Sum.inr y) ∧ qform (y - x) = r) ∨
  (∃ x y : Vec F, v = e (Sum.inl x) ∧ u = e (Sum.inr y) ∧ qform (y - x) = r)

private theorem incident_of_distanceEdge_mem [Fintype F] [DecidableEq F] [DecidableEq W]
    (e : Vertex F ↪ W) (r : F) {u v : W}
    (hne : u ≠ v) (h : ({u, v} : Finset W) ∈ distanceEdges e r) :
    distanceIncident e r u v := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
  have hu : u ∈ distanceEdge e r i := by rw [hi]; simp
  have hv : v ∈ distanceEdge e r i := by rw [hi]; simp
  have hform : qform ((i.1 + difference r i.2) - i.1) = r := by
    rw [add_sub_cancel_left, qform_difference]
  simp only [distanceEdge, mem_insert, mem_singleton] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact (hne (hu.trans hv.symm)).elim
  · exact Or.inl ⟨_, _, hu, hv, hform⟩
  · exact Or.inr ⟨_, _, hv, hu, hform⟩
  · exact (hne (hu.trans hv.symm)).elim

private theorem colored_triples {e : Vertex F ↪ W} {r : F}
    (hgeo : ∀ x y : Fin 3 → Vec F, Function.Injective x → Function.Injective y →
      (∀ i j, qform (y j - x i) = r) → False)
    (u v : Fin 3 → W) (hu : Function.Injective u) (hv : Function.Injective v)
    (h : ∀ i j, distanceIncident e r (u i) (v j))
    {x₀ y₀ : Vec F} (hx₀ : u 0 = e (Sum.inl x₀)) (hy₀ : v 0 = e (Sum.inr y₀)) : False := by
  have hx (i : Fin 3) : ∃ x : Vec F, u i = e (Sum.inl x) := by
    rcases h i 0 with ⟨x, _, hx, _, _⟩ | ⟨_, _, hy, _, _⟩
    · exact ⟨x, hx⟩
    · exact (Sum.inl_ne_inr (e.injective (hy.symm.trans hy₀))).elim
  have hy (j : Fin 3) : ∃ y : Vec F, v j = e (Sum.inr y) := by
    rcases h 0 j with ⟨_, y, _, hy, _⟩ | ⟨_, _, _, hx, _⟩
    · exact ⟨y, hy⟩
    · exact (Sum.inl_ne_inr (e.injective (hx₀.symm.trans hx))).elim
  choose x hx using hx
  choose y hy using hy
  have hxi : Function.Injective x := by
    intro i j hij
    apply hu
    rw [hx i, hx j, hij]
  have hyi : Function.Injective y := by
    intro i j hij
    apply hv
    rw [hy i, hy j, hij]
  apply hgeo x y hxi hyi
  intro i j
  rcases h i j with ⟨x', y', hx', hy', hq⟩ | ⟨_, _, _, hbad, _⟩
  · have heqX := Sum.inl.inj (e.injective ((hx i).symm.trans hx'))
    have heqY := Sum.inr.inj (e.injective ((hy j).symm.trans hy'))
    rwa [heqX, heqY]
  · exact (Sum.inl_ne_inr (e.injective ((hx i).symm.trans hbad))).elim

private theorem distanceEdges_no_K33 [Fintype F] [DecidableEq F] [DecidableEq W]
    (e : Vertex F ↪ W) (r : F)
    (hgeo : ∀ x y : Fin 3 → Vec F, Function.Injective x → Function.Injective y →
      (∀ i j, qform (y j - x i) = r) → False) :
    ¬ (distanceEdges e r).ContainsCompletePartiteHypergraph 2 3 := by
  rintro ⟨f, hf⟩
  have inc (x y : Fin 3) : distanceIncident e r (f (0, x)) (f (1, y)) := by
    let labels : Fin 2 → Fin 3 := fun i => if i = 0 then x else y
    have hp : univ.image (fun i => f (i, labels i)) = {f (0, x), f (1, y)} := by
      ext u
      simp [Fin.exists_fin_two, labels, eq_comm]
    have hn : ((0, x) : Fin 2 × Fin 3) ≠ (1, y) :=
      fun he => (show (0 : Fin 2) ≠ 1 by decide) (congrArg Prod.fst he)
    exact incident_of_distanceEdge_mem e r (fun he => hn (f.injective he)) (hp ▸ hf labels)
  have hu : Function.Injective (fun i : Fin 3 => f (0, i)) :=
    fun _ _ he => congrArg Prod.snd (f.injective he)
  have hv : Function.Injective (fun j : Fin 3 => f (1, j)) :=
    fun _ _ he => congrArg Prod.snd (f.injective he)
  rcases inc 0 0 with ⟨_, _, hleft, hright, _⟩ | ⟨_, _, hleft, hright, _⟩
  · exact colored_triples hgeo _ _ hu hv inc hleft hright
  · exact colored_triples hgeo _ _ hv hu (fun i j => Or.symm (inc j i)) hleft hright

theorem distance_count_le_partite_extremal {p n : ℕ} [Fact p.Prime] (hsize : 2 * p ^ 3 ≤ n)
    (r : ZMod p)
    (hgeo : ∀ x y : Fin 3 → Vec (ZMod p), Function.Injective x → Function.Injective y →
      (∀ i j, qform (y j - x i) = r) → False) :
    p ^ 4 * (p - 1) ≤ Hypergraph.partiteExtremalNumber n 2 3 := by
  classical
  have hcard : Fintype.card (Vertex (ZMod p)) ≤ Fintype.card (Fin n) := by
    simpa [Vertex, Vec, Fintype.card_fun, ZMod.card, two_mul] using hsize
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  rw [Hypergraph.partiteExtremalNumber, Hypergraph.extremalNumber, ← card_distanceEdges e r]
  apply Finset.le_sup
  simp only [Finset.mem_filter]
  refine ⟨Finset.mem_powerset.mpr ?_, distanceEdges_no_K33 e r hgeo⟩
  intro E hE
  exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ E, distanceEdges_uniform e r E hE⟩

end OMA.Erdos1158Brown

namespace OMA.Erdos1158Distance

open Filter

private theorem five_thirds_of_cube (x : ℝ) (hx : 0 ≤ x) :
    (x ^ 3) ^ (5 / 3 : ℝ) = x ^ 5 := by
  calc
    _ = x ^ (5 : ℝ) := by
      rw [← Real.rpow_natCast x 3, ← Real.rpow_mul hx]
      norm_num
    _ = _ := Real.rpow_natCast x 5

theorem eventually_prime_distance_bound {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ 2 < p ∧ 2 * p ^ 3 ≤ n ∧
      (n : ℝ) ^ (5 / 3 - ε) ≤ (p : ℝ) ^ 4 * ((p : ℝ) - 1) := by
  have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (128 : ℕ), htend.eventually_ge_atTop (486 : ℝ)]
    with n hn hlarge
  let m := Nat.nthRoot 3 (n / 16)
  have hm : 2 ≤ m := (Nat.le_nthRoot_iff (by decide : 3 ≠ 0)).mpr
    (by change 8 ≤ n / 16; omega)
  obtain ⟨p, hp, hmp, hpm⟩ :=
    Nat.exists_prime_lt_and_le_two_mul m (by omega)
  have hp2 : 2 < p := hm.trans_lt hmp
  have hmcube : m ^ 3 ≤ n / 16 := Nat.pow_nthRoot_le_iff.mpr (Or.inl (by decide))
  have hsmall : 2 * p ^ 3 ≤ n := by
    calc
      _ ≤ 2 * (2 * m) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpm 3)
      _ = 16 * m ^ 3 := by ring
      _ ≤ 16 * (n / 16) := Nat.mul_le_mul_left _ hmcube
      _ ≤ n := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self n 16
  have hpCube : n / 16 < p ^ 3 := (Nat.nthRoot_lt_iff (by decide : 3 ≠ 0)).mp hmp
  have hbig : n ≤ 27 * p ^ 3 := by
    have h := (Nat.div_lt_iff_lt_mul (by decide : 0 < 16)).mp hpCube
    omega
  have hbigR : (n : ℝ) ≤ (3 * (p : ℝ)) ^ 3 := by
    calc
      _ ≤ 27 * (p : ℝ) ^ 3 := by exact_mod_cast hbig
      _ = _ := by ring
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2.le
  have hcount : 0 ≤ (p : ℝ) ^ 4 * ((p : ℝ) - 1) :=
    mul_nonneg (by positivity) (by linarith)
  have hpow : (n : ℝ) ^ (5 / 3 : ℝ) ≤ 486 * ((p : ℝ) ^ 4 * ((p : ℝ) - 1)) := by
    calc
      _ ≤ ((3 * (p : ℝ)) ^ 3) ^ (5 / 3 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hbigR (by norm_num)
      _ = (3 * (p : ℝ)) ^ 5 := five_thirds_of_cube _ (by positivity)
      _ = (243 * (p : ℝ) ^ 4) * p := by ring
      _ ≤ (243 * (p : ℝ) ^ 4) * (2 * ((p : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  refine ⟨p, hp, hp2, hsmall, ?_⟩
  rw [Real.rpow_sub hnpos]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hnpos _)).mpr
  exact hpow.trans (by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hlarge hcount)

end OMA.Erdos1158Distance

open Filter OMA.Erdos1158Brown OMA.Erdos1158Distance in
theorem OMA.solution : OMA.R_Erdos1158_erdos_1158_R1.H2 := by
  intro ε hε
  have hex : (2 : ℝ) - (3 : ℝ) ^ (1 - (2 : ℝ)) - ε = 5 / 3 - ε := by
    rw [show 1 - (2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
    ring
  change ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ (2 - (3 : ℝ) ^ (1 - (2 : ℝ)) - ε) ≤
      (Hypergraph.partiteExtremalNumber n 2 3 : ℝ)
  rw [hex]
  filter_upwards [eventually_prime_distance_bound hε] with n hn
  obtain ⟨p, hp, hp2, hsize, hbound⟩ := hn
  let _ : Fact p.Prime := ⟨hp⟩
  have hchar : ringChar (ZMod p) ≠ 2 := by
    simpa only [ZMod.ringChar_zmod_n] using hp2.ne'
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hdivZ : (p : ℤ) ∣ (2 : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).mp (by exact_mod_cast hz)
    have hdiv : p ∣ 2 := by exact_mod_cast hdivZ
    exact hp2.not_ge (Nat.le_of_dvd (by decide) hdiv)
  obtain ⟨r, hr⟩ := FiniteField.exists_nonsquare (F := ZMod p) hchar
  have hgraph := distance_count_le_partite_extremal hsize r (no_bipartite_triples htwo hr)
  apply hbound.trans
  have hcast : ((p ^ 4 * (p - 1) : ℕ) : ℝ) ≤ (Hypergraph.partiteExtremalNumber n 2 3 : ℝ) := by
    exact_mod_cast hgraph
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_le, Nat.cast_one] using hcast
