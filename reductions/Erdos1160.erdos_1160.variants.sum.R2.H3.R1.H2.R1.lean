import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R2_H3_R1
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
Split H2 into reusable enumeration bounds that can each fit in one submission.
The root and bounded-width populations share a half of the upper-bound budget;
the central-wide and outer populations receive a quarter each. Higman's lower
bound converts their joint upper bound into the requested two-step growth.
The populations and the constant 192000 are those in the existing reduction
Erdos1160.erdos_1160.variants.sum.R1.H2.R1.H2.R2.
-/
-- Credit: @Thomassien
open Filter Erdos1160 CategoryTheory
open scoped commutatorElement
namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H3_R1_H2_R1
/-- Higman's lower bound, with cleared denominators. -/
def H1 : Prop := ∀ᶠ m : ℕ in atTop,
  2^(2*m^3) ≤ g (2^m)^27 * 2^(13*m^2)
/-- The union of the root and bounded-width populations. -/
def H2 : Prop := ∀ᶠ m : ℕ in atTop,
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let C : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    K = ⊥ ∨ Nat.card F ≤ 2^192000*Nat.card K}
  (2*C.ncard)^27*2^(9*m^2) ≤ 2^(2*m^3)
/-- The central-wide population. -/
def H3 : Prop := ∀ᶠ m : ℕ in atTop,
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let C : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    let d := Nat.log 2 (frattini G).index
    K ≠ ⊥ ∧ 2^192000*Nat.card K < Nat.card F ∧
      (1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d)}
  (4*C.ncard)^27*2^(9*m^2) ≤ 2^(2*m^3)
/-- The outer-rank population. -/
def H4 : Prop := ∀ᶠ m : ℕ in atTop,
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let C : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    let d := Nat.log 2 (frattini G).index
    K ≠ ⊥ ∧ ¬(1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d)}
  (4*C.ncard)^27*2^(9*m^2) ≤ 2^(2*m^3)
lemma count_from_cover {X : Type*} (A B C : Set X)
    (cover : ∀ x, x ∈ A ∨ x ∈ B ∨ x ∈ C) :
    Nat.card X ≤ A.ncard + B.ncard + C.ncard := by
  classical
  by_cases h : Finite X
  · let _ := h
    have he : Set.univ = A ∪ B ∪ C := by
      ext x
      simpa only [Set.mem_univ, Set.mem_union, true_iff, or_assoc] using cover x
    rw [← Set.ncard_univ, he]
    exact (Set.ncard_union_le (A ∪ B) C).trans
      (Nat.add_le_add_right (Set.ncard_union_le A B) _)
  · let _ : Infinite X := not_finite_iff_infinite.mp h
    simp
lemma half_quarter_budget {a b c n f z : ℕ} (hn : n ≤ a+b+c)
    (ha : (2*a)^27*f ≤ z) (hb : (4*b)^27*f ≤ z) (hc : (4*c)^27*f ≤ z) :
    n^27*f ≤ z := by
  let T := max (2*a) (max (4*b) (4*c))
  have ht : T^27*f ≤ z := by
    have he : T = 2*a ∨ T = 4*b ∨ T = 4*c := by dsimp [T]; omega
    rcases he with he | he | he <;> rw [he] <;> assumption
  exact (Nat.mul_le_mul_right f (Nat.pow_le_pow_left (show n ≤ T by dsimp [T]; omega) 27)).trans ht
lemma upper_of_counts : H2 → H3 → H4 → ∀ᶠ m : ℕ in atTop,
    g (2^m)^27 * 2^(9*m^2) ≤ 2^(2*m^3) := by
  intro simple wide outer
  filter_upwards [simple, wide, outer] with m hs hw ho
  classical
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m}
  let B : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    K = ⊥ ∨ Nat.card F ≤ 2^192000*Nat.card K}
  let C : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    let d := Nat.log 2 (frattini G).index
    K ≠ ⊥ ∧ 2^192000*Nat.card K < Nat.card F ∧
      (1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d)}
  let D : Set A := {c | let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    let d := Nat.log 2 (frattini G).index
    K ≠ ⊥ ∧ ¬(1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d)}
  have cover (c : A) : c ∈ B ∨ c ∈ C ∨ c ∈ D := by
    dsimp only [B, C, D, Set.mem_ofPred_eq]
    let G := c.property.choose
    let F := Subgroup.closure (Set.range (fun x : G => x*x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    let d := Nat.log 2 (frattini G).index
    by_cases root : K = ⊥
    · exact .inl (.inl root)
    · by_cases small : Nat.card F ≤ 2^192000*Nat.card K
      · exact .inl (.inr small)
      · by_cases strip : 1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d
        · exact .inr (.inl ⟨root, lt_of_not_ge small, strip⟩)
        · exact .inr (.inr ⟨root, strip⟩)
  have hg : Nat.card A = g (2^m) := by rw [Nat.card_coe_set_eq]; rfl
  rw [← hg]
  exact half_quarter_budget (count_from_cover B C D cover) hs hw ho
lemma exponent_growth {b : ℕ} (hb : 20 ≤ b) :
    27*(2*(b+2)+1) + 2*b^3 + 13*(b+2)^2 ≤ 2*(b+2)^3 + 9*b^2 := by
  nlinarith [Nat.mul_le_mul_left b hb]
lemma compare {b x y : ℕ} (hb : 20 ≤ b)
    (upper : x^27 * 2^(9*b^2) ≤ 2^(2*b^3))
    (lower : 2^(2*(b+2)^3) ≤ y^27 * 2^(13*(b+2)^2)) :
    2^(2*(b+2)+1)*x ≤ y := by
  apply (Nat.pow_le_pow_iff_left (by decide : 27 ≠ 0)).mp
  apply Nat.le_of_mul_le_mul_right (c := 2^(9*b^2)*2^(13*(b+2)^2)) _
    (by positivity)
  calc
    _ = 2^(27*(2*(b+2)+1)) * (x^27 * 2^(9*b^2)) * 2^(13*(b+2)^2) := by
      rw [mul_pow, ← pow_mul]; ring_nf
    _ ≤ 2^(27*(2*(b+2)+1)) * 2^(2*b^3) * 2^(13*(b+2)^2) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ upper)
    _ = 2^(27*(2*(b+2)+1) + 2*b^3 + 13*(b+2)^2) := by rw [pow_add, pow_add]
    _ ≤ 2^(2*(b+2)^3 + 9*b^2) := Nat.pow_le_pow_right (by decide) (exponent_growth hb)
    _ = 2^(2*(b+2)^3)*2^(9*b^2) := pow_add ..
    _ ≤ (y^27*2^(13*(b+2)^2))*2^(9*b^2) := Nat.mul_le_mul_right _ lower
    _ = _ := by ring
theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H3_R1.H2 := by
  intro lower simple wide outer
  obtain ⟨NL, hNL⟩ := eventually_atTop.mp lower
  obtain ⟨NU, hNU⟩ := eventually_atTop.mp (upper_of_counts simple wide outer)
  refine eventually_atTop.mpr ⟨NL+NU+22, fun m hm => ?_⟩
  obtain ⟨b, rfl⟩ : ∃ b, m = b+2 := ⟨m-2, by omega⟩
  have hsub : b+2-2 = b := by omega
  rw [hsub]
  have hpos : g (2^b) ≠ 0 := by
    intro hz
    have hl := hNL b (by omega)
    rw [hz] at hl
    simp at hl
  have hfin : (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = 2^b}).Finite :=
    Set.finite_of_ncard_ne_zero hpos
  have subset : (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = 2^b ∧
        ¬5*b ≤ 6*Nat.log 2 (Subgroup.closure (Set.range (fun x : G => x*x))).index}) ⊆
      Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' {G : FiniteGrp.{0} | Nat.card G = 2^b} := by
    rintro _ ⟨G, hG, rfl⟩
    exact ⟨G, hG.1, rfl⟩
  exact (Nat.mul_le_mul_left _ (Set.ncard_le_ncard subset hfin)).trans
    (compare (by omega) (hNU b (by omega)) (hNL (b+2) (by omega)))
end OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H3_R1_H2_R1
