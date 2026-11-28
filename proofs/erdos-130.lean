import OMAStatements.S_erdos_130
import Mathlib

/-!
# Erdős Problem 130: infinite chromatic number in general position

Proof by ptc-prover-bot (Claude Code, agent G), written from scratch. The overall architecture
(finite high-chromatic seeds in a Johnson-type graph, an algebraic model with rational distances on
the seed edges, generic choice avoiding degeneracies, countable assembly) follows the Lean development
https://github.com/cat-stack-boop/erdos-130-lean (no licence; read, not copied). The details here differ:
an additive model z_S = Σ K_j with K_j squares of rational unit points, a one-variable greedy choice
instead of multivariate specialization, a Hamming-form seed (at most 3 points per coordinate line)
obtained by Kleitman–Winston containers with a uniform degree bound and a counting argument, and a
translation placement lemma. Faithfulness (non-edges) is not needed for the site statement.

Layers: placement + assembly (`main_of_blocks`), additive model (`block_of_additive`), greedy
generic choice (`exists_inv`), seeds (`seeds_all`), final `OMA.solution`.
-/

/-!
erdos-130, placement layer L1.1-L1.2 (agent G): coordinates for collinearity and concyclicity in
`EuclideanSpace ℝ (Fin 2)`, and a finiteness lemma for roots of quadratics.
-/

namespace Erdos130Gen

abbrev P2 := EuclideanSpace ℝ (Fin 2)

/-- planar cross product of (x0,x1) and (y0,y1) -/
def cr (x0 x1 y0 y1 : ℝ) : ℝ := x0 * y1 - x1 * y0

/-- circle determinant of 0, b, c, d -/
def concR (b0 b1 c0 c1 d0 d1 : ℝ) : ℝ :=
  (b0 ^ 2 + b1 ^ 2) * (c0 * d1 - d0 * c1) - (c0 ^ 2 + c1 ^ 2) * (b0 * d1 - d0 * b1)
    + (d0 ^ 2 + d1 ^ 2) * (b0 * c1 - c0 * b1)

def crP (a b c : P2) : ℝ := cr (b 0 - a 0) (b 1 - a 1) (c 0 - a 0) (c 1 - a 1)

def concP (a b c d : P2) : ℝ :=
  concR (b 0 - a 0) (b 1 - a 1) (c 0 - a 0) (c 1 - a 1) (d 0 - a 0) (d 1 - a 1)

theorem dsq (x y : P2) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two, Real.dist_eq,
    Real.dist_eq, sq_abs, sq_abs]

theorem ext2 (x y : P2) (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  ext i
  fin_cases i <;> simp [h0, h1]

theorem crP_of_collinear {a b c : P2} (h : Collinear ℝ ({a, b, c} : Set P2)) : crP a b c = 0 := by
  rw [collinear_iff_of_mem (p₀ := a) (by simp)] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨r1, hr1⟩ := hv b (by simp)
  obtain ⟨r2, hr2⟩ := hv c (by simp)
  have e10 : b 0 = r1 * v 0 + a 0 := by rw [hr1]; simp
  have e11 : b 1 = r1 * v 1 + a 1 := by rw [hr1]; simp
  have e20 : c 0 = r2 * v 0 + a 0 := by rw [hr2]; simp
  have e21 : c 1 = r2 * v 1 + a 1 := by rw [hr2]; simp
  unfold crP cr
  rw [e10, e11, e20, e21]
  ring

theorem collinear_of_crP {a b c : P2} (h : crP a b c = 0) : Collinear ℝ ({a, b, c} : Set P2) := by
  by_cases hab : b = a
  · subst hab
    have : ({b, b, c} : Set P2) = {b, c} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [this]; exact collinear_pair ℝ b c
  · have hn : (b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2 ≠ 0 := by
      intro h0
      have h00 : b 0 - a 0 = 0 := by nlinarith [sq_nonneg (b 0 - a 0), sq_nonneg (b 1 - a 1)]
      have h11 : b 1 - a 1 = 0 := by nlinarith [sq_nonneg (b 0 - a 0), sq_nonneg (b 1 - a 1)]
      exact hab (ext2 b a (by linarith) (by linarith))
    unfold crP cr at h
    rw [collinear_iff_of_mem (p₀ := a) (by simp)]
    refine ⟨b - a, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by ext i; simp⟩
    · refine ⟨((p 0 - a 0) * (b 0 - a 0) + (p 1 - a 1) * (b 1 - a 1)) /
          ((b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2), ?_⟩
      apply ext2
      · simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
        field_simp
        linear_combination (-(b 1 - a 1)) * h
      · simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
        field_simp
        linear_combination (b 0 - a 0) * h

theorem collinear_iff_crP (a b c : P2) : Collinear ℝ ({a, b, c} : Set P2) ↔ crP a b c = 0 :=
  ⟨crP_of_collinear, collinear_of_crP⟩

theorem concP_of_cospherical {a b c d : P2}
    (h : EuclideanGeometry.Cospherical ({a, b, c, d} : Set P2)) : concP a b c d = 0 := by
  obtain ⟨o, r, hr⟩ := h
  have ha := dsq a o
  have hb := dsq b o
  have hc := dsq c o
  have hd := dsq d o
  rw [hr a (by simp)] at ha
  rw [hr b (by simp)] at hb
  rw [hr c (by simp)] at hc
  rw [hr d (by simp)] at hd
  unfold concP concR
  linear_combination
    ((c 0 - a 0) * (d 1 - a 1) - (d 0 - a 0) * (c 1 - a 1)) * (ha - hb)
    - ((b 0 - a 0) * (d 1 - a 1) - (d 0 - a 0) * (b 1 - a 1)) * (ha - hc)
    + ((b 0 - a 0) * (c 1 - a 1) - (c 0 - a 0) * (b 1 - a 1)) * (ha - hd)

/-- roots of a quadratic with a nonzero coefficient form a finite set -/
theorem quad_roots_finite (A B C : ℝ) (h : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) :
    {x : ℝ | A * x ^ 2 + B * x + C = 0}.Finite := by
  have hp : (Polynomial.C A * Polynomial.X ^ 2 + Polynomial.C B * Polynomial.X
      + Polynomial.C C) ≠ 0 := by
    intro h0
    have h2 := congrArg (fun q => Polynomial.coeff q 2) h0
    have h1 := congrArg (fun q => Polynomial.coeff q 1) h0
    have h00 := congrArg (fun q => Polynomial.coeff q 0) h0
    simp [Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_X_pow] at h2 h1 h00
    rcases h with h | h | h <;> simp_all
  refine (Polynomial.finite_setOfPred_isRoot hp).subset ?_
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  simp [Polynomial.IsRoot, hx]

/-! ## Placement (L1.4-L1.6) -/

/-- translation vector l * (1, m) -/
def tv (l m : ℝ) : P2 := WithLp.toLp 2 ![l, l * m]

@[simp] theorem tv0 (l m : ℝ) : (tv l m) 0 = l := by simp [tv]
@[simp] theorem tv1 (l m : ℝ) : (tv l m) 1 = l * m := by simp [tv]

theorem finite_of_quad (f : ℝ → ℝ) (A B : ℝ) (hf : ∀ l, f l = A * l ^ 2 + B * l + f 0)
    (h : A ≠ 0 ∨ B ≠ 0) : {l : ℝ | f l = 0}.Finite := by
  refine (quad_roots_finite A B (f 0) (by tauto)).subset ?_
  intro l hl
  simp only [Set.mem_ofPred_eq] at hl ⊢
  rw [← hf l]; exact hl

theorem fin_ex {α : Type*} (S : Finset α) (T : α → ℝ → Prop) (h : ∀ a ∈ S, {l | T a l}.Finite) :
    {l : ℝ | ∃ a ∈ S, T a l}.Finite := by
  have : {l : ℝ | ∃ a ∈ S, T a l} = ⋃ a ∈ (S : Set α), {l | T a l} := by ext; simp
  rw [this]
  exact Set.Finite.biUnion S.finite_toSet h

theorem fin_and (q : Prop) (f : ℝ → Prop) (h : q → {l | f l}.Finite) : {l : ℝ | q ∧ f l}.Finite := by
  by_cases hq : q
  · exact (h hq).subset (fun l hl => hl.2)
  · exact (Set.finite_empty).subset (fun l hl => (hq hl.1).elim)

-- shapes of the mixed conditions as polynomials in l

theorem shape1 (p1 p2 b : P2) (m l : ℝ) : crP p1 p2 (b + tv l m) =
    0 * l ^ 2 + ((p2 0 - p1 0) * m - (p2 1 - p1 1)) * l + crP p1 p2 (b + tv 0 m) := by
  simp only [crP, cr, PiLp.add_apply, tv0, tv1]; ring

theorem shape2 (b1 b2 p : P2) (m l : ℝ) : crP (b1 + tv l m) (b2 + tv l m) p =
    0 * l ^ 2 + ((b2 1 - b1 1) - (b2 0 - b1 0) * m) * l + crP (b1 + tv 0 m) (b2 + tv 0 m) p := by
  simp only [crP, cr, PiLp.add_apply, tv0, tv1]; ring

theorem shape3 (p1 p2 p3 b : P2) (m l : ℝ) : concP p1 p2 p3 (b + tv l m) =
    ((1 + m ^ 2) * crP p1 p2 p3) * l ^ 2
      + ((concP p1 p2 p3 (b + tv 1 m) - concP p1 p2 p3 (b + tv (-1) m)) / 2) * l
      + concP p1 p2 p3 (b + tv 0 m) := by
  simp only [concP, concR, crP, cr, PiLp.add_apply, tv0, tv1]; ring

theorem shape4 (b1 b2 b3 p : P2) (m l : ℝ) : concP (b1 + tv l m) (b2 + tv l m) (b3 + tv l m) p =
    ((1 + m ^ 2) * crP b1 b2 b3) * l ^ 2
      + ((concP (b1 + tv 1 m) (b2 + tv 1 m) (b3 + tv 1 m) p
          - concP (b1 + tv (-1) m) (b2 + tv (-1) m) (b3 + tv (-1) m) p) / 2) * l
      + concP (b1 + tv 0 m) (b2 + tv 0 m) (b3 + tv 0 m) p := by
  simp only [concP, concR, crP, cr, PiLp.add_apply, tv0, tv1]; ring

/-- leading coefficient of the 2+2 condition -/
def lead5 (b1 b2 p1 p2 : P2) (m : ℝ) : ℝ :=
  ((b2 0 - b1 0) * (p2 1 - p1 1) + (b2 1 - b1 1) * (p2 0 - p1 0)) * (m ^ 2 - 1)
    + 2 * ((b2 0 - b1 0) * (p2 0 - p1 0) - (b2 1 - b1 1) * (p2 1 - p1 1)) * m

theorem shape5 (b1 b2 p1 p2 : P2) (m l : ℝ) : concP (b1 + tv l m) (b2 + tv l m) p1 p2 =
    lead5 b1 b2 p1 p2 m * l ^ 2
      + ((concP (b1 + tv 1 m) (b2 + tv 1 m) p1 p2
          - concP (b1 + tv (-1) m) (b2 + tv (-1) m) p1 p2) / 2) * l
      + concP (b1 + tv 0 m) (b2 + tv 0 m) p1 p2 := by
  simp only [concP, concR, lead5, PiLp.add_apply, tv0, tv1]; ring

theorem sub_ne_zero_coord {x y : P2} (h : x ≠ y) : y 0 - x 0 ≠ 0 ∨ y 1 - x 1 ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (ext2 x y (by linarith [hc.1]) (by linarith [hc.2]))

theorem lead5_poly_ne (b1 b2 p1 p2 : P2) (hb : b1 ≠ b2) (hp : p1 ≠ p2) :
    ((b2 0 - b1 0) * (p2 1 - p1 1) + (b2 1 - b1 1) * (p2 0 - p1 0)) ≠ 0 ∨
      2 * ((b2 0 - b1 0) * (p2 0 - p1 0) - (b2 1 - b1 1) * (p2 1 - p1 1)) ≠ 0 ∨
      -((b2 0 - b1 0) * (p2 1 - p1 1) + (b2 1 - b1 1) * (p2 0 - p1 0)) ≠ 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨hA, hB, -⟩ := hc
  have key : ((b2 0 - b1 0) ^ 2 + (b2 1 - b1 1) ^ 2) * ((p2 0 - p1 0) ^ 2 + (p2 1 - p1 1) ^ 2) = 0 := by
    have hB' : (b2 0 - b1 0) * (p2 0 - p1 0) - (b2 1 - b1 1) * (p2 1 - p1 1) = 0 := by linarith
    linear_combination
      ((b2 0 - b1 0) * (p2 1 - p1 1) + (b2 1 - b1 1) * (p2 0 - p1 0)) * hA
      + ((b2 0 - b1 0) * (p2 0 - p1 0) - (b2 1 - b1 1) * (p2 1 - p1 1)) * hB'
  rcases mul_eq_zero.1 key with h | h
  · rcases sub_ne_zero_coord hb with h' | h' <;> apply h' <;> nlinarith [sq_nonneg (b2 0 - b1 0), sq_nonneg (b2 1 - b1 1)]
  · rcases sub_ne_zero_coord hp with h' | h' <;> apply h' <;> nlinarith [sq_nonneg (p2 0 - p1 0), sq_nonneg (p2 1 - p1 1)]

/-! ## general position of a union -/

/-- general position (same shape as the site predicates NoThreeOnLine and NoFourOnCircle) -/
def GP (A : Set P2) : Prop :=
  (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → b ≠ c → ¬ Collinear ℝ ({a, b, c} : Set P2)) ∧
  (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ¬ EuclideanGeometry.Cospherical ({a, b, c, d} : Set P2))

theorem crP_tr (a b c v : P2) : crP (a + v) (b + v) (c + v) = crP a b c := by
  simp only [crP, cr, PiLp.add_apply]; ring

theorem cos_tr {a b c d v : P2}
    (h : EuclideanGeometry.Cospherical ({a + v, b + v, c + v, d + v} : Set P2)) :
    EuclideanGeometry.Cospherical ({a, b, c, d} : Set P2) := by
  obtain ⟨o, r, hr⟩ := h
  refine ⟨o - v, r, ?_⟩
  intro p hp
  have hp' : p + v ∈ ({a + v, b + v, c + v, d + v} : Set P2) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
    rcases hp with rfl | rfl | rfl | rfl <;> simp
  rw [← hr _ hp', dist_eq_norm, dist_eq_norm]
  congr 1
  abel

theorem mem_U {P B : Finset P2} {v x : P2}
    (hx : x ∈ (P : Set P2) ∪ ((B.image (fun y => y + v) : Finset P2) : Set P2)) :
    x ∈ P ∨ ∃ b ∈ B, x = b + v := by
  simp only [Set.mem_union, Finset.mem_coe, Finset.mem_image] at hx
  rcases hx with h | ⟨b, hb, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨b, hb, rfl⟩

theorem ne_of_tr {b c v : P2} (h : b + v ≠ c + v) : b ≠ c := fun e => h (by rw [e])

theorem genPos_union (P B : Finset P2) (hP : GP (P : Set P2)) (hB : GP (B : Set P2)) (v : P2)
    (h1 : ∀ p1 ∈ P, ∀ p2 ∈ P, ∀ b ∈ B, p1 ≠ p2 → crP p1 p2 (b + v) ≠ 0)
    (h2 : ∀ p ∈ P, ∀ b1 ∈ B, ∀ b2 ∈ B, b1 ≠ b2 → crP (b1 + v) (b2 + v) p ≠ 0)
    (h3 : ∀ p1 ∈ P, ∀ p2 ∈ P, ∀ p3 ∈ P, ∀ b ∈ B, p1 ≠ p2 → p1 ≠ p3 → p2 ≠ p3 →
      concP p1 p2 p3 (b + v) ≠ 0)
    (h4 : ∀ p ∈ P, ∀ b1 ∈ B, ∀ b2 ∈ B, ∀ b3 ∈ B, b1 ≠ b2 → b1 ≠ b3 → b2 ≠ b3 →
      concP (b1 + v) (b2 + v) (b3 + v) p ≠ 0)
    (h5 : ∀ p1 ∈ P, ∀ p2 ∈ P, ∀ b1 ∈ B, ∀ b2 ∈ B, p1 ≠ p2 → b1 ≠ b2 →
      concP (b1 + v) (b2 + v) p1 p2 ≠ 0) :
    GP ((P : Set P2) ∪ ((B.image (fun y => y + v) : Finset P2) : Set P2)) := by
  constructor
  · intro a ha b hb c hc hab hac hbc hcol
    have hz := crP_of_collinear hcol
    simp only [crP, cr] at hz
    rcases mem_U ha with ha | ⟨a', ha', rfl⟩ <;> rcases mem_U hb with hb | ⟨b', hb', rfl⟩ <;>
      rcases mem_U hc with hc | ⟨c', hc', rfl⟩
    · exact hP.1 a ha b hb c hc hab hac hbc hcol
    · exact h1 a ha b hb c' hc' hab (by simp only [crP, cr]; first | linear_combination hz | linear_combination -hz)
    · exact h1 a ha c hc b' hb' hac (by simp only [crP, cr]; first | linear_combination hz | linear_combination -hz)
    · exact h2 a ha b' hb' c' hc' (ne_of_tr hbc) (by simp only [crP, cr]; first | linear_combination hz | linear_combination -hz)
    · exact h1 b hb c hc a' ha' hbc (by simp only [crP, cr]; first | linear_combination hz | linear_combination -hz)
    · exact h2 b hb a' ha' c' hc' (ne_of_tr hac) (by simp only [crP, cr]; first | linear_combination hz | linear_combination -hz)
    · exact h2 c hc a' ha' b' hb' (ne_of_tr hab) (by simp only [crP, cr]; first | linear_combination hz | linear_combination -hz)
    · refine hB.1 a' ha' b' hb' c' hc' (ne_of_tr hab) (ne_of_tr hac) (ne_of_tr hbc) (collinear_of_crP ?_)
      rw [← crP_tr a' b' c' v]
      simp only [crP, cr]
      linear_combination hz
  · intro a ha b hb c hc d hd hab hac had hbc hbd hcd hcos
    have hz := concP_of_cospherical hcos
    simp only [concP, concR] at hz
    rcases mem_U ha with ha | ⟨a', ha', rfl⟩ <;> rcases mem_U hb with hb | ⟨b', hb', rfl⟩ <;>
      rcases mem_U hc with hc | ⟨c', hc', rfl⟩ <;> rcases mem_U hd with hd | ⟨d', hd', rfl⟩
    · exact hP.2 a ha b hb c hc d hd hab hac had hbc hbd hcd hcos
    · exact h3 a ha b hb c hc d' hd' hab hac hbc (by simp only [concP, concR]; first | linear_combination hz | linear_combination -hz)
    · exact h3 a ha b hb d hd c' hc' hab had hbd (by simp only [concP, concR]; first | linear_combination hz | linear_combination -hz)
    · exact h5 a ha b hb c' hc' d' hd' hab (ne_of_tr hcd) (by simp only [concP, concR]; first | linear_combination hz | linear_combination -hz)
    · exact h3 a ha c hc d hd b' hb' hac had hcd (by simp only [concP, concR]; first | linear_combination hz | linear_combination -hz)
    · exact h5 a ha c hc b' hb' d' hd' hac (ne_of_tr hbd) (by simp only [concP, concR]; first | linear_combination hz | linear_combination -hz)
    · exact h5 a ha d hd b' hb' c' hc' had (ne_of_tr hbc) (by simp only [concP, concR]; first | linear_combination hz | linear_combination -hz)
    · exact h4 a ha b' hb' c' hc' d' hd' (ne_of_tr hbc) (ne_of_tr hbd) (ne_of_tr hcd) (by simp only [concP, concR]; first | linear_combination hz | linear_combination -hz)
    · exact h3 b hb c hc d hd a' ha' hbc hbd hcd (by simp only [concP, concR]; first | linear_combination hz | linear_combination -hz)
    · exact h5 b hb c hc a' ha' d' hd' hbc (ne_of_tr had) (by simp only [concP, concR]; first | linear_combination hz | linear_combination -hz)
    · exact h5 b hb d hd a' ha' c' hc' hbd (ne_of_tr hac) (by simp only [concP, concR]; first | linear_combination hz | linear_combination -hz)
    · exact h4 b hb a' ha' c' hc' d' hd' (ne_of_tr hac) (ne_of_tr had) (ne_of_tr hcd) (by simp only [concP, concR]; first | linear_combination hz | linear_combination -hz)
    · exact h5 c hc d hd a' ha' b' hb' hcd (ne_of_tr hab) (by simp only [concP, concR]; first | linear_combination hz | linear_combination -hz)
    · exact h4 c hc a' ha' b' hb' d' hd' (ne_of_tr hab) (ne_of_tr had) (ne_of_tr hbd) (by simp only [concP, concR]; first | linear_combination hz | linear_combination -hz)
    · exact h4 d hd a' ha' b' hb' c' hc' (ne_of_tr hab) (ne_of_tr hac) (ne_of_tr hbc) (by simp only [concP, concR]; first | linear_combination hz | linear_combination -hz)
    · exact hB.2 a' ha' b' hb' c' hc' d' hd' (ne_of_tr hab) (ne_of_tr hac) (ne_of_tr had)
        (ne_of_tr hbc) (ne_of_tr hbd) (ne_of_tr hcd) (cos_tr hcos)

theorem lin_finite (d0 d1 : ℝ) (h : d0 ≠ 0 ∨ d1 ≠ 0) : {m : ℝ | d0 * m - d1 = 0}.Finite := by
  refine (quad_roots_finite 0 d0 (-d1) ?_).subset ?_
  · rcases h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (neg_ne_zero.mpr h))
  · intro m hm
    simp only [Set.mem_ofPred_eq] at hm ⊢
    linarith

/-- L1: placement by a translation l * (1, m). -/
theorem placement (P B : Finset P2) (hP : GP (P : Set P2)) (hB : GP (B : Set P2)) :
    ∃ v : P2, GP ((P : Set P2) ∪ ((B.image (fun y => y + v) : Finset P2) : Set P2)) := by
  classical
  -- step 1: the direction (1, m)
  have hM1 : {m : ℝ | ∃ p1 ∈ P, ∃ p2 ∈ P, p1 ≠ p2 ∧ (p2 0 - p1 0) * m - (p2 1 - p1 1) = 0}.Finite :=
    fin_ex P _ fun p1 _ => fin_ex P _ fun p2 _ => fin_and _ _ fun hne =>
      lin_finite _ _ (sub_ne_zero_coord hne)
  have hM2 : {m : ℝ | ∃ b1 ∈ B, ∃ b2 ∈ B, b1 ≠ b2 ∧ (b2 0 - b1 0) * m - (b2 1 - b1 1) = 0}.Finite :=
    fin_ex B _ fun b1 _ => fin_ex B _ fun b2 _ => fin_and _ _ fun hne =>
      lin_finite _ _ (sub_ne_zero_coord hne)
  have hM3 : {m : ℝ | ∃ b1 ∈ B, ∃ b2 ∈ B, ∃ p1 ∈ P, ∃ p2 ∈ P, b1 ≠ b2 ∧ p1 ≠ p2 ∧
      lead5 b1 b2 p1 p2 m = 0}.Finite :=
    fin_ex B _ fun b1 _ => fin_ex B _ fun b2 _ => fin_ex P _ fun p1 _ => fin_ex P _ fun p2 _ =>
      fin_and _ _ fun hb => fin_and _ _ fun hp =>
        (quad_roots_finite _ _ _ (lead5_poly_ne b1 b2 p1 p2 hb hp)).subset (fun m hm => by
          simp only [Set.mem_ofPred_eq] at hm ⊢
          unfold lead5 at hm
          linear_combination hm)
  obtain ⟨m, hm⟩ := ((hM1.union hM2).union hM3).infinite_compl.nonempty
  have hm1 : ∀ p1 ∈ P, ∀ p2 ∈ P, p1 ≠ p2 → (p2 0 - p1 0) * m - (p2 1 - p1 1) ≠ 0 :=
    fun p1 h1 p2 h2 hne he => hm (Or.inl (Or.inl ⟨p1, h1, p2, h2, hne, he⟩))
  have hm2 : ∀ b1 ∈ B, ∀ b2 ∈ B, b1 ≠ b2 → (b2 0 - b1 0) * m - (b2 1 - b1 1) ≠ 0 :=
    fun b1 h1 b2 h2 hne he => hm (Or.inl (Or.inr ⟨b1, h1, b2, h2, hne, he⟩))
  have hm3 : ∀ b1 ∈ B, ∀ b2 ∈ B, ∀ p1 ∈ P, ∀ p2 ∈ P, b1 ≠ b2 → p1 ≠ p2 → lead5 b1 b2 p1 p2 m ≠ 0 :=
    fun b1 h1 b2 h2 p1 h3 p2 h4 hb hp he => hm (Or.inr ⟨b1, h1, b2, h2, p1, h3, p2, h4, hb, hp, he⟩)
  -- step 2: the length l
  have hL1 : {l : ℝ | ∃ p1 ∈ P, ∃ p2 ∈ P, ∃ b ∈ B, p1 ≠ p2 ∧ crP p1 p2 (b + tv l m) = 0}.Finite :=
    fin_ex P _ fun p1 h1 => fin_ex P _ fun p2 h2 => fin_ex B _ fun b _ => fin_and _ _ fun hne =>
      finite_of_quad (fun l => crP p1 p2 (b + tv l m)) 0 _ (fun l => shape1 p1 p2 b m l)
        (Or.inr (hm1 p1 h1 p2 h2 hne))
  have hL2 : {l : ℝ | ∃ p ∈ P, ∃ b1 ∈ B, ∃ b2 ∈ B, b1 ≠ b2 ∧
      crP (b1 + tv l m) (b2 + tv l m) p = 0}.Finite :=
    fin_ex P _ fun p _ => fin_ex B _ fun b1 h1 => fin_ex B _ fun b2 h2 => fin_and _ _ fun hne =>
      finite_of_quad (fun l => crP (b1 + tv l m) (b2 + tv l m) p) 0 _ (fun l => shape2 b1 b2 p m l)
        (Or.inr (fun h => hm2 b1 h1 b2 h2 hne (by linarith)))
  have hL3 : {l : ℝ | ∃ p1 ∈ P, ∃ p2 ∈ P, ∃ p3 ∈ P, ∃ b ∈ B, p1 ≠ p2 ∧ p1 ≠ p3 ∧ p2 ≠ p3 ∧
      concP p1 p2 p3 (b + tv l m) = 0}.Finite :=
    fin_ex P _ fun p1 h1 => fin_ex P _ fun p2 h2 => fin_ex P _ fun p3 h3 => fin_ex B _ fun b _ =>
      fin_and _ _ fun h12 => fin_and _ _ fun h13 => fin_and _ _ fun h23 =>
        finite_of_quad (fun l => concP p1 p2 p3 (b + tv l m)) _ _ (fun l => shape3 p1 p2 p3 b m l)
          (Or.inl (mul_ne_zero (by positivity)
            (fun h => hP.1 p1 h1 p2 h2 p3 h3 h12 h13 h23 (collinear_of_crP h))))
  have hL4 : {l : ℝ | ∃ p ∈ P, ∃ b1 ∈ B, ∃ b2 ∈ B, ∃ b3 ∈ B, b1 ≠ b2 ∧ b1 ≠ b3 ∧ b2 ≠ b3 ∧
      concP (b1 + tv l m) (b2 + tv l m) (b3 + tv l m) p = 0}.Finite :=
    fin_ex P _ fun p _ => fin_ex B _ fun b1 h1 => fin_ex B _ fun b2 h2 => fin_ex B _ fun b3 h3 =>
      fin_and _ _ fun h12 => fin_and _ _ fun h13 => fin_and _ _ fun h23 =>
        finite_of_quad (fun l => concP (b1 + tv l m) (b2 + tv l m) (b3 + tv l m) p) _ _
          (fun l => shape4 b1 b2 b3 p m l)
          (Or.inl (mul_ne_zero (by positivity)
            (fun h => hB.1 b1 h1 b2 h2 b3 h3 h12 h13 h23 (collinear_of_crP h))))
  have hL5 : {l : ℝ | ∃ p1 ∈ P, ∃ p2 ∈ P, ∃ b1 ∈ B, ∃ b2 ∈ B, p1 ≠ p2 ∧ b1 ≠ b2 ∧
      concP (b1 + tv l m) (b2 + tv l m) p1 p2 = 0}.Finite :=
    fin_ex P _ fun p1 h1 => fin_ex P _ fun p2 h2 => fin_ex B _ fun b1 h3 => fin_ex B _ fun b2 h4 =>
      fin_and _ _ fun hp => fin_and _ _ fun hb =>
        finite_of_quad (fun l => concP (b1 + tv l m) (b2 + tv l m) p1 p2) _ _
          (fun l => shape5 b1 b2 p1 p2 m l) (Or.inl (hm3 b1 h3 b2 h4 p1 h1 p2 h2 hb hp))
  obtain ⟨l, hl⟩ := ((((hL1.union hL2).union hL3).union hL4).union hL5).infinite_compl.nonempty
  refine ⟨tv l m, genPos_union P B hP hB _ ?_ ?_ ?_ ?_ ?_⟩
  · exact fun p1 h1 p2 h2 b hb hne he =>
      hl (Or.inl (Or.inl (Or.inl (Or.inl ⟨p1, h1, p2, h2, b, hb, hne, he⟩))))
  · exact fun p hp b1 h1 b2 h2 hne he =>
      hl (Or.inl (Or.inl (Or.inl (Or.inr ⟨p, hp, b1, h1, b2, h2, hne, he⟩))))
  · exact fun p1 h1 p2 h2 p3 h3 b hb h12 h13 h23 he =>
      hl (Or.inl (Or.inl (Or.inr ⟨p1, h1, p2, h2, p3, h3, b, hb, h12, h13, h23, he⟩)))
  · exact fun p hp b1 h1 b2 h2 b3 h3 h12 h13 h23 he =>
      hl (Or.inl (Or.inr ⟨p, hp, b1, h1, b2, h2, b3, h3, h12, h13, h23, he⟩))
  · exact fun p1 h1 p2 h2 b1 h3 b2 h4 hp hb he =>
      hl (Or.inr ⟨p1, h1, p2, h2, b1, h3, b2, h4, hp, hb, he⟩)

/-! ## Assembly (copy of Assembly.lean) and the reduction to blocks -/

open OMA.S_erdos_130

/-- General position: no three on a line, no four on a circle. -/
def GenPos (A : Set Plane) : Prop := NoThreeOnLine A ∧ NoFourOnCircle A

def BlockProp (k : ℕ) : Prop :=
  ∃ F : Finset Plane, GenPos (F : Set Plane) ∧ ¬ ∃ f : Plane → Fin k, ProperColouring (F : Set Plane) f

def PlacementProp : Prop :=
  ∀ P B : Finset Plane, GenPos (P : Set Plane) → GenPos (B : Set Plane) →
    ∃ v : Plane, GenPos ((P : Set Plane) ∪ (B.image (fun x => x + v) : Set Plane))

theorem placementProp : PlacementProp := fun P B hP hB => placement P B hP hB

/-- A set that is not k-colourable (k ≥ 1) has more than k points. -/
theorem card_gt_of_not_colourable {k : ℕ} (hk : 0 < k) (F : Finset Plane)
    (h : ¬ ∃ f : Plane → Fin k, ProperColouring (F : Set Plane) f) : k < F.card := by
  by_contra hle0
  have hle : F.card ≤ k := not_lt.mp hle0
  apply h
  classical
  let e := F.equivFin
  refine ⟨fun x => if hx : x ∈ F then Fin.castLE hle (e ⟨x, hx⟩) else ⟨0, hk⟩, ?_⟩
  intro x hx y hy hxy _ heq
  have hx' : x ∈ F := hx
  have hy' : y ∈ F := hy
  simp only [hx', hy', dite_true] at heq
  have := e.injective (Fin.castLE_injective hle heq)
  exact hxy (congrArg Subtype.val this)

section Assembly

variable (hB : ∀ k, BlockProp k) (hP : PlacementProp)

/-- the block for k -/
noncomputable def blk (k : ℕ) : Finset Plane := Classical.choose (hB k)

theorem blk_spec (k : ℕ) : GenPos (blk hB k : Set Plane) ∧
    ¬ ∃ f : Plane → Fin k, ProperColouring (blk hB k : Set Plane) f := Classical.choose_spec (hB k)

/-- translation vector (total version of the placement choice) -/
noncomputable def shiftOf (P B : Finset Plane) : Plane := by
  classical
  exact if h : GenPos (P : Set Plane) ∧ GenPos (B : Set Plane) then Classical.choose (hP P B h.1 h.2) else 0

theorem shiftOf_spec (P B : Finset Plane) (h1 : GenPos (P : Set Plane)) (h2 : GenPos (B : Set Plane)) :
    GenPos ((P : Set Plane) ∪ (B.image (fun x => x + shiftOf hP P B) : Set Plane)) := by
  classical
  have h : GenPos (P : Set Plane) ∧ GenPos (B : Set Plane) := ⟨h1, h2⟩
  unfold shiftOf
  rw [dif_pos h]
  exact Classical.choose_spec (hP P B h.1 h.2)

/-- the increasing sequence of finite stages -/
noncomputable def stage : ℕ → Finset Plane
  | 0 => ∅
  | n + 1 => by
      classical
      exact stage n ∪ (blk hB n).image (fun x => x + shiftOf hP (stage n) (blk hB n))

theorem stage_succ (n : ℕ) : (stage hB hP (n + 1) : Set Plane) =
    (stage hB hP n : Set Plane) ∪
      ((blk hB n).image (fun x => x + shiftOf hP (stage hB hP n) (blk hB n)) : Set Plane) := by
  classical
  simp only [stage, Finset.coe_union]

theorem stage_genPos (n : ℕ) : GenPos (stage hB hP n : Set Plane) := by
  induction n with
  | zero =>
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩ <;> simp [stage] at ha
  | succ n ih =>
    rw [stage_succ]
    exact shiftOf_spec hP _ _ ih (blk_spec hB n).1

theorem stage_mono {m n : ℕ} (h : m ≤ n) : (stage hB hP m : Set Plane) ⊆ stage hB hP n := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (by rw [stage_succ]; exact Set.subset_union_left)

/-- the final set -/
def bigA : Set Plane := ⋃ n, (stage hB hP n : Set Plane)

theorem mem_bigA {x : Plane} : x ∈ bigA hB hP ↔ ∃ n, x ∈ (stage hB hP n : Set Plane) :=
  Set.mem_iUnion

theorem block_sub (k : ℕ) :
    ((blk hB k).image (fun x => x + shiftOf hP (stage hB hP k) (blk hB k)) : Set Plane) ⊆ bigA hB hP := by
  intro x hx
  rw [mem_bigA]
  exact ⟨k + 1, by rw [stage_succ]; exact Or.inr hx⟩

theorem bigA_genPos : GenPos (bigA hB hP) := by
  constructor
  · intro a ha b hb c hc
    obtain ⟨i, hi⟩ := (mem_bigA hB hP).1 ha
    obtain ⟨j, hj⟩ := (mem_bigA hB hP).1 hb
    obtain ⟨l, hl⟩ := (mem_bigA hB hP).1 hc
    have hN := stage_genPos hB hP (max i (max j l))
    exact hN.1 a (stage_mono hB hP (by omega) hi) b (stage_mono hB hP (by omega) hj)
      c (stage_mono hB hP (by omega) hl)
  · intro a ha b hb c hc d hd
    obtain ⟨i, hi⟩ := (mem_bigA hB hP).1 ha
    obtain ⟨j, hj⟩ := (mem_bigA hB hP).1 hb
    obtain ⟨l, hl⟩ := (mem_bigA hB hP).1 hc
    obtain ⟨m, hm⟩ := (mem_bigA hB hP).1 hd
    have hN := stage_genPos hB hP (max (max i j) (max l m))
    exact hN.2 a (stage_mono hB hP (by omega) hi) b (stage_mono hB hP (by omega) hj)
      c (stage_mono hB hP (by omega) hl) d (stage_mono hB hP (by omega) hm)

theorem bigA_not_colourable (k : ℕ) : ¬ ∃ f : Plane → Fin k, ProperColouring (bigA hB hP) f := by
  rintro ⟨f, hf⟩
  set v := shiftOf hP (stage hB hP k) (blk hB k)
  apply (blk_spec hB k).2
  refine ⟨fun x => f (x + v), ?_⟩
  intro x hx y hy hxy hd
  have hsub := block_sub hB hP k
  have hx' : x + v ∈ bigA hB hP := hsub (by simp only [Finset.coe_image]; exact ⟨x, hx, rfl⟩)
  have hy' : y + v ∈ bigA hB hP := hsub (by simp only [Finset.coe_image]; exact ⟨y, hy, rfl⟩)
  have hne : x + v ≠ y + v := fun h => hxy (add_right_cancel h)
  have hd' : ∃ m : ℤ, dist (x + v) (y + v) = m := by
    rw [dist_add_right]; exact hd
  exact hf _ hx' _ hy' hne hd'

theorem bigA_infinite : (bigA hB hP).Infinite := by
  intro hfin
  classical
  set N := hfin.toFinset.card
  have hcard := card_gt_of_not_colourable (k := N + 1) (by omega) (blk hB (N + 1)) (blk_spec hB (N + 1)).2
  set v := shiftOf hP (stage hB hP (N + 1)) (blk hB (N + 1))
  have hinj : Function.Injective (fun x : Plane => x + v) := fun a b h => add_right_cancel h
  have himg := Finset.card_image_of_injective (blk hB (N + 1)) hinj
  have hsub : (blk hB (N + 1)).image (fun x => x + v) ⊆ hfin.toFinset := by
    intro x hx
    rw [Set.Finite.mem_toFinset]
    exact block_sub hB hP (N + 1) (by simpa using hx)
  have := Finset.card_le_card hsub
  omega

end Assembly

/-- The site statement from blocks alone (placement is proved). -/
theorem main_of_blocks (hB : ∀ k, BlockProp k) :
    ∃ A : Set Plane, A.Infinite ∧ NoThreeOnLine A ∧ NoFourOnCircle A ∧
      ∀ k : ℕ, ¬ ∃ f : Plane → Fin k, ProperColouring A f :=
  ⟨bigA hB placementProp, bigA_infinite hB placementProp, (bigA_genPos hB placementProp).1,
    (bigA_genPos hB placementProp).2, bigA_not_colourable hB placementProp⟩

end Erdos130Gen

/-!
erdos-130, layer P2 + P4 (agent G, 2026-11-28).
P2: additive model. For rational points w_j = (c_j, s_j) of the unit circle put K_j = w_j^2 and
z_S = sum_{j in S} K_j. If T = S - a + b then z_S - z_T = K_a - K_b and
|K_a - K_b| = |2 (s_a c_b - c_a s_b)| is rational. Scaling by a common denominator N (a homothety,
which keeps general position) makes every Johnson edge an integer distance (`block_of_additive`).
P4: finitely many nonzero rational polynomials have a common rational non-root (`exists_avoid`).
-/

namespace Erdos130Gen

open OMA.S_erdos_130

/-! ## P2: the additive model -/

/-- K = w^2 for w = (c, s) -/
def Kpt (c s : ℝ) : Plane := WithLp.toLp 2 ![c ^ 2 - s ^ 2, 2 * c * s]

@[simp] theorem Kpt0 (c s : ℝ) : (Kpt c s) 0 = c ^ 2 - s ^ 2 := by simp [Kpt]
@[simp] theorem Kpt1 (c s : ℝ) : (Kpt c s) 1 = 2 * c * s := by simp [Kpt]

theorem dist_Kpt (ca sa cb sb : ℝ) (ha : ca ^ 2 + sa ^ 2 = 1) (hb : cb ^ 2 + sb ^ 2 = 1) :
    dist (Kpt ca sa) (Kpt cb sb) = |2 * (sa * cb - ca * sb)| := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs,
    Kpt0, Kpt0, Kpt1, Kpt1, ← Real.sqrt_sq_eq_abs]
  congr 1
  linear_combination (ca ^ 2 - 2 * cb ^ 2 + sa ^ 2 - 2 * sb ^ 2 + 1) * ha
    + (cb ^ 2 + sb ^ 2 - 1) * hb

/-- z_S -/
def zS {n : ℕ} (K : Fin n → Plane) (S : Finset (Fin n)) : Plane := ∑ j ∈ S, K j

/-- Johnson adjacency: T = S - a + b -/
def JAdj {n : ℕ} (S T : Finset (Fin n)) : Prop :=
  ∃ a b, a ∈ S ∧ b ∈ T ∧ a ∉ T ∧ b ∉ S ∧ S.erase a = T.erase b

theorem JAdj.ne {n : ℕ} {S T : Finset (Fin n)} (h : JAdj S T) : S ≠ T := by
  obtain ⟨a, b, ha, -, haT, -, -⟩ := h
  rintro rfl; exact haT ha

theorem zS_sub_of_JAdj {n : ℕ} (K : Fin n → Plane) {S T : Finset (Fin n)} {a b : Fin n}
    (ha : a ∈ S) (hb : b ∈ T) (he : S.erase a = T.erase b) : zS K S - zS K T = K a - K b := by
  unfold zS
  rw [← Finset.add_sum_erase S K ha, ← Finset.add_sum_erase T K hb, he]
  abel

/-! ## homotheties keep general position -/

theorem image_smul_finset_mem {A : Finset Plane} {N : ℝ} {x : Plane}
    (hx : x ∈ ((A.image (fun y => N • y) : Finset Plane) : Set Plane)) : ∃ y ∈ A, x = N • y := by
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, hy, rfl⟩

theorem collinear_of_smul {N : ℝ} (hN : N ≠ 0) {a b c : Plane}
    (h : Collinear ℝ ({N • a, N • b, N • c} : Set Plane)) : Collinear ℝ ({a, b, c} : Set Plane) := by
  rw [collinear_iff_of_mem (p₀ := N • a) (by simp)] at h
  obtain ⟨v, hv⟩ := h
  rw [collinear_iff_of_mem (p₀ := a) (by simp)]
  refine ⟨N⁻¹ • v, ?_⟩
  intro p hp
  have hp' : N • p ∈ ({N • a, N • b, N • c} : Set Plane) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
    rcases hp with rfl | rfl | rfl <;> simp
  obtain ⟨r, hr⟩ := hv _ hp'
  refine ⟨r, ?_⟩
  have e := congrArg (fun x : Plane => N⁻¹ • x) hr
  simp only [vadd_eq_add, smul_add, smul_smul, inv_mul_cancel₀ hN, one_smul] at e
  rw [vadd_eq_add, e, smul_smul, mul_comm N⁻¹ r]

theorem cospherical_of_smul {N : ℝ} (hN : N ≠ 0) {a b c d : Plane}
    (h : EuclideanGeometry.Cospherical ({N • a, N • b, N • c, N • d} : Set Plane)) :
    EuclideanGeometry.Cospherical ({a, b, c, d} : Set Plane) := by
  obtain ⟨o, r, hr⟩ := h
  refine ⟨N⁻¹ • o, r / |N|, ?_⟩
  intro p hp
  have hp' : N • p ∈ ({N • a, N • b, N • c, N • d} : Set Plane) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
    rcases hp with rfl | rfl | rfl | rfl <;> simp
  have e := hr _ hp'
  have hNo : o = N • (N⁻¹ • o) := by rw [smul_smul, mul_inv_cancel₀ hN, one_smul]
  rw [hNo, dist_smul₀, Real.norm_eq_abs] at e
  have hNa : 0 < |N| := abs_pos.mpr hN
  rw [eq_div_iff hNa.ne', ← e]
  ring

theorem genPos_smul (A : Finset Plane) {N : ℝ} (hN : N ≠ 0)
    (h : NoThreeOnLine (A : Set Plane) ∧ NoFourOnCircle (A : Set Plane)) :
    NoThreeOnLine ((A.image (fun y => N • y) : Finset Plane) : Set Plane) ∧
      NoFourOnCircle ((A.image (fun y => N • y) : Finset Plane) : Set Plane) := by
  have hne : ∀ {x y : Plane}, N • x ≠ N • y → x ≠ y := fun hxy e => hxy (by rw [e])
  constructor
  · intro a ha b hb c hc hab hac hbc hcol
    obtain ⟨a', ha', rfl⟩ := image_smul_finset_mem ha
    obtain ⟨b', hb', rfl⟩ := image_smul_finset_mem hb
    obtain ⟨c', hc', rfl⟩ := image_smul_finset_mem hc
    exact h.1 a' ha' b' hb' c' hc' (hne hab) (hne hac) (hne hbc) (collinear_of_smul hN hcol)
  · intro a ha b hb c hc d hd hab hac had hbc hbd hcd hcos
    obtain ⟨a', ha', rfl⟩ := image_smul_finset_mem ha
    obtain ⟨b', hb', rfl⟩ := image_smul_finset_mem hb
    obtain ⟨c', hc', rfl⟩ := image_smul_finset_mem hc
    obtain ⟨d', hd', rfl⟩ := image_smul_finset_mem hd
    exact h.2 a' ha' b' hb' c' hc' d' hd' (hne hab) (hne hac) (hne had) (hne hbc) (hne hbd)
      (hne hcd) (cospherical_of_smul hN hcos)

/-! ## the block -/

/-- a common denominator: N * q is an integer for every q in a finite set -/
theorem common_den {ι : Type*} (s : Finset ι) (q : ι → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ i ∈ s, ∃ m : ℤ, (N : ℚ) * q i = m := by
  refine ⟨∏ i ∈ s, (q i).den, Finset.prod_pos (fun i _ => (q i).den_pos), ?_⟩
  intro i hi
  obtain ⟨M, hM⟩ := Finset.dvd_prod_of_mem (fun i => (q i).den) hi
  refine ⟨(q i).num * M, ?_⟩
  rw [hM]
  push_cast
  rw [mul_comm ((q i).den : ℚ) (M : ℚ), mul_assoc, mul_comm ((q i).den : ℚ), Rat.mul_den_eq_num]
  ring

/-- P2: a Johnson family realized by the additive model gives a block. -/
theorem block_of_additive {k n : ℕ} (c s : Fin n → ℚ) (hcs : ∀ j, c j ^ 2 + s j ^ 2 = 1)
    (F : Finset (Finset (Fin n)))
    (hinj : Set.InjOn (zS (fun j => Kpt (c j) (s j))) (F : Set (Finset (Fin n))))
    (hgp : NoThreeOnLine ((F.image (zS (fun j => Kpt (c j) (s j))) : Finset Plane) : Set Plane) ∧
      NoFourOnCircle ((F.image (zS (fun j => Kpt (c j) (s j))) : Finset Plane) : Set Plane))
    (hchi : ¬ ∃ col : Finset (Fin n) → Fin k, ∀ S ∈ F, ∀ T ∈ F, JAdj S T → col S ≠ col T) :
    ∃ G : Finset Plane, (NoThreeOnLine (G : Set Plane) ∧ NoFourOnCircle (G : Set Plane)) ∧
      ¬ ∃ f : Plane → Fin k, ProperColouring (G : Set Plane) f := by
  classical
  set K : Fin n → Plane := fun j => Kpt (c j) (s j) with hK
  obtain ⟨N, hN, hNq⟩ := common_den (Finset.univ : Finset (Fin n × Fin n))
    (fun p => |2 * (s p.1 * c p.2 - c p.1 * s p.2)|)
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  set A := F.image (zS K) with hA
  refine ⟨A.image (fun y => (N : ℝ) • y), genPos_smul A hN' hgp, ?_⟩
  rintro ⟨f, hf⟩
  apply hchi
  refine ⟨fun S => f ((N : ℝ) • zS K S), ?_⟩
  intro S hS T hT hadj
  have hST : S ≠ T := hadj.ne
  obtain ⟨a, b, ha, hb, -, -, he⟩ := hadj
  have hmem : ∀ U ∈ F, (N : ℝ) • zS K U ∈ ((A.image (fun y => (N : ℝ) • y) : Finset Plane) : Set Plane) := by
    intro U hU
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, hA]
    exact ⟨zS K U, ⟨U, hU, rfl⟩, rfl⟩
  have hne : (N : ℝ) • zS K S ≠ (N : ℝ) • zS K T := by
    intro e
    exact hST (hinj hS hT (smul_right_injective Plane hN' e))
  obtain ⟨m, hm⟩ := hNq (a, b) (Finset.mem_univ _)
  refine hf _ (hmem S hS) _ (hmem T hT) hne ⟨m, ?_⟩
  rw [dist_smul₀, dist_eq_norm, zS_sub_of_JAdj K ha hb he, ← dist_eq_norm, hK]
  simp only
  rw [dist_Kpt _ _ _ _ (by exact_mod_cast hcs a) (by exact_mod_cast hcs b), Real.norm_eq_abs,
    abs_of_pos (by exact_mod_cast hN : (0 : ℝ) < N)]
  have hm' : ((N : ℚ) * |2 * (s a * c b - c a * s b)| : ℚ) = (m : ℚ) := hm
  have := congrArg (fun q : ℚ => (q : ℝ)) hm'
  push_cast at this
  exact this

/-! ## P4: avoiding finitely many nonzero polynomials over ℚ -/

theorem exists_avoid {σ : Type*} (ps : Finset (MvPolynomial σ ℚ)) (h : ∀ p ∈ ps, p ≠ 0) :
    ∃ x : σ → ℚ, ∀ p ∈ ps, MvPolynomial.eval x p ≠ 0 := by
  classical
  have hq : (∏ p ∈ ps, p) ≠ 0 := Finset.prod_ne_zero_iff.mpr h
  by_contra hc
  push Not at hc
  apply hq
  apply MvPolynomial.funext
  intro x
  obtain ⟨p, hp, hpx⟩ := hc x
  rw [map_prod, map_zero]
  exact Finset.prod_eq_zero hp hpx

end Erdos130Gen

/-!
erdos-130, layer P3 part 1 (agent G): the key one-variable lemma and the choice family.
* `unit_roots_finite`: a quadratic P(u) on the plane that is not of the form A (|u|^2 - 1) vanishes at only
  finitely many points of the unit circle (tau = u1 / (1 + u0) gives a nonzero quartic).
* `Kv v` (v natural): rational squares of rational unit points, injective in v.
* `bad_finite`: for such P, only finitely many v have P (Kv v) = 0.
-/

namespace Erdos130Gen

open OMA.S_erdos_130

theorem quartic_roots_finite (a0 a1 a2 a3 a4 : ℝ)
    (h : ¬ (a0 = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0 ∧ a4 = 0)) :
    {x : ℝ | a4 * x ^ 4 + a3 * x ^ 3 + a2 * x ^ 2 + a1 * x + a0 = 0}.Finite := by
  have hp : (Polynomial.C a4 * Polynomial.X ^ 4 + Polynomial.C a3 * Polynomial.X ^ 3
      + Polynomial.C a2 * Polynomial.X ^ 2 + Polynomial.C a1 * Polynomial.X + Polynomial.C a0) ≠ 0 := by
    intro h0
    apply h
    have e4 := congrArg (fun q => Polynomial.coeff q 4) h0
    have e3 := congrArg (fun q => Polynomial.coeff q 3) h0
    have e2 := congrArg (fun q => Polynomial.coeff q 2) h0
    have e1 := congrArg (fun q => Polynomial.coeff q 1) h0
    have e0 := congrArg (fun q => Polynomial.coeff q 0) h0
    simp [Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_X_pow] at e4 e3 e2 e1 e0
    exact ⟨e0, e1, e2, e3, e4⟩
  refine (Polynomial.finite_setOfPred_isRoot hp).subset ?_
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  simp [Polynomial.IsRoot, hx]

/-- rational parametrisation of the unit circle -/
noncomputable def upt (τ : ℝ) : Plane := WithLp.toLp 2 ![(1 - τ ^ 2) / (1 + τ ^ 2), 2 * τ / (1 + τ ^ 2)]

@[simp] theorem upt0 (τ : ℝ) : (upt τ) 0 = (1 - τ ^ 2) / (1 + τ ^ 2) := by simp [upt]
@[simp] theorem upt1 (τ : ℝ) : (upt τ) 1 = 2 * τ / (1 + τ ^ 2) := by simp [upt]

theorem ext2' (x y : Plane) (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  ext i
  fin_cases i <;> simp [h0, h1]

theorem upt_of_unit (u : Plane) (hu : u 0 ^ 2 + u 1 ^ 2 = 1) (h0 : u 0 ≠ -1) :
    upt (u 1 / (1 + u 0)) = u := by
  have hd : (1 + u 0) ≠ 0 := fun h => h0 (by linarith)
  have ht : (u 1 / (1 + u 0)) ^ 2 = (1 - u 0) / (1 + u 0) := by
    rw [div_pow, div_eq_div_iff (pow_ne_zero 2 hd) hd]
    linear_combination (1 + u 0) * hu
  apply ext2'
  · rw [upt0, ht]; field_simp; ring
  · rw [upt1, ht]; field_simp; ring

/-- Key lemma GL. -/
theorem unit_roots_finite (P : Plane → ℝ) (A B C D E F : ℝ)
    (hP : ∀ u : Plane, P u = A * u 0 ^ 2 + B * u 0 * u 1 + C * u 1 ^ 2 + D * u 0 + E * u 1 + F)
    (hnot : ¬ (B = 0 ∧ C = A ∧ D = 0 ∧ E = 0 ∧ F = -A)) :
    {u : Plane | u 0 ^ 2 + u 1 ^ 2 = 1 ∧ P u = 0}.Finite := by
  have hq := quartic_roots_finite (A + D + F) (2 * B + 2 * E) (4 * C - 2 * A + 2 * F) (2 * E - 2 * B)
    (A - D + F) (by
      rintro ⟨h0, h1, h2, h3, h4⟩
      exact hnot ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩)
  refine ((hq.image upt).union (Set.finite_singleton (WithLp.toLp 2 ![-1, 0] : Plane))).subset ?_
  rintro u ⟨hu, hPu⟩
  by_cases h0 : u 0 = -1
  · right
    have h1 : u 1 = 0 := by nlinarith [sq_nonneg (u 1)]
    simp only [Set.mem_singleton_iff]
    apply ext2' <;> simp [h0, h1]
  · left
    refine ⟨u 1 / (1 + u 0), ?_, upt_of_unit u hu h0⟩
    simp only [Set.mem_ofPred_eq]
    have key : ∀ τ : ℝ, P (upt τ) * (1 + τ ^ 2) ^ 2 = (A - D + F) * τ ^ 4 + (2 * E - 2 * B) * τ ^ 3
        + (4 * C - 2 * A + 2 * F) * τ ^ 2 + (2 * B + 2 * E) * τ + (A + D + F) := by
      intro τ
      have hpos : (1 + τ ^ 2) ≠ 0 := by positivity
      rw [hP, upt0, upt1]
      field_simp
      ring
    have := key (u 1 / (1 + u 0))
    rw [upt_of_unit u hu h0, hPu, zero_mul] at this
    exact this.symm

/-! ## the choice family -/

noncomputable def cv (v : ℕ) : ℝ := ((v : ℝ) ^ 2 - 1) / ((v : ℝ) ^ 2 + 1)
noncomputable def sv (v : ℕ) : ℝ := 2 * (v : ℝ) / ((v : ℝ) ^ 2 + 1)

theorem cv_sv (v : ℕ) : cv v ^ 2 + sv v ^ 2 = 1 := by
  unfold cv sv
  have : ((v : ℝ) ^ 2 + 1) ≠ 0 := by positivity
  field_simp
  ring

noncomputable def Kv (v : ℕ) : Plane := Kpt (cv v) (sv v)

theorem Kv_unit (v : ℕ) : (Kv v) 0 ^ 2 + (Kv v) 1 ^ 2 = 1 := by
  unfold Kv
  rw [Kpt0, Kpt1]
  have h := cv_sv v
  linear_combination (cv v ^ 2 + sv v ^ 2 + 1) * h

theorem sv_nonneg (v : ℕ) : 0 ≤ sv v := by unfold sv; positivity

theorem Kv_injective : Function.Injective Kv := by
  intro v1 v2 h
  have e0 := congrArg (fun x : Plane => x 0) h
  simp only [Kv, Kpt0] at e0
  have h1 := cv_sv v1
  have h2 := cv_sv v2
  have hs : sv v1 ^ 2 = sv v2 ^ 2 := by linarith
  have hs' : sv v1 = sv v2 := by
    have := sv_nonneg v1
    have := sv_nonneg v2
    nlinarith [sq_nonneg (sv v1 - sv v2), sq_nonneg (sv v1 + sv v2)]
  unfold sv at hs'
  have hd1 : ((v1 : ℝ) ^ 2 + 1) ≠ 0 := by positivity
  have hd2 : ((v2 : ℝ) ^ 2 + 1) ≠ 0 := by positivity
  rw [div_eq_div_iff hd1 hd2] at hs'
  have key : ((v1 : ℝ) - v2) * (1 - (v1 : ℝ) * v2) = 0 := by linear_combination hs' / 2
  rcases mul_eq_zero.1 key with h | h
  · exact_mod_cast (sub_eq_zero.1 h)
  · have : (v1 : ℝ) * v2 = 1 := by linarith
    have h' : v1 * v2 = 1 := by exact_mod_cast this
    rw [Nat.eq_one_of_mul_eq_one_right h', Nat.eq_one_of_mul_eq_one_left h']

/-- only finitely many v give a root of a non-degenerate quadratic -/
theorem bad_finite (P : Plane → ℝ) (A B C D E F : ℝ)
    (hP : ∀ u : Plane, P u = A * u 0 ^ 2 + B * u 0 * u 1 + C * u 1 ^ 2 + D * u 0 + E * u 1 + F)
    (hnot : ¬ (B = 0 ∧ C = A ∧ D = 0 ∧ E = 0 ∧ F = -A)) :
    {v : ℕ | P (Kv v) = 0}.Finite := by
  have hs := unit_roots_finite P A B C D E F hP hnot
  refine (hs.preimage (Kv_injective.injOn)).subset ?_
  intro v hv
  exact ⟨Kv_unit v, hv⟩

/-- the same, with the degenerate case stated as an identity -/
theorem bad_finite' (P : Plane → ℝ) (A B C D E F : ℝ)
    (hP : ∀ u : Plane, P u = A * u 0 ^ 2 + B * u 0 * u 1 + C * u 1 ^ 2 + D * u 0 + E * u 1 + F)
    (hnot : ¬ ∀ u : Plane, P u = A * (u 0 ^ 2 + u 1 ^ 2 - 1)) :
    {v : ℕ | P (Kv v) = 0}.Finite := by
  refine bad_finite P A B C D E F hP ?_
  rintro ⟨hB, hC, hD, hE, hF⟩
  apply hnot
  intro u
  rw [hP u, hB, hC, hD, hE, hF]
  ring

/-! ## the condition shapes (P3 part 2) -/

/-- a quadratic in u that is not a multiple of |u|^2 - 1 -/
def NiceQ (P : Plane → ℝ) : Prop :=
  ∃ A B C D E F : ℝ, (∀ u : Plane, P u = A * u 0 ^ 2 + B * u 0 * u 1 + C * u 1 ^ 2 + D * u 0 + E * u 1 + F)
    ∧ ¬ ∀ u : Plane, P u = A * (u 0 ^ 2 + u 1 ^ 2 - 1)

theorem finite_of_nice {P : Plane → ℝ} (h : NiceQ P) : {v : ℕ | P (Kv v) = 0}.Finite := by
  obtain ⟨A, B, C, D, E, F, hP, hn⟩ := h
  exact bad_finite' P A B C D E F hP hn

/-- the point (x, y) -/
def pt (x y : ℝ) : Plane := WithLp.toLp 2 ![x, y]
@[simp] theorem pt0 (x y : ℝ) : (pt x y) 0 = x := by simp [pt]
@[simp] theorem pt1 (x y : ℝ) : (pt x y) 1 = y := by simp [pt]

theorem ne_coord {x y : Plane} (h : x ≠ y) : x 0 - y 0 ≠ 0 ∨ x 1 - y 1 ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (ext2' x y (by linarith [hc.1]) (by linarith [hc.2]))

theorem dist_eq_one_of_sq {x y : Plane} (h : (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 = 1) : dist x y = 1 := by
  have h2 : dist x y ^ 2 = 1 := by
    rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two, Real.dist_eq,
      Real.dist_eq, sq_abs, sq_abs, h]
  nlinarith [dist_nonneg (x := x) (y := y)]

/-- D1 shape: |d + u|^2 never vanishes identically -/
theorem nice_D1 (d : Plane) : NiceQ (fun u => (d 0 + u 0) ^ 2 + (d 1 + u 1) ^ 2) := by
  refine ⟨1, 0, 1, 2 * d 0, 2 * d 1, d 0 ^ 2 + d 1 ^ 2, fun u => by ring, ?_⟩
  intro H
  have h := H (pt 0 0)
  simp only [pt0, pt1] at h
  nlinarith [sq_nonneg (d 0), sq_nonneg (d 1)]

/-- D2 shape: |d + u|^2 - 1, for d ≠ 0 -/
theorem nice_D2 (d : Plane) (hd : d ≠ 0) : NiceQ (fun u => (d 0 + u 0) ^ 2 + (d 1 + u 1) ^ 2 - 1) := by
  refine ⟨1, 0, 1, 2 * d 0, 2 * d 1, d 0 ^ 2 + d 1 ^ 2 - 1, fun u => by ring, ?_⟩
  intro H
  have h := H (pt 0 0)
  simp only [pt0, pt1] at h
  rcases ne_coord hd with h' | h' <;> apply h' <;> simp <;>
    nlinarith [sq_nonneg (d 0), sq_nonneg (d 1)]

/-- collinear, one moving point -/
theorem nice_L1 (a b q : Plane) (hab : a ≠ b) : NiceQ (fun u => crP a b (q + u)) := by
  refine ⟨0, 0, 0, -(b 1 - a 1), b 0 - a 0, crP a b q, fun u => ?_, ?_⟩
  · simp only [crP, cr, PiLp.add_apply]; ring
  · intro H
    have h0 := H (pt 0 0)
    have h1 := H (pt 1 0)
    have h2 := H (pt 0 1)
    simp only [crP, cr, PiLp.add_apply, pt0, pt1] at h0 h1 h2
    rcases ne_coord hab with h' | h' <;> apply h' <;> linarith

/-- collinear, two moving points -/
theorem nice_L2 (q1 q2 p : Plane) (hq : q1 ≠ q2) : NiceQ (fun u => crP (q1 + u) (q2 + u) p) := by
  refine ⟨0, 0, 0, q2 1 - q1 1, -(q2 0 - q1 0), crP q1 q2 p, fun u => ?_, ?_⟩
  · simp only [crP, cr, PiLp.add_apply]; ring
  · intro H
    have h0 := H (pt 0 0)
    have h1 := H (pt 1 0)
    have h2 := H (pt 0 1)
    simp only [crP, cr, PiLp.add_apply, pt0, pt1] at h0 h1 h2
    rcases ne_coord hq with h' | h' <;> apply h' <;> linarith

/-- W = 0 forces two of 0, B, C to coincide -/
theorem bc_contra (B0 B1 C0 C1 : ℝ) (hB : B0 ≠ 0 ∨ B1 ≠ 0) (hC : C0 ≠ 0 ∨ C1 ≠ 0)
    (hBC : B0 - C0 ≠ 0 ∨ B1 - C1 ≠ 0)
    (hW0 : (B0 ^ 2 + B1 ^ 2) * C0 - (C0 ^ 2 + C1 ^ 2) * B0 = 0)
    (hW1 : (B0 ^ 2 + B1 ^ 2) * C1 - (C0 ^ 2 + C1 ^ 2) * B1 = 0) : False := by
  have hZB : B0 ^ 2 + B1 ^ 2 ≠ 0 := by
    rcases hB with h | h <;> intro h0 <;> apply h <;> nlinarith [sq_nonneg B0, sq_nonneg B1]
  have hZC : C0 ^ 2 + C1 ^ 2 ≠ 0 := by
    rcases hC with h | h <;> intro h0 <;> apply h <;> nlinarith [sq_nonneg C0, sq_nonneg C1]
  have e1 : (B0 ^ 2 + B1 ^ 2) * ((B0 * C0 + B1 * C1) - (C0 ^ 2 + C1 ^ 2)) = 0 := by
    linear_combination B0 * hW0 + B1 * hW1
  have e2 : (C0 ^ 2 + C1 ^ 2) * ((B0 ^ 2 + B1 ^ 2) - (B0 * C0 + B1 * C1)) = 0 := by
    linear_combination C0 * hW0 + C1 * hW1
  have f1 := (mul_eq_zero.1 e1).resolve_left hZB
  have f2 := (mul_eq_zero.1 e2).resolve_left hZC
  have hz : (B0 - C0) ^ 2 + (B1 - C1) ^ 2 = 0 := by linear_combination f2 - f1
  rcases hBC with h | h <;> apply h <;> nlinarith [sq_nonneg (B0 - C0), sq_nonneg (B1 - C1)]

/-- concyclic, one moving point: degenerate only if a, b, c are all at distance 1 from q -/
theorem nice_C1 (a b c q : Plane) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hfar : ¬ (dist a q = 1 ∧ dist b q = 1 ∧ dist c q = 1)) :
    NiceQ (fun u => concP a b c (q + u)) := by
  set B0 := b 0 - a 0
  set B1 := b 1 - a 1
  set C0 := c 0 - a 0
  set C1 := c 1 - a 1
  set Q0 := q 0 - a 0
  set Q1 := q 1 - a 1
  set M := B0 * C1 - C0 * B1
  refine ⟨M, 0, M, -(B0 ^ 2 + B1 ^ 2) * C1 + (C0 ^ 2 + C1 ^ 2) * B1 + 2 * M * Q0,
    (B0 ^ 2 + B1 ^ 2) * C0 - (C0 ^ 2 + C1 ^ 2) * B0 + 2 * M * Q1, concP a b c q, fun u => ?_, ?_⟩
  · simp only [concP, concR, PiLp.add_apply, M, B0, B1, C0, C1, Q0, Q1]; ring
  · intro H
    by_cases hM : M = 0
    · have h0 := H (pt 0 0)
      have h1 := H (pt 1 0)
      have h2 := H (pt (-1) 0)
      have h3 := H (pt 0 1)
      have h4 := H (pt 0 (-1))
      simp only [concP, concR, PiLp.add_apply, pt0, pt1, hM] at h0 h1 h2 h3 h4
      have hMc : (b 0 - a 0) * (c 1 - a 1) - (c 0 - a 0) * (b 1 - a 1) = 0 := hM
      have hW1 : (B0 ^ 2 + B1 ^ 2) * C1 - (C0 ^ 2 + C1 ^ 2) * B1 = 0 := by
        simp only [B0, B1, C0, C1]
        linear_combination (h2 - h1) / 2 + 2 * (q 0 - a 0) * hMc
      have hW0 : (B0 ^ 2 + B1 ^ 2) * C0 - (C0 ^ 2 + C1 ^ 2) * B0 = 0 := by
        simp only [B0, B1, C0, C1]
        linear_combination (h3 - h4) / 2 - 2 * (q 1 - a 1) * hMc
      refine bc_contra B0 B1 C0 C1 ?_ ?_ ?_ hW0 hW1
      · rcases ne_coord hab with h | h
        · left; intro e; apply h; simp only [B0] at e; linarith
        · right; intro e; apply h; simp only [B1] at e; linarith
      · rcases ne_coord hac with h | h
        · left; intro e; apply h; simp only [C0] at e; linarith
        · right; intro e; apply h; simp only [C1] at e; linarith
      · rcases ne_coord hbc with h | h
        · left; intro e; apply h; simp only [B0, C0] at e; linarith
        · right; intro e; apply h; simp only [B1, C1] at e; linarith
    · apply hfar
      have key : ∀ p : Plane, concP a b c p = 0 → (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 = 1 := by
        intro p hp
        have h := H (p - q)
        simp only [PiLp.sub_apply, add_sub_cancel] at h
        rw [hp] at h
        have : M * ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 - 1) = 0 := by linarith
        have := (mul_eq_zero.1 this).resolve_left hM
        linarith
      refine ⟨dist_eq_one_of_sq (key a ?_), dist_eq_one_of_sq (key b ?_), dist_eq_one_of_sq (key c ?_)⟩ <;>
        simp only [concP, concR] <;> ring

theorem nice_neg {P : Plane → ℝ} (h : NiceQ P) : NiceQ (fun u => P (-u)) := by
  obtain ⟨A, B, C, D, E, F, hP, hn⟩ := h
  refine ⟨A, B, C, -D, -E, F, fun u => ?_, ?_⟩
  · simp only [hP, PiLp.neg_apply]; ring
  · intro H
    apply hn
    intro w
    have := H (-w)
    simp only [neg_neg, PiLp.neg_apply] at this
    rw [this]; ring

/-- concyclic, three moving points: degenerate only if q1, q2, q3 are all at distance 1 from p -/
theorem nice_C3 (q1 q2 q3 p : Plane) (h12 : q1 ≠ q2) (h13 : q1 ≠ q3) (h23 : q2 ≠ q3)
    (hfar : ¬ (dist q1 p = 1 ∧ dist q2 p = 1 ∧ dist q3 p = 1)) :
    NiceQ (fun u => concP (q1 + u) (q2 + u) (q3 + u) p) := by
  have h := nice_neg (nice_C1 q1 q2 q3 p h12 h13 h23 hfar)
  have e : (fun u => concP (q1 + u) (q2 + u) (q3 + u) p) =
      (fun u => (fun w => concP q1 q2 q3 (p + w)) (-u)) := by
    funext u
    simp only [concP, concR, PiLp.add_apply, PiLp.neg_apply]
    ring
  rw [e]; exact h

theorem nice_of_coeffs (P : Plane → ℝ) (A B C D E F : ℝ)
    (hP : ∀ u : Plane, P u = A * u 0 ^ 2 + B * u 0 * u 1 + C * u 1 ^ 2 + D * u 0 + E * u 1 + F)
    (hn : ¬ (B = 0 ∧ C = A ∧ D = 0 ∧ E = 0 ∧ F = -A)) : NiceQ P := by
  refine ⟨A, B, C, D, E, F, hP, fun H => hn ?_⟩
  have h0 := H (pt 0 0)
  have h1 := H (pt 1 0)
  have h2 := H (pt (-1) 0)
  have h3 := H (pt 0 1)
  have h4 := H (pt 0 (-1))
  have h5 := H (pt 1 1)
  rw [hP] at h0 h1 h2 h3 h4 h5
  simp only [pt0, pt1] at h0 h1 h2 h3 h4 h5
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- the 2+2 shape in real coordinates (base point at the first moving point) -/
theorem nice_C2r (e0 e1 w0 w1 z0 z1 : ℝ) (he : e0 ≠ 0 ∨ e1 ≠ 0) (hf : z0 - w0 ≠ 0 ∨ z1 - w1 ≠ 0) :
    NiceQ (fun u => concR e0 e1 (w0 - u 0) (w1 - u 1) (z0 - u 0) (z1 - u 1)) := by
  refine nice_of_coeffs _ (e0 * w1 - e0 * z1 + e1 * w0 - e1 * z0)
    (2 * (-e0 * w0 + e0 * z0 + e1 * w1 - e1 * z1)) (-e0 * w1 + e0 * z1 - e1 * w0 + e1 * z0)
    (e0 ^ 2 * w1 - e0 ^ 2 * z1 + 2 * e0 * w0 * z1 - 2 * e0 * w1 * z0 + e1 ^ 2 * w1 - e1 ^ 2 * z1
      - e1 * w0 ^ 2 - e1 * w1 ^ 2 + e1 * z0 ^ 2 + e1 * z1 ^ 2)
    (-e0 ^ 2 * w0 + e0 ^ 2 * z0 + e0 * w0 ^ 2 + e0 * w1 ^ 2 - e0 * z0 ^ 2 - e0 * z1 ^ 2
      - e1 ^ 2 * w0 + e1 ^ 2 * z0 + 2 * e1 * w0 * z1 - 2 * e1 * w1 * z0)
    (concR e0 e1 w0 w1 z0 z1) (fun u => by simp only [concR]; ring) ?_
  rintro ⟨hB, hC, -, -, -⟩
  have hA1 : e0 * (z1 - w1) + e1 * (z0 - w0) = 0 := by linear_combination hC / 2
  have hB1 : e0 * (z0 - w0) - e1 * (z1 - w1) = 0 := by linear_combination hB / 2
  have key : (e0 ^ 2 + e1 ^ 2) * ((z0 - w0) ^ 2 + (z1 - w1) ^ 2) = 0 := by
    linear_combination (e0 * (z1 - w1) + e1 * (z0 - w0)) * hA1 + (e0 * (z0 - w0) - e1 * (z1 - w1)) * hB1
  rcases mul_eq_zero.1 key with h | h
  · rcases he with h' | h' <;> apply h' <;> nlinarith [sq_nonneg e0, sq_nonneg e1]
  · rcases hf with h' | h' <;> apply h' <;> nlinarith [sq_nonneg (z0 - w0), sq_nonneg (z1 - w1)]

/-- concyclic, two moving and two fixed points: never degenerate -/
theorem nice_C2 (q1 q2 p1 p2 : Plane) (hq : q1 ≠ q2) (hp : p1 ≠ p2) :
    NiceQ (fun u => concP (q1 + u) (q2 + u) p1 p2) := by
  have he : q2 0 - q1 0 ≠ 0 ∨ q2 1 - q1 1 ≠ 0 := by
    rcases ne_coord hq with h | h
    · left; intro e; apply h; linarith
    · right; intro e; apply h; linarith
  have hf : (p2 0 - q1 0) - (p1 0 - q1 0) ≠ 0 ∨ (p2 1 - q1 1) - (p1 1 - q1 1) ≠ 0 := by
    rcases ne_coord hp with h | h
    · left; intro e; apply h; linarith
    · right; intro e; apply h; linarith
  have h := nice_C2r (q2 0 - q1 0) (q2 1 - q1 1) (p1 0 - q1 0) (p1 1 - q1 1) (p2 0 - q1 0)
    (p2 1 - q1 1) he hf
  have e : (fun u => concP (q1 + u) (q2 + u) p1 p2) = (fun u => concR (q2 0 - q1 0) (q2 1 - q1 1)
      (p1 0 - q1 0 - u 0) (p1 1 - q1 1 - u 1) (p2 0 - q1 0 - u 0) (p2 1 - q1 1 - u 1)) := by
    funext u
    simp only [concP, PiLp.add_apply]
    congr 1 <;> ring
  rw [e]; exact h

theorem nice_congr {P Q : Plane → ℝ} (h : NiceQ P) (e : ∀ u, Q u = P u) : NiceQ Q := by
  obtain ⟨A, B, C, D, E, F, hP, hn⟩ := h
  exact ⟨A, B, C, D, E, F, fun u => (e u).trans (hP u), fun H => hn (fun u => (e u).symm.trans (H u))⟩

theorem nice_negc {P Q : Plane → ℝ} (h : NiceQ P) (e : ∀ u, Q u = -P u) : NiceQ Q := by
  obtain ⟨A, B, C, D, E, F, hP, hn⟩ := h
  refine ⟨-A, -B, -C, -D, -E, -F, fun u => by rw [e, hP]; ring, fun H => hn (fun u => ?_)⟩
  have := H u
  rw [e] at this
  linear_combination -this

/-! ## P3 part 3: the greedy choice -/

section Greedy

variable {n : ℕ}

noncomputable def zm (m : Fin n → ℕ) (S : Finset (Fin n)) : Plane := zS (fun j => Kv (m j)) S

theorem zm_erase (m : Fin n → ℕ) {J : Fin n} {S : Finset (Fin n)} (h : J ∈ S) :
    zm m S = zm m (S.erase J) + Kv (m J) := by
  unfold zm zS
  rw [← Finset.add_sum_erase S _ h, add_comm]

theorem zm_sub_K (m : Fin n → ℕ) {J : Fin n} {S : Finset (Fin n)} (h : J ∈ S) :
    zm m S - Kv (m J) = zm m (S.erase J) := by
  rw [zm_erase m h, add_sub_cancel_right]

theorem zm_update (m : Fin n → ℕ) (J : Fin n) (v : ℕ) (S : Finset (Fin n)) :
    zm (Function.update m J v) S = zm m S + (if J ∈ S then Kv v - Kv (m J) else 0) := by
  by_cases h : J ∈ S
  · rw [if_pos h, zm_erase _ h, zm_erase m h]
    have e : zm (Function.update m J v) (S.erase J) = zm m (S.erase J) := by
      unfold zm zS
      apply Finset.sum_congr rfl
      intro l hl
      simp only [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
    rw [e, Function.update_self]
    abel
  · rw [if_neg h, add_zero]
    unfold zm zS
    apply Finset.sum_congr rfl
    intro l hl
    have hlJ : l ≠ J := fun e => h (by rw [← e]; exact hl)
    simp only [Function.update_of_ne hlJ]

/-- agreement of two sets on the indices ≥ j -/
def Agree (j : ℕ) (X Y : Finset (Fin n)) : Prop := ∀ l : Fin n, j ≤ l.val → (l ∈ X ↔ l ∈ Y)

theorem Agree.symm {j : ℕ} {X Y : Finset (Fin n)} (h : Agree j X Y) : Agree j Y X :=
  fun l hl => (h l hl).symm

theorem Agree.trans {j : ℕ} {X Y Z : Finset (Fin n)} (h1 : Agree j X Y) (h2 : Agree j Y Z) :
    Agree j X Z := fun l hl => (h1 l hl).trans (h2 l hl)

theorem agree_zero {X Y : Finset (Fin n)} (h : Agree 0 X Y) : X = Y := by
  ext l; exact h l (Nat.zero_le _)

theorem agree_top (X Y : Finset (Fin n)) : Agree n X Y := fun l hl => absurd l.isLt (by omega)

theorem ag_down {j : ℕ} {J : Fin n} (hJ : J.val = j) {X Y : Finset (Fin n)} (h : Agree (j + 1) X Y)
    (hm : J ∈ X ↔ J ∈ Y) : Agree j X Y := by
  intro l hl
  by_cases e : l.val = j
  · have : l = J := Fin.ext (by omega)
    rw [this]; exact hm
  · exact h l (by omega)

theorem ag_erase {j : ℕ} {J : Fin n} (hJ : J.val = j) {X Y : Finset (Fin n)} (h : Agree (j + 1) X Y)
    (hY : J ∉ Y) : Agree j (X.erase J) Y := by
  intro l hl
  rw [Finset.mem_erase]
  by_cases e : l.val = j
  · have : l = J := Fin.ext (by omega)
    subst this
    simp [hY]
  · have hl' : l ≠ J := fun h' => e (by rw [h']; exact hJ)
    rw [← h l (by omega)]
    simp [hl']

theorem ag_erase2 {j : ℕ} {J : Fin n} (hJ : J.val = j) {X Y : Finset (Fin n)} (h : Agree (j + 1) X Y) :
    Agree j (X.erase J) (Y.erase J) := by
  intro l hl
  rw [Finset.mem_erase, Finset.mem_erase]
  by_cases e : l.val = j
  · have : l = J := Fin.ext (by omega)
    subst this
    simp
  · rw [h l (by omega)]

theorem erase_ne {J : Fin n} {X Y : Finset (Fin n)} (hX : J ∈ X) (hY : J ∈ Y) (hne : X ≠ Y) :
    X.erase J ≠ Y.erase J := fun e => hne (by rw [← Finset.insert_erase hX, ← Finset.insert_erase hY, e])

theorem sd_erase_self {J : Fin n} {S : Finset (Fin n)} (h : J ∈ S) : (symmDiff S (S.erase J)).card = 1 := by
  have : symmDiff S (S.erase J) = {J} := by
    ext l
    simp only [Finset.mem_symmDiff, Finset.mem_erase, Finset.mem_singleton]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · by_contra hl; exact h2 ⟨hl, h1⟩
      · exact absurd h2 h3
    · rintro rfl; exact Or.inl ⟨h, fun h' => h'.1 rfl⟩
  rw [this, Finset.card_singleton]

theorem sd_insert {J : Fin n} {X Y : Finset (Fin n)} (hX : J ∈ X) (hY : J ∉ Y) :
    symmDiff X (insert J Y) = symmDiff (X.erase J) Y := by
  ext l
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_erase]
  by_cases e : l = J
  · subst e; simp [hX, hY]
  · simp [e]

theorem sd_insert_self {J : Fin n} {Y : Finset (Fin n)} (hY : J ∉ Y) : (symmDiff Y (insert J Y)).card = 1 := by
  have : symmDiff Y (insert J Y) = {J} := by
    ext l
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    by_cases e : l = J
    · subst e; simp [hY]
    · simp [e]
  rw [this, Finset.card_singleton]

/-- the invariant after choosing the first j points -/
structure Inv (F : Finset (Finset (Fin n))) (j : ℕ) (m : Fin n → ℕ) : Prop where
  d1 : ∀ X Y : Finset (Fin n), Agree j X Y → X ≠ Y → zm m X ≠ zm m Y
  d2 : ∀ X Y : Finset (Fin n), Agree j X Y → (symmDiff X Y).card ≠ 1 → dist (zm m X) (zm m Y) ≠ 1
  c3 : ∀ S1 ∈ F, ∀ S2 ∈ F, ∀ S3 ∈ F, S1 ≠ S2 → S1 ≠ S3 → S2 ≠ S3 → Agree j S1 S2 → Agree j S1 S3 →
    crP (zm m S1) (zm m S2) (zm m S3) ≠ 0
  c4 : ∀ S1 ∈ F, ∀ S2 ∈ F, ∀ S3 ∈ F, ∀ S4 ∈ F, S1 ≠ S2 → S1 ≠ S3 → S1 ≠ S4 → S2 ≠ S3 → S2 ≠ S4 →
    S3 ≠ S4 → Agree j S1 S2 → Agree j S1 S3 → Agree j S1 S4 →
    concP (zm m S1) (zm m S2) (zm m S3) (zm m S4) ≠ 0

theorem inv_zero (F : Finset (Finset (Fin n))) (m : Fin n → ℕ) : Inv F 0 m := by
  refine ⟨fun X Y h hne => absurd (agree_zero h) hne, fun X Y h _ => ?_, ?_, ?_⟩
  · rw [agree_zero h, dist_self]; norm_num
  · intro S1 _ S2 _ S3 _ h12 _ _ a12 _; exact absurd (agree_zero a12) h12
  · intro S1 _ S2 _ S3 _ S4 _ h12 _ _ _ _ _ a12 _ _; exact absurd (agree_zero a12) h12

/-- no four members at symmetric distance 1 from a common set (no 4-star, no 4-top) -/
def NoFourStar (F : Finset (Finset (Fin n))) : Prop :=
  ∀ R : Finset (Fin n), ∀ S1 ∈ F, ∀ S2 ∈ F, ∀ S3 ∈ F, ∀ S4 ∈ F, S1 ≠ S2 → S1 ≠ S3 → S1 ≠ S4 →
    S2 ≠ S3 → S2 ≠ S4 → S3 ≠ S4 → (symmDiff S1 R).card = 1 → (symmDiff S2 R).card = 1 →
    (symmDiff S3 R).card = 1 → (symmDiff S4 R).card = 1 → False

section Step

variable {F : Finset (Finset (Fin n))} {j : ℕ} {m : Fin n → ℕ} {J : Fin n}

/-- the new position of z_X when u replaces K_J -/
noncomputable def np (m : Fin n → ℕ) (J : Fin n) (X : Finset (Fin n)) (u : Plane) : Plane :=
  zm m X + (if J ∈ X then u - Kv (m J) else 0)

theorem fixd (I : Inv F j m) (hJ : J.val = j) {X Y : Finset (Fin n)} (hX : J ∉ X) (hY : J ∉ Y)
    (a : Agree (j + 1) X Y) (hne : X ≠ Y) : zm m X ≠ zm m Y :=
  I.d1 X Y (ag_down hJ a (iff_of_false hX hY)) hne

theorem movd (I : Inv F j m) (hJ : J.val = j) {X Y : Finset (Fin n)} (hX : J ∈ X) (hY : J ∈ Y)
    (a : Agree (j + 1) X Y) (hne : X ≠ Y) : zm m X - Kv (m J) ≠ zm m Y - Kv (m J) := by
  rw [zm_sub_K m hX, zm_sub_K m hY]
  exact I.d1 _ _ (ag_erase2 hJ a) (erase_ne hX hY hne)

theorem split_D1 (X Y : Finset (Fin n)) (hs : ¬ (J ∈ X ↔ J ∈ Y)) :
    NiceQ (fun u => ((np m J X u) 0 - (np m J Y u) 0) ^ 2 + ((np m J X u) 1 - (np m J Y u) 1) ^ 2) := by
  by_cases hX : J ∈ X
  · have hY : J ∉ Y := fun hY => hs (iff_of_true hX hY)
    exact nice_congr (nice_D1 (zm m X - Kv (m J) - zm m Y)) (fun u => by
      simp only [np, if_pos hX, if_neg hY, add_zero, PiLp.add_apply, PiLp.sub_apply]; ring)
  · have hY : J ∈ Y := by
      by_contra hY; exact hs (iff_of_false hX hY)
    exact nice_congr (nice_D1 (zm m Y - Kv (m J) - zm m X)) (fun u => by
      simp only [np, if_neg hX, if_pos hY, add_zero, PiLp.add_apply, PiLp.sub_apply]; ring)

theorem split_D2 (I : Inv F j m) (hJ : J.val = j) (X Y : Finset (Fin n)) (a : Agree (j + 1) X Y)
    (hs : ¬ (J ∈ X ↔ J ∈ Y)) (hc : (symmDiff X Y).card ≠ 1) :
    NiceQ (fun u => ((np m J X u) 0 - (np m J Y u) 0) ^ 2 + ((np m J X u) 1 - (np m J Y u) 1) ^ 2 - 1) := by
  by_cases hX : J ∈ X
  · have hY : J ∉ Y := fun hY => hs (iff_of_true hX hY)
    have hne : X.erase J ≠ Y := by
      intro e; apply hc; rw [← e]; exact sd_erase_self hX
    have hd : zm m X - Kv (m J) - zm m Y ≠ 0 := by
      rw [zm_sub_K m hX, sub_ne_zero]
      exact I.d1 _ _ (ag_erase hJ a hY) hne
    exact nice_congr (nice_D2 _ hd) (fun u => by
      simp only [np, if_pos hX, if_neg hY, add_zero, PiLp.add_apply, PiLp.sub_apply]; ring)
  · have hY : J ∈ Y := by
      by_contra hY; exact hs (iff_of_false hX hY)
    have hne : Y.erase J ≠ X := by
      intro e; apply hc; rw [symmDiff_comm, ← e]; exact sd_erase_self hY
    have hd : zm m Y - Kv (m J) - zm m X ≠ 0 := by
      rw [zm_sub_K m hY, sub_ne_zero]
      exact I.d1 _ _ (ag_erase hJ a.symm hX) hne
    exact nice_congr (nice_D2 _ hd) (fun u => by
      simp only [np, if_neg hX, if_pos hY, add_zero, PiLp.add_apply, PiLp.sub_apply]; ring)

theorem split_C3 (I : Inv F j m) (hJ : J.val = j) (S1 S2 S3 : Finset (Fin n))
    (h12 : S1 ≠ S2) (h13 : S1 ≠ S3) (h23 : S2 ≠ S3) (a12 : Agree (j + 1) S1 S2)
    (a13 : Agree (j + 1) S1 S3) (hs : ¬ ((J ∈ S1 ↔ J ∈ S2) ∧ (J ∈ S1 ↔ J ∈ S3))) :
    NiceQ (fun u => crP (np m J S1 u) (np m J S2 u) (np m J S3 u)) := by
  have a23 : Agree (j + 1) S2 S3 := a12.symm.trans a13
  by_cases h1 : J ∈ S1 <;> by_cases h2 : J ∈ S2 <;> by_cases h3 : J ∈ S3
  · exact absurd ⟨iff_of_true h1 h2, iff_of_true h1 h3⟩ hs
  · first
      | exact nice_congr (nice_L2 _ _ (zm m S3) (movd I hJ h1 h2 a12 h12)) (fun u => by
          simp only [np, if_pos h1, if_pos h2, if_neg h3, add_zero, crP, cr, PiLp.add_apply,
            PiLp.sub_apply]; ring)
      | exact nice_negc (nice_L2 _ _ (zm m S3) (movd I hJ h1 h2 a12 h12)) (fun u => by
          simp only [np, if_pos h1, if_pos h2, if_neg h3, add_zero, crP, cr, PiLp.add_apply,
            PiLp.sub_apply]; ring)
  · first
      | exact nice_negc (nice_L2 _ _ (zm m S2) (movd I hJ h1 h3 a13 h13)) (fun u => by
          simp only [np, if_pos h1, if_neg h2, if_pos h3, add_zero, crP, cr, PiLp.add_apply,
            PiLp.sub_apply]; ring)
  · first
      | exact nice_congr (nice_L1 _ _ (zm m S1 - Kv (m J)) (fixd I hJ h2 h3 a23 h23)) (fun u => by
          simp only [np, if_pos h1, if_neg h2, if_neg h3, add_zero, crP, cr, PiLp.add_apply,
            PiLp.sub_apply]; ring)
      | exact nice_negc (nice_L1 _ _ (zm m S1 - Kv (m J)) (fixd I hJ h2 h3 a23 h23)) (fun u => by
          simp only [np, if_pos h1, if_neg h2, if_neg h3, add_zero, crP, cr, PiLp.add_apply,
            PiLp.sub_apply]; ring)
  · first
      | exact nice_congr (nice_L2 _ _ (zm m S1) (movd I hJ h2 h3 a23 h23)) (fun u => by
          simp only [np, if_neg h1, if_pos h2, if_pos h3, add_zero, crP, cr, PiLp.add_apply,
            PiLp.sub_apply]; ring)
      | exact nice_negc (nice_L2 _ _ (zm m S1) (movd I hJ h2 h3 a23 h23)) (fun u => by
          simp only [np, if_neg h1, if_pos h2, if_pos h3, add_zero, crP, cr, PiLp.add_apply,
            PiLp.sub_apply]; ring)
  · first
      | exact nice_negc (nice_L1 _ _ (zm m S2 - Kv (m J)) (fixd I hJ h1 h3 a13 h13)) (fun u => by
          simp only [np, if_neg h1, if_pos h2, if_neg h3, add_zero, crP, cr, PiLp.add_apply,
            PiLp.sub_apply]; ring)
  · first
      | exact nice_congr (nice_L1 _ _ (zm m S3 - Kv (m J)) (fixd I hJ h1 h2 a12 h12)) (fun u => by
          simp only [np, if_neg h1, if_neg h2, if_pos h3, add_zero, crP, cr, PiLp.add_apply,
            PiLp.sub_apply]; ring)
      | exact nice_negc (nice_L1 _ _ (zm m S3 - Kv (m J)) (fixd I hJ h1 h2 a12 h12)) (fun u => by
          simp only [np, if_neg h1, if_neg h2, if_pos h3, add_zero, crP, cr, PiLp.add_apply,
            PiLp.sub_apply]; ring)
  · exact absurd ⟨iff_of_false h1 h2, iff_of_false h1 h3⟩ hs

theorem far1 (I : Inv F j m) (hJ : J.val = j) (hseed : NoFourStar F) {Sa Sb Sc Sm : Finset (Fin n)}
    (ha' : Sa ∈ F) (hb' : Sb ∈ F) (hc' : Sc ∈ F) (hm' : Sm ∈ F)
    (hab : Sa ≠ Sb) (hac : Sa ≠ Sc) (ham : Sa ≠ Sm) (hbc : Sb ≠ Sc) (hbm : Sb ≠ Sm) (hcm : Sc ≠ Sm)
    (ama : Agree (j + 1) Sm Sa) (amb : Agree (j + 1) Sm Sb) (amc : Agree (j + 1) Sm Sc)
    (ha : J ∉ Sa) (hb : J ∉ Sb) (hc : J ∉ Sc) (hm : J ∈ Sm) :
    ¬ (dist (zm m Sa) (zm m Sm - Kv (m J)) = 1 ∧ dist (zm m Sb) (zm m Sm - Kv (m J)) = 1 ∧
      dist (zm m Sc) (zm m Sm - Kv (m J)) = 1) := by
  rintro ⟨e1, e2, e3⟩
  rw [zm_sub_K m hm] at e1 e2 e3
  have c : ∀ {X : Finset (Fin n)}, Agree (j + 1) Sm X → J ∉ X →
      dist (zm m X) (zm m (Sm.erase J)) = 1 → (symmDiff X (Sm.erase J)).card = 1 := by
    intro X a hX e
    by_contra hcd
    exact I.d2 _ _ (ag_erase hJ a hX).symm hcd e
  exact hseed (Sm.erase J) Sa ha' Sb hb' Sc hc' Sm hm' hab hac ham hbc hbm hcm (c ama ha e1)
    (c amb hb e2) (c amc hc e3) (sd_erase_self hm)

theorem far3 (I : Inv F j m) (hJ : J.val = j) (hseed : NoFourStar F) {Sa Sb Sc Sf : Finset (Fin n)}
    (ha' : Sa ∈ F) (hb' : Sb ∈ F) (hc' : Sc ∈ F) (hf' : Sf ∈ F)
    (hab : Sa ≠ Sb) (hac : Sa ≠ Sc) (haf : Sa ≠ Sf) (hbc : Sb ≠ Sc) (hbf : Sb ≠ Sf) (hcf : Sc ≠ Sf)
    (aaf : Agree (j + 1) Sa Sf) (abf : Agree (j + 1) Sb Sf) (acf : Agree (j + 1) Sc Sf)
    (ha : J ∈ Sa) (hb : J ∈ Sb) (hc : J ∈ Sc) (hf : J ∉ Sf) :
    ¬ (dist (zm m Sa - Kv (m J)) (zm m Sf) = 1 ∧ dist (zm m Sb - Kv (m J)) (zm m Sf) = 1 ∧
      dist (zm m Sc - Kv (m J)) (zm m Sf) = 1) := by
  rintro ⟨e1, e2, e3⟩
  rw [zm_sub_K m ha] at e1
  rw [zm_sub_K m hb] at e2
  rw [zm_sub_K m hc] at e3
  have c : ∀ {X : Finset (Fin n)}, Agree (j + 1) X Sf → J ∈ X →
      dist (zm m (X.erase J)) (zm m Sf) = 1 → (symmDiff X (insert J Sf)).card = 1 := by
    intro X a hX e
    rw [sd_insert hX hf]
    by_contra hcd
    exact I.d2 _ _ (ag_erase hJ a hf) hcd e
  exact hseed (insert J Sf) Sa ha' Sb hb' Sc hc' Sf hf' hab hac haf hbc hbf hcf (c aaf ha e1)
    (c abf hb e2) (c acf hc e3) (sd_insert_self hf)

theorem split_C4 (I : Inv F j m) (hJ : J.val = j) (hseed : NoFourStar F) {S1 S2 S3 S4 : Finset (Fin n)}
    (m1 : S1 ∈ F) (m2 : S2 ∈ F) (m3 : S3 ∈ F) (m4 : S4 ∈ F)
    (h12 : S1 ≠ S2) (h13 : S1 ≠ S3) (h14 : S1 ≠ S4) (h23 : S2 ≠ S3) (h24 : S2 ≠ S4) (h34 : S3 ≠ S4)
    (a12 : Agree (j + 1) S1 S2) (a13 : Agree (j + 1) S1 S3) (a14 : Agree (j + 1) S1 S4)
    (hs : ¬ ((J ∈ S1 ↔ J ∈ S2) ∧ (J ∈ S1 ↔ J ∈ S3) ∧ (J ∈ S1 ↔ J ∈ S4))) :
    NiceQ (fun u => concP (np m J S1 u) (np m J S2 u) (np m J S3 u) (np m J S4 u)) := by
  have a23 : Agree (j + 1) S2 S3 := a12.symm.trans a13
  have a24 : Agree (j + 1) S2 S4 := a12.symm.trans a14
  have a34 : Agree (j + 1) S3 S4 := a13.symm.trans a14
  by_cases h1 : J ∈ S1 <;> by_cases h2 : J ∈ S2 <;> by_cases h3 : J ∈ S3 <;> by_cases h4 : J ∈ S4
  · exact absurd ⟨iff_of_true h1 h2, iff_of_true h1 h3, iff_of_true h1 h4⟩ hs
  · -- TTTF
    refine nice_congr (nice_C3 _ _ _ (zm m S4) (movd I hJ h1 h2 a12 h12) (movd I hJ h1 h3 a13 h13)
      (movd I hJ h2 h3 a23 h23) (far3 I hJ hseed m1 m2 m3 m4 h12 h13 h14 h23 h24 h34 a14 a24 a34
        h1 h2 h3 h4)) ?_
    intro u
    simp only [np, if_pos h1, if_pos h2, if_pos h3, if_neg h4, add_zero, concP, concR,
      PiLp.add_apply, PiLp.sub_apply]
    ring
  · -- TTFT
    refine nice_negc (nice_C3 _ _ _ (zm m S3) (movd I hJ h1 h2 a12 h12) (movd I hJ h1 h4 a14 h14)
      (movd I hJ h2 h4 a24 h24) (far3 I hJ hseed m1 m2 m4 m3 h12 h14 h13 h24 h23 (Ne.symm h34)
        a13 a23 a34.symm h1 h2 h4 h3)) ?_
    intro u
    simp only [np, if_pos h1, if_pos h2, if_neg h3, if_pos h4, add_zero, concP, concR,
      PiLp.add_apply, PiLp.sub_apply]
    ring
  · -- TTFF
    refine nice_congr (nice_C2 _ _ (zm m S3) (zm m S4) (movd I hJ h1 h2 a12 h12)
      (fixd I hJ h3 h4 a34 h34)) ?_
    intro u
    simp only [np, if_pos h1, if_pos h2, if_neg h3, if_neg h4, add_zero, concP, concR,
      PiLp.add_apply, PiLp.sub_apply]
    ring
  · -- TFTT
    refine nice_congr (nice_C3 _ _ _ (zm m S2) (movd I hJ h1 h3 a13 h13) (movd I hJ h1 h4 a14 h14)
      (movd I hJ h3 h4 a34 h34) (far3 I hJ hseed m1 m3 m4 m2 h13 h14 h12 h34 (Ne.symm h23)
        (Ne.symm h24) a12 a23.symm a24.symm h1 h3 h4 h2)) ?_
    intro u
    simp only [np, if_pos h1, if_neg h2, if_pos h3, if_pos h4, add_zero, concP, concR,
      PiLp.add_apply, PiLp.sub_apply]
    ring
  · -- TFTF
    refine nice_negc (nice_C2 _ _ (zm m S2) (zm m S4) (movd I hJ h1 h3 a13 h13)
      (fixd I hJ h2 h4 a24 h24)) ?_
    intro u
    simp only [np, if_pos h1, if_neg h2, if_pos h3, if_neg h4, add_zero, concP, concR,
      PiLp.add_apply, PiLp.sub_apply]
    ring
  · -- TFFT
    refine nice_congr (nice_C2 _ _ (zm m S2) (zm m S3) (movd I hJ h1 h4 a14 h14)
      (fixd I hJ h2 h3 a23 h23)) ?_
    intro u
    simp only [np, if_pos h1, if_neg h2, if_neg h3, if_pos h4, add_zero, concP, concR,
      PiLp.add_apply, PiLp.sub_apply]
    ring
  · -- TFFF
    refine nice_negc (nice_C1 (zm m S2) (zm m S3) (zm m S4) _ (fixd I hJ h2 h3 a23 h23)
      (fixd I hJ h2 h4 a24 h24) (fixd I hJ h3 h4 a34 h34)
      (far1 I hJ hseed m2 m3 m4 m1 h23 h24 (Ne.symm h12) h34 (Ne.symm h13) (Ne.symm h14)
        a12 a13 a14 h2 h3 h4 h1)) ?_
    intro u
    simp only [np, if_pos h1, if_neg h2, if_neg h3, if_neg h4, add_zero, concP, concR,
      PiLp.add_apply, PiLp.sub_apply]
    ring
  · -- FTTT
    refine nice_negc (nice_C3 _ _ _ (zm m S1) (movd I hJ h2 h3 a23 h23) (movd I hJ h2 h4 a24 h24)
      (movd I hJ h3 h4 a34 h34) (far3 I hJ hseed m2 m3 m4 m1 h23 h24 (Ne.symm h12) h34
        (Ne.symm h13) (Ne.symm h14) a12.symm a13.symm a14.symm h2 h3 h4 h1)) ?_
    intro u
    simp only [np, if_neg h1, if_pos h2, if_pos h3, if_pos h4, add_zero, concP, concR,
      PiLp.add_apply, PiLp.sub_apply]
    ring
  · -- FTTF
    refine nice_congr (nice_C2 _ _ (zm m S1) (zm m S4) (movd I hJ h2 h3 a23 h23)
      (fixd I hJ h1 h4 a14 h14)) ?_
    intro u
    simp only [np, if_neg h1, if_pos h2, if_pos h3, if_neg h4, add_zero, concP, concR,
      PiLp.add_apply, PiLp.sub_apply]
    ring
  · -- FTFT
    refine nice_negc (nice_C2 _ _ (zm m S1) (zm m S3) (movd I hJ h2 h4 a24 h24)
      (fixd I hJ h1 h3 a13 h13)) ?_
    intro u
    simp only [np, if_neg h1, if_pos h2, if_neg h3, if_pos h4, add_zero, concP, concR,
      PiLp.add_apply, PiLp.sub_apply]
    ring
  · -- FTFF
    refine nice_congr (nice_C1 (zm m S1) (zm m S3) (zm m S4) _ (fixd I hJ h1 h3 a13 h13)
      (fixd I hJ h1 h4 a14 h14) (fixd I hJ h3 h4 a34 h34)
      (far1 I hJ hseed m1 m3 m4 m2 h13 h14 h12 h34 (Ne.symm h23) (Ne.symm h24)
        a12.symm a23 a24 h1 h3 h4 h2)) ?_
    intro u
    simp only [np, if_neg h1, if_pos h2, if_neg h3, if_neg h4, add_zero, concP, concR,
      PiLp.add_apply, PiLp.sub_apply]
    ring
  · -- FFTT
    refine nice_congr (nice_C2 _ _ (zm m S1) (zm m S2) (movd I hJ h3 h4 a34 h34)
      (fixd I hJ h1 h2 a12 h12)) ?_
    intro u
    simp only [np, if_neg h1, if_neg h2, if_pos h3, if_pos h4, add_zero, concP, concR,
      PiLp.add_apply, PiLp.sub_apply]
    ring
  · -- FFTF
    refine nice_negc (nice_C1 (zm m S1) (zm m S2) (zm m S4) _ (fixd I hJ h1 h2 a12 h12)
      (fixd I hJ h1 h4 a14 h14) (fixd I hJ h2 h4 a24 h24)
      (far1 I hJ hseed m1 m2 m4 m3 h12 h14 h13 h24 h23 (Ne.symm h34)
        a13.symm a23.symm a34 h1 h2 h4 h3)) ?_
    intro u
    simp only [np, if_neg h1, if_neg h2, if_pos h3, if_neg h4, add_zero, concP, concR,
      PiLp.add_apply, PiLp.sub_apply]
    ring
  · -- FFFT
    refine nice_congr (nice_C1 (zm m S1) (zm m S2) (zm m S3) _ (fixd I hJ h1 h2 a12 h12)
      (fixd I hJ h1 h3 a13 h13) (fixd I hJ h2 h3 a23 h23)
      (far1 I hJ hseed m1 m2 m3 m4 h12 h13 h14 h23 h24 h34
        a14.symm a24.symm a34.symm h1 h2 h3 h4)) ?_
    intro u
    simp only [np, if_neg h1, if_neg h2, if_neg h3, if_pos h4, add_zero, concP, concR,
      PiLp.add_apply, PiLp.sub_apply]
    ring
  · exact absurd ⟨iff_of_false h1 h2, iff_of_false h1 h3, iff_of_false h1 h4⟩ hs

theorem finN_ex {α : Type*} (S : Finset α) (T : α → ℕ → Prop) (h : ∀ a ∈ S, {v | T a v}.Finite) :
    {v : ℕ | ∃ a ∈ S, T a v}.Finite := by
  have : {v : ℕ | ∃ a ∈ S, T a v} = ⋃ a ∈ (S : Set α), {v | T a v} := by ext; simp
  rw [this]
  exact Set.Finite.biUnion S.finite_toSet h

theorem finN_and (q : Prop) (f : ℕ → Prop) (h : q → {v | f v}.Finite) : {v : ℕ | q ∧ f v}.Finite := by
  by_cases hq : q
  · exact (h hq).subset (fun v hv => hv.2)
  · exact (Set.finite_empty).subset (fun v hv => (hq hv.1).elim)

theorem np_same (u : Plane) {X Y : Finset (Fin n)} (h : J ∈ X ↔ J ∈ Y) :
    np m J Y u = zm m Y + (if J ∈ X then u - Kv (m J) else 0) := by
  unfold np
  by_cases hX : J ∈ X
  · rw [if_pos hX, if_pos (h.mp hX)]
  · rw [if_neg hX, if_neg (fun hY => hX (h.mpr hY))]

theorem dsq' (x y : Plane) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two, Real.dist_eq,
    Real.dist_eq, sq_abs, sq_abs]

/-- one greedy step -/
theorem inv_step (I : Inv F j m) (hJ : J.val = j) (hseed : NoFourStar F) :
    ∃ v : ℕ, Inv F (j + 1) (Function.update m J v) := by
  classical
  have B1 : {v : ℕ | ∃ X ∈ (Finset.univ : Finset (Finset (Fin n))), ∃ Y ∈ (Finset.univ : Finset (Finset (Fin n))),
      ¬ (J ∈ X ↔ J ∈ Y) ∧ ((np m J X (Kv v)) 0 - (np m J Y (Kv v)) 0) ^ 2
        + ((np m J X (Kv v)) 1 - (np m J Y (Kv v)) 1) ^ 2 = 0}.Finite :=
    finN_ex _ _ fun X _ => finN_ex _ _ fun Y _ => finN_and _ _ fun hs => finite_of_nice (split_D1 X Y hs)
  have B2 : {v : ℕ | ∃ X ∈ (Finset.univ : Finset (Finset (Fin n))), ∃ Y ∈ (Finset.univ : Finset (Finset (Fin n))),
      Agree (j + 1) X Y ∧ ¬ (J ∈ X ↔ J ∈ Y) ∧ (symmDiff X Y).card ≠ 1 ∧
      ((np m J X (Kv v)) 0 - (np m J Y (Kv v)) 0) ^ 2
        + ((np m J X (Kv v)) 1 - (np m J Y (Kv v)) 1) ^ 2 - 1 = 0}.Finite :=
    finN_ex _ _ fun X _ => finN_ex _ _ fun Y _ => finN_and _ _ fun a => finN_and _ _ fun hs =>
      finN_and _ _ fun hc => finite_of_nice (split_D2 I hJ X Y a hs hc)
  have B3 : {v : ℕ | ∃ S1 ∈ F, ∃ S2 ∈ F, ∃ S3 ∈ F, S1 ≠ S2 ∧ S1 ≠ S3 ∧ S2 ≠ S3 ∧
      Agree (j + 1) S1 S2 ∧ Agree (j + 1) S1 S3 ∧ ¬ ((J ∈ S1 ↔ J ∈ S2) ∧ (J ∈ S1 ↔ J ∈ S3)) ∧
      crP (np m J S1 (Kv v)) (np m J S2 (Kv v)) (np m J S3 (Kv v)) = 0}.Finite :=
    finN_ex _ _ fun S1 _ => finN_ex _ _ fun S2 _ => finN_ex _ _ fun S3 _ =>
      finN_and _ _ fun h12 => finN_and _ _ fun h13 => finN_and _ _ fun h23 =>
        finN_and _ _ fun a12 => finN_and _ _ fun a13 => finN_and _ _ fun hs =>
          finite_of_nice (split_C3 I hJ S1 S2 S3 h12 h13 h23 a12 a13 hs)
  have B4 : {v : ℕ | ∃ S1 ∈ F, ∃ S2 ∈ F, ∃ S3 ∈ F, ∃ S4 ∈ F, S1 ≠ S2 ∧ S1 ≠ S3 ∧ S1 ≠ S4 ∧
      S2 ≠ S3 ∧ S2 ≠ S4 ∧ S3 ≠ S4 ∧
      Agree (j + 1) S1 S2 ∧ Agree (j + 1) S1 S3 ∧ Agree (j + 1) S1 S4 ∧
      ¬ ((J ∈ S1 ↔ J ∈ S2) ∧ (J ∈ S1 ↔ J ∈ S3) ∧ (J ∈ S1 ↔ J ∈ S4)) ∧
      concP (np m J S1 (Kv v)) (np m J S2 (Kv v)) (np m J S3 (Kv v)) (np m J S4 (Kv v)) = 0}.Finite :=
    finN_ex _ _ fun S1 m1 => finN_ex _ _ fun S2 m2 => finN_ex _ _ fun S3 m3 => finN_ex _ _ fun S4 m4 =>
      finN_and _ _ fun h12 => finN_and _ _ fun h13 => finN_and _ _ fun h14 =>
        finN_and _ _ fun h23 => finN_and _ _ fun h24 => finN_and _ _ fun h34 =>
          finN_and _ _ fun a12 => finN_and _ _ fun a13 => finN_and _ _ fun a14 => finN_and _ _ fun hs =>
            finite_of_nice (split_C4 I hJ hseed m1 m2 m3 m4 h12 h13 h14 h23 h24 h34 a12 a13 a14 hs)
  obtain ⟨v, hv⟩ := (((B1.union B2).union B3).union B4).infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hv
  obtain ⟨⟨⟨hv1, hv2⟩, hv3⟩, hv4⟩ := hv
  have hz : ∀ X, zm (Function.update m J v) X = np m J X (Kv v) := fun X => zm_update m J v X
  refine ⟨v, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro X Y a hne
    rw [hz, hz]
    by_cases hs : J ∈ X ↔ J ∈ Y
    · intro e
      apply I.d1 X Y (ag_down hJ a hs) hne
      rw [np_same _ hs, np_same _ Iff.rfl] at e
      exact add_right_cancel e
    · intro e
      exact hv1 ⟨X, Finset.mem_univ _, Y, Finset.mem_univ _, hs, by rw [e]; ring⟩
  · intro X Y a hc
    rw [hz, hz]
    by_cases hs : J ∈ X ↔ J ∈ Y
    · rw [np_same _ hs, np_same _ Iff.rfl, dist_add_right]
      exact I.d2 X Y (ag_down hJ a hs) hc
    · intro e
      apply hv2 ⟨X, Finset.mem_univ _, Y, Finset.mem_univ _, a, hs, hc, ?_⟩
      have := dsq' (np m J X (Kv v)) (np m J Y (Kv v))
      rw [e] at this
      linarith
  · intro S1 m1 S2 m2 S3 m3 h12 h13 h23 a12 a13
    rw [hz, hz, hz]
    by_cases hs : (J ∈ S1 ↔ J ∈ S2) ∧ (J ∈ S1 ↔ J ∈ S3)
    · rw [np_same _ hs.1, np_same _ hs.2, np_same _ Iff.rfl]
      have e := I.c3 S1 m1 S2 m2 S3 m3 h12 h13 h23 (ag_down hJ a12 hs.1) (ag_down hJ a13 hs.2)
      intro h0
      apply e
      rw [← h0]
      simp only [crP, cr, PiLp.add_apply]
      ring
    · intro e
      exact hv3 ⟨S1, m1, S2, m2, S3, m3, h12, h13, h23, a12, a13, hs, e⟩
  · intro S1 m1 S2 m2 S3 m3 S4 m4 h12 h13 h14 h23 h24 h34 a12 a13 a14
    rw [hz, hz, hz, hz]
    by_cases hs : (J ∈ S1 ↔ J ∈ S2) ∧ (J ∈ S1 ↔ J ∈ S3) ∧ (J ∈ S1 ↔ J ∈ S4)
    · rw [np_same _ hs.1, np_same _ hs.2.1, np_same _ hs.2.2, np_same _ Iff.rfl]
      have e := I.c4 S1 m1 S2 m2 S3 m3 S4 m4 h12 h13 h14 h23 h24 h34 (ag_down hJ a12 hs.1)
        (ag_down hJ a13 hs.2.1) (ag_down hJ a14 hs.2.2)
      intro h0
      apply e
      rw [← h0]
      simp only [concP, concR, PiLp.add_apply]
      ring
    · intro e
      exact hv4 ⟨S1, m1, S2, m2, S3, m3, S4, m4, h12, h13, h14, h23, h24, h34, a12, a13, a14, hs, e⟩

end Step

/-- P3 + P4: a good choice for all n elements -/
theorem exists_inv (F : Finset (Finset (Fin n))) (hseed : NoFourStar F) :
    ∃ m : Fin n → ℕ, Inv F n m := by
  have key : ∀ j, j ≤ n → ∃ m : Fin n → ℕ, Inv F j m := by
    intro j
    induction j with
    | zero => intro _; exact ⟨fun _ => 0, inv_zero F _⟩
    | succ j ih =>
      intro hj
      obtain ⟨m, hm⟩ := ih (by omega)
      obtain ⟨v, hv⟩ := inv_step (J := ⟨j, by omega⟩) hm rfl hseed
      exact ⟨_, hv⟩
  exact key n le_rfl

end Greedy

/-! ## the reduction to seeds (P1 is the only remaining hypothesis) -/

theorem block_of_seed {k n : ℕ} (F : Finset (Finset (Fin n))) (hseed : NoFourStar F)
    (hchi : ¬ ∃ col : Finset (Fin n) → Fin k, ∀ S ∈ F, ∀ T ∈ F, JAdj S T → col S ≠ col T) :
    BlockProp k := by
  classical
  obtain ⟨m, I⟩ := exists_inv F hseed
  set cq : Fin n → ℚ := fun j => ((m j : ℚ) ^ 2 - 1) / ((m j : ℚ) ^ 2 + 1) with hcq
  set sq : Fin n → ℚ := fun j => 2 * (m j : ℚ) / ((m j : ℚ) ^ 2 + 1) with hsq
  have hcs : ∀ j, cq j ^ 2 + sq j ^ 2 = 1 := by
    intro j
    simp only [hcq, hsq]
    have : ((m j : ℚ) ^ 2 + 1) ≠ 0 := by positivity
    field_simp
    ring
  have hK : (fun j => Kpt (cq j) (sq j)) = fun j => Kv (m j) := by
    funext j
    simp only [hcq, hsq, Kv, cv, sv]
    congr 1 <;> simp
  have hz : zS (fun j => Kpt (cq j) (sq j)) = zm m := by rw [hK]; rfl
  have hinj : Set.InjOn (zS (fun j => Kpt (cq j) (sq j))) (F : Set (Finset (Fin n))) := by
    rw [hz]
    intro X _ Y _ e
    by_contra hne
    exact I.d1 X Y (agree_top X Y) hne e
  have hgp : NoThreeOnLine ((F.image (zS (fun j => Kpt (cq j) (sq j))) : Finset Plane) : Set Plane) ∧
      NoFourOnCircle ((F.image (zS (fun j => Kpt (cq j) (sq j))) : Finset Plane) : Set Plane) := by
    rw [hz]
    constructor
    · intro a ha b hb c hc hab hac hbc hcol
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha hb hc
      obtain ⟨S1, m1, rfl⟩ := ha
      obtain ⟨S2, m2, rfl⟩ := hb
      obtain ⟨S3, m3, rfl⟩ := hc
      exact I.c3 S1 m1 S2 m2 S3 m3 (fun e => hab (by rw [e])) (fun e => hac (by rw [e]))
        (fun e => hbc (by rw [e])) (agree_top _ _) (agree_top _ _) (crP_of_collinear hcol)
    · intro a ha b hb c hc d hd hab hac had hbc hbd hcd hcos
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha hb hc hd
      obtain ⟨S1, m1, rfl⟩ := ha
      obtain ⟨S2, m2, rfl⟩ := hb
      obtain ⟨S3, m3, rfl⟩ := hc
      obtain ⟨S4, m4, rfl⟩ := hd
      exact I.c4 S1 m1 S2 m2 S3 m3 S4 m4 (fun e => hab (by rw [e])) (fun e => hac (by rw [e]))
        (fun e => had (by rw [e])) (fun e => hbc (by rw [e])) (fun e => hbd (by rw [e]))
        (fun e => hcd (by rw [e])) (agree_top _ _) (agree_top _ _) (agree_top _ _)
        (concP_of_cospherical hcos)
  obtain ⟨G, hG, hG'⟩ := block_of_additive cq sq hcs F hinj hgp hchi
  exact ⟨G, hG, hG'⟩

/-- erdos-130 from the purely combinatorial seed statement P1. -/
theorem main_of_seeds (h : ∀ k : ℕ, ∃ n : ℕ, ∃ F : Finset (Finset (Fin n)), NoFourStar F ∧
      ¬ ∃ col : Finset (Fin n) → Fin k, ∀ S ∈ F, ∀ T ∈ F, JAdj S T → col S ≠ col T) :
    ∃ A : Set Plane, A.Infinite ∧ NoThreeOnLine A ∧ NoFourOnCircle A ∧
      ∀ k : ℕ, ¬ ∃ f : Plane → Fin k, ProperColouring A f :=
  main_of_blocks (fun k => by
    obtain ⟨n, F, h1, h2⟩ := h k
    exact block_of_seed F h1 h2)

end Erdos130Gen

/-!
erdos-130, layer P1.6 (agent G): the numeric inequality, in ℕ, with symbolic parameters
N = t Q, M = q t, R = 2 q^3 t, Q = q^4, a = t w (w = m - 1), r = Q.
-/

namespace Erdos130Gen

theorem pow_le_three_pow_mul_factorial (n : ℕ) : n ^ n ≤ 3 ^ n * n.factorial := by
  have h := Real.pow_div_factorial_le_exp (x := (n : ℝ)) (Nat.cast_nonneg n) n
  have he : Real.exp (n : ℝ) ≤ 3 ^ n := by
    rw [← Real.exp_one_rpow, Real.rpow_natCast]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  rw [div_le_iff₀ hf] at h
  have : (n : ℝ) ^ n ≤ 3 ^ n * n.factorial := by nlinarith
  exact_mod_cast this

theorem choose_mul_pow_le (R a : ℕ) : R.choose a * a ^ a ≤ 3 ^ a * R ^ a := by
  have h1 : a.factorial * R.choose a ≤ R ^ a := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]; exact Nat.descFactorial_le_pow R a
  have h2 := pow_le_three_pow_mul_factorial a
  calc R.choose a * a ^ a ≤ R.choose a * (3 ^ a * a.factorial) := Nat.mul_le_mul_left _ h2
    _ = 3 ^ a * (a.factorial * R.choose a) := by ring
    _ ≤ 3 ^ a * R ^ a := Nat.mul_le_mul_left _ h1

theorem choose_mono_half {N i t : ℕ} (hit : i ≤ t) (ht : 2 * t ≤ N) : N.choose i ≤ N.choose t := by
  induction t with
  | zero => rw [Nat.le_zero.1 hit]
  | succ t ih =>
    rcases Nat.lt_or_ge i (t + 1) with h | h
    · have := ih (by omega) (by omega)
      exact this.trans (Nat.choose_le_succ_of_lt_half_left (by omega))
    · rw [le_antisymm hit h]

/-- the fingerprint count -/
theorem sum_choose_mul_pow_le {N t : ℕ} (ht : 2 * t ≤ N) :
    (∑ i ∈ Finset.range (t + 1), N.choose i) * t ^ t ≤ (t + 1) * (3 ^ t * N ^ t) := by
  have h1 : ∑ i ∈ Finset.range (t + 1), N.choose i ≤ (t + 1) * N.choose t := by
    calc ∑ i ∈ Finset.range (t + 1), N.choose i ≤ ∑ _i ∈ Finset.range (t + 1), N.choose t :=
          Finset.sum_le_sum (fun i hi => choose_mono_half (by rw [Finset.mem_range] at hi; omega) ht)
      _ = (t + 1) * N.choose t := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  calc (∑ i ∈ Finset.range (t + 1), N.choose i) * t ^ t ≤ (t + 1) * N.choose t * t ^ t :=
        Nat.mul_le_mul_right _ h1
    _ = (t + 1) * (N.choose t * t ^ t) := by ring
    _ ≤ (t + 1) * (3 ^ t * N ^ t) := Nat.mul_le_mul_left _ (choose_mul_pow_le N t)

theorem descFactorial_mul_pow_le {M N : ℕ} (h : M ≤ N) :
    ∀ a, M.descFactorial a * N ^ a ≤ N.descFactorial a * M ^ a := by
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
    have h2 : (M - a) * N ≤ (N - a) * M := by
      rcases Nat.lt_or_ge M a with hMa | hMa
      · rw [Nat.sub_eq_zero_of_le hMa.le]; simp
      · have e1 : (M - a) * N + a * N = M * N := by
          rw [← add_mul, Nat.sub_add_cancel hMa]
        have e2 : (N - a) * M + a * M = N * M := by
          rw [← add_mul, Nat.sub_add_cancel (hMa.trans h)]
        have : a * M ≤ a * N := Nat.mul_le_mul_left _ h
        nlinarith
    calc (M - a) * M.descFactorial a * (N ^ a * N) = ((M - a) * N) * (M.descFactorial a * N ^ a) := by ring
      _ ≤ ((N - a) * M) * (N.descFactorial a * M ^ a) := Nat.mul_le_mul h2 ih
      _ = (N - a) * N.descFactorial a * (M ^ a * M) := by ring

/-- ratio of binomials -/
theorem choose_sub_mul_pow_le {N M a : ℕ} (haM : a ≤ M) (hMN : M ≤ N) :
    (N - a).choose (M - a) * N ^ a ≤ N.choose M * M ^ a := by
  have hid := Nat.choose_mul (n := N) (k := M) (s := a) haM
  have hpos : 0 < N.descFactorial a := Nat.descFactorial_pos.2 (haM.trans hMN)
  have key : (N - a).choose (M - a) * N ^ a * N.descFactorial a ≤
      N.choose M * M ^ a * N.descFactorial a := by
    have e1 : N.descFactorial a = a.factorial * N.choose a := Nat.descFactorial_eq_factorial_mul_choose N a
    have e2 : M.descFactorial a = a.factorial * M.choose a := Nat.descFactorial_eq_factorial_mul_choose M a
    have h3 := descFactorial_mul_pow_le hMN a
    calc (N - a).choose (M - a) * N ^ a * N.descFactorial a
        = a.factorial * (N.choose a * (N - a).choose (M - a)) * N ^ a := by rw [e1]; ring
      _ = a.factorial * (N.choose M * M.choose a) * N ^ a := by rw [hid]
      _ = N.choose M * (M.descFactorial a * N ^ a) := by rw [e2]; ring
      _ ≤ N.choose M * (N.descFactorial a * M ^ a) := Nat.mul_le_mul_left _ h3
      _ = N.choose M * M ^ a * N.descFactorial a := by ring
  exact Nat.le_of_mul_le_mul_right key hpos

theorem core_ineq (t Q w a : ℕ) (ha : a = t * w) (ht : 1 ≤ t) (hw : 12 ≤ w) (hQ : 12 * Q ≤ 2 ^ w) :
    3 * (t + 1) * (3 * Q) ^ t * 6 ^ a < 2 * w ^ a := by
  have h1 : (12 * Q) ^ t ≤ 2 ^ a := by
    calc (12 * Q) ^ t ≤ (2 ^ w) ^ t := Nat.pow_le_pow_left hQ t
      _ = 2 ^ a := by rw [← pow_mul, ha, mul_comm]
  have h2 : 12 ^ a ≤ w ^ a := Nat.pow_le_pow_left hw a
  have h3 : 3 * (t + 1) < 2 * 4 ^ t := by
    have e1 : t + 1 ≤ 2 ^ t := Nat.lt_two_pow_self
    have e2 : 2 ≤ 2 ^ t := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht
    have e3 : 4 ^ t = 2 ^ t * 2 ^ t := by rw [← mul_pow]; norm_num
    rw [e3]
    nlinarith
  have h4 : 4 ^ t * (3 * (t + 1) * (3 * Q) ^ t * 6 ^ a) < 4 ^ t * (2 * w ^ a) := by
    have e : (12 * Q) ^ t = 4 ^ t * (3 * Q) ^ t := by rw [← mul_pow]; ring_nf
    calc 4 ^ t * (3 * (t + 1) * (3 * Q) ^ t * 6 ^ a) = 3 * (t + 1) * (12 * Q) ^ t * 6 ^ a := by
          rw [e]; ring
      _ ≤ 3 * (t + 1) * 2 ^ a * 6 ^ a := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
      _ = 3 * (t + 1) * 12 ^ a := by rw [mul_assoc, ← mul_pow]; norm_num
      _ ≤ 3 * (t + 1) * w ^ a := Nat.mul_le_mul_left _ h2
      _ < 2 * 4 ^ t * w ^ a := Nat.mul_lt_mul_of_pos_right h3 (Nat.pow_pos (by omega))
      _ = 4 ^ t * (2 * w ^ a) := by ring
  exact Nat.lt_of_mul_lt_mul_left h4

/-- the container term -/
theorem term1 (q t w S : ℕ) (ht : 1 ≤ t) (hw : 12 ≤ w) (hQ : 12 * q ^ 4 ≤ 2 ^ w) (hwq : w ≤ q)
    (hS : S * t ^ t ≤ (t + 1) * (3 ^ t * (t * q ^ 4) ^ t)) :
    3 * (S * ((2 * q ^ 3 * t).choose (t * w) * (t * q ^ 4 - t * w).choose (q * t - t * w))) <
      2 * (t * q ^ 4).choose (q * t) := by
  have hq : 1 ≤ q := by omega
  have haM : t * w ≤ q * t := by rw [mul_comm q]; exact Nat.mul_le_mul_left _ hwq
  have hMN : q * t ≤ t * q ^ 4 := by
    rw [mul_comm q]
    exact Nat.mul_le_mul_left _ (by
      calc q = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ 4 := Nat.pow_le_pow_right hq (by norm_num))
  set N := t * q ^ 4
  set M := q * t
  set R := 2 * q ^ 3 * t
  set a := t * w
  set C := N.choose M
  have hX2 := choose_mul_pow_le R a
  have hX3 := choose_sub_mul_pow_le haM hMN
  have hcore := core_ineq t (q ^ 4) w a rfl ht hw hQ
  have hP : 0 < t ^ t * a ^ a * N ^ a := by
    have : 0 < a := Nat.mul_pos (by omega) (by omega)
    have : 0 < N := Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
    positivity
  -- the key comparison
  have hkey : 3 * ((t + 1) * (3 ^ t * N ^ t)) * (3 ^ a * R ^ a) * M ^ a <
      2 * (t ^ t * a ^ a * N ^ a) := by
    have ea : a ^ a = t ^ a * w ^ a := by simp only [a]; rw [mul_pow]
    have eNa : N ^ a = t ^ a * (q ^ 4) ^ a := by simp only [N]; rw [mul_pow]
    have e6 : (6 : ℕ) ^ a = 3 ^ a * 2 ^ a := by rw [← mul_pow]; norm_num
    have hpos : 0 < t ^ t * (t ^ a) ^ 2 * (q ^ 4) ^ a := by
      have : 0 < t := by omega
      positivity
    calc 3 * ((t + 1) * (3 ^ t * N ^ t)) * (3 ^ a * R ^ a) * M ^ a
        = (3 * (t + 1) * (3 * q ^ 4) ^ t * 6 ^ a) * (t ^ t * (t ^ a) ^ 2 * (q ^ 4) ^ a) := by
          rw [e6]; simp only [N, R, M]; ring
      _ < (2 * w ^ a) * (t ^ t * (t ^ a) ^ 2 * (q ^ 4) ^ a) := Nat.mul_lt_mul_of_pos_right hcore hpos
      _ = 2 * (t ^ t * a ^ a * N ^ a) := by rw [ea, eNa]; ring
  have hlhs : 3 * (S * (R.choose a * (N - a).choose (M - a))) * (t ^ t * a ^ a * N ^ a) ≤
      3 * ((t + 1) * (3 ^ t * N ^ t)) * (3 ^ a * R ^ a) * M ^ a * C := by
    calc 3 * (S * (R.choose a * (N - a).choose (M - a))) * (t ^ t * a ^ a * N ^ a)
        = 3 * (S * t ^ t) * (R.choose a * a ^ a) * ((N - a).choose (M - a) * N ^ a) := by ring
      _ ≤ 3 * ((t + 1) * (3 ^ t * N ^ t)) * (3 ^ a * R ^ a) * (C * M ^ a) := by
          gcongr
      _ = 3 * ((t + 1) * (3 ^ t * N ^ t)) * (3 ^ a * R ^ a) * M ^ a * C := by ring
  have hC : 0 < C := Nat.choose_pos hMN
  have hfin : 3 * (S * (R.choose a * (N - a).choose (M - a))) * (t ^ t * a ^ a * N ^ a) <
      2 * C * (t ^ t * a ^ a * N ^ a) := by
    calc _ ≤ _ := hlhs
      _ < 2 * (t ^ t * a ^ a * N ^ a) * C := Nat.mul_lt_mul_of_pos_right hkey hC
      _ = 2 * C * (t ^ t * a ^ a * N ^ a) := by ring
  exact Nat.lt_of_mul_lt_mul_right hfin

/-- the pruning term -/
theorem term2 (q t : ℕ) (ht : 1 ≤ t) (hq : 4 ≤ q) :
    6 * (t * q ^ 4 * (q ^ 4 * (q.choose 3 * (t * q ^ 4 - 4).choose (q * t - 4)))) ≤
      q * t * (t * q ^ 4).choose (q * t) := by
  have h4M : 4 ≤ q * t := le_trans hq (Nat.le_mul_of_pos_right q (by omega))
  have hMN : q * t ≤ t * q ^ 4 := by
    rw [mul_comm q]
    exact Nat.mul_le_mul_left _ (by
      calc q = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num))
  set N := t * q ^ 4
  set M := q * t
  set C := N.choose M
  have hr := choose_sub_mul_pow_le h4M hMN
  have h6 : 6 * q.choose 3 ≤ q ^ 3 := by
    have := Nat.descFactorial_le_pow q 3
    rw [Nat.descFactorial_eq_factorial_mul_choose] at this
    simpa [Nat.factorial] using this
  have hN4 : 0 < N ^ 4 := by
    have : 0 < N := Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
    positivity
  have key : 6 * (N * (q ^ 4 * (q.choose 3 * (N - 4).choose (M - 4)))) * N ^ 4 ≤ M * C * N ^ 4 := by
    calc 6 * (N * (q ^ 4 * (q.choose 3 * (N - 4).choose (M - 4)))) * N ^ 4
        = N * q ^ 4 * (6 * q.choose 3) * ((N - 4).choose (M - 4) * N ^ 4) := by ring
      _ ≤ N * q ^ 4 * q ^ 3 * (C * M ^ 4) := by gcongr
      _ = (q ^ 7 * M ^ 3) * (M * C * N) := by ring
      _ ≤ N ^ 3 * (M * C * N) := by
          gcongr
          simp only [M, N]
          have : q ^ 7 * (q * t) ^ 3 ≤ (t * q ^ 4) ^ 3 := by
            have e : q ^ 7 * (q * t) ^ 3 = t ^ 3 * q ^ 10 := by ring
            have e' : (t * q ^ 4) ^ 3 = t ^ 3 * q ^ 12 := by ring
            rw [e, e']
            exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by norm_num))
          exact this
      _ = M * C * N ^ 4 := by ring
  exact Nat.le_of_mul_le_mul_right key hN4

end Erdos130Gen

/-!
erdos-130, layer P1.0 (agent G): the Hamming form of the seed.
A set V of words Fin r → Fin q with at most 3 points on every coordinate line and a Hamming-1 graph that
is not k-colourable gives, through function graphs {(i, f i)} ⊆ Fin r × Fin q ≃ Fin (r * q), a family
with no four members at symmetric distance 1 from a common set (NoFourStar) whose swap graph (JAdj) is
not k-colourable.
-/

namespace Erdos130Gen

section Hamming

variable {r q : ℕ}

/-- Hamming adjacency: distinct words differing in at most (hence exactly) one coordinate -/
def HAdj (x y : Fin r → Fin q) : Prop := x ≠ y ∧ ∃ i, ∀ j, j ≠ i → x j = y j

/-- every coordinate line meets V in at most 3 points -/
def LinesLe3 (V : Finset (Fin r → Fin q)) : Prop :=
  ∀ x ∈ V, ∀ i : Fin r, (V.filter (fun y => ∀ j, j ≠ i → y j = x j)).card ≤ 3

def idx (i : Fin r) (c : Fin q) : Fin (r * q) := finProdFinEquiv (i, c)

theorem idx_inj {i j : Fin r} {c d : Fin q} : idx i c = idx j d ↔ i = j ∧ c = d := by
  unfold idx
  rw [finProdFinEquiv.apply_eq_iff_eq, Prod.mk.injEq]

theorem idx_surj (z : Fin (r * q)) : ∃ i c, z = idx i c := by
  refine ⟨(finProdFinEquiv.symm z).1, (finProdFinEquiv.symm z).2, ?_⟩
  unfold idx
  rw [Prod.mk.eta, Equiv.apply_symm_apply]

/-- the function graph -/
def gr (f : Fin r → Fin q) : Finset (Fin (r * q)) := Finset.univ.image (fun i => idx i (f i))

theorem mem_gr {f : Fin r → Fin q} {i : Fin r} {c : Fin q} : idx i c ∈ gr f ↔ f i = c := by
  unfold gr
  simp only [Finset.mem_image, Finset.mem_univ, true_and, idx_inj]
  constructor
  · rintro ⟨j, rfl, h⟩; exact h
  · intro h; exact ⟨i, rfl, h⟩

theorem gr_injective : Function.Injective (gr (r := r) (q := q)) := by
  intro f g h
  funext i
  have : idx i (f i) ∈ gr g := by rw [← h, mem_gr]
  rw [mem_gr] at this
  exact this.symm

theorem jadj_of_hadj {x y : Fin r → Fin q} (h : HAdj x y) : JAdj (gr x) (gr y) := by
  obtain ⟨hne, i, hi⟩ := h
  have hxi : x i ≠ y i := by
    intro e; apply hne; funext j
    by_cases hj : j = i
    · rw [hj, e]
    · exact hi j hj
  refine ⟨idx i (x i), idx i (y i), mem_gr.2 rfl, mem_gr.2 rfl, fun h' => hxi (mem_gr.1 h').symm,
    fun h' => hxi (mem_gr.1 h'), ?_⟩
  ext z
  obtain ⟨j, c, rfl⟩ := idx_surj z
  simp only [Finset.mem_erase, mem_gr, ne_eq, idx_inj, not_and]
  by_cases hj : j = i
  · subst hj
    constructor
    · rintro ⟨h1, h2⟩; exact absurd h2.symm (h1 rfl)
    · rintro ⟨h1, h2⟩; exact absurd h2.symm (h1 rfl)
  · rw [hi j hj]
    constructor
    · rintro ⟨-, h2⟩; exact ⟨fun h' => absurd h' hj, h2⟩
    · rintro ⟨-, h2⟩; exact ⟨fun h' => absurd h' hj, h2⟩

/-- the shape of a set at symmetric distance 1 -/
theorem sd_one {n : ℕ} {S R : Finset (Fin n)} (h : (symmDiff S R).card = 1) :
    (∃ a ∈ S, R = S.erase a) ∨ (∃ b, b ∉ S ∧ R = insert b S) := by
  obtain ⟨z, hz⟩ := Finset.card_eq_one.1 h
  have hzm : z ∈ symmDiff S R := by rw [hz]; exact Finset.mem_singleton_self z
  have hother : ∀ w, w ≠ z → (w ∈ S ↔ w ∈ R) := by
    intro w hw
    have : w ∉ symmDiff S R := by rw [hz, Finset.mem_singleton]; exact hw
    rw [Finset.mem_symmDiff] at this
    tauto
  rw [Finset.mem_symmDiff] at hzm
  rcases hzm with ⟨hzS, hzR⟩ | ⟨hzR, hzS⟩
  · left
    refine ⟨z, hzS, ?_⟩
    ext w
    rw [Finset.mem_erase]
    by_cases hw : w = z
    · subst hw; simp [hzR]
    · rw [← hother w hw]; simp [hw]
  · right
    refine ⟨z, hzS, ?_⟩
    ext w
    rw [Finset.mem_insert]
    by_cases hw : w = z
    · subst hw; simp [hzR]
    · rw [← hother w hw]; simp [hw]

theorem card_gr (f : Fin r → Fin q) : (gr f).card = r := by
  unfold gr
  rw [Finset.card_image_of_injective _ (fun i j h => (idx_inj.1 h).1), Finset.card_univ,
    Fintype.card_fin]

/-- the erase case: R inside the graph of f1, then every member containing R is on a line of f1 -/
theorem line_of_erase {f1 f : Fin r → Fin q} {a : Fin (r * q)} (ha : a ∈ gr f1)
    (hsub : (gr f1).erase a ⊆ gr f) : ∃ i, ∀ j, j ≠ i → f j = f1 j := by
  obtain ⟨i, c, rfl⟩ := idx_surj a
  refine ⟨i, fun j hj => ?_⟩
  have : idx j (f1 j) ∈ (gr f1).erase (idx i c) := by
    rw [Finset.mem_erase, ne_eq, idx_inj]
    exact ⟨fun h => hj h.1, mem_gr.2 rfl⟩
  exact (mem_gr.1 (hsub this))

theorem noFourStar_of_lines (V : Finset (Fin r → Fin q)) (hV : LinesLe3 V) :
    NoFourStar (V.image gr) := by
  classical
  intro R S1 h1 S2 h2 S3 h3 S4 h4 d12 d13 d14 d23 d24 d34 c1 c2 c3 c4
  simp only [Finset.mem_image] at h1 h2 h3 h4
  obtain ⟨f1, m1, rfl⟩ := h1
  obtain ⟨f2, m2, rfl⟩ := h2
  obtain ⟨f3, m3, rfl⟩ := h3
  obtain ⟨f4, m4, rfl⟩ := h4
  have n12 : f1 ≠ f2 := fun e => d12 (by rw [e])
  have n13 : f1 ≠ f3 := fun e => d13 (by rw [e])
  have n14 : f1 ≠ f4 := fun e => d14 (by rw [e])
  have n23 : f2 ≠ f3 := fun e => d23 (by rw [e])
  have n24 : f2 ≠ f4 := fun e => d24 (by rw [e])
  have n34 : f3 ≠ f4 := fun e => d34 (by rw [e])
  rcases sd_one c1 with ⟨a, ha, hR⟩ | ⟨b, hb, hR⟩
  · -- R = gr f1 minus a point: f2, f3, f4 lie on a line of f1
    have hcard : R.card + 1 = r := by
      rw [hR, Finset.card_erase_of_mem ha, card_gr]
      have : 0 < (gr f1).card := Finset.card_pos.2 ⟨a, ha⟩
      rw [card_gr] at this
      omega
    have hsub : ∀ f : Fin r → Fin q, (symmDiff (gr f) R).card = 1 → (gr f1).erase a ⊆ gr f := by
      intro f hf
      rcases sd_one hf with ⟨a', ha', hR'⟩ | ⟨b', hb', hR'⟩
      · rw [← hR, hR']; exact Finset.erase_subset _ _
      · exfalso
        have : R.card = r + 1 := by rw [hR', Finset.card_insert_of_notMem hb', card_gr]
        omega
    obtain ⟨i, -⟩ := line_of_erase ha (hsub f2 c2)
    obtain ⟨i0, c0, rfl⟩ := idx_surj a
    have hl : ∀ f : Fin r → Fin q, (symmDiff (gr f) R).card = 1 → ∀ j, j ≠ i0 → f j = f1 j := by
      intro f hf j hj
      have : idx j (f1 j) ∈ (gr f1).erase (idx i0 c0) := by
        rw [Finset.mem_erase, ne_eq, idx_inj]
        exact ⟨fun h => hj h.1, mem_gr.2 rfl⟩
      exact mem_gr.1 (hsub f hf this)
    have hline := hV f1 m1 i0
    have hsub4 : ({f1, f2, f3, f4} : Finset (Fin r → Fin q)) ⊆
        V.filter (fun y => ∀ j, j ≠ i0 → y j = f1 j) := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rw [Finset.mem_filter]
      rcases hy with rfl | rfl | rfl | rfl
      · exact ⟨m1, fun j _ => rfl⟩
      · exact ⟨m2, hl _ c2⟩
      · exact ⟨m3, hl _ c3⟩
      · exact ⟨m4, hl _ c4⟩
    have h4c : ({f1, f2, f3, f4} : Finset (Fin r → Fin q)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [n12, n13, n14]),
        Finset.card_insert_of_notMem (by simp [n23, n24]),
        Finset.card_insert_of_notMem (by simp [n34]), Finset.card_singleton]
    have := Finset.card_le_card hsub4
    omega
  · -- R = gr f1 plus a point: every member is f1 or one fixed modification
    obtain ⟨i, c, rfl⟩ := idx_surj b
    have hc : f1 i ≠ c := fun e => hb (mem_gr.2 e)
    have hsub : ∀ f : Fin r → Fin q, (symmDiff (gr f) R).card = 1 → gr f ⊆ R := by
      intro f hf
      rcases sd_one hf with ⟨a', ha', hR'⟩ | ⟨b', hb', hR'⟩
      · exfalso
        have e1 : R.card = r + 1 := by rw [hR, Finset.card_insert_of_notMem hb, card_gr]
        have e2 : R.card + 1 = r := by
          rw [hR', Finset.card_erase_of_mem ha', card_gr]
          have : 0 < (gr f).card := Finset.card_pos.2 ⟨a', ha'⟩
          rw [card_gr] at this
          omega
        omega
      · rw [hR']; exact Finset.subset_insert _ _
    have two : ∀ f : Fin r → Fin q, (symmDiff (gr f) R).card = 1 →
        f = f1 ∨ f = Function.update f1 i c := by
      intro f hf
      have hs := hsub f hf
      have key : ∀ j, (j = i ∧ f j = c) ∨ f1 j = f j := by
        intro j
        have : idx j (f j) ∈ R := hs (mem_gr.2 rfl)
        rw [hR, Finset.mem_insert, idx_inj, mem_gr] at this
        rcases this with ⟨h1, h2⟩ | h
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr h
      by_cases hfi : f i = c
      · right
        funext j
        by_cases hj : j = i
        · subst hj; rw [Function.update_self]; exact hfi
        · rw [Function.update_of_ne hj]
          rcases key j with ⟨h1, -⟩ | h
          · exact absurd h1 hj
          · exact h.symm
      · left
        funext j
        rcases key j with ⟨h1, h2⟩ | h
        · subst h1; exact absurd h2 hfi
        · exact h.symm
    rcases two f2 c2 with e2 | e2
    · exact n12 e2.symm
    rcases two f3 c3 with e3 | e3
    · exact n13 e3.symm
    exact n23 (e2.trans e3.symm)

/-- P1.0: the Hamming seed gives the seed of `main_of_seeds` -/
theorem seed_of_hamming {k : ℕ} (V : Finset (Fin r → Fin q)) (hV : LinesLe3 V)
    (hchi : ¬ ∃ col : (Fin r → Fin q) → Fin k, ∀ x ∈ V, ∀ y ∈ V, HAdj x y → col x ≠ col y) :
    ∃ n : ℕ, ∃ F : Finset (Finset (Fin n)), NoFourStar F ∧
      ¬ ∃ col : Finset (Fin n) → Fin k, ∀ S ∈ F, ∀ T ∈ F, JAdj S T → col S ≠ col T := by
  classical
  refine ⟨r * q, V.image gr, noFourStar_of_lines V hV, ?_⟩
  rintro ⟨col, hcol⟩
  apply hchi
  refine ⟨fun x => col (gr x), fun x hx y hy hxy => ?_⟩
  exact hcol _ (Finset.mem_image_of_mem _ hx) _ (Finset.mem_image_of_mem _ hy) (jadj_of_hadj hxy)

/-- P1.1: pigeonhole -/
theorem not_colourable_of_alpha {k s : ℕ} (W : Finset (Fin r → Fin q))
    (hadj : ∀ I ⊆ W, s ≤ I.card → ∃ x ∈ I, ∃ y ∈ I, HAdj x y) (hsize : k * (s - 1) < W.card) :
    ¬ ∃ col : (Fin r → Fin q) → Fin k, ∀ x ∈ W, ∀ y ∈ W, HAdj x y → col x ≠ col y := by
  classical
  rintro ⟨col, hcol⟩
  have hmap : ∀ x ∈ W, col x ∈ (Finset.univ : Finset (Fin k)) := fun _ _ => Finset.mem_univ _
  obtain ⟨c, -, hc⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmap
    (by rw [Finset.card_univ, Fintype.card_fin]; exact hsize)
  obtain ⟨x, hx, y, hy, hxy⟩ := hadj _ (Finset.filter_subset _ _) (Nat.le_of_pred_lt hc)
  rw [Finset.mem_filter] at hx hy
  exact hcol x hx.1 y hy.1 hxy (hx.2.trans hy.2.symm)

/-- P1.2: deleting the points on overloaded lines -/
def prune (V : Finset (Fin r → Fin q)) : Finset (Fin r → Fin q) :=
  V.filter (fun x => ∀ i : Fin r, (V.filter (fun y => ∀ j, j ≠ i → y j = x j)).card ≤ 3)

theorem prune_lines (V : Finset (Fin r → Fin q)) : LinesLe3 (prune V) := by
  intro x hx i
  have hx' := (Finset.mem_filter.1 hx).2 i
  refine le_trans (Finset.card_le_card ?_) hx'
  intro y hy
  rw [Finset.mem_filter] at hy ⊢
  exact ⟨(Finset.mem_filter.1 hy.1).1, hy.2⟩

theorem prune_subset (V : Finset (Fin r → Fin q)) : prune V ⊆ V := Finset.filter_subset _ _

/-- HP1 from a set V whose large subsets are not independent and whose pruning is large -/
theorem hamming_seed_of_dense {k s : ℕ} (V : Finset (Fin r → Fin q))
    (hadj : ∀ I ⊆ V, s ≤ I.card → ∃ x ∈ I, ∃ y ∈ I, HAdj x y) (hsize : k * (s - 1) < (prune V).card) :
    LinesLe3 (prune V) ∧
      ¬ ∃ col : (Fin r → Fin q) → Fin k, ∀ x ∈ prune V, ∀ y ∈ prune V, HAdj x y → col x ≠ col y :=
  ⟨prune_lines V, not_colourable_of_alpha (prune V)
    (fun I hI hs => hadj I (hI.trans (prune_subset V)) hs) hsize⟩

/-! ## DenseV skeleton: the counting argument (P1.5/P1.6 enter as the hypothesis `hbad`) -/

/-- independent set of the Hamming graph -/
def Indep (I : Finset (Fin r → Fin q)) : Prop := ∀ x ∈ I, ∀ y ∈ I, ¬ HAdj x y

/-- the bad M-subsets: an independent s-subset, or at least half of the points pruned -/
def IsBad (M s : ℕ) (V : Finset (Fin r → Fin q)) : Prop :=
  (∃ I ⊆ V, I.card = s ∧ Indep I) ∨ M ≤ 2 * (V \ prune V).card

open Classical in
theorem dense_of_count {k M s : ℕ} (hsM : 2 * k * s ≤ M)
    (hbad : ((Finset.univ.powersetCard M).filter (fun V => IsBad (r := r) (q := q) M s V)).card <
      (Finset.univ.powersetCard M : Finset (Finset (Fin r → Fin q))).card) :
    ∃ V : Finset (Fin r → Fin q), (∀ I ⊆ V, s ≤ I.card → ∃ x ∈ I, ∃ y ∈ I, HAdj x y) ∧
      k * (s - 1) < (prune V).card := by
  classical
  obtain ⟨V, hV, hnb⟩ : ∃ V ∈ (Finset.univ.powersetCard M : Finset (Finset (Fin r → Fin q))),
      ¬ IsBad M s V := by
    by_contra hc
    push Not at hc
    have : (Finset.univ.powersetCard M).filter (fun V => IsBad (r := r) (q := q) M s V) =
        Finset.univ.powersetCard M := Finset.filter_true_of_mem hc
    rw [this] at hbad
    exact lt_irrefl _ hbad
  have hcard : V.card = M := (Finset.mem_powersetCard.1 hV).2
  unfold IsBad at hnb
  push Not at hnb
  obtain ⟨h1, h2⟩ := hnb
  refine ⟨V, fun I hI hs => ?_, ?_⟩
  · obtain ⟨J, hJI, hJ⟩ := Finset.exists_subset_card_eq hs
    have hni := h1 J (hJI.trans hI) hJ
    unfold Indep at hni
    push Not at hni
    obtain ⟨x, hx, y, hy, hxy⟩ := hni
    exact ⟨x, hJI hx, y, hJI hy, hxy⟩
  · have hsplit : (prune V).card + (V \ prune V).card = V.card := by
      rw [add_comm, Finset.card_sdiff_add_card_eq_card (prune_subset V)]
    have : k * (s - 1) ≤ k * s := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp only [zero_mul]
      omega
    · have e : 2 * k * s = 2 * (k * s) := by ring
      have : k * s ≤ M / 2 := by omega
      omega

open Classical in
theorem card_supersets_le (M : ℕ) (W : Finset (Fin r → Fin q)) :
    ((Finset.univ.powersetCard M).filter (fun V => W ⊆ V)).card ≤
      (Fintype.card (Fin r → Fin q) - W.card).choose (M - W.card) := by
  have h := Finset.card_le_card_of_injOn (fun V => V \ W)
    (s := (Finset.univ.powersetCard M).filter (fun V => W ⊆ V))
    (t := (Finset.univ \ W).powersetCard (M - W.card)) (by
      intro V hV
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hV
      rw [Finset.mem_coe, Finset.mem_powersetCard]
      exact ⟨Finset.sdiff_subset_sdiff (Finset.subset_univ _) le_rfl,
        by rw [Finset.card_sdiff_of_subset hV.2, hV.1.2]⟩) (by
      intro V1 h1 V2 h2 e
      rw [Finset.mem_coe, Finset.mem_filter] at h1 h2
      have := congrArg (fun A => A ∪ W) e
      simp only [Finset.sdiff_union_of_subset h1.2, Finset.sdiff_union_of_subset h2.2] at this
      exact this)
  rwa [Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ] at h

open Classical in
/-- P1.5a: the independent-set part of the bad sets, counted through containers -/
theorem bad1_card_le {M s t R : ℕ} (Φ : Finset (Fin r → Fin q) → Finset (Fin r → Fin q))
    (hΦ : ∀ T, (Φ T).card ≤ R)
    (hcont : ∀ I : Finset (Fin r → Fin q), Indep I → ∃ T ⊆ I, T.card ≤ t ∧ I ⊆ T ∪ Φ T) :
    ((Finset.univ.powersetCard M).filter
        (fun V => ∃ I ⊆ V, I.card = s ∧ Indep (r := r) (q := q) I)).card ≤
      ((Finset.univ : Finset (Finset (Fin r → Fin q))).filter (fun T => T.card ≤ t)).card *
        (R.choose (s - t) * (Fintype.card (Fin r → Fin q) - (s - t)).choose (M - (s - t))) := by
  set 𝒯 := (Finset.univ : Finset (Finset (Fin r → Fin q))).filter (fun T => T.card ≤ t)
  have hsub : (Finset.univ.powersetCard M).filter
        (fun V => ∃ I ⊆ V, I.card = s ∧ Indep (r := r) (q := q) I) ⊆
      𝒯.biUnion (fun T => ((Φ T).powersetCard (s - t)).biUnion
        (fun W => (Finset.univ.powersetCard M).filter (fun V => W ⊆ V))) := by
    intro V hV
    rw [Finset.mem_filter] at hV
    obtain ⟨hVM, I, hIV, hIs, hI⟩ := hV
    obtain ⟨T, hTI, hTt, hIc⟩ := hcont I hI
    have hcard : s - t ≤ (I ∩ Φ T).card := by
      have h1 : I.card ≤ (T ∪ (I ∩ Φ T)).card := by
        apply Finset.card_le_card
        intro x hx
        rcases Finset.mem_union.1 (hIc hx) with h | h
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hx, h⟩)
      have h2 := Finset.card_union_le T (I ∩ Φ T)
      omega
    obtain ⟨W, hW, hWc⟩ := Finset.exists_subset_card_eq hcard
    rw [Finset.mem_biUnion]
    refine ⟨T, Finset.mem_filter.2 ⟨Finset.mem_univ _, hTt⟩, ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨W, Finset.mem_powersetCard.2 ⟨hW.trans Finset.inter_subset_right, hWc⟩, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨hVM, (hW.trans Finset.inter_subset_left).trans hIV⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_biUnion_le).trans ?_
  rw [← smul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ (fun T _ => ?_)
  refine (Finset.card_biUnion_le).trans ?_
  rw [← smul_eq_mul]
  have hc : ((Φ T).powersetCard (s - t)).card ≤ R.choose (s - t) := by
    rw [Finset.card_powersetCard]; exact Nat.choose_le_choose _ (hΦ T)
  calc ∑ W ∈ (Φ T).powersetCard (s - t), ((Finset.univ.powersetCard M).filter (fun V => W ⊆ V)).card
      ≤ ∑ W ∈ (Φ T).powersetCard (s - t),
          (Fintype.card (Fin r → Fin q) - (s - t)).choose (M - (s - t)) := by
        apply Finset.sum_le_sum
        intro W hW
        have := card_supersets_le M W
        rwa [(Finset.mem_powersetCard.1 hW).2] at this
    _ = ((Φ T).powersetCard (s - t)).card • (Fintype.card (Fin r → Fin q) - (s - t)).choose (M - (s - t)) := by
        rw [Finset.sum_const]
    _ ≤ R.choose (s - t) • (Fintype.card (Fin r → Fin q) - (s - t)).choose (M - (s - t)) :=
        Nat.mul_le_mul_right _ hc

/-- the coordinate line through x in direction i -/
def lineSet (x : Fin r → Fin q) (i : Fin r) : Finset (Fin r → Fin q) :=
  Finset.univ.filter (fun y => ∀ j, j ≠ i → y j = x j)

theorem card_lineSet_le (x : Fin r → Fin q) (i : Fin r) : (lineSet x i).card ≤ q := by
  have h := Finset.card_le_card_of_injOn (fun y => y i) (s := lineSet x i)
    (t := (Finset.univ : Finset (Fin q))) (by intro y _; exact Finset.mem_coe.2 (Finset.mem_univ _)) (by
      intro y1 h1 y2 h2 e
      rw [Finset.mem_coe, lineSet, Finset.mem_filter] at h1 h2
      funext j
      by_cases hj : j = i
      · subst hj; exact e
      · rw [h1.2 j hj, h2.2 j hj])
  rwa [Finset.card_univ, Fintype.card_fin] at h

open Classical in
/-- a pruned point lies with three more points of V on one line -/
theorem pruned_witness {V : Finset (Fin r → Fin q)} {x : Fin r → Fin q} (hx : x ∈ V \ prune V) :
    ∃ i, ∃ Y ∈ ((lineSet x i).erase x).powersetCard 3, insert x Y ⊆ V := by
  rw [Finset.mem_sdiff] at hx
  obtain ⟨hxV, hxp⟩ := hx
  unfold prune at hxp
  rw [Finset.mem_filter] at hxp
  push Not at hxp
  obtain ⟨i, hi⟩ := hxp hxV
  have hc : 3 ≤ ((V.filter (fun y => ∀ j, j ≠ i → y j = x j)).erase x).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨hxV, fun j _ => rfl⟩)]
    omega
  obtain ⟨Y, hY, hYc⟩ := Finset.exists_subset_card_eq hc
  refine ⟨i, Y, Finset.mem_powersetCard.2 ⟨fun y hy => ?_, hYc⟩, ?_⟩
  · have := hY hy
    rw [Finset.mem_erase, Finset.mem_filter] at this
    rw [Finset.mem_erase, lineSet, Finset.mem_filter]
    exact ⟨this.1, Finset.mem_univ _, this.2.2⟩
  · intro y hy
    rw [Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · exact hxV
    · have := hY hy
      rw [Finset.mem_erase, Finset.mem_filter] at this
      exact this.2.1

open Classical in
/-- P1.5b: the total number of pruned points over all M-subsets -/
theorem sum_pruned_le (M : ℕ) :
    ∑ V ∈ (Finset.univ.powersetCard M : Finset (Finset (Fin r → Fin q))), (V \ prune V).card ≤
      Fintype.card (Fin r → Fin q) *
        (r * (q.choose 3 * (Fintype.card (Fin r → Fin q) - 4).choose (M - 4))) := by
  have e : ∑ V ∈ (Finset.univ.powersetCard M : Finset (Finset (Fin r → Fin q))), (V \ prune V).card =
      ∑ x : Fin r → Fin q, ((Finset.univ.powersetCard M).filter (fun V => x ∈ V \ prune V)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro V _
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    congr 1
    ext y
    simp
  rw [e]
  refine (Finset.sum_le_card_nsmul Finset.univ _
    (r * (q.choose 3 * (Fintype.card (Fin r → Fin q) - 4).choose (M - 4))) (fun x _ => ?_)).trans
    (le_of_eq (by rw [Finset.card_univ, smul_eq_mul]))
  have hsub : (Finset.univ.powersetCard M).filter (fun V => x ∈ V \ prune V) ⊆
      (Finset.univ : Finset (Fin r)).biUnion (fun i => (((lineSet x i).erase x).powersetCard 3).biUnion
        (fun Y => (Finset.univ.powersetCard M).filter (fun V => insert x Y ⊆ V))) := by
    intro V hV
    rw [Finset.mem_filter] at hV
    obtain ⟨i, Y, hY, hYV⟩ := pruned_witness hV.2
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    exact ⟨i, Y, hY, hV.1, hYV⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  refine (Finset.sum_le_card_nsmul Finset.univ _
    (q.choose 3 * (Fintype.card (Fin r → Fin q) - 4).choose (M - 4)) (fun i _ => ?_)).trans
    (le_of_eq (by rw [Finset.card_univ, Fintype.card_fin, smul_eq_mul]))
  refine (Finset.card_biUnion_le).trans ?_
  have hc : (((lineSet x i).erase x).powersetCard 3).card ≤ q.choose 3 := by
    rw [Finset.card_powersetCard]
    exact Nat.choose_le_choose _ ((Finset.card_erase_le).trans (card_lineSet_le x i))
  calc ∑ Y ∈ ((lineSet x i).erase x).powersetCard 3,
        ((Finset.univ.powersetCard M).filter (fun V => insert x Y ⊆ V)).card
      ≤ ∑ Y ∈ ((lineSet x i).erase x).powersetCard 3,
          (Fintype.card (Fin r → Fin q) - 4).choose (M - 4) := by
        apply Finset.sum_le_sum
        intro Y hY
        have hY' := Finset.mem_powersetCard.1 hY
        have hx : x ∉ Y := fun h => (Finset.mem_erase.1 (hY'.1 h)).1 rfl
        have := card_supersets_le M (insert x Y)
        rwa [Finset.card_insert_of_notMem hx, hY'.2] at this
    _ = (((lineSet x i).erase x).powersetCard 3).card * (Fintype.card (Fin r → Fin q) - 4).choose (M - 4) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ q.choose 3 * (Fintype.card (Fin r → Fin q) - 4).choose (M - 4) := Nat.mul_le_mul_right _ hc

/-! ## P1.4 Kleitman–Winston containers with a uniform degree bound -/

section KW

open Classical

/-- U-neighbourhood of x -/
noncomputable def nbr (U : Finset (Fin r → Fin q)) (x : Fin r → Fin q) : Finset (Fin r → Fin q) :=
  U.filter (fun y => HAdj x y)

/-- the greedy run with membership oracle T; returns the container part -/
noncomputable def kwRun (R D : ℕ) (T : Finset (Fin r → Fin q)) (U : Finset (Fin r → Fin q)) :
    Finset (Fin r → Fin q) :=
  if hU : R < U.card then
    if h : ∃ x ∈ U, D ≤ (nbr U x).card then
      if Classical.choose h ∈ T then
        kwRun R D T (U \ insert (Classical.choose h) (nbr U (Classical.choose h)))
      else kwRun R D T (U.erase (Classical.choose h))
    else U
  else U
termination_by U.card
decreasing_by
  · exact Finset.card_lt_card (Finset.sdiff_ssubset (Finset.insert_subset (Classical.choose_spec h).1
      (Finset.filter_subset _ _)) (Finset.insert_nonempty _ _))
  · exact Finset.card_erase_lt_of_mem (Classical.choose_spec h).1

/-- the fingerprint of I -/
noncomputable def kwFp (R D : ℕ) (I : Finset (Fin r → Fin q)) (U : Finset (Fin r → Fin q)) :
    Finset (Fin r → Fin q) :=
  if hU : R < U.card then
    if h : ∃ x ∈ U, D ≤ (nbr U x).card then
      if Classical.choose h ∈ I then
        insert (Classical.choose h)
          (kwFp R D I (U \ insert (Classical.choose h) (nbr U (Classical.choose h))))
      else kwFp R D I (U.erase (Classical.choose h))
    else ∅
  else ∅
termination_by U.card
decreasing_by
  · exact Finset.card_lt_card (Finset.sdiff_ssubset (Finset.insert_subset (Classical.choose_spec h).1
      (Finset.filter_subset _ _)) (Finset.insert_nonempty _ _))
  · exact Finset.card_erase_lt_of_mem (Classical.choose_spec h).1

theorem kw_induct {P : Finset (Fin r → Fin q) → Prop}
    (step : ∀ U, (∀ U', U'.card < U.card → P U') → P U) : ∀ U, P U := by
  intro U
  induction h : U.card using Nat.strong_induction_on generalizing U with
  | _ n ih => exact step U (fun U' hU' => ih _ (h ▸ hU') U' rfl)

theorem kwFp_sub (R D : ℕ) (I : Finset (Fin r → Fin q)) :
    ∀ U, kwFp R D I U ⊆ I ∩ U := by
  refine kw_induct (fun U ih => ?_)
  rw [kwFp]
  split_ifs with hU h hx
  · have hxU := (Classical.choose_spec h).1
    refine Finset.insert_subset (Finset.mem_inter.2 ⟨hx, hxU⟩) ((ih _ ?_).trans ?_)
    · exact Finset.card_lt_card (Finset.sdiff_ssubset (Finset.insert_subset hxU
        (Finset.filter_subset _ _)) (Finset.insert_nonempty _ _))
    · exact Finset.inter_subset_inter le_rfl Finset.sdiff_subset
  · refine (ih _ (Finset.card_erase_lt_of_mem (Classical.choose_spec h).1)).trans ?_
    exact Finset.inter_subset_inter le_rfl (Finset.erase_subset _ _)
  · exact Finset.empty_subset _
  · exact Finset.empty_subset _

theorem kwRun_congr (R D : ℕ) :
    ∀ U, ∀ T T' : Finset (Fin r → Fin q), (∀ x ∈ U, (x ∈ T ↔ x ∈ T')) → kwRun R D T U = kwRun R D T' U := by
  refine kw_induct (fun U ih => ?_)
  intro T T' hTT
  rw [kwRun, kwRun]
  by_cases hU : R < U.card
  · rw [dif_pos hU, dif_pos hU]
    by_cases h : ∃ x ∈ U, D ≤ (nbr U x).card
    · rw [dif_pos h, dif_pos h]
      have hxU := (Classical.choose_spec h).1
      have hlt1 : (U \ insert (Classical.choose h) (nbr U (Classical.choose h))).card < U.card :=
        Finset.card_lt_card (Finset.sdiff_ssubset (Finset.insert_subset hxU
          (Finset.filter_subset _ _)) (Finset.insert_nonempty _ _))
      have hlt2 := Finset.card_erase_lt_of_mem hxU
      by_cases hx : Classical.choose h ∈ T
      · rw [if_pos hx, if_pos ((hTT _ hxU).1 hx)]
        exact ih _ hlt1 T T' (fun y hy => hTT y (Finset.sdiff_subset hy))
      · rw [if_neg hx, if_neg (fun h' => hx ((hTT _ hxU).2 h'))]
        exact ih _ hlt2 T T' (fun y hy => hTT y (Finset.erase_subset _ _ hy))
    · rw [dif_neg h, dif_neg h]
  · rw [dif_neg hU, dif_neg hU]

theorem kwRun_fp (R D : ℕ) (I : Finset (Fin r → Fin q)) :
    ∀ U, kwRun R D (kwFp R D I U) U = kwRun R D I U := by
  refine kw_induct (fun U ih => ?_)
  by_cases hU : R < U.card
  · by_cases h : ∃ x ∈ U, D ≤ (nbr U x).card
    · have hxU := (Classical.choose_spec h).1
      set x := Classical.choose h with hxdef
      have hlt1 : (U \ insert x (nbr U x)).card < U.card :=
        Finset.card_lt_card (Finset.sdiff_ssubset (Finset.insert_subset hxU
          (Finset.filter_subset _ _)) (Finset.insert_nonempty _ _))
      have hlt2 := Finset.card_erase_lt_of_mem hxU
      by_cases hx : x ∈ I
      · have hfp : kwFp R D I U = insert x (kwFp R D I (U \ insert x (nbr U x))) := by
          rw [kwFp, dif_pos hU, dif_pos h, if_pos hx]
        have hxf : x ∈ kwFp R D I U := by rw [hfp]; exact Finset.mem_insert_self _ _
        rw [kwRun, kwRun, dif_pos hU, dif_pos h, dif_pos hU, dif_pos h, if_pos hxf, if_pos hx]
        rw [← ih _ hlt1]
        apply kwRun_congr
        intro y hy
        rw [hfp, Finset.mem_insert]
        have : y ≠ x := fun e => by
          rw [e] at hy; exact (Finset.mem_sdiff.1 hy).2 (Finset.mem_insert_self _ _)
        simp [this]
      · have hfp : kwFp R D I U = kwFp R D I (U.erase x) := by
          rw [kwFp, dif_pos hU, dif_pos h, if_neg hx]
        have hxf : x ∉ kwFp R D I U := fun h' => hx (Finset.mem_inter.1 (kwFp_sub R D I U h')).1
        rw [kwRun, kwRun, dif_pos hU, dif_pos h, dif_pos hU, dif_pos h, if_neg hxf, if_neg hx, hfp]
        exact ih _ hlt2
    · rw [kwRun, kwRun, dif_pos hU, dif_neg h, dif_pos hU, dif_neg h]
  · rw [kwRun, kwRun, dif_neg hU, dif_neg hU]

theorem kw_cover (R D : ℕ) (I : Finset (Fin r → Fin q)) (hI : Indep I) :
    ∀ U, I ∩ U ⊆ kwFp R D I U ∪ kwRun R D I U := by
  refine kw_induct (fun U ih => ?_)
  intro z hz
  rw [Finset.mem_inter] at hz
  by_cases hU : R < U.card
  · by_cases h : ∃ x ∈ U, D ≤ (nbr U x).card
    · have hxU := (Classical.choose_spec h).1
      set x := Classical.choose h with hxdef
      have hlt1 : (U \ insert x (nbr U x)).card < U.card :=
        Finset.card_lt_card (Finset.sdiff_ssubset (Finset.insert_subset hxU
          (Finset.filter_subset _ _)) (Finset.insert_nonempty _ _))
      have hlt2 := Finset.card_erase_lt_of_mem hxU
      by_cases hx : x ∈ I
      · rw [kwFp, kwRun, dif_pos hU, dif_pos h, dif_pos hU, dif_pos h, if_pos hx, if_pos hx]
        by_cases hzx : z = x
        · exact Finset.mem_union_left _ (by rw [hzx]; exact Finset.mem_insert_self _ _)
        · have hzn : z ∉ nbr U x := by
            intro hn
            exact hI x hx z hz.1 (Finset.mem_filter.1 hn).2
          have hz' : z ∈ I ∩ (U \ insert x (nbr U x)) := by
            rw [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_insert]
            exact ⟨hz.1, hz.2, by tauto⟩
          rcases Finset.mem_union.1 (ih _ hlt1 hz') with h1 | h1
          · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem h1)
          · exact Finset.mem_union_right _ h1
      · rw [kwFp, kwRun, dif_pos hU, dif_pos h, dif_pos hU, dif_pos h, if_neg hx, if_neg hx]
        have hzx : z ≠ x := fun e => hx (e ▸ hz.1)
        exact ih _ hlt2 (Finset.mem_inter.2 ⟨hz.1, Finset.mem_erase.2 ⟨hzx, hz.2⟩⟩)
    · rw [kwRun, dif_pos hU, dif_neg h]
      exact Finset.mem_union_right _ hz.2
  · rw [kwRun, dif_neg hU]
    exact Finset.mem_union_right _ hz.2

theorem kwFp_card (R D : ℕ) (I : Finset (Fin r → Fin q)) :
    ∀ U, (D + 1) * (kwFp R D I U).card ≤ U.card := by
  refine kw_induct (fun U ih => ?_)
  rw [kwFp]
  split_ifs with hU h hx
  · have hxU := (Classical.choose_spec h).1
    have hdeg := (Classical.choose_spec h).2
    set x := Classical.choose h
    have hsub : insert x (nbr U x) ⊆ U := Finset.insert_subset hxU (Finset.filter_subset _ _)
    have hlt1 : (U \ insert x (nbr U x)).card < U.card :=
      Finset.card_lt_card (Finset.sdiff_ssubset hsub (Finset.insert_nonempty _ _))
    have hxn : x ∉ nbr U x := fun hn => (Finset.mem_filter.1 hn).2.1 rfl
    have hc : (U \ insert x (nbr U x)).card + (D + 1) ≤ U.card := by
      rw [Finset.card_sdiff_of_subset hsub, Finset.card_insert_of_notMem hxn]
      have := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hxn] at this
      omega
    have := ih _ hlt1
    have h2 := Finset.card_insert_le x (kwFp R D I (U \ insert x (nbr U x)))
    nlinarith
  · have hxU := (Classical.choose_spec h).1
    have := ih _ (Finset.card_erase_lt_of_mem hxU)
    have h2 := Finset.card_erase_of_mem hxU
    omega
  · simp
  · simp

theorem kwRun_card (R D : ℕ) (hdeg : ∀ U : Finset (Fin r → Fin q), R < U.card → ∃ x ∈ U, D ≤ (nbr U x).card)
    (T : Finset (Fin r → Fin q)) : ∀ U, (kwRun R D T U).card ≤ R := by
  refine kw_induct (fun U ih => ?_)
  rw [kwRun]
  split_ifs with hU h hx
  · exact ih _ (Finset.card_lt_card (Finset.sdiff_ssubset (Finset.insert_subset (Classical.choose_spec h).1
      (Finset.filter_subset _ _)) (Finset.insert_nonempty _ _)))
  · exact ih _ (Finset.card_erase_lt_of_mem (Classical.choose_spec h).1)
  · exact absurd (hdeg U hU) h
  · omega

/-- P1.4: the container statement used by `bad_lt_of_numeric` -/
theorem kw_containers (R D : ℕ)
    (hdeg : ∀ U : Finset (Fin r → Fin q), R < U.card → ∃ x ∈ U, D ≤ (nbr U x).card) :
    (∀ T : Finset (Fin r → Fin q), (kwRun R D T Finset.univ).card ≤ R) ∧
    ∀ I : Finset (Fin r → Fin q), Indep I → ∃ T ⊆ I,
      (D + 1) * T.card ≤ Fintype.card (Fin r → Fin q) ∧ I ⊆ T ∪ kwRun R D T Finset.univ := by
  refine ⟨fun T => kwRun_card R D hdeg T _, fun I hI => ⟨kwFp R D I Finset.univ, ?_, ?_, ?_⟩⟩
  · exact (kwFp_sub R D I _).trans Finset.inter_subset_left
  · have := kwFp_card R D I Finset.univ
    rwa [Finset.card_univ] at this
  · intro z hz
    have := kw_cover R D I hI Finset.univ (Finset.mem_inter.2 ⟨hz, Finset.mem_univ _⟩)
    rw [kwRun_fp]; exact this

end KW

/-! ## P1.3 supersaturation -/

section Super

open Classical

def proj (hq : 0 < q) (i : Fin r) (x : Fin r → Fin q) : Fin r → Fin q := Function.update x i ⟨0, hq⟩

theorem proj_eq_iff (hq : 0 < q) {i : Fin r} {x y : Fin r → Fin q} :
    proj hq i x = proj hq i y ↔ ∀ j, j ≠ i → x j = y j := by
  constructor
  · intro h j hj
    have := congrFun h j
    simp only [proj, Function.update_of_ne hj] at this
    exact this
  · intro h
    funext j
    by_cases hj : j = i
    · subst hj; simp [proj]
    · simp only [proj, Function.update_of_ne hj]; exact h j hj

def lineIn (U : Finset (Fin r → Fin q)) (i : Fin r) (x : Fin r → Fin q) : Finset (Fin r → Fin q) :=
  U.filter (fun y => ∀ j, j ≠ i → y j = x j)

theorem nbr_card (U : Finset (Fin r → Fin q)) {x : Fin r → Fin q} (hx : x ∈ U) :
    (nbr U x).card + r = ∑ i, (lineIn U i x).card := by
  have hU : nbr U x = (Finset.univ : Finset (Fin r)).biUnion (fun i => (lineIn U i x).erase x) := by
    ext y
    have e1 : y ∈ nbr U x ↔ y ∈ U ∧ HAdj x y := Finset.mem_filter
    rw [e1, Finset.mem_biUnion]
    simp only [lineIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, HAdj]
    constructor
    · rintro ⟨hy, hxy, i, hi⟩
      exact ⟨i, fun e => hxy e.symm, hy, fun j hj => (hi j hj).symm⟩
    · rintro ⟨i, hyx, hy, hi⟩
      exact ⟨hy, fun e => hyx e.symm, i, fun j hj => (hi j hj).symm⟩
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin r))) (fun i => (lineIn U i x).erase x) := by
    intro i _ i' _ hii'
    rw [Function.onFun, Finset.disjoint_left]
    intro y hy hy'
    simp only [lineIn, Finset.mem_erase, Finset.mem_filter] at hy hy'
    apply hy.1
    funext j
    by_cases hj : j = i
    · subst hj; exact hy'.2.2 j hii'
    · exact hy.2.2 j hj
  rw [hU, Finset.card_biUnion hdisj]
  have e2 : ∑ i, (lineIn U i x).card = ∑ i, (((lineIn U i x).erase x).card + 1) := by
    apply Finset.sum_congr rfl
    intro i _
    have hxm : x ∈ lineIn U i x := Finset.mem_filter.2 ⟨hx, fun j _ => rfl⟩
    rw [Finset.card_erase_of_mem hxm]
    have := Finset.card_pos.2 ⟨x, hxm⟩
    omega
  rw [e2, Finset.sum_add_distrib]
  simp

theorem img_card (hq : 0 < q) (U : Finset (Fin r → Fin q)) (i : Fin r) :
    (U.image (proj hq i)).card * q ≤ q ^ r := by
  have h := Finset.card_le_card_of_injOn (fun p : (Fin r → Fin q) × Fin q => Function.update p.1 i p.2)
    (s := (U.image (proj hq i)) ×ˢ (Finset.univ : Finset (Fin q)))
    (t := (Finset.univ : Finset (Fin r → Fin q))) (by intro p _; exact Finset.mem_coe.2 (Finset.mem_univ _)) (by
      intro p hp p' hp' e
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_image] at hp hp'
      obtain ⟨⟨a, -, ha⟩, -⟩ := hp
      obtain ⟨⟨a', -, ha'⟩, -⟩ := hp'
      have e2 := congrFun e i
      simp only [Function.update_self] at e2
      have e1 : p.1 = p'.1 := by
        funext j
        by_cases hj : j = i
        · subst hj; rw [← ha, ← ha']; simp [proj]
        · have := congrFun e j
          simp only [Function.update_of_ne hj] at this
          exact this
      exact Prod.ext e1 e2)
  rwa [Finset.card_product, Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_pi,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_fin] at h

theorem sum_line_ge (hq : 0 < q) (U : Finset (Fin r → Fin q)) (i : Fin r) :
    q * U.card ^ 2 ≤ q ^ r * ∑ x ∈ U, (lineIn U i x).card := by
  set img := U.image (proj hq i)
  have hfib : ∑ x ∈ U, (lineIn U i x).card =
      ∑ c ∈ img, (U.filter (fun x => proj hq i x = c)).card ^ 2 := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := U) (t := img) (g := proj hq i)
      (fun x hx => Finset.mem_image_of_mem _ hx)]
    apply Finset.sum_congr rfl
    intro c _
    have : ∀ x ∈ U.filter (fun x => proj hq i x = c),
        (lineIn U i x).card = (U.filter (fun x => proj hq i x = c)).card := by
      intro x hx
      congr 1
      ext y
      simp only [lineIn, Finset.mem_filter] at hx ⊢
      rw [← hx.2, proj_eq_iff]
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, sq]
  have hsum : ∑ c ∈ img, (U.filter (fun x => proj hq i x = c)).card = U.card :=
    (Finset.card_eq_sum_card_fiberwise (fun x hx => Finset.mem_image_of_mem _ hx)).symm
  have hcs : (∑ c ∈ img, (U.filter (fun x => proj hq i x = c)).card) ^ 2 ≤
      img.card * ∑ c ∈ img, (U.filter (fun x => proj hq i x = c)).card ^ 2 := sq_sum_le_card_mul_sum_sq
  rw [hsum] at hcs
  have himg := img_card hq U i
  rw [hfib]
  calc q * U.card ^ 2 ≤ q * (img.card * ∑ c ∈ img, (U.filter (fun x => proj hq i x = c)).card ^ 2) :=
        Nat.mul_le_mul_left _ hcs
    _ = (img.card * q) * ∑ c ∈ img, (U.filter (fun x => proj hq i x = c)).card ^ 2 := by ring
    _ ≤ q ^ r * ∑ c ∈ img, (U.filter (fun x => proj hq i x = c)).card ^ 2 := Nat.mul_le_mul_right _ himg

/-- P1.3: a large set has a vertex of degree ≥ r inside it -/
theorem hdeg_hamming (hq : 0 < q) (hr : 0 < r) (U : Finset (Fin r → Fin q))
    (hU : 2 * q ^ r < q * U.card) : ∃ x ∈ U, r ≤ (nbr U x).card := by
  by_contra hc
  push Not at hc
  have hsum : ∑ x ∈ U, ∑ i, (lineIn U i x).card ≤ (2 * r - 1) * U.card := by
    rw [mul_comm, ← smul_eq_mul]
    refine Finset.sum_le_card_nsmul U (fun x => ∑ i, (lineIn U i x).card) ((2 * r - 1) : ℕ)
      (fun x hx => ?_)
    show ∑ i, (lineIn U i x).card ≤ 2 * r - 1
    rw [← nbr_card U hx]
    have := hc x hx
    omega
  have hdir : r * (q * U.card ^ 2) ≤ q ^ r * ∑ x ∈ U, ∑ i, (lineIn U i x).card := by
    rw [Finset.sum_comm, Finset.mul_sum]
    calc r * (q * U.card ^ 2) = ∑ _i : Fin r, q * U.card ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ ≤ ∑ i : Fin r, q ^ r * ∑ x ∈ U, (lineIn U i x).card :=
          Finset.sum_le_sum (fun i _ => sum_line_ge hq U i)
  have h3 : r * (q * U.card ^ 2) ≤ q ^ r * ((2 * r - 1) * U.card) :=
    hdir.trans (Nat.mul_le_mul_left _ hsum)
  have hpos : 0 < U.card := by
    rcases Nat.eq_zero_or_pos U.card with h | h
    · rw [h] at hU; omega
    · exact h
  have h4 : r * (q * U.card) ≤ q ^ r * (2 * r - 1) := by
    have : r * (q * U.card) * U.card ≤ q ^ r * (2 * r - 1) * U.card := by
      calc r * (q * U.card) * U.card = r * (q * U.card ^ 2) := by ring
        _ ≤ q ^ r * ((2 * r - 1) * U.card) := h3
        _ = q ^ r * (2 * r - 1) * U.card := by ring
    exact Nat.le_of_mul_le_mul_right this hpos
  have h5 : r * (2 * q ^ r) < r * (q * U.card) := Nat.mul_lt_mul_of_pos_left hU hr
  have h6 : q ^ r * (2 * r - 1) < r * (2 * q ^ r) := by
    have : 0 < q ^ r := Nat.pow_pos hq
    have e : r * (2 * q ^ r) = q ^ r * (2 * r) := by ring
    rw [e]
    exact Nat.mul_lt_mul_of_pos_left (by omega) this
  omega

end Super

open Classical in
/-- P1.5: containers + the numeric inequality give few bad M-subsets -/
theorem bad_lt_of_numeric {M s t R : ℕ} (Φ : Finset (Fin r → Fin q) → Finset (Fin r → Fin q))
    (hΦ : ∀ T, (Φ T).card ≤ R)
    (hcont : ∀ I : Finset (Fin r → Fin q), Indep I → ∃ T ⊆ I, T.card ≤ t ∧ I ⊆ T ∪ Φ T)
    (hnum : M * (((Finset.univ : Finset (Finset (Fin r → Fin q))).filter (fun T => T.card ≤ t)).card *
        (R.choose (s - t) * (Fintype.card (Fin r → Fin q) - (s - t)).choose (M - (s - t)))) +
      2 * (Fintype.card (Fin r → Fin q) *
        (r * (q.choose 3 * (Fintype.card (Fin r → Fin q) - 4).choose (M - 4)))) <
      M * (Fintype.card (Fin r → Fin q)).choose M) :
    ((Finset.univ.powersetCard M).filter (fun V => IsBad (r := r) (q := q) M s V)).card <
      (Finset.univ.powersetCard M : Finset (Finset (Fin r → Fin q))).card := by
  set 𝒱 := (Finset.univ.powersetCard M : Finset (Finset (Fin r → Fin q)))
  have h1 := bad1_card_le (M := M) (s := s) Φ hΦ hcont
  have h2 : M * (𝒱.filter (fun V => M ≤ 2 * (V \ prune V).card)).card ≤
      2 * ∑ V ∈ 𝒱, (V \ prune V).card := by
    have := Finset.card_nsmul_le_sum (𝒱.filter (fun V => M ≤ 2 * (V \ prune V).card))
      (fun V => 2 * (V \ prune V).card) M (fun V hV => (Finset.mem_filter.1 hV).2)
    rw [smul_eq_mul, mul_comm] at this
    refine this.trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have h3 := sum_pruned_le (r := r) (q := q) M
  have hu : (𝒱.filter (fun V => IsBad (r := r) (q := q) M s V)).card ≤
      (𝒱.filter (fun V => ∃ I ⊆ V, I.card = s ∧ Indep (r := r) (q := q) I)).card +
        (𝒱.filter (fun V => M ≤ 2 * (V \ prune V).card)).card := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro V hV
    rw [Finset.mem_filter] at hV
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases hV.2 with h | h
    · exact Or.inl ⟨hV.1, h⟩
    · exact Or.inr ⟨hV.1, h⟩
  have hall : 𝒱.card = (Fintype.card (Fin r → Fin q)).choose M := by
    simp only [𝒱, Finset.card_powersetCard, Finset.card_univ]
  rw [hall]
  by_contra hc
  push Not at hc
  have key := calc M * (Fintype.card (Fin r → Fin q)).choose M
      ≤ M * (𝒱.filter (fun V => IsBad (r := r) (q := q) M s V)).card := Nat.mul_le_mul_left M hc
    _ ≤ M * ((𝒱.filter (fun V => ∃ I ⊆ V, I.card = s ∧ Indep (r := r) (q := q) I)).card +
        (𝒱.filter (fun V => M ≤ 2 * (V \ prune V).card)).card) := Nat.mul_le_mul_left M hu
    _ = M * (𝒱.filter (fun V => ∃ I ⊆ V, I.card = s ∧ Indep (r := r) (q := q) I)).card +
        M * (𝒱.filter (fun V => M ≤ 2 * (V \ prune V).card)).card := Nat.mul_add _ _ _
    _ ≤ M * (((Finset.univ : Finset (Finset (Fin r → Fin q))).filter (fun T => T.card ≤ t)).card *
        (R.choose (s - t) * (Fintype.card (Fin r → Fin q) - (s - t)).choose (M - (s - t)))) +
        2 * ∑ V ∈ 𝒱, (V \ prune V).card := Nat.add_le_add (Nat.mul_le_mul_left M h1) h2
    _ ≤ M * (((Finset.univ : Finset (Finset (Fin r → Fin q))).filter (fun T => T.card ≤ t)).card *
        (R.choose (s - t) * (Fintype.card (Fin r → Fin q) - (s - t)).choose (M - (s - t)))) +
        2 * (Fintype.card (Fin r → Fin q) *
        (r * (q.choose 3 * (Fintype.card (Fin r → Fin q) - 4).choose (M - 4)))) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left 2 h3) _
  exact absurd (lt_of_le_of_lt key hnum) (lt_irrefl _)

open Classical in
/-- the final reduction of P1: counting bounds give the Hamming seed -/
theorem hamming_seed_of_count
    (h : ∀ k : ℕ, ∃ r q M s : ℕ, 2 * k * s ≤ M ∧
      ((Finset.univ.powersetCard M).filter (fun V => IsBad (r := r) (q := q) M s V)).card <
        (Finset.univ.powersetCard M : Finset (Finset (Fin r → Fin q))).card) :
    ∀ k : ℕ, ∃ n : ℕ, ∃ F : Finset (Finset (Fin n)), NoFourStar F ∧
      ¬ ∃ col : Finset (Fin n) → Fin k, ∀ S ∈ F, ∀ T ∈ F, JAdj S T → col S ≠ col T := by
  intro k
  obtain ⟨r, q, M, s, hsM, hb⟩ := h k
  obtain ⟨V, hadj, hsize⟩ := dense_of_count hsM hb
  obtain ⟨hl, hc⟩ := hamming_seed_of_dense V hadj hsize
  exact seed_of_hamming (prune V) hl hc

open Classical in
/-- P1 skeleton: supersaturation (hdeg) and the numeric inequality (hnum) give the seed. -/
theorem seeds_of_numeric
    (h : ∀ k : ℕ, ∃ r q M s R D : ℕ, 2 * k * s ≤ M ∧
      (∀ U : Finset (Fin r → Fin q), R < U.card → ∃ x ∈ U, D ≤ (nbr U x).card) ∧
      M * (((Finset.univ : Finset (Finset (Fin r → Fin q))).filter
          (fun T => T.card ≤ Fintype.card (Fin r → Fin q) / (D + 1))).card *
        (R.choose (s - Fintype.card (Fin r → Fin q) / (D + 1)) *
          (Fintype.card (Fin r → Fin q) - (s - Fintype.card (Fin r → Fin q) / (D + 1))).choose
            (M - (s - Fintype.card (Fin r → Fin q) / (D + 1))))) +
      2 * (Fintype.card (Fin r → Fin q) *
        (r * (q.choose 3 * (Fintype.card (Fin r → Fin q) - 4).choose (M - 4)))) <
      M * (Fintype.card (Fin r → Fin q)).choose M) :
    ∀ k : ℕ, ∃ n : ℕ, ∃ F : Finset (Finset (Fin n)), NoFourStar F ∧
      ¬ ∃ col : Finset (Fin n) → Fin k, ∀ S ∈ F, ∀ T ∈ F, JAdj S T → col S ≠ col T := by
  refine hamming_seed_of_count (fun k => ?_)
  obtain ⟨r, q, M, s, R, D, hsM, hdeg, hnum⟩ := h k
  obtain ⟨hΦ, hcont⟩ := kw_containers R D hdeg
  refine ⟨r, q, M, s, hsM, bad_lt_of_numeric (fun T => kwRun R D T Finset.univ) hΦ ?_ hnum⟩
  intro I hI
  obtain ⟨T, hTI, hTc, hIT⟩ := hcont I hI
  exact ⟨T, hTI, (Nat.le_div_iff_mul_le (Nat.succ_pos D)).2 (by rw [mul_comm]; exact hTc), hIT⟩

end Hamming

/-! ## final instantiation of the parameters -/

open Classical in
theorem card_small_le {r q : ℕ} (t : ℕ) :
    ((Finset.univ : Finset (Finset (Fin r → Fin q))).filter (fun T => T.card ≤ t)).card ≤
      ∑ i ∈ Finset.range (t + 1), (Fintype.card (Fin r → Fin q)).choose i := by
  calc ((Finset.univ : Finset (Finset (Fin r → Fin q))).filter (fun T => T.card ≤ t)).card
      ≤ ((Finset.range (t + 1)).biUnion
          (fun i => (Finset.univ : Finset (Fin r → Fin q)).powersetCard i)).card := by
        apply Finset.card_le_card
        intro T hT
        rw [Finset.mem_filter] at hT
        rw [Finset.mem_biUnion]
        exact ⟨T.card, Finset.mem_range.2 (by omega),
          Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, rfl⟩⟩
    _ ≤ ∑ i ∈ Finset.range (t + 1), ((Finset.univ : Finset (Fin r → Fin q)).powersetCard i).card :=
        Finset.card_biUnion_le
    _ = ∑ i ∈ Finset.range (t + 1), (Fintype.card (Fin r → Fin q)).choose i := by
        simp only [Finset.card_powersetCard, Finset.card_univ]

theorem big_two_pow (K : ℕ) : 12 * (2 * K * 2 ^ (K + 10)) ^ 4 ≤ 2 ^ (2 ^ (K + 10) - 1) := by
  have hK : K < 2 ^ K := Nat.lt_two_pow_self
  have hK4 : K ^ 4 ≤ (2 ^ K) ^ 4 := Nat.pow_le_pow_left hK.le 4
  have e : (2 * K * 2 ^ (K + 10)) ^ 4 = K ^ 4 * 2 ^ (4 * K + 44) := by ring
  have hexp : 8 * K + 48 ≤ 2 ^ (K + 10) - 1 := by
    have : 2 ^ (K + 10) = 1024 * 2 ^ K := by ring
    omega
  calc 12 * (2 * K * 2 ^ (K + 10)) ^ 4 = 12 * (K ^ 4 * 2 ^ (4 * K + 44)) := by rw [e]
    _ ≤ 16 * ((2 ^ K) ^ 4 * 2 ^ (4 * K + 44)) := by
        apply Nat.mul_le_mul (by norm_num); exact Nat.mul_le_mul_right _ hK4
    _ = 2 ^ (8 * K + 48) := by ring
    _ ≤ 2 ^ (2 ^ (K + 10) - 1) := Nat.pow_le_pow_right (by norm_num) hexp

open Classical in
/-- P1 complete: the numeric hypothesis of `seeds_of_numeric` holds for every k. -/
theorem params (k : ℕ) : ∃ r q M s R D : ℕ, 2 * k * s ≤ M ∧
      (∀ U : Finset (Fin r → Fin q), R < U.card → ∃ x ∈ U, D ≤ (nbr U x).card) ∧
      M * (((Finset.univ : Finset (Finset (Fin r → Fin q))).filter
          (fun T => T.card ≤ Fintype.card (Fin r → Fin q) / (D + 1))).card *
        (R.choose (s - Fintype.card (Fin r → Fin q) / (D + 1)) *
          (Fintype.card (Fin r → Fin q) - (s - Fintype.card (Fin r → Fin q) / (D + 1))).choose
            (M - (s - Fintype.card (Fin r → Fin q) / (D + 1))))) +
      2 * (Fintype.card (Fin r → Fin q) *
        (r * (q.choose 3 * (Fintype.card (Fin r → Fin q) - 4).choose (M - 4)))) <
      M * (Fintype.card (Fin r → Fin q)).choose M := by
  obtain ⟨K, hKdef⟩ : ∃ K, K = k + 1 := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = 2 ^ (K + 10) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = m - 1 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = 2 * K * m := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = q ^ 4 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = q ^ (r - 4) := ⟨_, rfl⟩
  have hm12 : 13 ≤ m := by
    have : 2 ^ 10 ≤ 2 ^ (K + 10) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hq4 : 4 ≤ q := by
    have : 2 * 1 * 13 ≤ 2 * K * m := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hm12
    omega
  have hq0 : 0 < q := by omega
  have hr4 : 4 ≤ r := by
    rw [hr]
    calc 4 ≤ q := hq4
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ 4 := Nat.pow_le_pow_right hq0 (by norm_num)
  have ht1 : 1 ≤ t := by rw [ht]; exact Nat.one_le_pow _ _ hq0
  have hN : q ^ r = t * q ^ 4 := by rw [ht, ← pow_add, Nat.sub_add_cancel hr4]
  have hcard : Fintype.card (Fin r → Fin q) = t * q ^ 4 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, hN]
  have hD : Fintype.card (Fin r → Fin q) / (r - 1 + 1) = t := by
    rw [hcard, Nat.sub_add_cancel (by omega : 1 ≤ r), hr]
    exact Nat.mul_div_cancel _ (Nat.pow_pos hq0)
  have hst : t * m - t = t * w := by rw [hw, Nat.mul_sub_one]
  refine ⟨r, q, q * t, t * m, 2 * q ^ 3 * t, r - 1, ?_, ?_, ?_⟩
  · have : 2 * k * (t * m) ≤ 2 * K * (t * m) := Nat.mul_le_mul_right _ (by omega)
    calc 2 * k * (t * m) ≤ 2 * K * (t * m) := this
      _ = q * t := by rw [hq]; ring
  · intro U hU
    have h2 : 2 * q ^ r < q * U.card := by
      rw [hN]
      calc 2 * (t * q ^ 4) = q * (2 * q ^ 3 * t) := by ring
        _ < q * U.card := Nat.mul_lt_mul_of_pos_left hU hq0
    obtain ⟨x, hx, hd⟩ := hdeg_hamming hq0 (by omega) U h2
    exact ⟨x, hx, le_trans (Nat.sub_le r 1) hd⟩
  · rw [hD, hst, hcard]
    set S := ((Finset.univ : Finset (Finset (Fin r → Fin q))).filter (fun T => T.card ≤ t)).card
    have hS0 := card_small_le (r := r) (q := q) t
    rw [hcard] at hS0
    have h2t : 2 * t ≤ t * q ^ 4 := by
      rw [mul_comm]
      exact Nat.mul_le_mul_left _ (by
        calc 2 ≤ 4 := by norm_num
          _ ≤ q := hq4
          _ = q ^ 1 := (pow_one q).symm
          _ ≤ q ^ 4 := Nat.pow_le_pow_right hq0 (by norm_num))
    have hS : S * t ^ t ≤ (t + 1) * (3 ^ t * (t * q ^ 4) ^ t) :=
      (Nat.mul_le_mul_right _ hS0).trans (sum_choose_mul_pow_le h2t)
    have hQ : 12 * q ^ 4 ≤ 2 ^ w := by rw [hq, hw, hm]; exact big_two_pow K
    have hwq : w ≤ q := by
      rw [hq]
      calc w ≤ m := by omega
        _ = 1 * 1 * m := by ring
        _ ≤ 2 * K * m := Nat.mul_le_mul_right _ (Nat.mul_le_mul (by norm_num) (by omega))
    have h1 := term1 q t w S ht1 (by omega) hQ hwq hS
    have h2 : 6 * (t * q ^ 4 * (r * (q.choose 3 * (t * q ^ 4 - 4).choose (q * t - 4)))) ≤
        q * t * (t * q ^ 4).choose (q * t) := by
      rw [hr]; exact term2 q t ht1 hq4
    have hP : 0 < q * t := Nat.mul_pos hq0 (by omega)
    generalize S * ((2 * q ^ 3 * t).choose (t * w) * (t * q ^ 4 - t * w).choose (q * t - t * w)) = X
      at h1 ⊢
    generalize t * q ^ 4 * (r * (q.choose 3 * (t * q ^ 4 - 4).choose (q * t - 4))) = Y at h2 ⊢
    generalize (t * q ^ 4).choose (q * t) = C at h1 h2 ⊢
    have hu : 3 * (q * t * X) < 2 * (q * t * C) := by
      calc 3 * (q * t * X) = q * t * (3 * X) := by ring
        _ < q * t * (2 * C) := Nat.mul_lt_mul_of_pos_left h1 hP
        _ = 2 * (q * t * C) := by ring
    generalize q * t * X = u at hu ⊢
    generalize q * t * C = v at hu h2 ⊢
    omega

/-- the full seed statement -/
theorem seeds_all : ∀ k : ℕ, ∃ n : ℕ, ∃ F : Finset (Finset (Fin n)), NoFourStar F ∧
    ¬ ∃ col : Finset (Fin n) → Fin k, ∀ S ∈ F, ∀ T ∈ F, JAdj S T → col S ≠ col T :=
  seeds_of_numeric params

end Erdos130Gen

/-- Erdős Problem 130: an infinite planar set in general position whose integer-distance graph has
infinite chromatic number. -/
theorem OMA.solution : type_of% @OMA.S_erdos_130.main :=
  Erdos130Gen.main_of_seeds Erdos130Gen.seeds_all

