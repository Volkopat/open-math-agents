import OMAStatements.S_mo_456166
import Mathlib

/-!
MathOverflow 456166 (Prowse–Woodall conjecture): every k-colourable circular-arc graph is k-choosable.
Lean formalization (ours) of R. Tao, "List colouring of circular-arc graphs", arXiv:2611.20947v1
(16 Nov 2026), Theorem 1.1. The mathematics is Tao's.
-/

section Coefficient
/-!
# A coefficient formula (Tao, arXiv:2611.20947, Lemma 3.1; a case of Schauz's formula)

For `k`-element sets `B v ⊆ K` and a polynomial `F` in the variables `x_v` of total degree at
most `|V| (k - 1)`, the coefficient of `∏ x_v ^ (k - 1)` in `F` is
`∑_{c ∈ ∏ B_v} F(c) / ∏_v ∏_{a ∈ B_v ∖ {c v}} (c v - a)`.
-/

open Finset MvPolynomial

namespace OMA.P456166

/-- The one-variable identity, from Lagrange interpolation (`Lagrange.coeff_eq_sum`). -/
theorem sum_pow_div_prod {K : Type*} [Field K] [DecidableEq K] (B : Finset K) (n : ℕ)
    (hn : n < B.card) :
    ∑ b ∈ B, b ^ n / ∏ a ∈ B.erase b, (b - a) = if n = B.card - 1 then 1 else 0 := by
  have h := Lagrange.coeff_eq_sum (s := B) (v := id) (Set.injOn_id _)
    (P := Polynomial.X ^ n) (by rw [Polynomial.degree_X_pow]; exact_mod_cast hn)
  simp only [Polynomial.coeff_X_pow, Polynomial.eval_pow, Polynomial.eval_X, id] at h
  rw [← h]
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)

/-- The constant exponent vector `v ↦ m`. -/
noncomputable def constExp (σ : Type*) [Fintype σ] (m : ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun _ => m

@[simp] theorem constExp_apply {σ : Type*} [Fintype σ] (m : ℕ) (v : σ) : constExp σ m v = m := rfl

theorem coeff_eq_sum {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K] [DecidableEq K]
    (k : ℕ) (hk : 1 ≤ k) (B : σ → Finset K) (hB : ∀ v, (B v).card = k)
    (F : MvPolynomial σ K) (hF : F.totalDegree ≤ Fintype.card σ * (k - 1)) :
    F.coeff (constExp σ (k - 1)) =
      ∑ c ∈ Fintype.piFinset B, eval c F / ∏ v, ∏ a ∈ (B v).erase (c v), (c v - a) := by
  set M := constExp σ (k - 1)
  -- rewrite the right side monomial by monomial
  have hR : ∀ c : σ → K, eval c F / ∏ v, ∏ a ∈ (B v).erase (c v), (c v - a) =
      ∑ N ∈ F.support, F.coeff N * ∏ v, ((c v) ^ (N v) / ∏ a ∈ (B v).erase (c v), (c v - a)) := by
    intro c
    rw [eval_eq', Finset.sum_div]
    refine Finset.sum_congr rfl fun N _ => ?_
    rw [Finset.prod_div_distrib, mul_div_assoc]
  simp_rw [hR]
  rw [Finset.sum_comm]
  have key : ∀ N ∈ F.support,
      ∑ c ∈ Fintype.piFinset B,
        F.coeff N * ∏ v, ((c v) ^ (N v) / ∏ a ∈ (B v).erase (c v), (c v - a)) =
        if N = M then F.coeff M else 0 := by
    intro N hN
    rw [← Finset.mul_sum, ← Finset.prod_univ_sum (t := B)
      (f := fun v b => b ^ (N v) / ∏ a ∈ (B v).erase b, (b - a))]
    split_ifs with hNM
    · subst hNM
      rw [Finset.prod_eq_one, mul_one]
      intro v _
      rw [sum_pow_div_prod _ _ (by simp [M, hB]; omega)]
      simp [M, hB]
    · -- some exponent is below `k - 1`
      have hdeg := le_totalDegree hN
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hdeg
      obtain ⟨v, hv⟩ : ∃ v, N v < k - 1 := by
        by_contra! hall
        apply hNM
        have hsum : ∑ v, N v = ∑ _v : σ, (k - 1) := by
          apply le_antisymm
          · simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]; omega
          · exact Finset.sum_le_sum fun v _ => hall v
        have := (Finset.sum_eq_sum_iff_of_le (fun v _ => hall v)).1 hsum.symm
        ext v
        simp [M, (this v (Finset.mem_univ v)).symm]
      rw [Finset.prod_eq_zero (Finset.mem_univ v), mul_zero]
      rw [sum_pow_div_prod _ _ (by rw [hB]; omega)]
      simp [hB]; omega
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact MvPolynomial.notMem_support_iff.1 h

end OMA.P456166
end Coefficient

section GraphPoly
/-!
# The graph polynomial argument (Tao, arXiv:2611.20947, proof of Theorem 2.1)

Abstract setting: every vertex `v` lies in a `k`-element set `Q v`, any two distinct members
`w, w'` of a `Q v` satisfy `w ∈ Q w'` or `w' ∈ Q w`, and some colouring `c₀` with values in a
`k`-element set `B` is injective on every `Q v`. Then for all lists `S v` of size `k` there is
`s` with `s v ∈ S v` and `s v ≠ s w` whenever `w ∈ Q v`, `w ≠ v`.

The polynomial is `P = ∏_v ∏_{w ∈ Q v ∖ {v}} (x_v - x_w)`. By `TaoCA.coeff_eq_sum` with
`B_v = B`, its coefficient at `∏ x_v ^ (k - 1)` is the number of `c ∈ B^V` with `P(c) ≠ 0`,
which is positive (`c₀`), and the Combinatorial Nullstellensatz finishes.
-/

open Finset MvPolynomial

namespace OMA.P456166

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The graph polynomial `∏_v ∏_{w ∈ Q v ∖ {v}} (x_v - x_w)`. -/
noncomputable def graphPoly (Q : V → Finset V) : MvPolynomial V ℚ :=
  ∏ v, ∏ w ∈ (Q v).erase v, (X v - X w)

theorem eval_graphPoly (Q : V → Finset V) (c : V → ℚ) :
    eval c (graphPoly Q) = ∏ v, ∏ w ∈ (Q v).erase v, (c v - c w) := by
  simp [graphPoly, map_prod]

theorem eval_graphPoly_ne_zero_iff (Q : V → Finset V) (c : V → ℚ) :
    eval c (graphPoly Q) ≠ 0 ↔ ∀ v, ∀ w ∈ Q v, w ≠ v → c v ≠ c w := by
  rw [eval_graphPoly, Finset.prod_ne_zero_iff]
  simp only [Finset.mem_univ, true_implies, Finset.prod_ne_zero_iff, Finset.mem_erase,
    ne_eq, sub_eq_zero]
  constructor
  · intro h v w hw hwv; exact h v w ⟨hwv, hw⟩
  · intro h v w hw; exact h v w hw.2 hw.1

theorem totalDegree_graphPoly (Q : V → Finset V) (k : ℕ) (hQc : ∀ v, (Q v).card = k)
    (hQv : ∀ v, v ∈ Q v) : (graphPoly Q).totalDegree ≤ Fintype.card V * (k - 1) := by
  unfold graphPoly
  refine (totalDegree_finsetProd _ _).trans ?_
  rw [Finset.card_univ.symm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun v _ => ?_
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ w ∈ (Q v).erase v, (X v - X w : MvPolynomial V ℚ).totalDegree
      ≤ ∑ _w ∈ (Q v).erase v, 1 := by
        refine Finset.sum_le_sum fun w _ => (totalDegree_sub _ _).trans ?_
        simp [totalDegree_X]
    _ = k - 1 := by
        rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem (hQv v), hQc v]

/-- If `P(c) ≠ 0` and the clique condition holds, `c` is injective on each `Q v`. -/
theorem injOn_of_eval_ne_zero (Q : V → Finset V)
    (hcl : ∀ v, ∀ w ∈ Q v, ∀ w' ∈ Q v, w ≠ w' → w ∈ Q w' ∨ w' ∈ Q w)
    (c : V → ℚ) (hc : eval c (graphPoly Q) ≠ 0) (v : V) : Set.InjOn c (Q v) := by
  rw [eval_graphPoly_ne_zero_iff] at hc
  intro w hw w' hw' hww'
  by_contra hne
  rcases hcl v w hw w' hw' hne with h | h
  · exact hc w' w h hne hww'.symm
  · exact hc w w' h (Ne.symm hne) hww'

omit [Fintype V] in
theorem prod_erase_eq (B : Finset ℚ) (k : ℕ) (hB : B.card = k) (Q : Finset V) (hQ : Q.card = k)
    (v : V) (hv : v ∈ Q) (c : V → ℚ) (hcB : ∀ w, c w ∈ B) (hinj : Set.InjOn c Q) :
    ∏ w ∈ Q.erase v, (c v - c w) = ∏ a ∈ B.erase (c v), (c v - a) := by
  have hinj' : Set.InjOn c (Q.erase v) := hinj.mono fun x hx => Finset.mem_of_mem_erase hx
  have himg' : (Q.erase v).image c = B.erase (c v) := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 ha
      refine Finset.mem_erase.2 ⟨fun h => ?_, hcB w⟩
      exact (Finset.mem_erase.1 hw).1 (hinj (Finset.mem_of_mem_erase hw) hv h)
    · rw [Finset.card_image_of_injOn hinj', Finset.card_erase_of_mem hv,
        Finset.card_erase_of_mem (hcB v), hQ, hB]
  rw [← himg', Finset.prod_image]
  intro x hx y hy hxy
  exact hinj (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase hy) hxy

theorem exists_eval_ne_zero (k : ℕ) (hk : 1 ≤ k) (Q : V → Finset V) (hQv : ∀ v, v ∈ Q v)
    (hQc : ∀ v, (Q v).card = k)
    (hcl : ∀ v, ∀ w ∈ Q v, ∀ w' ∈ Q v, w ≠ w' → w ∈ Q w' ∨ w' ∈ Q w)
    (B : Finset ℚ) (hB : B.card = k) (c₀ : V → ℚ) (hc₀B : ∀ v, c₀ v ∈ B)
    (hc₀ : ∀ v, Set.InjOn c₀ (Q v))
    (S : V → Finset ℚ) (hS : ∀ v, (S v).card = k) :
    ∃ s : V → ℚ, (∀ v, s v ∈ S v) ∧ ∀ v, ∀ w ∈ Q v, w ≠ v → s v ≠ s w := by
  set P := graphPoly Q
  have hdeg := totalDegree_graphPoly Q k hQc hQv
  have hcoeff := coeff_eq_sum k hk (fun _ => B) (fun _ => hB) P hdeg
  -- each term is `1` or `0`
  have hterm : ∀ c ∈ Fintype.piFinset fun _ : V => B,
      eval c P / ∏ v, ∏ a ∈ B.erase (c v), (c v - a) = if eval c P ≠ 0 then 1 else 0 := by
    intro c hc
    rw [Fintype.mem_piFinset] at hc
    split_ifs with h
    · have : eval c P = ∏ v, ∏ a ∈ B.erase (c v), (c v - a) := by
        rw [eval_graphPoly]
        exact Finset.prod_congr rfl fun v _ =>
          prod_erase_eq B k hB (Q v) (hQc v) v (hQv v) c hc
            (injOn_of_eval_ne_zero Q hcl c h v)
      rw [← this, div_self h]
    · rw [not_not.1 h, zero_div]
  rw [Finset.sum_congr rfl hterm, Finset.sum_boole] at hcoeff
  have hc₀P : eval c₀ P ≠ 0 := by
    rw [eval_graphPoly_ne_zero_iff]
    intro v w hw hwv h
    exact hwv (hc₀ v hw (hQv v) h.symm)
  have hne : P.coeff (constExp V (k - 1)) ≠ 0 := by
    rw [hcoeff, Nat.cast_ne_zero, Finset.card_ne_zero]
    exact ⟨c₀, Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 hc₀B, hc₀P⟩⟩
  have hdeg' : P.totalDegree = (constExp V (k - 1)).degree := by
    rw [Finsupp.degree_eq_sum]
    simp only [constExp_apply, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    refine le_antisymm hdeg ?_
    have := le_totalDegree (MvPolynomial.mem_support_iff.2 hne)
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
    simpa using this
  obtain ⟨s, hsS, hs⟩ := combinatorial_nullstellensatz_exists_eval_nonzero P
    (constExp V (k - 1)) hne hdeg' S (fun v => by rw [constExp_apply, hS]; omega)
  exact ⟨s, hsS, (eval_graphPoly_ne_zero_iff Q s).1 hs⟩

end OMA.P456166
end GraphPoly

section ArcExtension
/-!
# Arc extension (Tao, arXiv:2611.20947, proof of Theorem 1.1)

Arcs on `ℝ / ℤ`: start `a v`, length `ℓ v`; `x` is on arc `v` when `fract (x - a v) ≤ ℓ v`.
A colouring `f` has disjoint arcs inside each colour class (`hdisj`).

Tao extends each arc `X_v` to the half-open arc `T_v` from its start to the next start of its
colour class (the whole circle for a singleton class). We never build `T_v` as a set: a point `x`
lies on `T_w` exactly when `w` is the strict minimiser of `fract (x - a z)` over its colour class
(`InT`), i.e. the start of `w` is the last start of its class before `x`. Then
`Q v = {w | InT w (a v)}`, and we prove:
* `inT_of_onArc`: `X_w ⊆ T_w`;
* `inT_edge`: two half-open arcs through a common point: one contains the start of the other;
* `existsUnique_inT`: each colour class has exactly one `T_w` through each point.
-/

open Int

namespace OMA.P456166

/-- The forward-distance identity on the circle. -/
theorem fract_sub_eq {x a b : ℝ} (h : fract (x - b) ≤ fract (x - a)) :
    fract (b - a) = fract (x - a) - fract (x - b) := by
  rw [Int.fract_eq_iff]
  refine ⟨by linarith, by linarith [fract_lt_one (x - a), fract_nonneg (x - b)],
    ⌊x - a⌋ - ⌊x - b⌋, ?_⟩
  simp only [Int.fract, Int.cast_sub]
  ring

/-- Adding forward distances that stay below one lap. -/
theorem fract_add_eq {x a b : ℝ} (h : fract (b - a) + fract (x - b) < 1) :
    fract (x - a) = fract (b - a) + fract (x - b) := by
  rw [Int.fract_eq_iff]
  refine ⟨by linarith [fract_nonneg (b - a), fract_nonneg (x - b)], h,
    ⌊b - a⌋ + ⌊x - b⌋, ?_⟩
  simp only [Int.fract, Int.cast_add]
  ring

variable {V α : Type*} (a : V → ℝ) (f : V → α)

/-- `x` lies on the extended arc `T_w`: the start of `w` is strictly the last start of its colour
class before `x` (going forward around the circle). -/
def InT (w : V) (x : ℝ) : Prop :=
  ∀ z, f z = f w → z ≠ w → fract (x - a w) < fract (x - a z)

variable {a f}

/-- Two extended arcs through a common point: one contains the start of the other. -/
theorem inT_edge {u w : V} {x : ℝ} (hu : InT a f u x) (hw : InT a f w x) :
    InT a f u (a w) ∨ InT a f w (a u) := by
  -- the general case, with `w`'s start closer before `x`
  have key : ∀ u w : V, InT a f u x → fract (x - a w) ≤ fract (x - a u) → InT a f u (a w) := by
    intro u w hu hle z hz hzu
    rw [fract_sub_eq hle]
    by_contra hlt
    push Not at hlt
    have hsum : fract (a w - a z) + fract (x - a w) < 1 := by
      linarith [fract_lt_one (x - a u)]
    have := fract_add_eq hsum
    linarith [hu z hz hzu]
  rcases le_total (fract (x - a w)) (fract (x - a u)) with h | h
  · exact Or.inl (key u w hu h)
  · exact Or.inr (key w u hw h)

variable (ℓ : V → ℝ) (hℓ : ∀ v, 0 ≤ ℓ v)
  (hdisj : ∀ u v, u ≠ v → f u = f v → ∀ x, ¬ (fract (x - a u) ≤ ℓ u ∧ fract (x - a v) ≤ ℓ v))
include hℓ hdisj

/-- `X_w ⊆ T_w`. -/
theorem inT_of_onArc {w : V} {x : ℝ} (hx : fract (x - a w) ≤ ℓ w) : InT a f w x := by
  intro z hz hzw
  by_contra hlt
  push Not at hlt
  have h1 := fract_sub_eq hlt
  refine hdisj z w hzw hz (a z) ⟨by simpa using hℓ z, ?_⟩
  rw [h1]; linarith [fract_nonneg (x - a z)]

/-- Starts inside a colour class are distinct on the circle. -/
theorem fract_ne_of_same_class {z w : V} (hz : f z = f w) (hzw : z ≠ w) (x : ℝ) :
    fract (x - a z) ≠ fract (x - a w) := by
  intro h
  have h1 := fract_sub_eq h.le
  refine hdisj z w hzw hz (a z) ⟨by simpa using hℓ z, ?_⟩
  rw [h1, h, sub_self]; exact hℓ w

/-- Each nonempty colour class has a vertex whose extended arc passes through `x`. -/
theorem exists_inT [Fintype V] (x : ℝ) (w₀ : V) : ∃ w, f w = f w₀ ∧ InT a f w x := by
  classical
  obtain ⟨w, hw, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun z => f z = f w₀)
    (fun z => fract (x - a z)) ⟨w₀, by simp⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw hmin
  refine ⟨w, hw, fun z hz hzw => lt_of_le_of_ne (hmin z (hz.trans hw)) ?_⟩
  exact (fract_ne_of_same_class ℓ hℓ hdisj hz hzw x).symm

omit hℓ hdisj in
/-- At most one vertex of each colour class has its extended arc through `x`. -/
theorem inT_unique {w w' : V} {x : ℝ} (h : InT a f w x) (h' : InT a f w' x) (hf : f w = f w') :
    w = w' := by
  by_contra hne
  have := h w' hf.symm (Ne.symm hne)
  have := h' w hf hne
  linarith

end OMA.P456166
end ArcExtension

section Main
/-!
# Main theorem (Tao, arXiv:2611.20947, Theorem 1.1)

Pass to a colouring with the least number `k₀ ≤ k` of colours (it is surjective), shrink the
lists to `k₀` elements, build `Q v = {w | p_v ∈ T_w}` from the arc extension, and apply the
graph polynomial argument.
-/

open Finset OMA.S_mo_456166

namespace OMA.P456166

theorem choosable_of_surjective {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (a ℓ : V → ℝ) (hℓ : ∀ v, 0 ≤ ℓ v)
    (hadj : ∀ u v, u ≠ v → (G.Adj u v ↔ ∃ x, OnArc (a u) (ℓ u) x ∧ OnArc (a v) (ℓ v) x))
    (k : ℕ) (hk : 1 ≤ k) (C₀ : G.Coloring (Fin k)) (hsurj : Function.Surjective C₀)
    (S : V → Finset ℕ) (hS : ∀ v, (S v).card = k) :
    ∃ C : G.Coloring ℕ, ∀ v, C v ∈ S v := by
  classical
  set f : V → Fin k := ⇑C₀
  have hdisj : ∀ u v, u ≠ v → f u = f v → ∀ x,
      ¬ (Int.fract (x - a u) ≤ ℓ u ∧ Int.fract (x - a v) ≤ ℓ v) := by
    intro u v huv hf x hx
    exact C₀.valid ((hadj u v huv).2 ⟨x, hx⟩) hf
  set Q : V → Finset V := fun v => univ.filter fun w => InT a f w (a v) with hQdef
  have hmemQ : ∀ v w, w ∈ Q v ↔ InT a f w (a v) := by intro v w; simp [Q]
  have hQv : ∀ v, v ∈ Q v := fun v =>
    (hmemQ v v).2 (inT_of_onArc ℓ hℓ hdisj (by simpa using hℓ v))
  have hQinj : ∀ v, Set.InjOn f (Q v) := fun v w hw w' hw' h =>
    inT_unique ((hmemQ v w).1 hw) ((hmemQ v w').1 hw') h
  have hQc : ∀ v, (Q v).card = k := by
    intro v
    have himg : (Q v).image f = univ := by
      apply Finset.eq_univ_of_forall
      intro i
      obtain ⟨w₀, rfl⟩ := hsurj i
      obtain ⟨w, hw, hT⟩ := exists_inT ℓ hℓ hdisj (a v) w₀
      exact Finset.mem_image.2 ⟨w, (hmemQ v w).2 hT, hw⟩
    rw [← Finset.card_image_of_injOn (hQinj v), himg, Finset.card_univ, Fintype.card_fin]
  have hcl : ∀ v, ∀ w ∈ Q v, ∀ w' ∈ Q v, w ≠ w' → w ∈ Q w' ∨ w' ∈ Q w := by
    intro v w hw w' hw' _
    rw [hmemQ, hmemQ]
    exact inT_edge ((hmemQ v w).1 hw) ((hmemQ v w').1 hw')
  set B : Finset ℚ := (range k).image (Nat.cast)
  have hB : B.card = k := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, card_range]
  let c₀ : V → ℚ := fun v => ((f v : ℕ) : ℚ)
  have hc₀B : ∀ v, c₀ v ∈ B := fun v =>
    Finset.mem_image.2 ⟨f v, Finset.mem_range.2 (f v).isLt, rfl⟩
  have hc₀ : ∀ v, Set.InjOn c₀ (Q v) := by
    intro v w hw w' hw' h
    apply hQinj v hw hw'
    have h' : ((f w : ℕ) : ℚ) = ((f w' : ℕ) : ℚ) := h
    exact Fin.ext (by exact_mod_cast h')
  obtain ⟨s, hsS, hs⟩ := exists_eval_ne_zero k hk Q hQv hQc hcl B hB c₀ hc₀B hc₀
    (fun v => (S v).image Nat.cast)
    (fun v => by rw [Finset.card_image_of_injective _ Nat.cast_injective, hS])
  choose n hn hns using fun v => Finset.mem_image.1 (hsS v)
  refine ⟨SimpleGraph.Coloring.mk n ?_, hn⟩
  intro u v huv heq
  have hne : u ≠ v := G.ne_of_adj huv
  obtain ⟨x, hxu, hxv⟩ := (hadj u v hne).1 huv
  have hTu := inT_of_onArc ℓ hℓ hdisj hxu
  have hTv := inT_of_onArc ℓ hℓ hdisj hxv
  rcases inT_edge hTu hTv with h | h
  · exact hs v u ((hmemQ v u).2 h) hne (by rw [← hns v, ← hns u, heq])
  · exact hs u v ((hmemQ u v).2 h) hne.symm (by rw [← hns u, ← hns v, heq])

theorem main_proof {V : Type*} [Finite V] (G : SimpleGraph V) (hG : IsCircularArcGraph G)
    (k : ℕ) (hk : G.Colorable k) : IsKChoosable G k := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨a, ℓ, hℓ, hadj⟩ := hG
  intro L hL
  have hex : ∃ m, G.Colorable m := ⟨k, hk⟩
  have hk₀ : G.Colorable (Nat.find hex) := Nat.find_spec hex
  have hk₀k : Nat.find hex ≤ k := Nat.find_min' hex hk
  have hsub : ∀ v, ∃ S ⊆ L v, S.card = Nat.find hex := fun v =>
    Finset.exists_subset_card_eq (by rw [hL]; exact hk₀k)
  choose S hSL hS using hsub
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0] at hk₀
    have : IsEmpty V := hk₀.isEmpty
    exact ⟨SimpleGraph.Coloring.mk (fun v => isEmptyElim v) (fun {u} => isEmptyElim u),
      fun v => isEmptyElim v⟩
  · obtain ⟨C₀⟩ := hk₀
    have hsurj : Function.Surjective C₀ := by
      have : ((Nat.find hex : ℕ) : ℕ∞) ≤ G.chromaticNumber :=
        SimpleGraph.le_chromaticNumber_iff_colorable.2 fun m hm => Nat.find_min' hex hm
      exact SimpleGraph.le_chromaticNumber_iff_forall_surjective.1 this C₀
    obtain ⟨C, hC⟩ := choosable_of_surjective G a ℓ hℓ hadj _ hpos C₀ hsurj S hS
    exact ⟨C, fun v => hSL v (hC v)⟩

end OMA.P456166
end Main

theorem OMA.solution : type_of% @OMA.S_mo_456166.main := @OMA.P456166.main_proof
