import OMAReductions.R_wp_nagata_s_conjecture_on_curves_R1_H3_R1
import Mathlib
-- Adapted from OpenAI openai/math 3344da59991ed94f9ba711217b29c1d760badfa6.
section
namespace OAI
section
noncomputable section
open scoped BigOperators
open Polynomial
namespace Nagata.W01.RowLagrange
variable {F : Type*} [Field F]
local instance : DecidableEq F := Classical.decEq F
theorem product_natDegree_le {ι : Type*} (s : Finset ι) (K : ι → F) :
    (∏ i ∈ s, (X - C (K i))).natDegree ≤ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    exact Polynomial.natDegree_mul_le.trans (by
      simpa only [Polynomial.natDegree_X_sub_C, Nat.add_comm] using Nat.add_le_add_right ih 1)
def basis (s : Finset F) (x : F) : F[X] :=
  C ((∏ y ∈ s.erase x, (x-y))⁻¹) * ∏ y ∈ s.erase x, (X - C y)
theorem basis_eval_self (s : Finset F) (x : F) : (basis s x).eval x = 1 := by
  classical
  have h : ∏ y ∈ s.erase x, (x-y) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro y hy
    exact sub_ne_zero.mpr (Finset.mem_erase.mp hy).1.symm
  simp only [basis, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  exact inv_mul_cancel₀ h
theorem basis_eval_other (s : Finset F) {x y : F} (hxy : x ≠ y) (hy : y ∈ s) :
    (basis s x).eval y = 0 := by
  classical
  simp only [basis, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  have h : ∏ z ∈ s.erase x, (y-z) = 0 :=
    Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hxy.symm, hy⟩) (sub_self _)
  rw [h, mul_zero]
theorem basis_natDegree_le (s : Finset F) (x : F) :
    (basis s x).natDegree ≤ (s.erase x).card :=
  (Polynomial.natDegree_C_mul_le _ _).trans (product_natDegree_le _ id)
def interpolate (s : Finset F) (v : F → F) : F[X] :=
  ∑ x ∈ s, C (v x) * basis s x
theorem interpolate_eval (s : Finset F) (v : F → F) {x : F} (hx : x ∈ s) :
    (interpolate s v).eval x = v x := by
  classical
  simp only [interpolate, eval_finsetSum, eval_mul, eval_C]
  rw [Finset.sum_eq_single x]
  · rw [basis_eval_self, mul_one]
  · intro y hy hyx
    rw [basis_eval_other s hyx hx, mul_zero]
  · intro h
    exact False.elim (h hx)
theorem interpolate_degree_lt (s : Finset F) (v : F → F) :
    (interpolate s v).degree < s.card := by
  classical
  apply lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
  rw [Nat.cast_withBot]
  apply (Finset.sup_lt_iff (WithBot.bot_lt_coe s.card)).2
  intro x hx
  have hdeg : (C (v x) * basis s x).natDegree ≤ s.card - 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans (by
      simpa [Finset.card_erase_of_mem hx] using basis_natDegree_le s x)
  apply lt_of_le_of_lt (Polynomial.degree_le_natDegree)
  exact WithBot.coe_lt_coe.mpr
    (lt_of_le_of_lt hdeg (Nat.sub_lt (Finset.card_pos.mpr ⟨x,hx⟩) (by decide : 0<1)))
end Nagata.W01.RowLagrange
end
end
section
noncomputable section
open scoped BigOperators
open Polynomial
namespace Nagata.W01
abbrev Plane := ℂ × ℂ
def monomial (b l : ℕ) : Plane → ℂ := fun z => z.1 ^ b * z.2 ^ l
def monomialSpace (q m : ℕ) : Submodule ℂ (Plane → ℂ) :=
  Submodule.span ℂ {f | ∃ b < m, ∃ l < q * (m - b), f = monomial b l}
theorem monomial_mem {q m b l : ℕ} (hb : b < m) (hl : l < q * (m-b)) :
    monomial b l ∈ monomialSpace q m :=
  Submodule.subset_span ⟨b, hb, l, hl, rfl⟩
theorem separable_mem {q m : ℕ} (p Q : ℂ[X])
    (h : ∀ b ∈ p.support, ∀ l ∈ Q.support, b < m ∧ l < q * (m-b)) :
    (fun z : Plane => p.eval z.1 * Q.eval z.2) ∈ monomialSpace q m := by
  have heq : (fun z : Plane => p.eval z.1 * Q.eval z.2) =
      ∑ b ∈ p.support, ∑ l ∈ Q.support,
        (p.coeff b * Q.coeff l) • monomial b l := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, monomial,
      Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [heq]
  apply Submodule.sum_mem
  intro b hb
  apply Submodule.sum_mem
  intro l hl
  exact Submodule.smul_mem _ _ (monomial_mem (h b hb l hl).1 (h b hb l hl).2)
def rowPrefix (K : ℕ → ℂ) (n : ℕ) : ℂ[X] :=
  ∏ i ∈ Finset.range n, (X - C (K i))
theorem rowPrefix_eval (K : ℕ → ℂ) (n : ℕ) (y : ℂ) :
    (rowPrefix K n).eval y = ∏ i ∈ Finset.range n, (y - K i) := by
  simp [rowPrefix, Polynomial.eval_prod]
theorem rowPrefix_eval_earlier (K : ℕ → ℂ) {i n : ℕ} (hi : i < n) :
    (rowPrefix K n).eval (K i) = 0 := by
  rw [rowPrefix_eval]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hi) (sub_self _)
theorem rowPrefix_eval_ne_zero (K : ℕ → ℂ) (n : ℕ)
    (hK : ∀ i < n, K n ≠ K i) : (rowPrefix K n).eval (K n) ≠ 0 := by
  rw [rowPrefix_eval]
  exact Finset.prod_ne_zero_iff.mpr fun i hi => sub_ne_zero.mpr (hK i (Finset.mem_range.mp hi))
theorem rowPrefix_natDegree_le (K : ℕ → ℂ) (n : ℕ) :
    (rowPrefix K n).natDegree ≤ n := by
  simpa [rowPrefix] using RowLagrange.product_natDegree_le (Finset.range n) K
theorem exists_row_polynomial (xs : Finset ℂ) (v : ℂ → ℂ) :
    ∃ p : ℂ[X], p.degree < xs.card ∧ ∀ x ∈ xs, p.eval x = v x := by
  exact ⟨RowLagrange.interpolate xs v, RowLagrange.interpolate_degree_lt xs v,
    fun x hx => RowLagrange.interpolate_eval xs v hx⟩
theorem correction_mem {q m n : ℕ} (K : ℕ → ℂ) (xs : Finset ℂ) (p : ℂ[X])
    (hp : p.degree < xs.card) (hcard : xs.card ≤ m)
    (horder : n + 1 ≤ q * (m - xs.card + 1)) :
    (fun z : Plane => p.eval z.1 * (rowPrefix K n).eval z.2) ∈ monomialSpace q m := by
  apply separable_mem
  intro b hb l hl
  have hbcard : b < xs.card := by
    exact WithBot.coe_lt_coe.mp
      (lt_of_le_of_lt (Polynomial.le_degree_of_mem_supp b hb) hp)
  have hlbound : l ≤ n :=
    (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hl)).trans
      (rowPrefix_natDegree_le K n)
  have hsub : m - xs.card + 1 ≤ m - b := by omega
  constructor
  · omega
  · exact lt_of_lt_of_le (by omega : l < q * (m - xs.card + 1))
      (Nat.mul_le_mul_left q hsub)
theorem interpolate_ordered_rows (q m s : ℕ) (K : ℕ → ℂ) (xs : ℕ → Finset ℂ)
    (hK : ∀ i < s, ∀ j < s, K i = K j → i = j)
    (hcard : ∀ i < s, (xs i).card ≤ m)
    (horder : ∀ i < s, i + 1 ≤ q * (m - (xs i).card + 1))
    (v : Plane → ℂ) :
    ∃ f ∈ monomialSpace q m, ∀ i < s, ∀ x ∈ xs i, f (x, K i) = v (x, K i) := by
  have step : ∀ n ≤ s, ∃ f ∈ monomialSpace q m,
      ∀ i < n, ∀ x ∈ xs i, f (x, K i) = v (x, K i) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      intro i hi
      omega
    | succ n ih =>
      intro hn
      obtain ⟨f, hf, hfv⟩ := ih (by omega)
      have hns : n < s := by omega
      have hQ : (rowPrefix K n).eval (K n) ≠ 0 := by
        apply rowPrefix_eval_ne_zero
        intro i hi heq
        have := hK n hns i (by omega) heq
        omega
      obtain ⟨p, hp, hpv⟩ := exists_row_polynomial (xs n)
        (fun x => (v (x, K n) - f (x, K n)) / (rowPrefix K n).eval (K n))
      let c : Plane → ℂ := fun z => p.eval z.1 * (rowPrefix K n).eval z.2
      refine ⟨f + c, Submodule.add_mem _ hf
        (correction_mem K (xs n) p hp (hcard n hns) (horder n hns)), ?_⟩
      intro i hi x hx
      by_cases hin : i = n
      · subst i
        change f (x, K n) + p.eval x * (rowPrefix K n).eval (K n) = v (x, K n)
        rw [hpv x hx, div_mul_cancel₀ _ hQ]
        ring
      · have hil : i < n := by omega
        change f (x, K i) + p.eval x * (rowPrefix K n).eval (K i) = v (x, K i)
        rw [rowPrefix_eval_earlier K hil, mul_zero, add_zero, hfv i hil x hx]
  exact step s le_rfl
theorem interpolate_fin_rows (q m s : ℕ) (K : Fin s → ℂ)
    (xs : Fin s → Finset ℂ) (hK : Function.Injective K)
    (hcard : ∀ i, (xs i).card ≤ m)
    (horder : ∀ i, i.val + 1 ≤ q * (m - (xs i).card + 1))
    (v : Plane → ℂ) :
    ∃ f ∈ monomialSpace q m, ∀ i, ∀ x ∈ xs i, f (x, K i) = v (x, K i) := by
  let K' : ℕ → ℂ := fun i => if h : i < s then K ⟨i, h⟩ else 0
  let xs' : ℕ → Finset ℂ := fun i => if h : i < s then xs ⟨i, h⟩ else ∅
  have hK' : ∀ i < s, ∀ j < s, K' i = K' j → i = j := by
    intro i hi j hj heq
    have h := hK (by simpa [K', hi, hj] using heq)
    exact congrArg Fin.val h
  have hcard' : ∀ i < s, (xs' i).card ≤ m := by
    intro i hi
    simpa [xs', hi] using hcard ⟨i, hi⟩
  have horder' : ∀ i < s, i + 1 ≤ q * (m - (xs' i).card + 1) := by
    intro i hi
    simpa [xs', hi] using horder ⟨i, hi⟩
  obtain ⟨f, hf, hv⟩ := interpolate_ordered_rows q m s K' xs' hK' hcard' horder' v
  refine ⟨f, hf, ?_⟩
  intro i x hx
  have hx' : x ∈ xs' i.val := by simpa [xs', i.isLt] using hx
  simpa [K', i.isLt] using hv i.val i.isLt x hx'
def planeEval (p : MvPolynomial (Fin 2) ℂ) : Plane → ℂ :=
  fun z => MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z.1 else z.2) p
def polynomialSpace (q m : ℕ) : Submodule ℂ (MvPolynomial (Fin 2) ℂ) :=
  Submodule.span ℂ {p | ∃ b < m, ∃ l < q * (m - b),
    p = MvPolynomial.X 0 ^ b * MvPolynomial.X 1 ^ l}
theorem exists_polynomialSpace_of_mem {q m : ℕ} {f : Plane → ℂ}
    (hf : f ∈ monomialSpace q m) :
    ∃ p ∈ polynomialSpace q m, planeEval p = f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨b, hb, l, hl, rfl⟩ := hf
    refine ⟨MvPolynomial.X 0 ^ b * MvPolynomial.X 1 ^ l,
      Submodule.subset_span ⟨b, hb, l, hl, rfl⟩, ?_⟩
    funext z
    simp [planeEval, monomial]
  | zero =>
    exact ⟨0, Submodule.zero_mem _, by funext z; simp [planeEval]⟩
  | add f g hf hg ihf ihg =>
    obtain ⟨p, hp, rfl⟩ := ihf
    obtain ⟨Q, hQ, rfl⟩ := ihg
    exact ⟨p + Q, Submodule.add_mem _ hp hQ, by funext z; simp [planeEval]⟩
  | smul a f hf ih =>
    obtain ⟨p, hp, rfl⟩ := ih
    exact ⟨a • p, Submodule.smul_mem _ a hp, by funext z; simp [planeEval]⟩
end Nagata.W01
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.ExponentEnclosure
noncomputable def positivePart (x : ℝ) : ℝ := max x 0
def exponentPolygon (ρ a Δ X Y : ℝ) : Prop :=
  0 ≤ X ∧ X ≤ 1 + ρ / 9 ∧
    -a * X + Δ * positivePart (X - 1) ≤ Y ∧
    Y ≤ -a * X + ρ + (Δ - 9) * positivePart (X - 1)
def enclosingPolygon (a lam X Y : ℝ) : Prop :=
  0 ≤ X ∧ -a * X ≤ Y ∧
    Y ≤ -a * X + lam * a - 9 * positivePart (X - lam)
lemma positivePart_of_nonpos {x : ℝ} (h : x ≤ 0) : positivePart x = 0 :=
  max_eq_right h
lemma positivePart_of_nonneg {x : ℝ} (h : 0 ≤ x) : positivePart x = x :=
  max_eq_left h
theorem polygon_containment {ρ a Δ lam X Y : ℝ}
    (hρ : 0 ≤ ρ) (hΔ : 0 ≤ Δ) (hlam : lam ≤ 1)
    (hslack : ρ + Δ * ρ / 9 < lam * a - 9 * (1 - lam))
    (h : exponentPolygon ρ a Δ X Y) : enclosingPolygon a lam X Y := by
  rcases h with ⟨hX, hXtop, hYlo, hYhi⟩
  refine ⟨hX, ?_, ?_⟩
  · have hp : 0 ≤ positivePart (X - 1) := le_max_right _ _
    have hprod := mul_nonneg hΔ hp
    linarith
  · by_cases hXone : X ≤ 1
    · rw [positivePart_of_nonpos (by linarith : X - 1 ≤ 0)] at hYhi
      have hmax : positivePart (X - lam) ≤ 1 - lam := by
        exact max_le (by linarith) (by linarith)
      have hprod := mul_nonneg hΔ hρ
      nlinarith
    · have hXone' : 1 ≤ X := le_of_lt (lt_of_not_ge hXone)
      rw [positivePart_of_nonneg (by linarith : 0 ≤ X - 1)] at hYhi
      rw [positivePart_of_nonneg (by linarith : 0 ≤ X - lam)]
      have hscaled : Δ * (X - 1) ≤ Δ * (ρ / 9) :=
        mul_le_mul_of_nonneg_left (by linarith) hΔ
      nlinarith
theorem degree_zero_tip {ρ a Δ : ℝ} (hρ : 0 ≤ ρ) :
    exponentPolygon ρ a Δ (1 + ρ / 9) (-a - ρ / 9 * (a - Δ)) := by
  unfold exponentPolygon
  rw [positivePart_of_nonneg (by linarith : 0 ≤ 1 + ρ / 9 - 1)]
  constructor
  · linarith
  constructor
  · exact le_rfl
  constructor <;> nlinarith
theorem first_interval_normalized {ρ a Δ m j K U : ℝ}
    (hm : 0 < m) (hρ : 0 ≤ ρ) (hj : 0 ≤ j) (hjm : j ≤ m)
    (hlo : U - a * j < K) (hhi : K < U - a * j + m * ρ) :
    exponentPolygon ρ a Δ (j / m) ((K - U) / m) := by
  have hdiv : j / m ≤ 1 := (div_le_one hm).mpr hjm
  unfold exponentPolygon
  rw [positivePart_of_nonpos (by linarith : j / m - 1 ≤ 0)]
  refine ⟨div_nonneg hj hm.le, by linarith, ?_, ?_⟩
  · simp only [mul_zero, add_zero]
    apply (le_div_iff₀ hm).mpr
    have heq : -a * (j / m) * m = -a * j := by field_simp [ne_of_gt hm]
    rw [heq]
    linarith
  · simp only [mul_zero, add_zero]
    apply (div_le_iff₀ hm).mpr
    have heq : (-a * (j / m) + ρ) * m = -a * j + m * ρ := by
      field_simp [ne_of_gt hm]
    rw [heq]
    linarith
theorem second_interval_normalized {ρ a Δ m j K U : ℝ}
    (hm : 0 < m) (hjm : m ≤ j) (hjtop : j ≤ m * (1 + ρ / 9))
    (hlo : U - a * j + Δ * (j - m) ≤ K)
    (hhi : K ≤ U - a * j + m * ρ + (Δ - 9) * (j - m)) :
    exponentPolygon ρ a Δ (j / m) ((K - U) / m) := by
  have hdiv : 1 ≤ j / m := (one_le_div hm).mpr hjm
  unfold exponentPolygon
  rw [positivePart_of_nonneg (by linarith : 0 ≤ j / m - 1)]
  refine ⟨by linarith, (div_le_iff₀ hm).mpr (by nlinarith), ?_, ?_⟩
  · apply (le_div_iff₀ hm).mpr
    have heq : (-a * (j / m) + Δ * (j / m - 1)) * m =
        -a * j + Δ * (j - m) := by field_simp [ne_of_gt hm]
    rw [heq]
    linarith
  · apply (div_le_iff₀ hm).mpr
    have heq : (-a * (j / m) + ρ + (Δ - 9) * (j / m - 1)) * m =
        -a * j + m * ρ + (Δ - 9) * (j - m) := by field_simp [ne_of_gt hm]
    rw [heq]
    linarith
theorem second_lower_endpoint (a Δ m j h : ℝ) :
    (h - 9 * (j - m)) / 9 * (a - Δ) - (h / 9 * (a - Δ) + m * a) =
      -a * j + Δ * (j - m) := by ring
theorem second_upper_endpoint (a Δ m j h : ℝ) :
    (h - 9 * (j - m)) / 9 * (a - Δ) + (h - 9 * (j - m)) -
        (h / 9 * (a - Δ) + m * a) =
      -a * j + h + (Δ - 9) * (j - m) := by ring
def rawExponent (d m h a Δ j K : ℝ) : Prop :=
  (0 ≤ j ∧ j ≤ m ∧
    h / 9 * (a - Δ) + (m - j) * a < K ∧
    K < h / 9 * (a - Δ) + (m - j) * a + h) ∨
  (m < j ∧ j ≤ d / 3 ∧ 0 < d - 3 * j ∧
    (h - 9 * (j - m)) / 9 * (a - Δ) < K ∧
    K < (h - 9 * (j - m)) / 9 * (a - Δ) + (h - 9 * (j - m))) ∨
  (m < j ∧ j ≤ d / 3 ∧ d - 3 * j = 0 ∧ K = 0)
theorem rawExponent_normalized {d m h ρ a Δ j K : ℝ}
    (hm : 0 < m) (hρ : 0 ≤ ρ) (hdegree : h = 3 * (d - 3 * m))
    (hratio : h = m * ρ) (hmem : rawExponent d m h a Δ j K) :
    exponentPolygon ρ a Δ (j / m)
      ((K - (h / 9 * (a - Δ) + m * a)) / m) := by
  rcases hmem with hfirst | hsecond | htip
  · rcases hfirst with ⟨hj, hjm, hlo, hhi⟩
    apply first_interval_normalized hm hρ hj hjm
    · nlinarith [hlo]
    · nlinarith [hhi]
  · rcases hsecond with ⟨hjm, hjtop, _, hlo, hhi⟩
    apply second_interval_normalized hm hjm.le
    · nlinarith
    · have hid := second_lower_endpoint a Δ m j h
      linarith
    · have hid := second_upper_endpoint a Δ m j h
      nlinarith
  · rcases htip with ⟨_, _, hzero, hK⟩
    have hj : j / m = 1 + ρ / 9 := by
      apply (div_eq_iff (ne_of_gt hm)).mpr
      nlinarith
    have hY : (K - (h / 9 * (a - Δ) + m * a)) / m =
        -a - ρ / 9 * (a - Δ) := by
      apply (div_eq_iff (ne_of_gt hm)).mpr
      rw [hK, hratio]
      ring
    rw [hj, hY]
    exact degree_zero_tip hρ
theorem integer_exponent_enclosure {d m h ρ a Δ lam : ℝ} {j K : ℤ}
    (hm : 0 < m) (hρ : 0 ≤ ρ) (hΔ : 0 ≤ Δ) (hlam : lam ≤ 1)
    (hdegree : h = 3 * (d - 3 * m)) (hratio : h = m * ρ)
    (hslack : ρ + Δ * ρ / 9 < lam * a - 9 * (1 - lam))
    (hmem : rawExponent d m h a Δ (j : ℝ) (K : ℝ)) :
    enclosingPolygon a lam ((j : ℝ) / m)
      (((K : ℝ) - (h / 9 * (a - Δ) + m * a)) / m) :=
  polygon_containment hρ hΔ hlam hslack
    (rawExponent_normalized hm hρ hdegree hratio hmem)
end Nagata.ExponentEnclosure
end
section
noncomputable section
namespace Nagata.W04
def InPolygon (a lam x y : ℝ) : Prop :=
  0 ≤ x ∧ -a * x ≤ y ∧ y ≤ -a * x + lam * a - 9 * max (x - lam) 0
theorem polygon_dilation (a lam scale x y : ℝ) (hscale : 0 < scale) :
    InPolygon a (scale * lam) (scale * x) (scale * y) ↔ InPolygon a lam x y := by
  have hmax : max (scale * x - scale * lam) 0 = scale * max (x - lam) 0 := by
    rw [mul_max_of_nonneg _ _ (le_of_lt hscale)]
    congr 1 <;> ring
  unfold InPolygon
  rw [hmax]
  have hlo : -a * (scale * x) = scale * (-a * x) := by ring
  have hup : -a * (scale * x) + (scale * lam) * a - 9 * (scale * max (x - lam) 0) =
      scale * (-a * x + lam * a - 9 * max (x - lam) 0) := by ring
  rw [hup, hlo]
  simp only [mul_nonneg_iff_of_pos_left hscale, mul_le_mul_iff_right₀ hscale]
theorem polygon_scaling (a lam x y : ℝ) (hlam : 0 < lam) :
    InPolygon a lam (lam * x) (lam * y) ↔ InPolygon a 1 x y := by
  simpa using polygon_dilation a 1 lam x y hlam
private theorem le_one_sub_div_iff (a x y : ℝ) (ha : 0 < a) :
    x ≤ 1 - y / a ↔ a * x ≤ a - y := by
  have h : x ≤ 1 - y / a ↔ y / a ≤ 1 - x := by constructor <;> intro h <;> linarith
  rw [h, div_le_iff₀ ha]
  constructor <;> intro h <;> nlinarith
theorem positive_slice (a x y : ℝ) (ha : 0 < a) (hy : 0 ≤ y) :
    InPolygon a 1 x y ↔ 0 ≤ x ∧ x ≤ 1 - y / a := by
  rw [le_one_sub_div_iff a x y ha]
  constructor
  · rintro ⟨hx, hlo, hup⟩
    refine ⟨hx, ?_⟩
    have hm := le_max_right (x - 1) (0 : ℝ)
    nlinarith
  · rintro ⟨hx, hup⟩
    have hx1 : x ≤ 1 := by nlinarith
    unfold InPolygon
    rw [max_eq_right (by linarith : x - 1 ≤ 0)]
    refine ⟨hx, ?_, ?_⟩
    · have hax : 0 ≤ a * x := mul_nonneg (le_of_lt ha) hx
      nlinarith
    · nlinarith
theorem negative_slice (a x y : ℝ) (ha : 0 < a) (hy : y ≤ 0) :
    InPolygon a 1 x y ↔ -y / a ≤ x ∧ x ≤ 1 - y / (a + 9) := by
  have ha9 : 0 < a + 9 := by linarith
  rw [div_le_iff₀ ha, le_one_sub_div_iff (a + 9) x y ha9]
  constructor
  · rintro ⟨hx, hlo, hup⟩
    refine ⟨by nlinarith, ?_⟩
    have hm := le_max_left (x - 1) (0 : ℝ)
    nlinarith
  · rintro ⟨hlo, hup⟩
    have hx : 0 ≤ x := by nlinarith
    refine ⟨hx, by nlinarith, ?_⟩
    by_cases hx1 : x ≤ 1
    · rw [max_eq_right (by linarith : x - 1 ≤ 0)]
      have hax : a * x ≤ a := by nlinarith
      nlinarith
    · rw [max_eq_left (by linarith : 0 ≤ x - 1)]
      nlinarith
theorem negative_width_identity (a y : ℝ) (ha : 0 < a) :
    (1 - y / (a + 9)) - (-y / a) = 1 + y / (a * (1 + a / 9)) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have ha90 : a + 9 ≠ 0 := ne_of_gt (by linarith)
  have ht : 1 + a / 9 ≠ 0 := ne_of_gt (by
    have h := div_pos ha (show (0 : ℝ) < 9 by norm_num)
    linarith)
  field_simp
  ring
def UnitSliceWidth (a y : ℝ) : ℝ :=
  if 0 ≤ y then 1 - y / a else 1 + y / (a * (1 + a / 9))
def SliceLower (a y : ℝ) : ℝ := if 0 ≤ y then 0 else -y / a
def SliceUpper (a y : ℝ) : ℝ :=
  if 0 ≤ y then 1 - y / a else 1 - y / (a + 9)
theorem unit_slice_width (a y : ℝ) (ha : 0 < a) :
    SliceUpper a y - SliceLower a y = UnitSliceWidth a y := by
  by_cases hy : 0 ≤ y
  · simp [SliceUpper, SliceLower, UnitSliceWidth, hy]
  · simp only [SliceUpper, SliceLower, UnitSliceWidth, if_neg hy]
    exact negative_width_identity a y ha
theorem unit_slice_interval (a x y : ℝ) (ha : 0 < a) :
    InPolygon a 1 x y ↔ SliceLower a y ≤ x ∧ x ≤ SliceUpper a y := by
  by_cases hy : 0 ≤ y
  · simp only [SliceLower, SliceUpper, if_pos hy]
    exact positive_slice a x y ha hy
  · simp only [SliceLower, SliceUpper, if_neg hy]
    exact negative_slice a x y ha (le_of_lt (lt_of_not_ge hy))
theorem unit_slice_nonempty (a y : ℝ) (ha : 0 < a) :
    (∃ x, InPolygon a 1 x y) ↔ 0 ≤ UnitSliceWidth a y := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨hl, hu⟩ := (unit_slice_interval a x y ha).mp hx
    rw [← unit_slice_width a y ha]
    linarith
  · intro h
    refine ⟨SliceLower a y, (unit_slice_interval a _ y ha).mpr ⟨le_rfl, ?_⟩⟩
    rw [← unit_slice_width a y ha] at h
    linarith
theorem unit_width_le_one (a y : ℝ) (ha : 0 < a) : UnitSliceWidth a y ≤ 1 := by
  unfold UnitSliceWidth
  split_ifs with hy
  · have h := div_nonneg hy (le_of_lt ha)
    linarith
  · have hA : 0 ≤ a * (1 + a / 9) := mul_nonneg (le_of_lt ha) (by
      have h := div_pos ha (show (0 : ℝ) < 9 by norm_num)
      linarith)
    have h := div_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge hy)) hA
    linarith
theorem unit_width_threshold (a y s : ℝ) (ha : 0 < a)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    s ≤ UnitSliceWidth a y ↔
      -a * (1 + a / 9) * (1 - s) ≤ y ∧ y ≤ a * (1 - s) := by
  have hA : 0 < a * (1 + a / 9) := mul_pos ha (by
    have h := div_pos ha (show (0 : ℝ) < 9 by norm_num)
    linarith)
  have htop : 0 ≤ a * (1 - s) := by
    have hsabs : |s| ≤ 1 := (abs_of_nonneg hs).symm ▸ hs1
    exact mul_nonneg ha.le (sub_nonneg.mpr (le_abs_self s |>.trans hsabs))
  have hbot : -a * (1 + a / 9) * (1 - s) ≤ 0 := by
    nlinarith [mul_nonneg (le_of_lt hA) (show 0 ≤ 1 - s by linarith)]
  unfold UnitSliceWidth
  split_ifs with hy
  · rw [le_one_sub_div_iff a s y ha]
    constructor <;> intro h
    · exact ⟨le_trans hbot hy, by nlinarith⟩
    · nlinarith [h.2]
  · have hy0 : y ≤ 0 := le_of_lt (lt_of_not_ge hy)
    have hid : 1 + y / (a * (1 + a / 9)) =
        1 - (-y) / (a * (1 + a / 9)) := by ring
    rw [hid, le_one_sub_div_iff (a * (1 + a / 9)) s (-y) hA]
    constructor <;> intro h
    · exact ⟨by nlinarith, le_trans hy0 htop⟩
    · nlinarith [h.1]
def ScaledSliceWidth (a scale U y : ℝ) : ℝ :=
  scale * UnitSliceWidth a ((y - U) / scale)
theorem scaled_width_le_scale (a scale U y : ℝ) (ha : 0 < a) (hscale : 0 ≤ scale) :
    ScaledSliceWidth a scale U y ≤ scale := by
  unfold ScaledSliceWidth
  simpa using mul_le_mul_of_nonneg_left (unit_width_le_one a ((y - U) / scale) ha) hscale
theorem scaled_slice_interval (a scale U x y : ℝ) (ha : 0 < a) (hscale : 0 < scale) :
    InPolygon a scale x (y - U) ↔
      scale * SliceLower a ((y - U) / scale) ≤ x ∧
      x ≤ scale * SliceUpper a ((y - U) / scale) := by
  have hp := polygon_scaling a scale (x / scale) ((y - U) / scale) hscale
  rw [mul_div_cancel₀ _ (ne_of_gt hscale), mul_div_cancel₀ _ (ne_of_gt hscale)] at hp
  rw [hp, unit_slice_interval a (x / scale) ((y - U) / scale) ha]
  rw [le_div_iff₀ hscale, div_le_iff₀ hscale]
  constructor <;> intro h <;> constructor <;> nlinarith [h.1, h.2]
theorem scaled_slice_width (a scale U y : ℝ) (ha : 0 < a) :
    scale * SliceUpper a ((y - U) / scale) -
      scale * SliceLower a ((y - U) / scale) = ScaledSliceWidth a scale U y := by
  rw [← mul_sub, unit_slice_width a ((y - U) / scale) ha]
  rfl
theorem scaled_width_threshold (a scale U y s : ℝ)
    (ha : 0 < a) (hscale : 0 < scale) (hs : 0 ≤ s) (hsupper : s ≤ scale) :
    s ≤ ScaledSliceWidth a scale U y ↔
      U - a * (1 + a / 9) * (scale - s) ≤ y ∧
      y ≤ U + a * (scale - s) := by
  have hsunit : s / scale ≤ 1 := by
    rw [div_le_iff₀ hscale]
    simpa using hsupper
  unfold ScaledSliceWidth
  have hw : s ≤ scale * UnitSliceWidth a ((y - U) / scale) ↔
      s / scale ≤ UnitSliceWidth a ((y - U) / scale) := by
    rw [div_le_iff₀ hscale]
    rw [mul_comm]
  rw [hw, unit_width_threshold a ((y - U) / scale) (s / scale) ha
    (div_nonneg hs (le_of_lt hscale)) hsunit]
  rw [le_div_iff₀ hscale, div_le_iff₀ hscale]
  have hid (c : ℝ) : c * (1 - s / scale) * scale = c * (scale - s) := by
    field_simp
  rw [hid, hid]
  constructor <;> intro h <;> constructor <;> nlinarith [h.1, h.2]
end Nagata.W04
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W02
theorem card_le_max_sub_min_add_one (s : Finset ℤ) (hs : s.Nonempty) :
    (s.card : ℤ) ≤ s.max' hs - s.min' hs + 1 := by
  have hsub : s ⊆ Finset.Icc (s.min' hs) (s.max' hs) := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨s.min'_le x hx, s.le_max' x hx⟩
  have hc := Finset.card_le_card hsub
  have hm := s.min'_le_max' hs
  have hi := Int.card_Icc_of_le (s.min' hs) (s.max' hs) (show s.min' hs ≤ s.max' hs + 1 by omega)
  have hcast : (s.card : ℤ) ≤ (Finset.card (Finset.Icc (s.min' hs) (s.max' hs)) : ℤ) := by
    exact_mod_cast hc
  omega
theorem card_le_interval_length_add_one (s : Finset ℤ) (a b : ℝ)
    (hab : a ≤ b) (h : ∀ k ∈ s, a ≤ (k : ℝ) ∧ (k : ℝ) ≤ b) :
    (s.card : ℝ) ≤ b - a + 1 := by
  by_cases hs : s.Nonempty
  · have hc := card_le_max_sub_min_add_one s hs
    have hcR : (s.card : ℝ) ≤ (s.max' hs : ℝ) - (s.min' hs : ℝ) + 1 := by
      exact_mod_cast hc
    have hmin := (h _ (s.min'_mem hs)).1
    have hmax := (h _ (s.max'_mem hs)).2
    linarith
  · have hz : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp only [hz, Finset.card_empty, Nat.cast_zero]
    linarith
theorem card_le_of_interval_length_lt (s : Finset ℤ) (a b : ℝ) (m : ℕ)
    (hab : a ≤ b) (h : ∀ k ∈ s, a ≤ (k : ℝ) ∧ (k : ℝ) ≤ b)
    (hlen : b - a < (m : ℝ)) : s.card ≤ m := by
  have hc := card_le_interval_length_add_one s a b hab h
  have hh : (s.card : ℝ) < ((m + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hn : s.card < m + 1 := by exact_mod_cast hh
  omega
theorem sub_one_le_interval_length (s : Finset ℤ) (a b : ℝ) (t : ℕ)
    (hab : a ≤ b) (h : ∀ k ∈ s, a ≤ (k : ℝ) ∧ (k : ℝ) ≤ b)
    (ht : t ≤ s.card) : (t : ℝ) - 1 ≤ b - a := by
  have hc := card_le_interval_length_add_one s a b hab h
  have htR : (t : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast ht
  linarith
end Nagata.W02
end
section
namespace Nagata.W09
noncomputable def thetaIndices (U : ℝ) (n : ℤ) : Finset ℤ :=
  Finset.Ioc ⌊U⌋ (⌊U⌋ + n)
theorem mem_thetaIndices_iff {U : ℝ} {n K : ℤ}
    (hU : U ∉ Set.range (Int.cast : ℤ → ℝ)) :
    K ∈ thetaIndices U n ↔ U < (K : ℝ) ∧ (K : ℝ) < U + (n : ℝ) := by
  rw [thetaIndices, Finset.mem_Ioc]
  constructor
  · rintro ⟨hK, hKn⟩
    refine ⟨Int.floor_lt.mp hK, ?_⟩
    have hfloor : (⌊U⌋ : ℝ) < U := Int.floor_lt_self_iff.mpr hU
    have hcast : (K : ℝ) ≤ (⌊U⌋ : ℝ) + (n : ℝ) := by
      simpa only [Int.cast_add] using
        (show (K : ℝ) ≤ ((⌊U⌋ + n : ℤ) : ℝ) from Int.cast_le.mpr hKn)
    linarith
  · rintro ⟨hK, hKn⟩
    refine ⟨Int.floor_lt.mpr hK, ?_⟩
    have hle : K ≤ ⌊U + (n : ℝ)⌋ := Int.le_floor.mpr hKn.le
    simpa only [Int.floor_add_intCast] using hle
theorem card_thetaIndices (U : ℝ) (n : ℤ) :
    (thetaIndices U n).card = n.toNat := by
  simp only [thetaIndices, Int.card_Ioc, add_sub_cancel_left]
end Nagata.W09
end
section
namespace Nagata.W09
theorem thetaIndices_residue_injective {U : ℝ} {n a b : ℤ}
    (ha : a ∈ thetaIndices U n) (hb : b ∈ thetaIndices U n)
    (hab : a % n = b % n) : a = b := by
  simp only [thetaIndices, Finset.mem_Ioc] at ha hb
  have ha0 : 0 ≤ a - (⌊U⌋ + 1) := by omega
  have han : a - (⌊U⌋ + 1) < n := by omega
  have hb0 : 0 ≤ b - (⌊U⌋ + 1) := by omega
  have hbn : b - (⌊U⌋ + 1) < n := by omega
  have h : (a - (⌊U⌋ + 1)) % n = (b - (⌊U⌋ + 1)) % n := by
    conv_lhs => rw [Int.sub_emod]
    conv_rhs => rw [Int.sub_emod]
    rw [hab]
  rw [Int.emod_eq_of_lt ha0 han, Int.emod_eq_of_lt hb0 hbn] at h
  omega
theorem exists_thetaIndex_modEq (U : ℝ) {n : ℤ} (hn : 0 < n) (z : ℤ) :
    ∃ K ∈ thetaIndices U n, K % n = z % n := by
  let a := ⌊U⌋ + 1
  refine ⟨a + (z - a) % n, ?_, ?_⟩
  · simp only [thetaIndices, Finset.mem_Ioc]
    have h0 := Int.emod_nonneg (z - a) (ne_of_gt hn)
    have hlt := Int.emod_lt_of_pos (z - a) hn
    dsimp [a] at *
    omega
  · have h : (a + (z - a) % n) % n = (a + (z - a)) % n := by
      simp only [Int.add_emod, Int.emod_emod]
    have hz : a + (z - a) = z := by omega
    rw [hz] at h
    exact h
end Nagata.W09
end
end OAI
end
section
namespace OAI
section
namespace Nagata.FiniteExponents
noncomputable def openIntegerInterval (U V : ℝ) : Finset ℤ :=
  Finset.Ioo ⌊U⌋ ⌈V⌉
@[simp] theorem mem_openIntegerInterval {U V : ℝ} {K : ℤ} :
    K ∈ openIntegerInterval U V ↔ U < (K : ℝ) ∧ (K : ℝ) < V := by
  simp only [openIntegerInterval, Finset.mem_Ioo, Int.floor_lt, Int.lt_ceil]
def commonDegree (d m : ℤ) : ℤ := 3 * (d - 3 * m)
def sourceDegree (d j : ℤ) : ℤ := 3 * (d - 3 * j)
noncomputable def firstLower (d m j : ℤ) (a Δ : ℝ) : ℝ :=
  (commonDegree d m : ℝ) / 9 * (a - Δ) + ((m : ℝ) - (j : ℝ)) * a
noncomputable def secondLower (d j : ℤ) (a Δ : ℝ) : ℝ :=
  (sourceDegree d j : ℝ) / 9 * (a - Δ)
def liftRow (j : ℤ) (s : Finset ℤ) : Finset (ℤ × ℤ) :=
  s.image (fun K => (j, K))
@[simp] theorem mem_liftRow {j j' K : ℤ} {s : Finset ℤ} :
    (j', K) ∈ liftRow j s ↔ j' = j ∧ K ∈ s := by
  constructor
  · intro h
    obtain ⟨L, hL, heq⟩ := Finset.mem_image.mp h
    have hj : j = j' := congrArg Prod.fst heq
    have hK : L = K := congrArg Prod.snd heq
    exact ⟨hj.symm, hK ▸ hL⟩
  · rintro ⟨rfl, hK⟩
    exact Finset.mem_image.mpr ⟨K, hK, rfl⟩
noncomputable def exponentSet (d m : ℤ) (a Δ : ℝ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc 0 m).biUnion fun j =>
    liftRow j (openIntegerInterval (firstLower d m j a Δ)
      (firstLower d m j a Δ + (commonDegree d m : ℝ)))) ∪
  ((Finset.Ioc m (d / 3)).biUnion fun j =>
    if 0 < d - 3 * j then
      liftRow j (openIntegerInterval (secondLower d j a Δ)
        (secondLower d j a Δ + (sourceDegree d j : ℝ)))
    else ∅) ∪
  (((Finset.Ioc m (d / 3)).filter fun j => d - 3 * j = 0).image fun j => (j, 0))
theorem mem_exponentSet_iff {d m j K : ℤ} {a Δ : ℝ} :
    (j, K) ∈ exponentSet d m a Δ ↔
      (0 ≤ j ∧ j ≤ m ∧ firstLower d m j a Δ < (K : ℝ) ∧
        (K : ℝ) < firstLower d m j a Δ + (commonDegree d m : ℝ)) ∨
      (m < j ∧ j ≤ d / 3 ∧ 0 < d - 3 * j ∧
        secondLower d j a Δ < (K : ℝ) ∧
        (K : ℝ) < secondLower d j a Δ + (sourceDegree d j : ℝ)) ∨
      (m < j ∧ j ≤ d / 3 ∧ d - 3 * j = 0 ∧ K = 0) := by
  classical
  simp only [exponentSet, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_Icc, Finset.mem_Ioc, mem_liftRow, mem_openIntegerInterval,
    Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ((⟨j', hj', hrow⟩ | ⟨j', hj', hrow⟩) | ⟨j', ⟨hj', hz⟩, heq⟩)
    · rcases hrow with ⟨rfl, hlo, hhi⟩
      exact Or.inl ⟨hj'.1, hj'.2, hlo, hhi⟩
    · split_ifs at hrow with hp
      · rw [mem_liftRow, mem_openIntegerInterval] at hrow
        rcases hrow with ⟨rfl, hlo, hhi⟩
        exact Or.inr (Or.inl ⟨hj'.1, hj'.2, hp, hlo, hhi⟩)
      · simp at hrow
    · cases heq
      exact Or.inr (Or.inr ⟨hj'.1, hj'.2, hz, rfl⟩)
  · rintro (hfirst | hsecond | hzero)
    · rcases hfirst with ⟨hj0, hjm, hlo, hhi⟩
      exact Or.inl (Or.inl ⟨j, ⟨hj0, hjm⟩, rfl, hlo, hhi⟩)
    · rcases hsecond with ⟨hjm, hjd, hp, hlo, hhi⟩
      refine Or.inl (Or.inr ⟨j, ⟨hjm, hjd⟩, ?_⟩)
      simp only [if_pos hp, mem_liftRow, mem_openIntegerInterval]
      exact ⟨True.intro, hlo, hhi⟩
    · rcases hzero with ⟨hjm, hjd, hz, rfl⟩
      exact Or.inr ⟨j, ⟨⟨hjm, hjd⟩, hz⟩, rfl⟩
theorem integer_degree_bound (d j : ℤ) :
    j ≤ d / 3 ↔ (j : ℝ) ≤ (d : ℝ) / 3 := by
  rw [Int.le_ediv_iff_mul_le (show (0 : ℤ) < 3 by decide)]
  constructor
  · intro h
    have hc : (j : ℝ) * 3 ≤ (d : ℝ) := by exact_mod_cast h
    linarith
  · intro h
    have hc : (j : ℝ) * 3 ≤ (d : ℝ) := by linarith
    exact_mod_cast hc
theorem mem_exponentSet_iff_raw {d m j K : ℤ} {a Δ : ℝ} :
    (j, K) ∈ exponentSet d m a Δ ↔
      Nagata.ExponentEnclosure.rawExponent (d : ℝ) (m : ℝ)
        (3 * ((d : ℝ) - 3 * (m : ℝ))) a Δ (j : ℝ) (K : ℝ) := by
  rw [mem_exponentSet_iff]
  unfold Nagata.ExponentEnclosure.rawExponent firstLower secondLower commonDegree sourceDegree
  have hn : (3 : ℝ) * ((d : ℝ) - 3 * (j : ℝ)) =
      3 * ((d : ℝ) - 3 * (m : ℝ)) - 9 * ((j : ℝ) - (m : ℝ)) := by ring
  have h0 : (0 : ℤ) ≤ j ↔ (0 : ℝ) ≤ (j : ℝ) := by norm_cast
  have hjm : j ≤ m ↔ (j : ℝ) ≤ (m : ℝ) := by norm_cast
  have hmj : m < j ↔ (m : ℝ) < (j : ℝ) := by norm_cast
  have hz : d - 3 * j = 0 ↔ (d : ℝ) - 3 * (j : ℝ) = 0 := by norm_cast
  have hp : 0 < d - 3 * j ↔ (0 : ℝ) < (d : ℝ) - 3 * (j : ℝ) := by norm_cast
  have hK : K = 0 ↔ (K : ℝ) = 0 := by norm_cast
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_ofNat, hn]
  simp only [h0, hjm, hmj, integer_degree_bound, hp, hz, hK]
theorem degree_zero_mem {d m j : ℤ} {a Δ : ℝ}
    (hjm : m < j) (hz : d - 3 * j = 0) :
    (j, 0) ∈ exponentSet d m a Δ := by
  apply mem_exponentSet_iff.mpr
  refine Or.inr (Or.inr ⟨hjm, ?_, hz, rfl⟩)
  apply (Int.le_ediv_iff_mul_le (show (0 : ℤ) < 3 by decide)).mpr
  linarith
theorem exponentSet_nonempty {d m : ℤ} {a Δ : ℝ}
    (hm : 0 ≤ m) (hd : 3 * m < d)
    (hU : firstLower d m 0 a Δ ∉ Set.range (Int.cast : ℤ → ℝ)) :
    (exponentSet d m a Δ).Nonempty := by
  have hh : 0 < commonDegree d m := by
    unfold commonDegree
    linarith
  let U := firstLower d m 0 a Δ
  let K : ℤ := ⌊U⌋ + 1
  have hfloor : (⌊U⌋ : ℝ) < U := Int.floor_lt_self_iff.mpr hU
  have hhreal : (1 : ℝ) ≤ (commonDegree d m : ℝ) := by exact_mod_cast hh
  have hlo : U < (K : ℝ) := by
    dsimp [K]
    simpa only [Int.cast_add, Int.cast_one] using Int.lt_floor_add_one U
  have hhi : (K : ℝ) < U + (commonDegree d m : ℝ) := by
    dsimp [K]
    push_cast
    linarith
  refine ⟨(0, K), mem_exponentSet_iff.mpr ?_⟩
  exact Or.inl ⟨le_rfl, hm, hlo, hhi⟩
noncomputable def Column (d m : ℤ) (a Δ : ℝ) :=
  {p : ℤ × ℤ // p ∈ exponentSet d m a Δ}
noncomputable instance columnFintype (d m : ℤ) (a Δ : ℝ) :
    Fintype (Column d m a Δ) := by
  unfold Column
  infer_instance
end Nagata.FiniteExponents
end
section
namespace Nagata.FiniteExponents
end Nagata.FiniteExponents
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Nagata.Workers.W10.LocalTupleSort
variable {n : ℕ}
variable {α : Type*} [LinearOrder α]
def graph (f : Fin n → α) : Finset (α ×ₗ Fin n) :=
  Finset.univ.image fun i => (f i, i)
def graph.proj {f : Fin n → α} : graph f → α := fun p => p.1.1
@[simp]
theorem graph.card (f : Fin n → α) : (graph f).card = n := by
  erw [graph, Finset.card_image_of_injective]
  · exact Finset.card_fin _
  · intro i j hij
    exact congrArg (fun p : α ×ₗ Fin n => p.2) hij
def graphEquiv₁ (f : Fin n → α) : Fin n ≃ graph f where
  toFun i := ⟨(f i, i), Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  invFun p := p.1.2
  left_inv i := by simp
  right_inv entry := by
    apply Subtype.ext
    obtain ⟨index, _, hindex⟩ := Finset.mem_image.mp entry.property
    change (f entry.val.2, entry.val.2) = entry.val
    rw [← hindex]
@[simp]
theorem proj_equiv₁' (f : Fin n → α) : graph.proj ∘ graphEquiv₁ f = f :=
  rfl
def graphEquiv₂ (f : Fin n → α) : Fin n ≃o graph f :=
  Finset.orderIsoOfFin _ (by simp)
def sort (f : Fin n → α) : Equiv.Perm (Fin n) :=
  (graphEquiv₂ f).toEquiv.trans (graphEquiv₁ f).symm
theorem self_comp_sort (f : Fin n → α) : f ∘ sort f = graph.proj ∘ graphEquiv₂ f :=
  show graph.proj ∘ (graphEquiv₁ f ∘ (graphEquiv₁ f).symm) ∘ (graphEquiv₂ f).toEquiv = _ by simp
theorem monotone_proj (f : Fin n → α) : Monotone (graph.proj : graph f → α) := by
  rintro ⟨⟨x, i⟩, hx⟩ ⟨⟨y, j⟩, hy⟩ (_ | h)
  · exact le_of_lt ‹_›
  · simp [graph.proj]
theorem monotone_sort (f : Fin n → α) : Monotone (f ∘ sort f) := by
  rw [self_comp_sort]
  exact (monotone_proj f).comp (graphEquiv₂ f).monotone
end Nagata.Workers.W10.LocalTupleSort
namespace Nagata.Workers.W10
section
theorem initial_rows_le_distribution (N : ℕ → ℕ) (s i : ℕ) (hi : i < s)
    (horder : ∀ j, j ≤ i → N i ≤ N j) :
    i + 1 ≤ ((Finset.range s).filter fun j => N i ≤ N j).card := by
  calc
    i + 1 = (Finset.range (i + 1)).card := (Finset.card_range _).symm
    _ ≤ ((Finset.range s).filter fun j => N i ≤ N j).card := by
      apply Finset.card_le_card
      intro j hj
      have hji : j ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (lt_of_le_of_lt hji hi), horder j hji⟩
theorem ordered_row_bound (N : ℕ → ℕ) (s q m : ℕ)
    (horder : ∀ i < s, ∀ j ≤ i, N i ≤ N j)
    (hpos : ∀ i < s, 1 ≤ N i)
    (hsize : ∀ i < s, N i ≤ m)
    (hdistribution : ∀ t, 1 ≤ t → t ≤ m →
      ((Finset.range s).filter fun j => t ≤ N j).card ≤ q * (m - t + 1))
    (i : ℕ) (hi : i < s) : i + 1 ≤ q * (m - N i + 1) :=
  (initial_rows_le_distribution N s i hi (horder i hi)).trans
    (hdistribution (N i) (hpos i hi) (hsize i hi))
theorem correction_exponent_bound (q m n i b ell : ℕ)
    (hsize : n ≤ m) (horder : i + 1 ≤ q * (m - n + 1))
    (hb : b < n) (hell : ell ≤ i) : b < m ∧ ell < q * (m - b) := by
  constructor
  · exact lt_of_lt_of_le hb hsize
  · have hsub : m - n + 1 ≤ m - b := by omega
    have hmul := Nat.mul_le_mul_left q hsub
    exact lt_of_le_of_lt hell (lt_of_lt_of_le (Nat.lt_of_succ_le horder) hmul)
theorem distributed_correction_exponent_bound (N : ℕ → ℕ) (s q m : ℕ)
    (horder : ∀ i < s, ∀ j ≤ i, N i ≤ N j)
    (hpos : ∀ i < s, 1 ≤ N i)
    (hsize : ∀ i < s, N i ≤ m)
    (hdistribution : ∀ t, 1 ≤ t → t ≤ m →
      ((Finset.range s).filter fun j => t ≤ N j).card ≤ q * (m - t + 1))
    (i b ell : ℕ) (hi : i < s) (hb : b < N i) (hell : ell ≤ i) :
    b < m ∧ ell < q * (m - b) :=
  correction_exponent_bound q m (N i) i b ell (hsize i hi)
    (ordered_row_bound N s q m horder hpos hsize hdistribution i hi) hb hell
theorem distribution_card_permutation {s : ℕ} (N : Fin s → ℕ)
    (σ : Equiv.Perm (Fin s)) (t : ℕ) :
    (Finset.univ.filter fun i => t ≤ N (σ i)).card =
      (Finset.univ.filter fun i => t ≤ N i).card := by
  apply Finset.card_equiv σ
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
theorem fin_ordered_row_bound {s : ℕ} (N : Fin s → ℕ) (q m : ℕ)
    (horder : Antitone N) (hpos : ∀ i, 1 ≤ N i) (hsize : ∀ i, N i ≤ m)
    (hdistribution : ∀ t, 1 ≤ t → t ≤ m →
      (Finset.univ.filter fun j => t ≤ N j).card ≤ q * (m - t + 1))
    (i : Fin s) : i.val + 1 ≤ q * (m - N i + 1) := by
  have hindex : i.val + 1 ≤ (Finset.univ.filter fun j => N i ≤ N j).card := by
    calc
      i.val + 1 = (Finset.Iic i).card := (Fin.card_Iic i).symm
      _ ≤ (Finset.univ.filter fun j => N i ≤ N j).card := by
        apply Finset.card_le_card
        intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, horder (Finset.mem_Iic.mp hj)⟩
  exact hindex.trans (hdistribution (N i) (hpos i) (hsize i))
open Nagata.FiniteExponents
def ColumnFiber (d m : ℤ) (a Δ : ℝ) (j : ℤ) :=
  {K : ℤ // (j, K) ∈ exponentSet d m a Δ}
instance columnFiberDecidableEq (d m : ℤ) (a Δ : ℝ) (j : ℤ) :
    DecidableEq (ColumnFiber d m a Δ j) := by
  unfold ColumnFiber
  infer_instance
instance columnFiberFintype (d m : ℤ) (a Δ : ℝ) (j : ℤ) :
    Fintype (ColumnFiber d m a Δ j) := by
  classical
  apply Fintype.ofInjective
    (fun K : ColumnFiber d m a Δ j => (⟨(j, K.val), K.property⟩ : Column d m a Δ))
  intro K L h
  apply Subtype.ext
  exact congrArg (fun c : Column d m a Δ => c.val.2) h
theorem column_first_bounds {d m : ℤ} {a Δ : ℝ} (hm : 0 ≤ m) (hd : 3 * m < d)
    (c : Column d m a Δ) : 0 ≤ c.val.1 ∧ c.val.1 ≤ d / 3 := by
  have hmd : m ≤ d / 3 :=
    (Int.le_ediv_iff_mul_le (show (0 : ℤ) < 3 by decide)).mpr (by omega)
  rcases mem_exponentSet_iff.mp c.property with h | h | h
  · exact ⟨h.1, h.2.1.trans hmd⟩
  · exact ⟨hm.trans h.1.le, h.2.1⟩
  · exact ⟨hm.trans h.1.le, h.2.1⟩
def columnFiberEquiv (d m : ℤ) (a Δ : ℝ) (hm : 0 ≤ m) (hd : 3 * m < d) :
    (Σ j : Fin ((d / 3).toNat + 1), ColumnFiber d m a Δ (j.val : ℤ)) ≃
      Column d m a Δ where
  toFun c := ⟨(c.1.val, c.2.val), c.2.property⟩
  invFun c :=
    ⟨⟨c.val.1.toNat, by
        have hb := column_first_bounds hm hd c
        have hnat := Int.toNat_le_toNat hb.2
        omega⟩,
      ⟨c.val.2, by
        have hb := column_first_bounds hm hd c
        simpa only [Int.toNat_of_nonneg hb.1] using c.property⟩⟩
  left_inv c := by
    rcases c with ⟨⟨j, hj⟩, ⟨K, hK⟩⟩
    rfl
  right_inv c := by
    apply Subtype.ext
    have hb := column_first_bounds hm hd c
    simp only [Int.toNat_of_nonneg hb.1, Prod.eta]
def zeroColumnFiberEquiv (d m j : ℤ) (a Δ : ℝ) (hj : m < j) (hz : d - 3 * j = 0) :
    ColumnFiber d m a Δ j ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := ⟨0, degree_zero_mem hj hz⟩
  left_inv K := by
    apply Subtype.ext
    rcases mem_exponentSet_iff.mp K.property with h | h | h
    · omega
    · omega
    · exact h.2.2.2.symm
  right_inv _ := rfl
def firstColumnFiberEquiv (d m j : ℤ) (a Δ : ℝ) (hj0 : 0 ≤ j) (hjm : j ≤ m)
    (hU : firstLower d m j a Δ ∉ Set.range (Int.cast : ℤ → ℝ)) :
    ColumnFiber d m a Δ j ≃ Nagata.W09.thetaIndices (firstLower d m j a Δ) (commonDegree d m) := by
  apply Equiv.subtypeEquivRight
  intro K
  rw [mem_exponentSet_iff, Nagata.W09.mem_thetaIndices_iff hU]
  constructor
  · rintro (h | h | h)
    · exact h.2.2
    · omega
    · omega
  · intro h
    exact Or.inl ⟨hj0, hjm, h⟩
def positiveColumnFiberEquiv (d m j : ℤ) (a Δ : ℝ) (hmj : m < j)
    (hjd : j ≤ d / 3) (hn : 0 < d - 3 * j)
    (hU : secondLower d j a Δ ∉ Set.range (Int.cast : ℤ → ℝ)) :
    ColumnFiber d m a Δ j ≃ Nagata.W09.thetaIndices (secondLower d j a Δ) (sourceDegree d j) := by
  apply Equiv.subtypeEquivRight
  intro K
  rw [mem_exponentSet_iff, Nagata.W09.mem_thetaIndices_iff hU]
  constructor
  · rintro (h | h | h)
    · omega
    · exact h.2.2.2
    · omega
  · intro h
    exact Or.inr (Or.inl ⟨hmj, hjd, hn, h⟩)
end
section
variable {α β : Type*}
def rowHeights (S : Finset (α × β)) : Finset β := by
  classical
  exact S.image Prod.snd
def rowXs (S : Finset (α × β)) (K : β) : Finset α := by
  classical
  exact (S.filter fun p => p.2 = K).image Prod.fst
theorem mem_rowXs {S : Finset (α × β)} {x : α} {K : β} :
    x ∈ rowXs S K ↔ (x, K) ∈ S := by
  classical
  constructor
  · intro hx
    obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hx
    obtain ⟨hp, hpk⟩ := Finset.mem_filter.mp hp
    have heq : p = (x, K) := Prod.ext hpx hpk
    simpa only [heq] using hp
  · intro hp
    exact Finset.mem_image.mpr
      ⟨(x, K), Finset.mem_filter.mpr ⟨hp, rfl⟩, rfl⟩
theorem rowXs_nonempty {S : Finset (α × β)} {K : β} (hK : K ∈ rowHeights S) :
    (rowXs S K).Nonempty := by
  classical
  obtain ⟨p, hp, hpk⟩ := Finset.mem_image.mp hK
  refine ⟨p.1, mem_rowXs.mpr ?_⟩
  simpa only [← hpk, Prod.eta] using hp
theorem snd_mem_rowHeights {S : Finset (α × β)} {p : α × β} (hp : p ∈ S) :
    p.2 ∈ rowHeights S := by
  classical
  exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
theorem row_distribution_card (S : Finset (α × β))
    (e : Fin (rowHeights S).card ≃ rowHeights S) (t : ℕ) :
    (Finset.univ.filter fun i => t ≤ (rowXs S (e i).val).card).card =
      ((rowHeights S).filter fun K => t ≤ (rowXs S K).card).card := by
  classical
  apply Finset.card_bij (fun i _ => (e i).val)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨(e i).property, (Finset.mem_filter.mp hi).2⟩
  · intro i hi j hj heq
    exact e.injective (Subtype.ext heq)
  · intro K hK
    let k : rowHeights S := ⟨K, (Finset.mem_filter.mp hK).1⟩
    refine ⟨e.symm k, ?_, ?_⟩
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.apply_symm_apply] using (Finset.mem_filter.mp hK).2
    · exact congrArg Subtype.val (e.apply_symm_apply k)
end
def descendingRowPermutation {s : ℕ} (N : Fin s → ℕ) : Equiv.Perm (Fin s) :=
  LocalTupleSort.sort (α := OrderDual ℕ) (fun i => N i)
theorem descendingRowPermutation_antitone {s : ℕ} (N : Fin s → ℕ) :
    Antitone (N ∘ descendingRowPermutation N) :=
  LocalTupleSort.monotone_sort (α := OrderDual ℕ) (fun i => N i)
theorem exists_ordered_rows {s : ℕ} (N : Fin s → ℕ) (q m : ℕ)
    (hpos : ∀ i, 1 ≤ N i) (hsize : ∀ i, N i ≤ m)
    (hdistribution : ∀ t, 1 ≤ t → t ≤ m →
      (Finset.univ.filter fun j => t ≤ N j).card ≤ q * (m - t + 1)) :
    ∃ σ : Equiv.Perm (Fin s), Antitone (N ∘ σ) ∧
      ∀ i : Fin s, i.val + 1 ≤ q * (m - N (σ i) + 1) := by
  let σ := descendingRowPermutation N
  refine ⟨σ, descendingRowPermutation_antitone N, ?_⟩
  intro i
  apply fin_ordered_row_bound (N ∘ σ) q m (descendingRowPermutation_antitone N)
    (fun j => hpos (σ j)) (fun j => hsize (σ j))
  intro t ht htm
  change (Finset.univ.filter fun j => t ≤ N (σ j)).card ≤ q * (m - t + 1)
  rw [distribution_card_permutation N σ t]
  exact hdistribution t ht htm
end Nagata.Workers.W10
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology
variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
theorem comp_coeff_eq_zero_below
    (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
    (m : ℕ) (hq : ∀ n < m, q n = 0) :
    ∀ n < m, (q.comp p) n = 0 := by
  intro n hn
  ext v
  simp only [FormalMultilinearSeries.comp, sum_apply,
    FormalMultilinearSeries.compAlongComposition_apply,
    zero_apply]
  apply Finset.sum_eq_zero
  intro c hc
  rw [hq c.length (lt_of_le_of_lt c.length_le hn)]
  rfl
def HasAnalyticOrderAtLeast (f : E → F) (x : E) (m : ℕ) : Prop :=
  ∃ p : FormalMultilinearSeries 𝕜 E F,
    HasFPowerSeriesAt f p x ∧ ∀ n < m, p n = 0
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology
end Nagata.Workers.W28
end
end
section
namespace Nagata.VariableUnitOrder
open scoped Topology
open Nagata.Workers.W28
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Nagata.VariableUnitOrder
end
section
noncomputable section
namespace Nagata.Workers.W28
end Nagata.Workers.W28
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.AffineMultiplicity
variable {σ K : Type*} [CommRing K]
noncomputable def pointIdeal (p : σ → K) : Ideal (MvPolynomial σ K) :=
  RingHom.ker (MvPolynomial.eval p)
section Field
variable {F : Type*} [Field F]
theorem pointIdeal_isMaximal (p : σ → F) : (pointIdeal p).IsMaximal := by
  apply RingHom.ker_isMaximal_of_surjective (MvPolynomial.eval p)
  intro a
  exact ⟨MvPolynomial.C a, MvPolynomial.eval_C a⟩
end Field
end Nagata.AffineMultiplicity
end
section
namespace Nagata.AffineMultiplicity
section MaximalIdeal
variable {R : Type*} [CommRing R] (I : Ideal R) (hI : I.IsMaximal)
include hI
end MaximalIdeal
section AffinePoint
variable {σ F : Type*} [Field F]
instance pointIdeal_isPrime (p : σ → F) : (pointIdeal p).IsPrime :=
  (pointIdeal_isMaximal p).isPrime
end AffinePoint
end Nagata.AffineMultiplicity
end
end OAI
end
section
namespace OAI
section
namespace Nagata.Workers.W30
open scoped BigOperators
abbrev JetIndex (q m : ℕ) := Σ b : Fin m, Fin (q * (m - b.val))
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open MvPolynomial
open scoped Pointwise
variable {σ R : Type*} [CommRing R]
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open scoped Pointwise
variable {A : Type*} [CommRing A]
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open MvPolynomial
open scoped BigOperators
variable (R : Type*) [CommRing R] (q m : ℕ)
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open MvPolynomial
variable {R : Type*} [CommRing R]
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open MvPolynomial
variable {R : Type*} [CommRing R]
end Nagata.Workers.W30
end
end OAI
end
section
namespace OAI
section
namespace Nagata.AffineMultiplicity
variable {R : Type*} [CommRing R]
end Nagata.AffineMultiplicity
end
section
namespace Nagata.AffineMultiplicity
variable {σ R : Type*} [CommRing R]
end Nagata.AffineMultiplicity
end
section
namespace Nagata.AffineMultiplicity
variable {σ R : Type*} [CommRing R]
end Nagata.AffineMultiplicity
end
section
namespace Nagata.AffineMultiplicity
variable {σ R : Type*} [CommRing R]
end Nagata.AffineMultiplicity
end
section
namespace Nagata.AffineMultiplicity
variable {σ R : Type*} [CommRing R]
section Field
variable {F : Type*} [Field F]
end Field
end Nagata.AffineMultiplicity
end
section
namespace Nagata.AffineMultiplicity
variable {R : Type*} [CommRing R]
end Nagata.AffineMultiplicity
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W28
open scoped BigOperators
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped BigOperators
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
end Nagata.Workers.W28
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W08
open Filter Topology
noncomputable def automorphicSections (τ : ℂ) (n : ℤ) (γ : ℂ) :
    Submodule ℂ (ℂ → ℂ) where
  carrier := {f | f 0 = 0 ∧ (∀ z, z ≠ 0 → DifferentiableAt ℂ f z) ∧
    (∀ z, z ≠ 0 → f (τ * z) = γ * z ^ (-n) * f z)}
  zero_mem' := by
    refine ⟨rfl, ?_, ?_⟩
    · intro z _
      exact differentiableAt_const 0
    · intro z _
      simp
  add_mem' := by
    intro f g hf hg
    refine ⟨?_, ?_, ?_⟩
    · change f 0 + g 0 = 0
      rw [hf.1, hg.1, add_zero]
    · intro z hz
      exact (hf.2.1 z hz).add (hg.2.1 z hz)
    · intro z hz
      change f (τ * z) + g (τ * z) = γ * z ^ (-n) * (f z + g z)
      rw [hf.2.2 z hz, hg.2.2 z hz, mul_add]
  smul_mem' := by
    intro a f hf
    refine ⟨?_, ?_, ?_⟩
    · change a * f 0 = 0
      rw [hf.1, mul_zero]
    · intro z hz
      exact (hf.2.1 z hz).const_smul a
    · intro z hz
      change a * f (τ * z) = γ * z ^ (-n) * (a * f z)
      rw [hf.2.2 z hz]
      ac_rfl
@[simp] theorem mem_automorphicSections_iff {τ γ : ℂ} {n : ℤ} {f : ℂ → ℂ} :
    f ∈ automorphicSections τ n γ ↔
      f 0 = 0 ∧ (∀ z, z ≠ 0 → DifferentiableAt ℂ f z) ∧
      (∀ z, z ≠ 0 → f (τ * z) = γ * z ^ (-n) * f z) := Iff.rfl
theorem automorphicSections_ext {τ γ : ℂ} {n : ℤ}
    (f g : automorphicSections τ n γ)
    (h : ∀ z, z ≠ 0 → f.val z = g.val z) : f = g := by
  apply Subtype.ext
  funext z
  by_cases hz : z = 0
  · subst z
    exact f.property.1.trans g.property.1.symm
  · exact h z hz
def sectionRestriction (τ : ℂ) (n : ℤ) (γ : ℂ) :
    automorphicSections τ n γ →ₗ[ℂ] ({z : ℂ // z ≠ 0} → ℂ) where
  toFun f z := f.val z.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem sectionRestriction_injective (τ : ℂ) (n : ℤ) (γ : ℂ) :
    Function.Injective (sectionRestriction τ n γ) := by
  intro f g h
  apply automorphicSections_ext
  intro z hz
  exact congrFun h ⟨z, hz⟩
noncomputable def normalizeAtZero (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else f z
@[simp] theorem normalizeAtZero_zero (f : ℂ → ℂ) : normalizeAtZero f 0 = 0 := by
  simp [normalizeAtZero]
@[simp] theorem normalizeAtZero_of_ne (f : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    normalizeAtZero f z = f z := by
  simp [normalizeAtZero, hz]
theorem normalizeAtZero_eventuallyEq (f : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    normalizeAtZero f =ᶠ[𝓝 z] f :=
  (eventually_ne_nhds hz).mono fun point hpoint ↦ normalizeAtZero_of_ne f (z := point) hpoint
theorem normalizeAtZero_differentiableAt_iff (f : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ (normalizeAtZero f) z ↔ DifferentiableAt ℂ f z :=
  (normalizeAtZero_eventuallyEq f hz).differentiableAt_iff
theorem normalizeAtZero_mem_automorphicSections {τ γ : ℂ} {n : ℤ}
    (hτ : τ ≠ 0) (f : ℂ → ℂ)
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z)
    (he : ∀ z, z ≠ 0 → f (τ * z) = γ * z ^ (-n) * f z) :
    normalizeAtZero f ∈ automorphicSections τ n γ := by
  refine ⟨normalizeAtZero_zero f, ?_, ?_⟩
  · intro z hz
    exact (normalizeAtZero_differentiableAt_iff f hz).mpr (hf z hz)
  · intro z hz
    rw [normalizeAtZero_of_ne f (mul_ne_zero hτ hz), normalizeAtZero_of_ne f hz]
    exact he z hz
noncomputable def sectionOfFunction {τ γ : ℂ} {n : ℤ}
    (hτ : τ ≠ 0) (f : ℂ → ℂ)
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z)
    (he : ∀ z, z ≠ 0 → f (τ * z) = γ * z ^ (-n) * f z) :
    automorphicSections τ n γ :=
  ⟨normalizeAtZero f, normalizeAtZero_mem_automorphicSections hτ f hf he⟩
@[simp] theorem sectionOfFunction_apply {τ γ : ℂ} {n : ℤ}
    (hτ : τ ≠ 0) (f : ℂ → ℂ)
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z)
    (he : ∀ z, z ≠ 0 → f (τ * z) = γ * z ^ (-n) * f z)
    {z : ℂ} (hz : z ≠ 0) :
    (sectionOfFunction hτ f hf he).val z = f z :=
  normalizeAtZero_of_ne f hz
end Nagata.W08
end
section
universe u
namespace Nagata.W08
def triangular (p : Int) : Int := p * (p - 1) / 2
@[simp] theorem triangular_zero : triangular 0 = 0 := by decide
theorem triangular_add_one (p : Int) : triangular (p + 1) = triangular p + p := by
  unfold triangular
  have h : (p + 1) * (p + 1 - 1) = p * (p - 1) + 2 * p := by
    simp only [Int.add_sub_cancel, Int.add_mul, Int.one_mul, Int.mul_sub, Int.mul_one]
    omega
  rw [h]
  omega
theorem triangular_sub_one (p : Int) : triangular (p - 1) = triangular p - (p - 1) := by
  have h := triangular_add_one (p - 1)
  have he : p - 1 + 1 = p := by omega
  rw [he] at h
  omega
def laurentExponent (n K p : Int) : Int := p * K + n * triangular p
@[simp] theorem laurentExponent_zero (n K : Int) : laurentExponent n K 0 = 0 := by
  simp [laurentExponent]
theorem laurentExponent_add_one (n K p : Int) :
    laurentExponent n K (p + 1) = laurentExponent n K p + (K + n * p) := by
  simp only [laurentExponent, triangular_add_one, Int.add_mul, Int.one_mul, Int.mul_add]
  omega
theorem laurentExponent_sub_one (n K p : Int) :
    laurentExponent n K (p - 1) = laurentExponent n K p - (K + n * (p - 1)) := by
  have h := laurentExponent_add_one n K (p - 1)
  have he : p - 1 + 1 = p := by omega
  rw [he] at h
  omega
theorem biInfinite_unique {α : Type u} (step : Int → α → α)
    (injective_step : ∀ p x y, step p x = step p y → x = y)
    (a b : Int → α) (ha : ∀ p, a (p + 1) = step p (a p))
    (hb : ∀ p, b (p + 1) = step p (b p)) (hzero : a 0 = b 0) : a = b := by
  have hnat : ∀ k : Nat, a (k : Int) = b (k : Int) := by
    intro k
    induction k with
    | zero => exact hzero
    | succ k ih =>
      have hindex : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
      rw [hindex, ha, hb, ih]
  have hneg : ∀ k : Nat, a (-(k : Int)) = b (-(k : Int)) := by
    intro k
    induction k with
    | zero => exact hzero
    | succ k ih =>
      apply injective_step (-((k + 1 : Nat) : Int))
      rw [← ha, ← hb]
      have hindex : -((k + 1 : Nat) : Int) + 1 = -(k : Int) := by omega
      rw [hindex]
      exact ih
  funext p
  cases p with
  | ofNat k => exact hnat k
  | negSucc k =>
    have hindex : Int.negSucc k = -((k + 1 : Nat) : Int) := by omega
    rw [hindex]
    exact hneg (k + 1)
theorem two_mul_triangular (p : Int) : 2 * triangular p = p * (p - 1) := by
  have heq : (fun p : Int => 2 * triangular p) = (fun p : Int => p * (p - 1)) := by
    apply biInfinite_unique (fun p x => x + 2 * p)
    · intro p x y h
      omega
    · intro p
      rw [triangular_add_one, Int.mul_add]
    · intro p
      simp only [Int.add_sub_cancel, Int.add_mul, Int.one_mul, Int.mul_sub, Int.mul_one]
      omega
    · decide
  exact congrFun heq p
theorem two_dvd_mul_pred (p : Int) : (2 : Int) ∣ p * (p - 1) :=
  ⟨triangular p, (two_mul_triangular p).symm⟩
theorem laurentExponent_eq_source (n K p : Int) :
    laurentExponent n K p = p * K + n * p * (p - 1) / 2 := by
  unfold laurentExponent triangular
  rw [← Int.mul_ediv_assoc n (two_dvd_mul_pred p), Int.mul_assoc]
end Nagata.W08
end
section
namespace Nagata.W08
end Nagata.W08
end
section
noncomputable section
namespace Nagata.W08
open Filter Topology
theorem periodic_eq_of_exp_eq (F : ℂ → ℂ)
    (hperiod : ∀ x (k : ℤ), F (x + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = F x)
    {x y : ℂ} (hxy : Complex.exp x = Complex.exp y) : F x = F y := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hxy
  rw [hk, hperiod]
theorem periodic_log_eq_localLog (F : ℂ → ℂ)
    (hperiod : ∀ x (k : ℤ), F (x + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = F x)
    {z z₀ : ℂ} (hz : z ≠ 0) (hz₀ : z₀ ≠ 0) :
    F (Complex.log z) = F (Complex.log (z / z₀) + Complex.log z₀) := by
  apply periodic_eq_of_exp_eq F hperiod
  rw [Complex.exp_log hz, Complex.exp_add, Complex.exp_log (div_ne_zero hz hz₀),
    Complex.exp_log hz₀, div_mul_cancel₀ _ hz₀]
theorem periodic_log_differentiableAt (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hperiod : ∀ x (k : ℤ), F (x + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = F x)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    DifferentiableAt ℂ (fun z ↦ F (Complex.log z)) z₀ := by
  have hdiv : DifferentiableAt ℂ (fun z : ℂ ↦ z / z₀) z₀ := by
    simp only [div_eq_mul_inv]
    exact differentiableAt_id.mul_const _
  have hslit : z₀ / z₀ ∈ Complex.slitPlane := by
    simp [div_self hz₀]
  have hlocal : DifferentiableAt ℂ
      (fun z : ℂ ↦ Complex.log (z / z₀) + Complex.log z₀) z₀ :=
    ((Complex.differentiableAt_log hslit).comp z₀ (f := fun z : ℂ ↦ z / z₀) hdiv).add
      (differentiableAt_const (Complex.log z₀))
  have hg := (hF (Complex.log (z₀ / z₀) + Complex.log z₀)).comp z₀ hlocal
  apply hg.congr_of_eventuallyEq
  exact (eventually_ne_nhds hz₀).mono fun z hz ↦
    periodic_log_eq_localLog F hperiod hz hz₀
theorem periodic_log_automorphy (F : ℂ → ℂ)
    (hperiod : ∀ x (k : ℤ), F (x + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = F x)
    {τ γ : ℂ} {n : ℤ} (hτ : τ ≠ 0)
    (hshift : ∀ x, F (x + Complex.log τ) =
      γ * Complex.exp (((-n : ℤ) : ℂ) * x) * F x)
    {z : ℂ} (hz : z ≠ 0) :
    F (Complex.log (τ * z)) = γ * z ^ (-n) * F (Complex.log z) := by
  have heq : F (Complex.log (τ * z)) = F (Complex.log z + Complex.log τ) := by
    apply periodic_eq_of_exp_eq F hperiod
    rw [Complex.exp_log (mul_ne_zero hτ hz), Complex.exp_add,
      Complex.exp_log hz, Complex.exp_log hτ, mul_comm]
  rw [heq, hshift, Complex.exp_int_mul, Complex.exp_log hz]
def automorphicSectionOfPeriodicFunction (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hperiod : ∀ x (k : ℤ), F (x + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = F x)
    {τ γ : ℂ} {n : ℤ} (hτ : τ ≠ 0)
    (hshift : ∀ x, F (x + Complex.log τ) =
      γ * Complex.exp (((-n : ℤ) : ℂ) * x) * F x) :
    automorphicSections τ n γ :=
  sectionOfFunction hτ (fun z ↦ F (Complex.log z))
    (fun _ hz ↦ periodic_log_differentiableAt F hF hperiod hz)
    (fun _ hz ↦ periodic_log_automorphy F hperiod hτ hshift hz)
theorem automorphicSectionOfPeriodicFunction_exp (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hperiod : ∀ x (k : ℤ), F (x + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = F x)
    {τ γ : ℂ} {n : ℤ} (hτ : τ ≠ 0)
    (hshift : ∀ x, F (x + Complex.log τ) =
      γ * Complex.exp (((-n : ℤ) : ℂ) * x) * F x) (x : ℂ) :
    (automorphicSectionOfPeriodicFunction F hF hperiod hτ hshift).val (Complex.exp x) = F x := by
  change normalizeAtZero (fun z ↦ F (Complex.log z)) (Complex.exp x) = F x
  rw [normalizeAtZero_of_ne _ (Complex.exp_ne_zero x)]
  apply periodic_eq_of_exp_eq F hperiod
  exact Complex.exp_log (Complex.exp_ne_zero x)
end Nagata.W08
end
end
section
namespace Nagata.W08
variable {F : Type*} [CommGroupWithZero F]
def orbitValue (τ γ : F) (n K : ℤ) (c₀ : F) (p : ℤ) : F :=
  γ ^ (-p) * τ ^ (laurentExponent n K p) * c₀
@[simp] theorem orbitValue_zero (τ γ : F) (n K : ℤ) (c₀ : F) :
    orbitValue τ γ n K c₀ 0 = c₀ := by
  simp [orbitValue]
theorem orbitValue_add_one (τ γ : F) (hτ : τ ≠ 0) (hγ : γ ≠ 0)
    (n K : ℤ) (c₀ : F) (p : ℤ) :
    orbitValue τ γ n K c₀ (p + 1) =
      (γ⁻¹ * τ ^ (K + n * p)) * orbitValue τ γ n K c₀ p := by
  unfold orbitValue
  rw [show -(p + 1) = -1 + -p by omega, zpow_add₀ hγ, zpow_neg_one,
    laurentExponent_add_one, zpow_add₀ hτ]
  ac_rfl
theorem laurent_recurrence_all_int (τ γ : F) (hτ : τ ≠ 0) (hγ : γ ≠ 0)
    (n : ℤ) (c : ℤ → F)
    (hc : ∀ K, c (K + n) = γ⁻¹ * τ ^ K * c K) (K p : ℤ) :
    c (K + n * p) = c K * γ ^ (-p) * τ ^ (p * K + n * (p * (p - 1) / 2)) := by
  have horbit : (fun p : ℤ => c (K + n * p)) = orbitValue τ γ n K (c K) := by
    apply biInfinite_unique (fun p x => (γ⁻¹ * τ ^ (K + n * p)) * x)
    · intro p
      exact fun _ _ h => mul_left_cancel₀
        (mul_ne_zero (inv_ne_zero hγ) (zpow_ne_zero _ hτ)) h
    · intro p
      have hindex : K + n * (p + 1) = K + n * p + n := by
        simp only [Int.mul_add, Int.mul_one]
        omega
      rw [hindex, hc]
    · exact orbitValue_add_one τ γ hτ hγ n K (c K)
    · simp
  have hvalue := congrFun horbit p
  simpa only [orbitValue, laurentExponent, triangular, mul_assoc, mul_comm, mul_left_comm]
    using hvalue
theorem laurent_recurrence_source_formula (τ γ : F) (hτ : τ ≠ 0) (hγ : γ ≠ 0)
    (n : ℤ) (c : ℤ → F)
    (hc : ∀ K, c (K + n) = γ⁻¹ * τ ^ K * c K) (K p : ℤ) :
    c (K + n * p) = c K * γ ^ (-p) * τ ^ (p * K + n * p * (p - 1) / 2) := by
  have h := laurent_recurrence_all_int τ γ hτ hγ n c hc K p
  change c (K + n * p) = c K * γ ^ (-p) * τ ^ (laurentExponent n K p) at h
  rw [laurentExponent_eq_source] at h
  exact h
theorem recurrence_of_coefficient_balance (τ γ : F) (hγ : γ ≠ 0)
    (n : ℤ) (c : ℤ → F)
    (hbalance : ∀ K, τ ^ K * c K = γ * c (K + n)) :
    ∀ K, c (K + n) = γ⁻¹ * τ ^ K * c K := by
  intro K
  calc
    c (K + n) = γ⁻¹ * (γ * c (K + n)) := (inv_mul_cancel_left₀ hγ _).symm
    _ = γ⁻¹ * (τ ^ K * c K) := by rw [← hbalance]
    _ = γ⁻¹ * τ ^ K * c K := (mul_assoc _ _ _).symm
end Nagata.W08
end
end OAI
end
section
namespace OAI
section
namespace Nagata.CoefficientSpaces
noncomputable def multiplyPower (P : ℂ → ℂ) (e : ℕ) :
    (ℂ → ℂ) →ₗ[ℂ] (ℂ → ℂ) where
  toFun f z := P z ^ e * f z
  map_add' f g := by funext z; simp [mul_add]
  map_smul' a f := by funext z; simp; ring
theorem multiplyPower_mem_sections {τ γ δ : ℂ} {n s : ℤ} {P f : ℂ → ℂ}
    (hP : P ∈ Nagata.W08.automorphicSections τ s δ)
    (hf : f ∈ Nagata.W08.automorphicSections τ n γ) (e : ℕ) :
    multiplyPower P e f ∈ Nagata.W08.automorphicSections τ
      (n + (e : ℤ) * s) (γ * δ ^ e) := by
  refine ⟨?_, ?_, ?_⟩
  · change P 0 ^ e * f 0 = 0
    rw [hf.1, mul_zero]
  · intro z hz
    exact ((hP.2.1 z hz).pow e).mul (hf.2.1 z hz)
  · intro z hz
    change P (τ * z) ^ e * f (τ * z) =
      (γ * δ ^ e) * z ^ (-(n + (e : ℤ) * s)) * (P z ^ e * f z)
    rw [hP.2.2 z hz, hf.2.2 z hz]
    have he : -(n + (e : ℤ) * s) = -n + (-s) * (e : ℤ) := by ring
    rw [he, zpow_add₀ hz, zpow_mul, zpow_natCast]
    simp only [mul_pow]
    ring
noncomputable def normalMinusMarkedMultiplier (γL γP : ℂ) : ℂ := γL ^ 3 / γP
noncomputable def coefficientSpace (τ γL γP : ℂ) (d m j : ℤ) (P : ℂ → ℂ) :
    Submodule ℂ (ℂ → ℂ) :=
  if j ≤ m then
    Nagata.W08.automorphicSections τ (3 * (d - 3 * m))
      (γL ^ (d - 3 * m) * normalMinusMarkedMultiplier γL γP ^ (m - j))
  else
    (Nagata.W08.automorphicSections τ (3 * (d - 3 * j)) (γL ^ (d - 3 * j))).map
      (multiplyPower P (j - m).toNat)
theorem mem_coefficientSpace_second {τ γL γP : ℂ} {d m j : ℤ} {P g : ℂ → ℂ}
    (hj : m < j) :
    g ∈ coefficientSpace τ γL γP d m j P ↔
      ∃ f ∈ Nagata.W08.automorphicSections τ (3 * (d - 3 * j))
        (γL ^ (d - 3 * j)), multiplyPower P (j - m).toNat f = g := by
  rw [coefficientSpace, if_neg (not_le.mpr hj)]
  exact Submodule.mem_map
theorem coefficientSpace_differentiableAt {τ γL γP : ℂ} {d m j : ℤ}
    {P f : ℂ → ℂ}
    (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z)
    (hf : f ∈ coefficientSpace τ γL γP d m j P) {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ f z := by
  by_cases hj : j ≤ m
  · rw [coefficientSpace, if_pos hj] at hf
    exact hf.2.1 z hz
  · obtain ⟨g, hg, rfl⟩ := (mem_coefficientSpace_second (lt_of_not_ge hj)).mp hf
    exact ((hP z hz).pow (j - m).toNat).mul (hg.2.1 z hz)
theorem coefficientSpace_zero_value {τ γL γP : ℂ} {d m j : ℤ}
    {P f : ℂ → ℂ} (hf : f ∈ coefficientSpace τ γL γP d m j P) : f 0 = 0 := by
  by_cases hj : j ≤ m
  · rw [coefficientSpace, if_pos hj] at hf
    exact hf.1
  · obtain ⟨g, hg, rfl⟩ := (mem_coefficientSpace_second (lt_of_not_ge hj)).mp hf
    change P 0 ^ (j - m).toNat * g 0 = 0
    rw [hg.1, mul_zero]
noncomputable def polynomialSections (τ γL γP : ℂ) (d m : ℤ) (P : ℂ → ℂ) :
    Submodule ℂ (Polynomial (ℂ → ℂ)) where
  carrier := {F | (∀ j : ℕ, (d / 3).toNat < j → F.coeff j = 0) ∧
    ∀ j : ℕ, F.coeff j ∈ coefficientSpace τ γL γP d m (j : ℤ) P}
  zero_mem' := by
    constructor
    · intro j _; simp
    · intro j; simp
  add_mem' := by
    intro F G hF hG
    constructor
    · intro j hj
      simp only [Polynomial.coeff_add, hF.1 j hj, hG.1 j hj, add_zero]
    · intro j
      simpa only [Polynomial.coeff_add] using
        (coefficientSpace τ γL γP d m (j : ℤ) P).add_mem (hF.2 j) (hG.2 j)
  smul_mem' := by
    intro a F hF
    constructor
    · intro j hj
      simp only [Polynomial.coeff_smul, hF.1 j hj, smul_zero]
    · intro j
      simpa only [Polynomial.coeff_smul] using
        (coefficientSpace τ γL γP d m (j : ℤ) P).smul_mem a (hF.2 j)
noncomputable def scalarExpression (F : Polynomial (ℂ → ℂ)) (z v : ℂ) : ℂ :=
  F.sum fun j f => f z * v ^ j
end Nagata.CoefficientSpaces
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W19
open scoped BigOperators Topology
open Filter Set
theorem analyticOnNhd_dslope {U : Set ℂ} {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h U) (a : ℂ) (ha : a ∈ U) :
    AnalyticOnNhd ℂ (dslope h a) U := by
  intro z hz
  by_cases hza : z = a
  · subst z
    obtain ⟨P, hP⟩ := hh a ha
    exact ⟨P.fslope, hP.has_fpower_series_dslope_fslope⟩
  · have hquot : AnalyticAt ℂ (fun w => (h w - h a) / (w - a)) z :=
      ((hh z hz).sub analyticAt_const).div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr hza)
    apply hquot.congr
    filter_upwards [isOpen_ne.mem_nhds hza] with w hw
    simp [dslope_of_ne h hw, slope, div_eq_mul_inv, smul_eq_mul, mul_comm]
theorem exists_analytic_centered_factor
    {U : Set ℂ} (hU : IsOpen U) (h : ℂ → ℂ)
    (hh : AnalyticOnNhd ℂ h U) (a : ℂ) (ha : a ∈ U)
    (k : ℕ) (ho : (k : ℕ∞) ≤ analyticOrderAt h a) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧
      ∀ z, h z = (z - a) ^ k * g z := by
  induction k generalizing h with
  | zero => exact ⟨h, hh, fun z => by simp⟩
  | succ k ih =>
    have hzero : h a = 0 := by
      apply apply_eq_zero_of_analyticOrderAt_ne_zero
      intro hz
      rw [hz] at ho
      simp at ho
    let g := dslope h a
    have hg : AnalyticOnNhd ℂ g U := analyticOnNhd_dslope hh a ha
    have heq : ∀ z, h z = (z - a) * g z := by
      intro z
      simpa [g, hzero, smul_eq_mul] using (sub_smul_dslope h a z).symm
    have hfun : h = (fun z => z - a) * g := funext heq
    have hlin : analyticOrderAt (fun z : ℂ => z - a) a = 1 := by
      simp
    have horder : analyticOrderAt h a = 1 + analyticOrderAt g a := by
      rw [hfun, analyticOrderAt_mul (by fun_prop)
        (hg.differentiableOn.analyticAt (hU.mem_nhds ha)), hlin]
    have hgo : (k : ℕ∞) ≤ analyticOrderAt g a := by
      rw [horder] at ho
      apply (ENat.add_le_add_iff_left (by simp : (1 : ℕ∞) ≠ ⊤)).mp
      simpa [Nat.cast_add, add_comm] using ho
    obtain ⟨G, hG, heG⟩ := ih g hg hgo
    refine ⟨G, hG, fun z => ?_⟩
    rw [heq z, heG z, pow_succ]
    ac_rfl
theorem analytic_order_of_nonvanishing_analytic_factor
    {U : Set ℂ} (hU : IsOpen U) {h g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g U) {a b : ℂ} (hb : b ∈ U)
    (hab : b ≠ a) (k : ℕ) (heq : ∀ z, h z = (z - a) ^ k * g z) :
    analyticOrderAt h b = analyticOrderAt g b := by
  have hfun : h = (fun z => (z - a) ^ k) * g := funext heq
  have hfac : AnalyticAt ℂ (fun z => (z - a) ^ k) b := by fun_prop
  rw [hfun, analyticOrderAt_mul hfac (hg.differentiableOn.analyticAt (hU.mem_nhds hb))]
  have hz : analyticOrderAt (fun z => (z - a) ^ k) b = 0 :=
    hfac.analyticOrderAt_eq_zero.mpr (pow_ne_zero k (sub_ne_zero.mpr hab))
  rw [hz, zero_add]
theorem exists_analytic_finset_factorization
    {I : Type*} (s : Finset I) {U : Set ℂ} (hU : IsOpen U)
    (h : ℂ → ℂ) (hh : AnalyticOnNhd ℂ h U)
    (ξ : I → ℂ) (hξ : Function.Injective ξ) (hmem : ∀ i ∈ s, ξ i ∈ U)
    (k : ℕ) (ho : ∀ i ∈ s, (k : ℕ∞) ≤ analyticOrderAt h (ξ i)) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧
      ∀ z, h z = (∏ i ∈ s, (z - ξ i) ^ k) * g z := by
  classical
  induction s using Finset.induction_on generalizing h with
  | empty => exact ⟨h, hh, fun z => by simp⟩
  | @insert i s his ih =>
    obtain ⟨g, hg, hfg⟩ := exists_analytic_centered_factor hU h hh (ξ i)
      (hmem i (Finset.mem_insert_self i s)) k (ho i (Finset.mem_insert_self i s))
    have hmems : ∀ j ∈ s, ξ j ∈ U := fun j hj =>
      hmem j (Finset.mem_insert_of_mem hj)
    have hgos : ∀ j ∈ s, (k : ℕ∞) ≤ analyticOrderAt g (ξ j) := by
      intro j hj
      have hji : ξ j ≠ ξ i := hξ.ne (fun e => his (e ▸ hj))
      rw [← analytic_order_of_nonvanishing_analytic_factor hU hg (hmems j hj) hji k hfg]
      exact ho j (Finset.mem_insert_of_mem hj)
    obtain ⟨G, hG, heG⟩ := ih g hg hmems hgos
    refine ⟨G, hG, fun z => ?_⟩
    rw [hfg z, heG z, Finset.prod_insert his, mul_assoc]
theorem exists_analytic_factorization
    {q : ℕ} {U : Set ℂ} (hU : IsOpen U) (h : ℂ → ℂ)
    (hh : AnalyticOnNhd ℂ h U) (ξ : Fin q → ℂ)
    (hξ : Function.Injective ξ) (hmem : ∀ i, ξ i ∈ U)
    (k : ℕ) (ho : ∀ i, (k : ℕ∞) ≤ analyticOrderAt h (ξ i)) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧
      ∀ z, h z = (∏ i, (z - ξ i) ^ k) * g z := by
  exact exists_analytic_finset_factorization Finset.univ hU h hh ξ hξ
    (fun i _ => hmem i) k (fun i _ => ho i)
end Nagata.W19
end
section
namespace Nagata.W19
end Nagata.W19
end
section
namespace Nagata.W19
open scoped BigOperators
theorem exists_holomorphic_finset_factorization
    {I : Type*} (s : Finset I) {U : Set ℂ} (hU : IsOpen U)
    (h : ℂ → ℂ) (hh : DifferentiableOn ℂ h U)
    (ξ : I → ℂ) (hξ : Function.Injective ξ) (hmem : ∀ i ∈ s, ξ i ∈ U)
    (k : ℕ) (ho : ∀ i ∈ s, (k : ℕ∞) ≤ analyticOrderAt h (ξ i)) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧
      ∀ z, h z = (∏ i ∈ s, (z - ξ i) ^ k) * g z := by
  obtain ⟨g, hg, heq⟩ := exists_analytic_finset_factorization s hU h
    (hh.analyticOnNhd hU) ξ hξ hmem k ho
  exact ⟨g, hg.differentiableOn, heq⟩
theorem exists_holomorphic_factorization
    {q : ℕ} {U : Set ℂ} (hU : IsOpen U) (h : ℂ → ℂ)
    (hh : DifferentiableOn ℂ h U) (ξ : Fin q → ℂ)
    (hξ : Function.Injective ξ) (hmem : ∀ i, ξ i ∈ U)
    (k : ℕ) (ho : ∀ i, (k : ℕ∞) ≤ analyticOrderAt h (ξ i)) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧
      ∀ z, h z = (∏ i, (z - ξ i) ^ k) * g z := by
  obtain ⟨g, hg, heq⟩ := exists_analytic_factorization hU h
    (hh.analyticOnNhd hU) ξ hξ hmem k ho
  exact ⟨g, hg.differentiableOn, heq⟩
end Nagata.W19
end
section
namespace Nagata.W19
end Nagata.W19
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W20
open Filter Metric
open scoped Topology BigOperators
variable {R : Type*} [NormedRing R]
theorem uniform_linear_combination_of_bounds {ι X : Type*} [Fintype ι]
    (K : Set X) (b : ι → X → R) (B : ι → ℝ)
    (hB : ∀ i z, z ∈ K → ‖b i z‖ ≤ B i)
    (c : ℕ → ι → R) (c₀ : ι → R)
    (hc : ∀ i, Tendsto (fun n => c n i) atTop (𝓝 (c₀ i))) :
    TendstoUniformlyOn (fun n z => ∑ i, c n i * b i z)
      (fun z => ∑ i, c₀ i * b i z) atTop K := by
  classical
  have herr : Tendsto (fun n => ∑ i, ‖c n i - c₀ i‖ * B i) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset ι) (fun i _ =>
      ((hc i).sub (tendsto_const_nhds (x := c₀ i))).norm.mul (tendsto_const_nhds (x := B i)))
    simpa only [sub_self, norm_zero, zero_mul, Finset.sum_const_zero] using h
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [herr.eventually_lt_const hε] with n hn
  intro z hz
  calc
    dist (∑ i, c₀ i * b i z) (∑ i, c n i * b i z)
        = ‖∑ i, (c n i - c₀ i) * b i z‖ := by
            rw [dist_comm, dist_eq_norm, ← Finset.sum_sub_distrib]
            simp only [sub_mul]
    _ ≤ ∑ i, ‖(c n i - c₀ i) * b i z‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖c n i - c₀ i‖ * ‖b i z‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact norm_mul_le _ _
    _ ≤ ∑ i, ‖c n i - c₀ i‖ * B i := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hB i z hz) (norm_nonneg _)
    _ < ε := hn
theorem uniform_linear_combination_on_compact {ι X : Type*} [Fintype ι]
    [TopologicalSpace X] (K : Set X) (hK : IsCompact K)
    (b : ι → X → R) (hb : ∀ i, ContinuousOn (b i) K)
    (c : ℕ → ι → R) (c₀ : ι → R)
    (hc : ∀ i, Tendsto (fun n => c n i) atTop (𝓝 (c₀ i))) :
    TendstoUniformlyOn (fun n z => ∑ i, c n i * b i z)
      (fun z => ∑ i, c₀ i * b i z) atTop K := by
  classical
  have hbounds := fun i => hK.exists_bound_of_continuousOn (hb i)
  let B : ι → ℝ := fun i => Classical.choose (hbounds i)
  apply uniform_linear_combination_of_bounds K b B
  · intro i z hz
    exact Classical.choose_spec (hbounds i) z hz
  · exact hc
theorem locally_uniform_linear_combination {ι X : Type*} [Fintype ι]
    [TopologicalSpace X] [LocallyCompactSpace X]
    {U : Set X} (hU : IsOpen U) (b : ι → X → R)
    (hb : ∀ i, ContinuousOn (b i) U)
    (c : ℕ → ι → R) (c₀ : ι → R)
    (hc : ∀ i, Tendsto (fun n => c n i) atTop (𝓝 (c₀ i))) :
    TendstoLocallyUniformlyOn (fun n z => ∑ i, c n i * b i z)
      (fun z => ∑ i, c₀ i * b i z) atTop U := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mpr
  intro K hKU hK
  exact uniform_linear_combination_on_compact K hK b (fun i => (hb i).mono hKU) c c₀ hc
end Nagata.W20
end
section
namespace Nagata.W20
open Filter
open scoped Topology
theorem unit_subsequence {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (v : ℕ → E) (hv : ∀ n, ‖v n‖ = 1) :
    ∃ a : E, ‖a‖ = 1 ∧ a ≠ 0 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (v ∘ φ) atTop (𝓝 a) := by
  obtain ⟨a, ha, φ, hφ, hlim⟩ :=
    (isCompact_sphere (0 : E) 1).tendsto_subseq (fun n => by
      simpa only [Metric.mem_sphere, dist_zero_right] using hv n)
  have hnorm : ‖a‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using ha
  refine ⟨a, hnorm, ?_, φ, hφ, hlim⟩
  intro ha0
  simp [ha0] at hnorm
end Nagata.W20
end
section
namespace Nagata.W20
open Filter Metric
open scoped Topology BigOperators
variable {𝕜 : Type*} [NormedField 𝕜]
theorem boundary_distance_lower {z ξ : 𝕜} {r : ℝ}
    (hz : ‖z‖ = r) (hξ : ‖ξ‖ ≤ r / 2) : r / 2 ≤ ‖z - ξ‖ := by
  have h := norm_sub_norm_le z ξ
  linarith
theorem collision_product_boundary_lower {ι : Type*} [Fintype ι]
    (ξ : ι → 𝕜) (k : ℕ) {r : ℝ} (hr : 0 < r)
    (hξ : ∀ i, ‖ξ i‖ ≤ r / 2) {z : 𝕜} (hz : ‖z‖ = r) :
    (r / 2) ^ (k * Fintype.card ι) ≤ ‖∏ i, (z - ξ i) ^ k‖ := by
  classical
  rw [norm_prod]
  have hp : (∏ _i : ι, (r / 2) ^ k) ≤ ∏ i : ι, ‖(z - ξ i) ^ k‖ := by
    apply Finset.prod_le_prod
    · intro i _
      exact pow_nonneg (by positivity) k
    · intro i _
      rw [norm_pow]
      exact pow_le_pow_left₀ (by positivity) (boundary_distance_lower hz (hξ i)) k
  simpa only [Finset.prod_const, Finset.card_univ, ← pow_mul] using hp
theorem collision_product_tendsto {ι : Type*} [Fintype ι]
    (ξ : ℕ → ι → 𝕜) (k : ℕ) (hξ : ∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0))
    (z : 𝕜) :
    Tendsto (fun n => ∏ i, (z - ξ n i) ^ k) atTop
      (𝓝 (z ^ (k * Fintype.card ι))) := by
  classical
  have hp := tendsto_finsetProd (Finset.univ : Finset ι)
    (fun i _ => ((tendsto_const_nhds (x := z)).sub (hξ i)).pow k)
  simpa only [sub_zero, Finset.prod_const, Finset.card_univ, ← pow_mul] using hp
theorem collision_limit_growth {ι : Type*} [Fintype ι]
    (ξ : ℕ → ι → 𝕜) (k : ℕ) (hξ : ∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0))
    (H G : ℕ → 𝕜 → 𝕜) (f : 𝕜 → 𝕜) (z : 𝕜) (C : ℝ)
    (hlim : Tendsto (fun n => H n z) atTop (𝓝 (f z)))
    (hfactor : ∀ n, H n z = (∏ i, (z - ξ n i) ^ k) * G n z)
    (hbound : ∀ n, ‖G n z‖ ≤ C) :
    ‖f z‖ ≤ ‖z‖ ^ (k * Fintype.card ι) * C := by
  have hp := (collision_product_tendsto ξ k hξ z).norm.mul
    (tendsto_const_nhds (x := C))
  apply le_of_tendsto_of_tendsto' hlim.norm (by simpa only [norm_pow] using hp)
  intro n
  rw [hfactor n, norm_mul]
  exact mul_le_mul_of_nonneg_left (hbound n) (norm_nonneg _)
theorem collision_limit_growth_eventually {ι : Type*} [Fintype ι]
    (ξ : ℕ → ι → 𝕜) (k : ℕ) (hξ : ∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0))
    (H G : ℕ → 𝕜 → 𝕜) (f : 𝕜 → 𝕜) (z : 𝕜) (C : ℝ)
    (hlim : Tendsto (fun n => H n z) atTop (𝓝 (f z)))
    (hfactor : ∀ n, H n z = (∏ i, (z - ξ n i) ^ k) * G n z)
    (hbound : ∀ᶠ n in atTop, ‖G n z‖ ≤ C) :
    ‖f z‖ ≤ ‖z‖ ^ (k * Fintype.card ι) * C := by
  have hp := (collision_product_tendsto ξ k hξ z).norm.mul
    (tendsto_const_nhds (x := C))
  apply le_of_tendsto_of_tendsto hlim.norm (by simpa only [norm_pow] using hp)
  filter_upwards [hbound] with n hn
  rw [hfactor n, norm_mul]
  exact mul_le_mul_of_nonneg_left hn (norm_nonneg _)
end Nagata.W20
end
section
namespace Nagata.W20
open Filter Metric
open scoped Topology
noncomputable def collisionCenters (q : ℕ) (r : ℝ) (n : ℕ) (i : Fin q) : ℂ :=
  ((r * (i.val : ℝ) / ((q + 1 : ℝ) * (n + 1 : ℝ)) : ℝ) : ℂ)
theorem collisionCenters_injective (q : ℕ) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    Function.Injective (collisionCenters q r n) := by
  intro i j hij
  apply Fin.ext
  apply Nat.cast_injective (R := ℝ)
  have heq : r * (i.val : ℝ) / ((q + 1 : ℝ) * (n + 1 : ℝ)) =
      r * (j.val : ℝ) / ((q + 1 : ℝ) * (n + 1 : ℝ)) :=
    Complex.ofReal_injective hij
  have hd : ((q + 1 : ℝ) * (n + 1 : ℝ)) ≠ 0 := by positivity
  exact mul_left_cancel₀ (ne_of_gt hr) ((div_left_inj' hd).mp heq)
theorem collisionCenters_mem_ball (q : ℕ) {r : ℝ} (hr : 0 < r)
    (n : ℕ) (i : Fin q) : collisionCenters q r n i ∈ ball 0 r := by
  have hi : (i.val : ℝ) < q + 1 := by exact_mod_cast Nat.lt_succ_of_lt i.isLt
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hd : (0 : ℝ) < (q + 1) * (n + 1) := by positivity
  have hir : (i.val : ℝ) < (q + 1 : ℝ) * (n + 1 : ℝ) := by nlinarith
  have hnonneg : 0 ≤ r * (i.val : ℝ) / ((q + 1 : ℝ) * (n + 1 : ℝ)) := by positivity
  simp only [Metric.mem_ball, dist_zero_right, collisionCenters, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact (div_lt_iff₀ hd).mpr (mul_lt_mul_of_pos_left hir hr)
theorem collisionCenters_tendsto (q : ℕ) (r : ℝ) (i : Fin q) :
    Tendsto (fun n => collisionCenters q r n i) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (r * (i.val : ℝ) / (q + 1 : ℝ)) *
      (1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := r * (i.val : ℝ) / (q + 1 : ℝ))).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp h
  simpa [collisionCenters, div_mul_eq_div_mul_one_div, Function.comp_def] using hc
theorem exists_collision_centers {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (q : ℕ) : ∃ ξ : ℕ → Fin q → ℂ,
      (∀ n, Function.Injective (ξ n)) ∧ (∀ n i, ξ n i ∈ U) ∧
      (∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0)) := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  exact ⟨collisionCenters q r, collisionCenters_injective q hr,
    fun n i => hsub (collisionCenters_mem_ball q hr n i), collisionCenters_tendsto q r⟩
end Nagata.W20
end
section
namespace Nagata.W20
open Filter Metric Set
open scoped Topology
theorem analyticOrderAt_lower_of_growth (f : ℂ → ℂ) (N : ℕ) {r C : ℝ}
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball 0 r))
    (hbound : ∀ z ∈ ball (0 : ℂ) r, ‖f z‖ ≤ ‖z‖ ^ N * C) :
    (N : ℕ∞) ≤ analyticOrderAt f 0 := by
  by_cases hN : N = 0
  · simp [hN]
  let Q : ℂ → ℂ := fun z => f z / z ^ N
  have hQdiff : DifferentiableOn ℂ Q (ball 0 r \ {0}) := by
    apply (hf.mono sdiff_subset).div (differentiableOn_id.pow N)
    intro z hz
    exact pow_ne_zero N hz.2
  have hQbound : BddAbove ((norm ∘ Q) '' (ball 0 r \ {0})) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    change ‖f z / z ^ N‖ ≤ C
    rw [norm_div, norm_pow]
    apply (div_le_iff₀ (pow_pos (norm_pos_iff.mpr hz.2) N)).mpr
    simpa only [mul_comm] using hbound z hz.1
  let G := Function.update Q 0 (limUnder (𝓝[≠] (0 : ℂ)) Q)
  have hG : DifferentiableOn ℂ G (ball 0 r) :=
    Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds _ hr)
      hQdiff hQbound
  apply (natCast_le_analyticOrderAt (hf.analyticAt (ball_mem_nhds _ hr))).mpr
  refine ⟨G, hG.analyticAt (ball_mem_nhds _ hr), ?_⟩
  filter_upwards [ball_mem_nhds (0 : ℂ) hr] with z hz
  by_cases hz0 : z = 0
  · subst z
    have hf0 : f 0 = 0 := by
      have h := hbound 0 (mem_ball_self hr)
      simpa [zero_pow hN] using h
    simp [hf0, zero_pow hN]
  · change f z = (z - 0) ^ N • Function.update Q 0 (limUnder (𝓝[≠] (0 : ℂ)) Q) z
    rw [Function.update_of_ne hz0, sub_zero, smul_eq_mul]
    change f z = z ^ N * (f z / z ^ N)
    rw [mul_comm, div_mul_cancel₀ _ (pow_ne_zero N hz0)]
end Nagata.W20
end
section
namespace Nagata.W20
open Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E]
theorem eventual_uniform_bound_on_compact {X : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (H : ℕ → X → E) (f : X → E)
    (hf : ContinuousOn f K) (hlim : TendstoUniformlyOn H f atTop K) :
    ∃ M : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, ‖H n z‖ ≤ M := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hf
  refine ⟨M + 1, ?_⟩
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hlim) 1 zero_lt_one] with n hn
  intro z hz
  apply (norm_le_norm_add_norm_sub (f z) (H n z)).trans
  apply add_le_add (hM z hz)
  exact le_of_lt (by simpa only [dist_eq_norm] using hn z hz)
theorem centers_eventually_half_disk {ι : Type*} [Finite ι]
    (ξ : ℕ → ι → E) (hξ : ∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0))
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n in atTop, ∀ i, ‖ξ n i‖ ≤ r / 2 := by
  apply Filter.eventually_all.mpr
  intro i
  filter_upwards [(hξ i).eventually (ball_mem_nhds (0 : E) (half_pos hr))] with n hn
  exact le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hn)
end Nagata.W20
end
section
namespace Nagata.W20
open Filter Metric
open scoped Topology BigOperators
theorem quotient_bound_on_closedBall (f P g : ℂ → ℂ) {r a M : ℝ}
    (hr : 0 < r) (ha : 0 < a)
    (hg : DiffContOnCl ℂ g (ball 0 r))
    (hfactor : ∀ z ∈ sphere (0 : ℂ) r, f z = P z * g z)
    (hlower : ∀ z ∈ sphere (0 : ℂ) r, a ≤ ‖P z‖)
    (hupper : ∀ z ∈ sphere (0 : ℂ) r, ‖f z‖ ≤ M)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) r) : ‖g z‖ ≤ M / a := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hg
  · intro w hw
    have hws : w ∈ sphere (0 : ℂ) r := by
      simpa only [frontier_ball (0 : ℂ) hr.ne'] using hw
    apply (le_div_iff₀ ha).mpr
    calc
      ‖g w‖ * a ≤ ‖g w‖ * ‖P w‖ :=
        mul_le_mul_of_nonneg_left (hlower w hws) (norm_nonneg _)
      _ = ‖f w‖ := by rw [hfactor w hws, norm_mul, mul_comm]
      _ ≤ M := hupper w hws
  · simpa only [closure_ball (0 : ℂ) hr.ne'] using hz
end Nagata.W20
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W20
open Filter Metric
open scoped Topology BigOperators
theorem order_collision_of_holomorphic_factorization {ι : Type*} [Fintype ι]
    (ξ : ℕ → ι → ℂ) (k : ℕ) (H G : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    {r M : ℝ} (hr : 0 < r)
    (hξlim : ∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0))
    (hξbound : ∀ᶠ n in atTop, ∀ i, ‖ξ n i‖ ≤ r / 2)
    (hf : DifferentiableOn ℂ f (ball 0 r))
    (hlim : ∀ z ∈ ball (0 : ℂ) r, Tendsto (fun n => H n z) atTop (𝓝 (f z)))
    (hG : ∀ n, DiffContOnCl ℂ (G n) (ball 0 r))
    (hfactor : ∀ n, ∀ z ∈ closedBall (0 : ℂ) r,
      H n z = (∏ i, (z - ξ n i) ^ k) * G n z)
    (hupper : ∀ᶠ n in atTop, ∀ z ∈ sphere (0 : ℂ) r, ‖H n z‖ ≤ M) :
    (↑(k * Fintype.card ι) : ℕ∞) ≤ analyticOrderAt f 0 := by
  classical
  let a := (r / 2) ^ (k * Fintype.card ι)
  have ha : 0 < a := pow_pos (by positivity) _
  apply analyticOrderAt_lower_of_growth f (k * Fintype.card ι) hr hf
  intro z hz
  apply collision_limit_growth_eventually ξ k hξlim H G f z (M / a) (hlim z hz)
  · intro n
    exact hfactor n z (ball_subset_closedBall hz)
  · filter_upwards [hξbound, hupper] with n hξn hn
    apply quotient_bound_on_closedBall (H n) (fun w => ∏ i, (w - ξ n i) ^ k)
      (G n) hr ha (hG n)
    · intro w hw
      exact hfactor n w (sphere_subset_closedBall hw)
    · intro w hw
      apply collision_product_boundary_lower (ξ n) k hr hξn
      simpa only [Metric.mem_sphere, dist_zero_right] using hw
    · exact hn
    · exact ball_subset_closedBall hz
theorem collision_of_locally_uniform_limit_and_factorizations
    {ι : Type*} [Fintype ι] {U : Set ℂ} (hU : IsOpen U)
    (ξ : ℕ → ι → ℂ) (k : ℕ) (H G : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    {r : ℝ} (hr : 0 < r) (hsub : closedBall (0 : ℂ) r ⊆ U)
    (hξlim : ∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0))
    (hH : ∀ n, DifferentiableOn ℂ (H n) U)
    (hlim : TendstoLocallyUniformlyOn H f atTop U)
    (hG : ∀ n, DifferentiableOn ℂ (G n) U)
    (hfactor : ∀ n, ∀ z ∈ U, H n z = (∏ i, (z - ξ n i) ^ k) * G n z) :
    (↑(k * Fintype.card ι) : ℕ∞) ≤ analyticOrderAt f 0 := by
  have hf : DifferentiableOn ℂ f U :=
    hlim.differentiableOn (Filter.Eventually.of_forall hH) hU
  have hsphere : sphere (0 : ℂ) r ⊆ U := sphere_subset_closedBall.trans hsub
  have hconv := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hlim
    (sphere (0 : ℂ) r) hsphere (isCompact_sphere _ _)
  obtain ⟨M, hM⟩ := eventual_uniform_bound_on_compact (sphere (0 : ℂ) r)
    (isCompact_sphere _ _) H f (hf.continuousOn.mono hsphere) hconv
  apply order_collision_of_holomorphic_factorization ξ k H G f hr hξlim
    (centers_eventually_half_disk ξ hξlim hr)
    (hf.mono (ball_subset_closedBall.trans hsub))
  · intro z hz
    exact hlim.tendsto_at (hsub (ball_subset_closedBall hz))
  · intro n
    exact (hG n).diffContOnCl_ball hsub
  · intro n z hz
    exact hfactor n z (hsub hz)
  · exact hM
end Nagata.W20
end
section
namespace Nagata.W20
open Filter Metric
open scoped Topology BigOperators
theorem holomorphic_collision_order {q : ℕ} {U : Set ℂ}
    (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (ξ : ℕ → Fin q → ℂ) (k : ℕ) (H : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hξlim : ∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0))
    (hξinj : ∀ n, Function.Injective (ξ n))
    (hξmem : ∀ n i, ξ n i ∈ U)
    (hH : ∀ n, DifferentiableOn ℂ (H n) U)
    (hlim : TendstoLocallyUniformlyOn H f atTop U)
    (horder : ∀ n i, (k : ℕ∞) ≤ analyticOrderAt (H n) (ξ n i)) :
    (↑(q * k) : ℕ∞) ≤ analyticOrderAt f 0 := by
  classical
  have hex := fun n => Nagata.W19.exists_holomorphic_factorization hU (H n)
    (hH n) (ξ n) (hξinj n) (hξmem n) k (horder n)
  let G : ℕ → ℂ → ℂ := fun n => Classical.choose (hex n)
  have hG : ∀ n, DifferentiableOn ℂ (G n) U :=
    fun n => (Classical.choose_spec (hex n)).1
  have hfactor : ∀ n, ∀ z ∈ U, H n z = (∏ i, (z - ξ n i) ^ k) * G n z :=
    fun n z _ => (Classical.choose_spec (hex n)).2 z
  obtain ⟨r, hr, hsub⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds h0)
  have hresult := collision_of_locally_uniform_limit_and_factorizations hU ξ k H G f
    hr hsub hξlim hH hlim hG hfactor
  simpa only [Fintype.card_fin, Nat.mul_comm] using hresult
theorem holomorphic_collision_jets {q : ℕ} {U : Set ℂ}
    (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (ξ : ℕ → Fin q → ℂ) (k : ℕ) (H : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hξlim : ∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0))
    (hξinj : ∀ n, Function.Injective (ξ n))
    (hξmem : ∀ n i, ξ n i ∈ U)
    (hH : ∀ n, DifferentiableOn ℂ (H n) U)
    (hlim : TendstoLocallyUniformlyOn H f atTop U)
    (horder : ∀ n i, (k : ℕ∞) ≤ analyticOrderAt (H n) (ξ n i)) :
    ∀ ℓ < q * k, iteratedDeriv ℓ f 0 = 0 := by
  have hf := hlim.differentiableOn (Filter.Eventually.of_forall hH) hU
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (hf.analyticAt (hU.mem_nhds h0))).mp
  exact holomorphic_collision_order hU h0 ξ k H f hξlim hξinj hξmem hH hlim horder
end Nagata.W20
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W19
open scoped Topology
open Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem directional_derivative_taylor_vanishing
    {H : E → ℂ} {p : E} (hH : AnalyticAt ℂ H p) (v : E) (m : ℕ)
    (hvan : ∀ n < m, iteratedFDeriv ℂ n H p = 0) :
    ∀ n, n + 1 < m →
      iteratedFDeriv ℂ n (fun z => fderiv ℂ H z v) p = 0 := by
  intro n hn
  have hz : iteratedFDeriv ℂ n (fderiv ℂ H) p = 0 := by
    apply norm_eq_zero.mp
    rw [norm_iteratedFDeriv_fderiv, hvan (n + 1) hn, norm_zero]
  change iteratedFDeriv ℂ n ((ContinuousLinearMap.apply ℂ ℂ v) ∘ fderiv ℂ H) p = 0
  rw [(ContinuousLinearMap.apply ℂ ℂ v).iteratedFDeriv_comp_left
    (hH.fderiv.contDiffAt (n := (n : WithTop ℕ∞))) le_rfl, hz]
  ext w
  simp
noncomputable def directionalIterate (v : E) : ℕ → (E → ℂ) → E → ℂ
  | 0, H => H
  | b + 1, H => directionalIterate v b (fun z => fderiv ℂ H z v)
theorem directionalIterate_analyticAt {H : E → ℂ} {p : E}
    (hH : AnalyticAt ℂ H p) (v : E) (b : ℕ) :
    AnalyticAt ℂ (directionalIterate v b H) p := by
  induction b generalizing H with
  | zero => exact hH
  | succ b ih =>
    apply ih
    exact ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp hH.fderiv
theorem directionalIterate_taylor_vanishing {H : E → ℂ} {p : E}
    (hH : AnalyticAt ℂ H p) (v : E) (m b : ℕ)
    (hvan : ∀ n < m, iteratedFDeriv ℂ n H p = 0) :
    ∀ n, n + b < m → iteratedFDeriv ℂ n (directionalIterate v b H) p = 0 := by
  induction b generalizing H m with
  | zero => simpa [directionalIterate] using hvan
  | succ b ih =>
    have ha : AnalyticAt ℂ (fun z => fderiv ℂ H z v) p :=
      ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp hH.fderiv
    have hv : ∀ n < m - 1, iteratedFDeriv ℂ n (fun z => fderiv ℂ H z v) p = 0 := by
      intro n hn
      exact directional_derivative_taylor_vanishing hH v m hvan n (by omega)
    intro n hn
    exact ih ha (m - 1) hv n (by omega)
theorem analytic_pullback_taylor_vanishing
    [CompleteSpace E]
    {H : E → ℂ} {p : ℂ} {γ : ℂ → E}
    (hH : AnalyticAt ℂ H (γ p)) (hγ : AnalyticAt ℂ γ p)
    (m : ℕ) (hvan : ∀ n < m, iteratedFDeriv ℂ n H (γ p) = 0) :
    ∀ n < m, iteratedFDeriv ℂ n (H ∘ γ) p = 0 := by
  intro n hn
  rw [iteratedFDeriv_comp (hH.contDiffAt (n := (n : WithTop ℕ∞)))
    (hγ.contDiffAt (n := (n : WithTop ℕ∞))) le_rfl]
  unfold FormalMultilinearSeries.taylorComp
  apply Finset.sum_eq_zero
  intro c _
  ext
  simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply, ftaylorSeries]
  rw [hvan c.length (lt_of_le_of_lt c.length_le hn)]
  simp
theorem transverse_restriction_order_of_total_taylor_vanishing
    {H : (ℂ × ℂ) → ℂ} (ξ : ℂ)
    (hH : AnalyticAt ℂ H (ξ, 0)) (m b : ℕ)
    (hvan : ∀ n < m, iteratedFDeriv ℂ n H (ξ, 0) = 0) :
    (m - b : ℕ) ≤ analyticOrderAt
      (fun x => directionalIterate (0, 1) b H (x, 0)) ξ := by
  let G := directionalIterate (0, 1) b H
  have hG : AnalyticAt ℂ G (ξ, 0) := directionalIterate_analyticAt hH (0, 1) b
  have hγ : AnalyticAt ℂ (fun x : ℂ => (x, (0 : ℂ))) ξ := by fun_prop
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hG.comp (f := fun x : ℂ => (x, (0 : ℂ))) (x := ξ) hγ)).mpr
  intro n hn
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have hv : ∀ j < m - b, iteratedFDeriv ℂ j G (ξ, 0) = 0 := by
    intro j hj
    exact directionalIterate_taylor_vanishing hH (0, 1) m b hvan j (by omega)
  have hz := analytic_pullback_taylor_vanishing (γ := fun x : ℂ => (x, (0 : ℂ))) (p := ξ) hG hγ (m - b) hv n hn
  simpa only [Function.comp_def, zero_apply] using congrArg (fun L => L (fun _ => (1 : ℂ))) hz
theorem directionalIterate_vertical_eq_iteratedDeriv
    {H : (ℂ × ℂ) → ℂ} {x y : ℂ} (hH : AnalyticAt ℂ H (x, y)) (b : ℕ) :
    directionalIterate (0, 1) b H (x, y) =
      iteratedDeriv b (fun t => H (x, t)) y := by
  induction b generalizing H with
  | zero => simp [directionalIterate]
  | succ b ih =>
    let G : (ℂ × ℂ) → ℂ := fun z => fderiv ℂ H z (0, 1)
    have hG : AnalyticAt ℂ G (x, y) := by
      change AnalyticAt ℂ ((ContinuousLinearMap.apply ℂ ℂ ((0, 1) : ℂ × ℂ)) ∘
        fderiv ℂ H) (x, y)
      exact ((ContinuousLinearMap.apply ℂ ℂ ((0, 1) : ℂ × ℂ)).analyticAt _).comp hH.fderiv
    have hc : ContinuousAt (fun t : ℂ => (x, t)) y := by fun_prop
    have hev : ∀ᶠ t in 𝓝 y, AnalyticAt ℂ H (x, t) :=
      hc.tendsto.eventually hH.eventually_analyticAt
    have heq : (fun t => deriv (fun u => H (x, u)) t) =ᶠ[𝓝 y]
        (fun t => G (x, t)) := by
      filter_upwards [hev] with t ht
      have hline : HasDerivAt (fun u : ℂ => (x, u)) (0, 1) t :=
        by simpa using ((hasFDerivAt_const (𝕜 := ℂ) x t).prodMk
          (hasFDerivAt_id t)).hasDerivAt
      exact (ht.differentiableAt.hasFDerivAt.comp_hasDerivAt t hline).deriv
    change directionalIterate (0, 1) b G (x, y) = _
    rw [ih hG, iteratedDeriv_succ']
    exact (Filter.EventuallyEq.iteratedDeriv_eq b heq).symm
theorem transverse_iteratedDeriv_order_of_total_taylor_vanishing
    {H : (ℂ × ℂ) → ℂ} (ξ : ℂ)
    (hH : AnalyticAt ℂ H (ξ, 0)) (m b : ℕ)
    (hvan : ∀ n < m, iteratedFDeriv ℂ n H (ξ, 0) = 0) :
    (m - b : ℕ) ≤ analyticOrderAt
      (fun x => iteratedDeriv b (fun y => H (x, y)) 0) ξ := by
  have hc : ContinuousAt (fun x : ℂ => (x, (0 : ℂ))) ξ := by fun_prop
  have hev : ∀ᶠ x in 𝓝 ξ, AnalyticAt ℂ H (x, 0) :=
    hc.tendsto.eventually hH.eventually_analyticAt
  have heq : (fun x => directionalIterate (0, 1) b H (x, 0)) =ᶠ[𝓝 ξ]
      (fun x => iteratedDeriv b (fun y => H (x, y)) 0) := by
    filter_upwards [hev] with x hx
    exact directionalIterate_vertical_eq_iteratedDeriv hx b
  rw [← analyticOrderAt_congr heq]
  exact transverse_restriction_order_of_total_taylor_vanishing ξ hH m b hvan
end Nagata.W19
end
section
namespace Nagata.W19
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
private theorem derivSeries_coeff_zero
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (P : FormalMultilinearSeries ℂ E F) (n : ℕ) (hzero : P (n + 1) = 0) :
    P.derivSeries n = 0 := by
  have hz' : ∀ j, j = n + 1 → P j = 0 := by
    intro j hj
    subst j
    exact hzero
  have hz : P (1 + n) = 0 := hz' (1 + n) (Nat.add_comm 1 n)
  ext v w
  simp [FormalMultilinearSeries.derivSeries,
    ContinuousLinearMap.compFormalMultilinearSeries_apply,
    FormalMultilinearSeries.changeOriginSeries,
    FormalMultilinearSeries.changeOriginSeriesTerm, hz]
private theorem iteratedFDeriv_zero_of_series_coeff (n : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
      {H : E → F} {p : E} {P : FormalMultilinearSeries ℂ E F},
      HasFPowerSeriesAt H P p → P n = 0 → iteratedFDeriv ℂ n H p = 0 := by
  induction n with
  | zero =>
    intro F _ _ _ H p P hP hzero
    ext v
    simpa [hzero] using (hP.coeff_zero v).symm
  | succ n ih =>
    intro F _ _ _ H p P hP hzero
    obtain ⟨r, hr⟩ := hP
    have hd : P.derivSeries n = 0 := derivSeries_coeff_zero P n hzero
    have hi := ih (F := E →L[ℂ] F) hr.fderiv.hasFPowerSeriesAt hd
    apply norm_eq_zero.mp
    rw [← norm_iteratedFDeriv_fderiv, hi, norm_zero]
theorem total_taylor_vanishing_of_powerSeries
    {H : E → ℂ} {p : E} {P : FormalMultilinearSeries ℂ E ℂ}
    (hP : HasFPowerSeriesAt H P p) (m : ℕ) (hzero : ∀ n < m, P n = 0) :
    ∀ n < m, iteratedFDeriv ℂ n H p = 0 := by
  intro n hn
  exact iteratedFDeriv_zero_of_series_coeff n hP (hzero n hn)
theorem transverse_iteratedDeriv_order_of_powerSeries
    {H : (ℂ × ℂ) → ℂ} {P : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ}
    (ξ : ℂ) (hP : HasFPowerSeriesAt H P (ξ, 0))
    (m b : ℕ) (hzero : ∀ n < m, P n = 0) :
    (m - b : ℕ) ≤ analyticOrderAt
      (fun x => iteratedDeriv b (fun y => H (x, y)) 0) ξ := by
  apply transverse_iteratedDeriv_order_of_total_taylor_vanishing ξ ⟨P, hP⟩ m b
  exact total_taylor_vanishing_of_powerSeries hP m hzero
end Nagata.W19
end
section
namespace Nagata.W19
open scoped Topology
open Filter
end Nagata.W19
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W20
open scoped Topology BigOperators
open Nagata.CoefficientSpaces
noncomputable section
abbrev ActualSection (τ γL γP : ℂ) (d : ℤ) (m : ℕ) (P : ℂ → ℂ) :=
  polynomialSections τ γL γP d (m : ℤ) P
def localScalar {τ γL γP : ℂ} {d : ℤ} {m : ℕ} {P : ℂ → ℂ}
    (F : ActualSection τ γL γP d m P) (z₀ x y : ℂ) : ℂ :=
  scalarExpression F.val (z₀ * Complex.exp x) (Complex.exp y)
def actualTransverse {τ γL γP : ℂ} {d : ℤ} {m : ℕ} {P : ℂ → ℂ}
    (F : ActualSection τ γL γP d m P) (z₀ : ℂ) (b : ℕ) (x : ℂ) : ℂ :=
  ∑ j ∈ Finset.range ((d / 3).toNat + 1),
    F.val.coeff j (z₀ * Complex.exp x) * (j : ℂ) ^ b
theorem scalarExpression_eq_sum_range {τ γL γP : ℂ} {d : ℤ} {m : ℕ}
    {P : ℂ → ℂ} (F : ActualSection τ γL γP d m P) (z v : ℂ) :
    scalarExpression F.val z v =
      ∑ j ∈ Finset.range ((d / 3).toNat + 1), F.val.coeff j z * v ^ j := by
  unfold scalarExpression
  apply Polynomial.sum_eq_of_subset (p := F.val) (fun (j : ℕ) (f : ℂ → ℂ) => f z * v ^ j)
  · intro j
    simp
  · intro j hj
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    by_contra hn
    exact (Polynomial.mem_support_iff.mp hj) (F.property.1 j (Nat.lt_of_not_ge hn))
theorem localScalar_eq_sum_exp {τ γL γP : ℂ} {d : ℤ} {m : ℕ}
    {P : ℂ → ℂ} (F : ActualSection τ γL γP d m P) (z₀ x y : ℂ) :
    localScalar F z₀ x y =
      ∑ j ∈ Finset.range ((d / 3).toNat + 1),
        F.val.coeff j (z₀ * Complex.exp x) * Complex.exp ((j : ℂ) * y) := by
  rw [localScalar, scalarExpression_eq_sum_range]
  simp only [Complex.exp_nat_mul]
theorem actualTransverse_eq_derivative {τ γL γP : ℂ} {d : ℤ} {m : ℕ}
    {P : ℂ → ℂ} (F : ActualSection τ γL γP d m P) (z₀ x : ℂ) (b : ℕ) :
    actualTransverse F z₀ b x = iteratedDeriv b (fun y => localScalar F z₀ x y) 0 := by
  have hfun : (fun y => localScalar F z₀ x y) =
      fun y => ∑ j ∈ Finset.range ((d / 3).toNat + 1),
        F.val.coeff j (z₀ * Complex.exp x) * Complex.exp ((j : ℂ) * y) :=
    funext (fun y => localScalar_eq_sum_exp F z₀ x y)
  rw [hfun]
  have hcd : ∀ j ∈ Finset.range ((d / 3).toNat + 1),
      ContDiffAt ℂ b (fun y => F.val.coeff j (z₀ * Complex.exp x) *
        Complex.exp ((j : ℂ) * y)) 0 := by
    intro j _
    fun_prop
  rw [iteratedDeriv_fun_sum hcd]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_cexp_const_mul,
    mul_zero, Complex.exp_zero, mul_one, actualTransverse]
theorem logarithmicCoefficient_differentiable {τ γL γP : ℂ} {d : ℤ} {m : ℕ}
    {P : ℂ → ℂ} (F : ActualSection τ γL γP d m P)
    (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) (j : ℕ) :
    Differentiable ℂ (fun x => F.val.coeff j (z₀ * Complex.exp x)) := by
  intro x
  apply (coefficientSpace_differentiableAt hP (F.property.2 j)
    (mul_ne_zero hz₀ (Complex.exp_ne_zero x))).comp x
  exact Complex.differentiableAt_exp.const_mul z₀
theorem actualTransverse_differentiable {τ γL γP : ℂ} {d : ℤ} {m : ℕ}
    {P : ℂ → ℂ} (F : ActualSection τ γL γP d m P)
    (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) (b : ℕ) :
    Differentiable ℂ (actualTransverse F z₀ b) := by
  apply Differentiable.fun_sum
  intro j _
  exact (logarithmicCoefficient_differentiable F hP hz₀ j).mul_const ((j : ℂ) ^ b)
@[simp] theorem actualTransverse_add {τ γL γP : ℂ} {d : ℤ} {m : ℕ}
    {P : ℂ → ℂ} (F G : ActualSection τ γL γP d m P) (z₀ x : ℂ) (b : ℕ) :
    actualTransverse (F + G) z₀ b x =
      actualTransverse F z₀ b x + actualTransverse G z₀ b x := by
  simp only [actualTransverse, Submodule.coe_add, Polynomial.coeff_add,
    Pi.add_apply, add_mul, Finset.sum_add_distrib]
@[simp] theorem actualTransverse_smul {τ γL γP : ℂ} {d : ℤ} {m : ℕ}
    {P : ℂ → ℂ} (F : ActualSection τ γL γP d m P) (a z₀ x : ℂ) (b : ℕ) :
    actualTransverse (a • F) z₀ b x = a * actualTransverse F z₀ b x := by
  simp only [actualTransverse, Submodule.coe_smul, Polynomial.coeff_smul,
    Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]
def actualTransverseLinear {τ γL γP : ℂ} {d : ℤ} {m : ℕ} {P : ℂ → ℂ}
    (z₀ : ℂ) (b : ℕ) : ActualSection τ γL γP d m P →ₗ[ℂ] (ℂ → ℂ) where
  toFun F := actualTransverse F z₀ b
  map_add' F G := funext (fun x => actualTransverse_add F G z₀ x b)
  map_smul' a F := funext (fun x => actualTransverse_smul F a z₀ x b)
end
end Nagata.W20
end
section
namespace Nagata.W20
open scoped Topology BigOperators
open Nagata.CoefficientSpaces
noncomputable section
def actualJetMap {τ γL γP : ℂ} {d : ℤ} {m : ℕ} {P : ℂ → ℂ}
    (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z) {z₀ : ℂ} (hz₀ : z₀ ≠ 0) (q : ℕ) :
    ActualSection τ γL γP d m P →ₗ[ℂ] (Nagata.Workers.W30.JetIndex q m → ℂ) where
  toFun F row := iteratedDeriv row.2.val (actualTransverse F z₀ row.1.val) 0
  map_add' F G := by
    funext row
    have hfun : actualTransverse (F + G) z₀ row.1.val =
        actualTransverse F z₀ row.1.val + actualTransverse G z₀ row.1.val :=
      funext (fun x => actualTransverse_add F G z₀ x row.1.val)
    rw [hfun, iteratedDeriv_add
      ((actualTransverse_differentiable F hP hz₀ row.1.val).analyticAt 0).contDiffAt
      ((actualTransverse_differentiable G hP hz₀ row.1.val).analyticAt 0).contDiffAt]
    rfl
  map_smul' a F := by
    funext row
    have hfun : actualTransverse (a • F) z₀ row.1.val =
        fun x => a * actualTransverse F z₀ row.1.val x :=
      funext (fun x => actualTransverse_smul F a z₀ x row.1.val)
    rw [hfun, iteratedDeriv_const_mul_field]
    rfl
theorem actualJetMap_apply_eq_mixed_derivative {τ γL γP : ℂ} {d : ℤ} {m : ℕ}
    {P : ℂ → ℂ} (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) {q : ℕ}
    (F : ActualSection τ γL γP d m P) (row : Nagata.Workers.W30.JetIndex q m) :
    actualJetMap hP hz₀ q F row =
      iteratedDeriv row.2.val (fun x =>
        iteratedDeriv row.1.val (fun y => localScalar F z₀ x y) 0) 0 := by
  change iteratedDeriv row.2.val (actualTransverse F z₀ row.1.val) 0 = _
  apply congrArg (fun f : ℂ → ℂ => iteratedDeriv row.2.val f 0)
  exact funext (fun x => actualTransverse_eq_derivative F z₀ x row.1.val)
end
end Nagata.W20
end
section
namespace Nagata.W20
open Filter Metric
open scoped Topology BigOperators
noncomputable section
def transverseExpression {ι : Type*} [Fintype ι] {m : ℕ}
    (basis : ι → Fin m → ℂ → ℂ) (c : ι → ℂ) (b : Fin m) (z : ℂ) : ℂ :=
  ∑ i, c i * basis i b z
@[simp] theorem transverseExpression_smul {ι : Type*} [Fintype ι] {m : ℕ}
    (basis : ι → Fin m → ℂ → ℂ) (c : ι → ℂ) (a : ℂ) (b : Fin m) (z : ℂ) :
    transverseExpression basis (a • c) b z = a * transverseExpression basis c b z := by
  simp only [transverseExpression, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]
theorem transverseExpression_differentiableOn {ι : Type*} [Fintype ι]
    {m : ℕ} {U : Set ℂ} (basis : ι → Fin m → ℂ → ℂ)
    (hbasis : ∀ i b, DifferentiableOn ℂ (basis i b) U)
    (c : ι → ℂ) (b : Fin m) :
    DifferentiableOn ℂ (transverseExpression basis c b) U := by
  apply DifferentiableOn.fun_sum
  intro i _
  exact (hbasis i b).const_mul (c i)
def coefficientJetMap {ι : Type*} [Fintype ι] (q m : ℕ)
    (basis : ι → Fin m → ℂ → ℂ) :
    (ι → ℂ) →ₗ[ℂ] (Nagata.Workers.W30.JetIndex q m → ℂ) where
  toFun c row := ∑ i, c i * iteratedDeriv row.2.val (basis i row.1) 0
  map_add' c d := by
    funext row
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    funext row
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum, RingHom.id_apply]
theorem coefficientJetMap_apply_eq_derivative {ι : Type*} [Fintype ι]
    {q m : ℕ} {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (basis : ι → Fin m → ℂ → ℂ)
    (hbasis : ∀ i b, DifferentiableOn ℂ (basis i b) U)
    (c : ι → ℂ) (row : Nagata.Workers.W30.JetIndex q m) :
    coefficientJetMap q m basis c row =
      iteratedDeriv row.2.val (transverseExpression basis c row.1) 0 := by
  classical
  change (∑ i, c i * iteratedDeriv row.2.val (basis i row.1) 0) = _
  symm
  unfold transverseExpression
  have hcd : ∀ i ∈ (Finset.univ : Finset ι),
      ContDiffAt ℂ row.2.val (fun z => c i * basis i row.1 z) 0 := by
    intro i _
    have ha : AnalyticAt ℂ (fun z => c i * basis i row.1 z) 0 :=
      analyticAt_const.mul ((hbasis i row.1).analyticAt (hU.mem_nhds h0))
    exact ha.contDiffAt
  rw [iteratedDeriv_fun_sum hcd]
  simp only [iteratedDeriv_const_mul_field]
theorem nonzero_collision_jet_kernel {ι : Type*} [Fintype ι]
    {q m : ℕ} {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (basis : ι → Fin m → ℂ → ℂ)
    (hbasis : ∀ i b, DifferentiableOn ℂ (basis i b) U)
    (c : ℕ → ι → ℂ) (hcnorm : ∀ n, ‖c n‖ = 1)
    (ξ : ℕ → Fin q → ℂ)
    (hξlim : ∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0))
    (hξinj : ∀ n, Function.Injective (ξ n))
    (hξmem : ∀ n i, ξ n i ∈ U)
    (horder : ∀ n (b : Fin m) i, (↑(m - b.val) : ℕ∞) ≤
      analyticOrderAt (transverseExpression basis (c n) b) (ξ n i)) :
    ∃ c₀ : ι → ℂ, ‖c₀‖ = 1 ∧ c₀ ≠ 0 ∧ coefficientJetMap q m basis c₀ = 0 := by
  classical
  obtain ⟨c₀, hc₀norm, hc₀ne, φ, hφ, hcφ⟩ := unit_subsequence c hcnorm
  have hcoord : ∀ i, Tendsto (fun n => c (φ n) i) atTop (𝓝 (c₀ i)) := by
    intro i
    exact ((continuous_apply i).tendsto c₀).comp hcφ
  have hroot : ∀ i, Tendsto (fun n => ξ (φ n) i) atTop (𝓝 0) :=
    fun i => (hξlim i).comp hφ.tendsto_atTop
  refine ⟨c₀, hc₀norm, hc₀ne, ?_⟩
  funext row
  rw [coefficientJetMap_apply_eq_derivative hU h0 basis hbasis]
  have hhol : ∀ n, DifferentiableOn ℂ
      (transverseExpression basis (c (φ n)) row.1) U := by
    intro n
    apply DifferentiableOn.fun_sum
    intro i _
    exact (hbasis i row.1).const_mul (c (φ n) i)
  have hconv := locally_uniform_linear_combination hU (fun i => basis i row.1)
    (fun i => (hbasis i row.1).continuousOn) (fun n => c (φ n)) c₀ hcoord
  exact holomorphic_collision_jets hU h0 (fun n => ξ (φ n)) (m - row.1.val)
    (fun n => transverseExpression basis (c (φ n)) row.1)
    (transverseExpression basis c₀ row.1) hroot (fun n => hξinj (φ n))
    (fun n => hξmem (φ n)) hhol hconv (fun n => horder (φ n) row.1)
    row.2.val row.2.isLt
theorem nonzero_collision_jet_kernel_of_nonzero {ι : Type*} [Fintype ι]
    {q m : ℕ} {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (basis : ι → Fin m → ℂ → ℂ)
    (hbasis : ∀ i b, DifferentiableOn ℂ (basis i b) U)
    (c : ℕ → ι → ℂ) (hc : ∀ n, c n ≠ 0)
    (ξ : ℕ → Fin q → ℂ)
    (hξlim : ∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0))
    (hξinj : ∀ n, Function.Injective (ξ n))
    (hξmem : ∀ n i, ξ n i ∈ U)
    (horder : ∀ n (b : Fin m) i, (↑(m - b.val) : ℕ∞) ≤
      analyticOrderAt (transverseExpression basis (c n) b) (ξ n i)) :
    ∃ c₀ : ι → ℂ, ‖c₀‖ = 1 ∧ c₀ ≠ 0 ∧ coefficientJetMap q m basis c₀ = 0 := by
  let normalized : ℕ → ι → ℂ := fun n => (‖c n‖⁻¹ : ℂ) • c n
  have hnorm : ∀ n, ‖normalized n‖ = 1 :=
    fun n => norm_smul_inv_norm (𝕜 := ℂ) (hc n)
  apply nonzero_collision_jet_kernel hU h0 basis hbasis normalized hnorm ξ
    hξlim hξinj hξmem
  intro n b i
  have ha := (transverseExpression_differentiableOn basis hbasis (c n) b).analyticAt
    (hU.mem_nhds (hξmem n i))
  have hfun : transverseExpression basis (normalized n) b =
      (fun _ => (‖c n‖⁻¹ : ℂ)) * transverseExpression basis (c n) b := by
    funext z
    exact transverseExpression_smul basis (c n) (‖c n‖⁻¹ : ℂ) b z
  rw [hfun, analyticOrderAt_mul analyticAt_const ha]
  exact (horder n b i).trans (le_add_of_nonneg_left zero_le)
end
end Nagata.W20
end
section
namespace Nagata.W20
open scoped Topology BigOperators
open Filter Module
noncomputable section
theorem actualTransverse_basis_repr {ι : Type*} [Fintype ι]
    {τ γL γP : ℂ} {d : ℤ} {m : ℕ} {P : ℂ → ℂ}
    (B : Basis ι ℂ (ActualSection τ γL γP d m P))
    (F : ActualSection τ γL γP d m P) (z₀ : ℂ) (b : Fin m) (x : ℂ) :
    transverseExpression (fun i b => actualTransverse (B i) z₀ b.val)
      (fun i => B.repr F i) b x = actualTransverse F z₀ b.val x := by
  have h := congrArg (fun G => actualTransverseLinear z₀ b.val G x) (B.sum_repr F)
  simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    transverseExpression, actualTransverseLinear, LinearMap.coe_mk, AddHom.coe_mk] using h
theorem actual_nonzero_collision_kernel {ι : Type*} [Fintype ι]
    {τ γL γP : ℂ} {d : ℤ} {m q : ℕ} {P : ℂ → ℂ}
    (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (B : Basis ι ℂ (ActualSection τ γL γP d m P))
    (F : ℕ → ActualSection τ γL γP d m P) (hF : ∀ n, F n ≠ 0)
    {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (ξ : ℕ → Fin q → ℂ)
    (hξlim : ∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0))
    (hξinj : ∀ n, Function.Injective (ξ n))
    (hξmem : ∀ n i, ξ n i ∈ U)
    (horder : ∀ n (b : Fin m) i, (↑(m - b.val) : ℕ∞) ≤
      analyticOrderAt (actualTransverse (F n) z₀ b.val) (ξ n i)) :
    ∃ F₀ : ActualSection τ γL γP d m P,
      F₀ ≠ 0 ∧ actualJetMap hP hz₀ q F₀ = 0 := by
  classical
  let c : ℕ → ι → ℂ := fun n i => B.repr (F n) i
  have hc : ∀ n, c n ≠ 0 := by
    intro n hn
    apply hF n
    apply B.repr.injective
    have hz : B.repr (F n) = 0 := Finsupp.ext (fun i => congrFun hn i)
    simpa only [map_zero] using hz
  let basis : ι → Fin m → ℂ → ℂ := fun i b => actualTransverse (B i) z₀ b.val
  have hbasis : ∀ i b, DifferentiableOn ℂ (basis i b) U :=
    fun i b => (actualTransverse_differentiable (B i) hP hz₀ b.val).differentiableOn
  have hord : ∀ n (b : Fin m) i, (↑(m - b.val) : ℕ∞) ≤
      analyticOrderAt (transverseExpression basis (c n) b) (ξ n i) := by
    intro n b i
    have heq : transverseExpression basis (c n) b = actualTransverse (F n) z₀ b.val :=
      funext (fun x => actualTransverse_basis_repr B (F n) z₀ b x)
    rw [heq]
    exact horder n b i
  obtain ⟨c₀, _, hc₀, hker⟩ := nonzero_collision_jet_kernel_of_nonzero hU h0 basis
    hbasis c hc ξ hξlim hξinj hξmem hord
  let F₀ : ActualSection τ γL γP d m P := ∑ i, c₀ i • B i
  have hF₀ : F₀ ≠ 0 := by
    intro hz
    apply hc₀
    funext i
    have hi := congrArg (fun G => B.repr G i) hz
    simpa [F₀, map_sum, map_smul, Finsupp.single_apply] using hi
  refine ⟨F₀, hF₀, ?_⟩
  have hjet : actualJetMap hP hz₀ q F₀ = coefficientJetMap q m basis c₀ := by
    ext row
    change actualJetMap hP hz₀ q (∑ i, c₀ i • B i) row = _
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  exact hjet.trans hker
theorem actual_kernel_from_local_powerSeries {ι : Type*} [Fintype ι]
    {τ γL γP : ℂ} {d : ℤ} {m q : ℕ} {P : ℂ → ℂ}
    (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (B : Basis ι ℂ (ActualSection τ γL γP d m P))
    (F : ℕ → ActualSection τ γL γP d m P) (hF : ∀ n, F n ≠ 0)
    {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (ξ : ℕ → Fin q → ℂ)
    (hξlim : ∀ i, Tendsto (fun n => ξ n i) atTop (𝓝 0))
    (hξinj : ∀ n, Function.Injective (ξ n))
    (hξmem : ∀ n i, ξ n i ∈ U)
    (S : ℕ → Fin q → FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    (hS : ∀ n i, HasFPowerSeriesAt (fun p : ℂ × ℂ => localScalar (F n) z₀ p.1 p.2)
      (S n i) (ξ n i, 0))
    (hzero : ∀ n i j, j < m → S n i j = 0) :
    ∃ F₀ : ActualSection τ γL γP d m P,
      F₀ ≠ 0 ∧ actualJetMap hP hz₀ q F₀ = 0 := by
  apply actual_nonzero_collision_kernel hP hz₀ B F hF hU h0 ξ hξlim hξinj hξmem
  intro n b i
  have heq : actualTransverse (F n) z₀ b.val =
      fun x => iteratedDeriv b.val (fun y => localScalar (F n) z₀ x y) 0 :=
    funext (fun x => actualTransverse_eq_derivative (F n) z₀ x b.val)
  rw [heq]
  exact Nagata.W19.transverse_iteratedDeriv_order_of_powerSeries
    (ξ n i) (hS n i) m b.val (hzero n i)
end
end Nagata.W20
end
section
namespace Nagata.W20
open scoped Topology
open Filter Module
theorem actual_kernel_of_every_configuration {ι : Type*} [Fintype ι]
    {τ γL γP : ℂ} {d : ℤ} {m q : ℕ} {P : ℂ → ℂ}
    (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (B : Basis ι ℂ (ActualSection τ γL γP d m P))
    {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (hEvery : ∀ p : Fin q → ℂ, Function.Injective p → (∀ i, p i ∈ U) →
      ∃ F : ActualSection τ γL γP d m P, F ≠ 0 ∧
        ∀ i, Nagata.Workers.W28.HasAnalyticOrderAtLeast (𝕜 := ℂ)
          (fun x : ℂ × ℂ => localScalar F z₀ x.1 x.2) (p i, 0) m) :
    ∃ F₀ : ActualSection τ γL γP d m P,
      F₀ ≠ 0 ∧ actualJetMap hP hz₀ q F₀ = 0 := by
  obtain ⟨ξ, hξinj, hξmem, hξlim⟩ := exists_collision_centers hU h0 q
  have he : ∀ n, ∃ F : ActualSection τ γL γP d m P, F ≠ 0 ∧
      ∀ i, Nagata.Workers.W28.HasAnalyticOrderAtLeast (𝕜 := ℂ)
        (fun x : ℂ × ℂ => localScalar F z₀ x.1 x.2) (ξ n i, 0) m :=
    fun n => hEvery (ξ n) (hξinj n) (hξmem n)
  choose F hF hTaylor using he
  choose S hS hzero using hTaylor
  exact actual_kernel_from_local_powerSeries hP hz₀ B F hF hU h0 ξ
    hξlim hξinj hξmem S hS hzero
end Nagata.W20
end
section
namespace Nagata.W20
open scoped Topology
open Filter Module
end Nagata.W20
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W09
open Complex Real Metric
open scoped Topology
noncomputable def analyticLaurentCoeff (r : ℝ) (f : ℂ → ℂ) (k : ℤ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∮ z in C(0, r), z ^ (-k - 1) * f z
theorem differentiableAt_laurentIntegrand {f : ℂ → ℂ}
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z) (k : ℤ) {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ (fun w => w ^ (-k - 1) * f w) z :=
  (differentiableAt_zpow.mpr (Or.inl hz)).mul (hf z hz)
theorem circleIntegrable_laurentIntegrand {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z) (k : ℤ) :
    CircleIntegrable (fun z => z ^ (-k - 1) * f z) 0 r := by
  apply ContinuousOn.circleIntegrable hr.le
  intro z hz
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    exact hr.ne (by simpa [Metric.mem_sphere] using hz)
  exact (differentiableAt_laurentIntegrand hf k hz0).continuousAt.continuousWithinAt
theorem analyticLaurentCoeff_add {r : ℝ} (hr : 0 < r) {f g : ℂ → ℂ}
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z)
    (hg : ∀ z, z ≠ 0 → DifferentiableAt ℂ g z) (k : ℤ) :
    analyticLaurentCoeff r (f + g) k = analyticLaurentCoeff r f k + analyticLaurentCoeff r g k := by
  unfold analyticLaurentCoeff
  simp only [Pi.add_apply, mul_add]
  rw [circleIntegral.integral_add (circleIntegrable_laurentIntegrand hr hf k)
    (circleIntegrable_laurentIntegrand hr hg k), mul_add]
theorem analyticLaurentCoeff_smul (r : ℝ) (a : ℂ) (f : ℂ → ℂ) (k : ℤ) :
    analyticLaurentCoeff r (a • f) k = a * analyticLaurentCoeff r f k := by
  unfold analyticLaurentCoeff
  simp only [Pi.smul_apply, smul_eq_mul]
  have heq : (fun z : ℂ => z ^ (-k - 1) * (a * f z)) =
      (fun z => a * (z ^ (-k - 1) * f z)) := by
    funext z
    ring
  rw [heq, circleIntegral.integral_const_mul]
  ring
noncomputable def laurentCoefficientMap (τ : ℂ) (n : ℤ) (γ : ℂ) :
    Nagata.W08.automorphicSections τ n γ →ₗ[ℂ] (ℤ → ℂ) where
  toFun f k := analyticLaurentCoeff 1 f.val k
  map_add' f g := by
    funext k
    exact analyticLaurentCoeff_add zero_lt_one f.property.2.1 g.property.2.1 k
  map_smul' a f := by
    funext k
    exact analyticLaurentCoeff_smul 1 a f.val k
end Nagata.W09
end
section
namespace Nagata.W09
open Complex Metric MeasureTheory Filter
open scoped Topology
theorem hasSum_circleIntegral_of_summable_bound
    {ι : Type*} [Countable ι] {r : ℝ} (hr : 0 < r)
    (F : ι → ℂ → ℂ) (f : ℂ → ℂ) (B : ι → ℝ)
    (hB : Summable B)
    (hcont : ∀ i, ContinuousOn (F i) (sphere 0 r))
    (hbound : ∀ i z, z ∈ sphere 0 r → ‖F i z‖ ≤ B i)
    (hsum : ∀ z, z ∈ sphere 0 r → HasSum (fun i => F i z) (f z)) :
    HasSum (fun i => ∮ z in C(0, r), F i z) (∮ z in C(0, r), f z) := by
  unfold circleIntegral
  apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun i _ => r * B i)
  · intro i
    exact ((hcont i).circleIntegrable hr.le).out.aestronglyMeasurable_restrict_uIoc
  · intro i
    exact ae_of_all _ fun θ _ => by
      simp only [norm_smul, deriv_circleMap, norm_mul, Complex.norm_I,
        mul_one, norm_circleMap_zero, abs_of_pos hr]
      exact mul_le_mul_of_nonneg_left (hbound i _ (circleMap_mem_sphere 0 hr.le θ)) hr.le
  · exact ae_of_all _ fun _ _ => hB.mul_left r
  · exact intervalIntegrable_const
  · exact ae_of_all _ fun θ _ =>
      (hsum _ (circleMap_mem_sphere 0 hr.le θ)).const_smul _
theorem hasSum_analyticLaurentCoeff_of_summable_bound
    {ι : Type*} [Countable ι] {r : ℝ} (hr : 0 < r)
    (F : ι → ℂ → ℂ) (f : ℂ → ℂ) (k : ℤ) (B : ι → ℝ)
    (hB : Summable B)
    (hcont : ∀ i, ContinuousOn (F i) (sphere 0 r))
    (hbound : ∀ i z, z ∈ sphere 0 r → ‖z ^ (-k - 1) * F i z‖ ≤ B i)
    (hsum : ∀ z, z ∈ sphere 0 r → HasSum (fun i => F i z) (f z)) :
    HasSum (fun i => analyticLaurentCoeff r (F i) k) (analyticLaurentCoeff r f k) := by
  have hpow : ContinuousOn (fun z : ℂ => z ^ (-k - 1)) (sphere 0 r) := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      subst z
      exact hr.ne (by simpa [Metric.mem_sphere] using hz)
    exact (differentiableAt_zpow.mpr (Or.inl hz0)).continuousAt.continuousWithinAt
  exact (hasSum_circleIntegral_of_summable_bound hr
    (fun i z => z ^ (-k - 1) * F i z) (fun z => z ^ (-k - 1) * f z) B hB
    (fun i => hpow.mul (hcont i)) hbound
    (fun z hz => (hsum z hz).mul_left _)).mul_left _
theorem hasSum_analyticLaurentCoeff_of_bound
    {ι : Type*} [Countable ι] {r : ℝ} (hr : 0 < r)
    (F : ι → ℂ → ℂ) (f : ℂ → ℂ) (k : ℤ) (B : ι → ℝ)
    (hB : Summable B)
    (hcont : ∀ i, ContinuousOn (F i) (sphere 0 r))
    (hbound : ∀ i z, z ∈ sphere 0 r → ‖F i z‖ ≤ B i)
    (hsum : ∀ z, z ∈ sphere 0 r → HasSum (fun i => F i z) (f z)) :
    HasSum (fun i => analyticLaurentCoeff r (F i) k) (analyticLaurentCoeff r f k) := by
  apply hasSum_analyticLaurentCoeff_of_summable_bound hr F f k
    (fun i => r ^ (-k - 1) * B i) (hB.mul_left _) hcont
  · intro i z hz
    have hnorm : ‖z‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
    rw [norm_mul, norm_zpow, hnorm]
    exact mul_le_mul_of_nonneg_left (hbound i z hz) (zpow_pos hr _).le
  · exact hsum
theorem exists_circle_angle_of_mem_sphere {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : z ∈ sphere 0 r) :
    ∃ θ ∈ Set.Ioc (0 : ℝ) (2 * Real.pi), circleMap 0 r θ = z := by
  have hmem : z ∈ circleMap 0 r '' Set.Ioc (0 : ℝ) (2 * Real.pi) := by
    rw [image_circleMap_Ioc, abs_of_pos hr]
    exact hz
  exact hmem
end Nagata.W09
end
section
namespace Nagata.W09
open Complex Real Metric
theorem analyticLaurentCoeff_congr {r : ℝ} (hr : 0 ≤ r) {f g : ℂ → ℂ}
    (h : Set.EqOn f g (Metric.sphere 0 r)) (k : ℤ) :
    analyticLaurentCoeff r f k = analyticLaurentCoeff r g k := by
  unfold analyticLaurentCoeff
  congr 1
  apply circleIntegral.integral_congr hr
  intro z hz
  dsimp only
  rw [h hz]
theorem circleIntegral_scale_real (a r : ℝ) (f : ℂ → ℂ) :
    (∮ z in C(0, a * r), f z) =
      (a : ℂ) * ∮ z in C(0, r), f ((a : ℂ) * z) := by
  unfold circleIntegral
  calc
    _ = ∫ θ in (0 : ℝ)..2 * Real.pi,
        (a : ℂ) * (deriv (circleMap 0 r) θ * f ((a : ℂ) * circleMap 0 r θ)) := by
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [deriv_circleMap, circleMap, zero_add,
        Complex.ofReal_mul, smul_eq_mul, mul_assoc]
    _ = _ := by
      simpa only [smul_eq_mul] using intervalIntegral.integral_const_mul (a : ℂ)
        (fun θ => deriv (circleMap 0 r) θ * f ((a : ℂ) * circleMap 0 r θ))
theorem analyticLaurentCoeff_zpow_mul {r : ℝ} (hr : 0 < r)
    (f : ℂ → ℂ) (n k : ℤ) :
    analyticLaurentCoeff r (fun z => z ^ (-n) * f z) k =
      analyticLaurentCoeff r f (k + n) := by
  unfold analyticLaurentCoeff
  congr 1
  apply circleIntegral.integral_congr hr.le
  intro z hz
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    exact hr.ne (by simpa [Metric.mem_sphere] using hz)
  dsimp only
  rw [← mul_assoc, ← zpow_add₀ hz0]
  congr 2
  omega
theorem analyticLaurentCoeff_comp_pos_mul {a : ℝ} (ha : 0 < a)
    (r : ℝ) (f : ℂ → ℂ) (k : ℤ) :
    analyticLaurentCoeff r (fun z => f ((a : ℂ) * z)) k =
      (a : ℂ) ^ k * analyticLaurentCoeff (a * r) f k := by
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  unfold analyticLaurentCoeff
  rw [circleIntegral_scale_real]
  have hfun : (fun z : ℂ => ((a : ℂ) * z) ^ (-k - 1) * f ((a : ℂ) * z)) =
      fun z => (a : ℂ) ^ (-k - 1) * (z ^ (-k - 1) * f ((a : ℂ) * z)) := by
    funext z
    rw [mul_zpow]
    ring
  rw [hfun, circleIntegral.integral_const_mul]
  have hpow : (a : ℂ) ^ k * (a : ℂ) * (a : ℂ) ^ (-k - 1) = 1 := by
    have hp : (a : ℂ) ^ k * (a : ℂ) = (a : ℂ) ^ (k + 1) := by
      rw [zpow_add₀ ha0, zpow_one]
    rw [hp, ← zpow_add₀ ha0]
    simp only [show k + 1 + (-k - 1) = 0 by omega, zpow_zero]
  calc
    _ = ((a : ℂ) ^ k * (a : ℂ) * (a : ℂ) ^ (-k - 1)) *
        ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ∮ z in C(0, r), z ^ (-k - 1) * f ((a : ℂ) * z)) := by rw [hpow, one_mul]
    _ = _ := by ring
end Nagata.W09
end
section
namespace Nagata.W09
open Complex Metric Set
theorem circleIntegral_radius_eq_of_holomorphic_punctured
    {r R : ℝ} (hr : 0 < r) (hle : r ≤ R) {f : ℂ → ℂ}
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z) :
    (∮ z in C(0, R), f z) = ∮ z in C(0, r), f z := by
  apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hle
    Set.countable_empty
  · intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      subst z
      exact hz.2 (by simpa using hr)
    exact (hf z hz0).continuousAt.continuousWithinAt
  · intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      subst z
      exact hz.1.2 (by simpa using hr.le)
    exact hf z hz0
theorem analyticLaurentCoeff_radius_independent
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) {f : ℂ → ℂ}
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z) (k : ℤ) :
    analyticLaurentCoeff r f k = analyticLaurentCoeff s f k := by
  unfold analyticLaurentCoeff
  congr 1
  rcases le_total r s with hrs | hsr
  · exact (circleIntegral_radius_eq_of_holomorphic_punctured hr hrs
      (fun z hz => differentiableAt_laurentIntegrand hf k hz)).symm
  · exact circleIntegral_radius_eq_of_holomorphic_punctured hs hsr
      (fun z hz => differentiableAt_laurentIntegrand hf k hz)
end Nagata.W09
end
section
namespace Nagata.W09
open Nagata.W08
variable {F : Type*} [CommGroupWithZero F]
noncomputable def supportedOrbitCoefficient (τ γ : F) (n K : ℤ) (c₀ : F) (k : ℤ) : F :=
  if n ∣ k - K then orbitValue τ γ n K c₀ ((k - K) / n) else 0
@[simp] theorem supportedOrbitCoefficient_initial (τ γ : F) (n K : ℤ) (c₀ : F) :
    supportedOrbitCoefficient τ γ n K c₀ K = c₀ := by
  simp [supportedOrbitCoefficient]
theorem supportedOrbitCoefficient_support (τ γ : F) (n K : ℤ) (c₀ : F) (k : ℤ)
    (h : supportedOrbitCoefficient τ γ n K c₀ k ≠ 0) : n ∣ k - K := by
  by_contra hdiv
  simp [supportedOrbitCoefficient, hdiv] at h
theorem supportedOrbitCoefficient_residue (τ γ : F) (n K : ℤ) (c₀ : F) (k : ℤ)
    (h : supportedOrbitCoefficient τ γ n K c₀ k ≠ 0) : k % n = K % n :=
  Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    (Int.emod_eq_zero_of_dvd (supportedOrbitCoefficient_support τ γ n K c₀ k h))
theorem supportedOrbitCoefficient_on_orbit (τ γ : F) {n : ℤ} (hn : n ≠ 0)
    (K : ℤ) (c₀ : F) (p : ℤ) :
    supportedOrbitCoefficient τ γ n K c₀ (K + n * p) = orbitValue τ γ n K c₀ p := by
  have hdiff : K + n * p - K = n * p := by omega
  simp [supportedOrbitCoefficient, hdiff, Int.mul_ediv_cancel_left p hn]
end Nagata.W09
end
section
namespace Nagata.W09
open Complex Metric
theorem analyticLaurentCoeff_balance_pos_real {τ : ℝ} (hτ : 0 < τ)
    (n : ℤ) (γ : ℂ) (f : Nagata.W08.automorphicSections (τ : ℂ) n γ) (k : ℤ) :
    (τ : ℂ) ^ k * analyticLaurentCoeff 1 f.val k =
      γ * analyticLaurentCoeff 1 f.val (k + n) := by
  have hcomp : analyticLaurentCoeff 1 (fun z => f.val ((τ : ℂ) * z)) k =
      γ * analyticLaurentCoeff 1 f.val (k + n) := by
    calc
      _ = analyticLaurentCoeff 1 (γ • (fun z => z ^ (-n) * f.val z)) k := by
        apply analyticLaurentCoeff_congr (by norm_num)
        intro z hz
        have hz0 : z ≠ 0 := by
          intro h
          subst z
          simp at hz
        simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc] using f.property.2.2 z hz0
      _ = γ * analyticLaurentCoeff 1 (fun z => z ^ (-n) * f.val z) k :=
        analyticLaurentCoeff_smul 1 γ _ k
      _ = γ * analyticLaurentCoeff 1 f.val (k + n) := by
        rw [analyticLaurentCoeff_zpow_mul zero_lt_one]
  have hdilate := analyticLaurentCoeff_comp_pos_mul hτ 1 f.val k
  rw [mul_one, analyticLaurentCoeff_radius_independent hτ zero_lt_one f.property.2.1 k] at hdilate
  exact hdilate.symm.trans hcomp
theorem laurentCoefficientMap_recurrence_pos_real {τ : ℝ} (hτ : 0 < τ)
    (n : ℤ) (γ : ℂ) (hγ : γ ≠ 0)
    (f : Nagata.W08.automorphicSections (τ : ℂ) n γ) (k : ℤ) :
    laurentCoefficientMap (τ : ℂ) n γ f (k + n) =
      γ⁻¹ * (τ : ℂ) ^ k * laurentCoefficientMap (τ : ℂ) n γ f k := by
  exact Nagata.W08.recurrence_of_coefficient_balance (τ : ℂ) γ hγ n
    (fun j => analyticLaurentCoeff 1 f.val j)
    (analyticLaurentCoeff_balance_pos_real hτ n γ f) k
end Nagata.W09
end
section
namespace Nagata.W09
open Complex Metric
theorem analyticLaurentCoeff_monomial {r : ℝ} (hr : 0 < r) (j k : ℤ) :
    analyticLaurentCoeff r (fun z => z ^ j) k = if j = k then 1 else 0 := by
  unfold analyticLaurentCoeff
  have hi : (∮ z in C(0, r), z ^ (-k - 1) * z ^ j) =
      ∮ z in C(0, r), z ^ (j - k - 1) := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      subst z
      exact hr.ne (by simpa [Metric.mem_sphere] using hz)
    dsimp only
    rw [← zpow_add₀ hz0]
    congr 1
    omega
  rw [hi]
  by_cases hjk : j = k
  · subst j
    simp only [sub_self, zero_sub, zpow_neg_one]
    have hcircle : (∮ z in C(0, r), z⁻¹) = 2 * (Real.pi : ℂ) * Complex.I := by
      simpa only [sub_zero] using circleIntegral.integral_sub_center_inv (0 : ℂ) hr.ne'
    have hconst : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
    rw [hcircle, inv_mul_cancel₀ hconst]
    simp
  · rw [if_neg hjk]
    have hne : j - k - 1 ≠ -1 := by omega
    have hcircle : (∮ z in C(0, r), z ^ (j - k - 1)) = 0 := by
      simpa only [sub_zero] using circleIntegral.integral_sub_zpow_of_ne hne (0 : ℂ) 0 r
    rw [hcircle, mul_zero]
theorem analyticLaurentCoeff_smul_monomial {r : ℝ} (hr : 0 < r)
    (a : ℂ) (j k : ℤ) :
    analyticLaurentCoeff r (fun z => a * z ^ j) k = if j = k then a else 0 := by
  change analyticLaurentCoeff r (a • (fun z : ℂ => z ^ j)) k = _
  rw [analyticLaurentCoeff_smul, analyticLaurentCoeff_monomial hr]
  split <;> simp
end Nagata.W09
end
section
namespace Nagata.W09
theorem laurent_recurrence_eq_of_thetaIndices
    {F : Type*} [CommGroupWithZero F] (τ γ : F) (hτ : τ ≠ 0) (hγ : γ ≠ 0)
    (U : ℝ) {n : ℤ} (hn : 0 < n) (c d : ℤ → F)
    (hc : ∀ k, c (k + n) = γ⁻¹ * τ ^ k * c k)
    (hd : ∀ k, d (k + n) = γ⁻¹ * τ ^ k * d k)
    (hinitial : ∀ K ∈ thetaIndices U n, c K = d K) : c = d := by
  funext k
  obtain ⟨K, hK, hres⟩ := exists_thetaIndex_modEq U hn k
  have hdiv : n ∣ k - K := Int.dvd_of_emod_eq_zero
    (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hres.symm)
  let p := (k - K) / n
  have hp : n * p = k - K := Int.mul_ediv_cancel_of_dvd hdiv
  have hkp : k = K + n * p := by omega
  rw [hkp, Nagata.W08.laurent_recurrence_all_int τ γ hτ hγ n c hc,
    Nagata.W08.laurent_recurrence_all_int τ γ hτ hγ n d hd, hinitial K hK]
end Nagata.W09
end
section
namespace Nagata.W09
open Complex Metric
private theorem continuousOn_scalar_monomial_circle {r : ℝ} (hr : 0 < r)
    (a : ℂ) (j : ℤ) : ContinuousOn (fun z : ℂ => a * z ^ j) (sphere 0 r) := by
  intro z hz
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    exact hr.ne (by simpa [Metric.mem_sphere] using hz)
  exact ((differentiableAt_const a).mul
    (differentiableAt_zpow.mpr (Or.inl hz0))).continuousAt.continuousWithinAt
theorem hasSum_analyticLaurentCoeff_of_monomial_series
    {ι : Type*} [Countable ι] {r : ℝ} (hr : 0 < r)
    (a : ι → ℂ) (N : ι → ℤ) (f : ℂ → ℂ) (B : ι → ℝ)
    (hB : Summable B)
    (hbound : ∀ i z, z ∈ sphere 0 r → ‖a i * z ^ N i‖ ≤ B i)
    (hsum : ∀ z, z ∈ sphere 0 r → HasSum (fun i => a i * z ^ N i) (f z)) (k : ℤ) :
    HasSum (fun i => if N i = k then a i else 0) (analyticLaurentCoeff r f k) := by
  simpa only [analyticLaurentCoeff_smul_monomial hr] using
    hasSum_analyticLaurentCoeff_of_bound hr (fun i z => a i * z ^ N i) f k B hB
      (fun i => continuousOn_scalar_monomial_circle hr (a i) (N i)) hbound hsum
theorem analyticLaurentCoeff_monomial_series_at
    {ι : Type*} [Countable ι] {r : ℝ} (hr : 0 < r)
    (a : ι → ℂ) (N : ι → ℤ) (hN : Function.Injective N)
    (f : ℂ → ℂ) (B : ι → ℝ) (hB : Summable B)
    (hbound : ∀ i z, z ∈ sphere 0 r → ‖a i * z ^ N i‖ ≤ B i)
    (hsum : ∀ z, z ∈ sphere 0 r → HasSum (fun i => a i * z ^ N i) (f z)) (i₀ : ι) :
    analyticLaurentCoeff r f (N i₀) = a i₀ := by
  have h := hasSum_analyticLaurentCoeff_of_monomial_series hr a N f B hB hbound hsum (N i₀)
  have hs : HasSum (fun i => if N i = N i₀ then a i else 0) (a i₀) := by
    have hz : ∀ i, i ≠ i₀ → (if N i = N i₀ then a i else 0) = 0 := by
      intro i hi
      exact if_neg (fun heq => hi (hN heq))
    simpa only [ite_true] using hasSum_single i₀ hz
  exact h.unique hs
theorem analyticLaurentCoeff_monomial_series_eq_zero
    {ι : Type*} [Countable ι] {r : ℝ} (hr : 0 < r)
    (a : ι → ℂ) (N : ι → ℤ) (f : ℂ → ℂ) (B : ι → ℝ) (hB : Summable B)
    (hbound : ∀ i z, z ∈ sphere 0 r → ‖a i * z ^ N i‖ ≤ B i)
    (hsum : ∀ z, z ∈ sphere 0 r → HasSum (fun i => a i * z ^ N i) (f z))
    (k : ℤ) (hk : k ∉ Set.range N) : analyticLaurentCoeff r f k = 0 := by
  have h := hasSum_analyticLaurentCoeff_of_monomial_series hr a N f B hB hbound hsum k
  have hz : (fun i => if N i = k then a i else 0) = fun _ => (0 : ℂ) := by
    funext i
    exact if_neg (fun heq => hk ⟨i, heq⟩)
  rw [hz] at h
  exact h.unique hasSum_zero
end Nagata.W09
end
end OAI
end
section
namespace OAI
section
noncomputable section
open scoped BigOperators
open Module
namespace Nagata.Workers.W10
variable {R V I : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
  [Fintype I] [DecidableEq I]
theorem coefficientMap_surjective (c : V →ₗ[R] (I → R)) (v : I → V)
    (hv : ∀ i, c (v i) = Pi.single i 1) : Function.Surjective c := by
  intro a
  refine ⟨∑ i, a i • v i, ?_⟩
  ext j
  simp [map_sum, hv, Pi.single_apply]
def coefficientEquiv (c : V →ₗ[R] (I → R)) (hc : Function.Injective c)
    (v : I → V) (hv : ∀ i, c (v i) = Pi.single i 1) : V ≃ₗ[R] (I → R) :=
  LinearEquiv.ofBijective c ⟨hc, coefficientMap_surjective c v hv⟩
def basisFromCoefficients (c : V →ₗ[R] (I → R)) (hc : Function.Injective c)
    (v : I → V) (hv : ∀ i, c (v i) = Pi.single i 1) : Basis I R V :=
  (Pi.basisFun R I).map (coefficientEquiv c hc v hv).symm
@[simp] theorem basisFromCoefficients_apply
    (c : V →ₗ[R] (I → R)) (hc : Function.Injective c)
    (v : I → V) (hv : ∀ i, c (v i) = Pi.single i 1) (i : I) :
    basisFromCoefficients c hc v hv i = v i := by
  apply (coefficientEquiv c hc v hv).injective
  change coefficientEquiv c hc v hv
    ((coefficientEquiv c hc v hv).symm (Pi.basisFun R I i)) = c (v i)
  rw [LinearEquiv.apply_symm_apply, Pi.basisFun_apply, hv]
end Nagata.Workers.W10
end
end
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.W08
def normalizedConstantSection (τ : ℂ) (hτ : τ ≠ 0) (a : ℂ) :
    automorphicSections τ 0 1 :=
  sectionOfFunction hτ (fun _ => a) (fun _ _ => differentiableAt_const a)
    (by intro z hz; simp)
@[simp] theorem normalizedConstantSection_apply (τ : ℂ) (hτ : τ ≠ 0) (a : ℂ)
    {z : ℂ} (hz : z ≠ 0) : (normalizedConstantSection τ hτ a).val z = a :=
  sectionOfFunction_apply hτ _ _ _ hz
end Nagata.Workers.W10
end
end
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.W08 Nagata.W09
def residueCoefficientMap {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (C : V →ₗ[ℂ] (ℤ → ℂ)) (U : ℝ) (n : ℤ) :
    V →ₗ[ℂ] (thetaIndices U n → ℂ) where
  toFun f K := C f K.val
  map_add' f g := by ext K; simp
  map_smul' a f := by ext K; simp
theorem residueCoefficientMap_injective {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (C : V →ₗ[ℂ] (ℤ → ℂ)) (hC : Function.Injective C)
    (τ γ : ℂ) (hτ : τ ≠ 0) (hγ : γ ≠ 0) (U : ℝ) {n : ℤ} (hn : 0 < n)
    (hrec : ∀ f k, C f (k + n) = γ⁻¹ * τ ^ k * C f k) :
    Function.Injective (residueCoefficientMap C U n) := by
  intro f g h
  apply hC
  apply laurent_recurrence_eq_of_thetaIndices τ γ hτ hγ U hn
    (C f) (C g) (hrec f) (hrec g)
  intro K hK
  exact congrFun h ⟨K, hK⟩
end Nagata.Workers.W10
end
end
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.W09
variable {V : Type*} [AddCommMonoid V] [Module ℂ V]
def normalizedResidueMap (C : V →ₗ[ℂ] (ℤ → ℂ)) (U : ℝ) (n : ℤ)
    (a : thetaIndices U n → ℂ) : V →ₗ[ℂ] (thetaIndices U n → ℂ) where
  toFun f K := (a K)⁻¹ * C f K.val
  map_add' f g := by ext K; simp [mul_add]
  map_smul' b f := by ext K; simp [mul_left_comm]
theorem normalizedResidueMap_injective (C : V →ₗ[ℂ] (ℤ → ℂ))
    (U : ℝ) (n : ℤ) (a : thetaIndices U n → ℂ)
    (ha : ∀ K, a K ≠ 0)
    (hc : Function.Injective (residueCoefficientMap C U n)) :
    Function.Injective (normalizedResidueMap C U n a) := by
  intro f g h
  apply hc
  ext K
  have he := congrFun h K
  change (a K)⁻¹ * C f K.val = (a K)⁻¹ * C g K.val at he
  exact mul_left_cancel₀ (inv_ne_zero (ha K)) he
theorem normalizedResidueMap_delta (C : V →ₗ[ℂ] (ℤ → ℂ))
    (τ γ : ℂ) (U : ℝ) (n : ℤ) (a : thetaIndices U n → ℂ)
    (ha : ∀ K, a K ≠ 0) (theta : thetaIndices U n → V)
    (hcoeff : ∀ K k, C (theta K) k = supportedOrbitCoefficient τ γ n K.val (a K) k)
    (K : thetaIndices U n) :
    normalizedResidueMap C U n a (theta K) = Pi.single K 1 := by
  classical
  ext L
  change (a L)⁻¹ * C (theta K) L.val = _
  rw [hcoeff]
  by_cases hLK : L = K
  · subst L
    simp [supportedOrbitCoefficient_initial, ha]
  · have hz : supportedOrbitCoefficient τ γ n K.val (a K) L.val = 0 := by
      by_contra hne
      have he := thetaIndices_residue_injective L.property K.property
        (supportedOrbitCoefficient_residue τ γ n K.val (a K) L.val hne)
      exact hLK (Subtype.ext he)
    simp [hz, hLK]
def basisFromSupportedOrbits (C : V →ₗ[ℂ] (ℤ → ℂ))
    (τ γ : ℂ) (U : ℝ) (n : ℤ) (a : thetaIndices U n → ℂ)
    (ha : ∀ K, a K ≠ 0)
    (hc : Function.Injective (residueCoefficientMap C U n))
    (theta : thetaIndices U n → V)
    (hcoeff : ∀ K k, C (theta K) k = supportedOrbitCoefficient τ γ n K.val (a K) k) :
    Basis (thetaIndices U n) ℂ V :=
  basisFromCoefficients (normalizedResidueMap C U n a)
    (normalizedResidueMap_injective C U n a ha hc) theta
    (normalizedResidueMap_delta C τ γ U n a ha theta hcoeff)
@[simp] theorem basisFromSupportedOrbits_apply (C : V →ₗ[ℂ] (ℤ → ℂ))
    (τ γ : ℂ) (U : ℝ) (n : ℤ) (a : thetaIndices U n → ℂ)
    (ha : ∀ K, a K ≠ 0)
    (hc : Function.Injective (residueCoefficientMap C U n))
    (theta : thetaIndices U n → V)
    (hcoeff : ∀ K k, C (theta K) k = supportedOrbitCoefficient τ γ n K.val (a K) k)
    (K : thetaIndices U n) : basisFromSupportedOrbits C τ γ U n a ha hc theta hcoeff K = theta K :=
  basisFromCoefficients_apply _ _ _ _ K
end Nagata.Workers.W10
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
open scoped BigOperators
open Module
namespace Nagata.Workers.W10
variable {R A : Type*} [Semiring R] [Semiring A] [Module R A]
def boundedCoefficientPolynomials (u : ℕ) (S : ℕ → Submodule R A) :
    Submodule R (Polynomial A) where
  carrier := {F | (∀ j, u < j → F.coeff j = 0) ∧ ∀ j, F.coeff j ∈ S j}
  zero_mem' := by constructor <;> simp
  add_mem' := by
    intro F G hF hG
    constructor
    · intro j hj; simp [Polynomial.coeff_add, hF.1 j hj, hG.1 j hj]
    · intro j; simpa using (S j).add_mem (hF.2 j) (hG.2 j)
  smul_mem' := by
    intro a F hF
    constructor
    · intro j hj; simp [Polynomial.coeff_smul, hF.1 j hj]
    · intro j; simpa using (S j).smul_mem a (hF.2 j)
def boundedPolynomialCoordinates (u : ℕ) (S : ℕ → Submodule R A) :
    boundedCoefficientPolynomials u S →ₗ[R] ((j : Fin (u + 1)) → S j.val) where
  toFun F j := ⟨F.val.coeff j.val, F.property.2 j.val⟩
  map_add' F G := by ext j; simp
  map_smul' a F := by ext j; simp
theorem boundedPolynomialCoordinates_injective (u : ℕ) (S : ℕ → Submodule R A) :
    Function.Injective (boundedPolynomialCoordinates u S) := by
  intro F G h
  apply Subtype.ext
  apply Polynomial.ext
  intro j
  by_cases hj : j ≤ u
  · exact congrArg Subtype.val (congrFun h ⟨j, by omega⟩)
  · rw [F.property.1 j (by omega), G.property.1 j (by omega)]
def finiteCoefficientPolynomial (u : ℕ) (S : ℕ → Submodule R A)
    (a : (j : Fin (u + 1)) → S j.val) : Polynomial A :=
  ∑ j, Polynomial.monomial j.val (a j).val
@[simp] theorem finiteCoefficientPolynomial_coeff (u : ℕ) (S : ℕ → Submodule R A)
    (a : (j : Fin (u + 1)) → S j.val) (j : Fin (u + 1)) :
    (finiteCoefficientPolynomial u S a).coeff j.val = (a j).val := by
  classical
  simp [finiteCoefficientPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, Fin.val_inj]
theorem finiteCoefficientPolynomial_coeff_above (u : ℕ) (S : ℕ → Submodule R A)
    (a : (j : Fin (u + 1)) → S j.val) (k : ℕ) (hk : u < k) :
    (finiteCoefficientPolynomial u S a).coeff k = 0 := by
  classical
  rw [finiteCoefficientPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro j hj
  apply Polynomial.coeff_monomial_of_ne
  omega
theorem boundedPolynomialCoordinates_surjective (u : ℕ) (S : ℕ → Submodule R A) :
    Function.Surjective (boundedPolynomialCoordinates u S) := by
  intro a
  have hmem : finiteCoefficientPolynomial u S a ∈ boundedCoefficientPolynomials u S := by
    constructor
    · exact finiteCoefficientPolynomial_coeff_above u S a
    · intro k
      by_cases hk : k ≤ u
      · have he := finiteCoefficientPolynomial_coeff u S a ⟨k, by omega⟩
        rw [he]
        exact (a ⟨k, by omega⟩).property
      · rw [finiteCoefficientPolynomial_coeff_above u S a k (by omega)]
        exact (S k).zero_mem
  refine ⟨⟨finiteCoefficientPolynomial u S a, hmem⟩, ?_⟩
  ext j
  exact finiteCoefficientPolynomial_coeff u S a j
def boundedPolynomialEquiv (u : ℕ) (S : ℕ → Submodule R A) :
    boundedCoefficientPolynomials u S ≃ₗ[R] ((j : Fin (u + 1)) → S j.val) :=
  LinearEquiv.ofBijective (boundedPolynomialCoordinates u S)
    ⟨boundedPolynomialCoordinates_injective u S, boundedPolynomialCoordinates_surjective u S⟩
def boundedPolynomialBasis (u : ℕ) (S : ℕ → Submodule R A)
    (I : Fin (u + 1) → Type*) (b : ∀ j, Basis (I j) R (S j.val)) :
    Basis (Σ j, I j) R (boundedCoefficientPolynomials u S) :=
  (Pi.basis b).map (boundedPolynomialEquiv u S).symm
theorem boundedPolynomialBasis_coeff (u : ℕ) (S : ℕ → Submodule R A)
    (I : Fin (u + 1) → Type*) (b : ∀ j, Basis (I j) R (S j.val))
    (j : Fin (u + 1)) (i : I j) (k : Fin (u + 1)) :
    ((boundedPolynomialBasis u S I b ⟨j, i⟩).val).coeff k.val =
      ((Pi.single (M := fun k : Fin (u + 1) => S k.val) j (b j i)) k).val := by
  classical
  change ((boundedPolynomialEquiv u S)
    ((boundedPolynomialEquiv u S).symm ((Pi.basis b) ⟨j, i⟩)) k).val = _
  rw [LinearEquiv.apply_symm_apply, Pi.basis_apply]
theorem boundedPolynomialBasis_as_monomial (u : ℕ) (S : ℕ → Submodule R A)
    (I : Fin (u + 1) → Type*) (b : ∀ j, Basis (I j) R (S j.val))
    (j : Fin (u + 1)) (i : I j) :
    (boundedPolynomialBasis u S I b ⟨j, i⟩).val =
      Polynomial.monomial j.val (b j i).val := by
  classical
  apply Polynomial.ext
  intro k
  by_cases hk : k ≤ u
  · let kk : Fin (u + 1) := ⟨k, by omega⟩
    have h := boundedPolynomialBasis_coeff u S I b j i kk
    rw [h, Polynomial.coeff_monomial]
    by_cases he : j = kk
    · subst j
      simp [kk]
    · have hev : j.val ≠ k := fun h => he (Fin.ext h)
      simp [Pi.single_eq_of_ne (Ne.symm he), hev]
  · rw [(boundedPolynomialBasis u S I b ⟨j, i⟩).property.1 k (by omega)]
    symm
    apply Polynomial.coeff_monomial_of_ne
    omega
end Nagata.Workers.W10
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W07
def thetaExponent (n a p : ℝ) : ℝ := p * a + n * p * (p - 1) / 2
def thetaMargin (n a : ℝ) : ℝ := min a (n - a)
theorem thetaMargin_pos {n a : ℝ} (ha : 0 < a) (han : a < n) :
    0 < thetaMargin n a := by
  exact lt_min ha (sub_pos.mpr han)
theorem thetaExponent_negative_index (n a t : ℝ) :
    thetaExponent n a (-t) = t * (n - a) + n * t * (t - 1) / 2 := by
  unfold thetaExponent
  ring
theorem thetaExponent_quadratic_lower (n a p : ℝ) :
    thetaMargin n a * |p| + n * |p| * (|p| - 1) / 2 ≤
      thetaExponent n a p := by
  by_cases hp : 0 ≤ p
  · rw [abs_of_nonneg hp]
    have h := mul_le_mul_of_nonneg_right (min_le_left a (n - a)) hp
    unfold thetaMargin thetaExponent
    nlinarith
  · have hp' : p ≤ 0 := le_of_lt (lt_of_not_ge hp)
    rw [abs_of_nonpos hp']
    have h := mul_le_mul_of_nonneg_right (min_le_right a (n - a))
      (neg_nonneg.mpr hp')
    unfold thetaMargin thetaExponent
    nlinarith
theorem thetaExponent_integer_lower {n a : ℝ} (hn : 0 ≤ n) (p : ℤ) :
    thetaMargin n a * |(p : ℝ)| ≤ thetaExponent n a (p : ℝ) := by
  by_cases hp : p = 0
  · subst p
    simp [thetaExponent]
  · have habs : 1 ≤ |(p : ℝ)| := by
      rcases Int.cast_le_neg_one_or_one_le_cast_of_ne_zero (R := ℝ) hp with h | h
      · rw [abs_of_nonpos (by linarith : (p : ℝ) ≤ 0)]
        linarith
      · rw [abs_of_nonneg (by linarith : 0 ≤ (p : ℝ))]
        exact h
    have hquad : 0 ≤ n * |(p : ℝ)| * (|(p : ℝ)| - 1) / 2 :=
      div_nonneg (mul_nonneg (mul_nonneg hn (abs_nonneg _))
        (sub_nonneg.mpr habs)) (by norm_num)
    exact le_trans (by linarith) (thetaExponent_quadratic_lower n a (p : ℝ))
end Nagata.W07
end
end
section
noncomputable section
namespace Nagata.W07
theorem laurentExponent_cast_real (n K p : ℤ) :
    (Nagata.W08.laurentExponent n K p : ℝ) =
      (p : ℝ) * (K : ℝ) + (n : ℝ) * (p : ℝ) * ((p : ℝ) - 1) / 2 := by
  have ht : (2 : ℝ) * (Nagata.W08.triangular p : ℝ) = (p : ℝ) * ((p : ℝ) - 1) := by
    exact_mod_cast Nagata.W08.two_mul_triangular p
  have ht' : (Nagata.W08.triangular p : ℝ) = (p : ℝ) * ((p : ℝ) - 1) / 2 := by
    linarith
  simp only [Nagata.W08.laurentExponent, Int.cast_add, Int.cast_mul, ht']
  ring
theorem normalized_exponent_identity (n K p : ℤ) (σ x₀ : ℝ) :
    -x₀ * (K : ℝ) + (-σ * (p : ℝ) + (Nagata.W08.laurentExponent n K p : ℝ)) +
      x₀ * ((K + n * p : ℤ) : ℝ) =
      thetaExponent (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)) (p : ℝ) := by
  rw [laurentExponent_cast_real]
  simp only [Int.cast_add, Int.cast_mul, thetaExponent]
  ring
end Nagata.W07
end
end
section
noncomputable section
namespace Nagata.W07
def normalizedThetaTerm (n a K : ℝ) (ε : ℂ) (τ : ℝ) (p : ℤ) (x : ℂ) : ℂ :=
  ε ^ (-p) * ((τ ^ thetaExponent n a (p : ℝ) : ℝ) : ℂ) *
    Complex.exp (((K + n * (p : ℝ) : ℝ) : ℂ) * x)
def normalizedThetaDerivativeTerm (n a K : ℝ) (ε : ℂ) (τ : ℝ)
    (c : ℕ) (p : ℤ) (x : ℂ) : ℂ :=
  (((K + n * (p : ℝ) : ℝ) : ℂ) ^ c) * normalizedThetaTerm n a K ε τ p x
@[simp] theorem normalizedThetaTerm_zero (n a K : ℝ) (ε : ℂ) (τ : ℝ) (x : ℂ) :
    normalizedThetaTerm n a K ε τ 0 x = Complex.exp ((K : ℂ) * x) := by
  simp [normalizedThetaTerm, thetaExponent]
@[simp] theorem normalizedThetaDerivativeTerm_zero_order
    (n a K : ℝ) (ε : ℂ) (τ : ℝ) (p : ℤ) (x : ℂ) :
    normalizedThetaDerivativeTerm n a K ε τ 0 p x =
      normalizedThetaTerm n a K ε τ p x := by
  simp [normalizedThetaDerivativeTerm]
@[simp] theorem normalizedThetaDerivativeTerm_zero_index
    (n a K : ℝ) (ε : ℂ) (τ : ℝ) (c : ℕ) (x : ℂ) :
    normalizedThetaDerivativeTerm n a K ε τ c 0 x =
      (K : ℂ) ^ c * Complex.exp ((K : ℂ) * x) := by
  simp [normalizedThetaDerivativeTerm]
theorem natAbs_real (p : ℤ) : (p.natAbs : ℝ) = |(p : ℝ)| := by
  rw [Nat.cast_natAbs, Int.cast_abs]
theorem theta_power_le_geometric {n a τ : ℝ} (hn : 0 ≤ n)
    (hτ : 0 < τ) (hτone : τ ≤ 1) (p : ℤ) :
    τ ^ thetaExponent n a (p : ℝ) ≤ (τ ^ thetaMargin n a) ^ p.natAbs := by
  have h := Real.rpow_le_rpow_of_exponent_ge hτ hτone
    (thetaExponent_integer_lower (a := a) hn p)
  calc
    _ ≤ τ ^ (thetaMargin n a * |(p : ℝ)|) := h
    _ = (τ ^ thetaMargin n a) ^ p.natAbs := by
      rw [← natAbs_real p, Real.rpow_mul_natCast hτ.le]
theorem theta_frequency_le {n : ℝ} (hn : 0 ≤ n) (K : ℝ) (p : ℤ) :
    |K + n * (p : ℝ)| ≤ |K| + n * (p.natAbs : ℝ) := by
  calc
    _ ≤ |K| + |n * (p : ℝ)| := abs_add_le _ _
    _ = _ := by rw [abs_mul, abs_of_nonneg hn, natAbs_real]
theorem norm_normalizedThetaDerivativeTerm_le {n a K τ R : ℝ} {ε x : ℂ}
    (hn : 0 ≤ n) (hτ : 0 < τ) (hτone : τ ≤ 1) (hε : ‖ε‖ = 1)
    (hR : 0 ≤ R) (hx : ‖x‖ ≤ R) (c : ℕ) (p : ℤ) :
    ‖normalizedThetaDerivativeTerm n a K ε τ c p x‖ ≤
      Real.exp (|K| * R) * (|K| + n * (p.natAbs : ℝ)) ^ c *
        (Real.exp (n * R) * τ ^ thetaMargin n a) ^ p.natAbs := by
  let A : ℝ := |K| + n * (p.natAbs : ℝ)
  have hA : 0 ≤ A := add_nonneg (abs_nonneg K) (mul_nonneg hn (Nat.cast_nonneg _))
  have hfreq : |K + n * (p : ℝ)| ≤ A := theta_frequency_le hn K p
  have hfreqpow : |K + n * (p : ℝ)| ^ c ≤ A ^ c :=
    pow_le_pow_left₀ (abs_nonneg _) hfreq c
  have hpow := theta_power_le_geometric (a := a) hn hτ hτone p
  have hexp : ‖Complex.exp (((K + n * (p : ℝ) : ℝ) : ℂ) * x)‖ ≤
      Real.exp (A * R) := by
    apply (Complex.norm_exp_le_exp_norm _).trans
    apply Real.exp_le_exp.mpr
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hx (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hfreq hR)
  have hexp_split : Real.exp (A * R) =
      Real.exp (|K| * R) * Real.exp (n * R) ^ p.natAbs := by
    have he : A * R = |K| * R + (p.natAbs : ℝ) * (n * R) := by
      dsimp [A]
      ring
    rw [he, Real.exp_add, Real.exp_nat_mul]
  have hnorm : ‖normalizedThetaDerivativeTerm n a K ε τ c p x‖ =
      |K + n * (p : ℝ)| ^ c * τ ^ thetaExponent n a (p : ℝ) *
        ‖Complex.exp (((K + n * (p : ℝ) : ℝ) : ℂ) * x)‖ := by
    simp only [normalizedThetaDerivativeTerm, normalizedThetaTerm, norm_mul, norm_pow,
      Complex.norm_zpow, hε, one_zpow, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hτ.le _), mul_assoc]
  rw [hnorm]
  calc
    _ ≤ (A ^ c * (τ ^ thetaMargin n a) ^ p.natAbs) * Real.exp (A * R) := by
      apply mul_le_mul
      · exact mul_le_mul hfreqpow hpow (Real.rpow_nonneg hτ.le _) (pow_nonneg hA _)
      · exact hexp
      · exact norm_nonneg _
      · exact mul_nonneg (pow_nonneg hA _) (pow_nonneg (Real.rpow_nonneg hτ.le _) _)
    _ = _ := by
      rw [hexp_split, mul_pow]
      dsimp [A]
      ring
theorem norm_normalizedThetaTerm_le {n a K τ R : ℝ} {ε x : ℂ}
    (hn : 0 ≤ n) (hτ : 0 < τ) (hτone : τ ≤ 1) (hε : ‖ε‖ = 1)
    (hR : 0 ≤ R) (hx : ‖x‖ ≤ R) (p : ℤ) :
    ‖normalizedThetaTerm n a K ε τ p x‖ ≤ Real.exp (|K| * R) *
      (Real.exp (n * R) * τ ^ thetaMargin n a) ^ p.natAbs := by
  simpa using norm_normalizedThetaDerivativeTerm_le
    (a := a) hn hτ hτone hε hR hx 0 p
end Nagata.W07
end
end
section
noncomputable section
namespace Nagata.W07
theorem complex_rpow_zpow {τ : ℝ} (hτ : 0 ≤ τ) (s : ℝ) (p : ℤ) :
    (((τ ^ s : ℝ) : ℂ) ^ p) = ((τ ^ (s * (p : ℝ)) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_zpow, ← Real.rpow_mul_intCast hτ]
def normalizedLaurentCoefficient (τ σ x₀ : ℝ) (ε : ℂ) (n K p : ℤ) : ℂ :=
  ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ) * ε ^ (-p) *
    ((τ ^ (-σ * (p : ℝ) + (Nagata.W08.laurentExponent n K p : ℝ)) : ℝ) : ℂ)
theorem normalizedLaurentCoefficient_eq_orbitValue {τ : ℝ} (hτ : 0 < τ)
    (σ x₀ : ℝ) (ε : ℂ) (n K p : ℤ) :
    normalizedLaurentCoefficient τ σ x₀ ε n K p =
      Nagata.W08.orbitValue (τ : ℂ) (ε * ((τ ^ σ : ℝ) : ℂ)) n K
        ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ) p := by
  unfold Nagata.W08.orbitValue
  rw [mul_zpow, complex_rpow_zpow hτ.le, ← Complex.ofReal_zpow, ← Real.rpow_intCast]
  simp only [normalizedLaurentCoefficient, Real.rpow_add hτ, Complex.ofReal_mul,
    Int.cast_neg, mul_neg, neg_mul]
  ring
theorem normalizedLaurentCoefficient_of_recurrence {τ : ℝ} (hτ : 0 < τ)
    (σ x₀ : ℝ) {ε : ℂ} (hε : ε ≠ 0) (n K : ℤ) (c : ℤ → ℂ)
    (hc : ∀ L : ℤ, c (L + n) =
      (ε * ((τ ^ σ : ℝ) : ℂ))⁻¹ * (τ : ℂ) ^ L * c L)
    (hstart : c K = ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ)) (p : ℤ) :
    c (K + n * p) = normalizedLaurentCoefficient τ σ x₀ ε n K p := by
  have hτC : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hτσ : ((τ ^ σ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hτ σ).ne'
  have hγ : ε * ((τ ^ σ : ℝ) : ℂ) ≠ 0 := mul_ne_zero hε hτσ
  have h := Nagata.W08.laurent_recurrence_all_int (τ : ℂ)
    (ε * ((τ ^ σ : ℝ) : ℂ)) hτC hγ n c hc K p
  change c (K + n * p) = c K * (ε * ((τ ^ σ : ℝ) : ℂ)) ^ (-p) *
    (τ : ℂ) ^ Nagata.W08.laurentExponent n K p at h
  rw [hstart, mul_zpow, complex_rpow_zpow hτ.le] at h
  rw [← Complex.ofReal_zpow, ← Real.rpow_intCast] at h
  rw [h]
  simp only [normalizedLaurentCoefficient, Real.rpow_add hτ, Complex.ofReal_mul,
    Int.cast_neg, mul_neg, neg_mul]
  ring
theorem normalizedLaurentCoefficient_eval {τ : ℝ} (hτ : 0 < τ)
    (σ x₀ : ℝ) (ε x : ℂ) (n K p : ℤ) :
    normalizedLaurentCoefficient τ σ x₀ ε n K p *
        (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) ^ (K + n * p) =
      normalizedThetaTerm (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x := by
  have hscalar : τ ^ (-x₀ * (K : ℝ)) *
      τ ^ (-σ * (p : ℝ) + (Nagata.W08.laurentExponent n K p : ℝ)) *
        τ ^ (x₀ * ((K + n * p : ℤ) : ℝ)) =
      τ ^ thetaExponent (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)) (p : ℝ) := by
    rw [← Real.rpow_add hτ, ← Real.rpow_add hτ, normalized_exponent_identity]
  calc
    _ = ε ^ (-p) *
        ((τ ^ (-x₀ * (K : ℝ)) *
          τ ^ (-σ * (p : ℝ) + (Nagata.W08.laurentExponent n K p : ℝ)) *
            τ ^ (x₀ * ((K + n * p : ℤ) : ℝ)) : ℝ) : ℂ) *
          Complex.exp (((K + n * p : ℤ) : ℂ) * x) := by
      simp only [normalizedLaurentCoefficient, mul_zpow, complex_rpow_zpow hτ.le,
        ← Complex.exp_int_mul, Complex.ofReal_mul]
      ring
    _ = _ := by
      rw [hscalar]
      simp only [normalizedThetaTerm, Int.cast_add, Int.cast_mul, Complex.ofReal_add,
        Complex.ofReal_mul, Complex.ofReal_intCast]
theorem normalized_recurrence_eval {τ : ℝ} (hτ : 0 < τ)
    (σ x₀ : ℝ) {ε : ℂ} (hε : ε ≠ 0) (n K : ℤ) (c : ℤ → ℂ)
    (hc : ∀ L : ℤ, c (L + n) =
      (ε * ((τ ^ σ : ℝ) : ℂ))⁻¹ * (τ : ℂ) ^ L * c L)
    (hstart : c K = ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ)) (p : ℤ) (x : ℂ) :
    c (K + n * p) * (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) ^ (K + n * p) =
      normalizedThetaTerm (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x := by
  rw [normalizedLaurentCoefficient_of_recurrence hτ σ x₀ hε n K c hc hstart p]
  exact normalizedLaurentCoefficient_eval hτ σ x₀ ε x n K p
theorem normalizedThetaTerm_shift {τ : ℝ} (hτ : 0 < τ)
    (n a K x₀ : ℝ) (ε x : ℂ) (p : ℤ) :
    ((τ ^ (-x₀ * K) : ℝ) : ℂ) *
        normalizedThetaTerm n a K ε τ p (((x₀ * Real.log τ : ℝ) : ℂ) + x) =
      normalizedThetaTerm n (a + x₀ * n) K ε τ p x := by
  have hexp : Complex.exp (((K + n * (p : ℝ) : ℝ) : ℂ) *
      (((x₀ * Real.log τ : ℝ) : ℂ) + x)) =
      ((τ ^ (x₀ * (K + n * (p : ℝ))) : ℝ) : ℂ) *
        Complex.exp (((K + n * (p : ℝ) : ℝ) : ℂ) * x) := by
    rw [mul_add, Complex.exp_add, Real.rpow_def_of_pos hτ, Complex.ofReal_exp]
    congr 2
    push_cast
    ring
  have hpowers : τ ^ (-x₀ * K) * τ ^ thetaExponent n a (p : ℝ) *
      τ ^ (x₀ * (K + n * (p : ℝ))) =
      τ ^ thetaExponent n (a + x₀ * n) (p : ℝ) := by
    rw [← Real.rpow_add hτ, ← Real.rpow_add hτ]
    congr 1
    unfold thetaExponent
    ring
  calc
    _ = ε ^ (-p) *
        ((τ ^ (-x₀ * K) * τ ^ thetaExponent n a (p : ℝ) *
          τ ^ (x₀ * (K + n * (p : ℝ))) : ℝ) : ℂ) *
          Complex.exp (((K + n * (p : ℝ) : ℝ) : ℂ) * x) := by
      unfold normalizedThetaTerm
      rw [hexp]
      simp only [Complex.ofReal_mul]
      ring
    _ = _ := by rw [hpowers]; rfl
theorem normalization_scalar_pos {τ : ℝ} (hτ : 0 < τ) (x₀ : ℝ) (K : ℤ) :
    0 < τ ^ (-x₀ * (K : ℝ)) := Real.rpow_pos_of_pos hτ _
theorem normalization_scalar_ne_zero {τ : ℝ} (hτ : 0 < τ) (x₀ : ℝ) (K : ℤ) :
    ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (normalization_scalar_pos hτ x₀ K).ne'
end Nagata.W07
end
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Nagata.W22
section
end
section
open Filter Topology
theorem differentiableOn_iteratedDeriv {f : ℂ → ℂ} {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (c : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv c f) U := by
  induction c with
  | zero => simpa using hf
  | succ c ih => simpa only [iteratedDeriv_succ] using ih.deriv hU
theorem tendstoLocallyUniformlyOn_iteratedDeriv
    {α : Type*} {l : Filter α} {F : α → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (h : TendstoLocallyUniformlyOn F f l U)
    (hF : ∀ᶠ a in l, DifferentiableOn ℂ (F a) U) (hU : IsOpen U) (c : ℕ) :
    TendstoLocallyUniformlyOn (fun a => iteratedDeriv c (F a)) (iteratedDeriv c f) l U := by
  induction c with
  | zero => simpa using h
  | succ c ih =>
    have hiF : ∀ᶠ a in l, DifferentiableOn ℂ (iteratedDeriv c (F a)) U :=
      hF.mono fun a ha => differentiableOn_iteratedDeriv ha hU c
    simpa only [iteratedDeriv_succ, Function.comp_def] using ih.deriv hiF hU
theorem summable_weighted_half (c : ℕ) :
    Summable (fun t : ℕ => ((t + 1 : ℕ) : ℝ) ^ c * (1 / 2 : ℝ) ^ t) := by
  have hs := (summable_nat_add_iff 1).2
    (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) c (r := 1 / 2)
      (by norm_num))
  apply (hs.mul_left 2).congr
  intro t
  simp only [pow_succ]
  ring
theorem weighted_term_le {w : ℕ → ℝ} (hw : ∀ t, 0 ≤ w t)
    {z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2) (t : ℕ) :
    w t * z ^ (t + 1) ≤ z * (w t * (1 / 2 : ℝ) ^ t) := by
  calc
    w t * z ^ (t + 1) = z * (w t * z ^ t) := by ring
    _ ≤ z * (w t * (1 / 2 : ℝ) ^ t) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz hzhalf t) (hw t)) hz
theorem summable_weighted_tail {w : ℕ → ℝ} (hw : ∀ t, 0 ≤ w t)
    (hs : Summable (fun t => w t * (1 / 2 : ℝ) ^ t))
    {z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2) :
    Summable (fun t => w t * z ^ (t + 1)) := by
  exact (hs.mul_left z).of_nonneg_of_le
    (fun t => mul_nonneg (hw t) (pow_nonneg hz _))
    (weighted_term_le hw hz hzhalf)
theorem weighted_tail_le {w : ℕ → ℝ} (hw : ∀ t, 0 ≤ w t)
    (hs : Summable (fun t => w t * (1 / 2 : ℝ) ^ t))
    {z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2) :
    (∑' t, w t * z ^ (t + 1)) ≤
      z * (∑' t, w t * (1 / 2 : ℝ) ^ t) := by
  calc
    _ ≤ ∑' t, z * (w t * (1 / 2 : ℝ) ^ t) :=
      (summable_weighted_tail hw hs hz hzhalf).tsum_le_tsum
        (weighted_term_le hw hz hzhalf) (hs.mul_left z)
    _ = _ := tsum_mul_left
theorem tendsto_weighted_tail_zero {α : Type*} {l : Filter α} {z : α → ℝ}
    {w : ℕ → ℝ} (hw : ∀ t, 0 ≤ w t)
    (hs : Summable (fun t => w t * (1 / 2 : ℝ) ^ t))
    (hz : Tendsto z l (𝓝 0))
    (hzrange : ∀ᶠ a in l, 0 ≤ z a ∧ z a ≤ 1 / 2) :
    Tendsto (fun a => ∑' t, w t * z a ^ (t + 1)) l (𝓝 0) := by
  apply squeeze_zero'
    (hzrange.mono fun a ha => tsum_nonneg fun t => mul_nonneg (hw t) (pow_nonneg ha.1 _))
    (hzrange.mono fun a ha => weighted_tail_le hw hs ha.1 ha.2)
  simpa using hz.mul_const (∑' t, w t * (1 / 2 : ℝ) ^ t)
theorem tendsto_polynomial_tail_zero {α : Type*} {l : Filter α} {z : α → ℝ}
    (c : ℕ) (hz : Tendsto z l (𝓝 0))
    (hzrange : ∀ᶠ a in l, 0 ≤ z a ∧ z a ≤ 1 / 2) :
    Tendsto (fun a => ∑' t : ℕ, ((t + 1 : ℕ) : ℝ) ^ c * z a ^ (t + 1))
      l (𝓝 0) :=
  tendsto_weighted_tail_zero (fun t => by positivity) (summable_weighted_half c) hz hzrange
theorem affine_weight_le {A n : ℝ} (hA : 0 ≤ A) (hn : 0 ≤ n)
    (c t : ℕ) :
    (A + n * ((t + 1 : ℕ) : ℝ)) ^ c ≤
      (A + n) ^ c * ((t + 1 : ℕ) : ℝ) ^ c := by
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have ht : (1 : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le t)
  nlinarith [mul_nonneg hA (sub_nonneg.mpr ht)]
theorem summable_affine_weighted_half {A n : ℝ} (hA : 0 ≤ A) (hn : 0 ≤ n)
    (c : ℕ) :
    Summable (fun t : ℕ => (A + n * ((t + 1 : ℕ) : ℝ)) ^ c * (1 / 2 : ℝ) ^ t) := by
  apply ((summable_weighted_half c).mul_left ((A + n) ^ c)).of_nonneg_of_le
  · intro t
    positivity
  · intro t
    calc
      _ ≤ ((A + n) ^ c * ((t + 1 : ℕ) : ℝ) ^ c) * (1 / 2 : ℝ) ^ t :=
        mul_le_mul_of_nonneg_right (affine_weight_le hA hn c t) (by positivity)
      _ = _ := by ring
theorem tendsto_affine_weighted_tail_zero {α : Type*} {l : Filter α} {z : α → ℝ}
    {A n : ℝ} (hA : 0 ≤ A) (hn : 0 ≤ n) (c : ℕ)
    (hz : Tendsto z l (𝓝 0))
    (hzrange : ∀ᶠ a in l, 0 ≤ z a ∧ z a ≤ 1 / 2) :
    Tendsto (fun a => ∑' t : ℕ,
      (A + n * ((t + 1 : ℕ) : ℝ)) ^ c * z a ^ (t + 1)) l (𝓝 0) :=
  tendsto_weighted_tail_zero (fun t => by positivity)
    (summable_affine_weighted_half hA hn c) hz hzrange
theorem summable_of_weighted_bound {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : ℕ → E} {w : ℕ → ℝ} (hw : ∀ t, 0 ≤ w t)
    (hs : Summable (fun t => w t * (1 / 2 : ℝ) ^ t))
    {C z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2)
    (hf : ∀ t, ‖f t‖ ≤ C * (w t * z ^ (t + 1))) : Summable f := by
  exact ((summable_weighted_tail hw hs hz hzhalf).mul_left C).of_norm_bounded hf
theorem norm_tsum_le_weighted_bound {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : ℕ → E} {w : ℕ → ℝ} (hw : ∀ t, 0 ≤ w t)
    (hs : Summable (fun t => w t * (1 / 2 : ℝ) ^ t))
    {C z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2)
    (hf : ∀ t, ‖f t‖ ≤ C * (w t * z ^ (t + 1))) :
    ‖∑' t, f t‖ ≤ C * (∑' t, w t * z ^ (t + 1)) := by
  have hmajor := (summable_weighted_tail hw hs hz hzhalf).mul_left C
  have hnorm : Summable (fun t => ‖f t‖) :=
    hmajor.of_nonneg_of_le (fun t => norm_nonneg _) hf
  calc
    _ ≤ ∑' t, ‖f t‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' t, C * (w t * z ^ (t + 1)) := hnorm.tsum_le_tsum hf hmajor
    _ = _ := tsum_mul_left
theorem tsum_int_eq_center_add_tails {E : Type*} [NormedAddCommGroup E]
    {f : ℤ → E}
    (hp : Summable (fun t : ℕ => f (t + 1)))
    (hm : Summable (fun t : ℕ => f (-(t + 1)))) :
    (∑' p : ℤ, f p) = f 0 +
      (∑' t : ℕ, f (t + 1)) + (∑' t : ℕ, f (-(t + 1))) := by
  have hp0 : Summable (fun t : ℕ => f t) := (summable_nat_add_iff 1).1 hp
  rw [tsum_of_nat_of_neg_add_one hp0 hm, ← hp0.sum_add_tsum_nat_add 1]
  simp
private theorem norm_tsum_int_sub_center_le_weighted_bound
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : ℤ → E} {w : ℕ → ℝ} (hw : ∀ t, 0 ≤ w t)
    (hs : Summable (fun t => w t * (1 / 2 : ℝ) ^ t))
    {C z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2)
    (hp : ∀ t : ℕ, ‖f (t + 1)‖ ≤ C * (w t * z ^ (t + 1)))
    (hm : ∀ t : ℕ, ‖f (-(t + 1))‖ ≤ C * (w t * z ^ (t + 1))) :
    ‖(∑' p, f p) - f 0‖ ≤ 2 * C * (∑' t, w t * z ^ (t + 1)) := by
  have hps := summable_of_weighted_bound hw hs hz hzhalf hp
  have hms := summable_of_weighted_bound hw hs hz hzhalf hm
  rw [tsum_int_eq_center_add_tails hps hms]
  have hid : (f 0 + (∑' t : ℕ, f (t + 1)) + (∑' t : ℕ, f (-(t + 1)))) - f 0 =
      (∑' t : ℕ, f (t + 1)) + (∑' t : ℕ, f (-(t + 1))) := by abel
  rw [hid]
  calc
    _ ≤ ‖∑' t : ℕ, f (t + 1)‖ + ‖∑' t : ℕ, f (-(t + 1))‖ := norm_add_le _ _
    _ ≤ C * (∑' t, w t * z ^ (t + 1)) + C * (∑' t, w t * z ^ (t + 1)) :=
      add_le_add (norm_tsum_le_weighted_bound hw hs hz hzhalf hp)
        (norm_tsum_le_weighted_bound hw hs hz hzhalf hm)
    _ = _ := by ring
theorem tendstoUniformlyOn_tsum_int_center_of_weighted_bound
    {α β E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {l : Filter α} {s : Set β} {f : α → ℤ → β → E} {g : β → E} {z : α → ℝ}
    {w : ℕ → ℝ} (hw : ∀ t, 0 ≤ w t)
    (hs : Summable (fun t => w t * (1 / 2 : ℝ) ^ t))
    (C : ℝ) (hz : Tendsto z l (𝓝 0))
    (hrange : ∀ᶠ a in l, 0 ≤ z a ∧ z a ≤ 1 / 2)
    (hcenter : ∀ a x, f a 0 x = g x)
    (hpos : ∀ᶠ a in l, ∀ t : ℕ, ∀ x ∈ s,
      ‖f a (t + 1) x‖ ≤ C * (w t * z a ^ (t + 1)))
    (hneg : ∀ᶠ a in l, ∀ t : ℕ, ∀ x ∈ s,
      ‖f a (-(t + 1)) x‖ ≤ C * (w t * z a ^ (t + 1))) :
    TendstoUniformlyOn (fun a x => ∑' p : ℤ, f a p x) g l s := by
  have hlim : Tendsto (fun a => 2 * C * (∑' t, w t * z a ^ (t + 1))) l (𝓝 0) := by
    simpa using (tendsto_weighted_tail_zero hw hs hz hrange).const_mul (2 * C)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hsmall : ∀ᶠ a in l, 2 * C * (∑' t, w t * z a ^ (t + 1)) < ε :=
    hlim.eventually (gt_mem_nhds hε)
  filter_upwards [hrange, hpos, hneg, hsmall] with a ha hp hm he x hx
  have hnorm := norm_tsum_int_sub_center_le_weighted_bound
    (f := fun p => f a p x) (C := C) hw hs ha.1 ha.2
    (fun t => hp t x hx) (fun t => hm t x hx)
  simpa only [dist_eq_norm, norm_sub_rev, hcenter] using hnorm.trans_lt he
end
section
open Nagata.W07
def thetaDiskMajorant (n K R z : ℝ) (c : ℕ) (p : ℤ) : ℝ :=
  Real.exp (|K| * R) * (|K| + n * (p.natAbs : ℝ)) ^ c * z ^ p.natAbs
theorem summable_thetaDiskMajorant {n z : ℝ} (hn : 0 ≤ n)
    (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2) (K R : ℝ) (c : ℕ) :
    Summable (thetaDiskMajorant n K R z c) := by
  have hw : ∀ t : ℕ, 0 ≤ (|K| + n * ((t + 1 : ℕ) : ℝ)) ^ c := fun t => by positivity
  have hs := (summable_weighted_tail hw
    (summable_affine_weighted_half (abs_nonneg K) hn c) hz hzhalf).mul_left
      (Real.exp (|K| * R))
  have hnat (t : ℕ) : ((t : ℤ) + 1).natAbs = t + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Int.natAbs_natCast (t + 1)
  have hp : Summable (fun t : ℕ => thetaDiskMajorant n K R z c (t + 1)) := by
    simpa only [thetaDiskMajorant, hnat, mul_assoc] using hs
  have hm : Summable (fun t : ℕ => thetaDiskMajorant n K R z c (-(t + 1))) := by
    simpa only [thetaDiskMajorant, Int.natAbs_neg, hnat, mul_assoc] using hs
  exact ((summable_nat_add_iff (f := fun t : ℕ => thetaDiskMajorant n K R z c t) 1).1 hp).of_nat_of_neg_add_one hm
end
section
open Filter Topology
open Nagata.W07
def normalizedThetaSeries (n a K : ℝ) (ε : ℂ) (τ : ℝ) (x : ℂ) : ℂ :=
  ∑' p : ℤ, normalizedThetaTerm n a K ε τ p x
def normalizedThetaDerivativeSeries (n a K : ℝ) (ε : ℂ) (τ : ℝ)
    (c : ℕ) (x : ℂ) : ℂ :=
  ∑' p : ℤ, normalizedThetaDerivativeTerm n a K ε τ c p x
@[simp] theorem normalizedThetaDerivativeSeries_zero (n a K : ℝ) (ε : ℂ)
    (τ : ℝ) (x : ℂ) :
    normalizedThetaDerivativeSeries n a K ε τ 0 x = normalizedThetaSeries n a K ε τ x := by
  simp [normalizedThetaDerivativeSeries, normalizedThetaSeries]
theorem theta_geometric_parameter_tendsto_zero
    {α : Type*} {l : Filter α} {τ : α → ℝ} {n a R : ℝ}
    (ha : 0 < a) (han : a < n) (hτ : Tendsto τ l (𝓝 0)) :
    Tendsto (fun j => Real.exp (n * R) * τ j ^ thetaMargin n a) l (𝓝 0) := by
  have hδ := thetaMargin_pos ha han
  have hc := (Real.continuousAt_rpow_const 0 (thetaMargin n a) (Or.inr hδ.le)).tendsto.comp hτ
  simpa only [Real.zero_rpow hδ.ne', mul_zero, Function.comp_def] using
    hc.const_mul (Real.exp (n * R))
theorem tendstoUniformlyOn_normalizedThetaDerivativeSeries
    {α : Type*} {l : Filter α} {τ : α → ℝ} {n a K R : ℝ} {ε : ℂ}
    (ha : 0 < a) (han : a < n) (hε : ‖ε‖ = 1) (hR : 0 ≤ R)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) (c : ℕ) :
    TendstoUniformlyOn (fun j => normalizedThetaDerivativeSeries n a K ε (τ j) c)
      (fun x => (K : ℂ) ^ c * Complex.exp ((K : ℂ) * x)) l
      {x : ℂ | ‖x‖ ≤ R} := by
  have hn : 0 ≤ n := le_of_lt (lt_trans ha han)
  let z : α → ℝ := fun j => Real.exp (n * R) * τ j ^ thetaMargin n a
  have hz : Tendsto z l (𝓝 0) := theta_geometric_parameter_tendsto_zero ha han hτ
  have hzhalf : ∀ᶠ j in l, z j < 1 / 2 := hz.eventually (gt_mem_nhds (by norm_num))
  have hτone : ∀ᶠ j in l, τ j < 1 := hτ.eventually (gt_mem_nhds zero_lt_one)
  have hrange : ∀ᶠ j in l, 0 ≤ z j ∧ z j ≤ 1 / 2 := by
    filter_upwards [hτpos, hzhalf] with j hj hzj
    exact ⟨mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hj.le _), hzj.le⟩
  apply tendstoUniformlyOn_tsum_int_center_of_weighted_bound
    (w := fun t : ℕ => (|K| + n * ((t + 1 : ℕ) : ℝ)) ^ c)
    (fun t => by positivity) (summable_affine_weighted_half (abs_nonneg K) hn c)
    (Real.exp (|K| * R)) hz hrange
  · intro j x
    exact normalizedThetaDerivativeTerm_zero_index n a K ε (τ j) c x
  · filter_upwards [hτpos, hτone] with j ht ht1 t x hx
    have hb := norm_normalizedThetaDerivativeTerm_le (a := a) (K := K)
      hn ht ht1.le hε hR hx c (((t + 1 : ℕ) : ℤ))
    simp only [Int.natAbs_natCast] at hb
    simpa only [Nat.cast_add, Nat.cast_one, mul_assoc, z] using hb
  · filter_upwards [hτpos, hτone] with j ht ht1 t x hx
    have hb := norm_normalizedThetaDerivativeTerm_le (a := a) (K := K)
      hn ht ht1.le hε hR hx c (-((t + 1 : ℕ) : ℤ))
    simp only [Int.natAbs_neg, Int.natAbs_natCast] at hb
    simpa only [Nat.cast_add, Nat.cast_one, mul_assoc, z] using hb
theorem tendstoUniformlyOn_normalizedThetaSeries
    {α : Type*} {l : Filter α} {τ : α → ℝ} {n a K R : ℝ} {ε : ℂ}
    (ha : 0 < a) (han : a < n) (hε : ‖ε‖ = 1) (hR : 0 ≤ R)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) :
    TendstoUniformlyOn (fun j => normalizedThetaSeries n a K ε (τ j))
      (fun x => Complex.exp ((K : ℂ) * x)) l {x : ℂ | ‖x‖ ≤ R} := by
  have h := tendstoUniformlyOn_normalizedThetaDerivativeSeries (K := K) ha han hε hR hτ hτpos 0
  change TendstoUniformlyOn (fun j x => normalizedThetaDerivativeSeries n a K ε (τ j) 0 x)
    (fun x => (K : ℂ) ^ 0 * Complex.exp ((K : ℂ) * x)) l {x : ℂ | ‖x‖ ≤ R} at h
  simpa only [normalizedThetaDerivativeSeries_zero, pow_zero, one_mul] using h
theorem tendstoLocallyUniformlyOn_normalizedThetaSeries
    {α : Type*} {l : Filter α} {τ : α → ℝ} {n a K : ℝ} {ε : ℂ}
    (ha : 0 < a) (han : a < n) (hε : ‖ε‖ = 1)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) :
    TendstoLocallyUniformlyOn (fun j => normalizedThetaSeries n a K ε (τ j))
      (fun x => Complex.exp ((K : ℂ) * x)) l Set.univ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro S hS hSc
  obtain ⟨R, hR⟩ := hSc.exists_bound_of_continuousOn (f := fun x : ℂ => x) continuous_id.continuousOn
  apply (tendstoUniformlyOn_normalizedThetaSeries ha han hε
    (le_max_right R 0) hτ hτpos).mono
  intro x hx
  exact (hR x hx).trans (le_max_left R 0)
end
section
open Nagata.W07
theorem hasDerivAt_normalizedThetaDerivativeTerm
    (n a K : ℝ) (ε : ℂ) (τ : ℝ) (c : ℕ) (p : ℤ) (x : ℂ) :
    HasDerivAt (normalizedThetaDerivativeTerm n a K ε τ c p)
      (normalizedThetaDerivativeTerm n a K ε τ (c + 1) p x) x := by
  let B : ℂ := ((K + n * (p : ℝ) : ℝ) : ℂ)
  let A : ℂ := ε ^ (-p) * ((τ ^ thetaExponent n a (p : ℝ) : ℝ) : ℂ)
  have h := ((((hasDerivAt_id x).const_mul B).cexp).const_mul A).const_mul (B ^ c)
  apply h.congr_deriv
  dsimp [normalizedThetaDerivativeTerm, normalizedThetaTerm, A, B]
  ring
end
section
open Filter Topology
open Nagata.W07
theorem deriv_normalizedThetaDerivativeSeries
    {n a K τ R : ℝ} {ε x : ℂ}
    (hn : 0 ≤ n) (hτ : 0 < τ) (hτone : τ ≤ 1) (hε : ‖ε‖ = 1)
    (hR : 0 ≤ R) (hzhalf : Real.exp (n * R) * τ ^ thetaMargin n a ≤ 1 / 2)
    (hx : ‖x‖ < R) (c : ℕ) :
    deriv (normalizedThetaDerivativeSeries n a K ε τ c) x =
      normalizedThetaDerivativeSeries n a K ε τ (c + 1) x := by
  let z := Real.exp (n * R) * τ ^ thetaMargin n a
  have hz : 0 ≤ z := mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hτ.le _)
  have hs := summable_thetaDiskMajorant hn hz hzhalf K R c
  have hsum := Complex.hasSum_deriv_of_summable_norm hs
    (F := fun p => normalizedThetaDerivativeTerm n a K ε τ c p)
    (U := {y : ℂ | ‖y‖ < R})
    (fun p y hy => (hasDerivAt_normalizedThetaDerivativeTerm n a K ε τ c p y).differentiableAt.differentiableWithinAt)
    (isOpen_lt continuous_norm continuous_const)
    (fun p y hy => norm_normalizedThetaDerivativeTerm_le hn hτ hτone hε hR hy.le c p) hx
  have heq : (fun p : ℤ => deriv (normalizedThetaDerivativeTerm n a K ε τ c p) x) =
      (fun p : ℤ => normalizedThetaDerivativeTerm n a K ε τ (c + 1) p x) := by
    funext p
    exact (hasDerivAt_normalizedThetaDerivativeTerm n a K ε τ c p x).deriv
  rw [heq] at hsum
  exact hsum.tsum_eq.symm
theorem iteratedDeriv_normalizedThetaSeries
    {n a K τ R : ℝ} {ε x : ℂ}
    (hn : 0 ≤ n) (hτ : 0 < τ) (hτone : τ ≤ 1) (hε : ‖ε‖ = 1)
    (hR : 0 ≤ R) (hzhalf : Real.exp (n * R) * τ ^ thetaMargin n a ≤ 1 / 2)
    (hx : ‖x‖ < R) (c : ℕ) :
    iteratedDeriv c (normalizedThetaSeries n a K ε τ) x =
      normalizedThetaDerivativeSeries n a K ε τ c x := by
  induction c generalizing x with
  | zero => simp
  | succ c ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv c (normalizedThetaSeries n a K ε τ) =ᶠ[𝓝 x]
        normalizedThetaDerivativeSeries n a K ε τ c := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
      exact ih hy
    rw [heq.deriv_eq]
    exact deriv_normalizedThetaDerivativeSeries hn hτ hτone hε hR hzhalf hx c
theorem tendstoUniformlyOn_iteratedDeriv_normalizedThetaSeries
    {α : Type*} {l : Filter α} {τ : α → ℝ} {n a K R : ℝ} {ε : ℂ}
    (ha : 0 < a) (han : a < n) (hε : ‖ε‖ = 1) (hR : 0 ≤ R)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) (c : ℕ) :
    TendstoUniformlyOn (fun j => iteratedDeriv c (normalizedThetaSeries n a K ε (τ j)))
      (fun x => (K : ℂ) ^ c * Complex.exp ((K : ℂ) * x)) l
      {x : ℂ | ‖x‖ ≤ R} := by
  have hbase := tendstoUniformlyOn_normalizedThetaDerivativeSeries (K := K) ha han hε hR hτ hτpos c
  apply hbase.congr
  have hparam := theta_geometric_parameter_tendsto_zero (R := R + 1) ha han hτ
  have hhalf : ∀ᶠ j in l, Real.exp (n * (R + 1)) * τ j ^ thetaMargin n a < 1 / 2 :=
    hparam.eventually (gt_mem_nhds (by norm_num))
  have hone : ∀ᶠ j in l, τ j < 1 := hτ.eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [hτpos, hhalf, hone] with j hj hh ho x hx
  exact (iteratedDeriv_normalizedThetaSeries (le_of_lt (lt_trans ha han)) hj ho.le hε
    (by linarith) hh.le (by dsimp at hx; linarith) c).symm
theorem tendsto_iteratedDeriv_normalizedThetaSeries_zero
    {α : Type*} {l : Filter α} {τ : α → ℝ} {n a K : ℝ} {ε : ℂ}
    (ha : 0 < a) (han : a < n) (hε : ‖ε‖ = 1)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) (c : ℕ) :
    Tendsto (fun j => iteratedDeriv c (normalizedThetaSeries n a K ε (τ j)) 0)
      l (𝓝 ((K : ℂ) ^ c)) := by
  have h := (tendstoUniformlyOn_iteratedDeriv_normalizedThetaSeries
    (R := 0) (K := K) ha han hε le_rfl hτ hτpos c).tendsto_at (x := (0 : ℂ)) (by simp)
  simpa using h
end
open Filter Topology
section
open Nagata.W07
theorem summable_normalizedThetaTerm_norm_on_disk
    {n a K τ R : ℝ} {ε x : ℂ}
    (hn : 0 ≤ n) (hτ : 0 < τ) (hτone : τ ≤ 1) (hε : ‖ε‖ = 1)
    (hR : 0 ≤ R) (hzhalf : Real.exp (n * R) * τ ^ thetaMargin n a ≤ 1 / 2)
    (hx : ‖x‖ ≤ R) :
    Summable (fun p : ℤ => ‖normalizedThetaTerm n a K ε τ p x‖) := by
  have hz : 0 ≤ Real.exp (n * R) * τ ^ thetaMargin n a :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hτ.le _)
  exact (summable_thetaDiskMajorant hn hz hzhalf K R 0).of_nonneg_of_le
    (fun p => norm_nonneg _) (fun p => by
      simpa [thetaDiskMajorant] using norm_normalizedThetaTerm_le hn hτ hτone hε hR hx p)
theorem hasSum_normalizedThetaTerm_on_disk
    {n a K τ R : ℝ} {ε x : ℂ}
    (hn : 0 ≤ n) (hτ : 0 < τ) (hτone : τ ≤ 1) (hε : ‖ε‖ = 1)
    (hR : 0 ≤ R) (hzhalf : Real.exp (n * R) * τ ^ thetaMargin n a ≤ 1 / 2)
    (hx : ‖x‖ ≤ R) :
    HasSum (fun p : ℤ => normalizedThetaTerm n a K ε τ p x)
      (normalizedThetaSeries n a K ε τ x) :=
  (summable_normalizedThetaTerm_norm_on_disk hn hτ hτone hε hR hzhalf hx).of_norm.hasSum
theorem tendstoUniformlyOn_normalizedThetaSeries_partialSums
    {n a K τ R : ℝ} {ε : ℂ}
    (hn : 0 ≤ n) (hτ : 0 < τ) (hτone : τ ≤ 1) (hε : ‖ε‖ = 1)
    (hR : 0 ≤ R) (hzhalf : Real.exp (n * R) * τ ^ thetaMargin n a ≤ 1 / 2) :
    TendstoUniformlyOn
      (fun S : Finset ℤ => fun x => ∑ p ∈ S, normalizedThetaTerm n a K ε τ p x)
      (normalizedThetaSeries n a K ε τ) atTop {x : ℂ | ‖x‖ ≤ R} := by
  have hz : 0 ≤ Real.exp (n * R) * τ ^ thetaMargin n a :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hτ.le _)
  apply tendstoUniformlyOn_tsum (summable_thetaDiskMajorant hn hz hzhalf K R 0)
  intro p x hx
  simpa [thetaDiskMajorant] using norm_normalizedThetaTerm_le hn hτ hτone hε hR hx p
theorem eventually_normalizedThetaSeries_partialSums
    {α : Type*} {l : Filter α} {τ : α → ℝ} {n a K R : ℝ} {ε : ℂ}
    (ha : 0 < a) (han : a < n) (hε : ‖ε‖ = 1) (hR : 0 ≤ R)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) :
    ∀ᶠ j in l, TendstoUniformlyOn
      (fun S : Finset ℤ => fun x => ∑ p ∈ S, normalizedThetaTerm n a K ε (τ j) p x)
      (normalizedThetaSeries n a K ε (τ j)) atTop {x : ℂ | ‖x‖ ≤ R} := by
  have hp := theta_geometric_parameter_tendsto_zero (R := R) ha han hτ
  have hhalf := hp.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hone := hτ.eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [hτpos, hhalf, hone] with j hj hh ho
  exact tendstoUniformlyOn_normalizedThetaSeries_partialSums
    (le_of_lt (lt_trans ha han)) hj ho.le hε hR hh.le
end
end Nagata.W22
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W02
def gaussianConstant (c C : ℝ) : ℝ := (C + 1) ^ 2 / (4 * c)
theorem gaussian_exponent_le (c C t : ℝ) (hc : 0 < c) :
    -c * t ^ 2 + C * t ≤ gaussianConstant c C - t := by
  have hid : c * gaussianConstant c C = (C + 1) ^ 2 / 4 := by
    unfold gaussianConstant
    field_simp
  apply le_of_mul_le_mul_left (a := c) _ hc
  nlinarith [sq_nonneg (c * t - (C + 1) / 2)]
theorem gaussian_exp_le (c C t : ℝ) (hc : 0 < c) :
    Real.exp (-c * t ^ 2 + C * t) ≤
      Real.exp (gaussianConstant c C) * Real.exp (-t) := by
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by simpa [sub_eq_add_neg] using gaussian_exponent_le c C t hc)
theorem summable_pow_mul_gaussian (c C : ℝ) (N : ℕ) (hc : 0 < c) :
    Summable (fun t : ℕ => (t : ℝ) ^ N * Real.exp (-c * (t : ℝ) ^ 2 + C * t)) := by
  have hsum := (Real.summable_pow_mul_exp_neg_nat_mul N (show (0 : ℝ) < 1 by norm_num)).mul_left
    (Real.exp (gaussianConstant c C))
  apply hsum.of_nonneg_of_le
  · intro t
    positivity
  · intro t
    have hb := mul_le_mul_of_nonneg_left (gaussian_exp_le c C (t : ℝ) hc)
      (pow_nonneg (Nat.cast_nonneg t) N)
    simpa only [one_mul, neg_mul, mul_neg_one, neg_one_mul, mul_comm, mul_left_comm, mul_assoc] using hb
end Nagata.W02
end
end
section
noncomputable section
namespace Nagata.W02
open Nagata.W07
def thetaGaussianDecay (n τ : ℝ) : ℝ := -Real.log τ * n / 2
def thetaGaussianLinear (n a τ R : ℝ) (ε : ℂ) : ℝ :=
  Real.log τ * (thetaMargin n a - n / 2) + n * R + |Real.log ‖ε‖|
def thetaGaussianMajorant (n a K τ R : ℝ) (ε : ℂ) (N : ℕ) (p : ℤ) : ℝ :=
  Real.exp (|K| * R) * (|K| + n) ^ N *
    Real.exp (-thetaGaussianDecay n τ * (p.natAbs : ℝ) ^ 2 +
      (thetaGaussianLinear n a τ R ε + N) * (p.natAbs : ℝ))
theorem thetaGaussianDecay_pos {n τ : ℝ} (hn : 0 < n) (hτ : 0 < τ) (hτ1 : τ < 1) :
    0 < thetaGaussianDecay n τ := by
  have hl : Real.log τ < 0 := Real.log_neg hτ hτ1
  exact div_pos (mul_pos (neg_pos.mpr hl) hn) (by norm_num)
theorem norm_zpow_le_exp_natAbs (ε : ℂ) (hε : ε ≠ 0) (p : ℤ) :
    ‖ε ^ (-p)‖ ≤ Real.exp (|Real.log ‖ε‖| * (p.natAbs : ℝ)) := by
  rw [norm_zpow, ← Real.rpow_intCast, Real.rpow_def_of_pos (norm_pos_iff.mpr hε)]
  apply Real.exp_le_exp.mpr
  rw [Int.cast_neg, natAbs_real]
  calc
    Real.log ‖ε‖ * -(p : ℝ) ≤ |Real.log ‖ε‖ * -(p : ℝ)| := le_abs_self _
    _ = |Real.log ‖ε‖| * |(p : ℝ)| := by rw [abs_mul, abs_neg]
theorem affine_frequency_pow_le (A n t : ℝ) (N : ℕ)
    (hA : 0 ≤ A) (hn : 0 ≤ n) (ht : 0 ≤ t) :
    (A + n * t) ^ N ≤ (A + n) ^ N * Real.exp ((N : ℝ) * t) := by
  have hbase : A + n * t ≤ (A + n) * Real.exp t := by
    calc
      A + n * t ≤ (A + n) * (t + 1) := by nlinarith
      _ ≤ (A + n) * Real.exp t :=
        mul_le_mul_of_nonneg_left (Real.add_one_le_exp t) (add_nonneg hA hn)
  have hp := pow_le_pow_left₀ (add_nonneg hA (mul_nonneg hn ht)) hbase N
  simpa only [mul_pow, ← Real.exp_nat_mul] using hp
theorem norm_normalizedThetaDerivativeTerm_le_gaussian
    {n a K τ R : ℝ} {ε x : ℂ} (hn : 0 < n) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hε : ε ≠ 0) (hR : 0 ≤ R) (hx : ‖x‖ ≤ R) (N : ℕ) (p : ℤ) :
    ‖normalizedThetaDerivativeTerm n a K ε τ N p x‖ ≤
      thetaGaussianMajorant n a K τ R ε N p := by
  let t : ℝ := p.natAbs
  let A : ℝ := |K| + n * t
  let Q : ℝ := thetaMargin n a * t + n * t * (t - 1) / 2
  have ht : 0 ≤ t := Nat.cast_nonneg _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hfreq : |K + n * (p : ℝ)| ≤ A := theta_frequency_le hn.le K p
  have hεbound := norm_zpow_le_exp_natAbs ε hε p
  have hlog : Real.log τ < 0 := Real.log_neg hτ hτ1
  have hquad : Q ≤ thetaExponent n a (p : ℝ) := by
    simpa only [Q, t, natAbs_real] using thetaExponent_quadratic_lower n a (p : ℝ)
  have hpower : τ ^ thetaExponent n a (p : ℝ) ≤ Real.exp (Real.log τ * Q) := by
    rw [Real.rpow_def_of_pos hτ]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hquad hlog.le)
  have hexp : ‖Complex.exp (((K + n * (p : ℝ) : ℝ) : ℂ) * x)‖ ≤ Real.exp (A * R) := by
    apply (Complex.norm_exp_le_exp_norm _).trans
    apply Real.exp_le_exp.mpr
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hx (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hfreq hR)
  have hfreqpow := pow_le_pow_left₀ (abs_nonneg _) hfreq N
  have hnorm : ‖normalizedThetaDerivativeTerm n a K ε τ N p x‖ =
      |K + n * (p : ℝ)| ^ N * ‖ε ^ (-p)‖ * τ ^ thetaExponent n a (p : ℝ) *
        ‖Complex.exp (((K + n * (p : ℝ) : ℝ) : ℂ) * x)‖ := by
    simp only [normalizedThetaDerivativeTerm, normalizedThetaTerm, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hτ.le _), mul_assoc]
  have hmain : ‖normalizedThetaDerivativeTerm n a K ε τ N p x‖ ≤
      A ^ N * Real.exp (|Real.log ‖ε‖| * t) * Real.exp (Real.log τ * Q) *
        Real.exp (A * R) := by
    rw [hnorm]
    gcongr
  have hfreq2 := affine_frequency_pow_le |K| n t N (abs_nonneg K) hn.le ht
  calc
    _ ≤ A ^ N * Real.exp (|Real.log ‖ε‖| * t) * Real.exp (Real.log τ * Q) *
        Real.exp (A * R) := hmain
    _ ≤ ((|K| + n) ^ N * Real.exp ((N : ℝ) * t)) *
        Real.exp (|Real.log ‖ε‖| * t) * Real.exp (Real.log τ * Q) *
        Real.exp (A * R) := by gcongr
    _ = thetaGaussianMajorant n a K τ R ε N p := by
      unfold thetaGaussianMajorant thetaGaussianDecay thetaGaussianLinear
      rw [mul_comm (Real.exp (|K| * R)) ((|K| + n) ^ N)]
      simp only [mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [Q, A, t]
      ring
end Nagata.W02
end
end
section
noncomputable section
open Filter Topology
namespace Nagata.W02
open Nagata.W07 Nagata.W22
theorem summable_natAbs {f : ℕ → ℝ} (hf : Summable f) :
    Summable (fun p : ℤ => f p.natAbs) := by
  have hp : Summable (fun t : ℕ => f (t : ℤ).natAbs) := by simpa using hf
  have hm : Summable (fun t : ℕ => f (-(t + 1 : ℤ)).natAbs) := by
    have hh := (summable_nat_add_iff (f := f) 1).mpr hf
    simpa only [Int.natAbs_neg, ← Nat.cast_one (R := ℤ), ← Nat.cast_add,
      Int.natAbs_natCast] using hh
  exact hp.of_nat_of_neg_add_one hm
theorem summable_thetaGaussianMajorant {n τ : ℝ} (hn : 0 < n)
    (hτ : 0 < τ) (hτ1 : τ < 1) (a K R : ℝ) (ε : ℂ) (N : ℕ) :
    Summable (thetaGaussianMajorant n a K τ R ε N) := by
  have hc := thetaGaussianDecay_pos hn hτ hτ1
  have hs : Summable (fun t : ℕ => Real.exp (-thetaGaussianDecay n τ * (t : ℝ) ^ 2 +
      (thetaGaussianLinear n a τ R ε + N) * (t : ℝ))) := by
    simpa using summable_pow_mul_gaussian (thetaGaussianDecay n τ)
      (thetaGaussianLinear n a τ R ε + N) 0 hc
  exact (summable_natAbs hs).mul_left (Real.exp (|K| * R) * (|K| + n) ^ N)
theorem summable_normalizedThetaDerivativeTerm_allTau
    {n a K τ : ℝ} {ε : ℂ} (hn : 0 < n) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hε : ε ≠ 0) (N : ℕ) (x : ℂ) :
    Summable (fun p : ℤ => ‖normalizedThetaDerivativeTerm n a K ε τ N p x‖) := by
  exact (summable_thetaGaussianMajorant hn hτ hτ1 a K ‖x‖ ε N).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun p => norm_normalizedThetaDerivativeTerm_le_gaussian
      hn hτ hτ1 hε (norm_nonneg x) le_rfl N p)
theorem tendstoUniformlyOn_normalizedThetaDerivativeSeries_allTau
    {n a K τ R : ℝ} {ε : ℂ} (hn : 0 < n) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hε : ε ≠ 0) (hR : 0 ≤ R) (N : ℕ) :
    TendstoUniformlyOn
      (fun S : Finset ℤ => fun x => ∑ p ∈ S, normalizedThetaDerivativeTerm n a K ε τ N p x)
      (normalizedThetaDerivativeSeries n a K ε τ N) atTop {x : ℂ | ‖x‖ ≤ R} := by
  apply tendstoUniformlyOn_tsum (summable_thetaGaussianMajorant hn hτ hτ1 a K R ε N)
  intro p x hx
  exact norm_normalizedThetaDerivativeTerm_le_gaussian hn hτ hτ1 hε hR hx N p
theorem differentiable_normalizedThetaDerivativeSeries_allTau
    {n a K τ : ℝ} {ε : ℂ} (hn : 0 < n) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hε : ε ≠ 0) (N : ℕ) :
    Differentiable ℂ (normalizedThetaDerivativeSeries n a K ε τ N) := by
  intro x
  let R : ℝ := ‖x‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hu := tendstoUniformlyOn_normalizedThetaDerivativeSeries_allTau
    (a := a) (K := K) hn hτ hτ1 hε hR N
  have hlocal := (hu.mono (show {z : ℂ | ‖z‖ < R} ⊆ {z : ℂ | ‖z‖ ≤ R}
    from fun z hz => (show ‖z‖ < R from hz).le)).tendstoLocallyUniformlyOn
  have hfinite : ∀ S : Finset ℤ, DifferentiableOn ℂ
      (fun z => ∑ p ∈ S, normalizedThetaDerivativeTerm n a K ε τ N p z)
      {z : ℂ | ‖z‖ < R} := by
    intro S
    apply DifferentiableOn.fun_sum
    intro p hp
    have hd : Differentiable ℂ (normalizedThetaDerivativeTerm n a K ε τ N p) := by
      unfold normalizedThetaDerivativeTerm normalizedThetaTerm
      exact (differentiable_const _).mul
        ((differentiable_const _).mul ((differentiable_const _).mul differentiable_id).cexp)
    exact hd.differentiableOn
  have hU : IsOpen {z : ℂ | ‖z‖ < R} := isOpen_lt continuous_norm continuous_const
  have hdiff := hlocal.differentiableOn (Eventually.of_forall hfinite) hU
  exact hdiff.differentiableAt (hU.mem_nhds (by dsimp [R]; simp))
theorem differentiable_normalizedThetaSeries_allTau
    {n a K τ : ℝ} {ε : ℂ} (hn : 0 < n) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hε : ε ≠ 0) : Differentiable ℂ (normalizedThetaSeries n a K ε τ) := by
  have he : normalizedThetaDerivativeSeries n a K ε τ 0 = normalizedThetaSeries n a K ε τ := by
    funext x
    exact normalizedThetaDerivativeSeries_zero n a K ε τ x
  rw [← he]
  exact differentiable_normalizedThetaDerivativeSeries_allTau (a := a) (K := K) hn hτ hτ1 hε 0
end Nagata.W02
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W08
open Nagata.W07
def thetaJacobiParameter (n τ : ℝ) : ℂ :=
  ((n * Real.log τ : ℝ) : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)
theorem thetaJacobiParameter_im_pos {n τ : ℝ}
    (hn : 0 < n) (hτ : 0 < τ) (hτone : τ < 1) :
    0 < (thetaJacobiParameter n τ).im := by
  have hnlog : n * Real.log τ < 0 := mul_neg_of_pos_of_neg hn (Real.log_neg hτ hτone)
  have htwoPi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hden : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hdenpos := Complex.normSq_pos.mpr hden
  have hquot : n * Real.log τ * (2 * Real.pi) /
      Complex.normSq (2 * (Real.pi : ℂ) * Complex.I) < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hnlog htwoPi) hdenpos
  simpa [thetaJacobiParameter, Complex.div_im, Complex.mul_re, Complex.mul_im] using
    neg_pos.mpr hquot
theorem normalizedThetaTerm_integerPeriod (n K k : ℤ) (a : ℝ) (ε : ℂ) (τ : ℝ)
    (p : ℤ) (x : ℂ) :
    normalizedThetaTerm (n : ℝ) a (K : ℝ) ε τ p
        (x + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) =
      normalizedThetaTerm (n : ℝ) a (K : ℝ) ε τ p x := by
  have hfreq : (((K : ℝ) + (n : ℝ) * (p : ℝ) : ℝ) : ℂ) =
      ((K + n * p : ℤ) : ℂ) := by push_cast; rfl
  unfold normalizedThetaTerm
  rw [hfreq, mul_add, Complex.exp_add]
  have hexp : Complex.exp (((K + n * p : ℤ) : ℂ) *
      ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) = 1 := by
    rw [← mul_assoc, ← Int.cast_mul]
    exact Complex.exp_int_mul_two_pi_mul_I ((K + n * p) * k)
  rw [hexp, mul_one]
theorem normalizedThetaSeries_integerPeriod (n K k : ℤ) (a : ℝ) (ε : ℂ) (τ : ℝ)
    (x : ℂ) :
    (∑' p : ℤ, normalizedThetaTerm (n : ℝ) a (K : ℝ) ε τ p
      (x + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) =
    (∑' p : ℤ, normalizedThetaTerm (n : ℝ) a (K : ℝ) ε τ p x) :=
  tsum_congr fun p ↦ normalizedThetaTerm_integerPeriod n K k a ε τ p x
theorem normalizedThetaTerm_eq_singleExp (n a K : ℝ) {ε : ℂ} (hε : ε ≠ 0)
    {τ : ℝ} (hτ : 0 < τ) (p : ℤ) (x : ℂ) :
    normalizedThetaTerm n a K ε τ p x =
      Complex.exp (((-p : ℤ) : ℂ) * Complex.log ε +
        ((Real.log τ * thetaExponent n a (p : ℝ) : ℝ) : ℂ) +
        (((K + n * (p : ℝ) : ℝ) : ℂ) * x)) := by
  have heps : ε ^ (-p) = Complex.exp (((-p : ℤ) : ℂ) * Complex.log ε) := by
    rw [Complex.exp_int_mul, Complex.exp_log hε]
  unfold normalizedThetaTerm
  rw [heps, Real.rpow_def_of_pos hτ, Complex.ofReal_exp,
    ← Complex.exp_add, ← Complex.exp_add]
theorem normalizedThetaTerm_realShift_index (n a K : ℝ) {ε : ℂ} (hε : ε ≠ 0)
    {τ : ℝ} (hτ : 0 < τ) (p : ℤ) (x : ℂ) :
    normalizedThetaTerm n a K ε τ p (x + (Real.log τ : ℂ)) =
      ((ε * ((τ ^ (K - a) : ℝ) : ℂ)) * Complex.exp (-(n : ℂ) * x)) *
        normalizedThetaTerm n a K ε τ (p + 1) x := by
  have hscalar : ε * ((τ ^ (K - a) : ℝ) : ℂ) =
      Complex.exp (Complex.log ε + ((Real.log τ * (K - a) : ℝ) : ℂ)) := by
    rw [Complex.exp_add, Complex.exp_log hε, Real.rpow_def_of_pos hτ, Complex.ofReal_exp]
  rw [normalizedThetaTerm_eq_singleExp n a K hε hτ,
    normalizedThetaTerm_eq_singleExp n a K hε hτ, hscalar,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  unfold thetaExponent
  push_cast
  ring
theorem normalizedThetaSeries_realShift (n a K : ℝ) {ε : ℂ} (hε : ε ≠ 0)
    {τ : ℝ} (hτ : 0 < τ) (x : ℂ) :
    (∑' p : ℤ, normalizedThetaTerm n a K ε τ p (x + (Real.log τ : ℂ))) =
      (ε * ((τ ^ (K - a) : ℝ) : ℂ)) * Complex.exp (-(n : ℂ) * x) *
        (∑' p : ℤ, normalizedThetaTerm n a K ε τ p x) := by
  simp_rw [normalizedThetaTerm_realShift_index n a K hε hτ]
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.addRight (1 : ℤ)).tsum_eq (fun p : ℤ ↦ normalizedThetaTerm n a K ε τ p x)
end Nagata.W08
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W21
abbrev MultiplicativeLineCover (R : Type*) [CommMonoid R] := Rˣ × R
def multiplierStep {R : Type*} [CommMonoid R] (τ γ : Rˣ) (n : ℤ) :
    Equiv.Perm (MultiplicativeLineCover R) where
  toFun p := (τ * p.1, (γ * p.1 ^ (-n)) • p.2)
  invFun p := (τ⁻¹ * p.1, (γ * (τ⁻¹ * p.1) ^ (-n))⁻¹ • p.2)
  left_inv := by
    rintro ⟨z, t⟩
    change (τ⁻¹ * (τ * z), (γ * (τ⁻¹ * (τ * z)) ^ (-n))⁻¹ •
      ((γ * z ^ (-n)) • t)) = (z, t)
    rw [inv_mul_cancel_left, inv_smul_smul]
  right_inv := by
    rintro ⟨z, t⟩
    change (τ * (τ⁻¹ * z), (γ * (τ⁻¹ * z) ^ (-n)) •
      ((γ * (τ⁻¹ * z) ^ (-n))⁻¹ • t)) = (z, t)
    rw [mul_inv_cancel_left, smul_inv_smul]
def multiplierIterate {R : Type*} [CommMonoid R] (τ γ : Rˣ) (n k : ℤ) :
    Equiv.Perm (MultiplicativeLineCover R) := multiplierStep τ γ n ^ k
@[simp] theorem multiplierIterate_zero {R : Type*} [CommMonoid R]
    (τ γ : Rˣ) (n : ℤ) (p : MultiplicativeLineCover R) :
    multiplierIterate τ γ n 0 p = p := by simp [multiplierIterate]
theorem multiplierIterate_add {R : Type*} [CommMonoid R]
    (τ γ : Rˣ) (n k l : ℤ) (p : MultiplicativeLineCover R) :
    multiplierIterate τ γ n (k + l) p =
      multiplierIterate τ γ n k (multiplierIterate τ γ n l p) := by
  simp only [multiplierIterate, zpow_add, Equiv.Perm.mul_apply]
def multiplierOrbitSetoid {R : Type*} [CommMonoid R] (τ γ : Rˣ) (n : ℤ) :
    Setoid (MultiplicativeLineCover R) where
  r p q := ∃ k : ℤ, multiplierIterate τ γ n k p = q
  iseqv := {
    refl := fun p ↦ ⟨0, multiplierIterate_zero τ γ n p⟩
    symm := by
      intro p q h
      obtain ⟨k, hk⟩ := h
      refine ⟨-k, ?_⟩
      calc
        multiplierIterate τ γ n (-k) q =
            multiplierIterate τ γ n (-k) (multiplierIterate τ γ n k p) := by rw [hk]
        _ = multiplierIterate τ γ n (-k + k) p :=
          (multiplierIterate_add τ γ n (-k) k p).symm
        _ = p := by rw [Int.add_left_neg, multiplierIterate_zero]
    trans := by
      intro p q r hp hq
      obtain ⟨k, hk⟩ := hp
      obtain ⟨l, hl⟩ := hq
      refine ⟨l + k, ?_⟩
      rw [multiplierIterate_add, hk, hl] }
def MultiplierQuotient {R : Type*} [CommMonoid R] (τ γ : Rˣ) (n : ℤ) : Type _ :=
  Quotient (multiplierOrbitSetoid τ γ n)
instance {R : Type*} [CommMonoid R] (τ γ : Rˣ) (n : ℤ) :
    Nonempty (MultiplierQuotient τ γ n) :=
  ⟨Quotient.mk _ (1, 1)⟩
end Nagata.W21
end
section
namespace Nagata.W21
def torusOrbitSetoid {G : Type*} [CommGroup G] (τ : G) : Setoid G where
  r z z' := ∃ k : ℤ, τ ^ k * z = z'
  iseqv := {
    refl := fun z ↦ ⟨0, by rw [zpow_zero, one_mul]⟩
    symm := by
      intro z z' h
      obtain ⟨k, hk⟩ := h
      refine ⟨-k, ?_⟩
      rw [← hk, ← mul_assoc, ← zpow_add, Int.add_left_neg, zpow_zero, one_mul]
    trans := by
      intro z z' z'' h h'
      obtain ⟨k, hk⟩ := h
      obtain ⟨l, hl⟩ := h'
      exact ⟨l + k, by rw [zpow_add, mul_assoc, hk, hl]⟩ }
def TorusPoint {G : Type*} [CommGroup G] (τ : G) : Type _ :=
  Quotient (torusOrbitSetoid τ)
def torusPointMk {G : Type*} [CommGroup G] (τ z : G) : TorusPoint τ :=
  Quotient.mk _ z
instance {G : Type*} [CommGroup G] (τ : G) : Nonempty (TorusPoint τ) :=
  ⟨torusPointMk τ 1⟩
end Nagata.W21
end
section
namespace Nagata.W21
end Nagata.W21
end
section
namespace Nagata.W21
instance torusPointTopologicalSpace {G : Type*} [CommGroup G] [TopologicalSpace G]
    (τ : G) : TopologicalSpace (TorusPoint τ) :=
  inferInstanceAs (TopologicalSpace (Quotient (torusOrbitSetoid τ)))
instance multiplierQuotientTopologicalSpace {R : Type*} [CommMonoid R]
    [TopologicalSpace R] [TopologicalSpace Rˣ] (τ γ : Rˣ) (n : ℤ) :
    TopologicalSpace (MultiplierQuotient τ γ n) :=
  inferInstanceAs (TopologicalSpace (Quotient (multiplierOrbitSetoid τ γ n)))
end Nagata.W21
end
section
namespace Nagata.W21
section TopologicalAction
variable {R : Type*} [CommMonoid R] [TopologicalSpace R] [TopologicalSpace Rˣ]
  [IsTopologicalGroup Rˣ] [ContinuousSMul Rˣ R]
 theorem continuous_multiplierStep (τ γ : Rˣ) (n : ℤ) :
    Continuous (multiplierStep τ γ n) := by
  change Continuous (fun p : MultiplicativeLineCover R ↦
    (τ * p.1, (γ * p.1 ^ (-n)) • p.2))
  exact (continuous_const.mul continuous_fst).prodMk
    ((continuous_const.mul (continuous_fst.zpow (-n))).smul continuous_snd)
 theorem continuous_multiplierStep_inv (τ γ : Rˣ) (n : ℤ) :
    Continuous ((multiplierStep τ γ n)⁻¹ : Equiv.Perm (MultiplicativeLineCover R)) := by
  change Continuous (fun p : MultiplicativeLineCover R ↦
    (τ⁻¹ * p.1, (γ * (τ⁻¹ * p.1) ^ (-n))⁻¹ • p.2))
  exact (continuous_const.mul continuous_fst).prodMk
    ((continuous_const.mul ((continuous_const.mul continuous_fst).zpow (-n))).inv.smul
      continuous_snd)
end TopologicalAction
section LocalChart
variable {R : Type*} [CommMonoid R] [TopologicalSpace R] [TopologicalSpace Rˣ]
variable [IsTopologicalGroup Rˣ] [ContinuousSMul Rˣ R]
end LocalChart
end Nagata.W21
end
end OAI
end
section
namespace OAI
section
namespace Nagata.LocalDivision
open Filter Topology
theorem exists_analytic_quotient_at_simple_zero {f P : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hP : AnalyticAt ℂ P z₀)
    (hP0 : P z₀ = 0) (hP' : deriv P z₀ ≠ 0) (k : ℕ)
    (horder : (k : ℕ∞) ≤ analyticOrderAt f z₀) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧
      ∀ᶠ z in 𝓝 z₀, f z = P z ^ k * g z := by
  have hPo : analyticOrderAt P z₀ = (1 : ℕ) :=
    hP.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hP0 hP'
  obtain ⟨u, hu, hu0, hPu⟩ := hP.analyticOrderAt_eq_natCast.mp hPo
  obtain ⟨v, hv, hfv⟩ := (natCast_le_analyticOrderAt hf).mp horder
  refine ⟨fun z => v z / u z ^ k, hv.div (hu.pow k) (pow_ne_zero k hu0), ?_⟩
  have hune : ∀ᶠ z in 𝓝 z₀, u z ≠ 0 := hu.continuousAt.eventually_ne hu0
  filter_upwards [hPu, hfv, hune] with z hPu hfv hu
  simp only [pow_one, smul_eq_mul] at hPu hfv
  rw [hPu, hfv, mul_pow]
  field_simp
theorem analytic_quotient_at_nonzero {f P : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hP : AnalyticAt ℂ P z₀)
    (hP0 : P z₀ ≠ 0) (k : ℕ) :
    AnalyticAt ℂ (fun z => f z / P z ^ k) z₀ :=
  hf.div (hP.pow k) (pow_ne_zero k hP0)
theorem exists_analytic_quotient {f P : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hP : AnalyticAt ℂ P z₀) (k : ℕ)
    (hzero : P z₀ = 0 → deriv P z₀ ≠ 0 ∧
      (k : ℕ∞) ≤ analyticOrderAt f z₀) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧
      ∀ᶠ z in 𝓝 z₀, f z = P z ^ k * g z := by
  by_cases hP0 : P z₀ = 0
  · exact exists_analytic_quotient_at_simple_zero hf hP hP0 (hzero hP0).1 k
      (hzero hP0).2
  · refine ⟨fun z => f z / P z ^ k, analytic_quotient_at_nonzero hf hP hP0 k, ?_⟩
    have hPne : ∀ᶠ z in 𝓝 z₀, P z ≠ 0 := hP.continuousAt.eventually_ne hP0
    filter_upwards [hPne] with z hz
    field_simp
end Nagata.LocalDivision
end
section
namespace Nagata.LocalDivision
open Filter Topology
theorem analytic_quotient_germ_unique {f P g h : ℂ → ℂ} {z₀ : ℂ} (k : ℕ)
    (hP : AnalyticAt ℂ P z₀) (hPfin : analyticOrderAt P z₀ ≠ ⊤)
    (hg : AnalyticAt ℂ g z₀) (hh : AnalyticAt ℂ h z₀)
    (hfg : ∀ᶠ z in 𝓝 z₀, f z = P z ^ k * g z)
    (hfh : ∀ᶠ z in 𝓝 z₀, f z = P z ^ k * h z) :
    g =ᶠ[𝓝 z₀] h := by
  have hPn : ∀ᶠ z in 𝓝[≠] z₀, P z ≠ 0 :=
    hP.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun hz => hPfin (analyticOrderAt_eq_top.mpr hz))
  have heq : g =ᶠ[𝓝[≠] z₀] h := by
    filter_upwards [hPn, hfg.filter_mono nhdsWithin_le_nhds,
      hfh.filter_mono nhdsWithin_le_nhds] with z hz hfg hfh
    exact mul_left_cancel₀ (pow_ne_zero k hz) (hfg.symm.trans hfh)
  exact (hg.frequently_eq_iff_eventually_eq hh).mp heq.frequently
theorem continuous_eq_at_of_eq_off_divisor {P g h : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hU : IsOpen U) (hz₀ : z₀ ∈ U) (hP : AnalyticAt ℂ P z₀)
    (hPfin : analyticOrderAt P z₀ ≠ ⊤) (hg : ContinuousAt g z₀)
    (hh : ContinuousAt h z₀)
    (heq : ∀ z ∈ U, P z ≠ 0 → g z = h z) : g z₀ = h z₀ := by
  have hPn : ∀ᶠ z in 𝓝[≠] z₀, P z ≠ 0 :=
    hP.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun hz => hPfin (analyticOrderAt_eq_top.mpr hz))
  have hlocal : g =ᶠ[𝓝[≠] z₀] h := by
    filter_upwards [hPn, (show ∀ᶠ z in 𝓝 z₀, z ∈ U from hU.mem_nhds hz₀).filter_mono nhdsWithin_le_nhds]
      with z hz hzu
    exact heq z hzu hz
  exact tendsto_nhds_unique_of_eventuallyEq
    (hg.tendsto.mono_left nhdsWithin_le_nhds)
    (hh.tendsto.mono_left nhdsWithin_le_nhds) hlocal
theorem multiply_power_injective_on {P f g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (k : ℕ) (hP : AnalyticOnNhd ℂ P U)
    (hPfin : ∀ z ∈ U, analyticOrderAt P z ≠ ⊤)
    (hf : ∀ z ∈ U, ContinuousAt f z) (hg : ∀ z ∈ U, ContinuousAt g z)
    (hmul : ∀ z ∈ U, P z ^ k * f z = P z ^ k * g z) :
    Set.EqOn f g U := by
  intro z hz
  apply continuous_eq_at_of_eq_off_divisor hU hz (hP z hz) (hPfin z hz)
    (hf z hz) (hg z hz)
  intro w hw hPw
  exact mul_left_cancel₀ (pow_ne_zero k hPw) (hmul w hw)
theorem glue_analytic_quotients {f P : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (k : ℕ) (hP : AnalyticOnNhd ℂ P U)
    (hPfin : ∀ z ∈ U, analyticOrderAt P z ≠ ⊤)
    (hlocal : ∀ z ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧
      ∀ᶠ w in 𝓝 z, f w = P w ^ k * g w) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G U ∧
      (∀ z ∈ U, f z = P z ^ k * G z) ∧ (∀ z ∉ U, G z = 0) := by
  classical
  choose g hg hfg using hlocal
  let G : ℂ → ℂ := fun z => if hz : z ∈ U then g z hz z else 0
  refine ⟨G, ?_, ?_, ?_⟩
  · intro z hz
    have heq : G =ᶠ[𝓝 z] g z hz := by
      filter_upwards [hU.mem_nhds hz, (hg z hz).eventually_analyticAt,
        (hfg z hz).eventually_nhds] with w hw hgw hfw
      have huniq := analytic_quotient_germ_unique k (hP w hw) (hPfin w hw)
        hgw (hg w hw) hfw (hfg w hw)
      simp only [G, dif_pos hw]
      exact huniq.self_of_nhds.symm
    exact (hg z hz).congr heq.symm
  · intro z hz
    simpa only [G, dif_pos hz] using (hfg z hz).self_of_nhds
  · intro z hz
    simp only [G, dif_neg hz]
theorem exists_global_analytic_quotient {f P : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) (hP : AnalyticOnNhd ℂ P U)
    (k : ℕ) (hzero : ∀ z ∈ U, P z = 0 → deriv P z ≠ 0 ∧
      (k : ℕ∞) ≤ analyticOrderAt f z) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G U ∧
      (∀ z ∈ U, f z = P z ^ k * G z) ∧ (∀ z ∉ U, G z = 0) := by
  apply glue_analytic_quotients hU k hP
  · intro z hz
    by_cases hPz : P z = 0
    · rw [(hP z hz).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hPz (hzero z hz hPz).1]
      simp
    · rw [(hP z hz).analyticOrderAt_eq_zero.mpr hPz]
      simp
  · intro z hz
    exact exists_analytic_quotient (hf z hz) (hP z hz) k (hzero z hz)
end Nagata.LocalDivision
end
section
namespace Nagata.CoefficientSpaces
open Nagata.W21
end Nagata.CoefficientSpaces
end
section
namespace Nagata.FiberCoordinateChange
open Nagata.Workers.W28
end Nagata.FiberCoordinateChange
end
section
namespace Nagata.LocalDivision
theorem quotient_transition_off_zero {T : ℂ → ℂ} {f P G A B : ℂ → ℂ}
    (k : ℕ) (z : ℂ) (hP : P z ≠ 0) (hB : B z ≠ 0)
    (hfz : f z = P z ^ k * G z) (hfT : f (T z) = P (T z) ^ k * G (T z))
    (htf : f (T z) = A z * f z) (htP : P (T z) = B z * P z) :
    G (T z) = (A z / B z ^ k) * G z := by
  have heq : P (T z) ^ k * G (T z) = A z * (P z ^ k * G z) := by
    rw [← hfT, htf, hfz]
  rw [htP, mul_pow] at heq
  have hcancel : B z ^ k * G (T z) = A z * G z := by
    apply mul_left_cancel₀ (pow_ne_zero k hP)
    calc
      P z ^ k * (B z ^ k * G (T z)) = (B z ^ k * P z ^ k) * G (T z) := by ring
      _ = A z * (P z ^ k * G z) := heq
      _ = P z ^ k * (A z * G z) := by ring
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (pow_ne_zero k hB)).mpr
  rw [mul_comm]
  exact hcancel
theorem quotient_transition_global {T : ℂ → ℂ} {f P G A B : ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) (k : ℕ)
    (hP : AnalyticOnNhd ℂ P U) (hPfin : ∀ z ∈ U, analyticOrderAt P z ≠ ⊤)
    (hTU : Set.MapsTo T U U) (hB : ∀ z ∈ U, B z ≠ 0)
    (hfactor : ∀ z ∈ U, f z = P z ^ k * G z)
    (htf : ∀ z ∈ U, f (T z) = A z * f z)
    (htP : ∀ z ∈ U, P (T z) = B z * P z)
    (hleft : ∀ z ∈ U, ContinuousAt (fun w => G (T w)) z)
    (hright : ∀ z ∈ U, ContinuousAt (fun w => (A w / B w ^ k) * G w) z) :
    ∀ z ∈ U, G (T z) = (A z / B z ^ k) * G z := by
  intro z hz
  apply continuous_eq_at_of_eq_off_divisor hU hz (hP z hz) (hPfin z hz)
    (hleft z hz) (hright z hz)
  intro w hw hPw
  exact quotient_transition_off_zero k w hPw (hB w hw) (hfactor w hw)
    (hfactor (T w) (hTU hw)) (htf w hw) (htP w hw)
end Nagata.LocalDivision
end
section
namespace Nagata.CoefficientSpaces
noncomputable def multiplySection (τ γ : ℂ) (n : ℤ) (P : ℂ → ℂ) (k : ℕ) :
    Nagata.W08.automorphicSections τ n γ →ₗ[ℂ] (ℂ → ℂ) :=
  (multiplyPower P k).comp (Nagata.W08.automorphicSections τ n γ).subtype
theorem multiplySection_injective (τ γ : ℂ) (n : ℤ) (P : ℂ → ℂ) (k : ℕ)
    (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
    (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤) :
    Function.Injective (multiplySection τ γ n P k) := by
  intro f g heq
  have hoff : Set.EqOn f.val g.val {z | z ≠ 0} := by
    apply Nagata.LocalDivision.multiply_power_injective_on
      isOpen_ne k hP hPfin
      (fun z hz => (f.property.2.1 z hz).continuousAt)
      (fun z hz => (g.property.2.1 z hz).continuousAt)
    intro z hz
    exact congrFun heq z
  apply Nagata.W08.automorphicSections_ext
  exact hoff
end Nagata.CoefficientSpaces
end
section
namespace Nagata.CoefficientSpaces
theorem quotient_multiplier_identity {γ δ z : ℂ} (hδ : δ ≠ 0) (hz : z ≠ 0)
    (n s : ℤ) (k : ℕ) :
    (γ * z ^ (-n)) / (δ * z ^ (-s)) ^ k =
      (γ / δ ^ k) * z ^ (-(n - (k : ℤ) * s)) := by
  have he : -(n - (k : ℤ) * s) = -n - (-s) * (k : ℤ) := by ring
  rw [he, zpow_sub₀ hz, zpow_mul, zpow_natCast, mul_pow]
  field_simp
theorem exists_automorphic_quotient {τ γ δ : ℂ} {n s : ℤ}
    (hτ : τ ≠ 0) (hδ : δ ≠ 0)
    (f : Nagata.W08.automorphicSections τ n γ)
    (P : Nagata.W08.automorphicSections τ s δ)
    (hf : AnalyticOnNhd ℂ f.val {z | z ≠ 0})
    (hP : AnalyticOnNhd ℂ P.val {z | z ≠ 0}) (k : ℕ)
    (hzero : ∀ z ≠ 0, P.val z = 0 → deriv P.val z ≠ 0 ∧
      (k : ℕ∞) ≤ analyticOrderAt f.val z) :
    ∃ G : Nagata.W08.automorphicSections τ (n - (k : ℤ) * s) (γ / δ ^ k),
      ∀ z ≠ 0, f.val z = P.val z ^ k * G.val z := by
  obtain ⟨G, hG, hfactor, hGoutside⟩ :=
    Nagata.LocalDivision.exists_global_analytic_quotient isOpen_ne hf hP k hzero
  have hPfin : ∀ z ≠ 0, analyticOrderAt P.val z ≠ ⊤ := by
    intro z hz
    by_cases hPz : P.val z = 0
    · rw [(hP z hz).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hPz (hzero z hz hPz).1]
      simp
    · rw [(hP z hz).analyticOrderAt_eq_zero.mpr hPz]
      simp
  have heq : ∀ z ≠ 0, G (τ * z) =
      ((γ * z ^ (-n)) / (δ * z ^ (-s)) ^ k) * G z := by
    apply Nagata.LocalDivision.quotient_transition_global isOpen_ne k hP hPfin
      (fun z hz => mul_ne_zero hτ hz)
      (fun z hz => mul_ne_zero hδ (zpow_ne_zero _ hz)) hfactor
      (fun z hz => f.property.2.2 z hz) (fun z hz => P.property.2.2 z hz)
    · intro z hz
      exact (hG (τ * z) (mul_ne_zero hτ hz)).continuousAt.comp
        (continuousAt_const.mul continuousAt_id)
    · intro z hz
      have hA : ContinuousAt (fun w : ℂ => γ * w ^ (-n)) z :=
        continuousAt_const.mul (continuousAt_zpow₀ z (-n) (Or.inl hz))
      have hB : ContinuousAt (fun w : ℂ => δ * w ^ (-s)) z :=
        continuousAt_const.mul (continuousAt_zpow₀ z (-s) (Or.inl hz))
      exact (hA.div (hB.pow k) (pow_ne_zero k
        (mul_ne_zero hδ (zpow_ne_zero _ hz)))).mul (hG z hz).continuousAt
  refine ⟨⟨G, ?_⟩, hfactor⟩
  refine ⟨hGoutside 0 (by simp), ?_, ?_⟩
  · intro z hz
    exact (hG z hz).differentiableAt
  · intro z hz
    rw [heq z hz, quotient_multiplier_identity hδ hz]
end Nagata.CoefficientSpaces
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W02
def multiplierSigma (τ : ℝ) (γ : ℂ) : ℝ := Real.log ‖γ‖ / Real.log τ
def multiplierPhase (γ : ℂ) : ℂ := γ / (‖γ‖ : ℂ)
theorem rpow_multiplierSigma {τ : ℝ} {γ : ℂ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (hγ : γ ≠ 0) :
    τ ^ multiplierSigma τ γ = ‖γ‖ := by
  have hl : Real.log τ ≠ 0 := ne_of_lt (Real.log_neg hτ hτ1)
  rw [Real.rpow_def_of_pos hτ, multiplierSigma]
  have hm : Real.log τ * (Real.log ‖γ‖ / Real.log τ) = Real.log ‖γ‖ :=
    mul_div_cancel₀ _ hl
  rw [hm, Real.exp_log (norm_pos_iff.mpr hγ)]
theorem norm_multiplierPhase {γ : ℂ} (hγ : γ ≠ 0) : ‖multiplierPhase γ‖ = 1 := by
  unfold multiplierPhase
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
    div_self (norm_ne_zero_iff.mpr hγ)]
theorem multiplier_factorization {τ : ℝ} {γ : ℂ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (hγ : γ ≠ 0) :
    γ = multiplierPhase γ * ((τ ^ multiplierSigma τ γ : ℝ) : ℂ) := by
  rw [rpow_multiplierSigma hτ hτ1 hγ]
  unfold multiplierPhase
  have hnorm : (‖γ‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hγ)
  exact (div_mul_cancel₀ γ hnorm).symm
def thetaFrameCenter (n σ : ℝ) : ℝ := (σ - 1 / 2) / n
theorem thetaFrameCenter_endpoint {n : ℝ} (hn : 0 < n) (σ : ℝ) :
    σ - thetaFrameCenter n σ * n = 1 / 2 := by
  unfold thetaFrameCenter
  rw [div_mul_cancel₀ _ (ne_of_gt hn)]
  ring
theorem half_not_integer : (1 / 2 : ℝ) ∉ Set.range (Int.cast : ℤ → ℝ) := by
  rintro ⟨z, hz⟩
  have hz0 : (0 : ℤ) < z := by
    exact_mod_cast (show (0 : ℝ) < (z : ℝ) by rw [hz]; norm_num)
  have hz1 : z < (1 : ℤ) := by
    exact_mod_cast (show (z : ℝ) < 1 by rw [hz]; norm_num)
  omega
theorem thetaFrameCenter_nonintegral {n : ℝ} (hn : 0 < n) (σ : ℝ) :
    σ - thetaFrameCenter n σ * n ∉ Set.range (Int.cast : ℤ → ℝ) := by
  rw [thetaFrameCenter_endpoint hn]
  exact half_not_integer
theorem exists_normalized_multiplier_frame {n τ : ℝ} {γ : ℂ}
    (hn : 0 < n) (hτ : 0 < τ) (hτ1 : τ < 1) (hγ : γ ≠ 0) :
    ∃ (σ x0 : ℝ) (ε : ℂ), ‖ε‖ = 1 ∧
      γ = ε * ((τ ^ σ : ℝ) : ℂ) ∧
      σ - x0 * n = 1 / 2 ∧
      σ - x0 * n ∉ Set.range (Int.cast : ℤ → ℝ) := by
  exact ⟨multiplierSigma τ γ, thetaFrameCenter n (multiplierSigma τ γ), multiplierPhase γ,
    norm_multiplierPhase hγ, multiplier_factorization hτ hτ1 hγ,
    thetaFrameCenter_endpoint hn _, thetaFrameCenter_nonintegral hn _⟩
end Nagata.W02
end
end
section
namespace Nagata.BundleArithmetic
theorem twisted_source_exponent (d m j s a : ℝ) :
    (d - 3 * j) * ((s + a) / 3) + (j - m) * s =
      (d - 3 * m) * ((s + a) / 3) + (m - j) * a := by
  ring
theorem first_interval_parameter (d m j s a Δ x₀ : ℝ)
    (hs : s = 9 * x₀ - Δ) :
    ((d - 3 * m) * ((s + a) / 3) + (m - j) * a) -
        x₀ * (3 * (d - 3 * m)) =
      (3 * (d - 3 * m)) / 9 * (a - Δ) + (m - j) * a := by
  rw [hs]
  ring
theorem second_interval_parameter (d j s a Δ x₀ : ℝ)
    (hs : s = 9 * x₀ - Δ) :
    (d - 3 * j) * ((s + a) / 3) - x₀ * (3 * (d - 3 * j)) =
      (3 * (d - 3 * j)) / 9 * (a - Δ) := by
  rw [hs]
  ring
end Nagata.BundleArithmetic
end
section
namespace Nagata.CoefficientSpaces
end Nagata.CoefficientSpaces
end
section
namespace Nagata.CoefficientSpaces
end Nagata.CoefficientSpaces
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W04.ReducibleSquare
open Polynomial
end Nagata.W04.ReducibleSquare
end
section
noncomputable section
namespace Nagata.W04.Dimension
open Polynomial
open scoped nonZeroDivisors
variable {R : Type*} [CommRing R] [IsDomain R]
section
local instance oaiLocInst8 {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] : Algebra (Polynomial R) (Polynomial A) := Polynomial.algebra R A
noncomputable local instance oaiLocInst9 {R : Type*} [CommSemiring R] {S : Submonoid R} {A : Type*} [CommSemiring A] [Algebra R A] [IsLocalization S A] : IsLocalization (S.map Polynomial.C) (Polynomial A) := Polynomial.isLocalization S A
theorem polynomial_height_le_one (I : Ideal R[X]) [I.IsPrime]
    (hC : I.comap Polynomial.C = ⊥) : I.height ≤ 1 := by
  let K := FractionRing R
  let M : Submonoid R[X] := (nonZeroDivisors R).map Polynomial.C
  have hd : Disjoint (M : Set R[X]) (I : Set R[X]) := by
    refine Set.disjoint_left.mpr ?_
    rintro p ⟨r, hr, rfl⟩ hp
    have hr0 : r = 0 := by
      have : r ∈ I.comap Polynomial.C := hp
      simpa [hC] using this
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hr) hr0
  let J : Ideal K[X] := I.map (algebraMap R[X] K[X])
  have : J.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M K[X] I inferInstance hd
  have he : J.height = I.height := IsLocalization.height_map_of_disjoint M I hd
  rw [← he]
  apply (Ideal.height_le_iff (n := 1)).mpr
  intro Q hQ hQJ
  have : Q.IsPrime := hQ
  have hQ0 : Q = ⊥ := by
    by_contra hQ0
    have : Q.IsMaximal := IsPrime.to_maximal_ideal hQ0
    exact hQJ.ne (Ideal.IsMaximal.eq_of_le inferInstance Ideal.IsPrime.ne_top' hQJ.le)
  simp [hQ0]
end
end Nagata.W04.Dimension
end
end
section
noncomputable section
namespace Nagata.W04.Dimension
open MvPolynomial
variable (K : Type*) [Field K] (n : ℕ)
variable {K n}
end Nagata.W04.Dimension
end
end
section
noncomputable section
namespace Nagata.W04.ReducibleSquare
variable {K : Type*} [Field K]
end Nagata.W04.ReducibleSquare
end
end
section
noncomputable section
namespace Nagata.W04.ReducibleSquare
open Polynomial
def markTail {K : Type*} [CommSemiring K] (k : ℕ) : K[X] :=
  ∏ j ∈ Finset.range (k - 1), (X + C ((j + 2 : ℕ) : K))
def firstMark (k i : ℕ) : ℕ := if i = 0 then k + 1 else 1
def markPolynomial {K : Type*} [CommSemiring K] (k i : ℕ) : K[X] :=
  (X + C ((firstMark k i : ℕ) : K)) * markTail k
variable {K : Type*} [Field K]
 theorem markTail_monic (k : ℕ) : (markTail k : K[X]).Monic := by
  exact monic_prod_of_monic _ _ (fun j _ => monic_X_add_C _)
 theorem markTail_natDegree (k : ℕ) : (markTail k : K[X]).natDegree = k - 1 := by
  unfold markTail
  rw [natDegree_prod_of_monic _ _ (fun j _ => monic_X_add_C _)]
  simp_rw [natDegree_X_add_C]
  simp
 theorem markPolynomial_monic (k i : ℕ) : (markPolynomial k i : K[X]).Monic :=
  (monic_X_add_C _).mul (markTail_monic k)
 theorem markPolynomial_natDegree (k i : ℕ) (hk : 0 < k) :
    (markPolynomial k i : K[X]).natDegree = k := by
  unfold markPolynomial
  rw [(monic_X_add_C _).natDegree_mul (markTail_monic k), natDegree_X_add_C,
    markTail_natDegree]
  omega
variable [CharZero K]
 theorem markTail_eval_nat_ne_zero (k n : ℕ) : (markTail k : K[X]).eval (n : K) ≠ 0 := by
  unfold markTail
  rw [eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  simp only [eval_add, eval_X, eval_C]
  exact_mod_cast (show n + (j + 2) ≠ 0 by omega)
 theorem firstMark_pos (k i : ℕ) : 0 < firstMark k i := by
  unfold firstMark
  split <;> omega
 theorem markPolynomial_eval_nat_ne_zero (k i n : ℕ) :
    (markPolynomial k i : K[X]).eval (n : K) ≠ 0 := by
  unfold markPolynomial
  rw [eval_mul, eval_add, eval_X, eval_C]
  apply mul_ne_zero _ (markTail_eval_nat_ne_zero k n)
  exact_mod_cast (show n + firstMark k i ≠ 0 by have := firstMark_pos k i; omega)
 theorem marked_linear_factors_coprime (u v : ℕ) (huv : u ≠ v) :
    IsCoprime (X + C (u : K)) (X + C (v : K)) := by
  have huv' : -(u : K) ≠ -(v : K) := by
    intro h
    have h' : (u : K) = (v : K) := neg_injective h
    exact huv (Nat.cast_injective h')
  simpa only [C_neg, sub_neg_eq_add] using
    (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr huv').isUnit)
 theorem firstMark_ne_tail (k i j : ℕ) (hj : j < k - 1) : firstMark k i ≠ j + 2 := by
  unfold firstMark
  split <;> omega
end Nagata.W04.ReducibleSquare
end
end
section
namespace Nagata.W04.ReducibleSquare
open Polynomial
end Nagata.W04.ReducibleSquare
end
section
namespace Nagata.W04.ReducibleSquare
open Polynomial
end Nagata.W04.ReducibleSquare
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W06.LineArrangement
open scoped BigOperators
def markedCoordinate (k i : ℕ) (s : Fin k) : ℕ :=
  if s.val = 0 then Nagata.W04.ReducibleSquare.firstMark k i else s.val + 1
variable {K : Type*} [Field K]
def graphValue (i : ℕ) (U : K) : K := (i : K) ^ 2 - (i : K) * U
def lineValue (i : ℕ) (U Y : K) : K := Y - graphValue i U
def markedPoint (K : Type*) [Field K] (k : ℕ) (i s : Fin k) : K × K :=
  let U : K := -(markedCoordinate k i.val s : K)
  (U, graphValue i.val U)
variable [CharZero K]
omit [CharZero K] in
theorem markedPoint_on_line (k : ℕ) (i s : Fin k) :
    lineValue i.val (markedPoint K k i s).1 (markedPoint K k i s).2 = 0 := by
  simp [markedPoint, lineValue]
def markedPoints (K : Type*) [Field K] (k : ℕ) : Finset (K × K) := by
  classical
  exact Finset.univ.image (fun p : Fin k × Fin k => markedPoint K k p.1 p.2)
end Nagata.W06.LineArrangement
end
end
section
noncomputable section
namespace Nagata.W06.LineArrangement
def additionalPoint (K : Type*) [Field K] (k : ℕ) : K × K :=
  (-((k + 2 : ℕ) : K), 0)
variable {K : Type*} [Field K] [CharZero K]
omit [CharZero K] in
theorem additionalPoint_on_zero (k : ℕ) :
    lineValue 0 (additionalPoint K k).1 (additionalPoint K k).2 = 0 := by
  simp [additionalPoint, lineValue, graphValue]
end Nagata.W06.LineArrangement
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.ProjectiveGeometry
open scoped BigOperators
abbrev PlanePoint := Projectivization ℂ (Fin 3 → ℂ)
structure MultihomogeneousEquation (r : ℕ) where
  polynomial : MvPolynomial (Fin r × Fin 3) ℂ
  multidegree : Fin r → ℕ
  homogeneous : ∀ a ∈ polynomial.support, ∀ i,
    (∑ j : Fin 3, a (i, j)) = multidegree i
abbrev ChartVariables (c : Fin 3) := {j : Fin 3 // j ≠ c}
end Nagata.ProjectiveGeometry
end
end
section
noncomputable section
namespace Nagata
open ProjectiveGeometry
open scoped BigOperators
end Nagata
end
end
section
noncomputable section
namespace Nagata.ProjectiveGeometry
def chartIndexEquiv (c : Fin 3) : Fin 2 ≃ ChartVariables c :=
  Equiv.ofBijective (fun j => ⟨c.succAbove j, Fin.succAbove_ne c j⟩) (by
    constructor
    · intro i j h
      exact Fin.succAbove_right_injective (congrArg Subtype.val h)
    · intro j
      obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq j.property
      exact ⟨i, Subtype.ext hi⟩)
@[simp] theorem chartIndexEquiv_val (c : Fin 3) (j : Fin 2) :
    (chartIndexEquiv c j).val = c.succAbove j := rfl
@[simp] theorem chartIndexEquiv_symm_succAbove (c : Fin 3) (j : Fin 2) :
    (chartIndexEquiv c).symm ⟨c.succAbove j, Fin.succAbove_ne c j⟩ = j :=
  (chartIndexEquiv c).symm_apply_apply j
end Nagata.ProjectiveGeometry
end
end
section
noncomputable section
namespace Nagata.ProjectiveGeometry
open scoped BigOperators
end Nagata.ProjectiveGeometry
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.Workers.W25
open MvPolynomial
end Nagata.Workers.W25
end
section
namespace Nagata.Workers.W25
end Nagata.Workers.W25
end
section
noncomputable section
namespace Nagata.Workers.W25
open Nagata.ProjectiveGeometry
end Nagata.Workers.W25
end
end
section
namespace Nagata.Workers.W25
end Nagata.Workers.W25
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W16
abbrev PlanePolynomial := MvPolynomial (Fin 3) ℂ
theorem homogeneous_eval_scale {σ K : Type*} [CommSemiring K]
    {F : MvPolynomial σ K} {d : ℕ} (hF : F.IsHomogeneous d)
    (x : σ → K) (a : K) :
    MvPolynomial.eval (fun i => a * x i) F = a ^ d * MvPolynomial.eval x F := by
  classical
  simp only [MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hF.degree_eq_sum_deg_support hu]
  ac_rfl
structure NonzeroHomogeneousForm (d : ℕ) where
  polynomial : PlanePolynomial
  homogeneous : polynomial.IsHomogeneous d
  nonzero : polynomial ≠ 0
namespace NonzeroHomogeneousForm
theorem totalDegree_eq {d : ℕ} (F : NonzeroHomogeneousForm d) :
    F.polynomial.totalDegree = d :=
  F.homogeneous.totalDegree F.nonzero
end NonzeroHomogeneousForm
open scoped BigOperators
end Nagata.W16
end
end
section
noncomputable section
namespace Nagata.W16
open scoped BigOperators
end Nagata.W16
end
end
section
namespace Nagata.W16
open Nagata.ProjectiveGeometry
end Nagata.W16
end
section
noncomputable section
namespace Nagata.W16
open Nagata.ProjectiveGeometry
open scoped BigOperators
end Nagata.W16
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W02
end Nagata.W02
end
end
section
noncomputable section
namespace Nagata.W02
def DegreeExponent (k : ℕ) := {d : Fin 3 →₀ ℕ // d.degree = k}
instance degreeExponentFintype (k : ℕ) : Fintype (DegreeExponent k) :=
  ((Finsupp.finite_of_degree_le (σ := Fin 3) k).subset
    (fun _ h => le_of_eq h)).fintype
def homogeneousCoefficientEquiv (R : Type*) [CommRing R] (k : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 3) R k ≃ₗ[R] (DegreeExponent k →₀ R) :=
  (LinearEquiv.ofEq _ _
    (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (Fin 3) R k)).trans
      (AddMonoidAlgebra.supportedEquivFinsupp {d : Fin 3 →₀ ℕ | d.degree = k})
end Nagata.W02
end
end
section
noncomputable section
namespace Nagata.W02
instance homogeneousFiniteDimensional (K : Type*) [Field K] (k : ℕ) :
    FiniteDimensional K (MvPolynomial.homogeneousSubmodule (Fin 3) K k) :=
  (homogeneousCoefficientEquiv K k).symm.finiteDimensional
end Nagata.W02
end
end
section
noncomputable section
namespace Nagata.W02
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
end Nagata.W02
end
end
section
noncomputable section
namespace Nagata.W02
open MvPolynomial
end Nagata.W02
end
end
section
noncomputable section
namespace Nagata.W02
open Nagata.W04.ReducibleSquare
end Nagata.W02
end
end
section
noncomputable section
namespace Nagata.W02
open MvPolynomial
noncomputable local instance oaiLocInst1 {σ R : Type*} [CommSemiring R] : GradedAlgebra (MvPolynomial.homogeneousSubmodule σ R) := MvPolynomial.gradedAlgebra
end Nagata.W02
end
end
section
namespace Nagata.W02
open Nagata.W04.ReducibleSquare
end Nagata.W02
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Module
namespace Nagata.Workers.W11
variable {ι κ V K : Type*} [Field K] [Fintype ι] [AddCommGroup V] [Module K V]
def basisJetMatrix (e : Basis ι K V) (J : V →ₗ[K] (κ → K)) : Matrix κ ι K :=
  fun row col => J (e col) row
theorem basisJetMatrix_mulVec_repr (e : Basis ι K V) (J : V →ₗ[K] (κ → K)) (v : V) :
    (basisJetMatrix e J).mulVec (e.repr v) = J v := by
  funext row
  have h := congrFun (congrArg J (e.sum_repr v)) row
  simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    basisJetMatrix, Matrix.mulVec, dotProduct, mul_comm] using h
theorem injective_of_basisJetMatrix (e : Basis ι K V) (J : V →ₗ[K] (κ → K))
    (h : Function.Injective (basisJetMatrix e J).mulVec) : Function.Injective J := by
  intro v w hvw
  apply e.repr.injective
  apply Finsupp.ext
  intro i
  have hc : (fun i => e.repr v i) = (fun i => e.repr w i) := h (by
    rw [basisJetMatrix_mulVec_repr, basisJetMatrix_mulVec_repr, hvw])
  exact congrFun hc i
theorem basisJetMatrix_nonzero_kernel (e : Basis ι K V) (J : V →ₗ[K] (κ → K))
    (v : V) (hv : v ≠ 0) (hJ : J v = 0) :
    ∃ c : ι → K, c ≠ 0 ∧ (basisJetMatrix e J).mulVec c = 0 := by
  refine ⟨e.repr v, ?_, by rw [basisJetMatrix_mulVec_repr, hJ]⟩
  intro hc
  apply hv
  apply e.repr.injective
  apply Finsupp.ext
  intro i
  simpa using congrFun hc i
end Nagata.Workers.W11
end
end
section
open Filter Topology
namespace Nagata.Workers.W11
variable {α ι κ : Type*} [Fintype ι] [DecidableEq ι]
theorem tendsto_det_of_entrywise {l : Filter α}
    {B : α → Matrix ι ι ℂ} {B₀ : Matrix ι ι ℂ}
    (hB : ∀ i j, Tendsto (fun t => B t i j) l (𝓝 (B₀ i j))) :
    Tendsto (fun t => (B t).det) l (𝓝 B₀.det) := by
  have h : Tendsto B l (𝓝 B₀) :=
    tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (hB i))
  exact (continuous_id.matrix_det.continuousAt.tendsto).comp h
theorem eventually_det_ne_zero_of_entrywise {l : Filter α}
    {B : α → Matrix ι ι ℂ} {B₀ : Matrix ι ι ℂ}
    (hB : ∀ i j, Tendsto (fun t => B t i j) l (𝓝 (B₀ i j)))
    (h₀ : B₀.det ≠ 0) : ∀ᶠ t in l, (B t).det ≠ 0 :=
  (tendsto_det_of_entrywise hB).eventually_ne h₀
theorem eventually_injective_of_entrywise {l : Filter α}
    {B : α → Matrix ι ι ℂ} {B₀ : Matrix ι ι ℂ}
    (hB : ∀ i j, Tendsto (fun t => B t i j) l (𝓝 (B₀ i j)))
    (h₀ : B₀.det ≠ 0) : ∀ᶠ t in l, Function.Injective (B t).mulVec := by
  exact (eventually_det_ne_zero_of_entrywise hB h₀).mono fun t ht =>
    Matrix.mulVec_injective_of_isUnit
      ((B t).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr ht))
theorem eventually_injective_of_nonzero_minor {l : Filter α}
    {B : α → Matrix κ ι ℂ} {B₀ : Matrix κ ι ℂ} (row : ι → κ)
    (hB : ∀ i j, Tendsto (fun t => B t i j) l (𝓝 (B₀ i j)))
    (h₀ : (B₀.submatrix row id).det ≠ 0) :
    ∀ᶠ t in l, Function.Injective (B t).mulVec := by
  have hminor : ∀ᶠ t in l,
      Function.Injective ((B t).submatrix row id).mulVec :=
    eventually_injective_of_entrywise (fun i j => hB (row i) j) h₀
  exact hminor.mono fun t ht x y hxy => ht (by
    funext i
    exact congrFun hxy (row i))
theorem eventually_injective_of_left_inverse [Fintype κ]
    {l : Filter α} {B : α → Matrix κ ι ℂ} {B₀ : Matrix κ ι ℂ}
    (C : Matrix ι κ ℂ) (hC : C * B₀ = 1)
    (hB : ∀ i j, Tendsto (fun t => B t i j) l (𝓝 (B₀ i j))) :
    ∀ᶠ t in l, Function.Injective (B t).mulVec := by
  have h : Tendsto B l (𝓝 B₀) :=
    tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (hB i))
  have hmul : Tendsto (fun t => C * B t) l (𝓝 (C * B₀)) :=
    ((continuous_const.matrix_mul continuous_id).continuousAt.tendsto).comp h
  have hentry : ∀ i j, Tendsto (fun t => (C * B t) i j) l (𝓝 ((C * B₀) i j)) :=
    fun i j => tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hmul i) j
  have hdet : (C * B₀).det ≠ 0 := by simp [hC]
  exact (eventually_injective_of_entrywise hentry hdet).mono fun t ht x y hxy =>
    ht (by simpa only [Matrix.mulVec_mulVec] using congrArg C.mulVec hxy)
theorem eventually_injective_of_injective_limit [Fintype κ] [DecidableEq κ]
    {l : Filter α} {B : α → Matrix κ ι ℂ} {B₀ : Matrix κ ι ℂ}
    (hB : ∀ i j, Tendsto (fun t => B t i j) l (𝓝 (B₀ i j)))
    (h₀ : Function.Injective B₀.mulVec) :
    ∀ᶠ t in l, Function.Injective (B t).mulVec := by
  obtain ⟨g, hg⟩ := (Matrix.toLin' B₀).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr h₀)
  have hC : LinearMap.toMatrix' g * B₀ = 1 := by
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_id] using congrArg LinearMap.toMatrix' hg
  exact eventually_injective_of_left_inverse (LinearMap.toMatrix' g) hC hB
end Nagata.Workers.W11
end
section
namespace Nagata.Workers.W11
variable {ρ κ K : Type*} [Fintype ρ] [Fintype κ] [DecidableEq κ]
omit [Fintype ρ] [DecidableEq κ] in
theorem not_nonzero_kernel_of_isEmpty_columns [CommRing K] [IsEmpty κ]
    (A : Matrix ρ κ K) : ¬ ∃ c : κ → K, c ≠ 0 ∧ A.mulVec c = 0 := by
  rintro ⟨c, hc, _⟩
  exact hc (Subsingleton.elim _ _)
omit [Fintype ρ] in
theorem not_all_maximal_minors_zero_of_isEmpty_columns
    [CommRing K] [Nontrivial K] [IsEmpty κ]
    (A : Matrix ρ κ K) :
    ¬ ∀ s : κ → ρ, Matrix.det (fun i j => A (s i) j) = 0 := by
  intro h
  have hz := h (fun i => isEmptyElim i)
  exact (one_ne_zero : (1 : K) ≠ 0) (Matrix.det_isEmpty.symm.trans hz)
end Nagata.Workers.W11
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W27
noncomputable section
open MvPolynomial
section Entries
variable {R : Type*} [CommRing R]
variable {ι : Type*}
end Entries
end
end Nagata.W27
end
section
noncomputable section
namespace Nagata.W27
open scoped BigOperators
open MvPolynomial
section MatrixEntries
variable {R : Type*} [CommRing R]
end MatrixEntries
section LinearEquations
variable {R : Type*} [CommRing R]
variable {σ κ ρ : Type*} [Fintype κ]
end LinearEquations
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open MvPolynomial
open Classical
variable {R : Type*} [CommRing R]
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open MvPolynomial
variable {ι R : Type*} [CommRing R]
end Nagata.W27
end
end
section
namespace Nagata.W27
noncomputable section
open scoped BigOperators
open MvPolynomial
section Determinants
variable {R : Type*} [CommRing R]
variable {σ κ ρ : Type*} [Fintype κ] [DecidableEq κ]
end Determinants
end
end Nagata.W27
end
section
noncomputable section
namespace Nagata.W27
open MvPolynomial
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open scoped BigOperators
open MvPolynomial
variable {R σ : Type*} [CommRing R]
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open scoped BigOperators
open MvPolynomial
variable {R : Type*} [CommRing R]
end Nagata.W27
end
end
section
namespace Nagata.W27
noncomputable section
open MvPolynomial
end
end Nagata.W27
end
section
noncomputable section
namespace Nagata.W27
open MvPolynomial
variable {R : Type*} [CommRing R]
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open MvPolynomial
variable {σ ρ κ K : Type*} [Field K]
variable [Fintype ρ] [Fintype κ] [DecidableEq κ]
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open MvPolynomial
variable {r : ℕ} {R : Type*} [CommRing R]
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open scoped BigOperators
open MvPolynomial
open Classical
variable {R : Type*} [CommRing R]
variable {r : ℕ}
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open MvPolynomial
open Classical
variable {r : ℕ} {K : Type*} [Field K]
end Nagata.W27
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.Workers.W30
open UniqueFactorizationMonoid
noncomputable section
abbrev TernaryPolynomial := MvPolynomial (Fin 3) ℂ
local instance : DecidableEq (Associates TernaryPolynomial) := Classical.decEq _
def equationMultiplicity (F : TernaryPolynomial) : Associates TernaryPolynomial →₀ ℕ :=
  factorization (Associates.mk F)
theorem equationMultiplicity_eq_iff {F G : TernaryPolynomial} (hF : F ≠ 0) (hG : G ≠ 0) :
    equationMultiplicity F = equationMultiplicity G ↔ Associated F G := by
  constructor
  · intro h
    have ha := associated_of_factorization_eq (Associates.mk F) (Associates.mk G)
      (Associates.mk_ne_zero.mpr hF) (Associates.mk_ne_zero.mpr hG) h
    exact Associates.mk_eq_mk_iff_associated.mp (associated_iff_eq.mp ha)
  · intro h
    unfold equationMultiplicity
    rw [Associates.mk_eq_mk_iff_associated.mpr h]
def associatePrincipalIdeal (a : Associates TernaryPolynomial) : Ideal TernaryPolynomial :=
  (Ideal.associatesEquivIsPrincipal TernaryPolynomial a).val
theorem associatePrincipalIdeal_injective : Function.Injective associatePrincipalIdeal := by
  intro a b h
  apply (Ideal.associatesEquivIsPrincipal TernaryPolynomial).injective
  exact Subtype.ext h
@[simp] theorem associatePrincipalIdeal_mk (F : TernaryPolynomial) :
    associatePrincipalIdeal (Associates.mk F) = Ideal.span {F} := rfl
def equationIdealCycle (F : TernaryPolynomial) : Ideal TernaryPolynomial →₀ ℕ :=
  (equationMultiplicity F).mapDomain associatePrincipalIdeal
theorem equationIdealCycle_eq_iff {F G : TernaryPolynomial} (hF : F ≠ 0) (hG : G ≠ 0) :
    equationIdealCycle F = equationIdealCycle G ↔ Associated F G := by
  change Finsupp.mapDomain associatePrincipalIdeal (equationMultiplicity F) =
    Finsupp.mapDomain associatePrincipalIdeal (equationMultiplicity G) ↔ _
  rw [(Finsupp.mapDomain_injective associatePrincipalIdeal_injective).eq_iff,
    equationMultiplicity_eq_iff hF hG]
theorem equationMultiplicity_support_prime (F : TernaryPolynomial)
    {a : Associates TernaryPolynomial} (ha : a ∈ (equationMultiplicity F).support) :
    Prime a := by
  apply prime_of_normalized_factor a
  simpa only [equationMultiplicity, support_factorization, Multiset.mem_toFinset] using ha
theorem equationIdealCycle_support (F : TernaryPolynomial)
    {I : Ideal TernaryPolynomial} (hI : I ∈ (equationIdealCycle F).support) :
    I.IsPrime ∧ I ≠ ⊥ ∧ I.IsPrincipal := by
  classical
  rw [equationIdealCycle,
    Finsupp.mapDomain_support_of_injective associatePrincipalIdeal_injective] at hI
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hI
  have hprime := equationMultiplicity_support_prime F ha
  obtain ⟨P, rfl⟩ := Associates.mk_surjective a
  have hP : Prime P := Associates.prime_mk.mp hprime
  rw [associatePrincipalIdeal_mk]
  exact ⟨(Ideal.span_singleton_prime hP.ne_zero).mpr hP,
    fun h => hP.ne_zero (Ideal.span_singleton_eq_bot.mp h), inferInstance⟩
theorem equationIdealCycle_coefficient (F : TernaryPolynomial)
    (a : Associates TernaryPolynomial) :
    equationIdealCycle F (associatePrincipalIdeal a) = equationMultiplicity F a := by
  exact Finsupp.mapDomain_apply associatePrincipalIdeal_injective _ _
end
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open UniqueFactorizationMonoid
variable {R : Type*} [CommRing R] [IsDomain R]
variable [UniqueFactorizationMonoid R]
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open MvPolynomial
open scoped BigOperators
variable {σ K : Type*} [Field K]
lemma topHomogeneousComponent_ne_zero {p : MvPolynomial σ K} (hp : p ≠ 0) :
    homogeneousComponent p.totalDegree p ≠ 0 := by
  classical
  obtain ⟨a,ha,hdeg⟩ := Finset.exists_mem_eq_sup p.support
    (support_nonempty.mpr hp) (fun a => a.sum fun _ e => e)
  intro hz
  have hz' := congrArg (fun polynomial : MvPolynomial σ K => polynomial.coeff a) hz
  have heq : a.degree = p.totalDegree := hdeg.symm
  have hc : p.coeff a = 0 := by
    simpa [coeff_homogeneousComponent, heq] using hz'
  exact (mem_support_iff.mp ha) hc
lemma topHomogeneousComponent_mul (p q : MvPolynomial σ K) :
    homogeneousComponent (p.totalDegree + q.totalDegree) (p*q) =
      homogeneousComponent p.totalDegree p * homogeneousComponent q.totalDegree q := by
  classical
  have hdecomp : p*q =
      (∑ i ∈ Finset.range (p.totalDegree+1), homogeneousComponent i p) *
      (∑ j ∈ Finset.range (q.totalDegree+1), homogeneousComponent j q) := by
    rw [sum_homogeneousComponent, sum_homogeneousComponent]
  rw [hdecomp]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, map_sum]
  rw [Finset.sum_eq_single p.totalDegree]
  · rw [Finset.sum_eq_single q.totalDegree]
    · rw [homogeneousComponent_of_mem
        ((homogeneousComponent_isHomogeneous p.totalDegree p).mul
          (homogeneousComponent_isHomogeneous q.totalDegree q))]
      simp
    · intro j hj hne
      rw [homogeneousComponent_of_mem
        ((homogeneousComponent_isHomogeneous p.totalDegree p).mul
          (homogeneousComponent_isHomogeneous j q))]
      simp only [ite_eq_right_iff]
      intro h
      exfalso
      apply hne
      omega
    · simp
  · intro i hi hne
    apply Finset.sum_eq_zero
    intro j hj
    rw [homogeneousComponent_of_mem
      ((homogeneousComponent_isHomogeneous i p).mul
        (homogeneousComponent_isHomogeneous j q))]
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have hne' : p.totalDegree + q.totalDegree ≠ i+j := by omega
    simp [hne']
  · simp
lemma degree_pos_of_nonzero_nonunit {p : MvPolynomial σ K} (hp : p ≠ 0)
    (hu : ¬ IsUnit p) : 0 < p.totalDegree := by
  by_contra hn
  have hz : p.totalDegree = 0 := by omega
  have heq := totalDegree_eq_zero_iff_eq_C.mp hz
  have hc : p.coeff 0 ≠ 0 := by
    intro hc
    apply hp
    rw [heq,hc,C_0]
  apply hu
  rw [heq]
  exact (isUnit_iff_ne_zero.mpr hc).map C
theorem exists_homogeneous_irreducible_factors (p : MvPolynomial σ K) {d : ℕ}
    (hp : p ≠ 0) (hhom : p.IsHomogeneous d) :
    ∃ L : Multiset (MvPolynomial σ K),
      (∀ P ∈ L, Irreducible P ∧ P.IsHomogeneous P.totalDegree) ∧ Associated L.prod p := by
  classical
  suffices H : ∀ n (p : MvPolynomial σ K), p.totalDegree = n → p ≠ 0 →
      p.IsHomogeneous n → ∃ L : Multiset (MvPolynomial σ K),
      (∀ P ∈ L, Irreducible P ∧ P.IsHomogeneous P.totalDegree) ∧ Associated L.prod p from
    H d p (hhom.totalDegree hp) hp hhom
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p hdeg hp hhom
    by_cases hu : IsUnit p
    · refine ⟨0, by simp, ?_⟩
      simpa using (associated_one_iff_isUnit.mpr hu).symm
    rcases irreducible_or_factor hu with hirr | ⟨a,b,hau,hbu,hab⟩
    · refine ⟨{p}, ?_, ?_⟩
      · intro P hP
        have heq : P = p := Multiset.mem_singleton.mp hP
        subst P
        exact ⟨hirr, by simpa only [hdeg] using hhom⟩
      · simp
    · have ha : a ≠ 0 := by intro h; simp [h] at hab; exact hp hab
      have hb : b ≠ 0 := by intro h; simp [h] at hab; exact hp hab
      have hsum : a.totalDegree+b.totalDegree = n := by
        rw [← totalDegree_mul_of_isDomain ha hb, ← hab, hdeg]
      have hapos := degree_pos_of_nonzero_nonunit ha hau
      have hbpos := degree_pos_of_nonzero_nonunit hb hbu
      let A := homogeneousComponent a.totalDegree a
      let B := homogeneousComponent b.totalDegree b
      have hA : A ≠ 0 := topHomogeneousComponent_ne_zero ha
      have hB : B ≠ 0 := topHomogeneousComponent_ne_zero hb
      have hAh : A.IsHomogeneous a.totalDegree := homogeneousComponent_isHomogeneous _ _
      have hBh : B.IsHomogeneous b.totalDegree := homogeneousComponent_isHomogeneous _ _
      have hprod : A*B = p := by
        change homogeneousComponent a.totalDegree a * homogeneousComponent b.totalDegree b = p
        rw [← topHomogeneousComponent_mul, ← hab, hsum,
          homogeneousComponent_of_mem hhom]
        simp
      obtain ⟨L,hL,hLp⟩ := ih a.totalDegree (by omega) A (hAh.totalDegree hA) hA hAh
      obtain ⟨M,hM,hMp⟩ := ih b.totalDegree (by omega) B (hBh.totalDegree hB) hB hBh
      refine ⟨L+M, ?_, ?_⟩
      · intro P hP
        exact (Multiset.mem_add.mp hP).elim (hL P) (hM P)
      · rw [Multiset.prod_add, ← hprod]
        exact hLp.mul_mul hMp
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open MvPolynomial UniqueFactorizationMonoid
variable {σ K : Type*} [Field K]
lemma unit_polynomial_totalDegree (u : (MvPolynomial σ K)ˣ) :
    (u : MvPolynomial σ K).totalDegree = 0 := by
  have h := totalDegree_mul_of_isDomain u.ne_zero (u⁻¹).ne_zero
  simp only [← Units.val_mul, mul_inv_cancel, Units.val_one, totalDegree_one] at h
  omega
lemma homogeneous_of_associated {p q : MvPolynomial σ K} {d : ℕ}
    (hp : p.IsHomogeneous d) (h : Associated p q) : q.IsHomogeneous d := by
  obtain ⟨u,rfl⟩ := h
  have hu : (u : MvPolynomial σ K).IsHomogeneous 0 :=
    (totalDegree_zero_iff_isHomogeneous σ).mp (unit_polynomial_totalDegree u)
  simpa only [add_zero] using hp.mul hu
theorem factors_homogeneous {p : MvPolynomial σ K} {d : ℕ}
    (hp : p ≠ 0) (hhom : p.IsHomogeneous d) :
    ∀ f ∈ factors p, f.IsHomogeneous f.totalDegree := by
  classical
  obtain ⟨L,hL,hprod⟩ := exists_homogeneous_irreducible_factors p hp hhom
  have hrel : Multiset.Rel Associated (factors p) L :=
    factors_unique irreducible_of_factor (fun f hf => (hL f hf).1)
      ((factors_prod hp).trans hprod.symm)
  intro f hf
  obtain ⟨g,hg,hfg⟩ := Multiset.exists_mem_of_rel_of_mem hrel hf
  have hgHom := homogeneous_of_associated (hL g hg).2 hfg.symm
  have hf0 : f ≠ 0 := (prime_of_factor f hf).ne_zero
  simpa only [hgHom.totalDegree hf0] using hgHom
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open MvPolynomial
noncomputable local instance oaiLocInst2 {σ R : Type*} [CommSemiring R] : GradedAlgebra (MvPolynomial.homogeneousSubmodule σ R) := MvPolynomial.gradedAlgebra
variable {σ K : Type*} [Field K]
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open MvPolynomial UniqueFactorizationMonoid
variable {σ K : Type*} [Field K]
lemma homogeneous_multiset_prod (L : Multiset (MvPolynomial σ K))
    (hL : ∀ f ∈ L, f.IsHomogeneous f.totalDegree) :
    L.prod.IsHomogeneous (L.map MvPolynomial.totalDegree).sum := by
  induction L using Multiset.induction_on with
  | empty => simpa using (isHomogeneous_one σ K)
  | @cons f L ih =>
    simpa only [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons] using
      (hL f (Multiset.mem_cons_self _ _)).mul
        (ih (fun g hg => hL g (Multiset.mem_cons_of_mem hg)))
theorem homogeneous_of_dvd {p f : MvPolynomial σ K} {d : ℕ}
    (hp : p ≠ 0) (hhom : p.IsHomogeneous d) (hf : f ∣ p) :
    f.IsHomogeneous f.totalDegree := by
  classical
  have hf0 : f ≠ 0 := by rintro rfl; exact hp (by simpa using hf)
  have hfac : ∀ a ∈ factors f, a.IsHomogeneous a.totalDegree := by
    intro a ha
    have hairr : Irreducible a := irreducible_of_factor a ha
    have hadvd : a ∣ p :=
      (Multiset.dvd_prod ha).trans ((factors_prod hf0).dvd.trans hf)
    obtain ⟨b,hb,hab⟩ := exists_mem_factors_of_dvd hp hairr hadvd
    have hah := homogeneous_of_associated (factors_homogeneous hp hhom b hb) hab.symm
    simpa only [hah.totalDegree hairr.ne_zero] using hah
  have hprod := homogeneous_multiset_prod (factors f) hfac
  have hfh := homogeneous_of_associated hprod (factors_prod hf0)
  simpa only [hfh.totalDegree hf0] using hfh
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open MvPolynomial
noncomputable local instance oaiLocInst3 {σ R : Type*} [CommSemiring R] : GradedAlgebra (MvPolynomial.homogeneousSubmodule σ R) := MvPolynomial.gradedAlgebra
variable {σ K : Type*} [Field K]
theorem span_homogeneous_of_homogeneous {f : MvPolynomial σ K} {d : ℕ}
    (hf : f.IsHomogeneous d) :
    (Ideal.span ({f} : Set (MvPolynomial σ K))).IsHomogeneous (homogeneousSubmodule σ K) := by
  apply Ideal.homogeneous_span
  intro x hx
  have heq : x = f := Set.mem_singleton_iff.mp hx
  subst x
  exact ⟨d,hf⟩
end Nagata.Workers.W30
end
end OAI
end
section
namespace OAI
section
namespace Nagata.Workers.W30
open UniqueFactorizationMonoid
noncomputable section
local instance cycleAssociateDecidableEq : DecidableEq (Associates TernaryPolynomial) := Classical.decEq _
end
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
@[simp] theorem equationIdealCycle_one : equationIdealCycle (1 : TernaryPolynomial) = 0 := by
  simp only [equationIdealCycle, equationMultiplicity, Associates.mk_one,
    factorization_one, Finsupp.mapDomain_zero]
theorem equationIdealCycle_zero_iff {F : TernaryPolynomial} (hF : F ≠ 0) :
    equationIdealCycle F = 0 ↔ IsUnit F := by
  rw [← equationIdealCycle_one, equationIdealCycle_eq_iff hF one_ne_zero,
    associated_one_iff_isUnit]
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open UniqueFactorizationMonoid
noncomputable section
local instance supportAssociateDecidableEq : DecidableEq (Associates TernaryPolynomial) := Classical.decEq _
theorem span_mem_equationIdealCycle_iff (F f : TernaryPolynomial) (hF : F ≠ 0) :
    Ideal.span ({f} : Set TernaryPolynomial) ∈ (equationIdealCycle F).support ↔
      Prime f ∧ f ∣ F := by
  classical
  rw [Finsupp.mem_support_iff, ← associatePrincipalIdeal_mk,
    equationIdealCycle_coefficient, ← Finsupp.mem_support_iff]
  change Associates.mk f ∈ (factorization (Associates.mk F)).support ↔ _
  rw [support_factorization, Multiset.mem_toFinset,
    mem_normalizedFactors_iff (Associates.mk_ne_zero.mpr hF),
    Associates.prime_mk, Associates.mk_dvd_mk]
end
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
noncomputable section
end
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open MvPolynomial UniqueFactorizationMonoid
noncomputable local instance oaiLocInst4 {σ R : Type*} [CommSemiring R] : GradedAlgebra (MvPolynomial.homogeneousSubmodule σ R) := MvPolynomial.gradedAlgebra
noncomputable section
theorem equationIdealCycle_homogeneous {F : TernaryPolynomial} {d : ℕ}
    (hF : F ≠ 0) (hhom : F.IsHomogeneous d) {I : Ideal TernaryPolynomial}
    (hI : I ∈ (equationIdealCycle F).support) :
    I.IsHomogeneous (homogeneousSubmodule (Fin 3) ℂ) := by
  classical
  rw [equationIdealCycle,
    Finsupp.mapDomain_support_of_injective associatePrincipalIdeal_injective] at hI
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨f,rfl⟩ := Associates.mk_surjective a
  have hs : Ideal.span ({f} : Set TernaryPolynomial) ∈ (equationIdealCycle F).support := by
    rw [equationIdealCycle,
      Finsupp.mapDomain_support_of_injective associatePrincipalIdeal_injective]
    exact Finset.mem_image.mpr ⟨Associates.mk f,ha,rfl⟩
  have hdiv := ((span_mem_equationIdealCycle_iff F f hF).mp hs).2
  rw [associatePrincipalIdeal_mk]
  exact span_homogeneous_of_homogeneous (homogeneous_of_dvd hF hhom hdiv)
end
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open MvPolynomial
noncomputable local instance oaiLocInst5 {σ R : Type*} [CommSemiring R] : GradedAlgebra (MvPolynomial.homogeneousSubmodule σ R) := MvPolynomial.gradedAlgebra
end Nagata.Workers.W30
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.ProjectiveGeometry
end Nagata.ProjectiveGeometry
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W16
open Nagata.ProjectiveGeometry
abbrev HomogeneousFormSpace (d : ℕ) :=
  ↥(MvPolynomial.homogeneousSubmodule (Fin 3) ℂ d)
abbrev PlaneEquationClass (d : ℕ) := Projectivization ℂ (HomogeneousFormSpace d)
structure PositivePlaneEquation where
  degree : ℕ
  degree_pos : 0 < degree
  equationClass : PlaneEquationClass degree
def formVector {d : ℕ} (F : NonzeroHomogeneousForm d) : HomogeneousFormSpace d :=
  ⟨F.polynomial, F.homogeneous⟩
theorem formVector_ne_zero {d : ℕ} (F : NonzeroHomogeneousForm d) : formVector F ≠ 0 := by
  intro h
  exact F.nonzero (congrArg Subtype.val h)
def classOfForm {d : ℕ} (F : NonzeroHomogeneousForm d) : PlaneEquationClass d :=
  Projectivization.mk ℂ (formVector F) (formVector_ne_zero F)
def classRepresentative {d : ℕ} (C : PlaneEquationClass d) : NonzeroHomogeneousForm d where
  polynomial := C.rep.val
  homogeneous := C.rep.property
  nonzero := by
    intro h
    apply C.rep_nonzero
    exact Subtype.ext h
theorem representative_totalDegree {d : ℕ} (C : PlaneEquationClass d) :
    (classRepresentative C).polynomial.totalDegree = d :=
  (classRepresentative C).totalDegree_eq
end Nagata.W16
end
end
section
noncomputable section
namespace Nagata.ProjectiveGeometry
end Nagata.ProjectiveGeometry
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W10
open Nagata.Workers.W30 Nagata.W16 MvPolynomial
end Nagata.Workers.W10
end
end
section
noncomputable section
namespace Nagata.Workers.W10
open Nagata.Workers.W30 Nagata.W16 MvPolynomial
noncomputable local instance oaiLocInst6 {σ R : Type*} [CommSemiring R] : GradedAlgebra (MvPolynomial.homogeneousSubmodule σ R) := MvPolynomial.gradedAlgebra
def EffectivePlaneCurve := {D : Ideal TernaryPolynomial →₀ ℕ //
  D ≠ 0 ∧ ∀ I ∈ D.support, I.IsPrime ∧ I ≠ ⊥ ∧ I.IsPrincipal ∧
    I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)}
def curveOfEquation (E : PositivePlaneEquation) : EffectivePlaneCurve :=
  ⟨equationIdealCycle (classRepresentative E.equationClass).polynomial, by
    constructor
    · intro hzero
      obtain ⟨u, hu⟩ := (equationIdealCycle_zero_iff (classRepresentative E.equationClass).nonzero).mp hzero
      have hd0 : (classRepresentative E.equationClass).polynomial.totalDegree = 0 := by
        rw [← hu]
        exact unit_polynomial_totalDegree u
      exact (Nat.ne_of_gt E.degree_pos) ((representative_totalDegree E.equationClass).symm.trans hd0)
    · intro I hI
      have hp := equationIdealCycle_support _ hI
      exact ⟨hp.1, hp.2.1, hp.2.2,
        equationIdealCycle_homogeneous (classRepresentative E.equationClass).nonzero
          (classRepresentative E.equationClass).homogeneous hI⟩⟩
end Nagata.Workers.W10
end
end
section
noncomputable section
namespace Nagata.Workers.W10
open Nagata.Workers.W30 Nagata.W16 Nagata.ProjectiveGeometry
end Nagata.Workers.W10
end
end
section
noncomputable section
namespace Nagata.Workers.W10
open Nagata.Workers.W30 Nagata.W16
def curveOfForm {d : ℕ} (F : NonzeroHomogeneousForm d) (hd : 0 < d) : EffectivePlaneCurve :=
  curveOfEquation ⟨d, hd, classOfForm F⟩
end Nagata.Workers.W10
end
end
section
noncomputable section
namespace Nagata.Workers.W10
open Nagata.W16
def coordinateLineForm : NonzeroHomogeneousForm 1 :=
  ⟨MvPolynomial.X (0 : Fin 3), MvPolynomial.isHomogeneous_X ℂ _, MvPolynomial.X_ne_zero (0 : Fin 3)⟩
def coordinateLineCurve : EffectivePlaneCurve := curveOfForm coordinateLineForm zero_lt_one
instance effectivePlaneCurveNonempty : Nonempty EffectivePlaneCurve := ⟨coordinateLineCurve⟩
end Nagata.Workers.W10
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.AffineMultiplicity
variable {σ R : Type*} [CommRing R]
end Nagata.AffineMultiplicity
end
section
namespace Nagata.W04.ReducibleSquare
variable {K : Type*} [Field K]
end Nagata.W04.ReducibleSquare
end
section
namespace Nagata.AffineMultiplicity
variable {σ R : Type*} [CommRing R]
end Nagata.AffineMultiplicity
end
section
namespace Nagata.ProjectiveGeometry
end Nagata.ProjectiveGeometry
end
section
noncomputable section
open scoped BigOperators
namespace Nagata.AffineMultiplicity
end Nagata.AffineMultiplicity
namespace Nagata.W15
open Nagata.ProjectiveGeometry
end Nagata.W15
end
end
section
noncomputable section
open scoped BigOperators
namespace Nagata.W15
open Nagata.Workers.W10 Nagata.Workers.W30 Nagata.ProjectiveGeometry
noncomputable local instance oaiLocInst7 {σ R : Type*} [CommSemiring R] : GradedAlgebra (MvPolynomial.homogeneousSubmodule σ R) := MvPolynomial.gradedAlgebra
end Nagata.W15
end
end
section
noncomputable section
open scoped BigOperators
namespace Nagata.W15
open Nagata.Workers.W10 Nagata.Workers.W30 Nagata.ProjectiveGeometry
end Nagata.W15
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W28
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
end Nagata.Workers.W28
end
end
end OAI
end
section
namespace OAI
section
open Polynomial
open scoped BigOperators
namespace Nagata.W18
end Nagata.W18
end
section
noncomputable section
open Polynomial
open scoped BigOperators
namespace Nagata.W18
end Nagata.W18
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W18
open scoped BigOperators
end Nagata.W18
end
section
noncomputable section
namespace Nagata.W18
end Nagata.W18
end
end
section
noncomputable section
open scoped BigOperators
namespace Nagata.W18
end Nagata.W18
end
end
section
namespace Nagata.W18
end Nagata.W18
end
end OAI
end
section
namespace OAI
section
namespace Nagata.Workers.W24
end Nagata.Workers.W24
end
section
namespace Nagata.Workers.W24
end Nagata.Workers.W24
end
section
noncomputable section
namespace Nagata.Workers.W24
open Polynomial
end Nagata.Workers.W24
end
end
section
namespace Nagata.Workers.W24
end Nagata.Workers.W24
end
section
namespace Nagata.Workers.W24
open Polynomial
end Nagata.Workers.W24
end
section
noncomputable section
namespace Nagata.Workers.W24
open MvPolynomial
end Nagata.Workers.W24
end
end
section
namespace Nagata.Workers.W24
open Module
end Nagata.Workers.W24
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W18
open scoped BigOperators
end Nagata.W18
end
section
noncomputable section
namespace Nagata.W18
variable {K : Type*} [CommRing K]
end Nagata.W18
end
end
section
noncomputable section
open Polynomial
open scoped BigOperators
namespace Nagata.W18
end Nagata.W18
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W24
open Polynomial
open scoped BigOperators
end Nagata.Workers.W24
end
end
section
namespace Nagata.Workers.W24
open Polynomial
open scoped BigOperators
end Nagata.Workers.W24
end
section
noncomputable section
namespace Nagata.Workers.W24
open scoped BigOperators
end Nagata.Workers.W24
end
end
section
noncomputable section
namespace Nagata.Workers.W24
end Nagata.Workers.W24
end
end
section
namespace Nagata.Workers.W24
end Nagata.Workers.W24
end
section
namespace Nagata.Workers.W24
open MvPolynomial
end Nagata.Workers.W24
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W06.LineArrangement
open Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]
variable [CharZero K]
end Nagata.W06.LineArrangement
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W06
theorem exists_between_avoiding_finite {a b : ℝ} (hab : a < b)
    {F : Set ℝ} (hF : F.Finite) : ∃ x, a < x ∧ x < b ∧ x ∉ F := by
  induction F, hF using Set.Finite.induction_on generalizing a b with
  | empty =>
    obtain ⟨x, hax, hxb⟩ := exists_between hab
    exact ⟨x, hax, hxb, by simp⟩
  | @insert c F hc hF ih =>
    obtain ⟨x, hax, hxb, hxF⟩ := ih hab
    by_cases hxc : x = c
    · obtain ⟨y, hxy, hyb, hyF⟩ := ih hxb
      refine ⟨y, lt_trans hax hxy, hyb, ?_⟩
      intro hy
      rcases Set.mem_insert_iff.mp hy with hyc | hyF'
      · linarith
      · exact hyF hyF'
    · refine ⟨x, hax, hxb, ?_⟩
      intro hx
      rcases Set.mem_insert_iff.mp hx with hxc' | hxF'
      · exact hxc hxc'
      · exact hxF hxF'
theorem exists_delta_avoiding_finite {ρ B : ℝ} (hρ : 0 < ρ) (hB : ρ < B)
    {F : Set ℝ} (hF : F.Finite) :
    ∃ Δ : ℝ, 0 < Δ ∧ Δ < 1 / 2 ∧ ρ + Δ * ρ / 9 < B ∧ Δ ∉ F := by
  have hbound : 0 < min (1 / 2 : ℝ) (9 * (B - ρ) / ρ) := by
    apply lt_min
    · norm_num
    · exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hB)) hρ
  obtain ⟨Δ, hΔ, hupper, havoid⟩ := exists_between_avoiding_finite hbound hF
  have hhalf : Δ < 1 / 2 := lt_of_lt_of_le hupper (min_le_left _ _)
  have hquot : Δ < 9 * (B - ρ) / ρ := lt_of_lt_of_le hupper (min_le_right _ _)
  have hprod : Δ * ρ < 9 * (B - ρ) := (lt_div_iff₀ hρ).mp hquot
  exact ⟨Δ, hΔ, hhalf, by linarith, havoid⟩
end Nagata.W06
end
section
namespace Nagata.W06
noncomputable def nineDisplacement (Δ : ℝ) (i : Fin 9) : ℝ := Δ * ((i.val : ℝ) + 1) / 45
noncomputable def markedExponent (Δ : ℝ) (i : Fin 9) : ℝ := 1 / 2 - nineDisplacement Δ i
theorem nineDisplacement_pos {Δ : ℝ} (hΔ : 0 < Δ) (i : Fin 9) :
    0 < nineDisplacement Δ i := by
  have hi : 0 < (i.val : ℝ) + 1 := by exact_mod_cast Nat.zero_lt_succ i.val
  exact div_pos (mul_pos hΔ hi) (by norm_num)
theorem nineDisplacement_lt {Δ : ℝ} (hΔ : 0 < Δ) (i : Fin 9) :
    nineDisplacement Δ i < Δ := by
  have hi : (i.val : ℝ) + 1 ≤ 9 := by exact_mod_cast (Nat.succ_le_of_lt i.isLt)
  have hp := mul_nonneg (le_of_lt hΔ) (show 0 ≤ 9 - ((i.val : ℝ) + 1) by linarith)
  dsimp [nineDisplacement]
  nlinarith
theorem nineDisplacement_injective {Δ : ℝ} (hΔ : 0 < Δ) :
    Function.Injective (nineDisplacement Δ) := by
  intro i j hij
  dsimp [nineDisplacement] at hij
  have hmul : Δ * ((i.val : ℝ) + 1) = Δ * ((j.val : ℝ) + 1) := by linarith
  have hval := mul_left_cancel₀ (ne_of_gt hΔ) hmul
  apply Fin.ext
  exact_mod_cast (show (i.val : ℝ) = (j.val : ℝ) by linarith)
theorem sum_nineDisplacement (Δ : ℝ) :
    ∑ i : Fin 9, nineDisplacement Δ i = Δ := by
  norm_num [Fin.sum_univ_succ, nineDisplacement]
  ring
theorem markedExponent_pos {Δ : ℝ} (hΔ : 0 < Δ) (hhalf : Δ < 1 / 2)
    (i : Fin 9) : 0 < markedExponent Δ i := by
  have h := nineDisplacement_lt hΔ i
  dsimp [markedExponent]
  linarith
theorem markedExponent_lt_half {Δ : ℝ} (hΔ : 0 < Δ) (i : Fin 9) :
    markedExponent Δ i < 1 / 2 := by
  have h := nineDisplacement_pos hΔ i
  dsimp [markedExponent]
  linarith
theorem markedExponent_injective {Δ : ℝ} (hΔ : 0 < Δ) :
    Function.Injective (markedExponent Δ) := by
  intro i j hij
  apply nineDisplacement_injective hΔ
  dsimp [markedExponent] at hij
  linarith
theorem sum_markedExponent_displacement (Δ : ℝ) :
    ∑ i : Fin 9, (1 / 2 - markedExponent Δ i) = Δ := by
  simpa only [markedExponent, sub_sub_cancel] using sum_nineDisplacement Δ
theorem exists_marked_parameters {Δ : ℝ} (hΔ : 0 < Δ) (hhalf : Δ < 1 / 2) :
    ∃ x : Fin 9 → ℝ, Function.Injective x ∧
      (∀ i, 0 < x i ∧ x i < 1 / 2) ∧
      ∑ i : Fin 9, (1 / 2 - x i) = Δ := by
  refine ⟨markedExponent Δ, markedExponent_injective hΔ, ?_,
    sum_markedExponent_displacement Δ⟩
  intro i
  exact ⟨markedExponent_pos hΔ hhalf i, markedExponent_lt_half hΔ i⟩
end Nagata.W06
end
end OAI
end
section
namespace OAI
section
namespace Nagata.Workers.W05
open Filter
open scoped Topology
end Nagata.Workers.W05
end
section
namespace Nagata.Workers.W05
end Nagata.Workers.W05
end
section
namespace Nagata.Workers.W05
open Filter
open scoped Topology
end Nagata.Workers.W05
end
section
namespace Nagata.W21
end Nagata.W21
end
section
namespace Nagata.Workers.W05
end Nagata.Workers.W05
end
section
namespace Nagata.W21
variable {R : Type*} [CommMonoid R]
section Topological
variable [TopologicalSpace R] [TopologicalSpace Rˣ]
  [IsTopologicalGroup Rˣ] [ContinuousSMul Rˣ R]
end Topological
end Nagata.W21
end
section
namespace Nagata.W21
variable {G : Type*} [CommGroup G]
end Nagata.W21
end
section
namespace Nagata.Workers.W05
theorem exists_int_scale_interval {τ a : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) (ha : 0 < a) :
    ∃ k : ℤ, τ ≤ τ ^ k * a ∧ τ ^ k * a ≤ 1 := by
  have hL : Real.log τ < 0 := Real.log_neg hτ hτ1
  let N : ℤ := ⌊Real.log a / Real.log τ⌋
  have hlo : (N : ℝ) ≤ Real.log a / Real.log τ := Int.floor_le _
  have hhi : Real.log a / Real.log τ < (N : ℝ) + 1 := Int.lt_floor_add_one _
  have hcancel : (Real.log a / Real.log τ) * Real.log τ = Real.log a :=
    div_mul_cancel₀ _ (ne_of_lt hL)
  have hupper := mul_le_mul_of_nonpos_right hlo (le_of_lt hL)
  have hlower := mul_lt_mul_of_neg_right hhi hL
  rw [hcancel] at hupper hlower
  have hscaled : 0 < τ ^ (-N) * a := mul_pos (zpow_pos hτ _) ha
  have hlog : Real.log (τ ^ (-N) * a) = -(N : ℝ) * Real.log τ + Real.log a := by
    rw [Real.log_mul (ne_of_gt (zpow_pos hτ _)) (ne_of_gt ha), Real.log_zpow]
    simp
  refine ⟨-N, ?_, ?_⟩
  · apply (Real.log_le_log_iff hτ hscaled).mp
    rw [hlog]
    linarith
  · apply (Real.log_le_log_iff hscaled zero_lt_one).mp
    rw [hlog, Real.log_one]
    linarith
theorem exists_zpow_in_annulus {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (z : ℂ) (hz : z ≠ 0) :
    ∃ k : ℤ, τ ≤ ‖(τ : ℂ) ^ k * z‖ ∧ ‖(τ : ℂ) ^ k * z‖ ≤ 1 := by
  obtain ⟨k, hklo, hkhi⟩ := exists_int_scale_interval hτ hτ1 (norm_pos_iff.mpr hz)
  refine ⟨k, ?_⟩
  simpa only [norm_mul, Complex.norm_zpow, Complex.norm_of_nonneg (le_of_lt hτ)]
    using And.intro hklo hkhi
def closedAnnulus (τ : ℝ) : Set ℂ := {z | τ ≤ ‖z‖ ∧ ‖z‖ ≤ 1}
theorem isCompact_closedAnnulus (τ : ℝ) : IsCompact (closedAnnulus τ) := by
  have hc : IsClosed (closedAnnulus τ) :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  apply (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset hc
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2
end Nagata.Workers.W05
end
section
namespace Nagata.W21
end Nagata.W21
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W06
theorem finite_affine_integer_preimages (a b R : ℝ) (ha : a ≠ 0) :
    {x : ℝ | |x| ≤ R ∧ ∃ k : ℤ, a * x + b = k}.Finite := by
  obtain ⟨N, hN⟩ := exists_nat_gt (|a| * R + |b|)
  have hfin : ((fun k : ℤ => ((k : ℝ) - b) / a) ''
      Set.Icc (-(N : ℤ)) (N : ℤ)).Finite :=
    (Set.finite_Icc _ _).image _
  apply hfin.subset
  intro x hx
  obtain ⟨hRx, k, hk⟩ := hx
  have hbound : |(k : ℝ)| < (N : ℝ) := by
    calc
      |(k : ℝ)| = |a * x + b| := congrArg abs hk.symm
      _ ≤ |a * x| + |b| := abs_add_le _ _
      _ = |a| * |x| + |b| := by rw [abs_mul]
      _ ≤ |a| * R + |b| := add_le_add (mul_le_mul_of_nonneg_left hRx (abs_nonneg a)) le_rfl
      _ < N := hN
  have hb := abs_le.mp (le_of_lt hbound)
  have hklo : -(N : ℤ) ≤ k := by exact_mod_cast hb.1
  have hkhi : k ≤ (N : ℤ) := by exact_mod_cast hb.2
  refine ⟨k, ⟨hklo, hkhi⟩, ?_⟩
  apply (div_eq_iff ha).mpr
  linarith
theorem exists_delta_avoiding_affine_integers {ι : Type*} [Finite ι]
    (a b : ι → ℝ) (ha : ∀ i, a i ≠ 0)
    {ρ B : ℝ} (hρ : 0 < ρ) (hB : ρ < B) :
    ∃ Δ : ℝ, 0 < Δ ∧ Δ < 1 / 2 ∧ ρ + Δ * ρ / 9 < B ∧
      ∀ i (k : ℤ), a i * Δ + b i ≠ k := by
  let F : ι → Set ℝ := fun i => {x | |x| ≤ 1 ∧ ∃ k : ℤ, a i * x + b i = k}
  have hF : (⋃ i, F i).Finite := Set.finite_iUnion fun i =>
    finite_affine_integer_preimages (a i) (b i) 1 (ha i)
  obtain ⟨Δ, hΔ, hhalf, hslack, havoid⟩ := exists_delta_avoiding_finite hρ hB hF
  refine ⟨Δ, hΔ, hhalf, hslack, ?_⟩
  intro i k hk
  apply havoid
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_, k, hk⟩
  rw [abs_of_pos hΔ]
  linarith
end Nagata.W06
end
section
namespace Nagata.W06
theorem exists_source_nonintegral_delta {m u₀ : ℕ} {h d ρ ρstar B : ℝ}
    (hh : 0 < h) (hdegree : h = 3 * (d - 3 * (m : ℝ)))
    (hρ : 0 < ρ) (hB : ρ < B) :
    ∃ Δ : ℝ, 0 < Δ ∧ Δ < 1 / 2 ∧ ρ + Δ * ρ / 9 < B ∧
      (∀ (j : Fin (m + 1)) (k : ℤ),
        h / 9 * (ρstar - Δ) + ((m : ℝ) - (j.val : ℝ)) * ρstar ≠ k) ∧
      (∀ (j : Fin (u₀ + 1)), m < j.val → 0 < d - 3 * (j.val : ℝ) →
        ∀ k : ℤ, (h - 9 * ((j.val : ℝ) - (m : ℝ))) / 9 * (ρstar - Δ) ≠ k) := by
  classical
  let J := {j : Fin (u₀ + 1) // m < j.val ∧ 0 < d - 3 * (j.val : ℝ)}
  let : Fintype J := inferInstance
  let a : Fin (m + 1) ⊕ J → ℝ := Sum.elim
    (fun _ => -(h / 9))
    (fun j => -((h - 9 * ((j.val.val : ℝ) - (m : ℝ))) / 9))
  let b : Fin (m + 1) ⊕ J → ℝ := Sum.elim
    (fun j => h / 9 * ρstar + ((m : ℝ) - (j.val : ℝ)) * ρstar)
    (fun j => (h - 9 * ((j.val.val : ℝ) - (m : ℝ))) / 9 * ρstar)
  have ha : ∀ i, a i ≠ 0 := by
    intro i
    cases i with
    | inl j =>
      dsimp [a]
      exact neg_ne_zero.mpr (div_ne_zero (ne_of_gt hh) (by norm_num))
    | inr j =>
      have hj := j.property.2
      have hnum : 0 < h - 9 * ((j.val.val : ℝ) - (m : ℝ)) := by linarith
      dsimp [a]
      exact neg_ne_zero.mpr (div_ne_zero (ne_of_gt hnum) (by norm_num))
  obtain ⟨Δ, hΔ, hhalf, hslack, hall⟩ :=
    exists_delta_avoiding_affine_integers a b ha hρ hB
  refine ⟨Δ, hΔ, hhalf, hslack, ?_, ?_⟩
  · intro j k hk
    apply hall (Sum.inl j) k
    dsimp [a, b]
    calc
      -(h / 9) * Δ + (h / 9 * ρstar + ((m : ℝ) - (j.val : ℝ)) * ρstar) =
          h / 9 * (ρstar - Δ) + ((m : ℝ) - (j.val : ℝ)) * ρstar := by ring
      _ = k := hk
  · intro j hjm hjd k hk
    apply hall (Sum.inr ⟨j, hjm, hjd⟩) k
    dsimp [a, b]
    calc
      -((h - 9 * ((j.val : ℝ) - (m : ℝ))) / 9) * Δ +
          (h - 9 * ((j.val : ℝ) - (m : ℝ))) / 9 * ρstar =
          (h - 9 * ((j.val : ℝ) - (m : ℝ))) / 9 * (ρstar - Δ) := by ring
      _ = k := hk
end Nagata.W06
end
section
noncomputable section
namespace Nagata.W06.TorusConfiguration
open Nagata.Workers.W05
open Nagata.W21
open Filter
open scoped Topology
end Nagata.W06.TorusConfiguration
end
end
section
noncomputable section
namespace Nagata.W06.TorusConfiguration
open Nagata.Workers.W05 Nagata.W21 Nagata.ProjectiveGeometry
open Filter Metric
open scoped Topology
end Nagata.W06.TorusConfiguration
end
end
section
noncomputable section
namespace Nagata.W06.LineArrangement
def extraPoint (K : Type*) [Field K] (k t : ℕ) : K × K :=
  (-((k + 2 + t : ℕ) : K), 0)
variable {K : Type*} [Field K] [CharZero K]
omit [CharZero K] in
theorem extraPoint_zero (k : ℕ) : extraPoint K k 0 = additionalPoint K k := by
  simp [extraPoint, additionalPoint]
omit [CharZero K] in
theorem extraPoint_on_zero (k t : ℕ) :
    lineValue 0 (extraPoint K k t).1 (extraPoint K k t).2 = 0 := by
  simp [extraPoint, lineValue, graphValue]
def manyMarkedPoints (K : Type*) [Field K] (k n : ℕ) : Finset (K × K) := by
  classical
  exact markedPoints K k ∪ (Finset.range n).image (extraPoint K k)
omit [CharZero K] in
theorem markedPoint_mem_manyMarkedPoints (k n : ℕ) (i s : Fin k) :
    markedPoint K k i s ∈ manyMarkedPoints K k n := by
  classical
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨(i, s), Finset.mem_univ _, rfl⟩
omit [CharZero K] in
theorem extraPoint_mem_manyMarkedPoints (k n t : ℕ) (ht : t < n) :
    extraPoint K k t ∈ manyMarkedPoints K k n := by
  classical
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, rfl⟩
omit [CharZero K] in
theorem triangle_additionalPoint_mem (r : ℕ) (hr : 10 ≤ r) :
    additionalPoint K 3 ∈ manyMarkedPoints K 3 (r - 9) := by
  rw [← extraPoint_zero]
  exact extraPoint_mem_manyMarkedPoints 3 (r - 9) 0 (by omega)
end Nagata.W06.LineArrangement
end
end
section
noncomputable section
namespace Nagata.W06.LineArrangement
open Nagata.ProjectiveGeometry
end Nagata.W06.LineArrangement
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.Workers.W05
theorem rhoStar_identity (r : ℝ) (hr : 0 ≤ r) :
    2 * (3 * (Real.sqrt r - 3)) + (3 * (Real.sqrt r - 3)) ^ 2 / 9 = r - 9 := by
  have hs := Real.sq_sqrt hr
  nlinarith
theorem rho_bounds (r d m : ℝ) (_hm : 0 < m)
    (hlow : 3 < d / m) (hupp : d / m < Real.sqrt r) :
    0 < 3 * (d / m - 3) ∧
      3 * (d / m - 3) < 3 * (Real.sqrt r - 3) ∧
      0 < 3 * (Real.sqrt r - 3) := by
  constructor
  · linarith
  constructor <;> linarith
theorem exists_contraction (rho a : ℝ) (hrho : 0 ≤ rho) (hgap : rho < a) :
    ∃ lam : ℝ, 0 < lam ∧ lam < 1 ∧ rho < lam * a - 9 * (1 - lam) := by
  have hden : 0 < a + 9 := by linarith
  have hfracpos : 0 < (rho + 9) / (a + 9) := div_pos (by linarith) hden
  have hfrac : (rho + 9) / (a + 9) < 1 :=
    (div_lt_one hden).2 (by linarith)
  obtain ⟨lam, hlow, hupp⟩ := exists_between hfrac
  refine ⟨lam, lt_trans hfracpos hlow, hupp, ?_⟩
  have hprod := (div_lt_iff₀ hden).1 hlow
  nlinarith
theorem exists_positive_scaling (q lam m : ℝ)
    (hq : 0 < q) (hlam : lam < 1) (hm : 0 < m) :
    ∃ n : ℕ, 0 < n ∧ 1 ≤ q * (1 - lam) * ((n : ℝ) * m) := by
  have hc : 0 < q * (1 - lam) * m := mul_pos (mul_pos hq (by linarith)) hm
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (q * (1 - lam) * m))
  have hnreal : 0 < (n : ℝ) := lt_trans (div_pos zero_lt_one hc) hn
  have hprod := (div_lt_iff₀ hc).1 hn
  refine ⟨n, by exact_mod_cast hnreal, ?_⟩
  nlinarith [hprod]
theorem ratio_scale (d m : ℝ) (n : ℕ) (hn : 0 < n) :
    ((n : ℝ) * d) / ((n : ℝ) * m) = d / m := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  exact mul_div_mul_left d m hn'
theorem degree_eq_mul_rho (d m : ℝ) (hm : 0 < m) :
    3 * (d - 3 * m) = m * (3 * (d / m - 3)) := by
  field_simp [ne_of_gt hm]
theorem q_pos (r : ℝ) (hr : 10 ≤ r) : 0 < r - 9 := by linarith
end Nagata.Workers.W05
end
section
namespace Nagata.Workers.W05
open Nagata.FiniteExponents
theorem natural_integer_floor (D : ℕ) : ((D / 3 : ℕ) : ℤ) = (D : ℤ) / 3 := by
  exact Int.natCast_ediv D 3
theorem coefficient_index_iff (D : ℕ) (j : ℤ) :
    0 ≤ j ∧ j ≤ (D : ℤ) / 3 ↔
      ∃ i : Fin (D / 3 + 1), (i.val : ℤ) = j := by
  rw [← natural_integer_floor]
  constructor
  · rintro ⟨hj0, hjD⟩
    have hjnat : j.toNat ≤ D / 3 := by omega
    exact ⟨⟨j.toNat, by omega⟩, Int.toNat_of_nonneg hj0⟩
  · rintro ⟨i, rfl⟩
    have hi := i.isLt
    omega
end Nagata.Workers.W05
end
section
namespace Nagata.Workers.W05
theorem exists_numeric_choices (r d m : ℕ) (hr : 10 ≤ r) (hm : 0 < m)
    (hlow : 3 < (d : ℝ) / (m : ℝ))
    (hupp : (d : ℝ) / (m : ℝ) < Real.sqrt (r : ℝ)) :
    ∃ (n : ℕ) (lam Δ : ℝ) (x : Fin 9 → ℝ),
      0 < n ∧ 0 < lam ∧ lam < 1 ∧
      1 ≤ ((r : ℝ) - 9) * (1 - lam) * ((n * m : ℕ) : ℝ) ∧
      0 < Δ ∧ Δ < 1 / 2 ∧
      (3 * ((d : ℝ) / (m : ℝ) - 3)) +
          Δ * (3 * ((d : ℝ) / (m : ℝ) - 3)) / 9 <
        lam * (3 * (Real.sqrt (r : ℝ) - 3)) - 9 * (1 - lam) ∧
      Function.Injective x ∧ (∀ i, 0 < x i ∧ x i < 1 / 2) ∧
      (∑ i : Fin 9, (1 / 2 - x i)) = Δ ∧
      (∀ (j : Fin (n * m + 1)) (k : ℤ),
        (3 * (((n * d : ℕ) : ℝ) - 3 * ((n * m : ℕ) : ℝ))) / 9 *
          (3 * (Real.sqrt (r : ℝ) - 3) - Δ) +
          (((n * m : ℕ) : ℝ) - (j.val : ℝ)) *
            (3 * (Real.sqrt (r : ℝ) - 3)) ≠ k) ∧
      (∀ (j : Fin (n * d / 3 + 1)), n * m < j.val →
        0 < ((n * d : ℕ) : ℝ) - 3 * (j.val : ℝ) → ∀ k : ℤ,
        ((3 * (((n * d : ℕ) : ℝ) - 3 * ((n * m : ℕ) : ℝ))) -
          9 * ((j.val : ℝ) - ((n * m : ℕ) : ℝ))) / 9 *
            (3 * (Real.sqrt (r : ℝ) - 3) - Δ) ≠ k) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hrR : (10 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  obtain ⟨hρ, hρa, _⟩ := rho_bounds (r : ℝ) (d : ℝ) (m : ℝ) hmR hlow hupp
  obtain ⟨lam, hlam0, hlam1, hgap⟩ :=
    exists_contraction _ _ (le_of_lt hρ) hρa
  obtain ⟨n, hn, hscale⟩ :=
    exists_positive_scaling ((r : ℝ) - 9) lam (m : ℝ) (q_pos _ hrR) hlam1 hmR
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hd : 0 < (d : ℝ) - 3 * (m : ℝ) := by
    have hprod := (lt_div_iff₀ hmR).mp hlow
    linarith
  have hscaled : 0 < 3 * (((n * d : ℕ) : ℝ) - 3 * ((n * m : ℕ) : ℝ)) := by
    push_cast
    nlinarith [mul_pos hnR hd]
  obtain ⟨Δ, hΔ, hhalf, hslack, hnonint1, hnonint2⟩ :=
    Nagata.W06.exists_source_nonintegral_delta
      (m := n * m) (u₀ := n * d / 3)
      (d := ((n * d : ℕ) : ℝ))
      (ρstar := 3 * (Real.sqrt (r : ℝ) - 3))
      hscaled rfl hρ hgap
  obtain ⟨x, hxinj, hxbounds, hxsum⟩ := Nagata.W06.exists_marked_parameters hΔ hhalf
  refine ⟨n, lam, Δ, x, hn, hlam0, hlam1, ?_, hΔ, hhalf, hslack,
    hxinj, hxbounds, hxsum, hnonint1, hnonint2⟩
  simpa only [Nat.cast_mul] using hscale
end Nagata.Workers.W05
end
section
namespace Nagata.Workers.W05
open Nagata.FiniteExponents
theorem firstLower_nonintegral_of_fin (D M : ℕ) (a Δ : ℝ)
    (h : ∀ (i : Fin (M + 1)) (k : ℤ),
      (3 * ((D : ℝ) - 3 * M)) / 9 * (a - Δ) +
        ((M : ℝ) - (i.val : ℝ)) * a ≠ k)
    (j : ℤ) (hj0 : 0 ≤ j) (hjM : j ≤ M) :
    firstLower (D : ℤ) (M : ℤ) j a Δ ∉ Set.range (Int.cast : ℤ → ℝ) := by
  let i : Fin (M + 1) := ⟨j.toNat, by omega⟩
  have hi : (i.val : ℝ) = (j : ℝ) := by
    dsimp [i]
    exact_mod_cast Int.toNat_of_nonneg hj0
  rintro ⟨k, hk⟩
  apply h i k
  rw [hi]
  simpa [firstLower, commonDegree] using hk.symm
theorem secondLower_nonintegral_of_fin (D M : ℕ) (a Δ : ℝ)
    (h : ∀ (i : Fin (D / 3 + 1)), M < i.val →
      0 < (D : ℝ) - 3 * (i.val : ℝ) → ∀ k : ℤ,
      ((3 * ((D : ℝ) - 3 * M)) - 9 * ((i.val : ℝ) - (M : ℝ))) / 9 *
        (a - Δ) ≠ k)
    (j : ℤ) (hjM : (M : ℤ) < j) (hjD : j ≤ (D : ℤ) / 3)
    (hjpos : 0 < (D : ℤ) - 3 * j) :
    secondLower (D : ℤ) j a Δ ∉ Set.range (Int.cast : ℤ → ℝ) := by
  have hj0 : 0 ≤ j := by omega
  obtain ⟨i, hi⟩ := (coefficient_index_iff D j).mp ⟨hj0, hjD⟩
  have hiR : (i.val : ℝ) = (j : ℝ) := by exact_mod_cast hi
  have hiM : M < i.val := by omega
  have hipos : 0 < (D : ℝ) - 3 * (i.val : ℝ) := by
    rw [hiR]
    exact_mod_cast hjpos
  rintro ⟨k, hk⟩
  apply h i hiM hipos k
  rw [hiR]
  have hnum : 3 * ((D : ℝ) - 3 * M) - 9 * ((j : ℝ) - M) =
      3 * ((D : ℝ) - 3 * j) := by ring
  rw [hnum]
  simpa [secondLower, sourceDegree] using hk.symm
end Nagata.Workers.W05
end
section
namespace Nagata.Workers.W05
open scoped BigOperators
theorem exists_scaled_parameters (r d m : ℕ) (hr : 10 ≤ r) (hm : 0 < m)
    (hlow : 3 < (d : ℝ) / m) (hupp : (d : ℝ) / m < Real.sqrt r) :
    ∃ (n D M q : ℕ) (rho a h lam Δ eta : ℝ) (x : Fin 9 → ℝ),
      0 < n ∧ D = n * d ∧ M = n * m ∧ q = r - 9 ∧
      0 < D ∧ 0 < M ∧ 0 < q ∧ M ≤ D / 3 ∧
      (D : ℝ) / M = (d : ℝ) / m ∧
      rho = 3 * ((D : ℝ) / M - 3) ∧ a = 3 * (Real.sqrt r - 3) ∧
      h = 3 * ((D : ℝ) - 3 * M) ∧ h = (M : ℝ) * rho ∧
      0 < rho ∧ rho < a ∧ 0 < a ∧ 0 < h ∧
      2 * a + a ^ 2 / 9 = (q : ℝ) ∧
      0 < lam ∧ lam < 1 ∧ rho < lam * a - 9 * (1 - lam) ∧
      1 ≤ (q : ℝ) * (1 - lam) * M ∧
      0 < Δ ∧ Δ < 1 / 2 ∧ rho + Δ * rho / 9 < lam * a - 9 * (1 - lam) ∧
      (∀ (j : Fin (M + 1)) (k : ℤ),
        h / 9 * (a - Δ) + ((M : ℝ) - (j.val : ℝ)) * a ≠ k) ∧
      (∀ (j : Fin (D / 3 + 1)), M < j.val → 0 < (D : ℝ) - 3 * (j.val : ℝ) →
        ∀ k : ℤ, (h - 9 * ((j.val : ℝ) - (M : ℝ))) / 9 * (a - Δ) ≠ k) ∧
      Function.Injective x ∧ (∀ i, 0 < x i ∧ x i < 1 / 2) ∧
      (∑ i : Fin 9, (1 / 2 - x i)) = Δ ∧
      (∑ i : Fin 9, x i) = 9 / 2 - Δ ∧
      eta = ((∑ i : Fin 9, x i) + a) / 3 ∧
      3 * eta = (∑ i : Fin 9, x i) + a := by
  obtain ⟨n, lam, Δ, x, hn, hlam0, hlam1, hscale, hΔ, hhalf, hslack,
    hxinj, hxbounds, hxsum, hnonint1, hnonint2⟩ :=
    exists_numeric_choices r d m hr hm hlow hupp
  let D := n * d
  let M := n * m
  let rho : ℝ := 3 * ((d : ℝ) / m - 3)
  let a : ℝ := 3 * (Real.sqrt r - 3)
  let h : ℝ := 3 * ((D : ℝ) - 3 * M)
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hM : 0 < M := Nat.mul_pos hn hm
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  have hdegree : 3 * m < d := by
    have ht := (lt_div_iff₀ hmR).mp hlow
    exact_mod_cast ht
  have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hdegree
  have hD : 0 < D := Nat.mul_pos hn hd
  have hscaleddegree : 3 * M < D := by
    dsimp [D, M]
    simpa only [Nat.mul_left_comm n 3 m] using Nat.mul_lt_mul_of_pos_left hdegree hn
  have hu0 : M ≤ D / 3 := (Nat.le_div_iff_mul_le (by decide)).2 (by
    simpa only [Nat.mul_comm M 3] using le_of_lt hscaleddegree)
  have hratio : (D : ℝ) / M = (d : ℝ) / m := by
    dsimp [D, M]
    simpa only [Nat.cast_mul] using ratio_scale (d : ℝ) (m : ℝ) n hn
  have hratioeq : rho = 3 * ((D : ℝ) / M - 3) := by rw [hratio]
  have hhrho : h = (M : ℝ) * rho := by
    rw [hratioeq]
    exact degree_eq_mul_rho (D : ℝ) (M : ℝ) hMR
  obtain ⟨hrho, hrhoa, ha⟩ := rho_bounds (r : ℝ) (d : ℝ) (m : ℝ) hmR hlow hupp
  have hh : 0 < h := by rw [hhrho]; exact mul_pos hMR hrho
  have hr9 : 9 ≤ r := le_trans (by decide : 9 ≤ 10) hr
  have hq : 0 < r - 9 := Nat.sub_pos_iff_lt.mpr (lt_of_lt_of_le (by decide : 9 < 10) hr)
  have hqcast : ((r - 9 : ℕ) : ℝ) = (r : ℝ) - 9 := by
    rw [Nat.cast_sub hr9]
    norm_num
  have hcoef : 2 * a + a ^ 2 / 9 = ((r - 9 : ℕ) : ℝ) := by
    rw [hqcast]
    exact rhoStar_identity (r : ℝ) (Nat.cast_nonneg r)
  have hgap : rho < lam * a - 9 * (1 - lam) := by
    have hp : 0 ≤ Δ * rho / 9 := div_nonneg (mul_nonneg (le_of_lt hΔ) (le_of_lt hrho)) (by norm_num)
    linarith
  have hsum : (∑ i : Fin 9, x i) = 9 / 2 - Δ := by
    have hs := hxsum
    rw [Finset.sum_sub_distrib] at hs
    norm_num at hs
    linarith
  refine ⟨n, D, M, r - 9, rho, a, h, lam, Δ,
    ((∑ i : Fin 9, x i) + a) / 3, x,
    hn, rfl, rfl, rfl, hD, hM, hq, hu0, hratio, hratioeq, rfl, rfl, hhrho,
    hrho, hrhoa, ha, hh, hcoef, hlam0, hlam1, hgap, ?_,
    hΔ, hhalf, hslack, hnonint1, hnonint2, hxinj, hxbounds, hxsum, hsum, rfl, ?_⟩
  · rw [hqcast]
    exact hscale
  · ring
end Nagata.Workers.W05
end
section
namespace Nagata.Workers.W05
end Nagata.Workers.W05
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W08
theorem automorphicSection_analyticAt {τ γ : ℂ} {n : ℤ}
    (f : automorphicSections τ n γ) {z : ℂ} (hz : z ≠ 0) :
    AnalyticAt ℂ f.val z := by
  have hd : DifferentiableOn ℂ f.val {w : ℂ | w ≠ 0} :=
    fun w hw ↦ (f.property.2.1 w hw).differentiableWithinAt
  exact hd.analyticAt (isOpen_ne.mem_nhds hz)
theorem automorphicSection_analyticOnNhd {τ γ : ℂ} {n : ℤ}
    (f : automorphicSections τ n γ) :
    AnalyticOnNhd ℂ f.val {z : ℂ | z ≠ 0} :=
  fun _ hz ↦ automorphicSection_analyticAt f hz
end Nagata.W08
end
section
noncomputable section
namespace Nagata.W08
open Nagata.W21
variable {R : Type*} [CommGroupWithZero R]
end Nagata.W08
end
end
section
noncomputable section
namespace Nagata.W06.TorusConfiguration
open Nagata.W21
end Nagata.W06.TorusConfiguration
end
end
section
noncomputable section
namespace Nagata.W08
open Nagata.W21
end Nagata.W08
end
end
section
noncomputable section
namespace Nagata.W08
open Nagata.W21 Filter Topology
end Nagata.W08
end
end
section
namespace Nagata.CoefficientSpaces
theorem exists_holomorphic_quotient {τ γ δ : ℂ} {n s : ℤ}
    (hτ : τ ≠ 0) (hδ : δ ≠ 0)
    (f : Nagata.W08.automorphicSections τ n γ)
    (P : Nagata.W08.automorphicSections τ s δ) (k : ℕ)
    (hzero : ∀ z ≠ 0, P.val z = 0 → deriv P.val z ≠ 0 ∧
      (k : ℕ∞) ≤ analyticOrderAt f.val z) :
    ∃ G : Nagata.W08.automorphicSections τ (n - (k : ℤ) * s) (γ / δ ^ k),
      ∀ z ≠ 0, f.val z = P.val z ^ k * G.val z :=
  exists_automorphic_quotient hτ hδ f P
    (Nagata.W08.automorphicSection_analyticOnNhd f)
    (Nagata.W08.automorphicSection_analyticOnNhd P) k hzero
end Nagata.CoefficientSpaces
end
section
noncomputable section
namespace Nagata.W08
open Nagata.W21 Filter Topology
end Nagata.W08
end
end
section
noncomputable section
namespace Nagata.W08
open Nagata.W21 Nagata.Workers.W05
end Nagata.W08
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W21
open Filter Topology
open scoped BigOperators
noncomputable def thetaPositive (τ z : ℂ) : ℂ :=
  ∏' n : ℕ, (1 - τ ^ n * z)
noncomputable def thetaProduct (τ z : ℂ) : ℂ :=
  thetaPositive τ z * thetaPositive τ (τ * z⁻¹)
theorem thetaPositive_multipliable {τ : ℂ} (hτ : ‖τ‖ < 1) (z : ℂ) :
    Multipliable (fun n : ℕ ↦ 1 - τ ^ n * z) := by
  simpa only [mul_neg, sub_eq_add_neg] using
    Complex.multipliable_one_add_of_summable
      ((summable_geometric_of_norm_lt_one hτ).mul_right (-z))
theorem thetaProduct_eq_source (τ z : ℂ) :
    thetaProduct τ z = (∏' n : ℕ, (1 - τ ^ n * z)) *
      ∏' n : ℕ, (1 - τ ^ (n + 1) / z) := by
  simp only [thetaProduct, thetaPositive, div_eq_mul_inv, pow_succ, mul_assoc]
theorem thetaPositive_shift {τ : ℂ} (hτ : ‖τ‖ < 1) (z : ℂ) :
    thetaPositive τ z = (1 - z) * thetaPositive τ (τ * z) := by
  have hm : Multipliable (fun n : ℕ ↦ 1 - τ ^ (n + 1) * z) := by
    simpa only [pow_succ, mul_assoc] using thetaPositive_multipliable hτ (τ * z)
  simpa only [thetaPositive, pow_zero, one_mul, pow_succ, mul_assoc] using
    tprod_eq_zero_mul' (f := fun n : ℕ ↦ 1 - τ ^ n * z) hm
theorem thetaProduct_automorphy {τ z : ℂ} (hτ : ‖τ‖ < 1)
    (hτ0 : τ ≠ 0) (hz : z ≠ 0) :
    thetaProduct τ (τ * z) = -z⁻¹ * thetaProduct τ z := by
  have hc : τ * (τ * z)⁻¹ = z⁻¹ := by
    rw [mul_inv_rev]
    calc
      τ * (z⁻¹ * τ⁻¹) = (τ * τ⁻¹) * z⁻¹ := by ac_rfl
      _ = z⁻¹ := by rw [mul_inv_cancel₀ hτ0, one_mul]
  have hb : 1 - z⁻¹ = -z⁻¹ * (1 - z) := by
    symm
    rw [mul_sub, mul_one, neg_mul, sub_neg_eq_add, inv_mul_cancel₀ hz, add_comm]
    exact (sub_eq_add_neg 1 z⁻¹).symm
  unfold thetaProduct
  rw [hc, thetaPositive_shift hτ z⁻¹, hb]
  calc
    thetaPositive τ (τ * z) * ((-z⁻¹ * (1 - z)) * thetaPositive τ (τ * z⁻¹)) =
        -z⁻¹ * (((1 - z) * thetaPositive τ (τ * z)) *
          thetaPositive τ (τ * z⁻¹)) := by ac_rfl
    _ = -z⁻¹ * (thetaPositive τ z * thetaPositive τ (τ * z⁻¹)) := by
      rw [← thetaPositive_shift hτ z]
theorem thetaProduct_automorphy_real {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {z : ℂ} (hz : z ≠ 0) :
    thetaProduct (τ : ℂ) ((τ : ℂ) * z) = -z⁻¹ * thetaProduct (τ : ℂ) z := by
  apply thetaProduct_automorphy
  · simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ0] using hτ1
  · exact Complex.ofReal_ne_zero.mpr (ne_of_gt hτ0)
  · exact hz
theorem thetaProduct_scaled_automorphy {τ a z : ℂ} (hτ : ‖τ‖ < 1)
    (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hz : z ≠ 0) :
    thetaProduct τ ((τ * z) / a) = (-a) * z⁻¹ * thetaProduct τ (z / a) := by
  simpa only [div_eq_mul_inv, mul_assoc, mul_inv_rev, inv_inv, neg_mul] using
    thetaProduct_automorphy hτ hτ0 (div_ne_zero hz ha)
theorem thetaPositive_ne_zero {τ : ℂ} (hτ : ‖τ‖ < 1) (z : ℂ)
    (hz : ∀ n : ℕ, 1 - τ ^ n * z ≠ 0) : thetaPositive τ z ≠ 0 := by
  have hn : Summable (fun n : ℕ ↦ ‖-(τ ^ n * z)‖) := by
    simpa only [norm_neg, norm_mul, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg τ) hτ).mul_right ‖z‖
  have hf : ∀ n : ℕ, 1 + -(τ ^ n * z) ≠ 0 := by
    simpa only [sub_eq_add_neg] using hz
  simpa only [thetaPositive, sub_eq_add_neg] using
    tprod_one_add_ne_zero_of_summable hf hn
theorem thetaPositive_eq_zero_iff {τ : ℂ} (hτ : ‖τ‖ < 1) (z : ℂ) :
    thetaPositive τ z = 0 ↔ ∃ n : ℕ, τ ^ n * z = 1 := by
  classical
  constructor
  · intro hp
    by_contra hf
    have hn : ∀ n : ℕ, 1 - τ ^ n * z ≠ 0 := by
      intro n hn
      apply hf
      exact ⟨n, (sub_eq_zero.mp hn).symm⟩
    exact thetaPositive_ne_zero hτ z hn hp
  · rintro ⟨n, hn⟩
    exact tprod_of_exists_eq_zero (f := fun n : ℕ ↦ 1 - τ ^ n * z)
      ⟨n, by change 1 - τ ^ n * z = 0; rw [hn, sub_self]⟩
theorem thetaProduct_eq_zero_iff_factors {τ : ℂ} (hτ : ‖τ‖ < 1) (z : ℂ) :
    thetaProduct τ z = 0 ↔
      (∃ n : ℕ, τ ^ n * z = 1) ∨ (∃ n : ℕ, τ ^ n * (τ * z⁻¹) = 1) := by
  rw [thetaProduct, mul_eq_zero, thetaPositive_eq_zero_iff hτ z,
    thetaPositive_eq_zero_iff hτ (τ * z⁻¹)]
end Nagata.W21
end
section
namespace Nagata.W21
open Filter Topology
open scoped BigOperators
theorem thetaPositive_hasProdUniformlyOn_comp {α : Type*} [TopologicalSpace α]
    {τ : ℂ} (hτ : ‖τ‖ < 1) {K : Set α} (hK : IsCompact K)
    (g : α → ℂ) (hg : ContinuousOn g K) (R : ℝ)
    (hR : ∀ x ∈ K, ‖g x‖ ≤ R) :
    HasProdUniformlyOn (fun (n : ℕ) x ↦ 1 - τ ^ n * g x)
      (fun x ↦ thetaPositive τ (g x)) K := by
  have hu : Summable (fun n : ℕ ↦ ‖τ‖ ^ n * R) :=
    (summable_geometric_of_lt_one (norm_nonneg τ) hτ).mul_right R
  have hb : ∀ᶠ n : ℕ in atTop, ∀ x ∈ K, ‖-(τ ^ n * g x)‖ ≤ ‖τ‖ ^ n * R := by
    exact Eventually.of_forall fun n x hx ↦ by
      rw [norm_neg, norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (hR x hx) (pow_nonneg (norm_nonneg τ) n)
  have hc : ∀ n : ℕ, ContinuousOn (fun x ↦ -(τ ^ n * g x)) K :=
    fun n ↦ (continuousOn_const.mul hg).neg
  simpa only [sub_eq_add_neg, thetaPositive] using
    Summable.hasProdUniformlyOn_nat_one_add hK hu hb hc
theorem thetaNegative_hasProdUniformlyOn {τ : ℂ} (hτ : ‖τ‖ < 1)
    {K : Set ℂ} (hK : IsCompact K) (hz : ∀ z ∈ K, z ≠ 0) :
    HasProdUniformlyOn (fun (n : ℕ) (z : ℂ) ↦ 1 - τ ^ (n + 1) / z)
      (fun z ↦ thetaPositive τ (τ * z⁻¹)) K := by
  have hg : ContinuousOn (fun z : ℂ ↦ τ * z⁻¹) K :=
    continuousOn_const.mul (continuousOn_id.inv₀ hz)
  obtain ⟨R, hR⟩ := (hK.image_of_continuousOn hg).isBounded.exists_norm_le
  have hu := thetaPositive_hasProdUniformlyOn_comp hτ hK
    (fun z : ℂ ↦ τ * z⁻¹) hg R (fun z hz ↦ hR _ ⟨z, hz, rfl⟩)
  simpa only [pow_succ, div_eq_mul_inv, mul_assoc] using hu
theorem thetaNegative_hasProdLocallyUniformlyOn {τ : ℂ} (hτ : ‖τ‖ < 1) :
    HasProdLocallyUniformlyOn (fun (n : ℕ) (z : ℂ) ↦ 1 - τ ^ (n + 1) / z)
      (fun z ↦ thetaPositive τ (τ * z⁻¹)) {z : ℂ | z ≠ 0} := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_ne
  intro K hKs hK
  exact thetaNegative_hasProdUniformlyOn hτ hK (fun z hz ↦ hKs hz)
theorem thetaPositive_hasProdLocallyUniformlyOn {τ : ℂ} (hτ : ‖τ‖ < 1) :
    HasProdLocallyUniformlyOn (fun (n : ℕ) (z : ℂ) ↦ 1 - τ ^ n * z)
      (thetaPositive τ) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  exact thetaPositive_hasProdUniformlyOn_comp hτ hK (fun z ↦ z)
    continuousOn_id R hR
theorem thetaPositive_differentiable {τ : ℂ} (hτ : ‖τ‖ < 1) :
    Differentiable ℂ (thetaPositive τ) := by
  have hlim := (thetaPositive_hasProdLocallyUniformlyOn hτ).tendstoLocallyUniformlyOn_finsetRange
  have hd : ∀ N : ℕ, DifferentiableOn ℂ
      (fun z ↦ ∏ n ∈ Finset.range N, (1 - τ ^ n * z)) Set.univ := by
    intro N
    exact DifferentiableOn.fun_finsetProd fun n _ ↦
      (differentiableOn_const (1 : ℂ)).sub ((differentiableOn_const (τ ^ n)).mul differentiableOn_id)
  exact differentiableOn_univ.mp
    (hlim.differentiableOn (Eventually.of_forall hd) isOpen_univ)
theorem thetaProduct_differentiableAt {τ z : ℂ} (hτ : ‖τ‖ < 1) (hz : z ≠ 0) :
    DifferentiableAt ℂ (thetaProduct τ) z := by
  have hp := thetaPositive_differentiable hτ
  exact (hp z).mul ((hp (τ * z⁻¹)).fun_comp' z
    ((differentiableAt_const τ).mul (differentiableAt_inv hz)))
theorem thetaPositive_parameter_ne_zero {τ : ℂ} (hτ : ‖τ‖ < 1) :
    thetaPositive τ τ ≠ 0 := by
  apply thetaPositive_ne_zero hτ τ
  intro n hn
  have he : τ ^ (n + 1) = 1 := by
    simpa only [pow_succ] using (sub_eq_zero.mp hn).symm
  have hlt : ‖τ ^ (n + 1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg τ) hτ (Nat.succ_ne_zero n)
  rw [he, norm_one] at hlt
  exact (lt_irrefl (1 : ℝ)) hlt
theorem thetaProduct_one {τ : ℂ} (hτ : ‖τ‖ < 1) : thetaProduct τ 1 = 0 := by
  rw [thetaProduct, thetaPositive_shift hτ 1]
  simp
theorem thetaProduct_hasDerivAt_one {τ : ℂ} (hτ : ‖τ‖ < 1) :
    HasDerivAt (thetaProduct τ) (-(thetaPositive τ τ) ^ 2) 1 := by
  have hp := thetaPositive_differentiable hτ
  have hg : DifferentiableAt ℂ
      (fun z : ℂ ↦ thetaPositive τ (τ * z) * thetaPositive τ (τ * z⁻¹)) 1 :=
    ((hp (τ * 1)).fun_comp' 1 ((differentiableAt_const τ).mul differentiableAt_id)).mul
      ((hp (τ * (1 : ℂ)⁻¹)).fun_comp' 1
        ((differentiableAt_const τ).mul (differentiableAt_inv one_ne_zero)))
  have heq : thetaProduct τ = fun z : ℂ ↦
      (1 - z) * (thetaPositive τ (τ * z) * thetaPositive τ (τ * z⁻¹)) := by
    funext z
    rw [thetaProduct, thetaPositive_shift hτ z]
    exact mul_assoc _ _ _
  rw [heq]
  apply (((hasDerivAt_id' (x := (1 : ℂ))).const_sub 1).mul hg.hasDerivAt).congr_deriv
  simp [pow_two]
theorem thetaProduct_deriv_one_ne_zero {τ : ℂ} (hτ : ‖τ‖ < 1) :
    deriv (thetaProduct τ) 1 ≠ 0 := by
  rw [(thetaProduct_hasDerivAt_one hτ).deriv]
  exact neg_ne_zero.mpr (pow_ne_zero 2 (thetaPositive_parameter_ne_zero hτ))
end Nagata.W21
end
section
namespace Nagata.W21
theorem thetaProduct_eq_zero_iff_nat_powers {τ z : ℂ} (hτ : ‖τ‖ < 1)
    (hτ0 : τ ≠ 0) (hz : z ≠ 0) :
    thetaProduct τ z = 0 ↔
      (∃ n : ℕ, z = (τ ^ n)⁻¹) ∨ (∃ n : ℕ, z = τ ^ (n + 1)) := by
  rw [thetaProduct_eq_zero_iff_factors hτ z]
  constructor
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · exact Or.inl ⟨n, ((mul_eq_one_iff_inv_eq₀ (pow_ne_zero n hτ0)).mp hn).symm⟩
    · have he : τ ^ (n + 1) * z⁻¹ = 1 := by
        simpa only [pow_succ, mul_assoc] using hn
      exact Or.inr ⟨n, ((mul_inv_eq_one₀ hz).mp he).symm⟩
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · exact Or.inl ⟨n, (mul_eq_one_iff_inv_eq₀ (pow_ne_zero n hτ0)).mpr hn.symm⟩
    · right
      refine ⟨n, ?_⟩
      have he : τ ^ (n + 1) * z⁻¹ = 1 := (mul_inv_eq_one₀ hz).mpr hn.symm
      simpa only [pow_succ, mul_assoc] using he
theorem thetaProduct_eq_zero_iff_zpow {τ z : ℂ} (hτ : ‖τ‖ < 1)
    (hτ0 : τ ≠ 0) (hz : z ≠ 0) :
    thetaProduct τ z = 0 ↔ ∃ k : ℤ, z = τ ^ k := by
  rw [thetaProduct_eq_zero_iff_nat_powers hτ hτ0 hz]
  constructor
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · exact ⟨-(n : ℤ), by simpa only [zpow_neg, zpow_natCast] using hn⟩
    · exact ⟨((n + 1 : ℕ) : ℤ), by simpa only [zpow_natCast] using hn⟩
  · rintro ⟨k, rfl⟩
    cases k with
    | ofNat n =>
      cases n with
      | zero => exact Or.inl ⟨0, by simp⟩
      | succ n => exact Or.inr ⟨n, zpow_natCast τ (n + 1)⟩
    | negSucc n => exact Or.inl ⟨n + 1, by simp only [zpow_negSucc]⟩
theorem thetaProduct_scaled_eq_zero_iff {τ a z : ℂ} (hτ : ‖τ‖ < 1)
    (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hz : z ≠ 0) :
    thetaProduct τ (z / a) = 0 ↔ ∃ k : ℤ, z = a * τ ^ k := by
  rw [thetaProduct_eq_zero_iff_zpow hτ hτ0 (div_ne_zero hz ha)]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by simpa only [mul_comm] using (div_eq_iff ha).mp hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, (div_eq_iff ha).mpr (by simpa only [mul_comm] using hk)⟩
end Nagata.W21
end
section
namespace Nagata.W21
open Filter Topology
theorem thetaProduct_zpow_eq_zero {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0)
    (k : ℤ) : thetaProduct τ (τ ^ k) = 0 :=
  (thetaProduct_eq_zero_iff_zpow hτ hτ0 (zpow_ne_zero k hτ0)).mpr ⟨k, rfl⟩
theorem thetaProduct_deriv_mul_at_zero {τ z : ℂ} (hτ : ‖τ‖ < 1)
    (hτ0 : τ ≠ 0) (hz : z ≠ 0) (hzero : thetaProduct τ z = 0) :
    deriv (thetaProduct τ) (τ * z) * τ = -z⁻¹ * deriv (thetaProduct τ) z := by
  have hl := (thetaProduct_differentiableAt hτ (mul_ne_zero hτ0 hz)).hasDerivAt.comp z
    (hasDerivAt_const_mul τ (x := z))
  have hr := (hasDerivAt_inv hz).neg.mul
    (thetaProduct_differentiableAt hτ hz).hasDerivAt
  have heq : (fun w : ℂ ↦ thetaProduct τ (τ * w)) =ᶠ[𝓝 z]
      (fun w : ℂ ↦ -w⁻¹ * thetaProduct τ w) :=
    Filter.Eventually.mono (isOpen_ne.mem_nhds hz) fun w hw ↦
      thetaProduct_automorphy hτ hτ0 hw
  have he := (hl.congr_of_eventuallyEq heq.symm).unique hr
  simpa only [hzero, mul_zero, zero_add, Pi.neg_apply] using he
theorem thetaProduct_deriv_mul_ne_zero_iff {τ z : ℂ} (hτ : ‖τ‖ < 1)
    (hτ0 : τ ≠ 0) (hz : z ≠ 0) (hzero : thetaProduct τ z = 0) :
    deriv (thetaProduct τ) (τ * z) ≠ 0 ↔ deriv (thetaProduct τ) z ≠ 0 := by
  have he := thetaProduct_deriv_mul_at_zero hτ hτ0 hz hzero
  constructor
  · intro hmul hd
    have hbad : deriv (thetaProduct τ) (τ * z) * τ = 0 := by
      rw [he, hd, mul_zero]
    exact (mul_ne_zero hmul hτ0) hbad
  · intro hd hmul
    have hbad : -z⁻¹ * deriv (thetaProduct τ) z = 0 := by
      rw [← he, hmul, zero_mul]
    exact (mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hz)) hd) hbad
theorem thetaProduct_deriv_pow_ne_zero {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0)
    (n : ℕ) : deriv (thetaProduct τ) (τ ^ n) ≠ 0 := by
  induction n with
  | zero => simpa only [pow_zero] using thetaProduct_deriv_one_ne_zero hτ
  | succ n ih =>
    have hz : thetaProduct τ (τ ^ n) = 0 := by
      simpa only [zpow_natCast] using thetaProduct_zpow_eq_zero hτ hτ0 (n : ℤ)
    have hd := (thetaProduct_deriv_mul_ne_zero_iff hτ hτ0 (pow_ne_zero n hτ0) hz).mpr ih
    simpa only [pow_succ', Nat.succ_eq_add_one] using hd
theorem thetaProduct_deriv_inv_pow_ne_zero {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0)
    (n : ℕ) : deriv (thetaProduct τ) ((τ ^ n)⁻¹) ≠ 0 := by
  induction n with
  | zero => simpa only [pow_zero, inv_one] using thetaProduct_deriv_one_ne_zero hτ
  | succ n ih =>
    have hz : thetaProduct τ ((τ ^ (n + 1))⁻¹) = 0 := by
      simpa only [zpow_neg, zpow_natCast] using
        thetaProduct_zpow_eq_zero hτ hτ0 (-((n + 1 : ℕ) : ℤ))
    have hm : τ * (τ ^ (n + 1))⁻¹ = (τ ^ n)⁻¹ := by
      rw [pow_succ, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hτ0, one_mul]
    have hd : deriv (thetaProduct τ) (τ * (τ ^ (n + 1))⁻¹) ≠ 0 := by
      rwa [hm]
    exact (thetaProduct_deriv_mul_ne_zero_iff hτ hτ0
      (inv_ne_zero (pow_ne_zero (n + 1) hτ0)) hz).mp hd
theorem thetaProduct_zero_has_nonzero_deriv {τ z : ℂ} (hτ : ‖τ‖ < 1)
    (hτ0 : τ ≠ 0) (hz : z ≠ 0) (hzero : thetaProduct τ z = 0) :
    deriv (thetaProduct τ) z ≠ 0 := by
  obtain ⟨k, rfl⟩ := (thetaProduct_eq_zero_iff_zpow hτ hτ0 hz).mp hzero
  cases k with
  | ofNat n =>
    simpa only [Int.ofNat_eq_natCast, zpow_natCast] using thetaProduct_deriv_pow_ne_zero hτ hτ0 n
  | negSucc n =>
    simpa only [zpow_negSucc] using thetaProduct_deriv_inv_pow_ne_zero hτ hτ0 (n + 1)
end Nagata.W21
end
section
namespace Nagata.W21
open scoped BigOperators
noncomputable def markedThetaProduct {ι : Type*} [Fintype ι] (τ : ℂ) (a : ι → ℂ)
    (z : ℂ) : ℂ := ∏ i, thetaProduct τ (z / a i)
theorem thetaProduct_scaled_differentiableAt {τ a z : ℂ} (hτ : ‖τ‖ < 1)
    (ha : a ≠ 0) (hz : z ≠ 0) : DifferentiableAt ℂ (fun w ↦ thetaProduct τ (w / a)) z :=
  (thetaProduct_differentiableAt (τ := τ) (z := z / a) hτ (div_ne_zero hz ha)).fun_comp' z
    ((differentiableAt_id (𝕜 := ℂ) (x := z)).div_const a)
theorem markedThetaProduct_differentiableAt {ι : Type*} [Fintype ι]
    {τ : ℂ} {a : ι → ℂ} {z : ℂ} (hτ : ‖τ‖ < 1) (ha : ∀ i, a i ≠ 0)
    (hz : z ≠ 0) : DifferentiableAt ℂ (markedThetaProduct τ a) z := by
  classical
  exact DifferentiableAt.fun_finsetProd fun i _ ↦
    thetaProduct_scaled_differentiableAt hτ (ha i) hz
theorem markedThetaProduct_eq_zero_iff {ι : Type*} [Fintype ι]
    {τ : ℂ} {a : ι → ℂ} {z : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0)
    (ha : ∀ i, a i ≠ 0) (hz : z ≠ 0) :
    markedThetaProduct τ a z = 0 ↔ ∃ i, ∃ k : ℤ, z = a i * τ ^ k := by
  classical
  simp only [markedThetaProduct, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and,
    thetaProduct_scaled_eq_zero_iff hτ hτ0 (ha _) hz]
theorem thetaProduct_scaled_zero_has_nonzero_deriv {τ a z : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hz : z ≠ 0)
    (hf : thetaProduct τ (z / a) = 0) :
    deriv (fun w ↦ thetaProduct τ (w / a)) z ≠ 0 := by
  have hd := (thetaProduct_differentiableAt hτ (div_ne_zero hz ha)).hasDerivAt.comp z
    ((hasDerivAt_id z).div_const a)
  change HasDerivAt (fun w ↦ thetaProduct τ (w / a))
    (deriv (thetaProduct τ) (z / a) * (1 / a)) z at hd
  rw [hd.deriv]
  exact mul_ne_zero (thetaProduct_zero_has_nonzero_deriv hτ hτ0 (div_ne_zero hz ha) hf)
    (div_ne_zero one_ne_zero ha)
end Nagata.W21
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W08
theorem exists_complex_nonroot {ι : Type*} [Countable ι]
    (p : ι → Polynomial ℂ) (hp : ∀ i, p i ≠ 0) :
    ∃ b : ℂ, ∀ i, (p i).eval b ≠ 0 := by
  let : Uncountable ℂ := Cardinal.aleph0_lt_mk_iff.mp (by
    rw [Cardinal.mk_complex]
    exact Cardinal.cantor Cardinal.aleph0)
  let B : Set ℂ := ⋃ i, {b | (p i).IsRoot b}
  have hB : B.Countable := Set.countable_iUnion fun i =>
    (Polynomial.finite_setOfPred_isRoot (hp i)).countable
  have hex : ∃ b : ℂ, b ∉ B := by
    by_contra h
    have hu : B = Set.univ := Set.eq_univ_of_forall fun b =>
      Classical.not_not.mp (fun hb => h ⟨b, hb⟩)
    exact Set.not_countable_univ (hu ▸ hB)
  obtain ⟨b, hb⟩ := hex
  exact ⟨b, fun i hi => hb (Set.mem_iUnion.mpr ⟨i, hi⟩)⟩
open Polynomial in
theorem exists_cubic_second_mark {τ a γ : ℂ} (hτ : τ ≠ 0) (ha : a ≠ 0) :
    ∃ b : ℂ, b ≠ 0 ∧
      (∀ k : ℤ, b ≠ a * τ ^ k) ∧
      (∀ k : ℤ, a ^ 2 * b * τ ^ k + γ ≠ 0) ∧
      (∀ k : ℤ, a * b ^ 2 * τ ^ k + γ ≠ 0) := by
  let p : Fin 4 × ℤ → Polynomial ℂ := fun i =>
    if i.1 = 0 then X else if i.1 = 1 then X - C (a * τ ^ i.2)
    else if i.1 = 2 then C (a ^ 2 * τ ^ i.2) * X + C γ
    else C (a * τ ^ i.2) * X ^ 2 + C γ
  have hp : ∀ i, p i ≠ 0 := by
    rintro ⟨j, k⟩ he
    fin_cases j
    · have hc := congrArg (fun q : Polynomial ℂ => q.coeff 1) he
      norm_num [p] at hc
    · have hc := congrArg (fun q : Polynomial ℂ => q.coeff 1) he
      norm_num [p] at hc
    · have hc := congrArg (fun q : Polynomial ℂ => q.coeff 1) he
      change (C (a ^ 2 * τ ^ k) * X + C γ).coeff 1 = (0 : Polynomial ℂ).coeff 1 at hc
      simp only [coeff_add, coeff_C_mul_X, coeff_C, coeff_zero] at hc
      norm_num [ha, zpow_ne_zero k hτ] at hc
    · have hc := congrArg (fun q : Polynomial ℂ => q.coeff 2) he
      change (C (a * τ ^ k) * X ^ 2 + C γ).coeff 2 = (0 : Polynomial ℂ).coeff 2 at hc
      simp only [coeff_add, coeff_C_mul_X_pow, coeff_C, coeff_zero] at hc
      norm_num [ha, zpow_ne_zero k hτ] at hc
  obtain ⟨b, hb⟩ := exists_complex_nonroot p hp
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · simpa [p] using hb (0, 0)
  · intro k
    simpa [p, sub_ne_zero] using hb (1, k)
  · intro k
    simpa [p, mul_assoc, mul_left_comm, mul_comm] using hb (2, k)
  · intro k
    simpa [p, mul_assoc, mul_left_comm, mul_comm] using hb (3, k)
end Nagata.W08
end
end
section
noncomputable section
namespace Nagata.W08
open Nagata.W21
def thetaProductSection {τ a : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) :
    automorphicSections τ 1 (-a) :=
  sectionOfFunction hτ0 (fun z ↦ thetaProduct τ (z / a))
    (fun z hz ↦ by
      have hd := thetaProduct_differentiableAt hτ (div_ne_zero hz ha)
      have hc : DifferentiableAt ℂ (fun z : ℂ ↦ z / a) z := by
        simp only [div_eq_mul_inv]
        exact differentiableAt_id.mul_const _
      exact hd.comp z hc)
    (fun z hz ↦ by
      simpa only [zpow_neg_one] using thetaProduct_scaled_automorphy hτ hτ0 ha hz)
@[simp] theorem thetaProductSection_apply {τ a z : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hz : z ≠ 0) :
    (thetaProductSection hτ hτ0 ha).val z = thetaProduct τ (z / a) := by
  change normalizeAtZero (fun w ↦ thetaProduct τ (w / a)) z = thetaProduct τ (z / a)
  exact normalizeAtZero_of_ne _ hz
end Nagata.W08
end
end
section
noncomputable section
namespace Nagata.W08
end Nagata.W08
end
end
section
noncomputable section
namespace Nagata.W08
open Nagata.W21
open scoped BigOperators
theorem markedThetaProduct_automorphy {ι : Type*} [Fintype ι]
    {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    {z : ℂ} (hz : z ≠ 0) :
    markedThetaProduct τ a (τ * z) =
      (∏ i, -a i) * z ^ (-(Fintype.card ι : ℤ)) * markedThetaProduct τ a z := by
  classical
  unfold markedThetaProduct
  simp_rw [thetaProduct_scaled_automorphy hτ hτ0 (ha _) hz]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, zpow_neg, zpow_natCast, inv_pow]
def markedThetaSection {ι : Type*} [Fintype ι]
    {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0) :
    automorphicSections τ (Fintype.card ι : ℤ) (∏ i, -a i) :=
  sectionOfFunction hτ0 (markedThetaProduct τ a)
    (fun _ hz ↦ markedThetaProduct_differentiableAt hτ ha hz)
    (fun _ hz ↦ markedThetaProduct_automorphy hτ hτ0 a ha hz)
@[simp] theorem markedThetaSection_apply {ι : Type*} [Fintype ι]
    {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    {z : ℂ} (hz : z ≠ 0) :
    (markedThetaSection hτ hτ0 a ha).val z = markedThetaProduct τ a z := by
  change normalizeAtZero (markedThetaProduct τ a) z = markedThetaProduct τ a z
  exact normalizeAtZero_of_ne _ hz
end Nagata.W08
end
end
section
noncomputable section
namespace Nagata.W08
open Nagata.W07
theorem normalizedThetaSeries_differentiable {n τ : ℝ} (hn : 0 < n)
    (hτ : 0 < τ) (hτone : τ < 1) (a K : ℝ) {ε : ℂ} (hε : ε ≠ 0) :
    Differentiable ℂ (fun x : ℂ ↦ ∑' p : ℤ, normalizedThetaTerm n a K ε τ p x) :=
  Nagata.W02.differentiable_normalizedThetaSeries_allTau hn hτ hτone hε
end Nagata.W08
end
end
section
namespace Nagata.W08
open Nagata.W21 Filter Topology
theorem thetaProductSection_zero_iff {τ a z : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hz : z ≠ 0) :
    (thetaProductSection hτ hτ0 ha).val z = 0 ↔ ∃ k : ℤ, z = a * τ ^ k := by
  rw [thetaProductSection_apply hτ hτ0 ha hz]
  exact thetaProduct_scaled_eq_zero_iff hτ hτ0 ha hz
@[simp] theorem thetaProductSection_at_mark {τ a : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) :
    (thetaProductSection hτ hτ0 ha).val a = 0 := by
  rw [thetaProductSection_apply hτ hτ0 ha ha, div_self ha]
  exact thetaProduct_one hτ
theorem thetaProductSection_deriv {τ a z : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hz : z ≠ 0) :
    deriv (thetaProductSection hτ hτ0 ha).val z =
      deriv (fun w ↦ thetaProduct τ (w / a)) z := by
  apply Filter.EventuallyEq.deriv_eq
  exact normalizeAtZero_eventuallyEq (fun w ↦ thetaProduct τ (w / a)) hz
theorem thetaProductSection_zero_has_nonzero_deriv {τ a z : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hz : z ≠ 0)
    (hf : (thetaProductSection hτ hτ0 ha).val z = 0) :
    deriv (thetaProductSection hτ hτ0 ha).val z ≠ 0 := by
  rw [thetaProductSection_deriv hτ hτ0 ha hz]
  apply thetaProduct_scaled_zero_has_nonzero_deriv hτ hτ0 ha hz
  simpa only [thetaProductSection_apply hτ hτ0 ha hz] using hf
end Nagata.W08
end
section
namespace Nagata.W08
open Nagata.W21 Filter Topology
end Nagata.W08
end
section
noncomputable section
namespace Nagata.W08
open Nagata.W07
def normalizedThetaSection (n K : ℤ) (hn : 0 < n) (a : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) :
    automorphicSections (τ : ℂ) n (ε * ((τ ^ ((K : ℝ) - a) : ℝ) : ℂ)) :=
  automorphicSectionOfPeriodicFunction
    (fun x ↦ ∑' p : ℤ, normalizedThetaTerm (n : ℝ) a (K : ℝ) ε τ p x)
    (normalizedThetaSeries_differentiable (by exact_mod_cast hn) hτ hτone a (K : ℝ) hε)
    (fun x k ↦ normalizedThetaSeries_integerPeriod n K k a ε τ x)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hτ))
    (fun x ↦ by
      rw [← Complex.ofReal_log hτ.le]
      simpa using normalizedThetaSeries_realShift (n : ℝ) a (K : ℝ) hε hτ x)
theorem normalizedThetaSection_exp (n K : ℤ) (hn : 0 < n) (a : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (x : ℂ) :
    (normalizedThetaSection n K hn a hε hτ hτone).val (Complex.exp x) =
      ∑' p : ℤ, normalizedThetaTerm (n : ℝ) a (K : ℝ) ε τ p x := by
  apply automorphicSectionOfPeriodicFunction_exp
end Nagata.W08
end
end
section
noncomputable section
namespace Nagata.W08
open Nagata.W07
theorem normalizedThetaSection_centered (n K : ℤ) (hn : 0 < n) (a x₀ : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (x : ℂ) :
    ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ) *
      (normalizedThetaSection n K hn a hε hτ hτone).val
        (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      ∑' p : ℤ, normalizedThetaTerm (n : ℝ) (a + x₀ * (n : ℝ)) (K : ℝ) ε τ p x := by
  have he : Complex.exp (((x₀ * Real.log τ : ℝ) : ℂ)) = ((τ ^ x₀ : ℝ) : ℂ) := by
    rw [Real.rpow_def_of_pos hτ, Complex.ofReal_exp]
    congr 1
    rw [mul_comm x₀ (Real.log τ)]
  have hcenter : Complex.exp (((x₀ * Real.log τ : ℝ) : ℂ) + x) =
      ((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x := by
    rw [Complex.exp_add, he]
  rw [← hcenter, normalizedThetaSection_exp, ← tsum_mul_left]
  exact tsum_congr fun p ↦ normalizedThetaTerm_shift hτ (n : ℝ) a (K : ℝ) x₀ ε x p
end Nagata.W08
end
end
section
noncomputable section
namespace Nagata.W08
end Nagata.W08
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W09
open Complex Metric
open Nagata.W07 Nagata.W22
noncomputable def thetaCircleMajorant (τ σ x₀ : ℝ) (n K : ℤ) (p : ℤ) : ℝ :=
  thetaDiskMajorant (n : ℝ) (K : ℝ) (2 * Real.pi)
    (Real.exp ((n : ℝ) * (2 * Real.pi)) *
      τ ^ thetaMargin (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))) 0 p
theorem thetaCircleMajorant_summable {τ : ℝ} (hτ : 0 < τ)
    (σ x₀ : ℝ) {n : ℤ} (hn : 0 ≤ n) (K : ℤ)
    (hhalf : Real.exp ((n : ℝ) * (2 * Real.pi)) *
      τ ^ thetaMargin (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)) ≤ 1 / 2) :
    Summable (thetaCircleMajorant τ σ x₀ n K) := by
  exact summable_thetaDiskMajorant (by exact_mod_cast hn)
    (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hτ.le _)) hhalf _ _ _
theorem normalizedLaurentMonomial_circle_bound {τ : ℝ} (hτ : 0 < τ) (hτone : τ ≤ 1)
    (σ x₀ : ℝ) {ε : ℂ} (hε : ‖ε‖ = 1) {n : ℤ} (hn : 0 ≤ n)
    (K p : ℤ) {z : ℂ} (hz : z ∈ sphere 0 (τ ^ x₀)) :
    ‖normalizedLaurentCoefficient τ σ x₀ ε n K p * z ^ (K + n * p)‖ ≤
      thetaCircleMajorant τ σ x₀ n K p := by
  obtain ⟨θ, hθ, rfl⟩ := exists_circle_angle_of_mem_sphere (Real.rpow_pos_of_pos hτ _) hz
  have hx : ‖(θ : ℂ) * Complex.I‖ ≤ 2 * Real.pi := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
      abs_of_pos hθ.1] using hθ.2
  have heval : circleMap 0 (τ ^ x₀) θ = ((τ ^ x₀ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    simp only [circleMap, zero_add]
  rw [heval, normalizedLaurentCoefficient_eval hτ]
  simpa only [thetaCircleMajorant, thetaDiskMajorant, pow_zero, mul_one] using
    norm_normalizedThetaTerm_le (by exact_mod_cast hn) hτ hτone hε
      (by positivity : 0 ≤ 2 * Real.pi) hx p
theorem normalizedLaurentMonomial_hasSum_on_circle
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ ≤ 1) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ‖ε‖ = 1) {n : ℤ} (hn : 0 ≤ n) (K : ℤ)
    (hhalf : Real.exp ((n : ℝ) * (2 * Real.pi)) *
      τ ^ thetaMargin (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)) ≤ 1 / 2)
    (f : ℂ → ℂ)
    (hlocal : ∀ x : ℂ, f (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      ∑' p : ℤ, normalizedThetaTerm (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x)
    {z : ℂ} (hz : z ∈ sphere 0 (τ ^ x₀)) :
    HasSum (fun p : ℤ => normalizedLaurentCoefficient τ σ x₀ ε n K p * z ^ (K + n * p)) (f z) := by
  obtain ⟨θ, hθ, rfl⟩ := exists_circle_angle_of_mem_sphere (Real.rpow_pos_of_pos hτ _) hz
  have hx : ‖(θ : ℂ) * Complex.I‖ ≤ 2 * Real.pi := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
      abs_of_pos hθ.1] using hθ.2
  have heval : circleMap 0 (τ ^ x₀) θ = ((τ ^ x₀ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    simp only [circleMap, zero_add]
  rw [heval, hlocal]
  simpa only [normalizedLaurentCoefficient_eval hτ, normalizedThetaSeries] using
    hasSum_normalizedThetaTerm_on_disk (by exact_mod_cast hn) hτ hτone hε
      (by positivity : 0 ≤ 2 * Real.pi) hhalf hx
theorem analyticLaurentCoeff_of_local_theta_series
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ ≤ 1) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ‖ε‖ = 1) {n : ℤ} (hn : 0 < n) (K : ℤ)
    (hhalf : Real.exp ((n : ℝ) * (2 * Real.pi)) *
      τ ^ thetaMargin (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)) ≤ 1 / 2)
    (f : ℂ → ℂ)
    (hlocal : ∀ x : ℂ, f (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      ∑' p : ℤ, normalizedThetaTerm (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x) (p : ℤ) :
    analyticLaurentCoeff (τ ^ x₀) f (K + n * p) = normalizedLaurentCoefficient τ σ x₀ ε n K p := by
  refine analyticLaurentCoeff_monomial_series_at (Real.rpow_pos_of_pos hτ _)
    (normalizedLaurentCoefficient τ σ x₀ ε n K) (fun p : ℤ => K + n * p)
    ?_ f (thetaCircleMajorant τ σ x₀ n K)
    (thetaCircleMajorant_summable hτ σ x₀ hn.le K hhalf) ?_ ?_ p
  · intro a b hab
    exact mul_left_cancel₀ hn.ne' (add_left_cancel hab)
  · intro i z hz
    exact normalizedLaurentMonomial_circle_bound hτ hτone σ x₀ hε hn.le K i hz
  · intro z hz
    exact normalizedLaurentMonomial_hasSum_on_circle hτ hτone σ x₀ hε hn.le K hhalf f hlocal hz
theorem analyticLaurentCoeff_local_theta_off_residue
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ ≤ 1) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ‖ε‖ = 1) {n : ℤ} (hn : 0 ≤ n) (K : ℤ)
    (hhalf : Real.exp ((n : ℝ) * (2 * Real.pi)) *
      τ ^ thetaMargin (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)) ≤ 1 / 2)
    (f : ℂ → ℂ)
    (hlocal : ∀ x : ℂ, f (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      ∑' p : ℤ, normalizedThetaTerm (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x) (k : ℤ) (hk : k % n ≠ K % n) :
    analyticLaurentCoeff (τ ^ x₀) f k = 0 := by
  refine analyticLaurentCoeff_monomial_series_eq_zero (Real.rpow_pos_of_pos hτ _)
    (normalizedLaurentCoefficient τ σ x₀ ε n K) (fun p : ℤ => K + n * p)
    f (thetaCircleMajorant τ σ x₀ n K)
    (thetaCircleMajorant_summable hτ σ x₀ hn K hhalf) ?_ ?_ k ?_
  · intro i z hz
    exact normalizedLaurentMonomial_circle_bound hτ hτone σ x₀ hε hn K i hz
  · intro z hz
    exact normalizedLaurentMonomial_hasSum_on_circle hτ hτone σ x₀ hε hn K hhalf f hlocal hz
  · rintro ⟨p, hp⟩
    apply hk
    rw [← hp]
    simp
theorem analyticLaurentCoeff_local_theta_eq_supportedOrbit
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ ≤ 1) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ‖ε‖ = 1) {n : ℤ} (hn : 0 < n) (K : ℤ)
    (hhalf : Real.exp ((n : ℝ) * (2 * Real.pi)) *
      τ ^ thetaMargin (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)) ≤ 1 / 2)
    (f : ℂ → ℂ)
    (hlocal : ∀ x : ℂ, f (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      ∑' p : ℤ, normalizedThetaTerm (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x) (k : ℤ) :
    analyticLaurentCoeff (τ ^ x₀) f k =
      supportedOrbitCoefficient (τ : ℂ) (ε * ((τ ^ σ : ℝ) : ℂ)) n K
        ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ) k := by
  by_cases hdiv : n ∣ k - K
  · let p := (k - K) / n
    have hp : n * p = k - K := Int.mul_ediv_cancel_of_dvd hdiv
    have hk : k = K + n * p := by omega
    rw [hk, analyticLaurentCoeff_of_local_theta_series hτ hτone σ x₀ hε hn K hhalf f hlocal,
      supportedOrbitCoefficient_on_orbit _ _ hn.ne', normalizedLaurentCoefficient_eq_orbitValue hτ]
  · have hres : k % n ≠ K % n := by
      intro heq
      exact hdiv (Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp heq))
    rw [analyticLaurentCoeff_local_theta_off_residue hτ hτone σ x₀ hε hn.le K hhalf f hlocal k hres]
    simp only [supportedOrbitCoefficient, if_neg hdiv]
end Nagata.W09
end
section
noncomputable section
namespace Nagata.W09
open Nagata.W07 Complex Metric
theorem norm_normalizedThetaTerm_imaginary {n a K τ : ℝ} {ε : ℂ}
    (hτ : 0 < τ) (hε : ‖ε‖ = 1) (p : ℤ) (θ : ℝ) :
    ‖normalizedThetaTerm n a K ε τ p ((θ : ℂ) * Complex.I)‖ =
      τ ^ thetaExponent n a (p : ℝ) := by
  simp [normalizedThetaTerm, hε, Complex.norm_exp,
    Complex.mul_re, Complex.mul_im, abs_of_nonneg (Real.rpow_nonneg hτ.le _)]
theorem summable_geometric_natAbs {q : ℝ} (hq : 0 ≤ q) (hqone : q < 1) :
    Summable (fun p : ℤ => q ^ p.natAbs) := by
  have hs := summable_geometric_of_lt_one hq hqone
  have hp : Summable (fun t : ℕ => q ^ (t : ℤ).natAbs) := by simpa using hs
  have hnat (t : ℕ) : ((t : ℤ) + 1).natAbs = t + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Int.natAbs_natCast (t + 1)
  have hm : Summable (fun t : ℕ => q ^ (-(t + 1 : ℤ)).natAbs) := by
    simpa only [Int.natAbs_neg, hnat] using
      (summable_nat_add_iff (f := fun t : ℕ => q ^ t) 1).2 hs
  exact hp.of_nat_of_neg_add_one hm
noncomputable def thetaImaginaryMajorant (τ n a : ℝ) (p : ℤ) : ℝ :=
  (τ ^ thetaMargin n a) ^ p.natAbs
theorem thetaImaginaryMajorant_summable {τ n a : ℝ}
    (hτ : 0 < τ) (hτone : τ < 1) (ha : 0 < a) (han : a < n) :
    Summable (thetaImaginaryMajorant τ n a) :=
  summable_geometric_natAbs (Real.rpow_nonneg hτ.le _)
    (Real.rpow_lt_one hτ.le hτone (thetaMargin_pos ha han))
theorem normalizedLaurentMonomial_circle_sharp_bound {τ : ℝ}
    (hτ : 0 < τ) (hτone : τ ≤ 1) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ‖ε‖ = 1) {n : ℤ} (hn : 0 ≤ n)
    (K p : ℤ) {z : ℂ} (hz : z ∈ sphere 0 (τ ^ x₀)) :
    ‖normalizedLaurentCoefficient τ σ x₀ ε n K p * z ^ (K + n * p)‖ ≤
      thetaImaginaryMajorant τ (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)) p := by
  obtain ⟨θ, _, rfl⟩ := exists_circle_angle_of_mem_sphere (Real.rpow_pos_of_pos hτ _) hz
  have heval : circleMap 0 (τ ^ x₀) θ = ((τ ^ x₀ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    simp only [circleMap, zero_add]
  rw [heval, normalizedLaurentCoefficient_eval hτ,
    norm_normalizedThetaTerm_imaginary hτ hε]
  exact theta_power_le_geometric (by exact_mod_cast hn) hτ hτone p
theorem normalizedThetaTerm_hasSum_imaginary {τ n a K : ℝ}
    (hτ : 0 < τ) (hτone : τ < 1) (hn : 0 ≤ n) (ha : 0 < a) (han : a < n)
    {ε : ℂ} (hε : ‖ε‖ = 1) (θ : ℝ) :
    HasSum (fun p : ℤ => normalizedThetaTerm n a K ε τ p ((θ : ℂ) * Complex.I))
      (∑' p : ℤ, normalizedThetaTerm n a K ε τ p ((θ : ℂ) * Complex.I)) := by
  apply Summable.hasSum
  apply Summable.of_norm
  apply (thetaImaginaryMajorant_summable hτ hτone ha han).of_nonneg_of_le
  · intro p; exact norm_nonneg _
  · intro p
    rw [norm_normalizedThetaTerm_imaginary hτ hε]
    exact theta_power_le_geometric hn hτ hτone.le p
end Nagata.W09
end
end
section
noncomputable section
namespace Nagata.W09
open Nagata.W07
def normalizedSourceThetaSection (n K : ℤ) (hn : 0 < n) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) :
    Nagata.W08.automorphicSections (τ : ℂ) n (ε * ((τ ^ σ : ℝ) : ℂ)) := by
  let g := Nagata.W08.normalizedThetaSection n K hn ((K : ℝ) - σ) hε hτ hτone
  let c : ℂ := ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ)
  refine ⟨fun z => c * g.val z, ?_, ?_, ?_⟩
  · change c * g.val 0 = 0
    rw [g.property.1, mul_zero]
  · intro z hz
    exact (differentiableAt_const c).mul (g.property.2.1 z hz)
  · intro z hz
    change c * g.val ((τ : ℂ) * z) = _
    rw [g.property.2.2 z hz]
    have hσ : (K : ℝ) - ((K : ℝ) - σ) = σ := by ring
    calc
      _ = (ε * ((τ ^ ((K : ℝ) - ((K : ℝ) - σ)) : ℝ) : ℂ)) *
          z ^ (-n) * (c * g.val z) := by ring
      _ = _ := congrArg (fun t : ℝ => (ε * (t : ℂ)) * z ^ (-n) * (c * g.val z))
        (congrArg (fun t : ℝ => τ ^ t) hσ)
@[simp] theorem normalizedSourceThetaSection_apply
    (n K : ℤ) (hn : 0 < n) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (z : ℂ) :
    (normalizedSourceThetaSection n K hn σ x₀ hε hτ hτone).val z =
      ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ) *
        (Nagata.W08.normalizedThetaSection n K hn ((K : ℝ) - σ) hε hτ hτone).val z := rfl
theorem normalizedSourceThetaSection_centered
    (n K : ℤ) (hn : 0 < n) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (x : ℂ) :
    (normalizedSourceThetaSection n K hn σ x₀ hε hτ hτone).val
      (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      ∑' p : ℤ, normalizedThetaTerm (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x :=
  Nagata.W08.normalizedThetaSection_centered n K hn ((K : ℝ) - σ) x₀ hε hτ hτone x
end Nagata.W09
end
end
section
namespace Nagata.W09
open Complex Metric Nagata.W07
theorem normalizedLaurentMonomial_hasSum_on_circle_all_tau
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ‖ε‖ = 1) {n : ℤ} (hn : 0 ≤ n) (K : ℤ)
    (ha : 0 < (K : ℝ) - σ + x₀ * (n : ℝ))
    (han : (K : ℝ) - σ + x₀ * (n : ℝ) < (n : ℝ))
    (f : ℂ → ℂ)
    (hlocal : ∀ x : ℂ, f (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      ∑' p : ℤ, normalizedThetaTerm (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x)
    {z : ℂ} (hz : z ∈ sphere 0 (τ ^ x₀)) :
    HasSum (fun p : ℤ => normalizedLaurentCoefficient τ σ x₀ ε n K p * z ^ (K + n * p)) (f z) := by
  obtain ⟨θ, hθ, rfl⟩ := exists_circle_angle_of_mem_sphere (Real.rpow_pos_of_pos hτ _) hz
  have heval : circleMap 0 (τ ^ x₀) θ = ((τ ^ x₀ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    simp only [circleMap, zero_add]
  rw [heval, hlocal]
  simpa only [normalizedLaurentCoefficient_eval hτ] using
    normalizedThetaTerm_hasSum_imaginary hτ hτone (by exact_mod_cast hn) ha han hε θ
theorem analyticLaurentCoeff_of_local_theta_series_all_tau
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ‖ε‖ = 1) {n : ℤ} (hn : 0 < n) (K : ℤ)
    (ha : 0 < (K : ℝ) - σ + x₀ * (n : ℝ))
    (han : (K : ℝ) - σ + x₀ * (n : ℝ) < (n : ℝ))
    (f : ℂ → ℂ)
    (hlocal : ∀ x : ℂ, f (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      ∑' p : ℤ, normalizedThetaTerm (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x) (p : ℤ) :
    analyticLaurentCoeff (τ ^ x₀) f (K + n * p) = normalizedLaurentCoefficient τ σ x₀ ε n K p := by
  refine analyticLaurentCoeff_monomial_series_at (Real.rpow_pos_of_pos hτ _)
    (normalizedLaurentCoefficient τ σ x₀ ε n K) (fun p : ℤ => K + n * p)
    ?_ f (thetaImaginaryMajorant τ (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)))
    (thetaImaginaryMajorant_summable hτ hτone ha han) ?_ ?_ p
  · intro a b hab
    exact mul_left_cancel₀ hn.ne' (add_left_cancel hab)
  · intro i z hz
    exact normalizedLaurentMonomial_circle_sharp_bound hτ hτone.le σ x₀ hε hn.le K i hz
  · intro z hz
    exact normalizedLaurentMonomial_hasSum_on_circle_all_tau hτ hτone σ x₀ hε hn.le K ha han f hlocal hz
theorem analyticLaurentCoeff_local_theta_off_residue_all_tau
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ‖ε‖ = 1) {n : ℤ} (hn : 0 ≤ n) (K : ℤ)
    (ha : 0 < (K : ℝ) - σ + x₀ * (n : ℝ))
    (han : (K : ℝ) - σ + x₀ * (n : ℝ) < (n : ℝ))
    (f : ℂ → ℂ)
    (hlocal : ∀ x : ℂ, f (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      ∑' p : ℤ, normalizedThetaTerm (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x) (k : ℤ) (hk : k % n ≠ K % n) :
    analyticLaurentCoeff (τ ^ x₀) f k = 0 := by
  refine analyticLaurentCoeff_monomial_series_eq_zero (Real.rpow_pos_of_pos hτ _)
    (normalizedLaurentCoefficient τ σ x₀ ε n K) (fun p : ℤ => K + n * p)
    f (thetaImaginaryMajorant τ (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)))
    (thetaImaginaryMajorant_summable hτ hτone ha han) ?_ ?_ k ?_
  · intro i z hz
    exact normalizedLaurentMonomial_circle_sharp_bound hτ hτone.le σ x₀ hε hn K i hz
  · intro z hz
    exact normalizedLaurentMonomial_hasSum_on_circle_all_tau hτ hτone σ x₀ hε hn K ha han f hlocal hz
  · rintro ⟨p, hp⟩
    apply hk
    rw [← hp]
    simp
theorem analyticLaurentCoeff_local_theta_eq_supportedOrbit_all_tau
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ‖ε‖ = 1) {n : ℤ} (hn : 0 < n) (K : ℤ)
    (ha : 0 < (K : ℝ) - σ + x₀ * (n : ℝ))
    (han : (K : ℝ) - σ + x₀ * (n : ℝ) < (n : ℝ))
    (f : ℂ → ℂ)
    (hlocal : ∀ x : ℂ, f (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      ∑' p : ℤ, normalizedThetaTerm (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x) (k : ℤ) :
    analyticLaurentCoeff (τ ^ x₀) f k =
      supportedOrbitCoefficient (τ : ℂ) (ε * ((τ ^ σ : ℝ) : ℂ)) n K
        ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ) k := by
  by_cases hdiv : n ∣ k - K
  · let p := (k - K) / n
    have hp : n * p = k - K := Int.mul_ediv_cancel_of_dvd hdiv
    have hk : k = K + n * p := by omega
    rw [hk, analyticLaurentCoeff_of_local_theta_series_all_tau hτ hτone σ x₀ hε hn K ha han f hlocal,
      supportedOrbitCoefficient_on_orbit _ _ hn.ne', normalizedLaurentCoefficient_eq_orbitValue hτ]
  · have hres : k % n ≠ K % n := by
      intro heq
      exact hdiv (Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp heq))
    rw [analyticLaurentCoeff_local_theta_off_residue_all_tau hτ hτone σ x₀ hε hn.le K ha han f hlocal k hres]
    simp only [supportedOrbitCoefficient, if_neg hdiv]
end Nagata.W09
end
section
noncomputable section
namespace Nagata.W09
open Nagata.W07
theorem laurentCoefficientMap_normalizedSourceThetaSection
    (n K : ℤ) (hn : 0 < n) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) (hunit : ‖ε‖ = 1)
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (hhalf : Real.exp ((n : ℝ) * (2 * Real.pi)) *
      τ ^ thetaMargin (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)) ≤ 1 / 2) (k : ℤ) :
    laurentCoefficientMap (τ : ℂ) n (ε * ((τ ^ σ : ℝ) : ℂ))
      (normalizedSourceThetaSection n K hn σ x₀ hε hτ hτone) k =
      supportedOrbitCoefficient (τ : ℂ) (ε * ((τ ^ σ : ℝ) : ℂ)) n K
        ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ) k := by
  let f := normalizedSourceThetaSection n K hn σ x₀ hε hτ hτone
  change analyticLaurentCoeff 1 f.val k = _
  rw [← analyticLaurentCoeff_radius_independent (Real.rpow_pos_of_pos hτ x₀)
    zero_lt_one f.property.2.1 k]
  exact analyticLaurentCoeff_local_theta_eq_supportedOrbit hτ hτone.le σ x₀ hunit hn K hhalf
    f.val (normalizedSourceThetaSection_centered n K hn σ x₀ hε hτ hτone) k
theorem laurentCoefficientMap_normalizedSourceThetaSection_all_tau
    (n K : ℤ) (hn : 0 < n) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) (hunit : ‖ε‖ = 1)
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (ha : 0 < (K : ℝ) - σ + x₀ * (n : ℝ))
    (han : (K : ℝ) - σ + x₀ * (n : ℝ) < (n : ℝ)) (k : ℤ) :
    laurentCoefficientMap (τ : ℂ) n (ε * ((τ ^ σ : ℝ) : ℂ))
      (normalizedSourceThetaSection n K hn σ x₀ hε hτ hτone) k =
      supportedOrbitCoefficient (τ : ℂ) (ε * ((τ ^ σ : ℝ) : ℂ)) n K
        ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ) k := by
  let f := normalizedSourceThetaSection n K hn σ x₀ hε hτ hτone
  change analyticLaurentCoeff 1 f.val k = _
  rw [← analyticLaurentCoeff_radius_independent (Real.rpow_pos_of_pos hτ x₀)
    zero_lt_one f.property.2.1 k]
  exact analyticLaurentCoeff_local_theta_eq_supportedOrbit_all_tau hτ hτone σ x₀ hunit hn K ha han
    f.val (normalizedSourceThetaSection_centered n K hn σ x₀ hε hτ hτone) k
end Nagata.W09
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.CoefficientSpaces
def polynomialSectionCoordinates (τ γL γP : ℂ) (d m : ℤ) (P : ℂ → ℂ) :
    polynomialSections τ γL γP d m P ≃ₗ[ℂ]
      ((j : Fin ((d / 3).toNat + 1)) → coefficientSpace τ γL γP d m (j.val : ℤ) P) :=
  boundedPolynomialEquiv (d / 3).toNat
    (fun j => coefficientSpace τ γL γP d m (j : ℤ) P)
@[simp] theorem polynomialSectionCoordinates_apply
    (τ γL γP : ℂ) (d m : ℤ) (P : ℂ → ℂ)
    (F : polynomialSections τ γL γP d m P) (j : Fin ((d / 3).toNat + 1)) :
    (polynomialSectionCoordinates τ γL γP d m P F j).val = F.val.coeff j.val := rfl
def polynomialSectionBasisFromCoefficients (τ γL γP : ℂ) (d m : ℤ) (P : ℂ → ℂ)
    (I : Fin ((d / 3).toNat + 1) → Type*) [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    (c : ∀ j, coefficientSpace τ γL γP d m (j.val : ℤ) P →ₗ[ℂ] (I j → ℂ))
    (hc : ∀ j, Function.Injective (c j))
    (v : ∀ j, I j → coefficientSpace τ γL γP d m (j.val : ℤ) P)
    (hv : ∀ j i, c j (v j i) = Pi.single i 1) :
    Basis (Σ j, I j) ℂ (polynomialSections τ γL γP d m P) :=
  boundedPolynomialBasis (d / 3).toNat
    (fun j => coefficientSpace τ γL γP d m (j : ℤ) P) I
    (fun j => basisFromCoefficients (c j) (hc j) (v j) (hv j))
theorem polynomialSectionBasis_as_monomial (τ γL γP : ℂ) (d m : ℤ) (P : ℂ → ℂ)
    (I : Fin ((d / 3).toNat + 1) → Type*) [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    (c : ∀ j, coefficientSpace τ γL γP d m (j.val : ℤ) P →ₗ[ℂ] (I j → ℂ))
    (hc : ∀ j, Function.Injective (c j))
    (v : ∀ j, I j → coefficientSpace τ γL γP d m (j.val : ℤ) P)
    (hv : ∀ j i, c j (v j i) = Pi.single i 1)
    (j : Fin ((d / 3).toNat + 1)) (i : I j) :
    (polynomialSectionBasisFromCoefficients τ γL γP d m P I c hc v hv ⟨j, i⟩).val =
      Polynomial.monomial j.val (v j i).val := by
  change (boundedPolynomialBasis (d / 3).toNat
    (fun degree => coefficientSpace τ γL γP d m (degree : ℤ) P) I
    (fun index => basisFromCoefficients (c index) (hc index) (v index) (hv index))
    ⟨j, i⟩).val = _
  rw [boundedPolynomialBasis_as_monomial, basisFromCoefficients_apply]
end Nagata.Workers.W10
end
end
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.W07 Nagata.W08 Nagata.W09
variable (n : ℤ) (hn : 0 < n) (σ x₀ : ℝ)
  {ε : ℂ} (hε : ε ≠ 0) (hunit : ‖ε‖ = 1)
  {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
  (hC : Function.Injective (laurentCoefficientMap (τ : ℂ) n (ε * ((τ ^ σ : ℝ) : ℂ))))
  (hU : σ - x₀ * (n : ℝ) ∉ Set.range (Int.cast : ℤ → ℝ))
def centeredThetaSectionBasis :
    Basis (thetaIndices (σ - x₀ * (n : ℝ)) n) ℂ
      (automorphicSections (τ : ℂ) n (ε * ((τ ^ σ : ℝ) : ℂ))) := by
  have hγ : ε * ((τ ^ σ : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero hε (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos hτ σ)))
  apply basisFromSupportedOrbits (laurentCoefficientMap (τ : ℂ) n (ε * ((τ ^ σ : ℝ) : ℂ)))
    (τ : ℂ) (ε * ((τ ^ σ : ℝ) : ℂ)) (σ - x₀ * (n : ℝ)) n
    (fun K => ((τ ^ (-x₀ * (K.val : ℝ)) : ℝ) : ℂ))
    (fun K => normalization_scalar_ne_zero hτ x₀ K.val)
    (residueCoefficientMap_injective _ hC (τ : ℂ) (ε * ((τ ^ σ : ℝ) : ℂ))
      (Complex.ofReal_ne_zero.mpr (ne_of_gt hτ)) hγ _ hn
      (laurentCoefficientMap_recurrence_pos_real hτ n _ hγ))
    (fun K => normalizedSourceThetaSection n K.val hn σ x₀ hε hτ hτone)
  intro K k
  have hmem := (mem_thetaIndices_iff hU).mp K.property
  exact laurentCoefficientMap_normalizedSourceThetaSection_all_tau n K.val hn σ x₀ hε hunit
    hτ hτone (by linarith [hmem.1]) (by linarith [hmem.2]) k
@[simp] theorem centeredThetaSectionBasis_apply
    (K : thetaIndices (σ - x₀ * (n : ℝ)) n) :
    centeredThetaSectionBasis n hn σ x₀ hε hunit hτ hτone hC hU K =
    normalizedSourceThetaSection n K.val hn σ x₀ hε hτ hτone := by
  unfold centeredThetaSectionBasis
  exact basisFromSupportedOrbits_apply _ _ _ _ _ _ _ _ _ _ K
end Nagata.Workers.W10
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.W08 Nagata.CoefficientSpaces
def firstCoefficientEquiv (τ γL γP : ℂ) (d m j : ℤ) (P : ℂ → ℂ) (hj : j ≤ m) :
    automorphicSections τ (3 * (d - 3 * m))
      (γL ^ (d - 3 * m) * normalMinusMarkedMultiplier γL γP ^ (m - j)) ≃ₗ[ℂ]
      coefficientSpace τ γL γP d m j P :=
  LinearEquiv.ofEq _ _ (by simp only [coefficientSpace, if_pos hj])
def highCoefficientMap (τ γL γP : ℂ) (d m j : ℤ) (P : ℂ → ℂ) (hj : m < j) :
    automorphicSections τ (3 * (d - 3 * j)) (γL ^ (d - 3 * j)) →ₗ[ℂ]
      coefficientSpace τ γL γP d m j P where
  toFun f := ⟨multiplyPower P (j - m).toNat f.val,
    (mem_coefficientSpace_second hj).mpr ⟨f.val, f.property, rfl⟩⟩
  map_add' f g := by apply Subtype.ext; exact (multiplyPower P (j - m).toNat).map_add f.val g.val
  map_smul' a f := by apply Subtype.ext; exact (multiplyPower P (j - m).toNat).map_smul a f.val
theorem highCoefficientMap_surjective (τ γL γP : ℂ) (d m j : ℤ)
    (P : ℂ → ℂ) (hj : m < j) :
    Function.Surjective (highCoefficientMap τ γL γP d m j P hj) := by
  intro g
  obtain ⟨f, hf, hfg⟩ := (mem_coefficientSpace_second hj).mp g.property
  refine ⟨⟨f, hf⟩, ?_⟩
  apply Subtype.ext
  exact hfg
theorem highCoefficientMap_injective (τ γL γP : ℂ) (d m j : ℤ)
    (P : ℂ → ℂ) (hj : m < j)
    (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
    (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤) :
    Function.Injective (highCoefficientMap τ γL γP d m j P hj) := by
  intro f g hfg
  apply multiplySection_injective τ (γL ^ (d - 3 * j)) (3 * (d - 3 * j))
    P (j - m).toNat hP hPfin
  exact congrArg Subtype.val hfg
def highCoefficientEquiv (τ γL γP : ℂ) (d m j : ℤ)
    (P : ℂ → ℂ) (hj : m < j)
    (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
    (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤) :
    automorphicSections τ (3 * (d - 3 * j)) (γL ^ (d - 3 * j)) ≃ₗ[ℂ]
      coefficientSpace τ γL γP d m j P :=
  LinearEquiv.ofBijective (highCoefficientMap τ γL γP d m j P hj)
    ⟨highCoefficientMap_injective τ γL γP d m j P hj hP hPfin,
      highCoefficientMap_surjective τ γL γP d m j P hj⟩
end Nagata.Workers.W10
end
end
section
noncomputable section
namespace Nagata.Workers.W10
open Nagata.CoefficientSpaces
end Nagata.Workers.W10
end
end
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.CoefficientSpaces Nagata.FiniteExponents Nagata.W08
def sourceBlock (τ γL γP : ℂ) (d m j : ℤ) : Submodule ℂ (ℂ → ℂ) :=
  if j ≤ m then
    automorphicSections τ (3 * (d - 3 * m))
      (γL ^ (d - 3 * m) * normalMinusMarkedMultiplier γL γP ^ (m - j))
  else automorphicSections τ (3 * (d - 3 * j)) (γL ^ (d - 3 * j))
def sourceCoefficientEquiv (τ γL γP : ℂ) (d m j : ℤ) (P : ℂ → ℂ)
    (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
    (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤) :
    sourceBlock τ γL γP d m j ≃ₗ[ℂ] coefficientSpace τ γL γP d m j P := by
  by_cases hj : j ≤ m
  · exact (LinearEquiv.ofEq _ _ (by simp only [sourceBlock, if_pos hj])).trans
      (firstCoefficientEquiv τ γL γP d m j P hj)
  · exact (LinearEquiv.ofEq _ _ (by simp only [sourceBlock, if_neg hj])).trans
      (highCoefficientEquiv τ γL γP d m j P (lt_of_not_ge hj) hP hPfin)
def blockCoordinateMap (τ γL γP : ℂ) (d m j : ℤ) (a Δ : ℝ) (P : ℂ → ℂ)
    (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
    (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤)
    (c : sourceBlock τ γL γP d m j →ₗ[ℂ] (ColumnFiber d m a Δ j → ℂ)) :
    coefficientSpace τ γL γP d m j P →ₗ[ℂ] (ColumnFiber d m a Δ j → ℂ) :=
  c.comp (sourceCoefficientEquiv τ γL γP d m j P hP hPfin).symm.toLinearMap
theorem blockCoordinateMap_injective (τ γL γP : ℂ) (d m j : ℤ) (a Δ : ℝ) (P : ℂ → ℂ)
    (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
    (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤)
    (c : sourceBlock τ γL γP d m j →ₗ[ℂ] (ColumnFiber d m a Δ j → ℂ))
    (hc : Function.Injective c) :
    Function.Injective (blockCoordinateMap τ γL γP d m j a Δ P hP hPfin c) :=
  hc.comp (sourceCoefficientEquiv τ γL γP d m j P hP hPfin).symm.injective
def literalPolynomialBasis (τ γL γP : ℂ) (d m : ℤ) (a Δ : ℝ) (P : ℂ → ℂ)
    (hm : 0 ≤ m) (hd : 3 * m < d)
    (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
    (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤)
    (c : ∀ j : Fin ((d / 3).toNat + 1), sourceBlock τ γL γP d m (j.val : ℤ) →ₗ[ℂ]
      (ColumnFiber d m a Δ (j.val : ℤ) → ℂ))
    (hc : ∀ j, Function.Injective (c j))
    (theta : ∀ j : Fin ((d / 3).toNat + 1), ColumnFiber d m a Δ (j.val : ℤ) →
      sourceBlock τ γL γP d m (j.val : ℤ))
    (htheta : ∀ j K, c j (theta j K) = Pi.single K 1) :
    Basis (Column d m a Δ) ℂ (polynomialSections τ γL γP d m P) := by
  classical
  let I := fun j : Fin ((d / 3).toNat + 1) => ColumnFiber d m a Δ (j.val : ℤ)
  let e := fun j : Fin ((d / 3).toNat + 1) =>
    sourceCoefficientEquiv τ γL γP d m (j.val : ℤ) P hP hPfin
  let cc := fun j => blockCoordinateMap τ γL γP d m (j.val : ℤ) a Δ P hP hPfin (c j)
  have hinj : ∀ j, Function.Injective (cc j) := fun j =>
    blockCoordinateMap_injective τ γL γP d m (j.val : ℤ) a Δ P hP hPfin (c j) (hc j)
  let v := fun j K => e j (theta j K)
  have hv : ∀ j K, cc j (v j K) = Pi.single K 1 := by
    intro j K
    change c j ((e j).symm (e j (theta j K))) = _
    rw [LinearEquiv.symm_apply_apply, htheta]
  exact (polynomialSectionBasisFromCoefficients τ γL γP d m P I cc hinj v hv).reindex
    (columnFiberEquiv d m a Δ hm hd)
end Nagata.Workers.W10
end
end
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.CoefficientSpaces Nagata.FiniteExponents
variable (τ γL γP : ℂ) (d : ℤ) (m : ℕ) (a Δ : ℝ) (P : ℂ → ℂ)
  (hd : 3 * (m : ℤ) < d)
  (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
  (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤)
  (c : ∀ j : Fin ((d / 3).toNat + 1), sourceBlock τ γL γP d (m : ℤ) (j.val : ℤ) →ₗ[ℂ]
    (ColumnFiber d (m : ℤ) a Δ (j.val : ℤ) → ℂ))
  (hc : ∀ j, Function.Injective (c j))
  (theta : ∀ j : Fin ((d / 3).toNat + 1), ColumnFiber d (m : ℤ) a Δ (j.val : ℤ) →
    sourceBlock τ γL γP d (m : ℤ) (j.val : ℤ))
  (htheta : ∀ j K, c j (theta j K) = Pi.single K 1)
theorem literalPolynomialBasis_as_monomial
    (j : Fin ((d / 3).toNat + 1)) (K : ColumnFiber d (m : ℤ) a Δ (j.val : ℤ)) :
    (literalPolynomialBasis τ γL γP d (m : ℤ) a Δ P (Int.natCast_nonneg m) hd hP hPfin
      c hc theta htheta (columnFiberEquiv d (m : ℤ) a Δ (Int.natCast_nonneg m) hd ⟨j, K⟩)).val =
    Polynomial.monomial j.val
      (sourceCoefficientEquiv τ γL γP d (m : ℤ) (j.val : ℤ) P hP hPfin (theta j K)).val := by
  classical
  unfold literalPolynomialBasis
  rw [Basis.reindex_apply, Equiv.symm_apply_apply]
  exact polynomialSectionBasis_as_monomial _ _ _ _ _ _ _ _ _ _ _ _ _
theorem literalPolynomialBasis_localScalar
    (j : Fin ((d / 3).toNat + 1)) (K : ColumnFiber d (m : ℤ) a Δ (j.val : ℤ))
    (z₀ x y : ℂ) :
    Nagata.W20.localScalar
      (literalPolynomialBasis τ γL γP d (m : ℤ) a Δ P (Int.natCast_nonneg m) hd hP hPfin
        c hc theta htheta (columnFiberEquiv d (m : ℤ) a Δ (Int.natCast_nonneg m) hd ⟨j, K⟩))
      z₀ x y =
    (sourceCoefficientEquiv τ γL γP d (m : ℤ) (j.val : ℤ) P hP hPfin (theta j K)).val
      (z₀ * Complex.exp x) * Complex.exp ((j.val : ℂ) * y) := by
  unfold Nagata.W20.localScalar
  rw [literalPolynomialBasis_as_monomial]
  simp [scalarExpression, Polynomial.sum_monomial_index, Complex.exp_nat_mul]
end Nagata.Workers.W10
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W19
open Filter Topology
theorem contraction_invariant_nat_pow {τ : ℂ} (hτ : τ ≠ 0)
    {f : ℂ → ℂ} (hf : ∀ z, z ≠ 0 → f (τ * z) = f z)
    (z : ℂ) (hz : z ≠ 0) (n : ℕ) : f (τ ^ n * z) = f z := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ', mul_assoc, hf _ (mul_ne_zero (pow_ne_zero n hτ) hz), hn]
theorem contraction_invariant_zpow {τ : ℂ} (hτ : τ ≠ 0)
    {f : ℂ → ℂ} (hf : ∀ z, z ≠ 0 → f (τ * z) = f z)
    (z : ℂ) (hz : z ≠ 0) (n : ℤ) : f (τ ^ n * z) = f z := by
  cases n with
  | ofNat n => simpa using contraction_invariant_nat_pow hτ hf z hz n
  | negSucc n =>
    have h := contraction_invariant_nat_pow hτ hf
      (τ ^ (-(n + 1 : ℤ)) * z) (mul_ne_zero (zpow_ne_zero _ hτ) hz) (n + 1)
    have hcancel : τ ^ (n + 1) * (τ ^ (-(n + 1 : ℤ)) * z) = z := by
      rw [zpow_neg, show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by simp,
        zpow_natCast, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hτ), one_mul]
    rw [hcancel] at h
    exact h.symm
theorem bounded_holomorphic_contraction_constant {τ : ℂ}
    (hτ : τ ≠ 0) (hτ1 : ‖τ‖ < 1) (f : ℂ → ℂ)
    (hhol : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z)
    (hperiod : ∀ z, z ≠ 0 → f (τ * z) = f z)
    (hbounded : ∃ B : ℝ, ∀ z, z ≠ 0 → ‖f z‖ ≤ B) :
    ∀ z, z ≠ 0 → f z = f 1 := by
  obtain ⟨B, hB⟩ := hbounded
  have hlim : Tendsto f (𝓝[≠] (0 : ℂ))
      (𝓝 (limUnder (𝓝[≠] (0 : ℂ)) f)) := by
    apply Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under
    · exact Filter.Eventually.mono self_mem_nhdsWithin fun z hz => hhol z hz
    · refine ⟨B + ‖f 0‖, ?_⟩
      change ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖f z - f 0‖ ≤ B + ‖f 0‖
      exact Filter.Eventually.mono self_mem_nhdsWithin fun z hz =>
        norm_sub_le_of_le (hB z hz) le_rfl
  have hvalue : ∀ z, z ≠ 0 → f z = limUnder (𝓝[≠] (0 : ℂ)) f := by
    intro z hz
    have horbit : Tendsto (fun n : ℕ => τ ^ n * z) atTop (𝓝[≠] (0 : ℂ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
      · simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hτ1).mul_const z
      · exact mul_ne_zero (pow_ne_zero n hτ) hz
    have hc : Tendsto (fun _ : ℕ => f z) atTop
        (𝓝 (limUnder (𝓝[≠] (0 : ℂ)) f)) := by
      simpa only [Function.comp_def, contraction_invariant_nat_pow hτ hperiod z hz] using
        hlim.comp horbit
    exact tendsto_nhds_unique tendsto_const_nhds hc
  intro z hz
  exact (hvalue z hz).trans (hvalue 1 one_ne_zero).symm
end Nagata.W19
end
section
noncomputable section
namespace Nagata.W19
open Nagata.W08 Nagata.Workers.W05 Nagata.Workers.W10
theorem periodic_holomorphic_bounded {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (f : ℂ → ℂ) (hhol : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z)
    (hperiod : ∀ z, z ≠ 0 → f ((τ : ℂ) * z) = f z) :
    ∃ B : ℝ, ∀ z, z ≠ 0 → ‖f z‖ ≤ B := by
  have hcont : ContinuousOn (fun z => ‖f z‖) (closedAnnulus τ) := by
    intro z hz
    exact (hhol z (norm_pos_iff.mp (lt_of_lt_of_le hτ hz.1))).continuousAt.norm.continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_closedAnnulus τ).bddAbove_image hcont
  refine ⟨B, ?_⟩
  intro z hz
  obtain ⟨k, hk⟩ := exists_zpow_in_annulus hτ hτ1 z hz
  have hval := contraction_invariant_zpow (Complex.ofReal_ne_zero.mpr (ne_of_gt hτ))
    hperiod z hz k
  rw [← hval]
  exact hB (Set.mem_image_of_mem _ hk)
theorem degree_zero_section_constant {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (f : automorphicSections (τ : ℂ) 0 1) (z : ℂ) (hz : z ≠ 0) :
    f.val z = f.val 1 := by
  have hp : ∀ z, z ≠ 0 → f.val ((τ : ℂ) * z) = f.val z := by
    intro z hz
    simpa using f.property.2.2 z hz
  exact bounded_holomorphic_contraction_constant
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hτ))
    (by simpa only [Complex.norm_of_nonneg hτ.le] using hτ1)
    f.val f.property.2.1 hp (periodic_holomorphic_bounded hτ hτ1 f.val f.property.2.1 hp) z hz
def degreeZeroSectionEquiv {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) :
    automorphicSections (τ : ℂ) 0 1 ≃ₗ[ℂ] ℂ where
  toFun f := f.val 1
  invFun a := normalizedConstantSection (τ : ℂ)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hτ)) a
  left_inv f := by
    apply automorphicSections_ext
    intro z hz
    rw [normalizedConstantSection_apply _ _ _ hz]
    exact (degree_zero_section_constant hτ hτ1 f z hz).symm
  right_inv a := normalizedConstantSection_apply _ _ _ one_ne_zero
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def degreeZeroConstantBasis {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) :
    Module.Basis PUnit ℂ (automorphicSections (τ : ℂ) 0 1) :=
  (Module.Basis.singleton PUnit ℂ).map (degreeZeroSectionEquiv hτ hτ1).symm
@[simp] theorem degreeZeroConstantBasis_apply {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (i : PUnit) : degreeZeroConstantBasis hτ hτ1 i =
      normalizedConstantSection (τ : ℂ) (Complex.ofReal_ne_zero.mpr (ne_of_gt hτ)) 1 := by
  simp [degreeZeroConstantBasis, degreeZeroSectionEquiv]
end Nagata.W19
end
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Nagata.W01
section
abbrev AngularCircle := AddCircle (2 * Real.pi)
def circleParam (r : ℝ) (t : AngularCircle) : ℂ :=
  (r : ℂ) * (AddCircle.toCircle t : ℂ)
theorem circleParam_ne_zero {r : ℝ} (hr : 0 < r) (t : AngularCircle) :
    circleParam r t ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') (AddCircle.toCircle t).coe_ne_zero
theorem continuous_circleParam (r : ℝ) : Continuous (circleParam r) :=
  continuous_const.mul (continuous_subtype_val.comp AddCircle.continuous_toCircle)
theorem circleParam_coe (r θ : ℝ) :
    circleParam r (θ : AngularCircle) = circleMap 0 r θ := by
  simp [circleParam, AddCircle.toCircle_apply_mk, Real.two_pi_pos.ne', Circle.coe_exp, circleMap]
theorem circleParam_arg (z : ℂ) :
    circleParam ‖z‖ (Complex.arg z : AngularCircle) = z := by
  rw [circleParam_coe]
  simp [circleMap]
def circleTrace (r : ℝ) (f : ℂ → ℂ) : AngularCircle → ℂ :=
  fun t => f (circleParam r t)
@[simp] theorem circleTrace_coe (r : ℝ) (f : ℂ → ℂ) (θ : ℝ) :
    circleTrace r f (θ : AngularCircle) = f (circleMap 0 r θ) := by
  rw [circleTrace, circleParam_coe]
theorem continuous_circleTrace {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : ∀ z, z ≠ 0 → ContinuousAt f z) : Continuous (circleTrace r f) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (hf _ (circleParam_ne_zero hr t)).comp (continuous_circleParam r).continuousAt
def circleTraceMap (r : ℝ) (hr : 0 < r) (f : ℂ → ℂ)
    (hf : ∀ z, z ≠ 0 → ContinuousAt f z) : C(AngularCircle, ℂ) :=
  ⟨circleTrace r f, continuous_circleTrace hr hf⟩
theorem punctured_eq_zero_of_circleTrace_zero {f : ℂ → ℂ}
    (h : ∀ r : ℝ, 0 < r → ∀ t : AngularCircle, circleTrace r f t = 0) :
    ∀ z : ℂ, z ≠ 0 → f z = 0 := by
  intro z hz
  have hh := h ‖z‖ (norm_pos_iff.mpr hz) (Complex.arg z : AngularCircle)
  simpa [circleTrace, circleParam_arg] using hh
variable {T : ℝ} [Fact (0 < T)]
theorem continuous_circle_zero_of_fourier_zero (f : C(AddCircle T, ℂ))
    (h : ∀ k : ℤ, fourierCoeff f k = 0) : f = 0 := by
  have hs : Summable (fourierCoeff f) := by
    simpa only [show fourierCoeff f = (fun _ : ℤ => (0 : ℂ)) from funext h]
      using (summable_zero : Summable (fun _ : ℤ => (0 : ℂ)))
  ext x
  have hsum := has_pointwise_sum_fourier_series_of_summable hs x
  simp only [h, zero_smul] at hsum
  exact hsum.unique hasSum_zero
end
open Complex
theorem laurent_tangent_integrand (z w : ℂ) (hz : z ≠ 0) (k : ℤ) :
    (z * I) * (z ^ (-k - 1) * w) = I * z ^ (-k) * w := by
  have hpow : z * z ^ (-k - 1) = z ^ (-k) := by
    conv_lhs => lhs; rw [← zpow_one z]
    rw [← zpow_add₀ hz]
    congr 1
    omega
  calc
    _ = I * (z * z ^ (-k - 1)) * w := by ring
    _ = _ := by rw [hpow]
theorem laurent_radius_factor_ne_zero {r : ℝ} (hr : 0 < r) (k : ℤ) :
    (r : ℂ) ^ (-k) ≠ 0 :=
  zpow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr.ne')
end Nagata.W01
section
open Complex Real
namespace Nagata.W01
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
theorem fourier_eq_circle_zpow (k : ℤ) (t : AngularCircle) :
    fourier k t = (AddCircle.toCircle t : ℂ) ^ k := by
  rw [fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow]
theorem circleMap_zpow_fourier (r θ : ℝ) (k : ℤ) :
    circleMap 0 r θ ^ k = (r : ℂ) ^ k * fourier k (θ : AngularCircle) := by
  rw [← circleParam_coe, circleParam, mul_zpow, fourier_eq_circle_zpow]
theorem laurent_integrand_parameterization {r : ℝ} (hr : 0 < r)
    (f : ℂ → ℂ) (k : ℤ) (θ : ℝ) :
    (circleMap 0 r θ * I) * ((circleMap 0 r θ) ^ (-k - 1) * f (circleMap 0 r θ)) =
      (I * (r : ℂ) ^ (-k)) * (fourier (-k) (θ : AngularCircle) * f (circleMap 0 r θ)) := by
  have hz : circleMap 0 r θ ≠ 0 := by
    simpa [circleParam_coe] using circleParam_ne_zero hr (θ : AngularCircle)
  rw [laurent_tangent_integrand _ _ hz, circleMap_zpow_fourier]
  ring
theorem analyticLaurentCoeff_eq_fourier {r : ℝ} (hr : 0 < r)
    (f : ℂ → ℂ) (k : ℤ) :
    Nagata.W09.analyticLaurentCoeff r f k =
      (r : ℂ) ^ (-k) * fourierCoeff (circleTrace r f) k := by
  unfold Nagata.W09.analyticLaurentCoeff circleIntegral
  simp only [deriv_circleMap, smul_eq_mul]
  have hi : (fun θ : ℝ => (circleMap 0 r θ * I) *
      ((circleMap 0 r θ) ^ (-k - 1) * f (circleMap 0 r θ))) =
      (fun θ : ℝ => (I * (r : ℂ) ^ (-k)) *
        (fourier (-k) (θ : AngularCircle) * f (circleMap 0 r θ))) :=
    funext (laurent_integrand_parameterization hr f k)
  rw [hi, intervalIntegral.integral_const_mul (a := 0) (b := 2 * Real.pi)
    (μ := MeasureTheory.volume) (I * (r : ℂ) ^ (-k))
    (fun θ : ℝ => fourier (-k) (θ : AngularCircle) * f (circleMap 0 r θ))]
  rw [fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [zero_add, smul_eq_mul, circleTrace_coe, Complex.real_smul,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hπ, Complex.I_ne_zero]
theorem circleTrace_zero_of_laurentCoeff_zero {r : ℝ} (hr : 0 < r) (f : ℂ → ℂ)
    (hf : ∀ z, z ≠ 0 → ContinuousAt f z)
    (hc : ∀ k : ℤ, Nagata.W09.analyticLaurentCoeff r f k = 0) :
    ∀ t : AngularCircle, circleTrace r f t = 0 := by
  have hz : circleTraceMap r hr f hf = 0 := by
    apply continuous_circle_zero_of_fourier_zero
    intro k
    have h := hc k
    rw [analyticLaurentCoeff_eq_fourier hr] at h
    exact (mul_eq_zero.mp h).resolve_left (laurent_radius_factor_ne_zero hr k)
  intro t
  exact congrArg (fun g : C(AngularCircle, ℂ) => g t) hz
theorem punctured_zero_of_all_laurentCoeff_zero (f : ℂ → ℂ)
    (hf : ∀ z, z ≠ 0 → ContinuousAt f z)
    (hc : ∀ r : ℝ, 0 < r → ∀ k : ℤ, Nagata.W09.analyticLaurentCoeff r f k = 0) :
    ∀ z : ℂ, z ≠ 0 → f z = 0 := by
  apply punctured_eq_zero_of_circleTrace_zero
  intro r hr
  exact circleTrace_zero_of_laurentCoeff_zero hr f hf (hc r hr)
end Nagata.W01
end
namespace Nagata.W01
theorem punctured_zero_of_radius_one_laurentCoeff_zero (f : ℂ → ℂ)
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z)
    (hc : ∀ k : ℤ, Nagata.W09.analyticLaurentCoeff 1 f k = 0) :
    ∀ z : ℂ, z ≠ 0 → f z = 0 := by
  apply punctured_zero_of_all_laurentCoeff_zero f (fun z hz => (hf z hz).continuousAt)
  intro r hr k
  rw [Nagata.W09.analyticLaurentCoeff_radius_independent hr zero_lt_one hf k]
  exact hc k
theorem laurentCoefficientMap_injective (τ : ℂ) (n : ℤ) (γ : ℂ) :
    Function.Injective (Nagata.W09.laurentCoefficientMap τ n γ) := by
  intro f g hfg
  have hzero : Nagata.W09.laurentCoefficientMap τ n γ (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  have hz := punctured_zero_of_radius_one_laurentCoeff_zero (f - g).val
    (f - g).property.2.1 (fun k => congrFun hzero k)
  apply Nagata.W08.automorphicSections_ext
  intro z hzne
  have h := hz z hzne
  change f.val z - g.val z = 0 at h
  exact sub_eq_zero.mp h
end Nagata.W01
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.W08 Nagata.W09
theorem positiveSectionBasis_exists {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (hC : ∀ (n : ℤ) (γ : ℂ), Function.Injective (laurentCoefficientMap (τ : ℂ) n γ))
    {n : ℤ} (hn : 0 < n) {γ : ℂ} (hγ : γ ≠ 0) :
    Nonempty (Basis (Fin n.toNat) ℂ (automorphicSections (τ : ℂ) n γ)) := by
  obtain ⟨σ, x₀, ε, heps, hgamma, _, hU⟩ :=
    Nagata.W02.exists_normalized_multiplier_frame (show (0 : ℝ) < (n : ℝ) by exact_mod_cast hn) hτ hτone hγ
  have heps0 : ε ≠ 0 := by intro hz; simp [hz] at heps
  let b := centeredThetaSectionBasis n hn σ x₀ heps0 heps hτ hτone (hC _ _) hU
  have hc : Fintype.card (thetaIndices (σ - x₀ * (n : ℝ)) n) = n.toNat := by
    rw [Fintype.card_coe, card_thetaIndices]
  let e : thetaIndices (σ - x₀ * (n : ℝ)) n ≃ Fin n.toNat :=
    (Fintype.equivFin _).trans (finCongr hc)
  let E : automorphicSections (τ : ℂ) n (ε * ((τ ^ σ : ℝ) : ℂ)) ≃ₗ[ℂ]
      automorphicSections (τ : ℂ) n γ := LinearEquiv.ofEq _ _ (by rw [hgamma])
  exact ⟨(b.map E).reindex e⟩
def positiveSectionBasisFin {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (hC : ∀ (n : ℤ) (γ : ℂ), Function.Injective (laurentCoefficientMap (τ : ℂ) n γ))
    {n : ℤ} (hn : 0 < n) {γ : ℂ} (hγ : γ ≠ 0) :
    Basis (Fin n.toNat) ℂ (automorphicSections (τ : ℂ) n γ) :=
  Classical.choice (positiveSectionBasis_exists hτ hτone hC hn hγ)
theorem positiveSection_finrank {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (hC : ∀ (n : ℤ) (γ : ℂ), Function.Injective (laurentCoefficientMap (τ : ℂ) n γ))
    {n : ℤ} (hn : 0 < n) {γ : ℂ} (hγ : γ ≠ 0) :
    Module.finrank ℂ (automorphicSections (τ : ℂ) n γ) = n.toNat := by
  rw [Module.finrank_eq_card_basis (positiveSectionBasisFin hτ hτone hC hn hγ), Fintype.card_fin]
end Nagata.Workers.W10
end
end
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.W07 Nagata.W08 Nagata.W09
def thetaLowerIndexEquiv (U x₀ : ℝ) (n : ℤ) :
    thetaIndices ((U + x₀ * (n : ℝ)) - x₀ * (n : ℝ)) n ≃ thetaIndices U n :=
  Equiv.subtypeEquivRight (fun K => by rw [add_sub_cancel_right])
def thetaSectionBasisAtLower (n : ℤ) (hn : 0 < n) (U x₀ : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) (hunit : ‖ε‖ = 1)
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (hC : Function.Injective (laurentCoefficientMap (τ : ℂ) n
      (ε * ((τ ^ (U + x₀ * (n : ℝ)) : ℝ) : ℂ))))
    (hU : U ∉ Set.range (Int.cast : ℤ → ℝ)) :
    Basis (thetaIndices U n) ℂ
      (automorphicSections (τ : ℂ) n (ε * ((τ ^ (U + x₀ * (n : ℝ)) : ℝ) : ℂ))) :=
  (centeredThetaSectionBasis n hn (U + x₀ * (n : ℝ)) x₀ hε hunit hτ hτone hC
    (by simpa only [add_sub_cancel_right] using hU)).reindex (thetaLowerIndexEquiv U x₀ n)
@[simp] theorem thetaSectionBasisAtLower_apply (n : ℤ) (hn : 0 < n) (U x₀ : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) (hunit : ‖ε‖ = 1)
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (hC : Function.Injective (laurentCoefficientMap (τ : ℂ) n
      (ε * ((τ ^ (U + x₀ * (n : ℝ)) : ℝ) : ℂ))))
    (hU : U ∉ Set.range (Int.cast : ℤ → ℝ)) (K : thetaIndices U n) :
    thetaSectionBasisAtLower n hn U x₀ hε hunit hτ hτone hC hU K =
      normalizedSourceThetaSection n K.val hn (U + x₀ * (n : ℝ)) x₀ hε hτ hτone := by
  simp only [thetaSectionBasisAtLower, Basis.reindex_apply, centeredThetaSectionBasis_apply]
  rfl
theorem thetaSectionBasisAtLower_local (n : ℤ) (hn : 0 < n) (U x₀ : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) (hunit : ‖ε‖ = 1)
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (hC : Function.Injective (laurentCoefficientMap (τ : ℂ) n
      (ε * ((τ ^ (U + x₀ * (n : ℝ)) : ℝ) : ℂ))))
    (hU : U ∉ Set.range (Int.cast : ℤ → ℝ)) (K : thetaIndices U n) (x : ℂ) :
    (thetaSectionBasisAtLower n hn U x₀ hε hunit hτ hτone hC hU K).val
      (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      Nagata.W22.normalizedThetaSeries (n : ℝ) ((K.val : ℝ) - U) (K.val : ℝ) ε τ x := by
  rw [thetaSectionBasisAtLower_apply, normalizedSourceThetaSection_centered]
  have ha : (K.val : ℝ) - (U + x₀ * (n : ℝ)) + x₀ * (n : ℝ) = (K.val : ℝ) - U := by ring
  rw [ha]
  rfl
end Nagata.Workers.W10
end
end
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.W08
end Nagata.Workers.W10
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W10
open Nagata.CoefficientSpaces Nagata.FiniteExponents
abbrev tauPower (τ s : ℝ) : ℂ := ((τ ^ s : ℝ) : ℂ)
theorem tauPower_ne_zero {τ : ℝ} (hτ : 0 < τ) (s : ℝ) : tauPower τ s ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos hτ s))
theorem tauPower_add {τ : ℝ} (hτ : 0 < τ) (s t : ℝ) :
    tauPower τ (s + t) = tauPower τ s * tauPower τ t := by
  simp only [tauPower, Real.rpow_add hτ, Complex.ofReal_mul]
theorem tauPower_zpow {τ : ℝ} (hτ : 0 < τ) (s : ℝ) (k : ℤ) :
    tauPower τ s ^ k = tauPower τ ((k : ℝ) * s) := by
  simp only [tauPower, ← Complex.ofReal_zpow, ← Real.rpow_mul_intCast hτ.le]
  rw [mul_comm]
theorem tauPower_div {τ : ℝ} (hτ : 0 < τ) (s t : ℝ) :
    tauPower τ s / tauPower τ t = tauPower τ (s - t) := by
  simp only [tauPower, Real.rpow_sub hτ, Complex.ofReal_div]
theorem normalMinusMarkedMultiplier_source {τ : ℝ} (hτ : 0 < τ) (s ρ : ℝ) :
    normalMinusMarkedMultiplier (tauPower τ ((s + ρ) / 3)) (-tauPower τ s) =
      -tauPower τ ρ := by
  unfold normalMinusMarkedMultiplier
  have hp : tauPower τ ((s + ρ) / 3) ^ (3 : ℕ) = tauPower τ (s + ρ) := by
    have h := tauPower_zpow hτ ((s + ρ) / 3) (3 : ℤ)
    norm_num at h
    convert h using 1
    congr 1
    ring
  rw [hp, div_neg, tauPower_div hτ]
  congr 2
  ring
theorem firstSourceMultiplier {τ : ℝ} (hτ : 0 < τ) (s ρ : ℝ) (d m j : ℤ) :
    tauPower τ ((s + ρ) / 3) ^ (d - 3 * m) *
      normalMinusMarkedMultiplier (tauPower τ ((s + ρ) / 3)) (-tauPower τ s) ^ (m - j) =
    (-1 : ℂ) ^ (m - j) *
      tauPower τ (((d - 3 * m : ℤ) : ℝ) * ((s + ρ) / 3) + ((m - j : ℤ) : ℝ) * ρ) := by
  rw [normalMinusMarkedMultiplier_source hτ, tauPower_zpow hτ]
  rw [show -tauPower τ ρ = (-1 : ℂ) * tauPower τ ρ by ring, mul_zpow,
    tauPower_zpow hτ, tauPower_add hτ]
  ring
theorem secondSourceMultiplier {τ : ℝ} (hτ : 0 < τ) (s ρ : ℝ) (d j : ℤ) :
    tauPower τ ((s + ρ) / 3) ^ (d - 3 * j) =
      tauPower τ (((d - 3 * j : ℤ) : ℝ) * ((s + ρ) / 3)) :=
  tauPower_zpow hτ _ _
theorem firstSourceEndpoint (s ρ Δ x₀ : ℝ) (d m j : ℤ) (hs : s = 9 * x₀ - Δ) :
    (((d - 3 * m : ℤ) : ℝ) * ((s + ρ) / 3) + ((m - j : ℤ) : ℝ) * ρ) -
      x₀ * (commonDegree d m : ℝ) = firstLower d m j ρ Δ := by
  simpa only [commonDegree, firstLower, Int.cast_mul, Int.cast_sub, Int.cast_ofNat] using
    Nagata.BundleArithmetic.first_interval_parameter (d : ℝ) (m : ℝ) (j : ℝ) s ρ Δ x₀ hs
theorem secondSourceEndpoint (s ρ Δ x₀ : ℝ) (d j : ℤ) (hs : s = 9 * x₀ - Δ) :
    (((d - 3 * j : ℤ) : ℝ) * ((s + ρ) / 3)) -
      x₀ * (sourceDegree d j : ℝ) = secondLower d j ρ Δ := by
  simpa only [sourceDegree, secondLower, Int.cast_mul, Int.cast_sub, Int.cast_ofNat] using
    Nagata.BundleArithmetic.second_interval_parameter (d : ℝ) (j : ℝ) s ρ Δ x₀ hs
end Nagata.Workers.W10
end
end
section
namespace Nagata.Workers.W10
theorem interpolate_distributed_rows (q m s : ℕ) (K : Fin s → ℂ)
    (xs : Fin s → Finset ℂ) (hK : Function.Injective K)
    (hpos : ∀ i, 1 ≤ (xs i).card) (hsize : ∀ i, (xs i).card ≤ m)
    (hdistribution : ∀ t, 1 ≤ t → t ≤ m →
      (Finset.univ.filter fun i => t ≤ (xs i).card).card ≤ q * (m - t + 1))
    (v : Nagata.W01.Plane → ℂ) :
    ∃ f ∈ Nagata.W01.monomialSpace q m,
      ∀ i, ∀ x ∈ xs i, f (x, K i) = v (x, K i) := by
  obtain ⟨σ, _, hσ⟩ := exists_ordered_rows (fun i => (xs i).card) q m
    hpos hsize hdistribution
  obtain ⟨f, hf, hv⟩ := Nagata.W01.interpolate_fin_rows q m s (K ∘ σ) (xs ∘ σ)
    (hK.comp σ.injective) (fun i => hsize (σ i)) hσ v
  refine ⟨f, hf, ?_⟩
  intro i x hx
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
    hv (σ.symm i) x (by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hx)
theorem interpolate_distributed_rows_polynomial (q m s : ℕ) (K : Fin s → ℂ)
    (xs : Fin s → Finset ℂ) (hK : Function.Injective K)
    (hpos : ∀ i, 1 ≤ (xs i).card) (hsize : ∀ i, (xs i).card ≤ m)
    (hdistribution : ∀ t, 1 ≤ t → t ≤ m →
      (Finset.univ.filter fun i => t ≤ (xs i).card).card ≤ q * (m - t + 1))
    (v : Nagata.W01.Plane → ℂ) :
    ∃ p ∈ Nagata.W01.polynomialSpace q m,
      ∀ i, ∀ x ∈ xs i, Nagata.W01.planeEval p (x, K i) = v (x, K i) := by
  obtain ⟨f, hf, hv⟩ := interpolate_distributed_rows q m s K xs hK hpos hsize hdistribution v
  obtain ⟨p, hp, hpf⟩ := Nagata.W01.exists_polynomialSpace_of_mem hf
  exact ⟨p, hp, by simpa [hpf] using hv⟩
end Nagata.Workers.W10
end
section
noncomputable section
namespace Nagata.Workers.W10
open Nagata.CoefficientSpaces
theorem sourceCoefficientEquiv_apply (τ γL γP : ℂ) (d m j : ℤ) (P : ℂ → ℂ)
    (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
    (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤)
    (f : sourceBlock τ γL γP d m j) (z : ℂ) :
    (sourceCoefficientEquiv τ γL γP d m j P hP hPfin f).val z =
      if j ≤ m then f.val z else P z ^ (j - m).toNat * f.val z := by
  unfold sourceCoefficientEquiv
  split_ifs <;> rfl
end Nagata.Workers.W10
end
end
section
noncomputable section
namespace Nagata.Workers.W10
open Nagata.CoefficientSpaces Nagata.FiniteExponents Nagata.W08
def firstSourceThetaEquiv {τ : ℝ} (hτ : 0 < τ) (s ρ Δ x₀ : ℝ)
    (d m j : ℤ) (hs : s = 9 * x₀ - Δ) (hj : j ≤ m) :
    sourceBlock (τ : ℂ) (tauPower τ ((s + ρ) / 3)) (-tauPower τ s) d m j ≃ₗ[ℂ]
    automorphicSections (τ : ℂ) (commonDegree d m)
      ((-1 : ℂ) ^ (m - j) * tauPower τ (firstLower d m j ρ Δ + x₀ * (commonDegree d m : ℝ))) :=
  LinearEquiv.ofEq _ _ (by
    simp only [sourceBlock, if_pos hj]
    rw [firstSourceMultiplier hτ]
    have he : (((d - 3 * m : ℤ) : ℝ) * ((s + ρ) / 3) + ((m - j : ℤ) : ℝ) * ρ) =
        firstLower d m j ρ Δ + x₀ * (commonDegree d m : ℝ) := by
      have h := firstSourceEndpoint s ρ Δ x₀ d m j hs
      linarith
    rw [he]
    rfl)
def secondSourceThetaEquiv {τ : ℝ} (hτ : 0 < τ) (s ρ Δ x₀ : ℝ)
    (d m j : ℤ) (hs : s = 9 * x₀ - Δ) (hj : m < j) :
    sourceBlock (τ : ℂ) (tauPower τ ((s + ρ) / 3)) (-tauPower τ s) d m j ≃ₗ[ℂ]
    automorphicSections (τ : ℂ) (sourceDegree d j)
      ((1 : ℂ) * tauPower τ (secondLower d j ρ Δ + x₀ * (sourceDegree d j : ℝ))) :=
  LinearEquiv.ofEq _ _ (by
    simp only [sourceBlock, if_neg (not_le.mpr hj), one_mul]
    rw [secondSourceMultiplier hτ]
    congr 1
    congr 1
    have he := secondSourceEndpoint s ρ Δ x₀ d j hs
    linarith)
def zeroSourceThetaEquiv (τ s ρ : ℝ) (d m j : ℤ) (hj : m < j) (hz : d - 3 * j = 0) :
    sourceBlock (τ : ℂ) (tauPower τ ((s + ρ) / 3)) (-tauPower τ s) d m j ≃ₗ[ℂ]
      automorphicSections (τ : ℂ) 0 1 :=
  LinearEquiv.ofEq _ _ (by
    simp only [sourceBlock, if_neg (not_le.mpr hj), hz, mul_zero, zpow_zero])
end Nagata.Workers.W10
end
end
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.CoefficientSpaces Nagata.FiniteExponents
variable (τ γL γP : ℂ) (d : ℤ) (m : ℕ) (a Δ : ℝ) (P : ℂ → ℂ)
  (hd : 3 * (m : ℤ) < d)
  (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
  (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤)
  (b : ∀ j : Fin ((d / 3).toNat + 1),
    Basis (ColumnFiber d (m : ℤ) a Δ (j.val : ℤ)) ℂ
      (sourceBlock τ γL γP d (m : ℤ) (j.val : ℤ)))
def polynomialBasisFromSourceBases :
    Basis (Column d (m : ℤ) a Δ) ℂ (polynomialSections τ γL γP d (m : ℤ) P) :=
  literalPolynomialBasis τ γL γP d (m : ℤ) a Δ P (Int.natCast_nonneg m) hd hP hPfin
    (fun j => (b j).equivFun.toLinearMap) (fun j => (b j).equivFun.injective) (fun j K => b j K)
    (fun j K => by ext L; simp [Basis.equivFun_self, Pi.single_apply, eq_comm])
theorem polynomialBasisFromSourceBases_local
    (j : Fin ((d / 3).toNat + 1)) (K : ColumnFiber d (m : ℤ) a Δ (j.val : ℤ))
    (z₀ x y : ℂ) :
    Nagata.W20.localScalar
      (polynomialBasisFromSourceBases τ γL γP d m a Δ P hd hP hPfin b
        (columnFiberEquiv d (m : ℤ) a Δ (Int.natCast_nonneg m) hd ⟨j, K⟩)) z₀ x y =
      (if (j.val : ℤ) ≤ (m : ℤ) then (b j K).val (z₀ * Complex.exp x)
        else P (z₀ * Complex.exp x) ^ ((j.val : ℤ) - (m : ℤ)).toNat *
          (b j K).val (z₀ * Complex.exp x)) * Complex.exp ((j.val : ℂ) * y) := by
  unfold polynomialBasisFromSourceBases
  rw [literalPolynomialBasis_localScalar, sourceCoefficientEquiv_apply]
end Nagata.Workers.W10
end
end
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.FiniteExponents
def zeroSourceBlockBasis {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (s ρ Δ : ℝ) (d m j : ℤ) (hj : m < j) (hz : d - 3 * j = 0) :
    Basis (ColumnFiber d m ρ Δ j) ℂ
      (sourceBlock (τ : ℂ) (tauPower τ ((s + ρ) / 3)) (-tauPower τ s) d m j) :=
  ((Nagata.W19.degreeZeroConstantBasis.{0} hτ hτone).map
    (zeroSourceThetaEquiv τ s ρ d m j hj hz).symm).reindex
    (zeroColumnFiberEquiv.{1} d m j ρ Δ hj hz).symm
@[simp] theorem zeroSourceBlockBasis_apply {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (s ρ Δ : ℝ) (d m j : ℤ) (hj : m < j) (hz : d - 3 * j = 0)
    (K : ColumnFiber d m ρ Δ j) (z : ℂ) (hz0 : z ≠ 0) :
    (zeroSourceBlockBasis hτ hτone s ρ Δ d m j hj hz K).val z = 1 := by
  simp only [zeroSourceBlockBasis, Basis.reindex_apply, Basis.map_apply, Equiv.symm_symm]
  change (Nagata.W19.degreeZeroConstantBasis.{0} hτ hτone
    (zeroColumnFiberEquiv.{1} d m j ρ Δ hj hz K)).val z = 1
  rw [Nagata.W19.degreeZeroConstantBasis_apply]
  exact normalizedConstantSection_apply _ _ _ hz0
end Nagata.Workers.W10
end
end
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.FiniteExponents Nagata.W08 Nagata.W09
variable {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
  (hC : ∀ (n : ℤ) (γ : ℂ), Function.Injective (laurentCoefficientMap (τ : ℂ) n γ))
  (s ρ Δ x₀ : ℝ) (d m j : ℤ) (hs : s = 9 * x₀ - Δ)
def firstSourceBlockBasis (hd : 3 * m < d) (hj0 : 0 ≤ j) (hj : j ≤ m)
    (hU : firstLower d m j ρ Δ ∉ Set.range (Int.cast : ℤ → ℝ)) :
    Basis (ColumnFiber d m ρ Δ j) ℂ
      (sourceBlock (τ : ℂ) (tauPower τ ((s + ρ) / 3)) (-tauPower τ s) d m j) :=
  ((thetaSectionBasisAtLower (commonDegree d m) (by unfold commonDegree; omega)
    (firstLower d m j ρ Δ) x₀ (zpow_ne_zero _ (by norm_num)) (by simp) hτ hτone
    (hC _ _) hU).map (firstSourceThetaEquiv hτ s ρ Δ x₀ d m j hs hj).symm).reindex
    (firstColumnFiberEquiv d m j ρ Δ hj0 hj hU).symm
def positiveSourceBlockBasis (hj : m < j) (hjd : j ≤ d / 3) (hn : 0 < d - 3 * j)
    (hU : secondLower d j ρ Δ ∉ Set.range (Int.cast : ℤ → ℝ)) :
    Basis (ColumnFiber d m ρ Δ j) ℂ
      (sourceBlock (τ : ℂ) (tauPower τ ((s + ρ) / 3)) (-tauPower τ s) d m j) :=
  ((thetaSectionBasisAtLower (sourceDegree d j) (by unfold sourceDegree; omega)
    (secondLower d j ρ Δ) x₀ one_ne_zero (by simp) hτ hτone
    (hC _ _) hU).map (secondSourceThetaEquiv hτ s ρ Δ x₀ d m j hs hj).symm).reindex
    (positiveColumnFiberEquiv d m j ρ Δ hj hjd hn hU).symm
theorem firstSourceBlockBasis_local (hd : 3 * m < d) (hj0 : 0 ≤ j) (hj : j ≤ m)
    (hU : firstLower d m j ρ Δ ∉ Set.range (Int.cast : ℤ → ℝ))
    (K : ColumnFiber d m ρ Δ j) (x : ℂ) :
    (firstSourceBlockBasis hτ hτone hC s ρ Δ x₀ d m j hs hd hj0 hj hU K).val
      (tauPower τ x₀ * Complex.exp x) =
      Nagata.W22.normalizedThetaSeries (commonDegree d m : ℝ)
        ((K.val : ℝ) - firstLower d m j ρ Δ) (K.val : ℝ) ((-1 : ℂ) ^ (m - j)) τ x := by
  rw [firstSourceBlockBasis, Basis.reindex_apply, Basis.map_apply]
  simp only [Equiv.symm_symm, firstSourceThetaEquiv, LinearEquiv.ofEq_symm,
    LinearEquiv.coe_ofEq_apply]
  exact thetaSectionBasisAtLower_local _ _ _ _ _ _ _ _ _ _ _ x
theorem positiveSourceBlockBasis_local (hj : m < j) (hjd : j ≤ d / 3) (hn : 0 < d - 3 * j)
    (hU : secondLower d j ρ Δ ∉ Set.range (Int.cast : ℤ → ℝ))
    (K : ColumnFiber d m ρ Δ j) (x : ℂ) :
    (positiveSourceBlockBasis hτ hτone hC s ρ Δ x₀ d m j hs hj hjd hn hU K).val
      (tauPower τ x₀ * Complex.exp x) =
      Nagata.W22.normalizedThetaSeries (sourceDegree d j : ℝ)
        ((K.val : ℝ) - secondLower d j ρ Δ) (K.val : ℝ) 1 τ x := by
  rw [positiveSourceBlockBasis, Basis.reindex_apply, Basis.map_apply]
  simp only [Equiv.symm_symm, secondSourceThetaEquiv, LinearEquiv.ofEq_symm,
    LinearEquiv.coe_ofEq_apply]
  exact thetaSectionBasisAtLower_local _ _ _ _ _ _ _ _ _ _ _ x
end Nagata.Workers.W10
end
end
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.FiniteExponents Nagata.W09
variable {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
  (hC : ∀ (n : ℤ) (γ : ℂ), Function.Injective (laurentCoefficientMap (τ : ℂ) n γ))
  (s ρ Δ x₀ : ℝ) (d : ℤ) (m : ℕ) (hs : s = 9 * x₀ - Δ)
  (hd : 3 * (m : ℤ) < d)
  (hUfirst : ∀ j : ℤ, 0 ≤ j → j ≤ (m : ℤ) →
    firstLower d (m : ℤ) j ρ Δ ∉ Set.range (Int.cast : ℤ → ℝ))
  (hUsecond : ∀ j : ℤ, (m : ℤ) < j → j ≤ d / 3 → 0 < d - 3 * j →
    secondLower d j ρ Δ ∉ Set.range (Int.cast : ℤ → ℝ))
def allSourceBlockBases (j : Fin ((d / 3).toNat + 1)) :
    Basis (ColumnFiber d (m : ℤ) ρ Δ (j.val : ℤ)) ℂ
      (sourceBlock (τ : ℂ) (tauPower τ ((s + ρ) / 3)) (-tauPower τ s) d (m : ℤ) (j.val : ℤ)) := by
  have hj0 : 0 ≤ (j.val : ℤ) := Int.natCast_nonneg _
  have hjd : (j.val : ℤ) ≤ d / 3 := by omega
  by_cases hj : (j.val : ℤ) ≤ (m : ℤ)
  · exact firstSourceBlockBasis hτ hτone hC s ρ Δ x₀ d (m : ℤ) (j.val : ℤ) hs hd hj0 hj
      (hUfirst _ hj0 hj)
  · have hmj : (m : ℤ) < (j.val : ℤ) := lt_of_not_ge hj
    by_cases hn : 0 < d - 3 * (j.val : ℤ)
    · exact positiveSourceBlockBasis hτ hτone hC s ρ Δ x₀ d (m : ℤ) (j.val : ℤ) hs hmj hjd hn
        (hUsecond _ hmj hjd hn)
    · exact zeroSourceBlockBasis hτ hτone s ρ Δ d (m : ℤ) (j.val : ℤ) hmj (by omega)
theorem allSourceBlockBases_local (j : Fin ((d / 3).toNat + 1))
    (K : ColumnFiber d (m : ℤ) ρ Δ (j.val : ℤ)) (x : ℂ) :
    (allSourceBlockBases hτ hτone hC s ρ Δ x₀ d m hs hd hUfirst hUsecond j K).val
      (tauPower τ x₀ * Complex.exp x) =
      if (j.val : ℤ) ≤ (m : ℤ) then
        Nagata.W22.normalizedThetaSeries (commonDegree d (m : ℤ) : ℝ)
          ((K.val : ℝ) - firstLower d (m : ℤ) (j.val : ℤ) ρ Δ) (K.val : ℝ)
          ((-1 : ℂ) ^ ((m : ℤ) - (j.val : ℤ))) τ x
      else if 0 < d - 3 * (j.val : ℤ) then
        Nagata.W22.normalizedThetaSeries (sourceDegree d (j.val : ℤ) : ℝ)
          ((K.val : ℝ) - secondLower d (j.val : ℤ) ρ Δ) (K.val : ℝ) 1 τ x
      else 1 := by
  unfold allSourceBlockBases
  split_ifs with hj hn
  · exact firstSourceBlockBasis_local _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K x
  · exact positiveSourceBlockBasis_local _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K x
  · exact zeroSourceBlockBasis_apply _ _ _ _ _ _ _ _ _ _ K _
      (mul_ne_zero (tauPower_ne_zero hτ x₀) (Complex.exp_ne_zero x))
end Nagata.Workers.W10
end
end
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.FiniteExponents
variable {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
  (s ρ Δ x₀ : ℝ) (d : ℤ) (m : ℕ) (hs : s = 9 * x₀ - Δ)
  (hd : 3 * (m : ℤ) < d)
  (hUfirst : ∀ j : ℤ, 0 ≤ j → j ≤ (m : ℤ) →
    firstLower d (m : ℤ) j ρ Δ ∉ Set.range (Int.cast : ℤ → ℝ))
  (hUsecond : ∀ j : ℤ, (m : ℤ) < j → j ≤ d / 3 → 0 < d - 3 * j →
    secondLower d j ρ Δ ∉ Set.range (Int.cast : ℤ → ℝ))
def actualSourceBlockBases (j : Fin ((d / 3).toNat + 1)) :
    Basis (ColumnFiber d (m : ℤ) ρ Δ (j.val : ℤ)) ℂ
      (sourceBlock (τ : ℂ) (tauPower τ ((s + ρ) / 3)) (-tauPower τ s) d (m : ℤ) (j.val : ℤ)) :=
  allSourceBlockBases hτ hτone (Nagata.W01.laurentCoefficientMap_injective (τ : ℂ))
    s ρ Δ x₀ d m hs hd hUfirst hUsecond j
theorem actualSourceBlockBases_local (j : Fin ((d / 3).toNat + 1))
    (K : ColumnFiber d (m : ℤ) ρ Δ (j.val : ℤ)) (x : ℂ) :
    (actualSourceBlockBases hτ hτone s ρ Δ x₀ d m hs hd hUfirst hUsecond j K).val
      (tauPower τ x₀ * Complex.exp x) =
      if (j.val : ℤ) ≤ (m : ℤ) then
        Nagata.W22.normalizedThetaSeries (commonDegree d (m : ℤ) : ℝ)
          ((K.val : ℝ) - firstLower d (m : ℤ) (j.val : ℤ) ρ Δ) (K.val : ℝ)
          ((-1 : ℂ) ^ ((m : ℤ) - (j.val : ℤ))) τ x
      else if 0 < d - 3 * (j.val : ℤ) then
        Nagata.W22.normalizedThetaSeries (sourceDegree d (j.val : ℤ) : ℝ)
          ((K.val : ℝ) - secondLower d (j.val : ℤ) ρ Δ) (K.val : ℝ) 1 τ x
      else 1 :=
  allSourceBlockBases_local hτ hτone (Nagata.W01.laurentCoefficientMap_injective (τ : ℂ))
    s ρ Δ x₀ d m hs hd hUfirst hUsecond j K x
end Nagata.Workers.W10
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.Workers.W14
end Nagata.Workers.W14
end
section
noncomputable section
namespace Nagata.Workers.W14
end Nagata.Workers.W14
end
end
section
noncomputable section
namespace Nagata.Workers.W14
open scoped BigOperators
 theorem homogeneous_one_eq_sum {K : Type*} [Field K]
    (L : MvPolynomial (Fin 3) K) (hL : L.IsHomogeneous 1) :
    L = ∑ i : Fin 3, MvPolynomial.monomial (Finsupp.single i 1)
      (L.coeff (Finsupp.single i 1)) := by
  classical
  ext e
  by_cases he : e.degree = 1
  · have hr : e ∈ Set.range (fun i : Fin 3 => Finsupp.single i (1 : ℕ)) := by
      rw [Finsupp.range_single_one]
      exact he
    obtain ⟨i,rfl⟩ := hr
    rw [MvPolynomial.coeff_sum]
    simp [MvPolynomial.coeff_monomial, Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]
  · have hcoeff : L.coeff e = 0 := by
      by_contra hc
      exact he (by simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hL hc)
    rw [hcoeff, MvPolynomial.coeff_sum]
    symm
    apply Finset.sum_eq_zero
    intro i _
    have hne : Finsupp.single i 1 ≠ e := by
      intro hi
      apply he
      rw [← hi]
      simp
    simp [MvPolynomial.coeff_monomial, hne]
 def homogeneousLinearMap {K : Type*} [Field K] (L : MvPolynomial (Fin 3) K) :
    (Fin 3 → K) →ₗ[K] K :=
  ∑ i : Fin 3, L.coeff (Finsupp.single i 1) • LinearMap.proj i
 theorem homogeneousLinearMap_apply {K : Type*} [Field K]
    (L : MvPolynomial (Fin 3) K) (hL : L.IsHomogeneous 1) (v : Fin 3 → K) :
    homogeneousLinearMap L v = MvPolynomial.eval v L := by
  conv_rhs => rw [homogeneous_one_eq_sum L hL]
  simp [homogeneousLinearMap, MvPolynomial.eval_monomial]
 theorem homogeneousLinearMap_ne_zero (L : MvPolynomial (Fin 3) ℂ)
    (hL : L.IsHomogeneous 1) (hne : L ≠ 0) : homogeneousLinearMap L ≠ 0 := by
  intro hz
  apply hne
  apply hL.eq_zero_of_forall_eval_eq_zero
  intro v
  rw [← homogeneousLinearMap_apply L hL, hz]
  rfl
end Nagata.Workers.W14
end
end
section
noncomputable section
namespace Nagata.Workers.W14
end Nagata.Workers.W14
end
end
section
noncomputable section
namespace Nagata.Workers.W14
 def coordinateLineRestriction : MvPolynomial (Fin 3) ℂ →+* MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C ![MvPolynomial.X 0,MvPolynomial.X 1,0]
 theorem coordinateLineRestriction_eval (Q : MvPolynomial (Fin 3) ℂ) (v : Fin 2 → ℂ) :
    MvPolynomial.eval v (coordinateLineRestriction Q) =
      MvPolynomial.eval ![v 0,v 1,0] Q := by
  have h : (MvPolynomial.eval v).comp coordinateLineRestriction =
      MvPolynomial.eval ![v 0,v 1,0] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [coordinateLineRestriction]
    · intro i
      fin_cases i <;> simp [coordinateLineRestriction]
  exact RingHom.congr_fun h Q
 theorem coordinateLineRestriction_homogeneous {Q : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hQ : Q.IsHomogeneous d) : (coordinateLineRestriction Q).IsHomogeneous d := by
  have hcoords : ∀ i : Fin 3,
      (![MvPolynomial.X 0,MvPolynomial.X 1,0] i : MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 := by
    intro i
    fin_cases i
    · exact MvPolynomial.isHomogeneous_X ℂ 0
    · exact MvPolynomial.isHomogeneous_X ℂ 1
    · exact MvPolynomial.isHomogeneous_zero (Fin 2) ℂ 1
  simpa only [coordinateLineRestriction, MvPolynomial.coe_eval₂Hom, one_mul] using hQ.eval₂ MvPolynomial.C
    ![MvPolynomial.X 0,MvPolynomial.X 1,0]
    (fun c => MvPolynomial.isHomogeneous_C (Fin 2) c) hcoords
 def polynomialInLastCoordinate : MvPolynomial (Fin 3) ℂ ≃ₐ[ℂ]
    Polynomial (MvPolynomial (Fin 2) ℂ) :=
  (MvPolynomial.renameEquiv ℂ (Equiv.swap (0 : Fin 3) 2)).trans
    (MvPolynomial.finSuccEquiv ℂ 2)
 theorem polynomialInLastCoordinate_X : polynomialInLastCoordinate (MvPolynomial.X 2) =
    Polynomial.X := by
  simp [polynomialInLastCoordinate, MvPolynomial.renameEquiv_apply,
    MvPolynomial.finSuccEquiv_apply]
 theorem polynomialInLastCoordinate_eval_zero (Q : MvPolynomial (Fin 3) ℂ) :
    (polynomialInLastCoordinate Q).eval 0 =
      MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) (coordinateLineRestriction Q) := by
  have h : (Polynomial.evalRingHom (0 : MvPolynomial (Fin 2) ℂ)).comp
      polynomialInLastCoordinate.toRingHom =
      (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)).toRingHom.comp coordinateLineRestriction := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [polynomialInLastCoordinate, coordinateLineRestriction,
        MvPolynomial.renameEquiv_apply, MvPolynomial.finSuccEquiv_apply]
    · intro i
      fin_cases i <;> simp [polynomialInLastCoordinate, coordinateLineRestriction,
        MvPolynomial.renameEquiv_apply, MvPolynomial.finSuccEquiv_apply, Equiv.swap_apply_def]
      all_goals
        change Polynomial.eval 0 (Polynomial.C _) = _
        simp
  exact RingHom.congr_fun h Q
 theorem coordinateLine_dvd_of_restriction_zero (Q : MvPolynomial (Fin 3) ℂ)
    (hQ : coordinateLineRestriction Q = 0) : MvPolynomial.X 2 ∣ Q := by
  rw [← map_dvd_iff polynomialInLastCoordinate, polynomialInLastCoordinate_X]
  apply Polynomial.X_dvd_iff.mpr
  rw [Polynomial.coeff_zero_eq_eval_zero,polynomialInLastCoordinate_eval_zero,hQ]
  simp
end Nagata.Workers.W14
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W29
def rowPositions (S : Finset (ℤ × ℤ)) (K : ℤ) : Finset ℤ :=
  (S.image Prod.fst).filter fun j => (j, K) ∈ S
def rowHeights (S : Finset (ℤ × ℤ)) : Finset ℤ := S.image Prod.snd
def largeRows (S : Finset (ℤ × ℤ)) (t : ℕ) : Finset ℤ :=
  (rowHeights S).filter fun K => t ≤ (rowPositions S K).card
@[simp] theorem mem_rowPositions (S : Finset (ℤ × ℤ)) (j K : ℤ) :
    j ∈ rowPositions S K ↔ (j, K) ∈ S := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(j, K), h, rfl⟩, h⟩
theorem rowPositions_eq_empty_of_not_mem (S : Finset (ℤ × ℤ)) (K : ℤ)
    (hK : K ∉ rowHeights S) : rowPositions S K = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  apply hK
  exact Finset.mem_image.mpr ⟨(j, K), (mem_rowPositions S j K).mp hj, rfl⟩
@[simp] theorem mem_largeRows (S : Finset (ℤ × ℤ)) (t : ℕ) (ht : 1 ≤ t)
    (K : ℤ) : K ∈ largeRows S t ↔ t ≤ (rowPositions S K).card := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    have hn : (rowPositions S K).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨j, hj⟩ := hn
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_image.mpr
      ⟨(j, K), (mem_rowPositions S j K).mp hj, rfl⟩, h⟩
theorem row_card_le (S : Finset (ℤ × ℤ)) (m : ℕ) (lam : ℝ)
    (hm : 0 < m) (hlam : lam < 1) (lo hi : ℤ → ℝ)
    (hinterval : ∀ K ∈ rowHeights S, lo K ≤ hi K)
    (hcontain : ∀ K, ∀ j ∈ rowPositions S K,
      lo K ≤ (j : ℝ) ∧ (j : ℝ) ≤ hi K)
    (hwidth : ∀ K ∈ rowHeights S, hi K - lo K ≤ (m : ℝ) * lam)
    (K : ℤ) : (rowPositions S K).card ≤ m := by
  by_cases hK : K ∈ rowHeights S
  · apply Nagata.W02.card_le_of_interval_length_lt (rowPositions S K)
      (lo K) (hi K) m (hinterval K hK) (hcontain K)
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    nlinarith [hwidth K hK, mul_lt_mul_of_pos_left hlam hmR]
  · rw [rowPositions_eq_empty_of_not_mem S K hK]
    simp
theorem largeRows_card_le (S : Finset (ℤ × ℤ)) (q m : ℕ)
    (lam U A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAB : A + B = (q : ℝ))
    (hmargin : 1 ≤ (q : ℝ) * (1 - lam) * m)
    (lo hi : ℤ → ℝ)
    (hinterval : ∀ K ∈ rowHeights S, lo K ≤ hi K)
    (hcontain : ∀ K, ∀ j ∈ rowPositions S K,
      lo K ≤ (j : ℝ) ∧ (j : ℝ) ≤ hi K)
    (hwidth : ∀ K ∈ rowHeights S, hi K - lo K ≤ (m : ℝ) * lam)
    (hprofile : ∀ s : ℝ, 0 ≤ s → s ≤ (m : ℝ) * lam →
      ∀ K ∈ rowHeights S, s ≤ hi K - lo K →
        U - A * ((m : ℝ) * lam - s) ≤ (K : ℝ) ∧
        (K : ℝ) ≤ U + B * ((m : ℝ) * lam - s))
    (t : ℕ) (ht : 1 ≤ t) (htm : t ≤ m) :
    (largeRows S t).card ≤ q * (m - t + 1) := by
  have hforce : ∀ K ∈ largeRows S t, (t : ℝ) - 1 ≤ hi K - lo K := by
    intro K hK
    obtain ⟨hKr, hKt⟩ := Finset.mem_filter.mp hK
    exact Nagata.W02.sub_one_le_interval_length (rowPositions S K)
      (lo K) (hi K) t (hinterval K hKr) (hcontain K) hKt
  by_cases hfit : (t : ℝ) - 1 ≤ (m : ℝ) * lam
  · have hnonneg : 0 ≤ (m : ℝ) * lam - ((t : ℝ) - 1) := by linarith
    have hintervalH : U - A * ((m : ℝ) * lam - ((t : ℝ) - 1)) ≤
        U + B * ((m : ℝ) * lam - ((t : ℝ) - 1)) := by
      nlinarith [mul_nonneg hA hnonneg, mul_nonneg hB hnonneg]
    have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hcount := Nagata.W02.card_le_interval_length_add_one (largeRows S t)
      (U - A * ((m : ℝ) * lam - ((t : ℝ) - 1)))
      (U + B * ((m : ℝ) * lam - ((t : ℝ) - 1))) hintervalH
      (by
        intro K hK
        exact hprofile ((t : ℝ) - 1) (by linarith) hfit K
          (Finset.mem_filter.mp hK).1 (hforce K hK))
    have hlength :
        (U + B * ((m : ℝ) * lam - ((t : ℝ) - 1))) -
        (U - A * ((m : ℝ) * lam - ((t : ℝ) - 1))) =
        (q : ℝ) * ((m : ℝ) * lam - (t : ℝ) + 1) := by
      rw [← hAB]
      ring
    rw [hlength] at hcount
    have hcast : ((q * (m - t + 1) : ℕ) : ℝ) =
        (q : ℝ) * ((m : ℝ) - (t : ℝ) + 1) := by
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_sub htm, Nat.cast_one]
    have hfinal : ((largeRows S t).card : ℝ) ≤ ((q * (m - t + 1) : ℕ) : ℝ) := by
      rw [hcast]
      nlinarith
    exact_mod_cast hfinal
  · have hempty : largeRows S t = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro K hK
      have hw := hwidth K (Finset.mem_filter.mp hK).1
      have hf := hforce K hK
      exact hfit (hf.trans hw)
    rw [hempty]
    simp
end Nagata.W29
end
section
namespace Nagata.W29
theorem integer_rows_of_polygon (S : Finset (ℤ × ℤ)) (q m : ℕ)
    (a lam U : ℝ) (ha : 0 < a) (hm : 0 < m)
    (hlam : 0 < lam) (hlam1 : lam < 1)
    (hcoef : 2 * a + a ^ 2 / 9 = (q : ℝ))
    (hmargin : 1 ≤ (q : ℝ) * (1 - lam) * m)
    (hpolygon : ∀ p ∈ S,
      Nagata.W04.InPolygon a ((m : ℝ) * lam) (p.1 : ℝ) ((p.2 : ℝ) - U)) :
    (∀ K : ℤ, (rowPositions S K).card ≤ m) ∧
    (∀ t : ℕ, 1 ≤ t → t ≤ m → (largeRows S t).card ≤ q * (m - t + 1)) := by
  let scale : ℝ := (m : ℝ) * lam
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hscale : 0 < scale := mul_pos hmR hlam
  let lo : ℤ → ℝ := fun K =>
    scale * Nagata.W04.SliceLower a (((K : ℝ) - U) / scale)
  let hi : ℤ → ℝ := fun K =>
    scale * Nagata.W04.SliceUpper a (((K : ℝ) - U) / scale)
  have hcontain : ∀ K, ∀ j ∈ rowPositions S K,
      lo K ≤ (j : ℝ) ∧ (j : ℝ) ≤ hi K := by
    intro K j hj
    exact (Nagata.W04.scaled_slice_interval a scale U j K ha hscale).mp
      (hpolygon (j, K) ((mem_rowPositions S j K).mp hj))
  have hinterval : ∀ K ∈ rowHeights S, lo K ≤ hi K := by
    intro K hK
    obtain ⟨⟨j, k⟩, hp, hpK⟩ := Finset.mem_image.mp hK
    change k = K at hpK
    subst k
    have hr : j ∈ rowPositions S K := (mem_rowPositions S j K).mpr hp
    exact (hcontain K j hr).1.trans (hcontain K j hr).2
  have hwidth_id (K : ℤ) : hi K - lo K =
      Nagata.W04.ScaledSliceWidth a scale U K :=
    Nagata.W04.scaled_slice_width a scale U K ha
  have hwidth : ∀ K ∈ rowHeights S, hi K - lo K ≤ (m : ℝ) * lam := by
    intro K _
    rw [hwidth_id]
    exact Nagata.W04.scaled_width_le_scale a scale U K ha (le_of_lt hscale)
  constructor
  · exact row_card_le S m lam hm hlam1 lo hi hinterval hcontain hwidth
  · intro t ht htm
    apply largeRows_card_le S q m lam U (a * (1 + a / 9)) a
      (by positivity) (le_of_lt ha) (by nlinarith [hcoef]) hmargin
      lo hi hinterval hcontain hwidth ?_ t ht htm
    intro s hs hsu K _ hsw
    apply (Nagata.W04.scaled_width_threshold a scale U K s ha hscale hs hsu).mp
    rwa [hwidth_id] at hsw
end Nagata.W29
end
section
noncomputable section
namespace Nagata.W29
def complexPoint (p : ℤ × ℤ) : ℂ × ℂ := ((p.1 : ℂ), (p.2 : ℂ))
def complexSet (S : Finset (ℤ × ℤ)) : Finset (ℂ × ℂ) := by
  classical
  exact S.image complexPoint
theorem complexPoint_injective : Function.Injective complexPoint := by
  intro p q hpq
  apply Prod.ext
  · have h := congrArg Prod.fst hpq
    change (p.1 : ℂ) = (q.1 : ℂ) at h
    exact_mod_cast h
  · have h := congrArg Prod.snd hpq
    change (p.2 : ℂ) = (q.2 : ℂ) at h
    exact_mod_cast h
theorem rowHeights_complexSet (S : Finset (ℤ × ℤ)) :
    Nagata.Workers.W10.rowHeights (complexSet S) =
      (rowHeights S).image (fun K : ℤ => (K : ℂ)) := by
  classical
  simp only [Nagata.Workers.W10.rowHeights, complexSet, rowHeights,
    Finset.image_image, Function.comp_def, complexPoint]
theorem rowXs_complexSet (S : Finset (ℤ × ℤ)) (K : ℤ) :
    Nagata.Workers.W10.rowXs (complexSet S) (K : ℂ) =
      (rowPositions S K).image (fun j : ℤ => (j : ℂ)) := by
  classical
  ext z
  constructor
  · intro hz
    have hp := Nagata.Workers.W10.mem_rowXs.mp hz
    obtain ⟨⟨j, k⟩, hjk, heq⟩ := Finset.mem_image.mp hp
    have hkC := congrArg Prod.snd heq
    change (k : ℂ) = (K : ℂ) at hkC
    have hk : k = K := by exact_mod_cast hkC
    subst k
    exact Finset.mem_image.mpr
      ⟨j, (mem_rowPositions S j K).mpr hjk, congrArg Prod.fst heq⟩
  · intro hz
    obtain ⟨j, hj, hjz⟩ := Finset.mem_image.mp hz
    apply Nagata.Workers.W10.mem_rowXs.mpr
    exact Finset.mem_image.mpr
      ⟨(j, K), (mem_rowPositions S j K).mp hj, Prod.ext hjz rfl⟩
theorem row_card_complexSet (S : Finset (ℤ × ℤ)) (K : ℤ) :
    (Nagata.Workers.W10.rowXs (complexSet S) (K : ℂ)).card =
      (rowPositions S K).card := by
  classical
  rw [rowXs_complexSet]
  exact Finset.card_image_of_injective _ Int.cast_injective
theorem distribution_card_complexSet (S : Finset (ℤ × ℤ)) (t : ℕ) :
    ((Nagata.Workers.W10.rowHeights (complexSet S)).filter
      fun K => t ≤ (Nagata.Workers.W10.rowXs (complexSet S) K).card).card =
    (largeRows S t).card := by
  classical
  symm
  apply Finset.card_bij (fun (K : ℤ) _ => (K : ℂ))
  · intro K hK
    obtain ⟨hheight, hcard⟩ := Finset.mem_filter.mp hK
    apply Finset.mem_filter.mpr
    constructor
    · rw [rowHeights_complexSet]
      exact Finset.mem_image.mpr ⟨K, hheight, rfl⟩
    · simpa only [row_card_complexSet] using hcard
  · intro K _ L _ heq
    exact_mod_cast heq
  · intro z hz
    obtain ⟨hzheight, hzcard⟩ := Finset.mem_filter.mp hz
    rw [rowHeights_complexSet] at hzheight
    obtain ⟨K, hK, hKz⟩ := Finset.mem_image.mp hzheight
    subst z
    refine ⟨K, Finset.mem_filter.mpr ⟨hK, ?_⟩, rfl⟩
    simpa only [row_card_complexSet] using hzcard
end Nagata.W29
end
end
section
namespace Nagata.W29
theorem polygon_dilation (a lam c x y : ℝ) (hc : 0 < c) :
    Nagata.W04.InPolygon a (c * lam) (c * x) (c * y) ↔
      Nagata.W04.InPolygon a lam x y :=
  Nagata.W04.polygon_dilation a lam c x y hc
theorem integer_rows_of_raw_exponents (S : Finset (ℤ × ℤ)) (q m : ℕ)
    (d h rho a delta lam : ℝ)
    (ha : 0 < a) (hm : 0 < m) (hrho : 0 ≤ rho) (hdelta : 0 ≤ delta)
    (hlam : 0 < lam) (hlam1 : lam < 1)
    (hdegree : h = 3 * (d - 3 * (m : ℝ))) (hratio : h = (m : ℝ) * rho)
    (hslack : rho + delta * rho / 9 < lam * a - 9 * (1 - lam))
    (hcoef : 2 * a + a ^ 2 / 9 = (q : ℝ))
    (hmargin : 1 ≤ (q : ℝ) * (1 - lam) * m)
    (hexponent : ∀ p ∈ S, Nagata.ExponentEnclosure.rawExponent
      d (m : ℝ) h a delta (p.1 : ℝ) (p.2 : ℝ)) :
    (∀ K : ℤ, (rowPositions S K).card ≤ m) ∧
    (∀ t : ℕ, 1 ≤ t → t ≤ m → (largeRows S t).card ≤ q * (m - t + 1)) := by
  apply integer_rows_of_polygon S q m a lam
    (h / 9 * (a - delta) + (m : ℝ) * a) ha hm hlam hlam1 hcoef hmargin
  intro p hp
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnormalized := Nagata.ExponentEnclosure.integer_exponent_enclosure
    hmR hrho hdelta hlam1.le hdegree hratio hslack (hexponent p hp)
  change Nagata.W04.InPolygon a lam ((p.1 : ℝ) / m)
    (((p.2 : ℝ) - (h / 9 * (a - delta) + (m : ℝ) * a)) / m) at hnormalized
  have hd := (polygon_dilation a lam (m : ℝ) ((p.1 : ℝ) / m)
    (((p.2 : ℝ) - (h / 9 * (a - delta) + (m : ℝ) * a)) / m) hmR).mpr hnormalized
  simpa only [mul_div_cancel₀ _ (ne_of_gt hmR)] using hd
end Nagata.W29
end
section
noncomputable section
namespace Nagata.Workers.W10
open Nagata.W01
theorem interpolate_finset_plane_data (q m : ℕ) (S : Finset Plane)
    (hsize : ∀ K ∈ rowHeights S, (rowXs S K).card ≤ m)
    (hdistribution : ∀ t, 1 ≤ t → t ≤ m →
      ((rowHeights S).filter fun K => t ≤ (rowXs S K).card).card ≤ q * (m - t + 1))
    (v : Plane → ℂ) :
    ∃ p ∈ polynomialSpace q m, ∀ z ∈ S, planeEval p z = v z := by
  classical
  let e : Fin (rowHeights S).card ≃ rowHeights S := (rowHeights S).equivFin.symm
  let K : Fin (rowHeights S).card → ℂ := fun i => (e i).val
  let xs : Fin (rowHeights S).card → Finset ℂ := fun i => rowXs S (K i)
  have hK : Function.Injective K := fun i j h => e.injective (Subtype.ext h)
  have hpos : ∀ i, 1 ≤ (xs i).card := fun i =>
    Finset.card_pos.mpr (rowXs_nonempty (e i).property)
  have hcard : ∀ i, (xs i).card ≤ m := fun i => hsize (K i) (e i).property
  have hdist : ∀ t, 1 ≤ t → t ≤ m →
      (Finset.univ.filter fun i => t ≤ (xs i).card).card ≤ q * (m - t + 1) := by
    intro t ht htm
    change (Finset.univ.filter fun i => t ≤ (rowXs S (e i).val).card).card ≤ _
    rw [row_distribution_card S e t]
    exact hdistribution t ht htm
  obtain ⟨p, hp, hv⟩ := interpolate_distributed_rows_polynomial q m (rowHeights S).card
    K xs hK hpos hcard hdist v
  refine ⟨p, hp, ?_⟩
  intro z hz
  let k : rowHeights S := ⟨z.2, snd_mem_rowHeights hz⟩
  have he : K (e.symm k) = z.2 := congrArg Subtype.val (e.apply_symm_apply k)
  have hx : z.1 ∈ xs (e.symm k) := by
    change z.1 ∈ rowXs S (K (e.symm k))
    rw [he]
    exact mem_rowXs.mpr (by simpa only [Prod.eta] using hz)
  simpa only [he, Prod.eta] using hv (e.symm k) z.1 hx
theorem interpolate_finset_polynomial (q m : ℕ) (S : Finset Plane)
    (hsize : ∀ K ∈ rowHeights S, (rowXs S K).card ≤ m)
    (hdistribution : ∀ t, 1 ≤ t → t ≤ m →
      ((rowHeights S).filter fun K => t ≤ (rowXs S K).card).card ≤ q * (m - t + 1))
    (v : S → ℂ) :
    ∃ p ∈ polynomialSpace q m, ∀ z : S, planeEval p z.val = v z := by
  classical
  let v' : Plane → ℂ := fun z => if hz : z ∈ S then v ⟨z, hz⟩ else 0
  obtain ⟨p, hp, hv⟩ := interpolate_finset_plane_data q m S hsize hdistribution v'
  refine ⟨p, hp, ?_⟩
  intro z
  simpa only [v', dif_pos z.property] using hv z.val z.property
end Nagata.Workers.W10
end
end
section
namespace Nagata.W29
theorem finite_exponent_rows (d : ℤ) (q m : ℕ) (rho a delta lam : ℝ)
    (ha : 0 < a) (hm : 0 < m) (hrho : 0 ≤ rho) (hdelta : 0 ≤ delta)
    (hlam : 0 < lam) (hlam1 : lam < 1)
    (hratio : 3 * ((d : ℝ) - 3 * (m : ℝ)) = (m : ℝ) * rho)
    (hslack : rho + delta * rho / 9 < lam * a - 9 * (1 - lam))
    (hcoef : 2 * a + a ^ 2 / 9 = (q : ℝ))
    (hmargin : 1 ≤ (q : ℝ) * (1 - lam) * m) :
    let S := Nagata.FiniteExponents.exponentSet d (m : ℤ) a delta
    (∀ K : ℤ, (rowPositions S K).card ≤ m) ∧
    (∀ t : ℕ, 1 ≤ t → t ≤ m → (largeRows S t).card ≤ q * (m - t + 1)) := by
  dsimp only
  apply integer_rows_of_raw_exponents
    (Nagata.FiniteExponents.exponentSet d (m : ℤ) a delta) q m
    (d : ℝ) (3 * ((d : ℝ) - 3 * (m : ℝ))) rho a delta lam
    ha hm hrho hdelta hlam hlam1 rfl hratio hslack hcoef hmargin
  intro p hp
  have hraw := Nagata.FiniteExponents.mem_exponentSet_iff_raw.mp hp
  simpa only [Int.cast_natCast] using hraw
end Nagata.W29
end
section
noncomputable section
namespace Nagata.W29
theorem interpolate_integer_finset (q m : ℕ) (S : Finset (ℤ × ℤ))
    (hsize : ∀ K, (rowPositions S K).card ≤ m)
    (hdistribution : ∀ t, 1 ≤ t → t ≤ m →
      (largeRows S t).card ≤ q * (m - t + 1))
    (v : complexSet S → ℂ) :
    ∃ p ∈ Nagata.W01.polynomialSpace q m,
      ∀ z : complexSet S, Nagata.W01.planeEval p z.val = v z := by
  classical
  apply Nagata.Workers.W10.interpolate_finset_polynomial q m (complexSet S) ?_ ?_ v
  · intro z hz
    rw [rowHeights_complexSet] at hz
    obtain ⟨K, _, hKz⟩ := Finset.mem_image.mp hz
    subst z
    simpa only [row_card_complexSet] using hsize K
  · intro t ht htm
    rw [distribution_card_complexSet]
    exact hdistribution t ht htm
end Nagata.W29
end
end
section
namespace Nagata.W29
open scoped BigOperators
noncomputable def sourceOffsets (x : Fin 9 → ℝ) : Fin 9 → ℝ := fun i => 1 / 2 - x i
theorem sourceOffsets_bounds (x : Fin 9 → ℝ)
    (hx : ∀ i, 0 < x i ∧ x i < 1 / 2) :
    ∀ i, 0 < sourceOffsets x i ∧ sourceOffsets x i < 1 / 2 := by
  intro i
  obtain ⟨hlo, hhi⟩ := hx i
  dsimp [sourceOffsets]
  constructor <;> linarith
theorem sourceOffsets_sum (x : Fin 9 → ℝ) (delta : ℝ)
    (hsum : (∑ i : Fin 9, (1 / 2 - x i)) = delta) :
    (∑ i : Fin 9, sourceOffsets x i) = delta := hsum
end Nagata.W29
end
section
noncomputable section
namespace Nagata.W29
theorem finite_exponent_interpolation (d : ℤ) (q m : ℕ) (rho a delta lam : ℝ)
    (ha : 0 < a) (hm : 0 < m) (hrho : 0 ≤ rho) (hdelta : 0 ≤ delta)
    (hlam : 0 < lam) (hlam1 : lam < 1)
    (hratio : 3 * ((d : ℝ) - 3 * (m : ℝ)) = (m : ℝ) * rho)
    (hslack : rho + delta * rho / 9 < lam * a - 9 * (1 - lam))
    (hcoef : 2 * a + a ^ 2 / 9 = (q : ℝ))
    (hmargin : 1 ≤ (q : ℝ) * (1 - lam) * m)
    (v : complexSet (Nagata.FiniteExponents.exponentSet d (m : ℤ) a delta) → ℂ) :
    ∃ p ∈ Nagata.W01.polynomialSpace q m,
      ∀ z : complexSet (Nagata.FiniteExponents.exponentSet d (m : ℤ) a delta),
        Nagata.W01.planeEval p z.val = v z := by
  have hrows := finite_exponent_rows d q m rho a delta lam ha hm hrho hdelta
    hlam hlam1 hratio hslack hcoef hmargin
  exact interpolate_integer_finset q m
    (Nagata.FiniteExponents.exponentSet d (m : ℤ) a delta) hrows.1 hrows.2 v
end Nagata.W29
end
end
section
noncomputable section
namespace Nagata.W29
open Nagata.Workers.W28
end Nagata.W29
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.Workers.W12
variable {R I S : Type*} [CommSemiring R]
theorem span_restrictions_eq_top {X : Type*} (g : I → X → R) (point : S → X)
    (hinterp : ∀ target : S → R, ∃ f : X → R,
      f ∈ Submodule.span R (Set.range g) ∧ (fun s => f (point s)) = target) :
    Submodule.span R (Set.range (fun i s => g i (point s))) = ⊤ := by
  let ev : (X → R) →ₗ[R] (S → R) :=
    { toFun := fun f s => f (point s)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply top_unique
  intro target _
  obtain ⟨f, hf, htarget⟩ := hinterp target
  have he := Submodule.apply_mem_span_image_of_mem_span ev hf
  change ev f = target at htarget
  rw [htarget] at he
  simpa [← Set.range_comp, Function.comp_def, ev] using he
end Nagata.Workers.W12
end
section
namespace Nagata.Workers.W12
open Matrix
variable {R I S : Type*} [CommSemiring R] [Fintype S]
theorem mulVec_injective_of_span_rows_top (A : Matrix I S R)
    (hspan : Submodule.span R (Set.range A) = ⊤) :
    Function.Injective A.mulVec := by
  classical
  intro v w hvw
  have hdot : ∀ x ∈ Submodule.span R (Set.range A), dotProduct x v = dotProduct x w := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact congrFun hvw i
    | zero => simp
    | add x y hx hy hx' hy' =>
        rw [add_dotProduct, add_dotProduct, hx', hy']
    | smul c x hx hx' =>
        rw [smul_dotProduct, smul_dotProduct, hx']
  funext s
  have hs : Pi.single s (1 : R) ∈ Submodule.span R (Set.range A) := by
    rw [hspan]
    exact Submodule.mem_top
  simpa using hdot (Pi.single s 1) hs
theorem evaluation_mulVec_injective {X : Type*} (g : I → X → R) (point : S → X)
    (hinterp : ∀ target : S → R, ∃ f : X → R,
      f ∈ Submodule.span R (Set.range g) ∧ (fun s => f (point s)) = target) :
    Function.Injective (Matrix.mulVec (fun i s => g i (point s))) :=
  mulVec_injective_of_span_rows_top _ (span_restrictions_eq_top g point hinterp)
end Nagata.Workers.W12
end
section
namespace Nagata.Workers.W12
open Nagata.W01
theorem planeEval_mem_monomialSpace {q m : ℕ} {p : MvPolynomial (Fin 2) ℂ}
    (hp : p ∈ polynomialSpace q m) : planeEval p ∈ monomialSpace q m := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨b, hb, l, hl, rfl⟩ := hp
    have heq : planeEval (MvPolynomial.X 0 ^ b * MvPolynomial.X 1 ^ l) =
        monomial b l := by
      funext z
      simp [planeEval, monomial]
    rw [heq]
    exact monomial_mem hb hl
  | zero =>
    have heq : planeEval (0 : MvPolynomial (Fin 2) ℂ) = 0 := by
      funext z
      simp [planeEval]
    rw [heq]
    exact Submodule.zero_mem _
  | add p p' hp hp' ih ih' =>
    have heq : planeEval (p + p') = planeEval p + planeEval p' := by
      funext z
      simp [planeEval]
    rw [heq]
    exact Submodule.add_mem _ ih ih'
  | smul c p hp ih =>
    have heq : planeEval (c • p) = c • planeEval p := by
      funext z
      simp [planeEval]
    rw [heq]
    exact Submodule.smul_mem _ c ih
end Nagata.Workers.W12
end
section
noncomputable section
namespace Nagata.Workers.W12
open Nagata.FiniteExponents Nagata.Workers.W30
def B0 (d : ℤ) (q m : ℕ) (a delta : ℝ) :
    Matrix (JetIndex q m) (Column d (m : ℤ) a delta) ℂ :=
  fun row col => (col.val.2 : ℂ) ^ row.2.val * (col.val.1 : ℂ) ^ row.1.val
theorem B0_column_nonempty (d : ℤ) (m : ℕ) (a delta : ℝ)
    (hd : 3 * (m : ℤ) < d)
    (hU : firstLower d (m : ℤ) 0 a delta ∉ Set.range (Int.cast : ℤ → ℝ)) :
    Nonempty (Column d (m : ℤ) a delta) := by
  obtain ⟨p, hp⟩ := exponentSet_nonempty (Int.natCast_nonneg m) hd hU
  exact ⟨⟨p, hp⟩⟩
def columnToComplex (d m : ℤ) (a delta : ℝ) (col : Column d m a delta) :
    Nagata.W29.complexSet (exponentSet d m a delta) := by
  classical
  exact ⟨Nagata.W29.complexPoint col.val,
    Finset.mem_image.mpr ⟨col.val, col.property, rfl⟩⟩
theorem columnToComplex_bijective (d m : ℤ) (a delta : ℝ) :
    Function.Bijective (columnToComplex d m a delta) := by
  classical
  constructor
  · intro c c' h
    apply Subtype.ext
    apply Nagata.W29.complexPoint_injective
    exact congrArg Subtype.val h
  · intro z
    obtain ⟨p, hp, hz⟩ := Finset.mem_image.mp z.property
    exact ⟨⟨p, hp⟩, Subtype.ext hz⟩
def columnComplexEquiv (d m : ℤ) (a delta : ℝ) :
    Column d m a delta ≃ Nagata.W29.complexSet (exponentSet d m a delta) :=
  Equiv.ofBijective (columnToComplex d m a delta)
    (columnToComplex_bijective d m a delta)
@[simp] theorem columnComplexEquiv_val (d m : ℤ) (a delta : ℝ)
    (col : Column d m a delta) :
    (columnComplexEquiv d m a delta col).val = Nagata.W29.complexPoint col.val := rfl
end Nagata.Workers.W12
end
end
section
namespace Nagata.Workers.W12
open scoped BigOperators
open Nagata.FiniteExponents Nagata.Workers.W30
end Nagata.Workers.W12
end
section
open Filter Topology
namespace Nagata.Workers.W12
open Nagata.Workers.W30 Nagata.FiniteExponents
theorem exists_common_small_parameter (P Q : ℝ → Prop)
    (hP : ∀ᶠ τ in 𝓝[>] (0 : ℝ), P τ)
    (hQ : ∀ᶠ τ in 𝓝[>] (0 : ℝ), Q τ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ τ : ℝ, 0 < τ ∧ τ < epsilon ∧ P τ ∧ Q τ := by
  have hpos : ∀ᶠ τ in 𝓝[>] (0 : ℝ), 0 < τ := self_mem_nhdsWithin
  have hsmall : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ < epsilon :=
    mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds hepsilon)
  obtain ⟨τ, ⟨hp, hq⟩, hpos, hsmall⟩ :=
    ((hP.and hQ).and (hpos.and hsmall)).exists
  exact ⟨τ, hpos, hsmall, hp, hq⟩
theorem coefficient_kernel_contradiction
    (d : ℤ) (q m : ℕ) (a delta : ℝ)
    (B : ℝ → Matrix (JetIndex q m) (Column d (m : ℤ) a delta) ℂ)
    (hinjective : ∀ᶠ τ in 𝓝[>] (0 : ℝ), Function.Injective (B τ).mulVec)
    (hkernel : ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      ∃ v : Column d (m : ℤ) a delta → ℂ,
        v ≠ 0 ∧ (B τ).mulVec v = 0) : False := by
  obtain ⟨τ, _, _, hinj, v, hv, hzero⟩ :=
    exists_common_small_parameter _ _ hinjective hkernel (show (0 : ℝ) < 1 from zero_lt_one)
  exact hv (hinj (by simpa only [Matrix.mulVec_zero] using hzero))
end Nagata.Workers.W12
end
section
noncomputable section
namespace Nagata.Workers.W12
open Nagata.W01 Nagata.FiniteExponents Nagata.Workers.W30
theorem jet_monomial_range (q m : ℕ) :
    Set.range (fun row : JetIndex q m => monomial row.1.val row.2.val) =
      {f | ∃ b < m, ∃ l < q * (m - b), f = monomial b l} := by
  ext f
  constructor
  · rintro ⟨⟨⟨b, hb⟩, ⟨l, hl⟩⟩, rfl⟩
    exact ⟨b, hb, l, hl, rfl⟩
  · rintro ⟨b, hb, l, hl, rfl⟩
    exact ⟨⟨⟨b, hb⟩, ⟨l, hl⟩⟩, rfl⟩
theorem B0_eq_evaluationMatrix (d : ℤ) (q m : ℕ) (a delta : ℝ) :
    B0 d q m a delta =
      (fun row col => monomial row.1.val row.2.val
        (Nagata.W29.complexPoint col.val)) := by
  funext row col
  simp only [B0, monomial, Nagata.W29.complexPoint, mul_comm]
theorem B0_mulVec_injective_of_interpolation (d : ℤ) (q m : ℕ) (a delta : ℝ)
    (hinterp : ∀ v : Nagata.W29.complexSet (exponentSet d (m : ℤ) a delta) → ℂ,
      ∃ p ∈ polynomialSpace q m,
        ∀ z : Nagata.W29.complexSet (exponentSet d (m : ℤ) a delta),
          planeEval p z.val = v z) :
    Function.Injective (B0 d q m a delta).mulVec := by
  rw [B0_eq_evaluationMatrix]
  apply evaluation_mulVec_injective
    (fun row : JetIndex q m => monomial row.1.val row.2.val)
    (fun col : Column d (m : ℤ) a delta => Nagata.W29.complexPoint col.val)
  intro target
  let e := columnComplexEquiv d (m : ℤ) a delta
  obtain ⟨p, hp, hvalues⟩ := hinterp (fun z => target (e.symm z))
  refine ⟨planeEval p, ?_, ?_⟩
  · rw [jet_monomial_range]
    exact planeEval_mem_monomialSpace hp
  · funext col
    have h := hvalues (e col)
    simpa only [e, columnComplexEquiv_val, Equiv.symm_apply_apply] using h
end Nagata.Workers.W12
end
end
section
noncomputable section
namespace Nagata.Workers.W12
open Nagata.W01 Nagata.FiniteExponents Nagata.Workers.W30
theorem B0_mulVec_injective (d : ℤ) (q m : ℕ) (rho a delta lam : ℝ)
    (ha : 0 < a) (hm : 0 < m) (hrho : 0 ≤ rho) (hdelta : 0 ≤ delta)
    (hlam : 0 < lam) (hlam1 : lam < 1)
    (hratio : 3 * ((d : ℝ) - 3 * (m : ℝ)) = (m : ℝ) * rho)
    (hslack : rho + delta * rho / 9 < lam * a - 9 * (1 - lam))
    (hcoef : 2 * a + a ^ 2 / 9 = (q : ℝ))
    (hmargin : 1 ≤ (q : ℝ) * (1 - lam) * m) :
    Function.Injective (B0 d q m a delta).mulVec := by
  apply B0_mulVec_injective_of_interpolation
  exact Nagata.W29.finite_exponent_interpolation
    d q m rho a delta lam ha hm hrho hdelta hlam hlam1 hratio hslack hcoef hmargin
end Nagata.Workers.W12
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Filter Topology
namespace Nagata.Workers.W11
open Nagata.W07 Nagata.W22
theorem eventually_differentiableOn_normalizedThetaSeries_disk
    {α : Type*} {l : Filter α} {τ : α → ℝ} {n a K : ℝ} {ε : ℂ}
    (ha : 0 < a) (han : a < n) (hε : ‖ε‖ = 1)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ t in l, 0 < τ t) :
    ∀ᶠ t in l, DifferentiableOn ℂ (normalizedThetaSeries n a K ε (τ t))
      {x : ℂ | ‖x‖ < 1} := by
  have hsum := eventually_normalizedThetaSeries_partialSums
    (K := K) (R := 1) ha han hε zero_le_one hτ hτpos
  apply hsum.mono
  intro t ht
  have hlocal := (ht.mono (show {x : ℂ | ‖x‖ < 1} ⊆ {x : ℂ | ‖x‖ ≤ 1}
    from fun x hx => (show ‖x‖ < 1 from hx).le)).tendstoLocallyUniformlyOn
  have hfinite : ∀ S : Finset ℤ, DifferentiableOn ℂ
      (fun x => ∑ p ∈ S, normalizedThetaTerm n a K ε (τ t) p x)
      {x : ℂ | ‖x‖ < 1} := by
    intro S
    apply DifferentiableOn.fun_sum
    intro p _
    have hd : Differentiable ℂ (normalizedThetaTerm n a K ε (τ t) p) := by
      unfold normalizedThetaTerm
      exact (differentiable_const _).mul ((differentiable_const _).mul differentiable_id).cexp
    exact hd.differentiableOn
  exact hlocal.differentiableOn (Eventually.of_forall hfinite)
    (isOpen_lt continuous_norm continuous_const)
end Nagata.Workers.W11
end
end
section
noncomputable section
open Filter Topology
namespace Nagata.Workers.W11
open Nagata.Workers.W12 Nagata.Workers.W30 Nagata.FiniteExponents
def mixedJetAtZero (F : ℂ → ℂ → ℂ) (ell b : ℕ) : ℂ :=
  iteratedDeriv ell (fun x => iteratedDeriv b (F x) 0) 0
theorem mixedJetAtZero_separated (f : ℂ → ℂ) (j : ℂ) (ell b : ℕ) :
    mixedJetAtZero (fun x y => f x * Complex.exp (j * y)) ell b =
      iteratedDeriv ell f 0 * j ^ b := by
  have hy : (fun x => iteratedDeriv b (fun y => f x * Complex.exp (j * y)) 0) =
      fun x => f x * j ^ b := by
    funext x
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_cexp_const_mul]
    simp
  unfold mixedJetAtZero
  rw [hy, iteratedDeriv_mul_const_field]
def separatedJetMatrix (d : ℤ) (q m : ℕ) (a delta : ℝ)
    (coeff : Column d (m : ℤ) a delta → ℂ → ℂ) :
    Matrix (JetIndex q m) (Column d (m : ℤ) a delta) ℂ :=
  fun row col => mixedJetAtZero
    (fun x y => coeff col x * Complex.exp ((col.val.1 : ℂ) * y))
    row.2.val row.1.val
theorem tendsto_separatedJetMatrix_entries
    {α : Type*} {l : Filter α} (d : ℤ) (q m : ℕ) (a delta : ℝ)
    (coeff : α → Column d (m : ℤ) a delta → ℂ → ℂ)
    (hcoeff : ∀ col ell, Tendsto (fun t => iteratedDeriv ell (coeff t col) 0) l
      (𝓝 ((col.val.2 : ℂ) ^ ell))) :
    ∀ row col, Tendsto (fun t => separatedJetMatrix d q m a delta (coeff t) row col)
      l (𝓝 (B0 d q m a delta row col)) := by
  intro row col
  simpa only [separatedJetMatrix, mixedJetAtZero_separated, B0] using
    (hcoeff col row.2.val).mul_const ((col.val.1 : ℂ) ^ row.1.val)
end Nagata.Workers.W11
end
end
section
open Filter Topology
namespace Nagata.Workers.W11
theorem mixedJetAtZero_congr_of_eventuallyEq
    {F G : ℂ → ℂ → ℂ} (ell b : ℕ)
    (h : ∀ᶠ z : ℂ × ℂ in 𝓝 (0, 0), F z.1 z.2 = G z.1 z.2) :
    mixedJetAtZero F ell b = mixedJetAtZero G ell b := by
  have hp : ∀ᶠ z : ℂ × ℂ in (𝓝 0) ×ˢ (𝓝 0), F z.1 z.2 = G z.1 z.2 := by
    simpa only [nhds_prod_eq] using h
  have hi : (fun x => iteratedDeriv b (F x) 0) =ᶠ[𝓝 0]
      (fun x => iteratedDeriv b (G x) 0) :=
    hp.curry.mono fun x hx => Filter.EventuallyEq.iteratedDeriv_eq b hx
  exact Filter.EventuallyEq.iteratedDeriv_eq ell hi
end Nagata.Workers.W11
end
section
noncomputable section
open Filter Topology
namespace Nagata.Workers.W11
open Nagata.Workers.W12 Nagata.Workers.W30 Nagata.FiniteExponents
end Nagata.Workers.W11
end
end
section
noncomputable section
open Filter Topology
namespace Nagata.Workers.W11
open Nagata.Workers.W12 Nagata.Workers.W30 Nagata.FiniteExponents
theorem eventually_injective_finite_jet_matrix
    {α : Type*} {l : Filter α}
    (d : ℤ) (q m : ℕ) (rho a delta lam : ℝ)
    (ha : 0 < a) (hm : 0 < m) (hrho : 0 ≤ rho) (hdelta : 0 ≤ delta)
    (hlam : 0 < lam) (hlam1 : lam < 1)
    (hratio : 3 * ((d : ℝ) - 3 * (m : ℝ)) = (m : ℝ) * rho)
    (hslack : rho + delta * rho / 9 < lam * a - 9 * (1 - lam))
    (hcoef : 2 * a + a ^ 2 / 9 = (q : ℝ))
    (hmargin : 1 ≤ (q : ℝ) * (1 - lam) * m)
    (B : α → Matrix (JetIndex q m) (Column d (m : ℤ) a delta) ℂ)
    (hB : ∀ row col, Tendsto (fun t => B t row col) l
      (𝓝 ((col.val.2 : ℂ) ^ row.2.val * (col.val.1 : ℂ) ^ row.1.val))) :
    ∀ᶠ t in l, Function.Injective (B t).mulVec := by
  classical
  exact eventually_injective_of_injective_limit (B₀ := B0 d q m a delta) hB
    (B0_mulVec_injective d q m rho a delta lam ha hm hrho hdelta hlam hlam1
      hratio hslack hcoef hmargin)
end Nagata.Workers.W11
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Filter Topology Module
namespace Nagata.Workers.W12
open Nagata.W20 Nagata.Workers.W11 Nagata.Workers.W30 Nagata.FiniteExponents
theorem actual_basisJetMatrix_eq_of_local_expressions
    {τ gammaL gammaP : ℂ} {d : ℤ} {q m : ℕ} {a delta : ℝ} {P : ℂ → ℂ}
    (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z) {z0 : ℂ} (hz0 : z0 ≠ 0)
    (e : Basis (Column d (m : ℤ) a delta) ℂ (ActualSection τ gammaL gammaP d m P))
    (coeff : Column d (m : ℤ) a delta → ℂ → ℂ)
    (hlocal : ∀ col, ∀ᶠ z : ℂ × ℂ in 𝓝 (0, 0),
      localScalar (e col) z0 z.1 z.2 =
        coeff col z.1 * Complex.exp ((col.val.1 : ℂ) * z.2)) :
    basisJetMatrix (K := ℂ) (V := ActualSection τ gammaL gammaP d m P) e (actualJetMap (τ := τ) (γL := gammaL) (γP := gammaP) (d := d) (m := m) hP hz0 q) =
      separatedJetMatrix d q m a delta coeff := by
  funext row col
  change actualJetMap (τ := τ) (γL := gammaL) (γP := gammaP) (d := d) (m := m) hP hz0 q (e col) row = _
  rw [actualJetMap_apply_eq_mixed_derivative]
  exact mixedJetAtZero_congr_of_eventuallyEq row.2.val row.1.val (hlocal col)
end Nagata.Workers.W12
end
end
section
noncomputable section
open Filter Topology Module
namespace Nagata.Workers.W12
open Nagata.W20 Nagata.Workers.W11 Nagata.Workers.W30 Nagata.FiniteExponents
theorem actual_kernel_to_coefficients
    {τ gammaL gammaP : ℂ} {d : ℤ} {q m : ℕ} {a delta : ℝ} {P : ℂ → ℂ}
    (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z) {z0 : ℂ} (hz0 : z0 ≠ 0)
    (e : Basis (Column d (m : ℤ) a delta) ℂ (ActualSection τ gammaL gammaP d m P))
    (M : Matrix (JetIndex q m) (Column d (m : ℤ) a delta) ℂ)
    (hmatrix : basisJetMatrix (K := ℂ) (V := ActualSection τ gammaL gammaP d m P) e (actualJetMap hP hz0 q) = M)
    (F : ActualSection τ gammaL gammaP d m P)
    (hF : F ≠ 0) (hjet : actualJetMap hP hz0 q F = 0) :
    ∃ c : Column d (m : ℤ) a delta → ℂ, c ≠ 0 ∧ M.mulVec c = 0 := by
  obtain ⟨c, hc, hkernel⟩ := basisJetMatrix_nonzero_kernel (K := ℂ) (V := ActualSection τ gammaL gammaP d m P) e
    (actualJetMap hP hz0 q) F hF hjet
  exact ⟨c, hc, hmatrix ▸ hkernel⟩
end Nagata.Workers.W12
end
end
section
noncomputable section
open Filter Topology Module
namespace Nagata.Workers.W12
open Nagata.W20 Nagata.Workers.W11 Nagata.Workers.W30 Nagata.FiniteExponents
end Nagata.Workers.W12
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Filter Topology
namespace Nagata.W03
variable {α β R : Type*} [TopologicalSpace β] [NormedCommRing R]
  {l : Filter α} {s : Set β}
theorem tendstoLocallyUniformlyOn_const_one :
    TendstoLocallyUniformlyOn (fun _ : α => fun _ : β => (1 : R))
      (fun _ => 1) l s :=
  (tendsto_const_nhds.tendstoUniformlyOn_const s).tendstoLocallyUniformlyOn
theorem tendstoLocallyUniformlyOn_pow_one {F : α → β → R}
    (hF : TendstoLocallyUniformlyOn F (fun _ => 1) l s) (c : ℕ) :
    TendstoLocallyUniformlyOn (fun a x => F a x ^ c) (fun _ => 1) l s := by
  induction c with
  | zero => simpa using (tendstoLocallyUniformlyOn_const_one (R := R) (l := l) (s := s))
  | succ c ih =>
    simpa only [pow_succ, Pi.mul_def, one_mul] using
      ih.mul₀ hF continuousOn_const continuousOn_const
theorem tendstoLocallyUniformlyOn_finset_prod_one {ι : Type*}
    (T : Finset ι) {F : ι → α → β → R}
    (hF : ∀ i ∈ T, TendstoLocallyUniformlyOn (F i) (fun _ => 1) l s) :
    TendstoLocallyUniformlyOn (fun a x => ∏ i ∈ T, F i a x) (fun _ => 1) l s := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using (tendstoLocallyUniformlyOn_const_one (R := R) (l := l) (s := s))
  | @insert i T hi ih =>
    have hFi := hF i (Finset.mem_insert_self i T)
    have hFT : ∀ j ∈ T, TendstoLocallyUniformlyOn (F j) (fun _ => 1) l s :=
      fun j hj => hF j (Finset.mem_insert_of_mem hj)
    simpa only [Finset.prod_insert hi, Pi.mul_def, one_mul] using
      hFi.mul₀ (ih hFT) continuousOn_const continuousOn_const
end Nagata.W03
end
end
section
noncomputable section
open Filter Topology
namespace Nagata.W03
theorem norm_tprod_one_add_sub_one_le {ι R : Type*}
    [NormedCommRing R] [NormOneClass R] [CompleteSpace R]
    {u : ι → R} (hu : Summable (fun i => ‖u i‖)) :
    ‖(∏' i, (1 + u i)) - 1‖ ≤ Real.exp (∑' i, ‖u i‖) - 1 := by
  have hp : Tendsto (fun t : Finset ι => ∏ i ∈ t, (1 + u i)) atTop
      (𝓝 (∏' i, (1 + u i))) := (multipliable_one_add_of_summable hu).hasProd
  have hs : Tendsto (fun t : Finset ι => ∑ i ∈ t, ‖u i‖) atTop
      (𝓝 (∑' i, ‖u i‖)) := hu.hasSum
  have hl := (hp.sub (tendsto_const_nhds (x := (1 : R)))).norm
  have hr := ((Real.continuous_exp.tendsto _).comp hs).sub (tendsto_const_nhds (x := (1 : ℝ)))
  exact le_of_tendsto_of_tendsto' hl hr (fun t => t.norm_prod_one_add_sub_one_le u)
theorem norm_tprod_one_add_sub_one_le_of_tsum_norm_le {ι R : Type*}
    [NormedCommRing R] [NormOneClass R] [CompleteSpace R]
    {u : ι → R} {B : ℝ} (hu : Summable (fun i => ‖u i‖))
    (hB : (∑' i, ‖u i‖) ≤ B) :
    ‖(∏' i, (1 + u i)) - 1‖ ≤ Real.exp B - 1 :=
  (norm_tprod_one_add_sub_one_le hu).trans
    (sub_le_sub_right (Real.exp_le_exp.mpr hB) 1)
theorem tendstoUniformlyOn_tprod_one_add_of_tsum_norm_le
    {α β ι R : Type*} [NormedCommRing R] [NormOneClass R] [CompleteSpace R]
    {l : Filter α} {s : Set β} {u : α → ι → β → R} {B : α → ℝ}
    (hB : Tendsto B l (𝓝 0))
    (hsum : ∀ᶠ a in l, ∀ x ∈ s, Summable (fun i => ‖u a i x‖))
    (hbound : ∀ᶠ a in l, ∀ x ∈ s, (∑' i, ‖u a i x‖) ≤ B a) :
    TendstoUniformlyOn (fun a x => ∏' i, (1 + u a i x)) (fun _ => 1) l s := by
  have hlim : Tendsto (fun a => Real.exp (B a) - 1) l (𝓝 0) := by
    simpa using ((Real.continuous_exp.tendsto 0).comp hB).sub
      (tendsto_const_nhds (x := (1 : ℝ)))
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hsmall : ∀ᶠ a in l, Real.exp (B a) - 1 < ε :=
    hlim.eventually (gt_mem_nhds hε)
  filter_upwards [hsum, hbound, hsmall] with a hs hb he x hx
  have hnorm := (norm_tprod_one_add_sub_one_le_of_tsum_norm_le
    (hs x hx) (hb x hx)).trans_lt he
  simpa only [dist_eq_norm, norm_sub_rev] using hnorm
end Nagata.W03
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Filter Topology
namespace Nagata.W22
open Nagata.W21
def scaledThetaPositive (a : ℝ) (δ : ℂ) (τ : ℝ) (x : ℂ) : ℂ :=
  thetaPositive (τ : ℂ) (((τ ^ a : ℝ) : ℂ) * Complex.exp (δ * x))
theorem scaledThetaPositive_factor_norm_le {a τ R : ℝ} {δ x : ℂ}
    (hτ : 0 ≤ τ) (hτhalf : τ ≤ 1 / 2) (hδ : ‖δ‖ ≤ 1)
    (hR : 0 ≤ R) (hx : ‖x‖ ≤ R) (t : ℕ) :
    ‖-((τ : ℂ) ^ t * (((τ ^ a : ℝ) : ℂ) * Complex.exp (δ * x)))‖ ≤
      (1 / 2 : ℝ) ^ t * (τ ^ a * Real.exp R) := by
  have he : ‖Complex.exp (δ * x)‖ ≤ Real.exp R := by
    apply (Complex.norm_exp_le_exp_norm _).trans
    apply Real.exp_le_exp.mpr
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hx (norm_nonneg _)).trans
      ((mul_le_mul_of_nonneg_right hδ hR).trans_eq (one_mul R))
  simp only [norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hτ, abs_of_nonneg (Real.rpow_nonneg hτ _)]
  exact mul_le_mul (pow_le_pow_left₀ hτ hτhalf t)
    (mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hτ _))
    (mul_nonneg (Real.rpow_nonneg hτ _) (norm_nonneg _)) (by positivity)
theorem tendstoUniformlyOn_scaledThetaPositive
    {α : Type*} {l : Filter α} {τ : α → ℝ} {a R : ℝ} {δ : ℂ}
    (ha : 0 < a) (hδ : ‖δ‖ ≤ 1) (hR : 0 ≤ R)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) :
    TendstoUniformlyOn (fun j => scaledThetaPositive a δ (τ j)) (fun _ => 1)
      l {x : ℂ | ‖x‖ ≤ R} := by
  let u : α → ℕ → ℂ → ℂ := fun j t x =>
    -((τ j : ℂ) ^ t * (((τ j ^ a : ℝ) : ℂ) * Complex.exp (δ * x)))
  let B : α → ℝ := fun j => 2 * (τ j ^ a * Real.exp R)
  have hp := (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto.comp hτ
  have hB : Tendsto B l (𝓝 0) := by
    simpa only [B, Function.comp_def, Real.zero_rpow ha.ne', zero_mul, mul_zero] using
      (hp.mul_const (Real.exp R)).const_mul 2
  have hhalf : ∀ᶠ j in l, τ j < 1 / 2 := hτ.eventually (gt_mem_nhds (by norm_num))
  have hg : Summable (fun t : ℕ => (1 / 2 : ℝ) ^ t) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsum : ∀ᶠ j in l, ∀ x ∈ {x : ℂ | ‖x‖ ≤ R}, Summable (fun t => ‖u j t x‖) := by
    filter_upwards [hτpos, hhalf] with j hj hh x hx
    exact (hg.mul_right (τ j ^ a * Real.exp R)).of_nonneg_of_le (fun t => norm_nonneg _)
      (fun t => scaledThetaPositive_factor_norm_le hj.le hh.le hδ hR hx t)
  have hbound : ∀ᶠ j in l, ∀ x ∈ {x : ℂ | ‖x‖ ≤ R}, (∑' t, ‖u j t x‖) ≤ B j := by
    filter_upwards [hτpos, hhalf, hsum] with j hj hh hs x hx
    calc
      _ ≤ ∑' t : ℕ, (1 / 2 : ℝ) ^ t * (τ j ^ a * Real.exp R) :=
        (hs x hx).tsum_le_tsum
          (fun t => scaledThetaPositive_factor_norm_le hj.le hh.le hδ hR hx t)
          (hg.mul_right _)
      _ = B j := by
        rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num [B]
  have h := Nagata.W03.tendstoUniformlyOn_tprod_one_add_of_tsum_norm_le hB hsum hbound
  unfold scaledThetaPositive thetaPositive
  simpa only [u, sub_eq_add_neg] using h
theorem tendstoLocallyUniformlyOn_scaledThetaPositive
    {α : Type*} {l : Filter α} {τ : α → ℝ} {a : ℝ} {δ : ℂ}
    (ha : 0 < a) (hδ : ‖δ‖ ≤ 1)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) :
    TendstoLocallyUniformlyOn (fun j => scaledThetaPositive a δ (τ j))
      (fun _ => 1) l Set.univ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro S hS hSc
  obtain ⟨R, hR⟩ := hSc.exists_bound_of_continuousOn (f := fun x : ℂ => x) continuous_id.continuousOn
  apply (tendstoUniformlyOn_scaledThetaPositive ha hδ (le_max_right R 0) hτ hτpos).mono
  intro x hx
  exact (hR x hx).trans (le_max_left R 0)
def shiftedThetaProduct (a : ℝ) (τ : ℝ) (x : ℂ) : ℂ :=
  thetaProduct (τ : ℂ) (((τ ^ a : ℝ) : ℂ) * Complex.exp x)
theorem shiftedThetaProduct_eq_halves {τ : ℝ} (hτ : 0 < τ) (a : ℝ) (x : ℂ) :
    shiftedThetaProduct a τ x = scaledThetaPositive a 1 τ x *
      scaledThetaPositive (1 - a) (-1) τ x := by
  unfold shiftedThetaProduct thetaProduct scaledThetaPositive
  simp only [one_mul, neg_one_mul, mul_inv_rev, ← Complex.exp_neg]
  congr 2
  rw [Real.rpow_sub hτ, Real.rpow_one, Complex.ofReal_div]
  ring
theorem tendstoLocallyUniformlyOn_shiftedThetaProduct
    {α : Type*} {l : Filter α} {τ : α → ℝ} {a : ℝ}
    (ha : 0 < a) (haone : a < 1)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) :
    TendstoLocallyUniformlyOn (fun j => shiftedThetaProduct a (τ j))
      (fun _ => 1) l Set.univ := by
  have hp := tendstoLocallyUniformlyOn_scaledThetaPositive (δ := (1 : ℂ)) ha (by simp) hτ hτpos
  have hm := tendstoLocallyUniformlyOn_scaledThetaPositive (δ := (-1 : ℂ))
    (sub_pos.mpr haone) (by simp) hτ hτpos
  have h := hp.mul₀ hm continuousOn_const continuousOn_const
  apply (show TendstoLocallyUniformlyOn
    (fun j x => scaledThetaPositive a 1 (τ j) x * scaledThetaPositive (1 - a) (-1) (τ j) x)
    (fun _ => (1 : ℂ)) l Set.univ by simpa only [Pi.mul_def, mul_one] using h).congr_inseparable
  filter_upwards [hτpos] with j hj x hx
  exact .of_eq (shiftedThetaProduct_eq_halves hj a x).symm
end Nagata.W22
end
end
section
noncomputable section
open Filter Topology
namespace Nagata.W22
def markedPi (a : Fin 9 → ℝ) (τ : ℝ) (x : ℂ) : ℂ :=
  ∏ i : Fin 9, shiftedThetaProduct (a i) τ x
theorem shiftedThetaProduct_differentiable {τ : ℝ}
    (hτ : 0 < τ) (hτone : τ < 1) (a : ℝ) :
    Differentiable ℂ (shiftedThetaProduct a τ) := by
  have ht : ‖(τ : ℂ)‖ < 1 := by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ] using hτone
  intro x
  have hz : ((τ ^ a : ℝ) : ℂ) * Complex.exp x ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hτ a).ne') (Complex.exp_ne_zero x)
  exact (Nagata.W21.thetaProduct_differentiableAt ht hz).comp x
    ((Complex.hasDerivAt_exp x).const_mul ((τ ^ a : ℝ) : ℂ)).differentiableAt
theorem markedPi_differentiable {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (a : Fin 9 → ℝ) : Differentiable ℂ (markedPi a τ) := by
  exact Differentiable.fun_finsetProd fun i hi => shiftedThetaProduct_differentiable hτ hτone (a i)
theorem tendstoLocallyUniformlyOn_markedPi
    {α : Type*} {l : Filter α} {τ : α → ℝ} {a : Fin 9 → ℝ}
    (ha : ∀ i, 0 < a i) (haone : ∀ i, a i < 1)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) :
    TendstoLocallyUniformlyOn (fun j => markedPi a (τ j)) (fun _ => 1) l Set.univ := by
  exact Nagata.W03.tendstoLocallyUniformlyOn_finset_prod_one Finset.univ
    (fun i hi => tendstoLocallyUniformlyOn_shiftedThetaProduct (ha i) (haone i) hτ hτpos)
theorem tendstoLocallyUniformlyOn_markedPi_pow
    {α : Type*} {l : Filter α} {τ : α → ℝ} {a : Fin 9 → ℝ}
    (ha : ∀ i, 0 < a i) (haone : ∀ i, a i < 1)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) (e : ℕ) :
    TendstoLocallyUniformlyOn (fun j x => markedPi a (τ j) x ^ e) (fun _ => 1) l Set.univ := by
  exact Nagata.W03.tendstoLocallyUniformlyOn_pow_one
    (tendstoLocallyUniformlyOn_markedPi ha haone hτ hτpos) e
theorem tendsto_iteratedDeriv_markedPi_pow_zero
    {α : Type*} {l : Filter α} {τ : α → ℝ} {marks : Fin 9 → ℝ}
    (hmarks : ∀ i, 0 < marks i) (hmarksone : ∀ i, marks i < 1)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) (e c : ℕ) :
    Tendsto (fun j => iteratedDeriv c (fun x => markedPi marks (τ j) x ^ e) 0)
      l (𝓝 ((0 : ℂ) ^ c)) := by
  have hf := tendstoLocallyUniformlyOn_markedPi_pow hmarks hmarksone hτ hτpos e
  have hone : ∀ᶠ j in l, τ j < 1 := hτ.eventually (gt_mem_nhds zero_lt_one)
  have hd : ∀ᶠ j in l, DifferentiableOn ℂ (fun x => markedPi marks (τ j) x ^ e) Set.univ := by
    filter_upwards [hτpos, hone] with j hj ho
    exact ((markedPi_differentiable hj ho marks).pow e).differentiableOn
  have h := (tendstoLocallyUniformlyOn_iteratedDeriv hf hd isOpen_univ c).tendsto_at
    (a := (0 : ℂ)) (Set.mem_univ _)
  convert h using 1
  cases c <;> simp [iteratedDeriv_const]
end Nagata.W22
end
end
section
noncomputable section
namespace Nagata.W22
def rayMarkedSection {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (ξ : Fin 9 → ℝ) :=
  Nagata.W08.markedThetaSection
    (τ := (τ : ℂ))
    (by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ] using hτone)
    (Complex.ofReal_ne_zero.mpr hτ.ne')
    (fun i => ((τ ^ ξ i : ℝ) : ℂ))
    (fun i => Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hτ (ξ i)).ne')
theorem rayMarkedSection_centered {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (ξ : Fin 9 → ℝ) (x₀ : ℝ) (x : ℂ) :
    (rayMarkedSection hτ hτone ξ).val (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      markedPi (fun i => x₀ - ξ i) τ x := by
  have hz : ((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hτ x₀).ne')
      (Complex.exp_ne_zero x)
  unfold rayMarkedSection
  rw [Nagata.W08.markedThetaSection_apply _ _ _ _ hz]
  unfold Nagata.W21.markedThetaProduct markedPi shiftedThetaProduct
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  rw [Real.rpow_sub hτ, Complex.ofReal_div]
  ring
end Nagata.W22
end
end
section
noncomputable section
open Filter Topology
namespace Nagata.W22
def multipliedThetaCoefficient (marks : Fin 9 → ℝ) (n a K : ℝ) (ε : ℂ)
    (e : ℕ) (τ : ℝ) (x : ℂ) : ℂ :=
  markedPi marks τ x ^ e * normalizedThetaSeries n a K ε τ x
theorem tendstoLocallyUniformlyOn_multipliedThetaCoefficient
    {α : Type*} {l : Filter α} {τ : α → ℝ} {marks : Fin 9 → ℝ}
    {n a K : ℝ} {ε : ℂ}
    (hmarks : ∀ i, 0 < marks i) (hmarksone : ∀ i, marks i < 1)
    (ha : 0 < a) (han : a < n) (hε : ‖ε‖ = 1)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) (e : ℕ) :
    TendstoLocallyUniformlyOn (fun j => multipliedThetaCoefficient marks n a K ε e (τ j))
      (fun x => Complex.exp ((K : ℂ) * x)) l Set.univ := by
  have hp := tendstoLocallyUniformlyOn_markedPi_pow hmarks hmarksone hτ hτpos e
  have ht := tendstoLocallyUniformlyOn_normalizedThetaSeries (K := K) ha han hε hτ hτpos
  unfold multipliedThetaCoefficient
  simpa only [Pi.mul_def, one_mul] using hp.mul₀ ht continuousOn_const
    ((Complex.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)
theorem tendsto_iteratedDeriv_multipliedThetaCoefficient_zero
    {α : Type*} {l : Filter α} {τ : α → ℝ} {marks : Fin 9 → ℝ}
    {n a K : ℝ} {ε : ℂ}
    (hmarks : ∀ i, 0 < marks i) (hmarksone : ∀ i, marks i < 1)
    (ha : 0 < a) (han : a < n) (hε : ‖ε‖ = 1)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) (e c : ℕ) :
    Tendsto (fun j => iteratedDeriv c (multipliedThetaCoefficient marks n a K ε e (τ j)) 0)
      l (𝓝 ((K : ℂ) ^ c)) := by
  have hf := tendstoLocallyUniformlyOn_multipliedThetaCoefficient (K := K)
    hmarks hmarksone ha han hε hτ hτpos e
  have hone : ∀ᶠ j in l, τ j < 1 := hτ.eventually (gt_mem_nhds zero_lt_one)
  have htheta := Nagata.Workers.W11.eventually_differentiableOn_normalizedThetaSeries_disk
    (K := K) ha han hε hτ hτpos
  have hd : ∀ᶠ j in l, DifferentiableOn ℂ
      (multipliedThetaCoefficient marks n a K ε e (τ j)) {x : ℂ | ‖x‖ < 1} := by
    filter_upwards [hτpos, hone, htheta] with j hj ho ht
    exact (((markedPi_differentiable hj ho marks).pow e).differentiableOn).mul ht
  have h := (tendstoLocallyUniformlyOn_iteratedDeriv
    (hf.mono (Set.subset_univ _)) hd (isOpen_lt continuous_norm continuous_const) c).tendsto_at
    (a := (0 : ℂ)) (by simp)
  simpa only [iteratedDeriv_cexp_const_mul, mul_zero, Complex.exp_zero, mul_one] using h
end Nagata.W22
end
end
section
noncomputable section
open Filter Topology
namespace Nagata.W22
open Nagata.FiniteExponents
def basisCoefficient (d m : ℤ) (ρ Δ : ℝ) (marks : Fin 9 → ℝ)
    (τ : ℝ) (col : Column d m ρ Δ) : ℂ → ℂ :=
  let j := col.val.1
  let K := col.val.2
  if j ≤ m then
    normalizedThetaSeries (commonDegree d m : ℝ)
      ((K : ℝ) - firstLower d m j ρ Δ) (K : ℝ) ((-1 : ℂ) ^ (m - j)) τ
  else if 0 < d - 3 * j then
    multipliedThetaCoefficient marks (sourceDegree d j : ℝ)
      ((K : ℝ) - secondLower d j ρ Δ) (K : ℝ) 1 (Int.toNat (j - m)) τ
  else
    fun x => markedPi marks τ x ^ Int.toNat (j - m)
theorem eventually_differentiableOn_basisCoefficient_disk
    {α : Type*} {l : Filter α} {τ : α → ℝ} {d m : ℤ} {ρ Δ : ℝ}
    (marks : Fin 9 → ℝ) (hτ : Tendsto τ l (𝓝 0))
    (hτpos : ∀ᶠ t in l, 0 < τ t) :
    ∀ᶠ t in l, ∀ col : Column d m ρ Δ,
      DifferentiableOn ℂ (basisCoefficient d m ρ Δ marks (τ t) col)
        {x : ℂ | ‖x‖ < 1} := by
  classical
  apply Filter.eventually_all.mpr
  rintro ⟨⟨j, K⟩, hcol⟩
  have hone : ∀ᶠ t in l, τ t < 1 := hτ.eventually (gt_mem_nhds zero_lt_one)
  change (j, K) ∈ exponentSet d m ρ Δ at hcol
  rcases mem_exponentSet_iff.mp hcol with hfirst | hsecond | hzero
  · rcases hfirst with ⟨hj0, hjm, hlo, hhi⟩
    simp only [basisCoefficient, if_pos hjm]
    exact Nagata.Workers.W11.eventually_differentiableOn_normalizedThetaSeries_disk
      (by linarith) (by linarith) (by simp) hτ hτpos
  · rcases hsecond with ⟨hmj, hjd, hdpos, hlo, hhi⟩
    simp only [basisCoefficient, if_neg (not_le.mpr hmj), if_pos hdpos]
    have ht := Nagata.Workers.W11.eventually_differentiableOn_normalizedThetaSeries_disk
      (n := (sourceDegree d j : ℝ)) (a := (K : ℝ) - secondLower d j ρ Δ)
      (K := (K : ℝ)) (ε := 1) (by linarith) (by linarith) (by simp) hτ hτpos
    filter_upwards [hτpos, hone, ht] with t hpos hone htheta
    exact (((markedPi_differentiable hpos hone marks).pow (Int.toNat (j-m))).differentiableOn).mul htheta
  · rcases hzero with ⟨hmj, hjd, hd0, rfl⟩
    simp only [basisCoefficient, if_neg (not_le.mpr hmj), hd0, lt_self_iff_false, ite_false]
    filter_upwards [hτpos, hone] with t hpos hone
    exact ((markedPi_differentiable hpos hone marks).pow (Int.toNat (j-m))).differentiableOn
theorem eventually_contDiffAt_basisCoefficient
    {α : Type*} {l : Filter α} {τ : α → ℝ} {d m : ℤ} {ρ Δ : ℝ}
    (marks : Fin 9 → ℝ) (hτ : Tendsto τ l (𝓝 0))
    (hτpos : ∀ᶠ j in l, 0 < τ j) :
    ∀ᶠ j in l, ∀ col : Column d m ρ Δ, ∀ c : ℕ,
      ContDiffAt ℂ c (basisCoefficient d m ρ Δ marks (τ j) col) 0 := by
  filter_upwards [eventually_differentiableOn_basisCoefficient_disk
    (d := d) (m := m) (ρ := ρ) (Δ := Δ) marks hτ hτpos] with j hj col c
  exact ((hj col).contDiffOn (isOpen_lt continuous_norm continuous_const)).contDiffAt
    ((isOpen_lt continuous_norm continuous_const).mem_nhds (by simp))
theorem tendsto_iteratedDeriv_basisCoefficient_zero
    {α : Type*} {l : Filter α} {τ : α → ℝ} {d m : ℤ} {ρ Δ : ℝ}
    {marks : Fin 9 → ℝ}
    (hmarks : ∀ i, 0 < marks i) (hmarksone : ∀ i, marks i < 1)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j)
    (col : Column d m ρ Δ) (c : ℕ) :
    Tendsto (fun t => iteratedDeriv c (basisCoefficient d m ρ Δ marks (τ t) col) 0)
      l (𝓝 ((col.val.2 : ℂ) ^ c)) := by
  rcases col with ⟨⟨j, K⟩, hcol⟩
  change (j, K) ∈ exponentSet d m ρ Δ at hcol
  rcases mem_exponentSet_iff.mp hcol with hfirst | hsecond | hzero
  · rcases hfirst with ⟨hj0, hjm, hlo, hhi⟩
    simp only [basisCoefficient, if_pos hjm]
    have hε : ‖(-1 : ℂ) ^ (m - j)‖ = 1 := by simp
    simpa using tendsto_iteratedDeriv_normalizedThetaSeries_zero
      (a := (K : ℝ) - firstLower d m j ρ Δ)
      (n := (commonDegree d m : ℝ)) (K := (K : ℝ))
      (by linarith) (by linarith) hε hτ hτpos c
  · rcases hsecond with ⟨hmj, hjd, hdpos, hlo, hhi⟩
    simp only [basisCoefficient, if_neg (not_le.mpr hmj), if_pos hdpos]
    simpa using tendsto_iteratedDeriv_multipliedThetaCoefficient_zero hmarks hmarksone
      (a := (K : ℝ) - secondLower d j ρ Δ)
      (n := (sourceDegree d j : ℝ)) (K := (K : ℝ))
      (by linarith) (by linarith) (by simp : ‖(1 : ℂ)‖ = 1) hτ hτpos
      (Int.toNat (j - m)) c
  · rcases hzero with ⟨hmj, hjd, hd0, rfl⟩
    simp only [basisCoefficient, if_neg (not_le.mpr hmj), hd0, lt_self_iff_false, ite_false]
    simpa only [Int.cast_zero] using tendsto_iteratedDeriv_markedPi_pow_zero hmarks hmarksone hτ hτpos
      (Int.toNat (j - m)) c
end Nagata.W22
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Filter Topology
namespace Nagata.Workers.W11
open Nagata.Workers.W12 Nagata.Workers.W30 Nagata.FiniteExponents
def thetaJetMatrix (d : ℤ) (q m : ℕ) (a delta : ℝ)
    (marks : Fin 9 → ℝ) (τ : ℝ) :
    Matrix (JetIndex q m) (Column d (m : ℤ) a delta) ℂ :=
  separatedJetMatrix d q m a delta
    (Nagata.W22.basisCoefficient d (m : ℤ) a delta marks τ)
theorem tendsto_thetaJetMatrix_entries
    {α : Type*} {l : Filter α} {τ : α → ℝ}
    (d : ℤ) (q m : ℕ) (a delta : ℝ) (marks : Fin 9 → ℝ)
    (hmarks : ∀ i, 0 < marks i) (hmarksone : ∀ i, marks i < 1)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ t in l, 0 < τ t) :
    ∀ row col, Tendsto (fun t => thetaJetMatrix d q m a delta marks (τ t) row col)
      l (𝓝 (B0 d q m a delta row col)) := by
  exact tendsto_separatedJetMatrix_entries d q m a delta
    (fun t => Nagata.W22.basisCoefficient d (m : ℤ) a delta marks (τ t))
    (Nagata.W22.tendsto_iteratedDeriv_basisCoefficient_zero hmarks hmarksone hτ hτpos)
end Nagata.Workers.W11
end
end
section
noncomputable section
open Filter Topology
namespace Nagata.Workers.W11
open Nagata.Workers.W12 Nagata.Workers.W30 Nagata.FiniteExponents
theorem eventually_injective_thetaJetMatrix
    (d : ℤ) (q m : ℕ) (rho a delta lam : ℝ)
    (ha : 0 < a) (hm : 0 < m) (hrho : 0 ≤ rho) (hdelta : 0 ≤ delta)
    (hlam : 0 < lam) (hlam1 : lam < 1)
    (hratio : 3 * ((d : ℝ) - 3 * (m : ℝ)) = (m : ℝ) * rho)
    (hslack : rho + delta * rho / 9 < lam * a - 9 * (1 - lam))
    (hcoef : 2 * a + a ^ 2 / 9 = (q : ℝ))
    (hmargin : 1 ≤ (q : ℝ) * (1 - lam) * m)
    (marks : Fin 9 → ℝ)
    (hmarks : ∀ i, 0 < marks i) (hmarksone : ∀ i, marks i < 1) :
    ∀ᶠ τ in 𝓝[>] (0 : ℝ), Function.Injective (thetaJetMatrix d q m a delta marks τ).mulVec := by
  classical
  apply eventually_injective_finite_jet_matrix d q m rho a delta lam
    ha hm hrho hdelta hlam hlam1 hratio hslack hcoef hmargin
    (thetaJetMatrix d q m a delta marks)
  exact tendsto_thetaJetMatrix_entries d q m a delta marks hmarks hmarksone
    (tendsto_id.mono_left nhdsWithin_le_nhds) self_mem_nhdsWithin
end Nagata.Workers.W11
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Filter Topology
open scoped BigOperators
namespace Nagata.W29
theorem exists_scaled_thetaJetMatrix_source_data
    (r d m : ℕ) (hr : 10 ≤ r) (hm : 0 < m)
    (hlow : 3 < (d : ℝ) / m) (hupp : (d : ℝ) / m < Real.sqrt r) :
    ∃ (n : ℕ) (delta : ℝ) (x : Fin 9 → ℝ),
      0 < n ∧ 0 < delta ∧ delta < 1 / 2 ∧
      Function.Injective x ∧ (∀ i, 0 < x i ∧ x i < 1 / 2) ∧
      (∑ i : Fin 9, sourceOffsets x i) = delta ∧
      (∀ j : ℤ, 0 ≤ j → j ≤ ((n * m : ℕ) : ℤ) →
        Nagata.FiniteExponents.firstLower ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
          j (3 * (Real.sqrt r - 3)) delta ∉ Set.range (Int.cast : ℤ → ℝ)) ∧
      (∀ j : ℤ, ((n * m : ℕ) : ℤ) < j → j ≤ ((n * d : ℕ) : ℤ) / 3 →
        0 < ((n * d : ℕ) : ℤ) - 3 * j →
        Nagata.FiniteExponents.secondLower ((n * d : ℕ) : ℤ) j
          (3 * (Real.sqrt r - 3)) delta ∉ Set.range (Int.cast : ℤ → ℝ)) ∧
      (Nagata.FiniteExponents.exponentSet ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
        (3 * (Real.sqrt r - 3)) delta).Nonempty ∧
      ∀ᶠ τ in 𝓝[>] (0 : ℝ), Function.Injective
        (Nagata.Workers.W11.thetaJetMatrix ((n * d : ℕ) : ℤ) (r - 9) (n * m)
          (3 * (Real.sqrt r - 3)) delta (sourceOffsets x) τ).mulVec := by
  obtain ⟨n, D, M, q, rho, a, h, lam, delta, eta, x,
    hn, hD, hM, hq, hDpos, hMpos, hqpos, hindex, hratio, hrhodef, hadef,
    hhdef, hhrho, hrhopos, hrhogap, hapos, hhpos, hcoef, hlam0, hlam1,
    hgap, hmargin, hdelta0, hdeltaHalf, hslack, hnonint1, hnonint2,
    hxinj, hxbounds, hxsum, hxsum2, heta, heta2⟩ :=
    Nagata.Workers.W05.exists_scaled_parameters r d m hr hm hlow hupp
  subst D
  subst M
  subst q
  subst a
  have hfirst := Nagata.Workers.W05.firstLower_nonintegral_of_fin
    (n * d) (n * m) (3 * (Real.sqrt r - 3)) delta
    (by simpa only [hhdef] using hnonint1)
  have hsecond := Nagata.Workers.W05.secondLower_nonintegral_of_fin
    (n * d) (n * m) (3 * (Real.sqrt r - 3)) delta
    (by simpa only [hhdef] using hnonint2)
  have hdegreeR : 3 * ((n * m : ℕ) : ℝ) < ((n * d : ℕ) : ℝ) := by
    linarith [hhdef, hhpos]
  have hdegreeZ : 3 * ((n * m : ℕ) : ℤ) < ((n * d : ℕ) : ℤ) := by
    exact_mod_cast hdegreeR
  have hnonempty := Nagata.FiniteExponents.exponentSet_nonempty
    (by positivity : (0 : ℤ) ≤ ((n * m : ℕ) : ℤ)) hdegreeZ
    (hfirst 0 le_rfl (by positivity))
  refine ⟨n, delta, x, hn, hdelta0, hdeltaHalf, hxinj, hxbounds,
    sourceOffsets_sum x delta hxsum, hfirst, hsecond, hnonempty, ?_⟩
  exact Nagata.Workers.W11.eventually_injective_thetaJetMatrix
    ((n * d : ℕ) : ℤ) (r - 9) (n * m) rho (3 * (Real.sqrt r - 3)) delta lam
    hapos hMpos hrhopos.le hdelta0.le hlam0 hlam1
    (by simpa only [Int.cast_natCast] using hhdef.symm.trans hhrho)
    hslack hcoef hmargin (sourceOffsets x)
    (fun i => (sourceOffsets_bounds x hxbounds i).1)
    (fun i => lt_trans (sourceOffsets_bounds x hxbounds i).2 (by norm_num))
end Nagata.W29
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.Workers.W17
open Filter
open scoped Topology
variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜]
    [TopologicalSpace V] [T2Space V] [Zero V]
variable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
end Nagata.Workers.W17
end
section
noncomputable section
namespace Nagata.Workers.W17
open Nagata.Workers.W28
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
end Nagata.Workers.W17
end
end
section
namespace Nagata.Workers.W17
open Nagata.Workers.W28
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
end Nagata.Workers.W17
end
section
namespace Nagata.Workers.W17
open scoped ContDiff
variable {𝕜 P E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup P] [NormedSpace 𝕜 P]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
end Nagata.Workers.W17
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W28
open scoped BigOperators
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators
end Nagata.Workers.W28
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W16.AssociatedBundle
open Nagata.ProjectiveGeometry
variable {n : ℕ} (G : NonzeroHomogeneousForm n)
structure BundleVector (k : ℕ) where
  x : Fin 3 → ℂ
  x_ne_zero : x ≠ 0
  on_curve : MvPolynomial.eval x G.polynomial = 0
  w : ℂ
variable {G}
def Equivalent {k : ℕ} (a b : BundleVector G k) : Prop :=
  ∃ u : ℂˣ, a.x = (u : ℂ) • b.x ∧ a.w = (u : ℂ) ^ k * b.w
theorem equivalent_refl {k : ℕ} (a : BundleVector G k) : Equivalent a a := by
  exact ⟨1, by simp, by simp⟩
theorem equivalent_symm {k : ℕ} {a b : BundleVector G k}
    (h : Equivalent a b) : Equivalent b a := by
  obtain ⟨u, hx, hw⟩ := h
  refine ⟨u⁻¹, ?_, ?_⟩
  · rw [hx, smul_smul]
    simp
  · rw [hw, ← mul_assoc, ← mul_pow]
    simp
theorem equivalent_trans {k : ℕ} {a b c : BundleVector G k}
    (hab : Equivalent a b) (hbc : Equivalent b c) : Equivalent a c := by
  obtain ⟨u, hux, huw⟩ := hab
  obtain ⟨v, hvx, hvw⟩ := hbc
  refine ⟨u * v, ?_, ?_⟩
  · rw [hux, hvx, smul_smul]
    rfl
  · rw [huw, hvw]
    simp [mul_pow, mul_assoc]
def bundleSetoid (G : NonzeroHomogeneousForm n) (k : ℕ) : Setoid (BundleVector G k) where
  r := Equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩
def TotalSpace (G : NonzeroHomogeneousForm n) (k : ℕ) := Quotient (bundleSetoid G k)
def mk {k : ℕ} (a : BundleVector G k) : TotalSpace G k := Quotient.mk _ a
open scoped BigOperators
end Nagata.W16.AssociatedBundle
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W07
open Nagata.W08
def sectionEval (τ : ℂ) (n : ℤ) (γ z : ℂ) :
    automorphicSections τ n γ →ₗ[ℂ] ℂ where
  toFun f := f.val z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem linearMap_surjective_of_kernel_codimension
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (L : V →ₗ[ℂ] W)
    (hdim : Module.finrank ℂ (LinearMap.ker L) + Module.finrank ℂ W =
      Module.finrank ℂ V) : Function.Surjective L := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  have hr := L.finrank_range_add_finrank_ker
  omega
theorem cubic_eval_surjective (τ γ z : ℂ)
    (h3 : Module.finrank ℂ (automorphicSections τ 3 γ) = 3)
    (hker : Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2) :
    Function.Surjective (sectionEval τ 3 γ z) := by
  let : FiniteDimensional ℂ (automorphicSections τ 3 γ) :=
    FiniteDimensional.of_finrank_pos (by omega)
  apply linearMap_surjective_of_kernel_codimension
  simp [h3, hker]
theorem cubic_exists_section_eval_one (τ γ z : ℂ)
    (h3 : Module.finrank ℂ (automorphicSections τ 3 γ) = 3)
    (hker : Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2) :
    ∃ f : automorphicSections τ 3 γ, f.val z = 1 :=
  cubic_eval_surjective τ γ z h3 hker 1
end Nagata.W07
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W07
open Nagata.W08 Filter Topology
theorem section_zero_mul_iff {τ γ z : ℂ} {n : ℤ} (hγ : γ ≠ 0) (hz : z ≠ 0)
    (f : automorphicSections τ n γ) : f.val (τ * z) = 0 ↔ f.val z = 0 := by
  rw [f.property.2.2 z hz]
  simp only [mul_eq_zero, hγ, zpow_ne_zero _ hz, false_or]
theorem invariant_zpow {G α : Type*} [CommGroup G] (τ : G) (F : G → α)
    (hstep : ∀ z, F (τ * z) = F z) (z : G) (k : ℤ) : F (τ ^ k * z) = F z := by
  have he : (fun k : ℤ => F (τ ^ k * z)) = (fun _ : ℤ => F z) := by
    apply Nagata.W08.biInfinite_unique (fun _ x => x)
    · intro _ _ _ h
      exact h
    · intro j
      rw [zpow_add, zpow_one, mul_comm (τ ^ j) τ, mul_assoc]
      exact hstep (τ ^ j * z)
    · intro _
      rfl
    · simp
  exact congrFun he k
theorem section_zero_orbit_iff {τ γ a : ℂ} {n : ℤ}
    (hτ : τ ≠ 0) (hγ : γ ≠ 0) (ha : a ≠ 0)
    (f : automorphicSections τ n γ) (k : ℤ) :
    f.val (τ ^ k * a) = 0 ↔ f.val a = 0 := by
  let τu : ℂˣ := Units.mk0 τ hτ
  let au : ℂˣ := Units.mk0 a ha
  have h := invariant_zpow τu (fun z : ℂˣ => f.val (z : ℂ) = 0)
    (fun z => propext (section_zero_mul_iff hγ z.ne_zero f)) au k
  simpa [τu, au] using Iff.of_eq h
theorem section_order_one_iff {τ γ z : ℂ} {n : ℤ}
    (f : automorphicSections τ n γ) (hz : z ≠ 0) :
    (1 : ℕ∞) ≤ analyticOrderAt f.val z ↔ f.val z = 0 := by
  have h := natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (n := 1) (automorphicSection_analyticAt f hz)
  simpa using h
end Nagata.W07
end
end
section
noncomputable section
namespace Nagata.W07
open Nagata.W08 Nagata.CoefficientSpaces
def pointThetaMultiply {τ a : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0)
    (n : ℤ) (γ : ℂ) (k : ℕ) :
    automorphicSections τ (n - (k : ℤ)) (γ / (-a) ^ k) →ₗ[ℂ]
      automorphicSections τ n γ :=
  LinearMap.codRestrict (automorphicSections τ n γ)
    (multiplySection τ (γ / (-a) ^ k) (n - (k : ℤ))
      (thetaProductSection hτ hτ0 ha).val k) (by
    intro G
    change multiplyPower (thetaProductSection hτ hτ0 ha).val k G.val ∈
      automorphicSections τ n γ
    have h := multiplyPower_mem_sections (thetaProductSection hτ hτ0 ha).property G.property k
    have hdeg : n - (k : ℤ) + (k : ℤ) * 1 = n := by ring
    have hgam : (γ / (-a) ^ k) * (-a) ^ k = γ :=
      div_mul_cancel₀ γ (pow_ne_zero k (neg_ne_zero.mpr ha))
    simpa only [hdeg, hgam] using h)
theorem pointTheta_order_ne_top {τ a z : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hz : z ≠ 0) :
    analyticOrderAt (thetaProductSection hτ hτ0 ha).val z ≠ ⊤ := by
  by_cases hP : (thetaProductSection hτ hτ0 ha).val z = 0
  · rw [(automorphicSection_analyticAt _ hz).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      hP (thetaProductSection_zero_has_nonzero_deriv hτ hτ0 ha hz hP)]
    simp
  · rw [(automorphicSection_analyticAt _ hz).analyticOrderAt_eq_zero.mpr hP]
    simp
theorem pointThetaMultiply_injective {τ a : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (n : ℤ) (γ : ℂ) (k : ℕ) :
    Function.Injective (pointThetaMultiply hτ hτ0 ha n γ k) := by
  have hinj := multiplySection_injective τ (γ / (-a) ^ k) (n - (k : ℤ))
    (thetaProductSection hτ hτ0 ha).val k
    (automorphicSection_analyticOnNhd _) (fun z hz => pointTheta_order_ne_top hτ hτ0 ha hz)
  intro f g hfg
  apply hinj
  exact congrArg Subtype.val hfg
theorem pointThetaMultiply_range_eq_eval_kernel {τ a γ : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hγ : γ ≠ 0) (n : ℤ) :
    LinearMap.range (pointThetaMultiply hτ hτ0 ha n γ 1) =
      LinearMap.ker (sectionEval τ n γ a) := by
  ext f
  constructor
  · rintro ⟨G, rfl⟩
    change (thetaProductSection hτ hτ0 ha).val a ^ 1 * G.val a = 0
    simp
  · intro hf
    have hfa : f.val a = 0 := hf
    have hzero : ∀ z ≠ 0, (thetaProductSection hτ hτ0 ha).val z = 0 →
        deriv (thetaProductSection hτ hτ0 ha).val z ≠ 0 ∧
          (1 : ℕ∞) ≤ analyticOrderAt f.val z := by
      intro z hz hP
      refine ⟨thetaProductSection_zero_has_nonzero_deriv hτ hτ0 ha hz hP, ?_⟩
      apply (section_order_one_iff f hz).mpr
      obtain ⟨k, hk⟩ := (thetaProductSection_zero_iff hτ hτ0 ha hz).mp hP
      rw [hk, mul_comm a]
      exact (section_zero_orbit_iff hτ0 hγ ha f k).mpr hfa
    obtain ⟨G, hG⟩ : ∃ G : automorphicSections τ (n - (1 : ℤ)) (γ / (-a) ^ 1),
        ∀ z ≠ 0, f.val z = (thetaProductSection hτ hτ0 ha).val z ^ 1 * G.val z := by
      obtain ⟨G, hG⟩ := exists_holomorphic_quotient hτ0 (neg_ne_zero.mpr ha)
        f (thetaProductSection hτ hτ0 ha) 1 hzero
      refine ⟨⟨G.val, ?_⟩, hG⟩
      simpa only [Nat.cast_one, mul_one] using G.property
    refine ⟨G, automorphicSections_ext _ _ ?_⟩
    intro z hz
    exact (hG z hz).symm
theorem sectionEval_kernel_finrank {τ a γ : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hγ : γ ≠ 0) (n : ℤ) :
    Module.finrank ℂ (LinearMap.ker (sectionEval τ n γ a)) =
      Module.finrank ℂ (automorphicSections τ (n - 1) (γ / (-a))) := by
  rw [← pointThetaMultiply_range_eq_eval_kernel hτ hτ0 ha hγ n,
    LinearMap.finrank_range_of_inj (pointThetaMultiply_injective hτ hτ0 ha n γ 1)]
  rw [pow_one]
  rfl
end Nagata.W07
end
end
section
noncomputable section
namespace Nagata.W07
open Nagata.W08
end Nagata.W07
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W07
open Nagata.W08 Nagata.W21
def cubicEvaluationVector {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ)) (z : ℂ) : Fin 3 → ℂ :=
  fun i => (b i).val z
theorem cubic_basis_finrank {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ)) :
    Module.finrank ℂ (automorphicSections τ 3 γ) = 3 := by
  simpa using Module.finrank_eq_card_basis b
theorem cubicEvaluationVector_ne_zero {τ γ z : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ))
    (hker : Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2) :
    cubicEvaluationVector b z ≠ 0 := by
  intro hv
  obtain ⟨f, hf⟩ := cubic_exists_section_eval_one τ γ z (cubic_basis_finrank b) hker
  have heval : sectionEval τ 3 γ z = 0 := by
    apply b.ext
    intro i
    exact congrFun hv i
  have hf0 : f.val z = 0 := congrArg (fun L : automorphicSections τ 3 γ →ₗ[ℂ] ℂ => L f) heval
  exact one_ne_zero (hf.symm.trans hf0)
def cubicCoverMap {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2)
    (z : ℂˣ) : Projectivization ℂ (Fin 3 → ℂ) :=
  Projectivization.mk ℂ (cubicEvaluationVector b (z : ℂ))
    (cubicEvaluationVector_ne_zero b (hbase z z.ne_zero))
theorem cubicCoverMap_period (τ : ℂˣ) {γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections (τ : ℂ) 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2)
    (z : ℂˣ) : cubicCoverMap b hbase (τ * z) = cubicCoverMap b hbase z := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨γ * (z : ℂ) ^ (-3 : ℤ), ?_⟩
  funext i
  exact ((b i).property.2.2 (z : ℂ) z.ne_zero).symm
theorem cubicCoverMap_zpow (τ : ℂˣ) {γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections (τ : ℂ) 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2)
    (z : ℂˣ) (k : ℤ) :
    cubicCoverMap b hbase (τ ^ k * z) = cubicCoverMap b hbase z := by
  have he : (fun k : ℤ => cubicCoverMap b hbase (τ ^ k * z)) =
      (fun _ : ℤ => cubicCoverMap b hbase z) := by
    apply Nagata.W08.biInfinite_unique (fun _ x => x)
    · intro _ _ _ h
      exact h
    · intro j
      rw [zpow_add, zpow_one, mul_comm (τ ^ j) τ, mul_assoc]
      exact cubicCoverMap_period τ b hbase (τ ^ j * z)
    · intro _
      rfl
    · simp
  exact congrFun he k
def cubicTorusMap (τ : ℂˣ) {γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections (τ : ℂ) 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2) :
    TorusPoint τ → Projectivization ℂ (Fin 3 → ℂ) :=
  Quotient.lift (cubicCoverMap b hbase) (by
    intro z w h
    obtain ⟨k, rfl⟩ := h
    exact (cubicCoverMap_zpow τ b hbase z k).symm)
end Nagata.W07
end
end
section
noncomputable section
namespace Nagata.W07
open Nagata.W08 Nagata.W21
theorem cubic_eval_kernel_dimension {τ γ z : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hγ : γ ≠ 0) (hz : z ≠ 0)
    (h2 : ∀ δ : ℂ, δ ≠ 0 → Module.finrank ℂ (automorphicSections τ 2 δ) = 2) :
    Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2 := by
  rw [sectionEval_kernel_finrank hτ hτ0 hz hγ 3]
  exact h2 _ (div_ne_zero hγ (neg_ne_zero.mpr hz))
end Nagata.W07
end
end
section
noncomputable section
namespace Nagata.W07
open Nagata.W08
end Nagata.W07
end
end
section
noncomputable section
namespace Nagata.W07
open Nagata.W08 Nagata.ProjectiveGeometry
end Nagata.W07
end
end
section
noncomputable section
namespace Nagata.W07
open Nagata.W08 Nagata.ProjectiveGeometry
end Nagata.W07
end
end
section
noncomputable section
namespace Nagata.W07
open Nagata.W08 Nagata.ProjectiveGeometry
end Nagata.W07
end
end
section
noncomputable section
namespace Nagata.W07
open Nagata.W08 Nagata.W21 Nagata.ProjectiveGeometry
def cubicPeriod {τ : ℝ} (hτ : 0 < τ) : ℂˣ :=
  Units.mk0 (τ : ℂ) (by exact_mod_cast ne_of_gt hτ)
theorem realPeriod_norm_lt_one {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) :
    ‖(τ : ℂ)‖ < 1 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ] using hτone
theorem actualPositiveSection_finrank {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {n : ℤ} (hn : 0 < n) {γ : ℂ} (hγ : γ ≠ 0) :
    Module.finrank ℂ (automorphicSections (τ : ℂ) n γ) = n.toNat :=
  Nagata.Workers.W10.positiveSection_finrank hτ hτone
    (fun n γ => Nagata.W01.laurentCoefficientMap_injective _ n γ) hn hγ
def actualCubicBasis {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) :
    Module.Basis (Fin 3) ℂ (automorphicSections (τ : ℂ) 3 γ) :=
  Nagata.Workers.W10.positiveSectionBasisFin hτ hτone
    (fun n γ => Nagata.W01.laurentCoefficientMap_injective _ n γ)
    (show (0 : ℤ) < 3 by decide) hγ
theorem actualCubic_eval_kernel_dimension {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (sectionEval (τ : ℂ) 3 γ z)) = 2 :=
  cubic_eval_kernel_dimension (realPeriod_norm_lt_one hτ hτone)
    (cubicPeriod hτ).ne_zero hγ hz
    (fun _ hd => actualPositiveSection_finrank hτ hτone (by decide) hd)
def actualCubicMap {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) : TorusPoint (cubicPeriod hτ) → PlanePoint :=
  cubicTorusMap (cubicPeriod hτ) (actualCubicBasis hτ hτone hγ)
    (fun _ hz => actualCubic_eval_kernel_dimension hτ hτone hγ hz)
end Nagata.W07
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W02
end Nagata.W02
end
end
section
noncomputable section
namespace Nagata.W02
end Nagata.W02
end
end
section
noncomputable section
namespace Nagata.W02
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
end Nagata.W02
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W21
instance projectivizationTopologicalSpace (K V : Type*) [DivisionRing K]
    [AddCommGroup V] [Module K V] [TopologicalSpace V] :
    TopologicalSpace (Projectivization K V) :=
  inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid K V)))
theorem continuous_projectivization_mk' (K V : Type*) [DivisionRing K]
    [AddCommGroup V] [Module K V] [TopologicalSpace V] :
    Continuous (Projectivization.mk' K : {v : V // v ≠ 0} → Projectivization K V) :=
  continuous_quotient_mk'
theorem isQuotientMap_projectivization_mk' (K V : Type*) [DivisionRing K]
    [AddCommGroup V] [Module K V] [TopologicalSpace V] :
    Topology.IsQuotientMap (Projectivization.mk' K : {v : V // v ≠ 0} → Projectivization K V) :=
  isQuotientMap_quotient_mk'
end Nagata.W21
end
section
noncomputable section
open Topology Set
namespace Nagata.Workers.W11
variable {ι : Type*}
theorem projectivization_mk'_eq_iff_minors
    (v w : {x : ι → ℂ // x ≠ 0}) :
    Projectivization.mk' ℂ v = Projectivization.mk' ℂ w ↔
      ∀ i j, v.val i * w.val j = v.val j * w.val i := by
  rw [Projectivization.mk'_eq_mk, Projectivization.mk'_eq_mk,
    Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨a, ha⟩ i j
    have hi := congrFun ha i
    have hj := congrFun ha j
    change a * w.val i = v.val i at hi
    change a * w.val j = v.val j at hj
    rw [← hi, ← hj]
    ring
  · intro h
    have hn : ∃ i, w.val i ≠ 0 := by
      by_contra hn
      apply w.property
      funext i
      exact not_not.mp (fun hi => hn ⟨i, hi⟩)
    obtain ⟨i, hi⟩ := hn
    refine ⟨v.val i / w.val i, ?_⟩
    funext j
    change v.val i / w.val i * w.val j = v.val j
    rw [div_mul_eq_mul_div, div_eq_iff hi]
    exact h i j
theorem isClosed_projectivization_relation :
    IsClosed {p : {x : ι → ℂ // x ≠ 0} × {x : ι → ℂ // x ≠ 0} |
      Projectivization.mk' ℂ p.1 = Projectivization.mk' ℂ p.2} := by
  have heq : {p : {x : ι → ℂ // x ≠ 0} × {x : ι → ℂ // x ≠ 0} |
      Projectivization.mk' ℂ p.1 = Projectivization.mk' ℂ p.2} =
      ⋂ i, ⋂ j, {p | p.1.val i * p.2.val j = p.1.val j * p.2.val i} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter]
    exact projectivization_mk'_eq_iff_minors p.1 p.2
  rw [heq]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply isClosed_eq
  · exact (((continuous_apply i).comp continuous_subtype_val).comp continuous_fst).mul
      (((continuous_apply j).comp continuous_subtype_val).comp continuous_snd)
  · exact (((continuous_apply j).comp continuous_subtype_val).comp continuous_fst).mul
      (((continuous_apply i).comp continuous_subtype_val).comp continuous_snd)
def scaleNonzeroVector (a : ℂˣ) (v : {x : ι → ℂ // x ≠ 0}) :
    {x : ι → ℂ // x ≠ 0} :=
  ⟨(a : ℂ) • v.val, smul_ne_zero (Units.ne_zero a) v.property⟩
theorem continuous_scaleNonzeroVector (a : ℂˣ) :
    Continuous (scaleNonzeroVector (ι := ι) a) := by
  exact (continuous_const_smul (a : ℂ)).comp continuous_subtype_val |>.subtype_mk _
theorem isOpenMap_projectivization_mk' :
    IsOpenMap (Projectivization.mk' ℂ : {x : ι → ℂ // x ≠ 0} →
      Projectivization ℂ (ι → ℂ)) := by
  intro U hU
  apply (Nagata.W21.isQuotientMap_projectivization_mk' ℂ (ι → ℂ)).isOpen_preimage.mp
  have heq : (Projectivization.mk' ℂ) ⁻¹' (Projectivization.mk' ℂ '' U) =
      ⋃ a : ℂˣ, scaleNonzeroVector a ⁻¹' U := by
    ext v
    constructor
    · rintro ⟨u, hu, huv⟩
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ u.val v.val
        u.property v.property).mp huv
      apply mem_iUnion.mpr
      refine ⟨a, ?_⟩
      have hs : scaleNonzeroVector a v = u := Subtype.ext ha
      simpa only [mem_preimage, hs] using hu
    · intro hv
      obtain ⟨a, ha⟩ := mem_iUnion.mp hv
      refine ⟨scaleNonzeroVector a v, ha, ?_⟩
      apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr
      exact ⟨a, rfl⟩
  rw [heq]
  exact isOpen_iUnion fun a => hU.preimage (continuous_scaleNonzeroVector a)
theorem isOpenQuotientMap_projectivization_mk' :
    IsOpenQuotientMap (Projectivization.mk' ℂ : {x : ι → ℂ // x ≠ 0} →
      Projectivization ℂ (ι → ℂ)) :=
  ⟨(Nagata.W21.isQuotientMap_projectivization_mk' ℂ (ι → ℂ)).surjective,
    Nagata.W21.continuous_projectivization_mk' ℂ (ι → ℂ),
    isOpenMap_projectivization_mk'⟩
instance complexProjectivizationT2Space (ι : Type*) :
    T2Space (Projectivization ℂ (ι → ℂ)) :=
  (t2Space_iff_of_isOpenQuotientMap
    (isOpenQuotientMap_projectivization_mk' (ι := ι))).mpr
      isClosed_projectivization_relation
end Nagata.Workers.W11
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W21
open scoped BigOperators
open Nagata.W08
end Nagata.W21
end
section
namespace Nagata.W21
open Nagata.W08
end Nagata.W21
end
section
namespace Nagata.W21
open Nagata.W07 Nagata.W08
 theorem continuous_cubicEvaluationVector {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ)) :
    Continuous (fun z : ℂˣ ↦ cubicEvaluationVector b (z : ℂ)) := by
  apply continuous_pi
  intro i
  apply continuous_iff_continuousAt.mpr
  intro z
  exact ((b i).property.2.1 (z : ℂ) z.ne_zero).continuousAt.comp
    Units.continuous_val.continuousAt
theorem continuous_cubicCoverMap {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections τ 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2) :
    Continuous (cubicCoverMap b hbase) := by
  have hc : Continuous (fun z : ℂˣ ↦
      (⟨cubicEvaluationVector b (z : ℂ),
        cubicEvaluationVector_ne_zero b (hbase z z.ne_zero)⟩ :
        {v : Fin 3 → ℂ // v ≠ 0})) :=
    (continuous_cubicEvaluationVector b).subtype_mk _
  exact (continuous_projectivization_mk' ℂ (Fin 3 → ℂ)).comp hc
theorem continuous_cubicTorusMap (τ : ℂˣ) {γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (automorphicSections (τ : ℂ) 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sectionEval τ 3 γ z)) = 2) :
    Continuous (cubicTorusMap τ b hbase) :=
  (continuous_cubicCoverMap b hbase).quotient_lift _
end Nagata.W21
end
section
namespace Nagata.W21
open Nagata.W07 Nagata.W08 Nagata.W16
end Nagata.W21
end
section
noncomputable section
namespace Nagata.W21
open Nagata.W07 Nagata.W08 Nagata.W16
open scoped BigOperators
end Nagata.W21
end
end
section
namespace Nagata.W21
open Nagata.W07 Nagata.W08 Nagata.Workers.W05
end Nagata.W21
end
section
noncomputable section
namespace Nagata.W21
open Nagata.W07 Nagata.W08 Nagata.W16
 theorem continuous_actualCubicMap {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) : Continuous (actualCubicMap hτ hτone hγ) :=
  continuous_cubicTorusMap _ _ _
end Nagata.W21
end
end
section
namespace Nagata.W21
open Nagata.W07 Nagata.W08 Nagata.W16
 theorem cubic_gradient_scale_iff (G : MvPolynomial (Fin 3) ℂ)
    (hG : G.IsHomogeneous 3) (x : Fin 3 → ℂ) (u : ℂ) (hu : u ≠ 0) :
    (∃ i, MvPolynomial.eval (u • x) (MvPolynomial.pderiv i G) ≠ 0) ↔
      ∃ i, MvPolynomial.eval x (MvPolynomial.pderiv i G) ≠ 0 := by
  have he (i : Fin 3) :
      MvPolynomial.eval (u • x) (MvPolynomial.pderiv i G) =
        u ^ 2 * MvPolynomial.eval x (MvPolynomial.pderiv i G) := by
    exact homogeneous_eval_scale (show (MvPolynomial.pderiv i G).IsHomogeneous 2 from hG.pderiv) x u
  simp only [he, ne_eq, mul_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0), hu,
    false_or]
 theorem cubic_gradient_mk_rep_iff (G : MvPolynomial (Fin 3) ℂ)
    (hG : G.IsHomogeneous 3) (x : Fin 3 → ℂ) (hx : x ≠ 0) :
    (∃ i, MvPolynomial.eval (Projectivization.mk ℂ x hx).rep
      (MvPolynomial.pderiv i G) ≠ 0) ↔
      ∃ i, MvPolynomial.eval x (MvPolynomial.pderiv i G) ≠ 0 := by
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℂ x hx
  rw [← hu]
  exact cubic_gradient_scale_iff G hG x (u : ℂ) u.ne_zero
 theorem actualCubicMap_gradient_iff {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) (G : MvPolynomial (Fin 3) ℂ)
    (hG : G.IsHomogeneous 3) (z : ℂˣ) :
    (∃ i, MvPolynomial.eval
      (actualCubicMap hτ hτone hγ (torusPointMk (cubicPeriod hτ) z)).rep
      (MvPolynomial.pderiv i G) ≠ 0) ↔
      ∃ i, MvPolynomial.eval (cubicEvaluationVector (actualCubicBasis hτ hτone hγ) z)
        (MvPolynomial.pderiv i G) ≠ 0 :=
  cubic_gradient_mk_rep_iff G hG _ _
end Nagata.W21
end
section
noncomputable section
namespace Nagata.W21
open Nagata.W07 Nagata.W08 Nagata.ProjectiveGeometry
end Nagata.W21
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W25
end Nagata.Workers.W25
end
end
section
namespace Nagata.Workers.W25
end Nagata.Workers.W25
end
section
namespace Nagata.Workers.W25
end Nagata.Workers.W25
end
section
namespace Nagata.Workers.W25
end Nagata.Workers.W25
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W17
end Nagata.Workers.W17
end
end
section
noncomputable section
namespace Nagata.Workers.W17
variable {σ : Type*}
end Nagata.Workers.W17
end
end
section
noncomputable section
namespace Nagata.Workers.W17
open scoped BigOperators
end Nagata.Workers.W17
end
end
section
namespace Nagata.Workers.W17
end Nagata.Workers.W17
end
section
noncomputable section
namespace Nagata.Workers.W17
open Nagata.Workers.W28
end Nagata.Workers.W17
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.CoefficientSpaces
open Nagata.Workers.W28
end Nagata.CoefficientSpaces
end
section
namespace Nagata.CoefficientSpaces
open Nagata.Workers.W17 Nagata.Workers.W28 Filter Topology
end Nagata.CoefficientSpaces
end
section
namespace Nagata.CoefficientSpaces
open Filter Topology
end Nagata.CoefficientSpaces
end
section
namespace Nagata.CoefficientSpaces
open scoped BigOperators
open Nagata.W21 Filter Topology
theorem finite_product_finite_order {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ) (z : ℂ)
    (ha : ∀ i ∈ S, AnalyticAt ℂ (f i) z)
    (hf : ∀ i ∈ S, analyticOrderAt (f i) z ≠ ⊤) :
    AnalyticAt ℂ (fun w => ∏ i ∈ S, f i w) z ∧
      analyticOrderAt (fun w => ∏ i ∈ S, f i w) z ≠ ⊤ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      have hc : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) z := analyticAt_const
      simpa only [Finset.prod_empty] using And.intro hc
        (by rw [hc.analyticOrderAt_eq_zero.mpr one_ne_zero]; simp)
  | @insert i S hi ih =>
      have hai := ha i (Finset.mem_insert_self _ _)
      have hfi := hf i (Finset.mem_insert_self _ _)
      have ht := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
        (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      have he : (fun w => ∏ j ∈ insert i S, f j w) = f i * (fun w => ∏ j ∈ S, f j w) := by
        funext w
        simp only [Finset.prod_insert hi, Pi.mul_apply]
      rw [he]
      refine ⟨hai.mul ht.1, ?_⟩
      rw [analyticOrderAt_mul hai ht.1]
      exact WithTop.add_ne_top.mpr ⟨hfi, ht.2⟩
theorem shiftedTheta_finite_order {τ a z : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0)
    (ha : a ≠ 0) (hz : z ≠ 0) :
    AnalyticAt ℂ (fun w => thetaProduct τ (w / a)) z ∧
      analyticOrderAt (fun w => thetaProduct τ (w / a)) z ≠ ⊤ := by
  have hd : DifferentiableOn ℂ (fun w => thetaProduct τ (w / a)) {w : ℂ | w ≠ 0} :=
    fun w hw => (thetaProduct_scaled_differentiableAt hτ ha hw).differentiableWithinAt
  have han := hd.analyticAt (isOpen_ne.mem_nhds hz)
  refine ⟨han, ?_⟩
  by_cases hf : thetaProduct τ (z / a) = 0
  · rw [han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hf
      (thetaProduct_scaled_zero_has_nonzero_deriv hτ hτ0 ha hz hf)]
    simp
  · rw [han.analyticOrderAt_eq_zero.mpr hf]
    simp
theorem markedThetaSection_finite_order {ι : Type*} [Fintype ι]
    {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    {z : ℂ} (hz : z ≠ 0) :
    analyticOrderAt (Nagata.W08.markedThetaSection hτ hτ0 a ha).val z ≠ ⊤ := by
  change analyticOrderAt (Nagata.W08.normalizeAtZero (markedThetaProduct τ a)) z ≠ ⊤
  rw [analyticOrderAt_congr (Nagata.W08.normalizeAtZero_eventuallyEq (markedThetaProduct τ a) hz)]
  exact (finite_product_finite_order Finset.univ (fun i w => thetaProduct τ (w / a i)) z
    (fun i _ => (shiftedTheta_finite_order hτ hτ0 (ha i) hz).1)
    (fun i _ => (shiftedTheta_finite_order hτ hτ0 (ha i) hz).2)).2
theorem rayMarkedSection_analyticOnNhd {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (ξ : Fin 9 → ℝ) :
    AnalyticOnNhd ℂ (Nagata.W22.rayMarkedSection hτ hτone ξ).val {z : ℂ | z ≠ 0} :=
  Nagata.W08.automorphicSection_analyticOnNhd _
theorem rayMarkedSection_finite_order {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (ξ : Fin 9 → ℝ) {z : ℂ} (hz : z ≠ 0) :
    analyticOrderAt (Nagata.W22.rayMarkedSection hτ hτone ξ).val z ≠ ⊤ :=
  markedThetaSection_finite_order _ _ _ _ hz
end Nagata.CoefficientSpaces
end
section
namespace Nagata.CoefficientSpaces
open scoped BigOperators
end Nagata.CoefficientSpaces
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Module Filter Topology
namespace Nagata.Workers.W12
open Nagata.Workers.W10 Nagata.W20 Nagata.Workers.W11 Nagata.FiniteExponents Nagata.W22
variable (τ : ℝ) (γL γP : ℂ) (d : ℤ) (m : ℕ) (a delta : ℝ)
  (marks : Fin 9 → ℝ) (P : ℂ → ℂ) (z0 : ℂ)
  (hd : 3 * (m : ℤ) < d)
  (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
  (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤)
  (b : ∀ j : Fin ((d / 3).toNat + 1),
    Basis (ColumnFiber d (m : ℤ) a delta (j.val : ℤ)) ℂ
      (sourceBlock (τ : ℂ) γL γP d (m : ℤ) (j.val : ℤ)))
  (hblock : ∀ (j : Fin ((d / 3).toNat + 1))
      (K : ColumnFiber d (m : ℤ) a delta (j.val : ℤ)) (x : ℂ),
    (b j K).val (z0 * Complex.exp x) =
      if (j.val : ℤ) ≤ (m : ℤ) then
        normalizedThetaSeries (commonDegree d (m : ℤ) : ℝ)
          ((K.val : ℝ) - firstLower d (m : ℤ) (j.val : ℤ) a delta)
          (K.val : ℝ) ((-1 : ℂ) ^ ((m : ℤ) - (j.val : ℤ))) τ x
      else if 0 < d - 3 * (j.val : ℤ) then
        normalizedThetaSeries (sourceDegree d (j.val : ℤ) : ℝ)
          ((K.val : ℝ) - secondLower d (j.val : ℤ) a delta) (K.val : ℝ) 1 τ x
      else 1)
  (hPi : ∀ x : ℂ, P (z0 * Complex.exp x) = markedPi marks τ x)
include hblock hPi
theorem sourceBasis_localScalar_eq_theta
    (col : Column d (m : ℤ) a delta) (x y : ℂ) :
    localScalar (polynomialBasisFromSourceBases (τ : ℂ) γL γP d m a delta P
      hd hP hPfin b col) z0 x y =
      basisCoefficient d (m : ℤ) a delta marks τ col x *
        Complex.exp ((col.val.1 : ℂ) * y) := by
  obtain ⟨⟨j, K⟩, rfl⟩ := (columnFiberEquiv d (m : ℤ) a delta
    (Int.natCast_nonneg m) hd).surjective col
  rw [polynomialBasisFromSourceBases_local, hblock, hPi]
  change _ = basisCoefficient d (m : ℤ) a delta marks τ
    ⟨((j.val : ℤ), K.val), K.property⟩ x * Complex.exp ((j.val : ℂ) * y)
  simp only [basisCoefficient]
  split_ifs <;> simp_all [multipliedThetaCoefficient]
end Nagata.Workers.W12
end
end
section
noncomputable section
open Filter Topology
open scoped BigOperators
namespace Nagata.Workers.W12
open Nagata.Workers.W11 Nagata.Workers.W30 Nagata.FiniteExponents Nagata.W29
theorem source_coefficient_bridge_contradiction
    (r d m : ℕ) (hr : 10 ≤ r) (hm : 0 < m)
    (hlow : 3 < (d : ℝ) / m) (hupp : (d : ℝ) / m < Real.sqrt r)
    (hbridge : ∀ (n : ℕ) (delta : ℝ) (x : Fin 9 → ℝ),
      0 < n → 0 < delta → delta < 1 / 2 → Function.Injective x →
      (∀ i, 0 < x i ∧ x i < 1 / 2) →
      (∑ i : Fin 9, sourceOffsets x i) = delta →
      (∀ j : ℤ, 0 ≤ j → j ≤ ((n * m : ℕ) : ℤ) →
        firstLower ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ) j
          (3 * (Real.sqrt r - 3)) delta ∉ Set.range (Int.cast : ℤ → ℝ)) →
      (∀ j : ℤ, ((n * m : ℕ) : ℤ) < j → j ≤ ((n * d : ℕ) : ℤ) / 3 →
        0 < ((n * d : ℕ) : ℤ) - 3 * j →
        secondLower ((n * d : ℕ) : ℤ) j
          (3 * (Real.sqrt r - 3)) delta ∉ Set.range (Int.cast : ℤ → ℝ)) →
      (exponentSet ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
        (3 * (Real.sqrt r - 3)) delta).Nonempty →
      ∀ᶠ τ in 𝓝[>] (0 : ℝ),
        ∃ c : Column ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
          (3 * (Real.sqrt r - 3)) delta → ℂ,
          c ≠ 0 ∧ (thetaJetMatrix ((n * d : ℕ) : ℤ) (r - 9) (n * m)
            (3 * (Real.sqrt r - 3)) delta (sourceOffsets x) τ).mulVec c = 0) :
    False := by
  obtain ⟨n, delta, x, hn, hd0, hdhalf, hxinj, hxbounds, hxsum,
    hfirst, hsecond, hnonempty, hinj⟩ :=
    exists_scaled_thetaJetMatrix_source_data r d m hr hm hlow hupp
  exact coefficient_kernel_contradiction ((n * d : ℕ) : ℤ) (r - 9) (n * m)
    (3 * (Real.sqrt r - 3)) delta
    (thetaJetMatrix ((n * d : ℕ) : ℤ) (r - 9) (n * m)
      (3 * (Real.sqrt r - 3)) delta (sourceOffsets x)) hinj
    (hbridge n delta x hn hd0 hdhalf hxinj hxbounds hxsum hfirst hsecond hnonempty)
end Nagata.Workers.W12
end
end
section
noncomputable section
open Filter Topology Module
open scoped BigOperators
namespace Nagata.Workers.W12
open Nagata.W20 Nagata.Workers.W11 Nagata.Workers.W30 Nagata.FiniteExponents Nagata.W29
end Nagata.Workers.W12
end
end
section
noncomputable section
open Filter Topology Module
open scoped BigOperators
namespace Nagata.Workers.W12
open Nagata.W20 Nagata.Workers.W11 Nagata.Workers.W30 Nagata.FiniteExponents
open Nagata.W29
theorem source_actual_section_bridge_contradiction
    (r d m : ℕ) (hr : 10 ≤ r) (hm : 0 < m)
    (hlow : 3 < (d : ℝ) / m) (hupp : (d : ℝ) / m < Real.sqrt r)
    (hbridge : ∀ (n : ℕ) (delta : ℝ) (x : Fin 9 → ℝ),
      0 < n → 0 < delta → delta < 1 / 2 → Function.Injective x →
      (∀ i, 0 < x i ∧ x i < 1 / 2) →
      (∑ i : Fin 9, sourceOffsets x i) = delta →
      (∀ j : ℤ, 0 ≤ j → j ≤ ((n * m : ℕ) : ℤ) →
        firstLower ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ) j
          (3 * (Real.sqrt r - 3)) delta ∉ Set.range (Int.cast : ℤ → ℝ)) →
      (∀ j : ℤ, ((n * m : ℕ) : ℤ) < j → j ≤ ((n * d : ℕ) : ℤ) / 3 →
        0 < ((n * d : ℕ) : ℤ) - 3 * j →
        secondLower ((n * d : ℕ) : ℤ) j
          (3 * (Real.sqrt r - 3)) delta ∉ Set.range (Int.cast : ℤ → ℝ)) →
      (exponentSet ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
        (3 * (Real.sqrt r - 3)) delta).Nonempty →
      ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
        ∃ (gammaL gammaP z0 : ℂ) (P : ℂ → ℂ)
          (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z) (hz0 : z0 ≠ 0)
          (e : Basis (Column ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
            (3 * (Real.sqrt r - 3)) delta) ℂ
            (ActualSection (τ : ℂ) gammaL gammaP ((n * d : ℕ) : ℤ) (n * m) P))
          (F : ActualSection (τ : ℂ) gammaL gammaP ((n * d : ℕ) : ℤ) (n * m) P),
          (∀ col, ∀ᶠ z : ℂ × ℂ in 𝓝 (0, 0),
            localScalar (e col) z0 z.1 z.2 =
              Nagata.W22.basisCoefficient ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
                (3 * (Real.sqrt r - 3)) delta (sourceOffsets x) τ col z.1 *
                Complex.exp ((col.val.1 : ℂ) * z.2)) ∧
          F ≠ 0 ∧ actualJetMap hP hz0 (r - 9) F = 0) : False := by
  apply source_coefficient_bridge_contradiction r d m hr hm hlow hupp
  intro n delta x hn hd0 hdhalf hxinj hxbounds hxsum hfirst hsecond hnonempty
  apply (hbridge n delta x hn hd0 hdhalf hxinj hxbounds hxsum
    hfirst hsecond hnonempty).mono
  intro τ hτ
  obtain ⟨gammaL, gammaP, z0, P, hP, hz0, e, F, hlocal, hF, hjet⟩ := hτ
  have hmatrix := actual_basisJetMatrix_eq_of_local_expressions (q := r - 9) hP hz0 e
    (Nagata.W22.basisCoefficient ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
      (3 * (Real.sqrt r - 3)) delta (sourceOffsets x) τ) hlocal
  exact actual_kernel_to_coefficients hP hz0 e
    (thetaJetMatrix ((n * d : ℕ) : ℤ) (r - 9) (n * m)
      (3 * (Real.sqrt r - 3)) delta (sourceOffsets x) τ) hmatrix F hF hjet
theorem source_every_configuration_bridge_contradiction
    (r d m : ℕ) (hr : 10 ≤ r) (hm : 0 < m)
    (hlow : 3 < (d : ℝ) / m) (hupp : (d : ℝ) / m < Real.sqrt r)
    (hgeometry : ∀ (n : ℕ) (delta : ℝ) (x : Fin 9 → ℝ),
      0 < n → 0 < delta → delta < 1 / 2 → Function.Injective x →
      (∀ i, 0 < x i ∧ x i < 1 / 2) →
      (∑ i : Fin 9, sourceOffsets x i) = delta →
      (∀ j : ℤ, 0 ≤ j → j ≤ ((n * m : ℕ) : ℤ) →
        firstLower ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ) j
          (3 * (Real.sqrt r - 3)) delta ∉ Set.range (Int.cast : ℤ → ℝ)) →
      (∀ j : ℤ, ((n * m : ℕ) : ℤ) < j → j ≤ ((n * d : ℕ) : ℤ) / 3 →
        0 < ((n * d : ℕ) : ℤ) - 3 * j →
        secondLower ((n * d : ℕ) : ℤ) j
          (3 * (Real.sqrt r - 3)) delta ∉ Set.range (Int.cast : ℤ → ℝ)) →
      (exponentSet ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
        (3 * (Real.sqrt r - 3)) delta).Nonempty →
      ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
        ∃ (gammaL gammaP z0 : ℂ) (P : ℂ → ℂ)
          (_ : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z) (_ : z0 ≠ 0)
          (e : Basis (Column ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
            (3 * (Real.sqrt r - 3)) delta) ℂ
            (ActualSection (τ : ℂ) gammaL gammaP ((n * d : ℕ) : ℤ) (n * m) P))
          (U : Set ℂ),
          (∀ col, ∀ᶠ z : ℂ × ℂ in 𝓝 (0, 0),
            localScalar (e col) z0 z.1 z.2 =
              Nagata.W22.basisCoefficient ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
                (3 * (Real.sqrt r - 3)) delta (sourceOffsets x) τ col z.1 *
                Complex.exp ((col.val.1 : ℂ) * z.2)) ∧
          IsOpen U ∧ (0 : ℂ) ∈ U ∧
          (∀ p : Fin (r - 9) → ℂ, Function.Injective p → (∀ i, p i ∈ U) →
            ∃ F : ActualSection (τ : ℂ) gammaL gammaP ((n * d : ℕ) : ℤ) (n * m) P,
              F ≠ 0 ∧ ∀ i, Nagata.Workers.W28.HasAnalyticOrderAtLeast (𝕜 := ℂ)
                (fun z : ℂ × ℂ => localScalar F z0 z.1 z.2) (p i, 0) (n * m))) : False := by
  apply source_actual_section_bridge_contradiction r d m hr hm hlow hupp
  intro n delta x hn hd0 hdhalf hxinj hxbounds hxsum hfirst hsecond hnonempty
  apply (hgeometry n delta x hn hd0 hdhalf hxinj hxbounds hxsum
    hfirst hsecond hnonempty).mono
  intro τ hτ
  obtain ⟨gammaL, gammaP, z0, P, hP, hz0, e, U, hlocal, hU, h0, hEvery⟩ := hτ
  obtain ⟨F, hF, hker⟩ := actual_kernel_of_every_configuration hP hz0 e hU h0 hEvery
  exact ⟨gammaL, gammaP, z0, P, hP, hz0, e, F, hlocal, hF, hker⟩
end Nagata.Workers.W12
end
end
section
noncomputable section
open Module Filter Topology
open scoped BigOperators
namespace Nagata.Workers.W12
open Nagata.Workers.W10 Nagata.W20 Nagata.Workers.W11 Nagata.FiniteExponents
open Nagata.W22 Nagata.CoefficientSpaces
variable {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
  (ξ : Fin 9 → ℝ) (a delta x0 : ℝ) (d : ℤ) (m : ℕ)
  (hs : (∑ i, ξ i) = 9 * x0 - delta)
  (hd : 3 * (m : ℤ) < d)
  (hfirst : ∀ j : ℤ, 0 ≤ j → j ≤ (m : ℤ) →
    firstLower d (m : ℤ) j a delta ∉ Set.range (Int.cast : ℤ → ℝ))
  (hsecond : ∀ j : ℤ, (m : ℤ) < j → j ≤ d / 3 → 0 < d - 3 * j →
    secondLower d j a delta ∉ Set.range (Int.cast : ℤ → ℝ))
def genuineSourceSections :=
  ActualSection (τ : ℂ) (tauPower τ (((∑ i, ξ i) + a) / 3))
    (-tauPower τ (∑ i, ξ i)) d m (rayMarkedSection hτ hτone ξ).val
def genuineSourceBasis : Basis (Column d (m : ℤ) a delta) ℂ
    (genuineSourceSections hτ hτone ξ a d m) :=
  polynomialBasisFromSourceBases (τ : ℂ) (tauPower τ (((∑ i, ξ i) + a) / 3))
    (-tauPower τ (∑ i, ξ i)) d m a delta (rayMarkedSection hτ hτone ξ).val hd
    (rayMarkedSection_analyticOnNhd hτ hτone ξ)
    (fun _ hz => rayMarkedSection_finite_order hτ hτone ξ hz)
    (actualSourceBlockBases hτ hτone (∑ i, ξ i) a delta x0 d m hs hd hfirst hsecond)
theorem genuineSourceBasis_localScalar (col : Column d (m : ℤ) a delta) (x y : ℂ) :
    localScalar (genuineSourceBasis hτ hτone ξ a delta x0 d m hs hd hfirst hsecond col)
      (tauPower τ x0) x y =
      basisCoefficient d (m : ℤ) a delta (fun i => x0 - ξ i) τ col x *
        Complex.exp ((col.val.1 : ℂ) * y) := by
  apply sourceBasis_localScalar_eq_theta
  · exact actualSourceBlockBases_local hτ hτone (∑ i, ξ i) a delta x0 d m
      hs hd hfirst hsecond
  · exact rayMarkedSection_centered hτ hτone ξ x0
include hs hd hfirst hsecond
end Nagata.Workers.W12
end
end
section
noncomputable section
open Module Filter Topology
open scoped BigOperators
namespace Nagata.Workers.W12
open Nagata.Workers.W10 Nagata.W20 Nagata.Workers.W11 Nagata.FiniteExponents
open Nagata.W22 Nagata.CoefficientSpaces Nagata.W29
theorem genuine_source_geometric_contradiction
    (r d m : ℕ) (hr : 10 ≤ r) (hm : 0 < m)
    (hlow : 3 < (d : ℝ) / m) (hupp : (d : ℝ) / m < Real.sqrt r)
    (hgeometry : ∀ (n : ℕ) (delta : ℝ) (x : Fin 9 → ℝ),
      0 < n → 0 < delta → delta < 1 / 2 → Function.Injective x →
      (∀ i, 0 < x i ∧ x i < 1 / 2) →
      (∑ i : Fin 9, sourceOffsets x i) = delta →
      (∀ j : ℤ, 0 ≤ j → j ≤ ((n * m : ℕ) : ℤ) →
        firstLower ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ) j
          (3 * (Real.sqrt r - 3)) delta ∉ Set.range (Int.cast : ℤ → ℝ)) →
      (∀ j : ℤ, ((n * m : ℕ) : ℤ) < j → j ≤ ((n * d : ℕ) : ℤ) / 3 →
        0 < ((n * d : ℕ) : ℤ) - 3 * j →
        secondLower ((n * d : ℕ) : ℤ) j
          (3 * (Real.sqrt r - 3)) delta ∉ Set.range (Int.cast : ℤ → ℝ)) →
      (exponentSet ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
        (3 * (Real.sqrt r - 3)) delta).Nonempty →
      ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
        ∃ (hτ : 0 < τ) (hτone : τ < 1) (U : Set ℂ),
          IsOpen U ∧ (0 : ℂ) ∈ U ∧
          (∀ p : Fin (r - 9) → ℂ, Function.Injective p → (∀ i, p i ∈ U) →
            ∃ F : genuineSourceSections hτ hτone x (3 * (Real.sqrt r - 3))
                ((n * d : ℕ) : ℤ) (n * m),
              F ≠ 0 ∧ ∀ i, Nagata.Workers.W28.HasAnalyticOrderAtLeast (𝕜 := ℂ)
                (fun z : ℂ × ℂ => localScalar F (tauPower τ (1 / 2)) z.1 z.2)
                (p i, 0) (n * m))) : False := by
  apply source_every_configuration_bridge_contradiction r d m hr hm hlow hupp
  intro n delta x hn hd0 hdhalf hxinj hxbounds hxsum hfirst hsecond hnonempty
  have hs : (∑ i, x i) = 9 * (1 / 2 : ℝ) - delta := by
    have hh := hxsum
    simp only [sourceOffsets, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
    linarith
  have hdmreal : 3 * (m : ℝ) < d :=
    (lt_div_iff₀ (Nat.cast_pos.mpr hm)).mp hlow
  have hdm : 3 * m < d := by exact_mod_cast hdmreal
  have hscale : 3 * (n * m) < n * d := by
    calc
      3 * (n * m) = n * (3 * m) := by ring
      _ < n * d := Nat.mul_lt_mul_of_pos_left hdm hn
  have hd : 3 * (((n * m : ℕ) : ℤ)) < ((n * d : ℕ) : ℤ) := by
    exact_mod_cast hscale
  apply (hgeometry n delta x hn hd0 hdhalf hxinj hxbounds hxsum
    hfirst hsecond hnonempty).mono
  intro τ hdata
  obtain ⟨hτ, hτone, U, hU, h0, hEvery⟩ := hdata
  refine ⟨tauPower τ (((∑ i, x i) + 3 * (Real.sqrt r - 3)) / 3),
    -tauPower τ (∑ i, x i), tauPower τ (1 / 2),
    (rayMarkedSection hτ hτone x).val,
    (fun z hz => (rayMarkedSection_analyticOnNhd hτ hτone x z hz).differentiableAt),
    tauPower_ne_zero hτ (1 / 2),
    genuineSourceBasis hτ hτone x (3 * (Real.sqrt r - 3)) delta (1 / 2)
      ((n * d : ℕ) : ℤ) (n * m) hs hd hfirst hsecond,
    U, ?_, hU, h0, hEvery⟩
  intro col
  exact Filter.Eventually.of_forall (fun z =>
    genuineSourceBasis_localScalar hτ hτone x (3 * (Real.sqrt r - 3)) delta (1 / 2)
      ((n * d : ℕ) : ℤ) (n * m) hs hd hfirst hsecond col z.1 z.2)
end Nagata.Workers.W12
end
end
end OAI
end
open Filter Topology OAI.Nagata OAI.Nagata.Workers.W12 OAI.Nagata.CoefficientSpaces
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2400000 in
theorem OMA.solution : OMA.R_wp_nagata_s_conjecture_on_curves_R1_H3_R1.H2 := by
  intro r hr _ D M hm hl hu hh
  apply genuine_source_geometric_contradiction r D M hr hm hl hu
  intro n delta x hn hd0 hdhalf hx hb hs hf hsec he
  apply (hh n x hx hb).mono
  rintro t ⟨ht,ht1,U,hU,h0,h⟩
  refine ⟨ht,ht1,U,hU,h0,?_⟩
  intro p hp hpu
  obtain ⟨F,hF,hd,hc,hv⟩ := h p hp hpu
  have hmem : F ∈ genuineSourceSections ht ht1 x (3*(Real.sqrt r-3)) ((n*D : ℕ):ℤ) (n*M) := by
    refine ⟨hd,?_⟩
    intro j
    specialize hc j
    unfold coefficientSpace
    split <;> rename_i hj
    · rw [if_pos hj] at hc; exact hc
    · rw [if_neg hj] at hc; exact hc
  exact ⟨⟨F,hmem⟩,fun hz => hF (congrArg Subtype.val hz),hv⟩
