import OMAStatements.S_mo_327958
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/- For H congruent to 1 or 7 modulo 60, the minimum sums for (H,3,4,5)
   give different polynomial formulas after multiplication by H. -/

open scoped BigOperators

namespace OMA.Mo327958

def sliceVector (H : ℚ) : Fin 4 → ℚ := ![H, 3, 4, 5]

private noncomputable def sliceVars : Fin 4 → Polynomial ℚ :=
  ![Polynomial.X, Polynomial.C 3, Polynomial.C 4, Polynomial.C 5]

private noncomputable def slicePolynomial (p : MvPolynomial (Fin 4) ℚ) : Polynomial ℚ :=
  MvPolynomial.aeval sliceVars p

private lemma eval_slicePolynomial (p : MvPolynomial (Fin 4) ℚ) (H : ℚ) :
    (slicePolynomial p).eval H = MvPolynomial.eval (sliceVector H) p := by
  have hv : (fun i : Fin 4 => Polynomial.aeval H (sliceVars i)) = sliceVector H := by
    funext i
    fin_cases i <;> simp [sliceVars, sliceVector]
  rw [slicePolynomial, ← Polynomial.coe_aeval_eq_eval, MvPolynomial.comp_aeval_apply,
    MvPolynomial.aeval_eq_eval]
  exact congrArg (fun f : Fin 4 → ℚ => MvPolynomial.eval f p) hv

private lemma eq_of_progression_eval_eq (P Q : Polynomial ℚ) (r : ℚ)
    (h : ∀ k : ℕ, P.eval (60 * (k : ℚ) + r) = Q.eval (60 * (k : ℚ) + r)) : P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq P Q
  have hi : Function.Injective (fun k : ℕ => 60 * (k : ℚ) + r) := by
    intro i j hij
    have he : (i : ℚ) = j := by linarith
    exact_mod_cast he
  refine (Set.infinite_range_of_injective hi).mono ?_
  rintro _ ⟨k, rfl⟩
  exact h k

lemma noTwoProgressionIdentity (p q : MvPolynomial (Fin 4) ℚ) (A B : Polynomial ℚ)
    (hAB : A ≠ B) (hq : MvPolynomial.eval (sliceVector 1) q ≠ 0)
    (h1 : ∀ k : ℕ, let H : ℚ := 60 * (k : ℚ) + 1
      H * MvPolynomial.eval (sliceVector H) p = A.eval H * MvPolynomial.eval (sliceVector H) q)
    (h7 : ∀ k : ℕ, let H : ℚ := 60 * (k : ℚ) + 7
      H * MvPolynomial.eval (sliceVector H) p = B.eval H * MvPolynomial.eval (sliceVector H) q) :
    False := by
  have hq' : slicePolynomial q ≠ 0 := by
    intro h0
    apply hq
    rw [← eval_slicePolynomial, h0, Polynomial.eval_zero]
  have e1 : Polynomial.X * slicePolynomial p = A * slicePolynomial q := by
    apply eq_of_progression_eval_eq _ _ 1
    simpa only [Polynomial.eval_mul, Polynomial.eval_X, eval_slicePolynomial] using h1
  have e7 : Polynomial.X * slicePolynomial p = B * slicePolynomial q := by
    apply eq_of_progression_eval_eq _ _ 7
    simpa only [Polynomial.eval_mul, Polynomial.eval_X, eval_slicePolynomial] using h7
  exact hAB (mul_right_cancel₀ hq' (e1.symm.trans e7))

private theorem capped_sum (H q : ℕ) (c : ℚ) (hH : 0 < H) (hq : q < H)
    (hlo : (q : ℚ) ≤ (H : ℚ) * c) (hhi : (H : ℚ) * c ≤ (q : ℚ) + 1) :
    (∑ r ∈ Finset.range H, min ((r : ℚ) / H) c) =
      (q : ℚ) * ((q : ℚ) + 1) / (2 * H) + ((H : ℚ) - q - 1) * c := by
  have hH' : (0 : ℚ) < H := by exact_mod_cast hH
  have hdecomp : q + 1 + (H - (q + 1)) = H := by omega
  have hdecomp' : (q : ℚ) + 1 + ((H - (q + 1) : ℕ) : ℚ) = H := by
    exact_mod_cast hdecomp
  have hsmall (r : ℕ) (hr : r ∈ Finset.range (q + 1)) :
      min ((r : ℚ) / H) c = (r : ℚ) / H := by
    apply min_eq_left
    apply (div_le_iff₀ hH').2
    have hrq : r ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    rw [mul_comm c]
    exact (show (r : ℚ) ≤ q by exact_mod_cast hrq).trans hlo
  have hlarge (r : ℕ) : min (((q + 1 + r : ℕ) : ℚ) / H) c = c := by
    apply min_eq_right
    apply (le_div_iff₀ hH').2
    rw [mul_comm c]
    push_cast
    linarith only [hhi, Nat.cast_nonneg (α := ℚ) r]
  have hgaussN : (∑ r ∈ Finset.range (q + 1), r) * 2 = (q + 1) * q := by
    simpa using Finset.sum_range_id_mul_two (q + 1)
  have hgaussQ : (∑ r ∈ Finset.range (q + 1), (r : ℚ)) * 2 =
      ((q : ℚ) + 1) * (q : ℚ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, Nat.cast_sum] using
      congrArg (fun n : ℕ => (n : ℚ)) hgaussN
  have hfirst : (∑ r ∈ Finset.range (q + 1), (r : ℚ) / H) =
      (q : ℚ) * ((q : ℚ) + 1) / (2 * H) := by
    have hsum : (∑ r ∈ Finset.range (q + 1), (r : ℚ)) =
        (q : ℚ) * ((q : ℚ) + 1) / 2 := by linarith only [hgaussQ]
    calc
      _ = (∑ r ∈ Finset.range (q + 1), (r : ℚ)) / H := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
      _ = _ := by rw [hsum, div_div]
  calc
    _ = ∑ r ∈ Finset.range (q + 1 + (H - (q + 1))), min ((r : ℚ) / H) c := by
      rw [hdecomp]
    _ = (∑ r ∈ Finset.range (q + 1), (r : ℚ) / H) +
        ∑ _r ∈ Finset.range (H - (q + 1)), c := by
      rw [Finset.sum_range_add]
      congr 1
      · exact Finset.sum_congr rfl hsmall
      · exact Finset.sum_congr rfl fun r _ => hlarge r
    _ = _ := by
      rw [hfirst, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have ht : ((H - (q + 1) : ℕ) : ℚ) = (H : ℚ) - q - 1 := by
        linarith only [hdecomp']
      rw [ht]

private theorem scaled_capped_sum (k r u : ℕ) (hr : 0 < r) (hu : u < 60) :
    let H := 60 * k + r
    let c : ℚ := (u : ℚ) / 60
    let θ : ℚ := (↑(r * u % 60) : ℚ) / 60
    (H : ℚ) * (∑ x ∈ Finset.range H, min ((x : ℚ) / H) c) =
      (H : ℚ)^2 * (c - c^2 / 2) - (H : ℚ) * (c / 2) - θ * (1 - θ) / 2 := by
  intro H c θ
  let q := k * u + r * u / 60
  have hH : 0 < H := by
    dsimp [H]
    omega
  have hH' : (0 : ℚ) < H := by exact_mod_cast hH
  have hd : (↑(r * u % 60) : ℚ) + 60 * (↑(r * u / 60) : ℚ) = (r : ℚ) * u := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      congrArg (fun n : ℕ => (n : ℚ)) (Nat.mod_add_div (r * u) 60)
  have hqc : (q : ℚ) + θ = (H : ℚ) * c := by
    dsimp [q, θ, H, c]
    push_cast
    linear_combination hd / 60
  have hθ0 : 0 ≤ θ := div_nonneg (Nat.cast_nonneg _) (by norm_num)
  have hθ1 : θ < 1 := by
    apply (div_lt_iff₀ (by norm_num : (0 : ℚ) < 60)).2
    rw [one_mul]
    exact_mod_cast Nat.mod_lt (r * u) (by decide : 0 < 60)
  have hc1 : c < 1 := by
    apply (div_lt_iff₀ (by norm_num : (0 : ℚ) < 60)).2
    rw [one_mul]
    exact_mod_cast hu
  have hlo : (q : ℚ) ≤ (H : ℚ) * c := by linarith only [hqc, hθ0]
  have hhi : (H : ℚ) * c ≤ (q : ℚ) + 1 := by linarith only [hqc, hθ1]
  have hqc' : (H : ℚ) * c < H := by simpa using mul_lt_mul_of_pos_left hc1 hH'
  have hq : q < H := by exact_mod_cast hlo.trans_lt hqc'
  rw [capped_sum H q c hH hq hlo hhi]
  calc
    _ = (q : ℚ) * ((q : ℚ) + 1) / 2 + (H : ℚ) * ((H : ℚ) - q - 1) * c := by
      field_simp [ne_of_gt hH']
    _ = _ := by
      have hs : (q : ℚ) = (H : ℚ) * c - θ := by linarith only [hqc]
      rw [hs]
      ring

private def tailBounds : Fin 3 → ℕ := ![3, 4, 5]

private abbrev Tail := (i : Fin 3) → Fin (tailBounds i)

private def bounds (H : ℕ) : Fin 4 → ℕ := Fin.cons H tailBounds

private def capUnits (r : Tail) : ℕ :=
  min (20 * (r 0).val) (min (15 * (r 1).val) (12 * (r 2).val))

private def cap (r : Tail) : ℚ := (capUnits r : ℚ) / 60

private theorem inf_four (f : Fin 4 → ℚ) :
    Finset.univ.inf' Finset.univ_nonempty f = min (f 0) (min (f 1) (min (f 2) (f 3))) := by
  apply le_antisymm
  · exact le_min (Finset.inf'_le f (Finset.mem_univ 0))
      (le_min (Finset.inf'_le f (Finset.mem_univ 1))
        (le_min (Finset.inf'_le f (Finset.mem_univ 2)) (Finset.inf'_le f (Finset.mem_univ 3))))
  · apply Finset.le_inf'
    intro i _
    fin_cases i
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

private theorem cap_eq (r : Tail) :
    cap r = min (((r 0).val : ℚ) / 3)
      (min (((r 1).val : ℚ) / 4) (((r 2).val : ℚ) / 5)) := by
  unfold cap capUnits
  push_cast
  rw [← min_div_div_right (by norm_num : (0 : ℚ) ≤ 60),
    ← min_div_div_right (by norm_num : (0 : ℚ) ≤ 60)]
  have h₁ : (20 * ((r 0).val : ℚ)) / 60 = ((r 0).val : ℚ) / 3 := by ring
  have h₂ : (15 * ((r 1).val : ℚ)) / 60 = ((r 1).val : ℚ) / 4 := by ring
  have h₃ : (12 * ((r 2).val : ℚ)) / 60 = ((r 2).val : ℚ) / 5 := by ring
  rw [h₁, h₂, h₃]

private theorem sumMin_slice (H : ℕ) :
    S_mo_327958.sumMin (bounds H) =
      ∑ r : Tail, ∑ x ∈ Finset.range H, min ((x : ℚ) / H) (cap r) := by
  let e : (Fin H × Tail) ≃ ((i : Fin 4) → Fin (bounds H i)) :=
    Fin.consEquiv (fun i => Fin (bounds H i))
  unfold S_mo_327958.sumMin
  calc
    _ = ∑ z : Fin H × Tail, min ((z.1.val : ℚ) / H) (cap z.2) := by
      refine (Fintype.sum_equiv e _ _ ?_).symm
      intro z
      simp only [cap_eq, e, Fin.consEquiv]
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type_right]
      apply Finset.sum_congr rfl
      intro r _
      exact Fin.sum_univ_eq_sum_range (fun x : ℕ => min ((x : ℚ) / H) (cap r)) H

private theorem capUnits_lt (r : Tail) : capUnits r < 60 := by
  have h : (r 0).val < 3 := (r 0).isLt
  have hmin : capUnits r ≤ 20 * (r 0).val := min_le_left _ _
  omega

private def correction (residue : ℕ) (r : Tail) : ℚ :=
  let θ : ℚ := ((residue * capUnits r % 60 : ℕ) : ℚ) / 60
  θ * (1 - θ) / 2

set_option maxRecDepth 2048 in
private theorem cap_quadratic_sum :
    (∑ r : Tail, (cap r - cap r ^ 2 / 2)) = (22729 : ℚ) / 3600 := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem cap_linear_sum :
    (∑ r : Tail, cap r / 2) = (233 : ℚ) / 60 := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem correction_one :
    (∑ r : Tail, correction 1 r) = (8749 : ℚ) / 3600 := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem correction_seven :
    (∑ r : Tail, correction 7 r) = (9181 : ℚ) / 3600 := by
  decide +kernel

private theorem bounds_pos (H : ℕ) (hH : 0 < H) : ∀ i, 0 < bounds H i := by
  intro i
  fin_cases i
  · exact hH
  · exact (by decide : 0 < 3)
  · exact (by decide : 0 < 4)
  · exact (by decide : 0 < 5)

private theorem bounds_coprime (k s : ℕ) (h3 : s.Coprime 3)
    (h4 : s.Coprime 4) (h5 : s.Coprime 5) :
    Pairwise (fun i j => (bounds (60 * k + s) i).Coprime (bounds (60 * k + s) j)) := by
  have hH3 : (60 * k + s).Coprime 3 := by
    rw [show 60 * k + s = s + (20 * k) * 3 by omega]
    exact (Nat.coprime_add_mul_right_left s 3 (20 * k)).2 h3
  have hH4 : (60 * k + s).Coprime 4 := by
    rw [show 60 * k + s = s + (15 * k) * 4 by omega]
    exact (Nat.coprime_add_mul_right_left s 4 (15 * k)).2 h4
  have hH5 : (60 * k + s).Coprime 5 := by
    rw [show 60 * k + s = s + (12 * k) * 5 by omega]
    exact (Nat.coprime_add_mul_right_left s 5 (12 * k)).2 h5
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (hij rfl).elim
    | exact hH3
    | exact hH4
    | exact hH5
    | exact hH3.symm
    | exact hH4.symm
    | exact hH5.symm
    | exact (by decide : Nat.Coprime 3 4)
    | exact (by decide : Nat.Coprime 3 5)
    | exact (by decide : Nat.Coprime 4 5)
    | exact (by decide : Nat.Coprime 4 3)
    | exact (by decide : Nat.Coprime 5 3)
    | exact (by decide : Nat.Coprime 5 4)

private theorem scaled_sumMin (k s : ℕ) (hs : 0 < s) :
    let H := 60 * k + s
    (H : ℚ) * S_mo_327958.sumMin (bounds H) =
      (22729 : ℚ) / 3600 * (H : ℚ)^2 - (233 : ℚ) / 60 * (H : ℚ) -
        ∑ r : Tail, correction s r := by
  let H := 60 * k + s
  change (H : ℚ) * S_mo_327958.sumMin (bounds H) =
    (22729 : ℚ) / 3600 * (H : ℚ)^2 - (233 : ℚ) / 60 * (H : ℚ) -
      ∑ r : Tail, correction s r
  rw [sumMin_slice, Finset.mul_sum]
  calc
    _ = ∑ r : Tail, ((H : ℚ)^2 * (cap r - cap r^2 / 2) -
        (H : ℚ) * (cap r / 2) - correction s r) := by
      apply Finset.sum_congr rfl
      intro r _
      exact scaled_capped_sum k s (capUnits r) hs (capUnits_lt r)
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        cap_quadratic_sum, cap_linear_sum]
      ring

private noncomputable def sliceFormula (d : ℚ) : Polynomial ℚ :=
  Polynomial.C ((22729 : ℚ) / 3600) * Polynomial.X^2 -
    Polynomial.C ((233 : ℚ) / 60) * Polynomial.X - Polynomial.C d

private theorem sliceFormula_distinct :
    sliceFormula (8749 / 3600) ≠ sliceFormula (9181 / 3600) := by
  intro h
  have h0 := congrArg (Polynomial.eval 0) h
  norm_num [sliceFormula] at h0

private theorem bounds_cast (H : ℕ) :
    (fun i : Fin 4 => (bounds H i : ℚ)) = sliceVector (H : ℚ) := by
  funext i
  fin_cases i <;> rfl

end OMA.Mo327958

open OMA.Mo327958

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_327958.main) := by
  intro h
  obtain ⟨p, q, pMax, qMax, h⟩ := h 3
  have eval_on_slice (k s : ℕ) (hs : 0 < s) (h3 : s.Coprime 3)
      (h4 : s.Coprime 4) (h5 : s.Coprime 5) :
      let H := 60 * k + s
      MvPolynomial.eval (sliceVector (H : ℚ)) q ≠ 0 ∧
        MvPolynomial.eval (sliceVector (H : ℚ)) p =
          OMA.S_mo_327958.sumMin (bounds H) * MvPolynomial.eval (sliceVector (H : ℚ)) q := by
    let H := 60 * k + s
    have hpos : 0 < H := by omega
    obtain ⟨hq, _, hmin, _⟩ := h (bounds H) (bounds_pos H hpos) (bounds_coprime k s h3 h4 h5)
    rw [bounds_cast H] at hq hmin
    exact ⟨hq, ((eq_div_iff hq).mp hmin).symm⟩
  refine noTwoProgressionIdentity p q (sliceFormula (8749 / 3600)) (sliceFormula (9181 / 3600))
    sliceFormula_distinct (eval_on_slice 0 1 (by decide) (by decide) (by decide) (by decide)).1 ?_ ?_
  · intro k
    have hscaled := scaled_sumMin k 1 (by decide)
    have hval := (eval_on_slice k 1 (by decide) (by decide) (by decide) (by decide)).2
    dsimp only at hscaled hval ⊢
    rw [correction_one] at hscaled
    push_cast at hscaled hval
    rw [hval, ← mul_assoc, hscaled]
    simp [sliceFormula]
  · intro k
    have hscaled := scaled_sumMin k 7 (by decide)
    have hval := (eval_on_slice k 7 (by decide) (by decide) (by decide) (by decide)).2
    dsimp only at hscaled hval ⊢
    rw [correction_seven] at hscaled
    push_cast at hscaled hval
    rw [hval, ← mul_assoc, hscaled]
    simp [sliceFormula]
