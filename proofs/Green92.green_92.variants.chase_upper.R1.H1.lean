import OMAReductions.R_Green92_green_92_variants_chase_upper_R1
import Mathlib

/-!
# Chase's Upper Bound for Trace Reconstruction (Amplified Pairwise Tests)

This file proves `OMA.R_Green92_green_92_variants_chase_upper_R1.H1`, establishing Chase's
`exp(C * n^(1/5) * (log n)^5)` upper bound for amplified pairwise tests under the `1/2`-deletion
channel.
-/

namespace Green92ChaseH1

open Finset Filter Real Complex
open scoped Classical BigOperators Topology

/- ### Section 1: Hoeffding's Inequality on Finite Product Spaces -/

private lemma cosh_le_exp_half_sq (x : ℝ) : Real.cosh x ≤ Real.exp (x ^ 2 / 2) := by
  suffices h : ∀ t : ℝ, 0 ≤ t → Real.cosh t ≤ Real.exp (t ^ 2 / 2) by
    rcases le_total 0 x with hx | hx
    · exact h x hx
    · simpa [Real.cosh_neg] using h (-x) (neg_nonneg.mpr hx)
  intro t ht
  have h1 : ∀ u : ℝ, 0 ≤ u → Real.sinh u ≤ u * Real.cosh u := by
    intro u hu
    let f : ℝ → ℝ := fun s => s * Real.cosh s - Real.sinh s
    have hf0 : f 0 = 0 := by simp [f]
    have hmono : MonotoneOn f (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact ((continuous_id.mul Real.continuous_cosh).sub Real.continuous_sinh).continuousOn
      · exact fun s _ =>
          (((hasDerivAt_id s).mul (Real.hasDerivAt_cosh s)).sub
            (Real.hasDerivAt_sinh s)).differentiableAt.differentiableWithinAt
      · intro s hs
        have hd : HasDerivAt f (s * Real.sinh s) s := by
          have h0 := ((hasDerivAt_id s).mul (Real.hasDerivAt_cosh s)).sub (Real.hasDerivAt_sinh s)
          dsimp only [id_eq] at h0
          have heq : 1 * Real.cosh s + s * Real.sinh s - Real.cosh s = s * Real.sinh s := by ring
          rwa [heq] at h0
        rw [hd.deriv]
        exact mul_nonneg (le_of_lt (by simpa using hs))
          (Real.sinh_nonneg_iff.mpr (le_of_lt (by simpa using hs)))
    have := hmono (Set.self_mem_Ici) hu hu
    simp only [f, hf0] at this
    linarith
  let g : ℝ → ℝ := fun s => Real.exp (-(s ^ 2 / 2)) * Real.cosh s
  have hg0 : g 0 = 1 := by simp [g]
  have hderiv_exp : ∀ s : ℝ, HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-s) s := fun s => by
    have h0 := ((hasDerivAt_pow 2 s).div_const 2).neg
    have heq : -((2 : ℕ) * s ^ (2 - 1) / 2) = -s := by norm_num
    rwa [heq] at h0
  have hanti : AntitoneOn g (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact ((Real.continuous_exp.comp
        ((continuous_pow 2).div_const 2).neg).mul Real.continuous_cosh).continuousOn
    · intro s _
      exact (((hderiv_exp s).exp).mul (Real.hasDerivAt_cosh s)).differentiableAt.differentiableWithinAt
    · intro s hs
      have hd : HasDerivAt g (Real.exp (-(s ^ 2 / 2)) * (Real.sinh s - s * Real.cosh s)) s := by
        have h0 := ((hderiv_exp s).exp).mul (Real.hasDerivAt_cosh s)
        have heq : Real.exp (-(s ^ 2 / 2)) * (-s) * Real.cosh s +
            Real.exp (-(s ^ 2 / 2)) * Real.sinh s =
            Real.exp (-(s ^ 2 / 2)) * (Real.sinh s - s * Real.cosh s) := by ring
        rwa [heq] at h0
      rw [hd.deriv]
      have hs' : 0 ≤ s := le_of_lt (by simpa using hs)
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr (h1 s hs'))
  have hle : g t ≤ g 0 := hanti (Set.self_mem_Ici) ht ht
  rw [hg0] at hle
  have hexp : Real.exp (-(t ^ 2 / 2)) * Real.exp (t ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]; simp
  calc Real.cosh t = Real.exp (t ^ 2 / 2) * (Real.exp (-(t ^ 2 / 2)) * Real.cosh t) := by
        rw [← mul_assoc, mul_comm (Real.exp (t ^ 2 / 2)), hexp, one_mul]
    _ ≤ Real.exp (t ^ 2 / 2) * 1 := by
        exact mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
    _ = Real.exp (t ^ 2 / 2) := mul_one _

private lemma exp_mul_le_of_abs_le {u M t : ℝ} (hM : 0 < M) (hu : |u| ≤ M) :
    Real.exp (t * u) ≤ ((M - u) / (2 * M)) * Real.exp (t * (-M)) +
      ((M + u) / (2 * M)) * Real.exp (t * M) := by
  have hu' := abs_le.mp hu
  have ha : 0 ≤ (M - u) / (2 * M) := div_nonneg (by linarith) (by positivity)
  have hb : 0 ≤ (M + u) / (2 * M) := div_nonneg (by linarith) (by positivity)
  have hab : (M - u) / (2 * M) + (M + u) / (2 * M) = 1 := by field_simp; ring
  have hconv := (convexOn_exp).2 (Set.mem_univ (t * (-M))) (Set.mem_univ (t * M)) ha hb hab
  have heq : (M - u) / (2 * M) * (t * (-M)) + (M + u) / (2 * M) * (t * M) = t * u := by
    field_simp; ring
  simp only [smul_eq_mul] at hconv
  rwa [heq] at hconv

private lemma hoeffding_one_sided {α : Type*} [Fintype α] [Nonempty α] (m : ℕ)
    (Y : α → ℝ) (M ε : ℝ) (hM : 0 < M) (hε : 0 < ε)
    (hmean : ∑ a : α, Y a = 0) (hbdd : ∀ a, |Y a| ≤ M) :
    ((univ.filter fun S : Fin m → α => (m : ℝ) * ε ≤ ∑ j : Fin m, Y (S j)).card : ℝ) ≤
      (Fintype.card (Fin m → α) : ℝ) * Real.exp (-(m : ℝ) * ε ^ 2 / (2 * M ^ 2)) := by
  set t : ℝ := ε / M ^ 2
  have ht : 0 < t := div_pos hε (sq_pos_of_pos hM)
  have hmgf : ∑ a : α, Real.exp (t * Y a) ≤
      (Fintype.card α : ℝ) * Real.exp (t ^ 2 * M ^ 2 / 2) := by
    calc ∑ a : α, Real.exp (t * Y a)
        ≤ ∑ a : α, (((M - Y a) / (2 * M)) * Real.exp (t * (-M)) +
            ((M + Y a) / (2 * M)) * Real.exp (t * M)) := by
          refine Finset.sum_le_sum fun a _ => exp_mul_le_of_abs_le hM (hbdd a)
      _ = (Fintype.card α : ℝ) * Real.cosh (t * M) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
          have hsub : ∑ a : α, (M - Y a) / (2 * M) = (Fintype.card α : ℝ) / 2 := by
            rw [← Finset.sum_div, Finset.sum_sub_distrib, hmean, sub_zero,
              Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            field_simp [hM.ne']
          have hadd : ∑ a : α, (M + Y a) / (2 * M) = (Fintype.card α : ℝ) / 2 := by
            rw [← Finset.sum_div, Finset.sum_add_distrib, hmean, add_zero,
              Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            field_simp [hM.ne']
          rw [hsub, hadd, Real.cosh_eq]
          have : t * (-M) = -(t * M) := by ring
          rw [this]; ring
      _ ≤ (Fintype.card α : ℝ) * Real.exp ((t * M) ^ 2 / 2) := by
          exact mul_le_mul_of_nonneg_left (cosh_le_exp_half_sq (t * M)) (Nat.cast_nonneg _)
      _ = (Fintype.card α : ℝ) * Real.exp (t ^ 2 * M ^ 2 / 2) := by ring_nf
  have hprod : ∑ S : Fin m → α, Real.exp (t * ∑ j : Fin m, Y (S j)) ≤
      (Fintype.card (Fin m → α) : ℝ) * Real.exp ((m : ℝ) * (t ^ 2 * M ^ 2 / 2)) := by
    have hrew : ∑ S : Fin m → α, Real.exp (t * ∑ j : Fin m, Y (S j)) =
        (∑ a : α, Real.exp (t * Y a)) ^ m := by
      calc ∑ S : Fin m → α, Real.exp (t * ∑ j : Fin m, Y (S j))
          = ∑ S : Fin m → α, ∏ j : Fin m, Real.exp (t * Y (S j)) := by
            refine Finset.sum_congr rfl fun S _ => ?_
            rw [Finset.mul_sum, Real.exp_sum]
        _ = ∏ _j : Fin m, ∑ a : α, Real.exp (t * Y a) := by
            rw [Fintype.prod_sum]
        _ = (∑ a : α, Real.exp (t * Y a)) ^ m := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hrew, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc (∑ a : α, Real.exp (t * Y a)) ^ m
        ≤ ((Fintype.card α : ℝ) * Real.exp (t ^ 2 * M ^ 2 / 2)) ^ m := by
          exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) hmgf m
      _ = (Fintype.card α : ℝ) ^ m * (Real.exp (t ^ 2 * M ^ 2 / 2)) ^ m := mul_pow _ _ _
      _ = (Fintype.card α : ℝ) ^ m * Real.exp ((m : ℝ) * (t ^ 2 * M ^ 2 / 2)) := by
          rw [← Real.exp_nat_mul]
  have hmarkov : ((univ.filter fun S : Fin m → α => (m : ℝ) * ε ≤ ∑ j : Fin m, Y (S j)).card : ℝ) *
      Real.exp (t * ((m : ℝ) * ε)) ≤ ∑ S : Fin m → α, Real.exp (t * ∑ j : Fin m, Y (S j)) := by
    calc ((univ.filter fun S : Fin m → α => (m : ℝ) * ε ≤ ∑ j : Fin m, Y (S j)).card : ℝ) *
          Real.exp (t * ((m : ℝ) * ε))
        = ∑ _S ∈ univ.filter (fun S : Fin m → α => (m : ℝ) * ε ≤ ∑ j : Fin m, Y (S j)),
            Real.exp (t * ((m : ℝ) * ε)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ S ∈ univ.filter (fun S : Fin m → α => (m : ℝ) * ε ≤ ∑ j : Fin m, Y (S j)),
            Real.exp (t * ∑ j : Fin m, Y (S j)) := by
          refine Finset.sum_le_sum fun S hS => ?_
          rw [Finset.mem_filter] at hS
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hS.2 ht.le)
      _ ≤ ∑ S : Fin m → α, Real.exp (t * ∑ j : Fin m, Y (S j)) := by
          exact Finset.sum_le_univ_sum_of_nonneg fun _ => (Real.exp_pos _).le
  have hcomb := hmarkov.trans hprod
  rw [← le_div_iff₀ (Real.exp_pos _), mul_div_assoc, ← Real.exp_sub] at hcomb
  have hexp : (m : ℝ) * (t ^ 2 * M ^ 2 / 2) - t * ((m : ℝ) * ε) =
      -(m : ℝ) * ε ^ 2 / (2 * M ^ 2) := by
    simp only [t]
    field_simp [hM.ne']
    ring
  rwa [hexp] at hcomb

private lemma hoeffding_two_sided {α : Type*} [Fintype α] [Nonempty α] (m : ℕ)
    (Y : α → ℝ) (M ε : ℝ) (hM : 0 < M) (hε : 0 < ε)
    (hmean : ∑ a : α, Y a = 0) (hbdd : ∀ a, |Y a| ≤ M) :
    ((univ.filter fun S : Fin m → α => (m : ℝ) * ε ≤ |∑ j : Fin m, Y (S j)|).card : ℝ) ≤
      2 * (Fintype.card (Fin m → α) : ℝ) * Real.exp (-(m : ℝ) * ε ^ 2 / (2 * M ^ 2)) := by
  have hsub : (univ.filter fun S : Fin m → α => (m : ℝ) * ε ≤ |∑ j : Fin m, Y (S j)|) ⊆
      (univ.filter fun S : Fin m → α => (m : ℝ) * ε ≤ ∑ j : Fin m, Y (S j)) ∪
      (univ.filter fun S : Fin m → α => (m : ℝ) * ε ≤ ∑ j : Fin m, (-Y) (S j)) := by
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Pi.neg_apply,
      Finset.sum_neg_distrib] at hS ⊢
    rcases le_total 0 (∑ j : Fin m, Y (S j)) with h | h
    · left; rwa [abs_of_nonneg h] at hS
    · right; rwa [abs_of_nonpos h] at hS
  have hcard : ((univ.filter fun S : Fin m → α => (m : ℝ) * ε ≤ |∑ j : Fin m, Y (S j)|).card : ℝ) ≤
      ((univ.filter fun S : Fin m → α => (m : ℝ) * ε ≤ ∑ j : Fin m, Y (S j)).card : ℝ) +
      ((univ.filter fun S : Fin m → α => (m : ℝ) * ε ≤ ∑ j : Fin m, (-Y) (S j)).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h1 := hoeffding_one_sided m Y M ε hM hε hmean hbdd
  have h2 := hoeffding_one_sided m (-Y) M ε hM hε (by simp [hmean]) (by intro a; simpa using hbdd a)
  linarith

/- ### Section 2: Trace Padding and Subsequence Generating Function Identity -/

private def padString {n : ℕ} (L : ℕ) (x : Fin n → Bool) : Fin (L + n) → Bool :=
  fun i => if h : i.1 < L then false else x ⟨i.1 - L, by omega⟩

private lemma padString_prefix {n : ℕ} (L : ℕ) (x : Fin n → Bool) (i : Fin (L + n)) (hi : i.1 < L) :
    padString L x i = false := by
  simp [padString, hi]

private lemma padString_inj {n : ℕ} (L : ℕ) {x y : Fin n → Bool}
    (h : padString L x = padString L y) : x = y := by
  funext i
  have hi := congrFun h ⟨L + i.1, by omega⟩
  simp only [padString, show ¬(L + i.1 < L) by omega, ↓reduceDIte, Nat.add_sub_cancel_left] at hi
  exact hi

private def inlEmb (L n : ℕ) : Fin L ↪ Fin (L + n) :=
  ⟨fun i => ⟨i.1, by omega⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩

private def inrEmb (L n : ℕ) : Fin n ↪ Fin (L + n) :=
  ⟨fun j => ⟨L + j.1, by omega⟩, fun a b h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)⟩

@[simp] private lemma inlEmb_apply (L n : ℕ) (i : Fin L) :
    inlEmb L n i = ⟨i.1, by omega⟩ := rfl

@[simp] private lemma inrEmb_apply (L n : ℕ) (j : Fin n) :
    inrEmb L n j = ⟨L + j.1, by omega⟩ := rfl

private def splitFinset (L n : ℕ) : Finset (Fin L) × Finset (Fin n) ≃ Finset (Fin (L + n)) where
  toFun p := p.1.map (inlEmb L n) ∪ p.2.map (inrEmb L n)
  invFun S :=
    (univ.filter fun i : Fin L => inlEmb L n i ∈ S,
     univ.filter fun j : Fin n => inrEmb L n j ∈ S)
  left_inv p := by
    rcases p with ⟨S₁, S₂⟩
    ext i
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_map,
        inlEmb_apply, inrEmb_apply]
      constructor
      · rintro (⟨a, ha, h⟩ | ⟨b, _, h⟩)
        · have : a = i := Fin.ext (by simpa using congrArg Fin.val h)
          rwa [← this]
        · exfalso; have := congrArg Fin.val h; dsimp at this; omega
      · intro hi; exact Or.inl ⟨i, hi, rfl⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_map,
        inlEmb_apply, inrEmb_apply]
      constructor
      · rintro (⟨a, _, h⟩ | ⟨b, hb, h⟩)
        · exfalso; have := congrArg Fin.val h; dsimp at this; omega
        · have : b = i := Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)
          rwa [← this]
      · intro hi; exact Or.inr ⟨i, hi, rfl⟩
  right_inv S := by
    ext k
    simp only [Finset.mem_union, Finset.mem_map, inlEmb_apply, inrEmb_apply]
    constructor
    · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
      · exact (Finset.mem_filter.mp ha).2
      · exact (Finset.mem_filter.mp hb).2
    · intro hk
      by_cases h : k.1 < L
      · exact Or.inl ⟨⟨k.1, h⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, rfl⟩
      · refine Or.inr ⟨⟨k.1 - L, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · convert hk using 1; ext; show L + (k.1 - L) = k.1; omega
        · ext; show L + (k.1 - L) = k.1; omega

private lemma finRange_add (L n : ℕ) :
    List.finRange (L + n) =
      (List.finRange L).map (inlEmb L n) ++ (List.finRange n).map (inrEmb L n) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_finRange]
    by_cases hi : i < L
    · rw [List.getElem_append_left (by simp [hi])]
      simp
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_map, List.length_finRange, List.getElem_map, List.getElem_finRange,
        inrEmb_apply]
      ext; show i = L + (i - L); omega

private lemma trace_padString {n : ℕ} (L : ℕ) (x : Fin n → Bool)
    (S₁ : Finset (Fin L)) (S₂ : Finset (Fin n)) :
    Green92.trace (padString L x) (splitFinset L n (S₁, S₂)) =
      List.replicate S₁.card false ++ Green92.trace x S₂ := by
  unfold Green92.trace
  rw [finRange_add, List.filter_append, List.map_append]
  congr 1
  · rw [List.filter_map, List.map_map]
    have hfilt : (List.finRange L).filter
        ((fun i : Fin (L + n) => decide (i ∈ splitFinset L n (S₁, S₂))) ∘ inlEmb L n) =
        (List.finRange L).filter (fun i : Fin L => decide (i ∈ S₁)) := by
      refine List.filter_congr fun i _ => ?_
      simp only [Function.comp_apply, decide_eq_decide]
      change inlEmb L n i ∈ S₁.map (inlEmb L n) ∪ S₂.map (inrEmb L n) ↔ i ∈ S₁
      simp only [Finset.mem_union, Finset.mem_map, inlEmb_apply, inrEmb_apply]
      constructor
      · rintro (⟨a, ha, h⟩ | ⟨b, _, h⟩)
        · have : a = i := Fin.ext (by simpa using congrArg Fin.val h)
          rwa [← this]
        · exfalso; have := congrArg Fin.val h; dsimp at this; omega
      · intro hi; exact Or.inl ⟨i, hi, rfl⟩
    rw [hfilt]
    have hmap : ((List.finRange L).filter (fun i : Fin L => decide (i ∈ S₁))).map
        (padString L x ∘ inlEmb L n) =
        List.replicate ((List.finRange L).filter (fun i : Fin L => decide (i ∈ S₁))).length false := by
      apply List.ext_getElem
      · simp
      · intro k hk _
        simp only [List.getElem_map, Function.comp_apply, List.getElem_replicate, inlEmb_apply]
        exact padString_prefix L x _ (by simp)
    rw [hmap]
    congr 1
    have hnd : ((List.finRange L).filter (fun i : Fin L => decide (i ∈ S₁))).Nodup :=
      (List.nodup_finRange L).filter _
    rw [← List.toFinset_card_of_nodup hnd]
    congr 1
    ext i
    simp
  · rw [List.filter_map, List.map_map]
    have hfilt : (List.finRange n).filter
        ((fun i : Fin (L + n) => decide (i ∈ splitFinset L n (S₁, S₂))) ∘ inrEmb L n) =
        (List.finRange n).filter (fun j : Fin n => decide (j ∈ S₂)) := by
      refine List.filter_congr fun j _ => ?_
      simp only [Function.comp_apply, decide_eq_decide]
      change inrEmb L n j ∈ S₁.map (inlEmb L n) ∪ S₂.map (inrEmb L n) ↔ j ∈ S₂
      simp only [Finset.mem_union, Finset.mem_map, inlEmb_apply, inrEmb_apply]
      constructor
      · rintro (⟨a, _, h⟩ | ⟨b, hb, h⟩)
        · exfalso; have := congrArg Fin.val h; dsimp at this; omega
        · have : b = j := Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)
          rwa [← this]
      · intro hj; exact Or.inr ⟨j, hj, rfl⟩
    rw [hfilt]
    refine List.map_congr_left fun j _ => ?_
    simp [padString, inrEmb_apply]

private lemma filter_finRange_eq_sort {N : ℕ} (S : Finset (Fin N)) :
    (List.finRange N).filter (fun i => decide (i ∈ S)) = S.sort := by
  have h1 : ((List.finRange N).filter (fun i => decide (i ∈ S))).Pairwise (· ≤ ·) := by
    have hle : (List.finRange N).Pairwise (· ≤ ·) := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      exact le_of_lt (by simpa using hij)
    exact hle.filter _
  have h2 : S.sort.Pairwise (· ≤ ·) := S.pairwise_sort (· ≤ ·)
  have hperm : ((List.finRange N).filter (fun i => decide (i ∈ S))).Perm S.sort := by
    rw [List.perm_ext_iff_of_nodup ((List.nodup_finRange N).filter _) (S.sort_nodup (· ≤ ·))]
    intro a
    simp
  exact hperm.eq_of_pairwise' h1 h2

private lemma trace_eq_sort_map {N : ℕ} (x : Fin N → Bool) (S : Finset (Fin N)) :
    Green92.trace x S = S.sort.map x := by
  unfold Green92.trace
  rw [filter_finRange_eq_sort]

private lemma trace_length {N : ℕ} (x : Fin N → Bool) (S : Finset (Fin N)) :
    (Green92.trace x S).length = S.card := by
  rw [trace_eq_sort_map, List.length_map, Finset.length_sort]

private lemma trace_getElem {N : ℕ} (x : Fin N → Bool) (S : Finset (Fin N))
    (j : Fin S.card) :
    (Green92.trace x S)[j.1]'(by rw [trace_length]; exact j.2) = x (S.orderEmbOfFin rfl j) := by
  simp only [trace_eq_sort_map, List.getElem_map, Finset.orderEmbOfFin_apply, Fin.getElem_fin]

/-- Subsequence generating statistic specialized to `q = p = 1/2` and `z_1 = ... = z_{l-1} = 0`. -/
private noncomputable def subseqStat {l : ℕ} (hl : 1 ≤ l) (w : Fin l → Bool) (z₀ : ℂ)
    (U : List Bool) : ℂ :=
  (2 : ℂ) ^ l *
    ∑ T ∈ (univ : Finset (Fin U.length)).powersetCard l,
      if hT : T.card = l then
        let e := T.orderEmbOfFin hT
        let j₀ : ℕ := (e ⟨0, by omega⟩).1
        let jlast : ℕ := (e ⟨l - 1, by omega⟩).1
        if ∀ i : Fin l, U[(e i).1]'(e i).2 = w i then
          (2 * z₀ - 1) ^ j₀ * (-1 : ℂ) ^ (jlast - j₀ - (l - 1))
        else 0
      else 0

private lemma norm_subseqStat_le {l N : ℕ} (hl : 1 ≤ l) (w : Fin l → Bool) (z₀ : ℂ)
    (U : List Bool) (hU : U.length ≤ N) :
    ‖subseqStat hl w z₀ U‖ ≤
      (2 : ℝ) ^ l * (Nat.choose N l : ℝ) * (max 1 ‖2 * z₀ - 1‖) ^ N := by
  unfold subseqStat
  rw [norm_mul, norm_pow, Complex.norm_ofNat]
  have hterm : ∀ T ∈ (univ : Finset (Fin U.length)).powersetCard l,
      ‖if hT : T.card = l then
        let e := T.orderEmbOfFin hT
        let j₀ : ℕ := (e ⟨0, by omega⟩).1
        let jlast : ℕ := (e ⟨l - 1, by omega⟩).1
        if ∀ i : Fin l, U[(e i).1]'(e i).2 = w i then
          (2 * z₀ - 1) ^ j₀ * (-1 : ℂ) ^ (jlast - j₀ - (l - 1))
        else 0
      else 0‖ ≤ (max 1 ‖2 * z₀ - 1‖) ^ N := by
    intro T _
    split_ifs with hT
    · dsimp only
      split_ifs with hmatch
      · rw [norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, mul_one]
        have hj₀ : (T.orderEmbOfFin hT ⟨0, by omega⟩).1 ≤ N :=
          le_trans (le_of_lt (T.orderEmbOfFin hT ⟨0, by omega⟩).2) hU
        calc ‖2 * z₀ - 1‖ ^ (T.orderEmbOfFin hT ⟨0, by omega⟩).1
            ≤ (max 1 ‖2 * z₀ - 1‖) ^ (T.orderEmbOfFin hT ⟨0, by omega⟩).1 :=
              pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _
          _ ≤ (max 1 ‖2 * z₀ - 1‖) ^ N :=
              pow_le_pow_right₀ (le_max_left _ _) hj₀
      · rw [norm_zero]; positivity
    · rw [norm_zero]; positivity
  have hsum : ‖∑ T ∈ (univ : Finset (Fin U.length)).powersetCard l,
      if hT : T.card = l then
        let e := T.orderEmbOfFin hT
        let j₀ : ℕ := (e ⟨0, by omega⟩).1
        let jlast : ℕ := (e ⟨l - 1, by omega⟩).1
        if ∀ i : Fin l, U[(e i).1]'(e i).2 = w i then
          (2 * z₀ - 1) ^ j₀ * (-1 : ℂ) ^ (jlast - j₀ - (l - 1))
        else 0
      else 0‖ ≤ ((univ : Finset (Fin U.length)).powersetCard l).card * (max 1 ‖2 * z₀ - 1‖) ^ N := by
    calc _ ≤ ∑ T ∈ (univ : Finset (Fin U.length)).powersetCard l, _ := norm_sum_le _ _
      _ ≤ ∑ _T ∈ (univ : Finset (Fin U.length)).powersetCard l, (max 1 ‖2 * z₀ - 1‖) ^ N :=
          Finset.sum_le_sum hterm
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at hsum
  have hch : (Nat.choose U.length l : ℝ) ≤ (Nat.choose N l : ℝ) := by
    exact_mod_cast Nat.choose_le_choose l hU
  calc (2 : ℝ) ^ l * ‖_‖
      ≤ (2 : ℝ) ^ l * ((Nat.choose U.length l : ℝ) * (max 1 ‖2 * z₀ - 1‖) ^ N) := by
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (2 : ℝ) ^ l * ((Nat.choose N l : ℝ) * (max 1 ‖2 * z₀ - 1‖) ^ N) := by
        gcongr
    _ = _ := by ring

private lemma card_filter_lt_fin {N : ℕ} (j : Fin N) :
    (univ.filter (fun i : Fin N => i < j)).card = j.1 := by
  have himg : (univ.filter (fun i : Fin N => i < j)).image Fin.val = Finset.range j.1 := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hx; exact ⟨⟨x, lt_trans hx j.2⟩, hx, rfl⟩
  rw [← Finset.card_image_of_injective _ Fin.val_injective, himg, Finset.card_range]

private lemma card_filter_lt_orderEmbOfFin {N : ℕ} (S : Finset (Fin N)) (j : Fin S.card) :
    (S.filter (· < S.orderEmbOfFin rfl j)).card = j.1 := by
  have himg : S.filter (· < S.orderEmbOfFin rfl j) =
      (univ.filter (fun i : Fin S.card => i < j)).image (S.orderEmbOfFin rfl) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨haS, halt⟩
      have ha' : a ∈ Set.range (S.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]; exact haS
      rcases ha' with ⟨i, rfl⟩
      exact ⟨i, (S.orderEmbOfFin rfl).lt_iff_lt.mp halt, rfl⟩
    · rintro ⟨i, hilt, rfl⟩
      exact ⟨S.orderEmbOfFin_mem rfl i, (S.orderEmbOfFin rfl).lt_iff_lt.mpr hilt⟩
  rw [himg, Finset.card_image_of_injective _ (S.orderEmbOfFin rfl).injective]
  exact card_filter_lt_fin j

private lemma sum_powerset_pow_card {α : Type*} [DecidableEq α] (A : Finset α) (c : ℂ) :
    ∑ S ∈ A.powerset, c ^ S.card = (1 + c) ^ A.card := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.powerset_insert, Finset.sum_union, Finset.card_insert_of_notMem ha, pow_succ]
    · rw [Finset.sum_image]
      · have h2 : ∑ x ∈ s.powerset, c ^ (insert a x).card = c * ∑ x ∈ s.powerset, c ^ x.card := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x hx => ?_
          have hax : a ∉ x := fun h => ha (Finset.mem_powerset.mp hx h)
          rw [Finset.card_insert_of_notMem hax, pow_succ']
        rw [h2, ih]; ring
      · intro x hx y hy hxy
        have hax : a ∉ x := fun h => ha (Finset.mem_powerset.mp hx h)
        have hay : a ∉ y := fun h => ha (Finset.mem_powerset.mp hy h)
        ext z
        by_cases hza : z = a
        · subst hza; simp [hax, hay]
        · have := Finset.ext_iff.mp hxy z
          simpa [Finset.mem_insert, hza] using this
    · rw [Finset.disjoint_left]
      intro x hx1 hx2
      rcases Finset.mem_image.mp hx2 with ⟨y, _, rfl⟩
      exact ha (Finset.mem_powerset.mp hx1 (Finset.mem_insert_self a y))

/-- Exact expectation of `subseqStat` over uniform `S : Finset (Fin N)` equals the contiguous
substring generating polynomial. -/
private lemma expectation_subseqStat {N l : ℕ} (hl : 1 ≤ l) (x : Fin N → Bool)
    (w : Fin l → Bool) (z₀ : ℂ) :
    ((2 : ℂ) ^ N)⁻¹ * ∑ S : Finset (Fin N), subseqStat hl w z₀ (Green92.trace x S) =
      ∑ k ∈ Finset.range (N + 1 - l),
        if ∀ i : Fin l, ∃ hk : k + i.1 < N, x ⟨k + i.1, hk⟩ = w i then z₀ ^ k else 0 := by
  -- Step 1: Rewrite inner sum for each S by mapping powersetCard l (Fin S.card) to S.powersetCard l
  have hS_rew : ∀ S : Finset (Fin N),
      subseqStat hl w z₀ (Green92.trace x S) =
        (2 : ℂ) ^ l * ∑ C ∈ S.powersetCard l,
          if hC : C.card = l then
            let eC := C.orderEmbOfFin hC
            let c₀ := eC ⟨0, by omega⟩
            let c₁ := eC ⟨l - 1, by omega⟩
            if ∀ i : Fin l, x (eC i) = w i then
              (2 * z₀ - 1) ^ (S.filter (· < c₀)).card *
                (-1 : ℂ) ^ ((S.filter (fun t => c₀ < t ∧ t < c₁)) \ C).card
            else 0
          else 0 := by
    intro S
    unfold subseqStat
    congr 1
    set U := Green92.trace x S
    have hUlen : U.length = S.card := trace_length x S
    let fS : Fin U.length ↪o Fin N :=
      (Fin.castOrderIso hUlen).toOrderEmbedding.trans (S.orderEmbOfFin rfl)
    refine Finset.sum_bij (fun T _ => T.map fS.toEmbedding) ?_ ?_ ?_ ?_
    · intro T hT
      rw [Finset.mem_powersetCard] at hT ⊢
      refine ⟨?_, by rw [Finset.card_map]; exact hT.2⟩
      intro a ha
      rcases Finset.mem_map.mp ha with ⟨j, _, rfl⟩
      exact S.orderEmbOfFin_mem rfl _
    · intro T₁ _ T₂ _ h
      exact Finset.map_injective fS.toEmbedding h
    · intro C hC
      rw [Finset.mem_powersetCard] at hC
      let T : Finset (Fin U.length) := univ.filter fun j => fS j ∈ C
      refine ⟨T, ?_, ?_⟩
      · rw [Finset.mem_powersetCard]
        refine ⟨Finset.subset_univ _, ?_⟩
        have hmap : T.map fS.toEmbedding = C := by
          ext a
          simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, T]
          constructor
          · rintro ⟨j, hj, rfl⟩; exact hj
          · intro haC
            have haS : a ∈ Set.range (S.orderEmbOfFin rfl) := by
              rw [Finset.range_orderEmbOfFin]; exact hC.1 haC
            rcases haS with ⟨j, rfl⟩
            refine ⟨(Fin.castOrderIso hUlen).symm j, ?_, ?_⟩ <;> simp [fS, haC]
        rw [← Finset.card_map fS.toEmbedding, hmap, hC.2]
      · ext a
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, T]
        constructor
        · rintro ⟨j, hj, rfl⟩; exact hj
        · intro haC
          have haS : a ∈ Set.range (S.orderEmbOfFin rfl) := by
            rw [Finset.range_orderEmbOfFin]; exact hC.1 haC
          rcases haS with ⟨j, rfl⟩
          refine ⟨(Fin.castOrderIso hUlen).symm j, ?_, ?_⟩ <;> simp [fS, haC]
    · intro T hT
      have hTcard : T.card = l := (Finset.mem_powersetCard.mp hT).2
      have hCcard : (T.map fS.toEmbedding).card = l := by rw [Finset.card_map]; exact hTcard
      simp only [hTcard, hCcard, ↓reduceDIte]
      have heC : (T.map fS.toEmbedding).orderEmbOfFin hCcard =
          (T.orderEmbOfFin hTcard).trans fS :=
        (Finset.orderEmbOfFin_unique' hCcard (f := (T.orderEmbOfFin hTcard).trans fS) fun i => by
          simp only [RelEmbedding.coe_trans, Function.comp_apply, Finset.mem_map]
          exact ⟨T.orderEmbOfFin hTcard i, T.orderEmbOfFin_mem hTcard i, rfl⟩).symm
      have hUget : ∀ i : Fin l, U[(T.orderEmbOfFin hTcard i).1]'(T.orderEmbOfFin hTcard i).2 =
          x ((T.map fS.toEmbedding).orderEmbOfFin hCcard i) := by
        intro i
        rw [heC]
        simp only [RelEmbedding.coe_trans, Function.comp_apply, fS, OrderIso.coe_toOrderEmbedding,
          Fin.castOrderIso_apply]
        have := trace_getElem x S (Fin.cast hUlen (T.orderEmbOfFin hTcard i))
        simpa [U] using this
      have hiff : (∀ i : Fin l, U[(T.orderEmbOfFin hTcard i).1]'(T.orderEmbOfFin hTcard i).2 = w i) ↔
          (∀ i : Fin l, x ((T.map fS.toEmbedding).orderEmbOfFin hCcard i) = w i) := by
        constructor <;> intro h i <;> [rw [← hUget i]; rw [hUget i]] <;> exact h i
      by_cases hm : ∀ i : Fin l, x ((T.map fS.toEmbedding).orderEmbOfFin hCcard i) = w i
      · simp only [hm, hiff.mpr hm]
        set eT := T.orderEmbOfFin hTcard
        set eC := (T.map fS.toEmbedding).orderEmbOfFin hCcard
        have hj₀ : (S.filter (· < eC ⟨0, by omega⟩)).card = (eT ⟨0, by omega⟩).1 := by
          have he0 : eC ⟨0, by omega⟩ = S.orderEmbOfFin rfl (Fin.cast hUlen (eT ⟨0, by omega⟩)) := by
            rw [heC]; rfl
          rw [he0, card_filter_lt_orderEmbOfFin]
          rfl
        have hj₁ : (S.filter (· < eC ⟨l - 1, by omega⟩)).card = (eT ⟨l - 1, by omega⟩).1 := by
          have he1 : eC ⟨l - 1, by omega⟩ =
              S.orderEmbOfFin rfl (Fin.cast hUlen (eT ⟨l - 1, by omega⟩)) := by
            rw [heC]; rfl
          rw [he1, card_filter_lt_orderEmbOfFin]
          rfl
        have hmid : ((S.filter (fun t => eC ⟨0, by omega⟩ < t ∧ t < eC ⟨l - 1, by omega⟩)) \
            (T.map fS.toEmbedding)).card =
            (eT ⟨l - 1, by omega⟩).1 - (eT ⟨0, by omega⟩).1 - (l - 1) := by
          set C := T.map fS.toEmbedding
          set c₀ := eC ⟨0, by omega⟩
          set c₁ := eC ⟨l - 1, by omega⟩
          have hc₀le : c₀ ≤ c₁ := eC.monotone (by simp [Fin.le_iff_val_le_val])
          have hCsub : C ⊆ S := by
            intro a ha
            rcases Finset.mem_map.mp ha with ⟨j, _, rfl⟩
            exact S.orderEmbOfFin_mem rfl _
          have hCmin : ∀ a ∈ C, c₀ ≤ a := by
            intro a ha
            have ha' : a ∈ Set.range eC := by rw [Finset.range_orderEmbOfFin]; exact ha
            rcases ha' with ⟨i, rfl⟩
            exact eC.monotone (by simp [Fin.le_iff_val_le_val])
          have hCmax : ∀ a ∈ C, a ≤ c₁ := by
            intro a ha
            have ha' : a ∈ Set.range eC := by rw [Finset.range_orderEmbOfFin]; exact ha
            rcases ha' with ⟨i, rfl⟩
            exact eC.monotone (by simp [Fin.le_iff_val_le_val]; omega)
          have hc₁C : c₁ ∈ C := C.orderEmbOfFin_mem hCcard ⟨l - 1, by omega⟩
          -- Partition S.filter (· < c₁) into:
          --   S.filter (· < c₀)  ⊔  (C.erase c₁)  ⊔  ((S.filter (c₀ < · < c₁)) \ C)
          have hpart : S.filter (· < c₁) =
              S.filter (· < c₀) ∪ (C.erase c₁ ∪ ((S.filter (fun t => c₀ < t ∧ t < c₁)) \ C)) := by
            ext a
            simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_erase, Finset.mem_sdiff]
            constructor
            · rintro ⟨haS, halt₁⟩
              by_cases h0 : a < c₀
              · exact Or.inl ⟨haS, h0⟩
              · by_cases haC : a ∈ C
                · exact Or.inr (Or.inl ⟨ne_of_lt halt₁, haC⟩)
                · have ha_ne0 : a ≠ c₀ := fun heq => haC (heq ▸ C.orderEmbOfFin_mem hCcard ⟨0, by omega⟩)
                  have h0lt : c₀ < a := lt_of_le_of_ne (not_lt.mp h0) ha_ne0.symm
                  exact Or.inr (Or.inr ⟨⟨haS, h0lt, halt₁⟩, haC⟩)
            · rintro (⟨haS, halt₀⟩ | ⟨hne, haC⟩ | ⟨⟨haS, _, halt₁⟩, _⟩)
              · exact ⟨haS, lt_of_lt_of_le halt₀ hc₀le⟩
              · exact ⟨hCsub haC, lt_of_le_of_ne (hCmax a haC) hne⟩
              · exact ⟨haS, halt₁⟩
          have hd1 : Disjoint (S.filter (· < c₀))
              (C.erase c₁ ∪ ((S.filter (fun t => c₀ < t ∧ t < c₁)) \ C)) := by
            rw [Finset.disjoint_left]
            intro a ha1 ha2
            have ha0 : a < c₀ := (Finset.mem_filter.mp ha1).2
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_filter] at ha2
            rcases ha2 with ⟨_, haC⟩ | ⟨⟨_, h0a, _⟩, _⟩
            · exact not_lt.mpr (hCmin a haC) ha0
            · exact lt_asymm ha0 h0a
          have hd2 : Disjoint (C.erase c₁) ((S.filter (fun t => c₀ < t ∧ t < c₁)) \ C) := by
            rw [Finset.disjoint_left]
            intro a ha1 ha2
            exact (Finset.mem_sdiff.mp ha2).2 (Finset.mem_erase.mp ha1).2
          have hcard := congrArg Finset.card hpart
          rw [Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2,
            Finset.card_erase_of_mem hc₁C, hCcard, hj₀, hj₁] at hcard
          omega
        rw [hj₀, hmid]
      · simp only [hm, show ¬(∀ i : Fin l, U[(T.orderEmbOfFin hTcard i).1]'(T.orderEmbOfFin hTcard i).2 = w i)
          by rwa [hiff], ↓reduceIte]
  -- Step 2: Swap sums over S and C ∈ powersetCard l univ
  simp_rw [hS_rew, ← Finset.mul_sum]
  have hswap : ∑ S : Finset (Fin N), ∑ C ∈ S.powersetCard l,
        (if hC : C.card = l then
          let eC := C.orderEmbOfFin hC
          let c₀ := eC ⟨0, by omega⟩
          let c₁ := eC ⟨l - 1, by omega⟩
          if ∀ i : Fin l, x (eC i) = w i then
            (2 * z₀ - 1) ^ (S.filter (· < c₀)).card *
              (-1 : ℂ) ^ ((S.filter (fun t => c₀ < t ∧ t < c₁)) \ C).card
          else 0
        else 0) =
      ∑ C ∈ (univ : Finset (Fin N)).powersetCard l,
        if hC : C.card = l then
          let eC := C.orderEmbOfFin hC
          let c₀ := eC ⟨0, by omega⟩
          let c₁ := eC ⟨l - 1, by omega⟩
          if ∀ i : Fin l, x (eC i) = w i then
            ∑ S ∈ univ.filter (fun S : Finset (Fin N) => C ⊆ S),
              (2 * z₀ - 1) ^ (S.filter (· < c₀)).card *
                (-1 : ℂ) ^ ((S.filter (fun t => c₀ < t ∧ t < c₁)) \ C).card
          else 0
        else 0 := by
    have h1 : ∀ S : Finset (Fin N),
        ∑ C ∈ S.powersetCard l,
          (if hC : C.card = l then
            let eC := C.orderEmbOfFin hC
            let c₀ := eC ⟨0, by omega⟩
            let c₁ := eC ⟨l - 1, by omega⟩
            if ∀ i : Fin l, x (eC i) = w i then
              (2 * z₀ - 1) ^ (S.filter (· < c₀)).card *
                (-1 : ℂ) ^ ((S.filter (fun t => c₀ < t ∧ t < c₁)) \ C).card
            else 0
          else 0) =
        ∑ C ∈ (univ : Finset (Fin N)).powersetCard l,
          if C ⊆ S then
            (if hC : C.card = l then
              let eC := C.orderEmbOfFin hC
              let c₀ := eC ⟨0, by omega⟩
              let c₁ := eC ⟨l - 1, by omega⟩
              if ∀ i : Fin l, x (eC i) = w i then
                (2 * z₀ - 1) ^ (S.filter (· < c₀)).card *
                  (-1 : ℂ) ^ ((S.filter (fun t => c₀ < t ∧ t < c₁)) \ C).card
              else 0
            else 0)
          else 0 := by
      intro S
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext C
      simp [Finset.mem_powersetCard, and_comm]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun C _ => ?_
    split_ifs with hC hm
    · rw [Finset.sum_filter]
    · simp
    · simp
  rw [hswap]
  -- Step 3: Evaluate inner sum over S ⊇ C by partitioning univ \ C into A, B, D
  have hinner : ∀ C ∈ (univ : Finset (Fin N)).powersetCard l,
      (if hC : C.card = l then
        let eC := C.orderEmbOfFin hC
        let c₀ := eC ⟨0, by omega⟩
        let c₁ := eC ⟨l - 1, by omega⟩
        if ∀ i : Fin l, x (eC i) = w i then
          ∑ S ∈ univ.filter (fun S : Finset (Fin N) => C ⊆ S),
            (2 * z₀ - 1) ^ (S.filter (· < c₀)).card *
              (-1 : ℂ) ^ ((S.filter (fun t => c₀ < t ∧ t < c₁)) \ C).card
        else 0
      else 0) =
      if hC : C.card = l then
        let eC := C.orderEmbOfFin hC
        let c₀ := eC ⟨0, by omega⟩
        let c₁ := eC ⟨l - 1, by omega⟩
        if (∀ i : Fin l, x (eC i) = w i) ∧ c₁.1 = c₀.1 + (l - 1) then
          (2 : ℂ) ^ (N - l) * z₀ ^ c₀.1
        else 0
      else 0 := by
    intro C hCmem
    have hC : C.card = l := (Finset.mem_powersetCard.mp hCmem).2
    simp only [hC, ↓reduceDIte]
    set eC := C.orderEmbOfFin hC
    set c₀ := eC ⟨0, by omega⟩
    set c₁ := eC ⟨l - 1, by omega⟩
    by_cases hm : ∀ i : Fin l, x (eC i) = w i
    · rw [if_pos hm]
      have htrue : ∀ P : Prop, ((∀ i : Fin l, x (eC i) = w i) ∧ P) ↔ P := fun P =>
        ⟨fun h => h.2, fun h => ⟨hm, h⟩⟩
      simp only [htrue]
      set A : Finset (Fin N) := univ.filter (· < c₀)
      set B : Finset (Fin N) := (univ.filter (fun t => c₀ < t ∧ t < c₁)) \ C
      set D : Finset (Fin N) := univ.filter (c₁ < ·)
      have hCmin : ∀ a ∈ C, c₀ ≤ a := by
        intro a ha
        have ha' : a ∈ Set.range eC := by rw [Finset.range_orderEmbOfFin]; exact ha
        rcases ha' with ⟨i, rfl⟩
        exact eC.monotone (by simp [Fin.le_iff_val_le_val])
      have hCmax : ∀ a ∈ C, a ≤ c₁ := by
        intro a ha
        have ha' : a ∈ Set.range eC := by rw [Finset.range_orderEmbOfFin]; exact ha
        rcases ha' with ⟨i, rfl⟩
        exact eC.monotone (by simp [Fin.le_iff_val_le_val]; omega)
      have hc₀le : c₀ ≤ c₁ := eC.monotone (by simp [Fin.le_iff_val_le_val])
      have hdAB : Disjoint A B := by
        rw [Finset.disjoint_left]; intro a ha hb
        exact lt_asymm (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp (Finset.mem_sdiff.mp hb).1).2.1
      have hdAD : Disjoint A D := by
        rw [Finset.disjoint_left]; intro a ha hd
        exact not_lt.mpr hc₀le (lt_trans (Finset.mem_filter.mp hd).2 (Finset.mem_filter.mp ha).2)
      have hdBD : Disjoint B D := by
        rw [Finset.disjoint_left]; intro a hb hd
        exact lt_asymm (Finset.mem_filter.mp (Finset.mem_sdiff.mp hb).1).2.2 (Finset.mem_filter.mp hd).2
      have hdAC : Disjoint A C := by
        rw [Finset.disjoint_left]; intro a ha hc
        exact not_lt.mpr (hCmin a hc) (Finset.mem_filter.mp ha).2
      have hdBC : Disjoint B C := Finset.sdiff_disjoint
      have hdDC : Disjoint D C := by
        rw [Finset.disjoint_left]; intro a hd hc
        exact not_lt.mpr (hCmax a hc) (Finset.mem_filter.mp hd).2
      have hunion : A ∪ B ∪ D ∪ C = univ := by
        ext a
        simp only [Finset.mem_union, Finset.mem_univ, iff_true, A, B, D, Finset.mem_filter,
          Finset.mem_sdiff, true_and]
        by_cases haC : a ∈ C
        · exact Or.inr haC
        · by_cases h0 : a < c₀
          · exact Or.inl (Or.inl (Or.inl h0))
          · by_cases h1 : c₁ < a
            · exact Or.inl (Or.inr h1)
            · have hne0 : a ≠ c₀ := fun heq => haC (heq ▸ C.orderEmbOfFin_mem hC ⟨0, by omega⟩)
              have hne1 : a ≠ c₁ := fun heq => haC (heq ▸ C.orderEmbOfFin_mem hC ⟨l - 1, by omega⟩)
              exact Or.inl (Or.inl (Or.inr ⟨⟨lt_of_le_of_ne (not_lt.mp h0) hne0.symm,
                lt_of_le_of_ne (not_lt.mp h1) hne1⟩, haC⟩))
      -- Bijection between (A.powerset × B.powerset × D.powerset) and {S | C ⊆ S}
      have hbij : ∑ S ∈ univ.filter (fun S : Finset (Fin N) => C ⊆ S),
            (2 * z₀ - 1) ^ (S.filter (· < c₀)).card *
              (-1 : ℂ) ^ ((S.filter (fun t => c₀ < t ∧ t < c₁)) \ C).card =
          (∑ SA ∈ A.powerset, (2 * z₀ - 1) ^ SA.card) *
          (∑ SB ∈ B.powerset, (-1 : ℂ) ^ SB.card) *
          (∑ _SD ∈ D.powerset, (1 : ℂ)) := by
        rw [Finset.sum_mul_sum, ← Finset.sum_product', Finset.sum_mul_sum, ← Finset.sum_product']
        refine (Finset.sum_bij (fun p _ => p.1.1 ∪ p.1.2 ∪ p.2 ∪ C) ?_ ?_ ?_ ?_).symm
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact Finset.subset_union_right
        · intro p₁ hp₁ p₂ hp₂ heq
          simp only [Finset.mem_product, Finset.mem_powerset] at hp₁ hp₂
          have h1 : p₁.1.1 = p₂.1.1 := by
            ext a
            have ha := Finset.ext_iff.mp heq a
            by_cases haA : a ∈ A
            · have hnotB : ∀ x ⊆ B, a ∉ x := fun x hx h => Finset.disjoint_left.mp hdAB haA (hx h)
              have hnotD : ∀ x ⊆ D, a ∉ x := fun x hx h => Finset.disjoint_left.mp hdAD haA (hx h)
              have hnotC : a ∉ C := Finset.disjoint_left.mp hdAC haA
              simpa [hnotB _ hp₁.1.2, hnotB _ hp₂.1.2, hnotD _ hp₁.2, hnotD _ hp₂.2, hnotC] using ha
            · have hn1 : a ∉ p₁.1.1 := fun h => haA (hp₁.1.1 h)
              have hn2 : a ∉ p₂.1.1 := fun h => haA (hp₂.1.1 h)
              simp [hn1, hn2]
          have h2 : p₁.1.2 = p₂.1.2 := by
            ext a
            have ha := Finset.ext_iff.mp heq a
            by_cases haB : a ∈ B
            · have hnotA : ∀ x ⊆ A, a ∉ x := fun x hx h => Finset.disjoint_right.mp hdAB haB (hx h)
              have hnotD : ∀ x ⊆ D, a ∉ x := fun x hx h => Finset.disjoint_left.mp hdBD haB (hx h)
              have hnotC : a ∉ C := Finset.disjoint_left.mp hdBC haB
              simpa [hnotA _ hp₁.1.1, hnotA _ hp₂.1.1, hnotD _ hp₁.2, hnotD _ hp₂.2, hnotC] using ha
            · have hn1 : a ∉ p₁.1.2 := fun h => haB (hp₁.1.2 h)
              have hn2 : a ∉ p₂.1.2 := fun h => haB (hp₂.1.2 h)
              simp [hn1, hn2]
          have h3 : p₁.2 = p₂.2 := by
            ext a
            have ha := Finset.ext_iff.mp heq a
            by_cases haD : a ∈ D
            · have hnotA : ∀ x ⊆ A, a ∉ x := fun x hx h => Finset.disjoint_right.mp hdAD haD (hx h)
              have hnotB : ∀ x ⊆ B, a ∉ x := fun x hx h => Finset.disjoint_right.mp hdBD haD (hx h)
              have hnotC : a ∉ C := Finset.disjoint_left.mp hdDC haD
              simpa [hnotA _ hp₁.1.1, hnotA _ hp₂.1.1, hnotB _ hp₁.1.2, hnotB _ hp₂.1.2, hnotC] using ha
            · have hn1 : a ∉ p₁.2 := fun h => haD (hp₁.2 h)
              have hn2 : a ∉ p₂.2 := fun h => haD (hp₂.2 h)
              simp [hn1, hn2]
          exact Prod.ext (Prod.ext h1 h2) h3
        · intro S hS
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
          refine ⟨((S ∩ A, S ∩ B), S ∩ D), ?_, ?_⟩
          · simp [Finset.mem_product, Finset.mem_powerset]
          · ext a
            simp only [Finset.mem_union, Finset.mem_inter]
            constructor
            · rintro (((⟨haS, _⟩ | ⟨haS, _⟩) | ⟨haS, _⟩) | haC)
              · exact haS
              · exact haS
              · exact haS
              · exact hS haC
            · intro haS
              have haU : a ∈ A ∪ B ∪ D ∪ C := by rw [hunion]; exact Finset.mem_univ a
              simp only [Finset.mem_union] at haU
              rcases haU with ((hA | hB) | hD) | hC'
              · exact Or.inl (Or.inl (Or.inl ⟨haS, hA⟩))
              · exact Or.inl (Or.inl (Or.inr ⟨haS, hB⟩))
              · exact Or.inl (Or.inr ⟨haS, hD⟩)
              · exact Or.inr hC'
        · intro p hp
          simp only [Finset.mem_product, Finset.mem_powerset] at hp
          have hfiltA : (p.1.1 ∪ p.1.2 ∪ p.2 ∪ C).filter (· < c₀) = p.1.1 := by
            ext a
            simp only [Finset.mem_filter, Finset.mem_union]
            constructor
            · rintro ⟨(((ha | ha) | ha) | ha), halt⟩
              · exact ha
              · exfalso; exact Finset.disjoint_left.mp hdAB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, halt⟩) (hp.1.2 ha)
              · exfalso; exact Finset.disjoint_left.mp hdAD (Finset.mem_filter.mpr ⟨Finset.mem_univ _, halt⟩) (hp.2 ha)
              · exfalso; exact Finset.disjoint_left.mp hdAC (Finset.mem_filter.mpr ⟨Finset.mem_univ _, halt⟩) ha
            · intro ha
              exact ⟨Or.inl (Or.inl (Or.inl ha)), (Finset.mem_filter.mp (hp.1.1 ha)).2⟩
          have hfiltB : ((p.1.1 ∪ p.1.2 ∪ p.2 ∪ C).filter (fun t => c₀ < t ∧ t < c₁)) \ C = p.1.2 := by
            ext a
            simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_union]
            constructor
            · rintro ⟨⟨(((ha | ha) | ha) | ha), h0, h1⟩, haC⟩
              · exfalso; exact Finset.disjoint_left.mp hdAB (hp.1.1 ha)
                  (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0, h1⟩, haC⟩)
              · exact ha
              · exfalso; exact Finset.disjoint_left.mp hdBD
                  (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0, h1⟩, haC⟩) (hp.2 ha)
              · exact (haC ha).elim
            · intro ha
              have haB := hp.1.2 ha
              exact ⟨⟨Or.inl (Or.inl (Or.inr ha)), (Finset.mem_filter.mp (Finset.mem_sdiff.mp haB).1).2⟩,
                (Finset.mem_sdiff.mp haB).2⟩
          rw [hfiltA, hfiltB, mul_one]
      rw [hbij, sum_powerset_pow_card, sum_powerset_pow_card]
      have hDsum : (∑ _SD ∈ D.powerset, (1 : ℂ)) = (2 : ℂ) ^ D.card := by
        rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
      rw [hDsum]
      have h1sub : (1 : ℂ) + (2 * z₀ - 1) = 2 * z₀ := by ring
      have h1neg : (1 : ℂ) + (-1) = 0 := by ring
      rw [h1sub, h1neg]
      -- Compute cardinalities of A, B, D
      have hcardA : A.card = c₀.1 := card_filter_lt_fin c₀
      have hcardD : D.card = N - 1 - c₁.1 := by
        have hcomp : D = univ \ (univ.filter (· ≤ c₁)) := by
          ext a; simp [D, not_le]
        have hle : (univ.filter (· ≤ c₁)).card = c₁.1 + 1 := by
          have hsub : univ.filter (· ≤ c₁) = insert c₁ (univ.filter (· < c₁)) := by
            ext a; simp [le_iff_eq_or_lt]
          rw [hsub, Finset.card_insert_of_notMem (by simp), card_filter_lt_fin c₁]
        rw [hcomp, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hle]
        omega
      have htot : A.card + B.card + D.card + C.card = N := by
        have hdis1 : Disjoint (A ∪ B) D := Finset.disjoint_union_left.mpr ⟨hdAD, hdBD⟩
        have hdis2 : Disjoint (A ∪ B ∪ D) C :=
          Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hdAC, hdBC⟩, hdDC⟩
        have hc := congrArg Finset.card hunion
        rw [Finset.card_union_of_disjoint hdis2, Finset.card_union_of_disjoint hdis1,
          Finset.card_union_of_disjoint hdAB, Finset.card_univ, Fintype.card_fin] at hc
        exact hc
      have hcardB : B.card = c₁.1 - c₀.1 - (l - 1) := by
        have : c₀.1 ≤ c₁.1 := hc₀le
        have : c₁.1 < N := c₁.2
        omega
      have hcle : c₀.1 + (l - 1) ≤ c₁.1 := by
        have hstep : ∀ k (hk : k < l), c₀.1 + k ≤ (eC ⟨k, hk⟩).1 := by
          intro k
          induction k with
          | zero => intro _; simp [c₀]
          | succ m ih =>
            intro hm
            have ih' := ih (by omega)
            have hlt : (eC ⟨m, by omega⟩).1 < (eC ⟨m + 1, hm⟩).1 :=
              eC.strictMono (by simp [Fin.lt_def])
            omega
        simpa [c₁] using hstep (l - 1) (by omega)
      by_cases hcontig : c₁.1 = c₀.1 + (l - 1)
      · have hB0 : B.card = 0 := by omega
        rw [hB0, pow_zero, mul_one, hcardA, hcardD, mul_pow, mul_comm ((2 : ℂ) ^ c₀.1),
          mul_assoc, ← pow_add]
        simp only [hcontig, ↓reduceIte]
        have hexp : c₀.1 + (N - 1 - (c₀.1 + (l - 1))) = N - l := by
          have : c₁.1 < N := c₁.2
          omega
        rw [hexp, mul_comm]
      · have hBpos : B.card ≠ 0 := by omega
        rw [zero_pow hBpos, mul_zero, zero_mul]
        simp only [hcontig, ↓reduceIte]
    · rw [if_neg hm, if_neg (fun h => hm h.1)]
  rw [Finset.sum_congr rfl hinner]
  -- Step 4: Match contiguous C with k ∈ range (N + 1 - l)
  have hfactor : ((2 : ℂ) ^ N)⁻¹ * ((2 : ℂ) ^ l *
      ∑ C ∈ (univ : Finset (Fin N)).powersetCard l,
        if hC : C.card = l then
          let eC := C.orderEmbOfFin hC
          let c₀ := eC ⟨0, by omega⟩
          let c₁ := eC ⟨l - 1, by omega⟩
          if (∀ i : Fin l, x (eC i) = w i) ∧ c₁.1 = c₀.1 + (l - 1) then
            (2 : ℂ) ^ (N - l) * z₀ ^ c₀.1
          else 0
        else 0) =
      ∑ C ∈ (univ : Finset (Fin N)).powersetCard l,
        if hC : C.card = l then
          let eC := C.orderEmbOfFin hC
          let c₀ := eC ⟨0, by omega⟩
          let c₁ := eC ⟨l - 1, by omega⟩
          if (∀ i : Fin l, x (eC i) = w i) ∧ c₁.1 = c₀.1 + (l - 1) then
            z₀ ^ c₀.1
          else 0
        else 0 := by
    by_cases hlN : l ≤ N
    · rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun C _ => ?_
      split_ifs with hC
      · dsimp only
        split_ifs
        · have hpow : (2 : ℂ) ^ N = (2 : ℂ) ^ l * (2 : ℂ) ^ (N - l) := by
            rw [← pow_add, Nat.add_sub_of_le hlN]
          have h2ne : (2 : ℂ) ^ N ≠ 0 := pow_ne_zero N (by norm_num)
          calc ((2 : ℂ) ^ N)⁻¹ * ((2 : ℂ) ^ l * ((2 : ℂ) ^ (N - l) *
                z₀ ^ (C.orderEmbOfFin hC ⟨0, by omega⟩).1))
              = (((2 : ℂ) ^ N)⁻¹ * ((2 : ℂ) ^ l * (2 : ℂ) ^ (N - l))) *
                z₀ ^ (C.orderEmbOfFin hC ⟨0, by omega⟩).1 := by ring
            _ = z₀ ^ (C.orderEmbOfFin hC ⟨0, by omega⟩).1 := by
                rw [← hpow, inv_mul_cancel₀ h2ne, one_mul]
        · simp
      · simp
    · have hempty : ((univ : Finset (Fin N)).powersetCard l) = ∅ := by
        rw [Finset.powersetCard_eq_empty]
        simpa using Nat.lt_of_not_ge hlN
      simp [hempty]
  rw [hfactor]
  -- Restrict LHS sum to contiguous intervals
  have hbij2 : ∑ C ∈ ((univ : Finset (Fin N)).powersetCard l).filter
        (fun C => if hC : C.card = l then
            (C.orderEmbOfFin hC ⟨l - 1, by omega⟩).1 = (C.orderEmbOfFin hC ⟨0, by omega⟩).1 + (l - 1)
          else False),
        (if hC : C.card = l then
          if ∀ i : Fin l, x (C.orderEmbOfFin hC i) = w i then
            z₀ ^ (C.orderEmbOfFin hC ⟨0, by omega⟩).1
          else 0
        else 0) =
      ∑ k ∈ Finset.range (N + 1 - l),
        if ∀ i : Fin l, ∃ hk : k + i.1 < N, x ⟨k + i.1, hk⟩ = w i then z₀ ^ k else 0 := by
    refine (Finset.sum_bij (fun k hk =>
        (univ : Finset (Fin l)).image (fun i => ⟨k + i.1, by
          have := Finset.mem_range.mp hk; omega⟩)) ?_ ?_ ?_ ?_).symm
    · intro k hk
      have hk' := Finset.mem_range.mp hk
      set C : Finset (Fin N) := (univ : Finset (Fin l)).image (fun i => ⟨k + i.1, by omega⟩)
      have hcard : C.card = l := by
        rw [Finset.card_image_of_injective]
        · simp
        · intro a b hab; ext; have := congrArg Fin.val hab; dsimp at this; omega
      let fShift : Fin l ↪o Fin N :=
        OrderEmbedding.ofStrictMono (fun i : Fin l => (⟨k + i.1, by omega⟩ : Fin N))
          (fun a b hab => Nat.add_lt_add_left hab k)
      have hemb : C.orderEmbOfFin hcard = fShift :=
        (Finset.orderEmbOfFin_unique' hcard (f := fShift) fun i =>
          Finset.mem_image_of_mem _ (Finset.mem_univ i)).symm
      simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and, hcard,
        ↓reduceDIte, hemb]
      change k + (l - 1) = k + 0 + (l - 1)
      omega
    · intro k₁ hk₁ k₂ hk₂ heq
      have hk₁' := Finset.mem_range.mp hk₁
      have hk₂' := Finset.mem_range.mp hk₂
      have h1 : (⟨k₁, by omega⟩ : Fin N) ∈ (univ : Finset (Fin l)).image
          (fun i => (⟨k₁ + i.1, by omega⟩ : Fin N)) := by
        exact Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, by simp⟩
      rw [heq] at h1
      rcases Finset.mem_image.mp h1 with ⟨i₂, _, hi₂⟩
      have hle1 : k₂ ≤ k₁ := by have := congrArg Fin.val hi₂; dsimp at this; omega
      have h2 : (⟨k₂, by omega⟩ : Fin N) ∈ (univ : Finset (Fin l)).image
          (fun i => (⟨k₂ + i.1, by omega⟩ : Fin N)) := by
        exact Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, by simp⟩
      rw [← heq] at h2
      rcases Finset.mem_image.mp h2 with ⟨i₁, _, hi₁⟩
      have hle2 : k₁ ≤ k₂ := by have := congrArg Fin.val hi₁; dsimp at this; omega
      omega
    · intro C hCmem
      simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and] at hCmem
      rcases hCmem with ⟨hC, hcontig⟩
      simp only [hC, ↓reduceDIte] at hcontig
      set eC := C.orderEmbOfFin hC
      set k := (eC ⟨0, by omega⟩).1
      have hklt : k < N + 1 - l := by
        have := (eC ⟨l - 1, by omega⟩).2
        omega
      refine ⟨k, Finset.mem_range.mpr hklt, ?_⟩
      have heCval : ∀ i : Fin l, (eC i).1 = k + i.1 := by
        have hlo : ∀ m (hm : m < l), k + m ≤ (eC ⟨m, hm⟩).1 := by
          intro m
          induction m with
          | zero => intro _; simp [k]
          | succ m ih =>
            intro hm
            have ih' := ih (by omega)
            have hlt : (eC ⟨m, by omega⟩).1 < (eC ⟨m + 1, hm⟩).1 :=
              eC.strictMono (by simp [Fin.lt_def])
            omega
        have hhi : ∀ i : Fin l, (eC i).1 + (l - 1 - i.1) ≤ (eC ⟨l - 1, by omega⟩).1 := by
          intro i
          suffices ∀ d : ℕ, ∀ j : Fin l, j.1 + d = l - 1 → (eC j).1 + d ≤ (eC ⟨l - 1, by omega⟩).1 by
            exact this (l - 1 - i.1) i (by omega)
          intro d
          induction d with
          | zero =>
            intro j hj
            have : j = ⟨l - 1, by omega⟩ := Fin.ext (by omega)
            rw [this]; simp
          | succ d ih =>
            intro j hj
            have hlt : (eC j).1 < (eC ⟨j.1 + 1, by omega⟩).1 :=
              eC.strictMono (by simp [Fin.lt_def])
            have ih' := ih ⟨j.1 + 1, by omega⟩ (by simp; omega)
            omega
        intro i
        have h1 : k + i.1 ≤ (eC i).1 := by simpa using hlo i.1 i.2
        have h2 := hhi i
        omega
      ext a
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        have : (⟨k + i.1, by omega⟩ : Fin N) = eC i := Fin.ext (heCval i).symm
        rw [this]
        exact C.orderEmbOfFin_mem hC i
      · intro haC
        have ha' : a ∈ Set.range eC := by rw [Finset.range_orderEmbOfFin]; exact haC
        rcases ha' with ⟨i, rfl⟩
        exact ⟨i, Fin.ext (heCval i).symm⟩
    · intro k hk
      have hk' := Finset.mem_range.mp hk
      set C : Finset (Fin N) := (univ : Finset (Fin l)).image (fun i => ⟨k + i.1, by omega⟩)
      have hcard : C.card = l := by
        rw [Finset.card_image_of_injective]
        · simp
        · intro a b hab; ext; have := congrArg Fin.val hab; dsimp at this; omega
      let fShift : Fin l ↪o Fin N :=
        OrderEmbedding.ofStrictMono (fun i : Fin l => (⟨k + i.1, by omega⟩ : Fin N))
          (fun a b hab => Nat.add_lt_add_left hab k)
      have hemb : C.orderEmbOfFin hcard = fShift :=
        (Finset.orderEmbOfFin_unique' hcard (f := fShift) fun i =>
          Finset.mem_image_of_mem _ (Finset.mem_univ i)).symm
      simp only [hcard, ↓reduceDIte, hemb]
      have hiff : (∀ i : Fin l, x (fShift i) = w i) ↔
          (∀ i : Fin l, ∃ hk : k + i.1 < N, x ⟨k + i.1, hk⟩ = w i) := by
        constructor
        · intro h i; exact ⟨by omega, h i⟩
        · intro h i; rcases h i with ⟨_, hi⟩; exact hi
      by_cases hm : ∀ i : Fin l, x (fShift i) = w i
      · rw [if_pos hm, if_pos (hiff.mp hm)]
        change z₀ ^ k = z₀ ^ (k + 0)
        simp
      · rw [if_neg hm, if_neg (by rwa [← hiff])]
  rw [← hbij2, Finset.sum_filter]
  refine Finset.sum_congr rfl fun C _ => ?_
  by_cases hC : C.card = l
  · simp only [hC, ↓reduceDIte]
    by_cases h1 : (C.orderEmbOfFin hC ⟨l - 1, by omega⟩).1 = (C.orderEmbOfFin hC ⟨0, by omega⟩).1 + (l - 1)
    · by_cases h2 : ∀ i : Fin l, x (C.orderEmbOfFin hC i) = w i
      · simp [h1, h2]
      · simp [h1, h2]
    · simp [h1]
  · simp [hC]

/- ### Section 3: Fine-Wilf, Robson's Lemma, and Sparse Polynomial Reduction -/

private lemma fine_wilf {L : ℕ} (f : ℕ → Bool) :
    ∀ n p q : ℕ, p + q = n → 0 < p → 0 < q → p + q ≤ L →
      (∀ i, i + p < L → f i = f (i + p)) →
      (∀ i, i + q < L → f i = f (i + q)) →
      ∀ i, i + Nat.gcd p q < L → f i = f (i + Nat.gcd p q) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro p q hsum hp hq hL hperP hperQ
    rcases lt_trichotomy p q with hlt | heq | hgt
    · have hperSub : ∀ i, i + (q - p) < L → f i = f (i + (q - p)) := by
        intro i hi
        by_cases hip : p ≤ i
        · have h1 := hperP (i - p) (by omega)
          have h2 := hperQ (i - p) (by omega)
          rw [show i - p + p = i by omega] at h1
          rw [show i - p + q = i + (q - p) by omega] at h2
          exact h1.symm.trans h2
        · have h1 := hperQ i (by omega)
          have h2 := hperP (i + (q - p)) (by omega)
          rw [show i + (q - p) + p = i + q by omega] at h2
          exact h1.trans h2.symm
      have hgcd : Nat.gcd p q = Nat.gcd p (q - p) := by
        rw [Nat.gcd_comm, ← Nat.gcd_sub_self_left (le_of_lt hlt), Nat.gcd_comm]
      rw [hgcd]
      exact ih (p + (q - p)) (by omega) p (q - p) rfl hp (by omega) (by omega) hperP hperSub
    · subst heq
      simpa [Nat.gcd_self] using hperP
    · have hgcd : Nat.gcd p q = Nat.gcd q p := Nat.gcd_comm p q
      rw [hgcd]
      have hperSub : ∀ i, i + (p - q) < L → f i = f (i + (p - q)) := by
        intro i hi
        by_cases hiq : q ≤ i
        · have h1 := hperQ (i - q) (by omega)
          have h2 := hperP (i - q) (by omega)
          rw [show i - q + q = i by omega] at h1
          rw [show i - q + p = i + (p - q) by omega] at h2
          exact h1.symm.trans h2
        · have h1 := hperP i (by omega)
          have h2 := hperQ (i + (p - q)) (by omega)
          rw [show i + (p - q) + q = i + p by omega] at h2
          exact h1.trans h2.symm
      have hgcd2 : Nat.gcd q p = Nat.gcd q (p - q) := by
        rw [Nat.gcd_comm, ← Nat.gcd_sub_self_left (le_of_lt hgt), Nat.gcd_comm]
      rw [hgcd2]
      exact ih (q + (p - q)) (by omega) q (p - q) rfl hq (by omega) (by omega) hperQ hperSub

private lemma periodic_step_mul {L g : ℕ} (f : ℕ → Bool) (hper : ∀ i, i + g < L → f i = f (i + g)) :
    ∀ k i, i + k * g < L → f i = f (i + k * g) := by
  intro k
  induction k with
  | zero => intro i _; simp
  | succ k ih =>
    intro i hi
    have h1 := ih i (by rw [Nat.succ_mul] at hi; omega)
    have h2 := hper (i + k * g) (by rw [Nat.succ_mul] at hi; omega)
    rw [show i + k * g + g = i + (k + 1) * g by ring] at h2
    exact h1.trans h2

/-- Robson's Lemma: any binary string of length `2s - 1` can be extended by one bit to a string
of length `2s` with no period in `{1, ..., s - 1}`. -/
private lemma robson_aperiodic_ext {s : ℕ} (hs : 1 ≤ s) (w' : Fin (2 * s - 1) → Bool) :
    ∃ b : Bool,
      let w : Fin (2 * s) → Bool := fun i => if h : i.1 < 2 * s - 1 then w' ⟨i.1, h⟩ else b
      ∀ p : ℕ, 1 ≤ p → p < s → ∃ i : ℕ, ∃ hi : i + p < 2 * s,
        w ⟨i, by omega⟩ ≠ w ⟨i + p, hi⟩ := by
  let extW : Bool → Fin (2 * s) → Bool :=
    fun b i => if h : i.1 < 2 * s - 1 then w' ⟨i.1, h⟩ else b
  by_contra h
  dsimp only at h
  push Not at h
  obtain ⟨p, hp1, hps, hperP⟩ := h false
  obtain ⟨q, hq1, hqs, hperQ⟩ := h true
  let f : ℕ → Bool := fun i => if hi : i < 2 * s - 1 then w' ⟨i, hi⟩ else false
  have hfP : ∀ i, i + p < 2 * s - 1 → f i = f (i + p) := by
    intro i hi
    have h1 := hperP i (by omega)
    simp only [show i < 2 * s - 1 by omega, hi, ↓reduceDIte] at h1
    simp only [f, show i < 2 * s - 1 by omega, hi, ↓reduceDIte]
    exact h1
  have hfQ : ∀ i, i + q < 2 * s - 1 → f i = f (i + q) := by
    intro i hi
    have h1 := hperQ i (by omega)
    simp only [show i < 2 * s - 1 by omega, hi, ↓reduceDIte] at h1
    simp only [f, show i < 2 * s - 1 by omega, hi, ↓reduceDIte]
    exact h1
  have hfg : ∀ i, i + Nat.gcd p q < 2 * s - 1 → f i = f (i + Nat.gcd p q) :=
    fine_wilf f (p + q) p q rfl (by omega) (by omega) (by omega) hfP hfQ
  have hfp : f (2 * s - 1 - p) = false := by
    have h1 := hperP (2 * s - 1 - p) (by omega)
    simp only [show 2 * s - 1 - p < 2 * s - 1 by omega,
      show ¬(2 * s - 1 - p + p < 2 * s - 1) by omega, ↓reduceDIte] at h1
    simp only [f, show 2 * s - 1 - p < 2 * s - 1 by omega, ↓reduceDIte]
    exact h1
  have hfq : f (2 * s - 1 - q) = true := by
    have h1 := hperQ (2 * s - 1 - q) (by omega)
    simp only [show 2 * s - 1 - q < 2 * s - 1 by omega,
      show ¬(2 * s - 1 - q + q < 2 * s - 1) by omega, ↓reduceDIte] at h1
    simp only [f, show 2 * s - 1 - q < 2 * s - 1 by omega, ↓reduceDIte]
    exact h1
  set g := Nat.gcd p q
  have hgdvdP : g ∣ p := Nat.gcd_dvd_left p q
  have hgdvdQ : g ∣ q := Nat.gcd_dvd_right p q
  rcases hgdvdP with ⟨kp, hkp⟩
  rcases hgdvdQ with ⟨kq, hkq⟩
  have heq : f (2 * s - 1 - p) = f (2 * s - 1 - q) := by
    rcases le_total p q with hpq | hqp
    · have hk : kq - kp = (q - p) / g := by
        have hgpos : 0 < g := Nat.gcd_pos_of_pos_left q (by omega)
        have hmul : g * (kq - kp) = q - p := by
          rw [Nat.mul_sub, ← hkq, ← hkp]
        rw [← hmul, Nat.mul_div_cancel_left _ hgpos]
      have hstep := periodic_step_mul f hfg (kq - kp) (2 * s - 1 - q) (by
        have : (kq - kp) * g = q - p := by
          rw [mul_comm, Nat.mul_sub, ← hkq, ← hkp]
        omega)
      have hidx : 2 * s - 1 - q + (kq - kp) * g = 2 * s - 1 - p := by
        have : (kq - kp) * g = q - p := by
          rw [mul_comm, Nat.mul_sub, ← hkq, ← hkp]
        omega
      rw [hidx] at hstep
      exact hstep.symm
    · have hstep := periodic_step_mul f hfg (kp - kq) (2 * s - 1 - p) (by
        have : (kp - kq) * g = p - q := by
          rw [mul_comm, Nat.mul_sub, ← hkq, ← hkp]
        omega)
      have hidx : 2 * s - 1 - p + (kp - kq) * g = 2 * s - 1 - q := by
        have : (kp - kq) * g = p - q := by
          rw [mul_comm, Nat.mul_sub, ← hkq, ← hkp]
        omega
      rw [hidx] at hstep
      exact hstep
  rw [hfp, hfq] at heq
  exact Bool.false_ne_true heq

/-- Positions where `w` occurs contiguously in `x`. -/
private def posSet {N l : ℕ} (x : Fin N → Bool) (w : Fin l → Bool) : Finset ℕ :=
  (Finset.range (N + 1 - l)).filter fun k =>
    ∀ i : Fin l, ∃ hk : k + i.1 < N, x ⟨k + i.1, hk⟩ = w i

/-- For distinct `x, y : Fin N → Bool` agreeing on `< 2s - 1`, there exists `w : Fin (2s) → Bool`,
`m₀ < N`, `ε ∈ {-1, 1}`, and a sparse polynomial `p(z) = 1 - σ z^d + ∑_{j=s}^N c_j z^j`
representing `ε * z^{-m₀}` times the substring generating function difference. -/
private lemma exists_sparse_poly_for_strings {N s : ℕ} (hs : 2 ≤ s)
    (x y : Fin N → Bool) (hxy : x ≠ y)
    (hpref : ∀ i : Fin N, i.1 < 2 * s - 1 → x i = y i) :
    ∃ (w : Fin (2 * s) → Bool) (σ : Bool) (d : ℕ) (c : ℕ → ℝ),
      1 ≤ d ∧ d < s ∧ (∀ j, |c j| ≤ 1) ∧
      ∀ z : ℂ, ‖z‖ = 1 →
        ‖(∑ k ∈ posSet x w, z ^ k) - (∑ k ∈ posSet y w, z ^ k)‖ =
          ‖(1 : ℂ) - (if σ then z ^ d else 0) + ∑ j ∈ Finset.Icc s N, (c j : ℂ) * z ^ j‖ := by
  -- Find first differing index i₀ ≥ 2s - 1
  have hex : ∃ i : Fin N, x i ≠ y i := by
    by_contra h; push Not at h; exact hxy (funext h)
  let diffSet : Finset (Fin N) := univ.filter fun i => x i ≠ y i
  have hdiff_ne : diffSet.Nonempty := by
    rcases hex with ⟨i, hi⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  set i₀ := diffSet.min' hdiff_ne
  have hi₀_diff : x i₀ ≠ y i₀ := (Finset.mem_filter.mp (diffSet.min'_mem hdiff_ne)).2
  have hi₀_ge : 2 * s - 1 ≤ i₀.1 := by
    by_contra hlt
    exact hi₀_diff (hpref i₀ (by omega))
  have hi₀_min : ∀ j : Fin N, j < i₀ → x j = y j := by
    intro j hj
    by_contra hne
    exact not_lt.mpr (diffSet.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)) hj
  -- Extract prefix w' of length 2s - 1 immediately before i₀
  let w' : Fin (2 * s - 1) → Bool := fun j => x ⟨i₀.1 - (2 * s - 1) + j.1, by omega⟩
  obtain ⟨b, hb⟩ := robson_aperiodic_ext (by omega) w'
  let w : Fin (2 * s) → Bool := fun j => if h : j.1 < 2 * s - 1 then w' ⟨j.1, h⟩ else b
  -- Show posSet x w and posSet y w are both s-separated
  have hsep : ∀ u : Fin N → Bool, ∀ k₁ ∈ posSet u w, ∀ k₂ ∈ posSet u w, k₁ < k₂ → s ≤ k₂ - k₁ := by
    intro u k₁ hk₁ k₂ hk₂ hlt
    by_contra hsmall
    have hp1 : 1 ≤ k₂ - k₁ := by omega
    have hps : k₂ - k₁ < s := by omega
    obtain ⟨j, hj, hne⟩ := hb (k₂ - k₁) hp1 hps
    have h1 := (Finset.mem_filter.mp hk₁).2 ⟨j + (k₂ - k₁), hj⟩
    have h2 := (Finset.mem_filter.mp hk₂).2 ⟨j, by omega⟩
    rcases h1 with ⟨hk₁', h1eq⟩
    rcases h2 with ⟨hk₂', h2eq⟩
    have hidx : (⟨k₁ + (j + (k₂ - k₁)), hk₁'⟩ : Fin N) = ⟨k₂ + j, hk₂'⟩ := by
      ext; dsimp; omega
    rw [hidx] at h1eq
    exact hne (h2eq.symm.trans h1eq)
  -- Show k₀ := i₀ - (2s - 1) is in the symmetric difference of posSet x w and posSet y w
  set k₀ : ℕ := i₀.1 - (2 * s - 1)
  have hk₀_range : k₀ < N + 1 - 2 * s := by omega
  have hk₀_symm : (k₀ ∈ posSet x w) ≠ (k₀ ∈ posSet y w) := by
    have hkx : k₀ ∈ posSet x w ↔ x i₀ = b := by
      simp only [posSet, Finset.mem_filter, Finset.mem_range, hk₀_range, true_and]
      constructor
      · intro h
        rcases h ⟨2 * s - 1, by omega⟩ with ⟨hk, hval⟩
        have hidx : (⟨k₀ + (2 * s - 1), hk⟩ : Fin N) = i₀ := by ext; dsimp [k₀]; omega
        rw [hidx] at hval
        simpa [w] using hval
      · intro hxb j
        refine ⟨by omega, ?_⟩
        by_cases hj : j.1 < 2 * s - 1
        · simp [w, w', hj, k₀]
        · have hidx : (⟨k₀ + j.1, by omega⟩ : Fin N) = i₀ := by ext; dsimp [k₀]; omega
          rw [hidx]
          simp [w, hj, hxb]
    have hky : k₀ ∈ posSet y w ↔ y i₀ = b := by
      simp only [posSet, Finset.mem_filter, Finset.mem_range, hk₀_range, true_and]
      constructor
      · intro h
        rcases h ⟨2 * s - 1, by omega⟩ with ⟨hk, hval⟩
        have hidx : (⟨k₀ + (2 * s - 1), hk⟩ : Fin N) = i₀ := by ext; dsimp [k₀]; omega
        rw [hidx] at hval
        simpa [w] using hval
      · intro hyb j
        refine ⟨by omega, ?_⟩
        by_cases hj : j.1 < 2 * s - 1
        · have heqxy : y ⟨k₀ + j.1, by omega⟩ = x ⟨k₀ + j.1, by omega⟩ :=
            (hi₀_min ⟨k₀ + j.1, by omega⟩ (by simp [Fin.lt_def, k₀]; omega)).symm
          rw [heqxy]
          simp [w, w', hj, k₀]
        · have hidx : (⟨k₀ + j.1, by omega⟩ : Fin N) = i₀ := by ext; dsimp [k₀]; omega
          rw [hidx]
          simp [w, hj, hyb]
    intro heq
    have hiff : x i₀ = b ↔ y i₀ = b := by rw [← hkx, ← hky, heq]
    cases hx : x i₀ <;> cases hy : y i₀ <;> cases hb' : b <;> simp_all
  -- Define A = posSet x w \ posSet y w, B = posSet y w \ posSet x w
  set A := posSet x w \ posSet y w
  set B := posSet y w \ posSet x w
  have hAB_ne : (A ∪ B).Nonempty := by
    by_cases hx : k₀ ∈ posSet x w
    · have hy : k₀ ∉ posSet y w := fun h => hk₀_symm (by simp [hx, h])
      exact ⟨k₀, Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hy⟩)⟩
    · have hy : k₀ ∈ posSet y w := by
        by_contra hny; exact hk₀_symm (by simp [hx, hny])
      exact ⟨k₀, Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hy, hx⟩)⟩
  set m₀ := (A ∪ B).min' hAB_ne
  have hm₀_mem : m₀ ∈ A ∪ B := (A ∪ B).min'_mem hAB_ne
  -- Symmetrize so the leading set contains m₀
  have hAB_lead : ∀ (P Q : Finset ℕ),
      (∀ k₁ ∈ P, ∀ k₂ ∈ P, k₁ < k₂ → s ≤ k₂ - k₁) →
      (∀ k₁ ∈ Q, ∀ k₂ ∈ Q, k₁ < k₂ → s ≤ k₂ - k₁) →
      (∀ k ∈ P, k < N) → (∀ k ∈ Q, k < N) →
      m₀ ∈ P \ Q → (∀ k ∈ (P \ Q) ∪ (Q \ P), m₀ ≤ k) →
      ∃ (σ : Bool) (d : ℕ) (c : ℕ → ℝ),
        1 ≤ d ∧ d < s ∧ (∀ j, |c j| ≤ 1) ∧
        ∀ z : ℂ, ‖z‖ = 1 →
          ‖(∑ k ∈ P, z ^ k) - (∑ k ∈ Q, z ^ k)‖ =
            ‖(1 : ℂ) - (if σ then z ^ d else 0) + ∑ j ∈ Finset.Icc s N, (c j : ℂ) * z ^ j‖ := by
    intro P Q hsepP hsepQ hPN hQN hm₀P hmin
    have hdiff_eq : ∀ z : ℂ, (∑ k ∈ P, z ^ k) - (∑ k ∈ Q, z ^ k) =
        (∑ k ∈ P \ Q, z ^ k) - (∑ k ∈ Q \ P, z ^ k) := by
      intro z
      have hP : ∑ k ∈ P, z ^ k = (∑ k ∈ P \ Q, z ^ k) + (∑ k ∈ P ∩ Q, z ^ k) := by
        rw [← Finset.sum_union (Finset.disjoint_sdiff_inter P Q), Finset.sdiff_union_inter]
      have hQ : ∑ k ∈ Q, z ^ k = (∑ k ∈ Q \ P, z ^ k) + (∑ k ∈ P ∩ Q, z ^ k) := by
        rw [Finset.inter_comm, ← Finset.sum_union (Finset.disjoint_sdiff_inter Q P),
          Finset.sdiff_union_inter]
      rw [hP, hQ]; ring
    -- Check if there is any element of Q \ P in (m₀, m₀ + s)
    let smallQ := (Q \ P).filter (fun k => k < m₀ + s)
    have hsmallQ_card : smallQ.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      have haQ : a ∈ Q := (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha).1).1
      have hbQ : b ∈ Q := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hb).1).1
      have ha_ge : m₀ ≤ a := hmin a (Finset.mem_union_right _ (Finset.mem_filter.mp ha).1)
      have hb_ge : m₀ ≤ b := hmin b (Finset.mem_union_right _ (Finset.mem_filter.mp hb).1)
      have ha_lt : a < m₀ + s := (Finset.mem_filter.mp ha).2
      have hb_lt : b < m₀ + s := (Finset.mem_filter.mp hb).2
      rcases lt_trichotomy a b with hlt | rfl | hgt
      · exfalso; have := hsepQ a haQ b hbQ hlt; omega
      · rfl
      · exfalso; have := hsepQ b hbQ a haQ hgt; omega
    have hsmallP : ∀ k ∈ P \ Q, k < m₀ + s → k = m₀ := by
      intro k hk hlt
      have hkP : k ∈ P := (Finset.mem_sdiff.mp hk).1
      have hk_ge : m₀ ≤ k := hmin k (Finset.mem_union_left _ hk)
      rcases eq_or_lt_of_le hk_ge with rfl | hlt'
      · rfl
      · exfalso; have := hsepP m₀ (Finset.mem_sdiff.mp hm₀P).1 k hkP hlt'; omega
    let σ : Bool := decide smallQ.Nonempty
    let d : ℕ := if h : smallQ.Nonempty then smallQ.min' h - m₀ else 1
    let c : ℕ → ℝ := fun j =>
      (if m₀ + j ∈ P \ Q then (1 : ℝ) else 0) - (if m₀ + j ∈ Q \ P then (1 : ℝ) else 0)
    have hd_bounds : 1 ≤ d ∧ d < s := by
      by_cases hne : smallQ.Nonempty
      · simp only [d, hne, ↓reduceDIte]
        have hmem := smallQ.min'_mem hne
        have hge : m₀ ≤ smallQ.min' hne := hmin _ (Finset.mem_union_right _ (Finset.mem_filter.mp hmem).1)
        have hne_m₀ : smallQ.min' hne ≠ m₀ := fun heq =>
          (Finset.mem_sdiff.mp hm₀P).2 (heq ▸ (Finset.mem_sdiff.mp (Finset.mem_filter.mp hmem).1).1)
        have hlt : smallQ.min' hne < m₀ + s := (Finset.mem_filter.mp hmem).2
        omega
      · simp only [d, hne, ↓reduceDIte]
        omega
    have hc_bdd : ∀ j, |c j| ≤ 1 := by
      intro j; simp only [c]; split_ifs <;> norm_num
    refine ⟨σ, d, c, hd_bounds.1, hd_bounds.2, hc_bdd, ?_⟩
    intro z hz
    rw [hdiff_eq]
    have hz_pow : ‖z ^ m₀‖ = 1 := by rw [norm_pow, hz, one_pow]
    have hfac : (∑ k ∈ P \ Q, z ^ k) - (∑ k ∈ Q \ P, z ^ k) =
        z ^ m₀ * ((1 : ℂ) - (if σ then z ^ d else 0) + ∑ j ∈ Finset.Icc s N, (c j : ℂ) * z ^ j) := by
      -- Express both sides as sums over j ∈ range (N + 1)
      have hP_sum : ∑ k ∈ P \ Q, z ^ k =
          z ^ m₀ * (1 + ∑ j ∈ Finset.Icc s N, (if m₀ + j ∈ P \ Q then (1 : ℂ) else 0) * z ^ j) := by
        rw [mul_add, mul_one, Finset.mul_sum]
        have hP_part : P \ Q = insert m₀ ((P \ Q).filter (fun k => m₀ + s ≤ k)) := by
          ext k
          simp only [Finset.mem_insert, Finset.mem_filter]
          constructor
          · intro hk
            by_cases hlt : k < m₀ + s
            · exact Or.inl (hsmallP k hk hlt)
            · exact Or.inr ⟨hk, not_lt.mp hlt⟩
          · rintro (rfl | ⟨hk, _⟩)
            · exact hm₀P
            · exact hk
        conv_lhs => rw [hP_part]
        rw [Finset.sum_insert (by simp; omega)]
        congr 1
        have hbijP : ∑ k ∈ (P \ Q).filter (fun k => m₀ + s ≤ k), z ^ k =
            ∑ j ∈ (Finset.Icc s N).filter (fun j => m₀ + j ∈ P \ Q), z ^ m₀ * z ^ j := by
          refine Finset.sum_bij (fun k _ => k - m₀) ?_ ?_ ?_ ?_
          · intro k hk
            simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
            have hkN : k < N := hPN k (Finset.mem_sdiff.mp hk.1).1
            refine ⟨⟨by omega, by omega⟩, ?_⟩
            convert hk.1 using 1; omega
          · intro k₁ hk₁ k₂ hk₂ heq
            simp only [Finset.mem_filter] at hk₁ hk₂
            omega
          · intro j hj
            simp only [Finset.mem_filter, Finset.mem_Icc] at hj
            exact ⟨m₀ + j, Finset.mem_filter.mpr ⟨hj.2, by omega⟩, by omega⟩
          · intro k hk
            simp only [Finset.mem_filter] at hk
            rw [← pow_add, show m₀ + (k - m₀) = k by omega]
        rw [hbijP, Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> ring
      have hQ_sum : ∑ k ∈ Q \ P, z ^ k =
          z ^ m₀ * ((if σ then z ^ d else 0) +
            ∑ j ∈ Finset.Icc s N, (if m₀ + j ∈ Q \ P then (1 : ℂ) else 0) * z ^ j) := by
        rw [mul_add, Finset.mul_sum]
        have hQ_part : Q \ P = smallQ ∪ ((Q \ P).filter (fun k => m₀ + s ≤ k)) := by
          ext k
          simp only [smallQ, Finset.mem_union, Finset.mem_filter]
          constructor
          · intro hk
            by_cases hlt : k < m₀ + s
            · exact Or.inl ⟨hk, hlt⟩
            · exact Or.inr ⟨hk, not_lt.mp hlt⟩
          · rintro (⟨hk, _⟩ | ⟨hk, _⟩) <;> exact hk
        have hdQ : Disjoint smallQ ((Q \ P).filter (fun k => m₀ + s ≤ k)) := by
          rw [Finset.disjoint_left]; intro k hk1 hk2
          exact not_lt.mpr (Finset.mem_filter.mp hk2).2 (Finset.mem_filter.mp hk1).2
        conv_lhs => rw [hQ_part]
        rw [Finset.sum_union hdQ]
        congr 1
        · by_cases hne : smallQ.Nonempty
          · have hsing : smallQ = {smallQ.min' hne} := by
              ext k
              simp only [Finset.mem_singleton]
              constructor
              · intro hk
                exact Finset.card_le_one.mp hsmallQ_card k hk (smallQ.min' hne) (smallQ.min'_mem hne)
              · rintro rfl; exact smallQ.min'_mem hne
            have hge : m₀ ≤ smallQ.min' hne :=
              hmin _ (Finset.mem_union_right _ (Finset.mem_filter.mp (smallQ.min'_mem hne)).1)
            rw [hsing, Finset.sum_singleton]
            simp only [σ, hne, decide_true, ↓reduceIte, d, ↓reduceDIte]
            rw [← pow_add, show m₀ + (smallQ.min' hne - m₀) = smallQ.min' hne by omega]
          · have hempty : smallQ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
            rw [hempty, Finset.sum_empty]
            simp [σ, hne]
        · have hbijQ : ∑ k ∈ (Q \ P).filter (fun k => m₀ + s ≤ k), z ^ k =
              ∑ j ∈ (Finset.Icc s N).filter (fun j => m₀ + j ∈ Q \ P), z ^ m₀ * z ^ j := by
            refine Finset.sum_bij (fun k _ => k - m₀) ?_ ?_ ?_ ?_
            · intro k hk
              simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
              have hkN : k < N := hQN k (Finset.mem_sdiff.mp hk.1).1
              refine ⟨⟨by omega, by omega⟩, ?_⟩
              convert hk.1 using 1; omega
            · intro k₁ hk₁ k₂ hk₂ heq
              simp only [Finset.mem_filter] at hk₁ hk₂; omega
            · intro j hj
              simp only [Finset.mem_filter, Finset.mem_Icc] at hj
              exact ⟨m₀ + j, Finset.mem_filter.mpr ⟨hj.2, by omega⟩, by omega⟩
            · intro k hk
              simp only [Finset.mem_filter] at hk
              rw [← pow_add, show m₀ + (k - m₀) = k by omega]
          rw [hbijQ, Finset.sum_filter]
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs <;> ring
      rw [hP_sum, hQ_sum]
      have hc_eq : ∑ j ∈ Finset.Icc s N, (c j : ℂ) * z ^ j =
          (∑ j ∈ Finset.Icc s N, (if m₀ + j ∈ P \ Q then (1 : ℂ) else 0) * z ^ j) -
          (∑ j ∈ Finset.Icc s N, (if m₀ + j ∈ Q \ P then (1 : ℂ) else 0) * z ^ j) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [c, Complex.ofReal_sub]
        split_ifs <;> simp
      rw [hc_eq]; ring
    rw [hfac, norm_mul, hz_pow, one_mul]
  have hPN : ∀ k ∈ posSet x w, k < N := fun k hk => by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hk).1; omega
  have hQN : ∀ k ∈ posSet y w, k < N := fun k hk => by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hk).1; omega
  rcases Finset.mem_union.mp hm₀_mem with hm₀A | hm₀B
  · obtain ⟨σ, d, c, hd1, hds, hc, hnorm⟩ :=
      hAB_lead (posSet x w) (posSet y w) (hsep x) (hsep y) hPN hQN hm₀A
        (fun k hk => (A ∪ B).min'_le k hk)
    exact ⟨w, σ, d, c, hd1, hds, hc, hnorm⟩
  · obtain ⟨σ, d, c, hd1, hds, hc, hnorm⟩ :=
      hAB_lead (posSet y w) (posSet x w) (hsep y) (hsep x) hQN hPN hm₀B
        (fun k hk => (A ∪ B).min'_le k (by rw [Finset.union_comm]; exact hk))
    refine ⟨w, σ, d, c, hd1, hds, hc, fun z hz => ?_⟩
    rw [← norm_neg, neg_sub]
    exact hnorm z hz

/- ### Section 4: The Auxiliary Polynomial `h`, Abel Summation, Unit Disk Bound, and Lens Mapping -/

private noncomputable def wLog (j : ℕ) : ℝ :=
  1 / (Real.log ((j : ℝ) + 3)) ^ 2

private noncomputable def aCoeff (j : ℕ) : ℝ :=
  1 / ((j : ℝ) ^ 2 * (Real.log ((j : ℝ) + 3)) ^ 2)

private lemma log_three_gt_one : (1 : ℝ) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  linarith [Real.exp_one_lt_d9]

private lemma log_four_gt_four_thirds : (4 / 3 : ℝ) < Real.log 4 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h1 : Real.exp (4 / 3 : ℝ) ^ 3 = Real.exp 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 : Real.exp 4 = (Real.exp 1) ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h3 : (Real.exp 1) ^ 4 < (2.72 : ℝ) ^ 4 := by
    gcongr; linarith [Real.exp_one_lt_d9]
  have h4 : (2.72 : ℝ) ^ 4 < 4 ^ 3 := by norm_num
  have h5 : Real.exp (4 / 3 : ℝ) ^ 3 < 4 ^ 3 := by linarith
  nlinarith [Real.exp_pos (4 / 3 : ℝ), sq_nonneg (Real.exp (4 / 3 : ℝ) - 4)]

private lemma log_four_lt_three_halves : Real.log 4 < (3 / 2 : ℝ) := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 : Real.exp (3 / 2 : ℝ) ^ 2 = Real.exp 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 : Real.exp 3 = (Real.exp 1) ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h3 : (2.7 : ℝ) ^ 3 < (Real.exp 1) ^ 3 := by
    gcongr; linarith [Real.exp_one_gt_d9]
  have h4 : (4 : ℝ) ^ 2 < (2.7 : ℝ) ^ 3 := by norm_num
  nlinarith [Real.exp_pos (3 / 2 : ℝ)]

private lemma log_five_gt_three_halves : (3 / 2 : ℝ) < Real.log 5 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h1 : Real.exp (3 / 2 : ℝ) ^ 2 = Real.exp 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 : Real.exp 3 = (Real.exp 1) ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h3 : (Real.exp 1) ^ 3 < (2.72 : ℝ) ^ 3 := by
    gcongr; linarith [Real.exp_one_lt_d9]
  have h4 : (2.72 : ℝ) ^ 3 < 5 ^ 2 := by norm_num
  nlinarith [Real.exp_pos (3 / 2 : ℝ)]

private lemma log_add_three_gt_one (j : ℕ) : (1 : ℝ) < Real.log ((j : ℝ) + 3) := by
  have h3 : (3 : ℝ) ≤ (j : ℝ) + 3 := by linarith [Nat.cast_nonneg (α := ℝ) j]
  exact lt_of_lt_of_le log_three_gt_one (Real.log_le_log (by norm_num) h3)

private lemma wLog_pos (j : ℕ) : 0 < wLog j := by
  unfold wLog
  have := log_add_three_gt_one j
  positivity

private lemma wLog_lt_one (j : ℕ) : wLog j < 1 := by
  unfold wLog
  rw [div_lt_one (sq_pos_of_pos (lt_trans zero_lt_one (log_add_three_gt_one j)))]
  nlinarith [log_add_three_gt_one j]

private lemma wLog_anti {i j : ℕ} (h : i ≤ j) : wLog j ≤ wLog i := by
  unfold wLog
  have hi := log_add_three_gt_one i
  have hj := log_add_three_gt_one j
  have hle : Real.log ((i : ℝ) + 3) ≤ Real.log ((j : ℝ) + 3) :=
    Real.log_le_log (by positivity) (by gcongr)
  gcongr

private lemma aCoeff_pos {j : ℕ} (hj : 1 ≤ j) : 0 < aCoeff j := by
  unfold aCoeff
  have hj' : (0 : ℝ) < j := by positivity
  have hl := lt_trans zero_lt_one (log_add_three_gt_one j)
  positivity

private lemma aCoeff_anti {i j : ℕ} (hi : 1 ≤ i) (h : i ≤ j) : aCoeff j ≤ aCoeff i := by
  unfold aCoeff
  have hi' : (0 : ℝ) < i := by positivity
  have hli := lt_trans zero_lt_one (log_add_three_gt_one i)
  have hle : Real.log ((i : ℝ) + 3) ≤ Real.log ((j : ℝ) + 3) :=
    Real.log_le_log (by positivity) (by gcongr)
  gcongr

private lemma sum_inv_sq_tail (a b : ℕ) (ha : 2 ≤ a) :
    ∑ j ∈ Finset.Icc a b, (1 : ℝ) / (j : ℝ) ^ 2 ≤ 1 / ((a : ℝ) - 1) := by
  by_cases hab : a ≤ b
  · have hterm : ∀ j ∈ Finset.Icc a b,
        (1 : ℝ) / (j : ℝ) ^ 2 ≤ 1 / ((j : ℝ) - 1) - 1 / (j : ℝ) := by
      intro j hj
      have hj2 : 2 ≤ j := le_trans ha (Finset.mem_Icc.mp hj).1
      have hj' : (1 : ℝ) < j := by exact_mod_cast (show 1 < j by omega)
      have hsub : (0 : ℝ) < (j : ℝ) - 1 := by linarith
      rw [div_sub_div _ _ hsub.ne' (by linarith)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have htele : ∀ m : ℕ, ∑ k ∈ Finset.range m,
        (1 / (((a + k : ℕ) : ℝ) - 1) - 1 / ((a + k : ℕ) : ℝ)) =
        1 / ((a : ℝ) - 1) - 1 / ((a + m - 1 : ℕ) : ℝ) := by
      intro m
      induction m with
      | zero =>
        simp only [Finset.range_zero, Finset.sum_empty, add_zero]
        have : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
        rw [this, sub_self]
      | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        have h1 : ((a + m - 1 : ℕ) : ℝ) = ((a + m : ℕ) : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        have h2 : ((a + (m + 1) - 1 : ℕ) : ℝ) = ((a + m : ℕ) : ℝ) := by
          have : a + (m + 1) - 1 = a + m := by omega
          rw [this]
        rw [h1, h2]; ring
    calc ∑ j ∈ Finset.Icc a b, (1 : ℝ) / (j : ℝ) ^ 2
        ≤ ∑ j ∈ Finset.Icc a b, (1 / ((j : ℝ) - 1) - 1 / (j : ℝ)) := Finset.sum_le_sum hterm
      _ = ∑ k ∈ Finset.range (b + 1 - a),
            (1 / (((a + k : ℕ) : ℝ) - 1) - 1 / ((a + k : ℕ) : ℝ)) := by
          refine Finset.sum_bij (fun j _ => j - a) ?_ ?_ ?_ ?_
          · intro j hj; simp only [Finset.mem_Icc] at hj; simp only [Finset.mem_range]; omega
          · intro j₁ hj₁ j₂ hj₂ heq; simp only [Finset.mem_Icc] at hj₁ hj₂; omega
          · intro k hk; simp only [Finset.mem_range] at hk
            exact ⟨a + k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
          · intro j hj; simp only [Finset.mem_Icc] at hj
            rw [Nat.add_sub_cancel' hj.1]
      _ = 1 / ((a : ℝ) - 1) - 1 / ((a + (b + 1 - a) - 1 : ℕ) : ℝ) := htele _
      _ ≤ 1 / ((a : ℝ) - 1) := by
          have : (0 : ℝ) ≤ 1 / ((a + (b + 1 - a) - 1 : ℕ) : ℝ) := by positivity
          linarith
  · have hempty : Finset.Icc a b = ∅ := Finset.Icc_eq_empty hab
    rw [hempty, Finset.sum_empty]
    have : (0 : ℝ) < (a : ℝ) - 1 := by
      have : (1 : ℝ) < a := by exact_mod_cast (show 1 < a by omega)
      linarith
    positivity

private noncomputable def sumA (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 r, aCoeff j

private lemma sumA_bounds {r : ℕ} (hr : 1 ≤ r) :
    (1 / 3 : ℝ) < sumA r ∧ sumA r < (43 / 48 : ℝ) := by
  constructor
  · have h1 : aCoeff 1 ≤ sumA r :=
      Finset.single_le_sum (fun j hj => (aCoeff_pos (Finset.mem_Icc.mp hj).1).le)
        (Finset.mem_Icc.mpr ⟨le_rfl, hr⟩)
    have ha1 : (1 / 3 : ℝ) < aCoeff 1 := by
      unfold aCoeff
      simp only [Nat.cast_one, one_pow, one_mul, show (1 : ℝ) + 3 = 4 by norm_num]
      rw [div_lt_div_iff₀ (by norm_num) (sq_pos_of_pos (by linarith [log_four_gt_four_thirds]))]
      nlinarith [log_four_lt_three_halves, log_four_gt_four_thirds]
    linarith
  · have ha1 : aCoeff 1 < 9 / 16 := by
      unfold aCoeff
      simp only [Nat.cast_one, one_pow, one_mul, show (1 : ℝ) + 3 = 4 by norm_num]
      rw [div_lt_div_iff₀ (sq_pos_of_pos (by linarith [log_four_gt_four_thirds])) (by norm_num)]
      nlinarith [log_four_gt_four_thirds]
    have ha2 : aCoeff 2 < 1 / 9 := by
      unfold aCoeff
      simp only [Nat.cast_ofNat, show (2 : ℝ) + 3 = 5 by norm_num]
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [log_five_gt_three_halves]
    have htail : ∑ j ∈ Finset.Icc 3 r, aCoeff j ≤ 2 / 9 := by
      have hterm : ∀ j ∈ Finset.Icc 3 r, aCoeff j ≤ (4 / 9 : ℝ) * (1 / (j : ℝ) ^ 2) := by
        intro j hj
        have hj3 : 3 ≤ j := (Finset.mem_Icc.mp hj).1
        have hlog : (3 / 2 : ℝ) < Real.log ((j : ℝ) + 3) := by
          have : (5 : ℝ) ≤ (j : ℝ) + 3 := by
            have : (3 : ℝ) ≤ j := by exact_mod_cast hj3
            linarith
          exact lt_of_lt_of_le log_five_gt_three_halves (Real.log_le_log (by norm_num) this)
        unfold aCoeff
        have hjpos : (0 : ℝ) < (j : ℝ) ^ 2 := by positivity
        rw [show (4 / 9 : ℝ) * (1 / (j : ℝ) ^ 2) = 1 / ((j : ℝ) ^ 2 * (9 / 4 : ℝ)) by ring]
        gcongr
        nlinarith
      calc ∑ j ∈ Finset.Icc 3 r, aCoeff j
          ≤ ∑ j ∈ Finset.Icc 3 r, (4 / 9 : ℝ) * (1 / (j : ℝ) ^ 2) := Finset.sum_le_sum hterm
        _ = (4 / 9 : ℝ) * ∑ j ∈ Finset.Icc 3 r, (1 : ℝ) / (j : ℝ) ^ 2 := by rw [← Finset.mul_sum]
        _ ≤ (4 / 9 : ℝ) * (1 / ((3 : ℝ) - 1)) := by
            gcongr; exact sum_inv_sq_tail 3 r (by omega)
        _ = 2 / 9 := by norm_num
    by_cases hr1 : r = 1
    · subst hr1; unfold sumA; simp only [Finset.Icc_self, Finset.sum_singleton]; linarith
    · by_cases hr2 : r = 2
      · subst hr2
        have : Finset.Icc 1 2 = {1, 2} := by decide
        unfold sumA; rw [this, Finset.sum_pair (by omega)]; linarith
      · have hsplit : Finset.Icc 1 r = insert 1 (insert 2 (Finset.Icc 3 r)) := by
          ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        unfold sumA
        rw [hsplit, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
        linarith

private noncomputable def lam (r : ℕ) : ℝ := (sumA r)⁻¹

private lemma lam_bounds {r : ℕ} (hr : 1 ≤ r) : (1 : ℝ) < lam r ∧ lam r < 3 := by
  have ⟨hlo, hhi⟩ := sumA_bounds hr
  unfold lam
  constructor
  · rw [one_lt_inv₀ (by linarith)]; linarith
  · rw [inv_lt_comm₀ (by linarith) (by norm_num)]; linarith

private lemma sum_j_aCoeff_le_four (r : ℕ) :
    ∑ j ∈ Finset.Icc 1 r, (j : ℝ) * aCoeff j ≤ 4 := by
  have hterm : ∀ j ∈ Finset.Icc 1 r,
      (j : ℝ) * aCoeff j ≤ 4 * (1 / Real.log ((j : ℝ) + 2) - 1 / Real.log ((j : ℝ) + 3)) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    have hlog2 : (1 : ℝ) < Real.log ((j : ℝ) + 2) := by
      have : (3 : ℝ) ≤ (j : ℝ) + 2 := by linarith
      exact lt_of_lt_of_le log_three_gt_one (Real.log_le_log (by norm_num) this)
    have hlog3 : Real.log ((j : ℝ) + 2) ≤ Real.log ((j : ℝ) + 3) :=
      Real.log_le_log (by linarith) (by linarith)
    have hlog_diff : 1 / ((j : ℝ) + 3) ≤ Real.log ((j : ℝ) + 3) - Real.log ((j : ℝ) + 2) := by
      rw [← Real.log_div (by linarith) (by linarith)]
      have h1 := Real.one_sub_inv_le_log_of_pos (x := ((j : ℝ) + 3) / ((j : ℝ) + 2)) (by positivity)
      have h2 : 1 - (((j : ℝ) + 3) / ((j : ℝ) + 2))⁻¹ = 1 / ((j : ℝ) + 3) := by
        field_simp; ring
      linarith
    have h4j : (j : ℝ) + 3 ≤ 4 * (j : ℝ) := by linarith
    have hstep1 : 1 / (4 * (j : ℝ)) ≤ 1 / ((j : ℝ) + 3) :=
      one_div_le_one_div_of_le (by linarith) h4j
    have hlog3_pos : 0 < Real.log ((j : ℝ) + 3) := by linarith
    have hlog2_pos : 0 < Real.log ((j : ℝ) + 2) := by linarith
    rw [div_sub_div _ _ hlog2_pos.ne' hlog3_pos.ne', one_mul, mul_one]
    unfold aCoeff
    have hsimp : (j : ℝ) * (1 / ((j : ℝ) ^ 2 * Real.log ((j : ℝ) + 3) ^ 2)) =
        1 / ((j : ℝ) * Real.log ((j : ℝ) + 3) ^ 2) := by
      field_simp
    rw [hsimp]
    calc 1 / ((j : ℝ) * Real.log ((j : ℝ) + 3) ^ 2)
        = 4 * (1 / (4 * (j : ℝ))) / (Real.log ((j : ℝ) + 3) * Real.log ((j : ℝ) + 3)) := by
          field_simp
      _ ≤ 4 * (Real.log ((j : ℝ) + 3) - Real.log ((j : ℝ) + 2)) /
            (Real.log ((j : ℝ) + 2) * Real.log ((j : ℝ) + 3)) := by
          gcongr; linarith
      _ = 4 * ((Real.log ((j : ℝ) + 3) - Real.log ((j : ℝ) + 2)) /
            (Real.log ((j : ℝ) + 2) * Real.log ((j : ℝ) + 3))) := by ring
  have htele : ∀ m : ℕ, ∑ k ∈ Finset.range m,
      (1 / Real.log (((k + 1 : ℕ) : ℝ) + 2) - 1 / Real.log (((k + 1 : ℕ) : ℝ) + 3)) =
      1 / Real.log 3 - 1 / Real.log ((m : ℝ) + 3) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  calc ∑ j ∈ Finset.Icc 1 r, (j : ℝ) * aCoeff j
      ≤ ∑ j ∈ Finset.Icc 1 r,
          4 * (1 / Real.log ((j : ℝ) + 2) - 1 / Real.log ((j : ℝ) + 3)) :=
        Finset.sum_le_sum hterm
    _ = 4 * ∑ j ∈ Finset.Icc 1 r,
          (1 / Real.log ((j : ℝ) + 2) - 1 / Real.log ((j : ℝ) + 3)) := by
        rw [← Finset.mul_sum]
    _ = 4 * ∑ k ∈ Finset.range r,
          (1 / Real.log (((k + 1 : ℕ) : ℝ) + 2) - 1 / Real.log (((k + 1 : ℕ) : ℝ) + 3)) := by
        congr 1
        refine Finset.sum_bij (fun j _ => j - 1) ?_ ?_ ?_ ?_
        · intro j hj; simp only [Finset.mem_Icc] at hj; simp only [Finset.mem_range]; omega
        · intro j₁ hj₁ j₂ hj₂ heq; simp only [Finset.mem_Icc] at hj₁ hj₂; omega
        · intro k hk; simp only [Finset.mem_range] at hk
          exact ⟨k + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro j hj; simp only [Finset.mem_Icc] at hj
          rw [Nat.sub_add_cancel hj.1]
    _ = 4 * (1 / Real.log 3 - 1 / Real.log ((r : ℝ) + 3)) := by rw [htele]
    _ ≤ 4 * (1 / 1 - 0) := by
        have h1 : 1 / Real.log 3 ≤ 1 / 1 := one_div_le_one_div_of_le zero_lt_one log_three_gt_one.le
        have h2 : 0 ≤ 1 / Real.log ((r : ℝ) + 3) := by
          have := lt_trans zero_lt_one (log_add_three_gt_one r); positivity
        linarith
    _ = 4 := by norm_num

private lemma quicknotee_tendsto_zero :
    Tendsto (fun r : ℕ =>
      (Real.log ((r : ℝ) + 3)) ^ 2 / (r : ℝ) * ∑ j ∈ Finset.Icc 1 r, (wLog j - wLog r))
      atTop (nhds 0) := by
  have hlog_top : Tendsto (fun r : ℕ => Real.log ((r : ℝ) + 3)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right atTop (3 : ℝ) tendsto_natCast_atTop_atTop)
  have hloglog_div : Tendsto (fun r : ℕ =>
      Real.log (Real.log ((r : ℝ) + 3)) / Real.log ((r : ℝ) + 3)) atTop (nhds 0) := by
    have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact h0.comp hlog_top
  have hinv_log : Tendsto (fun r : ℕ => 1 / Real.log ((r : ℝ) + 3)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hlog_top
  have hbound_top : Tendsto (fun r : ℕ =>
      1 / Real.log ((r : ℝ) + 3) +
      64 * (Real.log (Real.log ((r : ℝ) + 3)) / Real.log ((r : ℝ) + 3)) +
      16 / Real.log ((r : ℝ) + 3)) atTop (nhds 0) := by
    have h := (hinv_log.add (hloglog_div.const_mul 64)).add (hinv_log.const_mul 16)
    have h0 : (0 : ℝ) + 64 * 0 + 16 * 0 = 0 := by norm_num
    rw [h0] at h
    exact h.congr fun r => by ring
  refine squeeze_zero' ?_ ?_ hbound_top
  · filter_upwards [eventually_ge_atTop 1] with r hr
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun j hj => sub_nonneg.mpr (wLog_anti (Finset.mem_Icc.mp hj).2)
  · have hev1 : ∀ᶠ r : ℕ in atTop, (4 : ℝ) ≤ Real.log ((r : ℝ) + 3) :=
      hlog_top.eventually_ge_atTop 4
    have hev2 : ∀ᶠ r : ℕ in atTop,
        4 * Real.log (Real.log ((r : ℝ) + 3)) + 2 ≤ Real.log ((r : ℝ) + 3) / 2 := by
      filter_upwards [hloglog_div.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 16 by norm_num)),
        hlog_top.eventually_ge_atTop 16] with r hr1 hr2
      have hpos : 0 < Real.log ((r : ℝ) + 3) := by linarith
      have := (div_lt_iff₀ hpos).mp hr1
      linarith
    have hev3 : ∀ᶠ r : ℕ in atTop,
        (2 : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 3 ≤ (r : ℝ) := by
      have h0 : Tendsto (fun x : ℝ => (Real.log x) ^ 3 / x) atTop (nhds 0) := by
        simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 3 one_ne_zero
      have h1 := h0.comp (tendsto_atTop_add_const_right atTop (3 : ℝ) tendsto_natCast_atTop_atTop)
      filter_upwards [h1.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num)),
        eventually_ge_atTop 10] with r hr1 hr2
      have hrpos : (0 : ℝ) < (r : ℝ) + 3 := by positivity
      have := (div_lt_iff₀ hrpos).mp hr1
      have hr10 : (10 : ℝ) ≤ r := by exact_mod_cast hr2
      linarith
    filter_upwards [eventually_ge_atTop 10, hev1, hev2, hev3] with r hr10 hL4 hLL hrL3
    set L : ℝ := Real.log ((r : ℝ) + 3)
    set M : ℕ := ⌊(r : ℝ) / L ^ 3⌋₊
    have hLpos : 0 < L := by linarith
    have hrpos : (0 : ℝ) < r := by positivity
    have hM_le_r : M ≤ r := by
      have hL3 : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ (by linarith)
      have : (r : ℝ) / L ^ 3 ≤ r := div_le_self hrpos.le hL3
      exact Nat.floor_le_of_le this
    have hsplit : ∑ j ∈ Finset.Icc 1 r, (wLog j - wLog r) =
        (∑ j ∈ Finset.Icc 1 M, (wLog j - wLog r)) +
        (∑ j ∈ Finset.Icc (M + 1) r, (wLog j - wLog r)) := by
      rw [← Finset.sum_union]
      · congr 1; ext j; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      · rw [Finset.disjoint_left]; intro j h1 h2
        simp only [Finset.mem_Icc] at h1 h2; omega
    have hpart1 : ∑ j ∈ Finset.Icc 1 M, (wLog j - wLog r) ≤ (r : ℝ) / L ^ 3 := by
      calc ∑ j ∈ Finset.Icc 1 M, (wLog j - wLog r)
          ≤ ∑ _j ∈ Finset.Icc 1 M, (1 : ℝ) := by
            refine Finset.sum_le_sum fun j _ => ?_
            linarith [wLog_lt_one j, wLog_pos r]
        _ = (Finset.Icc 1 M).card := by simp
        _ = (M : ℝ) := by simp
        _ ≤ (r : ℝ) / L ^ 3 := Nat.floor_le (by positivity)
    have hpart2 : ∑ j ∈ Finset.Icc (M + 1) r, (wLog j - wLog r) ≤
        (r : ℝ) * (64 * Real.log L / L ^ 3 + 16 / L ^ 3) := by
      have hterm : ∀ j ∈ Finset.Icc (M + 1) r,
          wLog j - wLog r ≤ 64 * Real.log L / L ^ 3 + 16 / L ^ 3 := by
        intro j hj
        have hjM : M + 1 ≤ j := (Finset.mem_Icc.mp hj).1
        have hjr : j ≤ r := (Finset.mem_Icc.mp hj).2
        have hj_gt : (r : ℝ) / L ^ 3 < (j : ℝ) := by
          have := Nat.lt_floor_add_one ((r : ℝ) / L ^ 3)
          have hjM' : ((M : ℝ) + 1) ≤ (j : ℝ) := by exact_mod_cast hjM
          linarith
        have hratio : ((r : ℝ) + 3) / ((j : ℝ) + 3) ≤ 2 * L ^ 3 := by
          rw [div_le_iff₀ (by positivity)]
          have : (r : ℝ) + 3 ≤ 2 * (r : ℝ) := by
            have : (10 : ℝ) ≤ r := by exact_mod_cast hr10
            linarith
          have hmul : (r : ℝ) < (j : ℝ) * L ^ 3 := (div_lt_iff₀ (by positivity)).mp hj_gt
          nlinarith [pow_pos hLpos 3]
        have hdiff_log : L - Real.log ((j : ℝ) + 3) ≤ 3 * Real.log L + 1 := by
          have heq : L - Real.log ((j : ℝ) + 3) = Real.log (((r : ℝ) + 3) / ((j : ℝ) + 3)) :=
            (Real.log_div (by positivity) (by positivity)).symm
          rw [heq]
          calc Real.log (((r : ℝ) + 3) / ((j : ℝ) + 3))
              ≤ Real.log (2 * L ^ 3) := Real.log_le_log (by positivity) hratio
            _ = Real.log 2 + 3 * Real.log L := by
                rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; ring
            _ ≤ 1 + 3 * Real.log L := by
                have : Real.log 2 ≤ 1 := by
                  rw [Real.log_le_iff_le_exp (by norm_num)]; linarith [Real.exp_one_gt_d9]
                linarith
            _ = 3 * Real.log L + 1 := by ring
        have hlogj_ge : L / 2 ≤ Real.log ((j : ℝ) + 3) := by
          have : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
          linarith
        have hlogj_le : Real.log ((j : ℝ) + 3) ≤ L :=
          Real.log_le_log (by positivity) (by gcongr)
        have hlogj_pos : 0 < Real.log ((j : ℝ) + 3) := by linarith
        unfold wLog
        rw [div_sub_div _ _ (sq_pos_of_pos hlogj_pos).ne' (sq_pos_of_pos hLpos).ne', one_mul, mul_one]
        have hnum : L ^ 2 - Real.log ((j : ℝ) + 3) ^ 2 ≤ (3 * Real.log L + 1) * (2 * L) := by
          have hfac : L ^ 2 - Real.log ((j : ℝ) + 3) ^ 2 =
              (L - Real.log ((j : ℝ) + 3)) * (L + Real.log ((j : ℝ) + 3)) := by ring
          rw [hfac]
          have hsum_le : L + Real.log ((j : ℝ) + 3) ≤ 2 * L := by linarith
          have hsub_nn : 0 ≤ L - Real.log ((j : ℝ) + 3) := by linarith
          nlinarith
        have hden : (L / 2) ^ 2 * L ^ 2 ≤ Real.log ((j : ℝ) + 3) ^ 2 * L ^ 2 := by
          gcongr
        have hlogL_nn : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
        calc (L ^ 2 - Real.log ((j : ℝ) + 3) ^ 2) / (Real.log ((j : ℝ) + 3) ^ 2 * L ^ 2)
            ≤ ((3 * Real.log L + 1) * (2 * L)) / ((L / 2) ^ 2 * L ^ 2) := by
              exact div_le_div₀ (by positivity) hnum (by positivity) hden
          _ = 24 * Real.log L / L ^ 3 + 8 / L ^ 3 := by field_simp; ring
          _ ≤ 64 * Real.log L / L ^ 3 + 16 / L ^ 3 := by
              have h1 : 24 * Real.log L / L ^ 3 ≤ 64 * Real.log L / L ^ 3 := by gcongr; norm_num
              have h2 : 8 / L ^ 3 ≤ 16 / L ^ 3 := by gcongr; norm_num
              linarith
      calc ∑ j ∈ Finset.Icc (M + 1) r, (wLog j - wLog r)
          ≤ ∑ _j ∈ Finset.Icc (M + 1) r, (64 * Real.log L / L ^ 3 + 16 / L ^ 3) :=
            Finset.sum_le_sum hterm
        _ = ((Finset.Icc (M + 1) r).card : ℝ) * (64 * Real.log L / L ^ 3 + 16 / L ^ 3) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (r : ℝ) * (64 * Real.log L / L ^ 3 + 16 / L ^ 3) := by
            have hcard : ((Finset.Icc (M + 1) r).card : ℝ) ≤ r := by
              have : (Finset.Icc (M + 1) r).card ≤ r := by simp
              exact_mod_cast this
            have hnn : 0 ≤ 64 * Real.log L / L ^ 3 + 16 / L ^ 3 := by
              have : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
              positivity
            exact mul_le_mul_of_nonneg_right hcard hnn
    rw [hsplit]
    calc L ^ 2 / (r : ℝ) * ((∑ j ∈ Finset.Icc 1 M, (wLog j - wLog r)) +
          (∑ j ∈ Finset.Icc (M + 1) r, (wLog j - wLog r)))
        ≤ L ^ 2 / (r : ℝ) * ((r : ℝ) / L ^ 3 + (r : ℝ) * (64 * Real.log L / L ^ 3 + 16 / L ^ 3)) := by
          gcongr
      _ = 1 / L + 64 * (Real.log L / L) + 16 / L := by
          field_simp [hLpos.ne', hrpos.ne']
          ring

private noncomputable def dVal (r k : ℕ) : ℝ :=
  (∑ j ∈ Finset.Icc 1 k, wLog j) - (∑ j ∈ Finset.Icc (k + 1) r, wLog j)

private noncomputable def rStar (r : ℕ) : ℕ :=
  if h : ((Finset.Icc 1 r).filter fun k => (600 : ℝ) ≤ dVal r k).Nonempty then
    ((Finset.Icc 1 r).filter fun k => (600 : ℝ) ≤ dVal r k).min' h
  else r / 2

private lemma rStar_spec :
    ∀ᶠ r : ℕ in atTop,
      1 ≤ rStar r ∧ rStar r < r ∧ (600 : ℝ) ≤ dVal r (rStar r) ∧ dVal r (rStar r) ≤ 601 := by
  have hgrow : Tendsto (fun r : ℕ => (r : ℝ) / (Real.log ((r : ℝ) + 3)) ^ 2) atTop atTop := by
    have h0 : Tendsto (fun x : ℝ => (Real.log x) ^ 2 / x) atTop (nhds 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
    have h1 := h0.comp (tendsto_atTop_add_const_right atTop (3 : ℝ) tendsto_natCast_atTop_atTop)
    have hinv : Tendsto (fun r : ℕ => ((r : ℝ) + 3) / (Real.log ((r : ℝ) + 3)) ^ 2) atTop atTop := by
      have : ∀ᶠ r : ℕ in atTop, 0 < (Real.log ((r : ℝ) + 3)) ^ 2 / ((r : ℝ) + 3) := by
        filter_upwards [eventually_ge_atTop 1] with r _
        have := lt_trans zero_lt_one (log_add_three_gt_one r)
        positivity
      have h2 := Filter.Tendsto.inv_tendsto_nhdsGT_zero (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h1 this)
      exact h2.congr fun r => by simp [inv_div]
    refine tendsto_atTop_mono' atTop ?_ (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2) hinv)
    filter_upwards [eventually_ge_atTop 10] with r hr
    have hr10 : (10 : ℝ) ≤ r := by exact_mod_cast hr
    have : (1 / 2 : ℝ) * ((r : ℝ) + 3) ≤ r := by linarith
    calc (1 / 2 : ℝ) * (((r : ℝ) + 3) / Real.log ((r : ℝ) + 3) ^ 2)
        = ((1 / 2 : ℝ) * ((r : ℝ) + 3)) / Real.log ((r : ℝ) + 3) ^ 2 := by ring
      _ ≤ (r : ℝ) / Real.log ((r : ℝ) + 3) ^ 2 := by gcongr
  filter_upwards [hgrow.eventually_ge_atTop 1000, eventually_ge_atTop 20] with r hr1000 hr20
  have hsum_r : (1000 : ℝ) ≤ ∑ j ∈ Finset.Icc 1 r, wLog j := by
    calc (1000 : ℝ) ≤ (r : ℝ) / (Real.log ((r : ℝ) + 3)) ^ 2 := hr1000
      _ = ∑ _j ∈ Finset.Icc 1 r, wLog r := by
          rw [Finset.sum_const, nsmul_eq_mul]; unfold wLog; simp [div_eq_mul_inv]
      _ ≤ ∑ j ∈ Finset.Icc 1 r, wLog j := Finset.sum_le_sum fun j hj => wLog_anti (Finset.mem_Icc.mp hj).2
  have hne : ((Finset.Icc 1 r).filter fun k => (600 : ℝ) ≤ dVal r k).Nonempty := by
    refine ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, ?_⟩⟩
    unfold dVal
    have hempty : Finset.Icc (r + 1) r = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hempty, Finset.sum_empty, sub_zero]
    linarith
  have hrs_eq : rStar r = ((Finset.Icc 1 r).filter fun k => (600 : ℝ) ≤ dVal r k).min' hne := by
    simp [rStar, hne]
  have hmem := ((Finset.Icc 1 r).filter fun k => (600 : ℝ) ≤ dVal r k).min'_mem hne
  rw [← hrs_eq] at hmem
  have hmem' := Finset.mem_filter.mp hmem
  have hbounds := Finset.mem_Icc.mp hmem'.1
  have hstep : ∀ k, 1 ≤ k → k ≤ r → dVal r k - dVal r (k - 1) = 2 * wLog k := by
    intro k hk1 hkr
    unfold dVal
    have h1 : Finset.Icc 1 k = insert k (Finset.Icc 1 (k - 1)) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have h2 : Finset.Icc (k - 1 + 1) r = insert k (Finset.Icc (k + 1) r) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [h1, Finset.sum_insert (by simp; omega), h2, Finset.sum_insert (by simp)]
    ring
  have hrs_gt_10 : 10 < rStar r := by
    by_contra hle
    have h1 : ∑ j ∈ Finset.Icc 1 (rStar r), wLog j ≤ 10 := by
      calc ∑ j ∈ Finset.Icc 1 (rStar r), wLog j
          ≤ ∑ _j ∈ Finset.Icc 1 (rStar r), (1 : ℝ) := Finset.sum_le_sum fun j _ => (wLog_lt_one j).le
        _ = (rStar r : ℝ) := by simp
        _ ≤ 10 := by exact_mod_cast (show rStar r ≤ 10 by omega)
    have h2 : dVal r (rStar r) ≤ 10 := by
      unfold dVal
      have : 0 ≤ ∑ j ∈ Finset.Icc (rStar r + 1) r, wLog j :=
        Finset.sum_nonneg fun j _ => (wLog_pos j).le
      linarith
    linarith [hmem'.2]
  have hprev_lt : dVal r (rStar r - 1) < 600 := by
    by_contra hge
    push Not at hge
    have hprev_mem : rStar r - 1 ∈ (Finset.Icc 1 r).filter fun k => (600 : ℝ) ≤ dVal r k :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hge⟩
    have hmin := ((Finset.Icc 1 r).filter fun k => (600 : ℝ) ≤ dVal r k).min'_le (rStar r - 1) hprev_mem
    rw [← hrs_eq] at hmin
    omega
  have hwlog_small : 2 * wLog (rStar r) ≤ 1 := by
    have hge10 : (13 : ℝ) ≤ (rStar r : ℝ) + 3 := by
      have : (10 : ℝ) ≤ rStar r := by exact_mod_cast (show 10 ≤ rStar r by omega)
      linarith
    have hlog13 : (2 : ℝ) < Real.log 13 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have : Real.exp 2 = (Real.exp 1) ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      have : (Real.exp 1) ^ 2 < (2.72 : ℝ) ^ 2 := by gcongr; linarith [Real.exp_one_lt_d9]
      nlinarith
    have hlogrs : (2 : ℝ) < Real.log ((rStar r : ℝ) + 3) :=
      lt_of_lt_of_le hlog13 (Real.log_le_log (by norm_num) hge10)
    unfold wLog
    rw [mul_one_div, div_le_one (sq_pos_of_pos (by linarith))]
    nlinarith
  have hdle : dVal r (rStar r) ≤ 601 := by
    have := hstep (rStar r) hbounds.1 hbounds.2
    linarith
  have hrs_lt_r : rStar r < r := by
    by_contra hge
    have heq : rStar r = r := by omega
    rw [heq] at hdle
    unfold dVal at hdle
    have hempty : Finset.Icc (r + 1) r = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hempty, Finset.sum_empty, sub_zero] at hdle
    linarith
  exact ⟨hbounds.1, hrs_lt_r, hmem'.2, hdle⟩

private lemma rStar_div_tendsto :
    Tendsto (fun r : ℕ => (rStar r : ℝ) / (r : ℝ)) atTop (nhds (1 / 2)) := by
  have hlog2_div : Tendsto (fun r : ℕ => (Real.log ((r : ℝ) + 3)) ^ 2 / (r : ℝ)) atTop (nhds 0) := by
    have h0 : Tendsto (fun x : ℝ => (Real.log x) ^ 2 / x) atTop (nhds 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
    have h1 := h0.comp (tendsto_atTop_add_const_right atTop (3 : ℝ) tendsto_natCast_atTop_atTop)
    refine squeeze_zero' (Eventually.of_forall fun r => by positivity) ?_ (by simpa using h1.const_mul 2)
    filter_upwards [eventually_ge_atTop 10] with r hr
    have hr10 : (10 : ℝ) ≤ r := by exact_mod_cast hr
    have : ((r : ℝ) + 3) ≤ 2 * (r : ℝ) := by linarith
    have hrpos : (0 : ℝ) < r := by linarith
    calc (Real.log ((r : ℝ) + 3)) ^ 2 / (r : ℝ)
        ≤ (Real.log ((r : ℝ) + 3)) ^ 2 / (((r : ℝ) + 3) / 2) := by gcongr; linarith
      _ = 2 * ((Real.log ((r : ℝ) + 3)) ^ 2 / ((r : ℝ) + 3)) := by field_simp
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h1 := Metric.tendsto_atTop.mp quicknotee_tendsto_zero (ε / 2) (by linarith)
  have h2 := Metric.tendsto_atTop.mp hlog2_div (ε / 2000) (by linarith)
  rcases h1 with ⟨N₁, hN₁⟩
  rcases h2 with ⟨N₂, hN₂⟩
  rcases Filter.eventually_atTop.mp rStar_spec with ⟨N₃, hN₃⟩
  refine ⟨max (max N₁ N₂) (max N₃ 1), fun r hr => ?_⟩
  have hr1 : N₁ ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hr
  have hr2 : N₂ ≤ r := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hr
  have hr3 : N₃ ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hr
  have hrpos : (0 : ℝ) < r := by
    have : 1 ≤ r := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hr
    positivity
  obtain ⟨hrs1, hrs_lt, hd_lo, hd_hi⟩ := hN₃ r hr3
  have hq := hN₁ r hr1
  have hl := hN₂ r hr2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg] at hq hl
  · set L : ℝ := Real.log ((r : ℝ) + 3)
    have hLpos : 0 < L := lt_trans zero_lt_one (log_add_three_gt_one r)
    -- Express (2 * rStar/r - 1) in terms of dVal and quicknotee
    have hdiff : |(L ^ 2 / (r : ℝ)) * dVal r (rStar r) - (2 * ((rStar r : ℝ) / (r : ℝ)) - 1)| ≤
        (L ^ 2 / (r : ℝ)) * ∑ j ∈ Finset.Icc 1 r, (wLog j - wLog r) := by
      have heq1 : (L ^ 2 / (r : ℝ)) * ((∑ j ∈ Finset.Icc 1 (rStar r), wLog r) -
            (∑ j ∈ Finset.Icc (rStar r + 1) r, wLog r)) =
          2 * ((rStar r : ℝ) / (r : ℝ)) - 1 := by
        rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
        have hc1 : ((Finset.Icc 1 (rStar r)).card : ℝ) = (rStar r : ℝ) := by simp
        have hc2 : ((Finset.Icc (rStar r + 1) r).card : ℝ) = (r : ℝ) - (rStar r : ℝ) := by
          simp only [Nat.card_Icc]
          rw [show r + 1 - (rStar r + 1) = r - rStar r by omega, Nat.cast_sub (le_of_lt hrs_lt)]
        rw [hc1, hc2]
        unfold wLog
        change (L ^ 2 / (r : ℝ)) * ((rStar r : ℝ) * (1 / L ^ 2) - ((r : ℝ) - (rStar r : ℝ)) * (1 / L ^ 2)) = _
        field_simp [hLpos.ne', hrpos.ne']
        ring
      rw [← heq1, ← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
      gcongr
      unfold dVal
      have hsub_eq : ((∑ j ∈ Finset.Icc 1 (rStar r), wLog j) -
            (∑ j ∈ Finset.Icc (rStar r + 1) r, wLog j)) -
          ((∑ j ∈ Finset.Icc 1 (rStar r), wLog r) -
            (∑ j ∈ Finset.Icc (rStar r + 1) r, wLog r)) =
          (∑ j ∈ Finset.Icc 1 (rStar r), (wLog j - wLog r)) -
          (∑ j ∈ Finset.Icc (rStar r + 1) r, (wLog j - wLog r)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]; ring
      rw [hsub_eq]
      have hsplit : ∑ j ∈ Finset.Icc 1 r, (wLog j - wLog r) =
          (∑ j ∈ Finset.Icc 1 (rStar r), (wLog j - wLog r)) +
          (∑ j ∈ Finset.Icc (rStar r + 1) r, (wLog j - wLog r)) := by
        rw [← Finset.sum_union]
        · congr 1; ext j; simp only [Finset.mem_Icc, Finset.mem_union]; omega
        · rw [Finset.disjoint_left]; intro j h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
      have hnn1 : 0 ≤ ∑ j ∈ Finset.Icc 1 (rStar r), (wLog j - wLog r) :=
        Finset.sum_nonneg fun j hj => sub_nonneg.mpr (wLog_anti (le_trans (Finset.mem_Icc.mp hj).2 hrs_lt.le))
      have hnn2 : 0 ≤ ∑ j ∈ Finset.Icc (rStar r + 1) r, (wLog j - wLog r) :=
        Finset.sum_nonneg fun j hj => sub_nonneg.mpr (wLog_anti (Finset.mem_Icc.mp hj).2)
      rw [hsplit, abs_le]
      constructor <;> linarith
    have hd_term : |(L ^ 2 / (r : ℝ)) * dVal r (rStar r)| < ε / 2 := by
      rw [abs_of_nonneg (mul_nonneg (by positivity) (by linarith))]
      have : L ^ 2 / (r : ℝ) * dVal r (rStar r) ≤ (L ^ 2 / (r : ℝ)) * 601 :=
        mul_le_mul_of_nonneg_left hd_hi (by positivity)
      linarith
    rw [Real.dist_eq]
    have htri : |2 * ((rStar r : ℝ) / (r : ℝ)) - 1| < ε := by
      have := abs_sub_le (2 * ((rStar r : ℝ) / (r : ℝ)) - 1) ((L ^ 2 / (r : ℝ)) * dVal r (rStar r)) 0
      rw [sub_zero, sub_zero, abs_sub_comm (2 * ((rStar r : ℝ) / (r : ℝ)) - 1)] at this
      linarith
    have hhalf : |(rStar r : ℝ) / (r : ℝ) - 1 / 2| = |2 * ((rStar r : ℝ) / (r : ℝ)) - 1| / 2 := by
      have : (rStar r : ℝ) / (r : ℝ) - 1 / 2 = (2 * ((rStar r : ℝ) / (r : ℝ)) - 1) / 2 := by ring
      rw [this, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  · positivity
  · exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun j hj => sub_nonneg.mpr (wLog_anti (Finset.mem_Icc.mp hj).2))

private noncomputable def epsSign (r j : ℕ) : ℝ :=
  if j ≤ rStar r then 1 else -1

private noncomputable def dCoeff (r j : ℕ) : ℝ :=
  lam r * aCoeff j

private noncomputable def invTildeLam (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 r, epsSign r j * dCoeff r j

private noncomputable def tildeLam (r : ℕ) : ℝ :=
  (invTildeLam r)⁻¹

private noncomputable def tildeH (r : ℕ) (z : ℂ) : ℂ :=
  (tildeLam r : ℂ) * ∑ j ∈ Finset.Icc 1 r, ((epsSign r j * dCoeff r j : ℝ) : ℂ) * z ^ j

private lemma tail_aCoeff_bound :
    ∀ᶠ r : ℕ in atTop,
      ∑ j ∈ Finset.Icc (rStar r + 1) r, aCoeff j ≤ 12 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2) := by
  have hr_third : ∀ᶠ r : ℕ in atTop, (r : ℝ) / 3 ≤ (rStar r : ℝ) := by
    have := rStar_div_tendsto.eventually (Ioi_mem_nhds (show (1 / 3 : ℝ) < 1 / 2 by norm_num))
    filter_upwards [this, eventually_ge_atTop 1] with r hr hr1
    have hrpos : (0 : ℝ) < r := by positivity
    have := (lt_div_iff₀ hrpos).mp hr
    linarith
  have hlog_half : ∀ᶠ r : ℕ in atTop,
      Real.log ((r : ℝ) + 3) / 2 ≤ Real.log ((rStar r : ℝ) + 3) := by
    have hlog_top : Tendsto (fun r : ℕ => Real.log ((r : ℝ) + 3)) atTop atTop :=
      Real.tendsto_log_atTop.comp
        (tendsto_atTop_add_const_right atTop (3 : ℝ) tendsto_natCast_atTop_atTop)
    filter_upwards [hr_third, hlog_top.eventually_ge_atTop (4 * Real.log 3), eventually_ge_atTop 10] with
      r hr3 hL hr10
    have hrpos : (0 : ℝ) < r := by positivity
    have h1 : ((r : ℝ) + 3) / 3 ≤ (rStar r : ℝ) + 3 := by linarith
    have h2 : Real.log (((r : ℝ) + 3) / 3) ≤ Real.log ((rStar r : ℝ) + 3) :=
      Real.log_le_log (by positivity) h1
    rw [Real.log_div (by positivity) (by norm_num)] at h2
    have hlog3 : 0 < Real.log 3 := lt_trans zero_lt_one log_three_gt_one
    linarith
  filter_upwards [rStar_spec, hr_third, hlog_half, eventually_ge_atTop 10] with r hrs hr3 hlog hr10
  have hrs_pos : 1 ≤ rStar r := hrs.1
  have hterm : ∀ j ∈ Finset.Icc (rStar r + 1) r,
      aCoeff j ≤ (1 / (Real.log ((rStar r : ℝ) + 3)) ^ 2) * (1 / (j : ℝ) ^ 2) := by
    intro j hj
    have hj_ge : rStar r ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
    have hj1 : 1 ≤ j := by omega
    unfold aCoeff
    have h1 : Real.log ((rStar r : ℝ) + 3) ≤ Real.log ((j : ℝ) + 3) :=
      Real.log_le_log (by positivity) (by gcongr)
    have hpos : 0 < Real.log ((rStar r : ℝ) + 3) := lt_trans zero_lt_one (log_add_three_gt_one _)
    have hjpos : (0 : ℝ) < (j : ℝ) ^ 2 := by positivity
    rw [one_div_mul_one_div, mul_comm ((Real.log ((rStar r : ℝ) + 3)) ^ 2)]
    gcongr
  calc ∑ j ∈ Finset.Icc (rStar r + 1) r, aCoeff j
      ≤ ∑ j ∈ Finset.Icc (rStar r + 1) r,
          (1 / (Real.log ((rStar r : ℝ) + 3)) ^ 2) * (1 / (j : ℝ) ^ 2) := Finset.sum_le_sum hterm
    _ = (1 / (Real.log ((rStar r : ℝ) + 3)) ^ 2) *
          ∑ j ∈ Finset.Icc (rStar r + 1) r, (1 : ℝ) / (j : ℝ) ^ 2 := by rw [← Finset.mul_sum]
    _ ≤ (1 / (Real.log ((rStar r : ℝ) + 3)) ^ 2) * (1 / (((rStar r + 1 : ℕ) : ℝ) - 1)) := by
        gcongr; exact sum_inv_sq_tail (rStar r + 1) r (by omega)
    _ = 1 / ((rStar r : ℝ) * (Real.log ((rStar r : ℝ) + 3)) ^ 2) := by
        have hrs_ne : (rStar r : ℝ) ≠ 0 := by positivity
        push_cast
        rw [add_sub_cancel_right]
        field_simp [hrs_ne]
    _ ≤ 1 / (((r : ℝ) / 3) * (Real.log ((r : ℝ) + 3) / 2) ^ 2) := by
        have hLpos : 0 < Real.log ((r : ℝ) + 3) := lt_trans zero_lt_one (log_add_three_gt_one r)
        have hrpos : (0 : ℝ) < r := by positivity
        gcongr
    _ = 12 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2) := by ring

private lemma tildeLam_bounds :
    ∀ᶠ r : ℕ in atTop,
      1 - 72 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2) ≤ invTildeLam r ∧
      (1 : ℝ) < tildeLam r ∧ tildeLam r ≤ 2 := by
  filter_upwards [rStar_spec, tail_aCoeff_bound, eventually_ge_atTop 200] with r hrs htail hr200
  have hr1 : 1 ≤ r := by omega
  have ⟨hlam_lo, hlam_hi⟩ := lam_bounds hr1
  have hsum_d : ∑ j ∈ Finset.Icc 1 r, dCoeff r j = 1 := by
    unfold dCoeff lam
    rw [← Finset.mul_sum]
    have hpos : 0 < sumA r := lt_trans (by norm_num) (sumA_bounds hr1).1
    exact inv_mul_cancel₀ hpos.ne'
  have hinv_eq : invTildeLam r = 1 - 2 * ∑ j ∈ Finset.Icc (rStar r + 1) r, dCoeff r j := by
    have hsplit : Finset.Icc 1 r = Finset.Icc 1 (rStar r) ∪ Finset.Icc (rStar r + 1) r := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdis : Disjoint (Finset.Icc 1 (rStar r)) (Finset.Icc (rStar r + 1) r) := by
      rw [Finset.disjoint_left]; intro j h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
    unfold invTildeLam
    rw [hsplit, Finset.sum_union hdis]
    have h1 : ∑ j ∈ Finset.Icc 1 (rStar r), epsSign r j * dCoeff r j =
        ∑ j ∈ Finset.Icc 1 (rStar r), dCoeff r j := by
      refine Finset.sum_congr rfl fun j hj => ?_
      simp [epsSign, (Finset.mem_Icc.mp hj).2]
    have h2 : ∑ j ∈ Finset.Icc (rStar r + 1) r, epsSign r j * dCoeff r j =
        -(∑ j ∈ Finset.Icc (rStar r + 1) r, dCoeff r j) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have : ¬(j ≤ rStar r) := by have := (Finset.mem_Icc.mp hj).1; omega
      simp [epsSign, this]
    rw [h1, h2]
    have htot := hsum_d
    rw [hsplit, Finset.sum_union hdis] at htot
    linarith
  have htail_d : ∑ j ∈ Finset.Icc (rStar r + 1) r, dCoeff r j ≤
      36 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2) := by
    unfold dCoeff
    rw [← Finset.mul_sum]
    calc lam r * ∑ j ∈ Finset.Icc (rStar r + 1) r, aCoeff j
        ≤ 3 * (12 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2)) := by
          have hnn : 0 ≤ ∑ j ∈ Finset.Icc (rStar r + 1) r, aCoeff j :=
            Finset.sum_nonneg fun j hj => (aCoeff_pos (by have := (Finset.mem_Icc.mp hj).1; omega)).le
          nlinarith
      _ = 36 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2) := by ring
  have htail_pos : 0 < ∑ j ∈ Finset.Icc (rStar r + 1) r, dCoeff r j := by
    apply Finset.sum_pos
    · intro j hj; unfold dCoeff
      exact mul_pos (by linarith) (aCoeff_pos (by have := (Finset.mem_Icc.mp hj).1; omega))
    · exact ⟨r, Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩⟩
  have hinv_lo : 1 - 72 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2) ≤ invTildeLam r := by
    have : 2 * (36 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2)) =
        72 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2) := by ring
    linarith
  have hinv_half : (1 / 2 : ℝ) ≤ invTildeLam r := by
    have hr200' : (200 : ℝ) ≤ r := by exact_mod_cast hr200
    have hL1 : (1 : ℝ) < Real.log ((r : ℝ) + 3) := log_add_three_gt_one r
    have hden : (200 : ℝ) ≤ (r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2 := by nlinarith
    have hfrac : 72 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2) ≤ 72 / 200 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
    linarith
  refine ⟨hinv_lo, ?_, ?_⟩
  · unfold tildeLam
    rw [one_lt_inv₀ (by linarith)]
    linarith
  · unfold tildeLam
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith

private lemma tildeH_zero (r : ℕ) : tildeH r 0 = 0 := by
  unfold tildeH
  have : ∑ j ∈ Finset.Icc 1 r, ((epsSign r j * dCoeff r j : ℝ) : ℂ) * (0 : ℂ) ^ j = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj1 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
    simp [zero_pow hj1]
  rw [this, mul_zero]

private lemma tildeH_one {r : ℕ} (hinv : invTildeLam r ≠ 0) : tildeH r 1 = 1 := by
  unfold tildeH tildeLam
  simp only [one_pow, mul_one]
  rw [← Complex.ofReal_sum]
  change (((invTildeLam r)⁻¹ : ℝ) : ℂ) * (invTildeLam r : ℂ) = 1
  rw [← Complex.ofReal_mul, inv_mul_cancel₀ hinv, Complex.ofReal_one]

private lemma norm_tildeH_conj (r : ℕ) (z : ℂ) :
    ‖tildeH r (starRingEnd ℂ z)‖ = ‖tildeH r z‖ := by
  have hconj : tildeH r (starRingEnd ℂ z) = starRingEnd ℂ (tildeH r z) := by
    unfold tildeH
    rw [map_mul, Complex.conj_ofReal, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, Complex.conj_ofReal, map_pow]
  rw [hconj, Complex.norm_conj]

/-- Discrete Abel summation by parts on `Icc 1 m`. -/
private lemma abel_sum_Icc (a : ℕ → ℝ) (z : ℂ) (m : ℕ) (hm : 1 ≤ m) :
    ∑ j ∈ Finset.Icc 1 m, (a j : ℂ) * z ^ j =
      (a m : ℂ) * (∑ j ∈ Finset.Icc 1 m, z ^ j) +
      ∑ k ∈ Finset.Icc 1 (m - 1), ((a k - a (k + 1) : ℝ) : ℂ) * (∑ j ∈ Finset.Icc 1 k, z ^ j) := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hm0 : m = 0
    · subst hm0; simp
    · have hm1 : 1 ≤ m := by omega
      have ih' := ih hm1
      have h1 : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have h2 : Finset.Icc 1 m = insert m (Finset.Icc 1 (m - 1)) := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [h1, Finset.sum_insert (by simp), Finset.sum_insert (by simp), ih']
      simp only [Nat.add_sub_cancel]
      have hsplit2 : ∑ k ∈ Finset.Icc 1 m, ((a k - a (k + 1) : ℝ) : ℂ) * (∑ j ∈ Finset.Icc 1 k, z ^ j) =
          ((a m - a (m + 1) : ℝ) : ℂ) * (∑ j ∈ Finset.Icc 1 m, z ^ j) +
          ∑ k ∈ Finset.Icc 1 (m - 1), ((a k - a (k + 1) : ℝ) : ℂ) * (∑ j ∈ Finset.Icc 1 k, z ^ j) := by
        conv_lhs => rw [h2]; rw [Finset.sum_insert (by simp; omega)]
      rw [hsplit2]
      push_cast
      ring

private lemma norm_geom_sum_le_inv_u {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1 / 2) (k : ℕ) :
    ‖∑ j ∈ Finset.Icc 1 k, Complex.exp (2 * Real.pi * u * I) ^ j‖ ≤ 1 / u := by
  set z : ℂ := Complex.exp (2 * Real.pi * u * I)
  have hz_norm : ‖z‖ = 1 := by
    simp only [z]
    rw [show (2 : ℂ) * Real.pi * u * I = ((2 * Real.pi * u : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have h1z_norm : 4 * u ≤ ‖1 - z‖ := by
    have hsq : ‖1 - z‖ ^ 2 = (2 * Real.sin (Real.pi * u)) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      have hz_eq : z = Complex.exp (((2 * Real.pi * u : ℝ) : ℂ) * I) := by
        simp only [z]; congr 1; push_cast; ring
      have hre : (1 - z).re = 1 - Real.cos (2 * Real.pi * u) := by
        rw [Complex.sub_re, Complex.one_re, hz_eq, Complex.exp_ofReal_mul_I_re]
      have him : (1 - z).im = -Real.sin (2 * Real.pi * u) := by
        rw [Complex.sub_im, Complex.one_im, hz_eq, Complex.exp_ofReal_mul_I_im, zero_sub]
      rw [Complex.normSq_apply, hre, him]
      have hcos2 := Real.cos_two_mul (Real.pi * u)
      have hsc := Real.sin_sq_add_cos_sq (Real.pi * u)
      have hsc2 := Real.sin_sq_add_cos_sq (2 * Real.pi * u)
      have h2pi : 2 * (Real.pi * u) = 2 * Real.pi * u := by ring
      rw [h2pi] at hcos2
      nlinarith
    have hsin_nn : 0 ≤ Real.sin (Real.pi * u) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])
    have hnorm_eq : ‖1 - z‖ = 2 * Real.sin (Real.pi * u) := by
      nlinarith [norm_nonneg (1 - z)]
    rw [hnorm_eq]
    have hms := Real.mul_le_sin (by positivity) (by nlinarith [Real.pi_pos] : Real.pi * u ≤ Real.pi / 2)
    have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
    have heq : 2 * (2 / Real.pi * (Real.pi * u)) = 4 * u := by field_simp [hpi]; ring
    linarith
  have h1z_ne : 1 - z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h1z_norm; linarith
  have hgeom : (1 - z) * ∑ j ∈ Finset.Icc 1 k, z ^ j = z * (1 - z ^ k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [h1, Finset.sum_insert (by simp), mul_add, ih]
      ring
  have hmul : ‖1 - z‖ * ‖∑ j ∈ Finset.Icc 1 k, z ^ j‖ ≤ 2 := by
    rw [← norm_mul, hgeom, norm_mul, hz_norm, one_mul]
    calc ‖1 - z ^ k‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ k‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [norm_one, norm_pow, hz_norm, one_pow]
      _ = 2 := by norm_num
  have h1z_pos : 0 < ‖1 - z‖ := lt_of_lt_of_le (by linarith) h1z_norm
  calc ‖∑ j ∈ Finset.Icc 1 k, z ^ j‖
      ≤ 2 / ‖1 - z‖ := (le_div_iff₀' h1z_pos).mpr hmul
    _ ≤ 2 / (4 * u) := div_le_div_of_nonneg_left (by norm_num) (by linarith) h1z_norm
    _ ≤ 1 / u := by
        rw [div_le_div_iff₀ (by linarith) hu0]; linarith

private lemma abel_bound_partial_sum {m : ℕ} {u : ℝ} (hm : 1 ≤ m) (hu0 : 0 < u) (hu1 : u ≤ 1 / 2)
    (hKu : ⌊3 / u⌋₊ + 1 < m) :
    ‖∑ j ∈ Finset.Icc 1 m, (aCoeff j : ℂ) * Complex.exp (2 * Real.pi * u * I) ^ j‖ ≤
      (∑ j ∈ Finset.Icc 1 m, aCoeff j) -
      u / (8 * (Real.log ((m : ℝ) + 3)) ^ 2) + 1 / ((m : ℝ) * (Real.log ((m : ℝ) + 3)) ^ 2) := by
  set z : ℂ := Complex.exp (2 * Real.pi * u * I)
  set K : ℕ := ⌊3 / u⌋₊
  have habel := abel_sum_Icc aCoeff z m hm
  have habel1 : ∑ j ∈ Finset.Icc 1 m, aCoeff j =
      aCoeff m * m + ∑ k ∈ Finset.Icc 1 (m - 1), (aCoeff k - aCoeff (k + 1)) * k := by
    have h := abel_sum_Icc aCoeff 1 m hm
    simp only [one_pow, mul_one, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at h
    have hre := congrArg Complex.re h
    simp only [Complex.re_sum, Complex.ofReal_re, Complex.add_re, Complex.mul_re,
      Complex.natCast_re, Complex.natCast_im, Complex.ofReal_im, mul_zero, sub_zero] at hre
    exact hre
  have hdiff_nn : ∀ k ∈ Finset.Icc 1 (m - 1), 0 ≤ aCoeff k - aCoeff (k + 1) := fun k hk =>
    sub_nonneg.mpr (aCoeff_anti (Finset.mem_Icc.mp hk).1 (by omega))
  have hnorm_sum_k : ∀ k : ℕ, ‖∑ j ∈ Finset.Icc 1 k, z ^ j‖ ≤ (k : ℝ) := fun k => by
    calc ‖∑ j ∈ Finset.Icc 1 k, z ^ j‖
        ≤ ∑ j ∈ Finset.Icc 1 k, ‖z ^ j‖ := norm_sum_le _ _
      _ = ∑ _j ∈ Finset.Icc 1 k, (1 : ℝ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [norm_pow]
          have : ‖z‖ = 1 := by
            simp only [z]
            rw [show (2 : ℂ) * Real.pi * u * I = ((2 * Real.pi * u : ℝ) : ℂ) * I by push_cast; ring]
            exact Complex.norm_exp_ofReal_mul_I _
          rw [this, one_pow]
      _ = (k : ℝ) := by simp
  have hK1 : 1 ≤ K := by
    have : (6 : ℝ) ≤ 3 / u := by rw [le_div_iff₀ hu0]; linarith
    have : 6 ≤ K := Nat.le_floor this
    omega
  have hsplit : Finset.Icc 1 (m - 1) = Finset.Icc 1 (K - 1) ∪ Finset.Icc K (m - 1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdis : Disjoint (Finset.Icc 1 (K - 1)) (Finset.Icc K (m - 1)) := by
    rw [Finset.disjoint_left]; intro k h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
  have htri : ‖∑ j ∈ Finset.Icc 1 m, (aCoeff j : ℂ) * z ^ j‖ ≤
      (∑ j ∈ Finset.Icc 1 m, aCoeff j) -
      ∑ k ∈ Finset.Icc K (m - 1), (aCoeff k - aCoeff (k + 1)) * ((k : ℝ) - 1 / u) := by
    rw [habel]
    calc ‖(aCoeff m : ℂ) * (∑ j ∈ Finset.Icc 1 m, z ^ j) +
          ∑ k ∈ Finset.Icc 1 (m - 1), ((aCoeff k - aCoeff (k + 1) : ℝ) : ℂ) *
            (∑ j ∈ Finset.Icc 1 k, z ^ j)‖
        ≤ ‖(aCoeff m : ℂ) * (∑ j ∈ Finset.Icc 1 m, z ^ j)‖ +
          ∑ k ∈ Finset.Icc 1 (m - 1),
            ‖((aCoeff k - aCoeff (k + 1) : ℝ) : ℂ) * (∑ j ∈ Finset.Icc 1 k, z ^ j)‖ :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
      _ ≤ aCoeff m * m +
          ((∑ k ∈ Finset.Icc 1 (K - 1), (aCoeff k - aCoeff (k + 1)) * k) +
           (∑ k ∈ Finset.Icc K (m - 1), (aCoeff k - aCoeff (k + 1)) * (1 / u))) := by
          apply add_le_add
          · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (aCoeff_pos hm).le]
            exact mul_le_mul_of_nonneg_left (hnorm_sum_k m) (aCoeff_pos hm).le
          · rw [hsplit, Finset.sum_union hdis]
            apply add_le_add
            · refine Finset.sum_le_sum fun k hk => ?_
              have hk' : k ∈ Finset.Icc 1 (m - 1) := by
                simp only [Finset.mem_Icc] at hk ⊢; omega
              rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hdiff_nn k hk')]
              exact mul_le_mul_of_nonneg_left (hnorm_sum_k k) (hdiff_nn k hk')
            · refine Finset.sum_le_sum fun k hk => ?_
              have hk' : k ∈ Finset.Icc 1 (m - 1) := by
                simp only [Finset.mem_Icc] at hk ⊢; omega
              rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hdiff_nn k hk')]
              exact mul_le_mul_of_nonneg_left (norm_geom_sum_le_inv_u hu0 hu1 k) (hdiff_nn k hk')
      _ = (∑ j ∈ Finset.Icc 1 m, aCoeff j) -
          ∑ k ∈ Finset.Icc K (m - 1), (aCoeff k - aCoeff (k + 1)) * ((k : ℝ) - 1 / u) := by
          rw [habel1, hsplit, Finset.sum_union hdis]
          have hsub : ∑ k ∈ Finset.Icc K (m - 1), (aCoeff k - aCoeff (k + 1)) * ((k : ℝ) - 1 / u) =
              (∑ k ∈ Finset.Icc K (m - 1), (aCoeff k - aCoeff (k + 1)) * k) -
              (∑ k ∈ Finset.Icc K (m - 1), (aCoeff k - aCoeff (k + 1)) * (1 / u)) := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun k _ => by ring
          linarith
  -- Lower bound the subtracted sum by Abel summation + telescoping
  have hlower : u / (8 * (Real.log ((m : ℝ) + 3)) ^ 2) - 1 / ((m : ℝ) * (Real.log ((m : ℝ) + 3)) ^ 2) ≤
      ∑ k ∈ Finset.Icc K (m - 1), (aCoeff k - aCoeff (k + 1)) * ((k : ℝ) - 1 / u) := by
    have hhalf_k : ∀ k ∈ Finset.Icc K (m - 1),
        (1 / 2 : ℝ) * ((aCoeff k - aCoeff (k + 1)) * k) ≤
          (aCoeff k - aCoeff (k + 1)) * ((k : ℝ) - 1 / u) := by
      intro k hk
      have hk_ge : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).1
      have hK_lo : 3 / u - 1 < (K : ℝ) := by
        have := Nat.lt_floor_add_one (3 / u); linarith
      have h1u : (2 : ℝ) ≤ 1 / u := by rw [le_div_iff₀ hu0]; linarith
      have h2u : 2 / u ≤ 3 / u - 1 := by
        have : 3 / u - 2 / u = 1 / u := by ring
        linarith
      have hk_2u : 2 / u ≤ (k : ℝ) := by linarith
      have hk_half : (1 / 2 : ℝ) * (k : ℝ) ≤ (k : ℝ) - 1 / u := by
        have : 2 * (1 / u) = 2 / u := by ring
        linarith
      have hdiff : 0 ≤ aCoeff k - aCoeff (k + 1) :=
        hdiff_nn k (by simp only [Finset.mem_Icc] at hk ⊢; omega)
      nlinarith
    have habel_rev : ∑ k ∈ Finset.Icc K (m - 1), (aCoeff k - aCoeff (k + 1)) * (k : ℝ) =
        (K : ℝ) * aCoeff K + (∑ k ∈ Finset.Icc (K + 1) (m - 1), aCoeff k) -
        ((m - 1 : ℕ) : ℝ) * aCoeff m := by
      have hlen : K ≤ m - 1 := by omega
      suffices ∀ t : ℕ, ∑ k ∈ Finset.Icc K (K + t), (aCoeff k - aCoeff (k + 1)) * (k : ℝ) =
          (K : ℝ) * aCoeff K + (∑ k ∈ Finset.Icc (K + 1) (K + t), aCoeff k) -
          ((K + t : ℕ) : ℝ) * aCoeff (K + t + 1) by
        have h := this (m - 1 - K)
        have heq1 : K + (m - 1 - K) = m - 1 := by omega
        have heq2 : m - 1 + 1 = m := by omega
        rw [heq1, heq2] at h
        exact h
      intro t
      induction t with
      | zero =>
        simp only [add_zero, Finset.Icc_self, Finset.sum_singleton]
        have hempty : Finset.Icc (K + 1) K = ∅ := Finset.Icc_eq_empty (by omega)
        rw [hempty, Finset.sum_empty]
        ring
      | succ t ih =>
        have h1 : Finset.Icc K (K + (t + 1)) = insert (K + (t + 1)) (Finset.Icc K (K + t)) := by
          ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have h2 : Finset.Icc (K + 1) (K + (t + 1)) =
            insert (K + (t + 1)) (Finset.Icc (K + 1) (K + t)) := by
          ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [h1, Finset.sum_insert (by simp), ih, h2, Finset.sum_insert (by simp)]
        have : K + t + 1 = K + (t + 1) := by omega
        rw [this]
        push_cast
        ring
    have htele_lo : (1 / (Real.log ((m : ℝ) + 3)) ^ 2) * (1 / ((K : ℝ) + 1) - 1 / (m : ℝ)) ≤
        ∑ k ∈ Finset.Icc (K + 1) (m - 1), aCoeff k := by
      have hterm : ∀ k ∈ Finset.Icc (K + 1) (m - 1),
          (1 / (Real.log ((m : ℝ) + 3)) ^ 2) * (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) ≤ aCoeff k := by
        intro k hk
        have hk1 : 1 ≤ k := by have := (Finset.mem_Icc.mp hk).1; omega
        have hkm : k ≤ m := by have := (Finset.mem_Icc.mp hk).2; omega
        have hkpos : (0 : ℝ) < k := by positivity
        have hlog : Real.log ((k : ℝ) + 3) ≤ Real.log ((m : ℝ) + 3) :=
          Real.log_le_log (by positivity) (by gcongr)
        have hlogk : 0 < Real.log ((k : ℝ) + 3) := lt_trans zero_lt_one (log_add_three_gt_one k)
        have hfrac : 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) ≤ 1 / (k : ℝ) ^ 2 := by
          rw [div_sub_div _ _ hkpos.ne' (by positivity), one_mul, mul_one,
            div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        have hsub_nn : 0 ≤ 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) :=
          sub_nonneg.mpr (one_div_le_one_div_of_le hkpos (by linarith))
        unfold aCoeff
        calc (1 / (Real.log ((m : ℝ) + 3)) ^ 2) * (1 / (k : ℝ) - 1 / ((k : ℝ) + 1))
            ≤ (1 / (Real.log ((k : ℝ) + 3)) ^ 2) * (1 / (k : ℝ) ^ 2) := by
              gcongr
          _ = 1 / ((k : ℝ) ^ 2 * (Real.log ((k : ℝ) + 3)) ^ 2) := by ring
      have htele : ∀ t : ℕ, ∑ j ∈ Finset.range t,
          (1 / ((K + 1 + j : ℕ) : ℝ) - 1 / (((K + 1 + j : ℕ) : ℝ) + 1)) =
          1 / ((K + 1 : ℕ) : ℝ) - 1 / ((K + 1 + t : ℕ) : ℝ) := by
        intro t
        induction t with
        | zero => simp
        | succ t ih =>
          rw [Finset.sum_range_succ, ih]
          push_cast; ring
      calc (1 / (Real.log ((m : ℝ) + 3)) ^ 2) * (1 / ((K : ℝ) + 1) - 1 / (m : ℝ))
          = (1 / (Real.log ((m : ℝ) + 3)) ^ 2) *
              (1 / ((K + 1 : ℕ) : ℝ) - 1 / ((K + 1 + (m - 1 - K) : ℕ) : ℝ)) := by
            have : K + 1 + (m - 1 - K) = m := by omega
            rw [this]; push_cast; rfl
        _ = (1 / (Real.log ((m : ℝ) + 3)) ^ 2) *
              ∑ j ∈ Finset.range (m - 1 - K),
                (1 / ((K + 1 + j : ℕ) : ℝ) - 1 / (((K + 1 + j : ℕ) : ℝ) + 1)) := by
            rw [htele]
        _ = ∑ k ∈ Finset.Icc (K + 1) (m - 1),
              (1 / (Real.log ((m : ℝ) + 3)) ^ 2) * (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_bij (fun j _ => K + 1 + j) ?_ ?_ ?_ ?_
            · intro j hj; simp only [Finset.mem_range] at hj; simp only [Finset.mem_Icc]; omega
            · intro j₁ _ j₂ _ heq; omega
            · intro k hk; simp only [Finset.mem_Icc] at hk
              exact ⟨k - (K + 1), Finset.mem_range.mpr (by omega), by omega⟩
            · intro j _; rfl
        _ ≤ ∑ k ∈ Finset.Icc (K + 1) (m - 1), aCoeff k := Finset.sum_le_sum hterm
    have hK_hi : (K : ℝ) + 1 ≤ 4 / u := by
      have hfl : (K : ℝ) ≤ 3 / u := Nat.floor_le (by positivity)
      have h1u : (1 : ℝ) ≤ 1 / u := by rw [le_div_iff₀ hu0]; linarith
      have : 3 / u + 1 / u = 4 / u := by ring
      linarith
    have hinvK : u / 4 ≤ 1 / ((K : ℝ) + 1) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      have := (le_div_iff₀ hu0).mp hK_hi
      linarith
    have hm_term : ((m - 1 : ℕ) : ℝ) * aCoeff m ≤ 1 / ((m : ℝ) * (Real.log ((m : ℝ) + 3)) ^ 2) := by
      unfold aCoeff
      have hm1 : ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.sub_le m 1
      have hmpos : (0 : ℝ) < m := by positivity
      have hLpos : 0 < Real.log ((m : ℝ) + 3) := lt_trans zero_lt_one (log_add_three_gt_one m)
      calc ((m - 1 : ℕ) : ℝ) * (1 / ((m : ℝ) ^ 2 * (Real.log ((m : ℝ) + 3)) ^ 2))
          ≤ (m : ℝ) * (1 / ((m : ℝ) ^ 2 * (Real.log ((m : ℝ) + 3)) ^ 2)) := by gcongr
        _ = 1 / ((m : ℝ) * (Real.log ((m : ℝ) + 3)) ^ 2) := by field_simp
    have hKa_nn : 0 ≤ (K : ℝ) * aCoeff K := mul_nonneg (Nat.cast_nonneg _) (aCoeff_pos hK1).le
    have hsum_ge : ∑ k ∈ Finset.Icc K (m - 1), (aCoeff k - aCoeff (k + 1)) * ((k : ℝ) - 1 / u) ≥
        (1 / 2 : ℝ) * ∑ k ∈ Finset.Icc K (m - 1), (aCoeff k - aCoeff (k + 1)) * (k : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hhalf_k
    have hLpos : 0 < (Real.log ((m : ℝ) + 3)) ^ 2 := sq_pos_of_pos (lt_trans zero_lt_one (log_add_three_gt_one m))
    have hcomb : (1 / (Real.log ((m : ℝ) + 3)) ^ 2) * (u / 4 - 1 / (m : ℝ)) -
        1 / ((m : ℝ) * (Real.log ((m : ℝ) + 3)) ^ 2) ≤
        ∑ k ∈ Finset.Icc K (m - 1), (aCoeff k - aCoeff (k + 1)) * (k : ℝ) := by
      rw [habel_rev]
      have h1 : (1 / (Real.log ((m : ℝ) + 3)) ^ 2) * (u / 4 - 1 / (m : ℝ)) ≤
          (1 / (Real.log ((m : ℝ) + 3)) ^ 2) * (1 / ((K : ℝ) + 1) - 1 / (m : ℝ)) := by
        gcongr
      linarith
    have halg : u / (8 * (Real.log ((m : ℝ) + 3)) ^ 2) - 1 / ((m : ℝ) * (Real.log ((m : ℝ) + 3)) ^ 2) =
        (1 / 2 : ℝ) * ((1 / (Real.log ((m : ℝ) + 3)) ^ 2) * (u / 4 - 1 / (m : ℝ)) -
          1 / ((m : ℝ) * (Real.log ((m : ℝ) + 3)) ^ 2)) := by ring
    linarith
  linarith

private lemma norm_tildeH_large_t :
    ∀ᶠ r : ℕ in atTop, ∀ u : ℝ, |u| ≤ 1 / 2 → (3000 : ℝ) / (r : ℝ) ≤ |u| →
      ‖tildeH r (Complex.exp (2 * Real.pi * u * I))‖ ≤
        1 - |u| / (16 * (Real.log ((r : ℝ) + 3)) ^ 2) := by
  have hr_third : ∀ᶠ r : ℕ in atTop, (r : ℝ) / 3 ≤ (rStar r : ℝ) := by
    have := rStar_div_tendsto.eventually (Ioi_mem_nhds (show (1 / 3 : ℝ) < 1 / 2 by norm_num))
    filter_upwards [this, eventually_ge_atTop 1] with r hr hr1
    have hrpos : (0 : ℝ) < r := by positivity
    linarith [(lt_div_iff₀ hrpos).mp hr]
  have hlog_half : ∀ᶠ r : ℕ in atTop,
      Real.log ((r : ℝ) + 3) / 2 ≤ Real.log ((rStar r : ℝ) + 3) := by
    have hlog_top : Tendsto (fun r : ℕ => Real.log ((r : ℝ) + 3)) atTop atTop :=
      Real.tendsto_log_atTop.comp
        (tendsto_atTop_add_const_right atTop (3 : ℝ) tendsto_natCast_atTop_atTop)
    filter_upwards [hr_third, hlog_top.eventually_ge_atTop (4 * Real.log 3), eventually_ge_atTop 10] with
      r hr3 hL hr10
    have h1 : ((r : ℝ) + 3) / 3 ≤ (rStar r : ℝ) + 3 := by linarith
    have h2 : Real.log (((r : ℝ) + 3) / 3) ≤ Real.log ((rStar r : ℝ) + 3) :=
      Real.log_le_log (by positivity) h1
    rw [Real.log_div (by positivity) (by norm_num)] at h2
    have hlog3 : 0 < Real.log 3 := lt_trans zero_lt_one log_three_gt_one
    linarith
  filter_upwards [rStar_spec, tail_aCoeff_bound, tildeLam_bounds, hr_third, hlog_half,
    eventually_ge_atTop 10000] with r hrs htail htl hr3 hlog hr10000
  -- Reduce to u > 0 by conjugation symmetry
  suffices hpos : ∀ u : ℝ, u ≤ 1 / 2 → (3000 : ℝ) / (r : ℝ) ≤ u →
      ‖tildeH r (Complex.exp (2 * Real.pi * u * I))‖ ≤
        1 - u / (16 * (Real.log ((r : ℝ) + 3)) ^ 2) by
    intro u hu1 hu2
    rcases le_total 0 u with hge | hle
    · rw [abs_of_nonneg hge] at hu1 hu2 ⊢
      exact hpos u hu1 hu2
    · rw [abs_of_nonpos hle] at hu1 hu2 ⊢
      have hconj : Complex.exp (2 * Real.pi * u * I) =
          starRingEnd ℂ (Complex.exp (2 * Real.pi * ((-u : ℝ) : ℂ) * I)) := by
        rw [← Complex.exp_conj]
        congr 1
        simp [map_mul, Complex.conj_ofReal, Complex.ofReal_neg, Complex.conj_ofNat]
      rw [hconj, norm_tildeH_conj]
      exact hpos (-u) hu1 hu2
  intro u hu1 hu2
  have hrpos : (0 : ℝ) < r := by positivity
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu2
  have hKu : ⌊3 / u⌋₊ + 1 < rStar r := by
    have h1 : 3 / u ≤ (r : ℝ) / 1000 := by
      rw [div_le_div_iff₀ hu0 (by norm_num)]
      have := (div_le_iff₀ hrpos).mp hu2
      linarith
    have h2 : (⌊3 / u⌋₊ : ℝ) ≤ (r : ℝ) / 1000 := le_trans (Nat.floor_le (by positivity)) h1
    have hr10000' : (10000 : ℝ) ≤ r := by exact_mod_cast hr10000
    have h3 : (⌊3 / u⌋₊ : ℝ) + 1 < (rStar r : ℝ) := by linarith
    exact_mod_cast h3
  set z : ℂ := Complex.exp (2 * Real.pi * u * I)
  have hsplit : Finset.Icc 1 r = Finset.Icc 1 (rStar r) ∪ Finset.Icc (rStar r + 1) r := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdis : Disjoint (Finset.Icc 1 (rStar r)) (Finset.Icc (rStar r + 1) r) := by
    rw [Finset.disjoint_left]; intro j h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
  have hLpos : 0 < Real.log ((r : ℝ) + 3) := lt_trans zero_lt_one (log_add_three_gt_one r)
  have hLrs_le : Real.log ((rStar r : ℝ) + 3) ≤ Real.log ((r : ℝ) + 3) :=
    Real.log_le_log (by positivity) (by gcongr; exact hrs.2.1.le)
  have hLrs_pos : 0 < Real.log ((rStar r : ℝ) + 3) := lt_trans zero_lt_one (log_add_three_gt_one _)
  have hlam := lam_bounds (show 1 ≤ r by omega)
  have hpart1 : ‖∑ j ∈ Finset.Icc 1 (rStar r), ((epsSign r j * dCoeff r j : ℝ) : ℂ) * z ^ j‖ ≤
      1 - lam r * u / (8 * (Real.log ((r : ℝ) + 3)) ^ 2) +
        36 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2) := by
    have hrew : ∑ j ∈ Finset.Icc 1 (rStar r), ((epsSign r j * dCoeff r j : ℝ) : ℂ) * z ^ j =
        (lam r : ℂ) * ∑ j ∈ Finset.Icc 1 (rStar r), (aCoeff j : ℂ) * z ^ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp [epsSign, dCoeff, (Finset.mem_Icc.mp hj).2, mul_assoc]
    rw [hrew, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have hab := abel_bound_partial_sum hrs.1 hu0 hu1 hKu
    have hsum_le : ∑ j ∈ Finset.Icc 1 (rStar r), aCoeff j ≤ sumA r := by
      unfold sumA
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j hj _ => (aCoeff_pos (Finset.mem_Icc.mp hj).1).le)
      intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
    have hlam_sum : lam r * ∑ j ∈ Finset.Icc 1 (rStar r), aCoeff j ≤ 1 := by
      calc lam r * ∑ j ∈ Finset.Icc 1 (rStar r), aCoeff j
          ≤ lam r * sumA r := mul_le_mul_of_nonneg_left hsum_le (by linarith)
        _ = 1 := inv_mul_cancel₀ (lt_trans (by norm_num) (sumA_bounds (by omega)).1).ne'
    have hlog_inv : u / (8 * (Real.log ((r : ℝ) + 3)) ^ 2) ≤
        u / (8 * (Real.log ((rStar r : ℝ) + 3)) ^ 2) := by gcongr
    have htail_rs : 1 / ((rStar r : ℝ) * (Real.log ((rStar r : ℝ) + 3)) ^ 2) ≤
        12 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2) := by
      calc 1 / ((rStar r : ℝ) * (Real.log ((rStar r : ℝ) + 3)) ^ 2)
          ≤ 1 / (((r : ℝ) / 3) * (Real.log ((r : ℝ) + 3) / 2) ^ 2) := by gcongr
        _ = 12 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2) := by ring
    have hlam_bound : lam r * (1 / ((rStar r : ℝ) * (Real.log ((rStar r : ℝ) + 3)) ^ 2)) ≤
        36 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2) := by
      calc lam r * (1 / ((rStar r : ℝ) * (Real.log ((rStar r : ℝ) + 3)) ^ 2))
          ≤ 3 * (12 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2)) := by
            have : 0 ≤ 1 / ((rStar r : ℝ) * (Real.log ((rStar r : ℝ) + 3)) ^ 2) := by positivity
            nlinarith
        _ = 36 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2) := by ring
    have hmul := mul_le_mul_of_nonneg_left hab (show 0 ≤ lam r by linarith)
    change lam r * ‖∑ j ∈ Finset.Icc 1 (rStar r), (aCoeff j : ℂ) * z ^ j‖ ≤ _ at hmul
    have hlam_u : lam r * (u / (8 * (Real.log ((r : ℝ) + 3)) ^ 2)) ≤
        lam r * (u / (8 * (Real.log ((rStar r : ℝ) + 3)) ^ 2)) :=
      mul_le_mul_of_nonneg_left hlog_inv (by linarith)
    have hmul_div : lam r * (u / (8 * (Real.log ((r : ℝ) + 3)) ^ 2)) =
        lam r * u / (8 * (Real.log ((r : ℝ) + 3)) ^ 2) := by ring
    linarith
  have hpart2 : ‖∑ j ∈ Finset.Icc (rStar r + 1) r, ((epsSign r j * dCoeff r j : ℝ) : ℂ) * z ^ j‖ ≤
      36 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2) := by
    have hz1 : ‖z‖ = 1 := by
      simp only [z]
      rw [show (2 : ℂ) * Real.pi * u * I = ((2 * Real.pi * u : ℝ) : ℂ) * I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    calc ‖∑ j ∈ Finset.Icc (rStar r + 1) r, ((epsSign r j * dCoeff r j : ℝ) : ℂ) * z ^ j‖
        ≤ ∑ j ∈ Finset.Icc (rStar r + 1) r, ‖((epsSign r j * dCoeff r j : ℝ) : ℂ) * z ^ j‖ :=
          norm_sum_le _ _
      _ = ∑ j ∈ Finset.Icc (rStar r + 1) r, lam r * aCoeff j := by
          refine Finset.sum_congr rfl fun j hj => ?_
          have hnot : ¬(j ≤ rStar r) := by have := (Finset.mem_Icc.mp hj).1; omega
          have hj1 : 1 ≤ j := by have := (Finset.mem_Icc.mp hj).1; have := hrs.1; omega
          rw [norm_mul, norm_pow, hz1, one_pow, mul_one, Complex.norm_real]
          simp only [epsSign, hnot, ↓reduceIte, neg_one_mul, dCoeff, Real.norm_eq_abs, abs_neg,
            abs_of_nonneg (mul_nonneg (show 0 ≤ lam r by linarith) (aCoeff_pos hj1).le)]
      _ = lam r * ∑ j ∈ Finset.Icc (rStar r + 1) r, aCoeff j := by rw [← Finset.mul_sum]
      _ ≤ 3 * (12 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2)) := by
          have hnn : 0 ≤ ∑ j ∈ Finset.Icc (rStar r + 1) r, aCoeff j :=
            Finset.sum_nonneg fun j hj => (aCoeff_pos (by have := (Finset.mem_Icc.mp hj).1; have := hrs.1; omega)).le
          nlinarith
      _ = 36 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2) := by ring
  unfold tildeH
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith [htl.2.1]),
    hsplit, Finset.sum_union hdis]
  have hsum_norm : ‖(∑ j ∈ Finset.Icc 1 (rStar r), ((epsSign r j * dCoeff r j : ℝ) : ℂ) * z ^ j) +
      (∑ j ∈ Finset.Icc (rStar r + 1) r, ((epsSign r j * dCoeff r j : ℝ) : ℂ) * z ^ j)‖ ≤
      1 - u / (8 * (Real.log ((r : ℝ) + 3)) ^ 2) + 72 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2) := by
    have htri := norm_add_le
      (∑ j ∈ Finset.Icc 1 (rStar r), ((epsSign r j * dCoeff r j : ℝ) : ℂ) * z ^ j)
      (∑ j ∈ Finset.Icc (rStar r + 1) r, ((epsSign r j * dCoeff r j : ℝ) : ℂ) * z ^ j)
    have hlam_u : u / (8 * (Real.log ((r : ℝ) + 3)) ^ 2) ≤
        lam r * u / (8 * (Real.log ((r : ℝ) + 3)) ^ 2) := by
      have : 0 ≤ u / (8 * (Real.log ((r : ℝ) + 3)) ^ 2) := by positivity
      have : u / (8 * (Real.log ((r : ℝ) + 3)) ^ 2) * 1 ≤
          u / (8 * (Real.log ((r : ℝ) + 3)) ^ 2) * lam r := by nlinarith
      linarith [show lam r * u / (8 * (Real.log ((r : ℝ) + 3)) ^ 2) =
        u / (8 * (Real.log ((r : ℝ) + 3)) ^ 2) * lam r by ring]
    have h72 : 36 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2) +
        36 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2) =
        72 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2) := by ring
    linarith
  have hinv_pos : 0 < invTildeLam r := by
    have : 0 < tildeLam r := by linarith [htl.2.1]
    exact inv_pos.mp this
  have hu_dom : 144 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2) ≤
      u / (16 * (Real.log ((r : ℝ) + 3)) ^ 2) := by
    have h1 : (2304 : ℝ) / (r : ℝ) ≤ u := by
      have : (2304 : ℝ) / (r : ℝ) ≤ 3000 / (r : ℝ) := by gcongr; norm_num
      linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h2 : (2304 : ℝ) ≤ u * (r : ℝ) := (div_le_iff₀ hrpos).mp h1
    nlinarith [sq_pos_of_pos hLpos]
  calc tildeLam r * ‖_‖
      ≤ tildeLam r * (1 - u / (8 * (Real.log ((r : ℝ) + 3)) ^ 2) +
          72 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum_norm (by linarith [htl.2.1])
    _ ≤ 1 - u / (16 * (Real.log ((r : ℝ) + 3)) ^ 2) := by
        unfold tildeLam
        rw [inv_mul_le_iff₀ hinv_pos]
        have h1 : (1 - u / (16 * (Real.log ((r : ℝ) + 3)) ^ 2)) *
            (1 - 72 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2)) ≤
            (1 - u / (16 * (Real.log ((r : ℝ) + 3)) ^ 2)) * invTildeLam r := by
          have hnn : 0 ≤ 1 - u / (16 * (Real.log ((r : ℝ) + 3)) ^ 2) := by
            have : u / (16 * (Real.log ((r : ℝ) + 3)) ^ 2) ≤ (1 / 2) / 16 := by
              have hL1 : (1 : ℝ) ≤ (Real.log ((r : ℝ) + 3)) ^ 2 := by nlinarith [log_add_three_gt_one r]
              have : 16 ≤ 16 * (Real.log ((r : ℝ) + 3)) ^ 2 := by linarith
              exact div_le_div₀ (by norm_num) hu1 (by norm_num) this
            linarith
          exact mul_le_mul_of_nonneg_left htl.1 hnn
        have hprod_nn : 0 ≤ (u / (16 * (Real.log ((r : ℝ) + 3)) ^ 2)) *
            (72 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2)) := by positivity
        have h2u : 2 * (u / (16 * (Real.log ((r : ℝ) + 3)) ^ 2)) =
            u / (8 * (Real.log ((r : ℝ) + 3)) ^ 2) := by ring
        have h2r : 2 * (72 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2)) =
            144 / ((r : ℝ) * (Real.log ((r : ℝ) + 3)) ^ 2) := by ring
        nlinarith

/-- Fourth-order Taylor integral identity for `cos y` via explicit antiderivative. -/
private lemma cos_taylor4_integral (y : ℝ) :
    Real.cos y - 1 + y ^ 2 / 2 =
      y ^ 4 * ∫ s in (0 : ℝ)..1, ((1 - s) ^ 3 / 6) * Real.cos (y * s) := by
  let F : ℝ → ℝ := fun s =>
    y ^ 3 * (1 - s) ^ 3 / 6 * Real.sin (y * s) -
    y ^ 2 * (1 - s) ^ 2 / 2 * Real.cos (y * s) -
    y * (1 - s) * Real.sin (y * s) +
    Real.cos (y * s)
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt F (y ^ 4 * (((1 - s) ^ 3 / 6) * Real.cos (y * s))) s := by
    intro s _
    have h1ms : HasDerivAt (fun t : ℝ => 1 - t) (-1) s :=
      (hasDerivAt_id s).const_sub 1
    have hys : HasDerivAt (fun t : ℝ => y * t) y s := by
      simpa using (hasDerivAt_id s).const_mul y
    have hsin : HasDerivAt (fun t : ℝ => Real.sin (y * t)) (Real.cos (y * s) * y) s :=
      (Real.hasDerivAt_sin (y * s)).comp s hys
    have hcos : HasDerivAt (fun t : ℝ => Real.cos (y * t)) (-Real.sin (y * s) * y) s :=
      (Real.hasDerivAt_cos (y * s)).comp s hys
    have hp3 : HasDerivAt (fun t : ℝ => y ^ 3 * (1 - t) ^ 3 / 6)
        (y ^ 3 * (3 * (1 - s) ^ 2 * (-1)) / 6) s := by
      have := (((h1ms.pow 3).const_mul (y ^ 3)).div_const 6)
      simpa [Nat.cast_ofNat] using this
    have hp2 : HasDerivAt (fun t : ℝ => y ^ 2 * (1 - t) ^ 2 / 2)
        (y ^ 2 * (2 * (1 - s) ^ 1 * (-1)) / 2) s := by
      have := (((h1ms.pow 2).const_mul (y ^ 2)).div_const 2)
      simpa [Nat.cast_ofNat] using this
    have hp1 : HasDerivAt (fun t : ℝ => y * (1 - t)) (y * (-1)) s :=
      h1ms.const_mul y
    have hall := (((hp3.mul hsin).sub (hp2.mul hcos)).sub (hp1.mul hsin)).add hcos
    have heq : (y ^ 3 * (3 * (1 - s) ^ 2 * -1) / 6 * Real.sin (y * s) +
        y ^ 3 * (1 - s) ^ 3 / 6 * (Real.cos (y * s) * y) -
        (y ^ 2 * (2 * (1 - s) ^ 1 * -1) / 2 * Real.cos (y * s) +
          y ^ 2 * (1 - s) ^ 2 / 2 * (-Real.sin (y * s) * y)) -
        (y * -1 * Real.sin (y * s) + y * (1 - s) * (Real.cos (y * s) * y)) +
        -Real.sin (y * s) * y) =
        y ^ 4 * (((1 - s) ^ 3 / 6) * Real.cos (y * s)) := by ring
    rwa [heq] at hall
  have hint : IntervalIntegrable (fun s : ℝ => y ^ 4 * (((1 - s) ^ 3 / 6) * Real.cos (y * s)))
      MeasureTheory.volume 0 1 :=
    (Continuous.intervalIntegrable (by fun_prop) 0 1)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_const_mul] at hftc
  simp only [F, sub_self, zero_pow (by norm_num : 3 ≠ 0), zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, zero_div, zero_mul, sub_zero, zero_add, mul_one, Real.sin_zero, Real.cos_zero,
    one_pow, sub_zero, mul_one] at hftc
  linarith

private lemma integral_one_sub_cube_div_six :
    ∫ s in (0 : ℝ)..1, (1 - s) ^ 3 / 6 = 1 / 24 := by
  have hd : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => -((1 - t) ^ 4 / 24)) ((1 - s) ^ 3 / 6) s := by
    intro s _
    have h1ms : HasDerivAt (fun t : ℝ => 1 - t) (-1) s := (hasDerivAt_id s).const_sub 1
    have h0 := ((h1ms.pow 4).div_const 24).neg
    have heq : -((4 : ℕ) * (1 - s) ^ (4 - 1) * -1 / 24) = (1 - s) ^ 3 / 6 := by norm_num; ring
    rwa [heq] at h0
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) 0 1)]
  norm_num

private lemma abs_integral_cos_kernel_le (a : ℝ) :
    |∫ s in (0 : ℝ)..1, ((1 - s) ^ 3 / 6) * Real.cos (a * s)| ≤ 1 / 24 := by
  have h1 := intervalIntegral.abs_integral_le_integral_abs (μ := MeasureTheory.volume)
    (a := (0 : ℝ)) (b := 1) (by norm_num)
    (f := fun s => ((1 - s) ^ 3 / 6) * Real.cos (a * s))
  have h2 : ∫ s in (0 : ℝ)..1, |((1 - s) ^ 3 / 6) * Real.cos (a * s)| ≤
      ∫ s in (0 : ℝ)..1, (1 - s) ^ 3 / 6 := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (Continuous.intervalIntegrable (by fun_prop) 0 1)
      (Continuous.intervalIntegrable (by fun_prop) 0 1)
    intro s hs
    rw [abs_mul, abs_of_nonneg (by have := hs.2; positivity)]
    exact mul_le_of_le_one_right (by have := hs.2; positivity) (Real.abs_cos_le_one _)
  linarith [integral_one_sub_cube_div_six]

private lemma abs_cos_sub_taylor2_le (y : ℝ) :
    |Real.cos y - 1 + y ^ 2 / 2| ≤ y ^ 4 / 24 := by
  rw [cos_taylor4_integral y, abs_mul, abs_of_nonneg (by positivity : 0 ≤ y ^ 4)]
  have hbound := abs_integral_cos_kernel_le y
  have := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ y ^ 4)
  linarith

private noncomputable def fNaz (c x : ℝ) : ℝ :=
  x ^ 2 * ∫ s in (0 : ℝ)..1, ((1 - s) ^ 3 / 6) * Real.cos (c * x * s)

private lemma fNaz_abs_le (c x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |fNaz c x| ≤ 1 / 24 := by
  unfold fNaz
  rw [abs_mul, abs_of_nonneg (sq_nonneg x)]
  have h1 := abs_integral_cos_kernel_le (c * x)
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
  nlinarith [sq_nonneg x]

private lemma fNaz_lipschitz {C c x₁ x₂ : ℝ} (hC : 0 ≤ C) (hc0 : 0 ≤ c) (hcC : c ≤ C)
    (hx₁ : x₁ ∈ Set.Icc (0 : ℝ) 1) (hx₂ : x₂ ∈ Set.Icc (0 : ℝ) 1) :
    |fNaz c x₁ - fNaz c x₂| ≤ ((C + 2) / 24) * |x₁ - x₂| := by
  unfold fNaz
  set I₁ := ∫ s in (0 : ℝ)..1, ((1 - s) ^ 3 / 6) * Real.cos (c * x₁ * s)
  set I₂ := ∫ s in (0 : ℝ)..1, ((1 - s) ^ 3 / 6) * Real.cos (c * x₂ * s)
  have hI_diff : |I₁ - I₂| ≤ (C / 24) * |x₁ - x₂| := by
    have hsub : I₁ - I₂ = ∫ s in (0 : ℝ)..1, ((1 - s) ^ 3 / 6) *
        (Real.cos (c * x₁ * s) - Real.cos (c * x₂ * s)) := by
      rw [← intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) 0 1)
        (Continuous.intervalIntegrable (by fun_prop) 0 1)]
      congr 1; ext s; ring
    rw [hsub]
    have ha := intervalIntegral.abs_integral_le_integral_abs (μ := MeasureTheory.volume)
      (a := (0 : ℝ)) (b := 1) (by norm_num)
      (f := fun s => ((1 - s) ^ 3 / 6) * (Real.cos (c * x₁ * s) - Real.cos (c * x₂ * s)))
    have hb : ∫ s in (0 : ℝ)..1, |((1 - s) ^ 3 / 6) *
          (Real.cos (c * x₁ * s) - Real.cos (c * x₂ * s))| ≤
        ∫ s in (0 : ℝ)..1, ((1 - s) ^ 3 / 6) * (C * |x₁ - x₂|) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (Continuous.intervalIntegrable (by fun_prop) 0 1)
        (Continuous.intervalIntegrable (by fun_prop) 0 1)
      intro s hs
      rw [abs_mul, abs_of_nonneg (by have := hs.2; positivity)]
      apply mul_le_mul_of_nonneg_left _ (by have := hs.2; positivity)
      calc |Real.cos (c * x₁ * s) - Real.cos (c * x₂ * s)|
          ≤ |c * x₁ * s - c * x₂ * s| := Real.abs_cos_sub_cos_le _ _
        _ = c * s * |x₁ - x₂| := by
            rw [show c * x₁ * s - c * x₂ * s = c * s * (x₁ - x₂) by ring, abs_mul,
              abs_of_nonneg (mul_nonneg hc0 hs.1)]
        _ ≤ C * 1 * |x₁ - x₂| := by
            have hcs : c * s ≤ C * 1 := mul_le_mul hcC hs.2 hs.1 hC
            exact mul_le_mul_of_nonneg_right hcs (abs_nonneg _)
        _ = C * |x₁ - x₂| := by ring
    have hc : ∫ s in (0 : ℝ)..1, ((1 - s) ^ 3 / 6) * (C * |x₁ - x₂|) = (C / 24) * |x₁ - x₂| := by
      rw [intervalIntegral.integral_mul_const, integral_one_sub_cube_div_six]; ring
    linarith
  have hsplit : x₁ ^ 2 * I₁ - x₂ ^ 2 * I₂ = (x₁ + x₂) * (x₁ - x₂) * I₁ + x₂ ^ 2 * (I₁ - I₂) := by
    ring
  rw [hsplit]
  calc |(x₁ + x₂) * (x₁ - x₂) * I₁ + x₂ ^ 2 * (I₁ - I₂)|
      ≤ |(x₁ + x₂) * (x₁ - x₂) * I₁| + |x₂ ^ 2 * (I₁ - I₂)| := abs_add_le _ _
    _ = |x₁ + x₂| * |x₁ - x₂| * |I₁| + x₂ ^ 2 * |I₁ - I₂| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg x₂)]
    _ ≤ 2 * |x₁ - x₂| * (1 / 24) + 1 * ((C / 24) * |x₁ - x₂|) := by
        have hxsum : |x₁ + x₂| ≤ 2 := by
          rw [abs_of_nonneg (by linarith [hx₁.1, hx₂.1])]; linarith [hx₁.2, hx₂.2]
        have hx2sq : x₂ ^ 2 ≤ 1 := by nlinarith [hx₂.1, hx₂.2]
        have hI1 := abs_integral_cos_kernel_le (c * x₁)
        have h1 : |x₁ + x₂| * |x₁ - x₂| * |I₁| ≤ 2 * |x₁ - x₂| * (1 / 24) := by gcongr
        have h2 : x₂ ^ 2 * |I₁ - I₂| ≤ 1 * ((C / 24) * |x₁ - x₂|) := by gcongr
        linarith
    _ = ((C + 2) / 24) * |x₁ - x₂| := by ring

private lemma fNaz_eq_sinc_of_pos {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    c ^ 2 * fNaz c x = 1 / 2 - (1 / 2) * (Real.sin (c * x / 2) / (c * x / 2)) ^ 2 := by
  have h1 := cos_taylor4_integral (c * x)
  unfold fNaz
  have hmul : c ^ 2 * (x ^ 2 * ∫ s in (0 : ℝ)..1, ((1 - s) ^ 3 / 6) * Real.cos (c * x * s)) =
      (Real.cos (c * x) - 1 + (c * x) ^ 2 / 2) / (c * x) ^ 2 := by
    have hcx : c * x ≠ 0 := (mul_pos hc hx).ne'
    rw [h1]; field_simp [hcx]
  rw [hmul]
  have hcos : Real.cos (c * x) = 1 - 2 * Real.sin (c * x / 2) ^ 2 := by
    have h2 := Real.cos_two_mul (c * x / 2)
    have hsc := Real.sin_sq_add_cos_sq (c * x / 2)
    rw [show 2 * (c * x / 2) = c * x by ring] at h2
    linarith
  rw [hcos]
  have hcx : c * x ≠ 0 := (mul_pos hc hx).ne'
  field_simp [hcx]; ring

private lemma integral_sinc_sq_gt {b : ℝ} (hb : 0 < b) :
    ∫ u in b..(2 * b), (Real.sin u / u) ^ 2 < ∫ u in (0 : ℝ)..b, (Real.sin u / u) ^ 2 := by
  have hint_fn : Continuous (fun u : ℝ => if u = 0 then (1 : ℝ) else Real.sin u / u) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x = 0
    · subst hx
      rw [ContinuousAt, if_pos rfl]
      have hderiv : HasDerivAt Real.sin 1 0 := by simpa using Real.hasDerivAt_sin 0
      rw [hasDerivAt_iff_tendsto_slope_zero] at hderiv
      have hconv : Tendsto (fun t : ℝ => Real.sin t / t) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
        simpa [sub_zero, div_eq_inv_mul] using hderiv
      rw [Metric.tendsto_nhds] at hconv ⊢
      intro ε hε
      have hmem := hconv ε hε
      rw [eventually_nhdsWithin_iff] at hmem
      filter_upwards [hmem] with t ht
      by_cases ht0 : t = 0
      · subst ht0; simp [hε]
      · simpa [ht0] using ht ht0
    · have hev : (fun u : ℝ => if u = 0 then (1 : ℝ) else Real.sin u / u) =ᶠ[nhds x]
          (fun u : ℝ => Real.sin u / u) := by
        filter_upwards [isOpen_ne.mem_nhds hx] with u hu
        simp [hu]
      exact (ContinuousAt.div Real.continuous_sin.continuousAt continuousAt_id hx).congr hev.symm
  let sinc : ℝ → ℝ := fun u => if u = 0 then 1 else Real.sin u / u
  have hsinc_eq : ∀ a₁ a₂ : ℝ, ∫ u in a₁..a₂, (Real.sin u / u) ^ 2 = ∫ u in a₁..a₂, (sinc u) ^ 2 := by
    intro a₁ a₂
    apply intervalIntegral.integral_congr_ae
    have hae : ∀ᵐ u : ℝ ∂MeasureTheory.volume, u ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simp [MeasureTheory.measure_singleton]
    filter_upwards [hae] with u hu _
    simp [sinc, hu]
  rw [hsinc_eq b (2 * b), hsinc_eq 0 b]
  by_cases hpi : b ≤ Real.pi / 2
  · -- Case 1: b ≤ π / 2, use strict monotonicity of sinc on [0, π]
    have hanti : StrictAntiOn sinc (Set.Icc 0 Real.pi) := by
      have hderiv_neg : ∀ u ∈ Set.Ioo (0 : ℝ) Real.pi,
          HasDerivAt (fun t : ℝ => Real.sin t / t) ((u * Real.cos u - Real.sin u) / u ^ 2) u ∧
          (u * Real.cos u - Real.sin u) / u ^ 2 < 0 := by
        intro u hu
        refine ⟨?_, ?_⟩
        · have h0 := (Real.hasDerivAt_sin u).div (hasDerivAt_id u) hu.1.ne'
          dsimp only [id_eq] at h0
          have heq : (Real.cos u * u - Real.sin u * 1) / u ^ 2 =
              (u * Real.cos u - Real.sin u) / u ^ 2 := by ring
          rwa [heq] at h0
        · apply div_neg_of_neg_of_pos _ (sq_pos_of_pos hu.1)
          -- Show g(u) = sin u - u cos u > 0 on (0, π) since g'(u) = u sin u > 0
          let g : ℝ → ℝ := fun t => Real.sin t - t * Real.cos t
          have hg0 : g 0 = 0 := by simp [g]
          have hg_mono : StrictMonoOn g (Set.Icc 0 Real.pi) := by
            apply strictMonoOn_of_deriv_pos (convex_Icc 0 Real.pi)
            · exact (Real.continuous_sin.sub (continuous_id.mul Real.continuous_cos)).continuousOn
            · intro t ht
              rw [interior_Icc] at ht
              have hd : HasDerivAt g (t * Real.sin t) t := by
                have h0 := (Real.hasDerivAt_sin t).sub
                  ((hasDerivAt_id t).mul (Real.hasDerivAt_cos t))
                dsimp only [id_eq] at h0
                have heq : Real.cos t - (1 * Real.cos t + t * -Real.sin t) = t * Real.sin t := by ring
                rwa [heq] at h0
              rw [hd.deriv]
              exact mul_pos ht.1 (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2)
          have hgt := hg_mono (Set.left_mem_Icc.mpr Real.pi_pos.le)
            (Set.Ioo_subset_Icc_self hu) hu.1
          simp only [g, hg0] at hgt
          linarith
      apply strictAntiOn_of_deriv_neg (convex_Icc 0 Real.pi) hint_fn.continuousOn
      intro u hu
      rw [interior_Icc] at hu
      have hev : sinc =ᶠ[nhds u] (fun t : ℝ => Real.sin t / t) := by
        filter_upwards [isOpen_Ioi.mem_nhds hu.1] with t ht
        have ht0 : t ≠ 0 := (Set.mem_Ioi.mp ht).ne'
        simp [sinc, ht0]
      have hd := (hderiv_neg u hu).1.congr_of_eventuallyEq hev
      rw [hd.deriv]
      exact (hderiv_neg u hu).2
    have hshift : ∫ u in b..(2 * b), (sinc u) ^ 2 = ∫ u in (0 : ℝ)..b, (sinc (u + b)) ^ 2 := by
      have := intervalIntegral.integral_comp_add_right (fun u => (sinc u) ^ 2) b (a := (0 : ℝ)) (b := b)
      simpa [two_mul] using this.symm
    rw [hshift]
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hb
    · exact ((hint_fn.comp (continuous_id.add continuous_const)).pow 2).continuousOn
    · exact (hint_fn.pow 2).continuousOn
    · intro u hu
      have hlt : sinc (u + b) < sinc u :=
        hanti ⟨hu.1.le, by linarith [hu.2, hpi]⟩ ⟨by linarith [hu.1], by linarith [hu.2, hpi]⟩ (by linarith)
      have hnn : 0 ≤ sinc (u + b) := by
        have hpos : 0 < u + b := by linarith [hu.1]
        simp only [sinc, hpos.ne', ↓reduceIte]
        exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hpos.le (by linarith [hu.2, hpi])) hpos.le
      nlinarith
    · refine ⟨b / 2, ⟨by linarith, by linarith⟩, ?_⟩
      have hlt : sinc (b / 2 + b) < sinc (b / 2) :=
        hanti ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
      have hnn : 0 ≤ sinc (b / 2 + b) := by
        have hpos : 0 < b / 2 + b := by linarith
        simp only [sinc, hpos.ne', ↓reduceIte]
        exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hpos.le (by linarith)) hpos.le
      nlinarith
  · -- Case 2: b > π / 2
    push Not at hpi
    have hright : ∫ u in b..(2 * b), (sinc u) ^ 2 ≤ 1 / (2 * b) := by
      have hle : ∫ u in b..(2 * b), (sinc u) ^ 2 ≤ ∫ u in b..(2 * b), (1 : ℝ) / u ^ 2 := by
        apply intervalIntegral.integral_mono_on (by linarith)
        · exact (hint_fn.pow 2).intervalIntegrable _ _
        · apply ContinuousOn.intervalIntegrable
          intro u hu
          have hupos : 0 < u := by
            rw [Set.uIcc_of_le (by linarith)] at hu; linarith [hu.1]
          exact (continuousAt_const.div (continuousAt_id.pow 2) (sq_pos_of_pos hupos).ne').continuousWithinAt
        · intro u hu
          have hupos : 0 < u := by linarith [hu.1]
          simp only [sinc, hupos.ne', ↓reduceIte]
          rw [div_pow, one_div]
          have hsin : Real.sin u ^ 2 ≤ 1 := by
            nlinarith [Real.sin_le_one u, Real.neg_one_le_sin u]
          rw [div_eq_mul_inv]
          exact mul_le_of_le_one_left (by positivity) hsin
      have hval : ∫ u in b..(2 * b), (1 : ℝ) / u ^ 2 = 1 / (2 * b) := by
        have hd : ∀ u ∈ Set.uIcc b (2 * b), HasDerivAt (fun t : ℝ => -t⁻¹) (1 / u ^ 2) u := by
          intro u hu
          rw [Set.uIcc_of_le (by linarith)] at hu
          have hupos : 0 < u := by linarith [hu.1]
          have h0 : HasDerivAt (fun t : ℝ => -t⁻¹) (-( -(u ^ 2)⁻¹)) u :=
            (hasDerivAt_inv hupos.ne').neg
          simpa [one_div] using h0
        have hint : IntervalIntegrable (fun u : ℝ => (1 : ℝ) / u ^ 2) MeasureTheory.volume b (2 * b) := by
          apply ContinuousOn.intervalIntegrable
          intro u hu
          rw [Set.uIcc_of_le (by linarith)] at hu
          have hupos : 0 < u := by linarith [hu.1]
          exact (continuousAt_const.div (continuousAt_id.pow 2) (sq_pos_of_pos hupos).ne').continuousWithinAt
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
        field_simp [hb.ne']; ring
      linarith
    have hleft : 2 / Real.pi ≤ ∫ u in (0 : ℝ)..b, (sinc u) ^ 2 := by
      have hsplit : ∫ u in (0 : ℝ)..b, (sinc u) ^ 2 =
          (∫ u in (0 : ℝ)..(Real.pi / 2), (sinc u) ^ 2) +
          (∫ u in (Real.pi / 2)..b, (sinc u) ^ 2) :=
        (intervalIntegral.integral_add_adjacent_intervals
          ((hint_fn.pow 2).intervalIntegrable _ _) ((hint_fn.pow 2).intervalIntegrable _ _)).symm
      have hnn : 0 ≤ ∫ u in (Real.pi / 2)..b, (sinc u) ^ 2 :=
        intervalIntegral.integral_nonneg hpi.le fun u _ => sq_nonneg _
      have hmain : 2 / Real.pi ≤ ∫ u in (0 : ℝ)..(Real.pi / 2), (sinc u) ^ 2 := by
        have hle : ∫ u in (0 : ℝ)..(Real.pi / 2), (4 / Real.pi ^ 2 : ℝ) ≤
            ∫ u in (0 : ℝ)..(Real.pi / 2), (sinc u) ^ 2 := by
          apply intervalIntegral.integral_mono_on (by positivity)
            intervalIntegrable_const ((hint_fn.pow 2).intervalIntegrable _ _)
          intro u hu
          by_cases hu0 : u = 0
          · subst hu0
            change 4 / Real.pi ^ 2 ≤ (if (0 : ℝ) = 0 then (1 : ℝ) else Real.sin 0 / 0) ^ 2
            rw [if_pos rfl, one_pow, div_le_one (sq_pos_of_pos Real.pi_pos)]
            nlinarith [Real.pi_gt_three]
          · have hupos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
            change 4 / Real.pi ^ 2 ≤ (if u = 0 then (1 : ℝ) else Real.sin u / u) ^ 2
            rw [if_neg hu0]
            have hms := Real.mul_le_sin hu.1 hu.2
            have hdiv : 2 / Real.pi ≤ Real.sin u / u := by
              rw [le_div_iff₀ hupos]; linarith
            have : (2 / Real.pi) ^ 2 ≤ (Real.sin u / u) ^ 2 :=
              pow_le_pow_left₀ (by positivity) hdiv 2
            linarith [show (2 / Real.pi) ^ 2 = 4 / Real.pi ^ 2 by ring]
        have hconst : ∫ _u in (0 : ℝ)..(Real.pi / 2), (4 / Real.pi ^ 2 : ℝ) = 2 / Real.pi := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          field_simp [Real.pi_pos.ne']; ring
        linarith
      linarith
    have hlt_pi : 1 / (2 * b) < 2 / Real.pi := by
      rw [div_lt_div_iff₀ (by positivity) Real.pi_pos]
      nlinarith
    linarith

private lemma fNaz_integral_gap :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ c ∈ Set.Icc (0 : ℝ) (6000 * Real.pi),
      δ₀ ≤ (∫ x in (1 / 2 : ℝ)..1, fNaz c x) - (∫ x in (0 : ℝ)..(1 / 2), fNaz c x) := by
  let Δ : ℝ → ℝ := fun c =>
    (∫ x in (1 / 2 : ℝ)..1, fNaz c x) - (∫ x in (0 : ℝ)..(1 / 2), fNaz c x)
  have hcont_f : Continuous (fun p : ℝ × ℝ => fNaz p.1 p.2) := by
    unfold fNaz
    have hint_cont : Continuous (fun p : ℝ × ℝ =>
        ∫ s in (0 : ℝ)..1, ((1 - s) ^ 3 / 6) * Real.cos (p.1 * p.2 * s)) := by
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      fun_prop
    exact (continuous_snd.pow 2).mul hint_cont
  have hcont_Δ : Continuous Δ := by
    unfold Δ
    apply Continuous.sub
    · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcont_f _ _
    · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcont_f _ _
  have hpos_Δ : ∀ c ∈ Set.Icc (0 : ℝ) (6000 * Real.pi), 0 < Δ c := by
    intro c hc
    by_cases hc0 : c = 0
    · subst hc0
      have hf0 : ∀ x : ℝ, fNaz 0 x = x ^ 2 / 24 := by
        intro x; unfold fNaz
        simp only [zero_mul, Real.cos_zero, mul_one, integral_one_sub_cube_div_six]
        ring
      have hΔ0 : Δ 0 = (∫ x in (1 / 2 : ℝ)..1, x ^ 2 / 24) - (∫ x in (0 : ℝ)..(1 / 2), x ^ 2 / 24) := by
        simp only [Δ, hf0]
      rw [hΔ0]
      have hint_sq : ∀ a b : ℝ, ∫ x in a..b, x ^ 2 / 24 = (b ^ 3 - a ^ 3) / 72 := by
        intro a b
        have hd : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun t : ℝ => t ^ 3 / 72) (x ^ 2 / 24) x := by
          intro x _
          have h0 := (hasDerivAt_pow 3 x).div_const 72
          have heq : (3 : ℕ) * x ^ (3 - 1) / 72 = x ^ 2 / 24 := by norm_num; ring
          rwa [heq] at h0
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
          (Continuous.intervalIntegrable (by fun_prop) a b)]
        ring
      rw [hint_sq, hint_sq]; norm_num
    · have hcpos : 0 < c := lt_of_le_of_ne hc.1 (Ne.symm hc0)
      suffices h : 0 < c ^ 2 * Δ c by exact pos_of_mul_pos_right h (sq_nonneg c)
      have hrew : c ^ 2 * Δ c =
          (∫ x in (1 / 2 : ℝ)..1, c ^ 2 * fNaz c x) -
          (∫ x in (0 : ℝ)..(1 / 2), c ^ 2 * fNaz c x) := by
        unfold Δ
        rw [mul_sub, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      rw [hrew]
      have h1 : ∫ x in (1 / 2 : ℝ)..1, c ^ 2 * fNaz c x =
          1 / 4 - (1 / c) * ∫ u in (c / 4)..(2 * (c / 4)), (Real.sin u / u) ^ 2 := by
        have hcongr : ∫ x in (1 / 2 : ℝ)..1, c ^ 2 * fNaz c x =
            ∫ x in (1 / 2 : ℝ)..1, (1 / 2 - (1 / 2) * (Real.sin (c * x / 2) / (c * x / 2)) ^ 2) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [Set.uIcc_of_le (by norm_num)] at hx
          exact fNaz_eq_sinc_of_pos hcpos (by linarith [hx.1])
        rw [hcongr]
        have hsub : IntervalIntegrable (fun x : ℝ => (1 / 2) * (Real.sin (c * x / 2) / (c * x / 2)) ^ 2)
            MeasureTheory.volume (1 / 2) 1 := by
          apply ContinuousOn.intervalIntegrable
          intro x hx
          rw [Set.uIcc_of_le (by norm_num)] at hx
          have hne : c * x / 2 ≠ 0 := (by have := hx.1; positivity : 0 < c * x / 2).ne'
          fun_prop (disch := assumption)
        rw [intervalIntegral.integral_sub intervalIntegrable_const hsub, intervalIntegral.integral_const,
          smul_eq_mul, intervalIntegral.integral_const_mul]
        have hchg : ∫ x in (1 / 2 : ℝ)..1, (Real.sin (c * x / 2) / (c * x / 2)) ^ 2 =
            (2 / c) * ∫ u in (c / 4)..(2 * (c / 4)), (Real.sin u / u) ^ 2 := by
          have := intervalIntegral.integral_comp_mul_left
            (fun u : ℝ => (Real.sin u / u) ^ 2) (a := (1 / 2 : ℝ)) (b := 1)
            (show c / 2 ≠ 0 by positivity)
          have heq1 : (c / 2) * (1 / 2 : ℝ) = c / 4 := by ring
          have heq2 : (c / 2) * 1 = 2 * (c / 4) := by ring
          have heq3 : (c / 2)⁻¹ = 2 / c := by field_simp
          rw [heq1, heq2, heq3] at this
          simpa [show ∀ x : ℝ, c / 2 * x = c * x / 2 by intro x; ring, smul_eq_mul] using this
        rw [hchg]; ring
      have h2 : ∫ x in (0 : ℝ)..(1 / 2), c ^ 2 * fNaz c x =
          1 / 4 - (1 / c) * ∫ u in (0 : ℝ)..(c / 4), (Real.sin u / u) ^ 2 := by
        have hcongr : ∫ x in (0 : ℝ)..(1 / 2), c ^ 2 * fNaz c x =
            ∫ x in (0 : ℝ)..(1 / 2), (1 / 2 - (1 / 2) * (Real.sin (c * x / 2) / (c * x / 2)) ^ 2) := by
          apply intervalIntegral.integral_congr_ae
          have hae : ∀ᵐ x : ℝ ∂MeasureTheory.volume, x ≠ 0 := by
            rw [MeasureTheory.ae_iff]
            simp [MeasureTheory.measure_singleton]
          filter_upwards [hae] with x _ hmem
          rw [Set.uIoc_of_le (by norm_num)] at hmem
          exact fNaz_eq_sinc_of_pos hcpos hmem.1
        rw [hcongr]
        have hf_int : IntervalIntegrable (fun x : ℝ => c ^ 2 * fNaz c x)
            MeasureTheory.volume 0 (1 / 2) := by
          exact ((hcont_f.comp (continuous_const.prodMk continuous_id)).const_mul (c ^ 2)).intervalIntegrable _ _
        have hsub : IntervalIntegrable (fun x : ℝ => (1 / 2) * (Real.sin (c * x / 2) / (c * x / 2)) ^ 2)
            MeasureTheory.volume 0 (1 / 2) := by
          have hconst : IntervalIntegrable (fun _ : ℝ => (1 / 2 : ℝ)) MeasureTheory.volume 0 (1 / 2) :=
            intervalIntegrable_const
          refine (hconst.sub hf_int).congr_ae ?_
          rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
          filter_upwards with x hx
          rw [Set.uIoc_of_le (by norm_num)] at hx
          have := fNaz_eq_sinc_of_pos hcpos hx.1
          linarith
        rw [intervalIntegral.integral_sub intervalIntegrable_const hsub, intervalIntegral.integral_const,
          smul_eq_mul, intervalIntegral.integral_const_mul]
        have hchg : ∫ x in (0 : ℝ)..(1 / 2), (Real.sin (c * x / 2) / (c * x / 2)) ^ 2 =
            (2 / c) * ∫ u in (0 : ℝ)..(c / 4), (Real.sin u / u) ^ 2 := by
          have := intervalIntegral.integral_comp_mul_left
            (fun u : ℝ => (Real.sin u / u) ^ 2) (a := (0 : ℝ)) (b := 1 / 2)
            (show c / 2 ≠ 0 by positivity)
          have heq1 : (c / 2) * (0 : ℝ) = 0 := by ring
          have heq2 : (c / 2) * (1 / 2 : ℝ) = c / 4 := by ring
          have heq3 : (c / 2)⁻¹ = 2 / c := by field_simp
          rw [heq1, heq2, heq3] at this
          simpa [show ∀ x : ℝ, c / 2 * x = c * x / 2 by intro x; ring, smul_eq_mul] using this
        rw [hchg]; ring
      rw [h1, h2]
      have hgt := integral_sinc_sq_gt (show 0 < c / 4 by positivity)
      have hsub_pos : 0 < (∫ u in (0 : ℝ)..(c / 4), (Real.sin u / u) ^ 2) -
          (∫ u in (c / 4)..(2 * (c / 4)), (Real.sin u / u) ^ 2) := sub_pos.mpr hgt
      have halg : (1 / 4 - (1 / c) * ∫ u in (c / 4)..(2 * (c / 4)), (Real.sin u / u) ^ 2) -
          (1 / 4 - (1 / c) * ∫ u in (0 : ℝ)..(c / 4), (Real.sin u / u) ^ 2) =
          (1 / c) * ((∫ u in (0 : ℝ)..(c / 4), (Real.sin u / u) ^ 2) -
            (∫ u in (c / 4)..(2 * (c / 4)), (Real.sin u / u) ^ 2)) := by ring
      rw [halg]
      exact mul_pos (by positivity) hsub_pos
  obtain ⟨c₀, hc₀_mem, hc₀_min⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr (by positivity : (0 : ℝ) ≤ 6000 * Real.pi))
      hcont_Δ.continuousOn
  exact ⟨Δ c₀, hpos_Δ c₀ hc₀_mem, fun c hc => hc₀_min hc⟩

private lemma riemann_sum_lipschitz {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x₁ ∈ Set.Icc (0 : ℝ) 1, ∀ x₂ ∈ Set.Icc (0 : ℝ) 1, |f x₁ - f x₂| ≤ L * |x₁ - x₂|)
    (hcont : ContinuousOn f (Set.Icc 0 1))
    {r a b : ℕ} (hr : 1 ≤ r) (hab : a ≤ b) (hbr : b ≤ r) :
    |(1 / (r : ℝ)) * (∑ j ∈ Finset.Icc (a + 1) b, f ((j : ℝ) / r)) -
      ∫ x in ((a : ℝ) / r)..((b : ℝ) / r), f x| ≤ L / (r : ℝ) := by
  have hrpos : (0 : ℝ) < r := by positivity
  have hsum_int : ∫ x in ((a : ℝ) / r)..((b : ℝ) / r), f x =
      ∑ j ∈ Finset.Icc (a + 1) b, ∫ x in (((j - 1 : ℕ) : ℝ) / r)..((j : ℝ) / r), f x := by
    suffices ∀ m : ℕ, a + m ≤ r →
        ∫ x in ((a : ℝ) / r)..(((a + m : ℕ) : ℝ) / r), f x =
          ∑ j ∈ Finset.Icc (a + 1) (a + m), ∫ x in (((j - 1 : ℕ) : ℝ) / r)..((j : ℝ) / r), f x by
      have h := this (b - a) (by omega)
      rw [show a + (b - a) = b by omega] at h
      exact h
    intro m
    induction m with
    | zero =>
      intro _
      simp only [add_zero, intervalIntegral.integral_same]
      have hempty : Finset.Icc (a + 1) a = ∅ := Finset.Icc_eq_empty (by omega)
      rw [hempty, Finset.sum_empty]
    | succ m ih =>
      intro hle
      have h1 : Finset.Icc (a + 1) (a + (m + 1)) =
          insert (a + (m + 1)) (Finset.Icc (a + 1) (a + m)) := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [h1, Finset.sum_insert (by simp), ← ih (by omega)]
      have hint1 : IntervalIntegrable f MeasureTheory.volume ((a : ℝ) / r) (((a + m : ℕ) : ℝ) / r) :=
        (hcont.mono fun x hx => ⟨le_trans (by positivity) hx.1,
          le_trans hx.2 ((div_le_one hrpos).mpr (by exact_mod_cast (show a + m ≤ r by omega)))⟩).intervalIntegrable_of_Icc
          (div_le_div_of_nonneg_right (by exact_mod_cast (show a ≤ a + m by omega)) hrpos.le)
      have hint2 : IntervalIntegrable f MeasureTheory.volume (((a + m : ℕ) : ℝ) / r)
          (((a + (m + 1) : ℕ) : ℝ) / r) :=
        (hcont.mono fun x hx => ⟨le_trans (by positivity) hx.1,
          le_trans hx.2 ((div_le_one hrpos).mpr (by exact_mod_cast hle))⟩).intervalIntegrable_of_Icc
          (div_le_div_of_nonneg_right (by exact_mod_cast (show a + m ≤ a + (m + 1) by omega)) hrpos.le)
      have hsub : a + (m + 1) - 1 = a + m := by omega
      rw [hsub, add_comm (∫ x in (((a + m : ℕ) : ℝ) / r)..(((a + (m + 1) : ℕ) : ℝ) / r), f x)]
      exact (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm
  rw [hsum_int, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc |∑ j ∈ Finset.Icc (a + 1) b,
        ((1 / (r : ℝ)) * f ((j : ℝ) / r) - ∫ x in (((j - 1 : ℕ) : ℝ) / r)..((j : ℝ) / r), f x)|
      ≤ ∑ j ∈ Finset.Icc (a + 1) b,
        |(1 / (r : ℝ)) * f ((j : ℝ) / r) - ∫ x in (((j - 1 : ℕ) : ℝ) / r)..((j : ℝ) / r), f x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.Icc (a + 1) b, L / (r : ℝ) ^ 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj1 : a + 1 ≤ j := (Finset.mem_Icc.mp hj).1
        have hjb : j ≤ b := (Finset.mem_Icc.mp hj).2
        have hstep_le : ((j - 1 : ℕ) : ℝ) / (r : ℝ) ≤ (j : ℝ) / (r : ℝ) := by
          gcongr; exact_mod_cast Nat.sub_le j 1
        have hlen : (j : ℝ) / (r : ℝ) - ((j - 1 : ℕ) : ℝ) / (r : ℝ) = 1 / (r : ℝ) := by
          rw [Nat.cast_sub (by omega), Nat.cast_one]; field_simp [hrpos.ne']; ring
        have hconst : (1 / (r : ℝ)) * f ((j : ℝ) / r) =
            ∫ _x in (((j - 1 : ℕ) : ℝ) / r)..((j : ℝ) / r), f ((j : ℝ) / r) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, hlen]
        rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const]
        · have habs := intervalIntegral.abs_integral_le_integral_abs (μ := MeasureTheory.volume) hstep_le
            (f := fun x => f ((j : ℝ) / r) - f x)
          have hmono : ∫ x in (((j - 1 : ℕ) : ℝ) / r)..((j : ℝ) / r), |f ((j : ℝ) / r) - f x| ≤
              ∫ _x in (((j - 1 : ℕ) : ℝ) / r)..((j : ℝ) / r), L / (r : ℝ) := by
            apply intervalIntegral.integral_mono_on hstep_le
            · apply ContinuousOn.intervalIntegrable_of_Icc hstep_le
              exact (continuousOn_const.sub (hcont.mono (fun x hx =>
                ⟨le_trans (by positivity) hx.1,
                 le_trans hx.2 ((div_le_one hrpos).mpr (by exact_mod_cast (le_trans hjb hbr)))⟩))).abs
            · exact intervalIntegrable_const
            · intro x hx
              have hxI : x ∈ Set.Icc (0 : ℝ) 1 :=
                ⟨le_trans (by positivity) hx.1,
                 le_trans hx.2 ((div_le_one hrpos).mpr (by exact_mod_cast (le_trans hjb hbr)))⟩
              have hjI : (j : ℝ) / (r : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
                ⟨by positivity, (div_le_one hrpos).mpr (by exact_mod_cast (le_trans hjb hbr))⟩
              calc |f ((j : ℝ) / r) - f x|
                  ≤ L * |(j : ℝ) / r - x| := hlip _ hjI _ hxI
                _ ≤ L * (1 / (r : ℝ)) := by
                    gcongr
                    rw [abs_of_nonneg (sub_nonneg.mpr hx.2)]
                    linarith [hx.1, hlen]
                _ = L / (r : ℝ) := by ring
          have hval : ∫ _x in (((j - 1 : ℕ) : ℝ) / r)..((j : ℝ) / r), L / (r : ℝ) = L / (r : ℝ) ^ 2 := by
            rw [intervalIntegral.integral_const, smul_eq_mul, hlen]; ring
          linarith
        · exact (hcont.mono fun x hx => ⟨le_trans (by positivity) hx.1,
            le_trans hx.2 ((div_le_one hrpos).mpr (by exact_mod_cast (le_trans hjb hbr)))⟩).intervalIntegrable_of_Icc hstep_le
    _ = ((Finset.Icc (a + 1) b).card : ℝ) * (L / (r : ℝ) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (r : ℝ) * (L / (r : ℝ) ^ 2) := by
        have hc : ((Finset.Icc (a + 1) b).card : ℝ) ≤ r := by
          have : (Finset.Icc (a + 1) b).card ≤ r := by simp; omega
          exact_mod_cast this
        exact mul_le_mul_of_nonneg_right hc (by positivity)
    _ = L / (r : ℝ) := by field_simp [hrpos.ne']

private lemma nazarov_weighted_sum_le :
    ∀ᶠ r : ℕ in atTop, ∀ c ∈ Set.Icc (0 : ℝ) (6000 * Real.pi),
      ∑ j ∈ Finset.Icc 1 (rStar r), wLog j * fNaz c ((j : ℝ) / r) ≤
        ∑ j ∈ Finset.Icc (rStar r + 1) r, wLog j * fNaz c ((j : ℝ) / r) := by
  obtain ⟨δ₀, hδ₀, hgap⟩ := fNaz_integral_gap
  set C : ℝ := 6000 * Real.pi
  set L : ℝ := (C + 2) / 24
  have hC_nn : 0 ≤ C := by positivity
  have hL_nn : 0 ≤ L := by positivity
  have hev_rs : ∀ᶠ r : ℕ in atTop, |(rStar r : ℝ) / (r : ℝ) - 1 / 2| < min (1 / 4) (3 * δ₀) := by
    have hpos : 0 < min (1 / 4 : ℝ) (3 * δ₀) := lt_min (by norm_num) (by linarith)
    filter_upwards [rStar_div_tendsto.eventually (Metric.ball_mem_nhds _ hpos)] with r hr
    simpa [Metric.mem_ball, Real.dist_eq] using hr
  have hev_q : ∀ᶠ r : ℕ in atTop,
      (Real.log ((r : ℝ) + 3)) ^ 2 / (r : ℝ) * ∑ j ∈ Finset.Icc 1 r, (wLog j - wLog r) < 6 * δ₀ := by
    filter_upwards [quicknotee_tendsto_zero.eventually (Metric.ball_mem_nhds _ (show (0 : ℝ) < 6 * δ₀ by linarith))] with r hr
    rw [Real.dist_eq, sub_zero, abs_of_nonneg] at hr
    · exact hr
    · exact mul_nonneg (by positivity)
        (Finset.sum_nonneg fun j hj => sub_nonneg.mpr (wLog_anti (Finset.mem_Icc.mp hj).2))
  have hev_L : ∀ᶠ r : ℕ in atTop, 2 * L / (r : ℝ) < δ₀ / 4 := by
    have h0 : Tendsto (fun r : ℕ => 2 * L / (r : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    exact h0.eventually (Iio_mem_nhds (by linarith))
  filter_upwards [rStar_spec, hev_rs, hev_q, hev_L, eventually_ge_atTop 1] with r hrs hrs_close hq hL_small hr1
  intro c hc
  set γ : ℝ := (rStar r : ℝ) / (r : ℝ)
  have hrpos : (0 : ℝ) < r := by positivity
  have hLlog_pos : 0 < (Real.log ((r : ℝ) + 3)) ^ 2 :=
    sq_pos_of_pos (lt_trans zero_lt_one (log_add_three_gt_one r))
  have hcont_fc : Continuous (fNaz c) := by
    unfold fNaz
    have hint_cont : Continuous (fun x : ℝ =>
        ∫ s in (0 : ℝ)..1, ((1 - s) ^ 3 / 6) * Real.cos (c * x * s)) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) _ _
    exact (continuous_pow 2).mul hint_cont
  -- Step 1: Integral gap at split point γ
  have hint_gap_γ : δ₀ / 2 ≤ (∫ x in γ..1, fNaz c x) - (∫ x in (0 : ℝ)..γ, fNaz c x) := by
    have h1 : ∫ x in (0 : ℝ)..γ, fNaz c x =
        (∫ x in (0 : ℝ)..(1 / 2), fNaz c x) + (∫ x in (1 / 2 : ℝ)..γ, fNaz c x) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hcont_fc.intervalIntegrable _ _) (hcont_fc.intervalIntegrable _ _)).symm
    have h2 : ∫ x in (1 / 2 : ℝ)..1, fNaz c x =
        (∫ x in (1 / 2 : ℝ)..γ, fNaz c x) + (∫ x in γ..1, fNaz c x) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hcont_fc.intervalIntegrable _ _) (hcont_fc.intervalIntegrable _ _)).symm
    have hshift : |∫ x in (1 / 2 : ℝ)..γ, fNaz c x| ≤ (1 / 24 : ℝ) * |γ - 1 / 2| := by
      have hγI : γ ∈ Set.Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hrpos).mpr (by exact_mod_cast hrs.2.1.le)⟩
      have hbd := intervalIntegral.norm_integral_le_of_norm_le_const (C := (1 / 24 : ℝ))
        (a := (1 / 2 : ℝ)) (b := γ) (f := fNaz c) (fun x hx => by
          rw [Real.norm_eq_abs]
          apply fNaz_abs_le c x
          rw [Set.uIoc_eq_union] at hx
          rcases hx with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
          · exact ⟨by linarith, le_trans hhi hγI.2⟩
          · exact ⟨le_trans hγI.1 hlo.le, by linarith⟩)
      simpa [Real.norm_eq_abs, mul_comm] using hbd
    have hγ_close : |γ - 1 / 2| < 3 * δ₀ := lt_of_lt_of_le hrs_close (min_le_right _ _)
    have hgap0 := hgap c hc
    have hdiff : ((∫ x in γ..1, fNaz c x) - (∫ x in (0 : ℝ)..γ, fNaz c x)) =
        ((∫ x in (1 / 2 : ℝ)..1, fNaz c x) - (∫ x in (0 : ℝ)..(1 / 2), fNaz c x)) -
        2 * ∫ x in (1 / 2 : ℝ)..γ, fNaz c x := by linarith
    have habs_le := (abs_le.mp hshift).2
    linarith
  -- Step 2: Unweighted Riemann sums
  have hlip_fc : ∀ x₁ ∈ Set.Icc (0 : ℝ) 1, ∀ x₂ ∈ Set.Icc (0 : ℝ) 1,
      |fNaz c x₁ - fNaz c x₂| ≤ L * |x₁ - x₂| :=
    fun x₁ hx₁ x₂ hx₂ => fNaz_lipschitz hC_nn hc.1 hc.2 hx₁ hx₂
  have hr1_sum := riemann_sum_lipschitz hL_nn hlip_fc hcont_fc.continuousOn hr1 (Nat.zero_le _) hrs.2.1.le
  have hr2_sum := riemann_sum_lipschitz hL_nn hlip_fc hcont_fc.continuousOn hr1 hrs.2.1.le le_rfl
  simp only [Nat.cast_zero, zero_div, zero_add, div_self hrpos.ne'] at hr1_sum hr2_sum
  have hunw : δ₀ / 4 ≤
      (1 / (r : ℝ)) * (∑ j ∈ Finset.Icc (rStar r + 1) r, fNaz c ((j : ℝ) / r)) -
      (1 / (r : ℝ)) * (∑ j ∈ Finset.Icc 1 (rStar r), fNaz c ((j : ℝ) / r)) := by
    simp only [γ] at hint_gap_γ
    have h1 := (abs_le.mp hr1_sum).2
    have h2 := (abs_le.mp hr2_sum).1
    have h2L : L / (r : ℝ) + L / (r : ℝ) = 2 * L / (r : ℝ) := by ring
    linarith
  -- Step 3: Pass from unweighted sum to weighted sum via quicknotee
  suffices hscaled : ((Real.log ((r : ℝ) + 3)) ^ 2 / (r : ℝ)) *
      ((∑ j ∈ Finset.Icc (rStar r + 1) r, wLog j * fNaz c ((j : ℝ) / r)) -
       (∑ j ∈ Finset.Icc 1 (rStar r), wLog j * fNaz c ((j : ℝ) / r))) ≥ 0 by
    have := nonneg_of_mul_nonneg_right hscaled (by positivity)
    linarith
  have hrew : ((Real.log ((r : ℝ) + 3)) ^ 2 / (r : ℝ)) *
      ((∑ j ∈ Finset.Icc (rStar r + 1) r, wLog j * fNaz c ((j : ℝ) / r)) -
       (∑ j ∈ Finset.Icc 1 (rStar r), wLog j * fNaz c ((j : ℝ) / r))) =
      ((1 / (r : ℝ)) * (∑ j ∈ Finset.Icc (rStar r + 1) r, fNaz c ((j : ℝ) / r)) -
       (1 / (r : ℝ)) * (∑ j ∈ Finset.Icc 1 (rStar r), fNaz c ((j : ℝ) / r))) +
      ((Real.log ((r : ℝ) + 3)) ^ 2 / (r : ℝ)) *
        ((∑ j ∈ Finset.Icc (rStar r + 1) r, (wLog j - wLog r) * fNaz c ((j : ℝ) / r)) -
         (∑ j ∈ Finset.Icc 1 (rStar r), (wLog j - wLog r) * fNaz c ((j : ℝ) / r))) := by
    have hsplit_sum : ∀ S : Finset ℕ,
        ∑ j ∈ S, wLog j * fNaz c ((j : ℝ) / r) =
          wLog r * (∑ j ∈ S, fNaz c ((j : ℝ) / r)) +
          ∑ j ∈ S, (wLog j - wLog r) * fNaz c ((j : ℝ) / r) := by
      intro S
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => by ring
    have hmul_w : ((Real.log ((r : ℝ) + 3)) ^ 2 / (r : ℝ)) * wLog r = 1 / (r : ℝ) := by
      unfold wLog
      have hLne : Real.log ((r : ℝ) + 3) ≠ 0 := (lt_trans zero_lt_one (log_add_three_gt_one r)).ne'
      field_simp [hLne, hrpos.ne']
    set A₁ := ∑ j ∈ Finset.Icc (rStar r + 1) r, fNaz c ((j : ℝ) / r)
    set A₂ := ∑ j ∈ Finset.Icc 1 (rStar r), fNaz c ((j : ℝ) / r)
    set B₁ := ∑ j ∈ Finset.Icc (rStar r + 1) r, (wLog j - wLog r) * fNaz c ((j : ℝ) / r)
    set B₂ := ∑ j ∈ Finset.Icc 1 (rStar r), (wLog j - wLog r) * fNaz c ((j : ℝ) / r)
    rw [hsplit_sum, hsplit_sum]
    change ((Real.log ((r : ℝ) + 3)) ^ 2 / (r : ℝ)) * ((wLog r * A₁ + B₁) - (wLog r * A₂ + B₂)) =
      (1 / (r : ℝ) * A₁ - 1 / (r : ℝ) * A₂) + ((Real.log ((r : ℝ) + 3)) ^ 2 / (r : ℝ)) * (B₁ - B₂)
    calc ((Real.log ((r : ℝ) + 3)) ^ 2 / (r : ℝ)) * ((wLog r * A₁ + B₁) - (wLog r * A₂ + B₂))
        = (((Real.log ((r : ℝ) + 3)) ^ 2 / (r : ℝ)) * wLog r) * A₁ -
          (((Real.log ((r : ℝ) + 3)) ^ 2 / (r : ℝ)) * wLog r) * A₂ +
          ((Real.log ((r : ℝ) + 3)) ^ 2 / (r : ℝ)) * (B₁ - B₂) := by ring
      _ = (1 / (r : ℝ) * A₁ - 1 / (r : ℝ) * A₂) +
          ((Real.log ((r : ℝ) + 3)) ^ 2 / (r : ℝ)) * (B₁ - B₂) := by rw [hmul_w]
  rw [hrew]
  have herr : |(Real.log ((r : ℝ) + 3)) ^ 2 / (r : ℝ) *
      ((∑ j ∈ Finset.Icc (rStar r + 1) r, (wLog j - wLog r) * fNaz c ((j : ℝ) / r)) -
       (∑ j ∈ Finset.Icc 1 (rStar r), (wLog j - wLog r) * fNaz c ((j : ℝ) / r)))| ≤ δ₀ / 4 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have h1 : |(∑ j ∈ Finset.Icc (rStar r + 1) r, (wLog j - wLog r) * fNaz c ((j : ℝ) / r)) -
          (∑ j ∈ Finset.Icc 1 (rStar r), (wLog j - wLog r) * fNaz c ((j : ℝ) / r))| ≤
        (1 / 24 : ℝ) * ∑ j ∈ Finset.Icc 1 r, (wLog j - wLog r) := by
      have hsplit : Finset.Icc 1 r = Finset.Icc 1 (rStar r) ∪ Finset.Icc (rStar r + 1) r := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      have hdis : Disjoint (Finset.Icc 1 (rStar r)) (Finset.Icc (rStar r + 1) r) := by
        rw [Finset.disjoint_left]; intro j h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
      have hbd : ∀ S ⊆ Finset.Icc 1 r,
          |∑ j ∈ S, (wLog j - wLog r) * fNaz c ((j : ℝ) / r)| ≤
            (1 / 24 : ℝ) * ∑ j ∈ S, (wLog j - wLog r) := by
        intro S hS
        rw [Finset.mul_sum]
        calc |∑ j ∈ S, (wLog j - wLog r) * fNaz c ((j : ℝ) / r)|
            ≤ ∑ j ∈ S, |(wLog j - wLog r) * fNaz c ((j : ℝ) / r)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j ∈ S, (1 / 24 : ℝ) * (wLog j - wLog r) := by
              refine Finset.sum_le_sum fun j hj => ?_
              have hjr := Finset.mem_Icc.mp (hS hj)
              have hnn : 0 ≤ wLog j - wLog r := sub_nonneg.mpr (wLog_anti hjr.2)
              rw [abs_mul, abs_of_nonneg hnn]
              have hfbd := fNaz_abs_le c ((j : ℝ) / r)
                ⟨by positivity, (div_le_one hrpos).mpr (by exact_mod_cast hjr.2)⟩
              nlinarith
      have hA := hbd (Finset.Icc (rStar r + 1) r) (fun j hj => by simp only [Finset.mem_Icc] at hj ⊢; omega)
      have hB := hbd (Finset.Icc 1 (rStar r)) (fun j hj => by simp only [Finset.mem_Icc] at hj ⊢; omega)
      have htri := abs_sub_le (∑ j ∈ Finset.Icc (rStar r + 1) r, (wLog j - wLog r) * fNaz c ((j : ℝ) / r))
        0 (∑ j ∈ Finset.Icc 1 (rStar r), (wLog j - wLog r) * fNaz c ((j : ℝ) / r))
      rw [sub_zero, zero_sub, abs_neg] at htri
      rw [hsplit, Finset.sum_union hdis]
      linarith
    calc (Real.log ((r : ℝ) + 3)) ^ 2 / (r : ℝ) *
          |(∑ j ∈ Finset.Icc (rStar r + 1) r, (wLog j - wLog r) * fNaz c ((j : ℝ) / r)) -
           (∑ j ∈ Finset.Icc 1 (rStar r), (wLog j - wLog r) * fNaz c ((j : ℝ) / r))|
        ≤ (Real.log ((r : ℝ) + 3)) ^ 2 / (r : ℝ) * ((1 / 24 : ℝ) * ∑ j ∈ Finset.Icc 1 r, (wLog j - wLog r)) := by
          gcongr
      _ = (1 / 24 : ℝ) * ((Real.log ((r : ℝ) + 3)) ^ 2 / (r : ℝ) * ∑ j ∈ Finset.Icc 1 r, (wLog j - wLog r)) := by
          ring
      _ ≤ (1 / 24 : ℝ) * (6 * δ₀) := by linarith
      _ = δ₀ / 4 := by ring
  linarith [(abs_le.mp herr).1]

set_option maxHeartbeats 800000 in
/-- Lemma 5.1 (`unitdisk`): for sufficiently large `r`, `‖tildeH r (exp (I * t))‖ ≤ 1` for all `t`. -/
private lemma norm_tildeH_le_one_circle :
    ∀ᶠ r : ℕ in atTop, ∀ t : ℝ, ‖tildeH r (Complex.exp ((t : ℂ) * I))‖ ≤ 1 := by
  filter_upwards [rStar_spec, tildeLam_bounds, norm_tildeH_large_t, nazarov_weighted_sum_le,
    eventually_ge_atTop (max 10000000 ⌈12 * (6000 * Real.pi) ^ 4⌉₊)] with r hrs htl hlarge hnaz hr_max
  have hr_big : 10000000 ≤ r := le_trans (le_max_left _ _) hr_max
  have hr_huge : 12 * (6000 * Real.pi) ^ 4 ≤ (r : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast (le_trans (le_max_right _ _) hr_max))
  clear hr_max
  -- Reduce to t ∈ [0, π] by 2π-periodicity and conjugation symmetry
  suffices h0pi : ∀ t : ℝ, 0 ≤ t → t ≤ Real.pi → ‖tildeH r (Complex.exp ((t : ℂ) * I))‖ ≤ 1 by
    intro t
    set k : ℤ := ⌊(t + Real.pi) / (2 * Real.pi)⌋
    set t' : ℝ := t - k * (2 * Real.pi)
    have ht'_lo : -Real.pi ≤ t' := by
      have h1 : (k : ℝ) ≤ (t + Real.pi) / (2 * Real.pi) := Int.floor_le _
      have h2 := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mp h1
      linarith
    have ht'_hi : t' ≤ Real.pi := by
      have h1 : (t + Real.pi) / (2 * Real.pi) < (k : ℝ) + 1 := Int.lt_floor_add_one _
      have h2 := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mp h1
      linarith
    have hexp_eq : Complex.exp ((t : ℂ) * I) = Complex.exp ((t' : ℂ) * I) := by
      have : (t : ℂ) * I = (t' : ℂ) * I + k * (2 * Real.pi * I) := by
        simp only [t']; push_cast; ring
      rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hexp_eq]
    rcases le_total 0 t' with hge | hle
    · exact h0pi t' hge ht'_hi
    · have hconj : Complex.exp ((t' : ℂ) * I) = starRingEnd ℂ (Complex.exp (((-t' : ℝ) : ℂ) * I)) := by
        rw [← Complex.exp_conj]; congr 1; simp [map_mul, Complex.conj_ofReal]
      rw [hconj, norm_tildeH_conj]
      exact h0pi (-t') (by linarith) (by linarith)
  intro t ht0 htpi
  have hrpos : (0 : ℝ) < r := by positivity
  by_cases hbig : 6000 * Real.pi / (r : ℝ) ≤ t
  · set u : ℝ := t / (2 * Real.pi)
    have hu_nn : 0 ≤ u := by positivity
    have hu1 : |u| ≤ 1 / 2 := by
      rw [abs_of_nonneg hu_nn, div_le_iff₀ (by positivity)]; linarith
    have hu2 : (3000 : ℝ) / (r : ℝ) ≤ |u| := by
      rw [abs_of_nonneg hu_nn]
      have : (3000 : ℝ) / (r : ℝ) = (6000 * Real.pi / (r : ℝ)) / (2 * Real.pi) := by
        field_simp [Real.pi_pos.ne']; ring
      rw [this]
      exact div_le_div_of_nonneg_right hbig (by positivity)
    have heq : (t : ℂ) * I = 2 * Real.pi * u * I := by
      simp only [u]; push_cast; field_simp [Real.pi_pos.ne']
    rw [heq]
    have hbd := hlarge u hu1 hu2
    have hnn : 0 ≤ |u| / (16 * (Real.log ((r : ℝ) + 3)) ^ 2) := by positivity
    linarith
  · push Not at hbig
    set c : ℝ := t * (r : ℝ)
    have hc_mem : c ∈ Set.Icc (0 : ℝ) (6000 * Real.pi) := by
      refine ⟨by positivity, ?_⟩
      have := (lt_div_iff₀ hrpos).mp hbig
      linarith
    have hlam := lam_bounds (show 1 ≤ r by omega)
    have htl_pos : 0 < tildeLam r := by linarith [htl.2.1]
    have hinv_ne : invTildeLam r ≠ 0 := (inv_pos.mp htl_pos).ne'
    -- Bound |Im(tildeH r (exp (t*I)))| ≤ 24 * t
    have him : |(tildeH r (Complex.exp ((t : ℂ) * I))).im| ≤ 24 * t := by
      have him_eq : (tildeH r (Complex.exp ((t : ℂ) * I))).im =
          tildeLam r * ∑ j ∈ Finset.Icc 1 r, epsSign r j * dCoeff r j * Real.sin ((j : ℝ) * t) := by
        unfold tildeH
        rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Complex.im_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Complex.exp_nat_mul, show (j : ℂ) * ((t : ℂ) * I) = (((j : ℝ) * t : ℝ) : ℂ) * I by push_cast; ring]
        rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
          Complex.exp_ofReal_mul_I_im]
      rw [him_eq, abs_mul, abs_of_nonneg htl_pos.le]
      calc tildeLam r * |∑ j ∈ Finset.Icc 1 r, epsSign r j * dCoeff r j * Real.sin ((j : ℝ) * t)|
          ≤ tildeLam r * ∑ j ∈ Finset.Icc 1 r, |epsSign r j * dCoeff r j * Real.sin ((j : ℝ) * t)| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) htl_pos.le
        _ ≤ tildeLam r * ∑ j ∈ Finset.Icc 1 r, dCoeff r j * ((j : ℝ) * t) := by
            apply mul_le_mul_of_nonneg_left _ htl_pos.le
            refine Finset.sum_le_sum fun j hj => ?_
            rw [abs_mul, abs_mul]
            have heps : |epsSign r j| = 1 := by unfold epsSign; split_ifs <;> norm_num
            have hd_nn : 0 ≤ dCoeff r j := mul_nonneg (by linarith) (aCoeff_pos (Finset.mem_Icc.mp hj).1).le
            rw [heps, one_mul, abs_of_nonneg hd_nn]
            have hsin : |Real.sin ((j : ℝ) * t)| ≤ (j : ℝ) * t := by
              have hjt_nn : 0 ≤ (j : ℝ) * t := by positivity
              simpa [Real.sin_zero, abs_of_nonneg hjt_nn] using
                Real.abs_sin_sub_sin_le ((j : ℝ) * t) 0
            exact mul_le_mul_of_nonneg_left hsin hd_nn
        _ = tildeLam r * lam r * t * ∑ j ∈ Finset.Icc 1 r, (j : ℝ) * aCoeff j := by
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => by unfold dCoeff; ring
        _ ≤ 2 * 3 * t * 4 := by
            have hsum4 := sum_j_aCoeff_le_four r
            have hsum_nn : 0 ≤ ∑ j ∈ Finset.Icc 1 r, (j : ℝ) * aCoeff j :=
              Finset.sum_nonneg fun j hj => mul_nonneg (Nat.cast_nonneg _) (aCoeff_pos (Finset.mem_Icc.mp hj).1).le
            have h1 : tildeLam r * lam r ≤ 2 * 3 := by nlinarith [htl.2.1, htl.2.2, hlam.1, hlam.2]
            have h2 : tildeLam r * lam r * t ≤ 2 * 3 * t := mul_le_mul_of_nonneg_right h1 ht0
            nlinarith
        _ = 24 * t := by ring
    -- Bound Re(tildeH r (exp (t*I))) ∈ [0, 1 - 300 * t^2]
    have hre_eq : (tildeH r (Complex.exp ((t : ℂ) * I))).re =
        1 - (1 / 2 : ℝ) * tildeLam r * lam r * dVal r (rStar r) * t ^ 2 +
        tildeLam r * lam r * (r : ℝ) ^ 2 * t ^ 4 *
          ((∑ j ∈ Finset.Icc 1 (rStar r), wLog j * fNaz c ((j : ℝ) / r)) -
           (∑ j ∈ Finset.Icc (rStar r + 1) r, wLog j * fNaz c ((j : ℝ) / r))) := by
      have hre0 : (tildeH r (Complex.exp ((t : ℂ) * I))).re =
          tildeLam r * ∑ j ∈ Finset.Icc 1 r, epsSign r j * dCoeff r j * Real.cos ((j : ℝ) * t) := by
        unfold tildeH
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Complex.exp_nat_mul, show (j : ℂ) * ((t : ℂ) * I) = (((j : ℝ) * t : ℝ) : ℂ) * I by push_cast; ring]
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Complex.exp_ofReal_mul_I_re]
      rw [hre0]
      have hcos_term : ∀ j ∈ Finset.Icc 1 r,
          epsSign r j * dCoeff r j * Real.cos ((j : ℝ) * t) =
            epsSign r j * dCoeff r j - (1 / 2 : ℝ) * lam r * t ^ 2 * (epsSign r j * wLog j) +
            lam r * (r : ℝ) ^ 2 * t ^ 4 * (epsSign r j * (wLog j * fNaz c ((j : ℝ) / r))) := by
        intro j hj
        have hjpos : (0 : ℝ) < j := by have := (Finset.mem_Icc.mp hj).1; positivity
        have hct := cos_taylor4_integral ((j : ℝ) * t)
        have hf : fNaz c ((j : ℝ) / r) = ((j : ℝ) / r) ^ 2 *
            ∫ s in (0 : ℝ)..1, ((1 - s) ^ 3 / 6) * Real.cos ((j : ℝ) * t * s) := by
          unfold fNaz
          have : c * ((j : ℝ) / r) = (j : ℝ) * t := by simp only [c]; field_simp [hrpos.ne']
          simp_rw [this]
        have hcos_id : Real.cos ((j : ℝ) * t) =
            1 - ((j : ℝ) * t) ^ 2 / 2 + (j : ℝ) ^ 2 * (r : ℝ) ^ 2 * t ^ 4 * fNaz c ((j : ℝ) / r) := by
          rw [hf]
          have : (j : ℝ) ^ 2 * (r : ℝ) ^ 2 * t ^ 4 * (((j : ℝ) / r) ^ 2 *
              ∫ s in (0 : ℝ)..1, ((1 - s) ^ 3 / 6) * Real.cos ((j : ℝ) * t * s)) =
              ((j : ℝ) * t) ^ 4 * ∫ s in (0 : ℝ)..1, ((1 - s) ^ 3 / 6) * Real.cos ((j : ℝ) * t * s) := by
            field_simp [hrpos.ne']
          linarith
        rw [hcos_id]
        unfold dCoeff aCoeff wLog
        field_simp [hjpos.ne']
      rw [Finset.sum_congr rfl hcos_term, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
      have hsplit : Finset.Icc 1 r = Finset.Icc 1 (rStar r) ∪ Finset.Icc (rStar r + 1) r := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      have hdis : Disjoint (Finset.Icc 1 (rStar r)) (Finset.Icc (rStar r + 1) r) := by
        rw [Finset.disjoint_left]; intro j h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
      have hsum_eps : ∀ g : ℕ → ℝ,
          ∑ j ∈ Finset.Icc 1 r, epsSign r j * g j =
            (∑ j ∈ Finset.Icc 1 (rStar r), g j) - (∑ j ∈ Finset.Icc (rStar r + 1) r, g j) := by
        intro g
        rw [hsplit, Finset.sum_union hdis]
        have h1 : ∑ j ∈ Finset.Icc 1 (rStar r), epsSign r j * g j = ∑ j ∈ Finset.Icc 1 (rStar r), g j :=
          Finset.sum_congr rfl fun j hj => by simp [epsSign, (Finset.mem_Icc.mp hj).2]
        have h2 : ∑ j ∈ Finset.Icc (rStar r + 1) r, epsSign r j * g j =
            -(∑ j ∈ Finset.Icc (rStar r + 1) r, g j) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun j hj => ?_
          have : ¬(j ≤ rStar r) := by have := (Finset.mem_Icc.mp hj).1; omega
          simp [epsSign, this]
        rw [h1, h2]; ring
      rw [hsum_eps wLog, hsum_eps (fun j => wLog j * fNaz c ((j : ℝ) / r))]
      change tildeLam r * (invTildeLam r - (1 / 2 : ℝ) * lam r * t ^ 2 * dVal r (rStar r) +
        lam r * (r : ℝ) ^ 2 * t ^ 4 * _) = _
      have hmul1 : tildeLam r * invTildeLam r = 1 := inv_mul_cancel₀ hinv_ne
      rw [mul_add, mul_sub, hmul1]
      ring
    have hre_hi : (tildeH r (Complex.exp ((t : ℂ) * I))).re ≤ 1 - 300 * t ^ 2 := by
      have hnaz_c := hnaz c hc_mem
      have hcoeff_nn : 0 ≤ tildeLam r * lam r * (r : ℝ) ^ 2 * t ^ 4 := by
        have : 0 ≤ lam r := by linarith [hlam.1]
        positivity
      have h3rd : tildeLam r * lam r * (r : ℝ) ^ 2 * t ^ 4 *
          ((∑ j ∈ Finset.Icc 1 (rStar r), wLog j * fNaz c ((j : ℝ) / r)) -
           (∑ j ∈ Finset.Icc (rStar r + 1) r, wLog j * fNaz c ((j : ℝ) / r))) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hcoeff_nn (sub_nonpos.mpr hnaz_c)
      have h2nd : 300 * t ^ 2 ≤ (1 / 2 : ℝ) * tildeLam r * lam r * dVal r (rStar r) * t ^ 2 := by
        have htl1 : 1 ≤ tildeLam r := htl.2.1.le
        have hl1 : 1 ≤ lam r := hlam.1.le
        have hd600 : 600 ≤ dVal r (rStar r) := hrs.2.2.1
        have h1 : 1 ≤ tildeLam r * lam r := by nlinarith
        have hprod : 600 ≤ tildeLam r * lam r * dVal r (rStar r) := by nlinarith
        nlinarith [sq_nonneg t]
      linarith
    have ht_small : t ≤ 1 / 100 := by
      have hr_big' : (10000000 : ℝ) ≤ r := by exact_mod_cast hr_big
      have hpi4 : Real.pi < 4 := Real.pi_lt_four
      have h1 : 6000 * Real.pi / (r : ℝ) ≤ 24000 / 10000000 := by
        rw [div_le_div_iff₀ hrpos (by norm_num)]; nlinarith
      linarith
    have hre_lo : 0 ≤ (tildeH r (Complex.exp ((t : ℂ) * I))).re := by
      have h4_bound : |(∑ j ∈ Finset.Icc 1 (rStar r), wLog j * fNaz c ((j : ℝ) / r)) -
          (∑ j ∈ Finset.Icc (rStar r + 1) r, wLog j * fNaz c ((j : ℝ) / r))| ≤ (r : ℝ) := by
        have h1 : ∀ S ⊆ Finset.Icc 1 r,
            |∑ j ∈ S, wLog j * fNaz c ((j : ℝ) / r)| ≤ (S.card : ℝ) * (1 / 24 : ℝ) := by
          intro S hS
          calc |∑ j ∈ S, wLog j * fNaz c ((j : ℝ) / r)|
              ≤ ∑ j ∈ S, |wLog j * fNaz c ((j : ℝ) / r)| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _j ∈ S, (1 / 24 : ℝ) := by
                refine Finset.sum_le_sum fun j hj => ?_
                have hjr := Finset.mem_Icc.mp (hS hj)
                rw [abs_mul, abs_of_pos (wLog_pos j)]
                have hf := fNaz_abs_le c ((j : ℝ) / r)
                  ⟨by positivity, (div_le_one hrpos).mpr (by exact_mod_cast hjr.2)⟩
                nlinarith [wLog_lt_one j, wLog_pos j]
            _ = (S.card : ℝ) * (1 / 24 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
        have hA := h1 (Finset.Icc 1 (rStar r)) (fun j hj => by simp only [Finset.mem_Icc] at hj ⊢; omega)
        have hB := h1 (Finset.Icc (rStar r + 1) r) (fun j hj => by simp only [Finset.mem_Icc] at hj ⊢; omega)
        have htri := abs_sub_le (∑ j ∈ Finset.Icc 1 (rStar r), wLog j * fNaz c ((j : ℝ) / r)) 0
          (∑ j ∈ Finset.Icc (rStar r + 1) r, wLog j * fNaz c ((j : ℝ) / r))
        rw [sub_zero, zero_sub, abs_neg] at htri
        have hcA : ((Finset.Icc 1 (rStar r)).card : ℝ) ≤ r := by
          have : (Finset.Icc 1 (rStar r)).card ≤ r := by simp [hrs.2.1.le]
          exact_mod_cast this
        have hcB : ((Finset.Icc (rStar r + 1) r).card : ℝ) ≤ r := by
          have : (Finset.Icc (rStar r + 1) r).card ≤ r := by simp
          exact_mod_cast this
        linarith
      clear hlarge hnaz
      have h2nd_hi : (1 / 2 : ℝ) * tildeLam r * lam r * dVal r (rStar r) * t ^ 2 ≤ 1 / 4 := by
        have h1 : tildeLam r * lam r ≤ 6 := by
          have := mul_le_mul htl.2.2 hlam.2.le (by linarith [hlam.1]) (by norm_num)
          linarith
        have hprod : (1 / 2 : ℝ) * tildeLam r * lam r * dVal r (rStar r) ≤ 1803 := by
          have h2 : (1 / 2 : ℝ) * (tildeLam r * lam r) ≤ 3 := by linarith
          have h3 := mul_le_mul h2 hrs.2.2.2 (by linarith [hrs.2.2.1]) (by norm_num)
          linarith [show (1 / 2 : ℝ) * tildeLam r * lam r * dVal r (rStar r) =
            (1 / 2 : ℝ) * (tildeLam r * lam r) * dVal r (rStar r) by ring]
        have ht2 : t ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := pow_le_pow_left₀ ht0 ht_small 2
        have h1803 : 1803 * t ^ 2 ≤ 1803 * (1 / 100 : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left ht2 (by norm_num)
        have hmul_le : ((1 / 2 : ℝ) * tildeLam r * lam r * dVal r (rStar r)) * t ^ 2 ≤ 1803 * t ^ 2 :=
          mul_le_mul_of_nonneg_right hprod (sq_nonneg t)
        linarith
      have h4_hi : tildeLam r * lam r * (r : ℝ) ^ 2 * t ^ 4 * (r : ℝ) ≤ 1 / 2 := by
        have hrt : (r : ℝ) * t ≤ 6000 * Real.pi := by linarith [hc_mem.2]
        have hrt4 : (r : ℝ) ^ 4 * t ^ 4 ≤ (6000 * Real.pi) ^ 4 := by
          rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hrt 4
        have hprod : tildeLam r * lam r ≤ 6 := by
          have := mul_le_mul htl.2.2 hlam.2.le (by linarith [hlam.1]) (by norm_num)
          linarith
        have hrew4 : tildeLam r * lam r * (r : ℝ) ^ 2 * t ^ 4 * (r : ℝ) =
            (tildeLam r * lam r) * (((r : ℝ) ^ 4 * t ^ 4) / (r : ℝ)) := by
          field_simp [hrpos.ne']
        rw [hrew4]
        have hdiv : ((r : ℝ) ^ 4 * t ^ 4) / (r : ℝ) ≤ 1 / 12 := by
          rw [div_le_iff₀ hrpos]; linarith
        have hnn : 0 ≤ ((r : ℝ) ^ 4 * t ^ 4) / (r : ℝ) := by positivity
        have hmul_le := mul_le_mul hprod hdiv hnn (by norm_num)
        linarith
      have h4_neg : -(tildeLam r * lam r * (r : ℝ) ^ 2 * t ^ 4 * (r : ℝ)) ≤
          tildeLam r * lam r * (r : ℝ) ^ 2 * t ^ 4 *
            ((∑ j ∈ Finset.Icc 1 (rStar r), wLog j * fNaz c ((j : ℝ) / r)) -
             (∑ j ∈ Finset.Icc (rStar r + 1) r, wLog j * fNaz c ((j : ℝ) / r))) := by
        have hcoeff_nn : 0 ≤ tildeLam r * lam r * (r : ℝ) ^ 2 * t ^ 4 := by
          have : 0 ≤ lam r := by linarith [hlam.1]
          positivity
        have hmul := mul_le_mul_of_nonneg_left (abs_le.mp h4_bound).1 hcoeff_nn
        linarith
      linarith
    -- Combine Re ∈ [0, 1 - 300 t^2] and |Im| ≤ 24 t
    clear hr_huge hlarge hnaz
    have hsq_le : ‖tildeH r (Complex.exp ((t : ℂ) * I))‖ ^ 2 ≤ 1 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      have hre_sq : (tildeH r (Complex.exp ((t : ℂ) * I))).re ^ 2 ≤ (1 - 300 * t ^ 2) ^ 2 :=
        pow_le_pow_left₀ hre_lo hre_hi 2
      have him_sq : (tildeH r (Complex.exp ((t : ℂ) * I))).im ^ 2 ≤ (24 * t) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) him 2
      have ht2 : t ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := pow_le_pow_left₀ ht0 ht_small 2
      have h1 : (1 - 300 * t ^ 2) ^ 2 + (24 * t) ^ 2 ≤ 1 := by
        have h9 : 90000 * t ^ 2 ≤ 24 := by linarith
        have h9t : 90000 * t ^ 2 * t ^ 2 ≤ 24 * t ^ 2 :=
          mul_le_mul_of_nonneg_right h9 (sq_nonneg t)
        linarith [show (1 - 300 * t ^ 2) ^ 2 + (24 * t) ^ 2 =
          1 - 24 * t ^ 2 + 90000 * t ^ 2 * t ^ 2 by ring]
      linarith
    have hnorm_nn := norm_nonneg (tildeH r (Complex.exp ((t : ℂ) * I)))
    nlinarith

/-- Maximum modulus principle extends `‖tildeH r w‖ ≤ 1` to the closed unit disk. -/
private lemma norm_tildeH_le_one_closedBall :
    ∀ᶠ r : ℕ in atTop, ∀ w ∈ Metric.closedBall (0 : ℂ) 1, ‖tildeH r w‖ ≤ 1 := by
  filter_upwards [norm_tildeH_le_one_circle] with r hcirc w hw
  have hd : DiffContOnCl ℂ (tildeH r) (Metric.ball 0 1) := by
    apply Differentiable.diffContOnCl
    unfold tildeH
    exact (Differentiable.fun_sum fun j _ => (differentiable_id.pow j).const_mul _).const_mul _
  have hfront : ∀ z ∈ frontier (Metric.ball (0 : ℂ) 1), ‖tildeH r z‖ ≤ 1 := by
    intro z hz
    rw [frontier_ball (0 : ℂ) one_ne_zero, Metric.mem_sphere, dist_zero_right] at hz
    have hzeq : z = Complex.exp ((Complex.arg z : ℂ) * I) := by
      simpa [hz] using (Complex.norm_mul_exp_arg_mul_I z).symm
    rw [hzeq]
    exact hcirc (Complex.arg z)
  have hcl : w ∈ closure (Metric.ball (0 : ℂ) 1) := by
    rwa [closure_ball (0 : ℂ) one_ne_zero]
  exact Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hd hfront hcl

private noncomputable def hFunc (r : ℕ) (a : ℝ) (z : ℂ) : ℂ :=
  ((1 - a ^ 10 : ℝ) : ℂ) * tildeH r z

/-- Geometric region `G_a` inside the lens bounded by `I_{a/2}` and `I_a`. -/
private def inGa (a : ℝ) (z : ℂ) : Prop :=
  ‖z‖ < 1 ∧ Real.cos a < z.re ∧ 1 - ‖z‖ ^ 2 ≤ 2 * Real.cos a * (z.re - Real.cos a)

set_option maxHeartbeats 800000 in
private lemma hFunc_mem_inGa :
    ∀ᶠ r : ℕ in atTop, ∀ a : ℝ, 0 < a → a ≤ 1 / (r : ℝ) ^ 2 → a ≤ 1 / 100 →
      ∀ t : ℝ, |t| ≤ a / 2000 →
        inGa a (hFunc r a (Complex.exp (2 * Real.pi * t * I))) := by
  filter_upwards [rStar_spec, tildeLam_bounds, norm_tildeH_le_one_circle,
    eventually_ge_atTop 1000] with r hrs htl hcirc hr1000
  intro a ha0 ha_r ha_small t ht
  have hrpos : (0 : ℝ) < r := by positivity
  have ha10_lt : a ^ 10 < 1 := by
    have : a ≤ 1 / 2 := by linarith
    have : a ^ 10 ≤ (1 / 2 : ℝ) ^ 10 := pow_le_pow_left₀ ha0.le this 10
    linarith [show (1 / 2 : ℝ) ^ 10 < 1 by norm_num]
  set z : ℂ := hFunc r a (Complex.exp (2 * Real.pi * t * I))
  have hz_norm : ‖z‖ ≤ 1 - a ^ 10 := by
    unfold z hFunc
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have h1 := hcirc (2 * Real.pi * t)
    have heq : ((2 * Real.pi * t : ℝ) : ℂ) * I = 2 * Real.pi * t * I := by push_cast; ring
    rw [heq] at h1
    exact mul_le_of_le_one_right (by linarith) h1
  have hz_lt1 : ‖z‖ < 1 := lt_of_le_of_lt hz_norm (by linarith [pow_pos ha0 10])
  -- Lower bound Re(tildeH r (exp (2πt I))) ≥ 1 - (1/20) a^2
  have hlam := lam_bounds (show 1 ≤ r by omega)
  have htl_pos : 0 < tildeLam r := by linarith [htl.2.1]
  have hinv_ne : invTildeLam r ≠ 0 := (inv_pos.mp htl_pos).ne'
  have hre_tilde : 1 - (1 / 20 : ℝ) * a ^ 2 ≤ (tildeH r (Complex.exp (2 * Real.pi * t * I))).re := by
    set u : ℝ := 2 * Real.pi * t
    have hre0 : (tildeH r (Complex.exp (2 * Real.pi * t * I))).re =
        tildeLam r * ∑ j ∈ Finset.Icc 1 r, epsSign r j * dCoeff r j * Real.cos ((j : ℝ) * u) := by
      unfold tildeH
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Complex.exp_nat_mul, show (j : ℂ) * (2 * Real.pi * t * I) = (((j : ℝ) * u : ℝ) : ℂ) * I by
        simp only [u]; push_cast; ring]
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.exp_ofReal_mul_I_re]
    rw [hre0]
    have hterm : ∀ j ∈ Finset.Icc 1 r,
        epsSign r j * dCoeff r j - (1 / 2 : ℝ) * lam r * u ^ 2 * (epsSign r j * wLog j) -
          lam r * (j : ℝ) ^ 2 * u ^ 4 / 24 ≤
        epsSign r j * dCoeff r j * Real.cos ((j : ℝ) * u) := by
      intro j hj
      have hjpos : (0 : ℝ) < j := by have := (Finset.mem_Icc.mp hj).1; positivity
      have hct := abs_cos_sub_taylor2_le ((j : ℝ) * u)
      have hbd : |epsSign r j * dCoeff r j * (Real.cos ((j : ℝ) * u) - 1 + ((j : ℝ) * u) ^ 2 / 2)| ≤
          lam r * (j : ℝ) ^ 2 * u ^ 4 / 24 := by
        rw [abs_mul, abs_mul]
        have heps : |epsSign r j| = 1 := by unfold epsSign; split_ifs <;> norm_num
        have hd_nn : 0 ≤ dCoeff r j := mul_nonneg (by linarith) (aCoeff_pos (Finset.mem_Icc.mp hj).1).le
        rw [heps, one_mul, abs_of_nonneg hd_nn]
        calc dCoeff r j * |Real.cos ((j : ℝ) * u) - 1 + ((j : ℝ) * u) ^ 2 / 2|
            ≤ dCoeff r j * (((j : ℝ) * u) ^ 4 / 24) := mul_le_mul_of_nonneg_left hct hd_nn
          _ = lam r * wLog j * (j : ℝ) ^ 2 * u ^ 4 / 24 := by
              unfold dCoeff aCoeff wLog; field_simp [hjpos.ne']
          _ ≤ lam r * 1 * (j : ℝ) ^ 2 * u ^ 4 / 24 := by
              have := (wLog_lt_one j).le
              have : 0 ≤ lam r := by linarith
              gcongr
          _ = lam r * (j : ℝ) ^ 2 * u ^ 4 / 24 := by ring
      have h1 := (abs_le.mp hbd).1
      have hid : epsSign r j * dCoeff r j * (Real.cos ((j : ℝ) * u) - 1 + ((j : ℝ) * u) ^ 2 / 2) =
          epsSign r j * dCoeff r j * Real.cos ((j : ℝ) * u) - epsSign r j * dCoeff r j +
          (1 / 2 : ℝ) * lam r * u ^ 2 * (epsSign r j * wLog j) := by
        unfold dCoeff aCoeff wLog; field_simp [hjpos.ne']
      linarith
    have hsum_ge := Finset.sum_le_sum hterm
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum_ge
    have hsum_eps : ∑ j ∈ Finset.Icc 1 r, epsSign r j * wLog j = dVal r (rStar r) := by
      have hsplit : Finset.Icc 1 r = Finset.Icc 1 (rStar r) ∪ Finset.Icc (rStar r + 1) r := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      have hdis : Disjoint (Finset.Icc 1 (rStar r)) (Finset.Icc (rStar r + 1) r) := by
        rw [Finset.disjoint_left]; intro j h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
      rw [hsplit, Finset.sum_union hdis]
      unfold dVal
      have h1 : ∑ j ∈ Finset.Icc 1 (rStar r), epsSign r j * wLog j = ∑ j ∈ Finset.Icc 1 (rStar r), wLog j :=
        Finset.sum_congr rfl fun j hj => by simp [epsSign, (Finset.mem_Icc.mp hj).2]
      have h2 : ∑ j ∈ Finset.Icc (rStar r + 1) r, epsSign r j * wLog j =
          -(∑ j ∈ Finset.Icc (rStar r + 1) r, wLog j) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j hj => ?_
        have : ¬(j ≤ rStar r) := by have := (Finset.mem_Icc.mp hj).1; omega
        simp [epsSign, this]
      rw [h1, h2]; ring
    rw [hsum_eps] at hsum_ge
    have hj2_sum : ∑ j ∈ Finset.Icc 1 r, lam r * (j : ℝ) ^ 2 * u ^ 4 / 24 ≤
        lam r * (r : ℝ) ^ 3 * u ^ 4 / 24 := by
      calc ∑ j ∈ Finset.Icc 1 r, lam r * (j : ℝ) ^ 2 * u ^ 4 / 24
          ≤ ∑ _j ∈ Finset.Icc 1 r, lam r * (r : ℝ) ^ 2 * u ^ 4 / 24 := by
            refine Finset.sum_le_sum fun j hj => ?_
            have : (j : ℝ) ≤ r := by exact_mod_cast (Finset.mem_Icc.mp hj).2
            have : 0 ≤ lam r := by linarith
            gcongr
        _ = (r : ℝ) * (lam r * (r : ℝ) ^ 2 * u ^ 4 / 24) := by
            rw [Finset.sum_const, nsmul_eq_mul]; simp
        _ = lam r * (r : ℝ) ^ 3 * u ^ 4 / 24 := by ring
    have hsum_ge2 : invTildeLam r - (1 / 2 : ℝ) * lam r * u ^ 2 * dVal r (rStar r) -
        lam r * (r : ℝ) ^ 3 * u ^ 4 / 24 ≤
        ∑ j ∈ Finset.Icc 1 r, epsSign r j * dCoeff r j * Real.cos ((j : ℝ) * u) := by
      unfold invTildeLam
      linarith
    have hmul_ge := mul_le_mul_of_nonneg_left hsum_ge2 htl_pos.le
    have htl_inv : tildeLam r * invTildeLam r = 1 := inv_mul_cancel₀ hinv_ne
    have hmul_eq : tildeLam r * (invTildeLam r - (1 / 2 : ℝ) * lam r * u ^ 2 * dVal r (rStar r) -
        lam r * (r : ℝ) ^ 3 * u ^ 4 / 24) =
        1 - (1 / 2 : ℝ) * tildeLam r * lam r * dVal r (rStar r) * u ^ 2 -
        tildeLam r * lam r * (r : ℝ) ^ 3 * u ^ 4 / 24 := by
      rw [mul_sub, mul_sub, htl_inv]; ring
    have hu_le : |u| ≤ a / 200 := by
      have hpi4 : Real.pi < 4 := Real.pi_lt_four
      calc |u| = 2 * Real.pi * |t| := by
            simp only [u, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
        _ ≤ 2 * 4 * (a / 2000) := by
            have h1 : 2 * Real.pi ≤ 2 * 4 := by linarith
            exact mul_le_mul h1 ht (abs_nonneg t) (by norm_num)
        _ ≤ a / 200 := by linarith
    have hu2_le : u ^ 2 ≤ a ^ 2 / 40000 := by
      rw [← sq_abs u]
      calc |u| ^ 2 ≤ (a / 200) ^ 2 := pow_le_pow_left₀ (abs_nonneg u) hu_le 2
        _ = a ^ 2 / 40000 := by ring
    have hprod6 : tildeLam r * lam r ≤ 6 := by
      have := mul_le_mul htl.2.2 hlam.2.le (by linarith [hlam.1]) (by norm_num)
      linarith
    have hterm2 : (1 / 2 : ℝ) * tildeLam r * lam r * dVal r (rStar r) * u ^ 2 ≤ (1 / 22 : ℝ) * a ^ 2 := by
      have hprod : (1 / 2 : ℝ) * tildeLam r * lam r * dVal r (rStar r) ≤ 1803 := by
        have h2 : (1 / 2 : ℝ) * (tildeLam r * lam r) ≤ 3 := by linarith
        have h3 := mul_le_mul h2 hrs.2.2.2 (by linarith [hrs.2.2.1]) (by norm_num)
        linarith [show (1 / 2 : ℝ) * tildeLam r * lam r * dVal r (rStar r) =
          (1 / 2 : ℝ) * (tildeLam r * lam r) * dVal r (rStar r) by ring]
      have hmul_u := mul_le_mul_of_nonneg_right hprod (sq_nonneg u)
      have h1803 := mul_le_mul_of_nonneg_left hu2_le (by norm_num : (0 : ℝ) ≤ 1803)
      have ha2_nn : 0 ≤ a ^ 2 := sq_nonneg a
      have hfrac : 1803 * (a ^ 2 / 40000) ≤ (1 / 22 : ℝ) * a ^ 2 := by
        have : (1803 / 40000 : ℝ) ≤ 1 / 22 := by norm_num
        have := mul_le_mul_of_nonneg_right this ha2_nn
        linarith [show 1803 * (a ^ 2 / 40000) = (1803 / 40000 : ℝ) * a ^ 2 by ring]
      linarith
    have hterm4 : tildeLam r * lam r * (r : ℝ) ^ 3 * u ^ 4 / 24 ≤ (1 / 500 : ℝ) * a ^ 2 := by
      have hr2a : (r : ℝ) ^ 2 * a ≤ 1 := by
        have := (le_div_iff₀ (sq_pos_of_pos hrpos)).mp ha_r
        linarith
      have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
      have hra : (r : ℝ) * a ≤ 1 := by
        have : (r : ℝ) * a ≤ (r : ℝ) ^ 2 * a := by
          have : (r : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
          exact mul_le_mul_of_nonneg_right this ha0.le
        linarith
      have hr3a2 : (r : ℝ) ^ 3 * a ^ 2 ≤ 1 := by
        have : (r : ℝ) ^ 3 * a ^ 2 = ((r : ℝ) ^ 2 * a) * ((r : ℝ) * a) := by ring
        rw [this]
        exact mul_le_one₀ hr2a (by positivity) hra
      have hu4 : u ^ 4 ≤ a ^ 4 / 1000000 := by
        have hu2_weak : u ^ 2 ≤ a ^ 2 / 1000 := by
          have : a ^ 2 / 40000 ≤ a ^ 2 / 1000 := div_le_div_of_nonneg_left (sq_nonneg a) (by norm_num) (by norm_num)
          linarith
        have hsq := pow_le_pow_left₀ (sq_nonneg u) hu2_weak 2
        linarith [show (u ^ 2) ^ 2 = u ^ 4 by ring, show (a ^ 2 / 1000) ^ 2 = a ^ 4 / 1000000 by ring]
      have hr3u4 : (r : ℝ) ^ 3 * u ^ 4 ≤ a ^ 2 / 1000000 := by
        have h1 : (r : ℝ) ^ 3 * u ^ 4 ≤ (r : ℝ) ^ 3 * (a ^ 4 / 1000000) :=
          mul_le_mul_of_nonneg_left hu4 (by positivity)
        have h2 : (r : ℝ) ^ 3 * (a ^ 4 / 1000000) = ((r : ℝ) ^ 3 * a ^ 2) * (a ^ 2 / 1000000) := by ring
        rw [h2] at h1
        have h3 := mul_le_mul_of_nonneg_right hr3a2 (by positivity : (0 : ℝ) ≤ a ^ 2 / 1000000)
        linarith
      have hmul6 := mul_le_mul hprod6 hr3u4 (by positivity) (by norm_num)
      have ha2_nn : 0 ≤ a ^ 2 := sq_nonneg a
      have hfinal : 6 * (a ^ 2 / 1000000) / 24 ≤ (1 / 500 : ℝ) * a ^ 2 := by
        have : (6 / 24000000 : ℝ) ≤ 1 / 500 := by norm_num
        have := mul_le_mul_of_nonneg_right this ha2_nn
        linarith [show 6 * (a ^ 2 / 1000000) / 24 = (6 / 24000000 : ℝ) * a ^ 2 by ring]
      have hdiv24 : (tildeLam r * lam r * ((r : ℝ) ^ 3 * u ^ 4)) / 24 ≤ (6 * (a ^ 2 / 1000000)) / 24 :=
        div_le_div_of_nonneg_right hmul6 (by norm_num)
      linarith [show tildeLam r * lam r * (r : ℝ) ^ 3 * u ^ 4 / 24 =
        (tildeLam r * lam r * ((r : ℝ) ^ 3 * u ^ 4)) / 24 by ring]
    rw [hmul_eq] at hmul_ge
    linarith [show (1 / 22 : ℝ) * a ^ 2 + (1 / 500 : ℝ) * a ^ 2 ≤ (1 / 20 : ℝ) * a ^ 2 by
      have : (1 / 22 + 1 / 500 : ℝ) ≤ 1 / 20 := by norm_num
      nlinarith [sq_nonneg a]]
  have hz_re : 1 - (1 / 10 : ℝ) * a ^ 2 ≤ z.re := by
    unfold z hFunc
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have ha10_le : a ^ 10 ≤ (1 / 20 : ℝ) * a ^ 2 := by
      have ha_half : a ≤ 1 / 2 := by linarith
      have ha8 : a ^ 8 ≤ (1 / 2 : ℝ) ^ 8 := pow_le_pow_left₀ ha0.le ha_half 8
      have ha8' : a ^ 8 ≤ 1 / 20 := le_trans ha8 (by norm_num)
      have : a ^ 10 = a ^ 8 * a ^ 2 := by ring
      rw [this]; nlinarith [sq_nonneg a]
    have hre_nn : 0 ≤ (tildeH r (Complex.exp (2 * Real.pi * t * I))).re := by
      nlinarith [sq_nonneg a]
    nlinarith [pow_pos ha0 10]
  have hcos_hi : Real.cos a ≤ 1 - (1 / 3 : ℝ) * a ^ 2 := by
    have h1 := (abs_le.mp (abs_cos_sub_taylor2_le a)).2
    have ha4 : a ^ 4 / 24 ≤ (1 / 6 : ℝ) * a ^ 2 := by
      have : a ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := pow_le_pow_left₀ ha0.le ha_small 2
      nlinarith [sq_nonneg a]
    linarith
  have hcos_lo : (1 / 2 : ℝ) ≤ Real.cos a := by
    have h1 := (abs_le.mp (abs_cos_sub_taylor2_le a)).1
    have : a ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := pow_le_pow_left₀ ha0.le ha_small 2
    nlinarith [sq_nonneg a]
  have hre_gt : Real.cos a < z.re := by nlinarith [sq_pos_of_pos ha0]
  have hnorm_sq_ge : 1 - (1 / 5 : ℝ) * a ^ 2 ≤ ‖z‖ ^ 2 := by
    have hz_ge : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      nlinarith [sq_nonneg z.im]
    have hz_re_nn : 0 ≤ 1 - (1 / 10 : ℝ) * a ^ 2 := by nlinarith [sq_nonneg a]
    nlinarith [sq_nonneg a]
  refine ⟨hz_lt1, hre_gt, ?_⟩
  nlinarith [sq_nonneg a]

/- ### Section 5: Unified Product Bound and Maximum Modulus Lower Bound on `G_a` -/

private noncomputable def sparsePoly (N s : ℕ) (σ : Bool) (d : ℕ) (c : ℕ → ℝ) (z : ℂ) : ℂ :=
  (1 : ℂ) - (if σ then z ^ d else 0) + ∑ j ∈ Finset.Icc s N, (c j : ℂ) * z ^ j

private noncomputable def qPoly (N s : ℕ) (σ : Bool) (d : ℕ) (c : ℕ → ℝ) (a : ℝ) (z : ℂ) : ℂ :=
  (z - Complex.exp ((a : ℂ) * I)) * (z - Complex.exp (-(a : ℂ) * I)) * sparsePoly N s σ d c z

private lemma one_sub_pow_ge {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) {d : ℕ} (hd : 1 ≤ d) :
    min (1 / 2 : ℝ) ((d : ℝ) * x / 2) ≤ 1 - (1 - x) ^ d := by
  have h1 : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x); linarith
  have h2 : (1 - x) ^ d ≤ Real.exp (-((d : ℝ) * x)) := by
    calc (1 - x) ^ d ≤ (Real.exp (-x)) ^ d := pow_le_pow_left₀ (by linarith) h1 d
      _ = Real.exp ((d : ℝ) * (-x)) := (Real.exp_nat_mul (-x) d).symm
      _ = Real.exp (-((d : ℝ) * x)) := by ring_nf
  set y : ℝ := (d : ℝ) * x
  have hy0 : 0 < y := by positivity
  by_cases hy1 : y ≤ 1
  · have hexp : 1 + y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
    have hinv : Real.exp (-y) ≤ (1 + y)⁻¹ := by
      rw [Real.exp_neg]
      exact inv_anti₀ (by linarith) hexp
    have hfrac : y / 2 ≤ 1 - (1 + y)⁻¹ := by
      have hpos : (0 : ℝ) < 1 + y := by linarith
      have h1' : 1 - (1 + y)⁻¹ = y / (1 + y) := by field_simp [hpos.ne']; ring
      rw [h1']
      exact div_le_div_of_nonneg_left hy0.le hpos (by linarith)
    exact le_trans (min_le_right _ _) (by linarith)
  · push Not at hy1
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hexp_le : Real.exp (-y) ≤ 1 / 2 := by
      calc Real.exp (-y) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
        _ = (Real.exp 1)⁻¹ := Real.exp_neg 1
        _ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) he1
        _ = 1 / 2 := by norm_num
    exact le_trans (min_le_left _ _) (by linarith)

private lemma hFunc_zero (r : ℕ) (a : ℝ) : hFunc r a 0 = 0 := by
  simp [hFunc, tildeH_zero]

private lemma differentiable_tildeH (r : ℕ) : Differentiable ℂ (tildeH r) := by
  unfold tildeH
  exact (Differentiable.fun_sum fun j _ => (differentiable_id.pow j).const_mul _).const_mul _

private lemma differentiable_hFunc (r : ℕ) (a : ℝ) : Differentiable ℂ (hFunc r a) :=
  (differentiable_tildeH r).const_mul _

private lemma circleAverage_log_norm_comp_hFunc {r : ℕ} {a shift : ℝ} {F : ℂ → ℂ}
    (hFdiff : Differentiable ℂ F) (hF0 : ‖F 0‖ = 1)
    (hFne : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, F (hFunc r a w) ≠ 0) :
    ∫ t in (0 : ℝ)..1,
      Real.log ‖F (hFunc r a (Complex.exp (2 * Real.pi * (t + shift) * I)))‖ = 0 := by
  let rot : ℂ := Complex.exp (2 * Real.pi * (shift : ℂ) * I)
  have hrot_norm : ‖rot‖ = 1 := by
    have : rot = Complex.exp (((2 * Real.pi * shift : ℝ) : ℂ) * I) := by
      simp only [rot]; push_cast; ring_nf
    rw [this, Complex.norm_exp_ofReal_mul_I]
  let G : ℂ → ℂ := fun w => F (hFunc r a (rot * w))
  have hGdiff : Differentiable ℂ G :=
    hFdiff.comp ((differentiable_hFunc r a).comp (differentiable_id.const_mul rot))
  have hGan : AnalyticOnNhd ℂ G (Metric.closedBall (0 : ℂ) |(1 : ℝ)|) :=
    (analyticOnNhd_univ_iff_differentiable.mpr hGdiff).mono (Set.subset_univ _)
  have hGne : ∀ w ∈ Metric.closedBall (0 : ℂ) |(1 : ℝ)|, G w ≠ 0 := by
    intro w hw
    apply hFne (rot * w)
    simp only [Metric.mem_closedBall, dist_zero_right, abs_one] at hw ⊢
    rw [norm_mul, hrot_norm, one_mul]
    exact hw
  have hca := AnalyticOnNhd.circleAverage_log_norm_of_ne_zero hGan hGne
  have hG0 : Real.log ‖G 0‖ = 0 := by
    simp [G, hFunc_zero, hF0]
  rw [hG0, circleAverage_def, smul_eq_mul] at hca
  have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hint0 : ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.log ‖G (circleMap 0 1 θ)‖ = 0 := by
    have hmul := congrArg (fun x => (2 * Real.pi) * x) hca
    simp only [mul_zero] at hmul
    rwa [← mul_assoc, mul_inv_cancel₀ h2pi_ne, one_mul] at hmul
  have hcomp := intervalIntegral.integral_comp_mul_left
    (f := fun θ : ℝ => Real.log ‖G (circleMap 0 1 θ)‖) (a := (0 : ℝ)) (b := (1 : ℝ)) h2pi_ne
  simp only [mul_zero, mul_one, smul_eq_mul, hint0, mul_zero] at hcomp
  convert hcomp using 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [G, circleMap, zero_add, Complex.ofReal_one, one_mul, rot]
  congr 3
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma hasDerivAt_hFunc_circle {r : ℕ} (hr : 1 ≤ r) {a shift t : ℝ}
    (ha0 : 0 < a) (ha_half : a ≤ 1 / 2) (htl_pos : 0 < tildeLam r) (htl_le : tildeLam r ≤ 2) :
    ∃ h' : ℂ, HasDerivAt
      (fun s : ℝ => hFunc r a (Complex.exp (2 * Real.pi * ((s : ℂ) + (shift : ℂ)) * I))) h' t ∧
      ‖h'‖ ≤ 48 * Real.pi := by
  have ha10_lt : a ^ 10 < 1 := by
    have := pow_le_pow_left₀ ha0.le ha_half 10
    linarith [show (1 / 2 : ℝ) ^ 10 < 1 by norm_num]
  let c₀ : ℂ := ((1 - a ^ 10 : ℝ) : ℂ) * (tildeLam r : ℂ)
  let term : ℕ → ℝ → ℂ := fun j s =>
    ((epsSign r j * dCoeff r j : ℝ) : ℂ) *
      Complex.exp (((j : ℝ) * (2 * Real.pi * (s + shift)) : ℝ) * I)
  let term' : ℕ → ℂ := fun j =>
    ((epsSign r j * dCoeff r j : ℝ) : ℂ) *
      (Complex.exp (((j : ℝ) * (2 * Real.pi * (t + shift)) : ℝ) * I) *
        ((((j : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * I))
  have hfun_eq : (fun s : ℝ => hFunc r a (Complex.exp (2 * Real.pi * ((s : ℂ) + (shift : ℂ)) * I))) =
      fun s : ℝ => c₀ * ∑ j ∈ Finset.Icc 1 r, term j s := by
    funext s
    simp only [hFunc, tildeH, c₀, term, mul_assoc]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hderiv_term : ∀ j ∈ Finset.Icc 1 r, HasDerivAt (term j) (term' j) t := by
    intro j _
    have hlin : HasDerivAt (fun s : ℝ => (((j : ℝ) * (2 * Real.pi * (s + shift)) : ℝ) : ℂ) * I)
        ((((j : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * I) t := by
      have h1 : HasDerivAt (fun s : ℝ => (j : ℝ) * (2 * Real.pi * (s + shift)))
          ((j : ℝ) * (2 * Real.pi)) t := by
        have hadd : HasDerivAt (fun s : ℝ => s + shift) 1 t := (hasDerivAt_id t).add_const shift
        have hmul1 := hadd.const_mul (2 * Real.pi)
        have hmul2 := hmul1.const_mul (j : ℝ)
        simpa [mul_one] using hmul2
      exact (h1.ofReal_comp).mul_const I
    exact (hlin.cexp).const_mul _
  have hderiv_sum := HasDerivAt.fun_sum hderiv_term
  have hderiv_all := hderiv_sum.const_mul c₀
  refine ⟨c₀ * ∑ j ∈ Finset.Icc 1 r, term' j, ?_, ?_⟩
  · rw [hfun_eq]; exact hderiv_all
  · have hlam := lam_bounds hr
    have hc₀_le : ‖c₀‖ ≤ 2 := by
      simp only [c₀, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ 1 - a ^ 10),
        Real.norm_of_nonneg htl_pos.le]
      nlinarith [pow_pos ha0 10]
    have hsum_le : ‖∑ j ∈ Finset.Icc 1 r, term' j‖ ≤ 24 * Real.pi := by
      calc ‖∑ j ∈ Finset.Icc 1 r, term' j‖
          ≤ ∑ j ∈ Finset.Icc 1 r, ‖term' j‖ := norm_sum_le _ _
        _ = ∑ j ∈ Finset.Icc 1 r, dCoeff r j * ((j : ℝ) * (2 * Real.pi)) := by
            refine Finset.sum_congr rfl fun j hj => ?_
            simp only [term', norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I,
              Complex.norm_I, mul_one, one_mul]
            have heps : |epsSign r j| = 1 := by unfold epsSign; split_ifs <;> norm_num
            have hd_nn : 0 ≤ dCoeff r j := mul_nonneg (by linarith) (aCoeff_pos (Finset.mem_Icc.mp hj).1).le
            rw [Real.norm_eq_abs, heps, one_mul, Real.norm_of_nonneg hd_nn,
              Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by norm_num),
              Real.norm_of_nonneg Real.pi_pos.le]
        _ = 2 * Real.pi * lam r * ∑ j ∈ Finset.Icc 1 r, (j : ℝ) * aCoeff j := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => by unfold dCoeff; ring
        _ ≤ 2 * Real.pi * 3 * 4 := by
            have h4 := sum_j_aCoeff_le_four r
            have hsum_nn : 0 ≤ ∑ j ∈ Finset.Icc 1 r, (j : ℝ) * aCoeff j :=
              Finset.sum_nonneg fun j hj =>
                mul_nonneg (Nat.cast_nonneg _) (aCoeff_pos (Finset.mem_Icc.mp hj).1).le
            have h1 : 2 * Real.pi * lam r ≤ 2 * Real.pi * 3 :=
              mul_le_mul_of_nonneg_left hlam.2.le (by positivity)
            have h2 := mul_le_mul h1 h4 hsum_nn (by positivity)
            linarith
        _ = 24 * Real.pi := by ring
    rw [norm_mul]
    have hmul := mul_le_mul hc₀_le hsum_le (norm_nonneg _) (by norm_num)
    linarith

private lemma hasDerivAt_two_log_norm {φ : ℝ → ℂ} {φ' : ℂ} {t : ℝ}
    (hφ : HasDerivAt φ φ' t) (hne : φ t ≠ 0) :
    ∃ g' : ℝ, HasDerivAt (fun s : ℝ => 2 * Real.log ‖φ s‖) g' t ∧
      |g'| ≤ 2 * ‖φ'‖ / ‖φ t‖ := by
  have hre : HasDerivAt (fun s : ℝ => (φ s).re) φ'.re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hφ
  have him : HasDerivAt (fun s : ℝ => (φ s).im) φ'.im t :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hφ
  have hnsq : HasDerivAt (fun s : ℝ => Complex.normSq (φ s))
      (2 * (φ t).re * φ'.re + 2 * (φ t).im * φ'.im) t := by
    have h1 := (hre.pow 2).add (him.pow 2)
    refine (h1.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)).congr_deriv (by norm_num)
    simp [Complex.normSq_apply, sq]
  have hnsq_ne : Complex.normSq (φ t) ≠ 0 := (Complex.normSq_pos.mpr hne).ne'
  have hlog : HasDerivAt (fun s : ℝ => Real.log (Complex.normSq (φ s)))
      ((2 * (φ t).re * φ'.re + 2 * (φ t).im * φ'.im) / Complex.normSq (φ t)) t :=
    hnsq.log hnsq_ne
  have hfun_eq : (fun s : ℝ => 2 * Real.log ‖φ s‖) = fun s : ℝ => Real.log (Complex.normSq (φ s)) := by
    funext s
    rw [Complex.normSq_eq_norm_sq, Real.log_pow]
    push_cast
    ring
  refine ⟨(2 * (φ t).re * φ'.re + 2 * (φ t).im * φ'.im) / Complex.normSq (φ t), ?_, ?_⟩
  · rw [hfun_eq]; exact hlog
  · have hpos : 0 < ‖φ t‖ := norm_pos_iff.mpr hne
    rw [Complex.normSq_eq_norm_sq, abs_div, abs_of_pos (sq_pos_of_pos hpos)]
    have hcs : |2 * (φ t).re * φ'.re + 2 * (φ t).im * φ'.im| ≤ 2 * ‖φ t‖ * ‖φ'‖ := by
      have hsq : (2 * (φ t).re * φ'.re + 2 * (φ t).im * φ'.im) ^ 2 ≤ (2 * ‖φ t‖ * ‖φ'‖) ^ 2 := by
        have h1 : ‖φ t‖ ^ 2 = (φ t).re ^ 2 + (φ t).im ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
        have h2 : ‖φ'‖ ^ 2 = φ'.re ^ 2 + φ'.im ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
        have h3 : (2 * ‖φ t‖ * ‖φ'‖) ^ 2 = 4 * ‖φ t‖ ^ 2 * ‖φ'‖ ^ 2 := by ring
        rw [h3, h1, h2]
        nlinarith [sq_nonneg ((φ t).re * φ'.im - (φ t).im * φ'.re)]
      have hnn : 0 ≤ 2 * ‖φ t‖ * ‖φ'‖ := by positivity
      rw [← sq_abs] at hsq
      nlinarith [abs_nonneg (2 * (φ t).re * φ'.re + 2 * (φ t).im * φ'.im)]
    calc |2 * (φ t).re * φ'.re + 2 * (φ t).im * φ'.im| / ‖φ t‖ ^ 2
        ≤ (2 * ‖φ t‖ * ‖φ'‖) / ‖φ t‖ ^ 2 := div_le_div_of_nonneg_right hcs (sq_nonneg _)
      _ = 2 * ‖φ'‖ / ‖φ t‖ := by field_simp [hpos.ne']

private lemma riemann_sum_sub_integral_le {g : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    {m J₁ J₂ : ℕ} (hm : 1 ≤ m) (hJ₁₂ : J₁ ≤ J₂) (hJ₂m : J₂ ≤ m)
    (hderiv : ∀ t ∈ Set.Icc ((J₁ : ℝ) / m) ((J₂ : ℝ) / m), ∃ g', HasDerivAt g g' t ∧ |g'| ≤ L) :
    ∑ j ∈ Finset.Ico J₁ J₂, g ((j : ℝ) / m) ≤
      (m : ℝ) * (∫ t in ((J₁ : ℝ) / m)..((J₂ : ℝ) / m), g t) + L := by
  have hmpos : (0 : ℝ) < m := by positivity
  have hcont : ContinuousOn g (Set.Icc ((J₁ : ℝ) / m) ((J₂ : ℝ) / m)) := by
    intro t ht
    obtain ⟨g', hg', _⟩ := hderiv t ht
    exact hg'.continuousAt.continuousWithinAt
  let g' : ℝ → ℝ := fun z =>
    if h : z ∈ Set.Icc ((J₁ : ℝ) / m) ((J₂ : ℝ) / m) then (hderiv z h).choose else 0
  have hlip : ∀ x ∈ Set.Icc ((J₁ : ℝ) / m) ((J₂ : ℝ) / m),
      ∀ y ∈ Set.Icc ((J₁ : ℝ) / m) ((J₂ : ℝ) / m), |g x - g y| ≤ L * |x - y| := by
    intro x hx y hy
    rcases lt_trichotomy x y with hlt | rfl | hgt
    · have hsub : Set.Icc x y ⊆ Set.Icc ((J₁ : ℝ) / m) ((J₂ : ℝ) / m) :=
        fun z hz => ⟨le_trans hx.1 hz.1, le_trans hz.2 hy.2⟩
      obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g g' hlt
        (hcont.mono hsub)
        (fun z hz => by
          have hz' : z ∈ Set.Icc ((J₁ : ℝ) / m) ((J₂ : ℝ) / m) := hsub ⟨hz.1.le, hz.2.le⟩
          simpa only [g', dif_pos hz'] using (hderiv z hz').choose_spec.1)
      have hc' : c ∈ Set.Icc ((J₁ : ℝ) / m) ((J₂ : ℝ) / m) := hsub ⟨hc.1.le, hc.2.le⟩
      have hcb : |g' c| ≤ L := by
        simpa only [g', dif_pos hc'] using (hderiv c hc').choose_spec.2
      have hyx : 0 < y - x := sub_pos.mpr hlt
      have hdiff : g y - g x = g' c * (y - x) := by
        rw [hslope]; field_simp [hyx.ne']
      rw [abs_sub_comm x y, abs_sub_comm (g x) (g y), hdiff, abs_mul, abs_of_pos hyx]
      exact mul_le_mul_of_nonneg_right hcb hyx.le
    · simp
    · have hsub : Set.Icc y x ⊆ Set.Icc ((J₁ : ℝ) / m) ((J₂ : ℝ) / m) :=
        fun z hz => ⟨le_trans hy.1 hz.1, le_trans hz.2 hx.2⟩
      obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g g' hgt
        (hcont.mono hsub)
        (fun z hz => by
          have hz' : z ∈ Set.Icc ((J₁ : ℝ) / m) ((J₂ : ℝ) / m) := hsub ⟨hz.1.le, hz.2.le⟩
          simpa only [g', dif_pos hz'] using (hderiv z hz').choose_spec.1)
      have hc' : c ∈ Set.Icc ((J₁ : ℝ) / m) ((J₂ : ℝ) / m) := hsub ⟨hc.1.le, hc.2.le⟩
      have hcb : |g' c| ≤ L := by
        simpa only [g', dif_pos hc'] using (hderiv c hc').choose_spec.2
      have hxy : 0 < x - y := sub_pos.mpr hgt
      have hdiff : g x - g y = g' c * (x - y) := by
        rw [hslope]; field_simp [hxy.ne']
      rw [hdiff, abs_mul, abs_of_pos hxy]
      exact mul_le_mul_of_nonneg_right hcb hxy.le
  have hsum_int : ∀ k : ℕ, J₁ + k ≤ J₂ →
      ∫ t in ((J₁ : ℝ) / m)..(((J₁ + k : ℕ) : ℝ) / m), g t =
        ∑ j ∈ Finset.Ico J₁ (J₁ + k), ∫ t in ((j : ℝ) / m)..(((j + 1 : ℕ) : ℝ) / m), g t := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hle
      have h1 : Finset.Ico J₁ (J₁ + (k + 1)) = insert (J₁ + k) (Finset.Ico J₁ (J₁ + k)) := by
        ext j; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [h1, Finset.sum_insert (by simp), ← ih (by omega)]
      have hint1 : IntervalIntegrable g MeasureTheory.volume ((J₁ : ℝ) / m) (((J₁ + k : ℕ) : ℝ) / m) :=
        (hcont.mono fun z hz => ⟨hz.1, le_trans hz.2 (div_le_div_of_nonneg_right
          (by exact_mod_cast (show J₁ + k ≤ J₂ by omega)) hmpos.le)⟩).intervalIntegrable_of_Icc
          (div_le_div_of_nonneg_right (by exact_mod_cast (show J₁ ≤ J₁ + k by omega)) hmpos.le)
      have hint2 : IntervalIntegrable g MeasureTheory.volume (((J₁ + k : ℕ) : ℝ) / m)
          (((J₁ + (k + 1) : ℕ) : ℝ) / m) :=
        (hcont.mono fun z hz => ⟨le_trans (div_le_div_of_nonneg_right
          (by exact_mod_cast (show J₁ ≤ J₁ + k by omega)) hmpos.le) hz.1,
          le_trans hz.2 (div_le_div_of_nonneg_right (by exact_mod_cast hle) hmpos.le)⟩).intervalIntegrable_of_Icc
          (div_le_div_of_nonneg_right (by exact_mod_cast (show J₁ + k ≤ J₁ + (k + 1) by omega)) hmpos.le)
      have hcast : J₁ + (k + 1) = (J₁ + k) + 1 := by omega
      rw [hcast] at hint2 ⊢
      rw [add_comm (∫ t in (((J₁ + k : ℕ) : ℝ) / m)..((((J₁ + k) + 1 : ℕ) : ℝ) / m), g t)]
      exact (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm
  have hJ_int : ∫ t in ((J₁ : ℝ) / m)..((J₂ : ℝ) / m), g t =
      ∑ j ∈ Finset.Ico J₁ J₂, ∫ t in ((j : ℝ) / m)..(((j + 1 : ℕ) : ℝ) / m), g t := by
    have h2 := hsum_int (J₂ - J₁) (by omega)
    have hadd : J₁ + (J₂ - J₁) = J₂ := by omega
    simpa [hadd] using h2
  rw [hJ_int, Finset.mul_sum]
  have hdiff : ∑ j ∈ Finset.Ico J₁ J₂, (g ((j : ℝ) / m) -
      (m : ℝ) * ∫ t in ((j : ℝ) / m)..(((j + 1 : ℕ) : ℝ) / m), g t) ≤ L := by
    calc ∑ j ∈ Finset.Ico J₁ J₂, (g ((j : ℝ) / m) -
          (m : ℝ) * ∫ t in ((j : ℝ) / m)..(((j + 1 : ℕ) : ℝ) / m), g t)
        ≤ ∑ _j ∈ Finset.Ico J₁ J₂, L / (m : ℝ) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj1 : J₁ ≤ j := (Finset.mem_Ico.mp hj).1
          have hj2 : j < J₂ := (Finset.mem_Ico.mp hj).2
          have hstep : (j : ℝ) / m ≤ ((j + 1 : ℕ) : ℝ) / m :=
            div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ j) hmpos.le
          have hlen : ((j + 1 : ℕ) : ℝ) / m - (j : ℝ) / m = 1 / (m : ℝ) := by
            push_cast; field_simp [hmpos.ne']; ring
          have hconst : g ((j : ℝ) / m) =
              (m : ℝ) * ∫ _t in ((j : ℝ) / m)..(((j + 1 : ℕ) : ℝ) / m), g ((j : ℝ) / m) := by
            rw [intervalIntegral.integral_const, smul_eq_mul, hlen]; field_simp [hmpos.ne']
          rw [hconst, ← mul_sub]
          have hint_g : IntervalIntegrable g MeasureTheory.volume ((j : ℝ) / m) (((j + 1 : ℕ) : ℝ) / m) :=
            (hcont.mono fun z hz => ⟨le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hj1) hmpos.le) hz.1,
              le_trans hz.2 (div_le_div_of_nonneg_right (by exact_mod_cast (show j + 1 ≤ J₂ by omega)) hmpos.le)⟩).intervalIntegrable_of_Icc hstep
          rw [← intervalIntegral.integral_sub intervalIntegrable_const hint_g]
          have hmono : ∫ t in ((j : ℝ) / m)..(((j + 1 : ℕ) : ℝ) / m), (g ((j : ℝ) / m) - g t) ≤
              ∫ _t in ((j : ℝ) / m)..(((j + 1 : ℕ) : ℝ) / m), L / (m : ℝ) := by
            apply intervalIntegral.integral_mono_on hstep (intervalIntegrable_const.sub hint_g)
              intervalIntegrable_const
            intro t ht
            have hj_mem : (j : ℝ) / m ∈ Set.Icc ((J₁ : ℝ) / m) ((J₂ : ℝ) / m) :=
              ⟨div_le_div_of_nonneg_right (by exact_mod_cast hj1) hmpos.le,
               div_le_div_of_nonneg_right (by exact_mod_cast hj2.le) hmpos.le⟩
            have ht_mem : t ∈ Set.Icc ((J₁ : ℝ) / m) ((J₂ : ℝ) / m) :=
              ⟨le_trans hj_mem.1 ht.1,
               le_trans ht.2 (div_le_div_of_nonneg_right (by exact_mod_cast (show j + 1 ≤ J₂ by omega)) hmpos.le)⟩
            have h1 := (abs_le.mp (hlip ((j : ℝ) / m) hj_mem t ht_mem)).2
            have hdist : |(j : ℝ) / m - t| ≤ 1 / (m : ℝ) := by
              rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ht.1)]
              linarith [ht.2, hlen]
            calc g ((j : ℝ) / m) - g t ≤ L * |(j : ℝ) / m - t| := h1
              _ ≤ L * (1 / (m : ℝ)) := mul_le_mul_of_nonneg_left hdist hL
              _ = L / (m : ℝ) := by ring
          have hconst2 : ∫ _t in ((j : ℝ) / m)..(((j + 1 : ℕ) : ℝ) / m), L / (m : ℝ) = L / (m : ℝ) ^ 2 := by
            rw [intervalIntegral.integral_const, smul_eq_mul, hlen]; ring
          rw [hconst2] at hmono
          calc (m : ℝ) * ∫ t in ((j : ℝ) / m)..(((j + 1 : ℕ) : ℝ) / m), (g ((j : ℝ) / m) - g t)
              ≤ (m : ℝ) * (L / (m : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hmono hmpos.le
            _ = L / (m : ℝ) := by field_simp [hmpos.ne']
      _ = ((Finset.Ico J₁ J₂).card : ℝ) * (L / (m : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (m : ℝ) * (L / (m : ℝ)) := by
          have hc : ((Finset.Ico J₁ J₂).card : ℝ) ≤ m := by
            have : (Finset.Ico J₁ J₂).card ≤ m := by simp; omega
            exact_mod_cast this
          exact mul_le_mul_of_nonneg_right hc (by positivity)
      _ = L := by field_simp [hmpos.ne']
  rw [Finset.sum_sub_distrib] at hdiff
  linarith

private lemma log_pow_div_rpow_tendsto_zero (k : ℕ) {α : ℝ} (hα : 0 < α) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ k / (N : ℝ) ^ α) atTop (nhds 0) := by
  have h1 : Tendsto (fun x : ℝ => (Real.log x) ^ k / x ^ α) atTop (nhds 0) := by
    by_cases hk : k = 0
    · subst hk
      refine (tendsto_rpow_neg_atTop hα).congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      simp [Real.rpow_neg hx.le]
    · have h0 := (isLittleO_log_rpow_atTop (show 0 < α / (k + 1 : ℕ) by positivity)).tendsto_div_nhds_zero
      have hkp : (k : ℝ) * (α / (k + 1 : ℕ)) < α := by
        have hk1 : (0 : ℝ) < (k + 1 : ℕ) := by positivity
        rw [mul_div_assoc', div_lt_iff₀ hk1]
        have : (k : ℝ) < ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
        nlinarith
      have hpowk : Tendsto (fun x : ℝ => (Real.log x / x ^ (α / (k + 1 : ℕ))) ^ k) atTop (nhds 0) := by
        simpa [zero_pow hk] using h0.pow k
      refine squeeze_zero_norm' (a := fun x : ℝ => |(Real.log x / x ^ (α / (k + 1 : ℕ))) ^ k|) ?_ ?_
      · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
        have hx0 : 0 < x := by linarith
        have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg hx
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), div_pow,
          ← Real.rpow_natCast (x ^ (α / (k + 1 : ℕ))) k, ← Real.rpow_mul hx0.le]
        exact div_le_div_of_nonneg_left (pow_nonneg hlog_nn k) (Real.rpow_pos_of_pos hx0 _)
          (Real.rpow_le_rpow_of_exponent_le hx (by linarith))
      · simpa using hpowk.abs
  exact h1.comp tendsto_natCast_atTop_atTop

set_option maxHeartbeats 1600000 in
private lemma prod_factor_bound :
    ∀ᶠ N : ℕ in atTop,
      let a : ℝ := (N : ℝ) ^ (-(2 / 5 : ℝ))
      let r : ℕ := ⌊(N : ℝ) ^ (1 / 5 : ℝ)⌋₊
      let m : ℕ := ⌈2000 * (N : ℝ) ^ (2 / 5 : ℝ)⌉₊
      let J₁ : ℕ := ⌈32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (m : ℝ) * (Real.log N) ^ 4⌉₊
      let J₂ : ℕ := m - J₁ - 1
      1 ≤ r ∧ 1 ≤ J₁ ∧ J₁ ≤ J₂ ∧ J₂ < m ∧
      (∀ (δ : ℝ), 0 ≤ δ → δ < 1 →
        (∀ ζ : ℂ, ‖ζ‖ = 1 →
          ∏ j ∈ Finset.Ico J₁ J₂,
            ‖hFunc r a (Complex.exp (2 * Real.pi * (((j : ℝ) + δ) / (m : ℝ)) * I)) - ζ‖ ≤
            Real.exp (600000 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5)) ∧
        (∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ 2 * (N : ℝ) ^ (1 / 5 : ℝ) →
          ∏ j ∈ Finset.Ico J₁ J₂,
            ‖(1 : ℂ) - (hFunc r a (Complex.exp (2 * Real.pi * (((j : ℝ) + δ) / (m : ℝ)) * I))) ^ d‖ ≤
            Real.exp (600000 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5))) := by
  have hr_top : Tendsto (fun N : ℕ => ⌊(N : ℝ) ^ (1 / 5 : ℝ)⌋₊) atTop atTop := by
    have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 5 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp tendsto_natCast_atTop_atTop
    exact tendsto_nat_floor_atTop.comp h1
  have hlog_top : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog4_small := (log_pow_div_rpow_tendsto_zero 4 (by norm_num : (0 : ℝ) < 1 / 5)).eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 / 256 by norm_num))
  have hlog2_small := (log_pow_div_rpow_tendsto_zero 2 (by norm_num : (0 : ℝ) < 1 / 5)).eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  have hN15_top : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 5 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hr_top.eventually norm_tildeH_le_one_closedBall,
    hr_top.eventually norm_tildeH_large_t, hr_top.eventually tildeLam_bounds,
    hr_top.eventually (eventually_ge_atTop 100),
    hlog_top.eventually_ge_atTop 10, hN15_top.eventually_ge_atTop 100,
    hlog4_small, hlog2_small, eventually_ge_atTop 10000] with
      N hclosed hlarge htl hr100 hlog10 hN15 hlog4 hlog2 hN10000
  intro a r m J₁ J₂
  have hNpos : (0 : ℝ) < N := by positivity
  have hrpos : (0 : ℝ) < r := by positivity
  have ha0 : 0 < a := Real.rpow_pos_of_pos hNpos _
  have ha_le_half : a ≤ 1 / 2 := by
    have h1 : (N : ℝ) ^ (2 / 5 : ℝ) ≥ 2 := by
      have : (100 : ℝ) ^ (2 : ℕ) ≤ ((N : ℝ) ^ (1 / 5 : ℝ)) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) hN15 2
      rw [← Real.rpow_natCast ((N : ℝ) ^ (1 / 5 : ℝ)), ← Real.rpow_mul hNpos.le] at this
      norm_num at this; linarith
    have : a = ((N : ℝ) ^ (2 / 5 : ℝ))⁻¹ := Real.rpow_neg hNpos.le (2 / 5 : ℝ)
    rw [this]
    calc ((N : ℝ) ^ (2 / 5 : ℝ))⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h1
      _ = 1 / 2 := by norm_num
  have ha10_lt : a ^ 10 < 1 := by
    have := pow_le_pow_left₀ ha0.le ha_le_half 10
    linarith [show (1 / 2 : ℝ) ^ 10 < 1 by norm_num]
  have hN15_eq : (N : ℝ) ^ (1 / 5 : ℝ) * (N : ℝ) ^ (-(1 / 5 : ℝ)) = 1 := by
    rw [← Real.rpow_add hNpos]; norm_num
  have hN25_eq : (N : ℝ) ^ (2 / 5 : ℝ) * (N : ℝ) ^ (-(1 / 5 : ℝ)) = (N : ℝ) ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_add hNpos]; norm_num
  have hN25_ge : (10000 : ℝ) ≤ (N : ℝ) ^ (2 / 5 : ℝ) := by
    have := pow_le_pow_left₀ (by norm_num) hN15 2
    rw [← Real.rpow_natCast ((N : ℝ) ^ (1 / 5 : ℝ)), ← Real.rpow_mul hNpos.le] at this
    norm_num at this; linarith
  have hm_lo : 2000 * (N : ℝ) ^ (2 / 5 : ℝ) ≤ (m : ℝ) := Nat.le_ceil _
  have hm_hi : (m : ℝ) ≤ 2001 * (N : ℝ) ^ (2 / 5 : ℝ) := by
    have hlt := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2000 * (N : ℝ) ^ (2 / 5 : ℝ) by positivity)
    linarith
  have hm_pos : (0 : ℝ) < m := by linarith
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  have hJ₁_lo : 32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (m : ℝ) * (Real.log N) ^ 4 ≤ (J₁ : ℝ) := Nat.le_ceil _
  have hJ₁_div_lo : 32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (Real.log N) ^ 4 ≤ (J₁ : ℝ) / (m : ℝ) := by
    rw [le_div_iff₀ hm_pos]; linarith
  have hJ₁_div_hi : (J₁ : ℝ) / (m : ℝ) ≤ 1 / 4 := by
    have hlt := Nat.ceil_lt_add_one
      (show (0 : ℝ) ≤ 32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (m : ℝ) * (Real.log N) ^ 4 by positivity)
    have h1 : (N : ℝ) ^ (-(1 / 5 : ℝ)) * (Real.log N) ^ 4 < 1 / 256 := by
      have : (Real.log (N : ℝ)) ^ 4 / (N : ℝ) ^ (1 / 5 : ℝ) =
          (N : ℝ) ^ (-(1 / 5 : ℝ)) * (Real.log (N : ℝ)) ^ 4 := by
        rw [Real.rpow_neg hNpos.le, div_eq_mul_inv, mul_comm]
      linarith only [this, hlog4]
    have h2 : 32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (m : ℝ) * (Real.log N) ^ 4 < (m : ℝ) / 8 := by
      have : 32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (m : ℝ) * (Real.log N) ^ 4 =
          32 * ((N : ℝ) ^ (-(1 / 5 : ℝ)) * (Real.log N) ^ 4) * (m : ℝ) := by ring
      rw [this]; nlinarith
    rw [div_le_iff₀ hm_pos]
    linarith
  have hJ₁_ge1 : 1 ≤ J₁ := by
    have : (1 : ℝ) < (J₁ : ℝ) := by
      have h1 : (1 : ℝ) ≤ (Real.log (N : ℝ)) ^ 4 := by
        have := pow_le_pow_left₀ (by norm_num) (show (1 : ℝ) ≤ Real.log (N : ℝ) by linarith) 4
        simpa using this
      have h2 : 32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (2000 * (N : ℝ) ^ (2 / 5 : ℝ)) =
          64000 * (N : ℝ) ^ (1 / 5 : ℝ) := by
        calc 32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (2000 * (N : ℝ) ^ (2 / 5 : ℝ))
            = 64000 * ((N : ℝ) ^ (2 / 5 : ℝ) * (N : ℝ) ^ (-(1 / 5 : ℝ))) := by ring
          _ = 64000 * (N : ℝ) ^ (1 / 5 : ℝ) := by rw [hN25_eq]
      have h3 : 32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (m : ℝ) ≥ 64000 * (N : ℝ) ^ (1 / 5 : ℝ) := by
        have hnn : 0 ≤ 32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hm_lo hnn]
      nlinarith
    exact_mod_cast this.le
  have hJ₁_lt_half : 2 * J₁ + 2 ≤ m := by
    have h1 : (J₁ : ℝ) ≤ (m : ℝ) / 4 := by
      have := (div_le_iff₀ hm_pos).mp hJ₁_div_hi; linarith
    have : (2 * (J₁ : ℝ) + 2) ≤ (m : ℝ) := by linarith
    exact_mod_cast this
  have hJ₁_le_J₂ : J₁ ≤ J₂ := by simp only [J₂]; omega
  have hJ₂_lt_m : J₂ < m := by simp only [J₂]; omega
  have hr_le_N15 : (r : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ) := Nat.floor_le (by positivity)
  have hr_ge_half : (N : ℝ) ^ (1 / 5 : ℝ) / 2 ≤ (r : ℝ) := by
    have hlt := Nat.lt_floor_add_one ((N : ℝ) ^ (1 / 5 : ℝ))
    linarith
  have hlog_r_le : Real.log ((r : ℝ) + 3) ≤ Real.log (N : ℝ) := by
    apply Real.log_le_log (by positivity)
    have hN15_le_N : (N : ℝ) ^ (1 / 5 : ℝ) ≤ (N : ℝ) / 2 := by
      have h1 : (N : ℝ) ^ (1 / 5 : ℝ) * (N : ℝ) ^ (4 / 5 : ℝ) = (N : ℝ) := by
        rw [← Real.rpow_add hNpos]; norm_num
      have h45 : (2 : ℝ) ≤ (N : ℝ) ^ (4 / 5 : ℝ) := by
        have := pow_le_pow_left₀ (by norm_num) hN15 4
        rw [← Real.rpow_natCast ((N : ℝ) ^ (1 / 5 : ℝ)), ← Real.rpow_mul hNpos.le] at this
        norm_num at this; linarith
      nlinarith
    linarith [show (10000 : ℝ) ≤ N by exact_mod_cast hN10000]
  -- Define x₀ = 2 * N^(-1/5) * (log N)^2 and prove ‖h(t + δ/m)‖ ≤ 1 - x₀ on [J₁/m, J₂/m]
  set x₀ : ℝ := 2 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (Real.log N) ^ 2
  have hx₀_pos : 0 < x₀ := by positivity
  have hx₀_le_half : x₀ ≤ 1 / 2 := by
    have : (Real.log (N : ℝ)) ^ 2 / (N : ℝ) ^ (1 / 5 : ℝ) =
        (N : ℝ) ^ (-(1 / 5 : ℝ)) * (Real.log (N : ℝ)) ^ 2 := by
      rw [Real.rpow_neg hNpos.le, div_eq_mul_inv, mul_comm]
    linarith only [this, hlog2]
  have h3000_le : 3000 / (r : ℝ) ≤ (J₁ : ℝ) / (m : ℝ) := by
    have h1 : 3000 / (r : ℝ) ≤ 6000 * (N : ℝ) ^ (-(1 / 5 : ℝ)) := by
      rw [div_le_iff₀ hrpos]
      calc (3000 : ℝ) = 6000 * ((N : ℝ) ^ (-(1 / 5 : ℝ)) * ((N : ℝ) ^ (1 / 5 : ℝ) / 2)) := by
            rw [mul_div_assoc', mul_comm ((N : ℝ) ^ (-(1 / 5 : ℝ))), hN15_eq]; ring
        _ ≤ 6000 * ((N : ℝ) ^ (-(1 / 5 : ℝ)) * (r : ℝ)) := by
            gcongr
        _ = 6000 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (r : ℝ) := by ring
    have h2 : (6000 : ℝ) ≤ 32 * (Real.log (N : ℝ)) ^ 4 := by
      have : (10 : ℝ) ^ 4 ≤ (Real.log (N : ℝ)) ^ 4 := pow_le_pow_left₀ (by norm_num) hlog10 4
      linarith [show (10 : ℝ) ^ 4 = 10000 by norm_num]
    have h3 : 6000 * (N : ℝ) ^ (-(1 / 5 : ℝ)) ≤ 32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (Real.log N) ^ 4 := by
      have hnn : 0 ≤ (N : ℝ) ^ (-(1 / 5 : ℝ)) := by positivity
      nlinarith
    linarith
  have hx₀_le_gap : x₀ ≤ ((J₁ : ℝ) / (m : ℝ)) / (16 * (Real.log ((r : ℝ) + 3)) ^ 2) := by
    have hlog_r_pos : 0 < Real.log ((r : ℝ) + 3) := lt_trans zero_lt_one (log_add_three_gt_one r)
    rw [le_div_iff₀ (by positivity)]
    have hsq : (Real.log ((r : ℝ) + 3)) ^ 2 ≤ (Real.log (N : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hlog_r_pos.le hlog_r_le 2
    calc x₀ * (16 * (Real.log ((r : ℝ) + 3)) ^ 2)
        ≤ x₀ * (16 * (Real.log (N : ℝ)) ^ 2) := by gcongr
      _ = 32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (Real.log (N : ℝ)) ^ 4 := by simp only [x₀]; ring
      _ ≤ (J₁ : ℝ) / (m : ℝ) := hJ₁_div_lo
  have hJ₁_hi_bound : (J₁ : ℝ) + 1 ≤ 64050 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 4 := by
    have hlt := Nat.ceil_lt_add_one
      (show (0 : ℝ) ≤ 32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (m : ℝ) * (Real.log N) ^ 4 by positivity)
    have h1 : 32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (m : ℝ) ≤ 64032 * (N : ℝ) ^ (1 / 5 : ℝ) := by
      have hnn : 0 ≤ 32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) := by positivity
      calc 32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (m : ℝ)
          ≤ 32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (2001 * (N : ℝ) ^ (2 / 5 : ℝ)) :=
            mul_le_mul_of_nonneg_left hm_hi hnn
        _ = 64032 * ((N : ℝ) ^ (2 / 5 : ℝ) * (N : ℝ) ^ (-(1 / 5 : ℝ))) := by ring
        _ = 64032 * (N : ℝ) ^ (1 / 5 : ℝ) := by rw [hN25_eq]
    have h2 : 32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (m : ℝ) * (Real.log N) ^ 4 ≤
        64032 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 4 :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : (2 : ℝ) ≤ 18 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 4 := by
      have : (1 : ℝ) ≤ (Real.log (N : ℝ)) ^ 4 := by
        have := pow_le_pow_left₀ (by norm_num) (show (1 : ℝ) ≤ Real.log (N : ℝ) by linarith) 4
        simpa using this
      nlinarith
    linarith
  have hnorm_h_all : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, ‖hFunc r a w‖ ≤ 1 - a ^ 10 := by
    intro w hw
    unfold hFunc
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    exact mul_le_of_le_one_right (by linarith) (hclosed w hw)
  have hnorm_h_mid : ∀ (δ : ℝ), 0 ≤ δ → δ < 1 →
      ∀ t ∈ Set.Icc ((J₁ : ℝ) / m) ((J₂ : ℝ) / m),
        ‖hFunc r a (Complex.exp (2 * Real.pi * ((t : ℂ) + (δ : ℂ) / (m : ℂ)) * I))‖ ≤ 1 - x₀ := by
    intro δ hδ0 hδ1 t ht
    set u : ℝ := t + δ / (m : ℝ)
    have hu_lo : (J₁ : ℝ) / (m : ℝ) ≤ u := by
      have : 0 ≤ δ / (m : ℝ) := by positivity
      linarith [ht.1]
    have hu_hi : u ≤ 1 - (J₁ : ℝ) / (m : ℝ) := by
      have hJ₂_eq : (J₂ : ℝ) = (m : ℝ) - (J₁ : ℝ) - 1 := by
        have : J₂ + J₁ + 1 = m := by simp only [J₂]; omega
        have hcast : ((J₂ + J₁ + 1 : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast this
        push_cast at hcast; linarith
      have h1 : (J₂ : ℝ) / (m : ℝ) + 1 / (m : ℝ) = 1 - (J₁ : ℝ) / (m : ℝ) := by
        rw [hJ₂_eq]; field_simp [hm_pos.ne']; ring
      have h2 : δ / (m : ℝ) ≤ 1 / (m : ℝ) := div_le_div_of_nonneg_right hδ1.le hm_pos.le
      linarith [ht.2]
    set u' : ℝ := if u ≤ 1 / 2 then u else u - 1
    have hu'_exp : Complex.exp (2 * Real.pi * ((t : ℂ) + (δ : ℂ) / (m : ℂ)) * I) =
        Complex.exp (2 * Real.pi * (u' : ℂ) * I) := by
      have htu : ((t : ℂ) + (δ : ℂ) / (m : ℂ)) = (u : ℂ) := by simp only [u]; push_cast; ring
      rw [htu]
      by_cases hle : u ≤ 1 / 2
      · simp only [u', hle, ↓reduceIte]
      · simp only [u', hle, ↓reduceIte]
        rw [show 2 * Real.pi * (((u - 1 : ℝ) : ℂ)) * I =
          2 * Real.pi * (u : ℂ) * I - (2 * Real.pi * I) by push_cast; ring,
          Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
    have hu'_le : |u'| ≤ 1 / 2 := by
      by_cases hle : u ≤ 1 / 2
      · simp only [u', hle, ↓reduceIte]
        rw [abs_of_nonneg (le_trans (by positivity) hu_lo)]; exact hle
      · push Not at hle
        simp only [u', not_le.mpr hle, ↓reduceIte]
        rw [abs_of_nonpos (by linarith [show (0 : ℝ) ≤ (J₁ : ℝ) / (m : ℝ) by positivity])]
        linarith
    have hu'_ge : (J₁ : ℝ) / (m : ℝ) ≤ |u'| := by
      by_cases hle : u ≤ 1 / 2
      · simp only [u', hle, ↓reduceIte]
        rw [abs_of_nonneg (le_trans (by positivity) hu_lo)]; exact hu_lo
      · push Not at hle
        simp only [u', not_le.mpr hle, ↓reduceIte]
        rw [abs_of_nonpos (by linarith [show (0 : ℝ) ≤ (J₁ : ℝ) / (m : ℝ) by positivity])]
        linarith
    rw [hu'_exp]
    have htilde := hlarge u' hu'_le (le_trans h3000_le hu'_ge)
    have htilde_le : ‖tildeH r (Complex.exp (2 * Real.pi * (u' : ℂ) * I))‖ ≤ 1 - x₀ := by
      have hdiv : ((J₁ : ℝ) / (m : ℝ)) / (16 * (Real.log ((r : ℝ) + 3)) ^ 2) ≤
          |u'| / (16 * (Real.log ((r : ℝ) + 3)) ^ 2) :=
        div_le_div_of_nonneg_right hu'_ge (by positivity)
      linarith
    unfold hFunc
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    calc (1 - a ^ 10) * ‖tildeH r (Complex.exp (2 * Real.pi * (u' : ℂ) * I))‖
        ≤ 1 * ‖tildeH r (Complex.exp (2 * Real.pi * (u' : ℂ) * I))‖ := by
          have : 0 ≤ ‖tildeH r (Complex.exp (2 * Real.pi * (u' : ℂ) * I))‖ := norm_nonneg _
          nlinarith [pow_pos ha0 10]
      _ ≤ 1 - x₀ := by linarith
  -- Master helper for any polynomial factor F
  have hmaster : ∀ (δ : ℝ), 0 ≤ δ → δ < 1 → ∀ (F : ℂ → ℂ),
      Differentiable ℂ F → ‖F 0‖ = 1 →
      (∀ w ∈ Metric.closedBall (0 : ℂ) 1, a ^ 10 ≤ ‖F (hFunc r a w)‖) →
      (∀ t ∈ Set.Icc ((J₁ : ℝ) / m) ((J₂ : ℝ) / m),
        ∃ F', HasDerivAt (fun s : ℝ => F (hFunc r a (Complex.exp (2 * Real.pi * ((s : ℂ) + (δ : ℂ) / (m : ℂ)) * I)))) F' t ∧
          2 * ‖F'‖ / ‖F (hFunc r a (Complex.exp (2 * Real.pi * ((t : ℂ) + (δ : ℂ) / (m : ℂ)) * I)))‖ ≤
            384 * Real.pi * (N : ℝ) ^ (1 / 5 : ℝ)) →
      ∏ j ∈ Finset.Ico J₁ J₂,
        ‖F (hFunc r a (Complex.exp (2 * Real.pi * (((j : ℝ) + δ) / (m : ℝ)) * I)))‖ ≤
        Real.exp (600000 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5) := by
    intro δ hδ0 hδ1 F hFdiff hF0 hFlow hFderiv
    set shift : ℝ := δ / (m : ℝ)
    let φ : ℝ → ℂ := fun s => F (hFunc r a (Complex.exp (2 * Real.pi * ((s : ℂ) + (shift : ℂ)) * I)))
    let g : ℝ → ℝ := fun s => 2 * Real.log ‖φ s‖
    have hFne : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, F (hFunc r a w) ≠ 0 := by
      intro w hw
      have hpos : 0 < ‖F (hFunc r a w)‖ := lt_of_lt_of_le (pow_pos ha0 10) (hFlow w hw)
      exact norm_pos_iff.mp hpos
    have hφ_ne : ∀ s : ℝ, φ s ≠ 0 := by
      intro s
      apply hFne
      simp only [Metric.mem_closedBall, dist_zero_right]
      rw [show 2 * Real.pi * ((s : ℂ) + (shift : ℂ)) * I = (((2 * Real.pi * (s + shift) : ℝ) : ℂ)) * I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I]
    have hφ_low : ∀ s : ℝ, a ^ 10 ≤ ‖φ s‖ := by
      intro s
      apply hFlow
      simp only [Metric.mem_closedBall, dist_zero_right]
      rw [show 2 * Real.pi * ((s : ℂ) + (shift : ℂ)) * I = (((2 * Real.pi * (s + shift) : ℝ) : ℂ)) * I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I]
    have hg_cont : Continuous g := by
      have hφ_cont : Continuous φ :=
        hFdiff.continuous.comp ((differentiable_hFunc r a).continuous.comp
          (Complex.continuous_exp.comp (((continuous_const.mul (Complex.continuous_ofReal.add continuous_const)).mul continuous_const))))
      exact continuous_const.mul (hφ_cont.norm.log fun s => (norm_pos_iff.mpr (hφ_ne s)).ne')
    have hint_zero : ∫ t in (0 : ℝ)..1, g t = 0 := by
      have h0 := circleAverage_log_norm_comp_hFunc (r := r) (a := a) (shift := shift) hFdiff hF0 hFne
      have heq : (fun t : ℝ => g t) = fun t : ℝ =>
          2 * Real.log ‖F (hFunc r a (Complex.exp (2 * Real.pi * (t + shift) * I)))‖ := by
        funext t; simp only [g, φ]
      rw [heq, intervalIntegral.integral_const_mul, h0, mul_zero]
    have hg_low : ∀ s : ℝ, -(8 * Real.log (N : ℝ)) ≤ g s := by
      intro s
      have h1 : Real.log (a ^ 10) ≤ Real.log ‖φ s‖ :=
        Real.log_le_log (pow_pos ha0 10) (hφ_low s)
      have h2 : Real.log (a ^ 10) = -(4 * Real.log (N : ℝ)) := by
        rw [Real.log_pow, Real.log_rpow hNpos]; ring
      simp only [g]; linarith
    have hint_split : (∫ t in (0 : ℝ)..((J₁ : ℝ) / m), g t) +
        (∫ t in ((J₁ : ℝ) / m)..((J₂ : ℝ) / m), g t) +
        (∫ t in ((J₂ : ℝ) / m)..1, g t) = 0 := by
      have h1 := intervalIntegral.integral_add_adjacent_intervals
        (hg_cont.intervalIntegrable (μ := MeasureTheory.volume) 0 ((J₁ : ℝ) / m))
        (hg_cont.intervalIntegrable (μ := MeasureTheory.volume) ((J₁ : ℝ) / m) ((J₂ : ℝ) / m))
      have h2 := intervalIntegral.integral_add_adjacent_intervals
        (hg_cont.intervalIntegrable (μ := MeasureTheory.volume) 0 ((J₂ : ℝ) / m))
        (hg_cont.intervalIntegrable (μ := MeasureTheory.volume) ((J₂ : ℝ) / m) 1)
      rw [h1, h2, hint_zero]
    have hint_left : -(8 * Real.log (N : ℝ)) * ((J₁ : ℝ) / m) ≤ ∫ t in (0 : ℝ)..((J₁ : ℝ) / m), g t := by
      have hle : (0 : ℝ) ≤ (J₁ : ℝ) / m := by positivity
      calc -(8 * Real.log (N : ℝ)) * ((J₁ : ℝ) / m)
          = ∫ _t in (0 : ℝ)..((J₁ : ℝ) / m), -(8 * Real.log (N : ℝ)) := by
              rw [intervalIntegral.integral_const, smul_eq_mul]; ring
        _ ≤ ∫ t in (0 : ℝ)..((J₁ : ℝ) / m), g t :=
            intervalIntegral.integral_mono_on hle intervalIntegrable_const
              (hg_cont.intervalIntegrable _ _) (fun t _ => hg_low t)
    have hint_right : -(8 * Real.log (N : ℝ)) * (1 - (J₂ : ℝ) / m) ≤ ∫ t in ((J₂ : ℝ) / m)..1, g t := by
      have hle : (J₂ : ℝ) / m ≤ 1 := (div_le_one hm_pos).mpr (by exact_mod_cast hJ₂_lt_m.le)
      calc -(8 * Real.log (N : ℝ)) * (1 - (J₂ : ℝ) / m)
          = ∫ _t in ((J₂ : ℝ) / m)..1, -(8 * Real.log (N : ℝ)) := by
              rw [intervalIntegral.integral_const, smul_eq_mul]; ring
        _ ≤ ∫ t in ((J₂ : ℝ) / m)..1, g t :=
            intervalIntegral.integral_mono_on hle intervalIntegrable_const
              (hg_cont.intervalIntegrable _ _) (fun t _ => hg_low t)
    have h1_sub_J₂ : 1 - (J₂ : ℝ) / m = ((J₁ : ℝ) + 1) / m := by
      have : J₂ + J₁ + 1 = m := by simp only [J₂]; omega
      have hcast : ((J₂ + J₁ + 1 : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast this
      push_cast at hcast; field_simp [hm_pos.ne']; linarith
    have hint_mid_le : (m : ℝ) * (∫ t in ((J₁ : ℝ) / m)..((J₂ : ℝ) / m), g t) ≤
        16 * ((J₁ : ℝ) + 1) * Real.log (N : ℝ) := by
      have h1 : ∫ t in ((J₁ : ℝ) / m)..((J₂ : ℝ) / m), g t ≤
          8 * Real.log (N : ℝ) * ((J₁ : ℝ) / m + ((J₁ : ℝ) + 1) / m) := by
        rw [h1_sub_J₂] at hint_right; linarith only [hint_split, hint_left, hint_right]
      have h2 := mul_le_mul_of_nonneg_left h1 hm_pos.le
      have h3 : (m : ℝ) * (8 * Real.log (N : ℝ) * ((J₁ : ℝ) / m + ((J₁ : ℝ) + 1) / m)) =
          8 * Real.log (N : ℝ) * (2 * (J₁ : ℝ) + 1) := by
        field_simp [hm_pos.ne']; ring
      rw [h3] at h2
      have hlog_nn : 0 ≤ Real.log (N : ℝ) := by linarith only [hlog10]
      nlinarith only [h2, hlog_nn]
    have hriem := riemann_sum_sub_integral_le (g := g) (L := 384 * Real.pi * (N : ℝ) ^ (1 / 5 : ℝ))
      (by positivity) hm1 hJ₁_le_J₂ hJ₂_lt_m.le (fun t ht => by
        obtain ⟨F', hF', hbd⟩ := hFderiv t ht
        have hF'_eq : HasDerivAt φ F' t := by
          simpa only [φ, shift, Complex.ofReal_div, Complex.ofReal_natCast] using hF'
        obtain ⟨g', hg', hg'_bd⟩ := hasDerivAt_two_log_norm hF'_eq (hφ_ne t)
        refine ⟨g', hg', le_trans hg'_bd ?_⟩
        simpa only [φ, shift, Complex.ofReal_div, Complex.ofReal_natCast] using hbd)
    have hsum_log : ∑ j ∈ Finset.Ico J₁ J₂, Real.log ‖φ ((j : ℝ) / m)‖ ≤
        600000 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5 := by
      have hsum_2 : ∑ j ∈ Finset.Ico J₁ J₂, g ((j : ℝ) / m) =
          2 * ∑ j ∈ Finset.Ico J₁ J₂, Real.log ‖φ ((j : ℝ) / m)‖ := by
        simp only [g, Finset.mul_sum]
      have hbound_g : 2 * ∑ j ∈ Finset.Ico J₁ J₂, Real.log ‖φ ((j : ℝ) / m)‖ ≤
          16 * ((J₁ : ℝ) + 1) * Real.log (N : ℝ) + 384 * Real.pi * (N : ℝ) ^ (1 / 5 : ℝ) := by
        linarith only [hriem, hint_mid_le, hsum_2]
      have hterm1 : 8 * ((J₁ : ℝ) + 1) * Real.log (N : ℝ) ≤
          512400 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5 := by
        have hmul := mul_le_mul_of_nonneg_right hJ₁_hi_bound (show (0 : ℝ) ≤ 8 * Real.log (N : ℝ) by linarith only [hlog10])
        linarith only [hmul, show 8 * ((J₁ : ℝ) + 1) * Real.log (N : ℝ) = ((J₁ : ℝ) + 1) * (8 * Real.log (N : ℝ)) by ring,
          show 64050 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 4 * (8 * Real.log (N : ℝ)) =
            512400 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5 by ring]
      have hterm2 : 192 * Real.pi * (N : ℝ) ^ (1 / 5 : ℝ) ≤
          87600 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5 := by
        have hpi4 : Real.pi < 4 := Real.pi_lt_four
        have hlog5 : (1 : ℝ) ≤ (Real.log (N : ℝ)) ^ 5 := by
          have := pow_le_pow_left₀ (by norm_num) (show (1 : ℝ) ≤ Real.log (N : ℝ) by linarith only [hlog10]) 5
          simpa using this
        have h1 : 192 * Real.pi ≤ 87600 * (Real.log (N : ℝ)) ^ 5 := by nlinarith only [hpi4, hlog5]
        have h2 := mul_le_mul_of_nonneg_right h1 (show (0 : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ) by positivity)
        linarith only [h2, show 87600 * (Real.log (N : ℝ)) ^ 5 * (N : ℝ) ^ (1 / 5 : ℝ) =
          87600 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5 by ring]
      linarith only [hbound_g, hterm1, hterm2]
    have hprod_eq : ∏ j ∈ Finset.Ico J₁ J₂,
        ‖F (hFunc r a (Complex.exp (2 * Real.pi * (((j : ℝ) + δ) / (m : ℝ)) * I)))‖ =
        Real.exp (∑ j ∈ Finset.Ico J₁ J₂, Real.log ‖φ ((j : ℝ) / m)‖) := by
      rw [Real.exp_sum]
      refine Finset.prod_congr rfl fun j _ => ?_
      have heq : 2 * Real.pi * (((j : ℝ) + δ) / (m : ℝ)) * I =
          2 * Real.pi * ((((j : ℝ) / m : ℝ) : ℂ) + (shift : ℂ)) * I := by
        simp only [shift]; push_cast; ring
      rw [heq]
      exact (Real.exp_log (norm_pos_iff.mpr (hφ_ne ((j : ℝ) / m)))).symm
    rw [hprod_eq]
    exact Real.exp_le_exp.mpr hsum_log
  refine ⟨by omega, hJ₁_ge1, hJ₁_le_J₂, hJ₂_lt_m, fun δ hδ0 hδ1 => ⟨?_, ?_⟩⟩
  · -- Case 1: F(z) = z - ζ with ‖ζ‖ = 1
    intro ζ hζ
    refine hmaster δ hδ0 hδ1 (fun z => z - ζ) (differentiable_id.sub_const ζ)
      (by simp [hζ]) ?_ ?_
    · intro w hw
      have h1 := hnorm_h_all w hw
      have htri := norm_sub_norm_le ζ (hFunc r a w)
      rw [norm_sub_rev, hζ] at htri
      linarith
    · intro t ht
      obtain ⟨h', hh', hh'_bd⟩ := hasDerivAt_hFunc_circle (show 1 ≤ r by omega) ha0 ha_le_half
        (by linarith only [htl.2.1]) htl.2.2 (shift := δ / (m : ℝ)) (t := t)
      have hh'_eq : HasDerivAt
          (fun s : ℝ => hFunc r a (Complex.exp (2 * Real.pi * ((s : ℂ) + (δ : ℂ) / (m : ℂ)) * I)) - ζ)
          h' t := by
        simpa only [Complex.ofReal_div, Complex.ofReal_natCast] using hh'.sub_const ζ
      refine ⟨h', hh'_eq, ?_⟩
      have hhm := hnorm_h_mid δ hδ0 hδ1 t ht
      have hden : x₀ ≤ ‖hFunc r a (Complex.exp (2 * Real.pi * ((t : ℂ) + (δ : ℂ) / (m : ℂ)) * I)) - ζ‖ := by
        have htri := norm_sub_norm_le ζ (hFunc r a (Complex.exp (2 * Real.pi * ((t : ℂ) + (δ : ℂ) / (m : ℂ)) * I)))
        rw [norm_sub_rev, hζ] at htri
        linarith only [htri, hhm]
      calc 2 * ‖h'‖ / ‖hFunc r a (Complex.exp (2 * Real.pi * ((t : ℂ) + (δ : ℂ) / (m : ℂ)) * I)) - ζ‖
          ≤ 2 * (48 * Real.pi) / x₀ :=
            div_le_div₀ (by positivity) (by linarith only [hh'_bd]) hx₀_pos hden
        _ = 48 * Real.pi * (N : ℝ) ^ (1 / 5 : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
            simp only [x₀]
            have hinv : ((N : ℝ) ^ (-(1 / 5 : ℝ)))⁻¹ = (N : ℝ) ^ (1 / 5 : ℝ) := by
              rw [Real.rpow_neg hNpos.le, inv_inv]
            rw [div_eq_mul_inv, mul_inv, mul_inv, hinv]
            ring
        _ ≤ 384 * Real.pi * (N : ℝ) ^ (1 / 5 : ℝ) := by
            have hlog2_ge : (1 : ℝ) ≤ (Real.log (N : ℝ)) ^ 2 := by
              have := pow_le_pow_left₀ (by norm_num) (show (1 : ℝ) ≤ Real.log (N : ℝ) by linarith only [hlog10]) 2
              simpa using this
            have h1 : 48 * Real.pi * (N : ℝ) ^ (1 / 5 : ℝ) / (Real.log (N : ℝ)) ^ 2 ≤
                48 * Real.pi * (N : ℝ) ^ (1 / 5 : ℝ) :=
              div_le_self (by positivity) hlog2_ge
            have hnn : 0 ≤ Real.pi * (N : ℝ) ^ (1 / 5 : ℝ) := by positivity
            linarith only [h1, hnn]
  · -- Case 2: F(z) = 1 - z ^ d with 1 ≤ d ≤ 2 * N^(1/5)
    intro d hd1 hd_le
    refine hmaster δ hδ0 hδ1 (fun z => (1 : ℂ) - z ^ d)
      ((differentiable_const 1).sub (differentiable_id.pow d))
      (by simp [zero_pow (by omega : d ≠ 0)]) ?_ ?_
    · intro w hw
      have h1 := hnorm_h_all w hw
      have hpow : ‖hFunc r a w‖ ^ d ≤ 1 - a ^ 10 := by
        calc ‖hFunc r a w‖ ^ d ≤ (1 - a ^ 10) ^ d := pow_le_pow_left₀ (norm_nonneg _) h1 d
          _ ≤ (1 - a ^ 10) ^ 1 := pow_le_pow_of_le_one (by linarith only [ha10_lt]) (by linarith only [pow_pos ha0 10]) hd1
          _ = 1 - a ^ 10 := pow_one _
      have htri := norm_sub_norm_le (1 : ℂ) ((hFunc r a w) ^ d)
      rw [norm_one, norm_pow] at htri
      linarith only [htri, hpow]
    · intro t ht
      obtain ⟨h', hh', hh'_bd⟩ := hasDerivAt_hFunc_circle (show 1 ≤ r by omega) ha0 ha_le_half
        (by linarith only [htl.2.1]) htl.2.2 (shift := δ / (m : ℝ)) (t := t)
      have hh'_eq : HasDerivAt
          (fun s : ℝ => hFunc r a (Complex.exp (2 * Real.pi * ((s : ℂ) + (δ : ℂ) / (m : ℂ)) * I)))
          h' t := by
        simpa only [Complex.ofReal_div, Complex.ofReal_natCast] using hh'
      set hval : ℂ := hFunc r a (Complex.exp (2 * Real.pi * ((t : ℂ) + (δ : ℂ) / (m : ℂ)) * I))
      have hpow_d := hh'_eq.fun_pow d
      have hsub_d := (hasDerivAt_const t (1 : ℂ)).fun_sub hpow_d
      refine ⟨-(↑d * hval ^ (d - 1) * h'), by simpa [hval] using hsub_d, ?_⟩
      have hhm : ‖hval‖ ≤ 1 - x₀ := hnorm_h_mid δ hδ0 hδ1 t ht
      have hnum : ‖-(↑d * hval ^ (d - 1) * h')‖ ≤ 48 * Real.pi * (d : ℝ) := by
        rw [norm_neg, norm_mul, norm_mul, Complex.norm_natCast, norm_pow]
        have hp1 : ‖hval‖ ^ (d - 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) (by linarith only [hhm, hx₀_pos])
        calc (d : ℝ) * ‖hval‖ ^ (d - 1) * ‖h'‖
            ≤ (d : ℝ) * 1 * (48 * Real.pi) := by
              have h1 : (d : ℝ) * ‖hval‖ ^ (d - 1) ≤ (d : ℝ) * 1 :=
                mul_le_mul_of_nonneg_left hp1 (Nat.cast_nonneg _)
              exact mul_le_mul h1 hh'_bd (norm_nonneg _) (by positivity)
          _ = 48 * Real.pi * (d : ℝ) := by ring
      have hden : min (1 / 2 : ℝ) ((d : ℝ) * x₀ / 2) ≤ ‖(1 : ℂ) - hval ^ d‖ := by
        have htri := norm_sub_norm_le (1 : ℂ) (hval ^ d)
        rw [norm_one, norm_pow] at htri
        have hpow : ‖hval‖ ^ d ≤ (1 - x₀) ^ d := pow_le_pow_left₀ (norm_nonneg _) hhm d
        exact le_trans (one_sub_pow_ge hx₀_pos (by linarith only [hx₀_le_half]) hd1) (by linarith only [htri, hpow])
      rcases le_total (1 / 2 : ℝ) ((d : ℝ) * x₀ / 2) with hle | hle
      · rw [min_eq_left hle] at hden
        calc 2 * ‖-(↑d * hval ^ (d - 1) * h')‖ / ‖(1 : ℂ) - hval ^ d‖
            ≤ 2 * (48 * Real.pi * (d : ℝ)) / (1 / 2 : ℝ) :=
              div_le_div₀ (by positivity) (by linarith only [hnum]) (by norm_num) hden
          _ = 192 * Real.pi * (d : ℝ) := by ring
          _ ≤ 192 * Real.pi * (2 * (N : ℝ) ^ (1 / 5 : ℝ)) :=
              mul_le_mul_of_nonneg_left hd_le (by positivity)
          _ = 384 * Real.pi * (N : ℝ) ^ (1 / 5 : ℝ) := by ring
      · rw [min_eq_right hle] at hden
        have hd_pos : (0 : ℝ) < d := by positivity
        calc 2 * ‖-(↑d * hval ^ (d - 1) * h')‖ / ‖(1 : ℂ) - hval ^ d‖
            ≤ 2 * (48 * Real.pi * (d : ℝ)) / ((d : ℝ) * x₀ / 2) :=
              div_le_div₀ (by positivity) (by linarith only [hnum]) (by positivity) hden
          _ = 192 * Real.pi / x₀ := by field_simp [hd_pos.ne', hx₀_pos.ne']; ring
          _ = 96 * Real.pi * (N : ℝ) ^ (1 / 5 : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
              simp only [x₀]
              have hinv : ((N : ℝ) ^ (-(1 / 5 : ℝ)))⁻¹ = (N : ℝ) ^ (1 / 5 : ℝ) := by
                rw [Real.rpow_neg hNpos.le, inv_inv]
              rw [div_eq_mul_inv, mul_inv, mul_inv, hinv]
              ring
          _ ≤ 384 * Real.pi * (N : ℝ) ^ (1 / 5 : ℝ) := by
              have hlog2_ge : (1 : ℝ) ≤ (Real.log (N : ℝ)) ^ 2 := by
                have := pow_le_pow_left₀ (by norm_num) (show (1 : ℝ) ≤ Real.log (N : ℝ) by linarith only [hlog10]) 2
                simpa using this
              have h1 : 96 * Real.pi * (N : ℝ) ^ (1 / 5 : ℝ) / (Real.log (N : ℝ)) ^ 2 ≤
                  96 * Real.pi * (N : ℝ) ^ (1 / 5 : ℝ) :=
                div_le_self (by positivity) hlog2_ge
              have hnn : 0 ≤ Real.pi * (N : ℝ) ^ (1 / 5 : ℝ) := by positivity
              linarith only [h1, hnn]

set_option maxHeartbeats 1200000 in
/-- Proposition 5.6: Maximum modulus lower bound for `qPoly` on `inGa a`. -/
private lemma max_modulus_G_a_lower_bound :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (s : ℕ) (σ : Bool) (d : ℕ) (c : ℕ → ℝ) (M : ℝ),
        (N : ℝ) ^ (1 / 5 : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ 2 * (N : ℝ) ^ (1 / 5 : ℝ) →
        1 ≤ d → d < s → (∀ j, |c j| ≤ 1) →
        (∀ w : ℂ, inGa ((N : ℝ) ^ (-(2 / 5 : ℝ))) w →
          ‖qPoly N s σ d c ((N : ℝ) ^ (-(2 / 5 : ℝ))) w‖ ≤ M) →
        Real.exp (-C * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5) ≤ M := by
  refine ⟨2100000, by norm_num, ?_⟩
  have hr_top : Tendsto (fun N : ℕ => ⌊(N : ℝ) ^ (1 / 5 : ℝ)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp tendsto_natCast_atTop_atTop)
  have hlog_top : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hN15_top : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 5 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp tendsto_natCast_atTop_atTop
  have hlog2_small := (log_pow_div_rpow_tendsto_zero 2 (by norm_num : (0 : ℝ) < 1 / 5)).eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  filter_upwards [prod_factor_bound, hr_top.eventually hFunc_mem_inGa,
    hr_top.eventually norm_tildeH_le_one_closedBall,
    hr_top.eventually norm_tildeH_large_t,
    hlog_top.eventually_ge_atTop 10, hN15_top.eventually_ge_atTop 100,
    hlog2_small, eventually_ge_atTop 10000] with
      N hpf hinGa hclosed hlarge hlog10 hN15 hlog2 hN10000
  intro s σ d c M hs_lo hs_hi hd1 hds hc hM
  set a : ℝ := (N : ℝ) ^ (-(2 / 5 : ℝ))
  set r : ℕ := ⌊(N : ℝ) ^ (1 / 5 : ℝ)⌋₊
  set m : ℕ := ⌈2000 * (N : ℝ) ^ (2 / 5 : ℝ)⌉₊
  set J₁ : ℕ := ⌈32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (m : ℝ) * (Real.log N) ^ 4⌉₊
  set J₂ : ℕ := m - J₁ - 1
  rcases hpf with ⟨hr1, hJ₁1, hJ₁₂, hJ₂m, hprod_bd⟩
  have hNpos : (0 : ℝ) < N := by positivity
  have hrpos : (0 : ℝ) < r := by positivity
  have ha0 : 0 < a := Real.rpow_pos_of_pos hNpos _
  have hN25_ge : (10000 : ℝ) ≤ (N : ℝ) ^ (2 / 5 : ℝ) := by
    have := pow_le_pow_left₀ (by norm_num) hN15 2
    rw [← Real.rpow_natCast ((N : ℝ) ^ (1 / 5 : ℝ)), ← Real.rpow_mul hNpos.le] at this
    norm_num at this; linarith
  have ha_small : a ≤ 1 / 100 := by
    have : a = ((N : ℝ) ^ (2 / 5 : ℝ))⁻¹ := Real.rpow_neg hNpos.le (2 / 5 : ℝ)
    rw [this]
    calc ((N : ℝ) ^ (2 / 5 : ℝ))⁻¹ ≤ (10000 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hN25_ge
      _ ≤ 1 / 100 := by norm_num
  have ha_r : a ≤ 1 / (r : ℝ) ^ 2 := by
    have hr_le : (r : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ) := Nat.floor_le (by positivity)
    have hr2 : (r : ℝ) ^ 2 ≤ (N : ℝ) ^ (2 / 5 : ℝ) := by
      have := pow_le_pow_left₀ (Nat.cast_nonneg _) hr_le 2
      rw [← Real.rpow_natCast ((N : ℝ) ^ (1 / 5 : ℝ)), ← Real.rpow_mul hNpos.le] at this
      norm_num at this; exact this
    have : a = ((N : ℝ) ^ (2 / 5 : ℝ))⁻¹ := Real.rpow_neg hNpos.le (2 / 5 : ℝ)
    rw [this, one_div]
    exact inv_anti₀ (sq_pos_of_pos hrpos) hr2
  have hm_lo : 2000 * (N : ℝ) ^ (2 / 5 : ℝ) ≤ (m : ℝ) := Nat.le_ceil _
  have hm_hi : (m : ℝ) ≤ 2001 * (N : ℝ) ^ (2 / 5 : ℝ) := by
    have hlt := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2000 * (N : ℝ) ^ (2 / 5 : ℝ) by positivity)
    linarith
  have hm_pos : (0 : ℝ) < m := by linarith
  have hm_ge1 : 1 ≤ m := by omega
  have ha10_lt : a ^ 10 < 1 := by
    have := pow_le_pow_left₀ ha0.le (by linarith : a ≤ 1 / 2) 10
    linarith [show (1 / 2 : ℝ) ^ 10 < 1 by norm_num]
  -- Define g(z) = ∏_{j ∈ range m} qPoly (hFunc r a (exp (2π i j / m) * z))
  let gFun : ℂ → ℂ := fun z =>
    ∏ j ∈ Finset.range m, qPoly N s σ d c a (hFunc r a (Complex.exp (2 * Real.pi * (j : ℂ) / (m : ℂ) * I) * z))
  have hg0 : ‖gFun 0‖ = 1 := by
    have hq0 : qPoly N s σ d c a 0 = 1 := by
      have hs1 : 1 ≤ s := by omega
      have hsum0 : ∑ j ∈ Finset.Icc s N, (c j : ℂ) * (0 : ℂ) ^ j = 0 :=
        Finset.sum_eq_zero fun j hj => by
          have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
          simp [zero_pow hj0]
      have hp0 : sparsePoly N s σ d c 0 = 1 := by
        simp [sparsePoly, zero_pow (by omega : d ≠ 0), hsum0]
      simp only [qPoly, hp0, mul_one, zero_sub, neg_mul_neg]
      rw [← Complex.exp_add]
      simp
    simp [gFun, hFunc_zero, hq0]
  have hM_nn : 0 ≤ M := by
    have hmem := hinGa a ha0 ha_r ha_small 0 (by simp; positivity)
    exact le_trans (norm_nonneg _) (hM _ hmem)
  -- Bound ‖gFun z‖ on the unit circle ‖z‖ = 1
  have hfront : ∀ z ∈ frontier (Metric.ball (0 : ℂ) 1),
      ‖gFun z‖ ≤ M * Real.exp (2100000 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5) := by
    intro z hz
    rw [frontier_ball (0 : ℂ) one_ne_zero, Metric.mem_sphere, dist_zero_right] at hz
    set θ : ℝ := Int.fract (Complex.arg z / (2 * Real.pi))
    have hθ0 : 0 ≤ θ := Int.fract_nonneg _
    have hθ1 : θ < 1 := Int.fract_lt_one _
    have hz_eq : z = Complex.exp (2 * Real.pi * (θ : ℂ) * I) := by
      have h1 : z = Complex.exp ((Complex.arg z : ℂ) * I) := by
        simpa [hz] using (Complex.norm_mul_exp_arg_mul_I z).symm
      rw [h1]
      have hfr : (θ : ℝ) = Complex.arg z / (2 * Real.pi) - ⌊Complex.arg z / (2 * Real.pi)⌋ := rfl
      have harg : (Complex.arg z : ℂ) * I =
          2 * Real.pi * (θ : ℂ) * I + (⌊Complex.arg z / (2 * Real.pi)⌋ : ℂ) * (2 * Real.pi * I) := by
        have h2pi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (mul_ne_zero two_ne_zero Real.pi_ne_zero)
        rw [hfr]; push_cast; field_simp [h2pi]; ring
      rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    set k : ℕ := ⌊(m : ℝ) * θ⌋₊
    set δ : ℝ := (m : ℝ) * θ - (k : ℝ)
    have hδ0 : 0 ≤ δ := sub_nonneg.mpr (Nat.floor_le (by positivity))
    have hδ1 : δ < 1 := sub_lt_iff_lt_add'.mpr (Nat.lt_floor_add_one _)
    -- Reindex product by j ↦ (j + k) % m
    let f : ℕ → ℝ := fun j =>
      ‖qPoly N s σ d c a (hFunc r a (Complex.exp (2 * Real.pi * (((j : ℝ) + δ) / (m : ℝ)) * I)))‖
    have hprod_reindex : ‖gFun z‖ = ∏ j ∈ Finset.range m, f j := by
      simp only [gFun, norm_prod]
      have hterm : ∀ j ∈ Finset.range m,
          ‖qPoly N s σ d c a (hFunc r a (Complex.exp (2 * Real.pi * (j : ℂ) / (m : ℂ) * I) * z))‖ =
          f ((j + k) % m) := by
        intro j _
        simp only [f]
        congr 3
        rw [hz_eq, ← Complex.exp_add]
        have hdiv : j + k = m * ((j + k) / m) + (j + k) % m := (Nat.div_add_mod (j + k) m).symm
        have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
        have hθ_eq : (θ : ℂ) = ((k : ℂ) + (δ : ℂ)) / (m : ℂ) := by
          simp only [δ]; push_cast; field_simp [hmC]; ring
        have hexp_eq : 2 * Real.pi * (j : ℂ) / (m : ℂ) * I + 2 * Real.pi * (θ : ℂ) * I =
            2 * Real.pi * ((((j + k) % m : ℕ) : ℂ) + (δ : ℂ)) / (m : ℂ) * I +
              (((j + k) / m : ℕ) : ℂ) * (2 * Real.pi * I) := by
          rw [hθ_eq]
          have hcast : ((j + k : ℕ) : ℂ) = (m : ℂ) * (((j + k) / m : ℕ) : ℂ) + (((j + k) % m : ℕ) : ℂ) := by
            exact_mod_cast hdiv
          push_cast at hcast
          have hfrac : (j : ℂ) / (m : ℂ) + ((k : ℂ) + (δ : ℂ)) / (m : ℂ) =
              ((((j + k) % m : ℕ) : ℂ) + (δ : ℂ)) / (m : ℂ) + (((j + k) / m : ℕ) : ℂ) := by
            field_simp [hmC]
            linear_combination hcast
          linear_combination (2 * (Real.pi : ℂ) * I) * hfrac
        rw [hexp_eq, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
        congr 1; push_cast; ring
      rw [Finset.prod_congr rfl hterm]
      refine Finset.prod_bij (fun j _ => (j + k) % m)
        (fun j _ => Finset.mem_range.mpr (Nat.mod_lt _ (by omega))) ?_ ?_ (fun _ _ => rfl)
      · intro j₁ hj₁ j₂ hj₂ heq
        have hj₁' := Finset.mem_range.mp hj₁
        have hj₂' := Finset.mem_range.mp hj₂
        have h1 : (j₁ + k) % m = (j₂ + k) % m := heq
        have h2 : j₁ % m = j₂ % m := by
          have := Nat.ModEq.add_right_cancel' k h1
          exact this
        rwa [Nat.mod_eq_of_lt hj₁', Nat.mod_eq_of_lt hj₂'] at h2
      · intro b hb
        have hb' := Finset.mem_range.mp hb
        let j := (b + m - k % m) % m
        refine ⟨j, Finset.mem_range.mpr (Nat.mod_lt _ (by omega)), ?_⟩
        have hkm : k % m < m := Nat.mod_lt k (by omega)
        calc (j + k) % m = ((b + m - k % m) % m + k % m) % m := by
              rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          _ = (b + m - k % m + k % m) % m := by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          _ = (b + m) % m := by congr 1; omega
          _ = b := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hb']
    rw [hprod_reindex]
    -- Split range m into {0}, Ico 1 J₁, Ico J₁ J₂, Ico J₂ m
    have hsplit : Finset.range m =
        {0} ∪ (Finset.Ico 1 J₁ ∪ Finset.Ico J₁ J₂ ∪ Finset.Ico J₂ m) := by
      ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico]; omega
    have hd0 : Disjoint ({0} : Finset ℕ) (Finset.Ico 1 J₁ ∪ Finset.Ico J₁ J₂ ∪ Finset.Ico J₂ m) := by
      rw [Finset.disjoint_left]; intro j h1 h2
      simp only [Finset.mem_singleton, Finset.mem_union, Finset.mem_Ico] at h1 h2; omega
    have hd12 : Disjoint (Finset.Ico 1 J₁ ∪ Finset.Ico J₁ J₂) (Finset.Ico J₂ m) := by
      rw [Finset.disjoint_left]; intro j h1 h2
      simp only [Finset.mem_union, Finset.mem_Ico] at h1 h2; omega
    have hdis1 : Disjoint (Finset.Ico 1 J₁) (Finset.Ico J₁ J₂) := by
      rw [Finset.disjoint_left]; intro j h1 h2
      simp only [Finset.mem_Ico] at h1 h2; omega
    rw [hsplit, Finset.prod_union hd0, Finset.prod_union hd12, Finset.prod_union hdis1, Finset.prod_singleton]
    -- Part 1: f 0 ≤ M (since δ/m ≤ a/2000 → inGa a)
    have hf0 : f 0 ≤ M := by
      have hδm : |δ / (m : ℝ)| ≤ a / 2000 := by
        rw [abs_of_nonneg (by positivity)]
        have ha_inv : 2000 / a = 2000 * (N : ℝ) ^ (2 / 5 : ℝ) := by
          simp only [a, Real.rpow_neg hNpos.le, div_inv_eq_mul]
        have hm_ge : 2000 / a ≤ (m : ℝ) := by linarith
        calc δ / (m : ℝ) ≤ 1 / (m : ℝ) := div_le_div_of_nonneg_right hδ1.le hm_pos.le
          _ ≤ 1 / (2000 / a) := one_div_le_one_div_of_le (by positivity) hm_ge
          _ = a / 2000 := by field_simp
      have hmem := hinGa a ha0 ha_r ha_small (δ / (m : ℝ)) hδm
      have heq : 2 * Real.pi * ((((0 : ℕ) : ℝ) + δ) / (m : ℝ)) * I =
          2 * Real.pi * ((δ / (m : ℝ) : ℝ) : ℂ) * I := by push_cast; ring
      simpa only [f, heq] using hM _ hmem
    -- Part 2: Rough bound f j ≤ 8 * N for all j (used on Ico 1 J₁ and Ico J₂ m)
    have hf_rough : ∀ j, f j ≤ 8 * (N : ℝ) := by
      intro j
      set w : ℂ := hFunc r a (Complex.exp (2 * Real.pi * (((j : ℝ) + δ) / (m : ℝ)) * I))
      have hw1 : ‖w‖ ≤ 1 := by
        have h1 := hclosed (Complex.exp (2 * Real.pi * (((j : ℝ) + δ) / (m : ℝ)) * I)) (by
          simp only [Metric.mem_closedBall, dist_zero_right]
          rw [show 2 * Real.pi * (((j : ℝ) + δ) / (m : ℝ)) * I =
            (((2 * Real.pi * (((j : ℝ) + δ) / (m : ℝ)) : ℝ) : ℂ)) * I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I])
        unfold w hFunc
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        have : 1 - a ^ 10 ≤ 1 := by linarith [pow_pos ha0 10]
        exact mul_le_one₀ this (norm_nonneg _) h1
      have hp_bd : ‖sparsePoly N s σ d c w‖ ≤ 2 * (N : ℝ) := by
        unfold sparsePoly
        have h1 : ‖(1 : ℂ) - (if σ then w ^ d else 0)‖ ≤ 2 := by
          calc ‖(1 : ℂ) - (if σ then w ^ d else 0)‖
              ≤ ‖(1 : ℂ)‖ + ‖if σ then w ^ d else 0‖ := norm_sub_le _ _
            _ ≤ 1 + 1 := by
                rw [norm_one]; gcongr
                split_ifs
                · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hw1
                · simp
            _ = 2 := by ring
        have h2 : ‖∑ k ∈ Finset.Icc s N, (c k : ℂ) * w ^ k‖ ≤ (N : ℝ) := by
          calc ‖∑ k ∈ Finset.Icc s N, (c k : ℂ) * w ^ k‖
              ≤ ∑ k ∈ Finset.Icc s N, ‖(c k : ℂ) * w ^ k‖ := norm_sum_le _ _
            _ ≤ ∑ _k ∈ Finset.Icc s N, (1 : ℝ) := by
                refine Finset.sum_le_sum fun k _ => ?_
                rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
                exact mul_le_one₀ (hc k) (pow_nonneg (norm_nonneg _) _) (pow_le_one₀ (norm_nonneg _) hw1)
            _ = ((Finset.Icc s N).card : ℝ) := by simp
            _ ≤ (N : ℝ) := by
                have : (Finset.Icc s N).card ≤ N := by simp; omega
                exact_mod_cast this
        calc ‖(1 : ℂ) - (if σ then w ^ d else 0) + ∑ k ∈ Finset.Icc s N, (c k : ℂ) * w ^ k‖
            ≤ ‖(1 : ℂ) - (if σ then w ^ d else 0)‖ + ‖∑ k ∈ Finset.Icc s N, (c k : ℂ) * w ^ k‖ :=
              norm_add_le _ _
          _ ≤ 2 + (N : ℝ) := add_le_add h1 h2
          _ ≤ 2 * (N : ℝ) := by linarith [show (10000 : ℝ) ≤ N by exact_mod_cast hN10000]
      have hfac1 : ‖w - Complex.exp ((a : ℂ) * I)‖ ≤ 2 := by
        calc ‖w - Complex.exp ((a : ℂ) * I)‖ ≤ ‖w‖ + ‖Complex.exp ((a : ℂ) * I)‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := by rw [Complex.norm_exp_ofReal_mul_I]; linarith
          _ = 2 := by ring
      have hfac2 : ‖w - Complex.exp (-(a : ℂ) * I)‖ ≤ 2 := by
        calc ‖w - Complex.exp (-(a : ℂ) * I)‖ ≤ ‖w‖ + ‖Complex.exp (-(a : ℂ) * I)‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := by
              rw [show -(a : ℂ) * I = ((-a : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
              linarith
          _ = 2 := by ring
      simp only [f, qPoly, norm_mul]
      have h12 : ‖w - Complex.exp ((a : ℂ) * I)‖ * ‖w - Complex.exp (-(a : ℂ) * I)‖ ≤ 4 := by
        have := mul_le_mul hfac1 hfac2 (norm_nonneg _) (by norm_num)
        linarith
      have h123 := mul_le_mul h12 hp_bd (norm_nonneg _) (by norm_num)
      linarith
    have hprod_ends : (∏ j ∈ Finset.Ico 1 J₁, f j) * (∏ j ∈ Finset.Ico J₂ m, f j) ≤
        Real.exp (200000 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5) := by
      have h1 : ∏ j ∈ Finset.Ico 1 J₁, f j ≤ (8 * (N : ℝ)) ^ (J₁ - 1) := by
        calc ∏ j ∈ Finset.Ico 1 J₁, f j ≤ ∏ _j ∈ Finset.Ico 1 J₁, (8 * (N : ℝ)) :=
              Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => hf_rough j)
          _ = (8 * (N : ℝ)) ^ (J₁ - 1) := by simp
      have h2 : ∏ j ∈ Finset.Ico J₂ m, f j ≤ (8 * (N : ℝ)) ^ (J₁ + 1) := by
        calc ∏ j ∈ Finset.Ico J₂ m, f j ≤ ∏ _j ∈ Finset.Ico J₂ m, (8 * (N : ℝ)) :=
              Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => hf_rough j)
          _ = (8 * (N : ℝ)) ^ (m - J₂) := by simp
          _ = (8 * (N : ℝ)) ^ (J₁ + 1) := by congr 1; simp only [J₂]; omega
      have h12 : (∏ j ∈ Finset.Ico 1 J₁, f j) * (∏ j ∈ Finset.Ico J₂ m, f j) ≤
          (8 * (N : ℝ)) ^ (2 * J₁) := by
        have hmul := mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
        rw [← pow_add, show (J₁ - 1) + (J₁ + 1) = 2 * J₁ by omega] at hmul
        exact hmul
      have h8N_pos : 0 < 8 * (N : ℝ) := by positivity
      have hlog8N : Real.log (8 * (N : ℝ)) ≤ 3 / 2 * Real.log (N : ℝ) := by
        rw [Real.log_mul (by norm_num) hNpos.ne']
        have hlog8 : Real.log 8 ≤ 3 := by
          have h1 : (8 : ℝ) ≤ Real.exp 3 := by
            have := Real.exp_one_gt_d9
            have h3 : (2.718 : ℝ) ^ 3 ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
            rw [← Real.exp_nat_mul] at h3; norm_num at h3; linarith
          calc Real.log 8 ≤ Real.log (Real.exp 3) := Real.log_le_log (by norm_num) h1
            _ = 3 := Real.log_exp 3
        linarith
      have hJ₁_hi : (J₁ : ℝ) ≤ 64050 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 4 := by
        have hN25_eq : (N : ℝ) ^ (2 / 5 : ℝ) * (N : ℝ) ^ (-(1 / 5 : ℝ)) = (N : ℝ) ^ (1 / 5 : ℝ) := by
          rw [← Real.rpow_add hNpos]; norm_num
        have hlt := Nat.ceil_lt_add_one
          (show (0 : ℝ) ≤ 32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (m : ℝ) * (Real.log N) ^ 4 by positivity)
        have hm1 : 32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (m : ℝ) ≤ 64032 * (N : ℝ) ^ (1 / 5 : ℝ) := by
          have hnn : 0 ≤ 32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) := by positivity
          calc 32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (m : ℝ)
              ≤ 32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (2001 * (N : ℝ) ^ (2 / 5 : ℝ)) :=
                mul_le_mul_of_nonneg_left hm_hi hnn
            _ = 64032 * ((N : ℝ) ^ (2 / 5 : ℝ) * (N : ℝ) ^ (-(1 / 5 : ℝ))) := by ring
            _ = 64032 * (N : ℝ) ^ (1 / 5 : ℝ) := by rw [hN25_eq]
        have hlog4_ge : (1 : ℝ) ≤ (Real.log (N : ℝ)) ^ 4 := by
          have := pow_le_pow_left₀ (by norm_num) (show (1 : ℝ) ≤ Real.log (N : ℝ) by linarith) 4
          simpa using this
        have hmul := mul_le_mul_of_nonneg_right hm1 (by positivity : (0 : ℝ) ≤ (Real.log (N : ℝ)) ^ 4)
        nlinarith
      calc (∏ j ∈ Finset.Ico 1 J₁, f j) * (∏ j ∈ Finset.Ico J₂ m, f j)
          ≤ (8 * (N : ℝ)) ^ (2 * J₁) := h12
        _ = Real.exp ((2 * J₁ : ℕ) * Real.log (8 * (N : ℝ))) := by
            rw [Real.exp_nat_mul, Real.exp_log h8N_pos]
        _ ≤ Real.exp (200000 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5) := by
            apply Real.exp_le_exp.mpr
            push_cast
            have h1 : 2 * (J₁ : ℝ) * Real.log (8 * (N : ℝ)) ≤
                2 * (64050 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 4) * (3 / 2 * Real.log (N : ℝ)) := by
              have hA : 2 * (J₁ : ℝ) ≤ 2 * (64050 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 4) := by linarith
              have hlog_nn : 0 ≤ Real.log (8 * (N : ℝ)) :=
                Real.log_nonneg (by linarith [show (10000 : ℝ) ≤ N by exact_mod_cast hN10000])
              exact mul_le_mul hA hlog8N hlog_nn (by positivity)
            have hnn : 0 ≤ (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5 := by positivity
            linarith [show 2 * (64050 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 4) * (3 / 2 * Real.log (N : ℝ)) =
              192150 * ((N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5) by ring]
    -- Part 3: Middle product over Ico J₁ J₂ via prod_factor_bound + tail perturbation
    have hprod_mid : ∏ j ∈ Finset.Ico J₁ J₂, f j ≤
        Real.exp (1900000 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5) := by
      have hpf1 := (hprod_bd δ hδ0 hδ1).1 (Complex.exp ((a : ℂ) * I)) (Complex.norm_exp_ofReal_mul_I a)
      have hpf2 := (hprod_bd δ hδ0 hδ1).1 (Complex.exp (-(a : ℂ) * I)) (by
        rw [show -(a : ℂ) * I = ((-a : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I])
      -- Tail perturbation for sparsePoly on Ico J₁ J₂
      set x₀ : ℝ := 2 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (Real.log N) ^ 2
      have hx₀_pos : 0 < x₀ := by positivity
      have hN15_eq : (N : ℝ) ^ (1 / 5 : ℝ) * (N : ℝ) ^ (-(1 / 5 : ℝ)) = 1 := by
        rw [← Real.rpow_add hNpos]; norm_num
      have hr_le_N15 : (r : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ) := Nat.floor_le (by positivity)
      have hr_ge_half : (N : ℝ) ^ (1 / 5 : ℝ) / 2 ≤ (r : ℝ) := by
        have hlt := Nat.lt_floor_add_one ((N : ℝ) ^ (1 / 5 : ℝ)); linarith
      have hJ₁_div_lo : 32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (Real.log N) ^ 4 ≤ (J₁ : ℝ) / (m : ℝ) := by
        rw [le_div_iff₀ hm_pos]
        have hceil := Nat.le_ceil (32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (m : ℝ) * (Real.log N) ^ 4)
        linarith only [hceil, show 32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (Real.log N) ^ 4 * (m : ℝ) =
          32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (m : ℝ) * (Real.log N) ^ 4 by ring]
      have h3000_le : 3000 / (r : ℝ) ≤ (J₁ : ℝ) / (m : ℝ) := by
        have h1 : 3000 / (r : ℝ) ≤ 6000 * (N : ℝ) ^ (-(1 / 5 : ℝ)) := by
          rw [div_le_iff₀ hrpos]
          calc (3000 : ℝ) = 6000 * ((N : ℝ) ^ (-(1 / 5 : ℝ)) * ((N : ℝ) ^ (1 / 5 : ℝ) / 2)) := by
                rw [mul_div_assoc', mul_comm ((N : ℝ) ^ (-(1 / 5 : ℝ))), hN15_eq]; ring
            _ ≤ 6000 * ((N : ℝ) ^ (-(1 / 5 : ℝ)) * (r : ℝ)) := by gcongr
            _ = 6000 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (r : ℝ) := by ring
        have h2 : (6000 : ℝ) ≤ 32 * (Real.log (N : ℝ)) ^ 4 := by
          have : (10 : ℝ) ^ 4 ≤ (Real.log (N : ℝ)) ^ 4 := pow_le_pow_left₀ (by norm_num) hlog10 4
          linarith only [this, show (10 : ℝ) ^ 4 = 10000 by norm_num]
        have hnn : 0 ≤ (N : ℝ) ^ (-(1 / 5 : ℝ)) := by positivity
        nlinarith only [h1, h2, hnn, hJ₁_div_lo]
      have hlog_r_le : Real.log ((r : ℝ) + 3) ≤ Real.log (N : ℝ) := by
        apply Real.log_le_log (by positivity)
        have h1 : (N : ℝ) ^ (1 / 5 : ℝ) * (N : ℝ) ^ (4 / 5 : ℝ) = (N : ℝ) := by
          rw [← Real.rpow_add hNpos]; norm_num
        have h45 : (2 : ℝ) ≤ (N : ℝ) ^ (4 / 5 : ℝ) := by
          have := pow_le_pow_left₀ (by norm_num) hN15 4
          rw [← Real.rpow_natCast ((N : ℝ) ^ (1 / 5 : ℝ)), ← Real.rpow_mul hNpos.le] at this
          norm_num at this; linarith only [this]
        have hN15_half : (N : ℝ) ^ (1 / 5 : ℝ) ≤ (N : ℝ) / 2 := by
          nlinarith only [h1, h45, show (0 : ℝ) < (N : ℝ) ^ (1 / 5 : ℝ) by positivity]
        linarith only [hr_le_N15, hN15_half, show (10000 : ℝ) ≤ N by exact_mod_cast hN10000]
      have hx₀_le_gap : x₀ ≤ ((J₁ : ℝ) / (m : ℝ)) / (16 * (Real.log ((r : ℝ) + 3)) ^ 2) := by
        have hlog_r_pos : 0 < Real.log ((r : ℝ) + 3) := lt_trans zero_lt_one (log_add_three_gt_one r)
        rw [le_div_iff₀ (by positivity)]
        have hsq : (Real.log ((r : ℝ) + 3)) ^ 2 ≤ (Real.log (N : ℝ)) ^ 2 :=
          pow_le_pow_left₀ hlog_r_pos.le hlog_r_le 2
        calc x₀ * (16 * (Real.log ((r : ℝ) + 3)) ^ 2)
            ≤ x₀ * (16 * (Real.log (N : ℝ)) ^ 2) := by gcongr
          _ = 32 * (N : ℝ) ^ (-(1 / 5 : ℝ)) * (Real.log (N : ℝ)) ^ 4 := by simp only [x₀]; ring
          _ ≤ (J₁ : ℝ) / (m : ℝ) := hJ₁_div_lo
      have hsp_le : ∀ j ∈ Finset.Ico J₁ J₂,
          let w := hFunc r a (Complex.exp (2 * Real.pi * (((j : ℝ) + δ) / (m : ℝ)) * I))
          ‖sparsePoly N s σ d c w‖ ≤
            ‖(1 : ℂ) - (if σ then w ^ d else 0)‖ * (1 + (N : ℝ) ^ 2 * Real.exp (-(2 * (Real.log (N : ℝ)) ^ 2))) := by
        intro j hj w
        have hj1 := (Finset.mem_Ico.mp hj).1
        have hj2 := (Finset.mem_Ico.mp hj).2
        set u : ℝ := ((j : ℝ) + δ) / (m : ℝ)
        have hu_lo : (J₁ : ℝ) / (m : ℝ) ≤ u := by
          simp only [u]; exact div_le_div_of_nonneg_right (by linarith [show (J₁ : ℝ) ≤ j by exact_mod_cast hj1]) hm_pos.le
        have hu_hi : u ≤ 1 - (J₁ : ℝ) / (m : ℝ) := by
          have : J₂ + J₁ + 1 = m := by simp only [J₂]; omega
          have hcast : ((J₂ + J₁ + 1 : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast this
          have hj_le : (j : ℝ) + 1 ≤ (J₂ : ℝ) := by exact_mod_cast hj2
          push_cast at hcast
          simp only [u]
          rw [le_sub_iff_add_le, ← add_div]
          have hnum : (j : ℝ) + δ + (J₁ : ℝ) ≤ (m : ℝ) := by linarith only [hcast, hj_le, hδ1]
          exact (div_le_one hm_pos).mpr hnum
        set u' : ℝ := if u ≤ 1 / 2 then u else u - 1
        have hu'_exp : Complex.exp (2 * Real.pi * (((j : ℝ) + δ) / (m : ℝ)) * I) =
            Complex.exp (2 * Real.pi * (u' : ℂ) * I) := by
          have htu2 : 2 * Real.pi * (((j : ℝ) + δ) / (m : ℝ)) * I = 2 * Real.pi * (u : ℂ) * I := by
            simp only [u]; push_cast; ring
          rw [htu2]
          by_cases hle : u ≤ 1 / 2
          · simp only [u', hle, ↓reduceIte]
          · simp only [u', hle, ↓reduceIte]
            rw [show 2 * Real.pi * (((u - 1 : ℝ) : ℂ)) * I =
              2 * Real.pi * (u : ℂ) * I - (2 * Real.pi * I) by push_cast; ring,
              Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
        have hu'_le : |u'| ≤ 1 / 2 := by
          by_cases hle : u ≤ 1 / 2
          · simp only [u', hle, ↓reduceIte]; rw [abs_of_nonneg (le_trans (by positivity) hu_lo)]; exact hle
          · push Not at hle; simp only [u', not_le.mpr hle, ↓reduceIte]
            rw [abs_of_nonpos (by linarith only [hu_hi, show (0 : ℝ) ≤ (J₁ : ℝ) / (m : ℝ) by positivity])]; linarith only [hle]
        have hu'_ge : (J₁ : ℝ) / (m : ℝ) ≤ |u'| := by
          by_cases hle : u ≤ 1 / 2
          · simp only [u', hle, ↓reduceIte]; rw [abs_of_nonneg (le_trans (by positivity) hu_lo)]; exact hu_lo
          · push Not at hle; simp only [u', not_le.mpr hle, ↓reduceIte]
            rw [abs_of_nonpos (by linarith only [hu_hi, show (0 : ℝ) ≤ (J₁ : ℝ) / (m : ℝ) by positivity])]; linarith only [hu_hi]
        have hw_le : ‖w‖ ≤ 1 - x₀ := by
          have htilde := hlarge u' hu'_le (le_trans h3000_le hu'_ge)
          have hdiv : ((J₁ : ℝ) / (m : ℝ)) / (16 * (Real.log ((r : ℝ) + 3)) ^ 2) ≤
              |u'| / (16 * (Real.log ((r : ℝ) + 3)) ^ 2) :=
            div_le_div_of_nonneg_right hu'_ge (by positivity)
          have htilde_le : ‖tildeH r (Complex.exp (2 * Real.pi * (u' : ℂ) * I))‖ ≤ 1 - x₀ := by
            linarith only [htilde, hdiv, hx₀_le_gap]
          unfold w hFunc
          rw [hu'_exp, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith only [ha10_lt])]
          have h1a : 1 - a ^ 10 ≤ 1 := by linarith only [pow_pos ha0 10]
          have hnn := norm_nonneg (tildeH r (Complex.exp (2 * Real.pi * (u' : ℂ) * I)))
          nlinarith only [htilde_le, h1a, hnn]
        have hx₀_le_half : x₀ ≤ 1 / 2 := by
          have : (Real.log (N : ℝ)) ^ 2 / (N : ℝ) ^ (1 / 5 : ℝ) =
              (N : ℝ) ^ (-(1 / 5 : ℝ)) * (Real.log (N : ℝ)) ^ 2 := by
            rw [Real.rpow_neg hNpos.le, div_eq_mul_inv, mul_comm]
          linarith only [this, hlog2]
        have hws : ‖w‖ ^ s ≤ Real.exp (-(2 * (Real.log (N : ℝ)) ^ 2)) := by
          have h1 : 1 - x₀ ≤ Real.exp (-x₀) := by linarith [Real.add_one_le_exp (-x₀)]
          calc ‖w‖ ^ s ≤ (Real.exp (-x₀)) ^ s := pow_le_pow_left₀ (norm_nonneg _) (le_trans hw_le h1) s
            _ = Real.exp (-((s : ℝ) * x₀)) := by rw [← Real.exp_nat_mul]; congr 1; ring
            _ ≤ Real.exp (-(2 * (Real.log (N : ℝ)) ^ 2)) := by
                apply Real.exp_le_exp.mpr
                have h2 : 2 * (Real.log (N : ℝ)) ^ 2 ≤ (s : ℝ) * x₀ := by
                  calc 2 * (Real.log (N : ℝ)) ^ 2
                      = ((N : ℝ) ^ (1 / 5 : ℝ) * (N : ℝ) ^ (-(1 / 5 : ℝ))) * (2 * (Real.log (N : ℝ)) ^ 2) := by
                          rw [hN15_eq, one_mul]
                    _ = (N : ℝ) ^ (1 / 5 : ℝ) * x₀ := by simp only [x₀]; ring
                    _ ≤ (s : ℝ) * x₀ := mul_le_mul_of_nonneg_right hs_lo hx₀_pos.le
                linarith
        have htail_bd : ‖∑ k ∈ Finset.Icc s N, (c k : ℂ) * w ^ k‖ ≤
            (N : ℝ) * Real.exp (-(2 * (Real.log (N : ℝ)) ^ 2)) := by
          calc ‖∑ k ∈ Finset.Icc s N, (c k : ℂ) * w ^ k‖
              ≤ ∑ k ∈ Finset.Icc s N, ‖(c k : ℂ) * w ^ k‖ := norm_sum_le _ _
            _ ≤ ∑ _k ∈ Finset.Icc s N, Real.exp (-(2 * (Real.log (N : ℝ)) ^ 2)) := by
                refine Finset.sum_le_sum fun k hk => ?_
                rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
                have hwk : ‖w‖ ^ k ≤ ‖w‖ ^ s :=
                  pow_le_pow_of_le_one (norm_nonneg _) (by linarith) (Finset.mem_Icc.mp hk).1
                exact le_trans (mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) (hc k)) (le_trans hwk hws)
            _ = ((Finset.Icc s N).card : ℝ) * Real.exp (-(2 * (Real.log (N : ℝ)) ^ 2)) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (N : ℝ) * Real.exp (-(2 * (Real.log (N : ℝ)) ^ 2)) := by
                have hc_le : ((Finset.Icc s N).card : ℝ) ≤ (N : ℝ) := by
                  have : (Finset.Icc s N).card ≤ N := by simp; omega
                  exact_mod_cast this
                exact mul_le_mul_of_nonneg_right hc_le (Real.exp_pos _).le
        have hpt_lo : (N : ℝ)⁻¹ ≤ ‖(1 : ℂ) - (if σ then w ^ d else 0)‖ := by
          have hinv_le : (N : ℝ)⁻¹ ≤ x₀ := by
            have h1 : (N : ℝ)⁻¹ ≤ (N : ℝ) ^ (-(1 / 5 : ℝ)) := by
              rw [← Real.rpow_neg_one]
              exact Real.rpow_le_rpow_of_exponent_le (by linarith [show (10000 : ℝ) ≤ N by exact_mod_cast hN10000])
                (by norm_num)
            have hlog2_ge : (1 : ℝ) ≤ (Real.log (N : ℝ)) ^ 2 := by
              have := pow_le_pow_left₀ (by norm_num) (show (1 : ℝ) ≤ Real.log (N : ℝ) by linarith) 2
              simpa using this
            simp only [x₀]
            nlinarith [show 0 < (N : ℝ) ^ (-(1 / 5 : ℝ)) by positivity]
          cases σ
          · simp only [Bool.false_eq_true, ↓reduceIte, sub_zero, norm_one]
            linarith
          · simp only [↓reduceIte]
            have htri := norm_sub_norm_le (1 : ℂ) (w ^ d)
            rw [norm_one, norm_pow] at htri
            have hpow : ‖w‖ ^ d ≤ 1 - x₀ := by
              calc ‖w‖ ^ d ≤ (1 - x₀) ^ d := pow_le_pow_left₀ (norm_nonneg _) hw_le d
                _ ≤ (1 - x₀) ^ 1 := pow_le_pow_of_le_one (by linarith) (by linarith) hd1
                _ = 1 - x₀ := pow_one _
            linarith
        have hpt_N : (N : ℝ) ≤ (N : ℝ) ^ 2 * ‖(1 : ℂ) - (if σ then w ^ d else 0)‖ := by
          have hmul := mul_le_mul_of_nonneg_left hpt_lo (show (0 : ℝ) ≤ (N : ℝ) ^ 2 by positivity)
          have : (N : ℝ) ^ 2 * (N : ℝ)⁻¹ = (N : ℝ) := by field_simp [hNpos.ne']
          linarith
        unfold sparsePoly
        calc ‖(1 : ℂ) - (if σ then w ^ d else 0) + ∑ k ∈ Finset.Icc s N, (c k : ℂ) * w ^ k‖
            ≤ ‖(1 : ℂ) - (if σ then w ^ d else 0)‖ + ‖∑ k ∈ Finset.Icc s N, (c k : ℂ) * w ^ k‖ :=
              norm_add_le _ _
          _ ≤ ‖(1 : ℂ) - (if σ then w ^ d else 0)‖ +
              (N : ℝ) * Real.exp (-(2 * (Real.log (N : ℝ)) ^ 2)) := by linarith
          _ ≤ ‖(1 : ℂ) - (if σ then w ^ d else 0)‖ +
              ((N : ℝ) ^ 2 * ‖(1 : ℂ) - (if σ then w ^ d else 0)‖) *
                Real.exp (-(2 * (Real.log (N : ℝ)) ^ 2)) := by
              have hmul := mul_le_mul_of_nonneg_right hpt_N
                (Real.exp_pos (-(2 * (Real.log (N : ℝ)) ^ 2))).le
              linarith only [hmul]
          _ = ‖(1 : ℂ) - (if σ then w ^ d else 0)‖ *
              (1 + (N : ℝ) ^ 2 * Real.exp (-(2 * (Real.log (N : ℝ)) ^ 2))) := by ring
      have hpf3 : ∏ j ∈ Finset.Ico J₁ J₂,
          ‖(1 : ℂ) - (if σ then (hFunc r a (Complex.exp (2 * Real.pi * (((j : ℝ) + δ) / (m : ℝ)) * I))) ^ d else 0)‖ ≤
          Real.exp (600000 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5) := by
        cases σ
        · simp only [Bool.false_eq_true, ↓reduceIte, sub_zero, norm_one, Finset.prod_const_one]
          exact Real.one_le_exp (by positivity)
        · simp only [↓reduceIte]
          have hd_le : (d : ℝ) ≤ 2 * (N : ℝ) ^ (1 / 5 : ℝ) := le_trans (by exact_mod_cast hds.le) hs_hi
          exact (hprod_bd δ hδ0 hδ1).2 d hd1 hd_le
      have herr_prod : (1 + (N : ℝ) ^ 2 * Real.exp (-(2 * (Real.log (N : ℝ)) ^ 2))) ^ (Finset.Ico J₁ J₂).card ≤
          Real.exp 1 := by
        have h1 : 1 + (N : ℝ) ^ 2 * Real.exp (-(2 * (Real.log (N : ℝ)) ^ 2)) ≤
            Real.exp ((N : ℝ) ^ 2 * Real.exp (-(2 * (Real.log (N : ℝ)) ^ 2))) := by
          linarith [Real.add_one_le_exp ((N : ℝ) ^ 2 * Real.exp (-(2 * (Real.log (N : ℝ)) ^ 2)))]
        have hcard_le : ((Finset.Ico J₁ J₂).card : ℝ) ≤ (N : ℝ) := by
          have hc1 : ((Finset.Ico J₁ J₂).card : ℝ) ≤ (m : ℝ) := by
            have : (Finset.Ico J₁ J₂).card ≤ m := by simp; omega
            exact_mod_cast this
          have hm_le_N : (m : ℝ) ≤ (N : ℝ) := by
            have h1' : (N : ℝ) ^ (2 / 5 : ℝ) * (N : ℝ) ^ (3 / 5 : ℝ) = (N : ℝ) := by
              rw [← Real.rpow_add hNpos]; norm_num
            have h35 : (2001 : ℝ) ≤ (N : ℝ) ^ (3 / 5 : ℝ) := by
              have := pow_le_pow_left₀ (by norm_num) hN15 3
              rw [← Real.rpow_natCast ((N : ℝ) ^ (1 / 5 : ℝ)), ← Real.rpow_mul hNpos.le] at this
              norm_num at this; linarith only [this]
            nlinarith only [hm_hi, h1', h35, show (0 : ℝ) < (N : ℝ) ^ (2 / 5 : ℝ) by positivity]
          linarith only [hc1, hm_le_N]
        calc (1 + (N : ℝ) ^ 2 * Real.exp (-(2 * (Real.log (N : ℝ)) ^ 2))) ^ (Finset.Ico J₁ J₂).card
            ≤ (Real.exp ((N : ℝ) ^ 2 * Real.exp (-(2 * (Real.log (N : ℝ)) ^ 2)))) ^ (Finset.Ico J₁ J₂).card :=
              pow_le_pow_left₀ (by positivity) h1 _
          _ = Real.exp (((Finset.Ico J₁ J₂).card : ℝ) * ((N : ℝ) ^ 2 * Real.exp (-(2 * (Real.log (N : ℝ)) ^ 2)))) := by
              rw [← Real.exp_nat_mul]
          _ ≤ Real.exp 1 := by
              apply Real.exp_le_exp.mpr
              calc ((Finset.Ico J₁ J₂).card : ℝ) * ((N : ℝ) ^ 2 * Real.exp (-(2 * (Real.log (N : ℝ)) ^ 2)))
                  ≤ (N : ℝ) * ((N : ℝ) ^ 2 * Real.exp (-(2 * (Real.log (N : ℝ)) ^ 2))) := by
                    gcongr
                _ = Real.exp (3 * Real.log (N : ℝ) - 2 * (Real.log (N : ℝ)) ^ 2) := by
                    have hN3 : (N : ℝ) * (N : ℝ) ^ 2 = Real.exp (3 * Real.log (N : ℝ)) := by
                      have : (N : ℝ) * (N : ℝ) ^ 2 = (N : ℝ) ^ (3 : ℕ) := by ring
                      rw [this, show (3 : ℝ) * Real.log (N : ℝ) = ((3 : ℕ) : ℝ) * Real.log (N : ℝ) by norm_num,
                        Real.exp_nat_mul, Real.exp_log hNpos]
                    rw [← mul_assoc, hN3, ← Real.exp_add, sub_eq_add_neg]
                _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith only [hlog10])
                _ = 1 := Real.exp_zero
      have hmid_rew : ∏ j ∈ Finset.Ico J₁ J₂, f j =
          (∏ j ∈ Finset.Ico J₁ J₂,
            ‖hFunc r a (Complex.exp (2 * Real.pi * (((j : ℝ) + δ) / (m : ℝ)) * I)) - Complex.exp ((a : ℂ) * I)‖) *
          (∏ j ∈ Finset.Ico J₁ J₂,
            ‖hFunc r a (Complex.exp (2 * Real.pi * (((j : ℝ) + δ) / (m : ℝ)) * I)) - Complex.exp (-(a : ℂ) * I)‖) *
          (∏ j ∈ Finset.Ico J₁ J₂,
            ‖sparsePoly N s σ d c (hFunc r a (Complex.exp (2 * Real.pi * (((j : ℝ) + δ) / (m : ℝ)) * I)))‖) := by
        simp only [f, qPoly, norm_mul, Finset.prod_mul_distrib]
      rw [hmid_rew]
      have hsp_prod : ∏ j ∈ Finset.Ico J₁ J₂,
          ‖sparsePoly N s σ d c (hFunc r a (Complex.exp (2 * Real.pi * (((j : ℝ) + δ) / (m : ℝ)) * I)))‖ ≤
          Real.exp (600000 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5) * Real.exp 1 := by
        calc ∏ j ∈ Finset.Ico J₁ J₂,
              ‖sparsePoly N s σ d c (hFunc r a (Complex.exp (2 * Real.pi * (((j : ℝ) + δ) / (m : ℝ)) * I)))‖
            ≤ ∏ j ∈ Finset.Ico J₁ J₂,
              (‖(1 : ℂ) - (if σ then (hFunc r a (Complex.exp (2 * Real.pi * (((j : ℝ) + δ) / (m : ℝ)) * I))) ^ d else 0)‖ *
                (1 + (N : ℝ) ^ 2 * Real.exp (-(2 * (Real.log (N : ℝ)) ^ 2)))) :=
              Finset.prod_le_prod (fun _ _ => norm_nonneg _) hsp_le
          _ = (∏ j ∈ Finset.Ico J₁ J₂,
                ‖(1 : ℂ) - (if σ then (hFunc r a (Complex.exp (2 * Real.pi * (((j : ℝ) + δ) / (m : ℝ)) * I))) ^ d else 0)‖) *
              (1 + (N : ℝ) ^ 2 * Real.exp (-(2 * (Real.log (N : ℝ)) ^ 2))) ^ (Finset.Ico J₁ J₂).card := by
              rw [Finset.prod_mul_distrib, Finset.prod_const]
          _ ≤ Real.exp (600000 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5) * Real.exp 1 :=
              mul_le_mul hpf3 herr_prod (by positivity) (Real.exp_pos _).le
      have h12 : (∏ j ∈ Finset.Ico J₁ J₂,
            ‖hFunc r a (Complex.exp (2 * Real.pi * (((j : ℝ) + δ) / (m : ℝ)) * I)) - Complex.exp ((a : ℂ) * I)‖) *
          (∏ j ∈ Finset.Ico J₁ J₂,
            ‖hFunc r a (Complex.exp (2 * Real.pi * (((j : ℝ) + δ) / (m : ℝ)) * I)) - Complex.exp (-(a : ℂ) * I)‖) ≤
          Real.exp (600000 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5) *
            Real.exp (600000 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5) :=
        mul_le_mul hpf1 hpf2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Real.exp_pos _).le
      have h123 := mul_le_mul h12 hsp_prod (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
      refine le_trans h123 ?_
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1_le : (1 : ℝ) ≤ 100000 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5 := by
        have hlog5 : (1 : ℝ) ≤ (Real.log (N : ℝ)) ^ 5 := by
          have := pow_le_pow_left₀ (by norm_num) (show (1 : ℝ) ≤ Real.log (N : ℝ) by linarith only [hlog10]) 5
          simpa using this
        nlinarith only [hN15, hlog5]
      linarith only [h1_le]
    -- Combine Parts 1, 2, 3
    have hrearr : f 0 * ((∏ j ∈ Finset.Ico 1 J₁, f j) * (∏ j ∈ Finset.Ico J₁ J₂, f j) * (∏ j ∈ Finset.Ico J₂ m, f j)) =
        f 0 * (((∏ j ∈ Finset.Ico 1 J₁, f j) * (∏ j ∈ Finset.Ico J₂ m, f j)) * (∏ j ∈ Finset.Ico J₁ J₂, f j)) := by ring
    rw [hrearr]
    have h23 : ((∏ j ∈ Finset.Ico 1 J₁, f j) * (∏ j ∈ Finset.Ico J₂ m, f j)) * (∏ j ∈ Finset.Ico J₁ J₂, f j) ≤
        Real.exp (2100000 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5) := by
      have hmul := mul_le_mul hprod_ends hprod_mid (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Real.exp_pos _).le
      rw [← Real.exp_add] at hmul
      refine le_trans hmul (Real.exp_le_exp.mpr (by linarith only []))
    exact mul_le_mul hf0 h23 (mul_nonneg (mul_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      (Finset.prod_nonneg fun _ _ => norm_nonneg _)) (Finset.prod_nonneg fun _ _ => norm_nonneg _)) hM_nn
  -- Apply Maximum Modulus Principle to gFun on ball 0 1
  have hd : DiffContOnCl ℂ gFun (Metric.ball (0 : ℂ) 1) := by
    apply Differentiable.diffContOnCl
    have hqdiff : Differentiable ℂ (qPoly N s σ d c a) := by
      unfold qPoly sparsePoly
      refine (((differentiable_id.sub_const _).mul (differentiable_id.sub_const _)).mul ?_)
      have h1 : Differentiable ℂ (fun z : ℂ => if σ then z ^ d else 0) := by
        cases σ <;> [exact differentiable_const 0; exact differentiable_id.pow d]
      exact ((differentiable_const 1).sub h1).add
        (Differentiable.fun_sum fun j _ => (differentiable_id.pow j).const_mul _)
    have hprod_diff : ∀ S : Finset ℕ, Differentiable ℂ (fun z : ℂ =>
        ∏ j ∈ S, qPoly N s σ d c a (hFunc r a (Complex.exp (2 * Real.pi * (j : ℂ) / (m : ℂ) * I) * z))) := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp [differentiable_const]
      | @insert a' s' ha' ih =>
        have hstep : Differentiable ℂ (fun z : ℂ =>
            qPoly N s σ d c a (hFunc r a (Complex.exp (2 * Real.pi * (a' : ℂ) / (m : ℂ) * I) * z))) :=
          hqdiff.comp ((differentiable_hFunc r a).comp (differentiable_id.const_mul _))
        simpa [Finset.prod_insert ha'] using hstep.fun_mul ih
    exact hprod_diff (Finset.range m)
  have hmmp := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hd hfront
    (subset_closure (Metric.mem_ball_self zero_lt_one))
  rw [hg0] at hmmp
  have hexp_pos : 0 < Real.exp (2100000 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5) := Real.exp_pos _
  rw [show -2100000 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5 =
      -(2100000 * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5) by ring, Real.exp_neg]
  exact (inv_le_iff_one_le_mul₀' hexp_pos).mpr (by linarith)

/- ### Section 6: Hadamard Three Lines on the Lens and Arc Lower Bound (Theorem 4.2) -/

private noncomputable def mobiusLens (a : ℝ) (w : ℂ) : ℂ :=
  (Complex.exp ((a : ℂ) * I) + Complex.exp (-(a : ℂ) * I) * w) / (1 + w)

private lemma one_add_exp_I_mul_ne_zero {a : ℝ} (ha0 : 0 < a) (ha_pi : a < Real.pi / 4)
    {s : ℂ} (hs : s.re ∈ Set.Icc (-(1 / 2 : ℝ)) (3 / 2 : ℝ)) :
    (1 : ℂ) + Complex.exp (I * (a : ℂ) * s) ≠ 0 := by
  intro h0
  have hre : ((1 : ℂ) + Complex.exp (I * (a : ℂ) * s)).re = 0 := by rw [h0]; simp
  have hexp : I * (a : ℂ) * s = ((-a * s.im : ℝ) : ℂ) + ((a * s.re : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hexp, Complex.add_re, Complex.one_re, Complex.exp_add, Complex.mul_re,
    Complex.exp_ofReal_re, Complex.exp_ofReal_im, zero_mul, sub_zero,
    Complex.exp_ofReal_mul_I_re] at hre
  have hcos : 0 < Real.cos (a * s.re) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [hs.1, hs.2, Real.pi_pos]
  have : 0 < Real.exp (-a * s.im) * Real.cos (a * s.re) := mul_pos (Real.exp_pos _) hcos
  linarith

private lemma norm_mobiusLens_le_one {a : ℝ} (ha0 : 0 < a) (ha_pi : a < Real.pi / 4)
    {s : ℂ} (hs : s ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1) :
    ‖mobiusLens a (Complex.exp (I * (a : ℂ) * s))‖ ≤ 1 := by
  set w : ℂ := Complex.exp (I * (a : ℂ) * s)
  have hne : (1 : ℂ) + w ≠ 0 := one_add_exp_I_mul_ne_zero ha0 ha_pi ⟨by linarith [hs.1], by linarith [hs.2]⟩
  set R : ℝ := Real.exp (-a * s.im)
  set θ : ℝ := a * s.re
  have hRpos : 0 < R := Real.exp_pos _
  have hw_eq : w = (R : ℂ) * Complex.exp ((θ : ℂ) * I) := by
    simp only [w, R, θ]
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    apply Complex.ext <;> simp
  have hnum_eq : Complex.exp ((a : ℂ) * I) + Complex.exp (-(a : ℂ) * I) * w =
      Complex.exp ((a : ℂ) * I) * (1 + (R : ℂ) * Complex.exp (((θ - 2 * a : ℝ) : ℂ) * I)) := by
    rw [hw_eq, mul_add, mul_one]
    congr 1
    rw [show Complex.exp (-(a : ℂ) * I) * ((R : ℂ) * Complex.exp ((θ : ℂ) * I)) =
      (R : ℂ) * (Complex.exp (-(a : ℂ) * I) * Complex.exp ((θ : ℂ) * I)) by ring,
      show Complex.exp ((a : ℂ) * I) * ((R : ℂ) * Complex.exp (((θ - 2 * a : ℝ) : ℂ) * I)) =
      (R : ℂ) * (Complex.exp ((a : ℂ) * I) * Complex.exp (((θ - 2 * a : ℝ) : ℂ) * I)) by ring,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 2; push_cast; ring
  unfold mobiusLens
  rw [norm_div, hnum_eq, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, div_le_one (norm_pos_iff.mpr hne)]
  have hsq : ‖(1 : ℂ) + (R : ℂ) * Complex.exp (((θ - 2 * a : ℝ) : ℂ) * I)‖ ^ 2 ≤ ‖(1 : ℂ) + w‖ ^ 2 := by
    rw [hw_eq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero, add_zero, zero_add]
    have hcos_eq : Real.cos (θ - 2 * a) = Real.cos (2 * a - θ) := by
      rw [← Real.cos_neg]; congr 1; ring
    have hcos_le : Real.cos (2 * a - θ) ≤ Real.cos θ := by
      apply Real.strictAntiOn_cos.antitoneOn
      · exact ⟨by nlinarith [hs.1], by nlinarith [hs.2, Real.pi_pos]⟩
      · exact ⟨by nlinarith [hs.2], by nlinarith [hs.1, Real.pi_pos]⟩
      · nlinarith [hs.2]
    have hsc1 := Real.sin_sq_add_cos_sq (θ - 2 * a)
    have hsc2 := Real.sin_sq_add_cos_sq θ
    have hL : (1 + R * Real.cos (θ - 2 * a)) * (1 + R * Real.cos (θ - 2 * a)) +
        R * Real.sin (θ - 2 * a) * (R * Real.sin (θ - 2 * a)) =
        1 + R ^ 2 + 2 * R * Real.cos (θ - 2 * a) := by linear_combination R ^ 2 * hsc1
    have hR : (1 + R * Real.cos θ) * (1 + R * Real.cos θ) +
        R * Real.sin θ * (R * Real.sin θ) =
        1 + R ^ 2 + 2 * R * Real.cos θ := by linear_combination R ^ 2 * hsc2
    rw [hL, hR, hcos_eq]
    nlinarith [hcos_le, hRpos]
  nlinarith [norm_nonneg ((1 : ℂ) + (R : ℂ) * Complex.exp (((θ - 2 * a : ℝ) : ℂ) * I)),
    norm_nonneg ((1 : ℂ) + w)]

private lemma hadamard_lens_bound {N s d : ℕ} {σ : Bool} {c : ℕ → ℝ} {a L : ℝ}
    (ha0 : 0 < a) (ha_pi : a < Real.pi / 4) (hL : 0 < L)
    (hd1 : 1 ≤ d) (hds : d < s) (hsN : s ≤ N) (hc : ∀ j, |c j| ≤ 1)
    (harc : ∀ θ ∈ Set.Icc (-a) a, ‖sparsePoly N s σ d c (Complex.exp ((θ : ℂ) * I))‖ ≤ L) :
    ∀ z : ℂ, inGa a z →
      ‖qPoly N s σ d c a z‖ ≤ max (4 * L) (Real.sqrt (8 * L)) := by
  let f : ℂ → ℂ := fun t => qPoly N s σ d c a (mobiusLens a (Complex.exp (I * (a : ℂ) * t)))
  have hqdiff : Differentiable ℂ (qPoly N s σ d c a) := by
    unfold qPoly sparsePoly
    refine (((differentiable_id.sub_const _).mul (differentiable_id.sub_const _)).mul ?_)
    have h1 : Differentiable ℂ (fun z : ℂ => if σ then z ^ d else 0) := by
      cases σ <;> [exact differentiable_const 0; exact differentiable_id.pow d]
    exact ((differentiable_const 1).sub h1).add
      (Differentiable.fun_sum fun j _ => (differentiable_id.pow j).const_mul _)
  -- f is differentiable on verticalClosedStrip 0 1, hence DiffContOnCl on verticalStrip 0 1
  have hf_diffOn : DifferentiableOn ℂ f (Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    intro t ht
    have hne := one_add_exp_I_mul_ne_zero ha0 ha_pi (s := t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hexp_d : DifferentiableAt ℂ (fun u : ℂ => Complex.exp (I * (a : ℂ) * u)) t :=
      (differentiableAt_id.const_mul (I * (a : ℂ))).cexp
    have hmob_d : DifferentiableAt ℂ (fun u : ℂ => mobiusLens a (Complex.exp (I * (a : ℂ) * u))) t := by
      unfold mobiusLens
      exact ((differentiableAt_const _).add (hexp_d.const_mul _)).div ((differentiableAt_const _).add hexp_d) hne
    exact (hqdiff.differentiableAt.comp t hmob_d).differentiableWithinAt
  have hf_dc : DiffContOnCl ℂ f (Complex.HadamardThreeLines.verticalStrip 0 1) := by
    refine ⟨hf_diffOn.mono (fun t ht => ⟨ht.1.le, ht.2.le⟩), ?_⟩
    have hcl : closure (Complex.HadamardThreeLines.verticalStrip 0 1) ⊆
        Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
      refine closure_minimal (fun t ht => ⟨ht.1.le, ht.2.le⟩) ?_
      exact isClosed_Icc.preimage Complex.continuous_re
    exact hf_diffOn.continuousOn.mono hcl
  -- Bounded above on verticalClosedStrip 0 1
  have hf_bdd : BddAbove ((norm ∘ f) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨4 * (2 + (N : ℝ)), ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    set z : ℂ := mobiusLens a (Complex.exp (I * (a : ℂ) * t))
    have hz1 : ‖z‖ ≤ 1 := norm_mobiusLens_le_one ha0 ha_pi ht
    have h1 : ‖z - Complex.exp ((a : ℂ) * I)‖ ≤ 2 := by
      calc ‖z - Complex.exp ((a : ℂ) * I)‖ ≤ ‖z‖ + ‖Complex.exp ((a : ℂ) * I)‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by rw [Complex.norm_exp_ofReal_mul_I]; linarith
        _ = 2 := by ring
    have h2 : ‖z - Complex.exp (-(a : ℂ) * I)‖ ≤ 2 := by
      calc ‖z - Complex.exp (-(a : ℂ) * I)‖ ≤ ‖z‖ + ‖Complex.exp (-(a : ℂ) * I)‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by
            rw [show -(a : ℂ) * I = ((-a : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
            linarith
        _ = 2 := by ring
    have hp : ‖sparsePoly N s σ d c z‖ ≤ 2 + (N : ℝ) := by
      unfold sparsePoly
      have hp1 : ‖(1 : ℂ) - (if σ then z ^ d else 0)‖ ≤ 2 := by
        calc ‖(1 : ℂ) - (if σ then z ^ d else 0)‖ ≤ ‖(1 : ℂ)‖ + ‖if σ then z ^ d else 0‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := by
              rw [norm_one]; gcongr; split_ifs
              · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz1
              · simp
          _ = 2 := by ring
      have hp2 : ‖∑ j ∈ Finset.Icc s N, (c j : ℂ) * z ^ j‖ ≤ (N : ℝ) := by
        calc ‖∑ j ∈ Finset.Icc s N, (c j : ℂ) * z ^ j‖
            ≤ ∑ j ∈ Finset.Icc s N, ‖(c j : ℂ) * z ^ j‖ := norm_sum_le _ _
          _ ≤ ∑ _j ∈ Finset.Icc s N, (1 : ℝ) := by
              refine Finset.sum_le_sum fun j _ => ?_
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
              exact mul_le_one₀ (hc j) (pow_nonneg (norm_nonneg _) _) (pow_le_one₀ (norm_nonneg _) hz1)
          _ = ((Finset.Icc s N).card : ℝ) := by simp
          _ ≤ (N : ℝ) := by
              have : (Finset.Icc s N).card ≤ N := by simp; omega
              exact_mod_cast this
      exact le_trans (norm_add_le _ _) (add_le_add hp1 hp2)
    simp only [Function.comp_apply, f, qPoly, norm_mul]
    have h12 : ‖z - Complex.exp ((a : ℂ) * I)‖ * ‖z - Complex.exp (-(a : ℂ) * I)‖ ≤ 4 := by
      have := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num); linarith
    exact mul_le_mul h12 hp (norm_nonneg _) (by norm_num)
  -- Left boundary (t.re = 0): ‖f t‖ ≤ 2
  have hleft : ∀ t ∈ Complex.re ⁻¹' {(0 : ℝ)}, ‖f t‖ ≤ 2 := by
    intro t ht
    have htre : t.re = 0 := ht
    set R : ℝ := Real.exp (-a * t.im)
    have hRpos : 0 < R := Real.exp_pos _
    have hexpR : Complex.exp (I * (a : ℂ) * t) = (R : ℂ) := by
      simp only [R, Complex.ofReal_exp]; congr 1
      apply Complex.ext <;> simp [htre]
    set z : ℂ := mobiusLens a (R : ℂ)
    set u : ℝ := (1 - R) / (1 + R)
    have h1R : 0 < 1 + R := by linarith
    have hz_eq : z = (Real.cos a : ℂ) + ((u * Real.sin a : ℝ) : ℂ) * I := by
      simp only [z, mobiusLens]
      have h1RC : (1 : ℂ) + (R : ℂ) ≠ 0 := by exact_mod_cast h1R.ne'
      rw [div_eq_iff h1RC]
      have hneg : -(a : ℂ) * I = ((-a : ℝ) : ℂ) * I := by push_cast; ring
      apply Complex.ext
      · simp only [hneg, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.one_re, Complex.one_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg]
        ring
      · simp only [hneg, Complex.add_re, Complex.add_im, Complex.mul_im, Complex.one_re, Complex.one_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.sin_neg, u]
        field_simp [h1R.ne']; ring
    have hu_sq : 1 - u ^ 2 = 4 * R / (1 + R) ^ 2 := by
      simp only [u]; field_simp [h1R.ne']; ring
    have hu_sq_pos : 0 < 1 - u ^ 2 := by rw [hu_sq]; positivity
    have hsin_pos : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.pi_pos])
    have hz_norm_sq : ‖z‖ ^ 2 = 1 - (1 - u ^ 2) * (Real.sin a) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, hz_eq, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
        sub_zero, add_zero, zero_add]
      nlinarith [Real.sin_sq_add_cos_sq a]
    have hz_lt1 : ‖z‖ < 1 := by
      have : ‖z‖ ^ 2 < 1 := by nlinarith [sq_pos_of_pos hsin_pos]
      nlinarith [norm_nonneg z]
    have hquad : ‖(z - Complex.exp ((a : ℂ) * I)) * (z - Complex.exp (-(a : ℂ) * I))‖ = 1 - ‖z‖ ^ 2 := by
      have hz1 : z - Complex.exp ((a : ℂ) * I) = (((u - 1) * Real.sin a : ℝ) : ℂ) * I := by
        rw [hz_eq]; apply Complex.ext
        · simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.exp_ofReal_mul_I_re]
          ring
        · simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.exp_ofReal_mul_I_im]
          ring
      have hz2 : z - Complex.exp (-(a : ℂ) * I) = (((u + 1) * Real.sin a : ℝ) : ℂ) * I := by
        have hneg : -(a : ℂ) * I = ((-a : ℝ) : ℂ) * I := by push_cast; ring
        rw [hz_eq, hneg]; apply Complex.ext
        · simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
          ring
        · simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
          ring
      rw [hz1, hz2, norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, mul_one,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, ← abs_mul]
      have hprod : (u - 1) * Real.sin a * ((u + 1) * Real.sin a) = -((1 - u ^ 2) * (Real.sin a) ^ 2) := by ring
      rw [hprod, abs_neg, abs_of_pos (mul_pos hu_sq_pos (sq_pos_of_pos hsin_pos))]
      linarith
    have hp_geom : ‖sparsePoly N s σ d c z‖ ≤ 1 / (1 - ‖z‖) := by
      have hsub : ({0, d} ∪ Finset.Icc s N : Finset ℕ) ⊆ Finset.range (N + 1) := by
        intro j hj
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc,
          Finset.mem_range] at hj ⊢
        omega
      have hdis1 : Disjoint ({0} : Finset ℕ) ({d} : Finset ℕ) := by
        rw [Finset.disjoint_singleton]; omega
      have hdis2 : Disjoint ({0, d} : Finset ℕ) (Finset.Icc s N) := by
        rw [Finset.disjoint_left]; intro j h1 h2
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc] at h1 h2; omega
      have hsum_le : 1 + (if σ then ‖z‖ ^ d else 0) + ∑ j ∈ Finset.Icc s N, ‖z‖ ^ j ≤
          ∑ j ∈ Finset.range (N + 1), ‖z‖ ^ j := by
        have h1 : 1 + (if σ then ‖z‖ ^ d else 0) + ∑ j ∈ Finset.Icc s N, ‖z‖ ^ j ≤
            ∑ j ∈ ({0, d} ∪ Finset.Icc s N : Finset ℕ), ‖z‖ ^ j := by
          rw [Finset.sum_union hdis2, Finset.sum_pair (by omega : 0 ≠ d), pow_zero]
          split_ifs
          · linarith
          · linarith [pow_nonneg (norm_nonneg z) d]
        exact le_trans h1 (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => pow_nonneg (norm_nonneg z) _)
      have hgeom : ∑ j ∈ Finset.range (N + 1), ‖z‖ ^ j ≤ 1 / (1 - ‖z‖) := by
        rw [geom_sum_eq hz_lt1.ne]
        have h1 : (‖z‖ ^ (N + 1) - 1) / (‖z‖ - 1) = (1 - ‖z‖ ^ (N + 1)) / (1 - ‖z‖) := by
          rw [← neg_div_neg_eq]; congr 1 <;> ring
        rw [h1]
        exact div_le_div_of_nonneg_right (by linarith [pow_nonneg (norm_nonneg z) (N + 1)]) (by linarith)
      have htri : ‖sparsePoly N s σ d c z‖ ≤
          1 + (if σ then ‖z‖ ^ d else 0) + ∑ j ∈ Finset.Icc s N, ‖z‖ ^ j := by
        unfold sparsePoly
        calc ‖(1 : ℂ) - (if σ then z ^ d else 0) + ∑ j ∈ Finset.Icc s N, (c j : ℂ) * z ^ j‖
            ≤ ‖(1 : ℂ) - (if σ then z ^ d else 0)‖ + ‖∑ j ∈ Finset.Icc s N, (c j : ℂ) * z ^ j‖ :=
              norm_add_le _ _
          _ ≤ (1 + (if σ then ‖z‖ ^ d else 0)) + ∑ j ∈ Finset.Icc s N, ‖z‖ ^ j := by
              apply add_le_add
              · calc ‖(1 : ℂ) - (if σ then z ^ d else 0)‖ ≤ ‖(1 : ℂ)‖ + ‖if σ then z ^ d else 0‖ := norm_sub_le _ _
                  _ = 1 + (if σ then ‖z‖ ^ d else 0) := by rw [norm_one]; split_ifs <;> simp
              · calc ‖∑ j ∈ Finset.Icc s N, (c j : ℂ) * z ^ j‖
                    ≤ ∑ j ∈ Finset.Icc s N, ‖(c j : ℂ) * z ^ j‖ := norm_sum_le _ _
                  _ ≤ ∑ j ∈ Finset.Icc s N, ‖z‖ ^ j := by
                      refine Finset.sum_le_sum fun j _ => ?_
                      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
                      exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg z) j) (hc j)
      exact le_trans htri (le_trans hsum_le hgeom)
    simp only [f, hexpR, qPoly, norm_mul]
    rw [← norm_mul, hquad]
    have h1z_pos : 0 < 1 - ‖z‖ := by linarith
    calc (1 - ‖z‖ ^ 2) * ‖sparsePoly N s σ d c z‖
        ≤ (1 - ‖z‖ ^ 2) * (1 / (1 - ‖z‖)) := mul_le_mul_of_nonneg_left hp_geom (by nlinarith)
      _ = 1 + ‖z‖ := by field_simp [h1z_pos.ne']; ring
      _ ≤ 2 := by linarith
  -- Right boundary (t.re = 1): ‖f t‖ ≤ 4 * L
  have hright : ∀ t ∈ Complex.re ⁻¹' {(1 : ℝ)}, ‖f t‖ ≤ 4 * L := by
    intro t ht
    have htre : t.re = 1 := ht
    set R : ℝ := Real.exp (-a * t.im)
    have hRpos : 0 < R := Real.exp_pos _
    have hexpR : Complex.exp (I * (a : ℂ) * t) = (R : ℂ) * Complex.exp ((a : ℂ) * I) := by
      simp only [R, Complex.ofReal_exp]
      rw [← Complex.exp_add]
      congr 1
      apply Complex.ext <;> simp [htre]
    set z : ℂ := mobiusLens a ((R : ℂ) * Complex.exp ((a : ℂ) * I))
    have hden_ne : (1 : ℂ) + (R : ℂ) * Complex.exp ((a : ℂ) * I) ≠ 0 := by
      rw [← hexpR]; exact one_add_exp_I_mul_ne_zero ha0 ha_pi (s := t) ⟨by linarith, by linarith⟩
    have hz_rew : z = (Complex.exp ((a : ℂ) * I) + (R : ℂ)) / (1 + (R : ℂ) * Complex.exp ((a : ℂ) * I)) := by
      simp only [z, mobiusLens]
      congr 1
      rw [show Complex.exp (-(a : ℂ) * I) * ((R : ℂ) * Complex.exp ((a : ℂ) * I)) =
        (R : ℂ) * (Complex.exp (-(a : ℂ) * I) * Complex.exp ((a : ℂ) * I)) by ring,
        ← Complex.exp_add, show -(a : ℂ) * I + (a : ℂ) * I = 0 by ring, Complex.exp_zero, mul_one]
    have hz_norm : ‖z‖ = 1 := by
      rw [hz_rew, norm_div, div_eq_one_iff_eq (norm_pos_iff.mpr hden_ne).ne']
      have hsq : ‖Complex.exp ((a : ℂ) * I) + (R : ℂ)‖ ^ 2 =
          ‖(1 : ℂ) + (R : ℂ) * Complex.exp ((a : ℂ) * I)‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
        simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.mul_re,
          Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
          Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero, add_zero, zero_add]
        have hsc := Real.sin_sq_add_cos_sq a
        linear_combination (1 - R ^ 2) * hsc
      nlinarith [norm_nonneg (Complex.exp ((a : ℂ) * I) + (R : ℂ)),
        norm_nonneg ((1 : ℂ) + (R : ℂ) * Complex.exp ((a : ℂ) * I))]
    have hz_re : Real.cos a ≤ z.re := by
      rw [hz_rew, Complex.div_re]
      set D : ℝ := Complex.normSq ((1 : ℂ) + (R : ℂ) * Complex.exp ((a : ℂ) * I))
      have hDpos : 0 < D := Complex.normSq_pos.mpr hden_ne
      have hD_eq : D = 1 + R ^ 2 + 2 * R * Real.cos a := by
        simp only [D, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re,
          Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero, add_zero, zero_add]
        linear_combination R ^ 2 * Real.sin_sq_add_cos_sq a
      have hnum_eq : (Complex.exp ((a : ℂ) * I) + (R : ℂ)).re *
          ((1 : ℂ) + (R : ℂ) * Complex.exp ((a : ℂ) * I)).re +
          (Complex.exp ((a : ℂ) * I) + (R : ℂ)).im *
          ((1 : ℂ) + (R : ℂ) * Complex.exp ((a : ℂ) * I)).im =
          (1 + R ^ 2) * Real.cos a + 2 * R := by
        simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.mul_re,
          Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
          Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero, add_zero, zero_add]
        linear_combination R * Real.sin_sq_add_cos_sq a
      rw [← add_div, hnum_eq, le_div_iff₀ hDpos, hD_eq]
      nlinarith [Real.sin_sq_add_cos_sq a, sq_nonneg (Real.sin a)]
    set θ : ℝ := Complex.arg z
    have hz_exp : z = Complex.exp ((θ : ℂ) * I) := by
      simpa [hz_norm] using (Complex.norm_mul_exp_arg_mul_I z).symm
    have hθ_mem : θ ∈ Set.Icc (-a) a := by
      have hcos_ge : Real.cos a ≤ Real.cos |θ| := by
        rw [Real.cos_abs]
        have : z.re = Real.cos θ := by rw [hz_exp, Complex.exp_ofReal_mul_I_re]
        linarith
      have habs_le : |θ| ≤ a := by
        by_contra hgt; push Not at hgt
        have hlt := Real.strictAntiOn_cos ⟨ha0.le, by linarith [Real.pi_pos]⟩
          ⟨abs_nonneg θ, Complex.abs_arg_le_pi z⟩ hgt
        linarith
      exact abs_le.mp habs_le
    have hp_le : ‖sparsePoly N s σ d c z‖ ≤ L := by rw [hz_exp]; exact harc θ hθ_mem
    have hfac1 : ‖z - Complex.exp ((a : ℂ) * I)‖ ≤ 2 := by
      calc ‖z - Complex.exp ((a : ℂ) * I)‖ ≤ ‖z‖ + ‖Complex.exp ((a : ℂ) * I)‖ := norm_sub_le _ _
        _ = 2 := by rw [hz_norm, Complex.norm_exp_ofReal_mul_I]; ring
    have hfac2 : ‖z - Complex.exp (-(a : ℂ) * I)‖ ≤ 2 := by
      calc ‖z - Complex.exp (-(a : ℂ) * I)‖ ≤ ‖z‖ + ‖Complex.exp (-(a : ℂ) * I)‖ := norm_sub_le _ _
        _ = 2 := by
            rw [hz_norm, show -(a : ℂ) * I = ((-a : ℝ) : ℂ) * I by push_cast; ring,
              Complex.norm_exp_ofReal_mul_I]; ring
    simp only [f, hexpR, qPoly, norm_mul]
    have h12 : ‖z - Complex.exp ((a : ℂ) * I)‖ * ‖z - Complex.exp (-(a : ℂ) * I)‖ ≤ 4 := by
      have := mul_le_mul hfac1 hfac2 (norm_nonneg _) (by norm_num); linarith
    exact mul_le_mul h12 hp_le (norm_nonneg _) (by norm_num)
  -- For any z ∈ inGa a, find t₀ ∈ verticalClosedStrip 0 1 with t₀.re ∈ [1/2, 1] and mobiusLens = z
  intro z hz
  rcases hz with ⟨hz_lt1, hz_re, hz_lens⟩
  have hcos_pos : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsin_pos : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.pi_pos])
  have hden_ne : z - Complex.exp (-(a : ℂ) * I) ≠ 0 := by
    intro h0
    have heq : z = Complex.exp (-(a : ℂ) * I) := sub_eq_zero.mp h0
    have hn : ‖z‖ = 1 := by
      rw [heq, show -(a : ℂ) * I = ((-a : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
    linarith
  set w : ℂ := (Complex.exp ((a : ℂ) * I) - z) / (z - Complex.exp (-(a : ℂ) * I))
  have h1w_ne : (1 : ℂ) + w ≠ 0 := by
    simp only [w]
    rw [one_add_div hden_ne]
    apply div_ne_zero _ hden_ne
    intro h0
    have him : (z - Complex.exp (-(a : ℂ) * I) + (Complex.exp ((a : ℂ) * I) - z)).im = 0 := by rw [h0]; simp
    simp only [Complex.add_im, Complex.sub_im, Complex.exp_ofReal_mul_I_im,
      show -(a : ℂ) * I = ((-a : ℝ) : ℂ) * I by push_cast; ring, Real.sin_neg] at him
    linarith
  have hmob_eq : mobiusLens a w = z := by
    unfold mobiusLens
    rw [div_eq_iff h1w_ne]
    have hw_mul : w * (z - Complex.exp (-(a : ℂ) * I)) = Complex.exp ((a : ℂ) * I) - z :=
      div_mul_cancel₀ _ hden_ne
    apply mul_right_cancel₀ hden_ne
    calc (Complex.exp ((a : ℂ) * I) + Complex.exp (-(a : ℂ) * I) * w) * (z - Complex.exp (-(a : ℂ) * I))
        = Complex.exp ((a : ℂ) * I) * (z - Complex.exp (-(a : ℂ) * I)) +
            Complex.exp (-(a : ℂ) * I) * (w * (z - Complex.exp (-(a : ℂ) * I))) := by ring
      _ = Complex.exp ((a : ℂ) * I) * (z - Complex.exp (-(a : ℂ) * I)) +
            Complex.exp (-(a : ℂ) * I) * (Complex.exp ((a : ℂ) * I) - z) := by rw [hw_mul]
      _ = z * (z - Complex.exp (-(a : ℂ) * I)) + z * (Complex.exp ((a : ℂ) * I) - z) := by ring
      _ = z * (1 + w) * (z - Complex.exp (-(a : ℂ) * I)) := by rw [← hw_mul]; ring
  -- Compute w.re and w.im
  set D : ℝ := Complex.normSq (z - Complex.exp (-(a : ℂ) * I))
  have hDpos : 0 < D := Complex.normSq_pos.mpr hden_ne
  have hw_re_eq : w.re = ((1 - ‖z‖ ^ 2) + 2 * Real.cos a * (z.re - Real.cos a)) / D := by
    simp only [w, Complex.div_re, ← add_div]
    congr 1
    have hzsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [hzsq]
    simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      show -(a : ℂ) * I = ((-a : ℝ) : ℂ) * I by push_cast; ring, Real.cos_neg, Real.sin_neg]
    nlinarith [Real.sin_sq_add_cos_sq a]
  have hw_im_eq : w.im = (2 * Real.sin a * (z.re - Real.cos a)) / D := by
    simp only [w, Complex.div_im, ← sub_div]
    congr 1
    simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      show -(a : ℂ) * I = ((-a : ℝ) : ℂ) * I by push_cast; ring, Real.cos_neg, Real.sin_neg]
    ring
  have h1zsq : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hw_re_pos : 0 < w.re := by rw [hw_re_eq]; positivity
  have hw_im_pos : 0 < w.im := by rw [hw_im_eq]; positivity
  have hw_ne : w ≠ 0 := by intro h0; rw [h0] at hw_re_pos; simp at hw_re_pos
  have hratio_lt : w.im / w.re < Real.tan a := by
    rw [hw_im_eq, hw_re_eq, div_div_div_cancel_right₀ hDpos.ne', Real.tan_eq_sin_div_cos,
      div_lt_div_iff₀ (by positivity) hcos_pos]
    nlinarith
  have hratio_gt : Real.tan (a / 2) < w.im / w.re := by
    have hcos_lt1 : Real.cos a < 1 := by
      have hsq : Real.cos a ^ 2 < 1 := by nlinarith [Real.sin_sq_add_cos_sq a, sq_pos_of_pos hsin_pos]
      nlinarith
    have htan_half : Real.tan (a / 2) = Real.sin a / (1 + Real.cos a) := by
      have hcos_h : 0 < Real.cos (a / 2) :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      have hsin_2 : Real.sin a = 2 * Real.sin (a / 2) * Real.cos (a / 2) := by
        simpa [two_mul, add_halves] using Real.sin_two_mul (a / 2)
      have hcos_2 : 1 + Real.cos a = 2 * (Real.cos (a / 2)) ^ 2 := by
        have := Real.cos_two_mul (a / 2)
        rw [show 2 * (a / 2) = a by ring] at this
        linarith
      rw [Real.tan_eq_sin_div_cos, hsin_2, hcos_2]
      field_simp [hcos_h.ne']
    rw [htan_half, hw_im_eq, hw_re_eq, div_div_div_cancel_right₀ hDpos.ne',
      div_lt_div_iff₀ (by linarith) (by positivity)]
    have hstep : 1 - ‖z‖ ^ 2 < 2 * (z.re - Real.cos a) := by nlinarith [hz_lens, hz_re, hcos_lt1]
    nlinarith [hstep, hsin_pos]
  set θ : ℝ := Real.arctan (w.im / w.re)
  have hθ_gt : a / 2 < θ := by
    have h1 := Real.arctan_tan (x := a / 2) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    rw [← h1]
    exact Real.arctan_strictMono hratio_gt
  have hθ_lt : θ < a := by
    have h1 := Real.arctan_tan (x := a) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    rw [← h1]
    exact Real.arctan_strictMono hratio_lt
  have hw_polar : w = (‖w‖ : ℂ) * Complex.exp ((θ : ℂ) * I) := by
    have hcos_θ : Real.cos θ = w.re / ‖w‖ := by
      simp only [θ, Real.cos_arctan]
      have h1 : 1 + (w.im / w.re) ^ 2 = (‖w‖ / w.re) ^ 2 := by
        have hwsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
        field_simp [hw_re_pos.ne']; linarith
      rw [h1, Real.sqrt_sq (by positivity), one_div_div]
    have hsin_θ : Real.sin θ = w.im / ‖w‖ := by
      simp only [θ, Real.sin_arctan]
      have h1 : 1 + (w.im / w.re) ^ 2 = (‖w‖ / w.re) ^ 2 := by
        have hwsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
        field_simp [hw_re_pos.ne']; linarith
      rw [h1, Real.sqrt_sq (by positivity)]
      field_simp [hw_re_pos.ne', (norm_pos_iff.mpr hw_ne).ne']
    apply Complex.ext
    · simp [Complex.exp_ofReal_mul_I_re, hcos_θ, mul_div_cancel₀ _ (norm_pos_iff.mpr hw_ne).ne']
    · simp [Complex.exp_ofReal_mul_I_im, hsin_θ, mul_div_cancel₀ _ (norm_pos_iff.mpr hw_ne).ne']
  set t₀ : ℂ := ((θ / a : ℝ) : ℂ) + ((-(Real.log ‖w‖) / a : ℝ) : ℂ) * I
  have ht₀_re : t₀.re = θ / a := by simp [t₀]
  have ht₀_mem : t₀ ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    change t₀.re ∈ Set.Icc 0 1
    rw [ht₀_re]
    exact ⟨by positivity, (div_le_one ha0).mpr hθ_lt.le⟩
  have ht₀_half : 1 / 2 ≤ t₀.re := by
    rw [ht₀_re, le_div_iff₀ ha0]; linarith
  have hft₀ : f t₀ = qPoly N s σ d c a z := by
    have hexp : Complex.exp (I * (a : ℂ) * t₀) = w := by
      have h1 : I * (a : ℂ) * t₀ = ((Real.log ‖w‖ : ℝ) : ℂ) + ((θ : ℝ) : ℂ) * I := by
        simp only [t₀]
        apply Complex.ext <;> simp <;> field_simp [ha0.ne']
      rw [h1, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.mpr hw_ne), ← hw_polar]
    simp only [f, hexp, hmob_eq]
  -- Apply Hadamard Three Lines theorem!
  have hhad := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (f := f) (z := t₀) (a := (2 : ℝ)) (b := 4 * L) (l := 0) (u := 1)
    zero_lt_one ht₀_mem hf_dc hf_bdd hleft hright
  rw [hft₀] at hhad
  simp only [sub_zero, div_one] at hhad
  set u : ℝ := t₀.re
  have hu_le1 : u ≤ 1 := ht₀_mem.2
  have hrew : (2 : ℝ) ^ (1 - u) * (4 * L) ^ u = 2 * (2 * L) ^ u := by
    have h4L : (4 * L) ^ u = (2 : ℝ) ^ u * (2 * L) ^ u := by
      rw [← Real.mul_rpow (by norm_num) (by positivity)]; congr 1; ring
    rw [h4L, ← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), sub_add_cancel, Real.rpow_one]
  rw [hrew] at hhad
  rcases le_total 1 (2 * L) with h2L | h2L
  · have hpow : (2 * L) ^ u ≤ 2 * L := by
      calc (2 * L) ^ u ≤ (2 * L) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h2L hu_le1
        _ = 2 * L := Real.rpow_one _
    exact le_trans hhad (le_trans (by linarith) (le_max_left _ _))
  · have hpow : (2 * L) ^ u ≤ Real.sqrt (2 * L) := by
      calc (2 * L) ^ u ≤ (2 * L) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge (by positivity) h2L ht₀_half
        _ = Real.sqrt (2 * L) := (Real.sqrt_eq_rpow (2 * L)).symm
    have hsqrt : 2 * Real.sqrt (2 * L) = Real.sqrt (8 * L) := by
      rw [show (2 : ℝ) = Real.sqrt 4 by norm_num, ← Real.sqrt_mul (by norm_num)]; congr 1; ring
    exact le_trans hhad (le_trans (by linarith) (le_max_right _ _))

/-- Theorem 4.2 (Chase 2020): Lower bound for sparse polynomials on the small arc `[-N^{-2/5}, N^{-2/5}]`. -/
private lemma arclowerbound :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (s : ℕ) (σ : Bool) (d : ℕ) (c : ℕ → ℝ),
        (N : ℝ) ^ (1 / 5 : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ 2 * (N : ℝ) ^ (1 / 5 : ℝ) →
        1 ≤ d → d < s → (∀ j, |c j| ≤ 1) →
        ∃ θ ∈ Set.Icc (-((N : ℝ) ^ (-(2 / 5 : ℝ)))) ((N : ℝ) ^ (-(2 / 5 : ℝ))),
          Real.exp (-C * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5) ≤
            ‖sparsePoly N s σ d c (Complex.exp ((θ : ℂ) * I))‖ := by
  obtain ⟨C₀, hC₀, hprop⟩ := max_modulus_G_a_lower_bound
  refine ⟨2 * C₀ + 1, by linarith, ?_⟩
  have hN15_top : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 5 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp tendsto_natCast_atTop_atTop
  have hlog_top : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hprop, hN15_top.eventually_ge_atTop 10, hlog_top.eventually_ge_atTop 10,
    eventually_ge_atTop 1000] with N hN hN15 hlog10 hN1000
  intro s σ d c hs_lo hs_hi hd1 hds hc
  have hNpos : (0 : ℝ) < N := by positivity
  set a : ℝ := (N : ℝ) ^ (-(2 / 5 : ℝ))
  have ha0 : 0 < a := Real.rpow_pos_of_pos hNpos _
  have ha_pi : a < Real.pi / 4 := by
    have h25 : (100 : ℝ) ≤ (N : ℝ) ^ (2 / 5 : ℝ) := by
      have := pow_le_pow_left₀ (by norm_num) hN15 2
      rw [← Real.rpow_natCast ((N : ℝ) ^ (1 / 5 : ℝ)), ← Real.rpow_mul hNpos.le] at this
      norm_num at this; exact this
    have : a = ((N : ℝ) ^ (2 / 5 : ℝ))⁻¹ := Real.rpow_neg hNpos.le (2 / 5 : ℝ)
    rw [this]
    have hinv : ((N : ℝ) ^ (2 / 5 : ℝ))⁻¹ ≤ (100 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h25
    linarith [Real.pi_gt_three]
  have hsN : s ≤ N := by
    have h1 : (N : ℝ) ^ (1 / 5 : ℝ) * (N : ℝ) ^ (4 / 5 : ℝ) = (N : ℝ) := by
      rw [← Real.rpow_add hNpos]; norm_num
    have h45 : (2 : ℝ) ≤ (N : ℝ) ^ (4 / 5 : ℝ) := by
      have := pow_le_pow_left₀ (by norm_num) hN15 4
      rw [← Real.rpow_natCast ((N : ℝ) ^ (1 / 5 : ℝ)), ← Real.rpow_mul hNpos.le] at this
      norm_num at this; linarith
    have : (s : ℝ) ≤ (N : ℝ) := by nlinarith
    exact_mod_cast this
  by_contra hno
  push Not at hno
  set L : ℝ := Real.exp (-(2 * C₀ + 1) * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5)
  have hL_pos : 0 < L := Real.exp_pos _
  have harc : ∀ θ ∈ Set.Icc (-a) a, ‖sparsePoly N s σ d c (Complex.exp ((θ : ℂ) * I))‖ ≤ L :=
    fun θ hθ => (hno θ hθ).le
  have hM := hadamard_lens_bound ha0 ha_pi hL_pos hd1 hds hsN hc harc
  have hlo := hN s σ d c (max (4 * L) (Real.sqrt (8 * L))) hs_lo hs_hi hd1 hds hc hM
  set E : ℝ := (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5
  have hE_ge : (10 : ℝ) ≤ E := by
    have hlog5 : (1 : ℝ) ≤ (Real.log (N : ℝ)) ^ 5 := by
      have := pow_le_pow_left₀ (by norm_num) (show (1 : ℝ) ≤ Real.log (N : ℝ) by linarith) 5
      simpa using this
    nlinarith
  have h8L_lt : 8 * L < 1 := by
    have h1 : 8 * L = Real.exp (Real.log 8 - (2 * C₀ + 1) * E) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 8)]
      simp only [L, E, div_eq_mul_inv, ← Real.exp_neg]; congr 2; ring
    rw [h1]
    have hlog8 : Real.log 8 < 3 := by
      have h2 : (8 : ℝ) < Real.exp 3 := by
        have := Real.exp_one_gt_d9
        have h3 : (2.718 : ℝ) ^ 3 ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
        rw [← Real.exp_nat_mul] at h3; norm_num at h3; linarith
      calc Real.log 8 < Real.log (Real.exp 3) := Real.log_lt_log (by norm_num) h2
        _ = 3 := Real.log_exp 3
    exact Real.exp_lt_one_iff.mpr (by nlinarith)
  have hmax_le : max (4 * L) (Real.sqrt (8 * L)) = Real.sqrt (8 * L) := by
    apply max_eq_right
    have h1 : 4 * L ≤ 8 * L := by linarith
    have h2 : 8 * L ≤ Real.sqrt (8 * L) := by
      have hnn : 0 ≤ 8 * L := by positivity
      have := Real.sqrt_le_sqrt (show (8 * L) ^ 2 ≤ 8 * L by nlinarith)
      rwa [Real.sqrt_sq hnn] at this
    linarith
  rw [hmax_le] at hlo
  have hsqrt_lt : Real.sqrt (8 * L) < Real.exp (-C₀ * E) := by
    have hsq : 8 * L < (Real.exp (-C₀ * E)) ^ 2 := by
      rw [← Real.exp_nat_mul]
      have h1 : 8 * L = Real.exp (Real.log 8 - (2 * C₀ + 1) * E) := by
        rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 8)]
        simp only [L, E, div_eq_mul_inv, ← Real.exp_neg]; congr 2; ring
      rw [h1]
      apply Real.exp_lt_exp.mpr
      have hlog8 : Real.log 8 < 3 := by
        have h2 : (8 : ℝ) < Real.exp 3 := by
          have := Real.exp_one_gt_d9
          have h3 : (2.718 : ℝ) ^ 3 ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
          rw [← Real.exp_nat_mul] at h3; norm_num at h3; linarith
        calc Real.log 8 < Real.log (Real.exp 3) := Real.log_lt_log (by norm_num) h2
          _ = 3 := Real.log_exp 3
      push_cast; nlinarith
    calc Real.sqrt (8 * L) < Real.sqrt ((Real.exp (-C₀ * E)) ^ 2) := Real.sqrt_lt_sqrt (by positivity) hsq
      _ = Real.exp (-C₀ * E) := Real.sqrt_sq (Real.exp_pos _).le
  have hlo' : Real.exp (-C₀ * E) ≤ Real.sqrt (8 * L) := by
    simpa only [E, show -C₀ * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log N) ^ 5 = -C₀ * E by simp [E]; ring] using hlo
  linarith

/- ### Section 7: Final Assembly — Amplified Pairwise Tests (`OMA.solution`) -/

private lemma norm_two_exp_sub_one_le (θ : ℝ) :
    ‖(2 : ℂ) * Complex.exp ((θ : ℂ) * I) - 1‖ ≤ Real.exp (θ ^ 2) := by
  have hsq : ‖(2 : ℂ) * Complex.exp ((θ : ℂ) * I) - 1‖ ^ 2 ≤ (Real.exp (θ ^ 2)) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero, add_zero]
    have hsc := Real.sin_sq_add_cos_sq θ
    have hcos_id : (2 * Real.cos θ - 1) * (2 * Real.cos θ - 1) + 2 * Real.sin θ * (2 * Real.sin θ) =
        1 + 4 * (1 - Real.cos θ) := by linear_combination 4 * hsc
    rw [hcos_id]
    have h1cos : 1 - Real.cos θ ≤ θ ^ 2 / 2 := by
      have hhalf : 1 - Real.cos θ = 2 * (Real.sin (θ / 2)) ^ 2 := by
        have h2 := Real.cos_two_mul' (θ / 2)
        have hsc2 := Real.sin_sq_add_cos_sq (θ / 2)
        rw [show 2 * (θ / 2) = θ by ring] at h2
        linarith
      have hsin_le : |Real.sin (θ / 2)| ≤ |θ / 2| := by
        simpa [Real.sin_zero] using Real.abs_sin_sub_sin_le (θ / 2) 0
      have hsin_sq : (Real.sin (θ / 2)) ^ 2 ≤ (θ / 2) ^ 2 := by
        rw [← sq_abs (Real.sin (θ / 2)), ← sq_abs (θ / 2)]
        exact pow_le_pow_left₀ (abs_nonneg _) hsin_le 2
      linarith [show 2 * (θ / 2) ^ 2 = θ ^ 2 / 2 by ring]
    have hexp1 : 1 + θ ^ 2 ≤ Real.exp (θ ^ 2) := by linarith [Real.add_one_le_exp (θ ^ 2)]
    have hexp_sq : (1 + θ ^ 2) ^ 2 ≤ (Real.exp (θ ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hexp1 2
    nlinarith [sq_nonneg (θ ^ 2)]
  nlinarith [norm_nonneg ((2 : ℂ) * Complex.exp ((θ : ℂ) * I) - 1), Real.exp_pos (θ ^ 2)]

private lemma choose_le_pow_nat (N l : ℕ) : Nat.choose N l ≤ N ^ l :=
  (Nat.choose_le_descFactorial N l).trans (Nat.descFactorial_le_pow N l)

set_option maxHeartbeats 1200000 in
private lemma chase_upper_H1 : OMA.R_Green92_green_92_variants_chase_upper_R1.H1 := by
  obtain ⟨C_arc, hC_arc, harc⟩ := arclowerbound
  set C_final : ℝ := 200 * C_arc + 100
  refine ⟨C_final, by positivity, ?_⟩
  -- Define N(n) = (2 * s(n) - 1) + n where s(n) = ⌈(2 * n)^(1/5)⌉₊
  let sFun : ℕ → ℕ := fun n => ⌈(2 * (n : ℝ)) ^ (1 / 5 : ℝ)⌉₊
  let NFun : ℕ → ℕ := fun n => (2 * sFun n - 1) + n
  have hNFun_top : Tendsto NFun atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_left n (2 * sFun n - 1)) tendsto_id
  have hn15_top : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 5 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp tendsto_natCast_atTop_atTop
  have hlog_top : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog_div := (log_pow_div_rpow_tendsto_zero 1 (by norm_num : (0 : ℝ) < 1 / 5)).eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  filter_upwards [hNFun_top.eventually harc, hn15_top.eventually_ge_atTop 10,
    hlog_top.eventually_ge_atTop 10, hlog_div, eventually_ge_atTop 10000] with
      n hN_arc hn15 hlog10 hlog_small hn10000
  set m : ℕ := ⌈Real.exp (C_final * (n : ℝ) ^ (1 / 5 : ℝ) * Real.log (n : ℝ) ^ 5)⌉₊
  set s : ℕ := sFun n
  set l : ℕ := 2 * s
  set L : ℕ := 2 * s - 1
  set N : ℕ := L + n
  have hn_pos : (0 : ℝ) < n := by positivity
  have h2_15_le : (2 : ℝ) ^ (1 / 5 : ℝ) ≤ 3 / 2 := by
    have hpow : ((2 : ℝ) ^ (1 / 5 : ℝ)) ^ (5 : ℕ) ≤ (3 / 2 : ℝ) ^ (5 : ℕ) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (1 / 5 : ℝ)), ← Real.rpow_mul (by norm_num)]
      norm_num
    by_contra hgt; push Not at hgt
    have := pow_lt_pow_left₀ hgt (by norm_num) (by norm_num : 5 ≠ 0)
    linarith
  have hs_lo_2n : (2 * (n : ℝ)) ^ (1 / 5 : ℝ) ≤ (s : ℝ) := Nat.le_ceil _
  have hs_hi_2n : (s : ℝ) < (2 * (n : ℝ)) ^ (1 / 5 : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
  have h2n15 : (2 * (n : ℝ)) ^ (1 / 5 : ℝ) = (2 : ℝ) ^ (1 / 5 : ℝ) * (n : ℝ) ^ (1 / 5 : ℝ) :=
    Real.mul_rpow (by norm_num) hn_pos.le
  have hs_le_2n15 : (s : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 5 : ℝ) := by
    rw [h2n15] at hs_hi_2n
    have h1 : (2 : ℝ) ^ (1 / 5 : ℝ) * (n : ℝ) ^ (1 / 5 : ℝ) ≤ (3 / 2 : ℝ) * (n : ℝ) ^ (1 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_right h2_15_le (by positivity)
    linarith
  have hs_ge2 : 2 ≤ s := by
    have h1 : (2 : ℝ) ≤ (s : ℝ) := by
      have : (n : ℝ) ^ (1 / 5 : ℝ) ≤ (2 * (n : ℝ)) ^ (1 / 5 : ℝ) :=
        Real.rpow_le_rpow hn_pos.le (by linarith) (by norm_num)
      linarith
    exact_mod_cast h1
  have hl1 : 1 ≤ l := by omega
  have hN_ge_n : n ≤ N := Nat.le_add_left n L
  have hN_le_2n : N ≤ 2 * n := by
    have h45 : (4 : ℝ) ≤ (n : ℝ) ^ (4 / 5 : ℝ) := by
      have := pow_le_pow_left₀ (by norm_num) hn15 4
      rw [← Real.rpow_natCast ((n : ℝ) ^ (1 / 5 : ℝ)), ← Real.rpow_mul hn_pos.le] at this
      norm_num at this; linarith
    have hprod : (n : ℝ) ^ (1 / 5 : ℝ) * (n : ℝ) ^ (4 / 5 : ℝ) = (n : ℝ) := by
      rw [← Real.rpow_add hn_pos]; norm_num
    have h4s : (2 * s : ℝ) ≤ (n : ℝ) := by
      have : 4 * (n : ℝ) ^ (1 / 5 : ℝ) ≤ (n : ℝ) := by nlinarith only [h45, hprod, hn15]
      linarith
    have : 2 * s ≤ n := by exact_mod_cast h4s
    omega
  have hN_pos : (0 : ℝ) < N := by positivity
  have hs_lo_N : (N : ℝ) ^ (1 / 5 : ℝ) ≤ (s : ℝ) := by
    have h1 : (N : ℝ) ^ (1 / 5 : ℝ) ≤ (2 * (n : ℝ)) ^ (1 / 5 : ℝ) :=
      Real.rpow_le_rpow hN_pos.le (by exact_mod_cast hN_le_2n) (by norm_num)
    linarith
  have hs_hi_N : (s : ℝ) ≤ 2 * (N : ℝ) ^ (1 / 5 : ℝ) := by
    have h1 : (n : ℝ) ^ (1 / 5 : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ) :=
      Real.rpow_le_rpow hn_pos.le (by exact_mod_cast hN_ge_n) (by norm_num)
    linarith
  have hN15_le : (N : ℝ) ^ (1 / 5 : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 5 : ℝ) := by
    have h1 : (N : ℝ) ^ (1 / 5 : ℝ) ≤ (2 * (n : ℝ)) ^ (1 / 5 : ℝ) :=
      Real.rpow_le_rpow hN_pos.le (by exact_mod_cast hN_le_2n) (by norm_num)
    rw [h2n15] at h1
    have h2 : (2 : ℝ) ^ (1 / 5 : ℝ) * (n : ℝ) ^ (1 / 5 : ℝ) ≤ (3 / 2 : ℝ) * (n : ℝ) ^ (1 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_right h2_15_le (by positivity)
    linarith
  have hlogN_le : Real.log (N : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have h1 : Real.log (N : ℝ) ≤ Real.log (2 * (n : ℝ)) :=
      Real.log_le_log hN_pos (by exact_mod_cast hN_le_2n)
    rw [Real.log_mul (by norm_num) hn_pos.ne'] at h1
    have hlog2 : Real.log 2 ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ n by omega))
    linarith
  have hNE_le : (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log (N : ℝ)) ^ 5 ≤
      64 * (n : ℝ) ^ (1 / 5 : ℝ) * (Real.log (n : ℝ)) ^ 5 := by
    have hlog5 : (Real.log (N : ℝ)) ^ 5 ≤ 32 * (Real.log (n : ℝ)) ^ 5 := by
      have h1 := pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) hlogN_le 5
      linarith [show (2 * Real.log (n : ℝ)) ^ 5 = 32 * (Real.log (n : ℝ)) ^ 5 by ring]
    have hmul := mul_le_mul hN15_le hlog5 (by positivity) (by positivity)
    linarith [show 2 * (n : ℝ) ^ (1 / 5 : ℝ) * (32 * (Real.log (n : ℝ)) ^ 5) =
      64 * (n : ℝ) ^ (1 / 5 : ℝ) * (Real.log (n : ℝ)) ^ 5 by ring]
  -- Define amplitude bound B and separation threshold Δ
  set B : ℝ := (2 : ℝ) ^ l * (N : ℝ) ^ l * Real.exp ((N : ℝ) ^ (1 / 5 : ℝ))
  set Δ : ℝ := (1 / 2 : ℝ) * Real.exp (-C_arc * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log (N : ℝ)) ^ 5)
  have hB_pos : 0 < B := by positivity
  have hΔ_pos : 0 < Δ := by positivity
  -- Define the predicate for a good real statistic on an unordered pair P
  let goodStat (P : Finset (Fin n → Bool)) (h : List Bool → ℝ) : Prop :=
    (∀ U : List Bool, U.length ≤ n → |h U| ≤ B) ∧
    ∀ a ∈ P, ∀ b ∈ P, a ≠ b →
      Δ ≤ |((2 : ℝ) ^ n)⁻¹ * (∑ S : Finset (Fin n), h (Green92.trace a S)) -
            ((2 : ℝ) ^ n)⁻¹ * (∑ S : Finset (Fin n), h (Green92.trace b S))|
  -- Prove existence of a goodStat for every distinct pair {x, y}
  have hex_good : ∀ x y : Fin n → Bool, x ≠ y → ∃ h : List Bool → ℝ, goodStat ({x, y} : Finset (Fin n → Bool)) h := by
    intro x y hxy
    let x' : Fin N → Bool := padString L x
    let y' : Fin N → Bool := padString L y
    have hx'y' : x' ≠ y' := fun h => hxy (padString_inj L h)
    have hpref : ∀ i : Fin N, i.1 < 2 * s - 1 → x' i = y' i := fun i hi => by
      simp only [x', y', padString_prefix L x i hi, padString_prefix L y i hi]
    obtain ⟨w, σ, d, c, hd1, hds, hc, hpoly_eq⟩ := exists_sparse_poly_for_strings hs_ge2 x' y' hx'y' hpref
    obtain ⟨θ, hθ_mem, hθ_lb⟩ := hN_arc s σ d c hs_lo_N hs_hi_N hd1 hds hc
    set z₀ : ℂ := Complex.exp ((θ : ℂ) * I)
    have hz₀_norm : ‖z₀‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
    -- Complex padded statistic
    let statC : List Bool → ℂ := fun U =>
      ((2 : ℂ) ^ L)⁻¹ * ∑ S₁ : Finset (Fin L), subseqStat hl1 w z₀ (List.replicate S₁.card false ++ U)
    -- Bound ‖statC U‖ ≤ B for U.length ≤ n
    have hstatC_bd : ∀ U : List Bool, U.length ≤ n → ‖statC U‖ ≤ B := by
      intro U hU
      have h2z_le : max 1 ‖2 * z₀ - 1‖ ≤ Real.exp ((N : ℝ) ^ (-(4 / 5 : ℝ))) := by
        apply max_le
        · exact Real.one_le_exp (by positivity)
        · refine le_trans (norm_two_exp_sub_one_le θ) (Real.exp_le_exp.mpr ?_)
          have hθ_abs : |θ| ≤ (N : ℝ) ^ (-(2 / 5 : ℝ)) := abs_le.mpr hθ_mem
          have hsq : θ ^ 2 ≤ ((N : ℝ) ^ (-(2 / 5 : ℝ))) ^ (2 : ℕ) := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hθ_abs 2
          rw [← Real.rpow_natCast ((N : ℝ) ^ (-(2 / 5 : ℝ))), ← Real.rpow_mul hN_pos.le] at hsq
          norm_num at hsq; exact hsq
      have hpow_le : (max 1 ‖2 * z₀ - 1‖) ^ N ≤ Real.exp ((N : ℝ) ^ (1 / 5 : ℝ)) := by
        calc (max 1 ‖2 * z₀ - 1‖) ^ N
            ≤ (Real.exp ((N : ℝ) ^ (-(4 / 5 : ℝ)))) ^ N :=
              pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) h2z_le N
          _ = Real.exp ((N : ℝ) * (N : ℝ) ^ (-(4 / 5 : ℝ))) := (Real.exp_nat_mul _ N).symm
          _ = Real.exp ((N : ℝ) ^ (1 / 5 : ℝ)) := by
              congr 1
              calc (N : ℝ) * (N : ℝ) ^ (-(4 / 5 : ℝ))
                  = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(4 / 5 : ℝ)) := by rw [Real.rpow_one]
                _ = (N : ℝ) ^ (1 / 5 : ℝ) := by rw [← Real.rpow_add hN_pos]; norm_num
      have hterm_le : ∀ S₁ : Finset (Fin L),
          ‖subseqStat hl1 w z₀ (List.replicate S₁.card false ++ U)‖ ≤ B := by
        intro S₁
        have hlen : (List.replicate S₁.card false ++ U).length ≤ N := by
          simp only [List.length_append, List.length_replicate]
          have hS1 : S₁.card ≤ L := by simpa using S₁.card_le_univ
          omega
        have h1 := norm_subseqStat_le hl1 w z₀ (List.replicate S₁.card false ++ U) hlen
        have hch : (Nat.choose N l : ℝ) ≤ (N : ℝ) ^ l := by exact_mod_cast choose_le_pow_nat N l
        calc ‖subseqStat hl1 w z₀ (List.replicate S₁.card false ++ U)‖
            ≤ (2 : ℝ) ^ l * (Nat.choose N l : ℝ) * (max 1 ‖2 * z₀ - 1‖) ^ N := h1
          _ ≤ (2 : ℝ) ^ l * (N : ℝ) ^ l * Real.exp ((N : ℝ) ^ (1 / 5 : ℝ)) := by gcongr
      simp only [statC, norm_mul, norm_inv, norm_pow, Complex.norm_ofNat]
      have h2L_pos : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
      calc ((2 : ℝ) ^ L)⁻¹ * ‖∑ S₁ : Finset (Fin L), subseqStat hl1 w z₀ (List.replicate S₁.card false ++ U)‖
          ≤ ((2 : ℝ) ^ L)⁻¹ * ∑ S₁ : Finset (Fin L), ‖subseqStat hl1 w z₀ (List.replicate S₁.card false ++ U)‖ :=
            mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
        _ ≤ ((2 : ℝ) ^ L)⁻¹ * ∑ _S₁ : Finset (Fin L), B :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun S₁ _ => hterm_le S₁) (by positivity)
        _ = ((2 : ℝ) ^ L)⁻¹ * ((2 : ℝ) ^ L * B) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul]
            push_cast; rfl
        _ = B := by field_simp [h2L_pos.ne']
    -- Exact expectation of statC equals ∑ k ∈ posSet (padString L u) w, z₀ ^ k
    have hexp_statC : ∀ u : Fin n → Bool,
        ((2 : ℂ) ^ n)⁻¹ * ∑ S₂ : Finset (Fin n), statC (Green92.trace u S₂) =
          ∑ k ∈ posSet (padString L u) w, z₀ ^ k := by
      intro u
      have h1 : ((2 : ℂ) ^ n)⁻¹ * ∑ S₂ : Finset (Fin n), statC (Green92.trace u S₂) =
          ((2 : ℂ) ^ (L + n))⁻¹ *
            ∑ S : Finset (Fin (L + n)), subseqStat hl1 w z₀ (Green92.trace (padString L u) S) := by
        simp only [statC, ← Finset.mul_sum]
        rw [← mul_assoc, ← mul_inv, ← pow_add, add_comm n L]
        congr 1
        rw [Finset.sum_comm]
        rw [← Fintype.sum_prod_type']
        refine Fintype.sum_equiv (splitFinset L n) _ _ fun p => ?_
        rw [trace_padString L u p.1 p.2]
      rw [h1, expectation_subseqStat hl1 (padString L u) w z₀]
      simp only [posSet, Finset.sum_filter, l]
    -- Complex separation ≥ exp (-C_arc * N^(1/5) * (log N)^5)
    have hsepC : Real.exp (-C_arc * (N : ℝ) ^ (1 / 5 : ℝ) * (Real.log (N : ℝ)) ^ 5) ≤
        ‖((2 : ℂ) ^ n)⁻¹ * (∑ S₂ : Finset (Fin n), statC (Green92.trace x S₂)) -
          ((2 : ℂ) ^ n)⁻¹ * (∑ S₂ : Finset (Fin n), statC (Green92.trace y S₂))‖ := by
      rw [hexp_statC x, hexp_statC y, hpoly_eq z₀ hz₀_norm]
      exact hθ_lb
    set diffC : ℂ := ((2 : ℂ) ^ n)⁻¹ * (∑ S₂ : Finset (Fin n), statC (Green92.trace x S₂)) -
      ((2 : ℂ) ^ n)⁻¹ * (∑ S₂ : Finset (Fin n), statC (Green92.trace y S₂))
    have hre_im : ‖diffC‖ ≤ |diffC.re| + |diffC.im| := by
      have hsq : ‖diffC‖ ^ 2 ≤ (|diffC.re| + |diffC.im|) ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        have h1 : diffC.re * diffC.re = |diffC.re| ^ 2 := by rw [sq_abs]; ring
        have h2 : diffC.im * diffC.im = |diffC.im| ^ 2 := by rw [sq_abs]; ring
        nlinarith [abs_nonneg diffC.re, abs_nonneg diffC.im]
      nlinarith [norm_nonneg diffC, abs_nonneg diffC.re, abs_nonneg diffC.im]
    have hre_eq : diffC.re =
        ((2 : ℝ) ^ n)⁻¹ * (∑ S : Finset (Fin n), (statC (Green92.trace x S)).re) -
        ((2 : ℝ) ^ n)⁻¹ * (∑ S : Finset (Fin n), (statC (Green92.trace y S)).re) := by
      have hcast : ((2 : ℂ) ^ n)⁻¹ = ((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
      simp only [diffC, hcast, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, Complex.re_sum]
    have him_eq : diffC.im =
        ((2 : ℝ) ^ n)⁻¹ * (∑ S : Finset (Fin n), (statC (Green92.trace x S)).im) -
        ((2 : ℝ) ^ n)⁻¹ * (∑ S : Finset (Fin n), (statC (Green92.trace y S)).im) := by
      have hcast : ((2 : ℂ) ^ n)⁻¹ = ((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
      simp only [diffC, hcast, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, Complex.im_sum]
    by_cases hre_big : Δ ≤ |diffC.re|
    · refine ⟨fun U => (statC U).re, fun U hU => le_trans (Complex.abs_re_le_norm _) (hstatC_bd U hU), ?_⟩
      intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · rwa [← hre_eq]
      · rw [abs_sub_comm, ← hre_eq]; exact hre_big
      · exact absurd rfl hab
    · have him_big : Δ ≤ |diffC.im| := by simp only [Δ] at hre_big ⊢; linarith only [hre_big, hsepC, hre_im]
      refine ⟨fun U => (statC U).im, fun U hU => le_trans (Complex.abs_im_le_norm _) (hstatC_bd U hU), ?_⟩
      intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · rwa [← him_eq]
      · rw [abs_sub_comm, ← him_eq]; exact him_big
      · exact absurd rfl hab
  -- Symmetric pairwise statistic depending only on the unordered pair {x, y}
  let pairStat (x y : Fin n → Bool) : List Bool → ℝ :=
    if hex : ∃ h, goodStat ({x, y} : Finset (Fin n → Bool)) h then hex.choose else fun _ => 0
  have hpairStat_symm : ∀ x y : Fin n → Bool, pairStat x y = pairStat y x := by
    intro x y
    simp only [pairStat, Finset.pair_comm x y]
  let meanVal (x y z : Fin n → Bool) : ℝ :=
    ((2 : ℝ) ^ n)⁻¹ * ∑ S : Finset (Fin n), pairStat x y (Green92.trace z S)
  have hmeanVal_symm : ∀ x y z : Fin n → Bool, meanVal y x z = meanVal x y z := by
    intro x y z; simp only [meanVal, hpairStat_symm x y]
  let D : (Fin n → Bool) → (Fin n → Bool) → (Fin m → List Bool) → Prop :=
    fun x y o =>
      |((m : ℝ)⁻¹ * ∑ j : Fin m, pairStat x y (o j)) - meanVal x y x| <
      |((m : ℝ)⁻¹ * ∑ j : Fin m, pairStat x y (o j)) - meanVal x y y|
  refine ⟨D, ?_, ?_⟩
  · -- Antisymmetry of D
    intro x y o _ hDxy hDyx
    simp only [D, hpairStat_symm y x, hmeanVal_symm x y] at hDxy hDyx
    linarith
  · -- Error bound via Hoeffding's inequality
    intro x y hxy
    have hex : ∃ h, goodStat ({x, y} : Finset (Fin n → Bool)) h := hex_good x y hxy
    have hgs : goodStat ({x, y} : Finset (Fin n → Bool)) (pairStat x y) := by
      simp only [pairStat, dif_pos hex]
      exact hex.choose_spec
    have hbd_h : ∀ S : Finset (Fin n), |pairStat x y (Green92.trace x S)| ≤ B := by
      intro S
      apply hgs.1
      rw [trace_length]
      simpa using S.card_le_univ
    have hsep : Δ ≤ |meanVal x y x - meanVal x y y| :=
      hgs.2 x (by simp) y (by simp) hxy
    have hmean_bd : |meanVal x y x| ≤ B := by
      simp only [meanVal]
      have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
      rw [abs_mul, abs_of_pos (inv_pos.mpr h2n)]
      calc ((2 : ℝ) ^ n)⁻¹ * |∑ S : Finset (Fin n), pairStat x y (Green92.trace x S)|
          ≤ ((2 : ℝ) ^ n)⁻¹ * ∑ S : Finset (Fin n), |pairStat x y (Green92.trace x S)| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
        _ ≤ ((2 : ℝ) ^ n)⁻¹ * ∑ _S : Finset (Fin n), B :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun S _ => hbd_h S) (by positivity)
        _ = ((2 : ℝ) ^ n)⁻¹ * ((2 : ℝ) ^ n * B) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul]
            push_cast; rfl
        _ = B := by field_simp [h2n.ne']
    let Y : Finset (Fin n) → ℝ := fun S => pairStat x y (Green92.trace x S) - meanVal x y x
    have hY_mean : ∑ S : Finset (Fin n), Y S = 0 := by
      simp only [Y, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul, meanVal]
      have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
      push_cast
      field_simp [h2n]
      ring
    have hY_bd : ∀ S : Finset (Fin n), |Y S| ≤ 2 * B := fun S => by
      simp only [Y]
      exact le_trans (abs_sub _ _) (by linarith [hbd_h S, hmean_bd])
    have hm_pos : (0 : ℝ) < (m : ℝ) := by
      have : Real.exp (C_final * (n : ℝ) ^ (1 / 5 : ℝ) * Real.log (n : ℝ) ^ 5) ≤ (m : ℝ) := Nat.le_ceil _
      linarith [Real.exp_pos (C_final * (n : ℝ) ^ (1 / 5 : ℝ) * Real.log (n : ℝ) ^ 5)]
    -- Any failure S implies m * (Δ/2) ≤ |∑ j, Y (S j)|
    have hsub : (univ.filter fun S : Fin m → Finset (Fin n) =>
        ¬ D x y (fun j => Green92.trace x (S j))) ⊆
        (univ.filter fun S : Fin m → Finset (Fin n) =>
          (m : ℝ) * (Δ / 2) ≤ |∑ j : Fin m, Y (S j)|) := by
      intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, D, not_lt] at hS ⊢
      set avg : ℝ := (m : ℝ)⁻¹ * ∑ j : Fin m, pairStat x y (Green92.trace x (S j))
      have htri : |meanVal x y x - meanVal x y y| ≤ |avg - meanVal x y x| + |avg - meanVal x y y| := by
        have h1 := abs_sub_le (meanVal x y x) avg (meanVal x y y)
        rw [abs_sub_comm (meanVal x y x) avg] at h1
        exact h1
      have havg_ge : Δ / 2 ≤ |avg - meanVal x y x| := by linarith
      have hsum_eq : ∑ j : Fin m, Y (S j) = (m : ℝ) * (avg - meanVal x y x) := by
        simp only [Y, avg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, mul_sub]
        field_simp [hm_pos.ne']
      rw [hsum_eq, abs_mul, abs_of_pos hm_pos]
      exact mul_le_mul_of_nonneg_left havg_ge hm_pos.le
    have hhoeff := hoeffding_two_sided m Y (2 * B) (Δ / 2) (by positivity) (by positivity) hY_mean hY_bd
    have hcard_le : ((univ.filter fun S : Fin m → Finset (Fin n) =>
        ¬ D x y (fun j => Green92.trace x (S j))).card : ℝ) ≤
        2 * (Fintype.card (Fin m → Finset (Fin n)) : ℝ) *
          Real.exp (-(m : ℝ) * (Δ / 2) ^ 2 / (2 * (2 * B) ^ 2)) :=
      le_trans (by exact_mod_cast Finset.card_le_card hsub) hhoeff
    -- Show 2 * exp (-m * (Δ/2)^2 / (2 * (2*B)^2)) * (10 * 2^n) ≤ 1
    have hexp_bound : 2 * Real.exp (-(m : ℝ) * (Δ / 2) ^ 2 / (2 * (2 * B) ^ 2)) * (10 * (2 : ℝ) ^ n) ≤ 1 := by
      have h20 : 20 * (2 : ℝ) ^ n ≤ Real.exp ((n : ℝ) + 4) := by
        have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        have h2np : (2 : ℝ) ^ n ≤ Real.exp (n : ℝ) := by
          calc (2 : ℝ) ^ n ≤ (Real.exp 1) ^ n := pow_le_pow_left₀ (by norm_num) h2e n
            _ = Real.exp (n : ℝ) := by rw [← Real.exp_nat_mul]; simp
        have h20e : (20 : ℝ) ≤ Real.exp 4 := by
          have := Real.exp_one_gt_d9
          have h4 : (2.718 : ℝ) ^ 4 ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
          rw [← Real.exp_nat_mul] at h4; norm_num at h4; linarith
        rw [Real.exp_add]
        have hmul := mul_le_mul h20e h2np (by positivity) (Real.exp_pos _).le
        linarith
      -- Lower bound (m : ℝ) * (Δ/2)^2 / (2 * (2*B)^2) ≥ n + 4
      have hB_le : B ≤ Real.exp (15 * (n : ℝ) ^ (1 / 5 : ℝ) * (Real.log (n : ℝ)) ^ 5) := by
        have hl_le : (l : ℝ) ≤ 4 * (n : ℝ) ^ (1 / 5 : ℝ) := by
          have : (l : ℝ) = 2 * (s : ℝ) := by simp only [l]; push_cast; ring
          linarith
        have h2N_le : (2 * (N : ℝ)) ≤ (n : ℝ) ^ 2 := by
          have : (N : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hN_le_2n
          have : (10000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn10000
          nlinarith
        have h2Nl : (2 : ℝ) ^ l * (N : ℝ) ^ l ≤ Real.exp (8 * (n : ℝ) ^ (1 / 5 : ℝ) * Real.log (n : ℝ)) := by
          rw [← mul_pow]
          calc (2 * (N : ℝ)) ^ l ≤ ((n : ℝ) ^ 2) ^ l := pow_le_pow_left₀ (by positivity) h2N_le l
            _ = Real.exp ((l : ℝ) * (2 * Real.log (n : ℝ))) := by
                rw [show (l : ℝ) * (2 * Real.log (n : ℝ)) = ((l : ℕ) : ℝ) * Real.log ((n : ℝ) ^ 2) by
                  rw [Real.log_pow]; push_cast; ring,
                  Real.exp_nat_mul, Real.exp_log (by positivity)]
            _ ≤ Real.exp (8 * (n : ℝ) ^ (1 / 5 : ℝ) * Real.log (n : ℝ)) := by
                apply Real.exp_le_exp.mpr
                have hlog_nn : 0 ≤ Real.log (n : ℝ) := by linarith
                nlinarith
        have hlog4_ge : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ 4 := by
          have := pow_le_pow_left₀ (by norm_num) (show (1 : ℝ) ≤ Real.log (n : ℝ) by linarith) 4
          simpa using this
        have hlog5_ge : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ 5 := by
          have := pow_le_pow_left₀ (by norm_num) (show (1 : ℝ) ≤ Real.log (n : ℝ) by linarith) 5
          simpa using this
        calc B = ((2 : ℝ) ^ l * (N : ℝ) ^ l) * Real.exp ((N : ℝ) ^ (1 / 5 : ℝ)) := rfl
          _ ≤ Real.exp (8 * (n : ℝ) ^ (1 / 5 : ℝ) * Real.log (n : ℝ)) * Real.exp (2 * (n : ℝ) ^ (1 / 5 : ℝ)) :=
              mul_le_mul h2Nl (Real.exp_le_exp.mpr hN15_le) (Real.exp_pos _).le (Real.exp_pos _).le
          _ = Real.exp (8 * (n : ℝ) ^ (1 / 5 : ℝ) * Real.log (n : ℝ) + 2 * (n : ℝ) ^ (1 / 5 : ℝ)) :=
              (Real.exp_add _ _).symm
          _ ≤ Real.exp (15 * (n : ℝ) ^ (1 / 5 : ℝ) * (Real.log (n : ℝ)) ^ 5) := by
              apply Real.exp_le_exp.mpr
              have h1 : (n : ℝ) ^ (1 / 5 : ℝ) * Real.log (n : ℝ) ≤
                  (n : ℝ) ^ (1 / 5 : ℝ) * (Real.log (n : ℝ)) ^ 5 := by
                have hlog_nn : 0 ≤ Real.log (n : ℝ) := by linarith
                have : Real.log (n : ℝ) ≤ (Real.log (n : ℝ)) ^ 5 := by
                  calc Real.log (n : ℝ) = Real.log (n : ℝ) * 1 := (mul_one _).symm
                    _ ≤ Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ 4 := mul_le_mul_of_nonneg_left hlog4_ge hlog_nn
                    _ = (Real.log (n : ℝ)) ^ 5 := by ring
                exact mul_le_mul_of_nonneg_left this (by positivity)
              have h2 : (n : ℝ) ^ (1 / 5 : ℝ) ≤ (n : ℝ) ^ (1 / 5 : ℝ) * (Real.log (n : ℝ)) ^ 5 := by
                nlinarith [show (0 : ℝ) < (n : ℝ) ^ (1 / 5 : ℝ) by positivity]
              linarith
      set En : ℝ := (n : ℝ) ^ (1 / 5 : ℝ) * (Real.log (n : ℝ)) ^ 5
      have hEn_ge : (10 : ℝ) ≤ En := by
        have hlog5 : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ 5 := by
          have := pow_le_pow_left₀ (by norm_num) (show (1 : ℝ) ≤ Real.log (n : ℝ) by linarith) 5
          simpa using this
        nlinarith
      have hratio_lb : Real.exp (10 * En) ≤ (m : ℝ) * (Δ / 2) ^ 2 / (2 * (2 * B) ^ 2) := by
        have hΔ_lb : (1 / 2 : ℝ) * Real.exp (-64 * C_arc * En) ≤ Δ := by
          simp only [Δ]
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
          have : -64 * C_arc * En ≤ -C_arc * ((N : ℝ) ^ (1 / 5 : ℝ) * (Real.log (N : ℝ)) ^ 5) := by
            simp only [En]; nlinarith [hNE_le, hC_arc]
          linarith
        have hnum_lb : Real.exp ((200 * C_arc + 100 - 128 * C_arc) * En) / 16 ≤ (m : ℝ) * (Δ / 2) ^ 2 := by
          have hm_ge : Real.exp (C_final * En) ≤ (m : ℝ) := by
            rw [show C_final * En = C_final * (n : ℝ) ^ (1 / 5 : ℝ) * Real.log (n : ℝ) ^ 5 by
              simp only [En]; ring]
            exact Nat.le_ceil _
          have hΔ2_lb : (1 / 16 : ℝ) * Real.exp (-128 * C_arc * En) ≤ (Δ / 2) ^ 2 := by
            have h1 : (1 / 4 : ℝ) * Real.exp (-64 * C_arc * En) ≤ Δ / 2 := by linarith
            have h2 := pow_le_pow_left₀ (by positivity) h1 2
            rw [mul_pow, ← Real.exp_nat_mul] at h2
            norm_num at h2
            rw [show -(2 * (64 * C_arc * En)) = -128 * C_arc * En by ring] at h2
            exact h2
          have hmul := mul_le_mul hm_ge hΔ2_lb (by positivity) hm_pos.le
          calc Real.exp ((200 * C_arc + 100 - 128 * C_arc) * En) / 16
              = Real.exp (C_final * En) * ((1 / 16 : ℝ) * Real.exp (-128 * C_arc * En)) := by
                  simp only [C_final]
                  rw [show Real.exp ((200 * C_arc + 100) * En) * ((1 / 16 : ℝ) * Real.exp (-128 * C_arc * En)) =
                    (Real.exp ((200 * C_arc + 100) * En) * Real.exp (-128 * C_arc * En)) / 16 by ring,
                    ← Real.exp_add]
                  congr 2; ring
            _ ≤ (m : ℝ) * (Δ / 2) ^ 2 := hmul
        have hden_ub : 2 * (2 * B) ^ 2 ≤ 8 * Real.exp (30 * En) := by
          have hB2 : B ^ 2 ≤ Real.exp (30 * En) := by
            have h1 := pow_le_pow_left₀ hB_pos.le hB_le 2
            rw [← Real.exp_nat_mul] at h1
            simpa only [En, show (2 : ℕ) * (15 * (n : ℝ) ^ (1 / 5 : ℝ) * Real.log (n : ℝ) ^ 5) = 30 * En by
              simp only [En]; push_cast; ring] using h1
          linarith
        have h128 : (128 : ℝ) ≤ Real.exp (60 * En) := by
          have h1 : (128 : ℝ) ≤ Real.exp 5 := by
            have := Real.exp_one_gt_d9
            have h5 : (2.718 : ℝ) ^ 5 ≤ (Real.exp 1) ^ 5 := pow_le_pow_left₀ (by norm_num) (by linarith) 5
            rw [← Real.exp_nat_mul] at h5; norm_num at h5; linarith
          exact le_trans h1 (Real.exp_le_exp.mpr (by linarith))
        calc Real.exp (10 * En)
            ≤ Real.exp ((72 * C_arc + 100 - 30) * En) / 128 := by
                rw [le_div_iff₀ (by norm_num)]
                calc Real.exp (10 * En) * 128 ≤ Real.exp (10 * En) * Real.exp (60 * En) :=
                      mul_le_mul_of_nonneg_left h128 (Real.exp_pos _).le
                  _ = Real.exp (70 * En) := by rw [← Real.exp_add]; congr 1; ring
                  _ ≤ Real.exp ((72 * C_arc + 100 - 30) * En) :=
                      Real.exp_le_exp.mpr (by nlinarith)
          _ = (Real.exp ((200 * C_arc + 100 - 128 * C_arc) * En) / 16) / (8 * Real.exp (30 * En)) := by
                rw [div_div, show (16 : ℝ) * (8 * Real.exp (30 * En)) = 128 * Real.exp (30 * En) by ring,
                  div_mul_eq_div_div_swap, ← Real.exp_sub]
                congr 2; ring
          _ ≤ ((m : ℝ) * (Δ / 2) ^ 2) / (2 * (2 * B) ^ 2) :=
                div_le_div₀ (by positivity) hnum_lb (by positivity) hden_ub
      have hn4_le : (n : ℝ) + 4 ≤ Real.exp (10 * En) := by
        have hlogn_le : Real.log ((n : ℝ) + 4) ≤ 10 * En := by
          have h1 : (n : ℝ) + 4 ≤ (n : ℝ) ^ 2 := by
            have : (10000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn10000
            nlinarith
          have h2 : Real.log ((n : ℝ) + 4) ≤ 2 * Real.log (n : ℝ) := by
            calc Real.log ((n : ℝ) + 4) ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log (by positivity) h1
              _ = 2 * Real.log (n : ℝ) := by rw [Real.log_pow]; push_cast; ring
          have hlog4_ge : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ 4 := by
            have := pow_le_pow_left₀ (by norm_num) (show (1 : ℝ) ≤ Real.log (n : ℝ) by linarith) 4
            simpa using this
          have h3 : Real.log (n : ℝ) ≤ (Real.log (n : ℝ)) ^ 5 := by
            calc Real.log (n : ℝ) = Real.log (n : ℝ) * 1 := (mul_one _).symm
              _ ≤ Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ 4 := mul_le_mul_of_nonneg_left hlog4_ge (by linarith)
              _ = (Real.log (n : ℝ)) ^ 5 := by ring
          simp only [En]
          nlinarith
        calc (n : ℝ) + 4 = Real.exp (Real.log ((n : ℝ) + 4)) := (Real.exp_log (by positivity)).symm
          _ ≤ Real.exp (10 * En) := Real.exp_le_exp.mpr hlogn_le
      have hexp_ge : (n : ℝ) + 4 ≤ (m : ℝ) * (Δ / 2) ^ 2 / (2 * (2 * B) ^ 2) := le_trans hn4_le hratio_lb
      calc 2 * Real.exp (-(m : ℝ) * (Δ / 2) ^ 2 / (2 * (2 * B) ^ 2)) * (10 * (2 : ℝ) ^ n)
          = (20 * (2 : ℝ) ^ n) * Real.exp (-((m : ℝ) * (Δ / 2) ^ 2 / (2 * (2 * B) ^ 2))) := by
              rw [show -(m : ℝ) * (Δ / 2) ^ 2 / (2 * (2 * B) ^ 2) =
                -((m : ℝ) * (Δ / 2) ^ 2 / (2 * (2 * B) ^ 2)) by ring]; ring
        _ ≤ Real.exp ((n : ℝ) + 4) * Real.exp (-((n : ℝ) + 4)) :=
              mul_le_mul h20 (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    -- Convert real bound to ℕ division via Nat.le_div_iff_mul_le
    rw [Nat.le_div_iff_mul_le (by positivity : 0 < 10 * 2 ^ n)]
    have hreal_mul : ((univ.filter fun S : Fin m → Finset (Fin n) =>
        ¬ D x y (fun j => Green92.trace x (S j))).card : ℝ) * (10 * (2 : ℝ) ^ n) ≤
        (Fintype.card (Fin m → Finset (Fin n)) : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_right hcard_le (show (0 : ℝ) ≤ 10 * (2 : ℝ) ^ n by positivity)
      calc _ ≤ (2 * (Fintype.card (Fin m → Finset (Fin n)) : ℝ) *
              Real.exp (-(m : ℝ) * (Δ / 2) ^ 2 / (2 * (2 * B) ^ 2))) * (10 * (2 : ℝ) ^ n) := h1
        _ = (Fintype.card (Fin m → Finset (Fin n)) : ℝ) *
              (2 * Real.exp (-(m : ℝ) * (Δ / 2) ^ 2 / (2 * (2 * B) ^ 2)) * (10 * (2 : ℝ) ^ n)) := by ring
        _ ≤ (Fintype.card (Fin m → Finset (Fin n)) : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left hexp_bound (Nat.cast_nonneg _)
        _ = (Fintype.card (Fin m → Finset (Fin n)) : ℝ) := mul_one _
    exact_mod_cast hreal_mul

end Green92ChaseH1

theorem OMA.solution : OMA.R_Green92_green_92_variants_chase_upper_R1.H1 :=
  Green92ChaseH1.chase_upper_H1
