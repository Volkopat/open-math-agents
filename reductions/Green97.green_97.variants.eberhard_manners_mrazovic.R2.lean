import FormalConjectures.GreensOpenProblems.«97»
import Mathlib.Analysis.Fourier.ZMod

-- Reduction Green97.green_97.variants.eberhard_manners_mrazovic.R2
-- Credit: @wtho704
-- Eberhard–Manners–Mrazović, arXiv:1510.05987, Sections 2, 3 and 7.

/-!
# Fourier reduction for additive triples of bijections

The finite Fourier identity reduces the asymptotic to a fixed-cutoff limit
on major arcs and a uniformly small contribution from their complement.
-/

namespace OMA.R_Green97_green_97_variants_eberhard_manners_mrazovic_R2

open Filter Asymptotics
open scoped BigOperators Topology

/-- The fixed-cutoff contribution of frequencies close to a constant vector. -/
def H1 : Prop :=
  let coeff (n : ℕ) [NeZero n] (ξ : Fin n → ZMod n) : ℂ :=
    ∑ π : Fin n ≃ ZMod n, ∏ i, ZMod.stdAddChar (ξ i * π i)
  ∀ M : ℕ, Tendsto (fun n : ℕ ↦
    if hn : n = 0 then 0 else
      letI : NeZero n := ⟨hn⟩
      (∑ ξ : Fin n → ZMod n,
        if ∃ a : ZMod n, (Finset.univ.filter fun i ↦ ξ i ≠ a).card ≤ 2 * M then
          (coeff n ξ ^ 2 * coeff n (-ξ)).re / (n.factorial : ℝ) ^ 3
        else 0) / (n : ℝ))
    (atTop ⊓ principal {n : ℕ | Odd n})
    (𝓝 (∑ j ∈ Finset.range (M + 1), (-(1 / 2) : ℝ) ^ j / (j.factorial : ℝ)))

/-- The complement has arbitrarily small normalized contribution as the cutoff increases. -/
def H2 : Prop :=
  let coeff (n : ℕ) [NeZero n] (ξ : Fin n → ZMod n) : ℂ :=
    ∑ π : Fin n ≃ ZMod n, ∏ i, ZMod.stdAddChar (ξ i * π i)
  ∀ ε > (0 : ℝ), ∃ M₀ : ℕ, ∀ M ≥ M₀,
    ∀ᶠ n : ℕ in atTop ⊓ principal {n : ℕ | Odd n},
      |if hn : n = 0 then 0 else
        letI : NeZero n := ⟨hn⟩
        (∑ ξ : Fin n → ZMod n,
          if ∃ a : ZMod n, (Finset.univ.filter fun i ↦ ξ i ≠ a).card ≤ 2 * M then
            0
          else (coeff n ξ ^ 2 * coeff n (-ξ)).re / (n.factorial : ℝ) ^ 3) / (n : ℝ)| < ε

lemma scalar_orthogonality {n : ℕ} [NeZero n] (t : ZMod n) :
    (∑ a : ZMod n, ZMod.stdAddChar (a * t)) = if t = 0 then (n : ℂ) else 0 := by
  by_cases h : t = 0
  · simp [h, ZMod.card]
  · rw [if_neg h]
    simpa only [AddChar.mulShift_apply, mul_comm _ t] using
      AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar n h)

lemma finite_fourier_count (n : ℕ) [NeZero n] :
    let coeff (ξ : Fin n → ZMod n) : ℂ :=
      ∑ π : Fin n ≃ ZMod n, ∏ i, ZMod.stdAddChar (ξ i * π i)
    (Green97.numAdditiveTriples n : ℂ) * (n : ℂ) ^ n =
      ∑ ξ : Fin n → ZMod n, coeff ξ ^ 2 * coeff (-ξ) := by
  classical
  let E := Fin n ≃ ZMod n
  let phase (ξ x : Fin n → ZMod n) : ℂ := ∏ i, ZMod.stdAddChar (ξ i * x i)
  change _ = ∑ ξ : Fin n → ZMod n, (∑ π : E, phase ξ π) ^ 2 * (∑ π : E, phase (-ξ) π)
  have combine (ξ x y z : Fin n → ZMod n) :
      phase ξ x * phase ξ y * phase (-ξ) z =
        phase ξ (fun i ↦ x i + y i - z i) := by
    dsimp [phase]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [neg_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  have orthogonal (v : Fin n → ZMod n) :
      (∑ ξ : Fin n → ZMod n, phase ξ v) = if v = 0 then (n : ℂ) ^ n else 0 := by
    dsimp [phase]
    rw [← Fintype.prod_sum (fun (i : Fin n) (a : ZMod n) ↦ ZMod.stdAddChar (a * v i))]
    simp_rw [scalar_orthogonality]
    by_cases hv : v = 0
    · simp [hv]
    · have exists_nonzero : ∃ i, v i ≠ 0 := by
        by_contra! h
        exact hv (funext h)
      obtain ⟨i, hi⟩ := exists_nonzero
      rw [if_neg hv]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  have sum_third (a b : E) :
      (∑ c : E, if (fun i ↦ a i + b i - c i) = 0 then (n : ℂ) ^ n else 0) =
        if Function.Bijective (fun i ↦ a i + b i) then (n : ℂ) ^ n else 0 := by
    let f : Fin n → ZMod n := fun i ↦ a i + b i
    have zero_iff (c : E) :
        (fun i ↦ a i + b i - c i) = 0 ↔ (c : Fin n → ZMod n) = f := by
      constructor
      · intro h
        funext i
        exact (sub_eq_zero.mp (congrFun h i)).symm
      · intro h
        funext i
        exact sub_eq_zero.mpr (congrFun h i).symm
    by_cases h : Function.Bijective f
    · let c₀ : E := Equiv.ofBijective f h
      have unique (c : E) : (fun i ↦ a i + b i - c i) = 0 ↔ c = c₀ := by
        rw [zero_iff]
        exact ⟨fun eq ↦ Equiv.ext (congrFun eq), fun eq ↦ by subst c; rfl⟩
      change _ = if Function.Bijective f then _ else _
      rw [if_pos h, Finset.sum_eq_single c₀]
      · rw [if_pos ((unique c₀).mpr rfl)]
      · intro c _ hne
        exact if_neg (fun hz ↦ hne ((unique c).mp hz))
      · simp
    · have none (c : E) : (fun i ↦ a i + b i - c i) ≠ 0 :=
        fun hc ↦ h ((zero_iff c).mp hc ▸ c.bijective)
      change _ = if Function.Bijective f then _ else _
      rw [if_neg h]
      simp only [none, if_false, Finset.sum_const_zero]
  symm
  calc
    _ = ∑ ξ : Fin n → ZMod n, ∑ a : E, ∑ b : E, ∑ c : E,
        phase ξ (fun i ↦ a i + b i - c i) := by
      refine Finset.sum_congr rfl fun ξ _ ↦ ?_
      simp_rw [pow_two, ← combine, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
    _ = ∑ a : E, ∑ b : E, ∑ c : E, ∑ ξ : Fin n → ZMod n,
        phase ξ (fun i ↦ a i + b i - c i) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun b _ ↦ Finset.sum_comm
    _ = ∑ a : E, ∑ b : E, if Function.Bijective (fun i ↦ a i + b i) then
          (n : ℂ) ^ n else 0 := by simp_rw [orthogonal, sum_third]
    _ = (Green97.numAdditiveTriples n : ℂ) * (n : ℂ) ^ n := by
      rw [← Fintype.sum_prod_type' (fun (a b : E) ↦
        if Function.Bijective (fun i ↦ a i + b i) then (n : ℂ) ^ n else 0)]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      unfold Green97.numAdditiveTriples
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma normalized_fourier_count (n : ℕ) [NeZero n] :
    let coeff (ξ : Fin n → ZMod n) : ℂ :=
      ∑ π : Fin n ≃ ZMod n, ∏ i, ZMod.stdAddChar (ξ i * π i)
    (∑ ξ : Fin n → ZMod n, (coeff ξ ^ 2 * coeff (-ξ)).re / (n.factorial : ℝ) ^ 3) /
        (n : ℝ) =
      (Green97.numAdditiveTriples n : ℝ) / ((n.factorial : ℝ) ^ 3 / (n : ℝ) ^ (n - 1)) := by
  have h := congrArg Complex.re (finite_fourier_count n)
  rw [← Nat.cast_pow, ← Nat.cast_mul, Complex.natCast_re,
    Nat.cast_mul, Nat.cast_pow, Complex.re_sum] at h
  dsimp only
  rw [← Finset.sum_div, ← h]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hp : (n : ℝ) ^ n = (n : ℝ) ^ (n - 1) * (n : ℝ) := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))]
  rw [hp, div_div_eq_mul_div]
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hn, hf]

theorem main : H1 → H2 → type_of% @Green97.green_97.variants.eberhard_manners_mrazovic := by
  classical
  intro major minor
  let l : Filter ℕ := atTop ⊓ principal {n : ℕ | Odd n}
  let e : ℝ := Real.exp (-(1 / 2))
  let coeff (n : ℕ) [NeZero n] (ξ : Fin n → ZMod n) : ℂ :=
    ∑ π : Fin n ≃ ZMod n, ∏ i, ZMod.stdAddChar (ξ i * π i)
  let weight (n : ℕ) [NeZero n] (ξ : Fin n → ZMod n) : ℝ :=
    (coeff n ξ ^ 2 * coeff n (-ξ)).re / (n.factorial : ℝ) ^ 3
  let part (majorArc : Bool) (M n : ℕ) : ℝ :=
    if hn : n = 0 then 0 else
      letI : NeZero n := ⟨hn⟩
      (∑ ξ : Fin n → ZMod n,
        if ∃ a : ZMod n, (Finset.univ.filter fun i ↦ ξ i ≠ a).card ≤ 2 * M then
          bif majorArc then weight n ξ else 0
        else bif majorArc then 0 else weight n ξ) / (n : ℝ)
  let partialSum (M : ℕ) : ℝ :=
    ∑ j ∈ Finset.range (M + 1), (-(1 / 2) : ℝ) ^ j / (j.factorial : ℝ)
  let normCount (n : ℕ) : ℝ :=
    (Green97.numAdditiveTriples n : ℝ) / ((n.factorial : ℝ) ^ 3 / (n : ℝ) ^ (n - 1))
  have major' (M : ℕ) : Tendsto (part true M) l (𝓝 (partialSum M)) := major M
  have minor' (ε : ℝ) (hε : 0 < ε) : ∃ M₀ : ℕ, ∀ M ≥ M₀,
      ∀ᶠ n in l, |part false M n| < ε := minor ε hε
  have partial_limit : Tendsto partialSum atTop (𝓝 e) := by
    have series := (NormedSpace.expSeries_div_hasSum_exp (-(1 / 2) : ℝ)).tendsto_sum_nat
    rw [← Real.exp_eq_exp_ℝ] at series
    exact series.comp (tendsto_add_atTop_nat 1)
  have norm_limit : Tendsto normCount l (𝓝 e) := by
    refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
    have hδ : 0 < ε / 3 := by linarith
    obtain ⟨M₀, hM₀⟩ := minor' (ε / 3) hδ
    obtain ⟨M₁, hM₁⟩ := Metric.tendsto_atTop.mp partial_limit (ε / 3) hδ
    let M := max M₀ M₁
    have hseries := hM₁ M (le_max_right _ _)
    have hev := (eventually_ge_atTop (1 : ℕ)).filter_mono
      (inf_le_left : l ≤ atTop)
    filter_upwards [Metric.tendsto_nhds.mp (major' M) (ε / 3) hδ,
      hM₀ M (le_max_left _ _), hev] with n hmain htail hn
    have hn₀ : n ≠ 0 := by omega
    let _ : NeZero n := ⟨hn₀⟩
    have eq : part true M n + part false M n = normCount n := by
      simp only [part, dif_neg hn₀]
      rw [← add_div, ← Finset.sum_add_distrib]
      calc
        _ = (∑ ξ : Fin n → ZMod n, weight n ξ) / (n : ℝ) := by
          congr 1
          refine Finset.sum_congr rfl fun ξ _ ↦ ?_
          by_cases hs : ∃ a : ZMod n, (Finset.univ.filter fun i ↦ ξ i ≠ a).card ≤ 2 * M
          · simp only [if_pos hs, Bool.cond_true, Bool.cond_false, add_zero]
          · simp only [if_neg hs, Bool.cond_true, Bool.cond_false, zero_add]
        _ = normCount n := normalized_fourier_count n
    rw [← eq]
    calc
      dist (part true M n + part false M n) e
          ≤ |part false M n| +
            dist (part true M n) (partialSum M) + dist (partialSum M) e := by
        have h₁ := dist_triangle
          (part true M n + part false M n)
          (part true M n) e
        have h₂ := dist_triangle (part true M n) (partialSum M) e
        have ht : dist (part true M n + part false M n)
            (part true M n) = |part false M n| := by
          rw [Real.dist_eq, add_sub_cancel_left]
        linarith
      _ < ε := by linarith
  apply isEquivalent_of_tendsto_one
  have he : e ≠ 0 := Real.exp_ne_zero _
  have scale := norm_limit.div_const e
  rw [div_self he] at scale
  convert scale using 1
  ext n
  simp only [Pi.div_apply, normCount, e]
  ring

end OMA.R_Green97_green_97_variants_eberhard_manners_mrazovic_R2
