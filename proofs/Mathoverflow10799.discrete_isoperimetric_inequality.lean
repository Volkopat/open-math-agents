import FormalConjectures.Mathoverflow.«10799»

-- Problem: Optimal monotone families for the discrete isoperimetric inequality
-- Upstream: formal-conjectures FormalConjectures/Mathoverflow/10799.lean:238 (declaration Mathoverflow10799.discrete_isoperimetric_inequality)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Original proof: @Genbox, PR #341. Finite-sum bridges use standard Mathlib identities.

namespace OMA10799
open Finset Real

theorem key_log {p a b : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ha : 0 ≤ a) (hab : a ≤ b) :
    (1 - p) * (a * log a) + p * (b * log b) + p * (b - a) * log p ≤
      ((1 - p) * a + p * b) * log ((1 - p) * a + p * b) := by
  rcases ha.eq_or_lt with rfl | ha'
  · simp only [mul_zero, zero_add, sub_zero, Real.log_zero]
    rcases hab.eq_or_lt with rfl | hb
    · simp
    · rw [Real.log_mul hp0.ne' hb.ne']; ring_nf; simp
  · have hb : 0 < b := lt_of_lt_of_le ha' hab
    set μ := (1 - p) * a + p * b with hμ
    have hμpos : 0 < μ := by positivity
    have hconc : (1 - p) * log a + p * log b ≤ log μ := by
      have := (strictConcaveOn_log_Ioi.concaveOn).2 (Set.mem_Ioi.mpr ha') (Set.mem_Ioi.mpr hb)
        (by linarith : (0:ℝ) ≤ 1 - p) hp0.le (by ring)
      simpa [smul_eq_mul] using this
    have hpb : log p + log b ≤ log μ := by
      rw [← Real.log_mul hp0.ne' hb.ne']
      exact Real.log_le_log (by positivity) (by nlinarith)
    have e : μ * log μ = (1 - p) * a * log μ + p * b * log μ := by rw [hμ]; ring
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hconc),
      mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hpb), hp0, hp1]

noncomputable def f (p x : ℝ) : ℝ := x * logb p x

theorem two_point {p a b : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ha : 0 ≤ a) (hab : a ≤ b) :
    f p ((1 - p) * a + p * b) ≤ (1 - p) * f p a + p * f p b + p * (b - a) := by
  have hL : log p < 0 := Real.log_neg hp0 hp1
  have k := key_log hp0 hp1 ha hab
  unfold f logb
  set μ := (1 - p) * a + p * b
  have e : μ * (log μ / log p) - ((1 - p) * (a * (log a / log p)) + p * (b * (log b / log p))
      + p * (b - a)) = (μ * log μ - ((1 - p) * (a * log a) + p * (b * log b)
      + p * (b - a) * log p)) / log p := by
    have hL0 : log p ≠ 0 := hL.ne
    field_simp
  have : (μ * log μ - ((1 - p) * (a * log a) + p * (b * log b)
      + p * (b - a) * log p)) / log p ≤ 0 :=
    div_nonpos_of_nonneg_of_nonpos (by linarith) hL.le
  linarith

end OMA10799

namespace OMA10799
open Finset Real

variable {α : Type*} [DecidableEq α]

noncomputable def mu (p : ℝ) (U S : Finset α) : ℝ := p ^ S.card * (1 - p) ^ (U.card - S.card)

open Classical in
noncomputable def M (p : ℝ) (U : Finset α) (P : Finset α → Prop) : ℝ :=
  ∑ S ∈ U.powerset, if P S then mu p U S else 0

open Classical in
noncomputable def I (p : ℝ) (U : Finset α) (P : Finset α → Prop) : ℝ :=
  ∑ S ∈ U.powerset, mu p U S * ∑ i ∈ U, (if Xor (P S) (P (symmDiff S {i})) then (1:ℝ) else 0)

lemma sd1 {a : α} {S : Finset α} (h : a ∉ S) : symmDiff S {a} = insert a S := by
  simpa using (disjoint_singleton_right.mpr h).symmDiff_eq_sup

lemma sd2 {a : α} {S : Finset α} (h : a ∉ S) : symmDiff (insert a S) {a} = S := by
  rw [← sd1 h, symmDiff_symmDiff_cancel_right]

lemma sd3 {a i : α} {S : Finset α} (h : i ≠ a) :
    symmDiff (insert a S) {i} = insert a (symmDiff S {i}) := by
  ext x; simp only [mem_symmDiff, mem_singleton, mem_insert]
  by_cases hx : x = a <;> by_cases hi : x = i <;> simp_all

omit [DecidableEq α] in
lemma mu_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (U S : Finset α) : 0 ≤ mu p U S := by
  unfold mu; have : 0 ≤ 1 - p := by linarith
  positivity

lemma mu_ins0 {p : ℝ} {a : α} {U S : Finset α} (ha : a ∉ U) (hS : S ⊆ U) :
    mu p (insert a U) S = (1 - p) * mu p U S := by
  unfold mu
  have := card_le_card hS
  rw [card_insert_of_notMem ha, show U.card + 1 - S.card = (U.card - S.card) + 1 by omega, pow_succ]
  ring

lemma mu_ins1 {p : ℝ} {a : α} {U S : Finset α} (ha : a ∉ U) (hS : S ⊆ U) :
    mu p (insert a U) (insert a S) = p * mu p U S := by
  unfold mu
  have haS : a ∉ S := fun h => ha (hS h)
  rw [card_insert_of_notMem ha, card_insert_of_notMem haS, pow_succ,
    show U.card + 1 - (S.card + 1) = U.card - S.card by omega]
  ring

lemma M_insert {p : ℝ} {a : α} {U : Finset α} (ha : a ∉ U) (P : Finset α → Prop) :
    M p (insert a U) P = (1 - p) * M p U P + p * M p U (fun S => P (insert a S)) := by
  classical
  unfold M
  rw [sum_powerset_insert ha, mul_sum, mul_sum]
  congr 1 <;> refine sum_congr rfl fun S hS => ?_ <;> rw [mem_powerset] at hS
  · rw [mu_ins0 ha hS]; split_ifs <;> ring
  · rw [mu_ins1 ha hS]; split_ifs <;> ring

lemma I_insert {p : ℝ} {a : α} {U : Finset α} (ha : a ∉ U) (P : Finset α → Prop)
    (hP : ∀ S T, P S → S ⊆ T → P T) :
    I p (insert a U) P = (1 - p) * I p U P + p * I p U (fun S => P (insert a S))
      + (M p U (fun S => P (insert a S)) - M p U P) := by
  classical
  unfold I M
  rw [sum_powerset_insert ha, ← sum_add_distrib, mul_sum, mul_sum, ← sum_sub_distrib,
    ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun S hS => ?_
  rw [mem_powerset] at hS
  have haS : a ∉ S := fun h => ha (hS h)
  have h3 : ∑ i ∈ U, (if Xor (P (insert a S)) (P (symmDiff (insert a S) {i})) then (1:ℝ) else 0)
      = ∑ i ∈ U, (if Xor (P (insert a S)) (P (insert a (symmDiff S {i}))) then (1:ℝ) else 0) :=
    sum_congr rfl fun i hi => by rw [sd3 (show i ≠ a by rintro rfl; exact ha hi)]
  rw [mu_ins0 ha hS, mu_ins1 ha hS, sum_insert ha, sum_insert ha, sd1 haS, sd2 haS, h3]
  by_cases h1 : P S <;> by_cases h2 : P (insert a S)
  · simp [Xor, h1, h2]; ring
  · exact absurd (hP _ _ h1 (subset_insert _ _)) h2
  · simp [Xor, h1, h2]; ring
  · simp [Xor, h1, h2]; ring

theorem main {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (U : Finset α) :
    ∀ (P : Finset α → Prop), (∀ S T, P S → S ⊆ T → P T) → f p (M p U P) ≤ p * I p U P := by
  induction U using Finset.induction_on with
  | empty =>
    intro P _
    classical
    simp only [M, I, powerset_empty, sum_singleton, sum_empty, mul_zero]
    unfold f; split_ifs <;> simp [mu]
  | @insert a U ha ih =>
    intro P hP
    have hP1 : ∀ S T, P (insert a S) → S ⊆ T → P (insert a T) :=
      fun S T h hST => hP _ _ h (insert_subset_insert a hST)
    have i0 := ih P hP
    have i1 := ih _ hP1
    classical
    have hm0 : 0 ≤ M p U P := sum_nonneg fun S _ => by
      split_ifs
      · exact mu_nonneg hp0.le hp1.le _ _
      · exact le_rfl
    have hm01 : M p U P ≤ M p U (fun S => P (insert a S)) := sum_le_sum fun S _ => by
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd (hP _ _ h1 (subset_insert _ _)) h2
      · exact mu_nonneg hp0.le hp1.le _ _
      · exact le_rfl
    rw [M_insert ha, I_insert ha P hP]
    have := two_point hp0 hp1 hm0 hm01
    nlinarith [mul_le_mul_of_nonneg_left i0 (by linarith : (0:ℝ) ≤ 1 - p),
      mul_le_mul_of_nonneg_left i1 hp0.le]

end OMA10799

open Finset in
theorem OMA.solution : type_of% @Mathoverflow10799.discrete_isoperimetric_inequality := by
  intro n p hp hp' F hF
  classical
  have hP : ∀ S T : Finset (Fin n), S ∈ F → S ⊆ T → T ∈ F := fun S T hS hST => hF hST hS
  have h := OMA10799.main hp hp' (Finset.univ) (fun S => S ∈ F) hP
  have hM : OMA10799.M p univ (fun S => S ∈ F) = Mathoverflow10799.μFamily p F := by
    unfold OMA10799.M Mathoverflow10799.μFamily
    simp only [powerset_univ]
    convert! Fintype.sum_ite_mem F (Mathoverflow10799.μ p) using 1
    congr!
    ext
    simp [OMA10799.mu, Mathoverflow10799.μ]
  have hI : OMA10799.I p univ (fun S => S ∈ F) = Mathoverflow10799.edgeBoundary n p F := by
    simp only [OMA10799.I, Mathoverflow10799.edgeBoundary, Mathoverflow10799.boundaryCount,
      OMA10799.mu, Mathoverflow10799.μ, powerset_univ, card_univ, Fintype.card_fin,
      Finset.natCast_card_filter]
    congr!
  show Mathoverflow10799.edgeBoundary n p F ≥ _
  rw [← hM, ← hI, ge_iff_le, div_le_iff₀ hp]
  have := h; unfold OMA10799.f at this; linarith
