import OMAReductions.R_Green68_green_68_variants_voloch_R2
import Mathlib

namespace VolochH1Proof

open Finset MvPolynomial

section ProjLinear

variable {K : Type*} [Field K]

def embed (a : Fin 2 → K) : Fin 3 → K :=
  fun i => match i with | 0 => 1 | 1 => a 0 | 2 => a 1

def dot3 (u v : Fin 3 → K) : K :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

def cross3 (u v : Fin 3 → K) : Fin 3 → K :=
  fun i => match i with
    | 0 => u 1 * v 2 - u 2 * v 1
    | 1 => u 2 * v 0 - u 0 * v 2
    | 2 => u 0 * v 1 - u 1 * v 0

def det3 (u v w : Fin 3 → K) : K :=
  dot3 (cross3 u v) w

lemma embed_zero (a : Fin 2 → K) : embed a 0 = 1 := rfl
lemma embed_one (a : Fin 2 → K) : embed a 1 = a 0 := rfl
lemma embed_two (a : Fin 2 → K) : embed a 2 = a 1 := rfl

lemma embed_ne_zero (a : Fin 2 → K) : embed a ≠ 0 := by
  intro h
  have h0 : embed a 0 = 0 := congrFun h 0
  rw [embed_zero] at h0
  exact one_ne_zero h0

lemma embed_inj : Function.Injective (embed (K := K)) := by
  intro a b h
  ext i
  fin_cases i
  · exact congrFun h 1
  · exact congrFun h 2

lemma dot3_comm (u v : Fin 3 → K) : dot3 u v = dot3 v u := by
  unfold dot3; ring

lemma dot3_smul_left (c : K) (u v : Fin 3 → K) : dot3 (c • u) v = c * dot3 u v := by
  simp only [dot3, Pi.smul_apply, smul_eq_mul]; ring

lemma dot3_smul_right (c : K) (u v : Fin 3 → K) : dot3 u (c • v) = c * dot3 u v := by
  simp only [dot3, Pi.smul_apply, smul_eq_mul]; ring

lemma dot3_add_left (u₁ u₂ v : Fin 3 → K) : dot3 (u₁ + u₂) v = dot3 u₁ v + dot3 u₂ v := by
  simp only [dot3, Pi.add_apply]; ring

lemma dot3_add_right (u v₁ v₂ : Fin 3 → K) : dot3 u (v₁ + v₂) = dot3 u v₁ + dot3 u v₂ := by
  simp only [dot3, Pi.add_apply]; ring

lemma dot3_cross3_left (u v : Fin 3 → K) : dot3 (cross3 u v) u = 0 := by
  unfold dot3 cross3; dsimp only; ring

lemma dot3_cross3_right (u v : Fin 3 → K) : dot3 (cross3 u v) v = 0 := by
  unfold dot3 cross3; dsimp only; ring

lemma cross3_antisymm (u v : Fin 3 → K) : cross3 v u = (-1 : K) • cross3 u v := by
  ext i; fin_cases i <;> simp [cross3] <;> ring

lemma det3_swap12 (u v w : Fin 3 → K) : det3 v u w = - det3 u v w := by
  unfold det3 dot3 cross3; dsimp only; ring

lemma det3_swap23 (u v w : Fin 3 → K) : det3 u w v = - det3 u v w := by
  unfold det3 dot3 cross3; dsimp only; ring

lemma det3_cyclic (u v w : Fin 3 → K) : det3 u v w = det3 v w u := by
  unfold det3 dot3 cross3; dsimp only; ring

lemma det3_self_12 (u w : Fin 3 → K) : det3 u u w = 0 := by
  unfold det3 dot3 cross3; dsimp only; ring

lemma det3_self_13 (u v : Fin 3 → K) : det3 u v u = 0 := by
  unfold det3 dot3 cross3; dsimp only; ring

lemma det3_self_23 (u v : Fin 3 → K) : det3 u v v = 0 := by
  unfold det3 dot3 cross3; dsimp only; ring

lemma cross3_ne_zero_of_det3_ne_zero {u v w : Fin 3 → K} (h : det3 u v w ≠ 0) :
    cross3 u v ≠ 0 := by
  intro hc
  apply h
  simp [det3, hc, dot3]

lemma cross3_cross3 (u v w : Fin 3 → K) :
    cross3 (cross3 u v) (cross3 u w) = det3 u v w • u := by
  ext i; fin_cases i <;> simp [det3, dot3, cross3] <;> ring

lemma cramer3 (x y z a : Fin 3 → K) :
    det3 x y z • a = det3 a y z • x + det3 x a z • y + det3 x y a • z := by
  ext i; fin_cases i <;> simp [det3, dot3, cross3] <;> ring

lemma cross3_eq_zero_iff {u v : Fin 3 → K} (hu : u ≠ 0) :
    cross3 u v = 0 ↔ ∃ c : K, v = c • u := by
  constructor
  · intro hc
    have h0 : u 1 * v 2 - u 2 * v 1 = 0 := congrFun hc 0
    have h1 : u 2 * v 0 - u 0 * v 2 = 0 := congrFun hc 1
    have h2 : u 0 * v 1 - u 1 * v 0 = 0 := congrFun hc 2
    by_cases hu0 : u 0 ≠ 0
    · refine ⟨v 0 / u 0, ?_⟩
      ext i; fin_cases i
      · change v 0 = v 0 / u 0 * u 0; rw [div_mul_cancel₀ _ hu0]
      · change v 1 = v 0 / u 0 * u 1
        apply mul_left_cancel₀ hu0
        calc u 0 * v 1 = u 1 * v 0 := sub_eq_zero.mp h2
          _ = u 0 * (v 0 / u 0 * u 1) := by rw [← mul_assoc, mul_div_cancel₀ _ hu0]; ring
      · change v 2 = v 0 / u 0 * u 2
        apply mul_left_cancel₀ hu0
        calc u 0 * v 2 = u 2 * v 0 := (sub_eq_zero.mp h1).symm
          _ = u 0 * (v 0 / u 0 * u 2) := by rw [← mul_assoc, mul_div_cancel₀ _ hu0]; ring
    · have hu0' : u 0 = 0 := not_not.mp hu0
      by_cases hu1 : u 1 ≠ 0
      · refine ⟨v 1 / u 1, ?_⟩
        ext i; fin_cases i
        · change v 0 = v 1 / u 1 * u 0
          rw [hu0', mul_zero]
          have : u 1 * v 0 = 0 := by rw [hu0', zero_mul, zero_sub, neg_eq_zero] at h2; exact h2
          exact (mul_eq_zero.mp this).resolve_left hu1
        · change v 1 = v 1 / u 1 * u 1; rw [div_mul_cancel₀ _ hu1]
        · change v 2 = v 1 / u 1 * u 2
          apply mul_left_cancel₀ hu1
          calc u 1 * v 2 = u 2 * v 1 := sub_eq_zero.mp h0
            _ = u 1 * (v 1 / u 1 * u 2) := by rw [← mul_assoc, mul_div_cancel₀ _ hu1]; ring
      · have hu1' : u 1 = 0 := not_not.mp hu1
        have hu2 : u 2 ≠ 0 := by
          intro hu2; apply hu; ext i; fin_cases i <;> assumption
        refine ⟨v 2 / u 2, ?_⟩
        ext i; fin_cases i
        · change v 0 = v 2 / u 2 * u 0
          rw [hu0', mul_zero]
          have : u 2 * v 0 = 0 := by rw [hu0', zero_mul, sub_zero] at h1; exact h1
          exact (mul_eq_zero.mp this).resolve_left hu2
        · change v 1 = v 2 / u 2 * u 1
          rw [hu1', mul_zero]
          have : u 2 * v 1 = 0 := by rw [hu1', zero_mul, zero_sub, neg_eq_zero] at h0; exact h0
          exact (mul_eq_zero.mp this).resolve_left hu2
        · change v 2 = v 2 / u 2 * u 2; rw [div_mul_cancel₀ _ hu2]
  · rintro ⟨c, rfl⟩
    ext i; fin_cases i <;> simp [cross3] <;> ring

lemma det3_embed (a b c : Fin 2 → K) :
    det3 (embed a) (embed b) (embed c) =
      (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) := by
  unfold det3 dot3 cross3 embed; dsimp only; ring

lemma dot3_cross3_comm (u v w : Fin 3 → K) :
    dot3 w (cross3 u v) = det3 u v w := by
  unfold det3 dot3 cross3; dsimp only; ring

lemma cross3_cross3_eq_zero_of_dot3 {a b u : Fin 3 → K}
    (ha : dot3 u a = 0) (hb : dot3 u b = 0) :
    cross3 (cross3 a b) u = 0 := by
  ext i; fin_cases i
  · change (a 2 * b 0 - a 0 * b 2) * u 2 - (a 0 * b 1 - a 1 * b 0) * u 1 = 0
    unfold dot3 at ha hb; linear_combination b 0 * ha - a 0 * hb
  · change (a 0 * b 1 - a 1 * b 0) * u 0 - (a 1 * b 2 - a 2 * b 1) * u 2 = 0
    unfold dot3 at ha hb; linear_combination b 1 * ha - a 1 * hb
  · change (a 1 * b 2 - a 2 * b 1) * u 1 - (a 2 * b 0 - a 0 * b 2) * u 0 = 0
    unfold dot3 at ha hb; linear_combination b 2 * ha - a 2 * hb

lemma collinear_of_det3_embed_eq_zero {a b c : Fin 2 → K}
    (h : det3 (embed a) (embed b) (embed c) = 0) :
    Collinear K ({a, b, c} : Set (Fin 2 → K)) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  by_cases hab : a = b
  · refine ⟨a, c - a, ?_⟩
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with hq | hq | hq
    · subst hq; exact ⟨0, by simp⟩
    · subst hq; exact ⟨0, by simp [hab]⟩
    · subst hq; exact ⟨1, by simp⟩
  · refine ⟨a, b - a, ?_⟩
    have hdet : (b 0 - a 0) * (c 1 - a 1) = (b 1 - a 1) * (c 0 - a 0) := by
      rw [det3_embed] at h; exact sub_eq_zero.mp h
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with hq | hq | hq
    · subst hq; exact ⟨0, by simp⟩
    · subst hq; exact ⟨1, by simp⟩
    · rw [hq]
      by_cases h0 : b 0 - a 0 ≠ 0
      · refine ⟨(c 0 - a 0) / (b 0 - a 0), ?_⟩
        ext i; fin_cases i
        · change c 0 = (c 0 - a 0) / (b 0 - a 0) * (b 0 - a 0) + a 0
          rw [div_mul_cancel₀ _ h0]; ring
        · change c 1 = (c 0 - a 0) / (b 0 - a 0) * (b 1 - a 1) + a 1
          apply mul_left_cancel₀ h0
          calc (b 0 - a 0) * c 1
              = (b 0 - a 0) * (c 1 - a 1) + (b 0 - a 0) * a 1 := by ring
            _ = (b 1 - a 1) * (c 0 - a 0) + (b 0 - a 0) * a 1 := by rw [hdet]
            _ = (b 0 - a 0) * ((c 0 - a 0) / (b 0 - a 0) * (b 1 - a 1) + a 1) := by
                rw [mul_add, ← mul_assoc, mul_div_cancel₀ _ h0]; ring
      · have h0' : b 0 - a 0 = 0 := not_not.mp h0
        have h1 : b 1 - a 1 ≠ 0 := by
          intro h1
          apply hab
          ext i; fin_cases i
          · exact (sub_eq_zero.mp h0').symm
          · exact (sub_eq_zero.mp h1).symm
        have hc0 : c 0 - a 0 = 0 := by
          rw [h0', zero_mul] at hdet
          exact (mul_eq_zero.mp hdet.symm).resolve_left h1
        refine ⟨(c 1 - a 1) / (b 1 - a 1), ?_⟩
        ext i; fin_cases i
        · change c 0 = (c 1 - a 1) / (b 1 - a 1) * (b 0 - a 0) + a 0
          rw [h0', mul_zero, zero_add]; exact sub_eq_zero.mp hc0
        · change c 1 = (c 1 - a 1) / (b 1 - a 1) * (b 1 - a 1) + a 1
          rw [div_mul_cancel₀ _ h1]; ring

abbrev IsNorm (v : Fin 3 → K) : Prop :=
  v 0 = 1 ∨ (v 0 = 0 ∧ v 1 = 1) ∨ (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 1)

noncomputable def norm3 (v : Fin 3 → K) : Fin 3 → K := by
  classical
  exact if v 0 ≠ 0 then (v 0)⁻¹ • v
    else if v 1 ≠ 0 then (v 1)⁻¹ • v
    else (v 2)⁻¹ • v

lemma isNorm_ne_zero {v : Fin 3 → K} (hv : IsNorm v) : v ≠ 0 := by
  intro h
  rcases hv with h0 | ⟨_, h1⟩ | ⟨_, _, h2⟩
  · have := congrFun h 0; rw [h0] at this; exact one_ne_zero this
  · have := congrFun h 1; rw [h1] at this; exact one_ne_zero this
  · have := congrFun h 2; rw [h2] at this; exact one_ne_zero this

lemma norm3_isNorm {v : Fin 3 → K} (hv : v ≠ 0) : IsNorm (norm3 v) := by
  classical
  unfold norm3 IsNorm
  split_ifs with h0 h1
  · left; simp [h0]
  · right; left
    have h0' : v 0 = 0 := not_not.mp h0
    simp [h0', h1]
  · right; right
    have h0' : v 0 = 0 := not_not.mp h0
    have h1' : v 1 = 0 := not_not.mp h1
    have h2 : v 2 ≠ 0 := by intro h2; apply hv; ext i; fin_cases i <;> assumption
    simp [h0', h1', h2]

lemma norm3_exists_smul {v : Fin 3 → K} (hv : v ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ norm3 v = c • v := by
  classical
  unfold norm3
  split_ifs with h0 h1
  · exact ⟨(v 0)⁻¹, inv_ne_zero h0, rfl⟩
  · exact ⟨(v 1)⁻¹, inv_ne_zero h1, rfl⟩
  · have h0' : v 0 = 0 := not_not.mp h0
    have h1' : v 1 = 0 := not_not.mp h1
    have h2 : v 2 ≠ 0 := by intro h2; apply hv; ext i; fin_cases i <;> assumption
    exact ⟨(v 2)⁻¹, inv_ne_zero h2, rfl⟩

lemma isNorm_eq_of_smul {u v : Fin 3 → K} (hu : IsNorm u) (hv : IsNorm v)
    {c : K} (h : u = c • v) : u = v := by
  have hc : c = 1 := by
    have h0 : u 0 = c * v 0 := congrFun h 0
    have h1 : u 1 = c * v 1 := congrFun h 1
    have h2 : u 2 = c * v 2 := congrFun h 2
    rcases hu with hu0 | ⟨hu0, hu1⟩ | ⟨hu0, hu1, hu2⟩ <;>
    rcases hv with hv0 | ⟨hv0, hv1⟩ | ⟨hv0, hv1, hv2⟩
    · rw [hu0, hv0, mul_one] at h0; exact h0.symm
    · rw [hu0, hv0, mul_zero] at h0; exact absurd h0 one_ne_zero
    · rw [hu0, hv0, mul_zero] at h0; exact absurd h0 one_ne_zero
    · rw [hu0, hv0, mul_one] at h0
      rw [h0.symm, zero_mul] at h1; rw [hu1] at h1; exact absurd h1 one_ne_zero
    · rw [hu1, hv1, mul_one] at h1; exact h1.symm
    · rw [hu1, hv1, mul_zero] at h1; exact absurd h1 one_ne_zero
    · rw [hu0, hv0, mul_one] at h0
      rw [h0.symm, zero_mul] at h2; rw [hu2] at h2; exact absurd h2 one_ne_zero
    · rw [hu1, hv1, mul_one] at h1
      rw [h1.symm, zero_mul] at h2; rw [hu2] at h2; exact absurd h2 one_ne_zero
    · rw [hu2, hv2, mul_one] at h2; exact h2.symm
  rw [h, hc, one_smul]

lemma norm3_eq_self {v : Fin 3 → K} (hv : IsNorm v) : norm3 v = v := by
  obtain ⟨c, _, hc⟩ := norm3_exists_smul (isNorm_ne_zero hv)
  exact isNorm_eq_of_smul (norm3_isNorm (isNorm_ne_zero hv)) hv hc

lemma norm3_eq_iff_prop {u v : Fin 3 → K} (hu : u ≠ 0) (hv : v ≠ 0) :
    norm3 u = norm3 v ↔ ∃ c : K, c ≠ 0 ∧ u = c • v := by
  obtain ⟨cu, hcu, eq_u⟩ := norm3_exists_smul hu
  obtain ⟨cv, hcv, eq_v⟩ := norm3_exists_smul hv
  constructor
  · intro heq
    refine ⟨cu⁻¹ * cv, mul_ne_zero (inv_ne_zero hcu) hcv, ?_⟩
    have h1 : cu • u = cv • v := by rw [← eq_u, ← eq_v, heq]
    calc u = cu⁻¹ • (cu • u) := by rw [inv_smul_smul₀ hcu]
      _ = cu⁻¹ • (cv • v) := by rw [h1]
      _ = (cu⁻¹ * cv) • v := by rw [smul_smul]
  · rintro ⟨c, hc, rfl⟩
    apply isNorm_eq_of_smul (norm3_isNorm hu) (norm3_isNorm hv) (c := cu * c * cv⁻¹)
    rw [eq_u, eq_v, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ hcv, mul_one, ← smul_smul]

lemma norm3_eq_iff_cross3 {u v : Fin 3 → K} (hu : u ≠ 0) (hv : v ≠ 0) :
    norm3 u = norm3 v ↔ cross3 u v = 0 := by
  rw [norm3_eq_iff_prop hu hv, cross3_eq_zero_iff hu]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c⁻¹, by rw [inv_smul_smul₀ hc]⟩
  · rintro ⟨c, rfl⟩
    have hc : c ≠ 0 := by rintro rfl; exact hv (zero_smul K u)
    exact ⟨c⁻¹, inv_ne_zero hc, by rw [inv_smul_smul₀ hc]⟩

end ProjLinear

section ArcTangents

variable {p : ℕ} [Fact p.Prime]

private lemma det3_ne_zero_of_arc {A : Finset (Fin 2 → ZMod p)}
    (harc : ∀ s ⊆ A, s.card = 3 → ¬ Collinear (ZMod p) (s : Set (Fin 2 → ZMod p)))
    {a b c : Fin 2 → ZMod p} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    det3 (embed a) (embed b) (embed c) ≠ 0 := by
  intro h0
  have hsub : ({a, b, c} : Finset (Fin 2 → ZMod p)) ⊆ A := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcard : ({a, b, c} : Finset (Fin 2 → ZMod p)).card = 3 := by
    rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
    · simpa using hbc
    · simp [hab, hac]
  have hcol := collinear_of_det3_embed_eq_zero h0
  have hcoe : (({a, b, c} : Finset (Fin 2 → ZMod p)) : Set (Fin 2 → ZMod p)) = {a, b, c} := by
    simp
  exact harc {a, b, c} hsub hcard (hcoe ▸ hcol)

noncomputable def lineThrough (v : Fin 3 → ZMod p) : Finset (Fin 3 → ZMod p) :=
  univ.filter fun u => IsNorm u ∧ dot3 u v = 0

lemma mem_lineThrough {u v : Fin 3 → ZMod p} :
    u ∈ lineThrough v ↔ IsNorm u ∧ dot3 u v = 0 := by
  simp [lineThrough]

lemma card_lineThrough_embed (a : Fin 2 → ZMod p) :
    (lineThrough (embed a)).card = p + 1 := by
  classical
  let f : Option (ZMod p) → Fin 3 → ZMod p := fun o =>
    match o with
    | none => norm3 (fun i => match i with | 0 => -a 1 | 1 => 0 | 2 => 1)
    | some y => norm3 (fun i => match i with | 0 => -a 0 - a 1 * y | 1 => 1 | 2 => y)
  have hf_mem : ∀ o : Option (ZMod p), f o ∈ lineThrough (embed a) := by
    intro o
    rw [mem_lineThrough]
    cases o with
    | none =>
      let w : Fin 3 → ZMod p := fun i => match i with | 0 => -a 1 | 1 => 0 | 2 => 1
      have hw : w ≠ 0 := by intro h; exact one_ne_zero (congrFun h 2)
      obtain ⟨c, _, hc⟩ := norm3_exists_smul hw
      refine ⟨norm3_isNorm hw, ?_⟩
      change dot3 (norm3 w) (embed a) = 0
      rw [hc, dot3_smul_left]
      have : dot3 w (embed a) = 0 := by unfold dot3 w embed; dsimp only; ring
      rw [this, mul_zero]
    | some y =>
      let w : Fin 3 → ZMod p := fun i => match i with | 0 => -a 0 - a 1 * y | 1 => 1 | 2 => y
      have hw : w ≠ 0 := by intro h; exact one_ne_zero (congrFun h 1)
      obtain ⟨c, _, hc⟩ := norm3_exists_smul hw
      refine ⟨norm3_isNorm hw, ?_⟩
      change dot3 (norm3 w) (embed a) = 0
      rw [hc, dot3_smul_left]
      have : dot3 w (embed a) = 0 := by unfold dot3 w embed; dsimp only; ring
      rw [this, mul_zero]
  have hf_inj : Function.Injective f := by
    intro o₁ o₂ heq
    cases o₁ with
    | none =>
      cases o₂ with
      | none => rfl
      | some y =>
        let w₁ : Fin 3 → ZMod p := fun i => match i with | 0 => -a 1 | 1 => 0 | 2 => 1
        let w₂ : Fin 3 → ZMod p := fun i => match i with | 0 => -a 0 - a 1 * y | 1 => 1 | 2 => y
        have hw₁ : w₁ ≠ 0 := fun h => one_ne_zero (congrFun h 2)
        have hw₂ : w₂ ≠ 0 := fun h => one_ne_zero (congrFun h 1)
        obtain ⟨c, hc, hsm⟩ := (norm3_eq_iff_prop hw₁ hw₂).mp heq
        have h1 : w₁ 1 = c * w₂ 1 := congrFun hsm 1
        simp only [w₁, w₂, mul_one] at h1
        exact absurd h1.symm hc
    | some y₁ =>
      cases o₂ with
      | none =>
        let w₁ : Fin 3 → ZMod p := fun i => match i with | 0 => -a 0 - a 1 * y₁ | 1 => 1 | 2 => y₁
        let w₂ : Fin 3 → ZMod p := fun i => match i with | 0 => -a 1 | 1 => 0 | 2 => 1
        have hw₁ : w₁ ≠ 0 := fun h => one_ne_zero (congrFun h 1)
        have hw₂ : w₂ ≠ 0 := fun h => one_ne_zero (congrFun h 2)
        obtain ⟨c, _, hsm⟩ := (norm3_eq_iff_prop hw₁ hw₂).mp heq
        have h1 : w₁ 1 = c * w₂ 1 := congrFun hsm 1
        simp only [w₁, w₂, mul_zero] at h1
        exact absurd h1 one_ne_zero
      | some y₂ =>
        let w₁ : Fin 3 → ZMod p := fun i => match i with | 0 => -a 0 - a 1 * y₁ | 1 => 1 | 2 => y₁
        let w₂ : Fin 3 → ZMod p := fun i => match i with | 0 => -a 0 - a 1 * y₂ | 1 => 1 | 2 => y₂
        have hw₁ : w₁ ≠ 0 := fun h => one_ne_zero (congrFun h 1)
        have hw₂ : w₂ ≠ 0 := fun h => one_ne_zero (congrFun h 1)
        obtain ⟨c, _, hsm⟩ := (norm3_eq_iff_prop hw₁ hw₂).mp heq
        have h1 : (1 : ZMod p) = c * 1 := congrFun hsm 1
        have h2 : y₁ = c * y₂ := congrFun hsm 2
        rw [mul_one] at h1
        rw [← h1, one_mul] at h2
        exact congrArg some h2
  have h_eq : lineThrough (embed a) = univ.image f := by
    ext u
    simp only [mem_image, mem_univ, true_and]
    constructor
    · intro hu
      obtain ⟨hunorm, hudot⟩ := mem_lineThrough.mp hu
      have hu0 : u 0 = -a 0 * u 1 - a 1 * u 2 := by
        unfold dot3 embed at hudot; dsimp only at hudot
        linear_combination hudot
      by_cases h1 : u 1 = 0
      · refine ⟨none, ?_⟩
        have h2 : u 2 ≠ 0 := by
          intro h2
          have h0 : u 0 = 0 := by rw [hu0, h1, h2]; ring
          exact isNorm_ne_zero hunorm (by ext i; fin_cases i <;> assumption)
        let w : Fin 3 → ZMod p := fun i => match i with | 0 => -a 1 | 1 => 0 | 2 => 1
        have hw : w ≠ 0 := fun h => one_ne_zero (congrFun h 2)
        change norm3 w = u
        rw [← norm3_eq_self hunorm, norm3_eq_iff_prop hw (isNorm_ne_zero hunorm)]
        refine ⟨(u 2)⁻¹, inv_ne_zero h2, ?_⟩
        ext i; fin_cases i
        · change -a 1 = (u 2)⁻¹ * u 0
          rw [hu0, h1, mul_zero, zero_sub, mul_neg, mul_comm (u 2)⁻¹, mul_assoc,
            mul_inv_cancel₀ h2, mul_one]
        · simp [w, h1]
        · simp [w, inv_mul_cancel₀ h2]
      · refine ⟨some (u 2 / u 1), ?_⟩
        let w : Fin 3 → ZMod p := fun i =>
          match i with | 0 => -a 0 - a 1 * (u 2 / u 1) | 1 => 1 | 2 => u 2 / u 1
        have hw : w ≠ 0 := fun h => one_ne_zero (congrFun h 1)
        change norm3 w = u
        rw [← norm3_eq_self hunorm, norm3_eq_iff_prop hw (isNorm_ne_zero hunorm)]
        refine ⟨(u 1)⁻¹, inv_ne_zero h1, ?_⟩
        ext i; fin_cases i
        · change -a 0 - a 1 * (u 2 / u 1) = (u 1)⁻¹ * u 0
          rw [hu0, div_eq_mul_inv]
          have : (u 1)⁻¹ * (-a 0 * u 1 - a 1 * u 2) = -a 0 * ((u 1)⁻¹ * u 1) - a 1 * (u 2 * (u 1)⁻¹) := by ring
          rw [this, inv_mul_cancel₀ h1, mul_one]
        · simp [w, inv_mul_cancel₀ h1]
        · simp [w, div_eq_mul_inv, mul_comm]
    · rintro ⟨o, rfl⟩
      exact hf_mem o
  rw [h_eq, card_image_of_injective _ hf_inj, card_univ, Fintype.card_option, ZMod.card]

noncomputable def tangents (A : Finset (Fin 2 → ZMod p)) (a : Fin 2 → ZMod p) :
    Finset (Fin 3 → ZMod p) :=
  (lineThrough (embed a)).filter fun u => ∀ b ∈ A, b ≠ a → dot3 u (embed b) ≠ 0

lemma mem_tangents {A : Finset (Fin 2 → ZMod p)} {a : Fin 2 → ZMod p} {u : Fin 3 → ZMod p} :
    u ∈ tangents A a ↔ IsNorm u ∧ dot3 u (embed a) = 0 ∧ ∀ b ∈ A, b ≠ a → dot3 u (embed b) ≠ 0 := by
  simp [tangents, mem_lineThrough, and_assoc]

lemma card_tangents_add_card_erase {A : Finset (Fin 2 → ZMod p)}
    (harc : ∀ s ⊆ A, s.card = 3 → ¬ Collinear (ZMod p) (s : Set (Fin 2 → ZMod p)))
    {a : Fin 2 → ZMod p} (ha : a ∈ A) :
    (tangents A a).card + (A.card - 1) = p + 1 := by
  classical
  let sec := (A.erase a).image fun b => norm3 (cross3 (embed a) (embed b))
  have hsec_sub : sec ⊆ lineThrough (embed a) := by
    intro u hu
    rcases mem_image.mp hu with ⟨b, hb, rfl⟩
    have hba : b ≠ a := (mem_erase.mp hb).1
    have hcr : cross3 (embed a) (embed b) ≠ 0 := by
      intro h0
      obtain ⟨c, hc⟩ := (cross3_eq_zero_iff (embed_ne_zero a)).mp h0
      have h0' : (1 : ZMod p) = c * 1 := congrFun hc 0
      rw [mul_one] at h0'
      rw [← h0', one_smul] at hc
      exact hba (embed_inj hc)
    obtain ⟨c, _, hce⟩ := norm3_exists_smul hcr
    rw [mem_lineThrough]
    refine ⟨norm3_isNorm hcr, ?_⟩
    rw [hce, dot3_smul_left, dot3_cross3_left, mul_zero]
  have hsec_card : sec.card = A.card - 1 := by
    rw [← card_erase_of_mem ha]
    apply card_image_of_injOn
    intro b₁ hb₁ b₂ hb₂ heq
    by_contra hne
    have h1a : b₁ ≠ a := (mem_erase.mp hb₁).1
    have h2a : b₂ ≠ a := (mem_erase.mp hb₂).1
    have h1A : b₁ ∈ A := (mem_erase.mp hb₁).2
    have h2A : b₂ ∈ A := (mem_erase.mp hb₂).2
    have hdet : det3 (embed a) (embed b₁) (embed b₂) ≠ 0 :=
      det3_ne_zero_of_arc harc ha h1A h2A h1a.symm h2a.symm hne
    have hcr1 : cross3 (embed a) (embed b₁) ≠ 0 := cross3_ne_zero_of_det3_ne_zero hdet
    have hdet2 : det3 (embed a) (embed b₂) (embed b₁) ≠ 0 :=
      det3_ne_zero_of_arc harc ha h2A h1A h2a.symm h1a.symm (Ne.symm hne)
    have hcr2 : cross3 (embed a) (embed b₂) ≠ 0 := cross3_ne_zero_of_det3_ne_zero hdet2
    have hcc : cross3 (cross3 (embed a) (embed b₁)) (cross3 (embed a) (embed b₂)) = 0 :=
      (norm3_eq_iff_cross3 hcr1 hcr2).mp heq
    rw [cross3_cross3] at hcc
    have h0 := congrFun hcc 0
    simp only [Pi.smul_apply, smul_eq_mul, embed_zero, mul_one, Pi.zero_apply] at h0
    exact hdet h0
  have hpart : tangents A a = lineThrough (embed a) \ sec := by
    ext u
    simp only [tangents, mem_filter, mem_sdiff]
    constructor
    · rintro ⟨hu, htan⟩
      refine ⟨hu, ?_⟩
      intro hmem
      rcases mem_image.mp hmem with ⟨b, hb, rfl⟩
      have hba : b ≠ a := (mem_erase.mp hb).1
      have hcr : cross3 (embed a) (embed b) ≠ 0 := by
        intro h0
        obtain ⟨c, hc⟩ := (cross3_eq_zero_iff (embed_ne_zero a)).mp h0
        have h0' : (1 : ZMod p) = c * 1 := congrFun hc 0
        rw [mul_one] at h0'; rw [← h0', one_smul] at hc
        exact hba (embed_inj hc)
      obtain ⟨c, _, hce⟩ := norm3_exists_smul hcr
      apply htan b (mem_erase.mp hb).2 hba
      rw [hce, dot3_smul_left, dot3_cross3_right, mul_zero]
    · rintro ⟨hu, hnot⟩
      refine ⟨hu, ?_⟩
      intro b hb hba hdotb
      apply hnot
      rw [mem_image]
      refine ⟨b, mem_erase.mpr ⟨hba, hb⟩, ?_⟩
      obtain ⟨hunorm, hdota⟩ := mem_lineThrough.mp hu
      have hcr : cross3 (embed a) (embed b) ≠ 0 := by
        intro h0
        obtain ⟨c, hc⟩ := (cross3_eq_zero_iff (embed_ne_zero a)).mp h0
        have h0' : (1 : ZMod p) = c * 1 := congrFun hc 0
        rw [mul_one] at h0'; rw [← h0', one_smul] at hc
        exact hba (embed_inj hc)
      rw [← norm3_eq_self hunorm, norm3_eq_iff_cross3 hcr (isNorm_ne_zero hunorm)]
      exact cross3_cross3_eq_zero_of_dot3 hdota hdotb
  rw [hpart, card_sdiff_of_subset hsec_sub, hsec_card, card_lineThrough_embed]
  have hle : A.card - 1 ≤ p + 1 := by
    rw [← hsec_card, ← card_lineThrough_embed a]
    exact card_le_card hsec_sub
  omega

lemma card_le_add_two_of_arc {A : Finset (Fin 2 → ZMod p)}
    (harc : ∀ s ⊆ A, s.card = 3 → ¬ Collinear (ZMod p) (s : Set (Fin 2 → ZMod p))) :
    A.card ≤ p + 2 := by
  by_cases hA : A.Nonempty
  · obtain ⟨a, ha⟩ := hA
    have h := card_tangents_add_card_erase harc ha
    omega
  · rw [not_nonempty_iff_eq_empty.mp hA, card_empty]; omega

lemma card_le_add_one_of_arc {A : Finset (Fin 2 → ZMod p)} (hp2 : p ≠ 2)
    (harc : ∀ s ⊆ A, s.card = 3 → ¬ Collinear (ZMod p) (s : Set (Fin 2 → ZMod p))) :
    A.card ≤ p + 1 := by
  have h2 := card_le_add_two_of_arc harc
  by_contra hgt
  have hcard : A.card = p + 2 := by omega
  have hfib : ∀ y : ZMod p, (A.filter fun a => a 1 = y).card = 0 ∨
      (A.filter fun a => a 1 = y).card = 2 := by
    intro y
    set F := A.filter fun a => a 1 = y
    by_cases hF : F.Nonempty
    · right
      have hle2 : F.card ≤ 2 := by
        by_contra h3
        obtain ⟨s, hsF, hscard⟩ := exists_subset_card_eq (show 3 ≤ F.card by omega)
        apply harc s (hsF.trans (filter_subset _ _)) hscard
        rw [collinear_iff_exists_forall_eq_smul_vadd]
        refine ⟨fun i => match i with | 0 => 0 | 1 => y,
          fun i => match i with | 0 => 1 | 1 => 0, ?_⟩
        intro q hq
        have hqF : q ∈ F := hsF hq
        have hqy : q 1 = y := (mem_filter.mp hqF).2
        refine ⟨q 0, ?_⟩
        ext i; fin_cases i <;> simp [hqy]
      obtain ⟨a, haF⟩ := hF
      have haA : a ∈ A := (mem_filter.mp haF).1
      have hay : a 1 = y := (mem_filter.mp haF).2
      have htan0 : (tangents A a).card = 0 := by
        have := card_tangents_add_card_erase harc haA; omega
      let w : Fin 3 → ZMod p := fun i => match i with | 0 => -y | 1 => 0 | 2 => 1
      have hw : w ≠ 0 := fun h => one_ne_zero (congrFun h 2)
      have hu_mem : norm3 w ∈ lineThrough (embed a) := by
        rw [mem_lineThrough]
        refine ⟨norm3_isNorm hw, ?_⟩
        obtain ⟨c, _, hc⟩ := norm3_exists_smul hw
        rw [hc, dot3_smul_left]
        have : dot3 w (embed a) = 0 := by unfold dot3 w embed; dsimp only; rw [hay]; ring
        rw [this, mul_zero]
      have hnot_tan : norm3 w ∉ tangents A a := by
        rw [card_eq_zero.mp htan0]; simp
      simp only [tangents, mem_filter, hu_mem, true_and, not_forall, not_not] at hnot_tan
      obtain ⟨b, hbA, hba, hdotb⟩ := hnot_tan
      obtain ⟨c, hc0, hcw⟩ := norm3_exists_smul hw
      rw [hcw, dot3_smul_left] at hdotb
      have hwb : dot3 w (embed b) = 0 := (mul_eq_zero.mp hdotb).resolve_left hc0
      have hby : b 1 = y := by
        unfold dot3 w embed at hwb; dsimp only at hwb; linear_combination hwb
      have hbF : b ∈ F := mem_filter.mpr ⟨hbA, hby⟩
      have hge2 : 2 ≤ F.card := by
        have hsub : ({a, b} : Finset _) ⊆ F := by
          intro x hx; simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        have h2c : ({a, b} : Finset _).card = 2 := by
          rw [card_insert_of_notMem, card_singleton]; simpa using hba.symm
        have hle := card_le_card hsub
        rwa [h2c] at hle
      omega
    · left; exact card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hF)
  have hsum : ∑ y : ZMod p, (A.filter fun a => a 1 = y).card = A.card := by
    rw [← card_biUnion]
    · congr 1; ext a; simp
    · intro y₁ _ y₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro a ha1 ha2
      exact hne ((mem_filter.mp ha1).2.symm.trans (mem_filter.mp ha2).2)
  have hdvd : 2 ∣ A.card := by
    rw [← hsum]
    apply Finset.dvd_sum
    intro y _
    rcases hfib y with h0 | h2'
    · rw [h0]; exact dvd_zero 2
    · rw [h2']
  rw [hcard] at hdvd
  have h2p : 2 ∣ p := (Nat.dvd_add_left (dvd_refl 2)).mp hdvd
  have hp_prime : p.Prime := Fact.out
  exact hp2 ((hp_prime.eq_one_or_self_of_dvd 2 h2p).resolve_left (by decide)).symm

lemma tangents_disjoint {A : Finset (Fin 2 → ZMod p)} {a b : Fin 2 → ZMod p}
    (_ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) :
    Disjoint (tangents A a) (tangents A b) := by
  rw [Finset.disjoint_left]
  intro u hua hub
  exact (mem_tangents.mp hua).2.2 b hb hab.symm (mem_tangents.mp hub).2.1

end ArcTangents

section SegreTangents

variable {p : ℕ} [Fact p.Prime]

noncomputable def linForm {K : Type*} [CommRing K] (u : Fin 3 → K) : MvPolynomial (Fin 3) K :=
  C (u 0) * X 0 + C (u 1) * X 1 + C (u 2) * X 2

lemma eval_linForm {K : Type*} [Field K] (u v : Fin 3 → K) :
    eval v (linForm u) = dot3 u v := by
  simp [linForm, dot3]

lemma linForm_isHomogeneous {K : Type*} [CommRing K] (u : Fin 3 → K) :
    (linForm u).IsHomogeneous 1 := by
  unfold linForm
  apply IsHomogeneous.add
  · apply IsHomogeneous.add
    · exact (isHomogeneous_X K (0 : Fin 3)).C_mul (u 0)
    · exact (isHomogeneous_X K (1 : Fin 3)).C_mul (u 1)
  · exact (isHomogeneous_X K (2 : Fin 3)).C_mul (u 2)

noncomputable def fPoly (A : Finset (Fin 2 → ZMod p)) (a : Fin 2 → ZMod p) :
    MvPolynomial (Fin 3) (ZMod p) :=
  ∏ u ∈ tangents A a, linForm u

lemma eval_fPoly (A : Finset (Fin 2 → ZMod p)) (a : Fin 2 → ZMod p) (v : Fin 3 → ZMod p) :
    eval v (fPoly A a) = ∏ u ∈ tangents A a, dot3 u v := by
  simp [fPoly, eval_linForm]

lemma eval_fPoly_ne_zero {A : Finset (Fin 2 → ZMod p)} {a b : Fin 2 → ZMod p}
    (hb : b ∈ A) (hba : b ≠ a) : eval (embed b) (fPoly A a) ≠ 0 := by
  rw [eval_fPoly]
  apply Finset.prod_ne_zero_iff.mpr
  intro u hu
  exact (mem_tangents.mp hu).2.2 b hb hba

lemma segre_single_vertex {A : Finset (Fin 2 → ZMod p)}
    (harc : ∀ s ⊆ A, s.card = 3 → ¬ Collinear (ZMod p) (s : Set (Fin 2 → ZMod p)))
    {x y z : Fin 2 → ZMod p} (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (-1 : ZMod p) ^ (tangents A x).card *
      (eval (embed y) (fPoly A x) / eval (embed z) (fPoly A x)) *
      ∏ a ∈ ((A.erase x).erase y).erase z,
        (det3 (embed x) (embed y) (embed a) / det3 (embed x) (embed a) (embed z)) = -1 := by
  classical
  let L := ((lineThrough (embed x)).erase (norm3 (cross3 (embed x) (embed y)))).erase
    (norm3 (cross3 (embed x) (embed z)))
  have hdet_xyz : det3 (embed x) (embed y) (embed z) ≠ 0 :=
    det3_ne_zero_of_arc harc hx hy hz hxy hxz hyz
  have hcr_xy : cross3 (embed x) (embed y) ≠ 0 := cross3_ne_zero_of_det3_ne_zero hdet_xyz
  have hcr_xz : cross3 (embed x) (embed z) ≠ 0 :=
    cross3_ne_zero_of_det3_ne_zero (det3_ne_zero_of_arc harc hx hz hy hxz hxy hyz.symm)
  have hL_nz : ∀ u ∈ L, dot3 u (embed y) ≠ 0 ∧ dot3 u (embed z) ≠ 0 := by
    intro u hu
    have hu_nz : u ≠ norm3 (cross3 (embed x) (embed z)) := (mem_erase.mp hu).1
    have hu1 := (mem_erase.mp hu).2
    have hu_ny : u ≠ norm3 (cross3 (embed x) (embed y)) := (mem_erase.mp hu1).1
    have huL := (mem_erase.mp hu1).2
    obtain ⟨hunorm, hdox⟩ := mem_lineThrough.mp huL
    constructor
    · intro hdoy
      apply hu_ny
      rw [← norm3_eq_self hunorm, eq_comm, norm3_eq_iff_cross3 hcr_xy (isNorm_ne_zero hunorm)]
      exact cross3_cross3_eq_zero_of_dot3 hdox hdoy
    · intro hdoz
      apply hu_nz
      rw [← norm3_eq_self hunorm, eq_comm, norm3_eq_iff_cross3 hcr_xz (isNorm_ne_zero hunorm)]
      exact cross3_cross3_eq_zero_of_dot3 hdox hdoz
  let φ : (Fin 3 → ZMod p) → ZMod p := fun u => -(dot3 u (embed y)) / (dot3 u (embed z))
  have hφ_ne : ∀ u ∈ L, φ u ≠ 0 := by
    intro u hu
    obtain ⟨h1, h2⟩ := hL_nz u hu
    exact div_ne_zero (neg_ne_zero.mpr h1) h2
  have hφ_inj : Set.InjOn φ L := by
    intro u₁ hu₁ u₂ hu₂ heq
    have hL1 := (mem_erase.mp (mem_erase.mp hu₁).2).2
    have hL2 := (mem_erase.mp (mem_erase.mp hu₂).2).2
    obtain ⟨hn1, hx1⟩ := mem_lineThrough.mp hL1
    obtain ⟨hn2, hx2⟩ := mem_lineThrough.mp hL2
    obtain ⟨_, hz1⟩ := hL_nz u₁ hu₁
    obtain ⟨_, hz2⟩ := hL_nz u₂ hu₂
    have hprop : dot3 u₁ (embed y) * dot3 u₂ (embed z) = dot3 u₂ (embed y) * dot3 u₁ (embed z) := by
      have h1 : -(dot3 u₁ (embed y)) * dot3 u₂ (embed z) =
          -(dot3 u₂ (embed y)) * dot3 u₁ (embed z) := (div_eq_div_iff hz1 hz2).mp heq
      linear_combination -h1
    let c := dot3 u₁ (embed z) / dot3 u₂ (embed z)
    apply isNorm_eq_of_smul hn1 hn2 (c := c)
    ext i
    have hbasis : ∀ v : Fin 3 → ZMod p, dot3 u₁ v = c * dot3 u₂ v := by
      intro v
      have hcr := cramer3 (embed x) (embed y) (embed z) v
      have hd1 : det3 (embed x) (embed y) (embed z) * dot3 u₁ v =
          det3 (embed x) (embed y) (embed z) * (c * dot3 u₂ v) := by
        rw [← dot3_smul_right, hcr, dot3_add_right, dot3_add_right,
          dot3_smul_right, dot3_smul_right, dot3_smul_right, hx1, mul_zero, zero_add]
        have h2 : det3 (embed x) (embed y) (embed z) * dot3 u₂ v =
            det3 (embed x) v (embed z) * dot3 u₂ (embed y) +
            det3 (embed x) (embed y) v * dot3 u₂ (embed z) := by
          rw [← dot3_smul_right, hcr, dot3_add_right, dot3_add_right,
            dot3_smul_right, dot3_smul_right, dot3_smul_right, hx2, mul_zero, zero_add]
        rw [mul_left_comm, h2]
        have hcy : c * dot3 u₂ (embed y) = dot3 u₁ (embed y) := by
          apply mul_left_cancel₀ hz2
          calc dot3 u₂ (embed z) * (c * dot3 u₂ (embed y))
              = (c * dot3 u₂ (embed z)) * dot3 u₂ (embed y) := by ring
            _ = dot3 u₁ (embed z) * dot3 u₂ (embed y) := by rw [div_mul_cancel₀ _ hz2]
            _ = dot3 u₂ (embed z) * dot3 u₁ (embed y) := by linear_combination -hprop
        have hcz : c * dot3 u₂ (embed z) = dot3 u₁ (embed z) := div_mul_cancel₀ _ hz2
        rw [mul_add, ← mul_assoc, mul_comm c, mul_assoc, hcy,
          ← mul_assoc, mul_comm c, mul_assoc, hcz]
      exact mul_left_cancel₀ hdet_xyz hd1
    have hi := hbasis (Pi.single i 1)
    have hdot_single : ∀ w : Fin 3 → ZMod p, dot3 w (Pi.single i 1) = w i := by
      intro w; fin_cases i <;> simp [dot3]
    rw [hdot_single, hdot_single] at hi
    exact hi
  have hxy_in : norm3 (cross3 (embed x) (embed y)) ∈ lineThrough (embed x) := by
    rw [mem_lineThrough]
    obtain ⟨c, _, hc⟩ := norm3_exists_smul hcr_xy
    exact ⟨norm3_isNorm hcr_xy, by rw [hc, dot3_smul_left, dot3_cross3_left, mul_zero]⟩
  have hxz_in : norm3 (cross3 (embed x) (embed z)) ∈
      (lineThrough (embed x)).erase (norm3 (cross3 (embed x) (embed y))) := by
    rw [mem_erase]
    refine ⟨?_, ?_⟩
    · intro heq
      have hcc := (norm3_eq_iff_cross3 hcr_xz hcr_xy).mp heq
      rw [cross3_cross3] at hcc
      have h0 := congrFun hcc 0
      simp only [Pi.smul_apply, smul_eq_mul, embed_zero, mul_one, Pi.zero_apply] at h0
      rw [det3_swap23, neg_eq_zero] at h0
      exact hdet_xyz h0
    · rw [mem_lineThrough]
      obtain ⟨c, _, hc⟩ := norm3_exists_smul hcr_xz
      exact ⟨norm3_isNorm hcr_xz, by rw [hc, dot3_smul_left, dot3_cross3_left, mul_zero]⟩
  have hL_card : L.card = p - 1 := by
    dsimp only [L]
    rw [card_erase_of_mem hxz_in, card_erase_of_mem hxy_in, card_lineThrough_embed]
    have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  have hprod_L : ∏ u ∈ L, φ u = -1 := by
    let ψ : (Fin 3 → ZMod p) → (ZMod p)ˣ := fun u =>
      if h : φ u ≠ 0 then Units.mk0 (φ u) h else 1
    have hψ_val : ∀ u ∈ L, (ψ u : ZMod p) = φ u := by
      intro u hu; dsimp only [ψ]; split_ifs with h
      · rfl
      · exact absurd (hφ_ne u hu) h
    have hψ_inj : Set.InjOn ψ L := by
      intro u₁ hu₁ u₂ hu₂ heq
      apply hφ_inj hu₁ hu₂
      have := congrArg Units.val heq
      rwa [hψ_val u₁ hu₁, hψ_val u₂ hu₂] at this
    have hψ_img : L.image ψ = univ := by
      apply eq_univ_of_card
      rw [card_image_of_injOn hψ_inj, hL_card, Fintype.card_units, ZMod.card]
    have hprod_units : (∏ r : (ZMod p)ˣ, (r : ZMod p)) = -1 := by
      have h := congrArg Units.val (FiniteField.prod_univ_units_id_eq_neg_one (K := ZMod p))
      simpa using h
    rw [← Finset.prod_congr rfl hψ_val, ← Finset.prod_image (by intro a ha b hb h; exact hψ_inj ha hb h),
      hψ_img, hprod_units]
  let B := ((A.erase x).erase y).erase z
  let secB := B.image fun a => norm3 (cross3 (embed x) (embed a))
  have hB_mem : ∀ a ∈ B, a ∈ A ∧ a ≠ x ∧ a ≠ y ∧ a ≠ z := by
    intro a ha
    have h1 := mem_erase.mp ha
    have h2 := mem_erase.mp h1.2
    have h3 := mem_erase.mp h2.2
    exact ⟨h3.2, h3.1, h2.1, h1.1⟩
  have htan_sub : tangents A x ⊆ L := by
    intro u hu
    have huL := (mem_filter.mp hu).1
    have htan := (mem_filter.mp hu).2
    refine mem_erase.mpr ⟨?_, mem_erase.mpr ⟨?_, huL⟩⟩
    · rintro rfl
      obtain ⟨c, _, hc⟩ := norm3_exists_smul hcr_xz
      exact htan z hz hxz.symm (by rw [hc, dot3_smul_left, dot3_cross3_right, mul_zero])
    · rintro rfl
      obtain ⟨c, _, hc⟩ := norm3_exists_smul hcr_xy
      exact htan y hy hxy.symm (by rw [hc, dot3_smul_left, dot3_cross3_right, mul_zero])
  have hsecB_sub : secB ⊆ L := by
    intro u hu
    rcases mem_image.mp hu with ⟨a, haB, rfl⟩
    obtain ⟨haA, hax, hay, haz⟩ := hB_mem a haB
    have hcr_xa : cross3 (embed x) (embed a) ≠ 0 :=
      cross3_ne_zero_of_det3_ne_zero (det3_ne_zero_of_arc harc hx haA hy hax.symm hxy hay)
    refine mem_erase.mpr ⟨?_, mem_erase.mpr ⟨?_, ?_⟩⟩
    · intro heq
      have hcc := (norm3_eq_iff_cross3 hcr_xa hcr_xz).mp heq
      rw [cross3_cross3] at hcc
      have h0 := congrFun hcc 0
      simp only [Pi.smul_apply, smul_eq_mul, embed_zero, mul_one, Pi.zero_apply] at h0
      exact det3_ne_zero_of_arc harc hx haA hz hax.symm hxz haz h0
    · intro heq
      have hcc := (norm3_eq_iff_cross3 hcr_xa hcr_xy).mp heq
      rw [cross3_cross3] at hcc
      have h0 := congrFun hcc 0
      simp only [Pi.smul_apply, smul_eq_mul, embed_zero, mul_one, Pi.zero_apply] at h0
      exact det3_ne_zero_of_arc harc hx haA hy hax.symm hxy hay h0
    · rw [mem_lineThrough]
      obtain ⟨c, _, hc⟩ := norm3_exists_smul hcr_xa
      exact ⟨norm3_isNorm hcr_xa, by rw [hc, dot3_smul_left, dot3_cross3_left, mul_zero]⟩
  have hdisj : Disjoint (tangents A x) secB := by
    rw [Finset.disjoint_left]
    intro u hut hus
    rcases mem_image.mp hus with ⟨a, haB, rfl⟩
    obtain ⟨haA, hax, hay, _⟩ := hB_mem a haB
    have hcr_xa : cross3 (embed x) (embed a) ≠ 0 :=
      cross3_ne_zero_of_det3_ne_zero (det3_ne_zero_of_arc harc hx haA hy hax.symm hxy hay)
    obtain ⟨c, _, hc⟩ := norm3_exists_smul hcr_xa
    exact (mem_tangents.mp hut).2.2 a haA hax (by rw [hc, dot3_smul_left, dot3_cross3_right, mul_zero])
  have hL_eq : L = tangents A x ∪ secB := by
    apply Finset.Subset.antisymm
    · intro u hu
      by_cases ht : u ∈ tangents A x
      · exact mem_union_left _ ht
      · apply mem_union_right
        have huL := (mem_erase.mp (mem_erase.mp hu).2).2
        simp only [tangents, mem_filter, huL, true_and, not_forall, not_not] at ht
        obtain ⟨a, haA, hax, hdot_a⟩ := ht
        obtain ⟨hny, hnz⟩ := hL_nz u hu
        have hay : a ≠ y := fun h => hny (h ▸ hdot_a)
        have haz : a ≠ z := fun h => hnz (h ▸ hdot_a)
        have haB : a ∈ B := mem_erase.mpr ⟨haz, mem_erase.mpr ⟨hay, mem_erase.mpr ⟨hax, haA⟩⟩⟩
        rw [mem_image]
        refine ⟨a, haB, ?_⟩
        obtain ⟨hunorm, hdox⟩ := mem_lineThrough.mp huL
        have hcr_xa : cross3 (embed x) (embed a) ≠ 0 :=
          cross3_ne_zero_of_det3_ne_zero (det3_ne_zero_of_arc harc hx haA hy hax.symm hxy hay)
        rw [← norm3_eq_self hunorm, norm3_eq_iff_cross3 hcr_xa (isNorm_ne_zero hunorm)]
        exact cross3_cross3_eq_zero_of_dot3 hdox hdot_a
    · exact union_subset htan_sub hsecB_sub
  have hprod_tan : ∏ u ∈ tangents A x, φ u =
      (-1 : ZMod p) ^ (tangents A x).card *
        (eval (embed y) (fPoly A x) / eval (embed z) (fPoly A x)) := by
    rw [eval_fPoly, eval_fPoly, ← Finset.prod_div_distrib]
    dsimp only [φ]
    calc ∏ u ∈ tangents A x, (-dot3 u (embed y) / dot3 u (embed z))
        = ∏ u ∈ tangents A x, ((-1 : ZMod p) * (dot3 u (embed y) / dot3 u (embed z))) := by
            apply Finset.prod_congr rfl; intro u _; ring
      _ = (-1 : ZMod p) ^ (tangents A x).card * ∏ u ∈ tangents A x, (dot3 u (embed y) / dot3 u (embed z)) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hsecB_inj : Set.InjOn (fun a => norm3 (cross3 (embed x) (embed a))) B := by
    intro a₁ ha₁ a₂ ha₂ heq
    by_contra hne
    obtain ⟨h1A, h1x, h1y, _⟩ := hB_mem a₁ ha₁
    obtain ⟨h2A, h2x, h2y, _⟩ := hB_mem a₂ ha₂
    have hcr1 : cross3 (embed x) (embed a₁) ≠ 0 :=
      cross3_ne_zero_of_det3_ne_zero (det3_ne_zero_of_arc harc hx h1A hy h1x.symm hxy h1y)
    have hcr2 : cross3 (embed x) (embed a₂) ≠ 0 :=
      cross3_ne_zero_of_det3_ne_zero (det3_ne_zero_of_arc harc hx h2A hy h2x.symm hxy h2y)
    have hcc := (norm3_eq_iff_cross3 hcr1 hcr2).mp heq
    rw [cross3_cross3] at hcc
    have h0 := congrFun hcc 0
    simp only [Pi.smul_apply, smul_eq_mul, embed_zero, mul_one, Pi.zero_apply] at h0
    exact det3_ne_zero_of_arc harc hx h1A h2A h1x.symm h2x.symm hne h0
  have hprod_sec : ∏ u ∈ secB, φ u =
      ∏ a ∈ B, (det3 (embed x) (embed y) (embed a) / det3 (embed x) (embed a) (embed z)) := by
    rw [Finset.prod_image (by intro a ha b hb h; exact hsecB_inj ha hb h)]
    apply Finset.prod_congr rfl
    intro a haB
    obtain ⟨haA, hax, hay, haz⟩ := hB_mem a haB
    have hcr_xa : cross3 (embed x) (embed a) ≠ 0 :=
      cross3_ne_zero_of_det3_ne_zero (det3_ne_zero_of_arc harc hx haA hy hax.symm hxy hay)
    obtain ⟨c, hc0, hce⟩ := norm3_exists_smul hcr_xa
    dsimp only [φ]
    rw [hce, dot3_smul_left, dot3_smul_left]
    have hdy : dot3 (cross3 (embed x) (embed a)) (embed y) = -det3 (embed x) (embed y) (embed a) := by
      unfold det3 dot3 cross3; dsimp only; ring
    have hdz : dot3 (cross3 (embed x) (embed a)) (embed z) = det3 (embed x) (embed a) (embed z) := rfl
    rw [hdy, hdz, mul_neg, neg_neg, mul_div_mul_left _ _ hc0]
  rw [hL_eq, Finset.prod_union hdisj, hprod_tan, hprod_sec] at hprod_L
  exact hprod_L

lemma card_tangents_eq {A : Finset (Fin 2 → ZMod p)}
    (harc : ∀ s ⊆ A, s.card = 3 → ¬ Collinear (ZMod p) (s : Set (Fin 2 → ZMod p)))
    {a : Fin 2 → ZMod p} (ha : a ∈ A) :
    (tangents A a).card = p + 2 - A.card := by
  have h1 := card_tangents_add_card_erase harc ha
  have h2 := card_le_add_two_of_arc harc
  have hpos : 1 ≤ A.card := card_pos.mpr ⟨a, ha⟩
  omega

lemma segre_lemma_of_tangents {A : Finset (Fin 2 → ZMod p)}
    (harc : ∀ s ⊆ A, s.card = 3 → ¬ Collinear (ZMod p) (s : Set (Fin 2 → ZMod p)))
    {x y z : Fin 2 → ZMod p} (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    eval (embed y) (fPoly A x) * eval (embed z) (fPoly A y) * eval (embed x) (fPoly A z) =
      (-1 : ZMod p) ^ ((p + 2 - A.card) + 1) *
        (eval (embed x) (fPoly A y) * eval (embed y) (fPoly A z) * eval (embed z) (fPoly A x)) := by
  have ht_x := card_tangents_eq harc hx
  have ht_y := card_tangents_eq harc hy
  have ht_z := card_tangents_eq harc hz
  have h1 := segre_single_vertex harc hx hy hz hxy hxz hyz
  have h2 := segre_single_vertex harc hy hz hx hyz hxy.symm hxz.symm
  have h3 := segre_single_vertex harc hz hx hy hxz.symm hyz.symm hxy
  rw [ht_x] at h1; rw [ht_y] at h2; rw [ht_z] at h3
  set t := p + 2 - A.card
  set B := ((A.erase x).erase y).erase z
  have hB2 : ((A.erase y).erase z).erase x = B := by
    ext a; simp only [B, mem_erase]; tauto
  have hB3 : ((A.erase z).erase x).erase y = B := by
    ext a; simp only [B, mem_erase]; tauto
  rw [hB2] at h2; rw [hB3] at h3
  have hprod_det :
      (∏ a ∈ B, det3 (embed x) (embed y) (embed a) / det3 (embed x) (embed a) (embed z)) *
      (∏ a ∈ B, det3 (embed y) (embed z) (embed a) / det3 (embed y) (embed a) (embed x)) *
      (∏ a ∈ B, det3 (embed z) (embed x) (embed a) / det3 (embed z) (embed a) (embed y)) = 1 := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro a haB
    have h1' := mem_erase.mp haB
    have h2' := mem_erase.mp h1'.2
    have h3' := mem_erase.mp h2'.2
    have d1 : det3 (embed x) (embed a) (embed z) ≠ 0 :=
      det3_ne_zero_of_arc harc hx h3'.2 hz h3'.1.symm hxz h1'.1
    have d2 : det3 (embed y) (embed a) (embed x) ≠ 0 :=
      det3_ne_zero_of_arc harc hy h3'.2 hx h2'.1.symm hxy.symm h3'.1
    have d3 : det3 (embed z) (embed a) (embed y) ≠ 0 :=
      det3_ne_zero_of_arc harc hz h3'.2 hy h1'.1.symm hyz.symm h2'.1
    have e1 : det3 (embed x) (embed y) (embed a) = det3 (embed y) (embed a) (embed x) :=
      det3_cyclic _ _ _
    have e2 : det3 (embed y) (embed z) (embed a) = det3 (embed z) (embed a) (embed y) :=
      det3_cyclic _ _ _
    have e3 : det3 (embed z) (embed x) (embed a) = det3 (embed x) (embed a) (embed z) :=
      det3_cyclic _ _ _
    rw [e1, e2, e3, div_mul_div_comm, div_mul_div_comm]
    have num_eq : det3 (embed y) (embed a) (embed x) * det3 (embed z) (embed a) (embed y) *
        det3 (embed x) (embed a) (embed z) =
        det3 (embed x) (embed a) (embed z) * det3 (embed y) (embed a) (embed x) *
        det3 (embed z) (embed a) (embed y) := by ring
    rw [num_eq, div_self (mul_ne_zero (mul_ne_zero d1 d2) d3)]
  have hmul :
      ((-1 : ZMod p) ^ t * (eval (embed y) (fPoly A x) / eval (embed z) (fPoly A x)) *
        ∏ a ∈ B, det3 (embed x) (embed y) (embed a) / det3 (embed x) (embed a) (embed z)) *
      ((-1 : ZMod p) ^ t * (eval (embed z) (fPoly A y) / eval (embed x) (fPoly A y)) *
        ∏ a ∈ B, det3 (embed y) (embed z) (embed a) / det3 (embed y) (embed a) (embed x)) *
      ((-1 : ZMod p) ^ t * (eval (embed x) (fPoly A z) / eval (embed y) (fPoly A z)) *
        ∏ a ∈ B, det3 (embed z) (embed x) (embed a) / det3 (embed z) (embed a) (embed y)) =
      (-1 : ZMod p) * (-1) * (-1) := by
    rw [h1, h2, h3]
  have hrearr :
      ((-1 : ZMod p) ^ t) ^ 3 *
        ((eval (embed y) (fPoly A x) * eval (embed z) (fPoly A y) * eval (embed x) (fPoly A z)) /
         (eval (embed z) (fPoly A x) * eval (embed x) (fPoly A y) * eval (embed y) (fPoly A z))) *
      ((∏ a ∈ B, det3 (embed x) (embed y) (embed a) / det3 (embed x) (embed a) (embed z)) *
       (∏ a ∈ B, det3 (embed y) (embed z) (embed a) / det3 (embed y) (embed a) (embed x)) *
       (∏ a ∈ B, det3 (embed z) (embed x) (embed a) / det3 (embed z) (embed a) (embed y))) =
      -1 := by
    calc _ = _ := by ring
      _ = (-1 : ZMod p) * (-1) * (-1) := hmul
      _ = -1 := by ring
  rw [hprod_det, mul_one] at hrearr
  have hsign : ((-1 : ZMod p) ^ t) ^ 3 * (-1 : ZMod p) ^ t = 1 := by
    rw [← pow_mul, ← pow_add, show t * 3 + t = 2 * (2 * t) by omega, pow_mul]
    norm_num
  have hdiv :
      (eval (embed y) (fPoly A x) * eval (embed z) (fPoly A y) * eval (embed x) (fPoly A z)) /
      (eval (embed z) (fPoly A x) * eval (embed x) (fPoly A y) * eval (embed y) (fPoly A z)) =
      (-1 : ZMod p) ^ (t + 1) := by
    have hmul2 := congrArg ((-1 : ZMod p) ^ t * ·) hrearr
    rw [← mul_assoc, mul_comm ((-1 : ZMod p) ^ t), hsign, one_mul] at hmul2
    rw [hmul2, pow_succ]
  have hden : eval (embed z) (fPoly A x) * eval (embed x) (fPoly A y) * eval (embed y) (fPoly A z) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (eval_fPoly_ne_zero hz hxz.symm) (eval_fPoly_ne_zero hx hxy))
      (eval_fPoly_ne_zero hy hyz)
  have hfin := (div_eq_iff hden).mp hdiv
  linear_combination hfin

noncomputable def scaleA (A : Finset (Fin 2 → ZMod p)) (e a : Fin 2 → ZMod p) : ZMod p :=
  if a = e then 1
  else (eval (embed a) (fPoly A e) / eval (embed e) (fPoly A a)) ^ 2

lemma scaleA_ne_zero {A : Finset (Fin 2 → ZMod p)} {e a : Fin 2 → ZMod p}
    (he : e ∈ A) (ha : a ∈ A) : scaleA A e a ≠ 0 := by
  unfold scaleA
  split_ifs with h
  · exact one_ne_zero
  · exact pow_ne_zero 2 (div_ne_zero (eval_fPoly_ne_zero ha h) (eval_fPoly_ne_zero he (Ne.symm h)))

noncomputable def Fval (A : Finset (Fin 2 → ZMod p)) (e a b : Fin 2 → ZMod p) : ZMod p :=
  scaleA A e a * (eval (embed b) (fPoly A a)) ^ 2

lemma Fval_symm {A : Finset (Fin 2 → ZMod p)}
    (harc : ∀ s ⊆ A, s.card = 3 → ¬ Collinear (ZMod p) (s : Set (Fin 2 → ZMod p)))
    {e a b : Fin 2 → ZMod p} (he : e ∈ A) (ha : a ∈ A) (hb : b ∈ A) :
    Fval A e a b = Fval A e b a := by
  by_cases hab : a = b
  · subst hab; rfl
  by_cases hae : a = e
  · subst hae
    unfold Fval scaleA
    have hbe : b ≠ a := Ne.symm hab
    simp only [ite_true, hbe, ite_false]
    rw [one_mul, div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 (eval_fPoly_ne_zero ha (Ne.symm hbe)))]
  by_cases hbe : b = e
  · subst hbe
    unfold Fval scaleA
    simp only [ite_true, hae, ite_false]
    rw [one_mul, div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 (eval_fPoly_ne_zero hb (Ne.symm hae)))]
  have hseg := segre_lemma_of_tangents harc ha hb he hab hae hbe
  have hsq := congrArg (· ^ 2) hseg
  have hm1 : ((-1 : ZMod p) ^ (p + 2 - A.card + 1)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hsq' : (eval (embed b) (fPoly A a) * eval (embed e) (fPoly A b) * eval (embed a) (fPoly A e)) ^ 2 =
      (eval (embed a) (fPoly A b) * eval (embed b) (fPoly A e) * eval (embed e) (fPoly A a)) ^ 2 := by
    calc _ = ((-1 : ZMod p) ^ (p + 2 - A.card + 1) *
              (eval (embed a) (fPoly A b) * eval (embed b) (fPoly A e) * eval (embed e) (fPoly A a))) ^ 2 := hsq
      _ = ((-1 : ZMod p) ^ (p + 2 - A.card + 1)) ^ 2 *
          (eval (embed a) (fPoly A b) * eval (embed b) (fPoly A e) * eval (embed e) (fPoly A a)) ^ 2 := mul_pow _ _ _
      _ = _ := by rw [hm1, one_mul]
  unfold Fval scaleA
  simp only [hae, hbe, ite_false]
  have hae_ne : eval (embed e) (fPoly A a) ≠ 0 := eval_fPoly_ne_zero he (Ne.symm hae)
  have hbe_ne : eval (embed e) (fPoly A b) ≠ 0 := eval_fPoly_ne_zero he (Ne.symm hbe)
  rw [div_pow, div_pow, div_mul_eq_mul_div, div_mul_eq_mul_div]
  rw [div_eq_div_iff (pow_ne_zero 2 hae_ne) (pow_ne_zero 2 hbe_ne)]
  linear_combination hsq'

end SegreTangents

section HomogUtils

lemma weight_one_eq_degree {σ : Type*} (m : σ →₀ ℕ) :
    Finsupp.weight (1 : σ → ℕ) m = Finsupp.degree m := by
  simp [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum]

lemma isHomogeneous_sum_eq {K : Type*} [CommSemiring K] {σ : Type*} [Fintype σ]
    {P : MvPolynomial σ K} {d : ℕ} (hP : P.IsHomogeneous d) {m : σ →₀ ℕ} (hm : m ∈ P.support) :
    ∑ i : σ, m i = d := by
  have h := hP (MvPolynomial.mem_support_iff.mp hm)
  rw [weight_one_eq_degree, Finsupp.degree_apply] at h
  rw [← h]
  exact (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => Finsupp.notMem_support_iff.mp hi)).symm

variable {K : Type*} [Field K]

lemma isHomogeneous_eval_smul {σ : Type*} [Fintype σ] {P : MvPolynomial σ K} {d : ℕ}
    (hP : P.IsHomogeneous d) (c : K) (v : σ → K) :
    eval (c • v) P = c ^ d * eval v P := by
  rw [P.as_sum, map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [eval_monomial, eval_monomial]
  have hdeg : ∑ i : σ, m i = d := isHomogeneous_sum_eq hP hm
  have hprod : (m.prod fun i e => (c * v i) ^ e) = c ^ d * (m.prod fun i e => v i ^ e) := by
    rw [Finsupp.prod_fintype _ _ (fun _ => by simp), Finsupp.prod_fintype _ _ (fun _ => by simp)]
    calc ∏ i : σ, (c * v i) ^ m i
        = ∏ i : σ, (c ^ m i * v i ^ m i) := by
            apply Finset.prod_congr rfl; intro i _; exact mul_pow _ _ _
      _ = (∏ i : σ, c ^ m i) * (∏ i : σ, v i ^ m i) := Finset.prod_mul_distrib
      _ = c ^ (∑ i : σ, m i) * (∏ i : σ, v i ^ m i) := by rw [Finset.prod_pow_eq_pow_sum]
      _ = c ^ d * (∏ i : σ, v i ^ m i) := by rw [hdeg]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hprod]; ring

lemma isHomogeneous_of_dvd {σ : Type*} {Φ P H : MvPolynomial σ K} {n : ℕ}
    (hΦ : Φ.IsHomogeneous n) (hΦ0 : Φ ≠ 0) (hmul : P * H = Φ) :
    P.IsHomogeneous P.totalDegree ∧ H.IsHomogeneous H.totalDegree ∧
      P.totalDegree + H.totalDegree = n := by
  classical
  have hP0 : P ≠ 0 := by intro h; rw [h, zero_mul] at hmul; exact hΦ0 hmul.symm
  have hH0 : H ≠ 0 := by intro h; rw [h, mul_zero] at hmul; exact hΦ0 hmul.symm
  let S_P := P.support.image Finsupp.degree
  let S_H := H.support.image Finsupp.degree
  have hSP_ne : S_P.Nonempty := (MvPolynomial.support_nonempty.mpr hP0).image _
  have hSH_ne : S_H.Nonempty := (MvPolynomial.support_nonempty.mpr hH0).image _
  let a_min := S_P.min' hSP_ne
  let a_max := S_P.max' hSP_ne
  let b_min := S_H.min' hSH_ne
  let b_max := S_H.max' hSH_ne
  have hc_ne : ∀ (Q : MvPolynomial σ K) (d : ℕ),
      d ∈ Q.support.image Finsupp.degree → homogeneousComponent d Q ≠ 0 := by
    intro Q d hd h0
    rcases mem_image.mp hd with ⟨m, hm, rfl⟩
    have hc := congrArg (fun f : MvPolynomial σ K => f.coeff m) h0
    rw [coeff_homogeneousComponent, MvPolynomial.coeff_zero] at hc
    simp only [ite_true] at hc
    exact MvPolynomial.mem_support_iff.mp hm hc
  have hΦ_comp_zero : ∀ k : ℕ, k ≠ n → homogeneousComponent k Φ = 0 := by
    intro k hkn
    ext m
    rw [coeff_homogeneousComponent, MvPolynomial.coeff_zero]
    split_ifs with hdeg
    · by_contra hne
      have h := hΦ hne
      rw [weight_one_eq_degree] at h
      exact hkn (hdeg.symm.trans h)
    · rfl
  have hmin_eq : a_min + b_min = n := by
    have hcomp : homogeneousComponent (a_min + b_min) (P * H) =
        homogeneousComponent a_min P * homogeneousComponent b_min H := by
      ext m
      rw [coeff_homogeneousComponent, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
      split_ifs with hdeg
      · apply Finset.sum_congr rfl
        intro ⟨x, y⟩ hxy
        have hsum : Finsupp.degree x + Finsupp.degree y = a_min + b_min := by
          rw [← map_add, HasAntidiagonal.mem_antidiagonal.mp hxy, hdeg]
        rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
        by_cases hx : P.coeff x = 0
        · simp [hx]
        · by_cases hy : H.coeff y = 0
          · simp [hy]
          · have hxa : a_min ≤ Finsupp.degree x :=
              Finset.min'_le S_P _ (mem_image.mpr ⟨x, MvPolynomial.mem_support_iff.mpr hx, rfl⟩)
            have hyb : b_min ≤ Finsupp.degree y :=
              Finset.min'_le S_H _ (mem_image.mpr ⟨y, MvPolynomial.mem_support_iff.mpr hy, rfl⟩)
            have hxe : Finsupp.degree x = a_min := by omega
            have hye : Finsupp.degree y = b_min := by omega
            simp [hxe, hye]
      · symm
        apply Finset.sum_eq_zero
        intro ⟨x, y⟩ hxy
        have hsum : Finsupp.degree x + Finsupp.degree y = Finsupp.degree m := by
          rw [← map_add, HasAntidiagonal.mem_antidiagonal.mp hxy]
        rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
        split_ifs with hx hy
        · exact absurd (by rw [← hsum, hx, hy]) hdeg
        · ring
        · ring
        · ring
    have hne : homogeneousComponent (a_min + b_min) Φ ≠ 0 := by
      rw [← hmul, hcomp]
      exact mul_ne_zero (hc_ne P a_min (Finset.min'_mem _ _)) (hc_ne H b_min (Finset.min'_mem _ _))
    by_contra hneq
    exact hne (hΦ_comp_zero _ hneq)
  have hmax_eq : a_max + b_max = n := by
    have hcomp : homogeneousComponent (a_max + b_max) (P * H) =
        homogeneousComponent a_max P * homogeneousComponent b_max H := by
      ext m
      rw [coeff_homogeneousComponent, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
      split_ifs with hdeg
      · apply Finset.sum_congr rfl
        intro ⟨x, y⟩ hxy
        have hsum : Finsupp.degree x + Finsupp.degree y = a_max + b_max := by
          rw [← map_add, HasAntidiagonal.mem_antidiagonal.mp hxy, hdeg]
        rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
        by_cases hx : P.coeff x = 0
        · simp [hx]
        · by_cases hy : H.coeff y = 0
          · simp [hy]
          · have hxa : Finsupp.degree x ≤ a_max :=
              Finset.le_max' S_P _ (mem_image.mpr ⟨x, MvPolynomial.mem_support_iff.mpr hx, rfl⟩)
            have hyb : Finsupp.degree y ≤ b_max :=
              Finset.le_max' S_H _ (mem_image.mpr ⟨y, MvPolynomial.mem_support_iff.mpr hy, rfl⟩)
            have hxe : Finsupp.degree x = a_max := by omega
            have hye : Finsupp.degree y = b_max := by omega
            simp [hxe, hye]
      · symm
        apply Finset.sum_eq_zero
        intro ⟨x, y⟩ hxy
        have hsum : Finsupp.degree x + Finsupp.degree y = Finsupp.degree m := by
          rw [← map_add, HasAntidiagonal.mem_antidiagonal.mp hxy]
        rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
        split_ifs with hx hy
        · exact absurd (by rw [← hsum, hx, hy]) hdeg
        · ring
        · ring
        · ring
    have hne : homogeneousComponent (a_max + b_max) Φ ≠ 0 := by
      rw [← hmul, hcomp]
      exact mul_ne_zero (hc_ne P a_max (Finset.max'_mem _ _)) (hc_ne H b_max (Finset.max'_mem _ _))
    by_contra hneq
    exact hne (hΦ_comp_zero _ hneq)
  have ha_le : a_min ≤ a_max := Finset.min'_le _ _ (Finset.max'_mem _ _)
  have hb_le : b_min ≤ b_max := Finset.min'_le _ _ (Finset.max'_mem _ _)
  have ha_eq : a_min = a_max := by omega
  have hb_eq : b_min = b_max := by omega
  have hPh : P.IsHomogeneous a_min := by
    intro m hm
    have hmem : Finsupp.degree m ∈ S_P := mem_image.mpr ⟨m, MvPolynomial.mem_support_iff.mpr hm, rfl⟩
    have h1 := Finset.min'_le S_P _ hmem
    have h2 := Finset.le_max' S_P _ hmem
    rw [weight_one_eq_degree]
    omega
  have hHh : H.IsHomogeneous b_min := by
    intro m hm
    have hmem : Finsupp.degree m ∈ S_H := mem_image.mpr ⟨m, MvPolynomial.mem_support_iff.mpr hm, rfl⟩
    have h1 := Finset.min'_le S_H _ hmem
    have h2 := Finset.le_max' S_H _ hmem
    rw [weight_one_eq_degree]
    omega
  have hPd : P.totalDegree = a_min := hPh.totalDegree hP0
  have hHd : H.totalDegree = b_min := hHh.totalDegree hH0
  exact ⟨hPd ▸ hPh, hHd ▸ hHh, by omega⟩

lemma isHomogeneous_zero_eq_C {σ : Type*} {P : MvPolynomial σ K} (hP : P.IsHomogeneous 0) :
    P = C (P.coeff 0) := by
  classical
  ext m
  rw [MvPolynomial.coeff_C]
  split_ifs with hm
  · subst hm; rfl
  · by_contra hne
    have h := hP hne
    rw [weight_one_eq_degree] at h
    apply hm
    ext i
    have hle : m i ≤ Finsupp.degree m := by
      rw [Finsupp.degree_apply]
      by_cases hi : i ∈ m.support
      · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
      · rw [Finsupp.notMem_support_iff.mp hi]; exact Nat.zero_le _
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    omega

noncomputable def dehomog1 : MvPolynomial (Fin 2) K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => match i with | 0 => Polynomial.X | 1 => 1)

noncomputable def dehomog0 : MvPolynomial (Fin 2) K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => match i with | 0 => 1 | 1 => Polynomial.X)

lemma eval_dehomog1 (P : MvPolynomial (Fin 2) K) (r : K) :
    Polynomial.eval r (dehomog1 P) = eval (fun i => match i with | 0 => r | 1 => 1) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [dehomog1]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
    fin_cases i
    · rw [map_mul, map_mul, Polynomial.eval_mul, hp]; simp [dehomog1]
    · rw [map_mul, map_mul, Polynomial.eval_mul, hp]; simp [dehomog1]

lemma eval_dehomog0 (P : MvPolynomial (Fin 2) K) (r : K) :
    Polynomial.eval r (dehomog0 P) = eval (fun i => match i with | 0 => 1 | 1 => r) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [dehomog0]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
    fin_cases i
    · rw [map_mul, map_mul, Polynomial.eval_mul, hp]; simp [dehomog0]
    · rw [map_mul, map_mul, Polynomial.eval_mul, hp]; simp [dehomog0]

lemma dehomog1_monomial (m : Fin 2 →₀ ℕ) (a : K) :
    dehomog1 (monomial m a) = Polynomial.C a * Polynomial.X ^ (m 0) := by
  unfold dehomog1
  rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
  simp

lemma dehomog0_monomial (m : Fin 2 →₀ ℕ) (a : K) :
    dehomog0 (monomial m a) = Polynomial.C a * Polynomial.X ^ (m 1) := by
  unfold dehomog0
  rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
  simp

lemma coeff_dehomog1_of_isHomogeneous {P : MvPolynomial (Fin 2) K} {d : ℕ}
    (hP : P.IsHomogeneous d) (k : ℕ) :
    (dehomog1 P).coeff k =
      if k ≤ d then P.coeff (Finsupp.single 0 k + Finsupp.single 1 (d - k)) else 0 := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum, Polynomial.finset_sum_coeff]
  have hdeg : ∀ m ∈ P.support, m 0 + m 1 = d := by
    intro m hm
    have h := isHomogeneous_sum_eq hP hm
    rwa [Fin.sum_univ_two] at h
  split_ifs with hkd
  · let m₀ : Fin 2 →₀ ℕ := Finsupp.single 0 k + Finsupp.single 1 (d - k)
    have hm₀_0 : m₀ 0 = k := by simp [m₀]
    have hm₀_1 : m₀ 1 = d - k := by simp [m₀]
    by_cases hmem : m₀ ∈ P.support
    · rw [Finset.sum_eq_single m₀]
      · rw [dehomog1_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hm₀_0]; simp [m₀]
      · intro m hm hne
        rw [dehomog1_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        split_ifs with h0
        · exfalso; apply hne
          ext i; fin_cases i
          · change m 0 = m₀ 0; exact h0.symm.trans hm₀_0.symm
          · change m 1 = m₀ 1; have hd := hdeg m hm; rw [hm₀_1]; omega
        · rw [mul_zero]
      · intro h; exact absurd hmem h
    · have hc0 : P.coeff m₀ = 0 := MvPolynomial.notMem_support_iff.mp hmem
      change _ = P.coeff m₀
      rw [hc0]
      apply Finset.sum_eq_zero
      intro m hm
      rw [dehomog1_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      split_ifs with h0
      · exfalso; apply hmem
        have : m = m₀ := by
          ext i; fin_cases i
          · change m 0 = m₀ 0; exact h0.symm.trans hm₀_0.symm
          · change m 1 = m₀ 1; have hd := hdeg m hm; rw [hm₀_1]; omega
        exact this ▸ hm
      · rw [mul_zero]
  · apply Finset.sum_eq_zero
    intro m hm
    rw [dehomog1_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    split_ifs with h0
    · exfalso; have hd := hdeg m hm; omega
    · rw [mul_zero]

lemma coeff_dehomog0_of_isHomogeneous {P : MvPolynomial (Fin 2) K} {d : ℕ}
    (hP : P.IsHomogeneous d) (k : ℕ) :
    (dehomog0 P).coeff k =
      if k ≤ d then P.coeff (Finsupp.single 0 (d - k) + Finsupp.single 1 k) else 0 := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum, Polynomial.finset_sum_coeff]
  have hdeg : ∀ m ∈ P.support, m 0 + m 1 = d := by
    intro m hm
    have h := isHomogeneous_sum_eq hP hm
    rwa [Fin.sum_univ_two] at h
  split_ifs with hkd
  · let m₀ : Fin 2 →₀ ℕ := Finsupp.single 0 (d - k) + Finsupp.single 1 k
    have hm₀_0 : m₀ 0 = d - k := by simp [m₀]
    have hm₀_1 : m₀ 1 = k := by simp [m₀]
    by_cases hmem : m₀ ∈ P.support
    · rw [Finset.sum_eq_single m₀]
      · rw [dehomog0_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hm₀_1]; simp [m₀]
      · intro m hm hne
        rw [dehomog0_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        split_ifs with h1
        · exfalso; apply hne
          ext i; fin_cases i
          · change m 0 = m₀ 0; have hd := hdeg m hm; rw [hm₀_0]; omega
          · change m 1 = m₀ 1; exact h1.symm.trans hm₀_1.symm
        · rw [mul_zero]
      · intro h; exact absurd hmem h
    · have hc0 : P.coeff m₀ = 0 := MvPolynomial.notMem_support_iff.mp hmem
      change _ = P.coeff m₀
      rw [hc0]
      apply Finset.sum_eq_zero
      intro m hm
      rw [dehomog0_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      split_ifs with h1
      · exfalso; apply hmem
        have : m = m₀ := by
          ext i; fin_cases i
          · change m 0 = m₀ 0; have hd := hdeg m hm; rw [hm₀_0]; omega
          · change m 1 = m₀ 1; exact h1.symm.trans hm₀_1.symm
        exact this ▸ hm
      · rw [mul_zero]
  · apply Finset.sum_eq_zero
    intro m hm
    rw [dehomog0_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    split_ifs with h1
    · exfalso; have hd := hdeg m hm; omega
    · rw [mul_zero]

lemma natDegree_dehomog1_le {P : MvPolynomial (Fin 2) K} {d : ℕ} (hP : P.IsHomogeneous d) :
    (dehomog1 P).natDegree ≤ d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [coeff_dehomog1_of_isHomogeneous hP]
  have hnot : ¬ k ≤ d := by omega
  simp [hnot]

lemma eq_zero_of_dehomog1_eq_zero {P : MvPolynomial (Fin 2) K} {d : ℕ}
    (hP : P.IsHomogeneous d) (h0 : dehomog1 P = 0) : P = 0 := by
  ext m
  rw [MvPolynomial.coeff_zero]
  by_cases hm : m ∈ P.support
  · have hdeg : m 0 + m 1 = d := by
      have h := isHomogeneous_sum_eq hP hm
      rwa [Fin.sum_univ_two] at h
    have hc := congrArg (fun q => Polynomial.coeff q (m 0)) h0
    rw [Polynomial.coeff_zero, coeff_dehomog1_of_isHomogeneous hP] at hc
    have hle : m 0 ≤ d := by omega
    simp only [hle, ite_true] at hc
    have hmeq : Finsupp.single (0 : Fin 2) (m 0) + Finsupp.single 1 (d - m 0) = m := by
      ext i; fin_cases i
      · simp
      · simp; omega
    rwa [hmeq] at hc
  · exact MvPolynomial.notMem_support_iff.mp hm

lemma eq_zero_of_dehomog0_eq_zero {P : MvPolynomial (Fin 2) K} {d : ℕ}
    (hP : P.IsHomogeneous d) (h0 : dehomog0 P = 0) : P = 0 := by
  ext m
  rw [MvPolynomial.coeff_zero]
  by_cases hm : m ∈ P.support
  · have hdeg : m 0 + m 1 = d := by
      have h := isHomogeneous_sum_eq hP hm
      rwa [Fin.sum_univ_two] at h
    have hc := congrArg (fun q => Polynomial.coeff q (m 1)) h0
    rw [Polynomial.coeff_zero, coeff_dehomog0_of_isHomogeneous hP] at hc
    have hle : m 1 ≤ d := by omega
    simp only [hle, ite_true] at hc
    have hmeq : Finsupp.single (0 : Fin 2) (d - m 1) + Finsupp.single 1 (m 1) = m := by
      ext i; fin_cases i
      · simp; omega
      · simp
    rwa [hmeq] at hc
  · exact MvPolynomial.notMem_support_iff.mp hm

lemma X_pow_dvd_dehomog0_of_natDegree_dehomog1 {P : MvPolynomial (Fin 2) K} {d : ℕ}
    (hP : P.IsHomogeneous d) :
    Polynomial.X ^ (d - (dehomog1 P).natDegree) ∣ dehomog0 P := by
  rw [Polynomial.X_pow_dvd_iff]
  intro k hk
  rw [coeff_dehomog0_of_isHomogeneous hP]
  split_ifs with hkd
  · have hlt : (dehomog1 P).natDegree < d - k := by omega
    have h0 := Polynomial.coeff_eq_zero_of_natDegree_lt hlt
    rw [coeff_dehomog1_of_isHomogeneous hP] at h0
    have hle : d - k ≤ d := Nat.sub_le d k
    simp only [hle, ite_true, show d - (d - k) = k by omega] at h0
    exact h0
  · rfl

lemma eval_one_zero_eq_coeff_dehomog1 {P : MvPolynomial (Fin 2) K} {d : ℕ}
    (hP : P.IsHomogeneous d) :
    eval (fun i => match i with | 0 => (1 : K) | 1 => 0) P = (dehomog1 P).coeff d := by
  rw [coeff_dehomog1_of_isHomogeneous hP]
  simp only [le_refl, ite_true, Nat.sub_self, Finsupp.single_zero, add_zero]
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  let m₀ : Fin 2 →₀ ℕ := Finsupp.single 0 d
  by_cases hmem : m₀ ∈ P.support
  · rw [Finset.sum_eq_single m₀]
    · rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
      simp [m₀]
    · intro m hm hne
      rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
      have hdeg : m 0 + m 1 = d := by
        have h := isHomogeneous_sum_eq hP hm
        rwa [Fin.sum_univ_two] at h
      have hm1 : m 1 ≠ 0 := by
        intro h1; apply hne; ext i; fin_cases i
        · simp [m₀]; omega
        · simp [m₀, h1]
      simp [zero_pow hm1]
    · intro h; exact absurd hmem h
  · change _ = P.coeff m₀
    rw [MvPolynomial.notMem_support_iff.mp hmem]
    apply Finset.sum_eq_zero
    intro m hm
    rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
    have hdeg : m 0 + m 1 = d := by
      have h := isHomogeneous_sum_eq hP hm
      rwa [Fin.sum_univ_two] at h
    have hm1 : m 1 ≠ 0 := by
      intro h1; apply hmem
      have : m = m₀ := by ext i; fin_cases i <;> (simp [m₀, h1]; try omega)
      exact this ▸ hm
    simp [zero_pow hm1]

lemma homog2_eq_zero_of_roots {P : MvPolynomial (Fin 2) K} {d : ℕ}
    (hP : P.IsHomogeneous d) {S : Finset (Fin 2 → K)} (hcard : d + 1 ≤ S.card)
    (hnz : ∀ v ∈ S, v ≠ 0)
    (hnp : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → v 0 * w 1 - v 1 * w 0 ≠ 0)
    (hzero : ∀ v ∈ S, eval v P = 0) : P = 0 := by
  classical
  apply eq_zero_of_dehomog1_eq_zero hP
  set q := dehomog1 P
  by_contra hq0
  let S' := S.filter fun v => v 1 ≠ 0
  let R := S'.image fun v => v 0 / v 1
  have hR_inj : Set.InjOn (fun v : Fin 2 → K => v 0 / v 1) S' := by
    intro v hv w hw heq
    by_contra hne
    have hv1 : v 1 ≠ 0 := (mem_filter.mp hv).2
    have hw1 : w 1 ≠ 0 := (mem_filter.mp hw).2
    have hmul : v 0 * w 1 = w 0 * v 1 := (div_eq_div_iff hv1 hw1).mp heq
    exact hnp v (mem_filter.mp hv).1 w (mem_filter.mp hw).1 hne (by linear_combination hmul)
  have hR_card : R.card = S'.card := card_image_of_injOn hR_inj
  have hR_roots : ∀ r ∈ R, r ∈ q.roots := by
    intro r hr
    rcases mem_image.mp hr with ⟨v, hv, rfl⟩
    have hvS : v ∈ S := (mem_filter.mp hv).1
    have hv1 : v 1 ≠ 0 := (mem_filter.mp hv).2
    rw [Polynomial.mem_roots hq0, Polynomial.IsRoot.def, eval_dehomog1]
    have hsm : (fun i : Fin 2 => match i with | 0 => v 0 / v 1 | 1 => 1) = (v 1)⁻¹ • v := by
      ext i; fin_cases i
      · simp [div_eq_mul_inv, mul_comm]
      · simp [inv_mul_cancel₀ hv1]
    rw [hsm, isHomogeneous_eval_smul hP, hzero v hvS, mul_zero]
  have hR_le : R.card ≤ q.natDegree := by
    calc R.card ≤ q.roots.card := by
            have hsub : R.val ⊆ q.roots := by
              intro r hr; exact hR_roots r hr
            have hle := Multiset.card_le_card (Multiset.le_iff_subset R.nodup |>.mpr hsub)
            exact hle
      _ ≤ q.natDegree := Polynomial.card_roots' q
  have hbad_le : (S.filter fun v => v 1 = 0).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro v hv w hw
    by_contra hne
    have hv1 : v 1 = 0 := (mem_filter.mp hv).2
    have hw1 : w 1 = 0 := (mem_filter.mp hw).2
    exact hnp v (mem_filter.mp hv).1 w (mem_filter.mp hw).1 hne (by rw [hv1, hw1]; ring)
  have hpart : S'.card + (S.filter fun v => v 1 = 0).card = S.card := by
    have hdisj : Disjoint S' (S.filter fun v => v 1 = 0) := by
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      exact (mem_filter.mp hv1).2 (mem_filter.mp hv2).2
    rw [← card_union_of_disjoint hdisj]
    congr 1; ext v; simp only [S', mem_union, mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hv; by_cases h1 : v 1 = 0
      · exact Or.inr ⟨hv, h1⟩
      · exact Or.inl ⟨hv, h1⟩
  have hq_le : q.natDegree ≤ d := natDegree_dehomog1_le hP
  by_cases hhas : (S.filter fun v => v 1 = 0).Nonempty
  · obtain ⟨v₀, hv₀⟩ := hhas
    have hv₀S : v₀ ∈ S := (mem_filter.mp hv₀).1
    have hv₀1 : v₀ 1 = 0 := (mem_filter.mp hv₀).2
    have hv₀0 : v₀ 0 ≠ 0 := by
      intro h0; exact hnz v₀ hv₀S (by ext i; fin_cases i <;> assumption)
    have hcoeff_d : q.coeff d = 0 := by
      rw [← eval_one_zero_eq_coeff_dehomog1 hP]
      have hsm : (fun i : Fin 2 => match i with | 0 => (1 : K) | 1 => 0) = (v₀ 0)⁻¹ • v₀ := by
        ext i; fin_cases i
        · simp [inv_mul_cancel₀ hv₀0]
        · simp [hv₀1]
      rw [hsm, isHomogeneous_eval_smul hP, hzero v₀ hv₀S, mul_zero]
    have hdeg_lt : q.natDegree < d := by
      by_contra hge
      have heq : q.natDegree = d := by omega
      have hlc : q.leadingCoeff = 0 := by rw [Polynomial.leadingCoeff, heq]; exact hcoeff_d
      exact hq0 (Polynomial.leadingCoeff_eq_zero.mp hlc)
    omega
  · have h0 : (S.filter fun v => v 1 = 0).card = 0 :=
      card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hhas)
    omega

end HomogUtils

section SegreEnvelope

variable {p : ℕ} [Fact p.Prime]

noncomputable def segreEnv (A E : Finset (Fin 2 → ZMod p)) (e : Fin 2 → ZMod p) :
    MvPolynomial (Fin 3) (ZMod p) :=
  ∑ a ∈ E, ∑ b ∈ E.erase a,
    C (Fval A e a b) *
      ∏ u ∈ (E.erase a).erase b,
        C (det3 (embed a) (embed b) (embed u))⁻¹ * linForm (embed u)

lemma segreEnv_isHomogeneous {A E : Finset (Fin 2 → ZMod p)} {e : Fin 2 → ZMod p} {t : ℕ}
    (hE : E.card = 2 * t + 2) :
    (segreEnv A E e).IsHomogeneous (2 * t) := by
  unfold segreEnv
  apply IsHomogeneous.sum
  intro a ha
  apply IsHomogeneous.sum
  intro b hb
  apply IsHomogeneous.C_mul
  have hcard : ((E.erase a).erase b).card = 2 * t := by
    rw [card_erase_of_mem hb, card_erase_of_mem ha, hE]; omega
  have hprod := IsHomogeneous.prod ((E.erase a).erase b)
    (fun u => C (det3 (embed a) (embed b) (embed u))⁻¹ * linForm (embed u))
    (fun _ => 1)
    (fun u _ => (linForm_isHomogeneous (embed u)).C_mul _)
  simpa [hcard] using hprod

noncomputable def restrictA {K : Type*} [CommRing K] (a : Fin 2 → K) :
    MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 2) K :=
  MvPolynomial.eval₂Hom C (fun i => match i with
    | 0 => C (-a 0) * X 0 + C (-a 1) * X 1
    | 1 => X 0
    | 2 => X 1)

lemma restrictA_isHomogeneous {K : Type*} [CommRing K] (a : Fin 2 → K)
    {P : MvPolynomial (Fin 3) K} {d : ℕ} (hP : P.IsHomogeneous d) :
    (restrictA a P).IsHomogeneous d := by
  rw [P.as_sum, map_sum]
  apply IsHomogeneous.sum
  intro m hm
  have hdeg : ∑ i : Fin 3, m i = d := isHomogeneous_sum_eq hP hm
  unfold restrictA
  rw [MvPolynomial.eval₂Hom_monomial]
  apply IsHomogeneous.C_mul
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
  have h1 : ∀ i : Fin 3, ((match i with
      | 0 => C (-a 0) * X 0 + C (-a 1) * X 1
      | 1 => X 0
      | 2 => X 1 : MvPolynomial (Fin 2) K) ^ m i).IsHomogeneous (m i) := by
    intro i; fin_cases i
    · have h0 : (C (-a 0) * X 0 + C (-a 1) * X 1 : MvPolynomial (Fin 2) K).IsHomogeneous 1 :=
        ((isHomogeneous_X K (0 : Fin 2)).C_mul _).add ((isHomogeneous_X K (1 : Fin 2)).C_mul _)
      simpa using h0.pow (m 0)
    · simpa using (isHomogeneous_X K (0 : Fin 2)).pow (m 1)
    · simpa using (isHomogeneous_X K (1 : Fin 2)).pow (m 2)
  have hpr := IsHomogeneous.prod univ _ (fun i => m i) (fun i _ => h1 i)
  rwa [hdeg] at hpr

lemma eval_restrictA {K : Type*} [CommRing K] (a : Fin 2 → K)
    (P : MvPolynomial (Fin 3) K) (y : Fin 2 → K) :
    eval y (restrictA a P) =
      eval (fun i => match i with | 0 => -a 0 * y 0 - a 1 * y 1 | 1 => y 0 | 2 => y 1) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [restrictA]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
    fin_cases i
    · rw [map_mul, map_mul, hp]; simp [restrictA]; ring
    · rw [map_mul, map_mul, hp]; simp [restrictA]
    · rw [map_mul, map_mul, hp]; simp [restrictA]

lemma eval_restrictA_of_dot3_zero {K : Type*} [Field K] (a : Fin 2 → K)
    (P : MvPolynomial (Fin 3) K) {u : Fin 3 → K} (hu : dot3 u (embed a) = 0) :
    eval (fun i => match i with | 0 => u 1 | 1 => u 2) (restrictA a P) = eval u P := by
  rw [eval_restrictA]
  have harg : (fun i : Fin 3 => match i with
      | 0 => -a 0 * u 1 - a 1 * u 2 | 1 => u 1 | 2 => u 2) = u := by
    ext i; fin_cases i
    · change -a 0 * u 1 - a 1 * u 2 = u 0
      unfold dot3 embed at hu; dsimp only at hu; linear_combination -hu
    · rfl
    · rfl
  exact congrArg (fun f => eval f P) harg

lemma eval_restrictA_cross3 {K : Type*} [Field K] (a b : Fin 2 → K)
    (P : MvPolynomial (Fin 3) K) :
    eval (fun i => match i with | 0 => a 1 - b 1 | 1 => b 0 - a 0) (restrictA a P) =
      eval (cross3 (embed a) (embed b)) P := by
  rw [eval_restrictA]
  have harg : (fun i : Fin 3 => match i with
      | 0 => -a 0 * (a 1 - b 1) - a 1 * (b 0 - a 0) | 1 => a 1 - b 1 | 2 => b 0 - a 0) =
      cross3 (embed a) (embed b) := by
    ext i; fin_cases i
    · change -a 0 * (a 1 - b 1) - a 1 * (b 0 - a 0) = a 0 * b 1 - a 1 * b 0; ring
    · change a 1 - b 1 = a 1 * 1 - 1 * b 1; ring
    · change b 0 - a 0 = 1 * b 0 - a 0 * 1; ring
  exact congrArg (fun f => eval f P) harg

noncomputable def dualLin2 {K : Type*} [CommRing K] (u : Fin 3 → K) : MvPolynomial (Fin 2) K :=
  C (u 1) * X 1 - C (u 2) * X 0

lemma dualLin2_isHomogeneous {K : Type*} [CommRing K] (u : Fin 3 → K) :
    (dualLin2 u).IsHomogeneous 1 := by
  unfold dualLin2
  rw [sub_eq_add_neg]
  apply IsHomogeneous.add
  · exact (isHomogeneous_X K (1 : Fin 2)).C_mul _
  · exact ((isHomogeneous_X K (0 : Fin 2)).C_mul _).neg

lemma eval_dualLin2_cross3 {K : Type*} [Field K] {a b : Fin 2 → K} {u : Fin 3 → K}
    (hu : dot3 u (embed a) = 0) :
    eval (fun i => match i with | 0 => a 1 - b 1 | 1 => b 0 - a 0) (dualLin2 u) =
      dot3 u (embed b) := by
  simp only [dualLin2, map_sub, map_mul, eval_C, eval_X]
  unfold dot3 embed at hu ⊢; dsimp only at hu ⊢
  linear_combination -hu

noncomputable def gPoly (A : Finset (Fin 2 → ZMod p)) (e a : Fin 2 → ZMod p) :
    MvPolynomial (Fin 2) (ZMod p) :=
  C (scaleA A e a) * (∏ u ∈ tangents A a, dualLin2 u) ^ 2

lemma gPoly_isHomogeneous {A : Finset (Fin 2 → ZMod p)}
    (harc : ∀ s ⊆ A, s.card = 3 → ¬ Collinear (ZMod p) (s : Set (Fin 2 → ZMod p)))
    {e a : Fin 2 → ZMod p} (ha : a ∈ A) :
    (gPoly A e a).IsHomogeneous (2 * (p + 2 - A.card)) := by
  unfold gPoly
  apply IsHomogeneous.C_mul
  have h1 := IsHomogeneous.prod (tangents A a) (fun u => dualLin2 u) (fun _ => 1)
    (fun u _ => dualLin2_isHomogeneous u)
  have h2 := h1.pow 2
  have hcard := card_tangents_eq harc ha
  simpa [hcard, mul_comm] using h2

lemma eval_gPoly_cross3 {A : Finset (Fin 2 → ZMod p)} {e a b : Fin 2 → ZMod p} :
    eval (fun i => match i with | 0 => a 1 - b 1 | 1 => b 0 - a 0) (gPoly A e a) =
      Fval A e a b := by
  unfold gPoly Fval
  simp only [map_mul, map_pow, eval_C, map_prod, eval_fPoly]
  congr 2
  apply Finset.prod_congr rfl
  intro u hu
  exact eval_dualLin2_cross3 (mem_tangents.mp hu).2.1

lemma eval_segreEnv_cross3_mem_E {A E : Finset (Fin 2 → ZMod p)}
    (harc : ∀ s ⊆ A, s.card = 3 → ¬ Collinear (ZMod p) (s : Set (Fin 2 → ZMod p)))
    {e : Fin 2 → ZMod p} (he : e ∈ A) (hEA : E ⊆ A) {t : ℕ} (hE : E.card = 2 * t + 2)
    {x y : Fin 2 → ZMod p} (hx : x ∈ E) (hy : y ∈ E) (hxy : x ≠ y) :
    eval (cross3 (embed x) (embed y)) (segreEnv A E e) = 2 * Fval A e x y := by
  classical
  unfold segreEnv
  simp only [map_sum, map_mul, eval_C, map_prod, eval_linForm]
  have hterm : ∀ a ∈ E, ∀ b ∈ E.erase a,
      Fval A e a b * ∏ u ∈ (E.erase a).erase b,
        (det3 (embed a) (embed b) (embed u))⁻¹ * det3 (embed x) (embed y) (embed u) =
      if (a = x ∧ b = y) ∨ (a = y ∧ b = x) then Fval A e x y else 0 := by
    intro a ha b hb
    have hba : b ≠ a := (mem_erase.mp hb).1
    have hbE : b ∈ E := (mem_erase.mp hb).2
    split_ifs with hcase
    · rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hprod1 : ∏ u ∈ (E.erase a).erase b,
            (det3 (embed a) (embed b) (embed u))⁻¹ * det3 (embed a) (embed b) (embed u) = 1 := by
          apply Finset.prod_eq_one
          intro u hu
          have hub : u ≠ b := (mem_erase.mp hu).1
          have hua : u ≠ a := (mem_erase.mp (mem_erase.mp hu).2).1
          have huE : u ∈ E := (mem_erase.mp (mem_erase.mp hu).2).2
          exact inv_mul_cancel₀ (det3_ne_zero_of_arc harc (hEA ha) (hEA hbE) (hEA huE)
            hba.symm hua.symm hub.symm)
        rw [hprod1, mul_one]
      · have hprod1 : ∏ u ∈ (E.erase a).erase b,
            (det3 (embed a) (embed b) (embed u))⁻¹ * det3 (embed b) (embed a) (embed u) = 1 := by
          have hcard : ((E.erase a).erase b).card = 2 * t := by
            rw [card_erase_of_mem hb, card_erase_of_mem ha, hE]; omega
          calc ∏ u ∈ (E.erase a).erase b,
                (det3 (embed a) (embed b) (embed u))⁻¹ * det3 (embed b) (embed a) (embed u)
              = ∏ u ∈ (E.erase a).erase b, (-1 : ZMod p) := by
                  apply Finset.prod_congr rfl
                  intro u hu
                  have hub : u ≠ b := (mem_erase.mp hu).1
                  have hua : u ≠ a := (mem_erase.mp (mem_erase.mp hu).2).1
                  have huE : u ∈ E := (mem_erase.mp (mem_erase.mp hu).2).2
                  have hd := det3_ne_zero_of_arc harc (hEA ha) (hEA hbE) (hEA huE)
                    hba.symm hua.symm hub.symm
                  have hswap : det3 (embed b) (embed a) (embed u) =
                      -det3 (embed a) (embed b) (embed u) := det3_swap12 _ _ _
                  rw [hswap, mul_neg, inv_mul_cancel₀ hd]
            _ = (-1 : ZMod p) ^ (2 * t) := by rw [Finset.prod_const, hcard]
            _ = 1 := by rw [pow_mul]; norm_num
        rw [hprod1, mul_one, Fval_symm harc he (hEA hbE) (hEA ha)]
    · have hzero : ∏ u ∈ (E.erase a).erase b,
          (det3 (embed a) (embed b) (embed u))⁻¹ * det3 (embed x) (embed y) (embed u) = 0 := by
        by_cases hxa : x = a
        · subst hxa
          have hyb : y ≠ b := fun h => hcase (Or.inl ⟨rfl, h.symm⟩)
          have hymem : y ∈ (E.erase x).erase b := mem_erase.mpr ⟨hyb, mem_erase.mpr ⟨hxy.symm, hy⟩⟩
          apply Finset.prod_eq_zero hymem
          rw [det3_self_23, mul_zero]
        · by_cases hxb : x = b
          · subst hxb
            have hya : y ≠ a := fun h => hcase (Or.inr ⟨h.symm, rfl⟩)
            have hymem : y ∈ (E.erase a).erase x := mem_erase.mpr ⟨hxy.symm, mem_erase.mpr ⟨hya, hy⟩⟩
            apply Finset.prod_eq_zero hymem
            rw [det3_self_23, mul_zero]
          · have hxmem : x ∈ (E.erase a).erase b := mem_erase.mpr ⟨hxb, mem_erase.mpr ⟨hxa, hx⟩⟩
            apply Finset.prod_eq_zero hxmem
            rw [det3_self_13, mul_zero]
      rw [hzero, mul_zero]
  have hsum : ∑ a ∈ E, ∑ b ∈ E.erase a,
      Fval A e a b * ∏ u ∈ (E.erase a).erase b,
        (det3 (embed a) (embed b) (embed u))⁻¹ * dot3 (embed u) (cross3 (embed x) (embed y)) =
      ∑ a ∈ E, ∑ b ∈ E.erase a,
        if (a = x ∧ b = y) ∨ (a = y ∧ b = x) then Fval A e x y else 0 := by
    apply Finset.sum_congr rfl; intro a ha
    apply Finset.sum_congr rfl; intro b hb
    simp_rw [dot3_cross3_comm]
    exact hterm a ha b hb
  rw [hsum]
  have hinner : ∀ a ∈ E, (∑ b ∈ E.erase a,
      if (a = x ∧ b = y) ∨ (a = y ∧ b = x) then Fval A e x y else 0) =
      if a = x ∨ a = y then Fval A e x y else 0 := by
    intro a ha
    by_cases hax : a = x
    · subst hax
      rw [Finset.sum_eq_single y]
      · simp
      · intro b _ hby; simp [hby, hxy]
      · intro hnot; exact absurd (mem_erase.mpr ⟨hxy.symm, hy⟩) hnot
    · by_cases hay : a = y
      · subst hay
        rw [Finset.sum_eq_single x]
        · simp
        · intro b _ hbx; simp [hbx, hxy.symm]
        · intro hnot; exact absurd (mem_erase.mpr ⟨hxy, hx⟩) hnot
      · simp [hax, hay]
  rw [Finset.sum_congr rfl hinner]
  have hx_in : x ∈ E := hx
  have hy_in : y ∈ E.erase x := mem_erase.mpr ⟨hxy.symm, hy⟩
  rw [← Finset.add_sum_erase _ _ hx_in, ← Finset.add_sum_erase _ _ hy_in]
  have hrest : ∑ a ∈ (E.erase x).erase y, (if a = x ∨ a = y then Fval A e x y else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have h1 := (mem_erase.mp ha).1
    have h2 := (mem_erase.mp (mem_erase.mp ha).2).1
    simp [h1, h2]
  rw [hrest]; simp; ring

lemma restrictA_segreEnv {A E : Finset (Fin 2 → ZMod p)}
    (harc : ∀ s ⊆ A, s.card = 3 → ¬ Collinear (ZMod p) (s : Set (Fin 2 → ZMod p)))
    {e : Fin 2 → ZMod p} (he : e ∈ A) (hEA : E ⊆ A) (hE : E.card = 2 * (p + 2 - A.card) + 2)
    {a : Fin 2 → ZMod p} (ha : a ∈ A) :
    restrictA a (segreEnv A E e) = C 2 * gPoly A e a := by
  classical
  set t := p + 2 - A.card
  -- Helper: if restrictA x (segreEnv) agrees with C 2 * gPoly at all b in B (subset A.erase x, card >= 2*t+1), they are equal!
  have h_interp : ∀ x ∈ A, ∀ B ⊆ A.erase x, 2 * t + 1 ≤ B.card →
      (∀ b ∈ B, eval (cross3 (embed x) (embed b)) (segreEnv A E e) = 2 * Fval A e x b) →
      restrictA x (segreEnv A E e) = C 2 * gPoly A e x := by
    intro x hx B hBA hBcard hagree
    let diff := restrictA x (segreEnv A E e) - C 2 * gPoly A e x
    have hdiff_hom : diff.IsHomogeneous (2 * t) :=
      (restrictA_isHomogeneous x (segreEnv_isHomogeneous hE)).sub
        ((gPoly_isHomogeneous harc hx).C_mul 2)
    let dir : (Fin 2 → ZMod p) → (Fin 2 → ZMod p) :=
      fun b i => match i with | 0 => x 1 - b 1 | 1 => b 0 - x 0
    have hdir_inj : Set.InjOn dir B := by
      intro b₁ _ b₂ _ heq
      have h0 : x 1 - b₁ 1 = x 1 - b₂ 1 := congrFun heq 0
      have h1 : b₁ 0 - x 0 = b₂ 0 - x 0 := congrFun heq 1
      ext i; fin_cases i
      · change b₁ 0 = b₂ 0; linear_combination h1
      · change b₁ 1 = b₂ 1; linear_combination -h0
    let S := B.image dir
    have hScard : 2 * t + 1 ≤ S.card := by
      rw [card_image_of_injOn hdir_inj]; exact hBcard
    have hdiff0 : diff = 0 := by
      apply homog2_eq_zero_of_roots hdiff_hom hScard
      · intro v hv
        rcases mem_image.mp hv with ⟨b, hb, rfl⟩
        have hbx : b ≠ x := (mem_erase.mp (hBA hb)).1
        intro h0
        apply hbx; ext i; fin_cases i
        · change b 0 = x 0
          have h1 : b 0 - x 0 = 0 := congrFun h0 1
          linear_combination h1
        · change b 1 = x 1
          have h1 : x 1 - b 1 = 0 := congrFun h0 0
          linear_combination -h1
      · intro v hv w hw hvw
        rcases mem_image.mp hv with ⟨b₁, hb₁, rfl⟩
        rcases mem_image.mp hw with ⟨b₂, hb₂, rfl⟩
        have hne : b₁ ≠ b₂ := fun h => hvw (congrArg dir h)
        have h1 := mem_erase.mp (hBA hb₁)
        have h2 := mem_erase.mp (hBA hb₂)
        have hdet := det3_ne_zero_of_arc harc hx h1.2 h2.2 h1.1.symm h2.1.symm hne
        rw [det3_embed] at hdet
        intro h0; apply hdet; dsimp only [dir] at h0; linear_combination h0
      · intro v hv
        rcases mem_image.mp hv with ⟨b, hb, rfl⟩
        simp only [diff, map_sub, map_mul, eval_C]
        rw [eval_restrictA_cross3, eval_gPoly_cross3, hagree b hb, sub_self]
    exact sub_eq_zero.mp hdiff0
  -- First prove for all x in E
  have h_in_E : ∀ x ∈ E, restrictA x (segreEnv A E e) = C 2 * gPoly A e x := by
    intro x hx
    apply h_interp x (hEA hx) (E.erase x) (erase_subset_erase x hEA)
    · rw [card_erase_of_mem hx, hE]; omega
    · intro b hb
      exact eval_segreEnv_cross3_mem_E harc he hEA hE hx (mem_erase.mp hb).2 (mem_erase.mp hb).1.symm
  by_cases haE : a ∈ E
  · exact h_in_E a haE
  · apply h_interp a ha E (fun b hb => mem_erase.mpr ⟨fun h => haE (h ▸ hb), hEA hb⟩)
    · rw [hE]; omega
    · intro b hb
      have hba : b ≠ a := fun h => haE (h ▸ hb)
      have hhom := segreEnv_isHomogeneous (A := A) (E := E) (e := e) hE
      have hcr : eval (cross3 (embed a) (embed b)) (segreEnv A E e) =
          eval (cross3 (embed b) (embed a)) (segreEnv A E e) := by
        rw [cross3_antisymm (embed a) (embed b), isHomogeneous_eval_smul hhom]
        have hm : (-1 : ZMod p) ^ (2 * t) = 1 := by rw [pow_mul]; norm_num
        rw [hm, one_mul]
      rw [hcr, ← eval_restrictA_cross3, h_in_E b hb, map_mul, eval_C, eval_gPoly_cross3,
        Fval_symm harc he (hEA hb) ha]

lemma two_ne_zero_of_prime_ne_two (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hcast : ((2 : ℕ) : ZMod p) = 0 := by simpa using h
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hcast
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hdvd)

lemma restrictA_map {K L : Type*} [CommRing K] [CommRing L] (φ : K →+* L)
    (a : Fin 2 → K) (P : MvPolynomial (Fin 3) K) :
    restrictA (φ ∘ a) (MvPolynomial.map φ P) = MvPolynomial.map φ (restrictA a P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [restrictA]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
    fin_cases i
    · rw [map_mul, map_mul, map_mul, map_mul, hp]; simp [restrictA]
    · rw [map_mul, map_mul, map_mul, map_mul, hp]; simp [restrictA]
    · rw [map_mul, map_mul, map_mul, map_mul, hp]; simp [restrictA]

lemma segreEnv_ne_zero {A E : Finset (Fin 2 → ZMod p)} (hp2 : p ≠ 2)
    (harc : ∀ s ⊆ A, s.card = 3 → ¬ Collinear (ZMod p) (s : Set (Fin 2 → ZMod p)))
    {e : Fin 2 → ZMod p} (he : e ∈ A) (hEA : E ⊆ A) {t : ℕ} (hE : E.card = 2 * t + 2) :
    segreEnv A E e ≠ 0 := by
  have hE2 : 2 ≤ E.card := by omega
  obtain ⟨x, hx⟩ := card_pos.mp (show 0 < E.card by omega)
  have hEx : 0 < (E.erase x).card := by rw [card_erase_of_mem hx]; omega
  obtain ⟨y, hy⟩ := card_pos.mp hEx
  have hxy : x ≠ y := (mem_erase.mp hy).1.symm
  have hyE : y ∈ E := (mem_erase.mp hy).2
  intro h0
  have hev := eval_segreEnv_cross3_mem_E harc he hEA hE hx hyE hxy
  rw [h0, map_zero] at hev
  have hFne : Fval A e x y ≠ 0 :=
    mul_ne_zero (scaleA_ne_zero he (hEA hx)) (pow_ne_zero 2 (eval_fPoly_ne_zero (hEA hyE) hxy.symm))
  exact mul_ne_zero (two_ne_zero_of_prime_ne_two hp2) hFne hev.symm

lemma restrictA_segreEnv_ne_zero {A E : Finset (Fin 2 → ZMod p)} (hp2 : p ≠ 2)
    (harc : ∀ s ⊆ A, s.card = 3 → ¬ Collinear (ZMod p) (s : Set (Fin 2 → ZMod p)))
    {e : Fin 2 → ZMod p} (he : e ∈ A) (hEA : E ⊆ A) (hE : E.card = 2 * (p + 2 - A.card) + 2)
    {a : Fin 2 → ZMod p} (ha : a ∈ A) :
    restrictA a (segreEnv A E e) ≠ 0 := by
  have hA2 : 2 ≤ A.card := by
    have hE2 : 2 ≤ E.card := by omega
    exact hE2.trans (card_le_card hEA)
  have hAa : 0 < (A.erase a).card := by rw [card_erase_of_mem ha]; omega
  obtain ⟨b, hb⟩ := card_pos.mp hAa
  have hba : b ≠ a := (mem_erase.mp hb).1
  have hbA : b ∈ A := (mem_erase.mp hb).2
  intro h0
  have hev : eval (fun i => match i with | 0 => a 1 - b 1 | 1 => b 0 - a 0)
      (restrictA a (segreEnv A E e)) = 0 := by rw [h0, map_zero]
  rw [restrictA_segreEnv harc he hEA hE ha, map_mul, eval_C, eval_gPoly_cross3] at hev
  have hFne : Fval A e a b ≠ 0 :=
    mul_ne_zero (scaleA_ne_zero he ha) (pow_ne_zero 2 (eval_fPoly_ne_zero hbA hba))
  exact mul_ne_zero (two_ne_zero_of_prime_ne_two hp2) hFne hev

lemma eval_map_comp {K L : Type*} [CommRing K] [CommRing L] {σ : Type*}
    (φ : K →+* L) (v : σ → K) (P : MvPolynomial σ K) :
    eval (φ ∘ v) (MvPolynomial.map φ P) = φ (eval v P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp => simp [map_mul, hp]

lemma segreEnv_not_square {A E : Finset (Fin 2 → ZMod p)} (hp2 : p ≠ 2)
    (harc : ∀ s ⊆ A, s.card = 3 → ¬ Collinear (ZMod p) (s : Set (Fin 2 → ZMod p)))
    {e : Fin 2 → ZMod p} (he : e ∈ A) (hEA : E ⊆ A) (hE : E.card = 2 * (p + 2 - A.card) + 2)
    (hA3 : 3 ≤ A.card) :
    ¬ ∃ (c : AlgebraicClosure (ZMod p))
        (Ψ : MvPolynomial (Fin 3) (AlgebraicClosure (ZMod p))),
        MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) (segreEnv A E e) =
          C c * Ψ ^ 2 := by
  set Kbar := AlgebraicClosure (ZMod p)
  set ι : ZMod p →+* Kbar := algebraMap (ZMod p) Kbar
  set t := p + 2 - A.card
  rintro ⟨c, Ψ, hsq⟩
  have hΦ0 : segreEnv A E e ≠ 0 := segreEnv_ne_zero hp2 harc he hEA hE
  have hΦ_map0 : MvPolynomial.map ι (segreEnv A E e) ≠ 0 := by
    intro h0
    apply hΦ0
    ext m
    have hc := congrArg (fun f : MvPolynomial (Fin 3) Kbar => f.coeff m) h0
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at hc
    exact ι.injective (hc.trans (map_zero ι).symm)
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero, zero_mul] at hsq; exact hΦ_map0 hsq
  have hΨ0 : Ψ ≠ 0 := by
    intro h; rw [h, zero_pow (by decide), mul_zero] at hsq; exact hΦ_map0 hsq
  have hΦ_hom : (MvPolynomial.map ι (segreEnv A E e)).IsHomogeneous (2 * t) :=
    (segreEnv_isHomogeneous hE).map ι
  have hΨ_hom : Ψ.IsHomogeneous t := by
    have hmul : (C c * Ψ) * Ψ = MvPolynomial.map ι (segreEnv A E e) := by
      rw [hsq]; ring
    obtain ⟨h1, h2, hsum⟩ := isHomogeneous_of_dvd hΦ_hom hΦ_map0 hmul
    have hdeg_eq : (C c * Ψ).totalDegree = Ψ.totalDegree := by
      have hC_hom : (C c : MvPolynomial (Fin 3) Kbar).IsHomogeneous 0 := isHomogeneous_C _ c
      have hprod_hom : (C c * Ψ).IsHomogeneous (0 + Ψ.totalDegree) := hC_hom.mul h2
      have hne : C c * Ψ ≠ 0 := mul_ne_zero (by simpa using hc0) hΨ0
      rw [hprod_hom.totalDegree hne, zero_add]
    have htd : Ψ.totalDegree = t := by omega
    rwa [htd] at h2
  -- For every a in A, obtain nonzero μ_a such that restrictA (ι ∘ a) Ψ = C μ_a * map ι (∏ dualLin2)
  have hμ : ∀ a ∈ A, ∃ μ : Kbar, μ ≠ 0 ∧
      ∀ b ∈ A, b ≠ a →
        eval (cross3 (embed (ι ∘ a)) (embed (ι ∘ b))) Ψ = μ * ι (eval (embed b) (fPoly A a)) := by
    intro a ha
    have hres := congrArg (restrictA (ι ∘ a)) hsq
    rw [restrictA_map, restrictA_segreEnv harc he hEA hE ha] at hres
    unfold gPoly at hres
    simp only [map_mul, map_pow, MvPolynomial.map_C] at hres
    have hres_C : restrictA (ι ∘ a) (C c) = C c := by
      unfold restrictA; exact MvPolynomial.eval₂Hom_C _ _ _
    rw [hres_C] at hres
    -- Find square root s of ι (2 * scaleA A e a) / c in Kbar
    let val : Kbar := ι (2 * scaleA A e a) / c
    have hval0 : val ≠ 0 := div_ne_zero
      (by intro h; exact mul_ne_zero (two_ne_zero_of_prime_ne_two hp2) (scaleA_ne_zero he ha)
            (ι.injective (h.trans (map_zero ι).symm))) hc0
    let poly : Polynomial Kbar := Polynomial.X ^ 2 - Polynomial.C val
    have hdeg_poly : poly.degree ≠ 0 := by
      have hnd : poly.natDegree = 2 := by
        dsimp only [poly]
        rw [Polynomial.natDegree_sub_C, Polynomial.natDegree_X_pow]
      rw [Polynomial.degree_eq_natDegree (by intro h; rw [h, Polynomial.natDegree_zero] at hnd; omega), hnd]
      decide
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_root poly hdeg_poly
    have hs2 : s ^ 2 = val := by
      rw [Polynomial.IsRoot.def] at hs
      dsimp only [poly] at hs
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hs
      exact sub_eq_zero.mp hs
    have hs0 : s ≠ 0 := by intro h; rw [h, zero_pow (by decide)] at hs2; exact hval0 hs2.symm
    let P_a : MvPolynomial (Fin 2) Kbar := MvPolynomial.map ι (∏ u ∈ tangents A a, dualLin2 u)
    let Q_a : MvPolynomial (Fin 2) Kbar := restrictA (ι ∘ a) Ψ
    have hcs2 : c * s ^ 2 = ι 2 * ι (scaleA A e a) := by
      rw [hs2]; dsimp only [val]; rw [mul_div_cancel₀ _ hc0, map_mul]
    have hdiff : (Q_a - C s * P_a) * (Q_a + C s * P_a) = 0 := by
      have hC_cancel : C c * ((Q_a - C s * P_a) * (Q_a + C s * P_a)) = 0 := by
        calc C c * ((Q_a - C s * P_a) * (Q_a + C s * P_a))
            = C c * Q_a ^ 2 - (C c * C s ^ 2) * P_a ^ 2 := by ring
          _ = C c * Q_a ^ 2 - C (c * s ^ 2) * P_a ^ 2 := by rw [map_mul, map_pow]
          _ = C c * Q_a ^ 2 - C (ι 2) * C (ι (scaleA A e a)) * P_a ^ 2 := by rw [hcs2, map_mul]
          _ = 0 := by
              have hres' : C (ι 2) * (C (ι (scaleA A e a)) * P_a ^ 2) = C c * Q_a ^ 2 := hres
              linear_combination -hres'
      exact (mul_eq_zero.mp hC_cancel).resolve_left (by simpa using hc0)
    have hpm : ∃ μ : Kbar, μ ≠ 0 ∧ Q_a = C μ * P_a := by
      rcases mul_eq_zero.mp hdiff with h1 | h2
      · exact ⟨s, hs0, sub_eq_zero.mp h1⟩
      · exact ⟨-s, neg_ne_zero.mpr hs0, by rw [map_neg, neg_mul]; linear_combination h2⟩
    obtain ⟨μ, hμ0, hQa⟩ := hpm
    refine ⟨μ, hμ0, ?_⟩
    intro b hb hba
    have harg : (fun i : Fin 2 => match i with
        | 0 => (ι ∘ a) 1 - (ι ∘ b) 1 | 1 => (ι ∘ b) 0 - (ι ∘ a) 0) =
        ι ∘ (fun i : Fin 2 => match i with | 0 => a 1 - b 1 | 1 => b 0 - a 0) := by
      ext i; fin_cases i <;> simp [Function.comp]
    have hprod_eval : eval (fun i : Fin 2 => match i with | 0 => a 1 - b 1 | 1 => b 0 - a 0)
        (∏ u ∈ tangents A a, dualLin2 u) = eval (embed b) (fPoly A a) := by
      rw [map_prod, eval_fPoly]
      apply Finset.prod_congr rfl
      intro u hu
      exact eval_dualLin2_cross3 (mem_tangents.mp hu).2.1
    have h0 := congrArg (eval (ι ∘ (fun i : Fin 2 => match i with
      | 0 => a 1 - b 1 | 1 => b 0 - a 0))) hQa
    dsimp only [Q_a, P_a] at h0
    rw [← harg, eval_restrictA_cross3, map_mul, eval_C, harg, eval_map_comp, hprod_eval] at h0
    exact h0
  -- Pick 3 distinct points x, y, z in A
  obtain ⟨x, hx⟩ := card_pos.mp (show 0 < A.card by omega)
  have hAx : 0 < (A.erase x).card := by rw [card_erase_of_mem hx]; omega
  obtain ⟨y, hy⟩ := card_pos.mp hAx
  have hAxy : 0 < ((A.erase x).erase y).card := by
    rw [card_erase_of_mem hy, card_erase_of_mem hx]; omega
  obtain ⟨z, hz⟩ := card_pos.mp hAxy
  have hxy : x ≠ y := (mem_erase.mp hy).1.symm
  have hyA : y ∈ A := (mem_erase.mp hy).2
  have hyz : y ≠ z := (mem_erase.mp hz).1.symm
  have hxz : x ≠ z := (mem_erase.mp (mem_erase.mp hz).2).1.symm
  have hzA : z ∈ A := (mem_erase.mp (mem_erase.mp hz).2).2
  obtain ⟨μx, hμx0, hμx⟩ := hμ x hx
  obtain ⟨μy, hμy0, hμy⟩ := hμ y hyA
  obtain ⟨μz, hμz0, hμz⟩ := hμ z hzA
  have hanti : ∀ u v : Fin 2 → ZMod p,
      eval (cross3 (embed (ι ∘ v)) (embed (ι ∘ u))) Ψ =
        (-1 : Kbar) ^ t * eval (cross3 (embed (ι ∘ u)) (embed (ι ∘ v))) Ψ := by
    intro u v
    rw [cross3_antisymm (embed (ι ∘ u)) (embed (ι ∘ v)), isHomogeneous_eval_smul hΨ_hom]
  have hprod_eq :
      eval (cross3 (embed (ι ∘ x)) (embed (ι ∘ y))) Ψ *
      eval (cross3 (embed (ι ∘ y)) (embed (ι ∘ z))) Ψ *
      eval (cross3 (embed (ι ∘ z)) (embed (ι ∘ x))) Ψ =
      (-1 : Kbar) ^ t *
        (eval (cross3 (embed (ι ∘ y)) (embed (ι ∘ x))) Ψ *
         eval (cross3 (embed (ι ∘ z)) (embed (ι ∘ y))) Ψ *
         eval (cross3 (embed (ι ∘ x)) (embed (ι ∘ z))) Ψ) := by
    rw [hanti x y, hanti y z, hanti z x]
    have hm1 : ((-1 : Kbar) ^ t) ^ 4 = 1 := by
      rw [← pow_mul, show t * 4 = 2 * (2 * t) by omega, pow_mul]; norm_num
    calc eval (cross3 (embed (ι ∘ x)) (embed (ι ∘ y))) Ψ *
          eval (cross3 (embed (ι ∘ y)) (embed (ι ∘ z))) Ψ *
          eval (cross3 (embed (ι ∘ z)) (embed (ι ∘ x))) Ψ
        = ((-1 : Kbar) ^ t) ^ 4 * (eval (cross3 (embed (ι ∘ x)) (embed (ι ∘ y))) Ψ *
          eval (cross3 (embed (ι ∘ y)) (embed (ι ∘ z))) Ψ *
          eval (cross3 (embed (ι ∘ z)) (embed (ι ∘ x))) Ψ) := by rw [hm1, one_mul]
      _ = _ := by ring
  rw [hμx y hyA hxy.symm, hμy z hzA hyz.symm, hμz x hx hxz,
      hμy x hx hxy, hμz y hyA hyz, hμx z hzA hxz.symm] at hprod_eq
  have hseg := congrArg ι (segre_lemma_of_tangents harc hx hyA hzA hxy hxz hyz)
  simp only [map_mul, map_pow, map_neg, map_one] at hseg
  have hLHS :
      μx * ι (eval (embed y) (fPoly A x)) * (μy * ι (eval (embed z) (fPoly A y))) *
        (μz * ι (eval (embed x) (fPoly A z))) =
      μx * μy * μz * ((-1 : Kbar) ^ (t + 1) *
        (ι (eval (embed x) (fPoly A y)) * ι (eval (embed y) (fPoly A z)) *
         ι (eval (embed z) (fPoly A x)))) := by
    calc _ = μx * μy * μz * (ι (eval (embed y) (fPoly A x)) * ι (eval (embed z) (fPoly A y)) *
              ι (eval (embed x) (fPoly A z))) := by ring
      _ = _ := by rw [hseg]
  rw [hLHS] at hprod_eq
  have hfact : μx * μy * μz *
      (ι (eval (embed x) (fPoly A y)) * ι (eval (embed y) (fPoly A z)) *
       ι (eval (embed z) (fPoly A x))) * (-1 : Kbar) ^ t * (-1 - 1) = 0 := by
    have hp1 : (-1 : Kbar) ^ (t + 1) = (-1 : Kbar) ^ t * (-1) := pow_succ _ _
    rw [hp1] at hprod_eq
    linear_combination hprod_eq
  have hμne : μx * μy * μz ≠ 0 := mul_ne_zero (mul_ne_zero hμx0 hμy0) hμz0
  have hfne : ι (eval (embed x) (fPoly A y)) * ι (eval (embed y) (fPoly A z)) *
      ι (eval (embed z) (fPoly A x)) ≠ 0 := by
    rw [← map_mul, ← map_mul]
    intro h0
    have := ι.injective (h0.trans (map_zero ι).symm)
    exact mul_ne_zero (mul_ne_zero (eval_fPoly_ne_zero hx hxy) (eval_fPoly_ne_zero hyA hyz))
      (eval_fPoly_ne_zero hzA hxz.symm) this
  have hpowne : (-1 : Kbar) ^ t ≠ 0 := pow_ne_zero t (neg_ne_zero.mpr one_ne_zero)
  have hm2 : (-1 - 1 : Kbar) = 0 :=
    (mul_eq_zero.mp hfact).resolve_left (mul_ne_zero (mul_ne_zero hμne hfne) hpowne)
  have h2K : (2 : Kbar) = 0 := by linear_combination -hm2
  have h2Z : (2 : ZMod p) = 0 := ι.injective (by rw [map_ofNat, map_zero]; exact h2K)
  exact two_ne_zero_of_prime_ne_two hp2 h2Z

lemma natDegree_le_two_mul_roots_of_dvd_prod_sq {K : Type*} [Field K] [DecidableEq K]
    (R : Finset K) : ∀ {β : K} {q : Polynomial K}, β ≠ 0 → q ≠ 0 →
    q ∣ Polynomial.C β * ∏ r ∈ R, (Polynomial.X - Polynomial.C r) ^ 2 →
    q.natDegree ≤ 2 * (R.filter fun r => q.IsRoot r).card := by
  induction R using Finset.induction_on with
  | empty =>
    intro β q hβ hq hdvd
    rw [Finset.prod_empty, mul_one] at hdvd
    have hle := Polynomial.natDegree_le_of_dvd hdvd (by simpa using hβ)
    rw [Polynomial.natDegree_C] at hle
    simp; omega
  | @insert r₀ R hr₀ ih =>
    intro β q hβ hq hdvd
    rw [Finset.prod_insert hr₀] at hdvd
    have hlin_ne : Polynomial.X - Polynomial.C r₀ ≠ 0 := Polynomial.X_sub_C_ne_zero r₀
    have hlin_irr : Irreducible (Polynomial.X - Polynomial.C r₀) := Polynomial.irreducible_X_sub_C r₀
    by_cases hrt : q.IsRoot r₀
    · obtain ⟨q₁, hq1⟩ := Polynomial.dvd_iff_isRoot.mpr hrt
      have hq1_ne : q₁ ≠ 0 := by intro h; rw [h, mul_zero] at hq1; exact hq hq1
      have hdeg1 : q.natDegree = q₁.natDegree + 1 := by
        rw [hq1, Polynomial.natDegree_mul hlin_ne hq1_ne, Polynomial.natDegree_X_sub_C]; omega
      have hdvd1 : q₁ ∣ Polynomial.C β * (Polynomial.X - Polynomial.C r₀) *
          ∏ r ∈ R, (Polynomial.X - Polynomial.C r) ^ 2 := by
        rcases hdvd with ⟨u, hu⟩
        refine ⟨u, ?_⟩
        apply mul_left_cancel₀ hlin_ne
        calc (Polynomial.X - Polynomial.C r₀) *
              (Polynomial.C β * (Polynomial.X - Polynomial.C r₀) *
                ∏ r ∈ R, (Polynomial.X - Polynomial.C r) ^ 2)
            = Polynomial.C β * ((Polynomial.X - Polynomial.C r₀) ^ 2 *
                ∏ r ∈ R, (Polynomial.X - Polynomial.C r) ^ 2) := by ring
          _ = q * u := hu
          _ = (Polynomial.X - Polynomial.C r₀) * (q₁ * u) := by rw [hq1]; ring
      by_cases hrt1 : q₁.IsRoot r₀
      · obtain ⟨q₂, hq2⟩ := Polynomial.dvd_iff_isRoot.mpr hrt1
        have hq2_ne : q₂ ≠ 0 := by intro h; rw [h, mul_zero] at hq2; exact hq1_ne hq2
        have hdeg2 : q₁.natDegree = q₂.natDegree + 1 := by
          rw [hq2, Polynomial.natDegree_mul hlin_ne hq2_ne, Polynomial.natDegree_X_sub_C]; omega
        have hdvd2 : q₂ ∣ Polynomial.C β * ∏ r ∈ R, (Polynomial.X - Polynomial.C r) ^ 2 := by
          rcases hdvd1 with ⟨u, hu⟩
          refine ⟨u, ?_⟩
          apply mul_left_cancel₀ hlin_ne
          calc (Polynomial.X - Polynomial.C r₀) *
                (Polynomial.C β * ∏ r ∈ R, (Polynomial.X - Polynomial.C r) ^ 2)
              = Polynomial.C β * (Polynomial.X - Polynomial.C r₀) *
                  ∏ r ∈ R, (Polynomial.X - Polynomial.C r) ^ 2 := by ring
            _ = q₁ * u := hu
            _ = (Polynomial.X - Polynomial.C r₀) * (q₂ * u) := by rw [hq2]; ring
        have hih := ih hβ hq2_ne hdvd2
        have hsub : R.filter (fun r => q₂.IsRoot r) ⊆ R.filter (fun r => q.IsRoot r) := by
          intro r hr
          rw [mem_filter] at hr ⊢
          refine ⟨hr.1, ?_⟩
          rw [Polynomial.IsRoot.def, hq1, hq2, Polynomial.eval_mul, Polynomial.eval_mul,
            hr.2, mul_zero, mul_zero]
        have hcard_ins : ((insert r₀ R).filter fun r => q.IsRoot r).card =
            (R.filter fun r => q.IsRoot r).card + 1 := by
          rw [Finset.filter_insert]; simp only [hrt, ite_true]
          rw [card_insert_of_notMem (by intro h; exact hr₀ (mem_filter.mp h).1)]
        have hle := card_le_card hsub
        omega
      · have hcop : IsCoprime (Polynomial.X - Polynomial.C r₀) q₁ :=
          hlin_irr.coprime_iff_not_dvd.mpr (fun h => hrt1 (Polynomial.dvd_iff_isRoot.mp h))
        have hdvd1' : q₁ ∣ Polynomial.C β * ∏ r ∈ R, (Polynomial.X - Polynomial.C r) ^ 2 := by
          have hrearr : Polynomial.C β * (Polynomial.X - Polynomial.C r₀) *
              ∏ r ∈ R, (Polynomial.X - Polynomial.C r) ^ 2 =
              (Polynomial.X - Polynomial.C r₀) *
                (Polynomial.C β * ∏ r ∈ R, (Polynomial.X - Polynomial.C r) ^ 2) := by ring
          rw [hrearr] at hdvd1
          exact hcop.symm.dvd_of_dvd_mul_left hdvd1
        have hih := ih hβ hq1_ne hdvd1'
        have hsub : R.filter (fun r => q₁.IsRoot r) ⊆ R.filter (fun r => q.IsRoot r) := by
          intro r hr
          rw [mem_filter] at hr ⊢
          refine ⟨hr.1, ?_⟩
          rw [Polynomial.IsRoot.def, hq1, Polynomial.eval_mul, hr.2, mul_zero]
        have hcard_ins : ((insert r₀ R).filter fun r => q.IsRoot r).card =
            (R.filter fun r => q.IsRoot r).card + 1 := by
          rw [Finset.filter_insert]; simp only [hrt, ite_true]
          rw [card_insert_of_notMem (by intro h; exact hr₀ (mem_filter.mp h).1)]
        have hle := card_le_card hsub
        omega
    · have hcop : IsCoprime ((Polynomial.X - Polynomial.C r₀) ^ 2) q :=
        (hlin_irr.coprime_iff_not_dvd.mpr (fun h => hrt (Polynomial.dvd_iff_isRoot.mp h))).pow_left
      have hdvd' : q ∣ Polynomial.C β * ∏ r ∈ R, (Polynomial.X - Polynomial.C r) ^ 2 := by
        have hrearr : Polynomial.C β * ((Polynomial.X - Polynomial.C r₀) ^ 2 *
            ∏ r ∈ R, (Polynomial.X - Polynomial.C r) ^ 2) =
            (Polynomial.X - Polynomial.C r₀) ^ 2 *
              (Polynomial.C β * ∏ r ∈ R, (Polynomial.X - Polynomial.C r) ^ 2) := by ring
        rw [hrearr] at hdvd
        exact hcop.symm.dvd_of_dvd_mul_left hdvd
      have hih := ih hβ hq hdvd'
      have hcard_ins : ((insert r₀ R).filter fun r => q.IsRoot r).card =
          (R.filter fun r => q.IsRoot r).card := by
        rw [Finset.filter_insert]; simp only [hrt, ite_false]
      omega

lemma not_cube_dvd_prod_sq {K : Type*} [Field K]
    (R : Finset K) : ∀ {β : K} {q : Polynomial K}, β ≠ 0 → 1 ≤ q.natDegree →
    ¬ (q ^ 3 ∣ Polynomial.C β * ∏ r ∈ R, (Polynomial.X - Polynomial.C r) ^ 2) := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    intro β q hβ hdeg hdvd
    rw [Finset.prod_empty, mul_one] at hdvd
    have hq0 : q ≠ 0 := by intro h; rw [h, Polynomial.natDegree_zero] at hdeg; omega
    have hle := Polynomial.natDegree_le_of_dvd hdvd (by simpa using hβ)
    rw [Polynomial.natDegree_C, Polynomial.natDegree_pow] at hle
    omega
  | @insert r₀ R hr₀ ih =>
    intro β q hβ hdeg hdvd
    rw [Finset.prod_insert hr₀] at hdvd
    have hlin_ne : Polynomial.X - Polynomial.C r₀ ≠ 0 := Polynomial.X_sub_C_ne_zero r₀
    have hlin_irr : Irreducible (Polynomial.X - Polynomial.C r₀) := Polynomial.irreducible_X_sub_C r₀
    by_cases hrt : q.IsRoot r₀
    · obtain ⟨q₁, hq1⟩ := Polynomial.dvd_iff_isRoot.mpr hrt
      have hcube : (Polynomial.X - Polynomial.C r₀) ^ 3 ∣
          Polynomial.C β * ((Polynomial.X - Polynomial.C r₀) ^ 2 *
            ∏ r ∈ R, (Polynomial.X - Polynomial.C r) ^ 2) := by
        exact dvd_trans (pow_dvd_pow_of_dvd ⟨q₁, hq1⟩ 3) hdvd
      rcases hcube with ⟨u, hu⟩
      have hdiv : (Polynomial.X - Polynomial.C r₀) * u =
          Polynomial.C β * ∏ r ∈ R, (Polynomial.X - Polynomial.C r) ^ 2 := by
        apply mul_left_cancel₀ (pow_ne_zero 2 hlin_ne)
        calc (Polynomial.X - Polynomial.C r₀) ^ 2 * ((Polynomial.X - Polynomial.C r₀) * u)
            = (Polynomial.X - Polynomial.C r₀) ^ 3 * u := by ring
          _ = Polynomial.C β * ((Polynomial.X - Polynomial.C r₀) ^ 2 *
                ∏ r ∈ R, (Polynomial.X - Polynomial.C r) ^ 2) := hu.symm
          _ = (Polynomial.X - Polynomial.C r₀) ^ 2 *
                (Polynomial.C β * ∏ r ∈ R, (Polynomial.X - Polynomial.C r) ^ 2) := by ring
      have hev := congrArg (Polynomial.eval r₀) hdiv
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        sub_self, zero_mul, Polynomial.eval_prod, Polynomial.eval_pow] at hev
      have hprod_ne : ∏ r ∈ R, (r₀ - r) ^ 2 ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro r hr
        exact pow_ne_zero 2 (sub_ne_zero.mpr (fun h => hr₀ (h ▸ hr)))
      exact mul_ne_zero hβ hprod_ne hev.symm
    · have hcop : IsCoprime ((Polynomial.X - Polynomial.C r₀) ^ 2) (q ^ 3) :=
        ((hlin_irr.coprime_iff_not_dvd.mpr (fun h => hrt (Polynomial.dvd_iff_isRoot.mp h))).pow_left).pow_right
      have hdvd' : q ^ 3 ∣ Polynomial.C β * ∏ r ∈ R, (Polynomial.X - Polynomial.C r) ^ 2 := by
        have hrearr : Polynomial.C β * ((Polynomial.X - Polynomial.C r₀) ^ 2 *
            ∏ r ∈ R, (Polynomial.X - Polynomial.C r) ^ 2) =
            (Polynomial.X - Polynomial.C r₀) ^ 2 *
              (Polynomial.C β * ∏ r ∈ R, (Polynomial.X - Polynomial.C r) ^ 2) := by ring
        rw [hrearr] at hdvd
        exact hcop.symm.dvd_of_dvd_mul_left hdvd
      exact ih hβ hdeg hdvd'

lemma dehomog1_dualLin2 {K : Type*} [Field K] (u : Fin 3 → K) :
    dehomog1 (dualLin2 u) = Polynomial.C (u 1) - Polynomial.C (u 2) * Polynomial.X := by
  simp [dehomog1, dualLin2]

lemma dehomog0_dualLin2 {K : Type*} [Field K] (u : Fin 3 → K) :
    dehomog0 (dualLin2 u) = Polynomial.C (u 1) * Polynomial.X - Polynomial.C (u 2) := by
  simp [dehomog0, dualLin2]

lemma tangents_filter_u2_eq_zero_card_le_one {A : Finset (Fin 2 → ZMod p)} {a : Fin 2 → ZMod p} :
    ((tangents A a).filter fun u => u 2 = 0).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  have hun := (mem_tangents.mp (mem_filter.mp hu).1).1
  have hud := (mem_tangents.mp (mem_filter.mp hu).1).2.1
  have hu2 : u 2 = 0 := (mem_filter.mp hu).2
  have hvn := (mem_tangents.mp (mem_filter.mp hv).1).1
  have hvd := (mem_tangents.mp (mem_filter.mp hv).1).2.1
  have hv2 : v 2 = 0 := (mem_filter.mp hv).2
  have hv1 : v 1 ≠ 0 := by
    intro h1
    have hv0 : v 0 = 0 := by unfold dot3 embed at hvd; dsimp only at hvd; rw [h1, hv2] at hvd; linear_combination hvd
    exact isNorm_ne_zero hvn (by ext i; fin_cases i <;> assumption)
  apply isNorm_eq_of_smul hun hvn (c := u 1 / v 1)
  ext i; fin_cases i
  · change u 0 = u 1 / v 1 * v 0
    have hu0 : u 0 = -a 0 * u 1 := by unfold dot3 embed at hud; dsimp only at hud; rw [hu2] at hud; linear_combination hud
    have hv0 : v 0 = -a 0 * v 1 := by unfold dot3 embed at hvd; dsimp only at hvd; rw [hv2] at hvd; linear_combination hvd
    rw [hu0, hv0]
    calc -a 0 * u 1 = -a 0 * (u 1 / v 1 * v 1) := by rw [div_mul_cancel₀ _ hv1]
      _ = u 1 / v 1 * (-a 0 * v 1) := by ring
  · change u 1 = u 1 / v 1 * v 1; rw [div_mul_cancel₀ _ hv1]
  · change u 2 = u 1 / v 1 * v 2; rw [hu2, hv2, mul_zero]

lemma tangents_div_injOn {A : Finset (Fin 2 → ZMod p)} {a : Fin 2 → ZMod p} :
    Set.InjOn (fun u : Fin 3 → ZMod p => u 1 / u 2)
      ((tangents A a).filter fun u => u 2 ≠ 0) := by
  intro u hu v hv heq
  have hun := (mem_tangents.mp (mem_filter.mp hu).1).1
  have hud := (mem_tangents.mp (mem_filter.mp hu).1).2.1
  have hu2 : u 2 ≠ 0 := (mem_filter.mp hu).2
  have hvn := (mem_tangents.mp (mem_filter.mp hv).1).1
  have hvd := (mem_tangents.mp (mem_filter.mp hv).1).2.1
  have hv2 : v 2 ≠ 0 := (mem_filter.mp hv).2
  have hmul : u 1 * v 2 = v 1 * u 2 := (div_eq_div_iff hu2 hv2).mp heq
  apply isNorm_eq_of_smul hun hvn (c := u 2 / v 2)
  have hu1 : u 1 = u 2 / v 2 * v 1 := by
    apply mul_left_cancel₀ hv2
    calc v 2 * u 1 = u 1 * v 2 := mul_comm _ _
      _ = v 1 * u 2 := hmul
      _ = v 1 * (u 2 / v 2 * v 2) := by rw [div_mul_cancel₀ _ hv2]
      _ = v 2 * (u 2 / v 2 * v 1) := by ring
  ext i; fin_cases i
  · change u 0 = u 2 / v 2 * v 0
    have hu0 : u 0 = -a 0 * u 1 - a 1 * u 2 := by
      unfold dot3 embed at hud; dsimp only at hud; linear_combination hud
    have hv0 : v 0 = -a 0 * v 1 - a 1 * v 2 := by
      unfold dot3 embed at hvd; dsimp only at hvd; linear_combination hvd
    rw [hu0, hv0, hu1]
    calc -a 0 * (u 2 / v 2 * v 1) - a 1 * u 2
        = -a 0 * (u 2 / v 2 * v 1) - a 1 * (u 2 / v 2 * v 2) := by rw [div_mul_cancel₀ _ hv2]
      _ = u 2 / v 2 * (-a 0 * v 1 - a 1 * v 2) := by ring
  · exact hu1
  · change u 2 = u 2 / v 2 * v 2; rw [div_mul_cancel₀ _ hv2]

lemma dehomog1_two_mul_gPoly {A : Finset (Fin 2 → ZMod p)} (hp2 : p ≠ 2)
    {e a : Fin 2 → ZMod p} (he : e ∈ A) (ha : a ∈ A) :
    ∃ β : ZMod p, β ≠ 0 ∧
      dehomog1 (C 2 * gPoly A e a) =
        Polynomial.C β *
          ∏ r ∈ ((tangents A a).filter fun u => u 2 ≠ 0).image (fun u => u 1 / u 2),
            (Polynomial.X - Polynomial.C r) ^ 2 := by
  classical
  set T2 := (tangents A a).filter fun u => u 2 ≠ 0
  set T0 := (tangents A a).filter fun u => u 2 = 0
  have hpart : tangents A a = T2 ∪ T0 := by
    ext u; simp only [T2, T0, mem_union, mem_filter]
    constructor
    · intro h; by_cases h2 : u 2 = 0; exact Or.inr ⟨h, h2⟩; exact Or.inl ⟨h, h2⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdisj : Disjoint T2 T0 := by
    rw [Finset.disjoint_left]; intro u h1 h2; exact (mem_filter.mp h1).2 (mem_filter.mp h2).2
  have hT0_val : ∀ u ∈ T0, dehomog1 (dualLin2 u) = Polynomial.C (u 1) ∧ u 1 ≠ 0 := by
    intro u hu
    have hu2 : u 2 = 0 := (mem_filter.mp hu).2
    have hun := (mem_tangents.mp (mem_filter.mp hu).1).1
    have hud := (mem_tangents.mp (mem_filter.mp hu).1).2.1
    refine ⟨by rw [dehomog1_dualLin2, hu2, map_zero, zero_mul, sub_zero], ?_⟩
    intro h1
    have hu0 : u 0 = 0 := by unfold dot3 embed at hud; dsimp only at hud; rw [h1, hu2] at hud; linear_combination hud
    exact isNorm_ne_zero hun (by ext i; fin_cases i <;> assumption)
  have hT2_val : ∀ u ∈ T2,
      dehomog1 (dualLin2 u) = Polynomial.C (-u 2) * (Polynomial.X - Polynomial.C (u 1 / u 2)) := by
    intro u hu
    have hu2 : u 2 ≠ 0 := (mem_filter.mp hu).2
    rw [dehomog1_dualLin2, mul_sub, ← map_mul]
    have hmul : -u 2 * (u 1 / u 2) = -u 1 := by
      rw [neg_mul, mul_div_cancel₀ _ hu2]
    rw [hmul, map_neg, map_neg]
    ring
  let β : ZMod p := 2 * scaleA A e a * (∏ u ∈ T0, (u 1) ^ 2) * (∏ u ∈ T2, (-u 2) ^ 2)
  have hβ0 : β ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (two_ne_zero_of_prime_ne_two hp2) (scaleA_ne_zero he ha)) ?_) ?_
    · apply Finset.prod_ne_zero_iff.mpr; intro u hu; exact pow_ne_zero 2 (hT0_val u hu).2
    · apply Finset.prod_ne_zero_iff.mpr; intro u hu; exact pow_ne_zero 2 (neg_ne_zero.mpr (mem_filter.mp hu).2)
  refine ⟨β, hβ0, ?_⟩
  unfold gPoly
  rw [map_mul, map_mul, map_pow, map_prod]
  have hC1 : dehomog1 (C (2 : ZMod p)) = Polynomial.C 2 := by simp [dehomog1]
  have hC2 : dehomog1 (C (scaleA A e a)) = Polynomial.C (scaleA A e a) := by simp [dehomog1]
  rw [hC1, hC2, hpart, Finset.prod_union hdisj, mul_pow, ← Finset.prod_pow, ← Finset.prod_pow]
  have hP0 : (∏ u ∈ T0, dehomog1 (dualLin2 u) ^ 2) = Polynomial.C (∏ u ∈ T0, (u 1) ^ 2) := by
    rw [map_prod]
    apply Finset.prod_congr rfl; intro u hu
    rw [(hT0_val u hu).1, ← map_pow]
  have hP2 : (∏ u ∈ T2, dehomog1 (dualLin2 u) ^ 2) =
      Polynomial.C (∏ u ∈ T2, (-u 2) ^ 2) *
        ∏ u ∈ T2, (Polynomial.X - Polynomial.C (u 1 / u 2)) ^ 2 := by
    calc ∏ u ∈ T2, dehomog1 (dualLin2 u) ^ 2
        = ∏ u ∈ T2, (Polynomial.C ((-u 2) ^ 2) * (Polynomial.X - Polynomial.C (u 1 / u 2)) ^ 2) := by
            apply Finset.prod_congr rfl; intro u hu
            rw [hT2_val u hu, mul_pow, ← map_pow]
      _ = (∏ u ∈ T2, Polynomial.C ((-u 2) ^ 2)) *
            ∏ u ∈ T2, (Polynomial.X - Polynomial.C (u 1 / u 2)) ^ 2 := Finset.prod_mul_distrib
      _ = _ := by rw [← map_prod]
  rw [hP0, hP2]
  have himg : (∏ r ∈ T2.image (fun u => u 1 / u 2), (Polynomial.X - Polynomial.C r) ^ 2) =
      ∏ u ∈ T2, (Polynomial.X - Polynomial.C (u 1 / u 2)) ^ 2 :=
    Finset.prod_image (by intro u hu v hv h; exact tangents_div_injOn hu hv h)
  rw [himg]
  dsimp only [β]
  simp only [map_mul]
  ring

lemma dehomog0_two_mul_gPoly {A : Finset (Fin 2 → ZMod p)} (hp2 : p ≠ 2)
    {e a : Fin 2 → ZMod p} (he : e ∈ A) (ha : a ∈ A) :
    ∃ q₀ : Polynomial (ZMod p), Polynomial.eval 0 q₀ ≠ 0 ∧
      dehomog0 (C 2 * gPoly A e a) =
        Polynomial.X ^ (2 * ((tangents A a).filter fun u => u 2 = 0).card) * q₀ := by
  classical
  set T2 := (tangents A a).filter fun u => u 2 ≠ 0
  set T0 := (tangents A a).filter fun u => u 2 = 0
  have hpart : tangents A a = T2 ∪ T0 := by
    ext u; simp only [T2, T0, mem_union, mem_filter]
    constructor
    · intro h; by_cases h2 : u 2 = 0; exact Or.inr ⟨h, h2⟩; exact Or.inl ⟨h, h2⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdisj : Disjoint T2 T0 := by
    rw [Finset.disjoint_left]; intro u h1 h2; exact (mem_filter.mp h1).2 (mem_filter.mp h2).2
  have hT0_val : ∀ u ∈ T0, dehomog0 (dualLin2 u) = Polynomial.C (u 1) * Polynomial.X ∧ u 1 ≠ 0 := by
    intro u hu
    have hu2 : u 2 = 0 := (mem_filter.mp hu).2
    have hun := (mem_tangents.mp (mem_filter.mp hu).1).1
    have hud := (mem_tangents.mp (mem_filter.mp hu).1).2.1
    refine ⟨by rw [dehomog0_dualLin2, hu2, map_zero, sub_zero], ?_⟩
    intro h1
    have hu0 : u 0 = 0 := by unfold dot3 embed at hud; dsimp only at hud; rw [h1, hu2] at hud; linear_combination hud
    exact isNorm_ne_zero hun (by ext i; fin_cases i <;> assumption)
  let q₀ : Polynomial (ZMod p) :=
    Polynomial.C (2 * scaleA A e a * ∏ u ∈ T0, (u 1) ^ 2) *
      ∏ u ∈ T2, dehomog0 (dualLin2 u) ^ 2
  refine ⟨q₀, ?_, ?_⟩
  · dsimp only [q₀]
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
    refine mul_ne_zero ?_ ?_
    · refine mul_ne_zero (mul_ne_zero (two_ne_zero_of_prime_ne_two hp2) (scaleA_ne_zero he ha)) ?_
      apply Finset.prod_ne_zero_iff.mpr; intro u hu; exact pow_ne_zero 2 (hT0_val u hu).2
    · apply Finset.prod_ne_zero_iff.mpr; intro u hu
      simp only [Polynomial.eval_pow, dehomog0_dualLin2, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, mul_zero, zero_sub]
      exact pow_ne_zero 2 (neg_ne_zero.mpr (mem_filter.mp hu).2)
  · unfold gPoly
    rw [map_mul, map_mul, map_pow, map_prod]
    have hC1 : dehomog0 (C (2 : ZMod p)) = Polynomial.C 2 := by simp [dehomog0]
    have hC2 : dehomog0 (C (scaleA A e a)) = Polynomial.C (scaleA A e a) := by simp [dehomog0]
    rw [hC1, hC2, hpart, Finset.prod_union hdisj, mul_pow, ← Finset.prod_pow, ← Finset.prod_pow]
    have hP0 : (∏ u ∈ T0, dehomog0 (dualLin2 u) ^ 2) =
        Polynomial.C (∏ u ∈ T0, (u 1) ^ 2) * Polynomial.X ^ (2 * T0.card) := by
      calc ∏ u ∈ T0, dehomog0 (dualLin2 u) ^ 2
          = ∏ u ∈ T0, (Polynomial.C ((u 1) ^ 2) * Polynomial.X ^ 2) := by
              apply Finset.prod_congr rfl; intro u hu
              rw [(hT0_val u hu).1, mul_pow, ← map_pow]
        _ = (∏ u ∈ T0, Polynomial.C ((u 1) ^ 2)) * (∏ u ∈ T0, Polynomial.X ^ 2) := Finset.prod_mul_distrib
        _ = Polynomial.C (∏ u ∈ T0, (u 1) ^ 2) * Polynomial.X ^ (2 * T0.card) := by
              rw [← map_prod, Finset.prod_const, ← pow_mul]
    rw [hP0]
    dsimp only [q₀]
    simp only [map_mul]
    ring

lemma not_cube_dvd_segreEnv {A E : Finset (Fin 2 → ZMod p)} (hp2 : p ≠ 2)
    (harc : ∀ s ⊆ A, s.card = 3 → ¬ Collinear (ZMod p) (s : Set (Fin 2 → ZMod p)))
    {e : Fin 2 → ZMod p} (he : e ∈ A) (hEA : E ⊆ A) (hE : E.card = 2 * (p + 2 - A.card) + 2)
    {P : MvPolynomial (Fin 3) (ZMod p)} {d : ℕ} (hP : P.IsHomogeneous d) (hd : 1 ≤ d) :
    ¬ (P ^ 3 ∣ segreEnv A E e) := by
  intro hdvd
  have hres_dvd : (restrictA e P) ^ 3 ∣ C 2 * gPoly A e e := by
    rw [← restrictA_segreEnv harc he hEA hE he]
    rcases hdvd with ⟨Q, hQ⟩
    exact ⟨restrictA e Q, by rw [hQ, map_mul, map_pow]⟩
  have hres_hom : (restrictA e P).IsHomogeneous d := restrictA_isHomogeneous e hP
  by_cases hdeg : 1 ≤ (dehomog1 (restrictA e P)).natDegree
  · obtain ⟨β, hβ, hg1⟩ := dehomog1_two_mul_gPoly hp2 he he
    have hd1 : (dehomog1 (restrictA e P)) ^ 3 ∣
        Polynomial.C β * ∏ r ∈ ((tangents A e).filter fun u => u 2 ≠ 0).image (fun u => u 1 / u 2),
          (Polynomial.X - Polynomial.C r) ^ 2 := by
      rw [← hg1]
      rcases hres_dvd with ⟨Q, hQ⟩
      exact ⟨dehomog1 Q, by rw [hQ, map_mul, map_pow]⟩
    exact not_cube_dvd_prod_sq _ hβ hdeg hd1
  · have hdeg0 : (dehomog1 (restrictA e P)).natDegree = 0 := by omega
    have hXd : Polynomial.X ^ d ∣ dehomog0 (restrictA e P) := by
      have h := X_pow_dvd_dehomog0_of_natDegree_dehomog1 hres_hom
      rwa [hdeg0, Nat.sub_zero] at h
    have hX3d : Polynomial.X ^ (3 * d) ∣ dehomog0 (C 2 * gPoly A e e) := by
      have h1 : (Polynomial.X ^ d) ^ 3 ∣ (dehomog0 (restrictA e P)) ^ 3 := pow_dvd_pow_of_dvd hXd 3
      rw [← pow_mul, mul_comm d 3] at h1
      rcases hres_dvd with ⟨Q, hQ⟩
      exact dvd_trans h1 ⟨dehomog0 Q, by rw [hQ, map_mul, map_pow]⟩
    obtain ⟨q₀, hq0_ev, hg0⟩ := dehomog0_two_mul_gPoly hp2 he he
    rw [hg0] at hX3d
    set c0 := ((tangents A e).filter fun u => u 2 = 0).card
    have hc0_le : c0 ≤ 1 := tangents_filter_u2_eq_zero_card_le_one
    have hX_dvd_q0 : Polynomial.X ∣ q₀ := by
      rcases hX3d with ⟨u, hu⟩
      refine ⟨Polynomial.X ^ (3 * d - 2 * c0 - 1) * u, ?_⟩
      apply mul_left_cancel₀ (pow_ne_zero (2 * c0) Polynomial.X_ne_zero)
      calc Polynomial.X ^ (2 * c0) * q₀ = Polynomial.X ^ (3 * d) * u := hu
        _ = Polynomial.X ^ (2 * c0) * (Polynomial.X * (Polynomial.X ^ (3 * d - 2 * c0 - 1) * u)) := by
            rw [← mul_assoc, ← mul_assoc, ← pow_succ, ← pow_add]
            have hexp : 2 * c0 + 1 + (3 * d - 2 * c0 - 1) = 3 * d := by omega
            rw [hexp]
    rcases hX_dvd_q0 with ⟨v, hv⟩
    apply hq0_ev
    rw [hv, Polynomial.eval_mul, Polynomial.eval_X, zero_mul]

lemma exists_irreducible_dvd_of_homog {K : Type*} [Field K] :
    ∀ n : ℕ, 1 ≤ n → ∀ {F : MvPolynomial (Fin 3) K}, F.IsHomogeneous n → F ≠ 0 →
    ∃ (P : MvPolynomial (Fin 3) K) (d : ℕ), Irreducible P ∧ P.IsHomogeneous d ∧ 1 ≤ d ∧ P ∣ F := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn F hF hF0
    by_cases hirr : Irreducible F
    · exact ⟨F, n, hirr, hF, hn, dvd_refl F⟩
    · have hnotu : ¬ IsUnit F := by
        intro hu
        obtain ⟨G, hG⟩ := hu.exists_right_inv
        have h1 : (1 : MvPolynomial (Fin 3) K).IsHomogeneous 0 := isHomogeneous_one _ _
        obtain ⟨_, _, hsum⟩ := isHomogeneous_of_dvd h1 one_ne_zero hG
        have hFd : F.totalDegree = n := hF.totalDegree hF0
        omega
      rw [irreducible_iff] at hirr
      have hsplit : ∃ A B, F = A * B ∧ ¬ IsUnit A ∧ ¬ IsUnit B := by
        by_contra hall
        apply hirr
        refine ⟨hnotu, ?_⟩
        intro A B hAB
        by_contra hnor
        apply hall
        exact ⟨A, B, hAB, fun h => hnor (Or.inl h), fun h => hnor (Or.inr h)⟩
      obtain ⟨A, B, hAB, hAu, hBu⟩ := hsplit
      obtain ⟨hAh, hBh, hsum⟩ := isHomogeneous_of_dvd hF hF0 hAB.symm
      have hA0 : A ≠ 0 := by intro h; rw [h, zero_mul] at hAB; exact hF0 hAB
      have hB0 : B ≠ 0 := by intro h; rw [h, mul_zero] at hAB; exact hF0 hAB
      have hAd_pos : 1 ≤ A.totalDegree := by
        by_contra h0
        have heq : A.totalDegree = 0 := by omega
        rw [heq] at hAh
        have hAC := isHomogeneous_zero_eq_C hAh
        have hc0 : A.coeff 0 ≠ 0 := by intro h; rw [h, map_zero] at hAC; exact hA0 hAC
        apply hAu
        rw [hAC]
        exact (IsUnit.mk0 (A.coeff 0) hc0).map C
      have hBd_pos : 1 ≤ B.totalDegree := by
        by_contra h0
        have heq : B.totalDegree = 0 := by omega
        rw [heq] at hBh
        have hBC := isHomogeneous_zero_eq_C hBh
        have hc0 : B.coeff 0 ≠ 0 := by intro h; rw [h, map_zero] at hBC; exact hB0 hBC
        apply hBu
        rw [hBC]
        exact (IsUnit.mk0 (B.coeff 0) hc0).map C
      obtain ⟨P, d, hPirr, hPh, hd, hPA⟩ := ih A.totalDegree (by omega) hAd_pos hAh hA0
      exact ⟨P, d, hPirr, hPh, hd, dvd_trans hPA ⟨B, hAB⟩⟩

lemma exists_odd_mul_irreducible_of_not_square {K : Type*} [Field K] :
    ∀ n : ℕ, ∀ {Φ : MvPolynomial (Fin 3) K}, Φ.IsHomogeneous n → Φ ≠ 0 →
    (¬ ∃ (c : K) (Ψ : MvPolynomial (Fin 3) K), Φ = C c * Ψ ^ 2) →
    ∃ (P : MvPolynomial (Fin 3) K) (d : ℕ), Irreducible P ∧ P.IsHomogeneous d ∧ 1 ≤ d ∧
      ∃ (k : ℕ) (R : MvPolynomial (Fin 3) K), Φ = P ^ (2 * k + 1) * R ∧ ¬ (P ∣ R) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro Φ hΦ hΦ0 hnsq
    classical
    by_cases hn0 : n = 0
    · subst hn0
      exfalso; apply hnsq
      exact ⟨Φ.coeff 0, 1, by rw [one_pow, mul_one]; exact isHomogeneous_zero_eq_C hΦ⟩
    have hn1 : 1 ≤ n := by omega
    obtain ⟨P, d, hPirr, hPh, hd, hPF⟩ := exists_irreducible_dvd_of_homog n hn1 hΦ hΦ0
    have hP0 : P ≠ 0 := hPirr.ne_zero
    -- Find largest e with P ^ e ∣ Φ
    have hmax_ex : ∃ e : ℕ, P ^ e ∣ Φ ∧ ¬ (P ^ (e + 1) ∣ Φ) := by
      have hbound : ∀ m : ℕ, n < m → ¬ (P ^ m ∣ Φ) := by
        intro m hm hdvd
        rcases hdvd with ⟨Q, hQ⟩
        obtain ⟨hPm_h, _, hsum⟩ := isHomogeneous_of_dvd hΦ hΦ0 hQ.symm
        have hPm0 : P ^ m ≠ 0 := pow_ne_zero m hP0
        have hPm_d : (P ^ m).totalDegree = m * d := by
          have hpow : (P ^ m).IsHomogeneous (m * d) := by
            simpa [smul_eq_mul, mul_comm] using hPh.pow m
          exact hpow.totalDegree hPm0
        have hle : m * d ≤ n := by omega
        have hmd : m ≤ m * d := Nat.le_mul_of_pos_right m (by omega)
        omega
      let S := (Finset.range (n + 1)).filter fun e => P ^ e ∣ Φ
      have h1S : 1 ∈ S := by
        rw [mem_filter, Finset.mem_range]; exact ⟨by omega, by simpa using hPF⟩
      let e := S.max' ⟨1, h1S⟩
      have heS : e ∈ S := Finset.max'_mem S ⟨1, h1S⟩
      refine ⟨e, (mem_filter.mp heS).2, ?_⟩
      intro hsucc
      by_cases hlt : e + 1 < n + 1
      · have hle := Finset.le_max' S (e + 1) (mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hsucc⟩)
        omega
      · exact hbound (e + 1) (by omega) hsucc
    obtain ⟨e, ⟨R, hR⟩, hnot_succ⟩ := hmax_ex
    have he1 : 1 ≤ e := by
      by_contra h0
      have he0 : e = 0 := by omega
      rw [he0, zero_add, pow_one] at hnot_succ
      exact hnot_succ hPF
    have hnot_PR : ¬ (P ∣ R) := by
      rintro ⟨R', hR'⟩
      apply hnot_succ
      exact ⟨R', by rw [hR, hR', pow_succ]; ring⟩
    rcases Nat.even_or_odd' e with ⟨k, rfl | rfl⟩
    · -- e = 2 * k is even; recurse on R
      have hR0 : R ≠ 0 := by intro h; rw [h, mul_zero] at hR; exact hΦ0 hR
      obtain ⟨_, hRh, hsum⟩ := isHomogeneous_of_dvd hΦ hΦ0 hR.symm
      have hPe0 : P ^ (2 * k) ≠ 0 := pow_ne_zero (2 * k) hP0
      have hPed : (P ^ (2 * k)).totalDegree = (2 * k) * d := by
        have hpow : (P ^ (2 * k)).IsHomogeneous ((2 * k) * d) := by
          simpa [smul_eq_mul, mul_comm] using hPh.pow (2 * k)
        exact hpow.totalDegree hPe0
      have hRlt : R.totalDegree < n := by
        have hpos : 1 ≤ (2 * k) * d := Nat.mul_pos (by omega) (by omega)
        omega
      have hRnsq : ¬ ∃ (c : K) (Ψ : MvPolynomial (Fin 3) K), R = C c * Ψ ^ 2 := by
        rintro ⟨c, Ψ, hRsq⟩
        apply hnsq
        refine ⟨c, P ^ k * Ψ, ?_⟩
        rw [hR, hRsq, mul_pow, ← pow_mul, mul_comm k 2]; ring
      obtain ⟨Q, dQ, hQirr, hQh, hdQ, j, R', hR', hnot_QR'⟩ :=
        ih R.totalDegree hRlt hRh hR0 hRnsq
      have hQprime : Prime Q := UniqueFactorizationMonoid.irreducible_iff_prime.mp hQirr
      have hnot_QP : ¬ (Q ∣ P) := by
        intro hQP
        have hassoc : Associated Q P := hQirr.associated_of_dvd hPirr hQP
        have hPQ : P ∣ Q := hassoc.symm.dvd
        have hQ_dvd_R : Q ∣ R := ⟨Q ^ (2 * j) * R', by rw [hR', pow_succ]; ring⟩
        exact hnot_PR (dvd_trans hPQ hQ_dvd_R)
      have hnot_QPk : ¬ (Q ∣ P ^ (2 * k)) := fun h => hnot_QP (hQprime.dvd_of_dvd_pow h)
      have hnot_Qrest : ¬ (Q ∣ P ^ (2 * k) * R') := fun h =>
        (hQprime.dvd_or_dvd h).elim hnot_QPk hnot_QR'
      exact ⟨Q, dQ, hQirr, hQh, hdQ, j, P ^ (2 * k) * R',
        by rw [hR, hR']; ring, hnot_Qrest⟩
    · -- e = 2 * k + 1 is odd!
      exact ⟨P, d, hPirr, hPh, hd, k, R, hR, hnot_PR⟩

lemma exists_simple_irreducible_factor {A E : Finset (Fin 2 → ZMod p)} (hp2 : p ≠ 2)
    (harc : ∀ s ⊆ A, s.card = 3 → ¬ Collinear (ZMod p) (s : Set (Fin 2 → ZMod p)))
    {e : Fin 2 → ZMod p} (he : e ∈ A) (hEA : E ⊆ A)
    (hE : E.card = 2 * (p + 2 - A.card) + 2) (hA3 : 3 ≤ A.card) :
    ∃ (P H : MvPolynomial (Fin 3) (ZMod p)) (d : ℕ),
      Irreducible P ∧ P * H = segreEnv A E e ∧ ¬ (P ∣ H) ∧
      P.IsHomogeneous d ∧ H.IsHomogeneous (2 * (p + 2 - A.card) - d) ∧
      1 ≤ d ∧ d ≤ 2 * (p + 2 - A.card) := by
  set t := p + 2 - A.card
  have hΦh : (segreEnv A E e).IsHomogeneous (2 * t) := segreEnv_isHomogeneous hE
  have hΦ0 : segreEnv A E e ≠ 0 := segreEnv_ne_zero hp2 harc he hEA hE
  have hnsq_K : ¬ ∃ (c : ZMod p) (Ψ : MvPolynomial (Fin 3) (ZMod p)),
      segreEnv A E e = C c * Ψ ^ 2 := by
    rintro ⟨c, Ψ, hsq⟩
    apply segreEnv_not_square hp2 harc he hEA hE hA3
    refine ⟨algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) c,
      MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) Ψ, ?_⟩
    rw [hsq, map_mul, map_pow, MvPolynomial.map_C]
  obtain ⟨P, d, hPirr, hPh, hd, k, R, hR, hnot_PR⟩ :=
    exists_odd_mul_irreducible_of_not_square (2 * t) hΦh hΦ0 hnsq_K
  have hk0 : k = 0 := by
    by_contra hk
    apply not_cube_dvd_segreEnv hp2 harc he hEA hE hPh hd
    refine ⟨P ^ (2 * k - 2) * R, ?_⟩
    rw [hR, ← mul_assoc, ← pow_add]
    have hexp : 3 + (2 * k - 2) = 2 * k + 1 := by omega
    rw [hexp]
  subst hk0
  simp only [mul_zero, zero_add, pow_one] at hR
  obtain ⟨_, hRh, hsum⟩ := isHomogeneous_of_dvd hΦh hΦ0 hR.symm
  have hPd : P.totalDegree = d := hPh.totalDegree hPirr.ne_zero
  have hRd : R.totalDegree = 2 * t - d := by omega
  rw [hRd] at hRh
  exact ⟨P, R, d, hPirr, hR.symm, hnot_PR, hPh, hRh, hd, by omega⟩

lemma mem_tangents_of_eval_dvd_segreEnv {A E : Finset (Fin 2 → ZMod p)} (hp2 : p ≠ 2)
    (harc : ∀ s ⊆ A, s.card = 3 → ¬ Collinear (ZMod p) (s : Set (Fin 2 → ZMod p)))
    {e : Fin 2 → ZMod p} (he : e ∈ A) (hEA : E ⊆ A) (hE : E.card = 2 * (p + 2 - A.card) + 2)
    {P : MvPolynomial (Fin 3) (ZMod p)} (hdvd : P ∣ segreEnv A E e)
    {a : Fin 2 → ZMod p} (ha : a ∈ A) {u : Fin 3 → ZMod p}
    (huL : u ∈ lineThrough (embed a)) (hev : eval u P = 0) :
    u ∈ tangents A a := by
  obtain ⟨hunorm, hdota⟩ := mem_lineThrough.mp huL
  rcases hdvd with ⟨H, hH⟩
  have hres : restrictA a P * restrictA a H = C 2 * gPoly A e a := by
    rw [← map_mul, ← hH, restrictA_segreEnv harc he hEA hE ha]
  have hev_g : eval (fun i : Fin 2 => match i with | 0 => u 1 | 1 => u 2) (C 2 * gPoly A e a) = 0 := by
    rw [← hres, map_mul, eval_restrictA_of_dot3_zero a P hdota, hev, zero_mul]
  unfold gPoly at hev_g
  simp only [map_mul, map_pow, eval_C, map_prod] at hev_g
  have hprod0 : (∏ v ∈ tangents A a,
      eval (fun i : Fin 2 => match i with | 0 => u 1 | 1 => u 2) (dualLin2 v)) = 0 := by
    have hsq0 := (mul_eq_zero.mp ((mul_eq_zero.mp hev_g).resolve_left (two_ne_zero_of_prime_ne_two hp2))).resolve_left
      (scaleA_ne_zero he ha)
    exact eq_zero_of_pow_eq_zero hsq0
  obtain ⟨v, hv, hv0⟩ := Finset.prod_eq_zero_iff.mp hprod0
  have hvn := (mem_tangents.mp hv).1
  have hvd := (mem_tangents.mp hv).2.1
  simp only [dualLin2, map_sub, map_mul, eval_C, eval_X] at hv0
  have hdet_uv : v 1 * u 2 - v 2 * u 1 = 0 := hv0
  -- Both u and v lie on lineThrough (embed a) and have v 1 * u 2 = v 2 * u 1, so u = v
  have huv : u = v := by
    by_cases hv2 : v 2 ≠ 0
    · apply isNorm_eq_of_smul hunorm hvn (c := u 2 / v 2)
      have hu1 : u 1 = u 2 / v 2 * v 1 := by
        apply mul_left_cancel₀ hv2
        calc v 2 * u 1 = v 1 * u 2 := by linear_combination -hdet_uv
          _ = v 1 * (u 2 / v 2 * v 2) := by rw [div_mul_cancel₀ _ hv2]
          _ = v 2 * (u 2 / v 2 * v 1) := by ring
      ext i; fin_cases i
      · change u 0 = u 2 / v 2 * v 0
        have hu0 : u 0 = -a 0 * u 1 - a 1 * u 2 := by
          unfold dot3 embed at hdota; dsimp only at hdota; linear_combination hdota
        have hv0' : v 0 = -a 0 * v 1 - a 1 * v 2 := by
          unfold dot3 embed at hvd; dsimp only at hvd; linear_combination hvd
        rw [hu0, hv0', hu1]
        calc -a 0 * (u 2 / v 2 * v 1) - a 1 * u 2
            = -a 0 * (u 2 / v 2 * v 1) - a 1 * (u 2 / v 2 * v 2) := by rw [div_mul_cancel₀ _ hv2]
          _ = u 2 / v 2 * (-a 0 * v 1 - a 1 * v 2) := by ring
      · exact hu1
      · change u 2 = u 2 / v 2 * v 2; rw [div_mul_cancel₀ _ hv2]
    · have hv2' : v 2 = 0 := not_not.mp hv2
      have hv1 : v 1 ≠ 0 := by
        intro h1
        have hv0' : v 0 = 0 := by unfold dot3 embed at hvd; dsimp only at hvd; rw [h1, hv2'] at hvd; linear_combination hvd
        exact isNorm_ne_zero hvn (by ext i; fin_cases i <;> assumption)
      rw [hv2', zero_mul, sub_zero] at hdet_uv
      have hu2 : u 2 = 0 := (mul_eq_zero.mp hdet_uv).resolve_left hv1
      apply isNorm_eq_of_smul hunorm hvn (c := u 1 / v 1)
      ext i; fin_cases i
      · change u 0 = u 1 / v 1 * v 0
        have hu0 : u 0 = -a 0 * u 1 := by unfold dot3 embed at hdota; dsimp only at hdota; rw [hu2] at hdota; linear_combination hdota
        have hv0' : v 0 = -a 0 * v 1 := by unfold dot3 embed at hvd; dsimp only at hvd; rw [hv2'] at hvd; linear_combination hvd
        rw [hu0, hv0']
        calc -a 0 * u 1 = -a 0 * (u 1 / v 1 * v 1) := by rw [div_mul_cancel₀ _ hv1]
          _ = u 1 / v 1 * (-a 0 * v 1) := by ring
      · change u 1 = u 1 / v 1 * v 1; rw [div_mul_cancel₀ _ hv1]
      · change u 2 = u 1 / v 1 * v 2; rw [hu2, hv2', mul_zero]
  rwa [huv]

lemma deg_le_two_mul_card_tangents_zeros {A E : Finset (Fin 2 → ZMod p)} (hp2 : p ≠ 2)
    (harc : ∀ s ⊆ A, s.card = 3 → ¬ Collinear (ZMod p) (s : Set (Fin 2 → ZMod p)))
    {e : Fin 2 → ZMod p} (he : e ∈ A) (hEA : E ⊆ A) (hE : E.card = 2 * (p + 2 - A.card) + 2)
    {P : MvPolynomial (Fin 3) (ZMod p)} {d : ℕ} (hP : P.IsHomogeneous d)
    (hdvd : P ∣ segreEnv A E e) {a : Fin 2 → ZMod p} (ha : a ∈ A) :
    d ≤ 2 * ((tangents A a).filter fun u => eval u P = 0).card := by
  classical
  set P_a := restrictA a P
  have hPa_hom : P_a.IsHomogeneous d := restrictA_isHomogeneous a hP
  have hPa_ne : P_a ≠ 0 := by
    intro h0
    apply restrictA_segreEnv_ne_zero hp2 harc he hEA hE ha
    rcases hdvd with ⟨H, hH⟩
    have h0' : restrictA a P = 0 := h0
    rw [hH, map_mul, h0', zero_mul]
  have hPa_dvd : P_a ∣ C 2 * gPoly A e a := by
    rw [← restrictA_segreEnv harc he hEA hE ha]
    rcases hdvd with ⟨H, hH⟩
    exact ⟨restrictA a H, by rw [hH, map_mul]⟩
  set T2 := (tangents A a).filter fun u => u 2 ≠ 0
  set T0 := (tangents A a).filter fun u => u 2 = 0
  -- Part 1: (dehomog1 P_a).natDegree ≤ 2 * (T2.filter (eval · P = 0)).card
  have h1 : (dehomog1 P_a).natDegree ≤ 2 * (T2.filter fun u => eval u P = 0).card := by
    obtain ⟨β, hβ, hg1⟩ := dehomog1_two_mul_gPoly hp2 he ha
    have hq_ne : dehomog1 P_a ≠ 0 := fun h => hPa_ne (eq_zero_of_dehomog1_eq_zero hPa_hom h)
    have hq_dvd : dehomog1 P_a ∣
        Polynomial.C β * ∏ r ∈ T2.image (fun u => u 1 / u 2), (Polynomial.X - Polynomial.C r) ^ 2 := by
      rw [← hg1]
      rcases hPa_dvd with ⟨Q, hQ⟩
      exact ⟨dehomog1 Q, by rw [hQ, map_mul]⟩
    have hnd := natDegree_le_two_mul_roots_of_dvd_prod_sq _ hβ hq_ne hq_dvd
    have hcard_eq : ((T2.image (fun u => u 1 / u 2)).filter fun r => (dehomog1 P_a).IsRoot r).card =
        (T2.filter fun u => eval u P = 0).card := by
      have himg : (T2.image (fun u => u 1 / u 2)).filter (fun r => (dehomog1 P_a).IsRoot r) =
          (T2.filter fun u => eval u P = 0).image (fun u => u 1 / u 2) := by
        ext r
        simp only [mem_filter, mem_image]
        constructor
        · rintro ⟨⟨u, hu, rfl⟩, hrt⟩
          refine ⟨u, ⟨hu, ?_⟩, rfl⟩
          have hu2 : u 2 ≠ 0 := (mem_filter.mp hu).2
          have hud := (mem_tangents.mp (mem_filter.mp hu).1).2.1
          rw [Polynomial.IsRoot.def, eval_dehomog1] at hrt
          have hsm : (fun i : Fin 2 => match i with | 0 => u 1 / u 2 | 1 => 1) =
              (u 2)⁻¹ • (fun i : Fin 2 => match i with | 0 => u 1 | 1 => u 2) := by
            ext i; fin_cases i
            · simp [div_eq_mul_inv, mul_comm]
            · simp [inv_mul_cancel₀ hu2]
          rw [hsm, isHomogeneous_eval_smul hPa_hom, eval_restrictA_of_dot3_zero a P hud] at hrt
          exact (mul_eq_zero.mp hrt).resolve_left (pow_ne_zero d (inv_ne_zero hu2))
        · rintro ⟨u, ⟨hu, hev⟩, rfl⟩
          refine ⟨⟨u, hu, rfl⟩, ?_⟩
          have hu2 : u 2 ≠ 0 := (mem_filter.mp hu).2
          have hud := (mem_tangents.mp (mem_filter.mp hu).1).2.1
          rw [Polynomial.IsRoot.def, eval_dehomog1]
          have hsm : (fun i : Fin 2 => match i with | 0 => u 1 / u 2 | 1 => 1) =
              (u 2)⁻¹ • (fun i : Fin 2 => match i with | 0 => u 1 | 1 => u 2) := by
            ext i; fin_cases i
            · simp [div_eq_mul_inv, mul_comm]
            · simp [inv_mul_cancel₀ hu2]
          rw [hsm, isHomogeneous_eval_smul hPa_hom, eval_restrictA_of_dot3_zero a P hud, hev, mul_zero]
      rw [himg, card_image_of_injOn (tangents_div_injOn.mono (filter_subset _ _))]
    omega
  -- Part 2: d - (dehomog1 P_a).natDegree ≤ 2 * (T0.filter (eval · P = 0)).card
  have h2 : d - (dehomog1 P_a).natDegree ≤ 2 * (T0.filter fun u => eval u P = 0).card := by
    set k := d - (dehomog1 P_a).natDegree
    by_cases hk0 : k = 0
    · omega
    have hXk : Polynomial.X ^ k ∣ dehomog0 P_a := X_pow_dvd_dehomog0_of_natDegree_dehomog1 hPa_hom
    obtain ⟨q₀, hq0_ev, hg0⟩ := dehomog0_two_mul_gPoly hp2 he ha
    have hXk_g : Polynomial.X ^ k ∣ Polynomial.X ^ (2 * T0.card) * q₀ := by
      rw [← hg0]
      rcases hPa_dvd with ⟨Q, hQ⟩
      exact dvd_trans hXk ⟨dehomog0 Q, by rw [hQ, map_mul]⟩
    have hk_le : k ≤ 2 * T0.card := by
      by_contra hgt
      have hX_dvd_q0 : Polynomial.X ∣ q₀ := by
        rcases hXk_g with ⟨u, hu⟩
        refine ⟨Polynomial.X ^ (k - 2 * T0.card - 1) * u, ?_⟩
        apply mul_left_cancel₀ (pow_ne_zero (2 * T0.card) Polynomial.X_ne_zero)
        calc Polynomial.X ^ (2 * T0.card) * q₀ = Polynomial.X ^ k * u := hu
          _ = Polynomial.X ^ (2 * T0.card) * (Polynomial.X * (Polynomial.X ^ (k - 2 * T0.card - 1) * u)) := by
              rw [← mul_assoc, ← mul_assoc, ← pow_succ, ← pow_add]
              have hexp : 2 * T0.card + 1 + (k - 2 * T0.card - 1) = k := by omega
              rw [hexp]
      rcases hX_dvd_q0 with ⟨v, hv⟩
      exact hq0_ev (by rw [hv, Polynomial.eval_mul, Polynomial.eval_X, zero_mul])
    have hT0_ne : T0.Nonempty := card_pos.mp (by omega)
    obtain ⟨u₀, hu₀⟩ := hT0_ne
    have hu₀2 : u₀ 2 = 0 := (mem_filter.mp hu₀).2
    have hu₀_tan : u₀ ∈ tangents A a := (mem_filter.mp hu₀).1
    have hu₀d := (mem_tangents.mp hu₀_tan).2.1
    have hu₀_ev : eval u₀ P = 0 := by
      have hX1 : Polynomial.X ∣ dehomog0 P_a :=
        dvd_trans (dvd_pow_self Polynomial.X hk0) hXk
      have hev0 : Polynomial.eval 0 (dehomog0 P_a) = 0 := by
        rcases hX1 with ⟨v, hv⟩; rw [hv, Polynomial.eval_mul, Polynomial.eval_X, zero_mul]
      rw [eval_dehomog0] at hev0
      have hsm : (fun i : Fin 2 => match i with | 0 => u₀ 1 | 1 => u₀ 2) =
          u₀ 1 • (fun i : Fin 2 => match i with | 0 => (1 : ZMod p) | 1 => 0) := by
        ext i; fin_cases i
        · simp
        · simp [hu₀2]
      rw [← eval_restrictA_of_dot3_zero a P hu₀d, hsm, isHomogeneous_eval_smul hPa_hom, hev0, mul_zero]
    have hT0_card_le : T0.card ≤ 1 := tangents_filter_u2_eq_zero_card_le_one
    have hfilt_pos : 1 ≤ (T0.filter fun u => eval u P = 0).card :=
      card_pos.mpr ⟨u₀, mem_filter.mpr ⟨hu₀, hu₀_ev⟩⟩
    omega
  have hsum_card : (T2.filter fun u => eval u P = 0).card + (T0.filter fun u => eval u P = 0).card =
      ((tangents A a).filter fun u => eval u P = 0).card := by
    have hdisj : Disjoint (T2.filter fun u => eval u P = 0) (T0.filter fun u => eval u P = 0) := by
      rw [Finset.disjoint_left]
      intro u h1 h2
      exact (mem_filter.mp (mem_filter.mp h1).1).2 (mem_filter.mp (mem_filter.mp h2).1).2
    rw [← card_union_of_disjoint hdisj]
    congr 1; ext u; simp only [T2, T0, mem_union, mem_filter]
    constructor
    · rintro (⟨⟨h, _⟩, hev⟩ | ⟨⟨h, _⟩, hev⟩) <;> exact ⟨h, hev⟩
    · rintro ⟨h, hev⟩
      by_cases h2 : u 2 = 0
      · exact Or.inr ⟨⟨h, h2⟩, hev⟩
      · exact Or.inl ⟨⟨h, h2⟩, hev⟩
  have hle_d : (dehomog1 P_a).natDegree ≤ d := natDegree_dehomog1_le hPa_hom
  omega

lemma card_mul_deg_le_two_mul_Z {A E : Finset (Fin 2 → ZMod p)} (hp2 : p ≠ 2)
    (harc : ∀ s ⊆ A, s.card = 3 → ¬ Collinear (ZMod p) (s : Set (Fin 2 → ZMod p)))
    {e : Fin 2 → ZMod p} (he : e ∈ A) (hEA : E ⊆ A) (hE : E.card = 2 * (p + 2 - A.card) + 2)
    {P : MvPolynomial (Fin 3) (ZMod p)} {d : ℕ} (hP : P.IsHomogeneous d)
    (hdvd : P ∣ segreEnv A E e) :
    A.card * d ≤ 2 * ((univ : Finset (Fin 3 → ZMod p)).filter fun v =>
      IsNorm v ∧ eval v P = 0).card := by
  classical
  let Z := (univ : Finset (Fin 3 → ZMod p)).filter fun v => IsNorm v ∧ eval v P = 0
  have hsub : A.biUnion (fun a => (tangents A a).filter fun u => eval u P = 0) ⊆ Z := by
    intro u hu
    rcases mem_biUnion.mp hu with ⟨a, _, hua⟩
    exact mem_filter.mpr ⟨mem_univ u, (mem_tangents.mp (mem_filter.mp hua).1).1, (mem_filter.mp hua).2⟩
  have hdisj : Set.PairwiseDisjoint (A : Set (Fin 2 → ZMod p))
      (fun a => (tangents A a).filter fun u => eval u P = 0) := by
    intro a ha b hb hab
    change Disjoint _ _
    exact (tangents_disjoint ha hb hab).mono (filter_subset _ _) (filter_subset _ _)
  calc A.card * d
      = ∑ _a ∈ A, d := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ a ∈ A, 2 * ((tangents A a).filter fun u => eval u P = 0).card :=
        Finset.sum_le_sum (fun a ha => deg_le_two_mul_card_tangents_zeros hp2 harc he hEA hE hP hdvd ha)
    _ = 2 * ∑ a ∈ A, ((tangents A a).filter fun u => eval u P = 0).card := by rw [Finset.mul_sum]
    _ = 2 * (A.biUnion (fun a => (tangents A a).filter fun u => eval u P = 0)).card := by
        rw [card_biUnion hdisj]
    _ ≤ 2 * Z.card := Nat.mul_le_mul_left 2 (card_le_card hsub)

end SegreEnvelope

section DegOne

variable {p : ℕ} [Fact p.Prime]

lemma homog1_eq_linForm {K : Type*} [Field K] {P : MvPolynomial (Fin 3) K}
    (hP : P.IsHomogeneous 1) :
    P = linForm (fun i => P.coeff (Finsupp.single i 1)) := by
  ext m
  by_cases hm : m ∈ P.support
  · have hdeg : m 0 + m 1 + m 2 = 1 := by
      have h := isHomogeneous_sum_eq hP hm
      rwa [Fin.sum_univ_three] at h
    have hcases : m = Finsupp.single 0 1 ∨ m = Finsupp.single 1 1 ∨ m = Finsupp.single 2 1 := by
      by_cases h0 : m 0 = 1
      · left; ext i; fin_cases i <;> simp <;> omega
      · by_cases h1 : m 1 = 1
        · right; left; ext i; fin_cases i <;> simp <;> omega
        · right; right; ext i; fin_cases i <;> simp <;> omega
    rcases hcases with rfl | rfl | rfl <;>
      simp [linForm, MvPolynomial.coeff_X', Finsupp.single_eq_single_iff]
  · have h0 : P.coeff m = 0 := MvPolynomial.notMem_support_iff.mp hm
    rw [h0]
    unfold linForm
    simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X']
    have hc : ∀ i : Fin 3, (P.coeff (Finsupp.single i 1) * if Finsupp.single i 1 = m then 1 else 0) = 0 := by
      intro i; split_ifs with hi
      · rw [hi, h0, zero_mul]
      · rw [mul_zero]
    rw [hc 0, hc 1, hc 2]; ring

lemma X_zero_dvd_of_eval0_eq_zero {K : Type*} [Field K] {Q : MvPolynomial (Fin 3) K}
    (h0 : MvPolynomial.eval₂Hom C
      (fun i : Fin 3 => match i with | 0 => (0 : MvPolynomial (Fin 2) K) | 1 => X 0 | 2 => X 1) Q = 0) :
    X (0 : Fin 3) ∣ Q := by
  classical
  have hm0 : ∀ m ∈ Q.support, 1 ≤ m 0 := by
    intro m hm
    by_contra hlt
    have hz : m 0 = 0 := by omega
    let m' : Fin 2 →₀ ℕ := Finsupp.single 0 (m 1) + Finsupp.single 1 (m 2)
    have hc := congrArg (fun f : MvPolynomial (Fin 2) K => f.coeff m') h0
    rw [MvPolynomial.coeff_zero, Q.as_sum, map_sum, MvPolynomial.coeff_sum] at hc
    rw [Finset.sum_eq_single m] at hc
    · rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp),
        Fin.prod_univ_three] at hc
      simp only [hz, pow_zero, one_mul] at hc
      have hmon : C (Q.coeff m) * (X (0 : Fin 2) ^ m 1 * X 1 ^ m 2) = monomial m' (Q.coeff m) := by
        rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
        simp [m']
      rw [hmon, MvPolynomial.coeff_monomial] at hc
      simp only [ite_true] at hc
      exact MvPolynomial.mem_support_iff.mp hm hc
    · intro n hn hne
      rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp),
        Fin.prod_univ_three]
      by_cases hn0 : n 0 = 0
      · simp only [hn0, pow_zero, one_mul]
        let n' : Fin 2 →₀ ℕ := Finsupp.single 0 (n 1) + Finsupp.single 1 (n 2)
        have hmon : C (Q.coeff n) * (X (0 : Fin 2) ^ n 1 * X 1 ^ n 2) = monomial n' (Q.coeff n) := by
          rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
          simp [n']
        rw [hmon, MvPolynomial.coeff_monomial]
        split_ifs with heq
        · exfalso; apply hne; ext i; fin_cases i
          · change n 0 = m 0; omega
          · have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) heq; simpa [n', m'] using this
          · have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) heq; simpa [n', m'] using this
        · rfl
      · simp [zero_pow hn0]
    · intro hnot; exact absurd hm hnot
  refine ⟨∑ m ∈ Q.support, monomial (m - Finsupp.single 0 1) (Q.coeff m), ?_⟩
  rw [Finset.mul_sum]
  conv_lhs => rw [Q.as_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]
  have hmeq : Finsupp.single (0 : Fin 3) 1 + (m - Finsupp.single 0 1) = m := by
    ext i; fin_cases i
    · simp; have := hm0 m hm; omega
    · simp
    · simp
  rw [hmeq]

lemma linForm_embed_dvd_of_restrictA_eq_zero {K : Type*} [Field K] (a : Fin 2 → K)
    {H : MvPolynomial (Fin 3) K} (h0 : restrictA a H = 0) :
    linForm (embed a) ∣ H := by
  let σ : MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 3) K :=
    MvPolynomial.eval₂Hom C (fun i => match i with
      | 0 => X 0 - C (a 0) * X 1 - C (a 1) * X 2
      | 1 => X 1
      | 2 => X 2)
  let τ : MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 3) K :=
    MvPolynomial.eval₂Hom C (fun i => match i with
      | 0 => linForm (embed a)
      | 1 => X 1
      | 2 => X 2)
  have hτσ : ∀ P : MvPolynomial (Fin 3) K, τ (σ P) = P := by
    have hX0 : τ (σ (X 0)) = X 0 := by
      dsimp only [σ, τ]
      rw [MvPolynomial.eval₂Hom_X']
      change τ (X 0 - C (a 0) * X 1 - C (a 1) * X 2) = X 0
      simp only [τ, map_sub, map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
        linForm, embed]
      simp only [map_one, one_mul]
      ring
    intro P
    induction P using MvPolynomial.induction_on with
    | C c => simp [σ, τ]
    | add p q hp hq => simp [map_add, hp, hq]
    | mul_X p i hp =>
      fin_cases i
      · change τ (σ (p * X 0)) = p * X 0
        rw [map_mul, map_mul, hp, hX0]
      · rw [map_mul, map_mul, hp]; simp [σ, τ]
      · rw [map_mul, map_mul, hp]; simp [σ, τ]
  let ev0 : MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 2) K :=
    MvPolynomial.eval₂Hom C (fun i => match i with | 0 => 0 | 1 => X 0 | 2 => X 1)
  have hev0_σ : ∀ P : MvPolynomial (Fin 3) K, ev0 (σ P) = restrictA a P := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C c => simp [ev0, σ, restrictA]
    | add p q hp hq => simp [map_add, hp, hq]
    | mul_X p i hp =>
      fin_cases i
      · rw [map_mul, map_mul, map_mul, hp]; simp only [ev0, σ, restrictA, MvPolynomial.eval₂Hom_X',
          map_sub, map_mul, MvPolynomial.eval₂Hom_C, map_neg]; ring
      · rw [map_mul, map_mul, map_mul, hp]; simp [ev0, σ, restrictA]
      · rw [map_mul, map_mul, map_mul, hp]; simp [ev0, σ, restrictA]
  have hX0 : X (0 : Fin 3) ∣ σ H := X_zero_dvd_of_eval0_eq_zero (show ev0 (σ H) = 0 by rw [hev0_σ H, h0])
  rcases hX0 with ⟨Q, hQ⟩
  refine ⟨τ Q, ?_⟩
  have h1 := congrArg τ hQ
  rw [hτσ, map_mul] at h1
  have hτX : τ (X 0) = linForm (embed a) := by simp [τ]
  rwa [hτX] at h1

lemma isHomogeneous_rename_equiv {K : Type*} [Field K] {σ : Fin 3 ≃ Fin 3}
    {P : MvPolynomial (Fin 3) K} {d : ℕ} (hP : P.IsHomogeneous d) :
    (MvPolynomial.rename σ P).IsHomogeneous d := by
  rw [P.as_sum, map_sum]
  apply IsHomogeneous.sum
  intro m hm
  rw [MvPolynomial.rename_monomial]
  intro n hn
  rw [MvPolynomial.coeff_monomial] at hn
  have hneq : Finsupp.mapDomain σ m = n := by
    by_contra hne; exact hn (by simp [hne])
  rw [← hneq, weight_one_eq_degree, Finsupp.degree_apply]
  have hsum_eq : ∑ i ∈ (Finsupp.mapDomain σ m).support, (Finsupp.mapDomain σ m) i =
      ∑ i : Fin 3, (Finsupp.mapDomain σ m) i :=
    Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => Finsupp.notMem_support_iff.mp hi)
  rw [hsum_eq]
  calc ∑ i : Fin 3, (Finsupp.mapDomain σ m) i
      = ∑ i : Fin 3, (Finsupp.mapDomain σ m) (σ i) := (Equiv.sum_comp σ _).symm
    _ = ∑ i : Fin 3, m i := by
        apply Finset.sum_congr rfl; intro i _
        simp [Finsupp.mapDomain_apply, Finsupp.sum_fintype, Finsupp.single_apply, σ.injective.eq_iff]
    _ = d := isHomogeneous_sum_eq hP hm

lemma rename_swap_linForm {K : Type*} [Field K] (k : Fin 3) (w : Fin 3 → K) :
    MvPolynomial.rename (Equiv.swap (0 : Fin 3) k) (linForm w) =
      linForm (w ∘ Equiv.swap (0 : Fin 3) k) := by
  fin_cases k
  · simp [linForm]
  · simp [linForm, Equiv.swap_apply_def]; ring
  · simp [linForm, Equiv.swap_apply_def]; ring

lemma eval_u_H_eq_zero_of_deg_one {A E : Finset (Fin 2 → ZMod p)} (hp2 : p ≠ 2)
    (harc : ∀ s ⊆ A, s.card = 3 → ¬ Collinear (ZMod p) (s : Set (Fin 2 → ZMod p)))
    {e : Fin 2 → ZMod p} (he : e ∈ A) (hEA : E ⊆ A) (hE : E.card = 2 * (p + 2 - A.card) + 2)
    {P H : MvPolynomial (Fin 3) (ZMod p)} (hPh : P.IsHomogeneous 1)
    (hHh : H.IsHomogeneous (2 * (p + 2 - A.card) - 1))
    (hmul : P * H = segreEnv A E e)
    {a : Fin 2 → ZMod p} (ha : a ∈ A) {u : Fin 3 → ZMod p}
    (hu : u ∈ tangents A a) (hevP : eval u P = 0) :
    eval u H = 0 := by
  have hud := (mem_tangents.mp hu).2.1
  have hun := (mem_tangents.mp hu).1
  have hres : restrictA a P * restrictA a H = C 2 * gPoly A e a := by
    rw [← map_mul, hmul, restrictA_segreEnv harc he hEA hE ha]
  have hPa_ne : restrictA a P ≠ 0 := by
    intro h0; apply restrictA_segreEnv_ne_zero hp2 harc he hEA hE ha
    rw [← hmul, map_mul, h0, zero_mul]
  have hPa_hom : (restrictA a P).IsHomogeneous 1 := restrictA_isHomogeneous a hPh
  have hHa_hom : (restrictA a H).IsHomogeneous (2 * (p + 2 - A.card) - 1) :=
    restrictA_isHomogeneous a hHh
  by_cases hu2 : u 2 ≠ 0
  · set r := u 1 / u 2
    have hsm : (fun i : Fin 2 => match i with | 0 => r | 1 => 1) =
        (u 2)⁻¹ • (fun i : Fin 2 => match i with | 0 => u 1 | 1 => u 2) := by
      ext i; fin_cases i
      · simp [r, div_eq_mul_inv, mul_comm]
      · simp [inv_mul_cancel₀ hu2]
    have hrtP : (dehomog1 (restrictA a P)).IsRoot r := by
      rw [Polynomial.IsRoot.def, eval_dehomog1, hsm, isHomogeneous_eval_smul hPa_hom,
        eval_restrictA_of_dot3_zero a P hud, hevP, mul_zero]
    obtain ⟨cP, hcP⟩ := Polynomial.dvd_iff_isRoot.mpr hrtP
    have hqP_ne : dehomog1 (restrictA a P) ≠ 0 := fun h => hPa_ne (eq_zero_of_dehomog1_eq_zero hPa_hom h)
    have hcP_ne : cP ≠ 0 := by intro h; rw [h, mul_zero] at hcP; exact hqP_ne hcP
    have hlin_ne : Polynomial.X - Polynomial.C r ≠ 0 := Polynomial.X_sub_C_ne_zero r
    have hcP_deg : cP.natDegree = 0 := by
      have hle := natDegree_dehomog1_le hPa_hom
      rw [hcP, Polynomial.natDegree_mul hlin_ne hcP_ne, Polynomial.natDegree_X_sub_C] at hle
      omega
    have hcP_eq : cP = Polynomial.C (cP.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hcP_deg
    have hcP0_ne : cP.coeff 0 ≠ 0 := by intro h; rw [h, map_zero] at hcP_eq; exact hcP_ne hcP_eq
    obtain ⟨β, _, hg1⟩ := dehomog1_two_mul_gPoly hp2 he ha
    have hr_mem : r ∈ ((tangents A a).filter fun v => v 2 ≠ 0).image (fun v => v 1 / v 2) :=
      mem_image.mpr ⟨u, mem_filter.mpr ⟨hu, hu2⟩, rfl⟩
    have hsq_dvd : (Polynomial.X - Polynomial.C r) ^ 2 ∣ dehomog1 (C 2 * gPoly A e a) := by
      rw [hg1]
      exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hr_mem) _
    rcases hsq_dvd with ⟨Q, hQ⟩
    have hd1 : dehomog1 (restrictA a P) * dehomog1 (restrictA a H) =
        (Polynomial.X - Polynomial.C r) ^ 2 * Q := by
      rw [← map_mul, hres, hQ]
    have hlin_dvd_H : Polynomial.X - Polynomial.C r ∣ dehomog1 (restrictA a H) := by
      refine ⟨Polynomial.C (cP.coeff 0)⁻¹ * Q, ?_⟩
      apply mul_left_cancel₀ hlin_ne
      apply mul_left_cancel₀ (Polynomial.C_ne_zero.mpr hcP0_ne)
      calc Polynomial.C (cP.coeff 0) * ((Polynomial.X - Polynomial.C r) * dehomog1 (restrictA a H))
          = dehomog1 (restrictA a P) * dehomog1 (restrictA a H) := by
              conv_rhs => rw [hcP, hcP_eq]
              ring
        _ = (Polynomial.X - Polynomial.C r) ^ 2 * Q := hd1
        _ = Polynomial.C (cP.coeff 0) * ((Polynomial.X - Polynomial.C r) *
              ((Polynomial.X - Polynomial.C r) * (Polynomial.C (cP.coeff 0)⁻¹ * Q))) := by
            have hinv : Polynomial.C (cP.coeff 0) * Polynomial.C (cP.coeff 0)⁻¹ = 1 := by
              rw [← map_mul, mul_inv_cancel₀ hcP0_ne, map_one]
            calc (Polynomial.X - Polynomial.C r) ^ 2 * Q
                = (Polynomial.C (cP.coeff 0) * Polynomial.C (cP.coeff 0)⁻¹) *
                    ((Polynomial.X - Polynomial.C r) ^ 2 * Q) := by rw [hinv, one_mul]
              _ = _ := by ring
    have hevH_r : Polynomial.eval r (dehomog1 (restrictA a H)) = 0 := by
      rcases hlin_dvd_H with ⟨v, hv⟩
      rw [hv, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        sub_self, zero_mul]
    rw [eval_dehomog1, hsm, isHomogeneous_eval_smul hHa_hom,
      eval_restrictA_of_dot3_zero a H hud] at hevH_r
    exact (mul_eq_zero.mp hevH_r).resolve_left (pow_ne_zero _ (inv_ne_zero hu2))
  · have hu2' : u 2 = 0 := not_not.mp hu2
    have hu1 : u 1 ≠ 0 := by
      intro h1
      have hu0 : u 0 = 0 := by unfold dot3 embed at hud; dsimp only at hud; rw [h1, hu2'] at hud; linear_combination hud
      exact isNorm_ne_zero hun (by ext i; fin_cases i <;> assumption)
    have hsm : (fun i : Fin 2 => match i with | 0 => u 1 | 1 => u 2) =
        u 1 • (fun i : Fin 2 => match i with | 0 => (1 : ZMod p) | 1 => 0) := by
      ext i; fin_cases i <;> simp [hu2']
    have hev10 : eval (fun i : Fin 2 => match i with | 0 => (1 : ZMod p) | 1 => 0) (restrictA a P) = 0 := by
      have h := eval_restrictA_of_dot3_zero a P hud
      rw [hevP, hsm, isHomogeneous_eval_smul hPa_hom] at h
      exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 1 hu1)
    have hdeg1_0 : (dehomog1 (restrictA a P)).natDegree = 0 := by
      have hle := natDegree_dehomog1_le hPa_hom
      have hc1 : (dehomog1 (restrictA a P)).coeff 1 = 0 := by
        rw [← eval_one_zero_eq_coeff_dehomog1 hPa_hom]; exact hev10
      by_contra hne
      have heq1 : (dehomog1 (restrictA a P)).natDegree = 1 := by omega
      have hlc : (dehomog1 (restrictA a P)).leadingCoeff = 0 := by
        rw [Polynomial.leadingCoeff, heq1]; exact hc1
      exact hPa_ne (eq_zero_of_dehomog1_eq_zero hPa_hom (Polynomial.leadingCoeff_eq_zero.mp hlc))
    have hX_dvd_P : Polynomial.X ∣ dehomog0 (restrictA a P) := by
      have h := X_pow_dvd_dehomog0_of_natDegree_dehomog1 hPa_hom
      simpa [hdeg1_0] using h
    rcases hX_dvd_P with ⟨cP, hcP⟩
    have hqP0_ne : dehomog0 (restrictA a P) ≠ 0 := fun h => hPa_ne (eq_zero_of_dehomog0_eq_zero hPa_hom h)
    have hcP_ne : cP ≠ 0 := by intro h; rw [h, mul_zero] at hcP; exact hqP0_ne hcP
    have hnd0_le : (dehomog0 (restrictA a P)).natDegree ≤ 1 := by
      apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro k hk
      rw [coeff_dehomog0_of_isHomogeneous hPa_hom]
      have hnot : ¬ k ≤ 1 := by omega
      simp [hnot]
    have hcP_deg : cP.natDegree = 0 := by
      rw [hcP, Polynomial.natDegree_mul Polynomial.X_ne_zero hcP_ne, Polynomial.natDegree_X] at hnd0_le
      omega
    have hcP_eq : cP = Polynomial.C (cP.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hcP_deg
    have hcP0_ne : cP.coeff 0 ≠ 0 := by intro h; rw [h, map_zero] at hcP_eq; exact hcP_ne hcP_eq
    obtain ⟨q₀, _, hg0⟩ := dehomog0_two_mul_gPoly hp2 he ha
    have hc0_eq : ((tangents A a).filter fun v => v 2 = 0).card = 1 := by
      have hle := tangents_filter_u2_eq_zero_card_le_one (A := A) (a := a)
      have hge : 1 ≤ ((tangents A a).filter fun v => v 2 = 0).card :=
        card_pos.mpr ⟨u, mem_filter.mpr ⟨hu, hu2'⟩⟩
      omega
    rw [hc0_eq] at hg0
    have hd0 : dehomog0 (restrictA a P) * dehomog0 (restrictA a H) = Polynomial.X ^ 2 * q₀ := by
      rw [← map_mul, hres, hg0]
    have hX_dvd_H : Polynomial.X ∣ dehomog0 (restrictA a H) := by
      refine ⟨Polynomial.C (cP.coeff 0)⁻¹ * q₀, ?_⟩
      apply mul_left_cancel₀ Polynomial.X_ne_zero
      apply mul_left_cancel₀ (Polynomial.C_ne_zero.mpr hcP0_ne)
      calc Polynomial.C (cP.coeff 0) * (Polynomial.X * dehomog0 (restrictA a H))
          = dehomog0 (restrictA a P) * dehomog0 (restrictA a H) := by
              conv_rhs => rw [hcP, hcP_eq]
              ring
        _ = Polynomial.X ^ 2 * q₀ := hd0
        _ = Polynomial.C (cP.coeff 0) * (Polynomial.X *
              (Polynomial.X * (Polynomial.C (cP.coeff 0)⁻¹ * q₀))) := by
            have hinv : Polynomial.C (cP.coeff 0) * Polynomial.C (cP.coeff 0)⁻¹ = 1 := by
              rw [← map_mul, mul_inv_cancel₀ hcP0_ne, map_one]
            calc Polynomial.X ^ 2 * q₀
                = (Polynomial.C (cP.coeff 0) * Polynomial.C (cP.coeff 0)⁻¹) *
                    (Polynomial.X ^ 2 * q₀) := by rw [hinv, one_mul]
              _ = _ := by ring
    have hevH_0 : Polynomial.eval 0 (dehomog0 (restrictA a H)) = 0 := by
      rcases hX_dvd_H with ⟨v, hv⟩; rw [hv, Polynomial.eval_mul, Polynomial.eval_X, zero_mul]
    rw [eval_dehomog0] at hevH_0
    rw [← eval_restrictA_of_dot3_zero a H hud, hsm, isHomogeneous_eval_smul hHa_hom, hevH_0, mul_zero]

lemma card_le_four_mul_t_of_deg_one {A E : Finset (Fin 2 → ZMod p)} (hp2 : p ≠ 2)
    (harc : ∀ s ⊆ A, s.card = 3 → ¬ Collinear (ZMod p) (s : Set (Fin 2 → ZMod p)))
    {e : Fin 2 → ZMod p} (he : e ∈ A) (hEA : E ⊆ A) (hE : E.card = 2 * (p + 2 - A.card) + 2)
    {P H : MvPolynomial (Fin 3) (ZMod p)} (hPh : P.IsHomogeneous 1)
    (hHh : H.IsHomogeneous (2 * (p + 2 - A.card) - 1))
    (hmul : P * H = segreEnv A E e) (hnot : ¬ (P ∣ H)) :
    A.card ≤ 4 * (p + 2 - A.card) := by
  classical
  set t := p + 2 - A.card
  have hP0 : P ≠ 0 := by
    intro h; apply segreEnv_ne_zero hp2 harc he hEA hE; rw [← hmul, h, zero_mul]
  let w : Fin 3 → ZMod p := fun i => P.coeff (Finsupp.single i 1)
  have hPw : P = linForm w := homog1_eq_linForm hPh
  have hw0 : w ≠ 0 := by
    intro h; apply hP0; rw [hPw, h]; simp [linForm]
  have hex_k : ∃ k : Fin 3, w k ≠ 0 := by
    by_contra h; apply hw0; ext i; exact not_not.mp (fun hi => h ⟨i, hi⟩)
  obtain ⟨k, hwk⟩ := hex_k
  let σ : Fin 3 ≃ Fin 3 := Equiv.swap 0 k
  let w' : Fin 3 → ZMod p := w ∘ σ
  have hw'0 : w' 0 ≠ 0 := by simpa [w', σ] using hwk
  let a' : Fin 2 → ZMod p := fun j => match j with | 0 => w' 1 / w' 0 | 1 => w' 2 / w' 0
  let H' : MvPolynomial (Fin 3) (ZMod p) := MvPolynomial.rename σ H
  have hH'h : H'.IsHomogeneous (2 * t - 1) := isHomogeneous_rename_equiv hHh
  have hres_ne : restrictA a' H' ≠ 0 := by
    intro h0
    have hdvd_a' : linForm (embed a') ∣ H' := linForm_embed_dvd_of_restrictA_eq_zero a' h0
    have hlw' : linForm w' = C (w' 0) * linForm (embed a') := by
      unfold linForm embed a'; dsimp only
      simp only [mul_add, ← mul_assoc, ← map_mul]
      rw [mul_one, mul_div_cancel₀ _ hw'0, mul_div_cancel₀ _ hw'0]
    have hdvd_w' : linForm w' ∣ H' := by
      rcases hdvd_a' with ⟨Q, hQ⟩
      refine ⟨C (w' 0)⁻¹ * Q, ?_⟩
      rw [hlw', hQ]
      have hinv : C (w' 0) * C (w' 0)⁻¹ = (1 : MvPolynomial (Fin 3) (ZMod p)) := by
        rw [← map_mul, mul_inv_cancel₀ hw'0, map_one]
      calc linForm (embed a') * Q
          = (C (w' 0) * C (w' 0)⁻¹) * (linForm (embed a') * Q) := by rw [hinv, one_mul]
        _ = _ := by ring
    apply hnot
    rcases hdvd_w' with ⟨Q, hQ⟩
    refine ⟨MvPolynomial.rename σ Q, ?_⟩
    have hren := congrArg (MvPolynomial.rename σ) hQ
    rw [map_mul] at hren
    have hH_back : MvPolynomial.rename σ H' = H := by
      dsimp only [H']
      rw [MvPolynomial.rename_rename]
      have hcomp : (σ : Fin 3 → Fin 3) ∘ σ = id := by funext i; exact Equiv.swap_apply_self 0 k i
      rw [hcomp, MvPolynomial.rename_id]
      rfl
    have hP_back : MvPolynomial.rename σ (linForm w') = P := by
      rw [rename_swap_linForm, hPw]
      congr 1; ext i; exact congrArg w (Equiv.swap_apply_self 0 k i)
    rw [hH_back, hP_back] at hren
    exact hren
  -- For each a in A, pick u_a in tangents A a with eval u_a P = 0 (hence eval u_a H = 0)
  have hu_ex : ∀ a ∈ A, ∃ u ∈ tangents A a, eval u P = 0 := by
    intro a ha
    have h1 := deg_le_two_mul_card_tangents_zeros hp2 harc he hEA hE hPh ⟨H, hmul.symm⟩ ha
    obtain ⟨u, hu⟩ := card_pos.mp (show 0 < ((tangents A a).filter fun u => eval u P = 0).card by omega)
    exact ⟨u, (mem_filter.mp hu).1, (mem_filter.mp hu).2⟩
  let uA : (Fin 2 → ZMod p) → Fin 3 → ZMod p := fun a =>
    if h : a ∈ A then Classical.choose (hu_ex a h) else 0
  have huA_mem : ∀ a ∈ A, uA a ∈ tangents A a ∧ eval (uA a) P = 0 := by
    intro a ha
    dsimp only [uA]
    simp only [ha, dite_true]
    exact Classical.choose_spec (hu_ex a ha)
  let π : (Fin 3 → ZMod p) → Fin 2 → ZMod p := fun u j => match j with
    | 0 => u (σ 1) | 1 => u (σ 2)
  let f : (Fin 2 → ZMod p) → Fin 2 → ZMod p := fun a => π (uA a)
  have hdot_w' : ∀ a ∈ A, dot3 (uA a ∘ σ) (embed a') = 0 := by
    intro a ha
    have hev0 := (huA_mem a ha).2
    rw [hPw, eval_linForm] at hev0
    have hdw : dot3 w' (uA a ∘ σ) = 0 := by
      have h1 : dot3 w' (uA a ∘ σ) = dot3 w (uA a) := by
        unfold dot3 w' σ; fin_cases k <;> simp [Equiv.swap_apply_def] <;> ring
      rw [h1]; exact hev0
    unfold dot3 at hdw; simp only [Function.comp_apply] at hdw
    unfold dot3 embed a'; dsimp only; simp only [Function.comp_apply]
    apply mul_left_cancel₀ hw'0
    calc w' 0 * (uA a (σ 0) * 1 + uA a (σ 1) * (w' 1 / w' 0) + uA a (σ 2) * (w' 2 / w' 0))
        = w' 0 * uA a (σ 0) + (w' 0 * (w' 1 / w' 0)) * uA a (σ 1) +
            (w' 0 * (w' 2 / w' 0)) * uA a (σ 2) := by ring
      _ = w' 0 * uA a (σ 0) + w' 1 * uA a (σ 1) + w' 2 * uA a (σ 2) := by
            rw [mul_div_cancel₀ _ hw'0, mul_div_cancel₀ _ hw'0]
      _ = 0 := hdw
      _ = w' 0 * 0 := (mul_zero _).symm
  have hnp_A : ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ ≠ a₂ →
      f a₁ 0 * f a₂ 1 - f a₁ 1 * f a₂ 0 ≠ 0 := by
    intro a₁ ha₁ a₂ ha₂ hne hdet0
    have hu1_tan := (huA_mem a₁ ha₁).1
    have hu2_tan := (huA_mem a₂ ha₂).1
    have hu1_ne : uA a₁ ≠ uA a₂ := fun heq =>
      Finset.disjoint_left.mp (tangents_disjoint ha₁ ha₂ hne) hu1_tan (heq ▸ hu2_tan)
    have hn1 := (mem_tangents.mp hu1_tan).1
    have hn2 := (mem_tangents.mp hu2_tan).1
    have hd1 := hdot_w' a₁ ha₁
    have hd2 := hdot_w' a₂ ha₂
    -- Both uA a₁ ∘ σ and uA a₂ ∘ σ are orthogonal to embed a' and have proportional (1,2) coords
    have hprop : ∃ c : ZMod p, uA a₁ = c • uA a₂ := by
      have h12 : uA a₁ (σ 1) * uA a₂ (σ 2) = uA a₁ (σ 2) * uA a₂ (σ 1) := sub_eq_zero.mp hdet0
      by_cases h2 : uA a₂ (σ 2) ≠ 0
      · refine ⟨uA a₁ (σ 2) / uA a₂ (σ 2), ?_⟩
        have hc1 : uA a₁ (σ 1) = (uA a₁ (σ 2) / uA a₂ (σ 2)) * uA a₂ (σ 1) := by
          apply mul_left_cancel₀ h2
          calc uA a₂ (σ 2) * uA a₁ (σ 1) = uA a₁ (σ 1) * uA a₂ (σ 2) := mul_comm _ _
            _ = uA a₁ (σ 2) * uA a₂ (σ 1) := h12
            _ = (uA a₁ (σ 2) / uA a₂ (σ 2) * uA a₂ (σ 2)) * uA a₂ (σ 1) := by rw [div_mul_cancel₀ _ h2]
            _ = uA a₂ (σ 2) * (uA a₁ (σ 2) / uA a₂ (σ 2) * uA a₂ (σ 1)) := by ring
        have hc0 : uA a₁ (σ 0) = (uA a₁ (σ 2) / uA a₂ (σ 2)) * uA a₂ (σ 0) := by
          have e1 : uA a₁ (σ 0) = -a' 0 * uA a₁ (σ 1) - a' 1 * uA a₁ (σ 2) := by
            unfold dot3 embed at hd1; dsimp only at hd1; simp only [Function.comp_apply] at hd1; linear_combination hd1
          have e2 : uA a₂ (σ 0) = -a' 0 * uA a₂ (σ 1) - a' 1 * uA a₂ (σ 2) := by
            unfold dot3 embed at hd2; dsimp only at hd2; simp only [Function.comp_apply] at hd2; linear_combination hd2
          rw [e1, e2, hc1]
          calc -a' 0 * (uA a₁ (σ 2) / uA a₂ (σ 2) * uA a₂ (σ 1)) - a' 1 * uA a₁ (σ 2)
              = -a' 0 * (uA a₁ (σ 2) / uA a₂ (σ 2) * uA a₂ (σ 1)) -
                  a' 1 * (uA a₁ (σ 2) / uA a₂ (σ 2) * uA a₂ (σ 2)) := by rw [div_mul_cancel₀ _ h2]
            _ = _ := by ring
        ext i
        have hi : uA a₁ (σ (σ i)) = (uA a₁ (σ 2) / uA a₂ (σ 2)) * uA a₂ (σ (σ i)) := by
          generalize σ i = j
          fin_cases j
          · exact hc0
          · exact hc1
          · change uA a₁ (σ 2) = uA a₁ (σ 2) / uA a₂ (σ 2) * uA a₂ (σ 2)
            rw [div_mul_cancel₀ _ h2]
        simpa [σ] using hi
      · have h2' : uA a₂ (σ 2) = 0 := not_not.mp h2
        have h1 : uA a₂ (σ 1) ≠ 0 := by
          intro h1
          have h0 : uA a₂ (σ 0) = 0 := by
            unfold dot3 embed at hd2; dsimp only at hd2; simp only [Function.comp_apply] at hd2
            rw [h1, h2'] at hd2; linear_combination hd2
          apply isNorm_ne_zero hn2
          ext i
          have hi : uA a₂ (σ (σ i)) = 0 := by generalize σ i = j; fin_cases j <;> assumption
          simpa [σ] using hi
        rw [h2', mul_zero] at h12
        have h12' : uA a₁ (σ 2) = 0 := (mul_eq_zero.mp h12.symm).resolve_right h1
        refine ⟨uA a₁ (σ 1) / uA a₂ (σ 1), ?_⟩
        have hc0 : uA a₁ (σ 0) = (uA a₁ (σ 1) / uA a₂ (σ 1)) * uA a₂ (σ 0) := by
          have e1 : uA a₁ (σ 0) = -a' 0 * uA a₁ (σ 1) := by
            unfold dot3 embed at hd1; dsimp only at hd1; simp only [Function.comp_apply] at hd1
            rw [h12'] at hd1; linear_combination hd1
          have e2 : uA a₂ (σ 0) = -a' 0 * uA a₂ (σ 1) := by
            unfold dot3 embed at hd2; dsimp only at hd2; simp only [Function.comp_apply] at hd2
            rw [h2'] at hd2; linear_combination hd2
          rw [e1, e2]
          calc -a' 0 * uA a₁ (σ 1) = -a' 0 * (uA a₁ (σ 1) / uA a₂ (σ 1) * uA a₂ (σ 1)) := by
                rw [div_mul_cancel₀ _ h1]
            _ = _ := by ring
        ext i
        have hi : uA a₁ (σ (σ i)) = (uA a₁ (σ 1) / uA a₂ (σ 1)) * uA a₂ (σ (σ i)) := by
          generalize σ i = j
          fin_cases j
          · exact hc0
          · change uA a₁ (σ 1) = uA a₁ (σ 1) / uA a₂ (σ 1) * uA a₂ (σ 1)
            rw [div_mul_cancel₀ _ h1]
          · change uA a₁ (σ 2) = uA a₁ (σ 1) / uA a₂ (σ 1) * uA a₂ (σ 2)
            rw [h12', h2', mul_zero]
        simpa [σ] using hi
    obtain ⟨c, hc⟩ := hprop
    exact hu1_ne (isNorm_eq_of_smul hn1 hn2 hc)
  have hf_inj : Set.InjOn f A := by
    intro a₁ ha₁ a₂ ha₂ heq
    by_contra hne
    apply hnp_A a₁ ha₁ a₂ ha₂ hne
    rw [heq]; ring
  let S := A.image f
  have hScard : S.card = A.card := card_image_of_injOn hf_inj
  by_contra hgt
  have hcard_ge : (2 * t - 1) + 1 ≤ S.card := by omega
  apply hres_ne
  apply homog2_eq_zero_of_roots (restrictA_isHomogeneous a' hH'h) hcard_ge
  · intro v hv
    rcases mem_image.mp hv with ⟨a, ha, rfl⟩
    intro h0
    have h1 : uA a (σ 1) = 0 := congrFun h0 0
    have h2 : uA a (σ 2) = 0 := congrFun h0 1
    have hd := hdot_w' a ha
    have h0' : uA a (σ 0) = 0 := by
      unfold dot3 embed at hd; dsimp only at hd; simp only [Function.comp_apply] at hd
      rw [h1, h2] at hd; linear_combination hd
    apply isNorm_ne_zero (mem_tangents.mp (huA_mem a ha).1).1
    ext i
    have hi : uA a (σ (σ i)) = 0 := by generalize σ i = j; fin_cases j <;> assumption
    simpa [σ] using hi
  · intro v hv w hw hvw
    rcases mem_image.mp hv with ⟨a₁, ha₁, rfl⟩
    rcases mem_image.mp hw with ⟨a₂, ha₂, rfl⟩
    exact hnp_A a₁ ha₁ a₂ ha₂ (fun h => hvw (congrArg f h))
  · intro v hv
    rcases mem_image.mp hv with ⟨a, ha, rfl⟩
    have harg : f a = (fun i : Fin 2 => match i with | 0 => (uA a ∘ σ) 1 | 1 => (uA a ∘ σ) 2) := by
      ext i; fin_cases i <;> rfl
    rw [harg, eval_restrictA_of_dot3_zero a' H' (hdot_w' a ha)]
    dsimp only [H']
    rw [MvPolynomial.eval_rename]
    have hcomp : (uA a ∘ σ) ∘ σ = uA a := by ext i; exact congrArg (uA a) (Equiv.swap_apply_self 0 k i)
    rw [hcomp]
    exact eval_u_H_eq_zero_of_deg_one hp2 harc he hEA hE hPh hHh hmul ha
      (huA_mem a ha).1 (huA_mem a ha).2

end DegOne

section DegTwo

variable {p : ℕ} [Fact p.Prime]

lemma card_lineThrough_ne_zero {v : Fin 3 → ZMod p} (hv : v ≠ 0) :
    (lineThrough v).card = p + 1 := by
  classical
  have hex_k : ∃ k : Fin 3, v k ≠ 0 := by
    by_contra h; apply hv; ext i; exact not_not.mp (fun hi => h ⟨i, hi⟩)
  obtain ⟨k, hvk⟩ := hex_k
  let σ : Fin 3 ≃ Fin 3 := Equiv.swap 0 k
  let a' : Fin 2 → ZMod p := fun j => match j with | 0 => v (σ 1) / v k | 1 => v (σ 2) / v k
  have hv_dot_iff : ∀ u : Fin 3 → ZMod p, dot3 (u ∘ σ) (embed a') = 0 ↔ dot3 u v = 0 := by
    intro u
    have hsw : dot3 (u ∘ σ) (v ∘ σ) = dot3 u v := by
      unfold dot3 σ; fin_cases k <;> simp [Equiv.swap_apply_def] <;> ring
    have hmul : v k * dot3 (u ∘ σ) (embed a') = dot3 (u ∘ σ) (v ∘ σ) := by
      unfold dot3 embed a'; dsimp only; simp only [Function.comp_apply]
      have h0 : v (σ 0) = v k := by simp [σ]
      rw [h0]
      calc v k * (u (σ 0) * 1 + u (σ 1) * (v (σ 1) / v k) + u (σ 2) * (v (σ 2) / v k))
          = u (σ 0) * v k + u (σ 1) * (v k * (v (σ 1) / v k)) +
              u (σ 2) * (v k * (v (σ 2) / v k)) := by ring
        _ = u (σ 0) * v k + u (σ 1) * v (σ 1) + u (σ 2) * v (σ 2) := by
              rw [mul_div_cancel₀ _ hvk, mul_div_cancel₀ _ hvk]
    rw [← hsw, ← hmul]
    exact ⟨fun h => by rw [h, mul_zero], fun h => (mul_eq_zero.mp h).resolve_left hvk⟩
  let φ : (Fin 3 → ZMod p) → Fin 3 → ZMod p := fun u => norm3 (u ∘ σ)
  have hcomp_ne : ∀ {u : Fin 3 → ZMod p}, u ≠ 0 → u ∘ σ ≠ 0 := by
    intro u hu h0; apply hu; ext i
    have := congrFun h0 (σ i); simpa [σ] using this
  have hφ_mem : ∀ u ∈ lineThrough v, φ u ∈ lineThrough (embed a') := by
    intro u hu
    obtain ⟨hun, hud⟩ := mem_lineThrough.mp hu
    have hne : u ∘ σ ≠ 0 := hcomp_ne (isNorm_ne_zero hun)
    obtain ⟨c, _, hc⟩ := norm3_exists_smul hne
    rw [mem_lineThrough]
    refine ⟨norm3_isNorm hne, ?_⟩
    change dot3 (norm3 (u ∘ σ)) (embed a') = 0
    rw [hc, dot3_smul_left, (hv_dot_iff u).mpr hud, mul_zero]
  have hφ_inj : Set.InjOn φ (lineThrough v) := by
    intro u₁ hu₁ u₂ hu₂ heq
    have hn1 := (mem_lineThrough.mp hu₁).1
    have hn2 := (mem_lineThrough.mp hu₂).1
    obtain ⟨c, _, hc⟩ := (norm3_eq_iff_prop (hcomp_ne (isNorm_ne_zero hn1))
      (hcomp_ne (isNorm_ne_zero hn2))).mp heq
    apply isNorm_eq_of_smul hn1 hn2 (c := c)
    ext i
    have hi := congrFun hc (σ i)
    simpa [σ] using hi
  have hφ_img : (lineThrough v).image φ = lineThrough (embed a') := by
    apply Finset.Subset.antisymm
    · intro w hw; rcases mem_image.mp hw with ⟨u, hu, rfl⟩; exact hφ_mem u hu
    · intro w hw
      obtain ⟨hwn, hwd⟩ := mem_lineThrough.mp hw
      have hne : w ∘ σ ≠ 0 := hcomp_ne (isNorm_ne_zero hwn)
      let u := norm3 (w ∘ σ)
      obtain ⟨c, hc0, hcu⟩ := norm3_exists_smul hne
      have hu_mem : u ∈ lineThrough v := by
        rw [mem_lineThrough]
        refine ⟨norm3_isNorm hne, ?_⟩
        rw [← hv_dot_iff]
        have hcomp : u ∘ σ = c • w := by
          ext i
          have hi : u (σ i) = c * w (σ (σ i)) := congrFun hcu (σ i)
          simpa [σ] using hi
        rw [hcomp, dot3_smul_left, hwd, mul_zero]
      refine mem_image.mpr ⟨u, hu_mem, ?_⟩
      change norm3 (u ∘ σ) = w
      have hcomp : u ∘ σ = c • w := by
        ext i
        have hi : u (σ i) = c * w (σ (σ i)) := congrFun hcu (σ i)
        simpa [σ] using hi
      rw [hcomp]
      conv_rhs => rw [← norm3_eq_self hwn]
      rw [norm3_eq_iff_prop (smul_ne_zero hc0 (isNorm_ne_zero hwn)) (isNorm_ne_zero hwn)]
      exact ⟨c, hc0, rfl⟩
  rw [← card_lineThrough_embed a', ← hφ_img, card_image_of_injOn hφ_inj]

structure SymQuad (K : Type*) where
  a00 : K
  a11 : K
  a22 : K
  a01 : K
  a02 : K
  a12 : K

namespace SymQuad

variable {K : Type*} [CommRing K]

def det (Q : SymQuad K) : K :=
  Q.a00 * Q.a11 * Q.a22 + 2 * Q.a01 * Q.a02 * Q.a12 -
    Q.a00 * Q.a12 ^ 2 - Q.a11 * Q.a02 ^ 2 - Q.a22 * Q.a01 ^ 2

def adj (Q : SymQuad K) : SymQuad K where
  a00 := Q.a11 * Q.a22 - Q.a12 ^ 2
  a11 := Q.a00 * Q.a22 - Q.a02 ^ 2
  a22 := Q.a00 * Q.a11 - Q.a01 ^ 2
  a01 := Q.a02 * Q.a12 - Q.a01 * Q.a22
  a02 := Q.a01 * Q.a12 - Q.a02 * Q.a11
  a12 := Q.a01 * Q.a02 - Q.a12 * Q.a00

def mulVec (Q : SymQuad K) (u : Fin 3 → K) : Fin 3 → K := fun i =>
  match i with
  | 0 => Q.a00 * u 0 + Q.a01 * u 1 + Q.a02 * u 2
  | 1 => Q.a01 * u 0 + Q.a11 * u 1 + Q.a12 * u 2
  | 2 => Q.a02 * u 0 + Q.a12 * u 1 + Q.a22 * u 2

def bilin (Q : SymQuad K) (u v : Fin 3 → K) : K :=
  u 0 * (Q.a00 * v 0 + Q.a01 * v 1 + Q.a02 * v 2) +
  u 1 * (Q.a01 * v 0 + Q.a11 * v 1 + Q.a12 * v 2) +
  u 2 * (Q.a02 * v 0 + Q.a12 * v 1 + Q.a22 * v 2)

def evalQ (Q : SymQuad K) (u : Fin 3 → K) : K := Q.bilin u u

noncomputable def toPoly (Q : SymQuad K) : MvPolynomial (Fin 3) K :=
  C Q.a00 * X 0 ^ 2 + C Q.a11 * X 1 ^ 2 + C Q.a22 * X 2 ^ 2 +
  C (2 * Q.a01) * X 0 * X 1 + C (2 * Q.a02) * X 0 * X 2 + C (2 * Q.a12) * X 1 * X 2

noncomputable def toAffPoly (Q : SymQuad K) : MvPolynomial (Fin 2) K :=
  C Q.a00 + C (2 * Q.a01) * X 0 + C (2 * Q.a02) * X 1 +
  C Q.a11 * X 0 ^ 2 + C (2 * Q.a12) * X 0 * X 1 + C Q.a22 * X 1 ^ 2

def map {L : Type*} [CommRing L] (φ : K →+* L) (Q : SymQuad K) : SymQuad L where
  a00 := φ Q.a00
  a11 := φ Q.a11
  a22 := φ Q.a22
  a01 := φ Q.a01
  a02 := φ Q.a02
  a12 := φ Q.a12

lemma map_det {L : Type*} [CommRing L] (φ : K →+* L) (Q : SymQuad K) :
    (Q.map φ).det = φ Q.det := by
  simp [SymQuad.map, SymQuad.det, map_add, map_sub, map_mul, map_pow, map_ofNat]

lemma map_toPoly {L : Type*} [CommRing L] (φ : K →+* L) (Q : SymQuad K) :
    MvPolynomial.map φ Q.toPoly = (Q.map φ).toPoly := by
  simp [SymQuad.toPoly, SymQuad.map, map_add, map_mul, map_pow, map_ofNat]

lemma bilin_symm (Q : SymQuad K) (u v : Fin 3 → K) : Q.bilin u v = Q.bilin v u := by
  unfold bilin; ring

lemma bilin_eq_dot3 {F : Type*} [Field F] (Q : SymQuad F) (u v : Fin 3 → F) :
    Q.bilin u v = dot3 u (Q.mulVec v) := rfl

lemma bilin_smul_left (Q : SymQuad K) (c : K) (u v : Fin 3 → K) :
    Q.bilin (c • u) v = c * Q.bilin u v := by
  unfold bilin; simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma bilin_smul_right (Q : SymQuad K) (c : K) (u v : Fin 3 → K) :
    Q.bilin u (c • v) = c * Q.bilin u v := by
  unfold bilin; simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma bilin_add_right (Q : SymQuad K) (u v w : Fin 3 → K) :
    Q.bilin u (v + w) = Q.bilin u v + Q.bilin u w := by
  unfold bilin; simp only [Pi.add_apply]; ring

lemma evalQ_smul (Q : SymQuad K) (c : K) (u : Fin 3 → K) :
    Q.evalQ (c • u) = c ^ 2 * Q.evalQ u := by
  unfold evalQ bilin; simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma evalQ_add_smul (Q : SymQuad K) (s t : K) (u v : Fin 3 → K) :
    Q.evalQ (s • u + t • v) = s ^ 2 * Q.evalQ u + 2 * s * t * Q.bilin u v + t ^ 2 * Q.evalQ v := by
  unfold evalQ bilin; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma mulVec_smul (Q : SymQuad K) (c : K) (u : Fin 3 → K) :
    Q.mulVec (c • u) = c • Q.mulVec u := by
  ext i; fin_cases i <;> (unfold mulVec; dsimp only; simp only [Pi.smul_apply, smul_eq_mul]; ring)

lemma adj_mulVec_mulVec (Q : SymQuad K) (u : Fin 3 → K) :
    Q.adj.mulVec (Q.mulVec u) = Q.det • u := by
  ext i; fin_cases i
  · change (Q.a11 * Q.a22 - Q.a12 ^ 2) * (Q.a00 * u 0 + Q.a01 * u 1 + Q.a02 * u 2) +
        (Q.a02 * Q.a12 - Q.a01 * Q.a22) * (Q.a01 * u 0 + Q.a11 * u 1 + Q.a12 * u 2) +
        (Q.a01 * Q.a12 - Q.a02 * Q.a11) * (Q.a02 * u 0 + Q.a12 * u 1 + Q.a22 * u 2) = Q.det * u 0
    unfold det; ring
  · change (Q.a02 * Q.a12 - Q.a01 * Q.a22) * (Q.a00 * u 0 + Q.a01 * u 1 + Q.a02 * u 2) +
        (Q.a00 * Q.a22 - Q.a02 ^ 2) * (Q.a01 * u 0 + Q.a11 * u 1 + Q.a12 * u 2) +
        (Q.a01 * Q.a02 - Q.a12 * Q.a00) * (Q.a02 * u 0 + Q.a12 * u 1 + Q.a22 * u 2) = Q.det * u 1
    unfold det; ring
  · change (Q.a01 * Q.a12 - Q.a02 * Q.a11) * (Q.a00 * u 0 + Q.a01 * u 1 + Q.a02 * u 2) +
        (Q.a01 * Q.a02 - Q.a12 * Q.a00) * (Q.a01 * u 0 + Q.a11 * u 1 + Q.a12 * u 2) +
        (Q.a00 * Q.a11 - Q.a01 ^ 2) * (Q.a02 * u 0 + Q.a12 * u 1 + Q.a22 * u 2) = Q.det * u 2
    unfold det; ring

lemma mulVec_adj_mulVec (Q : SymQuad K) (u : Fin 3 → K) :
    Q.mulVec (Q.adj.mulVec u) = Q.det • u := by
  ext i; fin_cases i
  · change Q.a00 * ((Q.a11 * Q.a22 - Q.a12 ^ 2) * u 0 + (Q.a02 * Q.a12 - Q.a01 * Q.a22) * u 1 +
          (Q.a01 * Q.a12 - Q.a02 * Q.a11) * u 2) +
        Q.a01 * ((Q.a02 * Q.a12 - Q.a01 * Q.a22) * u 0 + (Q.a00 * Q.a22 - Q.a02 ^ 2) * u 1 +
          (Q.a01 * Q.a02 - Q.a12 * Q.a00) * u 2) +
        Q.a02 * ((Q.a01 * Q.a12 - Q.a02 * Q.a11) * u 0 + (Q.a01 * Q.a02 - Q.a12 * Q.a00) * u 1 +
          (Q.a00 * Q.a11 - Q.a01 ^ 2) * u 2) = Q.det * u 0
    unfold det; ring
  · change Q.a01 * ((Q.a11 * Q.a22 - Q.a12 ^ 2) * u 0 + (Q.a02 * Q.a12 - Q.a01 * Q.a22) * u 1 +
          (Q.a01 * Q.a12 - Q.a02 * Q.a11) * u 2) +
        Q.a11 * ((Q.a02 * Q.a12 - Q.a01 * Q.a22) * u 0 + (Q.a00 * Q.a22 - Q.a02 ^ 2) * u 1 +
          (Q.a01 * Q.a02 - Q.a12 * Q.a00) * u 2) +
        Q.a12 * ((Q.a01 * Q.a12 - Q.a02 * Q.a11) * u 0 + (Q.a01 * Q.a02 - Q.a12 * Q.a00) * u 1 +
          (Q.a00 * Q.a11 - Q.a01 ^ 2) * u 2) = Q.det * u 1
    unfold det; ring
  · change Q.a02 * ((Q.a11 * Q.a22 - Q.a12 ^ 2) * u 0 + (Q.a02 * Q.a12 - Q.a01 * Q.a22) * u 1 +
          (Q.a01 * Q.a12 - Q.a02 * Q.a11) * u 2) +
        Q.a12 * ((Q.a02 * Q.a12 - Q.a01 * Q.a22) * u 0 + (Q.a00 * Q.a22 - Q.a02 ^ 2) * u 1 +
          (Q.a01 * Q.a02 - Q.a12 * Q.a00) * u 2) +
        Q.a22 * ((Q.a01 * Q.a12 - Q.a02 * Q.a11) * u 0 + (Q.a01 * Q.a02 - Q.a12 * Q.a00) * u 1 +
          (Q.a00 * Q.a11 - Q.a01 ^ 2) * u 2) = Q.det * u 2
    unfold det; ring

lemma adj_det (Q : SymQuad K) : Q.adj.det = Q.det ^ 2 := by
  unfold adj det; ring

lemma evalQ_adj_mulVec (Q : SymQuad K) (u : Fin 3 → K) :
    Q.adj.evalQ (Q.mulVec u) = Q.det * Q.evalQ u := by
  unfold adj evalQ bilin mulVec det; dsimp only; ring

lemma evalQ_mulVec_adj (Q : SymQuad K) (u : Fin 3 → K) :
    Q.evalQ (Q.adj.mulVec u) = Q.det * Q.adj.evalQ u := by
  unfold adj evalQ bilin mulVec det; dsimp only; ring

lemma eval_toPoly (Q : SymQuad K) (u : Fin 3 → K) :
    eval u Q.toPoly = Q.evalQ u := by
  unfold toPoly evalQ bilin
  simp only [map_add, map_mul, map_pow, eval_C, eval_X]
  ring

lemma eval_toAffPoly {F : Type*} [Field F] (Q : SymQuad F) (a : Fin 2 → F) :
    eval a Q.toAffPoly = Q.evalQ (embed a) := by
  unfold toAffPoly evalQ bilin embed
  simp only [map_add, map_mul, map_pow, eval_C, eval_X]
  ring

lemma totalDegree_toAffPoly_le {F : Type*} [Field F] (Q : SymQuad F) : Q.toAffPoly.totalDegree ≤ 2 := by
  unfold toAffPoly
  have hle : ∀ p q : MvPolynomial (Fin 2) F, p.totalDegree ≤ 2 → q.totalDegree ≤ 2 →
      (p + q).totalDegree ≤ 2 := fun p q hp hq => (MvPolynomial.totalDegree_add p q).trans (max_le hp hq)
  have hC : ∀ c : F, (C c : MvPolynomial (Fin 2) F).totalDegree ≤ 2 := fun c => by
    rw [MvPolynomial.totalDegree_C]; omega
  have hX : ∀ i : Fin 2, (X i : MvPolynomial (Fin 2) F).totalDegree = 1 := fun i =>
    MvPolynomial.totalDegree_X i
  have hCX : ∀ (c : F) (i : Fin 2), (C c * X i : MvPolynomial (Fin 2) F).totalDegree ≤ 2 := fun c i =>
    (MvPolynomial.totalDegree_mul _ _).trans (by rw [MvPolynomial.totalDegree_C, hX i]; omega)
  have hCX2 : ∀ (c : F) (i : Fin 2), (C c * X i ^ 2 : MvPolynomial (Fin 2) F).totalDegree ≤ 2 := fun c i =>
    (MvPolynomial.totalDegree_mul _ _).trans (by
      rw [MvPolynomial.totalDegree_C]
      have h1 := MvPolynomial.totalDegree_pow (X i : MvPolynomial (Fin 2) F) 2
      rw [hX i] at h1; omega)
  have hCXY : ∀ c : F, (C c * X (0 : Fin 2) * X 1 : MvPolynomial (Fin 2) F).totalDegree ≤ 2 := fun c =>
    (MvPolynomial.totalDegree_mul _ _).trans (by
      have h1 := MvPolynomial.totalDegree_mul (C c) (X (0 : Fin 2))
      rw [MvPolynomial.totalDegree_C, hX 0] at h1
      rw [hX 1]; omega)
  exact hle _ _ (hle _ _ (hle _ _ (hle _ _ (hle _ _ (hC _) (hCX _ 0)) (hCX _ 1)) (hCX2 _ 0)) (hCXY _)) (hCX2 _ 1)

lemma toAffPoly_ne_zero_of_det_ne_zero {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (Q : SymQuad F) (hdet : Q.det ≠ 0) : Q.toAffPoly ≠ 0 := by
  intro h0
  have hev : ∀ x y : F, Q.a00 + 2 * Q.a01 * x + 2 * Q.a02 * y +
      Q.a11 * x ^ 2 + 2 * Q.a12 * x * y + Q.a22 * y ^ 2 = 0 := by
    intro x y
    have h := congrArg (eval (fun i : Fin 2 => match i with | 0 => x | 1 => y)) h0
    rw [map_zero] at h
    unfold toAffPoly at h
    simp only [map_add, map_mul, map_pow, eval_C, eval_X] at h
    exact h
  have c00 : Q.a00 = 0 := by have := hev 0 0; linear_combination this
  have h10 := hev 1 0
  have hm10 := hev (-1) 0
  have c11 : Q.a11 = 0 := by
    have : 2 * Q.a11 = 0 := by linear_combination h10 + hm10 - 2 * c00
    exact (mul_eq_zero.mp this).resolve_left h2
  have c01 : Q.a01 = 0 := by
    have : 2 * Q.a01 = 0 := by linear_combination h10 - c00 - c11
    exact (mul_eq_zero.mp this).resolve_left h2
  have h01 := hev 0 1
  have hm01 := hev 0 (-1)
  have c22 : Q.a22 = 0 := by
    have : 2 * Q.a22 = 0 := by linear_combination h01 + hm01 - 2 * c00
    exact (mul_eq_zero.mp this).resolve_left h2
  have c02 : Q.a02 = 0 := by
    have : 2 * Q.a02 = 0 := by linear_combination h01 - c00 - c22
    exact (mul_eq_zero.mp this).resolve_left h2
  have h11 := hev 1 1
  have c12 : Q.a12 = 0 := by
    have : 2 * Q.a12 = 0 := by linear_combination h11 - c00 - 2 * c01 - 2 * c02 - c11 - c22
    exact (mul_eq_zero.mp this).resolve_left h2
  apply hdet; unfold det; rw [c00, c11, c22, c01, c02, c12]; ring

lemma homog2_eq_toPoly {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    {P : MvPolynomial (Fin 3) F} (hP : P.IsHomogeneous 2) :
    ∃ Q : SymQuad F, P = Q.toPoly := by
  let Q : SymQuad F := {
    a00 := P.coeff (Finsupp.single 0 2)
    a11 := P.coeff (Finsupp.single 1 2)
    a22 := P.coeff (Finsupp.single 2 2)
    a01 := 2⁻¹ * P.coeff (Finsupp.single 0 1 + Finsupp.single 1 1)
    a02 := 2⁻¹ * P.coeff (Finsupp.single 0 1 + Finsupp.single 2 1)
    a12 := 2⁻¹ * P.coeff (Finsupp.single 1 1 + Finsupp.single 2 1)
  }
  refine ⟨Q, ?_⟩
  have hmul2 : ∀ c : F, 2 * (2⁻¹ * c) = c := fun c => by rw [← mul_assoc, mul_inv_cancel₀ h2, one_mul]
  have htoPoly_mon : Q.toPoly =
      monomial (Finsupp.single 0 2) Q.a00 +
      monomial (Finsupp.single 1 2) Q.a11 +
      monomial (Finsupp.single 2 2) Q.a22 +
      monomial (Finsupp.single 0 1 + Finsupp.single 1 1) (2 * Q.a01) +
      monomial (Finsupp.single 0 1 + Finsupp.single 2 1) (2 * Q.a02) +
      monomial (Finsupp.single 1 1 + Finsupp.single 2 1) (2 * Q.a12) := by
    unfold toPoly
    have hx2 : ∀ (c : F) (i : Fin 3), C c * (X i : MvPolynomial (Fin 3) F) ^ 2 =
        monomial (Finsupp.single i 2) c := fun c i => by
      rw [sq, MvPolynomial.X, MvPolynomial.C_apply, MvPolynomial.monomial_mul,
        MvPolynomial.monomial_mul, zero_add, mul_one, mul_one, ← Finsupp.single_add]
    have hxy : ∀ (c : F) (i j : Fin 3), C c * (X i : MvPolynomial (Fin 3) F) * X j =
        monomial (Finsupp.single i 1 + Finsupp.single j 1) c := fun c i j => by
      rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.C_apply, MvPolynomial.monomial_mul,
        MvPolynomial.monomial_mul, zero_add, mul_one, mul_one]
    rw [hx2, hx2, hx2, hxy, hxy, hxy]
  rw [htoPoly_mon]
  ext m
  by_cases hm : m ∈ P.support
  · have hdeg : m 0 + m 1 + m 2 = 2 := by
      have h := isHomogeneous_sum_eq hP hm
      rwa [Fin.sum_univ_three] at h
    have hcases : m = Finsupp.single 0 2 ∨ m = Finsupp.single 1 2 ∨ m = Finsupp.single 2 2 ∨
        m = Finsupp.single 0 1 + Finsupp.single 1 1 ∨
        m = Finsupp.single 0 1 + Finsupp.single 2 1 ∨
        m = Finsupp.single 1 1 + Finsupp.single 2 1 := by
      by_cases h0 : m 0 = 2
      · left; ext i; fin_cases i <;> simp <;> omega
      · by_cases h1 : m 1 = 2
        · right; left; ext i; fin_cases i <;> simp <;> omega
        · by_cases h2' : m 2 = 2
          · right; right; left; ext i; fin_cases i <;> simp <;> omega
          · by_cases h01 : m 0 = 1 ∧ m 1 = 1
            · right; right; right; left; ext i; fin_cases i <;> simp <;> omega
            · by_cases h02 : m 0 = 1 ∧ m 2 = 1
              · right; right; right; right; left; ext i; fin_cases i <;> simp <;> omega
              · right; right; right; right; right; ext i; fin_cases i <;> simp <;> omega
    have h3 : ∀ a b : Fin 3 →₀ ℕ, a = b ↔ a 0 = b 0 ∧ a 1 = b 1 ∧ a 2 = b 2 := by
      intro a b; constructor
      · intro h; subst h; exact ⟨rfl, rfl, rfl⟩
      · rintro ⟨h0, h1, h2⟩; ext i; fin_cases i <;> assumption
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [MvPolynomial.coeff_monomial, Q, hmul2, h3]
  · have h0 : P.coeff m = 0 := MvPolynomial.notMem_support_iff.mp hm
    rw [h0]
    simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_monomial, Q, hmul2]
    have hc : ∀ s : Fin 3 →₀ ℕ, (if s = m then P.coeff s else 0) = 0 := by
      intro s; split_ifs with hs; rw [hs, h0]; rfl
    rw [hc, hc, hc, hc, hc, hc]; ring

lemma not_irreducible_toPoly_of_a00_ne_zero_det_zero {F : Type*} [Field F] [IsAlgClosed F]
    (_h2 : (2 : F) ≠ 0) (Q : SymQuad F) (ha00 : Q.a00 ≠ 0) (hdet : Q.det = 0) :
    ¬ Irreducible Q.toPoly := by
  intro hirr
  let L : MvPolynomial (Fin 3) F := C Q.a00 * X 0 + C Q.a01 * X 1 + C Q.a02 * X 2
  have hLh : L.IsHomogeneous 1 :=
    (((isHomogeneous_X F (0 : Fin 3)).C_mul _).add ((isHomogeneous_X F 1).C_mul _)).add
      ((isHomogeneous_X F 2).C_mul _)
  let b22 := Q.a00 * Q.a11 - Q.a01 ^ 2
  let b11 := Q.a00 * Q.a22 - Q.a02 ^ 2
  let b12 := Q.a01 * Q.a02 - Q.a12 * Q.a00
  have hcompl : C Q.a00 * Q.toPoly =
      L ^ 2 + C b22 * X 1 ^ 2 - C (2 * b12) * X 1 * X 2 + C b11 * X 2 ^ 2 := by
    unfold toPoly L; dsimp only [b22, b11, b12]
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    ring
  have hdisc0 : b22 * b11 - b12 ^ 2 = 0 := by
    have : b22 * b11 - b12 ^ 2 = Q.a00 * Q.det := by dsimp only [b22, b11, b12]; unfold det; ring
    rw [this, hdet, mul_zero]
  have hex_lin : ∃ M : MvPolynomial (Fin 3) F, M.IsHomogeneous 1 ∧
      C Q.a00 * Q.toPoly = (L - M) * (L + M) := by
    by_cases hb22 : b22 ≠ 0
    · let poly : Polynomial F := Polynomial.X ^ 2 + Polynomial.C (b22⁻¹)
      have hdeg : poly.degree ≠ 0 := by
        have hnd : poly.natDegree = 2 := by
          dsimp only [poly]; rw [Polynomial.natDegree_add_C, Polynomial.natDegree_X_pow]
        rw [Polynomial.degree_eq_natDegree (by intro h; rw [h, Polynomial.natDegree_zero] at hnd; omega), hnd]
        decide
      obtain ⟨r, hr⟩ := IsAlgClosed.exists_root poly hdeg
      have hr2 : r ^ 2 = -b22⁻¹ := by
        rw [Polynomial.IsRoot.def] at hr
        dsimp only [poly] at hr
        simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hr
        linear_combination hr
      let M : MvPolynomial (Fin 3) F := C (r * b22) * X 1 - C (r * b12) * X 2
      have hMh : M.IsHomogeneous 1 :=
        ((isHomogeneous_X F (1 : Fin 3)).C_mul _).sub ((isHomogeneous_X F 2).C_mul _)
      refine ⟨M, hMh, ?_⟩
      rw [hcompl]
      have h1 : r ^ 2 * b22 ^ 2 = -b22 := by
        rw [hr2]; calc -b22⁻¹ * b22 ^ 2 = -(b22⁻¹ * b22) * b22 := by ring
          _ = -b22 := by rw [inv_mul_cancel₀ hb22]; ring
      have h2' : r ^ 2 * b22 * b12 = -b12 := by
        rw [hr2]; calc -b22⁻¹ * b22 * b12 = -(b22⁻¹ * b22) * b12 := by ring
          _ = -b12 := by rw [inv_mul_cancel₀ hb22]; ring
      have h3 : r ^ 2 * b12 ^ 2 = -b11 := by
        have hb12sq : b12 ^ 2 = b22 * b11 := by linear_combination -hdisc0
        rw [hr2, hb12sq]
        calc -b22⁻¹ * (b22 * b11) = -(b22⁻¹ * b22) * b11 := by ring
          _ = -b11 := by rw [inv_mul_cancel₀ hb22]; ring
      have hM2 : M ^ 2 = -(C b22 * X 1 ^ 2 - C (2 * b12) * X 1 * X 2 + C b11 * X 2 ^ 2) := by
        dsimp only [M]
        calc (C (r * b22) * X (1 : Fin 3) - C (r * b12) * X 2) ^ 2
            = C (r ^ 2 * b22 ^ 2) * X (1 : Fin 3) ^ 2 - C (2 * (r ^ 2 * b22 * b12)) * X 1 * X 2 +
                C (r ^ 2 * b12 ^ 2) * X 2 ^ 2 := by
                  simp only [map_mul, map_pow, map_ofNat]; ring
          _ = C (-b22) * X (1 : Fin 3) ^ 2 - C (2 * (-b12)) * X 1 * X 2 + C (-b11) * X 2 ^ 2 := by
                rw [h1, h2', h3]
          _ = _ := by simp only [map_neg, map_mul, map_ofNat]; ring
      calc L ^ 2 + C b22 * X 1 ^ 2 - C (2 * b12) * X 1 * X 2 + C b11 * X 2 ^ 2
          = L ^ 2 - M ^ 2 := by rw [hM2]; ring
        _ = (L - M) * (L + M) := by ring
    · have hb22' : b22 = 0 := not_not.mp hb22
      have hb12' : b12 = 0 := by
        rw [hb22', zero_mul, zero_sub, neg_eq_zero] at hdisc0
        exact eq_zero_of_pow_eq_zero hdisc0
      let poly : Polynomial F := Polynomial.X ^ 2 + Polynomial.C b11
      have hdeg : poly.degree ≠ 0 := by
        have hnd : poly.natDegree = 2 := by
          dsimp only [poly]; rw [Polynomial.natDegree_add_C, Polynomial.natDegree_X_pow]
        rw [Polynomial.degree_eq_natDegree (by intro h; rw [h, Polynomial.natDegree_zero] at hnd; omega), hnd]
        decide
      obtain ⟨r, hr⟩ := IsAlgClosed.exists_root poly hdeg
      have hr2 : r ^ 2 = -b11 := by
        rw [Polynomial.IsRoot.def] at hr
        dsimp only [poly] at hr
        simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hr
        linear_combination hr
      let M : MvPolynomial (Fin 3) F := C r * X 2
      refine ⟨M, (isHomogeneous_X F (2 : Fin 3)).C_mul r, ?_⟩
      rw [hcompl, hb22', hb12']
      simp only [mul_zero, map_zero, zero_mul, add_zero, sub_zero]
      dsimp only [M]
      have hM2 : (C r * X 2 : MvPolynomial (Fin 3) F) ^ 2 = -(C b11 * X 2 ^ 2) := by
        calc (C r * X 2 : MvPolynomial (Fin 3) F) ^ 2
            = C (r ^ 2) * X 2 ^ 2 := by rw [mul_pow, map_pow]
          _ = C (-b11) * X 2 ^ 2 := by rw [hr2]
          _ = -(C b11 * X 2 ^ 2) := by rw [map_neg, neg_mul]
      calc L ^ 2 + C b11 * X 2 ^ 2 = L ^ 2 - (C r * X 2) ^ 2 := by rw [hM2]; ring
        _ = (L - C r * X 2) * (L + C r * X 2) := by ring
  obtain ⟨M, hMh, hfac⟩ := hex_lin
  have hPfac : Q.toPoly = (C Q.a00⁻¹ * (L - M)) * (L + M) := by
    apply mul_left_cancel₀ (show (C Q.a00 : MvPolynomial (Fin 3) F) ≠ 0 by simpa using ha00)
    rw [hfac]
    have hinv : C Q.a00 * C Q.a00⁻¹ = (1 : MvPolynomial (Fin 3) F) := by
      rw [← map_mul, mul_inv_cancel₀ ha00, map_one]
    calc (L - M) * (L + M) = (C Q.a00 * C Q.a00⁻¹) * ((L - M) * (L + M)) := by rw [hinv, one_mul]
      _ = _ := by ring
  have hnotu : ∀ R : MvPolynomial (Fin 3) F, R.IsHomogeneous 1 → ¬ IsUnit R := by
    intro R hRh hu
    obtain ⟨G, hG⟩ := hu.exists_right_inv
    have hR0 : R ≠ 0 := by intro h; rw [h, zero_mul] at hG; exact zero_ne_one hG
    obtain ⟨_, _, hsum⟩ := isHomogeneous_of_dvd (isHomogeneous_one (Fin 3) F) one_ne_zero hG
    have hRd : R.totalDegree = 1 := hRh.totalDegree hR0
    omega
  rcases hirr.isUnit_or_isUnit hPfac with h1 | h2'
  · exact hnotu _ ((hLh.sub hMh).C_mul _) h1
  · exact hnotu _ (hLh.add hMh) h2'

lemma det_ne_zero_of_irreducible_map {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (Q : SymQuad (ZMod p))
    (hirr : Irreducible (MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) Q.toPoly)) :
    Q.det ≠ 0 := by
  set Kbar := AlgebraicClosure (ZMod p)
  set ι : ZMod p →+* Kbar := algebraMap (ZMod p) Kbar
  have h2K : (2 : Kbar) ≠ 0 := by
    intro h; exact two_ne_zero_of_prime_ne_two hp2 (ι.injective (by rw [map_ofNat, map_zero]; exact h))
  rw [map_toPoly] at hirr
  set Qbar := Q.map ι
  intro hdet
  have hdet_bar : Qbar.det = 0 := by rw [map_det, hdet, map_zero]
  have hirr_ren : ∀ (σ : Fin 3 ≃ Fin 3) (P : MvPolynomial (Fin 3) Kbar),
      Irreducible P → Irreducible (MvPolynomial.rename σ P) := by
    intro σ P hP
    let e := (MvPolynomial.renameEquiv Kbar σ).toRingEquiv
    have hnotu : ¬ IsUnit (e P) := fun hu => hP.not_isUnit (by
      have := hu.map e.symm.toRingHom; simpa using this)
    refine ⟨hnotu, ?_⟩
    intro A B hAB
    have hback : P = e.symm A * e.symm B := by
      have := congrArg e.symm hAB; simpa [e, map_mul] using this
    rcases hP.isUnit_or_isUnit hback with hA | hB
    · left; have := hA.map e.toRingHom; simpa using this
    · right; have := hB.map e.toRingHom; simpa using this
  by_cases ha00 : Qbar.a00 ≠ 0
  · exact not_irreducible_toPoly_of_a00_ne_zero_det_zero h2K Qbar ha00 hdet_bar hirr
  by_cases ha11 : Qbar.a11 ≠ 0
  · let Q1 : SymQuad Kbar := ⟨Qbar.a11, Qbar.a00, Qbar.a22, Qbar.a01, Qbar.a12, Qbar.a02⟩
    have hdet1 : Q1.det = 0 := by
      rw [← hdet_bar]; dsimp only [Q1]; unfold det; ring
    have hren : MvPolynomial.rename (Equiv.swap (0 : Fin 3) 1) Qbar.toPoly = Q1.toPoly := by
      dsimp only [Q1]; unfold toPoly
      simp [Equiv.swap_apply_def]; ring
    have hirr1 : Irreducible Q1.toPoly := hren ▸ hirr_ren (Equiv.swap 0 1) _ hirr
    exact not_irreducible_toPoly_of_a00_ne_zero_det_zero h2K Q1 ha11 hdet1 hirr1
  by_cases ha22 : Qbar.a22 ≠ 0
  · let Q2 : SymQuad Kbar := ⟨Qbar.a22, Qbar.a11, Qbar.a00, Qbar.a12, Qbar.a02, Qbar.a01⟩
    have hdet2 : Q2.det = 0 := by
      rw [← hdet_bar]; dsimp only [Q2]; unfold det; ring
    have hren : MvPolynomial.rename (Equiv.swap (0 : Fin 3) 2) Qbar.toPoly = Q2.toPoly := by
      dsimp only [Q2]; unfold toPoly
      simp [Equiv.swap_apply_def]; ring
    have hirr2 : Irreducible Q2.toPoly := hren ▸ hirr_ren (Equiv.swap 0 2) _ hirr
    exact not_irreducible_toPoly_of_a00_ne_zero_det_zero h2K Q2 ha22 hdet2 hirr2
  have h00 : Qbar.a00 = 0 := not_not.mp ha00
  have h11 : Qbar.a11 = 0 := not_not.mp ha11
  have h22 : Qbar.a22 = 0 := not_not.mp ha22
  unfold det at hdet_bar
  rw [h00, h11, h22] at hdet_bar
  have hprod0 : 2 * Qbar.a01 * Qbar.a02 * Qbar.a12 = 0 := by linear_combination hdet_bar
  have hnotu : ∀ R : MvPolynomial (Fin 3) Kbar, R.IsHomogeneous 1 → ¬ IsUnit R := by
    intro R hRh hu
    obtain ⟨G, hG⟩ := hu.exists_right_inv
    have hR0 : R ≠ 0 := by intro h; rw [h, zero_mul] at hG; exact zero_ne_one hG
    obtain ⟨_, _, hsum⟩ := isHomogeneous_of_dvd (isHomogeneous_one (Fin 3) Kbar) one_ne_zero hG
    have hRd : R.totalDegree = 1 := hRh.totalDegree hR0
    omega
  have hfac_zero : ∀ (i : Fin 3) (R : MvPolynomial (Fin 3) Kbar), R.IsHomogeneous 1 →
      Qbar.toPoly = X i * R → False := by
    intro i R hRh heq
    rcases hirr.isUnit_or_isUnit heq with h1 | h2'
    · exact hnotu _ (isHomogeneous_X Kbar i) h1
    · exact hnotu _ hRh h2'
  rcases mul_eq_zero.mp hprod0 with h12 | ha12
  · rcases mul_eq_zero.mp h12 with h01 | ha02
    · have ha01 : Qbar.a01 = 0 := (mul_eq_zero.mp h01).resolve_left h2K
      exact hfac_zero 2 (C (2 * Qbar.a02) * X 0 + C (2 * Qbar.a12) * X 1)
        (((isHomogeneous_X Kbar 0).C_mul _).add ((isHomogeneous_X Kbar 1).C_mul _))
        (by unfold toPoly; rw [h00, h11, h22, ha01]; simp only [mul_zero, map_zero, zero_mul, add_zero, zero_add]; ring)
    · exact hfac_zero 1 (C (2 * Qbar.a01) * X 0 + C (2 * Qbar.a12) * X 2)
        (((isHomogeneous_X Kbar 0).C_mul _).add ((isHomogeneous_X Kbar 2).C_mul _))
        (by unfold toPoly; rw [h00, h11, h22, ha02]; simp only [mul_zero, map_zero, zero_mul, add_zero, zero_add]; ring)
  · exact hfac_zero 0 (C (2 * Qbar.a01) * X 1 + C (2 * Qbar.a02) * X 2)
      (((isHomogeneous_X Kbar 1).C_mul _).add ((isHomogeneous_X Kbar 2).C_mul _))
      (by unfold toPoly; rw [h00, h11, h22, ha12]; simp only [mul_zero, map_zero, zero_mul, add_zero, zero_add]; ring)

lemma card_zeros_le_add_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (Q : SymQuad (ZMod p)) (hdet : Q.det ≠ 0) :
    ((univ : Finset (Fin 3 → ZMod p)).filter fun u => IsNorm u ∧ Q.evalQ u = 0).card ≤ p + 1 := by
  classical
  set Z := (univ : Finset (Fin 3 → ZMod p)).filter fun u => IsNorm u ∧ Q.evalQ u = 0
  by_cases hZ : Z.Nonempty
  · obtain ⟨u₀, hu₀⟩ := hZ
    have hu₀n : IsNorm u₀ := (mem_filter.mp hu₀).2.1
    have hu₀q : Q.evalQ u₀ = 0 := (mem_filter.mp hu₀).2.2
    have hu₀ne : u₀ ≠ 0 := isNorm_ne_zero hu₀n
    have hmul_ne : ∀ v : Fin 3 → ZMod p, v ≠ 0 → Q.mulVec v ≠ 0 := by
      intro v hv h0
      have h1 := Q.adj_mulVec_mulVec v
      rw [h0] at h1
      have h00 : Q.adj.mulVec 0 = 0 := by ext i; fin_cases i <;> simp [mulVec]
      rw [h00] at h1
      exact hv ((smul_eq_zero.mp h1.symm).resolve_left hdet)
    have hbilin_ne : ∀ u ∈ Z.erase u₀, Q.bilin u₀ u ≠ 0 := by
      intro u hu h0
      have hune : u ≠ u₀ := (mem_erase.mp hu).1
      have hun : IsNorm u := (mem_filter.mp (mem_erase.mp hu).2).2.1
      have huq : Q.evalQ u = 0 := (mem_filter.mp (mem_erase.mp hu).2).2.2
      have hcr : cross3 u₀ u ≠ 0 := by
        intro hcr0
        obtain ⟨c, hc⟩ := (cross3_eq_zero_iff hu₀ne).mp hcr0
        exact hune (isNorm_eq_of_smul hun hu₀n hc)
      have hm0_cr : cross3 (cross3 u₀ u) (Q.mulVec u₀) = 0 :=
        cross3_cross3_eq_zero_of_dot3
          (by rw [dot3_comm, ← Q.bilin_eq_dot3]; exact hu₀q)
          (by rw [dot3_comm, ← Q.bilin_eq_dot3, Q.bilin_symm]; exact h0)
      have hm1_cr : cross3 (cross3 u₀ u) (Q.mulVec u) = 0 :=
        cross3_cross3_eq_zero_of_dot3
          (by rw [dot3_comm, ← Q.bilin_eq_dot3]; exact h0)
          (by rw [dot3_comm, ← Q.bilin_eq_dot3]; exact huq)
      obtain ⟨c₀, hc₀⟩ := (cross3_eq_zero_iff hcr).mp hm0_cr
      obtain ⟨c₁, hc₁⟩ := (cross3_eq_zero_iff hcr).mp hm1_cr
      have hc₀_ne : c₀ ≠ 0 := by intro h; rw [h, zero_smul] at hc₀; exact hmul_ne u₀ hu₀ne hc₀
      have hprop : Q.mulVec u = (c₁ / c₀) • Q.mulVec u₀ := by
        rw [hc₁, hc₀, smul_smul, div_mul_cancel₀ _ hc₀_ne]
      have hadj := congrArg Q.adj.mulVec hprop
      rw [Q.adj_mulVec_mulVec, Q.adj.mulVec_smul, Q.adj_mulVec_mulVec, smul_smul,
        mul_comm (c₁ / c₀), ← smul_smul] at hadj
      have hu_eq : u = (c₁ / c₀) • u₀ := by
        ext i; exact mul_left_cancel₀ hdet (congrFun hadj i)
      exact hune (isNorm_eq_of_smul hun hu₀n hu_eq)
    let φ : (Fin 3 → ZMod p) → Fin 3 → ZMod p := fun u => norm3 (cross3 u₀ u)
    have hφ_sub : (Z.erase u₀).image φ ⊆ (lineThrough u₀).erase (norm3 (Q.mulVec u₀)) := by
      intro w hw
      rcases mem_image.mp hw with ⟨u, hu, rfl⟩
      have hune : u ≠ u₀ := (mem_erase.mp hu).1
      have hun : IsNorm u := (mem_filter.mp (mem_erase.mp hu).2).2.1
      have hcr : cross3 u₀ u ≠ 0 := by
        intro hcr0
        obtain ⟨c, hc⟩ := (cross3_eq_zero_iff hu₀ne).mp hcr0
        exact hune (isNorm_eq_of_smul hun hu₀n hc)
      refine mem_erase.mpr ⟨?_, ?_⟩
      · intro heq
        obtain ⟨c, hc0, hc⟩ := (norm3_eq_iff_prop hcr (hmul_ne u₀ hu₀ne)).mp heq
        have hdot : dot3 (Q.mulVec u₀) u = 0 := by
          have := dot3_cross3_right u₀ u
          rw [hc, dot3_smul_left] at this
          exact (mul_eq_zero.mp this).resolve_left hc0
        apply hbilin_ne u hu
        rw [Q.bilin_symm, Q.bilin_eq_dot3, dot3_comm]
        exact hdot
      · rw [mem_lineThrough]
        obtain ⟨c, _, hc⟩ := norm3_exists_smul hcr
        refine ⟨norm3_isNorm hcr, ?_⟩
        change dot3 (norm3 (cross3 u₀ u)) u₀ = 0
        rw [hc, dot3_smul_left, dot3_cross3_left, mul_zero]
    have hφ_inj : Set.InjOn φ (Z.erase u₀) := by
      intro u₁ hu₁ u₂ hu₂ heq
      by_contra h12
      have h1ne : u₁ ≠ u₀ := (mem_erase.mp hu₁).1
      have h2ne : u₂ ≠ u₀ := (mem_erase.mp hu₂).1
      have hn1 : IsNorm u₁ := (mem_filter.mp (mem_erase.mp hu₁).2).2.1
      have hn2 : IsNorm u₂ := (mem_filter.mp (mem_erase.mp hu₂).2).2.1
      have hq1 : Q.evalQ u₁ = 0 := (mem_filter.mp (mem_erase.mp hu₁).2).2.2
      have hq2 : Q.evalQ u₂ = 0 := (mem_filter.mp (mem_erase.mp hu₂).2).2.2
      have hcr1 : cross3 u₀ u₁ ≠ 0 := by
        intro h0; obtain ⟨c, hc⟩ := (cross3_eq_zero_iff hu₀ne).mp h0
        exact h1ne (isNorm_eq_of_smul hn1 hu₀n hc)
      have hcr2 : cross3 u₀ u₂ ≠ 0 := by
        intro h0; obtain ⟨c, hc⟩ := (cross3_eq_zero_iff hu₀ne).mp h0
        exact h2ne (isNorm_eq_of_smul hn2 hu₀n hc)
      obtain ⟨c, hc0, hc⟩ := (norm3_eq_iff_prop hcr1 hcr2).mp heq
      -- cross3 u₀ u₁ = c • cross3 u₀ u₂ -> cross3 u₀ (u₁ - c • u₂) = 0 -> u₁ - c • u₂ = s • u₀
      have hcr_diff : cross3 u₀ (u₁ - c • u₂) = 0 := by
        ext i; fin_cases i
        · change u₀ 1 * (u₁ 2 - c * u₂ 2) - u₀ 2 * (u₁ 1 - c * u₂ 1) = 0
          have h0 : u₀ 1 * u₁ 2 - u₀ 2 * u₁ 1 = c * (u₀ 1 * u₂ 2 - u₀ 2 * u₂ 1) := congrFun hc 0
          linear_combination h0
        · change u₀ 2 * (u₁ 0 - c * u₂ 0) - u₀ 0 * (u₁ 2 - c * u₂ 2) = 0
          have h1 : u₀ 2 * u₁ 0 - u₀ 0 * u₁ 2 = c * (u₀ 2 * u₂ 0 - u₀ 0 * u₂ 2) := congrFun hc 1
          linear_combination h1
        · change u₀ 0 * (u₁ 1 - c * u₂ 1) - u₀ 1 * (u₁ 0 - c * u₂ 0) = 0
          have h2 : u₀ 0 * u₁ 1 - u₀ 1 * u₁ 0 = c * (u₀ 0 * u₂ 1 - u₀ 1 * u₂ 0) := congrFun hc 2
          linear_combination h2
      obtain ⟨s, hs⟩ := (cross3_eq_zero_iff hu₀ne).mp hcr_diff
      have hu1_eq : u₁ = s • u₀ + c • u₂ := by
        ext i; have := congrFun hs i; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢; linear_combination this
      have hev1 : Q.evalQ u₁ = 0 := hq1
      rw [hu1_eq, Q.evalQ_add_smul, hu₀q, hq2, mul_zero, mul_zero, zero_add, add_zero] at hev1
      have hs0 : s = 0 := by
        have h1 := (mul_eq_zero.mp hev1).resolve_right (hbilin_ne u₂ hu₂)
        have h2 := (mul_eq_zero.mp h1).resolve_right hc0
        exact (mul_eq_zero.mp h2).resolve_left (two_ne_zero_of_prime_ne_two hp2)
      rw [hs0, zero_smul, zero_add] at hu1_eq
      exact h12 (isNorm_eq_of_smul hn1 hn2 hu1_eq)
    have htan_in : norm3 (Q.mulVec u₀) ∈ lineThrough u₀ := by
      rw [mem_lineThrough]
      obtain ⟨c, _, hc⟩ := norm3_exists_smul (hmul_ne u₀ hu₀ne)
      refine ⟨norm3_isNorm (hmul_ne u₀ hu₀ne), ?_⟩
      rw [hc, dot3_smul_left, dot3_comm, ← Q.bilin_eq_dot3]
      change c * Q.evalQ u₀ = 0
      rw [hu₀q, mul_zero]
    have hcard_le : (Z.erase u₀).card ≤ ((lineThrough u₀).erase (norm3 (Q.mulVec u₀))).card := by
      rw [← card_image_of_injOn hφ_inj]
      exact card_le_card hφ_sub
    rw [card_erase_of_mem hu₀, card_erase_of_mem htan_in, card_lineThrough_ne_zero hu₀ne] at hcard_le
    have hZpos : 1 ≤ Z.card := card_pos.mpr ⟨u₀, hu₀⟩
    omega
  · rw [not_nonempty_iff_eq_empty.mp hZ, card_empty]; omega

lemma restrictA_toPoly (Q : SymQuad (ZMod p)) (a : Fin 2 → ZMod p) :
    let A₂ := Q.a00 * a 0 ^ 2 - 2 * Q.a01 * a 0 + Q.a11
    let B₂ := Q.a00 * a 0 * a 1 - Q.a01 * a 1 - Q.a02 * a 0 + Q.a12
    let C₂ := Q.a00 * a 1 ^ 2 - 2 * Q.a02 * a 1 + Q.a22
    restrictA a Q.toPoly = C A₂ * X 0 ^ 2 + C (2 * B₂) * X 0 * X 1 + C C₂ * X 1 ^ 2 ∧
      A₂ * C₂ - B₂ ^ 2 = Q.adj.evalQ (embed a) := by
  refine ⟨?_, ?_⟩
  · unfold toPoly restrictA
    simp only [map_add, map_mul, map_pow, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
      map_sub, map_neg, map_ofNat]
    ring
  · unfold adj evalQ bilin embed; dsimp only; ring

end SymQuad

lemma two_le_card_tangents_zeros_of_adj_ne_zero {A E : Finset (Fin 2 → ZMod p)} (hp2 : p ≠ 2)
    (harc : ∀ s ⊆ A, s.card = 3 → ¬ Collinear (ZMod p) (s : Set (Fin 2 → ZMod p)))
    {e : Fin 2 → ZMod p} (he : e ∈ A) (hEA : E ⊆ A) (hE : E.card = 2 * (p + 2 - A.card) + 2)
    (Q : SymQuad (ZMod p)) (hdvd : Q.toPoly ∣ segreEnv A E e)
    {a : Fin 2 → ZMod p} (ha : a ∈ A) (hadj : Q.adj.evalQ (embed a) ≠ 0) :
    2 ≤ ((tangents A a).filter fun u => eval u Q.toPoly = 0).card := by
  classical
  have hQhom : Q.toPoly.IsHomogeneous 2 := by
    unfold SymQuad.toPoly
    have hX2 : ∀ (c : ZMod p) (i : Fin 3), (C c * (X i : MvPolynomial (Fin 3) (ZMod p)) ^ 2).IsHomogeneous 2 :=
      fun c i => (by simpa using (isHomogeneous_X (ZMod p) i).pow 2 : ((X i : MvPolynomial (Fin 3) (ZMod p)) ^ 2).IsHomogeneous 2).C_mul c
    have hXY : ∀ (c : ZMod p) (i j : Fin 3), (C c * (X i : MvPolynomial (Fin 3) (ZMod p)) * X j).IsHomogeneous 2 :=
      fun c i j => by
        rw [mul_assoc]
        exact ((isHomogeneous_X (ZMod p) i).mul (isHomogeneous_X (ZMod p) j)).C_mul c
    exact (((((hX2 _ 0).add (hX2 _ 1)).add (hX2 _ 2)).add (hXY _ 0 1)).add (hXY _ 0 2)).add (hXY _ 1 2)
  have hge1 : 1 ≤ ((tangents A a).filter fun u => eval u Q.toPoly = 0).card := by
    have h := deg_le_two_mul_card_tangents_zeros hp2 harc he hEA hE hQhom hdvd ha
    omega
  by_contra hlt2
  have hcard1 : ((tangents A a).filter fun u => eval u Q.toPoly = 0).card = 1 := by omega
  obtain ⟨u, hu_eq⟩ := Finset.card_eq_one.mp hcard1
  have hu_mem : u ∈ (tangents A a).filter fun v => eval v Q.toPoly = 0 := by rw [hu_eq]; exact mem_singleton_self u
  have hu_tan : u ∈ tangents A a := (mem_filter.mp hu_mem).1
  have hu_ev : eval u Q.toPoly = 0 := (mem_filter.mp hu_mem).2
  have hres_eq := Q.restrictA_toPoly a
  set A₂ := Q.a00 * a 0 ^ 2 - 2 * Q.a01 * a 0 + Q.a11
  set B₂ := Q.a00 * a 0 * a 1 - Q.a01 * a 1 - Q.a02 * a 0 + Q.a12
  set C₂ := Q.a00 * a 1 ^ 2 - 2 * Q.a02 * a 1 + Q.a22
  have hPa_eq : restrictA a Q.toPoly = C A₂ * X 0 ^ 2 + C (2 * B₂) * X 0 * X 1 + C C₂ * X 1 ^ 2 := hres_eq.1
  have hdisc : A₂ * C₂ - B₂ ^ 2 = Q.adj.evalQ (embed a) := hres_eq.2
  have hdehom : dehomog1 (restrictA a Q.toPoly) =
      Polynomial.C A₂ * Polynomial.X ^ 2 + Polynomial.C (2 * B₂) * Polynomial.X + Polynomial.C C₂ := by
    rw [hPa_eq]; simp [dehomog1]
  have hPa_ne : restrictA a Q.toPoly ≠ 0 := by
    intro h0; apply restrictA_segreEnv_ne_zero hp2 harc he hEA hE ha
    rcases hdvd with ⟨H, hH⟩; rw [hH, map_mul, h0, zero_mul]
  have hPa_hom : (restrictA a Q.toPoly).IsHomogeneous 2 := restrictA_isHomogeneous a hQhom
  have hq_ne : dehomog1 (restrictA a Q.toPoly) ≠ 0 := fun h => hPa_ne (eq_zero_of_dehomog1_eq_zero hPa_hom h)
  obtain ⟨β, hβ, hg1⟩ := dehomog1_two_mul_gPoly hp2 he ha
  have hq_dvd : dehomog1 (restrictA a Q.toPoly) ∣
      Polynomial.C β * ∏ r ∈ ((tangents A a).filter fun v => v 2 ≠ 0).image (fun v => v 1 / v 2),
        (Polynomial.X - Polynomial.C r) ^ 2 := by
    rw [← hg1, ← restrictA_segreEnv harc he hEA hE ha]
    rcases hdvd with ⟨H, hH⟩; exact ⟨dehomog1 (restrictA a H), by rw [hH, map_mul, map_mul]⟩
  have hA2_zero_imp : A₂ = 0 → u 2 = 0 := by
    intro hA2
    let w₀ : Fin 3 → ZMod p := fun i => match i with | 0 => -a 0 | 1 => 1 | 2 => 0
    have hw₀ : w₀ ≠ 0 := fun h => one_ne_zero (congrFun h 1)
    have hv_mem : norm3 w₀ ∈ lineThrough (embed a) := by
      rw [mem_lineThrough]
      obtain ⟨c, _, hc⟩ := norm3_exists_smul hw₀
      exact ⟨norm3_isNorm hw₀, by rw [hc, dot3_smul_left]; unfold dot3 w₀ embed; dsimp only; ring⟩
    have hv_ev : eval (norm3 w₀) Q.toPoly = 0 := by
      obtain ⟨c, _, hc⟩ := norm3_exists_smul hw₀
      rw [hc, isHomogeneous_eval_smul hQhom]
      have hdot : dot3 w₀ (embed a) = 0 := by unfold dot3 w₀ embed; dsimp only; ring
      rw [← eval_restrictA_of_dot3_zero a Q.toPoly hdot, hPa_eq]
      simp [w₀, hA2]
    have hv_tan : norm3 w₀ ∈ tangents A a :=
      mem_tangents_of_eval_dvd_segreEnv hp2 harc he hEA hE hdvd ha hv_mem hv_ev
    have hv_in : norm3 w₀ ∈ (tangents A a).filter fun v => eval v Q.toPoly = 0 :=
      mem_filter.mpr ⟨hv_tan, hv_ev⟩
    rw [hu_eq, mem_singleton] at hv_in
    obtain ⟨c, _, hc⟩ := norm3_exists_smul hw₀
    have h2 : u 2 = c * w₀ 2 := by rw [← hv_in, hc]; rfl
    simpa [w₀] using h2
  by_cases hu2 : u 2 = 0
  · -- Only zero is at u 2 = 0, so dehomog1 has NO roots in T2.image, hence natDegree = 0 -> A2 = B2 = 0
    have hno_root : (((tangents A a).filter fun v => v 2 ≠ 0).image (fun v => v 1 / v 2)).filter
        (fun r => (dehomog1 (restrictA a Q.toPoly)).IsRoot r) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro r hr
      rcases mem_image.mp (mem_filter.mp hr).1 with ⟨v, hv, rfl⟩
      have hv2 : v 2 ≠ 0 := (mem_filter.mp hv).2
      have hv_tan : v ∈ tangents A a := (mem_filter.mp hv).1
      have hrt : (dehomog1 (restrictA a Q.toPoly)).IsRoot (v 1 / v 2) := (mem_filter.mp hr).2
      rw [Polynomial.IsRoot.def, eval_dehomog1] at hrt
      have hsm : (fun i : Fin 2 => match i with | 0 => v 1 / v 2 | 1 => 1) =
          (v 2)⁻¹ • (fun i : Fin 2 => match i with | 0 => v 1 | 1 => v 2) := by
        ext i; fin_cases i
        · simp [div_eq_mul_inv, mul_comm]
        · simp [inv_mul_cancel₀ hv2]
      rw [hsm, isHomogeneous_eval_smul hPa_hom,
        eval_restrictA_of_dot3_zero a Q.toPoly (mem_tangents.mp hv_tan).2.1] at hrt
      have hv_ev : eval v Q.toPoly = 0 := (mul_eq_zero.mp hrt).resolve_left (pow_ne_zero 2 (inv_ne_zero hv2))
      have hv_in : v ∈ (tangents A a).filter fun w => eval w Q.toPoly = 0 := mem_filter.mpr ⟨hv_tan, hv_ev⟩
      rw [hu_eq, mem_singleton] at hv_in
      exact hv2 (hv_in ▸ hu2)
    have hnd0 : (dehomog1 (restrictA a Q.toPoly)).natDegree = 0 := by
      have hle := natDegree_le_two_mul_roots_of_dvd_prod_sq _ hβ hq_ne hq_dvd
      rw [hno_root, card_empty, mul_zero] at hle
      omega
    have hA2 : A₂ = 0 := by
      have hc := Polynomial.coeff_eq_zero_of_natDegree_lt (show (dehomog1 (restrictA a Q.toPoly)).natDegree < 2 by omega)
      rw [hdehom] at hc
      simpa [Polynomial.coeff_X_pow, Polynomial.coeff_C] using hc
    have hB2 : B₂ = 0 := by
      have hc := Polynomial.coeff_eq_zero_of_natDegree_lt (show (dehomog1 (restrictA a Q.toPoly)).natDegree < 1 by omega)
      rw [hdehom] at hc
      have h2B : 2 * B₂ = 0 := by simpa [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] using hc
      exact (mul_eq_zero.mp h2B).resolve_left (two_ne_zero_of_prime_ne_two hp2)
    apply hadj; rw [← hdisc, hA2, hB2]; ring
  · -- u 2 ≠ 0, so A₂ ≠ 0 and dehomog1 has degree 2 with unique root r = u 1 / u 2
    have hA2 : A₂ ≠ 0 := fun h => hu2 (hA2_zero_imp h)
    set r := u 1 / u 2
    have hsm : (fun i : Fin 2 => match i with | 0 => r | 1 => 1) =
        (u 2)⁻¹ • (fun i : Fin 2 => match i with | 0 => u 1 | 1 => u 2) := by
      ext i; fin_cases i
      · simp [r, div_eq_mul_inv, mul_comm]
      · simp [inv_mul_cancel₀ hu2]
    have hrt_u : (dehomog1 (restrictA a Q.toPoly)).IsRoot r := by
      rw [Polynomial.IsRoot.def, eval_dehomog1, hsm, isHomogeneous_eval_smul hPa_hom,
        eval_restrictA_of_dot3_zero a Q.toPoly (mem_tangents.mp hu_tan).2.1, hu_ev, mul_zero]
    have hnd2 : (dehomog1 (restrictA a Q.toPoly)).natDegree = 2 := by
      have hle := natDegree_dehomog1_le hPa_hom
      have hc2 : (dehomog1 (restrictA a Q.toPoly)).coeff 2 = A₂ := by
        rw [hdehom]; simp [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
      have hge2 : 2 ≤ (dehomog1 (restrictA a Q.toPoly)).natDegree :=
        Polynomial.le_natDegree_of_ne_zero (by rw [hc2]; exact hA2)
      omega
    obtain ⟨q₁, hq1⟩ := Polynomial.dvd_iff_isRoot.mpr hrt_u
    have hlin_ne : Polynomial.X - Polynomial.C r ≠ 0 := Polynomial.X_sub_C_ne_zero r
    have hq1_ne : q₁ ≠ 0 := by intro h; rw [h, mul_zero] at hq1; exact hq_ne hq1
    have hq1_nd : q₁.natDegree = 1 := by
      rw [hq1, Polynomial.natDegree_mul hlin_ne hq1_ne, Polynomial.natDegree_X_sub_C] at hnd2
      omega
    -- Any root of q₁ in ZMod p must be r; since q₁ has degree 1, its root IS r!
    have hq1_eq : q₁ = Polynomial.C (q₁.coeff 1) * Polynomial.X + Polynomial.C (q₁.coeff 0) :=
      Polynomial.eq_X_add_C_of_degree_le_one (Polynomial.degree_le_of_natDegree_le (show q₁.natDegree ≤ 1 by omega))
    have hq1_c1 : q₁.coeff 1 ≠ 0 := by
      intro h
      have hlc : q₁.leadingCoeff = 0 := by
        change q₁.coeff q₁.natDegree = 0; rw [hq1_nd]; exact h
      exact hq1_ne (Polynomial.leadingCoeff_eq_zero.mp hlc)
    let r₂ := -(q₁.coeff 0) / q₁.coeff 1
    have hq1_rt2 : q₁.IsRoot r₂ := by
      rw [Polynomial.IsRoot.def, hq1_eq]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, r₂]
      rw [mul_div_cancel₀ _ hq1_c1]; ring
    have hq_rt2 : (dehomog1 (restrictA a Q.toPoly)).IsRoot r₂ := by
      rw [Polynomial.IsRoot.def, hq1, Polynomial.eval_mul, hq1_rt2, mul_zero]
    -- Show r₂ = r by constructing point v₂ on lineThrough (embed a) with v₂ 1 / v₂ 2 = r₂
    let w₂ : Fin 3 → ZMod p := fun i => match i with | 0 => -a 0 * r₂ - a 1 | 1 => r₂ | 2 => 1
    have hw₂ : w₂ ≠ 0 := fun h => one_ne_zero (congrFun h 2)
    have hv2_mem : norm3 w₂ ∈ lineThrough (embed a) := by
      rw [mem_lineThrough]
      obtain ⟨c, _, hc⟩ := norm3_exists_smul hw₂
      exact ⟨norm3_isNorm hw₂, by rw [hc, dot3_smul_left]; unfold dot3 w₂ embed; dsimp only; ring⟩
    have hv2_ev : eval (norm3 w₂) Q.toPoly = 0 := by
      obtain ⟨c, _, hc⟩ := norm3_exists_smul hw₂
      rw [hc, isHomogeneous_eval_smul hQhom]
      have hdot : dot3 w₂ (embed a) = 0 := by unfold dot3 w₂ embed; dsimp only; ring
      rw [← eval_restrictA_of_dot3_zero a Q.toPoly hdot]
      have harg : (fun i : Fin 2 => match i with | 0 => w₂ 1 | 1 => w₂ 2) =
          (fun i : Fin 2 => match i with | 0 => r₂ | 1 => 1) := by ext i; fin_cases i <;> rfl
      rw [harg, ← eval_dehomog1]
      exact by rw [hq_rt2, mul_zero]
    have hv2_tan : norm3 w₂ ∈ tangents A a :=
      mem_tangents_of_eval_dvd_segreEnv hp2 harc he hEA hE hdvd ha hv2_mem hv2_ev
    have hv2_in : norm3 w₂ ∈ (tangents A a).filter fun v => eval v Q.toPoly = 0 :=
      mem_filter.mpr ⟨hv2_tan, hv2_ev⟩
    rw [hu_eq, mem_singleton] at hv2_in
    obtain ⟨c, hc0, hc⟩ := norm3_exists_smul hw₂
    have hr2_eq : r₂ = r := by
      have h1 : u 1 = c * r₂ := by rw [← hv2_in, hc]; rfl
      have h2 : u 2 = c * 1 := by rw [← hv2_in, hc]; rfl
      rw [mul_one] at h2
      dsimp only [r]; rw [h1, h2, mul_div_cancel_left₀ _ hc0]
    -- So q₁ = C (q₁.coeff 1) * (X - C r), hence dehomog1 = C A₂ * (X - C r)^2 -> A₂ C₂ - B₂^2 = 0!
    have hq1_lin : q₁ = Polynomial.C (q₁.coeff 1) * (Polynomial.X - Polynomial.C r) := by
      conv_lhs => rw [hq1_eq]
      rw [← hr2_eq]
      have hc0 : q₁.coeff 0 = -(q₁.coeff 1 * r₂) := by
        dsimp only [r₂]; rw [mul_div_cancel₀ _ hq1_c1, neg_neg]
      rw [hc0, mul_sub, ← map_mul, map_neg]; ring
    have hq_sq : dehomog1 (restrictA a Q.toPoly) = Polynomial.C (q₁.coeff 1) * (Polynomial.X - Polynomial.C r) ^ 2 := by
      conv_lhs => rw [hq1, hq1_lin]
      ring
    have hsq_exp : Polynomial.C (q₁.coeff 1) * (Polynomial.X - Polynomial.C r) ^ 2 =
        Polynomial.C (q₁.coeff 1) * Polynomial.X ^ 2 +
        Polynomial.C (-2 * q₁.coeff 1 * r) * Polynomial.X +
        Polynomial.C (q₁.coeff 1 * r ^ 2) := by
      simp only [map_mul, map_neg, map_ofNat, map_pow]; ring
    have hc2_eq : A₂ = q₁.coeff 1 := by
      have h := congrArg (fun f => Polynomial.coeff f 2) (hdehom.symm.trans (hq_sq.trans hsq_exp))
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_X, Polynomial.coeff_C] at h
      norm_num at h; exact h
    have hc1_eq : 2 * B₂ = -2 * q₁.coeff 1 * r := by
      have h := congrArg (fun f => Polynomial.coeff f 1) (hdehom.symm.trans (hq_sq.trans hsq_exp))
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_X, Polynomial.coeff_C] at h
      norm_num at h; linear_combination h
    have hc0_eq : C₂ = q₁.coeff 1 * r ^ 2 := by
      have h := congrArg (fun f => Polynomial.coeff f 0) (hdehom.symm.trans (hq_sq.trans hsq_exp))
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_X, Polynomial.coeff_C] at h
      norm_num at h; exact h
    have hB2_eq : B₂ = -(q₁.coeff 1 * r) := by
      apply mul_left_cancel₀ (two_ne_zero_of_prime_ne_two hp2)
      linear_combination hc1_eq
    apply hadj
    rw [← hdisc, hc2_eq, hB2_eq, hc0_eq]; ring

lemma four_mul_card_le_of_deg_two {A E : Finset (Fin 2 → ZMod p)} (hp2 : p ≠ 2)
    (harc : ∀ s ⊆ A, s.card = 3 → ¬ Collinear (ZMod p) (s : Set (Fin 2 → ZMod p)))
    (hnc : ¬ ∃ R : MvPolynomial (Fin 2) (ZMod p),
      R ≠ 0 ∧ R.totalDegree ≤ 2 ∧ ∀ a ∈ A, eval a R = 0)
    {e : Fin 2 → ZMod p} (he : e ∈ A) (hEA : E ⊆ A) (hE : E.card = 2 * (p + 2 - A.card) + 2)
    {P : MvPolynomial (Fin 3) (ZMod p)} (hPh : P.IsHomogeneous 2)
    (hdvd : P ∣ segreEnv A E e)
    (hirr : Irreducible (MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) P)) :
    4 * A.card ≤ 3 * p + 5 := by
  classical
  obtain ⟨Q, rfl⟩ := SymQuad.homog2_eq_toPoly (two_ne_zero_of_prime_ne_two hp2) hPh
  have hdet : Q.det ≠ 0 := SymQuad.det_ne_zero_of_irreducible_map hp2 Q hirr
  let ZP := (univ : Finset (Fin 3 → ZMod p)).filter fun u => IsNorm u ∧ Q.evalQ u = 0
  let ZQ := (univ : Finset (Fin 3 → ZMod p)).filter fun u => IsNorm u ∧ Q.adj.evalQ u = 0
  have hZP_le : ZP.card ≤ p + 1 := SymQuad.card_zeros_le_add_one hp2 Q hdet
  have hZQ_le : ZQ.card ≤ p + 1 :=
    SymQuad.card_zeros_le_add_one hp2 Q.adj (by rw [Q.adj_det]; exact pow_ne_zero 2 hdet)
  let B := A.filter fun a => Q.adj.evalQ (embed a) = 0
  let Cset := A.filter fun a => Q.adj.evalQ (embed a) ≠ 0
  have hBC_sum : B.card + Cset.card = A.card := by
    have hdisj : Disjoint B Cset := by
      rw [Finset.disjoint_left]; intro a h1 h2; exact (mem_filter.mp h2).2 (mem_filter.mp h1).2
    rw [← card_union_of_disjoint hdisj]
    congr 1; ext a; simp only [B, Cset, mem_union, mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro ha; by_cases h : Q.adj.evalQ (embed a) = 0; exact Or.inl ⟨ha, h⟩; exact Or.inr ⟨ha, h⟩
  -- Bound 1: B.card + 2 * Cset.card ≤ ZP.card ≤ p + 1
  have hbound1 : B.card + 2 * Cset.card ≤ p + 1 := by
    have hsub : A.biUnion (fun a => (tangents A a).filter fun u => eval u Q.toPoly = 0) ⊆ ZP := by
      intro u hu
      rcases mem_biUnion.mp hu with ⟨a, _, hua⟩
      exact mem_filter.mpr ⟨mem_univ u, (mem_tangents.mp (mem_filter.mp hua).1).1,
        by rw [← Q.eval_toPoly]; exact (mem_filter.mp hua).2⟩
    have hdisj : Set.PairwiseDisjoint (A : Set (Fin 2 → ZMod p))
        (fun a => (tangents A a).filter fun u => eval u Q.toPoly = 0) := by
      intro a ha b hb hab
      change Disjoint _ _
      exact (tangents_disjoint ha hb hab).mono (filter_subset _ _) (filter_subset _ _)
    have hpart_A : A = B ∪ Cset := by
      ext a; simp only [B, Cset, mem_union, mem_filter]
      constructor
      · intro ha; by_cases h : Q.adj.evalQ (embed a) = 0; exact Or.inl ⟨ha, h⟩; exact Or.inr ⟨ha, h⟩
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    have hBC_disj : Disjoint B Cset := by
      rw [Finset.disjoint_left]; intro a h1 h2; exact (mem_filter.mp h2).2 (mem_filter.mp h1).2
    calc B.card + 2 * Cset.card
        = (∑ _a ∈ B, 1) + ∑ _a ∈ Cset, 2 := by simp [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ (∑ a ∈ B, ((tangents A a).filter fun u => eval u Q.toPoly = 0).card) +
          ∑ a ∈ Cset, ((tangents A a).filter fun u => eval u Q.toPoly = 0).card := by
            apply Nat.add_le_add
            · apply Finset.sum_le_sum; intro a ha
              have h := deg_le_two_mul_card_tangents_zeros hp2 harc he hEA hE hPh hdvd (mem_filter.mp ha).1
              omega
            · apply Finset.sum_le_sum; intro a ha
              exact two_le_card_tangents_zeros_of_adj_ne_zero hp2 harc he hEA hE Q hdvd
                (mem_filter.mp ha).1 (mem_filter.mp ha).2
      _ = ∑ a ∈ A, ((tangents A a).filter fun u => eval u Q.toPoly = 0).card := by
            rw [hpart_A, Finset.sum_union hBC_disj]
      _ = (A.biUnion (fun a => (tangents A a).filter fun u => eval u Q.toPoly = 0)).card :=
            (card_biUnion hdisj).symm
      _ ≤ ZP.card := card_le_card hsub
      _ ≤ p + 1 := hZP_le
  -- Bound 2: 2 * B.card + 2 ≤ ZQ.card ≤ p + 1 (using x ∈ Cset from hnc)
  have hC_ne : Cset.Nonempty := by
    by_contra hemp
    apply hnc
    refine ⟨Q.adj.toAffPoly,
      Q.adj.toAffPoly_ne_zero_of_det_ne_zero (two_ne_zero_of_prime_ne_two hp2)
        (by rw [Q.adj_det]; exact pow_ne_zero 2 hdet),
      Q.adj.totalDegree_toAffPoly_le, ?_⟩
    intro a ha
    rw [Q.adj.eval_toAffPoly]
    by_contra hne
    exact hemp ⟨a, mem_filter.mpr ⟨ha, hne⟩⟩
  obtain ⟨x, hxC⟩ := hC_ne
  have hxA : x ∈ A := (mem_filter.mp hxC).1
  have hxq : Q.adj.evalQ (embed x) ≠ 0 := (mem_filter.mp hxC).2
  -- For every b ∈ B, Q.adj.bilin (embed x) (embed b) ≠ 0
  have hbilin_ne : ∀ b ∈ B, Q.adj.bilin (embed x) (embed b) ≠ 0 := by
    intro b hb h0
    have hbA : b ∈ A := (mem_filter.mp hb).1
    have hbq : Q.adj.evalQ (embed b) = 0 := (mem_filter.mp hb).2
    have hbx : b ≠ x := fun h => hxq (h ▸ hbq)
    let u := Q.adj.mulVec (embed b)
    have hu_ne : u ≠ 0 := by
      intro hu0
      have h1 := Q.mulVec_adj_mulVec (embed b)
      change Q.mulVec u = Q.det • embed b at h1
      rw [hu0] at h1
      have h00 : Q.mulVec 0 = 0 := by ext i; fin_cases i <;> simp [SymQuad.mulVec]
      rw [h00] at h1
      exact embed_ne_zero b ((smul_eq_zero.mp h1.symm).resolve_left hdet)
    obtain ⟨c, hc0, hc⟩ := norm3_exists_smul hu_ne
    have hnu_mem : norm3 u ∈ lineThrough (embed x) := by
      rw [mem_lineThrough]
      refine ⟨norm3_isNorm hu_ne, ?_⟩
      rw [hc, dot3_smul_left, dot3_comm, ← Q.adj.bilin_eq_dot3, h0, mul_zero]
    have hnu_ev : eval (norm3 u) Q.toPoly = 0 := by
      rw [Q.eval_toPoly, hc, Q.evalQ_smul, Q.evalQ_mulVec_adj, hbq, mul_zero, mul_zero]
    have hnu_tan : norm3 u ∈ tangents A x :=
      mem_tangents_of_eval_dvd_segreEnv hp2 harc he hEA hE hdvd hxA hnu_mem hnu_ev
    apply (mem_tangents.mp hnu_tan).2.2 b hbA hbx
    rw [hc, dot3_smul_left, dot3_comm, ← Q.adj.bilin_eq_dot3]
    change c * Q.adj.evalQ (embed b) = 0
    rw [hbq, mul_zero]
  -- Construct 3 pairwise disjoint subsets of ZQ: S1 = embed '' B, S2 = secant2 '' B, S3 = {q1, q2}
  let S1 := B.image embed
  let sec2 : (Fin 2 → ZMod p) → Fin 3 → ZMod p := fun b =>
    norm3 ((-Q.adj.evalQ (embed x)) • embed b + (2 * Q.adj.bilin (embed x) (embed b)) • embed x)
  let S2 := B.image sec2
  have hS1_card : S1.card = B.card :=
    card_image_of_injOn (fun a _ b _ h => embed_inj h)
  have hS1_sub : S1 ⊆ ZQ := by
    intro v hv; rcases mem_image.mp hv with ⟨b, hb, rfl⟩
    exact mem_filter.mpr ⟨mem_univ _, Or.inl rfl, (mem_filter.mp hb).2⟩
  have hvec_ne : ∀ b ∈ B,
      (-Q.adj.evalQ (embed x)) • embed b + (2 * Q.adj.bilin (embed x) (embed b)) • embed x ≠ 0 := by
    intro b hb h0
    have hbA : b ∈ A := (mem_filter.mp hb).1
    have hbq : Q.adj.evalQ (embed b) = 0 := (mem_filter.mp hb).2
    have hbx : b ≠ x := fun h => hxq (h ▸ hbq)
    have hcr := congrArg (cross3 (embed x)) h0
    have hcr0 : cross3 (embed x) 0 = 0 := by ext i; fin_cases i <;> simp [cross3]
    rw [hcr0] at hcr
    have hcr_lin : cross3 (embed x) ((-Q.adj.evalQ (embed x)) • embed b +
        (2 * Q.adj.bilin (embed x) (embed b)) • embed x) =
        (-Q.adj.evalQ (embed x)) • cross3 (embed x) (embed b) := by
      ext i; fin_cases i <;>
        (unfold cross3; dsimp only; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring)
    rw [hcr_lin] at hcr
    have hcr_xb : cross3 (embed x) (embed b) = 0 :=
      (smul_eq_zero.mp hcr).resolve_left (neg_ne_zero.mpr hxq)
    obtain ⟨c, hc⟩ := (cross3_eq_zero_iff (embed_ne_zero x)).mp hcr_xb
    have hc1 : (1 : ZMod p) = c * 1 := congrFun hc 0
    rw [mul_one] at hc1; rw [← hc1, one_smul] at hc
    exact hbx (embed_inj hc)
  have hS2_sub : S2 ⊆ ZQ := by
    intro v hv; rcases mem_image.mp hv with ⟨b, hb, rfl⟩
    have hne := hvec_ne b hb
    obtain ⟨c, _, hc⟩ := norm3_exists_smul hne
    refine mem_filter.mpr ⟨mem_univ _, norm3_isNorm hne, ?_⟩
    change Q.adj.evalQ (norm3 _) = 0
    rw [hc, Q.adj.evalQ_smul, Q.adj.evalQ_add_smul, (mem_filter.mp hb).2, Q.adj.bilin_symm]
    ring
  have hS2_inj : Set.InjOn sec2 B := by
    intro b₁ hb₁ b₂ hb₂ heq
    by_contra h12
    have h1A : b₁ ∈ A := (mem_filter.mp hb₁).1
    have h2A : b₂ ∈ A := (mem_filter.mp hb₂).1
    have h1x : b₁ ≠ x := fun h => hxq (h ▸ (mem_filter.mp hb₁).2)
    have h2x : b₂ ≠ x := fun h => hxq (h ▸ (mem_filter.mp hb₂).2)
    obtain ⟨c, hc0, hc⟩ := (norm3_eq_iff_prop (hvec_ne b₁ hb₁) (hvec_ne b₂ hb₂)).mp heq
    have hdet0 : det3 (embed x) (embed b₁) (embed b₂) = 0 := by
      -- (-q) • b₁ + s₁ • x = c • ((-q) • b₂ + s₂ • x) -> det3 x b₁ b₂ = 0!
      have hcr : det3 (embed x) ((-Q.adj.evalQ (embed x)) • embed b₁ +
            (2 * Q.adj.bilin (embed x) (embed b₁)) • embed x) (embed b₂) =
          det3 (embed x) (c • ((-Q.adj.evalQ (embed x)) • embed b₂ +
            (2 * Q.adj.bilin (embed x) (embed b₂)) • embed x)) (embed b₂) := by rw [hc]
      have hL : det3 (embed x) ((-Q.adj.evalQ (embed x)) • embed b₁ +
            (2 * Q.adj.bilin (embed x) (embed b₁)) • embed x) (embed b₂) =
          (-Q.adj.evalQ (embed x)) * det3 (embed x) (embed b₁) (embed b₂) := by
        unfold det3 dot3 cross3; dsimp only; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      have hR : det3 (embed x) (c • ((-Q.adj.evalQ (embed x)) • embed b₂ +
            (2 * Q.adj.bilin (embed x) (embed b₂)) • embed x)) (embed b₂) = 0 := by
        unfold det3 dot3 cross3; dsimp only; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [hL, hR] at hcr
      exact (mul_eq_zero.mp hcr).resolve_left (neg_ne_zero.mpr hxq)
    exact det3_ne_zero_of_arc harc hxA h1A h2A h1x.symm h2x.symm h12 hdet0
  have hS2_card : S2.card = B.card := card_image_of_injOn hS2_inj
  have hS12_disj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    rcases mem_image.mp hv1 with ⟨b₁, hb₁, rfl⟩
    rcases mem_image.mp hv2 with ⟨b₂, hb₂, heq⟩
    have h1A : b₁ ∈ A := (mem_filter.mp hb₁).1
    have h2A : b₂ ∈ A := (mem_filter.mp hb₂).1
    have h1x : b₁ ≠ x := fun h => hxq (h ▸ (mem_filter.mp hb₁).2)
    have h2x : b₂ ≠ x := fun h => hxq (h ▸ (mem_filter.mp hb₂).2)
    obtain ⟨c, hc0, hc⟩ := norm3_exists_smul (hvec_ne b₂ hb₂)
    have hEq : embed b₁ = c • ((-Q.adj.evalQ (embed x)) • embed b₂ +
        (2 * Q.adj.bilin (embed x) (embed b₂)) • embed x) := by rw [← heq, ← hc]
    by_cases h12 : b₁ = b₂
    · subst h12
      -- embed b₁ = (-c * q) • embed b₁ + (c * s) • embed x -> cross3 b₁ x = 0!
      have hcr : cross3 (embed b₁) (embed b₁) =
          cross3 (embed b₁) (c • ((-Q.adj.evalQ (embed x)) • embed b₁ +
            (2 * Q.adj.bilin (embed x) (embed b₁)) • embed x)) := congrArg (cross3 (embed b₁)) hEq
      have hL : cross3 (embed b₁) (embed b₁) = 0 := by
        ext i; fin_cases i <;> simp [cross3] <;> ring
      have hR : cross3 (embed b₁) (c • ((-Q.adj.evalQ (embed x)) • embed b₁ +
            (2 * Q.adj.bilin (embed x) (embed b₁)) • embed x)) =
          (c * (2 * Q.adj.bilin (embed x) (embed b₁))) • cross3 (embed b₁) (embed x) := by
        ext i; fin_cases i <;>
          (unfold cross3; dsimp only; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring)
      rw [hL, hR] at hcr
      have hcr0 : cross3 (embed b₁) (embed x) = 0 :=
        (smul_eq_zero.mp hcr.symm).resolve_left
          (mul_ne_zero hc0 (mul_ne_zero (two_ne_zero_of_prime_ne_two hp2) (hbilin_ne b₁ hb₁)))
      obtain ⟨d, hd⟩ := (cross3_eq_zero_iff (embed_ne_zero b₁)).mp hcr0
      have hd1 : (1 : ZMod p) = d * 1 := congrFun hd 0
      rw [mul_one] at hd1; rw [← hd1, one_smul] at hd
      exact h1x (embed_inj hd).symm
    · have hdet0 : det3 (embed x) (embed b₂) (embed b₁) = 0 := by
        rw [hEq]
        unfold det3 dot3 cross3; dsimp only; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      exact det3_ne_zero_of_arc harc hxA h2A h1A h2x.symm h1x.symm (Ne.symm h12) hdet0
  -- Two distinct tangent points q₁, q₂ from S_x = (tangents A x).filter (eval · Q.toPoly = 0)
  have hSx_ge2 : 2 ≤ ((tangents A x).filter fun u => eval u Q.toPoly = 0).card :=
    two_le_card_tangents_zeros_of_adj_ne_zero hp2 harc he hEA hE Q hdvd hxA hxq
  obtain ⟨u₁, hu₁, u₂, hu₂, hu12⟩ :=
    Finset.one_lt_card.mp (show 1 < ((tangents A x).filter fun u => eval u Q.toPoly = 0).card by omega)
  have hmul_ne : ∀ u : Fin 3 → ZMod p, u ≠ 0 → Q.mulVec u ≠ 0 := by
    intro u hu h0
    have h1 := Q.adj_mulVec_mulVec u
    rw [h0] at h1
    have h00 : Q.adj.mulVec 0 = 0 := by ext i; fin_cases i <;> simp [SymQuad.mulVec]
    rw [h00] at h1
    exact hu ((smul_eq_zero.mp h1.symm).resolve_left hdet)
  have hu1_ne : u₁ ≠ 0 := isNorm_ne_zero (mem_tangents.mp (mem_filter.mp hu₁).1).1
  have hu2_ne : u₂ ≠ 0 := isNorm_ne_zero (mem_tangents.mp (mem_filter.mp hu₂).1).1
  let q₁ := norm3 (Q.mulVec u₁)
  let q₂ := norm3 (Q.mulVec u₂)
  have hq12 : q₁ ≠ q₂ := by
    intro heq
    obtain ⟨c, hc0, hc⟩ := (norm3_eq_iff_prop (hmul_ne u₁ hu1_ne) (hmul_ne u₂ hu2_ne)).mp heq
    have hadj := congrArg Q.adj.mulVec hc
    rw [Q.adj_mulVec_mulVec, Q.adj.mulVec_smul, Q.adj_mulVec_mulVec, smul_smul,
      mul_comm c, ← smul_smul] at hadj
    have hu_eq : u₁ = c • u₂ := by ext i; exact mul_left_cancel₀ hdet (congrFun hadj i)
    exact hu12 (isNorm_eq_of_smul (mem_tangents.mp (mem_filter.mp hu₁).1).1
      (mem_tangents.mp (mem_filter.mp hu₂).1).1 hu_eq)
  have hq_in_ZQ : ∀ {u : Fin 3 → ZMod p}, u ∈ (tangents A x).filter (fun v => eval v Q.toPoly = 0) →
      norm3 (Q.mulVec u) ∈ ZQ ∧ Q.adj.bilin (embed x) (norm3 (Q.mulVec u)) = 0 := by
    intro u hu
    have hun := (mem_tangents.mp (mem_filter.mp hu).1).1
    have hud := (mem_tangents.mp (mem_filter.mp hu).1).2.1
    have hue := (mem_filter.mp hu).2
    rw [Q.eval_toPoly] at hue
    have hne := hmul_ne u (isNorm_ne_zero hun)
    obtain ⟨c, _, hc⟩ := norm3_exists_smul hne
    refine ⟨mem_filter.mpr ⟨mem_univ _, norm3_isNorm hne, ?_⟩, ?_⟩
    · rw [hc, Q.adj.evalQ_smul, Q.evalQ_adj_mulVec, hue, mul_zero, mul_zero]
    · rw [hc, Q.adj.bilin_smul_right, Q.adj.bilin_eq_dot3, Q.adj_mulVec_mulVec,
        dot3_smul_right, dot3_comm, hud, mul_zero, mul_zero]
  let S3 : Finset (Fin 3 → ZMod p) := {q₁, q₂}
  have hS3_card : S3.card = 2 := by rw [card_insert_of_notMem, card_singleton]; simpa using hq12
  have hS3_sub : S3 ⊆ ZQ := by
    intro v hv; simp only [S3, mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact (hq_in_ZQ hu₁).1
    · exact (hq_in_ZQ hu₂).1
  have hS3_bilin0 : ∀ v ∈ S3, Q.adj.bilin (embed x) v = 0 := by
    intro v hv; simp only [S3, mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact (hq_in_ZQ hu₁).2
    · exact (hq_in_ZQ hu₂).2
  have hS13_disj : Disjoint S1 S3 := by
    rw [Finset.disjoint_left]
    intro v hv1 hv3
    rcases mem_image.mp hv1 with ⟨b, hb, rfl⟩
    exact hbilin_ne b hb (hS3_bilin0 _ hv3)
  have hS23_disj : Disjoint S2 S3 := by
    rw [Finset.disjoint_left]
    intro v hv2 hv3
    rcases mem_image.mp hv2 with ⟨b, hb, rfl⟩
    have h0 := hS3_bilin0 _ hv3
    obtain ⟨c, hc0, hc⟩ := norm3_exists_smul (hvec_ne b hb)
    change Q.adj.bilin (embed x) (norm3 _) = 0 at h0
    rw [hc, Q.adj.bilin_smul_right, Q.adj.bilin_add_right, Q.adj.bilin_smul_right,
      Q.adj.bilin_smul_right] at h0
    have hsimp : Q.adj.bilin (embed x) (embed x) = Q.adj.evalQ (embed x) := rfl
    rw [hsimp] at h0
    have hprod : c * (Q.adj.evalQ (embed x) * Q.adj.bilin (embed x) (embed b)) = 0 := by
      linear_combination h0
    exact mul_ne_zero hc0 (mul_ne_zero hxq (hbilin_ne b hb)) hprod
  have hbound2 : 2 * B.card + 2 ≤ p + 1 := by
    have hdisj_all : Disjoint (S1 ∪ S2) S3 := Finset.disjoint_union_left.mpr ⟨hS13_disj, hS23_disj⟩
    have hunion_sub : (S1 ∪ S2) ∪ S3 ⊆ ZQ :=
      union_subset (union_subset hS1_sub hS2_sub) hS3_sub
    have hle := card_le_card hunion_sub
    rw [card_union_of_disjoint hdisj_all, card_union_of_disjoint hS12_disj,
      hS1_card, hS2_card, hS3_card] at hle
    omega
  omega

end DegTwo

section GeomReducible

variable {p : ℕ} [Fact p.Prime]

lemma exists_notMem_of_isAlgClosed {K : Type*} [Field K] [IsAlgClosed K] (S : Finset K) :
    ∃ x : K, x ∉ S := by
  by_cases hS : S.Nonempty
  · let P : Polynomial K := (∏ s ∈ S, (Polynomial.X - Polynomial.C s)) + 1
    have hmon_prod : (∏ s ∈ S, (Polynomial.X - Polynomial.C s)).Monic :=
      Polynomial.monic_prod_of_monic S _ (fun s _ => Polynomial.monic_X_sub_C s)
    have hnd_prod : (∏ s ∈ S, (Polynomial.X - Polynomial.C s)).natDegree = S.card := by
      rw [Polynomial.natDegree_prod_of_monic S _ (fun s _ => Polynomial.monic_X_sub_C s)]
      simp
    have hnd_P : P.natDegree = S.card := by
      dsimp only [P]
      rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
      · exact hnd_prod
      · rw [Polynomial.natDegree_one, hnd_prod]; exact card_pos.mpr hS
    have hP0 : P ≠ 0 := by intro h; rw [h, Polynomial.natDegree_zero] at hnd_P; have := card_pos.mpr hS; omega
    have hdeg : P.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hP0, hnd_P]
      have hpos : 0 < S.card := card_pos.mpr hS
      intro h0
      have : S.card = 0 := by exact_mod_cast h0
      omega
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root P hdeg
    refine ⟨r, ?_⟩
    intro hrS
    rw [Polynomial.IsRoot.def] at hr
    dsimp only [P] at hr
    rw [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_prod] at hr
    have hprod0 : (∏ s ∈ S, Polynomial.eval r (Polynomial.X - Polynomial.C s)) = 0 := by
      apply Finset.prod_eq_zero hrS
      simp
    rw [hprod0, zero_add] at hr
    exact one_ne_zero hr
  · exact ⟨0, by rw [not_nonempty_iff_eq_empty.mp hS]; exact notMem_empty 0⟩

lemma exists_eval_ne_zero_mv2 {K : Type*} [Field K] [IsAlgClosed K]
    {G : MvPolynomial (Fin 2) K} (hG : G ≠ 0) :
    ∃ v : Fin 2 → K, eval v G ≠ 0 := by
  classical
  let g := MvPolynomial.finSuccEquiv K 1 G
  have hg0 : g ≠ 0 := fun h => hG ((MvPolynomial.finSuccEquiv K 1).injective (h.trans (map_zero _).symm))
  have hlc0 : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg0
  let toPoly1 : MvPolynomial (Fin 1) K →+* Polynomial K :=
    MvPolynomial.eval₂Hom Polynomial.C (fun _ => Polynomial.X)
  have hev1 : ∀ (q : MvPolynomial (Fin 1) K) (β : K),
      Polynomial.eval β (toPoly1 q) = eval (fun _ => β) q := by
    intro q β
    induction q using MvPolynomial.induction_on with
    | C c => simp [toPoly1]
    | add a b ha hb => simp [map_add, ha, hb]
    | mul_X a i ha => rw [map_mul, map_mul, Polynomial.eval_mul, ha]; simp [toPoly1]
  have htoPoly1_ne : toPoly1 g.leadingCoeff ≠ 0 := by
    intro h0
    apply hlc0
    ext m
    rw [MvPolynomial.coeff_zero]
    have hc := congrArg (fun f : Polynomial K => f.coeff (m 0)) h0
    rw [Polynomial.coeff_zero] at hc
    conv_lhs at hc => rw [g.leadingCoeff.as_sum]
    rw [map_sum, Polynomial.finsetSum_coeff] at hc
    have hterm : ∀ n : Fin 1 →₀ ℕ,
        (toPoly1 (monomial n (g.leadingCoeff.coeff n))).coeff (m 0) =
          if n = m then g.leadingCoeff.coeff n else 0 := by
      intro n
      unfold toPoly1
      rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp),
        Fin.prod_univ_one, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      have hiff : n 0 = m 0 ↔ n = m := by
        constructor
        · intro h; exact Finsupp.ext fun i => by rw [Fin.eq_zero i]; exact h
        · intro h; rw [h]
      by_cases heq : n = m
      · rw [heq]; simp
      · have hne0 : ¬ (m 0 = n 0) := fun h => heq (hiff.mp h.symm)
        simp [heq, hne0]
    simp_rw [hterm] at hc
    by_cases hm : m ∈ g.leadingCoeff.support
    · rw [Finset.sum_eq_single m] at hc
      · simpa using hc
      · intro n _ hne; simp [hne]
      · intro hnot; exact absurd hm hnot
    · exact MvPolynomial.notMem_support_iff.mp hm
  obtain ⟨β, hβ⟩ := exists_notMem_of_isAlgClosed (toPoly1 g.leadingCoeff).roots.toFinset
  have hlc_ev : eval (fun _ : Fin 1 => β) g.leadingCoeff ≠ 0 := by
    rw [← hev1]
    intro h0
    apply hβ
    rw [Multiset.mem_toFinset, Polynomial.mem_roots htoPoly1_ne, Polynomial.IsRoot.def]
    exact h0
  let gβ : Polynomial K := g.map (eval (fun _ : Fin 1 => β))
  have hgβ_ne : gβ ≠ 0 := by
    intro h0
    have hc := congrArg (fun f : Polynomial K => f.coeff g.natDegree) h0
    rw [Polynomial.coeff_zero, Polynomial.coeff_map] at hc
    exact hlc_ev hc
  obtain ⟨α, hα⟩ := exists_notMem_of_isAlgClosed gβ.roots.toFinset
  have hα_ne : Polynomial.eval α gβ ≠ 0 := by
    intro h0
    apply hα
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hgβ_ne, Polynomial.IsRoot.def]
    exact h0
  refine ⟨Fin.cons α (fun _ => β), ?_⟩
  rw [MvPolynomial.eval_eq_eval_mv_eval']
  exact hα_ne

lemma resultant_isHomogeneous {K : Type*} [Field K] {f₀ f₁ : Polynomial (MvPolynomial (Fin 2) K)}
    {m : ℕ}
    (hf0_h : ∀ k, k ≤ m → (f₀.coeff k).IsHomogeneous (m - k))
    (hf1_h : ∀ k, k ≤ m → (f₁.coeff k).IsHomogeneous (m - k)) :
    (Polynomial.resultant f₀ f₁ m m).IsHomogeneous (m * m) := by
  classical
  unfold Polynomial.resultant
  rw [Matrix.det_apply]
  apply IsHomogeneous.sum
  intro σ _
  have hsign : ∀ (s : ℤˣ) (P : MvPolynomial (Fin 2) K), P.IsHomogeneous (m * m) →
      (s • P).IsHomogeneous (m * m) := by
    intro s P hP
    rcases Int.units_eq_one_or s with rfl | rfl
    · simpa using hP
    · simpa using hP.neg
  apply hsign
  let base : Fin (m + m) → ℕ := fun j => if j.val < m then j.val else j.val - m
  have hsylv_left : ∀ (i : Fin (m + m)) (j₁ : Fin m),
      (f₀.sylvester f₁ m m) i (Fin.castAdd m j₁) =
        if i.val ∈ Set.Icc j₁.val (j₁.val + m) then f₁.coeff (i.val - j₁.val) else 0 := by
    intro i j₁; unfold Polynomial.sylvester; simp only [Matrix.of_apply, Fin.addCases_left]
  have hsylv_right : ∀ (i : Fin (m + m)) (j₁ : Fin m),
      (f₀.sylvester f₁ m m) i (Fin.natAdd m j₁) =
        if i.val ∈ Set.Icc j₁.val (j₁.val + m) then f₀.coeff (i.val - j₁.val) else 0 := by
    intro i j₁; unfold Polynomial.sylvester; simp only [Matrix.of_apply, Fin.addCases_right]
  by_cases hall : ∀ j : Fin (m + m), (σ j).val ∈ Set.Icc (base j) (base j + m)
  · have hterm_h : ∀ j : Fin (m + m),
        ((f₀.sylvester f₁ m m) (σ j) j).IsHomogeneous (m + base j - (σ j).val) := by
      intro j
      by_cases hj : j.val < m
      · let j₁ : Fin m := ⟨j.val, hj⟩
        have hj_eq : j = Fin.castAdd m j₁ := Fin.ext rfl
        have hbase : base j = j₁.val := by simp [base, hj, j₁]
        have hin : (σ j).val ∈ Set.Icc j₁.val (j₁.val + m) := by
          have := hall j; rwa [hbase] at this
        rw [hj_eq, hsylv_left, ← hj_eq]
        simp only [hin, ite_true, hbase]
        have hle : (σ j).val - j₁.val ≤ m := by have h1 := hin.1; have h2 := hin.2; omega
        have heq : m - ((σ j).val - j₁.val) = m + j₁.val - (σ j).val := by
          have h1 := hin.1; have h2 := hin.2; omega
        rw [← heq]
        exact hf1_h _ hle
      · let j₁ : Fin m := ⟨j.val - m, by omega⟩
        have hj_eq : j = Fin.natAdd m j₁ := Fin.ext (by dsimp [Fin.natAdd, j₁]; omega)
        have hbase : base j = j₁.val := by simp [base, hj, j₁]
        have hin : (σ j).val ∈ Set.Icc j₁.val (j₁.val + m) := by
          have := hall j; rwa [hbase] at this
        rw [hj_eq, hsylv_right, ← hj_eq]
        simp only [hin, ite_true, hbase]
        have hle : (σ j).val - j₁.val ≤ m := by have h1 := hin.1; have h2 := hin.2; omega
        have heq : m - ((σ j).val - j₁.val) = m + j₁.val - (σ j).val := by
          have h1 := hin.1; have h2 := hin.2; omega
        rw [← heq]
        exact hf0_h _ hle
    have hprod := IsHomogeneous.prod univ (fun j => (f₀.sylvester f₁ m m) (σ j) j)
      (fun j => m + base j - (σ j).val) (fun j _ => hterm_h j)
    have hsum_deg : ∑ j : Fin (m + m), (m + base j - (σ j).val) = m * m := by
      have hadd : ∑ j : Fin (m + m), (m + base j - (σ j).val) + ∑ j : Fin (m + m), (σ j).val =
          ∑ j : Fin (m + m), (m + base j) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        have h2 := (hall j).2
        omega
      have hperm : ∑ j : Fin (m + m), (σ j).val = ∑ i : Fin (m + m), i.val :=
        Equiv.sum_comp σ (fun i : Fin (m + m) => i.val)
      have hsum_i : ∑ i : Fin (m + m), i.val =
          (∑ j₁ : Fin m, j₁.val) + (∑ j₁ : Fin m, (m + j₁.val)) := by
        rw [Fin.sum_univ_add]
        simp only [Fin.val_castAdd, Fin.val_natAdd]
      have hsum_b : ∑ j : Fin (m + m), (m + base j) =
          (∑ j₁ : Fin m, (m + j₁.val)) + (∑ j₁ : Fin m, (m + j₁.val)) := by
        rw [Fin.sum_univ_add]
        congr 1
        · apply Finset.sum_congr rfl; intro j₁ _; simp [base, j₁.isLt]
        · apply Finset.sum_congr rfl; intro j₁ _; simp [base]
      have hdiff : ∑ j₁ : Fin m, (m + j₁.val) = m * m + ∑ j₁ : Fin m, j₁.val := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      omega
    rwa [hsum_deg] at hprod
  · have hex : ∃ j : Fin (m + m), (σ j).val ∉ Set.Icc (base j) (base j + m) := by
      by_contra h; apply hall; intro j; exact not_not.mp (fun hj => h ⟨j, hj⟩)
    obtain ⟨j₀, hj₀⟩ := hex
    have hzero : (f₀.sylvester f₁ m m) (σ j₀) j₀ = 0 := by
      by_cases hj : j₀.val < m
      · let j₁ : Fin m := ⟨j₀.val, hj⟩
        have hj_eq : j₀ = Fin.castAdd m j₁ := Fin.ext rfl
        have hbase : base j₀ = j₁.val := by simp [base, hj, j₁]
        have hnot : (σ j₀).val ∉ Set.Icc j₁.val (j₁.val + m) := by rwa [← hbase]
        rw [hj_eq, hsylv_left, ← hj_eq]; simp [hnot]
      · let j₁ : Fin m := ⟨j₀.val - m, by omega⟩
        have hj_eq : j₀ = Fin.natAdd m j₁ := Fin.ext (by dsimp [Fin.natAdd, j₁]; omega)
        have hbase : base j₀ = j₁.val := by simp [base, hj, j₁]
        have hnot : (σ j₀).val ∉ Set.Icc j₁.val (j₁.val + m) := by rwa [← hbase]
        rw [hj_eq, hsylv_right, ← hj_eq]; simp [hnot]
    have hprod0 : (∏ i : Fin (m + m), (f₀.sylvester f₁ m m) (σ i) i) = 0 :=
      Finset.prod_eq_zero (mem_univ j₀) hzero
    rw [hprod0]
    exact isHomogeneous_zero _ _ _

lemma bezout_coprime_homog {K : Type*} [Field K] [IsAlgClosed K]
    {Q₀ Q₁ : MvPolynomial (Fin 3) K} {m : ℕ} (_hm : 1 ≤ m)
    (hQ0h : Q₀.IsHomogeneous m) (hQ1h : Q₁.IsHomogeneous m)
    (hQ0irr : Irreducible Q₀) (hQ1irr : Irreducible Q₁) (hnassoc : ¬ Associated Q₀ Q₁)
    {Z : Finset (Fin 3 → K)} (hZnz : ∀ u ∈ Z, u ≠ 0)
    (hZnp : ∀ u ∈ Z, ∀ v ∈ Z, u ≠ v → cross3 u v ≠ 0)
    (hZ0 : ∀ u ∈ Z, eval u Q₀ = 0) (hZ1 : ∀ u ∈ Z, eval u Q₁ = 0) :
    Z.card ≤ m * m := by
  classical
  let aff0 : MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 2) K :=
    MvPolynomial.eval₂Hom C (fun i => match i with | 0 => 1 | 1 => X 0 | 2 => X 1)
  have hev_aff0 : ∀ (Q : MvPolynomial (Fin 3) K) (w : Fin 2 → K),
      eval w (aff0 Q) = eval (embed w) Q := by
    intro Q w
    induction Q using MvPolynomial.induction_on with
    | C c => simp [aff0]
    | add a b ha hb => simp [map_add, ha, hb]
    | mul_X a i ha =>
      fin_cases i <;> (rw [map_mul, map_mul, map_mul, ha]; simp [aff0, embed])
  have haff0_ne : ∀ {Q : MvPolynomial (Fin 3) K}, Q.IsHomogeneous m → Q ≠ 0 → aff0 Q ≠ 0 := by
    intro Q hQh hQ0 h0
    obtain ⟨n, hn⟩ := MvPolynomial.support_nonempty.mpr hQ0
    let n' : Fin 2 →₀ ℕ := Finsupp.single 0 (n 1) + Finsupp.single 1 (n 2)
    have hc := congrArg (fun f : MvPolynomial (Fin 2) K => f.coeff n') h0
    rw [MvPolynomial.coeff_zero, Q.as_sum, map_sum, MvPolynomial.coeff_sum] at hc
    rw [Finset.sum_eq_single n] at hc
    · unfold aff0 at hc
      rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp),
        Fin.prod_univ_three, one_pow, one_mul] at hc
      have hmon : C (Q.coeff n) * (X (0 : Fin 2) ^ n 1 * X 1 ^ n 2) = monomial n' (Q.coeff n) := by
        rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
        simp [n']
      rw [hmon, MvPolynomial.coeff_monomial] at hc
      simp only [ite_true] at hc
      exact MvPolynomial.mem_support_iff.mp hn hc
    · intro s hs hne
      unfold aff0
      rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp),
        Fin.prod_univ_three, one_pow, one_mul]
      let s' : Fin 2 →₀ ℕ := Finsupp.single 0 (s 1) + Finsupp.single 1 (s 2)
      have hmon : C (Q.coeff s) * (X (0 : Fin 2) ^ s 1 * X 1 ^ s 2) = monomial s' (Q.coeff s) := by
        rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
        simp [s']
      rw [hmon, MvPolynomial.coeff_monomial]
      split_ifs with heq
      · exfalso; apply hne
        have h1 : s 1 = n 1 := by have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) heq; simpa [s', n'] using this
        have h2 : s 2 = n 2 := by have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) heq; simpa [s', n'] using this
        have hds := isHomogeneous_sum_eq hQh hs
        have hdn := isHomogeneous_sum_eq hQh hn
        rw [Fin.sum_univ_three] at hds hdn
        ext i; fin_cases i
        · change s 0 = n 0; omega
        · exact h1
        · exact h2
      · rfl
    · intro hnot; exact absurd hn hnot
  let G : MvPolynomial (Fin 2) K :=
    aff0 Q₀ * aff0 Q₁ *
      (∏ u ∈ Z, if u 0 ≠ 0 then X (0 : Fin 2) - C (u 1 / u 0) else 1) *
      (∏ u ∈ Z, ∏ v ∈ Z.erase u,
        (C (cross3 u v 0) + C (cross3 u v 1) * X 0 + C (cross3 u v 2) * X 1))
  have hG_ne : G ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (haff0_ne hQ0h hQ0irr.ne_zero)
      (haff0_ne hQ1h hQ1irr.ne_zero)) ?_) ?_
    · apply Finset.prod_ne_zero_iff.mpr
      intro u _
      split_ifs
      · intro h0
        have h1 := congrArg (eval (fun _ : Fin 2 => u 1 / u 0 + 1)) h0
        simp at h1
      · exact one_ne_zero
    · apply Finset.prod_ne_zero_iff.mpr
      intro u hu
      apply Finset.prod_ne_zero_iff.mpr
      intro v hv
      have hne : u ≠ v := (mem_erase.mp hv).1.symm
      have hcr : cross3 u v ≠ 0 := hZnp u hu v (mem_erase.mp hv).2 hne
      intro h0
      have e0 := congrArg (eval (fun _ : Fin 2 => (0 : K))) h0
      have e1 := congrArg (eval (fun i : Fin 2 => match i with | 0 => (1 : K) | 1 => 0)) h0
      have e2 := congrArg (eval (fun i : Fin 2 => match i with | 0 => (0 : K) | 1 => 1)) h0
      simp only [map_add, map_mul, eval_C, eval_X, map_zero, mul_zero, mul_one, add_zero] at e0 e1 e2
      apply hcr; ext i; fin_cases i
      · exact e0
      · change cross3 u v 1 = 0; linear_combination e1 - e0
      · change cross3 u v 2 = 0; linear_combination e2 - e0
  obtain ⟨w, hw⟩ := exists_eval_ne_zero_mv2 hG_ne
  set α := w 0
  set β := w 1
  dsimp only [G] at hw
  simp only [map_mul, map_prod] at hw
  have hQ0w : eval (embed w) Q₀ ≠ 0 := by
    rw [← hev_aff0]; exact left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hw))
  have hQ1w : eval (embed w) Q₁ ≠ 0 := by
    rw [← hev_aff0]; exact right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hw))
  have hZ_u0 : ∀ u ∈ Z, u 0 ≠ 0 → α - u 1 / u 0 ≠ 0 := by
    intro u hu hu0
    have hpr := right_ne_zero_of_mul (left_ne_zero_of_mul hw)
    have hfac := (Finset.prod_ne_zero_iff.mp hpr) u hu
    simp [hu0] at hfac
    exact hfac
  have hZ_det : ∀ u ∈ Z, ∀ v ∈ Z, u ≠ v →
      (u 1 - α * u 0) * (v 2 - β * v 0) - (u 2 - β * u 0) * (v 1 - α * v 0) ≠ 0 := by
    intro u hu v hv huv
    have hpr := right_ne_zero_of_mul hw
    have hfac := (Finset.prod_ne_zero_iff.mp ((Finset.prod_ne_zero_iff.mp hpr) u hu)) v
      (mem_erase.mpr ⟨huv.symm, hv⟩)
    simp only [map_add, map_mul, eval_C, eval_X] at hfac
    have hid : (u 1 - α * u 0) * (v 2 - β * v 0) - (u 2 - β * u 0) * (v 1 - α * v 0) =
        cross3 u v 0 + cross3 u v 1 * w 0 + cross3 u v 2 * w 1 := by
      unfold cross3; dsimp only [α, β]; ring
    rw [hid]; exact hfac
  -- Define shear automorphism X 0 ↦ X 0, X 1 ↦ X 1 + C α * X 0, X 2 ↦ X 2 + C β * X 0
  let shear : K → K → MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 3) K := fun a b =>
    MvPolynomial.eval₂Hom C (fun i => match i with
      | 0 => X 0 | 1 => X 1 + C a * X 0 | 2 => X 2 + C b * X 0)
  have hshear_inv : ∀ (a b : K) (P : MvPolynomial (Fin 3) K), shear (-a) (-b) (shear a b P) = P := by
    intro a b P
    induction P using MvPolynomial.induction_on with
    | C c => simp [shear]
    | add p q hp hq => simp [map_add, hp, hq]
    | mul_X p i hp =>
      fin_cases i
      · change shear (-a) (-b) (shear a b (p * X 0)) = p * X 0
        rw [map_mul, map_mul, hp]; simp [shear]
      · change shear (-a) (-b) (shear a b (p * X 1)) = p * X 1
        rw [map_mul, map_mul, hp]; simp only [shear, MvPolynomial.eval₂Hom_X', map_add, map_mul,
          MvPolynomial.eval₂Hom_C, map_neg]; ring
      · change shear (-a) (-b) (shear a b (p * X 2)) = p * X 2
        rw [map_mul, map_mul, hp]; simp only [shear, MvPolynomial.eval₂Hom_X', map_add, map_mul,
          MvPolynomial.eval₂Hom_C, map_neg]; ring
  have hshear_eval : ∀ (a b : K) (P : MvPolynomial (Fin 3) K) (v : Fin 3 → K),
      eval v (shear a b P) =
        eval (fun i => match i with | 0 => v 0 | 1 => v 1 + a * v 0 | 2 => v 2 + b * v 0) P := by
    intro a b P v
    induction P using MvPolynomial.induction_on with
    | C c => simp [shear]
    | add p q hp hq => simp [map_add, hp, hq]
    | mul_X p i hp =>
      fin_cases i <;> (rw [map_mul, map_mul, hp]; simp [shear])
  have hshear_hom : ∀ (a b : K) {P : MvPolynomial (Fin 3) K},
      P.IsHomogeneous m → (shear a b P).IsHomogeneous m := by
    intro a b P hPh
    rw [P.as_sum, map_sum]
    apply IsHomogeneous.sum
    intro s hs
    unfold shear
    rw [MvPolynomial.eval₂Hom_monomial]
    apply IsHomogeneous.C_mul
    rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
    have h1 : ∀ i : Fin 3, ((match i with
        | 0 => X (0 : Fin 3) | 1 => X 1 + C a * X 0 | 2 => X 2 + C b * X 0 :
          MvPolynomial (Fin 3) K) ^ s i).IsHomogeneous (s i) := by
      intro i; fin_cases i
      · simpa using (isHomogeneous_X K (0 : Fin 3)).pow (s 0)
      · have hlin : (X (1 : Fin 3) + C a * X 0 : MvPolynomial (Fin 3) K).IsHomogeneous 1 :=
          (isHomogeneous_X K 1).add ((isHomogeneous_X K 0).C_mul a)
        simpa using hlin.pow (s 1)
      · have hlin : (X (2 : Fin 3) + C b * X 0 : MvPolynomial (Fin 3) K).IsHomogeneous 1 :=
          (isHomogeneous_X K 2).add ((isHomogeneous_X K 0).C_mul b)
        simpa using hlin.pow (s 2)
    have hpr := IsHomogeneous.prod univ _ (fun i => s i) (fun i _ => h1 i)
    rwa [isHomogeneous_sum_eq hPh hs] at hpr
  let c₀ := eval (embed w) Q₀
  let c₁ := eval (embed w) Q₁
  let F₀ : MvPolynomial (Fin 3) K := C c₀⁻¹ * shear α β Q₀
  let F₁ : MvPolynomial (Fin 3) K := C c₁⁻¹ * shear α β Q₁
  have hF0h : F₀.IsHomogeneous m := (hshear_hom α β hQ0h).C_mul _
  have hF1h : F₁.IsHomogeneous m := (hshear_hom α β hQ1h).C_mul _
  have hF0_e0 : eval (fun i : Fin 3 => match i with | 0 => (1 : K) | 1 => 0 | 2 => 0) F₀ = 1 := by
    dsimp only [F₀]; rw [map_mul, eval_C, hshear_eval]
    have harg : (fun i : Fin 3 => match i with
        | 0 => (1 : K) | 1 => 0 + α * 1 | 2 => 0 + β * 1) = embed w := by
      ext i; fin_cases i <;> simp [embed, α, β]
    rw [harg]; exact inv_mul_cancel₀ hQ0w
  have hF1_e0 : eval (fun i : Fin 3 => match i with | 0 => (1 : K) | 1 => 0 | 2 => 0) F₁ = 1 := by
    dsimp only [F₁]; rw [map_mul, eval_C, hshear_eval]
    have harg : (fun i : Fin 3 => match i with
        | 0 => (1 : K) | 1 => 0 + α * 1 | 2 => 0 + β * 1) = embed w := by
      ext i; fin_cases i <;> simp [embed, α, β]
    rw [harg]; exact inv_mul_cancel₀ hQ1w
  have hF0_irr : Irreducible F₀ := by
    have hsh_irr : Irreducible (shear α β Q₀) := by
      have hnotu : ¬ IsUnit (shear α β Q₀) := fun hu =>
        hQ0irr.not_isUnit (by have := hu.map (shear (-α) (-β)); rwa [hshear_inv] at this)
      refine ⟨hnotu, ?_⟩
      intro A B hAB
      have hback : Q₀ = shear (-α) (-β) A * shear (-α) (-β) B := by
        have := congrArg (shear (-α) (-β)) hAB; rwa [hshear_inv, map_mul] at this
      rcases hQ0irr.isUnit_or_isUnit hback with hA | hB
      · left; have := hA.map (shear α β)
        have hinva : shear α β (shear (-α) (-β) A) = A := by
          have := hshear_inv (-α) (-β) A; rwa [neg_neg, neg_neg] at this
        rwa [hinva] at this
      · right; have := hB.map (shear α β)
        have hinvb : shear α β (shear (-α) (-β) B) = B := by
          have := hshear_inv (-α) (-β) B; rwa [neg_neg, neg_neg] at this
        rwa [hinvb] at this
    have hu : IsUnit (C c₀⁻¹ : MvPolynomial (Fin 3) K) := (IsUnit.mk0 c₀⁻¹ (inv_ne_zero hQ0w)).map C
    exact (associated_unit_mul_left (shear α β Q₀) (C c₀⁻¹) hu).irreducible_iff.mpr hsh_irr
  have hF01_ne : F₀ ≠ F₁ := by
    intro heq
    apply hnassoc
    have hback := congrArg (shear (-α) (-β)) heq
    dsimp only [F₀, F₁] at hback
    rw [map_mul, map_mul, hshear_inv, hshear_inv] at hback
    have hC0 : shear (-α) (-β) (C c₀⁻¹) = C c₀⁻¹ := by simp [shear]
    have hC1 : shear (-α) (-β) (C c₁⁻¹) = C c₁⁻¹ := by simp [shear]
    rw [hC0, hC1] at hback
    have hQ1eq : Q₀ * C (c₀⁻¹ * c₁) = Q₁ := by
      have h1 := congrArg (C c₁ * ·) hback
      have hinv : C c₁ * C c₁⁻¹ = (1 : MvPolynomial (Fin 3) K) := by
        rw [← map_mul, mul_inv_cancel₀ hQ1w, map_one]
      calc Q₀ * C (c₀⁻¹ * c₁) = C c₁ * (C c₀⁻¹ * Q₀) := by rw [map_mul]; ring
        _ = C c₁ * (C c₁⁻¹ * Q₁) := h1
        _ = (C c₁ * C c₁⁻¹) * Q₁ := by ring
        _ = Q₁ := by rw [hinv, one_mul]
    have hu : IsUnit (C (c₀⁻¹ * c₁) : MvPolynomial (Fin 3) K) :=
      (IsUnit.mk0 (c₀⁻¹ * c₁) (mul_ne_zero (inv_ne_zero hQ0w) hQ1w)).map C
    exact ⟨hu.unit, hQ1eq⟩
  -- Convert F₀, F₁ to monic polynomials f₀, f₁ ∈ Polynomial (MvPolynomial (Fin 2) K) of degree m
  let f₀ : Polynomial (MvPolynomial (Fin 2) K) := MvPolynomial.finSuccEquiv K 2 F₀
  let f₁ : Polynomial (MvPolynomial (Fin 2) K) := MvPolynomial.finSuccEquiv K 2 F₁
  have hcoeff_hom : ∀ {F : MvPolynomial (Fin 3) K}, F.IsHomogeneous m →
      (∀ k, k ≤ m → ((MvPolynomial.finSuccEquiv K 2 F).coeff k).IsHomogeneous (m - k)) ∧
      (∀ k, m < k → (MvPolynomial.finSuccEquiv K 2 F).coeff k = 0) := by
    intro F hFh
    refine ⟨?_, ?_⟩
    · intro k hk s hs
      rw [MvPolynomial.finSuccEquiv_coeff_coeff] at hs
      have hdeg := hFh hs
      rw [weight_one_eq_degree, Finsupp.degree_apply] at hdeg
      have hsum : ∑ i ∈ (Finsupp.cons k s).support, (Finsupp.cons k s) i =
          ∑ i : Fin 3, (Finsupp.cons k s) i :=
        Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => Finsupp.notMem_support_iff.mp hi)
      rw [hsum, Fin.sum_univ_three] at hdeg
      have h0 : (Finsupp.cons k s) 0 = k := Finsupp.cons_zero k s
      have h1 : (Finsupp.cons k s) 1 = s 0 := Finsupp.cons_succ (0 : Fin 2) k s
      have h2 : (Finsupp.cons k s) 2 = s 1 := Finsupp.cons_succ (1 : Fin 2) k s
      rw [h0, h1, h2] at hdeg
      rw [weight_one_eq_degree, Finsupp.degree_apply]
      have hsum2 : ∑ i ∈ s.support, s i = ∑ i : Fin 2, s i :=
        Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => Finsupp.notMem_support_iff.mp hi)
      rw [hsum2, Fin.sum_univ_two]
      omega
    · intro k hk
      ext s
      rw [MvPolynomial.finSuccEquiv_coeff_coeff, MvPolynomial.coeff_zero]
      by_contra hne
      have hdeg := hFh hne
      rw [weight_one_eq_degree, Finsupp.degree_apply] at hdeg
      have hsum : ∑ i ∈ (Finsupp.cons k s).support, (Finsupp.cons k s) i =
          ∑ i : Fin 3, (Finsupp.cons k s) i :=
        Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => Finsupp.notMem_support_iff.mp hi)
      rw [hsum, Fin.sum_univ_three] at hdeg
      have h0 : (Finsupp.cons k s) 0 = k := Finsupp.cons_zero k s
      rw [h0] at hdeg
      omega
  have hcoeff_m : ∀ {F : MvPolynomial (Fin 3) K}, F.IsHomogeneous m →
      eval (fun i : Fin 3 => match i with | 0 => (1 : K) | 1 => 0 | 2 => 0) F = 1 →
      (MvPolynomial.finSuccEquiv K 2 F).coeff m = 1 := by
    intro F hFh hev1
    have hhom0 : ((MvPolynomial.finSuccEquiv K 2 F).coeff m).IsHomogeneous 0 := by
      have := (hcoeff_hom hFh).1 m (le_refl m); rwa [Nat.sub_self] at this
    rw [isHomogeneous_zero_eq_C hhom0]
    have hc0 : ((MvPolynomial.finSuccEquiv K 2 F).coeff m).coeff 0 = 1 := by
      rw [MvPolynomial.finSuccEquiv_coeff_coeff]
      have hcons : Finsupp.cons m (0 : Fin 2 →₀ ℕ) = Finsupp.single (0 : Fin 3) m := by
        ext i; fin_cases i
        · simp [Finsupp.cons_zero]
        · change (Finsupp.cons m (0 : Fin 2 →₀ ℕ)) (Fin.succ 0) = (Finsupp.single (0 : Fin 3) m) 1
          rw [Finsupp.cons_succ]; simp
        · change (Finsupp.cons m (0 : Fin 2 →₀ ℕ)) (Fin.succ 1) = (Finsupp.single (0 : Fin 3) m) 2
          rw [Finsupp.cons_succ]; simp
      rw [hcons]
      have hev_eq : eval (fun i : Fin 3 => match i with | 0 => (1 : K) | 1 => 0 | 2 => 0) F =
          F.coeff (Finsupp.single 0 m) := by
        conv_lhs => rw [F.as_sum]
        rw [map_sum]
        by_cases hmem : Finsupp.single (0 : Fin 3) m ∈ F.support
        · rw [Finset.sum_eq_single (Finsupp.single 0 m)]
          · rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_three]
            simp
          · intro s hs hne
            rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_three]
            have hdeg := isHomogeneous_sum_eq hFh hs
            rw [Fin.sum_univ_three] at hdeg
            by_cases hs1 : s 1 = 0
            · have hs2 : s 2 ≠ 0 := by
                intro h2; apply hne; ext i; fin_cases i <;> simp <;> omega
              simp [zero_pow hs2]
            · simp [zero_pow hs1]
          · intro hnot; exact absurd hmem hnot
        · rw [MvPolynomial.notMem_support_iff.mp hmem]
          apply Finset.sum_eq_zero
          intro s hs
          rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_three]
          have hdeg := isHomogeneous_sum_eq hFh hs
          rw [Fin.sum_univ_three] at hdeg
          by_cases hs1 : s 1 = 0
          · have hs2 : s 2 ≠ 0 := by
              intro h2; apply hmem
              have : s = Finsupp.single (0 : Fin 3) m := by ext i; fin_cases i <;> simp <;> omega
              exact this ▸ hs
            simp [zero_pow hs2]
          · simp [zero_pow hs1]
      rw [← hev_eq]; exact hev1
    rw [hc0, map_one]
  have hf0_nd : f₀.natDegree = m := by
    have hle : f₀.natDegree ≤ m :=
      Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun k hk => (hcoeff_hom hF0h).2 k hk)
    have hge : m ≤ f₀.natDegree :=
      Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff_m hF0h hF0_e0]; exact one_ne_zero)
    omega
  have hf1_nd : f₁.natDegree = m := by
    have hle : f₁.natDegree ≤ m :=
      Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun k hk => (hcoeff_hom hF1h).2 k hk)
    have hge : m ≤ f₁.natDegree :=
      Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff_m hF1h hF1_e0]; exact one_ne_zero)
    omega
  have hf0_mon : f₀.Monic := by rw [Polynomial.Monic, Polynomial.leadingCoeff, hf0_nd]; exact hcoeff_m hF0h hF0_e0
  have hf1_mon : f₁.Monic := by rw [Polynomial.Monic, Polynomial.leadingCoeff, hf1_nd]; exact hcoeff_m hF1h hF1_e0
  -- Resultant in MvPolynomial (Fin 2) K is nonzero, homogeneous of degree m^2, vanishes on projected Z
  let Res : MvPolynomial (Fin 2) K := Polynomial.resultant f₀ f₁ m m
  have hRes_hom : Res.IsHomogeneous (m * m) :=
    resultant_isHomogeneous (hcoeff_hom hF0h).1 (hcoeff_hom hF1h).1
  have hRes_ne : Res ≠ 0 := by
    let : GCDMonoid (MvPolynomial (Fin 2) K) :=
      UniqueFactorizationMonoid.toGCDMonoid (MvPolynomial (Fin 2) K)
    let FracR := FractionRing (MvPolynomial (Fin 2) K)
    let ιF := algebraMap (MvPolynomial (Fin 2) K) FracR
    have hf0_irr : Irreducible f₀ := by
      let e := (MvPolynomial.finSuccEquiv K 2).toRingEquiv
      have hnotu : ¬ IsUnit (e F₀) := fun hu => hF0_irr.not_isUnit (by
        have := hu.map e.symm.toRingHom; simpa using this)
      refine ⟨hnotu, ?_⟩
      intro A B hAB
      have hback : F₀ = e.symm A * e.symm B := by
        have := congrArg e.symm hAB; simpa [e, f₀, map_mul] using this
      rcases hF0_irr.isUnit_or_isUnit hback with hA | hB
      · left; have := hA.map e.toRingHom; simpa using this
      · right; have := hB.map e.toRingHom; simpa using this
    have hf0_map_irr : Irreducible (f₀.map ιF) :=
      (Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map hf0_mon.isPrimitive).mp hf0_irr
    have hf0_map_mon : (f₀.map ιF).Monic := hf0_mon.map ιF
    have hf1_map_mon : (f₁.map ιF).Monic := hf1_mon.map ιF
    have hnot_dvd : ¬ (f₀.map ιF ∣ f₁.map ιF) := by
      rintro ⟨q, hq⟩
      have hq0 : q ≠ 0 := by intro h; rw [h, mul_zero] at hq; exact hf1_map_mon.ne_zero hq
      have hnd_eq : (f₁.map ιF).natDegree = (f₀.map ιF).natDegree + q.natDegree := by
        rw [hq, Polynomial.natDegree_mul hf0_map_mon.ne_zero hq0]
      rw [hf0_mon.natDegree_map, hf1_mon.natDegree_map, hf0_nd, hf1_nd] at hnd_eq
      have hq_nd : q.natDegree = 0 := by omega
      have hq_lc : q.leadingCoeff = 1 := by
        have hlc := congrArg Polynomial.leadingCoeff hq
        rw [Polynomial.leadingCoeff_mul, hf0_map_mon.leadingCoeff, hf1_map_mon.leadingCoeff, one_mul] at hlc
        exact hlc.symm
      have hq1 : q = 1 := by
        rw [Polynomial.eq_C_of_natDegree_eq_zero hq_nd]
        have : q.coeff 0 = 1 := by rw [← hq_nd]; exact hq_lc
        rw [this, map_one]
      rw [hq1, mul_one] at hq
      have hf01 : f₀ = f₁ := Polynomial.map_injective ιF (IsFractionRing.injective _ _) hq.symm
      exact hF01_ne ((MvPolynomial.finSuccEquiv K 2).injective hf01)
    have hcop : IsCoprime (f₀.map ιF) (f₁.map ιF) :=
      hf0_map_irr.coprime_iff_not_dvd.mpr hnot_dvd
    intro hRes0
    have hmap0 : (f₀.map ιF).resultant (f₁.map ιF) m m = 0 := by
      rw [Polynomial.resultant_map_map]
      change ιF Res = 0
      rw [hRes0, map_zero]
    have hnd0 : (f₀.map ιF).natDegree = m := by rw [hf0_mon.natDegree_map, hf0_nd]
    have hnd1 : (f₁.map ιF).natDegree = m := by rw [hf1_mon.natDegree_map, hf1_nd]
    have hmap0' : (f₀.map ιF).resultant (f₁.map ιF) = 0 := by
      change (f₀.map ιF).resultant (f₁.map ιF) (f₀.map ιF).natDegree (f₁.map ιF).natDegree = 0
      rw [hnd0, hnd1]; exact hmap0
    exact (Polynomial.resultant_eq_zero_iff.mp hmap0').2 hcop
  -- Map Z into Fin 2 → K via u ↦ (u 1 - α * u 0, u 2 - β * u 0)
  let proj : (Fin 3 → K) → Fin 2 → K := fun u j => match j with
    | 0 => u 1 - α * u 0 | 1 => u 2 - β * u 0
  have hproj_inj : Set.InjOn proj Z := by
    intro u hu v hv heq
    by_contra hne
    apply hZ_det u hu v hv hne
    have h0 : u 1 - α * u 0 = v 1 - α * v 0 := congrFun heq 0
    have h1 : u 2 - β * u 0 = v 2 - β * v 0 := congrFun heq 1
    rw [h0, h1]; ring
  let S := Z.image proj
  have hScard : S.card = Z.card := card_image_of_injOn hproj_inj
  by_contra hgt
  have hge : m * m + 1 ≤ S.card := by omega
  apply hRes_ne
  apply homog2_eq_zero_of_roots hRes_hom hge
  · intro v hv
    rcases mem_image.mp hv with ⟨u, hu, rfl⟩
    intro h0
    have h1 : u 1 - α * u 0 = 0 := congrFun h0 0
    have h2 : u 2 - β * u 0 = 0 := congrFun h0 1
    by_cases hu0 : u 0 = 0
    · apply hZnz u hu; ext i; fin_cases i
      · exact hu0
      · change u 1 = 0; linear_combination h1 + α * hu0
      · change u 2 = 0; linear_combination h2 + β * hu0
    · apply hZ_u0 u hu hu0
      apply mul_left_cancel₀ hu0
      calc u 0 * (α - u 1 / u 0) = α * u 0 - u 0 * (u 1 / u 0) := by ring
        _ = α * u 0 - u 1 := by rw [mul_div_cancel₀ _ hu0]
        _ = 0 := by linear_combination -h1
        _ = u 0 * 0 := (mul_zero _).symm
  · intro v hv w' hw' hvw
    rcases mem_image.mp hv with ⟨u₁, hu₁, rfl⟩
    rcases mem_image.mp hw' with ⟨u₂, hu₂, rfl⟩
    exact hZ_det u₁ hu₁ u₂ hu₂ (fun h => hvw (congrArg proj h))
  · intro v hv
    rcases mem_image.mp hv with ⟨u, hu, rfl⟩
    dsimp only [Res]
    rw [← Polynomial.resultant_map_map]
    have hnd0 : (f₀.map (eval (proj u))).natDegree = m := by rw [hf0_mon.natDegree_map, hf0_nd]
    have hnd1 : (f₁.map (eval (proj u))).natDegree = m := by rw [hf1_mon.natDegree_map, hf1_nd]
    suffices hres0 : (f₀.map (eval (proj u))).resultant (f₁.map (eval (proj u))) = 0 by
      change (f₀.map (eval (proj u))).resultant (f₁.map (eval (proj u)))
        (f₀.map (eval (proj u))).natDegree (f₁.map (eval (proj u))).natDegree = 0 at hres0
      rwa [hnd0, hnd1] at hres0
    rw [Polynomial.resultant_eq_zero_iff]
    refine ⟨Or.inl (hf0_mon.map (eval (proj u))).ne_zero, ?_⟩
    let u' : Fin 3 → K := Fin.cons (u 0) (proj u)
    have harg : (fun i : Fin 3 => match i with
        | 0 => u' 0 | 1 => u' 1 + α * u' 0 | 2 => u' 2 + β * u' 0) = u := by
      ext i; fin_cases i
      · rfl
      · change (u 1 - α * u 0) + α * u 0 = u 1; ring
      · change (u 2 - β * u 0) + β * u 0 = u 2; ring
    have hrt0 : (f₀.map (eval (proj u))).IsRoot (u 0) := by
      rw [Polynomial.IsRoot.def, ← MvPolynomial.eval_eq_eval_mv_eval']
      change eval u' F₀ = 0
      dsimp only [F₀]; rw [map_mul, eval_C, hshear_eval, harg, hZ0 u hu, mul_zero]
    have hrt1 : (f₁.map (eval (proj u))).IsRoot (u 0) := by
      rw [Polynomial.IsRoot.def, ← MvPolynomial.eval_eq_eval_mv_eval']
      change eval u' F₁ = 0
      dsimp only [F₁]; rw [map_mul, eval_C, hshear_eval, harg, hZ1 u hu, mul_zero]
    intro hcop
    rcases hcop with ⟨a, b, hab⟩
    have hev := congrArg (Polynomial.eval (u 0)) hab
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
      Polynomial.IsRoot.def.mp hrt0, Polynomial.IsRoot.def.mp hrt1,
      mul_zero, mul_zero, add_zero, Polynomial.eval_one] at hev
    exact zero_ne_one hev

lemma frob_fixed_iff (x : AlgebraicClosure (ZMod p)) :
    x ^ p = x ↔ ∃ c : ZMod p, algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) c = x := by
  classical
  let Kbar := AlgebraicClosure (ZMod p)
  let ι : ZMod p →+* Kbar := algebraMap (ZMod p) Kbar
  constructor
  · intro hxp
    let poly : Polynomial Kbar := Polynomial.X ^ p - Polynomial.X
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hnd : poly.natDegree = p := by
      dsimp only [poly]
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
      · exact Polynomial.natDegree_X_pow p
      · rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]; omega
    have hpoly0 : poly ≠ 0 := by intro h; rw [h, Polynomial.natDegree_zero] at hnd; omega
    let R : Finset Kbar := (univ : Finset (ZMod p)).image ι
    have hR_card : R.card = p := by
      rw [card_image_of_injective _ ι.injective, card_univ, ZMod.card]
    have hR_sub : R.val ⊆ poly.roots := by
      intro y hy
      rcases mem_image.mp hy with ⟨c, _, rfl⟩
      rw [Polynomial.mem_roots hpoly0, Polynomial.IsRoot.def]
      dsimp only [poly]
      rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, ← map_pow, ZMod.pow_card, sub_self]
    have hR_le : R.val ≤ poly.roots := (Multiset.le_iff_subset R.nodup).mpr hR_sub
    have hroots_le : poly.roots.card ≤ R.val.card := by
      calc poly.roots.card ≤ poly.natDegree := Polynomial.card_roots' poly
        _ = p := hnd
        _ = R.val.card := hR_card.symm
    have heq : R.val = poly.roots := Multiset.eq_of_le_of_card_le hR_le hroots_le
    have hx_root : x ∈ poly.roots := by
      rw [Polynomial.mem_roots hpoly0, Polynomial.IsRoot.def]
      dsimp only [poly]
      rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hxp, sub_self]
    rw [← heq] at hx_root
    rcases mem_image.mp hx_root with ⟨c, _, hc⟩
    exact ⟨c, hc⟩
  · rintro ⟨c, rfl⟩
    rw [← map_pow, ZMod.pow_card]

lemma frob_iter_finite_period {Q : MvPolynomial (Fin 3) (AlgebraicClosure (ZMod p))} (_hQ : Q ≠ 0) :
    ∃ r : ℕ, 1 ≤ r ∧ (MvPolynomial.map (frobenius (AlgebraicClosure (ZMod p)) p))^[r] Q = Q := by
  classical
  set Kbar := AlgebraicClosure (ZMod p)
  set ι : ZMod p →+* Kbar := algebraMap (ZMod p) Kbar
  let frob : Kbar →+* Kbar := frobenius Kbar p
  let Frob : MvPolynomial (Fin 3) Kbar →+* MvPolynomial (Fin 3) Kbar := MvPolynomial.map frob
  have hfrob_inj : Function.Injective frob := frobenius_inj Kbar p
  have hFrob_inj : Function.Injective Frob := MvPolynomial.map_injective frob hfrob_inj
  have hfrob_iter : ∀ (k : ℕ) (P : MvPolynomial (Fin 3) Kbar) (m : Fin 3 →₀ ℕ),
      (Frob^[k] P).coeff m = frob^[k] (P.coeff m) := by
    intro k
    induction k with
    | zero => intro P m; rfl
    | succ k ih =>
      intro P m
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change (MvPolynomial.map frob (Frob^[k] P)).coeff m = frob (frob^[k] (P.coeff m))
      rw [MvPolynomial.coeff_map, ih]
  have hfrob_aeval : ∀ (μ : Polynomial (ZMod p)) (x : Kbar),
      Polynomial.aeval (frob x) μ = frob (Polynomial.aeval x μ) := by
    intro μ x
    induction μ using Polynomial.induction_on' with
    | add a b ha hb => simp [map_add, ha, hb]
    | monomial n c =>
      simp only [Polynomial.aeval_monomial, map_mul, map_pow]
      have hc : frob (ι c) = ι c := by
        change (ι c) ^ p = ι c; rw [← map_pow, ZMod.pow_card]
      rw [hc]
  -- Every coefficient c of Q has finite Frobenius orbit contained in ((minpoly (ZMod p) c).map ι).roots
  have horb : ∀ c : Kbar, ∃ S : Finset Kbar, ∀ k : ℕ, frob^[k] c ∈ S := by
    intro c
    have hint : IsIntegral (ZMod p) c :=
      ((AlgebraicClosure.isAlgebraic (ZMod p)).isAlgebraic c).isIntegral
    let μ := minpoly (ZMod p) c
    have hμ0 : μ ≠ 0 := minpoly.ne_zero hint
    have hμmap0 : μ.map ι ≠ 0 := Polynomial.map_ne_zero hμ0
    refine ⟨(μ.map ι).roots.toFinset, ?_⟩
    intro k
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hμmap0, Polynomial.IsRoot.def,
      Polynomial.eval_map, ← Polynomial.aeval_def]
    induction k with
    | zero => exact minpoly.aeval (ZMod p) c
    | succ k ih =>
      rw [Function.iterate_succ_apply', hfrob_aeval, ih, map_zero]
  let bigSet : Finset Kbar := Q.support.biUnion fun m => Classical.choose (horb (Q.coeff m))
  let Fspace : Finset (Q.support → Kbar) := Fintype.piFinset (fun _ => bigSet)
  let Φ : ℕ → (Q.support → Kbar) := fun k m => (Frob^[k] Q).coeff m.1
  have hΦ_mem : ∀ k : ℕ, Φ k ∈ Fspace := by
    intro k
    rw [Fintype.mem_piFinset]
    intro m
    dsimp only [Φ]
    rw [hfrob_iter]
    exact mem_biUnion.mpr ⟨m.1, m.2, Classical.choose_spec (horb (Q.coeff m.1)) k⟩
  have hlt : Fspace.card < (Finset.range (Fspace.card + 1)).card := by rw [Finset.card_range]; omega
  obtain ⟨i, hi, j, hj, hij, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt (fun k _ => hΦ_mem k)
  have hPQ : ∀ a b : ℕ, Φ a = Φ b → Frob^[a] Q = Frob^[b] Q := by
    intro a b hab
    ext m
    by_cases hm : m ∈ Q.support
    · exact congrFun hab ⟨m, hm⟩
    · have h0 : Q.coeff m = 0 := MvPolynomial.notMem_support_iff.mp hm
      have hf0 : ∀ k : ℕ, frob^[k] (0 : Kbar) = 0 := by
        intro k; induction k with
        | zero => rfl
        | succ k ih => rw [Function.iterate_succ_apply', ih, map_zero]
      rw [hfrob_iter, hfrob_iter, h0, hf0, hf0]
  have heqQ : Frob^[i] Q = Frob^[j] Q := hPQ i j heq
  rcases lt_or_gt_of_ne hij with hlt' | hgt'
  · refine ⟨j - i, by omega, ?_⟩
    have hiter : Frob^[i] (Frob^[j - i] Q) = Frob^[i] Q := by
      rw [← Function.iterate_add_apply, show i + (j - i) = j by omega, heqQ]
    exact (hFrob_inj.iterate i) hiter
  · refine ⟨i - j, by omega, ?_⟩
    have hiter : Frob^[j] (Frob^[i - j] Q) = Frob^[j] Q := by
      rw [← Function.iterate_add_apply, show j + (i - j) = i by omega, heqQ.symm]
    exact (hFrob_inj.iterate j) hiter

lemma card_le_four_mul_t_of_not_irreducible_map {A E : Finset (Fin 2 → ZMod p)} (hp2 : p ≠ 2)
    (harc : ∀ s ⊆ A, s.card = 3 → ¬ Collinear (ZMod p) (s : Set (Fin 2 → ZMod p)))
    {e : Fin 2 → ZMod p} (he : e ∈ A) (hEA : E ⊆ A) (hE : E.card = 2 * (p + 2 - A.card) + 2)
    {P : MvPolynomial (Fin 3) (ZMod p)} {d : ℕ}
    (hPirr : Irreducible P) (hPh : P.IsHomogeneous d) (hd1 : 1 ≤ d)
    (hdt : d ≤ 2 * (p + 2 - A.card)) (hdvd : P ∣ segreEnv A E e)
    (hred : ¬ Irreducible (MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) P)) :
    A.card ≤ 4 * (p + 2 - A.card) := by
  classical
  set Kbar := AlgebraicClosure (ZMod p)
  set ι : ZMod p →+* Kbar := algebraMap (ZMod p) Kbar
  let frob : Kbar →+* Kbar := frobenius Kbar p
  let Frob : MvPolynomial (Fin 3) Kbar →+* MvPolynomial (Fin 3) Kbar := MvPolynomial.map frob
  have hfrob_inj : Function.Injective frob := frobenius_inj Kbar p
  have hFrob_inj : Function.Injective Frob := MvPolynomial.map_injective frob hfrob_inj
  have hfrob_surj : Function.Surjective frob := by
    intro a
    let poly : Polynomial Kbar := Polynomial.X ^ p - Polynomial.C a
    have hp2' : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hnd : poly.natDegree = p := by
      dsimp only [poly]; rw [Polynomial.natDegree_sub_C, Polynomial.natDegree_X_pow]
    have hpoly0 : poly ≠ 0 := by intro h; rw [h, Polynomial.natDegree_zero] at hnd; omega
    have hdeg : poly.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hpoly0, hnd]
      intro h0; have : p = 0 := by exact_mod_cast h0
      omega
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_root poly hdeg
    refine ⟨b, ?_⟩
    rw [Polynomial.IsRoot.def] at hb; dsimp only [poly] at hb
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hb
    exact sub_eq_zero.mp hb
  let eFrob : MvPolynomial (Fin 3) Kbar ≃+* MvPolynomial (Fin 3) Kbar :=
    MvPolynomial.mapEquiv (Fin 3) (RingEquiv.ofBijective frob ⟨hfrob_inj, hfrob_surj⟩)
  have hFrob_eq_eFrob : ∀ Q, Frob Q = eFrob Q := fun _ => rfl
  have hFrob_fixed_iff : ∀ Q : MvPolynomial (Fin 3) Kbar,
      Frob Q = Q ↔ ∃ Q0 : MvPolynomial (Fin 3) (ZMod p), MvPolynomial.map ι Q0 = Q := by
    intro Q
    constructor
    · intro hfix
      have hcoeff_fix : ∀ s : Fin 3 →₀ ℕ, ∃ c : ZMod p, ι c = Q.coeff s := by
        intro s
        rw [← frob_fixed_iff]
        have hc := congrArg (fun f : MvPolynomial (Fin 3) Kbar => f.coeff s) hfix
        change (MvPolynomial.map frob Q).coeff s = Q.coeff s at hc
        rwa [MvPolynomial.coeff_map] at hc
      let Q0 : MvPolynomial (Fin 3) (ZMod p) :=
        ∑ s ∈ Q.support, monomial s (Classical.choose (hcoeff_fix s))
      refine ⟨Q0, ?_⟩
      ext s
      rw [MvPolynomial.coeff_map]
      dsimp only [Q0]
      rw [MvPolynomial.coeff_sum]
      by_cases hs : s ∈ Q.support
      · rw [Finset.sum_eq_single s]
        · rw [MvPolynomial.coeff_monomial]; simp only [ite_true]
          exact Classical.choose_spec (hcoeff_fix s)
        · intro t _ hts; rw [MvPolynomial.coeff_monomial]; simp [hts]
        · intro hnot; exact absurd hs hnot
      · have h0 : Q.coeff s = 0 := MvPolynomial.notMem_support_iff.mp hs
        rw [h0]
        have hsum0 : (∑ t ∈ Q.support, (monomial t (Classical.choose (hcoeff_fix t))).coeff s) = 0 := by
          apply Finset.sum_eq_zero
          intro t ht
          rw [MvPolynomial.coeff_monomial]
          have hts : t ≠ s := fun h => hs (h ▸ ht)
          simp [hts]
        rw [hsum0, map_zero]
    · rintro ⟨Q0, rfl⟩
      ext s
      change (MvPolynomial.map frob (MvPolynomial.map ι Q0)).coeff s = (MvPolynomial.map ι Q0).coeff s
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map]
      change (ι (Q0.coeff s)) ^ p = ι (Q0.coeff s)
      rw [← map_pow, ZMod.pow_card]
  have hmap_dvd_iff : ∀ {A B : MvPolynomial (Fin 3) (ZMod p)}, A ≠ 0 →
      MvPolynomial.map ι A ∣ MvPolynomial.map ι B → A ∣ B := by
    intro A B hA0 ⟨Rbar, hRbar⟩
    have hFrob_fix : Frob Rbar = Rbar := by
      have h1 := congrArg Frob hRbar
      rw [map_mul, (hFrob_fixed_iff _).mpr ⟨B, rfl⟩, (hFrob_fixed_iff _).mpr ⟨A, rfl⟩] at h1
      have hAmap0 : MvPolynomial.map ι A ≠ 0 := fun h =>
        hA0 (MvPolynomial.map_injective ι ι.injective (h.trans (map_zero _).symm))
      exact mul_left_cancel₀ hAmap0 (h1.symm.trans hRbar)
    obtain ⟨R0, rfl⟩ := (hFrob_fixed_iff Rbar).mp hFrob_fix
    rw [← map_mul] at hRbar
    exact ⟨R0, MvPolynomial.map_injective ι ι.injective hRbar⟩
  -- Pick an irreducible homogeneous factor Q of Pbar = map ι P
  let Pbar := MvPolynomial.map ι P
  have hPbar0 : Pbar ≠ 0 := fun h =>
    hPirr.ne_zero (MvPolynomial.map_injective ι ι.injective (h.trans (map_zero _).symm))
  have hPbarh : Pbar.IsHomogeneous d := hPh.map ι
  obtain ⟨Qraw, m, hQraw_irr, hQraw_h, hm1, hQraw_dvd⟩ :=
    exists_irreducible_dvd_of_homog d hd1 hPbarh hPbar0
  -- Normalize Q₀ so that coeff s₀ Q₀ = 1
  obtain ⟨s₀, hs₀⟩ := MvPolynomial.support_nonempty.mpr hQraw_irr.ne_zero
  have hc0_ne : Qraw.coeff s₀ ≠ 0 := MvPolynomial.mem_support_iff.mp hs₀
  let Q₀ : MvPolynomial (Fin 3) Kbar := C (Qraw.coeff s₀)⁻¹ * Qraw
  have hQ0_assoc : Associated Qraw Q₀ :=
    (associated_unit_mul_left Qraw (C (Qraw.coeff s₀)⁻¹)
      ((IsUnit.mk0 _ (inv_ne_zero hc0_ne)).map C)).symm
  have hQ0_irr : Irreducible Q₀ := hQ0_assoc.irreducible_iff.mp hQraw_irr
  have hQ0_h : Q₀.IsHomogeneous m := hQraw_h.C_mul _
  have hQ0_dvd : Q₀ ∣ Pbar := dvd_trans hQ0_assoc.symm.dvd hQraw_dvd
  have hQ0_s0 : Q₀.coeff s₀ = 1 := by
    dsimp only [Q₀]; rw [MvPolynomial.coeff_C_mul, inv_mul_cancel₀ hc0_ne]
  have hm_lt : m < d := by
    rcases hQ0_dvd with ⟨R, hR⟩
    obtain ⟨_, hRh, hsum⟩ := isHomogeneous_of_dvd hPbarh hPbar0 hR.symm
    have hQd : Q₀.totalDegree = m := hQ0_h.totalDegree hQ0_irr.ne_zero
    by_contra hge
    have hRd0 : R.totalDegree = 0 := by omega
    rw [hRd0] at hRh
    have hRC := isHomogeneous_zero_eq_C hRh
    have hR0 : R ≠ 0 := by intro h; rw [h, mul_zero] at hR; exact hPbar0 hR
    have hRc0 : R.coeff 0 ≠ 0 := by intro h; rw [h, map_zero] at hRC; exact hR0 hRC
    have hRu : IsUnit R := by rw [hRC]; exact (IsUnit.mk0 _ hRc0).map C
    have hassoc : Associated Q₀ Pbar := ⟨hRu.unit, hR.symm⟩
    exact hred (hassoc.irreducible_iff.mp hQ0_irr)
  -- Find minimal positive period r of Q₀ under Frob
  obtain ⟨r_any, hr_any1, hr_any_fix⟩ := frob_iter_finite_period hQ0_irr.ne_zero
  let perSet := (Finset.range (r_any + 1)).filter fun k => 1 ≤ k ∧ Frob^[k] Q₀ = Q₀
  have hr_any_mem : r_any ∈ perSet := mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hr_any1, hr_any_fix⟩
  let r := perSet.min' ⟨r_any, hr_any_mem⟩
  have hr_mem : r ∈ perSet := Finset.min'_mem perSet ⟨r_any, hr_any_mem⟩
  have hr1 : 1 ≤ r := (mem_filter.mp hr_mem).2.1
  have hr_fix : Frob^[r] Q₀ = Q₀ := (mem_filter.mp hr_mem).2.2
  have hr_min : ∀ k : ℕ, 1 ≤ k → k < r → Frob^[k] Q₀ ≠ Q₀ := by
    intro k hk1 hkr hfix
    have hr_le : r ≤ r_any := by
      have := Finset.mem_range.mp (mem_filter.mp hr_mem).1; omega
    have hk_mem : k ∈ perSet := mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hk1, hfix⟩
    have := Finset.min'_le perSet k hk_mem
    omega
  have hr2 : 2 ≤ r := by
    by_contra hlt2
    have hr1' : r = 1 := by omega
    rw [hr1', Function.iterate_one] at hr_fix
    obtain ⟨Q_K, hQK⟩ := (hFrob_fixed_iff Q₀).mp hr_fix
    have hQK0 : Q_K ≠ 0 := fun h => hQ0_irr.ne_zero (by rw [← hQK, h, map_zero])
    have hQK_dvd : Q_K ∣ P := hmap_dvd_iff hQK0 (by rw [hQK]; exact hQ0_dvd)
    rcases hQK_dvd with ⟨R_K, hRK⟩
    obtain ⟨hQKh, hRKh, hsum⟩ := isHomogeneous_of_dvd hPh hPirr.ne_zero hRK.symm
    have hQK_hom : Q_K.IsHomogeneous m := by
      intro s hs
      apply hQ0_h
      rw [← hQK, MvPolynomial.coeff_map]
      intro h0; exact hs (ι.injective (h0.trans (map_zero ι).symm))
    have hQKd : Q_K.totalDegree = m := hQK_hom.totalDegree hQK0
    have hRK0 : R_K ≠ 0 := by intro h; rw [h, mul_zero] at hRK; exact hPirr.ne_zero hRK
    have hnotu : ∀ {G : MvPolynomial (Fin 3) (ZMod p)} {k : ℕ},
        G.IsHomogeneous k → 1 ≤ k → ¬ IsUnit G := by
      intro G k hGh hk hu
      obtain ⟨U, hU⟩ := hu.exists_right_inv
      have hG0 : G ≠ 0 := by intro h; rw [h, zero_mul] at hU; exact zero_ne_one hU
      obtain ⟨_, _, hs⟩ := isHomogeneous_of_dvd (isHomogeneous_one (Fin 3) (ZMod p)) one_ne_zero hU
      have hGd : G.totalDegree = k := hGh.totalDegree hG0
      omega
    rcases hPirr.isUnit_or_isUnit hRK with h1 | h2
    · exact hnotu hQK_hom hm1 h1
    · exact hnotu hRKh (by omega) h2
  -- Show conjugates Frob^[j] Q₀ (j < r) are irreducible, homogeneous of deg m, divide Pbar, and pairwise non-associated
  have hconj_s0 : ∀ k : ℕ, (Frob^[k] Q₀).coeff s₀ = 1 := by
    intro k
    induction k with
    | zero => exact hQ0_s0
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      change (MvPolynomial.map frob (Frob^[k] Q₀)).coeff s₀ = 1
      rw [MvPolynomial.coeff_map, ih, map_one]
  have hconj_irr : ∀ k : ℕ, Irreducible (Frob^[k] Q₀) := by
    intro k
    induction k with
    | zero => exact hQ0_irr
    | succ k ih =>
      rw [Function.iterate_succ_apply', hFrob_eq_eFrob]
      have hnotu : ¬ IsUnit (eFrob (Frob^[k] Q₀)) := fun hu =>
        ih.not_isUnit (by have := hu.map eFrob.symm.toRingHom; simpa using this)
      refine ⟨hnotu, ?_⟩
      intro A B hAB
      have hback : Frob^[k] Q₀ = eFrob.symm A * eFrob.symm B := by
        have := congrArg eFrob.symm hAB; simpa [map_mul] using this
      rcases ih.isUnit_or_isUnit hback with hA | hB
      · left; have := hA.map eFrob.toRingHom; simpa using this
      · right; have := hB.map eFrob.toRingHom; simpa using this
  have hconj_hom : ∀ k : ℕ, (Frob^[k] Q₀).IsHomogeneous m := by
    intro k
    induction k with
    | zero => exact hQ0_h
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ih.map frob
  have hconj_dvd : ∀ k : ℕ, Frob^[k] Q₀ ∣ Pbar := by
    intro k
    induction k with
    | zero => exact hQ0_dvd
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with ⟨T, hT⟩
      refine ⟨Frob T, ?_⟩
      have h1 := congrArg Frob hT
      rw [map_mul, (hFrob_fixed_iff Pbar).mpr ⟨P, rfl⟩] at h1
      exact h1
  have hconj_nassoc : ∀ i j : ℕ, i < r → j < r → i ≠ j →
      ¬ Associated (Frob^[i] Q₀) (Frob^[j] Q₀) := by
    intro i j hi hj hij ⟨u, hu⟩
    have hu_hom : (u : MvPolynomial (Fin 3) Kbar).IsHomogeneous 0 := by
      obtain ⟨U, hU⟩ := u.isUnit.exists_right_inv
      obtain ⟨huh, _, hsum⟩ := isHomogeneous_of_dvd (isHomogeneous_one (Fin 3) Kbar) one_ne_zero hU
      have h0 : (u : MvPolynomial (Fin 3) Kbar).totalDegree = 0 := by omega
      rwa [h0] at huh
    have huC := isHomogeneous_zero_eq_C hu_hom
    have hcoeff_s0 := congrArg (fun f : MvPolynomial (Fin 3) Kbar => f.coeff s₀) hu
    rw [huC, mul_comm, MvPolynomial.coeff_C_mul, hconj_s0 i, hconj_s0 j, mul_one] at hcoeff_s0
    rw [hcoeff_s0, map_one] at huC
    rw [huC, mul_one] at hu
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · apply hr_min (j - i) (by omega) (by omega)
      have hiter : Frob^[i] (Frob^[j - i] Q₀) = Frob^[i] Q₀ := by
        rw [← Function.iterate_add_apply, show i + (j - i) = j by omega, hu.symm]
      exact (hFrob_inj.iterate i) hiter
    · apply hr_min (i - j) (by omega) (by omega)
      have hiter : Frob^[j] (Frob^[i - j] Q₀) = Frob^[j] Q₀ := by
        rw [← Function.iterate_add_apply, show j + (i - j) = i by omega, hu]
      exact (hFrob_inj.iterate j) hiter
  -- Product R := ∏ j < r, Frob^[j] Q₀ divides Pbar, is Frob-fixed, hence associated to Pbar!
  let R : MvPolynomial (Fin 3) Kbar := ∏ j ∈ Finset.range r, Frob^[j] Q₀
  have hR_dvd : R ∣ Pbar := by
    have hgen : ∀ S : Finset ℕ, (∀ j ∈ S, j < r) → (∏ j ∈ S, Frob^[j] Q₀) ∣ Pbar := by
      intro S
      induction S using Finset.induction_on with
      | empty => intro _; rw [Finset.prod_empty]; exact one_dvd _
      | @insert a S ha ih =>
        intro hS
        rw [Finset.prod_insert ha]
        have ha_lt : a < r := hS a (mem_insert_self a S)
        have hS_lt : ∀ j ∈ S, j < r := fun j hj => hS j (mem_insert_of_mem hj)
        have hd1 : Frob^[a] Q₀ ∣ Pbar := hconj_dvd a
        have hd2 : (∏ j ∈ S, Frob^[j] Q₀) ∣ Pbar := ih hS_lt
        have hprime : Prime (Frob^[a] Q₀) :=
          UniqueFactorizationMonoid.irreducible_iff_prime.mp (hconj_irr a)
        rcases hd2 with ⟨T, hT⟩
        have hnot_prod : ¬ (Frob^[a] Q₀ ∣ ∏ j ∈ S, Frob^[j] Q₀) := by
          intro hdiv
          obtain ⟨j, hjS, hja⟩ := hprime.dvd_finset_prod_iff _ |>.mp hdiv
          have hassoc : Associated (Frob^[a] Q₀) (Frob^[j] Q₀) :=
            (hconj_irr a).associated_of_dvd (hconj_irr j) hja
          exact hconj_nassoc a j ha_lt (hS_lt j hjS) (fun h => ha (h ▸ hjS)) hassoc
        have hdivT : Frob^[a] Q₀ ∣ T := (hprime.dvd_or_dvd (hT ▸ hd1)).resolve_left hnot_prod
        rcases hdivT with ⟨U, hU⟩
        exact ⟨U, by rw [hT, hU]; ring⟩
    exact hgen (Finset.range r) (fun j hj => Finset.mem_range.mp hj)
  have hR_hom : R.IsHomogeneous (r * m) := by
    have h := IsHomogeneous.prod (Finset.range r) (fun j => Frob^[j] Q₀) (fun _ => m)
      (fun j _ => hconj_hom j)
    simpa [Finset.sum_const, Finset.card_range, smul_eq_mul] using h
  have hR_ne : R ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => (hconj_irr j).ne_zero)
  have hrm_le : r * m ≤ d := by
    rcases hR_dvd with ⟨T, hT⟩
    obtain ⟨_, _, hsum⟩ := isHomogeneous_of_dvd hPbarh hPbar0 hT.symm
    have hRd : R.totalDegree = r * m := hR_hom.totalDegree hR_ne
    omega
  have h2m_le : 2 * m ≤ d := by
    have : 2 * m ≤ r * m := Nat.mul_le_mul_right m hr2
    omega
  -- R is Frob-invariant, so R = map ι R_K with R_K ∣ P, hence Associated R_K P, so Pbar ∣ R!
  have hR_fix : Frob R = R := by
    dsimp only [R]
    rw [map_prod]
    have hshift : (∏ j ∈ Finset.range r, Frob (Frob^[j] Q₀)) =
        ∏ j ∈ Finset.range r, Frob^[j + 1] Q₀ := by
      apply Finset.prod_congr rfl; intro j _; rw [Function.iterate_succ_apply']
    rw [hshift]
    have hsplit1 : (∏ j ∈ Finset.range r, Frob^[j + 1] Q₀) =
        (∏ j ∈ Finset.range (r - 1), Frob^[j + 1] Q₀) * Frob^[r] Q₀ := by
      have hr_eq : r = (r - 1) + 1 := by omega
      conv_lhs => rw [hr_eq, Finset.prod_range_succ]
      rw [show r - 1 + 1 = r by omega]
    have hsplit2 : (∏ j ∈ Finset.range r, Frob^[j] Q₀) =
        Q₀ * ∏ j ∈ Finset.range (r - 1), Frob^[j + 1] Q₀ := by
      have hr_eq : r = (r - 1) + 1 := by omega
      conv_lhs => rw [hr_eq, Finset.prod_range_succ']
      rw [Function.iterate_zero_apply, mul_comm]
    rw [hsplit1, hr_fix, hsplit2, mul_comm]
  obtain ⟨R_K, hRK⟩ := (hFrob_fixed_iff R).mp hR_fix
  have hRK0 : R_K ≠ 0 := fun h => hR_ne (by rw [← hRK, h, map_zero])
  have hRK_dvd : R_K ∣ P := hmap_dvd_iff hRK0 (by rw [hRK]; exact hR_dvd)
  have hRK_hom : R_K.IsHomogeneous (r * m) := by
    intro s hs
    apply hR_hom
    rw [← hRK, MvPolynomial.coeff_map]
    intro h0; exact hs (ι.injective (h0.trans (map_zero ι).symm))
  have hRK_notu : ¬ IsUnit R_K := by
    intro hu
    obtain ⟨U, hU⟩ := hu.exists_right_inv
    obtain ⟨_, _, hsum⟩ := isHomogeneous_of_dvd (isHomogeneous_one (Fin 3) (ZMod p)) one_ne_zero hU
    have hRKd : R_K.totalDegree = r * m := hRK_hom.totalDegree hRK0
    have hpos : 1 ≤ r * m := Nat.mul_pos (by omega) hm1
    omega
  have hP_dvd_RK : P ∣ R_K := by
    rcases hRK_dvd with ⟨U, hU⟩
    have hUu : IsUnit U := (hPirr.isUnit_or_isUnit hU).resolve_left hRK_notu
    obtain ⟨V, hV⟩ := hUu.exists_right_inv
    exact ⟨V, by rw [hU, mul_assoc, hV, mul_one]⟩
  have hPbar_dvd_R : Pbar ∣ R := by
    rcases hP_dvd_RK with ⟨U, hU⟩
    exact ⟨MvPolynomial.map ι U, by rw [← hRK, hU, map_mul]⟩
  -- Every u ∈ Z(P) satisfies eval (ι ∘ u) Q₀ = 0 AND eval (ι ∘ u) (Frob Q₀) = 0
  let ZP := (univ : Finset (Fin 3 → ZMod p)).filter fun v => IsNorm v ∧ eval v P = 0
  let Zbar := ZP.image (fun u : Fin 3 → ZMod p => ι ∘ u)
  have hZbar_card : Zbar.card = ZP.card := by
    apply card_image_of_injOn
    intro u _ v _ heq
    ext i; exact ι.injective (congrFun heq i)
  have hev_frob : ∀ (k : ℕ) (u : Fin 3 → ZMod p),
      eval (ι ∘ u) (Frob^[k] Q₀) = frob^[k] (eval (ι ∘ u) Q₀) := by
    intro k u
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hfix_u : frob ∘ (ι ∘ u) = ι ∘ u := by
        funext i; change (ι (u i)) ^ p = ι (u i); rw [← map_pow, ZMod.pow_card]
      conv_lhs => rw [← hfix_u]
      change eval (frob ∘ (ι ∘ u)) (MvPolynomial.map frob (Frob^[k] Q₀)) = _
      rw [eval_map_comp, ih]
  have hZbar_Q0 : ∀ w ∈ Zbar, eval w Q₀ = 0 := by
    intro w hw
    rcases mem_image.mp hw with ⟨u, hu, rfl⟩
    have hevP : eval u P = 0 := (mem_filter.mp hu).2.2
    have hevPbar : eval (ι ∘ u) Pbar = 0 := by
      dsimp only [Pbar]; rw [eval_map_comp, hevP, map_zero]
    have hevR : eval (ι ∘ u) R = 0 := by
      rcases hPbar_dvd_R with ⟨U, hU⟩
      rw [hU, map_mul, hevPbar, zero_mul]
    dsimp only [R] at hevR
    rw [map_prod] at hevR
    obtain ⟨j, _, hj0⟩ := Finset.prod_eq_zero_iff.mp hevR
    rw [hev_frob j u] at hj0
    have hf0 : ∀ t : ℕ, frob^[t] (0 : Kbar) = 0 := by
      intro t; induction t with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply', ih, map_zero]
    exact (hfrob_inj.iterate j) (hj0.trans (hf0 j).symm)
  have hZbar_Q1 : ∀ w ∈ Zbar, eval w (Frob Q₀) = 0 := by
    intro w hw
    rcases mem_image.mp hw with ⟨u, hu, rfl⟩
    have h0 := hZbar_Q0 (ι ∘ u) (mem_image.mpr ⟨u, hu, rfl⟩)
    have h1 := hev_frob 1 u
    rw [Function.iterate_one, Function.iterate_one] at h1
    rw [h1, h0, map_zero]
  -- Apply Sylvester Resultant Bézout to Q₀ and Frob Q₀!
  have hZbar_le : Zbar.card ≤ m * m := by
    apply bezout_coprime_homog hm1 hQ0_h (hconj_hom 1) hQ0_irr (hconj_irr 1)
      (hconj_nassoc 0 1 (by omega) (by omega) (by decide))
    · intro w hw
      rcases mem_image.mp hw with ⟨u, hu, rfl⟩
      intro h0
      apply isNorm_ne_zero (mem_filter.mp hu).2.1
      ext i; exact ι.injective (by simpa using congrFun h0 i)
    · intro w₁ hw₁ w₂ hw₂ hne
      rcases mem_image.mp hw₁ with ⟨u₁, hu₁, rfl⟩
      rcases mem_image.mp hw₂ with ⟨u₂, hu₂, rfl⟩
      have hu12 : u₁ ≠ u₂ := fun h => hne (congrArg (ι ∘ ·) h)
      intro hcr0
      have hcrZ : cross3 u₁ u₂ = 0 := by
        ext i; apply ι.injective
        change ι (cross3 u₁ u₂ i) = ι 0
        rw [map_zero]
        have hi := congrFun hcr0 i
        fin_cases i <;>
          (unfold cross3 at hi ⊢; dsimp only at hi ⊢; simp only [Function.comp_apply] at hi;
           rw [map_sub, map_mul, map_mul]; exact hi)
      obtain ⟨c, hc⟩ := (cross3_eq_zero_iff (isNorm_ne_zero (mem_filter.mp hu₁).2.1)).mp hcrZ
      exact hu12 (isNorm_eq_of_smul (mem_filter.mp hu₂).2.1 (mem_filter.mp hu₁).2.1 hc).symm
    · exact hZbar_Q0
    · exact hZbar_Q1
  -- Combine A.card * d ≤ 2 * ZP.card ≤ 2 * m^2 with 2 * m ≤ d ≤ 2 * t!
  have hinc := card_mul_deg_le_two_mul_Z hp2 harc he hEA hE hPh hdvd
  have hZP_le : ZP.card ≤ m * m := by rwa [← hZbar_card]
  have h1 : 2 * (A.card * d) ≤ d * d := by
    calc 2 * (A.card * d) ≤ 2 * (2 * ZP.card) := Nat.mul_le_mul_left 2 hinc
      _ = 4 * ZP.card := by ring
      _ ≤ 4 * (m * m) := Nat.mul_le_mul_left 4 hZP_le
      _ = (2 * m) * (2 * m) := by ring
      _ ≤ d * d := Nat.mul_le_mul h2m_le h2m_le
  have h2 : 2 * A.card ≤ d := by
    have hmul : (2 * A.card) * d ≤ d * d := by linarith
    exact Nat.le_of_mul_le_mul_right hmul (by omega)
  omega

end GeomReducible

section MainAssembly

theorem voloch_H1_main :
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ A : Finset (Fin 2 → ZMod p),
      (∀ s ⊆ A, s.card = 3 → ¬ Collinear (ZMod p) (s : Set (Fin 2 → ZMod p))) →
      6 ≤ A.card →
      (¬ ∃ Q : MvPolynomial (Fin 2) (ZMod p),
        Q ≠ 0 ∧ Q.totalDegree ≤ 2 ∧ ∀ a ∈ A, eval a Q = 0) →
      A.card ≤ p + 2 ∧
        (4 * A.card ≤ 3 * p + 5 ∨ A.card ≤ 4 * (p + 2 - A.card) ∨
          ∃ (n : ℕ) (F : MvPolynomial (Fin 3) (ZMod p)),
            3 ≤ n ∧ n ≤ 2 * (p + 2 - A.card) ∧ F.IsHomogeneous n ∧
            Irreducible (MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) F) ∧
            let Z := (univ : Finset (Fin 3 → ZMod p)).filter fun v =>
              (v 0 = 1 ∨ (v 0 = 0 ∧ v 1 = 1) ∨
                (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 1)) ∧ eval v F = 0
            A.card * n ≤ 2 * Z.card) := by
  intro p _ hp2 A harc hA6 hnc
  refine ⟨card_le_add_two_of_arc harc, ?_⟩
  by_cases h1 : 4 * A.card ≤ 3 * p + 5
  · exact Or.inl h1
  by_cases h2 : A.card ≤ 4 * (p + 2 - A.card)
  · exact Or.inr (Or.inl h2)
  have hA_le1 : A.card ≤ p + 1 := card_le_add_one_of_arc hp2 harc
  set t := p + 2 - A.card
  have ht1 : 1 ≤ t := by omega
  have hE_le : 2 * t + 2 ≤ A.card := by omega
  obtain ⟨E, hEA, hEcard⟩ := Finset.exists_subset_card_eq hE_le
  obtain ⟨e, he⟩ := card_pos.mp (show 0 < A.card by omega)
  obtain ⟨P, H, d, hPirr, hmul, hnot, hPh, hHh, hd1, hdt⟩ :=
    exists_simple_irreducible_factor hp2 harc he hEA hEcard (by omega)
  by_cases hirr_bar : Irreducible (MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) P)
  · by_cases hd_eq1 : d = 1
    · subst hd_eq1
      exact absurd (card_le_four_mul_t_of_deg_one hp2 harc he hEA hEcard hPh hHh hmul hnot) h2
    · by_cases hd_eq2 : d = 2
      · subst hd_eq2
        exact absurd (four_mul_card_le_of_deg_two hp2 harc hnc he hEA hEcard hPh ⟨H, hmul.symm⟩ hirr_bar) h1
      · refine Or.inr (Or.inr ⟨d, P, by omega, hdt, hPh, hirr_bar, ?_⟩)
        exact card_mul_deg_le_two_mul_Z hp2 harc he hEA hEcard hPh ⟨H, hmul.symm⟩
  · exact absurd (card_le_four_mul_t_of_not_irreducible_map hp2 harc he hEA hEcard hPirr hPh hd1 hdt
      ⟨H, hmul.symm⟩ hirr_bar) h2

end MainAssembly

end VolochH1Proof

theorem OMA.solution : OMA.R_Green68_green_68_variants_voloch_R2.H1 := by
  intro p _ hp2 A harc hA6 hnc
  exact VolochH1Proof.voloch_H1_main p hp2 A harc hA6 hnc
