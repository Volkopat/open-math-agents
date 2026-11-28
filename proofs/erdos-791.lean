import OMAStatements.S_erdos_791
import Mathlib

-- Problem: Erdős Problem 791
-- Upstream: formal-conjectures statements/erdos-791.lean:0 (declaration OMA.S_erdos_791.main)
-- Credit: @npnelson (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Disproof, following the Mrose-type construction in Kohonen, J. Number Theory 174 (2017),
-- Section 2, Example 2. For t >= 1 and T = t^2 let
--   V = [0, t],  H = {0, t, ..., t^2 - t},  S = {0, t + 1, ..., t^2 - 1},
--   A = (V + T * {0, 6, 10}) ∪ (H + T * {0, 1, 2}) ∪ (S + 3 * T).
-- Then V + H and V + S contain [0, T - 1], and (H + S) ∪ (H + S + T) contains [T, 2 T - 1],
-- so A + A contains [0, 14 T - 1], while A has at most 7 t + 3 elements and lies in
-- [0, 14 T - 1]. Hence g(14 t^2 - 1) <= 7 t + 3, and g(n) / sqrt n is at most 19/10 along
-- n = 14 t^2 - 1 for t >= 28, so it cannot tend to 2.

namespace Erdos791Proof
open Finset Filter Topology OMA.S_erdos_791

def A (t : ℕ) : Finset ℕ :=
  ((({0, 6, 10} : Finset ℕ) ×ˢ range (t + 1)).image (fun p => p.2 + p.1 * (t * t))) ∪
  ((({0, 1, 2} : Finset ℕ) ×ˢ range t).image (fun p => t * p.2 + p.1 * (t * t))) ∪
  ((range t).image (fun c => (t + 1) * c + 3 * (t * t)))

lemma memV {t i v : ℕ} (hi : i = 0 ∨ i = 6 ∨ i = 10) (hv : v ≤ t) :
    v + i * (t * t) ∈ A t := by
  unfold A
  apply mem_union_left
  apply mem_union_left
  rw [mem_image]
  refine ⟨(i, v), ?_, rfl⟩
  rw [mem_product]
  refine ⟨?_, ?_⟩
  · simp only [mem_insert, mem_singleton]
    exact hi
  · rw [mem_range]
    omega

lemma memH {t j a : ℕ} (hj : j = 0 ∨ j = 1 ∨ j = 2) (ha : a < t) :
    t * a + j * (t * t) ∈ A t := by
  unfold A
  apply mem_union_left
  apply mem_union_right
  rw [mem_image]
  refine ⟨(j, a), ?_, rfl⟩
  rw [mem_product]
  refine ⟨?_, ?_⟩
  · simp only [mem_insert, mem_singleton]
    exact hj
  · rw [mem_range]
    exact ha

lemma memS {t c : ℕ} (hc : c < t) : (t + 1) * c + 3 * (t * t) ∈ A t := by
  unfold A
  apply mem_union_right
  rw [mem_image]
  exact ⟨c, mem_range.mpr hc, rfl⟩

lemma card_A (t : ℕ) : (A t).card ≤ 7 * t + 3 := by
  unfold A
  have h1 : ((({0, 6, 10} : Finset ℕ) ×ˢ range (t + 1)).image
      (fun p => p.2 + p.1 * (t * t))).card ≤ 3 * (t + 1) := by
    refine card_image_le.trans ?_
    rw [card_product, card_range]
    exact Nat.mul_le_mul_right _ (card_le_three)
  have h2 : ((({0, 1, 2} : Finset ℕ) ×ˢ range t).image
      (fun p => t * p.2 + p.1 * (t * t))).card ≤ 3 * t := by
    refine card_image_le.trans ?_
    rw [card_product, card_range]
    exact Nat.mul_le_mul_right _ (card_le_three)
  have h3 : ((range t).image (fun c => (t + 1) * c + 3 * (t * t))).card ≤ t := by
    refine card_image_le.trans ?_
    rw [card_range]
  have h4 := card_union_le
    (((({0, 6, 10} : Finset ℕ) ×ˢ range (t + 1)).image (fun p => p.2 + p.1 * (t * t))) ∪
      ((({0, 1, 2} : Finset ℕ) ×ˢ range t).image (fun p => t * p.2 + p.1 * (t * t))))
    ((range t).image (fun c => (t + 1) * c + 3 * (t * t)))
  have h5 := card_union_le
    ((({0, 6, 10} : Finset ℕ) ×ˢ range (t + 1)).image (fun p => p.2 + p.1 * (t * t)))
    ((({0, 1, 2} : Finset ℕ) ×ˢ range t).image (fun p => t * p.2 + p.1 * (t * t)))
  omega

/-- `V + H` contains `[0, t^2 - 1]`. -/
lemma coverVH {t r : ℕ} (hr : r < t * t) : ∃ v ≤ t, ∃ a < t, v + t * a = r := by
  have ht : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h] at hr; omega
    · exact h
  refine ⟨r % t, (Nat.mod_lt r ht).le, r / t, ?_, Nat.mod_add_div r t⟩
  exact (Nat.div_lt_iff_lt_mul ht).mpr hr

/-- `V + S` contains `[0, t^2 - 1]`. -/
lemma coverVS {t r : ℕ} (hr : r < t * t) : ∃ v ≤ t, ∃ c < t, v + (t + 1) * c = r := by
  refine ⟨r % (t + 1), Nat.lt_succ_iff.mp (Nat.mod_lt r (Nat.succ_pos t)), r / (t + 1), ?_,
    Nat.mod_add_div r (t + 1)⟩
  refine (Nat.div_lt_iff_lt_mul (Nat.succ_pos t)).mpr ?_
  nlinarith

/-- `(H + S) ∪ (H + S + t^2)` contains `[t^2, 2 t^2 - 1]`. -/
lemma coverHS {t r : ℕ} (hr : r < t * t) :
    ∃ a < t, ∃ c < t, ∃ e, (e = 0 ∨ e = 1) ∧ t * a + (t + 1) * c + e * (t * t) = r + t * t := by
  have ht : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h] at hr; omega
    · exact h
  have hx : t * ((r + t * t) / t) + (r + t * t) % t = r + t * t := Nat.div_add_mod _ _
  have hw : (r + t * t) % t < t := Nat.mod_lt _ ht
  generalize (r + t * t) / t = u at hx
  generalize (r + t * t) % t = w at hx hw
  have hu1 : t ≤ u := by
    by_contra hcon
    have h1 : u + 1 ≤ t := by omega
    have h2 : t * (u + 1) ≤ t * t := Nat.mul_le_mul_left t h1
    nlinarith
  have hu2 : u < 2 * t := by
    by_contra hcon
    have h1 : 2 * t ≤ u := by omega
    have h2 : t * (2 * t) ≤ t * u := Nat.mul_le_mul_left t h1
    nlinarith
  by_cases hlt : u < w + t
  · obtain ⟨a, ha⟩ : ∃ a, u = a + w := ⟨u - w, by omega⟩
    refine ⟨a, by omega, w, hw, 0, Or.inl rfl, ?_⟩
    rw [← hx, ha]
    ring
  · obtain ⟨a, ha⟩ : ∃ a, u = a + w + t := ⟨u - w - t, by omega⟩
    refine ⟨a, by omega, w, hw, 1, Or.inr rfl, ?_⟩
    rw [← hx, ha]
    ring

lemma cover {t m : ℕ} (ht : 1 ≤ t) (hm : m < 14 * (t * t)) :
    ∃ a ∈ A t, ∃ b ∈ A t, a + b = m := by
  have hT : 0 < t * t := Nat.mul_pos ht ht
  have hdm : t * t * (m / (t * t)) + m % (t * t) = m := Nat.div_add_mod m (t * t)
  have hr : m % (t * t) < t * t := Nat.mod_lt m hT
  have hq : m / (t * t) < 14 := (Nat.div_lt_iff_lt_mul hT).mpr hm
  generalize m / (t * t) = q at hdm hq
  generalize m % (t * t) = r at hdm hr
  have hVH := coverVH hr
  have hVS := coverVS hr
  have hHS := coverHS hr
  obtain ⟨v, hv, a, ha, hva⟩ := hVH
  obtain ⟨v', hv', c, hc, hvc⟩ := hVS
  obtain ⟨a', ha', c', hc', e, he, hace⟩ := hHS
  interval_cases q
  · exact ⟨_, memV (i := 0) (Or.inl rfl) hv, _, memH (j := 0) (Or.inl rfl) ha, by linarith⟩
  · exact ⟨_, memV (i := 0) (Or.inl rfl) hv, _, memH (j := 1) (Or.inr (Or.inl rfl)) ha,
      by linarith⟩
  · exact ⟨_, memV (i := 0) (Or.inl rfl) hv, _, memH (j := 2) (Or.inr (Or.inr rfl)) ha,
      by linarith⟩
  · exact ⟨_, memV (i := 0) (Or.inl rfl) hv', _, memS hc, by linarith⟩
  · rcases he with he | he
    · exact ⟨_, memH (j := 0) (Or.inl rfl) ha', _, memS hc', by rw [he] at hace; linarith⟩
    · exact ⟨_, memH (j := 1) (Or.inr (Or.inl rfl)) ha', _, memS hc',
        by rw [he] at hace; linarith⟩
  · rcases he with he | he
    · exact ⟨_, memH (j := 1) (Or.inr (Or.inl rfl)) ha', _, memS hc',
        by rw [he] at hace; linarith⟩
    · exact ⟨_, memH (j := 2) (Or.inr (Or.inr rfl)) ha', _, memS hc',
        by rw [he] at hace; linarith⟩
  · exact ⟨_, memV (i := 6) (Or.inr (Or.inl rfl)) hv, _, memH (j := 0) (Or.inl rfl) ha,
      by linarith⟩
  · exact ⟨_, memV (i := 6) (Or.inr (Or.inl rfl)) hv, _, memH (j := 1) (Or.inr (Or.inl rfl)) ha,
      by linarith⟩
  · exact ⟨_, memV (i := 6) (Or.inr (Or.inl rfl)) hv, _, memH (j := 2) (Or.inr (Or.inr rfl)) ha,
      by linarith⟩
  · exact ⟨_, memV (i := 6) (Or.inr (Or.inl rfl)) hv', _, memS hc, by linarith⟩
  · exact ⟨_, memV (i := 10) (Or.inr (Or.inr rfl)) hv, _, memH (j := 0) (Or.inl rfl) ha,
      by linarith⟩
  · exact ⟨_, memV (i := 10) (Or.inr (Or.inr rfl)) hv, _, memH (j := 1) (Or.inr (Or.inl rfl)) ha,
      by linarith⟩
  · exact ⟨_, memV (i := 10) (Or.inr (Or.inr rfl)) hv, _, memH (j := 2) (Or.inr (Or.inr rfl)) ha,
      by linarith⟩
  · exact ⟨_, memV (i := 10) (Or.inr (Or.inr rfl)) hv', _, memS hc, by linarith⟩

lemma subset_A {t : ℕ} (ht : 1 ≤ t) : A t ⊆ range (14 * (t * t)) := by
  have htt : t ≤ t * t := Nat.le_mul_self t
  intro x hx
  rw [mem_range]
  unfold A at hx
  rw [mem_union, mem_union, mem_image, mem_image, mem_image] at hx
  rcases hx with (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | ⟨c, hc, rfl⟩
  · rw [mem_product, mem_range] at hp
    obtain ⟨hp1, hp2⟩ := hp
    simp only [mem_insert, mem_singleton] at hp1
    rcases hp1 with h | h | h <;> rw [h] <;> omega
  · rw [mem_product, mem_range] at hp
    obtain ⟨hp1, hp2⟩ := hp
    have h1 : t * p.2 < t * t := (Nat.mul_lt_mul_left (by omega : 0 < t)).mpr hp2
    simp only [mem_insert, mem_singleton] at hp1
    rcases hp1 with h | h | h <;> rw [h] <;> omega
  · rw [mem_range] at hc
    have h1 : (t + 1) * c < t * t + t := by nlinarith
    omega

lemma g_le {t : ℕ} (ht : 1 ≤ t) : g (14 * (t * t) - 1) ≤ 7 * t + 3 := by
  have hT : 0 < t * t := Nat.mul_pos ht ht
  have hn : 14 * (t * t) - 1 + 1 = 14 * (t * t) := by omega
  unfold g
  refine (Nat.sInf_le ?_).trans (card_A t)
  refine ⟨A t, ?_, rfl, ?_⟩
  · rw [hn]
    exact subset_A ht
  · intro m hm
    exact cover ht (by omega)

end Erdos791Proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_erdos_791.main) := by
  intro h
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      (19 / 10 : ℝ) < (OMA.S_erdos_791.g n : ℝ) / Real.sqrt n :=
    h.eventually (lt_mem_nhds (by norm_num))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  have ht28 : 28 ≤ max N 28 := le_max_right _ _
  have htN : N ≤ max N 28 := le_max_left _ _
  generalize max N 28 = t at ht28 htN
  have htt : t ≤ t * t := Nat.le_mul_self t
  have h1 := hN (14 * (t * t) - 1) (by omega)
  have h2 := Erdos791Proof.g_le (t := t) (by omega)
  have hcast : ((14 * (t * t) - 1 : ℕ) : ℝ) = 14 * ((t : ℝ) * t) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have ht' : (28 : ℝ) ≤ t := by exact_mod_cast ht28
  have hnpos : (0 : ℝ) < ((14 * (t * t) - 1 : ℕ) : ℝ) := by
    rw [hcast]
    nlinarith
  have hpos : (0 : ℝ) < Real.sqrt ((14 * (t * t) - 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hnpos
  rw [lt_div_iff₀ hpos] at h1
  have h3 : (OMA.S_erdos_791.g (14 * (t * t) - 1) : ℝ) ≤ 7 * t + 3 := by exact_mod_cast h2
  have h4 : (19 / 10 : ℝ) * Real.sqrt ((14 * (t * t) - 1 : ℕ) : ℝ) < 7 * t + 3 :=
    lt_of_lt_of_le h1 h3
  have h5 : ((19 / 10 : ℝ) * Real.sqrt ((14 * (t * t) - 1 : ℕ) : ℝ)) ^ 2 < (7 * (t : ℝ) + 3) ^ 2 :=
    pow_lt_pow_left₀ h4 (by positivity) (by norm_num)
  rw [mul_pow, Real.sq_sqrt hnpos.le, hcast] at h5
  nlinarith [mul_nonneg (sub_nonneg.mpr ht') (by positivity : (0 : ℝ) ≤ (t : ℝ))]
