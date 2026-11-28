import OMAStatements.S_opg_are_critical_k_forests_tight

-- Problem: Strausz's conjecture on critical uniform hyperforests
-- Credit: @EmadY
--
-- Counterexample following Gebauer, Gundert, Moser, and Okamoto (arXiv:1109.3390, Theorem 2.2):
-- While Lovasz's bound caps any k-uniform hyperforest on n vertices at C(n - 1, k - 1) edges
-- (attained by tight stars, here C(5, 2) = 10 for n = 6, k = 3), the 6-vertex, 8-edge
-- 3-uniform hyperforest H6 below is already saturated (via two-edge color-rigidity retractions
-- covering all 12 missing 3-sets) yet fails tightness under coloring (2, 1, 1, 1, 1, 0).

open OMA.S_opg_are_critical_k_forests_tight (Rainbow IsForest IsSaturated IsTight)

private def H6 : Finset (Finset (Fin 6)) :=
  {{0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 2, 3}, {1, 2, 5}, {1, 4, 5}, {2, 3, 5}, {2, 4, 5}}

private lemma hcard_H6 : ∀ e ∈ H6, e.card = 3 := by
  decide +kernel

private def forestColoring (i : Fin 8) (v : Fin 6) : Fin 3 :=
  match i.val, v.val with
  | 0, 0 => 2 | 0, 1 => 1 | 0, 2 => 0 | 0, 3 => 2 | 0, 4 => 1 | 0, _ => 0
  | 1, 0 => 0 | 1, 1 => 2 | 1, 2 => 0 | 1, 3 => 1 | 1, 4 => 0 | 1, _ => 0
  | 2, 0 => 2 | 2, 1 => 1 | 2, 2 => 1 | 2, 3 => 1 | 2, 4 => 0 | 2, _ => 0
  | 3, 0 => 2 | 3, 1 => 2 | 3, 2 => 0 | 3, 3 => 1 | 3, 4 => 0 | 3, _ => 0
  | 4, 0 => 2 | 4, 1 => 2 | 4, 2 => 1 | 4, 3 => 1 | 4, 4 => 0 | 4, _ => 0
  | 5, 0 => 2 | 5, 1 => 2 | 5, 2 => 0 | 5, 3 => 0 | 5, 4 => 1 | 5, _ => 0
  | 6, 0 => 2 | 6, 1 => 2 | 6, 2 => 2 | 6, 3 => 1 | 6, 4 => 0 | 6, _ => 0
  | _, 0 => 0 | _, 1 => 0 | _, 2 => 2 | _, 3 => 0 | _, 4 => 1 | _, _ => 0

private lemma isForest_of_table {n k m : ℕ} {E : Finset (Finset (Fin n))}
    (γ : Fin m → Fin n → Fin k)
    (h : ∀ e ∈ E, ∃ i : Fin m, ∀ f ∈ E, (f.image (γ i) = Finset.univ ↔ f = e)) :
    IsForest k E :=
  fun e he => let ⟨i, hi⟩ := h e he; ⟨γ i, hi⟩

private lemma isForest_H6 : IsForest 3 H6 :=
  isForest_of_table forestColoring (by decide +kernel)

private def cTight : Fin 6 → Fin 3
  | ⟨0, _⟩ => 2
  | ⟨5, _⟩ => 0
  | _ => 1

private lemma not_isTight_H6 : ¬ IsTight 3 H6 := by
  intro hT
  have hc : Finset.univ.image cTight = Finset.univ := by decide +kernel
  have hno : ¬ ∃ e ∈ H6, e.image cTight = Finset.univ := by decide +kernel
  exact hno (hT cTight hc)

private def r1 : Fin 6 → Fin 6
  | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 0 | ⟨4, _⟩ => 1 | ⟨5, _⟩ => 2

private def r2 : Fin 6 → Fin 6
  | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 2 | ⟨4, _⟩ => 5 | ⟨5, _⟩ => 5

private lemma forced_color_aux :
    ∀ u v w x : Fin 3,
      ({u, v, w} : Finset (Fin 3)) = Finset.univ →
      ({u, v, x} : Finset (Fin 3)) ≠ Finset.univ →
      ({u, w, x} : Finset (Fin 3)) ≠ Finset.univ →
      x = u := by
  decide +kernel

private lemma rainbow_perm {c : Fin 6 → Fin 3} {e0 : Finset (Fin 6)}
    (hr : Rainbow c e0) {a b d : Fin 6} (heq : ({a, b, d} : Finset (Fin 6)) = e0) :
    ({c a, c b, c d} : Finset (Fin 3)) = Finset.univ := by
  rw [← heq] at hr
  simpa only [Rainbow, Finset.image_insert, Finset.image_singleton] using hr

private lemma not_rainbow_mem {e e0 : Finset (Fin 6)} {c : Fin 6 → Fin 3}
    (hc : ∀ f ∈ insert e H6, Rainbow c f ↔ f = e0)
    {a b d : Fin 6} (hm : ({a, b, d} : Finset (Fin 6)) ∈ H6)
    (hne : ({a, b, d} : Finset (Fin 6)) ≠ e0) :
    ({c a, c b, c d} : Finset (Fin 3)) ≠ Finset.univ := by
  intro hu
  have hr : Rainbow c {a, b, d} := by
    simpa only [Rainbow, Finset.image_insert, Finset.image_singleton] using hu
  exact hne ((hc {a, b, d} (Finset.mem_insert_of_mem hm)).mp hr)

private lemma image_ne_of_retract {e e0 : Finset (Fin 6)}
    (he : e ∉ H6) (he0 : e0 ∈ H6) (hF : IsForest 3 (insert e H6))
    (r : Fin 6 → Fin 6)
    (hrig : ∀ c : Fin 6 → Fin 3,
      (∀ f ∈ insert e H6, Rainbow c f ↔ f = e0) → c = c ∘ r) :
    e.image r ≠ e0 := by
  intro himg
  obtain ⟨c, hc⟩ := hF e0 (Finset.mem_insert_of_mem he0)
  have hr0 : Rainbow c e0 := (hc e0 (Finset.mem_insert_of_mem he0)).mpr rfl
  have hre : Rainbow c e := by
    unfold Rainbow at hr0 ⊢
    rw [hrig c hc, ← Finset.image_image, himg]
    exact hr0
  have he_eq : e = e0 := (hc e (Finset.mem_insert_self e H6)).mp hre
  exact he (he_eq ▸ he0)

private lemma rig_r1 {e : Finset (Fin 6)} {c : Fin 6 → Fin 3}
    (hc : ∀ f ∈ insert e H6, Rainbow c f ↔ f = {0, 1, 2}) : c = c ∘ r1 := by
  have hr0 : Rainbow c {0, 1, 2} :=
    (hc {0, 1, 2} (Finset.mem_insert_of_mem (by decide +kernel))).mpr rfl
  have h3 : c 3 = c 0 :=
    forced_color_aux (c 0) (c 1) (c 2) (c 3)
      (rainbow_perm hr0 rfl)
      (not_rainbow_mem hc (a := 0) (b := 1) (d := 3) (by decide +kernel) (by decide +kernel))
      (not_rainbow_mem hc (a := 0) (b := 2) (d := 3) (by decide +kernel) (by decide +kernel))
  have h235 := not_rainbow_mem hc (a := 2) (b := 3) (d := 5) (by decide +kernel) (by decide +kernel)
  rw [h3] at h235
  have h5 : c 5 = c 2 :=
    forced_color_aux (c 2) (c 1) (c 0) (c 5)
      (rainbow_perm hr0 (by decide +kernel))
      (not_rainbow_mem hc (a := 2) (b := 1) (d := 5) (by decide +kernel) (by decide +kernel))
      h235
  have h154 := not_rainbow_mem hc (a := 1) (b := 5) (d := 4) (by decide +kernel) (by decide +kernel)
  rw [h5] at h154
  have h4 : c 4 = c 1 :=
    forced_color_aux (c 1) (c 0) (c 2) (c 4)
      (rainbow_perm hr0 (by decide +kernel))
      (not_rainbow_mem hc (a := 1) (b := 0) (d := 4) (by decide +kernel) (by decide +kernel))
      h154
  funext i
  match i with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => exact h3
  | ⟨4, _⟩ => exact h4
  | ⟨5, _⟩ => exact h5

private lemma rig_r2 {e : Finset (Fin 6)} {c : Fin 6 → Fin 3}
    (hc : ∀ f ∈ insert e H6, Rainbow c f ↔ f = {1, 2, 5}) : c = c ∘ r2 := by
  have hr0 : Rainbow c {1, 2, 5} :=
    (hc {1, 2, 5} (Finset.mem_insert_of_mem (by decide +kernel))).mpr rfl
  have h4 : c 4 = c 5 :=
    forced_color_aux (c 5) (c 1) (c 2) (c 4)
      (rainbow_perm hr0 (by decide +kernel))
      (not_rainbow_mem hc (a := 5) (b := 1) (d := 4) (by decide +kernel) (by decide +kernel))
      (not_rainbow_mem hc (a := 5) (b := 2) (d := 4) (by decide +kernel) (by decide +kernel))
  have h140 := not_rainbow_mem hc (a := 1) (b := 4) (d := 0) (by decide +kernel) (by decide +kernel)
  rw [h4] at h140
  have h0 : c 0 = c 1 :=
    forced_color_aux (c 1) (c 2) (c 5) (c 0)
      (rainbow_perm hr0 rfl)
      (not_rainbow_mem hc (a := 1) (b := 2) (d := 0) (by decide +kernel) (by decide +kernel))
      h140
  have h203 := not_rainbow_mem hc (a := 2) (b := 0) (d := 3) (by decide +kernel) (by decide +kernel)
  rw [h0] at h203
  have h3 : c 3 = c 2 :=
    forced_color_aux (c 2) (c 5) (c 1) (c 3)
      (rainbow_perm hr0 (by decide +kernel))
      (not_rainbow_mem hc (a := 2) (b := 5) (d := 3) (by decide +kernel) (by decide +kernel))
      h203
  funext i
  match i with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ | ⟨2, _⟩ | ⟨5, _⟩ => rfl
  | ⟨3, _⟩ => exact h3
  | ⟨4, _⟩ => exact h4

private lemma nonedge_covered :
    ∀ e ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      e ∉ H6 → e.image r1 = {0, 1, 2} ∨ e.image r2 = {1, 2, 5} := by
  decide +kernel

private lemma isSaturated_H6 : IsSaturated 3 H6 := by
  intro e he_card he_not hF
  have hne1 : e.image r1 ≠ {0, 1, 2} :=
    image_ne_of_retract he_not (by decide +kernel) hF r1 (fun _ hc => rig_r1 hc)
  have hne2 : e.image r2 ≠ {1, 2, 5} :=
    image_ne_of_retract he_not (by decide +kernel) hF r2 (fun _ hc => rig_r2 hc)
  rcases nonedge_covered e he_card he_not with h1 | h2
  · exact hne1 h1
  · exact hne2 h2

theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_are_critical_k_forests_tight.main) := by
  intro h
  exact not_isTight_H6 (h 6 3 H6 (by decide) (by decide) hcard_H6 isForest_H6 isSaturated_H6)
