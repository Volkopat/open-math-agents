import OMAReductions.R_Erdos651_erdos_651_R1_H1_R1

open Filter Erdos651
open scoped EuclideanGeometry BigOperators Matrix

namespace Erdos651H1Proof

/- ## Module 1: General d-uniform 2-color Hypergraph Ramsey Theorem -/

private def IsMono {α : Type} [DecidableEq α] (d : ℕ)
    (c : Finset α → Bool) (S : Finset α) (b : Bool) : Prop :=
  ∀ e ⊆ S, e.card = d → c e = b

private theorem hypergraph_ramsey :
    ∀ (d : ℕ) (m₁ m₂ : ℕ), ∃ R : ℕ, ∀ (α : Type) [DecidableEq α] (V : Finset α),
      R ≤ V.card → ∀ c : Finset α → Bool,
        (∃ S ⊆ V, S.card = m₁ ∧ IsMono d c S true) ∨
        (∃ S ⊆ V, S.card = m₂ ∧ IsMono d c S false) := by
  intro d
  induction d with
  | zero =>
    intro m₁ m₂
    refine ⟨max m₁ m₂, ?_⟩
    intro α _ V hV c
    cases hc : c ∅ with
    | true =>
      obtain ⟨S, hSV, hSc⟩ := Finset.exists_subset_card_eq (le_trans (le_max_left m₁ m₂) hV)
      refine Or.inl ⟨S, hSV, hSc, fun e _ he => ?_⟩
      rw [Finset.card_eq_zero.mp he, hc]
    | false =>
      obtain ⟨S, hSV, hSc⟩ := Finset.exists_subset_card_eq (le_trans (le_max_right m₁ m₂) hV)
      refine Or.inr ⟨S, hSV, hSc, fun e _ he => ?_⟩
      rw [Finset.card_eq_zero.mp he, hc]
  | succ d ih_d =>
    intro m₁ m₂
    have key : ∀ s : ℕ, ∀ a b : ℕ, a + b = s → ∃ R : ℕ,
        ∀ (α : Type) [DecidableEq α] (V : Finset α),
          R ≤ V.card → ∀ c : Finset α → Bool,
            (∃ S ⊆ V, S.card = a ∧ IsMono (d + 1) c S true) ∨
            (∃ S ⊆ V, S.card = b ∧ IsMono (d + 1) c S false) := by
      intro s
      induction s with
      | zero =>
        intro a b hab
        have ha : a = 0 := by omega
        subst ha
        refine ⟨0, fun α _ V _ c => Or.inl ⟨∅, Finset.empty_subset V, rfl, ?_⟩⟩
        intro e he hcard
        have := Finset.subset_empty.mp he
        subst this
        simp at hcard
      | succ s ih_s =>
        intro a b hab
        rcases eq_or_ne a 0 with rfl | ha0
        · refine ⟨0, fun α _ V _ c => Or.inl ⟨∅, Finset.empty_subset V, rfl, ?_⟩⟩
          intro e he hcard
          have := Finset.subset_empty.mp he
          subst this
          simp at hcard
        rcases eq_or_ne b 0 with rfl | hb0
        · refine ⟨0, fun α _ V _ c => Or.inr ⟨∅, Finset.empty_subset V, rfl, ?_⟩⟩
          intro e he hcard
          have := Finset.subset_empty.mp he
          subst this
          simp at hcard
        obtain ⟨R₁, hR₁⟩ := ih_s (a - 1) b (by omega)
        obtain ⟨R₂, hR₂⟩ := ih_s a (b - 1) (by omega)
        obtain ⟨R₀, hR₀⟩ := ih_d R₁ R₂
        refine ⟨R₀ + 1, ?_⟩
        intro α _ V hV c
        have hVne : V.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨v, hv⟩ := hVne
        let V' := V.erase v
        have hV' : R₀ ≤ V'.card := by
          rw [Finset.card_erase_of_mem hv]
          omega
        let c' : Finset α → Bool := fun e => c (insert v e)
        rcases hR₀ α V' hV' c' with ⟨W, hWV', hWc, hWmono⟩ | ⟨W, hWV', hWc, hWmono⟩
        · rcases hR₁ α W (by omega) c with ⟨S, hSW, hSc, hSmono⟩ | ⟨S, hSW, hSc, hSmono⟩
          · refine Or.inl ⟨insert v S, ?_, ?_, ?_⟩
            · exact Finset.insert_subset hv (hSW.trans (hWV'.trans (Finset.erase_subset v V)))
            · have hvS : v ∉ S := fun h => (Finset.mem_erase.mp (hWV' (hSW h))).1 rfl
              rw [Finset.card_insert_of_notMem hvS, hSc]
              omega
            · intro e he hcard
              by_cases hve : v ∈ e
              · have he' : e.erase v ⊆ W := by
                  intro x hx
                  have hx' := Finset.mem_erase.mp hx
                  have := he hx'.2
                  rcases Finset.mem_insert.mp this with rfl | hxS
                  · exact (hx'.1 rfl).elim
                  · exact hSW hxS
                have hcard' : (e.erase v).card = d := by
                  rw [Finset.card_erase_of_mem hve]
                  omega
                have hcol := hWmono (e.erase v) he' hcard'
                simpa [c', Finset.insert_erase hve] using hcol
              · have he' : e ⊆ S := by
                  intro x hx
                  rcases Finset.mem_insert.mp (he hx) with rfl | hxS
                  · exact (hve hx).elim
                  · exact hxS
                exact hSmono e he' hcard
          · exact Or.inr ⟨S, hSW.trans (hWV'.trans (Finset.erase_subset v V)), hSc, hSmono⟩
        · rcases hR₂ α W (by omega) c with ⟨S, hSW, hSc, hSmono⟩ | ⟨S, hSW, hSc, hSmono⟩
          · exact Or.inl ⟨S, hSW.trans (hWV'.trans (Finset.erase_subset v V)), hSc, hSmono⟩
          · refine Or.inr ⟨insert v S, ?_, ?_, ?_⟩
            · exact Finset.insert_subset hv (hSW.trans (hWV'.trans (Finset.erase_subset v V)))
            · have hvS : v ∉ S := fun h => (Finset.mem_erase.mp (hWV' (hSW h))).1 rfl
              rw [Finset.card_insert_of_notMem hvS, hSc]
              omega
            · intro e he hcard
              by_cases hve : v ∈ e
              · have he' : e.erase v ⊆ W := by
                  intro x hx
                  have hx' := Finset.mem_erase.mp hx
                  have := he hx'.2
                  rcases Finset.mem_insert.mp this with rfl | hxS
                  · exact (hx'.1 rfl).elim
                  · exact hSW hxS
                have hcard' : (e.erase v).card = d := by
                  rw [Finset.card_erase_of_mem hve]
                  omega
                have hcol := hWmono (e.erase v) he' hcard'
                simpa [c', Finset.insert_erase hve] using hcol
              · have he' : e ⊆ S := by
                  intro x hx
                  rcases Finset.mem_insert.mp (he hx) with rfl | hxS
                  · exact (hve hx).elim
                  · exact hxS
                exact hSmono e he' hcard
    exact key (m₁ + m₂) m₁ m₂ rfl

private lemma ramsey_orderEmb (d m : ℕ) :
    ∃ R : ℕ, ∀ c : (Fin d ↪o Fin R) → Bool,
      ∃ (idx : Fin m ↪o Fin R) (b : Bool),
        ∀ f : Fin d ↪o Fin m, c (f.trans idx) = b := by
  obtain ⟨R, hR⟩ := hypergraph_ramsey d m m
  refine ⟨R, ?_⟩
  intro c
  let cSet : Finset (Fin R) → Bool := fun s =>
    if h : s.card = d then c (s.orderEmbOfFin h) else false
  have hcard : R ≤ (Finset.univ : Finset (Fin R)).card := by simp
  rcases hR (Fin R) Finset.univ hcard cSet with ⟨S, _, hSc, hSm⟩ | ⟨S, _, hSc, hSm⟩
  · refine ⟨S.orderEmbOfFin hSc, true, ?_⟩
    intro f
    let g := f.trans (S.orderEmbOfFin hSc)
    let e := Finset.univ.image g
    have heS : e ⊆ S := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.orderEmbOfFin_mem S hSc (f i)
    have hec : e.card = d := by
      rw [Finset.card_image_of_injective _ g.injective]
      simp
    have hmono := hSm e heS hec
    simp only [cSet, hec, ↓reduceDIte] at hmono
    have heq : e.orderEmbOfFin hec = g := by
      apply RelEmbedding.ext
      intro i
      exact congrFun (Finset.orderEmbOfFin_unique hec
        (fun j => Finset.mem_image_of_mem g (Finset.mem_univ j))
        (fun a b hab => (OrderEmbedding.lt_iff_lt g).mpr hab)).symm i
    simpa [heq, g] using hmono
  · refine ⟨S.orderEmbOfFin hSc, false, ?_⟩
    intro f
    let g := f.trans (S.orderEmbOfFin hSc)
    let e := Finset.univ.image g
    have heS : e ⊆ S := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.orderEmbOfFin_mem S hSc (f i)
    have hec : e.card = d := by
      rw [Finset.card_image_of_injective _ g.injective]
      simp
    have hmono := hSm e heS hec
    simp only [cSet, hec, ↓reduceDIte] at hmono
    have heq : e.orderEmbOfFin hec = g := by
      apply RelEmbedding.ext
      intro i
      exact congrFun (Finset.orderEmbOfFin_unique hec
        (fun j => Finset.mem_image_of_mem g (Finset.mem_univ j))
        (fun a b hab => (OrderEmbedding.lt_iff_lt g).mpr hab)).symm i
    simpa [heq, g] using hmono

/- ## Module 2: 4x4 Orientation Determinant and Transversal Counting -/

private def mat4 (v : Fin 4 → ℝ^3) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j =>
    match j with
    | ⟨0, _⟩ => 1
    | ⟨1, _⟩ => v i 0
    | ⟨2, _⟩ => v i 1
    | ⟨3, _⟩ => v i 2

private def det4 (v : Fin 4 → ℝ^3) : ℝ := (mat4 v).det

private lemma det4_permute (v : Fin 4 → ℝ^3) (σ : Equiv.Perm (Fin 4)) :
    det4 (v ∘ σ) = (Equiv.Perm.sign σ : ℝ) * det4 v := by
  unfold det4
  have hmat : mat4 (v ∘ σ) = (mat4 v).submatrix σ id := by
    ext i j; rfl
  rw [hmat, Matrix.det_permute]

private lemma det4_ne_zero_of_affineIndependent {v : Fin 4 → ℝ^3}
    (hv : AffineIndependent ℝ v) : det4 v ≠ 0 := by
  intro hdet
  have hdetT : (mat4 v)ᵀ.det = 0 := by rw [Matrix.det_transpose]; exact hdet
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetT
  have hsum : ∑ i : Fin 4, w i = 0 := by
    have h0 := congrFun hw 0
    simpa [Matrix.mulVec, dotProduct, mat4] using h0
  have hvec : ∑ i : Fin 4, w i • v i = 0 := by
    ext k
    fin_cases k
    · have h1 := congrFun hw 1
      simpa [Matrix.mulVec, dotProduct, mat4, mul_comm] using h1
    · have h2 := congrFun hw 2
      simpa [Matrix.mulVec, dotProduct, mat4, mul_comm] using h2
    · have h3 := congrFun hw 3
      simpa [Matrix.mulVec, dotProduct, mat4, mul_comm] using h3
  have hw_all : ∀ i : Fin 4, w i = 0 := by
    have hli := (affineIndependent_iff_linearIndependent_vsub ℝ v (0 : Fin 4)).mp hv
    have hsub0 : ∑ i : {i : Fin 4 // i ≠ 0}, w i.1 • (v i.1 -ᵥ v 0) = 0 := by
      have hfull : ∑ i : Fin 4, w i • (v i - v 0) = 0 := by
        simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hvec, hsum, zero_smul, sub_zero]
      have hsplit : ∑ i : Fin 4, w i • (v i - v 0) =
          w 0 • (v 0 - v 0) + ∑ i ∈ Finset.univ.erase (0 : Fin 4), w i • (v i - v 0) :=
        (Finset.add_sum_erase Finset.univ (fun i => w i • (v i - v 0)) (Finset.mem_univ 0)).symm
      rw [sub_self, smul_zero, zero_add] at hsplit
      rw [hsplit] at hfull
      have heq : ∑ i : {i : Fin 4 // i ≠ 0}, w i.1 • (v i.1 -ᵥ v 0) =
          ∑ i ∈ Finset.univ.erase (0 : Fin 4), w i • (v i - v 0) := by
        symm
        refine Finset.sum_bij (fun (i : Fin 4) (hi : i ∈ Finset.univ.erase 0) =>
            (⟨i, (Finset.mem_erase.mp hi).1⟩ : {i : Fin 4 // i ≠ 0})) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro _ _ _ _ h; exact congrArg Subtype.val h
        · intro ⟨i, hi⟩ _
          exact ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩, rfl⟩
        · intro _ _; rfl
      rw [heq]; exact hfull
    have hnz : ∀ i : Fin 4, i ≠ 0 → w i = 0 := fun i hi =>
      Fintype.linearIndependent_iff.mp hli (fun j => w j.1) hsub0 ⟨i, hi⟩
    intro i
    by_cases hi : i = 0
    · subst hi
      rw [Fin.sum_univ_four] at hsum
      rw [hnz 1 (by decide), hnz 2 (by decide), hnz 3 (by decide)] at hsum
      linarith
    · exact hnz i hi
  exact hw0 (funext hw_all)

private lemma det4_ne_zero_of_generalPosition {X : Finset (ℝ^3)}
    (hX : IsInGeneralPosition X) {v : Fin 4 → ℝ^3}
    (hmem : ∀ i, v i ∈ X) (hinj : Function.Injective v) : det4 v ≠ 0 := by
  apply det4_ne_zero_of_affineIndependent
  let Y : Finset (ℝ^3) := Finset.univ.image v
  have hYX : Y ⊆ X := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hmem i
  have hYc : Y.card ≤ 3 + 1 := by
    rw [Finset.card_image_of_injective _ hinj]; simp
  have haff := hX Y hYX hYc
  have hinj' : Function.Injective (fun i : Fin 4 =>
      (⟨v i, Finset.mem_image_of_mem v (Finset.mem_univ i)⟩ : ↥(Y : Set (ℝ^3)))) := by
    intro i j hij
    exact hinj (congrArg Subtype.val hij)
  exact haff.comp_embedding ⟨_, hinj'⟩

private def signVal (b : Bool) : ℝ := if b then 1 else -1

private lemma signVal_mul_pos {b : Bool} {x : ℝ} (hx : x ≠ 0) (hb : decide (0 < x) = b) :
    0 < signVal b * x := by
  cases b with
  | true =>
    simp only [signVal, ↓reduceIte, one_mul]
    exact of_decide_eq_true hb
  | false =>
    simp only [signVal, Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul, Left.neg_pos_iff]
    have hle : ¬ (0 < x) := of_decide_eq_false hb
    exact lt_of_le_of_ne (not_lt.mp hle) hx

/-- Moving the last entry of a 4-tuple into its sorted position changes `det4` by `(-1)^cnt`. -/
private lemma det4_insert_sign {L : ℕ} (w : Fin L → ℝ^3) (σ : Bool)
    (hmono : ∀ f : Fin 4 ↪o Fin L, 0 < signVal σ * det4 (fun j => w (f j)))
    {p r s u : Fin L} (hpr : p < r) (hrs : r < s)
    (hup : u ≠ p) (hur : u ≠ r) (hus : u ≠ s) :
    0 < signVal σ * ((-1 : ℝ) ^ (Finset.filter (fun d : Fin L => u < d) {p, r, s}).card) *
      det4 ![w p, w r, w s, w u] := by
  have hps : p < s := hpr.trans hrs
  have hcard3 : ({p, r, s} : Finset (Fin L)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hrs.ne]
    · simp [hpr.ne, hps.ne]
  by_cases h1 : u < p
  · have hf : (Finset.filter (fun d : Fin L => u < d) {p, r, s}).card = 3 := by
      have heq : Finset.filter (fun d : Fin L => u < d) {p, r, s} = {p, r, s} := by
        apply Finset.filter_true_of_mem
        intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl
        · exact h1
        · exact h1.trans hpr
        · exact h1.trans hps
      rw [heq, hcard3]
    let emb : Fin 4 ↪o Fin L := OrderEmbedding.ofStrictMono ![u, p, r, s] (by
      intro a b hab; fin_cases a <;> fin_cases b <;> simp_all [h1, hpr, hrs, hps, h1.trans hpr, h1.trans hps])
    have hpos := hmono emb
    let τ : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3
    have hcomp : ![w p, w r, w s, w u] = (fun j => w (emb j)) ∘ τ := by
      have h0 : τ 0 = 1 := by decide
      have h1 : τ 1 = 2 := by decide
      have h2 : τ 2 = 3 := by decide
      have h3 : τ 3 = 0 := by decide
      funext i; fin_cases i
      · change w p = w (emb (τ 0)); rw [h0]; rfl
      · change w r = w (emb (τ 1)); rw [h1]; rfl
      · change w s = w (emb (τ 2)); rw [h2]; rfl
      · change w u = w (emb (τ 3)); rw [h3]; rfl
    have hsign : (Equiv.Perm.sign τ : ℝ) = -1 := by
      have : Equiv.Perm.sign τ = -1 := by decide
      rw [this]; norm_num
    rw [hcomp, det4_permute, hsign, hf]
    norm_num
    linarith
  · have hpu : p < u := lt_of_le_of_ne (not_lt.mp h1) hup.symm
    by_cases h2 : u < r
    · have hf : (Finset.filter (fun d : Fin L => u < d) {p, r, s}).card = 2 := by
        have heq : Finset.filter (fun d : Fin L => u < d) {p, r, s} = {r, s} := by
          ext d; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | rfl | rfl, hd⟩
            · exact (lt_asymm hpu hd).elim
            · exact Or.inl rfl
            · exact Or.inr rfl
          · rintro (rfl | rfl)
            · exact ⟨Or.inr (Or.inl rfl), h2⟩
            · exact ⟨Or.inr (Or.inr rfl), h2.trans hrs⟩
        rw [heq, Finset.card_pair hrs.ne]
      let emb : Fin 4 ↪o Fin L := OrderEmbedding.ofStrictMono ![p, u, r, s] (by
        intro a b hab; fin_cases a <;> fin_cases b <;> simp_all [hpu, h2, hrs, hpr, hps, h2.trans hrs])
      have hpos := hmono emb
      let τ : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 2 3
      have hcomp : ![w p, w r, w s, w u] = (fun j => w (emb j)) ∘ τ := by
        have h0 : τ 0 = 0 := by decide
        have h1 : τ 1 = 2 := by decide
        have h2 : τ 2 = 3 := by decide
        have h3 : τ 3 = 1 := by decide
        funext i; fin_cases i
        · change w p = w (emb (τ 0)); rw [h0]; rfl
        · change w r = w (emb (τ 1)); rw [h1]; rfl
        · change w s = w (emb (τ 2)); rw [h2]; rfl
        · change w u = w (emb (τ 3)); rw [h3]; rfl
      have hsign : (Equiv.Perm.sign τ : ℝ) = 1 := by
        have : Equiv.Perm.sign τ = 1 := by decide
        rw [this]; norm_num
      rw [hcomp, det4_permute, hsign, hf]
      norm_num
      linarith
    · have hru : r < u := lt_of_le_of_ne (not_lt.mp h2) hur.symm
      by_cases h3 : u < s
      · have hf : (Finset.filter (fun d : Fin L => u < d) {p, r, s}).card = 1 := by
          have heq : Finset.filter (fun d : Fin L => u < d) {p, r, s} = {s} := by
            ext d; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl | rfl, hd⟩
              · exact (lt_asymm hpu hd).elim
              · exact (lt_asymm hru hd).elim
              · rfl
            · rintro rfl
              exact ⟨Or.inr (Or.inr rfl), h3⟩
          rw [heq, Finset.card_singleton]
        let emb : Fin 4 ↪o Fin L := OrderEmbedding.ofStrictMono ![p, r, u, s] (by
          intro a b hab; fin_cases a <;> fin_cases b <;> simp_all [hpr, hru, h3, hpu, hps])
        have hpos := hmono emb
        let τ : Equiv.Perm (Fin 4) := Equiv.swap 2 3
        have hcomp : ![w p, w r, w s, w u] = (fun j => w (emb j)) ∘ τ := by
          have h0 : τ 0 = 0 := by decide
          have h1 : τ 1 = 1 := by decide
          have h2 : τ 2 = 3 := by decide
          have h3 : τ 3 = 2 := by decide
          funext i; fin_cases i
          · change w p = w (emb (τ 0)); rw [h0]; rfl
          · change w r = w (emb (τ 1)); rw [h1]; rfl
          · change w s = w (emb (τ 2)); rw [h2]; rfl
          · change w u = w (emb (τ 3)); rw [h3]; rfl
        have hsign : (Equiv.Perm.sign τ : ℝ) = -1 := by
          have : Equiv.Perm.sign τ = -1 := by decide
          rw [this]; norm_num
        rw [hcomp, det4_permute, hsign, hf]
        norm_num
        linarith
      · have hsu : s < u := lt_of_le_of_ne (not_lt.mp h3) hus.symm
        have hf : (Finset.filter (fun d : Fin L => u < d) {p, r, s}).card = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro d hd
          simp only [Finset.mem_insert, Finset.mem_singleton] at hd
          rcases hd with rfl | rfl | rfl
          · exact not_lt.mpr hpu.le
          · exact not_lt.mpr hru.le
          · exact not_lt.mpr hsu.le
        let emb : Fin 4 ↪o Fin L := OrderEmbedding.ofStrictMono ![p, r, s, u] (by
          intro a b hab; fin_cases a <;> fin_cases b <;> simp_all [hpr, hrs, hsu, hps, hpu, hru])
        have hpos := hmono emb
        have hcomp : ![w p, w r, w s, w u] = fun j => w (emb j) := by
          funext i; fin_cases i <;> rfl
        rw [hcomp, hf]
        norm_num
        linarith

/-- Extract `k + 1` anchors `h` and `k` disjoint clusters `U` of size `≥ N / C` with alternating
determinant signs across anchors. -/
private lemma extract_anchors_clusters (k : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ X : Finset (ℝ^3), IsInGeneralPosition X → C ≤ X.card →
      ∃ (h : Fin (k + 1) → ℝ^3) (U : Fin k → Finset (ℝ^3)) (σ : Bool),
        (∀ i, U i ⊆ X) ∧
        (∀ i, X.card ≤ C * (U i).card) ∧
        (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧
        ∀ (p r s : Fin (k + 1)), p < r → r < s → ∀ (i : Fin k), ∀ u ∈ U i,
          0 < signVal σ *
            ((-1 : ℝ) ^ (Finset.filter (fun d : Fin (k + 1) => i.val < d.val) {p, r, s}).card) *
            det4 ![h p, h r, h s, u] := by
  classical
  let L := 2 * k + 1
  obtain ⟨R, hRam⟩ := ramsey_orderEmb 4 L
  -- R ≥ L ≥ 1 because constant coloring yields an order embedding Fin L ↪o Fin R
  have hRL : L ≤ R := by
    obtain ⟨idx, _, _⟩ := hRam (fun _ => true)
    have hle := Fintype.card_le_of_injective idx idx.injective
    simpa using hle
  have hRpos : 0 < R := by omega
  let D : ℕ := 2 * Fintype.card (Fin L ↪o Fin R)
  have hDpos : 0 < D := by
    obtain ⟨idx, _, _⟩ := hRam (fun _ => true)
    have hpos : 0 < Fintype.card (Fin L ↪o Fin R) := Fintype.card_pos_iff.mpr ⟨idx⟩
    dsimp [D]; omega
  let C : ℕ := 2 * R * D
  have hCpos : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hCpos, ?_⟩
  intro X hX hXC
  let q : ℕ := X.card / R
  have hqpos : 0 < q := by
    dsimp [q]
    exact Nat.div_pos (le_trans (by dsimp [C]; nlinarith) hXC) hRpos
  have hXle : X.card ≤ 2 * R * q := by
    have hdiv : R * q + X.card % R = X.card := Nat.div_add_mod X.card R
    have hmod : X.card % R < R := Nat.mod_lt X.card hRpos
    nlinarith
  -- Partition X into R disjoint blocks of size q
  let eX : Fin X.card ≃ ↥(X : Set (ℝ^3)) := (X.equivFin).symm
  let blkFn (r : Fin R) (j : Fin q) : ℝ^3 :=
    (eX ⟨r.val * q + j.val, by
      have h1 : (r.val + 1) * q ≤ R * q := Nat.mul_le_mul_right q r.isLt
      have h2 : R * q ≤ X.card := Nat.mul_div_le X.card R
      nlinarith [j.isLt]⟩).val
  have hblk_inj : ∀ r₁ j₁ r₂ j₂, blkFn r₁ j₁ = blkFn r₂ j₂ → r₁ = r₂ ∧ j₁ = j₂ := by
    intro r₁ j₁ r₂ j₂ heq
    have hsub : eX ⟨r₁.val * q + j₁.val, _⟩ = eX ⟨r₂.val * q + j₂.val, _⟩ := Subtype.ext heq
    have hfin := eX.injective hsub
    have hval : r₁.val * q + j₁.val = r₂.val * q + j₂.val := congrArg Fin.val hfin
    have hr : r₁.val = r₂.val := by
      have hdiv1 : (r₁.val * q + j₁.val) / q = r₁.val := by
        rw [mul_comm r₁.val q, Nat.mul_add_div hqpos, Nat.div_eq_of_lt j₁.isLt, add_zero]
      have hdiv2 : (r₂.val * q + j₂.val) / q = r₂.val := by
        rw [mul_comm r₂.val q, Nat.mul_add_div hqpos, Nat.div_eq_of_lt j₂.isLt, add_zero]
      rw [← hdiv1, hval, hdiv2]
    exact ⟨Fin.ext hr, Fin.ext (by nlinarith [hr])⟩
  let B : Fin R → Finset (ℝ^3) := fun r => Finset.univ.image (blkFn r)
  have hBsub : ∀ r, B r ⊆ X := by
    intro r x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact (eX _).property
  have hBcard : ∀ r, (B r).card = q := by
    intro r
    rw [Finset.card_image_of_injective]
    · simp
    · intro j₁ j₂ h; exact (hblk_inj r j₁ r j₂ h).2
  have hBdisj : ∀ r₁ r₂, r₁ ≠ r₂ → Disjoint (B r₁) (B r₂) := by
    intro r₁ r₂ hne
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    obtain ⟨j₁, _, rfl⟩ := Finset.mem_image.mp hx₁
    obtain ⟨j₂, _, heq⟩ := Finset.mem_image.mp hx₂
    exact hne (hblk_inj r₂ j₂ r₁ j₁ heq).1.symm
  -- Transversals T = Fintype.piFinset B
  let T : Finset (Fin R → ℝ^3) := Fintype.piFinset B
  have hTcard : T.card = q ^ R := by
    rw [Fintype.card_piFinset]
    simp [hBcard]
  have hTinj : ∀ τ ∈ T, Function.Injective τ := by
    intro τ hτ r₁ r₂ heq
    by_contra hne
    have h1 : τ r₁ ∈ B r₁ := Fintype.mem_piFinset.mp hτ r₁
    have h2 : τ r₂ ∈ B r₂ := Fintype.mem_piFinset.mp hτ r₂
    exact Finset.disjoint_left.mp (hBdisj r₁ r₂ hne) h1 (heq ▸ h2)
  have hTmem : ∀ τ ∈ T, ∀ r, τ r ∈ X := by
    intro τ hτ r
    exact hBsub r (Fintype.mem_piFinset.mp hτ r)
  -- Assign each transversal a monochromatic L-embedding and sign
  let col (τ : Fin R → ℝ^3) (f : Fin 4 ↪o Fin R) : Bool :=
    decide (0 < det4 (fun i => τ (f i)))
  let assign (τ : Fin R → ℝ^3) : (Fin L ↪o Fin R) × Bool :=
    ⟨Classical.choose (hRam (col τ)), Classical.choose (Classical.choose_spec (hRam (col τ)))⟩
  have hassign_spec (τ : Fin R → ℝ^3) (f : Fin 4 ↪o Fin L) :
      col τ (f.trans (assign τ).1) = (assign τ).2 :=
    Classical.choose_spec (Classical.choose_spec (hRam (col τ))) f
  -- Pigeonhole 1 over (Fin L ↪o Fin R) × Bool
  have hD_eq : (Finset.univ : Finset ((Fin L ↪o Fin R) × Bool)).card = D := by
    simp [D, mul_comm]
  have hT_nonempty : (Finset.univ : Finset ((Fin L ↪o Fin R) × Bool)).Nonempty :=
    Finset.card_pos.mp (by rw [hD_eq]; exact hDpos)
  have hexT1 : ∃ p : (Fin L ↪o Fin R) × Bool,
      T.card ≤ D * (T.filter (fun τ => assign τ = p)).card := by
    by_contra hno
    push_neg at hno
    have hsum : T.card = ∑ p ∈ (Finset.univ : Finset ((Fin L ↪o Fin R) × Bool)),
        (T.filter (fun τ => assign τ = p)).card := by
      rw [← Finset.card_biUnion]
      · congr 1; ext τ; simp
      · intro p₁ _ p₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro τ h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    have hlt : D * T.card < D * T.card := by
      calc D * T.card = ∑ p ∈ (Finset.univ : Finset ((Fin L ↪o Fin R) × Bool)),
              D * (T.filter (fun τ => assign τ = p)).card := by rw [hsum, Finset.mul_sum]
        _ < ∑ _p ∈ (Finset.univ : Finset ((Fin L ↪o Fin R) × Bool)), T.card :=
              Finset.sum_lt_sum_of_nonempty hT_nonempty (fun p _ => hno p)
        _ = D * T.card := by simp [hD_eq]
    exact lt_irrefl _ hlt
  obtain ⟨⟨idx, σ⟩, hT1_le⟩ := hexT1
  let T₁ := T.filter (fun τ => assign τ = (idx, σ))
  -- Variable positions: idx (2*i + 1) for i : Fin k
  let varPos (i : Fin k) : Fin R := idx ⟨2 * i.val + 1, by omega⟩
  have hvarPos_inj : Function.Injective varPos := by
    intro i₁ i₂ h
    have h' := congrArg Fin.val (idx.injective h)
    change 2 * i₁.val + 1 = 2 * i₂.val + 1 at h'
    exact Fin.ext (by omega)
  let Vpos : Finset (Fin R) := Finset.univ.image varPos
  have hVpos_card : Vpos.card = k := by
    rw [Finset.card_image_of_injective _ hvarPos_inj]; simp
  let Fpos : Finset (Fin R) := Finset.univ \ Vpos
  have hFpos_card : Fpos.card = R - k := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hVpos_card]
  -- Project T1 onto Fpos
  let proj (τ : Fin R → ℝ^3) : {r : Fin R // r ∈ Fpos} → ℝ^3 := fun r => τ r.1
  let Pset : Finset ({r : Fin R // r ∈ Fpos} → ℝ^3) :=
    Fintype.piFinset (fun r : {r : Fin R // r ∈ Fpos} => B r.1)
  have hPcard : Pset.card = q ^ (R - k) := by
    rw [Fintype.card_piFinset]
    simp only [hBcard, Finset.prod_const, Finset.card_univ, Fintype.card_coe, hFpos_card]
  have hPmaps : ∀ τ ∈ T₁, proj τ ∈ Pset := by
    intro τ hτ
    rw [Fintype.mem_piFinset]
    intro r
    exact Fintype.mem_piFinset.mp (Finset.mem_filter.mp hτ).1 r.1
  have hPne : Pset.Nonempty := Finset.card_pos.mp (by rw [hPcard]; exact pow_pos hqpos _)
  -- Pigeonhole 2 over Pset
  have hexT2 : ∃ τ₀ ∈ Pset, T₁.card ≤ Pset.card * (T₁.filter (fun τ => proj τ = τ₀)).card := by
    by_contra hno
    push_neg at hno
    have hsum : T₁.card = ∑ τ₀ ∈ Pset, (T₁.filter (fun τ => proj τ = τ₀)).card := by
      rw [← Finset.card_biUnion]
      · congr 1; ext τ; simp only [Finset.mem_biUnion, Finset.mem_filter]
        exact ⟨fun h => ⟨proj τ, hPmaps τ h, h, rfl⟩, fun ⟨_, _, h, _⟩ => h⟩
      · intro a _ b _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro τ h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    have hlt : Pset.card * T₁.card < Pset.card * T₁.card := by
      calc Pset.card * T₁.card = ∑ τ₀ ∈ Pset,
              Pset.card * (T₁.filter (fun τ => proj τ = τ₀)).card := by rw [hsum, Finset.mul_sum]
        _ < ∑ _τ₀ ∈ Pset, T₁.card := Finset.sum_lt_sum_of_nonempty hPne hno
        _ = Pset.card * T₁.card := by simp
    exact lt_irrefl _ hlt
  obtain ⟨τ₀, _, hT2_le⟩ := hexT2
  let T₂ := T₁.filter (fun τ => proj τ = τ₀)
  have hqk_le : q ^ k ≤ D * T₂.card := by
    have hRk : R = (R - k) + k := by omega
    have hmul : q ^ (R - k) * q ^ k ≤ q ^ (R - k) * (D * T₂.card) := by
      calc q ^ (R - k) * q ^ k = q ^ R := by rw [← pow_add, ← hRk]
        _ = T.card := hTcard.symm
        _ ≤ D * T₁.card := hT1_le
        _ ≤ D * (Pset.card * T₂.card) := Nat.mul_le_mul_left D hT2_le
        _ = q ^ (R - k) * (D * T₂.card) := by rw [hPcard]; ring
    exact Nat.le_of_mul_le_mul_left hmul (pow_pos hqpos _)
  -- Anchors h j = τ₀ (idx (2*j)) and clusters U i = T₂.image (fun τ => τ (varPos i))
  let ancIdx (j : Fin (k + 1)) : Fin L :=
    ⟨2 * j.val, Nat.lt_succ_of_le (Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ j.isLt))⟩
  have hanc_mem (j : Fin (k + 1)) : idx (ancIdx j) ∈ Fpos := by
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hmem
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
    have h' : (⟨2 * i.val + 1, by omega⟩ : Fin L).val = (ancIdx j).val :=
      congrArg Fin.val (idx.injective hi)
    change 2 * i.val + 1 = 2 * j.val at h'
    omega
  let h : Fin (k + 1) → ℝ^3 := fun j => τ₀ ⟨idx (ancIdx j), hanc_mem j⟩
  let U : Fin k → Finset (ℝ^3) := fun i => T₂.image (fun τ => τ (varPos i))
  refine ⟨h, U, σ, ?_, ?_, ?_, ?_⟩
  · -- U i ⊆ X
    intro i u hu
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hu
    exact hTmem τ (Finset.mem_filter.mp (Finset.mem_filter.mp hτ).1).1 (varPos i)
  · -- X.card ≤ C * (U i).card
    intro i
    -- Embed T₂ into Fintype.piFinset (fun i' : Fin k => if i' = i then U i else B (varPos i'))
    let box (i' : Fin k) : Finset (ℝ^3) := if i' = i then U i else B (varPos i')
    let Q := Fintype.piFinset box
    have hT2_inj : Set.InjOn (fun (τ : Fin R → ℝ^3) (i' : Fin k) => τ (varPos i')) (T₂ : Set (Fin R → ℝ^3)) := by
      intro τ₁ hτ₁ τ₂ hτ₂ heq
      funext r
      by_cases hr : r ∈ Vpos
      · obtain ⟨i', _, rfl⟩ := Finset.mem_image.mp hr
        exact congrFun heq i'
      · have hrF : r ∈ Fpos := Finset.mem_sdiff.mpr ⟨Finset.mem_univ r, hr⟩
        have h1 : proj τ₁ ⟨r, hrF⟩ = τ₀ ⟨r, hrF⟩ := congrFun (Finset.mem_filter.mp hτ₁).2 ⟨r, hrF⟩
        have h2 : proj τ₂ ⟨r, hrF⟩ = τ₀ ⟨r, hrF⟩ := congrFun (Finset.mem_filter.mp hτ₂).2 ⟨r, hrF⟩
        exact h1.trans h2.symm
    have hT2_sub : T₂.image (fun (τ : Fin R → ℝ^3) (i' : Fin k) => τ (varPos i')) ⊆ Q := by
      intro f hf
      obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hf
      rw [Fintype.mem_piFinset]
      intro i'
      by_cases hi' : i' = i
      · subst hi'; simp only [box, ↓reduceIte]; exact Finset.mem_image_of_mem _ hτ
      · simp only [box, hi', ↓reduceIte]
        exact Fintype.mem_piFinset.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hτ).1).1 (varPos i')
    have hT2_le_Q : T₂.card ≤ (U i).card * q ^ (k - 1) := by
      calc T₂.card = (T₂.image (fun (τ : Fin R → ℝ^3) (i' : Fin k) => τ (varPos i'))).card :=
            (Finset.card_image_of_injOn hT2_inj).symm
        _ ≤ Q.card := Finset.card_le_card hT2_sub
        _ = ∏ i' : Fin k, (box i').card := Fintype.card_piFinset box
        _ = (U i).card * ∏ i' ∈ Finset.univ.erase i, (box i').card := by
            rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
            simp [box]
        _ = (U i).card * q ^ (k - 1) := by
            congr 1
            have hprod : ∀ i' ∈ Finset.univ.erase i, (box i').card = q := by
              intro i' hi'
              simp [box, (Finset.mem_erase.mp hi').1, hBcard]
            rw [Finset.prod_congr rfl hprod, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
              Finset.card_univ, Fintype.card_fin]
    have hq_le : q ≤ D * (U i).card := by
      have hkpos : 1 ≤ k := Nat.succ_le_of_lt i.pos
      have hmul : q ^ (k - 1) * q ≤ q ^ (k - 1) * (D * (U i).card) := by
        calc q ^ (k - 1) * q = q ^ k := by rw [← pow_succ, Nat.sub_add_cancel hkpos]
          _ ≤ D * T₂.card := hqk_le
          _ ≤ D * ((U i).card * q ^ (k - 1)) := Nat.mul_le_mul_left D hT2_le_Q
          _ = q ^ (k - 1) * (D * (U i).card) := by ring
      exact Nat.le_of_mul_le_mul_left hmul (pow_pos hqpos _)
    calc X.card ≤ 2 * R * q := hXle
      _ ≤ 2 * R * (D * (U i).card) := Nat.mul_le_mul_left _ hq_le
      _ = C * (U i).card := by dsimp [C]; ring
  · -- Disjoint (U i) (U j)
    intro i j hij
    have hsubi : U i ⊆ B (varPos i) := by
      intro u hu
      obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hu
      exact Fintype.mem_piFinset.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hτ).1).1 (varPos i)
    have hsubj : U j ⊆ B (varPos j) := by
      intro u hu
      obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hu
      exact Fintype.mem_piFinset.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hτ).1).1 (varPos j)
    exact (hBdisj (varPos i) (varPos j) (fun heq => hij (hvarPos_inj heq))).mono hsubi hsubj
  · -- Determinant sign across anchors
    intro p r s hpr hrs i u hu
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hu
    have hτT1 : τ ∈ T₁ := (Finset.mem_filter.mp hτ).1
    have hτT : τ ∈ T := (Finset.mem_filter.mp hτT1).1
    have hτass : assign τ = (idx, σ) := (Finset.mem_filter.mp hτT1).2
    have hτproj : proj τ = τ₀ := (Finset.mem_filter.mp hτ).2
    let w : Fin L → ℝ^3 := fun a => τ (idx a)
    have hw_mono : ∀ f : Fin 4 ↪o Fin L, 0 < signVal σ * det4 (fun j => w (f j)) := by
      intro f
      have hcol := hassign_spec τ f
      rw [hτass] at hcol
      apply signVal_mul_pos _ hcol
      apply det4_ne_zero_of_generalPosition hX
      · intro j; exact hTmem τ hτT (idx (f j))
      · intro a b hab; exact f.injective (idx.injective (hTinj τ hτT hab))
    let pL : Fin L := ancIdx p
    let rL : Fin L := ancIdx r
    let sL : Fin L := ancIdx s
    let uL : Fin L := ⟨2 * i.val + 1, by omega⟩
    have hwp : w pL = h p := congrFun hτproj ⟨idx pL, hanc_mem p⟩
    have hwr : w rL = h r := congrFun hτproj ⟨idx rL, hanc_mem r⟩
    have hws : w sL = h s := congrFun hτproj ⟨idx sL, hanc_mem s⟩
    have hwu : w uL = τ (varPos i) := rfl
    have hcard_eq :
        (Finset.filter (fun d : Fin L => uL < d) {pL, rL, sL}).card =
        (Finset.filter (fun d : Fin (k + 1) => i.val < d.val) {p, r, s}).card := by
      let emb : Fin (k + 1) ↪ Fin L := ⟨ancIdx, by
        intro a b hab
        have h' : (ancIdx a).val = (ancIdx b).val := congrArg Fin.val hab
        change 2 * a.val = 2 * b.val at h'
        exact Fin.ext (by omega)⟩
      have hmap : Finset.filter (fun d : Fin L => uL < d) {pL, rL, sL} =
          (Finset.filter (fun d : Fin (k + 1) => i.val < d.val) {p, r, s}).map emb := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.mem_map]
        constructor
        · rintro ⟨hx_mem, hx_lt⟩
          rcases hx_mem with hx | hx | hx
          · refine ⟨p, ⟨Or.inl rfl, ?_⟩, ?_⟩
            · rw [hx] at hx_lt; change 2 * i.val + 1 < 2 * p.val at hx_lt; omega
            · exact hx.symm
          · refine ⟨r, ⟨Or.inr (Or.inl rfl), ?_⟩, ?_⟩
            · rw [hx] at hx_lt; change 2 * i.val + 1 < 2 * r.val at hx_lt; omega
            · exact hx.symm
          · refine ⟨s, ⟨Or.inr (Or.inr rfl), ?_⟩, ?_⟩
            · rw [hx] at hx_lt; change 2 * i.val + 1 < 2 * s.val at hx_lt; omega
            · exact hx.symm
        · rintro ⟨d, ⟨hd_mem, hd_lt⟩, rfl⟩
          rcases hd_mem with rfl | rfl | rfl
          · exact ⟨Or.inl rfl, by change 2 * i.val + 1 < 2 * d.val; omega⟩
          · exact ⟨Or.inr (Or.inl rfl), by change 2 * i.val + 1 < 2 * d.val; omega⟩
          · exact ⟨Or.inr (Or.inr rfl), by change 2 * i.val + 1 < 2 * d.val; omega⟩
      rw [hmap, Finset.card_map]
    have hdet := det4_insert_sign w σ hw_mono
      (show pL < rL by change 2 * p.val < 2 * r.val; have : p.val < r.val := hpr; omega)
      (show rL < sL by change 2 * r.val < 2 * s.val; have : r.val < s.val := hrs; omega)
      (by intro heq; have h' : uL.val = pL.val := congrArg Fin.val heq; change 2 * i.val + 1 = 2 * p.val at h'; omega)
      (by intro heq; have h' : uL.val = rL.val := congrArg Fin.val heq; change 2 * i.val + 1 = 2 * r.val at h'; omega)
      (by intro heq; have h' : uL.val = sL.val := congrArg Fin.val heq; change 2 * i.val + 1 = 2 * s.val at h'; omega)
    rw [hwp, hwr, hws, hwu, hcard_eq] at hdet
    exact hdet

/- ## Module 3: Anchor Affine Forms, Generic Perturbation, and Orthants -/

private lemma inner_eq_sum_fin3 (u v : ℝ^3) :
    inner ℝ u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

private lemma det4_affine (a b c : ℝ^3) :
    ∃ (n : ℝ^3) (d : ℝ), ∀ x : ℝ^3, det4 ![a, b, c, x] = inner ℝ n x + d := by
  let d : ℝ := det4 ![a, b, c, 0]
  let n : ℝ^3 := (EuclideanSpace.equiv (Fin 3) ℝ).symm fun j =>
    det4 ![a, b, c, EuclideanSpace.single j 1] - d
  refine ⟨n, d, ?_⟩
  intro x
  rw [inner_eq_sum_fin3]
  have hn0 : n 0 = det4 ![a, b, c, EuclideanSpace.single 0 1] - d := rfl
  have hn1 : n 1 = det4 ![a, b, c, EuclideanSpace.single 1 1] - d := rfl
  have hn2 : n 2 = det4 ![a, b, c, EuclideanSpace.single 2 1] - d := rfl
  rw [hn0, hn1, hn2]
  have hexpand (y : ℝ^3) : det4 ![a, b, c, y] =
      (mat4 ![a, b, c, y] 3 0) * (-1 : ℝ) ^ (3 + 0) * ((mat4 ![a, b, c, y]).submatrix (Fin.succAbove 3) (Fin.succAbove 0)).det +
      (mat4 ![a, b, c, y] 3 1) * (-1 : ℝ) ^ (3 + 1) * ((mat4 ![a, b, c, y]).submatrix (Fin.succAbove 3) (Fin.succAbove 1)).det +
      (mat4 ![a, b, c, y] 3 2) * (-1 : ℝ) ^ (3 + 2) * ((mat4 ![a, b, c, y]).submatrix (Fin.succAbove 3) (Fin.succAbove 2)).det +
      (mat4 ![a, b, c, y] 3 3) * (-1 : ℝ) ^ (3 + 3) * ((mat4 ![a, b, c, y]).submatrix (Fin.succAbove 3) (Fin.succAbove 3)).det := by
    rw [det4, Matrix.det_succ_row (mat4 ![a, b, c, y]) 3, Fin.sum_univ_four]
    have h0 : (0 : Fin 4).val = 0 := rfl
    have h1 : (1 : Fin 4).val = 1 := rfl
    have h2 : (2 : Fin 4).val = 2 := rfl
    have h3 : (3 : Fin 4).val = 3 := rfl
    simp only [h0, h1, h2, h3]
    ring
  have hsub_indep (j : Fin 4) (y₁ y₂ : ℝ^3) :
      ((mat4 ![a, b, c, y₁]).submatrix (Fin.succAbove 3) (Fin.succAbove j)) =
      ((mat4 ![a, b, c, y₂]).submatrix (Fin.succAbove 3) (Fin.succAbove j)) := by
    ext r col
    fin_cases r <;> rfl
  rw [hexpand x, hexpand (EuclideanSpace.single 0 1), hexpand (EuclideanSpace.single 1 1),
    hexpand (EuclideanSpace.single 2 1)]
  dsimp only [d]
  rw [hexpand 0]
  rw [hsub_indep 0 (EuclideanSpace.single 0 1) x, hsub_indep 1 (EuclideanSpace.single 0 1) x,
    hsub_indep 2 (EuclideanSpace.single 0 1) x, hsub_indep 3 (EuclideanSpace.single 0 1) x,
    hsub_indep 0 (EuclideanSpace.single 1 1) x, hsub_indep 1 (EuclideanSpace.single 1 1) x,
    hsub_indep 2 (EuclideanSpace.single 1 1) x, hsub_indep 3 (EuclideanSpace.single 1 1) x,
    hsub_indep 0 (EuclideanSpace.single 2 1) x, hsub_indep 1 (EuclideanSpace.single 2 1) x,
    hsub_indep 2 (EuclideanSpace.single 2 1) x, hsub_indep 3 (EuclideanSpace.single 2 1) x,
    hsub_indep 0 0 x, hsub_indep 1 0 x, hsub_indep 2 0 x, hsub_indep 3 0 x]
  simp only [mat4, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    PiLp.zero_apply]
  have hs00 : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : ℝ^3) 0 = 1 := by simp
  have hs01 : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : ℝ^3) 1 = 0 := by simp
  have hs02 : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : ℝ^3) 2 = 0 := by simp
  have hs10 : (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : ℝ^3) 0 = 0 := by simp
  have hs11 : (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : ℝ^3) 1 = 1 := by simp
  have hs12 : (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : ℝ^3) 2 = 0 := by simp
  have hs20 : (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : ℝ^3) 0 = 0 := by simp
  have hs21 : (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : ℝ^3) 1 = 0 := by simp
  have hs22 : (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : ℝ^3) 2 = 1 := by simp
  rw [hs00, hs01, hs02, hs10, hs11, hs12, hs20, hs21, hs22]
  ring

/-- Inside any open ball around `v₀` in `ℝ^3`, there is a vector not orthogonal to any nonzero
vector in a finite set `S`. -/
private lemma avoid_finset_hyperplanes (S : Finset (ℝ^3)) (hS : ∀ w ∈ S, w ≠ 0)
    (v₀ : ℝ^3) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : ℝ^3, ‖v - v₀‖ < ε ∧ ∀ w ∈ S, inner ℝ v w ≠ 0 := by
  classical
  -- Step 1: find d with inner d w ≠ 0 for all w ∈ S, using moment curve (1, s, s^2)
  let poly (w : ℝ^3) : Polynomial ℝ :=
    Polynomial.C (w 0) + Polynomial.C (w 1) * Polynomial.X + Polynomial.C (w 2) * Polynomial.X ^ 2
  have hpoly_ne : ∀ w ∈ S, poly w ≠ 0 := by
    intro w hw hp0
    apply hS w hw
    ext j
    fin_cases j
    · have h0 := congrArg (fun p : Polynomial ℝ => p.coeff 0) hp0
      simpa [poly] using h0
    · have h1 := congrArg (fun p : Polynomial ℝ => p.coeff 1) hp0
      simpa [poly] using h1
    · have h2 := congrArg (fun p : Polynomial ℝ => p.coeff 2) hp0
      simpa [poly] using h2
  let badS : Finset ℝ := S.biUnion (fun w => (poly w).roots.toFinset)
  obtain ⟨s, hs⟩ := Infinite.exists_notMem_finset badS
  let d : ℝ^3 := (EuclideanSpace.equiv (Fin 3) ℝ).symm ![1, s, s ^ 2]
  have hd_ne : ∀ w ∈ S, inner ℝ d w ≠ 0 := by
    intro w hw h0
    have heval : (poly w).eval s = 0 := by
      rw [inner_eq_sum_fin3] at h0
      have hd0 : d 0 = 1 := rfl
      have hd1 : d 1 = s := rfl
      have hd2 : d 2 = s ^ 2 := rfl
      rw [hd0, hd1, hd2] at h0
      simp only [poly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_pow]
      linarith
    have hmem : s ∈ (poly w).roots := (Polynomial.mem_roots (hpoly_ne w hw)).mpr heval
    exact hs (Finset.mem_biUnion.mpr ⟨w, hw, Multiset.mem_toFinset.mpr hmem⟩)
  -- Step 2: choose t ∈ (0, ε / (‖d‖ + 1)) avoiding - inner v₀ w / inner d w
  let δ : ℝ := ε / (‖d‖ + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  let badT : Finset ℝ := S.image (fun w => - inner ℝ v₀ w / inner ℝ d w)
  have hinf : (Set.Ioo (0 : ℝ) δ).Infinite := Set.Ioo_infinite hδ
  obtain ⟨t, htIoo, htNot⟩ := (hinf.diff badT.finite_toSet).nonempty
  refine ⟨v₀ + t • d, ?_, ?_⟩
  · rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg htIoo.1.le]
    calc t * ‖d‖ ≤ t * (‖d‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) htIoo.1.le
      _ < δ * (‖d‖ + 1) := mul_lt_mul_of_pos_right htIoo.2 (by positivity)
      _ = ε := div_mul_cancel₀ ε (by positivity)
  · intro w hw h0
    rw [inner_add_left, inner_smul_left] at h0
    simp only [conj_trivial] at h0
    have hdw : inner ℝ d w ≠ 0 := hd_ne w hw
    have ht_eq : t = - inner ℝ v₀ w / inner ℝ d w := by
      field_simp [hdw]
      linarith
    exact htNot (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨w, hw, ht_eq.symm⟩))

/-- Cross product in `ℝ^3` for linear-independence checks. -/
private noncomputable def cross3 (u v : ℝ^3) : ℝ^3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm
    ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

private lemma cross3_apply (u v : ℝ^3) :
    cross3 u v 0 = u 1 * v 2 - u 2 * v 1 ∧
    cross3 u v 1 = u 2 * v 0 - u 0 * v 2 ∧
    cross3 u v 2 = u 0 * v 1 - u 1 * v 0 := ⟨rfl, rfl, rfl⟩

private lemma det3_eq_inner_cross (u v w : ℝ^3) :
    (Matrix.of fun (j k : Fin 3) => (![u, v, w] j) k).det = inner ℝ w (cross3 u v) := by
  rw [Matrix.det_fin_three, inner_eq_sum_fin3, (cross3_apply u v).1, (cross3_apply u v).2.1,
    (cross3_apply u v).2.2]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

private lemma cross3_ne_zero_of_linearIndependent {u v : ℝ^3}
    (hli : LinearIndependent ℝ ![u, v]) : cross3 u v ≠ 0 := by
  intro h0
  have hc0 : u 1 * v 2 - u 2 * v 1 = 0 := by
    have := congrArg (fun z : ℝ^3 => z 0) h0; simpa [cross3] using this
  have hc1 : u 2 * v 0 - u 0 * v 2 = 0 := by
    have := congrArg (fun z : ℝ^3 => z 1) h0; simpa [cross3] using this
  have hc2 : u 0 * v 1 - u 1 * v 0 = 0 := by
    have := congrArg (fun z : ℝ^3 => z 2) h0; simpa [cross3] using this
  have hu0 : u ≠ 0 := by
    intro hu
    have := hli.ne_zero (0 : Fin 2)
    exact this (by simpa using hu)
  have hcoord : u 0 ≠ 0 ∨ u 1 ≠ 0 ∨ u 2 ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hu0
    ext j; fin_cases j <;> simp [hall]
  have hdep (a b : ℝ) (hab : a • u + b • v = 0) : a = 0 ∧ b = 0 := by
    have hsum : ∑ i : Fin 2, (![a, b] i) • (![u, v] i) = 0 := by
      rw [Fin.sum_univ_two]; simpa using hab
    have hz := Fintype.linearIndependent_iff.mp hli ![a, b] hsum
    exact ⟨hz 0, hz 1⟩
  rcases hcoord with h | h | h
  · have := (hdep (v 0) (-u 0) (by
      ext j; fin_cases j <;> simp <;> linarith)).2
    exact h (by linarith)
  · have := (hdep (v 1) (-u 1) (by
      ext j; fin_cases j <;> simp <;> linarith)).2
    exact h (by linarith)
  · have := (hdep (v 2) (-u 2) (by
      ext j; fin_cases j <;> simp <;> linarith)).2
    exact h (by linarith)

/-- Three distinct points of a general-position set `X` have linearly independent differences. -/
private lemma vsub_linearIndependent_of_generalPosition {X : Finset (ℝ^3)}
    (hX : IsInGeneralPosition X) {x y z : ℝ^3}
    (hx : x ∈ X) (hy : y ∈ X) (hz : z ∈ X)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    LinearIndependent ℝ ![y - x, z - x] := by
  let Z : Finset (ℝ^3) := {x, y, z}
  have hZX : Z ⊆ X := by
    intro w hw; simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  have hZc : Z.card ≤ 3 + 1 := by
    calc Z.card ≤ 3 := Finset.card_le_three
      _ ≤ 3 + 1 := by omega
  have haff := hX Z hZX hZc
  let f : Fin 3 → ↥(Z : Set (ℝ^3)) :=
    ![⟨x, by simp [Z]⟩, ⟨y, by simp [Z]⟩, ⟨z, by simp [Z]⟩]
  have hfinj : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f, hxy, hxz, hyz, hxy.symm, hxz.symm, hyz.symm]
  have haff3 : AffineIndependent ℝ ![x, y, z] := by
    have hcomp := haff.comp_embedding ⟨f, hfinj⟩
    have heq : ((↑) : ↥(Z : Set (ℝ^3)) → ℝ^3) ∘ f = ![x, y, z] := by
      funext i; fin_cases i <;> rfl
    simpa [heq] using hcomp
  have hli0 := (affineIndependent_iff_linearIndependent_vsub ℝ ![x, y, z] (0 : Fin 3)).mp haff3
  rw [Fintype.linearIndependent_iff]
  intro g hg
  let g' : {i : Fin 3 // i ≠ 0} → ℝ := fun i =>
    if i.1 = 1 then g 0 else g 1
  have hg' : ∑ i : {i : Fin 3 // i ≠ 0}, g' i • (![x, y, z] i.1 -ᵥ ![x, y, z] 0) = 0 := by
    let i1 : {i : Fin 3 // i ≠ 0} := ⟨1, by decide⟩
    let i2 : {i : Fin 3 // i ≠ 0} := ⟨2, by decide⟩
    have h12 : i1 ≠ i2 := by decide
    have huniv : (Finset.univ : Finset {i : Fin 3 // i ≠ 0}) = {i1, i2} := by
      ext ⟨a, ha⟩; fin_cases a
      · exact (ha rfl).elim
      · simp [i1, i2]
      · simp [i1, i2]
    rw [huniv, Finset.sum_pair h12]
    rw [Fin.sum_univ_two] at hg
    simpa [g', i1, i2, vsub_eq_sub] using hg
  have hall := Fintype.linearIndependent_iff.mp hli0 g' hg'
  intro i
  fin_cases i
  · exact hall ⟨1, by decide⟩
  · exact hall ⟨2, by decide⟩

/-- Sequential generic perturbation of three normal vectors `n₀, n₁, n₂` in `ℝ^3`. -/
private lemma perturb_three_normals {X : Finset (ℝ^3)} (hX : IsInGeneralPosition X)
    (n₀ n₁ n₂ : ℝ^3) (ε : ℝ) (hε : 0 < ε) :
    ∃ n' : Fin 3 → ℝ^3,
      ‖n' 0 - n₀‖ < ε ∧ ‖n' 1 - n₁‖ < ε ∧ ‖n' 2 - n₂‖ < ε ∧
      (Matrix.of fun (j k : Fin 3) => n' j k).det ≠ 0 ∧
      ∀ (r s : Fin 3), r < s → ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X,
        x ≠ y → x ≠ z → y ≠ z →
        inner ℝ (n' r) (y - x) * inner ℝ (n' s) (z - x) -
          inner ℝ (n' r) (z - x) * inner ℝ (n' s) (y - x) ≠ 0 := by
  classical
  -- Finite set of nonzero pairwise differences y - x for distinct x, y ∈ X
  let diffs : Finset (ℝ^3) :=
    ((X ×ˢ X).filter (fun p => p.1 ≠ p.2)).image (fun p => p.2 - p.1)
  have hdiffs_ne : ∀ w ∈ diffs, w ≠ 0 := by
    intro w hw
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hw
    exact sub_ne_zero.mpr (Finset.mem_filter.mp hxy).2.symm
  -- Step 1: pick n0' avoiding diffs ∪ {e0} (so n0' ≠ 0 automatically!)
  let e0_vec : ℝ^3 := EuclideanSpace.single 0 1
  have he0_ne : e0_vec ≠ 0 := by
    intro h; have := congrArg (fun z : ℝ^3 => z 0) h; simp [e0_vec] at this
  let S0 : Finset (ℝ^3) := insert e0_vec diffs
  have hS0_ne : ∀ w ∈ S0, w ≠ 0 := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw'
    · exact he0_ne
    · exact hdiffs_ne w hw'
  obtain ⟨n0', hn0'_dist, hn0'_av⟩ := avoid_finset_hyperplanes S0 hS0_ne n₀ ε hε
  have hn0'_ne : n0' ≠ 0 := by
    intro h0
    have := hn0'_av e0_vec (Finset.mem_insert_self _ _)
    simp [h0] at this
  have hn0'_diff : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → inner ℝ n0' (y - x) ≠ 0 := by
    intro x hx y hy hxy
    exact hn0'_av (y - x) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(x, y),
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩, rfl⟩))
  -- Helper: given u avoiding diffs, form the finite set of linear-combination vectors
  -- (inner u (y - x)) • (z - x) - (inner u (z - x)) • (y - x) for distinct x, y, z ∈ X
  let tripleVecs (u : ℝ^3) : Finset (ℝ^3) :=
    (((X ×ˢ X) ×ˢ X).filter (fun p => p.1.1 ≠ p.1.2 ∧ p.1.1 ≠ p.2 ∧ p.1.2 ≠ p.2)).image
      (fun p => inner ℝ u (p.1.2 - p.1.1) • (p.2 - p.1.1) -
                inner ℝ u (p.2 - p.1.1) • (p.1.2 - p.1.1))
  have htriple_ne : ∀ u : ℝ^3, (∀ x ∈ X, ∀ y ∈ X, x ≠ y → inner ℝ u (y - x) ≠ 0) →
      ∀ w ∈ tripleVecs u, w ≠ 0 := by
    intro u hu w hw
    obtain ⟨⟨⟨x, y⟩, z⟩, hmem, rfl⟩ := Finset.mem_image.mp hw
    have hf := Finset.mem_filter.mp hmem
    have hx : x ∈ X := (Finset.mem_product.mp (Finset.mem_product.mp hf.1).1).1
    have hy : y ∈ X := (Finset.mem_product.mp (Finset.mem_product.mp hf.1).1).2
    have hz : z ∈ X := (Finset.mem_product.mp hf.1).2
    have hli := vsub_linearIndependent_of_generalPosition hX hx hy hz hf.2.1 hf.2.2.1 hf.2.2.2
    intro hzero
    have hsum : ∑ i : Fin 2,
        (![-inner ℝ u (z - x), inner ℝ u (y - x)] i) • (![y - x, z - x] i) = 0 := by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul]
      rw [add_comm, ← sub_eq_add_neg]
      exact hzero
    have h1 := Fintype.linearIndependent_iff.mp hli ![-inner ℝ u (z - x), inner ℝ u (y - x)] hsum 1
    exact hu x hx y hy hf.2.1 (by simpa using h1)
  -- Also find a vector perpendicular to n0' to force n1' not a scalar multiple of n0'?
  -- Actually: pick any e_k not parallel to n0', then cross3 n0' e_k ≠ 0, OR simply pick
  -- any nonzero vector w_perp with inner n0' w_perp ≠ 0? No, to ensure LinearIndependent ![n0', n1'],
  -- we just need n1' not in span {n0'}. Since span {n0'} is 1D in ℝ^3, there exists w_orth ≠ 0
  -- with inner n0' w_orth = 0! Avoiding {v | inner v w_orth = 0} forces n1' ∉ span {n0'}!
  have hex_orth : ∃ w : ℝ^3, w ≠ 0 ∧ inner ℝ n0' w = 0 := by
    let e0 : ℝ^3 := EuclideanSpace.single 0 1
    let e1 : ℝ^3 := EuclideanSpace.single 1 1
    have he0 : e0 0 = 1 ∧ e0 1 = 0 ∧ e0 2 = 0 := ⟨by simp [e0], by simp [e0], by simp [e0]⟩
    have he1 : e1 0 = 0 ∧ e1 1 = 1 ∧ e1 2 = 0 := ⟨by simp [e1], by simp [e1], by simp [e1]⟩
    by_cases h0 : cross3 n0' e0 ≠ 0
    · refine ⟨cross3 n0' e0, h0, ?_⟩
      rw [inner_eq_sum_fin3, (cross3_apply n0' e0).1, (cross3_apply n0' e0).2.1, (cross3_apply n0' e0).2.2,
        he0.1, he0.2.1, he0.2.2]
      ring
    · push_neg at h0
      by_cases h1 : cross3 n0' e1 ≠ 0
      · refine ⟨cross3 n0' e1, h1, ?_⟩
        rw [inner_eq_sum_fin3, (cross3_apply n0' e1).1, (cross3_apply n0' e1).2.1, (cross3_apply n0' e1).2.2,
          he1.1, he1.2.1, he1.2.2]
        ring
      · push_neg at h1
        have hn0_zero : n0' = 0 := by
          ext j
          fin_cases j
          · have h2 := congrArg (fun z : ℝ^3 => z 2) h1
            rw [(cross3_apply n0' e1).2.2, he1.1, he1.2.1] at h2
            change n0' 0 = 0
            change n0' 0 * 1 - n0' 1 * 0 = 0 at h2
            linarith
          · have h2 := congrArg (fun z : ℝ^3 => z 2) h0
            rw [(cross3_apply n0' e0).2.2, he0.1, he0.2.1] at h2
            change n0' 1 = 0
            change n0' 0 * 0 - n0' 1 * 1 = 0 at h2
            linarith
          · have h2 := congrArg (fun z : ℝ^3 => z 1) h0
            rw [(cross3_apply n0' e0).2.1, he0.1, he0.2.2] at h2
            change n0' 2 = 0
            change n0' 2 * 1 - n0' 0 * 0 = 0 at h2
            linarith
        exact (hn0'_ne hn0_zero).elim
  obtain ⟨w_orth, hw_orth_ne, hw_orth_perp⟩ := hex_orth
  -- Step 2: pick n1' avoiding diffs ∪ tripleVecs n0' ∪ {w_orth}
  let S1 : Finset (ℝ^3) := insert w_orth (diffs ∪ tripleVecs n0')
  have hS1_ne : ∀ w ∈ S1, w ≠ 0 := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw'
    · exact hw_orth_ne
    · rcases Finset.mem_union.mp hw' with hd | ht
      · exact hdiffs_ne w hd
      · exact htriple_ne n0' hn0'_diff w ht
  obtain ⟨n1', hn1'_dist, hn1'_av⟩ := avoid_finset_hyperplanes S1 hS1_ne n₁ ε hε
  have hn1'_diff : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → inner ℝ n1' (y - x) ≠ 0 := by
    intro x hx y hy hxy
    exact hn1'_av (y - x) (Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨(x, y),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩, rfl⟩)))
  have h01_li : LinearIndependent ℝ ![n0', n1'] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_two] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg
    have hinner := congrArg (fun z : ℝ^3 => inner ℝ z w_orth) hg
    simp only [inner_add_left, inner_smul_left, conj_trivial, hw_orth_perp, mul_zero, zero_add,
      inner_zero_left] at hinner
    have hg1 : g 1 = 0 := by
      rcases mul_eq_zero.mp hinner with h | h
      · exact h
      · exact (hn1'_av w_orth (Finset.mem_insert_self _ _) h).elim
    have hg0 : g 0 = 0 := by
      rw [hg1, zero_smul, add_zero] at hg
      exact (smul_eq_zero.mp hg).resolve_right hn0'_ne
    intro i; fin_cases i <;> assumption
  -- Step 3: pick n2' avoiding {cross3 n0' n1'} ∪ tripleVecs n0' ∪ tripleVecs n1'
  let S2 : Finset (ℝ^3) := insert (cross3 n0' n1') (tripleVecs n0' ∪ tripleVecs n1')
  have hS2_ne : ∀ w ∈ S2, w ≠ 0 := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw'
    · exact cross3_ne_zero_of_linearIndependent h01_li
    · rcases Finset.mem_union.mp hw' with h0 | h1
      · exact htriple_ne n0' hn0'_diff w h0
      · exact htriple_ne n1' hn1'_diff w h1
  obtain ⟨n2', hn2'_dist, hn2'_av⟩ := avoid_finset_hyperplanes S2 hS2_ne n₂ ε hε
  refine ⟨![n0', n1', n2'], hn0'_dist, hn1'_dist, hn2'_dist, ?_, ?_⟩
  · rw [det3_eq_inner_cross]
    exact hn2'_av (cross3 n0' n1') (Finset.mem_insert_self _ _)
  · intro r s hrs x hx y hy z hz hxy hxz hyz
    have hmem_t (u : ℝ^3) :
        inner ℝ u (y - x) • (z - x) - inner ℝ u (z - x) • (y - x) ∈ tripleVecs u :=
      Finset.mem_image.mpr ⟨((x, y), z),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hz⟩,
          hxy, hxz, hyz⟩, rfl⟩
    have hrewrite (u v : ℝ^3) :
        inner ℝ u (y - x) * inner ℝ v (z - x) - inner ℝ u (z - x) * inner ℝ v (y - x) =
        inner ℝ v (inner ℝ u (y - x) • (z - x) - inner ℝ u (z - x) • (y - x)) := by
      symm
      rw [inner_sub_right, inner_smul_right, inner_smul_right]
    fin_cases r <;> fin_cases s <;> try (exfalso; exact absurd hrs (by decide))
    · change inner ℝ n0' (y - x) * inner ℝ n1' (z - x) - inner ℝ n0' (z - x) * inner ℝ n1' (y - x) ≠ 0
      rw [hrewrite]
      exact hn1'_av _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ (hmem_t n0')))
    · change inner ℝ n0' (y - x) * inner ℝ n2' (z - x) - inner ℝ n0' (z - x) * inner ℝ n2' (y - x) ≠ 0
      rw [hrewrite]
      exact hn2'_av _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ (hmem_t n0')))
    · change inner ℝ n1' (y - x) * inner ℝ n2' (z - x) - inner ℝ n1' (z - x) * inner ℝ n2' (y - x) ≠ 0
      rw [hrewrite]
      exact hn2'_av _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ (hmem_t n1')))

/-- Build an `AffineEquiv ℝ (ℝ^3) (ℝ^3)` from three linearly independent normals and offsets. -/
private noncomputable def affineEquivOfNormals (n : Fin 3 → ℝ^3) (c : Fin 3 → ℝ)
    (hdet : (Matrix.of fun (j k : Fin 3) => n j k).det ≠ 0) : (ℝ^3) ≃ᵃ[ℝ] (ℝ^3) :=
  let M : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun j k => n j k
  let hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  let L_fin : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) :=
    LinearEquiv.ofLinearMap (Matrix.toLin' M) (Matrix.toLin' M⁻¹)
      (by rw [← Matrix.toLin'_mul, Matrix.mul_nonsing_inv M hunit, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, Matrix.nonsing_inv_mul M hunit, Matrix.toLin'_one])
  let L_euc : (ℝ^3) ≃ₗ[ℝ] (ℝ^3) :=
    (EuclideanSpace.equiv (Fin 3) ℝ).toLinearEquiv.trans
      (L_fin.trans (EuclideanSpace.equiv (Fin 3) ℝ).toLinearEquiv.symm)
  let v_c : ℝ^3 := (EuclideanSpace.equiv (Fin 3) ℝ).symm c
  L_euc.toAffineEquiv.trans (AffineEquiv.vaddConst ℝ v_c)

private lemma affineEquivOfNormals_apply (n : Fin 3 → ℝ^3) (c : Fin 3 → ℝ)
    (hdet : (Matrix.of fun (j k : Fin 3) => n j k).det ≠ 0) (x : ℝ^3) (j : Fin 3) :
    affineEquivOfNormals n c hdet x j = inner ℝ (n j) x + c j := by
  have h1 : affineEquivOfNormals n c hdet x j =
      (Matrix.of fun (i k : Fin 3) => n i k).mulVec (fun k => x k) j + c j := by
    simp only [affineEquivOfNormals, AffineEquiv.trans_apply, LinearEquiv.coe_toAffineEquiv,
      AffineEquiv.vaddConst_apply, vadd_eq_add, PiLp.add_apply, LinearEquiv.trans_apply]
    rfl
  rw [h1, Matrix.mulVec, dotProduct, inner_eq_sum_fin3, Fin.sum_univ_three]
  simp only [Matrix.of_apply]

/-- Projection general position: if all 2x2 determinants of `(n r, n s)` on triples of `X` are
nonzero and `|X| ≥ 3`, then every 2-coordinate projection of `Z ⊆ X` (`|Z| ≤ 3`) is affinely
independent. -/
private lemma proj_affineIndependent {X : Finset (ℝ^3)} (hX3 : 3 ≤ X.card)
    (n : Fin 3 → ℝ^3) (c : Fin 3 → ℝ)
    (hdet : (Matrix.of fun (j k : Fin 3) => n j k).det ≠ 0)
    (htriple : ∀ (r s : Fin 3), r < s → ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X,
      x ≠ y → x ≠ z → y ≠ z →
      inner ℝ (n r) (y - x) * inner ℝ (n s) (z - x) -
        inner ℝ (n r) (z - x) * inner ℝ (n s) (y - x) ≠ 0)
    (j : Fin 3) (Z : Finset (ℝ^3)) (hZX : Z ⊆ X) (hZc : Z.card ≤ 3) :
    AffineIndependent ℝ
      (fun x : ↥(Z : Set (ℝ^3)) => fun k : Fin 2 =>
        affineEquivOfNormals n c hdet x (j.succAbove k)) := by
  classical
  let e := affineEquivOfNormals n c hdet
  let r : Fin 3 := j.succAbove 0
  let s : Fin 3 := j.succAbove 1
  have hrs : r < s := j.strictMono_succAbove (by decide : (0 : Fin 2) < 1)
  let proj (x : ℝ^3) : Fin 2 → ℝ := fun k => e x (j.succAbove k)
  have hproj_sub (x y : ℝ^3) :
      proj y 0 - proj x 0 = inner ℝ (n r) (y - x) ∧
      proj y 1 - proj x 1 = inner ℝ (n s) (y - x) := by
    constructor
    · simp only [proj, e, r, affineEquivOfNormals_apply, inner_sub_right]; ring
    · simp only [proj, e, s, affineEquivOfNormals_apply, inner_sub_right]; ring
  have hdet2 (x y z : ℝ^3) (hx : x ∈ X) (hy : y ∈ X) (hz : z ∈ X)
      (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
      (proj y 0 - proj x 0) * (proj z 1 - proj x 1) -
        (proj z 0 - proj x 0) * (proj y 1 - proj x 1) ≠ 0 := by
    rw [(hproj_sub x y).1, (hproj_sub x y).2, (hproj_sub x z).1, (hproj_sub x z).2]
    exact htriple r s hrs x hx y hy z hz hxy hxz hyz
  -- Case split on Z.card ≤ 1, = 2, = 3
  rcases le_or_gt Z.card 1 with h1 | h2
  · haveI : Subsingleton ↥(Z : Set (ℝ^3)) := by
      refine ⟨fun a b => ?_⟩
      apply Subtype.ext
      exact Finset.card_le_one.mp h1 a.1 (Finset.mem_coe.mp a.2) b.1 (Finset.mem_coe.mp b.2)
    exact affineIndependent_of_subsingleton ℝ _
  · rcases eq_or_lt_of_le (show 2 ≤ Z.card by omega) with hcard2 | hcard3
    · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard2.symm
      have hxX : x ∈ X := hZX (by simp)
      have hyX : y ∈ X := hZX (by simp)
      have hne3 : (X \ {x, y}).Nonempty := by
        rw [← Finset.card_pos]
        have hle : ({x, y} : Finset (ℝ^3)).card ≤ 2 := Finset.card_le_two
        have := Finset.card_sdiff_add_card_inter X {x, y}
        have hinter : (X ∩ {x, y}).card ≤ 2 := (Finset.card_le_card Finset.inter_subset_right).trans hle
        omega
      obtain ⟨z, hz⟩ := hne3
      have hzX : z ∈ X := (Finset.mem_sdiff.mp hz).1
      have hzx : x ≠ z := fun h => (Finset.mem_sdiff.mp hz).2 (by simp [h])
      have hzy : y ≠ z := fun h => (Finset.mem_sdiff.mp hz).2 (by simp [h])
      have hne_proj : proj x ≠ proj y := by
        intro heq
        have h0 : proj y 0 - proj x 0 = 0 := by rw [heq, sub_self]
        have h1 : proj y 1 - proj x 1 = 0 := by rw [heq, sub_self]
        exact hdet2 x y z hxX hyX hzX hxy hzx hzy (by rw [h0, h1]; ring)
      rw [affineIndependent_iff_linearIndependent_vsub ℝ _ (⟨x, by simp⟩ : ↥(({x, y} : Finset (ℝ^3)) : Set (ℝ^3)))]
      rw [Fintype.linearIndependent_iff]
      intro g hg a
      have ha_eq : a = ⟨⟨y, by simp⟩, by intro h; exact hxy (congrArg Subtype.val h).symm⟩ := by
        apply Subtype.ext; apply Subtype.ext
        have hmem := a.1.2
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with h | h
        · exact (a.2 (Subtype.ext h)).elim
        · exact h
      have hsum : ∑ b : {b : ↥(({x, y} : Finset (ℝ^3)) : Set (ℝ^3)) // b ≠ ⟨x, by simp⟩},
          g b • (proj b.1.1 -ᵥ proj x) = g a • (proj y - proj x) := by
        rw [Finset.sum_eq_single a]
        · rw [ha_eq]; rfl
        · intro b _ hba
          exfalso; apply hba
          apply Subtype.ext; apply Subtype.ext
          have hb := b.1.2
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with h | h
          · exact (b.2 (Subtype.ext h)).elim
          · rw [ha_eq]; exact h
        · intro ha; exact (ha (Finset.mem_univ a)).elim
      rw [hsum] at hg
      exact (smul_eq_zero.mp hg).resolve_right (sub_ne_zero.mpr hne_proj.symm)
    · have hcard3' : Z.card = 3 := by omega
      obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hcard3'
      have hxX : x ∈ X := hZX (by simp)
      have hyX : y ∈ X := hZX (by simp)
      have hzX : z ∈ X := hZX (by simp)
      have hd := hdet2 x y z hxX hyX hzX hxy hxz hyz
      let x0 : ↥(({x, y, z} : Finset (ℝ^3)) : Set (ℝ^3)) := ⟨x, by simp⟩
      rw [affineIndependent_iff_linearIndependent_vsub ℝ _ x0]
      rw [Fintype.linearIndependent_iff]
      intro g hg
      let ay : {b : ↥(({x, y, z} : Finset (ℝ^3)) : Set (ℝ^3)) // b ≠ x0} :=
        ⟨⟨y, by simp⟩, by intro h; exact hxy (congrArg Subtype.val h).symm⟩
      let az : {b : ↥(({x, y, z} : Finset (ℝ^3)) : Set (ℝ^3)) // b ≠ x0} :=
        ⟨⟨z, by simp⟩, by intro h; exact hxz (congrArg Subtype.val h).symm⟩
      have hayz : ay ≠ az := fun h => hyz (congrArg (fun u => u.1.1) h)
      have huniv : (Finset.univ : Finset {b : ↥(({x, y, z} : Finset (ℝ^3)) : Set (ℝ^3)) // b ≠ x0}) = {ay, az} := by
        ext b
        simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
        have hb := b.1.2
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with h | h | h
        · exact (b.2 (Subtype.ext h)).elim
        · exact Or.inl (Subtype.ext (Subtype.ext h))
        · exact Or.inr (Subtype.ext (Subtype.ext h))
      rw [huniv, Finset.sum_pair hayz] at hg
      have h0 : g ay * (proj y 0 - proj x 0) + g az * (proj z 0 - proj x 0) = 0 := by
        have h' := congrFun hg 0; simpa [ay, az, vsub_eq_sub] using h'
      have h1 : g ay * (proj y 1 - proj x 1) + g az * (proj z 1 - proj x 1) = 0 := by
        have h' := congrFun hg 1; simpa [ay, az, vsub_eq_sub] using h'
      have hgay : g ay = 0 := by
        have : g ay * ((proj y 0 - proj x 0) * (proj z 1 - proj x 1) -
            (proj z 0 - proj x 0) * (proj y 1 - proj x 1)) = 0 := by
          linear_combination (proj z 1 - proj x 1) * h0 - (proj z 0 - proj x 0) * h1
        exact (mul_eq_zero.mp this).resolve_right hd
      have hgaz : g az = 0 := by
        have : g az * ((proj y 0 - proj x 0) * (proj z 1 - proj x 1) -
            (proj z 0 - proj x 0) * (proj y 1 - proj x 1)) = 0 := by
          linear_combination (proj y 0 - proj x 0) * h1 - (proj y 1 - proj x 1) * h0
        exact (mul_eq_zero.mp this).resolve_right hd
      intro b
      have hb : b ∈ ({ay, az} : Finset _) := by rw [← huniv]; exact Finset.mem_univ b
      rcases Finset.mem_insert.mp hb with rfl | hb'
      · exact hgay
      · rw [Finset.mem_singleton.mp hb']; exact hgaz

/- ## Module 4: Orthants, No-3-Sets Line Lemma, Strict Partial Order & Chain-Antichain -/

/-- No line contains a point of `M`, a point of `Q_A`, and a point of `Q_E` simultaneously. -/
private lemma no_line_three_sets {f₀ f₁ f₂ : ℝ^3 → ℝ}
    (hf₀ : ∀ x y t, f₀ (t • x + (1 - t) • y) = t * f₀ x + (1 - t) * f₀ y)
    (hf₁ : ∀ x y t, f₁ (t • x + (1 - t) • y) = t * f₁ x + (1 - t) * f₁ y)
    (hf₂ : ∀ x y t, f₂ (t • x + (1 - t) • y) = t * f₂ x + (1 - t) * f₂ y)
    {δ : ℝ} (hδ : 0 < δ) {m qA qE : ℝ^3}
    (hm0 : 0 < f₀ m) (hm1 : f₁ m < 0) (hm2 : 0 < f₂ m)
    (hA0 : f₀ qA ≤ 0) (hA1 : f₁ qA ≤ -δ) (hA2 : f₂ qA ≤ -δ)
    (hE0 : f₀ qE ≤ 0) (hE1 : δ ≤ f₁ qE) (hE2 : δ ≤ f₂ qE)
    {u v : ℝ^3} (hmL : m ∈ (line[ℝ, u, v] : Set (ℝ^3)))
    (hAL : qA ∈ (line[ℝ, u, v] : Set (ℝ^3)))
    (hEL : qE ∈ (line[ℝ, u, v] : Set (ℝ^3))) : False := by
  rw [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq] at hmL hAL hEL
  obtain ⟨tm, htm⟩ := hmL
  obtain ⟨tA, htA⟩ := hAL
  obtain ⟨tE, htE⟩ := hEL
  -- Helper: any affine functional g evaluates linearly along lineMap u v
  have hlin (g : ℝ^3 → ℝ) (hg : ∀ x y t, g (t • x + (1 - t) • y) = t * g x + (1 - t) * g y)
      (a b c : ℝ) (ha : a ≤ b) (hb : b ≤ c) (hac : a < c)
      (hga : g (AffineMap.lineMap u v a) ≤ 0) (hgc : g (AffineMap.lineMap u v c) ≤ 0) :
      g (AffineMap.lineMap u v b) ≤ 0 := by
    let s := (b - a) / (c - a)
    have hs0 : 0 ≤ s := div_nonneg (by linarith) (by linarith)
    have hs1 : s ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    have hpt : AffineMap.lineMap u v b =
        s • AffineMap.lineMap u v c + (1 - s) • AffineMap.lineMap u v a := by
      simp only [AffineMap.lineMap_apply_module]
      ext j
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      have hne : c - a ≠ 0 := by linarith
      dsimp [s]
      field_simp [hne]
      ring
    rw [hpt, hg]
    nlinarith
  have hlin_neg (g : ℝ^3 → ℝ) (hg : ∀ x y t, g (t • x + (1 - t) • y) = t * g x + (1 - t) * g y)
      (a b c : ℝ) (ha : a ≤ b) (hb : b ≤ c) (hac : a < c)
      (hga : 0 ≤ g (AffineMap.lineMap u v a)) (hgc : 0 ≤ g (AffineMap.lineMap u v c)) :
      0 ≤ g (AffineMap.lineMap u v b) := by
    have := hlin (fun x => -g x) (fun x y t => by rw [hg]; ring) a b c ha hb hac (by linarith) (by linarith)
    linarith
  have htmA : tm ≠ tA := fun h => by rw [h, htA] at htm; rw [← htm] at hm0; linarith
  have htmE : tm ≠ tE := fun h => by rw [h, htE] at htm; rw [← htm] at hm0; linarith
  have htAE : tA ≠ tE := fun h => by rw [h, htE] at htA; rw [← htA] at hA1; linarith
  -- Whichever of tm, tA, tE is in the middle yields a contradiction
  rcases lt_or_gt_of_ne htmA with h1 | h1 <;>
  rcases lt_or_gt_of_ne htmE with h2 | h2 <;>
  rcases lt_or_gt_of_ne htAE with h3 | h3
  · -- tm < tA < tE: tA is in the middle, contradict f₂(qA) ≤ -δ < 0
    have := hlin_neg f₂ hf₂ tm tA tE h1.le h3.le (h1.trans h3)
      (by rw [htm]; linarith) (by rw [htE]; linarith)
    rw [htA] at this; linarith
  · -- tm < tE < tA: tE is in the middle, contradict f₁(qE) ≥ δ > 0
    have := hlin f₁ hf₁ tm tE tA h2.le h3.le (h2.trans h3)
      (by rw [htm]; linarith) (by rw [htA]; linarith)
    rw [htE] at this; linarith
  · exact (lt_asymm (h2.trans h1) h3).elim
  · -- tE < tm < tA: tm is in the middle, contradict f₀(m) > 0
    have := hlin f₀ hf₀ tE tm tA h2.le h1.le (h2.trans h1)
      (by rw [htE]; exact hE0) (by rw [htA]; exact hA0)
    rw [htm] at this; linarith
  · -- tA < tm < tE: tm is in the middle, contradict f₀(m) > 0
    have := hlin f₀ hf₀ tA tm tE h1.le h2.le (h1.trans h2)
      (by rw [htA]; exact hA0) (by rw [htE]; exact hE0)
    rw [htm] at this; linarith
  · exact (lt_asymm (h1.trans h2) h3).elim
  · -- tA < tE < tm: tE is in the middle, contradict f₁(qE) ≥ δ > 0
    have := hlin f₁ hf₁ tA tE tm h3.le h2.le (h3.trans h2)
      (by rw [htA]; linarith) (by rw [htm]; linarith)
    rw [htE] at this; linarith
  · -- tE < tA < tm: tA is in the middle, contradict f₂(qA) ≤ -δ < 0
    have := hlin_neg f₂ hf₂ tE tA tm h3.le h1.le (h3.trans h1)
      (by rw [htE]; linarith) (by rw [htm]; linarith)
    rw [htA] at this; linarith

/-- Rank-based chain-antichain theorem (Erdős-Szekeres / Mirsky): every finite set with a strict
partial order has a chain or an antichain of size at least `√|M|`. -/
private lemma chain_or_antichain {α : Type} [DecidableEq α] (M : Finset α)
    (lt : α → α → Prop)
    (hirr : ∀ x ∈ M, ¬ lt x x)
    (htrans : ∀ x ∈ M, ∀ y ∈ M, ∀ z ∈ M, lt x y → lt y z → lt x z) :
    ∃ Y ⊆ M, M.card ≤ Y.card ^ 2 ∧
      ((∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → lt x y ∨ lt y x) ∨
       (∀ x ∈ Y, ∀ y ∈ Y, ¬ lt x y)) := by
  classical
  -- Induction on M.card? Even simpler: define rank(x) = max length of a chain in M ending at x!
  -- A chain is a list L of elements of M with L.Chain' lt.
  -- Every chain in M has length ≤ M.card (since elements are distinct by irrefl + trans!).
  have hchain_nodup : ∀ L : List α, (∀ x ∈ L, x ∈ M) → L.IsChain lt → L.Nodup := by
    intro L
    induction L with
    | nil => intros; exact List.nodup_nil
    | cons a l ih =>
      intro hmem hch
      rw [List.nodup_cons]
      refine ⟨?_, ih (fun x hx => hmem x (List.mem_cons_of_mem a hx)) (List.isChain_cons.mp hch).2⟩
      intro ha_in
      have hlt_all : ∀ l' : List α, ∀ b, b ∈ M → (∀ x ∈ l', x ∈ M) → List.IsChain lt (b :: l') →
          ∀ x ∈ l', lt b x := by
        intro l'
        induction l' with
        | nil => intro _ _ _ _ _ hx; exact (List.not_mem_nil hx).elim
        | cons c t ih' =>
          intro b hb hmt hch' x hx
          have hbc : lt b c := (List.isChain_cons_cons.mp hch').1
          have hct : List.IsChain lt (c :: t) := (List.isChain_cons_cons.mp hch').2
          rcases List.mem_cons.mp hx with rfl | hxt
          · exact hbc
          · exact htrans b hb c (hmt c (List.mem_cons_self ..)) x (hmt x (List.mem_cons_of_mem c hxt))
              hbc (ih' c (hmt c (List.mem_cons_self ..))
                (fun y hy => hmt y (List.mem_cons_of_mem c hy)) hct x hxt)
      exact hirr a (hmem a (List.mem_cons_self ..))
        (hlt_all l a (hmem a (List.mem_cons_self ..))
          (fun x hx => hmem x (List.mem_cons_of_mem a hx)) hch a ha_in)
  have hchain_len_le : ∀ L : List α, (∀ x ∈ L, x ∈ M) → L.IsChain lt → L.length ≤ M.card := by
    intro L hmem hch
    have hnd := hchain_nodup L hmem hch
    calc L.length = L.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
      _ ≤ M.card := Finset.card_le_card (fun x hx => hmem x (List.mem_toFinset.mp hx))
  let validLen (x : α) (k : ℕ) : Prop :=
    ∃ L : List α, (∀ y ∈ L, y ∈ M) ∧ L.IsChain lt ∧ L.getLast? = some x ∧ L.length = k
  have hlen_ex : ∀ x ∈ M, ∃ k, validLen x k := by
    intro x hx
    exact ⟨1, [x], by simp [hx], List.isChain_singleton x, rfl, rfl⟩
  have hlen_bdd : ∀ x, ∀ k, validLen x k → k ≤ M.card := by
    rintro x k ⟨L, hmem, hch, _, rfl⟩
    exact hchain_len_le L hmem hch
  let rank (x : α) : ℕ :=
    ((Finset.range (M.card + 1)).filter (validLen x)).sup id
  have hrank_mem : ∀ x ∈ M, validLen x (rank x) := by
    intro x hx
    let S := (Finset.range (M.card + 1)).filter (validLen x)
    have hSne : S.Nonempty := by
      obtain ⟨k, hk⟩ := hlen_ex x hx
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hlen_bdd x k hk)), hk⟩⟩
    obtain ⟨k, hkS, hksup⟩ := Finset.exists_mem_eq_sup S hSne id
    have hEq : rank x = k := hksup
    rw [hEq]
    exact (Finset.mem_filter.mp hkS).2
  have hrank_le : ∀ x ∈ M, ∀ k, validLen x k → k ≤ rank x := by
    intro x _ k hk
    exact Finset.le_sup (f := id)
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hlen_bdd x k hk)), hk⟩)
  have hrank_pos : ∀ x ∈ M, 1 ≤ rank x := by
    intro x hx
    exact hrank_le x hx 1 ⟨[x], by simp [hx], List.isChain_singleton x, rfl, rfl⟩
  have hrank_mono : ∀ x ∈ M, ∀ y ∈ M, lt x y → rank x < rank y := by
    intro x hx y hy hxy
    obtain ⟨L, hLmem, hLch, hLlast, hLlen⟩ := hrank_mem x hx
    have hch' : (L ++ [y]).IsChain lt := by
      rw [List.isChain_append]
      refine ⟨hLch, List.isChain_singleton y, ?_⟩
      intro a ha b hb
      rw [hLlast, Option.mem_def] at ha
      simp only [Option.some.injEq] at ha
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
      subst ha; subst hb
      exact hxy
    have hval : validLen y (rank x + 1) := by
      refine ⟨L ++ [y], ?_, hch', by simp, by simp [hLlen]⟩
      intro z hz
      rcases List.mem_append.mp hz with h | h
      · exact hLmem z h
      · rw [List.mem_singleton.mp h]; exact hy
    have := hrank_le y hy (rank x + 1) hval
    omega
  rcases M.eq_empty_or_nonempty with rfl | hMne
  · exact ⟨∅, Finset.empty_subset _, by simp, Or.inr (by simp)⟩
  obtain ⟨x_max, hx_max, hmax_eq⟩ := Finset.exists_mem_eq_sup M hMne rank
  let h := rank x_max
  have hpos : 1 ≤ h := hrank_pos x_max hx_max
  have hmaps : ∀ x ∈ M, rank x ∈ Finset.Icc 1 h := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨hrank_pos x hx, by
      have : rank x ≤ M.sup rank := Finset.le_sup (f := rank) hx
      omega⟩
  have hexA : ∃ r ∈ Finset.Icc 1 h, M.card ≤ h * (M.filter (fun x => rank x = r)).card := by
    by_contra hno
    push_neg at hno
    have hIcc_card : (Finset.Icc 1 h).card = h := by simp
    have hIcc_ne : (Finset.Icc 1 h).Nonempty := Finset.card_pos.mp (by omega)
    have hsum : M.card = ∑ r ∈ Finset.Icc 1 h, (M.filter (fun x => rank x = r)).card := by
      rw [← Finset.card_biUnion]
      · congr 1; ext x; simp only [Finset.mem_biUnion, Finset.mem_filter]
        exact ⟨fun hx => ⟨rank x, hmaps x hx, hx, rfl⟩, fun ⟨_, _, hx, _⟩ => hx⟩
      · intro a _ b _ hab
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro x h1 h2
        exact hab ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    have hlt : h * M.card < h * M.card := by
      calc h * M.card = ∑ r ∈ Finset.Icc 1 h,
              h * (M.filter (fun x => rank x = r)).card := by rw [hsum, Finset.mul_sum]
        _ < ∑ _r ∈ Finset.Icc 1 h, M.card := Finset.sum_lt_sum_of_nonempty hIcc_ne hno
        _ = h * M.card := by simp [hIcc_card]
    exact lt_irrefl _ hlt
  obtain ⟨r, _, hA_card⟩ := hexA
  let A := M.filter (fun x => rank x = r)
  obtain ⟨L, hLmem, hLch, _, hLlen⟩ := hrank_mem x_max hx_max
  let C : Finset α := L.toFinset
  have hCsub : C ⊆ M := fun x hx => hLmem x (List.mem_toFinset.mp hx)
  have hCcard : C.card = h := by
    rw [List.toFinset_card_of_nodup (hchain_nodup L hLmem hLch), hLlen]
  rcases le_or_gt h A.card with hle | hgt
  · refine ⟨A, Finset.filter_subset _ _, ?_, Or.inr ?_⟩
    · calc M.card ≤ h * A.card := hA_card
        _ ≤ A.card * A.card := Nat.mul_le_mul_right A.card hle
        _ = A.card ^ 2 := by ring
    · intro x hx y hy hxy
      have hx' := Finset.mem_filter.mp hx
      have hy' := Finset.mem_filter.mp hy
      have hlt := hrank_mono x hx'.1 y hy'.1 hxy
      omega
  · refine ⟨C, hCsub, ?_, Or.inl ?_⟩
    · calc M.card ≤ h * A.card := hA_card
        _ ≤ h * h := Nat.mul_le_mul_left h hgt.le
        _ = C.card ^ 2 := by rw [hCcard]; ring
    · intro x hx y hy hxy
      have hxL : x ∈ L := List.mem_toFinset.mp hx
      have hyL : y ∈ L := List.mem_toFinset.mp hy
      have hcomp : ∀ L' : List α, (∀ z ∈ L', z ∈ M) → L'.IsChain lt →
          ∀ a ∈ L', ∀ b ∈ L', a ≠ b → lt a b ∨ lt b a := by
        intro L'
        induction L' with
        | nil => intro _ _ _ ha; exact (List.not_mem_nil ha).elim
        | cons u t ih =>
          intro hmem' hch' a ha b hb hab
          have hlt_tail : ∀ v ∈ t, lt u v := by
            have hgo : ∀ t' : List α, ∀ w, w ∈ M → (∀ z ∈ t', z ∈ M) → List.IsChain lt (w :: t') →
                ∀ v ∈ t', lt w v := by
              intro t'
              induction t' with
              | nil => intro _ _ _ _ _ hv; exact (List.not_mem_nil hv).elim
              | cons c rest ih2 =>
                intro w hw hmt hch2 v hv
                rcases List.mem_cons.mp hv with rfl | hvr
                · exact (List.isChain_cons_cons.mp hch2).1
                · exact htrans w hw c (hmt c (List.mem_cons_self ..)) v
                    (hmt v (List.mem_cons_of_mem c hvr))
                    (List.isChain_cons_cons.mp hch2).1
                    (ih2 c (hmt c (List.mem_cons_self ..))
                      (fun z hz => hmt z (List.mem_cons_of_mem c hz))
                      (List.isChain_cons_cons.mp hch2).2 v hvr)
            exact hgo t u (hmem' u (List.mem_cons_self ..))
              (fun z hz => hmem' z (List.mem_cons_of_mem u hz)) hch'
          rcases List.mem_cons.mp ha with rfl | hat <;>
          rcases List.mem_cons.mp hb with rfl | hbt
          · exact (hab rfl).elim
          · exact Or.inl (hlt_tail b hbt)
          · exact Or.inr (hlt_tail a hat)
          · exact ih (fun z hz => hmem' z (List.mem_cons_of_mem u hz))
              (List.isChain_cons.mp hch').2 a hat b hbt hab
      exact hcomp L hLmem hLch x hxL y hyL hxy

/- ## Module 5: Triple Coloring, 3-Uniform Ramsey, and Main Theorem -/

/-- For a triple `a < b < c` in `Fin k`, construct the generic orthants `Q_A, Q_E` and extract
either a `Q_A`-free or `Q_E`-free subset of `U b` of size `≥ √|U b|`. -/
private lemma triple_orthant_split {k : ℕ} {X : Finset (ℝ^3)}
    (hX : IsInGeneralPosition X) (hX3 : 3 ≤ X.card)
    (h : Fin (k + 1) → ℝ^3) (U : Fin k → Finset (ℝ^3)) (σ : Bool)
    (hUX : ∀ i, U i ⊆ X)
    (hsign : ∀ (p r s : Fin (k + 1)), p < r → r < s → ∀ (i : Fin k), ∀ u ∈ U i,
      0 < signVal σ *
        ((-1 : ℝ) ^ (Finset.filter (fun d : Fin (k + 1) => i.val < d.val) {p, r, s}).card) *
        det4 ![h p, h r, h s, u])
    (a b c : Fin k) (hab : a < b) (hbc : b < c) :
    (∃ (Y : Finset (ℝ^3)) (P : Set (ℝ^3)),
      Y ⊆ U b ∧ (U b).card ≤ Y.card ^ 2 ∧
      (∃ e : (ℝ^3) ≃ᵃ[ℝ] (ℝ^3), P = {x | ∀ j : Fin 3, e x j ≤ 0} ∧
        ∀ (j : Fin 3) (Z : Finset (ℝ^3)), Z ⊆ Y → Z.card ≤ 3 →
          AffineIndependent ℝ (fun x : ↥(Z : Set (ℝ^3)) => fun k : Fin 2 => e x (j.succAbove k))) ∧
      (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → Disjoint (line[ℝ, x, y] : Set (ℝ^3)) P) ∧
      (∀ i : Fin k, (i < a ∨ (b < i ∧ i ≤ c)) → (U i : Set (ℝ^3)) ⊆ P)) ∨
    (∃ (Y : Finset (ℝ^3)) (P : Set (ℝ^3)),
      Y ⊆ U b ∧ (U b).card ≤ Y.card ^ 2 ∧
      (∃ e : (ℝ^3) ≃ᵃ[ℝ] (ℝ^3), P = {x | ∀ j : Fin 3, e x j ≤ 0} ∧
        ∀ (j : Fin 3) (Z : Finset (ℝ^3)), Z ⊆ Y → Z.card ≤ 3 →
          AffineIndependent ℝ (fun x : ↥(Z : Set (ℝ^3)) => fun k : Fin 2 => e x (j.succAbove k))) ∧
      (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → Disjoint (line[ℝ, x, y] : Set (ℝ^3)) P) ∧
      (∀ i : Fin k, ((a ≤ i ∧ i < b) ∨ c < i) → (U i : Set (ℝ^3)) ⊆ P)) := by
  classical
  -- Anchor indices in Fin (k + 1)
  let p0 : Fin (k + 1) := ⟨0, by omega⟩
  let pa : Fin (k + 1) := ⟨a.val, by omega⟩
  let pb : Fin (k + 1) := ⟨b.val, by omega⟩
  let pb1 : Fin (k + 1) := ⟨b.val + 1, by omega⟩
  let pc1 : Fin (k + 1) := ⟨c.val + 1, by omega⟩
  -- Affine forms for the three anchor triples
  obtain ⟨m₀, d₀, hm₀⟩ := det4_affine (h p0) (h pb) (h pb1)
  obtain ⟨m₁, d₁, hm₁⟩ := det4_affine (h pa) (h pb) (h pc1)
  obtain ⟨m₂, d₂, hm₂⟩ := det4_affine (h pa) (h pb1) (h pc1)
  -- Orient them: f0 = -σ * det(0, b, b+1, x), f1 = σ * det(a, b, c+1, x), f2 = σ * det(a, b+1, c+1, x)
  let s0 : ℝ := -signVal σ
  let s1 : ℝ := signVal σ
  let n₀ : ℝ^3 := s0 • m₀
  let c₀ : ℝ := s0 * d₀
  let n₁ : ℝ^3 := s1 • m₁
  let c₁ : ℝ := s1 * d₁
  let n₂ : ℝ^3 := s1 • m₂
  let c₂ : ℝ := s1 * d₂
  let g₀ (x : ℝ^3) : ℝ := inner ℝ n₀ x + c₀
  let g₁ (x : ℝ^3) : ℝ := inner ℝ n₁ x + c₁
  let g₂ (x : ℝ^3) : ℝ := inner ℝ n₂ x + c₂
  have hg₀_eq (x : ℝ^3) : g₀ x = -signVal σ * det4 ![h p0, h pb, h pb1, x] := by
    simp only [g₀, n₀, c₀, s0, inner_smul_left, conj_trivial, hm₀]; ring
  have hg₁_eq (x : ℝ^3) : g₁ x = signVal σ * det4 ![h pa, h pb, h pc1, x] := by
    simp only [g₁, n₁, c₁, s1, inner_smul_left, conj_trivial, hm₁]; ring
  have hg₂_eq (x : ℝ^3) : g₂ x = signVal σ * det4 ![h pa, h pb1, h pc1, x] := by
    simp only [g₂, n₂, c₂, s1, inner_smul_left, conj_trivial, hm₂]; ring
  -- Verify strict signs of g₀, g₁, g₂ on every cluster U i
  have hcnt_eval (p r s : Fin (k + 1)) (hpr : p < r) (hrs : r < s) (i : Fin k) :
      (Finset.filter (fun d : Fin (k + 1) => i.val < d.val) {p, r, s}).card =
        (if i.val < p.val then 1 else 0) +
        (if i.val < r.val then 1 else 0) +
        (if i.val < s.val then 1 else 0) := by
    have hps : p < s := hpr.trans hrs
    have hne1 : p ≠ r := hpr.ne
    have hne2 : p ≠ s := hps.ne
    have hne3 : r ≠ s := hrs.ne
    rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
    split_ifs <;> simp [Finset.card_insert_of_notMem, hne1, hne2, hne3]
  have hp0_pb : p0 < pb := by change 0 < b.val; have : a.val < b.val := hab; omega
  have hpb_pb1 : pb < pb1 := by change b.val < b.val + 1; omega
  have hpa_pb : pa < pb := by change a.val < b.val; exact hab
  have hpb_pc1 : pb < pc1 := by change b.val < c.val + 1; have : b.val < c.val := hbc; omega
  have hpa_pb1 : pa < pb1 := by change a.val < b.val + 1; have : a.val < b.val := hab; omega
  have hpb1_pc1 : pb1 < pc1 := by change b.val + 1 < c.val + 1; have : b.val < c.val := hbc; omega
  have hg₀_pos : ∀ u ∈ U b, 0 < g₀ u := by
    intro u hu
    have hs := hsign p0 pb pb1 hp0_pb hpb_pb1 b u hu
    rw [hcnt_eval p0 pb pb1 hp0_pb hpb_pb1 b] at hs
    have hcnt : (if b.val < p0.val then 1 else 0) + (if b.val < pb.val then 1 else 0) +
        (if b.val < pb1.val then 1 else 0) = 1 := by
      simp [p0, pb, pb1]
    rw [hcnt] at hs
    rw [hg₀_eq]
    norm_num at hs
    linarith
  have hg₀_neg : ∀ i : Fin k, i ≠ b → ∀ u ∈ U i, g₀ u < 0 := by
    intro i hib u hu
    have hs := hsign p0 pb pb1 hp0_pb hpb_pb1 i u hu
    rw [hcnt_eval p0 pb pb1 hp0_pb hpb_pb1 i] at hs
    have hcnt : (if i.val < p0.val then 1 else 0) + (if i.val < pb.val then 1 else 0) +
        (if i.val < pb1.val then 1 else 0) = if i.val < b.val then 2 else 0 := by
      have : i.val ≠ b.val := fun h => hib (Fin.ext h)
      simp only [p0, pb, pb1]
      split_ifs <;> omega
    rw [hcnt] at hs
    rw [hg₀_eq]
    split_ifs at hs <;> norm_num at hs <;> linarith
  have hg₁_neg : ∀ i : Fin k, (i < a ∨ (b ≤ i ∧ i ≤ c)) → ∀ u ∈ U i, g₁ u < 0 := by
    intro i hi u hu
    have hs := hsign pa pb pc1 hpa_pb hpb_pc1 i u hu
    rw [hcnt_eval pa pb pc1 hpa_pb hpb_pc1 i] at hs
    have hcnt : (if i.val < pa.val then 1 else 0) + (if i.val < pb.val then 1 else 0) +
        (if i.val < pc1.val then 1 else 0) = if i.val < a.val then 3 else 1 := by
      simp only [pa, pb, pc1]
      rcases hi with h1 | ⟨h2, h3⟩
      · have h1' : i.val < a.val := h1
        have : a.val < b.val := hab
        have : b.val < c.val := hbc
        split_ifs <;> omega
      · have h2' : b.val ≤ i.val := h2
        have h3' : i.val ≤ c.val := h3
        have : a.val < b.val := hab
        split_ifs <;> omega
    rw [hcnt] at hs
    rw [hg₁_eq]
    split_ifs at hs <;> norm_num at hs <;> linarith
  have hg₁_pos : ∀ i : Fin k, ((a ≤ i ∧ i < b) ∨ c < i) → ∀ u ∈ U i, 0 < g₁ u := by
    intro i hi u hu
    have hs := hsign pa pb pc1 hpa_pb hpb_pc1 i u hu
    rw [hcnt_eval pa pb pc1 hpa_pb hpb_pc1 i] at hs
    have hcnt : (if i.val < pa.val then 1 else 0) + (if i.val < pb.val then 1 else 0) +
        (if i.val < pc1.val then 1 else 0) = if i.val < b.val then 2 else 0 := by
      simp only [pa, pb, pc1]
      rcases hi with ⟨h1, h2⟩ | h3
      · have h1' : a.val ≤ i.val := h1
        have h2' : i.val < b.val := h2
        have : b.val < c.val := hbc
        split_ifs <;> omega
      · have h3' : c.val < i.val := h3
        have : a.val < b.val := hab
        have : b.val < c.val := hbc
        split_ifs <;> omega
    rw [hcnt] at hs
    rw [hg₁_eq]
    split_ifs at hs <;> norm_num at hs <;> linarith
  have hg₂_neg : ∀ i : Fin k, (i < a ∨ (b < i ∧ i ≤ c)) → ∀ u ∈ U i, g₂ u < 0 := by
    intro i hi u hu
    have hs := hsign pa pb1 pc1 hpa_pb1 hpb1_pc1 i u hu
    rw [hcnt_eval pa pb1 pc1 hpa_pb1 hpb1_pc1 i] at hs
    have hcnt : (if i.val < pa.val then 1 else 0) + (if i.val < pb1.val then 1 else 0) +
        (if i.val < pc1.val then 1 else 0) = if i.val < a.val then 3 else 1 := by
      simp only [pa, pb1, pc1]
      rcases hi with h1 | ⟨h2, h3⟩
      · have h1' : i.val < a.val := h1
        have : a.val < b.val := hab
        have : b.val < c.val := hbc
        split_ifs <;> omega
      · have h2' : b.val < i.val := h2
        have h3' : i.val ≤ c.val := h3
        have : a.val < b.val := hab
        split_ifs <;> omega
    rw [hcnt] at hs
    rw [hg₂_eq]
    split_ifs at hs <;> norm_num at hs <;> linarith
  have hg₂_pos : ∀ i : Fin k, ((a ≤ i ∧ i ≤ b) ∨ c < i) → ∀ u ∈ U i, 0 < g₂ u := by
    intro i hi u hu
    have hs := hsign pa pb1 pc1 hpa_pb1 hpb1_pc1 i u hu
    rw [hcnt_eval pa pb1 pc1 hpa_pb1 hpb1_pc1 i] at hs
    have hcnt : (if i.val < pa.val then 1 else 0) + (if i.val < pb1.val then 1 else 0) +
        (if i.val < pc1.val then 1 else 0) = if i.val ≤ b.val then 2 else 0 := by
      simp only [pa, pb1, pc1]
      rcases hi with ⟨h1, h2⟩ | h3
      · have h1' : a.val ≤ i.val := h1
        have h2' : i.val ≤ b.val := h2
        have : b.val < c.val := hbc
        split_ifs <;> omega
      · have h3' : c.val < i.val := h3
        have : a.val < b.val := hab
        have : b.val < c.val := hbc
        split_ifs <;> omega
    rw [hcnt] at hs
    rw [hg₂_eq]
    split_ifs at hs <;> norm_num at hs <;> linarith
  -- Choose ε > 0 small enough that perturbing (n₀, n₁, n₂) by < ε preserves all strict signs on ⋃ U_i
  let allU : Finset (ℝ^3) := Finset.univ.biUnion U
  have hmargin : ∃ η : ℝ, 0 < η ∧ ∀ u ∈ allU, η ≤ |g₀ u| ∧ η ≤ |g₁ u| ∧ η ≤ |g₂ u| := by
    have hne : ∀ u ∈ allU, 0 < min (|g₀ u|) (min (|g₁ u|) (|g₂ u|)) := by
      intro u hu
      obtain ⟨i, _, hui⟩ := Finset.mem_biUnion.mp hu
      have h0 : g₀ u ≠ 0 := by
        by_cases hib : i = b
        · subst hib; exact (hg₀_pos u hui).ne'
        · exact (hg₀_neg i hib u hui).ne
      have h1 : g₁ u ≠ 0 := by
        rcases lt_or_ge i a with hia | hia
        · exact (hg₁_neg i (Or.inl hia) u hui).ne
        · rcases lt_or_ge i b with hib | hib
          · exact (hg₁_pos i (Or.inl ⟨hia, hib⟩) u hui).ne'
          · rcases le_or_gt i c with hic | hic
            · exact (hg₁_neg i (Or.inr ⟨hib, hic⟩) u hui).ne
            · exact (hg₁_pos i (Or.inr hic) u hui).ne'
      have h2 : g₂ u ≠ 0 := by
        rcases lt_or_ge i a with hia | hia
        · exact (hg₂_neg i (Or.inl hia) u hui).ne
        · rcases le_or_gt i b with hib | hib
          · exact (hg₂_pos i (Or.inl ⟨hia, hib⟩) u hui).ne'
          · rcases le_or_gt i c with hic | hic
            · exact (hg₂_neg i (Or.inr ⟨hib, hic⟩) u hui).ne
            · exact (hg₂_pos i (Or.inr hic) u hui).ne'
      exact lt_min (abs_pos.mpr h0) (lt_min (abs_pos.mpr h1) (abs_pos.mpr h2))
    rcases allU.eq_empty_or_nonempty with hEmpty | hNonempty
    · exact ⟨1, one_pos, fun u hu => by rw [hEmpty] at hu; exact (Finset.notMem_empty u hu).elim⟩
    · obtain ⟨u₀, hu₀, hmin⟩ :=
        Finset.exists_min_image allU (fun u => min (|g₀ u|) (min (|g₁ u|) (|g₂ u|))) hNonempty
      refine ⟨min (|g₀ u₀|) (min (|g₁ u₀|) (|g₂ u₀|)), hne u₀ hu₀, fun u hu => ?_⟩
      have hle := hmin u hu
      exact ⟨le_trans hle (min_le_left _ _),
        le_trans hle (le_trans (min_le_right _ _) (min_le_left _ _)),
        le_trans hle (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  obtain ⟨η, hη, hη_le⟩ := hmargin
  have hRnorm : ∃ M : ℝ, 1 ≤ M ∧ ∀ u ∈ allU, ‖u‖ ≤ M := by
    rcases allU.eq_empty_or_nonempty with hE | hN
    · exact ⟨1, le_refl 1, fun u hu => by rw [hE] at hu; exact (Finset.notMem_empty u hu).elim⟩
    · obtain ⟨u₀, _, hmax⟩ := Finset.exists_max_image allU (fun u => ‖u‖) hN
      exact ⟨max 1 ‖u₀‖, le_max_left _ _, fun u hu => le_trans (hmax u hu) (le_max_right _ _)⟩
  obtain ⟨Mnorm, hMnorm1, hMnorm_le⟩ := hRnorm
  let ε : ℝ := η / (2 * Mnorm)
  have hε : 0 < ε := div_pos hη (by linarith)
  obtain ⟨n', hn'0, hn'1, hn'2, hdet_n', htriple_n'⟩ := perturb_three_normals hX n₀ n₁ n₂ ε hε
  let f₀ (x : ℝ^3) : ℝ := inner ℝ (n' 0) x + c₀
  let f₁ (x : ℝ^3) : ℝ := inner ℝ (n' 1) x + c₁
  let f₂ (x : ℝ^3) : ℝ := inner ℝ (n' 2) x + c₂
  have hdiff_bound (u : ℝ^3) (hu : u ∈ allU) :
      |f₀ u - g₀ u| < η / 2 ∧ |f₁ u - g₁ u| < η / 2 ∧ |f₂ u - g₂ u| < η / 2 := by
    have hstep (v v₀ : ℝ^3) (hv : ‖v - v₀‖ < ε) (c_off : ℝ) :
        |(inner ℝ v u + c_off) - (inner ℝ v₀ u + c_off)| < η / 2 := by
      have heq : (inner ℝ v u + c_off) - (inner ℝ v₀ u + c_off) = inner ℝ (v - v₀) u := by
        rw [inner_sub_left]; ring
      rw [heq]
      calc |inner ℝ (v - v₀) u| ≤ ‖v - v₀‖ * ‖u‖ := abs_real_inner_le_norm (v - v₀) u
        _ ≤ ‖v - v₀‖ * Mnorm := mul_le_mul_of_nonneg_left (hMnorm_le u hu) (norm_nonneg _)
        _ < ε * Mnorm := mul_lt_mul_of_pos_right hv (by linarith)
        _ = η / 2 := by dsimp [ε]; field_simp [show Mnorm ≠ 0 by linarith]
    exact ⟨hstep (n' 0) n₀ hn'0 c₀, hstep (n' 1) n₁ hn'1 c₁, hstep (n' 2) n₂ hn'2 c₂⟩
  -- Set δ = η / 4 > 0
  let δ : ℝ := η / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  -- Strict perturbed signs with margin δ!
  have hf_M : ∀ u ∈ U b, 0 < f₀ u ∧ f₁ u < 0 ∧ 0 < f₂ u := by
    intro u hu
    have hall : u ∈ allU := Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b, hu⟩
    have ⟨hd0, hd1, hd2⟩ := hdiff_bound u hall
    have ⟨hm0', hm1', hm2'⟩ := hη_le u hall
    have h0 := hg₀_pos u hu
    have h1 := hg₁_neg b (Or.inr ⟨le_refl b, hbc.le⟩) u hu
    have h2 := hg₂_pos b (Or.inl ⟨hab.le, le_refl b⟩) u hu
    rw [abs_of_pos h0] at hm0'
    rw [abs_of_neg h1] at hm1'
    rw [abs_of_pos h2] at hm2'
    rw [abs_lt] at hd0 hd1 hd2
    exact ⟨by linarith, by linarith, by linarith⟩
  have hf_A : ∀ i : Fin k, (i < a ∨ (b < i ∧ i ≤ c)) → ∀ u ∈ U i,
      f₀ u ≤ 0 ∧ f₁ u ≤ -δ ∧ f₂ u ≤ -δ := by
    intro i hi u hu
    have hall : u ∈ allU := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hu⟩
    have ⟨hd0, hd1, hd2⟩ := hdiff_bound u hall
    have ⟨hm0', hm1', hm2'⟩ := hη_le u hall
    have hib : i ≠ b := by rcases hi with h1 | ⟨h2, _⟩ <;> [exact (h1.trans hab).ne; exact h2.ne']
    have h0 := hg₀_neg i hib u hu
    have h1 := hg₁_neg i (by rcases hi with h1 | ⟨h2, h3⟩; exact Or.inl h1; exact Or.inr ⟨h2.le, h3⟩) u hu
    have h2 := hg₂_neg i hi u hu
    rw [abs_of_neg h0] at hm0'
    rw [abs_of_neg h1] at hm1'
    rw [abs_of_neg h2] at hm2'
    rw [abs_lt] at hd0 hd1 hd2
    dsimp [δ]
    exact ⟨by linarith, by linarith, by linarith⟩
  have hf_E : ∀ i : Fin k, ((a ≤ i ∧ i < b) ∨ c < i) → ∀ u ∈ U i,
      f₀ u ≤ 0 ∧ δ ≤ f₁ u ∧ δ ≤ f₂ u := by
    intro i hi u hu
    have hall : u ∈ allU := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hu⟩
    have ⟨hd0, hd1, hd2⟩ := hdiff_bound u hall
    have ⟨hm0', hm1', hm2'⟩ := hη_le u hall
    have hib : i ≠ b := by rcases hi with ⟨_, h2⟩ | h3 <;> [exact h2.ne; exact (hbc.trans h3).ne']
    have h0 := hg₀_neg i hib u hu
    have h1 := hg₁_pos i hi u hu
    have h2 := hg₂_pos i (by rcases hi with ⟨h1, h2⟩ | h3; exact Or.inl ⟨h1, h2.le⟩; exact Or.inr h3) u hu
    rw [abs_of_neg h0] at hm0'
    rw [abs_of_pos h1] at hm1'
    rw [abs_of_pos h2] at hm2'
    rw [abs_lt] at hd0 hd1 hd2
    dsimp [δ]
    exact ⟨by linarith, by linarith, by linarith⟩
  -- Define closed orthants Q_A and Q_E and their AffineEquivs
  let Q_A : Set (ℝ^3) := {x | f₀ x ≤ 0 ∧ f₁ x ≤ -δ ∧ f₂ x ≤ -δ}
  let Q_E : Set (ℝ^3) := {x | f₀ x ≤ 0 ∧ δ ≤ f₁ x ∧ δ ≤ f₂ x}
  let cA : Fin 3 → ℝ := ![c₀, c₁ + δ, c₂ + δ]
  let eA : (ℝ^3) ≃ᵃ[ℝ] (ℝ^3) := affineEquivOfNormals n' cA hdet_n'
  have hQA_eq : Q_A = {x | ∀ j : Fin 3, eA x j ≤ 0} := by
    ext x
    constructor
    · rintro ⟨h0, h1, h2⟩ j
      fin_cases j
      · simpa [eA, affineEquivOfNormals_apply, cA, f₀] using h0
      · have : inner ℝ (n' 1) x + (c₁ + δ) ≤ 0 := by dsimp [f₁] at h1; linarith
        simpa [eA, affineEquivOfNormals_apply, cA] using this
      · have : inner ℝ (n' 2) x + (c₂ + δ) ≤ 0 := by dsimp [f₂] at h2; linarith
        simpa [eA, affineEquivOfNormals_apply, cA] using this
    · intro hall
      have h0 := hall 0
      have h1 := hall 1
      have h2 := hall 2
      simp only [eA, affineEquivOfNormals_apply, cA, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val] at h0 h1 h2
      exact ⟨h0, by dsimp [f₁]; linarith, by dsimp [f₂]; linarith⟩
  let nE : Fin 3 → ℝ^3 := ![n' 0, -n' 1, -n' 2]
  let cE : Fin 3 → ℝ := ![c₀, δ - c₁, δ - c₂]
  have hdet_nE : (Matrix.of fun (j k : Fin 3) => nE j k).det ≠ 0 := by
    have heq : (Matrix.of fun (j k : Fin 3) => nE j k).det =
        (Matrix.of fun (j k : Fin 3) => n' j k).det := by
      rw [Matrix.det_fin_three, Matrix.det_fin_three]
      have h0 : ∀ k : Fin 3, nE 0 k = n' 0 k := fun _ => rfl
      have h1 : ∀ k : Fin 3, nE 1 k = -(n' 1 k) := fun _ => rfl
      have h2 : ∀ k : Fin 3, nE 2 k = -(n' 2 k) := fun _ => rfl
      simp only [Matrix.of_apply, h0, h1, h2]
      ring
    rw [heq]; exact hdet_n'
  let eE : (ℝ^3) ≃ᵃ[ℝ] (ℝ^3) := affineEquivOfNormals nE cE hdet_nE
  have hQE_eq : Q_E = {x | ∀ j : Fin 3, eE x j ≤ 0} := by
    ext x
    constructor
    · rintro ⟨h0, h1, h2⟩ j
      fin_cases j
      · simpa [eE, affineEquivOfNormals_apply, nE, cE, f₀] using h0
      · have : inner ℝ (-n' 1) x + (δ - c₁) ≤ 0 := by
          rw [inner_neg_left]; dsimp [f₁] at h1; linarith
        simpa [eE, affineEquivOfNormals_apply, nE, cE] using this
      · have : inner ℝ (-n' 2) x + (δ - c₂) ≤ 0 := by
          rw [inner_neg_left]; dsimp [f₂] at h2; linarith
        simpa [eE, affineEquivOfNormals_apply, nE, cE] using this
    · intro hall
      have h0 := hall 0
      have h1 := hall 1
      have h2 := hall 2
      simp only [eE, affineEquivOfNormals_apply, nE, cE, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, inner_neg_left] at h0 h1 h2
      exact ⟨h0, by dsimp [f₁]; linarith, by dsimp [f₂]; linarith⟩
  have htriple_nE : ∀ (r s : Fin 3), r < s → ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X,
      x ≠ y → x ≠ z → y ≠ z →
      inner ℝ (nE r) (y - x) * inner ℝ (nE s) (z - x) -
        inner ℝ (nE r) (z - x) * inner ℝ (nE s) (y - x) ≠ 0 := by
    intro r s hrs x hx y hy z hz hxy hxz hyz
    have h := htriple_n' r s hrs x hx y hy z hz hxy hxz hyz
    fin_cases r <;> fin_cases s <;> try (exfalso; exact absurd hrs (by decide))
    · change inner ℝ (n' 0) (y - x) * inner ℝ (-n' 1) (z - x) -
        inner ℝ (n' 0) (z - x) * inner ℝ (-n' 1) (y - x) ≠ 0
      have h01 := htriple_n' 0 1 (by decide) x hx y hy z hz hxy hxz hyz
      simp only [inner_neg_left]; intro h0; exact h01 (by linear_combination -h0)
    · change inner ℝ (n' 0) (y - x) * inner ℝ (-n' 2) (z - x) -
        inner ℝ (n' 0) (z - x) * inner ℝ (-n' 2) (y - x) ≠ 0
      have h02 := htriple_n' 0 2 (by decide) x hx y hy z hz hxy hxz hyz
      simp only [inner_neg_left]; intro h0; exact h02 (by linear_combination -h0)
    · change inner ℝ (-n' 1) (y - x) * inner ℝ (-n' 2) (z - x) -
        inner ℝ (-n' 1) (z - x) * inner ℝ (-n' 2) (y - x) ≠ 0
      have h12 := htriple_n' 1 2 (by decide) x hx y hy z hz hxy hxz hyz
      simp only [inner_neg_left]; intro h0; exact h12 (by linear_combination h0)
  -- Affine combination property of f₀, f₁, f₂
  have hf₀_aff : ∀ x y t, f₀ (t • x + (1 - t) • y) = t * f₀ x + (1 - t) * f₀ y := by
    intro x y t; simp only [f₀, inner_add_right, inner_smul_right]; ring
  have hf₁_aff : ∀ x y t, f₁ (t • x + (1 - t) • y) = t * f₁ x + (1 - t) * f₁ y := by
    intro x y t; simp only [f₁, inner_add_right, inner_smul_right]; ring
  have hf₂_aff : ∀ x y t, f₂ (t • x + (1 - t) • y) = t * f₂ x + (1 - t) * f₂ y := by
    intro x y t; simp only [f₂, inner_add_right, inner_smul_right]; ring
  -- Define strict partial order lt on U b: x ≺ y ↔ ∃ z ∈ Q_A, ∃ t ∈ (0, 1), x = t • y + (1 - t) • z
  let lt (x y : ℝ^3) : Prop := ∃ z ∈ Q_A, ∃ t : ℝ, 0 < t ∧ t < 1 ∧ x = t • y + (1 - t) • z
  have hlt_f0 : ∀ x ∈ U b, ∀ y ∈ U b, lt x y → f₀ x < f₀ y := by
    rintro x _ y hy ⟨z, hz, t, ht0, ht1, rfl⟩
    rw [hf₀_aff]
    have hy0 := (hf_M y hy).1
    have hz0 := hz.1
    nlinarith
  have hlt_irr : ∀ x ∈ U b, ¬ lt x x := by
    intro x hx hxx
    exact lt_irrefl _ (hlt_f0 x hx x hx hxx)
  have hlt_trans : ∀ x ∈ U b, ∀ y ∈ U b, ∀ z ∈ U b, lt x y → lt y z → lt x z := by
    rintro x _ y _ w _ ⟨q1, hq1, t1, ht1_0, ht1_1, rfl⟩ ⟨q2, hq2, t2, ht2_0, ht2_1, rfl⟩
    let t := t1 * t2
    have ht0 : 0 < t := mul_pos ht1_0 ht2_0
    have ht1 : t < 1 := by nlinarith
    let α := (t1 * (1 - t2)) / (1 - t)
    have hα0 : 0 ≤ α := div_nonneg (by nlinarith) (by linarith)
    have hα1 : α ≤ 1 := (div_le_one (by linarith)).mpr (by dsimp [t]; nlinarith)
    let q := α • q2 + (1 - α) • q1
    have hq_mem : q ∈ Q_A := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hf₀_aff]; nlinarith [hq1.1, hq2.1]
      · rw [hf₁_aff]; nlinarith [hq1.2.1, hq2.2.1]
      · rw [hf₂_aff]; nlinarith [hq1.2.2, hq2.2.2]
    refine ⟨q, hq_mem, t, ht0, ht1, ?_⟩
    ext j
    simp only [q, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have hne : 1 - t1 * t2 ≠ 0 := by linarith
    dsimp [α, t]
    field_simp [hne]
    ring
  -- Line intersection with Q_A ↔ lt x y ∨ lt y x
  have hline_QA' : ∀ x ∈ U b, ∀ y ∈ U b, x ≠ y →
      (∃ z ∈ Q_A, z ∈ (line[ℝ, x, y] : Set (ℝ^3))) → lt x y ∨ lt y x := by
    intro x hx y hy hxy ⟨z, hz, hzL⟩
    rw [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq] at hzL
    obtain ⟨s, hs⟩ := hzL
    have hz_eq : z = (1 - s) • x + s • y := by
      rw [← hs, AffineMap.lineMap_apply_module]
    have hfx := (hf_M x hx).1
    have hfy := (hf_M y hy).1
    have hfz := hz.1
    have hfz_lin : f₀ z = (1 - s) * f₀ x + s * f₀ y := by
      rw [hz_eq, add_comm, hf₀_aff y x s]
      ring
    rcases lt_or_ge s 0 with hs0 | hs0
    · left
      refine ⟨z, hz, (-s) / (1 - s), div_pos (by linarith) (by linarith),
        (div_lt_one (by linarith)).mpr (by linarith), ?_⟩
      ext j
      have hzj := congrArg (fun w : ℝ^3 => w j) hz_eq
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hzj ⊢
      have hne : 1 - s ≠ 0 := by linarith
      field_simp [hne]
      linarith
    · have hs1 : 1 < s := by
        by_contra hle
        push_neg at hle
        have hm1 : 0 ≤ (1 - s) * f₀ x := mul_nonneg (by linarith) hfx.le
        have hm2 : 0 ≤ s * f₀ y := mul_nonneg hs0 hfy.le
        have hm3 : 0 < (1 - s) * f₀ x + s * f₀ y := by
          rcases eq_or_lt_of_le hs0 with rfl | hs_pos
          · linarith
          · have : 0 < s * f₀ y := mul_pos hs_pos hfy
            linarith
        linarith
      right
      refine ⟨z, hz, (s - 1) / s, div_pos (by linarith) (by linarith),
        (div_lt_one (by linarith)).mpr (by linarith), ?_⟩
      ext j
      have hzj := congrArg (fun w : ℝ^3 => w j) hz_eq
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hzj ⊢
      have hne : s ≠ 0 := by linarith
      field_simp [hne]
      linarith
  -- Apply chain_or_antichain to U b
  obtain ⟨Y, hYsub, hYcard, hchain | hanti⟩ := chain_or_antichain (U b) lt hlt_irr hlt_trans
  · -- Chain: Y is Q_E-free!
    right
    refine ⟨Y, Q_E, hYsub, hYcard, ⟨eE, hQE_eq, fun j Z hZY hZc =>
      proj_affineIndependent hX3 nE cE hdet_nE htriple_nE j Z (hZY.trans (hYsub.trans (hUX b))) hZc⟩,
      ?_, fun i hi u hu => hf_E i hi u hu⟩
    intro x hx y hy hxy
    rw [Set.disjoint_left]
    intro z hzL hzE
    -- Since Y is a chain, lt x y ∨ lt y x, so line[ℝ, x, y] meets Q_A!
    have hQA_meet : ∃ qA ∈ Q_A, qA ∈ (line[ℝ, x, y] : Set (ℝ^3)) := by
      rcases hchain x hx y hy hxy with ⟨qA, hqA, t, ht0, ht1, hEq⟩ | ⟨qA, hqA, t, ht0, ht1, hEq⟩
      · refine ⟨qA, hqA, ?_⟩
        rw [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq]
        refine ⟨-t / (1 - t), ?_⟩
        ext j
        have hj := congrArg (fun w : ℝ^3 => w j) hEq
        simp only [AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hj ⊢
        have hne : 1 - t ≠ 0 := by linarith
        field_simp [hne]; linarith
      · refine ⟨qA, hqA, ?_⟩
        rw [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq]
        refine ⟨1 / (1 - t), ?_⟩
        ext j
        have hj := congrArg (fun w : ℝ^3 => w j) hEq
        simp only [AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hj ⊢
        have hne : 1 - t ≠ 0 := by linarith
        field_simp [hne]; linarith
    obtain ⟨qA, hqA, hqAL⟩ := hQA_meet
    have hxM := hf_M x (hYsub hx)
    exact no_line_three_sets hf₀_aff hf₁_aff hf₂_aff hδ
      hxM.1 hxM.2.1 hxM.2.2 hqA.1 hqA.2.1 hqA.2.2 hzE.1 hzE.2.1 hzE.2.2
      (left_mem_affineSpan_pair ℝ x y) hqAL hzL
  · -- Antichain: Y is Q_A-free!
    left
    refine ⟨Y, Q_A, hYsub, hYcard, ⟨eA, hQA_eq, fun j Z hZY hZc =>
      proj_affineIndependent hX3 n' cA hdet_n' htriple_n' j Z (hZY.trans (hYsub.trans (hUX b))) hZc⟩,
      ?_, fun i hi u hu => hf_A i hi u hu⟩
    intro x hx y hy hxy
    rw [Set.disjoint_left]
    intro z hzL hzA
    rcases hline_QA' x (hYsub hx) y (hYsub hy) hxy ⟨z, hzA, hzL⟩ with hlt | hlt
    · exact hanti x hx y hy hlt
    · exact hanti y hy x hx hlt

end Erdos651H1Proof

theorem OMA.solution : OMA.R_Erdos651_erdos_651_R1_H1_R1.H1 := by
  classical
  intro t ht
  obtain ⟨k, hRam3⟩ := Erdos651H1Proof.ramsey_orderEmb 3 (2 * t + 1)
  obtain ⟨C, hCpos, hExtract⟩ := Erdos651H1Proof.extract_anchors_clusters k
  refine ⟨max 3 (C ^ 2), ?_⟩
  intro X hX hXcard
  have hX3 : 3 ≤ X.card := le_trans (le_max_left 3 (C ^ 2)) hXcard
  have hXC2 : C ^ 2 ≤ X.card := le_trans (le_max_right 3 (C ^ 2)) hXcard
  have hXC : C ≤ X.card := le_trans (by nlinarith) hXC2
  obtain ⟨h, U, σ, hUX, hUcard, hUdisj, hsign⟩ := hExtract X hX hXC
  -- Color each ordered triple f : Fin 3 ↪o Fin k: true if Q_A-free witness exists, false otherwise
  let redProp (f : Fin 3 ↪o Fin k) : Prop :=
    ∃ (Y : Finset (ℝ^3)) (P : Set (ℝ^3)),
      Y ⊆ U (f 1) ∧ (U (f 1)).card ≤ Y.card ^ 2 ∧
      (∃ e : (ℝ^3) ≃ᵃ[ℝ] (ℝ^3), P = {x | ∀ j : Fin 3, e x j ≤ 0} ∧
        ∀ (j : Fin 3) (Z : Finset (ℝ^3)), Z ⊆ Y → Z.card ≤ 3 →
          AffineIndependent ℝ (fun x : ↥(Z : Set (ℝ^3)) => fun m : Fin 2 => e x (j.succAbove m))) ∧
      (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → Disjoint (line[ℝ, x, y] : Set (ℝ^3)) P) ∧
      (∀ i : Fin k, (i < f 0 ∨ (f 1 < i ∧ i ≤ f 2)) → (U i : Set (ℝ^3)) ⊆ P)
  let blueProp (f : Fin 3 ↪o Fin k) : Prop :=
    ∃ (Y : Finset (ℝ^3)) (P : Set (ℝ^3)),
      Y ⊆ U (f 1) ∧ (U (f 1)).card ≤ Y.card ^ 2 ∧
      (∃ e : (ℝ^3) ≃ᵃ[ℝ] (ℝ^3), P = {x | ∀ j : Fin 3, e x j ≤ 0} ∧
        ∀ (j : Fin 3) (Z : Finset (ℝ^3)), Z ⊆ Y → Z.card ≤ 3 →
          AffineIndependent ℝ (fun x : ↥(Z : Set (ℝ^3)) => fun m : Fin 2 => e x (j.succAbove m))) ∧
      (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → Disjoint (line[ℝ, x, y] : Set (ℝ^3)) P) ∧
      (∀ i : Fin k, ((f 0 ≤ i ∧ i < f 1) ∨ f 2 < i) → (U i : Set (ℝ^3)) ⊆ P)
  have hsplit : ∀ f : Fin 3 ↪o Fin k, redProp f ∨ blueProp f := fun f =>
    Erdos651H1Proof.triple_orthant_split hX hX3 h U σ hUX hsign (f 0) (f 1) (f 2)
      (f.lt_iff_lt.mpr (by decide : (0 : Fin 3) < 1))
      (f.lt_iff_lt.mpr (by decide : (1 : Fin 3) < 2))
  let col3 (f : Fin 3 ↪o Fin k) : Bool := decide (redProp f)
  obtain ⟨s, col, hs_mono⟩ := hRam3 col3
  -- Final cluster centers are s (2*r + 1) for r : Fin t
  let center (r : Fin t) : Fin k := s ⟨2 * r.val + 1, by omega⟩
  have hcard_lift : ∀ (r : Fin t) (Y : Finset (ℝ^3)),
      (U (center r)).card ≤ Y.card ^ 2 → X.card ≤ Y.card ^ 4 := by
    intro r Y hY2
    have h1 : X.card ≤ C * (U (center r)).card := hUcard (center r)
    have h2 : X.card * X.card ≤ C ^ 2 * Y.card ^ 4 := by
      calc X.card * X.card ≤ (C * (U (center r)).card) * (C * (U (center r)).card) :=
            Nat.mul_le_mul h1 h1
        _ = C ^ 2 * ((U (center r)).card * (U (center r)).card) := by ring
        _ ≤ C ^ 2 * (Y.card ^ 2 * Y.card ^ 2) :=
            Nat.mul_le_mul_left (C ^ 2) (Nat.mul_le_mul hY2 hY2)
        _ = C ^ 2 * Y.card ^ 4 := by ring
    have h3 : C ^ 2 * X.card ≤ C ^ 2 * Y.card ^ 4 :=
      le_trans (Nat.mul_le_mul_right X.card hXC2) h2
    exact Nat.le_of_mul_le_mul_left h3 (pow_pos hCpos 2)
  cases col with
  | true =>
    -- Red case: for center s(2r+1), use triple (s(2r), s(2r+1), s(2t))
    let fRed (r : Fin t) : Fin 3 ↪o Fin (2 * t + 1) :=
      OrderEmbedding.ofStrictMono
        (fun a : Fin 3 => match a with
          | ⟨0, _⟩ => ⟨2 * r.val, by omega⟩
          | ⟨1, _⟩ => ⟨2 * r.val + 1, by omega⟩
          | ⟨2, _⟩ => ⟨2 * t, by omega⟩)
        (by
          intro a b hab
          fin_cases a <;> fin_cases b <;>
            first | exact absurd hab (by decide) | (rw [Fin.lt_def]; dsimp only; omega))
    have hred (r : Fin t) : redProp ((fRed r).trans s) := by
      have h := hs_mono (fRed r)
      exact of_decide_eq_true h
    let Y : Fin t → Finset (ℝ^3) := fun r => Classical.choose (hred r)
    let P : Fin t → Set (ℝ^3) := fun r => Classical.choose (Classical.choose_spec (hred r))
    have hspec (r : Fin t) := Classical.choose_spec (Classical.choose_spec (hred r))
    refine ⟨Y, P, ?_, ?_⟩
    · intro r
      obtain ⟨hYsub, hY2, he, hdisj, _⟩ := hspec r
      exact ⟨hYsub.trans (hUX (center r)), hcard_lift r (Y r) hY2, he, hdisj⟩
    · intro i j hij
      obtain ⟨hYsub_i, _, _, _, hcont_i⟩ := hspec i
      obtain ⟨hYsub_j, _, _, _, _⟩ := hspec j
      have hne_c : center i ≠ center j := by
        intro heq
        have h' := congrArg Fin.val (s.injective heq)
        change 2 * i.val + 1 = 2 * j.val + 1 at h'
        exact hij (Fin.ext (by omega))
      refine ⟨(hUdisj (center i) (center j) hne_c).mono hYsub_i hYsub_j, ?_⟩
      have hpos : center j < ((fRed i).trans s) 0 ∨
          (((fRed i).trans s) 1 < center j ∧ center j ≤ ((fRed i).trans s) 2) := by
        rcases lt_or_gt_of_ne hij with hlt | hgt
        · right
          constructor
          · apply s.lt_iff_lt.mpr
            change 2 * i.val + 1 < 2 * j.val + 1
            have : i.val < j.val := hlt
            omega
          · apply s.le_iff_le.mpr
            change 2 * j.val + 1 ≤ 2 * t
            omega
        · left
          apply s.lt_iff_lt.mpr
          change 2 * j.val + 1 < 2 * i.val
          have : j.val < i.val := hgt
          omega
      exact (Finset.coe_subset.mpr hYsub_j).trans (hcont_i (center j) hpos)
  | false =>
    -- Blue case: for center s(2r+1), use triple (s(0), s(2r+1), s(2r+2))
    let fBlue (r : Fin t) : Fin 3 ↪o Fin (2 * t + 1) :=
      OrderEmbedding.ofStrictMono
        (fun a : Fin 3 => match a with
          | ⟨0, _⟩ => ⟨0, by omega⟩
          | ⟨1, _⟩ => ⟨2 * r.val + 1, by omega⟩
          | ⟨2, _⟩ => ⟨2 * r.val + 2, by omega⟩)
        (by
          intro a b hab
          fin_cases a <;> fin_cases b <;>
            first | exact absurd hab (by decide) | (rw [Fin.lt_def]; dsimp only; omega))
    have hblue (r : Fin t) : blueProp ((fBlue r).trans s) := by
      have h := hs_mono (fBlue r)
      have hnr : ¬ redProp ((fBlue r).trans s) := of_decide_eq_false h
      exact (hsplit ((fBlue r).trans s)).resolve_left hnr
    let Y : Fin t → Finset (ℝ^3) := fun r => Classical.choose (hblue r)
    let P : Fin t → Set (ℝ^3) := fun r => Classical.choose (Classical.choose_spec (hblue r))
    have hspec (r : Fin t) := Classical.choose_spec (Classical.choose_spec (hblue r))
    refine ⟨Y, P, ?_, ?_⟩
    · intro r
      obtain ⟨hYsub, hY2, he, hdisj, _⟩ := hspec r
      exact ⟨hYsub.trans (hUX (center r)), hcard_lift r (Y r) hY2, he, hdisj⟩
    · intro i j hij
      obtain ⟨hYsub_i, _, _, _, hcont_i⟩ := hspec i
      obtain ⟨hYsub_j, _, _, _, _⟩ := hspec j
      have hne_c : center i ≠ center j := by
        intro heq
        have h' := congrArg Fin.val (s.injective heq)
        change 2 * i.val + 1 = 2 * j.val + 1 at h'
        exact hij (Fin.ext (by omega))
      refine ⟨(hUdisj (center i) (center j) hne_c).mono hYsub_i hYsub_j, ?_⟩
      have hpos : (((fBlue i).trans s) 0 ≤ center j ∧ center j < ((fBlue i).trans s) 1) ∨
          ((fBlue i).trans s) 2 < center j := by
        rcases lt_or_gt_of_ne hij with hlt | hgt
        · right
          apply s.lt_iff_lt.mpr
          change 2 * i.val + 2 < 2 * j.val + 1
          have : i.val < j.val := hlt
          omega
        · left
          constructor
          · apply s.le_iff_le.mpr
            change 0 ≤ 2 * j.val + 1
            omega
          · apply s.lt_iff_lt.mpr
            change 2 * j.val + 1 < 2 * i.val + 1
            have : j.val < i.val := hgt
            omega
      exact (Finset.coe_subset.mpr hYsub_j).trans (hcont_i (center j) hpos)
