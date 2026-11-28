import OMAReductions.R_Green5_green_5_variants_kedlaya_R1

/-!
Kedlaya's product-free coset construction: for any proper subgroup `H < Q` of index `m`,
there is a product-free subset `T ⊆ Q` of size at least `(7 / 384) * |Q| / sqrt m`.
-/

section

open Finset

private lemma card_fiber_smul {Q : Type} [Group Q] [Fintype Q] (H : Subgroup Q)
    [Fintype H] (u v : Q ⧸ H) [DecidablePred fun x : Q => x • u = v] :
    (Finset.univ.filter fun x : Q => x • u = v).card = Fintype.card H := by
  classical
  obtain ⟨a, rfl⟩ := Quotient.exists_rep u
  obtain ⟨b, rfl⟩ := Quotient.exists_rep v
  have hiff : ∀ x : Q, x • (a : Q ⧸ H) = (b : Q ⧸ H) ↔ ∃ h : H, x = b * (h : Q) * a⁻¹ := by
    intro x
    change ((x * a : Q) : Q ⧸ H) = (b : Q ⧸ H) ↔ _
    rw [QuotientGroup.eq]
    constructor
    · intro hx
      refine ⟨⟨((x * a)⁻¹ * b)⁻¹, H.inv_mem hx⟩, ?_⟩
      group
    · rintro ⟨h, rfl⟩
      have heq : (b * (h : Q) * a⁻¹ * a)⁻¹ * b = (h : Q)⁻¹ := by group
      rw [heq]
      exact H.inv_mem h.2
  let f : H → {x : Q // x • (a : Q ⧸ H) = (b : Q ⧸ H)} :=
    fun h => ⟨b * (h : Q) * a⁻¹, (hiff _).2 ⟨h, rfl⟩⟩
  have hf_bij : Function.Bijective f := by
    constructor
    · intro h1 h2 heq
      have heq' : b * (h1 : Q) * a⁻¹ = b * (h2 : Q) * a⁻¹ := congrArg Subtype.val heq
      apply Subtype.ext
      calc
        (h1 : Q) = b⁻¹ * (b * (h1 : Q) * a⁻¹) * a := by group
        _ = b⁻¹ * (b * (h2 : Q) * a⁻¹) * a := by rw [heq']
        _ = (h2 : Q) := by group
    · rintro ⟨x, hx⟩
      obtain ⟨h, rfl⟩ := (hiff x).1 hx
      exact ⟨h, rfl⟩
  calc
    (Finset.univ.filter fun x : Q => x • (a : Q ⧸ H) = (b : Q ⧸ H)).card
        = Fintype.card {x : Q // x • (a : Q ⧸ H) = (b : Q ⧸ H)} := (Fintype.card_subtype _).symm
    _ = Fintype.card H := (Fintype.card_of_bijective hf_bij).symm

private lemma card_fun_zero {X : Type*} [Fintype X] [DecidableEq X] (q : ℕ) [NeZero q]
    (U : Finset X) :
    (Finset.univ.filter fun f : X → Fin q => ∀ u ∈ U, f u = 0).card =
      q ^ (Fintype.card X - U.card) := by
  classical
  let A := {f : X → Fin q // ∀ u ∈ U, f u = 0}
  let B := {x : X // x ∉ U} → Fin q
  let φ : A → B := fun f x => f.1 x.1
  let ψ : B → A := fun g => ⟨fun x => if hx : x ∈ U then 0 else g ⟨x, hx⟩, fun u hu => by simp [hu]⟩
  have heq : Equiv A B :=
    { toFun := φ
      invFun := ψ
      left_inv := fun f => by
        apply Subtype.ext
        funext x
        dsimp [φ, ψ]
        by_cases hx : x ∈ U
        · simp [hx, f.2 x hx]
        · simp [hx]
      right_inv := fun g => by
        funext x
        dsimp [φ, ψ]
        simp [x.2] }
  have hcardB : Fintype.card {x : X // x ∉ U} = Fintype.card X - U.card := by
    rw [Fintype.card_subtype]
    have hsplit := Finset.card_sdiff_add_card_inter (Finset.univ : Finset X) U
    simp only [Finset.univ_inter] at hsplit
    have hfilter : Finset.univ.filter (fun x : X => x ∉ U) = Finset.univ \ U := by
      ext x; simp
    rw [hfilter]
    rw [Finset.card_univ] at hsplit
    omega
  calc
    (Finset.univ.filter fun f : X → Fin q => ∀ u ∈ U, f u = 0).card
        = Fintype.card A := (Fintype.card_subtype _).symm
    _ = Fintype.card B := Fintype.card_congr heq
    _ = q ^ Fintype.card {x : X // x ∉ U} := by
        rw [Fintype.card_fun, Fintype.card_fin]
    _ = q ^ (Fintype.card X - U.card) := by rw [hcardB]

private lemma kedlaya_index_two (Q : Type) [Group Q] [Fintype Q] (H : Subgroup Q)
    (hm2 : H.index = 2) :
    ∃ T : Finset Q, IsProductFree (T : Set Q) ∧
      ((7 : ℝ) / 384) * Fintype.card Q / (H.index : ℝ) ^ ((1 : ℝ) / 2) ≤ (T.card : ℝ) := by
  classical
  have hN : H.Normal := Subgroup.normal_of_index_eq_two hm2
  let T : Finset Q := Finset.univ.filter fun x => x ∉ H
  refine ⟨T, isProductFree_iff.2 ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, T, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy hxy
    have hx1 : (x : Q ⧸ H) ≠ 1 := by rwa [ne_eq, QuotientGroup.eq_one_iff]
    have hy1 : (y : Q ⧸ H) ≠ 1 := by rwa [ne_eq, QuotientGroup.eq_one_iff]
    have hcardX : Fintype.card (Q ⧸ H) = 2 := by
      rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card H, hm2]
    have hx_eq_y : (x : Q ⧸ H) = (y : Q ⧸ H) := by
      by_contra hne
      have h3 : ({1, (x : Q ⧸ H), (y : Q ⧸ H)} : Finset (Q ⧸ H)).card = 3 := by
        simp [hx1.symm, hy1.symm, hne]
      have hle := Finset.card_le_univ ({1, (x : Q ⧸ H), (y : Q ⧸ H)} : Finset (Q ⧸ H))
      rw [hcardX] at hle
      omega
    have hy_inv : (y : Q ⧸ H)⁻¹ = (y : Q ⧸ H) := by
      have hy1' : (y : Q ⧸ H)⁻¹ ≠ 1 := by simp [hy1]
      by_contra hne
      have h3 : ({1, (y : Q ⧸ H), (y : Q ⧸ H)⁻¹} : Finset (Q ⧸ H)).card = 3 := by
        simp [hy1.symm, hy1'.symm, Ne.symm hne]
      have hle := Finset.card_le_univ ({1, (y : Q ⧸ H), (y : Q ⧸ H)⁻¹} : Finset (Q ⧸ H))
      rw [hcardX] at hle
      omega
    have hmul : ((x * y : Q) : Q ⧸ H) = 1 := by
      change (x : Q ⧸ H) * (y : Q ⧸ H) = 1
      rw [hx_eq_y]
      conv_lhs => arg 1; rw [← hy_inv]
      rw [inv_mul_cancel]
    rw [QuotientGroup.eq_one_iff] at hmul
    exact hxy hmul
  · have hH_mul := Subgroup.index_mul_card H
    rw [hm2, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hH_mul
    have hH_card : (Finset.univ.filter fun x : Q => x ∈ H).card = Fintype.card H := by
      rw [← Fintype.card_subtype]
    have hpart := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Q)) (p := fun x : Q => x ∈ H)
    rw [Finset.card_univ, hH_card] at hpart
    have hT_eq : T.card = Fintype.card H := by
      dsimp [T]
      omega
    have hT2 : 2 * T.card = Fintype.card Q := by omega
    have hT2R : (2 : ℝ) * (T.card : ℝ) = (Fintype.card Q : ℝ) := by exact_mod_cast hT2
    have hsq2 : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / 2) := by
      simpa using Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [hm2]
    calc
      ((7 : ℝ) / 384) * Fintype.card Q / ((2 : ℕ) : ℝ) ^ ((1 : ℝ) / 2)
          ≤ ((7 : ℝ) / 384) * Fintype.card Q / 1 := by
              apply div_le_div_of_nonneg_left (by positivity) zero_lt_one
              exact_mod_cast hsq2
      _ = ((7 : ℝ) / 192) * (T.card : ℝ) := by rw [← hT2R]; ring
      _ ≤ (T.card : ℝ) := by
          have h0 : (0 : ℝ) ≤ (T.card : ℝ) := Nat.cast_nonneg _
          nlinarith

end

theorem OMA.solution : OMA.R_Green5_green_5_variants_kedlaya_R1.H2 := by
  classical
  refine ⟨(7 : ℝ) / 384, by norm_num, fun Q _ _ H hH => ?_⟩
  set m : ℕ := H.index
  have hm1 : 1 < m := H.one_lt_index_of_ne_top hH
  by_cases hm2 : m = 2
  · exact kedlaya_index_two Q H hm2
  have hm3 : 3 ≤ m := by omega
  let q : ℕ := 4 * (Nat.sqrt m + 1)
  have hsqrt1 : 1 ≤ Nat.sqrt m := by
    rw [Nat.le_sqrt]; omega
  have hq8 : 8 ≤ q := by dsimp [q]; omega
  have hq_pos : 0 < q := by omega
  let : NeZero q := ⟨hq_pos.ne'⟩
  have h16m_lt : 16 * m < q ^ 2 := by
    have hlt := Nat.lt_succ_sqrt m
    dsimp [q]
    nlinarith
  have hq2_le : q ^ 2 ≤ 64 * m := by
    have hle := Nat.sqrt_le m
    have h2 : Nat.sqrt m + 1 ≤ 2 * Nat.sqrt m := by omega
    calc
      q ^ 2 = 16 * (Nat.sqrt m + 1) * (Nat.sqrt m + 1) := by dsimp [q]; ring
      _ ≤ 16 * (2 * Nat.sqrt m) * (2 * Nat.sqrt m) := by gcongr
      _ = 64 * (Nat.sqrt m * Nat.sqrt m) := by ring
      _ ≤ 64 * m := Nat.mul_le_mul_left 64 hle
  have hX_card : Fintype.card (Q ⧸ H) = m := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card H]
  have hH_mul : m * Fintype.card H = Fintype.card Q := by
    have := Subgroup.index_mul_card H
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this
  let s0 : Q ⧸ H := (1 : Q)
  let Fix (x : Q) : Finset (Q ⧸ H) := Finset.univ.filter fun u : Q ⧸ H => x • u = u
  let Q0 : Finset Q := Finset.univ.filter fun x : Q => x • s0 ≠ s0 ∧ (Fix x).card ≤ 2
  have hQ0_ge : Fintype.card Q ≤ 3 * Q0.card := by
    let Bad1 : Finset Q := Finset.univ.filter fun x : Q => x • s0 = s0
    let Bad2 : Finset Q := Finset.univ.filter fun x : Q => 3 ≤ (Fix x).card
    have hBad1 : Bad1.card = Fintype.card H := card_fiber_smul H s0 s0
    have hsum_fix : ∑ x : Q, (Fix x).card = Fintype.card Q := by
      have heq : ∑ x : Q, (Fix x).card =
          ∑ x : Q, ∑ u : Q ⧸ H, if x • u = u then 1 else 0 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp [Fix]
      rw [heq, Finset.sum_comm]
      calc
        ∑ u : Q ⧸ H, ∑ x : Q, (if x • u = u then 1 else 0)
            = ∑ u : Q ⧸ H, (Finset.univ.filter fun x : Q => x • u = u).card := by
              refine Finset.sum_congr rfl fun u _ => by simp
        _ = ∑ _u : Q ⧸ H, Fintype.card H := by
            refine Finset.sum_congr rfl fun u _ => card_fiber_smul H u u
        _ = Fintype.card (Q ⧸ H) * Fintype.card H := by simp
        _ = Fintype.card Q := by rw [hX_card, hH_mul]
    have hBad2 : 3 * Bad2.card ≤ Fintype.card Q := by
      calc
        3 * Bad2.card = ∑ _x ∈ Bad2, 3 := by simp [mul_comm]
        _ ≤ ∑ x ∈ Bad2, (Fix x).card := Finset.sum_le_sum fun x hx => (Finset.mem_filter.1 hx).2
        _ ≤ ∑ x : Q, (Fix x).card := Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
        _ = Fintype.card Q := hsum_fix
    have huniv_sub : (Finset.univ : Finset Q) ⊆ Q0 ∪ (Bad1 ∪ Bad2) := by
      intro x _
      simp only [Finset.mem_union, Q0, Bad1, Bad2, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h1 : x • s0 = s0
      · simp [h1]
      · by_cases h2 : 3 ≤ (Fix x).card
        · simp [h2]
        · left; exact ⟨h1, by omega⟩
    have hcard_univ := Finset.card_le_card huniv_sub
    have hunion : (Q0 ∪ (Bad1 ∪ Bad2)).card ≤ Q0.card + Bad1.card + Bad2.card :=
      (Finset.card_union_le _ _).trans (by
        have := Finset.card_union_le Bad1 Bad2
        omega)
    rw [Finset.card_univ] at hcard_univ
    have hBad1_le : 3 * Bad1.card ≤ Fintype.card Q := by
      rw [hBad1, ← hH_mul]
      exact Nat.mul_le_mul_right _ hm3
    omega
  let T (f : (Q ⧸ H) → Fin q) : Finset Q :=
    Finset.univ.filter fun x : Q => f (x • s0) = 0 ∧ ∀ u : Q ⧸ H, ¬ (f u = 0 ∧ f (x • u) = 0)
  have hT_pf : ∀ f : (Q ⧸ H) → Fin q, IsProductFree (T f : Set Q) := by
    intro f
    rw [isProductFree_iff]
    intro x hx y hy hxy
    simp only [Finset.mem_coe, T, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy hxy
    have hxy' : f (x • (y • s0)) = 0 := by simpa [mul_smul] using hxy.1
    exact hx.2 (y • s0) ⟨hy.1, hxy'⟩
  have hx_count : ∀ x ∈ Q0, 7 * q ^ (m - 1) ≤
      16 * (Finset.univ.filter fun f : (Q ⧸ H) → Fin q => x ∈ T f).card := by
    intro x hx
    have hx_prop : x • s0 ≠ s0 ∧ (Fix x).card ≤ 2 := (Finset.mem_filter.1 hx).2
    let Good : Finset ((Q ⧸ H) → Fin q) := Finset.univ.filter fun f => f (x • s0) = 0
    let Bad (u : Q ⧸ H) : Finset ((Q ⧸ H) → Fin q) :=
      Finset.univ.filter fun f => f (x • s0) = 0 ∧ f u = 0 ∧ f (x • u) = 0
    have hGood_card : Good.card = q ^ (m - 1) := by
      have hsub : Good = Finset.univ.filter fun f : (Q ⧸ H) → Fin q => ∀ y ∈ ({x • s0} : Finset (Q ⧸ H)), f y = 0 := by
        ext f; simp [Good]
      rw [hsub, card_fun_zero, hX_card, Finset.card_singleton]
    have hsub_good : Good \ (Finset.univ.biUnion Bad) ⊆
        Finset.univ.filter fun f : (Q ⧸ H) → Fin q => x ∈ T f := by
      intro f hf
      simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_filter, Good, Bad, T] at hf ⊢
      push Not at hf
      exact ⟨hf.1, fun u ⟨h1, h2⟩ => hf.2 u hf.1 h1 h2⟩
    have hcard_diff : Good.card - (Finset.univ.biUnion Bad).card ≤
        (Finset.univ.filter fun f : (Q ⧸ H) → Fin q => x ∈ T f).card := by
      have hsub2 : Good ⊆ (Good \ (Finset.univ.biUnion Bad)) ∪ (Finset.univ.biUnion Bad) :=
        fun f hf => by by_cases h : f ∈ Finset.univ.biUnion Bad <;> simp [hf, h]
      have hc1 : Good.card ≤ (Good \ (Finset.univ.biUnion Bad)).card +
          (Finset.univ.biUnion Bad).card :=
        (Finset.card_le_card hsub2).trans (Finset.card_union_le _ _)
      have hc2 := Finset.card_le_card hsub_good
      omega
    have hBad_sum : (Finset.univ.biUnion Bad).card ≤ ∑ u : Q ⧸ H, (Bad u).card :=
      Finset.card_biUnion_le
    have hBad_card : ∀ u : Q ⧸ H, (Bad u).card =
        q ^ (m - ({x • s0, u, x • u} : Finset (Q ⧸ H)).card) := by
      intro u
      have hsub : Bad u = Finset.univ.filter fun f : (Q ⧸ H) → Fin q =>
          ∀ y ∈ ({x • s0, u, x • u} : Finset (Q ⧸ H)), f y = 0 := by
        ext f; simp [Bad]
      rw [hsub, card_fun_zero, hX_card]
    have hfix_ne : ∀ u ∈ Fix x, u ≠ x • s0 := by
      intro u hu heq
      have hfix : x • u = u := (Finset.mem_filter.1 hu).2
      rw [heq] at hfix
      have hinj : x • s0 = s0 := smul_left_cancel x hfix
      exact hx_prop.1 hinj
    have hBad_bound : ∑ u : Q ⧸ H, (Bad u).card ≤ 4 * q ^ (m - 2) + m * q ^ (m - 3) := by
      let S2 : Finset (Q ⧸ H) := Fix x ∪ {x • s0, s0}
      have hS2_card : S2.card ≤ 4 := by
        dsimp only [S2]
        have := Finset.card_union_le (Fix x) ({x • s0, s0} : Finset (Q ⧸ H))
        have h2 : ({x • s0, s0} : Finset (Q ⧸ H)).card ≤ 2 := Finset.card_le_two
        omega
      have hS2_bd : ∀ u ∈ S2, (Bad u).card ≤ q ^ (m - 2) := by
        intro u hu
        rw [hBad_card u]
        refine Nat.pow_le_pow_right hq_pos (Nat.sub_le_sub_left ?_ m)
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, S2] at hu
        rcases hu with hu_fix | rfl | rfl
        · have hne := hfix_ne u hu_fix
          have h2 : ({x • s0, u} : Finset (Q ⧸ H)).card = 2 := by simp [hne.symm]
          rw [← h2]
          refine Finset.card_le_card fun z hz => ?_
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
          tauto
        · have hx_ne_xx : x • (x • s0) ≠ x • s0 := fun h => hx_prop.1 (smul_left_cancel x h)
          have h2 : ({x • s0, x • (x • s0)} : Finset (Q ⧸ H)).card = 2 := by simp [hx_ne_xx.symm]
          rw [← h2]
          refine Finset.card_le_card fun z hz => ?_
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
          tauto
        · have h2 : ({x • s0, s0} : Finset (Q ⧸ H)).card = 2 := by simp [hx_prop.1]
          rw [← h2]
          refine Finset.card_le_card fun z hz => ?_
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
          tauto
      have hcompl_bd : ∀ u ∉ S2, (Bad u).card ≤ q ^ (m - 3) := by
        intro u hu
        rw [hBad_card u]
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, S2, Fix,
          Finset.mem_filter, Finset.mem_univ, true_and] at hu
        push Not at hu
        have h1 : x • s0 ≠ u := Ne.symm hu.2.1
        have h2 : x • s0 ≠ x • u := fun h => hu.2.2 (smul_left_cancel x h.symm)
        have h3 : u ≠ x • u := Ne.symm hu.1
        have hcard3 : ({x • s0, u, x • u} : Finset (Q ⧸ H)).card = 3 := by
          simp [h1, h2, h3]
        rw [hcard3]
      calc
        ∑ u : Q ⧸ H, (Bad u).card
            = (∑ u ∈ S2, (Bad u).card) + ∑ u ∈ Finset.univ \ S2, (Bad u).card := by
              rw [← Finset.sum_sdiff (Finset.subset_univ S2), add_comm]
        _ ≤ (∑ _u ∈ S2, q ^ (m - 2)) + ∑ _u ∈ Finset.univ \ S2, q ^ (m - 3) := by
              gcongr
              · exact hS2_bd _ ‹_›
              · exact hcompl_bd _ (Finset.mem_sdiff.1 ‹_›).2
        _ = S2.card * q ^ (m - 2) + (Finset.univ \ S2).card * q ^ (m - 3) := by simp
        _ ≤ 4 * q ^ (m - 2) + m * q ^ (m - 3) := by
            have hle_m : (Finset.univ \ S2).card ≤ m := by
              calc
                (Finset.univ \ S2).card ≤ (Finset.univ : Finset (Q ⧸ H)).card :=
                  Finset.card_le_card Finset.sdiff_subset
                _ = m := by rw [Finset.card_univ, hX_card]
            gcongr
    have hpow1 : q ^ (m - 1) = q ^ 2 * q ^ (m - 3) := by
      rw [← pow_add]; congr 1; omega
    have hpow2 : q ^ (m - 2) = q * q ^ (m - 3) := by
      conv_lhs => rw [show m - 2 = 1 + (m - 3) by omega, pow_add, pow_one]
    have hpoly : 7 * q ^ 2 + 16 * (4 * q + m) ≤ 16 * q ^ 2 := by
      have hq8' : 0 ≤ q - 8 := by omega
      nlinarith [hq8, h16m_lt]
    have hscale : 7 * q ^ (m - 1) + 16 * (Finset.univ.biUnion Bad).card ≤ 16 * Good.card := by
      calc
        7 * q ^ (m - 1) + 16 * (Finset.univ.biUnion Bad).card
            ≤ 7 * q ^ (m - 1) + 16 * (4 * q ^ (m - 2) + m * q ^ (m - 3)) := by
              gcongr; exact hBad_sum.trans hBad_bound
        _ = (7 * q ^ 2 + 16 * (4 * q + m)) * q ^ (m - 3) := by rw [hpow1, hpow2]; ring
        _ ≤ (16 * q ^ 2) * q ^ (m - 3) := Nat.mul_le_mul_right _ hpoly
        _ = 16 * Good.card := by rw [hGood_card, hpow1]; ring
    omega
  have hsum_all : 7 * (Fintype.card Q) * q ^ m ≤ 48 * q * ∑ f : (Q ⧸ H) → Fin q, (T f).card := by
    have hswap : ∑ f : (Q ⧸ H) → Fin q, (T f).card =
        ∑ x : Q, (Finset.univ.filter fun f : (Q ⧸ H) → Fin q => x ∈ T f).card := by
      have h1 : ∀ f : (Q ⧸ H) → Fin q, (T f).card =
          ∑ x : Q, if x ∈ T f then 1 else 0 := fun f => by simp
      simp_rw [h1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => by simp
    calc
      7 * Fintype.card Q * q ^ m
          ≤ 7 * (3 * Q0.card) * q ^ m := by gcongr
      _ = 3 * q * (Q0.card * (7 * q ^ (m - 1))) := by
          have : q ^ m = q * q ^ (m - 1) := by
            conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ m), pow_succ']
          rw [this]; ring
      _ ≤ 3 * q * ∑ x ∈ Q0, (16 * (Finset.univ.filter fun f : (Q ⧸ H) → Fin q => x ∈ T f).card) := by
          gcongr
          calc
            Q0.card * (7 * q ^ (m - 1)) = ∑ _x ∈ Q0, 7 * q ^ (m - 1) := by simp
            _ ≤ ∑ x ∈ Q0, 16 * (Finset.univ.filter fun f : (Q ⧸ H) → Fin q => x ∈ T f).card :=
                Finset.sum_le_sum fun x hx => hx_count x hx
      _ = 48 * q * ∑ x ∈ Q0, (Finset.univ.filter fun f : (Q ⧸ H) → Fin q => x ∈ T f).card := by
          rw [← Finset.mul_sum]; ring
      _ ≤ 48 * q * ∑ x : Q, (Finset.univ.filter fun f : (Q ⧸ H) → Fin q => x ∈ T f).card :=
          Nat.mul_le_mul_left _ (Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _)
      _ = 48 * q * ∑ f : (Q ⧸ H) → Fin q, (T f).card := by rw [hswap]
  have hex_f : ∃ f : (Q ⧸ H) → Fin q, 7 * Fintype.card Q ≤ 48 * q * (T f).card := by
    by_contra hlt
    push Not at hlt
    have hsum_lt : 48 * q * ∑ f : (Q ⧸ H) → Fin q, (T f).card <
        ∑ _f : (Q ⧸ H) → Fin q, 7 * Fintype.card Q := by
      rw [Finset.mul_sum]
      exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun f _ => hlt f
    have hcard_fn : (Finset.univ : Finset ((Q ⧸ H) → Fin q)).card = q ^ m := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hX_card]
    simp only [Finset.sum_const, hcard_fn, smul_eq_mul] at hsum_lt
    rw [mul_comm (q ^ m)] at hsum_lt
    omega
  obtain ⟨f, hf⟩ := hex_f
  refine ⟨T f, hT_pf f, ?_⟩
  have hfR : (7 : ℝ) * (Fintype.card Q : ℝ) ≤ 48 * (q : ℝ) * ((T f).card : ℝ) := by
    exact_mod_cast hf
  have hqR : (q : ℝ) ≤ 8 * (m : ℝ) ^ ((1 : ℝ) / 2) := by
    have hsq_le : ((q : ℝ)) ^ 2 ≤ (8 * (m : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 := by
      rw [mul_pow, ← Real.rpow_natCast ((m : ℝ) ^ _), ← Real.rpow_mul (Nat.cast_nonneg m)]
      norm_num
      exact_mod_cast hq2_le
    nlinarith [Real.rpow_nonneg (Nat.cast_nonneg m) ((1 : ℝ) / 2)]
  have hm_posR : (0 : ℝ) < (m : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < m)) _
  have hqR_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
  calc
    ((7 : ℝ) / 384) * (Fintype.card Q : ℝ) / (m : ℝ) ^ ((1 : ℝ) / 2)
        = (7 * (Fintype.card Q : ℝ)) / (48 * (8 * (m : ℝ) ^ ((1 : ℝ) / 2))) := by ring
    _ ≤ (7 * (Fintype.card Q : ℝ)) / (48 * (q : ℝ)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        linarith
    _ ≤ ((T f).card : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        linarith
