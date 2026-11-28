import OMAReductions.R_Erdos107_erdos_107_R1_H1_R1_H2_R1

/-! # Geometric normalization and four-point parity transfer (Erdos 107)

We prove `OMA.R_Erdos107_erdos_107_R1_H1_R1_H2_R1.H1`: given an orientation
triple sign `o : Fin 17 → Fin 17 → Fin 17 → Bool` realized by integer
coordinates `(x, y)` with `StrictMono x` and nonzero orientation determinants,
there exist `g` and `π : Equiv.Perm (Fin 17)` such that:
1. `π 0 = 0` and the remaining 16 points are sorted by strictly increasing slope
   `(y i - y 0) / (x i - x 0)` from vertex `0`, making `g 0 b c = true` for all
   `0 < b < c`.
2. Applying the projective coordinate change `X i = (y (π i) - y 0) / (x (π i) - x 0)`,
   `Y i = 1 / (x (π i) - x 0)` for `i > 0` preserves orientation signs and satisfies
   `X a < X b < X c < X d`, so `E107Signs.signotope` yields `packet g`.
3. The four-point XOR parity of an alternating orientation function is invariant
   under adjacent transpositions, hence under sorting any 4-tuple, transferring
   `allEven g S` to `allEven o (S.map π.toEmbedding)`.
-/

namespace Erdos107H1

open Finset

private lemma xor4_swap12 (a b c d : Bool) :
    (((!a).xor (!b)).xor d).xor c = (((a.xor b).xor c).xor d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private lemma xor4_swap23 (a b c d : Bool) :
    (((!a).xor c).xor b).xor (!d) = (((a.xor b).xor c).xor d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private lemma xor4_swap34 (a b c d : Bool) :
    ((b.xor a).xor (!c)).xor (!d) = (((a.xor b).xor c).xor d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private lemma packet_of_signotope {A B C D : Prop} [Decidable A] [Decidable B]
    [Decidable C] [Decidable D]
    (h : ((A ↔ C) → (A ↔ B)) ∧ ((A ↔ D) → (A ↔ B)) ∧ ((A ↔ D) → (A ↔ C)) ∧ ((B ↔ D) → (B ↔ C))) :
    (decide A = decide B ∧ decide B = decide C) ∨
    (decide A = decide B ∧ decide C = decide D) ∨
    (decide B = decide C ∧ decide C = decide D) := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> by_cases hD : D <;> simp_all

/-- Sorting a 4-tuple of distinct elements using only adjacent swaps. -/
private lemma prop_of_sorted4 {α : Type*} [LinearOrder α] (S : Finset α)
    (P : α → α → α → α → Prop)
    (h12 : ∀ u v w z, u ≠ v → u ≠ w → u ≠ z → v ≠ w → v ≠ z → w ≠ z → (P v u w z ↔ P u v w z))
    (h23 : ∀ u v w z, u ≠ v → u ≠ w → u ≠ z → v ≠ w → v ≠ z → w ≠ z → (P u w v z ↔ P u v w z))
    (h34 : ∀ u v w z, u ≠ v → u ≠ w → u ≠ z → v ≠ w → v ≠ z → w ≠ z → (P u v z w ↔ P u v w z))
    (hs : ∀ u ∈ S, ∀ v ∈ S, ∀ w ∈ S, ∀ z ∈ S, u < v → v < w → w < z → P u v w z) :
    ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → P a b c d := by
  -- Helper 1: assume a < b < c, place d
  have hplace_d : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
      a < b → b < c → a ≠ d → b ≠ d → c ≠ d → P a b c d := by
    intro a ha b hb c hc d hd hab hbc had hbd hcd
    rcases lt_or_gt_of_ne hcd with hcd' | hdc
    · exact hs a ha b hb c hc d hd hab hbc hcd'
    · rw [← h34 a b c d hab.ne (hab.trans hbc).ne had hbc.ne hbd hcd]
      rcases lt_or_gt_of_ne hbd with hbd' | hdb
      · exact hs a ha b hb d hd c hc hab hbd' hdc
      · rw [← h23 a b d c hab.ne had (hab.trans hbc).ne hbd hbc.ne hcd.symm]
        rcases lt_or_gt_of_ne had with had' | hda
        · exact hs a ha d hd b hb c hc had' hdb hbc
        · rw [← h12 a d b c had hab.ne (hab.trans hbc).ne hbd.symm hcd.symm hbc.ne]
          exact hs d hd a ha b hb c hc hda hab hbc
  -- Helper 2: assume a < b, sort (a, b, c) and place d
  have hplace_c : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
      a < b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → P a b c d := by
    intro a ha b hb c hc d hd hab hac had hbc hbd hcd
    rcases lt_or_gt_of_ne hbc with hbc' | hcb
    · exact hplace_d a ha b hb c hc d hd hab hbc' had hbd hcd
    · rw [← h23 a b c d hab.ne hac had hbc hbd hcd]
      rcases lt_or_gt_of_ne hac with hac' | hca
      · exact hplace_d a ha c hc b hb d hd hac' hcb had hcd hbd
      · rw [← h12 a c b d hac hab.ne had hbc.symm hcd hbd]
        exact hplace_d c hc a ha b hb d hd hca hab hcd had hbd
  -- Full case: order (a, b) first
  intro a ha b hb c hc d hd hab hac had hbc hbd hcd
  rcases lt_or_gt_of_ne hab with hab' | hba
  · exact hplace_c a ha b hb c hc d hd hab' hac had hbc hbd hcd
  · rw [← h12 a b c d hab hac had hbc hbd hcd]
    exact hplace_c b hb a ha c hc d hd hba hbc hbd hac had hcd

theorem main_H1 : OMA.R_Erdos107_erdos_107_R1_H1_R1_H2_R1.H1 := by
  intro o hreal
  obtain ⟨x, y, hmono, hdet⟩ := hreal
  let D : Fin 17 → Fin 17 → Fin 17 → ℤ := fun a b c =>
    (x b - x a) * (y c - y a) - (y b - y a) * (x c - x a)
  let ori : Fin 17 → Fin 17 → Fin 17 → Bool := fun a b c => decide (0 < D a b c)
  have hD_swap12 : ∀ a b c, D b a c = -D a b c := fun a b c => by dsimp [D]; ring
  have hD_swap23 : ∀ a b c, D a c b = -D a b c := fun a b c => by dsimp [D]; ring
  have hD_ne : ∀ a b c : Fin 17, a ≠ b → a ≠ c → b ≠ c → D a b c ≠ 0 := by
    intro a b c hab hac hbc
    rcases lt_or_gt_of_ne hab with hab' | hba
    · rcases lt_or_gt_of_ne hbc with hbc' | hcb
      · exact (hdet a b c hab' hbc').1
      · rcases lt_or_gt_of_ne hac with hac' | hca
        · rw [hD_swap23]
          exact neg_ne_zero.mpr (hdet a c b hac' hcb).1
        · rw [hD_swap23, hD_swap12, neg_neg]
          exact (hdet c a b hca hab').1
    · rcases lt_or_gt_of_ne hac with hac' | hca
      · rw [hD_swap12]
        exact neg_ne_zero.mpr (hdet b a c hba hac').1
      · rcases lt_or_gt_of_ne hbc with hbc' | hcb
        · rw [hD_swap12, hD_swap23, neg_neg]
          exact (hdet b c a hbc' hca).1
        · rw [hD_swap12, hD_swap23, neg_neg, hD_swap12]
          exact neg_ne_zero.mpr (hdet c b a hcb hba).1
  have hori_swap12 : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → ori b a c = !(ori a b c) := by
    intro a b c hab hac hbc
    have hne := hD_ne a b c hab hac hbc
    dsimp [ori]
    rw [hD_swap12]
    by_cases hpos : 0 < D a b c
    · simp [hpos]
      omega
    · simp [hpos]
      omega
  have hori_swap23 : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → ori a c b = !(ori a b c) := by
    intro a b c hab hac hbc
    have hne := hD_ne a b c hab hac hbc
    dsimp [ori]
    rw [hD_swap23]
    by_cases hpos : 0 < D a b c
    · simp [hpos]
      omega
    · simp [hpos]
      omega
  have hori_eq_o : ∀ a b c, a < b → b < c → o a b c = ori a b c := fun a b c hab hbc =>
    (hdet a b c hab hbc).2
  -- Step 1: Sort {1, ..., 16} by slope from vertex 0
  let S₀ : Finset (Fin 17) := (Finset.univ : Finset (Fin 17)).erase 0
  have hS₀_card : S₀.card = 16 := by decide
  let slope : Fin 17 → ℚ := fun i => ((y i - y 0 : ℤ) : ℚ) / ((x i - x 0 : ℤ) : ℚ)
  have hdx_pos : ∀ i : Fin 17, i ≠ 0 → (0 : ℚ) < ((x i - x 0 : ℤ) : ℚ) := by
    intro i hi
    have h0i : (0 : Fin 17) < i := Fin.pos_of_ne_zero hi
    have hlt : x 0 < x i := hmono h0i
    exact_mod_cast sub_pos.mpr hlt
  have hslope_inj : Set.InjOn slope (S₀ : Set (Fin 17)) := by
    intro i hi j hj heq
    have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
    have hj0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
    by_contra hij
    have hdxi := hdx_pos i hi0
    have hdxj := hdx_pos j hj0
    dsimp [slope] at heq
    rw [div_eq_div_iff hdxi.ne' hdxj.ne'] at heq
    have hD0 : (D 0 i j : ℚ) = 0 := by
      dsimp [D]
      push_cast at heq ⊢
      linarith
    exact hD_ne 0 i j hi0.symm hj0.symm hij (by exact_mod_cast hD0)
  let K : Finset ℚ := S₀.image slope
  have hK_card : K.card = 16 := by
    rw [Finset.card_image_of_injOn hslope_inj, hS₀_card]
  let eK : Fin 16 ≃o K := K.orderIsoOfFin hK_card
  have hpre : ∀ k : Fin 16, ∃ i ∈ S₀, slope i = (eK k).1 := fun k =>
    Finset.mem_image.mp (eK k).2
  choose p hp_mem hp_slope using hpre
  have hp_ne0 : ∀ k : Fin 16, p k ≠ 0 := fun k => (Finset.mem_erase.mp (hp_mem k)).1
  have hp_mono : StrictMono (fun k : Fin 16 => slope (p k)) := by
    intro k₁ k₂ hlt
    dsimp only
    rw [hp_slope k₁, hp_slope k₂]
    exact eK.strictMono hlt
  have hp_inj : Function.Injective p := fun k₁ k₂ h =>
    hp_mono.injective (congrArg slope h)
  let π_fun : Fin 17 → Fin 17 := fun i =>
    if h : i.val = 0 then 0 else p ⟨i.val - 1, by have := i.isLt; omega⟩
  have hπ_inj : Function.Injective π_fun := by
    intro i j hij
    dsimp [π_fun] at hij
    split_ifs at hij with hi hj hj
    · exact Fin.ext (by omega)
    · exact absurd hij.symm (hp_ne0 _)
    · exact absurd hij (hp_ne0 _)
    · have hsub := hp_inj hij
      have hval := congrArg Fin.val hsub
      dsimp only at hval
      exact Fin.ext (by omega)
  let π : Equiv.Perm (Fin 17) := Equiv.ofBijective π_fun (Finite.injective_iff_bijective.mp hπ_inj)
  have hπ0 : π 0 = 0 := by
    change π_fun 0 = 0
    simp [π_fun]
  have hπ_ne0 : ∀ i : Fin 17, 0 < i → π i ≠ 0 := by
    intro i hi
    have hi0 : i.val ≠ 0 := Fin.pos_iff_ne_zero.mp hi |> fun h => fun hv => h (Fin.ext hv)
    change π_fun i ≠ 0
    dsimp [π_fun]
    rw [if_neg hi0]
    exact hp_ne0 _
  have hπ_slope : ∀ i j : Fin 17, 0 < i → i < j → slope (π i) < slope (π j) := by
    intro i j hi hij
    have hi0 : i.val ≠ 0 := fun hv => (Fin.pos_iff_ne_zero.mp hi) (Fin.ext hv)
    have hj0 : j.val ≠ 0 := fun hv => (Fin.pos_iff_ne_zero.mp (hi.trans hij)) (Fin.ext hv)
    change slope (π_fun i) < slope (π_fun j)
    simp only [π_fun, hi0, hj0, ↓reduceDIte]
    exact hp_mono (Fin.mk_lt_mk.mpr (by have : i.val < j.val := hij; omega))
  let g : Fin 17 → Fin 17 → Fin 17 → Bool := fun a b c => ori (π a) (π b) (π c)
  refine ⟨g, π, ?_, ?_, ?_⟩
  -- Step 2: packet g
  · intro a b c d hab hbc hcd
    by_cases ha0 : a = 0
    · subst ha0
      have hapex : ∀ u v : Fin 17, 0 < u → u < v → g 0 u v = true := by
        intro u v hu huv
        have hlt := hπ_slope u v hu huv
        have hdu := hdx_pos (π u) (hπ_ne0 u hu)
        have hdv := hdx_pos (π v) (hπ_ne0 v (hu.trans huv))
        dsimp [slope] at hlt
        rw [div_lt_div_iff₀ hdu hdv] at hlt
        have hDpos : (0 : ℚ) < (D 0 (π u) (π v) : ℚ) := by
          dsimp [D]
          push_cast at hlt ⊢
          linarith
        have hDposZ : 0 < D 0 (π u) (π v) := by exact_mod_cast hDpos
        change decide (0 < D (π 0) (π u) (π v)) = true
        rw [hπ0]
        simp [hDposZ]
      left
      rw [hapex b c hab hbc, hapex b d hab (hbc.trans hcd), hapex c d (hab.trans hbc) hcd]
      exact ⟨rfl, rfl⟩
    · have ha_pos : 0 < a := Fin.pos_of_ne_zero ha0
      have hb_pos : 0 < b := ha_pos.trans hab
      have hc_pos : 0 < c := hb_pos.trans hbc
      have hd_pos : 0 < d := hc_pos.trans hcd
      let X : Fin 17 → ℝ := fun i =>
        ((y (π i) - y 0 : ℤ) : ℝ) / ((x (π i) - x 0 : ℤ) : ℝ)
      let Y : Fin 17 → ℝ := fun i => 1 / ((x (π i) - x 0 : ℤ) : ℝ)
      let DXY : Fin 17 → Fin 17 → Fin 17 → ℝ := fun u v w =>
        (X v - X u) * (Y w - Y u) - (Y v - Y u) * (X w - X u)
      have hX_lt : ∀ u v : Fin 17, 0 < u → u < v → X u < X v := by
        intro u v hu huv
        have hlt := hπ_slope u v hu huv
        have hltR : (slope (π u) : ℝ) < (slope (π v) : ℝ) := by exact_mod_cast hlt
        simpa [X, slope] using hltR
      have hDXY_iff : ∀ u v w : Fin 17, 0 < u → 0 < v → 0 < w →
          (0 < DXY u v w ↔ 0 < D (π u) (π v) (π w)) := by
        intro u v w hu hv hw
        have hdu : (0 : ℝ) < ((x (π u) - x 0 : ℤ) : ℝ) := by exact_mod_cast hdx_pos (π u) (hπ_ne0 u hu)
        have hdv : (0 : ℝ) < ((x (π v) - x 0 : ℤ) : ℝ) := by exact_mod_cast hdx_pos (π v) (hπ_ne0 v hv)
        have hdw : (0 : ℝ) < ((x (π w) - x 0 : ℤ) : ℝ) := by exact_mod_cast hdx_pos (π w) (hπ_ne0 w hw)
        have hprod_pos : (0 : ℝ) <
            ((x (π u) - x 0 : ℤ) : ℝ) * ((x (π v) - x 0 : ℤ) : ℝ) * ((x (π w) - x 0 : ℤ) : ℝ) :=
          by positivity
        have hid : DXY u v w =
            (D (π u) (π v) (π w) : ℝ) /
              (((x (π u) - x 0 : ℤ) : ℝ) * ((x (π v) - x 0 : ℤ) : ℝ) * ((x (π w) - x 0 : ℤ) : ℝ)) := by
          dsimp [DXY, X, Y, D]
          field_simp [hdu.ne', hdv.ne', hdw.ne']
          push_cast
          ring
        rw [hid, div_pos_iff_of_pos_right hprod_pos]
        exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩
      have hsig := E107Signs.signotope X Y DXY (fun _ _ _ => rfl) a b c d
        (hX_lt a b ha_pos hab) (hX_lt b c hb_pos hbc) (hX_lt c d hc_pos hcd)
      dsimp only at hsig
      rw [hDXY_iff a b c ha_pos hb_pos hc_pos, hDXY_iff a b d ha_pos hb_pos hd_pos,
        hDXY_iff a c d ha_pos hc_pos hd_pos, hDXY_iff b c d hb_pos hc_pos hd_pos] at hsig
      exact packet_of_signotope hsig
  -- Step 3: Apex positivity
  · intro b c hb hbc
    have hlt := hπ_slope b c hb hbc
    have hdb := hdx_pos (π b) (hπ_ne0 b hb)
    have hdc := hdx_pos (π c) (hπ_ne0 c (hb.trans hbc))
    dsimp [slope] at hlt
    rw [div_lt_div_iff₀ hdb hdc] at hlt
    have hDpos : (0 : ℚ) < (D 0 (π b) (π c) : ℚ) := by
      dsimp [D]
      push_cast at hlt ⊢
      linarith
    have hDposZ : 0 < D 0 (π b) (π c) := by exact_mod_cast hDpos
    change decide (0 < D (π 0) (π b) (π c)) = true
    rw [hπ0]
    simp [hDposZ]
  -- Step 4: Transfer allEven g S → allEven o (S.map π.toEmbedding)
  · intro S hS a ha b hb c hc d hd hab hbc hcd
    obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
    obtain ⟨c', hc', rfl⟩ := Finset.mem_map.mp hc
    obtain ⟨d', hd', rfl⟩ := Finset.mem_map.mp hd
    change π a' < π b' at hab
    change π b' < π c' at hbc
    change π c' < π d' at hcd
    change (((o (π a') (π b') (π c')).xor (o (π a') (π b') (π d'))).xor
      (o (π a') (π c') (π d'))).xor (o (π b') (π c') (π d')) = false
    rw [hori_eq_o _ _ _ hab hbc, hori_eq_o _ _ _ hab (hbc.trans hcd),
      hori_eq_o _ _ _ (hab.trans hbc) hcd, hori_eq_o _ _ _ hbc hcd]
    let P : Fin 17 → Fin 17 → Fin 17 → Fin 17 → Prop := fun u v w z =>
      (((ori (π u) (π v) (π w)).xor (ori (π u) (π v) (π z))).xor
        (ori (π u) (π w) (π z))).xor (ori (π v) (π w) (π z)) = false
    have hP12 : ∀ u v w z, u ≠ v → u ≠ w → u ≠ z → v ≠ w → v ≠ z → w ≠ z →
        (P v u w z ↔ P u v w z) := by
      intro u v w z huv huw huz hvw hvz hwz
      dsimp only [P]
      rw [hori_swap12 (π u) (π v) (π w) (π.injective.ne huv) (π.injective.ne huw) (π.injective.ne hvw),
        hori_swap12 (π u) (π v) (π z) (π.injective.ne huv) (π.injective.ne huz) (π.injective.ne hvz),
        xor4_swap12]
    have hP23 : ∀ u v w z, u ≠ v → u ≠ w → u ≠ z → v ≠ w → v ≠ z → w ≠ z →
        (P u w v z ↔ P u v w z) := by
      intro u v w z huv huw huz hvw hvz hwz
      dsimp only [P]
      rw [hori_swap23 (π u) (π v) (π w) (π.injective.ne huv) (π.injective.ne huw) (π.injective.ne hvw),
        hori_swap12 (π v) (π w) (π z) (π.injective.ne hvw) (π.injective.ne hvz) (π.injective.ne hwz),
        xor4_swap23]
    have hP34 : ∀ u v w z, u ≠ v → u ≠ w → u ≠ z → v ≠ w → v ≠ z → w ≠ z →
        (P u v z w ↔ P u v w z) := by
      intro u v w z huv huw huz hvw hvz hwz
      dsimp only [P]
      rw [hori_swap23 (π u) (π w) (π z) (π.injective.ne huw) (π.injective.ne huz) (π.injective.ne hwz),
        hori_swap23 (π v) (π w) (π z) (π.injective.ne hvw) (π.injective.ne hvz) (π.injective.ne hwz),
        xor4_swap34]
    exact prop_of_sorted4 S P hP12 hP23 hP34 hS a' ha' b' hb' c' hc' d' hd'
      (fun h => hab.ne (congrArg π h))
      (fun h => (hab.trans hbc).ne (congrArg π h))
      (fun h => ((hab.trans hbc).trans hcd).ne (congrArg π h))
      (fun h => hbc.ne (congrArg π h))
      (fun h => (hbc.trans hcd).ne (congrArg π h))
      (fun h => hcd.ne (congrArg π h))

end Erdos107H1

theorem OMA.solution : OMA.R_Erdos107_erdos_107_R1_H1_R1_H2_R1.H1 := by
  exact Erdos107H1.main_H1
