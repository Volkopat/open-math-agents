import OMAReductions.R_ManickamMiklosSinghiConjecture_manickam_miklos_singhi_conjecture_variants_pokrovskiy_R1_H2_R1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Cyclic restricted sumset bound (Pokrovskiy Claim 5.10)

We prove `H1` of the Pokrovskiy reduction for the Manickam-Miklos-Singhi
conjecture: if `A, B ⊆ Fin k` each cover every antipodal pair `{u, -u}` and
`S ⊆ A ×ˢ B` omits at most `k^2 / 10000` pairs, then the restricted sumset
`U = {a + b | (a, b) ∈ S}` has cardinality at least `3k / 5`.

Assuming `5 * |U| < 3 * k`, we apply Markov to the representation count `r(x)`
over `Uᶜ`, obtaining a dense set `X ⊆ Uᶜ` (`|X| > 19k / 50`) on which `x - B`
is close to `Aᶜ` in symmetric difference. Thus the difference set `T₀ = X - X`
and its sumset `H = T₀ + T₀` consist of small-shift approximate periods of `B`.
Double-counting total translate distance forces `2 * |H| ≤ k`, so
`2 * |T₀ + T₀| < 3 * |T₀|`, which by the 3/2 Freiman lemma forces `H` to be an
additive subgroup of `Fin k`. Lagrange's theorem forces `H` to have index 2,
and summing the translate distance over `H` contradicts the antipodal overlap
bound on `B`.
-/

namespace MMSPokrovskiyH1

open Finset

private lemma card_symmDiff_eq_sdiff_add {α : Type*} [DecidableEq α] (s t : Finset α) :
    (symmDiff s t).card = (s \ t).card + (t \ s).card := by
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint]
  exact Finset.disjoint_left.mpr fun x hx hy => (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1

private lemma card_symmDiff_triangle {α : Type*} [DecidableEq α] (s t u : Finset α) :
    (symmDiff s u).card ≤ (symmDiff s t).card + (symmDiff t u).card := by
  calc
    (symmDiff s u).card ≤ (symmDiff s t ∪ symmDiff t u).card := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_symmDiff, Finset.mem_union] at hx ⊢
      tauto
    _ ≤ (symmDiff s t).card + (symmDiff t u).card := Finset.card_union_le _ _

private lemma card_symmDiff_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s t : Finset α) {f : α → β} (hf : Function.Injective f) :
    (symmDiff (s.image f) (t.image f)).card = (symmDiff s t).card := by
  have h : symmDiff (s.image f) (t.image f) = (symmDiff s t).image f := by
    ext y
    simp only [Finset.mem_symmDiff, Finset.mem_image]
    constructor
    · rintro (⟨⟨x, hx, rfl⟩, hnt⟩ | ⟨⟨x, hx, rfl⟩, hns⟩)
      · exact ⟨x, Or.inl ⟨hx, fun hxt => hnt ⟨x, hxt, rfl⟩⟩, rfl⟩
      · exact ⟨x, Or.inr ⟨hx, fun hxs => hns ⟨x, hxs, rfl⟩⟩, rfl⟩
    · rintro ⟨x, (⟨hxs, hxt⟩ | ⟨hxt, hxs⟩), rfl⟩
      · left
        refine ⟨⟨x, hxs, rfl⟩, ?_⟩
        rintro ⟨x', hx', heq⟩
        exact hxt (hf heq ▸ hx')
      · right
        refine ⟨⟨x, hxt, rfl⟩, ?_⟩
        rintro ⟨x', hx', heq⟩
        exact hxs (hf heq ▸ hx')
  rw [h, Finset.card_image_of_injective _ hf]

private lemma card_symmDiff_eq_two_mul_sdiff {α : Type*} [DecidableEq α] {s t : Finset α}
    (hcard : s.card = t.card) :
    (symmDiff s t).card = 2 * (s \ t).card := by
  have h1 := Finset.card_sdiff_add_card_inter s t
  have h2 := Finset.card_sdiff_add_card_inter t s
  rw [Finset.inter_comm] at h2
  rw [card_symmDiff_eq_sdiff_add]
  omega

private lemma sum_translate_sdiff {k : ℕ} [NeZero k] (B F : Finset (Fin k)) :
    ∑ z ∈ F, (B \ B.image (· + z)).card =
      ∑ u ∈ B, (F.image (fun z => u - z) \ B).card := by
  have hstep : ∀ z : Fin k,
      (B \ B.image (· + z)).card = ∑ u ∈ B, if u - z ∉ B then 1 else 0 := by
    intro z
    rw [← Finset.card_filter]
    congr 1
    ext u
    simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨hu, hnot⟩
      refine ⟨hu, fun hsub => hnot ⟨u - z, hsub, sub_add_cancel u z⟩⟩
    · rintro ⟨hu, hsub⟩
      refine ⟨hu, ?_⟩
      rintro ⟨b, hb, rfl⟩
      exact hsub (by simpa using hb)
  simp_rw [hstep]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.card_filter]
  refine Finset.card_bij (fun z _ => u - z) ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_filter] at hz
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨z, hz.1, rfl⟩, hz.2⟩
  · intro z₁ _ z₂ _ h
    simpa using congrArg (fun w => u - w) h
  · intro w hw
    obtain ⟨hwimg, hwnot⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨z, hzF, rfl⟩ := Finset.mem_image.mp hwimg
    exact ⟨z, Finset.mem_filter.mpr ⟨hzF, hwnot⟩, rfl⟩

private lemma antipodal_card_eq {k : ℕ} [NeZero k] (B : Finset (Fin k))
    (hB : ∀ u, u ∈ B ∨ -u ∈ B) :
    2 * B.card = k + (B ∩ B.image (- ·)).card := by
  have hunion : B ∪ B.image (- ·) = Finset.univ := by
    ext u
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, iff_true]
    rcases hB u with hu | hnu
    · exact Or.inl hu
    · exact Or.inr ⟨-u, hnu, neg_neg u⟩
  have hneg : (B.image (- ·)).card = B.card :=
    Finset.card_image_of_injective B neg_injective
  have hci := Finset.card_union_add_card_inter B (B.image (- ·))
  rw [hunion, Finset.card_univ, Fintype.card_fin, hneg] at hci
  omega

private lemma main_bound (k : ℕ) [NeZero k] (A B : Finset (Fin k))
    (S : Finset (Fin k × Fin k))
    (hS : S ⊆ A ×ˢ B)
    (hA : ∀ u, u ∈ A ∨ -u ∈ A)
    (hB : ∀ u, u ∈ B ∨ -u ∈ B)
    (hE : 10000 * (A ×ˢ B \ S).card ≤ k ^ 2) :
    3 * k ≤ 5 * (S.image (fun p => p.1 + p.2)).card := by
  classical
  have hkpos : 0 < k := NeZero.pos k
  by_contra hlt
  have hlt : 5 * (S.image (fun p => p.1 + p.2)).card < 3 * k := Nat.lt_of_not_ge hlt
  set U := S.image (fun p => p.1 + p.2)
  set E := A ×ˢ B \ S
  have hAcard : k ≤ 2 * A.card := by
    have := antipodal_card_eq A hA
    omega
  have hBanti : 2 * B.card = k + (B ∩ B.image (- ·)).card := antipodal_card_eq B hB
  have hBcard : k ≤ 2 * B.card := by omega
  -- Step 1: Representation count r x
  let r : Fin k → ℕ := fun x => (A ∩ B.image (fun b => x - b)).card
  have hsum_r : ∑ x ∈ Uᶜ, r x ≤ E.card := by
    have hEcard : E.card = ∑ x : Fin k, (E.filter (fun p => p.1 + p.2 = x)).card := by
      have := Finset.card_eq_sum_card_fiberwise (f := fun p : Fin k × Fin k => p.1 + p.2)
        (s := E) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
      exact this
    calc
      ∑ x ∈ Uᶜ, r x ≤ ∑ x ∈ Uᶜ, (E.filter (fun p => p.1 + p.2 = x)).card := by
        apply Finset.sum_le_sum
        intro x hx
        have hxU : x ∉ U := Finset.mem_compl.mp hx
        refine Finset.card_le_card_of_injOn (fun a => (a, x - a)) ?_ ?_
        · intro a ha
          obtain ⟨haA, haB⟩ := Finset.mem_inter.mp ha
          obtain ⟨b, hbB, hba⟩ := Finset.mem_image.mp haB
          have hxb : x - a = b := by
            rw [← hba]
            abel
          have hmemAB : (a, x - a) ∈ A ×ˢ B := Finset.mem_product.mpr ⟨haA, hxb ▸ hbB⟩
          have hsumx : a + (x - a) = x := add_sub_cancel a x
          have hnotS : (a, x - a) ∉ S := fun hmemS =>
            hxU (Finset.mem_image.mpr ⟨(a, x - a), hmemS, hsumx⟩)
          exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hmemAB, hnotS⟩, hsumx⟩
        · intro a₁ _ a₂ _ h
          exact (Prod.mk.inj h).1
      _ ≤ ∑ x ∈ (Finset.univ : Finset (Fin k)), (E.filter (fun p => p.1 + p.2 = x)).card :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = E.card := hEcard.symm
  -- Step 2: Markov on X = Uᶜ.filter (200 * r x ≤ k)
  let X := Uᶜ.filter (fun x => 200 * r x ≤ k)
  have hbad : 50 * (Uᶜ \ X).card < k := by
    by_cases hne : (Uᶜ \ X).Nonempty
    · have hmarkov : (Uᶜ \ X).card * k < 200 * E.card := by
        calc
          (Uᶜ \ X).card * k = ∑ _x ∈ Uᶜ \ X, k := by simp
          _ < ∑ x ∈ Uᶜ \ X, 200 * r x := by
            apply Finset.sum_lt_sum_of_nonempty hne
            intro x hx
            have hxUc : x ∈ Uᶜ := (Finset.mem_sdiff.mp hx).1
            have hxnotX : x ∉ X := (Finset.mem_sdiff.mp hx).2
            have hgt : ¬ (200 * r x ≤ k) := fun hle =>
              hxnotX (Finset.mem_filter.mpr ⟨hxUc, hle⟩)
            omega
          _ = 200 * ∑ x ∈ Uᶜ \ X, r x := by rw [← Finset.mul_sum]
          _ ≤ 200 * ∑ x ∈ Uᶜ, r x :=
            Nat.mul_le_mul_left 200 (Finset.sum_le_sum_of_subset Finset.sdiff_subset)
          _ ≤ 200 * E.card := Nat.mul_le_mul_left 200 hsum_r
      have hmul : 50 * (Uᶜ \ X).card * k < k * k := by
        calc
          50 * (Uᶜ \ X).card * k = 50 * ((Uᶜ \ X).card * k) := by ring
          _ < 50 * (200 * E.card) := Nat.mul_lt_mul_of_pos_left hmarkov (by norm_num)
          _ = 10000 * E.card := by ring
          _ ≤ k ^ 2 := hE
          _ = k * k := by ring
      exact Nat.lt_of_mul_lt_mul_right hmul
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
      omega
  have hUc_card : Uᶜ.card + U.card = k := by
    have := Finset.card_compl_add_card U
    simpa [Fintype.card_fin] using this
  have hX_split : X.card + (Uᶜ \ X).card = Uᶜ.card := by
    have hsub : X ⊆ Uᶜ := Finset.filter_subset _ _
    have := Finset.card_sdiff_add_card_eq_card hsub
    omega
  have hX_large : 19 * k < 50 * X.card := by omega
  have hX_ne : X.Nonempty := Finset.card_pos.mp (by omega)
  -- Step 3: Upper bounds on A.card, B.card, and antipodal overlap of B
  obtain ⟨x₀, hx₀⟩ := hX_ne
  have hr₀ : 200 * r x₀ ≤ k := (Finset.mem_filter.mp hx₀).2
  have hAB_upper : A.card + B.card ≤ k + r x₀ := by
    let B₀ := B.image (fun b => x₀ - b)
    have hB₀card : B₀.card = B.card :=
      Finset.card_image_of_injective B (fun a b h => by simpa using congrArg (x₀ - ·) h)
    have hun := Finset.card_union_add_card_inter A B₀
    have hle : (A ∪ B₀).card ≤ k := by
      simpa [Fintype.card_fin] using Finset.card_le_univ (A ∪ B₀)
    have hr_eq : (A ∩ B₀).card = r x₀ := rfl
    omega
  have hB_upper : 200 * B.card ≤ 101 * k := by omega
  have hB_overlap : 100 * (B ∩ B.image (- ·)).card ≤ k := by omega
  -- Step 4: Symmetric difference distance d t
  let d : Fin k → ℕ := fun t => (symmDiff B (B.image (· + t))).card
  have hd_add : ∀ s t : Fin k, d (s + t) ≤ d s + d t := by
    intro s t
    have hcomp : B.image (· + (s + t)) = (B.image (· + t)).image (· + s) := by
      ext y
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨b + t, ⟨b, hb, rfl⟩, by abel⟩
      · rintro ⟨w, ⟨b, hb, rfl⟩, rfl⟩
        exact ⟨b, hb, by abel⟩
    calc
      d (s + t) = (symmDiff B (B.image (· + (s + t)))).card := rfl
      _ ≤ (symmDiff B (B.image (· + s))).card +
          (symmDiff (B.image (· + s)) (B.image (· + (s + t)))).card :=
        card_symmDiff_triangle _ _ _
      _ = d s + (symmDiff (B.image (· + s)) ((B.image (· + t)).image (· + s))).card := by
        rw [hcomp]
      _ = d s + d t := by
        rw [card_symmDiff_image B (B.image (· + t)) (add_left_injective s)]
  have hsymm_X : ∀ x ∈ X, 100 * (symmDiff Aᶜ (B.image (fun b => x - b))).card ≤ k := by
    intro x hx
    have hrx : 200 * r x ≤ k := (Finset.mem_filter.mp hx).2
    let Bx := B.image (fun b => x - b)
    have hBx_card : Bx.card = B.card :=
      Finset.card_image_of_injective B (fun a b h => by simpa using congrArg (x - ·) h)
    have hBx_sdiff : Bx \ Aᶜ = A ∩ Bx := by
      ext u
      simp [and_comm]
    have h1 := Finset.card_sdiff_add_card_inter Aᶜ Bx
    have h2 := Finset.card_sdiff_add_card_inter Bx Aᶜ
    rw [Finset.inter_comm] at h2
    have hAc : Aᶜ.card + A.card = k := by
      have := Finset.card_compl_add_card A
      simpa [Fintype.card_fin] using this
    have hBx_sdiff_card : (Bx \ Aᶜ).card = r x := by
      rw [hBx_sdiff]
    have hsym := card_symmDiff_eq_sdiff_add Aᶜ Bx
    change 100 * (symmDiff Aᶜ Bx).card ≤ k
    omega
  have hd_X_diff : ∀ x ∈ X, ∀ y ∈ X, 50 * d (x - y) ≤ k := by
    intro x hx y hy
    let Bx := B.image (fun b => x - b)
    let By := B.image (fun b => y - b)
    have htri : (symmDiff Bx By).card ≤
        (symmDiff Bx Aᶜ).card + (symmDiff Aᶜ By).card :=
      card_symmDiff_triangle Bx Aᶜ By
    have hcomm : symmDiff Bx Aᶜ = symmDiff Aᶜ Bx := symmDiff_comm Bx Aᶜ
    have h1 : 100 * (symmDiff Aᶜ Bx).card ≤ k := hsymm_X x hx
    have h2 : 100 * (symmDiff Aᶜ By).card ≤ k := hsymm_X y hy
    have hfx : Bx.image (fun u => x - u) = B := by
      ext w
      simp only [Bx, Finset.mem_image]
      constructor
      · rintro ⟨u, ⟨b, hb, rfl⟩, rfl⟩
        simpa [sub_sub_cancel] using hb
      · intro hw
        exact ⟨x - w, ⟨w, hw, rfl⟩, sub_sub_cancel x w⟩
    have hfy : By.image (fun u => x - u) = B.image (· + (x - y)) := by
      ext w
      simp only [By, Finset.mem_image]
      constructor
      · rintro ⟨u, ⟨b, hb, rfl⟩, rfl⟩
        exact ⟨b, hb, by abel⟩
      · rintro ⟨b, hb, rfl⟩
        exact ⟨y - b, ⟨b, hb, rfl⟩, by abel⟩
    have hd_eq : d (x - y) = (symmDiff Bx By).card := by
      have hinj : Function.Injective (fun u : Fin k => x - u) :=
        fun a b h => by simpa using congrArg (x - ·) h
      have := card_symmDiff_image Bx By hinj
      rw [hfx, hfy] at this
      exact this
    rw [hcomm] at htri
    omega
  -- Step 5: T₀ = X - X and H = T₀ + T₀
  let T₀ := (X ×ˢ X).image (fun p => p.1 - p.2)
  let H := (T₀ ×ˢ T₀).image (fun p => p.1 + p.2)
  have hT₀_zero : (0 : Fin k) ∈ T₀ :=
    Finset.mem_image.mpr ⟨(x₀, x₀), Finset.mem_product.mpr ⟨hx₀, hx₀⟩, sub_self x₀⟩
  have hT₀_neg : ∀ t ∈ T₀, -t ∈ T₀ := by
    intro t ht
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
    exact Finset.mem_image.mpr ⟨(y, x), Finset.mem_product.mpr ⟨hy, hx⟩, by abel⟩
  have hT₀_sub_H : T₀ ⊆ H := by
    intro t ht
    exact Finset.mem_image.mpr ⟨(t, 0), Finset.mem_product.mpr ⟨ht, hT₀_zero⟩, add_zero t⟩
  have hX_le_T₀ : X.card ≤ T₀.card := by
    refine Finset.card_le_card_of_injOn (fun x => x - x₀) ?_ ?_
    · intro x hx
      exact Finset.mem_image.mpr ⟨(x, x₀), Finset.mem_product.mpr ⟨hx, hx₀⟩, rfl⟩
    · intro x₁ _ x₂ _ h
      simpa using congrArg (· + x₀) h
  have hT₀_large : 19 * k < 50 * T₀.card := by omega
  have hH_large : 19 * k < 50 * H.card := by
    have := Finset.card_le_card hT₀_sub_H
    omega
  have hd_T₀ : ∀ t ∈ T₀, 50 * d t ≤ k := by
    intro t ht
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
    exact hd_X_diff x hx y hy
  have hd_H : ∀ h ∈ H, 25 * d h ≤ k := by
    intro h hh
    obtain ⟨⟨t₁, t₂⟩, ht, rfl⟩ := Finset.mem_image.mp hh
    obtain ⟨ht₁, ht₂⟩ := Finset.mem_product.mp ht
    have h1 := hd_T₀ t₁ ht₁
    have h2 := hd_T₀ t₂ ht₂
    have h3 := hd_add t₁ t₂
    dsimp only
    omega
  -- Step 6: Prove 2 * H.card ≤ k by summing d z over all z : Fin k
  have hd_eq_two : ∀ z : Fin k, d z = 2 * (B \ B.image (· + z)).card := by
    intro z
    exact card_symmDiff_eq_two_mul_sdiff
      (Finset.card_image_of_injective B (add_left_injective z)).symm
  have hH_le_half : 2 * H.card ≤ k := by
    by_contra hbig
    have hbig : k < 2 * H.card := Nat.lt_of_not_ge hbig
    have hd_all : ∀ z : Fin k, 25 * d z ≤ 2 * k := by
      intro z
      let Hz := H.image (fun h => z - h)
      have hHz_card : Hz.card = H.card :=
        Finset.card_image_of_injective H (fun a b h => by simpa using congrArg (z - ·) h)
      have hinter_ne : (H ∩ Hz).Nonempty := by
        have hun := Finset.card_union_add_card_inter H Hz
        have hle : (H ∪ Hz).card ≤ k := by
          simpa [Fintype.card_fin] using Finset.card_le_univ (H ∪ Hz)
        exact Finset.card_pos.mp (by omega)
      obtain ⟨h₁, hh₁⟩ := hinter_ne
      obtain ⟨hh₁H, hh₁Hz⟩ := Finset.mem_inter.mp hh₁
      obtain ⟨h₂, hh₂H, heq⟩ := Finset.mem_image.mp hh₁Hz
      have hz : z = h₁ + h₂ := by
        rw [← heq]
        abel
      have h1 := hd_H h₁ hh₁H
      have h2 := hd_H h₂ hh₂H
      have h3 := hd_add h₁ h₂
      rw [hz]
      omega
    have hsum_d_all : ∑ z : Fin k, d z = 2 * B.card * (k - B.card) := by
      calc
        ∑ z : Fin k, d z = ∑ z : Fin k, 2 * (B \ B.image (· + z)).card := by
          simp_rw [hd_eq_two]
        _ = 2 * ∑ z ∈ (Finset.univ : Finset (Fin k)), (B \ B.image (· + z)).card := by
          rw [← Finset.mul_sum]
        _ = 2 * ∑ u ∈ B, ((Finset.univ : Finset (Fin k)).image (fun z => u - z) \ B).card := by
          rw [sum_translate_sdiff]
        _ = 2 * ∑ _u ∈ B, (k - B.card) := by
          congr 1
          apply Finset.sum_congr rfl
          intro u _
          have himg : (Finset.univ : Finset (Fin k)).image (fun z => u - z) = Finset.univ := by
            ext w
            simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
            exact ⟨u - w, sub_sub_cancel u w⟩
          rw [himg, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
        _ = 2 * B.card * (k - B.card) := by
          simp [mul_assoc]
    have hsum_upper : 25 * ∑ z : Fin k, d z ≤ 2 * k ^ 2 := by
      calc
        25 * ∑ z : Fin k, d z = ∑ z : Fin k, 25 * d z := by rw [Finset.mul_sum]
        _ ≤ ∑ _z : Fin k, (2 * k) := Finset.sum_le_sum fun z _ => hd_all z
        _ = 2 * k ^ 2 := by
          simp [Fintype.card_fin]
          ring
    have hB_le_k : B.card ≤ k := by
      simpa [Fintype.card_fin] using Finset.card_le_univ B
    have hsum_lower : 99 * k ^ 2 ≤ 200 * ∑ z : Fin k, d z := by
      rw [hsum_d_all]
      have h1 : k ≤ 2 * B.card := hBcard
      have h2 : 99 * k ≤ 200 * (k - B.card) := by omega
      have hmul := Nat.mul_le_mul h1 h2
      calc
        99 * k ^ 2 = k * (99 * k) := by ring
        _ ≤ (2 * B.card) * (200 * (k - B.card)) := hmul
        _ = 200 * (2 * B.card * (k - B.card)) := by ring
    have hk2 : 0 < k ^ 2 := Nat.pow_pos hkpos
    omega
  -- Step 7 & 8: Freiman 3/2 lemma => H is an additive subgroup of Fin k
  have h32 : 2 * H.card < 3 * T₀.card := by omega
  have hH_sub : ∀ x ∈ H, ∀ y ∈ H, x - y ∈ H := by
    have hshift_big : ∀ x ∈ H, T₀.card < 2 * (T₀ ∩ T₀.image (· + x)).card := by
      intro x hx
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      have hnb : -b ∈ T₀ := hT₀_neg b hb
      let Sa := T₀.image (· + a)
      let Sb := T₀.image (· + (-b))
      have hSa_sub : Sa ⊆ H := by
        intro w hw
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hw
        exact Finset.mem_image.mpr ⟨(t, a), Finset.mem_product.mpr ⟨ht, ha⟩, rfl⟩
      have hSb_sub : Sb ⊆ H := by
        intro w hw
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hw
        exact Finset.mem_image.mpr ⟨(t, -b), Finset.mem_product.mpr ⟨ht, hnb⟩, rfl⟩
      have hSa_card : Sa.card = T₀.card :=
        Finset.card_image_of_injective T₀ (add_left_injective a)
      have hSb_card : Sb.card = T₀.card :=
        Finset.card_image_of_injective T₀ (add_left_injective (-b))
      have hun := Finset.card_union_add_card_inter Sa Sb
      have hle : (Sa ∪ Sb).card ≤ H.card := Finset.card_le_card (Finset.union_subset hSa_sub hSb_sub)
      have hbij : (Sa ∩ Sb).card = (T₀ ∩ T₀.image (· + (a + b))).card := by
        refine Finset.card_bij (fun w _ => w + b) ?_ ?_ ?_
        · intro w hw
          obtain ⟨hwa, hwb⟩ := Finset.mem_inter.mp hw
          obtain ⟨t₁, ht₁, rfl⟩ := Finset.mem_image.mp hwa
          obtain ⟨t₂, ht₂, heq⟩ := Finset.mem_image.mp hwb
          refine Finset.mem_inter.mpr ⟨?_, ?_⟩
          · have : t₁ + a + b = t₂ := by
              rw [← heq]
              abel
            exact this ▸ ht₂
          · exact Finset.mem_image.mpr ⟨t₁, ht₁, by abel⟩
        · intro w₁ _ w₂ _ h
          exact add_right_cancel h
        · intro z hz
          obtain ⟨hzT, hzimg⟩ := Finset.mem_inter.mp hz
          obtain ⟨t₁, ht₁, rfl⟩ := Finset.mem_image.mp hzimg
          refine ⟨t₁ + a, Finset.mem_inter.mpr ⟨?_, ?_⟩, by abel⟩
          · exact Finset.mem_image.mpr ⟨t₁, ht₁, rfl⟩
          · exact Finset.mem_image.mpr ⟨t₁ + (a + b), hzT, by abel⟩
      dsimp only
      omega
    intro x hx y hy
    let Sx := T₀ ∩ T₀.image (· + x)
    let Sy := T₀ ∩ T₀.image (· + y)
    have h1 : T₀.card < 2 * Sx.card := hshift_big x hx
    have h2 : T₀.card < 2 * Sy.card := hshift_big y hy
    have hun := Finset.card_union_add_card_inter Sx Sy
    have hle : (Sx ∪ Sy).card ≤ T₀.card :=
      Finset.card_le_card (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
    have hne : (Sx ∩ Sy).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨z, hz⟩ := hne
    obtain ⟨hzx, hzy⟩ := Finset.mem_inter.mp hz
    obtain ⟨t₁, ht₁, heq₁⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hzx).2
    obtain ⟨t₂, ht₂, heq₂⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hzy).2
    have hxy : x - y = t₂ + (-t₁) := by
      have h1' : x = z - t₁ := eq_sub_of_add_eq' heq₁
      have h2' : y = z - t₂ := eq_sub_of_add_eq' heq₂
      rw [h1', h2']
      abel
    rw [hxy]
    exact Finset.mem_image.mpr ⟨(t₂, -t₁), Finset.mem_product.mpr ⟨ht₂, hT₀_neg t₁ ht₁⟩, rfl⟩
  have hH_zero : (0 : Fin k) ∈ H := hT₀_sub_H hT₀_zero
  have hH_neg : ∀ x ∈ H, -x ∈ H := by
    intro x hx
    simpa using hH_sub 0 hH_zero x hx
  have hH_add : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H := by
    intro x hx y hy
    simpa using hH_sub x hx (-y) (hH_neg y hy)
  -- Step 9: Lagrange's theorem (direct coset partition) gives 2 * H.card = k
  have hdvd : H.card ∣ k := by
    let C : Finset (Finset (Fin k)) := Finset.univ.image (fun x => H.image (x + ·))
    have hdisj : (C : Set (Finset (Fin k))).PairwiseDisjoint id := by
      intro S₁ hS₁ S₂ hS₂ hne
      obtain ⟨x₁, _, rfl⟩ := Finset.mem_image.mp hS₁
      obtain ⟨x₂, _, rfl⟩ := Finset.mem_image.mp hS₂
      rw [Function.onFun, id, id, Finset.disjoint_left]
      intro w hw₁ hw₂
      apply hne
      obtain ⟨h₁, hh₁, rfl⟩ := Finset.mem_image.mp hw₁
      obtain ⟨h₂, hh₂, heq⟩ := Finset.mem_image.mp hw₂
      ext u
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨h, hh, rfl⟩
        refine ⟨h₂ + (h - h₁), hH_add h₂ hh₂ (h - h₁) (hH_sub h hh h₁ hh₁), ?_⟩
        have hx : x₁ = x₂ + h₂ - h₁ := by
          rw [heq]
          abel
        rw [hx]
        abel
      · rintro ⟨h, hh, rfl⟩
        refine ⟨h₁ + (h - h₂), hH_add h₁ hh₁ (h - h₂) (hH_sub h hh h₂ hh₂), ?_⟩
        have hx : x₂ = x₁ + h₁ - h₂ := by
          rw [← heq]
          abel
        rw [hx]
        abel
    have hbi : C.biUnion id = Finset.univ := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true, id]
      exact ⟨H.image (x + ·), Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩,
        Finset.mem_image.mpr ⟨0, hH_zero, add_zero x⟩⟩
    have hcard_coset : ∀ S ∈ C, S.card = H.card := by
      intro S hS
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hS
      exact Finset.card_image_of_injective H (fun _ _ h => add_left_cancel h)
    have htot : k = C.card * H.card := by
      calc
        k = (Finset.univ : Finset (Fin k)).card := by simp
        _ = (C.biUnion id).card := by rw [hbi]
        _ = ∑ S ∈ C, S.card := Finset.card_biUnion hdisj
        _ = ∑ _S ∈ C, H.card := Finset.sum_congr rfl hcard_coset
        _ = C.card * H.card := by simp
    exact ⟨C.card, htot.trans (mul_comm _ _)⟩
  obtain ⟨q, hq⟩ := hdvd
  set m := H.card
  have hm_pos : 0 < m := Finset.card_pos.mpr ⟨0, hH_zero⟩
  have hq2 : q = 2 := by
    have hq_ge : 2 ≤ q := by
      by_contra hlt2
      have : q ≤ 1 := by omega
      have : m * q ≤ m * 1 := Nat.mul_le_mul_left m this
      omega
    have hq_le : q ≤ 2 := by
      by_contra hgt2
      have : 3 ≤ q := by omega
      have : m * 3 ≤ m * q := Nat.mul_le_mul_left m this
      omega
    omega
  have hk_eq : k = 2 * m := by
    rw [hq, hq2]
    ring
  -- Step 10: Sum d h over h ∈ H and derive contradiction
  let B₁ := B ∩ H
  let B₂ := B ∩ Hᶜ
  set a := B₁.card
  set b := B₂.card
  have hHc_card : Hᶜ.card = m := by
    have := Finset.card_compl_add_card H
    simp only [Fintype.card_fin] at this
    omega
  have hab_sum : a + b = B.card := by
    have hdisj : Disjoint B₁ B₂ := Finset.disjoint_left.mpr fun u h1 h2 =>
      (Finset.mem_compl.mp (Finset.mem_inter.mp h2).2) (Finset.mem_inter.mp h1).2
    have hunion : B₁ ∪ B₂ = B := by
      ext u
      simp only [B₁, B₂, Finset.mem_union, Finset.mem_inter, Finset.mem_compl]
      by_cases hu : u ∈ H <;> simp [hu]
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have ha_le : a ≤ m := Finset.card_le_card Finset.inter_subset_right
  have hb_le : b ≤ m := by
    calc
      b ≤ Hᶜ.card := Finset.card_le_card Finset.inter_subset_right
      _ = m := hHc_card
  have hsum_H : ∑ h ∈ H, d h = 2 * (a * (m - a) + b * (m - b)) := by
    have h1 : ∑ h ∈ H, d h = 2 * ∑ u ∈ B, (H.image (fun h => u - h) \ B).card := by
      calc
        ∑ h ∈ H, d h = ∑ h ∈ H, 2 * (B \ B.image (· + h)).card := by
          simp_rw [hd_eq_two]
        _ = 2 * ∑ h ∈ H, (B \ B.image (· + h)).card := by rw [← Finset.mul_sum]
        _ = 2 * ∑ u ∈ B, (H.image (fun h => u - h) \ B).card := by rw [sum_translate_sdiff]
    rw [h1]
    congr 1
    have hdisj : Disjoint B₁ B₂ := Finset.disjoint_left.mpr fun u h1 h2 =>
      (Finset.mem_compl.mp (Finset.mem_inter.mp h2).2) (Finset.mem_inter.mp h1).2
    have hunion : B₁ ∪ B₂ = B := by
      ext u
      simp only [B₁, B₂, Finset.mem_union, Finset.mem_inter, Finset.mem_compl]
      by_cases hu : u ∈ H <;> simp [hu]
    have hsum1 : ∑ u ∈ B₁, (H.image (fun h => u - h) \ B).card = a * (m - a) := by
      calc
        ∑ u ∈ B₁, (H.image (fun h => u - h) \ B).card = ∑ _u ∈ B₁, (m - a) := by
          apply Finset.sum_congr rfl
          intro u hu
          have huH : u ∈ H := (Finset.mem_inter.mp hu).2
          have himg : H.image (fun h => u - h) = H := by
            ext w
            simp only [Finset.mem_image]
            constructor
            · rintro ⟨h, hh, rfl⟩
              exact hH_sub u huH h hh
            · intro hw
              exact ⟨u - w, hH_sub u huH w hw, sub_sub_cancel u w⟩
          rw [himg]
          have hsd : (H \ B).card + (H ∩ B).card = H.card := Finset.card_sdiff_add_card_inter H B
          rw [Finset.inter_comm] at hsd
          have ha_eq : (B ∩ H).card = a := rfl
          have hm_eq : H.card = m := rfl
          omega
        _ = a * (m - a) := by simp [a]
    have hsum2 : ∑ u ∈ B₂, (H.image (fun h => u - h) \ B).card = b * (m - b) := by
      calc
        ∑ u ∈ B₂, (H.image (fun h => u - h) \ B).card = ∑ _u ∈ B₂, (m - b) := by
          apply Finset.sum_congr rfl
          intro u hu
          have huHc : u ∈ Hᶜ := (Finset.mem_inter.mp hu).2
          have huNotH : u ∉ H := Finset.mem_compl.mp huHc
          have himg : H.image (fun h => u - h) = Hᶜ := by
            apply Finset.eq_of_subset_of_card_le
            · intro w hw
              obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hw
              refine Finset.mem_compl.mpr fun hsub => huNotH ?_
              have := hH_add (u - h) hsub h hh
              simpa [sub_add_cancel] using this
            · rw [hHc_card,
                Finset.card_image_of_injective H (fun x y h => by simpa using congrArg (u - ·) h)]
          rw [himg]
          have hsd : (Hᶜ \ B).card + (Hᶜ ∩ B).card = Hᶜ.card :=
            Finset.card_sdiff_add_card_inter Hᶜ B
          rw [Finset.inter_comm] at hsd
          have hb_eq : (B ∩ Hᶜ).card = b := rfl
          omega
        _ = b * (m - b) := by simp [b]
    calc
      ∑ u ∈ B, (H.image (fun h => u - h) \ B).card
          = ∑ u ∈ B₁ ∪ B₂, (H.image (fun h => u - h) \ B).card := by rw [hunion]
      _ = ∑ u ∈ B₁, (H.image (fun h => u - h) \ B).card +
          ∑ u ∈ B₂, (H.image (fun h => u - h) \ B).card := Finset.sum_union hdisj
      _ = a * (m - a) + b * (m - b) := by rw [hsum1, hsum2]
  have hsum_H_upper : 25 * (a * (m - a) + b * (m - b)) ≤ m ^ 2 := by
    have hle : 25 * ∑ h ∈ H, d h ≤ 2 * m ^ 2 := by
      calc
        25 * ∑ h ∈ H, d h = ∑ h ∈ H, 25 * d h := by rw [Finset.mul_sum]
        _ ≤ ∑ _h ∈ H, k := Finset.sum_le_sum fun h hh => hd_H h hh
        _ = m * k := by simp [m]
        _ = 2 * m ^ 2 := by rw [hk_eq]; ring
    rw [hsum_H] at hle
    omega
  -- Overlap bounds on B₁ and B₂
  set c := (B ∩ B.image (- ·)).card
  have hc_bound : 50 * c ≤ m := by omega
  have ha_upper : 2 * a ≤ m + c := by
    have hsub : B₁ ∩ B₁.image (- ·) ⊆ B ∩ B.image (- ·) := by
      apply Finset.inter_subset_inter Finset.inter_subset_left
      exact Finset.image_subset_image Finset.inter_subset_left
    have hcard_inter : (B₁ ∩ B₁.image (- ·)).card ≤ c := Finset.card_le_card hsub
    have hun_sub : B₁ ∪ B₁.image (- ·) ⊆ H := by
      refine Finset.union_subset Finset.inter_subset_right ?_
      intro u hu
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      exact hH_neg v (Finset.mem_inter.mp hv).2
    have hle : (B₁ ∪ B₁.image (- ·)).card ≤ m := Finset.card_le_card hun_sub
    have hneg : (B₁.image (- ·)).card = a :=
      Finset.card_image_of_injective B₁ neg_injective
    have hun := Finset.card_union_add_card_inter B₁ (B₁.image (- ·))
    omega
  have hb_upper : 2 * b ≤ m + c := by
    have hsub : B₂ ∩ B₂.image (- ·) ⊆ B ∩ B.image (- ·) := by
      apply Finset.inter_subset_inter Finset.inter_subset_left
      exact Finset.image_subset_image Finset.inter_subset_left
    have hcard_inter : (B₂ ∩ B₂.image (- ·)).card ≤ c := Finset.card_le_card hsub
    have hun_sub : B₂ ∪ B₂.image (- ·) ⊆ Hᶜ := by
      refine Finset.union_subset Finset.inter_subset_right ?_
      intro u hu
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      have hvNotH : v ∉ H := Finset.mem_compl.mp (Finset.mem_inter.mp hv).2
      exact Finset.mem_compl.mpr fun hnv => hvNotH (by simpa using hH_neg (-v) hnv)
    have hle : (B₂ ∪ B₂.image (- ·)).card ≤ m := by
      calc
        (B₂ ∪ B₂.image (- ·)).card ≤ Hᶜ.card := Finset.card_le_card hun_sub
        _ = m := hHc_card
    have hneg : (B₂.image (- ·)).card = b :=
      Finset.card_image_of_injective B₂ neg_injective
    have hun := Finset.card_union_add_card_inter B₂ (B₂.image (- ·))
    omega
  have ha_lo : 49 * m ≤ 100 * a := by omega
  have hma_lo : 49 * m ≤ 100 * (m - a) := by omega
  have hprod_lo : 2401 * m ^ 2 ≤ 10000 * (a * (m - a)) := by
    have hmul := Nat.mul_le_mul ha_lo hma_lo
    calc
      2401 * m ^ 2 = (49 * m) * (49 * m) := by ring
      _ ≤ (100 * a) * (100 * (m - a)) := hmul
      _ = 10000 * (a * (m - a)) := by ring
  have hprod_hi : 10000 * (a * (m - a)) ≤ 400 * m ^ 2 := by
    have : 25 * (a * (m - a)) ≤ m ^ 2 := by omega
    omega
  have hm2 : 0 < m ^ 2 := Nat.pow_pos hm_pos
  omega

end MMSPokrovskiyH1

theorem OMA.solution : OMA.R_ManickamMiklosSinghiConjecture_manickam_miklos_singhi_conjecture_variants_pokrovskiy_R1_H2_R1.H1 := by
  exact MMSPokrovskiyH1.main_bound
