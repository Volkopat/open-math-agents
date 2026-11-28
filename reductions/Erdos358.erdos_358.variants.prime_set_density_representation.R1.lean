import FormalConjectures.ErdosProblems.«358»
import Mathlib

/-! A finite family of dyadic prime intervals, and a sufficient bound on repeated sums. -/

namespace OMA.R_Erdos358_erdos_358_variants_prime_set_density_representation_R1

open Filter Finset

/-- An explicit, weak Chebyshev upper bound on a prime of dyadic index. -/
def H1 : Prop := ∀ s : ℕ, Nat.nth Nat.Prime (2^s) ≤ 16 * (s+1) * 2^s

/-- On arbitrarily high scales, at least half of the sampled prime intervals have
a sum which occurs at most a fixed number of times within that sample. -/
def H2 : Prop :=
  let blocks (k : ℕ) : Finset (ℕ × ℕ) :=
    (range k).biUnion fun j => (Ico (2^j) (2^(j+1))) ×ˢ (range (2^(2*k-j)))
  let value (b : ℕ × ℕ) := ∑ i ∈ Icc (b.2+1) (b.2+b.1), Nat.nth Nat.Prime i
  let crowded (k B : ℕ) := (blocks k).filter fun b =>
    B < ((blocks k).filter fun c => value c = value b).card
  ∃ B : ℕ, 0 < B ∧ ∃ᶠ k : ℕ in atTop,
  2 * (crowded k B).card ≤ (blocks k).card

theorem blocks_card (k : ℕ) : ((range k).biUnion (fun j => (Ico (2^j) (2^(j+1))) ×ˢ (range (2^(2*k-j))))).card = k * 2^(2*k) := by
  classical
  rw [card_biUnion]
  · calc
      _ = ∑ _j ∈ range k, 2^(2*k) := by
        apply sum_congr rfl
        intro j hj
        have h := mem_range.mp hj
        simp only [card_product, Nat.card_Ico, card_range, pow_succ]
        rw [show 2^j*2-2^j=2^j by omega, ← pow_add]
        congr 1; omega
      _ = _ := by simp
  · intro i hi j hj hne
    apply Finset.disjoint_left.mpr
    intro b hb hb'
    have h := mem_Ico.mp (mem_product.mp hb).1
    have h' := mem_Ico.mp (mem_product.mp hb').1
    rcases lt_or_gt_of_ne hne with hij|hji
    · have hp : (2:ℕ)^(i+1) ≤ 2^j := Nat.pow_le_pow_right (by decide) hij
      omega
    · have hp : (2:ℕ)^(j+1) ≤ 2^i := Nat.pow_le_pow_right (by decide) hji
      omega

theorem value_bound (hp : H1) {k : ℕ} {b : ℕ × ℕ} (hb : b ∈ ((range k).biUnion (fun j => (Ico (2^j) (2^(j+1))) ×ˢ (range (2^(2*k-j)))))) :
    (∑ i ∈ Icc (b.2+1) (b.2+b.1), Nat.nth Nat.Prime i) ≤ 256 * k * 2^(2*k) := by
  obtain ⟨j,hj,hs⟩ := mem_biUnion.mp hb
  have hjk := mem_range.mp hj
  have hl := mem_Ico.mp (mem_product.mp hs).1
  have ha := mem_range.mp (mem_product.mp hs).2
  let d := 2*k-j
  have hjd : j+1 ≤ d := by dsimp [d]; omega
  have hld : (2:ℕ)^(j+1) ≤ 2^d := Nat.pow_le_pow_right (by decide) hjd
  have hend : b.2+b.1 ≤ 2^(d+1) := by rw [pow_succ]; change b.2 < 2^d at ha; omega
  have hprime (i : ℕ) (hi : i ∈ Icc (b.2+1) (b.2+b.1)) :
      Nat.nth Nat.Prime i ≤ 16*(d+2)*2^(d+1) :=
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone ((mem_Icc.mp hi).2.trans hend) |>.trans (hp (d+1))
  calc
    _ ≤ ∑ _i ∈ Icc (b.2+1) (b.2+b.1), 16*(d+2)*2^(d+1) := sum_le_sum hprime
    _ = b.1 * (16*(d+2)*2^(d+1)) := by simp
    _ ≤ 2^(j+1) * (16*(d+2)*2^(d+1)) := Nat.mul_le_mul_right _ hl.2.le
    _ = 64*(d+2)*2^(2*k) := by
        have hpow : 2^(j+d) = (2:ℕ)^(2*k) := by congr 1; dsimp [d]; omega
        rw [← hpow,pow_add,pow_succ,pow_succ]; ring
    _ ≤ 256*k*2^(2*k) := by
        apply Nat.mul_le_mul_right
        dsimp [d]; omega

theorem belongs {k : ℕ} {b : ℕ × ℕ} (hb : b ∈ ((range k).biUnion (fun j => (Ico (2^j) (2^(j+1))) ×ˢ (range (2^(2*k-j)))))) :
    (Erdos358.intervalRepresentations (Nat.nth Nat.Prime) ((∑ i ∈ Icc (b.2+1) (b.2+b.1), Nat.nth Nat.Prime i))).Nonempty := by
  obtain ⟨j,_,hs⟩ := mem_biUnion.mp hb
  have h := (mem_Ico.mp (mem_product.mp hs).1).1
  have : 0 < (2:ℕ)^j := by positivity
  exact ⟨(b.2+1,b.2+b.1), by exact ⟨by omega, by omega, rfl⟩⟩

theorem light_bound {α : Type*} [DecidableEq α] (D : Finset α) (value : α → ℕ) (B : ℕ) :
    (D \ (D.filter fun b => B < (D.filter fun c => value c = value b).card)).card ≤ B * (D.image value).card := by
  classical
  let L := D \ (D.filter fun b => B < (D.filter fun c => value c = value b).card)
  let V := D.image value
  have sub : L ⊆ D := sdiff_subset
  change L.card ≤ B * V.card
  calc
    _ = ∑ n ∈ V, (L.filter (fun b => value b = n)).card :=
        card_eq_sum_card_fiberwise (fun b hb => mem_image_of_mem _ (sub hb))
    _ ≤ ∑ _n ∈ V, B := by
      apply sum_le_sum
      intro n _
      by_cases h : (L.filter (fun b => value b = n)).Nonempty
      · obtain ⟨b,hb⟩ := h
        obtain ⟨hb,hen⟩ := mem_filter.mp hb
        have hn := (mem_sdiff.mp hb).2
        have hle : (D.filter fun c => value c = n).card ≤ B := by
          by_contra! hcontr
          apply hn
          exact mem_filter.mpr ⟨sub hb,hen ▸ hcontr⟩
        exact (card_le_card (filter_subset_filter _ sub)).trans hle
      · rw [not_nonempty_iff_eq_empty.mp h]; simp
    _ = _ := by simp [Nat.mul_comm]

theorem main : H1 → H2 → type_of% @Erdos358.erdos_358.variants.prime_set_density_representation := by
  classical
  intro hp ⟨B,hB,hfreq⟩
  let blocks (k : ℕ) : Finset (ℕ × ℕ) :=
    (range k).biUnion fun j => (Ico (2^j) (2^(j+1))) ×ˢ (range (2^(2*k-j)))
  let value (b : ℕ × ℕ) := ∑ i ∈ Icc (b.2+1) (b.2+b.1), Nat.nth Nat.Prime i
  let crowded (k B : ℕ) := (blocks k).filter fun b =>
    B < ((blocks k).filter fun c => value c = value b).card
  change ∃ᶠ k : ℕ in atTop, 2 * (crowded k B).card ≤ (blocks k).card at hfreq
  let S := {n | (Erdos358.intervalRepresentations (Nat.nth Nat.Prime) n).Nonempty}
  change 0 < S.upperDensity
  apply lt_of_lt_of_le (show 0 < (1:ℝ)/(514*(B:ℝ)) by positivity)
  apply le_limsup_of_frequently_le
  · rw [frequently_atTop] at hfreq ⊢
    intro n
    obtain ⟨k,hk,hc⟩ := hfreq (n+1)
    let W := k*2^(2*k)
    let x := 256*W+1
    have hw : 0 < W := Nat.mul_pos (by omega) (pow_pos (by decide) _)
    have hkw : k ≤ W := Nat.le_mul_of_pos_right _ (pow_pos (by decide) _)
    refine ⟨x,by dsimp [x]; omega,?_⟩
    have hlight := light_bound (blocks k) value B
    change ((blocks k) \ (crowded k B)).card ≤ B * ((blocks k).image value).card at hlight
    have ht := card_sdiff_add_card_eq_card (show crowded k B ⊆ blocks k from filter_subset _ _)
    rw [blocks_card] at hc ht
    have hcover : ↑((blocks k).image value) ⊆ (S ∩ Set.univ) ∩ Set.Iio x := by
      intro z hz
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hz
      have hval := value_bound hp hb
      change value b ≤ 256*k*2^(2*k) at hval
      refine ⟨⟨belongs hb,Set.mem_univ _⟩,?_⟩
      change value b < 256*(k*2^(2*k))+1
      rw [← Nat.mul_assoc]; omega
    have hcard := Set.ncard_le_ncard hcover
    rw [Set.ncard_coe_finset] at hcard
    have htot : W ≤ 2 * (B * ((S ∩ Set.univ) ∩ Set.Iio x).ncard) := by
      have hm := Nat.mul_le_mul_left B hcard
      change 2 * (crowded k B).card ≤ W at hc
      change _ + _ = W at ht
      omega
    change 1 / (514*(B:ℝ)) ≤ (((S ∩ Set.univ) ∩ Set.Iio x).ncard:ℝ) / _
    simp only [Set.univ_inter, Set.ncard_Iio_nat]
    have hx : 0 < x := by dsimp [x]; omega
    apply (div_le_div_iff₀ (by positivity) (by exact_mod_cast hx)).mpr
    have hxx : x ≤ 257 * W := by dsimp [x]; omega
    have hr : (W:ℝ) ≤ 2*((B:ℝ)*(((S ∩ Set.univ) ∩ Set.Iio x).ncard:ℝ)) := by exact_mod_cast htot
    have hr' : (x:ℝ) ≤ 257 * (W:ℝ) := by exact_mod_cast hxx
    nlinarith
  · refine ⟨1,?_⟩
    change ∀ᶠ n : ℕ in atTop, S.partialDensity Set.univ n ≤ 1
    exact Filter.Eventually.of_forall (fun n => S.partialDensity_le_one Set.univ n)

end OMA.R_Erdos358_erdos_358_variants_prime_set_density_representation_R1
