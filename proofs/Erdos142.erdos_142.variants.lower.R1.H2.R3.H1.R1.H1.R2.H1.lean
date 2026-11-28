import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R2
import Mathlib

namespace E142W
open Finset

lemma arith (n t δ M M' b : ℕ) (ht : t ≤ n) (htd : t ≤ δ + 1) (hd : n * δ ≤ 2 * M)
    (hm : t * t + 2 * M' ≤ t + 2 * M) (ih : (n - t) ^ 2 ≤ (n - t + 2 * M') * b) :
    n ^ 2 ≤ (n + 2 * M) * (b + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  simp only [Nat.add_sub_cancel_left] at ih
  have hD1 : (t + k) * t ≤ t + k + 2 * M := by
    have := Nat.mul_le_mul_left (t + k) htd
    nlinarith
  have hD2 : t * t ≤ (t + k) * t := by nlinarith
  have hk : k + 2 * M' + t * t ≤ t + k + 2 * M := by omega
  have hb : (0:ℤ) ≤ b := by positivity
  have hD0 : (0:ℤ) ≤ (t:ℤ) + k + 2 * M := by positivity
  have hD1' : ((t:ℤ) + k) * t ≤ (t:ℤ) + k + 2 * M := by exact_mod_cast hD1
  have hD2' : (t:ℤ) * t ≤ (t:ℤ) + k + 2 * M := by
    have : (t:ℤ) * t ≤ ((t:ℤ) + k) * t := by exact_mod_cast hD2
    linarith
  have hk' : (k:ℤ) + 2 * M' ≤ ((t:ℤ) + k + 2 * M) - t * t := by
    have : (k:ℤ) + 2 * M' + t * t ≤ (t:ℤ) + k + 2 * M := by exact_mod_cast hk
    linarith
  have ih' : (k:ℤ) ^ 2 ≤ ((k:ℤ) + 2 * M') * b := by exact_mod_cast ih
  have h3 : (k:ℤ) ^ 2 ≤ (((t:ℤ) + k + 2 * M) - t * t) * b :=
    ih'.trans (mul_le_mul_of_nonneg_right hk' hb)
  have iden : (((t:ℤ) + k + 2 * M) - t * t) * (((t:ℤ) + k + 2 * M) * (b + 1) - ((t:ℤ) + k) ^ 2)
      = ((t:ℤ) + k + 2 * M) * ((((t:ℤ) + k + 2 * M) - t * t) * b - (k:ℤ) ^ 2)
        + (((t:ℤ) + k + 2 * M) - ((t:ℤ) + k) * t) ^ 2 := by ring
  suffices hz : ((t:ℤ) + k) ^ 2 ≤ ((t:ℤ) + k + 2 * M) * (b + 1) by exact_mod_cast hz
  rcases eq_or_lt_of_le hD2' with heq | hlt
  · rw [← heq] at h3
    have hk0 : (k:ℤ) ^ 2 ≤ 0 := by simpa using h3
    have : (k:ℤ) = 0 := by nlinarith [sq_nonneg (k:ℤ)]
    rw [← heq, this]
    nlinarith [mul_nonneg (mul_nonneg (Int.natCast_nonneg t) (Int.natCast_nonneg t)) hb]
  · by_contra hcon'
    have hcon := not_le.mp hcon'
    have hneg : (((t:ℤ) + k + 2 * M) - t * t) * (((t:ℤ) + k + 2 * M) * (b + 1) - ((t:ℤ) + k) ^ 2) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (by linarith)
    have hpos : 0 ≤ ((t:ℤ) + k + 2 * M) * ((((t:ℤ) + k + 2 * M) - t * t) * b - (k:ℤ) ^ 2)
        + (((t:ℤ) + k + 2 * M) - ((t:ℤ) + k) * t) ^ 2 :=
      add_nonneg (mul_nonneg hD0 (by linarith)) (sq_nonneg _)
    linarith

variable {V : Type} [DecidableEq V]

def EA (E : Finset (V × V)) (A : Finset V) : Finset (V × V) :=
  E.filter (fun e => e.1 ∈ A ∧ e.2 ∈ A)

def deg (E : Finset (V × V)) (A : Finset V) (v : V) : ℕ :=
  ((EA E A).filter (fun e => e.1 = v ∨ e.2 = v)).card

lemma sum_deg_le (E : Finset (V × V)) (A S : Finset V) :
    ∑ u ∈ S, deg E A u ≤ 2 * ((EA E A).filter (fun e => e.1 ∈ S ∨ e.2 ∈ S)).card := by
  set T := (EA E A).filter (fun e => e.1 ∈ S ∨ e.2 ∈ S) with hT
  calc ∑ u ∈ S, deg E A u ≤ ∑ u ∈ S, (T.filter (fun e => e.1 = u ∨ e.2 = u)).card := by
        apply Finset.sum_le_sum
        intro u hu
        apply Finset.card_le_card
        intro e he
        simp only [Finset.mem_filter, hT] at he ⊢
        refine ⟨⟨he.1, ?_⟩, he.2⟩
        rcases he.2 with h | h
        · left; rw [h]; exact hu
        · right; rw [h]; exact hu
    _ = ∑ e ∈ T, (S.filter (fun u => e.1 = u ∨ e.2 = u)).card :=
        Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (r := fun (u : V) (e : V × V) => e.1 = u ∨ e.2 = u)
    _ ≤ ∑ _e ∈ T, 2 := by
        apply Finset.sum_le_sum
        intro e _
        calc (S.filter (fun u => e.1 = u ∨ e.2 = u)).card ≤ ({e.1, e.2} : Finset V).card := by
              apply Finset.card_le_card
              intro u hu
              simp only [Finset.mem_filter] at hu
              rcases hu.2 with h | h <;> simp [h]
          _ ≤ 2 := Finset.card_le_two
    _ = 2 * T.card := by simp [mul_comm]

lemma main (E : Finset (V × V)) (hE : ∀ e ∈ E, e.1 ≠ e.2) (A : Finset V) :
    ∃ B ⊆ A, (∀ e ∈ E, e.1 ∈ B → e.2 ∉ B) ∧
      A.card ^ 2 ≤ (A.card + 2 * (EA E A).card) * B.card := by
  induction A using Finset.strongInduction with
  | H A ih =>
  rcases A.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, subset_refl _, by simp, by simp⟩
  obtain ⟨v, hvA, hvmin⟩ := Finset.exists_min_image A (deg E A) hne
  set δ := deg E A v with hδ
  set R := A.filter (fun u => u = v ∨ (u, v) ∈ E ∨ (v, u) ∈ E) with hR
  set T := (EA E A).filter (fun e => e.1 ∈ R ∨ e.2 ∈ R) with hT
  have hvR : v ∈ R := by simp [hR, hvA]
  have hRA : R ⊆ A := Finset.filter_subset _ _
  have htd : R.card ≤ δ + 1 := by
    have h1 : R.erase v ⊆ ((EA E A).filter (fun e => e.1 = v ∨ e.2 = v)).image
        (fun e => if e.1 = v then e.2 else e.1) := by
      intro u hu
      simp only [Finset.mem_erase, hR, Finset.mem_filter] at hu
      obtain ⟨huv, huA, h⟩ := hu
      simp only [Finset.mem_image, Finset.mem_filter, EA]
      rcases h with h | h | h
      · exact absurd h huv
      · exact ⟨(u, v), ⟨⟨h, huA, hvA⟩, Or.inr rfl⟩, by simp [huv]⟩
      · exact ⟨(v, u), ⟨⟨h, hvA, huA⟩, Or.inl rfl⟩, by simp⟩
    have h2 : (R.erase v).card ≤ δ := (Finset.card_le_card h1).trans Finset.card_image_le
    have h3 := Finset.card_erase_add_one hvR
    omega
  have hnδ : A.card * δ ≤ 2 * (EA E A).card := by
    have h1 : A.card • δ ≤ ∑ u ∈ A, deg E A u :=
      Finset.card_nsmul_le_sum _ _ _ (fun u hu => hvmin u hu)
    have h2 := sum_deg_le E A A
    have h3 : ((EA E A).filter (fun e => e.1 ∈ A ∨ e.2 ∈ A)).card ≤ (EA E A).card :=
      Finset.card_filter_le _ _
    simp only [smul_eq_mul] at h1
    omega
  have hRδ : R.card * δ ≤ 2 * T.card := by
    have h1 : R.card • δ ≤ ∑ u ∈ R, deg E A u :=
      Finset.card_nsmul_le_sum _ _ _ (fun u hu => hvmin u (hRA hu))
    have h2 : ∑ u ∈ R, deg E A u ≤ 2 * T.card := sum_deg_le E A R
    simp only [smul_eq_mul] at h1
    omega
  have hm : (EA E (A \ R)).card + T.card ≤ (EA E A).card := by
    rw [← Finset.card_union_of_disjoint]
    · apply Finset.card_le_card
      intro e he
      rcases Finset.mem_union.1 he with he | he
      · simp only [EA, Finset.mem_filter, Finset.mem_sdiff] at he ⊢
        exact ⟨he.1, he.2.1.1, he.2.2.1⟩
      · exact (Finset.mem_filter.1 he).1
    · rw [Finset.disjoint_left]
      intro e he1 he2
      simp only [EA, hT, Finset.mem_filter, Finset.mem_sdiff] at he1 he2
      rcases he2.2 with h | h
      · exact he1.2.1.2 h
      · exact he1.2.2.2 h
  have hss : A \ R ⊂ A := Finset.sdiff_ssubset hRA ⟨v, hvR⟩
  obtain ⟨B', hB'A, hB'ind, hB'card⟩ := ih (A \ R) hss
  have hvB' : v ∉ B' := fun h => (Finset.mem_sdiff.1 (hB'A h)).2 hvR
  refine ⟨insert v B', ?_, ?_, ?_⟩
  · intro u hu
    rcases Finset.mem_insert.1 hu with rfl | hu
    · exact hvA
    · exact (Finset.mem_sdiff.1 (hB'A hu)).1
  · rintro ⟨a, c⟩ he h1 h2
    simp only [Finset.mem_insert] at h1 h2
    rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
    · exact hE _ he rfl
    · have hc := Finset.mem_sdiff.1 (hB'A h2)
      exact hc.2 (by simp [hR, hc.1, he])
    · have ha := Finset.mem_sdiff.1 (hB'A h1)
      exact ha.2 (by simp [hR, ha.1, he])
    · exact hB'ind _ he h1 h2
  · rw [Finset.card_insert_of_notMem hvB']
    rw [Finset.card_sdiff_of_subset hRA] at hB'card
    have hmul : R.card * R.card ≤ R.card * δ + R.card := by
      have := Nat.mul_le_mul_left R.card htd
      linarith
    exact arith A.card R.card δ (EA E A).card (EA E (A \ R)).card B'.card
      (Finset.card_le_card hRA) htd hnδ (by linarith) hB'card

end E142W

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R2.H1 := by
  intro V A E hE
  classical
  obtain ⟨B, hBA, hind, hcard⟩ := E142W.main E hE A
  refine ⟨B, hBA, ?_, hind⟩
  have : (E142W.EA E A).card ≤ E.card := Finset.card_filter_le _ _
  calc A.card ^ 2 ≤ _ := hcard
    _ ≤ _ := by apply Nat.mul_le_mul_right; omega
