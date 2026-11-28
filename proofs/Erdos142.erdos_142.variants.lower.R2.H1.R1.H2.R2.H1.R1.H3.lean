import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R1
import Mathlib

namespace E142W

def Free3 (G : Finset ℕ) : Prop :=
  ∀ a d : ℕ, 0 < d → a ∈ G → a + d ∈ G → a + 2 * d ∈ G → False

theorem bridge (G : Finset ℕ) (h : Free3 G) : ((G : Set ℕ)).IsAPOfLengthFree 3 := by
  intro t ht hAP
  exfalso
  obtain ⟨a, d, hcard, heq⟩ := hAP
  have h0 : a ∈ t := by rw [heq]; exact ⟨0, by norm_num, by simp⟩
  have h1 : a + d ∈ t := by rw [heq]; exact ⟨1, by norm_num, by simp⟩
  have h2 : a + 2 * d ∈ t := by rw [heq]; exact ⟨2, by norm_num, by simp⟩
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have ht1 : t = {a} := by
      rw [heq]; ext x
      simp only [smul_zero, add_zero, Set.mem_singleton_iff]
      show (∃ n : ℕ, ∃ _ : (n : ℕ∞) < 3, a = x) ↔ x = a
      constructor
      · rintro ⟨n, _, hn⟩; exact hn.symm
      · rintro rfl; exact ⟨0, by norm_num, rfl⟩
    rw [ht1] at hcard
    simp at hcard
  · exact h a d hd (Finset.mem_coe.mp (ht h0)) (Finset.mem_coe.mp (ht h1))
      (Finset.mem_coe.mp (ht h2))

theorem free_of_card_le_two (S : Finset ℕ) (hS : S.card ≤ 2) : Free3 S := by
  intro a d hd ha h1 h2
  have hsub : ({a, a + d, a + 2 * d} : Finset ℕ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have h3 : ({a, a + d, a + 2 * d} : Finset ℕ).card = 3 :=
    Finset.card_eq_three.mpr ⟨a, a + d, a + 2 * d, by omega, by omega, by omega, rfl⟩
  have := Finset.card_le_card hsub
  omega

theorem greedy (S : Finset ℕ) : ∃ G ⊆ S, Free3 G ∧
    ∀ y ∈ S, y ∉ G → ∃ w ∈ G, ∃ z ∈ G, w < z ∧ y + w = 2 * z := by
  induction S using Finset.induction_on_max with
  | empty => exact ⟨∅, Finset.Subset.refl _, fun a d _ ha => by simp at ha, fun y hy => by simp at hy⟩
  | insert x S hlt ih =>
    obtain ⟨G, hGS, hG, hrest⟩ := ih
    have hGlt : ∀ y ∈ G, y < x := fun y hy => hlt y (hGS hy)
    by_cases hfree : Free3 (insert x G)
    · refine ⟨insert x G, Finset.insert_subset_insert x hGS, hfree, ?_⟩
      intro y hy hyG
      rw [Finset.mem_insert] at hy hyG
      push Not at hyG
      rcases hy with rfl | hy
      · exact absurd rfl hyG.1
      · obtain ⟨w, hw, z, hz, hwz, he⟩ := hrest y hy hyG.2
        exact ⟨w, Finset.mem_insert_of_mem hw, z, Finset.mem_insert_of_mem hz, hwz, he⟩
    · refine ⟨G, hGS.trans (Finset.subset_insert x S), hG, ?_⟩
      intro y hy hyG
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · unfold Free3 at hfree
        push Not at hfree
        obtain ⟨a, d, hd, ha, had, ha2d⟩ := hfree
        rw [Finset.mem_insert] at ha had ha2d
        rcases ha with ha | ha
        · rcases had with had | had
          · omega
          · have := hGlt _ had; omega
        rcases had with had | had
        · rcases ha2d with ha2d | ha2d
          · omega
          · have := hGlt _ ha2d; omega
        rcases ha2d with ha2d | ha2d
        · exact ⟨a, ha, a + d, had, by omega, by omega⟩
        · exact absurd (hG a d hd ha had ha2d) id
      · exact hrest y hy hyG

theorem count (G S : Finset ℕ)
    (h : ∀ y ∈ S, ∃ w ∈ G, ∃ z ∈ G, w < z ∧ y + w = 2 * z) :
    2 * S.card ≤ G.card * (G.card - 1) := by
  have h1 : S ⊆ ((G ×ˢ G).filter (fun p : ℕ × ℕ => p.1 < p.2)).image
      (fun p : ℕ × ℕ => 2 * p.2 - p.1) := by
    intro y hy
    obtain ⟨w, hw, z, hz, hwz, he⟩ := h y hy
    rw [Finset.mem_image]
    exact ⟨(w, z), by simp [hw, hz, hwz], by simp only; omega⟩
  have h2 : ((G ×ˢ G).filter (fun p : ℕ × ℕ => p.1 < p.2)).card ≤ (G.powersetCard 2).card := by
    apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => ({p.1, p.2} : Finset ℕ))
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
      simp only [Finset.mem_coe, Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hp.1.1
        · exact hp.1.2
      · exact Finset.card_pair (by omega)
    · intro p hp p' hp' he
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp hp'
      simp only at he
      have e1 : p.1 ∈ ({p'.1, p'.2} : Finset ℕ) := by
        rw [← he]; simp
      have e2 : p.2 ∈ ({p'.1, p'.2} : Finset ℕ) := by
        rw [← he]; simp
      have e3 : p'.1 ∈ ({p.1, p.2} : Finset ℕ) := by
        rw [he]; simp
      have e4 : p'.2 ∈ ({p.1, p.2} : Finset ℕ) := by
        rw [he]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at e1 e2 e3 e4
      exact Prod.ext (by omega) (by omega)
  have h3 := (Finset.card_le_card h1).trans (Finset.card_image_le.trans h2)
  rw [Finset.card_powersetCard, Nat.choose_two_right] at h3
  have := Nat.mul_div_le (G.card * (G.card - 1)) 2
  omega

theorem rounds : ∀ (m : ℕ) (S : Finset ℕ), 2 * S.card ≤ m * (m + 1) →
    ∃ B : Fin m → Finset ℕ, S ⊆ Finset.univ.biUnion B ∧ ∀ i, B i ⊆ S ∧ Free3 (B i) := by
  intro m
  induction m with
  | zero =>
    intro S hS
    have : S = ∅ := Finset.card_eq_zero.mp (by omega)
    subst this
    exact ⟨fun _ => ∅, Finset.empty_subset _, fun i => i.elim0⟩
  | succ m ih =>
    intro S hS
    obtain ⟨G, hGS, hG, hrest⟩ := greedy S
    have hT := Finset.card_sdiff_add_card_eq_card hGS
    have hcnt := count G (S \ G) (fun y hy => by
      rw [Finset.mem_sdiff] at hy
      exact hrest y hy.1 hy.2)
    have hbound : 2 * (S \ G).card ≤ m * (m + 1) := by
      rcases Nat.lt_or_ge m G.card with hk | hk
      · nlinarith
      · calc 2 * (S \ G).card ≤ G.card * (G.card - 1) := hcnt
          _ ≤ m * (m + 1) := Nat.mul_le_mul hk (by omega)
    obtain ⟨B', hcov, hB'⟩ := ih (S \ G) hbound
    refine ⟨(Fin.cons G B' : Fin (m + 1) → Finset ℕ), ?_, ?_⟩
    · intro y hy
      rw [Finset.mem_biUnion]
      by_cases hyG : y ∈ G
      · exact ⟨0, Finset.mem_univ _, by simpa using hyG⟩
      · have hy' : y ∈ S \ G := Finset.mem_sdiff.mpr ⟨hy, hyG⟩
        obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (hcov hy')
        exact ⟨i.succ, Finset.mem_univ _, by simpa using hi⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using ⟨hGS, hG⟩
      · simp only [Fin.cons_succ]
        exact ⟨(hB' j).1.trans Finset.sdiff_subset, (hB' j).2⟩

end E142W

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R1.H3 := by
  intro N S hSN _ hcard
  by_cases hs : S.card ≤ 2
  · refine ⟨1, fun _ => S, ?_, fun _ => ⟨hSN, E142W.bridge S (E142W.free_of_card_le_two S hs)⟩, ?_⟩
    · intro y hy
      exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ _, hy⟩
    · have h1 : S.card ≤ S.card ^ 2 := Nat.le_self_pow two_ne_zero _
      have h2 : 1 ^ 2 * S.card ≤ 4 * N := by omega
      exact_mod_cast h2
  · push Not at hs
    set s := S.card with hsdef
    set a := Nat.sqrt (2 * s) with hadef
    have ha1 : a ^ 2 ≤ 2 * s := Nat.sqrt_le' (2 * s)
    have ha2 : 2 * s < (a + 1) ^ 2 := Nat.lt_succ_sqrt' (2 * s)
    have has : a < s := by
      by_contra hh
      push Not at hh
      nlinarith
    obtain ⟨B, hcov, hB⟩ := E142W.rounds (a + 1) S (by nlinarith)
    refine ⟨a + 1, B, hcov, fun i => ⟨(hB i).1.trans hSN, E142W.bridge _ (hB i).2⟩, ?_⟩
    have hm : (a + 1) ^ 2 ≤ 4 * s := by nlinarith
    have hfin : (a + 1) ^ 2 * s ≤ 4 * N := by nlinarith
    exact_mod_cast hfin
