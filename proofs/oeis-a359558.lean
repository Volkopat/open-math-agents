import OMAStatements.S_oeis_a359558
import Mathlib

namespace OMA.S_oeis_a359558.Proof
open Finset OMA.S_oeis_a359558

lemma w_rec (i : ℕ) : weight (i + 2) = weight (i + 1) + weight i := by
  simp only [weight]
  rw [show i + 2 + 2 = (i + 2) + 2 by ring, Nat.fib_add_two]
  ring_nf

lemma w_pos (i : ℕ) : 1 ≤ weight i := Nat.fib_pos.2 (by omega)

lemma w_smono : StrictMono weight := Nat.fib_add_two_strictMono

lemma w_lt {i j : ℕ} (h : i < j) : weight i < weight j := w_smono h

lemma w_le {i j : ℕ} (h : i ≤ j) : weight i ≤ weight j := w_smono.monotone h

lemma w_inj {i j : ℕ} (h : weight i = weight j) : i = j := w_smono.injective h

lemma le_w (i : ℕ) : i ≤ weight i := w_smono.id_le i

/-- number of strictly decreasing index lists of length `j`, entries `< K`, weight sum `m` -/
def cnt : ℕ → ℕ → ℕ → ℕ
  | 0, m, _ => if m = 0 then 1 else 0
  | j + 1, m, K => ∑ t ∈ range K, if weight t ≤ m then cnt j (m - weight t) t else 0

def g (j m t : ℕ) : ℕ := if weight t ≤ m then cnt j (m - weight t) t else 0

lemma cnt_succ (j m K : ℕ) : cnt (j + 1) m K = ∑ t ∈ range K, g j m t := rfl

lemma cnt_big : ∀ j m K, weight (K + 1) ≤ m → cnt j m K = 0
  | 0, m, K, h => by
    have := w_pos (K + 1)
    simp only [cnt]; rw [if_neg]; omega
  | j + 1, m, K, h => by
    rw [cnt_succ]
    apply Finset.sum_eq_zero
    intro t ht
    simp only [mem_range] at ht
    simp only [g]
    split_ifs with h1
    · apply cnt_big
      have := w_rec t
      have := w_le (show t + 2 ≤ K + 1 by omega)
      omega
    · rfl

lemma cnt_zero (j K : ℕ) : cnt (j + 1) 0 K = 0 := by
  rw [cnt_succ]
  apply Finset.sum_eq_zero
  intro t _
  have := w_pos t
  simp only [g]; rw [if_neg (by omega)]

lemma g_ne {j m t : ℕ} (h : g j m t ≠ 0) : weight t ≤ m ∧ m < weight (t + 2) := by
  simp only [g] at h
  split_ifs at h with h1
  · refine ⟨h1, ?_⟩
    by_contra h2
    apply h
    apply cnt_big
    have := w_rec t
    omega
  · exact absurd rfl h

/-- support of the top index -/
lemma tops_close {j m t t' : ℕ} (h : g j m t ≠ 0) (h' : g j m t' ≠ 0) : t' ≤ t + 1 := by
  have a := g_ne h
  have b := g_ne h'
  by_contra hc
  have := w_le (show t + 2 ≤ t' by omega)
  omega

lemma two_tops (j m K : ℕ) : ∃ u, cnt (j + 1) m K ≤ g j m u + g j m (u + 1) := by
  rw [cnt_succ]
  set Sp := (range K).filter (fun t => g j m t ≠ 0) with hSp
  have hsum : ∑ t ∈ range K, g j m t = ∑ t ∈ Sp, g j m t := by
    rw [hSp, Finset.sum_filter_ne_zero]
  rw [hsum]
  rcases Sp.eq_empty_or_nonempty with he | hne
  · exact ⟨0, by rw [he]; simp⟩
  · refine ⟨Sp.min' hne, ?_⟩
    have hmin := Sp.min'_mem hne
    have hsub : Sp ⊆ {Sp.min' hne, Sp.min' hne + 1} := by
      intro t ht
      have h1 := Sp.min'_le t ht
      have h2 : g j m t ≠ 0 := (mem_filter.1 ht).2
      have h3 : g j m (Sp.min' hne) ≠ 0 := (mem_filter.1 hmin).2
      have := tops_close h3 h2
      simp only [mem_insert, mem_singleton]
      omega
    calc ∑ t ∈ Sp, g j m t ≤ ∑ t ∈ ({Sp.min' hne, Sp.min' hne + 1} : Finset ℕ), g j m t :=
          Finset.sum_le_sum_of_subset hsub
      _ = g j m (Sp.min' hne) + g j m (Sp.min' hne + 1) := by
          rw [Finset.sum_pair (by omega)]

lemma one_top (j m K s : ℕ) (h : ∀ t, g j m t ≠ 0 → t = s) : cnt (j + 1) m K ≤ g j m s := by
  rw [cnt_succ, ← Finset.sum_filter_ne_zero]
  calc ∑ t ∈ (range K).filter (fun t => g j m t ≠ 0), g j m t
      ≤ ∑ t ∈ ({s} : Finset ℕ), g j m t := by
        apply Finset.sum_le_sum_of_subset
        intro t ht
        simp only [mem_singleton]
        exact h t (mem_filter.1 ht).2
    _ = g j m s := by simp

/-- if the count is at least two and all terms are at most one, two consecutive tops occur -/
lemma two_of_ge (j m K : ℕ) (hle : ∀ t, g j m t ≤ 1) (h2 : 2 ≤ cnt (j + 1) m K) :
    ∃ t, t + 1 < K ∧ g j m t ≠ 0 ∧ g j m (t + 1) ≠ 0 := by
  rw [cnt_succ, ← Finset.sum_filter_ne_zero] at h2
  set Sp := (range K).filter (fun t => g j m t ≠ 0) with hSp
  have hc : 2 ≤ Sp.card := by
    have : ∑ t ∈ Sp, g j m t ≤ ∑ t ∈ Sp, 1 := Finset.sum_le_sum (fun t _ => hle t)
    simp at this
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (show 1 < Sp.card by omega)
  have ga := (mem_filter.1 ha).2
  have gb := (mem_filter.1 hb).2
  have ra := mem_range.1 (mem_filter.1 ha).1
  have rb := mem_range.1 (mem_filter.1 hb).1
  have h1 := tops_close ga gb
  have h2 := tops_close gb ga
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · exact ⟨a, by omega, ga, by rw [show a + 1 = b by omega]; exact gb⟩
  · exact ⟨b, by omega, gb, by rw [show b + 1 = a by omega]; exact ga⟩

lemma g_le {j B : ℕ} (h : ∀ m K, cnt j m K ≤ B) (m t : ℕ) : g j m t ≤ B := by
  simp only [g]; split_ifs
  · exact h _ _
  · exact Nat.zero_le _

lemma g_ne' {j m t : ℕ} (h : g j m t ≠ 0) :
    weight t ≤ m ∧ cnt j (m - weight t) t ≠ 0 ∧ g j m t = cnt j (m - weight t) t := by
  simp only [g] at h ⊢
  split_ifs at h ⊢ with h1
  · exact ⟨h1, h, rfl⟩
  · exact absurd rfl h

lemma g_zero (m t : ℕ) : g 0 m t = if weight t = m then 1 else 0 := by
  simp only [g, cnt]
  by_cases h : weight t = m
  · simp [h]
  · by_cases h2 : weight t ≤ m
    · rw [if_pos h2, if_neg (by omega), if_neg h]
    · rw [if_neg h2, if_neg h]

lemma cnt1_le (r t : ℕ) : cnt 1 r t ≤ 1 := by
  obtain ⟨u, hu⟩ := two_tops 0 r t
  change cnt 1 r t ≤ _ at hu
  rw [g_zero, g_zero] at hu
  have := w_lt (show u < u + 1 by omega)
  split_ifs at hu <;> omega

lemma cnt_ne {j m K : ℕ} (h : cnt (j + 1) m K ≠ 0) : ∃ t < K, g j m t ≠ 0 := by
  rw [cnt_succ] at h
  obtain ⟨t, ht, h2⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨t, mem_range.1 ht, h2⟩

lemma cnt1_ne {r t : ℕ} (h : cnt 1 r t ≠ 0) : ∃ b < t, weight b = r := by
  obtain ⟨b, hb, h2⟩ := cnt_ne (j := 0) h
  rw [g_zero] at h2
  split_ifs at h2 with h3
  · exact ⟨b, hb, h3⟩
  · exact absurd rfl h2

lemma cnt2_ne {r t : ℕ} (h : cnt 2 r t ≠ 0) : ∃ a < t, ∃ b < a, r = weight a + weight b := by
  obtain ⟨a, ha, h2⟩ := cnt_ne (j := 1) h
  obtain ⟨h3, h4, _⟩ := g_ne' h2
  obtain ⟨b, hb, h5⟩ := cnt1_ne h4
  exact ⟨a, ha, b, hb, by omega⟩

lemma cnt2_le (m K : ℕ) : cnt 2 m K ≤ 1 := by
  obtain ⟨u, hu⟩ := two_tops 1 m K
  change cnt 2 m K ≤ _ at hu
  have e1 := g_le cnt1_le m u
  have e2 := g_le cnt1_le m (u + 1)
  by_contra hc
  have n1 : g 1 m u ≠ 0 := by omega
  have n2 : g 1 m (u + 1) ≠ 0 := by omega
  obtain ⟨h1, h2, _⟩ := g_ne' n1
  obtain ⟨h3, h4, _⟩ := g_ne' n2
  obtain ⟨b, hb, hb'⟩ := cnt1_ne h2
  obtain ⟨a, ha, ha'⟩ := cnt1_ne h4
  obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
  rw [show v + 1 + 1 = v + 2 by ring] at ha'
  have := w_rec v
  have := w_le (show b ≤ v by omega)
  have := w_pos a
  omega

lemma cnt3_le (m K : ℕ) : cnt 3 m K ≤ 2 := by
  obtain ⟨u, hu⟩ := two_tops 2 m K
  change cnt 3 m K ≤ _ at hu
  have e1 := g_le cnt2_le m u
  have e2 := g_le cnt2_le m (u + 1)
  omega

lemma pair_le {c d : ℕ} (h : d < c) : weight c + weight d ≤ weight (c + 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, c = e + 1 := ⟨c - 1, by omega⟩
  rw [show e + 1 + 1 = e + 2 by ring]
  have := w_rec e
  have := w_le (show d ≤ e by omega)
  omega

lemma cnt3_fib (e K : ℕ) : cnt 3 (weight (e + 1)) K ≤ 1 := by
  calc cnt 3 (weight (e + 1)) K ≤ g 2 (weight (e + 1)) e := by
        apply one_top
        intro t ht
        have h := g_ne ht
        have h1 : t ≤ e + 1 := by
          by_contra hc; have := w_lt (show e + 1 < t by omega); omega
        have h2 : e ≤ t := by
          by_contra hc; have := w_le (show t + 2 ≤ e + 1 by omega); omega
        rcases (show t = e ∨ t = e + 1 by omega) with h3 | h3
        · exact h3
        · exfalso; apply ht; rw [h3]; simp only [g, le_refl, if_true, Nat.sub_self]
          exact cnt_zero 1 _
    _ ≤ 1 := g_le cnt2_le _ _

lemma cnt4_le (m K : ℕ) : cnt 4 m K ≤ 3 := by
  obtain ⟨u, hu⟩ := two_tops 3 m K
  change cnt 4 m K ≤ _ at hu
  have e1 := g_le cnt3_le m u
  have e2 := g_le cnt3_le m (u + 1)
  by_contra hc
  have n1 : g 3 m u = 2 := by omega
  have n2 : g 3 m (u + 1) = 2 := by omega
  obtain ⟨h1, -, h1e⟩ := g_ne' (show g 3 m u ≠ 0 by omega)
  have hlt := (g_ne (show g 3 m u ≠ 0 by omega)).2
  obtain ⟨h3, -, h3e⟩ := g_ne' (show g 3 m (u + 1) ≠ 0 by omega)
  rw [h1e] at n1
  rw [h3e] at n2
  set x := m - weight u with hx
  set y := m - weight (u + 1) with hy
  obtain ⟨t, htu, gt1, gt2⟩ := two_of_ge 2 x u (g_le cnt2_le x) (show 2 ≤ cnt 3 x u by omega)
  obtain ⟨v, rfl⟩ : ∃ v, u = v + 2 := ⟨u - 2, by omega⟩
  simp only [show v + 2 + 2 = v + 4 from rfl, show v + 2 + 1 = v + 3 from rfl] at *
  have r1 : weight (v + 3) = weight (v + 2) + weight (v + 1) := w_rec (v + 1)
  have ht : t = v := by
    have := (g_ne gt1).2
    by_contra hc
    have := w_le (show t + 2 ≤ v + 1 by omega)
    omega
  subst ht
  obtain ⟨-, k2, -⟩ := g_ne' gt2
  obtain ⟨a, -, b, -, hab⟩ := cnt2_ne k2
  obtain ⟨-, k1, -⟩ := g_ne' gt1
  obtain ⟨c, hc, d, hd, hcd⟩ := cnt2_ne k1
  have hyx : y = x - weight (t + 1) := by omega
  have hy2 : 2 ≤ y := by have := w_pos a; have := w_pos b; omega
  obtain ⟨z, rfl⟩ : ∃ z, t = z + 2 := ⟨t - 2, by omega⟩
  simp only [show z + 2 + 2 = z + 4 from rfl, show z + 2 + 1 = z + 3 from rfl,
    show z + 2 + 3 = z + 5 from rfl] at *
  have r2 : weight (z + 2) = weight (z + 1) + weight z := w_rec z
  have r3 : weight (z + 3) = weight (z + 2) + weight (z + 1) := w_rec (z + 1)
  have hc' : c = z + 1 := by
    by_contra hne
    have := pair_le hd
    have := w_le (show c + 1 ≤ z + 1 by omega)
    omega
  subst hc'
  have hyd : y = weight d := by omega
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0; simp [weight] at hyd; omega
    · omega⟩
  have key : ∀ K', cnt 3 y K' ≤ 1 := fun K' => by rw [hyd]; exact cnt3_fib e K'
  have k1 := key (z + 5)
  have k2 := key (z + 2 + 2 + 1)
  have k3 := key (z + 2 + 3)
  have k4 := key (z + 4 + 1)
  omega

lemma cnt5_le (m K : ℕ) : cnt 5 m K ≤ 6 := by
  obtain ⟨u, hu⟩ := two_tops 4 m K
  change cnt 5 m K ≤ _ at hu
  have e1 := g_le cnt4_le m u
  have e2 := g_le cnt4_le m (u + 1)
  omega

lemma card_le : ∀ (j m K : ℕ) (s : Finset (List ℕ)),
    (∀ l ∈ s, l.Pairwise (· > ·) ∧ l.length = j ∧ (∀ x ∈ l, x < K) ∧ (l.map weight).sum = m) →
    s.card ≤ cnt j m K
  | 0, m, K, s, hs => by
    have hsub : s ⊆ {[]} := by
      intro l hl
      have := (hs l hl).2.1
      simp only [mem_singleton]
      exact List.eq_nil_of_length_eq_zero this
    by_cases hm : m = 0
    · simp only [cnt, hm, if_true]
      exact (Finset.card_le_card hsub).trans (by simp)
    · simp only [cnt, hm, if_false]
      rw [Nat.le_zero, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro l hl
      have h1 := hsub hl
      simp only [mem_singleton] at h1
      have := (hs l hl).2.2.2
      rw [h1] at this
      simp at this
      exact hm this.symm
  | j + 1, m, K, s, hs => by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun l => l.headD 0) (t := range K)]
    · rw [cnt_succ]
      apply Finset.sum_le_sum
      intro t _
      set F := s.filter (fun l => l.headD 0 = t) with hF
      have hmemF : ∀ l ∈ F, ∃ l', l = t :: l' := by
        intro l hl
        rw [hF, mem_filter] at hl
        obtain ⟨hl1, hl2⟩ := hl
        have hlen := (hs l hl1).2.1
        match l, hlen, hl2 with
        | x :: l', _, h2 => exact ⟨l', by simp at h2; rw [h2]⟩
      simp only [g]
      split_ifs with hw
      · rw [← Finset.card_image_of_injOn (f := List.tail)]
        · apply card_le j (m - weight t) t
          intro l' hl'
          rw [mem_image] at hl'
          obtain ⟨l, hl, rfl⟩ := hl'
          obtain ⟨l', rfl⟩ := hmemF l hl
          have := hs _ (mem_filter.1 hl).1
          obtain ⟨hp, hlen, _, hsum⟩ := this
          rw [List.pairwise_cons] at hp
          simp only [List.tail_cons]
          refine ⟨hp.2, by simpa using hlen, fun x hx => hp.1 x hx, ?_⟩
          simp only [List.map_cons, List.sum_cons] at hsum
          omega
        · intro l1 h1 l2 h2 he
          obtain ⟨l1', rfl⟩ := hmemF l1 h1
          obtain ⟨l2', rfl⟩ := hmemF l2 h2
          simp only [List.tail_cons] at he
          rw [he]
      · rw [Nat.le_zero, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro l hl
        obtain ⟨l', rfl⟩ := hmemF l hl
        have := (hs _ (mem_filter.1 hl).1).2.2.2
        simp only [List.map_cons, List.sum_cons] at this
        omega
    · intro l hl
      obtain ⟨hp, hlen, hK, _⟩ := hs l hl
      match l, hlen, hK with
      | x :: l', _, hK' => simpa using hK' x (by simp)

theorem solution_main : type_of% @OMA.S_oeis_a359558.main := by
  intro n s hs
  calc s.card ≤ cnt 5 n (n + 1) := by
        apply card_le 5 n (n + 1) s
        intro l hl
        obtain ⟨hp, hlen, hsum⟩ := hs l hl
        refine ⟨hp, hlen, fun x hx => ?_, hsum⟩
        have h1 : weight x ≤ (l.map weight).sum :=
          List.le_sum_of_mem (List.mem_map_of_mem hx)
        have := le_w x
        omega
    _ ≤ 6 := cnt5_le n (n + 1)

end OMA.S_oeis_a359558.Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a359558.main := OMA.S_oeis_a359558.Proof.solution_main
