import OMAStatements.S_oeis_a122536
import Mathlib

/-! OEIS A122536: binary words without an initial repeat; `a n / 2^n` converges to a
positive constant.
Source: https://oeis.org/A122536

Dropping the last letter maps good words of length `n + 1` into good words of length `n`,
so `a (n + 1) ≤ 2 a n` and `a n / 2^n` is antitone. Appending a letter to a good word of
length `n` gives a bad word only if the whole word is a square `w w`, so
`2 a n ≤ a (n + 1) + [n + 1 even] 2^((n+1)/2)`. With `a 4 = 6` this gives
`8 a n ≥ 2^n + 8 · 2^(n - n/2)` for `n ≥ 4`, so the limit is at least `1/8`. -/

namespace OMA.A122536Proof

open OMA.S_oeis_a122536 Filter Topology

def HasSq (s : List Bool) : Prop := ∃ w : List Bool, w ≠ [] ∧ w ++ w <+: s

def Good (n : ℕ) : Set (List Bool) := {s | s.length = n ∧ ¬ HasSq s}

def Sq (L : ℕ) : Set (List Bool) := {t | ∃ w : List Bool, t = w ++ w ∧ w.length + w.length = L}

theorem a_eq (n : ℕ) : a n = (Good n).ncard := rfl

theorem good_finite (n : ℕ) : (Good n).Finite :=
  (List.finite_length_eq Bool n).subset (fun _ hs => hs.1)

theorem len_ncard (m : ℕ) : {w : List Bool | w.length = m}.ncard = 2 ^ m := by
  have h : {w : List Bool | w.length = m} = Set.range (fun v : List.Vector Bool m => v.toList) := by
    ext w
    constructor
    · intro hw
      exact ⟨⟨w, hw⟩, rfl⟩
    · rintro ⟨v, rfl⟩
      exact v.2
  rw [h, Set.ncard_range_of_injective List.Vector.toList_injective, Nat.card_eq_fintype_card,
    card_vector, Fintype.card_bool]

theorem hasSq_append {s : List Bool} (t : List Bool) (h : HasSq s) : HasSq (s ++ t) := by
  obtain ⟨w, hw, hp⟩ := h
  exact ⟨w, hw, hp.trans (List.prefix_append s t)⟩

theorem hasSq_of_prefix {s t : List Bool} (hst : s <+: t) (h : HasSq s) : HasSq t := by
  obtain ⟨w, hw, hp⟩ := h
  exact ⟨w, hw, hp.trans hst⟩

theorem hasSq_iff (s : List Bool) :
    HasSq s ↔ ∃ k ∈ Finset.range (s.length + 1), 0 < k ∧ s.take k ++ s.take k <+: s := by
  constructor
  · rintro ⟨w, hw, hp⟩
    have hw' : w <+: s := (List.prefix_append w w).trans hp
    have hlen := hp.length_le
    simp only [List.length_append] at hlen
    refine ⟨w.length, Finset.mem_range.2 (by omega), List.length_pos_iff.2 hw, ?_⟩
    rw [← List.prefix_iff_eq_take.mp hw']
    exact hp
  · rintro ⟨k, hk, hk0, hp⟩
    rw [Finset.mem_range] at hk
    refine ⟨s.take k, ?_, hp⟩
    intro he
    have := congrArg List.length he
    simp only [List.length_take, List.length_nil] at this
    omega

theorem upper (n : ℕ) : a (n + 1) ≤ 2 * a n := by
  rw [a_eq, a_eq]
  have hsub : Good (n + 1) ⊆
      (fun p : List Bool × Bool => p.1 ++ [p.2]) '' (Good n ×ˢ Set.univ) := by
    intro s hs
    obtain ⟨hlen, hgood⟩ := hs
    have hne : s ≠ [] := by
      intro he
      rw [he] at hlen
      simp at hlen
    refine ⟨(s.dropLast, s.getLast hne), ⟨⟨?_, ?_⟩, Set.mem_univ _⟩, ?_⟩
    · rw [List.length_dropLast, hlen]
      rfl
    · intro h
      exact hgood (hasSq_of_prefix (List.dropLast_prefix s) h)
    · exact List.dropLast_append_getLast hne
  have hfin : ((fun p : List Bool × Bool => p.1 ++ [p.2]) '' (Good n ×ˢ Set.univ)).Finite :=
    ((good_finite n).prod Set.finite_univ).image _
  calc (Good (n + 1)).ncard
      ≤ ((fun p : List Bool × Bool => p.1 ++ [p.2]) '' (Good n ×ˢ Set.univ)).ncard :=
        Set.ncard_le_ncard hsub hfin
    _ ≤ (Good n ×ˢ (Set.univ : Set Bool)).ncard :=
        Set.ncard_image_le ((good_finite n).prod Set.finite_univ)
    _ = 2 * (Good n).ncard := by
        rw [Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_bool, mul_comm]

theorem lower (n : ℕ) : 2 * a n ≤ a (n + 1) + (Sq (n + 1)).ncard := by
  rw [a_eq, a_eq]
  have hinj : Set.InjOn (fun p : List Bool × Bool => p.1 ++ [p.2]) (Good n ×ˢ Set.univ) := by
    intro p _ q _ h
    obtain ⟨h1, h2⟩ := List.append_inj' h rfl
    simp only [List.cons.injEq, and_true] at h2
    exact Prod.ext h1 h2
  have hsub : (fun p : List Bool × Bool => p.1 ++ [p.2]) '' (Good n ×ˢ Set.univ) ⊆
      Good (n + 1) ∪ Sq (n + 1) := by
    rintro t ⟨p, ⟨⟨hlen, hgood⟩, -⟩, rfl⟩
    have htlen : (p.1 ++ [p.2]).length = n + 1 := by simp [hlen]
    by_cases hb : HasSq (p.1 ++ [p.2])
    · right
      obtain ⟨w, hw, hp⟩ := hb
      have hl := hp.length_le
      rw [htlen] at hl
      by_cases hle : (w ++ w).length ≤ n
      · exfalso
        apply hgood
        refine ⟨w, hw, List.prefix_of_prefix_length_le hp (List.prefix_append p.1 [p.2]) ?_⟩
        rw [hlen]
        exact hle
      · refine ⟨w, (hp.eq_of_length (by rw [htlen]; omega)).symm, ?_⟩
        simp only [List.length_append] at hl hle
        omega
    · left
      exact ⟨htlen, hb⟩
  have hfin : (Good (n + 1) ∪ Sq (n + 1)).Finite := by
    refine (good_finite (n + 1)).union ((List.finite_length_eq Bool (n + 1)).subset ?_)
    rintro t ⟨w, rfl, hw⟩
    simp only [Set.mem_ofPred_eq, List.length_append]
    exact hw
  calc 2 * (Good n).ncard = (Good n ×ˢ (Set.univ : Set Bool)).ncard := by
        rw [Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_bool, mul_comm]
    _ = ((fun p : List Bool × Bool => p.1 ++ [p.2]) '' (Good n ×ˢ Set.univ)).ncard :=
        (hinj.ncard_image).symm
    _ ≤ (Good (n + 1) ∪ Sq (n + 1)).ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ (Good (n + 1)).ncard + (Sq (n + 1)).ncard := Set.ncard_union_le _ _

theorem sq_even (m : ℕ) : (Sq (m + m)).ncard ≤ 2 ^ m := by
  have hsub : Sq (m + m) ⊆ (fun w : List Bool => w ++ w) '' {w : List Bool | w.length = m} := by
    rintro t ⟨w, rfl, hw⟩
    exact ⟨w, by simp only [Set.mem_ofPred_eq]; omega, rfl⟩
  calc (Sq (m + m)).ncard
      ≤ ((fun w : List Bool => w ++ w) '' {w : List Bool | w.length = m}).ncard :=
        Set.ncard_le_ncard hsub ((List.finite_length_eq Bool m).image _)
    _ ≤ {w : List Bool | w.length = m}.ncard := Set.ncard_image_le (List.finite_length_eq Bool m)
    _ = 2 ^ m := len_ncard m

theorem sq_odd (m : ℕ) : (Sq (m + m + 1)).ncard = 0 := by
  have : Sq (m + m + 1) = ∅ := by
    ext t
    simp only [Sq, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
    intro w _ hw
    omega
  rw [this, Set.ncard_empty]

theorem a_four : 6 ≤ a 4 := by
  rw [a_eq]
  have hsub : ((({[false, true, false, false], [false, true, true, false],
      [false, true, true, true], [true, false, true, true], [true, false, false, true],
      [true, false, false, false]} : Finset (List Bool)) : Set (List Bool))) ⊆ Good 4 := by
    intro s hs
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨rfl, by rw [hasSq_iff]; decide⟩
  have := Set.ncard_le_ncard hsub (good_finite 4)
  rw [Set.ncard_coe_finset] at this
  exact le_trans (by decide) this

theorem bound : ∀ n : ℕ, 4 ≤ n → 2 ^ n + 8 * 2 ^ (n - n / 2) ≤ 8 * a n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    have := a_four
    norm_num
    omega
  | succ n hn ih =>
    have hl := lower n
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · have h0 := sq_odd m
      have e1 : m + m - (m + m) / 2 = m := by omega
      have e2 : m + m + 1 - (m + m + 1) / 2 = m + 1 := by omega
      rw [e1] at ih
      rw [e2, pow_succ, pow_succ]
      omega
    · have h0 := sq_even (m + 1)
      have e0 : 2 * m + 1 + 1 = (m + 1) + (m + 1) := by omega
      rw [← e0] at h0
      have e1 : 2 * m + 1 - (2 * m + 1) / 2 = m + 1 := by omega
      have e2 : 2 * m + 1 + 1 - (2 * m + 1 + 1) / 2 = m + 1 := by omega
      rw [e1] at ih
      rw [e2]
      have p1 : (2 : ℕ) ^ (2 * m + 1 + 1) = 2 * 2 ^ (2 * m + 1) := by ring
      rw [p1]
      generalize (2 : ℕ) ^ (2 * m + 1) = X at ih ⊢
      generalize (2 : ℕ) ^ (m + 1) = Y at ih h0 ⊢
      omega

end OMA.A122536Proof

open OMA.A122536Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a122536.main := by
  set c : ℕ → ℝ := fun n => (OMA.S_oeis_a122536.a n : ℝ) / 2 ^ n with hc
  have hanti : Antitone c := by
    refine antitone_nat_of_succ_le (fun n => ?_)
    simp only [hc]
    rw [div_le_div_iff₀ (by positivity) (by positivity), pow_succ]
    have := upper n
    have h : ((OMA.S_oeis_a122536.a (n + 1) : ℕ) : ℝ) ≤ 2 * (OMA.S_oeis_a122536.a n : ℝ) := by
      exact_mod_cast this
    nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) n]
  have hbdd : BddBelow (Set.range c) := ⟨0, by rintro _ ⟨n, rfl⟩; simp only [hc]; positivity⟩
  have hge : ∀ n, 4 ≤ n → (1 : ℝ) / 8 ≤ c n := by
    intro n hn
    have h := bound n hn
    have h' : ((2 : ℕ) : ℝ) ^ n ≤ 8 * (OMA.S_oeis_a122536.a n : ℝ) := by
      have : 2 ^ n ≤ 8 * OMA.S_oeis_a122536.a n := le_trans (Nat.le_add_right _ _) h
      exact_mod_cast this
    simp only [hc]
    rw [le_div_iff₀ (by positivity)]
    push_cast at h'
    linarith
  have hall : ∀ n, (1 : ℝ) / 8 ≤ c n := by
    intro n
    by_cases hn : 4 ≤ n
    · exact hge n hn
    · exact le_trans (hge 4 le_rfl) (hanti (by omega))
  refine ⟨⨅ n, c n, ?_, tendsto_atTop_ciInf hanti hbdd⟩
  have : (1 : ℝ) / 8 ≤ ⨅ n, c n := le_ciInf hall
  linarith
