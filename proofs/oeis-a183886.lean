import OMAStatements.S_oeis_a183886
import Mathlib

/-!
# OEIS A183886: words in four residues

We prove Kotesovec's closed formula for `a n` (`n >= 2`), Barker's generating
function identity, and Barker's order-7 linear recurrence (`n > 8`).

A word `w : Fin N -> Fin 4` is `Valid` iff its residue multiplicity tuple
`(c0, c1, c2, c3)` satisfies `ValidCounts`, which depends only on the capped
counts `min c_r 4`. For `N >= 5`, the invalid count tuples partition into
three disjoint families:
1. `c1 + c3 = 1` (`N * 2^N` words),
2. `c0 + c2 = 1` (`N * 2^N` words),
3. 22 explicit sparse patterns contributing `2 + 2*N + 12*(N.choose 2) + 28*(N.choose 3)` words.

Subtracting from `4^N` yields the exact closed form for `n >= 2`. Combined with
`a 0 = 0` and `a 1 = 16` (from the 5 valid count tuples at `N = 4`), expanding
the denominator polynomial yields both the generating function and the recurrence.
-/

namespace OMA.A183886Proof

open Finset OMA.S_oeis_a183886

section CountCharacterization

def cnt {N : ℕ} (w : Fin N → Fin 4) (r : Fin 4) : ℕ :=
  (univ.filter (fun i : Fin N => w i = r)).card

lemma cnt_sum {N : ℕ} (w : Fin N → Fin 4) :
    cnt w 0 + cnt w 1 + cnt w 2 + cnt w 3 = N := by
  have h : (univ : Finset (Fin N)).card =
      ∑ r : Fin 4, (univ.filter (fun i : Fin N => w i = r)).card :=
    Finset.card_eq_sum_card_fiberwise (f := w) (s := univ) (t := univ) (fun _ _ => mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin, Fin.sum_univ_four] at h
  exact h.symm

def need (r a b d k : Fin 4) : ℕ :=
  (if r = k then 1 else 0) + (if a = k then 1 else 0) +
  (if b = k then 1 else 0) + (if d = k then 1 else 0)

lemma need_le_four (r a b d k : Fin 4) : need r a b d k ≤ 4 := by
  unfold need
  split_ifs <;> omega

lemma fin4_sum_mod (r a b d : Fin 4) :
    (a.val + b.val + d.val) % 4 = r.val ↔ d = r - a - b := by
  fin_cases r <;> fin_cases a <;> fin_cases b <;> fin_cases d <;> decide

def ValidCounts (c : Fin 4 → ℕ) : Prop :=
  ∀ r : Fin 4, 0 < c r →
    ∃ a b : Fin 4, ∀ k : Fin 4, need r a b (r - a - b) k ≤ c k

instance (c : Fin 4 → ℕ) : Decidable (ValidCounts c) := by
  unfold ValidCounts
  infer_instance

def mk4 (c0 c1 c2 c3 : ℕ) : Fin 4 → ℕ
  | 0 => c0
  | 1 => c1
  | 2 => c2
  | 3 => c3

lemma cnt_eq_mk4 {N : ℕ} (w : Fin N → Fin 4) :
    cnt w = mk4 (cnt w 0) (cnt w 1) (cnt w 2) (cnt w 3) := by
  funext k
  fin_cases k <;> rfl

private lemma exists_mem_filter_notMem {N : ℕ} (w : Fin N → Fin 4) (S : Finset (Fin N)) (k : Fin 4)
    (h : (S.filter (fun j => w j = k)).card < cnt w k) :
    ∃ x : Fin N, w x = k ∧ x ∉ S := by
  have hlt : (S.filter (fun j => w j = k)).card < (univ.filter (fun j => w j = k)).card := h
  obtain ⟨x, hx1, hx2⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hwk : w x = k := (mem_filter.mp hx1).2
  exact ⟨x, hwk, fun hxS => hx2 (mem_filter.mpr ⟨hxS, hwk⟩)⟩

lemma valid_iff_validCounts {N : ℕ} (w : Fin N → Fin 4) :
    Valid w ↔ ValidCounts (cnt w) := by
  constructor
  · intro hw r hr
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hr
    have hwi : w i = r := (mem_filter.mp hi).2
    obtain ⟨t, ht3, hit, hsum⟩ := hw i
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp ht3
    have hix : i ≠ x := fun h => hit (by simp [h])
    have hiy : i ≠ y := fun h => hit (by simp [h])
    have hiz : i ≠ z := fun h => hit (by simp [h])
    have hsum' : ((w x).val + (w y).val + (w z).val) % 4 = r.val := by
      have h1 : ∑ j ∈ ({x, y, z} : Finset (Fin N)), (w j).val =
          (w x).val + (w y).val + (w z).val := by
        rw [Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_insert (by simp [hyz]),
          Finset.sum_singleton, add_assoc]
      rw [h1, hwi] at hsum
      exact hsum
    have hwz : w z = r - w x - w y := (fin4_sum_mod r (w x) (w y) (w z)).mp hsum'
    refine ⟨w x, w y, fun k => ?_⟩
    have hsub : ({i, x, y, z} : Finset (Fin N)).filter (fun j => w j = k) ⊆
        univ.filter (fun j => w j = k) :=
      filter_subset_filter _ (subset_univ _)
    have hcard : (({i, x, y, z} : Finset (Fin N)).filter (fun j => w j = k)).card =
        need r (w x) (w y) (r - w x - w y) k := by
      rw [Finset.card_filter,
        Finset.sum_insert (by simp [hix, hiy, hiz]),
        Finset.sum_insert (by simp [hxy, hxz]),
        Finset.sum_insert (by simp [hyz]),
        Finset.sum_singleton, hwi, hwz]
      unfold need
      omega
    rw [← hcard]
    exact Finset.card_le_card hsub
  · intro hvc i
    set r := w i
    have hr : 0 < cnt w r := Finset.card_pos.mpr ⟨i, by simp [r]⟩
    obtain ⟨a, b, hneed⟩ := hvc r hr
    set d := r - a - b
    have hlt1 : (({i} : Finset (Fin N)).filter (fun j => w j = a)).card < cnt w a := by
      have hle := hneed a
      rw [Finset.card_filter, Finset.sum_singleton]
      unfold need at hle
      change (if r = a then 1 else 0) < cnt w a
      split_ifs at hle ⊢ <;> omega
    obtain ⟨x, hwx, hxS⟩ := exists_mem_filter_notMem w {i} a hlt1
    have hxi : x ≠ i := by simpa using hxS
    have hix : i ≠ x := hxi.symm
    have hlt2 : (({i, x} : Finset (Fin N)).filter (fun j => w j = b)).card < cnt w b := by
      have hle := hneed b
      rw [Finset.card_filter, Finset.sum_insert (by simp [hix]), Finset.sum_singleton, hwx]
      unfold need at hle
      change (if r = b then 1 else 0) + (if a = b then 1 else 0) < cnt w b
      split_ifs at hle ⊢ <;> omega
    obtain ⟨y, hwy, hyS⟩ := exists_mem_filter_notMem w {i, x} b hlt2
    have hyi : y ≠ i := fun h => hyS (by simp [h])
    have hyx : y ≠ x := fun h => hyS (by simp [h])
    have hiy : i ≠ y := hyi.symm
    have hxy : x ≠ y := hyx.symm
    have hlt3 : (({i, x, y} : Finset (Fin N)).filter (fun j => w j = d)).card < cnt w d := by
      have hle := hneed d
      rw [Finset.card_filter, Finset.sum_insert (by simp [hix, hiy]),
        Finset.sum_insert (by simp [hxy]), Finset.sum_singleton, hwx, hwy]
      unfold need at hle
      change (if r = d then 1 else 0) + ((if a = d then 1 else 0) + (if b = d then 1 else 0)) <
        cnt w d
      split_ifs at hle ⊢ <;> omega
    obtain ⟨z, hwz, hzS⟩ := exists_mem_filter_notMem w {i, x, y} d hlt3
    have hzi : z ≠ i := fun h => hzS (by simp [h])
    have hzx : z ≠ x := fun h => hzS (by simp [h])
    have hzy : z ≠ y := fun h => hzS (by simp [h])
    refine ⟨{x, y, z}, ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem (by simp [hxy, hzx.symm]),
        Finset.card_insert_of_notMem (by simp [hzy.symm]), Finset.card_singleton]
    · simp [hix, hiy, hzi.symm]
    · rw [Finset.sum_insert (by simp [hxy, hzx.symm]),
        Finset.sum_insert (by simp [hzy.symm]), Finset.sum_singleton, hwx, hwy, hwz, ← add_assoc]
      exact (fin4_sum_mod r a b d).mpr rfl

lemma validCounts_cap (c0 c1 c2 c3 : ℕ) :
    ValidCounts (mk4 c0 c1 c2 c3) ↔
      ValidCounts (mk4 (min c0 4) (min c1 4) (min c2 4) (min c3 4)) := by
  have hpos : ∀ r : Fin 4, 0 < mk4 c0 c1 c2 c3 r ↔
      0 < mk4 (min c0 4) (min c1 4) (min c2 4) (min c3 4) r := by
    intro r; fin_cases r <;> simp [mk4]
  have hle : ∀ r a b k : Fin 4, need r a b (r - a - b) k ≤ mk4 c0 c1 c2 c3 k ↔
      need r a b (r - a - b) k ≤ mk4 (min c0 4) (min c1 4) (min c2 4) (min c3 4) k := by
    intro r a b k
    have h4 := need_le_four r a b (r - a - b) k
    fin_cases k <;> simp only [mk4] at h4 ⊢ <;> omega
  constructor <;> intro h r hr
  · obtain ⟨a, b, hab⟩ := h r ((hpos r).mpr hr)
    exact ⟨a, b, fun k => (hle r a b k).mp (hab k)⟩
  · obtain ⟨a, b, hab⟩ := h r ((hpos r).mp hr)
    exact ⟨a, b, fun k => (hle r a b k).mpr (hab k)⟩

end CountCharacterization

section Classification

def fam3List (N : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  [ (N - 1, 0, 1, 0), (N - 2, 1, 0, 1), (N - 3, 1, 0, 2), (N - 3, 1, 1, 1), (N - 3, 2, 0, 1),
    (0, N, 0, 0), (0, N - 2, 2, 0), (0, N - 3, 3, 0), (1, N - 2, 1, 0), (2, N - 2, 0, 0),
    (3, N - 3, 0, 0),
    (0, 1, N - 2, 1), (0, 1, N - 3, 2), (0, 2, N - 3, 1), (1, 0, N - 1, 0), (1, 1, N - 3, 1),
    (0, 0, 0, N), (0, 0, 2, N - 2), (0, 0, 3, N - 3), (1, 0, 1, N - 2), (2, 0, 0, N - 2),
    (3, 0, 0, N - 3) ]

def fam3Cap : List (ℕ × ℕ × ℕ × ℕ) :=
  [ (4, 0, 1, 0), (4, 1, 0, 1), (4, 1, 0, 2), (4, 1, 1, 1), (4, 2, 0, 1),
    (0, 4, 0, 0), (0, 4, 2, 0), (0, 4, 3, 0), (1, 4, 1, 0), (2, 4, 0, 0), (3, 4, 0, 0),
    (0, 1, 4, 1), (0, 1, 4, 2), (0, 2, 4, 1), (1, 0, 4, 0), (1, 1, 4, 1),
    (0, 0, 0, 4), (0, 0, 2, 4), (0, 0, 3, 4), (1, 0, 1, 4), (2, 0, 0, 4), (3, 0, 0, 4) ]

private lemma classify_N5_fin :
    ∀ c0 c1 c2 c3 : Fin 6, c0.val + c1.val + c2.val + c3.val = 5 →
      (¬ ValidCounts (mk4 c0.val c1.val c2.val c3.val) ↔
        c1.val + c3.val = 1 ∨ c0.val + c2.val = 1 ∨
        (c0.val, c1.val, c2.val, c3.val) ∈ fam3List 5) := by
  decide

private lemma classify_N6_fin :
    ∀ c0 c1 c2 c3 : Fin 7, c0.val + c1.val + c2.val + c3.val = 6 →
      (¬ ValidCounts (mk4 c0.val c1.val c2.val c3.val) ↔
        c1.val + c3.val = 1 ∨ c0.val + c2.val = 1 ∨
        (c0.val, c1.val, c2.val, c3.val) ∈ fam3List 6) := by
  decide

private lemma classify_cap_fin :
    ∀ a0 a1 a2 a3 : Fin 5,
      (a0.val = 4 ∨ a1.val = 4 ∨ a2.val = 4 ∨ a3.val = 4 ∨
        7 ≤ a0.val + a1.val + a2.val + a3.val) →
      (¬ ValidCounts (mk4 a0.val a1.val a2.val a3.val) ↔
        a1.val + a3.val = 1 ∨ a0.val + a2.val = 1 ∨
        (a0.val, a1.val, a2.val, a3.val) ∈ fam3Cap) := by
  decide

private lemma mem_fam3List_iff_cap {N c0 c1 c2 c3 : ℕ} (hN : 7 ≤ N)
    (hsum : c0 + c1 + c2 + c3 = N) :
    (c0, c1, c2, c3) ∈ fam3List N ↔
      (min c0 4, min c1 4, min c2 4, min c3 4) ∈ fam3Cap := by
  simp only [fam3List, fam3Cap, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
  repeat' first | (refine or_congr ?_ ?_; omega) | omega

lemma classify_invalid {N c0 c1 c2 c3 : ℕ} (hN : 5 ≤ N) (hsum : c0 + c1 + c2 + c3 = N) :
    ¬ ValidCounts (mk4 c0 c1 c2 c3) ↔
      c1 + c3 = 1 ∨ c0 + c2 = 1 ∨ (c0, c1, c2, c3) ∈ fam3List N := by
  by_cases h5 : N = 5
  · subst h5
    exact classify_N5_fin ⟨c0, by omega⟩ ⟨c1, by omega⟩ ⟨c2, by omega⟩ ⟨c3, by omega⟩ hsum
  · by_cases h6 : N = 6
    · subst h6
      exact classify_N6_fin ⟨c0, by omega⟩ ⟨c1, by omega⟩ ⟨c2, by omega⟩ ⟨c3, by omega⟩ hsum
    · have h7 : 7 ≤ N := by omega
      rw [validCounts_cap]
      have hcap : min c0 4 = 4 ∨ min c1 4 = 4 ∨ min c2 4 = 4 ∨ min c3 4 = 4 ∨
          7 ≤ min c0 4 + min c1 4 + min c2 4 + min c3 4 := by omega
      have hfin := classify_cap_fin ⟨min c0 4, by omega⟩ ⟨min c1 4, by omega⟩
        ⟨min c2 4, by omega⟩ ⟨min c3 4, by omega⟩ hcap
      rw [hfin, ← mem_fam3List_iff_cap h7 hsum]
      have h13 : min c1 4 + min c3 4 = 1 ↔ c1 + c3 = 1 := by omega
      have h02 : min c0 4 + min c2 4 = 1 ↔ c0 + c2 = 1 := by omega
      rw [h13, h02]

lemma fam3List_nodup {N : ℕ} (hN : 5 ≤ N) : (fam3List N).Nodup := by
  simp only [fam3List, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq, List.nodup_nil, and_true, not_or, not_false_eq_true]
  repeat' first | (refine ⟨?_, ?_⟩) | omega

lemma fam3List_disjoint_fam12 {N c0 c1 c2 c3 : ℕ} (hN : 5 ≤ N)
    (hmem : (c0, c1, c2, c3) ∈ fam3List N) :
    c1 + c3 ≠ 1 ∧ c0 + c2 ≠ 1 := by
  simp only [fam3List, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega

lemma valid_N4_fin :
    ∀ c0 c1 c2 c3 : Fin 5, c0.val + c1.val + c2.val + c3.val = 4 →
      (ValidCounts (mk4 c0.val c1.val c2.val c3.val) ↔
        (c0.val, c1.val, c2.val, c3.val) ∈
          [(0, 0, 4, 0), (0, 1, 0, 3), (0, 3, 0, 1), (2, 0, 2, 0), (4, 0, 0, 0)]) := by
  decide

end Classification

section Counting

def fiber (N c0 c1 c2 c3 : ℕ) : Finset (Fin N → Fin 4) :=
  univ.filter (fun w => cnt w 0 = c0 ∧ cnt w 1 = c1 ∧ cnt w 2 = c2 ∧ cnt w 3 = c3)

lemma card_fiber {N c0 c1 c2 c3 : ℕ} (hsum : c0 + c1 + c2 + c3 = N) :
    (fiber N c0 c1 c2 c3).card =
      N.choose c0 * (N - c0).choose c1 * (N - c0 - c1).choose c2 := by
  let T : Finset (Σ _ : Finset (Fin N), Σ _ : Finset (Fin N), Finset (Fin N)) :=
    (univ.powersetCard c0).sigma fun S0 =>
      ((univ \ S0).powersetCard c1).sigma fun S1 =>
        (((univ \ S0) \ S1).powersetCard c2)
  have hTcard : T.card = N.choose c0 * (N - c0).choose c1 * (N - c0 - c1).choose c2 := by
    simp only [T, Finset.card_sigma]
    have hinner : ∀ S0 ∈ (univ : Finset (Fin N)).powersetCard c0,
        ∑ S1 ∈ (univ \ S0).powersetCard c1, (((univ \ S0) \ S1).powersetCard c2).card =
          (N - c0).choose c1 * (N - c0 - c1).choose c2 := by
      intro S0 hS0
      rw [mem_powersetCard] at hS0
      have hS0card : (univ \ S0).card = N - c0 := by
        have h1 := Finset.card_sdiff_add_card_eq_card (subset_univ S0)
        rw [Finset.card_univ, Fintype.card_fin, hS0.2] at h1
        omega
      have hinner2 : ∀ S1 ∈ (univ \ S0).powersetCard c1,
          (((univ \ S0) \ S1).powersetCard c2).card = (N - c0 - c1).choose c2 := by
        intro S1 hS1
        rw [mem_powersetCard] at hS1
        rw [Finset.card_powersetCard]
        have hS1card : ((univ \ S0) \ S1).card = N - c0 - c1 := by
          have h1 := Finset.card_sdiff_add_card_eq_card hS1.1
          rw [hS0card, hS1.2] at h1
          omega
        rw [hS1card]
      rw [Finset.sum_congr rfl hinner2, Finset.sum_const, Finset.card_powersetCard, hS0card,
        smul_eq_mul]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_assoc]
  rw [← hTcard]
  symm
  refine Finset.card_bij
    (fun t _ => fun i : Fin N =>
      if i ∈ t.1 then (0 : Fin 4)
      else if i ∈ t.2.1 then 1
      else if i ∈ t.2.2 then 2
      else 3) ?_ ?_ ?_
  · rintro ⟨S0, S1, S2⟩ ht
    simp only [T, mem_sigma, mem_powersetCard] at ht
    rcases ht with ⟨⟨_, hS0c⟩, ⟨hS1sub, hS1c⟩, ⟨hS2sub, hS2c⟩⟩
    have hdisj01 : ∀ i, i ∈ S1 → i ∉ S0 := fun i hi => (mem_sdiff.mp (hS1sub hi)).2
    have hdisj02 : ∀ i, i ∈ S2 → i ∉ S0 := fun i hi =>
      (mem_sdiff.mp (mem_sdiff.mp (hS2sub hi)).1).2
    have hdisj12 : ∀ i, i ∈ S2 → i ∉ S1 := fun i hi => (mem_sdiff.mp (hS2sub hi)).2
    set w : Fin N → Fin 4 := fun i =>
      if i ∈ S0 then 0 else if i ∈ S1 then 1 else if i ∈ S2 then 2 else 3
    have hf0 : univ.filter (fun i => w i = 0) = S0 := by
      ext i; simp only [mem_filter, mem_univ, true_and, w]
      split_ifs <;> simp_all
    have hf1 : univ.filter (fun i => w i = 1) = S1 := by
      ext i; simp only [mem_filter, mem_univ, true_and, w]
      by_cases h0 : i ∈ S0
      · simp [h0]; exact fun h1 => hdisj01 i h1 h0
      · by_cases h1 : i ∈ S1
        · simp [h0, h1]
        · simp [h0, h1]; split_ifs <;> decide
    have hf2 : univ.filter (fun i => w i = 2) = S2 := by
      ext i; simp only [mem_filter, mem_univ, true_and, w]
      by_cases h0 : i ∈ S0
      · simp [h0]; exact fun h2 => hdisj02 i h2 h0
      · by_cases h1 : i ∈ S1
        · simp [h0, h1]; exact fun h2 => hdisj12 i h2 h1
        · by_cases h2 : i ∈ S2
          · simp [h0, h1, h2]
          · simp [h0, h1, h2]
    have hc0 : cnt w 0 = c0 := by unfold cnt; rw [hf0, hS0c]
    have hc1 : cnt w 1 = c1 := by unfold cnt; rw [hf1, hS1c]
    have hc2 : cnt w 2 = c2 := by unfold cnt; rw [hf2, hS2c]
    have hc3 : cnt w 3 = c3 := by have := cnt_sum w; omega
    simp only [fiber, mem_filter, mem_univ, true_and]
    exact ⟨hc0, hc1, hc2, hc3⟩
  · rintro ⟨S0, S1, S2⟩ ht1 ⟨T0, T1, T2⟩ ht2 heq
    simp only [T, mem_sigma, mem_powersetCard] at ht1 ht2
    rcases ht1 with ⟨_, ⟨hS1sub, _⟩, ⟨hS2sub, _⟩⟩
    rcases ht2 with ⟨_, ⟨hT1sub, _⟩, ⟨hT2sub, _⟩⟩
    have h0 : S0 = T0 := by
      ext i
      have hi := congrFun heq i
      by_cases hS : i ∈ S0 <;> by_cases hT : i ∈ T0 <;> simp_all
      · split_ifs at hi <;> cases hi
      · split_ifs at hi <;> cases hi
    subst h0
    have h1 : S1 = T1 := by
      ext i
      have hi := congrFun heq i
      by_cases hS : i ∈ S1 <;> by_cases hT : i ∈ T1
      · simp [hS, hT]
      · have h0 : i ∉ S0 := (mem_sdiff.mp (hS1sub hS)).2
        simp [h0, hS, hT] at hi
        split_ifs at hi <;> cases hi
      · have h0 : i ∉ S0 := (mem_sdiff.mp (hT1sub hT)).2
        simp [h0, hS, hT] at hi
        split_ifs at hi <;> cases hi
      · simp [hS, hT]
    subst h1
    have h2 : S2 = T2 := by
      ext i
      have hi := congrFun heq i
      by_cases hS : i ∈ S2 <;> by_cases hT : i ∈ T2
      · simp [hS, hT]
      · have h0 : i ∉ S0 := (mem_sdiff.mp (mem_sdiff.mp (hS2sub hS)).1).2
        have h1 : i ∉ S1 := (mem_sdiff.mp (hS2sub hS)).2
        simp [h0, h1, hS, hT] at hi
      · have h0 : i ∉ S0 := (mem_sdiff.mp (mem_sdiff.mp (hT2sub hT)).1).2
        have h1 : i ∉ S1 := (mem_sdiff.mp (hT2sub hT)).2
        simp [h0, h1, hS, hT] at hi
      · simp [hS, hT]
    subst h2
    rfl
  · intro w hw
    simp only [fiber, mem_filter, mem_univ, true_and] at hw
    let S0 := univ.filter (fun i : Fin N => w i = 0)
    let S1 := univ.filter (fun i : Fin N => w i = 1)
    let S2 := univ.filter (fun i : Fin N => w i = 2)
    refine ⟨⟨S0, S1, S2⟩, ?_, ?_⟩
    · simp only [T, mem_sigma, mem_powersetCard]
      refine ⟨⟨subset_univ _, hw.1⟩, ⟨?_, hw.2.1⟩, ⟨?_, hw.2.2.1⟩⟩
      · intro i hi
        simp only [S1, S0, mem_sdiff, mem_univ, true_and, mem_filter] at hi ⊢
        rw [hi]; decide
      · intro i hi
        simp only [S2, S1, S0, mem_sdiff, mem_univ, true_and, mem_filter] at hi ⊢
        rw [hi]; exact ⟨by decide, by decide⟩
    · funext i
      simp only [S0, S1, S2, mem_filter, mem_univ, true_and]
      have hi := w i
      generalize hw_eq : w i = r
      fin_cases r <;> simp

def fam1Set (N : ℕ) : Finset (Fin N → Fin 4) :=
  univ.filter (fun w => cnt w 1 + cnt w 3 = 1)

def fam2Set (N : ℕ) : Finset (Fin N → Fin 4) :=
  univ.filter (fun w => cnt w 0 + cnt w 2 = 1)

lemma card_fam1Set (N : ℕ) : (fam1Set N).card = N * 2 ^ N := by
  have hcard : (univ : Finset (Fin N × (Fin N → Bool))).card = N * 2 ^ N := by
    simp [Fintype.card_prod, Fintype.card_pi, Fintype.card_bool]
  rw [← hcard]
  symm
  refine Finset.card_bij
    (fun p _ => fun j : Fin N =>
      if j = p.1 then (if p.2 j then 1 else 3) else (if p.2 j then 0 else 2)) ?_ ?_ ?_
  · rintro ⟨i, b⟩ _
    set w : Fin N → Fin 4 := fun j =>
      if j = i then (if b j then 1 else 3) else (if b j then 0 else 2)
    have h13 : (univ.filter (fun j => w j = 1)) ∪ (univ.filter (fun j => w j = 3)) = {i} := by
      ext j
      simp only [mem_union, mem_filter, mem_univ, true_and, mem_singleton, w]
      by_cases hj : j = i
      · subst hj; cases b j <;> simp
      · simp only [hj, ↓reduceIte, iff_false, not_or]
        cases b j <;> decide
    have hdisj : Disjoint (univ.filter (fun j => w j = 1)) (univ.filter (fun j => w j = 3)) := by
      rw [Finset.disjoint_left]
      intro j h1 h3
      simp only [mem_filter, mem_univ, true_and] at h1 h3
      rw [h1] at h3; cases h3
    simp only [fam1Set, mem_filter, mem_univ, true_and]
    unfold cnt
    rw [← Finset.card_union_of_disjoint hdisj, h13, Finset.card_singleton]
  · rintro ⟨i1, b1⟩ _ ⟨i2, b2⟩ _ heq
    have hi : i1 = i2 := by
      by_contra hne
      have h := congrFun heq i1
      dsimp only at h
      simp only [↓reduceIte, hne] at h
      cases h1 : b1 i1 <;> cases h2 : b2 i1 <;> simp [h1, h2] at h
    subst hi
    have hb : b1 = b2 := by
      funext j
      have h := congrFun heq j
      by_cases hj : j = i1
      · subst hj; cases h1 : b1 j <;> cases h2 : b2 j <;> simp_all
      · cases h1 : b1 j <;> cases h2 : b2 j <;> simp_all
    subst hb; rfl
  · intro w hw
    simp only [fam1Set, mem_filter, mem_univ, true_and] at hw
    unfold cnt at hw
    have hdisj : Disjoint (univ.filter (fun j => w j = 1)) (univ.filter (fun j => w j = 3)) := by
      rw [Finset.disjoint_left]
      intro j h1 h3
      simp only [mem_filter, mem_univ, true_and] at h1 h3
      rw [h1] at h3; cases h3
    have hcard1 : ((univ.filter (fun j => w j = 1)) ∪ (univ.filter (fun j => w j = 3))).card = 1 := by
      rw [Finset.card_union_of_disjoint hdisj, hw]
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard1
    refine ⟨(i, fun j => decide (w j = 0 ∨ w j = 1)), mem_univ _, ?_⟩
    funext j
    have hmem : ∀ x, (w x = 1 ∨ w x = 3) ↔ x = i := by
      intro x
      have hx := Finset.ext_iff.mp hi x
      simpa [mem_union, mem_filter, mem_singleton] using hx
    by_cases hj : j = i
    · subst hj
      have hwi : w j = 1 ∨ w j = 3 := (hmem j).mpr rfl
      rcases hwi with h | h <;> simp [h]
    · have hne : ¬ (w j = 1 ∨ w j = 3) := fun h => hj ((hmem j).mp h)
      generalize hr : w j = r at hne ⊢
      fin_cases r <;> simp_all

lemma card_fam2Set (N : ℕ) : (fam2Set N).card = N * 2 ^ N := by
  have hcard : (univ : Finset (Fin N × (Fin N → Bool))).card = N * 2 ^ N := by
    simp [Fintype.card_prod, Fintype.card_pi, Fintype.card_bool]
  rw [← hcard]
  symm
  refine Finset.card_bij
    (fun p _ => fun j : Fin N =>
      if j = p.1 then (if p.2 j then 0 else 2) else (if p.2 j then 1 else 3)) ?_ ?_ ?_
  · rintro ⟨i, b⟩ _
    set w : Fin N → Fin 4 := fun j =>
      if j = i then (if b j then 0 else 2) else (if b j then 1 else 3)
    have h02 : (univ.filter (fun j => w j = 0)) ∪ (univ.filter (fun j => w j = 2)) = {i} := by
      ext j
      simp only [mem_union, mem_filter, mem_univ, true_and, mem_singleton, w]
      by_cases hj : j = i
      · subst hj; cases b j <;> simp
      · simp only [hj, ↓reduceIte, iff_false, not_or]
        cases b j <;> decide
    have hdisj : Disjoint (univ.filter (fun j => w j = 0)) (univ.filter (fun j => w j = 2)) := by
      rw [Finset.disjoint_left]
      intro j h0 h2
      simp only [mem_filter, mem_univ, true_and] at h0 h2
      rw [h0] at h2; cases h2
    simp only [fam2Set, mem_filter, mem_univ, true_and]
    unfold cnt
    rw [← Finset.card_union_of_disjoint hdisj, h02, Finset.card_singleton]
  · rintro ⟨i1, b1⟩ _ ⟨i2, b2⟩ _ heq
    have hi : i1 = i2 := by
      by_contra hne
      have h := congrFun heq i1
      dsimp only at h
      simp only [↓reduceIte, hne] at h
      cases h1 : b1 i1 <;> cases h2 : b2 i1 <;> simp [h1, h2] at h
    subst hi
    have hb : b1 = b2 := by
      funext j
      have h := congrFun heq j
      by_cases hj : j = i1
      · subst hj; cases h1 : b1 j <;> cases h2 : b2 j <;> simp_all
      · cases h1 : b1 j <;> cases h2 : b2 j <;> simp_all
    subst hb; rfl
  · intro w hw
    simp only [fam2Set, mem_filter, mem_univ, true_and] at hw
    unfold cnt at hw
    have hdisj : Disjoint (univ.filter (fun j => w j = 0)) (univ.filter (fun j => w j = 2)) := by
      rw [Finset.disjoint_left]
      intro j h0 h2
      simp only [mem_filter, mem_univ, true_and] at h0 h2
      rw [h0] at h2; cases h2
    have hcard1 : ((univ.filter (fun j => w j = 0)) ∪ (univ.filter (fun j => w j = 2))).card = 1 := by
      rw [Finset.card_union_of_disjoint hdisj, hw]
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard1
    refine ⟨(i, fun j => decide (w j = 0 ∨ w j = 1)), mem_univ _, ?_⟩
    funext j
    have hmem : ∀ x, (w x = 0 ∨ w x = 2) ↔ x = i := by
      intro x
      have hx := Finset.ext_iff.mp hi x
      simpa [mem_union, mem_filter, mem_singleton] using hx
    by_cases hj : j = i
    · subst hj
      have hwi : w j = 0 ∨ w j = 2 := (hmem j).mpr rfl
      rcases hwi with h | h <;> simp [h]
    · have hne : ¬ (w j = 0 ∨ w j = 2) := fun h => hj ((hmem j).mp h)
      generalize hr : w j = r at hne ⊢
      fin_cases r <;> simp_all

def fam3Set (N : ℕ) : Finset (Fin N → Fin 4) :=
  (fam3List N).toFinset.biUnion (fun t => fiber N t.1 t.2.1 t.2.2.1 t.2.2.2)

private lemma choose_two_mul (N : ℕ) : 2 * N.choose 2 = N * (N - 1) := by
  rw [Nat.choose_two_right]
  have h := Nat.even_mul_pred_self N
  obtain ⟨k, hk⟩ := h
  omega

private lemma choose_three_mul (N : ℕ) :
    6 * N.choose 3 = N * (N - 1) * (N - 2) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose N 3
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial, Nat.sub_zero,
    mul_one] at h
  have h6 : Nat.succ 2 * (Nat.succ 1 * Nat.succ 0) = 6 := by decide
  rw [h6] at h
  rw [← h]
  ring

lemma card_fam3Set {N : ℕ} (hN : 5 ≤ N) :
    3 * (fam3Set N).card =
      6 + 6 * N + 18 * (N * (N - 1)) + 14 * (N * (N - 1) * (N - 2)) := by
  have hpw : ((fam3List N).toFinset : Set (ℕ × ℕ × ℕ × ℕ)).PairwiseDisjoint
      (fun t => fiber N t.1 t.2.1 t.2.2.1 t.2.2.2) := by
    intro t1 _ t2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro w h1 h2
    simp only [fiber, mem_filter, mem_univ, true_and] at h1 h2
    apply hne
    ext <;> omega
  have hcard : (fam3Set N).card =
      ((fam3List N).map (fun t => (fiber N t.1 t.2.1 t.2.2.1 t.2.2.2).card)).sum := by
    unfold fam3Set
    rw [Finset.card_biUnion hpw, List.sum_toFinset _ (fam3List_nodup hN)]
  have hsub1 : N - (N - 1) = 1 := by omega
  have hsub2 : N - (N - 2) = 2 := by omega
  have hsub3 : N - (N - 3) = 3 := by omega
  have hch1 : N.choose (N - 1) = N := by
    rw [Nat.choose_symm (by omega : 1 ≤ N), Nat.choose_one_right]
  have hch2 : N.choose (N - 2) = N.choose 2 :=
    Nat.choose_symm (by omega : 2 ≤ N)
  have hch3 : N.choose (N - 3) = N.choose 3 :=
    Nat.choose_symm (by omega : 3 ≤ N)
  have hch2' : (N - 1).choose (N - 2) = N - 1 := by
    rw [show N - 2 = (N - 1) - 1 by omega, Nat.choose_symm (by omega : 1 ≤ N - 1),
      Nat.choose_one_right]
  have hch3' : (N - 1).choose (N - 3) = (N - 1).choose 2 := by
    rw [show N - 3 = (N - 1) - 2 by omega, Nat.choose_symm (by omega : 2 ≤ N - 1)]
  have hch3'' : (N - 2).choose (N - 3) = N - 2 := by
    rw [show N - 3 = (N - 2) - 1 by omega, Nat.choose_symm (by omega : 1 ≤ N - 2),
      Nat.choose_one_right]
  have hch1' : (N - 1).choose (N - 1) = 1 := Nat.choose_self _
  have hc2 : 2 * N.choose 2 = N * (N - 1) := choose_two_mul N
  have hc2' : 2 * (N - 1).choose 2 = (N - 1) * (N - 2) := by
    have := choose_two_mul (N - 1)
    rwa [show N - 1 - 1 = N - 2 by omega] at this
  have hc3 : 6 * N.choose 3 = N * (N - 1) * (N - 2) := choose_three_mul N
  simp only [fam3List, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hcard
  rw [card_fiber (by omega : N - 1 + 0 + 1 + 0 = N),
    card_fiber (by omega : N - 2 + 1 + 0 + 1 = N),
    card_fiber (by omega : N - 3 + 1 + 0 + 2 = N),
    card_fiber (by omega : N - 3 + 1 + 1 + 1 = N),
    card_fiber (by omega : N - 3 + 2 + 0 + 1 = N),
    card_fiber (by omega : 0 + N + 0 + 0 = N),
    card_fiber (by omega : 0 + (N - 2) + 2 + 0 = N),
    card_fiber (by omega : 0 + (N - 3) + 3 + 0 = N),
    card_fiber (by omega : 1 + (N - 2) + 1 + 0 = N),
    card_fiber (by omega : 2 + (N - 2) + 0 + 0 = N),
    card_fiber (by omega : 3 + (N - 3) + 0 + 0 = N),
    card_fiber (by omega : 0 + 1 + (N - 2) + 1 = N),
    card_fiber (by omega : 0 + 1 + (N - 3) + 2 = N),
    card_fiber (by omega : 0 + 2 + (N - 3) + 1 = N),
    card_fiber (by omega : 1 + 0 + (N - 1) + 0 = N),
    card_fiber (by omega : 1 + 1 + (N - 3) + 1 = N),
    card_fiber (by omega : 0 + 0 + 0 + N = N),
    card_fiber (by omega : 0 + 0 + 2 + (N - 2) = N),
    card_fiber (by omega : 0 + 0 + 3 + (N - 3) = N),
    card_fiber (by omega : 1 + 0 + 1 + (N - 2) = N),
    card_fiber (by omega : 2 + 0 + 0 + (N - 2) = N),
    card_fiber (by omega : 3 + 0 + 0 + (N - 3) = N)] at hcard
  simp only [Nat.sub_zero, hsub1, hsub2, hsub3, hch1, hch2, hch3, hch2', hch3', hch3'', hch1',
    Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_self,
    show N - 1 - (N - 2) = 1 by omega, show N - 1 - 1 = N - 2 by omega,
    show 3 - 1 = 2 by omega, show 3 - 2 = 1 by omega,
    show (3 : ℕ).choose 2 = 3 by decide, one_mul, mul_one] at hcard
  have h1 : N * (N - 1).choose 2 = 3 * N.choose 3 := by
    have hmul : 2 * (N * (N - 1).choose 2) = N * (N - 1) * (N - 2) := by
      calc 2 * (N * (N - 1).choose 2) = N * (2 * (N - 1).choose 2) := by ring
        _ = N * ((N - 1) * (N - 2)) := by rw [hc2']
        _ = N * (N - 1) * (N - 2) := by ring
    omega
  have h2 : N.choose 2 * (N - 2) = 3 * N.choose 3 := by
    have hmul : 2 * (N.choose 2 * (N - 2)) = N * (N - 1) * (N - 2) := by
      calc 2 * (N.choose 2 * (N - 2)) = (2 * N.choose 2) * (N - 2) := by ring
        _ = N * (N - 1) * (N - 2) := by rw [hc2]
    omega
  have h3 : N * (N - 1) * (N - 2) = 6 * N.choose 3 := hc3.symm
  have h4 : N * (N - 1) = 2 * N.choose 2 := hc2.symm
  omega

private lemma card_filter_add_neg {α : Type*} [Fintype α] [DecidableEq α]
    (P : α → Prop) [DecidablePred P] :
    (univ.filter P).card + (univ.filter (fun x => ¬ P x)).card = Fintype.card α := by
  have hdisj : Disjoint (univ.filter P) (univ.filter (fun x => ¬ P x)) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    exact h2 h1
  have hunion : univ.filter P ∪ univ.filter (fun x => ¬ P x) = univ := by
    ext x; simp [em]
  rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]

private lemma invalid_eq_union {N : ℕ} (hN : 5 ≤ N) :
    univ.filter (fun w => ¬ @Valid N w) = fam1Set N ∪ fam2Set N ∪ fam3Set N := by
  ext w
  simp only [mem_filter, mem_univ, true_and, mem_union, fam1Set, fam2Set, fam3Set,
    mem_biUnion, List.mem_toFinset, fiber]
  have hv : ¬ Valid w ↔ cnt w 1 + cnt w 3 = 1 ∨ cnt w 0 + cnt w 2 = 1 ∨
      (cnt w 0, cnt w 1, cnt w 2, cnt w 3) ∈ fam3List N := by
    rw [valid_iff_validCounts]
    have hmk : ValidCounts (cnt w) ↔
        ValidCounts (mk4 (cnt w 0) (cnt w 1) (cnt w 2) (cnt w 3)) := by
      rw [← cnt_eq_mk4 w]
    rw [hmk]
    exact classify_invalid hN (cnt_sum w)
  rw [hv]
  constructor
  · rintro (h1 | h2 | h3)
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr h2)
    · exact Or.inr ⟨(cnt w 0, cnt w 1, cnt w 2, cnt w 3), h3, rfl, rfl, rfl, rfl⟩
  · rintro ((h1 | h2) | ⟨⟨a0, a1, a2, a3⟩, hmem, h0, h1, h2, h3⟩)
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · dsimp only at h0 h1 h2 h3
      rw [← h0, ← h1, ← h2, ← h3] at hmem
      exact Or.inr (Or.inr hmem)

private lemma disjoint_fam1_fam2 {N : ℕ} (hN : 5 ≤ N) :
    Disjoint (fam1Set N) (fam2Set N) := by
  rw [Finset.disjoint_left]
  intro w h1 h2
  simp only [fam1Set, fam2Set, mem_filter, mem_univ, true_and] at h1 h2
  have := cnt_sum w
  omega

private lemma disjoint_fam12_fam3 {N : ℕ} (hN : 5 ≤ N) :
    Disjoint (fam1Set N ∪ fam2Set N) (fam3Set N) := by
  unfold fam3Set
  rw [Finset.disjoint_biUnion_right]
  rintro ⟨a0, a1, a2, a3⟩ ht
  have hmem : (a0, a1, a2, a3) ∈ fam3List N := List.mem_toFinset.mp ht
  have hd := fam3List_disjoint_fam12 hN hmem
  rw [Finset.disjoint_left]
  intro w h12 h3
  simp only [mem_union, fam1Set, fam2Set, mem_filter, mem_univ, true_and] at h12
  simp only [fiber, mem_filter, mem_univ, true_and] at h3
  rcases h3 with ⟨h0, h1, h2, h3⟩
  rcases h12 with h | h
  · exact hd.1 (by omega)
  · exact hd.2 (by omega)

lemma card_valid_ge5 {N : ℕ} (hN : 5 ≤ N) :
    3 * (univ.filter (@Valid N)).card + 3 * (2 * (N * 2 ^ N)) +
      (6 + 6 * N + 18 * (N * (N - 1)) + 14 * (N * (N - 1) * (N - 2))) = 3 * 4 ^ N := by
  have hcompl : (univ.filter (@Valid N)).card + (univ.filter (fun w => ¬ @Valid N w)).card =
      4 ^ N := by
    have h := card_filter_add_neg (@Valid N)
    simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ] at h
    exact h
  have hinv_card : (univ.filter (fun w => ¬ @Valid N w)).card =
      2 * (N * 2 ^ N) + (fam3Set N).card := by
    rw [invalid_eq_union hN, Finset.card_union_of_disjoint (disjoint_fam12_fam3 hN),
      Finset.card_union_of_disjoint (disjoint_fam1_fam2 hN), card_fam1Set, card_fam2Set]
    ring
  have hf3 := card_fam3Set hN
  generalize (univ.filter (@Valid N)).card = V at hcompl ⊢
  generalize (univ.filter (fun w => ¬ @Valid N w)).card = I at hcompl hinv_card
  generalize (fam3Set N).card = F at hinv_card hf3
  omega

theorem closed_form (n : ℕ) (hn : 2 ≤ n) :
    3 * a n = 3 * (4 ^ (n + 3) - ((n : ℤ) + 3) * 2 ^ (n + 4)) -
      2 * (7 * (n : ℤ) ^ 3 + 51 * (n : ℤ) ^ 2 + 125 * (n : ℤ) + 108) := by
  have hne : n ≠ 0 := by omega
  simp only [a, hne, ↓reduceIte]
  have hN := card_valid_ge5 (N := n + 3) (by omega)
  have hsub1 : n + 3 - 1 = n + 2 := by omega
  have hsub2 : n + 3 - 2 = n + 1 := by omega
  rw [hsub1, hsub2] at hN
  have hZ : (3 * ((univ.filter (@Valid (n + 3))).card : ℤ)) +
      3 * (2 * (((n : ℤ) + 3) * 2 ^ (n + 3))) +
      (6 + 6 * ((n : ℤ) + 3) + 18 * (((n : ℤ) + 3) * ((n : ℤ) + 2)) +
        14 * (((n : ℤ) + 3) * ((n : ℤ) + 2) * ((n : ℤ) + 1))) =
      3 * 4 ^ (n + 3) := by
    exact_mod_cast hN
  have hpow : (2 : ℤ) ^ (n + 4) = 2 * 2 ^ (n + 3) := by
    rw [show n + 4 = (n + 3) + 1 by omega, pow_succ]
    ring
  rw [hpow]
  linarith

lemma a_zero : a 0 = 0 := by simp [a]

lemma a_one : a 1 = 16 := by
  simp only [a, one_ne_zero, ↓reduceIte]
  let L : List (ℕ × ℕ × ℕ × ℕ) :=
    [(0, 0, 4, 0), (0, 1, 0, 3), (0, 3, 0, 1), (2, 0, 2, 0), (4, 0, 0, 0)]
  have hset : univ.filter (@Valid 4) =
      L.toFinset.biUnion (fun t => fiber 4 t.1 t.2.1 t.2.2.1 t.2.2.2) := by
    ext w
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, List.mem_toFinset, fiber]
    have hv : Valid w ↔ (cnt w 0, cnt w 1, cnt w 2, cnt w 3) ∈ L := by
      rw [valid_iff_validCounts]
      have hmk : ValidCounts (cnt w) ↔ ValidCounts (mk4 (cnt w 0) (cnt w 1) (cnt w 2) (cnt w 3)) := by
        rw [← cnt_eq_mk4 w]
      rw [hmk]
      have hsum := cnt_sum w
      exact valid_N4_fin ⟨cnt w 0, by omega⟩ ⟨cnt w 1, by omega⟩
        ⟨cnt w 2, by omega⟩ ⟨cnt w 3, by omega⟩ hsum
    rw [hv]
    constructor
    · intro h
      exact ⟨(cnt w 0, cnt w 1, cnt w 2, cnt w 3), h, rfl, rfl, rfl, rfl⟩
    · rintro ⟨⟨a0, a1, a2, a3⟩, hmem, h0, h1, h2, h3⟩
      dsimp only at h0 h1 h2 h3
      rwa [h0, h1, h2, h3]
  have hpw : (L.toFinset : Set (ℕ × ℕ × ℕ × ℕ)).PairwiseDisjoint
      (fun t => fiber 4 t.1 t.2.1 t.2.2.1 t.2.2.2) := by
    intro t1 _ t2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro w h1 h2
    simp only [fiber, mem_filter, mem_univ, true_and] at h1 h2
    apply hne
    ext <;> omega
  have hnodup : L.Nodup := by decide
  have hcard : (univ.filter (@Valid 4)).card = 16 := by
    rw [hset, Finset.card_biUnion hpw, List.sum_toFinset _ hnodup]
    simp only [L, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [card_fiber (by decide : 0 + 0 + 4 + 0 = 4),
      card_fiber (by decide : 0 + 1 + 0 + 3 = 4),
      card_fiber (by decide : 0 + 3 + 0 + 1 = 4),
      card_fiber (by decide : 2 + 0 + 2 + 0 = 4),
      card_fiber (by decide : 4 + 0 + 0 + 0 = 4)]
    decide
  exact_mod_cast hcard

end Counting

section GeneratingFunction

open PowerSeries

private def poly3 (m : ℤ) : ℤ := 7 * m ^ 3 + 51 * m ^ 2 + 125 * m + 108

private lemma poly3_rec (m : ℤ) :
    poly3 (m + 9) - 12 * poly3 (m + 8) + 58 * poly3 (m + 7) - 148 * poly3 (m + 6) +
    217 * poly3 (m + 5) - 184 * poly3 (m + 4) + 84 * poly3 (m + 3) - 16 * poly3 (m + 2) = 0 := by
  unfold poly3
  ring

private lemma closed_form_at (k d : ℕ) (hd : 2 ≤ d) (c4 c2 d3 dz : ℤ)
    (hc4 : (4 : ℤ) ^ (d - 2) = c4) (hc2 : (2 : ℤ) ^ (d - 2) = c2)
    (hd3 : (d : ℤ) + 3 = d3) (hdz : (d : ℤ) = dz) :
    3 * a (k + d) =
      3 * (c4 * (4 : ℤ) ^ (k + 5) - ((k : ℤ) + d3) * (c2 * (2 : ℤ) ^ (k + 6))) -
      2 * poly3 ((k : ℤ) + dz) := by
  have h := closed_form (k + d) (by omega)
  have h4 : (4 : ℤ) ^ (k + d + 3) = c4 * (4 : ℤ) ^ (k + 5) := by
    rw [← hc4, ← pow_add, show d - 2 + (k + 5) = k + d + 3 by omega]
  have h2 : (2 : ℤ) ^ (k + d + 4) = c2 * (2 : ℤ) ^ (k + 6) := by
    rw [← hc2, ← pow_add, show d - 2 + (k + 6) = k + d + 4 by omega]
  rw [h4, h2] at h
  push_cast at h
  rw [add_assoc (k : ℤ) (d : ℤ) 3, hd3, hdz] at h
  exact h

private lemma rec_alg (m x y v0 v1 v2 v3 v4 v5 v6 v7 : ℤ)
    (h0 : 3 * v0 = 3 * (1 * x - (m + 5) * (1 * y)) - 2 * poly3 (m + 2))
    (h1 : 3 * v1 = 3 * (4 * x - (m + 6) * (2 * y)) - 2 * poly3 (m + 3))
    (h2 : 3 * v2 = 3 * (16 * x - (m + 7) * (4 * y)) - 2 * poly3 (m + 4))
    (h3 : 3 * v3 = 3 * (64 * x - (m + 8) * (8 * y)) - 2 * poly3 (m + 5))
    (h4 : 3 * v4 = 3 * (256 * x - (m + 9) * (16 * y)) - 2 * poly3 (m + 6))
    (h5 : 3 * v5 = 3 * (1024 * x - (m + 10) * (32 * y)) - 2 * poly3 (m + 7))
    (h6 : 3 * v6 = 3 * (4096 * x - (m + 11) * (64 * y)) - 2 * poly3 (m + 8))
    (h7 : 3 * v7 = 3 * (16384 * x - (m + 12) * (128 * y)) - 2 * poly3 (m + 9)) :
    v7 = 12 * v6 - 58 * v5 + 148 * v4 - 217 * v3 + 184 * v2 - 84 * v1 + 16 * v0 := by
  have hp := poly3_rec m
  have hxy :
      (16384 * x - (m + 12) * (128 * y)) - 12 * (4096 * x - (m + 11) * (64 * y)) +
      58 * (1024 * x - (m + 10) * (32 * y)) - 148 * (256 * x - (m + 9) * (16 * y)) +
      217 * (64 * x - (m + 8) * (8 * y)) - 184 * (16 * x - (m + 7) * (4 * y)) +
      84 * (4 * x - (m + 6) * (2 * y)) - 16 * (1 * x - (m + 5) * (1 * y)) = 0 := by
    ring
  linarith

lemma recurrence (n : ℕ) (hn : 8 < n) :
    a n = 12 * a (n - 1) - 58 * a (n - 2) + 148 * a (n - 3) -
      217 * a (n - 4) + 184 * a (n - 5) - 84 * a (n - 6) + 16 * a (n - 7) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
  simp only [show k + 9 - 1 = k + 8 by omega, show k + 9 - 2 = k + 7 by omega,
    show k + 9 - 3 = k + 6 by omega, show k + 9 - 4 = k + 5 by omega,
    show k + 9 - 5 = k + 4 by omega, show k + 9 - 6 = k + 3 by omega,
    show k + 9 - 7 = k + 2 by omega]
  exact rec_alg (k : ℤ) ((4 : ℤ) ^ (k + 5)) ((2 : ℤ) ^ (k + 6))
    (a (k + 2)) (a (k + 3)) (a (k + 4)) (a (k + 5))
    (a (k + 6)) (a (k + 7)) (a (k + 8)) (a (k + 9))
    (closed_form_at k 2 (by omega) 1 1 5 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (closed_form_at k 3 (by omega) 4 2 6 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (closed_form_at k 4 (by omega) 16 4 7 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (closed_form_at k 5 (by omega) 64 8 8 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (closed_form_at k 6 (by omega) 256 16 9 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (closed_form_at k 7 (by omega) 1024 32 10 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (closed_form_at k 8 (by omega) 4096 64 11 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (closed_form_at k 9 (by omega) 16384 128 12 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num))

private lemma a_eval (n : ℕ) (v : ℤ) (hn : 2 ≤ n)
    (hv : 3 * (4 ^ (n + 3) - ((n : ℤ) + 3) * 2 ^ (n + 4)) -
      2 * (7 * (n : ℤ) ^ 3 + 51 * (n : ℤ) ^ 2 + 125 * (n : ℤ) + 108) = 3 * v) :
    a n = v := by
  have h := closed_form n hn
  omega

theorem gf_identity :
    PowerSeries.mk a * ((1 - X) ^ 4 * (1 - 2 * X) ^ 2 * (1 - 4 * X)) =
      2 * X * (8 + 50 * X - X ^ 2 - 1488 * X ^ 3 + 4469 * X ^ 4 -
        5336 * X ^ 5 + 2996 * X ^ 6 - 656 * X ^ 7) := by
  have hL : PowerSeries.mk a * ((1 - X) ^ 4 * (1 - 2 * X) ^ 2 * (1 - 4 * X)) =
      PowerSeries.mk a - (12 : ℤ) • (PowerSeries.mk a * X ^ 1) +
      (58 : ℤ) • (PowerSeries.mk a * X ^ 2) - (148 : ℤ) • (PowerSeries.mk a * X ^ 3) +
      (217 : ℤ) • (PowerSeries.mk a * X ^ 4) - (184 : ℤ) • (PowerSeries.mk a * X ^ 5) +
      (84 : ℤ) • (PowerSeries.mk a * X ^ 6) - (16 : ℤ) • (PowerSeries.mk a * X ^ 7) := by
    simp only [zsmul_eq_mul]
    ring
  have hR : (2 * X * (8 + 50 * X - X ^ 2 - 1488 * X ^ 3 + 4469 * X ^ 4 -
        5336 * X ^ 5 + 2996 * X ^ 6 - 656 * X ^ 7) : PowerSeries ℤ) =
      (16 : ℤ) • X ^ 1 + (100 : ℤ) • X ^ 2 - (2 : ℤ) • X ^ 3 - (2976 : ℤ) • X ^ 4 +
      (8938 : ℤ) • X ^ 5 - (10672 : ℤ) • X ^ 6 + (5992 : ℤ) • X ^ 7 - (1312 : ℤ) • X ^ 8 := by
    simp only [zsmul_eq_mul]
    ring
  rw [hL, hR]
  have ha0 : a 0 = 0 := a_zero
  have ha1 : a 1 = 16 := a_one
  have ha2 : a 2 = 292 := a_eval 2 292 (by omega) (by norm_num)
  have ha3 : a 3 = 2574 := a_eval 3 2574 (by omega) (by norm_num)
  have ha4 : a 4 = 13344 := a_eval 4 13344 (by omega) (by norm_num)
  have ha5 : a 5 = 59518 := a_eval 5 59518 (by omega) (by norm_num)
  have ha6 : a 6 = 250124 := a_eval 6 250124 (by omega) (by norm_num)
  have ha7 : a 7 = 1024174 := a_eval 7 1024174 (by omega) (by norm_num)
  have ha8 : a 8 = 4143944 := a_eval 8 4143944 (by omega) (by norm_num)
  ext n
  simp only [map_add, map_sub, map_zsmul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow, smul_eq_mul]
  by_cases hn : n < 9
  · interval_cases n <;> simp [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8]
  · have hgt : 8 < n := by omega
    have hrec := recurrence n hgt
    have h1 : 1 ≤ n := by omega
    have h2 : 2 ≤ n := by omega
    have h3 : 3 ≤ n := by omega
    have h4 : 4 ≤ n := by omega
    have h5 : 5 ≤ n := by omega
    have h6 : 6 ≤ n := by omega
    have h7 : 7 ≤ n := by omega
    have hn1 : n ≠ 1 := by omega
    have hn2 : n ≠ 2 := by omega
    have hn3 : n ≠ 3 := by omega
    have hn4 : n ≠ 4 := by omega
    have hn5 : n ≠ 5 := by omega
    have hn6 : n ≠ 6 := by omega
    have hn7 : n ≠ 7 := by omega
    have hn8 : n ≠ 8 := by omega
    simp only [h1, h2, h3, h4, h5, h6, h7, ↓reduceIte, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8]
    omega

end GeneratingFunction

end OMA.A183886Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a183886.main :=
  ⟨OMA.A183886Proof.closed_form, OMA.A183886Proof.gf_identity, OMA.A183886Proof.recurrence⟩
