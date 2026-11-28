import OMAStatements.S_oeis_a004485
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a004485

/-- Values of the Wythoff Sprague-Grundy function in rows 0 to 4, columns 0 to 20. -/
def wythTab : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20],
   [1, 2, 0, 4, 5, 3, 7, 8, 6, 10, 11, 9, 13, 14, 12, 16, 17, 15, 19, 20, 18],
   [2, 0, 1, 5, 3, 4, 8, 6, 7, 11, 9, 10, 14, 12, 13, 17, 15, 16, 20, 18, 19],
   [3, 4, 5, 6, 2, 0, 1, 9, 10, 12, 8, 7, 15, 11, 16, 18, 14, 13, 21, 17, 22],
   [4, 5, 3, 2, 7, 6, 9, 0, 1, 8, 13, 12, 11, 16, 15, 10, 19, 18, 17, 14, 21]]

/-- Table lookup. -/
def wythT (a x : ℕ) : ℕ := (wythTab.getD a []).getD x 0

/-- The explicit candidate for rows 0 to 4: additively periodic with period 12 from column 9. -/
def wythF (a x : ℕ) : ℕ :=
  if x < 9 then wythT a x else wythT a (9 + (x - 9) % 12) + 12 * ((x - 9) / 12)

theorem wythF_shift (a x : ℕ) (hx : 9 ≤ x) : wythF a (x + 12) = wythF a x + 12 := by
  have h1 : ¬ (x + 12 < 9) := by omega
  have h2 : ¬ (x < 9) := by omega
  have h3 : x + 12 - 9 = (x - 9) + 12 := by omega
  unfold wythF
  rw [if_neg h1, if_neg h2, h3, Nat.add_mod_right, Nat.add_div_right _ (by norm_num)]
  ring

theorem wythF_big (a x : ℕ) (hx : 21 ≤ x) : 12 ≤ wythF a x := by
  have h2 : ¬ (x < 9) := by omega
  have h3 : 1 ≤ (x - 9) / 12 := by omega
  unfold wythF
  rw [if_neg h2]
  omega

/-- The option condition at (a, b): no option has the same value. -/
def wythPA (a b : ℕ) : Prop := ∀ c d, Move a b c d → wythF c d ≠ wythF a b

/-- The mex condition at (a, b): every smaller value is the value of an option. -/
def wythPB (a b : ℕ) : Prop := ∀ m, m < wythF a b → ∃ c d, Move a b c d ∧ wythF c d = m

/-- Boolean check of the option condition. -/
def wythChkA (a b : ℕ) : Bool :=
  (List.range b).all (fun d => decide (wythF a d ≠ wythF a b)) &&
  (List.range a).all (fun c => decide (wythF c b ≠ wythF a b)) &&
  (List.range (min a b)).all (fun k => decide (wythF (a - (k + 1)) (b - (k + 1)) ≠ wythF a b))

/-- Boolean check of the mex condition. -/
def wythChkB (a b : ℕ) : Bool :=
  (List.range (wythF a b)).all (fun m =>
    (List.range b).any (fun d => decide (wythF a d = m)) ||
    (List.range a).any (fun c => decide (wythF c b = m)) ||
    (List.range (min a b)).any (fun k => decide (wythF (a - (k + 1)) (b - (k + 1)) = m)))

theorem wythChkA_sound (a b : ℕ) (h : wythChkA a b = true) : wythPA a b := by
  simp only [wythChkA, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨hr, hv⟩, hd⟩ := h
  intro c d hm
  rcases hm with ⟨hc, rfl⟩ | ⟨rfl, hdb⟩ | ⟨k, hk, hac, hbd⟩
  · exact hv c hc
  · exact hr d hdb
  · have hk' : k - 1 < min a b := by
      rw [Nat.lt_min]; omega
    have e1 : a - (k - 1 + 1) = c := by omega
    have e2 : b - (k - 1 + 1) = d := by omega
    have := hd (k - 1) hk'
    rw [e1, e2] at this
    exact this

theorem wythChkB_sound (a b : ℕ) (h : wythChkB a b = true) : wythPB a b := by
  simp only [wythChkB, List.all_eq_true, List.mem_range, Bool.or_eq_true, List.any_eq_true,
    decide_eq_true_eq] at h
  intro m hm
  rcases h m hm with (⟨d, hd, hf⟩ | ⟨c, hc, hf⟩) | ⟨k, hk, hf⟩
  · exact ⟨a, d, Or.inr (Or.inl ⟨rfl, hd⟩), hf⟩
  · exact ⟨c, b, Or.inl ⟨hc, rfl⟩, hf⟩
  · rw [Nat.lt_min] at hk
    refine ⟨a - (k + 1), b - (k + 1), Or.inr (Or.inr ⟨k + 1, by omega, by omega, by omega⟩), hf⟩

theorem wyth_fin_check :
    (List.range 5).all (fun a => (List.range 28).all (fun b => wythChkA a b && wythChkB a b))
      = true := by
  decide +kernel

theorem wyth_fin (a b : ℕ) (ha : a < 5) (hb : b < 28) : wythPA a b ∧ wythPB a b := by
  have h := wyth_fin_check
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  obtain ⟨hA, hB⟩ := h a ha b hb
  exact ⟨wythChkA_sound a b hA, wythChkB_sound a b hB⟩

theorem wyth_small_check :
    (List.range 5).all (fun a => (List.range 21).all (fun d =>
      decide (wythF a d ≤ 22) && (decide (9 ≤ d) || decide (wythF a d ≤ 10)) &&
      (decide (d < 16) || decide (11 ≤ wythF a d)))) = true := by
  decide +kernel

theorem wyth_hit_check :
    (List.range 5).all (fun a => (List.range 23).all (fun m =>
      (List.range 28).any (fun d => decide (wythF a d = m)))) = true := by
  decide +kernel

theorem wyth_le22 (a d : ℕ) (ha : a < 5) (hd : d < 21) : wythF a d ≤ 22 := by
  have h := wyth_small_check
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at h
  exact (h a ha d hd).1.1

theorem wyth_le10 (a d : ℕ) (ha : a < 5) (hd : d < 9) : wythF a d ≤ 10 := by
  have h := wyth_small_check
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at h
  rcases (h a ha d (by omega)).1.2 with h' | h'
  · omega
  · exact h'

theorem wyth_ge11 (a b : ℕ) (ha : a < 5) (hb : 16 ≤ b) : 11 ≤ wythF a b := by
  by_cases hb' : b < 21
  · have h := wyth_small_check
    simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at h
    rcases (h a ha b hb').2 with h' | h'
    · omega
    · exact h'
  · have := wythF_big a b (by omega)
    omega

theorem wyth_hit (a m : ℕ) (ha : a < 5) (hm : m < 23) : ∃ d, d < 28 ∧ wythF a d = m := by
  have h := wyth_hit_check
  simp only [List.all_eq_true, List.mem_range, List.any_eq_true, decide_eq_true_eq] at h
  exact h a ha m hm

theorem wyth_move_le {a b c d : ℕ} (h : Move a b c d) : c ≤ a ∧ d ≤ b ∧ c + d < a + b := by
  rcases h with ⟨hc, rfl⟩ | ⟨rfl, hd⟩ | ⟨k, hk, hac, hbd⟩ <;> omega

theorem wyth_step (a b : ℕ) (ha : a < 5) (hb : 16 ≤ b) (hA : wythPA a b) (hB : wythPB a b) :
    wythPA a (b + 12) ∧ wythPB a (b + 12) := by
  have hsa : wythF a (b + 12) = wythF a b + 12 := wythF_shift a b (by omega)
  refine ⟨?_, ?_⟩
  · intro c d hm
    rw [hsa]
    rcases hm with ⟨hc, hdb⟩ | ⟨hca, hdb⟩ | ⟨k, hk, hac, hbd⟩
    · rw [hdb, wythF_shift c b (by omega)]
      have := hA c b (Or.inl ⟨hc, rfl⟩)
      omega
    · rw [hca]
      by_cases hd' : 21 ≤ d
      · have e : d = (d - 12) + 12 := by omega
        rw [e, wythF_shift a (d - 12) (by omega)]
        have := hA a (d - 12) (Or.inr (Or.inl ⟨rfl, by omega⟩))
        omega
      · have h1 := wyth_le22 a d ha (by omega)
        have h2 := wyth_ge11 a b ha hb
        omega
    · have hk5 : k ≤ a := by omega
      have e : d = (b - k) + 12 := by omega
      rw [e, wythF_shift c (b - k) (by omega)]
      have := hA c (b - k) (Or.inr (Or.inr ⟨k, hk, hac, by omega⟩))
      omega
  · intro m hm
    rw [hsa] at hm
    by_cases hm23 : m < 23
    · obtain ⟨d, hd, hf⟩ := wyth_hit a m ha hm23
      exact ⟨a, d, Or.inr (Or.inl ⟨rfl, by omega⟩), hf⟩
    · obtain ⟨c, d, hmv, hf⟩ := hB (m - 12) (by omega)
      have hle := wyth_move_le hmv
      have hd9 : 9 ≤ d := by
        by_contra hlt
        have := wyth_le10 c d (by omega) (by omega)
        omega
      refine ⟨c, d + 12, ?_, ?_⟩
      · rcases hmv with ⟨hc, rfl⟩ | ⟨rfl, hdb⟩ | ⟨k, hk, hac, hbd⟩
        · exact Or.inl ⟨hc, rfl⟩
        · exact Or.inr (Or.inl ⟨rfl, by omega⟩)
        · exact Or.inr (Or.inr ⟨k, hk, hac, by omega⟩)
      · rw [wythF_shift c d hd9]
        omega

theorem wyth_all : ∀ b a, a < 5 → wythPA a b ∧ wythPB a b := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro a ha
    by_cases hb : b < 28
    · exact wyth_fin a b ha hb
    · have e : b = (b - 12) + 12 := by omega
      obtain ⟨hA, hB⟩ := ih (b - 12) (by omega) a ha
      rw [e]
      exact wyth_step a (b - 12) ha (by omega) hA hB

theorem wyth_eq (g : ℕ → ℕ → ℕ) (hg : IsGrundy g) :
    ∀ s a b, a + b = s → a < 5 → g a b = wythF a b := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro a b hs ha
    obtain ⟨h1, h2⟩ := hg a b
    obtain ⟨hA, hB⟩ := wyth_all b a ha
    rcases lt_trichotomy (g a b) (wythF a b) with hlt | heq | hgt
    · exfalso
      obtain ⟨c, d, hmv, hf⟩ := hB (g a b) hlt
      have hle := wyth_move_le hmv
      have hcd := ih (c + d) (by omega) c d rfl (by omega)
      exact h1 c d hmv (hcd.trans hf)
    · exact heq
    · exfalso
      obtain ⟨c, d, hmv, hgcd⟩ := h2 (wythF a b) hgt
      have hle := wyth_move_le hmv
      have hcd := ih (c + d) (by omega) c d rfl (by omega)
      exact hA c d hmv (hcd ▸ hgcd)

theorem wyth_tail_check :
    (List.range 22).all (fun n =>
      decide (((wythF 4 n : ℕ) : ℤ) - (if 1 ≤ n then ((wythF 4 (n - 1) : ℕ) : ℤ) else 0)
        - (if 12 ≤ n then ((wythF 4 (n - 12) : ℕ) : ℤ) else 0)
        + (if 13 ≤ n then ((wythF 4 (n - 13) : ℕ) : ℤ) else 0) = numeratorCoeff n)) = true := by
  decide +kernel

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a004485.main := by
  intro g hg
  have key : ∀ n, OMA.S_oeis_a004485.a g n = ((wythF 4 n : ℕ) : ℤ) := by
    intro n
    simp only [OMA.S_oeis_a004485.a, wyth_eq g hg (4 + n) 4 n rfl (by norm_num),
      Int.ofNat_eq_natCast]
  have hrec : ∀ n : ℕ, 21 < n → OMA.S_oeis_a004485.a g n =
      OMA.S_oeis_a004485.a g (n - 1) + OMA.S_oeis_a004485.a g (n - 12)
        - OMA.S_oeis_a004485.a g (n - 13) := by
    intro n hn
    rw [key, key, key, key]
    have e1 : wythF 4 n = wythF 4 (n - 12) + 12 := by
      have := wythF_shift 4 (n - 12) (by omega)
      rw [show n - 12 + 12 = n by omega] at this
      exact this
    have e2 : wythF 4 (n - 1) = wythF 4 (n - 13) + 12 := by
      have := wythF_shift 4 (n - 13) (by omega)
      rw [show n - 13 + 12 = n - 1 by omega] at this
      exact this
    rw [e1, e2]
    push_cast
    ring
  refine ⟨hrec, ?_⟩
  intro n
  by_cases hn : 22 ≤ n
  · have hnone : ([4, 1, -2, -1, 5, -1, 3, -9, 1, 7, 5, -1, -5, 4, 1, -4, 4, 0,
        -4, 6, 6, -8] : List ℤ)[n]? = none := List.getElem?_eq_none (by simp; omega)
    have hz : OMA.S_oeis_a004485.numeratorCoeff n = 0 := by
      simp only [OMA.S_oeis_a004485.numeratorCoeff, hnone, Option.getD_none]
    rw [hz]
    simp only [OMA.S_oeis_a004485.shifted, if_pos (show 1 ≤ n by omega),
      if_pos (show 12 ≤ n by omega), if_pos (show 13 ≤ n by omega)]
    rw [hrec n (by omega)]
    ring
  · have h := wyth_tail_check
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    have h' := h n (by omega)
    simp only [OMA.S_oeis_a004485.shifted, key]
    exact h'
