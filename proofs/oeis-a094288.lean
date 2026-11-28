import OMAStatements.S_oeis_a094288

-- Problem: A094288: Number of (s(0), s(1), ..., s(n)) such that 0 < s(i) < 8 and |s(i) - s(i-1)| <= 1 for i = 1,2,...,n, s(0) = 1, s(n) = 1.
-- Upstream: formal-conjectures statements/oeis-a094288.lean:0 (declaration OMA.S_oeis_a094288.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: wS094288 lo hi x R n y is the set of sequences s(0..n) with values in lo..hi,
-- s(0) = x, s(n) = y and R s(i-1) s(i). Removing the last value (Fin.init, inverse Fin.snoc)
-- maps the sequences of length n+2 ending at y whose value before last is z onto those of
-- length n+1 ending at z (wfib094288), so the count c(n+1, y) is the sum of c(n, z) over the z
-- with R z y (wcard094288); c(0, y) = [y = x] (wbase094288). Here values 1..7, x = 1,
-- R u v = (|u - v| <= 1): c(n+1, y) = c(n, y-1) + c(n, y) + c(n, y+1). The 7 x 7 matrix of this
-- step has characteristic polynomial t^7 - 7t^6 + 15t^5 - 5t^4 - 15t^3 + 9t^2 + 3t - 1, so by
-- Cayley-Hamilton the recurrence is a linear combination of the step equations (certificate for
-- linear_combination). The g.f. follows by comparing coefficients.

/-- Sequences s(0..n) with values in lo..hi, s(0) = x, s(n) = y and R between consecutive
values. -/
def wS094288 (lo hi x : ℕ) (R : ℕ → ℕ → Prop) [DecidableRel R] (n y : ℕ) :
    Finset (Fin (n + 1) → ℕ) :=
  (Fintype.piFinset fun _ : Fin (n + 1) => Finset.Icc lo hi).filter
    (fun s => s 0 = x ∧ s (Fin.last n) = y ∧ ∀ i : Fin n, R (s i.castSucc) (s i.succ))

theorem wmem094288 (lo hi x : ℕ) (R : ℕ → ℕ → Prop) [DecidableRel R] (n y : ℕ)
    (s : Fin (n + 1) → ℕ) :
    s ∈ wS094288 lo hi x R n y ↔ (∀ i, lo ≤ s i ∧ s i ≤ hi) ∧ s 0 = x ∧ s (Fin.last n) = y ∧
      ∀ i : Fin n, R (s i.castSucc) (s i.succ) := by
  unfold wS094288
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  simp only [Finset.mem_Icc]

/-- Removing the last value: a bijection onto the sequences one shorter. -/
theorem wfib094288 (lo hi x : ℕ) (R : ℕ → ℕ → Prop) [DecidableRel R] (n y z : ℕ)
    (hy1 : lo ≤ y) (hy2 : y ≤ hi) (hz : R z y) :
    ((wS094288 lo hi x R (n + 1) y).filter (fun s => s (Fin.last n).castSucc = z)).card =
      (wS094288 lo hi x R n z).card := by
  have e1 : (Fin.last n).succ = Fin.last (n + 1) := Fin.succ_last n
  apply Finset.card_nbij' (fun s : Fin (n + 1 + 1) → ℕ => (Fin.init s : Fin (n + 1) → ℕ))
    (fun t : Fin (n + 1) → ℕ => (Fin.snoc t y : Fin (n + 1 + 1) → ℕ))
  · intro s hs
    rw [Finset.mem_coe, Finset.mem_filter, wmem094288] at hs
    obtain ⟨⟨hr, h0, -, hst⟩, hz2⟩ := hs
    rw [Finset.mem_coe, wmem094288]
    refine ⟨fun i => hr i.castSucc, h0, hz2, fun i => ?_⟩
    exact hst i.castSucc
  · intro t ht
    rw [Finset.mem_coe, wmem094288] at ht
    obtain ⟨hr, h0, hl, hst⟩ := ht
    rw [Finset.mem_coe]
    simp only [Finset.mem_filter]
    rw [wmem094288]
    refine ⟨⟨fun i => ?_, ?_, ?_, fun i => ?_⟩, ?_⟩
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i2, rfl⟩ | rfl
      · rw [Fin.snoc_castSucc]
        exact hr i2
      · rw [Fin.snoc_last]
        exact ⟨hy1, hy2⟩
    · show (Fin.snoc t y : Fin (n + 1 + 1) → ℕ) (Fin.castSucc 0) = x
      rw [Fin.snoc_castSucc]
      exact h0
    · rw [Fin.snoc_last]
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i2, rfl⟩ | rfl
      · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact hst i2
      · rw [e1, Fin.snoc_last, Fin.snoc_castSucc, hl]
        exact hz
    · rw [Fin.snoc_castSucc]
      exact hl
  · intro s hs
    rw [Finset.mem_coe, Finset.mem_filter, wmem094288] at hs
    obtain ⟨⟨-, -, hl, -⟩, -⟩ := hs
    show (Fin.snoc (Fin.init s) y : Fin (n + 1 + 1) → ℕ) = s
    rw [← hl]
    exact Fin.snoc_init_self s
  · intro t _
    show Fin.init (Fin.snoc t y : Fin (n + 1 + 1) → ℕ) = t
    rw [Fin.init_snoc]

/-- The transfer-matrix recursion. -/
theorem wcard094288 (lo hi x : ℕ) (R : ℕ → ℕ → Prop) [DecidableRel R] (n y : ℕ)
    (hy1 : lo ≤ y) (hy2 : y ≤ hi) :
    (wS094288 lo hi x R (n + 1) y).card =
      ∑ z ∈ (Finset.Icc lo hi).filter (fun z => R z y), (wS094288 lo hi x R n z).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun s : Fin (n + 1 + 1) → ℕ => s (Fin.last n).castSucc)
    (t := (Finset.Icc lo hi).filter (fun z => R z y))]
  · apply Finset.sum_congr rfl
    intro z hz
    rw [Finset.mem_filter] at hz
    exact wfib094288 lo hi x R n y z hy1 hy2 hz.2
  · intro s hs
    rw [Finset.mem_coe, wmem094288] at hs
    obtain ⟨hr, -, hl, hst⟩ := hs
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    have h := hst (Fin.last n)
    have e1 : (Fin.last n).succ = Fin.last (n + 1) := Fin.succ_last n
    rw [e1, hl] at h
    exact ⟨hr _, h⟩

/-- Sequences of length one. -/
theorem wbase094288 (lo hi x : ℕ) (R : ℕ → ℕ → Prop) [DecidableRel R] (y : ℕ) :
    (wS094288 lo hi x R 0 y).card = if y = x ∧ lo ≤ x ∧ x ≤ hi then 1 else 0 := by
  split_ifs with h
  · obtain ⟨hyx, h1, h2⟩ := h
    rw [Finset.card_eq_one]
    refine ⟨fun _ => y, ?_⟩
    ext s
    rw [wmem094288, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h0, -, -⟩
      funext i
      have hi0 : i = 0 := Fin.fin_one_eq_zero i
      rw [hi0]
      exact h0.trans hyx.symm
    · rintro rfl
      refine ⟨fun _ => ?_, hyx, rfl, fun i => i.elim0⟩
      show lo ≤ y ∧ y ≤ hi
      omega
  · rw [Finset.card_eq_zero]
    apply Finset.subset_empty.1
    intro s hs
    exfalso
    obtain ⟨hr, h0, hl, -⟩ := (wmem094288 lo hi x R 0 y s).1 hs
    have e : Fin.last 0 = 0 := Fin.last_zero
    rw [e] at hl
    have hr0 := hr 0
    apply h
    omega

/-- The step relation of A094288. -/
abbrev wR094288 (u v : ℕ) : Prop := v ≤ u + 1 ∧ u ≤ v + 1

theorem wf1094288 : (Finset.Icc 1 7).filter (fun z => wR094288 z 1) = {1, 2} := by
  ext z
  rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  omega

theorem wf2094288 : (Finset.Icc 1 7).filter (fun z => wR094288 z 2) = {1, 2, 3} := by
  ext z
  rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
  omega

theorem wf3094288 : (Finset.Icc 1 7).filter (fun z => wR094288 z 3) = {2, 3, 4} := by
  ext z
  rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
  omega

theorem wf4094288 : (Finset.Icc 1 7).filter (fun z => wR094288 z 4) = {3, 4, 5} := by
  ext z
  rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
  omega

theorem wf5094288 : (Finset.Icc 1 7).filter (fun z => wR094288 z 5) = {4, 5, 6} := by
  ext z
  rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
  omega

theorem wf6094288 : (Finset.Icc 1 7).filter (fun z => wR094288 z 6) = {5, 6, 7} := by
  ext z
  rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
  omega

theorem wf7094288 : (Finset.Icc 1 7).filter (fun z => wR094288 z 7) = {6, 7} := by
  ext z
  rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  omega

theorem wr094288 (m : ℕ) :
    (wS094288 1 7 1 wR094288 (m + 1) 1).card =
      (wS094288 1 7 1 wR094288 m 1).card + (wS094288 1 7 1 wR094288 m 2).card ∧
    (wS094288 1 7 1 wR094288 (m + 1) 2).card =
      (wS094288 1 7 1 wR094288 m 1).card +
        ((wS094288 1 7 1 wR094288 m 2).card + (wS094288 1 7 1 wR094288 m 3).card) ∧
    (wS094288 1 7 1 wR094288 (m + 1) 3).card =
      (wS094288 1 7 1 wR094288 m 2).card +
        ((wS094288 1 7 1 wR094288 m 3).card + (wS094288 1 7 1 wR094288 m 4).card) ∧
    (wS094288 1 7 1 wR094288 (m + 1) 4).card =
      (wS094288 1 7 1 wR094288 m 3).card +
        ((wS094288 1 7 1 wR094288 m 4).card + (wS094288 1 7 1 wR094288 m 5).card) ∧
    (wS094288 1 7 1 wR094288 (m + 1) 5).card =
      (wS094288 1 7 1 wR094288 m 4).card +
        ((wS094288 1 7 1 wR094288 m 5).card + (wS094288 1 7 1 wR094288 m 6).card) ∧
    (wS094288 1 7 1 wR094288 (m + 1) 6).card =
      (wS094288 1 7 1 wR094288 m 5).card +
        ((wS094288 1 7 1 wR094288 m 6).card + (wS094288 1 7 1 wR094288 m 7).card) ∧
    (wS094288 1 7 1 wR094288 (m + 1) 7).card =
      (wS094288 1 7 1 wR094288 m 6).card + (wS094288 1 7 1 wR094288 m 7).card := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [wcard094288 1 7 1 wR094288 m 1 (by norm_num) (by norm_num), wf1094288,
      Finset.sum_pair (show (1 : ℕ) ≠ 2 by decide)]
  · rw [wcard094288 1 7 1 wR094288 m 2 (by norm_num) (by norm_num), wf2094288,
      Finset.sum_insert (show (1 : ℕ) ∉ ({2, 3} : Finset ℕ) by simp),
      Finset.sum_pair (show (2 : ℕ) ≠ 3 by decide)]
  · rw [wcard094288 1 7 1 wR094288 m 3 (by norm_num) (by norm_num), wf3094288,
      Finset.sum_insert (show (2 : ℕ) ∉ ({3, 4} : Finset ℕ) by simp),
      Finset.sum_pair (show (3 : ℕ) ≠ 4 by decide)]
  · rw [wcard094288 1 7 1 wR094288 m 4 (by norm_num) (by norm_num), wf4094288,
      Finset.sum_insert (show (3 : ℕ) ∉ ({4, 5} : Finset ℕ) by simp),
      Finset.sum_pair (show (4 : ℕ) ≠ 5 by decide)]
  · rw [wcard094288 1 7 1 wR094288 m 5 (by norm_num) (by norm_num), wf5094288,
      Finset.sum_insert (show (4 : ℕ) ∉ ({5, 6} : Finset ℕ) by simp),
      Finset.sum_pair (show (5 : ℕ) ≠ 6 by decide)]
  · rw [wcard094288 1 7 1 wR094288 m 6 (by norm_num) (by norm_num), wf6094288,
      Finset.sum_insert (show (5 : ℕ) ∉ ({6, 7} : Finset ℕ) by simp),
      Finset.sum_pair (show (6 : ℕ) ≠ 7 by decide)]
  · rw [wcard094288 1 7 1 wR094288 m 7 (by norm_num) (by norm_num), wf7094288,
      Finset.sum_pair (show (6 : ℕ) ≠ 7 by decide)]

open OMA.S_oeis_a094288 in
theorem OMA.solution : type_of% @OMA.S_oeis_a094288.main := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → ℕ, ∀ n k, c n k = (wS094288 1 7 1 wR094288 n k).card :=
    ⟨_, fun _ _ => rfl⟩
  have ha : ∀ n, a n = c n 1 := fun n =>
    (show a n = (wS094288 1 7 1 wR094288 n 1).card from rfl).trans (hc n 1).symm
  have r : ∀ m, c (m + 1) 1 = c m 1 + c m 2 ∧
      c (m + 1) 2 = c m 1 + (c m 2 + c m 3) ∧
      c (m + 1) 3 = c m 2 + (c m 3 + c m 4) ∧
      c (m + 1) 4 = c m 3 + (c m 4 + c m 5) ∧
      c (m + 1) 5 = c m 4 + (c m 5 + c m 6) ∧
      c (m + 1) 6 = c m 5 + (c m 6 + c m 7) ∧
      c (m + 1) 7 = c m 6 + c m 7 := by
    intro m
    simp only [hc]
    exact wr094288 m
  have b1 : c 0 1 = 1 := by
    rw [hc, wbase094288]
    decide
  have b2 : c 0 2 = 0 := by
    rw [hc, wbase094288]
    decide
  have b3 : c 0 3 = 0 := by
    rw [hc, wbase094288]
    decide
  have b4 : c 0 4 = 0 := by
    rw [hc, wbase094288]
    decide
  have b5 : c 0 5 = 0 := by
    rw [hc, wbase094288]
    decide
  have b6 : c 0 6 = 0 := by
    rw [hc, wbase094288]
    decide
  have b7 : c 0 7 = 0 := by
    rw [hc, wbase094288]
    decide
  have g01 : c 1 1 = c 0 1 + c 0 2 := (r 0).1
  have g02 : c 1 2 = c 0 1 + (c 0 2 + c 0 3) := (r 0).2.1
  have g03 : c 1 3 = c 0 2 + (c 0 3 + c 0 4) := (r 0).2.2.1
  have g04 : c 1 4 = c 0 3 + (c 0 4 + c 0 5) := (r 0).2.2.2.1
  have g05 : c 1 5 = c 0 4 + (c 0 5 + c 0 6) := (r 0).2.2.2.2.1
  have g06 : c 1 6 = c 0 5 + (c 0 6 + c 0 7) := (r 0).2.2.2.2.2.1
  have g07 : c 1 7 = c 0 6 + c 0 7 := (r 0).2.2.2.2.2.2
  have g11 : c 2 1 = c 1 1 + c 1 2 := (r 1).1
  have g12 : c 2 2 = c 1 1 + (c 1 2 + c 1 3) := (r 1).2.1
  have g13 : c 2 3 = c 1 2 + (c 1 3 + c 1 4) := (r 1).2.2.1
  have g14 : c 2 4 = c 1 3 + (c 1 4 + c 1 5) := (r 1).2.2.2.1
  have g15 : c 2 5 = c 1 4 + (c 1 5 + c 1 6) := (r 1).2.2.2.2.1
  have g16 : c 2 6 = c 1 5 + (c 1 6 + c 1 7) := (r 1).2.2.2.2.2.1
  have g21 : c 3 1 = c 2 1 + c 2 2 := (r 2).1
  have g22 : c 3 2 = c 2 1 + (c 2 2 + c 2 3) := (r 2).2.1
  have g23 : c 3 3 = c 2 2 + (c 2 3 + c 2 4) := (r 2).2.2.1
  have g24 : c 3 4 = c 2 3 + (c 2 4 + c 2 5) := (r 2).2.2.2.1
  have g25 : c 3 5 = c 2 4 + (c 2 5 + c 2 6) := (r 2).2.2.2.2.1
  have g31 : c 4 1 = c 3 1 + c 3 2 := (r 3).1
  have g32 : c 4 2 = c 3 1 + (c 3 2 + c 3 3) := (r 3).2.1
  have g33 : c 4 3 = c 3 2 + (c 3 3 + c 3 4) := (r 3).2.2.1
  have g34 : c 4 4 = c 3 3 + (c 3 4 + c 3 5) := (r 3).2.2.2.1
  have g41 : c 5 1 = c 4 1 + c 4 2 := (r 4).1
  have g42 : c 5 2 = c 4 1 + (c 4 2 + c 4 3) := (r 4).2.1
  have g43 : c 5 3 = c 4 2 + (c 4 3 + c 4 4) := (r 4).2.2.1
  have g51 : c 6 1 = c 5 1 + c 5 2 := (r 5).1
  have g52 : c 6 2 = c 5 1 + (c 5 2 + c 5 3) := (r 5).2.1
  have g61 : c 7 1 = c 6 1 + c 6 2 := (r 6).1
  have v1 : a 1 = 1 := by
    rw [ha]
    omega
  have v2 : a 2 = 2 := by
    rw [ha]
    omega
  have v3 : a 3 = 4 := by
    rw [ha]
    omega
  have v4 : a 4 = 9 := by
    rw [ha]
    omega
  have v5 : a 5 = 21 := by
    rw [ha]
    omega
  have v6 : a 6 = 51 := by
    rw [ha]
    omega
  have v7 : a 7 = 127 := by
    rw [ha]
    omega
  have hrec : ∀ n : ℕ, 7 ≤ n → (a n : ℤ) = 7 * a (n - 1) - 15 * a (n - 2) + 5 * a (n - 3) +
      15 * a (n - 4) - 9 * a (n - 5) - 3 * a (n - 6) + a (n - 7) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    rw [show m + 7 - 1 = m + 6 by omega,
      show m + 7 - 2 = m + 5 by omega,
      show m + 7 - 3 = m + 4 by omega,
      show m + 7 - 4 = m + 3 by omega,
      show m + 7 - 5 = m + 2 by omega,
      show m + 7 - 6 = m + 1 by omega,
      show m + 7 - 7 = m by omega]
    simp only [ha]
    have e01 : (c (m + 1) 1 : ℤ) =
        (c m 1 : ℤ) + (c m 2 : ℤ) := by
      exact_mod_cast (r m).1
    have e03 : (c (m + 1) 3 : ℤ) =
        (c m 2 : ℤ) + ((c m 3 : ℤ) + (c m 4 : ℤ)) := by
      exact_mod_cast (r m).2.2.1
    have e04 : (c (m + 1) 4 : ℤ) =
        (c m 3 : ℤ) + ((c m 4 : ℤ) + (c m 5 : ℤ)) := by
      exact_mod_cast (r m).2.2.2.1
    have e06 : (c (m + 1) 6 : ℤ) =
        (c m 5 : ℤ) + ((c m 6 : ℤ) + (c m 7 : ℤ)) := by
      exact_mod_cast (r m).2.2.2.2.2.1
    have e07 : (c (m + 1) 7 : ℤ) =
        (c m 6 : ℤ) + (c m 7 : ℤ) := by
      exact_mod_cast (r m).2.2.2.2.2.2
    have e11 : (c (m + 2) 1 : ℤ) =
        (c (m + 1) 1 : ℤ) + (c (m + 1) 2 : ℤ) := by
      exact_mod_cast (r (m + 1)).1
    have e12 : (c (m + 2) 2 : ℤ) =
        (c (m + 1) 1 : ℤ) + ((c (m + 1) 2 : ℤ) + (c (m + 1) 3 : ℤ)) := by
      exact_mod_cast (r (m + 1)).2.1
    have e13 : (c (m + 2) 3 : ℤ) =
        (c (m + 1) 2 : ℤ) + ((c (m + 1) 3 : ℤ) + (c (m + 1) 4 : ℤ)) := by
      exact_mod_cast (r (m + 1)).2.2.1
    have e14 : (c (m + 2) 4 : ℤ) =
        (c (m + 1) 3 : ℤ) + ((c (m + 1) 4 : ℤ) + (c (m + 1) 5 : ℤ)) := by
      exact_mod_cast (r (m + 1)).2.2.2.1
    have e15 : (c (m + 2) 5 : ℤ) =
        (c (m + 1) 4 : ℤ) + ((c (m + 1) 5 : ℤ) + (c (m + 1) 6 : ℤ)) := by
      exact_mod_cast (r (m + 1)).2.2.2.2.1
    have e16 : (c (m + 2) 6 : ℤ) =
        (c (m + 1) 5 : ℤ) + ((c (m + 1) 6 : ℤ) + (c (m + 1) 7 : ℤ)) := by
      exact_mod_cast (r (m + 1)).2.2.2.2.2.1
    have e21 : (c (m + 3) 1 : ℤ) =
        (c (m + 2) 1 : ℤ) + (c (m + 2) 2 : ℤ) := by
      exact_mod_cast (r (m + 2)).1
    have e22 : (c (m + 3) 2 : ℤ) =
        (c (m + 2) 1 : ℤ) + ((c (m + 2) 2 : ℤ) + (c (m + 2) 3 : ℤ)) := by
      exact_mod_cast (r (m + 2)).2.1
    have e23 : (c (m + 3) 3 : ℤ) =
        (c (m + 2) 2 : ℤ) + ((c (m + 2) 3 : ℤ) + (c (m + 2) 4 : ℤ)) := by
      exact_mod_cast (r (m + 2)).2.2.1
    have e24 : (c (m + 3) 4 : ℤ) =
        (c (m + 2) 3 : ℤ) + ((c (m + 2) 4 : ℤ) + (c (m + 2) 5 : ℤ)) := by
      exact_mod_cast (r (m + 2)).2.2.2.1
    have e25 : (c (m + 3) 5 : ℤ) =
        (c (m + 2) 4 : ℤ) + ((c (m + 2) 5 : ℤ) + (c (m + 2) 6 : ℤ)) := by
      exact_mod_cast (r (m + 2)).2.2.2.2.1
    have e32 : (c (m + 4) 2 : ℤ) =
        (c (m + 3) 1 : ℤ) + ((c (m + 3) 2 : ℤ) + (c (m + 3) 3 : ℤ)) := by
      exact_mod_cast (r (m + 3)).2.1
    have e33 : (c (m + 4) 3 : ℤ) =
        (c (m + 3) 2 : ℤ) + ((c (m + 3) 3 : ℤ) + (c (m + 3) 4 : ℤ)) := by
      exact_mod_cast (r (m + 3)).2.2.1
    have e34 : (c (m + 4) 4 : ℤ) =
        (c (m + 3) 3 : ℤ) + ((c (m + 3) 4 : ℤ) + (c (m + 3) 5 : ℤ)) := by
      exact_mod_cast (r (m + 3)).2.2.2.1
    have e41 : (c (m + 5) 1 : ℤ) =
        (c (m + 4) 1 : ℤ) + (c (m + 4) 2 : ℤ) := by
      exact_mod_cast (r (m + 4)).1
    have e42 : (c (m + 5) 2 : ℤ) =
        (c (m + 4) 1 : ℤ) + ((c (m + 4) 2 : ℤ) + (c (m + 4) 3 : ℤ)) := by
      exact_mod_cast (r (m + 4)).2.1
    have e43 : (c (m + 5) 3 : ℤ) =
        (c (m + 4) 2 : ℤ) + ((c (m + 4) 3 : ℤ) + (c (m + 4) 4 : ℤ)) := by
      exact_mod_cast (r (m + 4)).2.2.1
    have e51 : (c (m + 6) 1 : ℤ) =
        (c (m + 5) 1 : ℤ) + (c (m + 5) 2 : ℤ) := by
      exact_mod_cast (r (m + 5)).1
    have e52 : (c (m + 6) 2 : ℤ) =
        (c (m + 5) 1 : ℤ) + ((c (m + 5) 2 : ℤ) + (c (m + 5) 3 : ℤ)) := by
      exact_mod_cast (r (m + 5)).2.1
    have e61 : (c (m + 7) 1 : ℤ) =
        (c (m + 6) 1 : ℤ) + (c (m + 6) 2 : ℤ) := by
      exact_mod_cast (r (m + 6)).1
    linear_combination (1 : ℤ) * e01 +
      (-1 : ℤ) * e03 +
      (1 : ℤ) * e04 +
      (-1 : ℤ) * e06 +
      (1 : ℤ) * e07 +
      (2 : ℤ) * e11 +
      (-4 : ℤ) * e12 +
      (2 : ℤ) * e13 +
      (1 : ℤ) * e14 +
      (-2 : ℤ) * e15 +
      (1 : ℤ) * e16 +
      (-9 : ℤ) * e21 +
      (2 : ℤ) * e22 +
      (3 : ℤ) * e23 +
      (-3 : ℤ) * e24 +
      (1 : ℤ) * e25 +
      (6 : ℤ) * e32 +
      (-4 : ℤ) * e33 +
      (1 : ℤ) * e34 +
      (10 : ℤ) * e41 +
      (-5 : ℤ) * e42 +
      (1 : ℤ) * e43 +
      (-6 : ℤ) * e51 +
      (1 : ℤ) * e52 +
      (1 : ℤ) * e61
  refine ⟨hrec, ?_⟩
  have q1 : (a 1 : ℚ) = 1 := by exact_mod_cast v1
  have q2 : (a 2 : ℚ) = 2 := by exact_mod_cast v2
  have q3 : (a 3 : ℚ) = 4 := by exact_mod_cast v3
  have q4 : (a 4 : ℚ) = 9 := by exact_mod_cast v4
  have q5 : (a 5 : ℚ) = 21 := by exact_mod_cast v5
  have q6 : (a 6 : ℚ) = 51 := by exact_mod_cast v6
  have q7 : (a 7 : ℚ) = 127 := by exact_mod_cast v7
  obtain ⟨A, hA⟩ : ∃ A : PowerSeries ℚ,
      A = PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) := ⟨_, rfl⟩
  rw [← hA]
  have cA : ∀ m, PowerSeries.coeff m A = if m = 0 then (0 : ℚ) else (a m : ℚ) := by
    intro m
    rw [hA, PowerSeries.coeff_mk]
  have h2 : (PowerSeries.C (2 : ℚ) : PowerSeries ℚ) = 2 := map_ofNat _ 2
  have h3 : (PowerSeries.C (3 : ℚ) : PowerSeries ℚ) = 3 := map_ofNat _ 3
  have h5 : (PowerSeries.C (5 : ℚ) : PowerSeries ℚ) = 5 := map_ofNat _ 5
  have h6 : (PowerSeries.C (6 : ℚ) : PowerSeries ℚ) = 6 := map_ofNat _ 6
  have h7 : (PowerSeries.C (7 : ℚ) : PowerSeries ℚ) = 7 := map_ofNat _ 7
  have h9 : (PowerSeries.C (9 : ℚ) : PowerSeries ℚ) = 9 := map_ofNat _ 9
  have h15 : (PowerSeries.C (15 : ℚ) : PowerSeries ℚ) = 15 := map_ofNat _ 15
  have e : A * ((PowerSeries.X - 1) * (PowerSeries.X ^ 2 + 2 * PowerSeries.X - 1) *
      (PowerSeries.X ^ 4 - 4 * PowerSeries.X ^ 3 - 2 * PowerSeries.X ^ 2 + 4 * PowerSeries.X - 1)) =
      PowerSeries.C (7 : ℚ) * (A * PowerSeries.X ^ 1) + PowerSeries.C (15 : ℚ) * (A * PowerSeries.X ^ 4) +
        PowerSeries.C (5 : ℚ) * (A * PowerSeries.X ^ 3) + A * PowerSeries.X ^ 7 - A -
        PowerSeries.C (15 : ℚ) * (A * PowerSeries.X ^ 2) - PowerSeries.C (9 : ℚ) * (A * PowerSeries.X ^ 5) -
        PowerSeries.C (3 : ℚ) * (A * PowerSeries.X ^ 6) := by
    rw [h7, h15, h5, h9, h3]
    ring
  have e2 : (-PowerSeries.X * (1 - 5 * PowerSeries.X + 5 * PowerSeries.X ^ 2 + 6 * PowerSeries.X ^ 3 -
      7 * PowerSeries.X ^ 4 - 2 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6) : PowerSeries ℚ) =
      -PowerSeries.X ^ 1 + PowerSeries.C (5 : ℚ) * PowerSeries.X ^ 2 - PowerSeries.C (5 : ℚ) * PowerSeries.X ^ 3 -
        PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 4 + PowerSeries.C (7 : ℚ) * PowerSeries.X ^ 5 +
        PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 6 - PowerSeries.X ^ 7 := by
    rw [h5, h6, h7, h2]
    ring
  refine e.trans (Eq.trans ?_ e2.symm)
  ext m
  simp only [map_add, map_sub, map_neg, PowerSeries.coeff_C_mul]
  rcases Nat.lt_or_ge m 8 with hm | hm
  · interval_cases m <;> simp only [PowerSeries.coeff_mul_X_pow', cA, PowerSeries.coeff_X_pow] <;>
      norm_num [q1, q2, q3, q4, q5, q6, q7]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 8 := ⟨m - 8, by omega⟩
    have t0 : PowerSeries.coeff (k + 8) A = (a (k + 8) : ℚ) := by
      rw [cA, if_neg (show ¬(k + 8 = 0) by omega)]
    have t1 : PowerSeries.coeff (k + 8) (A * PowerSeries.X ^ 1) = (a (k + 7) : ℚ) := by
      rw [show k + 8 = k + 7 + 1 by omega, PowerSeries.coeff_mul_X_pow, cA,
        if_neg (show ¬(k + 7 = 0) by omega)]
    have t2 : PowerSeries.coeff (k + 8) (A * PowerSeries.X ^ 2) = (a (k + 6) : ℚ) := by
      rw [show k + 8 = k + 6 + 2 by omega, PowerSeries.coeff_mul_X_pow, cA,
        if_neg (show ¬(k + 6 = 0) by omega)]
    have t3 : PowerSeries.coeff (k + 8) (A * PowerSeries.X ^ 3) = (a (k + 5) : ℚ) := by
      rw [show k + 8 = k + 5 + 3 by omega, PowerSeries.coeff_mul_X_pow, cA,
        if_neg (show ¬(k + 5 = 0) by omega)]
    have t4 : PowerSeries.coeff (k + 8) (A * PowerSeries.X ^ 4) = (a (k + 4) : ℚ) := by
      rw [show k + 8 = k + 4 + 4 by omega, PowerSeries.coeff_mul_X_pow, cA,
        if_neg (show ¬(k + 4 = 0) by omega)]
    have t5 : PowerSeries.coeff (k + 8) (A * PowerSeries.X ^ 5) = (a (k + 3) : ℚ) := by
      rw [show k + 8 = k + 3 + 5 by omega, PowerSeries.coeff_mul_X_pow, cA,
        if_neg (show ¬(k + 3 = 0) by omega)]
    have t6 : PowerSeries.coeff (k + 8) (A * PowerSeries.X ^ 6) = (a (k + 2) : ℚ) := by
      rw [show k + 8 = k + 2 + 6 by omega, PowerSeries.coeff_mul_X_pow, cA,
        if_neg (show ¬(k + 2 = 0) by omega)]
    have t7 : PowerSeries.coeff (k + 8) (A * PowerSeries.X ^ 7) = (a (k + 1) : ℚ) := by
      rw [show k + 8 = k + 1 + 7 by omega, PowerSeries.coeff_mul_X_pow, cA,
        if_neg (show ¬(k + 1 = 0) by omega)]
    have u1 : PowerSeries.coeff (k + 8) (PowerSeries.X ^ 1 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 8 = 1) by omega)]
    have u2 : PowerSeries.coeff (k + 8) (PowerSeries.X ^ 2 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 8 = 2) by omega)]
    have u3 : PowerSeries.coeff (k + 8) (PowerSeries.X ^ 3 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 8 = 3) by omega)]
    have u4 : PowerSeries.coeff (k + 8) (PowerSeries.X ^ 4 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 8 = 4) by omega)]
    have u5 : PowerSeries.coeff (k + 8) (PowerSeries.X ^ 5 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 8 = 5) by omega)]
    have u6 : PowerSeries.coeff (k + 8) (PowerSeries.X ^ 6 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 8 = 6) by omega)]
    have u7 : PowerSeries.coeff (k + 8) (PowerSeries.X ^ 7 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 8 = 7) by omega)]
    rw [t0, t1, t2, t3, t4, t5, t6, t7, u1, u2, u3, u4, u5, u6, u7]
    have h := hrec (k + 8) (by omega)
    rw [show k + 8 - 1 = k + 7 by omega,
      show k + 8 - 2 = k + 6 by omega,
      show k + 8 - 3 = k + 5 by omega,
      show k + 8 - 4 = k + 4 by omega,
      show k + 8 - 5 = k + 3 by omega,
      show k + 8 - 6 = k + 2 by omega,
      show k + 8 - 7 = k + 1 by omega] at h
    have hq := congrArg (fun z : ℤ => (z : ℚ)) h
    push_cast at hq
    linear_combination (-1 : ℚ) * hq
