import OMAStatements.S_oeis_a050129

-- Credit: @frido22 (complete proof and case certificates).
-- Independent audit and proof-stage assembly: @CubeJerry.
-- uses note #93815
-- Source: https://github.com/frido22/open-math-agents/blob/faa4e268123181dc368655497366ca4144bbf644/proofs/oeis-a050129.lean

/-!
Kimberling's forward sequence is A050128, and Israel's first-occurrence conjecture is A050129.
The deadline and injectivity first reduce the problem to seven possible positions. A run
of at most three halvings gives four possible forms at each time. In the six residue cases
below, the recurrence and injectivity exclude the extra position 4n+4. Each local clause
comes from the numbered time or pair of times given in its proof. The propositional
contradictions are checked inside Lean.

A related deadline argument for the reset-to-3n sequence appears in Franklin T. Adams-Watters's
2006 comment on https://oeis.org/A050132.
-/

namespace OMA.Halving

open OMA.S_oeis_a050129

private abbrev seen (t : ℕ) := (state t).seen
private def reset (t : ℕ) := value t = 2*t

private lemma nextValue {t : ℕ} (ht : 0 < t) : value (t+1) =
    if value t / 2 ∈ seen t then 2*(t+1) else value t / 2 := by
  cases t with
  | zero => omega
  | succ t => rfl

private lemma seenStep (t : ℕ) : seen (t+1) = insert (value (t+1)) (seen t) := by
  cases t with
  | zero => decide +kernel
  | succ t => rfl

private lemma seenMono {i j : ℕ} (h : i ≤ j) : seen i ⊆ seen j := by
  induction j, h using Nat.le_induction with
  | base => rfl
  | succ j _ ih => rw [seenStep]; exact ih.trans (Finset.subset_insert _ _)

private lemma occurs {x t : ℕ} : x ∈ seen t ↔ ∃ j ≤ t, value j = x := by
  induction t with
  | zero => simp [seen, state, value, eq_comm]
  | succ t ih =>
    rw [seenStep, Finset.mem_insert, ih]
    constructor
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact ⟨_, le_rfl, rfl⟩
      · exact ⟨j, by omega, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      rcases Nat.eq_or_lt_of_le hj with rfl | h
      · exact .inl rfl
      · exact .inr ⟨_, by omega, rfl⟩

private lemma selfSeen (t : ℕ) : value t ∈ seen t := occurs.mpr ⟨t, le_rfl, rfl⟩

private lemma valueBound (t : ℕ) : value t ≤ 2*t := by
  induction t with
  | zero => decide
  | succ t ih =>
    by_cases ht : t = 0
    · subst t; decide
    · rw [nextValue (by omega)]; split <;> omega

private lemma fresh (t : ℕ) : value (t+1) ∉ seen t := by
  by_cases ht : t = 0
  · subst t; decide
  rw [nextValue (by omega)]
  split
  · intro h
    obtain ⟨j, hj, eq⟩ := occurs.mp h
    have := valueBound j; omega
  · assumption

private lemma positive {t : ℕ} (ht : 0 < t) : 0 < value t := by
  obtain ⟨j, rfl⟩ : ∃ j, t = j+1 := ⟨t-1, by omega⟩
  have hz : 0 ∈ seen j := occurs.mpr ⟨0, Nat.zero_le _, rfl⟩
  have hf := fresh j
  by_contra! h
  exact hf ((show value (j+1) = 0 by omega) ▸ hz)

private lemma uniqueIndex {i j : ℕ} (h : value i = value j) : i = j := by
  wlog hle : i ≤ j generalizing i j
  · exact (this h.symm (by omega)).symm
  by_contra! ne
  obtain ⟨t, rfl⟩ : ∃ t, j = t+1 := ⟨j-1, by omega⟩
  exact fresh t (occurs.mpr ⟨i, by omega, h⟩)

private lemma halve {t : ℕ} (ht : 0 < t) (hr : ¬ reset (t+1)) : value (t+1) = value t / 2 := by
  unfold reset at hr
  rw [nextValue ht] at hr ⊢
  split <;> simp_all

/-- Once a value has appeared, its parent in the binary tree is present one step later. -/
private lemma parent {x t : ℕ} (hx : x ∈ seen t) : x/2 ∈ seen (t+1) := by
  obtain ⟨j, hj, rfl⟩ := occurs.mp hx
  apply seenMono (show j+1 ≤ t+1 by omega)
  by_cases old : value j / 2 ∈ seen j
  · exact seenMono (Nat.le_succ _) old
  · have jpos : 0 < j := by
      by_contra! h
      have hj0 : j = 0 := by omega
      subst j
      exact old (by decide)
    exact occurs.mpr ⟨_, le_rfl, by rw [nextValue jpos, if_neg old]⟩

/-- Every positive value occurs, and its first occurrence is at most `4*n+5`. -/
private lemma deadline (n : ℕ) : n ∈ seen (4*n+5) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n ≤ 1
    · interval_cases n <;> decide +kernel
    have start (t : ℕ) (ht : 4*n ≤ t) (he : t ≤ 4*n+2) (hr : reset t) : n ∈ seen (4*n+5) := by
      have occ : 2*t ∈ seen t := hr ▸ selfSeen t
      have h := parent (parent (parent occ))
      have eq : 2*t/2/2/2 = n := by omega
      rw [eq] at h
      exact seenMono (by omega) h
    by_cases h₀ : reset (4*n)
    · exact start _ (by omega) (by omega) h₀
    by_cases h₁ : reset (4*n+1)
    · exact start _ (by omega) (by omega) h₁
    by_cases h₂ : reset (4*n+2)
    · exact start _ (by omega) (by omega) h₂
    have v₀ : value (4*n) = value (4*n-1)/2 := by
      have eq : 4*n-1+1 = 4*n := by omega
      simpa only [eq] using halve (t := 4*n-1) (by omega) (by simpa only [eq] using h₀)
    have v₁ := halve (t := 4*n) (by omega) h₁
    have v₂ := halve (t := 4*n+1) (by omega) h₂
    have bound := valueBound (4*n-1)
    change value (4*n+2) = value (4*n+1)/2 at v₂
    have lower : value (4*n+2) < n := by rw [v₂, v₁, v₀]; omega
    have old := ih _ lower
    have hit : value (4*n+2) ∈ seen (4*n+1) := seenMono (by omega) old
    exact False.elim (fresh (4*n+1) hit)

private lemma atStep {k : ℕ} (hk : 2 ≤ k) : reset k ∨ value k = value (k-1)/2 := by
  by_cases h : reset k
  · exact .inl h
  · have eq : k-1+1 = k := by omega
    exact .inr (by simpa only [eq] using halve (t := k-1) (by omega) (by simpa only [eq] using h))

private def six (n k : ℕ) : Prop :=
  2*k = n ∨ k = n+1 ∨ k = 2*n+2 ∨ k = 2*n+3 ∨ k = 4*n+3 ∨ k = 4*n+5

/-- Three halvings after a reset leave just one potential extra position. -/
private lemma seven {n k : ℕ} (hn : 1 < n) (hv : value k = n) : six n k ∨ k = 4*n+4 := by
  obtain ⟨i, hi, hval⟩ := occurs.mp (deadline n)
  have limit : k ≤ 4*n+5 := (uniqueIndex (hv.trans hval.symm)) ▸ hi
  unfold six
  by_cases small : k ≤ 5
  · interval_cases k <;> norm_num [value, state] at hv <;> omega
  obtain r | h₀ := atStep (k := k) (by omega)
  · unfold reset at r; omega
  obtain r | h₁ := atStep (k := k-1) (by omega)
  · unfold reset at r; rw [r] at h₀; omega
  obtain r | h₂ := atStep (k := k-2) (by omega)
  · unfold reset at r
    rw [show k-1-1 = k-2 by omega, r] at h₁
    rw [h₁] at h₀
    omega
  obtain r | h₃ := atStep (k := k-3) (by omega)
  · unfold reset at r
    rw [show k-2-1 = k-3 by omega, r] at h₂
    rw [show k-1-1 = k-2 by omega, h₂] at h₁
    rw [h₁] at h₀
    omega
  · rw [show k-3-1 = k-4 by omega] at h₃
    rw [show k-2-1 = k-3 by omega, h₃] at h₂
    rw [show k-1-1 = k-2 by omega, h₂] at h₁
    rw [h₁] at h₀
    have := valueBound (k-4)
    omega

/-- The four possible forms at time t after zero through three halvings. -/
private def form (t d : ℕ) : ℕ := 2*(t-d) / 2^d
private def tag (t d : ℕ) : Bool := decide (value t = form t d)

private lemma tagged {t d} : tag t d ↔ value t = form t d := by simp [tag]

private lemma optionsAt {t : ℕ} (ht : 6 ≤ t) : tag t 0 ∨ tag t 1 ∨ tag t 2 ∨ tag t 3 := by
  have pos := positive (t := t) (by omega)
  have gt : 1 < value t := by
    by_contra! h
    have e : value t = value 1 := by change value t = 1; omega
    have := uniqueIndex e; omega
  have sevenfold := seven gt (rfl : value t = value t)
  simp only [tagged, form, six] at *
  norm_num at *; omega

private lemma distinctForms {t d e : ℕ} (h : form t d ≠ form t e) : ¬ tag t d ∨ ¬ tag t e := by
  simp only [tagged]; omega

private lemma differentTimes {t i d e : ℕ} (hne : t ≠ i) (same : form t d = form i e) :
    ¬ tag t d ∨ ¬ tag i e := by
  by_cases h : tag t d
  · exact .inr (fun hh => hne (uniqueIndex ((tagged.mp h).trans (same.trans (tagged.mp hh).symm))))
  · exact .inl h

private lemma shortRun {t d : ℕ} (ht : 0 < t) (hs : form t d / 2 = form (t+1) (d+1)) :
    ¬ tag t d ∨ tag (t+1) 0 ∨ tag (t+1) (d+1) := by
  simp only [tagged]
  by_cases h : value t = form t d
  · right; rw [nextValue ht]; split
    · exact .inl (by simp [form])
    · exact .inr (by rw [h, hs])
  · exact .inl h

private lemma mustReset {t : ℕ} (ht : 16 ≤ t) : ¬ tag t 3 ∨ tag (t+1) 0 := by
  by_cases cur : tag t 3
  · right
    have h := shortRun (t := t) (d := 3) (by omega) (by unfold form; norm_num; omega)
    rcases h with h | h | h
    · contradiction
    · exact h
    · have disj := optionsAt (t := t+1) (by omega)
      simp only [tagged, form] at cur h disj; norm_num at *; omega
  · exact .inl cur

private lemma alreadySeen {t i d e : ℕ} (ht : 0 < t) (hle : i ≤ t) (hs : form t d/2 = form i e) :
    ¬ tag t d ∨ ¬ tag i e ∨ tag (t+1) 0 := by
  by_cases hx : tag t d <;> [skip; exact .inl hx]
  by_cases hy : tag i e <;> [skip; exact .inr (.inl hy)]
  have mem : value t/2 ∈ seen t := occurs.mpr ⟨i, hle, by rw [tagged.mp hx, hs, tagged.mp hy]⟩
  exact .inr (.inr (tagged.mpr (by rw [nextValue ht, if_pos mem]; simp [form])))

/-- A previous occurrence has one of the seven candidate indices, with the corresponding form. -/
private lemma positionOf {i x : ℕ} (hx : 1 < x) (h : value i = x) :
    (2*i = x ∧ tag i 0) ∨ (i = x+1 ∧ tag i 1) ∨
    (i = 2*x+2 ∧ tag i 2) ∨ (i = 2*x+3 ∧ tag i 2) ∨
    (i = 4*x+3 ∧ tag i 3) ∨ (i = 4*x+4 ∧ tag i 3) ∨ (i = 4*x+5 ∧ tag i 3) := by
  rcases seven hx h with (p | p | p | p | p | p) | p
  · exact .inl ⟨p, tagged.mpr (by norm_num [form]; omega)⟩
  · exact .inr (.inl ⟨p, tagged.mpr (by norm_num [form]; omega)⟩)
  · exact .inr (.inr (.inl ⟨p, tagged.mpr (by norm_num [form]; omega)⟩))
  · exact .inr (.inr (.inr (.inl ⟨p, tagged.mpr (by norm_num [form]; omega)⟩)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨p, tagged.mpr (by norm_num [form]; omega)⟩))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (⟨p, tagged.mpr (by norm_num [form]; omega)⟩))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨p, tagged.mpr (by norm_num [form]; omega)⟩)))))

private lemma beforeReset {t d : ℕ} (ht : 0 < t) (h : tag t d) (r : tag (t+1) 0) :
    ∃ i ≤ t, value i = form t d / 2 := by
  have rt := tagged.mp r
  have bound := valueBound t
  simp only [form, Nat.sub_zero, pow_zero, Nat.div_one] at rt
  rw [nextValue ht] at rt
  split at rt
  · obtain ⟨i, hi, hv⟩ := occurs.mp ‹value t/2 ∈ seen t›
    exact ⟨i, hi, hv.trans (by rw [tagged.mp h])⟩
  · omega

private lemma ruledOut {n t : ℕ} (ht : 16 ≤ t)
    (ih : ∀ x i, 1 < x → x < n → value i = x → six x i)
    (cut : (t % 4 = 2) ∨ (t % 2 = 0 ∧ t < 4*n+4)) : ¬ tag t 3 := by
  intro h
  have hv := tagged.mp h
  simp only [form] at hv; norm_num at hv
  have hx : 1 < value t := by omega
  rcases cut with always | ⟨even, earlier⟩
  · have hs := seven hx (rfl : value t = value t)
    unfold six at hs; omega
  · have hs := ih (value t) t hx (by omega) rfl
    unfold six at hs; omega

private lemma earlier {T : Prop} {t d x : ℕ} (ht : 0 < t) (eq : form t d / 2 = x)
    (found : ∀ i ≤ t, value i = x → T) : ¬ tag t d ∨ ¬ tag (t+1) 0 ∨ T := by
  by_cases a : tag t d
  · by_cases b : tag (t+1) 0
    · obtain ⟨i, hi, hv⟩ := beforeReset ht a b
      exact .inr (.inr (found i hi (hv.trans eq)))
    · exact .inr (.inl b)
  · exact .inl a


set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
private lemma initial : ∀ n ∈ Finset.range 128, 1 < n → value (4*n+4) ≠ n := by decide +kernel


set_option maxRecDepth 6000 in
set_option maxHeartbeats 3500000 in
/-- Excludes the extra position for `n = 4q + 128`. -/
private lemma exclude4_0 (q : ℕ) (ih : ∀ x i, 1 < x → x < q*4+128 → value i = x → six x i) :
    ¬ tag (q*16+516) 3 := by
  intro bad
  have c0 := optionsAt (t := (q*2+63)) (by omega)
  have c1 := optionsAt (t := (q*2+64)) (by omega)
  have c2 := ruledOut (t := (q*2+64)) (by omega) ih (by omega)
  have c3 := optionsAt (t := (q*4+127)) (by omega)
  have c4 := optionsAt (t := (q*4+128)) (by omega)
  have c5 := distinctForms (t := (q*4+128)) (d := 1) (e := 2) (by norm_num [form]; omega)
  have c6 := ruledOut (t := (q*4+128)) (by omega) ih (by omega)
  have c7 := optionsAt (t := (q*4+129)) (by omega)
  have c8 := distinctForms (t := (q*4+129)) (d := 2) (e := 3) (by norm_num [form]; omega)
  have c9 := differentTimes (t := (q*2+64)) (i := (q*4+129)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c10 := optionsAt (t := (q*4+126)) (by omega)
  have c11 := ruledOut (t := (q*4+126)) (by omega) ih (by omega)
  have c12 := optionsAt (t := (q*8+253)) (by omega)
  have c13 := differentTimes (t := (q*2+63)) (i := (q*8+253)) (d := 1) (e := 3) (by omega) (by norm_num [form]; omega)
  have c14 := shortRun (t := (q*2+63)) (d := 0) (by omega) (by norm_num [form])
  have c15 := optionsAt (t := (q*8+255)) (by omega)
  have c16 := optionsAt (t := (q*8+256)) (by omega)
  have c17 := ruledOut (t := (q*8+256)) (by omega) ih (by omega)
  have c18 := optionsAt (t := (q*8+257)) (by omega)
  have c19 := differentTimes (t := (q*2+64)) (i := (q*4+128)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c20 := differentTimes (t := (q*4+129)) (i := (q*8+257)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c21 := shortRun (t := (q*2+63)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c22 := mustReset (t := (q*2+63)) (by omega)
  have c23 := optionsAt (t := (q*8+254)) (by omega)
  have c24 := ruledOut (t := (q*8+254)) (by omega) ih (by omega)
  have c25 := optionsAt (t := (q*16+507)) (by omega)
  have c26 := optionsAt (t := (q*16+508)) (by omega)
  have c27 := ruledOut (t := (q*16+508)) (by omega) ih (by omega)
  have c28 := differentTimes (t := (q*4+127)) (i := (q*8+254)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c29 := differentTimes (t := (q*4+127)) (i := (q*16+507)) (d := 1) (e := 3) (by omega) (by norm_num [form]; omega)
  have c30 := shortRun (t := (q*4+126)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c31 := shortRun (t := (q*4+126)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c32 := shortRun (t := (q*4+127)) (d := 0) (by omega) (by norm_num [form])
  have c33 := optionsAt (t := (q*16+511)) (by omega)
  have c34 := ruledOut (t := (q*16+512)) (by omega) ih (by omega)
  have c35 := optionsAt (t := (q*16+513)) (by omega)
  have c36 := differentTimes (t := (q*4+128)) (i := (q*8+256)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c37 := differentTimes (t := (q*4+128)) (i := (q*8+257)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c38 := shortRun (t := (q*4+127)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c39 := mustReset (t := (q*4+127)) (by omega)
  have c40 := optionsAt (t := (q*8+258)) (by omega)
  have c41 := ruledOut (t := (q*8+258)) (by omega) ih (by omega)
  have c42 := optionsAt (t := (q*16+515)) (by omega)
  have c43 := distinctForms (t := (q*16+516)) (d := 0) (e := 3) (by norm_num [form]; omega)
  have c44 := distinctForms (t := (q*16+516)) (d := 1) (e := 3) (by norm_num [form]; omega)
  have c45 := distinctForms (t := (q*16+516)) (d := 2) (e := 3) (by norm_num [form]; omega)
  have c46 := differentTimes (t := (q*2+64)) (i := (q*16+516)) (d := 0) (e := 3) (by omega) (by norm_num [form]; omega)
  have c47 := differentTimes (t := (q*4+129)) (i := (q*16+516)) (d := 1) (e := 3) (by omega) (by norm_num [form]; omega)
  have c48 := differentTimes (t := (q*8+258)) (i := (q*16+516)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c49 := differentTimes (t := (q*8+259)) (i := (q*16+516)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c50 := differentTimes (t := (q*16+515)) (i := (q*16+516)) (d := 3) (e := 3) (by omega) (by norm_num [form]; omega)
  have c51 := shortRun (t := (q*4+128)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c52 := shortRun (t := (q*4+128)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c53 := differentTimes (t := (q*4+126)) (i := (q*8+253)) (d := 0) (e := 1) (by omega) (by norm_num [form]; omega)
  have c54 := differentTimes (t := (q*4+126)) (i := (q*16+507)) (d := 0) (e := 2) (by omega) (by norm_num [form]; omega)
  have c55 := differentTimes (t := (q*8+254)) (i := (q*16+508)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c56 := differentTimes (t := (q*8+254)) (i := (q*16+509)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c57 := shortRun (t := (q*8+253)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c58 := distinctForms (t := (q*16+510)) (d := 1) (e := 2) (by norm_num [form]; omega)
  have c59 : ¬ tag (q*8+254) 0 ∨ ¬ tag (q*8+255) 0 ∨ tag (q*4+127) 0 := by
    clear * - q
    apply earlier (t := (q*8+254)) (d := 0) (x := (q*8+254)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*4+127 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c60 := shortRun (t := (q*8+255)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c61 := shortRun (t := (q*8+255)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c62 := mustReset (t := (q*8+255)) (by omega)
  have c63 := shortRun (t := (q*8+256)) (d := 0) (by omega) (by norm_num [form])
  have c64 := ruledOut (t := (q*16+514)) (by omega) ih (by omega)
  have c65 := differentTimes (t := (q*4+128)) (i := (q*16+515)) (d := 0) (e := 2) (by omega) (by norm_num [form]; omega)
  have c66 := differentTimes (t := (q*8+257)) (i := (q*16+515)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c67 := alreadySeen (t := (q*8+256)) (i := (q*4+128)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c68 := alreadySeen (t := (q*8+256)) (i := (q*4+128)) (d := 2) (e := 2) (by omega) (by omega) (by norm_num [form]; omega)
  have c69 : ¬ tag (q*8+257) 0 ∨ ¬ tag (q*8+258) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*8+257)) (d := 0) (x := (q*8+257)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c70 := alreadySeen (t := (q*8+258)) (i := (q*4+129)) (d := 0) (e := 0) (by omega) (by omega) (by norm_num [form]; omega)
  have c71 := shortRun (t := (q*8+258)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c72 : ¬ tag (q*8+258) 1 ∨ ¬ tag (q*8+259) 0 ∨ tag (q*2+64) 0 ∨ tag (q*4+129) 1 ∨ tag (q*8+258) 2 := by
    clear * - q
    apply earlier (t := (q*8+258)) (d := 1) (x := (q*4+128)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact .inl ((show i = q*2+64 by omega) ▸ a)
    · exact .inr (.inl ((show i = q*4+129 by omega) ▸ a))
    · exact .inr (.inr (((show i = q*8+258 by omega) ▸ a)))
    · omega
    · omega
    · omega
    · omega
  have c73 := differentTimes (t := (q*8+253)) (i := (q*16+507)) (d := 0) (e := 1) (by omega) (by norm_num [form]; omega)
  have c74 : ¬ tag (q*16+507) 0 ∨ ¬ tag (q*16+508) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*16+507)) (d := 0) (x := (q*16+507)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c75 := shortRun (t := (q*16+508)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c76 := shortRun (t := (q*16+509)) (d := 0) (by omega) (by norm_num [form])
  have c77 : ¬ tag (q*16+509) 0 ∨ ¬ tag (q*16+510) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*16+509)) (d := 0) (x := (q*16+509)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c78 : ¬ tag (q*16+510) 1 ∨ ¬ tag (q*16+511) 0 ∨ tag (q*4+127) 0 ∨ tag (q*8+255) 1 ∨ tag (q*16+510) 2 := by
    clear * - q
    apply earlier (t := (q*16+510)) (d := 1) (x := (q*8+254)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact .inl ((show i = q*4+127 by omega) ▸ a)
    · exact .inr (.inl ((show i = q*8+255 by omega) ▸ a))
    · exact .inr (.inr (((show i = q*16+510 by omega) ▸ a)))
    · omega
    · omega
    · omega
    · omega
  have c79 := alreadySeen (t := (q*16+511)) (i := (q*8+256)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c80 := shortRun (t := (q*16+511)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c81 := mustReset (t := (q*16+511)) (by omega)
  have c82 : ¬ tag (q*16+512) 0 ∨ ¬ tag (q*16+513) 0 ∨ tag (q*8+256) 0 := by
    clear * - q
    apply earlier (t := (q*16+512)) (d := 0) (x := (q*16+512)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*8+256 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c83 := shortRun (t := (q*16+513)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c84 := shortRun (t := (q*16+513)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c85 := mustReset (t := (q*16+513)) (by omega)
  have c86 := shortRun (t := (q*16+514)) (d := 0) (by omega) (by norm_num [form])
  have c87 := shortRun (t := (q*16+514)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c88 := shortRun (t := (q*16+515)) (d := 0) (by omega) (by norm_num [form])
  have c89 := shortRun (t := (q*16+515)) (d := 1) (by omega) (by norm_num [form]; omega)
  grind (splits := 256) only


set_option maxRecDepth 6000 in
set_option maxHeartbeats 3500000 in
/-- Excludes the extra position for `n = 4q + 129`. -/
private lemma exclude4_1 (q : ℕ) (ih : ∀ x i, 1 < x → x < q*4+129 → value i = x → six x i) :
    ¬ tag (q*16+520) 3 := by
  intro bad
  have c0 := optionsAt (t := (q*2+62)) (by omega)
  have c1 := ruledOut (t := (q*2+62)) (by omega) ih (by omega)
  have c2 := optionsAt (t := (q*2+63)) (by omega)
  have c3 := optionsAt (t := (q*4+125)) (by omega)
  have c4 := optionsAt (t := (q*2+64)) (by omega)
  have c5 := ruledOut (t := (q*2+64)) (by omega) ih (by omega)
  have c6 := optionsAt (t := (q*4+127)) (by omega)
  have c7 := optionsAt (t := (q*4+128)) (by omega)
  have c8 := ruledOut (t := (q*4+128)) (by omega) ih (by omega)
  have c9 := optionsAt (t := (q*4+129)) (by omega)
  have c10 := optionsAt (t := (q*4+126)) (by omega)
  have c11 := ruledOut (t := (q*4+126)) (by omega) ih (by omega)
  have c12 := optionsAt (t := (q*8+251)) (by omega)
  have c13 := optionsAt (t := (q*8+252)) (by omega)
  have c14 := ruledOut (t := (q*8+252)) (by omega) ih (by omega)
  have c15 := optionsAt (t := (q*8+253)) (by omega)
  have c16 := differentTimes (t := (q*2+63)) (i := (q*4+126)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c17 := differentTimes (t := (q*2+63)) (i := (q*8+251)) (d := 1) (e := 3) (by omega) (by norm_num [form]; omega)
  have c18 := shortRun (t := (q*2+62)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c19 := shortRun (t := (q*2+62)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c20 := shortRun (t := (q*2+63)) (d := 0) (by omega) (by norm_num [form])
  have c21 := optionsAt (t := (q*8+255)) (by omega)
  have c22 := optionsAt (t := (q*8+256)) (by omega)
  have c23 := ruledOut (t := (q*8+256)) (by omega) ih (by omega)
  have c24 := optionsAt (t := (q*8+257)) (by omega)
  have c25 := differentTimes (t := (q*2+64)) (i := (q*4+128)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c26 := differentTimes (t := (q*4+129)) (i := (q*8+255)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c27 := shortRun (t := (q*2+63)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c28 := mustReset (t := (q*2+63)) (by omega)
  have c29 := optionsAt (t := (q*4+130)) (by omega)
  have c30 := ruledOut (t := (q*4+130)) (by omega) ih (by omega)
  have c31 := optionsAt (t := (q*8+259)) (by omega)
  have c32 := optionsAt (t := (q*8+260)) (by omega)
  have c33 := ruledOut (t := (q*8+260)) (by omega) ih (by omega)
  have c34 := differentTimes (t := (q*4+130)) (i := (q*8+259)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c35 := differentTimes (t := (q*2+62)) (i := (q*8+251)) (d := 0) (e := 2) (by omega) (by norm_num [form]; omega)
  have c36 := optionsAt (t := (q*16+503)) (by omega)
  have c37 := optionsAt (t := (q*16+504)) (by omega)
  have c38 := ruledOut (t := (q*16+504)) (by omega) ih (by omega)
  have c39 := differentTimes (t := (q*4+126)) (i := (q*8+252)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c40 := differentTimes (t := (q*4+126)) (i := (q*16+503)) (d := 1) (e := 3) (by omega) (by norm_num [form]; omega)
  have c41 := alreadySeen (t := (q*4+125)) (i := (q*2+63)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c42 := shortRun (t := (q*4+125)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c43 := mustReset (t := (q*4+125)) (by omega)
  have c44 := ruledOut (t := (q*8+254)) (by omega) ih (by omega)
  have c45 := optionsAt (t := (q*16+507)) (by omega)
  have c46 := ruledOut (t := (q*16+508)) (by omega) ih (by omega)
  have c47 := optionsAt (t := (q*16+509)) (by omega)
  have c48 := differentTimes (t := (q*8+255)) (i := (q*16+507)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c49 := differentTimes (t := (q*8+255)) (i := (q*16+509)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c50 : ¬ tag (q*4+126) 0 ∨ ¬ tag (q*4+127) 0 ∨ tag (q*2+63) 0 := by
    clear * - q
    apply earlier (t := (q*4+126)) (d := 0) (x := (q*4+126)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*2+63 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c51 := optionsAt (t := (q*16+511)) (by omega)
  have c52 := optionsAt (t := (q*16+512)) (by omega)
  have c53 := ruledOut (t := (q*16+512)) (by omega) ih (by omega)
  have c54 := differentTimes (t := (q*4+128)) (i := (q*8+256)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c55 := differentTimes (t := (q*4+128)) (i := (q*16+511)) (d := 1) (e := 3) (by omega) (by norm_num [form]; omega)
  have c56 := shortRun (t := (q*4+127)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c57 := shortRun (t := (q*4+127)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c58 := mustReset (t := (q*4+127)) (by omega)
  have c59 := shortRun (t := (q*4+128)) (d := 0) (by omega) (by norm_num [form])
  have c60 := optionsAt (t := (q*8+258)) (by omega)
  have c61 := distinctForms (t := (q*8+258)) (d := 1) (e := 2) (by norm_num [form]; omega)
  have c62 := ruledOut (t := (q*8+258)) (by omega) ih (by omega)
  have c63 := optionsAt (t := (q*16+515)) (by omega)
  have c64 := optionsAt (t := (q*16+516)) (by omega)
  have c65 := distinctForms (t := (q*16+516)) (d := 1) (e := 2) (by norm_num [form]; omega)
  have c66 := ruledOut (t := (q*16+516)) (by omega) ih (by omega)
  have c67 := optionsAt (t := (q*16+517)) (by omega)
  have c68 := differentTimes (t := (q*2+64)) (i := (q*8+258)) (d := 0) (e := 2) (by omega) (by norm_num [form]; omega)
  have c69 := differentTimes (t := (q*4+129)) (i := (q*8+258)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c70 := differentTimes (t := (q*4+129)) (i := (q*8+259)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c71 := shortRun (t := (q*4+128)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c72 := alreadySeen (t := (q*4+128)) (i := (q*2+64)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c73 := alreadySeen (t := (q*4+128)) (i := (q*2+64)) (d := 2) (e := 2) (by omega) (by omega) (by norm_num [form]; omega)
  have c74 := optionsAt (t := (q*16+519)) (by omega)
  have c75 := distinctForms (t := (q*16+520)) (d := 0) (e := 3) (by norm_num [form]; omega)
  have c76 := distinctForms (t := (q*16+520)) (d := 1) (e := 3) (by norm_num [form]; omega)
  have c77 := distinctForms (t := (q*16+520)) (d := 2) (e := 3) (by norm_num [form]; omega)
  have c78 := differentTimes (t := (q*4+130)) (i := (q*16+520)) (d := 1) (e := 3) (by omega) (by norm_num [form]; omega)
  have c79 := differentTimes (t := (q*8+260)) (i := (q*16+520)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c80 := differentTimes (t := (q*8+261)) (i := (q*16+520)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c81 := differentTimes (t := (q*16+519)) (i := (q*16+520)) (d := 3) (e := 3) (by omega) (by norm_num [form]; omega)
  have c82 := shortRun (t := (q*4+129)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c83 := mustReset (t := (q*4+129)) (by omega)
  have c84 := differentTimes (t := (q*4+125)) (i := (q*16+503)) (d := 0) (e := 2) (by omega) (by norm_num [form]; omega)
  have c85 := differentTimes (t := (q*8+252)) (i := (q*16+504)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c86 := differentTimes (t := (q*8+252)) (i := (q*16+505)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c87 := alreadySeen (t := (q*8+251)) (i := (q*4+126)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c88 := distinctForms (t := (q*16+506)) (d := 1) (e := 2) (by norm_num [form]; omega)
  have c89 : ¬ tag (q*8+252) 0 ∨ ¬ tag (q*8+253) 0 ∨ tag (q*4+126) 0 := by
    clear * - q
    apply earlier (t := (q*8+252)) (d := 0) (x := (q*8+252)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*4+126 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c90 := shortRun (t := (q*8+253)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c91 := shortRun (t := (q*8+253)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c92 := alreadySeen (t := (q*8+253)) (i := (q*2+64)) (d := 3) (e := 2) (by omega) (by omega) (by norm_num [form]; omega)
  have c93 := differentTimes (t := (q*4+127)) (i := (q*8+255)) (d := 0) (e := 1) (by omega) (by norm_num [form]; omega)
  have c94 := differentTimes (t := (q*4+127)) (i := (q*16+510)) (d := 0) (e := 2) (by omega) (by norm_num [form]; omega)
  have c95 := differentTimes (t := (q*4+127)) (i := (q*16+511)) (d := 0) (e := 2) (by omega) (by norm_num [form]; omega)
  have c96 := alreadySeen (t := (q*8+254)) (i := (q*4+127)) (d := 0) (e := 0) (by omega) (by omega) (by norm_num [form]; omega)
  have c97 := alreadySeen (t := (q*8+254)) (i := (q*4+129)) (d := 2) (e := 2) (by omega) (by omega) (by norm_num [form]; omega)
  have c98 := differentTimes (t := (q*8+256)) (i := (q*16+512)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c99 := differentTimes (t := (q*8+256)) (i := (q*16+513)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c100 : ¬ tag (q*8+255) 0 ∨ ¬ tag (q*8+256) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*8+255)) (d := 0) (x := (q*8+255)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c101 := alreadySeen (t := (q*8+255)) (i := (q*4+128)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c102 := shortRun (t := (q*8+255)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c103 := mustReset (t := (q*8+255)) (by omega)
  have c104 := optionsAt (t := (q*16+514)) (by omega)
  have c105 := distinctForms (t := (q*16+514)) (d := 1) (e := 2) (by norm_num [form]; omega)
  have c106 := ruledOut (t := (q*16+514)) (by omega) ih (by omega)
  have c107 : ¬ tag (q*8+256) 0 ∨ ¬ tag (q*8+257) 0 ∨ tag (q*4+128) 0 := by
    clear * - q
    apply earlier (t := (q*8+256)) (d := 0) (x := (q*8+256)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*4+128 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c108 := shortRun (t := (q*8+256)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c109 := shortRun (t := (q*8+256)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c110 := shortRun (t := (q*8+257)) (d := 0) (by omega) (by norm_num [form])
  have c111 := differentTimes (t := (q*8+258)) (i := (q*16+516)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c112 := shortRun (t := (q*8+257)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c113 := shortRun (t := (q*8+257)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c114 := mustReset (t := (q*8+257)) (by omega)
  have c115 := shortRun (t := (q*8+258)) (d := 0) (by omega) (by norm_num [form])
  have c116 := ruledOut (t := (q*16+518)) (by omega) ih (by omega)
  have c117 := differentTimes (t := (q*4+129)) (i := (q*16+519)) (d := 0) (e := 2) (by omega) (by norm_num [form]; omega)
  have c118 := differentTimes (t := (q*8+259)) (i := (q*16+519)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c119 := alreadySeen (t := (q*8+258)) (i := (q*2+64)) (d := 1) (e := 0) (by omega) (by omega) (by norm_num [form]; omega)
  have c120 := alreadySeen (t := (q*8+258)) (i := (q*4+129)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c121 : ¬ tag (q*8+259) 0 ∨ ¬ tag (q*8+260) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*8+259)) (d := 0) (x := (q*8+259)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c122 := alreadySeen (t := (q*8+260)) (i := (q*4+130)) (d := 0) (e := 0) (by omega) (by omega) (by norm_num [form]; omega)
  have c123 := shortRun (t := (q*8+260)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c124 : ¬ tag (q*8+260) 1 ∨ ¬ tag (q*8+261) 0 ∨ tag (q*4+130) 1 ∨ tag (q*8+260) 2 := by
    clear * - q
    apply earlier (t := (q*8+260)) (d := 1) (x := (q*4+129)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · exact .inl ((show i = q*4+130 by omega) ▸ a)
    · exact .inr (((show i = q*8+260 by omega) ▸ a))
    · omega
    · omega
    · omega
    · omega
  have c125 := differentTimes (t := (q*8+251)) (i := (q*16+503)) (d := 0) (e := 1) (by omega) (by norm_num [form]; omega)
  have c126 : ¬ tag (q*16+503) 0 ∨ ¬ tag (q*16+504) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*16+503)) (d := 0) (x := (q*16+503)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c127 := shortRun (t := (q*16+504)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c128 := shortRun (t := (q*16+505)) (d := 0) (by omega) (by norm_num [form])
  have c129 : ¬ tag (q*16+505) 0 ∨ ¬ tag (q*16+506) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*16+505)) (d := 0) (x := (q*16+505)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c130 := differentTimes (t := (q*8+253)) (i := (q*16+507)) (d := 0) (e := 1) (by omega) (by norm_num [form]; omega)
  have c131 : ¬ tag (q*16+506) 1 ∨ ¬ tag (q*16+507) 0 ∨ tag (q*4+126) 0 ∨ tag (q*8+253) 1 ∨ tag (q*16+506) 2 := by
    clear * - q
    apply earlier (t := (q*16+506)) (d := 1) (x := (q*8+252)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact .inl ((show i = q*4+126 by omega) ▸ a)
    · exact .inr (.inl ((show i = q*8+253 by omega) ▸ a))
    · exact .inr (.inr (((show i = q*16+506 by omega) ▸ a)))
    · omega
    · omega
    · omega
    · omega
  have c132 := shortRun (t := (q*16+507)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c133 : ¬ tag (q*16+508) 0 ∨ ¬ tag (q*16+509) 0 ∨ tag (q*8+254) 0 := by
    clear * - q
    apply earlier (t := (q*16+508)) (d := 0) (x := (q*16+508)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*8+254 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c134 := shortRun (t := (q*16+509)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c135 := alreadySeen (t := (q*16+509)) (i := (q*8+255)) (d := 2) (e := 2) (by omega) (by omega) (by norm_num [form]; omega)
  have c136 := differentTimes (t := (q*8+255)) (i := (q*16+511)) (d := 0) (e := 1) (by omega) (by norm_num [form]; omega)
  have c137 : ¬ tag (q*16+510) 0 ∨ ¬ tag (q*16+511) 0 ∨ tag (q*8+255) 0 := by
    clear * - q
    apply earlier (t := (q*16+510)) (d := 0) (x := (q*16+510)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*8+255 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c138 : ¬ tag (q*16+511) 0 ∨ ¬ tag (q*16+512) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*16+511)) (d := 0) (x := (q*16+511)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c139 := shortRun (t := (q*16+511)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c140 := shortRun (t := (q*16+511)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c141 := mustReset (t := (q*16+511)) (by omega)
  have c142 := alreadySeen (t := (q*16+512)) (i := (q*8+256)) (d := 0) (e := 0) (by omega) (by omega) (by norm_num [form]; omega)
  have c143 := shortRun (t := (q*16+512)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c144 := alreadySeen (t := (q*16+512)) (i := (q*4+128)) (d := 2) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c145 := shortRun (t := (q*16+513)) (d := 0) (by omega) (by norm_num [form])
  have c146 : ¬ tag (q*16+513) 0 ∨ ¬ tag (q*16+514) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*16+513)) (d := 0) (x := (q*16+513)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c147 := shortRun (t := (q*16+514)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c148 : ¬ tag (q*16+514) 1 ∨ ¬ tag (q*16+515) 0 ∨ tag (q*4+128) 0 ∨ tag (q*8+257) 1 ∨ tag (q*16+514) 2 := by
    clear * - q
    apply earlier (t := (q*16+514)) (d := 1) (x := (q*8+256)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact .inl ((show i = q*4+128 by omega) ▸ a)
    · exact .inr (.inl ((show i = q*8+257 by omega) ▸ a))
    · exact .inr (.inr (((show i = q*16+514 by omega) ▸ a)))
    · omega
    · omega
    · omega
    · omega
  have c149 := shortRun (t := (q*16+514)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c150 := shortRun (t := (q*16+515)) (d := 0) (by omega) (by norm_num [form])
  have c151 := shortRun (t := (q*16+515)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c152 := shortRun (t := (q*16+515)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c153 := mustReset (t := (q*16+515)) (by omega)
  have c154 : ¬ tag (q*16+516) 0 ∨ ¬ tag (q*16+517) 0 ∨ tag (q*8+258) 0 := by
    clear * - q
    apply earlier (t := (q*16+516)) (d := 0) (x := (q*16+516)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*8+258 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c155 : ¬ tag (q*16+516) 1 ∨ ¬ tag (q*16+517) 0 ∨ tag (q*8+258) 1 ∨ tag (q*16+516) 2 := by
    clear * - q
    apply earlier (t := (q*16+516)) (d := 1) (x := (q*8+257)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · exact .inl ((show i = q*8+258 by omega) ▸ a)
    · exact .inr (((show i = q*16+516 by omega) ▸ a))
    · omega
    · omega
    · omega
    · omega
  have c156 := shortRun (t := (q*16+517)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c157 := shortRun (t := (q*16+517)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c158 := mustReset (t := (q*16+517)) (by omega)
  have c159 := shortRun (t := (q*16+518)) (d := 0) (by omega) (by norm_num [form])
  have c160 := shortRun (t := (q*16+518)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c161 := shortRun (t := (q*16+519)) (d := 0) (by omega) (by norm_num [form])
  have c162 := shortRun (t := (q*16+519)) (d := 1) (by omega) (by norm_num [form]; omega)
  grind (splits := 256) only


set_option maxRecDepth 6000 in
set_option maxHeartbeats 3500000 in
/-- Excludes the extra position for `n = 4q + 130`. -/
private lemma exclude4_2 (q : ℕ) (ih : ∀ x i, 1 < x → x < q*4+130 → value i = x → six x i) :
    ¬ tag (q*16+524) 3 := by
  intro bad
  have c0 := optionsAt (t := (q*4+128)) (by omega)
  have c1 := ruledOut (t := (q*4+128)) (by omega) ih (by omega)
  have c2 := optionsAt (t := (q*4+129)) (by omega)
  have c3 := optionsAt (t := (q*4+131)) (by omega)
  have c4 := distinctForms (t := (q*4+131)) (d := 2) (e := 3) (by norm_num [form]; omega)
  have c5 := distinctForms (t := (q*4+132)) (d := 0) (e := 1) (by norm_num [form]; omega)
  have c6 := ruledOut (t := (q*4+132)) (by omega) ih (by omega)
  have c7 := optionsAt (t := (q*8+257)) (by omega)
  have c8 := optionsAt (t := (q*4+130)) (by omega)
  have c9 := ruledOut (t := (q*4+130)) (by omega) ih (by omega)
  have c10 := optionsAt (t := (q*8+259)) (by omega)
  have c11 := distinctForms (t := (q*8+259)) (d := 0) (e := 1) (by norm_num [form]; omega)
  have c12 := optionsAt (t := (q*8+260)) (by omega)
  have c13 := ruledOut (t := (q*8+260)) (by omega) ih (by omega)
  have c14 := optionsAt (t := (q*8+261)) (by omega)
  have c15 := differentTimes (t := (q*4+131)) (i := (q*8+261)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c16 := optionsAt (t := (q*8+263)) (by omega)
  have c17 := optionsAt (t := (q*8+258)) (by omega)
  have c18 := ruledOut (t := (q*8+258)) (by omega) ih (by omega)
  have c19 := optionsAt (t := (q*16+515)) (by omega)
  have c20 := optionsAt (t := (q*16+516)) (by omega)
  have c21 := ruledOut (t := (q*16+516)) (by omega) ih (by omega)
  have c22 := optionsAt (t := (q*16+517)) (by omega)
  have c23 := differentTimes (t := (q*4+129)) (i := (q*8+258)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c24 := differentTimes (t := (q*4+129)) (i := (q*16+515)) (d := 1) (e := 3) (by omega) (by norm_num [form]; omega)
  have c25 := differentTimes (t := (q*4+129)) (i := (q*16+517)) (d := 1) (e := 3) (by omega) (by norm_num [form]; omega)
  have c26 := shortRun (t := (q*4+128)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c27 := shortRun (t := (q*4+128)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c28 := shortRun (t := (q*4+129)) (d := 0) (by omega) (by norm_num [form])
  have c29 := optionsAt (t := (q*16+519)) (by omega)
  have c30 := ruledOut (t := (q*16+520)) (by omega) ih (by omega)
  have c31 := optionsAt (t := (q*16+521)) (by omega)
  have c32 := differentTimes (t := (q*4+130)) (i := (q*8+261)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c33 := shortRun (t := (q*4+129)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c34 := mustReset (t := (q*4+129)) (by omega)
  have c35 := optionsAt (t := (q*8+262)) (by omega)
  have c36 := ruledOut (t := (q*8+262)) (by omega) ih (by omega)
  have c37 := optionsAt (t := (q*16+523)) (by omega)
  have c38 := distinctForms (t := (q*16+524)) (d := 0) (e := 3) (by norm_num [form]; omega)
  have c39 := distinctForms (t := (q*16+524)) (d := 1) (e := 3) (by norm_num [form]; omega)
  have c40 := distinctForms (t := (q*16+524)) (d := 2) (e := 3) (by norm_num [form]; omega)
  have c41 := differentTimes (t := (q*2+65)) (i := (q*16+524)) (d := 0) (e := 3) (by omega) (by norm_num [form]; omega)
  have c42 := differentTimes (t := (q*4+131)) (i := (q*16+524)) (d := 1) (e := 3) (by omega) (by norm_num [form]; omega)
  have c43 := differentTimes (t := (q*8+262)) (i := (q*16+524)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c44 := differentTimes (t := (q*8+263)) (i := (q*16+524)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c45 := differentTimes (t := (q*16+523)) (i := (q*16+524)) (d := 3) (e := 3) (by omega) (by norm_num [form]; omega)
  have c46 := shortRun (t := (q*4+130)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c47 := shortRun (t := (q*4+130)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c48 := shortRun (t := (q*4+131)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c49 := mustReset (t := (q*4+131)) (by omega)
  have c50 := differentTimes (t := (q*4+128)) (i := (q*16+515)) (d := 0) (e := 2) (by omega) (by norm_num [form]; omega)
  have c51 := differentTimes (t := (q*8+258)) (i := (q*16+516)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c52 := differentTimes (t := (q*8+258)) (i := (q*16+517)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c53 := shortRun (t := (q*8+257)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c54 := shortRun (t := (q*8+257)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c55 := mustReset (t := (q*8+257)) (by omega)
  have c56 := optionsAt (t := (q*16+518)) (by omega)
  have c57 := distinctForms (t := (q*16+518)) (d := 1) (e := 2) (by norm_num [form]; omega)
  have c58 := ruledOut (t := (q*16+518)) (by omega) ih (by omega)
  have c59 : ¬ tag (q*8+258) 0 ∨ ¬ tag (q*8+259) 0 ∨ tag (q*4+129) 0 := by
    clear * - q
    apply earlier (t := (q*8+258)) (d := 0) (x := (q*8+258)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*4+129 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c60 := shortRun (t := (q*8+259)) (d := 0) (by omega) (by norm_num [form])
  have c61 := shortRun (t := (q*8+259)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c62 := alreadySeen (t := (q*8+259)) (i := (q*4+130)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c63 := shortRun (t := (q*8+259)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c64 := mustReset (t := (q*8+259)) (by omega)
  have c65 := shortRun (t := (q*8+260)) (d := 0) (by omega) (by norm_num [form])
  have c66 := ruledOut (t := (q*16+522)) (by omega) ih (by omega)
  have c67 := differentTimes (t := (q*4+130)) (i := (q*16+523)) (d := 0) (e := 2) (by omega) (by norm_num [form]; omega)
  have c68 := differentTimes (t := (q*8+261)) (i := (q*16+523)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c69 := alreadySeen (t := (q*8+260)) (i := (q*4+130)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c70 := alreadySeen (t := (q*8+260)) (i := (q*4+130)) (d := 2) (e := 2) (by omega) (by omega) (by norm_num [form]; omega)
  have c71 : ¬ tag (q*8+261) 0 ∨ ¬ tag (q*8+262) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*8+261)) (d := 0) (x := (q*8+261)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c72 := shortRun (t := (q*8+262)) (d := 0) (by omega) (by norm_num [form])
  have c73 := differentTimes (t := (q*4+131)) (i := (q*8+263)) (d := 0) (e := 1) (by omega) (by norm_num [form]; omega)
  have c74 := alreadySeen (t := (q*8+262)) (i := (q*4+131)) (d := 0) (e := 0) (by omega) (by omega) (by norm_num [form]; omega)
  have c75 := shortRun (t := (q*8+262)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c76 : ¬ tag (q*8+262) 1 ∨ ¬ tag (q*8+263) 0 ∨ tag (q*2+65) 0 ∨ tag (q*4+131) 1 ∨ tag (q*8+262) 2 := by
    clear * - q
    apply earlier (t := (q*8+262)) (d := 1) (x := (q*4+130)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact .inl ((show i = q*2+65 by omega) ▸ a)
    · exact .inr (.inl ((show i = q*4+131 by omega) ▸ a))
    · exact .inr (.inr (((show i = q*8+262 by omega) ▸ a)))
    · omega
    · omega
    · omega
    · omega
  have c77 : ¬ tag (q*8+263) 0 ∨ ¬ tag (q*8+264) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*8+263)) (d := 0) (x := (q*8+263)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c78 : ¬ tag (q*8+263) 1 ∨ ¬ tag (q*8+264) 0 ∨ tag (q*4+132) 1 := by
    clear * - q
    apply earlier (t := (q*8+263)) (d := 1) (x := (q*4+131)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · exact ((show i = q*4+132 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
  have c79 := mustReset (t := (q*8+263)) (by omega)
  have c80 := differentTimes (t := (q*8+257)) (i := (q*16+515)) (d := 0) (e := 1) (by omega) (by norm_num [form]; omega)
  have c81 : ¬ tag (q*16+515) 0 ∨ ¬ tag (q*16+516) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*16+515)) (d := 0) (x := (q*16+515)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c82 := shortRun (t := (q*16+516)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c83 := alreadySeen (t := (q*16+516)) (i := (q*8+258)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c84 := shortRun (t := (q*16+517)) (d := 0) (by omega) (by norm_num [form])
  have c85 : ¬ tag (q*16+517) 0 ∨ ¬ tag (q*16+518) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*16+517)) (d := 0) (x := (q*16+517)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c86 : ¬ tag (q*16+517) 1 ∨ ¬ tag (q*16+518) 0 ∨ tag (q*4+129) 0 ∨ tag (q*8+259) 1 := by
    clear * - q
    apply earlier (t := (q*16+517)) (d := 1) (x := (q*8+258)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact .inl ((show i = q*4+129 by omega) ▸ a)
    · exact .inr (((show i = q*8+259 by omega) ▸ a))
    · omega
    · omega
    · omega
    · omega
    · omega
  have c87 := differentTimes (t := (q*8+259)) (i := (q*16+519)) (d := 0) (e := 1) (by omega) (by norm_num [form]; omega)
  have c88 : ¬ tag (q*16+518) 1 ∨ ¬ tag (q*16+519) 0 ∨ tag (q*4+129) 0 ∨ tag (q*8+259) 1 ∨ tag (q*16+518) 2 := by
    clear * - q
    apply earlier (t := (q*16+518)) (d := 1) (x := (q*8+258)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact .inl ((show i = q*4+129 by omega) ▸ a)
    · exact .inr (.inl ((show i = q*8+259 by omega) ▸ a))
    · exact .inr (.inr (((show i = q*16+518 by omega) ▸ a)))
    · omega
    · omega
    · omega
    · omega
  have c89 := alreadySeen (t := (q*16+519)) (i := (q*8+260)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c90 := shortRun (t := (q*16+519)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c91 := mustReset (t := (q*16+519)) (by omega)
  have c92 : ¬ tag (q*16+520) 0 ∨ ¬ tag (q*16+521) 0 ∨ tag (q*8+260) 0 := by
    clear * - q
    apply earlier (t := (q*16+520)) (d := 0) (x := (q*16+520)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*8+260 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c93 := shortRun (t := (q*16+521)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c94 := shortRun (t := (q*16+521)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c95 := mustReset (t := (q*16+521)) (by omega)
  have c96 := shortRun (t := (q*16+522)) (d := 0) (by omega) (by norm_num [form])
  have c97 := shortRun (t := (q*16+522)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c98 := shortRun (t := (q*16+523)) (d := 0) (by omega) (by norm_num [form])
  have c99 := shortRun (t := (q*16+523)) (d := 1) (by omega) (by norm_num [form]; omega)
  grind (splits := 256) only


set_option maxRecDepth 6000 in
set_option maxHeartbeats 3500000 in
/-- Excludes the extra position for `n = 8q + 131`. -/
private lemma exclude8_3 (q : ℕ) (ih : ∀ x i, 1 < x → x < q*8+131 → value i = x → six x i) :
    ¬ tag (q*32+528) 3 := by
  intro bad
  have c0 := optionsAt (t := (q*2+30)) (by omega)
  have c1 := ruledOut (t := (q*2+30)) (by omega) ih (by omega)
  have c2 := optionsAt (t := (q*4+61)) (by omega)
  have c3 := optionsAt (t := (q*2+31)) (by omega)
  have c4 := optionsAt (t := (q*4+62)) (by omega)
  have c5 := ruledOut (t := (q*4+62)) (by omega) ih (by omega)
  have c6 := optionsAt (t := (q*4+63)) (by omega)
  have c7 := optionsAt (t := (q*8+123)) (by omega)
  have c8 := optionsAt (t := (q*8+124)) (by omega)
  have c9 := ruledOut (t := (q*8+124)) (by omega) ih (by omega)
  have c10 := differentTimes (t := (q*2+31)) (i := (q*4+62)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c11 := differentTimes (t := (q*2+31)) (i := (q*8+123)) (d := 1) (e := 3) (by omega) (by norm_num [form]; omega)
  have c12 := shortRun (t := (q*2+30)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c13 := shortRun (t := (q*2+30)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c14 := optionsAt (t := (q*2+32)) (by omega)
  have c15 := ruledOut (t := (q*2+32)) (by omega) ih (by omega)
  have c16 := shortRun (t := (q*2+31)) (d := 0) (by omega) (by norm_num [form])
  have c17 := optionsAt (t := (q*4+64)) (by omega)
  have c18 := ruledOut (t := (q*4+64)) (by omega) ih (by omega)
  have c19 := optionsAt (t := (q*4+65)) (by omega)
  have c20 := optionsAt (t := (q*8+127)) (by omega)
  have c21 := ruledOut (t := (q*8+128)) (by omega) ih (by omega)
  have c22 := optionsAt (t := (q*8+129)) (by omega)
  have c23 := differentTimes (t := (q*2+32)) (i := (q*4+64)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c24 := shortRun (t := (q*2+31)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c25 := mustReset (t := (q*2+31)) (by omega)
  have c26 := distinctForms (t := (q*4+66)) (d := 0) (e := 1) (by norm_num [form]; omega)
  have c27 := distinctForms (t := (q*4+66)) (d := 1) (e := 2) (by norm_num [form]; omega)
  have c28 := ruledOut (t := (q*4+66)) (by omega) ih (by omega)
  have c29 := optionsAt (t := (q*8+131)) (by omega)
  have c30 := distinctForms (t := (q*8+131)) (d := 2) (e := 3) (by norm_num [form]; omega)
  have c31 := optionsAt (t := (q*8+132)) (by omega)
  have c32 := distinctForms (t := (q*8+132)) (d := 0) (e := 2) (by norm_num [form]; omega)
  have c33 := ruledOut (t := (q*8+132)) (by omega) ih (by omega)
  have c34 := differentTimes (t := (q*4+66)) (i := (q*8+131)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c35 := differentTimes (t := (q*2+30)) (i := (q*8+123)) (d := 0) (e := 2) (by omega) (by norm_num [form]; omega)
  have c36 := differentTimes (t := (q*4+62)) (i := (q*8+124)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c37 := differentTimes (t := (q*4+62)) (i := (q*8+125)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c38 := alreadySeen (t := (q*4+61)) (i := (q*2+31)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c39 := shortRun (t := (q*4+61)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c40 := mustReset (t := (q*4+61)) (by omega)
  have c41 := distinctForms (t := (q*8+126)) (d := 1) (e := 2) (by norm_num [form]; omega)
  have c42 : ¬ tag (q*4+62) 0 ∨ ¬ tag (q*4+63) 0 ∨ tag (q*2+31) 0 := by
    clear * - q
    apply earlier (t := (q*4+62)) (d := 0) (x := (q*4+62)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*2+31 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c43 := shortRun (t := (q*4+63)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c44 := shortRun (t := (q*4+63)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c45 := mustReset (t := (q*4+63)) (by omega)
  have c46 := shortRun (t := (q*4+64)) (d := 0) (by omega) (by norm_num [form])
  have c47 := optionsAt (t := (q*8+130)) (by omega)
  have c48 := ruledOut (t := (q*8+130)) (by omega) ih (by omega)
  have c49 := optionsAt (t := (q*16+259)) (by omega)
  have c50 := optionsAt (t := (q*16+260)) (by omega)
  have c51 := ruledOut (t := (q*16+260)) (by omega) ih (by omega)
  have c52 := differentTimes (t := (q*2+32)) (i := (q*8+131)) (d := 0) (e := 2) (by omega) (by norm_num [form]; omega)
  have c53 := differentTimes (t := (q*4+65)) (i := (q*8+131)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c54 := differentTimes (t := (q*8+130)) (i := (q*16+259)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c55 := alreadySeen (t := (q*4+64)) (i := (q*2+32)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c56 := alreadySeen (t := (q*4+64)) (i := (q*2+32)) (d := 2) (e := 2) (by omega) (by omega) (by norm_num [form]; omega)
  have c57 := optionsAt (t := (q*16+263)) (by omega)
  have c58 := distinctForms (t := (q*16+263)) (d := 2) (e := 3) (by norm_num [form]; omega)
  have c59 := optionsAt (t := (q*16+264)) (by omega)
  have c60 := ruledOut (t := (q*16+264)) (by omega) ih (by omega)
  have c61 := optionsAt (t := (q*16+265)) (by omega)
  have c62 := distinctForms (t := (q*16+265)) (d := 0) (e := 3) (by norm_num [form]; omega)
  have c63 := distinctForms (t := (q*16+265)) (d := 1) (e := 3) (by norm_num [form]; omega)
  have c64 : tag (q*4+66) 1 ∨ tag (q*8+132) 2 ∨ tag (q*8+133) 2 ∨ tag (q*16+263) 3 ∨ tag (q*16+264) 3 ∨ tag (q*16+265) 3 := by
    clear * - q
    obtain ⟨i, hi, hit⟩ := occurs.mp (deadline (q*4+65))
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · exact .inl ((show i = q*4+66 by omega) ▸ a)
    · exact .inr (.inl ((show i = q*8+132 by omega) ▸ a))
    · exact .inr (.inr (.inl ((show i = q*8+133 by omega) ▸ a)))
    · exact .inr (.inr (.inr (.inl ((show i = q*16+263 by omega) ▸ a))))
    · exact .inr (.inr (.inr (.inr (.inl ((show i = q*16+264 by omega) ▸ a)))))
    · exact .inr (.inr (.inr (.inr (.inr (((show i = q*16+265 by omega) ▸ a))))))
  have c65 := differentTimes (t := (q*8+132)) (i := (q*16+263)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c66 : ¬ tag (q*4+65) 0 ∨ ¬ tag (q*4+66) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*4+65)) (d := 0) (x := (q*4+65)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c67 := shortRun (t := (q*4+65)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c68 := shortRun (t := (q*4+65)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c69 := mustReset (t := (q*4+65)) (by omega)
  have c70 := distinctForms (t := (q*8+134)) (d := 0) (e := 1) (by norm_num [form]; omega)
  have c71 := distinctForms (t := (q*8+134)) (d := 1) (e := 2) (by norm_num [form]; omega)
  have c72 := ruledOut (t := (q*8+134)) (by omega) ih (by omega)
  have c73 := optionsAt (t := (q*16+268)) (by omega)
  have c74 := distinctForms (t := (q*16+268)) (d := 1) (e := 2) (by norm_num [form]; omega)
  have c75 := ruledOut (t := (q*16+268)) (by omega) ih (by omega)
  have c76 := differentTimes (t := (q*4+61)) (i := (q*8+123)) (d := 0) (e := 1) (by omega) (by norm_num [form]; omega)
  have c77 : ¬ tag (q*8+123) 0 ∨ ¬ tag (q*8+124) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*8+123)) (d := 0) (x := (q*8+123)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c78 := shortRun (t := (q*8+124)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c79 := shortRun (t := (q*8+125)) (d := 0) (by omega) (by norm_num [form])
  have c80 : ¬ tag (q*8+125) 0 ∨ ¬ tag (q*8+126) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*8+125)) (d := 0) (x := (q*8+125)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c81 : ¬ tag (q*8+126) 1 ∨ ¬ tag (q*8+127) 0 ∨ tag (q*2+31) 0 ∨ tag (q*4+63) 1 ∨ tag (q*8+126) 2 := by
    clear * - q
    apply earlier (t := (q*8+126)) (d := 1) (x := (q*4+62)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact .inl ((show i = q*2+31 by omega) ▸ a)
    · exact .inr (.inl ((show i = q*4+63 by omega) ▸ a))
    · exact .inr (.inr (((show i = q*8+126 by omega) ▸ a)))
    · omega
    · omega
    · omega
    · omega
  have c82 := alreadySeen (t := (q*8+127)) (i := (q*4+64)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c83 := shortRun (t := (q*8+127)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c84 := mustReset (t := (q*8+127)) (by omega)
  have c85 := differentTimes (t := (q*8+129)) (i := (q*16+259)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c86 : ¬ tag (q*8+128) 0 ∨ ¬ tag (q*8+129) 0 ∨ tag (q*4+64) 0 := by
    clear * - q
    apply earlier (t := (q*8+128)) (d := 0) (x := (q*8+128)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*4+64 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c87 := shortRun (t := (q*8+129)) (d := 0) (by omega) (by norm_num [form])
  have c88 := shortRun (t := (q*8+129)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c89 := shortRun (t := (q*8+129)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c90 := mustReset (t := (q*8+129)) (by omega)
  have c91 := shortRun (t := (q*8+130)) (d := 0) (by omega) (by norm_num [form])
  have c92 := optionsAt (t := (q*16+262)) (by omega)
  have c93 := ruledOut (t := (q*16+262)) (by omega) ih (by omega)
  have c94 := differentTimes (t := (q*4+65)) (i := (q*16+262)) (d := 0) (e := 2) (by omega) (by norm_num [form]; omega)
  have c95 := differentTimes (t := (q*8+131)) (i := (q*16+263)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c96 := shortRun (t := (q*8+130)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c97 := shortRun (t := (q*8+130)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c98 := optionsAt (t := (q*32+527)) (by omega)
  have c99 := distinctForms (t := (q*32+528)) (d := 0) (e := 3) (by norm_num [form]; omega)
  have c100 := distinctForms (t := (q*32+528)) (d := 1) (e := 3) (by norm_num [form]; omega)
  have c101 := distinctForms (t := (q*32+528)) (d := 2) (e := 3) (by norm_num [form]; omega)
  have c102 := differentTimes (t := (q*8+132)) (i := (q*32+528)) (d := 1) (e := 3) (by omega) (by norm_num [form]; omega)
  have c103 := differentTimes (t := (q*16+264)) (i := (q*32+528)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c104 := differentTimes (t := (q*16+265)) (i := (q*32+528)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c105 := differentTimes (t := (q*32+527)) (i := (q*32+528)) (d := 3) (e := 3) (by omega) (by norm_num [form]; omega)
  have c106 : ¬ tag (q*8+131) 1 ∨ ¬ tag (q*8+132) 0 ∨ tag (q*4+66) 1 := by
    clear * - q
    apply earlier (t := (q*8+131)) (d := 1) (x := (q*4+65)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · exact ((show i = q*4+66 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
  have c107 := shortRun (t := (q*8+131)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c108 := mustReset (t := (q*8+131)) (by omega)
  have c109 := shortRun (t := (q*8+132)) (d := 0) (by omega) (by norm_num [form])
  have c110 := distinctForms (t := (q*16+266)) (d := 1) (e := 2) (by norm_num [form]; omega)
  have c111 := distinctForms (t := (q*32+531)) (d := 0) (e := 3) (by norm_num [form]; omega)
  have c112 := distinctForms (t := (q*32+532)) (d := 1) (e := 3) (by norm_num [form]; omega)
  have c113 := distinctForms (t := (q*32+533)) (d := 0) (e := 3) (by norm_num [form]; omega)
  have c114 : tag (q*4+66) 0 ∨ tag (q*8+133) 1 ∨ tag (q*16+266) 2 ∨ tag (q*16+267) 2 ∨ tag (q*32+531) 3 ∨ tag (q*32+532) 3 ∨ tag (q*32+533) 3 := by
    clear * - q
    obtain ⟨i, hi, hit⟩ := occurs.mp (deadline (q*8+132))
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact .inl ((show i = q*4+66 by omega) ▸ a)
    · exact .inr (.inl ((show i = q*8+133 by omega) ▸ a))
    · exact .inr (.inr (.inl ((show i = q*16+266 by omega) ▸ a)))
    · exact .inr (.inr (.inr (.inl ((show i = q*16+267 by omega) ▸ a))))
    · exact .inr (.inr (.inr (.inr (.inl ((show i = q*32+531 by omega) ▸ a)))))
    · exact .inr (.inr (.inr (.inr (.inr (.inl ((show i = q*32+532 by omega) ▸ a))))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (((show i = q*32+533 by omega) ▸ a)))))))
  have c115 := alreadySeen (t := (q*8+132)) (i := (q*4+66)) (d := 0) (e := 0) (by omega) (by omega) (by norm_num [form]; omega)
  have c116 := shortRun (t := (q*8+133)) (d := 0) (by omega) (by norm_num [form])
  have c117 := differentTimes (t := (q*8+134)) (i := (q*16+268)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c118 : ¬ tag (q*8+133) 0 ∨ ¬ tag (q*8+134) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*8+133)) (d := 0) (x := (q*8+133)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c119 := shortRun (t := (q*8+133)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c120 := shortRun (t := (q*8+133)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c121 : ¬ tag (q*16+259) 0 ∨ ¬ tag (q*16+260) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*16+259)) (d := 0) (x := (q*16+259)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c122 : ¬ tag (q*16+259) 1 ∨ ¬ tag (q*16+260) 0 ∨ tag (q*8+130) 1 := by
    clear * - q
    apply earlier (t := (q*16+259)) (d := 1) (x := (q*8+129)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · exact ((show i = q*8+130 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
  have c123 := shortRun (t := (q*16+260)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c124 := shortRun (t := (q*16+260)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c125 := shortRun (t := (q*16+261)) (d := 0) (by omega) (by norm_num [form])
  have c126 := shortRun (t := (q*16+261)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c127 := mustReset (t := (q*16+261)) (by omega)
  have c128 := shortRun (t := (q*16+262)) (d := 0) (by omega) (by norm_num [form])
  have c129 := differentTimes (t := (q*8+131)) (i := (q*32+527)) (d := 0) (e := 2) (by omega) (by norm_num [form]; omega)
  have c130 := differentTimes (t := (q*16+263)) (i := (q*32+527)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c131 := shortRun (t := (q*16+262)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c132 := alreadySeen (t := (q*16+262)) (i := (q*4+65)) (d := 1) (e := 0) (by omega) (by omega) (by norm_num [form]; omega)
  have c133 : ¬ tag (q*16+263) 0 ∨ ¬ tag (q*16+264) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*16+263)) (d := 0) (x := (q*16+263)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c134 := shortRun (t := (q*16+264)) (d := 0) (by omega) (by norm_num [form])
  have c135 := differentTimes (t := (q*8+132)) (i := (q*16+265)) (d := 0) (e := 1) (by omega) (by norm_num [form]; omega)
  have c136 : ¬ tag (q*16+264) 0 ∨ ¬ tag (q*16+265) 0 ∨ tag (q*8+132) 0 := by
    clear * - q
    apply earlier (t := (q*16+264)) (d := 0) (x := (q*16+264)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*8+132 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c137 := shortRun (t := (q*16+264)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c138 : ¬ tag (q*16+264) 1 ∨ ¬ tag (q*16+265) 0 ∨ tag (q*8+132) 1 ∨ tag (q*16+264) 2 := by
    clear * - q
    apply earlier (t := (q*16+264)) (d := 1) (x := (q*8+131)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · exact .inl ((show i = q*8+132 by omega) ▸ a)
    · exact .inr (((show i = q*16+264 by omega) ▸ a))
    · omega
    · omega
    · omega
    · omega
  have c139 := shortRun (t := (q*16+265)) (d := 0) (by omega) (by norm_num [form])
  have c140 : ¬ tag (q*16+265) 0 ∨ ¬ tag (q*16+266) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*16+265)) (d := 0) (x := (q*16+265)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c141 := shortRun (t := (q*16+266)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c142 := alreadySeen (t := (q*16+266)) (i := (q*4+66)) (d := 1) (e := 0) (by omega) (by omega) (by norm_num [form]; omega)
  have c143 := alreadySeen (t := (q*16+266)) (i := (q*8+133)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c144 := shortRun (t := (q*16+267)) (d := 0) (by omega) (by norm_num [form])
  have c145 : ¬ tag (q*16+267) 0 ∨ ¬ tag (q*16+268) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*16+267)) (d := 0) (x := (q*16+267)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c146 := shortRun (t := (q*16+267)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c147 : ¬ tag (q*16+268) 0 ∨ ¬ tag (q*16+269) 0 ∨ tag (q*8+134) 0 := by
    clear * - q
    apply earlier (t := (q*16+268)) (d := 0) (x := (q*16+268)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*8+134 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c148 : ¬ tag (q*16+268) 1 ∨ ¬ tag (q*16+269) 0 ∨ tag (q*8+134) 1 ∨ tag (q*16+268) 2 := by
    clear * - q
    apply earlier (t := (q*16+268)) (d := 1) (x := (q*8+133)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · exact .inl ((show i = q*8+134 by omega) ▸ a)
    · exact .inr (((show i = q*16+268 by omega) ▸ a))
    · omega
    · omega
    · omega
    · omega
  have c149 := alreadySeen (t := (q*16+268)) (i := (q*8+134)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c150 := shortRun (t := (q*32+527)) (d := 0) (by omega) (by norm_num [form])
  have c151 := shortRun (t := (q*32+527)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c152 := mustReset (t := (q*32+528)) (by omega)
  have c153 := shortRun (t := (q*32+529)) (d := 0) (by omega) (by norm_num [form])
  have c154 : ¬ tag (q*32+529) 0 ∨ ¬ tag (q*32+530) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*32+529)) (d := 0) (x := (q*32+529)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c155 := alreadySeen (t := (q*32+530)) (i := (q*8+132)) (d := 1) (e := 0) (by omega) (by omega) (by norm_num [form]; omega)
  have c156 := alreadySeen (t := (q*32+530)) (i := (q*16+265)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c157 := shortRun (t := (q*32+531)) (d := 0) (by omega) (by norm_num [form])
  have c158 : ¬ tag (q*32+531) 0 ∨ ¬ tag (q*32+532) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*32+531)) (d := 0) (x := (q*32+531)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c159 := alreadySeen (t := (q*32+532)) (i := (q*16+266)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  grind (splits := 256) only


set_option maxRecDepth 6000 in
set_option maxHeartbeats 3500000 in
/-- Excludes the extra position for `n = 16q + 135`. -/
private lemma exclude16_7 (q : ℕ) (ih : ∀ x i, 1 < x → x < q*16+135 → value i = x → six x i) :
    ¬ tag (q*64+544) 3 := by
  intro bad
  have c0 := optionsAt (t := (q*8+65)) (by omega)
  have c1 := optionsAt (t := (q*8+66)) (by omega)
  have c2 := ruledOut (t := (q*8+66)) (by omega) ih (by omega)
  have c3 := optionsAt (t := (q*8+67)) (by omega)
  have c4 := optionsAt (t := (q*16+131)) (by omega)
  have c5 := optionsAt (t := (q*16+132)) (by omega)
  have c6 := ruledOut (t := (q*16+132)) (by omega) ih (by omega)
  have c7 := optionsAt (t := (q*16+133)) (by omega)
  have c8 := optionsAt (t := (q*4+34)) (by omega)
  have c9 := ruledOut (t := (q*4+34)) (by omega) ih (by omega)
  have c10 := optionsAt (t := (q*8+68)) (by omega)
  have c11 := distinctForms (t := (q*8+68)) (d := 0) (e := 1) (by norm_num [form]; omega)
  have c12 := distinctForms (t := (q*8+68)) (d := 0) (e := 2) (by norm_num [form]; omega)
  have c13 := distinctForms (t := (q*8+68)) (d := 1) (e := 2) (by norm_num [form]; omega)
  have c14 := ruledOut (t := (q*8+68)) (by omega) ih (by omega)
  have c15 := distinctForms (t := (q*8+69)) (d := 0) (e := 2) (by norm_num [form]; omega)
  have c16 := optionsAt (t := (q*16+135)) (by omega)
  have c17 := distinctForms (t := (q*16+135)) (d := 2) (e := 3) (by norm_num [form]; omega)
  have c18 := optionsAt (t := (q*16+136)) (by omega)
  have c19 := distinctForms (t := (q*16+136)) (d := 0) (e := 2) (by norm_num [form]; omega)
  have c20 := ruledOut (t := (q*16+136)) (by omega) ih (by omega)
  have c21 : tag (q*4+34) 1 ∨ tag (q*8+68) 2 ∨ tag (q*8+69) 2 ∨ tag (q*16+135) 3 ∨ tag (q*16+136) 3 ∨ tag (q*16+137) 3 := by
    clear * - q
    obtain ⟨i, hi, hit⟩ := occurs.mp (deadline (q*4+33))
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · exact .inl ((show i = q*4+34 by omega) ▸ a)
    · exact .inr (.inl ((show i = q*8+68 by omega) ▸ a))
    · exact .inr (.inr (.inl ((show i = q*8+69 by omega) ▸ a)))
    · exact .inr (.inr (.inr (.inl ((show i = q*16+135 by omega) ▸ a))))
    · exact .inr (.inr (.inr (.inr (.inl ((show i = q*16+136 by omega) ▸ a)))))
    · exact .inr (.inr (.inr (.inr (.inr (((show i = q*16+137 by omega) ▸ a))))))
  have c22 := differentTimes (t := (q*4+34)) (i := (q*16+135)) (d := 1) (e := 3) (by omega) (by norm_num [form]; omega)
  have c23 := differentTimes (t := (q*8+68)) (i := (q*16+135)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c24 := differentTimes (t := (q*8+69)) (i := (q*16+135)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c25 := shortRun (t := (q*4+34)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c26 : ¬ tag (q*4+34) 1 ∨ ¬ tag (q*4+35) 0 ∨ tag (q+8) 0 ∨ tag (q*2+17) 1 ∨ tag (q*4+34) 2 := by
    clear * - q
    apply earlier (t := (q*4+34)) (d := 1) (x := (q*2+16)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact .inl ((show i = q+8 by omega) ▸ a)
    · exact .inr (.inl ((show i = q*2+17 by omega) ▸ a))
    · exact .inr (.inr (((show i = q*4+34 by omega) ▸ a)))
    · omega
    · omega
    · omega
    · omega
  have c27 := optionsAt (t := (q*32+263)) (by omega)
  have c28 := optionsAt (t := (q*32+264)) (by omega)
  have c29 := ruledOut (t := (q*32+264)) (by omega) ih (by omega)
  have c30 := optionsAt (t := (q*32+265)) (by omega)
  have c31 := differentTimes (t := (q*8+66)) (i := (q*16+132)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c32 := differentTimes (t := (q*8+66)) (i := (q*32+263)) (d := 1) (e := 3) (by omega) (by norm_num [form]; omega)
  have c33 := shortRun (t := (q*8+65)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c34 := shortRun (t := (q*8+65)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c35 := mustReset (t := (q*8+65)) (by omega)
  have c36 := shortRun (t := (q*8+66)) (d := 0) (by omega) (by norm_num [form])
  have c37 := optionsAt (t := (q*16+134)) (by omega)
  have c38 := ruledOut (t := (q*16+134)) (by omega) ih (by omega)
  have c39 := optionsAt (t := (q*32+267)) (by omega)
  have c40 := optionsAt (t := (q*32+268)) (by omega)
  have c41 := ruledOut (t := (q*32+268)) (by omega) ih (by omega)
  have c42 := optionsAt (t := (q*32+269)) (by omega)
  have c43 := differentTimes (t := (q*8+67)) (i := (q*16+135)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c44 := differentTimes (t := (q*16+134)) (i := (q*32+267)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c45 := differentTimes (t := (q*16+135)) (i := (q*32+267)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c46 := alreadySeen (t := (q*8+66)) (i := (q+8)) (d := 2) (e := 0) (by omega) (by omega) (by norm_num [form]; omega)
  have c47 := alreadySeen (t := (q*8+66)) (i := (q*2+17)) (d := 2) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c48 := alreadySeen (t := (q*8+66)) (i := (q*4+34)) (d := 2) (e := 2) (by omega) (by omega) (by norm_num [form]; omega)
  have c49 := alreadySeen (t := (q*8+66)) (i := (q*4+35)) (d := 2) (e := 2) (by omega) (by omega) (by norm_num [form]; omega)
  have c50 := shortRun (t := (q*8+67)) (d := 0) (by omega) (by norm_num [form])
  have c51 := optionsAt (t := (q*32+271)) (by omega)
  have c52 := distinctForms (t := (q*32+271)) (d := 2) (e := 3) (by norm_num [form]; omega)
  have c53 := optionsAt (t := (q*32+272)) (by omega)
  have c54 := ruledOut (t := (q*32+272)) (by omega) ih (by omega)
  have c55 := optionsAt (t := (q*32+273)) (by omega)
  have c56 := distinctForms (t := (q*32+273)) (d := 0) (e := 3) (by norm_num [form]; omega)
  have c57 := distinctForms (t := (q*32+273)) (d := 1) (e := 3) (by norm_num [form]; omega)
  have c58 : tag (q*8+68) 1 ∨ tag (q*16+136) 2 ∨ tag (q*16+137) 2 ∨ tag (q*32+271) 3 ∨ tag (q*32+272) 3 ∨ tag (q*32+273) 3 := by
    clear * - q
    obtain ⟨i, hi, hit⟩ := occurs.mp (deadline (q*8+67))
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · exact .inl ((show i = q*8+68 by omega) ▸ a)
    · exact .inr (.inl ((show i = q*16+136 by omega) ▸ a))
    · exact .inr (.inr (.inl ((show i = q*16+137 by omega) ▸ a)))
    · exact .inr (.inr (.inr (.inl ((show i = q*32+271 by omega) ▸ a))))
    · exact .inr (.inr (.inr (.inr (.inl ((show i = q*32+272 by omega) ▸ a)))))
    · exact .inr (.inr (.inr (.inr (.inr (((show i = q*32+273 by omega) ▸ a))))))
  have c59 := differentTimes (t := (q*8+68)) (i := (q*32+271)) (d := 1) (e := 3) (by omega) (by norm_num [form]; omega)
  have c60 := differentTimes (t := (q*16+136)) (i := (q*32+271)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c61 : ¬ tag (q*8+67) 0 ∨ ¬ tag (q*8+68) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*8+67)) (d := 0) (x := (q*8+67)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c62 := shortRun (t := (q*8+67)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c63 := shortRun (t := (q*8+67)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c64 := mustReset (t := (q*8+67)) (by omega)
  have c65 := distinctForms (t := (q*16+138)) (d := 0) (e := 1) (by norm_num [form]; omega)
  have c66 := distinctForms (t := (q*16+138)) (d := 1) (e := 2) (by norm_num [form]; omega)
  have c67 := ruledOut (t := (q*16+138)) (by omega) ih (by omega)
  have c68 := optionsAt (t := (q*32+276)) (by omega)
  have c69 := distinctForms (t := (q*32+276)) (d := 1) (e := 2) (by norm_num [form]; omega)
  have c70 := ruledOut (t := (q*32+276)) (by omega) ih (by omega)
  have c71 := alreadySeen (t := (q*8+68)) (i := (q*4+34)) (d := 0) (e := 0) (by omega) (by omega) (by norm_num [form]; omega)
  have c72 := shortRun (t := (q*8+68)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c73 : ¬ tag (q*8+68) 1 ∨ ¬ tag (q*8+69) 0 ∨ tag (q*4+34) 1 ∨ tag (q*8+68) 2 := by
    clear * - q
    apply earlier (t := (q*8+68)) (d := 1) (x := (q*4+33)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · exact .inl ((show i = q*4+34 by omega) ▸ a)
    · exact .inr (((show i = q*8+68 by omega) ▸ a))
    · omega
    · omega
    · omega
    · omega
  have c74 := differentTimes (t := (q*8+65)) (i := (q*32+263)) (d := 0) (e := 2) (by omega) (by norm_num [form]; omega)
  have c75 := optionsAt (t := (q*64+527)) (by omega)
  have c76 := differentTimes (t := (q*16+132)) (i := (q*32+264)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c77 := differentTimes (t := (q*16+132)) (i := (q*64+527)) (d := 1) (e := 3) (by omega) (by norm_num [form]; omega)
  have c78 := alreadySeen (t := (q*16+131)) (i := (q*8+66)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c79 := shortRun (t := (q*16+131)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c80 := mustReset (t := (q*16+131)) (by omega)
  have c81 := optionsAt (t := (q*32+266)) (by omega)
  have c82 := ruledOut (t := (q*32+266)) (by omega) ih (by omega)
  have c83 := optionsAt (t := (q*64+531)) (by omega)
  have c84 := ruledOut (t := (q*64+532)) (by omega) ih (by omega)
  have c85 := optionsAt (t := (q*64+533)) (by omega)
  have c86 := differentTimes (t := (q*16+133)) (i := (q*32+267)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c87 := differentTimes (t := (q*32+267)) (i := (q*64+531)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c88 := differentTimes (t := (q*32+267)) (i := (q*64+533)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c89 : ¬ tag (q*16+132) 0 ∨ ¬ tag (q*16+133) 0 ∨ tag (q*8+66) 0 := by
    clear * - q
    apply earlier (t := (q*16+132)) (d := 0) (x := (q*16+132)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*8+66 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c90 := shortRun (t := (q*16+133)) (d := 0) (by omega) (by norm_num [form])
  have c91 := optionsAt (t := (q*64+535)) (by omega)
  have c92 := ruledOut (t := (q*64+536)) (by omega) ih (by omega)
  have c93 := shortRun (t := (q*16+133)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c94 := shortRun (t := (q*16+133)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c95 := mustReset (t := (q*16+133)) (by omega)
  have c96 := shortRun (t := (q*16+134)) (d := 0) (by omega) (by norm_num [form])
  have c97 := ruledOut (t := (q*32+270)) (by omega) ih (by omega)
  have c98 := distinctForms (t := (q*64+540)) (d := 1) (e := 2) (by norm_num [form]; omega)
  have c99 := ruledOut (t := (q*64+540)) (by omega) ih (by omega)
  have c100 := optionsAt (t := (q*64+541)) (by omega)
  have c101 := differentTimes (t := (q*8+67)) (i := (q*32+271)) (d := 0) (e := 2) (by omega) (by norm_num [form]; omega)
  have c102 := differentTimes (t := (q*16+135)) (i := (q*32+271)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c103 := shortRun (t := (q*16+134)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c104 := shortRun (t := (q*16+134)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c105 := optionsAt (t := (q*64+543)) (by omega)
  have c106 := distinctForms (t := (q*64+544)) (d := 0) (e := 3) (by norm_num [form]; omega)
  have c107 := distinctForms (t := (q*64+544)) (d := 1) (e := 3) (by norm_num [form]; omega)
  have c108 := distinctForms (t := (q*64+544)) (d := 2) (e := 3) (by norm_num [form]; omega)
  have c109 := differentTimes (t := (q*16+136)) (i := (q*64+544)) (d := 1) (e := 3) (by omega) (by norm_num [form]; omega)
  have c110 := differentTimes (t := (q*32+272)) (i := (q*64+544)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c111 := differentTimes (t := (q*32+273)) (i := (q*64+544)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c112 := differentTimes (t := (q*64+543)) (i := (q*64+544)) (d := 3) (e := 3) (by omega) (by norm_num [form]; omega)
  have c113 : ¬ tag (q*16+135) 1 ∨ ¬ tag (q*16+136) 0 ∨ tag (q*8+68) 1 := by
    clear * - q
    apply earlier (t := (q*16+135)) (d := 1) (x := (q*8+67)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · exact ((show i = q*8+68 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
  have c114 := shortRun (t := (q*16+135)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c115 := mustReset (t := (q*16+135)) (by omega)
  have c116 := shortRun (t := (q*16+136)) (d := 0) (by omega) (by norm_num [form])
  have c117 := distinctForms (t := (q*32+274)) (d := 1) (e := 2) (by norm_num [form]; omega)
  have c118 := distinctForms (t := (q*64+547)) (d := 0) (e := 3) (by norm_num [form]; omega)
  have c119 := distinctForms (t := (q*64+548)) (d := 1) (e := 3) (by norm_num [form]; omega)
  have c120 := distinctForms (t := (q*64+549)) (d := 0) (e := 3) (by norm_num [form]; omega)
  have c121 : tag (q*8+68) 0 ∨ tag (q*16+137) 1 ∨ tag (q*32+274) 2 ∨ tag (q*32+275) 2 ∨ tag (q*64+547) 3 ∨ tag (q*64+548) 3 ∨ tag (q*64+549) 3 := by
    clear * - q
    obtain ⟨i, hi, hit⟩ := occurs.mp (deadline (q*16+136))
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact .inl ((show i = q*8+68 by omega) ▸ a)
    · exact .inr (.inl ((show i = q*16+137 by omega) ▸ a))
    · exact .inr (.inr (.inl ((show i = q*32+274 by omega) ▸ a)))
    · exact .inr (.inr (.inr (.inl ((show i = q*32+275 by omega) ▸ a))))
    · exact .inr (.inr (.inr (.inr (.inl ((show i = q*64+547 by omega) ▸ a)))))
    · exact .inr (.inr (.inr (.inr (.inr (.inl ((show i = q*64+548 by omega) ▸ a))))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (((show i = q*64+549 by omega) ▸ a)))))))
  have c122 := alreadySeen (t := (q*16+136)) (i := (q*8+68)) (d := 0) (e := 0) (by omega) (by omega) (by norm_num [form]; omega)
  have c123 := shortRun (t := (q*16+137)) (d := 0) (by omega) (by norm_num [form])
  have c124 := differentTimes (t := (q*16+138)) (i := (q*32+276)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c125 : ¬ tag (q*16+137) 0 ∨ ¬ tag (q*16+138) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*16+137)) (d := 0) (x := (q*16+137)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c126 := shortRun (t := (q*16+137)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c127 := shortRun (t := (q*16+137)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c128 := mustReset (t := (q*16+137)) (by omega)
  have c129 := differentTimes (t := (q*16+131)) (i := (q*64+527)) (d := 0) (e := 2) (by omega) (by norm_num [form]; omega)
  have c130 := differentTimes (t := (q*32+264)) (i := (q*64+529)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c131 := alreadySeen (t := (q*32+263)) (i := (q*16+132)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c132 := distinctForms (t := (q*64+530)) (d := 1) (e := 2) (by norm_num [form]; omega)
  have c133 : ¬ tag (q*32+264) 0 ∨ ¬ tag (q*32+265) 0 ∨ tag (q*16+132) 0 := by
    clear * - q
    apply earlier (t := (q*32+264)) (d := 0) (x := (q*32+264)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*16+132 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c134 := differentTimes (t := (q*32+266)) (i := (q*64+533)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c135 := shortRun (t := (q*32+265)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c136 := shortRun (t := (q*32+265)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c137 := mustReset (t := (q*32+265)) (by omega)
  have c138 := differentTimes (t := (q*16+133)) (i := (q*32+267)) (d := 0) (e := 1) (by omega) (by norm_num [form]; omega)
  have c139 := differentTimes (t := (q*16+133)) (i := (q*64+534)) (d := 0) (e := 2) (by omega) (by norm_num [form]; omega)
  have c140 := alreadySeen (t := (q*32+266)) (i := (q*16+133)) (d := 0) (e := 0) (by omega) (by omega) (by norm_num [form]; omega)
  have c141 := alreadySeen (t := (q*32+266)) (i := (q*16+135)) (d := 2) (e := 2) (by omega) (by omega) (by norm_num [form]; omega)
  have c142 : ¬ tag (q*32+267) 0 ∨ ¬ tag (q*32+268) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*32+267)) (d := 0) (x := (q*32+267)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c143 : ¬ tag (q*32+267) 1 ∨ ¬ tag (q*32+268) 0 ∨ tag (q*16+134) 1 := by
    clear * - q
    apply earlier (t := (q*32+267)) (d := 1) (x := (q*16+133)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · exact ((show i = q*16+134 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
  have c144 := optionsAt (t := (q*64+538)) (by omega)
  have c145 := ruledOut (t := (q*64+538)) (by omega) ih (by omega)
  have c146 := differentTimes (t := (q*32+269)) (i := (q*64+538)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c147 := shortRun (t := (q*32+268)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c148 := shortRun (t := (q*32+268)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c149 := shortRun (t := (q*32+269)) (d := 0) (by omega) (by norm_num [form])
  have c150 := shortRun (t := (q*32+269)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c151 := mustReset (t := (q*32+269)) (by omega)
  have c152 := shortRun (t := (q*32+270)) (d := 0) (by omega) (by norm_num [form])
  have c153 := ruledOut (t := (q*64+542)) (by omega) ih (by omega)
  have c154 := differentTimes (t := (q*16+135)) (i := (q*64+543)) (d := 0) (e := 2) (by omega) (by norm_num [form]; omega)
  have c155 := differentTimes (t := (q*32+271)) (i := (q*64+543)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c156 := shortRun (t := (q*32+270)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c157 : ¬ tag (q*32+271) 0 ∨ ¬ tag (q*32+272) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*32+271)) (d := 0) (x := (q*32+271)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c158 := shortRun (t := (q*32+272)) (d := 0) (by omega) (by norm_num [form])
  have c159 := differentTimes (t := (q*16+136)) (i := (q*32+273)) (d := 0) (e := 1) (by omega) (by norm_num [form]; omega)
  have c160 : ¬ tag (q*32+272) 0 ∨ ¬ tag (q*32+273) 0 ∨ tag (q*16+136) 0 := by
    clear * - q
    apply earlier (t := (q*32+272)) (d := 0) (x := (q*32+272)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*16+136 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c161 := shortRun (t := (q*32+272)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c162 : ¬ tag (q*32+272) 1 ∨ ¬ tag (q*32+273) 0 ∨ tag (q*16+136) 1 ∨ tag (q*32+272) 2 := by
    clear * - q
    apply earlier (t := (q*32+272)) (d := 1) (x := (q*16+135)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · exact .inl ((show i = q*16+136 by omega) ▸ a)
    · exact .inr (((show i = q*32+272 by omega) ▸ a))
    · omega
    · omega
    · omega
    · omega
  have c163 := shortRun (t := (q*32+273)) (d := 0) (by omega) (by norm_num [form])
  have c164 : ¬ tag (q*32+273) 0 ∨ ¬ tag (q*32+274) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*32+273)) (d := 0) (x := (q*32+273)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c165 := shortRun (t := (q*32+274)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c166 := alreadySeen (t := (q*32+274)) (i := (q*8+68)) (d := 1) (e := 0) (by omega) (by omega) (by norm_num [form]; omega)
  have c167 := alreadySeen (t := (q*32+274)) (i := (q*16+137)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c168 := shortRun (t := (q*32+275)) (d := 0) (by omega) (by norm_num [form])
  have c169 : ¬ tag (q*32+275) 0 ∨ ¬ tag (q*32+276) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*32+275)) (d := 0) (x := (q*32+275)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c170 := shortRun (t := (q*32+275)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c171 : ¬ tag (q*32+276) 0 ∨ ¬ tag (q*32+277) 0 ∨ tag (q*16+138) 0 := by
    clear * - q
    apply earlier (t := (q*32+276)) (d := 0) (x := (q*32+276)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*16+138 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c172 : ¬ tag (q*32+276) 1 ∨ ¬ tag (q*32+277) 0 ∨ tag (q*16+138) 1 ∨ tag (q*32+276) 2 := by
    clear * - q
    apply earlier (t := (q*32+276)) (d := 1) (x := (q*16+137)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · exact .inl ((show i = q*16+138 by omega) ▸ a)
    · exact .inr (((show i = q*32+276 by omega) ▸ a))
    · omega
    · omega
    · omega
    · omega
  have c173 := alreadySeen (t := (q*32+276)) (i := (q*16+138)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c174 := differentTimes (t := (q*32+263)) (i := (q*64+527)) (d := 0) (e := 1) (by omega) (by norm_num [form]; omega)
  have c175 := shortRun (t := (q*64+527)) (d := 0) (by omega) (by norm_num [form])
  have c176 : ¬ tag (q*64+527) 0 ∨ ¬ tag (q*64+528) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*64+527)) (d := 0) (x := (q*64+527)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c177 := shortRun (t := (q*64+528)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c178 := shortRun (t := (q*64+529)) (d := 0) (by omega) (by norm_num [form])
  have c179 : ¬ tag (q*64+529) 0 ∨ ¬ tag (q*64+530) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*64+529)) (d := 0) (x := (q*64+529)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c180 := differentTimes (t := (q*32+265)) (i := (q*64+531)) (d := 0) (e := 1) (by omega) (by norm_num [form]; omega)
  have c181 : ¬ tag (q*64+530) 1 ∨ ¬ tag (q*64+531) 0 ∨ tag (q*16+132) 0 ∨ tag (q*32+265) 1 ∨ tag (q*64+530) 2 := by
    clear * - q
    apply earlier (t := (q*64+530)) (d := 1) (x := (q*32+264)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact .inl ((show i = q*16+132 by omega) ▸ a)
    · exact .inr (.inl ((show i = q*32+265 by omega) ▸ a))
    · exact .inr (.inr (((show i = q*64+530 by omega) ▸ a)))
    · omega
    · omega
    · omega
    · omega
  have c182 := shortRun (t := (q*64+531)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c183 : ¬ tag (q*64+532) 0 ∨ ¬ tag (q*64+533) 0 ∨ tag (q*32+266) 0 := by
    clear * - q
    apply earlier (t := (q*64+532)) (d := 0) (x := (q*64+532)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*32+266 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c184 := shortRun (t := (q*64+533)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c185 : ¬ tag (q*64+534) 0 ∨ ¬ tag (q*64+535) 0 ∨ tag (q*32+267) 0 := by
    clear * - q
    apply earlier (t := (q*64+534)) (d := 0) (x := (q*64+534)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*32+267 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c186 := shortRun (t := (q*64+535)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c187 := shortRun (t := (q*64+535)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c188 := mustReset (t := (q*64+535)) (by omega)
  have c189 := shortRun (t := (q*64+536)) (d := 0) (by omega) (by norm_num [form])
  have c190 := differentTimes (t := (q*32+268)) (i := (q*64+537)) (d := 0) (e := 1) (by omega) (by norm_num [form]; omega)
  have c191 := alreadySeen (t := (q*64+536)) (i := (q*16+134)) (d := 2) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c192 : ¬ tag (q*64+537) 0 ∨ ¬ tag (q*64+538) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*64+537)) (d := 0) (x := (q*64+537)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c193 := shortRun (t := (q*64+538)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c194 := shortRun (t := (q*64+539)) (d := 0) (by omega) (by norm_num [form])
  have c195 := shortRun (t := (q*64+539)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c196 : ¬ tag (q*64+540) 0 ∨ ¬ tag (q*64+541) 0 ∨ tag (q*32+270) 0 := by
    clear * - q
    apply earlier (t := (q*64+540)) (d := 0) (x := (q*64+540)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*32+270 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c197 : ¬ tag (q*64+540) 1 ∨ ¬ tag (q*64+541) 0 ∨ tag (q*32+270) 1 ∨ tag (q*64+540) 2 := by
    clear * - q
    apply earlier (t := (q*64+540)) (d := 1) (x := (q*32+269)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · exact .inl ((show i = q*32+270 by omega) ▸ a)
    · exact .inr (((show i = q*64+540 by omega) ▸ a))
    · omega
    · omega
    · omega
    · omega
  have c198 := shortRun (t := (q*64+541)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c199 := shortRun (t := (q*64+541)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c200 := mustReset (t := (q*64+541)) (by omega)
  have c201 := shortRun (t := (q*64+542)) (d := 0) (by omega) (by norm_num [form])
  have c202 := shortRun (t := (q*64+542)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c203 := shortRun (t := (q*64+543)) (d := 0) (by omega) (by norm_num [form])
  have c204 := shortRun (t := (q*64+543)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c205 := mustReset (t := (q*64+544)) (by omega)
  have c206 := shortRun (t := (q*64+545)) (d := 0) (by omega) (by norm_num [form])
  have c207 : ¬ tag (q*64+545) 0 ∨ ¬ tag (q*64+546) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*64+545)) (d := 0) (x := (q*64+545)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c208 := alreadySeen (t := (q*64+546)) (i := (q*16+136)) (d := 1) (e := 0) (by omega) (by omega) (by norm_num [form]; omega)
  have c209 := alreadySeen (t := (q*64+546)) (i := (q*32+273)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c210 := shortRun (t := (q*64+547)) (d := 0) (by omega) (by norm_num [form])
  have c211 : ¬ tag (q*64+547) 0 ∨ ¬ tag (q*64+548) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*64+547)) (d := 0) (x := (q*64+547)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c212 := alreadySeen (t := (q*64+548)) (i := (q*32+274)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  grind (splits := 256) only


set_option maxRecDepth 6000 in
set_option maxHeartbeats 3500000 in
/-- Excludes the extra position for `n = 16q + 143`. -/
private lemma exclude16_15 (q : ℕ) (ih : ∀ x i, 1 < x → x < q*16+143 → value i = x → six x i) :
    ¬ tag (q*64+576) 3 := by
  intro bad
  have c0 := optionsAt (t := (q*8+69)) (by omega)
  have c1 := optionsAt (t := (q*8+70)) (by omega)
  have c2 := ruledOut (t := (q*8+70)) (by omega) ih (by omega)
  have c3 := optionsAt (t := (q*8+71)) (by omega)
  have c4 := optionsAt (t := (q*16+139)) (by omega)
  have c5 := optionsAt (t := (q*16+140)) (by omega)
  have c6 := ruledOut (t := (q*16+140)) (by omega) ih (by omega)
  have c7 := optionsAt (t := (q*16+141)) (by omega)
  have c8 := optionsAt (t := (q*4+36)) (by omega)
  have c9 := ruledOut (t := (q*4+36)) (by omega) ih (by omega)
  have c10 := optionsAt (t := (q*8+72)) (by omega)
  have c11 := distinctForms (t := (q*8+72)) (d := 0) (e := 1) (by norm_num [form]; omega)
  have c12 := distinctForms (t := (q*8+72)) (d := 0) (e := 2) (by norm_num [form]; omega)
  have c13 := distinctForms (t := (q*8+72)) (d := 1) (e := 2) (by norm_num [form]; omega)
  have c14 := ruledOut (t := (q*8+72)) (by omega) ih (by omega)
  have c15 := distinctForms (t := (q*8+73)) (d := 0) (e := 2) (by norm_num [form]; omega)
  have c16 := optionsAt (t := (q*16+143)) (by omega)
  have c17 := distinctForms (t := (q*16+143)) (d := 2) (e := 3) (by norm_num [form]; omega)
  have c18 := optionsAt (t := (q*16+144)) (by omega)
  have c19 := distinctForms (t := (q*16+144)) (d := 0) (e := 2) (by norm_num [form]; omega)
  have c20 := ruledOut (t := (q*16+144)) (by omega) ih (by omega)
  have c21 : tag (q*4+36) 1 ∨ tag (q*8+72) 2 ∨ tag (q*8+73) 2 ∨ tag (q*16+143) 3 ∨ tag (q*16+144) 3 ∨ tag (q*16+145) 3 := by
    clear * - q
    obtain ⟨i, hi, hit⟩ := occurs.mp (deadline (q*4+35))
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · exact .inl ((show i = q*4+36 by omega) ▸ a)
    · exact .inr (.inl ((show i = q*8+72 by omega) ▸ a))
    · exact .inr (.inr (.inl ((show i = q*8+73 by omega) ▸ a)))
    · exact .inr (.inr (.inr (.inl ((show i = q*16+143 by omega) ▸ a))))
    · exact .inr (.inr (.inr (.inr (.inl ((show i = q*16+144 by omega) ▸ a)))))
    · exact .inr (.inr (.inr (.inr (.inr (((show i = q*16+145 by omega) ▸ a))))))
  have c22 := differentTimes (t := (q*4+36)) (i := (q*16+143)) (d := 1) (e := 3) (by omega) (by norm_num [form]; omega)
  have c23 := differentTimes (t := (q*8+72)) (i := (q*16+143)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c24 := differentTimes (t := (q*8+73)) (i := (q*16+143)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c25 := shortRun (t := (q*4+36)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c26 : ¬ tag (q*4+36) 1 ∨ ¬ tag (q*4+37) 0 ∨ tag (q*2+18) 1 ∨ tag (q*4+36) 2 := by
    clear * - q
    apply earlier (t := (q*4+36)) (d := 1) (x := (q*2+17)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · exact .inl ((show i = q*2+18 by omega) ▸ a)
    · exact .inr (((show i = q*4+36 by omega) ▸ a))
    · omega
    · omega
    · omega
    · omega
  have c27 := optionsAt (t := (q*32+279)) (by omega)
  have c28 := optionsAt (t := (q*32+280)) (by omega)
  have c29 := ruledOut (t := (q*32+280)) (by omega) ih (by omega)
  have c30 := optionsAt (t := (q*32+281)) (by omega)
  have c31 := differentTimes (t := (q*8+70)) (i := (q*16+140)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c32 := differentTimes (t := (q*8+70)) (i := (q*32+279)) (d := 1) (e := 3) (by omega) (by norm_num [form]; omega)
  have c33 := shortRun (t := (q*8+69)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c34 := shortRun (t := (q*8+69)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c35 := mustReset (t := (q*8+69)) (by omega)
  have c36 := shortRun (t := (q*8+70)) (d := 0) (by omega) (by norm_num [form])
  have c37 := optionsAt (t := (q*16+142)) (by omega)
  have c38 := ruledOut (t := (q*16+142)) (by omega) ih (by omega)
  have c39 := optionsAt (t := (q*32+283)) (by omega)
  have c40 := optionsAt (t := (q*32+284)) (by omega)
  have c41 := ruledOut (t := (q*32+284)) (by omega) ih (by omega)
  have c42 := optionsAt (t := (q*32+285)) (by omega)
  have c43 := differentTimes (t := (q*8+71)) (i := (q*16+143)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c44 := differentTimes (t := (q*16+142)) (i := (q*32+283)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c45 := differentTimes (t := (q*16+143)) (i := (q*32+283)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c46 := alreadySeen (t := (q*8+70)) (i := (q*2+18)) (d := 2) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c47 := alreadySeen (t := (q*8+70)) (i := (q*4+36)) (d := 2) (e := 2) (by omega) (by omega) (by norm_num [form]; omega)
  have c48 := alreadySeen (t := (q*8+70)) (i := (q*4+37)) (d := 2) (e := 2) (by omega) (by omega) (by norm_num [form]; omega)
  have c49 := shortRun (t := (q*8+71)) (d := 0) (by omega) (by norm_num [form])
  have c50 := optionsAt (t := (q*32+287)) (by omega)
  have c51 := distinctForms (t := (q*32+287)) (d := 2) (e := 3) (by norm_num [form]; omega)
  have c52 := optionsAt (t := (q*32+288)) (by omega)
  have c53 := ruledOut (t := (q*32+288)) (by omega) ih (by omega)
  have c54 := optionsAt (t := (q*32+289)) (by omega)
  have c55 := distinctForms (t := (q*32+289)) (d := 0) (e := 3) (by norm_num [form]; omega)
  have c56 := distinctForms (t := (q*32+289)) (d := 1) (e := 3) (by norm_num [form]; omega)
  have c57 : tag (q*8+72) 1 ∨ tag (q*16+144) 2 ∨ tag (q*16+145) 2 ∨ tag (q*32+287) 3 ∨ tag (q*32+288) 3 ∨ tag (q*32+289) 3 := by
    clear * - q
    obtain ⟨i, hi, hit⟩ := occurs.mp (deadline (q*8+71))
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · exact .inl ((show i = q*8+72 by omega) ▸ a)
    · exact .inr (.inl ((show i = q*16+144 by omega) ▸ a))
    · exact .inr (.inr (.inl ((show i = q*16+145 by omega) ▸ a)))
    · exact .inr (.inr (.inr (.inl ((show i = q*32+287 by omega) ▸ a))))
    · exact .inr (.inr (.inr (.inr (.inl ((show i = q*32+288 by omega) ▸ a)))))
    · exact .inr (.inr (.inr (.inr (.inr (((show i = q*32+289 by omega) ▸ a))))))
  have c58 := differentTimes (t := (q*8+72)) (i := (q*32+287)) (d := 1) (e := 3) (by omega) (by norm_num [form]; omega)
  have c59 := differentTimes (t := (q*16+144)) (i := (q*32+287)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c60 : ¬ tag (q*8+71) 0 ∨ ¬ tag (q*8+72) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*8+71)) (d := 0) (x := (q*8+71)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c61 := shortRun (t := (q*8+71)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c62 := shortRun (t := (q*8+71)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c63 := mustReset (t := (q*8+71)) (by omega)
  have c64 := distinctForms (t := (q*16+146)) (d := 0) (e := 1) (by norm_num [form]; omega)
  have c65 := distinctForms (t := (q*16+146)) (d := 1) (e := 2) (by norm_num [form]; omega)
  have c66 := ruledOut (t := (q*16+146)) (by omega) ih (by omega)
  have c67 := optionsAt (t := (q*32+292)) (by omega)
  have c68 := distinctForms (t := (q*32+292)) (d := 1) (e := 2) (by norm_num [form]; omega)
  have c69 := ruledOut (t := (q*32+292)) (by omega) ih (by omega)
  have c70 := alreadySeen (t := (q*8+72)) (i := (q*4+36)) (d := 0) (e := 0) (by omega) (by omega) (by norm_num [form]; omega)
  have c71 := shortRun (t := (q*8+72)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c72 : ¬ tag (q*8+72) 1 ∨ ¬ tag (q*8+73) 0 ∨ tag (q*4+36) 1 ∨ tag (q*8+72) 2 := by
    clear * - q
    apply earlier (t := (q*8+72)) (d := 1) (x := (q*4+35)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · exact .inl ((show i = q*4+36 by omega) ▸ a)
    · exact .inr (((show i = q*8+72 by omega) ▸ a))
    · omega
    · omega
    · omega
    · omega
  have c73 := differentTimes (t := (q*8+69)) (i := (q*32+279)) (d := 0) (e := 2) (by omega) (by norm_num [form]; omega)
  have c74 := optionsAt (t := (q*64+559)) (by omega)
  have c75 := differentTimes (t := (q*16+140)) (i := (q*32+280)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c76 := differentTimes (t := (q*16+140)) (i := (q*64+559)) (d := 1) (e := 3) (by omega) (by norm_num [form]; omega)
  have c77 := alreadySeen (t := (q*16+139)) (i := (q*8+70)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c78 := shortRun (t := (q*16+139)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c79 := mustReset (t := (q*16+139)) (by omega)
  have c80 := optionsAt (t := (q*32+282)) (by omega)
  have c81 := ruledOut (t := (q*32+282)) (by omega) ih (by omega)
  have c82 := optionsAt (t := (q*64+563)) (by omega)
  have c83 := ruledOut (t := (q*64+564)) (by omega) ih (by omega)
  have c84 := optionsAt (t := (q*64+565)) (by omega)
  have c85 := differentTimes (t := (q*16+141)) (i := (q*32+283)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c86 := differentTimes (t := (q*32+283)) (i := (q*64+563)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c87 := differentTimes (t := (q*32+283)) (i := (q*64+565)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c88 : ¬ tag (q*16+140) 0 ∨ ¬ tag (q*16+141) 0 ∨ tag (q*8+70) 0 := by
    clear * - q
    apply earlier (t := (q*16+140)) (d := 0) (x := (q*16+140)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*8+70 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c89 := shortRun (t := (q*16+141)) (d := 0) (by omega) (by norm_num [form])
  have c90 := optionsAt (t := (q*64+567)) (by omega)
  have c91 := ruledOut (t := (q*64+568)) (by omega) ih (by omega)
  have c92 := shortRun (t := (q*16+141)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c93 := shortRun (t := (q*16+141)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c94 := mustReset (t := (q*16+141)) (by omega)
  have c95 := shortRun (t := (q*16+142)) (d := 0) (by omega) (by norm_num [form])
  have c96 := ruledOut (t := (q*32+286)) (by omega) ih (by omega)
  have c97 := distinctForms (t := (q*64+572)) (d := 1) (e := 2) (by norm_num [form]; omega)
  have c98 := ruledOut (t := (q*64+572)) (by omega) ih (by omega)
  have c99 := optionsAt (t := (q*64+573)) (by omega)
  have c100 := differentTimes (t := (q*8+71)) (i := (q*32+287)) (d := 0) (e := 2) (by omega) (by norm_num [form]; omega)
  have c101 := differentTimes (t := (q*16+143)) (i := (q*32+287)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c102 := shortRun (t := (q*16+142)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c103 := shortRun (t := (q*16+142)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c104 := optionsAt (t := (q*64+575)) (by omega)
  have c105 := distinctForms (t := (q*64+576)) (d := 0) (e := 3) (by norm_num [form]; omega)
  have c106 := distinctForms (t := (q*64+576)) (d := 1) (e := 3) (by norm_num [form]; omega)
  have c107 := distinctForms (t := (q*64+576)) (d := 2) (e := 3) (by norm_num [form]; omega)
  have c108 := differentTimes (t := (q*16+144)) (i := (q*64+576)) (d := 1) (e := 3) (by omega) (by norm_num [form]; omega)
  have c109 := differentTimes (t := (q*32+288)) (i := (q*64+576)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c110 := differentTimes (t := (q*32+289)) (i := (q*64+576)) (d := 2) (e := 3) (by omega) (by norm_num [form]; omega)
  have c111 := differentTimes (t := (q*64+575)) (i := (q*64+576)) (d := 3) (e := 3) (by omega) (by norm_num [form]; omega)
  have c112 : ¬ tag (q*16+143) 1 ∨ ¬ tag (q*16+144) 0 ∨ tag (q*8+72) 1 := by
    clear * - q
    apply earlier (t := (q*16+143)) (d := 1) (x := (q*8+71)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · exact ((show i = q*8+72 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
  have c113 := shortRun (t := (q*16+143)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c114 := mustReset (t := (q*16+143)) (by omega)
  have c115 := shortRun (t := (q*16+144)) (d := 0) (by omega) (by norm_num [form])
  have c116 := distinctForms (t := (q*32+290)) (d := 1) (e := 2) (by norm_num [form]; omega)
  have c117 := distinctForms (t := (q*64+579)) (d := 0) (e := 3) (by norm_num [form]; omega)
  have c118 := distinctForms (t := (q*64+580)) (d := 1) (e := 3) (by norm_num [form]; omega)
  have c119 := distinctForms (t := (q*64+581)) (d := 0) (e := 3) (by norm_num [form]; omega)
  have c120 : tag (q*8+72) 0 ∨ tag (q*16+145) 1 ∨ tag (q*32+290) 2 ∨ tag (q*32+291) 2 ∨ tag (q*64+579) 3 ∨ tag (q*64+580) 3 ∨ tag (q*64+581) 3 := by
    clear * - q
    obtain ⟨i, hi, hit⟩ := occurs.mp (deadline (q*16+144))
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact .inl ((show i = q*8+72 by omega) ▸ a)
    · exact .inr (.inl ((show i = q*16+145 by omega) ▸ a))
    · exact .inr (.inr (.inl ((show i = q*32+290 by omega) ▸ a)))
    · exact .inr (.inr (.inr (.inl ((show i = q*32+291 by omega) ▸ a))))
    · exact .inr (.inr (.inr (.inr (.inl ((show i = q*64+579 by omega) ▸ a)))))
    · exact .inr (.inr (.inr (.inr (.inr (.inl ((show i = q*64+580 by omega) ▸ a))))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (((show i = q*64+581 by omega) ▸ a)))))))
  have c121 := alreadySeen (t := (q*16+144)) (i := (q*8+72)) (d := 0) (e := 0) (by omega) (by omega) (by norm_num [form]; omega)
  have c122 := shortRun (t := (q*16+145)) (d := 0) (by omega) (by norm_num [form])
  have c123 := differentTimes (t := (q*16+146)) (i := (q*32+292)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c124 : ¬ tag (q*16+145) 0 ∨ ¬ tag (q*16+146) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*16+145)) (d := 0) (x := (q*16+145)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c125 := shortRun (t := (q*16+145)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c126 := shortRun (t := (q*16+145)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c127 := mustReset (t := (q*16+145)) (by omega)
  have c128 := differentTimes (t := (q*16+139)) (i := (q*64+559)) (d := 0) (e := 2) (by omega) (by norm_num [form]; omega)
  have c129 := differentTimes (t := (q*32+280)) (i := (q*64+561)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c130 := alreadySeen (t := (q*32+279)) (i := (q*16+140)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c131 := distinctForms (t := (q*64+562)) (d := 1) (e := 2) (by norm_num [form]; omega)
  have c132 : ¬ tag (q*32+280) 0 ∨ ¬ tag (q*32+281) 0 ∨ tag (q*16+140) 0 := by
    clear * - q
    apply earlier (t := (q*32+280)) (d := 0) (x := (q*32+280)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*16+140 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c133 := differentTimes (t := (q*32+282)) (i := (q*64+565)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c134 := shortRun (t := (q*32+281)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c135 := shortRun (t := (q*32+281)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c136 := mustReset (t := (q*32+281)) (by omega)
  have c137 := differentTimes (t := (q*16+141)) (i := (q*32+283)) (d := 0) (e := 1) (by omega) (by norm_num [form]; omega)
  have c138 := differentTimes (t := (q*16+141)) (i := (q*64+566)) (d := 0) (e := 2) (by omega) (by norm_num [form]; omega)
  have c139 := alreadySeen (t := (q*32+282)) (i := (q*16+141)) (d := 0) (e := 0) (by omega) (by omega) (by norm_num [form]; omega)
  have c140 := alreadySeen (t := (q*32+282)) (i := (q*16+143)) (d := 2) (e := 2) (by omega) (by omega) (by norm_num [form]; omega)
  have c141 : ¬ tag (q*32+283) 0 ∨ ¬ tag (q*32+284) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*32+283)) (d := 0) (x := (q*32+283)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c142 : ¬ tag (q*32+283) 1 ∨ ¬ tag (q*32+284) 0 ∨ tag (q*16+142) 1 := by
    clear * - q
    apply earlier (t := (q*32+283)) (d := 1) (x := (q*16+141)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · exact ((show i = q*16+142 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
  have c143 := optionsAt (t := (q*64+570)) (by omega)
  have c144 := ruledOut (t := (q*64+570)) (by omega) ih (by omega)
  have c145 := differentTimes (t := (q*32+285)) (i := (q*64+570)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c146 := shortRun (t := (q*32+284)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c147 := shortRun (t := (q*32+284)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c148 := shortRun (t := (q*32+285)) (d := 0) (by omega) (by norm_num [form])
  have c149 := shortRun (t := (q*32+285)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c150 := mustReset (t := (q*32+285)) (by omega)
  have c151 := shortRun (t := (q*32+286)) (d := 0) (by omega) (by norm_num [form])
  have c152 := ruledOut (t := (q*64+574)) (by omega) ih (by omega)
  have c153 := differentTimes (t := (q*16+143)) (i := (q*64+575)) (d := 0) (e := 2) (by omega) (by norm_num [form]; omega)
  have c154 := differentTimes (t := (q*32+287)) (i := (q*64+575)) (d := 1) (e := 2) (by omega) (by norm_num [form]; omega)
  have c155 := shortRun (t := (q*32+286)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c156 : ¬ tag (q*32+287) 0 ∨ ¬ tag (q*32+288) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*32+287)) (d := 0) (x := (q*32+287)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c157 := shortRun (t := (q*32+288)) (d := 0) (by omega) (by norm_num [form])
  have c158 := differentTimes (t := (q*16+144)) (i := (q*32+289)) (d := 0) (e := 1) (by omega) (by norm_num [form]; omega)
  have c159 : ¬ tag (q*32+288) 0 ∨ ¬ tag (q*32+289) 0 ∨ tag (q*16+144) 0 := by
    clear * - q
    apply earlier (t := (q*32+288)) (d := 0) (x := (q*32+288)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*16+144 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c160 := shortRun (t := (q*32+288)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c161 : ¬ tag (q*32+288) 1 ∨ ¬ tag (q*32+289) 0 ∨ tag (q*16+144) 1 ∨ tag (q*32+288) 2 := by
    clear * - q
    apply earlier (t := (q*32+288)) (d := 1) (x := (q*16+143)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · exact .inl ((show i = q*16+144 by omega) ▸ a)
    · exact .inr (((show i = q*32+288 by omega) ▸ a))
    · omega
    · omega
    · omega
    · omega
  have c162 := shortRun (t := (q*32+289)) (d := 0) (by omega) (by norm_num [form])
  have c163 : ¬ tag (q*32+289) 0 ∨ ¬ tag (q*32+290) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*32+289)) (d := 0) (x := (q*32+289)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c164 := shortRun (t := (q*32+290)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c165 := alreadySeen (t := (q*32+290)) (i := (q*8+72)) (d := 1) (e := 0) (by omega) (by omega) (by norm_num [form]; omega)
  have c166 := alreadySeen (t := (q*32+290)) (i := (q*16+145)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c167 := shortRun (t := (q*32+291)) (d := 0) (by omega) (by norm_num [form])
  have c168 : ¬ tag (q*32+291) 0 ∨ ¬ tag (q*32+292) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*32+291)) (d := 0) (x := (q*32+291)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c169 := shortRun (t := (q*32+291)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c170 : ¬ tag (q*32+292) 0 ∨ ¬ tag (q*32+293) 0 ∨ tag (q*16+146) 0 := by
    clear * - q
    apply earlier (t := (q*32+292)) (d := 0) (x := (q*32+292)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*16+146 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c171 : ¬ tag (q*32+292) 1 ∨ ¬ tag (q*32+293) 0 ∨ tag (q*16+146) 1 ∨ tag (q*32+292) 2 := by
    clear * - q
    apply earlier (t := (q*32+292)) (d := 1) (x := (q*16+145)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · exact .inl ((show i = q*16+146 by omega) ▸ a)
    · exact .inr (((show i = q*32+292 by omega) ▸ a))
    · omega
    · omega
    · omega
    · omega
  have c172 := alreadySeen (t := (q*32+292)) (i := (q*16+146)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c173 := differentTimes (t := (q*32+279)) (i := (q*64+559)) (d := 0) (e := 1) (by omega) (by norm_num [form]; omega)
  have c174 := shortRun (t := (q*64+559)) (d := 0) (by omega) (by norm_num [form])
  have c175 : ¬ tag (q*64+559) 0 ∨ ¬ tag (q*64+560) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*64+559)) (d := 0) (x := (q*64+559)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c176 := shortRun (t := (q*64+560)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c177 := shortRun (t := (q*64+561)) (d := 0) (by omega) (by norm_num [form])
  have c178 : ¬ tag (q*64+561) 0 ∨ ¬ tag (q*64+562) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*64+561)) (d := 0) (x := (q*64+561)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c179 := differentTimes (t := (q*32+281)) (i := (q*64+563)) (d := 0) (e := 1) (by omega) (by norm_num [form]; omega)
  have c180 : ¬ tag (q*64+562) 1 ∨ ¬ tag (q*64+563) 0 ∨ tag (q*16+140) 0 ∨ tag (q*32+281) 1 ∨ tag (q*64+562) 2 := by
    clear * - q
    apply earlier (t := (q*64+562)) (d := 1) (x := (q*32+280)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact .inl ((show i = q*16+140 by omega) ▸ a)
    · exact .inr (.inl ((show i = q*32+281 by omega) ▸ a))
    · exact .inr (.inr (((show i = q*64+562 by omega) ▸ a)))
    · omega
    · omega
    · omega
    · omega
  have c181 := shortRun (t := (q*64+563)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c182 : ¬ tag (q*64+564) 0 ∨ ¬ tag (q*64+565) 0 ∨ tag (q*32+282) 0 := by
    clear * - q
    apply earlier (t := (q*64+564)) (d := 0) (x := (q*64+564)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*32+282 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c183 := shortRun (t := (q*64+565)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c184 : ¬ tag (q*64+566) 0 ∨ ¬ tag (q*64+567) 0 ∨ tag (q*32+283) 0 := by
    clear * - q
    apply earlier (t := (q*64+566)) (d := 0) (x := (q*64+566)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*32+283 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c185 := shortRun (t := (q*64+567)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c186 := shortRun (t := (q*64+567)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c187 := mustReset (t := (q*64+567)) (by omega)
  have c188 := shortRun (t := (q*64+568)) (d := 0) (by omega) (by norm_num [form])
  have c189 := differentTimes (t := (q*32+284)) (i := (q*64+569)) (d := 0) (e := 1) (by omega) (by norm_num [form]; omega)
  have c190 := alreadySeen (t := (q*64+568)) (i := (q*16+142)) (d := 2) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c191 : ¬ tag (q*64+569) 0 ∨ ¬ tag (q*64+570) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*64+569)) (d := 0) (x := (q*64+569)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c192 := shortRun (t := (q*64+570)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c193 := shortRun (t := (q*64+571)) (d := 0) (by omega) (by norm_num [form])
  have c194 := shortRun (t := (q*64+571)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c195 : ¬ tag (q*64+572) 0 ∨ ¬ tag (q*64+573) 0 ∨ tag (q*32+286) 0 := by
    clear * - q
    apply earlier (t := (q*64+572)) (d := 0) (x := (q*64+572)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · exact ((show i = q*32+286 by omega) ▸ a)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c196 : ¬ tag (q*64+572) 1 ∨ ¬ tag (q*64+573) 0 ∨ tag (q*32+286) 1 ∨ tag (q*64+572) 2 := by
    clear * - q
    apply earlier (t := (q*64+572)) (d := 1) (x := (q*32+285)) (by omega) (by norm_num [form]; omega)
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · exact .inl ((show i = q*32+286 by omega) ▸ a)
    · exact .inr (((show i = q*64+572 by omega) ▸ a))
    · omega
    · omega
    · omega
    · omega
  have c197 := shortRun (t := (q*64+573)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c198 := shortRun (t := (q*64+573)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c199 := mustReset (t := (q*64+573)) (by omega)
  have c200 := shortRun (t := (q*64+574)) (d := 0) (by omega) (by norm_num [form])
  have c201 := shortRun (t := (q*64+574)) (d := 2) (by omega) (by norm_num [form]; omega)
  have c202 := shortRun (t := (q*64+575)) (d := 0) (by omega) (by norm_num [form])
  have c203 := shortRun (t := (q*64+575)) (d := 1) (by omega) (by norm_num [form]; omega)
  have c204 := mustReset (t := (q*64+576)) (by omega)
  have c205 := shortRun (t := (q*64+577)) (d := 0) (by omega) (by norm_num [form])
  have c206 : ¬ tag (q*64+577) 0 ∨ ¬ tag (q*64+578) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*64+577)) (d := 0) (x := (q*64+577)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c207 := alreadySeen (t := (q*64+578)) (i := (q*16+144)) (d := 1) (e := 0) (by omega) (by omega) (by norm_num [form]; omega)
  have c208 := alreadySeen (t := (q*64+578)) (i := (q*32+289)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  have c209 := shortRun (t := (q*64+579)) (d := 0) (by omega) (by norm_num [form])
  have c210 : ¬ tag (q*64+579) 0 ∨ ¬ tag (q*64+580) 0 ∨ False := by
    clear * - q
    apply earlier (t := (q*64+579)) (d := 0) (x := (q*64+579)) (by omega) (by norm_num [form])
    intro i hi hit
    rcases positionOf (by omega) hit with ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩ | ⟨h, a⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have c211 := alreadySeen (t := (q*64+580)) (i := (q*32+290)) (d := 1) (e := 1) (by omega) (by omega) (by norm_num [form]; omega)
  grind (splits := 256) only


set_option maxRecDepth 6000 in
set_option maxHeartbeats 1000000 in
private lemma allSix (n : ℕ) : ∀ i, 1 < n → value i = n → six n i := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro i hn hv
    rcases seven hn hv with good | bad
    · exact good
    subst i
    exfalso
    by_cases small : n < 128
    · exact initial n (Finset.mem_range.mpr small) hn hv
    have past : ∀ x i, 1 < x → x < n → value i = x → six x i := fun x i hx hlt => ih x hlt i hx
    have marked : tag (4*n+4) 3 := tagged.mpr (by rw [hv]; norm_num [form]; omega)
    by_cases r0 : n % 4 = 0
    · obtain ⟨q, rfl⟩ : ∃ q, n = q*4+128 := ⟨(n-128)/4, by omega⟩
      apply exclude4_0 q past
      exact (congrArg (fun j : ℕ => tag j 3 = true) (show 4*(q*4+128)+4 = q*16+516 by omega)).mp marked
    by_cases r1 : n % 4 = 1
    · obtain ⟨q, rfl⟩ : ∃ q, n = q*4+129 := ⟨(n-129)/4, by omega⟩
      apply exclude4_1 q past
      exact (congrArg (fun j : ℕ => tag j 3 = true) (show 4*(q*4+129)+4 = q*16+520 by omega)).mp marked
    by_cases r2 : n % 4 = 2
    · obtain ⟨q, rfl⟩ : ∃ q, n = q*4+130 := ⟨(n-130)/4, by omega⟩
      apply exclude4_2 q past
      exact (congrArg (fun j : ℕ => tag j 3 = true) (show 4*(q*4+130)+4 = q*16+524 by omega)).mp marked
    by_cases r3 : n % 8 = 3
    · obtain ⟨q, rfl⟩ : ∃ q, n = q*8+131 := ⟨(n-131)/8, by omega⟩
      apply exclude8_3 q past
      exact (congrArg (fun j : ℕ => tag j 3 = true) (show 4*(q*8+131)+4 = q*32+528 by omega)).mp marked
    by_cases r4 : n % 16 = 7
    · obtain ⟨q, rfl⟩ : ∃ q, n = q*16+135 := ⟨(n-135)/16, by omega⟩
      apply exclude16_7 q past
      exact (congrArg (fun j : ℕ => tag j 3 = true) (show 4*(q*16+135)+4 = q*64+544 by omega)).mp marked
    obtain ⟨q, rfl⟩ : ∃ q, n = q*16+143 := ⟨(n-143)/16, by omega⟩
    apply exclude16_15 q past
    exact (congrArg (fun j : ℕ => tag j 3 = true) (show 4*(q*16+143)+4 = q*64+576 by omega)).mp marked

end OMA.Halving

open OMA.S_oeis_a050129 OMA.Halving

theorem OMA.solution : type_of% @OMA.S_oeis_a050129.main := by
  intro n hn
  obtain ⟨k, _, hk⟩ := occurs.mp (deadline n)
  have pos : 0 < k := by
    by_contra! h
    have h0 : k = 0 := by omega
    subst k
    change 0 = n at hk
    omega
  exact ⟨k, pos, hk, fun j _ hj => (uniqueIndex (hk.trans hj.symm)).le, allSix n k hn hk⟩
