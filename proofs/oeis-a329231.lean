import OMAStatements.S_oeis_a329231
import Mathlib

namespace OMA.A329231Proof

open OMA.S_oeis_a329231

/-- Digit `q` of `T` in base `65536`: the packed visit count of position `q`. -/
def dig (T q : ℕ) : ℕ := T / 65536 ^ q % 65536

/-- The next position of the packed simulation: hop of length `j` from `cur`, packed counts `T`. -/
def hopS (n j cur T : ℕ) : ℕ :=
  if dig T ((cur + (n - j % n)) % n) < dig T ((cur + j) % n) then (cur + (n - j % n)) % n
  else (cur + j) % n

/-- `f` more hops of the packed simulation; the next hop has length `j`. The test is at the head of each step,
so the kernel evaluates the state step by step. -/
def loop (n : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, _, cur, T => (cur, T)
  | f + 1, j, cur, T =>
    let cw := (cur + j) % n
    let ccw := (cur + (n - j % n)) % n
    if dig T ccw < dig T cw then loop n f (j + 1) ccw (T + 65536 ^ ccw)
    else loop n f (j + 1) cw (T + 65536 ^ cw)

theorem loop_succ (n f j cur T : ℕ) :
    loop n (f + 1) j cur T = loop n f (j + 1) (hopS n j cur T) (T + 65536 ^ hopS n j cur T) := by
  unfold hopS
  split_ifs with h
  · simp only [loop, h, ↓reduceIte]
  · simp only [loop, h, ↓reduceIte]

/-- All of `P 0, …, P (m - 1)` hold. -/
def checkAll (P : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | m + 1 => P m && checkAll P m

theorem checkAll_true (P : ℕ → Bool) : ∀ m, checkAll P m = true → ∀ p, p < m → P p = true
  | 0, _, p, hp => absurd hp (Nat.not_lt_zero p)
  | m + 1, h, p, hp => by
    have h1 : P m = true ∧ checkAll P m = true := by simpa [checkAll] using h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp' | hp'
    · exact checkAll_true P m h1.2 p hp'
    · rw [hp']; exact h1.1

theorem checkAll_false (P : ℕ → Bool) : ∀ m, checkAll P m = false → ∃ p, p < m ∧ P p = false
  | 0, h => by simp [checkAll] at h
  | m + 1, h => by
    cases hm : P m with
    | false => exact ⟨m, Nat.lt_succ_self m, hm⟩
    | true =>
      have h' : checkAll P m = false := by simpa [checkAll, hm] using h
      obtain ⟨p, hp, hP⟩ := checkAll_false P m h'
      exact ⟨p, by omega, hP⟩

theorem add_pow_div (T p : ℕ) : (T + 65536 ^ p) / 65536 ^ p = T / 65536 ^ p + 1 := by
  have hp : 0 < (65536 : ℕ) ^ p := pow_pos (by norm_num) p
  exact Nat.add_div_right T hp

/-- Adding `65536 ^ p` adds one to digit `p` and keeps the other digits, when digit `p` is below `65535`. -/
theorem dig_add (T p q : ℕ) (h : dig T p + 1 < 65536) :
    dig (T + 65536 ^ p) q = if q = p then dig T p + 1 else dig T q := by
  have hpos : ∀ i : ℕ, 0 < (65536 : ℕ) ^ i := fun i => pow_pos (by norm_num) i
  unfold dig at h ⊢
  rcases lt_trichotomy q p with hlt | heq | hgt
  · rw [if_neg (by omega)]
    have e : (65536 : ℕ) ^ p = 65536 ^ q * (65536 * 65536 ^ (p - q - 1)) := by
      rw [← pow_succ', ← pow_add, show q + (p - q - 1 + 1) = p by omega]
    rw [e, Nat.add_mul_div_left _ _ (hpos q), Nat.add_mul_mod_self_left]
  · subst heq
    rw [if_pos rfl, add_pow_div]
    generalize T / 65536 ^ q = x at h ⊢
    omega
  · rw [if_neg (by omega)]
    have e : (65536 : ℕ) ^ q = 65536 ^ p * 65536 * 65536 ^ (q - p - 1) := by
      rw [← pow_succ, ← pow_add, show p + 1 + (q - p - 1) = q by omega]
    rw [e]
    simp only [← Nat.div_div_eq_div_mul]
    rw [add_pow_div]
    have hx : (T / 65536 ^ p + 1) / 65536 = T / 65536 ^ p / 65536 := by
      generalize T / 65536 ^ p = x at h ⊢
      omega
    rw [hx]

theorem hop_fst (n j : ℕ) (s : ℕ × (ℕ → ℕ)) :
    (hop n j s).1 = if s.2 ((s.1 + (n - j % n)) % n) < s.2 ((s.1 + j) % n) then (s.1 + (n - j % n)) % n
      else (s.1 + j) % n := rfl

theorem hop_snd (n j : ℕ) (s : ℕ × (ℕ → ℕ)) :
    (hop n j s).2 = Function.update s.2 (hop n j s).1 (s.2 (hop n j s).1 + 1) := rfl

/-- Every visit count after `k` hops is at most `k + 1`. -/
theorem cnt_le (n : ℕ) : ∀ k q, (state n k).2 q ≤ k + 1
  | 0, q => by
    show (if q = 0 then 1 else 0) ≤ 0 + 1
    split_ifs <;> omega
  | k + 1, q => by
    have ih1 := cnt_le n k q
    have ih2 := cnt_le n k (hop n (k + 1) (state n k)).1
    show (hop n (k + 1) (state n k)).2 q ≤ k + 1 + 1
    rw [hop_snd, Function.update_apply]
    split_ifs <;> omega

theorem cnt_mono (n k q : ℕ) : (state n k).2 q ≤ (state n (k + 1)).2 q := by
  show (state n k).2 q ≤ (hop n (k + 1) (state n k)).2 q
  rw [hop_snd, Function.update_apply]
  split_ifs with h
  · rw [h]; exact Nat.le_succ _
  · exact le_refl _

theorem allVisited_mono (n k m : ℕ) (hkm : k ≤ m) (h : AllVisited n k) : AllVisited n m := by
  induction hkm with
  | refl => exact h
  | step _ ih => exact fun p hp => lt_of_lt_of_le (ih p hp) (cnt_mono n _ p)

/-- `(cur, T)` represents the state after `k` hops: same position, and digit `q` of `T` is the count of `q`. -/
abbrev Rep (n k cur T : ℕ) : Prop := (state n k).1 = cur ∧ ∀ q, q < n → (state n k).2 q = dig T q

theorem rep_zero (n : ℕ) : Rep n 0 0 1 := by
  refine ⟨rfl, fun q _ => ?_⟩
  show (if q = 0 then 1 else 0) = 1 / 65536 ^ q % 65536
  rcases Nat.eq_zero_or_pos q with h | h
  · subst h
    rfl
  · have h1 : 1 < (65536 : ℕ) ^ q := Nat.one_lt_pow (by omega) (by norm_num)
    rw [if_neg (by omega), Nat.div_eq_of_lt h1]

theorem rep_succ (n k cur T : ℕ) (hn : 0 < n) (hk : k + 2 < 65536) (h : Rep n k cur T) :
    Rep n (k + 1) (hopS n (k + 1) cur T) (T + 65536 ^ hopS n (k + 1) cur T) := by
  obtain ⟨h1, h2⟩ := h
  have hcw : (cur + (k + 1)) % n < n := Nat.mod_lt _ hn
  have hccw : (cur + (n - (k + 1) % n)) % n < n := Nat.mod_lt _ hn
  have hfst : (hop n (k + 1) (state n k)).1 = hopS n (k + 1) cur T := by
    rw [hop_fst, h1, h2 _ hcw, h2 _ hccw]
    rfl
  have hnx : hopS n (k + 1) cur T < n := by
    unfold hopS
    split_ifs
    · exact hccw
    · exact hcw
  have hb : dig T (hopS n (k + 1) cur T) + 1 < 65536 := by
    have := cnt_le n k (hopS n (k + 1) cur T)
    rw [h2 _ hnx] at this
    omega
  refine ⟨hfst, fun q hq => ?_⟩
  rw [dig_add _ _ _ hb]
  show (hop n (k + 1) (state n k)).2 q = _
  rw [hop_snd, hfst, Function.update_apply]
  split_ifs with hq'
  · rw [h2 _ hnx]
  · exact h2 q hq

theorem rep_loop (n : ℕ) (hn : 0 < n) :
    ∀ f k cur T, k + f + 1 < 65536 → Rep n k cur T →
      Rep n (k + f) (loop n f (k + 1) cur T).1 (loop n f (k + 1) cur T).2
  | 0, k, cur, T, _, h => h
  | f + 1, k, cur, T, hb, h => by
    rw [loop_succ]
    have h' := rep_succ n k cur T hn (by omega) h
    have ih := rep_loop n hn f (k + 1) _ _ (by omega) h'
    rw [show k + (f + 1) = k + 1 + f by omega]
    exact ih

theorem rep_loop0 (n : ℕ) (hn : 0 < n) (f : ℕ) (hf : f + 1 < 65536) :
    Rep n f (loop n f 1 0 1).1 (loop n f 1 0 1).2 := by
  have h := rep_loop n hn f 0 0 1 (by omega) (rep_zero n)
  simp only [Nat.zero_add] at h
  exact h

/-- The packed counts after `K + 1` hops. -/
def lastT (n K : ℕ) : ℕ :=
  (loop n K 1 0 1).2 + 65536 ^ hopS n (K + 1) (loop n K 1 0 1).1 (loop n K 1 0 1).2

/-- The computed facts: some position is unvisited after `K` hops, all are visited after `K + 1` hops, and then
the largest count is `M`. -/
abbrev Checks (n K M : ℕ) : Prop :=
  checkAll (fun p => decide (0 < dig (loop n K 1 0 1).2 p)) n = false ∧
  checkAll (fun p => decide (0 < dig (lastT n K) p)) n = true ∧
  checkAll (fun p => decide (dig (lastT n K) p ≤ M)) n = true ∧
  checkAll (fun p => decide (dig (lastT n K) p < M)) n = false

theorem a_of_checks (n K M : ℕ) (hn : 0 < n) (hK : K + 2 < 65536) (h : Checks n K M) :
    stopHop n = K + 1 ∧ a n = M := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have r0 := rep_loop0 n hn K (by omega)
  have r1 := rep_succ n K _ _ hn hK r0
  obtain ⟨_, r1c⟩ := r1
  obtain ⟨_, r0c⟩ := r0
  have hall : AllVisited n (K + 1) := by
    intro p hp
    rw [r1c p hp]
    exact of_decide_eq_true (checkAll_true _ _ h2 p hp)
  have hnot : ¬ AllVisited n K := by
    intro hall'
    obtain ⟨p, hp, hP⟩ := checkAll_false _ _ h1
    have hpos := hall' p hp
    rw [r0c p hp] at hpos
    exact (of_decide_eq_false hP) hpos
  have hstop : stopHop n = K + 1 := by
    unfold OMA.S_oeis_a329231.stopHop
    apply le_antisymm
    · exact Nat.sInf_le (show K + 1 ∈ {k | AllVisited n k} from hall)
    · apply le_csInf ⟨K + 1, hall⟩
      intro k hk
      by_contra hlt
      exact hnot (allVisited_mono n k K (by omega) hk)
  refine ⟨hstop, ?_⟩
  unfold OMA.S_oeis_a329231.a
  rw [hstop]
  apply le_antisymm
  · apply Finset.sup_le
    intro q hq
    have hq' : q < n := Finset.mem_range.mp hq
    rw [r1c q hq']
    exact of_decide_eq_true (checkAll_true _ _ h3 q hq')
  · obtain ⟨q, hq, hP⟩ := checkAll_false _ _ h4
    have h5 : ¬ dig (lastT n K) q < M := of_decide_eq_false hP
    have hle : dig (lastT n K) q ≤ M := of_decide_eq_true (checkAll_true _ _ h3 q hq)
    have e : (state n (K + 1)).2 q = M := by
      rw [r1c q hq]
      exact le_antisymm hle (Nat.not_lt.mp h5)
    calc M = (state n (K + 1)).2 q := e.symm
      _ ≤ _ := Finset.le_sup (Finset.mem_range.mpr hq)

set_option maxHeartbeats 0 in
/-- Kernel computation for `n = 2436`: the procedure stops at hop `7720` with largest count `5`. -/
theorem checks_2436 : Checks 2436 7719 5 := by decide +kernel

theorem a_2436 : a 2436 = 5 := (a_of_checks 2436 7719 5 (by norm_num) (by norm_num) checks_2436).2

end OMA.A329231Proof

/-- C2 fails: `a 2436 = 5` although `2436 > 1972`. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a329231.main) := by
  intro h
  obtain ⟨_, ⟨_, _, _, h5'⟩, _⟩ := h
  obtain ⟨_, h5⟩ := h5'
  exact h5 2436 (by norm_num) OMA.A329231Proof.a_2436
