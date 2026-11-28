import OMAReductions.R_AlgebraicNormality_irrational_algebraic_normal_in_some_base_R1_H1_R1

/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
/-!
# Division by a positive integer preserves normality

This is the reciprocal-integer case of D. D. Wall's normality-preservation theorem (1949).
See Doty, Lutz and Nandakumar, Finite-State Dimension and Real Arithmetic, Corollary 4.4:
https://www.cs.ucdavis.edu/~doty/papers/fsdra-icalp.pdf

The digit/equidistribution bridge in WallBridge is reused from @sobrien032's accepted
integer-multiplier proof, open-math-agents PR #3500, revision
2a50a78e24c84a2501313ab15f10a78b663cb83b. That bridge was adapted from the Apache-2.0
Lean proof in Ralf Stephan's formal-conjectures fork, revision
a522a5352dd28df0b5ef08c213c368b5f6a5df6e:
https://github.com/rwst/formal-conjectures/blob/a522a5352dd28df0b5ef08c213c368b5f6a5df6e/FormalConjectures/Books/BugeaudDistributionModuloOne/NormalAndRich.lean
The original copyright and license notice above is retained.
The parent reduction was contributed by @arjunkshah12345-hash.

New measure-convergence, finite-cover and ergodic formalization:
Hanan Beer (@hananzlt), with the coordinating Codex session and three solver sessions.
Every empirical limit is invariant under multiplication by the base. Its image under
the integer covering is Haar, so it is absolutely continuous; ergodicity identifies
it with Haar. The digit characterization then yields normality of the divided number.
-/

open NormalNumber Filter Topology

namespace WallBridge

/-- The natural number formed by the first `k` base-`b` digits of the fractional part of `y`. -/
noncomputable def digitPrefix (b k : ℕ) (y : ℝ) : ℕ :=
  ⌊(b : ℝ) ^ k * Int.fract y⌋₊

/-- The natural number with base-`b` digits `w 0, …, w (k - 1)`, most significant first. -/
def ofBlock (b : ℕ) (w : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => b * ofBlock b w k + w k

/-- The proportion of indices `m < n` such that the fractional part of `s m` lies in `S`. -/
noncomputable def visitFreq (s : ℕ → ℝ) (S : Set ℝ) [DecidablePred (· ∈ S)] (n : ℕ) : ℝ :=
  (((Finset.range n).filter fun m => Int.fract (s m) ∈ S).card : ℝ) / n

theorem digitPrefix_zero (b : ℕ) (y : ℝ) : digitPrefix b 0 y = 0 := by
  simp [digitPrefix, Int.fract_lt_one]

theorem digitPrefix_succ {b : ℕ} (hb : 0 < b) (k : ℕ) (y : ℝ) :
    digitPrefix b (k + 1) y = b * digitPrefix b k y + digitSeq b y k := by
  have hb' : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
  have h : digitPrefix b (k + 1) y / b = digitPrefix b k y := by
    rw [digitPrefix, digitPrefix, ← Nat.floor_div_natCast]
    congr 1
    field_simp
    ring
  rw [← h]
  exact (Nat.div_add_mod _ _).symm

theorem digitPrefix_lt {b : ℕ} (hb : 0 < b) (k : ℕ) (y : ℝ) : digitPrefix b k y < b ^ k := by
  have hB : (0 : ℝ) < (b : ℝ) ^ k := by positivity
  rw [digitPrefix, Nat.floor_lt (mul_nonneg hB.le (Int.fract_nonneg y))]
  push_cast
  exact mul_lt_of_lt_one_right hB (Int.fract_lt_one y)

theorem digitPrefix_eq_iff {b : ℕ} (hb : 0 < b) (k m : ℕ) (y : ℝ) :
    digitPrefix b k y = m ↔
      Int.fract y ∈ Set.Ico ((m : ℝ) / (b : ℝ) ^ k) (((m : ℝ) + 1) / (b : ℝ) ^ k) := by
  have hB : (0 : ℝ) < (b : ℝ) ^ k := by positivity
  rw [digitPrefix, Nat.floor_eq_iff (mul_nonneg hB.le (Int.fract_nonneg y)), Set.mem_Ico,
    div_le_iff₀ hB, lt_div_iff₀ hB, mul_comm (Int.fract y)]

theorem digitPrefix_add {b : ℕ} (i j : ℕ) (x : ℝ) :
    digitPrefix b (i + j) x = digitPrefix b j ((b : ℝ) ^ i * x) + b ^ j * digitPrefix b i x := by
  have hnn : 0 ≤ (b : ℝ) ^ i * Int.fract x := mul_nonneg (by positivity) (Int.fract_nonneg x)
  have hfr : Int.fract ((b : ℝ) ^ i * x) =
      (b : ℝ) ^ i * Int.fract x - (⌊(b : ℝ) ^ i * Int.fract x⌋₊ : ℝ) := by
    have h1 : (b : ℝ) ^ i * x = (b : ℝ) ^ i * Int.fract x + ((b ^ i * ⌊x⌋ : ℤ) : ℝ) := by
      push_cast
      rw [← Int.fract_add_floor x]
      ring_nf
      simp
    rw [h1, Int.fract_add_intCast, Int.fract, ← Int.natCast_floor_eq_floor hnn]
    push_cast
    ring
  rw [digitPrefix, digitPrefix, digitPrefix, hfr, add_comm, ← Nat.floor_add_natCast]
  · congr 1
    rw [pow_add]
    push_cast
    ring
  · exact mul_nonneg (by positivity) (sub_nonneg.2 (Nat.floor_le hnn))

theorem digitSeq_add {b : ℕ} (i j : ℕ) (x : ℝ) :
    digitSeq b x (i + j) = digitSeq b ((b : ℝ) ^ i * x) j := by
  have h := digitPrefix_add (b := b) i (j + 1) x
  rw [← add_assoc] at h
  change digitPrefix b (i + j + 1) x % b = digitPrefix b (j + 1) ((b : ℝ) ^ i * x) % b
  rw [h, pow_succ, mul_comm (b ^ j) b, mul_assoc, Nat.add_mul_mod_self_left]

theorem mul_add_eq_mul_add_iff {b a r a' r' : ℕ} (hb : 0 < b) (hr : r < b) (hr' : r' < b) :
    b * a + r = b * a' + r' ↔ a = a' ∧ r = r' := by
  refine ⟨fun h => ?_, fun ⟨h1, h2⟩ => h1 ▸ h2 ▸ rfl⟩
  have h1 := congrArg (· / b) h
  have h2 := congrArg (· % b) h
  simp only [Nat.mul_add_div hb, Nat.div_eq_of_lt hr, Nat.div_eq_of_lt hr', add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr'] at h1 h2
  exact ⟨h1, h2⟩

theorem forall_digitSeq_eq_iff {b : ℕ} (hb : 0 < b) {w : ℕ → ℕ} (hw : ∀ j, w j < b) (k : ℕ)
    (y : ℝ) : (∀ j < k, digitSeq b y j = w j) ↔ digitPrefix b k y = ofBlock b w k := by
  induction k with
  | zero => simp [digitPrefix_zero, ofBlock]
  | succ k ih =>
    rw [Nat.forall_lt_succ_right, ih, digitPrefix_succ hb, ofBlock,
      mul_add_eq_mul_add_iff hb (show digitSeq b y k < b from Nat.mod_lt _ hb) (hw k)]

theorem ofBlock_lt {b : ℕ} {w : ℕ → ℕ} (hw : ∀ j, w j < b) (k : ℕ) : ofBlock b w k < b ^ k := by
  induction k with
  | zero => simp [ofBlock]
  | succ k ih =>
    calc b * ofBlock b w k + w k < b * (ofBlock b w k + 1) := by linarith [hw k]
      _ ≤ b * b ^ k := Nat.mul_le_mul_left _ ih
      _ = b ^ (k + 1) := by ring

theorem ofBlock_congr {b : ℕ} {w w' : ℕ → ℕ} (k : ℕ) (h : ∀ j < k, w j = w' j) :
    ofBlock b w k = ofBlock b w' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [ofBlock, ofBlock, ih fun j hj => h j (by omega), h k (by omega)]

theorem exists_ofBlock_eq {b : ℕ} (hb : 0 < b) (k : ℕ) :
    ∀ m < b ^ k, ∃ w : ℕ → ℕ, (∀ j, w j < b) ∧ ofBlock b w k = m := by
  induction k with
  | zero =>
    intro m hm
    rw [pow_zero, Nat.lt_one_iff] at hm
    exact ⟨fun _ => 0, fun _ => hb, hm.symm⟩
  | succ k ih =>
    intro m hm
    obtain ⟨w, hw, hwm⟩ := ih (m / b) ((Nat.div_lt_iff_lt_mul hb).2 (by rwa [← pow_succ]))
    refine ⟨Function.update w k (m % b), fun j => ?_, ?_⟩
    · rcases eq_or_ne j k with rfl | hj
      · simpa using Nat.mod_lt m hb
      · simpa [hj] using hw j
    · rw [ofBlock, ofBlock_congr (w' := w) k fun j hj => Function.update_of_ne hj.ne _ _, hwm,
        Function.update_self]
      exact Nat.div_add_mod m b

theorem exists_extend {b k : ℕ} (hb : 0 < b) (wf : Fin k → ℕ) (hwf : ∀ j, wf j < b) :
    ∃ w : ℕ → ℕ, (∀ j, w j < b) ∧ ∀ j : Fin k, wf j = w j := by
  refine ⟨fun j => if hj : j < k then wf ⟨j, hj⟩ else 0, fun j => ?_, fun j => by simp [j.isLt]⟩
  dsimp only
  split_ifs
  exacts [hwf _, hb]

/-- A block of digits at position `i` corresponds to a `b`-adic interval for `b ^ i * x`. -/
theorem block_iff {b : ℕ} (hb : 0 < b) {w : ℕ → ℕ} (hw : ∀ j, w j < b) (k i : ℕ) (x : ℝ) :
    (∀ j : Fin k, digitSeq b x (i + j) = w j) ↔
      Int.fract ((b : ℝ) ^ i * x) ∈ Set.Ico ((ofBlock b w k : ℝ) / (b : ℝ) ^ k)
        (((ofBlock b w k : ℝ) + 1) / (b : ℝ) ^ k) := by
  rw [← digitPrefix_eq_iff hb, ← forall_digitSeq_eq_iff hb hw, Fin.forall_iff]
  simp only [digitSeq_add]

theorem visitFreq_mono {s : ℕ → ℝ} {S T : Set ℝ} [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ T)] (h : ∀ y ∈ Set.Ico (0 : ℝ) 1, y ∈ S → y ∈ T)
    (n : ℕ) : visitFreq s S n ≤ visitFreq s T n := by
  refine div_le_div_of_nonneg_right (Nat.cast_le.2 (Finset.card_le_card fun m hm => ?_))
    (Nat.cast_nonneg _)
  rw [Finset.mem_filter] at hm ⊢
  exact ⟨hm.1, h _ ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩ hm.2⟩

theorem visitFreq_congr {s : ℕ → ℝ} {S T : Set ℝ} [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ T)] (h : S = T) : visitFreq s S = visitFreq s T := by
  subst h
  congr

theorem visitFreq_union {s : ℕ → ℝ} {S T : Set ℝ} [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ T)] (h : Disjoint S T) (n : ℕ) :
    visitFreq s (S ∪ T) n = visitFreq s S n + visitFreq s T n := by
  rw [visitFreq, visitFreq, visitFreq, ← add_div, ← Nat.cast_add, ← Finset.card_union_of_disjoint]
  · simp only [Set.mem_union, Finset.filter_or]
  · exact Finset.disjoint_filter.2 fun _ _ h1 h2 => Set.disjoint_left.1 h h1 h2

/-- Frequencies of unions of consecutive `b`-adic intervals. -/
theorem tendsto_visitFreq_Ico {b : ℕ} {s : ℕ → ℝ}
    (hA : ∀ k, ∀ m < b ^ k, Tendsto (visitFreq s (Set.Ico ((m : ℝ) / (b : ℝ) ^ k)
      (((m : ℝ) + 1) / (b : ℝ) ^ k))) atTop (𝓝 (1 / (b : ℝ) ^ k)))
    (k : ℕ) {m₁ m₂ : ℕ} (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ b ^ k) :
    Tendsto (visitFreq s (Set.Ico ((m₁ : ℝ) / (b : ℝ) ^ k) ((m₂ : ℝ) / (b : ℝ) ^ k))) atTop
      (𝓝 (((m₂ : ℝ) - m₁) / (b : ℝ) ^ k)) := by
  induction m₂, h₁₂ using Nat.le_induction with
  | base =>
    rw [sub_self, zero_div]
    refine tendsto_const_nhds.congr fun n => ?_
    simp [visitFreq]
  | succ m₂ h ih =>
    have hdiv : (m₁ : ℝ) / (b : ℝ) ^ k ≤ (m₂ : ℝ) / (b : ℝ) ^ k :=
      div_le_div_of_nonneg_right (Nat.cast_le.2 h) (by positivity)
    have hdiv' : (m₂ : ℝ) / (b : ℝ) ^ k ≤ ((m₂ : ℝ) + 1) / (b : ℝ) ^ k :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have hset : Set.Ico ((m₁ : ℝ) / (b : ℝ) ^ k) (((m₂ + 1 : ℕ) : ℝ) / (b : ℝ) ^ k) =
        Set.Ico ((m₁ : ℝ) / (b : ℝ) ^ k) ((m₂ : ℝ) / (b : ℝ) ^ k) ∪
          Set.Ico ((m₂ : ℝ) / (b : ℝ) ^ k) (((m₂ : ℝ) + 1) / (b : ℝ) ^ k) := by
      rw [Set.Ico_union_Ico_eq_Ico hdiv hdiv']
      push_cast
      rfl
    have hsum := ((ih (by omega)).add (hA k m₂ (by omega))).congr
      (f₂ := visitFreq s (Set.Ico ((m₁ : ℝ) / (b : ℝ) ^ k) (((m₂ + 1 : ℕ) : ℝ) / (b : ℝ) ^ k)))
      fun n => by rw [visitFreq_congr hset, visitFreq_union Set.Ico_disjoint_Ico_same]
    convert hsum using 2
    push_cast
    ring

/-- `x` is normal in base `b` iff every `b`-adic interval has the expected frequency. -/
theorem isNormalInBase_iff_tendsto {b : ℕ} (hb : 0 < b) (x : ℝ) :
    IsNormalInBase b x ↔ ∀ k, ∀ m < b ^ k,
      Tendsto (visitFreq (fun n => (b : ℝ) ^ n * x) (Set.Ico ((m : ℝ) / (b : ℝ) ^ k)
        (((m : ℝ) + 1) / (b : ℝ) ^ k))) atTop (𝓝 (1 / (b : ℝ) ^ k)) := by
  constructor
  · intro h k m hm
    obtain ⟨w, hw, rfl⟩ := exists_ofBlock_eq hb k m hm
    refine (h k (fun j => w j) fun j => hw j).congr fun n => ?_
    simp only [visitFreq]
    congr 3
    exact Finset.filter_congr fun i _ => block_iff hb hw k i x
  · intro h k wf hwf
    obtain ⟨w, hw, hwf'⟩ := exists_extend hb wf hwf
    refine (h k _ (ofBlock_lt hw k)).congr fun n => ?_
    simp only [visitFreq, hwf']
    congr 3
    exact (Finset.filter_congr fun i _ => block_iff hb hw k i x).symm


theorem exists_one_div_pow_lt {b : ℕ} (hb : 2 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, 1 / (b : ℝ) ^ k < ε := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε
    ((div_lt_one (by positivity)).2 (by exact_mod_cast (by omega : 1 < b)) : (1 : ℝ) / b < 1)
  exact ⟨k, by rwa [div_pow, one_pow] at hk⟩

theorem add_one_div_pow_le_one {b k m : ℕ} (hm : m < b ^ k) :
    ((m : ℝ) + 1) / (b : ℝ) ^ k ≤ 1 :=
  div_le_one_of_le₀ (by exact_mod_cast Nat.succ_le_of_lt hm) (by positivity)


/-- Frequencies of `b`-adic intervals determine uniform distribution modulo one. -/
theorem tendsto_Ico_iff_isEquidistributedModuloOne {b : ℕ} (hb : 2 ≤ b) (s : ℕ → ℝ) :
    (∀ k, ∀ m < b ^ k, Tendsto (visitFreq s (Set.Ico ((m : ℝ) / (b : ℝ) ^ k)
      (((m : ℝ) + 1) / (b : ℝ) ^ k))) atTop (𝓝 (1 / (b : ℝ) ^ k))) ↔
    IsEquidistributedModuloOne s := by
  constructor
  · intro hA c d hcd hsub
    have hc0 : 0 ≤ c := (hsub ⟨le_rfl, hcd⟩).1
    have hd1 : d ≤ 1 := (hsub ⟨hcd, le_rfl⟩).2
    have hd0 : 0 ≤ d := hc0.trans hcd
    change Tendsto (visitFreq s (Set.Icc c d)) atTop (𝓝 ((d - c) / (1 - 0)))
    rw [sub_zero, div_one, tendsto_order]
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · obtain ⟨k, hk⟩ := exists_one_div_pow_lt hb (show 0 < (d - c - a) / 2 by linarith)
      have hB : (0 : ℝ) < (b : ℝ) ^ k := by positivity
      set B := (b : ℝ) ^ k with hBdef
      set m₂ := ⌊d * B⌋₊ with hm₂def
      set m₁ := min ⌈c * B⌉₊ m₂ with hm₁def
      have hm₂ : m₂ ≤ b ^ k := Nat.floor_le_of_le (by
        push_cast
        exact mul_le_of_le_one_left hB.le hd1)
      have hlim := tendsto_visitFreq_Ico hA k (min_le_right ⌈c * B⌉₊ m₂) hm₂
      have h1 : (m₁ : ℝ) < c * B + 1 :=
        (Nat.cast_le.2 (min_le_left _ _)).trans_lt (Nat.ceil_lt_add_one (mul_nonneg hc0 hB.le))
      have h2 : d * B - 1 < m₂ := Nat.sub_one_lt_floor _
      have h3 : 2 < d * B - c * B - a * B := by
        have := (div_lt_iff₀ hB).1 hk
        linarith
      have hgt : a < ((m₂ : ℝ) - m₁) / B := by
        rw [lt_div_iff₀ hB]
        linarith
      refine (hlim.eventually (lt_mem_nhds hgt)).mono fun n hn => hn.trans_le (visitFreq_mono ?_ n)
      rintro y - ⟨hy1, hy2⟩
      have hlt : m₁ < m₂ := by exact_mod_cast (div_lt_div_iff_of_pos_right hB).1 (hy1.trans_lt hy2)
      have hm₁ : m₁ = ⌈c * B⌉₊ := by
        rw [hm₁def]
        refine min_eq_left ?_
        by_contra hne
        rw [not_le] at hne
        rw [hm₁def, min_eq_right hne.le] at hlt
        exact lt_irrefl _ hlt
      constructor
      · calc c ≤ (m₁ : ℝ) / B := by
              rw [le_div_iff₀ hB, hm₁]
              exact Nat.le_ceil _
          _ ≤ y := hy1
      · calc y ≤ (m₂ : ℝ) / B := hy2.le
          _ ≤ d := by
              rw [div_le_iff₀ hB]
              exact Nat.floor_le (mul_nonneg hd0 hB.le)
    · obtain ⟨k, hk⟩ := exists_one_div_pow_lt hb (show 0 < (a - (d - c)) / 2 by linarith)
      have hB : (0 : ℝ) < (b : ℝ) ^ k := by positivity
      set B := (b : ℝ) ^ k with hBdef
      have hBnat : ((b ^ k : ℕ) : ℝ) = B := by push_cast; rfl
      set m₁ := ⌊c * B⌋₊ with hm₁def
      set m₂ := min (⌊d * B⌋₊ + 1) (b ^ k) with hm₂def
      have hm₁ : m₁ ≤ b ^ k := Nat.floor_le_of_le (by
        rw [hBnat]
        exact mul_le_of_le_one_left hB.le (hcd.trans hd1))
      have hm₁₂ : m₁ ≤ m₂ := le_min
        ((Nat.floor_le_floor (mul_le_mul_of_nonneg_right hcd hB.le)).trans (Nat.le_succ _)) hm₁
      have hlim := tendsto_visitFreq_Ico hA k hm₁₂ (min_le_right _ _)
      have h1 : c * B - 1 < m₁ := Nat.sub_one_lt_floor _
      have h2 : (m₂ : ℝ) ≤ d * B + 1 := by
        have : (m₂ : ℝ) ≤ ((⌊d * B⌋₊ + 1 : ℕ) : ℝ) := Nat.cast_le.2 (min_le_left _ _)
        push_cast at this
        linarith [Nat.floor_le (mul_nonneg hd0 hB.le)]
      have h3 : 2 < a * B - d * B + c * B := by
        have := (div_lt_iff₀ hB).1 hk
        linarith
      have hlt : ((m₂ : ℝ) - m₁) / B < a := by
        rw [div_lt_iff₀ hB]
        linarith
      refine (hlim.eventually (gt_mem_nhds hlt)).mono fun n hn => (visitFreq_mono ?_ n).trans_lt hn
      rintro y ⟨-, hy1⟩ ⟨hcy, hyd⟩
      constructor
      · calc (m₁ : ℝ) / B ≤ c := by
              rw [div_le_iff₀ hB]
              exact Nat.floor_le (mul_nonneg hc0 hB.le)
          _ ≤ y := hcy
      · rw [lt_div_iff₀ hB, hm₂def, Nat.cast_min, lt_min_iff]
        constructor
        · push_cast
          linarith [mul_le_mul_of_nonneg_right hyd hB.le, Nat.lt_floor_add_one (d * B)]
        · rw [hBnat]
          exact mul_lt_of_lt_one_left hB hy1
  · intro hud k m hm
    have hB : (0 : ℝ) < (b : ℝ) ^ k := by positivity
    have hc0 : 0 ≤ (m : ℝ) / (b : ℝ) ^ k := by positivity
    have hcd : (m : ℝ) / (b : ℝ) ^ k ≤ ((m : ℝ) + 1) / (b : ℝ) ^ k :=
      div_le_div_of_nonneg_right (by linarith) hB.le
    have hd1 := add_one_div_pow_le_one hm
    have h1 : Tendsto (visitFreq s (Set.Icc _ _)) atTop _ :=
      hud _ _ hcd (Set.Icc_subset_Icc hc0 hd1)
    have h2 : Tendsto (visitFreq s (Set.Icc _ _)) atTop _ :=
      hud _ _ le_rfl (Set.Icc_subset_Icc (hc0.trans hcd) hd1)
    have hsplit (n : ℕ) : visitFreq s (Set.Ico ((m : ℝ) / (b : ℝ) ^ k)
        (((m : ℝ) + 1) / (b : ℝ) ^ k)) n =
        visitFreq s (Set.Icc ((m : ℝ) / (b : ℝ) ^ k) (((m : ℝ) + 1) / (b : ℝ) ^ k)) n -
          visitFreq s (Set.Icc (((m : ℝ) + 1) / (b : ℝ) ^ k) (((m : ℝ) + 1) / (b : ℝ) ^ k)) n := by
      rw [eq_sub_iff_add_eq, ← visitFreq_union (Set.disjoint_left.2 fun y hy hy' =>
        lt_irrefl y (hy.2.trans_le hy'.1))]
      exact congrFun (visitFreq_congr (Set.Ico_union_Icc_eq_Icc hcd le_rfl)) n
    convert (h1.sub h2).congr fun n => (hsplit n).symm using 2
    ring

/-- A real number $\xi$ is normal in base $b$ if and only if $(b^n \xi)_{n \ge 0}$ is uniformly
distributed modulo $1$ [Wal49], [Bug12, Theorem 4.14]. -/
theorem isNormalInBase_iff_isEquidistributedModuloOne (b : ℕ) (hb : 2 ≤ b) (ξ : ℝ) :
    IsNormalInBase b ξ ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * ξ :=
  (isNormalInBase_iff_tendsto (by omega) ξ).trans (tendsto_Ico_iff_isEquidistributedModuloOne hb _)


end WallBridge


open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction
open scoped ENNReal

namespace WallEmpirical

noncomputable def haar : ProbabilityMeasure (AddCircle (1 : ℝ)) :=
  ⟨volume, ⟨by simp [AddCircle.measure_univ]⟩⟩

variable {X : Type*} [MeasurableSpace X]

noncomputable def empirical (s : ℕ → X) (n : ℕ) : ProbabilityMeasure X :=
  ⟨(n + 1 : ℝ≥0∞)⁻¹ • ∑ i ∈ Finset.range (n + 1), Measure.dirac (s i), by
    constructor
    simp [Measure.smul_apply, ENNReal.inv_mul_cancel]⟩

open scoped Classical in
theorem empirical_apply (s : ℕ → X) (n : ℕ) {A : Set X} (hA : MeasurableSet A) :
    (empirical s n : Measure X) A =
      (n + 1 : ℝ≥0∞)⁻¹ * (((Finset.range (n + 1)).filter (s · ∈ A)).card : ℝ≥0∞) := by
  classical
  simp only [empirical, ProbabilityMeasure.coe_mk, Measure.smul_apply, smul_eq_mul]
  rw [Measure.finsetSum_apply]
  congr 1
  simp [Measure.dirac_apply' _ hA, Set.indicator_apply, Finset.sum_boole]

variable [TopologicalSpace X] [BorelSpace X] [T2Space X]

theorem integral_empirical (s : ℕ → X) (n : ℕ) (f : X →ᵇ ℝ) :
    ∫ x, f x ∂(empirical s n : Measure X) =
      (n + 1 : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1), f (s i) := by
  simp only [empirical, ProbabilityMeasure.coe_mk]
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [ENNReal.toReal_add]
  · intro i hi
    exact integrable_dirac (by simp)

variable {Y : Type*} [MeasurableSpace Y]

omit [TopologicalSpace X] [BorelSpace X] [T2Space X] in
theorem empirical_map (s : ℕ → X) (n : ℕ) {g : X → Y} (hg : Measurable g) :
    (empirical s n).map hg.aemeasurable = empirical (g ∘ s) n := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map g (empirical s n : Measure X) = (empirical (g ∘ s) n : Measure Y)
  ext A hA
  rw [Measure.map_apply hg hA,
    empirical_apply s n (hg hA), empirical_apply (g ∘ s) n hA]
  rfl

theorem empirical_integral_shift (s : ℕ → X) (f : X →ᵇ ℝ) (n : ℕ) :
    (∫ x, f x ∂(empirical (fun i => s (i + 1)) n : Measure X)) -
      (∫ x, f x ∂(empirical s n : Measure X)) =
      (n + 1 : ℝ)⁻¹ * (f (s (n + 1)) - f (s 0)) := by
  rw [integral_empirical, integral_empirical, ← mul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_range_sub (fun i => f (s i)) (n + 1)

theorem tendsto_empirical_integral_shift (s : ℕ → X) (f : X →ᵇ ℝ) :
    Tendsto (fun n => (∫ x, f x ∂(empirical (fun i => s (i + 1)) n : Measure X)) -
      (∫ x, f x ∂(empirical s n : Measure X))) atTop (𝓝 0) := by
  simp_rw [empirical_integral_shift]
  refine squeeze_zero_norm (a := fun n : ℕ => (n + 1 : ℝ)⁻¹ * (‖f‖ + ‖f‖)) ?_ ?_
  · intro n
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left
      ((norm_sub_le _ _).trans (add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)))
      (by positivity)
  · have hi : Tendsto (fun n : ℕ => (n + 1 : ℝ)⁻¹) atTop (𝓝 0) :=
      (tendsto_atTop_add_const_right atTop 1
        (tendsto_natCast_atTop_atTop (R := ℝ))).inv_tendsto_atTop
    simpa using hi.mul_const (‖f‖ + ‖f‖)

variable [HasOuterApproxClosed X]

theorem empirical_limit_invariant {s : ℕ → X} {T : X → X} (hT : Continuous T)
    (hs : ∀ n, s (n + 1) = T (s n)) {l : Filter ℕ} [l.NeBot] (hl : l ≤ atTop)
    {ν : ProbabilityMeasure X} (hν : Tendsto (empirical s) l (𝓝 ν)) :
    MeasurePreserving T (ν : Measure X) (ν : Measure X) := by
  refine ⟨hT.measurable, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let g : X →ᵇ ℝ := f.compContinuous ⟨T, hT⟩
  have h₁ := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν) g
  have h₂ := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν) f
  have h₀ := (tendsto_empirical_integral_shift s f).mono_left hl
  have heq (n : ℕ) :
      (∫ x, f x ∂(empirical (fun i => s (i + 1)) n : Measure X)) =
      (∫ x, g x ∂(empirical s n : Measure X)) := by
    simp only [integral_empirical]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp [g, hs]
  simp_rw [heq] at h₀
  have hlim := tendsto_nhds_unique (h₁.sub h₂) h₀
  rw [integral_map hT.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  exact sub_eq_zero.mp hlim

end WallEmpirical

/- Absolute continuity for lifts under a finite covering of the circle. -/

open Set MeasureTheory MeasureTheory.Measure

namespace WallCover

private theorem nsmul_preserving (m : ℕ) (hm : m ≠ 0) :
    MeasurePreserving (fun x : AddCircle (1 : ℝ) => m • x) volume volume := by
  simpa only [natCast_zsmul] using
    (measurePreserving_zsmul (volume : Measure (AddCircle (1 : ℝ)))
      (show (m : ℤ) ≠ 0 by exact_mod_cast hm))

private theorem compact_null_image (m : ℕ) (hm : m ≠ 0)
    (K : Set (AddCircle (1 : ℝ))) (hK : IsCompact K) (hK0 : volume K = 0) :
    volume ((fun x : AddCircle (1 : ℝ) => m • x) '' K) = 0 := by
  let f : AddCircle (1 : ℝ) → AddCircle (1 : ℝ) := fun x => m • x
  have hf : Continuous f := continuous_id.nsmul m
  have hT : {t : AddCircle (1 : ℝ) | m • t = 0}.Finite :=
    AddCircle.finite_torsion 1 (Nat.pos_of_ne_zero hm)
  have hnull : volume (⋃ t ∈ {t : AddCircle (1 : ℝ) | m • t = 0},
      (fun y => t + y) '' K) = 0 := by
    apply (measure_biUnion_null_iff hT.countable).2
    intro t _
    have heq : (fun y => t + y) '' K = (fun y => -t + y) ⁻¹' K := by
      ext y
      simp only [mem_image, mem_preimage]
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa using hz
      · intro hy
        exact ⟨-t + y, hy, by simp⟩
    rw [heq, measure_preimage_add, hK0]
  have hsub : f ⁻¹' (f '' K) ⊆
      ⋃ t ∈ {t : AddCircle (1 : ℝ) | m • t = 0}, (fun y => t + y) '' K := by
    rintro x ⟨y, hy, hxy⟩
    refine mem_iUnion.2 ⟨x - y, mem_iUnion.2 ⟨?_, ?_⟩⟩
    · change m • (x - y) = 0
      change m • y = m • x at hxy
      rw [nsmul_sub, hxy, sub_self]
    · exact ⟨y, hy, sub_add_cancel x y⟩
  have hpre : volume (f ⁻¹' (f '' K)) = 0 := measure_mono_null hsub hnull
  rw [(nsmul_preserving m hm).measure_preimage
    (hK.image hf).measurableSet.nullMeasurableSet] at hpre
  exact hpre

/-- A measure whose image under a nonzero integer dilation is Haar is absolutely continuous. -/
theorem absolutelyContinuous_of_map_nsmul_eq_volume
    (m : ℕ) (hm : m ≠ 0) (ν : Measure (AddCircle (1 : ℝ)))
    (hmap : ν.map (fun x => m • x) = volume) : ν ≪ volume := by
  have hf : Continuous (fun x : AddCircle (1 : ℝ) => m • x) := continuous_id.nsmul m
  have huniv : ν univ = (volume : Measure (AddCircle (1 : ℝ))) univ := by
    rw [← hmap, map_apply hf.measurable MeasurableSet.univ, preimage_univ]
  let : IsFiniteMeasure ν := ⟨by rw [huniv]; exact measure_lt_top _ _⟩
  apply AbsolutelyContinuous.mk
  intro s hs hs0
  rw [hs.measure_eq_iSup_isCompact ν]
  apply ENNReal.iSup_eq_zero.2
  intro K
  apply ENNReal.iSup_eq_zero.2
  intro hKs
  apply ENNReal.iSup_eq_zero.2
  intro hK
  have himage := compact_null_image m hm K hK (measure_mono_null hKs hs0)
  have hpre : ν ((fun x : AddCircle (1 : ℝ) => m • x) ⁻¹'
      ((fun x : AddCircle (1 : ℝ) => m • x) '' K)) = 0 := by
    rw [← map_apply hf.measurable (hK.image hf).measurableSet, hmap, himage]
  exact measure_mono_null (subset_preimage_image _ _) hpre

end WallCover


open MeasureTheory Filter Topology

namespace WallEmpirical

/-- The orbit of a lift under a finite integer covering is equidistributed if its image is. -/
theorem tendsto_empirical_of_nsmul {s : ℕ → AddCircle (1 : ℝ)} {b m : ℕ}
    (hb : 2 ≤ b) (hm : m ≠ 0) (hs : ∀ n, s (n + 1) = b • s n)
    (himage : Tendsto (empirical (fun n => m • s n)) atTop (𝓝 haar)) :
    Tendsto (empirical s) atTop (𝓝 haar) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro ν hν
  obtain ⟨U, hU, hlim⟩ := mapClusterPt_iff_ultrafilter.mp hν
  have hinv := empirical_limit_invariant (continuous_id.nsmul b) hs hU hlim
  have hcont : Continuous (fun z : AddCircle (1 : ℝ) => m • z) := continuous_id.nsmul m
  have hmaplim := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (empirical s) ν hlim hcont
  have hmaplim' : Tendsto (empirical (fun n => m • s n)) (U : Filter ℕ)
      (𝓝 (ν.map hcont.measurable.aemeasurable)) := by
    exact hmaplim.congr fun n => empirical_map s n hcont.measurable
  have hmap : ν.map hcont.measurable.aemeasurable = haar :=
    tendsto_nhds_unique hmaplim' (himage.mono_left hU)
  have hmapMeasure : Measure.map (fun z => m • z) (ν : Measure (AddCircle (1 : ℝ))) = volume := by
    exact congrArg ProbabilityMeasure.toMeasure hmap
  have habs := WallCover.absolutelyContinuous_of_map_nsmul_eq_volume m hm
    (ν : Measure (AddCircle (1 : ℝ))) hmapMeasure
  let : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := haar.property
  apply ProbabilityMeasure.toMeasure_injective
  exact (AddCircle.ergodic_nsmul (by omega : 1 < b)).eq_of_absolutelyContinuous hinv habs

end WallEmpirical


namespace WallInverse

theorem equidistributed_of_natScale
    (hbridge : ∀ s : ℕ → ℝ, IsEquidistributedModuloOne s ↔
      Tendsto (WallEmpirical.empirical (fun n => (s n : AddCircle (1 : ℝ)))) atTop
        (𝓝 WallEmpirical.haar))
    (b m : ℕ) (hb : 2 ≤ b) (hm : m ≠ 0) (x : ℝ)
    (hx : IsEquidistributedModuloOne (fun n => (b : ℝ)^n * ((m : ℝ) * x))) :
    IsEquidistributedModuloOne (fun n => (b : ℝ)^n * x) := by
  apply (hbridge _).mpr
  apply WallEmpirical.tendsto_empirical_of_nsmul hb hm
  · intro n
    rw [← AddCircle.coe_nsmul]
    congr 1
    simp only [nsmul_eq_mul, pow_succ]
    ring
  · have heq : (fun n => m • (((b : ℝ)^n * x : ℝ) : AddCircle (1 : ℝ))) =
        (fun n => (((b : ℝ)^n * ((m : ℝ) * x) : ℝ) : AddCircle (1 : ℝ))) := by
      funext n
      rw [← AddCircle.coe_nsmul]
      congr 1
      simp only [nsmul_eq_mul]
      ring
    rw [heq]
    exact (hbridge _).mp hx

end WallInverse


open MeasureTheory Filter Set Topology

namespace WallBridgeMeasure

open scoped Classical in
theorem freq_Icc {s : ℕ → ℝ} (hs : IsEquidistributedModuloOne s) (a b : ℝ) :
    Tendsto (fun n : ℕ =>
      (((Finset.range n).filter (fun i => Int.fract (s i) ∈ Icc a b)).card : ℝ) / n)
      atTop (𝓝 ((volume.restrict (Icc (0 : ℝ) 1)).real (Icc a b))) := by
  classical
  have hc (i : ℕ) : Int.fract (s i) ∈ Icc a b ↔
      Int.fract (s i) ∈ Icc (max a 0) (min b 1) := by
    simp only [mem_Icc, max_le_iff, le_min_iff]
    have := Int.fract_nonneg (s i)
    have := (Int.fract_lt_one (s i)).le
    tauto
  simp_rw [hc]
  have hv : (volume.restrict (Icc (0 : ℝ) 1)).real (Icc a b) =
      max (min b 1 - max a 0) 0 := by
    simp [Measure.real, Measure.restrict_apply measurableSet_Icc, Icc_inter_Icc,
      Real.volume_Icc, ENNReal.toReal_ofReal']
  rw [hv]
  by_cases hab : max a 0 ≤ min b 1
  · rw [max_eq_left (sub_nonneg.mpr hab)]
    simpa using hs (max a 0) (min b 1) hab
      (Icc_subset_Icc (le_max_right _ _) (min_le_right _ _))
  · have he : Icc (max a 0) (min b 1) = ∅ := Icc_eq_empty_of_lt (lt_of_not_ge hab)
    simp [he, max_eq_right (sub_nonpos.mpr (le_of_not_ge hab))]

open scoped Classical in
theorem empirical_real (s : ℕ → ℝ) (n : ℕ) (a b : ℝ) :
    (WallEmpirical.empirical s n : Measure ℝ).real (Icc a b) =
      (((Finset.range (n + 1)).filter (fun i => s i ∈ Icc a b)).card : ℝ) / (n + 1) := by
  rw [Measure.real, WallEmpirical.empirical_apply _ _ measurableSet_Icc]
  simp [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_add,
    div_eq_mul_inv, mul_comm]

theorem equidist_real_tendsto (U : ProbabilityMeasure ℝ)
    (hU : (U : Measure ℝ) = volume.restrict (Icc (0 : ℝ) 1))
    (s : ℕ → ℝ) (hs : IsEquidistributedModuloOne s) :
    Tendsto (fun n => WallEmpirical.empirical (Int.fract ∘ s) n) atTop (𝓝 U) := by
  classical
  apply (isPiSystem_Icc (id : ℝ → ℝ) id).tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro A ⟨a, b, hab, rfl⟩
    exact measurableSet_Icc
  · intro A hA x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hA x hx
    refine ⟨Icc (x - ε/2) (x + ε/2), ⟨x - ε/2, x + ε/2, by dsimp; linarith, rfl⟩,
      Icc_mem_nhds (by linarith) (by linarith), ?_⟩
    intro y hy
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  · rintro A ⟨a, b, hab, rfl⟩
    apply NNReal.tendsto_coe.mp
    have h := (freq_Icc hs a b).comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, ← ProbabilityMeasure.measureReal_eq_coe_coeFn,
      empirical_real, hU, Nat.cast_add, Nat.cast_one, id_eq] using h

end WallBridgeMeasure

namespace WallBridgeMeasure

noncomputable def uniform01 : ProbabilityMeasure ℝ :=
  ⟨volume.restrict (Set.Icc 0 1), by constructor; simp⟩

def real_to_circle (x : ℝ) : AddCircle (1 : ℝ) := x

lemma continuous_real_to_circle : Continuous real_to_circle :=
  AddCircle.continuous_mk' 1

lemma uniform01_map_real_to_circle :
    uniform01.map continuous_real_to_circle.measurable.aemeasurable = WallEmpirical.haar := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map real_to_circle (volume.restrict (Set.Icc 0 1)) = volume
  rw [← restrict_Ioc_eq_restrict_Icc]
  change Measure.map ((↑) : ℝ → AddCircle (1 : ℝ)) (volume.restrict (Set.Ioc 0 1)) = volume
  convert (AddCircle.measurePreserving_mk (1 : ℝ) 0).map_eq using 1
  norm_num

lemma empirical_fract_map_real_to_circle (s : ℕ → ℝ) (n : ℕ) :
    (WallEmpirical.empirical (Int.fract ∘ s) n).map
      continuous_real_to_circle.measurable.aemeasurable =
      WallEmpirical.empirical (real_to_circle ∘ s) n := by
  rw [WallEmpirical.empirical_map _ _ continuous_real_to_circle.measurable]
  congr 1
  funext i
  exact AddCircle.coe_fract (s i)

lemma tendsto_circle_empirical_of_fract {s : ℕ → ℝ}
    (hs : Tendsto (WallEmpirical.empirical (Int.fract ∘ s)) atTop (𝓝 uniform01)) :
    Tendsto (WallEmpirical.empirical (real_to_circle ∘ s)) atTop (𝓝 WallEmpirical.haar) := by
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hs
    continuous_real_to_circle
  simpa only [empirical_fract_map_real_to_circle, uniform01_map_real_to_circle] using h

end WallBridgeMeasure

open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace WallConverse
abbrev C := AddCircle (1 : ℝ)
noncomputable def repr (x : C) : ℝ := AddCircle.equivIco 1 0 x

theorem repr_coe (x : ℝ) : repr (x : C) = Int.fract x := by
  simp [repr, AddCircle.coe_equivIco_mk_apply]

theorem measurable_repr : Measurable repr :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable

theorem continuousAt_repr {x : C} (hx : x ≠ 0) : ContinuousAt repr x :=
  continuous_subtype_val.continuousAt.comp
    (AddCircle.continuousAt_equivIco 1 0 (by simpa using hx))

theorem coe_repr (x : C) : (repr x : C) = x :=
  AddCircle.coe_equivIco

theorem volume_singleton (x : C) : volume ({x} : Set C) = 0 := by
  simpa using AddCircle.volume_closedBall (T := (1 : ℝ)) (x := x) 0

theorem frontier_repr_preimage_subset (c d : ℝ) :
    frontier (repr ⁻¹' Icc c d) ⊆ {0, (c : C), (d : C)} := by
  intro x hx
  by_contra hn
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hn
  have hc : repr x ≠ c := by
    intro h
    exact hn.2.1 ((coe_repr x).symm.trans (congrArg (fun t : ℝ => (t : C)) h))
  have hd : repr x ≠ d := by
    intro h
    exact hn.2.2 ((coe_repr x).symm.trans (congrArg (fun t : ℝ => (t : C)) h))
  have hcont := continuousAt_repr hn.1
  by_cases hmem : repr x ∈ Icc c d
  · have hi : Icc c d ∈ 𝓝 (repr x) :=
      Icc_mem_nhds (lt_of_le_of_ne hmem.1 hc.symm) (lt_of_le_of_ne hmem.2 hd)
    exact hx.2 (mem_interior_iff_mem_nhds.mpr (hcont.preimage_mem_nhds hi))
  · have hi : (Icc c d)ᶜ ∈ 𝓝 (repr x) := isClosed_Icc.isOpen_compl.mem_nhds hmem
    have he := mem_closure_iff_nhds.mp hx.1 _ (hcont.preimage_mem_nhds hi)
    simp only [preimage_compl, compl_inter_self, Set.not_nonempty_empty] at he

theorem null_frontier_repr_preimage (c d : ℝ) :
    volume (frontier (repr ⁻¹' Icc c d)) = 0 := by
  apply measure_mono_null (frontier_repr_preimage_subset c d)
  rw [show ({0, (c : C), (d : C)} : Set C) = {0} ∪ {(c : C)} ∪ {(d : C)} by ext; simp [or_assoc, or_comm]]
  exact measure_union_null (measure_union_null (volume_singleton 0) (volume_singleton c))
    (volume_singleton d)

theorem volume_repr_Icc {c d : ℝ} (_hcd : c ≤ d) (hsub : Icc c d ⊆ Icc 0 1) :
    volume (repr ⁻¹' Icc c d) = ENNReal.ofReal (d - c) := by
  have hmk : MeasurePreserving ((↑) : ℝ → C) (volume.restrict (Ico 0 1)) volume := by
    rw [restrict_Ico_eq_restrict_Ioc]
    simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0
  rw [← hmk.measure_preimage (measurable_repr measurableSet_Icc).nullMeasurableSet,
    Measure.restrict_apply (hmk.measurable (measurable_repr measurableSet_Icc))]
  have heq : ((↑) : ℝ → C) ⁻¹' (repr ⁻¹' Icc c d) ∩ Ico 0 1 = Icc c d ∩ Ico 0 1 := by
    ext x
    constructor
    · rintro ⟨hx, hx01⟩
      refine ⟨?_, hx01⟩
      have hr : repr (x : C) = x := by
        simpa [repr] using congrArg Subtype.val
          (AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := 0) (by simpa using hx01))
      simpa only [mem_preimage, hr] using hx
    · rintro ⟨hx, hx01⟩
      refine ⟨?_, hx01⟩
      have hr : repr (x : C) = x := by
        simpa [repr] using congrArg Subtype.val
          (AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := 0) (by simpa using hx01))
      simpa only [mem_preimage, hr] using hx
  rw [heq]
  calc
    volume (Icc c d ∩ Ico 0 1) = volume (Icc c d ∩ Icc 0 1) :=
      measure_congr (Filter.EventuallyEq.inter (Filter.EventuallyEq.refl _ _) Ico_ae_eq_Icc)
    _ = volume (Icc c d) := by rw [inter_eq_left.mpr hsub]
    _ = ENNReal.ofReal (d - c) := Real.volume_Icc


theorem empirical_to_equidist
    (s : ℕ → ℝ)
    (h : Tendsto (WallEmpirical.empirical (fun n => (s n : C)))
      atTop (𝓝 WallEmpirical.haar)) : IsEquidistributedModuloOne s := by
  classical
  intro c d hcd hsub
  have hlim := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    h (null_frontier_repr_preimage c d)
  have hfinite : (WallEmpirical.haar : Measure C) (repr ⁻¹' Icc c d) ≠ ∞ :=
    measure_ne_top _ _
  have hreal := (ENNReal.tendsto_toReal hfinite).comp hlim
  have he (n : ℕ) :
      ((WallEmpirical.empirical (fun n => (s n : C)) n : Measure C)
        (repr ⁻¹' Icc c d)).toReal =
      (((Finset.range (n + 1)).filter
        (fun i => Int.fract (s i) ∈ Icc c d)).card : ℝ) / (n + 1) := by
    rw [WallEmpirical.empirical_apply _ _ (measurable_repr measurableSet_Icc)]
    simp [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_add,
      div_eq_mul_inv, mul_comm, repr_coe]
  have hv : ((WallEmpirical.haar : Measure C) (repr ⁻¹' Icc c d)).toReal = d - c := by
    change (volume (repr ⁻¹' Icc c d)).toReal = d - c
    rw [volume_repr_Icc hcd hsub, ENNReal.toReal_ofReal (sub_nonneg.mpr hcd)]
  simp only [Function.comp_def, he, hv] at hreal
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [Nat.cast_add, Nat.cast_one, sub_zero, div_one] using hreal

end WallConverse


namespace WallBridgeMeasure

theorem equidist_iff_empirical (s : ℕ → ℝ) :
    IsEquidistributedModuloOne s ↔
      Tendsto (WallEmpirical.empirical (fun n => (s n : AddCircle (1 : ℝ)))) atTop
        (𝓝 WallEmpirical.haar) := by
  constructor
  · intro hs
    exact tendsto_circle_empirical_of_fract (equidist_real_tendsto uniform01 rfl s hs)
  · exact WallConverse.empirical_to_equidist s

end WallBridgeMeasure

namespace WallInverse

theorem normal_div_nat {b : ℕ} (hb : 2 ≤ b) {x : ℝ} (hx : IsNormalInBase b x)
    {m : ℕ} (hm : m ≠ 0) : IsNormalInBase b ((m : ℝ)⁻¹ * x) := by
  apply (WallBridge.isNormalInBase_iff_isEquidistributedModuloOne b hb _).mpr
  apply equidistributed_of_natScale WallBridgeMeasure.equidist_iff_empirical b m hb hm
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  simpa only [mul_inv_cancel_left₀ hmR] using
    (WallBridge.isNormalInBase_iff_isEquidistributedModuloOne b hb x).mp hx

end WallInverse

theorem OMA.solution :
    OMA.R_AlgebraicNormality_irrational_algebraic_normal_in_some_base_R1_H1_R1.H3 := by
  intro b hb x m hm hx
  exact WallInverse.normal_div_nat hb hx hm
