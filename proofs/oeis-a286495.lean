import OMAStatements.S_oeis_a286495
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Nth
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Instances.Real.Lemmas

/-! Proof of Clark Kimberling's OEIS A286495 gap and limit statements. -/

namespace OMA.S_oeis_a286495

theorem tm_lt (n : ℕ) : tm n < 2 := Nat.mod_lt _ (by decide)
theorem tm_even (n : ℕ) : tm (2*n) = tm n := by
  cases n with
  | zero => rfl
  | succ n =>
    unfold tm
    rw [Nat.digits_of_two_le_of_pos (by decide) (by omega : 0 < 2*(n+1))]
    simp
theorem tm_odd (n : ℕ) : tm (2*n+1) = 1-tm n := by
  unfold tm
  rw [Nat.digits_of_two_le_of_pos (by decide) (by omega : 0 < 2*n+1)]
  rw [show (2*n+1)/2 = n by omega]
  simp
  omega
end OMA.S_oeis_a286495

namespace OMA.S_oeis_a286495
def prefixSum (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => prefixSum f n + f n

abbrev matchAt (t : ℕ → ℕ) (i : ℕ) :=
  t i = 1 ∧ t (i+1) = 0 ∧ t (i+2) = 1 ∧ t (i+3) = 1

def matchBit (t : ℕ → ℕ) (i : ℕ) := if matchAt t i then 1 else 0

end OMA.S_oeis_a286495

namespace OMA.S_oeis_a286495

private theorem no_even_mark (q : ℕ) : ¬ matchAt tm (2*q) := by
  rintro ⟨_, _, h₂, h₃⟩
  rw [show 2*q+2 = 2*(q+1) by omega, tm_even] at h₂
  rw [show 2*q+3 = 2*(q+1)+1 by omega, tm_odd, h₂] at h₃
  contradiction

private theorem marks_after (i : ℕ) (h : matchAt tm i) :
    matchBit tm (i+1) = 0 ∧ matchBit tm (i+2) = 0 ∧ matchBit tm (i+3) = 0 := by
  obtain ⟨h₀,h₁,h₂,h₃⟩ := h
  have one : ¬ matchAt tm (i+1) := by
    rintro ⟨hh, _⟩
    omega
  have two : ¬ matchAt tm (i+2) := by
    rintro ⟨_, hh, _⟩
    exact (by omega : ¬ tm (i+3) = 0) hh
  have three : ¬ matchAt tm (i+3) := by
    have hi : i % 2 ≠ 0 := by
      intro he
      exact no_even_mark (i/2) (by simpa [show 2*(i/2)=i by omega] using
        (show matchAt tm i from ⟨h₀,h₁,h₂,h₃⟩))
    rw [show i+3=2*((i+3)/2) by omega]
    exact no_even_mark _
  simp [matchBit, one, two, three]

theorem scan_accounting (k : ℕ) :
    pos k = k + 3 * prefixSum (matchBit tm) (pos k) ∧
    prefixSum w k + 3 * prefixSum (matchBit tm) (pos k) = prefixSum tm (pos k) := by
  induction k with
  | zero => simp [pos,prefixSum]
  | succ k ih =>
    by_cases h : matchAt tm (pos k)
    · have hm : matchBit tm (pos k) = 1 := by simp [matchBit, h]
      obtain ⟨ha,hb,hc⟩ := marks_after _ h
      have hs : pos (k+1) = pos k + 4 := if_pos h
      have hw : w k = 0 := if_pos h
      obtain ⟨a,b,c,d⟩ := h
      rw [hs]
      simp only [prefixSum, hw, hm, ha, hb, hc, a, b, c, d]
      omega
    · have hs : pos (k+1) = pos k + 1 := if_neg h
      have hw : w k = tm (pos k) := if_neg h
      have hm : matchBit tm (pos k) = 0 := by simp [matchBit, h]
      rw [hs]
      simp only [prefixSum, hw, hm]
      omega

theorem count_w_eq (k : ℕ) : Nat.count (fun i => w i = 1) k = prefixSum w k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hw : w k < 2 := by unfold w; split <;> first | decide | apply tm_lt
    rw [Nat.count_succ, ih]
    simp only [prefixSum]
    split <;> omega
end OMA.S_oeis_a286495

namespace OMA.S_oeis_a286495

private def hit (t : ℕ → ℕ) (p : ℕ) : Bool :=
  decide (t p = 1 ∧ t (p+1) = 0 ∧ t (p+2) = 1 ∧ t (p+3) = 1)

private def advance (t : ℕ → ℕ) (p : ℕ) : ℕ := p + if hit t p then 4 else 1

private def output (t : ℕ → ℕ) (p : ℕ) : ℕ := if hit t p then 0 else t p

private def scan (t : ℕ → ℕ) (p : ℕ) : ℕ → ℕ
  | 0 => p
  | n+1 => advance t (scan t p n)

-- Consecutive aligned blocks of length 32 are either the base block or its complement.
private def localWord (x y i : ℕ) : ℕ :=
  if i < 32 then (x + tm i) % 2 else (y + tm (i-32)) % 2

private def gapOk (t : ℕ → ℕ) (p d : ℕ) : Bool :=
  (output t (scan t p d) == 1) &&
    ((List.range d).drop 1).all (fun e => output t (scan t p e) != 1)

private def gaps : List ℕ := [1,2,3,5,6]

-- Within six scan steps, each starting offset has enough lookahead in these two blocks.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem finite_gap (x y : Fin 2) (p : Fin 32) :
    output (localWord x y) p = 1 →
    gaps.any (gapOk (localWord x y) p) = true :=
  (by decide : ∀ (x y : Fin 2) (p : Fin 32),
    output (localWord x y) p = 1 →
    gaps.any (gapOk (localWord x y) p) = true) x y p

private theorem tm_block (m b i : ℕ) (hi : i < 2^m) :
    tm (2^m*b+i) = (tm b + tm i) % 2 := by
  induction m generalizing i with
  | zero =>
    simp only [pow_zero] at hi ⊢
    have : i = 0 := by omega
    subst i
    have hzero : tm 0 = 0 := by decide
    simpa [hzero] using (Nat.mod_eq_of_lt (tm_lt b)).symm
  | succ m ih =>
    have hp : i / 2 < 2 ^ m := by rw [pow_succ] at hi; omega
    have hh := ih (i/2) hp
    have hparity : i = 2*(i/2) ∨ i = 2*(i/2)+1 := by omega
    rcases hparity with h | h
    · conv_lhs => rw [show 2^(m+1)*b+i = 2*(2^m*b+i/2) by rw [pow_succ, Nat.mul_right_comm]; omega]
      rw [tm_even, hh]
      have ht : tm i = tm (i/2) := by nth_rewrite 1 [h]; exact tm_even _
      rw [ht]
    · conv_lhs => rw [show 2^(m+1)*b+i = 2*(2^m*b+i/2)+1 by rw [pow_succ, Nat.mul_right_comm]; omega]
      rw [tm_odd, hh]
      have ht : tm i = 1 - tm (i/2) := by nth_rewrite 1 [h]; exact tm_odd _
      rw [ht]
      have := tm_lt b
      have := tm_lt (i/2)
      omega

private theorem localWord_correct (b i : ℕ) (hi : i < 64) :
    tm (32*b+i) = localWord (tm b) (tm (b+1)) i := by
  unfold localWord
  split
  · exact tm_block 5 b i (by assumption)
  · rw [show 32*b+i = 32*(b+1)+(i-32) by omega]
    exact tm_block 5 (b+1) (i-32) (by omega)

private theorem pos_scan (k n : ℕ) : pos (k+n) = scan tm (pos k) n := by
  induction n with
  | zero => simp [scan]
  | succ n =>
    rw [← Nat.add_assoc]
    simp [pos, scan, advance, hit, *]
    split <;> rfl

private theorem output_w (k : ℕ) : output tm (pos k) = w k := by
  simp [output, hit, w]

private theorem hit_local (b p : ℕ) (hp : p+3 < 64) :
    hit tm (32*b+p) = hit (localWord (tm b) (tm (b+1))) p := by
  simp only [hit, Nat.add_assoc, localWord_correct b p (by omega),
    localWord_correct b (p+1) (by omega), localWord_correct b (p+2) (by omega),
    localWord_correct b (p+3) (by omega)]

private theorem output_local (b p : ℕ) (hp : p+3 < 64) :
    output tm (32*b+p) = output (localWord (tm b) (tm (b+1))) p := by
  simp [output, hit_local b p hp, localWord_correct b p (by omega)]

private theorem scan_bound (t : ℕ → ℕ) (p n : ℕ) : scan t p n ≤ p+4*n := by
  induction n with
  | zero => simp [scan]
  | succ n ih =>
    dsimp [scan, advance]
    split <;> omega

private theorem scan_local (b p n : ℕ) (hp : p+4*n+3 < 64) :
    scan tm (32*b+p) n = 32*b+scan (localWord (tm b) (tm (b+1))) p n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [scan, advance, ih (by omega)]
    rw [hit_local b _ (by have := scan_bound (localWord (tm b) (tm (b+1))) p n; omega)]
    omega

/-- The first following 1 occurs at one of the five allowed distances. -/
theorem next_gap (k : ℕ) (hk : w k = 1) :
    ∃ d ∈ ([1,2,3,5,6] : List ℕ), w (k+d)=1 ∧ ∀ e, 0<e → e<d → w (k+e) ≠ 1 := by
  let b := pos k / 32
  let p := pos k % 32
  have hp : p < 32 := Nat.mod_lt _ (by decide)
  have hpos : pos k = 32*b+p := by dsimp [b,p]; omega
  have heq (n : ℕ) (hn : n ≤ 6) :
      w (k+n) = output (localWord (tm b) (tm (b+1))) (scan (localWord (tm b) (tm (b+1))) p n) := by
    rw [← output_w, pos_scan, hpos, scan_local b p n (by omega)]
    exact output_local b _ (by have := scan_bound (localWord (tm b) (tm (b+1))) p n; omega)
  have hf := finite_gap ⟨tm b, tm_lt b⟩ ⟨tm (b+1), tm_lt _⟩ ⟨p,hp⟩ (by simpa [scan] using (heq 0 (by decide)).symm.trans (by simpa using hk))
  obtain ⟨d, hd, hc⟩ := List.any_eq_true.mp hf
  have hd6 : d ≤ 6 := by simp [gaps] at hd; omega
  refine ⟨d, hd, ?_, ?_⟩
  · simp only [gapOk, Bool.and_eq_true, beq_iff_eq] at hc
    rw [heq d hd6]
    exact hc.1
  · intro e he hed
    simp only [gapOk, Bool.and_eq_true, List.all_eq_true] at hc
    have he_mem : e ∈ (List.range d).drop 1 := by
      cases d with
      | zero => omega
      | succ d =>
        simp only [List.range_succ_eq_map, List.drop_succ_cons, List.drop_zero, List.mem_map, List.mem_range]
        exact ⟨e-1, by omega, by omega⟩
    rw [heq e (by omega)]
    simpa using hc.2 _ he_mem

end OMA.S_oeis_a286495

namespace OMA.S_oeis_a286495

section AbstractWord

variable (t : ℕ → ℕ)
variable (even : ∀ n, t (2*n) = t n)
variable (odd : ∀ n, t (2*n+1) = 1-t n)
variable (ltTwo : ∀ n, t n < 2)

def eqPair (t : ℕ → ℕ) (i : ℕ) := if t i = t (i+1) then 1 else 0

def zeroPair (t : ℕ → ℕ) (i : ℕ) := if t i = 0 ∧ t (i+1) = 0 then 1 else 0

include even odd ltTwo

lemma eqPair_even (n : ℕ) : eqPair t (2*n) = 0 := by
  unfold eqPair
  rw [even, odd, if_neg]
  have := ltTwo n
  omega

lemma eqPair_odd (n : ℕ) : eqPair t (2*n+1) = 1 - eqPair t n := by
  have h : 2*n+1+1 = 2*(n+1) := by omega
  unfold eqPair
  rw [h, even, odd]
  have ha := ltTwo n
  have hb := ltTwo (n+1)
  split_ifs <;> omega

lemma prefix_eqPair_even (n : ℕ) : prefixSum (eqPair t) (2*n) = n - prefixSum (eqPair t) n := by
  have bounded : ∀ m, prefixSum (eqPair t) m ≤ m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      simp only [prefixSum]
      have h : eqPair t m ≤ 1 := by unfold eqPair; split_ifs <;> omega
      omega
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 by omega]
    simp only [prefixSum]
    rw [eqPair_even t even odd ltTwo, eqPair_odd t even odd ltTwo, ih]
    have hb := bounded n
    by_cases h : t n = t (n+1)
    · have : eqPair t n = 1 := by simp [eqPair,h]
      omega
    · have : eqPair t n = 0 := by simp [eqPair,h]
      omega

lemma prefix_eqPair_odd (n : ℕ) : prefixSum (eqPair t) (2*n+1) = n - prefixSum (eqPair t) n := by
  simp only [prefixSum]
  rw [prefix_eqPair_even t even odd ltTwo, eqPair_even t even odd ltTwo, Nat.add_zero]

lemma prefix_ones_even (n : ℕ) : prefixSum t (2*n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 by omega]
    simp only [prefixSum]
    rw [even, odd, ih]
    have := ltTwo n
    omega

lemma prefix_ones_odd (n : ℕ) : prefixSum t (2*n+1) = n + t n := by
  simp only [prefixSum]
  rw [even, prefix_ones_even t even odd ltTwo]

omit even odd in
lemma zeroPair_identity (n : ℕ) : 2 * prefixSum (zeroPair t) n + prefixSum t n +
    prefixSum t (n+1) = prefixSum (eqPair t) n + n + t 0 := by
  induction n with
  | zero => simp [prefixSum]
  | succ n ih =>
    simp only [prefixSum] at ih ⊢
    have h : 2 * zeroPair t n + t n + t (n+1) = eqPair t n + 1 := by
      unfold zeroPair eqPair
      have ha := ltTwo n
      have hb := ltTwo (n+1)
      split_ifs <;> omega
    omega

omit ltTwo in
lemma matches_even (n : ℕ) : matchBit t (2*n) = 0 := by
  have h₂ : 2*n+2 = 2*(n+1) := by omega
  have h₃ : 2*n+3 = 2*(n+1)+1 := by omega
  unfold matchBit matchAt
  rw [h₂, h₃, even (n+1), odd (n+1), if_neg]
  omega

lemma matches_odd (n : ℕ) : matchBit t (2*n+1) = zeroPair t n := by
  have h₁ : 2*n+1+1 = 2*(n+1) := by omega
  have h₂ : 2*n+1+2 = 2*(n+1)+1 := by omega
  have h₃ : 2*n+1+3 = 2*(n+2) := by omega
  unfold matchBit matchAt zeroPair
  rw [h₁,h₂,h₃,even,even,odd,odd]
  have ha := ltTwo n
  have hb := ltTwo (n+1)
  have hc := ltTwo (n+2)
  have hno : ¬ (t n = 0 ∧ t (n+1) = 0 ∧ t (n+2) = 0) := by
    rintro ⟨hₙ,hₛ,hₛ₂⟩
    by_cases hn : n % 2 = 0
    · rw [show n = 2*(n/2) by omega, even] at hₙ
      rw [show n+1 = 2*(n/2)+1 by omega, odd] at hₛ
      omega
    · rw [show n+1 = 2*(n/2+1) by omega, even] at hₛ
      rw [show n+2 = 2*(n/2+1)+1 by omega, odd] at hₛ₂
      omega
  split_ifs <;> omega

lemma prefix_matches_even (n : ℕ) : prefixSum (matchBit t) (2*n) = prefixSum (zeroPair t) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 by omega]
    simp only [prefixSum]
    rw [matches_even t even odd, matches_odd t even odd ltTwo, ih, Nat.add_zero]

open Filter Topology

def pairError (t : ℕ → ℕ) (n : ℕ) : ℝ := 3*(prefixSum (eqPair t) n : ℝ) - n

lemma pairError_step (n : ℕ) : |pairError t n| ≤ |pairError t (n/2)| + 1 := by
  let m := n / 2
  have hm : n = 2*m ∨ n = 2*m+1 := by dsimp [m]; omega
  have hb : prefixSum (eqPair t) m ≤ m := by
    induction m with
    | zero => rfl
    | succ m ih =>
      simp only [prefixSum]
      have h : eqPair t m ≤ 1 := by unfold eqPair; split_ifs <;> omega
      omega
  change |pairError t n| ≤ |pairError t m| + 1
  rcases hm with hm | hm
  · have hs := prefix_eqPair_even t even odd ltTwo m
    rw [hm, pairError, hs, Nat.cast_sub hb]
    have h : 3*((m : ℝ) - prefixSum (eqPair t) m) - ↑(2*m) = -pairError t m := by
      simp [pairError]
      ring
    rw [h, abs_neg]
    linarith
  · have hs := prefix_eqPair_odd t even odd ltTwo m
    rw [hm, pairError, hs, Nat.cast_sub hb]
    have h : 3*((m : ℝ) - prefixSum (eqPair t) m) - ↑(2*m+1) = -pairError t m + (-1) := by
      simp [pairError]
      ring
    rw [h]
    simpa using abs_add_le (-pairError t m) (-1)

lemma pairError_sublinear (ε : ℝ) (he : 0 < ε) :
    ∃ C : ℝ, ∀ n : ℕ, |pairError t n| ≤ ε*n + C := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2/ε + 2)
  let C := ∑ k ∈ Finset.range (N+1), |pairError t k|
  refine ⟨C, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ N
    · have hC : |pairError t n| ≤ C :=
        Finset.single_le_sum (fun k _ => abs_nonneg (pairError t k)) (Finset.mem_range.mpr (by omega))
      linarith [mul_nonneg he.le (Nat.cast_nonneg n)]
    · have hq : n/2 < n := by omega
      have hk := ih (n/2) hq
      have hstep := pairError_step t even odd ltTwo n
      have htwo : (2 : ℝ) * ((n/2 : ℕ) : ℝ) ≤ n := by exact_mod_cast (show 2*(n/2) ≤ n by omega)
      have hgt : (N : ℝ) < n := by exact_mod_cast (Nat.lt_of_not_ge hn)
      have hε : (2 : ℝ) < ε * n := by
        rw [mul_comm]
        apply (div_lt_iff₀ he).mp
        linarith
      nlinarith
lemma prefix_ones_error (n : ℕ) : |2*(prefixSum t n : ℝ)-n| ≤ 1 := by
  have hn : n = 2*(n/2) ∨ n = 2*(n/2)+1 := by omega
  generalize n/2 = m at hn
  rcases hn with hn | hn
  · rw [hn, prefix_ones_even t even odd ltTwo]
    push_cast
    simp
  · rw [hn, prefix_ones_odd t even odd ltTwo]
    have h : (t m : ℝ) ≤ 1 := by exact_mod_cast (show t m ≤ 1 from Nat.le_of_lt_succ (ltTwo m))
    have hzero : (0:ℝ) ≤ t m := Nat.cast_nonneg _
    push_cast
    rw [abs_le]
    constructor <;> linarith

lemma match_error (n : ℕ) : |12*(prefixSum (matchBit t) n : ℝ)-n|
    ≤ 2*|pairError t (n/2)|+7 := by
  let m := n/2
  have hm : n = 2*m ∨ n = 2*m+1 := by dsimp [m]; omega
  have hrange : 2*m ≤ n ∧ n ≤ 2*m+1 := by omega
  have hh : prefixSum (matchBit t) n = prefixSum (zeroPair t) m := by
    rcases hm with hm | hm
    · rw [hm, prefix_matches_even t even odd ltTwo]
    · rw [hm]
      simp only [prefixSum]
      rw [matches_even t even odd, prefix_matches_even t even odd ltTwo, Nat.add_zero]
  have hp : prefixSum t m + prefixSum t (m+1) = m + t (m/2) := by
    have hm2 : m = 2*(m/2) ∨ m = 2*(m/2)+1 := by omega
    generalize m/2 = j at *
    rcases hm2 with h | h
    · rw [h, prefix_ones_even t even odd ltTwo, prefix_ones_odd t even odd ltTwo]
      omega
    · rw [h, show 2*j+1+1 = 2*(j+1) by omega, prefix_ones_odd t even odd ltTwo,
        prefix_ones_even t even odd ltTwo]
      omega
  have hZ := zeroPair_identity t ltTwo m
  have hI : 2*(prefixSum (zeroPair t) m : ℝ) + t (m/2) =
      prefixSum (eqPair t) m + t 0 := by
    have h : 2*prefixSum (zeroPair t) m + t (m/2) = prefixSum (eqPair t) m + t 0 := by omega
    exact_mod_cast h
  have hlo : (2 : ℝ)*m ≤ n := by exact_mod_cast hrange.1
  have hhi : (n : ℝ) ≤ 2*(m : ℝ)+1 := by exact_mod_cast hrange.2
  have hzero : (0:ℝ) ≤ t 0 := Nat.cast_nonneg _
  have hone : (t 0:ℝ) ≤ 1 := by exact_mod_cast (show t 0 ≤ 1 from Nat.le_of_lt_succ (ltTwo 0))
  have hmid : (0:ℝ) ≤ t (m/2) := Nat.cast_nonneg _
  have hmid1 : (t (m/2):ℝ) ≤ 1 := by exact_mod_cast (show t (m/2) ≤ 1 from Nat.le_of_lt_succ (ltTwo (m/2)))
  change |12*(prefixSum (matchBit t) n : ℝ)-n| ≤ 2*|pairError t m|+7
  rw [hh, abs_le]
  simp only [pairError]
  constructor
  · linarith [neg_abs_le (3*(prefixSum (eqPair t) m : ℝ)-m)]
  · linarith [le_abs_self (3*(prefixSum (eqPair t) m : ℝ)-m)]

theorem abstract_density_discrepancy (p out : ℕ → ℕ)
    (hp : ∀ k, p k = k + 3*prefixSum (matchBit t) (p k))
    (hout : ∀ k, prefixSum out k + 3*prefixSum (matchBit t) (p k) = prefixSum t (p k))
    (hpBound : ∀ k, p k ≤ 4*k)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ k : ℕ, |3*(prefixSum out k : ℝ)-k| ≤ ε*k + C := by
  obtain ⟨C,hC⟩ := pairError_sublinear t even odd ltTwo (ε/2) (by positivity)
  refine ⟨C+5, fun k => ?_⟩
  have hhalf : ((p k/2 : ℕ):ℝ) ≤ 2*(k:ℝ) := by
    exact_mod_cast (show p k/2 ≤ 2*k from by have := hpBound k; omega)
  have hpair := hC (p k/2)
  have herr := match_error t even odd ltTwo (p k)
  have hones := prefix_ones_error t even odd ltTwo (p k)
  have hpin : (p k : ℝ) = (k : ℝ) + 3*(prefixSum (matchBit t) (p k) : ℝ) := by exact_mod_cast hp k
  have houtR : (prefixSum out k : ℝ) + 3*(prefixSum (matchBit t) (p k) : ℝ)
      = prefixSum t (p k) := by exact_mod_cast hout k
  rw [abs_le] at herr hones ⊢
  constructor <;> nlinarith
end AbstractWord

theorem density_discrepancy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ k : ℕ, |3*(prefixSum w k : ℝ)-k| ≤ ε*k + C := by
  apply abstract_density_discrepancy tm tm_even tm_odd tm_lt pos w
    (fun k => (scan_accounting k).1) (fun k => (scan_accounting k).2) _ ε hε
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : pos (k+1) ≤ pos k+4 := by
      change (if matchAt tm (pos k) then pos k + 4 else pos k + 1) ≤ _
      split_ifs <;> omega
    omega

end OMA.S_oeis_a286495

open Filter Topology

namespace A286495

/-- Transfer a bound on gaps between successive hits to the one-based enumeration. -/
theorem indexed_gaps {p : ℕ → Prop} (hp : {n | p n}.Infinite)
    (hg : ∀ i j, p i → p j → i < j → (∀ k, i < k → k < j → ¬ p k) →
      j-i ∈ ([1,2,3,5,6] : List ℕ)) :
    ∀ n : ℕ, 2 ≤ n →
      ((Nat.nth p (n-1)+1) - (Nat.nth p (n-1-1)+1)) ∈ ([1,2,3,5,6] : List ℕ) := by
  intro n hn
  have hs : n - 1 = (n - 1 - 1) + 1 := by omega
  simp only [Nat.add_sub_add_right]
  refine hg _ _ (Nat.nth_mem_of_infinite hp _) (Nat.nth_mem_of_infinite hp _) ?_ ?_
  · exact Nat.nth_strictMono hp (by omega)
  · intro k hk hlt hpk
    rw [hs] at hlt
    exact (not_le_of_gt hk) (Nat.le_nth_of_lt_nth_succ hlt hpk)

/-- Positive prefix density guarantees infinitely many hits. -/
theorem infinite_of_density {p : ℕ → Prop} [DecidablePred p]
    (hd : Tendsto (fun n : ℕ => (Nat.count p n : ℝ) / n) atTop (𝓝 (1/3))) :
    {n | p n}.Infinite := by
  intro hf
  have hlarge : ∀ᶠ n : ℕ in atTop, (1/4 : ℝ) < (Nat.count p n : ℝ) / n :=
    hd.eventually_const_lt (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hlarge
  let n := max N (4 * hf.toFinset.card + 1)
  have hn : 0 < n := lt_of_lt_of_le (by omega : 0 < 4 * hf.toFinset.card + 1) (le_max_right ..)
  have hratio := hN n (le_max_left ..)
  have hcard : (Nat.count p n : ℝ) ≤ hf.toFinset.card := by
    exact_mod_cast Nat.count_le_card hf n
  have hx : (4 * hf.toFinset.card : ℝ) < n := by
    exact_mod_cast (show 4 * hf.toFinset.card < n from
      Nat.lt_of_succ_le (le_max_right ..))
  have hdiv := (lt_div_iff₀ (Nat.cast_pos.mpr hn : (0 : ℝ) < n)).mp hratio
  linarith

/-- Invert the positive density at prefix lengths ending at the n-th hit. -/
theorem indexed_limit {p : ℕ → Prop} [DecidablePred p]
    (hd : Tendsto (fun n : ℕ => (Nat.count p n : ℝ) / n) atTop (𝓝 (1/3))) :
    Tendsto (fun n : ℕ => ((Nat.nth p (n-1)+1 : ℕ) : ℝ) / n) atTop (𝓝 3) := by
  have hp := infinite_of_density hd
  have hs : Tendsto (fun n : ℕ => n-1) atTop atTop :=
    tendsto_atTop.2 fun m => eventually_atTop.2 ⟨m+1, fun n hn => by omega⟩
  have hnth : Tendsto (fun k : ℕ => Nat.nth p k + 1) atTop atTop :=
    (show StrictMono (fun k => Nat.nth p k + 1) from
      fun _ _ h => Nat.add_lt_add_right (Nat.nth_strictMono hp h) 1).tendsto_atTop
  have hc := hd.comp (hnth.comp hs)
  have hi := hc.inv₀ (by norm_num : (1/3 : ℝ) ≠ 0)
  norm_num at hi
  refine hi.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  simp only [Nat.count_nth_succ_of_infinite hp, Nat.sub_add_cancel hn, Nat.cast_add,
    Nat.cast_one]

end A286495

open Filter Topology

namespace OMA.S_oeis_a286495

/-- A sublinear discrepancy gives density one third. -/
theorem density_of_discrepancy {p : ℕ → Prop} [DecidablePred p]
    (hd : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ,
      |3 * (Nat.count p n : ℝ) - n| ≤ ε * n + C) :
    Tendsto (fun n : ℕ => (Nat.count p n : ℝ) / n) atTop (𝓝 (1/3)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨C, hC⟩ := hd ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (max 0 (C/ε))
  refine ⟨N, ?_⟩
  intro n hn
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := (lt_of_le_of_lt (le_max_left ..) hN).trans_le hnR
  have hsmall : C < ε * n := by
    have hc : C / ε < (n : ℝ) := (lt_of_le_of_lt (le_max_right ..) hN).trans_le hnR
    nlinarith [(div_lt_iff₀ hε).mp hc]
  rw [Real.dist_eq, abs_lt]
  have hb := abs_le.mp (hC n)
  constructor
  · have hdiv : (1/3 : ℝ) - ε < (Nat.count p n : ℝ) / n := by
      apply (lt_div_iff₀ hpos).mpr
      nlinarith [mul_pos hε hpos]
    linarith
  · have hdiv : (Nat.count p n : ℝ) / n < (1/3 : ℝ) + ε := by
      apply (div_lt_iff₀ hpos).mpr
      nlinarith [mul_pos hε hpos]
    linarith

/-- Complete the upstream conclusion once the scan discrepancy is bounded. -/
theorem assemble
    (hd : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ,
      |((3 * prefixSum w n : ℕ) : ℝ) - n| ≤ ε * n + C) :
    (∀ n, 2 ≤ n → a n - a (n - 1) = 1 ∨ a n - a (n - 1) = 2 ∨
      a n - a (n - 1) = 3 ∨ a n - a (n - 1) = 5 ∨ a n - a (n - 1) = 6) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 3) := by
  have hden : Tendsto (fun n : ℕ => (Nat.count (fun i => w i = 1) n : ℝ) / n)
      atTop (𝓝 (1/3)) := by
    apply density_of_discrepancy
    intro ε hε
    obtain ⟨C, hC⟩ := hd ε hε
    refine ⟨C, fun n => ?_⟩
    simpa [Nat.cast_mul, count_w_eq] using hC n
  have hinf := A286495.infinite_of_density hden
  constructor
  · intro n hn
    have hg := A286495.indexed_gaps hinf (fun i j hi hj hij hnext => by
      obtain ⟨d, hd, hhit, hgap⟩ := next_gap i hi
      have hpos : 0 < d := by simp at hd; omega
      have heq : j = i + d := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact (hgap (j-i) (by omega) (by omega)) (by
            simpa [show i + (j-i) = j by omega] using hj)
        · exact hnext (i+d) (by omega) hgt hhit
      rwa [heq, Nat.add_sub_cancel_left]) n hn
    simpa [a, List.mem_cons, eq_comm, or_assoc] using hg
  · exact A286495.indexed_limit hden

end OMA.S_oeis_a286495

open OMA.S_oeis_a286495 in
theorem OMA.solution : type_of% @OMA.S_oeis_a286495.main := by
  apply assemble
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using density_discrepancy
