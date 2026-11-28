import OMAStatements.S_oeis_a250271
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Dist
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

-- Problem: A250271, ternary words admitting a zero signed sum of squared differences.
-- Source: https://oeis.org/A250271
-- Statement credit: @VashaTS
-- Proof credit: @CubeJerry
-- A parity criterion gives an exact finite word automaton. Its transfer identities
-- yield the closed count and the conjectured generating function.

-- Component: A250271Machine

namespace A250271Machine

abbrev Letter := Fin 3
abbrev State := Letter × Fin 6 × Fin 2

def diff (p c : Letter) : Letter :=
  ⟨Nat.dist p.val c.val, by
    have hp := p.isLt
    have hc := c.isLt
    simp only [Nat.dist]
    omega⟩

def inc (q : Fin 6) : Fin 6 :=
  if h : q.val < 4 then ⟨q.val + 1, by omega⟩
  else if q = 4 then 5 else 4

def step (s : State) (c : Letter) : State :=
  (c, (if diff s.1 c = 1 then inc s.2.1 else s.2.1),
    (if diff s.1 c = 2 then ⟨(s.2.2.val + 1) % 2, Nat.mod_lt _ (by decide)⟩
      else s.2.2))

def initial (c : Letter) : State := (c, 0, 0)

def final (s : State) : ℕ :=
  if s.2.1.val % 2 = 0 ∧ (s.2.2 = 0 ∨ s.2.1 = 4) then 1 else 0

def run : State → List Letter → State
  | s, [] => s
  | s, c :: cs => run (step s c) cs

def Accepted {n : ℕ} (w : Fin (n + 1) → Letter) : Prop :=
  final (run (initial (w 0)) (List.ofFn fun i : Fin n => w i.succ)) = 1

instance {n : ℕ} (w : Fin (n + 1) → Letter) : Decidable (Accepted w) :=
  inferInstanceAs (Decidable (_ = _))

end A250271Machine

-- Component: A250271Signs

namespace A250271Signs

open Finset

variable {ι : Type*} [Fintype ι]

def ones (f : ι → Fin 3) : ℕ :=
  (univ.filter fun i => f i = 1).card

def twos (f : ι → Fin 3) : ℕ :=
  (univ.filter fun i => f i = 2).card

def selected (f : ι → Fin 3) (b : ι → Bool) (v : Fin 3) : ℕ :=
  (univ.filter fun i => f i = v ∧ b i = true).card

lemma scalar_identity (v : Fin 3) (b : Bool) :
    (if b then (1 : ℤ) else -1) * (v.val : ℤ) ^ 2 =
      2 * (if v = 1 ∧ b = true then (1 : ℤ) else 0) +
      8 * (if v = 2 ∧ b = true then (1 : ℤ) else 0) -
      (if v = 1 then (1 : ℤ) else 0) -
      4 * (if v = 2 then (1 : ℤ) else 0) := by
  fin_cases v <;> cases b <;> decide

lemma sum_sign_eq (f : ι → Fin 3) (b : ι → Bool) :
    (∑ i, (if b i then (1 : ℤ) else -1) * (f i).val ^ 2) =
      2 * (selected f b 1 : ℤ) + 8 * (selected f b 2 : ℤ) -
      ones f - 4 * twos f := by
  classical
  simp_rw [scalar_identity]
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]
  simp [selected, ones, twos]

lemma selected_le (f : ι → Fin 3) (b : ι → Bool) (v : Fin 3) :
    selected f b v ≤ (univ.filter fun i => f i = v).card := by
  apply card_le_card
  intro i hi
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  exact hi.1

lemma arithmetic (a b : ℕ) :
    (∃ x ≤ a, ∃ y ≤ b, 2 * x + 8 * y = a + 4 * b) ↔
      a % 2 = 0 ∧ (b % 2 = 0 ∨ 4 ≤ a) := by
  constructor
  · rintro ⟨x, hxa, y, hyb, he⟩
    constructor
    · omega
    · by_cases h : 4 ≤ a
      · exact Or.inr h
      · left
        omega
  · rintro ⟨ha, hb⟩
    rcases hb with hb | ha4
    · exact ⟨a / 2, by omega, b / 2, by omega, by omega⟩
    · by_cases hb : b % 2 = 0
      · exact ⟨a / 2, by omega, b / 2, by omega, by omega⟩
      · exact ⟨(a - 4) / 2, by omega, (b + 1) / 2, by omega, by omega⟩

lemma exists_selected (f : ι → Fin 3) (x y : ℕ)
    (hx : x ≤ ones f) (hy : y ≤ twos f) :
    ∃ b : ι → Bool, selected f b 1 = x ∧ selected f b 2 = y := by
  classical
  obtain ⟨U, hU, hUc⟩ := exists_subset_card_eq (s := univ.filter fun i => f i = 1) hx
  obtain ⟨V, hV, hVc⟩ := exists_subset_card_eq (s := univ.filter fun i => f i = 2) hy
  have hu : ∀ i ∈ U, f i = 1 := fun i hi => (mem_filter.mp (hU hi)).2
  have hv : ∀ i ∈ V, f i = 2 := fun i hi => (mem_filter.mp (hV hi)).2
  let b : ι → Bool := fun i => decide (i ∈ U ∪ V)
  have hU' : (univ.filter fun i => f i = 1 ∧ b i = true) = U := by
    ext i
    simp only [mem_filter, mem_univ, true_and, b, decide_eq_true_eq, mem_union]
    constructor
    · rintro ⟨hi, hiU | hiV⟩
      · exact hiU
      · have hi2 := hv i hiV
        have : (1 : Fin 3) = 2 := hi.symm.trans hi2
        exact False.elim ((by decide : (1 : Fin 3) ≠ 2) this)
    · intro hi
      exact ⟨hu i hi, Or.inl hi⟩
  have hV' : (univ.filter fun i => f i = 2 ∧ b i = true) = V := by
    ext i
    simp only [mem_filter, mem_univ, true_and, b, decide_eq_true_eq, mem_union]
    constructor
    · rintro ⟨hi, hiU | hiV⟩
      · have hi1 := hu i hiU
        have : (1 : Fin 3) = 2 := hi1.symm.trans hi
        exact False.elim ((by decide : (1 : Fin 3) ≠ 2) this)
      · exact hiV
    · intro hi
      exact ⟨hv i hi, Or.inr hi⟩
  exact ⟨b, by simp [selected, hU', hUc], by simp [selected, hV', hVc]⟩

lemma signed_zero_iff (f : ι → Fin 3) :
    (∃ b : ι → Bool, ∑ i, (if b i then (1 : ℤ) else -1) * (f i).val ^ 2 = 0) ↔
      ones f % 2 = 0 ∧ (twos f % 2 = 0 ∨ 4 ≤ ones f) := by
  rw [← arithmetic]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨selected f b 1, selected_le f b 1,
      selected f b 2, selected_le f b 2, ?_⟩
    rw [sum_sign_eq] at hb
    omega
  · rintro ⟨x, hx, y, hy, he⟩
    obtain ⟨b, hbx, hby⟩ := exists_selected f x y hx hy
    refine ⟨b, ?_⟩
    rw [sum_sign_eq, hbx, hby]
    omega

end A250271Signs

-- Component: A250271Semantic

namespace A250271Machine

def cap (a : ℕ) : Fin 6 :=
  if h : a < 4 then ⟨a, by omega⟩
  else ⟨4 + a % 2, by omega⟩

def encode (p : Letter) (a b : ℕ) : State :=
  (p, cap a, ⟨b % 2, Nat.mod_lt _ (by decide)⟩)

lemma cap_succ (a : ℕ) : cap (a + 1) = inc (cap a) := by
  by_cases h : a < 4
  · interval_cases a <;> decide
  · have ha : ¬ a + 1 < 4 := by omega
    have hm : a % 2 = 0 ∨ a % 2 = 1 := by omega
    rcases hm with hm | hm
    · have hs : (a + 1) % 2 = 1 := by omega
      norm_num [cap, h, ha, inc, hm, hs, Fin.ext_iff]
    · have hs : (a + 1) % 2 = 0 := by omega
      norm_num [cap, h, ha, inc, hm, hs, Fin.ext_iff]

lemma step_encode (p c : Letter) (a b : ℕ) :
    step (encode p a b) c =
      encode c (a + if diff p c = 1 then 1 else 0)
        (b + if diff p c = 2 then 1 else 0) := by
  fin_cases p <;> fin_cases c <;>
    simp [step, encode, diff, Nat.dist, cap_succ, Nat.add_mod]

def last : Letter → List Letter → Letter
  | p, [] => p
  | _, c :: cs => last c cs

def weights : Letter → List Letter → List Letter
  | _, [] => []
  | p, c :: cs => diff p c :: weights c cs

lemma weights_count_cons (p c v : Letter) (cs : List Letter) :
    (weights p (c :: cs)).count v =
      (if diff p c = v then 1 else 0) + (weights c cs).count v := by
  simp [weights, List.count_cons, Nat.add_comm]

lemma run_encode (p : Letter) (a b : ℕ) (cs : List Letter) :
    run (encode p a b) cs =
      encode (last p cs) (a + (weights p cs).count 1)
        (b + (weights p cs).count 2) := by
  induction cs generalizing p a b with
  | nil => simp [run, last, weights]
  | cons c cs ih =>
    simp only [run, step_encode, ih, last, weights_count_cons, Nat.add_assoc]

lemma final_encode (p : Letter) (a b : ℕ) :
    final (encode p a b) = 1 ↔ a % 2 = 0 ∧ (b % 2 = 0 ∨ 4 ≤ a) := by
  by_cases h : a < 4
  · interval_cases a <;> simp [final, encode, cap, Fin.ext_iff]
  · simp only [final, encode, cap, dif_neg h, Fin.ext_iff]
    split_ifs <;> simp_all <;> omega

lemma run_accept (p : Letter) (cs : List Letter) :
    final (run (initial p) cs) = 1 ↔
      (weights p cs).count 1 % 2 = 0 ∧
        ((weights p cs).count 2 % 2 = 0 ∨ 4 ≤ (weights p cs).count 1) := by
  change final (run (encode p 0 0) cs) = 1 ↔ _
  rw [run_encode, final_encode]
  simp

lemma weights_ofFn {n : ℕ} (w : Fin (n + 1) → Letter) :
    weights (w 0) (List.ofFn fun i : Fin n => w i.succ) =
      List.ofFn (fun i : Fin n => diff (w i.castSucc) (w i.succ)) := by
  induction n with
  | zero => simp [weights]
  | succ n ih =>
    rw [List.ofFn_succ, weights, List.ofFn_succ]
    congr 1
    simpa only [Fin.castSucc_succ] using ih (fun i => w i.succ)

lemma count_ofFn {n : ℕ} (f : Fin n → Letter) (v : Letter) :
    (List.ofFn f).count v = (Finset.univ.filter fun i => f i = v).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.count_cons, Fin.card_filter_univ_succ']
    simp [ih, Nat.add_comm]

lemma diff_square (p c : Letter) :
    ((diff p c).val : ℤ) ^ 2 = ((c.val : ℤ) - p.val) ^ 2 := by
  fin_cases p <;> fin_cases c <;> norm_num [diff, Nat.dist]

lemma signedSumZero_iff {n : ℕ} (w : Fin (n + 1) → Letter) :
    OMA.S_oeis_a250271.SignedSumZero w ↔ Accepted w := by
  unfold OMA.S_oeis_a250271.SignedSumZero
  simp_rw [OMA.S_oeis_a250271.sign, ← diff_square]
  rw [A250271Signs.signed_zero_iff]
  unfold Accepted
  rw [run_accept, weights_ofFn]
  simp only [A250271Signs.ones, A250271Signs.twos, count_ofFn]

lemma count_eq (n : ℕ) : OMA.S_oeis_a250271.a n =
    Nat.card {w : Fin (n + 1) → Letter // Accepted w} := by
  classical
  rw [Nat.card_eq_fintype_card]
  simp only [Fintype.card_subtype, OMA.S_oeis_a250271.a]
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, signedSumZero_iff]

end A250271Machine

-- Component: A250271Count

namespace A250271Count

open A250271Machine
open scoped BigOperators

def advance (f : State → ℤ) (s : State) : ℤ := ∑ c : Letter, f (step s c)

def count : ℕ → State → ℤ
  | 0 => fun s => final s
  | n + 1 => advance (count n)

lemma advance_add (f g : State → ℤ) :
    advance (fun s => f s + g s) = fun s => advance f s + advance g s := by
  funext s
  simp [advance, Finset.sum_add_distrib]

lemma advance_mul (k : ℤ) (f : State → ℤ) :
    advance (fun s => k * f s) = fun s => k * advance f s := by
  funext s
  simp [advance, Finset.mul_sum]

def admissible : (n : ℕ) → State → (Fin n → Letter) → Prop
  | 0, s, _ => final s = 1
  | n + 1, s, w => admissible n (step s (w 0)) (Fin.tail w)

lemma admissible_iff_run (n : ℕ) (s : State) (w : Fin n → Letter) :
    admissible n s w ↔ final (run s (List.ofFn w)) = 1 := by
  induction n generalizing s with
  | zero => simp [admissible, run]
  | succ n ih =>
    rw [admissible, List.ofFn_succ, run]
    exact ih (step s (w 0)) (Fin.tail w)

noncomputable def wordSuccEquiv (n : ℕ) (s : State) :
    {w : Fin (n + 1) → Letter // admissible (n + 1) s w} ≃
      (c : Letter) × {w : Fin n → Letter // admissible n (step s c) w} where
  toFun w := ⟨w.val 0, ⟨Fin.tail w.val, w.property⟩⟩
  invFun w := ⟨Fin.cons w.1 w.2.val, by
    simpa only [admissible, Fin.cons_zero, Fin.tail_cons] using w.2.property⟩
  left_inv w := by
    apply Subtype.ext
    exact Fin.cons_self_tail w.val
  right_inv w := by cases w; rfl

lemma card_admissible (n : ℕ) (s : State) :
    (Nat.card {w : Fin n → Letter // admissible n s w} : ℤ) = count n s := by
  classical
  induction n generalizing s with
  | zero =>
    by_cases h : s.2.1.val % 2 = 0 ∧ (s.2.2 = 0 ∨ s.2.1 = 4)
    · simp [admissible, count, final, h, Nat.card_eq_fintype_card]
    · simp [admissible, count, final, h, Nat.card_eq_fintype_card]
  | succ n ih =>
    rw [Nat.card_congr (wordSuccEquiv n s)]
    simp only [Nat.card_eq_fintype_card, Fintype.card_sigma, Nat.cast_sum]
    simp only [← Nat.card_eq_fintype_card, ih]
    rfl

noncomputable def acceptedEquiv (n : ℕ) :
    {w : Fin (n + 1) → Letter // Accepted w} ≃
      (c : Letter) × {w : Fin n → Letter // admissible n (initial c) w} where
  toFun w := ⟨w.val 0, ⟨Fin.tail w.val,
    (admissible_iff_run n _ _).mpr w.property⟩⟩
  invFun w := ⟨Fin.cons w.1 w.2.val, by
    have h := (admissible_iff_run n _ _).mp w.2.property
    simpa only [Accepted, Fin.cons_zero, Fin.cons_succ] using h⟩
  left_inv w := by
    apply Subtype.ext
    exact Fin.cons_self_tail w.val
  right_inv w := by cases w; rfl

lemma card_accepted (n : ℕ) :
    (Nat.card {w : Fin (n + 1) → Letter // Accepted w} : ℤ) =
      ∑ c : Letter, count n (initial c) := by
  classical
  rw [Nat.card_congr (acceptedEquiv n)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_sigma, Nat.cast_sum]
  simp only [← Nat.card_eq_fintype_card, card_admissible]

end A250271Count

-- Component: A250271CountCertificate

namespace A250271Count

open A250271Machine
open scoped BigOperators

def u (s : State) : ℤ :=
  ![![![0, -2], ![1, 0], ![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![4, 1], ![2, 0], ![0, -1], ![0, 0], ![0, 0], ![0, 0]], ![![0, -2], ![1, 0], ![0, 0], ![0, 0], ![0, 0], ![0, 0]]] s.1 s.2.1 s.2.2

def v (s : State) : ℤ :=
  ![![![0, 0], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![2, 0], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![0, 0], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![0, 0]]] s.1 s.2.1 s.2.2

def w (s : State) : ℤ :=
  ![![![-2, -2], ![-2, -2], ![-2, -2], ![0, 0], ![0, 0], ![0, 0]], ![![-4, -4], ![-4, -4], ![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![-2, -2], ![-2, -2], ![-2, -2], ![0, 0], ![0, 0], ![0, 0]]] s.1 s.2.1 s.2.2

def z (s : State) : ℤ :=
  ![![![-2, -2], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![0, 0], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![-2, -2], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![0, 0]]] s.1 s.2.1 s.2.2

def y (s : State) : ℤ :=
  ![![![6, 6], ![3, 3], ![6, 6], ![3, 3], ![6, 6], ![3, 3]], ![![3, 3], ![6, 6], ![3, 3], ![6, 6], ![3, 3], ![6, 6]], ![![6, 6], ![3, 3], ![6, 6], ![3, 3], ![6, 6], ![3, 3]]] s.1 s.2.1 s.2.2

lemma certificate_base : ∀ s : State, count 2 s = u s + w s + y s := by
  decide +kernel

lemma certificate_u : ∀ s : State, advance u s = u s + v s := by
  decide +kernel

lemma certificate_v : ∀ s : State, advance v s = v s := by
  decide +kernel

lemma certificate_w : ∀ s : State, advance w s = 2 * (w s + z s) := by
  decide +kernel

lemma certificate_z : ∀ s : State, advance z s = 2 * z s := by
  decide +kernel

lemma certificate_y : ∀ s : State, advance y s = 3 * y s := by
  decide +kernel

lemma initial_sums :
    (∑ c : Letter, u (initial c)) = 4 ∧
    (∑ c : Letter, v (initial c)) = 2 ∧
    (∑ c : Letter, w (initial c)) = -8 ∧
    (∑ c : Letter, z (initial c)) = -4 ∧
    (∑ c : Letter, y (initial c)) = 15 := by
  decide +kernel

lemma count_formula (n : ℕ) :
    count (n + 2) = fun s =>
      u s + (n : ℤ) * v s + 2 ^ n * (w s + (n : ℤ) * z s) + 3 ^ n * y s := by
  induction n with
  | zero =>
    funext s
    simpa using certificate_base s
  | succ n ih =>
    change advance (count (n + 2)) = _
    rw [ih]
    simp only [advance_add, advance_mul]
    funext s
    simp only [certificate_u, certificate_v, certificate_w, certificate_z, certificate_y,
      Nat.cast_add, Nat.cast_one, pow_succ]
    ring

lemma initial_formula_shift (n : ℕ) :
    (∑ c : Letter, count (n + 2) (initial c)) =
      5 * (3 : ℤ) ^ (n + 1) - ((2 : ℤ) ^ (n + 2) - 2) * (n + 2 : ℕ) := by
  rw [count_formula]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [initial_sums.1, initial_sums.2.1, initial_sums.2.2.1,
    initial_sums.2.2.2.1, initial_sums.2.2.2.2]
  simp only [pow_succ, Nat.cast_add, Nat.cast_ofNat]
  ring

lemma initial_formula (n : ℕ) (hn : 1 < n) :
    (∑ c : Letter, count n (initial c)) =
      5 * (3 : ℤ) ^ (n - 1) - ((2 : ℤ) ^ n - 2) * n := by
  have he : n = (n - 2) + 2 := by omega
  conv_lhs => rw [he]
  rw [initial_formula_shift]
  have hex : n - 2 + 1 = n - 1 := by omega
  rw [hex, ← he]

lemma card_accepted_formula (n : ℕ) (hn : 1 < n) :
    (Nat.card {w : Fin (n + 1) → Letter // Accepted w} : ℤ) =
      5 * (3 : ℤ) ^ (n - 1) - ((2 : ℤ) ^ n - 2) * n := by
  rw [card_accepted]
  exact initial_formula n hn

lemma initial_zero : (∑ c : Letter, count 0 (initial c)) = 3 := by decide +kernel
lemma initial_one : (∑ c : Letter, count 1 (initial c)) = 3 := by decide +kernel

end A250271Count

-- Component: A250271Finish

namespace A250271Finish

open OMA.S_oeis_a250271 PowerSeries

lemma count_formula (n : ℕ) (hn : 1 < n) :
    (a n : ℤ) = 5 * 3 ^ (n - 1) - (2 ^ n - 2) * n := by
  rw [A250271Machine.count_eq]
  exact A250271Count.card_accepted_formula n hn

lemma count_one : a 1 = 3 := by
  have h : (a 1 : ℤ) = 3 := by
    rw [A250271Machine.count_eq, A250271Count.card_accepted]
    exact A250271Count.initial_one
  exact_mod_cast h

def value : ℕ → ℚ
  | 0 => 0
  | 1 => 3
  | n + 2 => 15 * 3 ^ n - (4 * 2 ^ n - 2) * (n + 2 : ℕ)

lemma coefficient_eq (n : ℕ) :
    (if n = 0 then (0 : ℚ) else (a n : ℚ)) = value n := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => simp [value, count_one]
    | succ n =>
      simp only [Nat.succ_ne_zero, if_false]
      have hz := count_formula (n + 2) (by omega)
      have he : n + 2 - 1 = n + 1 := by omega
      rw [he] at hz
      have hq : (a (n + 2) : ℚ) =
          5 * (3 : ℚ) ^ (n + 1) - ((2 : ℚ) ^ (n + 2) - 2) * (n + 2 : ℕ) := by
        exact_mod_cast hz
      change (a (n + 2) : ℚ) = value (n + 2)
      rw [hq]
      simp only [value, pow_succ, Nat.cast_add, Nat.cast_ofNat]
      ring

lemma recurrence (n : ℕ) (hn : 6 < n) :
    value n - 9 * value (n - 1) + 31 * value (n - 2) -
      51 * value (n - 3) + 40 * value (n - 4) - 12 * value (n - 5) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 7 := ⟨n - 7, by omega⟩
  have h1 : k + 7 - 1 = k + 6 := by omega
  have h2 : k + 7 - 2 = k + 5 := by omega
  have h3 : k + 7 - 3 = k + 4 := by omega
  have h4 : k + 7 - 4 = k + 3 := by omega
  have h5 : k + 7 - 5 = k + 2 := by omega
  rw [h1, h2, h3, h4, h5]
  norm_num [value, pow_add, Nat.cast_add]
  ring

lemma coeff_mk_mul_monomial (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then f (n - k) * c else 0 := by
  rw [← mul_assoc, coeff_mul_X_pow']
  split_ifs with h
  · rw [coeff_mul_C, coeff_mk]
  · rfl

lemma denominator_expansion :
    ((1 - X) ^ 2 * (1 - 2 * X) ^ 2 * (1 - 3 * X) : PowerSeries ℚ) =
      C 1 * X ^ 0 + C (-9) * X ^ 1 + C 31 * X ^ 2 + C (-51) * X ^ 3 +
        C 40 * X ^ 4 + C (-12) * X ^ 5 := by
  simp only [map_one, map_neg, map_ofNat]
  ring

lemma numerator_expansion :
    (X * (3 - 16 * X + 21 * X ^ 2 + 24 * X ^ 3 - 60 * X ^ 4 + 24 * X ^ 5) :
      PowerSeries ℚ) =
      C 3 * X ^ 1 + C (-16) * X ^ 2 + C 21 * X ^ 3 + C 24 * X ^ 4 +
        C (-60) * X ^ 5 + C 24 * X ^ 6 := by
  simp only [map_neg, map_ofNat]
  ring

lemma generating_function :
    mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - X) ^ 2 * (1 - 2 * X) ^ 2 * (1 - 3 * X)) =
      X * (3 - 16 * X + 21 * X ^ 2 + 24 * X ^ 3 - 60 * X ^ 4 + 24 * X ^ 5) := by
  simp_rw [coefficient_eq]
  rw [denominator_expansion, numerator_expansion]
  ext n
  simp only [mul_add, map_add, coeff_mk_mul_monomial, coeff_C_mul_X_pow]
  by_cases hn : 6 < n
  · have hr := recurrence n hn
    simp (disch := omega) only [if_pos, if_neg]
    simp only [Nat.sub_zero]
    linarith
  · interval_cases n <;> norm_num [value]

end A250271Finish

theorem OMA.solution : type_of% @OMA.S_oeis_a250271.main := by
  exact ⟨A250271Finish.generating_function, A250271Finish.count_formula⟩
