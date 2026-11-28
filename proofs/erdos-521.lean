import OMAStatements.S_erdos_521
import Mathlib

/-!
# Erdős Problem 521 is false (original proof)

Almost surely, `R_n / log n` does NOT converge to `2/π`, where `R_n` counts the real roots (with
multiplicity) of `f_n = ∑_{k ≤ n} ε_k X^k` with i.i.d. uniform signs `ε_k`.

That the almost-sure statement fails is known; the argument formalized here is our own:
for odd `n = 2K-1`, condition on a "cone" event for the last `2K` coefficients read backwards in pairs
(a two-dimensional ±1 walk staying in the closed quadrant and ending at height `≥ λ = ⌈n^{39/80}⌉`),
of probability `≍ 1/K` (ballot/reflection counts and Wallis bounds). On that event Descartes' rule applied
to `f · D_N²` (`D_N = 1 + X + ⋯ + X^N`) bounds the positive roots by one plus the number of weak sign
changes of the forward two-fold sums `c_k`, `k < n - n^{19/20}` (Hoeffding controls the tail), and the
same for `f(-x)`. A sharp local estimate for the probability of a sign change of `(c_k, c_{k+1})`
(`≤ (√3/(2π) + o(1))/k`, Fourier inversion with explicit error terms), independence of disjoint coefficient
blocks and Markov give `μ(H_K) ≳ 1/K` for the event `H_K` where `R_n < 0.63 log n + 2`; a second-moment
(Kochen–Stone) argument with the pair bound `μ(H_K ∩ H_K') ≲ 1/(K(K'-K+1))` gives `μ(limsup H_K) > 0`,
contradicting a.s. convergence to `2/π > 0.635`.

Every step is formalized from scratch here (route brainstormed with Claude Fable and Gemini).
-/

-- ===== C1 =====
section S_C1

/-! Ballot counts in one and two dimensions (original). -/

open Finset

namespace E521

/-- Reflection-principle window: number of `±1` paths of length `h` started at height `u`
that stay `≥ 0`. -/
def Wn (h u : ℕ) : ℕ :=
  ∑ k ∈ range (h + 1), if h ≤ 2 * k + u ∧ 2 * k ≤ h + u + 1 then h.choose k else 0

lemma Wn_zero (u : ℕ) : Wn 0 u = 1 := by
  simp [Wn]

lemma Wn_succ (h u : ℕ) :
    Wn (h + 1) u = Wn h (u + 1) + (if u = 0 then 0 else Wn h (u - 1)) := by
  -- write both sides as sums over `range (h + 1)` against `h.choose j`
  have hL : Wn (h + 1) u = ∑ j ∈ range (h + 1),
      ((if h + 1 ≤ 2 * j + u ∧ 2 * j ≤ h + u + 2 then h.choose j else 0) +
       (if h ≤ 2 * j + u + 1 ∧ 2 * j ≤ h + u then h.choose j else 0)) := by
    unfold Wn
    rw [sum_range_succ', Finset.sum_add_distrib]
    have e1 : ∀ k ∈ range (h + 1),
        (if h + 1 ≤ 2 * (k + 1) + u ∧ 2 * (k + 1) ≤ h + 1 + u + 1 then (h + 1).choose (k + 1) else 0)
        = (if h + 1 ≤ 2 * (k + 1) + u ∧ 2 * (k + 1) ≤ h + u + 2 then h.choose (k + 1) else 0)
          + (if h ≤ 2 * k + u + 1 ∧ 2 * k ≤ h + u then h.choose k else 0) := by
      intro k _
      rw [Nat.choose_succ_succ']
      by_cases c1 : h + 1 ≤ 2 * (k + 1) + u ∧ 2 * (k + 1) ≤ h + 1 + u + 1
      · rw [if_pos c1, if_pos (by omega), if_pos (by omega)]; ring
      · rw [if_neg c1, if_neg (by omega), if_neg (by omega)]
    rw [sum_congr rfl e1, Finset.sum_add_distrib]
    -- the `choose (k+1)` part: reindex to `j = k + 1`, add the `j = 0` term
    have e2 : (∑ k ∈ range (h + 1),
        (if h + 1 ≤ 2 * (k + 1) + u ∧ 2 * (k + 1) ≤ h + u + 2 then h.choose (k + 1) else 0)) +
        (if h + 1 ≤ 2 * 0 + u ∧ 2 * 0 ≤ h + 1 + u + 1 then (h + 1).choose 0 else 0) =
        ∑ j ∈ range (h + 1),
          (if h + 1 ≤ 2 * j + u ∧ 2 * j ≤ h + u + 2 then h.choose j else 0) := by
      have := sum_range_succ' (fun j =>
        (if h + 1 ≤ 2 * j + u ∧ 2 * j ≤ h + u + 2 then h.choose j else 0)) (h + 1)
      rw [sum_range_succ] at this
      have hz : (if h + 1 ≤ 2 * (h + 1) + u ∧ 2 * (h + 1) ≤ h + u + 2 then h.choose (h + 1) else 0)
          = 0 := by
        split_ifs <;> simp
      rw [hz, add_zero] at this
      rw [this]
      congr 1
      simp only [Nat.choose_zero_right]
      by_cases c : h + 1 ≤ u
      · rw [if_pos (by omega), if_pos (by omega)]
      · rw [if_neg (by omega), if_neg (by omega)]
    rw [← Finset.sum_add_distrib] at *
    rw [← e2, Finset.sum_add_distrib]
    ring
  rw [hL]
  have hR : Wn h (u + 1) + (if u = 0 then 0 else Wn h (u - 1)) = ∑ j ∈ range (h + 1),
      ((if h ≤ 2 * j + (u + 1) ∧ 2 * j ≤ h + (u + 1) + 1 then h.choose j else 0) +
       (if u = 0 then 0 else if h ≤ 2 * j + (u - 1) ∧ 2 * j ≤ h + (u - 1) + 1 then h.choose j else 0))
      := by
    rw [Finset.sum_add_distrib]
    unfold Wn
    congr 1
    by_cases hu : u = 0
    · simp [hu]
    · simp [hu]
  rw [hR]
  apply sum_congr rfl
  intro j _
  by_cases hu : u = 0
  · subst hu
    simp only [if_true]
    split_ifs <;> omega
  · rw [if_neg hu]
    split_ifs <;> omega

lemma Wn_zero_start (h : ℕ) : Wn h 0 = h.choose ((h + 1) / 2) := by
  unfold Wn
  rw [sum_eq_single ((h + 1) / 2)]
  · rw [if_pos (by omega)]
  · intro k _ hk
    rw [if_neg (by omega)]
  · intro hk
    exfalso; apply hk; rw [mem_range]; omega

/-! ### one-dimensional paths -/

/-- `±1` step of a coin. -/
def st (b : Bool) : ℤ := if b then 1 else -1

/-- a path of `L` steps started at `u` stays `≥ 0` (including the start). -/
def good1 : (L : ℕ) → ℤ → (Fin L → Bool) → Prop
  | 0, u, _ => 0 ≤ u
  | L + 1, u, p => 0 ≤ u ∧ good1 L (u + st (p 0)) (Fin.tail p)

instance good1_dec : ∀ (L : ℕ) (u : ℤ) (p : Fin L → Bool), Decidable (good1 L u p)
  | 0, u, _ => by unfold good1; infer_instance
  | L + 1, u, p => by
    unfold good1
    haveI := good1_dec L (u + st (p 0)) (Fin.tail p)
    infer_instance

def N1 (L : ℕ) (u : ℤ) : ℕ := (univ.filter (fun p : Fin L → Bool => good1 L u p)).card

lemma N1_neg (L : ℕ) {u : ℤ} (hu : u < 0) : N1 L u = 0 := by
  unfold N1
  rw [card_eq_zero, filter_eq_empty_iff]
  intro p _
  cases L with
  | zero => simp only [good1]; omega
  | succ L => simp only [good1]; omega

/-- sum over sequences by the first coordinate. -/
lemma sum_cons {α : Type*} [Fintype α] {L : ℕ} (f : (Fin (L + 1) → α) → ℕ) :
    ∑ p, f p = ∑ a : α, ∑ q : Fin L → α, f (Fin.cons a q) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => α)) _ _ (fun _ => rfl)).symm

lemma card_filter_eq_sum {β : Type*} [Fintype β] (P : β → Prop) [DecidablePred P] :
    (univ.filter P).card = ∑ x, if P x then 1 else 0 := by
  rw [card_filter]

lemma N1_succ (L : ℕ) {u : ℤ} (hu : 0 ≤ u) : N1 (L + 1) u = N1 L (u + 1) + N1 L (u - 1) := by
  unfold N1
  rw [card_filter_eq_sum, card_filter_eq_sum, card_filter_eq_sum, sum_cons]
  simp only [Fintype.univ_bool, mem_insert, mem_singleton, Bool.true_eq_false, not_false_eq_true,
    sum_insert, sum_singleton]
  congr 1
  · apply Fintype.sum_congr; intro q
    simp only [good1, Fin.cons_zero, Fin.tail_cons, st, if_true]
    by_cases h : good1 L (u + 1) q
    · rw [if_pos ⟨hu, h⟩, if_pos h]
    · rw [if_neg (fun h' => h h'.2), if_neg h]
  · apply Fintype.sum_congr; intro q
    simp only [good1, Fin.cons_zero, Fin.tail_cons, st]
    have e : u + (if false = true then (1 : ℤ) else -1) = u - 1 := by simp; ring
    rw [e]
    by_cases h : good1 L (u - 1) q
    · rw [if_pos ⟨hu, h⟩, if_pos h]
    · rw [if_neg (fun h' => h h'.2), if_neg h]

lemma N1_eq_Wn (L : ℕ) : ∀ u : ℕ, N1 L u = Wn L u := by
  induction L with
  | zero =>
    intro u
    unfold N1
    rw [Wn_zero, card_eq_one]
    refine ⟨default, ?_⟩
    ext p
    have hp : p = default := Subsingleton.elim _ _
    simp only [mem_filter, mem_univ, true_and, mem_singleton, good1]
    refine ⟨fun _ => hp, fun _ => ?_⟩
    exact Finset.mem_filter.mpr ⟨mem_univ _, show (0:ℤ) ≤ (u:ℤ) by positivity⟩
  | succ L ih =>
    intro u
    rw [N1_succ L (by positivity), Wn_succ]
    have h1 : ((u : ℤ) + 1) = ((u + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h1, ih]
    congr 1
    by_cases hu : u = 0
    · subst hu; rw [if_pos rfl]; exact N1_neg L (by norm_num)
    · rw [if_neg hu]
      have h2 : ((u : ℤ) - 1) = ((u - 1 : ℕ) : ℤ) := by omega
      rw [h2, ih]

/-! ### two-dimensional axis walk -/

/-- a pair of coins `(a, b)`: if `a = b` the walk moves horizontally by `st a`,
otherwise vertically by `st a`. -/
def dU (s : Bool × Bool) : ℤ := if s.1 = s.2 then st s.1 else 0
def dV (s : Bool × Bool) : ℤ := if s.1 = s.2 then 0 else st s.1

def good2 : (L : ℕ) → ℤ → ℤ → (Fin L → Bool × Bool) → Prop
  | 0, u, v, _ => 0 ≤ u ∧ 0 ≤ v
  | L + 1, u, v, p => 0 ≤ u ∧ 0 ≤ v ∧ good2 L (u + dU (p 0)) (v + dV (p 0)) (Fin.tail p)

instance good2_dec : ∀ (L : ℕ) (u v : ℤ) (p : Fin L → Bool × Bool), Decidable (good2 L u v p)
  | 0, u, v, _ => by unfold good2; infer_instance
  | L + 1, u, v, p => by
    unfold good2
    haveI := good2_dec L (u + dU (p 0)) (v + dV (p 0)) (Fin.tail p)
    infer_instance

def N2 (L : ℕ) (u v : ℤ) : ℕ := (univ.filter (fun p : Fin L → Bool × Bool => good2 L u v p)).card

lemma N2_succ (L : ℕ) {u v : ℤ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    N2 (L + 1) u v = N2 L (u + 1) v + N2 L (u - 1) v + N2 L u (v + 1) + N2 L u (v - 1) := by
  unfold N2
  simp only [card_filter_eq_sum]
  rw [sum_cons]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.univ_bool, mem_insert, mem_singleton, Bool.true_eq_false, not_false_eq_true,
    sum_insert, sum_singleton]
  have key : ∀ (a b : Bool) (q : Fin L → Bool × Bool),
      (if good2 (L + 1) u v (Fin.cons (a, b) q) then 1 else 0) =
      (if good2 L (u + dU (a, b)) (v + dV (a, b)) q then 1 else 0) := by
    intro a b q
    simp only [good2, Fin.cons_zero, Fin.tail_cons]
    by_cases h : good2 L (u + dU (a, b)) (v + dV (a, b)) q
    · rw [if_pos ⟨hu, hv, h⟩, if_pos h]
    · rw [if_neg (fun h' => h h'.2.2), if_neg h]
  simp only [key, dU, dV, st]
  simp only [if_true, Bool.true_eq_false, if_false, Bool.false_eq_true, add_zero]
  have e : u + -1 = u - 1 := by ring
  have e' : v + -1 = v - 1 := by ring
  rw [e, e']
  ring

lemma N2_neg {L : ℕ} {u v : ℤ} (h : u < 0 ∨ v < 0) : N2 L u v = 0 := by
  unfold N2
  rw [card_eq_zero, filter_eq_empty_iff]
  intro p _
  cases L with
  | zero => simp only [good2]; omega
  | succ L => simp only [good2]; omega

/-- product formula: the axis walk is a binomial interleaving of two independent 1D walks. -/
theorem N2_eq (L : ℕ) : ∀ u v : ℤ,
    N2 L u v = ∑ h ∈ range (L + 1), L.choose h * (N1 h u * N1 (L - h) v) := by
  induction L with
  | zero =>
    intro u v
    simp only [zero_add, range_one, sum_singleton, Nat.choose_self, Nat.sub_self, one_mul]
    unfold N2 N1
    by_cases hu : 0 ≤ u
    · by_cases hv : 0 ≤ v
      · have e1 : (univ.filter (fun p : Fin 0 → Bool × Bool => good2 0 u v p)) = univ := by
          ext p; simp [good2, hu, hv]
        have e2 : (univ.filter (fun p : Fin 0 → Bool => good1 0 u p)) = univ := by
          ext p; simp [good1, hu]
        have e3 : (univ.filter (fun p : Fin 0 → Bool => good1 0 v p)) = univ := by
          ext p; simp [good1, hv]
        rw [e1, e2, e3]; simp
      · have := N2_neg (L := 0) (u := u) (v := v) (Or.inr (by omega))
        unfold N2 at this; rw [this]
        have := N1_neg 0 (u := v) (by omega)
        unfold N1 at this; rw [this]; simp
    · have := N2_neg (L := 0) (u := u) (v := v) (Or.inl (by omega))
      unfold N2 at this; rw [this]
      have := N1_neg 0 (u := u) (by omega)
      unfold N1 at this; rw [this]; simp
  | succ L ih =>
    intro u v
    by_cases huv : 0 ≤ u ∧ 0 ≤ v
    · rw [N2_succ L huv.1 huv.2, ih, ih, ih, ih]
      -- 1D recursions
      have r1 : ∀ h, N1 h (u + 1) + N1 h (u - 1) = N1 (h + 1) u := fun h =>
        (N1_succ h huv.1).symm
      have r2 : ∀ h, N1 h (v + 1) + N1 h (v - 1) = N1 (h + 1) v := fun h =>
        (N1_succ h huv.2).symm
      have A : (∑ h ∈ range (L + 1), L.choose h * (N1 h (u + 1) * N1 (L - h) v)) +
          (∑ h ∈ range (L + 1), L.choose h * (N1 h (u - 1) * N1 (L - h) v)) =
          ∑ h ∈ range (L + 1), L.choose h * (N1 (h + 1) u * N1 (L - h) v) := by
        rw [← sum_add_distrib]; apply sum_congr rfl; intro h _; rw [← r1]; ring
      have B : (∑ h ∈ range (L + 1), L.choose h * (N1 h u * N1 (L - h) (v + 1))) +
          (∑ h ∈ range (L + 1), L.choose h * (N1 h u * N1 (L - h) (v - 1))) =
          ∑ h ∈ range (L + 1), L.choose h * (N1 h u * N1 (L - h + 1) v) := by
        rw [← sum_add_distrib]; apply sum_congr rfl; intro h _; rw [← r2]; ring
      rw [A, add_assoc, B]
      -- Pascal on the right
      rw [sum_range_succ' _ (L + 1)]
      simp only [Nat.choose_succ_succ', add_mul, sum_add_distrib]
      rw [sum_range_succ (fun h => L.choose (h + 1) * (N1 (h + 1) u * N1 (L + 1 - (h + 1)) v)) L]
      simp only [Nat.choose_succ_self, zero_mul, add_zero, Nat.choose_zero_right, one_mul,
        Nat.sub_zero]
      have C1 : ∑ h ∈ range (L + 1), L.choose h * (N1 (h + 1) u * N1 (L + 1 - (h + 1)) v) =
          ∑ h ∈ range (L + 1), L.choose h * (N1 (h + 1) u * N1 (L - h) v) := by
        apply sum_congr rfl; intro h _; congr 3; omega
      have C2 : ∑ h ∈ range L, L.choose (h + 1) * (N1 (h + 1) u * N1 (L + 1 - (h + 1)) v) +
          N1 0 u * N1 (L + 1) v =
          ∑ h ∈ range (L + 1), L.choose h * (N1 h u * N1 (L - h + 1) v) := by
        rw [sum_range_succ' (fun h => L.choose h * (N1 h u * N1 (L - h + 1) v))]
        simp only [Nat.choose_zero_right, one_mul, Nat.sub_zero]
        congr 1
        apply sum_congr rfl; intro h hh; rw [mem_range] at hh; congr 3; omega
      rw [C1, ← C2]; ring
    · rw [N2_neg (by omega)]
      symm
      apply sum_eq_zero
      intro h _
      rcases not_and_or.mp huv with hu | hv
      · rw [N1_neg h (by omega)]; ring
      · rw [N1_neg (L + 1 - h) (by omega)]; ring

/-- total number of axis walks of length `L` from the origin staying in the closed quadrant. -/
theorem N2_origin (L : ℕ) : N2 L 0 0 =
    ∑ h ∈ range (L + 1), L.choose h * (h.choose ((h + 1) / 2) * (L - h).choose ((L - h + 1) / 2)) := by
  rw [N2_eq]
  apply sum_congr rfl
  intro h _
  have e1 := N1_eq_Wn h 0
  have e2 := N1_eq_Wn (L - h) 0
  simp only [Nat.cast_zero] at e1 e2
  rw [e1, e2, Wn_zero_start, Wn_zero_start]

end E521

end S_C1

-- ===== C2 =====
section S_C2

/-! Two-sided bounds for the quadrant count `N2 L 0 0` (original). -/

open Finset

namespace E521

lemma cb_sq (p : ℕ) : (Nat.centralBinom p : ℝ) ^ 2 * (2 * p + 1) ≤ 16 ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
    have h := Nat.succ_mul_centralBinom_succ p
    have hc : (Nat.centralBinom (p + 1) : ℝ) = 2 * (2 * p + 1) * Nat.centralBinom p / (p + 1) := by
      rw [eq_div_iff (by positivity)]
      have : ((p + 1 : ℕ) : ℝ) * Nat.centralBinom (p + 1) = 2 * (2 * p + 1) * Nat.centralBinom p := by
        exact_mod_cast h
      push_cast at this; linarith
    rw [hc, div_pow, div_mul_eq_mul_div]
    have hp : (0 : ℝ) < ((p : ℝ) + 1) ^ 2 := by positivity
    rw [div_le_iff₀ hp]
    have key : (2 * (p : ℝ) + 1) * (2 * ((p : ℝ) + 1) + 1) ≤ 4 * ((p : ℝ) + 1) ^ 2 := by nlinarith
    have e1 : (2 * (2 * (p : ℝ) + 1) * (Nat.centralBinom p : ℝ)) ^ 2 * (2 * ((p : ℝ) + 1) + 1)
        = 4 * (((Nat.centralBinom p : ℝ)) ^ 2 * (2 * p + 1)) * ((2 * p + 1) * (2 * ((p : ℝ) + 1) + 1)) := by
      ring
    push_cast
    rw [e1]
    have := mul_le_mul ih key (by positivity) (by positivity)
    calc 4 * (((Nat.centralBinom p : ℝ)) ^ 2 * (2 * p + 1)) * ((2 * p + 1) * (2 * ((p : ℝ) + 1) + 1))
        = 4 * ((((Nat.centralBinom p : ℝ)) ^ 2 * (2 * p + 1)) * ((2 * p + 1) * (2 * ((p : ℝ) + 1) + 1))) := by ring
      _ ≤ 4 * (16 ^ p * (4 * ((p : ℝ) + 1) ^ 2)) := by linarith
      _ = 16 ^ (p + 1) * ((p : ℝ) + 1) ^ 2 := by rw [pow_succ]; ring

/-- lower bound `16^p ≤ 4 p c_p^2` for `p ≥ 1`. -/
lemma cb_sq_low (p : ℕ) (hp : 1 ≤ p) : (16 : ℝ) ^ p ≤ 4 * p * (Nat.centralBinom p : ℝ) ^ 2 := by
  induction p, hp using Nat.le_induction with
  | base => rw [show Nat.centralBinom 1 = 2 by rfl]; norm_num
  | succ p hp ih =>
    have h := Nat.succ_mul_centralBinom_succ p
    have hc : (Nat.centralBinom (p + 1) : ℝ) = 2 * (2 * p + 1) * Nat.centralBinom p / (p + 1) := by
      rw [eq_div_iff (by positivity)]
      have : ((p + 1 : ℕ) : ℝ) * Nat.centralBinom (p + 1) = 2 * (2 * p + 1) * Nat.centralBinom p := by
        exact_mod_cast h
      push_cast at this; linarith
    rw [hc]
    have hp1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
    have e : 4 * ((p + 1 : ℕ) : ℝ) * (2 * (2 * p + 1) * Nat.centralBinom p / (p + 1)) ^ 2
        = 16 * (2 * (p : ℝ) + 1) ^ 2 / (p + 1) * (Nat.centralBinom p : ℝ) ^ 2 := by
      push_cast; field_simp; ring
    rw [e, pow_succ]
    have key : 4 * (p : ℝ) ≤ (2 * (p : ℝ) + 1) ^ 2 / (p + 1) * (p : ℝ)⁻¹ * (p:ℝ) * (p + 1) / (p + 1) := by
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
      rw [mul_assoc ((2 * (p : ℝ) + 1) ^ 2 / (p + 1)), inv_mul_cancel₀ hp0.ne', mul_one,
        mul_div_assoc, div_self hp1.ne', mul_one, le_div_iff₀ hp1]
      nlinarith
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
    have hc0 : (0 : ℝ) ≤ (Nat.centralBinom p : ℝ) ^ 2 := by positivity
    have : (2 * (p : ℝ) + 1) ^ 2 / (p + 1) ≥ 4 * p := by
      rw [ge_iff_le, le_div_iff₀ hp1]; nlinarith
    calc (16 : ℝ) ^ p * 16 ≤ (4 * p * (Nat.centralBinom p : ℝ) ^ 2) * 16 := by linarith
      _ ≤ 16 * (2 * (p : ℝ) + 1) ^ 2 / (p + 1) * (Nat.centralBinom p : ℝ) ^ 2 := by
        rw [mul_div_assoc]; nlinarith

/-- `C(h, ⌈h/2⌉)` -/
def cc (h : ℕ) : ℕ := h.choose ((h + 1) / 2)

lemma cc_odd (p : ℕ) : (cc (2 * p + 1) : ℝ) = Nat.centralBinom (p + 1) / 2 := by
  unfold cc
  have h2 : (2 * p + 1 + 1) / 2 = p + 1 := by omega
  rw [h2]
  have hsum : Nat.centralBinom (p + 1) = 2 * (2 * p + 1).choose (p + 1) := by
    rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (p + 1) = (2 * p + 1) + 1 by ring,
      Nat.choose_succ_succ, Nat.choose_symm_of_eq_add (show 2 * p + 1 = (p + 1) + p by omega)]
    ring
  rw [hsum]; push_cast; ring

lemma cc_even (p : ℕ) : (cc (2 * p) : ℝ) = Nat.centralBinom p := by
  unfold cc
  have h2 : (2 * p + 1) / 2 = p := by omega
  rw [h2, Nat.centralBinom_eq_two_mul_choose]

lemma cc_upper (h : ℕ) : (cc h : ℝ) ^ 2 * (h + 1) ≤ 4 ^ h := by
  obtain ⟨p, rfl | rfl⟩ := Nat.even_or_odd' h
  · rw [cc_even]
    have := cb_sq p
    have h16 : (4 : ℝ) ^ (2 * p) = 16 ^ p := by rw [pow_mul]; norm_num
    rw [h16]; push_cast; linarith
  · rw [cc_odd]
    have := cb_sq (p + 1)
    have h16 : (4 : ℝ) ^ (2 * p + 1) = 16 ^ (p + 1) / 4 := by
      rw [pow_succ, pow_mul, pow_succ]; ring
    rw [h16]; push_cast at this ⊢
    have : (0 : ℝ) ≤ (Nat.centralBinom (p + 1) : ℝ) ^ 2 := by positivity
    nlinarith

lemma cc_lower (h : ℕ) : (4 : ℝ) ^ h ≤ 2 * (h + 1) * (cc h : ℝ) ^ 2 := by
  obtain ⟨p, rfl | rfl⟩ := Nat.even_or_odd' h
  · rw [cc_even]
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp; simp
    · have := cb_sq_low p hp
      have h16 : (4 : ℝ) ^ (2 * p) = 16 ^ p := by rw [pow_mul]; norm_num
      rw [h16]; push_cast
      have : (0 : ℝ) ≤ (Nat.centralBinom p : ℝ) ^ 2 := by positivity
      nlinarith
  · rw [cc_odd]
    have := cb_sq_low (p + 1) (by omega)
    have h16 : (4 : ℝ) ^ (2 * p + 1) = 16 ^ (p + 1) / 4 := by
      rw [pow_succ, pow_mul, pow_succ]; ring
    rw [h16]; push_cast at this ⊢
    nlinarith

lemma N2_origin' (L : ℕ) : (N2 L 0 0 : ℝ) =
    ∑ h ∈ range (L + 1), (L.choose h : ℝ) * ((cc h : ℝ) * (cc (L - h) : ℝ)) := by
  rw [N2_origin]; push_cast; rfl

theorem N2_lower (L : ℕ) : (4 : ℝ) ^ L / (L + 2) ≤ N2 L 0 0 := by
  rw [N2_origin']
  have hL : (0 : ℝ) < L + 2 := by positivity
  have each : ∀ h ∈ range (L + 1), (L.choose h : ℝ) * (2 ^ L / (L + 2)) ≤
      (L.choose h : ℝ) * ((cc h : ℝ) * (cc (L - h) : ℝ)) := by
    intro h hh
    rw [mem_range] at hh
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have a := cc_lower h
    have b := cc_lower (L - h)
    have hLh : ((L - h : ℕ) : ℝ) = L - h := by rw [Nat.cast_sub (by omega)]
    rw [hLh] at b
    set x := (cc h : ℝ)
    set y := (cc (L - h) : ℝ)
    have hx : 0 ≤ x := by positivity
    have hy : 0 ≤ y := by positivity
    -- (x y)^2 ≥ 4^L / (4 (h+1)(L-h+1)) ≥ 4^L/(L+2)^2
    have h4 : (4 : ℝ) ^ L = 4 ^ h * 4 ^ (L - h) := by rw [← pow_add]; congr 1; omega
    have hh0 : (0 : ℝ) ≤ h := by positivity
    have hh1 : (h : ℝ) ≤ L := by exact_mod_cast (by omega : h ≤ L)
    have prod : (4 : ℝ) ^ L ≤ (L + 2) ^ 2 * (x * y) ^ 2 := by
      have amgm : 4 * ((h : ℝ) + 1) * (L - h + 1) ≤ (L + 2) ^ 2 := by
        nlinarith [sq_nonneg (((h : ℝ) + 1) - (L - h + 1))]
      have := mul_le_mul a b (by positivity) (by positivity)
      rw [h4]
      calc (4 : ℝ) ^ h * 4 ^ (L - h) ≤ 2 * (h + 1) * x ^ 2 * (2 * ((L : ℝ) - h + 1) * y ^ 2) := this
        _ = (4 * ((h : ℝ) + 1) * (L - h + 1)) * (x * y) ^ 2 := by ring
        _ ≤ (L + 2) ^ 2 * (x * y) ^ 2 := by
          apply mul_le_mul_of_nonneg_right amgm (by positivity)
    have h2 : ((2 : ℝ) ^ L) ^ 2 = 4 ^ L := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [div_le_iff₀ hL]
    have hxy : 0 ≤ x * y * (L + 2) := by positivity
    have : ((2 : ℝ) ^ L) ^ 2 ≤ (x * y * (L + 2)) ^ 2 := by rw [h2]; nlinarith
    have := (pow_le_pow_iff_left₀ (by positivity) hxy two_ne_zero).mp this
    linarith
  have := sum_le_sum each
  rw [← sum_mul] at this
  have hs : ∑ h ∈ range (L + 1), (L.choose h : ℝ) = 2 ^ L := by
    exact_mod_cast Nat.sum_range_choose L
  rw [hs] at this
  calc (4 : ℝ) ^ L / (L + 2) = 2 ^ L * (2 ^ L / (L + 2)) := by
        rw [show (4 : ℝ) ^ L = 2 ^ L * 2 ^ L by rw [← mul_pow]; norm_num]; ring
    _ ≤ _ := this

/-- `∑ C(L,h)/(h+1) ≤ 2^(L+1)/(L+1)`. -/
lemma sum_choose_div (L : ℕ) :
    ∑ h ∈ range (L + 1), (L.choose h : ℝ) / (h + 1) ≤ 2 ^ (L + 1) / (L + 1) := by
  have e : ∀ h ∈ range (L + 1), (L.choose h : ℝ) / (h + 1) = ((L + 1).choose (h + 1) : ℝ) / (L + 1) := by
    intro h _
    have := Nat.add_one_mul_choose_eq L h
    rw [div_eq_div_iff (by positivity) (by positivity)]
    have : ((L + 1 : ℕ) : ℝ) * (L.choose h : ℝ) = ((L + 1).choose (h + 1) : ℝ) * ((h + 1 : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at this; linarith
  rw [sum_congr rfl e, ← sum_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : ∑ h ∈ range (L + 1), ((L + 1).choose (h + 1) : ℝ) ≤ ∑ h ∈ range (L + 2), ((L + 1).choose h : ℝ) := by
    rw [sum_range_succ' (fun h => ((L + 1).choose h : ℝ))]
    simp
  calc _ ≤ _ := this
    _ = 2 ^ (L + 1) := by exact_mod_cast Nat.sum_range_choose (L + 1)

theorem N2_upper (L : ℕ) : (N2 L 0 0 : ℝ) ≤ 2 * 4 ^ L / (L + 1) := by
  rw [N2_origin']
  have each : ∀ h ∈ range (L + 1), (L.choose h : ℝ) * ((cc h : ℝ) * (cc (L - h) : ℝ)) ≤
      2 ^ L * ((L.choose h : ℝ) / (h + 1) + ((L.choose (L - h)) : ℝ) / ((L - h : ℕ) + 1)) / 2 := by
    intro h hh
    rw [mem_range] at hh
    have a := cc_upper h
    have b := cc_upper (L - h)
    set x := (cc h : ℝ)
    set y := (cc (L - h) : ℝ)
    set A := (h : ℝ) + 1
    set B := ((L - h : ℕ) : ℝ) + 1
    have hA : 0 < A := by positivity
    have hB : 0 < B := by positivity
    have hsym : (L.choose (L - h) : ℝ) = L.choose h := by rw [Nat.choose_symm (by omega)]
    rw [hsym]
    have h4 : (4 : ℝ) ^ L = 4 ^ h * 4 ^ (L - h) := by rw [← pow_add]; congr 1; omega
    have h2 : ((2 : ℝ) ^ L) ^ 2 = 4 ^ L := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    -- (x y)^2 A B ≤ 4^L, hence x y ≤ 2^L / sqrt(A B) ≤ 2^L (1/A + 1/B)/2
    have hxy2 : (x * y) ^ 2 * (A * B) ≤ ((2 : ℝ) ^ L) ^ 2 := by
      rw [h2, h4]
      have := mul_le_mul a b (by positivity) (by positivity)
      calc (x * y) ^ 2 * (A * B) = x ^ 2 * A * (y ^ 2 * B) := by ring
        _ ≤ _ := this
    have hx : 0 ≤ x := by positivity
    have hy : 0 ≤ y := by positivity
    have hc : (0 : ℝ) ≤ L.choose h := by positivity
    have key : x * y ≤ 2 ^ L * (1 / A + 1 / B) / 2 := by
      -- 2 xy ≤ 2^L (A+B)/(AB) since 2 sqrt(AB) ≤ A + B
      have hAB : 0 < A * B := by positivity
      have s1 : (x * y * (A * B)) ^ 2 ≤ ((2 : ℝ) ^ L) ^ 2 * (A * B) := by nlinarith
      have s2 : (2 * x * y * (A * B)) ^ 2 ≤ ((2 : ℝ) ^ L * (A + B)) ^ 2 := by
        have : 4 * (A * B) ≤ (A + B) ^ 2 := by nlinarith [sq_nonneg (A - B)]
        nlinarith
      have s3 : 2 * x * y * (A * B) ≤ (2 : ℝ) ^ L * (A + B) := by
        exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp s2
      rw [show (2 : ℝ) ^ L * (1 / A + 1 / B) / 2 = (2 : ℝ) ^ L * (A + B) / (2 * (A * B)) by
        field_simp; ring]
      rw [le_div_iff₀ (by positivity)]; linarith
    calc (L.choose h : ℝ) * (x * y) ≤ (L.choose h : ℝ) * (2 ^ L * (1 / A + 1 / B) / 2) :=
          mul_le_mul_of_nonneg_left key hc
      _ = _ := by ring
  have := sum_le_sum each
  rw [← sum_div, ← mul_sum, sum_add_distrib] at this
  have s1 := sum_choose_div L
  have s2 : ∑ h ∈ range (L + 1), ((L.choose (L - h)) : ℝ) / ((L - h : ℕ) + 1) =
      ∑ h ∈ range (L + 1), (L.choose h : ℝ) / (h + 1) := by
    exact sum_range_reflect (fun h => (L.choose h : ℝ) / (h + 1)) (L + 1)
  rw [s2] at this
  calc _ ≤ _ := this
    _ ≤ 2 ^ L * (2 ^ (L + 1) / (L + 1) + 2 ^ (L + 1) / (L + 1)) / 2 := by
        gcongr
    _ = 2 * 4 ^ L / (L + 1) := by
        rw [show (4 : ℝ) ^ L = 2 ^ L * 2 ^ L by rw [← mul_pow]; norm_num, pow_succ]; ring

end E521

end S_C2

-- ===== C3 =====
section S_C3

/-! Cylinder probabilities for the sign measure, read through backward pairs (original). -/

open Finset MeasureTheory
open scoped ENNReal

namespace E521

noncomputable def ν : Measure Bool := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure ν := by
  constructor
  simp [ν]
  rw [ENNReal.inv_two_add_inv_two]

lemma ν_singleton (b : Bool) : ν {b} = 2⁻¹ := by
  cases b <;> simp [ν]

noncomputable def μS : Measure (ℕ → Bool) := Measure.infinitePi (fun _ : ℕ => ν)

instance : IsProbabilityMeasure μS := by unfold μS; infer_instance

/-- the backward pairs of the first `2K` coordinates: pair `j` is `(ω (2K-1-2j), ω (2K-2-2j))`. -/
def Φ (K : ℕ) (ω : ℕ → Bool) : Fin K → Bool × Bool :=
  fun j => (ω (2 * K - 1 - 2 * j), ω (2 * K - 2 - 2 * j))

/-- the coordinate value forced by a pair pattern. -/
def bit (K : ℕ) (p : Fin K → Bool × Bool) (i : ℕ) : Bool :=
  if h : (2 * K - 1 - i) / 2 < K then
    (if (2 * K - 1 - i) % 2 = 0 then (p ⟨(2 * K - 1 - i) / 2, h⟩).1
      else (p ⟨(2 * K - 1 - i) / 2, h⟩).2)
  else false

lemma Φ_preimage_singleton (K : ℕ) (p : Fin K → Bool × Bool) :
    Φ K ⁻¹' {p} = Set.pi (↑(range (2 * K))) (fun i => {bit K p i}) := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, coe_range, Set.mem_Iio]
  constructor
  · intro h i hi
    subst h
    unfold bit
    have hlt : (2 * K - 1 - i) / 2 < K := by omega
    rw [dif_pos hlt]
    split_ifs with hpar
    · simp only [Φ]; congr 1; omega
    · simp only [Φ]; congr 1; omega
  · intro h
    funext j
    have hj := j.isLt
    have h1 := h (2 * K - 1 - 2 * j) (by omega)
    have h2 := h (2 * K - 2 - 2 * j) (by omega)
    unfold bit at h1 h2
    have e1 : (2 * K - 1 - (2 * K - 1 - 2 * (j : ℕ))) / 2 = j := by omega
    have e2 : (2 * K - 1 - (2 * K - 2 - 2 * (j : ℕ))) / 2 = j := by omega
    rw [dif_pos (by omega)] at h1 h2
    have p1 : (2 * K - 1 - (2 * K - 1 - 2 * (j : ℕ))) % 2 = 0 := by omega
    have p2 : ¬ (2 * K - 1 - (2 * K - 2 - 2 * (j : ℕ))) % 2 = 0 := by omega
    rw [if_pos p1] at h1
    rw [if_neg p2] at h2
    have f1 : (⟨(2 * K - 1 - (2 * K - 1 - 2 * (j : ℕ))) / 2, by omega⟩ : Fin K) = j := Fin.ext e1
    have f2 : (⟨(2 * K - 1 - (2 * K - 2 - 2 * (j : ℕ))) / 2, by omega⟩ : Fin K) = j := Fin.ext e2
    rw [f1] at h1; rw [f2] at h2
    simp only [Φ]
    rw [h1, h2]

lemma measurableSet_Φ_singleton (K : ℕ) (p : Fin K → Bool × Bool) :
    MeasurableSet (Φ K ⁻¹' {p}) := by
  rw [Φ_preimage_singleton]
  exact MeasurableSet.pi (Finset.countable_toSet _) (fun i _ => measurableSet_singleton _)

lemma μS_Φ_singleton (K : ℕ) (p : Fin K → Bool × Bool) :
    μS (Φ K ⁻¹' {p}) = (4⁻¹ : ℝ≥0∞) ^ K := by
  rw [Φ_preimage_singleton, μS]
  have h := Measure.infinitePi_pi (μ := fun _ : ℕ => ν) (s := range (2 * K))
    (t := fun i => ({bit K p i} : Set Bool)) (fun i _ => measurableSet_singleton _)
  refine h.trans ?_
  simp only [ν_singleton, prod_const, card_range]
  rw [pow_mul]
  congr 1
  rw [← ENNReal.inv_pow]; norm_num

lemma μS_Φ (K : ℕ) (S : Finset (Fin K → Bool × Bool)) :
    μS (Φ K ⁻¹' (S : Set (Fin K → Bool × Bool))) = S.card * (4⁻¹ : ℝ≥0∞) ^ K := by
  have : Φ K ⁻¹' (S : Set (Fin K → Bool × Bool)) = ⋃ p ∈ S, Φ K ⁻¹' {p} := by
    ext ω; simp
  rw [this, measure_biUnion_finset]
  · simp only [μS_Φ_singleton, sum_const, nsmul_eq_mul]
  · intro p _ q _ hpq
    simp only [Function.onFun]
    rw [Set.disjoint_iff]
    intro ω ⟨h1, h2⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
    exact hpq (h1.symm.trans h2)
  · intro p _; exact measurableSet_Φ_singleton K p

lemma μS_Φ_real (K : ℕ) (S : Finset (Fin K → Bool × Bool)) :
    μS.real (Φ K ⁻¹' (S : Set (Fin K → Bool × Bool))) = S.card / 4 ^ K := by
  rw [Measure.real, μS_Φ, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]
  simp [div_eq_mul_inv]

lemma measurableSet_Φ (K : ℕ) (S : Set (Fin K → Bool × Bool)) : MeasurableSet (Φ K ⁻¹' S) := by
  have : Φ K ⁻¹' S = ⋃ p ∈ (Set.toFinite S).toFinset, Φ K ⁻¹' {p} := by
    ext ω; simp
  rw [this]
  exact Finset.measurableSet_biUnion _ (fun p _ => measurableSet_Φ_singleton K p)

/-! ### the pair sequence of a pattern and its partial sums -/

/-- `a_i`: the `i`-th reversed coefficient read from the pairs. -/
def aS {K : ℕ} (p : Fin K → Bool × Bool) (i : ℕ) : ℤ :=
  if h : i / 2 < K then (if i % 2 = 0 then st (p ⟨i / 2, h⟩).1 else st (p ⟨i / 2, h⟩).2) else 0

def Tk {K : ℕ} (p : Fin K → Bool × Bool) (k : ℕ) : ℤ := ∑ i ∈ range k, aS p i
def Ak {K : ℕ} (p : Fin K → Bool × Bool) (k : ℕ) : ℤ := ∑ i ∈ range k, (-1) ^ i * aS p i

/-- the cone condition on `K` backward pairs. -/
def coneP (K : ℕ) (p : Fin K → Bool × Bool) : Prop :=
  (∀ k ≤ 2 * K, 0 ≤ Tk p k ∧ 0 ≤ Ak p k) ∧ 0 < Tk p (2 * K) ∧ 0 < Ak p (2 * K)

/-- the weak (closed-quadrant) condition on the first `L` pairs. -/
def weakP (L : ℕ) (q : Fin L → Bool × Bool) : Prop := ∀ k ≤ 2 * L, 0 ≤ Tk q k ∧ 0 ≤ Ak q k

instance (K : ℕ) : DecidablePred (coneP K) := fun _ => by unfold coneP; infer_instance
instance (L : ℕ) : DecidablePred (weakP L) := fun _ => by unfold weakP; infer_instance

lemma aS_Φ (K : ℕ) (ω : ℕ → Bool) (i : ℕ) (hi : i < 2 * K) :
    aS (Φ K ω) i = st (ω (2 * K - 1 - i)) := by
  unfold aS
  rw [dif_pos (by omega)]
  split_ifs with h
  · simp only [Φ]; congr 2; omega
  · simp only [Φ]; congr 2; omega

/-- unit partial sums of the axis walk. -/
def Uc {L : ℕ} (q : Fin L → Bool × Bool) (j : ℕ) : ℤ :=
  ∑ i ∈ range j, if h : i < L then dU (q ⟨i, h⟩) else 0
def Vc {L : ℕ} (q : Fin L → Bool × Bool) (j : ℕ) : ℤ :=
  ∑ i ∈ range j, if h : i < L then dV (q ⟨i, h⟩) else 0

lemma st_sq (b : Bool) : st b * st b = 1 := by cases b <;> simp [st]

lemma aS_even {L : ℕ} (q : Fin L → Bool × Bool) (j : ℕ) (hj : j < L) :
    aS q (2 * j) = st (q ⟨j, hj⟩).1 := by
  unfold aS
  have hlt : 2 * j / 2 < L := by omega
  rw [dif_pos hlt, if_pos (by omega)]
  have : (⟨2 * j / 2, hlt⟩ : Fin L) = ⟨j, hj⟩ := Fin.ext (by simp only []; omega)
  rw [this]

lemma aS_odd {L : ℕ} (q : Fin L → Bool × Bool) (j : ℕ) (hj : j < L) :
    aS q (2 * j + 1) = st (q ⟨j, hj⟩).2 := by
  unfold aS
  have hlt : (2 * j + 1) / 2 < L := by omega
  rw [dif_pos hlt, if_neg (by omega)]
  have : (⟨(2 * j + 1) / 2, hlt⟩ : Fin L) = ⟨j, hj⟩ := Fin.ext (by simp only []; omega)
  rw [this]

lemma Tk_even {L : ℕ} (q : Fin L → Bool × Bool) (j : ℕ) (hj : j ≤ L) :
    Tk q (2 * j) = 2 * Uc q j ∧ Ak q (2 * j) = 2 * Vc q j := by
  induction j with
  | zero => simp [Tk, Ak, Uc, Vc]
  | succ j ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hjL : j < L := by omega
    unfold Tk Ak at *
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      sum_range_succ, sum_range_succ, ih1, ih2]
    unfold Uc Vc
    rw [sum_range_succ, sum_range_succ, dif_pos hjL, dif_pos hjL]
    rw [aS_even q j hjL, aS_odd q j hjL]
    have s1 : ((-1 : ℤ) ^ (2 * j)) = 1 := by rw [pow_mul]; norm_num
    have s2 : ((-1 : ℤ) ^ (2 * j + 1)) = -1 := by rw [pow_succ, s1]; norm_num
    rw [s1, s2]
    constructor
    · rcases q ⟨j, hjL⟩ with ⟨a, b⟩
      cases a <;> cases b <;> simp [dU, st] <;> ring
    · rcases q ⟨j, hjL⟩ with ⟨a, b⟩
      cases a <;> cases b <;> simp [dV, st] <;> ring

lemma Tk_odd {L : ℕ} (q : Fin L → Bool × Bool) (j : ℕ) (hj : j < L) :
    Tk q (2 * j + 1) = Tk q (2 * j) + st (q ⟨j, hj⟩).1 ∧
    Ak q (2 * j + 1) = Ak q (2 * j) + st (q ⟨j, hj⟩).1 := by
  unfold Tk Ak
  rw [sum_range_succ, sum_range_succ]
  have a1 := aS_even q j hj
  have s1 : ((-1 : ℤ) ^ (2 * j)) = 1 := by rw [pow_mul]; norm_num
  rw [a1, s1, one_mul]
  exact ⟨rfl, rfl⟩

/-- `good2` read through partial sums. -/
lemma good2_iff : ∀ (L : ℕ) (u v : ℤ) (q : Fin L → Bool × Bool),
    good2 L u v q ↔ ∀ j ≤ L, 0 ≤ u + Uc q j ∧ 0 ≤ v + Vc q j := by
  intro L
  induction L with
  | zero =>
    intro u v q
    simp [good2, Uc, Vc]
  | succ L ih =>
    intro u v q
    simp only [good2]
    rw [ih]
    have hU : ∀ j, Uc q (j + 1) = dU (q 0) + Uc (Fin.tail q) j := by
      intro j
      unfold Uc
      rw [sum_range_succ']
      rw [dif_pos (by omega), add_comm]
      congr 1
      apply sum_congr rfl
      intro i hi
      by_cases h : i < L
      · rw [dif_pos (by omega), dif_pos h]; rfl
      · rw [dif_neg (by omega), dif_neg h]
    have hV : ∀ j, Vc q (j + 1) = dV (q 0) + Vc (Fin.tail q) j := by
      intro j
      unfold Vc
      rw [sum_range_succ']
      rw [dif_pos (by omega), add_comm]
      congr 1
      apply sum_congr rfl
      intro i hi
      by_cases h : i < L
      · rw [dif_pos (by omega), dif_pos h]; rfl
      · rw [dif_neg (by omega), dif_neg h]
    constructor
    · rintro ⟨hu, hv, h⟩ j hj
      cases j with
      | zero => simp [Uc, Vc, hu, hv]
      | succ j =>
        rw [hU, hV]
        have := h j (by omega)
        constructor <;> linarith [this.1, this.2]
    · intro h
      have h0 := h 0 (by omega)
      simp only [Uc, Vc, range_zero, sum_empty, add_zero] at h0
      refine ⟨h0.1, h0.2, fun j hj => ?_⟩
      have := h (j + 1) (by omega)
      rw [hU, hV] at this
      constructor <;> linarith [this.1, this.2]

lemma weakP_good2 {L : ℕ} (q : Fin L → Bool × Bool) (h : weakP L q) : good2 L 0 0 q := by
  rw [good2_iff]
  intro j hj
  have := h (2 * j) (by omega)
  obtain ⟨e1, e2⟩ := Tk_even q j hj
  rw [e1, e2] at this
  constructor <;> linarith [this.1, this.2]

end E521

end S_C3

-- ===== P1 =====
section S_P1

/-! Cylinder events under the sign measure: measurability, independence of disjoint
coordinate blocks, shift invariance (original). -/

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace E521

/-- restriction of `ω` to a finite set of coordinates. -/
def rs (s : Finset ℕ) (ω : ℕ → Bool) : s → Bool := fun i => ω i

lemma measurable_rs (s : Finset ℕ) : Measurable (rs s) := by
  unfold rs; fun_prop

lemma measurableSet_rs (s : Finset ℕ) (P : Set (s → Bool)) : MeasurableSet (rs s ⁻¹' P) :=
  measurable_rs s (Set.toFinite P).measurableSet

lemma iIndep_coords : iIndepFun (fun (i : ℕ) (ω : ℕ → Bool) => ω i) μS := by
  unfold μS
  exact iIndepFun_infinitePi (X := fun _ (b : Bool) => b) (fun _ => measurable_id)

/-- **independence of disjoint coordinate blocks.** -/
lemma indep_blocks {S T : Finset ℕ} (hST : Disjoint S T) (P : Set (S → Bool)) (Q : Set (T → Bool)) :
    μS (rs S ⁻¹' P ∩ rs T ⁻¹' Q) = μS (rs S ⁻¹' P) * μS (rs T ⁻¹' Q) := by
  have h := iIndep_coords.indepFun_finset S T hST (fun i => measurable_pi_apply i)
  exact h.measure_inter_preimage_eq_mul _ _ (Set.toFinite P).measurableSet (Set.toFinite Q).measurableSet

/-- shift invariance. -/
lemma μS_map_shift (d : ℕ) : μS.map (fun ω i => ω (i + d)) = μS := by
  unfold μS
  exact Measure.map_infinitePi_infinitePi_of_inj (f := fun i => i + d) (add_left_injective d)

lemma measurable_shift (d : ℕ) : Measurable (fun (ω : ℕ → Bool) (i : ℕ) => ω (i + d)) := by
  fun_prop

lemma μS_shift_preimage (d : ℕ) {A : Set (ℕ → Bool)} (hA : MeasurableSet A) :
    μS ((fun ω i => ω (i + d)) ⁻¹' A) = μS A := by
  rw [← Measure.map_apply (measurable_shift d) hA, μS_map_shift]

end E521

end S_P1

-- ===== C18 =====
section S_C18

/-! Ballot counts with a terminal condition, and the reflection (ballot) formula (original). -/

open Finset

namespace E521

/-- `±1` paths from `u` staying `≥ 0` whose final height satisfies `F`. -/
def good1F (F : ℤ → Prop) : (L : ℕ) → ℤ → (Fin L → Bool) → Prop
  | 0, u, _ => 0 ≤ u ∧ F u
  | L + 1, u, p => 0 ≤ u ∧ good1F F L (u + st (p 0)) (Fin.tail p)

instance good1F_dec (F : ℤ → Prop) [DecidablePred F] :
    ∀ (L : ℕ) (u : ℤ) (p : Fin L → Bool), Decidable (good1F F L u p)
  | 0, u, _ => by unfold good1F; infer_instance
  | L + 1, u, p => by
    unfold good1F
    haveI := good1F_dec F L (u + st (p 0)) (Fin.tail p)
    infer_instance

def N1F (F : ℤ → Prop) [DecidablePred F] (L : ℕ) (u : ℤ) : ℕ :=
  (univ.filter (fun p : Fin L → Bool => good1F F L u p)).card

lemma N1F_neg (F : ℤ → Prop) [DecidablePred F] (L : ℕ) {u : ℤ} (hu : u < 0) : N1F F L u = 0 := by
  unfold N1F
  rw [card_eq_zero, filter_eq_empty_iff]
  intro p _
  cases L with
  | zero => simp only [good1F]; omega
  | succ L => simp only [good1F]; omega

lemma N1F_succ (F : ℤ → Prop) [DecidablePred F] (L : ℕ) {u : ℤ} (hu : 0 ≤ u) :
    N1F F (L + 1) u = N1F F L (u + 1) + N1F F L (u - 1) := by
  unfold N1F
  rw [card_filter_eq_sum, card_filter_eq_sum, card_filter_eq_sum, sum_cons]
  simp only [Fintype.univ_bool, mem_singleton, Bool.true_eq_false, not_false_eq_true,
    sum_insert, sum_singleton]
  congr 1
  · apply Fintype.sum_congr; intro q
    simp only [good1F, Fin.cons_zero, Fin.tail_cons, st, if_true]
    by_cases h : good1F F L (u + 1) q
    · rw [if_pos ⟨hu, h⟩, if_pos h]
    · rw [if_neg (fun h' => h h'.2), if_neg h]
  · apply Fintype.sum_congr; intro q
    simp only [good1F, Fin.cons_zero, Fin.tail_cons, st]
    have e : u + (if false = true then (1 : ℤ) else -1) = u - 1 := by simp; ring
    rw [e]
    by_cases h : good1F F L (u - 1) q
    · rw [if_pos ⟨hu, h⟩, if_pos h]
    · rw [if_neg (fun h' => h h'.2), if_neg h]

lemma N1F_zero (F : ℤ → Prop) [DecidablePred F] (u : ℤ) :
    N1F F 0 u = if 0 ≤ u ∧ F u then 1 else 0 := by
  unfold N1F
  by_cases h : 0 ≤ u ∧ F u
  · rw [if_pos h, Finset.card_eq_one]
    refine ⟨default, ?_⟩
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => by first | exact h | (simp only [Set.mem_setOf_eq]; exact h) | simpa [good1F] using h⟩
  · rw [if_neg h, Finset.card_eq_zero, filter_eq_empty_iff]
    intro p _; simp only [good1F]; exact h

def good2F (F G : ℤ → Prop) : (L : ℕ) → ℤ → ℤ → (Fin L → Bool × Bool) → Prop
  | 0, u, v, _ => 0 ≤ u ∧ 0 ≤ v ∧ F u ∧ G v
  | L + 1, u, v, p => 0 ≤ u ∧ 0 ≤ v ∧ good2F F G L (u + dU (p 0)) (v + dV (p 0)) (Fin.tail p)

instance good2F_dec (F G : ℤ → Prop) [DecidablePred F] [DecidablePred G] :
    ∀ (L : ℕ) (u v : ℤ) (p : Fin L → Bool × Bool), Decidable (good2F F G L u v p)
  | 0, u, v, _ => by unfold good2F; infer_instance
  | L + 1, u, v, p => by
    unfold good2F
    haveI := good2F_dec F G L (u + dU (p 0)) (v + dV (p 0)) (Fin.tail p)
    infer_instance

def N2F (F G : ℤ → Prop) [DecidablePred F] [DecidablePred G] (L : ℕ) (u v : ℤ) : ℕ :=
  (univ.filter (fun p : Fin L → Bool × Bool => good2F F G L u v p)).card

lemma N2F_succ (F G : ℤ → Prop) [DecidablePred F] [DecidablePred G] (L : ℕ) {u v : ℤ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    N2F F G (L + 1) u v = N2F F G L (u + 1) v + N2F F G L (u - 1) v + N2F F G L u (v + 1)
      + N2F F G L u (v - 1) := by
  unfold N2F
  simp only [card_filter_eq_sum]
  rw [sum_cons]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.univ_bool, mem_singleton, Bool.true_eq_false, not_false_eq_true,
    sum_insert, sum_singleton]
  have key : ∀ (a b : Bool) (q : Fin L → Bool × Bool),
      (if good2F F G (L + 1) u v (Fin.cons (a, b) q) then 1 else 0) =
      (if good2F F G L (u + dU (a, b)) (v + dV (a, b)) q then 1 else 0) := by
    intro a b q
    simp only [good2F, Fin.cons_zero, Fin.tail_cons]
    by_cases h : good2F F G L (u + dU (a, b)) (v + dV (a, b)) q
    · rw [if_pos ⟨hu, hv, h⟩, if_pos h]
    · rw [if_neg (fun h' => h h'.2.2), if_neg h]
  simp only [key, dU, dV, st]
  simp only [if_true, Bool.true_eq_false, if_false, Bool.false_eq_true, add_zero]
  have e : u + -1 = u - 1 := by ring
  have e' : v + -1 = v - 1 := by ring
  rw [e, e']
  ring

lemma N2F_neg (F G : ℤ → Prop) [DecidablePred F] [DecidablePred G] {L : ℕ} {u v : ℤ}
    (h : u < 0 ∨ v < 0) : N2F F G L u v = 0 := by
  unfold N2F
  rw [card_eq_zero, filter_eq_empty_iff]
  intro p _
  cases L with
  | zero => simp only [good2F]; omega
  | succ L => simp only [good2F]; omega

lemma N2F_zero (F G : ℤ → Prop) [DecidablePred F] [DecidablePred G] (u v : ℤ) :
    N2F F G 0 u v = if 0 ≤ u ∧ 0 ≤ v ∧ F u ∧ G v then 1 else 0 := by
  unfold N2F
  by_cases h : 0 ≤ u ∧ 0 ≤ v ∧ F u ∧ G v
  · rw [if_pos h, Finset.card_eq_one]
    refine ⟨default, ?_⟩
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => by first | exact h | (simp only [Set.mem_setOf_eq]; exact h) | simpa [good2F] using h⟩
  · rw [if_neg h, Finset.card_eq_zero, filter_eq_empty_iff]
    intro p _; simp only [good2F]; exact h

theorem N2F_eq (F G : ℤ → Prop) [DecidablePred F] [DecidablePred G] (L : ℕ) : ∀ u v : ℤ,
    N2F F G L u v = ∑ h ∈ range (L + 1), L.choose h * (N1F F h u * N1F G (L - h) v) := by
  induction L with
  | zero =>
    intro u v
    simp only [zero_add, range_one, sum_singleton, Nat.choose_self, Nat.sub_self, one_mul]
    rw [N1F_zero, N1F_zero, N2F_zero]
    by_cases h1 : 0 ≤ u ∧ F u <;> by_cases h2 : 0 ≤ v ∧ G v
    · rw [if_pos ⟨h1.1, h2.1, h1.2, h2.2⟩, if_pos h1, if_pos h2]
    · rw [if_neg (fun h => h2 ⟨h.2.1, h.2.2.2⟩), if_pos h1, if_neg h2]
    · rw [if_neg (fun h => h1 ⟨h.1, h.2.2.1⟩), if_neg h1, if_pos h2]
    · rw [if_neg (fun h => h1 ⟨h.1, h.2.2.1⟩), if_neg h1, if_neg h2]
  | succ L ih =>
    intro u v
    by_cases huv : 0 ≤ u ∧ 0 ≤ v
    · rw [N2F_succ F G L huv.1 huv.2, ih, ih, ih, ih]
      have r1 : ∀ h, N1F F h (u + 1) + N1F F h (u - 1) = N1F F (h + 1) u := fun h =>
        (N1F_succ F h huv.1).symm
      have r2 : ∀ h, N1F G h (v + 1) + N1F G h (v - 1) = N1F G (h + 1) v := fun h =>
        (N1F_succ G h huv.2).symm
      have A : (∑ h ∈ range (L + 1), L.choose h * (N1F F h (u + 1) * N1F G (L - h) v)) +
          (∑ h ∈ range (L + 1), L.choose h * (N1F F h (u - 1) * N1F G (L - h) v)) =
          ∑ h ∈ range (L + 1), L.choose h * (N1F F (h + 1) u * N1F G (L - h) v) := by
        rw [← sum_add_distrib]; apply sum_congr rfl; intro h _; rw [← r1]; ring
      have B : (∑ h ∈ range (L + 1), L.choose h * (N1F F h u * N1F G (L - h) (v + 1))) +
          (∑ h ∈ range (L + 1), L.choose h * (N1F F h u * N1F G (L - h) (v - 1))) =
          ∑ h ∈ range (L + 1), L.choose h * (N1F F h u * N1F G (L - h + 1) v) := by
        rw [← sum_add_distrib]; apply sum_congr rfl; intro h _; rw [← r2]; ring
      rw [A, add_assoc, B]
      rw [sum_range_succ' _ (L + 1)]
      simp only [Nat.choose_succ_succ', add_mul, sum_add_distrib]
      rw [sum_range_succ (fun h => L.choose (h + 1) * (N1F F (h + 1) u * N1F G (L + 1 - (h + 1)) v)) L]
      simp only [Nat.choose_succ_self, zero_mul, add_zero, Nat.choose_zero_right, one_mul,
        Nat.sub_zero]
      have C1 : ∑ h ∈ range (L + 1), L.choose h * (N1F F (h + 1) u * N1F G (L + 1 - (h + 1)) v) =
          ∑ h ∈ range (L + 1), L.choose h * (N1F F (h + 1) u * N1F G (L - h) v) := by
        apply sum_congr rfl; intro h _; congr 3; omega
      have C2 : ∑ h ∈ range L, L.choose (h + 1) * (N1F F (h + 1) u * N1F G (L + 1 - (h + 1)) v) +
          N1F F 0 u * N1F G (L + 1) v =
          ∑ h ∈ range (L + 1), L.choose h * (N1F F h u * N1F G (L - h + 1) v) := by
        rw [sum_range_succ' (fun h => L.choose h * (N1F F h u * N1F G (L - h + 1) v))]
        simp only [Nat.choose_zero_right, one_mul, Nat.sub_zero]
        congr 1
        apply sum_congr rfl; intro h hh; rw [mem_range] at hh; congr 3; omega
      rw [C1, ← C2]; ring
    · rw [N2F_neg F G (by omega)]
      symm
      apply sum_eq_zero
      intro h _
      rcases not_and_or.mp huv with hu | hv
      · rw [N1F_neg F h (by omega)]; ring
      · rw [N1F_neg G (L + 1 - h) (by omega)]; ring

/-! ### the ballot formula -/

/-- binomial coefficient extended by `0` to negative arguments. -/
def chZ (h : ℕ) (k : ℤ) : ℤ := if k < 0 then 0 else (h.choose k.toNat : ℤ)

lemma chZ_pascal (h : ℕ) (k : ℤ) : chZ (h + 1) k = chZ h k + chZ h (k - 1) := by
  unfold chZ
  by_cases hk : k < 0
  · rw [if_pos hk, if_pos hk, if_pos (by omega)]; ring
  · rw [if_neg hk, if_neg hk]
    by_cases hk0 : k = 0
    · subst hk0; rw [if_pos (by omega)]; simp
    · rw [if_neg (by omega)]
      have : k.toNat = (k - 1).toNat + 1 := by omega
      rw [this, Nat.choose_succ_succ']; push_cast; ring

lemma chZ_zero_of_lt {h : ℕ} {k : ℤ} (hk : (h : ℤ) < k) : chZ h k = 0 := by
  unfold chZ; rw [if_neg (by omega)]
  rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

lemma chZ_zero_pos {k : ℤ} (hk : 0 < k) : chZ 0 k = 0 := chZ_zero_of_lt (by simpa using hk)

/-- **Ballot formula**: paths of length `h` from `u` staying `≥ 0` and ending at
`y = u + 2k - h ≥ 0` number `C(h,k) - C(h,k+u+1)`. -/
theorem ballot (h : ℕ) : ∀ (u : ℕ) (k : ℤ), 0 ≤ (u : ℤ) + 2 * k - h →
    (N1F (· = (u : ℤ) + 2 * k - h) h u : ℤ) = chZ h k - chZ h (k + u + 1) := by
  induction h with
  | zero =>
    intro u k hy
    rw [N1F_zero]
    push_cast
    by_cases hk : k = 0
    · subst hk
      rw [if_pos ⟨by positivity, by ring⟩]
      have hc : chZ 0 (0 + (u : ℤ) + 1) = 0 := chZ_zero_pos (by omega)
      rw [hc]
      simp [chZ]
    · rw [if_neg (fun h' => hk (by omega))]
      rcases lt_or_gt_of_ne hk with hk' | hk'
      · rw [show chZ 0 k = 0 by unfold chZ; rw [if_pos hk'], chZ_zero_pos (by omega)]; simp
      · rw [chZ_zero_pos hk', chZ_zero_pos (by omega)]; simp
  | succ h ih =>
    intro u k hy
    rw [N1F_succ _ h (by positivity)]
    push_cast
    have hup := ih (u + 1) (k - 1) (by push_cast; omega)
    have e1 : ((u + 1 : ℕ) : ℤ) + 2 * (k - 1) - h = (u : ℤ) + 2 * k - (h + 1) := by push_cast; ring
    have e2 : ((u + 1 : ℕ) : ℤ) = (u : ℤ) + 1 := by push_cast; ring
    rw [e1, e2] at hup
    have e3 : k - 1 + ((u : ℤ) + 1) + 1 = k + u + 1 := by ring
    rw [e3] at hup
    rw [hup]
    rcases Nat.eq_zero_or_pos u with hu | hu
    · subst hu
      rw [N1F_neg _ h (by norm_num)]
      push_cast
      rw [chZ_pascal, chZ_pascal]
      ring_nf
    · have hdown := ih (u - 1) k (by
        have : ((u - 1 : ℕ) : ℤ) = (u : ℤ) - 1 := by omega
        rw [this]; omega)
      have e4 : ((u - 1 : ℕ) : ℤ) = (u : ℤ) - 1 := by omega
      rw [e4] at hdown
      have e5 : (u : ℤ) - 1 + 2 * k - h = (u : ℤ) + 2 * k - (h + 1) := by ring
      rw [e5] at hdown
      rw [hdown]
      rw [chZ_pascal, chZ_pascal]
      ring_nf

end E521

end S_C18

-- ===== P2 =====
section S_P2

/-! The cone and top events and their probabilities (original). -/

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace E521

/-- `good2F` read through partial sums. -/
lemma good2F_iff (F G : ℤ → Prop) : ∀ (L : ℕ) (u v : ℤ) (q : Fin L → Bool × Bool),
    good2F F G L u v q ↔ (∀ j ≤ L, 0 ≤ u + Uc q j ∧ 0 ≤ v + Vc q j) ∧ F (u + Uc q L) ∧ G (v + Vc q L) := by
  intro L
  induction L with
  | zero => intro u v q; simp [good2F, Uc, Vc]; tauto
  | succ L ih =>
    intro u v q
    simp only [good2F]
    rw [ih]
    have hU : ∀ j, Uc q (j + 1) = dU (q 0) + Uc (Fin.tail q) j := by
      intro j
      unfold Uc
      rw [sum_range_succ', dif_pos (by omega), add_comm]
      congr 1
      apply sum_congr rfl
      intro i _
      by_cases h : i < L
      · rw [dif_pos (by omega), dif_pos h]; rfl
      · rw [dif_neg (by omega), dif_neg h]
    have hV : ∀ j, Vc q (j + 1) = dV (q 0) + Vc (Fin.tail q) j := by
      intro j
      unfold Vc
      rw [sum_range_succ', dif_pos (by omega), add_comm]
      congr 1
      apply sum_congr rfl
      intro i _
      by_cases h : i < L
      · rw [dif_pos (by omega), dif_pos h]; rfl
      · rw [dif_neg (by omega), dif_neg h]
    constructor
    · rintro ⟨hu, hv, ⟨h, hF, hG⟩⟩
      refine ⟨fun j hj => ?_, ?_, ?_⟩
      · cases j with
        | zero => simp [Uc, Vc, hu, hv]
        | succ j =>
          rw [hU, hV]
          have := h j (by omega)
          constructor <;> linarith [this.1, this.2]
      · rw [hU]; convert hF using 1; ring
      · rw [hV]; convert hG using 1; ring
    · rintro ⟨h, hF, hG⟩
      have h0 := h 0 (by omega)
      simp only [Uc, Vc, range_zero, sum_empty, add_zero] at h0
      refine ⟨h0.1, h0.2, fun j hj => ?_, ?_, ?_⟩
      · have := h (j + 1) (by omega)
        rw [hU, hV] at this
        constructor <;> linarith [this.1, this.2]
      · rw [hU] at hF; convert hF using 1; ring
      · rw [hV] at hG; convert hG using 1; ring

/-- the cone event on `K` backward pairs, with final conditions. -/
def coneE (K : ℕ) (F G : ℤ → Prop) : Set (ℕ → Bool) := Φ K ⁻¹' {p | good2F F G K 0 0 p}

lemma coneE_real (K : ℕ) (F G : ℤ → Prop) [DecidablePred F] [DecidablePred G] :
    μS.real (coneE K F G) = (N2F F G K 0 0 : ℝ) / 4 ^ K := by
  have h := μS_Φ_real K (univ.filter (fun p : Fin K → Bool × Bool => good2F F G K 0 0 p))
  unfold coneE N2F
  convert h using 2
  ext p; simp

/-- the closed-quadrant condition on the first `L` backward pairs of level `K`. -/
def topE (K L : ℕ) : Set (ℕ → Bool) :=
  {ω | good2 L 0 0 (fun j : Fin L => (ω (2 * K - 1 - 2 * j), ω (2 * K - 2 - 2 * j)))}

lemma topE_eq (K L : ℕ) (hL : L ≤ K) :
    topE K L = (fun ω i => ω (i + 2 * (K - L))) ⁻¹' (Φ L ⁻¹' {p | good2 L 0 0 p}) := by
  ext ω
  simp only [topE, Set.mem_setOf_eq, Set.mem_preimage, Φ]
  have : (fun j : Fin L => (ω (2 * K - 1 - 2 * j), ω (2 * K - 2 - 2 * j))) =
      (fun j : Fin L => (ω (2 * L - 1 - 2 * j + 2 * (K - L)), ω (2 * L - 2 - 2 * j + 2 * (K - L)))) := by
    funext j; have := j.isLt; congr 2 <;> omega
  rw [this]
  exact Iff.rfl

lemma topE_real (K L : ℕ) (hL : L ≤ K) : μS.real (topE K L) = (N2 L 0 0 : ℝ) / 4 ^ L := by
  rw [Measure.real, topE_eq K L hL, μS_shift_preimage _ (measurableSet_Φ L _)]
  have h := μS_Φ_real L (univ.filter (fun p : Fin L → Bool × Bool => good2 L 0 0 p))
  rw [Measure.real] at h
  unfold N2
  convert h using 3
  ext p; simp

lemma cone_sub_top (K L : ℕ) (hL : L ≤ K) (F G : ℤ → Prop) : coneE K F G ⊆ topE K L := by
  intro ω hω
  simp only [coneE, Set.mem_preimage, Set.mem_setOf_eq] at hω
  rw [good2F_iff] at hω
  simp only [topE, Set.mem_setOf_eq]
  rw [good2_iff]
  intro j hj
  have := hω.1 j (by omega)
  have eU : Uc (fun j : Fin L => (ω (2 * K - 1 - 2 * j), ω (2 * K - 2 - 2 * j))) j = Uc (Φ K ω) j := by
    unfold Uc; apply sum_congr rfl; intro i hi; rw [mem_range] at hi
    rw [dif_pos (by omega), dif_pos (by omega)]; rfl
  have eV : Vc (fun j : Fin L => (ω (2 * K - 1 - 2 * j), ω (2 * K - 2 - 2 * j))) j = Vc (Φ K ω) j := by
    unfold Vc; apply sum_congr rfl; intro i hi; rw [mem_range] at hi
    rw [dif_pos (by omega), dif_pos (by omega)]; rfl
  rw [eU, eV]; simpa using this

/-- `topE K L` only depends on the coordinates `[2K-2L, 2K)`. -/
lemma topE_cyl (K L : ℕ) (hL : L ≤ K) :
    ∃ Q : Set (Ico (2 * K - 2 * L) (2 * K) → Bool), topE K L = rs (Ico (2 * K - 2 * L) (2 * K)) ⁻¹' Q := by
  refine ⟨{r | good2 L 0 0 (fun j : Fin L =>
    (r ⟨2 * K - 1 - 2 * j, by have := j.isLt; simp [mem_Ico]; omega⟩,
     r ⟨2 * K - 2 - 2 * j, by have := j.isLt; simp [mem_Ico]; omega⟩))}, ?_⟩
  ext ω; simp [topE, rs]

end E521

end S_P2

-- ===== C4 =====
section S_C4

-- ===== RR0 =====

/-!
# Erdős 522 (real roots), part 0: Erdős's Littlewood–Offord bound

For signs `ε : ι → ℤˣ` and weights `a` with `|a i| ≥ 1` on a set `I` of size `M`, the number of sign
vectors with `∑ ε i a i` in a half-open interval of length `2` is at most `2^|ι| / √M`.
(Erdős 1945, via Sperner's theorem.)
-/

open Finset Real

noncomputable section S_RR0

namespace R522

/-- Signed sum. -/
def ssum {ι : Type*} [Fintype ι] (ε : ι → ℤˣ) (a : ι → ℝ) : ℝ := ∑ i, ((ε i : ℤ) : ℝ) * a i

lemma cb_sq (p : ℕ) : (Nat.centralBinom p : ℝ) ^ 2 * (2 * p + 1) ≤ 16 ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
    have h := Nat.succ_mul_centralBinom_succ p
    have hc : (Nat.centralBinom (p + 1) : ℝ) = 2 * (2 * p + 1) * Nat.centralBinom p / (p + 1) := by
      rw [eq_div_iff (by positivity)]
      have : ((p + 1 : ℕ) : ℝ) * Nat.centralBinom (p + 1) = 2 * (2 * p + 1) * Nat.centralBinom p := by
        exact_mod_cast h
      push_cast at this; linarith
    rw [hc, div_pow, div_mul_eq_mul_div]
    have hp : (0 : ℝ) < ((p : ℝ) + 1) ^ 2 := by positivity
    rw [div_le_iff₀ hp]
    have key : (2 * (p : ℝ) + 1) * (2 * ((p : ℝ) + 1) + 1) ≤ 4 * ((p : ℝ) + 1) ^ 2 := by nlinarith
    have e1 : (2 * (2 * (p : ℝ) + 1) * (Nat.centralBinom p : ℝ)) ^ 2 * (2 * ((p : ℝ) + 1) + 1)
        = 4 * (((Nat.centralBinom p : ℝ)) ^ 2 * (2 * p + 1)) * ((2 * p + 1) * (2 * ((p : ℝ) + 1) + 1)) := by
      ring
    push_cast
    rw [e1]
    have := mul_le_mul ih key (by positivity) (by positivity)
    calc 4 * (((Nat.centralBinom p : ℝ)) ^ 2 * (2 * p + 1)) * ((2 * p + 1) * (2 * ((p : ℝ) + 1) + 1))
        = 4 * ((((Nat.centralBinom p : ℝ)) ^ 2 * (2 * p + 1)) * ((2 * p + 1) * (2 * ((p : ℝ) + 1) + 1))) := by ring
      _ ≤ 4 * (16 ^ p * (4 * ((p : ℝ) + 1) ^ 2)) := by linarith
      _ = 16 ^ (p + 1) * ((p : ℝ) + 1) ^ 2 := by rw [pow_succ]; ring

lemma choose_half_sq (M : ℕ) : ((M.choose (M / 2) : ℕ) : ℝ) ^ 2 * M ≤ 4 ^ M := by
  obtain ⟨p, rfl | rfl⟩ := Nat.even_or_odd' M
  · have h2 : 2 * p / 2 = p := by omega
    rw [h2, ← Nat.centralBinom_eq_two_mul_choose]
    have := cb_sq p
    have h16 : (4 : ℝ) ^ (2 * p) = 16 ^ p := by rw [pow_mul]; norm_num
    rw [h16]; push_cast
    have : (0 : ℝ) ≤ (Nat.centralBinom p : ℝ) ^ 2 := by positivity
    nlinarith
  · have h2 : (2 * p + 1) / 2 = p := by omega
    rw [h2]
    have hsum : Nat.centralBinom (p + 1) = 2 * (2 * p + 1).choose p := by
      rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (p + 1) = (2 * p + 1) + 1 by ring,
        Nat.choose_succ_succ, Nat.choose_symm_of_eq_add (show 2 * p + 1 = (p + 1) + p by omega)]
      ring
    have := cb_sq (p + 1)
    have hc : ((2 * p + 1).choose p : ℝ) = Nat.centralBinom (p + 1) / 2 := by
      rw [hsum]; push_cast; ring
    rw [hc]
    have h16 : (4 : ℝ) ^ (2 * p + 1) = 16 ^ (p + 1) / 4 := by
      rw [pow_succ, pow_mul, pow_succ]; ring
    rw [h16]; push_cast at this ⊢
    have : (0 : ℝ) ≤ (Nat.centralBinom (p + 1) : ℝ) ^ 2 := by positivity
    nlinarith

/-- The antichain step: with the outside signs fixed, the inside sign patterns giving a sum in
`[t, t + 2)` form an antichain. -/
lemma lo_fiber {κ : Type*} [Fintype κ] [DecidableEq κ] (a : κ → ℝ) (ha : ∀ i, 1 ≤ |a i|)
    (c t : ℝ) :
    ((univ.filter fun ε : κ → ℤˣ => t ≤ c + ssum ε a ∧ c + ssum ε a < t + 2).card)
      ≤ (Fintype.card κ).choose (Fintype.card κ / 2) := by
  classical
  -- sign of each weight
  set s : κ → ℤˣ := fun i => if 0 ≤ a i then 1 else -1 with hs
  have hsa : ∀ i, ((s i : ℤ) : ℝ) * a i = |a i| := by
    intro i; simp only [hs]; split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (not_le.mp h)]
  set T : (κ → ℤˣ) → Finset κ := fun ε => univ.filter fun i => ε i = s i with hT
  have hval : ∀ (ε : κ → ℤˣ) i, ε i = s i ∨ ε i = -s i := by
    intro ε i
    rcases Int.units_eq_one_or (ε i) with h | h <;> rcases Int.units_eq_one_or (s i) with h' | h' <;>
      simp [h, h']
  have hTinj : Function.Injective T := by
    intro ε ε' h
    funext i
    have hi := congrArg (fun F => i ∈ F) h
    simp only [hT, mem_filter, mem_univ, true_and, eq_iff_iff] at hi
    rcases hval ε i with h1 | h1 <;> rcases hval ε' i with h2 | h2
    · rw [h1, h2]
    · exfalso; have := hi.mp h1; rw [this] at h2
      exact absurd h2 (by rcases Int.units_eq_one_or (s i) with h | h <;> simp [h])
    · exfalso; have := hi.mpr h2; rw [this] at h1
      exact absurd h1 (by rcases Int.units_eq_one_or (s i) with h | h <;> simp [h])
    · rw [h1, h2]
  -- sum formula: ssum ε a = 2 ∑_{T ε} |a| - ∑ |a|
  have hsum : ∀ ε : κ → ℤˣ, ssum ε a = 2 * ∑ i ∈ T ε, |a i| - ∑ i, |a i| := by
    intro ε
    unfold ssum
    have : ∀ i, ((ε i : ℤ) : ℝ) * a i = 2 * (if ε i = s i then |a i| else 0) - |a i| := by
      intro i
      rcases hval ε i with h | h
      · rw [if_pos h, h, hsa]; ring
      · rw [if_neg (by rw [h]; rcases Int.units_eq_one_or (s i) with h' | h' <;> simp [h']), h]
        push_cast; rw [neg_mul, hsa]; ring
    simp_rw [this]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  set F := univ.filter fun ε : κ → ℤˣ => t ≤ c + ssum ε a ∧ c + ssum ε a < t + 2 with hF
  have hanti : IsAntichain (· ⊆ ·) (SetLike.coe (F.image T)) := by
    intro A hA B hB hAB hsub
    simp only [coe_image, Set.mem_image, mem_coe] at hA hB
    obtain ⟨ε, hε, rfl⟩ := hA
    obtain ⟨ε', hε', rfl⟩ := hB
    have hne : T ε ⊂ T ε' := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hAB⟩
    obtain ⟨j, hj', hj⟩ := Finset.exists_of_ssubset hne
    have hdiff : ∑ i ∈ T ε', |a i| - ∑ i ∈ T ε, |a i| ≥ 1 := by
      rw [← Finset.sum_sdiff hsub]
      have : |a j| ≤ ∑ i ∈ T ε' \ T ε, |a i| :=
        Finset.single_le_sum (f := fun i => |a i|) (fun i _ => abs_nonneg _)
          (Finset.mem_sdiff.mpr ⟨hj', hj⟩)
      linarith [ha j]
    simp only [hF, mem_filter, mem_univ, true_and] at hε hε'
    rw [hsum] at hε hε'
    linarith [hε.1, hε'.2]
  have := hanti.sperner
  rwa [Finset.card_image_of_injective _ hTinj] at this

/-- **Erdős's Littlewood–Offord bound.** -/
theorem lo_interval {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) (I : Finset ι)
    (hI : ∀ i ∈ I, 1 ≤ |a i|) (hIne : I.Nonempty) (t : ℝ) :
    ((univ.filter fun ε : ι → ℤˣ => t ≤ ssum ε a ∧ ssum ε a < t + 2).card : ℝ)
      ≤ 2 ^ Fintype.card ι / √(I.card) := by
  classical
  set p : ι → Prop := fun i => i ∈ I
  let e := Equiv.piEquivPiSubtypeProd p (fun _ => ℤˣ)
  let κ := {i // p i}
  let ν := {i // ¬ p i}
  have hsplit : ∀ ε : ι → ℤˣ, ssum ε a = (∑ j : ν, (((e ε).2 j : ℤ) : ℝ) * a j)
      + ssum (e ε).1 (fun i : κ => a i) := by
    intro ε
    unfold ssum
    rw [add_comm]
    convert (Fintype.sum_subtype_add_sum_subtype p (fun i => ((ε i : ℤ) : ℝ) * a i)).symm <;> rfl
  -- count via the equivalence
  have hcount : ((univ.filter fun ε : ι → ℤˣ => t ≤ ssum ε a ∧ ssum ε a < t + 2).card : ℝ)
      = ∑ o : ν → ℤˣ, ((univ.filter fun ε : κ → ℤˣ =>
          t ≤ (∑ j : ν, ((o j : ℤ) : ℝ) * a j) + ssum ε (fun i : κ => a i) ∧
          (∑ j : ν, ((o j : ℤ) : ℝ) * a j) + ssum ε (fun i : κ => a i) < t + 2).card : ℝ) := by
    rw [Finset.card_filter]
    push_cast
    rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun o _ => ?_)
    rw [Finset.card_filter]; push_cast
    refine Finset.sum_congr rfl (fun ε _ => ?_)
    simp only [hsplit, Equiv.apply_symm_apply]
  have hfib : ∀ o : ν → ℤˣ, ((univ.filter fun ε : κ → ℤˣ =>
          t ≤ (∑ j : ν, ((o j : ℤ) : ℝ) * a j) + ssum ε (fun i : κ => a i) ∧
          (∑ j : ν, ((o j : ℤ) : ℝ) * a j) + ssum ε (fun i : κ => a i) < t + 2).card : ℝ)
        ≤ (Fintype.card κ).choose (Fintype.card κ / 2) := by
    intro o
    exact_mod_cast lo_fiber (fun i : κ => a i) (fun i => hI i i.2) _ t
  have hκ : Fintype.card κ = I.card := by
    simp only [κ, p]; exact Fintype.card_coe I
  have hν : Fintype.card (ν → ℤˣ) * 2 ^ I.card = 2 ^ Fintype.card ι := by
    rw [Fintype.card_fun, Fintype.card_units_int, ← hκ, ← pow_add]
    congr 1
    rw [add_comm, Fintype.card_subtype_compl]
    have := Fintype.card_subtype_le p
    show Fintype.card {x // p x} + _ = _
    omega
  rw [hcount]
  have hM : (0 : ℝ) < I.card := by exact_mod_cast hIne.card_pos
  calc _ ≤ ∑ _o : ν → ℤˣ, (((Fintype.card κ).choose (Fintype.card κ / 2) : ℕ) : ℝ) :=
        Finset.sum_le_sum (fun o _ => hfib o)
    _ = Fintype.card (ν → ℤˣ) * ((I.card.choose (I.card / 2) : ℕ) : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hκ]
    _ ≤ 2 ^ Fintype.card ι / √(I.card) := by
        rw [le_div_iff₀ (Real.sqrt_pos.mpr hM)]
        have h1 := choose_half_sq I.card
        have hsq : ((I.card.choose (I.card / 2) : ℕ) : ℝ) * √(I.card) ≤ 2 ^ I.card := by
          have h0 : 0 ≤ ((I.card.choose (I.card / 2) : ℕ) : ℝ) * √(I.card) := by positivity
          have : (((I.card.choose (I.card / 2) : ℕ) : ℝ) * √(I.card)) ^ 2 ≤ (2 ^ I.card) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hM.le, ← pow_mul, mul_comm I.card 2, pow_mul]; norm_num
            linarith
          exact (pow_le_pow_iff_left₀ h0 (by positivity) (by norm_num)).mp this
        have hν' : (Fintype.card (ν → ℤˣ) : ℝ) * 2 ^ I.card = 2 ^ Fintype.card ι := by
          exact_mod_cast hν
        calc (Fintype.card (ν → ℤˣ) : ℝ) * ((I.card.choose (I.card / 2) : ℕ) : ℝ) * √(I.card)
            = (Fintype.card (ν → ℤˣ) : ℝ) * (((I.card.choose (I.card / 2) : ℕ) : ℝ) * √(I.card)) := by ring
          _ ≤ (Fintype.card (ν → ℤˣ) : ℝ) * 2 ^ I.card := by gcongr
          _ = _ := hν'

end R522

end S_RR0
-- ===== RR2 =====

/-!
# Erdős 522 (real roots), part 2: averages over sign vectors

`EE f` is the average of `f` over `ε : ι → ℤˣ`, and `PP S` the proportion of sign vectors in `S`.
Markov and Chebyshev, second moments of signed sums, a weighted Cauchy–Schwarz bound, and
independence of functions of disjoint coordinate sets.
-/

open Finset Real

noncomputable section S_RR2

namespace R522

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Average over sign vectors. -/
def EE (f : (ι → ℤˣ) → ℝ) : ℝ := (∑ ε, f ε) / 2 ^ Fintype.card ι

open scoped Classical in
/-- Proportion of sign vectors satisfying `S`. -/
def PP (S : (ι → ℤˣ) → Prop) : ℝ := EE fun ε => if S ε then 1 else 0

lemma PP_eq (S : (ι → ℤˣ) → Prop) [DecidablePred S] :
    PP S = EE fun ε => if S ε then (1 : ℝ) else 0 := by
  unfold PP; congr 1; ext ε; split_ifs <;> simp_all

lemma card_signs : (Fintype.card (ι → ℤˣ) : ℝ) = 2 ^ Fintype.card ι := by
  rw [Fintype.card_fun, Fintype.card_units_int]; push_cast; rfl

lemma EE_const (c : ℝ) : EE (ι := ι) (fun _ => c) = c := by
  unfold EE
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_signs]
  field_simp

lemma EE_add (f g : (ι → ℤˣ) → ℝ) : EE (fun ε => f ε + g ε) = EE f + EE g := by
  unfold EE; rw [Finset.sum_add_distrib, add_div]

lemma EE_sub (f g : (ι → ℤˣ) → ℝ) : EE (fun ε => f ε - g ε) = EE f - EE g := by
  unfold EE; rw [Finset.sum_sub_distrib, sub_div]

lemma EE_smul (c : ℝ) (f : (ι → ℤˣ) → ℝ) : EE (fun ε => c * f ε) = c * EE f := by
  unfold EE; rw [← Finset.mul_sum, mul_div_assoc]

lemma EE_sum {κ : Type*} (s : Finset κ) (f : κ → (ι → ℤˣ) → ℝ) :
    EE (fun ε => ∑ k ∈ s, f k ε) = ∑ k ∈ s, EE (f k) := by
  unfold EE; rw [Finset.sum_comm, Finset.sum_div]

lemma EE_mono {f g : (ι → ℤˣ) → ℝ} (h : ∀ ε, f ε ≤ g ε) : EE f ≤ EE g := by
  unfold EE; gcongr with ε; exact h ε

lemma EE_nonneg {f : (ι → ℤˣ) → ℝ} (h : ∀ ε, 0 ≤ f ε) : 0 ≤ EE f := by
  have := EE_mono (f := fun _ => (0 : ℝ)) h
  rwa [EE_const] at this

lemma PP_nonneg (S : (ι → ℤˣ) → Prop) : 0 ≤ PP S := by
  classical
  unfold PP; exact EE_nonneg (fun ε => by split_ifs <;> norm_num)

lemma PP_le_one (S : (ι → ℤˣ) → Prop) : PP S ≤ 1 := by
  classical
  unfold PP
  have := EE_mono (f := fun ε => if S ε then (1 : ℝ) else 0) (g := fun _ => 1)
    (fun ε => by split_ifs <;> norm_num)
  rwa [EE_const] at this

lemma PP_mono {S T : (ι → ℤˣ) → Prop} (h : ∀ ε, S ε → T ε) : PP S ≤ PP T := by
  classical
  unfold PP
  exact EE_mono (fun ε => by
    by_cases hs : S ε
    · rw [if_pos hs, if_pos (h ε hs)]
    · rw [if_neg hs]; split_ifs <;> norm_num)

lemma PP_or_le (S T : (ι → ℤˣ) → Prop) : PP (fun ε => S ε ∨ T ε) ≤ PP S + PP T := by
  classical
  unfold PP
  rw [← EE_add]
  exact EE_mono (fun ε => by split_ifs <;> simp_all)

lemma PP_exists_le {κ : Type*} (s : Finset κ) (S : κ → (ι → ℤˣ) → Prop) :
    PP (fun ε => ∃ k ∈ s, S k ε) ≤ ∑ k ∈ s, PP (S k) := by
  classical
  unfold PP
  rw [← EE_sum]
  refine EE_mono (fun ε => ?_)
  split_ifs with h
  · obtain ⟨k, hk, hS⟩ := h
    calc (1 : ℝ) = if S k ε then 1 else 0 := by rw [if_pos hS]
      _ ≤ ∑ j ∈ s, if S j ε then (1 : ℝ) else 0 :=
          Finset.single_le_sum (f := fun j => if S j ε then (1 : ℝ) else 0)
            (fun j _ => by split_ifs <;> norm_num) hk
  · exact Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)

lemma PP_compl (S : (ι → ℤˣ) → Prop) : PP (fun ε => ¬ S ε) = 1 - PP S := by
  classical
  unfold PP
  have key : ∀ g : (ι → ℤˣ) → ℝ, (∀ ε, g ε = 1 - (if S ε then 1 else 0)) →
      EE g = 1 - EE (fun ε => if S ε then (1 : ℝ) else 0) := by
    intro g hg
    rw [show g = fun ε => 1 - (if S ε then (1 : ℝ) else 0) from funext hg, EE_sub, EE_const]
  exact key _ (fun ε => by by_cases h : S ε <;> simp [h])

/-- Markov. -/
lemma markov {f : (ι → ℤˣ) → ℝ} (hf : ∀ ε, 0 ≤ f ε) {t : ℝ} (ht : 0 < t) :
    PP (fun ε => t ≤ f ε) ≤ EE f / t := by
  classical
  rw [le_div_iff₀ ht]
  unfold PP
  rw [mul_comm, ← EE_smul]
  exact EE_mono (fun ε => by split_ifs with h <;> nlinarith [hf ε])

/-- Markov with indicators bounded above by a function. -/
lemma PP_le_EE {S : (ι → ℤˣ) → Prop} {f : (ι → ℤˣ) → ℝ} (hf : ∀ ε, 0 ≤ f ε)
    (h : ∀ ε, S ε → 1 ≤ f ε) : PP S ≤ EE f := by
  classical
  unfold PP
  exact EE_mono (fun ε => by split_ifs with hs; exacts [h ε hs, hf ε])

/-- Chebyshev. -/
lemma chebyshev (f : (ι → ℤˣ) → ℝ) {t : ℝ} (ht : 0 < t) :
    PP (fun ε => t ≤ |f ε|) ≤ EE (fun ε => f ε ^ 2) / t ^ 2 := by
  have h := markov (f := fun ε => f ε ^ 2) (fun ε => sq_nonneg _) (pow_pos ht 2)
  refine (PP_mono (fun ε hε => ?_)).trans h
  have : t ^ 2 ≤ |f ε| ^ 2 := pow_le_pow_left₀ ht.le hε 2
  rwa [sq_abs] at this

/-! ### Flips and first moments -/

/-- Flip coordinate `i`. -/
def flipAt (i : ι) (ε : ι → ℤˣ) : ι → ℤˣ := Function.update ε i (-ε i)

lemma flipAt_invol (i : ι) : Function.Involutive (flipAt i) := by
  intro ε; funext j; unfold flipAt
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h]

lemma sum_flip {M : Type*} [AddCommMonoid M] (i : ι) (f : (ι → ℤˣ) → M) :
    ∑ ε, f (flipAt i ε) = ∑ ε, f ε :=
  Equiv.sum_comp (flipAt_invol i).toPerm f

lemma EE_coord (i : ι) : EE (ι := ι) (fun ε => ((ε i : ℤ) : ℝ)) = 0 := by
  unfold EE
  have h := sum_flip i (fun ε => ((ε i : ℤ) : ℝ))
  simp only [flipAt, Function.update_self, Units.val_neg, Int.cast_neg, Finset.sum_neg_distrib] at h
  have : ∑ ε : ι → ℤˣ, ((ε i : ℤ) : ℝ) = 0 := by linarith
  rw [this, zero_div]

lemma EE_coord_mul (i j : ι) (hij : i ≠ j) :
    EE (ι := ι) (fun ε => ((ε i : ℤ) : ℝ) * ((ε j : ℤ) : ℝ)) = 0 := by
  unfold EE
  have h := sum_flip i (fun ε => ((ε i : ℤ) : ℝ) * ((ε j : ℤ) : ℝ))
  simp only [flipAt, Function.update_self, Function.update_of_ne hij.symm, Units.val_neg,
    Int.cast_neg, neg_mul, Finset.sum_neg_distrib] at h
  have : ∑ ε : ι → ℤˣ, ((ε i : ℤ) : ℝ) * ((ε j : ℤ) : ℝ) = 0 := by linarith
  rw [this, zero_div]

lemma unit_sq (u : ℤˣ) : ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

/-- Second mixed moment of signed sums. -/
lemma EE_ssum_mul (c d : ι → ℝ) :
    EE (fun ε => ssum ε c * ssum ε d) = ∑ i, c i * d i := by
  unfold ssum
  have : ∀ ε : ι → ℤˣ, (∑ i, ((ε i : ℤ) : ℝ) * c i) * (∑ j, ((ε j : ℤ) : ℝ) * d j)
      = ∑ i, ∑ j, (c i * d j) * (((ε i : ℤ) : ℝ) * ((ε j : ℤ) : ℝ)) := by
    intro ε; rw [Finset.sum_mul_sum]; refine Finset.sum_congr rfl (fun i _ =>
      Finset.sum_congr rfl (fun j _ => by ring))
  simp_rw [this]
  rw [EE_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [EE_sum, Finset.sum_eq_single i]
  · rw [EE_smul]
    simp_rw [unit_sq]; rw [EE_const, mul_one]
  · intro j _ hj; rw [EE_smul, EE_coord_mul i j (Ne.symm hj), mul_zero]
  · simp

lemma EE_ssum_sq (c : ι → ℝ) : EE (fun ε => ssum ε c ^ 2) = ∑ i, c i ^ 2 := by
  have := EE_ssum_mul c c
  simp_rw [sq]; exact this

/-- Chebyshev for signed sums. -/
lemma cheb_ssum (c : ι → ℝ) {t : ℝ} (ht : 0 < t) :
    PP (fun ε => t ≤ |ssum ε c|) ≤ (∑ i, c i ^ 2) / t ^ 2 := by
  have := chebyshev (fun ε => ssum ε c) ht
  rwa [EE_ssum_sq] at this

/-- Weighted Cauchy–Schwarz: if `E X_j² ≤ μ_j²` then `E (∑ w_j |X_j|)² ≤ (∑ w_j μ_j)²`. -/
lemma EE_wsum_sq {κ : Type*} (s : Finset κ) (w μ : κ → ℝ) (X : κ → (ι → ℤˣ) → ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) (hμ : ∀ k ∈ s, 0 < μ k) (hX : ∀ k ∈ s, EE (fun ε => X k ε ^ 2) ≤ μ k ^ 2) :
    EE (fun ε => (∑ k ∈ s, w k * |X k ε|) ^ 2) ≤ (∑ k ∈ s, w k * μ k) ^ 2 := by
  set W := ∑ k ∈ s, w k * μ k with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun k hk => mul_nonneg (hw k hk) (hμ k hk).le)
  have hpt : ∀ ε, (∑ k ∈ s, w k * |X k ε|) ^ 2 ≤ W * ∑ k ∈ s, w k * (X k ε ^ 2 / μ k) := by
    intro ε
    have := Finset.sum_mul_sq_le_sq_mul_sq s (fun k => √(w k * μ k)) (fun k => √(w k / μ k) * |X k ε|)
    have e1 : ∀ k ∈ s, √(w k * μ k) * (√(w k / μ k) * |X k ε|) = w k * |X k ε| := by
      intro k hk
      rw [← mul_assoc, ← Real.sqrt_mul (mul_nonneg (hw k hk) (hμ k hk).le)]
      have : w k * μ k * (w k / μ k) = w k ^ 2 := by field_simp [(hμ k hk).ne']
      rw [this, Real.sqrt_sq (hw k hk)]
    have e2 : ∀ k ∈ s, √(w k * μ k) ^ 2 = w k * μ k := fun k hk =>
      Real.sq_sqrt (mul_nonneg (hw k hk) (hμ k hk).le)
    have e3 : ∀ k ∈ s, (√(w k / μ k) * |X k ε|) ^ 2 = w k * (X k ε ^ 2 / μ k) := by
      intro k hk
      rw [mul_pow, Real.sq_sqrt (div_nonneg (hw k hk) (hμ k hk).le), sq_abs]; ring
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3] at this
    exact this
  calc EE (fun ε => (∑ k ∈ s, w k * |X k ε|) ^ 2)
      ≤ EE (fun ε => W * ∑ k ∈ s, w k * (X k ε ^ 2 / μ k)) := EE_mono hpt
    _ = W * ∑ k ∈ s, w k * (EE (fun ε => X k ε ^ 2) / μ k) := by
        rw [EE_smul, EE_sum]; congr 1
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [show (fun ε => w k * (X k ε ^ 2 / μ k)) = (fun ε => (w k / μ k) * X k ε ^ 2) by
          ext ε; ring, EE_smul]; ring
    _ ≤ W * ∑ k ∈ s, w k * (μ k ^ 2 / μ k) := by
        gcongr with k hk
        · exact hw k hk
        · exact (hμ k hk).le
        · exact hX k hk
    _ = W ^ 2 := by
        rw [sq, hW]; congr 1
        refine Finset.sum_congr rfl (fun k hk => ?_)
        field_simp [(hμ k hk).ne']

/-! ### Independence of disjoint coordinate sets -/

/-- `f` only depends on the coordinates in `A`. -/
def DepOn (A : Finset ι) (f : (ι → ℤˣ) → ℝ) : Prop :=
  ∀ ε ε' : ι → ℤˣ, (∀ i ∈ A, ε i = ε' i) → f ε = f ε'

lemma EE_mul_indep (A : Finset ι) (f g : (ι → ℤˣ) → ℝ) (hf : DepOn A f)
    (hg : DepOn Aᶜ g) : EE (fun ε => f ε * g ε) = EE f * EE g := by
  classical
  set p : ι → Prop := fun i => i ∈ A
  let e := Equiv.piEquivPiSubtypeProd p (fun _ => ℤˣ)
  -- glue two partial sign vectors
  let glue : ({i // p i} → ℤˣ) → ({i // ¬ p i} → ℤˣ) → (ι → ℤˣ) := fun α β => e.symm (α, β)
  have hglue1 : ∀ α β, ∀ i (hi : p i), glue α β i = α ⟨i, hi⟩ := by
    intro α β i hi; simp [glue, e, Equiv.piEquivPiSubtypeProd, hi]
  have hglue2 : ∀ α β, ∀ i (hi : ¬ p i), glue α β i = β ⟨i, hi⟩ := by
    intro α β i hi; simp [glue, e, Equiv.piEquivPiSubtypeProd, hi]
  -- choose a reference point
  let β0 : {i // ¬ p i} → ℤˣ := fun _ => 1
  let α0 : {i // p i} → ℤˣ := fun _ => 1
  have hf' : ∀ α β, f (glue α β) = f (glue α β0) := by
    intro α β; apply hf; intro i hi
    rw [hglue1 α β i hi, hglue1 α β0 i hi]
  have hg' : ∀ α β, g (glue α β) = g (glue α0 β) := by
    intro α β; apply hg; intro i hi
    have hi' : ¬ p i := by simpa [p] using hi
    rw [hglue2 α β i hi', hglue2 α0 β i hi']
  have hsum : ∀ F : (ι → ℤˣ) → ℝ, ∑ ε, F ε = ∑ α, ∑ β, F (glue α β) := by
    intro F
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  have hcard : (2 : ℝ) ^ Fintype.card ι
      = (2 : ℝ) ^ Fintype.card {i // p i} * (2 : ℝ) ^ Fintype.card {i // ¬ p i} := by
    rw [← pow_add, Fintype.card_subtype_compl]
    congr 1; have := Fintype.card_subtype_le p; omega
  have hA : ∑ ε, f ε = (∑ α, f (glue α β0)) * 2 ^ Fintype.card {i // ¬ p i} := by
    rw [hsum]; simp_rw [hf']
    rw [Finset.sum_mul]; congr 1; ext α
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    congr 1
    rw [Fintype.card_fun, Fintype.card_units_int]; push_cast; rfl
  have hB : ∑ ε, g ε = (∑ β, g (glue α0 β)) * 2 ^ Fintype.card {i // p i} := by
    rw [hsum, Finset.sum_comm]; simp_rw [hg']
    rw [Finset.sum_mul]; congr 1; ext β
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    congr 1
    rw [Fintype.card_fun, Fintype.card_units_int]; push_cast; rfl
  have hAB : ∑ ε, f ε * g ε = (∑ α, f (glue α β0)) * (∑ β, g (glue α0 β)) := by
    rw [hsum]
    simp_rw [hf', hg']
    rw [Finset.sum_mul_sum]
  unfold EE
  rw [hAB, hA, hB, hcard]
  field_simp

end R522

end S_RR2

-- ===== RR3 =====

/-!
# Erdős 522 (real roots), part 3: a two-point CLT by Fourier inversion

For Schwartz test functions `ψ₁, ψ₂` and unit weight vectors `a, b` with correlation `ρ`,
the sign-vector average of `ψ₁(∑ ε a) ψ₂(∑ ε b)` and the Gaussian average of `ψ₁(Z₁) ψ₂(ρ Z₁ + σ Z₂)`
(`σ² = 1 - ρ²`) are both `∫∫ 𝓕ψ₁ 𝓕ψ₂ · K`, with `K` a cosine product resp. a Gaussian; their
difference is at most `16 (2π)⁴ (M₄ψ₁ M₀ψ₂ ∑ a⁴ + M₀ψ₁ M₄ψ₂ ∑ b⁴)`.
-/

open Finset Real MeasureTheory FourierTransform ProbabilityTheory

noncomputable section S_RR3

namespace R522

lemma schwartz_inv (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    ψ x = ∫ ξ : ℝ, Complex.exp (↑(2 * π * ξ * x) * Complex.I) * 𝓕 (ψ : ℝ → ℂ) ξ := by
  have h := ψ.continuous.fourierInv_fourier_eq ψ.integrable (by
    rw [← SchwartzMap.fourier_coe]; exact (𝓕 ψ).integrable)
  have := congrFun h x
  rw [← this, Real.fourierInv_eq']
  simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
  congr 1; ext ξ; congr 3; push_cast; ring

lemma fourier_integrable (ψ : SchwartzMap ℝ ℂ) : Integrable (𝓕 (ψ : ℝ → ℂ)) := by
  rw [← SchwartzMap.fourier_coe]; exact (𝓕 ψ).integrable

lemma fourier_continuous (ψ : SchwartzMap ℝ ℂ) : Continuous (𝓕 (ψ : ℝ → ℂ)) := by
  rw [← SchwartzMap.fourier_coe]; exact (𝓕 ψ).continuous

lemma integrable_exp_mul_fourier (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    Integrable (fun ξ : ℝ => Complex.exp (↑(2 * π * ξ * x) * Complex.I) * 𝓕 (ψ : ℝ → ℂ) ξ) := by
  refine (fourier_integrable ψ).bdd_mul (c := 1) (by fun_prop) ?_
  refine Filter.Eventually.of_forall (fun ξ => ?_)
  rw [Complex.norm_exp_ofReal_mul_I]

/-- Fourier moments. -/
def Mom (k : ℕ) (ψ : SchwartzMap ℝ ℂ) : ℝ := ∫ u : ℝ, |u| ^ k * ‖𝓕 (ψ : ℝ → ℂ) u‖

lemma integrable_mom (k : ℕ) (ψ : SchwartzMap ℝ ℂ) :
    Integrable (fun u : ℝ => |u| ^ k * ‖𝓕 (ψ : ℝ → ℂ) u‖) := by
  have := (𝓕 ψ).integrable_pow_mul volume k
  rw [SchwartzMap.fourier_coe] at this
  simpa [Real.norm_eq_abs] using this

lemma mom_nonneg (k : ℕ) (ψ : SchwartzMap ℝ ℂ) : 0 ≤ Mom k ψ :=
  integral_nonneg (fun u => by positivity)

lemma mom_zero (ψ : SchwartzMap ℝ ℂ) : Mom 0 ψ = ∫ u : ℝ, ‖𝓕 (ψ : ℝ → ℂ) u‖ := by
  simp [Mom]

/-! ### The sign-vector side -/

lemma sum_units_exp (ξ c : ℝ) :
    ∑ u : ℤˣ, Complex.exp (↑(2 * π * ξ * (((u : ℤ) : ℝ) * c)) * Complex.I)
      = 2 * (Real.cos (2 * π * ξ * c) : ℂ) := by
  rw [show (Finset.univ : Finset ℤˣ) = {1, -1} from by decide]
  rw [Finset.sum_pair (by decide)]
  simp only [Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg, neg_mul]
  rw [Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

lemma sum_signs_exp {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ) (ξ : ℝ) :
    ∑ b : ι → ℤˣ, Complex.exp (↑(2 * π * ξ * ∑ i, ((b i : ℤ) : ℝ) * c i) * Complex.I)
      = ∏ i, 2 * (Real.cos (2 * π * ξ * c i) : ℂ) := by
  have : ∀ b : ι → ℤˣ, Complex.exp (↑(2 * π * ξ * ∑ i, ((b i : ℤ) : ℝ) * c i) * Complex.I)
      = ∏ i, Complex.exp (↑(2 * π * ξ * (((b i : ℤ) : ℝ) * c i)) * Complex.I) := by
    intro b
    rw [← Complex.exp_sum]
    congr 1
    rw [← Finset.sum_mul]
    congr 1
    push_cast
    rw [Finset.mul_sum]
  simp_rw [this]
  rw [← Fintype.prod_sum (fun i (u : ℤˣ) =>
    Complex.exp (↑(2 * π * ξ * (((u : ℤ) : ℝ) * c i)) * Complex.I))]
  simp_rw [sum_units_exp]

/-- **Two-point identity on the sign side.** -/
theorem avg_two {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ₁ ψ₂ : SchwartzMap ℝ ℂ)
    (c d : ι → ℝ) :
    (∑ b : ι → ℤˣ, ψ₁ (ssum b c) * ψ₂ (ssum b d)) / 2 ^ Fintype.card ι
      = ∫ u : ℝ, ∫ v : ℝ, 𝓕 (ψ₁ : ℝ → ℂ) u * 𝓕 (ψ₂ : ℝ → ℂ) v *
          ∏ i, (Real.cos (2 * π * (u * c i + v * d i)) : ℂ) := by
  set F₁ := 𝓕 (ψ₁ : ℝ → ℂ)
  set F₂ := 𝓕 (ψ₂ : ℝ → ℂ)
  have hprod : ∀ x y : ℝ, ψ₁ x * ψ₂ y = ∫ u : ℝ, ∫ v : ℝ,
      Complex.exp (↑(2 * π * u * x) * Complex.I) * Complex.exp (↑(2 * π * v * y) * Complex.I) *
        (F₁ u * F₂ v) := by
    intro x y
    rw [schwartz_inv ψ₁ x, schwartz_inv ψ₂ y, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    simp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    simp only; ring
  have hinner : ∀ (x y u : ℝ), Integrable (fun v : ℝ =>
      Complex.exp (↑(2 * π * u * x) * Complex.I) * Complex.exp (↑(2 * π * v * y) * Complex.I) *
        (F₁ u * F₂ v)) := by
    intro x y u
    have := (integrable_exp_mul_fourier ψ₂ y).const_mul
      (Complex.exp (↑(2 * π * u * x) * Complex.I) * F₁ u)
    refine this.congr (Filter.Eventually.of_forall (fun v => ?_))
    simp only; ring
  have hinner_eval : ∀ (x y u : ℝ), ∫ v : ℝ,
      Complex.exp (↑(2 * π * u * x) * Complex.I) * Complex.exp (↑(2 * π * v * y) * Complex.I) *
        (F₁ u * F₂ v) = Complex.exp (↑(2 * π * u * x) * Complex.I) * F₁ u * ψ₂ y := by
    intro x y u
    rw [schwartz_inv ψ₂ y, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    simp only; ring
  have houter : ∀ x y : ℝ, Integrable (fun u : ℝ => ∫ v : ℝ,
      Complex.exp (↑(2 * π * u * x) * Complex.I) * Complex.exp (↑(2 * π * v * y) * Complex.I) *
        (F₁ u * F₂ v)) := by
    intro x y
    simp_rw [hinner_eval x y]
    exact (integrable_exp_mul_fourier ψ₁ x).mul_const _
  simp_rw [hprod]
  rw [← integral_finsetSum _ (fun b _ => houter _ _)]
  rw [div_eq_mul_inv, mul_comm, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  simp only
  rw [← integral_finsetSum _ (fun b _ => hinner _ _ u)]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  simp only
  have hc : ∀ b : ι → ℤˣ, Complex.exp (↑(2 * π * u * ssum b c) * Complex.I) *
      Complex.exp (↑(2 * π * v * ssum b d) * Complex.I)
      = Complex.exp (↑(2 * π * ∑ i, ((b i : ℤ) : ℝ) * (u * c i + v * d i)) * Complex.I) := by
    intro b
    unfold ssum
    rw [← Complex.exp_add]; congr 1
    push_cast
    simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    rw [← add_mul]; congr 1
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  simp_rw [← mul_assoc, hc]
  have hs := sum_signs_exp (fun i => u * c i + v * d i) 1
  simp only [mul_one] at hs
  rw [← Finset.sum_mul, ← Finset.sum_mul, hs, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ]
  field_simp

/-! ### The Gaussian side -/

/-- Fubini for a probability measure. -/
theorem fub_two {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (ψ₁ ψ₂ : SchwartzMap ℝ ℂ) :
    ∫ ω, ψ₁ (X ω) * ψ₂ (Y ω) ∂μ = ∫ u : ℝ, ∫ v : ℝ, 𝓕 (ψ₁ : ℝ → ℂ) u * 𝓕 (ψ₂ : ℝ → ℂ) v *
      ∫ ω, Complex.exp (↑(2 * π * (u * X ω + v * Y ω)) * Complex.I) ∂μ := by
  set F₁ := 𝓕 (ψ₁ : ℝ → ℂ)
  set F₂ := 𝓕 (ψ₂ : ℝ → ℂ)
  have hF₁ := fourier_integrable ψ₁
  have hF₂ := fourier_integrable ψ₂
  have cF₁ := fourier_continuous ψ₁
  have cF₂ := fourier_continuous ψ₂
  obtain ⟨C₂, hC₂⟩ : ∃ C, ∀ y, ‖ψ₂ y‖ ≤ C := ⟨SchwartzMap.seminorm ℝ 0 0 ψ₂, fun y => by
    have := ψ₂.le_seminorm ℝ 0 0 y; simpa [norm_iteratedFDeriv_zero] using this⟩
  -- step 1: expand `ψ₁` and swap
  have step1 : ∀ ω, ψ₁ (X ω) * ψ₂ (Y ω)
      = ∫ u : ℝ, Complex.exp (↑(2 * π * u * X ω) * Complex.I) * F₁ u * ψ₂ (Y ω) := by
    intro ω; rw [schwartz_inv ψ₁, ← integral_mul_const]
  have int1 : Integrable (Function.uncurry fun (ω : Ω) (u : ℝ) =>
      Complex.exp (↑(2 * π * u * X ω) * Complex.I) * F₁ u * ψ₂ (Y ω)) (μ.prod volume) := by
    refine Integrable.mono' ((integrable_const C₂).mul_prod hF₁.norm) ?_ ?_
    · have m1 : Measurable (fun p : Ω × ℝ => (X p.1, p.2, Y p.1)) :=
        (hX.comp measurable_fst).prodMk (measurable_snd.prodMk (hY.comp measurable_fst))
      have c1 : Continuous (fun q : ℝ × ℝ × ℝ =>
          Complex.exp (↑(2 * π * q.2.1 * q.1) * Complex.I) * F₁ q.2.1 * ψ₂ q.2.2) :=
        ((by fun_prop : Continuous fun (q : ℝ × ℝ × ℝ) =>
          Complex.exp (↑(2 * π * q.2.1 * q.1) * Complex.I)).mul (cF₁.comp (by fun_prop))).mul
          (ψ₂.continuous.comp (by fun_prop))
      exact (c1.measurable.comp m1).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun p => ?_)
      simp only [Function.uncurry, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hC₂ _) (norm_nonneg _)
  have hL : ∫ ω, ψ₁ (X ω) * ψ₂ (Y ω) ∂μ
      = ∫ u : ℝ, F₁ u * ∫ ω, Complex.exp (↑(2 * π * u * X ω) * Complex.I) * ψ₂ (Y ω) ∂μ := by
    simp_rw [step1]
    rw [integral_integral_swap int1]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    simp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
    simp only; ring
  rw [hL]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  simp only
  -- step 2: expand `ψ₂` and swap
  have step2 : ∀ ω, Complex.exp (↑(2 * π * u * X ω) * Complex.I) * ψ₂ (Y ω)
      = ∫ v : ℝ, Complex.exp (↑(2 * π * u * X ω) * Complex.I) *
          Complex.exp (↑(2 * π * v * Y ω) * Complex.I) * F₂ v := by
    intro ω; rw [schwartz_inv ψ₂, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_)); simp only; ring
  have int2 : Integrable (Function.uncurry fun (ω : Ω) (v : ℝ) =>
      Complex.exp (↑(2 * π * u * X ω) * Complex.I) *
          Complex.exp (↑(2 * π * v * Y ω) * Complex.I) * F₂ v) (μ.prod volume) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod hF₂.norm) ?_ ?_
    · have m1 : Measurable (fun p : Ω × ℝ => (X p.1, p.2, Y p.1)) :=
        (hX.comp measurable_fst).prodMk (measurable_snd.prodMk (hY.comp measurable_fst))
      have c1 : Continuous (fun q : ℝ × ℝ × ℝ =>
          Complex.exp (↑(2 * π * u * q.1) * Complex.I) *
            Complex.exp (↑(2 * π * q.2.1 * q.2.2) * Complex.I) * F₂ q.2.1) :=
        (by fun_prop : Continuous fun (q : ℝ × ℝ × ℝ) =>
          Complex.exp (↑(2 * π * u * q.1) * Complex.I) *
            Complex.exp (↑(2 * π * q.2.1 * q.2.2) * Complex.I)).mul (cF₂.comp (by fun_prop))
      exact (c1.measurable.comp m1).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun p => ?_)
      simp only [Function.uncurry, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      exact le_refl _
  simp_rw [step2]
  rw [integral_integral_swap int2, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  simp only
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
  simp only
  rw [show (↑(2 * π * (u * X ω + v * Y ω)) * Complex.I : ℂ)
      = ↑(2 * π * u * X ω) * Complex.I + ↑(2 * π * v * Y ω) * Complex.I by push_cast; ring,
    Complex.exp_add]
  ring

/-- The standard Gaussian. -/
abbrev γ : Measure ℝ := gaussianReal 0 1

lemma gauss_char (t : ℝ) : ∫ x, Complex.exp (↑(t * x) * Complex.I) ∂γ = Complex.exp (-(t ^ 2 / 2 : ℝ)) := by
  have h := charFun_gaussianReal (μ := 0) (v := 1) t
  rw [charFun_apply_real] at h
  rw [show (fun x : ℝ => Complex.exp (↑(t * x) * Complex.I)) = fun x : ℝ => Complex.exp (↑t * ↑x * Complex.I) by
    ext x; push_cast; ring_nf]
  rw [h]; congr 1; push_cast; ring

/-- **Two-point identity on the Gaussian side.** -/
theorem gauss_two (ψ₁ ψ₂ : SchwartzMap ℝ ℂ) (ρ σ : ℝ) :
    ∫ z, ψ₁ z.1 * ψ₂ (ρ * z.1 + σ * z.2) ∂(γ.prod γ)
      = ∫ u : ℝ, ∫ v : ℝ, 𝓕 (ψ₁ : ℝ → ℂ) u * 𝓕 (ψ₂ : ℝ → ℂ) v *
          Complex.exp (-(2 * π ^ 2 * ((u + ρ * v) ^ 2 + σ ^ 2 * v ^ 2) : ℝ)) := by
  rw [fub_two (γ.prod γ) (fun z => z.1) (fun z => ρ * z.1 + σ * z.2) measurable_fst
    (by fun_prop) ψ₁ ψ₂]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  simp only
  congr 1
  have : ∀ z : ℝ × ℝ, Complex.exp (↑(2 * π * (u * z.1 + v * (ρ * z.1 + σ * z.2))) * Complex.I)
      = Complex.exp (↑((2 * π * (u + ρ * v)) * z.1) * Complex.I) *
          Complex.exp (↑((2 * π * σ * v) * z.2) * Complex.I) := by
    intro z; rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp_rw [this]
  rw [integral_prod_mul (fun x => Complex.exp (↑((2 * π * (u + ρ * v)) * x) * Complex.I))
    (fun y => Complex.exp (↑((2 * π * σ * v) * y) * Complex.I)), gauss_char, gauss_char,
    ← Complex.exp_add]
  congr 1; push_cast; ring

/-! ### The error -/

lemma cos_exp_err (θ : ℝ) : |Real.cos θ - Real.exp (-(θ ^ 2 / 2))| ≤ 2 * θ ^ 4 := by
  by_cases hθ : |θ| ≤ 1
  · have h1 := Real.cos_bound hθ
    have hy : |-(θ ^ 2 / 2)| ≤ 1 := by
      rw [abs_neg, abs_of_nonneg (by positivity)]
      have : θ ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg θ]
      linarith
    have h2 := Real.abs_exp_sub_one_sub_id_le hy
    have h4 : |θ| ^ 4 = θ ^ 4 := by rw [← abs_pow]; exact abs_of_nonneg (by positivity)
    rw [h4] at h1
    have : (-(θ ^ 2 / 2)) ^ 2 = θ ^ 4 / 4 := by ring
    rw [this] at h2
    calc |Real.cos θ - Real.exp (-(θ ^ 2 / 2))|
        = |(Real.cos θ - (1 - θ ^ 2 / 2)) - (Real.exp (-(θ ^ 2 / 2)) - 1 - -(θ ^ 2 / 2))| := by
          congr 1; ring
      _ ≤ |Real.cos θ - (1 - θ ^ 2 / 2)| + |Real.exp (-(θ ^ 2 / 2)) - 1 - -(θ ^ 2 / 2)| :=
          abs_sub _ _
      _ ≤ θ ^ 4 * (5 / 96) + θ ^ 4 / 4 := add_le_add h1 h2
      _ ≤ 2 * θ ^ 4 := by nlinarith [pow_nonneg (sq_nonneg θ) 2]
  · push Not at hθ
    have h1 : 1 ≤ θ ^ 4 := by
      have : 1 ≤ |θ| ^ 4 := one_le_pow₀ hθ.le
      rwa [← abs_pow, abs_of_nonneg (by positivity)] at this
    have hc := Real.abs_cos_le_one θ
    have he : |Real.exp (-(θ ^ 2 / 2))| ≤ 1 := by
      rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg θ])
    calc _ ≤ |Real.cos θ| + |Real.exp (-(θ ^ 2 / 2))| := abs_sub _ _
      _ ≤ 2 := by linarith
      _ ≤ 2 * θ ^ 4 := by linarith

lemma prod_sub_prod_le {ι : Type*} (s : Finset ι) (x y : ι → ℝ) (hx : ∀ i ∈ s, |x i| ≤ 1)
    (hy : ∀ i ∈ s, |y i| ≤ 1) : |∏ i ∈ s, x i - ∏ i ∈ s, y i| ≤ ∑ i ∈ s, |x i - y i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have ih' := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
      (fun i hi => hy i (Finset.mem_insert_of_mem hi))
    have hxa := hx a (Finset.mem_insert_self a s)
    have hPy : |∏ i ∈ s, y i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun i _ => abs_nonneg _)
        (fun i hi => hy i (Finset.mem_insert_of_mem hi))
    calc |x a * ∏ i ∈ s, x i - y a * ∏ i ∈ s, y i|
        = |x a * (∏ i ∈ s, x i - ∏ i ∈ s, y i) + (x a - y a) * ∏ i ∈ s, y i| := by congr 1; ring
      _ ≤ |x a| * |∏ i ∈ s, x i - ∏ i ∈ s, y i| + |x a - y a| * |∏ i ∈ s, y i| := by
          refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
      _ ≤ 1 * ∑ i ∈ s, |x i - y i| + |x a - y a| * 1 := by
          gcongr
      _ = |x a - y a| + ∑ i ∈ s, |x i - y i| := by ring

lemma sum_fourth_le (s t : ℝ) (a b : ℝ) : (s * a + t * b) ^ 4 ≤ 8 * (s ^ 4 * a ^ 4 + t ^ 4 * b ^ 4) := by
  nlinarith [sq_nonneg (s * a - t * b), sq_nonneg (s * a + t * b), sq_nonneg ((s*a)^2 - (t*b)^2),
    sq_nonneg (s*a), sq_nonneg (t*b), mul_self_nonneg (s * a * (t * b))]

lemma norm_iter_le {k : ℕ} (f : ℝ → ℝ → ℂ) (a b : Fin k → ℝ → ℝ) (ha : ∀ i, Integrable (a i))
    (hb : ∀ i, Integrable (b i)) (h : ∀ u v, ‖f u v‖ ≤ ∑ i, a i u * b i v) :
    ‖∫ u, ∫ v, f u v‖ ≤ ∑ i, (∫ u, a i u) * (∫ v, b i v) := by
  have hin : ∀ u, ‖∫ v, f u v‖ ≤ ∑ i, a i u * ∫ v, b i v := by
    intro u
    refine (norm_integral_le_of_norm_le (g := fun v => ∑ i, a i u * b i v)
      (integrable_finsetSum _ (fun i _ => (hb i).const_mul _))
      (Filter.Eventually.of_forall (h u))).trans (le_of_eq ?_)
    rw [integral_finsetSum _ (fun i _ => (hb i).const_mul _)]
    exact Finset.sum_congr rfl (fun i _ => integral_const_mul _ _)
  refine (norm_integral_le_of_norm_le (g := fun u => ∑ i, a i u * ∫ v, b i v)
    (integrable_finsetSum _ (fun i _ => (ha i).mul_const _))
    (Filter.Eventually.of_forall hin)).trans (le_of_eq ?_)
  rw [integral_finsetSum _ (fun i _ => (ha i).mul_const _)]
  exact Finset.sum_congr rfl (fun i _ => integral_mul_const _ _)

/-- Integrability of a bounded kernel against `𝓕ψ₁ ⊗ 𝓕ψ₂`. -/
lemma int_kernel (ψ₁ ψ₂ : SchwartzMap ℝ ℂ) (K : ℝ → ℝ → ℂ) (hK : Continuous (Function.uncurry K))
    (hK1 : ∀ u v, ‖K u v‖ ≤ 1) :
    Integrable (Function.uncurry fun u v => 𝓕 (ψ₁ : ℝ → ℂ) u * 𝓕 (ψ₂ : ℝ → ℂ) v * K u v)
      (volume.prod volume) := by
  refine Integrable.mono' ((fourier_integrable ψ₁).norm.mul_prod (fourier_integrable ψ₂).norm) ?_ ?_
  · exact (((fourier_continuous ψ₁).comp continuous_fst).mul
      ((fourier_continuous ψ₂).comp continuous_snd) |>.mul hK).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun p => ?_)
    simp only [Function.uncurry, norm_mul]
    have := hK1 p.1 p.2
    calc ‖𝓕 (ψ₁ : ℝ → ℂ) p.1‖ * ‖𝓕 (ψ₂ : ℝ → ℂ) p.2‖ * ‖K p.1 p.2‖
        ≤ ‖𝓕 (ψ₁ : ℝ → ℂ) p.1‖ * ‖𝓕 (ψ₂ : ℝ → ℂ) p.2‖ * 1 := by gcongr
      _ = _ := by ring

lemma int_kernel_u (ψ₁ ψ₂ : SchwartzMap ℝ ℂ) (K : ℝ → ℝ → ℂ) (hK : ∀ u, Continuous (K u))
    (hK1 : ∀ u v, ‖K u v‖ ≤ 1) (u : ℝ) :
    Integrable (fun v => 𝓕 (ψ₁ : ℝ → ℂ) u * 𝓕 (ψ₂ : ℝ → ℂ) v * K u v) := by
  refine Integrable.mono' ((fourier_integrable ψ₂).norm.const_mul ‖𝓕 (ψ₁ : ℝ → ℂ) u‖) ?_ ?_
  · exact ((continuous_const.mul (fourier_continuous ψ₂)).mul (hK u)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun v => ?_)
    simp only [norm_mul]
    have := hK1 u v
    calc ‖𝓕 (ψ₁ : ℝ → ℂ) u‖ * ‖𝓕 (ψ₂ : ℝ → ℂ) v‖ * ‖K u v‖
        ≤ ‖𝓕 (ψ₁ : ℝ → ℂ) u‖ * ‖𝓕 (ψ₂ : ℝ → ℂ) v‖ * 1 := by gcongr
      _ = _ := by ring

/-- The Gaussian kernel. -/
def gk (ρ : ℝ) (u v : ℝ) : ℝ := Real.exp (-(2 * π ^ 2 * (u ^ 2 + 2 * ρ * u * v + v ^ 2)))

/-- The kernel difference. -/
lemma kernel_diff {ι : Type*} [Fintype ι] (a b : ι → ℝ) (ρ : ℝ) (ha : ∑ i, a i ^ 2 = 1)
    (hb : ∑ i, b i ^ 2 = 1) (hab : ∑ i, a i * b i = ρ) (u v : ℝ) :
    |∏ i, Real.cos (2 * π * (u * a i + v * b i)) - gk ρ u v|
      ≤ 16 * (2 * π) ^ 4 * ((∑ i, a i ^ 4) * u ^ 4 + (∑ i, b i ^ 4) * v ^ 4) := by
  have hg : gk ρ u v = ∏ i, Real.exp (-((2 * π * (u * a i + v * b i)) ^ 2 / 2)) := by
    rw [← Real.exp_sum]; unfold gk; congr 1
    rw [Finset.sum_neg_distrib]
    have : ∑ i, (2 * π * (u * a i + v * b i)) ^ 2 / 2
        = 2 * π ^ 2 * (u ^ 2 * ∑ i, a i ^ 2 + 2 * u * v * ∑ i, a i * b i + v ^ 2 * ∑ i, b i ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [this, ha, hb, hab]; ring
  rw [hg]
  refine (prod_sub_prod_le _ _ _ (fun i _ => Real.abs_cos_le_one _) (fun i _ => by
    rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_one_iff.2 (by
      have := sq_nonneg (2 * π * (u * a i + v * b i)); linarith))).trans ?_
  have hpi : (0 : ℝ) ≤ (2 * π) ^ 4 := by positivity
  calc ∑ i, |Real.cos (2 * π * (u * a i + v * b i)) - Real.exp (-((2 * π * (u * a i + v * b i)) ^ 2 / 2))|
      ≤ ∑ i, 2 * (2 * π * (u * a i + v * b i)) ^ 4 :=
        Finset.sum_le_sum (fun i _ => cos_exp_err _)
    _ ≤ ∑ i, 2 * (2 * π) ^ 4 * (8 * (u ^ 4 * a i ^ 4 + v ^ 4 * b i ^ 4)) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [show (2 * π * (u * a i + v * b i)) ^ 4 = (2 * π) ^ 4 * (u * a i + v * b i) ^ 4 by ring,
          ← mul_assoc]
        exact mul_le_mul_of_nonneg_left (sum_fourth_le u v (a i) (b i)) (by positivity)
    _ = 16 * (2 * π) ^ 4 * ((∑ i, a i ^ 4) * u ^ 4 + (∑ i, b i ^ 4) * v ^ 4) := by
        rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => by ring)

lemma abs_rho_le {ι : Type*} [Fintype ι] (a b : ι → ℝ) (ρ : ℝ) (ha : ∑ i, a i ^ 2 = 1)
    (hb : ∑ i, b i ^ 2 = 1) (hab : ∑ i, a i * b i = ρ) : ρ ^ 2 ≤ 1 := by
  rw [← hab]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  rw [ha, hb, one_mul] at h2; exact h2

lemma gk_le_one (ρ : ℝ) (hρ : ρ ^ 2 ≤ 1) (u v : ℝ) : |gk ρ u v| ≤ 1 := by
  unfold gk
  rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
  have : 0 ≤ u ^ 2 + 2 * ρ * u * v + v ^ 2 := by
    nlinarith [sq_nonneg (u + ρ * v), sq_nonneg v]
  positivity

/-- **Two-point CLT.** -/
theorem clt_two {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ₁ ψ₂ : SchwartzMap ℝ ℂ)
    (a b : ι → ℝ) (ρ : ℝ) (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1)
    (hab : ∑ i, a i * b i = ρ) :
    ‖(∑ ε : ι → ℤˣ, ψ₁ (ssum ε a) * ψ₂ (ssum ε b)) / 2 ^ Fintype.card ι
      - ∫ u : ℝ, ∫ v : ℝ, 𝓕 (ψ₁ : ℝ → ℂ) u * 𝓕 (ψ₂ : ℝ → ℂ) v * (gk ρ u v : ℂ)‖
      ≤ 16 * (2 * π) ^ 4 * (Mom 4 ψ₁ * Mom 0 ψ₂ * ∑ i, a i ^ 4 + Mom 0 ψ₁ * Mom 4 ψ₂ * ∑ i, b i ^ 4) := by
  rw [avg_two]
  have hρ := abs_rho_le a b ρ ha hb hab
  obtain ⟨Kc, hKc⟩ : ∃ K : ℝ → ℝ → ℂ, K = fun u v => ∏ i, (Real.cos (2 * π * (u * a i + v * b i)) : ℂ) :=
    ⟨_, rfl⟩
  obtain ⟨Kg, hKg⟩ : ∃ K : ℝ → ℝ → ℂ, K = fun u v => (gk ρ u v : ℂ) := ⟨_, rfl⟩
  have eC : ∀ u v, (∏ i, (Real.cos (2 * π * (u * a i + v * b i)) : ℂ)) = Kc u v := by
    intro u v; rw [hKc]
  have eG : ∀ u v, ((gk ρ u v : ℝ) : ℂ) = Kg u v := by intro u v; rw [hKg]
  simp_rw [eC, eG]
  have hKc1 : ∀ u v, ‖Kc u v‖ ≤ 1 := by
    intro u v; rw [hKc]; simp only [norm_prod]
    exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hKg1 : ∀ u v, ‖Kg u v‖ ≤ 1 := by
    intro u v; rw [hKg]; simp only [Complex.norm_real, Real.norm_eq_abs]
    exact gk_le_one ρ hρ u v
  have cKc : Continuous (Function.uncurry Kc) := by
    rw [hKc]; exact continuous_finsetProd _ (fun i _ => by fun_prop)
  have cKg : Continuous (Function.uncurry Kg) := by
    rw [hKg]; simp only [gk]; fun_prop
  have hdiff : ∀ u v, ‖Kc u v - Kg u v‖
      ≤ 16 * (2 * π) ^ 4 * ((∑ i, a i ^ 4) * u ^ 4 + (∑ i, b i ^ 4) * v ^ 4) := by
    intro u v
    rw [hKc, hKg]; simp only
    rw [← Complex.ofReal_prod, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact kernel_diff a b ρ ha hb hab u v
  set F₁ := 𝓕 (ψ₁ : ℝ → ℂ)
  set F₂ := 𝓕 (ψ₂ : ℝ → ℂ)
  have iC := int_kernel ψ₁ ψ₂ Kc cKc hKc1
  have iG := int_kernel ψ₁ ψ₂ Kg cKg hKg1
  have iCu := int_kernel_u ψ₁ ψ₂ Kc (fun u => cKc.comp (Continuous.prodMk_right u)) hKc1
  have iGu := int_kernel_u ψ₁ ψ₂ Kg (fun u => cKg.comp (Continuous.prodMk_right u)) hKg1
  have iC' : Integrable (fun u => ∫ v, F₁ u * F₂ v * Kc u v) := iC.integral_prod_left
  have iG' : Integrable (fun u => ∫ v, F₁ u * F₂ v * Kg u v) := iG.integral_prod_left
  rw [← integral_sub iC' iG']
  have : ∀ u, (∫ v, F₁ u * F₂ v * Kc u v) - ∫ v, F₁ u * F₂ v * Kg u v
      = ∫ v, F₁ u * F₂ v * (Kc u v - Kg u v) := by
    intro u; rw [← integral_sub (iCu u) (iGu u)]; congr 1; ext v; ring
  simp_rw [this]
  set A4 := ∑ i, a i ^ 4
  set B4 := ∑ i, b i ^ 4
  set C0 := 16 * (2 * π) ^ 4
  have hA : 0 ≤ A4 := Finset.sum_nonneg (fun i _ => by positivity)
  have hB : 0 ≤ B4 := Finset.sum_nonneg (fun i _ => by positivity)
  have hC0 : 0 ≤ C0 := by positivity
  let fa : Fin 2 → ℝ → ℝ := ![fun u => C0 * A4 * (|u| ^ 4 * ‖F₁ u‖), fun u => C0 * B4 * (|u| ^ 0 * ‖F₁ u‖)]
  let fb : Fin 2 → ℝ → ℝ := ![fun v => |v| ^ 0 * ‖F₂ v‖, fun v => |v| ^ 4 * ‖F₂ v‖]
  have ia : ∀ i, Integrable (fa i) := by
    intro i; fin_cases i
    · exact (integrable_mom 4 ψ₁).const_mul _
    · exact (integrable_mom 0 ψ₁).const_mul _
  have ib : ∀ i, Integrable (fb i) := by
    intro i; fin_cases i
    · exact integrable_mom 0 ψ₂
    · exact integrable_mom 4 ψ₂
  have key := norm_iter_le (k := 2) (fun u v => F₁ u * F₂ v * (Kc u v - Kg u v)) fa fb ia ib (by
    intro u v
    simp only [fa, fb, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, pow_zero, one_mul]
    rw [norm_mul, norm_mul]
    have hu4 : |u| ^ 4 = u ^ 4 := by rw [← abs_pow]; exact abs_of_nonneg (by positivity)
    have hv4 : |v| ^ 4 = v ^ 4 := by rw [← abs_pow]; exact abs_of_nonneg (by positivity)
    rw [hu4, hv4]
    calc ‖F₁ u‖ * ‖F₂ v‖ * ‖Kc u v - Kg u v‖
        ≤ ‖F₁ u‖ * ‖F₂ v‖ * (C0 * (A4 * u ^ 4 + B4 * v ^ 4)) := by
          gcongr; exact hdiff u v
      _ = _ := by ring)
  refine key.trans (le_of_eq ?_)
  simp only [fa, fb, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [integral_const_mul, integral_const_mul]
  unfold Mom
  ring

end R522

end S_RR3

-- ===== RR4 =====

/-!
# Erdős 522 (real roots), part 4: Gaussian facts

* `wedge`: `(γ ⊗ γ) {z₁ > 0, ρ z₁ + σ z₂ < 0} = arccos ρ / (2π)` (polar coordinates).
* `wedge'`: the opposite wedge has the same measure.
* `law_Y`: `ρ z₁ + σ z₂` is standard Gaussian when `ρ² + σ² = 1`.
* `gauss_strip`, `gauss_tail`: `γ [a, a + w] ≤ w / √(2π)`, `γ {R ≤ |x|} ≤ 1 / R²`.
-/

open Finset Real MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section S_RR4

namespace R522

/-- The standard Gaussian density (as `ℝ≥0∞`). -/
abbrev φ : ℝ → ℝ≥0∞ := gaussianPDF 0 1

lemma γ_eq : γ = volume.withDensity φ := gaussianReal_of_var_ne_zero 0 one_ne_zero

lemma γγ_eq : γ.prod γ = (volume : Measure (ℝ × ℝ)).withDensity (fun z => φ z.1 * φ z.2) := by
  rw [γ_eq, prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1),
    Measure.volume_eq_prod]

lemma φ_apply (x : ℝ) : φ x = ENNReal.ofReal ((√(2 * π))⁻¹ * Real.exp (-x ^ 2 / 2)) := by
  simp [φ, gaussianPDF, gaussianPDFReal]

lemma φφ_polar (r θ : ℝ) : φ (r * Real.cos θ) * φ (r * Real.sin θ)
    = ENNReal.ofReal ((2 * π)⁻¹ * Real.exp (-r ^ 2 / 2)) := by
  rw [φ_apply, φ_apply, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have h1 : (√(2 * π))⁻¹ * (√(2 * π))⁻¹ = (2 * π)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  have h2 : Real.exp (-(r * Real.cos θ) ^ 2 / 2) * Real.exp (-(r * Real.sin θ) ^ 2 / 2)
      = Real.exp (-r ^ 2 / 2) := by
    rw [← Real.exp_add]; congr 1
    have := Real.sin_sq_add_cos_sq θ
    have : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
      rw [mul_pow, mul_pow, ← mul_add]; nlinarith
    linarith
  calc (√(2 * π))⁻¹ * Real.exp (-(r * Real.cos θ) ^ 2 / 2) * ((√(2 * π))⁻¹ * Real.exp (-(r * Real.sin θ) ^ 2 / 2))
      = ((√(2 * π))⁻¹ * (√(2 * π))⁻¹) * (Real.exp (-(r * Real.cos θ) ^ 2 / 2) *
          Real.exp (-(r * Real.sin θ) ^ 2 / 2)) := by ring
    _ = _ := by rw [h1, h2]

/-- Angular description of the wedge. -/
lemma wedge_angle {ρ : ℝ} (hρ1 : -1 < ρ) (hρ2 : ρ < 1) {r θ : ℝ} (hr : 0 < r)
    (hθ : θ ∈ Set.Ioo (-π) π) :
    (0 < r * Real.cos θ ∧ ρ * (r * Real.cos θ) + √(1 - ρ ^ 2) * (r * Real.sin θ) < 0)
      ↔ θ ∈ Set.Ioo (-(π / 2)) (Real.arccos ρ - π / 2) := by
  set α := Real.arccos ρ with hα
  have hα0 : 0 < α := Real.arccos_pos.2 hρ2
  have hαπ : α < π := Real.arccos_lt_pi.2 hρ1
  have hcos : Real.cos α = ρ := Real.cos_arccos hρ1.le hρ2.le
  have hsin : Real.sin α = √(1 - ρ ^ 2) := Real.sin_arccos ρ
  have hexp : ρ * (r * Real.cos θ) + √(1 - ρ ^ 2) * (r * Real.sin θ) = r * Real.cos (θ - α) := by
    rw [Real.cos_sub, hcos, hsin]; ring
  rw [hexp]
  have hpos : 0 < r * Real.cos θ ↔ θ ∈ Set.Ioo (-(π / 2)) (π / 2) := by
    rw [mul_pos_iff_of_pos_left hr]
    constructor
    · intro h
      by_contra hn
      simp only [Set.mem_Ioo, not_and_or, not_lt] at hn
      rcases hn with h1 | h1
      · have : Real.cos θ ≤ 0 := by
          rw [← Real.cos_neg]
          exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith [hθ.1])
        linarith
      · have : Real.cos θ ≤ 0 :=
          Real.cos_nonpos_of_pi_div_two_le_of_le h1 (by linarith [hθ.2])
        linarith
    · intro h; exact Real.cos_pos_of_mem_Ioo h
  rw [hpos, mul_neg_iff]
  simp only [Set.mem_Ioo]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    rcases h3 with ⟨_, h3⟩ | ⟨h3, _⟩
    · refine ⟨h1, ?_⟩
      by_contra hn; push Not at hn
      have : 0 ≤ Real.cos (θ - α) := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
      linarith
    · linarith
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, by linarith⟩, Or.inl ⟨hr, ?_⟩⟩
    rw [← Real.cos_neg]
    exact Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)

/-- **The Gaussian wedge.** -/
theorem wedge {ρ : ℝ} (hρ1 : -1 < ρ) (hρ2 : ρ < 1) :
    (γ.prod γ) {z : ℝ × ℝ | 0 < z.1 ∧ ρ * z.1 + √(1 - ρ ^ 2) * z.2 < 0}
      = ENNReal.ofReal (Real.arccos ρ / (2 * π)) := by
  set W := {z : ℝ × ℝ | 0 < z.1 ∧ ρ * z.1 + √(1 - ρ ^ 2) * z.2 < 0} with hW
  have hWm : MeasurableSet W := by
    apply MeasurableSet.inter
    · exact measurableSet_lt measurable_const measurable_fst
    · exact measurableSet_lt (f := fun z : ℝ × ℝ => ρ * z.1 + √(1 - ρ ^ 2) * z.2)
        (g := fun _ => (0 : ℝ)) (by fun_prop) measurable_const
  rw [γγ_eq, withDensity_apply _ hWm, ← lintegral_indicator hWm,
    ← lintegral_comp_polarCoord_symm]
  set α := Real.arccos ρ
  have hα0 : 0 < α := Real.arccos_pos.2 hρ2
  have hαπ : α < π := Real.arccos_lt_pi.2 hρ1
  -- the integrand on the target
  have hpt : ∀ p ∈ polarCoord.target, ENNReal.ofReal p.1 •
      W.indicator (fun z => φ z.1 * φ z.2) (polarCoord.symm p)
      = ENNReal.ofReal (p.1 * ((2 * π)⁻¹ * Real.exp (-p.1 ^ 2 / 2))) *
          (Set.Ioo (-(π / 2)) (α - π / 2)).indicator 1 p.2 := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    simp only [Set.mem_Ioi] at hr
    simp only [smul_eq_mul, polarCoord, OpenPartialHomeomorph.coe_mk_symm, PartialEquiv.coe_symm_mk]
    by_cases hin : θ ∈ Set.Ioo (-(π / 2)) (α - π / 2)
    · have hmem : (r * Real.cos θ, r * Real.sin θ) ∈ W := (wedge_angle hρ1 hρ2 hr hθ).2 hin
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hin, Pi.one_apply, mul_one, φφ_polar,
        ← ENNReal.ofReal_mul hr.le]
    · have hmem : (r * Real.cos θ, r * Real.sin θ) ∉ W := fun h => hin ((wedge_angle hρ1 hρ2 hr hθ).1 h)
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hin, mul_zero, mul_zero]
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hpt]
  have htarget : polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π := rfl
  rw [htarget, Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [lintegral_prod_mul (f := fun r => ENNReal.ofReal (r * ((2 * π)⁻¹ * Real.exp (-r ^ 2 / 2))))
    (g := (Set.Ioo (-(π / 2)) (α - π / 2)).indicator 1)
    ((ENNReal.measurable_ofReal.comp (by fun_prop)).aemeasurable)
    ((measurable_one.indicator measurableSet_Ioo).aemeasurable)]
  -- radial part
  have hrad : ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r * ((2 * π)⁻¹ * Real.exp (-r ^ 2 / 2)))
      = ENNReal.ofReal ((2 * π)⁻¹) := by
    have hint : IntegrableOn (fun r : ℝ => r * ((2 * π)⁻¹ * Real.exp (-r ^ 2 / 2))) (Set.Ioi 0) := by
      have := (integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).integrableOn (s := Set.Ioi 0)
      refine IntegrableOn.congr_fun (this.const_mul (2 * π)⁻¹) (fun r _ => ?_) measurableSet_Ioi
      ring_nf
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem measurableSet_Ioi
      (fun r hr => by simp only [Pi.zero_apply]; have : (0 : ℝ) < r := hr; positivity))]
    · congr 1
      have hc := integral_mul_cexp_neg_mul_sq (b := (1 / 2 : ℂ)) (by norm_num)
      have : ∫ r in Set.Ioi (0 : ℝ), r * Real.exp (-r ^ 2 / 2) = 1 := by
        have h2 : (∫ r in Set.Ioi (0 : ℝ), ((r * Real.exp (-r ^ 2 / 2) : ℝ) : ℂ)) = 1 := by
          rw [show (2 * (1 / 2 : ℂ))⁻¹ = 1 by norm_num] at hc
          rw [← hc]
          refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
          push_cast; congr 2; ring
        rw [integral_complex_ofReal] at h2
        exact_mod_cast h2
      rw [show (fun r : ℝ => r * ((2 * π)⁻¹ * Real.exp (-r ^ 2 / 2)))
          = fun r => (2 * π)⁻¹ * (r * Real.exp (-r ^ 2 / 2)) by ext r; ring,
        integral_const_mul, this, mul_one]
  have hang : ∫⁻ θ in Set.Ioo (-π) π, (Set.Ioo (-(π / 2)) (α - π / 2)).indicator 1 θ
      = ENNReal.ofReal α := by
    rw [lintegral_indicator_one measurableSet_Ioo, Measure.restrict_apply measurableSet_Ioo,
      Set.inter_eq_left.mpr (Set.Ioo_subset_Ioo (by linarith [Real.pi_pos]) (by linarith)),
      Real.volume_Ioo]
    congr 1; ring
  rw [hrad, hang, ← ENNReal.ofReal_mul (by positivity)]
  congr 1; ring

lemma map_neg_γ : γ.map (fun x => -x) = γ := by
  rw [gaussianReal_map_neg, neg_zero]

/-- The opposite wedge. -/
theorem wedge' {ρ : ℝ} (hρ1 : -1 < ρ) (hρ2 : ρ < 1) :
    (γ.prod γ) {z : ℝ × ℝ | z.1 < 0 ∧ 0 < ρ * z.1 + √(1 - ρ ^ 2) * z.2}
      = ENNReal.ofReal (Real.arccos ρ / (2 * π)) := by
  have hW : MeasurableSet {z : ℝ × ℝ | 0 < z.1 ∧ ρ * z.1 + √(1 - ρ ^ 2) * z.2 < 0} := by
    apply MeasurableSet.inter
    · exact measurableSet_lt measurable_const measurable_fst
    · exact measurableSet_lt (f := fun z : ℝ × ℝ => ρ * z.1 + √(1 - ρ ^ 2) * z.2)
        (g := fun _ => (0 : ℝ)) (by fun_prop) measurable_const
  have hm : Measurable (Prod.map (fun x : ℝ => -x) (fun x : ℝ => -x)) := by fun_prop
  have hmap : (γ.prod γ).map (Prod.map (fun x : ℝ => -x) (fun x : ℝ => -x)) = γ.prod γ := by
    rw [← Measure.map_prod_map γ γ (by fun_prop) (by fun_prop), map_neg_γ]
  rw [← wedge hρ1 hρ2, ← hmap, Measure.map_apply hm hW]
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Prod.map_fst, Prod.map_snd]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- The law of `ρ z₁ + σ z₂`. -/
theorem law_Y (ρ σ : ℝ) (h : ρ ^ 2 + σ ^ 2 = 1) :
    (γ.prod γ).map (fun z : ℝ × ℝ => ρ * z.1 + σ * z.2) = γ := by
  have e : (fun z : ℝ × ℝ => ρ * z.1 + σ * z.2)
      = (fun p : ℝ × ℝ => p.1 + p.2) ∘ Prod.map (fun x : ℝ => ρ * x) (fun x : ℝ => σ * x) := by
    ext z; rfl
  rw [e, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map γ γ (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_const_mul]
  change Measure.conv _ _ = _
  rw [gaussianReal_conv_gaussianReal]
  congr 1
  · simp
  · ext; simp [h]

lemma φ_le (x : ℝ) : φ x ≤ ENNReal.ofReal ((√(2 * π))⁻¹) := by
  rw [φ_apply]
  apply ENNReal.ofReal_le_ofReal
  have : Real.exp (-x ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])
  have h0 : 0 ≤ (√(2 * π))⁻¹ := by positivity
  nlinarith

/-- Gaussian strips. -/
theorem gauss_strip (a b : ℝ) (hab : a ≤ b) : γ.real (Set.Icc a b) ≤ (b - a) / √(2 * π) := by
  have h1 : γ (Set.Icc a b) ≤ ENNReal.ofReal ((√(2 * π))⁻¹) * ENNReal.ofReal (b - a) := by
    rw [γ_eq, withDensity_apply _ measurableSet_Icc]
    calc ∫⁻ x in Set.Icc a b, φ x ≤ ∫⁻ _x in Set.Icc a b, ENNReal.ofReal ((√(2 * π))⁻¹) :=
          lintegral_mono (fun x => φ_le x)
      _ = _ := by rw [setLIntegral_const, Real.volume_Icc]
  rw [← ENNReal.ofReal_mul (by positivity)] at h1
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  have hba : 0 ≤ (√(2 * π))⁻¹ * (b - a) := mul_nonneg (by positivity) (by linarith)
  rw [ENNReal.toReal_ofReal hba] at this
  rw [measureReal_def]
  calc _ ≤ (√(2 * π))⁻¹ * (b - a) := this
    _ = _ := by ring

/-- Gaussian tails. -/
theorem gauss_tail {R : ℝ} (hR : 0 < R) : γ.real {x | R ≤ |x|} ≤ 1 / R ^ 2 := by
  have h := meas_ge_le_variance_div_sq (μ := γ) (X := id) (memLp_id_gaussianReal 2) hR
  have e1 : ∫ x, id x ∂γ = 0 := integral_id_gaussianReal
  have e2 : Var[id; γ] = 1 := by rw [variance_id_gaussianReal]; simp
  rw [e1, e2] at h
  simp only [id, sub_zero] at h
  rw [measureReal_def]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal (by positivity)] at this

lemma wedge_real {ρ : ℝ} (hρ1 : -1 < ρ) (hρ2 : ρ < 1) :
    (γ.prod γ).real {z : ℝ × ℝ | 0 < z.1 ∧ ρ * z.1 + √(1 - ρ ^ 2) * z.2 < 0}
      = Real.arccos ρ / (2 * π) := by
  rw [measureReal_def, wedge hρ1 hρ2, ENNReal.toReal_ofReal]
  have := Real.arccos_nonneg ρ; positivity

lemma wedge'_real {ρ : ℝ} (hρ1 : -1 < ρ) (hρ2 : ρ < 1) :
    (γ.prod γ).real {z : ℝ × ℝ | z.1 < 0 ∧ 0 < ρ * z.1 + √(1 - ρ ^ 2) * z.2}
      = Real.arccos ρ / (2 * π) := by
  rw [measureReal_def, wedge' hρ1 hρ2, ENNReal.toReal_ofReal]
  have := Real.arccos_nonneg ρ; positivity

/-- Strips for the second coordinate. -/
theorem strip_Y (ρ σ : ℝ) (h : ρ ^ 2 + σ ^ 2 = 1) (a b : ℝ) (hab : a ≤ b) :
    (γ.prod γ).real {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc a b} ≤ (b - a) / √(2 * π) := by
  have hm : Measurable (fun z : ℝ × ℝ => ρ * z.1 + σ * z.2) := by fun_prop
  have := map_measureReal_apply hm (μ := γ.prod γ) measurableSet_Icc (s := Set.Icc a b)
  rw [law_Y ρ σ h] at this
  rw [show {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc a b}
      = (fun z : ℝ × ℝ => ρ * z.1 + σ * z.2) ⁻¹' Set.Icc a b from rfl, ← this]
  exact gauss_strip a b hab

theorem strip_X (a b : ℝ) (hab : a ≤ b) :
    (γ.prod γ).real {z : ℝ × ℝ | z.1 ∈ Set.Icc a b} ≤ (b - a) / √(2 * π) := by
  have := strip_Y 1 0 (by norm_num) a b hab
  simpa using this

theorem tail_Y (ρ σ : ℝ) (h : ρ ^ 2 + σ ^ 2 = 1) {R : ℝ} (hR : 0 < R) :
    (γ.prod γ).real {z : ℝ × ℝ | R ≤ |ρ * z.1 + σ * z.2|} ≤ 1 / R ^ 2 := by
  have hm : Measurable (fun z : ℝ × ℝ => ρ * z.1 + σ * z.2) := by fun_prop
  have hs : MeasurableSet {x : ℝ | R ≤ |x|} := measurableSet_le measurable_const (by fun_prop)
  have := map_measureReal_apply hm (μ := γ.prod γ) hs
  rw [law_Y ρ σ h] at this
  rw [show {z : ℝ × ℝ | R ≤ |ρ * z.1 + σ * z.2|}
      = (fun z : ℝ × ℝ => ρ * z.1 + σ * z.2) ⁻¹' {x | R ≤ |x|} from rfl, ← this]
  exact gauss_tail hR

theorem tail_X {R : ℝ} (hR : 0 < R) : (γ.prod γ).real {z : ℝ × ℝ | R ≤ |z.1|} ≤ 1 / R ^ 2 := by
  have := tail_Y 1 0 (by norm_num) hR
  simpa using this

end R522

end S_RR4

-- ===== RR5 =====

/-!
# Erdős 522 (real roots), part 5: quadrant probabilities for signed sums

`quad_up`: `P(∑ εa > 0, ∑ εb < 0) ≤ arccos ρ/(2π) + 2w/√(2π) + 2/R² + C·(∑a⁴ + ∑b⁴)`.
`quad_low`: `P(∑ εa > τ, ∑ εb < -τ) ≥ arccos ρ/(2π) - 2(τ+2w)/√(2π) - 2/R² - C·(∑a⁴ + ∑b⁴)`.
The constants only depend on `(τ, R, w)`.
-/

open Finset Real MeasureTheory FourierTransform ProbabilityTheory

noncomputable section S_RR5

namespace R522

/-- A bump: `1` on `[p, q]`, `0` outside `(p - w, q + w)`. -/
def bb (p q w : ℝ) (hpq : p < q) (hw : 0 < w) : ContDiffBump ((p + q) / 2) :=
  ⟨(q - p) / 2, (q - p) / 2 + w, by linarith, by linarith⟩

lemma bb_one {p q w : ℝ} (hpq : p < q) (hw : 0 < w) {x : ℝ} (hx : x ∈ Set.Icc p q) :
    bb p q w hpq hw x = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  rw [Real.closedBall_eq_Icc]
  simp only [bb, Set.mem_Icc] at hx ⊢
  constructor <;> linarith [hx.1, hx.2]

lemma bb_zero {p q w : ℝ} (hpq : p < q) (hw : 0 < w) {x : ℝ} (hx : x ∉ Set.Ioo (p - w) (q + w)) :
    bb p q w hpq hw x = 0 := by
  apply ContDiffBump.zero_of_le_dist
  simp only [bb, Set.mem_Ioo, not_and_or, not_lt] at hx ⊢
  rw [Real.dist_eq]
  rcases hx with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

lemma bb_nonneg (p q w : ℝ) (hpq : p < q) (hw : 0 < w) (x : ℝ) : 0 ≤ bb p q w hpq hw x :=
  ContDiffBump.nonneg _

lemma bb_le_one (p q w : ℝ) (hpq : p < q) (hw : 0 < w) (x : ℝ) : bb p q w hpq hw x ≤ 1 :=
  ContDiffBump.le_one _

/-- The bump as a Schwartz function. -/
def Sb (p q w : ℝ) (hpq : p < q) (hw : 0 < w) : SchwartzMap ℝ ℂ :=
  (((bb p q w hpq hw).hasCompactSupport).comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (bb p q w hpq hw).contDiff)

lemma Sb_apply (p q w : ℝ) (hpq : p < q) (hw : 0 < w) (x : ℝ) :
    Sb p q w hpq hw x = ((bb p q w hpq hw x : ℝ) : ℂ) := rfl

/-- The CLT for bumps, in real form. -/
theorem clt_bb {ι : Type*} [Fintype ι] [DecidableEq ι] {p₁ q₁ w₁ p₂ q₂ w₂ : ℝ}
    (h₁ : p₁ < q₁) (k₁ : 0 < w₁) (h₂ : p₂ < q₂) (k₂ : 0 < w₂)
    (a b : ι → ℝ) (ρ : ℝ) (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1)
    (hab : ∑ i, a i * b i = ρ) :
    |EE (fun ε => bb p₁ q₁ w₁ h₁ k₁ (ssum ε a) * bb p₂ q₂ w₂ h₂ k₂ (ssum ε b))
      - ∫ z, bb p₁ q₁ w₁ h₁ k₁ z.1 * bb p₂ q₂ w₂ h₂ k₂ (ρ * z.1 + √(1 - ρ ^ 2) * z.2) ∂(γ.prod γ)|
      ≤ 16 * (2 * π) ^ 4 * (Mom 4 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 0 (Sb p₂ q₂ w₂ h₂ k₂) * ∑ i, a i ^ 4
          + Mom 0 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 4 (Sb p₂ q₂ w₂ h₂ k₂) * ∑ i, b i ^ 4) := by
  have hρ := abs_rho_le a b ρ ha hb hab
  have h := clt_two (Sb p₁ q₁ w₁ h₁ k₁) (Sb p₂ q₂ w₂ h₂ k₂) a b ρ ha hb hab
  have hσ : √(1 - ρ ^ 2) ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by linarith)
  have hG := gauss_two (Sb p₁ q₁ w₁ h₁ k₁) (Sb p₂ q₂ w₂ h₂ k₂) ρ (√(1 - ρ ^ 2))
  have hk : ∀ u v : ℝ, Complex.exp (-(2 * π ^ 2 * ((u + ρ * v) ^ 2 + √(1 - ρ ^ 2) ^ 2 * v ^ 2) : ℝ))
      = (gk ρ u v : ℂ) := by
    intro u v; unfold gk; rw [hσ, Complex.ofReal_exp]; congr 1; push_cast; ring
  simp_rw [hk] at hG
  rw [← hG] at h
  simp only [Sb_apply] at h
  have e1 : (∑ ε : ι → ℤˣ, ((bb p₁ q₁ w₁ h₁ k₁ (ssum ε a) : ℝ) : ℂ) *
      ((bb p₂ q₂ w₂ h₂ k₂ (ssum ε b) : ℝ) : ℂ)) / 2 ^ Fintype.card ι
      = ((EE (fun ε => bb p₁ q₁ w₁ h₁ k₁ (ssum ε a) * bb p₂ q₂ w₂ h₂ k₂ (ssum ε b)) : ℝ) : ℂ) := by
    unfold EE; push_cast; rfl
  have e2 : ∫ z, ((bb p₁ q₁ w₁ h₁ k₁ z.1 : ℝ) : ℂ) *
      ((bb p₂ q₂ w₂ h₂ k₂ (ρ * z.1 + √(1 - ρ ^ 2) * z.2) : ℝ) : ℂ) ∂(γ.prod γ)
      = ((∫ z, bb p₁ q₁ w₁ h₁ k₁ z.1 * bb p₂ q₂ w₂ h₂ k₂ (ρ * z.1 + √(1 - ρ ^ 2) * z.2)
          ∂(γ.prod γ) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]; push_cast; rfl
  rw [e1, e2, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- Integrals of `[0, 1]`-valued functions vs. measures of sets. -/
lemma integral_le_of_supp {f : ℝ × ℝ → ℝ} (hf : Continuous f) (h0 : ∀ z, 0 ≤ f z)
    (h1 : ∀ z, f z ≤ 1) {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) (hfA : ∀ z, z ∉ A → f z = 0) :
    ∫ z, f z ∂(γ.prod γ) ≤ (γ.prod γ).real A := by
  rw [← integral_indicator_one hA]
  refine integral_mono (Integrable.mono' (integrable_const (1 : ℝ)) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 z)]; exact h1 z)))
    ((integrable_const (1 : ℝ)).indicator hA) (fun z => ?_)
  by_cases hz : z ∈ A
  · rw [Set.indicator_of_mem hz]; exact h1 z
  · rw [Set.indicator_of_notMem hz, hfA z hz]

lemma integral_ge_of_one {f : ℝ × ℝ → ℝ} (hf : Continuous f) (h0 : ∀ z, 0 ≤ f z)
    (h1 : ∀ z, f z ≤ 1) {B : Set (ℝ × ℝ)} (hB : MeasurableSet B) (hfB : ∀ z, z ∈ B → f z = 1) :
    (γ.prod γ).real B ≤ ∫ z, f z ∂(γ.prod γ) := by
  rw [← integral_indicator_one hB]
  refine integral_mono ((integrable_const (1 : ℝ)).indicator hB)
    (Integrable.mono' (integrable_const (1 : ℝ)) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 z)]; exact h1 z)))
    (fun z => ?_)
  by_cases hz : z ∈ B
  · rw [Set.indicator_of_mem hz, hfB z hz]; rfl
  · rw [Set.indicator_of_notMem hz]; exact h0 z

/-- The constant of the quadrant bounds. -/
def Cq (p₁ q₁ w₁ p₂ q₂ w₂ : ℝ) (h₁ : p₁ < q₁) (k₁ : 0 < w₁) (h₂ : p₂ < q₂) (k₂ : 0 < w₂) : ℝ :=
  16 * (2 * π) ^ 4 * (Mom 4 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 0 (Sb p₂ q₂ w₂ h₂ k₂)
    + Mom 0 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 4 (Sb p₂ q₂ w₂ h₂ k₂))

lemma clt_bb' {ι : Type*} [Fintype ι] [DecidableEq ι] {p₁ q₁ w₁ p₂ q₂ w₂ : ℝ}
    (h₁ : p₁ < q₁) (k₁ : 0 < w₁) (h₂ : p₂ < q₂) (k₂ : 0 < w₂)
    (a b : ι → ℝ) (ρ : ℝ) (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1)
    (hab : ∑ i, a i * b i = ρ) :
    |EE (fun ε => bb p₁ q₁ w₁ h₁ k₁ (ssum ε a) * bb p₂ q₂ w₂ h₂ k₂ (ssum ε b))
      - ∫ z, bb p₁ q₁ w₁ h₁ k₁ z.1 * bb p₂ q₂ w₂ h₂ k₂ (ρ * z.1 + √(1 - ρ ^ 2) * z.2) ∂(γ.prod γ)|
      ≤ Cq p₁ q₁ w₁ p₂ q₂ w₂ h₁ k₁ h₂ k₂ * (∑ i, a i ^ 4 + ∑ i, b i ^ 4) := by
  refine (clt_bb h₁ k₁ h₂ k₂ a b ρ ha hb hab).trans ?_
  unfold Cq
  have m1 := mom_nonneg 4 (Sb p₁ q₁ w₁ h₁ k₁)
  have m2 := mom_nonneg 0 (Sb p₂ q₂ w₂ h₂ k₂)
  have m3 := mom_nonneg 0 (Sb p₁ q₁ w₁ h₁ k₁)
  have m4 := mom_nonneg 4 (Sb p₂ q₂ w₂ h₂ k₂)
  have hA : 0 ≤ ∑ i, a i ^ 4 := Finset.sum_nonneg (fun i _ => by positivity)
  have hB : 0 ≤ ∑ i, b i ^ 4 := Finset.sum_nonneg (fun i _ => by positivity)
  have hc : (0 : ℝ) ≤ 16 * (2 * π) ^ 4 := by positivity
  have key : Mom 4 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 0 (Sb p₂ q₂ w₂ h₂ k₂) * ∑ i, a i ^ 4
      + Mom 0 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 4 (Sb p₂ q₂ w₂ h₂ k₂) * ∑ i, b i ^ 4
      ≤ (Mom 4 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 0 (Sb p₂ q₂ w₂ h₂ k₂)
        + Mom 0 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 4 (Sb p₂ q₂ w₂ h₂ k₂)) * (∑ i, a i ^ 4 + ∑ i, b i ^ 4) := by
    nlinarith [mul_nonneg (mul_nonneg m1 m2) hB, mul_nonneg (mul_nonneg m3 m4) hA]
  calc _ ≤ 16 * (2 * π) ^ 4 * ((Mom 4 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 0 (Sb p₂ q₂ w₂ h₂ k₂)
        + Mom 0 (Sb p₁ q₁ w₁ h₁ k₁) * Mom 4 (Sb p₂ q₂ w₂ h₂ k₂)) * (∑ i, a i ^ 4 + ∑ i, b i ^ 4)) :=
        mul_le_mul_of_nonneg_left key hc
    _ = _ := by ring

/-- **Upper quadrant bound.** -/
theorem quad_up {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℝ) (ρ : ℝ)
    (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1) (hab : ∑ i, a i * b i = ρ)
    (hρ1 : -1 < ρ) (hρ2 : ρ < 1) {R w : ℝ} (hR : 0 < R) (hw : 0 < w) :
    PP (fun ε => 0 < ssum ε a ∧ ssum ε b < 0)
      ≤ Real.arccos ρ / (2 * π) + 2 * w / √(2 * π) + 2 / R ^ 2
        + Cq 0 R w (-R) 0 w hR hw (by linarith) hw * (∑ i, a i ^ 4 + ∑ i, b i ^ 4) := by
  classical
  have hR' : -R < 0 := by linarith
  have hclt := clt_bb' hR hw hR' hw a b ρ ha hb hab
  set f₁ := bb 0 R w hR hw
  set f₂ := bb (-R) 0 w hR' hw
  set σ := √(1 - ρ ^ 2) with hσdef
  have hσ : ρ ^ 2 + σ ^ 2 = 1 := by rw [hσdef, Real.sq_sqrt (by nlinarith)]; ring
  -- pointwise
  have hpt : ∀ ε : ι → ℤˣ, (if 0 < ssum ε a ∧ ssum ε b < 0 then (1 : ℝ) else 0)
      ≤ f₁ (ssum ε a) * f₂ (ssum ε b) + (if R ≤ |ssum ε a| then 1 else 0)
        + (if R ≤ |ssum ε b| then 1 else 0) := by
    intro ε
    have n1 := bb_nonneg 0 R w hR hw (ssum ε a)
    have n2 := bb_nonneg (-R) 0 w (by linarith) hw (ssum ε b)
    split_ifs with h hA hB hB <;> try nlinarith
    push Not at hA hB
    rw [abs_lt] at hA hB
    rw [bb_one hR hw ⟨h.1.le, by linarith⟩, bb_one (by linarith) hw ⟨by linarith, h.2.le⟩]
    norm_num
  have hP : PP (fun ε => 0 < ssum ε a ∧ ssum ε b < 0)
      ≤ EE (fun ε => f₁ (ssum ε a) * f₂ (ssum ε b)) + PP (fun ε => R ≤ |ssum ε a|)
        + PP (fun ε => R ≤ |ssum ε b|) := by
    rw [PP_eq, PP_eq, PP_eq, ← EE_add, ← EE_add]
    exact EE_mono hpt
  have t1 := cheb_ssum a hR
  have t2 := cheb_ssum b hR
  rw [ha] at t1; rw [hb] at t2
  -- the Gaussian integral
  have hint : ∫ z, f₁ z.1 * f₂ (ρ * z.1 + σ * z.2) ∂(γ.prod γ)
      ≤ Real.arccos ρ / (2 * π) + 2 * w / √(2 * π) := by
    set A := {z : ℝ × ℝ | z.1 ∈ Set.Ioo (0 - w) (R + w) ∧ ρ * z.1 + σ * z.2 ∈ Set.Ioo (-R - w) (0 + w)}
    have hA : MeasurableSet A := by
      apply MeasurableSet.inter
      · exact measurableSet_Ioo.preimage measurable_fst
      · exact measurableSet_Ioo.preimage (by fun_prop)
    have h1 := integral_le_of_supp (f := fun z : ℝ × ℝ => f₁ z.1 * f₂ (ρ * z.1 + σ * z.2))
      ((f₁.continuous.comp continuous_fst).mul (f₂.continuous.comp (by fun_prop))) (fun z => mul_nonneg (bb_nonneg _ _ _ _ _ _) (bb_nonneg _ _ _ _ _ _))
      (fun z => mul_le_one₀ (bb_le_one _ _ _ _ _ _) (bb_nonneg _ _ _ _ _ _) (bb_le_one _ _ _ _ _ _))
      hA (fun z hz => by
        simp only [A, Set.mem_ofPred_eq, not_and_or] at hz
        rcases hz with hz | hz
        · rw [bb_zero hR hw hz, zero_mul]
        · rw [bb_zero (by linarith) hw hz, mul_zero])
    refine h1.trans ?_
    have hsub : A ⊆ {z : ℝ × ℝ | 0 < z.1 ∧ ρ * z.1 + σ * z.2 < 0} ∪
        {z : ℝ × ℝ | z.1 ∈ Set.Icc (-w) 0} ∪ {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc 0 w} := by
      intro z hz
      simp only [A, Set.mem_ofPred_eq, Set.mem_Ioo] at hz
      simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_Icc]
      by_cases h1 : 0 < z.1
      · by_cases h2 : ρ * z.1 + σ * z.2 < 0
        · exact Or.inl (Or.inl ⟨h1, h2⟩)
        · exact Or.inr ⟨by linarith, by linarith⟩
      · exact Or.inl (Or.inr ⟨by linarith, by linarith⟩)
    calc (γ.prod γ).real A
        ≤ (γ.prod γ).real ({z : ℝ × ℝ | 0 < z.1 ∧ ρ * z.1 + σ * z.2 < 0} ∪
            {z : ℝ × ℝ | z.1 ∈ Set.Icc (-w) 0} ∪ {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc 0 w}) :=
          measureReal_mono hsub
      _ ≤ (γ.prod γ).real {z : ℝ × ℝ | 0 < z.1 ∧ ρ * z.1 + σ * z.2 < 0}
          + (γ.prod γ).real {z : ℝ × ℝ | z.1 ∈ Set.Icc (-w) 0}
          + (γ.prod γ).real {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc 0 w} := by
          refine (measureReal_union_le _ _).trans ?_
          gcongr
          exact measureReal_union_le _ _
      _ ≤ Real.arccos ρ / (2 * π) + (0 - -w) / √(2 * π) + (w - 0) / √(2 * π) := by
          gcongr
          · rw [hσdef, wedge_real hρ1 hρ2]
          · exact strip_X (-w) 0 (by linarith)
          · exact strip_Y ρ σ hσ 0 w hw.le
      _ = _ := by ring
  have hc := (abs_le.mp hclt).2
  have final : PP (fun ε => 0 < ssum ε a ∧ ssum ε b < 0)
      ≤ Real.arccos ρ / (2 * π) + 2 * w / √(2 * π) + 2 / R ^ 2
        + Cq 0 R w (-R) 0 w hR hw hR' hw * (∑ i, a i ^ 4 + ∑ i, b i ^ 4) := by
    have e : (2 : ℝ) / R ^ 2 = 1 / R ^ 2 + 1 / R ^ 2 := by ring
    linarith
  exact final

/-- **Lower quadrant bound (with margin `τ`).** -/
theorem quad_low {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℝ) (ρ : ℝ)
    (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1) (hab : ∑ i, a i * b i = ρ)
    (hρ1 : -1 < ρ) (hρ2 : ρ < 1) {τ R w : ℝ} (hτ : 0 ≤ τ) (hw : 0 < w) (hR : τ + 2 * w < R) :
    Real.arccos ρ / (2 * π) - 2 * (τ + 2 * w) / √(2 * π) - 2 / R ^ 2
        - Cq (τ + 2 * w) R w (-R) (-τ - 2 * w) w hR hw (by linarith) hw
          * (∑ i, a i ^ 4 + ∑ i, b i ^ 4)
      ≤ PP (fun ε => τ < ssum ε a ∧ ssum ε b < -τ) := by
  classical
  have hR0 : 0 < R := by linarith
  have hR' : -R < -τ - 2 * w := by linarith
  have hclt := clt_bb' hR hw hR' hw a b ρ ha hb hab
  set f₁ := bb (τ + 2 * w) R w hR hw
  set f₂ := bb (-R) (-τ - 2 * w) w hR' hw
  set σ := √(1 - ρ ^ 2) with hσdef
  have hσ : ρ ^ 2 + σ ^ 2 = 1 := by rw [hσdef, Real.sq_sqrt (by nlinarith)]; ring
  have hpt : ∀ ε : ι → ℤˣ, f₁ (ssum ε a) * f₂ (ssum ε b)
      ≤ if τ < ssum ε a ∧ ssum ε b < -τ then (1 : ℝ) else 0 := by
    intro ε
    split_ifs with h
    · exact mul_le_one₀ (bb_le_one _ _ _ _ _ _) (bb_nonneg _ _ _ _ _ _) (bb_le_one _ _ _ _ _ _)
    · rw [not_and_or, not_lt, not_lt] at h
      rcases h with h | h
      · rw [bb_zero (p := τ + 2 * w) (q := R) (x := ssum ε a) hR hw
          (by simp only [Set.mem_Ioo, not_and_or, not_lt]; left; linarith), zero_mul]
      · rw [bb_zero (p := -R) (q := -τ - 2 * w) (x := ssum ε b) (by linarith) hw
          (by simp only [Set.mem_Ioo, not_and_or, not_lt]; right; linarith), mul_zero]
  have hP : EE (fun ε => f₁ (ssum ε a) * f₂ (ssum ε b))
      ≤ PP (fun ε => τ < ssum ε a ∧ ssum ε b < -τ) := by rw [PP_eq]; exact EE_mono hpt
  have hint : Real.arccos ρ / (2 * π) - 2 * (τ + 2 * w) / √(2 * π) - 2 / R ^ 2
      ≤ ∫ z, f₁ z.1 * f₂ (ρ * z.1 + σ * z.2) ∂(γ.prod γ) := by
    set B := {z : ℝ × ℝ | z.1 ∈ Set.Icc (τ + 2 * w) R ∧ ρ * z.1 + σ * z.2 ∈ Set.Icc (-R) (-τ - 2 * w)}
    have hB : MeasurableSet B := by
      apply MeasurableSet.inter
      · exact measurableSet_Icc.preimage measurable_fst
      · exact measurableSet_Icc.preimage (by fun_prop)
    have h1 := integral_ge_of_one (f := fun z : ℝ × ℝ => f₁ z.1 * f₂ (ρ * z.1 + σ * z.2))
      ((f₁.continuous.comp continuous_fst).mul (f₂.continuous.comp (by fun_prop))) (fun z => mul_nonneg (bb_nonneg _ _ _ _ _ _) (bb_nonneg _ _ _ _ _ _))
      (fun z => mul_le_one₀ (bb_le_one _ _ _ _ _ _) (bb_nonneg _ _ _ _ _ _) (bb_le_one _ _ _ _ _ _))
      hB (fun z hz => by
        simp only [B, Set.mem_ofPred_eq] at hz
        simp only [f₁, f₂]
        rw [bb_one hR hw hz.1, bb_one (by linarith) hw hz.2, mul_one])
    refine le_trans ?_ h1
    have hsub : {z : ℝ × ℝ | 0 < z.1 ∧ ρ * z.1 + σ * z.2 < 0} ⊆ B ∪
        {z : ℝ × ℝ | z.1 ∈ Set.Icc 0 (τ + 2 * w)} ∪
        {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc (-τ - 2 * w) 0} ∪ {z : ℝ × ℝ | R ≤ |z.1|} ∪
        {z : ℝ × ℝ | R ≤ |ρ * z.1 + σ * z.2|} := by
      intro z ⟨h1, h2⟩
      simp only [B, Set.mem_union, Set.mem_ofPred_eq, Set.mem_Icc]
      by_cases c1 : z.1 ≤ τ + 2 * w
      · left; left; left; right; exact ⟨h1.le, c1⟩
      by_cases c2 : -τ - 2 * w ≤ ρ * z.1 + σ * z.2
      · left; left; right; exact ⟨c2, h2.le⟩
      by_cases c3 : R ≤ |z.1|
      · left; right; exact c3
      by_cases c4 : R ≤ |ρ * z.1 + σ * z.2|
      · right; exact c4
      left; left; left; left
      push Not at c1 c2 c3 c4
      rw [abs_lt] at c3 c4
      exact ⟨⟨c1.le, c3.2.le⟩, ⟨c4.1.le, c2.le⟩⟩
    have hW := wedge_real hρ1 hρ2
    rw [← hσdef] at hW
    have s1 := strip_X 0 (τ + 2 * w) (by linarith)
    have s2 := strip_Y ρ σ hσ (-τ - 2 * w) 0 (by linarith)
    have t1 := tail_X hR0
    have t2 := tail_Y ρ σ hσ hR0
    have hmono := measureReal_mono (μ := γ.prod γ) hsub
    have u1 := measureReal_union_le (μ := γ.prod γ) (B ∪ {z : ℝ × ℝ | z.1 ∈ Set.Icc 0 (τ + 2 * w)} ∪
        {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc (-τ - 2 * w) 0} ∪ {z : ℝ × ℝ | R ≤ |z.1|})
        {z : ℝ × ℝ | R ≤ |ρ * z.1 + σ * z.2|}
    have u2 := measureReal_union_le (μ := γ.prod γ) (B ∪ {z : ℝ × ℝ | z.1 ∈ Set.Icc 0 (τ + 2 * w)} ∪
        {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc (-τ - 2 * w) 0}) {z : ℝ × ℝ | R ≤ |z.1|}
    have u3 := measureReal_union_le (μ := γ.prod γ) (B ∪ {z : ℝ × ℝ | z.1 ∈ Set.Icc 0 (τ + 2 * w)})
        {z : ℝ × ℝ | ρ * z.1 + σ * z.2 ∈ Set.Icc (-τ - 2 * w) 0}
    have u4 := measureReal_union_le (μ := γ.prod γ) B {z : ℝ × ℝ | z.1 ∈ Set.Icc 0 (τ + 2 * w)}
    have e1 : (τ + 2 * w - 0) / √(2 * π) + (0 - (-τ - 2 * w)) / √(2 * π)
        = 2 * (τ + 2 * w) / √(2 * π) := by ring
    have e2 : 1 / R ^ 2 + 1 / R ^ 2 = 2 / R ^ 2 := by ring
    linarith
  have hc := (abs_le.mp hclt).1
  have final : Real.arccos ρ / (2 * π) - 2 * (τ + 2 * w) / √(2 * π) - 2 / R ^ 2
        - Cq (τ + 2 * w) R w (-R) (-τ - 2 * w) w hR hw hR' hw * (∑ i, a i ^ 4 + ∑ i, b i ^ 4)
      ≤ PP (fun ε => τ < ssum ε a ∧ ssum ε b < -τ) := by linarith
  exact final

end R522

end S_RR5

end S_C4

-- ===== C5 =====
section S_C5

/-! A two-point *local* smoothing estimate: the cosine-product kernel is compared with the
Gaussian kernel only on a box `|u|, |v| ≤ R`; outside the box but inside the cell
`|u| ≤ U, |v| ≤ V` both kernels are assumed small, and beyond the cell the Fourier tails of the
test functions are used (original). -/

open Finset Real MeasureTheory FourierTransform ProbabilityTheory

noncomputable section

namespace R522

/-- the cosine kernel -/
def Kc {ι : Type*} [Fintype ι] (a b : ι → ℝ) (u v : ℝ) : ℝ :=
  ∏ i, Real.cos (2 * π * (u * a i + v * b i))

lemma Kc_abs_le_one {ι : Type*} [Fintype ι] (a b : ι → ℝ) (u v : ℝ) : |Kc a b u v| ≤ 1 := by
  unfold Kc; rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun i _ => abs_nonneg _) (fun i _ => Real.abs_cos_le_one _)

/-- Fourier tail mass. -/
def Tail (ψ : SchwartzMap ℝ ℂ) (U : ℝ) : ℝ :=
  ∫ u, Set.indicator {u : ℝ | U < |u|} (fun u => ‖𝓕 (ψ : ℝ → ℂ) u‖) u

lemma integrable_ind_le (c R : ℝ) :
    Integrable (Set.indicator {u : ℝ | |u| ≤ R} (fun _ => c)) := by
  have : {u : ℝ | |u| ≤ R} = Set.Icc (-R) R := by ext u; simp [abs_le]
  rw [this]
  exact (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc

lemma integral_ind_le (c R : ℝ) (hR : 0 ≤ R) :
    ∫ u, Set.indicator {u : ℝ | |u| ≤ R} (fun _ => c) u = c * (2 * R) := by
  have : {u : ℝ | |u| ≤ R} = Set.Icc (-R) R := by ext u; simp [abs_le]
  rw [this, integral_indicator measurableSet_Icc, setIntegral_const]
  simp only [Measure.real, Real.volume_Icc, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by linarith)]; ring

lemma integrable_ind_gt (ψ : SchwartzMap ℝ ℂ) (U : ℝ) :
    Integrable (Set.indicator {u : ℝ | U < |u|} (fun u => ‖𝓕 (ψ : ℝ → ℂ) u‖)) :=
  (fourier_integrable ψ).norm.indicator (measurableSet_lt measurable_const measurable_abs)

lemma integrable_ind_le_f (ψ : SchwartzMap ℝ ℂ) (U c : ℝ) :
    Integrable (Set.indicator {u : ℝ | |u| ≤ U} (fun _ => c)) := integrable_ind_le c U

/-- **Two-point local estimate.** -/
theorem llt_two {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ₁ ψ₂ : SchwartzMap ℝ ℂ)
    (a b : ι → ℝ) (ρ : ℝ) (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1)
    (hab : ∑ i, a i * b i = ρ) {R U V η M₁ M₂ : ℝ} (hR : 0 ≤ R) (hU : 0 ≤ U) (hη : 0 ≤ η)
    (hM₁ : ∀ u, ‖𝓕 (ψ₁ : ℝ → ℂ) u‖ ≤ M₁) (hM₂ : ∀ v, ‖𝓕 (ψ₂ : ℝ → ℂ) v‖ ≤ M₂)
    (hdec : ∀ u v, |u| ≤ U → |v| ≤ V → (R < |u| ∨ R < |v|) → |Kc a b u v| + gk ρ u v ≤ η) :
    ‖(∑ ε : ι → ℤˣ, ψ₁ (ssum ε a) * ψ₂ (ssum ε b)) / 2 ^ Fintype.card ι
      - ∫ u : ℝ, ∫ v : ℝ, 𝓕 (ψ₁ : ℝ → ℂ) u * 𝓕 (ψ₂ : ℝ → ℂ) v * (gk ρ u v : ℂ)‖
      ≤ (M₁ * (16 * (2 * π) ^ 4 * R ^ 4 * ((∑ i, a i ^ 4) + ∑ i, b i ^ 4))) * (2 * R) * (M₂ * (2 * R))
        + (M₁ * η) * (2 * U) * Mom 0 ψ₂ + 2 * Tail ψ₁ U * Mom 0 ψ₂ + 2 * Mom 0 ψ₁ * Tail ψ₂ V := by
  rw [avg_two]
  have hρ := abs_rho_le a b ρ ha hb hab
  obtain ⟨KC, hKC⟩ : ∃ K : ℝ → ℝ → ℂ, K = fun u v => ∏ i, (Real.cos (2 * π * (u * a i + v * b i)) : ℂ) :=
    ⟨_, rfl⟩
  obtain ⟨KG, hKG⟩ : ∃ K : ℝ → ℝ → ℂ, K = fun u v => (gk ρ u v : ℂ) := ⟨_, rfl⟩
  have eC : ∀ u v, (∏ i, (Real.cos (2 * π * (u * a i + v * b i)) : ℂ)) = KC u v := by
    intro u v; rw [hKC]
  have eG : ∀ u v, ((gk ρ u v : ℝ) : ℂ) = KG u v := by intro u v; rw [hKG]
  simp_rw [eC, eG]
  have hKC1 : ∀ u v, ‖KC u v‖ ≤ 1 := by
    intro u v; rw [hKC]; simp only [norm_prod]
    exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hKG1 : ∀ u v, ‖KG u v‖ ≤ 1 := by
    intro u v; rw [hKG]; simp only [Complex.norm_real, Real.norm_eq_abs]
    exact gk_le_one ρ hρ u v
  have cKC : Continuous (Function.uncurry KC) := by
    rw [hKC]; exact continuous_finsetProd _ (fun i _ => by fun_prop)
  have cKG : Continuous (Function.uncurry KG) := by
    rw [hKG]; simp only [gk]; fun_prop
  have hKCnorm : ∀ u v, ‖KC u v‖ = |Kc a b u v| := by
    intro u v; rw [hKC]; simp only [Kc]
    rw [← Complex.ofReal_prod, Complex.norm_real, Real.norm_eq_abs]
  have hKGnorm : ∀ u v, ‖KG u v‖ = gk ρ u v := by
    intro u v; rw [hKG]; simp only [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (Real.exp_pos _)
  have hdiff : ∀ u v, ‖KC u v - KG u v‖
      ≤ 16 * (2 * π) ^ 4 * ((∑ i, a i ^ 4) * u ^ 4 + (∑ i, b i ^ 4) * v ^ 4) := by
    intro u v
    rw [hKC, hKG]; simp only
    rw [← Complex.ofReal_prod, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact kernel_diff a b ρ ha hb hab u v
  set F₁ := 𝓕 (ψ₁ : ℝ → ℂ)
  set F₂ := 𝓕 (ψ₂ : ℝ → ℂ)
  have iC := int_kernel ψ₁ ψ₂ KC cKC hKC1
  have iG := int_kernel ψ₁ ψ₂ KG cKG hKG1
  have iCu := int_kernel_u ψ₁ ψ₂ KC (fun u => cKC.comp (Continuous.prodMk_right u)) hKC1
  have iGu := int_kernel_u ψ₁ ψ₂ KG (fun u => cKG.comp (Continuous.prodMk_right u)) hKG1
  have iC' : Integrable (fun u => ∫ v, F₁ u * F₂ v * KC u v) := iC.integral_prod_left
  have iG' : Integrable (fun u => ∫ v, F₁ u * F₂ v * KG u v) := iG.integral_prod_left
  rw [← integral_sub iC' iG']
  have : ∀ u, (∫ v, F₁ u * F₂ v * KC u v) - ∫ v, F₁ u * F₂ v * KG u v
      = ∫ v, F₁ u * F₂ v * (KC u v - KG u v) := by
    intro u; rw [← integral_sub (iCu u) (iGu u)]; congr 1; ext v; ring
  simp_rw [this]
  set A4 := ∑ i, a i ^ 4
  set B4 := ∑ i, b i ^ 4
  set E := 16 * (2 * π) ^ 4 * R ^ 4 * (A4 + B4)
  have hA : 0 ≤ A4 := Finset.sum_nonneg (fun i _ => by positivity)
  have hB : 0 ≤ B4 := Finset.sum_nonneg (fun i _ => by positivity)
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ 0)
  let SR : Set ℝ := {u | |u| ≤ R}
  let SU : Set ℝ := {u | |u| ≤ U}
  let GU : Set ℝ := {u | U < |u|}
  let GV : Set ℝ := {u | V < |u|}
  let fa : Fin 4 → ℝ → ℝ := ![Set.indicator SR (fun _ => M₁ * E), Set.indicator SU (fun _ => M₁ * η),
    fun u => 2 * Set.indicator GU (fun u => ‖F₁ u‖) u, fun u => 2 * ‖F₁ u‖]
  let fb : Fin 4 → ℝ → ℝ := ![Set.indicator SR (fun _ => M₂), fun v => ‖F₂ v‖, fun v => ‖F₂ v‖,
    Set.indicator GV (fun v => ‖F₂ v‖)]
  have ia : ∀ i, Integrable (fa i) := by
    intro i; fin_cases i
    · exact integrable_ind_le _ _
    · exact integrable_ind_le _ _
    · exact (integrable_ind_gt ψ₁ U).const_mul 2
    · exact (fourier_integrable ψ₁).norm.const_mul 2
  have ib : ∀ i, Integrable (fb i) := by
    intro i; fin_cases i
    · exact integrable_ind_le _ _
    · exact (fourier_integrable ψ₂).norm
    · exact (fourier_integrable ψ₂).norm
    · exact integrable_ind_gt ψ₂ V
  have key := norm_iter_le (k := 4) (fun u v => F₁ u * F₂ v * (KC u v - KG u v)) fa fb ia ib (by
    intro u v
    simp only [fa, fb, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
    rw [norm_mul, norm_mul]
    have n1 := norm_nonneg (F₁ u)
    have n2 := norm_nonneg (F₂ v)
    have hE0 : 0 ≤ E := by positivity
    have hK2 : ‖KC u v - KG u v‖ ≤ 2 := by
      calc ‖KC u v - KG u v‖ ≤ ‖KC u v‖ + ‖KG u v‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (hKC1 u v) (hKG1 u v)
        _ = 2 := by norm_num
    have T0 : 0 ≤ Set.indicator SR (fun _ => M₁ * E) u * Set.indicator SR (fun _ => M₂) v := by
      apply mul_nonneg <;> apply Set.indicator_nonneg <;> intro _ _ <;> positivity
    have T1 : 0 ≤ Set.indicator SU (fun _ => M₁ * η) u * ‖F₂ v‖ := by
      apply mul_nonneg _ n2; apply Set.indicator_nonneg; intro _ _; positivity
    have T2 : 0 ≤ 2 * Set.indicator GU (fun u => ‖F₁ u‖) u * ‖F₂ v‖ := by
      apply mul_nonneg _ n2; apply mul_nonneg (by norm_num)
      apply Set.indicator_nonneg; intro _ _; positivity
    have T3 : 0 ≤ 2 * ‖F₁ u‖ * Set.indicator GV (fun v => ‖F₂ v‖) v := by
      apply mul_nonneg (by positivity); apply Set.indicator_nonneg; intro _ _; positivity
    by_cases hbox : |u| ≤ R ∧ |v| ≤ R
    · have h1 : Set.indicator SR (fun _ => M₁ * E) u = M₁ * E := Set.indicator_of_mem (show u ∈ SR from hbox.1) _
      have h2 : Set.indicator SR (fun _ => M₂) v = M₂ := Set.indicator_of_mem (show v ∈ SR from hbox.2) _
      have hd := hdiff u v
      have hu4 : u ^ 4 ≤ R ^ 4 := by
        have := pow_le_pow_left₀ (abs_nonneg u) hbox.1 4
        rwa [show |u| ^ 4 = u ^ 4 by rw [← abs_pow]; exact abs_of_nonneg (by positivity)] at this
      have hv4 : v ^ 4 ≤ R ^ 4 := by
        have := pow_le_pow_left₀ (abs_nonneg v) hbox.2 4
        rwa [show |v| ^ 4 = v ^ 4 by rw [← abs_pow]; exact abs_of_nonneg (by positivity)] at this
      have hd' : ‖KC u v - KG u v‖ ≤ E := by
        refine hd.trans ?_
        simp only [E]
        have : A4 * u ^ 4 + B4 * v ^ 4 ≤ R ^ 4 * (A4 + B4) := by nlinarith
        nlinarith [show (0:ℝ) ≤ 16 * (2 * π) ^ 4 by positivity]
      have : ‖F₁ u‖ * ‖F₂ v‖ * ‖KC u v - KG u v‖ ≤ M₁ * E * M₂ := by
        calc ‖F₁ u‖ * ‖F₂ v‖ * ‖KC u v - KG u v‖ ≤ M₁ * M₂ * E := by
              gcongr
              · exact hM₁ u
              · exact hM₂ v
          _ = M₁ * E * M₂ := by ring
      rw [h1, h2]; linarith
    · by_cases hu : |u| ≤ U
      · by_cases hv : |v| ≤ V
        · have hout : R < |u| ∨ R < |v| := by
            by_contra hc; push Not at hc; exact hbox ⟨hc.1, hc.2⟩
          have hd := hdec u v hu hv hout
          have hK : ‖KC u v - KG u v‖ ≤ η := by
            calc ‖KC u v - KG u v‖ ≤ ‖KC u v‖ + ‖KG u v‖ := norm_sub_le _ _
              _ = |Kc a b u v| + gk ρ u v := by rw [hKCnorm, hKGnorm]
              _ ≤ η := hd
          have h1 : Set.indicator SU (fun _ => M₁ * η) u = M₁ * η := Set.indicator_of_mem (show u ∈ SU from hu) _
          have : ‖F₁ u‖ * ‖F₂ v‖ * ‖KC u v - KG u v‖ ≤ M₁ * η * ‖F₂ v‖ := by
            calc ‖F₁ u‖ * ‖F₂ v‖ * ‖KC u v - KG u v‖ ≤ M₁ * ‖F₂ v‖ * η := by
                  gcongr; exact hM₁ u
              _ = M₁ * η * ‖F₂ v‖ := by ring
          rw [h1]; linarith
        · have h3 : Set.indicator GV (fun v => ‖F₂ v‖) v = ‖F₂ v‖ :=
            Set.indicator_of_mem (show v ∈ GV from lt_of_not_ge hv) _
          have : ‖F₁ u‖ * ‖F₂ v‖ * ‖KC u v - KG u v‖ ≤ 2 * ‖F₁ u‖ * ‖F₂ v‖ := by
            calc ‖F₁ u‖ * ‖F₂ v‖ * ‖KC u v - KG u v‖ ≤ ‖F₁ u‖ * ‖F₂ v‖ * 2 := by gcongr
              _ = _ := by ring
          rw [h3]; linarith
      · have h3 : Set.indicator GU (fun u => ‖F₁ u‖) u = ‖F₁ u‖ :=
          Set.indicator_of_mem (show u ∈ GU from lt_of_not_ge hu) _
        have : ‖F₁ u‖ * ‖F₂ v‖ * ‖KC u v - KG u v‖ ≤ 2 * ‖F₁ u‖ * ‖F₂ v‖ := by
          calc ‖F₁ u‖ * ‖F₂ v‖ * ‖KC u v - KG u v‖ ≤ ‖F₁ u‖ * ‖F₂ v‖ * 2 := by gcongr
            _ = _ := by ring
        rw [h3]; linarith)
  refine key.trans (le_of_eq ?_)
  simp only [fa, fb, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
  rw [integral_ind_le _ _ hR, integral_ind_le _ _ hR, integral_ind_le _ _ hU, integral_const_mul,
    integral_const_mul]
  unfold Tail Mom
  simp only [pow_zero, one_mul]
  ring

end R522
end

end S_C5

-- ===== C6 =====
section S_C6

/-! Decay of cosine products over arithmetic progressions (original). -/

open Finset Real

noncomputable section

namespace R522

lemma abs_cos_le_exp_sin (x : ℝ) : |Real.cos x| ≤ Real.exp (-(Real.sin x ^ 2 / 2)) := by
  have h1 : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by rw [← Real.sin_sq_add_cos_sq x]; ring
  have h2 : 1 - Real.sin x ^ 2 ≤ Real.exp (-(Real.sin x ^ 2)) := by
    have := Real.add_one_le_exp (-(Real.sin x ^ 2)); linarith
  have h3 : |Real.cos x| ^ 2 ≤ Real.exp (-(Real.sin x ^ 2 / 2)) ^ 2 := by
    rw [sq_abs, h1, ← Real.exp_nat_mul]; push_cast
    calc 1 - Real.sin x ^ 2 ≤ Real.exp (-(Real.sin x ^ 2)) := h2
      _ = Real.exp (2 * -(Real.sin x ^ 2 / 2)) := by ring_nf
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (Real.exp_pos _).le two_ne_zero).mp h3

lemma abs_prod_cos_le {n : ℕ} (θ : ℕ → ℝ) :
    |∏ w ∈ range n, Real.cos (θ w)| ≤ Real.exp (-((∑ w ∈ range n, Real.sin (θ w) ^ 2) / 2)) := by
  rw [Finset.abs_prod, Finset.sum_div, ← Finset.sum_neg_distrib, Real.exp_sum]
  exact Finset.prod_le_prod (fun w _ => abs_nonneg _) (fun w _ => abs_cos_le_exp_sin _)

lemma sin_sq_sub_le (x y : ℝ) : Real.sin (x - y) ^ 2 ≤ 2 * (Real.sin x ^ 2 + Real.sin y ^ 2) := by
  rw [Real.sin_sub]
  nlinarith [Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y,
    sq_nonneg (Real.sin x * Real.cos y + Real.cos x * Real.sin y),
    sq_nonneg (Real.sin x * Real.cos y), sq_nonneg (Real.cos x * Real.sin y)]

/-- pairing at gap `d` -/
lemma sum_sin_sq_ge_pair (n d : ℕ) (hd : d ≤ n) (s t : ℝ) :
    ((n - d : ℕ) : ℝ) * Real.sin (d * s) ^ 2 ≤ 4 * ∑ w ∈ range n, Real.sin (s * w + t) ^ 2 := by
  have hpair : ∀ w : ℕ, Real.sin (d * s) ^ 2 ≤
      2 * (Real.sin (s * (w + d : ℕ) + t) ^ 2 + Real.sin (s * w + t) ^ 2) := by
    intro w
    have := sin_sq_sub_le (s * (w + d : ℕ) + t) (s * w + t)
    have e : s * ((w + d : ℕ) : ℝ) + t - (s * w + t) = d * s := by push_cast; ring
    rwa [e] at this
  have hsum := Finset.sum_le_sum (s := range (n - d)) (fun w _ => hpair w)
  rw [sum_const, card_range, nsmul_eq_mul] at hsum
  rw [← mul_sum, sum_add_distrib] at hsum
  have h1 : ∑ w ∈ range (n - d), Real.sin (s * ((w + d : ℕ) : ℝ) + t) ^ 2 ≤
      ∑ w ∈ range n, Real.sin (s * w + t) ^ 2 := by
    have e : ∑ w ∈ range (n - d), Real.sin (s * ((w + d : ℕ) : ℝ) + t) ^ 2 =
        ∑ w ∈ Ico d n, Real.sin (s * (w : ℝ) + t) ^ 2 := by
      rw [sum_Ico_eq_sum_range]; apply sum_congr rfl; intro w _; rw [add_comm w d]
    rw [e]
    exact sum_le_sum_of_subset_of_nonneg (fun x hx => by
      rw [mem_Ico] at hx; rw [mem_range]; omega) (fun _ _ _ => by positivity)
  have h2 : ∑ w ∈ range (n - d), Real.sin (s * (w : ℝ) + t) ^ 2 ≤
      ∑ w ∈ range n, Real.sin (s * w + t) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (fun x hx => by rw [mem_range] at hx ⊢; omega) (fun _ _ _ => by positivity)
  linarith

lemma sin_half_le_sin {x : ℝ} (h1 : 1 / 2 ≤ |x|) (h2 : |x| ≤ 5 / 2) :
    Real.sin (1 / 2) ^ 2 ≤ Real.sin x ^ 2 := by
  have hsa : Real.sin x ^ 2 = Real.sin |x| ^ 2 := by
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
    rw [Real.sin_neg]; ring
  rw [hsa]
  have hpi := Real.pi_gt_three
  have key : Real.sin (1 / 2) ≤ Real.sin |x| := by
    rcases le_or_gt |x| (π / 2) with h | h
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h h1
    · rw [← Real.sin_pi_sub |x|]
      apply Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith)
      linarith
  have h0 : 0 ≤ Real.sin (1 / 2) := Real.sin_nonneg_of_nonneg_of_le_pi (by norm_num) (by linarith)
  nlinarith

/-- **Case A**: a non-tiny step gives linear decay. -/
lemma sum_sin_sq_caseA (n : ℕ) (s t : ℝ) (hs1 : 8 / n ≤ |s|) (hs2 : |s| ≤ 2) (hn : 16 ≤ n) :
    (n : ℝ) * Real.sin (1 / 2) ^ 2 ≤ 8 * ∑ w ∈ range n, Real.sin (s * w + t) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hsp : 0 < |s| := lt_of_lt_of_le (by positivity) hs1
  set d := ⌈1 / (2 * |s|)⌉₊ with hd
  have hd1 : 1 / (2 * |s|) ≤ d := Nat.le_ceil _
  have hd2 : (d : ℝ) < 1 / (2 * |s|) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hdn : (d : ℝ) ≤ n / 2 := by
    have : 1 / (2 * |s|) ≤ n / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : 8 ≤ |s| * n := by rwa [div_le_iff₀ hn0] at hs1
      nlinarith
    have : (16 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hdn' : d ≤ n := by
    have : (d : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hds1 : 1 / 2 ≤ |d * s| := by
    rw [abs_mul, Nat.abs_cast]
    have := mul_le_mul_of_nonneg_right hd1 hsp.le
    rwa [show 1 / (2 * |s|) * |s| = 1 / 2 by field_simp] at this
  have hds2 : |d * s| ≤ 5 / 2 := by
    rw [abs_mul, Nat.abs_cast]
    have := mul_le_mul_of_nonneg_right hd2.le hsp.le
    rw [add_mul, show 1 / (2 * |s|) * |s| = 1 / 2 by field_simp, one_mul] at this
    linarith
  have hsin := sin_half_le_sin hds1 hds2
  have hp := sum_sin_sq_ge_pair n d hdn' s t
  have hnd : (n : ℝ) / 2 ≤ ((n - d : ℕ) : ℝ) := by
    rw [Nat.cast_sub hdn']; linarith
  have h0 : 0 ≤ Real.sin (1 / 2) ^ 2 := by positivity
  nlinarith

lemma sum_sq_range_mul_six (m : ℕ) :
    (∑ w ∈ range m, (w : ℝ) ^ 2) * 6 = (m : ℝ) * (m - 1) * (2 * m - 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, add_mul, ih]; push_cast; ring

/-- the quadratic form of an arithmetic progression is comparable to its diagonal. -/
lemma ap_quad_ge (m : ℕ) (s t : ℝ) :
    ((m : ℝ) * t ^ 2 + (∑ w ∈ range m, (w : ℝ) ^ 2) * s ^ 2) / 8 ≤
      ∑ w ∈ range m, (t + s * w) ^ 2 := by
  have hA : ∑ w ∈ range m, (t + s * w) ^ 2 =
      m * t ^ 2 + 2 * (∑ w ∈ range m, (w : ℝ)) * t * s + (∑ w ∈ range m, (w : ℝ) ^ 2) * s ^ 2 := by
    rw [show (m : ℝ) * t ^ 2 = ∑ w ∈ range m, t ^ 2 by simp]
    rw [mul_sum, sum_mul, sum_mul, sum_mul, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl; intro w _; ring
  -- B^2 ≤ (3/4) A C
  have hB : (∑ w ∈ range m, (w : ℝ)) ^ 2 * 4 ≤ 3 * (m : ℝ) * ∑ w ∈ range m, (w : ℝ) ^ 2 := by
    have e1 : (∑ w ∈ range m, (w : ℝ)) * 2 = (m : ℝ) * (m - 1) := by
      have := Finset.sum_range_id_mul_two m
      have h' : ((∑ w ∈ range m, w : ℕ) : ℝ) * 2 = (m : ℝ) * ((m - 1 : ℕ) : ℝ) := by exact_mod_cast this
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp
      · rw [Nat.cast_sub h, Nat.cast_one] at h'; push_cast at h'; linarith
    have e2 := sum_sq_range_mul_six m
    have hm : (0 : ℝ) ≤ m := by positivity
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h
      nlinarith [mul_nonneg hm (sub_nonneg.mpr hm1), sq_nonneg ((m : ℝ) - 1)]
  rw [hA]
  set A := (m : ℝ)
  set B := ∑ w ∈ range m, (w : ℝ)
  set C := ∑ w ∈ range m, (w : ℝ) ^ 2
  have hA0 : 0 ≤ A := by positivity
  have hC0 : 0 ≤ C := sum_nonneg (fun _ _ => by positivity)
  have key : A * ((7 / 8) * A * t ^ 2 + 2 * B * t * s + (7 / 8) * C * s ^ 2) =
      (7 / 8) * (A * t + 8 / 7 * B * s) ^ 2 + ((7 / 8) * A * C - 8 / 7 * B ^ 2) * s ^ 2 := by ring
  have hpos : 0 ≤ (7 / 8) * A * t ^ 2 + 2 * B * t * s + (7 / 8) * C * s ^ 2 := by
    rcases eq_or_lt_of_le hA0 with h0 | h0
    · have hB0 : B = 0 := by
        have : B ^ 2 * 4 ≤ 0 := by rw [← h0] at hB; simpa using hB
        nlinarith [sq_nonneg B]
      rw [← h0, hB0]; nlinarith [mul_nonneg hC0 (sq_nonneg s)]
    · have : 0 ≤ (7 / 8) * (A * t + 8 / 7 * B * s) ^ 2 + ((7 / 8) * A * C - 8 / 7 * B ^ 2) * s ^ 2 := by
        have : 0 ≤ (7 / 8) * A * C - 8 / 7 * B ^ 2 := by nlinarith
        positivity
      rw [← key] at this
      exact (mul_nonneg_iff_of_pos_left h0).mp this
  nlinarith

lemma sin_sq_ge_of_le {x : ℝ} (hx : |x| ≤ 2) : x ^ 2 / 8 ≤ Real.sin x ^ 2 := by
  have hsa : Real.sin x ^ 2 = Real.sin |x| ^ 2 := by
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]; rw [Real.sin_neg]; ring
  rw [hsa, ← sq_abs x]
  set y := |x|
  have hy0 : 0 ≤ y := abs_nonneg x
  -- sin y ≥ y/2 on [0, 2] (concavity on [0, π])
  have hpi := Real.pi_gt_three
  have key : (1 - 2 / π) * y ≤ Real.sin y := by
    have hpi4 : 2 / π ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have hpi5 : 1 - 2 / π ≤ 2 / π := by
      have : 4 / π ≥ 1 := by rw [ge_iff_le, le_div_iff₀ (by positivity)]; linarith [Real.pi_lt_four]
      have e : 4 / π = 2 * (2 / π) := by ring
      linarith
    rcases le_or_gt y (π / 2) with h | h
    · have := Real.mul_le_sin hy0 h
      nlinarith
    · have h2 : π - y ≤ π / 2 := by linarith
      have h3 : 0 ≤ π - y := by linarith
      have := Real.mul_le_sin h3 h2
      rw [Real.sin_pi_sub] at this
      have e : 2 / π * (π - y) = 2 - 2 / π * y := by field_simp
      nlinarith
  have hc : 1 / 8 ≤ (1 - 2 / π) ^ 2 := by
    have : 2 / π ≤ 0.64 := by rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_gt_d2]
    nlinarith
  have h0 : 0 ≤ (1 - 2 / π) * y := by
    apply mul_nonneg _ hy0
    have : 2 / π ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  nlinarith

/-- **Case B**: tiny steps; the first `m` terms stay inside `|θ| ≤ 2`. -/
lemma sum_sin_sq_caseB (n m : ℕ) (hm : m ≤ n) (s t : ℝ) (ht : |t| ≤ 8 / 5)
    (hsm : |s| * m ≤ 2 / 5) :
    ((m : ℝ) * t ^ 2 + (∑ w ∈ range m, (w : ℝ) ^ 2) * s ^ 2) / 64 ≤
      ∑ w ∈ range n, Real.sin (s * w + t) ^ 2 := by
  have h1 : ∀ w ∈ range m, (t + s * w) ^ 2 / 8 ≤ Real.sin (s * w + t) ^ 2 := by
    intro w hw
    rw [mem_range] at hw
    have hw' : (w : ℝ) ≤ m := by exact_mod_cast hw.le
    have hsw : |s * w| ≤ 2 / 5 := by
      rw [abs_mul, Nat.abs_cast]
      calc |s| * w ≤ |s| * m := mul_le_mul_of_nonneg_left hw' (abs_nonneg s)
        _ ≤ 2 / 5 := hsm
    have : |s * w + t| ≤ 2 := by
      calc |s * w + t| ≤ |s * w| + |t| := abs_add_le _ _
        _ ≤ 2 := by linarith
    have h := sin_sq_ge_of_le this
    calc (t + s * w) ^ 2 / 8 = (s * w + t) ^ 2 / 8 := by ring
      _ ≤ Real.sin (s * w + t) ^ 2 := h
  have h2 : ∑ w ∈ range m, (t + s * w) ^ 2 / 8 ≤ ∑ w ∈ range m, Real.sin (s * w + t) ^ 2 :=
    sum_le_sum h1
  have h3 : ∑ w ∈ range m, Real.sin (s * w + t) ^ 2 ≤ ∑ w ∈ range n, Real.sin (s * w + t) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (fun x hx => by rw [mem_range] at hx ⊢; omega) (fun _ _ _ => by positivity)
  have h4 := ap_quad_ge m s t
  rw [← sum_div] at h2
  linarith

end R522
end

end S_C6

-- ===== C7 =====
section S_C7

/-! Affine changes of variable for Fourier transforms, and the test functions (original). -/

open Finset Real MeasureTheory FourierTransform

noncomputable section

namespace R522

lemma integral_affine (F : ℝ → ℂ) {a : ℝ} (b : ℝ) (ha : a ≠ 0) :
    ∫ x, F (a * x + b) = ((|a|⁻¹ : ℝ) : ℂ) * ∫ y, F y := by
  have h1 : (fun x => F (a * x + b)) = fun x => (fun y => F (y + b)) (a * x) := rfl
  rw [h1, Measure.integral_comp_mul_left (fun y => F (y + b)) a, integral_add_right_eq_self F b]
  rw [abs_inv, Complex.real_smul]

lemma integral_affine_real (F : ℝ → ℝ) {a : ℝ} (b : ℝ) (ha : a ≠ 0) :
    ∫ x, F (a * x + b) = |a|⁻¹ * ∫ y, F y := by
  have h1 : (fun x => F (a * x + b)) = fun x => (fun y => F (y + b)) (a * x) := rfl
  rw [h1, Measure.integral_comp_mul_left (fun y => F (y + b)) a, integral_add_right_eq_self F b]
  rw [abs_inv, smul_eq_mul]

lemma norm_fourier_affine (f : ℝ → ℂ) {a : ℝ} (b : ℝ) (ha : a ≠ 0) (u : ℝ) :
    ‖𝓕 (fun x => f (a * x + b)) u‖ = |a|⁻¹ * ‖𝓕 f (u / a)‖ := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  set F : ℝ → ℂ := fun y => Complex.exp (↑(-2 * π * ((y - b) / a) * u) * Complex.I) • f y
  have hF : ∀ x, Complex.exp (↑(-2 * π * x * u) * Complex.I) • f (a * x + b) = F (a * x + b) := by
    intro x; simp only [F]; congr 4; field_simp; ring
  simp_rw [hF]
  rw [integral_affine F b ha]
  have hF' : ∀ y, F y = Complex.exp (↑(2 * π * b * u / a) * Complex.I) *
      (Complex.exp (↑(-2 * π * y * (u / a)) * Complex.I) • f y) := by
    intro y; simp only [F, smul_eq_mul]; rw [← mul_assoc, ← Complex.exp_add]; congr 2; push_cast
    field_simp; ring
  simp_rw [hF']
  rw [integral_const_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

lemma integral_norm_fourier_affine (f : ℝ → ℂ) {a : ℝ} (b : ℝ) (ha : a ≠ 0) :
    ∫ u, ‖𝓕 (fun x => f (a * x + b)) u‖ = ∫ v, ‖𝓕 f v‖ := by
  simp_rw [norm_fourier_affine f b ha, div_eq_inv_mul]
  rw [integral_const_mul]
  have := integral_affine_real (fun v => ‖𝓕 f v‖) (a := a⁻¹) 0 (inv_ne_zero ha)
  simp only [add_zero] at this
  rw [this, abs_inv, inv_inv, ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr ha), one_mul]

lemma integral_tail_fourier_affine (f : ℝ → ℂ) {a : ℝ} (b : ℝ) (ha : a ≠ 0) (U : ℝ) :
    ∫ u, Set.indicator {u : ℝ | U < |u|} (fun u => ‖𝓕 (fun x => f (a * x + b)) u‖) u
      = ∫ v, Set.indicator {v : ℝ | U / |a| < |v|} (fun v => ‖𝓕 f v‖) v := by
  have e : ∀ u, Set.indicator {u : ℝ | U < |u|} (fun u => ‖𝓕 (fun x => f (a * x + b)) u‖) u
      = |a|⁻¹ * (fun v => Set.indicator {v : ℝ | U / |a| < |v|} (fun v => ‖𝓕 f v‖) v) (a⁻¹ * u + 0) := by
    intro u
    simp only [add_zero, Set.indicator, Set.mem_setOf_eq]
    have hab : 0 < |a| := abs_pos.mpr ha
    have : (U < |u|) ↔ (U / |a| < |a⁻¹ * u|) := by
      rw [abs_mul, abs_inv, div_lt_iff₀ hab, inv_mul_eq_div, div_mul_cancel₀ _ hab.ne']
    by_cases h : U < |u|
    · rw [if_pos h, if_pos (this.mp h), norm_fourier_affine f b ha, div_eq_inv_mul]
    · rw [if_neg h, if_neg (fun h' => h (this.mpr h'))]; ring
  simp_rw [e]
  rw [integral_const_mul, integral_affine_real _ 0 (inv_ne_zero ha), abs_inv, inv_inv, ← mul_assoc,
    inv_mul_cancel₀ (abs_ne_zero.mpr ha), one_mul]

lemma norm_fourier_le (f : ℝ → ℂ) (u : ℝ) : ‖𝓕 f u‖ ≤ ∫ x, ‖f x‖ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; ext x
  rw [smul_eq_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

lemma tail_le_mom4 (ψ : SchwartzMap ℝ ℂ) {U : ℝ} (hU : 0 < U) : Tail ψ U ≤ Mom 4 ψ / U ^ 4 := by
  unfold Tail Mom
  rw [le_div_iff₀ (by positivity), ← integral_mul_const]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall (fun u =>
      mul_nonneg (Set.indicator_nonneg (fun _ _ => norm_nonneg _) u) (by positivity))
  · exact integrable_mom 4 ψ
  · refine Filter.Eventually.of_forall (fun u => ?_)
    simp only [Set.indicator, Set.mem_setOf_eq]
    split_ifs with h
    · have : U ^ 4 ≤ |u| ^ 4 := pow_le_pow_left₀ hU.le h.le 4
      have hn := norm_nonneg (𝓕 (ψ : ℝ → ℂ) u)
      show ‖𝓕 (ψ : ℝ → ℂ) u‖ * U ^ 4 ≤ |u| ^ 4 * ‖𝓕 (ψ : ℝ → ℂ) u‖
      nlinarith
    · show 0 * U ^ 4 ≤ |u| ^ 4 * ‖𝓕 (ψ : ℝ → ℂ) u‖
      rw [zero_mul]; positivity

/-! ### test functions -/

/-- the `X`-bump at scale `lam`: `1` on `[0, lam]`, supported in `(-lamδ, lam(1+δ))`. -/
def ψX (lam δ : ℝ) (hlam : 0 < lam) (hδ : 0 < δ) : SchwartzMap ℝ ℂ :=
  Sb 0 lam (lam * δ) hlam (mul_pos hlam hδ)

lemma bb_scale {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) (x : ℝ) :
    bb 0 lam (lam * δ) hlam (mul_pos hlam hδ) x = bb 0 1 δ one_pos hδ (lam⁻¹ * x + 0) := by
  simp only [bb, ContDiffBump.apply, add_zero]
  have hl : lam ≠ 0 := hlam.ne'
  congr 1
  · simp only [sub_zero]; field_simp
  · simp only [smul_eq_mul, sub_zero]; field_simp; ring

lemma ψX_apply {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) (x : ℝ) :
    ψX lam δ hlam hδ x = Sb 0 1 δ one_pos hδ (lam⁻¹ * x + 0) := by
  simp only [ψX, Sb_apply, bb_scale hlam hδ]

lemma ψX_coe {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) :
    (ψX lam δ hlam hδ : ℝ → ℂ) = fun x => (Sb 0 1 δ one_pos hδ : ℝ → ℂ) (lam⁻¹ * x + 0) := by
  funext x; exact ψX_apply hlam hδ x

lemma mom0_ψX {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) : Mom 0 (ψX lam δ hlam hδ) = Mom 0 (Sb 0 1 δ one_pos hδ) := by
  simp only [Mom, pow_zero, one_mul]
  rw [ψX_coe, integral_norm_fourier_affine _ 0 (inv_ne_zero hlam.ne')]

lemma tail_ψX {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) (U : ℝ) :
    Tail (ψX lam δ hlam hδ) U = Tail (Sb 0 1 δ one_pos hδ) (lam * U) := by
  unfold Tail
  rw [ψX_coe, integral_tail_fourier_affine _ 0 (inv_ne_zero hlam.ne'), abs_inv, abs_of_pos hlam,
    div_inv_eq_mul, mul_comm]

lemma sup_ψX {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) (u : ℝ) :
    ‖𝓕 (ψX lam δ hlam hδ : ℝ → ℂ) u‖ ≤ lam * (1 + 2 * δ) := by
  refine (norm_fourier_le _ u).trans ?_
  -- the bump is in [0,1] and vanishes outside an interval of length lam(1+2δ)
  have hle : ∀ x, ‖(ψX lam δ hlam hδ : ℝ → ℂ) x‖ ≤
      Set.indicator (Set.Icc (-(lam * δ)) (lam + lam * δ)) (fun _ => (1 : ℝ)) x := by
    intro x
    simp only [ψX, Sb_apply, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (bb_nonneg _ _ _ _ _ x)]
    by_cases hx : x ∈ Set.Icc (-(lam * δ)) (lam + lam * δ)
    · rw [Set.indicator_of_mem hx]; exact bb_le_one _ _ _ _ _ x
    · rw [Set.indicator_of_notMem hx, bb_zero]
      intro h; apply hx
      simp only [Set.mem_Ioo, zero_sub] at h
      exact ⟨h.1.le, h.2.le⟩
  calc ∫ x, ‖(ψX lam δ hlam hδ : ℝ → ℂ) x‖
      ≤ ∫ x, Set.indicator (Set.Icc (-(lam * δ)) (lam + lam * δ)) (fun _ => (1 : ℝ)) x := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => norm_nonneg _))
        · exact (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
        · exact Filter.Eventually.of_forall hle
    _ = lam * (1 + 2 * δ) := by
        rw [integral_indicator measurableSet_Icc, setIntegral_const]
        simp only [Measure.real, Real.volume_Icc, smul_eq_mul, mul_one]
        rw [ENNReal.toReal_ofReal (by nlinarith)]; ring

/-- the base of the partition of unity: `st z - st (z - 1)`, supported in `[0, 2]`. -/
def χ0 (z : ℝ) : ℝ := Real.smoothTransition z - Real.smoothTransition (z - 1)

lemma χ0_nonneg (z : ℝ) : 0 ≤ χ0 z := by
  unfold χ0; have := Real.smoothTransition.monotone (show z - 1 ≤ z by linarith); linarith

lemma χ0_le_one (z : ℝ) : χ0 z ≤ 1 := by
  unfold χ0
  have := Real.smoothTransition.le_one z
  have := Real.smoothTransition.nonneg (z - 1)
  linarith

lemma χ0_zero_of {z : ℝ} (hz : z ≤ 0 ∨ 2 ≤ z) : χ0 z = 0 := by
  unfold χ0
  rcases hz with h | h
  · rw [Real.smoothTransition.zero_of_nonpos h, Real.smoothTransition.zero_of_nonpos (by linarith)]
    ring
  · rw [Real.smoothTransition.one_of_one_le (by linarith), Real.smoothTransition.one_of_one_le (by linarith)]
    ring

lemma χ0_contDiff : ContDiff ℝ (⊤ : ℕ∞) χ0 := by
  unfold χ0
  exact Real.smoothTransition.contDiff.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

lemma χ0_hasCompactSupport : HasCompactSupport χ0 := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 2))
  intro z hz
  simp only [Set.mem_Icc, not_and_or, not_le] at hz
  exact χ0_zero_of (hz.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le))

/-- the `Y`-weight of shell `j`: `χ0 (-y/h - j + 1)`. -/
def χY (h : ℝ) (j : ℕ) (y : ℝ) : ℝ := χ0 ((-h⁻¹) * y + (1 - j))

lemma χY_contDiff (h : ℝ) (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (χY h j) := by
  unfold χY; exact χ0_contDiff.comp ((contDiff_const.mul contDiff_id).add contDiff_const)

lemma χY_hasCompactSupport {h : ℝ} (hh : 0 < h) (j : ℕ) : HasCompactSupport (χY h j) := by
  unfold χY
  have : (fun y => χ0 ((-h⁻¹) * y + (1 - j))) = χ0 ∘ (fun y => (-h⁻¹) * y + (1 - j)) := rfl
  rw [this]
  exact χ0_hasCompactSupport.comp_homeomorph
    ((Homeomorph.mulLeft₀ (-h⁻¹) (by simp [hh.ne'])).trans (Homeomorph.addRight _))

def ψY (h : ℝ) (hh : 0 < h) (j : ℕ) : SchwartzMap ℝ ℂ :=
  ((χY_hasCompactSupport hh j).comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (χY_contDiff h j))

lemma ψY_apply {h : ℝ} (hh : 0 < h) (j : ℕ) (y : ℝ) : ψY h hh j y = ((χY h j y : ℝ) : ℂ) := rfl

lemma ψY_coe {h : ℝ} (hh : 0 < h) (j : ℕ) :
    (ψY h hh j : ℝ → ℂ) = fun y => (fun z => ((χ0 z : ℝ) : ℂ)) ((-h⁻¹) * y + (1 - j)) := by
  funext y; rfl

/-- `χ0` as a Schwartz function. -/
def ψ0 : SchwartzMap ℝ ℂ :=
  (χ0_hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp χ0_contDiff)

lemma ψ0_coe : (ψ0 : ℝ → ℂ) = fun z => ((χ0 z : ℝ) : ℂ) := rfl

lemma mom0_ψY {h : ℝ} (hh : 0 < h) (j : ℕ) : Mom 0 (ψY h hh j) = Mom 0 ψ0 := by
  simp only [Mom, pow_zero, one_mul]
  rw [ψY_coe, ψ0_coe]
  exact integral_norm_fourier_affine (fun z => ((χ0 z : ℝ) : ℂ)) (a := -h⁻¹) (1 - j) (by simp [hh.ne'])

lemma tail_ψY {h : ℝ} (hh : 0 < h) (j : ℕ) (V : ℝ) : Tail (ψY h hh j) V = Tail ψ0 (h * V) := by
  unfold Tail
  rw [ψY_coe, ψ0_coe]
  have := integral_tail_fourier_affine (fun z => ((χ0 z : ℝ) : ℂ)) (a := -h⁻¹) (1 - j)
    (by simp [hh.ne']) V
  rw [abs_neg, abs_inv, abs_of_pos hh, div_inv_eq_mul, mul_comm] at this
  exact this

lemma sup_ψY {h : ℝ} (hh : 0 < h) (j : ℕ) (v : ℝ) : ‖𝓕 (ψY h hh j : ℝ → ℂ) v‖ ≤ 2 * h := by
  rw [ψY_coe]
  have e := norm_fourier_affine (fun z => ((χ0 z : ℝ) : ℂ)) (a := -h⁻¹) (1 - j) (by simp [hh.ne']) v
  rw [show (fun y => (fun z => ((χ0 z : ℝ) : ℂ)) ((-h⁻¹) * y + (1 - j))) =
    (fun x => (fun z => ((χ0 z : ℝ) : ℂ)) ((-h⁻¹) * x + (1 - j))) from rfl, e]
  rw [abs_neg, abs_inv, abs_of_pos hh]
  have : ‖𝓕 (fun z => ((χ0 z : ℝ) : ℂ)) (v / -h⁻¹)‖ ≤ 2 := by
    refine (norm_fourier_le _ _).trans ?_
    have hle : ∀ z, ‖((χ0 z : ℝ) : ℂ)‖ ≤ Set.indicator (Set.Icc (0 : ℝ) 2) (fun _ => (1 : ℝ)) z := by
      intro z
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (χ0_nonneg z)]
      by_cases hz : z ∈ Set.Icc (0 : ℝ) 2
      · rw [Set.indicator_of_mem hz]; exact χ0_le_one z
      · rw [Set.indicator_of_notMem hz, χ0_zero_of]
        simp only [Set.mem_Icc, not_and_or, not_le] at hz
        exact hz.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le)
    calc ∫ z, ‖((χ0 z : ℝ) : ℂ)‖ ≤ ∫ z, Set.indicator (Set.Icc (0 : ℝ) 2) (fun _ => (1 : ℝ)) z := by
          apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => norm_nonneg _))
          · exact (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
          · exact Filter.Eventually.of_forall hle
      _ = 2 := by
          rw [integral_indicator measurableSet_Icc, setIntegral_const]
          simp only [Measure.real, Real.volume_Icc, smul_eq_mul, mul_one]
          norm_num
  have h0 : (0 : ℝ) < h⁻¹⁻¹ := by positivity
  rw [inv_inv] at h0 ⊢
  nlinarith [norm_nonneg (𝓕 (fun z => ((χ0 z : ℝ) : ℂ)) (v / -h⁻¹))]

end R522
end

end S_C7

-- ===== C8 =====
section S_C8

/-! The sign-change model `(c_k, S_{k+1})` and the decay of its characteristic function (original).
Coordinates `j : Fin n` (`n = k + 2`), weights `w j = n - 1 - j` for `c` and `1` for `S`. -/

open Finset Real

noncomputable section

namespace R522

/-- `c`-weights. -/
def wt (n : ℕ) (j : Fin n) : ℝ := (n : ℝ) - 1 - j

def σa (n : ℕ) : ℝ := √(∑ j : Fin n, wt n j ^ 2)

def aw (n : ℕ) (j : Fin n) : ℝ := wt n j / σa n
def bw (n : ℕ) (_j : Fin n) : ℝ := 1 / √(n : ℝ)
def ρw (n : ℕ) : ℝ := ∑ j : Fin n, aw n j * bw n j

lemma sum_wt_sq (n : ℕ) : ∑ j : Fin n, wt n j ^ 2 = ∑ w ∈ range n, (w : ℝ) ^ 2 := by
  simp only [wt]
  rw [Fin.sum_univ_eq_sum_range (fun j => ((n : ℝ) - 1 - j) ^ 2) n]
  rw [← sum_range_reflect]
  apply sum_congr rfl; intro w hw; rw [mem_range] at hw
  congr 1; rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring

lemma sum_wt (n : ℕ) : ∑ j : Fin n, wt n j = ∑ w ∈ range n, (w : ℝ) := by
  simp only [wt]
  rw [Fin.sum_univ_eq_sum_range (fun j => ((n : ℝ) - 1 - j)) n]
  rw [← sum_range_reflect]
  apply sum_congr rfl; intro w hw; rw [mem_range] at hw
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring

lemma sum_wt_four (n : ℕ) : ∑ j : Fin n, wt n j ^ 4 = ∑ w ∈ range n, (w : ℝ) ^ 4 := by
  simp only [wt]
  rw [Fin.sum_univ_eq_sum_range (fun j => ((n : ℝ) - 1 - j) ^ 4) n]
  rw [← sum_range_reflect]
  apply sum_congr rfl; intro w hw; rw [mem_range] at hw
  congr 1; rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring

lemma sq6 (n : ℕ) : (∑ w ∈ range n, (w : ℝ) ^ 2) * 6 = (n : ℝ) * (n - 1) * (2 * n - 1) :=
  sum_sq_range_mul_six n

lemma sum_range_cast (n : ℕ) : (∑ w ∈ range n, (w : ℝ)) * 2 = (n : ℝ) * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, add_mul, ih]; push_cast; ring

lemma sum_four_le (n : ℕ) : ∑ w ∈ range n, (w : ℝ) ^ 4 ≤ (n : ℝ) ^ 5 := by
  calc ∑ w ∈ range n, (w : ℝ) ^ 4 ≤ ∑ _w ∈ range n, (n : ℝ) ^ 4 := by
        apply sum_le_sum; intro w hw; rw [mem_range] at hw
        exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hw.le) 4
    _ = (n : ℝ) ^ 5 := by simp; ring

lemma σa_sq (n : ℕ) : σa n ^ 2 = ∑ w ∈ range n, (w : ℝ) ^ 2 := by
  rw [σa, Real.sq_sqrt (sum_nonneg (fun _ _ => by positivity)), sum_wt_sq]

lemma σa_sq_eq (n : ℕ) : σa n ^ 2 * 6 = (n : ℝ) * (n - 1) * (2 * n - 1) := by
  rw [σa_sq, sq6]

lemma σa_pos {n : ℕ} (hn : 2 ≤ n) : 0 < σa n := by
  apply Real.sqrt_pos.mpr
  rw [sum_wt_sq]
  apply sum_pos' (fun _ _ => by positivity) ⟨1, by rw [mem_range]; omega, by norm_num⟩

lemma aw_sq {n : ℕ} (hn : 2 ≤ n) : ∑ j, aw n j ^ 2 = 1 := by
  have h : ∑ j, aw n j ^ 2 = (∑ j, wt n j ^ 2) / σa n ^ 2 := by simp only [aw, div_pow, sum_div]
  rw [h, show (∑ j, wt n j ^ 2) = σa n ^ 2 by rw [σa_sq, sum_wt_sq]]
  exact div_self (by have := σa_pos hn; positivity)

lemma bw_sq {n : ℕ} (hn : 2 ≤ n) : ∑ j, bw n j ^ 2 = 1 := by
  simp only [bw, div_pow, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Real.sq_sqrt (by positivity)]
  field_simp

/-- the cosine kernel along an arithmetic progression. -/
lemma Kc_eq (n : ℕ) (u v : ℝ) :
    Kc (aw n) (bw n) u v = ∏ w ∈ range n,
      Real.cos (2 * π * u / σa n * w + 2 * π * v / √(n : ℝ)) := by
  unfold Kc
  simp only [aw, bw, wt]
  rw [Fin.prod_univ_eq_prod_range (fun j => Real.cos (2 * π * (u * (((n : ℝ) - 1 - j) / σa n) +
    v * (1 / √(n : ℝ))))) n]
  · rw [← prod_range_reflect]
    apply prod_congr rfl; intro w hw; rw [mem_range] at hw
    congr 1; rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring

lemma pi_div_two_le_two : π / 2 ≤ 2 := by linarith [Real.pi_lt_four]

/-- numeric core of case B -/
lemma caseB_num (n m : ℕ) (σ2 u v s t C : ℝ) (hn0 : (0 : ℝ) < n) (hm1 : (n : ℝ) / 40 ≤ m)
    (hσp : 0 < σ2) (hσ2 : σ2 ≤ (n : ℝ) ^ 3 / 3) (hCm : (m : ℝ) ^ 3 / 12 ≤ C)
    (hss : s ^ 2 = 4 * π ^ 2 * u ^ 2 / σ2) (htt : t ^ 2 = 4 * π ^ 2 * v ^ 2 / n) :
    π ^ 2 * (u ^ 2 + v ^ 2) / 4096000 ≤ ((m : ℝ) * t ^ 2 + C * s ^ 2) / 64 := by
  have hpi : 0 ≤ π ^ 2 := by positivity
  have hv2 : 0 ≤ 4 * π ^ 2 * v ^ 2 := by positivity
  have hu2 : 0 ≤ 4 * π ^ 2 * u ^ 2 := by positivity
  have hmn : (1 : ℝ) / 40 ≤ m / n := by rw [le_div_iff₀ hn0]; linarith
  have hT1 : π ^ 2 * v ^ 2 / 10 ≤ (m : ℝ) * t ^ 2 := by
    rw [htt, show (m : ℝ) * (4 * π ^ 2 * v ^ 2 / n) = 4 * π ^ 2 * v ^ 2 * (m / n) by ring]
    have := mul_le_mul_of_nonneg_left hmn hv2
    linarith
  have hm0 : (0 : ℝ) ≤ m := le_trans (by positivity) hm1
  have h1 : 4 * π ^ 2 * u ^ 2 / ((n : ℝ) ^ 3 / 3) ≤ s ^ 2 := by
    rw [hss]; exact div_le_div_of_nonneg_left hu2 hσp hσ2
  have h2 : (n : ℝ) ^ 3 / 64000 ≤ (m : ℝ) ^ 3 := by
    have := pow_le_pow_left₀ (by positivity) hm1 3
    rw [div_pow] at this
    linarith
  have h3 : π ^ 2 * u ^ 2 / 64000 = ((n : ℝ) ^ 3 / 64000) * (4 * π ^ 2 * u ^ 2 / ((n : ℝ) ^ 3 / 3)) / 12 := by
    field_simp; ring
  have hT2 : π ^ 2 * u ^ 2 / 64000 ≤ C * s ^ 2 := by
    rw [h3]
    have hs0 : 0 ≤ 4 * π ^ 2 * u ^ 2 / ((n : ℝ) ^ 3 / 3) := by positivity
    calc ((n : ℝ) ^ 3 / 64000) * (4 * π ^ 2 * u ^ 2 / ((n : ℝ) ^ 3 / 3)) / 12
        ≤ ((m : ℝ) ^ 3) * (4 * π ^ 2 * u ^ 2 / ((n : ℝ) ^ 3 / 3)) / 12 := by gcongr
      _ = ((m : ℝ) ^ 3 / 12) * (4 * π ^ 2 * u ^ 2 / ((n : ℝ) ^ 3 / 3)) := by ring
      _ ≤ C * s ^ 2 := by
          apply mul_le_mul hCm h1 hs0 (le_trans (by positivity) hCm)
  have : π ^ 2 * (u ^ 2 + v ^ 2) / 4096000 ≤ (π ^ 2 * v ^ 2 / 10 + π ^ 2 * u ^ 2 / 64000) / 64 := by
    have : 0 ≤ π ^ 2 * v ^ 2 := by positivity
    have : 0 ≤ π ^ 2 * u ^ 2 := by positivity
    linarith
  linarith

/-- **Decay on the cell outside the box.** -/
theorem Kc_decay {n : ℕ} (hn : 40 ≤ n) {u v R : ℝ}
    (hu : |u| ≤ σa n / 4) (hv : |v| ≤ √(n : ℝ) / 4) (hout : R ^ 2 ≤ u ^ 2 + v ^ 2) :
    |Kc (aw n) (bw n) u v| ≤
      Real.exp (-((n : ℝ) * Real.sin (1 / 2) ^ 2 / 16)) + Real.exp (-(R ^ 2 * (π ^ 2 / 8192000))) := by
  rw [Kc_eq]
  have hσ := σa_pos (show 2 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by positivity
  set s := 2 * π * u / σa n with hs
  set t := 2 * π * v / √(n : ℝ) with ht
  have hsn : |s| ≤ π / 2 := by
    rw [hs, abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π), abs_of_pos hσ,
      div_le_iff₀ hσ]
    nlinarith [Real.pi_pos]
  have htn : |t| ≤ π / 2 := by
    have hsq : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr hn0
    rw [ht, abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π), abs_of_pos hsq,
      div_le_iff₀ hsq]
    nlinarith [Real.pi_pos]
  have hprod := abs_prod_cos_le (n := n) (fun w => s * w + t)
  refine hprod.trans ?_
  have e1 := Real.exp_pos (-((n : ℝ) * Real.sin (1 / 2) ^ 2 / 16))
  have e2 := Real.exp_pos (-(R ^ 2 * (π ^ 2 / 8192000)))
  by_cases hA : 8 / (n : ℝ) ≤ |s|
  · have := sum_sin_sq_caseA n s t hA (hsn.trans pi_div_two_le_two) (by omega)
    have : Real.exp (-((∑ w ∈ range n, Real.sin (s * w + t) ^ 2) / 2)) ≤
        Real.exp (-((n : ℝ) * Real.sin (1 / 2) ^ 2 / 16)) := by
      apply Real.exp_le_exp.mpr; linarith
    linarith
  · push Not at hA
    set m := n / 20 with hm
    have hm1 : (n : ℝ) / 40 ≤ m := by
      have : 20 * m + 20 ≥ n + 1 := by omega
      have : (20 : ℝ) * m + 20 ≥ n + 1 := by exact_mod_cast this
      have : (40 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hm2 : (m : ℝ) ≤ n / 20 := by
      have : 20 * m ≤ n := by omega
      have : (20 : ℝ) * m ≤ n := by exact_mod_cast this
      linarith
    have hmn : m ≤ n := by omega
    have hsm : |s| * m ≤ 2 / 5 := by
      calc |s| * m ≤ (8 / n) * (n / 20) := by
            apply mul_le_mul hA.le hm2 (by positivity) (by positivity)
        _ = 2 / 5 := by field_simp; ring
    have hB := sum_sin_sq_caseB n m hmn s t (htn.trans (by linarith [Real.pi_lt_d2])) hsm
    -- lower bounds for the two diagonal terms
    have hm2' : 2 ≤ m := by omega
    have hCm : (m : ℝ) ^ 3 / 12 ≤ ∑ w ∈ range m, (w : ℝ) ^ 2 := by
      have := sq6 m
      have hm2r : (2 : ℝ) ≤ m := by exact_mod_cast hm2'
      have hm0 : (0 : ℝ) ≤ m := by positivity
      have key : (m : ℝ) ^ 3 / 12 * 6 ≤ (m : ℝ) * (m - 1) * (2 * m - 1) := by
        nlinarith [mul_nonneg (mul_nonneg hm0 hm0) (sub_nonneg.mpr hm2r)]
      linarith
    have hσ2 : σa n ^ 2 ≤ (n : ℝ) ^ 3 / 3 := by
      have := σa_sq_eq n
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sub_nonneg.mpr hn1)]
    have hss : s ^ 2 = 4 * π ^ 2 * u ^ 2 / σa n ^ 2 := by rw [hs]; field_simp; ring
    have htt : t ^ 2 = 4 * π ^ 2 * v ^ 2 / n := by
      rw [ht, div_pow, Real.sq_sqrt hn0.le]; ring
    have hcb := caseB_num n m (σa n ^ 2) u v s t (∑ w ∈ range m, (w : ℝ) ^ 2) hn0 hm1
      (by positivity) hσ2 hCm hss htt
    have hsum : R ^ 2 * (π ^ 2 / 4096000) ≤ ∑ w ∈ range n, Real.sin (s * w + t) ^ 2 := by
      have hR : R ^ 2 * (π ^ 2 / 4096000) ≤ π ^ 2 * (u ^ 2 + v ^ 2) / 4096000 := by
        have := mul_le_mul_of_nonneg_right hout (by positivity : (0:ℝ) ≤ π ^ 2 / 4096000)
        linarith
      linarith
    have : Real.exp (-((∑ w ∈ range n, Real.sin (s * w + t) ^ 2) / 2)) ≤
        Real.exp (-(R ^ 2 * (π ^ 2 / 8192000))) := by
      apply Real.exp_le_exp.mpr; linarith
    linarith

/-- the Gaussian kernel outside the box. -/
lemma gk_decay {ρ R u v : ℝ} (hρ : |ρ| ≤ 1) (hout : R ^ 2 ≤ u ^ 2 + v ^ 2) :
    gk ρ u v ≤ Real.exp (-(2 * π ^ 2 * (1 - |ρ|) * R ^ 2)) := by
  unfold gk
  apply Real.exp_le_exp.mpr
  have h1 : (1 - |ρ|) * (u ^ 2 + v ^ 2) ≤ u ^ 2 + 2 * ρ * u * v + v ^ 2 := by
    have : |2 * ρ * u * v| ≤ |ρ| * (u ^ 2 + v ^ 2) := by
      rw [show 2 * ρ * u * v = ρ * (2 * u * v) by ring, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (u + v), sq_nonneg (u - v)]
    have := neg_abs_le (2 * ρ * u * v)
    nlinarith
  have h2 : (1 - |ρ|) * R ^ 2 ≤ (1 - |ρ|) * (u ^ 2 + v ^ 2) :=
    mul_le_mul_of_nonneg_left hout (by linarith)
  nlinarith [Real.pi_pos, sq_nonneg π]

end R522
end

end S_C8

-- ===== C9 =====
section S_C9

/-! Hoeffding for sign sums, the partition of unity, and the pointwise wedge majorant (original). -/

open Finset Real MeasureTheory

noncomputable section

namespace R522

section hoeff
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sum_signs_rexp (c : ι → ℝ) :
    ∑ ε : ι → ℤˣ, Real.exp (ssum ε c) = ∏ i, (Real.exp (c i) + Real.exp (-c i)) := by
  have : ∀ ε : ι → ℤˣ, Real.exp (ssum ε c) = ∏ i, Real.exp (((ε i : ℤ) : ℝ) * c i) := by
    intro ε; unfold ssum; rw [Real.exp_sum]
  simp_rw [this]
  rw [← Fintype.prod_sum (fun i (u : ℤˣ) => Real.exp (((u : ℤ) : ℝ) * c i))]
  apply prod_congr rfl; intro i _
  rw [show (Finset.univ : Finset ℤˣ) = {1, -1} from by decide, Finset.sum_pair (by decide)]
  simp

lemma EE_exp_ssum_le (c : ι → ℝ) :
    EE (fun ε => Real.exp (ssum ε c)) ≤ Real.exp ((∑ i, c i ^ 2) / 2) := by
  unfold EE
  rw [sum_signs_rexp, div_le_iff₀ (by positivity)]
  have h2 : (2 : ℝ) ^ Fintype.card ι = ∏ _i : ι, (2 : ℝ) := by simp
  rw [h2]
  rw [show Real.exp ((∑ i, c i ^ 2) / 2) * ∏ _i : ι, (2 : ℝ) = ∏ i, (2 * Real.exp (c i ^ 2 / 2)) by
    rw [sum_div, Real.exp_sum, ← prod_mul_distrib]; apply prod_congr rfl; intro i _; ring]
  apply prod_le_prod (fun i _ => by positivity)
  intro i _
  have := Real.cosh_le_exp_half_sq (c i)
  rw [Real.cosh_eq] at this
  linarith

/-- **Hoeffding.** -/
lemma hoeffding (c : ι → ℝ) {T : ℝ} (hT : 0 < T) :
    PP (fun ε => T ≤ |ssum ε c|) ≤ 2 * Real.exp (-(T ^ 2 / (2 * ∑ i, c i ^ 2))) := by
  classical
  set V := ∑ i, c i ^ 2 with hV
  by_cases hV0 : V = 0
  · -- all weights vanish
    have hc : ∀ i, c i = 0 := by
      intro i
      have : c i ^ 2 = 0 := by
        have := Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (c j)) |>.mp hV0.symm.symm
        exact this i (mem_univ _)
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this
    have : ∀ ε : ι → ℤˣ, ssum ε c = 0 := by intro ε; simp [ssum, hc]
    have : PP (fun ε => T ≤ |ssum ε c|) = 0 := by
      rw [PP_eq]; unfold EE; simp only [this, abs_zero]
      rw [show (fun _ : ι → ℤˣ => if T ≤ (0:ℝ) then (1:ℝ) else 0) = fun _ => 0 by
        funext _; rw [if_neg (by linarith)]]
      simp
    rw [this]; positivity
  have hVp : 0 < V := lt_of_le_of_ne (sum_nonneg (fun _ _ => sq_nonneg _)) (Ne.symm hV0)
  set lam := T / V
  have one_side : ∀ d : ι → ℝ, ∑ i, d i ^ 2 = V →
      PP (fun ε => T ≤ ssum ε d) ≤ Real.exp (-(T ^ 2 / (2 * V))) := by
    intro d hd
    have hm := markov (f := fun ε => Real.exp (lam * ssum ε d)) (fun ε => (Real.exp_pos _).le)
      (Real.exp_pos (lam * T))
    have hmono : PP (fun ε => T ≤ ssum ε d) ≤
        PP (fun ε => Real.exp (lam * T) ≤ Real.exp (lam * ssum ε d)) := by
      apply PP_mono; intro ε h
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left h (by positivity)
    have hE : EE (fun ε => Real.exp (lam * ssum ε d)) ≤ Real.exp (lam ^ 2 * V / 2) := by
      have : ∀ ε : ι → ℤˣ, lam * ssum ε d = ssum ε (fun i => lam * d i) := by
        intro ε; unfold ssum; rw [mul_sum]; apply sum_congr rfl; intro i _; ring
      simp_rw [this]
      refine (EE_exp_ssum_le _).trans (le_of_eq ?_)
      congr 1; rw [← hd]; simp only [mul_pow]; rw [← mul_sum]
    calc PP (fun ε => T ≤ ssum ε d) ≤ _ := hmono
      _ ≤ EE (fun ε => Real.exp (lam * ssum ε d)) / Real.exp (lam * T) := hm
      _ ≤ Real.exp (lam ^ 2 * V / 2) / Real.exp (lam * T) := by gcongr
      _ = Real.exp (-(T ^ 2 / (2 * V))) := by
          rw [← Real.exp_sub]; congr 1; simp only [lam]; field_simp; ring
  have h1 := one_side c rfl
  have h2 := one_side (fun i => -c i) (by simp [hV])
  have hsplit : PP (fun ε => T ≤ |ssum ε c|) ≤
      PP (fun ε => T ≤ ssum ε c) + PP (fun ε => T ≤ ssum ε (fun i => -c i)) := by
    refine le_trans (PP_mono (T := fun ε => T ≤ ssum ε c ∨ T ≤ ssum ε (fun i => -c i))
      (fun ε h => ?_)) (PP_or_le _ _)
    have e : ssum ε (fun i => -c i) = -ssum ε c := by unfold ssum; rw [← sum_neg_distrib]; simp
    rw [e]
    rcases le_abs'.mp h with h' | h'
    · right; linarith
    · left; exact h'
  linarith

end hoeff

/-! ### partition of unity -/

lemma sum_χ0 (x : ℝ) (N : ℕ) :
    ∑ j ∈ range N, χ0 (x - j) = Real.smoothTransition x - Real.smoothTransition (x - N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]; unfold χ0; push_cast; ring_nf

lemma sum_χY_le_one (h y : ℝ) (N : ℕ) : ∑ j ∈ range N, χY h j y ≤ 1 := by
  have := sum_χ0 ((-h⁻¹) * y + 1) N
  unfold χY
  have e : ∀ j ∈ range N, χ0 ((-h⁻¹) * y + (1 - j)) = χ0 ((-h⁻¹) * y + 1 - j) := by
    intro j _; ring_nf
  rw [sum_congr rfl e, this]
  have := Real.smoothTransition.le_one ((-h⁻¹) * y + 1)
  have := Real.smoothTransition.nonneg ((-h⁻¹) * y + 1 - N)
  linarith

lemma sum_χY_eq_one {h y : ℝ} (hh : 0 < h) (N : ℕ) (hy0 : y ≤ 0) (hy1 : -((N - 1 : ℝ) * h) ≤ y) :
    ∑ j ∈ range N, χY h j y = 1 := by
  have := sum_χ0 ((-h⁻¹) * y + 1) N
  unfold χY
  have e : ∀ j ∈ range N, χ0 ((-h⁻¹) * y + (1 - j)) = χ0 ((-h⁻¹) * y + 1 - j) := by
    intro j _; ring_nf
  rw [sum_congr rfl e, this]
  have hz0 : 0 ≤ (-h⁻¹) * y := by
    have : 0 ≤ h⁻¹ := by positivity
    nlinarith
  have hz1 : (-h⁻¹) * y ≤ N - 1 := by
    have e : (-h⁻¹) * y = (-y) / h := by field_simp
    rw [e, div_le_iff₀ hh]; linarith
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring

lemma χY_nonneg (h : ℝ) (j : ℕ) (y : ℝ) : 0 ≤ χY h j y := χ0_nonneg _

lemma χY_supp {h y : ℝ} (hh : 0 < h) (j : ℕ) (hpos : 0 < χY h j y) :
    ((j : ℝ) - 1) * h < -y ∧ -y < ((j : ℝ) + 1) * h := by
  unfold χY at hpos
  have h1 : 0 < (-h⁻¹) * y + (1 - j) ∧ (-h⁻¹) * y + (1 - j) < 2 := by
    by_contra hc
    rw [not_and_or, not_lt, not_lt] at hc
    rw [χ0_zero_of hc] at hpos
    exact lt_irrefl _ hpos
  have e : (-h⁻¹) * y = (-y) / h := by field_simp
  rw [e] at h1
  constructor
  · have := h1.1
    have : ((j : ℝ) - 1) < (-y) / h := by linarith
    rwa [lt_div_iff₀ hh] at this
  · have : (-y) / h < (j : ℝ) + 1 := by linarith [h1.2]
    rwa [div_lt_iff₀ hh] at this

end R522
end

end S_C9

-- ===== C10 =====
section S_C10

/-! The Gaussian side of the thin-wedge bound (original). -/

open Finset Real MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace R522

lemma integral_Ioi_mul_exp : ∫ x in Ioi (0 : ℝ), x * Real.exp (-(x ^ 2 / 2)) = 1 := by
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun x => -Real.exp (-(x ^ 2 / 2)))
      (x * Real.exp (-(x ^ 2 / 2))) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => -(x ^ 2 / 2)) (-x) x := by
      have := ((hasDerivAt_pow 2 x).div_const 2).neg
      exact this.congr_deriv (by norm_num)
    have h2 := h1.exp.neg
    exact h2.congr_deriv (by ring)
  have hint : IntegrableOn (fun x : ℝ => x * Real.exp (-(x ^ 2 / 2))) (Ioi 0) := by
    have := integrable_mul_exp_neg_mul_sq (show (0:ℝ) < 1 / 2 by norm_num)
    refine (this.congr (Filter.Eventually.of_forall (fun x => ?_))).integrableOn
    simp only; congr 2; ring
  have htend : Filter.Tendsto (fun x : ℝ => -Real.exp (-(x ^ 2 / 2))) Filter.atTop (nhds 0) := by
    have : Filter.Tendsto (fun x : ℝ => -(x ^ 2 / 2)) Filter.atTop Filter.atBot := by
      apply Filter.tendsto_neg_atTop_atBot.comp
      exact (Filter.tendsto_pow_atTop two_ne_zero).atTop_div_const (by norm_num)
    have := (Real.tendsto_exp_atBot.comp this).neg
    rw [neg_zero] at this
    exact this
  have hcont : ContinuousWithinAt (fun x : ℝ => -Real.exp (-(x ^ 2 / 2))) (Ici 0) 0 :=
    (by fun_prop : Continuous (fun x : ℝ => -Real.exp (-(x ^ 2 / 2)))).continuousWithinAt
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont (fun x hx => hderiv x (mem_Ici.mpr (le_of_lt hx))) hint htend]
  simp

lemma gaussPDF_eq (x : ℝ) : gaussianPDFReal 0 1 x = (√(2 * π))⁻¹ * Real.exp (-(x ^ 2 / 2)) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  congr 2; ring

lemma integral_γ_pos_part : ∫ z, max z 0 ∂γ = 1 / √(2 * π) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  have e : ∀ z : ℝ, gaussianPDFReal 0 1 z * max z 0 =
      Set.indicator (Ioi 0) (fun z => (√(2 * π))⁻¹ * (z * Real.exp (-(z ^ 2 / 2)))) z := by
    intro z
    by_cases hz : 0 < z
    · rw [indicator_of_mem (show z ∈ Ioi (0:ℝ) from hz), max_eq_left hz.le, gaussPDF_eq]; ring
    · rw [indicator_of_notMem (show z ∉ Ioi (0:ℝ) from hz), max_eq_right (not_lt.mp hz)]; ring
  simp_rw [e]
  rw [integral_indicator measurableSet_Ioi, integral_const_mul, integral_Ioi_mul_exp]
  ring

lemma integral_γ_neg_part : ∫ z, max (-z) 0 ∂γ = 1 / √(2 * π) := by
  have := integral_map (μ := γ) (f := fun z : ℝ => max z 0) (φ := fun z => -z)
    (by fun_prop) (by fun_prop)
  rw [map_neg_γ, integral_γ_pos_part] at this
  rw [this]

lemma γ_real_Icc_le (a b : ℝ) : γ.real (Icc a b) ≤ max (b - a) 0 / √(2 * π) := by
  by_cases hab : a ≤ b
  · rw [max_eq_left (by linarith)]; exact gauss_strip a b hab
  · rw [Icc_eq_empty hab]; simp only [measureReal_empty]
    exact div_nonneg (le_max_right _ _) (by positivity)

/-- `E[|Z|; Z ≤ z₀] ≤ (1 + z₀²)/√(2π)` for `z₀ ≥ 0`. -/
lemma integral_abs_le_z0 {z0 : ℝ} (hz0 : 0 ≤ z0) :
    ∫ z, Set.indicator (Iic z0) (fun z => |z|) z ∂γ ≤ (1 + z0 ^ 2) / √(2 * π) := by
  have hpt : ∀ z, Set.indicator (Iic z0) (fun z => |z|) z ≤
      max (-z) 0 + z0 * Set.indicator (Icc 0 z0) (fun _ => (1 : ℝ)) z := by
    intro z
    by_cases h1 : z ≤ z0
    · rw [indicator_of_mem (show z ∈ Iic z0 from h1)]
      by_cases h2 : 0 ≤ z
      · rw [indicator_of_mem (show z ∈ Icc 0 z0 from ⟨h2, h1⟩), abs_of_nonneg h2]
        have : max (-z) 0 = 0 := max_eq_right (by linarith)
        rw [this]; linarith
      · rw [indicator_of_notMem (fun h => h2 h.1), abs_of_neg (not_le.mp h2)]
        rw [max_eq_left (by linarith)]; simp
    · rw [indicator_of_notMem (show z ∉ Iic z0 from h1)]
      have : 0 ≤ max (-z) 0 := le_max_right _ _
      have : 0 ≤ z0 * Set.indicator (Icc 0 z0) (fun _ => (1 : ℝ)) z :=
        mul_nonneg hz0 (indicator_nonneg (fun _ _ => zero_le_one) _)
      linarith
  have i1 : Integrable (fun z : ℝ => max (-z) 0) γ := by
    have hid : Integrable (fun z : ℝ => z) γ := (memLp_id_gaussianReal 1).integrable le_rfl
    have : Integrable (fun z : ℝ => -z) γ := hid.neg
    exact this.sup (integrable_const 0)
  have i2 : Integrable (fun z : ℝ => z0 * Set.indicator (Icc 0 z0) (fun _ => (1 : ℝ)) z) γ :=
    ((integrable_const (1 : ℝ)).indicator measurableSet_Icc).const_mul z0
  have i0 : Integrable (fun z : ℝ => Set.indicator (Iic z0) (fun z => |z|) z) γ := by
    have : Integrable (fun z : ℝ => |z|) γ := by
      have hid : Integrable (fun z : ℝ => z) γ := (memLp_id_gaussianReal 1).integrable le_rfl
      exact hid.abs
    exact this.indicator measurableSet_Iic
  calc ∫ z, Set.indicator (Iic z0) (fun z => |z|) z ∂γ
      ≤ ∫ z, (max (-z) 0 + z0 * Set.indicator (Icc 0 z0) (fun _ => (1 : ℝ)) z) ∂γ :=
        integral_mono i0 (i1.add i2) hpt
    _ = 1 / √(2 * π) + z0 * γ.real (Icc 0 z0) := by
        rw [integral_add i1 i2, integral_γ_neg_part, integral_const_mul,
          integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one]
    _ ≤ 1 / √(2 * π) + z0 * (z0 / √(2 * π)) := by
        gcongr
        exact gauss_strip 0 z0 hz0 |>.trans (by rw [sub_zero])
    _ = (1 + z0 ^ 2) / √(2 * π) := by ring

end R522
end

end S_C10

-- ===== C11 =====
section S_C11

/-! The thin-wedge estimate: real form of `llt_two`, and the Gaussian main term (original). -/

open Finset Real MeasureTheory ProbabilityTheory Set FourierTransform
open scoped ENNReal

noncomputable section

namespace R522

/-- `llt_two` for real-valued Schwartz functions. -/
theorem llt_real {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ₁ ψ₂ : SchwartzMap ℝ ℂ)
    (f₁ f₂ : ℝ → ℝ) (h₁ : ∀ x, ψ₁ x = ((f₁ x : ℝ) : ℂ)) (h₂ : ∀ x, ψ₂ x = ((f₂ x : ℝ) : ℂ))
    (a b : ι → ℝ) (ρ : ℝ) (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1)
    (hab : ∑ i, a i * b i = ρ) {R U V η M₁ M₂ : ℝ} (hR : 0 ≤ R) (hU : 0 ≤ U) (hη : 0 ≤ η)
    (hM₁ : ∀ u, ‖𝓕 (ψ₁ : ℝ → ℂ) u‖ ≤ M₁) (hM₂ : ∀ v, ‖𝓕 (ψ₂ : ℝ → ℂ) v‖ ≤ M₂)
    (hdec : ∀ u v, |u| ≤ U → |v| ≤ V → (R < |u| ∨ R < |v|) → |Kc a b u v| + gk ρ u v ≤ η) :
    EE (fun ε => f₁ (ssum ε a) * f₂ (ssum ε b))
      ≤ ∫ z, f₁ z.1 * f₂ (ρ * z.1 + √(1 - ρ ^ 2) * z.2) ∂(γ.prod γ)
        + ((M₁ * (16 * (2 * π) ^ 4 * R ^ 4 * ((∑ i, a i ^ 4) + ∑ i, b i ^ 4))) * (2 * R) * (M₂ * (2 * R))
          + (M₁ * η) * (2 * U) * Mom 0 ψ₂ + 2 * Tail ψ₁ U * Mom 0 ψ₂ + 2 * Mom 0 ψ₁ * Tail ψ₂ V) := by
  have hρ := abs_rho_le a b ρ ha hb hab
  have h := llt_two ψ₁ ψ₂ a b ρ ha hb hab hR hU hη hM₁ hM₂ hdec
  have hσ : √(1 - ρ ^ 2) ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by linarith)
  have hG := gauss_two ψ₁ ψ₂ ρ (√(1 - ρ ^ 2))
  have hk : ∀ u v : ℝ, Complex.exp (-(2 * π ^ 2 * ((u + ρ * v) ^ 2 + √(1 - ρ ^ 2) ^ 2 * v ^ 2) : ℝ))
      = (gk ρ u v : ℂ) := by
    intro u v; unfold gk; rw [hσ, Complex.ofReal_exp]; congr 1; push_cast; ring
  simp_rw [hk] at hG
  rw [← hG] at h
  simp only [h₁, h₂] at h
  have e1 : (∑ ε : ι → ℤˣ, ((f₁ (ssum ε a) : ℝ) : ℂ) * ((f₂ (ssum ε b) : ℝ) : ℂ)) / 2 ^ Fintype.card ι
      = ((EE (fun ε => f₁ (ssum ε a) * f₂ (ssum ε b)) : ℝ) : ℂ) := by
    unfold EE; push_cast; rfl
  have e2 : ∫ z, ((f₁ z.1 : ℝ) : ℂ) * ((f₂ (ρ * z.1 + √(1 - ρ ^ 2) * z.2) : ℝ) : ℂ) ∂(γ.prod γ)
      = ((∫ z, f₁ z.1 * f₂ (ρ * z.1 + √(1 - ρ ^ 2) * z.2) ∂(γ.prod γ) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]; push_cast; rfl
  rw [e1, e2, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  linarith [le_abs_self (EE (fun ε => f₁ (ssum ε a) * f₂ (ssum ε b)) -
    ∫ z, f₁ z.1 * f₂ (ρ * z.1 + √(1 - ρ ^ 2) * z.2) ∂(γ.prod γ))]

/-! ### the Gaussian main term -/

/-- the `x`-window function. -/
def Gw (e σ h t : ℝ) : ℝ := e * (1 + 4 * e) * (σ * |t| + 2 * h)

def Bset (e σ h δ z0 : ℝ) : Set (ℝ × ℝ) :=
  {z | z.2 ≤ z0 ∧ -δ * Gw e σ h z.2 ≤ z.1 ∧ z.1 ≤ (1 + δ) * Gw e σ h z.2}

lemma Bset_meas (e σ h δ z0 : ℝ) : MeasurableSet (Bset e σ h δ z0) := by
  unfold Bset Gw
  apply MeasurableSet.inter (measurableSet_le measurable_snd measurable_const)
  apply MeasurableSet.inter
  · exact measurableSet_le (by fun_prop) measurable_fst
  · exact measurableSet_le measurable_fst (by fun_prop)

/-- the product measure of the window set. -/
lemma Bset_measure {e σ h δ z0 : ℝ} (he : 0 ≤ e) (hσ : 0 ≤ σ) (hh : 0 ≤ h) (hδ : 0 ≤ δ)
    (hz0 : 0 ≤ z0) :
    (γ.prod γ).real (Bset e σ h δ z0) ≤
      (1 + 2 * δ) / √(2 * π) * (e * (1 + 4 * e)) * (σ * (1 + z0 ^ 2) / √(2 * π) + 2 * h) := by
  have hm := Bset_meas e σ h δ z0
  set c := (1 + 2 * δ) / √(2 * π) with hc
  have hc0 : 0 ≤ c := by positivity
  -- sections
  have hsec : ∀ t, γ ((fun x => (x, t)) ⁻¹' Bset e σ h δ z0) ≤
      ENNReal.ofReal (Set.indicator (Iic z0) (fun t => c * Gw e σ h t) t) := by
    intro t
    by_cases ht : t ≤ z0
    · have : (fun x => (x, t)) ⁻¹' Bset e σ h δ z0 = Icc (-δ * Gw e σ h t) ((1 + δ) * Gw e σ h t) := by
        ext x; simp [Bset, ht]
      rw [this, indicator_of_mem (show t ∈ Iic z0 from ht)]
      have hG : 0 ≤ Gw e σ h t := by unfold Gw; positivity
      have := γ_real_Icc_le (-δ * Gw e σ h t) ((1 + δ) * Gw e σ h t)
      rw [show (1 + δ) * Gw e σ h t - -δ * Gw e σ h t = (1 + 2 * δ) * Gw e σ h t by ring,
        max_eq_left (by positivity)] at this
      rw [← ENNReal.ofReal_toReal (measure_ne_top γ _)]
      apply ENNReal.ofReal_le_ofReal
      refine this.trans (le_of_eq ?_)
      rw [hc]; ring
    · have : (fun x => (x, t)) ⁻¹' Bset e σ h δ z0 = ∅ := by
        ext x; simp [Bset, ht]
      rw [this, measure_empty]; exact bot_le
  have hint : Integrable (fun t => Set.indicator (Iic z0) (fun t => c * Gw e σ h t) t) γ := by
    have hid : Integrable (fun z : ℝ => z) γ := (memLp_id_gaussianReal 1).integrable le_rfl
    have h2 : Integrable (fun t : ℝ => c * Gw e σ h t) γ := by
      have h3 := ((hid.abs.const_mul σ).add (integrable_const (2 * h))).const_mul (c * (e * (1 + 4 * e)))
      refine h3.congr (Filter.Eventually.of_forall (fun t => ?_))
      simp only [Gw, Pi.add_apply]; ring
    exact h2.indicator measurableSet_Iic
  have hnonneg : ∀ t, 0 ≤ Set.indicator (Iic z0) (fun t => c * Gw e σ h t) t := by
    intro t; apply indicator_nonneg; intro t _; unfold Gw; positivity
  have hmeas : (γ.prod γ) (Bset e σ h δ z0) ≤
      ENNReal.ofReal (∫ t, Set.indicator (Iic z0) (fun t => c * Gw e σ h t) t ∂γ) := by
    rw [Measure.prod_apply_symm hm, ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall hnonneg)]
    exact lintegral_mono hsec
  have hreal : (γ.prod γ).real (Bset e σ h δ z0) ≤
      ∫ t, Set.indicator (Iic z0) (fun t => c * Gw e σ h t) t ∂γ := by
    rw [Measure.real]
    exact ENNReal.toReal_le_of_le_ofReal (integral_nonneg hnonneg) hmeas
  refine hreal.trans ?_
  -- integrate
  have e1 : ∀ t, Set.indicator (Iic z0) (fun t => c * Gw e σ h t) t =
      c * (e * (1 + 4 * e)) * (σ * Set.indicator (Iic z0) (fun t => |t|) t +
        2 * h * Set.indicator (Iic z0) (fun _ => (1 : ℝ)) t) := by
    intro t; by_cases ht : t ∈ Iic z0
    · simp only [indicator_of_mem ht, Gw]; ring
    · simp only [indicator_of_notMem ht]; ring
  simp_rw [e1]
  have hid : Integrable (fun z : ℝ => z) γ := (memLp_id_gaussianReal 1).integrable le_rfl
  have i1 : Integrable (fun t => Set.indicator (Iic z0) (fun t => |t|) t) γ :=
    hid.abs.indicator measurableSet_Iic
  have i2 : Integrable (fun t => Set.indicator (Iic z0) (fun _ => (1 : ℝ)) t) γ :=
    (integrable_const _).indicator measurableSet_Iic
  rw [integral_const_mul, integral_add (i1.const_mul σ) (i2.const_mul (2 * h)), integral_const_mul,
    integral_const_mul]
  have hA := integral_abs_le_z0 hz0
  have hB : ∫ t, Set.indicator (Iic z0) (fun _ => (1 : ℝ)) t ∂γ ≤ 1 := by
    rw [integral_indicator measurableSet_Iic, setIntegral_const, smul_eq_mul, mul_one]
    exact measureReal_le_one
  have hE : 0 ≤ c * (e * (1 + 4 * e)) := by positivity
  rw [hc] at hE ⊢
  apply mul_le_mul_of_nonneg_left _ hE
  have : σ * ∫ t, Set.indicator (Iic z0) (fun t => |t|) t ∂γ ≤ σ * ((1 + z0 ^ 2) / √(2 * π)) :=
    mul_le_mul_of_nonneg_left hA hσ
  have : 2 * h * ∫ t, Set.indicator (Iic z0) (fun _ => (1 : ℝ)) t ∂γ ≤ 2 * h * 1 :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  calc σ * ∫ t, Set.indicator (Iic z0) (fun t => |t|) t ∂γ + 2 * h * ∫ t, Set.indicator (Iic z0) (fun _ => (1 : ℝ)) t ∂γ
      ≤ σ * ((1 + z0 ^ 2) / √(2 * π)) + 2 * h * 1 := by linarith
    _ = σ * (1 + z0 ^ 2) / √(2 * π) + 2 * h := by ring

end R522
end

end S_C11

-- ===== C12 =====
section S_C12

/-! The thin-wedge bound for the sign-change model, with explicit error terms (original). -/

open Finset Real MeasureTheory ProbabilityTheory Set FourierTransform

noncomputable section

namespace R522

/-- shell scale -/
def lamj (e h : ℝ) (j : ℕ) : ℝ := e * (j + 1) * h

/-- the cell decay constant -/
def ηc (n : ℕ) (R ρ : ℝ) : ℝ :=
  Real.exp (-((n : ℝ) * Real.sin (1 / 2) ^ 2 / 16)) + Real.exp (-(R ^ 2 * (π ^ 2 / 8192000)))
    + Real.exp (-(2 * π ^ 2 * (1 - |ρ|) * R ^ 2))

/-- the error of shell `j`. -/
def Errj (n : ℕ) (e h δ R : ℝ) (j : ℕ) : ℝ :=
  (lamj e h j * (1 + 2 * δ) * (16 * (2 * π) ^ 4 * R ^ 4 *
      ((∑ i : Fin n, aw n i ^ 4) + ∑ i : Fin n, bw n i ^ 4))) * (2 * R) * (2 * h * (2 * R))
    + (lamj e h j * (1 + 2 * δ) * ηc n R (ρw n)) * (2 * (σa n / 4)) * Mom 0 ψ0
    + 2 * (if hδ : 0 < δ then Tail (Sb 0 1 δ one_pos hδ) (lamj e h j * (σa n / 4)) else 0) * Mom 0 ψ0
    + 2 * (if hδ : 0 < δ then Mom 0 (Sb 0 1 δ one_pos hδ) else 0) * Tail ψ0 (h * (√(n : ℝ) / 4))

/-- the Gaussian main term. -/
def GM (e σ h δ : ℝ) : ℝ :=
  (1 + 2 * δ) / √(2 * π) * (e * (1 + 4 * e)) * (σ * (1 + (2 * h / σ) ^ 2) / √(2 * π) + 2 * h)

lemma abs_ρw_le {n : ℕ} (hn : 2 ≤ n) : |ρw n| ≤ 1 := by
  have := abs_rho_le (aw n) (bw n) (ρw n) (aw_sq hn) (bw_sq hn) rfl
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (ρw n + 1), sq_nonneg (ρw n - 1)]

lemma χY_le_one' (h : ℝ) (j : ℕ) (y : ℝ) : χY h j y ≤ 1 := χ0_le_one _

lemma mem_Bset_of {e σ h δ ρ : ℝ} {j : ℕ} {z : ℝ × ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 < h)
    (he0 : 0 < e) (he : e ≤ 1 / 16) (hσ0 : 0 < σ) (hρ1 : |ρ| ≤ 1) (hlam : 0 < lamj e h j)
    (hF : 0 < bb 0 (lamj e h j) (lamj e h j * δ) hlam (mul_pos hlam hδ) z.1)
    (hχ : 0 < χY h j (ρ * z.1 + σ * z.2)) : z ∈ Bset e σ h δ (2 * h / σ) := by
  obtain ⟨x, t⟩ := z
  simp only at hF hχ
  set lam := lamj e h j with hlam_def
  have hs := χY_supp hh j hχ
  have hx : x ∈ Ioo (0 - lam * δ) (lam + lam * δ) := by
    by_contra hc
    rw [bb_zero _ _ hc] at hF; exact lt_irrefl _ hF
  simp only [zero_sub, Set.mem_Ioo] at hx
  set W := σ * |t| + 2 * h with hW
  have hW0 : 0 ≤ W := by positivity
  have hy : |ρ * x + σ * t| ≤ |x| + σ * |t| := by
    calc |ρ * x + σ * t| ≤ |ρ * x| + |σ * t| := abs_add_le _ _
      _ = |ρ| * |x| + σ * |t| := by rw [abs_mul, abs_mul, abs_of_pos hσ0]
      _ ≤ 1 * |x| + σ * |t| := by gcongr
      _ = |x| + σ * |t| := by ring
  have hlam1 : lam ≤ e * (|x| + W) := by
    have h1 : lam = e * (((j : ℝ) + 1) * h) := by rw [hlam_def, lamj]; ring
    have h2 : ((j : ℝ) + 1) * h ≤ -(ρ * x + σ * t) + 2 * h := by linarith [hs.1]
    have h3 : -(ρ * x + σ * t) ≤ |x| + σ * |t| := by
      have := neg_abs_le (ρ * x + σ * t); linarith [neg_le_abs (ρ * x + σ * t)]
    rw [h1]; apply mul_le_mul_of_nonneg_left _ he0.le; linarith
  have hxabs : |x| < 2 * lam := by
    rw [abs_lt]; constructor
    · nlinarith
    · nlinarith
  have hxW : |x| ≤ 4 * e * W := by
    have : |x| < 2 * e * (|x| + W) := by linarith
    have h7 : |x| * (1 - 2 * e) < 2 * e * W := by nlinarith
    have h8 : 0 < 1 - 2 * e := by linarith
    by_contra hc; push Not at hc
    have : 4 * e * W * (1 - 2 * e) ≤ |x| * (1 - 2 * e) := mul_le_mul_of_nonneg_right hc.le h8.le
    nlinarith
  have hlamG : lam ≤ Gw e σ h t := by
    unfold Gw
    rw [← hW]
    calc lam ≤ e * (|x| + W) := hlam1
      _ ≤ e * (4 * e * W + W) := by gcongr
      _ = e * (1 + 4 * e) * W := by ring
  have hG0 : 0 ≤ Gw e σ h t := le_trans hlam.le hlamG
  refine ⟨?_, ?_, ?_⟩
  · -- t ≤ 2h/σ
    simp only
    rw [le_div_iff₀ hσ0]
    have hy1 : ρ * x + σ * t < h := by
      have : ((j : ℝ) - 1) * h ≥ -h := by
        have : (0 : ℝ) ≤ j := by positivity
        nlinarith
      linarith [hs.1]
    have hρx : -(ρ * x) ≤ |x| := by
      have := neg_abs_le (ρ * x)
      have : |ρ * x| ≤ |x| := by rw [abs_mul]; nlinarith [abs_nonneg x]
      linarith [neg_le_abs (ρ * x)]
    by_cases ht : t ≤ 0
    · nlinarith
    · push Not at ht
      have : σ * |t| = σ * t := by rw [abs_of_pos ht]
      have : σ * t < h + 4 * e * (σ * t + 2 * h) := by
        have : σ * t < h + |x| := by linarith
        nlinarith
      nlinarith
  · simp only
    have := mul_le_mul_of_nonneg_right hlamG hδ.le
    linarith [hx.1]
  · simp only
    have := mul_le_mul_of_nonneg_right hlamG (show (0:ℝ) ≤ 1 + δ by linarith)
    linarith [hx.2]

/-- **Thin-wedge bound.** -/
theorem wedge_bound {n : ℕ} (hn : 40 ≤ n) {δ h R : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 < h)
    (hR : 0 ≤ R) (N : ℕ) (hN : 1 ≤ N)
    (he : √(n : ℝ) / σa n ≤ 1 / 16) (hσ : 0 < 1 - ρw n ^ 2) :
    PP (fun ε : Fin n → ℤˣ => 0 ≤ ssum ε (aw n) ∧ ssum ε (aw n) < -(√(n : ℝ) / σa n) * ssum ε (bw n))
      ≤ GM (√(n : ℝ) / σa n) (√(1 - ρw n ^ 2)) h δ + ∑ j ∈ range N, Errj n (√(n : ℝ) / σa n) h δ R j
        + 2 * Real.exp (-(((N : ℝ) - 1) * h) ^ 2 / 2) := by
  classical
  set e := √(n : ℝ) / σa n with he_def
  set ρ := ρw n with hρ_def
  set σ := √(1 - ρ ^ 2) with hσ_def
  have hn2 : 2 ≤ n := by omega
  have hσa := σa_pos hn2
  have hn0 : (0 : ℝ) < n := by positivity
  have he0 : 0 < e := by positivity
  have hσ0 : 0 < σ := Real.sqrt_pos.mpr hσ
  have hρ1 := abs_ρw_le hn2
  have hlam : ∀ j : ℕ, 0 < lamj e h j := fun j => by unfold lamj; positivity
  set X := fun ε : Fin n → ℤˣ => ssum ε (aw n)
  set Y := fun ε : Fin n → ℤˣ => ssum ε (bw n)
  let F : ℕ → ℝ → ℝ := fun j x => bb 0 (lamj e h j) (lamj e h j * δ) (hlam j) (mul_pos (hlam j) hδ) x
  -- (1) pointwise majorant
  have hmaj : ∀ ε : Fin n → ℤˣ, (if 0 ≤ X ε ∧ X ε < -e * Y ε then (1 : ℝ) else 0) ≤
      (∑ j ∈ range N, F j (X ε) * χY h j (Y ε)) +
        (if ((N : ℝ) - 1) * h ≤ |Y ε| then (1 : ℝ) else 0) := by
    intro ε
    have hsum0 : 0 ≤ ∑ j ∈ range N, F j (X ε) * χY h j (Y ε) :=
      sum_nonneg (fun j _ => mul_nonneg (bb_nonneg _ _ _ _ _ _) (χY_nonneg _ _ _))
    split_ifs with h1 h2 h2
    · linarith
    · -- in the wedge and not in the tail
      have hY0 : Y ε ≤ 0 := by
        have := h1.1; have := h1.2
        by_contra hc; push Not at hc
        have : -e * Y ε < 0 := by nlinarith
        linarith
      have hYN : -(((N : ℝ) - 1) * h) ≤ Y ε := by
        push Not at h2
        have := neg_abs_le (Y ε)
        linarith
      have hpart := sum_χY_eq_one hh N hY0 hYN
      have : ∑ j ∈ range N, F j (X ε) * χY h j (Y ε) = ∑ j ∈ range N, χY h j (Y ε) := by
        apply sum_congr rfl; intro j _
        by_cases hc : 0 < χY h j (Y ε)
        · have hs := χY_supp hh j hc
          have hX : X ε ∈ Icc 0 (lamj e h j) := by
            constructor
            · exact h1.1
            · have : X ε ≤ e * (-Y ε) := by linarith [h1.2]
              unfold lamj
              have : e * (-Y ε) ≤ e * (((j : ℝ) + 1) * h) := mul_le_mul_of_nonneg_left hs.2.le he0.le
              nlinarith
          have : F j (X ε) = 1 := by
            simp only [F]; exact bb_one _ _ (by simpa using hX)
          rw [this, one_mul]
        · have : χY h j (Y ε) = 0 := le_antisymm (not_lt.mp hc) (χY_nonneg _ _ _)
          rw [this, mul_zero]
      rw [this, hpart]; linarith
    · linarith
    · linarith
  -- (2) to expectations
  have hPP : PP (fun ε : Fin n → ℤˣ => 0 ≤ X ε ∧ X ε < -e * Y ε) ≤
      (∑ j ∈ range N, EE (fun ε => F j (X ε) * χY h j (Y ε))) +
        PP (fun ε : Fin n → ℤˣ => ((N : ℝ) - 1) * h ≤ |Y ε|) := by
    rw [PP_eq, PP_eq, ← EE_sum, ← EE_add]
    exact EE_mono hmaj
  -- (3) each shell
  have hshell : ∀ j ∈ range N, EE (fun ε => F j (X ε) * χY h j (Y ε)) ≤
      (∫ z, F j z.1 * χY h j (ρ * z.1 + σ * z.2) ∂(γ.prod γ)) + Errj n e h δ R j := by
    intro j _
    have hU : (0 : ℝ) ≤ σa n / 4 := by positivity
    have hη : 0 ≤ ηc n R ρ := by unfold ηc; positivity
    have hdec : ∀ u v, |u| ≤ σa n / 4 → |v| ≤ √(n : ℝ) / 4 → (R < |u| ∨ R < |v|) →
        |Kc (aw n) (bw n) u v| + gk ρ u v ≤ ηc n R ρ := by
      intro u v hu hv hout
      have hout' : R ^ 2 ≤ u ^ 2 + v ^ 2 := by
        rcases hout with h' | h'
        · have : R ^ 2 ≤ |u| ^ 2 := pow_le_pow_left₀ hR h'.le 2
          rw [sq_abs] at this; nlinarith [sq_nonneg v]
        · have : R ^ 2 ≤ |v| ^ 2 := pow_le_pow_left₀ hR h'.le 2
          rw [sq_abs] at this; nlinarith [sq_nonneg u]
      have h1 := Kc_decay hn hu hv hout'
      have h2 := gk_decay hρ1 hout'
      unfold ηc; linarith
    have hM1 := sup_ψX (hlam j) hδ
    have hM2 := sup_ψY hh j
    have key := llt_real (ψX (lamj e h j) δ (hlam j) hδ) (ψY h hh j) (F j) (χY h j)
      (fun x => by simp only [ψX, Sb_apply, F]) (fun y => ψY_apply hh j y)
      (aw n) (bw n) ρ (aw_sq hn2) (bw_sq hn2) rfl hR hU hη hM1 hM2 hdec
    refine key.trans (le_of_eq ?_)
    unfold Errj
    rw [mom0_ψY, tail_ψY, tail_ψX, mom0_ψX, dif_pos hδ, dif_pos hδ]
  -- (4) the Gaussian sum
  have hgauss : ∑ j ∈ range N, ∫ z, F j z.1 * χY h j (ρ * z.1 + σ * z.2) ∂(γ.prod γ) ≤
      GM e σ h δ := by
    have hint : ∀ j ∈ range N, Integrable (fun z : ℝ × ℝ => F j z.1 * χY h j (ρ * z.1 + σ * z.2))
        (γ.prod γ) := by
      intro j _
      refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ (Filter.Eventually.of_forall (fun z => ?_))
      · exact (((bb _ _ _ _ _).continuous.comp continuous_fst).mul
          ((χY_contDiff h j).continuous.comp (by fun_prop))).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (bb_nonneg _ _ _ _ _ _) (χY_nonneg _ _ _))]
        calc F j z.1 * χY h j (ρ * z.1 + σ * z.2) ≤ 1 * 1 :=
              mul_le_mul (bb_le_one _ _ _ _ _ _) (χY_le_one' h j _) (χY_nonneg _ _ _) zero_le_one
          _ = 1 := by ring
    rw [← integral_finset_sum _ hint]
    set f := fun z : ℝ × ℝ => ∑ j ∈ range N, F j z.1 * χY h j (ρ * z.1 + σ * z.2)
    have hf_cont : Continuous f := by
      apply continuous_finset_sum; intro j _
      exact ((bb _ _ _ _ _).continuous.comp continuous_fst).mul
        ((χY_contDiff h j).continuous.comp (by fun_prop))
    have hf0 : ∀ z, 0 ≤ f z := fun z =>
      sum_nonneg (fun j _ => mul_nonneg (bb_nonneg _ _ _ _ _ _) (χY_nonneg _ _ _))
    have hf1 : ∀ z, f z ≤ 1 := by
      intro z
      calc f z ≤ ∑ j ∈ range N, χY h j (ρ * z.1 + σ * z.2) := by
            apply sum_le_sum; intro j _
            have := bb_le_one 0 (lamj e h j) (lamj e h j * δ) (hlam j) (mul_pos (hlam j) hδ) z.1
            have := χY_nonneg h j (ρ * z.1 + σ * z.2)
            calc F j z.1 * χY h j (ρ * z.1 + σ * z.2) ≤ 1 * χY h j (ρ * z.1 + σ * z.2) := by
                  apply mul_le_mul_of_nonneg_right (bb_le_one _ _ _ _ _ _) this
              _ = _ := one_mul _
        _ ≤ 1 := sum_χY_le_one h _ N
    have hfB : ∀ z, z ∉ Bset e σ h δ (2 * h / σ) → f z = 0 := by
      intro z hz
      apply sum_eq_zero; intro j _
      by_contra hne
      have hpos : 0 < F j z.1 * χY h j (ρ * z.1 + σ * z.2) :=
        lt_of_le_of_ne (mul_nonneg (bb_nonneg _ _ _ _ _ _) (χY_nonneg _ _ _)) (Ne.symm hne)
      have hF : 0 < F j z.1 := lt_of_le_of_ne (bb_nonneg _ _ _ _ _ _) (fun h0 => by
        rw [← h0, zero_mul] at hpos; exact lt_irrefl _ hpos)
      have hχ : 0 < χY h j (ρ * z.1 + σ * z.2) := lt_of_le_of_ne (χY_nonneg _ _ _) (fun h0 => by
        rw [← h0, mul_zero] at hpos; exact lt_irrefl _ hpos)
      apply hz
      exact mem_Bset_of hδ hδ1 hh he0 he hσ0 hρ1 (hlam j) hF hχ
    have := integral_le_of_supp hf_cont hf0 hf1 (Bset_meas e σ h δ (2 * h / σ)) hfB
    refine this.trans ?_
    exact Bset_measure he0.le hσ0.le hh.le hδ.le (by positivity)
  -- (5) tail
  have htail : PP (fun ε : Fin n → ℤˣ => ((N : ℝ) - 1) * h ≤ |Y ε|) ≤
      2 * Real.exp (-(((N : ℝ) - 1) * h) ^ 2 / 2) := by
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ ((N : ℝ) - 1) * h by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith) with h0 | h0
    · rw [← h0]; simp only [zero_pow two_ne_zero, neg_zero, zero_div, Real.exp_zero, mul_one]
      linarith [PP_le_one (fun ε : Fin n → ℤˣ => (0 : ℝ) ≤ |Y ε|)]
    · have := hoeffding (bw n) h0
      rw [bw_sq hn2, mul_one] at this
      refine this.trans (le_of_eq ?_)
      congr 2; ring
  have hsh := sum_le_sum hshell
  rw [sum_add_distrib] at hsh
  have hPP' : PP (fun ε : Fin n → ℤˣ => 0 ≤ X ε ∧ X ε < -e * Y ε) =
      PP (fun ε : Fin n → ℤˣ => 0 ≤ ssum ε (aw n) ∧ ssum ε (aw n) < -(√(n : ℝ) / σa n) * ssum ε (bw n)) :=
    rfl
  rw [← hPP']
  linarith

end R522
end

end S_C12

-- ===== C13 =====
section S_C13

/-! Asymptotics of the thin-wedge bound (original). -/

open Finset Real MeasureTheory Filter Topology

noncomputable section

namespace R522

lemma natpow_neg_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-a)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop

lemma natpow_exp_tendsto (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ a * Real.exp (-b * (n : ℝ) ^ c)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a / c) b hb).comp
    ((tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop)
  refine h.congr' (Eventually.of_forall (fun n => ?_))
  simp only [Function.comp]
  rw [← Real.rpow_mul (by positivity), mul_div_cancel₀ _ hc.ne']

/-- `e_n = √n / σa n`. -/
def en (n : ℕ) : ℝ := √(n : ℝ) / σa n
def sn (n : ℕ) : ℝ := √(1 - ρw n ^ 2)

lemma σa_sq_ge {n : ℕ} (hn : 2 ≤ n) : (n : ℝ) ^ 3 / 12 ≤ σa n ^ 2 := by
  have h := σa_sq_eq n
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [mul_nonneg (sub_nonneg.mpr hn2) (sub_nonneg.mpr hn2), sq_nonneg (n : ℝ)]

lemma ne_sq {n : ℕ} (hn : 2 ≤ n) :
    ((n : ℝ) * en n) ^ 2 = 6 * (n : ℝ) ^ 2 / (((n : ℝ) - 1) * (2 * n - 1)) := by
  have hσ := σa_pos hn
  have h := σa_sq_eq n
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : ((n : ℝ) - 1) * (2 * n - 1) ≠ 0 := by
    apply mul_ne_zero <;> linarith
  rw [en, mul_div_assoc', div_pow, mul_pow, Real.sq_sqrt (by positivity)]
  rw [div_eq_div_iff (by positivity) h1]
  nlinarith

lemma ne_nonneg (n : ℕ) : 0 ≤ (n : ℝ) * en n := by
  unfold en
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp [σa]
  · have := σa_pos h; positivity

lemma tendsto_ne : Tendsto (fun n : ℕ => (n : ℝ) * en n) atTop (𝓝 (√3)) := by
  have hsq : Tendsto (fun n : ℕ => ((n : ℝ) * en n) ^ 2) atTop (𝓝 3) := by
    have e : ∀ᶠ n : ℕ in atTop, ((n : ℝ) * en n) ^ 2 =
        6 / ((1 - 1 / (n : ℝ)) * (2 - 1 / (n : ℝ))) := by
      filter_upwards [eventually_ge_atTop 2] with n hn
      rw [ne_sq hn]
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp
    refine Tendsto.congr' (EventuallyEq.symm e) ?_
    have h1 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 1
    have hA : Tendsto (fun n : ℕ => (1 - 1 / (n : ℝ)) * (2 - 1 / (n : ℝ))) atTop
        (𝓝 ((1 - 0) * (2 - 0))) :=
      ((tendsto_const_nhds (x := (1:ℝ))).sub h1).mul ((tendsto_const_nhds (x := (2:ℝ))).sub h1)
    have hB : Tendsto (fun n : ℕ => 6 / ((1 - 1 / (n : ℝ)) * (2 - 1 / (n : ℝ)))) atTop
        (𝓝 (6 / ((1 - 0) * (2 - 0)))) :=
      (tendsto_const_nhds (x := (6:ℝ))).div hA (by norm_num)
    convert hB using 2; norm_num
  have := (Real.continuous_sqrt.tendsto 3).comp hsq
  refine this.congr' (Eventually.of_forall (fun n => ?_))
  simp only [Function.comp]
  exact Real.sqrt_sq (ne_nonneg n)

lemma tendsto_en : Tendsto en atTop (𝓝 0) := by
  have h := tendsto_ne.mul (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp

lemma ρw_eq {n : ℕ} (hn : 2 ≤ n) : ρw n = ((n : ℝ) * (n - 1) / 2) / (σa n * √(n : ℝ)) := by
  unfold ρw aw bw
  have : ∑ j : Fin n, wt n j / σa n * (1 / √(n : ℝ)) = (∑ j : Fin n, wt n j) / (σa n * √(n : ℝ)) := by
    rw [sum_div]; apply sum_congr rfl; intro j _; field_simp
  rw [this, sum_wt]
  congr 1
  have := sum_range_cast n
  linarith

lemma one_sub_ρw_sq {n : ℕ} (hn : 2 ≤ n) : 1 - ρw n ^ 2 = ((n : ℝ) + 1) / (2 * (2 * n - 1)) := by
  rw [ρw_eq hn, div_pow, mul_pow, Real.sq_sqrt (by positivity)]
  have hσ := σa_pos hn
  have h := σa_sq_eq n
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 2 * (2 * (n : ℝ) - 1) ≠ 0 := by
    apply mul_ne_zero (by norm_num); linarith
  rw [sub_eq_iff_eq_add, div_add_div _ _ hd (by positivity), eq_div_iff (by positivity)]
  have hσ2 : σa n ^ 2 = (n : ℝ) * (n - 1) * (2 * n - 1) / 6 := by linarith
  rw [hσ2]
  ring

lemma ρw_sq_lt {n : ℕ} (hn : 2 ≤ n) : ρw n ^ 2 ≤ 3 / 4 := by
  have := one_sub_ρw_sq hn
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have : 1 / 4 ≤ ((n : ℝ) + 1) / (2 * (2 * n - 1)) := by
    rw [div_le_div_iff₀ (by norm_num) (by nlinarith)]; nlinarith
  linarith

lemma tendsto_sn : Tendsto sn atTop (𝓝 (1 / 2)) := by
  have h1 : Tendsto (fun n : ℕ => 1 - ρw n ^ 2) atTop (𝓝 (1 / 4)) := by
    have e : ∀ᶠ n : ℕ in atTop, 1 - ρw n ^ 2 = (1 + 1 / (n : ℝ)) / (2 * (2 - 1 / (n : ℝ))) := by
      filter_upwards [eventually_ge_atTop 2] with n hn
      rw [one_sub_ρw_sq hn]
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp
    refine Tendsto.congr' (EventuallyEq.symm e) ?_
    have h0 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 1
    have hA : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
      (tendsto_const_nhds (x := (1:ℝ))).add h0
    have hB : Tendsto (fun n : ℕ => 2 * (2 - 1 / (n : ℝ))) atTop (𝓝 (2 * (2 - 0))) :=
      (tendsto_const_nhds (x := (2:ℝ))).mul ((tendsto_const_nhds (x := (2:ℝ))).sub h0)
    have := hA.div hB (by norm_num)
    rw [show ((1:ℝ) + 0) / (2 * (2 - 0)) = 1 / 4 by norm_num] at this
    exact this
  have := (Real.continuous_sqrt.tendsto (1 / 4)).comp h1
  have hs : √(1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hs] at this
  exact this

/-- the limit constant of `n · GM`. -/
def GMlim (h δ : ℝ) : ℝ :=
  (1 + 2 * δ) / √(2 * π) * √3 * ((1 / 2) * (1 + (4 * h) ^ 2) / √(2 * π) + 2 * h)

lemma tendsto_GM (h δ : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) * GM (en n) (sn n) h δ) atTop (𝓝 (GMlim h δ)) := by
  have hs := tendsto_sn
  have he := tendsto_en
  have hne := tendsto_ne
  have e : ∀ n : ℕ, (n : ℝ) * GM (en n) (sn n) h δ =
      (1 + 2 * δ) / √(2 * π) * ((n : ℝ) * en n) * (1 + 4 * en n) *
        (sn n * (1 + (2 * h / sn n) ^ 2) / √(2 * π) + 2 * h) := by
    intro n; unfold GM; ring
  simp_rw [e]
  unfold GMlim
  have h2 : Tendsto (fun n : ℕ => 2 * h / sn n) atTop (𝓝 (4 * h)) := by
    have := (tendsto_const_nhds (x := 2 * h)).div hs (by norm_num)
    rw [show 2 * h / (1 / 2 : ℝ) = 4 * h by ring] at this
    exact this
  have := ((((tendsto_const_nhds (x := (1 + 2 * δ) / √(2 * π))).mul hne).mul
    ((tendsto_const_nhds (x := (1:ℝ))).add ((tendsto_const_nhds (x := (4:ℝ))).mul he))).mul
    (((hs.mul ((tendsto_const_nhds (x := (1:ℝ))).add (h2.pow 2))).div_const (√(2 * π))).add
      (tendsto_const_nhds (x := 2 * h))))
  rw [show (1 + 2 * δ) / √(2 * π) * √3 * (1 + 4 * 0) * (1 / 2 * (1 + (4 * h) ^ 2) / √(2 * π) + 2 * h)
    = (1 + 2 * δ) / √(2 * π) * √3 * (1 / 2 * (1 + (4 * h) ^ 2) / √(2 * π) + 2 * h) by ring] at this
  exact this

end R522
end

end S_C13

-- ===== C14 =====
section S_C14

/-! The error terms vanish; the sign-change probability bound `p ≤ (√3/(2π) + θ)/n` (original). -/

open Finset Real MeasureTheory Filter Topology

noncomputable section

namespace R522

def Rn (n : ℕ) : ℝ := (n : ℝ) ^ ((1 : ℝ) / 8)
def Nn (n : ℕ) : ℕ := ⌊(n : ℝ) ^ ((1 : ℝ) / 16)⌋₊ + 2

lemma Tail_anti (ψ : SchwartzMap ℝ ℂ) {U U' : ℝ} (h : U' ≤ U) : Tail ψ U ≤ Tail ψ U' := by
  unfold Tail
  apply integral_mono_of_nonneg
  · exact Eventually.of_forall (fun u => Set.indicator_nonneg (fun _ _ => norm_nonneg _) u)
  · exact integrable_ind_gt ψ U'
  · refine Eventually.of_forall (fun u => ?_)
    simp only [Set.indicator, Set.mem_setOf_eq]
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact absurd (lt_of_le_of_lt h h1) h2
    · exact norm_nonneg _
    · exact le_rfl

lemma Nn_le (n : ℕ) (hn : 1 ≤ n) : (Nn n : ℝ) ≤ 3 * (n : ℝ) ^ ((1 : ℝ) / 16) := by
  unfold Nn
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 16) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have := Nat.floor_le (show 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 16) by positivity)
  push_cast; linarith

lemma Nn_ge (n : ℕ) : (n : ℝ) ^ ((1 : ℝ) / 16) ≤ (Nn n : ℝ) - 1 := by
  unfold Nn
  have := Nat.lt_floor_add_one ((n : ℝ) ^ ((1 : ℝ) / 16))
  push_cast; linarith

lemma Nn_one (n : ℕ) : 1 ≤ Nn n := by unfold Nn; omega

lemma ne_le_two {n : ℕ} (hn : 6 ≤ n) : (n : ℝ) * en n ≤ 2 := by
  have h := ne_sq (show 2 ≤ n by omega)
  have hn6 : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < ((n : ℝ) - 1) * (2 * n - 1) := by apply mul_pos <;> linarith
  have : ((n : ℝ) * en n) ^ 2 ≤ 2 ^ 2 := by
    rw [h, div_le_iff₀ hpos]; nlinarith
  exact (pow_le_pow_iff_left₀ (ne_nonneg n) (by norm_num) two_ne_zero).mp this

lemma σa_le {n : ℕ} : σa n ≤ (n : ℝ) ^ ((3 : ℝ) / 2) := by
  have h := σa_sq_eq n
  rcases Nat.lt_or_ge n 1 with hn | hn
  · interval_cases n; simp [σa]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have e : ((n : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = (n : ℝ) ^ 3 := by
      rw [← Real.rpow_natCast ((n : ℝ) ^ ((3 : ℝ) / 2)) 2, ← Real.rpow_mul (by positivity)]
      norm_num
    have h2 : σa n ^ 2 ≤ ((n : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 := by
      rw [e]
      nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sub_nonneg.mpr hn1)]
    have hσ0 : 0 ≤ σa n := Real.sqrt_nonneg _
    exact (pow_le_pow_iff_left₀ hσ0 (by positivity) two_ne_zero).mp h2

lemma A4_le {n : ℕ} (hn : 2 ≤ n) : ∑ i : Fin n, aw n i ^ 4 ≤ 144 / n := by
  have hσ := σa_pos hn
  have h1 : ∑ i : Fin n, aw n i ^ 4 = (∑ w ∈ range n, (w : ℝ) ^ 4) / (σa n ^ 2) ^ 2 := by
    simp only [aw, div_pow]
    rw [← sum_div, sum_wt_four]; ring
  rw [h1]
  have h2 := sum_four_le n
  have h3 := σa_sq_ge hn
  have hn0 : (0 : ℝ) < n := by positivity
  rw [div_le_div_iff₀ (by positivity) hn0]
  have : ((n : ℝ) ^ 3 / 12) ^ 2 ≤ (σa n ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
  nlinarith

lemma B4_eq {n : ℕ} (hn : 1 ≤ n) : ∑ i : Fin n, bw n i ^ 4 = 1 / n := by
  simp only [bw, div_pow, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : √(n : ℝ) ^ 4 = (n : ℝ) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt (by positivity)]
  rw [this]
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp

end R522

namespace R522

lemma Rn_sq (n : ℕ) : Rn n ^ 2 = (n : ℝ) ^ ((1 : ℝ) / 4) := by
  unfold Rn
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num

lemma Rn_six (n : ℕ) : Rn n ^ 6 = (n : ℝ) ^ ((3 : ℝ) / 4) := by
  unfold Rn
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num

def c1 : ℝ := π ^ 2 / 8192000

lemma ηc_le {n : ℕ} (hn : 2 ≤ n) :
    ηc n (Rn n) (ρw n) ≤ 3 * Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4))) := by
  unfold ηc
  have hR2 := Rn_sq n
  have hpi := Real.pi_lt_d2
  have hpi' := Real.pi_gt_three
  have hc1 : c1 ≤ 1 / 100000 := by unfold c1; rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
  have hc0 : 0 < c1 := by unfold c1; positivity
  have hq : (n : ℝ) ^ ((1 : ℝ) / 4) ≤ n := by
    apply Real.rpow_le_self_of_one_le (by exact_mod_cast (show 1 ≤ n by omega)) (by norm_num)
  have hq0 : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := by positivity
  -- term 1
  have hs : (1 / 100 : ℝ) ≤ Real.sin (1 / 2) ^ 2 := by
    have := Real.sin_gt_sub_cube (x := 1 / 2) (by norm_num)
    nlinarith
  have t1 : Real.exp (-((n : ℝ) * Real.sin (1 / 2) ^ 2 / 16)) ≤ Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4))) := by
    apply Real.exp_le_exp.mpr
    have : c1 * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ (n : ℝ) * Real.sin (1 / 2) ^ 2 / 16 := by
      have : c1 * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ (1 / 100000) * n := by
        apply mul_le_mul hc1 hq hq0 (by norm_num)
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    linarith
  have t2 : Real.exp (-(Rn n ^ 2 * (π ^ 2 / 8192000))) = Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4))) := by
    rw [hR2, c1]; ring_nf
  have t3 : Real.exp (-(2 * π ^ 2 * (1 - |ρw n|) * Rn n ^ 2)) ≤ Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4))) := by
    apply Real.exp_le_exp.mpr
    have hρ := ρw_sq_lt hn
    have hρa : |ρw n| ≤ 9 / 10 := by
      have : |ρw n| ^ 2 ≤ (9 / 10) ^ 2 := by rw [sq_abs]; nlinarith
      exact (pow_le_pow_iff_left₀ (abs_nonneg _) (by norm_num) two_ne_zero).mp this
    rw [hR2]
    have : c1 ≤ 2 * π ^ 2 * (1 - |ρw n|) := by nlinarith
    nlinarith
  linarith

end R522
end

end S_C14

-- ===== C15 =====
section S_C15

/-! The error terms of the thin-wedge bound vanish (original). -/

open Finset Real MeasureTheory Filter Topology

noncomputable section

namespace R522

lemma en_σa {n : ℕ} (hn : 2 ≤ n) : en n * σa n = √(n : ℝ) := by
  unfold en; have := σa_pos hn; field_simp

lemma Errj_le {n : ℕ} (hn : 40 ≤ n) {δ h : ℝ} (hδ : 0 < δ) (hh : 0 < h) {j : ℕ} (hj : j < Nn n) :
    Errj n (en n) h δ (Rn n) j ≤
      en n * Nn n * h * (1 + 2 * δ) * (16 * (2 * π) ^ 4 * Rn n ^ 4 * (145 / n)) * (2 * Rn n) * (2 * h * (2 * Rn n))
      + en n * Nn n * h * (1 + 2 * δ) * (3 * Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4)))) * (2 * (σa n / 4)) * Mom 0 ψ0
      + 2 * (Mom 4 (Sb 0 1 δ one_pos hδ) / (h * (√(n : ℝ) / 4)) ^ 4) * Mom 0 ψ0
      + 2 * Mom 0 (Sb 0 1 δ one_pos hδ) * (Mom 4 ψ0 / (h * (√(n : ℝ) / 4)) ^ 4) := by
  simp only [Errj]
  rw [dif_pos hδ, dif_pos hδ]
  have hn2 : 2 ≤ n := by omega
  have hσ := σa_pos hn2
  have he0 : 0 < en n := by unfold en; positivity
  have hn0 : (0 : ℝ) < n := by positivity
  have hR0 : 0 ≤ Rn n := by unfold Rn; positivity
  have hlam : lamj (en n) h j ≤ en n * Nn n * h := by
    unfold lamj
    have : ((j : ℝ) + 1) ≤ Nn n := by exact_mod_cast hj
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this he0.le) hh.le
  have hlam0 : 0 ≤ lamj (en n) h j := by unfold lamj; positivity
  have hAB : (∑ i : Fin n, aw n i ^ 4) + ∑ i : Fin n, bw n i ^ 4 ≤ 145 / n := by
    have := A4_le hn2
    rw [B4_eq (by omega)]
    have : (144 : ℝ) / n + 1 / n = 145 / n := by ring
    linarith
  have hAB0 : 0 ≤ (∑ i : Fin n, aw n i ^ 4) + ∑ i : Fin n, bw n i ^ 4 :=
    add_nonneg (sum_nonneg (fun _ _ => by positivity)) (sum_nonneg (fun _ _ => by positivity))
  have hη := ηc_le hn2
  have hη0 : 0 ≤ ηc n (Rn n) (ρw n) := by unfold ηc; positivity
  have hthr : h * (√(n : ℝ) / 4) ≤ lamj (en n) h j * (σa n / 4) := by
    have e : lamj (en n) h j * (σa n / 4) = ((j : ℝ) + 1) * h * (en n * σa n) / 4 := by
      unfold lamj; ring
    rw [e, en_σa hn2]
    have : (1 : ℝ) ≤ (j : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
    have hs : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
    have : h * √(n : ℝ) ≤ ((j : ℝ) + 1) * h * √(n : ℝ) := by
      have := mul_le_mul_of_nonneg_right this (mul_nonneg hh.le hs)
      linarith
    linarith
  have hthr0 : 0 < h * (√(n : ℝ) / 4) := by positivity
  have hT1 : Tail (Sb 0 1 δ one_pos hδ) (lamj (en n) h j * (σa n / 4)) ≤
      Mom 4 (Sb 0 1 δ one_pos hδ) / (h * (√(n : ℝ) / 4)) ^ 4 :=
    (Tail_anti _ hthr).trans (tail_le_mom4 _ hthr0)
  have hT2 : Tail ψ0 (h * (√(n : ℝ) / 4)) ≤ Mom 4 ψ0 / (h * (√(n : ℝ) / 4)) ^ 4 :=
    tail_le_mom4 _ hthr0
  have hm0 : 0 ≤ Mom 0 ψ0 := mom_nonneg 0 ψ0
  have hmS : 0 ≤ Mom 0 (Sb 0 1 δ one_pos hδ) := mom_nonneg 0 _
  have e1 : lamj (en n) h j * (1 + 2 * δ) * (16 * (2 * π) ^ 4 * Rn n ^ 4 *
      ((∑ i : Fin n, aw n i ^ 4) + ∑ i : Fin n, bw n i ^ 4)) * (2 * Rn n) * (2 * h * (2 * Rn n)) ≤
      en n * Nn n * h * (1 + 2 * δ) * (16 * (2 * π) ^ 4 * Rn n ^ 4 * (145 / n)) * (2 * Rn n) *
        (2 * h * (2 * Rn n)) := by
    gcongr
  have e2 : lamj (en n) h j * (1 + 2 * δ) * ηc n (Rn n) (ρw n) * (2 * (σa n / 4)) * Mom 0 ψ0 ≤
      en n * Nn n * h * (1 + 2 * δ) * (3 * Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4)))) *
        (2 * (σa n / 4)) * Mom 0 ψ0 := by
    gcongr
  have e3 : 2 * Tail (Sb 0 1 δ one_pos hδ) (lamj (en n) h j * (σa n / 4)) * Mom 0 ψ0 ≤
      2 * (Mom 4 (Sb 0 1 δ one_pos hδ) / (h * (√(n : ℝ) / 4)) ^ 4) * Mom 0 ψ0 := by
    gcongr
  have e4 : 2 * Mom 0 (Sb 0 1 δ one_pos hδ) * Tail ψ0 (h * (√(n : ℝ) / 4)) ≤
      2 * Mom 0 (Sb 0 1 δ one_pos hδ) * (Mom 4 ψ0 / (h * (√(n : ℝ) / 4)) ^ 4) := by
    gcongr
  linarith

end R522
end

end S_C15

-- ===== C16 =====
section S_C16

/-! Total error → 0, and the sign-change bound (original). -/

open Finset Real MeasureTheory Filter Topology

noncomputable section

namespace R522

lemma rp_mul (n : ℕ) (a b : ℝ) (hn : 1 ≤ n) : (n : ℝ) ^ a * (n : ℝ) ^ b = (n : ℝ) ^ (a + b) := by
  rw [← Real.rpow_add (by exact_mod_cast (show 0 < n by omega))]

lemma rp_div (n : ℕ) (a : ℝ) (hn : 1 ≤ n) : (n : ℝ) ^ a / n = (n : ℝ) ^ (a - 1) := by
  rw [Real.rpow_sub (by exact_mod_cast (show 0 < n by omega)), Real.rpow_one]

lemma Nn_sq_le (n : ℕ) (hn : 1 ≤ n) : (Nn n : ℝ) ^ 2 ≤ 9 * (n : ℝ) ^ ((1 : ℝ) / 8) := by
  have h := Nn_le n hn
  have h0 : (0 : ℝ) ≤ Nn n := by positivity
  have : (Nn n : ℝ) ^ 2 ≤ (3 * (n : ℝ) ^ ((1 : ℝ) / 16)) ^ 2 := pow_le_pow_left₀ h0 h 2
  rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / 16)) 2, ← Real.rpow_mul (by positivity)] at this
  norm_num at this ⊢
  linarith

/-- the explicit total bound -/
def Btot (h δ : ℝ) (hδ : 0 < δ) (n : ℕ) : ℝ :=
  18 * (h * (1 + 2 * δ) * (16 * (2 * π) ^ 4) * 145 * (8 * h)) * (n : ℝ) ^ (-(1 / 8 : ℝ))
  + 27 * h * (1 + 2 * δ) * Mom 0 ψ0 * ((n : ℝ) ^ (13 / 8 : ℝ) * Real.exp (-c1 * (n : ℝ) ^ (1 / 4 : ℝ)))
  + 3 * (256 * (2 * Mom 4 (Sb 0 1 δ one_pos hδ) * Mom 0 ψ0 + 2 * Mom 0 (Sb 0 1 δ one_pos hδ) * Mom 4 ψ0)
      / h ^ 4) * (n : ℝ) ^ (-(15 / 16 : ℝ))
  + 2 * ((n : ℝ) ^ (1 : ℝ) * Real.exp (-(h ^ 2 / 2) * (n : ℝ) ^ (1 / 8 : ℝ)))

lemma tendsto_Btot (h δ : ℝ) (hδ : 0 < δ) (hh : 0 < h) : Tendsto (Btot h δ hδ) atTop (𝓝 0) := by
  have c1p : 0 < c1 := by unfold c1; positivity
  have t1 := natpow_neg_tendsto (a := 1 / 8) (by norm_num)
  have t2 := natpow_exp_tendsto (13 / 8) c1 (1 / 4) c1p (by norm_num)
  have t3 := natpow_neg_tendsto (a := 15 / 16) (by norm_num)
  have t4 := natpow_exp_tendsto 1 (h ^ 2 / 2) (1 / 8) (by positivity) (by norm_num)
  have := (((t1.const_mul (18 * (h * (1 + 2 * δ) * (16 * (2 * π) ^ 4) * 145 * (8 * h)))).add
    (t2.const_mul (27 * h * (1 + 2 * δ) * Mom 0 ψ0))).add
    (t3.const_mul (3 * (256 * (2 * Mom 4 (Sb 0 1 δ one_pos hδ) * Mom 0 ψ0 +
      2 * Mom 0 (Sb 0 1 δ one_pos hδ) * Mom 4 ψ0) / h ^ 4)))).add (t4.const_mul 2)
  simp only [mul_zero, add_zero] at this
  exact this

theorem err_le_Btot {n : ℕ} (hn : 40 ≤ n) {h δ : ℝ} (hδ : 0 < δ) (hh : 0 < h) :
    (n : ℝ) * (∑ j ∈ range (Nn n), Errj n (en n) h δ (Rn n) j
      + 2 * Real.exp (-(((Nn n : ℝ) - 1) * h) ^ 2 / 2)) ≤ Btot h δ hδ n := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by positivity
  have hsum : ∑ j ∈ range (Nn n), Errj n (en n) h δ (Rn n) j ≤ (Nn n) *
      ((en n) * (Nn n) * h * (1 + 2 * δ) * (16 * (2 * π) ^ 4 * (Rn n) ^ 4 * (145 / n)) * (2 * (Rn n)) * (2 * h * (2 * (Rn n)))
      + (en n) * (Nn n) * h * (1 + 2 * δ) * (3 * Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4)))) * (2 * (σa n / 4)) * Mom 0 ψ0
      + 2 * (Mom 4 (Sb 0 1 δ one_pos hδ) / (h * (√(n : ℝ) / 4)) ^ 4) * Mom 0 ψ0
      + 2 * Mom 0 (Sb 0 1 δ one_pos hδ) * (Mom 4 ψ0 / (h * (√(n : ℝ) / 4)) ^ 4)) := by
    have := sum_le_card_nsmul (range (Nn n)) (fun j => Errj n (en n) h δ (Rn n) j) _
      (fun j hj => Errj_le hn hδ hh (mem_range.mp hj))
    rw [card_range, nsmul_eq_mul] at this
    exact this
  have hne := ne_le_two (show 6 ≤ n by omega)
  have hN2 := Nn_sq_le n hn1
  have hR6 := Rn_six n
  have hσ := σa_le (n := n)
  have hNl := Nn_le n hn1
  have hNg := Nn_ge n
  have he0 : 0 ≤ (en n) := by unfold en; have := σa_pos hn2; positivity
  have hm0 := mom_nonneg 0 ψ0
  have hm4 := mom_nonneg 4 ψ0
  have hs0 := mom_nonneg 0 (Sb 0 1 δ one_pos hδ)
  have hs4 := mom_nonneg 4 (Sb 0 1 δ one_pos hδ)
  have hexp0 : 0 ≤ Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4))) := (Real.exp_pos _).le
  -- piece 1
  have p1 : (n : ℝ) * ((Nn n) * ((en n) * (Nn n) * h * (1 + 2 * δ) * (16 * (2 * π) ^ 4 * (Rn n) ^ 4 * (145 / n)) * (2 * (Rn n)) *
      (2 * h * (2 * (Rn n))))) ≤
      18 * (h * (1 + 2 * δ) * (16 * (2 * π) ^ 4) * 145 * (8 * h)) * (n : ℝ) ^ (-(1 / 8 : ℝ)) := by
    have e1 : (n : ℝ) * ((Nn n) * ((en n) * (Nn n) * h * (1 + 2 * δ) * (16 * (2 * π) ^ 4 * (Rn n) ^ 4 * (145 / n)) * (2 * (Rn n)) *
        (2 * h * (2 * (Rn n))))) =
        ((n : ℝ) * (en n)) * ((Nn n) : ℝ) ^ 2 * (h * (1 + 2 * δ) * (16 * (2 * π) ^ 4) * 145 * (8 * h)) * (Rn n) ^ 6 / n := by
      field_simp; ring
    rw [e1, hR6]
    have hK : 0 ≤ h * (1 + 2 * δ) * (16 * (2 * π) ^ 4) * 145 * (8 * h) := by positivity
    have e2 : (n : ℝ) ^ ((1 : ℝ) / 8) * (n : ℝ) ^ ((3 : ℝ) / 4) / n = (n : ℝ) ^ (-(1 / 8 : ℝ)) := by
      rw [rp_mul n _ _ hn1, rp_div n _ hn1]; norm_num
    calc ((n : ℝ) * (en n)) * ((Nn n) : ℝ) ^ 2 * (h * (1 + 2 * δ) * (16 * (2 * π) ^ 4) * 145 * (8 * h)) *
          (n : ℝ) ^ ((3 : ℝ) / 4) / n
        ≤ 2 * (9 * (n : ℝ) ^ ((1 : ℝ) / 8)) * (h * (1 + 2 * δ) * (16 * (2 * π) ^ 4) * 145 * (8 * h)) *
          (n : ℝ) ^ ((3 : ℝ) / 4) / n := by
          gcongr
      _ = 18 * (h * (1 + 2 * δ) * (16 * (2 * π) ^ 4) * 145 * (8 * h)) *
          ((n : ℝ) ^ ((1 : ℝ) / 8) * (n : ℝ) ^ ((3 : ℝ) / 4) / n) := by ring
      _ = _ := by rw [e2]
  -- piece 2
  have p2 : (n : ℝ) * ((Nn n) * ((en n) * (Nn n) * h * (1 + 2 * δ) * (3 * Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4)))) *
      (2 * (σa n / 4)) * Mom 0 ψ0)) ≤
      27 * h * (1 + 2 * δ) * Mom 0 ψ0 * ((n : ℝ) ^ (13 / 8 : ℝ) * Real.exp (-c1 * (n : ℝ) ^ (1 / 4 : ℝ))) := by
    have e1 : (n : ℝ) * ((Nn n) * ((en n) * (Nn n) * h * (1 + 2 * δ) * (3 * Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4)))) *
        (2 * (σa n / 4)) * Mom 0 ψ0)) =
        ((n : ℝ) * (en n)) * ((Nn n) : ℝ) ^ 2 * σa n * (h * (1 + 2 * δ) * Mom 0 ψ0 * (3 / 2)) *
          Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4))) := by ring
    rw [e1]
    have e2 : (n : ℝ) ^ ((1 : ℝ) / 8) * (n : ℝ) ^ ((3 : ℝ) / 2) = (n : ℝ) ^ (13 / 8 : ℝ) := by
      rw [rp_mul n _ _ hn1]; norm_num
    have hK : 0 ≤ h * (1 + 2 * δ) * Mom 0 ψ0 * (3 / 2) := by positivity
    have hσ0 : 0 ≤ σa n := Real.sqrt_nonneg _
    calc ((n : ℝ) * (en n)) * ((Nn n) : ℝ) ^ 2 * σa n * (h * (1 + 2 * δ) * Mom 0 ψ0 * (3 / 2)) *
          Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4)))
        ≤ 2 * (9 * (n : ℝ) ^ ((1 : ℝ) / 8)) * (n : ℝ) ^ ((3 : ℝ) / 2) *
          (h * (1 + 2 * δ) * Mom 0 ψ0 * (3 / 2)) * Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4))) := by
          gcongr
      _ = 27 * h * (1 + 2 * δ) * Mom 0 ψ0 * (((n : ℝ) ^ ((1 : ℝ) / 8) * (n : ℝ) ^ ((3 : ℝ) / 2)) *
          Real.exp (-(c1 * (n : ℝ) ^ ((1 : ℝ) / 4)))) := by ring
      _ = _ := by rw [e2]; congr 3; ring
  -- pieces 3, 4
  have p3 : (n : ℝ) * ((Nn n) * (2 * (Mom 4 (Sb 0 1 δ one_pos hδ) / (h * (√(n : ℝ) / 4)) ^ 4) * Mom 0 ψ0
      + 2 * Mom 0 (Sb 0 1 δ one_pos hδ) * (Mom 4 ψ0 / (h * (√(n : ℝ) / 4)) ^ 4))) ≤
      3 * (256 * (2 * Mom 4 (Sb 0 1 δ one_pos hδ) * Mom 0 ψ0 + 2 * Mom 0 (Sb 0 1 δ one_pos hδ) * Mom 4 ψ0)
        / h ^ 4) * (n : ℝ) ^ (-(15 / 16 : ℝ)) := by
    have hq : (h * (√(n : ℝ) / 4)) ^ 4 = h ^ 4 * (n : ℝ) ^ 2 / 256 := by
      rw [mul_pow, div_pow, show (4 : ℕ) = 2 * 2 by rfl, pow_mul (√(n : ℝ)), Real.sq_sqrt hn0.le]
      norm_num; ring
    rw [hq]
    set K := 256 * (2 * Mom 4 (Sb 0 1 δ one_pos hδ) * Mom 0 ψ0 + 2 * Mom 0 (Sb 0 1 δ one_pos hδ) * Mom 4 ψ0)
      / h ^ 4 with hK
    have hK0 : 0 ≤ K := by rw [hK]; positivity
    have e1 : (n : ℝ) * ((Nn n) * (2 * (Mom 4 (Sb 0 1 δ one_pos hδ) / (h ^ 4 * (n : ℝ) ^ 2 / 256)) * Mom 0 ψ0
        + 2 * Mom 0 (Sb 0 1 δ one_pos hδ) * (Mom 4 ψ0 / (h ^ 4 * (n : ℝ) ^ 2 / 256)))) = K * ((Nn n) / n) := by
      rw [hK]; field_simp
    rw [e1]
    have e2 : (n : ℝ) ^ ((1 : ℝ) / 16) / n = (n : ℝ) ^ (-(15 / 16 : ℝ)) := by
      rw [rp_div n _ hn1]; norm_num
    calc K * ((Nn n) / n) ≤ K * (3 * (n : ℝ) ^ ((1 : ℝ) / 16) / n) := by gcongr
      _ = 3 * K * ((n : ℝ) ^ ((1 : ℝ) / 16) / n) := by ring
      _ = _ := by rw [e2]
  -- tail
  have p4 : (n : ℝ) * (2 * Real.exp (-((((Nn n) : ℝ) - 1) * h) ^ 2 / 2)) ≤
      2 * ((n : ℝ) ^ (1 : ℝ) * Real.exp (-(h ^ 2 / 2) * (n : ℝ) ^ (1 / 8 : ℝ))) := by
    rw [Real.rpow_one]
    have : -((((Nn n) : ℝ) - 1) * h) ^ 2 / 2 ≤ -(h ^ 2 / 2) * (n : ℝ) ^ (1 / 8 : ℝ) := by
      have h1 : (n : ℝ) ^ ((1 : ℝ) / 8) = ((n : ℝ) ^ ((1 : ℝ) / 16)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      have h2 : ((n : ℝ) ^ ((1 : ℝ) / 16)) ^ 2 ≤ (((Nn n) : ℝ) - 1) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hNg 2
      rw [show (1 / 8 : ℝ) = (1 : ℝ) / 8 by norm_num, h1]
      nlinarith [sq_nonneg h]
    have := Real.exp_le_exp.mpr this
    nlinarith
  have hfin := mul_le_mul_of_nonneg_left hsum hn0.le
  unfold Btot
  rw [mul_add]
  have hsplit := congrArg id (rfl : (0:ℝ) = 0)
  linarith [p1, p2, p3, p4, hfin, show ∀ a b c d : ℝ, (n : ℝ) * ((Nn n : ℝ) * (a + b + c + d)) =
    (n : ℝ) * ((Nn n : ℝ) * a) + (n : ℝ) * ((Nn n : ℝ) * b) + (n : ℝ) * ((Nn n : ℝ) * (c + d)) from
    fun a b c d => by ring]

end R522
end

end S_C16

-- ===== C17 =====
section S_C17

/-! **Sign-change bound.** For the sequence `c = ∑ ε_j (n-1-j)`, `S = ∑ ε_j` over `n` signs, the
probability that `c` and `c + S` have a strict/weak sign change is at most `(√3/(2π) + θ)/n`
for large `n` (original). -/

open Finset Real MeasureTheory Filter Topology

noncomputable section

namespace R522

/-- the sign-change event. -/
def SCev (n : ℕ) (ε : Fin n → ℤˣ) : Prop :=
  (0 ≤ ssum ε (wt n) ∧ ssum ε (wt n) + ssum ε (fun _ => (1 : ℝ)) < 0) ∨
  (ssum ε (wt n) ≤ 0 ∧ 0 < ssum ε (wt n) + ssum ε (fun _ => (1 : ℝ)))

lemma ssum_neg {ι : Type*} [Fintype ι] (ε : ι → ℤˣ) (c : ι → ℝ) :
    ssum (fun i => -ε i) c = -ssum ε c := by
  unfold ssum; rw [← sum_neg_distrib]; apply sum_congr rfl; intro i _; push_cast; ring

lemma PP_flip {ι : Type*} [Fintype ι] [DecidableEq ι] (S : (ι → ℤˣ) → Prop) :
    PP (fun ε => S (fun i => -ε i)) = PP S := by
  classical
  rw [PP_eq, PP_eq]
  unfold EE
  congr 1
  exact Fintype.sum_equiv (Equiv.neg (ι → ℤˣ)) _ _ (fun ε => by simp [Pi.neg_def])

lemma ssum_aw {n : ℕ} (ε : Fin n → ℤˣ) : ssum ε (aw n) = ssum ε (wt n) / σa n := by
  unfold ssum aw; rw [sum_div]; apply sum_congr rfl; intro i _; ring

lemma ssum_bw {n : ℕ} (ε : Fin n → ℤˣ) : ssum ε (bw n) = ssum ε (fun _ => (1 : ℝ)) / √(n : ℝ) := by
  unfold ssum bw; rw [sum_div]; apply sum_congr rfl; intro i _; ring

lemma wedge_iff {n : ℕ} (hn : 2 ≤ n) (ε : Fin n → ℤˣ) :
    (0 ≤ ssum ε (wt n) ∧ ssum ε (wt n) + ssum ε (fun _ => (1 : ℝ)) < 0) ↔
    (0 ≤ ssum ε (aw n) ∧ ssum ε (aw n) < -(√(n : ℝ) / σa n) * ssum ε (bw n)) := by
  have hσ := σa_pos hn
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr (by positivity)
  rw [ssum_aw, ssum_bw]
  have e : -(√(n : ℝ) / σa n) * (ssum ε (fun _ => (1 : ℝ)) / √(n : ℝ)) =
      -ssum ε (fun _ => (1 : ℝ)) / σa n := by field_simp
  rw [e, div_lt_div_iff_of_pos_right hσ]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨div_nonneg h1 hσ.le, by linarith⟩
  · rintro ⟨h1, h2⟩
    have := mul_nonneg h1 hσ.le
    rw [div_mul_cancel₀ _ hσ.ne'] at this
    exact ⟨this, by linarith⟩

lemma GMlim_cont : Tendsto (fun h : ℝ => GMlim h h) (𝓝 0) (𝓝 (√3 / (4 * π))) := by
  have hc : Continuous (fun h : ℝ => GMlim h h) := by unfold GMlim; fun_prop
  have := hc.tendsto 0
  have e : GMlim 0 0 = √3 / (4 * π) := by
    unfold GMlim
    have h2 : √(2 * π) * √(2 * π) = 2 * π := Real.mul_self_sqrt (by positivity)
    have h3 : √(2 * π) ≠ 0 := by positivity
    field_simp
    nlinarith [h2]
  rwa [e] at this

/-- **The sign-change bound.** -/
theorem pk_bound {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ n : ℕ in atTop, PP (SCev n) ≤ (√3 / (2 * π) + θ) / n := by
  -- choose the smoothing parameters
  obtain ⟨h, hh0, hh1, hGM⟩ : ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧ GMlim h h < √3 / (4 * π) + θ / 4 := by
    have := (GMlim_cont.eventually (gt_mem_nhds (show √3 / (4 * π) < √3 / (4 * π) + θ / 4 by linarith)))
    have h2 := this.and (Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h2
    refine ⟨min (ε / 2) (1 / 2), by positivity, by
      have := min_le_right (ε / 2) (1 / 2); linarith, ?_⟩
    have := hball (y := min (ε / 2) (1 / 2)) (by
      rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
      have := min_le_left (ε / 2) (1 / 2); linarith)
    exact this.1
  have hδ : (0 : ℝ) < h := hh0
  have hGMt := tendsto_GM h h
  have hB := tendsto_Btot h h hδ hh0
  have ev1 := hGMt.eventually (gt_mem_nhds (show GMlim h h < GMlim h h + θ / 8 by linarith))
  have ev2 := hB.eventually (gt_mem_nhds (show (0 : ℝ) < θ / 8 by linarith))
  have ev3 := tendsto_en.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 16 by norm_num))
  filter_upwards [ev1, ev2, ev3, eventually_ge_atTop 40] with n h1 h2 h3 hn
  have hn2 : 2 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by positivity
  have hσ : 0 < 1 - ρw n ^ 2 := by have := ρw_sq_lt hn2; linarith
  have hw := wedge_bound hn (R := Rn n) hδ hh1 hh0 (by unfold Rn; positivity) (Nn n) (Nn_one n) h3.le hσ
  -- the wedge probability
  have hA : PP (fun ε : Fin n → ℤˣ => 0 ≤ ssum ε (wt n) ∧ ssum ε (wt n) + ssum ε (fun _ => (1 : ℝ)) < 0)
      ≤ (√3 / (4 * π) + θ / 2) / n := by
    have heq : PP (fun ε : Fin n → ℤˣ => 0 ≤ ssum ε (wt n) ∧ ssum ε (wt n) + ssum ε (fun _ => (1 : ℝ)) < 0)
        = PP (fun ε : Fin n → ℤˣ => 0 ≤ ssum ε (aw n) ∧ ssum ε (aw n) < -(√(n : ℝ) / σa n) * ssum ε (bw n)) := by
      congr 1; funext ε; exact propext (wedge_iff hn2 ε)
    rw [heq]
    have hb := err_le_Btot hn hδ hh0 (h := h) (δ := h)
    rw [le_div_iff₀ hn0]
    have : (n : ℝ) * PP (fun ε : Fin n → ℤˣ => 0 ≤ ssum ε (aw n) ∧
        ssum ε (aw n) < -(√(n : ℝ) / σa n) * ssum ε (bw n)) ≤
        (n : ℝ) * GM (en n) (sn n) h h + (n : ℝ) * (∑ j ∈ range (Nn n), Errj n (en n) h h (Rn n) j
          + 2 * Real.exp (-(((Nn n : ℝ) - 1) * h) ^ 2 / 2)) := by
      rw [← mul_add]
      apply mul_le_mul_of_nonneg_left _ hn0.le
      have := hw
      unfold en sn
      linarith
    linarith
  -- the second wedge by symmetry
  have hB' : PP (fun ε : Fin n → ℤˣ => ssum ε (wt n) ≤ 0 ∧ 0 < ssum ε (wt n) + ssum ε (fun _ => (1 : ℝ)))
      = PP (fun ε : Fin n → ℤˣ => 0 ≤ ssum ε (wt n) ∧ ssum ε (wt n) + ssum ε (fun _ => (1 : ℝ)) < 0) := by
    rw [← PP_flip]
    congr 1; funext ε
    simp only [ssum_neg]
    apply propext; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
  have hsplit := PP_or_le (fun ε : Fin n → ℤˣ => 0 ≤ ssum ε (wt n) ∧
      ssum ε (wt n) + ssum ε (fun _ => (1 : ℝ)) < 0)
    (fun ε : Fin n → ℤˣ => ssum ε (wt n) ≤ 0 ∧ 0 < ssum ε (wt n) + ssum ε (fun _ => (1 : ℝ)))
  have : PP (SCev n) = PP (fun ε : Fin n → ℤˣ => (0 ≤ ssum ε (wt n) ∧
      ssum ε (wt n) + ssum ε (fun _ => (1 : ℝ)) < 0) ∨
      (ssum ε (wt n) ≤ 0 ∧ 0 < ssum ε (wt n) + ssum ε (fun _ => (1 : ℝ)))) := rfl
  rw [this]
  have e2 : (√3 / (2 * π) + θ) / n = 2 * ((√3 / (4 * π) + θ / 2) / n) := by
    field_simp; ring
  rw [e2]
  linarith

end R522
end

end S_C17

-- ===== D1 =====
section S_D1

/-! Sign variations of truncated coefficient sequences (original). -/

open Polynomial Finset

namespace E521D

/-- truncation `∑_{i<N} c_i X^i`. -/
noncomputable def T (c : ℕ → ℝ) (N : ℕ) : ℝ[X] := ∑ i ∈ range N, C (c i) * X ^ i

/-- the weak sign-change indicator. -/
def Ip (x y : ℝ) : Prop := (0 ≤ x ∧ y < 0) ∨ (x ≤ 0 ∧ 0 < y)

noncomputable instance (x y : ℝ) : Decidable (Ip x y) := by unfold Ip; infer_instance

lemma T_succ (c : ℕ → ℝ) (N : ℕ) : T c (N + 1) = T c N + C (c N) * X ^ N := by
  unfold T; rw [sum_range_succ]

lemma T_coeff (c : ℕ → ℝ) (N i : ℕ) : (T c N).coeff i = if i < N then c i else 0 := by
  unfold T
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  split_ifs with h
  · rw [sum_eq_single i]
    · simp
    · intro b _ hb; rw [if_neg (Ne.symm hb)]
    · intro h'; exact absurd (mem_range.mpr h) h'
  · apply sum_eq_zero; intro b hb; rw [mem_range] at hb; rw [if_neg (by omega)]

lemma T_degree_lt (c : ℕ → ℝ) (N : ℕ) : (T c N).degree < N := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm; rw [T_coeff, if_neg (by omega)]

lemma T_succ_lead (c : ℕ → ℝ) {N : ℕ} (hc : c N ≠ 0) :
    (T c (N + 1)).leadingCoeff = c N ∧ (T c (N + 1)).eraseLead = T c N := by
  have hdeg : (T c (N + 1)).natDegree = N := by
    rw [T_succ]
    rw [natDegree_add_eq_right_of_degree_lt]
    · exact natDegree_C_mul_X_pow N (c N) hc
    · rw [degree_C_mul_X_pow N hc]; exact T_degree_lt c N
  constructor
  · rw [leadingCoeff, hdeg, T_coeff, if_pos (by omega)]
  · ext i
    rw [eraseLead_coeff, hdeg, T_coeff, T_coeff]
    by_cases hi : i = N
    · rw [if_pos hi, if_neg (by omega)]
    · rw [if_neg hi]
      by_cases hi2 : i < N
      · rw [if_pos (by omega), if_pos hi2]
      · rw [if_neg (by omega), if_neg hi2]

lemma T_succ_zero (c : ℕ → ℝ) {N : ℕ} (hc : c N = 0) : T c (N + 1) = T c N := by
  rw [T_succ, hc, C_0, zero_mul, add_zero]

/-- the leading coefficient of `T c N` is `c (N-1)` when that is nonzero. -/
lemma T_lead_of (c : ℕ → ℝ) {N : ℕ} (hc : c N ≠ 0) : (T c (N + 1)).leadingCoeff = c N :=
  (T_succ_lead c hc).1

/-- one step of the sign-variation count. -/
lemma sv_step (c : ℕ → ℝ) (N : ℕ) :
    signVariations (T c (N + 2)) ≤ signVariations (T c (N + 1)) +
      (if Ip (c N) (c (N + 1)) then 1 else 0) := by
  by_cases h1 : c (N + 1) = 0
  · rw [T_succ_zero c h1]; omega
  · have hne : T c (N + 2) ≠ 0 := by
      intro h0
      have := (T_succ_lead c h1).1
      rw [h0, leadingCoeff_zero] at this; exact h1 this.symm
    rw [signVariations_eq_eraseLead_add_ite hne, (T_succ_lead c h1).2, (T_succ_lead c h1).1]
    apply Nat.add_le_add_left
    split_ifs with hs hI hI
    · exact le_rfl
    · exfalso; apply hI
      by_cases h0 : c N = 0
      · unfold Ip; rw [h0]
        rcases lt_or_gt_of_ne h1 with h | h
        · left; exact ⟨le_rfl, h⟩
        · right; exact ⟨le_rfl, h⟩
      · rw [T_lead_of c h0] at hs
        unfold Ip
        rcases lt_or_gt_of_ne h1 with h | h
        · rw [sign_neg h] at hs
          have : SignType.sign (c N) = 1 := by
            have := congrArg Neg.neg hs; simpa using this.symm
          left; exact ⟨(sign_eq_one_iff.mp this).le, h⟩
        · rw [sign_pos h] at hs
          have : SignType.sign (c N) = -1 := by
            have := congrArg Neg.neg hs; simpa using this.symm
          right; exact ⟨(sign_eq_neg_one_iff.mp this).le, h⟩
    · omega
    · omega

/-- iterate: from `a+1` to `b+1`. -/
lemma sv_range (c : ℕ → ℝ) (a : ℕ) : ∀ b, a ≤ b →
    signVariations (T c (b + 1)) ≤ signVariations (T c (a + 1)) +
      ((Ico a b).filter (fun k => Ip (c k) (c (k + 1)))).card := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have := sv_step c b
    have hc : ((Ico a (b + 1)).filter (fun k => Ip (c k) (c (k + 1)))).card =
        ((Ico a b).filter (fun k => Ip (c k) (c (k + 1)))).card + (if Ip (c b) (c (b + 1)) then 1 else 0) := by
      rw [Nat.Ico_succ_right_eq_insert_Ico hab, filter_insert]
      split_ifs with h
      · rw [card_insert_of_notMem (by simp)]
      · rfl
    rw [hc]; show signVariations (T c (b + 2)) ≤ _; omega

lemma sv_one (c : ℕ → ℝ) : signVariations (T c 1) = 0 := by
  unfold T; simp only [range_one, sum_singleton, pow_zero, mul_one]
  rw [← monomial_zero_left]; exact signVariations_monomial 0 _

/-- nonnegative continuation with a positive leading coefficient does not add variations. -/
lemma sv_nonneg (c : ℕ → ℝ) (a : ℕ) (ha : 0 < (T c (a + 1)).leadingCoeff) :
    ∀ b, a ≤ b → (∀ k, a < k → k ≤ b → 0 ≤ c k) →
      signVariations (T c (b + 1)) = signVariations (T c (a + 1)) ∧ 0 < (T c (b + 1)).leadingCoeff := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => intro _; exact ⟨rfl, ha⟩
  | succ b hab ih =>
    intro hpos
    obtain ⟨h1, h2⟩ := ih (fun k hk1 hk2 => hpos k hk1 (by omega))
    by_cases hz : c (b + 1) = 0
    · rw [T_succ_zero c hz]; exact ⟨h1, h2⟩
    · have hp : 0 < c (b + 1) := lt_of_le_of_ne (hpos (b + 1) (by omega) le_rfl) (Ne.symm hz)
      have hne : T c (b + 2) ≠ 0 := by
        intro h0
        have := (T_succ_lead c hz).1
        rw [h0, leadingCoeff_zero] at this; exact hz this.symm
      rw [signVariations_eq_eraseLead_add_ite hne, (T_succ_lead c hz).2, (T_succ_lead c hz).1]
      rw [if_neg]
      · exact ⟨by rw [h1]; rfl, hp⟩
      · rw [sign_pos hp, sign_pos h2]; decide

/-- an increasing stretch contributes at most one weak sign change. -/
lemma Ip_incr (c : ℕ → ℝ) (a b : ℕ) (hinc : ∀ k, a ≤ k → k < b → c k < c (k + 1)) :
    ((Ico a b).filter (fun k => Ip (c k) (c (k + 1)))).card ≤ 1 := by
  rw [card_le_one]
  intro x hx y hy
  rw [mem_filter, mem_Ico] at hx hy
  -- in an increasing stretch, Ip means `c k ≤ 0 < c (k+1)`, which happens at most once
  have mono : ∀ i j, a ≤ i → i ≤ j → j ≤ b → c i ≤ c j := by
    intro i j hi hij hj
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih => exact (ih (by omega)).trans (hinc j (by omega) (by omega)).le
  have hx' : c x ≤ 0 ∧ 0 < c (x + 1) := by
    rcases hx.2 with ⟨h1, h2⟩ | h
    · exact absurd (hinc x hx.1.1 hx.1.2) (by linarith)
    · exact h
  have hy' : c y ≤ 0 ∧ 0 < c (y + 1) := by
    rcases hy.2 with ⟨h1, h2⟩ | h
    · exact absurd (hinc y hy.1.1 hy.1.2) (by linarith)
    · exact h
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := mono (x + 1) y (by omega) (by omega) (by omega); linarith [hx'.2, hy'.1]
  · have := mono (y + 1) x (by omega) (by omega) (by omega); linarith [hy'.2, hx'.1]

end E521D

end S_D1

-- ===== D2 =====
section S_D2

/-! Coefficients of `f · D_N²` (original). -/

open Polynomial Finset

namespace E521D

/-- `D_N = 1 + X + ... + X^N`. -/
noncomputable def DN (N : ℕ) : ℝ[X] := ∑ a ∈ range (N + 1), X ^ a

/-- the tent `W t = #{(a, b) ∈ [0,N]² : a + b = t}`. -/
def W (N : ℕ) (t : ℤ) : ℕ := ((range (N + 1)).filter (fun a : ℕ => 0 ≤ t - a ∧ t - a ≤ N)).card

lemma DN_sq_coeff (N t : ℕ) : (DN N * DN N).coeff t = W N t := by
  unfold DN W
  rw [sum_mul_sum]
  rw [finsetSum_coeff]
  simp_rw [finsetSum_coeff, ← pow_add, coeff_X_pow]
  rw [card_filter, Nat.cast_sum]
  apply sum_congr rfl
  intro a ha
  rw [mem_range] at ha
  by_cases h : 0 ≤ (t : ℤ) - a ∧ (t : ℤ) - a ≤ N
  · rw [if_pos h]
    rw [sum_eq_single (t - a)]
    · rw [if_pos (by omega)]; simp
    · intro b _ hb; rw [if_neg (by omega)]
    · intro hb; rw [mem_range] at hb; omega
  · rw [if_neg h, Nat.cast_zero]
    apply sum_eq_zero; intro b hb; rw [mem_range] at hb; rw [if_neg (by omega)]

lemma W_low (N : ℕ) {t : ℤ} (h0 : 0 ≤ t) (h1 : t ≤ N) : (W N t : ℤ) = t + 1 := by
  unfold W
  have : (range (N + 1)).filter (fun a : ℕ => 0 ≤ t - a ∧ t - a ≤ N) = range (t.toNat + 1) := by
    ext a; simp only [mem_filter, mem_range]; omega
  rw [this, card_range]; push_cast; omega

lemma W_high (N : ℕ) {t : ℤ} (h0 : (N : ℤ) ≤ t) (h1 : t ≤ 2 * N) : (W N t : ℤ) = 2 * N + 1 - t := by
  unfold W
  have : (range (N + 1)).filter (fun a : ℕ => 0 ≤ t - a ∧ t - a ≤ N) = Ico (t - N).toNat (N + 1) := by
    ext a; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [this, Nat.card_Ico]; omega

lemma W_neg (N : ℕ) {t : ℤ} (h : t < 0) : W N t = 0 := by
  unfold W; rw [card_eq_zero, filter_eq_empty_iff]; intro a _; omega

/-- coefficients of `f · D²` for `f = ∑_{j ≤ n} e_j X^j`. -/
lemma Q_coeff (e : ℕ → ℝ) (n N k : ℕ) :
    ((T e (n + 1)) * (DN N * DN N)).coeff k = ∑ j ∈ range (n + 1), e j * (W N ((k : ℤ) - j) : ℝ) := by
  rw [coeff_mul]
  unfold T
  have : ∀ x ∈ antidiagonal k, (∑ i ∈ range (n + 1), C (e i) * X ^ i).coeff x.1 * (DN N * DN N).coeff x.2 =
      ∑ i ∈ range (n + 1), (if i = x.1 then e i else 0) * (W N ((k : ℤ) - i) : ℝ) := by
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [finsetSum_coeff, sum_mul, DN_sq_coeff]
    apply sum_congr rfl; intro i _
    rw [coeff_C_mul_X_pow]
    by_cases h : x.1 = i
    · rw [if_pos h, if_pos h.symm]
      congr 3; omega
    · rw [if_neg h, if_neg (Ne.symm h)]; simp
  rw [sum_congr rfl this, sum_comm]
  apply sum_congr rfl; intro i hi
  rw [← sum_mul]
  by_cases hik : i ≤ k
  · rw [sum_eq_single (i, k - i)]
    · simp
    · intro x hx hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      rw [if_neg]
      intro h; apply hne; ext <;> dsimp only <;> omega
    · intro h; exfalso; apply h; rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega
  · rw [sum_eq_zero, W_neg N (by omega)]
    · simp
    · intro x hx; rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx; rw [if_neg (by omega)]

end E521D

end S_D2

-- ===== D3 =====
section S_D3

/-! Positive roots of `f = ∑_{j≤n} e_j X^j` are at most the weak sign changes of the forward
two-fold sums before `n - t`, plus one, under the tail and backward-positivity conditions
(original). -/

open Polynomial Finset

namespace E521D

/-- forward two-fold sums `c_k = ∑_{j≤k} e_j (k - j + 1)`. -/
def c2 (e : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ range (k + 1), e j * ((k : ℝ) - j + 1)

/-- forward partial sums. -/
def S1 (e : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ range (k + 1), e j

/-- backward two-fold sums of `a_i = e_{n-i}`. -/
def b2 (e : ℕ → ℝ) (n k : ℕ) : ℝ := ∑ i ∈ range (k + 1), e (n - i) * ((k : ℝ) - i + 1)

lemma Qc_low (e : ℕ → ℝ) {n N k : ℕ} (hk : k ≤ n) (hN : n ≤ N) :
    ((T e (n + 1)) * (DN N * DN N)).coeff k = c2 e k := by
  rw [Q_coeff]
  unfold c2
  rw [show n + 1 = (k + 1) + (n - k) by omega, sum_range_add]
  have h0 : ∑ j ∈ range (n - k), e (k + 1 + j) * (W N ((k : ℤ) - (k + 1 + j : ℕ)) : ℝ) = 0 := by
    apply sum_eq_zero; intro j _; rw [W_neg N (t := (k : ℤ) - ((k + 1 + j : ℕ) : ℤ)) (by push_cast; omega)]; simp
  rw [h0, add_zero]
  apply sum_congr rfl; intro j hj; rw [mem_range] at hj
  congr 1
  have := W_low N (t := (k : ℤ) - j) (by omega) (by omega)
  have h2 : ((W N ((k : ℤ) - j) : ℕ) : ℝ) = (((W N ((k : ℤ) - j) : ℕ) : ℤ) : ℝ) := by norm_cast
  rw [h2, this]; push_cast; ring

lemma Qc_mid_lin (e : ℕ → ℝ) {n N k : ℕ} (hk1 : n ≤ k) (hk2 : k ≤ N) :
    ((T e (n + 1)) * (DN N * DN N)).coeff k = ∑ j ∈ range (n + 1), e j * ((k : ℝ) - j + 1) := by
  rw [Q_coeff]
  apply sum_congr rfl; intro j hj; rw [mem_range] at hj
  congr 1
  have := W_low N (t := (k : ℤ) - j) (by omega) (by omega)
  have h2 : ((W N ((k : ℤ) - j) : ℕ) : ℝ) = (((W N ((k : ℤ) - j) : ℕ) : ℤ) : ℝ) := by norm_cast
  rw [h2, this]; push_cast; ring

lemma abs_e_le (e : ℕ → ℝ) (he : ∀ j, e j = 1 ∨ e j = -1) (j : ℕ) : |e j| = 1 := by
  rcases he j with h | h <;> rw [h] <;> simp

/-- the middle coefficients are positive. -/
lemma Qc_mid_pos (e : ℕ → ℝ) (he : ∀ j, e j = 1 ∨ e j = -1) {n N k : ℕ} (hN : n * n + n + 1 ≤ N)
    (hS : 1 ≤ S1 e n) (hk1 : N ≤ k) (hk2 : k ≤ N + n) :
    0 < ((T e (n + 1)) * (DN N * DN N)).coeff k := by
  rw [Q_coeff]
  -- c_k = (N+1) S_n - ∑ e_j (N + 1 - W(k-j)), with 0 ≤ N + 1 - W ≤ n
  have hW : ∀ j ∈ range (n + 1), |(N : ℝ) + 1 - (W N ((k : ℤ) - j) : ℝ)| ≤ n := by
    intro j hj; rw [mem_range] at hj
    have h2 : ((W N ((k : ℤ) - j) : ℕ) : ℝ) = (((W N ((k : ℤ) - j) : ℕ) : ℤ) : ℝ) := by norm_cast
    rw [h2]
    rcases le_or_gt ((k : ℤ) - j) N with h | h
    · rw [W_low N (by omega) h]; push_cast
      have hjn : (j : ℝ) ≤ n := by exact_mod_cast (by omega : j ≤ n)
      have hNk : (N : ℝ) ≤ k := by exact_mod_cast hk1
      have hkN : (k : ℝ) ≤ N + n := by exact_mod_cast hk2
      have hj0 : (0 : ℝ) ≤ j := by positivity
      rw [abs_le]; constructor <;> linarith
    · rw [W_high N h.le (by omega)]; push_cast
      have hk2' : (k : ℝ) ≤ N + n := by exact_mod_cast hk2
      have hj' : (0 : ℝ) ≤ j := by positivity
      have hlt : ((N : ℤ) : ℝ) < (k : ℝ) - j := by exact_mod_cast h
      rw [abs_le]; constructor <;> push_cast at hlt <;> linarith
  have e1 : ∑ j ∈ range (n + 1), e j * (W N ((k : ℤ) - j) : ℝ) =
      ((N : ℝ) + 1) * S1 e n - ∑ j ∈ range (n + 1), e j * ((N : ℝ) + 1 - (W N ((k : ℤ) - j) : ℝ)) := by
    unfold S1; rw [mul_sum, ← sum_sub_distrib]; apply sum_congr rfl; intro j _; ring
  rw [e1]
  have hb : ∑ j ∈ range (n + 1), e j * ((N : ℝ) + 1 - (W N ((k : ℤ) - j) : ℝ)) ≤ (n + 1) * n := by
    calc ∑ j ∈ range (n + 1), e j * ((N : ℝ) + 1 - (W N ((k : ℤ) - j) : ℝ))
        ≤ ∑ j ∈ range (n + 1), (n : ℝ) := by
          apply sum_le_sum; intro j hj
          calc e j * ((N : ℝ) + 1 - (W N ((k : ℤ) - j) : ℝ))
              ≤ |e j * ((N : ℝ) + 1 - (W N ((k : ℤ) - j) : ℝ))| := le_abs_self _
            _ = |(N : ℝ) + 1 - (W N ((k : ℤ) - j) : ℝ)| := by rw [abs_mul, abs_e_le e he, one_mul]
            _ ≤ n := hW j hj
      _ = (n + 1) * n := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  have hNr : (n : ℝ) * n + n + 1 ≤ N := by exact_mod_cast hN
  nlinarith

/-- the top coefficients are the backward two-fold sums (or their linear continuation). -/
lemma Qc_top (e : ℕ → ℝ) {n N k : ℕ} (hk1 : N + n ≤ k) (hk2 : k ≤ 2 * N + n) (hN : n ≤ N) :
    ((T e (n + 1)) * (DN N * DN N)).coeff k =
      ∑ i ∈ range (n + 1), (if i ≤ 2 * N + n - k then e (n - i) * ((2 * N + n - k : ℕ) - (i : ℝ) + 1) else 0) := by
  rw [Q_coeff]
  rw [← sum_range_reflect]
  simp only [Nat.add_sub_cancel]
  apply sum_congr rfl; intro i hi; rw [mem_range] at hi
  have hj : n - i ≤ n := by omega
  by_cases hik : i ≤ 2 * N + n - k
  · rw [if_pos hik]
    congr 1
    have := W_high N (t := (k : ℤ) - (n - i : ℕ)) (by push_cast; omega) (by push_cast; omega)
    have h2 : ((W N ((k : ℤ) - (n - i : ℕ)) : ℕ) : ℝ) = (((W N ((k : ℤ) - (n - i : ℕ)) : ℕ) : ℤ) : ℝ) := by
      norm_cast
    rw [h2, this]
    push_cast
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  · rw [if_neg hik]
    have : W N ((k : ℤ) - (n - i : ℕ)) = 0 := by
      unfold W; rw [card_eq_zero, filter_eq_empty_iff]; intro a ha; rw [mem_range] at ha; omega
    rw [this]; simp

end E521D

end S_D3

-- ===== P3 =====
section S_P3

/-! Forward cylinder events and the bridge to sign-vector averages (original). -/

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace E521

lemma rs_preimage_singleton (s : Finset ℕ) (r : s → Bool) :
    rs s ⁻¹' {r} = Set.pi (↑s) (fun i => {if h : i ∈ s then r ⟨i, h⟩ else false}) := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, mem_coe]
  constructor
  · intro h i hi; subst h; simp [rs, hi]
  · intro h; funext i; have := h i i.2; simp only [dif_pos i.2] at this; exact this

lemma μS_rs_singleton (s : Finset ℕ) (r : s → Bool) : μS (rs s ⁻¹' {r}) = (2⁻¹ : ℝ≥0∞) ^ s.card := by
  rw [rs_preimage_singleton, μS]
  have h := Measure.infinitePi_pi (μ := fun _ : ℕ => ν) (s := s)
    (t := fun i => ({if h : i ∈ s then r ⟨i, h⟩ else false} : Set Bool)) (fun i _ => measurableSet_singleton _)
  refine h.trans ?_
  simp only [ν_singleton, prod_const]

lemma μS_rs_real (s : Finset ℕ) (Q : Finset (s → Bool)) :
    μS.real (rs s ⁻¹' (Q : Set (s → Bool))) = Q.card / 2 ^ s.card := by
  have : rs s ⁻¹' (Q : Set (s → Bool)) = ⋃ r ∈ Q, rs s ⁻¹' {r} := by ext ω; simp
  rw [Measure.real, this, measure_biUnion_finset]
  · simp only [μS_rs_singleton, sum_const, nsmul_eq_mul]
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]
    simp [div_eq_mul_inv]
  · intro p _ q _ hpq
    simp only [Function.onFun]
    rw [Set.disjoint_iff]
    intro ω ⟨h1, h2⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
    exact hpq (h1.symm.trans h2)
  · intro r _; exact measurable_rs s (measurableSet_singleton r)

/-- real signs of `ω`. -/
def eR (ω : ℕ → Bool) (j : ℕ) : ℝ := if ω j then 1 else -1

lemma eR_pm (ω : ℕ → Bool) (j : ℕ) : eR ω j = 1 ∨ eR ω j = -1 := by
  unfold eR; split_ifs <;> simp

/-- the weak sign-change event of the forward two-fold sums at `k`. -/
def Iev (k : ℕ) : Set (ℕ → Bool) :=
  {ω | E521D.Ip (E521D.c2 (eR ω) k) (E521D.c2 (eR ω) (k + 1))}

end E521

namespace E521

/-- Bool patterns on `range n` vs sign vectors on `Fin n`. -/
def toSigns (n : ℕ) (r : range n → Bool) : Fin n → ℤˣ :=
  fun j => if r ⟨j, mem_range.mpr j.2⟩ then 1 else -1

def ofSigns (n : ℕ) (ε : Fin n → ℤˣ) : range n → Bool :=
  fun i => decide (ε ⟨i, mem_range.mp i.2⟩ = 1)

lemma units_eq (u : ℤˣ) : u = 1 ∨ u = -1 := Int.units_eq_one_or u

def signEquiv (n : ℕ) : (range n → Bool) ≃ (Fin n → ℤˣ) where
  toFun := toSigns n
  invFun := ofSigns n
  left_inv r := by
    funext i
    simp only [ofSigns, toSigns]
    by_cases h : r ⟨(i : ℕ), mem_range.mpr (mem_range.mp i.2)⟩ <;> simp_all
  right_inv ε := by
    funext j
    simp only [ofSigns, toSigns]
    rcases units_eq (ε j) with h | h <;> simp [h]

lemma toSigns_val (n : ℕ) (r : range n → Bool) (j : Fin n) :
    (((toSigns n r j : ℤˣ) : ℤ) : ℝ) = if r ⟨j, mem_range.mpr j.2⟩ then 1 else -1 := by
  unfold toSigns; split_ifs <;> simp

/-- the forward signs of a pattern. -/
def extR (n : ℕ) (r : range n → Bool) (j : ℕ) : ℝ :=
  if h : j < n then (if r ⟨j, mem_range.mpr h⟩ then 1 else -1) else 0

lemma extR_rs (n : ℕ) (ω : ℕ → Bool) {j : ℕ} (hj : j < n) : extR n (rs (range n) ω) j = eR ω j := by
  (unfold extR rs eR; rw [dif_pos hj]) <;> (split_ifs <;> simp_all)

lemma c2_ext (k : ℕ) (ω : ℕ → Bool) (i : ℕ) (hi : i ≤ k + 1) :
    E521D.c2 (eR ω) i = E521D.c2 (extR (k + 2) (rs (range (k + 2)) ω)) i := by
  unfold E521D.c2
  apply sum_congr rfl; intro j hj; rw [mem_range] at hj
  rw [extR_rs _ _ (by omega)]

lemma Iev_cyl (k : ℕ) :
    Iev k = rs (range (k + 2)) ⁻¹' {r | E521D.Ip (E521D.c2 (extR (k + 2) r) k)
      (E521D.c2 (extR (k + 2) r) (k + 1))} := by
  ext ω
  simp only [Iev, Set.mem_setOf_eq, Set.mem_preimage]
  rw [c2_ext k ω k (by omega), c2_ext k ω (k + 1) le_rfl]

lemma card_bridge (n : ℕ) (P : (range n → Bool) → Prop) [DecidablePred P] :
    (univ.filter P).card = (univ.filter (fun ε : Fin n → ℤˣ => P (ofSigns n ε))).card := by
  apply card_bij (fun r _ => toSigns n r)
  · intro r hr; simp only [mem_filter, mem_univ, true_and] at hr ⊢
    have : ofSigns n (toSigns n r) = r := (signEquiv n).left_inv r
    rw [this]; exact hr
  · intro r1 _ r2 _ h; exact (signEquiv n).injective h
  · intro ε hε; refine ⟨ofSigns n ε, ?_, (signEquiv n).right_inv ε⟩
    simp only [mem_filter, mem_univ, true_and] at hε ⊢; exact hε

/-- **range bridge**: a cylinder event on the first `n` coordinates has the sign-vector probability. -/
theorem μS_range_bridge (n : ℕ) (P : (range n → Bool) → Prop) [DecidablePred P] :
    μS.real (rs (range n) ⁻¹' {r | P r}) = R522.PP (fun ε : Fin n → ℤˣ => P (ofSigns n ε)) := by
  classical
  have h := μS_rs_real (range n) (univ.filter P)
  have e : ((univ.filter P : Finset (range n → Bool)) : Set (range n → Bool)) = {r | P r} := by
    ext r; simp
  rw [e] at h
  rw [h, R522.PP_eq]
  unfold R522.EE
  rw [card_range, Fintype.card_fin, card_bridge n P]
  congr 1
  rw [card_filter]; push_cast
  apply sum_congr rfl; intro ε _; split_ifs <;> simp

lemma extR_ofSigns (n : ℕ) (ε : Fin n → ℤˣ) (j : ℕ) (hj : j < n) :
    extR n (ofSigns n ε) j = ((ε ⟨j, hj⟩ : ℤ) : ℝ) := by
  unfold extR ofSigns
  rw [dif_pos hj]
  rcases units_eq (ε ⟨j, hj⟩) with h | h <;> simp [h]

end E521

end S_P3

-- ===== P4 =====
section S_P4

/-! The probability of a weak sign change at `k` is the sign-vector quantity `p_k` (original). -/

open Finset MeasureTheory

namespace E521

lemma c2_signs (k : ℕ) (ε : Fin (k + 2) → ℤˣ) :
    E521D.c2 (extR (k + 2) (ofSigns (k + 2) ε)) k = R522.ssum ε (R522.wt (k + 2)) ∧
    E521D.c2 (extR (k + 2) (ofSigns (k + 2) ε)) (k + 1) =
      R522.ssum ε (R522.wt (k + 2)) + R522.ssum ε (fun _ => (1 : ℝ)) := by
  set e := extR (k + 2) (ofSigns (k + 2) ε)
  have he : ∀ j (hj : j < k + 2), e j = ((ε ⟨j, hj⟩ : ℤ) : ℝ) := fun j hj => extR_ofSigns _ ε j hj
  have hw : R522.ssum ε (R522.wt (k + 2)) = ∑ j ∈ range (k + 2), e j * ((k : ℝ) + 1 - j) := by
    unfold R522.ssum R522.wt
    rw [Fin.sum_univ_eq_sum_range (fun j => e j * ((k : ℝ) + 1 - j)) (k + 2) |>.symm]
    apply Fintype.sum_congr; intro j; rw [he j j.2]; push_cast; ring
  have h1 : R522.ssum ε (fun _ => (1 : ℝ)) = ∑ j ∈ range (k + 2), e j := by
    unfold R522.ssum
    rw [Fin.sum_univ_eq_sum_range (fun j => e j) (k + 2) |>.symm]
    apply Fintype.sum_congr; intro j; rw [he j j.2]; ring
  constructor
  · rw [hw]; unfold E521D.c2
    rw [show k + 2 = (k + 1) + 1 by ring, sum_range_succ (fun j => e j * ((k : ℝ) + 1 - j)) (k + 1)]
    have : ((k : ℝ) + 1 - ((k + 1 : ℕ) : ℝ)) = 0 := by push_cast; ring
    rw [this, mul_zero, add_zero]
    apply sum_congr rfl; intro j _; ring
  · rw [hw, h1, ← sum_add_distrib]; unfold E521D.c2
    apply sum_congr rfl; intro j _; push_cast; ring

/-- **`μ(I_k) = p_k`.** -/
theorem Iev_real (k : ℕ) : μS.real (Iev k) = R522.PP (R522.SCev (k + 2)) := by
  classical
  rw [Iev_cyl, μS_range_bridge]
  congr 1; funext ε
  obtain ⟨h1, h2⟩ := c2_signs k ε
  apply propext
  simp only [E521D.Ip, R522.SCev]
  rw [h1, h2]

end E521

end S_P4

-- ===== P5 =====
section S_P5

/-! Hoeffding for blocks of coordinates under `μS`; the tail event (original). -/

open Finset MeasureTheory

namespace E521

/-- `μ (|∑_{j<l} ε_j| ≥ x) ≤ 2 exp (-x²/(2l))`. -/
lemma block_hoeffding (l : ℕ) (hl : 1 ≤ l) {x : ℝ} (hx : 0 < x) :
    μS.real {ω | x ≤ |∑ j ∈ range l, eR ω j|} ≤ 2 * Real.exp (-(x ^ 2 / (2 * l))) := by
  classical
  have hcyl : {ω | x ≤ |∑ j ∈ range l, eR ω j|} =
      rs (range l) ⁻¹' {r | x ≤ |∑ j ∈ range l, extR l r j|} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage]
    congr! 2
    apply sum_congr rfl; intro j hj; rw [mem_range] at hj; rw [extR_rs _ _ hj]
  rw [hcyl, μS_range_bridge]
  have e : ∀ ε : Fin l → ℤˣ, ∑ j ∈ range l, extR l (ofSigns l ε) j = R522.ssum ε (fun _ => (1 : ℝ)) := by
    intro ε
    unfold R522.ssum
    rw [Fin.sum_univ_eq_sum_range (fun j => extR l (ofSigns l ε) j) l |>.symm]
    apply Fintype.sum_congr; intro j; rw [extR_ofSigns _ ε j j.2]; ring
  simp_rw [e]
  have h := R522.hoeffding (ι := Fin l) (fun _ => (1 : ℝ)) hx
  simp only [one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  exact h

end E521

namespace E521

/-- Hoeffding for a block with unit-modulus weights. -/
lemma block_hoeffding_w (l : ℕ) (w : ℕ → ℝ) (hw : ∀ j, w j ^ 2 = 1) {x : ℝ} (hx : 0 < x) :
    μS.real {ω | x ≤ |∑ j ∈ range l, w j * eR ω j|} ≤ 2 * Real.exp (-(x ^ 2 / (2 * l))) := by
  classical
  have hcyl : {ω | x ≤ |∑ j ∈ range l, w j * eR ω j|} =
      rs (range l) ⁻¹' {r | x ≤ |∑ j ∈ range l, w j * extR l r j|} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage]
    congr! 2
    apply sum_congr rfl; intro j hj; rw [mem_range] at hj; rw [extR_rs _ _ hj]
  rw [hcyl, μS_range_bridge]
  have e : ∀ ε : Fin l → ℤˣ, ∑ j ∈ range l, w j * extR l (ofSigns l ε) j = R522.ssum ε (fun j => w j) := by
    intro ε
    unfold R522.ssum
    rw [Fin.sum_univ_eq_sum_range (fun j => w j * extR l (ofSigns l ε) j) l |>.symm]
    apply Fintype.sum_congr; intro j; rw [extR_ofSigns _ ε j j.2]; ring
  simp_rw [e]
  have h := R522.hoeffding (ι := Fin l) (fun j => w j) hx
  have hs : ∑ i : Fin l, w i ^ 2 = l := by simp [hw]
  rw [hs] at h
  exact h

/-- the backward block sum, shifted to the front. -/
lemma back_shift (n l : ℕ) (hl : l ≤ n + 1) (w : ℕ → ℝ) (ω : ℕ → Bool) :
    ∑ i ∈ range l, w i * eR ω (n - i) =
      ∑ j ∈ range l, w (l - 1 - j) * eR (fun i => ω (i + (n + 1 - l))) j := by
  rw [← sum_range_reflect]
  apply sum_congr rfl; intro j hj; rw [mem_range] at hj
  have e1 : n - (l - 1 - j) = j + (n + 1 - l) := by omega
  have e2 : l - 1 - (l - 1 - j) = j := by omega
  simp only [eR, e1, e2]

end E521

end S_P5

-- ===== P6 =====
section S_P6

/-! Pair bound for cones and the independence of a forward event from the top block (original). -/

open Finset MeasureTheory

namespace E521

lemma coneE_cyl (K : ℕ) (F G : ℤ → Prop) :
    ∃ Q : Set (range (2 * K) → Bool), coneE K F G = rs (range (2 * K)) ⁻¹' Q := by
  refine ⟨{r | good2F F G K 0 0 (fun j : Fin K =>
    (r ⟨2 * K - 1 - 2 * j, by have := j.isLt; simp [mem_range]; omega⟩,
     r ⟨2 * K - 2 - 2 * j, by have := j.isLt; simp [mem_range]; omega⟩))}, ?_⟩
  ext ω; exact Iff.rfl

lemma disjoint_range_Ico (a b c : ℕ) (h : a ≤ b) : Disjoint (range a) (Ico b c) := by
  rw [Finset.disjoint_left]; intro x hx hx'; rw [mem_range] at hx; rw [mem_Ico] at hx'; omega

/-- `μ(cone_K ∩ cone_K') ≤ μ(cone_K) u_{K'-K}`. -/
theorem cone_pair (K K' : ℕ) (hKK : K ≤ K') (F G F' G' : ℤ → Prop) :
    μS.real (coneE K F G ∩ coneE K' F' G') ≤ μS.real (coneE K F G) * ((N2 (K' - K) 0 0 : ℝ) / 4 ^ (K' - K)) := by
  have hsub : coneE K F G ∩ coneE K' F' G' ⊆ coneE K F G ∩ topE K' (K' - K) :=
    Set.inter_subset_inter_right _ (cone_sub_top K' (K' - K) (by omega) F' G')
  obtain ⟨Q1, hQ1⟩ := coneE_cyl K F G
  obtain ⟨Q2, hQ2⟩ := topE_cyl K' (K' - K) (by omega)
  have hdis : Disjoint (range (2 * K)) (Ico (2 * K' - 2 * (K' - K)) (2 * K')) :=
    disjoint_range_Ico _ _ _ (by omega)
  have hind := indep_blocks hdis Q1 Q2
  rw [← hQ1, ← hQ2] at hind
  calc μS.real (coneE K F G ∩ coneE K' F' G') ≤ μS.real (coneE K F G ∩ topE K' (K' - K)) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ = μS.real (coneE K F G) * μS.real (topE K' (K' - K)) := by
        rw [Measure.real, hind, ENNReal.toReal_mul]; rfl
    _ = _ := by rw [topE_real K' (K' - K) (by omega)]

/-- `μ(cone_K ∩ I_k) ≤ u_L p_k` when the forward block `[0, k+2)` lies below the top block. -/
theorem cone_Iev (K L k : ℕ) (hL : L ≤ K) (hk : k + 2 ≤ 2 * K - 2 * L) (F G : ℤ → Prop) :
    μS.real (coneE K F G ∩ Iev k) ≤ ((N2 L 0 0 : ℝ) / 4 ^ L) * R522.PP (R522.SCev (k + 2)) := by
  have hsub : coneE K F G ∩ Iev k ⊆ topE K L ∩ Iev k :=
    Set.inter_subset_inter_left _ (cone_sub_top K L hL F G)
  obtain ⟨Q2, hQ2⟩ := topE_cyl K L hL
  have hcyl := Iev_cyl k
  have hdis : Disjoint (range (k + 2)) (Ico (2 * K - 2 * L) (2 * K)) :=
    disjoint_range_Ico _ _ _ hk
  have hind := indep_blocks hdis {r | E521D.Ip (E521D.c2 (extR (k + 2) r) k) (E521D.c2 (extR (k + 2) r) (k + 1))} Q2
  rw [← hcyl, ← hQ2] at hind
  calc μS.real (coneE K F G ∩ Iev k) ≤ μS.real (topE K L ∩ Iev k) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ = μS.real (Iev k ∩ topE K L) := by rw [Set.inter_comm]
    _ = μS.real (Iev k) * μS.real (topE K L) := by
        rw [Measure.real, hind, ENNReal.toReal_mul]; rfl
    _ = _ := by rw [topE_real K L hL, Iev_real]; ring

end E521

end S_P6

-- ===== P7 =====
section S_P7

/-! The alternating (negative-root) sign-change event has the same probability (original). -/

open Finset MeasureTheory

namespace E521

/-- coefficients of `-f(-x)`: `ẽ_j = -(-1)^j e_j`. -/
def eAlt (e : ℕ → ℝ) (j : ℕ) : ℝ := -((-1) ^ j * e j)

def Ialt (k : ℕ) : Set (ℕ → Bool) :=
  {ω | E521D.Ip (E521D.c2 (eAlt (eR ω)) k) (E521D.c2 (eAlt (eR ω)) (k + 1))}

lemma Ialt_cyl (k : ℕ) :
    Ialt k = rs (range (k + 2)) ⁻¹' {r | E521D.Ip (E521D.c2 (eAlt (extR (k + 2) r)) k)
      (E521D.c2 (eAlt (extR (k + 2) r)) (k + 1))} := by
  ext ω
  simp only [Ialt, Set.mem_setOf_eq, Set.mem_preimage]
  have h : ∀ i ≤ k + 1, E521D.c2 (eAlt (eR ω)) i = E521D.c2 (eAlt (extR (k + 2) (rs (range (k + 2)) ω))) i := by
    intro i hi
    unfold E521D.c2 eAlt
    apply sum_congr rfl; intro j hj; rw [mem_range] at hj
    rw [extR_rs _ _ (by omega)]
  rw [h k (by omega), h (k + 1) le_rfl]

/-- the involution `ε ↦ (j ↦ -(-1)^j ε_j)` on sign vectors. -/
def altU {n : ℕ} (ε : Fin n → ℤˣ) : Fin n → ℤˣ := fun j => -((-1) ^ (j : ℕ) * ε j)

lemma altU_invol {n : ℕ} (ε : Fin n → ℤˣ) : altU (altU ε) = ε := by
  funext j; simp only [altU]
  rw [neg_mul_eq_mul_neg, neg_neg, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp

lemma extR_ofSigns_altU (n : ℕ) (ε : Fin n → ℤˣ) (j : ℕ) (hj : j < n) :
    eAlt (extR n (ofSigns n ε)) j = extR n (ofSigns n (altU ε)) j := by
  rw [extR_ofSigns _ _ _ hj, eAlt, extR_ofSigns _ _ _ hj]
  simp only [altU]; push_cast; ring

theorem Ialt_real (k : ℕ) : μS.real (Ialt k) = R522.PP (R522.SCev (k + 2)) := by
  classical
  rw [Ialt_cyl, μS_range_bridge]
  have e : ∀ ε : Fin (k + 2) → ℤˣ, ∀ i ≤ k + 1,
      E521D.c2 (eAlt (extR (k + 2) (ofSigns (k + 2) ε))) i = E521D.c2 (extR (k + 2) (ofSigns (k + 2) (altU ε))) i := by
    intro ε i hi
    unfold E521D.c2
    apply sum_congr rfl; intro j hj; rw [mem_range] at hj
    rw [extR_ofSigns_altU _ _ _ (by omega)]
  have h1 : R522.PP (fun ε : Fin (k + 2) → ℤˣ => E521D.Ip (E521D.c2 (eAlt (extR (k + 2) (ofSigns (k + 2) ε))) k)
      (E521D.c2 (eAlt (extR (k + 2) (ofSigns (k + 2) ε))) (k + 1))) =
      R522.PP (fun ε : Fin (k + 2) → ℤˣ => R522.SCev (k + 2) (altU ε)) := by
    congr 1; funext ε
    obtain ⟨h1, h2⟩ := c2_signs k (altU ε)
    rw [e ε k (by omega), e ε (k + 1) le_rfl, h1, h2]
    rfl
  rw [h1]
  -- PP is invariant under the involution
  rw [R522.PP_eq, R522.PP_eq]
  unfold R522.EE
  congr 1
  exact Fintype.sum_equiv ⟨altU, altU, altU_invol, altU_invol⟩ _ _ (fun ε => rfl)

end E521

namespace E521

theorem cone_Ialt (K L k : ℕ) (hL : L ≤ K) (hk : k + 2 ≤ 2 * K - 2 * L) (F G : ℤ → Prop) :
    μS.real (coneE K F G ∩ Ialt k) ≤ ((N2 L 0 0 : ℝ) / 4 ^ L) * R522.PP (R522.SCev (k + 2)) := by
  have hsub : coneE K F G ∩ Ialt k ⊆ topE K L ∩ Ialt k :=
    Set.inter_subset_inter_left _ (cone_sub_top K L hL F G)
  obtain ⟨Q2, hQ2⟩ := topE_cyl K L hL
  have hcyl := Ialt_cyl k
  have hdis : Disjoint (range (k + 2)) (Ico (2 * K - 2 * L) (2 * K)) :=
    disjoint_range_Ico _ _ _ hk
  have hind := indep_blocks hdis {r | E521D.Ip (E521D.c2 (eAlt (extR (k + 2) r)) k)
    (E521D.c2 (eAlt (extR (k + 2) r)) (k + 1))} Q2
  rw [← hcyl, ← hQ2] at hind
  calc μS.real (coneE K F G ∩ Ialt k) ≤ μS.real (topE K L ∩ Ialt k) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ = μS.real (Ialt k ∩ topE K L) := by rw [Set.inter_comm]
    _ = μS.real (Ialt k) * μS.real (topE K L) := by
        rw [Measure.real, hind, ENNReal.toReal_mul]; rfl
    _ = _ := by rw [topE_real K L hL, Ialt_real]; ring

end E521

end S_P7

-- ===== D4 =====
section S_D4

/-! The closed quadrant forces nonnegative backward two-fold sums (original). -/

open Finset

namespace E521

/-- the backward sequence `a_i` read from the pairs: `a_{2j} = st (p j).1`, `a_{2j+1} = st (p j).2`. -/
lemma Tk_two_step {L : ℕ} (q : Fin L → Bool × Bool) (j : ℕ) (hj : j < L) :
    Tk q (2 * j + 1) = 2 * Uc q j + (dU (q ⟨j, hj⟩) + dV (q ⟨j, hj⟩)) ∧
    Ak q (2 * j + 1) = 2 * Vc q j + (dU (q ⟨j, hj⟩) + dV (q ⟨j, hj⟩)) := by
  obtain ⟨e1, e2⟩ := Tk_even q j hj.le
  obtain ⟨o1, o2⟩ := Tk_odd q j hj
  have hs : st (q ⟨j, hj⟩).1 = dU (q ⟨j, hj⟩) + dV (q ⟨j, hj⟩) := by
    rcases q ⟨j, hj⟩ with ⟨a, b⟩; cases a <;> cases b <;> simp [dU, dV, st]
  rw [o1, o2, e1, e2, hs]; exact ⟨rfl, rfl⟩

lemma Uc_succ {L : ℕ} (q : Fin L → Bool × Bool) (j : ℕ) (hj : j < L) :
    Uc q (j + 1) = Uc q j + dU (q ⟨j, hj⟩) := by
  unfold Uc; rw [sum_range_succ, dif_pos hj]

lemma Vc_succ {L : ℕ} (q : Fin L → Bool × Bool) (j : ℕ) (hj : j < L) :
    Vc q (j + 1) = Vc q j + dV (q ⟨j, hj⟩) := by
  unfold Vc; rw [sum_range_succ, dif_pos hj]

/-- `∑_{l ≤ k} T_l ≥ 0` on the closed quadrant (backward two-fold sums are nonnegative). -/
theorem T2_nonneg {L : ℕ} (q : Fin L → Bool × Bool) (hq : good2 L 0 0 q) :
    ∀ k ≤ 2 * L, 0 ≤ ∑ l ∈ range (k + 1), Tk q l ∧ 0 ≤ ∑ l ∈ range (k + 1), Ak q l := by
  rw [good2_iff] at hq
  -- even prefixes: ∑_{l ≤ 2J} T_l = ∑_{j<J} (U_j + 3 U_{j+1}) + V_J  (and symmetric for A)
  have heven : ∀ J ≤ L, ∑ l ∈ range (2 * J + 1), Tk q l =
      ∑ j ∈ range J, (Uc q j + 3 * Uc q (j + 1)) + Vc q J ∧
      ∑ l ∈ range (2 * J + 1), Ak q l = ∑ j ∈ range J, (Vc q j + 3 * Vc q (j + 1)) + Uc q J := by
    intro J hJ
    induction J with
    | zero => simp [Tk, Ak, Uc, Vc]
    | succ J ih =>
      obtain ⟨i1, i2⟩ := ih (by omega)
      have hJL : J < L := by omega
      rw [show 2 * (J + 1) + 1 = (2 * J + 1) + 1 + 1 by ring, sum_range_succ, sum_range_succ,
        sum_range_succ (fun l => Ak q l), sum_range_succ (fun l => Ak q l), i1, i2]
      obtain ⟨o1, o2⟩ := Tk_two_step q J hJL
      obtain ⟨e1, e2⟩ := Tk_even q (J + 1) (by omega)
      rw [show 2 * J + 1 + 1 = 2 * (J + 1) by ring, e1, e2, o1, o2, sum_range_succ, sum_range_succ,
        Uc_succ q J hJL, Vc_succ q J hJL]
      constructor <;> ring
  intro k hk
  have hU : ∀ j ≤ L, 0 ≤ Uc q j := fun j hj => by have := (hq j hj).1; simpa using this
  have hV : ∀ j ≤ L, 0 ≤ Vc q j := fun j hj => by have := (hq j hj).2; simpa using this
  have hsumU : ∀ J ≤ L, 0 ≤ ∑ j ∈ range J, (Uc q j + 3 * Uc q (j + 1)) := fun J hJ =>
    sum_nonneg (fun j hj => by rw [mem_range] at hj; linarith [hU j (by omega), hU (j + 1) (by omega)])
  have hsumV : ∀ J ≤ L, 0 ≤ ∑ j ∈ range J, (Vc q j + 3 * Vc q (j + 1)) := fun J hJ =>
    sum_nonneg (fun j hj => by rw [mem_range] at hj; linarith [hV j (by omega), hV (j + 1) (by omega)])
  obtain ⟨J, rfl | rfl⟩ := Nat.even_or_odd' k
  · obtain ⟨h1, h2⟩ := heven J (by omega)
    rw [h1, h2]
    exact ⟨by linarith [hsumU J (by omega), hV J (by omega)], by linarith [hsumV J (by omega), hU J (by omega)]⟩
  · -- k = 2J+1 < 2L
    have hJL : J < L := by omega
    obtain ⟨h1, h2⟩ := heven J (by omega)
    obtain ⟨o1, o2⟩ := Tk_two_step q J hJL
    rw [show 2 * J + 1 + 1 = (2 * J + 1) + 1 by ring, sum_range_succ, sum_range_succ (fun l => Ak q l),
      h1, h2, o1, o2]
    have hu1 := hU (J + 1) (by omega)
    have hv1 := hV (J + 1) (by omega)
    rw [Uc_succ q J hJL] at hu1
    rw [Vc_succ q J hJL] at hv1
    constructor
    · nlinarith [hsumU J (by omega), hV J (by omega), hU J (by omega)]
    · nlinarith [hsumV J (by omega), hU J (by omega), hV J (by omega)]

end E521

end S_D4

-- ===== D5 =====
section S_D5

/-! Real roots: from `ℂ` to `ℝ`, and negative roots via `x ↦ -x` (original). -/

open Polynomial

namespace E521D

open scoped Classical in
lemma realRoots_card (p : ℝ[X]) :
    ((p.map Complex.ofRealHom).roots.filter (fun z => ∃ r : ℝ, (r : ℂ) = z)).card = p.roots.card := by
  classical
  have h := filter_roots_map_range_eq_map_roots (f := Complex.ofRealHom) Complex.ofReal_injective p
  have e : (p.map Complex.ofRealHom).roots.filter (fun z => ∃ r : ℝ, (r : ℂ) = z) =
      (p.map Complex.ofRealHom).roots.filter (· ∈ Complex.ofRealHom.range) := by
    apply Multiset.filter_congr; intro z _; simp [RingHom.mem_range]
  rw [e, h, Multiset.card_map]

lemma neg_comp_aux (p : ℝ[X]) (a : ℝ) (k : ℕ) :
    (X - C a) ^ k ∣ p.comp (-X) ↔ (X - C (-a)) ^ k ∣ p := by
  have key : ∀ q : ℝ[X], (q.comp (-X)).comp (-X) = q := by
    intro q; rw [comp_assoc]; simp
  have hlin : (X - C (-a)).comp (-X) = -(X - C a) := by simp; ring
  constructor
  · intro h
    obtain ⟨r, hr⟩ := h
    refine ⟨(-1) ^ k * r.comp (-X), ?_⟩
    have := congrArg (fun q => q.comp (-X)) hr
    simp only [key] at this
    rw [this, mul_comp, pow_comp]
    have e2 : (X - C a).comp (-X) = -(X - C (-a)) := by simp; ring
    rw [e2, neg_pow]; ring
  · intro h
    obtain ⟨r, hr⟩ := h
    refine ⟨(-1) ^ k * r.comp (-X), ?_⟩
    rw [hr, mul_comp, pow_comp, hlin, neg_pow]; ring

lemma rootMultiplicity_comp_neg (p : ℝ[X]) (a : ℝ) :
    rootMultiplicity a (p.comp (-X)) = rootMultiplicity (-a) p := by
  by_cases hp : p = 0
  · simp [hp]
  have hp' : p.comp (-X) ≠ 0 := by
    intro h
    have := congrArg (fun q => q.comp (-X)) h
    simp only [zero_comp] at this
    rw [comp_assoc] at this; simp at this; exact hp this
  apply le_antisymm
  · rw [le_rootMultiplicity_iff hp, ← neg_comp_aux]
    exact pow_rootMultiplicity_dvd _ _
  · rw [le_rootMultiplicity_iff hp', neg_comp_aux]
    exact pow_rootMultiplicity_dvd _ _

lemma roots_comp_neg (p : ℝ[X]) : (p.comp (-X)).roots = p.roots.map (fun x => -x) := by
  classical
  ext a
  rw [count_roots, rootMultiplicity_comp_neg, ← count_roots]
  have h := Multiset.count_map_eq_count' (fun x : ℝ => -x) p.roots neg_injective (-a)
  simp only [neg_neg] at h
  exact h.symm

lemma countP_neg_roots (p : ℝ[X]) :
    p.roots.countP (· < 0) = (p.comp (-X)).roots.countP (0 < ·) := by
  rw [roots_comp_neg, Multiset.countP_map, Multiset.countP_eq_card_filter]
  simp only [neg_pos]

/-- the number of real roots splits into positive and negative ones when `p(0) ≠ 0`. -/
lemma card_roots_split (p : ℝ[X]) (h0 : p.eval 0 ≠ 0) :
    p.roots.card = p.roots.countP (0 < ·) + (p.comp (-X)).roots.countP (0 < ·) := by
  rw [← countP_neg_roots]
  have h1 := Multiset.card_eq_countP_add_countP (fun x : ℝ => 0 < x) p.roots
  have h2 : p.roots.countP (fun x => ¬ 0 < x) = p.roots.countP (· < 0) := by
    apply Multiset.countP_congr rfl
    intro x hx
    have hx0 : x ≠ 0 := by
      intro h; rw [h] at hx
      exact h0 (isRoot_of_mem_roots hx)
    simp only [not_lt]
    apply propext
    constructor
    · intro h; exact lt_of_le_of_ne h hx0
    · intro h; exact h.le
  rw [h1, h2]

end E521D

end S_D5

-- ===== D6 =====
section S_D6

/-! The positive-root bound (original). -/

open Polynomial Finset

namespace E521D

lemma T_ne_zero (e : ℕ → ℝ) (he : ∀ j, e j = 1 ∨ e j = -1) (n : ℕ) : T e (n + 1) ≠ 0 := by
  intro h
  have := congrArg (fun p => p.coeff 0) h
  simp only [T_coeff, coeff_zero] at this
  rw [if_pos (by omega)] at this
  rcases he 0 with h0 | h0 <;> rw [h0] at this <;> norm_num at this

lemma DN_ne_zero (N : ℕ) : DN N ≠ 0 := by
  intro h
  have := congrArg (fun p => p.coeff 0) h
  simp only [DN, finsetSum_coeff, coeff_X_pow, coeff_zero] at this
  rw [sum_eq_single 0] at this
  · simp at this
  · intro b _ hb; rw [if_neg (Ne.symm hb)]
  · intro h0; exact absurd (mem_range.mpr (by omega)) h0

lemma DN_pos_roots (N : ℕ) : (DN N * DN N).roots.countP (0 < ·) = 0 := by
  rw [Multiset.countP_eq_zero]
  intro x hx hx0
  have hr := isRoot_of_mem_roots hx
  rw [IsRoot, eval_mul, mul_self_eq_zero] at hr
  unfold DN at hr
  rw [eval_finset_sum] at hr
  have : 0 < ∑ i ∈ range (N + 1), eval x (X ^ i : ℝ[X]) := by
    apply sum_pos (fun i _ => by rw [eval_pow, eval_X]; exact pow_pos hx0 i) ⟨0, by simp⟩
  linarith

/-- **Positive roots** of `f = ∑_{j≤n} e_j X^j`: at most `#{k < p : Ip(c_k, c_{k+1})} + 1`, when
the forward partial sums are `≥ 1` on `[p, n]`, the backward two-fold sums are `≥ 0`, and `N ≥ n²+n+1`. -/
theorem pos_roots_le (e : ℕ → ℝ) (he : ∀ j, e j = 1 ∨ e j = -1) (n p N : ℕ) (hp : p ≤ n)
    (hN : n * n + n + 1 ≤ N) (hS : ∀ j, p ≤ j → j ≤ n → 1 ≤ S1 e j)
    (hB : ∀ k ≤ n, 0 ≤ b2 e n k) :
    (T e (n + 1)).roots.countP (0 < ·) ≤
      ((range p).filter (fun k => Ip (c2 e k) (c2 e (k + 1)))).card + 1 := by
  classical
  set Q := T e (n + 1) * (DN N * DN N) with hQ
  have hf0 := T_ne_zero e he n
  have hD0 : DN N * DN N ≠ 0 := mul_ne_zero (DN_ne_zero N) (DN_ne_zero N)
  have hQ0 : Q ≠ 0 := mul_ne_zero hf0 hD0
  have hnN : n ≤ N := by nlinarith
  -- roots of f are roots of Q
  have hroots : (T e (n + 1)).roots.countP (0 < ·) ≤ Q.roots.countP (0 < ·) := by
    rw [hQ, roots_mul hQ0, Multiset.countP_add]; omega
  refine hroots.trans ((roots_countP_pos_le_signVariations Q).trans ?_)
  set c := Q.coeff with hc
  set D := Q.natDegree with hD
  have hQT : Q = T c (D + 1) := by
    rw [hc]; unfold T; exact as_sum_range_C_mul_X_pow Q
  -- coefficient facts
  have hlow : ∀ k ≤ n, c k = c2 e k := fun k hk => Qc_low e hk hnN
  have hS1n : 1 ≤ S1 e n := hS n hp le_rfl
  have hdiff : ∀ k, c2 e (k + 1) - c2 e k = S1 e (k + 1) := by
    intro k; unfold c2 S1
    rw [sum_range_succ (fun j => e j * (((k + 1 : ℕ) : ℝ) - j + 1)), sum_range_succ (fun j => e j)]
    have : ∑ j ∈ range (k + 1), e j * (((k + 1 : ℕ) : ℝ) - j + 1) - ∑ j ∈ range (k + 1), e j * ((k : ℝ) - j + 1)
        = ∑ j ∈ range (k + 1), e j := by
      rw [← sum_sub_distrib]; apply sum_congr rfl; intro j _; push_cast; ring
    push_cast at this ⊢
    linarith
  have hinc : ∀ k, p ≤ k → k < N → c k < c (k + 1) := by
    intro k hk1 hk2
    by_cases hkn : k + 1 ≤ n
    · rw [hlow k (by omega), hlow (k + 1) hkn]
      have := hdiff k; have := hS (k + 1) (by omega) hkn; linarith
    · have hk : n ≤ k := by omega
      have h1 := Qc_mid_lin e (N := N) hk hk2.le
      have h2 := Qc_mid_lin e (n := n) (N := N) (k := k + 1) (by omega) hk2
      rw [← hQ] at h1 h2
      show Q.coeff k < Q.coeff (k + 1)
      rw [h1, h2]
      have : ∑ j ∈ range (n + 1), e j * (((k + 1 : ℕ) : ℝ) - j + 1) - ∑ j ∈ range (n + 1), e j * ((k : ℝ) - j + 1)
          = S1 e n := by
        unfold S1; rw [← sum_sub_distrib]; apply sum_congr rfl; intro j _; push_cast; ring
      linarith
  have hmidpos : ∀ k, N ≤ k → k ≤ N + n → 0 < c k := by
    intro k h1 h2
    have := Qc_mid_pos e he hN hS1n h1 h2
    rw [← hQ] at this; exact this
  have hDle : D ≤ 2 * N + n := by
    rw [hD, hQ]
    refine (natDegree_mul_le).trans ?_
    have h1 : (T e (n + 1)).natDegree ≤ n := by
      have := T_degree_lt e (n + 1)
      exact Nat.lt_succ_iff.mp ((natDegree_lt_iff_degree_lt hf0).mpr this)
    have h2 : (DN N * DN N).natDegree ≤ 2 * N := by
      refine (natDegree_mul_le).trans ?_
      have : (DN N).natDegree ≤ N := by
        unfold DN
        refine (natDegree_sum_le _ _).trans ?_
        rw [Finset.fold_max_le]
        refine ⟨by omega, fun i hi => ?_⟩
        rw [mem_range] at hi; simp only [Function.comp, natDegree_X_pow]; omega
      omega
    omega
  have hNle : N ≤ D := by
    rw [hD]; apply le_natDegree_of_ne_zero
    have := hmidpos N le_rfl (by omega)
    rw [hc] at this; exact this.ne'
  have htop : ∀ k, N < k → k ≤ D → 0 ≤ c k := by
    intro k h1 h2
    by_cases hk : k ≤ N + n
    · exact (hmidpos k h1.le hk).le
    · have h := Qc_top e (N := N) (k := k) (by omega) (by omega) hnN
      rw [← hQ] at h
      show 0 ≤ Q.coeff k
      rw [h]
      set k' := 2 * N + n - k with hk'
      by_cases hkn : k' ≤ n
      · have : ∑ i ∈ range (n + 1), (if i ≤ k' then e (n - i) * ((k' : ℝ) - i + 1) else 0) = b2 e n k' := by
          unfold b2
          rw [show n + 1 = (k' + 1) + (n - k') by omega, sum_range_add]
          have : ∑ x ∈ range (n - k'), (if k' + 1 + x ≤ k' then e (n - (k' + 1 + x)) *
              ((k' : ℝ) - ((k' + 1 + x : ℕ) : ℝ) + 1) else 0) = 0 := by
            apply sum_eq_zero; intro x _; rw [if_neg (by omega)]
          rw [this, add_zero]
          apply sum_congr rfl; intro i hi; rw [mem_range] at hi; rw [if_pos (by omega)]
        rw [this]; exact hB k' hkn
      · have : ∑ i ∈ range (n + 1), (if i ≤ k' then e (n - i) * ((k' : ℝ) - i + 1) else 0) =
            b2 e n n + ((k' : ℝ) - n) * S1 e n := by
          unfold b2 S1
          rw [← sum_range_reflect (fun j => e j) (n + 1), mul_sum, ← sum_add_distrib]
          apply sum_congr rfl; intro i hi; rw [mem_range] at hi
          rw [if_pos (by omega), show n + 1 - 1 - i = n - i by omega]; ring
        rw [this]
        have := hB n le_rfl
        have : (0 : ℝ) ≤ (k' : ℝ) - n := by
          have : (n : ℝ) ≤ k' := by exact_mod_cast (by omega : n ≤ k')
          linarith
        nlinarith
  -- assemble the sign-variation count
  rw [hQT]
  have s1 := sv_range c 0 p (Nat.zero_le p)
  simp only [zero_add] at s1
  rw [sv_one] at s1
  have s2 := sv_range c p N (by omega)
  have s3 := Ip_incr c p N hinc
  have hlead : 0 < (T c (N + 1)).leadingCoeff := by
    rw [T_lead_of c (hmidpos N le_rfl (by omega)).ne']; exact hmidpos N le_rfl (by omega)
  have s4 := (sv_nonneg c N hlead D hNle (fun k h1 h2 => htop k h1 h2)).1
  have hcount : ((Ico 0 p).filter (fun k => Ip (c k) (c (k + 1)))).card =
      ((range p).filter (fun k => Ip (c2 e k) (c2 e (k + 1)))).card := by
    rw [range_eq_Ico]
    congr 1
    apply filter_congr; intro k hk; rw [mem_Ico] at hk
    rw [hlow k (by omega), hlow (k + 1) (by omega)]
  rw [hcount] at s1
  omega

end E521D

end S_D6

-- ===== F0 =====
section S_F0

/-! The site statement's objects in our notation (original). -/

open Polynomial Finset MeasureTheory Filter Topology
open scoped ENNReal

namespace E521

/-- verbatim copies of the statement's definitions (namespace `OMA.S_erdos_521`). -/
noncomputable def signMeasure' : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false))

def eps' (k : ℕ) (ω : ℕ → Bool) : ℤ := if ω k then 1 else -1

noncomputable def randPoly' (n : ℕ) (ω : ℕ → Bool) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C ((eps' k ω : ℂ)) * Polynomial.X ^ k

open scoped Classical in
noncomputable def realRootCount' (n : ℕ) (ω : ℕ → Bool) : ℕ :=
  ((randPoly' n ω).roots.filter (fun z => ∃ r : ℝ, (r : ℂ) = z)).card

lemma signMeasure'_eq : signMeasure' = μS := rfl

/-- the real polynomial. -/
noncomputable def fR (n : ℕ) (ω : ℕ → Bool) : ℝ[X] := E521D.T (eR ω) (n + 1)

lemma randPoly'_eq (n : ℕ) (ω : ℕ → Bool) : randPoly' n ω = (fR n ω).map Complex.ofRealHom := by
  unfold randPoly' fR E521D.T
  rw [Polynomial.map_sum]
  apply sum_congr rfl; intro k _
  rw [Polynomial.map_mul, Polynomial.map_pow, map_X, map_C]
  congr 2
  unfold eps' eR; split_ifs <;> simp

lemma realRootCount'_eq (n : ℕ) (ω : ℕ → Bool) : realRootCount' n ω = (fR n ω).roots.card := by
  classical
  unfold realRootCount'
  rw [randPoly'_eq]
  convert E521D.realRoots_card (fR n ω)

end E521

end S_F0

-- ===== P8 =====
section S_P8

/-! On the good event, the number of real roots is at most the two sign-change counts plus two
(original). -/

open Finset MeasureTheory Polynomial

namespace E521

noncomputable instance instDecIev (k : ℕ) (ω : ℕ → Bool) : Decidable (ω ∈ Iev k) :=
  inferInstanceAs (Decidable (E521D.Ip _ _))

noncomputable instance instDecIalt (k : ℕ) (ω : ℕ → Bool) : Decidable (ω ∈ Ialt k) :=
  inferInstanceAs (Decidable (E521D.Ip _ _))

/-- forward partial sums from the total and a backward block. -/
lemma fwd_split (e : ℕ → ℝ) (n j : ℕ) (hj : j ≤ n) :
    E521D.S1 e j = ∑ i ∈ range (n + 1), e (n - i) - ∑ i ∈ range (n - j), e (n - i) := by
  unfold E521D.S1
  rw [show n + 1 = (n - j) + (j + 1) by omega, sum_range_add (fun i => e (n - i)) (n - j) (j + 1)]
  have : ∑ y ∈ range (j + 1), e (n - (n - j + y)) = ∑ y ∈ range (j + 1), e y := by
    rw [← sum_range_reflect]
    apply sum_congr rfl; intro y hy; rw [mem_range] at hy; congr 1; omega
  rw [this]; ring

lemma eAlt_pm (e : ℕ → ℝ) (he : ∀ j, e j = 1 ∨ e j = -1) (j : ℕ) : eAlt e j = 1 ∨ eAlt e j = -1 := by
  unfold eAlt
  rcases neg_one_pow_eq_or ℝ j with h | h <;> rcases he j with h' | h' <;> rw [h, h'] <;> norm_num

lemma aS_real (K : ℕ) (ω : ℕ → Bool) (i : ℕ) (hi : i < 2 * K) :
    ((aS (Φ K ω) i : ℤ) : ℝ) = eR ω (2 * K - 1 - i) := by
  rw [aS_Φ K ω i hi]; unfold st eR; split_ifs <;> simp

lemma Tk_real (K : ℕ) (ω : ℕ → Bool) (l : ℕ) (hl : l ≤ 2 * K) :
    ((Tk (Φ K ω) l : ℤ) : ℝ) = ∑ i ∈ range l, eR ω (2 * K - 1 - i) := by
  unfold Tk; push_cast
  apply sum_congr rfl; intro i hi; rw [mem_range] at hi; exact aS_real K ω i (by omega)

lemma Ak_real (K : ℕ) (ω : ℕ → Bool) (l : ℕ) (hl : l ≤ 2 * K) :
    ((Ak (Φ K ω) l : ℤ) : ℝ) = ∑ i ∈ range l, (-1) ^ i * eR ω (2 * K - 1 - i) := by
  unfold Ak; push_cast
  apply sum_congr rfl; intro i hi; rw [mem_range] at hi; rw [aS_real K ω i (by omega)]

/-- backward two-fold sums are sums of backward partial sums. -/
lemma b2_eq_sumT (e : ℕ → ℝ) (n k : ℕ) :
    E521D.b2 e n k = ∑ l ∈ range (k + 2), ∑ i ∈ range l, e (n - i) := by
  unfold E521D.b2
  induction k with
  | zero => simp [sum_range_succ]
  | succ k ih =>
    rw [sum_range_succ (fun l => ∑ i ∈ range l, e (n - i)), ← ih]
    rw [sum_range_succ (fun i => e (n - i) * (((k + 1 : ℕ) : ℝ) - i + 1))]
    rw [sum_range_succ (fun i => e (n - i))]
    have : ∑ i ∈ range (k + 1), e (n - i) * (((k + 1 : ℕ) : ℝ) - i + 1) =
        ∑ i ∈ range (k + 1), e (n - i) * ((k : ℝ) - i + 1) + ∑ i ∈ range (k + 1), e (n - i) := by
      rw [← sum_add_distrib]; apply sum_congr rfl; intro i _; push_cast; ring
    rw [this]; push_cast; ring

end E521

namespace E521

lemma neg_one_pow_sub {n i : ℕ} (hn : Odd n) (hi : i ≤ n) : ((-1 : ℝ) ^ (n - i)) = -((-1) ^ i) := by
  have h : (-1 : ℝ) ^ (n - i) * (-1) ^ i = -1 := by
    rw [← pow_add, Nat.sub_add_cancel hi, hn.neg_one_pow]
  have h2 : ((-1 : ℝ) ^ i) * (-1) ^ i = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  calc (-1 : ℝ) ^ (n - i) = (-1) ^ (n - i) * ((-1) ^ i * (-1) ^ i) := by rw [h2, mul_one]
    _ = ((-1) ^ (n - i) * (-1) ^ i) * (-1) ^ i := by ring
    _ = -((-1) ^ i) := by rw [h]; ring

/-- the negative-root polynomial. -/
lemma comp_neg_eq (e : ℕ → ℝ) (n : ℕ) :
    -((E521D.T e (n + 1)).comp (-X)) = E521D.T (eAlt e) (n + 1) := by
  unfold E521D.T eAlt
  rw [Polynomial.sum_comp, ← sum_neg_distrib]
  apply sum_congr rfl; intro j _
  rw [mul_comp, C_comp, pow_comp, X_comp, neg_pow]
  simp only [map_neg, map_mul, map_pow, map_one]
  ring

/-- **roots on the good event.** -/
theorem roots_good (K t lam : ℕ) (ω : ℕ → Bool) (hK : 1 ≤ K) (ht : t ≤ 2 * K - 1)
    (hcone : ω ∈ coneE K (fun y => (lam : ℤ) ≤ y) (fun y => (lam : ℤ) ≤ y))
    (hG : ∀ l ≤ t, |∑ i ∈ range l, eR ω (2 * K - 1 - i)| < 2 * lam - 1)
    (hG' : ∀ l ≤ t, |∑ i ∈ range l, (-1) ^ i * eR ω (2 * K - 1 - i)| < 2 * lam - 1) :
    (fR (2 * K - 1) ω).roots.card ≤
      ((range (2 * K - 1 - t)).filter (fun k => ω ∈ Iev k)).card +
      ((range (2 * K - 1 - t)).filter (fun k => ω ∈ Ialt k)).card + 2 := by
  classical
  set n := 2 * K - 1 with hn
  have hnodd : Odd n := ⟨K - 1, by omega⟩
  simp only [coneE, Set.mem_preimage, Set.mem_setOf_eq] at hcone
  rw [good2F_iff] at hcone
  obtain ⟨hquad, hUf, hVf⟩ := hcone
  have hq : good2 K 0 0 (Φ K ω) := by
    rw [good2_iff]; intro j hj; exact hquad j hj
  have hT2 := T2_nonneg (Φ K ω) hq
  -- final sums
  obtain ⟨eT, eA⟩ := Tk_even (Φ K ω) K le_rfl
  have hSn : 2 * (lam : ℝ) ≤ ∑ i ∈ range (2 * K), eR ω (2 * K - 1 - i) := by
    rw [← Tk_real K ω (2 * K) le_rfl, eT]; push_cast
    have h1 : (lam : ℤ) ≤ Uc (Φ K ω) K := by simpa using hUf
    have h2 : ((lam : ℤ) : ℝ) ≤ ((Uc (Φ K ω) K : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  have hAn : 2 * (lam : ℝ) ≤ ∑ i ∈ range (2 * K), (-1) ^ i * eR ω (2 * K - 1 - i) := by
    rw [← Ak_real K ω (2 * K) le_rfl, eA]; push_cast
    have h1 : (lam : ℤ) ≤ Vc (Φ K ω) K := by simpa using hVf
    have h2 : ((lam : ℤ) : ℝ) ≤ ((Vc (Φ K ω) K : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  have he := eR_pm ω
  have hf0 : (fR n ω).eval 0 ≠ 0 := by
    unfold fR E521D.T
    rw [eval_finsetSum]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    rw [sum_eq_single 0]
    · simp; rcases he 0 with h | h <;> rw [h] <;> norm_num
    · intro b _ hb; simp [zero_pow hb]
    · intro h; exact absurd (mem_range.mpr (by omega)) h
  rw [E521D.card_roots_split _ hf0]
  have hn1 : n + 1 = 2 * K := by omega
  have hSn' : 2 * (lam : ℝ) ≤ ∑ i ∈ range (2 * K), eR ω (n - i) := hSn
  have hAn' : 2 * (lam : ℝ) ≤ ∑ i ∈ range (2 * K), (-1) ^ i * eR ω (n - i) := hAn
  have heA := eAlt_pm (eR ω) he
  have halt : ∀ i ≤ n, eAlt (eR ω) (n - i) = (-1) ^ i * eR ω (n - i) := by
    intro i hi; unfold eAlt; rw [neg_one_pow_sub hnodd hi]; ring
  -- forward partial sums
  have hS : ∀ j, n - t ≤ j → j ≤ n → 1 ≤ E521D.S1 (eR ω) j := by
    intro j hj1 hj2
    rw [fwd_split _ n j hj2, hn1]
    have hb := hG (n - j) (by omega)
    have := (abs_lt.mp hb).2
    linarith
  have hSA : ∀ j, n - t ≤ j → j ≤ n → 1 ≤ E521D.S1 (eAlt (eR ω)) j := by
    intro j hj1 hj2
    rw [fwd_split _ n j hj2]
    have e1 : ∑ i ∈ range (n + 1), eAlt (eR ω) (n - i) = ∑ i ∈ range (2 * K), (-1) ^ i * eR ω (n - i) := by
      rw [hn1]; apply sum_congr rfl; intro i hi; rw [mem_range] at hi; rw [halt i (by omega)]
    have e2 : ∑ i ∈ range (n - j), eAlt (eR ω) (n - i) = ∑ i ∈ range (n - j), (-1) ^ i * eR ω (n - i) := by
      apply sum_congr rfl; intro i hi; rw [mem_range] at hi; rw [halt i (by omega)]
    rw [e1, e2]
    have hb := hG' (n - j) (by omega)
    have := (abs_lt.mp hb).2
    linarith
  -- backward two-fold sums
  have hB : ∀ k ≤ n, 0 ≤ E521D.b2 (eR ω) n k := by
    intro k hk
    rw [b2_eq_sumT]
    have h := (hT2 (k + 1) (by omega)).1
    have e : ∑ l ∈ range (k + 1 + 1), ((Tk (Φ K ω) l : ℤ) : ℝ) = ∑ l ∈ range (k + 2), ∑ i ∈ range l, eR ω (n - i) := by
      apply sum_congr rfl; intro l hl; rw [mem_range] at hl; rw [Tk_real K ω l (by omega)]
    have h' : (0 : ℝ) ≤ ∑ l ∈ range (k + 1 + 1), ((Tk (Φ K ω) l : ℤ) : ℝ) := by exact_mod_cast h
    rw [e] at h'; exact h'
  have hBA : ∀ k ≤ n, 0 ≤ E521D.b2 (eAlt (eR ω)) n k := by
    intro k hk
    rw [b2_eq_sumT]
    have h := (hT2 (k + 1) (by omega)).2
    have e : ∑ l ∈ range (k + 1 + 1), ((Ak (Φ K ω) l : ℤ) : ℝ) = ∑ l ∈ range (k + 2), ∑ i ∈ range l, eAlt (eR ω) (n - i) := by
      apply sum_congr rfl; intro l hl; rw [mem_range] at hl; rw [Ak_real K ω l (by omega)]
      apply sum_congr rfl; intro i hi; rw [mem_range] at hi; rw [halt i (by omega)]
    have h' : (0 : ℝ) ≤ ∑ l ∈ range (k + 1 + 1), ((Ak (Φ K ω) l : ℤ) : ℝ) := by exact_mod_cast h
    rw [e] at h'; exact h'
  have hpos := E521D.pos_roots_le (eR ω) he n (n - t) (n * n + n + 1) (by omega) le_rfl hS hB
  have hneg := E521D.pos_roots_le (eAlt (eR ω)) heA n (n - t) (n * n + n + 1) (by omega) le_rfl hSA hBA
  have hcomp : ((fR n ω).comp (-X)).roots = (E521D.T (eAlt (eR ω)) (n + 1)).roots := by
    rw [← comp_neg_eq, roots_neg]; rfl
  have c1 : ((range (n - t)).filter (fun k => ω ∈ Iev k)).card =
      ((range (n - t)).filter (fun k => E521D.Ip (E521D.c2 (eR ω) k) (E521D.c2 (eR ω) (k + 1)))).card := by
    congr 1
  have c2' : ((range (n - t)).filter (fun k => ω ∈ Ialt k)).card =
      ((range (n - t)).filter (fun k => E521D.Ip (E521D.c2 (eAlt (eR ω)) k) (E521D.c2 (eAlt (eR ω)) (k + 1)))).card := by
    congr 1
  rw [hcomp, c1, c2']
  have hfR : fR n ω = E521D.T (eR ω) (n + 1) := rfl
  rw [hfR]
  omega

end E521

end S_P8

-- ===== Q4 =====
section S_Q4

/-! Markov for a count of events restricted to an event (original). -/

open MeasureTheory Finset

namespace E521Q

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem markov_count (E : Set Ω) (hE : MeasurableSet E) (s : Finset ℕ) (B : ℕ → Set Ω)
    (hB : ∀ k, MeasurableSet (B k)) [∀ k, DecidablePred (· ∈ B k)] {A : ℝ} (hA : 0 < A) :
    A * μ.real (E ∩ {ω | A ≤ ((s.filter (fun k => ω ∈ B k)).card : ℝ)}) ≤ ∑ k ∈ s, μ.real (E ∩ B k) := by
  classical
  set C := E ∩ {ω | A ≤ ((s.filter (fun k => ω ∈ B k)).card : ℝ)} with hC
  have hcnt : ∀ ω, ((s.filter (fun k => ω ∈ B k)).card : ℝ) = ∑ k ∈ s, (B k).indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    rw [card_filter]; push_cast
    apply sum_congr rfl; intro k _
    by_cases h : ω ∈ B k <;> simp [h]
  have hCm : MeasurableSet C := by
    apply hE.inter
    have : {ω | A ≤ ((s.filter (fun k => ω ∈ B k)).card : ℝ)} =
        {ω | A ≤ ∑ k ∈ s, (B k).indicator (fun _ => (1 : ℝ)) ω} := by
      ext ω; simp only [Set.mem_setOf_eq, hcnt]
    rw [this]
    exact measurableSet_le measurable_const
      (Finset.measurable_sum _ (fun k _ => (measurable_const.indicator (hB k))))
  have hpt : ∀ ω, A * C.indicator (fun _ => (1 : ℝ)) ω ≤
      ∑ k ∈ s, (E ∩ B k).indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ C
    · rw [Set.indicator_of_mem hω, mul_one]
      have h1 : A ≤ ((s.filter (fun k => ω ∈ B k)).card : ℝ) := hω.2
      rw [hcnt] at h1
      refine h1.trans (le_of_eq ?_)
      apply sum_congr rfl; intro k _
      by_cases h : ω ∈ B k
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show ω ∈ E ∩ B k from ⟨hω.1, h⟩)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' : ω ∈ E ∩ B k => h h'.2)]
    · rw [Set.indicator_of_notMem hω, mul_zero]
      exact sum_nonneg (fun k _ => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
  have hi : ∀ k, Integrable ((E ∩ B k).indicator (fun _ => (1 : ℝ))) μ :=
    fun k => (integrable_const 1).indicator (hE.inter (hB k))
  have := integral_mono ((integrable_const (1 : ℝ)).indicator hCm |>.const_mul A)
    (integrable_finset_sum s (fun k _ => hi k)) hpt
  rw [integral_const_mul, integral_indicator_const _ hCm, integral_finset_sum s (fun k _ => hi k)] at this
  rw [sum_congr rfl (fun k _ => integral_indicator_const (1 : ℝ) (μ := μ) (hE.inter (hB k)))] at this
  simpa using this

end E521Q

end S_Q4

-- ===== Q2 =====
section S_Q2

/-! Harmonic-type sums (original). -/

open Finset Real

namespace E521Q

lemma inv_succ_le_log (k : ℕ) (hk : 1 ≤ k) : 1 / ((k : ℝ) + 1) ≤ Real.log (k + 1) - Real.log k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [← Real.log_div (by positivity) hk0.ne']
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < k / (k + 1) by positivity)
  rw [Real.log_div hk0.ne' (by positivity)] at h
  rw [Real.log_div (by positivity) hk0.ne']
  have : (k : ℝ) / (k + 1) - 1 = -(1 / ((k : ℝ) + 1)) := by field_simp; ring
  linarith

/-- `∑_{k=a}^{b-1} 1/(k+1) ≤ log b - log a` for `1 ≤ a ≤ b`. -/
lemma harm_Ico (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ k ∈ Ico a b, 1 / ((k : ℝ) + 1) ≤ Real.log b - Real.log a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [sum_Ico_succ_top hab]
    have := inv_succ_le_log b (by omega)
    push_cast
    linarith

/-- partial fractions: `1/((k+2)(n-k)) = (1/(n+2)) (1/(k+2) + 1/(n-k))`. -/
lemma pf (n k : ℕ) (hk : k < n) :
    1 / (((k : ℝ) + 2) * ((n : ℝ) - k)) = 1 / ((n : ℝ) + 2) * (1 / ((k : ℝ) + 2) + 1 / ((n : ℝ) - k)) := by
  have h1 : (0 : ℝ) < (n : ℝ) - k := by
    have : (k : ℝ) < n := by exact_mod_cast hk
    linarith
  field_simp
  ring

/-- `∑_{k<p} 1/((k+2)(n-k)) ≤ (log (p+1) + log n - log (n-p+1) + 1) / (n+2)` for `p ≤ n`. -/
lemma double_harm (n p : ℕ) (hpl : p < n) (hn : 1 ≤ n) :
    ∑ k ∈ range p, 1 / (((k : ℝ) + 2) * ((n : ℝ) - k)) ≤
      (Real.log (p + 1) + (Real.log n - Real.log (n - p + 1)) + 1) / ((n : ℝ) + 2) := by
  have hp : p ≤ n := hpl.le
  rcases Nat.eq_zero_or_pos p with h0 | hp0
  · subst h0; simp
    have : 0 ≤ Real.log (n : ℝ) - Real.log ((n : ℝ) + 1) + 1 := by
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < ((n : ℝ) + 1) / n by positivity)
      rw [Real.log_div (by positivity) hn0.ne'] at this
      have : ((n : ℝ) + 1) / n - 1 ≤ 1 := by
        rw [div_sub_one hn0.ne', div_le_one hn0]
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      linarith
    first | exact div_nonneg (by linarith) (by positivity) | linarith | positivity
  have e : ∀ k ∈ range p, 1 / (((k : ℝ) + 2) * ((n : ℝ) - k)) =
      1 / ((n : ℝ) + 2) * (1 / ((k + 1 : ℕ) + 1 : ℝ) + 1 / (((n - k - 1 : ℕ) : ℝ) + 1)) := by
    intro k hk; rw [mem_range] at hk
    rw [pf n k (by omega)]
    congr 2
    · push_cast; ring
    · rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  rw [sum_congr rfl e, ← mul_sum, sum_add_distrib]
  -- first harmonic piece: k+1 ranges over [1, p]
  have h1 : ∑ k ∈ range p, 1 / (((k + 1 : ℕ) : ℝ) + 1) ≤ Real.log (p + 1) := by
    have := harm_Ico 1 (p + 1) le_rfl (by omega)
    rw [Nat.cast_one, Real.log_one, sub_zero] at this
    have e2 : ∑ k ∈ Ico 1 (p + 1), 1 / ((k : ℝ) + 1) = ∑ k ∈ range p, 1 / (((k + 1 : ℕ) : ℝ) + 1) := by
      rw [sum_Ico_eq_sum_range]; apply sum_congr (by congr 1) ; intro k _; push_cast; ring_nf
    rw [← e2]; push_cast at this ⊢; exact this
  -- second piece: n-k-1 ranges over [n-p, n-1]
  have h2 : ∑ k ∈ range p, 1 / (((n - k - 1 : ℕ) : ℝ) + 1) ≤ (Real.log n - Real.log (n - p + 1)) + 1 := by
    have hrefl : ∑ k ∈ range p, 1 / (((n - k - 1 : ℕ) : ℝ) + 1) = ∑ j ∈ Ico (n - p) n, 1 / ((j : ℝ) + 1) := by
      rw [sum_Ico_eq_sum_range, show n - (n - p) = p by omega, ← sum_range_reflect]
      apply sum_congr rfl; intro k hk; rw [mem_range] at hk
      congr 3; omega
    rw [hrefl]
    have hpn : p ≠ n := by omega
    have := harm_Ico (n - p) n (by omega) (by omega)
    have hl : Real.log ((n - p : ℕ) : ℝ) ≥ Real.log ((n : ℝ) - p + 1) - 1 := by
      rw [Nat.cast_sub hp]
      have hpos : (0 : ℝ) < (n : ℝ) - p := by
        have : (p : ℝ) < n := by exact_mod_cast (lt_of_le_of_ne hp hpn)
        linarith
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) - p + 1) / ((n : ℝ) - p) by positivity)
      rw [Real.log_div (by positivity) hpos.ne'] at this
      have h1np : (1 : ℝ) ≤ (n : ℝ) - p := by
        have : ((p + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : p + 1 ≤ n)
        push_cast at this; linarith
      have : ((n : ℝ) - p + 1) / ((n : ℝ) - p) - 1 ≤ 1 := by
        rw [div_sub_one hpos.ne', div_le_one hpos]
        linarith
      linarith
    linarith
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have key : ∑ k ∈ range p, 1 / (((k + 1 : ℕ) : ℝ) + 1) + ∑ k ∈ range p, 1 / (((n - k - 1 : ℕ) : ℝ) + 1) ≤
      Real.log (p + 1) + (Real.log n - Real.log (n - p + 1)) + 1 := by linarith
  calc _ = (∑ k ∈ range p, 1 / (((k + 1 : ℕ) : ℝ) + 1) + ∑ k ∈ range p, 1 / (((n - k - 1 : ℕ) : ℝ) + 1)) /
        ((n : ℝ) + 2) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right key hn2.le

end E521Q

end S_Q2

-- ===== Q5 =====
section S_Q5

/-! The conditional first-moment sum (pure real analysis, original). -/

open Finset Real

namespace E521Q

/-- `∑_{k<p} u_k p_k` with `p_k ≤ a/(k+2)` beyond `n₀` and `u_k ≤ b/(n-k)`. -/
theorem count_sum {n p n0 : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : p < n) (hn0 : n0 ≤ p)
    (pk uk : ℕ → ℝ) (hpk0 : ∀ k, 0 ≤ pk k) (hpk1 : ∀ k, pk k ≤ 1)
    (hpk : ∀ k, n0 ≤ k → pk k ≤ a / ((k : ℝ) + 2)) (huk0 : ∀ k, 0 ≤ uk k)
    (huk : ∀ k < p, uk k ≤ b / ((n : ℝ) - k)) :
    ∑ k ∈ range p, uk k * pk k ≤
      n0 * (b / ((n : ℝ) - n0)) + a * b * ((Real.log (p + 1) + (Real.log n - Real.log (n - p + 1)) + 1) / ((n : ℝ) + 2)) := by
  have hn1 : 1 ≤ n := by omega
  have hsplit : ∑ k ∈ range p, uk k * pk k =
      ∑ k ∈ range n0, uk k * pk k + ∑ k ∈ range (p - n0), uk (n0 + k) * pk (n0 + k) := by
    rw [← sum_range_add, Nat.add_sub_cancel' hn0]
  rw [hsplit]
  have h1 : ∑ k ∈ range n0, uk k * pk k ≤ n0 * (b / ((n : ℝ) - n0)) := by
    calc ∑ k ∈ range n0, uk k * pk k ≤ ∑ k ∈ range n0, b / ((n : ℝ) - n0) := by
          apply sum_le_sum; intro k hk; rw [mem_range] at hk
          have hu := huk k (by omega)
          have hnk : (0 : ℝ) < (n : ℝ) - k := by
            have : (k : ℝ) < n := by exact_mod_cast (by omega : k < n)
            linarith
          have hnn0 : (0 : ℝ) < (n : ℝ) - n0 := by
            have : (n0 : ℝ) < n := by exact_mod_cast (by omega : n0 < n)
            linarith
          have : b / ((n : ℝ) - k) ≤ b / ((n : ℝ) - n0) := by
            apply div_le_div_of_nonneg_left hb hnn0
            have : (k : ℝ) ≤ n0 := by exact_mod_cast hk.le
            linarith
          calc uk k * pk k ≤ uk k * 1 := mul_le_mul_of_nonneg_left (hpk1 k) (huk0 k)
            _ ≤ b / ((n : ℝ) - n0) := by rw [mul_one]; exact hu.trans this
      _ = n0 * (b / ((n : ℝ) - n0)) := by simp
  have h2 : ∑ k ∈ range (p - n0), uk (n0 + k) * pk (n0 + k) ≤
      a * b * ∑ k ∈ range p, 1 / (((k : ℝ) + 2) * ((n : ℝ) - k)) := by
    have : ∑ k ∈ range (p - n0), uk (n0 + k) * pk (n0 + k) ≤
        ∑ k ∈ range (p - n0), a * b * (1 / ((((n0 + k : ℕ) : ℝ) + 2) * ((n : ℝ) - (n0 + k : ℕ)))) := by
      apply sum_le_sum; intro k hk; rw [mem_range] at hk
      have hu := huk (n0 + k) (by omega)
      have hpp := hpk (n0 + k) (by omega)
      have hnk : (0 : ℝ) < (n : ℝ) - (n0 + k : ℕ) := by
        have : ((n0 + k : ℕ) : ℝ) < n := by exact_mod_cast (by omega : n0 + k < n)
        linarith
      calc uk (n0 + k) * pk (n0 + k) ≤ (b / ((n : ℝ) - (n0 + k : ℕ))) * (a / (((n0 + k : ℕ) : ℝ) + 2)) :=
            mul_le_mul hu hpp (hpk0 _) (by positivity)
        _ = a * b * (1 / ((((n0 + k : ℕ) : ℝ) + 2) * ((n : ℝ) - (n0 + k : ℕ)))) := by
            field_simp
    refine this.trans ?_
    rw [← mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hsub : ∑ k ∈ range (p - n0), 1 / ((((n0 + k : ℕ) : ℝ) + 2) * ((n : ℝ) - (n0 + k : ℕ))) =
        ∑ k ∈ Ico n0 p, 1 / (((k : ℝ) + 2) * ((n : ℝ) - k)) := by
      rw [sum_Ico_eq_sum_range]
    rw [hsub]
    apply sum_le_sum_of_subset_of_nonneg
    · intro x hx; rw [mem_Ico] at hx; rw [mem_range]; omega
    · intro k hk _
      rw [mem_range] at hk
      have : (k : ℝ) < n := by exact_mod_cast (by omega : k < n)
      have : (0 : ℝ) < (n : ℝ) - k := by linarith
      positivity
  have h3 := double_harm n p hp hn1
  have h2' := h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
  linarith

end E521Q

end S_Q5

-- ===== C19 =====
section S_C19

/-! Sharp bounds for the quadrant probability `u_L = N2 L 0 0 / 4^L` via Wallis:
`(4/π)/(L+4) ≤ u_L ≤ (4/π)/(L+1) · √(1 + 40/L)` (original). -/

open Finset Real
open scoped Nat

namespace E521

/-- normalized central binomial `b_h = C(h, ⌈h/2⌉)/2^h`. -/
noncomputable def bb (h : ℕ) : ℝ := (cc h : ℝ) / 2 ^ h

lemma cb_wallis (k : ℕ) :
    (Nat.centralBinom k : ℝ) ^ 2 * (2 * k + 1) = 16 ^ k / Real.Wallis.W k := by
  rw [Real.Wallis.W_eq_factorial_ratio, Nat.centralBinom_eq_two_mul_choose,
    Nat.cast_choose ℝ (show k ≤ 2 * k by omega)]
  have h1 : (2 * k - k) = k := by omega
  rw [h1]
  have hf : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  have hf2 : (0 : ℝ) < (2 * k)! := by exact_mod_cast Nat.factorial_pos (2 * k)
  rw [show (16 : ℝ) ^ k = 2 ^ (4 * k) by rw [pow_mul]; norm_num]
  field_simp

lemma cb_sq_lower (k : ℕ) : (2 / π) * 16 ^ k ≤ (Nat.centralBinom k : ℝ) ^ 2 * (2 * k + 1) := by
  rw [cb_wallis]
  have hW := Real.Wallis.W_le k
  have hW0 := Real.Wallis.W_pos k
  rw [le_div_iff₀ hW0]
  have : (2 / π) * 16 ^ k * Real.Wallis.W k ≤ (2 / π) * 16 ^ k * (π / 2) := by (gcongr)
  have e : (2 / π) * 16 ^ k * (π / 2) = (16 : ℝ) ^ k := by field_simp
  linarith

lemma cb_sq_upper (k : ℕ) :
    (Nat.centralBinom k : ℝ) ^ 2 * (2 * k + 1) ^ 2 ≤ (2 / π) * 16 ^ k * (2 * k + 2) := by
  have h := cb_wallis k
  have hW := Real.Wallis.le_W k
  have hW0 := Real.Wallis.W_pos k
  have hk : (0 : ℝ) < 2 * k + 1 := by positivity
  have e : (Nat.centralBinom k : ℝ) ^ 2 * (2 * k + 1) ^ 2 = 16 ^ k / Real.Wallis.W k * (2 * k + 1) := by
    rw [← h]; ring
  rw [e, div_mul_eq_mul_div, div_le_iff₀ hW0]
  have : (2 / π) * 16 ^ k * (2 * k + 2) * (((2 : ℝ) * k + 1) / (2 * k + 2) * (π / 2)) ≤
      (2 / π) * 16 ^ k * (2 * k + 2) * Real.Wallis.W k := by (gcongr)
  have e2 : (2 / π) * 16 ^ k * (2 * k + 2) * (((2 : ℝ) * k + 1) / (2 * k + 2) * (π / 2)) =
      16 ^ k * (2 * k + 1) := by field_simp
  linarith

lemma bb_sq_bounds (h : ℕ) :
    (2 / π) / (h + 2) ≤ bb h ^ 2 ∧ bb h ^ 2 ≤ (2 / π) * (h + 2) / (h + 1) ^ 2 := by
  have hpi := Real.pi_pos
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' h
  · -- h = 2k
    unfold bb; rw [cc_even, div_pow]
    have h2 : ((2 : ℝ) ^ (2 * k)) ^ 2 = 16 ^ k := by
      rw [← pow_mul, show 2 * k * 2 = 4 * k by ring, pow_mul]; norm_num
    rw [h2]
    have l := cb_sq_lower k
    have u := cb_sq_upper k
    push_cast
    constructor
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
  · -- h = 2k+1: bb h = c_{k+1}/4^{k+1}
    unfold bb; rw [cc_odd, div_pow]
    have h2 : ((Nat.centralBinom (k + 1) : ℝ) / 2) ^ 2 / ((2 : ℝ) ^ (2 * k + 1)) ^ 2 =
        (Nat.centralBinom (k + 1) : ℝ) ^ 2 / 16 ^ (k + 1) := by
      rw [div_pow, div_div]; congr 1
      rw [← pow_mul, ← pow_add, show 2 + (2 * k + 1) * 2 = 4 * (k + 1) by ring, pow_mul]; norm_num
    rw [h2]
    have l := cb_sq_lower (k + 1)
    have u := cb_sq_upper (k + 1)
    push_cast at l u ⊢
    constructor
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hk0 := Nat.cast_nonneg (α := ℝ) k
      -- (2k+3)^{-2}(2k+4) ≤ (2k+3)(2k+2)^{-2}: use (h+3)(h+1)^2 ≤ (h+2)^3
      have key : (2 * (k : ℝ) + 4) * (2 * k + 2) ^ 2 ≤ (2 * k + 3) ^ 3 := by nlinarith
      nlinarith [sq_nonneg ((Nat.centralBinom (k + 1) : ℝ)), key,
        mul_le_mul_of_nonneg_left key (by positivity : (0:ℝ) ≤ (2 / π) * 16 ^ (k + 1))]

lemma bb_nonneg (h : ℕ) : 0 ≤ bb h := by unfold bb; positivity

lemma u_eq (L : ℕ) : (N2 L 0 0 : ℝ) / 4 ^ L =
    ∑ h ∈ range (L + 1), (L.choose h : ℝ) / 2 ^ L * (bb h * bb (L - h)) := by
  rw [N2_origin', sum_div]
  apply sum_congr rfl; intro h hh; rw [mem_range] at hh
  unfold bb
  have : (4 : ℝ) ^ L = 2 ^ L * (2 ^ h * 2 ^ (L - h)) := by
    rw [← pow_add, ← pow_add, show h + (L - h) = L by omega, ← two_mul, pow_mul]; norm_num
  rw [this]; field_simp

/-- **lower bound** `u_L ≥ (4/π)/(L+4)`. -/
theorem u_lower (L : ℕ) : (4 / π) / (L + 4) ≤ (N2 L 0 0 : ℝ) / 4 ^ L := by
  rw [u_eq]
  have each : ∀ h ∈ range (L + 1), (L.choose h : ℝ) / 2 ^ L * ((4 / π) / (L + 4)) ≤
      (L.choose h : ℝ) / 2 ^ L * (bb h * bb (L - h)) := by
    intro h hh; rw [mem_range] at hh
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have a := (bb_sq_bounds h).1
    have b := (bb_sq_bounds (L - h)).1
    have hLh : ((L - h : ℕ) : ℝ) = L - h := by rw [Nat.cast_sub (by omega)]
    rw [hLh] at b
    have hx := bb_nonneg h
    have hy := bb_nonneg (L - h)
    have hpi := Real.pi_pos
    have hh0 : (0 : ℝ) ≤ h := by positivity
    have hhL : (h : ℝ) ≤ L := by exact_mod_cast (show h ≤ L by omega)
    -- (bb h bb(L-h))^2 ≥ (2/π)^2/((h+2)(L-h+2)) ≥ (4/π)^2/(L+4)^2
    have amgm : 4 * ((h : ℝ) + 2) * (L - h + 2) ≤ (L + 4) ^ 2 := by
      nlinarith [sq_nonneg (((h : ℝ) + 2) - (L - h + 2))]
    have sq : ((4 / π) / (L + 4)) ^ 2 ≤ (bb h * bb (L - h)) ^ 2 := by
      rw [mul_pow]
      have := mul_le_mul a b (by positivity) (by positivity)
      refine le_trans ?_ this
      rw [div_pow, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (4 / π) ^ 2 = 4 * (2 / π * (2 / π)) := by ring
      rw [this]
      nlinarith [mul_pos hpi hpi, sq_nonneg (2 / π)]
    exact (pow_le_pow_iff_left₀ (by positivity) (mul_nonneg hx hy) two_ne_zero).mp sq
  have := sum_le_sum each
  rw [← sum_mul] at this
  have hs : ∑ h ∈ range (L + 1), (L.choose h : ℝ) / 2 ^ L = 1 := by
    rw [← sum_div]
    have : ∑ h ∈ range (L + 1), (L.choose h : ℝ) = 2 ^ L := by exact_mod_cast Nat.sum_range_choose L
    rw [this]; exact div_self (by positivity)
  rw [hs, one_mul] at this
  exact this

end E521

end S_C19

-- ===== C20 =====
section S_C20

/-! Upper bound `u_L ≤ (4/π)/(L+1) · √(1 + 24/(L+1))` (original). -/

open Finset Real
open scoped Nat

namespace E521

lemma row_partial (n M r : ℕ) : ∑ h ∈ range M, ((n.choose (h + r) : ℕ) : ℝ) ≤ 2 ^ n := by
  have h1 : ∑ h ∈ range M, ((n.choose (h + r) : ℕ) : ℝ) ≤ ∑ j ∈ range (M + r), ((n.choose j : ℕ) : ℝ) := by
    rw [sum_range_add_sum_Ico _ (show r ≤ M + r by omega) |>.symm]
    have : ∑ h ∈ range M, ((n.choose (h + r) : ℕ) : ℝ) = ∑ j ∈ Ico r (M + r), ((n.choose j : ℕ) : ℝ) := by
      rw [sum_Ico_eq_sum_range]; apply sum_congr (by congr 1; omega); intro h _; rw [add_comm]
    rw [this]
    have : 0 ≤ ∑ j ∈ range r, ((n.choose j : ℕ) : ℝ) := sum_nonneg (fun _ _ => by positivity)
    linarith
  refine h1.trans ?_
  have h2 : ∀ K, ∑ j ∈ range K, ((n.choose j : ℕ) : ℝ) ≤ 2 ^ n := by
    intro K
    rcases le_or_gt K (n + 1) with hK | hK
    · calc ∑ j ∈ range K, ((n.choose j : ℕ) : ℝ) ≤ ∑ j ∈ range (n + 1), ((n.choose j : ℕ) : ℝ) :=
            sum_le_sum_of_subset_of_nonneg (fun x hx => by rw [mem_range] at hx ⊢; omega)
              (fun _ _ _ => by positivity)
        _ = 2 ^ n := by exact_mod_cast Nat.sum_range_choose n
    · rw [show K = (n + 1) + (K - (n + 1)) by omega, sum_range_add]
      have : ∑ j ∈ range (K - (n + 1)), ((n.choose (n + 1 + j) : ℕ) : ℝ) = 0 := by
        apply sum_eq_zero; intro j _; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
      rw [this, add_zero]
      exact_mod_cast (Nat.sum_range_choose n).le
  exact h2 _

lemma choose_id2 (L h : ℕ) (hh : h ≤ L) :
    (L.choose h : ℝ) * ((L + 1) * (L + 2)) = ((L + 2).choose (h + 1) : ℝ) * ((h + 1) * (L - h + 1)) := by
  have hA := Nat.choose_mul_factorial_mul_factorial hh
  have hB := Nat.choose_mul_factorial_mul_factorial (show h + 1 ≤ L + 2 by omega)
  rw [show L + 2 - (h + 1) = (L - h) + 1 by omega, Nat.factorial_succ h, Nat.factorial_succ (L - h),
    Nat.factorial_succ (L + 1), Nat.factorial_succ L] at hB
  have hA' := congrArg (fun x : ℕ => (x : ℝ)) hA
  have hB' := congrArg (fun x : ℕ => (x : ℝ)) hB
  push_cast [Nat.cast_sub hh] at hA' hB'
  apply mul_right_cancel₀ (show ((h ! : ℕ) : ℝ) * ((L - h)! : ℕ) ≠ 0 by positivity)
  linear_combination ((L : ℝ) + 1) * ((L : ℝ) + 2) * hA' - hB'

lemma choose_id3 (L h : ℕ) (hh : h ≤ L) :
    (L.choose h : ℝ) * ((L + 1) * (L + 2) * (L + 3)) =
      ((L + 3).choose (h + 1) : ℝ) * ((h + 1) * (L - h + 1) * (L - h + 2)) := by
  have hA := Nat.choose_mul_factorial_mul_factorial hh
  have hB := Nat.choose_mul_factorial_mul_factorial (show h + 1 ≤ L + 3 by omega)
  rw [show L + 3 - (h + 1) = (L - h) + 1 + 1 by omega, Nat.factorial_succ h, Nat.factorial_succ (L - h + 1),
    Nat.factorial_succ (L - h), Nat.factorial_succ (L + 2),
    Nat.factorial_succ (L + 1), Nat.factorial_succ L] at hB
  have hA' := congrArg (fun x : ℕ => (x : ℝ)) hA
  have hB' := congrArg (fun x : ℕ => (x : ℝ)) hB
  push_cast [Nat.cast_sub hh] at hA' hB'
  apply mul_right_cancel₀ (show ((h ! : ℕ) : ℝ) * ((L - h)! : ℕ) ≠ 0 by positivity)
  linear_combination ((L : ℝ) + 1) * ((L : ℝ) + 2) * ((L : ℝ) + 3) * hA' - hB'

lemma choose_id4 (L h : ℕ) (hh : h ≤ L) :
    (L.choose h : ℝ) * ((L + 1) * (L + 2) * (L + 3) * (L + 4)) =
      ((L + 4).choose (h + 2) : ℝ) * ((h + 1) * (h + 2) * (L - h + 1) * (L - h + 2)) := by
  have hA := Nat.choose_mul_factorial_mul_factorial hh
  have hB := Nat.choose_mul_factorial_mul_factorial (show h + 2 ≤ L + 4 by omega)
  rw [show L + 4 - (h + 2) = (L - h) + 1 + 1 by omega, Nat.factorial_succ (h + 1), Nat.factorial_succ h, Nat.factorial_succ (L - h + 1),
    Nat.factorial_succ (L - h), Nat.factorial_succ (L + 3),
    Nat.factorial_succ (L + 2),
    Nat.factorial_succ (L + 1), Nat.factorial_succ L] at hB
  have hA' := congrArg (fun x : ℕ => (x : ℝ)) hA
  have hB' := congrArg (fun x : ℕ => (x : ℝ)) hB
  push_cast [Nat.cast_sub hh] at hA' hB'
  apply mul_right_cancel₀ (show ((h ! : ℕ) : ℝ) * ((L - h)! : ℕ) ≠ 0 by positivity)
  linear_combination ((L : ℝ) + 1) * ((L : ℝ) + 2) * ((L : ℝ) + 3) * ((L : ℝ) + 4) * hA' - hB'

lemma choose_id3' (L h : ℕ) (hh : h ≤ L) :
    (L.choose h : ℝ) * ((L + 1) * (L + 2) * (L + 3)) =
      ((L + 3).choose (h + 2) : ℝ) * ((h + 1) * (h + 2) * (L - h + 1)) := by
  have hA := Nat.choose_mul_factorial_mul_factorial hh
  have hB := Nat.choose_mul_factorial_mul_factorial (show h + 2 ≤ L + 3 by omega)
  rw [show L + 3 - (h + 2) = (L - h) + 1 by omega, Nat.factorial_succ (h + 1), Nat.factorial_succ h, Nat.factorial_succ (L - h),
    Nat.factorial_succ (L + 2),
    Nat.factorial_succ (L + 1), Nat.factorial_succ L] at hB
  have hA' := congrArg (fun x : ℕ => (x : ℝ)) hA
  have hB' := congrArg (fun x : ℕ => (x : ℝ)) hB
  push_cast [Nat.cast_sub hh] at hA' hB'
  apply mul_right_cancel₀ (show ((h ! : ℕ) : ℝ) * ((L - h)! : ℕ) ≠ 0 by positivity)
  linear_combination ((L : ℝ) + 1) * ((L : ℝ) + 2) * ((L : ℝ) + 3) * hA' - hB'

lemma term_num {c c2 c3 c3' c4 A B P2 P3 P4 : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hc : 0 ≤ c)
    (hP2 : 0 < P2) (hP3 : 0 < P3) (hP4 : 0 < P4)
    (I2 : c * P2 = c2 * (A * B)) (I3 : c * P3 = c3 * (A * B * (B + 1)))
    (I3' : c * P3 = c3' * (A * (A + 1) * B)) (I4 : c * P4 = c4 * (A * (A + 1) * B * (B + 1))) :
    c * ((A + 1) * (B + 1) / (A ^ 2 * B ^ 2)) ≤ c2 / P2 + 2 * c3 / P3 + 2 * c3' / P3 + 4 * c4 / P4 := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have e : c * ((A + 1) * (B + 1) / (A ^ 2 * B ^ 2)) =
      c / (A * B) + c / (A * B ^ 2) + c / (A ^ 2 * B) + c / (A ^ 2 * B ^ 2) := by
    field_simp; ring
  rw [e]
  have t1 : c / (A * B) = c2 / P2 := by
    rw [div_eq_div_iff (by positivity) hP2.ne']; linarith
  have hAB0 : 0 < A * B := mul_pos hA0 hB0
  have t2 : c / (A * B ^ 2) ≤ 2 * c3 / P3 := by
    have e2 : 2 * c3 / P3 = 2 * c / (A * B * (B + 1)) := by
      rw [div_eq_div_iff hP3.ne' (by positivity)]; linarith [I3]
    rw [e2, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hc (mul_nonneg hAB0.le (sub_nonneg.mpr hB))]
  have t3 : c / (A ^ 2 * B) ≤ 2 * c3' / P3 := by
    have e3 : 2 * c3' / P3 = 2 * c / (A * (A + 1) * B) := by
      rw [div_eq_div_iff hP3.ne' (by positivity)]; linarith [I3']
    rw [e3, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hc (mul_nonneg hAB0.le (sub_nonneg.mpr hA))]
  have t4 : c / (A ^ 2 * B ^ 2) ≤ 4 * c4 / P4 := by
    have e4 : 4 * c4 / P4 = 4 * c / (A * (A + 1) * B * (B + 1)) := by
      rw [div_eq_div_iff hP4.ne' (by positivity)]; linarith [I4]
    rw [e4, div_le_div_iff₀ (by positivity) (by positivity)]
    have hq : (A + 1) * (B + 1) ≤ 4 * (A * B) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)]
    have := mul_le_mul_of_nonneg_left hq (mul_nonneg hc hAB0.le)
    nlinarith
  linarith

/-- **upper bound** for `u_L`. -/
theorem u_upper (L : ℕ) :
    (N2 L 0 0 : ℝ) / 4 ^ L ≤ (4 / π) / (L + 1) * √(1 + 24 / (L + 1)) := by
  rw [u_eq]
  have hpi := Real.pi_pos
  set w : ℕ → ℝ := fun h => (L.choose h : ℝ) / 2 ^ L with hw
  have hw0 : ∀ h, 0 ≤ w h := fun h => by simp only [hw]; positivity
  have hwsum : ∑ h ∈ range (L + 1), w h = 1 := by
    simp only [hw]; rw [← sum_div]
    have : ∑ h ∈ range (L + 1), (L.choose h : ℝ) = 2 ^ L := by exact_mod_cast Nat.sum_range_choose L
    rw [this]; exact div_self (by positivity)
  -- R h = (h+2)(L-h+2)/((h+1)^2 (L-h+1)^2)
  set Rf : ℕ → ℝ := fun h => ((h : ℝ) + 2) * (L - h + 2) / (((h : ℝ) + 1) ^ 2 * (L - h + 1) ^ 2) with hRf
  have hbb : ∀ h ∈ range (L + 1), bb h * bb (L - h) ≤ (2 / π) * √(Rf h) := by
    intro h hh; rw [mem_range] at hh
    have a := (bb_sq_bounds h).2
    have b := (bb_sq_bounds (L - h)).2
    have hLh : ((L - h : ℕ) : ℝ) = L - h := by rw [Nat.cast_sub (by omega)]
    rw [hLh] at b
    have hh1 : (h : ℝ) ≤ L := by exact_mod_cast (show h ≤ L by omega)
    have sq : (bb h * bb (L - h)) ^ 2 ≤ ((2 / π) * √(Rf h)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by simp only [hRf]; apply div_nonneg <;> nlinarith)]
      have := mul_le_mul a b (by positivity) (by positivity)
      refine this.trans (le_of_eq ?_)
      simp only [hRf]; field_simp
    exact (pow_le_pow_iff_left₀ (mul_nonneg (bb_nonneg _) (bb_nonneg _)) (by positivity)
      two_ne_zero).mp sq
  -- Cauchy–Schwarz: ∑ w √R ≤ √(∑ w R)
  have hCS : ∑ h ∈ range (L + 1), w h * √(Rf h) ≤ √(∑ h ∈ range (L + 1), w h * Rf h) := by
    apply Real.le_sqrt_of_sq_le
    have key := Finset.sum_mul_sq_le_sq_mul_sq (range (L + 1)) (fun h => √(w h)) (fun h => √(w h) * √(Rf h))
    have e1 : ∑ h ∈ range (L + 1), √(w h) * (√(w h) * √(Rf h)) = ∑ h ∈ range (L + 1), w h * √(Rf h) := by
      apply sum_congr rfl; intro h _; rw [← mul_assoc, Real.mul_self_sqrt (hw0 h)]
    have e2 : ∑ h ∈ range (L + 1), √(w h) ^ 2 = 1 := by
      rw [← hwsum]; apply sum_congr rfl; intro h _; rw [Real.sq_sqrt (hw0 h)]
    have e3 : ∑ h ∈ range (L + 1), (√(w h) * √(Rf h)) ^ 2 ≤ ∑ h ∈ range (L + 1), w h * Rf h := by
      apply sum_le_sum; intro h hh; rw [mem_range] at hh
      have hh1 : (h : ℝ) ≤ L := by exact_mod_cast (show h ≤ L by omega)
      have hR0 : 0 ≤ Rf h := by simp only [hRf]; apply div_nonneg <;> nlinarith
      rw [mul_pow, Real.sq_sqrt (hw0 h), Real.sq_sqrt hR0]
    rw [e1, e2, one_mul] at key
    linarith
  -- the moment bound ∑ w R ≤ 4/((L+1)(L+2)) (1 + 24/(L+3))
  have hER : ∑ h ∈ range (L + 1), w h * Rf h ≤ 4 / ((L + 1 : ℝ) ^ 2) * (1 + 24 / (L + 1)) := by
    have per : ∀ h ∈ range (L + 1), w h * Rf h ≤
        (((L + 2).choose (h + 1) : ℝ) / ((L + 1) * (L + 2)) +
         2 * ((L + 3).choose (h + 1) : ℝ) / ((L + 1) * (L + 2) * (L + 3)) +
         2 * ((L + 3).choose (h + 2) : ℝ) / ((L + 1) * (L + 2) * (L + 3)) +
         4 * ((L + 4).choose (h + 2) : ℝ) / ((L + 1) * (L + 2) * (L + 3) * (L + 4))) / 2 ^ L := by
      intro h hh; rw [mem_range] at hh
      have hhL : h ≤ L := by omega
      have hh1 : (h : ℝ) ≤ L := by exact_mod_cast hhL
      have e : w h * Rf h = ((L.choose h : ℝ) * ((((h : ℝ) + 1) + 1) * ((L - h + 1) + 1) /
          (((h : ℝ) + 1) ^ 2 * (L - h + 1) ^ 2))) / 2 ^ L := by
        simp only [hw, hRf]; ring_nf
      rw [e]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have := term_num (c := (L.choose h : ℝ)) (A := (h : ℝ) + 1) (B := (L : ℝ) - h + 1)
        (P2 := ((L : ℝ) + 1) * (L + 2)) (P3 := ((L : ℝ) + 1) * (L + 2) * (L + 3))
        (P4 := ((L : ℝ) + 1) * (L + 2) * (L + 3) * (L + 4))
        (by linarith [Nat.cast_nonneg (α := ℝ) h]) (by linarith) (by positivity)
        (by positivity) (by positivity) (by positivity)
        (choose_id2 L h hhL) (by rw [choose_id3 L h hhL]; ring) (by rw [choose_id3' L h hhL]; ring)
        (by rw [choose_id4 L h hhL]; ring)
      exact this
    refine (sum_le_sum per).trans ?_
    rw [← sum_div, sum_add_distrib, sum_add_distrib, sum_add_distrib, ← sum_div, ← sum_div, ← mul_sum,
      ← sum_div, ← mul_sum, ← sum_div, ← mul_sum]
    have s1 := row_partial (L + 2) (L + 1) 1
    have s2 := row_partial (L + 3) (L + 1) 1
    have s3 := row_partial (L + 3) (L + 1) 2
    have s4 := row_partial (L + 4) (L + 1) 2
    push_cast at s1 s2 s3 s4
    have hL0 : (0 : ℝ) ≤ L := by positivity
    have h2L : (0 : ℝ) < 2 ^ L := by positivity
    rw [div_le_iff₀ h2L]
    have b1 : (∑ h ∈ range (L + 1), ((L + 2).choose (h + 1) : ℝ)) / ((L + 1) * (L + 2)) ≤
        2 ^ (L + 2) / ((L + 1) * (L + 2)) := by (gcongr)
    have b2 : 2 * (∑ h ∈ range (L + 1), ((L + 3).choose (h + 1) : ℝ)) / ((L + 1) * (L + 2) * (L + 3)) ≤
        2 * 2 ^ (L + 3) / ((L + 1) * (L + 2) * (L + 3)) := by (gcongr)
    have b3 : 2 * (∑ h ∈ range (L + 1), ((L + 3).choose (h + 2) : ℝ)) / ((L + 1) * (L + 2) * (L + 3)) ≤
        2 * 2 ^ (L + 3) / ((L + 1) * (L + 2) * (L + 3)) := by (gcongr)
    have b4 : 4 * (∑ h ∈ range (L + 1), ((L + 4).choose (h + 2) : ℝ)) / ((L + 1) * (L + 2) * (L + 3) * (L + 4)) ≤
        4 * 2 ^ (L + 4) / ((L + 1) * (L + 2) * (L + 3) * (L + 4)) := by (gcongr)
    have fin : 2 ^ (L + 2) / ((L + 1 : ℝ) * (L + 2)) + 2 * 2 ^ (L + 3) / ((L + 1) * (L + 2) * (L + 3)) +
        2 * 2 ^ (L + 3) / ((L + 1) * (L + 2) * (L + 3)) + 4 * 2 ^ (L + 4) / ((L + 1) * (L + 2) * (L + 3) * (L + 4))
        ≤ 4 / ((L + 1 : ℝ) ^ 2) * (1 + 24 / (L + 1)) * 2 ^ L := by
      rw [pow_add, pow_add, pow_add]
      have : (2 : ℝ) ^ L * 2 ^ 2 / ((L + 1) * (L + 2)) + 2 * (2 ^ L * 2 ^ 3) / ((L + 1) * (L + 2) * (L + 3)) +
          2 * (2 ^ L * 2 ^ 3) / ((L + 1) * (L + 2) * (L + 3)) + 4 * (2 ^ L * 2 ^ 4) / ((L + 1) * (L + 2) * (L + 3) * (L + 4))
          = 2 ^ L * (4 / ((L + 1) * (L + 2)) + 32 / ((L + 1) * (L + 2) * (L + 3)) +
            64 / ((L + 1) * (L + 2) * (L + 3) * (L + 4))) := by ring
      rw [this, mul_comm]
      apply mul_le_mul_of_nonneg_right _ h2L.le
      rw [div_add_div _ _ (by positivity) (by positivity), div_add_div _ _ (by positivity) (by positivity),
        div_le_iff₀ (by positivity)]
      field_simp
      nlinarith [mul_nonneg hL0 hL0, mul_nonneg (mul_nonneg hL0 hL0) hL0,
        mul_nonneg (mul_nonneg (mul_nonneg hL0 hL0) hL0) hL0]
    linarith
  have hfin : ∑ h ∈ range (L + 1), w h * (bb h * bb (L - h)) ≤
      (2 / π) * √(4 / ((L + 1 : ℝ) ^ 2) * (1 + 24 / (L + 1))) := by
    calc ∑ h ∈ range (L + 1), w h * (bb h * bb (L - h))
        ≤ ∑ h ∈ range (L + 1), w h * ((2 / π) * √(Rf h)) :=
          sum_le_sum (fun h hh => mul_le_mul_of_nonneg_left (hbb h hh) (hw0 h))
      _ = (2 / π) * ∑ h ∈ range (L + 1), w h * √(Rf h) := by
          rw [mul_sum]; apply sum_congr rfl; intro h _; ring
      _ ≤ (2 / π) * √(∑ h ∈ range (L + 1), w h * Rf h) := by (gcongr)
      _ ≤ (2 / π) * √(4 / ((L + 1 : ℝ) ^ 2) * (1 + 24 / (L + 1))) := by (gcongr)
  refine hfin.trans (le_of_eq ?_)
  rw [Real.sqrt_mul (by positivity), show (4 : ℝ) / (L + 1) ^ 2 = (2 / (L + 1)) ^ 2 by rw [div_pow]; norm_num,
    Real.sqrt_sq (by positivity)]
  ring

end E521

end S_C20

-- ===== C21 =====
section S_C21

/-! Endpoint estimates for the quadrant walk (original). -/

open Finset Real

namespace E521

lemma N1F_parity (h : ℕ) : ∀ (u y : ℤ), N1F (· = y) h u ≠ 0 → Even (u + h - y) := by
  induction h with
  | zero =>
    intro u y hne
    rw [N1F_zero] at hne
    split_ifs at hne with hc
    · rw [hc.2]; simp
    · exact absurd rfl hne
  | succ h ih =>
    intro u y hne
    by_cases hu : 0 ≤ u
    · rw [N1F_succ _ h hu] at hne
      rcases Nat.eq_zero_or_pos (N1F (· = y) h (u + 1)) with h1 | h1
      · rw [h1, zero_add] at hne
        have := ih (u - 1) y hne
        have e : u + ((h + 1 : ℕ) : ℤ) - y = (u - 1 + h - y) + 2 := by push_cast; ring
        rw [e]; exact this.add (by decide)
      · have := ih (u + 1) y (by omega)
        have e : u + ((h + 1 : ℕ) : ℤ) - y = u + 1 + h - y := by push_cast; ring
        rw [e]; exact this
    · exact absurd (N1F_neg _ _ (not_le.mp hu)) hne

lemma N1F_true (L : ℕ) : ∀ u : ℤ, N1F (fun _ => True) L u = N1 L u := by
  induction L with
  | zero =>
    intro u; rw [N1F_zero]
    unfold N1
    by_cases hu : 0 ≤ u
    · rw [if_pos ⟨hu, trivial⟩]
      rw [eq_comm, card_eq_one]; refine ⟨default, ?_⟩
      ext p
      have hp : p = default := Subsingleton.elim _ _
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · intro _; exact hp
      · intro _; first | exact hu | simp [good1, hu] | (simp only [Set.mem_setOf_eq]; simp [good1, hu])
    · rw [if_neg (fun h : 0 ≤ u ∧ _ => hu h.1)]
      have := N1_neg 0 (not_le.mp hu); unfold N1 at this; rw [this]
  | succ L ih =>
    intro u
    by_cases hu : 0 ≤ u
    · rw [N1F_succ _ L hu, N1_succ L hu, ih, ih]
    · rw [N1F_neg _ _ (not_le.mp hu), N1_neg _ (not_le.mp hu)]

lemma N1F_sum (S : Finset ℤ) (L : ℕ) : ∀ u : ℤ,
    N1F (· ∈ S) L u = ∑ y ∈ S, N1F (· = y) L u := by
  induction L with
  | zero =>
    intro u
    rw [N1F_zero]
    simp_rw [N1F_zero]
    by_cases hu : 0 ≤ u
    · by_cases huS : u ∈ S
      · rw [if_pos ⟨hu, huS⟩, sum_eq_single u]
        · rw [if_pos ⟨hu, rfl⟩]
        · intro y _ hy; rw [if_neg (fun h : 0 ≤ u ∧ u = y => hy h.2.symm)]
        · intro h; exact absurd huS h
      · rw [if_neg (fun h => huS h.2)]
        symm; apply sum_eq_zero; intro y hy
        rw [if_neg (fun h : 0 ≤ u ∧ u = y => huS (by rw [h.2]; exact hy))]
    · rw [if_neg (fun h : 0 ≤ u ∧ _ => hu h.1)]
      symm; apply sum_eq_zero; intro y _; rw [if_neg (fun h : 0 ≤ u ∧ u = y => hu h.1)]
  | succ L ih =>
    intro u
    by_cases hu : 0 ≤ u
    · rw [N1F_succ _ L hu, ih, ih]
      simp_rw [N1F_succ _ L hu]
      rw [sum_add_distrib]
    · rw [N1F_neg _ _ (not_le.mp hu)]
      symm; apply sum_eq_zero; intro y _; exact N1F_neg _ _ (not_le.mp hu)

lemma choose_le_cc (h k : ℕ) : h.choose k ≤ cc h := by
  unfold cc
  have h1 := Nat.choose_le_middle k h
  have h2 : h.choose ((h + 1) / 2) = h.choose (h / 2) := by
    rcases Nat.even_or_odd' h with ⟨p, rfl | rfl⟩
    · congr 1; omega
    · rw [show (2 * p + 1 + 1) / 2 = p + 1 by omega, show (2 * p + 1) / 2 = p by omega]
      exact Nat.choose_symm_of_eq_add (by omega)
  rw [h2]; exact h1

/-- endpoint (ballot) bound from the origin: `N1F(·=y) h 0 · (h+2) ≤ 2 (y+1) cc h`. -/
lemma endpoint_bound (h y : ℕ) :
    (N1F (· = (y : ℤ)) h 0 : ℝ) * (h + 2) ≤ 2 * (y + 1) * cc h := by
  by_cases hne : N1F (· = (y : ℤ)) h 0 = 0
  · rw [hne]; simp; positivity
  have hpar := N1F_parity h 0 y hne
  obtain ⟨r, hr⟩ := hpar
  -- k = (h + y)/2
  have hk : ((h : ℤ) + y) = 2 * (y + r) := by omega
  set k : ℤ := y + r with hk_def
  have hy : (0 : ℤ) ≤ ((0 : ℕ) : ℤ) + 2 * k - h := by push_cast; omega
  have hb := ballot h 0 k hy
  have hfin : ((0 : ℕ) : ℤ) + 2 * k - h = (y : ℤ) := by push_cast; omega
  rw [hfin] at hb
  -- k ≥ 0, k ≤ h
  have hk0 : 0 ≤ k := by omega
  have hkn : k.toNat ≤ h ∨ h < k.toNat := le_or_gt _ _
  push_cast at hb
  simp only [add_zero] at hb
  have hchZ1 : chZ h k = (h.choose k.toNat : ℤ) := by unfold chZ; rw [if_neg (by omega)]
  have hchZ2 : chZ h (k + 1) = (h.choose (k.toNat + 1) : ℤ) := by
    unfold chZ; rw [if_neg (by omega)]; congr 2; omega
  rw [hchZ1, hchZ2] at hb
  have hid := Nat.choose_succ_right_eq h k.toNat
  -- (k+1)(C(h,k) - C(h,k+1)) = C(h,k)(2k+1-h) = C(h,k)(y+1)
  have hN : (N1F (· = (y : ℤ)) h 0 : ℝ) = (h.choose k.toNat : ℝ) - h.choose (k.toNat + 1) := by
    exact_mod_cast hb
  have hktn : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk0
  have hkr : 2 * (k : ℝ) = h + y := by exact_mod_cast (show 2 * k = (h : ℤ) + y by omega)
  have hidr : ((h.choose (k.toNat + 1) : ℕ) : ℝ) * (k + 1) = (h.choose k.toNat : ℝ) * (h - k) := by
    have : ((h.choose (k.toNat + 1) * (k.toNat + 1) : ℕ) : ℝ) = ((h.choose k.toNat * (h - k.toNat) : ℕ) : ℝ) := by
      exact_mod_cast hid
    push_cast at this
    by_cases hkh : k.toNat ≤ h
    · rw [Nat.cast_sub hkh, hktn] at this; linarith
    · have hz : h.choose k.toNat = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have hz2 : h.choose (k.toNat + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hz, hz2]; simp
  have key : (N1F (· = (y : ℤ)) h 0 : ℝ) * (k + 1) = (h.choose k.toNat : ℝ) * (y + 1) := by
    rw [hN, sub_mul, hidr]; nlinarith
  have hC := choose_le_cc h k.toNat
  have hCr : (h.choose k.toNat : ℝ) ≤ cc h := by exact_mod_cast hC
  have hk1 : ((h : ℝ) + 2) ≤ 2 * (k + 1) := by linarith [show (0:ℝ) ≤ y by positivity]
  have hN0 : (0 : ℝ) ≤ N1F (· = (y : ℤ)) h 0 := by positivity
  calc (N1F (· = (y : ℤ)) h 0 : ℝ) * (h + 2) ≤ (N1F (· = (y : ℤ)) h 0 : ℝ) * (2 * (k + 1)) :=
        mul_le_mul_of_nonneg_left hk1 hN0
    _ = 2 * ((h.choose k.toNat : ℝ) * (y + 1)) := by rw [← key]; ring
    _ ≤ 2 * (cc h * (y + 1)) := by (gcongr)
    _ = 2 * (y + 1) * cc h := by ring

end E521

end S_C21

-- ===== C22 =====
section S_C22

/-! The quadrant walk rarely ends near an axis (original). -/

open Finset Real
open scoped Nat

namespace E521

lemma N1F_or (F G : ℤ → Prop) [DecidablePred F] [DecidablePred G] (hdis : ∀ y, ¬ (F y ∧ G y)) (L : ℕ) :
    ∀ u : ℤ, N1F (fun y => F y ∨ G y) L u = N1F F L u + N1F G L u := by
  induction L with
  | zero =>
    intro u
    rw [N1F_zero, N1F_zero, N1F_zero]
    by_cases hu : 0 ≤ u
    · by_cases hF : F u
      · rw [if_pos ⟨hu, Or.inl hF⟩, if_pos ⟨hu, hF⟩, if_neg (fun h : 0 ≤ u ∧ G u => hdis u ⟨hF, h.2⟩)]
      · by_cases hG : G u
        · rw [if_pos ⟨hu, Or.inr hG⟩, if_neg (fun h : 0 ≤ u ∧ F u => hF h.2), if_pos ⟨hu, hG⟩]
        · rw [if_neg (fun h : 0 ≤ u ∧ (F u ∨ G u) => h.2.elim hF hG), if_neg (fun h : 0 ≤ u ∧ F u => hF h.2), if_neg (fun h : 0 ≤ u ∧ G u => hG h.2)]
    · rw [if_neg (fun h : 0 ≤ u ∧ _ => hu h.1), if_neg (fun h : 0 ≤ u ∧ _ => hu h.1), if_neg (fun h : 0 ≤ u ∧ _ => hu h.1)]
  | succ L ih =>
    intro u
    by_cases hu : 0 ≤ u
    · rw [N1F_succ _ L hu, N1F_succ _ L hu, N1F_succ _ L hu, ih, ih]; ring
    · rw [N1F_neg _ _ (not_le.mp hu), N1F_neg _ _ (not_le.mp hu), N1F_neg _ _ (not_le.mp hu)]

lemma choose_id3b (L h : ℕ) (hh : h ≤ L) :
    (L.choose h : ℝ) * ((L + 1) * (L + 2) * (L + 3)) =
      ((L + 3).choose (h + 3) : ℝ) * ((h + 1) * (h + 2) * (h + 3)) := by
  rw [Nat.cast_choose ℝ hh, Nat.cast_choose ℝ (show h + 3 ≤ L + 3 by omega)]
  have e : L + 3 - (h + 3) = L - h := by omega
  rw [e, show L + 3 = (L + 2) + 1 by ring, Nat.factorial_succ (L + 2), show L + 2 = (L + 1) + 1 by ring,
    Nat.factorial_succ (L + 1), Nat.factorial_succ L, show h + 3 = (h + 2) + 1 by ring,
    Nat.factorial_succ (h + 2), show h + 2 = (h + 1) + 1 by ring, Nat.factorial_succ (h + 1),
    Nat.factorial_succ h]
  have h1 : (0 : ℝ) < h ! := by exact_mod_cast Nat.factorial_pos h
  have h2 : (0 : ℝ) < (L - h)! := by exact_mod_cast Nat.factorial_pos (L - h)
  push_cast
  field_simp
  ring

/-- `P(quadrant ∧ U_end ≤ x) ≤ 2√24 (x+1)²/(L+1)²`. -/
theorem end_small (L x : ℕ) :
    (N2F (· ∈ Icc (0 : ℤ) x) (fun _ => True) L 0 0 : ℝ) / 4 ^ L ≤ 2 * √24 * ((x : ℝ) + 1) ^ 2 / (L + 1) ^ 2 := by
  rw [N2F_eq]
  push_cast
  -- bound each term
  have hterm : ∀ h ∈ range (L + 1), (L.choose h : ℝ) * ((N1F (· ∈ Icc (0 : ℤ) x) h 0 : ℝ) *
      (N1F (fun _ => True) (L - h) 0 : ℝ)) ≤
      (L.choose h : ℝ) * (2 * ((x : ℝ) + 1) ^ 2 * cc h / (h + 2) * cc (L - h)) := by
    intro h _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have e1 : (N1F (fun _ => True) (L - h) 0 : ℝ) = cc (L - h) := by
      rw [N1F_true]
      have := N1_eq_Wn (L - h) 0
      simp only [Nat.cast_zero] at this
      rw [this, Wn_zero_start]; rfl
    rw [e1]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [N1F_sum]
    push_cast
    rw [le_div_iff₀ (by positivity), sum_mul]
    have : ∀ y ∈ Icc (0 : ℤ) x, (N1F (· = y) h 0 : ℝ) * (h + 2) ≤ 2 * ((x : ℝ) + 1) * cc h := by
      intro y hy
      rw [mem_Icc] at hy
      have hy0 : y = ((y.toNat : ℕ) : ℤ) := by omega
      rw [hy0]
      refine (endpoint_bound h y.toNat).trans ?_
      (gcongr)
      have : (y.toNat : ℝ) ≤ x := by exact_mod_cast (show y.toNat ≤ x by omega)
      linarith
    calc ∑ y ∈ Icc (0 : ℤ) x, (N1F (· = y) h 0 : ℝ) * (h + 2)
        ≤ ∑ y ∈ Icc (0 : ℤ) x, 2 * ((x : ℝ) + 1) * cc h := sum_le_sum this
      _ = ((x : ℝ) + 1) * (2 * ((x : ℝ) + 1) * cc h) := by
          rw [sum_const, Int.card_Icc, nsmul_eq_mul, show ((x : ℤ) + 1 - 0).toNat = x + 1 by omega]
          push_cast; ring
      _ = 2 * ((x : ℝ) + 1) ^ 2 * cc h := by ring
  refine (div_le_div_of_nonneg_right (sum_le_sum hterm) (by positivity)).trans ?_
  -- normalize: ∑ w_h · 2(x+1)² bb_h bb_{L-h}/(h+2), with bb_h ≤ 1/√(h+1)
  set w : ℕ → ℝ := fun h => (L.choose h : ℝ) / 2 ^ L with hw
  have hw0 : ∀ h, 0 ≤ w h := fun h => by simp only [hw]; positivity
  have e1 : (∑ h ∈ range (L + 1), (L.choose h : ℝ) * (2 * ((x : ℝ) + 1) ^ 2 * cc h / (h + 2) * cc (L - h))) / 4 ^ L
      = 2 * ((x : ℝ) + 1) ^ 2 * ∑ h ∈ range (L + 1), w h * (bb h * bb (L - h) / (h + 2)) := by
    rw [sum_div, mul_sum]
    apply sum_congr rfl; intro h hh; rw [mem_range] at hh
    simp only [hw, bb]
    have : (4 : ℝ) ^ L = 2 ^ L * (2 ^ h * 2 ^ (L - h)) := by
      rw [← pow_add, ← pow_add, show h + (L - h) = L by omega, ← two_mul, pow_mul]; norm_num
    rw [this]; field_simp
  rw [e1]
  have hbb : ∀ h, bb h ≤ 1 / √((h : ℝ) + 1) := by
    intro h
    have := cc_upper h
    unfold bb
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have h2 : ((cc h : ℝ) * √((h : ℝ) + 1)) ^ 2 ≤ ((2 : ℝ) ^ h) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), ← pow_mul, mul_comm h 2, pow_mul]; norm_num; linarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h2
  -- g h = 1/((h+2) √(h+1) √(L-h+1))
  have hg : ∀ h ∈ range (L + 1), w h * (bb h * bb (L - h) / (h + 2)) ≤
      √(w h) * (1 / (((h : ℝ) + 2) * √((h : ℝ) + 1))) * (√(w h) * (1 / √(((L - h : ℕ) : ℝ) + 1))) := by
    intro h _
    have e2 : √(w h) * (1 / (((h : ℝ) + 2) * √((h : ℝ) + 1))) * (√(w h) * (1 / √(((L - h : ℕ) : ℝ) + 1))) =
        w h * ((1 / √((h : ℝ) + 1)) * (1 / √(((L - h : ℕ) : ℝ) + 1)) / (h + 2)) := by
      rw [show √(w h) * (1 / (((h : ℝ) + 2) * √((h : ℝ) + 1))) * (√(w h) * (1 / √(((L - h : ℕ) : ℝ) + 1))) =
        (√(w h) * √(w h)) * ((1 / √((h : ℝ) + 1)) * (1 / √(((L - h : ℕ) : ℝ) + 1)) / (h + 2)) by
          field_simp]
      rw [Real.mul_self_sqrt (hw0 h)]
    rw [e2]
    apply mul_le_mul_of_nonneg_left _ (hw0 h)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul (hbb h) (hbb (L - h)) (bb_nonneg _) (by positivity)
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (range (L + 1))
    (fun h => √(w h) * (1 / (((h : ℝ) + 2) * √((h : ℝ) + 1))))
    (fun h => √(w h) * (1 / √(((L - h : ℕ) : ℝ) + 1)))
  have hA : ∑ h ∈ range (L + 1), (√(w h) * (1 / (((h : ℝ) + 2) * √((h : ℝ) + 1)))) ^ 2 ≤
      12 / ((L : ℝ) + 1) ^ 3 := by
    have per : ∀ h ∈ range (L + 1), (√(w h) * (1 / (((h : ℝ) + 2) * √((h : ℝ) + 1)))) ^ 2 ≤
        (3 / 2) * (((L + 3).choose (h + 3) : ℝ) / ((L + 1) * (L + 2) * (L + 3))) / 2 ^ L := by
      intro h hh; rw [mem_range] at hh
      rw [mul_pow, Real.sq_sqrt (hw0 h), div_pow, one_pow, mul_pow, Real.sq_sqrt (by positivity)]
      have hid := choose_id3b L h (by omega)
      simp only [hw]
      have hq : ((L + 3).choose (h + 3) : ℝ) / ((L + 1) * (L + 2) * (L + 3)) =
          (L.choose h : ℝ) / ((h + 1) * (h + 2) * (h + 3)) := by
        rw [div_eq_div_iff (by positivity) (by positivity)]; linarith [hid]
      rw [hq]
      have lhs : (L.choose h : ℝ) / 2 ^ L * (1 / (((h : ℝ) + 2) ^ 2 * ((h : ℝ) + 1))) =
          (L.choose h : ℝ) * 1 / (2 ^ L * (((h : ℝ) + 2) ^ 2 * ((h : ℝ) + 1))) := by
        rw [div_mul_div_comm]
      have rhs : (3 / 2 : ℝ) * ((L.choose h : ℝ) / (((h : ℝ) + 1) * ((h : ℝ) + 2) * ((h : ℝ) + 3))) / 2 ^ L =
          3 * (L.choose h : ℝ) / (2 * (((h : ℝ) + 1) * ((h : ℝ) + 2) * ((h : ℝ) + 3)) * 2 ^ L) := by
        rw [div_mul_div_comm, div_div]
      rw [lhs, rhs, div_le_div_iff₀ (by positivity) (by positivity)]
      have hpos : 0 ≤ (L.choose h : ℝ) * 2 ^ L * (((h : ℝ) + 1) * ((h : ℝ) + 2)) * h := by positivity
      nlinarith [hpos]
    refine (sum_le_sum per).trans ?_
    rw [← sum_div, ← mul_sum, ← sum_div]
    have hs := row_partial (L + 3) (L + 1) 3
    push_cast at hs
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (3 / 2 : ℝ) * ((∑ h ∈ range (L + 1), ((L + 3).choose (h + 3) : ℝ)) / ((L + 1) * (L + 2) * (L + 3))) *
        ((L : ℝ) + 1) ^ 3 ≤ (3 / 2) * (2 ^ (L + 3) / ((L + 1) * (L + 2) * (L + 3))) * ((L : ℝ) + 1) ^ 3 := by
      (gcongr)
    refine this.trans ?_
    have hL0 : (0 : ℝ) ≤ L := by positivity
    have hP : (0 : ℝ) < ((L : ℝ) + 1) * (L + 2) * (L + 3) := by positivity
    have e : (3 / 2 : ℝ) * (2 ^ (L + 3) / (((L : ℝ) + 1) * (L + 2) * (L + 3))) * ((L : ℝ) + 1) ^ 3 =
        12 * 2 ^ L * (((L : ℝ) + 1) ^ 3 / (((L : ℝ) + 1) * (L + 2) * (L + 3))) := by
      rw [pow_add]; ring
    rw [e]
    have hfrac : ((L : ℝ) + 1) ^ 3 / (((L : ℝ) + 1) * (L + 2) * (L + 3)) ≤ 1 := by
      rw [div_le_one hP]; nlinarith [hL0]
    have h2 : (0 : ℝ) < 12 * 2 ^ L := by positivity
    calc _ ≤ 12 * 2 ^ L * 1 := mul_le_mul_of_nonneg_left hfrac h2.le
      _ = 12 * 2 ^ L := mul_one _
  have hB : ∑ h ∈ range (L + 1), (√(w h) * (1 / √(((L - h : ℕ) : ℝ) + 1))) ^ 2 ≤ 2 / ((L : ℝ) + 1) := by
    have e3 : ∑ h ∈ range (L + 1), (√(w h) * (1 / √(((L - h : ℕ) : ℝ) + 1))) ^ 2 =
        (∑ h ∈ range (L + 1), (L.choose h : ℝ) / (h + 1)) / 2 ^ L := by
      rw [← sum_range_reflect (fun h => (L.choose h : ℝ) / (h + 1)), sum_div]
      apply sum_congr rfl; intro h hh; rw [mem_range] at hh
      rw [mul_pow, Real.sq_sqrt (hw0 h), div_pow, one_pow, Real.sq_sqrt (by positivity)]
      simp only [hw]
      rw [show L + 1 - 1 - h = L - h by omega, Nat.choose_symm (by omega)]
      field_simp
    rw [e3]
    have := sum_choose_div L
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rw [le_div_iff₀ (by positivity)] at this
    rw [pow_succ] at this
    nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) L]
  have hsum : ∑ h ∈ range (L + 1), w h * (bb h * bb (L - h) / (h + 2)) ≤ √24 / ((L : ℝ) + 1) ^ 2 := by
    refine (sum_le_sum hg).trans ?_
    have hnn : 0 ≤ ∑ h ∈ range (L + 1), √(w h) * (1 / (((h : ℝ) + 2) * √((h : ℝ) + 1))) *
        (√(w h) * (1 / √(((L - h : ℕ) : ℝ) + 1))) := sum_nonneg (fun h _ => by positivity)
    have hsq : (∑ h ∈ range (L + 1), √(w h) * (1 / (((h : ℝ) + 2) * √((h : ℝ) + 1))) *
        (√(w h) * (1 / √(((L - h : ℕ) : ℝ) + 1)))) ^ 2 ≤ (√24 / ((L : ℝ) + 1) ^ 2) ^ 2 := by
      refine hCS.trans ?_
      calc _ ≤ 12 / ((L : ℝ) + 1) ^ 3 * (2 / ((L : ℝ) + 1)) :=
            mul_le_mul hA hB (sum_nonneg (fun _ _ => by positivity)) (by positivity)
        _ = (√24 / ((L : ℝ) + 1) ^ 2) ^ 2 := by
            rw [div_pow, Real.sq_sqrt (by norm_num)]; field_simp; ring
    exact (pow_le_pow_iff_left₀ hnn (by positivity) two_ne_zero).mp hsq
  have := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 2 * ((x : ℝ) + 1) ^ 2 by positivity)
  refine this.trans (le_of_eq ?_)
  ring

end E521

end S_C22

-- ===== C23 =====
section S_C23

/-! The cone with large final coordinates keeps almost all of the quadrant mass (original). -/

open Finset Real

namespace E521

lemma N1F_congr (F G : ℤ → Prop) [DecidablePred F] [DecidablePred G] (hFG : ∀ y, 0 ≤ y → (F y ↔ G y))
    (L : ℕ) : ∀ u : ℤ, N1F F L u = N1F G L u := by
  induction L with
  | zero =>
    intro u; rw [N1F_zero, N1F_zero]
    by_cases hu : 0 ≤ u
    · by_cases hF : F u
      · rw [if_pos ⟨hu, hF⟩, if_pos ⟨hu, (hFG u hu).mp hF⟩]
      · rw [if_neg (fun h : 0 ≤ u ∧ F u => hF h.2), if_neg (fun h : 0 ≤ u ∧ G u => hF ((hFG u hu).mpr h.2))]
    · rw [if_neg (fun h : 0 ≤ u ∧ _ => hu h.1), if_neg (fun h : 0 ≤ u ∧ _ => hu h.1)]
  | succ L ih =>
    intro u
    by_cases hu : 0 ≤ u
    · rw [N1F_succ _ L hu, N1F_succ _ L hu, ih, ih]
    · rw [N1F_neg _ _ (not_le.mp hu), N1F_neg _ _ (not_le.mp hu)]

lemma N1_split (lam : ℕ) (hlam : 1 ≤ lam) (L : ℕ) (u : ℤ) :
    N1 L u = N1F (fun y => (lam : ℤ) ≤ y) L u + N1F (· ∈ Icc (0 : ℤ) ((lam - 1 : ℕ) : ℤ)) L u := by
  rw [← N1F_true, ← N1F_or _ _ (fun y h => by
    rcases h with ⟨h1, h2⟩; rw [mem_Icc] at h2; omega)]
  apply N1F_congr
  intro y hy
  simp only [true_iff, mem_Icc]
  omega

/-- the final-coordinate restriction costs at most `4√24 λ²/(K+1)²`. -/
theorem cone_plus_lower (K lam : ℕ) (hlam : 1 ≤ lam) :
    (N2 K 0 0 : ℝ) / 4 ^ K - 4 * √24 * (lam : ℝ) ^ 2 / (K + 1) ^ 2 ≤
      (N2F (fun y => (lam : ℤ) ≤ y) (fun y => (lam : ℤ) ≤ y) K 0 0 : ℝ) / 4 ^ K := by
  have hN2 : (N2 K 0 0 : ℝ) ≤ N2F (fun y => (lam : ℤ) ≤ y) (fun y => (lam : ℤ) ≤ y) K 0 0 + N2F (· ∈ Icc (0 : ℤ) ((lam - 1 : ℕ) : ℤ)) (fun _ => True) K 0 0
      + N2F (fun _ => True) (· ∈ Icc (0 : ℤ) ((lam - 1 : ℕ) : ℤ)) K 0 0 := by
    rw [N2_eq, N2F_eq, N2F_eq, N2F_eq]
    push_cast
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_le_sum; intro h _
    rw [N1_split lam hlam h 0, N1_split lam hlam (K - h) 0, N1F_true, N1F_true, N1_split lam hlam h 0,
      N1_split lam hlam (K - h) 0]
    push_cast
    have hc := Nat.cast_nonneg (α := ℝ) (K.choose h)
    have a1 := Nat.cast_nonneg (α := ℝ) (N1F (fun y => (lam : ℤ) ≤ y) h 0)
    have a2 := Nat.cast_nonneg (α := ℝ) (N1F (· ∈ Icc (0 : ℤ) ((lam - 1 : ℕ) : ℤ)) h 0)
    have a3 := Nat.cast_nonneg (α := ℝ) (N1F (fun y => (lam : ℤ) ≤ y) (K - h) 0)
    have a4 := Nat.cast_nonneg (α := ℝ) (N1F (· ∈ Icc (0 : ℤ) ((lam - 1 : ℕ) : ℤ)) (K - h) 0)
    have := mul_nonneg hc (mul_nonneg a2 a4)
    nlinarith
  have hx : ((lam - 1 : ℕ) : ℝ) + 1 = lam := by rw [Nat.cast_sub hlam]; push_cast; ring
  have e1 := end_small K (lam - 1)
  rw [hx] at e1
  have e2 : (N2F (fun _ => True) (· ∈ Icc (0 : ℤ) ((lam - 1 : ℕ) : ℤ)) K 0 0 : ℝ) = N2F (· ∈ Icc (0 : ℤ) ((lam - 1 : ℕ) : ℤ)) (fun _ => True) K 0 0 := by
    rw [N2F_eq, N2F_eq]
    push_cast
    rw [← sum_range_reflect]
    apply sum_congr rfl; intro h hh; rw [mem_range] at hh
    rw [show K + 1 - 1 - h = K - h by omega, show K - (K - h) = h by omega, Nat.choose_symm (by omega)]
    ring
  rw [e2] at hN2
  have h4 : (0 : ℝ) < 4 ^ K := by positivity
  have key : (N2 K 0 0 : ℝ) / 4 ^ K ≤ (N2F (fun y => (lam : ℤ) ≤ y) (fun y => (lam : ℤ) ≤ y) K 0 0 : ℝ) / 4 ^ K + (N2F (· ∈ Icc (0 : ℤ) ((lam - 1 : ℕ) : ℤ)) (fun _ => True) K 0 0 : ℝ) / 4 ^ K
      + (N2F (· ∈ Icc (0 : ℤ) ((lam - 1 : ℕ) : ℤ)) (fun _ => True) K 0 0 : ℝ) / 4 ^ K := by
    rw [← add_div, ← add_div]
    exact div_le_div_of_nonneg_right hN2 h4.le
  have e1' : (N2F (· ∈ Icc (0 : ℤ) ((lam - 1 : ℕ) : ℤ)) (fun _ => True) K 0 0 : ℝ) / 4 ^ K ≤ 2 * √24 * (lam : ℝ) ^ 2 / (K + 1) ^ 2 := e1
  have : 2 * √24 * (lam : ℝ) ^ 2 / (K + 1) ^ 2 + 2 * √24 * (lam : ℝ) ^ 2 / (K + 1) ^ 2 =
      4 * √24 * (lam : ℝ) ^ 2 / (K + 1) ^ 2 := by ring
  linarith

end E521

end S_C23

-- ===== P9 =====
section S_P9

/-! The good event `H_K` and its probability (original). Parameters for `n = 2K - 1`:
`t = ⌊n^{19/20}⌋`, `λ = ⌈n^{39/80}⌉`, count threshold `A = c' log n` with `c' = 63/100`. -/

open Finset MeasureTheory Filter Topology

noncomputable section

namespace E521

def tK (K : ℕ) : ℕ := ⌊((2 * K - 1 : ℕ) : ℝ) ^ ((19 : ℝ) / 20)⌋₊
def lamK (K : ℕ) : ℕ := ⌈((2 * K - 1 : ℕ) : ℝ) ^ ((39 : ℝ) / 80)⌉₊
def pK (K : ℕ) : ℕ := (2 * K - 1) - tK K
def AK (K : ℕ) : ℝ := (63 / 100) * Real.log ((2 * K - 1 : ℕ) : ℝ)

/-- the tail events. -/
def Gev (K : ℕ) : Set (ℕ → Bool) :=
  {ω | ∀ l ≤ tK K, |∑ i ∈ range l, eR ω (2 * K - 1 - i)| < 2 * (lamK K : ℝ) - 1}
def Gev' (K : ℕ) : Set (ℕ → Bool) :=
  {ω | ∀ l ≤ tK K, |∑ i ∈ range l, (-1) ^ i * eR ω (2 * K - 1 - i)| < 2 * (lamK K : ℝ) - 1}

/-- the sign-change count before `p`. -/
def cnt (K : ℕ) (ω : ℕ → Bool) : ℕ :=
  ((range (pK K)).filter (fun k => ω ∈ Iev k)).card + ((range (pK K)).filter (fun k => ω ∈ Ialt k)).card

def Cplus (K : ℕ) : Set (ℕ → Bool) := coneE K (fun y => (lamK K : ℤ) ≤ y) (fun y => (lamK K : ℤ) ≤ y)

/-- **the good event**. -/
def Hev (K : ℕ) : Set (ℕ → Bool) := Cplus K ∩ Gev K ∩ Gev' K ∩ {ω | (cnt K ω : ℝ) < AK K}

/-- on the good event the root count is small. -/
theorem roots_on_H (K : ℕ) (hK : 1 ≤ K) (ω : ℕ → Bool) (hω : ω ∈ Hev K) (ht : tK K ≤ 2 * K - 1) :
    ((fR (2 * K - 1) ω).roots.card : ℝ) < AK K + 2 := by
  obtain ⟨⟨⟨hC, hG⟩, hG'⟩, hc⟩ := hω
  have := roots_good K (tK K) (lamK K) ω hK ht hC hG hG'
  have hc' : (cnt K ω : ℝ) < AK K := hc
  unfold cnt at hc'
  have : ((fR (2 * K - 1) ω).roots.card : ℝ) ≤
      ((((range (2 * K - 1 - tK K)).filter (fun k => ω ∈ Iev k)).card +
      ((range (2 * K - 1 - tK K)).filter (fun k => ω ∈ Ialt k)).card + 2 : ℕ) : ℝ) := by
    exact_mod_cast this
  push_cast at this hc'
  unfold pK at hc'
  linarith

end E521
end

end S_P9

-- ===== P10 =====
section S_P10

/-! A deterministic lower bound for `μ(H_K)` (original). -/

open Finset MeasureTheory Filter Topology

noncomputable section

namespace E521

lemma measurable_eR (j : ℕ) : Measurable (fun ω : ℕ → Bool => eR ω j) := by
  unfold eR
  exact Measurable.ite (measurableSet_eq_fun (measurable_pi_apply j) measurable_const)
    measurable_const measurable_const

lemma meas_blockset (l : ℕ) (w : ℕ → ℝ) (x : ℝ) :
    MeasurableSet {ω : ℕ → Bool | x ≤ |∑ j ∈ range l, w j * eR ω j|} := by
  apply measurableSet_le measurable_const
  exact (Finset.measurable_sum _ (fun j _ => (measurable_eR j).const_mul (w j))).abs

/-- generic tail bound for backward blocks. -/
lemma back_tail (n t : ℕ) (ht : t ≤ n + 1) (w : ℕ → ℝ) (hw : ∀ j, w j ^ 2 = 1) {x : ℝ} (hx : 0 < x) :
    μS.real {ω | ∃ l ≤ t, x ≤ |∑ i ∈ range l, w i * eR ω (n - i)|} ≤ (t + 1) * (2 * Real.exp (-(x ^ 2 / (2 * t)))) := by
  have hsub : {ω | ∃ l ≤ t, x ≤ |∑ i ∈ range l, w i * eR ω (n - i)|} ⊆
      ⋃ l ∈ range (t + 1), {ω | x ≤ |∑ i ∈ range l, w i * eR ω (n - i)|} := by
    intro ω ⟨l, hl, h⟩; simp only [Set.mem_iUnion, mem_range]; exact ⟨l, by omega, h⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  have each : ∀ l ∈ range (t + 1), μS.real {ω | x ≤ |∑ i ∈ range l, w i * eR ω (n - i)|} ≤
      2 * Real.exp (-(x ^ 2 / (2 * t))) := by
    intro l hl; rw [mem_range] at hl
    rcases Nat.eq_zero_or_pos l with h0 | hpos
    · subst h0
      have : {ω : ℕ → Bool | x ≤ |∑ i ∈ range 0, w i * eR ω (n - i)|} = ∅ := by
        ext ω; simp; linarith
      rw [this]; simp; positivity
    · have hset : {ω | x ≤ |∑ i ∈ range l, w i * eR ω (n - i)|} =
          (fun ω i => ω (i + (n + 1 - l))) ⁻¹' {ω | x ≤ |∑ j ∈ range l, w (l - 1 - j) * eR ω j|} := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage]
        rw [back_shift n l (by omega) w ω]
      rw [hset, Measure.real, μS_shift_preimage _ (meas_blockset l _ x), ← Measure.real]
      refine (block_hoeffding_w l (fun j => w (l - 1 - j)) (fun j => hw _) hx).trans ?_
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      have hl' : (l : ℝ) ≤ t := by exact_mod_cast (by omega : l ≤ t)
      have hl0 : (0 : ℝ) < l := by exact_mod_cast hpos
      have : x ^ 2 / (2 * t) ≤ x ^ 2 / (2 * l) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      linarith
  refine (sum_le_sum each).trans (le_of_eq ?_)
  rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring

lemma Gev_compl_le (K : ℕ) (hK : 1 ≤ K) (hlam : 1 ≤ lamK K) (ht : tK K ≤ 2 * K - 1) :
    μS.real (Gev K)ᶜ ≤ (tK K + 1) * (2 * Real.exp (-((2 * (lamK K : ℝ) - 1) ^ 2 / (2 * tK K)))) := by
  have hx : (0 : ℝ) < 2 * (lamK K : ℝ) - 1 := by
    have : (1 : ℝ) ≤ lamK K := by exact_mod_cast hlam
    linarith
  have hsub : (Gev K)ᶜ ⊆ {ω | ∃ l ≤ tK K, 2 * (lamK K : ℝ) - 1 ≤
      |∑ i ∈ range l, (fun _ => (1 : ℝ)) i * eR ω (2 * K - 1 - i)|} := by
    intro ω hω
    simp only [Gev, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_lt] at hω
    obtain ⟨l, hl, h⟩ := hω
    exact ⟨l, hl, by simpa using h⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  exact back_tail (2 * K - 1) (tK K) (by omega) (fun _ => 1) (fun _ => by norm_num) hx

lemma Gev'_compl_le (K : ℕ) (hK : 1 ≤ K) (hlam : 1 ≤ lamK K) (ht : tK K ≤ 2 * K - 1) :
    μS.real (Gev' K)ᶜ ≤ (tK K + 1) * (2 * Real.exp (-((2 * (lamK K : ℝ) - 1) ^ 2 / (2 * tK K)))) := by
  have hx : (0 : ℝ) < 2 * (lamK K : ℝ) - 1 := by
    have : (1 : ℝ) ≤ lamK K := by exact_mod_cast hlam
    linarith
  have hsub : (Gev' K)ᶜ ⊆ {ω | ∃ l ≤ tK K, 2 * (lamK K : ℝ) - 1 ≤
      |∑ i ∈ range l, (fun i => (-1 : ℝ) ^ i) i * eR ω (2 * K - 1 - i)|} := by
    intro ω hω
    simp only [Gev', Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_lt] at hω
    obtain ⟨l, hl, h⟩ := hω
    exact ⟨l, hl, h⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  exact back_tail (2 * K - 1) (tK K) (by omega) (fun i => (-1) ^ i)
    (fun j => by rw [← pow_mul, mul_comm, pow_mul]; norm_num) hx

end E521
end

end S_P10

-- ===== P11 =====
section S_P11

/-! `μ(H_K) ≥ (1/40)(4/π)/K` for large `K`, the pair bound, and a positive-probability `limsup`
(original). -/

open Finset MeasureTheory Filter Topology

noncomputable section

namespace E521

lemma tK_le (K : ℕ) (hK : 1 ≤ K) : tK K ≤ 2 * K - 1 := by
  unfold tK
  have hn : (1 : ℝ) ≤ ((2 * K - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * K - 1)
  have := Real.rpow_le_self_of_one_le hn (show (19 : ℝ) / 20 ≤ 1 by norm_num)
  have h := Nat.floor_le (show (0 : ℝ) ≤ ((2 * K - 1 : ℕ) : ℝ) ^ ((19 : ℝ) / 20) by positivity)
  exact_mod_cast (h.trans this)

/-- the combined event family for Markov. -/
def Bfam (K : ℕ) (k : ℕ) : Set (ℕ → Bool) := if k < pK K then Iev k else Ialt (k - pK K)

instance instDecBfam (K k : ℕ) (ω : ℕ → Bool) : Decidable (ω ∈ Bfam K k) := by
  unfold Bfam; split_ifs <;> infer_instance

lemma cnt_eq (K : ℕ) (ω : ℕ → Bool) :
    cnt K ω = ((range (2 * pK K)).filter (fun k => ω ∈ Bfam K k)).card := by
  classical
  unfold cnt
  rw [card_filter, card_filter, card_filter, show 2 * pK K = pK K + pK K by ring, sum_range_add]
  congr 1
  · apply sum_congr rfl; intro k hk; rw [mem_range] at hk
    have e : (ω ∈ Bfam K k) ↔ ω ∈ Iev k := by unfold Bfam; rw [if_pos hk]
    by_cases h : ω ∈ Iev k
    · rw [if_pos h, if_pos (e.mpr h)]
    · rw [if_neg h, if_neg (fun h' => h (e.mp h'))]
  · apply sum_congr rfl; intro k _
    have e : (ω ∈ Bfam K (pK K + k)) ↔ ω ∈ Ialt k := by
      unfold Bfam; rw [if_neg (by omega), Nat.add_sub_cancel_left]
    by_cases h : ω ∈ Ialt k
    · rw [if_pos h, if_pos (e.mpr h)]
    · rw [if_neg h, if_neg (fun h' => h (e.mp h'))]

end E521

namespace E521

lemma coneE_le_u (K : ℕ) (F G : ℤ → Prop) :
    μS.real (coneE K F G) ≤ (N2 K 0 0 : ℝ) / 4 ^ K := by
  rw [← topE_real K K le_rfl]
  exact measureReal_mono (cone_sub_top K K le_rfl F G) (measure_ne_top _ _)

lemma Hev_sub (K : ℕ) : Hev K ⊆ Cplus K := fun ω h => h.1.1.1

lemma Hev_pair (K K' : ℕ) (h : K ≤ K') :
    μS.real (Hev K ∩ Hev K') ≤ ((N2 K 0 0 : ℝ) / 4 ^ K) * ((N2 (K' - K) 0 0 : ℝ) / 4 ^ (K' - K)) := by
  have h1 : Hev K ∩ Hev K' ⊆ Cplus K ∩ Cplus K' :=
    Set.inter_subset_inter (Hev_sub K) (Hev_sub K')
  refine (measureReal_mono h1 (measure_ne_top _ _)).trans ?_
  refine (cone_pair K K' h _ _ _ _).trans ?_
  apply mul_le_mul_of_nonneg_right (coneE_le_u K _ _) (by positivity)

lemma u_crude (L : ℕ) : (N2 L 0 0 : ℝ) / 4 ^ L ≤ (20 / Real.pi) / (L + 1) := by
  refine (u_upper L).trans ?_
  have h : √(1 + 24 / ((L : ℝ) + 1)) ≤ 5 := by
    rw [Real.sqrt_le_left (by norm_num)]
    have : 24 / ((L : ℝ) + 1) ≤ 24 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [Nat.cast_nonneg (α := ℝ) L]
    linarith
  have hp := Real.pi_pos
  calc (4 / Real.pi) / ((L : ℝ) + 1) * √(1 + 24 / ((L : ℝ) + 1)) ≤ (4 / Real.pi) / ((L : ℝ) + 1) * 5 :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (20 / Real.pi) / (L + 1) := by ring

end E521

namespace E521

lemma meas_Iev (k : ℕ) : MeasurableSet (Iev k) := by
  rw [Iev_cyl]; exact measurableSet_rs _ _

lemma meas_Ialt (k : ℕ) : MeasurableSet (Ialt k) := by
  rw [Ialt_cyl]; exact measurableSet_rs _ _

lemma meas_coneE (K : ℕ) (F G : ℤ → Prop) : MeasurableSet (coneE K F G) := measurableSet_Φ K _

lemma meas_Bfam (K k : ℕ) : MeasurableSet (Bfam K k) := by
  unfold Bfam; split_ifs; exacts [meas_Iev _, meas_Ialt _]

/-- Markov for the combined count. -/
lemma cone_cnt (K : ℕ) (hA : 0 < AK K) :
    AK K * μS.real (Cplus K ∩ {ω | AK K ≤ (cnt K ω : ℝ)}) ≤
      ∑ k ∈ range (pK K), (μS.real (Cplus K ∩ Iev k) + μS.real (Cplus K ∩ Ialt k)) := by
  classical
  have hset : Cplus K ∩ {ω | AK K ≤ (cnt K ω : ℝ)} =
      Cplus K ∩ {ω | AK K ≤ (((range (2 * pK K)).filter (fun k => ω ∈ Bfam K k)).card : ℝ)} := by
    ext ω; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, cnt_eq]
  rw [hset]
  have hm := E521Q.markov_count μS (Cplus K) (meas_coneE _ _ _) (range (2 * pK K)) (Bfam K)
    (meas_Bfam K) hA
  refine hm.trans (le_of_eq ?_)
  rw [show 2 * pK K = pK K + pK K by ring, sum_range_add, sum_add_distrib]
  congr 1
  · apply sum_congr rfl; intro k hk; rw [mem_range] at hk; simp [Bfam, hk]
  · apply sum_congr rfl; intro k _; simp [Bfam]

end E521

namespace E521

def LK (K k : ℕ) : ℕ := (2 * K - k - 2) / 2

/-- **deterministic lower bound for `μ(H_K)`.** -/
theorem Hev_det (K : ℕ) (hK : 1 ≤ K) (hlam : 1 ≤ lamK K) (hA : 0 < AK K) (hpn : pK K + 2 ≤ 2 * K) :
    (4 / Real.pi) / (K + 4) - 4 * √24 * (lamK K : ℝ) ^ 2 / (K + 1) ^ 2
      - 2 * ((tK K + 1) * (2 * Real.exp (-((2 * (lamK K : ℝ) - 1) ^ 2 / (2 * tK K)))))
      - (2 / AK K) * ∑ k ∈ range (pK K), ((N2 (LK K k) 0 0 : ℝ) / 4 ^ (LK K k)) * R522.PP (R522.SCev (k + 2))
      ≤ μS.real (Hev K) := by
  classical
  have ht := tK_le K hK
  -- covering
  have hcov : Cplus K ⊆ Hev K ∪ (Gev K)ᶜ ∪ (Gev' K)ᶜ ∪ (Cplus K ∩ {ω | AK K ≤ (cnt K ω : ℝ)}) := by
    intro ω hω
    by_cases h1 : ω ∈ Gev K
    · by_cases h2 : ω ∈ Gev' K
      · by_cases h3 : (cnt K ω : ℝ) < AK K
        · left; left; left; exact ⟨⟨⟨hω, h1⟩, h2⟩, h3⟩
        · right; exact ⟨hω, not_lt.mp h3⟩
      · left; right; exact h2
    · left; left; right; exact h1
  have hmeas := measureReal_mono (μ := μS) hcov (measure_ne_top _ _)
  have hu1 := measureReal_union_le (μ := μS) (Hev K ∪ (Gev K)ᶜ ∪ (Gev' K)ᶜ) (Cplus K ∩ {ω | AK K ≤ (cnt K ω : ℝ)})
  have hu2 := measureReal_union_le (μ := μS) (Hev K ∪ (Gev K)ᶜ) (Gev' K)ᶜ
  have hu3 := measureReal_union_le (μ := μS) (Hev K) (Gev K)ᶜ
  -- the cone
  have hC : (4 / Real.pi) / (K + 4) - 4 * √24 * (lamK K : ℝ) ^ 2 / (K + 1) ^ 2 ≤ μS.real (Cplus K) := by
    unfold Cplus
    rw [coneE_real]
    have := cone_plus_lower K (lamK K) hlam
    have := u_lower K
    linarith
  have hG := Gev_compl_le K hK hlam ht
  have hG' := Gev'_compl_le K hK hlam ht
  -- the count
  have hcnt := cone_cnt K hA
  have hsum : ∑ k ∈ range (pK K), (μS.real (Cplus K ∩ Iev k) + μS.real (Cplus K ∩ Ialt k)) ≤
      2 * ∑ k ∈ range (pK K), ((N2 (LK K k) 0 0 : ℝ) / 4 ^ (LK K k)) * R522.PP (R522.SCev (k + 2)) := by
    rw [mul_sum]
    apply sum_le_sum; intro k hk; rw [mem_range] at hk
    have hL : LK K k ≤ K := by unfold LK; omega
    have hk2 : k + 2 ≤ 2 * K - 2 * LK K k := by unfold LK; omega
    have a := cone_Iev K (LK K k) k hL hk2 (fun y => (lamK K : ℤ) ≤ y) (fun y => (lamK K : ℤ) ≤ y)
    have b := cone_Ialt K (LK K k) k hL hk2 (fun y => (lamK K : ℤ) ≤ y) (fun y => (lamK K : ℤ) ≤ y)
    unfold Cplus; linarith
  have hcnt' : μS.real (Cplus K ∩ {ω | AK K ≤ (cnt K ω : ℝ)}) ≤
      (2 / AK K) * ∑ k ∈ range (pK K), ((N2 (LK K k) 0 0 : ℝ) / 4 ^ (LK K k)) * R522.PP (R522.SCev (k + 2)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hA]
    linarith
  linarith

end E521
end

end S_P11

-- ===== P12 =====
section S_P12

/-! Asymptotics: `μ(H_K) ≥ (4/π)/(40 K)` eventually (original). -/

open Finset MeasureTheory Filter Topology

noncomputable section

namespace E521

/-- `n = 2K - 1 → ∞`. -/
lemma tendsto_nK : Tendsto (fun K : ℕ => ((2 * K - 1 : ℕ) : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp
    (tendsto_atTop_atTop_of_monotone (fun a b h => by omega) (fun b => ⟨b + 1, by omega⟩))

lemma lamK_ge (K : ℕ) : ((2 * K - 1 : ℕ) : ℝ) ^ ((39 : ℝ) / 80) ≤ lamK K := Nat.le_ceil _

lemma lamK_le (K : ℕ) : (lamK K : ℝ) ≤ ((2 * K - 1 : ℕ) : ℝ) ^ ((39 : ℝ) / 80) + 1 :=
  (Nat.ceil_lt_add_one (by positivity)).le

lemma tK_ge (K : ℕ) : ((2 * K - 1 : ℕ) : ℝ) ^ ((19 : ℝ) / 20) ≤ (tK K : ℝ) + 1 :=
  (Nat.lt_floor_add_one _).le

lemma tK_le' (K : ℕ) : (tK K : ℝ) ≤ ((2 * K - 1 : ℕ) : ℝ) ^ ((19 : ℝ) / 20) :=
  Nat.floor_le (by positivity)

/-- the numerical heart: `2 (c+θ)(1+θ)(21/20)/c' ≤ 0.95` with `c = √3/(2π)`, `θ = 1/200`, `c' = 63/100`. -/
lemma key_const : 2 * (√3 / (2 * Real.pi) + 1 / 200) * (1 + 1 / 200) * (21 / 20) / (63 / 100) ≤ 95 / 100 := by
  have hs : √3 ≤ 17321 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hpi : (3141 / 1000 : ℝ) < Real.pi := by have := Real.pi_gt_d4; linarith
  have hp0 := Real.pi_pos
  have : √3 / (2 * Real.pi) ≤ (17321 / 10000) / (2 * (3141 / 1000)) := by
    apply div_le_div₀ (by norm_num) hs (by norm_num) (by linarith)
  have hc : (17321 / 10000 : ℝ) / (2 * (3141 / 1000)) ≤ 2758 / 10000 := by norm_num
  nlinarith

end E521

namespace E521

/-- `K · E₁ → 0` (endpoint term). -/
lemma E1_small : Tendsto (fun K : ℕ => (K : ℝ) * (4 * √24 * (lamK K : ℝ) ^ 2 / (K + 1) ^ 2)) atTop (𝓝 0) := by
  -- ≤ 32√24 n^{-1/40}
  have hlim : Tendsto (fun K : ℕ => 32 * √24 * ((2 * K - 1 : ℕ) : ℝ) ^ (-(1 / 40 : ℝ))) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (show (0:ℝ) < 1/40 by norm_num)).comp tendsto_nK).const_mul (32 * √24)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall (fun K => by positivity)) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with K hK
  set n : ℝ := ((2 * K - 1 : ℕ) : ℝ) with hn
  have hn1 : (1 : ℝ) ≤ n := by rw [hn]; exact_mod_cast (by omega : 1 ≤ 2 * K - 1)
  have hnK : n = 2 * K - 1 := by rw [hn]; push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * K)]; ring
  have hlam := lamK_le K
  have hq : (1 : ℝ) ≤ n ^ ((39 : ℝ) / 80) := Real.one_le_rpow hn1 (by norm_num)
  have hl2 : (lamK K : ℝ) ^ 2 ≤ 4 * n ^ ((39 : ℝ) / 40) := by
    have : (lamK K : ℝ) ≤ 2 * n ^ ((39 : ℝ) / 80) := by linarith
    have h0 : (0 : ℝ) ≤ lamK K := by positivity
    have := pow_le_pow_left₀ h0 this 2
    rw [mul_pow, ← Real.rpow_natCast (n ^ ((39 : ℝ) / 80)) 2, ← Real.rpow_mul (by linarith)] at this
    norm_num at this ⊢; linarith
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  -- K/(K+1)^2 ≤ 1/K ≤ 2/n... use K ≥ (n+1)/2
  have : (K : ℝ) * (4 * √24 * (lamK K : ℝ) ^ 2 / (K + 1) ^ 2) ≤ 4 * √24 * (lamK K : ℝ) ^ 2 / K := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have h0 : (0 : ℝ) ≤ 4 * √24 * (lamK K : ℝ) ^ 2 := by positivity
    nlinarith [mul_nonneg h0 (sq_nonneg (K : ℝ))]
  refine this.trans ?_
  have hKn : (K : ℝ) ≥ n / 2 := by rw [hnK]; linarith
  have e : n ^ (-(1 / 40 : ℝ)) = n ^ ((39 : ℝ) / 40) / n := by
    rw [show (-(1 / 40 : ℝ)) = (39 : ℝ) / 40 - 1 by norm_num, Real.rpow_sub (by linarith), Real.rpow_one]
  rw [e]
  have hn0 : (0 : ℝ) < n := by linarith
  have h24 : (0 : ℝ) ≤ √24 := Real.sqrt_nonneg _
  calc 4 * √24 * (lamK K : ℝ) ^ 2 / K ≤ 4 * √24 * (4 * n ^ ((39 : ℝ) / 40)) / (n / 2) := by
        apply div_le_div₀ (by positivity) (by gcongr) (by positivity) hKn
    _ = 32 * √24 * (n ^ ((39 : ℝ) / 40) / n) := by field_simp; ring

end E521

namespace E521

/-- `K · E₂ → 0` (tail term). -/
lemma E2_small : Tendsto (fun K : ℕ => (K : ℝ) * (2 * ((tK K + 1) *
    (2 * Real.exp (-((2 * (lamK K : ℝ) - 1) ^ 2 / (2 * tK K))))))) atTop (𝓝 0) := by
  have hlim : Tendsto (fun K : ℕ => 8 * (((2 * K - 1 : ℕ) : ℝ) ^ (2 : ℝ) *
      Real.exp (-(1 / 2) * ((2 * K - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 40)))) atTop (𝓝 0) := by
    have := (((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * 40) (1 / 2) (by norm_num)).comp
      ((tendsto_rpow_atTop (show (0:ℝ) < 1 / 40 by norm_num)).comp tendsto_nK)).const_mul 8)
    rw [mul_zero] at this
    refine this.congr' (Eventually.of_forall (fun K => ?_))
    simp only [Function.comp]
    rw [← Real.rpow_mul (by positivity)]; norm_num
  refine squeeze_zero' (Eventually.of_forall (fun K => by positivity)) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with K hK
  set n : ℝ := ((2 * K - 1 : ℕ) : ℝ) with hn
  have hn1 : (1 : ℝ) ≤ n := by rw [hn]; exact_mod_cast (by omega : 1 ≤ 2 * K - 1)
  have hnK : n = 2 * K - 1 := by rw [hn]; push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * K)]; ring
  have hlam := lamK_ge K
  have ht := tK_le' K
  have hq : (1 : ℝ) ≤ n ^ ((39 : ℝ) / 80) := Real.one_le_rpow hn1 (by norm_num)
  have hlam1 : (1 : ℝ) ≤ lamK K := by rw [← hn] at hlam; linarith
  -- exponent
  have hexp : -((2 * (lamK K : ℝ) - 1) ^ 2 / (2 * tK K)) ≤ -(1 / 2) * n ^ ((1 : ℝ) / 40) := by
    have h1t : 1 ≤ tK K := by
      unfold tK; apply Nat.le_floor; push_cast; exact Real.one_le_rpow hn1 (by norm_num)
    have htp : (0 : ℝ) < tK K := by exact_mod_cast h1t
    have h1 : n ^ ((39 : ℝ) / 40) ≤ (2 * (lamK K : ℝ) - 1) ^ 2 := by
      have : n ^ ((39 : ℝ) / 80) ≤ 2 * (lamK K : ℝ) - 1 := by rw [← hn] at hlam; linarith
      have := pow_le_pow_left₀ (by positivity) this 2
      rw [← Real.rpow_natCast (n ^ ((39 : ℝ) / 80)) 2, ← Real.rpow_mul (by linarith)] at this
      norm_num at this; exact this
    have h2 : n ^ ((1 : ℝ) / 40) * n ^ ((19 : ℝ) / 20) = n ^ ((39 : ℝ) / 40) := by
      rw [← Real.rpow_add (by linarith)]; norm_num
    rw [← hn] at ht
    have hx0 := Real.rpow_nonneg (show (0:ℝ) ≤ n by linarith) ((1 : ℝ) / 40)
    have hm := mul_le_mul_of_nonneg_left ht hx0
    have hq2 : (1 / 2) * n ^ ((1 : ℝ) / 40) ≤ (2 * (lamK K : ℝ) - 1) ^ 2 / (2 * tK K) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    linarith
  have hK1 : (K : ℝ) ≤ n := by
    rw [hnK]
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have ht1 : (tK K : ℝ) + 1 ≤ 2 * n := by
    have := Real.rpow_le_self_of_one_le hn1 (show (19 : ℝ) / 20 ≤ 1 by norm_num)
    rw [← hn] at ht; linarith
  have hn2 : n ^ (2 : ℝ) = n ^ 2 := Real.rpow_natCast n 2 ▸ by norm_num
  rw [hn2]
  have hE := Real.exp_le_exp.mpr hexp
  have hE0 := Real.exp_pos (-((2 * (lamK K : ℝ) - 1) ^ 2 / (2 * tK K)))
  calc (K : ℝ) * (2 * ((tK K + 1) * (2 * Real.exp (-((2 * (lamK K : ℝ) - 1) ^ 2 / (2 * tK K))))))
      = 4 * (K * (tK K + 1)) * Real.exp (-((2 * (lamK K : ℝ) - 1) ^ 2 / (2 * tK K))) := by ring
    _ ≤ 4 * (n * (2 * n)) * Real.exp (-(1 / 2) * n ^ ((1 : ℝ) / 40)) := by
        (gcongr)
    _ = 8 * (n ^ 2 * Real.exp (-(1 / 2) * n ^ ((1 : ℝ) / 40))) := by ring

end E521

namespace E521

lemma sqrt_bound {x : ℝ} (hx : 2400 ≤ x) : √(1 + 24 / x) ≤ 1 + 1 / 200 := by
  rw [Real.sqrt_le_left (by norm_num)]
  have h : 24 / x ≤ 1 / 100 := by rw [div_le_iff₀ (by linarith)]; linarith
  norm_num
  linarith

lemma ub_step {A x y : ℝ} (hA : 0 ≤ A) (hx : 0 < x) (hy : 0 < y) (h : y ≤ 2 * x) : A / x ≤ (2 * A) / y := by
  rw [div_le_div_iff₀ hx hy]
  have := mul_le_mul_of_nonneg_left h hA
  linarith

lemma tK_half : ∀ᶠ K : ℕ in atTop, (tK K : ℝ) ≤ ((2 * K - 1 : ℕ) : ℝ) / 2 := by
  have h20 := ((tendsto_rpow_atTop (show (0:ℝ) < 1 / 20 by norm_num)).comp tendsto_nK).eventually_ge_atTop 2
  filter_upwards [h20, eventually_ge_atTop 1] with K hK2 hK1
  simp only [Function.comp] at hK2
  have hn1 : (1 : ℝ) ≤ ((2 * K - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * K - 1)
  have e : ((2 * K - 1 : ℕ) : ℝ) = ((2 * K - 1 : ℕ) : ℝ) ^ ((19 : ℝ) / 20) * ((2 * K - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 20) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have := tK_le' K
  have hpos : (0 : ℝ) ≤ ((2 * K - 1 : ℕ) : ℝ) ^ ((19 : ℝ) / 20) := by positivity
  have hm := mul_le_mul_of_nonneg_left hK2 hpos
  linarith

end E521

namespace E521

set_option maxHeartbeats 1000000 in
/-- the count term. -/
lemma E3_bound : ∀ᶠ K : ℕ in atTop, (K : ℝ) * ((2 / AK K) * ∑ k ∈ range (pK K),
    ((N2 (LK K k) 0 0 : ℝ) / 4 ^ (LK K k)) * R522.PP (R522.SCev (k + 2))) ≤ (4 / Real.pi) * (96 / 100) := by
  set θ : ℝ := 1 / 200 with hθ
  set a : ℝ := √3 / (2 * Real.pi) + θ with ha
  set b : ℝ := (8 / Real.pi) * (1 + θ) with hb
  have hpi := Real.pi_pos
  have ha0 : 0 ≤ a := by rw [ha, hθ]; positivity
  have hb0 : 0 ≤ b := by rw [hb, hθ]; positivity
  obtain ⟨n1, hn1⟩ := eventually_atTop.mp (R522.pk_bound (θ := θ) (by rw [hθ]; norm_num))
  -- t → ∞ and log n → ∞
  have ht : Tendsto (fun K : ℕ => (tK K : ℝ)) atTop atTop := by
    have h := (tendsto_rpow_atTop (show (0:ℝ) < 19 / 20 by norm_num)).comp tendsto_nK
    refine tendsto_atTop_mono' atTop (Eventually.of_forall (fun K => ?_)) (h.atTop_add (tendsto_const_nhds (x := (-1 : ℝ))))
    simp only [Function.comp]; have := tK_ge K; linarith
  have hlog : Tendsto (fun K : ℕ => Real.log ((2 * K - 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_nK
  have hinvlog := hlog.inv_tendsto_atTop
  set C : ℝ := (2 * a * b + 2 * n1 * b) / (63 / 100) with hC
  have hsmall := (hinvlog.const_mul C).eventually (gt_mem_nhds (show C * 0 < (4 / Real.pi) / 100 by
    rw [mul_zero]; positivity))
  have hhalf := tK_half
  filter_upwards [ht.eventually_ge_atTop (4800 + n1), hlog.eventually_gt_atTop 1, hsmall,
    eventually_ge_atTop (2 * n1 + 2), hhalf] with K htK hlK hsK hK hhK
  set n := 2 * K - 1 with hn
  set t := tK K with htdef
  set p := pK K with hpdef
  have hnr : ((n : ℕ) : ℝ) = 2 * K - 1 := by rw [hn]; push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * K)]; ring
  have htn : t ≤ n := tK_le K (by omega)
  have ht2 : (t : ℝ) ≤ n / 2 := hhK
  have hpn : p = n - t := rfl
  have ht1 : 4800 + n1 ≤ t := by exact_mod_cast htK
  have hp_lt : p < n := by omega
  have hn1p : n1 ≤ p := by
    have : (n : ℝ) / 2 ≤ (p : ℝ) := by
      rw [hpn, Nat.cast_sub htn]; linarith
    have : (n1 : ℝ) ≤ n / 2 := by
      rw [hnr]
      have : ((2 * n1 + 2 : ℕ) : ℝ) ≤ K := by exact_mod_cast hK
      push_cast at this; linarith
    exact_mod_cast (by linarith : (n1 : ℝ) ≤ p)
  -- the u-bound
  have huk : ∀ k < p, (N2 (LK K k) 0 0 : ℝ) / 4 ^ (LK K k) ≤ b / ((n : ℝ) - k) := by
    intro k hk
    have hL2 : n - k ≤ 2 * (LK K k + 1) := by unfold LK; omega
    have hL3 : 2400 ≤ LK K k + 1 := by unfold LK; omega
    have hu := u_upper (LK K k)
    have hnk : (0 : ℝ) < (n : ℝ) - k := by
      have : (k : ℝ) < n := by exact_mod_cast (by omega : k < n)
      linarith
    have hL1 : (2400 : ℝ) ≤ (LK K k : ℝ) + 1 := by exact_mod_cast hL3
    have hsq : √(1 + 24 / ((LK K k : ℝ) + 1)) ≤ 1 + θ := by
      rw [hθ]; exact sqrt_bound hL1
    have hL4 : (n : ℝ) - k ≤ 2 * ((LK K k : ℝ) + 1) := by
      have : ((n - k : ℕ) : ℝ) ≤ ((2 * (LK K k + 1) : ℕ) : ℝ) := by exact_mod_cast hL2
      push_cast [Nat.cast_sub (by omega : k ≤ n)] at this; linarith
    calc (N2 (LK K k) 0 0 : ℝ) / 4 ^ (LK K k) ≤ (4 / Real.pi) / ((LK K k : ℝ) + 1) * √(1 + 24 / ((LK K k : ℝ) + 1)) := hu
      _ ≤ (4 / Real.pi) / ((LK K k : ℝ) + 1) * (1 + θ) := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ (8 / Real.pi) / ((n : ℝ) - k) * (1 + θ) := by
          apply mul_le_mul_of_nonneg_right _ (by rw [hθ]; norm_num)
          have hst := ub_step (A := 4 / Real.pi) (by positivity) (by positivity) hnk hL4
          rw [show (8 : ℝ) / Real.pi = 2 * (4 / Real.pi) by ring]
          exact hst
      _ = b / ((n : ℝ) - k) := by rw [hb]; ring
  have hcs := E521Q.count_sum (n := n) (p := p) (n0 := n1) ha0 hb0 hp_lt hn1p
    (fun k => R522.PP (R522.SCev (k + 2))) (fun k => (N2 (LK K k) 0 0 : ℝ) / 4 ^ (LK K k))
    (fun k => R522.PP_nonneg _) (fun k => R522.PP_le_one _)
    (fun k hk => by
      have := hn1 (k + 2) (by omega)
      push_cast at this; exact this)
    (fun k => by positivity) huk
  -- logarithms
  have hlogn := hlK
  have hlp : Real.log ((p : ℝ) + 1) ≤ Real.log n + 1 := by
    have hp1 : (p : ℝ) + 1 ≤ n := by exact_mod_cast (by omega : p + 1 ≤ n)
    have := Real.log_le_log (by positivity) hp1
    linarith
  have hlt : (19 / 20) * Real.log n ≤ Real.log ((n : ℝ) - p + 1) := by
    have e : (n : ℝ) - p + 1 = (t : ℝ) + 1 := by rw [hpn, Nat.cast_sub htn]; ring
    rw [e]
    have := tK_ge K
    rw [← hn] at this
    have hn1' : (0 : ℝ) < n := by
      rw [hnr]
      have : (2 : ℝ) ≤ K := by exact_mod_cast (by omega : 2 ≤ K)
      linarith
    calc (19 / 20) * Real.log n = Real.log ((n : ℝ) ^ ((19 : ℝ) / 20)) := by
          rw [Real.log_rpow hn1']
      _ ≤ Real.log ((t : ℝ) + 1) := Real.log_le_log (Real.rpow_pos_of_pos hn1' _) this
  set L := Real.log ((n : ℕ) : ℝ) with hL
  have hA : AK K = (63 / 100) * L := rfl
  have hL0 : 0 < L := by linarith
  have hKn1 : (K : ℝ) ≤ (n : ℝ) - n1 := by
    rw [hnr]; have : ((2 * n1 + 2 : ℕ) : ℝ) ≤ K := by exact_mod_cast hK
    push_cast at this; linarith
  have hKn2 : 2 * (K : ℝ) ≤ (n : ℝ) + 2 := by rw [hnr]; linarith
  have hnn1 : (0 : ℝ) < (n : ℝ) - n1 := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
    linarith
  rw [hA]
  have key := key_const
  have hLne : L ≠ 0 := hL0.ne'
  have hnn1ne : (n : ℝ) - n1 ≠ 0 := hnn1.ne'
  have hn2ne : (n : ℝ) + 2 ≠ 0 := by positivity
  have hpine : Real.pi ≠ 0 := hpi.ne'
  -- assemble
  have hbr : Real.log ((p : ℝ) + 1) + (Real.log n - Real.log ((n : ℝ) - p + 1)) + 1 ≤ (21 / 20) * L + 2 := by
    rw [hL]; linarith
  have hpart1 : (K : ℝ) * (2 / ((63 / 100) * L)) * (n1 * (b / ((n : ℝ) - n1))) ≤ (2 * n1 * b / (63 / 100)) * L⁻¹ := by
    rw [show (K : ℝ) * (2 / ((63 / 100) * L)) * (n1 * (b / ((n : ℝ) - n1))) =
      (2 * n1 * b / (63 / 100)) * L⁻¹ * (K / ((n : ℝ) - n1)) by field_simp]
    have : (K : ℝ) / ((n : ℝ) - n1) ≤ 1 := by rw [div_le_one hnn1]; exact hKn1
    have h0 : 0 ≤ (2 * n1 * b / (63 / 100)) * L⁻¹ :=
      mul_nonneg (div_nonneg (mul_nonneg (by positivity) hb0) (by norm_num)) (inv_nonneg.mpr hL0.le)
    calc (2 * n1 * b / (63 / 100)) * L⁻¹ * (K / ((n : ℝ) - n1)) ≤ (2 * n1 * b / (63 / 100)) * L⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left this h0
      _ = (2 * n1 * b / (63 / 100)) * L⁻¹ := mul_one _
  have hpart2 : (K : ℝ) * (2 / ((63 / 100) * L)) * (a * b * ((Real.log ((p : ℝ) + 1) +
      (Real.log n - Real.log ((n : ℝ) - p + 1)) + 1) / ((n : ℝ) + 2))) ≤
      (a * b / (63 / 100)) * (21 / 20) + (2 * a * b / (63 / 100)) * L⁻¹ := by
    have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hab : 0 ≤ a * b := mul_nonneg ha0 hb0
    have step : (K : ℝ) * (2 / ((63 / 100) * L)) * (a * b * ((Real.log ((p : ℝ) + 1) +
        (Real.log n - Real.log ((n : ℝ) - p + 1)) + 1) / ((n : ℝ) + 2))) ≤
        (2 * K / ((n : ℝ) + 2)) * ((a * b / (63 / 100)) * (((21 / 20) * L + 2) / L)) := by
      rw [show (K : ℝ) * (2 / ((63 / 100) * L)) * (a * b * ((Real.log ((p : ℝ) + 1) +
        (Real.log n - Real.log ((n : ℝ) - p + 1)) + 1) / ((n : ℝ) + 2))) =
        (2 * K / ((n : ℝ) + 2)) * ((a * b / (63 / 100)) * ((Real.log ((p : ℝ) + 1) +
        (Real.log n - Real.log ((n : ℝ) - p + 1)) + 1) / L)) by field_simp]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hab (by norm_num))
      exact div_le_div_of_nonneg_right hbr hL0.le
    refine step.trans ?_
    have h2K : 2 * (K : ℝ) / ((n : ℝ) + 2) ≤ 1 := by rw [div_le_one hn2]; exact hKn2
    have e2 : ((21 / 20) * L + 2) / L = 21 / 20 + 2 * L⁻¹ := by field_simp
    rw [e2]
    have h0 : 0 ≤ (a * b / (63 / 100)) * (21 / 20 + 2 * L⁻¹) :=
      mul_nonneg (div_nonneg hab (by norm_num)) (by have := inv_nonneg.mpr hL0.le; linarith)
    calc (2 * K / ((n : ℝ) + 2)) * ((a * b / (63 / 100)) * (21 / 20 + 2 * L⁻¹))
        ≤ 1 * ((a * b / (63 / 100)) * (21 / 20 + 2 * L⁻¹)) := mul_le_mul_of_nonneg_right h2K h0
      _ = _ := by ring
  have hmain : (K : ℝ) * ((2 / ((63 / 100) * L)) * ∑ k ∈ range p,
      ((N2 (LK K k) 0 0 : ℝ) / 4 ^ (LK K k)) * R522.PP (R522.SCev (k + 2))) ≤
      (a * b / (63 / 100)) * (21 / 20) + C * L⁻¹ := by
    have hcs' := mul_le_mul_of_nonneg_left hcs (show (0 : ℝ) ≤ (K : ℝ) * (2 / ((63 / 100) * L)) from
      mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by norm_num) (mul_nonneg (by norm_num) hL0.le)))
    rw [← mul_assoc]
    refine hcs'.trans ?_
    rw [mul_add]
    have : C * L⁻¹ = (2 * n1 * b / (63 / 100)) * L⁻¹ + (2 * a * b / (63 / 100)) * L⁻¹ := by
      rw [hC]; ring
    linarith
  refine hmain.trans ?_
  have hab_eq : (a * b / (63 / 100)) * (21 / 20) = (4 / Real.pi) * (2 * a * (1 + θ) * (21 / 20) / (63 / 100)) := by
    rw [hb]; field_simp; ring
  rw [hab_eq]
  have hk2 : 2 * a * (1 + θ) * (21 / 20) / (63 / 100) ≤ 95 / 100 := by
    rw [ha, hθ]; exact key
  have h4p : 0 < 4 / Real.pi := by positivity
  have := mul_le_mul_of_nonneg_left hk2 h4p.le
  have hsK' : C * L⁻¹ < (4 / Real.pi) / 100 := hsK
  linarith

/-- **`μ(H_K) ≥ (4/π)/(40 K)` eventually.** -/
theorem Hev_lower : ∀ᶠ K : ℕ in atTop, (4 / Real.pi) / (60 * K) ≤ μS.real (Hev K) := by
  have h1 := E1_small.eventually (gt_mem_nhds (show (0:ℝ) < (4 / Real.pi) / 200 by positivity))
  have h2 := E2_small.eventually (gt_mem_nhds (show (0:ℝ) < (4 / Real.pi) / 200 by positivity))
  have h3 := E3_bound
  have h4 : Tendsto (fun K : ℕ => (K : ℝ) * ((4 / Real.pi) / (K + 4))) atTop (𝓝 (4 / Real.pi)) := by
    have : Tendsto (fun K : ℕ => (4 / Real.pi) * ((K : ℝ) / (K + 4))) atTop (𝓝 ((4 / Real.pi) * 1)) := by
      refine tendsto_const_nhds.mul ?_
      have := tendsto_natCast_div_add_atTop (4 : ℝ)
      exact this
    rw [mul_one] at this
    refine this.congr' (Eventually.of_forall (fun K => ?_)); ring
  have h4' := h4.eventually (lt_mem_nhds (show (4 / Real.pi) * (99 / 100) < 4 / Real.pi by
    have := Real.pi_pos; nlinarith [div_pos (show (0:ℝ) < 4 by norm_num) this]))
  have hlamev : ∀ᶠ K : ℕ in atTop, 1 ≤ lamK K := by
    filter_upwards [eventually_ge_atTop 1] with K hK
    unfold lamK; exact Nat.one_le_iff_ne_zero.mpr (by
      rw [ne_eq, Nat.ceil_eq_zero, not_le]
      have : (1 : ℝ) ≤ ((2 * K - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * K - 1)
      positivity)
  have hAev : ∀ᶠ K : ℕ in atTop, 0 < AK K := by
    filter_upwards [eventually_ge_atTop 2] with K hK
    unfold AK; apply mul_pos (by norm_num); apply Real.log_pos
    exact_mod_cast (by omega : 1 < 2 * K - 1)
  filter_upwards [h1, h2, h3, h4', hlamev, hAev, eventually_ge_atTop 2] with K e1 e2 e3 e4 hl hA hK
  have hpn : pK K + 2 ≤ 2 * K := by
    have ht1 : 1 ≤ tK K := by
      unfold tK
      apply Nat.le_floor
      push_cast
      exact Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ 2 * K - 1)) (by norm_num)
    unfold pK; omega
  have hdet := Hev_det K (by omega) hl hA hpn
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  rw [div_le_iff₀ (by positivity)]
  have : (4 / Real.pi) / 60 ≤ (K : ℝ) * μS.real (Hev K) := by
    have := mul_le_mul_of_nonneg_left hdet hK0.le
    rw [mul_sub, mul_sub, mul_sub] at this
    have hc4 : 0 < 4 / Real.pi := by positivity
    linarith
  linarith

end E521
end

end S_P12

-- ===== Q1 =====
section S_Q1

/-! A second-moment (Kochen–Stone type) lower bound for unions (original). -/

open MeasureTheory Finset

namespace E521Q

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- `(∑ μ H_m)² ≤ (∑∑ μ(H_m ∩ H_m')) · μ(⋃ H_m)` for finitely many measurable sets. -/
theorem second_moment (s : Finset ℕ) (H : ℕ → Set Ω) (hH : ∀ m, MeasurableSet (H m)) :
    (∑ m ∈ s, μ.real (H m)) ^ 2 ≤
      (∑ m ∈ s, ∑ m' ∈ s, μ.real (H m ∩ H m')) * μ.real (⋃ m ∈ s, H m) := by
  classical
  set U := ⋃ m ∈ s, H m with hU
  have hUm : MeasurableSet U := Finset.measurableSet_biUnion s (fun m _ => hH m)
  set Z : Ω → ℝ := fun ω => ∑ m ∈ s, (H m).indicator (fun _ => (1 : ℝ)) ω with hZ
  have hZi : ∀ m, Integrable ((H m).indicator (fun _ => (1 : ℝ))) μ :=
    fun m => (integrable_const 1).indicator (hH m)
  have hZint : Integrable Z μ := integrable_finset_sum s (fun m _ => hZi m)
  have hZ_eq : ∀ ω, Z ω = Z ω * U.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ U
    · rw [Set.indicator_of_mem hω, mul_one]
    · rw [Set.indicator_of_notMem hω, mul_zero]
      simp only [hZ]
      apply sum_eq_zero; intro m hm
      rw [Set.indicator_of_notMem]
      intro h; apply hω; rw [hU]; exact Set.mem_biUnion hm h
  have hEZ : ∫ ω, Z ω ∂μ = ∑ m ∈ s, μ.real (H m) := by
    simp only [hZ]; rw [integral_finset_sum s (fun m _ => hZi m)]
    apply sum_congr rfl; intro m _; rw [integral_indicator_const _ (hH m)]; simp
  have hZ2 : ∀ ω, Z ω ^ 2 = ∑ m ∈ s, ∑ m' ∈ s, (H m ∩ H m').indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    simp only [hZ]
    rw [sq, sum_mul_sum]
    apply sum_congr rfl; intro m _; apply sum_congr rfl; intro m' _
    by_cases h1 : ω ∈ H m <;> by_cases h2 : ω ∈ H m' <;> simp [Set.indicator, h1, h2]
  have hEZ2 : ∫ ω, Z ω ^ 2 ∂μ = ∑ m ∈ s, ∑ m' ∈ s, μ.real (H m ∩ H m') := by
    simp_rw [hZ2]
    rw [integral_finset_sum s (fun m _ => integrable_finset_sum s (fun m' _ =>
      (integrable_const 1).indicator ((hH m).inter (hH m'))))]
    apply sum_congr rfl; intro m _
    rw [integral_finset_sum s (fun m' _ => (integrable_const 1).indicator ((hH m).inter (hH m')))]
    apply sum_congr rfl; intro m' _
    rw [integral_indicator_const _ ((hH m).inter (hH m'))]; simp
  -- Cauchy–Schwarz
  have hZb : ∀ ω, |Z ω| ≤ s.card := by
    intro ω
    simp only [hZ]
    rw [abs_of_nonneg (sum_nonneg (fun m _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _))]
    calc ∑ m ∈ s, (H m).indicator (fun _ => (1 : ℝ)) ω ≤ ∑ m ∈ s, (1 : ℝ) :=
          sum_le_sum (fun m _ => Set.indicator_le_self' (fun _ _ => zero_le_one) ω |>.trans (le_refl _))
      _ = s.card := by simp
  have hmemZ : MemLp Z 2 μ := by
    refine MemLp.of_bound hZint.aestronglyMeasurable (s.card : ℝ) (Filter.Eventually.of_forall
      (fun ω => by rw [Real.norm_eq_abs]; exact hZb ω))
  have hmemU : MemLp (U.indicator (fun _ => (1 : ℝ))) 2 μ :=
    (memLp_const (1 : ℝ)).indicator hUm
  have h2 : ENNReal.ofReal 2 = 2 := by simp
  rw [← h2] at hmemZ hmemU
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) (μ := μ)
    (f := Z) (g := U.indicator (fun _ => (1 : ℝ)))
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun ω => sum_nonneg (fun m _ =>
      Set.indicator_nonneg (fun _ _ => zero_le_one) ω)))
    (Filter.Eventually.of_forall (fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω))
    hmemZ hmemU
  have hInt : ∫ ω, Z ω * U.indicator (fun _ => (1 : ℝ)) ω ∂μ = ∫ ω, Z ω ∂μ := by
    congr 1; funext ω; exact (hZ_eq ω).symm
  rw [hInt, hEZ] at hCS
  have hU2 : ∫ ω, U.indicator (fun _ => (1 : ℝ)) ω ^ (2 : ℝ) ∂μ = μ.real U := by
    rw [← integral_indicator_one hUm]
    congr 1; funext ω
    by_cases h : ω ∈ U <;> simp [Set.indicator, h]
  have hZ2' : ∫ ω, Z ω ^ (2 : ℝ) ∂μ = ∑ m ∈ s, ∑ m' ∈ s, μ.real (H m ∩ H m') := by
    rw [← hEZ2]; congr 1; funext ω; rw [Real.rpow_two]
  rw [hU2, hZ2'] at hCS
  have h0 : 0 ≤ ∑ m ∈ s, μ.real (H m) := sum_nonneg (fun m _ => measureReal_nonneg)
  have hA : 0 ≤ ∑ m ∈ s, ∑ m' ∈ s, μ.real (H m ∩ H m') :=
    sum_nonneg (fun m _ => sum_nonneg (fun m' _ => measureReal_nonneg))
  have hB : 0 ≤ μ.real U := measureReal_nonneg
  calc (∑ m ∈ s, μ.real (H m)) ^ 2
      ≤ ((∑ m ∈ s, ∑ m' ∈ s, μ.real (H m ∩ H m')) ^ (1 / (2 : ℝ)) * μ.real U ^ (1 / (2 : ℝ))) ^ 2 := by
        exact pow_le_pow_left₀ h0 hCS 2
    _ = (∑ m ∈ s, ∑ m' ∈ s, μ.real (H m ∩ H m')) * μ.real U := by
        rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (μ.real U ^ (1 / (2 : ℝ))),
          ← Real.rpow_mul hA, ← Real.rpow_mul hB]
        norm_num

end E521Q

end S_Q1

-- ===== Q3 =====
section S_Q3

/-! From second moments to a positive-probability `limsup` (original). -/

open MeasureTheory Finset Filter Topology

namespace E521Q

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- If on every tail window the second-moment ratio is eventually `≥ δ`, then `μ (limsup H) ≥ δ`. -/
theorem limsup_pos (H : ℕ → Set Ω) (hH : ∀ m, MeasurableSet (H m)) {δ : ℝ} (hδ : 0 < δ)
    (hratio : ∀ N, ∃ M, N ≤ M ∧ δ * (∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, μ.real (H m ∩ H m')) ≤
      (∑ m ∈ Icc N M, μ.real (H m)) ^ 2 ∧ 0 < ∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, μ.real (H m ∩ H m')) :
    δ ≤ μ.real (Filter.limsup H atTop) := by
  -- each tail union has measure ≥ δ
  have htail : ∀ N, δ ≤ μ.real (⋃ m ≥ N, H m) := by
    intro N
    obtain ⟨M, hNM, h1, h2⟩ := hratio N
    have hsm := second_moment μ (Icc N M) H hH
    have hU : μ.real (⋃ m ∈ Icc N M, H m) ≤ μ.real (⋃ m ≥ N, H m) := by
      apply measureReal_mono
      · intro ω hω
        simp only [Set.mem_iUnion, mem_Icc] at hω ⊢
        obtain ⟨m, hm, h⟩ := hω; exact ⟨m, hm.1, h⟩
      · exact measure_ne_top _ _
    have : δ ≤ μ.real (⋃ m ∈ Icc N M, H m) := by
      by_contra hc; push Not at hc
      have := mul_lt_mul_of_pos_left hc h2
      nlinarith
    linarith
  -- limsup = ⋂_N ⋃_{m ≥ N}, decreasing
  rw [Filter.limsup_eq_iInf_iSup_of_nat]
  have hanti : Antitone (fun N => ⋃ m ≥ N, H m) := by
    intro a b hab ω hω
    simp only [Set.mem_iUnion] at hω ⊢
    obtain ⟨m, hm, h⟩ := hω; exact ⟨m, le_trans hab hm, h⟩
  have hmeas : ∀ N, MeasurableSet (⋃ m ≥ N, H m) := fun N =>
    MeasurableSet.iUnion (fun m => MeasurableSet.iUnion (fun _ => hH m))
  have ht := tendsto_measure_iInter_atTop (μ := μ) (fun N => (hmeas N).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  have e : (⋂ N, ⋃ m ≥ N, H m) = ⨅ N, ⨆ m ≥ N, H m := by
    simp [Set.iInf_eq_iInter, Set.iSup_eq_iUnion]
  rw [← e]
  have ht' : Tendsto (fun N => μ.real (⋃ m ≥ N, H m)) atTop (𝓝 (μ.real (⋂ N, ⋃ m ≥ N, H m))) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht
  exact ge_of_tendsto' ht' htail

end E521Q

end S_Q3

-- ===== P13 =====
section S_P13

/-! A positive-probability `limsup` of the good events (Kochen–Stone, original). -/

open Finset MeasureTheory Filter Topology

noncomputable section

namespace E521

lemma meas_cnt (K : ℕ) : Measurable (fun ω => (cnt K ω : ℝ)) := by
  classical
  have e : (fun ω => (cnt K ω : ℝ)) = fun ω => ∑ k ∈ range (pK K),
      ((if ω ∈ Iev k then (1 : ℝ) else 0) + (if ω ∈ Ialt k then (1 : ℝ) else 0)) := by
    funext ω; unfold cnt
    rw [sum_add_distrib, Nat.cast_add, card_filter, card_filter]; push_cast; rfl
  rw [e]
  refine Finset.measurable_sum _ (fun k _ => ?_)
  exact (Measurable.ite (meas_Iev k) measurable_const measurable_const).add
    (Measurable.ite (meas_Ialt k) measurable_const measurable_const)

lemma meas_Gev (K : ℕ) : MeasurableSet (Gev K) := by
  simp only [Gev, Set.setOf_forall]
  refine MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ => measurableSet_lt ?_ measurable_const
  exact (Finset.measurable_sum _ (fun i _ => measurable_eR _)).abs

lemma meas_Gev' (K : ℕ) : MeasurableSet (Gev' K) := by
  simp only [Gev', Set.setOf_forall]
  refine MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ => measurableSet_lt ?_ measurable_const
  exact (Finset.measurable_sum _ (fun i _ => (measurable_eR _).const_mul _)).abs

lemma meas_Hev (K : ℕ) : MeasurableSet (Hev K) :=
  (((meas_coneE _ _ _).inter (meas_Gev K)).inter (meas_Gev' K)).inter
    (measurableSet_lt (meas_cnt K) measurable_const)

/-- harmonic upper bound. -/
lemma harm_upper (M : ℕ) : ∑ d ∈ range (M + 1), 1 / ((d : ℝ) + 1) ≤ Real.log (M + 1) + 1 := by
  rw [range_eq_Ico, ← Ico_union_Ico_eq_Ico (show 0 ≤ 1 by omega) (show 1 ≤ M + 1 by omega),
    sum_union (Ico_disjoint_Ico_consecutive _ _ _)]
  have h := E521Q.harm_Ico 1 (M + 1) le_rfl (by omega)
  simp only [Nat.Ico_succ_singleton, sum_singleton, Nat.cast_zero, zero_add, div_one, Nat.cast_one,
    Real.log_one, sub_zero] at h ⊢
  push_cast at h
  linarith

/-- the pair bound in symmetric form. -/
lemma pair_sym (m m' : ℕ) :
    μS.real (Hev m ∩ Hev m') ≤
      (if m ≤ m' then (20 / Real.pi) ^ 2 * (1 / ((m : ℝ) + 1) * (1 / (((m' - m : ℕ) : ℝ) + 1))) else 0) +
      (if m' ≤ m then (20 / Real.pi) ^ 2 * (1 / ((m' : ℝ) + 1) * (1 / (((m - m' : ℕ) : ℝ) + 1))) else 0) := by
  have hp := Real.pi_pos
  have key : ∀ a b : ℕ, a ≤ b → μS.real (Hev a ∩ Hev b) ≤
      (20 / Real.pi) ^ 2 * (1 / ((a : ℝ) + 1) * (1 / (((b - a : ℕ) : ℝ) + 1))) := by
    intro a b hab
    refine (Hev_pair a b hab).trans ?_
    have h1 := u_crude a
    have h2 := u_crude (b - a)
    have h0 : (0 : ℝ) ≤ (N2 (b - a) 0 0 : ℝ) / 4 ^ (b - a) := by positivity
    calc ((N2 a 0 0 : ℝ) / 4 ^ a) * ((N2 (b - a) 0 0 : ℝ) / 4 ^ (b - a))
        ≤ ((20 / Real.pi) / (a + 1)) * ((20 / Real.pi) / (((b - a : ℕ) : ℝ) + 1)) :=
          mul_le_mul h1 h2 h0 (by positivity)
      _ = _ := by ring
  rcases le_total m m' with h | h
  · have := key m m' h
    have hz : 0 ≤ (if m' ≤ m then (20 / Real.pi) ^ 2 * (1 / ((m' : ℝ) + 1) * (1 / (((m - m' : ℕ) : ℝ) + 1))) else 0) := by
      split_ifs <;> positivity
    rw [if_pos h]; linarith
  · have := key m' m h
    rw [Set.inter_comm] at this
    have hz : 0 ≤ (if m ≤ m' then (20 / Real.pi) ^ 2 * (1 / ((m : ℝ) + 1) * (1 / (((m' - m : ℕ) : ℝ) + 1))) else 0) := by
      split_ifs <;> positivity
    rw [if_pos h]; linarith

/-- one-sided row sum. -/
lemma row_sum (N M m : ℕ) :
    ∑ m' ∈ Icc N M, (if m ≤ m' then (1 / (((m' - m : ℕ) : ℝ) + 1)) else 0) ≤ Real.log (M + 1) + 1 := by
  classical
  refine le_trans ?_ (harm_upper M)
  rw [← sum_filter]
  have : ∑ m' ∈ (Icc N M).filter (fun m' => m ≤ m'), 1 / (((m' - m : ℕ) : ℝ) + 1) =
      ∑ d ∈ ((Icc N M).filter (fun m' => m ≤ m')).image (fun m' => m' - m), 1 / ((d : ℝ) + 1) := by
    rw [sum_image]
    intro x hx y hy hxy
    simp only [coe_filter, Set.mem_setOf_eq, mem_Icc] at hx hy
    simp only at hxy; omega
  rw [this]
  apply sum_le_sum_of_subset_of_nonneg
  · intro d hd
    simp only [mem_image, mem_filter, mem_Icc] at hd
    obtain ⟨x, ⟨⟨_, hx⟩, _⟩, rfl⟩ := hd
    rw [mem_range]; omega
  · intro _ _ _; positivity

theorem double_sum_le (N M : ℕ) :
    ∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, μS.real (Hev m ∩ Hev m') ≤
      2 * (20 / Real.pi) ^ 2 * (Real.log (M + 1) + 1) ^ 2 := by
  have hp := Real.pi_pos
  set A : ℝ := (20 / Real.pi) ^ 2
  set g : ℕ → ℕ → ℝ := fun m m' =>
    if m ≤ m' then A * (1 / ((m : ℝ) + 1) * (1 / (((m' - m : ℕ) : ℝ) + 1))) else 0 with hg
  have h1 : ∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, μS.real (Hev m ∩ Hev m') ≤
      ∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, (g m m' + g m' m) :=
    sum_le_sum fun m _ => sum_le_sum fun m' _ => pair_sym m m'
  have hrow : ∀ m, ∑ m' ∈ Icc N M, g m m' ≤ A * (1 / ((m : ℝ) + 1)) * (Real.log (M + 1) + 1) := by
    intro m
    have e : ∑ m' ∈ Icc N M, g m m' =
        A * (1 / ((m : ℝ) + 1)) * ∑ m' ∈ Icc N M, (if m ≤ m' then (1 / (((m' - m : ℕ) : ℝ) + 1)) else 0) := by
      rw [mul_sum]; apply sum_congr rfl; intro m' _
      simp only [hg]; split_ifs <;> ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (row_sum N M m) (by positivity)
  have hG : ∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, g m m' ≤ A * (Real.log (M + 1) + 1) ^ 2 := by
    calc ∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, g m m'
        ≤ ∑ m ∈ Icc N M, A * (1 / ((m : ℝ) + 1)) * (Real.log (M + 1) + 1) := sum_le_sum fun m _ => hrow m
      _ = A * (Real.log (M + 1) + 1) * ∑ m ∈ Icc N M, 1 / ((m : ℝ) + 1) := by
          rw [mul_sum]; apply sum_congr rfl; intro m _; ring
      _ ≤ A * (Real.log (M + 1) + 1) * (Real.log (M + 1) + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by
            have : 0 ≤ Real.log ((M : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M])
            positivity)
          refine le_trans ?_ (harm_upper M)
          apply sum_le_sum_of_subset_of_nonneg
          · intro x hx; rw [mem_Icc] at hx; rw [mem_range]; omega
          · intro _ _ _; positivity
      _ = A * (Real.log (M + 1) + 1) ^ 2 := by ring
  have hsw : ∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, g m' m = ∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, g m m' := sum_comm
  have : ∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, (g m m' + g m' m) =
      ∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, g m m' + ∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, g m' m := by
    rw [← sum_add_distrib]; apply sum_congr rfl; intro m _; rw [sum_add_distrib]
  rw [this, hsw] at h1
  linarith

/-- `∑_{K ∈ [N, M]} 1/(K+1) ≥ log (M+2) - log (N+1)`. -/
lemma harm_lower (N M : ℕ) (h : N ≤ M) :
    Real.log ((M : ℝ) + 2) - Real.log ((N : ℝ) + 1) ≤ ∑ K ∈ Icc N M, 1 / ((K : ℝ) + 1) := by
  induction M, h using Nat.le_induction with
  | base =>
    simp only [Icc_self, sum_singleton]
    rw [← Real.log_div (by positivity) (by positivity)]
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < ((N : ℝ) + 2) / ((N : ℝ) + 1) by positivity)
    have e : ((N : ℝ) + 2) / ((N : ℝ) + 1) - 1 = 1 / ((N : ℝ) + 1) := by field_simp; ring
    linarith
  | succ M hNM ih =>
    rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), sum_insert (by simp)]
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < ((M + 1 : ℕ) + 2 : ℝ) / ((M : ℝ) + 2) by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at this
    have e : (((M + 1 : ℕ) : ℝ) + 2) / ((M : ℝ) + 2) - 1 = 1 / (((M + 1 : ℕ) : ℝ) + 1) := by
      push_cast; field_simp; ring
    push_cast at this e ⊢
    linarith

/-- **positive-probability limsup.** -/
theorem limsup_Hev_pos : ∃ δ : ℝ, 0 < δ ∧ δ ≤ μS.real (Filter.limsup Hev atTop) := by
  have hp := Real.pi_pos
  set c : ℝ := (4 / Real.pi) / 60 with hc
  set A : ℝ := (20 / Real.pi) ^ 2 with hA
  have hc0 : 0 < c := by positivity
  have hA0 : 0 < A := by positivity
  set δ : ℝ := c ^ 2 / (8 * A) with hδ
  have hδ0 : 0 < δ := by positivity
  refine ⟨δ, hδ0, E521Q.limsup_pos μS Hev meas_Hev hδ0 ?_⟩
  obtain ⟨K0, hK0⟩ := eventually_atTop.mp Hev_lower
  intro N
  set N' := max N (max K0 1) with hN'
  have hlog : Tendsto (fun M : ℕ => Real.log ((M : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  obtain ⟨M, hM1, hM2⟩ := ((hlog.eventually_ge_atTop (2 * Real.log ((N' : ℝ) + 1) + 2)).and
    (eventually_ge_atTop N')).exists
  refine ⟨M, le_trans (le_max_left _ _) hM2, ?_, ?_⟩
  · -- lower bound for the first moment
    have hS : c * (Real.log ((M : ℝ) + 2) - Real.log ((N' : ℝ) + 1)) ≤ ∑ m ∈ Icc N M, μS.real (Hev m) := by
      have hsub : Icc N' M ⊆ Icc N M := Icc_subset_Icc (le_max_left _ _) le_rfl
      refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => measureReal_nonneg))
      have hh := harm_lower N' M hM2
      calc c * (Real.log ((M : ℝ) + 2) - Real.log ((N' : ℝ) + 1)) ≤ c * ∑ m ∈ Icc N' M, 1 / ((m : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hh hc0.le
        _ = ∑ m ∈ Icc N' M, c * (1 / ((m : ℝ) + 1)) := by rw [mul_sum]
        _ ≤ ∑ m ∈ Icc N' M, μS.real (Hev m) := by
            apply sum_le_sum; intro m hm; rw [mem_Icc] at hm
            have hmK : K0 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm.1
            have hm1 : (1 : ℝ) ≤ m := by
              have : 1 ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm.1
              exact_mod_cast this
            have := hK0 m hmK
            have e : (4 / Real.pi) / (60 * m) = c * (1 / (m : ℝ)) := by rw [hc]; field_simp
            rw [e] at this
            refine le_trans ?_ this
            apply mul_le_mul_of_nonneg_left _ hc0.le
            exact one_div_le_one_div_of_le (by linarith) (by linarith)
    have hD := double_sum_le N M
    have hlN : 0 ≤ Real.log ((N' : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N'])
    have hlM : Real.log ((M : ℝ) + 1) ≤ Real.log ((M : ℝ) + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlM0 : 0 ≤ Real.log ((M : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M])
    -- (log(M+1)+1) ≤ 2 (log(M+2) - log(N'+1))
    have hcmp : Real.log ((M : ℝ) + 1) + 1 ≤ 2 * (Real.log ((M : ℝ) + 2) - Real.log ((N' : ℝ) + 1)) := by
      linarith
    have hX : 0 ≤ Real.log ((M : ℝ) + 1) + 1 := by linarith
    have hsq : (Real.log ((M : ℝ) + 1) + 1) ^ 2 ≤ 4 * (Real.log ((M : ℝ) + 2) - Real.log ((N' : ℝ) + 1)) ^ 2 := by
      nlinarith
    have hS0 : 0 ≤ c * (Real.log ((M : ℝ) + 2) - Real.log ((N' : ℝ) + 1)) := by
      apply mul_nonneg hc0.le; linarith
    have hS2 := pow_le_pow_left₀ hS0 hS 2
    calc δ * ∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, μS.real (Hev m ∩ Hev m')
        ≤ δ * (2 * A * (Real.log ((M : ℝ) + 1) + 1) ^ 2) := mul_le_mul_of_nonneg_left hD hδ0.le
      _ ≤ δ * (2 * A * (4 * (Real.log ((M : ℝ) + 2) - Real.log ((N' : ℝ) + 1)) ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ hδ0.le
          exact mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (c * (Real.log ((M : ℝ) + 2) - Real.log ((N' : ℝ) + 1))) ^ 2 := by
          rw [hδ]; field_simp; ring
      _ ≤ _ := hS2
  · -- positivity of the double sum via the diagonal at `M`
    have hMK : K0 ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM2
    have hM1' : 1 ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM2
    have hNM : N ≤ M := le_trans (le_max_left _ _) hM2
    have hpos : 0 < μS.real (Hev M ∩ Hev M) := by
      rw [Set.inter_self]
      refine lt_of_lt_of_le ?_ (hK0 M hMK)
      have : (0 : ℝ) < M := by exact_mod_cast hM1'
      positivity
    have hmem : M ∈ Icc N M := mem_Icc.mpr ⟨hNM, le_rfl⟩
    have h1 : μS.real (Hev M ∩ Hev M) ≤ ∑ m' ∈ Icc N M, μS.real (Hev M ∩ Hev m') :=
      single_le_sum (f := fun m' => μS.real (Hev M ∩ Hev m')) (fun _ _ => measureReal_nonneg) hmem
    have h2 : ∑ m' ∈ Icc N M, μS.real (Hev M ∩ Hev m') ≤ ∑ m ∈ Icc N M, ∑ m' ∈ Icc N M, μS.real (Hev m ∩ Hev m') :=
      single_le_sum (f := fun m => ∑ m' ∈ Icc N M, μS.real (Hev m ∩ Hev m'))
        (fun _ _ => sum_nonneg fun _ _ => measureReal_nonneg) hmem
    linarith

end E521
end

end S_P13

-- ===== F1 =====
section S_F1

/-! **Erdős 521 is false**: almost surely `R_n / log n` does not tend to `2/π` (original). -/

open Finset MeasureTheory Filter Topology

noncomputable section

namespace E521

/-- **The disproof.** -/
theorem erdos521_false :
    ¬ (∀ᵐ ω ∂μS, Tendsto (fun n : ℕ => ((fR n ω).roots.card : ℝ) / Real.log n) atTop (𝓝 (2 / Real.pi))) := by
  intro hconv
  obtain ⟨δ, hδ, hpos⟩ := limsup_Hev_pos
  have hlin : Tendsto (fun K : ℕ => 2 * K - 1) atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun a b h => by omega) (fun b => ⟨b + 1, by omega⟩)
  have hc : (635 / 1000 : ℝ) < 2 / Real.pi := by
    rw [lt_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d4]
  have hlogT : Tendsto (fun K : ℕ => Real.log ((2 * K - 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hlin)
  have hlog : ∀ᶠ K : ℕ in atTop, 2 < (5 / 1000) * Real.log ((2 * K - 1 : ℕ) : ℝ) :=
    (hlogT.const_mul_atTop (by norm_num)).eventually_gt_atTop 2
  have hnull : μS (Filter.limsup Hev atTop) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hconv] with ω hω
    intro hmem
    rw [mem_limsup_iff_frequently_mem] at hmem
    have hev := hω.eventually (lt_mem_nhds hc)
    have hev2 := hlin.eventually hev
    obtain ⟨K, hKH, ⟨hK2, hK3⟩, hK1⟩ := (hmem.and_eventually ((hev2.and hlog).and (eventually_ge_atTop 2))).exists
    have hroots := roots_on_H K (by omega) ω hKH (tK_le K (by omega))
    have hlogpos : 0 < Real.log ((2 * K - 1 : ℕ) : ℝ) := by
      apply Real.log_pos; exact_mod_cast (by omega : 1 < 2 * K - 1)
    have hK2' : (635 / 1000 : ℝ) < ((fR (2 * K - 1) ω).roots.card : ℝ) / Real.log ((2 * K - 1 : ℕ) : ℝ) := hK2
    rw [lt_div_iff₀ hlogpos] at hK2'
    unfold AK at hroots
    linarith
  have := hpos
  rw [Measure.real, hnull] at this
  simp at this
  linarith

end E521
end

end S_F1

-- ===== F2 =====
section S_F2

open MeasureTheory Filter Topology

namespace E521

theorem disproof' :
    ¬ (∀ᵐ ω ∂signMeasure', Tendsto (fun n : ℕ => (realRootCount' n ω : ℝ) / Real.log n) atTop
      (𝓝 (2 / Real.pi))) := by
  intro h
  apply erdos521_false
  rw [← signMeasure'_eq]
  simpa only [realRootCount'_eq] using h

end E521

end S_F2

theorem OMA.disproof : ¬ (type_of% @OMA.S_erdos_521.main) := by
  intro h
  exact E521.disproof' h
