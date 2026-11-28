import OMAStatements.S_oeis_a269585

-- Problem: A269585, length-five arrays over 0..n whose repeated values (the values of the adjacent equal pairs, read left to right) step by 0, +1 or -1.
-- Credit: @mattdorman (the owner of the agent is credited as the solver)
--
-- Proof. Move the Fin sums to sums over range (n + 1). Split the indicator by which adjacent pairs
-- (a,b), (b,c), (c,d), (d,e) are equal (`ind_eq`): eleven patterns have at most one run of equal
-- entries and carry no constraint (`nc`); five patterns have two runs, whose values v (earlier)
-- and w (later) are constrained (`cr`). Reflecting every value x -> m - 1 - x preserves the
-- adjacent equalities and turns the factor [v = w + 1] into [w = v + 1] (`box_bad`), so every
-- factor has the later variable bare and `good_sum` evaluates the box sum by repeated
-- `Finset.sum_ite_eq` to the quintic closed form. The recurrence and the generating function
-- follow from it: its sixth difference vanishes, and the first seven coefficients of
-- (1 - x)^6 A(x) are the numerator's.

namespace OMA.A269585
open OMA.S_oeis_a269585

/-- The indicator `[x = y]`. -/
def δ (x y : ℕ) : ℚ := if x = y then 1 else 0

theorem self_ne1 (x : ℕ) : x = x + 1 ↔ False := ⟨fun h => by omega, False.elim⟩
theorem self_ne2 (x : ℕ) : x = x + 2 ↔ False := ⟨fun h => by omega, False.elim⟩
theorem self_ne1' (x : ℕ) : x + 1 = x ↔ False := ⟨fun h => by omega, False.elim⟩

/-- `repeats` with natural-number entries. -/
def repeatsN (a b c d e : ℕ) : List ℕ :=
  (if b = a then [a] else []) ++ (if c = b then [b] else []) ++
  (if d = c then [c] else []) ++ (if e = d then [d] else [])

theorem repeats_eq {q : ℕ} (a b c d e : Fin q) :
    repeats a b c d e = repeatsN a b c d e := by
  simp [repeats, repeatsN, Fin.ext_iff]

/-- The eleven equality patterns of adjacent pairs with at most one run of equal entries. -/
def nc (a b c d e : ℕ) : ℚ :=
  (1 - δ a b) * (1 - δ b c) * (1 - δ c d) * (1 - δ d e)
  + δ a b * (1 - δ b c) * (1 - δ c d) * (1 - δ d e)
  + (1 - δ a b) * δ b c * (1 - δ c d) * (1 - δ d e)
  + (1 - δ a b) * (1 - δ b c) * δ c d * (1 - δ d e)
  + (1 - δ a b) * (1 - δ b c) * (1 - δ c d) * δ d e
  + δ a b * δ b c * (1 - δ c d) * (1 - δ d e)
  + (1 - δ a b) * δ b c * δ c d * (1 - δ d e)
  + (1 - δ a b) * (1 - δ b c) * δ c d * δ d e
  + δ a b * δ b c * δ c d * (1 - δ d e)
  + (1 - δ a b) * δ b c * δ c d * δ d e
  + δ a b * δ b c * δ c d * δ d e

/-- The five patterns with two runs, the factor `F v w` relating the run values. -/
def cr (a b c d e : ℕ) (F : ℕ → ℕ → ℚ) : ℚ :=
  δ a b * (1 - δ b c) * δ c d * (1 - δ d e) * F a c
  + δ a b * (1 - δ b c) * (1 - δ c d) * δ d e * F a d
  + (1 - δ a b) * δ b c * (1 - δ c d) * δ d e * F b d
  + δ a b * δ b c * (1 - δ c d) * δ d e * F b d
  + δ a b * (1 - δ b c) * δ c d * δ d e * F a c

theorem link (x y : ℕ) :
    (if x ≤ y + 1 ∧ y ≤ x + 1 then (1 : ℚ) else 0) = δ y x + δ y (x + 1) + δ x (y + 1) := by
  unfold δ
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

theorem δ_one {x y : ℕ} (h : x = y) : δ x y = 1 := by simp [δ, h]
theorem δ_zero {x y : ℕ} (h : x ≠ y) : δ x y = 0 := by simp [δ, h]

theorem ind_eq (a b c d e : ℕ) :
    (if allowed (repeatsN a b c d e) then (1 : ℚ) else 0) =
      nc a b c d e + cr a b c d e (fun v w => δ w v + δ w (v + 1) + δ v (w + 1)) := by
  unfold nc cr repeatsN
  by_cases h1 : b = a <;> by_cases h2 : c = b <;> by_cases h3 : d = c <;> by_cases h4 : e = d <;>
  · (try simp only [if_pos h1])
    (try simp only [if_neg h1])
    (try simp only [if_pos h2])
    (try simp only [if_neg h2])
    (try simp only [if_pos h3])
    (try simp only [if_neg h3])
    (try simp only [if_pos h4])
    (try simp only [if_neg h4])
    simp only [if_true, if_false, List.nil_append, List.cons_append, allowed]
    (try simp only [eq_true h1, δ_one h1.symm])
    (try simp only [eq_false h1, δ_zero (Ne.symm h1)])
    (try simp only [eq_true h2, δ_one h2.symm])
    (try simp only [eq_false h2, δ_zero (Ne.symm h2)])
    (try simp only [eq_true h3, δ_one h3.symm])
    (try simp only [eq_false h3, δ_zero (Ne.symm h3)])
    (try simp only [eq_true h4, δ_one h4.symm])
    (try simp only [eq_false h4, δ_zero (Ne.symm h4)])
    (try simp only [h1, h2, h3, h4])
    (try simp only [le_refl, Nat.le_succ, and_self, true_and, and_true, self_ne1, self_ne1', ne_eq,
      not_false_eq_true, decide_true, decide_eq_true_eq, Bool.and_true, Bool.true_and, Bool.and_self])
    (try simp only [decide_eq_true_eq, Bool.and_true, Bool.true_and, Bool.and_self, link])
    (try norm_num)
    (try ring)

theorem mem_range_add (x k m : ℕ) : x + k ∈ Finset.range m ↔ x ∈ Finset.range (m - k) := by
  simp only [Finset.mem_range]; omega

theorem range_inter (p q : ℕ) : Finset.range p ∩ Finset.range q = Finset.range (min p q) := by
  ext x; simp only [Finset.mem_inter, Finset.mem_range]; omega

theorem good_sum (t : ℕ) :
    (∑ a ∈ Finset.range (t + 1), ∑ b ∈ Finset.range (t + 1), ∑ c ∈ Finset.range (t + 1),
      ∑ d ∈ Finset.range (t + 1), ∑ e ∈ Finset.range (t + 1),
        (nc a b c d e + cr a b c d e (fun v w => δ w v + δ w (v + 1)) + cr a b c d e (fun v w => δ w (v + 1)))) = (t:ℚ)^5 + 5*(t:ℚ)^4 + 7*(t:ℚ)^3 + 12*(t:ℚ)^2 + 6*(t:ℚ) + 1 := by
  unfold nc cr δ
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_const, nsmul_eq_mul, Finset.sum_ite_mem,
    Finset.inter_self, Finset.sum_ite_irrel, Finset.sum_const_zero, mem_range_add, range_inter,
    Finset.card_range]
  have m5 : min (t + 1) t = t := by omega
  have m6 : min t (t + 1) = t := by omega
  simp only [if_true, Nat.add_sub_cancel, m5, m6, min_self, Finset.card_range, self_ne1, self_ne2,
    if_false, Finset.sum_const_zero, sub_zero]
  push_cast
  ring

/-- The box sum over `{0, ..., m-1}^5`. -/
def box (m : ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℕ → ℚ) : ℚ :=
  ∑ a ∈ Finset.range m, ∑ b ∈ Finset.range m, ∑ c ∈ Finset.range m, ∑ d ∈ Finset.range m,
    ∑ e ∈ Finset.range m, F a b c d e

theorem box_add (m : ℕ) (F H : ℕ → ℕ → ℕ → ℕ → ℕ → ℚ) :
    box m (fun a b c d e => F a b c d e + H a b c d e) = box m F + box m H := by
  simp only [box, Finset.sum_add_distrib]

theorem r1 (m : ℕ) (g : ℕ → ℚ) :
    ∑ x ∈ Finset.range m, g x = ∑ x ∈ Finset.range m, g (m - 1 - x) :=
  (Finset.sum_range_reflect g m).symm

theorem box_reflect (m : ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℕ → ℚ) :
    box m F = box m (fun a b c d e => F (m-1-a) (m-1-b) (m-1-c) (m-1-d) (m-1-e)) := by
  unfold box
  rw [r1 m (fun a => ∑ b ∈ Finset.range m, ∑ c ∈ Finset.range m, ∑ d ∈ Finset.range m,
    ∑ e ∈ Finset.range m, F a b c d e)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [r1 m (fun b => ∑ c ∈ Finset.range m, ∑ d ∈ Finset.range m, ∑ e ∈ Finset.range m,
    F (m-1-a) b c d e)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [r1 m (fun c => ∑ d ∈ Finset.range m, ∑ e ∈ Finset.range m, F (m-1-a) (m-1-b) c d e)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [r1 m (fun d => ∑ e ∈ Finset.range m, F (m-1-a) (m-1-b) (m-1-c) d e)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [r1 m (fun e => F (m-1-a) (m-1-b) (m-1-c) (m-1-d) e)]

theorem dr {m x y : ℕ} (hx : x < m) (hy : y < m) : δ (m-1-x) (m-1-y) = δ x y := by
  unfold δ; split_ifs <;> first | rfl | (exfalso; omega)

theorem dr1 {m v w : ℕ} (hv : v < m) (hw : w < m) : δ (m-1-v) (m-1-w+1) = δ w (v+1) := by
  unfold δ; split_ifs <;> first | rfl | (exfalso; omega)

theorem box_bad (m : ℕ) :
    box m (fun a b c d e => cr a b c d e (fun v w => δ v (w + 1))) =
      box m (fun a b c d e => cr a b c d e (fun v w => δ w (v + 1))) := by
  rw [box_reflect]
  unfold box
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl
    fun c hc => Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun e he => ?_
  simp only [Finset.mem_range] at ha hb hc hd he
  simp only [cr, dr ha hb, dr hb hc, dr hc hd, dr hd he, dr1 ha hc, dr1 ha hd, dr1 hb hd]

theorem count_box (k : ℕ) :
    count k = box (k + 1) (fun a b c d e => if allowed (repeatsN a b c d e) then (1 : ℚ) else 0) := by
  simp only [count, box, repeats_eq]
  rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin (k+1), ∑ c : Fin (k+1), ∑ d : Fin (k+1),
    ∑ e : Fin (k+1), if allowed (repeatsN a ↑b ↑c ↑d ↑e) then (1 : ℚ) else 0) (k + 1)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.sum_univ_eq_sum_range (fun b => ∑ c : Fin (k+1), ∑ d : Fin (k+1),
    ∑ e : Fin (k+1), if allowed (repeatsN a b ↑c ↑d ↑e) then (1 : ℚ) else 0) (k + 1)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fin.sum_univ_eq_sum_range (fun c => ∑ d : Fin (k+1),
    ∑ e : Fin (k+1), if allowed (repeatsN a b c ↑d ↑e) then (1 : ℚ) else 0) (k + 1)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fin.sum_univ_eq_sum_range (fun d =>
    ∑ e : Fin (k+1), if allowed (repeatsN a b c d ↑e) then (1 : ℚ) else 0) (k + 1)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Fin.sum_univ_eq_sum_range (fun e => if allowed (repeatsN a b c d e) then (1 : ℚ) else 0) (k + 1)]

theorem count_eq (n : ℕ) : count n = (n:ℚ)^5 + 5*n^4 + 7*n^3 + 12*n^2 + 6*n + 1 := by
  rw [count_box, ← good_sum n]
  have e1 : (fun a b c d e => if allowed (repeatsN a b c d e) then (1 : ℚ) else 0) =
      fun a b c d e => (nc a b c d e + cr a b c d e (fun v w => δ w v + δ w (v + 1))) +
        cr a b c d e (fun v w => δ v (w + 1)) := by
    funext a b c d e; rw [ind_eq]; unfold cr; ring
  have e2 : (fun a b c d e => nc a b c d e + cr a b c d e (fun v w => δ w v + δ w (v + 1)) + cr a b c d e (fun v w => δ w (v + 1))) =
      fun a b c d e => (nc a b c d e + cr a b c d e (fun v w => δ w v + δ w (v + 1))) +
        cr a b c d e (fun v w => δ w (v + 1)) := by
    funext a b c d e; ring
  rw [e1, box_add, box_bad, ← box_add, ← e2]
  rfl

theorem terms_zero : terms 0 = 0 := rfl

theorem terms_succ (n : ℕ) :
    terms (n + 1) = ((n:ℚ)+1)^5 + 5*((n:ℚ)+1)^4 + 7*((n:ℚ)+1)^3 + 12*((n:ℚ)+1)^2 + 6*((n:ℚ)+1) + 1 := by
  rw [terms, count_eq (n + 1)]
  push_cast
  ring

theorem recurrence (n : ℕ) : terms (n+7) = 6*terms (n+6) - 15*terms (n+5) +
    20*terms (n+4) - 15*terms (n+3) + 6*terms (n+2) - terms (n+1) := by
  rw [show n + 7 = (n + 6) + 1 by omega, show n + 6 = (n + 5) + 1 by omega,
    show n + 5 = (n + 4) + 1 by omega, show n + 4 = (n + 3) + 1 by omega,
    show n + 3 = (n + 2) + 1 by omega, show n + 2 = (n + 1) + 1 by omega]
  simp only [terms_succ]
  push_cast
  ring

open PowerSeries in
theorem gf : (1-X)^6 * mk terms = (X * (32 + 37*X + 70*X^2 - 20*X^3 + 2*X^4 - X^5) : PowerSeries ℚ) := by
  set A := mk terms with hA
  have hl : (1 - X) ^ 6 * A =
      A - C (6:ℚ) * (A * X ^ 1) + C (15:ℚ) * (A * X ^ 2) - C (20:ℚ) * (A * X ^ 3) +
        C (15:ℚ) * (A * X ^ 4) - C (6:ℚ) * (A * X ^ 5) + A * X ^ 6 := by
    simp only [map_ofNat]
    ring
  have hr : (X * (32 + 37*X + 70*X^2 - 20*X^3 + 2*X^4 - X^5) : PowerSeries ℚ) =
      C (32:ℚ) * X ^ 1 + C (37:ℚ) * X ^ 2 + C (70:ℚ) * X ^ 3 - C (20:ℚ) * X ^ 4 + C (2:ℚ) * X ^ 5 - C (1:ℚ) * X ^ 6 := by
    simp only [map_ofNat, map_one]
    ring
  rw [hl, hr, hA]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  rcases n with _ | _ | _ | _ | _ | _ | _ | m
  all_goals try (simp [terms_zero, terms_succ, coeff_C] <;> norm_num <;> done)
  · have e0 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 = (m + 6) + 1 := by omega
    have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 = (m + 5) + 1 := by omega
    have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 2 = (m + 4) + 1 := by omega
    have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 3 = (m + 3) + 1 := by omega
    have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 4 = (m + 2) + 1 := by omega
    have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 5 = (m + 1) + 1 := by omega
    have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m + 1 := by omega
    simp only [e1, e2, e3, e4, e5, e6, show 1 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega, show 2 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega,
      show 3 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega, show 4 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega, show 5 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega,
      show 6 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega, if_true, coeff_C, Nat.add_one_ne_zero, if_false]
    rw [e0, terms_succ, terms_succ, terms_succ, terms_succ, terms_succ, terms_succ, terms_succ]
    push_cast
    ring

end OMA.A269585

theorem OMA.solution : type_of% @OMA.S_oeis_a269585.main :=
  ⟨OMA.A269585.count_eq, OMA.A269585.recurrence, OMA.A269585.gf⟩
