import OMAStatements.S_oeis_a202303

-- Problem: A202303: Drop the last digit of A023110(n).
-- Credit: @sobrien032

/-!
N. J. A. Sloane's A202303 deletes the last digit from each square in
A023110. Colin Barker conjectured its recurrence in 2014. The current
one-based sequence has four leading zeros, following Georg Fischer's
2022 correction. With this convention the recurrence starts at 23.

Robert Israel's seven Pell families for A031149 enumerate the pairs
(x,y) satisfying x² = 10y² + d for 0 ≤ d ≤ 9 and x > 0. Decimal
truncation keeps y². Advancing seven places applies the same linear
map to (x,y), so three such steps give the recurrence for y². The
exception at 22 is checked explicitly below.

Sources: https://oeis.org/A202303 and https://oeis.org/A031149
Lean proof by Codex, adapted from the team's A023110 classification.
-/

namespace Trunc

abbrev P := ℕ × ℕ

def sol (v : P) : Prop :=
  10 * v.2 ^ 2 ≤ v.1 ^ 2 ∧ v.1 ^ 2 ≤ 10 * v.2 ^ 2 + 9

def next (v : P) : P := (19*v.1 + 60*v.2, 6*v.1 + 19*v.2)

def pair : ℕ → P
  | 0 => (1, 0)
  | 1 => (2, 0)
  | 2 => (3, 0)
  | 3 => (4, 1)
  | 4 => (7, 2)
  | 5 => (13, 4)
  | 6 => (16, 5)
  | n+7 => next (pair n)

theorem pair_step (n : ℕ) : pair (n+7) = next (pair n) := rfl

end Trunc

namespace Trunc

theorem predecessor {v : P} (hv : sol v) (hx : 19 ≤ v.1) :
    ∃ u : P, sol u ∧ 0 < u.1 ∧ u.1 < v.1 ∧ next u = v := by
  rcases v with ⟨x, y⟩
  change 10 * y ^ 2 ≤ x ^ 2 ∧ x ^ 2 ≤ 10 * y ^ 2 + 9 at hv
  change 19 ≤ x at hx
  obtain ⟨hlo, hhi⟩ := hv
  have hx2 := Nat.pow_le_pow_left hx 2
  have ha : 60 * y < 19 * x := by
    by_contra! h
    nlinarith only [hlo, hx2, Nat.pow_le_pow_left h 2]
  have hb : 6 * x ≤ 19 * y := by
    by_contra! h
    have hgap : 19 * y + 1 ≤ 6 * x := by omega
    have hsq := Nat.pow_le_pow_left hgap 2
    have hu : y ≤ 7 := by
      by_contra! hh
      nlinarith only [hhi, hsq, hh, Nat.pow_le_pow_left hh 2]
    have hl : 6 ≤ y := by
      by_contra! hh
      have hy5 : y ≤ 5 := by omega
      nlinarith only [hx2, hhi, Nat.pow_le_pow_left hy5 2]
    interval_cases y
    · have hx20 : 20 ≤ x := by omega
      nlinarith only [hhi, Nat.pow_le_pow_left hx20 2]
    · have hx23 : 23 ≤ x := by omega
      nlinarith only [hhi, Nat.pow_le_pow_left hx23 2]
  have hdrop : 3 * x < 10 * y := by
    by_contra! h
    nlinarith only [hhi, hx2, Nat.pow_le_pow_left h 2]
  let a := 19 * x - 60 * y
  let b := 19 * y - 6 * x
  have hax : a + 60 * y = 19 * x := Nat.sub_add_cancel ha.le
  have hby : b + 6 * x = 19 * y := Nat.sub_add_cancel hb
  have hnextX : 19 * a + 60 * b = x := by omega
  have hnextY : 6 * a + 19 * b = y := by omega
  have hnorm : (19 * a + 60 * b) ^ 2 + 10 * b ^ 2 =
      10 * (6 * a + 19 * b) ^ 2 + a ^ 2 := by ring
  rw [hnextX, hnextY] at hnorm
  refine ⟨(a, b), ?_, ?_, ?_, ?_⟩
  · change 10 * b ^ 2 ≤ a ^ 2 ∧ a ^ 2 ≤ 10 * b ^ 2 + 9
    constructor <;> nlinarith only [hnorm, hlo, hhi]
  · change 0 < a
    omega
  · change a < x
    omega
  · exact Prod.ext hnextX hnextY

end Trunc

namespace Trunc

private theorem next_sol (v : P) (h : sol v) : sol (Trunc.next v) := by
  rcases v with ⟨x,y⟩
  rcases h with ⟨h₁,h₂⟩
  change 10*y^2 ≤ x^2 at h₁
  change x^2 ≤ 10*y^2 + 9 at h₂
  change 10*(6*x+19*y)^2 ≤ (19*x+60*y)^2 ∧ (19*x+60*y)^2 ≤ 10*(6*x+19*y)^2+9
  have he : (19*x+60*y)^2 + 10*y^2 = 10*(6*x+19*y)^2 + x^2 := by ring
  omega

private theorem small_pair (x y : ℕ) (hx : 0 < x) (hb : x < 19) (hv : sol (x,y)) :
    ∃ n, pair n = (x,y) := by
  obtain ⟨h₁,h₂⟩ := hv
  change 10*y^2 ≤ x^2 at h₁
  change x^2 ≤ 10*y^2 + 9 at h₂
  have hy : y < 6 := by
    by_contra! h
    have hl := Nat.pow_le_pow_left h 2
    have hu := Nat.pow_le_pow_left (show x ≤ 18 by omega) 2
    omega
  have checked : ∀ a : Fin 19, ∀ b : Fin 6, 0 < a.val → 10*b.val^2 ≤ a.val^2 →
      a.val^2 ≤ 10*b.val^2+9 → ∃ i : Fin 7, pair i.val = (a.val,b.val) := by decide
  obtain ⟨i,hi⟩ := checked ⟨x,hb⟩ ⟨y,hy⟩ hx h₁ h₂
  exact ⟨i.val,hi⟩

theorem exists_pair {v : P} (hv : sol v) (hx : 0 < v.1) : ∃ n, pair n = v := by
  rcases v with ⟨x,y⟩
  induction x using Nat.strong_induction_on generalizing y with
  | h x ih =>
    by_cases hge : 19 ≤ x
    · obtain ⟨⟨u,w⟩,hu,hu0,hu_lt,hstep⟩ := predecessor hv hge
      obtain ⟨n,hn⟩ : ∃ n, pair n = (u,w) := by
        apply ih u hu_lt <;> assumption
      exact ⟨n+7, by rw [pair_step, hn, hstep]⟩
    · exact small_pair x y hx (by omega) hv

theorem pair_sol (n : ℕ) : sol (pair n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hs : n < 7
    · interval_cases n <;> norm_num [sol, pair]
    · have hv := next_sol _ (ih (n-7) (by omega))
      simpa only [← pair_step, Nat.sub_add_cancel (show 7 ≤ n by omega)] using hv

end Trunc

namespace Trunc

open OMA.S_oeis_a202303

private theorem pair_order (n : ℕ) :
    (pair n).1 < (pair (n+1)).1 ∧ (pair n).2 ≤ (pair (n+1)).2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < 7
    · interval_cases n <;> decide
    · obtain ⟨k, rfl⟩ : ∃ k, n = k+7 := ⟨n-7, by omega⟩
      obtain ⟨hx, hy⟩ := ih k (by omega)
      rw [show k+7+1 = (k+1)+7 by omega, pair_step, pair_step]
      dsimp only [Trunc.next]
      constructor <;> omega

private def orderedSquares : ℕ → ℕ
  | 0 => 0
  | n+1 => (pair n).1 ^ 2

private theorem orderedSquares_strict : StrictMono orderedSquares := by
  apply strictMono_nat_of_lt_succ
  intro n
  cases n with
  | zero => decide
  | succ n =>
    change (pair n).1 ^ 2 < (pair (n+1)).1 ^ 2
    exact (sq_lt_sq₀ (Nat.zero_le _) (Nat.zero_le _)).2 (pair_order n).1

private theorem sol_div (v : P) : sol v ↔ v.1 ^ 2 / 10 = v.2 ^ 2 := by
  unfold sol
  omega

private theorem nth_ordered (n : ℕ) : Nat.nth IsA023110 n = orderedSquares n := by
  have hr : Set.range orderedSquares = Set.ofPred IsA023110 := by
    ext m
    change (∃ k, orderedSquares k = m) ↔ IsA023110 m
    constructor
    · rintro ⟨k, rfl⟩
      cases k with
      | zero => exact ⟨⟨0, rfl⟩, ⟨0, rfl⟩⟩
      | succ k =>
        constructor
        · exact (isSquare_iff_exists_sq _).2 ⟨(pair k).1, rfl⟩
        · exact (isSquare_iff_exists_sq _).2 ⟨(pair k).2, (sol_div _).1 (pair_sol k)⟩
    · intro hm
      obtain ⟨x, rfl⟩ := (isSquare_iff_exists_sq _).1 hm.1
      obtain ⟨y, hy⟩ := (isSquare_iff_exists_sq _).1 hm.2
      by_cases hx : x = 0
      · subst x
        exact ⟨0, rfl⟩
      · obtain ⟨k, hk⟩ := exists_pair (v := (x, y)) ((sol_div _).2 hy) (Nat.pos_of_ne_zero hx)
        refine ⟨k+1, ?_⟩
        change (pair k).1 ^ 2 = x ^ 2
        rw [hk]
  have hinf : (Set.ofPred IsA023110).Infinite := by
    rw [← hr]
    exact Set.infinite_range_of_injective orderedSquares_strict.injective
  have heq := (orderedSquares_strict.range_inj (Nat.nth_strictMono hinf)).1
    (hr.trans (Nat.range_nth_of_infinite hinf).symm)
  exact (congrFun heq n).symm

/-- The original sequence includes zero. At index k+2 the truncated value
is the squared second coordinate of the kth positive orbit pair. -/
theorem term (k : ℕ) : a (k+2) = (pair k).2 ^ 2 := by
  change Nat.nth IsA023110 (k+1) / 10 = (pair k).2 ^ 2
  rw [nth_ordered]
  exact (sol_div _).1 (pair_sol k)

/-- The preceding index misses the proposed recurrence by exactly one. -/
theorem discrepancy_at_22 :
    (a 22 : ℤ) - (1443 * a 15 - 1443 * a 8 + a 1) = 1 := by
  have first : a 1 = 0 := by
    change Nat.nth IsA023110 0 / 10 = 0
    rw [nth_ordered]
    rfl
  rw [term 20, term 13, term 6, first]
  decide

end Trunc

namespace Trunc

/-- The characteristic polynomial for the squared second coordinates of three Pell steps. -/
theorem square_recurrence (v : P) :
    ((next (next (next v))).2 : ℤ)^2 =
      1443*((next (next v)).2 : ℤ)^2 - 1443*((next v).2 : ℤ)^2 + (v.2 : ℤ)^2 := by
  simp only [next, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

end Trunc

open Trunc OMA.S_oeis_a202303 in
theorem OMA.solution : type_of% @OMA.S_oeis_a202303.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k+23 := ⟨n-23, by omega⟩
  change (a ((k+7+7+7)+2) : ℤ) =
    1443 * a ((k+23)-7) - 1443 * a ((k+23)-14) + a ((k+23)-21)
  rw [show k+23-7 = (k+7+7)+2 by omega, show k+23-14 = (k+7)+2 by omega,
    show k+23-21 = k+2 by omega]
  simp only [term, Nat.cast_pow, pair_step]
  exact square_recurrence (pair k)
