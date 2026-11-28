import FormalConjectures.OEIS.«153330»

-- Reduction OeisA153330.conjecture2.R2 of Collatz step differences, conjecture2
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Collatz step differences: the values 1, 6, 16 and 3 from the bound 4/3 on the Collatz ratio

`a n` is the number of Collatz steps of `n + 1` minus that of `n`. The target says that the value
`1` occurs only at `n = 1`, the value `6` only at `n = 2`, the value `16` only at `n = 8`, and the
value `3` only at `n = 4, 5`.

For a terminating `x` with `U` tripling steps and `E` halvings put `R x = 2^E / 3^U`. Telescoping
gives `R x ≥ x` (lemma `tr_ratio`).

* `H1` (open, the only open input; it is a stronger statement than the target, not a part of it):
  `R x < 4/3 * x` for every terminating `x`. This is, character for character, hypothesis `H2` of
  the merged reduction `OeisA153330.conjecture3.R1` (by @mbilenko03), so one proof serves both
  trees. Numerically `R x / x ≤ 1.2532` for `x ≤ 3 * 10^5`, with the maximum at `x = 993`.
* `H2` (elementary, known): if `3^(K+1)` divides `2^s + 1` then `3^K` divides `s`. This is the
  lifting-the-exponent lemma for the prime `3` (equivalently, `2` is a primitive root modulo every
  power of `3`).

What `main` proves from them:

1. With `v = a n` and `(U, E)`, `(U', E')` the exponents of `n`, `n + 1`, the two-sided bounds give
   `6^U * 2^v * 3n < 6^U' * 4(n+1)` and `6^U' * 3(n+1) < 6^U * 2^v * 4n` (lemma `six_v`). Hence
   `v = 1` forces `n < 2`, `v = 6` forces `n ≤ 2`, `v = 16` forces `n ≤ 18`, and `v = 3` forces
   `U' = U + 1`, `E' = E + 2` (lemma `v_three`). The small cases are computed.
2. Value `3`, `n = 2m` even (lemma `even_case`): the pair `(m, 3m+2)` has exponents `(U, E)` and
   `(U, E+2)`. If `m` is even then either `U = 0`, so `m` and `3m+2` are powers of two and `m = 2`,
   or `R m ≥ m + 2/3`, which contradicts `H1` at `3m+2`. If `m > 1` is odd, the pair
   `((3m+1)/2, 3(3m+1)/2 + 2)` has the same shape with `U` one smaller: induction on `U`.
3. Value `3`, `n = 2w - 1` odd (lemma `odd3`): `w` has exponents `(u+2, e+2)` and `Y = 3w - 1` has
   `(u, e)`. `H1` at `w` gives `R Y < Y + 1`. Lemma `shape` classifies such `Y`: all the odd steps
   of `Y` but the last are followed by a single halving, up to one exception, so
   `2^e + 2^g = 3^(u+1) * w` with `g = u` or `g = u - 1`. Hence `w = 2^g * z` with
   `3^K * z = 2^s + 1`, where `K = u + 1`, `s = e - g`, and `z` has exponents `(K+1, s+2)`.
   Lemma `inv_bound` follows the trajectory of `z` while it shadows that of the 2-adic number
   `3^(-K)` and gives `2^s ≤ 4 * ∏_{j<K} (1 + 3^j)`. But `H2` gives `s ≥ 3^(K-1)`, which is
   larger for `K ≥ 3` (lemma `big`). The cases `K = 1, 2` are finite and leave `z = 3`, `n = 5`.

So `H1` alone decides the whole target; the bound `4/3` is used only at `n`, `n + 1`, `3m + 2`
and `w` above.
-/

namespace OMA.R_OeisA153330_conjecture2_R2

open OeisA153330

/-- Open (shared with `OeisA153330.conjecture3.R1`, there `H2`): for every terminating `n ≥ 1` with
`k` Collatz steps of which `U` are odd, `3 * 2^(k - U) < 4 * 3^U * n`. -/
def H1 : Prop :=
  ∀ n k : ℕ, 0 < n → collatzSteps n = some k →
    3 * 2 ^ (k - ((Finset.range k).filter (fun i => collatzStep^[i] n % 2 = 1)).card) <
      4 * (3 ^ ((Finset.range k).filter (fun i => collatzStep^[i] n % 2 = 1)).card * n)

/-- Elementary (lifting the exponent at the prime `3`): if `3^(K+1)` divides `2^s + 1`, then
`3^K` divides `s`. -/
def H2 : Prop := ∀ K s : ℕ, 3 ^ (K + 1) ∣ 2 ^ s + 1 → 3 ^ K ∣ s

lemma steps_spec {x k : ℕ} (h : collatzSteps x = some k) :
    x ≠ 0 ∧ collatzStep^[k] x = 1 ∧ ∀ j < k, collatzStep^[j] x ≠ 1 := by
  unfold collatzSteps at h
  split_ifs at h with h0 hex
  obtain rfl := Option.some.inj h
  exact ⟨h0, Nat.sInf_mem hex, fun j hj hj1 => Nat.notMem_of_lt_sInf hj hj1⟩

lemma steps_of {x k : ℕ} (h0 : x ≠ 0) (h1 : collatzStep^[k] x = 1)
    (h2 : ∀ j < k, collatzStep^[j] x ≠ 1) : collatzSteps x = some k := by
  have hex : ∃ j, collatzStep^[j] x = 1 := ⟨k, h1⟩
  rw [collatzSteps, if_neg h0, if_pos hex]
  congr 1
  apply le_antisymm (Nat.sInf_le (show k ∈ {j : ℕ | collatzStep^[j] x = 1} from h1))
  by_contra hlt
  exact h2 _ (not_le.1 hlt) (Nat.sInf_mem hex)

lemma steps_shift {x k : ℕ} (h : collatzSteps x = some k) (hx1 : x ≠ 1) :
    ∃ k', k = k' + 1 ∧ collatzSteps (collatzStep x) = some k' := by
  obtain ⟨h0, h1, h2⟩ := steps_spec h
  cases k with
  | zero => exact absurd h1 hx1
  | succ k' =>
    refine ⟨k', rfl, steps_of ?_ ?_ ?_⟩
    · unfold collatzStep
      split_ifs <;> omega
    · rw [← Function.iterate_succ_apply]; exact h1
    · intro j hj
      rw [← Function.iterate_succ_apply]
      exact h2 (j + 1) (by omega)

lemma card_shift (x k : ℕ) :
    ((Finset.range (k + 1)).filter (fun i => collatzStep^[i] x % 2 = 1)).card =
      ((Finset.range k).filter (fun i => collatzStep^[i] (collatzStep x) % 2 = 1)).card +
        (if x % 2 = 1 then 1 else 0) := by
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ']
  rfl

lemma tr_of_steps {x k : ℕ} (h : collatzSteps x = some k) :
    ∃ U E, k = U + E ∧ (collatzSteps x = some (U + E) ∧ ((Finset.range (U + E)).filter (fun i => collatzStep^[i] x % 2 = 1)).card = U) := by
  have key : ∀ c, c = ((Finset.range k).filter (fun i => collatzStep^[i] x % 2 = 1)).card →
      ∃ U E, k = U + E ∧ (collatzSteps x = some (U + E) ∧ ((Finset.range (U + E)).filter (fun i => collatzStep^[i] x % 2 = 1)).card = U) := by
    intro c hc
    have hle : c ≤ k := by
      rw [hc]
      exact (Finset.card_filter_le _ _).trans (by simp)
    refine ⟨c, k - c, by omega, ?_, ?_⟩
    · rw [show c + (k - c) = k by omega]; exact h
    · rw [show c + (k - c) = k by omega]; exact hc.symm
  exact key _ rfl

lemma tr_one {U E : ℕ} (h : (collatzSteps 1 = some (U + E) ∧ ((Finset.range (U + E)).filter (fun i => collatzStep^[i] 1 % 2 = 1)).card = U)) : U = 0 ∧ E = 0 := by
  by_contra hne
  exact (steps_spec h.1).2.2 0 (by omega) rfl

lemma tr_even {x U E : ℕ} (h : (collatzSteps x = some (U + E) ∧ ((Finset.range (U + E)).filter (fun i => collatzStep^[i] x % 2 = 1)).card = U)) (hx : x % 2 = 0) :
    ∃ E', E = E' + 1 ∧ (collatzSteps (x / 2) = some (U + E') ∧ ((Finset.range (U + E')).filter (fun i => collatzStep^[i] (x / 2) % 2 = 1)).card = U) := by
  obtain ⟨hs, hc⟩ := h
  obtain ⟨k', hk, hs'⟩ := steps_shift hs (by omega)
  have hstep : collatzStep x = x / 2 := by simp [collatzStep, hx]
  rw [hk, card_shift, hstep, if_neg (by omega), add_zero] at hc
  rw [hstep] at hs'
  have hle : U ≤ k' := by
    rw [← hc]
    exact (Finset.card_filter_le _ _).trans (by simp)
  refine ⟨k' - U, by omega, ?_, ?_⟩
  · rw [show U + (k' - U) = k' by omega]; exact hs'
  · rw [show U + (k' - U) = k' by omega]; exact hc

lemma tr_odd {x U E : ℕ} (h : (collatzSteps x = some (U + E) ∧ ((Finset.range (U + E)).filter (fun i => collatzStep^[i] x % 2 = 1)).card = U)) (hx : x % 2 = 1) (hx1 : x ≠ 1) :
    ∃ U', U = U' + 1 ∧ (collatzSteps (3 * x + 1) = some (U' + E) ∧ ((Finset.range (U' + E)).filter (fun i => collatzStep^[i] (3 * x + 1) % 2 = 1)).card = U') := by
  obtain ⟨hs, hc⟩ := h
  obtain ⟨k', hk, hs'⟩ := steps_shift hs hx1
  have hstep : collatzStep x = 3 * x + 1 := by simp [collatzStep, hx]
  rw [hk, card_shift, hstep, if_pos hx] at hc
  rw [hstep] at hs'
  have key : ∀ c, c = ((Finset.range k').filter
      (fun i => collatzStep^[i] (3 * x + 1) % 2 = 1)).card →
      ∃ U', U = U' + 1 ∧ (collatzSteps (3 * x + 1) = some (U' + E) ∧ ((Finset.range (U' + E)).filter (fun i => collatzStep^[i] (3 * x + 1) % 2 = 1)).card = U') := by
    intro c hcc
    have hle : c ≤ k' := by
      rw [hcc]
      exact (Finset.card_filter_le _ _).trans (by simp)
    rw [← hcc] at hc
    refine ⟨c, by omega, ?_, ?_⟩
    · rw [show c + E = k' by omega]; exact hs'
    · rw [show c + E = k' by omega]; exact hcc.symm
  exact key _ rfl

lemma tr_pos {x U E : ℕ} (h : (collatzSteps x = some (U + E) ∧ ((Finset.range (U + E)).filter (fun i => collatzStep^[i] x % 2 = 1)).card = U)) : 0 < x :=
  Nat.pos_of_ne_zero (steps_spec h.1).1

lemma tr_ratio : ∀ (k x U E : ℕ), U + E = k → (collatzSteps x = some (U + E) ∧ ((Finset.range (U + E)).filter (fun i => collatzStep^[i] x % 2 = 1)).card = U) → 3 ^ U * x ≤ 2 ^ E := by
  intro k
  induction k with
  | zero =>
    intro x U E hk h
    obtain rfl : U = 0 := by omega
    obtain rfl : E = 0 := by omega
    have := (steps_spec h.1).2.1
    simp at this
    simp [this]
  | succ k ih =>
    intro x U E hk h
    by_cases hx1 : x = 1
    · subst hx1
      have := tr_one h
      omega
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx
    · obtain ⟨E', rfl, h'⟩ := tr_even h hx
      have := ih (x / 2) U E' (by omega) h'
      have hd : 2 * (x / 2) = x := by omega
      calc 3 ^ U * x = 2 * (3 ^ U * (x / 2)) := by
            rw [← mul_assoc, mul_comm 2, mul_assoc, hd]
        _ ≤ 2 * 2 ^ E' := Nat.mul_le_mul_left 2 this
        _ = 2 ^ (E' + 1) := by ring
    · obtain ⟨U', rfl, h'⟩ := tr_odd h hx hx1
      have := ih (3 * x + 1) U' E (by omega) h'
      calc 3 ^ (U' + 1) * x = 3 ^ U' * (3 * x) := by ring
        _ ≤ 3 ^ U' * (3 * x + 1) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ 2 ^ E := this

lemma tr_h1 (h1 : H1) {x U E : ℕ} (h : (collatzSteps x = some (U + E) ∧ ((Finset.range (U + E)).filter (fun i => collatzStep^[i] x % 2 = 1)).card = U)) : 3 * 2 ^ E < 4 * (3 ^ U * x) := by
  have := h1 x (U + E) (tr_pos h) h.1
  rw [h.2, Nat.add_sub_cancel_left] at this
  exact this

lemma tr_zero : ∀ (E x : ℕ), (collatzSteps x = some (0 + E) ∧ ((Finset.range (0 + E)).filter (fun i => collatzStep^[i] x % 2 = 1)).card = 0) → x = 2 ^ E := by
  intro E
  induction E with
  | zero =>
    intro x h
    have := (steps_spec h.1).2.1
    simpa using this
  | succ E ih =>
    intro x h
    by_cases hx1 : x = 1
    · subst hx1
      have := tr_one h
      omega
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx
    · obtain ⟨E', hE, h'⟩ := tr_even h hx
      obtain rfl : E' = E := by omega
      have := ih (x / 2) h'
      rw [pow_succ]
      omega
    · obtain ⟨U', hU, -⟩ := tr_odd h hx hx1
      omega

lemma tr_evenIneq : ∀ (x U E : ℕ), (collatzSteps x = some (U + E) ∧ ((Finset.range (U + E)).filter (fun i => collatzStep^[i] x % 2 = 1)).card = U) → x % 2 = 0 →
    U = 0 ∨ 3 ^ U * (3 * x + 2) ≤ 3 * 2 ^ E := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro U E h hx
    have hpos := tr_pos h
    obtain ⟨E', rfl, h'⟩ := tr_even h hx
    have hd : x = 2 * (x / 2) := by omega
    by_cases hy1 : x / 2 = 1
    · rw [hy1] at h'
      exact Or.inl (tr_one h').1
    rcases Nat.mod_two_eq_zero_or_one (x / 2) with hy | hy
    · rcases ih (x / 2) (by omega) U E' h' hy with h0 | hin
      · exact Or.inl h0
      · right
        have hp : 0 < 3 ^ U := by positivity
        calc 3 ^ U * (3 * x + 2) ≤ 2 * (3 ^ U * (3 * (x / 2) + 2)) := by
              rw [← mul_assoc, mul_comm 2 (3 ^ U), mul_assoc]
              exact Nat.mul_le_mul_left _ (by omega)
          _ ≤ 2 * (3 * 2 ^ E') := Nat.mul_le_mul_left 2 hin
          _ = 3 * 2 ^ (E' + 1) := by ring
    · obtain ⟨U', rfl, h''⟩ := tr_odd h' hy hy1
      right
      have := tr_ratio _ _ _ _ rfl h''
      calc 3 ^ (U' + 1) * (3 * x + 2) = 6 * (3 ^ U' * (3 * (x / 2) + 1)) := by
            rw [show 3 * x + 2 = 2 * (3 * (x / 2) + 1) by omega]; ring
        _ ≤ 6 * 2 ^ E' := Nat.mul_le_mul_left 6 this
        _ = 3 * 2 ^ (E' + 1) := by ring

lemma even_case (h1 : H1) : ∀ (U m E : ℕ), (collatzSteps m = some (U + E) ∧ ((Finset.range (U + E)).filter (fun i => collatzStep^[i] m % 2 = 1)).card = U) → (collatzSteps (3 * m + 2) = some (U + (E + 2)) ∧ ((Finset.range (U + (E + 2))).filter (fun i => collatzStep^[i] (3 * m + 2) % 2 = 1)).card = U) → m = 2 := by
  intro U
  induction U using Nat.strong_induction_on with
  | _ U ih =>
    intro m E hm hy
    rcases Nat.mod_two_eq_zero_or_one m with hpar | hpar
    · rcases tr_evenIneq m U E hm hpar with h0 | hin
      · subst h0
        have e1 := tr_zero _ _ hm
        have e2 := tr_zero _ _ hy
        rw [pow_succ, pow_succ] at e2
        omega
      · have := tr_h1 h1 hy
        rw [pow_succ, pow_succ] at this
        omega
    · by_cases hm1 : m = 1
      · subst hm1
        obtain ⟨rfl, rfl⟩ := tr_one hm
        have := tr_zero _ _ hy
        norm_num at this
      · obtain ⟨U', rfl, hz⟩ := tr_odd hm hpar hm1
        obtain ⟨E0, rfl, hh⟩ := tr_even hz (by omega)
        obtain ⟨U'', hU'', hz2⟩ := tr_odd hy (by omega) (by omega)
        have eU : U'' = U' := by omega
        rw [eU] at hz2
        obtain ⟨E1, hE1, hh2⟩ := tr_even hz2 (by omega)
        have eE : E1 = E0 + 2 := by omega
        rw [eE] at hh2
        rw [show (3 * (3 * m + 2) + 1) / 2 = 3 * ((3 * m + 1) / 2) + 2 by omega] at hh2
        have := ih U' (by omega) _ _ hh hh2
        omega

lemma six {n U E U' E' : ℕ} (h1 : H1) (h : (collatzSteps n = some (U + E) ∧ ((Finset.range (U + E)).filter (fun i => collatzStep^[i] n % 2 = 1)).card = U)) (h' : (collatzSteps (n + 1) = some (U' + E') ∧ ((Finset.range (U' + E')).filter (fun i => collatzStep^[i] (n + 1) % 2 = 1)).card = U')) :
    6 ^ U * 2 ^ (U' + E') * (3 * n) < 6 ^ U' * 2 ^ (U + E) * (4 * (n + 1)) ∧
    6 ^ U' * 2 ^ (U + E) * (3 * (n + 1)) < 6 ^ U * 2 ^ (U' + E') * (4 * n) := by
  have hA := tr_ratio _ _ _ _ rfl h
  have hB := tr_h1 h1 h
  have hC := tr_ratio _ _ _ _ rfl h'
  have hD := tr_h1 h1 h'
  rw [show (6 : ℕ) = 2 * 3 by norm_num, mul_pow, mul_pow, pow_add, pow_add]
  have p1 : 0 < 2 ^ U * 2 ^ U' := by positivity
  have p2 : 0 < 2 ^ E := by positivity
  have p3 : 0 < 2 ^ E' := by positivity
  constructor
  · have := Nat.mul_lt_mul_of_le_of_lt hA hD p2
    calc 2 ^ U * 3 ^ U * (2 ^ U' * 2 ^ E') * (3 * n)
        = 2 ^ U * 2 ^ U' * (3 ^ U * n * (3 * 2 ^ E')) := by ring
      _ < 2 ^ U * 2 ^ U' * (2 ^ E * (4 * (3 ^ U' * (n + 1)))) :=
          Nat.mul_lt_mul_of_pos_left this p1
      _ = 2 ^ U' * 3 ^ U' * (2 ^ U * 2 ^ E) * (4 * (n + 1)) := by ring
  · have := Nat.mul_lt_mul_of_le_of_lt hC hB p3
    calc 2 ^ U' * 3 ^ U' * (2 ^ U * 2 ^ E) * (3 * (n + 1))
        = 2 ^ U * 2 ^ U' * (3 ^ U' * (n + 1) * (3 * 2 ^ E)) := by ring
      _ < 2 ^ U * 2 ^ U' * (2 ^ E' * (4 * (3 ^ U * n))) :=
          Nat.mul_lt_mul_of_pos_left this p1
      _ = 2 ^ U * 3 ^ U * (2 ^ U' * 2 ^ E') * (4 * n) := by ring

lemma six_v {n U E U' E' v : ℕ} (h1 : H1) (h : (collatzSteps n = some (U + E) ∧ ((Finset.range (U + E)).filter (fun i => collatzStep^[i] n % 2 = 1)).card = U)) (h' : (collatzSteps (n + 1) = some (U' + E') ∧ ((Finset.range (U' + E')).filter (fun i => collatzStep^[i] (n + 1) % 2 = 1)).card = U'))
    (hv : U' + E' = U + E + v) :
    6 ^ U * (2 ^ v * (3 * n)) < 6 ^ U' * (4 * (n + 1)) ∧
    6 ^ U' * (3 * (n + 1)) < 6 ^ U * (2 ^ v * (4 * n)) := by
  obtain ⟨s1, s2⟩ := six h1 h h'
  rw [hv, pow_add 2 (U + E) v] at s1 s2
  have p : 0 < 2 ^ (U + E) := by positivity
  constructor
  · apply Nat.lt_of_mul_lt_mul_left (a := 2 ^ (U + E))
    calc 2 ^ (U + E) * (6 ^ U * (2 ^ v * (3 * n)))
        = 6 ^ U * (2 ^ (U + E) * 2 ^ v) * (3 * n) := by ring
      _ < 6 ^ U' * 2 ^ (U + E) * (4 * (n + 1)) := s1
      _ = 2 ^ (U + E) * (6 ^ U' * (4 * (n + 1))) := by ring
  · apply Nat.lt_of_mul_lt_mul_left (a := 2 ^ (U + E))
    calc 2 ^ (U + E) * (6 ^ U' * (3 * (n + 1)))
        = 6 ^ U' * 2 ^ (U + E) * (3 * (n + 1)) := by ring
      _ < 6 ^ U * (2 ^ (U + E) * 2 ^ v) * (4 * n) := s2
      _ = 2 ^ (U + E) * (6 ^ U * (2 ^ v * (4 * n))) := by ring

lemma cmpA {U U' d a b : ℕ} (h : 6 ^ U * a < 6 ^ U' * b) (hd : U' ≤ U + d) : a < 6 ^ d * b := by
  have h6 : 6 ^ U' ≤ 6 ^ U * 6 ^ d := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) hd
  apply Nat.lt_of_mul_lt_mul_left (a := 6 ^ U)
  calc 6 ^ U * a < 6 ^ U' * b := h
    _ ≤ 6 ^ U * 6 ^ d * b := Nat.mul_le_mul_right b h6
    _ = 6 ^ U * (6 ^ d * b) := by ring

lemma cmpB {U U' d a b : ℕ} (h : 6 ^ U' * a < 6 ^ U * b) (hd : U + d ≤ U') : 6 ^ d * a < b := by
  have h6 : 6 ^ U * 6 ^ d ≤ 6 ^ U' := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) hd
  apply Nat.lt_of_mul_lt_mul_left (a := 6 ^ U)
  calc 6 ^ U * (6 ^ d * a) = 6 ^ U * 6 ^ d * a := by ring
    _ ≤ 6 ^ U' * a := Nat.mul_le_mul_right a h6
    _ < 6 ^ U * b := h

lemma a_spec {n : ℕ} {v : ℤ} (hn : 0 < n) (ha : a n = some v) :
    ∃ U E U' E', (collatzSteps n = some (U + E) ∧ ((Finset.range (U + E)).filter (fun i => collatzStep^[i] n % 2 = 1)).card = U) ∧ (collatzSteps (n + 1) = some (U' + E') ∧ ((Finset.range (U' + E')).filter (fun i => collatzStep^[i] (n + 1) % 2 = 1)).card = U') ∧
      v = ((U' : ℤ) + E') - ((U : ℤ) + E) := by
  have key : ∃ s1 s2, collatzSteps n = some s1 ∧ collatzSteps (n + 1) = some s2 ∧
      ((s2 : ℤ) - s1) = v := by
    unfold a at ha
    rw [if_neg (by omega)] at ha
    rcases hs2 : collatzSteps (n + 1) with _ | s2 <;> rcases hs1 : collatzSteps n with _ | s1 <;>
      rw [hs2, hs1] at ha <;> simp at ha
    exact ⟨s1, s2, rfl, rfl, ha⟩
  obtain ⟨s1, s2, hs1, hs2, ha⟩ := key
  obtain ⟨U, E, rfl, h⟩ := tr_of_steps hs1
  obtain ⟨U', E', rfl, h'⟩ := tr_of_steps hs2
  refine ⟨U, E, U', E', h, h', ?_⟩
  rw [← ha]; push_cast; ring

lemma a_of_tr {n U E U' E' : ℕ} (h : (collatzSteps n = some (U + E) ∧ ((Finset.range (U + E)).filter (fun i => collatzStep^[i] n % 2 = 1)).card = U)) (h' : (collatzSteps (n + 1) = some (U' + E') ∧ ((Finset.range (U' + E')).filter (fun i => collatzStep^[i] (n + 1) % 2 = 1)).card = U')) :
    a n = some (((U' : ℤ) + E') - ((U : ℤ) + E)) := by
  have hn := tr_pos h
  unfold a
  rw [if_neg (by omega), h.1, h'.1]
  simp

lemma v_three (h1 : H1) {n U E U' E' : ℕ} (hn : 0 < n) (h : (collatzSteps n = some (U + E) ∧ ((Finset.range (U + E)).filter (fun i => collatzStep^[i] n % 2 = 1)).card = U))
    (h' : (collatzSteps (n + 1) = some (U' + E') ∧ ((Finset.range (U' + E')).filter (fun i => collatzStep^[i] (n + 1) % 2 = 1)).card = U')) (hv : U' + E' = U + E + 3) : U' = U + 1 ∧ E' = E + 2 := by
  obtain ⟨t1, t2⟩ := six_v h1 h h' hv
  have hU : U' = U + 1 := by
    by_contra hne
    by_cases hle : U' ≤ U
    · have := cmpA t1 (d := 0) (by omega)
      norm_num at this
      omega
    · have := cmpB t2 (d := 2) (by omega)
      norm_num at this
      omega
  exact ⟨hU, by omega⟩

lemma even3 (h1 : H1) {n : ℕ} (hpar : n % 2 = 0) (hn : 0 < n) (ha : a n = some 3) : n = 4 := by
  obtain ⟨U, E, U', E', h, h', hv⟩ := a_spec hn ha
  obtain ⟨rfl, rfl⟩ := v_three h1 hn h h' (by omega)
  obtain ⟨E0, rfl, hm⟩ := tr_even h hpar
  obtain ⟨U1, hU1, hz⟩ := tr_odd h' (by omega) (by omega)
  obtain rfl : U1 = U := by omega
  obtain ⟨E1, hE1, hy⟩ := tr_even hz (by omega)
  obtain rfl : E1 = E0 + 2 := by omega
  rw [show (3 * (n + 1) + 1) / 2 = 3 * (n / 2) + 2 by omega] at hy
  have := even_case h1 _ _ _ hm hy
  omega

lemma steps_small : ∀ n : ℕ, 1 ≤ n → n ≤ 19 →
    collatzSteps n =
      some ([0, 0, 1, 7, 2, 5, 8, 16, 3, 19, 6, 14, 9, 9, 17, 17, 4, 12, 20, 20].getD n 0) := by
  intro n h1 h2
  interval_cases n <;> exact steps_of (by decide) (by decide) (by decide)

lemma a_small : ∀ n : ℕ, 1 ≤ n → n ≤ 18 →
    a n = some
      ([0, 1, 6, -5, 3, 3, 8, -13, 16, -13, 8, -5, 0, 8, 0, -13, 8, 8, 0].getD n (0 : ℤ)) := by
  intro n h1 h2
  unfold a
  rw [if_neg (by omega), steps_small n h1 (by omega), steps_small (n + 1) (by omega) (by omega)]
  interval_cases n <;> rfl

lemma two_mul_two_pow_le : ∀ u : ℕ, 2 ≤ u → 2 * 2 ^ u ≤ 3 ^ u := by
  intro u hu
  induction u, hu using Nat.le_induction with
  | base => norm_num
  | succ u hu ih =>
    rw [pow_succ, pow_succ]
    omega

lemma shape : ∀ (k x u e : ℕ), u + e = k → (collatzSteps x = some (u + e) ∧ ((Finset.range (u + e)).filter (fun i => collatzStep^[i] x % 2 = 1)).card = u) → 2 ^ e < 3 ^ u * (x + 1) →
    2 ^ e + 2 ^ u = 3 ^ u * (x + 1) ∨ (1 ≤ u ∧ 2 * 2 ^ e + 2 ^ u = 2 * (3 ^ u * (x + 1))) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x u e hk h hlt
    by_cases hx1 : x = 1
    · subst hx1
      obtain ⟨rfl, rfl⟩ := tr_one h
      left; norm_num
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx
    · obtain ⟨e', rfl, h'⟩ := tr_even h hx
      obtain ⟨y, rfl⟩ : ∃ y, x = 2 * y := ⟨x / 2, by omega⟩
      rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)] at h'
      have e1 : 3 ^ u * (2 * y + 1) = 2 * (3 ^ u * y) + 3 ^ u := by ring
      have e2 : 3 ^ u * (y + 1) = 3 ^ u * y + 3 ^ u := by ring
      have hpow : 2 ^ u ≤ 3 ^ u := Nat.pow_le_pow_left (by norm_num) u
      have h2u : 0 < 2 ^ u := by positivity
      rw [e1, pow_succ] at hlt
      rw [e1, pow_succ]
      have hlt' : 2 ^ e' < 3 ^ u * (y + 1) := by rw [e2]; omega
      rcases ih (u + e') (by omega) y u e' rfl h' hlt' with ha | ⟨hu1, hb⟩
      · rw [e2] at ha
        have hu : u ≤ 1 := by
          by_contra hgt
          have := two_mul_two_pow_le u (by omega)
          omega
        interval_cases u
        · left
          simp only [pow_zero] at ha ⊢
          omega
        · right
          simp only [pow_one] at ha ⊢
          omega
      · rw [e2] at hb
        omega
    · obtain ⟨u', rfl, h'⟩ := tr_odd h hx hx1
      obtain ⟨e', rfl, h''⟩ := tr_even h' (by omega)
      obtain ⟨y, hy⟩ : ∃ y, 3 * x + 1 = 2 * y := ⟨(3 * x + 1) / 2, by omega⟩
      rw [hy, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)] at h''
      have hid : 3 ^ (u' + 1) * (x + 1) = 2 * (3 ^ u' * (y + 1)) := by
        have : 3 * (x + 1) = 2 * (y + 1) := by omega
        calc 3 ^ (u' + 1) * (x + 1) = 3 ^ u' * (3 * (x + 1)) := by ring
          _ = 2 * (3 ^ u' * (y + 1)) := by rw [this]; ring
      rw [hid, pow_succ] at hlt
      rw [hid, pow_succ, pow_succ]
      have hlt' : 2 ^ e' < 3 ^ u' * (y + 1) := by omega
      rcases ih (u' + e') (by omega) y u' e' rfl h'' hlt' with ha | ⟨hu1, hb⟩
      · left; omega
      · right; exact ⟨by omega, by omega⟩

lemma tr_even_pow : ∀ (g z U E : ℕ), 0 < z → (collatzSteps (2 ^ g * z) = some (U + E) ∧ ((Finset.range (U + E)).filter (fun i => collatzStep^[i] (2 ^ g * z) % 2 = 1)).card = U) →
    ∃ E', E = E' + g ∧ (collatzSteps z = some (U + E') ∧ ((Finset.range (U + E')).filter (fun i => collatzStep^[i] z % 2 = 1)).card = U) := by
  intro g
  induction g with
  | zero =>
    intro z U E hz h
    rw [pow_zero, one_mul] at h
    exact ⟨E, rfl, h⟩
  | succ g ih =>
    intro z U E hz h
    have hmul : 2 ^ (g + 1) * z = 2 * (2 ^ g * z) := by ring
    rw [hmul] at h
    obtain ⟨E1, rfl, h'⟩ := tr_even h (by omega)
    rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)] at h'
    obtain ⟨E', rfl, h''⟩ := ih z U E1 hz h'
    exact ⟨E', by omega, h''⟩

lemma inv_bound : ∀ (k x m σ q T : ℕ), m + 1 + T = k → (collatzSteps x = some (m + 1 + T) ∧ ((Finset.range (m + 1 + T)).filter (fun i => collatzStep^[i] x % 2 = 1)).card = m + 1) →
    3 ^ m * x = 2 ^ σ + q → 1 ≤ q → 2 ^ σ ≤ 4 * (∏ j ∈ Finset.range m, (1 + 3 ^ j)) * q := by
  intro k
  induction k with
  | zero => intro x m σ q T hk; omega
  | succ k ih =>
    intro x m σ q T hk h hq hq1
    have hP : 0 < ∏ j ∈ Finset.range m, (1 + 3 ^ j) := Finset.prod_pos fun j _ => by positivity
    by_cases hx1 : x = 1
    · subst hx1
      have := tr_one h
      omega
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx
    · obtain ⟨T', rfl, h'⟩ := tr_even h hx
      obtain ⟨y, rfl⟩ : ∃ y, x = 2 * y := ⟨x / 2, by omega⟩
      rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)] at h'
      cases σ with
      | zero =>
        have : 0 < 4 * (∏ j ∈ Finset.range m, (1 + 3 ^ j)) * q := by positivity
        rw [pow_zero]; exact this
      | succ σ' =>
        have hB : 3 ^ m * (2 * y) = 2 * (3 ^ m * y) := by ring
        rw [hB, pow_succ] at hq
        obtain ⟨q', rfl⟩ : ∃ q', q = 2 * q' := ⟨q / 2, by omega⟩
        have hq' : 3 ^ m * y = 2 ^ σ' + q' := by omega
        have := ih y m σ' q' T' (by omega) h' hq' (by omega)
        have e : 4 * (∏ j ∈ Finset.range m, (1 + 3 ^ j)) * (2 * q') =
            2 * (4 * (∏ j ∈ Finset.range m, (1 + 3 ^ j)) * q') := by ring
        rw [e, pow_succ]
        omega
    · obtain ⟨U', hU', h'⟩ := tr_odd h hx hx1
      have eU : U' = m := by omega
      rw [eU] at h'
      cases m with
      | zero =>
        have hT := tr_zero _ _ h'
        simp only [pow_zero, one_mul, Finset.range_zero, Finset.prod_empty, mul_one] at hq ⊢
        by_contra hcon
        rcases Nat.lt_or_ge T (σ + 2) with hlt | hge
        · have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (show T ≤ σ + 1 by omega)
          rw [pow_succ] at this
          omega
        · have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hge
          rw [pow_succ, pow_succ] at this
          omega
      | succ m' =>
        have hq2 : 3 ^ m' * (3 * x + 1) = 2 ^ σ + (q + 3 ^ m') := by
          have : 3 ^ m' * (3 * x + 1) = 3 ^ (m' + 1) * x + 3 ^ m' := by ring
          rw [this, hq]; ring
        have h3m : 0 < 3 ^ m' := by positivity
        have := ih (3 * x + 1) m' σ (q + 3 ^ m') T (by omega) h' hq2 (by omega)
        rw [Finset.prod_range_succ]
        have hle : q + 3 ^ m' ≤ (1 + 3 ^ m') * q := by
          have : 3 ^ m' ≤ 3 ^ m' * q := Nat.le_mul_of_pos_right _ (by omega)
          rw [add_mul, one_mul]
          omega
        calc 2 ^ σ ≤ 4 * (∏ j ∈ Finset.range m', (1 + 3 ^ j)) * (q + 3 ^ m') := this
          _ ≤ 4 * (∏ j ∈ Finset.range m', (1 + 3 ^ j)) * ((1 + 3 ^ m') * q) :=
              Nat.mul_le_mul_left _ hle
          _ = 4 * ((∏ j ∈ Finset.range m', (1 + 3 ^ j)) * (1 + 3 ^ m')) * q := by ring

lemma big : ∀ j : ℕ, 4 * (∏ i ∈ Finset.range (j + 3), (1 + 3 ^ i)) < 2 ^ 3 ^ (j + 2) ∧
    1 + 3 ^ (j + 3) ≤ 4 * (∏ i ∈ Finset.range (j + 3), (1 + 3 ^ i)) := by
  intro j
  induction j with
  | zero => norm_num [Finset.prod_range_succ]
  | succ j ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [Finset.prod_range_succ _ (j + 3)]
    have e : 4 * ((∏ i ∈ Finset.range (j + 3), (1 + 3 ^ i)) * (1 + 3 ^ (j + 3))) =
        4 * (∏ i ∈ Finset.range (j + 3), (1 + 3 ^ i)) * (1 + 3 ^ (j + 3)) := by ring
    rw [e]
    generalize 4 * (∏ i ∈ Finset.range (j + 3), (1 + 3 ^ i)) = B at ih1 ih2 ⊢
    constructor
    · have h3 : (2 : ℕ) ^ 3 ^ (j + 1 + 2) = 2 ^ 3 ^ (j + 2) * 2 ^ 3 ^ (j + 2) * 2 ^ 3 ^ (j + 2) := by
        rw [show j + 1 + 2 = (j + 2) + 1 by ring, pow_succ 3, ← pow_add, ← pow_add]
        congr 1; ring
      rw [h3]
      have hp : 1 ≤ 2 ^ 3 ^ (j + 2) := Nat.one_le_two_pow
      calc B * (1 + 3 ^ (j + 3)) ≤ B * B := Nat.mul_le_mul_left B ih2
        _ < 2 ^ 3 ^ (j + 2) * 2 ^ 3 ^ (j + 2) := Nat.mul_lt_mul'' ih1 ih1
        _ ≤ 2 ^ 3 ^ (j + 2) * 2 ^ 3 ^ (j + 2) * 2 ^ 3 ^ (j + 2) := Nat.le_mul_of_pos_right _ hp
    · have hB : 4 ≤ B := by
        have : 3 ^ 1 ≤ 3 ^ (j + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [pow_one] at this
        omega
      have e3 : 3 ^ (j + 1 + 3) = 3 * 3 ^ (j + 3) := by ring
      rw [e3]
      calc 1 + 3 * 3 ^ (j + 3) ≤ 4 * (1 + 3 ^ (j + 3)) := by omega
        _ ≤ B * (1 + 3 ^ (j + 3)) := Nat.mul_le_mul_right _ hB

lemma fin (h2 : H2) {K s z : ℕ} (hK : 1 ≤ K) (hz : 3 ^ K * z = 2 ^ s + 1)
    (h : (collatzSteps z = some (K + 1 + (s + 2)) ∧ ((Finset.range (K + 1 + (s + 2))).filter (fun i => collatzStep^[i] z % 2 = 1)).card = K + 1)) : K = 1 ∧ s = 3 := by
  have hb := inv_bound _ z K s 1 (s + 2) rfl h hz le_rfl
  rw [mul_one] at hb
  rcases Nat.lt_or_ge K 3 with hK3 | hK3
  · interval_cases K
    · have hs : s ≤ 3 := by
        by_contra hgt
        have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (show 4 ≤ s by omega)
        norm_num [Finset.prod_range_succ] at hb
        omega
      interval_cases s
      · omega
      · have hz1 : z = 1 := by omega
        rw [hz1] at h
        have := tr_one h
        omega
      · omega
      · exact ⟨rfl, rfl⟩
    · exfalso
      have hs : s ≤ 5 := by
        by_contra hgt
        have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (show 6 ≤ s by omega)
        norm_num [Finset.prod_range_succ] at hb
        omega
      interval_cases s
      · omega
      · omega
      · omega
      · have hz1 : z = 1 := by omega
        rw [hz1] at h
        have := tr_one h
        omega
      · omega
      · omega
  · exfalso
    obtain ⟨j, rfl⟩ : ∃ j, K = j + 3 := ⟨K - 3, by omega⟩
    have hdvd : 3 ^ (j + 2 + 1) ∣ 2 ^ s + 1 := ⟨z, hz.symm⟩
    have hs := h2 (j + 2) s hdvd
    have hs0 : 0 < s := by
      rcases Nat.eq_zero_or_pos s with h0 | h0
      · subst h0
        have : 3 ∣ 2 ^ 0 + 1 := Dvd.dvd.trans (dvd_pow_self 3 (by omega)) hdvd
        norm_num at this
      · exact h0
    have hle := Nat.le_of_dvd hs0 hs
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hle
    have := (big j).1
    omega

lemma odd3 (h1 : H1) (h2 : H2) {n : ℕ} (hpar : n % 2 = 1) (ha : a n = some 3) : n = 5 := by
  by_cases hn1 : n = 1
  · subst hn1
    rw [a_small 1 (by norm_num) (by norm_num)] at ha
    exact absurd (Option.some.inj ha) (by decide)
  obtain ⟨U, E, U', E', h, h', hv⟩ := a_spec (by omega) ha
  obtain ⟨eU, eE⟩ := v_three h1 (by omega) h h' (by omega)
  rw [eU, eE] at h'
  obtain ⟨c, rfl⟩ : ∃ c, n = 2 * c + 1 := ⟨n / 2, by omega⟩
  obtain ⟨E1, hE1, hW⟩ := tr_even h' (by omega)
  obtain ⟨U0, rfl, t1⟩ := tr_odd h hpar hn1
  obtain ⟨E0, rfl, hY⟩ := tr_even t1 (by omega)
  have eE1 : E1 = E0 + 2 := by omega
  rw [eE1, show (2 * c + 1 + 1) / 2 = c + 1 by omega] at hW
  rw [show (3 * (2 * c + 1) + 1) / 2 = 3 * c + 2 by omega] at hY
  have hH := tr_h1 h1 hW
  have hR := tr_ratio _ _ _ _ rfl hY
  have e1 : 3 ^ (U0 + 1 + 1) * (c + 1) = 9 * (3 ^ U0 * (c + 1)) := by ring
  have e2 : 3 ^ U0 * (3 * c + 2 + 1) = 3 * (3 ^ U0 * (c + 1)) := by ring
  have e3 : 3 ^ U0 * (3 * c + 2) = 3 * (3 ^ U0 * (c + 1)) - 3 ^ U0 := by
    have : 3 ^ U0 * (3 * c + 2) + 3 ^ U0 = 3 * (3 ^ U0 * (c + 1)) := by ring
    omega
  have hp3 : 1 ≤ 3 ^ U0 := Nat.one_le_pow _ _ (by norm_num)
  have hcc : 3 ^ U0 * 2 ≤ 3 ^ U0 * (c + 1) := Nat.mul_le_mul_left _ (by omega)
  rw [e1, pow_succ, pow_succ] at hH
  have hlt : 2 ^ E0 < 3 ^ U0 * (3 * c + 2 + 1) := by rw [e2]; omega
  have key : ∃ g, (g = U0 ∨ g + 1 = U0) ∧ 2 ^ E0 + 2 ^ g = 3 ^ (U0 + 1) * (c + 1) := by
    have e4 : 3 ^ (U0 + 1) * (c + 1) = 3 * (3 ^ U0 * (c + 1)) := by ring
    rw [e4]
    rcases shape _ _ _ _ rfl hY hlt with hs | ⟨hu1, hs⟩
    · exact ⟨U0, Or.inl rfl, by rw [e2] at hs; exact hs⟩
    · obtain ⟨g, rfl⟩ : ∃ g, U0 = g + 1 := ⟨U0 - 1, by omega⟩
      refine ⟨g, Or.inr rfl, ?_⟩
      rw [e2, pow_succ 2 g] at hs
      omega
  obtain ⟨g, hg, hs⟩ := key
  have hg2 : 2 ^ g ≤ 3 ^ U0 :=
    (Nat.pow_le_pow_right (by norm_num) (show g ≤ U0 by omega)).trans
      (Nat.pow_le_pow_left (by norm_num) U0)
  have hgE : g < E0 := by
    by_contra hcon
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (show E0 ≤ g by omega)
    rw [e3] at hR
    omega
  obtain ⟨s, rfl⟩ : ∃ s, E0 = g + s := ⟨E0 - g, by omega⟩
  have hs' : 2 ^ g * (2 ^ s + 1) = 3 ^ (U0 + 1) * (c + 1) := by rw [← hs, pow_add]; ring
  have hcop : Nat.Coprime (2 ^ g) (3 ^ (U0 + 1)) := Nat.Coprime.pow _ _ (by norm_num)
  have hdvd : 2 ^ g ∣ c + 1 := hcop.dvd_of_dvd_mul_left ⟨_, hs'.symm⟩
  obtain ⟨z, hz⟩ := hdvd
  have hz0 : 0 < z := by
    rcases Nat.eq_zero_or_pos z with h0 | h0
    · rw [h0] at hz; omega
    · exact h0
  rw [hz] at hW hs'
  have hz3 : 3 ^ (U0 + 1) * z = 2 ^ s + 1 := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 ^ g by positivity)
    rw [hs']; ring
  obtain ⟨E', hE', hZ⟩ := tr_even_pow g z _ _ hz0 hW
  have eE' : E' = s + 2 := by omega
  rw [eE'] at hZ
  obtain ⟨hK, hs3⟩ := fin h2 (by omega) hz3 hZ
  have hU0 : U0 = 0 := by omega
  have hg0 : g = 0 := by omega
  rw [hU0, hs3] at hz3
  rw [hg0] at hz
  norm_num at hz3 hz
  omega

theorem main : H1 → H2 → type_of% @OeisA153330.conjecture2 := by
  intro h1 h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext n
    simp only [indices, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hn, ha⟩
      obtain ⟨U, E, U', E', h, h', hv⟩ := a_spec hn ha
      obtain ⟨t1, t2⟩ := six_v h1 h h' (v := 1) (by omega)
      by_cases hle : U' ≤ U
      · have := cmpA t1 (d := 0) (by omega)
        norm_num at this
        omega
      · have := cmpB t2 (d := 1) (by omega)
        norm_num at this
        omega
    · rintro rfl
      exact ⟨by norm_num, a_small 1 (by norm_num) (by norm_num)⟩
  · ext n
    simp only [indices, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hn, ha⟩
      obtain ⟨U, E, U', E', h, h', hv⟩ := a_spec hn ha
      obtain ⟨t1, t2⟩ := six_v h1 h h' (v := 6) (by omega)
      by_cases hle : U' ≤ U + 2
      · have := cmpA t1 (d := 2) (by omega)
        norm_num at this
        have hn2 : n ≤ 2 := by omega
        by_contra hne
        obtain rfl : n = 1 := by omega
        rw [a_small 1 (by norm_num) (by norm_num)] at ha
        exact absurd (Option.some.inj ha) (by decide)
      · have := cmpB t2 (d := 3) (by omega)
        norm_num at this
        omega
    · rintro rfl
      exact ⟨by norm_num, a_small 2 (by norm_num) (by norm_num)⟩
  · ext n
    simp only [indices, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hn, ha⟩
      obtain ⟨U, E, U', E', h, h', hv⟩ := a_spec hn ha
      obtain ⟨t1, t2⟩ := six_v h1 h h' (v := 16) (by omega)
      by_cases hle : U' ≤ U + 6
      · have := cmpA t1 (d := 6) (by omega)
        norm_num at this
        have hn18 : n ≤ 18 := by omega
        have hs := a_small n hn hn18
        rw [ha] at hs
        have hs' := Option.some.inj hs
        by_contra hne
        interval_cases n <;> first | exact absurd rfl hne | exact absurd hs' (by decide)
      · have := cmpB t2 (d := 7) (by omega)
        norm_num at this
        omega
    · rintro rfl
      exact ⟨by norm_num, a_small 8 (by norm_num) (by norm_num)⟩
  · ext n
    simp only [indices, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hn, ha⟩
      rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
      · exact Or.inl (even3 h1 hpar hn ha)
      · exact Or.inr (odd3 h1 h2 hpar ha)
    · rintro (rfl | rfl)
      · exact ⟨by norm_num, a_small 4 (by norm_num) (by norm_num)⟩
      · exact ⟨by norm_num, a_small 5 (by norm_num) (by norm_num)⟩

end OMA.R_OeisA153330_conjecture2_R2
