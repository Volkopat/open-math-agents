import OMAStatements.S_erdos_306
/-
Adapted from Shisheng Li, Unit fractions with semiprime denominators: an elementary
proof of Erdős Problem #306, arXiv:2609.32140v1, 26 September 2026.
Source and version: https://arxiv.org/src/2609.32140v1/anc
License: Creative Commons Attribution 4.0 International
(https://creativecommons.org/licenses/by/4.0/).

The original Lean modules are identified inline. Changes combine the modules,
adapt the code to the pinned Mathlib and checker, and replace the original
Ramanujan hypothesis with a proof of the eventual dyadic prime-counting bound.
The new bound keeps the upper-interval factors in the central-binomial argument
for Bertrand's postulate, using the central-binomial estimates in Mathlib.
The mathematical circle-method framework is credited to Yuren Tang by Li.
-/

section
-- Source: https://arxiv.org/src/2609.32140v1/anc/lean/Erdos306/Basic.lean
/-
Erdős Problem #306 — formalisation of S. Li, "Unit fractions with semiprime denominators:
an elementary solution of Erdős Problem #306" (paper/erdos306.tex).

Basic notation shared by all files:
* `nint x`  — the distance `‖x‖` from a real number to the nearest integer (paper §8);
* `ee x`    — the additive character `e(x) = exp(2πix)` (paper §5).
-/

open Real

namespace Erdos306

/-- `‖x‖`: the distance from the real number `x` to the nearest integer (paper, §8). -/
noncomputable def nint (x : ℝ) : ℝ := |x - round x|

/-- `e(x) = exp(2πix)` (paper, §5). -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

/-- `‖x‖ ≥ 0`. -/
lemma nint_nonneg (x : ℝ) : 0 ≤ nint x := abs_nonneg _

/-- `‖x‖ ≤ 1/2`. -/
lemma nint_le_half (x : ℝ) : nint x ≤ 1 / 2 := abs_sub_round x

/-- `‖x‖ ≤ |x - n|` for every integer `n`. -/
lemma nint_le_abs_sub (x : ℝ) (n : ℤ) : nint x ≤ |x - n| := round_le x n

/-- `‖x‖ ≤ |x|`. -/
lemma nint_le_abs (x : ℝ) : nint x ≤ |x| := by
  simpa using nint_le_abs_sub x 0

/-- `‖x + n‖ = ‖x‖` for integers `n`. -/
lemma nint_add_int (x : ℝ) (n : ℤ) : nint (x + n) = nint x := by
  unfold nint
  rw [round_add_intCast]
  push_cast
  congr 1
  ring

/-- `‖x - n‖ = ‖x‖` for integers `n`. -/
lemma nint_sub_int (x : ℝ) (n : ℤ) : nint (x - n) = nint x := by
  have := nint_add_int x (-n)
  simpa [sub_eq_add_neg] using this

/-- `‖-x‖ = ‖x‖`. -/
lemma nint_neg (x : ℝ) : nint (-x) = nint x := by
  apply le_antisymm
  · calc nint (-x) ≤ |-x - ((-round x : ℤ) : ℝ)| := nint_le_abs_sub _ _
      _ = nint x := by unfold nint; push_cast; rw [← abs_neg]; ring_nf
  · calc nint x ≤ |x - ((-round (-x) : ℤ) : ℝ)| := nint_le_abs_sub _ _
      _ = nint (-x) := by unfold nint; push_cast; rw [← abs_neg]; ring_nf

/-- Triangle inequality for `‖·‖`. -/
lemma nint_add_le (x z : ℝ) : nint (x + z) ≤ nint x + nint z := by
  calc nint (x + z) ≤ |x + z - ((round x + round z : ℤ) : ℝ)| := nint_le_abs_sub _ _
    _ = |(x - round x) + (z - round z)| := by push_cast; ring_nf
    _ ≤ nint x + nint z := abs_add_le _ _

/-- `‖x - z‖ ≤ ‖x‖ + ‖z‖`. -/
lemma nint_sub_le (x z : ℝ) : nint (x - z) ≤ nint x + nint z := by
  have := nint_add_le x (-z)
  rw [nint_neg] at this
  simpa [sub_eq_add_neg] using this

/-- If `‖x‖ ≤ d` then some integer `n` has `|x - n| ≤ d`. -/
lemma exists_int_of_nint_le {x d : ℝ} (h : nint x ≤ d) : ∃ n : ℤ, |x - n| ≤ d :=
  ⟨round x, h⟩

/-- `e(x + z) = e(x) e(z)`. -/
lemma ee_add (x z : ℝ) : ee (x + z) = ee x * ee z := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `e(0) = 1`. -/
lemma ee_zero : ee 0 = 1 := by simp [ee]

/-- `|e(x)| = 1`. -/
lemma norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  rw [Complex.norm_exp]
  simp

end Erdos306

end

section
-- Source: https://arxiv.org/src/2609.32140v1/anc/lean/Erdos306/Primes.lean
/-
§2 of the paper: two bounds for primes.

* `lem_cheb_erdos`, `DyadicPrimeCount` — Lemma 2.1 (Chebyshev-type bounds);
* `cor_mertens`                — Corollary 2.2 (the large side carries reciprocal mass `≥ 1/50`).
-/

namespace Erdos306

open Real Finset

/-- The primes `p` with `a < p ≤ b`. -/
def primesIn (a b : ℕ) : Finset ℕ := (Finset.Ioc a b).filter Nat.Prime

/-- Membership in `primesIn a b`. -/
lemma mem_primesIn {a b p : ℕ} : p ∈ primesIn a b ↔ a < p ∧ p ≤ b ∧ p.Prime := by
  simp [primesIn, and_assoc]

/-- **Lemma 2.1, first part** (Erdős' bound): `∏_{p ≤ x} p ≤ 4^x`.  This is Mathlib's
`primorial_le_four_pow`. -/
theorem lem_cheb_erdos (n : ℕ) : primorial n ≤ 4 ^ n := primorial_le_four_pow n

/-- Eventual quantitative form of Bertrand's postulate used below. -/
def DyadicPrimeCount : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, x / (7 * log x) ≤ ((primesIn ⌊x / 2⌋₊ ⌊x⌋₊).card : ℝ)

/-- Telescoping bound for the harmonic sum used in Corollary 2.2:
`∑_{a ≤ i < a+n} 1/(i+1) ≥ log((a+n+1)/(a+1))` (from `log(1+1/m) ≤ 1/m`). -/
lemma harmonic_ge_log (a n : ℕ) :
    log (((a + n + 1 : ℕ) : ℝ) / ((a + 1 : ℕ) : ℝ)) ≤
      ∑ i ∈ Finset.Ico a (a + n), (1 : ℝ) / ((i : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, Finset.sum_Ico_succ_top (by omega)]
    have hpos1 : (0 : ℝ) < ((a + n + 1 : ℕ) : ℝ) := by positivity
    have hpos2 : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) := by positivity
    have hsplit : log (((a + n + 1 + 1 : ℕ) : ℝ) / ((a + 1 : ℕ) : ℝ)) =
        log (((a + n + 1 : ℕ) : ℝ) / ((a + 1 : ℕ) : ℝ)) +
          log (((a + n + 2 : ℕ) : ℝ) / ((a + n + 1 : ℕ) : ℝ)) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
    have hstep : log (((a + n + 2 : ℕ) : ℝ) / ((a + n + 1 : ℕ) : ℝ)) ≤
        1 / (((a + n : ℕ) : ℝ) + 1) := by
      refine le_trans (Real.log_le_sub_one_of_pos (by positivity)) (le_of_eq ?_)
      field_simp
      push_cast; ring
    rw [hsplit]
    linarith

/-- One dyadic block in the proof of Corollary 2.2: if `2^{i+1}` is past the threshold of
Lemma 2.1, then `∑_{2^i < p ≤ 2^{i+1}} 1/p ≥ 1/(7 (i+1) log 2)`. -/
lemma dyadic_block {x0 : ℝ} (hx0 : ∀ x ≥ x0, x / (7 * log x) ≤ ((primesIn ⌊x / 2⌋₊ ⌊x⌋₊).card : ℝ))
    (i : ℕ) (hi : x0 ≤ (2 : ℝ) ^ (i + 1)) :
    1 / (7 * ((i : ℝ) + 1) * log 2) ≤ ∑ p ∈ primesIn (2 ^ i) (2 ^ (i + 1)), (1 : ℝ) / p := by
  have h := hx0 _ hi
  have hfl1 : ⌊(2 : ℝ) ^ (i + 1) / 2⌋₊ = 2 ^ i := by
    rw [pow_succ, mul_div_assoc, div_self (by norm_num), mul_one]
    exact_mod_cast Nat.floor_natCast (2 ^ i)
  have hfl2 : ⌊(2 : ℝ) ^ (i + 1)⌋₊ = 2 ^ (i + 1) := by exact_mod_cast Nat.floor_natCast _
  rw [hfl1, hfl2, Real.log_pow] at h
  have hsum : ((primesIn (2 ^ i) (2 ^ (i + 1))).card : ℝ) * (1 / (2 : ℝ) ^ (i + 1)) ≤
      ∑ p ∈ primesIn (2 ^ i) (2 ^ (i + 1)), (1 : ℝ) / p := by
    rw [← nsmul_eq_mul]
    apply Finset.card_nsmul_le_sum
    intro p hp
    obtain ⟨h1, h2, h3⟩ := mem_primesIn.1 hp
    apply one_div_le_one_div_of_le (by exact_mod_cast h3.pos)
    exact_mod_cast h2
  refine le_trans ?_ hsum
  have h2pos : (0 : ℝ) < 2 ^ (i + 1) := by positivity
  have hl2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  calc 1 / (7 * ((i : ℝ) + 1) * log 2)
      = (2 : ℝ) ^ (i + 1) / (7 * (((i + 1 : ℕ) : ℝ) * log 2)) * (1 / (2 : ℝ) ^ (i + 1)) := by
        push_cast; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right h (by positivity)

/-- **Corollary 2.2**: for all sufficiently large `y`, `∑_{y^8 < p ≤ y^9} 1/p ≥ c_U = 1/50`. -/
theorem cor_mertens (hR : DyadicPrimeCount) : ∃ y0 : ℕ, ∀ y ≥ y0,
    (1 : ℝ) / 50 ≤ ∑ p ∈ primesIn (y ^ 8) (y ^ 9), (1 : ℝ) / p := by
  obtain ⟨x0, hx0⟩ := hR
  set K0 : ℕ := max 75 ⌈x0⌉₊ with hK0
  refine ⟨2 ^ K0, fun y hy => ?_⟩
  have hy0 : y ≠ 0 := by have := Nat.one_le_two_pow (n := K0); omega
  set k := Nat.log 2 y with hk
  have hkK : K0 ≤ k := (Nat.le_log_iff_pow_le (by norm_num) hy0).2 hy
  have hk75 : 75 ≤ k := le_trans (le_max_left _ _) hkK
  have hkx : ⌈x0⌉₊ ≤ k := le_trans (le_max_right _ _) hkK
  have hlo : 2 ^ k ≤ y := Nat.pow_log_le_self 2 hy0
  have hhi : y < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) y
  -- the blocks `(2^i, 2^{i+1}]`, `8k+8 ≤ i < 9k`, lie inside `(y^8, y^9]`
  have hsub : (Finset.Ico (8 * k + 8) (9 * k)).biUnion
      (fun i => primesIn (2 ^ i) (2 ^ (i + 1))) ⊆ primesIn (y ^ 8) (y ^ 9) := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.1 hp
    obtain ⟨h1, h2, h3⟩ := mem_primesIn.1 hpi
    rw [Finset.mem_Ico] at hi
    refine mem_primesIn.2 ⟨?_, ?_, h3⟩
    · calc y ^ 8 < (2 ^ (k + 1)) ^ 8 := Nat.pow_lt_pow_left hhi (by norm_num)
        _ = 2 ^ (8 * k + 8) := by rw [← pow_mul]; ring_nf
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi.1
        _ < p := h1
    · calc p ≤ 2 ^ (i + 1) := h2
        _ ≤ 2 ^ (9 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = (2 ^ k) ^ 9 := by rw [← pow_mul]; ring_nf
        _ ≤ y ^ 9 := Nat.pow_le_pow_left hlo 9
  have hdisj : (↑(Finset.Ico (8 * k + 8) (9 * k)) : Set ℕ).PairwiseDisjoint
      (fun i => primesIn (2 ^ i) (2 ^ (i + 1))) := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro p hpi hpj
    obtain ⟨a1, a2, -⟩ := mem_primesIn.1 hpi
    obtain ⟨b1, b2, -⟩ := mem_primesIn.1 hpj
    rcases lt_or_gt_of_ne hij with h | h
    · have : 2 ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) h
      omega
    · have : 2 ^ (j + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h
      omega
  have hl2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  -- sum of the block bounds
  have hblocks : (1 / (7 * log 2)) * ∑ i ∈ Finset.Ico (8 * k + 8) (9 * k), (1 : ℝ) / ((i : ℝ) + 1)
      ≤ ∑ p ∈ primesIn (y ^ 8) (y ^ 9), (1 : ℝ) / p := by
    rw [Finset.mul_sum]
    calc ∑ i ∈ Finset.Ico (8 * k + 8) (9 * k), 1 / (7 * log 2) * (1 / ((i : ℝ) + 1))
        ≤ ∑ i ∈ Finset.Ico (8 * k + 8) (9 * k),
            ∑ p ∈ primesIn (2 ^ i) (2 ^ (i + 1)), (1 : ℝ) / p := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.mem_Ico] at hi
          have hx : x0 ≤ (2 : ℝ) ^ (i + 1) := by
            calc x0 ≤ (⌈x0⌉₊ : ℝ) := Nat.le_ceil x0
              _ ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
              _ ≤ ((2 ^ (i + 1) : ℕ) : ℝ) := by exact_mod_cast (Nat.lt_two_pow_self).le
              _ = (2 : ℝ) ^ (i + 1) := by push_cast; ring
          have := dyadic_block hx0 i hx
          calc 1 / (7 * log 2) * (1 / ((i : ℝ) + 1)) = 1 / (7 * ((i : ℝ) + 1) * log 2) := by
                field_simp
            _ ≤ _ := this
      _ = ∑ p ∈ (Finset.Ico (8 * k + 8) (9 * k)).biUnion
            (fun i => primesIn (2 ^ i) (2 ^ (i + 1))), (1 : ℝ) / p := (Finset.sum_biUnion hdisj).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  -- the harmonic sum is at least `log((9k+1)/(8k+9)) ≥ log 1.11 ≥ (7/50) log 2`
  have hharm := harmonic_ge_log (8 * k + 8) (k - 8)
  have e1 : 8 * k + 8 + (k - 8) = 9 * k := by omega
  rw [e1] at hharm
  have hratio : (1.11 : ℝ) ≤ ((9 * k + 1 : ℕ) : ℝ) / ((8 * k + 8 + 1 : ℕ) : ℝ) := by
    rw [le_div_iff₀ (by positivity)]
    have : (75 : ℝ) ≤ k := by exact_mod_cast hk75
    push_cast; linarith
  have hlog111 : 7 * log 2 / 50 ≤ log (1.11 : ℝ) := by
    have h1 : log ((2 : ℝ) ^ 7) ≤ log ((1.11 : ℝ) ^ 50) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow, Real.log_pow] at h1
    push_cast at h1
    linarith
  have hlogr := Real.log_le_log (by norm_num) hratio
  have hH : 7 * log 2 / 50 ≤ ∑ i ∈ Finset.Ico (8 * k + 8) (9 * k), (1 : ℝ) / ((i : ℝ) + 1) := by
    linarith
  calc (1 : ℝ) / 50 = (1 / (7 * log 2)) * (7 * log 2 / 50) := by field_simp
    _ ≤ (1 / (7 * log 2)) * ∑ i ∈ Finset.Ico (8 * k + 8) (9 * k), (1 : ℝ) / ((i : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hH (by positivity)
    _ ≤ _ := hblocks

end Erdos306

end

section
-- Source: https://arxiv.org/src/2609.32140v1/anc/lean/Erdos306/Construction.lean
/-
§4 of the paper: the construction `V = {2} ∪ B ∪ W`, `U = U(Y)`, the tuning lemma, and the
reduction of Theorem 3.1 to Proposition 4.2 (a congruence mod 1 forces equality).

Conventions.  The target is a rational `τ` (the paper's `a/b`, so `b = τ.den`); `y` is a natural
number (the paper allows real `y`; natural `y` suffices and makes `y^7` an integer).
Edges `vu` of the complete bipartite graph `V × U` are pairs `(v, u) : ℕ × ℕ`.
The endpoint `Y` is a natural number with `y^8 ≤ Y ≤ y^9` (the paper takes `Y` prime; only
the set `U(Y)` matters, and `U(Y) = U(max U(Y))`).
-/

namespace Erdos306

open Real Finset

variable (τ : ℚ) (y Y : ℕ)

/-- `B`: the primes dividing `b = τ.den`. -/
def Bset : Finset ℕ := τ.den.primeFactors

/-- `W = {w prime : y^2 < w ≤ 2y^2}`: the test primes. -/
def Wset : Finset ℕ := primesIn (y ^ 2) (2 * y ^ 2)

/-- The small side `V = {2} ∪ B ∪ W`. -/
def Vset : Finset ℕ := insert 2 (Bset τ ∪ Wset y)

/-- The large side `U = U(Y) = {u prime : y^8 < u ≤ Y}`. -/
def Uset : Finset ℕ := primesIn (y ^ 8) Y

/-- `H_V = ∑_{v ∈ V} 1/v`. -/
noncomputable def HV : ℝ := ∑ v ∈ Vset τ y, (1 : ℝ) / v

/-- The edge set `A = A(Y) = V × U`. -/
def Aset : Finset (ℕ × ℕ) := Vset τ y ×ˢ Uset y Y

/-- `μ(Y) = ½ ∑_{(v,u) ∈ A} 1/(uv)`: half the total mass of `A`. -/
noncomputable def mu : ℝ := (1 / 2) * ∑ p ∈ Aset τ y Y, (1 : ℝ) / (p.1 * p.2)

/-- `σ(S) = ∑_{(v,u) ∈ S} 1/(vu)` (a rational number). -/
def sigma (S : Finset (ℕ × ℕ)) : ℚ := ∑ p ∈ S, (1 : ℚ) / (p.1 * p.2)

/-- `L = ∏_{p ∈ V ∪ U} p`. -/
def Lnum : ℕ := ∏ p ∈ Vset τ y ∪ Uset y Y, p

/-- `δ = 1/(400 log y)` (paper §8.1). -/
noncomputable def delta : ℝ := 1 / (400 * log y)

/-- `ε = exp(-|W| δ² / 8)` (paper §8.1). -/
noncomputable def eps : ℝ := exp (-((Wset y).card * delta y ^ 2 / 8))

/-- `δ_a = 1/(8y²)` (paper §8.2). -/
noncomputable def deltaA : ℝ := 1 / (8 * (y : ℝ) ^ 2)

/-- All the inequalities that the paper asserts "for `y` sufficiently large (in terms of `b`)".
Each field is used at exactly the place indicated; `eventually_large` (file `Asymptotics`)
shows that they all hold for all large `y`. -/
structure Large : Prop where
  /-- a harmless lower bound on `y` -/
  y_ge : 3 ≤ y
  /-- `y > max B` (§4) -/
  B_lt : ∀ r ∈ Bset τ, r < y
  /-- eq. (1): `|W| ≥ y²/(8 log y)` -/
  card_W : (y : ℝ) ^ 2 / (8 * log y) ≤ (Wset y).card
  /-- eq. (1) / Corollary 2.2: `∑_{u ∈ U(y^9)} 1/u ≥ c_U = 1/50` -/
  mertens : (1 : ℝ) / 50 ≤ ∑ u ∈ Uset y (y ^ 9), (1 : ℝ) / u
  /-- Lemma 4.1: `H_V/(2y^8) < τ/2` -/
  tune : HV τ y / (2 * (y : ℝ) ^ 8) < τ / 2
  /-- Proposition 7.1, step 4: `y > 2 H_V` -/
  major : 2 * HV τ y < y
  /-- Lemma 8.2: `y²/(20 log y) + 10 ≤ y²/(16 log y)` -/
  count : (y : ℝ) ^ 2 / (20 * log y) + 10 ≤ (y : ℝ) ^ 2 / (16 * log y)
  /-- Proposition 9.1, case II: `y^{-3} ≤ δ/2` -/
  phase : 1 / (y : ℝ) ^ 3 ≤ delta y / 2
  /-- Proposition 9.1, case III: `e^{-2δ_a²} + Yε ≤ e^{-δ_a²}` (with `Y ≤ y^9`) -/
  colIII : exp (-2 * deltaA y ^ 2) + (y : ℝ) ^ 9 * eps y ≤ exp (-(deltaA y ^ 2))
  /-- Proposition 9.1, case III: `2b·16^{y²}·exp(-τy⁴/(64 H_V)) ≤ 1/4` -/
  caseIII : 2 * (τ.den : ℝ) * 16 ^ (y ^ 2) * exp (-((τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y)))
    ≤ 1 / 4
  /-- Proposition 9.1, case II: `3y^{25} ε e^{y^{18} ε} ≤ 1/4` -/
  caseII : 3 * (y : ℝ) ^ 25 * eps y * exp ((y : ℝ) ^ 18 * eps y) ≤ 1 / 4

/-- The conclusions of the tuning lemma (Lemma 4.1) for the endpoint `Y`. -/
structure Tuned : Prop where
  lo : y ^ 8 ≤ Y
  hi : Y ≤ y ^ 9
  beta_nonpos : mu τ y Y ≤ τ
  beta_ge : (τ : ℝ) - mu τ y Y ≤ HV τ y / (2 * (y : ℝ) ^ 8)
  mu_ge : (τ : ℝ) / 2 ≤ mu τ y Y
  card_U : (τ : ℝ) * (y : ℝ) ^ 8 / HV τ y ≤ (Uset y Y).card

/-! ### Elementary facts about the construction -/

section facts

variable {τ y Y}

/-- Membership in `W`. -/
lemma mem_Wset {w : ℕ} : w ∈ Wset y ↔ y ^ 2 < w ∧ w ≤ 2 * y ^ 2 ∧ w.Prime := mem_primesIn

/-- Membership in `U(Y)`. -/
lemma mem_Uset {u : ℕ} : u ∈ Uset y Y ↔ y ^ 8 < u ∧ u ≤ Y ∧ u.Prime := mem_primesIn

/-- Membership in `V = {2} ∪ B ∪ W`. -/
lemma mem_Vset {v : ℕ} : v ∈ Vset τ y ↔ v = 2 ∨ v ∈ Bset τ ∨ v ∈ Wset y := by
  simp [Vset]

/-- Membership in `A = V × U`. -/
lemma mem_Aset {p : ℕ × ℕ} : p ∈ Aset τ y Y ↔ p.1 ∈ Vset τ y ∧ p.2 ∈ Uset y Y := by
  simp [Aset]

/-- Every element of `V` is prime. -/
lemma prime_of_mem_Vset {v : ℕ} (hv : v ∈ Vset τ y) : v.Prime := by
  rcases mem_Vset.1 hv with h | h | h
  · subst h; exact Nat.prime_two
  · exact Nat.prime_of_mem_primeFactors h
  · exact (mem_Wset.1 h).2.2

/-- Every element of `U` is prime. -/
lemma prime_of_mem_Uset {u : ℕ} (hu : u ∈ Uset y Y) : u.Prime := (mem_Uset.1 hu).2.2

/-- `2 ∈ V`. -/
lemma two_mem_Vset : 2 ∈ Vset τ y := by simp [Vset]

/-- `W ⊆ V`. -/
lemma Wset_subset_Vset : Wset y ⊆ Vset τ y := by
  intro w hw; simp [Vset, hw]

/-- Every `v ∈ V` satisfies `2 ≤ v ≤ 2y²`. -/
lemma le_of_mem_Vset (hL : Large τ y) {v : ℕ} (hv : v ∈ Vset τ y) : 2 ≤ v ∧ v ≤ 2 * y ^ 2 := by
  refine ⟨(prime_of_mem_Vset hv).two_le, ?_⟩
  have hy := hL.y_ge
  have hyy : y ≤ y ^ 2 := Nat.le_self_pow (by norm_num) y
  rcases mem_Vset.1 hv with h | h | h
  · omega
  · have := hL.B_lt v h; omega
  · exact (mem_Wset.1 h).2.1

/-- Every `u ∈ U(Y)` satisfies `y^8 < u ≤ Y`. -/
lemma bounds_of_mem_Uset {u : ℕ} (hu : u ∈ Uset y Y) : y ^ 8 < u ∧ u ≤ Y :=
  ⟨(mem_Uset.1 hu).1, (mem_Uset.1 hu).2.1⟩

/-- `V` and `U` are disjoint (they live at different scales). -/
lemma two_y_sq_lt (hL : Large τ y) : 2 * y ^ 2 < y ^ 8 := by
  have hy := hL.y_ge
  have h6 : 2 < y ^ 6 := by
    calc 2 < 3 ^ 6 := by norm_num
      _ ≤ y ^ 6 := Nat.pow_le_pow_left hy 6
  have : y ^ 8 = y ^ 2 * y ^ 6 := by ring
  rw [this]
  have : 0 < y ^ 2 := by positivity
  nlinarith

/-- `V` and `U` are disjoint (they live at different scales, `v ≤ 2y² < y^8 < u`). -/
lemma disjoint_V_U (hL : Large τ y) : Disjoint (Vset τ y) (Uset y Y) := by
  rw [Finset.disjoint_left]
  intro v hv hu
  have h1 := (le_of_mem_Vset hL hv).2
  have h2 := (bounds_of_mem_Uset hu).1
  have := two_y_sq_lt hL
  omega

/-- `b ∣ L`: the primes of `b` are among the primes of the graph (`b` squarefree). -/
lemma den_dvd_L (hsq : Squarefree τ.den) : τ.den ∣ Lnum τ y Y := by
  have h : ∏ p ∈ Bset τ, p = τ.den := Nat.prod_primeFactors_of_squarefree hsq
  rw [← h]
  apply Finset.prod_dvd_prod_of_subset
  intro r hr
  exact Finset.mem_union_left _ (by simp [Vset, hr])

/-- every edge `vu` divides `L` -/
lemma edge_dvd_L (hL : Large τ y) {p : ℕ × ℕ} (hp : p ∈ Aset τ y Y) :
    p.1 * p.2 ∣ Lnum τ y Y := by
  obtain ⟨hv, hu⟩ := mem_Aset.1 hp
  have hne : p.1 ≠ p.2 := by
    intro h
    exact Finset.disjoint_left.1 (disjoint_V_U (Y := Y) hL) hv (h ▸ hu)
  have : ∏ x ∈ ({p.1, p.2} : Finset ℕ), x = p.1 * p.2 := Finset.prod_pair hne
  rw [← this]
  apply Finset.prod_dvd_prod_of_subset
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact Finset.mem_union_left _ hv
  · exact Finset.mem_union_right _ hu

/-- `μ = ½ H_V ∑_{u ∈ U} 1/u`. -/
lemma mu_eq : mu τ y Y = (1 / 2) * HV τ y * ∑ u ∈ Uset y Y, (1 : ℝ) / u := by
  unfold mu HV Aset
  rw [Finset.sum_product, mul_assoc, Finset.sum_mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun u _ => ?_))
  rw [div_mul_div_comm, one_mul]

/-- eq. (1), second item: `∏_{v ∈ V} v ≤ 2 b 16^{y²}`. -/
lemma prod_V_le :
    ((∏ v ∈ Vset τ y, v : ℕ) : ℝ) ≤ 2 * τ.den * 16 ^ (y ^ 2) := by
  -- `∏_{insert 2 s} ∣ 2 ∏_s`
  have h1 : ∏ v ∈ Vset τ y, v ∣ 2 * ∏ v ∈ Bset τ ∪ Wset y, v := by
    unfold Vset
    by_cases h2 : 2 ∈ Bset τ ∪ Wset y
    · rw [Finset.insert_eq_of_mem h2]; exact Dvd.intro_left _ rfl
    · rw [Finset.prod_insert h2]
  have h2 : ∏ v ∈ Bset τ ∪ Wset y, v ∣ (∏ v ∈ Bset τ, v) * ∏ v ∈ Wset y, v := by
    rw [← Finset.prod_union_inter]; exact Dvd.intro _ rfl
  have hB : ∏ v ∈ Bset τ, v ∣ τ.den := Nat.prod_primeFactors_dvd τ.den
  have hW : ∏ v ∈ Wset y, v ∣ primorial (2 * y ^ 2) := by
    unfold primorial
    apply Finset.prod_dvd_prod_of_subset
    intro w hw
    obtain ⟨-, h2, h3⟩ := mem_Wset.1 hw
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, h3⟩
  have hprim := primorial_le_four_pow (2 * y ^ 2)
  have hden := τ.den_pos
  have hpp : 0 < primorial (2 * y ^ 2) := primorial_pos _
  have hN : ∏ v ∈ Vset τ y, v ≤ 2 * τ.den * 16 ^ (y ^ 2) := by
    have h3 : ∏ v ∈ Vset τ y, v ∣ 2 * (τ.den * primorial (2 * y ^ 2)) :=
      h1.trans (mul_dvd_mul_left 2 (h2.trans (mul_dvd_mul hB hW)))
    have h4 := Nat.le_of_dvd (by positivity) h3
    have h5 : (4 : ℕ) ^ (2 * y ^ 2) = 16 ^ (y ^ 2) := by
      rw [pow_mul]; norm_num
    calc ∏ v ∈ Vset τ y, v ≤ 2 * (τ.den * primorial (2 * y ^ 2)) := h4
      _ ≤ 2 * (τ.den * 4 ^ (2 * y ^ 2)) := by gcongr
      _ = 2 * τ.den * 16 ^ (y ^ 2) := by rw [h5]; ring
  exact_mod_cast hN

/-- eq. (1), third item: `½ ≤ H_V ≤ 3/2 + ∑_{r ∈ B} 1/r`. -/
lemma HV_bounds (hL : Large τ y) :
    1 / 2 ≤ HV τ y ∧ HV τ y ≤ 3 / 2 + ∑ r ∈ Bset τ, (1 : ℝ) / r := by
  have hnn : ∀ s : Finset ℕ, ∀ i ∈ s, (0 : ℝ) ≤ 1 / (i : ℝ) := fun _ _ _ => by positivity
  constructor
  · have := Finset.single_le_sum (f := fun v : ℕ => (1 : ℝ) / v) (hnn _)
      (two_mem_Vset (τ := τ) (y := y))
    simpa [HV] using this
  · -- `∑_{w ∈ W} 1/w ≤ |W|/y² ≤ 1`
    have hy : (0 : ℝ) < (y : ℝ) ^ 2 := by have := hL.y_ge; positivity
    have hWsum : ∑ w ∈ Wset y, (1 : ℝ) / w ≤ 1 := by
      have hcard : (Wset y).card ≤ y ^ 2 := by
        unfold Wset primesIn
        refine (Finset.card_filter_le _ _).trans ?_
        simp only [Nat.card_Ioc]
        omega
      calc ∑ w ∈ Wset y, (1 : ℝ) / w ≤ ∑ w ∈ Wset y, (1 : ℝ) / (y : ℝ) ^ 2 := by
            refine Finset.sum_le_sum (fun w hw => ?_)
            have h1 := (mem_Wset.1 hw).1
            have h2 : (y : ℝ) ^ 2 ≤ w := by exact_mod_cast h1.le
            exact one_div_le_one_div_of_le hy h2
        _ = (Wset y).card / (y : ℝ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ 1 := by
            rw [div_le_one hy]; exact_mod_cast hcard
    have hunion : ∑ v ∈ Bset τ ∪ Wset y, (1 : ℝ) / v ≤
        ∑ r ∈ Bset τ, (1 : ℝ) / r + ∑ w ∈ Wset y, (1 : ℝ) / w := by
      rw [← Finset.sum_union_inter]
      have := Finset.sum_nonneg (hnn (Bset τ ∩ Wset y))
      linarith
    have hins : HV τ y ≤ 1 / 2 + ∑ v ∈ Bset τ ∪ Wset y, (1 : ℝ) / v := by
      unfold HV Vset
      by_cases h2 : 2 ∈ Bset τ ∪ Wset y
      · rw [Finset.insert_eq_of_mem h2]; linarith
      · rw [Finset.sum_insert h2]; norm_num
    linarith

/-- `H_V > 0`. -/
lemma HV_pos (hL : Large τ y) : 0 < HV τ y := by
  have := (HV_bounds hL).1; linarith

end facts

/-! ### Lemma 4.1 (Tuning) -/

/-- Auxiliary: `U(y^8) = ∅`. -/
lemma Uset_eq_empty (y : ℕ) : Uset y (y ^ 8) = ∅ := by
  ext u; simp only [mem_Uset, Finset.notMem_empty, iff_false]; omega

/-- Adding the next integer `Y+1` adds at most one prime, of reciprocal `< 1/y^8`. -/
lemma sumU_succ_le {y Y : ℕ} (hy : 0 < y) (hY : y ^ 8 ≤ Y) :
    ∑ u ∈ Uset y (Y + 1), (1 : ℝ) / u ≤ ∑ u ∈ Uset y Y, (1 : ℝ) / u + 1 / (y : ℝ) ^ 8 := by
  have hsub : Uset y (Y + 1) ⊆ insert (Y + 1) (Uset y Y) := by
    intro u hu
    obtain ⟨h1, h2, h3⟩ := mem_Uset.1 hu
    rcases Nat.lt_or_ge u (Y + 1) with h | h
    · exact Finset.mem_insert_of_mem (mem_Uset.2 ⟨h1, by omega, h3⟩)
    · rw [show u = Y + 1 by omega]; exact Finset.mem_insert_self _ _
  have hnotin : Y + 1 ∉ Uset y Y := by intro h; have := (mem_Uset.1 h).2.1; omega
  calc ∑ u ∈ Uset y (Y + 1), (1 : ℝ) / u ≤ ∑ u ∈ insert (Y + 1) (Uset y Y), (1 : ℝ) / u :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = 1 / ((Y + 1 : ℕ) : ℝ) + ∑ u ∈ Uset y Y, (1 : ℝ) / u := Finset.sum_insert hnotin
    _ ≤ ∑ u ∈ Uset y Y, (1 : ℝ) / u + 1 / (y : ℝ) ^ 8 := by
        have : (y : ℝ) ^ 8 ≤ ((Y + 1 : ℕ) : ℝ) := by push_cast; exact_mod_cast (by omega : y ^ 8 ≤ Y + 1)
        have hpos : (0 : ℝ) < (y : ℝ) ^ 8 := by positivity
        have := one_div_le_one_div_of_le hpos this; linarith

/-- `∑_{u ∈ U} 1/u ≤ |U|/y^8`. -/
lemma sumU_le_card {y Y : ℕ} (hy : 0 < y) :
    ∑ u ∈ Uset y Y, (1 : ℝ) / u ≤ (Uset y Y).card / (y : ℝ) ^ 8 := by
  have hpos : (0 : ℝ) < (y : ℝ) ^ 8 := by positivity
  calc ∑ u ∈ Uset y Y, (1 : ℝ) / u ≤ ∑ u ∈ Uset y Y, 1 / (y : ℝ) ^ 8 := by
        refine Finset.sum_le_sum (fun u hu => ?_)
        have h1 := (mem_Uset.1 hu).1
        exact one_div_le_one_div_of_le hpos (by exact_mod_cast h1.le)
    _ = (Uset y Y).card / (y : ℝ) ^ 8 := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **Lemma 4.1 (Tuning).**  For `0 < τ ≤ η = 1/400` and `y` large, there is an endpoint
`Y ∈ [y^8, y^9]` with `0 ≤ τ - μ(Y) ≤ H_V/(2y^8)`, `μ(Y) ≥ τ/2` and `|U| ≥ τ y^8 / H_V`.
(Add the primes of `(y^8, y^9]` one at a time; stop at the last point where `μ ≤ τ`.) -/
theorem lem_tuning {τ : ℚ} {y : ℕ} (h0 : 0 < τ) (hη : τ ≤ 1 / 400) (hL : Large τ y) :
    ∃ Y, Tuned τ y Y := by
  classical
  have hτ0 : (0 : ℝ) < τ := by exact_mod_cast h0
  have hτη : (τ : ℝ) ≤ 1 / 400 := by
    have := (Rat.cast_le (K := ℝ)).2 hη; simpa using this
  have hHV := HV_bounds hL
  have hHVpos := HV_pos hL
  have hy : 0 < y := by have := hL.y_ge; omega
  have hy8 : y ^ 8 ≤ y ^ 9 := Nat.pow_le_pow_right hy (by norm_num)
  set T := (Finset.Icc (y ^ 8) (y ^ 9)).filter (fun Z => mu τ y Z ≤ τ) with hT
  have hne : y ^ 8 ∈ T := by
    simp only [hT, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨le_rfl, hy8⟩, ?_⟩
    rw [mu_eq, Uset_eq_empty]; simp; exact h0.le
  set Y := T.max' ⟨_, hne⟩ with hYdef
  have hYT : Y ∈ T := Finset.max'_mem _ _
  simp only [hT, Finset.mem_filter, Finset.mem_Icc] at hYT
  obtain ⟨⟨hYlo, hYhi⟩, hmuY⟩ := hYT
  -- the full range has `μ(y^9) ≥ c_U/4 = 1/200 > τ`
  have hfull : τ < mu τ y (y ^ 9) := by
    rw [mu_eq]
    have := hL.mertens
    have : (1 : ℝ) / 2 * (1 / 2) * (1 / 50) ≤ 1 / 2 * HV τ y * ∑ u ∈ Uset y (y ^ 9), (1 : ℝ) / u := by
      gcongr
      linarith [hHV.1]
    linarith
  have hYlt : Y < y ^ 9 := by
    rcases lt_or_eq_of_le hYhi with h | h
    · exact h
    · rw [h] at hmuY; linarith
  have hnext : τ < mu τ y (Y + 1) := by
    by_contra hcon
    push Not at hcon
    have hmem : Y + 1 ∈ T := by
      simp only [hT, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, hcon⟩
    have := Finset.le_max' T (Y + 1) hmem
    rw [← hYdef] at this
    omega
  have hstep : mu τ y (Y + 1) ≤ mu τ y Y + HV τ y / (2 * (y : ℝ) ^ 8) := by
    rw [mu_eq, mu_eq]
    have := sumU_succ_le (y := y) hy hYlo
    have h2 : 0 ≤ 1 / 2 * HV τ y := by positivity
    have := mul_le_mul_of_nonneg_left this h2
    have e : 1 / 2 * HV τ y * (1 / (y : ℝ) ^ 8) = HV τ y / (2 * (y : ℝ) ^ 8) := by
      field_simp
    nlinarith
  have hbeta : (τ : ℝ) - mu τ y Y ≤ HV τ y / (2 * (y : ℝ) ^ 8) := by linarith
  have hmu : (τ : ℝ) / 2 ≤ mu τ y Y := by linarith [hL.tune]
  refine ⟨Y, hYlo, hYhi, hmuY, hbeta, hmu, ?_⟩
  -- `∑_U 1/u = 2μ/H_V ≥ τ/H_V` and `∑_U 1/u ≤ |U|/y^8`
  have hsum : (τ : ℝ) / HV τ y ≤ ∑ u ∈ Uset y Y, (1 : ℝ) / u := by
    rw [div_le_iff₀ hHVpos]
    have := mu_eq (τ := τ) (y := y) (Y := Y)
    nlinarith
  have hcard := sumU_le_card (Y := Y) hy
  have hy8pos : (0 : ℝ) < (y : ℝ) ^ 8 := by positivity
  have := hsum.trans hcard
  rw [le_div_iff₀ hy8pos] at this
  calc (τ : ℝ) * (y : ℝ) ^ 8 / HV τ y = (τ : ℝ) / HV τ y * (y : ℝ) ^ 8 := by ring
    _ ≤ _ := this

/-! ### A congruence mod 1 forces equality (end of §4) -/

/-- The total mass of the graph is `2μ ≤ 2τ ≤ 1/2`, so every `S ⊆ A` has `0 ≤ σ(S) ≤ 1/2`. -/
lemma sigma_le_half {τ : ℚ} {y Y : ℕ} (hη : τ ≤ 1 / 400) (hT : Tuned τ y Y)
    {S : Finset (ℕ × ℕ)} (hS : S ⊆ Aset τ y Y) : 0 ≤ sigma S ∧ sigma S ≤ 1 / 2 := by
  have hnn : ∀ p : ℕ × ℕ, (0 : ℚ) ≤ 1 / ((p.1 : ℚ) * p.2) := fun _ => by positivity
  refine ⟨Finset.sum_nonneg (fun p _ => hnn p), ?_⟩
  have h1 : sigma S ≤ sigma (Aset τ y Y) :=
    Finset.sum_le_sum_of_subset_of_nonneg hS (fun p _ _ => hnn p)
  have h2 : ((sigma (Aset τ y Y) : ℚ) : ℝ) = 2 * mu τ y Y := by
    unfold sigma mu; push_cast; ring
  have h3 : ((sigma (Aset τ y Y) : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by
    rw [h2]
    have := hT.beta_nonpos
    have : (τ : ℝ) ≤ 1 / 400 := by have := (Rat.cast_le (K := ℝ)).2 hη; simpa using this
    push_cast; linarith
  exact h1.trans (by exact_mod_cast h3)

/-- If `σ(S) ≡ τ (mod 1)` then `σ(S) = τ` (end of §4). -/
lemma sigma_eq_of_congr {τ : ℚ} {y Y : ℕ} (h0 : 0 < τ) (hη : τ ≤ 1 / 400) (hT : Tuned τ y Y)
    {S : Finset (ℕ × ℕ)} (hS : S ⊆ Aset τ y Y) (k : ℤ) (hk : sigma S - τ = k) :
    sigma S = τ := by
  obtain ⟨hs0, hs1⟩ := sigma_le_half hη hT hS
  have hk1 : (k : ℚ) < 1 := by rw [← hk]; linarith
  have hk2 : (-1 : ℚ) < k := by rw [← hk]; linarith
  have : k = 0 := by
    have a : k < 1 := by exact_mod_cast hk1
    have b : -1 < k := by exact_mod_cast hk2
    omega
  rw [this] at hk
  simp at hk
  linarith

end Erdos306

end

section
-- Source: https://arxiv.org/src/2609.32140v1/anc/lean/Erdos306/Asymptotics.lean
/-
All "for `y` sufficiently large" statements of the paper, collected: every field of `Large τ y`
holds for all large `y`.
-/

namespace Erdos306

open Real Finset

/-- The bound for `ε` stated in §8.1: `ε ≤ exp(-y²/(2·10⁷ log³ y))` (from eq. (1)). -/
lemma eps_le {y : ℕ} (hy : 3 ≤ y) (hW : (y : ℝ) ^ 2 / (8 * log y) ≤ (Wset y).card) :
    eps y ≤ exp (-((y : ℝ) ^ 2 / (2 * 10 ^ 7 * log y ^ 3))) := by
  unfold eps delta
  apply Real.exp_le_exp.2
  have hlog : 0 < log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hy2 : (0 : ℝ) ≤ (y : ℝ) ^ 2 := by positivity
  have hdelta : (1 / (400 * log (y : ℝ))) ^ 2 / 8 = 1 / (1280000 * log y ^ 2) := by
    field_simp; ring
  have h1 : (y : ℝ) ^ 2 / (2 * 10 ^ 7 * log y ^ 3) ≤
      (y : ℝ) ^ 2 / (8 * log y) * (1 / (1280000 * log y ^ 2)) := by
    rw [div_mul_div_comm, mul_one]
    apply div_le_div_of_nonneg_left hy2 (by positivity)
    nlinarith [pow_pos hlog 3]
  have h2 : (y : ℝ) ^ 2 / (8 * log y) * (1 / (1280000 * log y ^ 2)) ≤
      (Wset y).card * (1 / (1280000 * log y ^ 2)) :=
    mul_le_mul_of_nonneg_right hW (by positivity)
  rw [mul_div_assoc, hdelta]
  linarith

/-- A `y`-uniform version of the bounds eq. (1) for `H_V`:
`½ ≤ H_V ≤ 3/2 + ∑_{r ∈ B} 1/r` for every `y ≥ 1` (using `∑_{w ∈ W} 1/w ≤ |W|/y² ≤ 1`). -/
lemma HV_bounds_uniform (τ : ℚ) {y : ℕ} (hy : 1 ≤ y) :
    1 / 2 ≤ HV τ y ∧ HV τ y ≤ 3 / 2 + ∑ r ∈ Bset τ, (1 : ℝ) / r := by
  have hnn : ∀ s : Finset ℕ, 0 ≤ ∑ i ∈ s, (1 : ℝ) / i := fun s => by positivity
  constructor
  · unfold HV
    have := Finset.single_le_sum (f := fun v : ℕ => (1 : ℝ) / v)
      (fun i _ => by positivity) (two_mem_Vset (τ := τ) (y := y))
    simpa using this
  · -- `∑_{w ∈ W} 1/w ≤ 1`
    have hW : ∑ w ∈ Wset y, (1 : ℝ) / w ≤ 1 := by
      have hy2 : (0 : ℝ) < (y : ℝ) ^ 2 := by positivity
      calc ∑ w ∈ Wset y, (1 : ℝ) / w ≤ ∑ w ∈ Wset y, (1 : ℝ) / (y : ℝ) ^ 2 := by
            apply Finset.sum_le_sum
            intro w hw
            have := (mem_Wset.1 hw).1
            apply one_div_le_one_div_of_le hy2
            exact_mod_cast this.le
        _ = (Wset y).card / (y : ℝ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ 1 := by
            rw [div_le_one hy2]
            have : (Wset y).card ≤ y ^ 2 := by
              calc (Wset y).card ≤ (Finset.Ioc (y ^ 2) (2 * y ^ 2)).card :=
                    Finset.card_filter_le _ _
                _ = y ^ 2 := by simp; omega
            exact_mod_cast this
    have hunion : ∑ v ∈ Bset τ ∪ Wset y, (1 : ℝ) / v ≤
        ∑ v ∈ Bset τ, (1 : ℝ) / v + ∑ v ∈ Wset y, (1 : ℝ) / v := by
      rw [← Finset.sum_union_inter]
      linarith [hnn (Bset τ ∩ Wset y)]
    have hins : HV τ y ≤ 1 / 2 + ∑ v ∈ Bset τ ∪ Wset y, (1 : ℝ) / v := by
      unfold HV Vset
      by_cases h2 : 2 ∈ Bset τ ∪ Wset y
      · rw [Finset.insert_eq_of_mem h2]; linarith
      · rw [Finset.sum_insert h2]; norm_num
    linarith

/-- `y^30 ε ≤ 1` for large `y` (the only place where the super-polynomial decay of `ε`,
`ε ≤ exp(-y²/(2·10⁷ log³ y))`, is used). -/
lemma y30_eps_le {y : ℕ} (hy : 2 * 10 ^ 11 ≤ y)
    (hW : (y : ℝ) ^ 2 / (8 * log y) ≤ (Wset y).card) : (y : ℝ) ^ 30 * eps y ≤ 1 := by
  have hy3 : 3 ≤ y := by omega
  have hyR : (2 * 10 ^ 11 : ℝ) ≤ y := by exact_mod_cast hy
  have hypos : (0 : ℝ) < y := by linarith
  have hlog : 0 < log (y : ℝ) := Real.log_pos (by linarith)
  -- `log y ≤ 4 y^{1/4}`, hence `log⁴ y ≤ 256 y`
  have hl4 : log (y : ℝ) ^ 4 ≤ 256 * y := by
    have h1 := Real.log_le_rpow_div hypos.le (by norm_num : (0 : ℝ) < 1 / 4)
    have h2 : ((y : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = y := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hypos.le]; norm_num
    calc log (y : ℝ) ^ 4 ≤ ((y : ℝ) ^ (1 / 4 : ℝ) / (1 / 4)) ^ 4 :=
          pow_le_pow_left₀ hlog.le h1 4
      _ = 256 * ((y : ℝ) ^ (1 / 4 : ℝ)) ^ 4 := by ring
      _ = 256 * y := by rw [h2]
  -- hence `30 log y ≤ y²/(2·10⁷ log³ y)`
  have hkey : 30 * log (y : ℝ) ≤ (y : ℝ) ^ 2 / (2 * 10 ^ 7 * log y ^ 3) := by
    rw [le_div_iff₀ (by positivity)]
    have : 30 * log (y : ℝ) * (2 * 10 ^ 7 * log y ^ 3) = 6 * 10 ^ 8 * log y ^ 4 := by ring
    rw [this]
    nlinarith
  have he := eps_le hy3 hW
  have hy30 : (y : ℝ) ^ 30 = exp (30 * log y) := by
    rw [show (30 : ℝ) = ((30 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hypos]
  rw [hy30]
  calc exp (30 * log y) * eps y
      ≤ exp (30 * log y) * exp (-((y : ℝ) ^ 2 / (2 * 10 ^ 7 * log y ^ 3))) :=
        mul_le_mul_of_nonneg_left he (by positivity)
    _ = exp (30 * log y - (y : ℝ) ^ 2 / (2 * 10 ^ 7 * log y ^ 3)) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ exp 0 := Real.exp_le_exp.2 (by linarith)
    _ = 1 := Real.exp_zero

/-- `|W| ≥ y²/(8 log y)` for large `y` (eq. (1), from Lemma 2.1 with `x = 2y²`). -/
lemma card_W_eventually (hR : DyadicPrimeCount) : ∃ y0 : ℕ, ∀ y ≥ y0, (y : ℝ) ^ 2 / (8 * log y) ≤ (Wset y).card := by
  obtain ⟨x0, hx0⟩ := hR
  refine ⟨max 12 ⌈x0⌉₊, fun y hy => ?_⟩
  have hy12 : 12 ≤ y := le_trans (le_max_left _ _) hy
  have hyx : ⌈x0⌉₊ ≤ y := le_trans (le_max_right _ _) hy
  have hyR : (12 : ℝ) ≤ y := by exact_mod_cast hy12
  have hx : x0 ≤ 2 * (y : ℝ) ^ 2 := by
    calc x0 ≤ (⌈x0⌉₊ : ℝ) := Nat.le_ceil x0
      _ ≤ y := by exact_mod_cast hyx
      _ ≤ 2 * (y : ℝ) ^ 2 := by nlinarith
  have h := hx0 _ hx
  have hf1 : ⌊2 * (y : ℝ) ^ 2 / 2⌋₊ = y ^ 2 := by
    rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
    exact_mod_cast Nat.floor_natCast (y ^ 2)
  have hf2 : ⌊2 * (y : ℝ) ^ 2⌋₊ = 2 * y ^ 2 := by exact_mod_cast Nat.floor_natCast (2 * y ^ 2)
  rw [hf1, hf2] at h
  refine le_trans ?_ h
  have hlog : 0 < log (y : ℝ) := Real.log_pos (by linarith)
  have hlog2 : log (2 * (y : ℝ) ^ 2) = log 2 + 2 * log y := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  -- `7 log 2 ≤ 2 log y` since `2^7 ≤ y²`
  have h7 : 7 * log (2 : ℝ) ≤ 2 * log y := by
    have : log ((2 : ℝ) ^ 7) ≤ log ((y : ℝ) ^ 2) := Real.log_le_log (by norm_num) (by nlinarith)
    rw [Real.log_pow, Real.log_pow] at this; push_cast at this; linarith
  have hl2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  rw [hlog2, div_le_div_iff₀ (by positivity) (by positivity)]
  have hy2 : (0 : ℝ) ≤ (y : ℝ) ^ 2 := by positivity
  nlinarith

/-- Numerics for Proposition 9.1, case III (one column):
`e^{-2δ_a²} + y^9 ε ≤ e^{-δ_a²}`, since `e^{-x} - e^{-2x} ≥ x/2` and `y^9 ε ≤ 1/(128 y⁴)`. -/
lemma colIII_numeric {y : ℕ} (hy : 128 ≤ y) (heps : (y : ℝ) ^ 30 * eps y ≤ 1) :
    exp (-2 * deltaA y ^ 2) + (y : ℝ) ^ 9 * eps y ≤ exp (-(deltaA y ^ 2)) := by
  have hyR : (128 : ℝ) ≤ y := by exact_mod_cast hy
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have heps0 : 0 ≤ eps y := (Real.exp_pos _).le
  set x := deltaA y ^ 2 with hx
  have hxy : x = 1 / (64 * (y : ℝ) ^ 4) := by rw [hx]; unfold deltaA; field_simp; ring
  have hx0 : 0 ≤ x := by rw [hxy]; positivity
  have hx4 : x ≤ 1 / 4 := by
    rw [hxy, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [one_le_pow₀ (n := 4) hy1]
  have hdiff : x / 2 ≤ exp (-x) - exp (-2 * x) := by
    have h1 : exp (-x) - exp (-2 * x) = exp (-2 * x) * (exp x - 1) := by
      rw [mul_sub, ← Real.exp_add]; ring_nf
    have h2 : x ≤ exp x - 1 := by linarith [Real.add_one_le_exp x]
    have h3 : 1 - 2 * x ≤ exp (-2 * x) := by linarith [Real.add_one_le_exp (-2 * x)]
    rw [h1]
    nlinarith
  have hy9 : (y : ℝ) ^ 9 * eps y ≤ x / 2 := by
    rw [hxy]
    have hy17 : (128 : ℝ) ≤ (y : ℝ) ^ 17 := le_trans hyR (le_self_pow₀ hy1 (by norm_num))
    have : (y : ℝ) ^ 9 * eps y * (128 * (y : ℝ) ^ 4) ≤ 1 := by
      calc (y : ℝ) ^ 9 * eps y * (128 * (y : ℝ) ^ 4) = 128 * ((y : ℝ) ^ 13 * eps y) := by ring
        _ ≤ (y : ℝ) ^ 17 * ((y : ℝ) ^ 13 * eps y) :=
            mul_le_mul_of_nonneg_right hy17 (by positivity)
        _ = (y : ℝ) ^ 30 * eps y := by ring
        _ ≤ 1 := heps
    rw [div_div, le_div_iff₀ (by positivity)]
    linarith
  linarith

/-- Numerics for Proposition 9.1, case II: `3y^{25} ε e^{y^{18} ε} ≤ 1/4`. -/
lemma caseII_numeric {y : ℕ} (hy : 36 ≤ y) (heps : (y : ℝ) ^ 30 * eps y ≤ 1) :
    3 * (y : ℝ) ^ 25 * eps y * exp ((y : ℝ) ^ 18 * eps y) ≤ 1 / 4 := by
  have hyR : (36 : ℝ) ≤ y := by exact_mod_cast hy
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have heps0 : 0 ≤ eps y := (Real.exp_pos _).le
  have hy12 : (1 : ℝ) ≤ (y : ℝ) ^ 12 := one_le_pow₀ hy1
  have h18 : (y : ℝ) ^ 18 * eps y ≤ 1 := by
    calc (y : ℝ) ^ 18 * eps y ≤ (y : ℝ) ^ 12 * ((y : ℝ) ^ 18 * eps y) :=
          le_mul_of_one_le_left (by positivity) hy12
      _ = (y : ℝ) ^ 30 * eps y := by ring
      _ ≤ 1 := heps
  have hexp : exp ((y : ℝ) ^ 18 * eps y) ≤ 3 := by
    calc exp ((y : ℝ) ^ 18 * eps y) ≤ exp 1 := Real.exp_le_exp.2 h18
      _ ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
  have h25 : 36 * ((y : ℝ) ^ 25 * eps y) ≤ 1 := by
    have hy5 : (36 : ℝ) ≤ (y : ℝ) ^ 5 := le_trans hyR (le_self_pow₀ hy1 (by norm_num))
    calc 36 * ((y : ℝ) ^ 25 * eps y) ≤ (y : ℝ) ^ 5 * ((y : ℝ) ^ 25 * eps y) :=
          mul_le_mul_of_nonneg_right hy5 (by positivity)
      _ = (y : ℝ) ^ 30 * eps y := by ring
      _ ≤ 1 := heps
  have hpos : 0 ≤ 3 * (y : ℝ) ^ 25 * eps y := by positivity
  calc 3 * (y : ℝ) ^ 25 * eps y * exp ((y : ℝ) ^ 18 * eps y)
      ≤ 3 * (y : ℝ) ^ 25 * eps y * 3 := mul_le_mul_of_nonneg_left hexp hpos
    _ ≤ 1 / 4 := by linarith

/-- Numerics for Proposition 9.1, case III (total): with `C ≥ H_V` and `y² ≥ Q`,
`2b·16^{y²}·exp(-τy⁴/(64 H_V)) ≤ 1/4`. -/
lemma caseIII_numeric {τ : ℚ} {y : ℕ} (hτ : 0 < τ) {C : ℝ} (hHV0 : 0 < HV τ y)
    (hHVC : HV τ y ≤ C) (hy1 : (1 : ℝ) ≤ y)
    (hyQ : 64 * C * (log (8 * τ.den) + log 16) / τ ≤ (y : ℝ) ^ 2) :
    2 * (τ.den : ℝ) * 16 ^ (y ^ 2) * exp (-((τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y))) ≤ 1 / 4 := by
  have hτR : (0 : ℝ) < τ := by exact_mod_cast hτ
  have hden1 : (1 : ℝ) ≤ τ.den := by exact_mod_cast τ.den_pos
  have hlog8b : 0 ≤ log (8 * (τ.den : ℝ)) := Real.log_nonneg (by linarith)
  have hlog16 : 0 < log (16 : ℝ) := Real.log_pos (by norm_num)
  have hC0 : 0 < C := lt_of_lt_of_le hHV0 hHVC
  have h16 : (16 : ℝ) ^ (y ^ 2) = exp ((y : ℝ) ^ 2 * log 16) := by
    rw [show ((y : ℝ) ^ 2) = ((y ^ 2 : ℕ) : ℝ) by push_cast; ring, Real.exp_nat_mul,
      Real.exp_log (by norm_num)]
  have h8b : 2 * (τ.den : ℝ) = exp (log (8 * τ.den)) / 4 := by
    rw [Real.exp_log (by positivity)]; ring
  have hexp : (y : ℝ) ^ 2 * log 16 + log (8 * τ.den) ≤ (τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y) := by
    have h1 : (τ : ℝ) * (y : ℝ) ^ 4 / (64 * C) ≤ (τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    refine le_trans ?_ h1
    have hQ' : 64 * C * (log (8 * τ.den) + log 16) ≤ τ * (y : ℝ) ^ 2 := by
      rwa [div_le_iff₀ hτR, mul_comm ((y : ℝ) ^ 2)] at hyQ
    rw [le_div_iff₀ (by positivity)]
    have hy2 : (1 : ℝ) ≤ (y : ℝ) ^ 2 := one_le_pow₀ hy1
    calc ((y : ℝ) ^ 2 * log 16 + log (8 * τ.den)) * (64 * C)
        ≤ (y : ℝ) ^ 2 * (64 * C * (log (8 * τ.den) + log 16)) := by
          have e : (y : ℝ) ^ 2 * (64 * C * (log (8 * τ.den) + log 16)) -
              ((y : ℝ) ^ 2 * log 16 + log (8 * τ.den)) * (64 * C) =
              ((y : ℝ) ^ 2 - 1) * (64 * C * log (8 * τ.den)) := by ring
          have : 0 ≤ ((y : ℝ) ^ 2 - 1) * (64 * C * log (8 * τ.den)) := by
            apply mul_nonneg (by linarith); positivity
          linarith
      _ ≤ (y : ℝ) ^ 2 * (τ * (y : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hQ' (by positivity)
      _ = τ * (y : ℝ) ^ 4 := by ring
  rw [h16, h8b]
  calc exp (log (8 * τ.den)) / 4 * exp ((y : ℝ) ^ 2 * log 16) *
        exp (-((τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y)))
      = exp ((y : ℝ) ^ 2 * log 16 + log (8 * τ.den) -
          (τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y)) / 4 := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_add]; ring
    _ ≤ exp 0 / 4 := by gcongr; linarith
    _ = 1 / 4 := by rw [Real.exp_zero]

/-- Numerics for Lemma 8.2 and Proposition 9.1 (case II): `800 log y ≤ y²` gives
`y²/(20 log y) + 10 ≤ y²/(16 log y)` and `y^{-3} ≤ δ/2`. -/
lemma count_phase_numeric {y : ℕ} (hy : 800 ≤ y) :
    (y : ℝ) ^ 2 / (20 * log y) + 10 ≤ (y : ℝ) ^ 2 / (16 * log y) ∧
      1 / (y : ℝ) ^ 3 ≤ delta y / 2 := by
  have hyR : (800 : ℝ) ≤ y := by exact_mod_cast hy
  have hypos : (0 : ℝ) < y := by linarith
  have hlog : 0 < log (y : ℝ) := Real.log_pos (by linarith)
  have hlogy : log (y : ℝ) ≤ y := le_trans (Real.log_le_sub_one_of_pos hypos) (by linarith)
  have h800 : 800 * log (y : ℝ) ≤ (y : ℝ) ^ 2 := by nlinarith
  constructor
  · have e : (y : ℝ) ^ 2 / (16 * log y) - (y : ℝ) ^ 2 / (20 * log y) =
        (y : ℝ) ^ 2 / (80 * log y) := by
      field_simp; ring
    have : 10 ≤ (y : ℝ) ^ 2 / (80 * log y) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  · unfold delta
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

/-- All the "sufficiently large `y`" conditions hold simultaneously for large `y`. -/
theorem eventually_large (hR : DyadicPrimeCount) {τ : ℚ} (h0 : 0 < τ) :
    ∃ y0 : ℕ, ∀ y ≥ y0, Large τ y := by
  obtain ⟨yW, hyW⟩ := card_W_eventually hR
  obtain ⟨yM, hyM⟩ := cor_mertens hR
  set C : ℝ := 3 / 2 + ∑ r ∈ Bset τ, (1 : ℝ) / r with hC
  have hτR : (0 : ℝ) < τ := by exact_mod_cast h0
  set Q : ℝ := 64 * C * (log (8 * τ.den) + log 16) / τ with hQ
  refine ⟨max (max yW yM) (max (2 * 10 ^ 11) (max (τ.den + 1)
    (⌈C / τ⌉₊ + ⌈2 * C⌉₊ + ⌈Q⌉₊ + 1))), fun y hy => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hy
  obtain ⟨⟨hyW', hyM'⟩, hbig, hden, hy1'⟩ := hy
  have hyR : (2 * 10 ^ 11 : ℝ) ≤ y := by exact_mod_cast hbig
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hsum : (⌈C / τ⌉₊ : ℝ) + ⌈2 * C⌉₊ + ⌈Q⌉₊ + 1 ≤ y := by exact_mod_cast hy1'
  have c1 := Nat.le_ceil (C / τ)
  have c2 := Nat.le_ceil (2 * C)
  have c3 := Nat.le_ceil Q
  have n1 : (0 : ℝ) ≤ ⌈C / τ⌉₊ := Nat.cast_nonneg _
  have n2 : (0 : ℝ) ≤ ⌈2 * C⌉₊ := Nat.cast_nonneg _
  have n3 : (0 : ℝ) ≤ ⌈Q⌉₊ := Nat.cast_nonneg _
  have hyC : C / τ ≤ y := by linarith
  have hy2C : 2 * C < y := by linarith
  have hyQ : Q ≤ (y : ℝ) ^ 2 := le_trans (by linarith) (le_self_pow₀ hy1 (by norm_num))
  have hHV := HV_bounds_uniform τ (y := y) (by omega)
  have hHVpos : 0 < HV τ y := by linarith [hHV.1]
  have hW := hyW y hyW'
  have heps := y30_eps_le hbig hW
  have hcp := count_phase_numeric (y := y) (by omega)
  refine
    { y_ge := by omega
      B_lt := ?_
      card_W := hW
      mertens := hyM y hyM'
      tune := ?_
      major := ?_
      count := hcp.1
      phase := hcp.2
      colIII := colIII_numeric (by omega) heps
      caseIII := caseIII_numeric h0 hHVpos hHV.2 hy1 hyQ
      caseII := caseII_numeric (by omega) heps }
  · intro r hr
    have hr' := Nat.le_of_dvd τ.den_pos (Nat.dvd_of_mem_primeFactors hr)
    omega
  · -- `H_V/(2y^8) < τ/2`: `H_V ≤ C ≤ τ y < τ y^8`
    have hy8 : (y : ℝ) < (y : ℝ) ^ 8 := by
      have : (y : ℝ) ^ 1 < (y : ℝ) ^ 8 := pow_lt_pow_right₀ (by linarith) (by norm_num)
      simpa using this
    have hCy : C ≤ τ * y := by rwa [div_le_iff₀ hτR, mul_comm] at hyC
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [hHV.2]
  · -- `2 H_V < y`
    linarith [hHV.2]

end Erdos306

end

section
-- Source: https://arxiv.org/src/2609.32140v1/anc/lean/Erdos306/Counting.lean
/-
§5 of the paper: counting with a geometric sum.

For a finite edge set `A` (pairs `(v,u)`, the edge standing for `1/(vu)`), a target `τ` and a
common denominator `L`, the number `N` of subsets `S ⊆ A` with `σ(S) ≡ τ (mod 1)` satisfies
  `N / 2^{|A|} = (1/L) ∑_h e(-hτ) φ(h)`,       eq. (2)
where `h` runs over the frequencies `-L/2 < h ≤ L/2` and `φ(h) = ∏_{(v,u)∈A} (1 + e(h/(uv)))/2`.
-/

namespace Erdos306

open Real Finset

/-- The frequencies: the integers `h` with `-⌊L/2⌋ < h ≤ L - ⌊L/2⌋` (for even `L`, exactly the
paper's `-L/2 < h ≤ L/2`); a complete residue system modulo `L`. -/
noncomputable def freq (L : ℕ) : Finset ℤ := Finset.Ioc (-((L : ℤ) / 2)) ((L : ℤ) - (L : ℤ) / 2)

/-- `φ(h) = ∏_{(v,u) ∈ A} (1 + e(h/(uv)))/2`. -/
noncomputable def phi (A : Finset (ℕ × ℕ)) (h : ℤ) : ℂ :=
  ∏ p ∈ A, (1 + ee ((h : ℝ) / ((p.1 : ℝ) * p.2))) / 2

open Classical in
/-- `N`: the number of `S ⊆ A` with `σ(S) ≡ τ (mod 1)`. -/
noncomputable def Ncount (A : Finset (ℕ × ℕ)) (τ : ℚ) : ℕ :=
  ((A.powerset).filter (fun S => ∃ k : ℤ, sigma S - τ = k)).card

/-- There are exactly `L` frequencies. -/
lemma card_freq (L : ℕ) : (freq L).card = L := by
  simp [freq]

/-- `e(n) = 1` for integers `n` (period 1). -/
lemma ee_int (n : ℤ) : ee (n : ℝ) = 1 := by
  unfold ee
  rw [← Complex.exp_int_mul_two_pi_mul_I n]
  congr 1; push_cast; ring

/-- `e(kx) = e(x)^k`. -/
lemma ee_nat_mul (k : ℕ) (x : ℝ) : ee ((k : ℝ) * x) = ee x ^ k := by
  unfold ee
  rw [← Complex.exp_nat_mul]
  congr 1; push_cast; ring

/-- `e(∑ f) = ∏ e(f)`. -/
lemma ee_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) : ee (∑ i ∈ s, f i) = ∏ i ∈ s, ee (f i) := by
  unfold ee
  rw [← Complex.exp_sum]
  congr 1; push_cast; rw [Finset.mul_sum]

/-- `e(x) = 1` iff `x` is an integer. -/
lemma ee_eq_one_iff (x : ℝ) : ee x = 1 ↔ ∃ n : ℤ, x = n := by
  unfold ee
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hpi : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : ((x : ℂ) - n) * (2 * π * Complex.I) = 0 := by rw [sub_mul]; rw [← hn]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact_mod_cast sub_eq_zero.1 h
    · exact absurd h hpi
  · rintro ⟨n, rfl⟩; exact ⟨n, by push_cast; ring⟩

/-- The geometric-series identity: over any `L` consecutive integers `h`,
`∑_h e(hm/L) = L` if `L ∣ m` and `= 0` otherwise. -/
theorem lem_geom (L : ℕ) (hL : 0 < L) (a m : ℤ) :
    ∑ h ∈ Finset.Ioc a (a + L), ee ((h : ℝ) * m / L) = if (L : ℤ) ∣ m then (L : ℂ) else 0 := by
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  split_ifs with hdvd
  · obtain ⟨k, rfl⟩ := hdvd
    have : ∀ h ∈ Finset.Ioc a (a + L), ee ((h : ℝ) * ((L : ℤ) * k : ℤ) / L) = 1 := by
      intro h _
      have : (h : ℝ) * (((L : ℤ) * k : ℤ) : ℝ) / L = ((h * k : ℤ) : ℝ) := by
        push_cast; field_simp
      rw [this, ee_int]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Int.card_Ioc]
    simp
  · -- reindex `h = a + 1 + k`, `0 ≤ k < L`
    have hre : ∑ h ∈ Finset.Ioc a (a + L), ee ((h : ℝ) * m / L) =
        ∑ k ∈ Finset.range L, ee (((a + 1 : ℤ) : ℝ) * m / L) * ee ((m : ℝ) / L) ^ k := by
      refine Finset.sum_nbij' (fun h => (h - a - 1).toNat) (fun k => a + 1 + k) ?_ ?_ ?_ ?_ ?_
      · intro h hh; simp only [Finset.mem_Ioc] at hh; simp only [Finset.mem_range]; omega
      · intro k hk; simp only [Finset.mem_range] at hk; simp only [Finset.mem_Ioc]; omega
      · intro h hh; simp only [Finset.mem_Ioc] at hh
        show a + 1 + ((h - a - 1).toNat : ℤ) = h; omega
      · intro k _
        show (a + 1 + (k : ℤ) - a - 1).toNat = k; omega
      · intro h hh
        simp only [Finset.mem_Ioc] at hh
        rw [← ee_nat_mul, ← ee_add]
        congr 1
        have : (((h - a - 1).toNat : ℕ) : ℝ) = (h : ℝ) - a - 1 := by
          have : (((h - a - 1).toNat : ℕ) : ℤ) = h - a - 1 := Int.toNat_of_nonneg (by omega)
          exact_mod_cast this
        rw [this]; push_cast; field_simp; ring
    rw [hre, ← Finset.mul_sum]
    set ζ := ee ((m : ℝ) / L)
    have hζ1 : ζ ≠ 1 := by
      intro h
      obtain ⟨n, hn⟩ := (ee_eq_one_iff _).1 h
      apply hdvd
      refine ⟨n, ?_⟩
      have : (m : ℝ) = L * n := by field_simp at hn; linarith
      exact_mod_cast this
    have hζL : ζ ^ L = 1 := by
      rw [← ee_nat_mul]
      have : (L : ℝ) * ((m : ℝ) / L) = ((m : ℤ) : ℝ) := by field_simp
      rw [this, ee_int]
    rw [geom_sum_eq hζ1, hζL]
    simp

/-- **Formula (2)**: `N / 2^{|A|} = (1/L) ∑_h e(-hτ) φ(h)`, valid whenever `L > 0`, every
edge `vu` divides `L`, and the denominator of `τ` divides `L`. -/
theorem eq_N (A : Finset (ℕ × ℕ)) (τ : ℚ) (L : ℕ) (hL : 0 < L)
    (hA : ∀ p ∈ A, 0 < p.1 * p.2 ∧ p.1 * p.2 ∣ L) (hτ : τ.den ∣ L) :
    (Ncount A τ : ℂ) / 2 ^ A.card =
      (1 / (L : ℂ)) * ∑ h ∈ freq L, ee (-((h : ℝ) * τ)) * phi A h := by
  classical
  have hLq : (L : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  -- every `L (σ(S) - τ)` is an integer
  have hint : ∀ S ⊆ A, ∃ m : ℤ, (L : ℚ) * (sigma S - τ) = m := by
    intro S hS
    have hσ : ∃ m : ℤ, (L : ℚ) * sigma S = m := by
      induction S using Finset.induction_on with
      | empty => exact ⟨0, by simp [sigma]⟩
      | insert p S hpS ih =>
        obtain ⟨m, hm⟩ := ih ((Finset.subset_insert _ _).trans hS)
        obtain ⟨hpos, ⟨c, hc⟩⟩ := hA p (hS (Finset.mem_insert_self _ _))
        refine ⟨c + m, ?_⟩
        unfold sigma at hm ⊢
        rw [Finset.sum_insert hpS, mul_add, hm, hc]
        have : ((p.1 : ℚ) * p.2) ≠ 0 := by exact_mod_cast hpos.ne'
        push_cast
        rw [mul_one_div, mul_div_cancel_left₀ _ this]
    obtain ⟨m, hm⟩ := hσ
    obtain ⟨c, hc⟩ := hτ
    refine ⟨m - c * τ.num, ?_⟩
    rw [mul_sub, hm]
    push_cast
    congr 1
    conv_lhs => rw [← Rat.num_div_den τ, hc]
    have : (τ.den : ℚ) ≠ 0 := by exact_mod_cast τ.den_pos.ne'
    push_cast
    field_simp
  -- the indicator of `σ(S) ≡ τ` as a geometric sum
  have hind : ∀ S ⊆ A, (if ∃ k : ℤ, sigma S - τ = k then (1 : ℂ) else 0) =
      (1 / (L : ℂ)) * ∑ h ∈ freq L, ee ((h : ℝ) * (((sigma S : ℚ) : ℝ) - τ)) := by
    intro S hS
    obtain ⟨m, hm⟩ := hint S hS
    have hσq : sigma S - τ = (m : ℚ) / L := by
      rw [eq_div_iff hLq, mul_comm, hm]
    have hσ : (((sigma S : ℚ) : ℝ) - τ) = (m : ℝ) / L := by
      have := congrArg (fun q : ℚ => (q : ℝ)) hσq
      push_cast at this
      exact this
    have hsum : ∑ h ∈ freq L, ee ((h : ℝ) * (((sigma S : ℚ) : ℝ) - τ)) =
        if (L : ℤ) ∣ m then (L : ℂ) else 0 := by
      rw [← lem_geom L hL (-((L : ℤ) / 2)) m]
      unfold freq
      have : (L : ℤ) - (L : ℤ) / 2 = -((L : ℤ) / 2) + L := by ring
      rw [this]
      refine Finset.sum_congr rfl (fun h _ => ?_)
      rw [hσ]; ring_nf
    rw [hsum]
    have hiff : (∃ k : ℤ, sigma S - τ = k) ↔ (L : ℤ) ∣ m := by
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have : (m : ℚ) = L * k := by rw [← hm, hk]
        exact_mod_cast this
      · rintro ⟨c, hc⟩
        refine ⟨c, ?_⟩
        rw [hσq, hc]; push_cast; field_simp
    by_cases hc : (L : ℤ) ∣ m
    · rw [if_pos hc, if_pos (hiff.2 hc)]
      have : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
      field_simp
    · rw [if_neg hc, if_neg (mt hiff.1 hc)]; simp
  -- the product formula for `φ`
  have hphi : ∀ h : ℤ, ee (-((h : ℝ) * τ)) * phi A h =
      (1 / 2 ^ A.card) * ∑ S ∈ A.powerset, ee ((h : ℝ) * (((sigma S : ℚ) : ℝ) - τ)) := by
    intro h
    have h1 : phi A h = (∏ p ∈ A, (1 + ee ((h : ℝ) / ((p.1 : ℝ) * p.2)))) / 2 ^ A.card := by
      unfold phi; rw [Finset.prod_div_distrib, Finset.prod_const]
    have h2 : ∏ p ∈ A, (1 + ee ((h : ℝ) / ((p.1 : ℝ) * p.2))) =
        ∑ S ∈ A.powerset, ee ((h : ℝ) * ((sigma S : ℚ) : ℝ)) := by
      have := Finset.prod_add (fun p : ℕ × ℕ => ee ((h : ℝ) / ((p.1 : ℝ) * p.2)))
        (fun _ => (1 : ℂ)) A
      simp only [Finset.prod_const_one, mul_one] at this
      rw [Finset.prod_congr rfl (fun p _ => add_comm _ _), this]
      refine Finset.sum_congr rfl (fun S _ => ?_)
      rw [← ee_sum]
      congr 1
      unfold sigma; push_cast; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_); ring
    rw [h1, h2, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [show (h : ℝ) * (((sigma S : ℚ) : ℝ) - τ) = -((h : ℝ) * τ) + (h : ℝ) * ((sigma S : ℚ) : ℝ)
      by ring, ee_add]
    ring
  rw [Finset.sum_congr rfl (fun h _ => hphi h)]
  unfold Ncount
  rw [Finset.card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.sum_congr rfl (fun S hS => hind S (Finset.mem_powerset.1 hS))]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun _ _ => ?_)
  ring

/-- eq. (3): `1 + e(x) = 2 e(x/2) cos πx`. -/
lemma eq_half (x : ℝ) : 1 + ee x = 2 * ee (x / 2) * (Real.cos (π * x) : ℂ) := by
  rw [mul_assoc, mul_comm (ee _), ← mul_assoc, Complex.ofReal_cos, Complex.two_cos]
  unfold ee
  rw [add_mul, ← Complex.exp_add, ← Complex.exp_add]
  have e1 : (↑(π * x) : ℂ) * Complex.I + 2 * ↑π * Complex.I * ↑(x / 2) = 2 * π * Complex.I * x := by
    push_cast; ring
  have e2 : -(↑(π * x) : ℂ) * Complex.I + 2 * ↑π * Complex.I * ↑(x / 2) = 0 := by
    push_cast; ring
  rw [e1, e2, Complex.exp_zero, add_comm]

/-- `|φ(h)| = ∏_{(v,u) ∈ A} |cos(π h/(uv))|`. -/
lemma norm_phi (A : Finset (ℕ × ℕ)) (h : ℤ) :
    ‖phi A h‖ = ∏ p ∈ A, |Real.cos (π * ((h : ℝ) / ((p.1 : ℝ) * p.2)))| := by
  unfold phi
  rw [norm_prod]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  rw [eq_half, norm_div, norm_mul, norm_mul, norm_ee, Complex.norm_real, Real.norm_eq_abs]
  simp

/-- Each factor of `φ(h)` has absolute value at most `1`, so `|φ(h)| ≤ 1` (§5). -/
lemma norm_phi_le_one (A : Finset (ℕ × ℕ)) (h : ℤ) : ‖phi A h‖ ≤ 1 := by
  rw [norm_phi]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => Real.abs_cos_le_one _)

/-- `φ(0) = 1` (§5). -/
lemma phi_zero (A : Finset (ℕ × ℕ)) : phi A 0 = 1 := by
  simp [phi, ee]

end Erdos306

end

section
-- Source: https://arxiv.org/src/2609.32140v1/anc/lean/Erdos306/Table.lean
/-
§6 of the paper: the `V × U` table and the three cases.

By the Chinese remainder theorem a frequency `h` is the same as its row labels
`ξ_v = h mod v` (`v ∈ V`) and its column labels `ζ_u = h mod u` (`u ∈ U`).  We record the row
labels as a single residue `ξ = h mod P_V`, `P_V = ∏_{v∈V} v` (so `ξ_v = ξ mod v`), and the
column labels as residues `ζ_u ∈ [0, u)`.  The `(v,u)` entry of the table is
`|cos π φ_{vu}|`, where the phase `φ_{vu}(ξ, ζ_u) = J/(uv)` for the CRT integer
`J ≡ ξ (mod P_V)`, `J ≡ ζ_u (mod u)`.

For the minor-arc bound we only need that the label map `h ↦ (ξ, ζ)` is *injective* on
frequencies (`label_inj`); surjectivity (the other half of the CRT bijection) is never used,
because all terms are nonnegative.
-/

namespace Erdos306

open Real Finset

variable (τ : ℚ) (y Y : ℕ)

/-- `P_V = ∏_{v ∈ V} v = |G_V|`. -/
def PV : ℕ := ∏ v ∈ Vset τ y, v

/-- The CRT integer `J ∈ [0, P_V u)` with `J ≡ ξ (mod P_V)` and `J ≡ z (mod u)`. -/
noncomputable def crt (u ξ z : ℕ) : ℕ :=
  if h : Nat.Coprime (PV τ y) u then (Nat.chineseRemainder h ξ z).1 else 0

/-- The phase `φ_{vu}(ξ, ζ_u) = J/(uv)` (defined modulo 1; only `|cos π ·|` and `‖·‖` of it are
used). -/
noncomputable def phase (u v ξ z : ℕ) : ℝ := (crt τ y u ξ z : ℝ) / ((u : ℝ) * v)

/-- `F_u(ξ, ζ_u) = ∏_{v ∈ V} |cos π φ_{vu}(ξ, ζ_u)|`: the weight of column `u`. -/
noncomputable def Fcol (u ξ z : ℕ) : ℝ := ∏ v ∈ Vset τ y, |Real.cos (π * phase τ y u v ξ z)|

/-- `S_u(ξ) = ∑_{ζ_u mod u} F_u(ξ, ζ_u)`. -/
noncomputable def Scol (u ξ : ℕ) : ℝ := ∑ z ∈ range u, Fcol τ y u ξ z

/-- Row labels `ξ` are *coherent* if `ξ ≡ M (mod v)` for all `v ∈ V`, for some `|M| ≤ y^7`. -/
def Coherent (ξ : ℤ) : Prop := ∃ M : ℤ, |M| ≤ (y : ℤ) ^ 7 ∧ ∀ v ∈ Vset τ y, (v : ℤ) ∣ ξ - M

/-- Case I: coherent rows `ξ ≡ M`, all columns matching (`ζ_u ≡ M (mod u)` for all `u`). -/
def CaseI (h : ℤ) : Prop :=
  ∃ M : ℤ, |M| ≤ (y : ℤ) ^ 7 ∧ (∀ v ∈ Vset τ y, (v : ℤ) ∣ h - M) ∧ ∀ u ∈ Uset y Y, (u : ℤ) ∣ h - M

/-- Case II: coherent rows `ξ ≡ M`, some mismatched column. -/
def CaseII (h : ℤ) : Prop :=
  ∃ M : ℤ, |M| ≤ (y : ℤ) ^ 7 ∧ (∀ v ∈ Vset τ y, (v : ℤ) ∣ h - M) ∧
    ∃ u ∈ Uset y Y, ¬ (u : ℤ) ∣ h - M

/-- Case III: incoherent rows. -/
def CaseIII (h : ℤ) : Prop := ¬ Coherent τ y h

variable {τ y Y}

/-- A product of distinct primes that all divide an integer `n` divides `n`. -/
lemma prod_primes_dvd_int (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) (n : ℤ)
    (h : ∀ p ∈ t, (p : ℤ) ∣ n) : ((∏ p ∈ t, p : ℕ) : ℤ) ∣ n := by
  apply Int.natCast_dvd.2
  exact Finset.prod_primes_dvd _ (fun p hp => (ht p hp).prime)
    (fun p hp => Int.natCast_dvd.1 (h p hp))

/-- `u > 2y² ≥ v` for `u ∈ U`, `v ∈ V`. -/
lemma v_lt_u (hL : Large τ y) {u v : ℕ} (hu : u ∈ Uset y Y) (hv : v ∈ Vset τ y) : v < u := by
  have h1 := (le_of_mem_Vset hL hv).2
  have h2 := (bounds_of_mem_Uset hu).1
  have hy := hL.y_ge
  have : 2 * y ^ 2 < y ^ 8 := by
    have : y ^ 8 = y ^ 2 * y ^ 6 := by ring
    have h6 : 2 < y ^ 6 := by
      calc 2 < 3 ^ 6 := by norm_num
        _ ≤ y ^ 6 := Nat.pow_le_pow_left hy 6
    rw [this]
    have : 0 < y ^ 2 := by positivity
    nlinarith
  omega

/-- For `v ∈ V` and `u ∈ U`: `P_V` and `u` are coprime. -/
lemma coprime_PV_u (hL : Large τ y) {u : ℕ} (hu : u ∈ Uset y Y) : Nat.Coprime (PV τ y) u := by
  apply Nat.Coprime.prod_left
  intro v hv
  exact (Nat.coprime_primes (prime_of_mem_Vset hv) (prime_of_mem_Uset hu)).2
    (v_lt_u hL hu hv).ne

/-- `|W| ≥ 100` (from eq. (1) and the numerical condition of Lemma 8.2). -/
lemma card_W_ge (hL : Large τ y) : 100 ≤ (Wset y).card := by
  have h1 := hL.card_W
  have h2 := hL.count
  have hy : (3 : ℝ) ≤ y := by exact_mod_cast hL.y_ge
  have hlog : 0 < Real.log y := Real.log_pos (by linarith)
  have e1 : (y : ℝ) ^ 2 / (16 * Real.log y) - (y : ℝ) ^ 2 / (20 * Real.log y) =
      ((y : ℝ) ^ 2 / (8 * Real.log y)) / 10 := by field_simp; ring
  have : (100 : ℝ) ≤ (Wset y).card := by linarith
  exact_mod_cast this

/-- `P_V > y^8`. -/
lemma PV_gt_y8 (hL : Large τ y) : y ^ 8 < PV τ y := by
  have hW := card_W_ge hL
  have h1 : ∏ w ∈ Wset y, w ≤ PV τ y := by
    unfold PV
    apply Finset.prod_le_prod_of_subset_of_one_le' Wset_subset_Vset
    intro v hv _
    exact (prime_of_mem_Vset hv).one_lt.le
  have h2 : (y ^ 2 + 1) ^ (Wset y).card ≤ ∏ w ∈ Wset y, w :=
    Finset.pow_card_le_prod _ _ _ (fun w hw => (mem_Wset.1 hw).1)
  have h3 : (y ^ 2 + 1) ^ 4 ≤ (y ^ 2 + 1) ^ (Wset y).card :=
    Nat.pow_le_pow_right (by positivity) (by omega)
  have h4 : y ^ 8 < (y ^ 2 + 1) ^ 4 := by
    calc y ^ 8 = (y ^ 2) ^ 4 := by ring
      _ < (y ^ 2 + 1) ^ 4 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  omega

/-- `P_V > 2 y^7` (so a coherent `ξ` determines `M`). -/
lemma PV_gt (hL : Large τ y) : 2 * (y : ℤ) ^ 7 < PV τ y := by
  have h := PV_gt_y8 hL
  have hy := hL.y_ge
  have : 2 * y ^ 7 < y ^ 8 := by
    have : y ^ 8 = y * y ^ 7 := by ring
    rw [this]
    have : 0 < y ^ 7 := by positivity
    nlinarith
  exact_mod_cast (by omega : 2 * y ^ 7 < PV τ y)

/-- `L > 2 y^7 + 2`. -/
lemma L_gt (hL : Large τ y) : 2 * (y : ℤ) ^ 7 + 2 < Lnum τ y Y := by
  have h := PV_gt_y8 hL
  have hy := hL.y_ge
  have h1 : PV τ y ≤ Lnum τ y Y := by
    unfold PV Lnum
    apply Finset.prod_le_prod_of_subset_of_one_le' Finset.subset_union_left
    intro p hp _
    rcases Finset.mem_union.1 hp with h | h
    · exact (prime_of_mem_Vset h).one_lt.le
    · exact (prime_of_mem_Uset h).one_lt.le
  have : 2 * y ^ 7 + 2 < y ^ 8 := by
    have : y ^ 8 = y * y ^ 7 := by ring
    rw [this]
    have : 3 ≤ y ^ 7 := le_trans hy (Nat.le_self_pow (by norm_num) y)
    nlinarith
  exact_mod_cast (by omega : 2 * y ^ 7 + 2 < Lnum τ y Y)

/-- The CRT integer is `≡ ξ (mod P_V)`. -/
lemma crt_modEq_xi (hL : Large τ y) {u : ℕ} (hu : u ∈ Uset y Y) (ξ z : ℕ) :
    ((crt τ y u ξ z : ℕ) : ℤ) ≡ ξ [ZMOD PV τ y] := by
  have hc := coprime_PV_u hL hu
  have h := (Nat.chineseRemainder hc ξ z).2.1
  unfold crt
  rw [dif_pos hc]
  exact Int.modEq_iff_dvd.2 (Nat.modEq_iff_dvd.1 h)

/-- The CRT integer is `≡ ζ_u (mod u)`. -/
lemma crt_modEq_z (hL : Large τ y) {u : ℕ} (hu : u ∈ Uset y Y) (ξ z : ℕ) :
    ((crt τ y u ξ z : ℕ) : ℤ) ≡ z [ZMOD u] := by
  have hc := coprime_PV_u hL hu
  have h := (Nat.chineseRemainder hc ξ z).2.2
  unfold crt
  rw [dif_pos hc]
  exact Int.modEq_iff_dvd.2 (Nat.modEq_iff_dvd.1 h)

/-- The phase depends only on `J` modulo `uv`: if `J ≡ ξ (mod v)` and `J ≡ z (mod u)` then
`|cos π φ_{vu}(ξ,z)| = |cos(π J/(uv))|` and `‖φ_{vu}(ξ,z)‖ = ‖J/(uv)‖`. -/
lemma phase_congr (hL : Large τ y) {u v : ℕ} (hu : u ∈ Uset y Y) (hv : v ∈ Vset τ y)
    (ξ z : ℕ) (J : ℤ) (hJv : (v : ℤ) ∣ J - ξ) (hJu : (u : ℤ) ∣ J - z) :
    ∃ n : ℤ, phase τ y u v ξ z = (J : ℝ) / ((u : ℝ) * v) + n := by
  set C : ℤ := ((crt τ y u ξ z : ℕ) : ℤ) with hC
  have hvP : (v : ℤ) ∣ (PV τ y : ℤ) := by
    exact_mod_cast Finset.dvd_prod_of_mem (fun v : ℕ => v) hv
  have h1 : (v : ℤ) ∣ C - J := by
    have := hvP.trans (crt_modEq_xi hL hu ξ z).dvd
    have e : C - J = -(J - ξ) - ((ξ : ℤ) - C) := by ring
    rw [e]; exact dvd_sub (dvd_neg.2 hJv) this
  have h2 : (u : ℤ) ∣ C - J := by
    have := (crt_modEq_z hL hu ξ z).dvd
    have e : C - J = -(J - z) - ((z : ℤ) - C) := by ring
    rw [e]; exact dvd_sub (dvd_neg.2 hJu) this
  have hcop : IsCoprime (u : ℤ) (v : ℤ) := Nat.isCoprime_iff_coprime.2
    ((Nat.coprime_primes (prime_of_mem_Uset hu) (prime_of_mem_Vset hv)).2 (v_lt_u hL hu hv).ne')
  obtain ⟨n, hn⟩ := hcop.mul_dvd h2 h1
  refine ⟨n, ?_⟩
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (prime_of_mem_Uset hu).pos
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (prime_of_mem_Vset hv).pos
  have hCR : ((crt τ y u ξ z : ℕ) : ℝ) = (J : ℝ) + (u : ℝ) * v * n := by
    have := congrArg (fun m : ℤ => (m : ℝ)) hn
    push_cast at this
    rw [hC] at this
    push_cast at this
    linarith
  unfold phase
  rw [hCR]
  field_simp

/-- Uniqueness of `M` for coherent row labels. -/
lemma coherent_unique (hL : Large τ y) {ξ M M' : ℤ} (hM : |M| ≤ (y : ℤ) ^ 7)
    (hM' : |M'| ≤ (y : ℤ) ^ 7) (h1 : ∀ v ∈ Vset τ y, (v : ℤ) ∣ ξ - M)
    (h2 : ∀ v ∈ Vset τ y, (v : ℤ) ∣ ξ - M') : M = M' := by
  have hd : ((PV τ y : ℕ) : ℤ) ∣ M' - M := by
    apply prod_primes_dvd_int _ (fun v hv => prime_of_mem_Vset hv)
    intro v hv
    have := dvd_sub (h1 v hv) (h2 v hv)
    have e : ξ - M - (ξ - M') = M' - M := by ring
    rwa [e] at this
  have hlt : |M' - M| < (PV τ y : ℤ) := by
    have := PV_gt (τ := τ) hL
    have h3 := abs_sub M' M
    linarith
  have := Int.eq_zero_of_abs_lt_dvd hd hlt
  linarith

/-- Injectivity of the label map on frequencies (half of the CRT bijection): two frequencies
with the same residue modulo `P_V` and modulo every `u ∈ U` are equal. -/
lemma label_inj {h h' : ℤ} (hh : h ∈ freq (Lnum τ y Y))
    (hh' : h' ∈ freq (Lnum τ y Y)) (hV : (PV τ y : ℤ) ∣ h - h')
    (hU : ∀ u ∈ Uset y Y, (u : ℤ) ∣ h - h') : h = h' := by
  have hd : ((Lnum τ y Y : ℕ) : ℤ) ∣ h - h' := by
    apply prod_primes_dvd_int
    · intro p hp
      rcases Finset.mem_union.1 hp with h | h
      · exact prime_of_mem_Vset h
      · exact prime_of_mem_Uset h
    · intro p hp
      rcases Finset.mem_union.1 hp with hpV | hpU
      · have hvP : (p : ℤ) ∣ (PV τ y : ℤ) := by
          exact_mod_cast Finset.dvd_prod_of_mem (fun v : ℕ => v) hpV
        exact hvP.trans hV
      · exact hU p hpU
  have hlt : |h - h'| < (Lnum τ y Y : ℤ) := by
    simp only [freq, Finset.mem_Ioc] at hh hh'
    rw [abs_lt]
    constructor <;> linarith
  have := Int.eq_zero_of_abs_lt_dvd hd hlt
  linarith

/-- Every frequency falls into exactly one of the three cases. -/
lemma three_cases (hL : Large τ y) (h : ℤ) :
    (CaseI τ y Y h ∨ CaseII τ y Y h ∨ CaseIII τ y h) ∧
    ¬ (CaseI τ y Y h ∧ CaseII τ y Y h) ∧ ¬ (CaseI τ y Y h ∧ CaseIII τ y h) ∧
    ¬ (CaseII τ y Y h ∧ CaseIII τ y h) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases hc : Coherent τ y h
    · obtain ⟨M, hM, hMv⟩ := hc
      by_cases hU : ∀ u ∈ Uset y Y, (u : ℤ) ∣ h - M
      · exact Or.inl ⟨M, hM, hMv, hU⟩
      · push Not at hU
        exact Or.inr (Or.inl ⟨M, hM, hMv, hU⟩)
    · exact Or.inr (Or.inr hc)
  · rintro ⟨⟨M, hM, hMv, hMu⟩, ⟨M', hM', hM'v, u, hu, hnd⟩⟩
    have := coherent_unique hL hM hM' hMv hM'v
    subst this
    exact hnd (hMu u hu)
  · rintro ⟨⟨M, hM, hMv, -⟩, hIII⟩
    exact hIII ⟨M, hM, hMv⟩
  · rintro ⟨⟨M, hM, hMv, -⟩, hIII⟩
    exact hIII ⟨M, hM, hMv⟩

/-- Every `|M| ≤ y^7` is a frequency. -/
lemma mem_freq_of_small (hL : Large τ y) {M : ℤ} (hM : |M| ≤ (y : ℤ) ^ 7) :
    M ∈ freq (Lnum τ y Y) := by
  have h := L_gt (Y := Y) hL
  simp only [freq, Finset.mem_Ioc]
  rw [abs_le] at hM
  constructor <;> omega

/-- Case I consists exactly of the frequencies `h` with `|h| ≤ y^7` (the major arcs). -/
lemma caseI_iff (hL : Large τ y) {h : ℤ} (hh : h ∈ freq (Lnum τ y Y)) :
    CaseI τ y Y h ↔ |h| ≤ (y : ℤ) ^ 7 := by
  constructor
  · rintro ⟨M, hM, hMv, hMu⟩
    have hPV : (PV τ y : ℤ) ∣ h - M := by
      apply prod_primes_dvd_int _ (fun v hv => prime_of_mem_Vset hv)
      exact hMv
    have := label_inj hh (mem_freq_of_small hL hM) hPV hMu
    rw [this]; exact hM
  · intro hsmall
    exact ⟨h, hsmall, fun v _ => by simp, fun u _ => by simp⟩

/-- `|φ(h)|` is the product of the column weights: `|φ(h)| = ∏_{u ∈ U} F_u(ξ, ζ_u)` with
`ξ = h mod P_V`, `ζ_u = h mod u`. -/
lemma norm_phi_eq_prod_Fcol (hL : Large τ y) (h : ℤ) :
    ‖phi (Aset τ y Y) h‖ =
      ∏ u ∈ Uset y Y, Fcol τ y u (h % (PV τ y : ℤ)).toNat (h % (u : ℤ)).toNat := by
  rw [norm_phi, Aset, Finset.prod_product_right]
  refine Finset.prod_congr rfl (fun u hu => ?_)
  unfold Fcol
  refine Finset.prod_congr rfl (fun v hv => ?_)
  have hPV0 : (PV τ y : ℤ) ≠ 0 := by
    have := PV_gt (τ := τ) hL
    have : (0 : ℤ) ≤ (y : ℤ) ^ 7 := by positivity
    omega
  have hu0 : (u : ℤ) ≠ 0 := by exact_mod_cast (prime_of_mem_Uset hu).ne_zero
  have hvP : (v : ℤ) ∣ (PV τ y : ℤ) := by
    exact_mod_cast Finset.dvd_prod_of_mem (fun v : ℕ => v) hv
  have hJv : (v : ℤ) ∣ h - (((h % (PV τ y : ℤ)).toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hPV0)]
    exact hvP.trans (Int.dvd_self_sub_emod)
  have hJu : (u : ℤ) ∣ h - (((h % (u : ℤ)).toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hu0)]
    exact Int.dvd_self_sub_emod
  obtain ⟨n, hn⟩ := phase_congr hL hu hv _ _ h hJv hJu
  rw [hn, mul_add, mul_comm π ((n : ℤ) : ℝ), Real.cos_add_int_mul_pi, abs_mul, abs_neg_one_zpow,
    one_mul, mul_comm (u : ℝ)]

/-- eq. (4) Once the row labels `ξ` are fixed, the sum over column labels factorises:
`∑_ζ ∏_u F_u(ξ, ζ_u) = ∏_u S_u(ξ)`. -/
lemma eq_factor (ξ : ℕ) :
    ∑ ζ ∈ Fintype.piFinset (fun u : Uset y Y => range (u : ℕ)),
        ∏ u : Uset y Y, Fcol τ y u ξ (ζ u) =
      ∏ u ∈ Uset y Y, Scol τ y u ξ := by
  rw [← Finset.prod_coe_sort (Uset y Y) (fun u => Scol τ y u ξ)]
  unfold Scol
  exact (Finset.prod_univ_sum (fun u : Uset y Y => range (u : ℕ))
    (fun u z => Fcol τ y u ξ z)).symm

/-- Column weights are nonnegative. -/
lemma Fcol_nonneg (u ξ z : ℕ) : 0 ≤ Fcol τ y u ξ z :=
  Finset.prod_nonneg (fun _ _ => abs_nonneg _)

/-- Column weights are at most `1` (§6). -/
lemma Fcol_le_one (u ξ z : ℕ) : Fcol τ y u ξ z ≤ 1 :=
  Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => Real.abs_cos_le_one _)

/-- `S_u(ξ) ≥ 0`. -/
lemma Scol_nonneg (u ξ : ℕ) : 0 ≤ Scol τ y u ξ :=
  Finset.sum_nonneg (fun _ _ => Fcol_nonneg _ _ _)

end Erdos306

end

section
-- Source: https://arxiv.org/src/2609.32140v1/anc/lean/Erdos306/Major.lean
/-
§7 of the paper: Case I, the major arcs (Proposition 7.1), by positivity.
-/

namespace Erdos306

open Real Finset

variable (τ : ℚ) (y Y : ℕ)

/-- `P(M) = ∏_{(v,u) ∈ A} cos(π M/(uv))`. -/
noncomputable def Pmaj (M : ℤ) : ℝ :=
  ∏ p ∈ Aset τ y Y, Real.cos (π * ((M : ℝ) / ((p.1 : ℝ) * p.2)))

/-- `Σ_maj = (1/L) ∑_{|M| ≤ y^7} e(-Mτ) φ(M)`: the part of eq. (2) coming from case I. -/
noncomputable def SigmaMaj : ℂ :=
  (1 / (Lnum τ y Y : ℂ)) *
    ∑ M ∈ Finset.Icc (-(y : ℤ) ^ 7) ((y : ℤ) ^ 7), ee (-((M : ℝ) * τ)) * phi (Aset τ y Y) M

variable {τ y Y}

/-- `Re e(x) = cos 2πx`. -/
lemma ee_re (x : ℝ) : (ee x).re = Real.cos (2 * π * x) := by
  unfold ee
  rw [Complex.exp_re]
  have h1 : (2 * (π : ℂ) * Complex.I * x).re = 0 := by simp
  have h2 : (2 * (π : ℂ) * Complex.I * x).im = 2 * π * x := by simp
  rw [h1, h2, Real.exp_zero, one_mul]

/-- `Im e(x) = sin 2πx`. -/
lemma ee_im (x : ℝ) : (ee x).im = Real.sin (2 * π * x) := by
  unfold ee
  rw [Complex.exp_im]
  have h1 : (2 * (π : ℂ) * Complex.I * x).re = 0 := by simp
  have h2 : (2 * (π : ℂ) * Complex.I * x).im = 2 * π * x := by simp
  rw [h1, h2, Real.exp_zero, one_mul]

/-- Proposition 7.1, Step 1: `φ(M) = e(Mμ) P(M)`, hence `e(-Mτ) φ(M) = e(Mβ) P(M)` with
`β = μ - τ`. -/
lemma major_step1 (M : ℤ) :
    ee (-((M : ℝ) * τ)) * phi (Aset τ y Y) M =
      ee ((M : ℝ) * (mu τ y Y - τ)) * (Pmaj τ y Y M : ℂ) := by
  have hphi : phi (Aset τ y Y) M = ee ((M : ℝ) * mu τ y Y) * (Pmaj τ y Y M : ℂ) := by
    unfold phi Pmaj
    have : ∀ p ∈ Aset τ y Y, (1 + ee ((M : ℝ) / ((p.1 : ℝ) * p.2))) / 2 =
        ee ((M : ℝ) / ((p.1 : ℝ) * p.2) / 2) *
          (Real.cos (π * ((M : ℝ) / ((p.1 : ℝ) * p.2))) : ℂ) := by
      intro p _
      rw [eq_half]; ring
    rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, ← ee_sum, Complex.ofReal_prod]
    congr 2
    unfold mu
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    ring
  rw [hphi, ← mul_assoc, ← ee_add]
  congr 2
  ring

/-- Proposition 7.1, Step 2: `P(M) > 0` for `|M| ≤ y^7`; `P(0) = 1`; `P(-M) = P(M)`. -/
lemma major_step2 (hL : Large τ y) {M : ℤ} (hM : |M| ≤ (y : ℤ) ^ 7) :
    0 < Pmaj τ y Y M := by
  unfold Pmaj
  refine Finset.prod_pos (fun p hp => ?_)
  obtain ⟨hv, hu⟩ := mem_Aset.1 hp
  have hv2 := (le_of_mem_Vset hL hv).1
  have hu8 := (bounds_of_mem_Uset hu).1
  have hy := hL.y_ge
  -- `2|M| ≤ 2y^7 < 2y^8 < vu`
  have hy78 : y ^ 7 < y ^ 8 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  have hMR : |(M : ℝ)| ≤ (y : ℝ) ^ 7 := by exact_mod_cast hM
  have hprod : 2 * (y : ℝ) ^ 8 < (p.1 : ℝ) * p.2 := by
    have : 2 * y ^ 8 < p.1 * p.2 := by nlinarith
    exact_mod_cast this
  have hy78R : (y : ℝ) ^ 7 < (y : ℝ) ^ 8 := by exact_mod_cast hy78
  have hpos : (0 : ℝ) < (p.1 : ℝ) * p.2 := by
    have : (0 : ℝ) ≤ (y : ℝ) ^ 8 := by positivity
    linarith
  have hx : |(M : ℝ) / ((p.1 : ℝ) * p.2)| < 1 / 2 := by
    rw [abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
    linarith
  apply Real.cos_pos_of_mem_Ioo
  rw [abs_lt] at hx
  constructor <;> nlinarith [Real.pi_pos]

/-- Proposition 7.1, Step 2: `P(0) = 1`. -/
lemma Pmaj_zero : Pmaj τ y Y 0 = 1 := by
  simp [Pmaj]

/-- Proposition 7.1, Step 2: `P(-M) = P(M)` (cosine is even). -/
lemma Pmaj_neg (M : ℤ) : Pmaj τ y Y (-M) = Pmaj τ y Y M := by
  unfold Pmaj
  refine Finset.prod_congr rfl (fun p _ => ?_)
  push_cast
  rw [neg_div, mul_neg, Real.cos_neg]

/-- **Proposition 7.1 (major arcs).**  `Σ_maj` is real and `Σ_maj ≥ 1/L`.
(Pair `M` with `-M`: the contribution is `2 cos(2πMβ) P(M) ≥ 0`, since `|2πMβ| < π/2` by the
tuning lemma; and `M = 0` contributes `1/L`.) -/
theorem prop_major (hL : Large τ y) (hT : Tuned τ y Y) :
    (SigmaMaj τ y Y).im = 0 ∧ 1 / (Lnum τ y Y : ℝ) ≤ (SigmaMaj τ y Y).re := by
  set β : ℝ := mu τ y Y - τ with hβ
  set K : ℤ := (y : ℤ) ^ 7 with hK
  have hS : SigmaMaj τ y Y = ((1 / (Lnum τ y Y : ℝ) : ℝ) : ℂ) *
      ∑ M ∈ Finset.Icc (-K) K, ee ((M : ℝ) * β) * (Pmaj τ y Y M : ℂ) := by
    unfold SigmaMaj
    rw [Finset.sum_congr rfl (fun M _ => major_step1 M)]
    push_cast; ring
  have hre : ∀ M : ℤ, (ee ((M : ℝ) * β) * (Pmaj τ y Y M : ℂ)).re =
      Real.cos (2 * π * ((M : ℝ) * β)) * Pmaj τ y Y M := by
    intro M; rw [Complex.mul_re, ee_re]; simp
  have him : ∀ M : ℤ, (ee ((M : ℝ) * β) * (Pmaj τ y Y M : ℂ)).im =
      Real.sin (2 * π * ((M : ℝ) * β)) * Pmaj τ y Y M := by
    intro M; rw [Complex.mul_im, ee_im]; simp
  have hLpos : (0 : ℝ) < 1 / (Lnum τ y Y : ℝ) := by
    have h1 := L_gt (Y := Y) hL
    have h2 : (0 : ℤ) ≤ (y : ℤ) ^ 7 := by positivity
    have : (0 : ℤ) < (Lnum τ y Y : ℤ) := by linarith
    have : (0 : ℝ) < (Lnum τ y Y : ℝ) := by exact_mod_cast this
    positivity
  constructor
  · -- Step 3: pairing `M ↔ -M` makes the sum real
    rw [hS, Complex.im_ofReal_mul, Complex.im_sum]
    simp only [him]
    have : ∑ M ∈ Finset.Icc (-K) K, Real.sin (2 * π * ((M : ℝ) * β)) * Pmaj τ y Y M = 0 := by
      refine Finset.sum_involution (fun M _ => -M) ?_ ?_ ?_ ?_
      · intro M _
        rw [Pmaj_neg]; push_cast
        rw [show 2 * π * (-(M : ℝ) * β) = -(2 * π * ((M : ℝ) * β)) by ring, Real.sin_neg]
        ring
      · intro M _ hne heq
        apply hne
        change -M = M at heq
        have : M = 0 := by omega
        subst this; simp
      · intro M hM; simp only [Finset.mem_Icc] at hM ⊢; omega
      · intro M _; simp
    rw [this, mul_zero]
  · -- Step 4: every term is nonnegative, and `M = 0` contributes `1`
    rw [hS, Complex.re_ofReal_mul, Complex.re_sum]
    simp only [hre]
    have hβ1 : |β| ≤ HV τ y / (2 * (y : ℝ) ^ 8) := by
      rw [abs_le]
      constructor
      · linarith [hT.beta_ge]
      · have := hT.beta_nonpos
        have hHV := HV_pos hL
        have : 0 ≤ HV τ y / (2 * (y : ℝ) ^ 8) := by positivity
        linarith
    have hy : (3 : ℝ) ≤ y := by exact_mod_cast hL.y_ge
    have hterm : ∀ M ∈ Finset.Icc (-K) K,
        0 ≤ Real.cos (2 * π * ((M : ℝ) * β)) * Pmaj τ y Y M := by
      intro M hM
      have hMabs : |M| ≤ K := abs_le.2 (Finset.mem_Icc.1 hM)
      refine mul_nonneg ?_ (major_step2 hL hMabs).le
      apply Real.cos_nonneg_of_mem_Icc
      -- `|2 M β| ≤ 2 y^7 · H_V/(2y^8) = H_V / y < 1/2`
      have hMR : |(M : ℝ)| ≤ (y : ℝ) ^ 7 := by exact_mod_cast hMabs
      have hy0 : (0 : ℝ) < y := by linarith
      have hb : |(M : ℝ) * β| ≤ (y : ℝ) ^ 7 * (HV τ y / (2 * (y : ℝ) ^ 8)) := by
        rw [abs_mul]
        exact mul_le_mul hMR hβ1 (abs_nonneg _) (by positivity)
      have he : (y : ℝ) ^ 7 * (HV τ y / (2 * (y : ℝ) ^ 8)) = HV τ y / (2 * y) := by
        field_simp
      rw [he] at hb
      have hmaj := hL.major
      have : HV τ y / (2 * y) < 1 / 4 := by
        rw [div_lt_iff₀ (by positivity)]; linarith
      rw [abs_le] at hb
      constructor <;> nlinarith [Real.pi_pos]
    have h0mem : (0 : ℤ) ∈ Finset.Icc (-K) K := by
      simp only [Finset.mem_Icc]
      have : (0 : ℤ) ≤ K := by positivity
      omega
    have := Finset.single_le_sum hterm h0mem
    simp only [Int.cast_zero, zero_mul, mul_zero, Real.cos_zero, one_mul, Pmaj_zero] at this
    nlinarith

end Erdos306

end

section
-- Source: https://arxiv.org/src/2609.32140v1/anc/lean/Erdos306/Columns.lean
/-
§8 of the paper: two lemmas about a single column.

* Lemma 8.1 (`lem_cos`):        `|cos πx| ≤ exp(-2‖x‖²)`;
* eq. (5) (`eq_pf`):              changing only the column label by `s` shifts the phase in row `v`
                                by `s v̄ / u (mod 1)`;
* Lemma 8.2 (`lem_count`):      few test primes are "invisible" (divisor count);
* Lemma 8.3 (`lem_unique`):     separation;
* Lemma 8.4 (`lem_admissible`): no wrap-around.

Inverses modulo `u` are avoided: "`‖s w̄/u‖ ≤ δ`" is expressed as
"`t w ≡ s (mod u)` for some integer `|t| ≤ δ u`" (`Invisible`); the two are equivalent, since
`t` is then the balanced representative of `s w̄` (see the proof of Lemma 8.2 in the paper).
-/

namespace Erdos306

open Real Finset

open scoped Classical

/-- **Lemma 8.1.**  For all real `x`, `|cos πx| ≤ exp(-2‖x‖²)`. -/
theorem lem_cos (x : ℝ) : |Real.cos (π * x)| ≤ exp (-2 * nint x ^ 2) := by
  set t := x - round x with ht
  -- `|cos πx|` has period 1 and is even, so `|cos πx| = cos πa` with `a = ‖x‖ ∈ [0, 1/2]`
  have hper : |Real.cos (π * x)| = |Real.cos (π * t)| := by
    have : π * x = π * t + ((round x : ℤ) : ℝ) * π := by rw [ht]; ring
    rw [this, Real.cos_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]
  set a := nint x with ha
  have hat : a = |t| := rfl
  have ha0 : 0 ≤ a := nint_nonneg x
  have ha1 : a ≤ 1 / 2 := nint_le_half x
  have hcos_abs : |Real.cos (π * t)| = Real.cos (π * a) := by
    have h1 : Real.cos (π * t) = Real.cos (π * a) := by
      rw [hat]
      rcases abs_cases t with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h]
      · rw [h, mul_neg, Real.cos_neg]
    rw [h1]
    apply abs_of_nonneg
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_pos]
  rw [hper, hcos_abs]
  have hc0 : 0 ≤ Real.cos (π * a) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_pos]
  -- `sin πa ≥ 2a` (concavity, i.e. Jordan's inequality)
  have hsin : 2 * a ≤ Real.sin (π * a) := by
    have := Real.mul_le_sin (x := π * a) (by positivity) (by nlinarith [Real.pi_pos])
    have e : 2 / π * (π * a) = 2 * a := by field_simp
    linarith
  -- `cos² πa = 1 - sin² πa ≤ 1 - 4a² ≤ e^{-4a²}`
  have hsq : Real.cos (π * a) ^ 2 ≤ exp (-4 * a ^ 2) := by
    have h1 : Real.cos (π * a) ^ 2 = 1 - Real.sin (π * a) ^ 2 := by
      rw [← Real.sin_sq_add_cos_sq (π * a)]; ring
    have h2 : (2 * a) ^ 2 ≤ Real.sin (π * a) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) hsin
    have h3 := Real.add_one_le_exp (-4 * a ^ 2)
    nlinarith
  by_contra hcon
  push Not at hcon
  have : exp (-2 * a ^ 2) ^ 2 < Real.cos (π * a) ^ 2 :=
    pow_lt_pow_left₀ hcon (by positivity) (by norm_num)
  rw [← Real.exp_nat_mul] at this
  have e : ((2 : ℕ) : ℝ) * (-2 * a ^ 2) = -4 * a ^ 2 := by push_cast; ring
  rw [e] at this
  linarith

variable {τ : ℚ} {y Y : ℕ}

/-- **eq. (5)**: two frequencies with the same row labels `ξ` and column labels `z, z'` at `u`:
their phases in row `v` differ by `k/u` where `v k ≡ z - z' (mod u)`, i.e. by `s v̄/u` with
`s = z - z'`. -/
lemma eq_pf (hL : Large τ y) {u v : ℕ} (hu : u ∈ Uset y Y) (hv : v ∈ Vset τ y) (ξ z z' : ℕ) :
    ∃ k : ℤ, (u : ℤ) ∣ (v : ℤ) * k - ((z : ℤ) - z') ∧
      phase τ y u v ξ z - phase τ y u v ξ z' = (k : ℝ) / u := by
  have hJ := crt_modEq_xi hL hu ξ z
  have hJ' := crt_modEq_xi hL hu ξ z'
  have hvP : (v : ℤ) ∣ (PV τ y : ℤ) := by
    exact_mod_cast Finset.dvd_prod_of_mem (fun v : ℕ => v) hv
  -- `J ≡ J' (mod v)`, so `J - J' = v k`
  have hdv : (v : ℤ) ∣ ((crt τ y u ξ z : ℕ) : ℤ) - (crt τ y u ξ z' : ℕ) :=
    hvP.trans ((hJ.trans hJ'.symm).symm.dvd)
  obtain ⟨k, hk⟩ := hdv
  refine ⟨k, ?_, ?_⟩
  · have h1 := (crt_modEq_z hL hu ξ z).symm.dvd
    have h2 := (crt_modEq_z hL hu ξ z').symm.dvd
    rw [← hk]
    have := dvd_sub h1 h2
    have e : ((crt τ y u ξ z : ℕ) : ℤ) - (crt τ y u ξ z' : ℕ) - ((z : ℤ) - z') =
        ((crt τ y u ξ z : ℕ) - (z : ℤ)) - ((crt τ y u ξ z' : ℕ) - (z' : ℤ)) := by ring
    rw [e]; exact this
  · have hu0 : (0 : ℝ) < u := by exact_mod_cast (prime_of_mem_Uset hu).pos
    have hv0 : (0 : ℝ) < v := by exact_mod_cast (prime_of_mem_Vset hv).pos
    have hkR : ((crt τ y u ξ z : ℕ) : ℝ) - (crt τ y u ξ z' : ℕ) = (v : ℝ) * k := by
      have := congrArg (fun n : ℤ => (n : ℝ)) hk
      push_cast at this
      exact this
    unfold phase
    rw [div_sub_div_same, hkR]
    field_simp

/-- A test prime `w` is *invisible* for the shift `s` at the column `u` if `‖s w̄/u‖ ≤ δ`,
i.e. if `t w ≡ s (mod u)` for some integer `t` with `|t| ≤ δ u`. -/
def Invisible (d : ℝ) (u : ℕ) (s : ℤ) (w : ℕ) : Prop :=
  ∃ t : ℤ, |(t : ℝ)| ≤ d * u ∧ (u : ℤ) ∣ t * w - s

/-- **Lemma 8.2 (divisor count).**  Let `u ∈ U` and `s ≢ 0 (mod u)`.  If `y` is large, then
`#{w ∈ W : ‖s w̄/u‖ ≤ δ} ≤ 5(4δy² + 2) ≤ |W|/2`.
(Each invisible `w` divides one of the at most `4δy²+2` nonzero integers `s + uℓ`, of absolute
value at most `y^{11}`, and such an integer has at most `5` prime factors exceeding `y²`.) -/
theorem lem_count (hL : Large τ y) (hY : Y ≤ y ^ 9) {u : ℕ} (hu : u ∈ Uset y Y) {s : ℤ}
    (hs : ¬ (u : ℤ) ∣ s) :
    (((Wset y).filter (fun w => Invisible (delta y) u s w)).card : ℝ)
        ≤ 5 * (4 * delta y * (y : ℝ) ^ 2 + 2) ∧
      5 * (4 * delta y * (y : ℝ) ^ 2 + 2) ≤ ((Wset y).card : ℝ) / 2 := by
  have hy3 : 3 ≤ y := hL.y_ge
  have hyR : (3 : ℝ) ≤ y := by exact_mod_cast hy3
  have hlog : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) (by linarith)
  have hlog2 := Real.log_two_gt_d9
  have hlogpos : 0 < Real.log y := by linarith
  set δ := delta y with hδdef
  have hδ0 : 0 < δ := by rw [hδdef, delta]; positivity
  have hδ1 : 2 * δ ≤ 1 := by
    rw [hδdef, delta]
    rw [mul_one_div, div_le_one (by positivity)]
    linarith
  obtain ⟨hu8, huY, hup⟩ := mem_Uset.1 hu
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hup.pos
  have hu0' : (0 : ℤ) < u := by exact_mod_cast hup.pos
  have huy9 : (u : ℝ) ≤ (y : ℝ) ^ 9 := by exact_mod_cast huY.trans hY
  -- Step 0: take `s` balanced, `|s'| ≤ u/2`, `s' ≡ s (mod u)`.
  set s' : ℤ := s - u * round ((s : ℝ) / u) with hs'def
  have hs' : |(s' : ℝ)| ≤ u / 2 := by
    have h1 := abs_sub_round ((s : ℝ) / u)
    have e : (s' : ℝ) = u * ((s : ℝ) / u - round ((s : ℝ) / u)) := by
      rw [hs'def]; push_cast; field_simp
    rw [e, abs_mul, abs_of_pos hu0]
    nlinarith
  have hss' : (u : ℤ) ∣ s - s' := ⟨round ((s : ℝ) / u), by rw [hs'def]; ring⟩
  have hs'nd : ¬ (u : ℤ) ∣ s' := by
    intro h; exact hs (by have := dvd_add h hss'; simpa using this)
  -- Step 1: for each invisible `w` choose `t` with `|t| ≤ δu`, `t w ≡ s (mod u)`,
  -- and write `t w = s' + u ℓ`.
  set I := (Wset y).filter (fun w => Invisible δ u s w) with hIdef
  let tw : ℕ → ℤ := fun w => if h : Invisible δ u s w then Classical.choose h else 0
  have htw : ∀ w ∈ I, |((tw w : ℤ) : ℝ)| ≤ δ * u ∧ (u : ℤ) ∣ tw w * w - s := by
    intro w hw
    have hinv := (Finset.mem_filter.1 hw).2
    simp only [tw, dif_pos hinv]
    exact Classical.choose_spec hinv
  let ℓ : ℕ → ℤ := fun w => (tw w * w - s') / u
  have hℓeq : ∀ w ∈ I, tw w * w = s' + u * ℓ w := by
    intro w hw
    have h1 : (u : ℤ) ∣ tw w * w - s' := by
      have := dvd_add (htw w hw).2 hss'
      have e : tw w * ↑w - s + (s - s') = tw w * w - s' := by ring
      rwa [e] at this
    simp only [ℓ]
    rw [Int.mul_ediv_cancel' h1]; ring
  have hWb : ∀ w ∈ I, y ^ 2 < w ∧ w ≤ 2 * y ^ 2 ∧ w.Prime := fun w hw =>
    mem_Wset.1 (Finset.mem_filter.1 hw).1
  -- `|t w| ≤ δ u · 2y² ≤ u y² ≤ y^{11}`
  have htwb : ∀ w ∈ I, |((tw w * w : ℤ) : ℝ)| ≤ δ * u * (2 * (y : ℝ) ^ 2) := by
    intro w hw
    have h1 := (htw w hw).1
    have h2 : (w : ℝ) ≤ 2 * (y : ℝ) ^ 2 := by exact_mod_cast (hWb w hw).2.1
    push_cast
    rw [abs_mul, Nat.abs_cast]
    apply mul_le_mul h1 h2 (by positivity) (by positivity)
  -- Step 2: `|ℓ| ≤ 2δy² + 1/2`, so `ℓ` takes at most `4δy² + 2` values.
  set m : ℕ := ⌊2 * δ * (y : ℝ) ^ 2 + 1 / 2⌋₊ with hmdef
  have hℓm : ∀ w ∈ I, ℓ w ∈ Finset.Icc (-(m : ℤ)) m := by
    intro w hw
    have e := hℓeq w hw
    have h1 : (u : ℝ) * |((ℓ w : ℤ) : ℝ)| ≤ u * (2 * δ * (y : ℝ) ^ 2 + 1 / 2) := by
      have e' : ((u : ℤ) : ℝ) * ((ℓ w : ℤ) : ℝ) = ((tw w * w : ℤ) : ℝ) - (s' : ℝ) := by
        have := congrArg (fun n : ℤ => (n : ℝ)) e
        push_cast at this ⊢
        linarith
      have h2 : |((u : ℤ) : ℝ) * ((ℓ w : ℤ) : ℝ)| ≤ δ * u * (2 * (y : ℝ) ^ 2) + u / 2 := by
        rw [e']
        exact (abs_sub _ _).trans (add_le_add (htwb w hw) hs')
      rw [abs_mul] at h2
      push_cast at h2
      rw [abs_of_pos hu0] at h2
      nlinarith
    have h2 : |((ℓ w : ℤ) : ℝ)| ≤ 2 * δ * (y : ℝ) ^ 2 + 1 / 2 := le_of_mul_le_mul_left h1 hu0
    have h3 : (ℓ w).natAbs ≤ m := by
      apply Nat.le_floor
      rw [Nat.cast_natAbs, Int.cast_abs]
      exact h2
    rw [Finset.mem_Icc]
    constructor <;> omega
  -- Step 3: each value of `ℓ` accounts for at most 5 primes `w`.
  have hfib : ∀ l : ℤ, (I.filter (fun w => ℓ w = l)).card ≤ 5 := by
    intro l
    by_contra hcon
    push Not at hcon
    set T := I.filter (fun w => ℓ w = l) with hT
    obtain ⟨w0, hw0⟩ : T.Nonempty := Finset.card_pos.1 (by omega)
    have hw0I := (Finset.mem_filter.1 hw0).1
    have hw0l := (Finset.mem_filter.1 hw0).2
    set n : ℤ := s' + u * l with hn
    have hn0 : n ≠ 0 := by
      intro h
      apply hs'nd
      exact ⟨-l, by linarith⟩
    -- every `w ∈ T` divides `n`
    have hdvd : ∀ w ∈ T, w ∣ n.natAbs := by
      intro w hw
      have hwI := (Finset.mem_filter.1 hw).1
      have hwl := (Finset.mem_filter.1 hw).2
      have e := hℓeq w hwI
      rw [hwl] at e
      have : (w : ℤ) ∣ n := ⟨tw w, by rw [hn, ← e]; ring⟩
      exact Int.natCast_dvd.1 this
    -- `|n| ≤ y^{11}`
    have hnb : n.natAbs ≤ y ^ 11 := by
      have e := hℓeq w0 hw0I
      rw [hw0l] at e
      have h1 := htwb w0 hw0I
      rw [e] at h1
      have h2 : |(n : ℝ)| ≤ (y : ℝ) ^ 11 := by
        have : δ * u * (2 * (y : ℝ) ^ 2) ≤ (y : ℝ) ^ 11 := by
          have : δ * u * (2 * (y : ℝ) ^ 2) = (2 * δ) * (u * (y : ℝ) ^ 2) := by ring
          rw [this]
          have h3 : u * (y : ℝ) ^ 2 ≤ (y : ℝ) ^ 11 := by
            have : (y : ℝ) ^ 11 = (y : ℝ) ^ 9 * (y : ℝ) ^ 2 := by ring
            rw [this]
            exact mul_le_mul_of_nonneg_right huy9 (by positivity)
          calc 2 * δ * (u * (y : ℝ) ^ 2) ≤ 1 * (u * (y : ℝ) ^ 2) :=
                mul_le_mul_of_nonneg_right hδ1 (by positivity)
            _ ≤ (y : ℝ) ^ 11 := by linarith
        push_cast [hn] at h1 ⊢
        linarith
      have : ((n.natAbs : ℕ) : ℝ) ≤ ((y ^ 11 : ℕ) : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs]; push_cast; exact h2
      exact_mod_cast this
    -- the product of the primes in `T` divides `n`, hence is at most `y^{11}`
    have hprod : ∏ w ∈ T, w ∣ n.natAbs :=
      Finset.prod_primes_dvd _ (fun w hw => (hWb w (Finset.mem_filter.1 hw).1).2.2.prime) hdvd
    have hprodle : ∏ w ∈ T, w ≤ y ^ 11 :=
      (Nat.le_of_dvd (Int.natAbs_pos.2 hn0) hprod).trans hnb
    -- but it exceeds `(y²)^6 = y^{12}`
    have hlow : (y ^ 2 + 1) ^ T.card ≤ ∏ w ∈ T, w :=
      Finset.pow_card_le_prod _ _ _ (fun w hw => (hWb w (Finset.mem_filter.1 hw).1).1)
    have h6 : (y ^ 2 + 1) ^ 6 ≤ (y ^ 2 + 1) ^ T.card :=
      Nat.pow_le_pow_right (by positivity) hcon
    have h12 : y ^ 11 < (y ^ 2 + 1) ^ 6 := by
      calc y ^ 11 < y ^ 12 := Nat.pow_lt_pow_right (by omega) (by norm_num)
        _ = (y ^ 2) ^ 6 := by ring
        _ < (y ^ 2 + 1) ^ 6 := Nat.pow_lt_pow_left (by omega) (by norm_num)
    omega
  -- Step 4: combine.
  have hcard : I.card ≤ 5 * (I.image ℓ).card :=
    Finset.card_le_mul_card_image I 5 (fun b _ => hfib b)
  have himg : (I.image ℓ).card ≤ 2 * m + 1 := by
    have h1 : I.image ℓ ⊆ Finset.Icc (-(m : ℤ)) m := by
      intro l hl
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hl
      exact hℓm w hw
    have h2 := Finset.card_le_card h1
    rw [Int.card_Icc] at h2
    omega
  have hmR : (m : ℝ) ≤ 2 * δ * (y : ℝ) ^ 2 + 1 / 2 := Nat.floor_le (by positivity)
  refine ⟨?_, ?_⟩
  · have : (I.card : ℝ) ≤ 5 * (2 * m + 1) := by exact_mod_cast (hcard.trans (by omega))
    linarith
  · have hW := hL.card_W
    have hc := hL.count
    have e : 5 * (4 * δ * (y : ℝ) ^ 2 + 2) = (y : ℝ) ^ 2 / (20 * Real.log y) + 10 := by
      rw [hδdef, delta]; field_simp; ring
    have e2 : (y : ℝ) ^ 2 / (16 * Real.log y) = ((y : ℝ) ^ 2 / (8 * Real.log y)) / 2 := by
      field_simp; ring
    rw [e]
    linarith

/-- The heart of the separation argument: in a *visible* row `w` (i.e. `‖s w̄/u‖ > δ` with
`s = ζ_u - ζ_u'`), the two phases cannot both be close to an integer:
`‖φ_{wu}(ξ,ζ_u)‖ + ‖φ_{wu}(ξ,ζ_u')‖ > δ` (triangle inequality for `‖·‖` and eq. (5)). -/
lemma visible_phase_sum (hL : Large τ y) {u w : ℕ} (hu : u ∈ Uset y Y) (hw : w ∈ Wset y)
    (ξ z z' : ℕ) (hvis : ¬ Invisible (delta y) u ((z : ℤ) - z') w) :
    delta y < nint (phase τ y u w ξ z) + nint (phase τ y u w ξ z') := by
  by_contra hcon
  push Not at hcon
  apply hvis
  obtain ⟨k, hk, hph⟩ := eq_pf hL hu (Wset_subset_Vset hw) ξ z z'
  have h1 : nint ((k : ℝ) / u) ≤ delta y := by
    rw [← hph]; exact (nint_sub_le _ _).trans hcon
  obtain ⟨n, hn⟩ := exists_int_of_nint_le h1
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (prime_of_mem_Uset hu).pos
  refine ⟨k - n * u, ?_, ?_⟩
  · have e : ((k - n * u : ℤ) : ℝ) = u * ((k : ℝ) / u - n) := by push_cast; field_simp
    rw [e, abs_mul, abs_of_pos hu0, mul_comm]
    exact mul_le_mul_of_nonneg_right hn hu0.le
  · have e : (k - n * u) * (w : ℤ) - ((z : ℤ) - z') = ((w : ℤ) * k - ((z : ℤ) - z')) - u * (n * w) := by
      ring
    rw [e]
    exact dvd_sub hk (dvd_mul_right _ _)

/-- A product of factors in `[0,1]` only grows when factors are dropped. -/
lemma prod_le_prod_subset_of_le_one {s t : Finset ℕ} (hst : s ⊆ t) (f : ℕ → ℝ)
    (h0 : ∀ i ∈ t, 0 ≤ f i) (h1 : ∀ i ∈ t, f i ≤ 1) : ∏ i ∈ t, f i ≤ ∏ i ∈ s, f i :=
  Finset.prod_le_prod_of_subset_of_le_one hst h0 (fun i hi _ => h1 i hi)

/-- The visible rows form at least half of `W` (Lemma 8.2). -/
lemma card_visible (hL : Large τ y) (hY : Y ≤ y ^ 9) {u : ℕ} (hu : u ∈ Uset y Y) {s : ℤ}
    (hs : ¬ (u : ℤ) ∣ s) :
    ((Wset y).card : ℝ) / 2 ≤
      (((Wset y).filter (fun w => ¬ Invisible (delta y) u s w)).card : ℝ) := by
  have h := lem_count hL hY hu hs
  have e := Finset.card_filter_add_card_filter_not
    (s := Wset y) (fun w => Invisible (delta y) u s w)
  have e' : (((Wset y).filter (fun w => Invisible (delta y) u s w)).card : ℝ) +
      (((Wset y).filter (fun w => ¬ Invisible (delta y) u s w)).card : ℝ) = (Wset y).card := by
    exact_mod_cast e
  linarith [h.1, h.2]

/-- `exp(-δ²/2)^{#visible} ≤ ε²`. -/
lemma pow_visible_le (n : ℕ) (hn : ((Wset y).card : ℝ) / 2 ≤ n) :
    exp (-(delta y ^ 2 / 2)) ^ n ≤ eps y ^ 2 := by
  rw [← Real.exp_nat_mul, eps, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  have : 0 ≤ delta y ^ 2 := by positivity
  push_cast
  nlinarith

/-- **Lemma 8.3 (Separation).**  Let `u ∈ U`, `ξ` row labels, and `ζ_u ≢ ζ_u' (mod u)`.
(i) `F_u(ξ,ζ_u) F_u(ξ,ζ_u') ≤ ε²`; in particular at most one label is heavy (`> ε`).
(ii) If `‖φ_{wu}(ξ, ζ_u')‖ ≤ δ/2` for all `w ∈ W`, then `F_u(ξ, ζ_u) ≤ ε`. -/
theorem lem_unique (hL : Large τ y) (hY : Y ≤ y ^ 9) {u : ℕ} (hu : u ∈ Uset y Y) (ξ z z' : ℕ)
    (hzz : ¬ (u : ℤ) ∣ (z : ℤ) - z') :
    Fcol τ y u ξ z * Fcol τ y u ξ z' ≤ eps y ^ 2 ∧
      ((∀ w ∈ Wset y, nint (phase τ y u w ξ z') ≤ delta y / 2) → Fcol τ y u ξ z ≤ eps y) := by
  set s : ℤ := (z : ℤ) - z' with hsdef
  set Vis := (Wset y).filter (fun w => ¬ Invisible (delta y) u s w) with hVis
  have hVisW : Vis ⊆ Wset y := Finset.filter_subset _ _
  have hVisV : Vis ⊆ Vset τ y := hVisW.trans Wset_subset_Vset
  have hcard := card_visible hL hY hu hzz
  -- one cosine factor is at most `exp(-δ²/2)` when its phase exceeds `δ/2`
  have hfac : ∀ x : ℝ, delta y / 2 < nint x → |Real.cos (π * x)| ≤ exp (-(delta y ^ 2 / 2)) := by
    intro x hx
    refine (lem_cos x).trans (Real.exp_le_exp.2 ?_)
    have : 0 ≤ delta y / 2 := by
      have := hL.y_ge
      rw [delta]
      have : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
      positivity
    nlinarith
  set c := fun (ζ : ℕ) (v : ℕ) => |Real.cos (π * phase τ y u v ξ ζ)| with hc
  have hc0 : ∀ ζ v, 0 ≤ c ζ v := fun _ _ => abs_nonneg _
  have hc1 : ∀ ζ v, c ζ v ≤ 1 := fun _ _ => Real.abs_cos_le_one _
  constructor
  · -- (i)
    have e : Fcol τ y u ξ z * Fcol τ y u ξ z' = ∏ v ∈ Vset τ y, (c z v * c z' v) := by
      rw [Fcol, Fcol, ← Finset.prod_mul_distrib]
    rw [e]
    calc ∏ v ∈ Vset τ y, (c z v * c z' v) ≤ ∏ v ∈ Vis, (c z v * c z' v) :=
          prod_le_prod_subset_of_le_one hVisV _ (fun v _ => mul_nonneg (hc0 _ _) (hc0 _ _))
            (fun v _ => mul_le_one₀ (hc1 _ _) (hc0 _ _) (hc1 _ _))
      _ ≤ ∏ v ∈ Vis, exp (-(delta y ^ 2 / 2)) := by
          apply Finset.prod_le_prod (fun v _ => mul_nonneg (hc0 _ _) (hc0 _ _))
          intro w hw
          have hw' := Finset.mem_filter.1 hw
          have hsum := visible_phase_sum hL hu hw'.1 ξ z z' hw'.2
          by_cases h1 : delta y / 2 < nint (phase τ y u w ξ z)
          · calc c z w * c z' w ≤ exp (-(delta y ^ 2 / 2)) * 1 :=
                  mul_le_mul (hfac _ h1) (hc1 _ _) (hc0 _ _) (by positivity)
              _ = _ := mul_one _
          · have h2 : delta y / 2 < nint (phase τ y u w ξ z') := by linarith
            calc c z w * c z' w ≤ 1 * exp (-(delta y ^ 2 / 2)) :=
                  mul_le_mul (hc1 _ _) (hfac _ h2) (hc0 _ _) zero_le_one
              _ = _ := one_mul _
      _ = exp (-(delta y ^ 2 / 2)) ^ Vis.card := Finset.prod_const _
      _ ≤ eps y ^ 2 := pow_visible_le _ hcard
  · -- (ii)
    intro hsmall
    have heps1 : eps y ≤ 1 := by
      rw [eps]; apply Real.exp_le_one_iff.2
      have : 0 ≤ ((Wset y).card : ℝ) * delta y ^ 2 / 8 := by positivity
      linarith
    have heps0 : 0 ≤ eps y := (Real.exp_pos _).le
    calc Fcol τ y u ξ z = ∏ v ∈ Vset τ y, c z v := rfl
      _ ≤ ∏ v ∈ Vis, c z v := prod_le_prod_subset_of_le_one hVisV _ (fun v _ => hc0 _ _)
            (fun v _ => hc1 _ _)
      _ ≤ ∏ v ∈ Vis, exp (-(delta y ^ 2 / 2)) := by
          apply Finset.prod_le_prod (fun v _ => hc0 _ _)
          intro w hw
          have hw' := Finset.mem_filter.1 hw
          have hsum := visible_phase_sum hL hu hw'.1 ξ z z' hw'.2
          have h2 := hsmall w hw'.1
          exact hfac _ (by linarith)
      _ = exp (-(delta y ^ 2 / 2)) ^ Vis.card := Finset.prod_const _
      _ ≤ eps y ^ 2 := pow_visible_le _ hcard
      _ ≤ eps y := by nlinarith

/-- Consequence of Lemma 8.3(i): at most one label of a column is heavy. -/
lemma heavy_unique (hL : Large τ y) (hY : Y ≤ y ^ 9) {u : ℕ} (hu : u ∈ Uset y Y) (ξ z z' : ℕ)
    (hz : eps y < Fcol τ y u ξ z) (hz' : eps y < Fcol τ y u ξ z') : (u : ℤ) ∣ (z : ℤ) - z' := by
  by_contra hcon
  have h := (lem_unique hL hY hu ξ z z' hcon).1
  have heps0 : 0 ≤ eps y := (Real.exp_pos _).le
  have : eps y * eps y < Fcol τ y u ξ z * Fcol τ y u ξ z' :=
    mul_lt_mul'' hz hz' heps0 heps0
  nlinarith

/-- **Lemma 8.4 (No wrap-around).**  Let `u ∈ U`, `ξ` row labels and `ζ_u` a column label.
If `‖φ_{vu}(ξ, ζ_u)‖ ≤ δ_a` for all `v ∈ V`, then there is an integer `M` with `|M| ≤ y^7/4`
and `ξ ≡ M (mod v)` for all `v ∈ V`; in particular `ξ` is coherent. -/
theorem lem_admissible (hL : Large τ y) (hY : Y ≤ y ^ 9) {u : ℕ} (hu : u ∈ Uset y Y) (ξ z : ℕ)
    (h : ∀ v ∈ Vset τ y, nint (phase τ y u v ξ z) ≤ deltaA y) :
    ∃ M : ℤ, (|M| : ℝ) ≤ (y : ℝ) ^ 7 / 4 ∧ ∀ v ∈ Vset τ y, (v : ℤ) ∣ (ξ : ℤ) - M := by
  set J : ℤ := ((crt τ y u ξ z : ℕ) : ℤ) with hJdef
  obtain ⟨hu8, huY, hup⟩ := mem_Uset.1 hu
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hup.pos
  have hy0 : (0 : ℝ) < y := by have := hL.y_ge; exact_mod_cast (by omega : 0 < y)
  -- `J_v`: the balanced representative of `J` modulo `uv`
  let Jv : ℕ → ℤ := fun v => J - round ((J : ℝ) / ((u : ℝ) * v)) * (u * v)
  have hJv_bound : ∀ v ∈ Vset τ y, |((Jv v : ℤ) : ℝ)| ≤ deltaA y * u * v := by
    intro v hv
    have hv0 : (0 : ℝ) < v := by exact_mod_cast (prime_of_mem_Vset hv).pos
    have h1 := h v hv
    unfold nint phase at h1
    have e : ((Jv v : ℤ) : ℝ) = ((u : ℝ) * v) *
        ((J : ℝ) / ((u : ℝ) * v) - round ((J : ℝ) / ((u : ℝ) * v))) := by
      simp only [Jv]; push_cast; field_simp
    rw [e, abs_mul, abs_of_pos (by positivity)]
    have hJ : ((crt τ y u ξ z : ℕ) : ℝ) = (J : ℝ) := by rw [hJdef]; push_cast; rfl
    rw [hJ] at h1
    have : (0 : ℝ) < u * v := by positivity
    calc (u : ℝ) * v * |(J : ℝ) / ((u : ℝ) * v) - round ((J : ℝ) / ((u : ℝ) * v))|
        ≤ u * v * deltaA y := mul_le_mul_of_nonneg_left h1 this.le
      _ = deltaA y * u * v := by ring
  have hJv_u : ∀ v ∈ Vset τ y, |((Jv v : ℤ) : ℝ)| ≤ u / 4 := by
    intro v hv
    have hvb := (le_of_mem_Vset hL hv).2
    have hvR : (v : ℝ) ≤ 2 * (y : ℝ) ^ 2 := by exact_mod_cast hvb
    refine (hJv_bound v hv).trans ?_
    rw [deltaA]
    have : 1 / (8 * (y : ℝ) ^ 2) * u * v = u * (v / (8 * (y : ℝ) ^ 2)) := by ring
    rw [this]
    have : v / (8 * (y : ℝ) ^ 2) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    nlinarith
  -- all `J_v` are `≡ J (mod u)`, differ by less than `u`, hence are equal
  have hJv_mod : ∀ v, (u : ℤ) ∣ J - Jv v := by
    intro v; exact ⟨round ((J : ℝ) / ((u : ℝ) * v)) * v, by simp only [Jv]; ring⟩
  have h2 : (2 : ℕ) ∈ Vset τ y := two_mem_Vset
  have hall : ∀ v ∈ Vset τ y, Jv v = Jv 2 := by
    intro v hv
    have hd : (u : ℤ) ∣ Jv v - Jv 2 := by
      have := dvd_sub (hJv_mod 2) (hJv_mod v)
      have e : J - Jv 2 - (J - Jv v) = Jv v - Jv 2 := by ring
      rwa [e] at this
    have hlt : |Jv v - Jv 2| < (u : ℤ) := by
      have h1 := hJv_u v hv
      have h2' := hJv_u 2 h2
      have : |((Jv v - Jv 2 : ℤ) : ℝ)| < (u : ℝ) := by
        push_cast
        calc |((Jv v : ℤ) : ℝ) - ((Jv 2 : ℤ) : ℝ)| ≤ |((Jv v : ℤ) : ℝ)| + |((Jv 2 : ℤ) : ℝ)| :=
              abs_sub _ _
          _ ≤ u / 4 + u / 4 := add_le_add h1 h2'
          _ < u := by linarith
      exact_mod_cast this
    have := Int.eq_zero_of_abs_lt_dvd hd hlt
    linarith
  refine ⟨Jv 2, ?_, ?_⟩
  · -- `|M| = |J_2| ≤ 2 δ_a u ≤ Y/(4y²) ≤ y^7/4`
    have h1 := hJv_bound 2 h2
    have huy : (u : ℝ) ≤ (y : ℝ) ^ 9 := by exact_mod_cast huY.trans hY
    push_cast at h1 ⊢
    calc |((Jv 2 : ℤ) : ℝ)| ≤ deltaA y * u * 2 := h1
      _ = u / (4 * (y : ℝ) ^ 2) := by rw [deltaA]; field_simp; ring
      _ ≤ (y : ℝ) ^ 9 / (4 * (y : ℝ) ^ 2) := by gcongr
      _ = (y : ℝ) ^ 7 / 4 := by field_simp
  · -- `M = J_v ≡ J ≡ ξ (mod v)`
    intro v hv
    rw [← hall v hv]
    have hvP : (v : ℤ) ∣ (PV τ y : ℤ) := by
      exact_mod_cast Finset.dvd_prod_of_mem (fun v : ℕ => v) hv
    have hJξ : (v : ℤ) ∣ (ξ : ℤ) - J := hvP.trans (crt_modEq_xi hL hu ξ z).dvd
    have : (ξ : ℤ) - Jv v = ((ξ : ℤ) - J) + round ((J : ℝ) / ((u : ℝ) * v)) * u * v := by
      simp only [Jv]; ring
    rw [this]
    exact dvd_add hJξ (dvd_mul_left _ _)

/-- Lemma 8.4, last sentence: under its hypothesis the row labels `ξ` are coherent. -/
lemma coherent_of_admissible (hL : Large τ y) (hY : Y ≤ y ^ 9) {u : ℕ} (hu : u ∈ Uset y Y)
    (ξ z : ℕ) (h : ∀ v ∈ Vset τ y, nint (phase τ y u v ξ z) ≤ deltaA y) :
    Coherent τ y ξ := by
  obtain ⟨M, hM, hMv⟩ := lem_admissible hL hY hu ξ z h
  refine ⟨M, ?_, hMv⟩
  have : ((|M| : ℤ) : ℝ) ≤ ((y ^ 7 : ℕ) : ℤ) := by
    push_cast
    have : (0 : ℝ) ≤ (y : ℝ) ^ 7 := by positivity
    linarith
  exact_mod_cast this

end Erdos306

end

section
-- Source: https://arxiv.org/src/2609.32140v1/anc/lean/Erdos306/Minor.lean
/-
§9 of the paper: Cases II and III, the minor arcs (Proposition 9.1).
-/

namespace Erdos306

open Real Finset

open scoped Classical

variable {τ : ℚ} {y Y : ℕ}

/-! ### Generic helpers -/

/-- A single factor bounds a product of factors in `[0,1]`. -/
lemma prod_le_single_of_le_one {s : Finset ℕ} {f : ℕ → ℝ} {a : ℕ} (ha : a ∈ s)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ f a := by
  have := Finset.prod_le_prod_of_subset_of_le_one (Finset.singleton_subset_iff.2 ha) h0
    (fun i hi _ => h1 i hi)
  simpa using this

/-- `∏ (a_u + R_u) - ∏ a_u ≤ (1 + r)^n - 1` for `0 ≤ a_u ≤ 1`, `0 ≤ R_u ≤ r` (this is the
expansion over the set `T` of mismatched columns in the proof of Prop. 9.1, case II). -/
lemma prod_add_sub_prod_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (a R : ι → ℝ) (r : ℝ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) (hR0 : ∀ i ∈ s, 0 ≤ R i)
    (hR : ∀ i ∈ s, R i ≤ r) :
    ∏ i ∈ s, (a i + R i) - ∏ i ∈ s, a i ≤ (1 + r) ^ s.card - 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
    have ha0' := fun i hi => ha0 i (Finset.mem_insert_of_mem hi)
    have ha1' := fun i hi => ha1 i (Finset.mem_insert_of_mem hi)
    have hR0' := fun i hi => hR0 i (Finset.mem_insert_of_mem hi)
    have hR' := fun i hi => hR i (Finset.mem_insert_of_mem hi)
    have ih' := ih ha0' ha1' hR0' hR'
    have hj0 := ha0 j (Finset.mem_insert_self j s)
    have hj1 := ha1 j (Finset.mem_insert_self j s)
    have hRj0 := hR0 j (Finset.mem_insert_self j s)
    have hRj := hR j (Finset.mem_insert_self j s)
    set P := ∏ i ∈ s, (a i + R i)
    set Q := ∏ i ∈ s, a i
    have hQ0 : 0 ≤ Q := Finset.prod_nonneg ha0'
    have hQP : Q ≤ P := Finset.prod_le_prod ha0' (fun i hi => by linarith [hR0' i hi])
    have hr0 : 0 ≤ r := hRj0.trans hRj
    have hP : P ≤ (1 + r) ^ s.card := by
      calc P ≤ ∏ i ∈ s, (1 + r) := Finset.prod_le_prod
            (fun i hi => by linarith [ha0' i hi, hR0' i hi])
            (fun i hi => by linarith [ha1' i hi, hR' i hi])
        _ = (1 + r) ^ s.card := Finset.prod_const _
    -- `(a+R)P - aQ = a(P - Q) + R P`
    have e : (a j + R j) * P - a j * Q = a j * (P - Q) + R j * P := by ring
    rw [e, pow_succ]
    have h1 : a j * (P - Q) ≤ (1 + r) ^ s.card - 1 := by
      calc a j * (P - Q) ≤ 1 * (P - Q) := mul_le_mul_of_nonneg_right hj1 (by linarith)
        _ ≤ _ := by linarith
    have h2 : R j * P ≤ r * (1 + r) ^ s.card :=
      mul_le_mul hRj hP (hQ0.trans hQP) hr0
    nlinarith

/-- `(1 + z)^n - 1 ≤ n z e^{n z}` for `z ≥ 0`. -/
lemma one_add_pow_sub_one_le (n : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    (1 + z) ^ n - 1 ≤ n * z * exp (n * z) := by
  have h1 : (1 + z) ^ n ≤ exp (n * z) := by
    rw [Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by linarith)
    linarith [Real.add_one_le_exp z]
  have h2 : exp (n * z) - 1 ≤ n * z * exp (n * z) := by
    have := Real.add_one_le_exp (-(n * z))
    have hpos := Real.exp_pos (n * z)
    have e : exp (-(n * z)) * exp (n * z) = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  linarith

/-- For `u ∈ U`, a column label is an element of `range u`. -/
lemma toNat_emod_lt {h : ℤ} {m : ℕ} (hm : 0 < m) : (h % (m : ℤ)).toNat < m := by
  have h1 : 0 ≤ h % (m : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hm.ne')
  have h2 : h % (m : ℤ) < m := Int.emod_lt_of_pos _ (by exact_mod_cast hm)
  omega

/-- `m ∣ h - (h mod m)`. -/
lemma dvd_sub_toNat_emod (h : ℤ) {m : ℕ} (hm : 0 < m) : (m : ℤ) ∣ h - ((h % (m : ℤ)).toNat : ℤ) := by
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.ne'))]
  exact Int.dvd_self_sub_emod

/-- Column bound: with at most one heavy label and every label of weight at most `c`,
`S_u(ξ) ≤ c + u ε`. -/
lemma Scol_le_of_heavy (hL : Large τ y) (hT : Tuned τ y Y) {u : ℕ} (hu : u ∈ Uset y Y) (ξ : ℕ)
    {c : ℝ} (hc : ∀ z, Fcol τ y u ξ z ≤ c) : Scol τ y u ξ ≤ c + u * eps y := by
  have heps0 : 0 ≤ eps y := (Real.exp_pos _).le
  have hc0 : 0 ≤ c := (Fcol_nonneg u ξ 0).trans (hc 0)
  unfold Scol
  by_cases hheavy : ∃ z0 ∈ range u, eps y < Fcol τ y u ξ z0
  · obtain ⟨z0, hz0, hz0h⟩ := hheavy
    rw [← Finset.add_sum_erase _ _ hz0]
    have hrest : ∑ z ∈ (range u).erase z0, Fcol τ y u ξ z ≤ ((range u).erase z0).card * eps y := by
      have : ∀ z ∈ (range u).erase z0, Fcol τ y u ξ z ≤ eps y := by
        intro z hz
        by_contra hcon
        push Not at hcon
        have hdvd := heavy_unique hL hT.hi hu ξ z z0 hcon hz0h
        have hz := Finset.mem_erase.1 hz
        have h1 := Finset.mem_range.1 hz.2
        have h2 := Finset.mem_range.1 hz0
        have : (z : ℤ) - z0 = 0 := by
          apply Int.eq_zero_of_abs_lt_dvd hdvd
          rw [abs_lt]; constructor <;> omega
        omega
      calc _ ≤ ∑ z ∈ (range u).erase z0, eps y := Finset.sum_le_sum this
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (((range u).erase z0).card : ℝ) ≤ u := by
      rw [Finset.card_erase_of_mem hz0, Finset.card_range]
      exact_mod_cast Nat.sub_le u 1
    have := mul_le_mul_of_nonneg_right hcard heps0
    linarith [hc z0]
  · push Not at hheavy
    calc ∑ z ∈ range u, Fcol τ y u ξ z ≤ ∑ z ∈ range u, eps y := Finset.sum_le_sum hheavy
      _ = u * eps y := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ c + u * eps y := by linarith

/-- Proposition 9.1, case III, one column: for incoherent `ξ`, `S_u(ξ) ≤ e^{-δ_a²}`.
(By Lemma 8.4 every label has an entry with phase `> δ_a`, so weight `≤ e^{-2δ_a²}`; by
Lemma 8.3(i) at most one label is heavy, the others have weight `≤ ε`.) -/
theorem caseIII_column (hL : Large τ y) (hT : Tuned τ y Y) {u : ℕ} (hu : u ∈ Uset y Y) (ξ : ℕ)
    (hξ : ¬ Coherent τ y ξ) : Scol τ y u ξ ≤ exp (-(deltaA y ^ 2)) := by
  -- every label has an entry with phase `> δ_a` (Lemma 8.4), so weight `≤ e^{-2δ_a²}`
  have hc : ∀ z, Fcol τ y u ξ z ≤ exp (-2 * deltaA y ^ 2) := by
    intro z
    have : ¬ ∀ v ∈ Vset τ y, nint (phase τ y u v ξ z) ≤ deltaA y :=
      fun h => hξ (coherent_of_admissible hL hT.hi hu ξ z h)
    push Not at this
    obtain ⟨v, hv, hvd⟩ := this
    have hδa : 0 ≤ deltaA y := by rw [deltaA]; positivity
    calc Fcol τ y u ξ z ≤ |Real.cos (π * phase τ y u v ξ z)| :=
          prod_le_single_of_le_one hv (fun _ _ => abs_nonneg _) (fun _ _ => Real.abs_cos_le_one _)
      _ ≤ exp (-2 * nint (phase τ y u v ξ z) ^ 2) := lem_cos _
      _ ≤ exp (-2 * deltaA y ^ 2) := by
          apply Real.exp_le_exp.2
          nlinarith
  have h1 := Scol_le_of_heavy hL hT hu ξ hc
  have hu9 : (u : ℝ) ≤ (y : ℝ) ^ 9 := by
    exact_mod_cast (bounds_of_mem_Uset hu).2.trans hT.hi
  have heps0 : 0 ≤ eps y := (Real.exp_pos _).le
  have := mul_le_mul_of_nonneg_right hu9 heps0
  linarith [hL.colIII]

/-- Proposition 9.1, case III: `∑_{ξ incoherent} ∏_u S_u(ξ) ≤ 2b·16^{y²} e^{-δ_a²|U|} ≤ 1/4`. -/
theorem caseIII_total (hL : Large τ y) (hT : Tuned τ y Y) :
    ∑ ξ ∈ (range (PV τ y)).filter (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ)), ∏ u ∈ Uset y Y, Scol τ y u ξ
      ≤ 1 / 4 := by
  set X := exp (-(deltaA y ^ 2)) ^ (Uset y Y).card with hX
  have h1 : ∀ ξ ∈ (range (PV τ y)).filter (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ)),
      ∏ u ∈ Uset y Y, Scol τ y u ξ ≤ X := by
    intro ξ hξ
    have hξ' := (Finset.mem_filter.1 hξ).2
    calc ∏ u ∈ Uset y Y, Scol τ y u ξ ≤ ∏ u ∈ Uset y Y, exp (-(deltaA y ^ 2)) :=
          Finset.prod_le_prod (fun u _ => Scol_nonneg u ξ)
            (fun u hu => caseIII_column hL hT hu ξ hξ')
      _ = X := Finset.prod_const _
  have hX0 : 0 ≤ X := by positivity
  have h2 : ∑ ξ ∈ (range (PV τ y)).filter (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ)),
      ∏ u ∈ Uset y Y, Scol τ y u ξ ≤ (PV τ y : ℝ) * X := by
    calc _ ≤ ∑ ξ ∈ (range (PV τ y)).filter (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ)), X :=
          Finset.sum_le_sum h1
      _ = (((range (PV τ y)).filter (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ))).card : ℝ) * X := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (PV τ y : ℝ) * X := by
          apply mul_le_mul_of_nonneg_right _ hX0
          have := Finset.card_filter_le (range (PV τ y)) (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ))
          rw [Finset.card_range] at this
          exact_mod_cast this
  -- `e^{-δ_a² |U|} ≤ exp(-τ y⁴/(64 H_V))` since `|U| ≥ τ y^8/H_V`
  have hHV := HV_pos hL
  have hy0 : (0 : ℝ) < y := by have := hL.y_ge; exact_mod_cast (by omega : 0 < y)
  have h3 : X ≤ exp (-((τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y))) := by
    rw [hX, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hU := hT.card_U
    have e1 : deltaA y ^ 2 = 1 / (64 * (y : ℝ) ^ 4) := by rw [deltaA]; field_simp; ring
    rw [e1]
    have e2 : (τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y) =
        ((τ : ℝ) * (y : ℝ) ^ 8 / HV τ y) * (1 / (64 * (y : ℝ) ^ 4)) := by
      field_simp
    rw [e2]
    have : 0 ≤ 1 / (64 * (y : ℝ) ^ 4) := by positivity
    nlinarith
  have h4 := prod_V_le (τ := τ) (y := y)
  have h5 := hL.caseIII
  have hPV : (PV τ y : ℝ) = ((∏ v ∈ Vset τ y, v : ℕ) : ℝ) := rfl
  calc _ ≤ (PV τ y : ℝ) * X := h2
    _ ≤ (2 * (τ.den : ℝ) * 16 ^ (y ^ 2)) * exp (-((τ : ℝ) * (y : ℝ) ^ 4 / (64 * HV τ y))) := by
        apply mul_le_mul (hPV ▸ h4) h3 hX0 (by positivity)
    _ ≤ 1 / 4 := h5

/-- Proposition 9.1, case II, for one coherent `ξ ≡ M`: the frequencies with some mismatched
column contribute `∏_u S_u(ξ) - ∏_u F_u(ξ, M mod u) ≤ |U| Y ε e^{|U| Y ε}`. -/
theorem caseII_single (hL : Large τ y) (hT : Tuned τ y Y) {M : ℤ} (hM : |M| ≤ (y : ℤ) ^ 7) :
    ∏ u ∈ Uset y Y, Scol τ y u (M % (PV τ y : ℤ)).toNat
        - ∏ u ∈ Uset y Y, Fcol τ y u (M % (PV τ y : ℤ)).toNat (M % (u : ℤ)).toNat
      ≤ (Uset y Y).card * Y * eps y * exp ((Uset y Y).card * Y * eps y) := by
  set ξ := (M % (PV τ y : ℤ)).toNat with hξ
  set m : ℕ → ℕ := fun u => (M % (u : ℤ)).toNat with hm
  have heps0 : 0 ≤ eps y := (Real.exp_pos _).le
  have hy3 := hL.y_ge
  have hyR : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hPV0 : 0 < PV τ y := by
    have := PV_gt_y8 hL; omega
  -- the matching label `M mod u` has small phases in the test rows, so every mismatched label
  -- has weight `≤ ε` (Lemma 8.3(ii))
  have hmis : ∀ u ∈ Uset y Y, ∀ z ∈ (range u).erase (m u), Fcol τ y u ξ z ≤ eps y := by
    intro u hu z hz
    have hu0 : 0 < u := (prime_of_mem_Uset hu).pos
    have hz' := Finset.mem_erase.1 hz
    apply (lem_unique hL hT.hi hu ξ z (m u) ?_).2 ?_
    · intro hd
      have h1 := Finset.mem_range.1 hz'.2
      have h2 : m u < u := toNat_emod_lt hu0
      have : (z : ℤ) - (m u : ℕ) = 0 := by
        apply Int.eq_zero_of_abs_lt_dvd hd
        rw [abs_lt]; constructor <;> omega
      exact hz'.1 (by omega)
    · intro w hw
      have hwV := Wset_subset_Vset (τ := τ) hw
      have hwP : (w : ℤ) ∣ (PV τ y : ℤ) := by
        exact_mod_cast Finset.dvd_prod_of_mem (fun v : ℕ => v) hwV
      obtain ⟨n, hn⟩ := phase_congr hL hu hwV ξ (m u) M
        (hwP.trans (dvd_sub_toNat_emod M hPV0)) (dvd_sub_toNat_emod M hu0)
      rw [hn, nint_add_int]
      obtain ⟨hw1, -, -⟩ := mem_Wset.1 hw
      obtain ⟨hu1, -, -⟩ := mem_Uset.1 hu
      have hw1' : (y : ℝ) ^ 2 < w := by exact_mod_cast hw1
      have hu1' : (y : ℝ) ^ 8 < u := by exact_mod_cast hu1
      have hM' : |(M : ℝ)| ≤ (y : ℝ) ^ 7 := by
        have : ((|M| : ℤ) : ℝ) ≤ (((y : ℤ) ^ 7 : ℤ) : ℝ) := by exact_mod_cast hM
        push_cast at this; exact this
      have huw : (y : ℝ) ^ 10 < (u : ℝ) * w := by
        have : (y : ℝ) ^ 10 = (y : ℝ) ^ 8 * (y : ℝ) ^ 2 := by ring
        rw [this]
        exact mul_lt_mul'' hu1' hw1' (by positivity) (by positivity)
      calc nint ((M : ℝ) / ((u : ℝ) * w)) ≤ |(M : ℝ) / ((u : ℝ) * w)| := nint_le_abs _
        _ = |(M : ℝ)| / ((u : ℝ) * w) := by
            rw [abs_div, abs_of_pos (a := (u : ℝ) * w) (lt_trans (by positivity) huw)]
        _ ≤ (y : ℝ) ^ 7 / (y : ℝ) ^ 10 := by
            exact div_le_div₀ (by positivity) hM' (by positivity) huw.le
        _ = 1 / (y : ℝ) ^ 3 := by field_simp
        _ ≤ delta y / 2 := hL.phase
  -- `S_u = F_u(ξ, M mod u) + R_u` with `R_u ≤ Y ε`
  set R : ℕ → ℝ := fun u => ∑ z ∈ (range u).erase (m u), Fcol τ y u ξ z with hR
  have hS : ∀ u ∈ Uset y Y, Scol τ y u ξ = Fcol τ y u ξ (m u) + R u := by
    intro u hu
    unfold Scol
    rw [hR, Finset.add_sum_erase _ _ (Finset.mem_range.2 (toNat_emod_lt (prime_of_mem_Uset hu).pos))]
  have hRb : ∀ u ∈ Uset y Y, R u ≤ Y * eps y := by
    intro u hu
    calc R u ≤ ∑ z ∈ (range u).erase (m u), eps y := Finset.sum_le_sum (hmis u hu)
      _ = (((range u).erase (m u)).card : ℝ) * eps y := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Y * eps y := by
          apply mul_le_mul_of_nonneg_right _ heps0
          have h1 := Finset.card_erase_le (s := range u) (a := m u)
          rw [Finset.card_range] at h1
          have h2 := (bounds_of_mem_Uset hu).2
          exact_mod_cast h1.trans h2
  have hR0 : ∀ u ∈ Uset y Y, 0 ≤ R u := fun u _ => Finset.sum_nonneg (fun _ _ => Fcol_nonneg _ _ _)
  rw [Finset.prod_congr rfl hS]
  have := prod_add_sub_prod_le (Uset y Y) (fun u => Fcol τ y u ξ (m u)) R (Y * eps y)
    (fun u _ => Fcol_nonneg _ _ _) (fun u _ => Fcol_le_one _ _ _) hR0 hRb
  refine this.trans ?_
  have h := one_add_pow_sub_one_le (Uset y Y).card (z := Y * eps y) (by positivity)
  calc _ ≤ _ := h
    _ = _ := by ring_nf


/-- Proposition 9.1, case II: summing over the `2y^7+1 ≤ 3y^7` values of `M` gives `≤ 1/4`. -/
theorem caseII_total (hL : Large τ y) (hT : Tuned τ y Y) :
    ∑ M ∈ Finset.Icc (-(y : ℤ) ^ 7) ((y : ℤ) ^ 7),
      (∏ u ∈ Uset y Y, Scol τ y u (M % (PV τ y : ℤ)).toNat
        - ∏ u ∈ Uset y Y, Fcol τ y u (M % (PV τ y : ℤ)).toNat (M % (u : ℤ)).toNat) ≤ 1 / 4 := by
  set B := ((Uset y Y).card : ℝ) * Y * eps y * exp ((Uset y Y).card * Y * eps y) with hB
  have heps0 : 0 ≤ eps y := (Real.exp_pos _).le
  have hy3 := hL.y_ge
  have hyR : (1 : ℝ) ≤ y := by exact_mod_cast (by omega : 1 ≤ y)
  have hYR : (Y : ℝ) ≤ (y : ℝ) ^ 9 := by exact_mod_cast hT.hi
  have hUR : ((Uset y Y).card : ℝ) ≤ (y : ℝ) ^ 9 := by
    have : (Uset y Y).card ≤ Y := by
      calc (Uset y Y).card ≤ (Finset.Ioc (y ^ 8) Y).card := Finset.card_filter_le _ _
        _ = Y - y ^ 8 := Nat.card_Ioc _ _
        _ ≤ Y := Nat.sub_le _ _
    exact le_trans (by exact_mod_cast this) hYR
  have hUY : ((Uset y Y).card : ℝ) * Y * eps y ≤ (y : ℝ) ^ 18 * eps y := by
    have : ((Uset y Y).card : ℝ) * Y ≤ (y : ℝ) ^ 9 * (y : ℝ) ^ 9 :=
      mul_le_mul hUR hYR (by positivity) (by positivity)
    have e : (y : ℝ) ^ 18 = (y : ℝ) ^ 9 * (y : ℝ) ^ 9 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right this heps0
  have hB' : B ≤ (y : ℝ) ^ 18 * eps y * exp ((y : ℝ) ^ 18 * eps y) := by
    rw [hB]
    apply mul_le_mul hUY (Real.exp_le_exp.2 hUY) (by positivity) (by positivity)
  have hcard : ((Finset.Icc (-(y : ℤ) ^ 7) ((y : ℤ) ^ 7)).card : ℝ) ≤ 3 * (y : ℝ) ^ 7 := by
    rw [Int.card_Icc]
    have h7 : (1 : ℤ) ≤ (y : ℤ) ^ 7 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ y))
    have : ((y : ℤ) ^ 7 + 1 - -(y : ℤ) ^ 7).toNat ≤ 3 * y ^ 7 := by
      have : ((y : ℤ) ^ 7 + 1 - -(y : ℤ) ^ 7) ≤ 3 * (y : ℤ) ^ 7 := by linarith
      have h' : (((3 * y ^ 7 : ℕ)) : ℤ) = 3 * (y : ℤ) ^ 7 := by push_cast; ring
      omega
    exact_mod_cast this
  calc _ ≤ ∑ M ∈ Finset.Icc (-(y : ℤ) ^ 7) ((y : ℤ) ^ 7), B := by
        apply Finset.sum_le_sum
        intro M hM
        have hM' : |M| ≤ (y : ℤ) ^ 7 := abs_le.2 (Finset.mem_Icc.1 hM)
        exact caseII_single hL hT hM'
    _ = ((Finset.Icc (-(y : ℤ) ^ 7) ((y : ℤ) ^ 7)).card : ℝ) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 * (y : ℝ) ^ 7) * ((y : ℝ) ^ 18 * eps y * exp ((y : ℝ) ^ 18 * eps y)) :=
        mul_le_mul hcard hB' (by positivity) (by positivity)
    _ = 3 * (y : ℝ) ^ 25 * eps y * exp ((y : ℝ) ^ 18 * eps y) := by ring
    _ ≤ 1 / 4 := hL.caseII


/-- Passing from frequencies to labels (via eq. (4) and the injectivity of the label map):
the case III frequencies contribute at most `∑_{ξ incoherent} ∏_u S_u(ξ)`, and the case II
frequencies at most `∑_M (∏_u S_u(M) - ∏_u F_u(M, M mod u))`. -/
theorem minor_le_labels (hL : Large τ y) :
    ∑ h ∈ (freq (Lnum τ y Y)).filter (fun h => CaseII τ y Y h ∨ CaseIII τ y h),
        ‖phi (Aset τ y Y) h‖
      ≤ ∑ ξ ∈ (range (PV τ y)).filter (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ)), ∏ u ∈ Uset y Y, Scol τ y u ξ
        + ∑ M ∈ Finset.Icc (-(y : ℤ) ^ 7) ((y : ℤ) ^ 7),
          (∏ u ∈ Uset y Y, Scol τ y u (M % (PV τ y : ℤ)).toNat
            - ∏ u ∈ Uset y Y, Fcol τ y u (M % (PV τ y : ℤ)).toNat (M % (u : ℤ)).toNat) := by
  set L := Lnum τ y Y with hLdef
  set P := PV τ y with hPdef
  have hP0 : 0 < P := by have := PV_gt_y8 hL; omega
  have hP0' : (P : ℤ) ≠ 0 := by exact_mod_cast hP0.ne'
  -- the label map `h ↦ (ξ, ζ)` and the column-product `G(ξ, ζ) = ∏_u F_u(ξ, ζ_u)`
  let col : ℤ → (Uset y Y → ℕ) := fun h u => (h % ((u : ℕ) : ℤ)).toNat
  let lab : ℤ → ℕ × (Uset y Y → ℕ) := fun h => ((h % (P : ℤ)).toNat, col h)
  let G : ℕ × (Uset y Y → ℕ) → ℝ := fun x => ∏ u : Uset y Y, Fcol τ y u x.1 (x.2 u)
  have hG0 : ∀ x, 0 ≤ G x := fun x => Finset.prod_nonneg (fun _ _ => Fcol_nonneg _ _ _)
  have hphi : ∀ h, ‖phi (Aset τ y Y) h‖ = G (lab h) := by
    intro h
    rw [norm_phi_eq_prod_Fcol hL]
    exact (Finset.prod_coe_sort (Uset y Y)
      (fun u => Fcol τ y u (h % (P : ℤ)).toNat (h % (u : ℤ)).toNat)).symm
  have hu0 : ∀ u : Uset y Y, 0 < (u : ℕ) := fun u => (prime_of_mem_Uset u.2).pos
  have hcol_mem : ∀ h, col h ∈ Fintype.piFinset (fun u : Uset y Y => range (u : ℕ)) := by
    intro h
    rw [Fintype.mem_piFinset]
    intro u
    exact Finset.mem_range.2 (toNat_emod_lt (hu0 u))
  -- equal column labels give divisibility by each `u`
  have hcol_dvd : ∀ h h', col h = col h' → ∀ u ∈ Uset y Y, (u : ℤ) ∣ h - h' := by
    intro h h' he u hu
    have := congrFun he ⟨u, hu⟩
    simp only [col] at this
    have h1 := Int.toNat_of_nonneg (Int.emod_nonneg h (b := (u : ℤ))
      (by exact_mod_cast (prime_of_mem_Uset hu).ne_zero))
    have h2 := Int.toNat_of_nonneg (Int.emod_nonneg h' (b := (u : ℤ))
      (by exact_mod_cast (prime_of_mem_Uset hu).ne_zero))
    have h3 : h % (u : ℤ) = h' % (u : ℤ) := by rw [← h1, ← h2, this]
    exact Int.ModEq.dvd h3.symm
  -- equal row labels give divisibility by `P_V`
  have hrow_dvd : ∀ h h', (h % (P : ℤ)).toNat = (h' % (P : ℤ)).toNat → (P : ℤ) ∣ h - h' := by
    intro h h' he
    have h1 := Int.toNat_of_nonneg (Int.emod_nonneg h hP0')
    have h2 := Int.toNat_of_nonneg (Int.emod_nonneg h' hP0')
    have h3 : h % (P : ℤ) = h' % (P : ℤ) := by rw [← h1, ← h2, he]
    exact Int.ModEq.dvd h3.symm
  -- Step 0: split cases II and III
  have hsplit : ∑ h ∈ (freq L).filter (fun h => CaseII τ y Y h ∨ CaseIII τ y h),
        ‖phi (Aset τ y Y) h‖ ≤
      ∑ h ∈ (freq L).filter (fun h => CaseIII τ y h), ‖phi (Aset τ y Y) h‖ +
      ∑ h ∈ (freq L).filter (fun h => CaseII τ y Y h), ‖phi (Aset τ y Y) h‖ := by
    rw [Finset.filter_or]
    have e := Finset.sum_union_inter (s₁ := (freq L).filter (fun h => CaseII τ y Y h))
      (s₂ := (freq L).filter (fun h => CaseIII τ y h)) (f := fun h => ‖phi (Aset τ y Y) h‖)
    have : 0 ≤ ∑ h ∈ (freq L).filter (fun h => CaseII τ y Y h) ∩
        (freq L).filter (fun h => CaseIII τ y h), ‖phi (Aset τ y Y) h‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    linarith
  -- Step 1: case III, via the injective label map and eq. (4)
  have h3 : ∑ h ∈ (freq L).filter (fun h => CaseIII τ y h), ‖phi (Aset τ y Y) h‖ ≤
      ∑ ξ ∈ (range P).filter (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ)),
        ∏ u ∈ Uset y Y, Scol τ y u ξ := by
    set s := (freq L).filter (fun h => CaseIII τ y h)
    have hinj : Set.InjOn lab s := by
      intro h hh h' hh' he
      have hh := (Finset.mem_filter.1 hh).1
      have hh' := (Finset.mem_filter.1 hh').1
      have e1 := congrArg Prod.fst he
      have e2 := congrArg Prod.snd he
      exact label_inj hh hh' (hrow_dvd h h' e1) (hcol_dvd h h' e2)
    set T := (range P).filter (fun ξ : ℕ => ¬ Coherent τ y (ξ : ℤ)) ×ˢ
      Fintype.piFinset (fun u : Uset y Y => range (u : ℕ))
    have himg : s.image lab ⊆ T := by
      intro x hx
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hx
      have hIII := (Finset.mem_filter.1 hh).2
      refine Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_range.2 (toNat_emod_lt hP0), ?_⟩,
        hcol_mem h⟩
      -- `h ≡ ξ (mod P_V)`, so coherence of `ξ` would give coherence of `h`
      rintro ⟨M, hM, hMv⟩
      apply hIII
      refine ⟨M, hM, fun v hv => ?_⟩
      have hvP : (v : ℤ) ∣ (P : ℤ) := by
        exact_mod_cast Finset.dvd_prod_of_mem (fun v : ℕ => v) hv
      have := dvd_add (hvP.trans (dvd_sub_toNat_emod h hP0)) (hMv v hv)
      simp only [lab] at this
      have e : h - (((h % (P : ℤ)).toNat : ℕ) : ℤ) + ((((h % (P : ℤ)).toNat : ℕ) : ℤ) - M) =
        h - M := by ring
      rwa [e] at this
    calc ∑ h ∈ s, ‖phi (Aset τ y Y) h‖ = ∑ h ∈ s, G (lab h) := Finset.sum_congr rfl (fun h _ => hphi h)
      _ = ∑ x ∈ s.image lab, G x := (Finset.sum_image hinj).symm
      _ ≤ ∑ x ∈ T, G x := Finset.sum_le_sum_of_subset_of_nonneg himg (fun x _ _ => hG0 x)
      _ = _ := by
          rw [Finset.sum_product]
          refine Finset.sum_congr rfl (fun ξ _ => ?_)
          exact eq_factor ξ
  -- Step 2: case II.  First a union bound over the (unique) `M`.
  set K := (y : ℤ) ^ 7
  let Q : ℤ → ℤ → Prop := fun M h =>
    (∀ v ∈ Vset τ y, (v : ℤ) ∣ h - M) ∧ ∃ u ∈ Uset y Y, ¬ (u : ℤ) ∣ h - M
  have h2a : ∑ h ∈ (freq L).filter (fun h => CaseII τ y Y h), ‖phi (Aset τ y Y) h‖ ≤
      ∑ M ∈ Finset.Icc (-K) K, ∑ h ∈ (freq L).filter (Q M), ‖phi (Aset τ y Y) h‖ := by
    calc _ ≤ ∑ h ∈ (freq L).filter (fun h => CaseII τ y Y h),
          ∑ M ∈ Finset.Icc (-K) K, (if Q M h then ‖phi (Aset τ y Y) h‖ else 0) := by
          apply Finset.sum_le_sum
          intro h hh
          obtain ⟨M, hM, hMv, hMu⟩ := (Finset.mem_filter.1 hh).2
          have hMI : M ∈ Finset.Icc (-K) K := Finset.mem_Icc.2 (abs_le.1 hM)
          have := Finset.single_le_sum (f := fun M => if Q M h then ‖phi (Aset τ y Y) h‖ else 0)
            (fun M _ => by positivity) hMI
          rw [if_pos ⟨hMv, hMu⟩] at this
          exact this
      _ = ∑ M ∈ Finset.Icc (-K) K, ∑ h ∈ (freq L).filter (fun h => CaseII τ y Y h),
          (if Q M h then ‖phi (Aset τ y Y) h‖ else 0) := Finset.sum_comm
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro M _
          rw [← Finset.sum_filter]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro h hh
            simp only [Finset.mem_filter] at hh ⊢
            exact ⟨hh.1.1, hh.2⟩
          · intros; exact norm_nonneg _
  -- For fixed `M`: inject `h ↦ ζ(h)` into the mismatched column labels.
  have h2b : ∀ M ∈ Finset.Icc (-K) K, ∑ h ∈ (freq L).filter (Q M), ‖phi (Aset τ y Y) h‖ ≤
      ∏ u ∈ Uset y Y, Scol τ y u (M % (P : ℤ)).toNat
        - ∏ u ∈ Uset y Y, Fcol τ y u (M % (P : ℤ)).toNat (M % (u : ℤ)).toNat := by
    intro M _
    set ξM := (M % (P : ℤ)).toNat
    set s := (freq L).filter (Q M)
    let G' : (Uset y Y → ℕ) → ℝ := fun ζ => ∏ u : Uset y Y, Fcol τ y u ξM (ζ u)
    have hPdvd : ∀ h ∈ s, (P : ℤ) ∣ h - M := by
      intro h hh
      exact prod_primes_dvd_int _ (fun v hv => prime_of_mem_Vset hv) _
        (Finset.mem_filter.1 hh).2.1
    have hrow : ∀ h ∈ s, (h % (P : ℤ)).toNat = ξM := by
      intro h hh
      have : h % (P : ℤ) = M % (P : ℤ) := (Int.modEq_iff_dvd.2 (hPdvd h hh)).symm
      simp only [ξM, this]
    have hinj : Set.InjOn col s := by
      intro h hh h' hh' he
      have hd : (P : ℤ) ∣ h - h' := by
        have := dvd_sub (hPdvd h hh) (hPdvd h' hh')
        have e : h - M - (h' - M) = h - h' := by ring
        rwa [e] at this
      exact label_inj (Finset.mem_filter.1 hh).1 (Finset.mem_filter.1 hh').1 hd
        (hcol_dvd h h' he)
    set ζM : Uset y Y → ℕ := col M
    have hζM : ζM ∈ Fintype.piFinset (fun u : Uset y Y => range (u : ℕ)) := hcol_mem M
    have himg : s.image col ⊆ (Fintype.piFinset (fun u : Uset y Y => range (u : ℕ))).erase ζM := by
      intro ζ hζ
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hζ
      refine Finset.mem_erase.2 ⟨fun he => ?_, hcol_mem h⟩
      obtain ⟨u, hu, hnd⟩ := (Finset.mem_filter.1 hh).2.2
      exact hnd (hcol_dvd h M he u hu)
    calc ∑ h ∈ s, ‖phi (Aset τ y Y) h‖ = ∑ h ∈ s, G' (col h) := by
          refine Finset.sum_congr rfl (fun h hh => ?_)
          rw [hphi h]
          simp only [G, G', lab, hrow h hh]
      _ = ∑ ζ ∈ s.image col, G' ζ := (Finset.sum_image hinj).symm
      _ ≤ ∑ ζ ∈ (Fintype.piFinset (fun u : Uset y Y => range (u : ℕ))).erase ζM, G' ζ :=
          Finset.sum_le_sum_of_subset_of_nonneg himg
            (fun ζ _ _ => Finset.prod_nonneg (fun _ _ => Fcol_nonneg _ _ _))
      _ = ∑ ζ ∈ Fintype.piFinset (fun u : Uset y Y => range (u : ℕ)), G' ζ - G' ζM :=
          Finset.sum_erase_eq_sub hζM
      _ = _ := by
          rw [eq_factor ξM]
          congr 1
          exact Finset.prod_coe_sort (Uset y Y)
            (fun u => Fcol τ y u ξM (M % (u : ℤ)).toNat)
  have h2 := h2a.trans (Finset.sum_le_sum h2b)
  linarith

/-- **Proposition 9.1 (minor arcs).**  For `y` large, `∑_{h in cases II and III} |φ(h)| ≤ 1/2`. -/
theorem prop_minor (hL : Large τ y) (hT : Tuned τ y Y) :
    ∑ h ∈ (freq (Lnum τ y Y)).filter (fun h => CaseII τ y Y h ∨ CaseIII τ y h),
        ‖phi (Aset τ y Y) h‖ ≤ 1 / 2 := by
  have h1 := minor_le_labels (Y := Y) hL
  have h2 := caseIII_total hL hT
  have h3 := caseII_total hL hT
  linarith

end Erdos306

end

section
-- Source: https://arxiv.org/src/2609.32140v1/anc/lean/Erdos306/Core.lean
/-
Assembly of §§4–9: Proposition 4.2 and Theorem 3.1 (small targets).
-/

namespace Erdos306

open Real Finset

open scoped Classical

variable {τ : ℚ} {y Y : ℕ}

/-- **Proposition 4.2.**  There is `S ⊆ A` with `σ(S) ≡ τ (mod 1)`.
(Split formula (2) into the three cases: case I contributes `≥ 1/L` (Prop. 7.1), cases II and III at
most `1/(2L)` in absolute value (Prop. 9.1); so `N > 0`.) -/
theorem prop_core (hsq : Squarefree τ.den) (hL : Large τ y) (hT : Tuned τ y Y) :
    ∃ S ⊆ Aset τ y Y, ∃ k : ℤ, sigma S - τ = k := by
  set L := Lnum τ y Y with hLdef
  set A := Aset τ y Y with hAdef
  set K : ℤ := (y : ℤ) ^ 7 with hK
  have hLpos : 0 < L := by
    have h1 := L_gt (Y := Y) hL
    have h2 : (0 : ℤ) ≤ (y : ℤ) ^ 7 := by positivity
    have : (0 : ℤ) < (L : ℤ) := by rw [hLdef]; linarith
    exact_mod_cast this
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hA : ∀ p ∈ A, 0 < p.1 * p.2 ∧ p.1 * p.2 ∣ L := by
    intro p hp
    refine ⟨?_, edge_dvd_L hL hp⟩
    have h1 := (prime_of_mem_Vset (mem_Aset.1 hp).1).pos
    have h2 := (prime_of_mem_Uset (mem_Aset.1 hp).2).pos
    positivity
  have hN := eq_N A τ L hLpos hA (den_dvd_L hsq)
  -- split the frequencies into major arcs `|h| ≤ y^7` and the rest
  set f : ℤ → ℂ := fun h => ee (-((h : ℝ) * τ)) * phi A h with hf
  have hsplit := Finset.sum_filter_add_sum_filter_not (freq L) (fun h => |h| ≤ K) f
  have hmaj : (freq L).filter (fun h => |h| ≤ K) = Finset.Icc (-K) K := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨-, hh⟩; exact abs_le.1 hh
    · intro hh
      exact ⟨mem_freq_of_small hL (abs_le.2 hh), abs_le.2 hh⟩
  rw [hmaj] at hsplit
  -- bound on the minor arcs
  have hminor : ‖∑ h ∈ (freq L).filter (fun h => ¬ |h| ≤ K), f h‖ ≤ 1 / 2 := by
    calc ‖∑ h ∈ (freq L).filter (fun h => ¬ |h| ≤ K), f h‖
        ≤ ∑ h ∈ (freq L).filter (fun h => ¬ |h| ≤ K), ‖f h‖ := norm_sum_le _ _
      _ = ∑ h ∈ (freq L).filter (fun h => ¬ |h| ≤ K), ‖phi A h‖ := by
          refine Finset.sum_congr rfl (fun h _ => ?_)
          simp [hf, norm_ee]
      _ ≤ ∑ h ∈ (freq L).filter (fun h => CaseII τ y Y h ∨ CaseIII τ y h), ‖phi A h‖ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro h hh
            simp only [Finset.mem_filter] at hh ⊢
            refine ⟨hh.1, ?_⟩
            rcases (three_cases (Y := Y) hL h).1 with h1 | h1
            · exact absurd ((caseI_iff hL hh.1).1 h1) hh.2
            · exact h1
          · intros; exact norm_nonneg _
      _ ≤ 1 / 2 := prop_minor hL hT
  have hmajor := prop_major hL hT
  -- real parts
  have hre : ((Ncount A τ : ℂ) / 2 ^ A.card).re ≥ 1 / (2 * L) := by
    rw [hN, ← hsplit, mul_add]
    have e1 : (1 / (L : ℂ)) * ∑ h ∈ Finset.Icc (-K) K, f h = SigmaMaj τ y Y := rfl
    rw [Complex.add_re, e1]
    have e2 : ((1 / (L : ℂ)) * ∑ h ∈ (freq L).filter (fun h => ¬ |h| ≤ K), f h).re
        ≥ -(1 / (2 * L)) := by
      set R := ∑ h ∈ (freq L).filter (fun h => ¬ |h| ≤ K), f h
      have : (1 / (L : ℂ)) * R = ((1 / (L : ℝ) : ℝ) : ℂ) * R := by push_cast; ring
      rw [this, Complex.re_ofReal_mul]
      have hRre : -‖R‖ ≤ R.re := by
        have := Complex.abs_re_le_norm R
        linarith [neg_abs_le R.re]
      have hpos : (0 : ℝ) ≤ 1 / L := by positivity
      have : -(1 / (2 * (L : ℝ))) = 1 / L * (-(1 / 2)) := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left (by linarith) hpos
    have e3 := hmajor.2
    have : 1 / (L : ℝ) - 1 / (2 * L) = 1 / (2 * L) := by field_simp; ring
    linarith
  have hNpos : 0 < Ncount A τ := by
    by_contra hcon
    push Not at hcon
    have : Ncount A τ = 0 := by omega
    rw [this] at hre
    simp at hre
    have : (0 : ℝ) < (L : ℝ)⁻¹ * 2⁻¹ := by positivity
    linarith
  unfold Ncount at hNpos
  obtain ⟨S, hS⟩ := Finset.card_pos.1 hNpos
  simp only [Finset.mem_filter, Finset.mem_powerset] at hS
  exact ⟨S, hS.1, hS.2⟩

/-- The statement of Theorem 3.1 (small targets). -/
def SmallTargets : Prop :=
  ∀ τ : ℚ, 0 < τ → τ ≤ 1 / 400 → Squarefree τ.den →
    ∃ y0 : ℕ, ∀ y ≥ y0, ∃ S : Finset (ℕ × ℕ),
      (∀ p ∈ S, p.1.Prime ∧ p.2.Prime ∧ p.1 ≤ 2 * y ^ 2 ∧ y ^ 8 < p.2 ∧ p.2 ≤ y ^ 9) ∧
      ∑ p ∈ S, (1 : ℚ) / (p.1 * p.2) = τ

/-- **Theorem 3.1 (Small targets).**  Let `τ = a/b ∈ (0, η]`, `η = 1/400`, with `b` squarefree.
Then for every sufficiently large `y`, `τ` is a finite sum of distinct `1/(vu)` with
`v ≤ 2y² < y^8 < u ≤ y^9` primes. -/
theorem thm_small (hR : DyadicPrimeCount) : SmallTargets := by
  intro τ h0 hη hsq
  obtain ⟨y0, hy0⟩ := eventually_large hR h0
  refine ⟨y0, fun y hy => ?_⟩
  have hL := hy0 y hy
  obtain ⟨Y, hT⟩ := lem_tuning h0 hη hL
  obtain ⟨S, hSA, k, hk⟩ := prop_core hsq hL hT
  refine ⟨S, fun p hp => ?_, sigma_eq_of_congr h0 hη hT hSA k hk⟩
  have hpA := mem_Aset.1 (hSA hp)
  have hv := le_of_mem_Vset hL hpA.1
  have hu := bounds_of_mem_Uset hpA.2
  exact ⟨prime_of_mem_Vset hpA.1, prime_of_mem_Uset hpA.2, hv.2, hu.1, hu.2.trans hT.hi⟩

end Erdos306

end

section
-- Source: https://arxiv.org/src/2609.32140v1/anc/lean/Erdos306/Reduction.lean
/-
§3 of the paper: reduction of Theorem 1.1 to small targets (Theorem 3.1) by prime dilution.
-/

namespace Erdos306

open Finset

/-- `n` is a product of two distinct primes. -/
def IsSemiprime2 (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n = p * q

/-- The statement of Theorem 1.1. -/
def MainStatement : Prop :=
  ∀ q : ℚ, 0 < q → Squarefree q.den →
    ∃ F : Finset ℕ, (∀ n ∈ F, IsSemiprime2 n) ∧ ∑ n ∈ F, (1 : ℚ) / n = q

/-- **Proof of Theorem 1.1 from Theorem 3.1** (§3).  Split `a/b` into `q` equal parts
`x = a/(bq) ≤ η` for a large prime `q ∤ ab`, represent `x` with `q` different values of `y`
whose ranges `(y^8, y^9]` are disjoint, and take the union. -/
theorem thm_main_of_small
    (hsmall : ∀ τ : ℚ, 0 < τ → τ ≤ 1 / 400 → Squarefree τ.den →
      ∃ y0 : ℕ, ∀ y ≥ y0, ∃ S : Finset (ℕ × ℕ),
        (∀ p ∈ S, p.1.Prime ∧ p.2.Prime ∧ p.1 ≤ 2 * y ^ 2 ∧ y ^ 8 < p.2 ∧ p.2 ≤ y ^ 9) ∧
        ∑ p ∈ S, (1 : ℚ) / (p.1 * p.2) = τ) :
    MainStatement := by
  intro q hq hsq
  -- Step 1: choose a large prime `p ∤ ab` with `x = q/p ≤ η`.
  obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes (400 * q.num.natAbs + q.den + 1)
  have hnum : 0 < q.num := Rat.num_pos.2 hq
  have hq_le : q ≤ (q.num.natAbs : ℚ) := by
    have h1 : (q.num.natAbs : ℚ) = (q.num : ℚ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hnum)]
    rw [h1]
    conv_lhs => rw [← Rat.num_div_den q]
    apply div_le_self (by exact_mod_cast hnum.le)
    exact_mod_cast q.den_pos
  have hbp : Nat.Coprime q.den p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    have := Nat.le_of_dvd q.den_pos hdvd
    omega
  set x : ℚ := q * (p : ℚ)⁻¹ with hx
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hx0 : 0 < x := by positivity
  have hxη : x ≤ 1 / 400 := by
    rw [hx, ← div_eq_mul_inv, div_le_iff₀ hp0]
    have : (400 * q.num.natAbs : ℚ) ≤ p := by exact_mod_cast (by omega)
    linarith
  have hxsq : Squarefree x.den := by
    have h1 : x.den ∣ q.den * p := by
      have := Rat.mul_den_dvd q ((p : ℚ)⁻¹)
      rwa [Rat.inv_natCast_den, if_neg hp.ne_zero] at this
    exact Squarefree.squarefree_of_dvd h1
      ((Nat.squarefree_mul hbp).2 ⟨hsq, hp.prime.squarefree⟩)
  obtain ⟨y0, hy0⟩ := hsmall x hx0 hxη hxsq
  -- Step 2: `k` disjoint representations of `x`, one for each of `k` increasing values of `y`.
  have key : ∀ k : ℕ, ∃ F : Finset ℕ, (∀ n ∈ F, IsSemiprime2 n) ∧
      ∑ n ∈ F, (1 : ℚ) / n = k * x := by
    intro k
    induction k with
    | zero => exact ⟨∅, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨F, hF, hFsum⟩ := ih
      -- choose `y` so large that the new semiprimes exceed every element of `F`
      set y := max y0 (max (F.sup id + 1) 2) with hy
      have hy0' : y0 ≤ y := le_max_left _ _
      have hyF : F.sup id + 1 ≤ y := le_trans (le_max_left _ _) (le_max_right _ _)
      have hy2 : 2 ≤ y := le_trans (le_max_right _ _) (le_max_right _ _)
      obtain ⟨S, hS, hSsum⟩ := hy0 y hy0'
      have h2y : 2 * y ^ 2 < y ^ 8 := by
        have : y ^ 8 = y ^ 2 * y ^ 6 := by ring
        have h6 : 2 < y ^ 6 := by
          calc 2 < 2 ^ 6 := by norm_num
            _ ≤ y ^ 6 := Nat.pow_le_pow_left hy2 6
        rw [this]
        have : 0 < y ^ 2 := by positivity
        nlinarith
      have hyy : y ≤ y ^ 8 := Nat.le_self_pow (by norm_num) y
      set G := S.image (fun r : ℕ × ℕ => r.1 * r.2) with hG
      have hinj : Set.InjOn (fun r : ℕ × ℕ => r.1 * r.2) S := by
        rintro ⟨v, u⟩ hr ⟨v', u'⟩ hr' heq
        simp only at heq
        obtain ⟨hv, hu, hv2, hu8, -⟩ := hS _ hr
        obtain ⟨hv', hu', hv2', hu8', -⟩ := hS _ hr'
        simp only at hv hu hv2 hu8 hv' hu' hv2' hu8'
        have hdvd : u ∣ v' * u' := ⟨v, by rw [← heq]; ring⟩
        rcases (Nat.Prime.dvd_mul hu).1 hdvd with h | h
        · have := (Nat.prime_dvd_prime_iff_eq hu hv').1 h
          omega
        · have huu := (Nat.prime_dvd_prime_iff_eq hu hu').1 h
          subst huu
          have : v = v' := Nat.eq_of_mul_eq_mul_right hu.pos heq
          rw [this]
      have hdisj : Disjoint F G := by
        rw [Finset.disjoint_left]
        intro n hnF hnG
        obtain ⟨⟨v, u⟩, hr, rfl⟩ := Finset.mem_image.1 hnG
        obtain ⟨hv, hu, -, hu8, -⟩ := hS _ hr
        have h1 : v * u ≤ F.sup id := Finset.le_sup (f := id) hnF
        have h2 : u ≤ v * u := Nat.le_mul_of_pos_left u hv.pos
        simp only at hu8
        omega
      refine ⟨F ∪ G, ?_, ?_⟩
      · intro n hn
        rcases Finset.mem_union.1 hn with h | h
        · exact hF n h
        · obtain ⟨⟨v, u⟩, hr, rfl⟩ := Finset.mem_image.1 h
          obtain ⟨hv, hu, hv2, hu8, -⟩ := hS _ hr
          exact ⟨v, u, hv, hu, by simp only at hv2 hu8 ⊢; omega, rfl⟩
      · rw [Finset.sum_union hdisj, hFsum, hG, Finset.sum_image hinj]
        push_cast
        rw [hSsum]
        ring
  obtain ⟨F, hF, hFsum⟩ := key p
  refine ⟨F, hF, ?_⟩
  rw [hFsum, hx]
  field_simp

end Erdos306

end

section
-- Source: https://arxiv.org/src/2609.32140v1/anc/lean/Erdos306/Main.lean
/-
Main theorem (Theorem 1.1 of the paper): Erdős Problem #306.
-/

namespace Erdos306

/-- The representation follows from the eventual dyadic prime-counting bound. -/
theorem erdos_306_of_dyadicCount (hR : DyadicPrimeCount) (q : ℚ) (hq : 0 < q)
    (hsq : Squarefree q.den) :
    ∃ F : Finset ℕ, (∀ n ∈ F, ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p ≠ r ∧ n = p * r) ∧
      ∑ n ∈ F, (1 : ℚ) / n = q := by
  obtain ⟨F, hF, hsum⟩ := thm_main_of_small (thm_small hR) q hq hsq
  refine ⟨F, fun n hn => ?_, hsum⟩
  obtain ⟨p, r, hp, hr, hpr, rfl⟩ := hF n hn
  exact ⟨p, r, hp, hr, hpr.ne, rfl⟩


end Erdos306

end


namespace Erdos306Transfer

open scoped BigOperators
open Filter Asymptotics

/-- Keeping the primes in the upper interval in the central-binomial-coefficient
    argument for Bertrand's postulate gives a quantitative bound. -/
private lemma logCentralBinom_le (n : ℕ) (hn : 2 < n) :
    Real.log (n.centralBinom : ℝ) ≤
      (Nat.sqrt (2 * n) + 1 : ℝ) * Real.log (2 * n) +
      Real.log 4 * ((2 * n : ℝ) / 3) +
      (((Finset.Ioc n (2 * n)).filter Nat.Prime).card : ℝ) * Real.log (2 * n) := by
  classical
  let t : ℕ := 2 * n
  let P := Nat.primesLE t
  let f (p : ℕ) : ℝ := Real.log ((p : ℝ) ^ n.centralBinom.factorization p)
  let small (p : ℕ) : ℝ := if p ≤ t.sqrt then Real.log t else 0
  let middle (p : ℕ) : ℝ := if p ≤ t / 3 then Real.log p else 0
  let upper (p : ℕ) : ℝ := if n < p then Real.log t else 0
  have ht : (0 : ℝ) < t := by dsimp [t]; positivity
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (show 1 ≤ t by dsimp [t]; omega)
  have hlog := Real.log_nonneg ht1
  have hprod : (∏ p ∈ P, p ^ n.centralBinom.factorization p) = n.centralBinom := by
    rw [show P = (Finset.range (t + 1)).filter Nat.Prime by
      ext p
      simp [P, Nat.mem_primesLE, and_comm]]
    rw [Finset.prod_filter_of_ne]
    · exact Nat.prod_pow_factorization_centralBinom n
    · intro p hp hne
      contrapose! hne
      rw [Nat.factorization_eq_zero_of_not_prime _ hne, pow_zero]
  have hcastprod :
      (∏ p ∈ P, (p : ℝ) ^ n.centralBinom.factorization p) = (n.centralBinom : ℝ) := by
    exact_mod_cast hprod
  have hsum : Real.log (n.centralBinom : ℝ) = ∑ p ∈ P, f p := by
    rw [← hcastprod, Real.log_prod]
    intro p hp
    have prime : p.Prime := (Nat.mem_primesLE.mp hp).2
    exact pow_ne_zero _ (by exact_mod_cast prime.ne_zero)
  have hpoint (p : ℕ) (hp : p ∈ P) : f p ≤ small p + middle p + upper p := by
    have hprime : p.Prime := (Nat.mem_primesLE.mp hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hprime.one_lt.le
    have hlogp := Real.log_nonneg hp1
    have hmid : 0 ≤ middle p := by dsimp [middle]; split <;> positivity
    have hup : 0 ≤ upper p := by dsimp [upper]; split <;> positivity
    have hf : f p ≤ Real.log t := by
      apply Real.log_le_log (pow_pos hp0 _)
      exact_mod_cast (Nat.pow_factorization_choose_le (p := p) (k := n)
        (show 0 < t by dsimp [t]; omega))
    by_cases hs : p ≤ t.sqrt
    · simp only [small, if_pos hs]
      linarith
    have hf' : f p ≤ Real.log p := by
      apply Real.log_le_log (pow_pos hp0 _)
      calc
        _ ≤ (p : ℝ) ^ 1 := by
          apply pow_le_pow_right₀ hp1
          exact Nat.factorization_choose_le_one ((Nat.sqrt_lt'.mp (lt_of_not_ge hs)))
        _ = _ := pow_one _
    by_cases hm : p ≤ t / 3
    · simp only [small, if_neg hs, middle, if_pos hm, zero_add]
      linarith
    by_cases hu : n < p
    · simpa [small, hs, middle, hm, upper, hu] using hf
    have hexp := Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul
      hn (le_of_not_gt hu) (show 2 * n < 3 * p by dsimp [t] at hm; omega)
    simp [f, hexp, small, hs, middle, hm, upper, hu]
  have hsmall : ∑ p ∈ P, small p ≤ (t.sqrt + 1 : ℝ) * Real.log t := by
    have hc : (P.filter (· ≤ t.sqrt)).card ≤ t.sqrt + 1 := by
      simpa using (Finset.card_le_card (t := Finset.range (t.sqrt + 1))
        (fun p hp => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hp).2)))
    dsimp [small]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hc' : ((P.filter (· ≤ t.sqrt)).card : ℝ) ≤ (t.sqrt : ℝ) + 1 := by exact_mod_cast hc
    exact mul_le_mul_of_nonneg_right hc' hlog
  have hmiddle : ∑ p ∈ P, middle p ≤ Real.log 4 * ((t : ℝ) / 3) := by
    have hset : P.filter (· ≤ t / 3) = Nat.primesLE (t / 3) := by
      ext p
      simp only [P, Finset.mem_filter, Nat.mem_primesLE]
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.trans (Nat.div_le_self _ _), h.2⟩, h.1⟩⟩
    dsimp [middle]
    rw [← Finset.sum_filter, hset, ← Chebyshev.theta_eq_sum_primesLE_log]
    exact (Chebyshev.theta_le_log4_mul_x (by positivity)).trans
      (mul_le_mul_of_nonneg_left (Nat.cast_div_le.trans (by norm_cast)) (by positivity))
  have hupper :
      ∑ p ∈ P, upper p = (((Finset.Ioc n t).filter Nat.Prime).card : ℝ) * Real.log t := by
    have hset : P.filter (n < ·) = (Finset.Ioc n t).filter Nat.Prime := by
      ext p
      simp [P, Nat.mem_primesLE, and_left_comm, and_comm]
    dsimp [upper]
    rw [← Finset.sum_filter, hset]
    simp [nsmul_eq_mul]
  have htotal := Finset.sum_le_sum (s := P) hpoint
  simp only [Finset.sum_add_distrib] at htotal
  rw [← hsum, hupper] at htotal
  push_cast [t] at hsmall hmiddle htotal ⊢
  linarith

private lemma eventualLogError :
    ∀ᶠ t : ℝ in atTop, (Real.sqrt t + 2) * Real.log t ≤ t / 30 := by
  filter_upwards [
    (isLittleO_log_rpow_atTop (r := (1 : ℝ) / 2) (by norm_num)).bound
      (c := (1 : ℝ) / 90) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with t ht ht1
  have ht0 : 0 ≤ t := by linarith
  have hlog := Real.log_nonneg ht1
  have hs : 1 ≤ Real.sqrt t := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt ht1
  rw [← Real.sqrt_eq_rpow, Real.norm_of_nonneg hlog,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)] at ht
  have hsq := Real.sq_sqrt ht0
  calc
    (Real.sqrt t + 2) * Real.log t ≤ (3 * Real.sqrt t) * Real.log t :=
      mul_le_mul_of_nonneg_right (by linarith) hlog
    _ ≤ (3 * Real.sqrt t) * ((1 / 90 : ℝ) * Real.sqrt t) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = t / 30 := by nlinarith

/-- Eventually the dyadic interval contains at least x/(7 log x) primes. -/
theorem eventually_dyadic_count :
    ∃ x0 : ℝ, ∀ x ≥ x0, x / (7 * Real.log x) ≤
      (((Finset.Ioc ⌊x / 2⌋₊ ⌊x⌋₊).filter Nat.Prime).card : ℝ) := by
  obtain ⟨X, hX⟩ := eventually_atTop.1 eventualLogError
  refine ⟨max 16 (X + 2), fun x hx => ?_⟩
  have hx16 : (16 : ℝ) ≤ x := (le_max_left _ _).trans hx
  have hxX : X + 2 ≤ x := (le_max_right _ _).trans hx
  let n := ⌊x / 2⌋₊
  let t : ℝ := 2 * (n : ℝ)
  let d : ℝ := (((Finset.Ioc n (2 * n)).filter Nat.Prime).card : ℝ)
  let D : ℝ := (((Finset.Ioc n ⌊x⌋₊).filter Nat.Prime).card : ℝ)
  have htx : t ≤ x := by
    have := Nat.floor_le (a := x / 2) (by linarith)
    dsimp [t, n]
    linarith
  have hxt : x < t + 2 := by
    have := Nat.lt_floor_add_one (x / 2)
    dsimp [t, n]
    linarith
  have hn : 4 ≤ n := by
    exact (Nat.le_floor (a := x / 2) (by norm_num at *; linarith))
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have ht1 : 1 ≤ t := by dsimp [t]; linarith
  have ht0 : 0 ≤ t := by linarith
  have hlog := Real.log_nonneg ht1
  have hs : (Nat.sqrt (2 * n) : ℝ) ≤ Real.sqrt t := by
    simpa [t] using Real.nat_sqrt_le_real_sqrt (a := 2 * n)
  have hlogn : Real.log (n : ℝ) ≤ Real.log t :=
    Real.log_le_log (by linarith) (by dsimp [t]; linarith)
  have herror := hX t (by linarith)
  have hlower : Real.log 4 * n < Real.log (n : ℝ) + Real.log (n.centralBinom : ℝ) := by
    have hreal : (4 : ℝ) ^ n < (n : ℝ) * (n.centralBinom : ℝ) := by
      exact_mod_cast Nat.four_pow_lt_mul_centralBinom n hn
    have hp : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
    have h := Real.log_lt_log hp hreal
    rw [Real.log_pow, Real.log_mul (by positivity) (by exact_mod_cast (Nat.centralBinom_pos n).ne')] at h
    linarith
  have hupper := logCentralBinom_le n (by omega)
  change Real.log (n.centralBinom : ℝ) ≤
    (↑(2 * n).sqrt + 1 : ℝ) * Real.log t + Real.log 4 * (t / 3) + d * Real.log t at hupper
  have hsmall := mul_le_mul_of_nonneg_right (add_le_add_right hs (1 : ℝ)) hlog
  have hmain : t / 6 ≤ d * Real.log t := by
    have hln4 : (6 / 5 : ℝ) ≤ Real.log 4 := by
      rw [Real.log_four_eq]
      linarith [Real.log_two_gt_d9]
    have hmul := mul_le_mul_of_nonneg_right hln4 ht0
    have hlogn' : Real.log (n : ℝ) ≤ Real.log t := hlogn
    have heq : Real.log 4 * (n : ℝ) = Real.log 4 * (t / 2) := by dsimp [t]; ring
    rw [heq] at hlower
    linarith
  have hd : d ≤ D := by
    have htfl : 2 * n ≤ ⌊x⌋₊ := by apply Nat.le_floor; simpa [t] using htx
    apply Nat.cast_le.mpr (Finset.card_le_card _)
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans htfl⟩, hp.2⟩
  have hxlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogtx := Real.log_le_log (show 0 < t by linarith) htx
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hterm := mul_le_mul hd hlogtx hlog hD
  change x / (7 * Real.log x) ≤ D
  rw [div_le_iff₀ (by positivity)]
  nlinarith

end Erdos306Transfer


theorem OMA.solution : type_of% @OMA.S_erdos_306.main := by
  exact Erdos306.erdos_306_of_dyadicCount Erdos306Transfer.eventually_dyadic_count
