import OMAReductions.R_ABC_abc_R1
import Mathlib

-- Step ABC.abc.R1.H1: hypothesis H1 of reduction ABC.abc.R1 (the S-unit equation over the rationals)
-- Credit: @Mapika

/-!
The S-unit equation over the rationals (step `ABC.abc.R1.H1`)

Target (`reductions/ABC.abc.R1.lean`):

  def H1 : Prop := ∀ S : Finset ℕ, {p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧ p.1.Coprime p.2 ∧
      (p.1 * p.2 * (p.1 + p.2)).primeFactors ⊆ S}.Finite

This is the theorem of Siegel (1921) and Mahler (1933): `a + b = c` has only finitely many
coprime positive solutions whose prime factors all lie in a fixed finite set.

Existing formalization. A Lean 4 proof of the S-unit equation in two variables over number
fields (through the Subspace Theorem) is announced in the public GitHub repository
`Subspace-Theorems`, file `DiophantineApproximation/UnitEquation.lean`. It is not part of the
Mathlib used here. The present development is independent of it and follows a different,
elementary route; nobody on this team has read that code.

Method. The hypergeometric (Pade) method of Thue and Siegel with two solutions in one family, as
used for unit equations by Evertse (Invent. Math. 75 (1984), 561-584; not read by the leads, known
from its abstract and from citations) and by Hirata-Kohno, Kawashima, Poels, Washio
(arXiv:2211.14399; read in excerpts: Pade approximants of binomial functions, cube roots in a
number field, heights). The chain below is the leads' own elementary variant over the integers: an
auxiliary prime exponent `n ≥ 17` outside `S`, no p-adic numbers, no real `n`-th roots, no Siegel
lemma, and real logarithms only in the last selection step. It was derived on paper, re-derived by
a second lead and by a reviewer, and every lemma was tested numerically (exact-arithmetic
test scripts kept outside this file); it is not a transcription of a
published proof.

Part A (Pade approximants to `(1 - X)^(1/n)`, over `ℚ[X]` and then `ℤ[X]`).
  `F ν m = ∑_{k ≤ m} binom(m + ν, k) binom(2m - k, m) (-X)^k`, `A_m = F (1/n) m`, `B_m = F (-1/n) m`.
  * `ode`  : the hypergeometric differential equation of `F ν m`.
  * `pade` : `X^(2m+1) ∣ A_m^n - (1 - X) B_m^n` (from the ODE through a Wronskian).
  * `det`  : `A_m B_{m+1} - A_{m+1} B_m = d X^(2m+1)`, `d ≠ 0`.
  * `size` : the sum of the absolute values of the coefficients of `F ν m` is at most `16^m`.
  * `gb`   : `k! ∣ n^k ∏_{j<k} (a - j n)` for `n` prime (so `n^(2m) F (±1/n) m` is integral).
  * `pkg`  : packaging: integer polynomials `P_m = n^(2m) A_m`, `Q_m = n^(2m) B_m` form a
             `PadeSys n (16 n^2) P Q`.
Part B (one pair of solutions `a_i = A y_i^n`, `b_i = B z_i^n`, `c_i = a_i + b_i`).
  * `lin`  : an integer polynomial `R` with `R^n ≡ n^(ne) (1 - X)` and `n^e P ≡ R Q` mod `X^M`.
  * `div`  : for a prime `p ≠ n`: `p^E ∣ c₁^M` and `p^E ∣ b₁ u^n + a₁ w^n` and `u ≡ w` mod `p`
             imply `p^E ∣ w hom(P)(c₁, b₁) - u hom(Q)(c₁, b₁)`.
  * `nv`   : the linear forms for `m` and `m + 1` do not both vanish (proved here, with the
             helper `hom_cast`).
  * `pair` : for every `m` some `m' ∈ {m, m+1}` has
             `gcd(c₁^(2m'+1), c₂)^n ≤ (2 (K c₁)^m')^n c₁ c₂`.
Part C (families and selection).
  * `rep`  : every `S`-unit is `A y^n` with `A ∣ (∏ S)^(n-1)`.
  * `fam`  : an infinite solution set contains an infinite family with fixed `A`, `B` and fixed
             residues of `y`, `z` modulo every prime of `S`.
  * `cell` : pigeonhole on the shares `v_p(c) log p / log c`.
  * `ineq` : two members of a cell, the second at least the fifth power of the first, violate
             the bound of `pair`.
  * `sel` (proved here from `cell` and `ineq`), `main`, `OMA.solution` (proved here).

The file was written by a team of agents from one blueprint: each lemma named above was proved
separately against a fixed statement (helper names carry a two-letter tag) and the pieces were
assembled mechanically.

Review (one independent adversarial reviewer, with scripts of its own): all statements
re-derived and attacked numerically, no counterexample, no change of statement proposed.
Strongest objection: a single rational `u / w` cannot follow the right p-adic branch of the
`n`-th root at every prime of `c₁` at once, and the root is not unique when `p` divides
`P(0) = n^(2m) binom(2m, m)`. Disposition: `lin` is one congruence in `ℤ[X]`, valid at every
prime simultaneously; `div` fixes the branch at each `p` through `u ≡ w` modulo `p` (the
conclusion fails in every case of the negative control without it) and never takes `n`-th roots
of `P`; the primes are combined with `Nat.dvd_iff_prime_pow_dvd_dvd`. Second objection: the chain
proves too much. Disposition: only `ineq` uses `n ≥ 17`; for `n = 2` on the genuinely infinite
family `y² + z² = 5^k` the bound of `pair` holds and the conclusion of `ineq` fails, as it must;
for `n ≥ 3` the chain gives finiteness of `A y^n + B z^n ∈ S-units`, which is Thue-Mahler.
-/

namespace OMA.SUnit

open Polynomial

/-- The coefficient of `X^k` in `F ν m`:
`(-1)^k * binom(m + ν, k) * binom(2m - k, m)`, the generalized binomial coefficient written as
`(∏_{j<k} (m + ν - j)) / k!`. Only `k ≤ m` is ever used (for `k > m` and `m = 0` the natural
subtraction `2 * m - k` makes the value meaningless). -/
noncomputable def cf (ν : ℚ) (m k : ℕ) : ℚ :=
  (-1) ^ k * (∏ j ∈ Finset.range k, ((m : ℚ) + ν - (j : ℚ))) / (k.factorial : ℚ)
    * (((2 * m - k).choose m : ℕ) : ℚ)

/-- `F ν m = ∑_{k ≤ m} cf ν m k * X^k`, that is `binom(2m, m) * ₂F₁(-m, -m - ν; -2m; X)`.
`F (1/n) m` and `F (-1/n) m` are the numerator and the denominator of the diagonal Pade
approximant of `(1 - X)^(1/n)`. -/
noncomputable def F (ν : ℚ) (m : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (m + 1), C (cf ν m k) * X ^ k

/-- Homogenization in degree `m`: `hom m P c b = ∑_{k ≤ m} P_k c^k b^(m-k)`
(`= b^m P(c / b)` when `natDegree P ≤ m` and `b ≠ 0`). -/
def hom (m : ℕ) (P : ℤ[X]) (c b : ℤ) : ℤ :=
  ∑ k ∈ Finset.range (m + 1), P.coeff k * c ^ k * b ^ (m - k)

/-- What Part B needs to know about the integer Pade approximants `P m / Q m` of
`(1 - X)^(1/n)`. -/
structure PadeSys (n K : ℕ) (P Q : ℕ → ℤ[X]) : Prop where
  one_le : 1 ≤ K
  degP : ∀ m, (P m).natDegree ≤ m
  degQ : ∀ m, (Q m).natDegree ≤ m
  coeff_zero_eq : ∀ m, (P m).coeff 0 = (Q m).coeff 0
  coeff_zero_ne : ∀ m, (P m).coeff 0 ≠ 0
  pade : ∀ m, (X : ℤ[X]) ^ (2 * m + 1) ∣ (P m) ^ n - (1 - X) * (Q m) ^ n
  det : ∀ m, ∃ d : ℤ, d ≠ 0 ∧ P m * Q (m + 1) - P (m + 1) * Q m = C d * X ^ (2 * m + 1)
  sizeP : ∀ m, ∑ k ∈ Finset.range (m + 1), |(P m).coeff k| ≤ (K : ℤ) ^ m
  sizeQ : ∀ m, ∑ k ∈ Finset.range (m + 1), |(Q m).coeff k| ≤ (K : ℤ) ^ m

-- ### Part A: the Pade approximants

-- ode
section OD

lemma OD_coeff (ν : ℚ) (m k : ℕ) :
    (F ν m).coeff k = if k ≤ m then cf ν m k else 0 := by
  simp only [F, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

lemma OD_cf_rec (ν : ℚ) (m k : ℕ) (hk : k < m) :
    ((k : ℚ) + 1) * ((k : ℚ) - 2 * m) * cf ν m (k + 1)
      = ((k : ℚ) - m) * ((k : ℚ) - m - ν) * cf ν m k := by
  have hch : ((2 * m - (k + 1)).choose m * (2 * m - k) : ℕ)
      = (2 * m - k).choose m * (m - k) := by
    have h := Nat.choose_mul_succ_eq (2 * m - (k + 1)) m
    have e1 : 2 * m - (k + 1) + 1 = 2 * m - k := by omega
    have e2 : 2 * m - k - m = m - k := by omega
    rw [e1, e2] at h
    exact h
  have hch' : (((2 * m - (k + 1)).choose m : ℕ) : ℚ) * (2 * (m : ℚ) - k)
      = (((2 * m - k).choose m : ℕ) : ℚ) * ((m : ℚ) - k) := by
    have := congrArg (fun x : ℕ => (x : ℚ)) hch
    simp only [Nat.cast_mul] at this
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)] at this
    push_cast at this
    linarith [this]
  unfold cf
  rw [Finset.prod_range_succ, Nat.factorial_succ, pow_succ]
  have hf : ((k.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  push_cast
  generalize (∏ j ∈ Finset.range k, ((m : ℚ) + ν - (j : ℚ))) = P
  generalize ((-1 : ℚ) ^ k) = s
  generalize ((k.factorial : ℕ) : ℚ) = f at hf ⊢
  generalize (((2 * m - (k + 1)).choose m : ℕ) : ℚ) = c1 at hch' ⊢
  generalize (((2 * m - k).choose m : ℕ) : ℚ) = c0 at hch' ⊢
  field_simp
  linear_combination (s * P * ((m : ℚ) + ν - k)) * hch'

lemma OD_rec (ν : ℚ) (m k : ℕ) :
    ((k : ℚ) + 1) * ((k : ℚ) - 2 * m) * (F ν m).coeff (k + 1)
      = ((k : ℚ) - m) * ((k : ℚ) - m - ν) * (F ν m).coeff k := by
  rw [OD_coeff, OD_coeff]
  rcases lt_trichotomy k m with h | h | h
  · rw [if_pos (by omega), if_pos h.le]
    exact OD_cf_rec ν m k h
  · subst h
    simp
  · rw [if_neg (by omega), if_neg (by omega)]
    simp

lemma ode (ν : ℚ) (m : ℕ) :
    X * (1 - X) * derivative (derivative (F ν m))
      + (C (-(2 * (m : ℚ))) + C (2 * (m : ℚ) + ν - 1) * X) * derivative (F ν m)
      - C ((m : ℚ) * ((m : ℚ) + ν)) * F ν m = 0 := by
  have e : X * (1 - X) * derivative (derivative (F ν m))
      + (C (-(2 * (m : ℚ))) + C (2 * (m : ℚ) + ν - 1) * X) * derivative (F ν m)
      - C ((m : ℚ) * ((m : ℚ) + ν)) * F ν m
      = X * derivative (derivative (F ν m)) - X * (X * derivative (derivative (F ν m)))
        + C (-(2 * (m : ℚ))) * derivative (F ν m)
        + C (2 * (m : ℚ) + ν - 1) * (X * derivative (F ν m))
        - C ((m : ℚ) * ((m : ℚ) + ν)) * F ν m := by ring
  rw [e]
  ext n
  rcases n with _ | n
  · have h0 := OD_rec ν m 0
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_mul_zero, coeff_derivative,
      coeff_zero]
    push_cast at h0 ⊢
    linear_combination h0
  · have h1 := OD_rec ν m (n + 1)
    rcases n with _ | n
    · simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_mul, coeff_X_mul_zero,
        coeff_derivative, coeff_zero]
      push_cast at h1 ⊢
      linear_combination h1
    · simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_mul, coeff_derivative,
        coeff_zero]
      push_cast at h1 ⊢
      linear_combination h1

end OD

-- pade
section PD

/-- The constant coefficient of `F ν m` is `binom(2m, m)`. -/
lemma PD_coeff_zero (ν : ℚ) (m : ℕ) : (F ν m).coeff 0 = ((2 * m).choose m : ℚ) := by
  unfold F
  rw [finsetSum_coeff, Finset.sum_eq_single 0]
  · simp [cf]
  · intro k _ hk
    rw [coeff_C_mul, coeff_X_pow, if_neg (Ne.symm hk), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.succ_pos m)) h

/-- The Wronskian-type combination `W = n (1 - X) (A' B - A B') + A B` satisfies the Euler
equation `X W' = 2m W` when `n ν = 1`. -/
lemma PD_wronskian (n : ℕ) (ν : ℚ) (hν : (n : ℚ) * ν = 1) (m : ℕ) :
    X * derivative (C (n : ℚ) * (1 - X)
        * (derivative (F ν m) * F (-ν) m - F ν m * derivative (F (-ν) m))
        + F ν m * F (-ν) m)
      = C (2 * (m : ℚ)) * (C (n : ℚ) * (1 - X)
        * (derivative (F ν m) * F (-ν) m - F ν m * derivative (F (-ν) m))
        + F ν m * F (-ν) m) := by
  have hA := ode ν m
  have hB := ode (-ν) m
  have hcn : C (n : ℚ) * C ν = 1 := by rw [← C_mul, hν, C_1]
  have h2 : (C (2 : ℚ) : ℚ[X]) = 2 := by
    rw [show (2 : ℚ) = 1 + 1 by norm_num, C_add, C_1]; norm_num
  simp only [derivative_mul, derivative_C, derivative_X,
    derivative_one, map_add, map_sub, map_mul, map_neg, map_one, h2] at hA hB ⊢
  generalize derivative (derivative (F ν m)) = A2 at *
  generalize derivative (derivative (F (-ν) m)) = B2 at *
  generalize derivative (F ν m) = A1 at *
  generalize derivative (F (-ν) m) = B1 at *
  generalize F ν m = A at *
  generalize F (-ν) m = B at *
  generalize C (n : ℚ) = cn at *
  generalize C ν = cv at *
  generalize C (m : ℚ) = cm at *
  linear_combination cn * B * hA - cn * A * hB
    + (-(X * (A1 * B + A * B1) - 2 * cm * A * B)) * hcn

/-- A solution of the Euler equation `X W' = 2m W` is divisible by `X^(2m)`. -/
lemma PD_dvd_of_euler (W : ℚ[X]) (m : ℕ)
    (h : X * derivative W = C (2 * (m : ℚ)) * W) : (X : ℚ[X]) ^ (2 * m) ∣ W := by
  rw [X_pow_dvd_iff]
  intro k hk
  have hc := congrArg (fun p : ℚ[X] => p.coeff k) h
  simp only [coeff_C_mul] at hc
  cases k with
  | zero =>
    rw [coeff_X_mul_zero] at hc
    have hm : (0 : ℚ) < 2 * (m : ℚ) := by exact_mod_cast hk
    rcases mul_eq_zero.1 hc.symm with h0 | h0
    · exact absurd h0 hm.ne'
    · exact h0
  | succ k =>
    rw [coeff_X_mul, coeff_derivative] at hc
    have hlt : ((k : ℚ) + 1) < 2 * (m : ℚ) := by exact_mod_cast hk
    have hz : W.coeff (k + 1) * (((k : ℚ) + 1) - 2 * (m : ℚ)) = 0 := by
      linear_combination hc
    rcases mul_eq_zero.1 hz with h0 | h0
    · exact h0
    · exfalso; linarith

/-- The first-order equation satisfied by `Φ = A^n - (1 - X) B^n`. -/
lemma PD_phi (A B : ℚ[X]) (n' : ℕ) :
    (1 - X) * B * derivative (A ^ (n' + 1) - (1 - X) * B ^ (n' + 1))
      - (C ((n' : ℚ) + 1) * (1 - X) * derivative B - B)
        * (A ^ (n' + 1) - (1 - X) * B ^ (n' + 1))
      = A ^ n' * (C ((n' : ℚ) + 1) * (1 - X) * (derivative A * B - A * derivative B)
        + A * B) := by
  simp only [derivative_sub, derivative_mul, derivative_pow_succ, derivative_one, derivative_X]
  ring

/-- If `(1 - X) B Φ' - Q Φ` is divisible by `X^N`, `B(0) ≠ 0` and `Φ(0) = 0`, then `Φ` is
divisible by `X^(N+1)`. -/
lemma PD_step (B Φ Q R : ℚ[X]) (N : ℕ) (hB : B.coeff 0 ≠ 0) (h0 : Φ.coeff 0 = 0)
    (hid : (1 - X) * B * derivative Φ - Q * Φ = X ^ N * R) : (X : ℚ[X]) ^ (N + 1) ∣ Φ := by
  have key : ∀ j : ℕ, j ≤ N + 1 → (X : ℚ[X]) ^ j ∣ Φ := by
    intro j
    induction j with
    | zero => intro _; exact one_dvd _
    | succ j ih =>
      intro hj
      obtain ⟨G, hG⟩ := ih (by omega)
      cases j with
      | zero => simpa using X_dvd_iff.2 h0
      | succ i =>
        obtain ⟨d, rfl⟩ : ∃ d, N = i + 1 + d := Nat.exists_eq_add_of_le (by omega)
        have hder : derivative Φ
            = C ((i : ℚ) + 1) * X ^ i * G + X ^ (i + 1) * derivative G := by
          rw [hG, derivative_mul, derivative_X_pow]
          simp
        rw [hder, hG] at hid
        have hfac : (X : ℚ[X]) ^ i * ((1 - X) * B * (C ((i : ℚ) + 1) * G)
            - X * (X ^ d * R + Q * G - (1 - X) * B * derivative G)) = 0 := by
          linear_combination hid
        have hG0 : (1 - X) * B * (C ((i : ℚ) + 1) * G)
            - X * (X ^ d * R + Q * G - (1 - X) * B * derivative G) = 0 := by
          rcases mul_eq_zero.1 hfac with h | h
          · exact absurd h (pow_ne_zero _ X_ne_zero)
          · exact h
        have hc := congrArg (fun p : ℚ[X] => p.coeff 0) hG0
        simp only [coeff_sub, mul_coeff_zero, coeff_X_zero, coeff_one_zero, coeff_C_zero,
          zero_mul, sub_zero, coeff_zero, one_mul] at hc
        have hi : ((i : ℚ) + 1) ≠ 0 := by positivity
        have hGc : G.coeff 0 = 0 := by
          rcases mul_eq_zero.1 hc with h | h
          · exact absurd h hB
          · rcases mul_eq_zero.1 h with h' | h'
            · exact absurd h' hi
            · exact h'
        obtain ⟨G', hG'⟩ := X_dvd_iff.2 hGc
        exact ⟨G', by rw [hG, hG']; ring⟩
  exact key (N + 1) le_rfl

lemma pade (n m : ℕ) (hn : 0 < n) :
    (X : ℚ[X]) ^ (2 * m + 1) ∣
      F (1 / (n : ℚ)) m ^ n - (1 - X) * F (-(1 / (n : ℚ))) m ^ n := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hν : ((n' + 1 : ℕ) : ℚ) * (1 / ((n' + 1 : ℕ) : ℚ)) = 1 := by
    have : ((n' + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    field_simp
  obtain ⟨W0, hW0⟩ := PD_dvd_of_euler _ m (PD_wronskian (n' + 1) _ hν m)
  have hch : (((2 * m).choose m : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : m ≤ 2 * m)).ne'
  refine PD_step (F (-(1 / ((n' + 1 : ℕ) : ℚ))) m) _
    (C ((n' : ℚ) + 1) * (1 - X) * derivative (F (-(1 / ((n' + 1 : ℕ) : ℚ))) m)
      - F (-(1 / ((n' + 1 : ℕ) : ℚ))) m)
    (F (1 / ((n' + 1 : ℕ) : ℚ)) m ^ n' * W0) (2 * m) ?_ ?_ ?_
  · rw [PD_coeff_zero]; exact hch
  · have e : ∀ ν : ℚ, eval 0 (F ν m) = (((2 * m).choose m : ℕ) : ℚ) := fun ν => by
      rw [← coeff_zero_eq_eval_zero, PD_coeff_zero]
    rw [coeff_zero_eq_eval_zero, eval_sub, eval_mul, eval_pow, eval_pow, e, e]
    simp
  · rw [PD_phi]
    have hcast : (C ((n' : ℚ) + 1) : ℚ[X]) = C (((n' + 1 : ℕ) : ℚ)) := by
      congr 1; push_cast; ring
    rw [hcast, hW0]
    ring

end PD

-- det
section DT

lemma DT_coeff (ν : ℚ) (m k : ℕ) (hk : k ≤ m) : (F ν m).coeff k = cf ν m k := by
  unfold F
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range, Nat.lt_succ_of_le hk]

lemma DT_natDegree (ν : ℚ) (m : ℕ) : (F ν m).natDegree ≤ m := by
  unfold F
  apply natDegree_sum_le_of_forall_le
  intro k hk
  exact le_trans (natDegree_C_mul_X_pow_le _ _)
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))

lemma DT_coeff_zero (ν : ℚ) (m : ℕ) :
    (F ν m).coeff 0 = (((2 * m).choose m : ℕ) : ℚ) := by
  rw [DT_coeff ν m 0 (Nat.zero_le _)]
  simp [cf]

lemma DT_top_succ (ν : ℚ) (m : ℕ) :
    cf ν (m + 1) (m + 1) = -(((m : ℚ) + 1 + ν) / ((m : ℚ) + 1)) * cf ν m m := by
  unfold cf
  have h1 : 2 * (m + 1) - (m + 1) = m + 1 := by omega
  have h2 : 2 * m - m = m := by omega
  rw [h1, h2, Nat.choose_self, Nat.choose_self, Finset.prod_range_succ', Nat.factorial_succ]
  have hf : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
  have hprod : ∏ j ∈ Finset.range m, (((m + 1 : ℕ) : ℚ) + ν - ((j + 1 : ℕ) : ℚ))
      = ∏ j ∈ Finset.range m, ((m : ℚ) + ν - (j : ℚ)) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    push_cast; ring
  rw [hprod]
  push_cast
  field_simp
  ring

lemma DT_top_ne (ν : ℚ) (hν : |ν| < 1) (m : ℕ) : cf ν m m ≠ 0 := by
  unfold cf
  have h2 : 2 * m - m = m := by omega
  rw [h2, Nat.choose_self]
  have hf : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hp : ∏ j ∈ Finset.range m, ((m : ℚ) + ν - (j : ℚ)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    have hj' : j + 1 ≤ m := Finset.mem_range.mp hj
    have hj'' : (j : ℚ) + 1 ≤ m := by exact_mod_cast hj'
    have := (abs_lt.mp hν).1
    linarith
  simp only [Nat.cast_one, mul_one]
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hp) hf

lemma DT_dvd (n m : ℕ) (hn : 2 ≤ n) :
    (X : ℚ[X]) ^ (2 * m + 1) ∣
      F (1 / (n : ℚ)) m * F (-(1 / (n : ℚ))) (m + 1)
        - F (1 / (n : ℚ)) (m + 1) * F (-(1 / (n : ℚ))) m := by
  set A := F (1 / (n : ℚ)) m
  set B := F (-(1 / (n : ℚ))) m
  set A' := F (1 / (n : ℚ)) (m + 1)
  set B' := F (-(1 / (n : ℚ))) (m + 1)
  have hn0 : 0 < n := by omega
  have h1 : (X : ℚ[X]) ^ (2 * m + 1) ∣ A ^ n - (1 - X) * B ^ n := pade n m hn0
  have h2 : (X : ℚ[X]) ^ (2 * m + 1) ∣ A' ^ n - (1 - X) * B' ^ n :=
    dvd_trans (pow_dvd_pow X (by omega)) (pade n (m + 1) hn0)
  set U := A * B'
  set V := A' * B
  have h3 : (X : ℚ[X]) ^ (2 * m + 1) ∣ U ^ n - V ^ n := by
    have e : U ^ n - V ^ n
        = B' ^ n * (A ^ n - (1 - X) * B ^ n) - B ^ n * (A' ^ n - (1 - X) * B' ^ n) := by
      simp only [U, V]; ring
    rw [e]
    exact dvd_sub (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h2 _)
  rw [← geom_sum₂_mul] at h3
  refine (prime_X.pow_dvd_of_dvd_mul_left (2 * m + 1) ?_ h3)
  rw [X_dvd_iff]
  have hU : U.coeff 0 = (((2 * m).choose m : ℕ) : ℚ) * (((2 * (m + 1)).choose (m + 1) : ℕ) : ℚ) := by
    simp only [U, mul_coeff_zero, A, B', DT_coeff_zero]
  have hV : V.coeff 0 = (((2 * m).choose m : ℕ) : ℚ) * (((2 * (m + 1)).choose (m + 1) : ℕ) : ℚ) := by
    simp only [V, mul_coeff_zero, A', B, DT_coeff_zero]; ring
  set c := (((2 * m).choose m : ℕ) : ℚ) * (((2 * (m + 1)).choose (m + 1) : ℕ) : ℚ)
  have hc : c ≠ 0 := by
    simp only [c]
    apply mul_ne_zero <;> exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hcoeff : (∑ i ∈ Finset.range n, U ^ i * V ^ (n - 1 - i)).coeff 0
      = ∑ i ∈ Finset.range n, c ^ i * c ^ (n - 1 - i) := by
    rw [finsetSum_coeff]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_coeff_zero, coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero, eval_pow, eval_pow,
      ← coeff_zero_eq_eval_zero, ← coeff_zero_eq_eval_zero, hU, hV]
  rw [hcoeff, geom_sum₂_self]
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn0.ne'
  exact mul_ne_zero hn' (pow_ne_zero _ hc)

lemma det (n m : ℕ) (hn : 2 ≤ n) :
    ∃ d : ℚ, d ≠ 0 ∧
      F (1 / (n : ℚ)) m * F (-(1 / (n : ℚ))) (m + 1)
        - F (1 / (n : ℚ)) (m + 1) * F (-(1 / (n : ℚ))) m = C d * X ^ (2 * m + 1) := by
  set ν : ℚ := 1 / (n : ℚ) with hνdef
  have hnq : (2 : ℚ) ≤ n := by exact_mod_cast hn
  have hνpos : 0 < ν := by rw [hνdef]; positivity
  have hνlt : ν < 1 := by
    rw [hνdef, div_lt_one (by linarith)]; linarith
  have habs1 : |ν| < 1 := by rw [abs_lt]; constructor <;> linarith
  have habs2 : |-ν| < 1 := by rw [abs_neg]; exact habs1
  set D := F ν m * F (-ν) (m + 1) - F ν (m + 1) * F (-ν) m with hD
  have hdvd : (X : ℚ[X]) ^ (2 * m + 1) ∣ D := DT_dvd n m hn
  have hdeg : D.natDegree ≤ 2 * m + 1 := by
    have e1 : 2 * m + 1 = m + (m + 1) := by ring
    have e2 : 2 * m + 1 = (m + 1) + m := by ring
    have k1 : (F ν m * F (-ν) (m + 1)).natDegree ≤ 2 * m + 1 := by
      rw [e1]; exact natDegree_mul_le_of_le (DT_natDegree _ _) (DT_natDegree _ _)
    have k2 : (F ν (m + 1) * F (-ν) m).natDegree ≤ 2 * m + 1 := by
      rw [e2]; exact natDegree_mul_le_of_le (DT_natDegree _ _) (DT_natDegree _ _)
    exact (natDegree_sub_le_of_le k1 k2).trans (max_self _).le
  have htop : D.coeff (2 * m + 1)
      = cf ν m m * cf (-ν) (m + 1) (m + 1) - cf ν (m + 1) (m + 1) * cf (-ν) m m := by
    have e1 : 2 * m + 1 = m + (m + 1) := by ring
    rw [hD, coeff_sub]
    congr 1
    · rw [e1, coeff_mul_add_eq_of_natDegree_le (DT_natDegree _ _) (DT_natDegree _ _),
        DT_coeff _ _ _ le_rfl, DT_coeff _ _ _ le_rfl]
    · rw [show 2 * m + 1 = (m + 1) + m by ring,
        coeff_mul_add_eq_of_natDegree_le (DT_natDegree _ _) (DT_natDegree _ _),
        DT_coeff _ _ _ le_rfl, DT_coeff _ _ _ le_rfl]
  refine ⟨D.coeff (2 * m + 1), ?_, ?_⟩
  · rw [htop, DT_top_succ ν m, DT_top_succ (-ν) m]
    have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
    have ha := DT_top_ne ν habs1 m
    have hb := DT_top_ne (-ν) habs2 m
    have e : cf ν m m * (-(((m : ℚ) + 1 + -ν) / ((m : ℚ) + 1)) * cf (-ν) m m)
        - -(((m : ℚ) + 1 + ν) / ((m : ℚ) + 1)) * cf ν m m * cf (-ν) m m
        = (2 * ν / ((m : ℚ) + 1)) * (cf ν m m * cf (-ν) m m) := by
      field_simp; ring
    rw [e]
    exact mul_ne_zero (div_ne_zero (by positivity) hm) (mul_ne_zero ha hb)
  · ext k
    rw [coeff_C_mul_X_pow]
    split_ifs with hk
    · rw [hk]
    · rcases Nat.lt_or_gt_of_ne hk with hlt | hgt
      · exact (X_pow_dvd_iff.mp hdvd) k hlt
      · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hgt)

end DT

-- size
section SZ

lemma SZ_abs_cf_le (ν : ℚ) (hν : |ν| ≤ 1) (m k : ℕ) (hk : k ≤ m) :
    |cf ν m k| ≤ ((m + 1).choose k : ℚ) * (4 : ℚ) ^ m := by
  have hprod : ∏ j ∈ Finset.range k, |(m : ℚ) + ν - (j : ℚ)|
      ≤ (((m + 1).descFactorial k : ℕ) : ℚ) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
    intro j hj
    have hjm : j + 1 ≤ m := by
      have := Finset.mem_range.mp hj
      omega
    rw [Nat.cast_sub (by omega)]
    have h1 : (j : ℚ) + 1 ≤ m := by exact_mod_cast hjm
    have h2 := abs_le.mp hν
    rw [abs_of_nonneg (by linarith)]
    push_cast
    linarith
  have hdf : (((m + 1).descFactorial k : ℕ) : ℚ)
      = (k.factorial : ℚ) * ((m + 1).choose k : ℚ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  have hch : (((2 * m - k).choose m : ℕ) : ℚ) ≤ 4 ^ m := by
    have : (2 * m - k).choose m ≤ 4 ^ m :=
      (Nat.choose_le_choose m (Nat.sub_le _ _)).trans
        ((Nat.choose_le_centralBinom m m).trans (Nat.centralBinom_le_four_pow m))
    exact_mod_cast this
  have hkf : (0 : ℚ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  unfold cf
  rw [abs_mul, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    Finset.abs_prod, Nat.abs_cast, Nat.abs_cast]
  calc (∏ j ∈ Finset.range k, |(m : ℚ) + ν - (j : ℚ)|) / (k.factorial : ℚ)
        * (((2 * m - k).choose m : ℕ) : ℚ)
      ≤ ((k.factorial : ℚ) * ((m + 1).choose k : ℚ)) / (k.factorial : ℚ) * 4 ^ m := by
        rw [← hdf]
        gcongr
    _ = ((m + 1).choose k : ℚ) * (4 : ℚ) ^ m := by
        field_simp

lemma size (ν : ℚ) (hν : |ν| ≤ 1) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), |cf ν m k| ≤ (16 : ℚ) ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [cf]
  calc ∑ k ∈ Finset.range (m + 1), |cf ν m k|
      ≤ ∑ k ∈ Finset.range (m + 1), ((m + 1).choose k : ℚ) * (4 : ℚ) ^ m :=
        Finset.sum_le_sum (fun k hk =>
          SZ_abs_cf_le ν hν m k (by have := Finset.mem_range.mp hk; omega))
    _ ≤ ∑ k ∈ Finset.range (m + 1 + 1), ((m + 1).choose k : ℚ) * (4 : ℚ) ^ m :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun _ _ _ => by positivity)
    _ = (2 : ℚ) ^ (m + 1) * (4 : ℚ) ^ m := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose (m + 1)
    _ ≤ (16 : ℚ) ^ m := by
        have h2 : (2 : ℚ) ≤ 2 ^ m := by
          calc (2 : ℚ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
        have h16 : (16 : ℚ) ^ m = 2 ^ m * (2 ^ m * 4 ^ m) := by
          rw [← mul_pow, ← mul_pow]; norm_num
        rw [h16, pow_succ]
        have : (0 : ℚ) ≤ 2 ^ m * 4 ^ m := by positivity
        nlinarith

end SZ

-- gb
section GB

/-- A product of `k` consecutive integers is divisible by `k!`. -/
lemma GB_fact_dvd_prod (t : ℤ) (k : ℕ) :
    ((k.factorial : ℕ) : ℤ) ∣ ∏ j ∈ Finset.range k, (t - (j : ℤ)) := by
  rw [← descPochhammer_eval_eq_prod_range, eval_eq_smeval,
    Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]
  exact Dvd.intro _ rfl

lemma gb (n : ℕ) (hn : n.Prime) (a : ℤ) (k : ℕ) :
    ((k.factorial : ℕ) : ℤ) ∣ (n : ℤ) ^ k * ∏ j ∈ Finset.range k, (a - (j : ℤ) * (n : ℤ)) := by
  obtain ⟨s, r, hnr, hk⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero k) n hn.one_lt.ne'
  have hs : s ≤ k := by
    have : Fact n.Prime := ⟨hn⟩
    have h1 : n ^ s ∣ k.factorial := hk ▸ Dvd.intro r rfl
    exact ((padicValNat_dvd_iff_le (Nat.factorial_ne_zero k)).mp h1).trans
      (padicValNat_factorial_le (p := n) k)
  have hcop : Nat.Coprime n r := (Nat.Prime.coprime_iff_not_dvd hn).mpr hnr
  have hrk : (r : ℤ) ∣ ((k.factorial : ℕ) : ℤ) := by
    rw [hk]; exact Int.natCast_dvd_natCast.mpr (Dvd.intro_left _ rfl)
  have hr : (r : ℤ) ∣ ∏ j ∈ Finset.range k, (a - (j : ℤ) * (n : ℤ)) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    obtain ⟨t, ht⟩ := ZMod.intCast_surjective
      ((((ZMod.unitOfCoprime n hcop)⁻¹ : (ZMod r)ˣ) : ZMod r) * (a : ZMod r))
    have ha : (a : ZMod r) = (n : ZMod r) * (t : ZMod r) := by
      rw [ht, ← mul_assoc, ← ZMod.coe_unitOfCoprime n hcop, Units.mul_inv, one_mul]
    have h0 : ((∏ j ∈ Finset.range k, (t - (j : ℤ)) : ℤ) : ZMod r) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hrk.trans (GB_fact_dvd_prod t k))
    push_cast at h0 ⊢
    rw [ha]
    have : ∀ j ∈ Finset.range k, (n : ZMod r) * (t : ZMod r) - (j : ZMod r) * (n : ZMod r)
        = (n : ZMod r) * ((t : ZMod r) - (j : ZMod r)) := fun j _ => by ring
    rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, h0, mul_zero]
  have hcopz : IsCoprime ((n : ℤ) ^ s) (r : ℤ) := by
    have := Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left s hcop)
    simpa using this
  rw [hk]
  push_cast
  exact hcopz.mul_dvd (dvd_mul_of_dvd_left (pow_dvd_pow _ hs) _) (dvd_mul_of_dvd_right hr _)

end GB

-- pkg
section PK

/-- `n^(2m) * cf ν m k` is an integer when `n ν` is an integer, `n` prime, `k ≤ m`. -/
lemma PK_int (n : ℕ) (hn : n.Prime) (ν : ℚ) (s : ℤ) (hs : (n : ℚ) * ν = s) (m k : ℕ)
    (hk : k ≤ m) : ∃ z : ℤ, (z : ℚ) = (n : ℚ) ^ (2 * m) * cf ν m k := by
  obtain ⟨t, ht⟩ := gb n hn ((m : ℤ) * n + s) k
  refine ⟨(-1) ^ k * (n : ℤ) ^ (2 * m - 2 * k) * t * (((2 * m - k).choose m : ℕ) : ℤ), ?_⟩
  have hf : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have ht' : (n : ℚ) ^ k * ∏ j ∈ Finset.range k, (((m : ℚ) * n + s) - (j : ℚ) * n)
      = (k.factorial : ℚ) * t := by
    have := congrArg (fun z : ℤ => (z : ℚ)) ht
    push_cast at this
    exact this
  have hprod : ∏ j ∈ Finset.range k, (((m : ℚ) * n + s) - (j : ℚ) * n)
      = (n : ℚ) ^ k * ∏ j ∈ Finset.range k, ((m : ℚ) + ν - (j : ℚ)) := by
    rw [← Finset.card_range k, ← Finset.prod_const, Finset.card_range, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← hs]; ring
  have htq : (t : ℚ) = (n : ℚ) ^ k * (n : ℚ) ^ k
      * (∏ j ∈ Finset.range k, ((m : ℚ) + ν - (j : ℚ))) / (k.factorial : ℚ) := by
    rw [eq_div_iff hf, mul_assoc, ← hprod, ht']; ring
  have hpow : (n : ℚ) ^ (2 * m) = (n : ℚ) ^ (2 * m - 2 * k) * (n : ℚ) ^ k * (n : ℚ) ^ k := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  rw [cf, hpow]
  push_cast
  rw [htq]
  ring

/-- The integer polynomial `∑_{k ≤ m} n^(2m) cf ν m k X^k` (via `Int.floor`). -/
noncomputable def PK_poly (n : ℕ) (ν : ℚ) (m : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.range (m + 1), C ⌊(n : ℚ) ^ (2 * m) * cf ν m k⌋ * X ^ k

lemma PK_coeff (n : ℕ) (ν : ℚ) (m k : ℕ) :
    (PK_poly n ν m).coeff k = if k ∈ Finset.range (m + 1) then ⌊(n : ℚ) ^ (2 * m) * cf ν m k⌋
      else 0 := by
  simp only [PK_poly, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]

lemma PK_deg (n : ℕ) (ν : ℚ) (m : ℕ) : (PK_poly n ν m).natDegree ≤ m :=
  natDegree_sum_le_of_forall_le _ _ fun _k hk =>
    (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))

lemma PK_map (n : ℕ) (ν : ℚ) (m : ℕ)
    (hint : ∀ k, k ≤ m → ∃ z : ℤ, (z : ℚ) = (n : ℚ) ^ (2 * m) * cf ν m k) :
    (PK_poly n ν m).map (Int.castRingHom ℚ) = C ((n : ℚ) ^ (2 * m)) * F ν m := by
  simp only [PK_poly, F, Polynomial.map_sum, Polynomial.map_mul, map_C, Polynomial.map_pow,
    map_X, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨z, hz⟩ := hint k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  rw [← mul_assoc, ← C_mul, ← hz, Int.floor_intCast, eq_intCast]

lemma PK_dvd (p : ℤ[X]) (M : ℕ) (h : (X : ℚ[X]) ^ M ∣ p.map (Int.castRingHom ℚ)) :
    (X : ℤ[X]) ^ M ∣ p := by
  rw [X_pow_dvd_iff] at h ⊢
  intro d hd
  have := h d hd
  rw [coeff_map, eq_intCast] at this
  exact_mod_cast this

lemma PK_coeff_zero (n : ℕ) (ν : ℚ) (m : ℕ) :
    (PK_poly n ν m).coeff 0 = ((n ^ (2 * m) * (2 * m).choose m : ℕ) : ℤ) := by
  rw [PK_coeff, if_pos (Finset.mem_range.mpr (Nat.succ_pos m))]
  have : (n : ℚ) ^ (2 * m) * cf ν m 0 = (((n ^ (2 * m) * (2 * m).choose m : ℕ) : ℤ) : ℚ) := by
    simp [cf]
  rw [this, Int.floor_intCast]

lemma PK_size (n : ℕ) (ν : ℚ) (hν : |ν| ≤ 1) (m : ℕ)
    (hint : ∀ k, k ≤ m → ∃ z : ℤ, (z : ℚ) = (n : ℚ) ^ (2 * m) * cf ν m k) :
    ∑ k ∈ Finset.range (m + 1), |(PK_poly n ν m).coeff k| ≤ ((16 * n ^ 2 : ℕ) : ℤ) ^ m := by
  have hsum : ((∑ k ∈ Finset.range (m + 1), |(PK_poly n ν m).coeff k| : ℤ) : ℚ)
      = (n : ℚ) ^ (2 * m) * ∑ k ∈ Finset.range (m + 1), |cf ν m k| := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [PK_coeff, if_pos hk]
    obtain ⟨z, hz⟩ := hint k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    rw [← hz, Int.floor_intCast, hz, abs_mul, abs_of_nonneg (by positivity)]
  suffices h : ((∑ k ∈ Finset.range (m + 1), |(PK_poly n ν m).coeff k| : ℤ) : ℚ)
      ≤ (((16 * n ^ 2 : ℕ) : ℤ) ^ m : ℤ) by exact_mod_cast h
  rw [hsum]
  push_cast
  rw [mul_pow, ← pow_mul, mul_comm ((16 : ℚ) ^ m), mul_comm 2 m]
  exact mul_le_mul_of_nonneg_left (size ν hν m) (by positivity)

lemma pkg (n : ℕ) (hn : n.Prime) : ∃ (K : ℕ) (P Q : ℕ → ℤ[X]), PadeSys n K P Q := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne_zero
  have hn1 : (1 : ℚ) ≤ n := by exact_mod_cast hn.one_lt.le
  have hsP : (n : ℚ) * (1 / (n : ℚ)) = ((1 : ℤ) : ℚ) := by field_simp; simp
  have hsQ : (n : ℚ) * (-(1 / (n : ℚ))) = ((-1 : ℤ) : ℚ) := by field_simp; simp
  have hνP : |1 / (n : ℚ)| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]; exact (div_le_one (by positivity)).mpr hn1
  have hνQ : |-(1 / (n : ℚ))| ≤ 1 := by rw [abs_neg]; exact hνP
  have intP : ∀ m k, k ≤ m → ∃ z : ℤ, (z : ℚ) = (n : ℚ) ^ (2 * m) * cf (1 / (n : ℚ)) m k :=
    fun m k hk => PK_int n hn _ _ hsP m k hk
  have intQ : ∀ m k, k ≤ m → ∃ z : ℤ, (z : ℚ) = (n : ℚ) ^ (2 * m) * cf (-(1 / (n : ℚ))) m k :=
    fun m k hk => PK_int n hn _ _ hsQ m k hk
  have mapP := fun m => PK_map n _ m (intP m)
  have mapQ := fun m => PK_map n _ m (intQ m)
  refine ⟨16 * n ^ 2, PK_poly n (1 / (n : ℚ)), PK_poly n (-(1 / (n : ℚ))), ?_⟩
  refine
    { one_le := ?_
      degP := fun m => PK_deg n _ m
      degQ := fun m => PK_deg n _ m
      coeff_zero_eq := fun m => by rw [PK_coeff_zero, PK_coeff_zero]
      coeff_zero_ne := fun m => ?_
      pade := fun m => ?_
      det := fun m => ?_
      sizeP := fun m => PK_size n _ hνP m (intP m)
      sizeQ := fun m => PK_size n _ hνQ m (intQ m) }
  · have := hn.one_lt
    nlinarith
  · rw [PK_coeff_zero]
    exact_mod_cast mul_ne_zero (pow_ne_zero _ hn.ne_zero) (Nat.choose_pos (by omega)).ne'
  · apply PK_dvd
    have e : ((PK_poly n (1 / (n : ℚ)) m) ^ n - (1 - X) * (PK_poly n (-(1 / (n : ℚ))) m) ^ n).map
        (Int.castRingHom ℚ) = C ((n : ℚ) ^ (2 * m)) ^ n *
          (F (1 / (n : ℚ)) m ^ n - (1 - X) * F (-(1 / (n : ℚ))) m ^ n) := by
      simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_one,
        map_X, mapP, mapQ]
      ring
    rw [e]
    exact Dvd.dvd.mul_left (pade n m hn.pos) _
  · obtain ⟨d, hd, hdq⟩ := det n m hn.two_le
    set a : ℚ := (n : ℚ) ^ (2 * m)
    set b : ℚ := (n : ℚ) ^ (2 * (m + 1))
    have hD : (PK_poly n (1 / (n : ℚ)) m * PK_poly n (-(1 / (n : ℚ))) (m + 1)
        - PK_poly n (1 / (n : ℚ)) (m + 1) * PK_poly n (-(1 / (n : ℚ))) m).map
          (Int.castRingHom ℚ) = C (a * b * d) * X ^ (2 * m + 1) := by
      simp only [Polynomial.map_sub, Polynomial.map_mul, mapP, mapQ]
      rw [C_mul, C_mul]
      linear_combination (C a * C b) * hdq
    have hab : a * b * d ≠ 0 := mul_ne_zero (mul_ne_zero (pow_ne_zero _ hn0) (pow_ne_zero _ hn0)) hd
    set D := PK_poly n (1 / (n : ℚ)) m * PK_poly n (-(1 / (n : ℚ))) (m + 1)
        - PK_poly n (1 / (n : ℚ)) (m + 1) * PK_poly n (-(1 / (n : ℚ))) m with hDdef
    have hc : ((D.coeff (2 * m + 1) : ℤ) : ℚ) = a * b * d := by
      have := congrArg (fun p : ℚ[X] => p.coeff (2 * m + 1)) hD
      simp only [coeff_map, eq_intCast, coeff_C_mul_X_pow] at this
      exact this
    refine ⟨D.coeff (2 * m + 1), ?_, ?_⟩
    · intro h0
      rw [h0, Int.cast_zero] at hc
      exact hab hc.symm
    · apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
      rw [hD, Polynomial.map_mul, map_C, Polynomial.map_pow, map_X, eq_intCast, hc]

end PK

-- ### Part B: two solutions

-- lin
section LN

/-- First-order binomial expansion: `(x + y)^(n+1) = x^(n+1) + (n+1) x^n y` modulo `y^2`. -/
lemma LN_binom {A : Type*} [CommRing A] (x y : A) (n : ℕ) :
    ∃ z : A, (x + y) ^ (n + 1) = x ^ (n + 1) + ((n : A) + 1) * x ^ n * y + y ^ 2 * z := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨x * z + ((n : A) + 1) * x ^ n + y * z, ?_⟩
    rw [pow_succ, hz]
    push_cast
    ring

/-- Part (a): an integer polynomial `R` with `R(0) = n^e` and `R^n ≡ n^(n e) (1 - X)` modulo
`X^(M+1)`, by Hensel-style induction on `M`. -/
lemma LN_root (n : ℕ) (hn : 0 < n) (M : ℕ) :
    ∃ (e : ℕ) (R : ℤ[X]), R.coeff 0 = (n : ℤ) ^ e ∧
      (X : ℤ[X]) ^ (M + 1) ∣ R ^ n - C ((n : ℤ) ^ (n * e)) * (1 - X) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  induction M with
  | zero => exact ⟨0, 1, by simp, by simp⟩
  | succ M ih =>
    obtain ⟨e, R, hR0, G, hG⟩ := ih
    rw [coeff_zero_eq_eval_zero] at hR0
    rw [map_pow] at hG
    obtain ⟨z, hz⟩ := LN_binom (C (((n' + 1 : ℕ) : ℤ)) ^ (1 + e * n') * R)
      (-(C (G.coeff 0) * X ^ (M + 1))) n'
    have hcast : ((n' : ℤ[X]) + 1) = C (((n' + 1 : ℕ) : ℤ)) := by
      simp
    have key : (C (((n' + 1 : ℕ) : ℤ)) ^ (1 + e * n') * R - C (G.coeff 0) * X ^ (M + 1)) ^ (n' + 1)
        - C (((n' + 1 : ℕ) : ℤ)) ^ ((n' + 1) * (e + (1 + e * n'))) * (1 - X)
        = X ^ (M + 1) * (C (((n' + 1 : ℕ) : ℤ)) ^ ((1 + e * n') * (n' + 1)) * G
            - C (((n' + 1 : ℕ) : ℤ)) * C (((n' + 1 : ℕ) : ℤ)) ^ ((1 + e * n') * n')
              * C (G.coeff 0) * R ^ n')
          + X ^ (2 * (M + 1)) * (C (G.coeff 0) ^ 2 * z) := by
      rw [sub_eq_add_neg (C (((n' + 1 : ℕ) : ℤ)) ^ (1 + e * n') * R), hz, hcast]
      linear_combination (C (((n' + 1 : ℕ) : ℤ)) ^ ((1 + e * n') * (n' + 1))) * hG
    refine ⟨e + (1 + e * n'),
      C (((n' + 1 : ℕ) : ℤ)) ^ (1 + e * n') * R - C (G.coeff 0) * X ^ (M + 1), ?_, ?_⟩
    · rw [coeff_zero_eq_eval_zero]
      simp only [eval_sub, eval_mul, eval_pow, eval_C, eval_X, hR0]
      rw [zero_pow (Nat.succ_ne_zero M)]
      ring
    · rw [map_pow, key]
      refine dvd_add ?_ (dvd_mul_of_dvd_left (pow_dvd_pow X (by omega)) _)
      rw [pow_succ X (M + 1)]
      refine mul_dvd_mul_left _ ?_
      rw [X_dvd_iff, coeff_zero_eq_eval_zero]
      simp only [eval_sub, eval_mul, eval_pow, eval_C, hR0]
      rw [← coeff_zero_eq_eval_zero]
      ring

lemma lin (n : ℕ) (hn : 0 < n) (P Q : ℤ[X]) (M : ℕ)
    (h0 : P.coeff 0 = Q.coeff 0) (h0' : P.coeff 0 ≠ 0)
    (hpade : (X : ℤ[X]) ^ M ∣ P ^ n - (1 - X) * Q ^ n) :
    ∃ (e : ℕ) (R : ℤ[X]), R.coeff 0 = (n : ℤ) ^ e ∧
      (X : ℤ[X]) ^ M ∣ R ^ n - C ((n : ℤ) ^ (n * e)) * (1 - X) ∧
      (X : ℤ[X]) ^ M ∣ C ((n : ℤ) ^ e) * P - R * Q := by
  obtain ⟨e, R, hR0, hR⟩ := LN_root n hn M
  have hR' : (X : ℤ[X]) ^ M ∣ R ^ n - C ((n : ℤ) ^ (n * e)) * (1 - X) :=
    dvd_trans (pow_dvd_pow X (Nat.le_succ M)) hR
  refine ⟨e, R, hR0, hR', ?_⟩
  have hfac := (Commute.all (C ((n : ℤ) ^ e) * P) (R * Q)).mul_geom_sum₂ n
  have hdiff : (C ((n : ℤ) ^ e) * P) ^ n - (R * Q) ^ n
      = C ((n : ℤ) ^ (n * e)) * (P ^ n - (1 - X) * Q ^ n)
        - (R ^ n - C ((n : ℤ) ^ (n * e)) * (1 - X)) * Q ^ n := by
    simp only [map_pow]
    ring
  have hdvd : (X : ℤ[X]) ^ M ∣ (C ((n : ℤ) ^ e) * P - R * Q)
      * ∑ i ∈ Finset.range n, (C ((n : ℤ) ^ e) * P) ^ i * (R * Q) ^ (n - 1 - i) := by
    rw [hfac, hdiff]
    exact dvd_sub (dvd_mul_of_dvd_right hpade _) (dvd_mul_of_dvd_left hR' _)
  refine Prime.pow_dvd_of_dvd_mul_right prime_X M ?_ hdvd
  rw [X_dvd_iff, coeff_zero_eq_eval_zero, eval_finsetSum]
  have hQ0 : eval 0 Q = eval 0 P := by
    rw [← coeff_zero_eq_eval_zero, ← coeff_zero_eq_eval_zero, h0]
  rw [coeff_zero_eq_eval_zero] at hR0 h0'
  have hterm : ∀ i ∈ Finset.range n,
      eval 0 ((C ((n : ℤ) ^ e) * P) ^ i * (R * Q) ^ (n - 1 - i))
        = ((n : ℤ) ^ e * eval 0 P) ^ (n - 1) := by
    intro i hi
    have hi' : i + (n - 1 - i) = n - 1 := by
      have := Finset.mem_range.mp hi
      omega
    simp only [eval_mul, eval_pow, eval_C, hR0, hQ0]
    rw [← pow_add, hi']
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact mul_ne_zero (by exact_mod_cast hn.ne')
    (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hn.ne')) h0'))

end LN

-- div
section DV

/-- Uniqueness of `n`-th roots near a unit: in a commutative ring where `n` is a unit, if
`s^n = t^n`, `t` is a unit and `s - t` is nilpotent, then `s = t`. -/
lemma DV_root {A : Type*} [CommRing A] (n : ℕ) (s t : A) (hst : s ^ n = t ^ n)
    (ht : IsUnit t) (hn : IsUnit (n : A)) (hd : IsNilpotent (s - t)) : s = t := by
  obtain ⟨k, hk⟩ := Polynomial.powAddExpansion t (s - t) n
  have h1 : (s - t) * ((n : A) * t ^ (n - 1) + k * (s - t)) = 0 := by
    have hs : t + (s - t) = s := by ring
    rw [hs, hst] at hk
    linear_combination -hk
  have hu : IsUnit ((n : A) * t ^ (n - 1) + k * (s - t)) := by
    have h2 : IsUnit ((n : A) * t ^ (n - 1)) := hn.mul (ht.pow _)
    have h3 : IsNilpotent (k * (s - t)) := (Commute.all k (s - t)).isNilpotent_mul_left hd
    exact IsNilpotent.isUnit_add_left_of_commute h3 h2 (Commute.all _ _)
  exact sub_eq_zero.mp ((hu.mul_left_eq_zero).mp h1)

/-- A multiple of `X^M` evaluates to `0` at a point `x` with `x^M = 0`. -/
lemma DV_eval_zero {A : Type*} [CommRing A] (x : A) (M : ℕ) (hx : x ^ M = 0) (G : ℤ[X])
    (hG : (X : ℤ[X]) ^ M ∣ G) : eval₂ (Int.castRingHom A) x G = 0 := by
  obtain ⟨H, rfl⟩ := hG
  rw [eval₂_mul, eval₂_pow, eval₂_X, hx, zero_mul]

/-- `hom m P c b = b^m * P(c / b)` in a commutative ring where `b` has the inverse `β`. -/
lemma DV_hom {A : Type*} [CommRing A] (m : ℕ) (P : ℤ[X]) (hP : P.natDegree ≤ m) (c b : ℤ)
    (β : A) (hβ : (b : A) * β = 1) :
    ((hom m P c b : ℤ) : A)
      = (b : A) ^ m * eval₂ (Int.castRingHom A) ((c : A) * β) P := by
  rw [eval₂_eq_sum_range' (Int.castRingHom A) (Nat.lt_succ_of_le hP), hom, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hpow : (b : A) ^ m = (b : A) ^ (m - k) * (b : A) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk']
  have h1 : (b : A) ^ k * β ^ k = 1 := by rw [← mul_pow, hβ, one_pow]
  rw [hpow, mul_pow, eq_intCast]
  linear_combination ((P.coeff k : A) * (c : A) ^ k * (b : A) ^ (m - k)) * (-h1)

/-- An integer prime to `p` is invertible modulo `p^E`. -/
lemma DV_inv (p : ℕ) (hp : p.Prime) (E : ℕ) (b : ℤ) (hb : ¬ (p : ℤ) ∣ b) :
    ∃ β : ZMod (p ^ E), ((b : ℤ) : ZMod (p ^ E)) * β = 1 := by
  have hc : IsCoprime ((p : ℤ) ^ E) b :=
    ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr hb).pow_left
  obtain ⟨s, t, hst⟩ := hc
  refine ⟨(t : ZMod (p ^ E)), ?_⟩
  have h := congrArg (fun z : ℤ => (z : ZMod (p ^ E))) hst
  simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_one] at h
  have hz : ((p : ZMod (p ^ E))) ^ E = 0 := by
    rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  rw [hz, mul_zero, zero_add] at h
  rw [mul_comm]; exact h

/-- LEMMA `div`. For primes `p ≠ n`: if `p^E` divides `(a + b)^M` and `b u^n + a w^n`, with
`p ∤ b`, `p ∤ w`, `u ≡ w` modulo `p`, then `p^E` divides
`w * hom m P (a + b) b - u * hom m Q (a + b) b`. Proof in `ZMod (p^E)` at `x = (a + b) / b`:
with `(e, R)` from `lin`, `R(x) w` and `n^e u` have the same `n`-th power and differ by a
nilpotent element, so they are equal (`DV_root`); then `n^e P(x) = R(x) Q(x)` gives the claim. -/
lemma div (n p : ℕ) (hn : n.Prime) (hp : p.Prime) (hpn : p ≠ n) (m M : ℕ) (P Q : ℤ[X])
    (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ m)
    (h0 : P.coeff 0 = Q.coeff 0) (h0' : P.coeff 0 ≠ 0)
    (hpade : (X : ℤ[X]) ^ M ∣ P ^ n - (1 - X) * Q ^ n)
    (a b u w : ℤ) (E : ℕ) (hb : ¬ (p : ℤ) ∣ b) (hw : ¬ (p : ℤ) ∣ w) (huw : (p : ℤ) ∣ u - w)
    (h1 : (p : ℤ) ^ E ∣ (a + b) ^ M) (h2 : (p : ℤ) ^ E ∣ b * u ^ n + a * w ^ n) :
    (p : ℤ) ^ E ∣ w * hom m P (a + b) b - u * hom m Q (a + b) b := by
  -- the criterion for divisibility by `p^E`
  have hcrit : ∀ z : ℤ, (p : ℤ) ^ E ∣ z ↔ ((z : ℤ) : ZMod (p ^ E)) = 0 := by
    intro z
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow]
  rw [hcrit]
  have hpz : ((p : ZMod (p ^ E))) ^ E = 0 := by
    rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  -- units
  have hu : ¬ (p : ℤ) ∣ u := fun h => hw (by simpa using dvd_sub h huw)
  have hnp : ¬ (p : ℤ) ∣ (n : ℤ) := by
    intro h
    exact hpn ((Nat.prime_dvd_prime_iff_eq hp hn).mp (Int.natCast_dvd_natCast.mp h))
  obtain ⟨β, hβ⟩ := DV_inv p hp E b hb
  obtain ⟨υ, hυ⟩ := DV_inv p hp E u hu
  obtain ⟨ν, hν⟩ := DV_inv p hp E (n : ℤ) hnp
  rw [Int.cast_natCast] at hν
  have hnU : IsUnit ((n : ℕ) : ZMod (p ^ E)) := isUnit_iff_exists_inv.mpr ⟨ν, hν⟩
  have huU : IsUnit ((u : ℤ) : ZMod (p ^ E)) := isUnit_iff_exists_inv.mpr ⟨υ, hυ⟩
  -- the point `x = (a + b) / b`
  set x : ZMod (p ^ E) := ((a + b : ℤ) : ZMod (p ^ E)) * β with hx
  have hxM : x ^ M = 0 := by
    have h := (hcrit _).mp h1
    rw [Int.cast_pow] at h
    rw [hx, mul_pow, h, zero_mul]
  have h2' : (b : ZMod (p ^ E)) * (u : ZMod (p ^ E)) ^ n
      + (a : ZMod (p ^ E)) * (w : ZMod (p ^ E)) ^ n = 0 := by
    have h := (hcrit _).mp h2
    push_cast at h
    exact h
  have hx1 : (1 - x) * (w : ZMod (p ^ E)) ^ n = (u : ZMod (p ^ E)) ^ n := by
    rw [hx]; push_cast
    linear_combination (-β) * h2' - ((w : ZMod (p ^ E)) ^ n - (u : ZMod (p ^ E)) ^ n) * hβ
  -- the linearized Pade congruence
  obtain ⟨e, R, hR0, hRn, hRP⟩ := lin n hn.pos P Q M h0 h0' hpade
  have hRn' := DV_eval_zero x M hxM _ hRn
  have hRP' := DV_eval_zero x M hxM _ hRP
  simp only [eval₂_sub, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X, eval₂_one] at hRn' hRP'
  simp only [eq_intCast, Int.cast_pow, Int.cast_natCast] at hRn' hRP'
  set ρ : ZMod (p ^ E) := eval₂ (Int.castRingHom (ZMod (p ^ E))) x R with hρ
  set Px : ZMod (p ^ E) := eval₂ (Int.castRingHom (ZMod (p ^ E))) x P with hPx
  set Qx : ZMod (p ^ E) := eval₂ (Int.castRingHom (ZMod (p ^ E))) x Q with hQx
  set N : ZMod (p ^ E) := (n : ZMod (p ^ E)) ^ e with hN
  have hNU : IsUnit N := hnU.pow e
  -- `ρ - N` is a multiple of `x`
  have hρN : ∃ g : ZMod (p ^ E), ρ - N = x * g := by
    obtain ⟨G, hG⟩ := X_dvd_sub_C (p := R)
    refine ⟨eval₂ (Int.castRingHom (ZMod (p ^ E))) x G, ?_⟩
    have h := congrArg (eval₂ (Int.castRingHom (ZMod (p ^ E))) x) hG
    rw [hR0, eval₂_sub, eval₂_mul, eval₂_C, eval₂_X, eq_intCast, Int.cast_pow,
      Int.cast_natCast] at h
    exact h
  obtain ⟨g, hg⟩ := hρN
  have hxnil : IsNilpotent x := ⟨M, hxM⟩
  have hpnil : IsNilpotent ((p : ZMod (p ^ E))) := ⟨E, hpz⟩
  -- the two `n`-th roots agree
  have hkey : ρ * (w : ZMod (p ^ E)) = N * (u : ZMod (p ^ E)) := by
    apply DV_root n _ _ _ (hNU.mul huU) hnU
    · obtain ⟨d, hd⟩ := huw
      have hd' : (u : ZMod (p ^ E))
          = (w : ZMod (p ^ E)) + (p : ZMod (p ^ E)) * (d : ZMod (p ^ E)) := by
        have h := congrArg (fun z : ℤ => (z : ZMod (p ^ E))) hd
        simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] at h
        linear_combination h
      have e1 : ρ * (w : ZMod (p ^ E)) - N * (u : ZMod (p ^ E))
          = x * (g * (w : ZMod (p ^ E))) + (p : ZMod (p ^ E)) * (-(N * (d : ZMod (p ^ E)))) := by
        rw [hd']; linear_combination (w : ZMod (p ^ E)) * hg
      rw [e1]
      exact (Commute.all _ _).isNilpotent_add
        ((Commute.all _ _).isNilpotent_mul_right hxnil)
        ((Commute.all _ _).isNilpotent_mul_right hpnil)
    · rw [mul_pow, mul_pow, ← hx1, hN, ← pow_mul, mul_comm e n]
      linear_combination ((w : ZMod (p ^ E)) ^ n) * hRn'
  -- conclusion at `x`
  have hfin : (w : ZMod (p ^ E)) * Px - (u : ZMod (p ^ E)) * Qx = 0 := by
    have h : N * ((w : ZMod (p ^ E)) * Px - (u : ZMod (p ^ E)) * Qx) = 0 := by
      linear_combination (w : ZMod (p ^ E)) * hRP' + Qx * hkey
    exact (hNU.mul_right_eq_zero).mp h
  push_cast
  rw [DV_hom m P hP (a + b) b β hβ, DV_hom m Q hQ (a + b) b β hβ]
  rw [← hx, ← hPx, ← hQx]
  linear_combination ((b : ZMod (p ^ E)) ^ m) * hfin

end DV

/-- PROVED (kept by the lead). For `b ≠ 0` and `natDegree P ≤ m`, over `ℚ`:
`hom m P c b = b^m * P(c / b)`. Free to use in `div` and `pair` (in `ZMod (p^E)` the same
computation works with `b` a unit). -/
lemma hom_cast (m : ℕ) (P : ℤ[X]) (hP : P.natDegree ≤ m) (c b : ℤ) (hb : b ≠ 0) :
    ((hom m P c b : ℤ) : ℚ) = (b : ℚ) ^ m * eval ((c : ℚ) / b) (P.map (Int.castRingHom ℚ)) := by
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have hdeg : (P.map (Int.castRingHom ℚ)).natDegree < m + 1 :=
    lt_of_le_of_lt (natDegree_map_le) (Nat.lt_succ_of_le hP)
  rw [eval_eq_sum_range' hdeg, hom, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hpow : (b : ℚ) ^ m = (b : ℚ) ^ (m - k) * (b : ℚ) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk']
  rw [coeff_map, div_pow, hpow]
  simp only [eq_intCast]
  field_simp

/-- PROVED (kept by the lead): `nv`. Non-vanishing: if `P Q' - P' Q = d X^(2m+1)` with `d ≠ 0`
(degrees at most `m`, `m`, `m+1`, `m+1`), then for `c ≠ 0`, `b ≠ 0` and `(u, w) ≠ (0, 0)` the two
linear forms `w hom(P) - u hom(Q)` (degree `m`) and `w hom(P') - u hom(Q')` (degree `m+1`) at
`(c, b)` are not both zero.

Proof: evaluating the determinant identity at `c / b` and multiplying by `b^(2m+1)` gives
`hom m P c b * hom (m+1) Q' c b - hom (m+1) P' c b * hom m Q c b = d c^(2m+1) ≠ 0`; if both forms
vanished, `u` and `w` would both annihilate this number.
Tested: 3,000 random cases with the true Pade pairs (`n ≤ 7`, `m ≤ 5`, all signs). -/
lemma nv (m : ℕ) (P Q P' Q' : ℤ[X]) (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ m)
    (hP' : P'.natDegree ≤ m + 1) (hQ' : Q'.natDegree ≤ m + 1) (d : ℤ) (hd : d ≠ 0)
    (hdet : P * Q' - P' * Q = C d * X ^ (2 * m + 1))
    (c b u w : ℤ) (hc : c ≠ 0) (hb : b ≠ 0) (huw : u ≠ 0 ∨ w ≠ 0) :
    w * hom m P c b - u * hom m Q c b ≠ 0 ∨
      w * hom (m + 1) P' c b - u * hom (m + 1) Q' c b ≠ 0 := by
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have key : hom m P c b * hom (m + 1) Q' c b - hom (m + 1) P' c b * hom m Q c b
      = d * c ^ (2 * m + 1) := by
    have h := congrArg (fun p : ℤ[X] => eval ((c : ℚ) / b) (p.map (Int.castRingHom ℚ))) hdet
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_X,
      Polynomial.map_intCast, eval_sub, eval_mul, eval_pow, eval_intCast, eval_X,
      eq_intCast] at h
    have : ((hom m P c b * hom (m + 1) Q' c b - hom (m + 1) P' c b * hom m Q c b : ℤ) : ℚ)
        = ((d * c ^ (2 * m + 1) : ℤ) : ℚ) := by
      push_cast
      rw [hom_cast m P hP c b hb, hom_cast m Q hQ c b hb, hom_cast (m + 1) P' hP' c b hb,
        hom_cast (m + 1) Q' hQ' c b hb]
      have e : (d : ℚ) * (c : ℚ) ^ (2 * m + 1)
          = (b : ℚ) ^ m * (b : ℚ) ^ (m + 1) * ((d : ℚ) * ((c : ℚ) / b) ^ (2 * m + 1)) := by
        rw [div_pow, ← pow_add]
        have : m + (m + 1) = 2 * m + 1 := by ring
        rw [this]
        field_simp
      rw [e, ← h]
      ring
    exact_mod_cast this
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hne : d * c ^ (2 * m + 1) ≠ 0 := mul_ne_zero hd (pow_ne_zero _ hc)
  have hw : w * (d * c ^ (2 * m + 1)) = 0 := by
    rw [← key]; linear_combination (hom (m + 1) Q' c b) * h1 - (hom m Q c b) * h2
  have hu : u * (d * c ^ (2 * m + 1)) = 0 := by
    rw [← key]; linear_combination (hom (m + 1) P' c b) * h1 - (hom m P c b) * h2
  rcases huw with h | h
  · exact h ((mul_eq_zero.mp hu).resolve_right hne)
  · exact h ((mul_eq_zero.mp hw).resolve_right hne)

-- pair
section PR

lemma PR_hom_abs (j : ℕ) (P : ℤ[X]) (c b : ℤ) (hb : 0 ≤ b) (hbc : b ≤ c) :
    |hom j P c b| ≤ (∑ k ∈ Finset.range (j + 1), |P.coeff k|) * c ^ j := by
  have hc : 0 ≤ c := hb.trans hbc
  unfold hom
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hc k), abs_of_nonneg (pow_nonneg hb _),
    mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc c ^ k * b ^ (j - k) ≤ c ^ k * c ^ (j - k) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb hbc _) (pow_nonneg hc k)
    _ = c ^ j := by rw [← pow_add, Nat.add_sub_cancel' hk']

lemma PR_add_pow (u w N n : ℕ) (hu : u ^ n ≤ N) (hw : w ^ n ≤ N) :
    (u + w) ^ n ≤ 2 ^ n * N := by
  rcases le_total u w with h | h
  · calc (u + w) ^ n ≤ (2 * w) ^ n := Nat.pow_le_pow_left (by omega) n
      _ = 2 ^ n * w ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * N := Nat.mul_le_mul_left _ hw
  · calc (u + w) ^ n ≤ (2 * u) ^ n := Nat.pow_le_pow_left (by omega) n
      _ = 2 ^ n * u ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * N := Nat.mul_le_mul_left _ hu

/-- The linear form `L_j = w hom(P j) - u hom(Q j)` at `(c₁, b₁)` with `u = y₁ z₂`, `w = z₁ y₂`. -/
def PR_L (n : ℕ) (P Q : ℕ → ℤ[X]) (A B y₁ z₁ y₂ z₂ : ℕ) (j : ℕ) : ℤ :=
  ((z₁ : ℤ) * (y₂ : ℤ)) *
      hom j (P j) ((A : ℤ) * (y₁ : ℤ) ^ n + (B : ℤ) * (z₁ : ℤ) ^ n) ((B : ℤ) * (z₁ : ℤ) ^ n)
    - ((y₁ : ℤ) * (z₂ : ℤ)) *
      hom j (Q j) ((A : ℤ) * (y₁ : ℤ) ^ n + (B : ℤ) * (z₁ : ℤ) ^ n) ((B : ℤ) * (z₁ : ℤ) ^ n)

lemma PR_gcd_dvd (n K : ℕ) (P Q : ℕ → ℤ[X]) (hn : n.Prime) (hsys : PadeSys n K P Q)
    (A B y₁ z₁ y₂ z₂ : ℕ)
    (hcop₁ : (A * y₁ ^ n).Coprime (B * z₁ ^ n)) (hcop₂ : (A * y₂ ^ n).Coprime (B * z₂ ^ n))
    (hnc : ¬ n ∣ A * y₁ ^ n + B * z₁ ^ n)
    (hcong : ∀ p : ℕ, p.Prime → p ∣ A * y₁ ^ n + B * z₁ ^ n → p ∣ A * y₂ ^ n + B * z₂ ^ n →
      y₁ ≡ y₂ [MOD p] ∧ z₁ ≡ z₂ [MOD p])
    (j : ℕ) :
    Nat.gcd ((A * y₁ ^ n + B * z₁ ^ n) ^ (2 * j + 1)) (A * y₂ ^ n + B * z₂ ^ n) ∣
      (PR_L n P Q A B y₁ z₁ y₂ z₂ j).natAbs := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hpg := (dvd_pow_self p hk.ne').trans hpk
  have hpc1 : p ∣ A * y₁ ^ n + B * z₁ ^ n :=
    hp.dvd_of_dvd_pow (hpg.trans (Nat.gcd_dvd_left _ _))
  have hpc2 : p ∣ A * y₂ ^ n + B * z₂ ^ n := hpg.trans (Nat.gcd_dvd_right _ _)
  have hpn : p ≠ n := by rintro rfl; exact hnc hpc1
  have hpb1 : ¬ p ∣ B * z₁ ^ n := fun h => by
    have ha : p ∣ A * y₁ ^ n := (Nat.dvd_add_left h).mp hpc1
    have h1 := Nat.dvd_gcd ha h
    rw [Nat.Coprime.gcd_eq_one hcop₁] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hpz1 : ¬ p ∣ z₁ := fun h =>
    hpb1 (dvd_mul_of_dvd_right (dvd_pow h hn.ne_zero) _)
  have hpy2 : ¬ p ∣ y₂ := fun h => by
    have ha : p ∣ A * y₂ ^ n := dvd_mul_of_dvd_right (dvd_pow h hn.ne_zero) _
    have hb : p ∣ B * z₂ ^ n := (Nat.dvd_add_right ha).mp hpc2
    have h1 := Nat.dvd_gcd ha hb
    rw [Nat.Coprime.gcd_eq_one hcop₂] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hpw : ¬ p ∣ z₁ * y₂ := fun h => (hp.dvd_mul.mp h).elim hpz1 hpy2
  obtain ⟨hy, hz⟩ := hcong p hp hpc1 hpc2
  have hb' : ¬ (p : ℤ) ∣ (B : ℤ) * (z₁ : ℤ) ^ n := fun h => hpb1 (by exact_mod_cast h)
  have hw' : ¬ (p : ℤ) ∣ (z₁ : ℤ) * (y₂ : ℤ) := fun h => hpw (by exact_mod_cast h)
  have huw : (p : ℤ) ∣ (y₁ : ℤ) * (z₂ : ℤ) - (z₁ : ℤ) * (y₂ : ℤ) := by
    have h : z₁ * y₂ ≡ y₁ * z₂ [MOD p] := by
      have := hz.mul hy.symm
      rwa [mul_comm z₂ y₁] at this
    have h' := Int.modEq_iff_dvd.mp (Int.natCast_modEq_iff.mpr h)
    push_cast at h'
    exact h'
  have h1 : (p : ℤ) ^ k ∣
      ((A : ℤ) * (y₁ : ℤ) ^ n + (B : ℤ) * (z₁ : ℤ) ^ n) ^ (2 * j + 1) := by
    have := Int.natCast_dvd_natCast.mpr (hpk.trans (Nat.gcd_dvd_left _ _))
    exact_mod_cast this
  have h2 : (p : ℤ) ^ k ∣ (B : ℤ) * (z₁ : ℤ) ^ n * ((y₁ : ℤ) * (z₂ : ℤ)) ^ n
      + (A : ℤ) * (y₁ : ℤ) ^ n * ((z₁ : ℤ) * (y₂ : ℤ)) ^ n := by
    have h3 : (p : ℤ) ^ k ∣ (A : ℤ) * (y₂ : ℤ) ^ n + (B : ℤ) * (z₂ : ℤ) ^ n := by
      have := Int.natCast_dvd_natCast.mpr (hpk.trans (Nat.gcd_dvd_right _ _))
      exact_mod_cast this
    have e : (B : ℤ) * (z₁ : ℤ) ^ n * ((y₁ : ℤ) * (z₂ : ℤ)) ^ n
        + (A : ℤ) * (y₁ : ℤ) ^ n * ((z₁ : ℤ) * (y₂ : ℤ)) ^ n
        = ((y₁ : ℤ) * (z₁ : ℤ)) ^ n * ((A : ℤ) * (y₂ : ℤ) ^ n + (B : ℤ) * (z₂ : ℤ) ^ n) := by
      ring
    rw [e]
    exact dvd_mul_of_dvd_right h3 _
  have hdiv := div n p hn hp hpn j (2 * j + 1) (P j) (Q j) (hsys.degP j) (hsys.degQ j)
    (hsys.coeff_zero_eq j) (hsys.coeff_zero_ne j) (hsys.pade j)
    ((A : ℤ) * (y₁ : ℤ) ^ n) ((B : ℤ) * (z₁ : ℤ) ^ n)
    ((y₁ : ℤ) * (z₂ : ℤ)) ((z₁ : ℤ) * (y₂ : ℤ)) k hb' hw' huw h1 h2
  refine Int.natCast_dvd.mp ?_
  rw [PR_L]
  exact_mod_cast hdiv

lemma PR_size (n K : ℕ) (P Q : ℕ → ℤ[X]) (hsys : PadeSys n K P Q)
    (A B y₁ z₁ y₂ z₂ : ℕ) (j : ℕ) :
    (PR_L n P Q A B y₁ z₁ y₂ z₂ j).natAbs ≤
      (y₁ * z₂ + z₁ * y₂) * (K * (A * y₁ ^ n + B * z₁ ^ n)) ^ j := by
  have hb : (0 : ℤ) ≤ (B : ℤ) * (z₁ : ℤ) ^ n := by positivity
  have hbc : (B : ℤ) * (z₁ : ℤ) ^ n ≤ (A : ℤ) * (y₁ : ℤ) ^ n + (B : ℤ) * (z₁ : ℤ) ^ n := by
    have : (0 : ℤ) ≤ (A : ℤ) * (y₁ : ℤ) ^ n := by positivity
    linarith
  have hc : (0 : ℤ) ≤ ((A : ℤ) * (y₁ : ℤ) ^ n + (B : ℤ) * (z₁ : ℤ) ^ n) ^ j := by positivity
  have hP : |hom j (P j) ((A : ℤ) * (y₁ : ℤ) ^ n + (B : ℤ) * (z₁ : ℤ) ^ n)
      ((B : ℤ) * (z₁ : ℤ) ^ n)|
      ≤ ((K : ℤ) * ((A : ℤ) * (y₁ : ℤ) ^ n + (B : ℤ) * (z₁ : ℤ) ^ n)) ^ j := by
    rw [mul_pow]
    exact (PR_hom_abs j (P j) _ _ hb hbc).trans (mul_le_mul_of_nonneg_right (hsys.sizeP j) hc)
  have hQ : |hom j (Q j) ((A : ℤ) * (y₁ : ℤ) ^ n + (B : ℤ) * (z₁ : ℤ) ^ n)
      ((B : ℤ) * (z₁ : ℤ) ^ n)|
      ≤ ((K : ℤ) * ((A : ℤ) * (y₁ : ℤ) ^ n + (B : ℤ) * (z₁ : ℤ) ^ n)) ^ j := by
    rw [mul_pow]
    exact (PR_hom_abs j (Q j) _ _ hb hbc).trans (mul_le_mul_of_nonneg_right (hsys.sizeQ j) hc)
  have hw : (0 : ℤ) ≤ (z₁ : ℤ) * (y₂ : ℤ) := by positivity
  have hu : (0 : ℤ) ≤ (y₁ : ℤ) * (z₂ : ℤ) := by positivity
  have key : |PR_L n P Q A B y₁ z₁ y₂ z₂ j| ≤
      ((y₁ : ℤ) * (z₂ : ℤ) + (z₁ : ℤ) * (y₂ : ℤ))
        * ((K : ℤ) * ((A : ℤ) * (y₁ : ℤ) ^ n + (B : ℤ) * (z₁ : ℤ) ^ n)) ^ j := by
    rw [PR_L]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul ((z₁ : ℤ) * (y₂ : ℤ)), abs_mul ((y₁ : ℤ) * (z₂ : ℤ)), abs_of_nonneg hw,
      abs_of_nonneg hu, add_mul]
    linarith [mul_le_mul_of_nonneg_left hP hw, mul_le_mul_of_nonneg_left hQ hu]
  rw [← Int.natCast_natAbs] at key
  exact_mod_cast key

lemma PR_final (n K : ℕ) (P Q : ℕ → ℤ[X]) (hn : n.Prime) (hsys : PadeSys n K P Q)
    (A B y₁ z₁ y₂ z₂ : ℕ) (hA : 0 < A) (hB : 0 < B)
    (hcop₁ : (A * y₁ ^ n).Coprime (B * z₁ ^ n)) (hcop₂ : (A * y₂ ^ n).Coprime (B * z₂ ^ n))
    (hnc : ¬ n ∣ A * y₁ ^ n + B * z₁ ^ n)
    (hcong : ∀ p : ℕ, p.Prime → p ∣ A * y₁ ^ n + B * z₁ ^ n → p ∣ A * y₂ ^ n + B * z₂ ^ n →
      y₁ ≡ y₂ [MOD p] ∧ z₁ ≡ z₂ [MOD p])
    (j : ℕ) (hL : PR_L n P Q A B y₁ z₁ y₂ z₂ j ≠ 0) :
    (Nat.gcd ((A * y₁ ^ n + B * z₁ ^ n) ^ (2 * j + 1)) (A * y₂ ^ n + B * z₂ ^ n)) ^ n ≤
      (2 * (K * (A * y₁ ^ n + B * z₁ ^ n)) ^ j) ^ n
        * (A * y₁ ^ n + B * z₁ ^ n) * (A * y₂ ^ n + B * z₂ ^ n) := by
  have hg := Nat.le_of_dvd (Int.natAbs_pos.mpr hL)
    (PR_gcd_dvd n K P Q hn hsys A B y₁ z₁ y₂ z₂ hcop₁ hcop₂ hnc hcong j)
  have hle := hg.trans (PR_size n K P Q hsys A B y₁ z₁ y₂ z₂ j)
  have hy₁ : y₁ ^ n ≤ A * y₁ ^ n + B * z₁ ^ n :=
    (Nat.le_mul_of_pos_left _ hA).trans (Nat.le_add_right _ _)
  have hz₁ : z₁ ^ n ≤ A * y₁ ^ n + B * z₁ ^ n :=
    (Nat.le_mul_of_pos_left _ hB).trans (Nat.le_add_left _ _)
  have hy₂ : y₂ ^ n ≤ A * y₂ ^ n + B * z₂ ^ n :=
    (Nat.le_mul_of_pos_left _ hA).trans (Nat.le_add_right _ _)
  have hz₂ : z₂ ^ n ≤ A * y₂ ^ n + B * z₂ ^ n :=
    (Nat.le_mul_of_pos_left _ hB).trans (Nat.le_add_left _ _)
  have hu : (y₁ * z₂) ^ n ≤ (A * y₁ ^ n + B * z₁ ^ n) * (A * y₂ ^ n + B * z₂ ^ n) := by
    rw [mul_pow]; exact Nat.mul_le_mul hy₁ hz₂
  have hw : (z₁ * y₂) ^ n ≤ (A * y₁ ^ n + B * z₁ ^ n) * (A * y₂ ^ n + B * z₂ ^ n) := by
    rw [mul_pow]; exact Nat.mul_le_mul hz₁ hy₂
  calc (Nat.gcd ((A * y₁ ^ n + B * z₁ ^ n) ^ (2 * j + 1)) (A * y₂ ^ n + B * z₂ ^ n)) ^ n
      ≤ ((y₁ * z₂ + z₁ * y₂) * (K * (A * y₁ ^ n + B * z₁ ^ n)) ^ j) ^ n :=
        Nat.pow_le_pow_left hle n
    _ = (y₁ * z₂ + z₁ * y₂) ^ n * ((K * (A * y₁ ^ n + B * z₁ ^ n)) ^ j) ^ n := mul_pow _ _ _
    _ ≤ (2 ^ n * ((A * y₁ ^ n + B * z₁ ^ n) * (A * y₂ ^ n + B * z₂ ^ n)))
          * ((K * (A * y₁ ^ n + B * z₁ ^ n)) ^ j) ^ n :=
        Nat.mul_le_mul_right _ (PR_add_pow _ _ _ n hu hw)
    _ = (2 * (K * (A * y₁ ^ n + B * z₁ ^ n)) ^ j) ^ n
          * (A * y₁ ^ n + B * z₁ ^ n) * (A * y₂ ^ n + B * z₂ ^ n) := by
        rw [mul_pow]; ring

lemma pair (n K : ℕ) (P Q : ℕ → ℤ[X]) (hn : n.Prime) (hsys : PadeSys n K P Q)
    (A B y₁ z₁ y₂ z₂ : ℕ) (hA : 0 < A) (hB : 0 < B)
    (hy₁ : 0 < y₁) (hz₁ : 0 < z₁) (hy₂ : 0 < y₂) (hz₂ : 0 < z₂)
    (hcop₁ : (A * y₁ ^ n).Coprime (B * z₁ ^ n)) (hcop₂ : (A * y₂ ^ n).Coprime (B * z₂ ^ n))
    (hnc : ¬ n ∣ A * y₁ ^ n + B * z₁ ^ n)
    (hcong : ∀ p : ℕ, p.Prime → p ∣ A * y₁ ^ n + B * z₁ ^ n → p ∣ A * y₂ ^ n + B * z₂ ^ n →
      y₁ ≡ y₂ [MOD p] ∧ z₁ ≡ z₂ [MOD p])
    (m : ℕ) :
    ∃ m' : ℕ, (m' = m ∨ m' = m + 1) ∧
      (Nat.gcd ((A * y₁ ^ n + B * z₁ ^ n) ^ (2 * m' + 1)) (A * y₂ ^ n + B * z₂ ^ n)) ^ n ≤
        (2 * (K * (A * y₁ ^ n + B * z₁ ^ n)) ^ m') ^ n
          * (A * y₁ ^ n + B * z₁ ^ n) * (A * y₂ ^ n + B * z₂ ^ n) := by
  -- `hz₂` is not needed for the bound; this line only keeps the unused-variable linter quiet.
  have _ := hz₂
  obtain ⟨d, hd, hdet⟩ := hsys.det m
  have hc : (A : ℤ) * (y₁ : ℤ) ^ n + (B : ℤ) * (z₁ : ℤ) ^ n ≠ 0 := by positivity
  have hb : (B : ℤ) * (z₁ : ℤ) ^ n ≠ 0 := by positivity
  have hw : (z₁ : ℤ) * (y₂ : ℤ) ≠ 0 := by positivity
  rcases nv m (P m) (Q m) (P (m + 1)) (Q (m + 1)) (hsys.degP m) (hsys.degQ m)
    (hsys.degP (m + 1)) (hsys.degQ (m + 1)) d hd hdet
    ((A : ℤ) * (y₁ : ℤ) ^ n + (B : ℤ) * (z₁ : ℤ) ^ n) ((B : ℤ) * (z₁ : ℤ) ^ n)
    ((y₁ : ℤ) * (z₂ : ℤ)) ((z₁ : ℤ) * (y₂ : ℤ)) hc hb (Or.inr hw) with h | h
  · exact ⟨m, Or.inl rfl,
      PR_final n K P Q hn hsys A B y₁ z₁ y₂ z₂ hA hB hcop₁ hcop₂ hnc hcong m h⟩
  · exact ⟨m + 1, Or.inr rfl,
      PR_final n K P Q hn hsys A B y₁ z₁ y₂ z₂ hA hB hcop₁ hcop₂ hnc hcong (m + 1) h⟩

end PR

-- ### Part C: families and selection

-- rep
section RP

lemma rep (S : Finset ℕ) (n : ℕ) (hn : 0 < n) (a : ℕ) (ha : 0 < a) (haS : a.primeFactors ⊆ S) :
    ∃ A y : ℕ, a = A * y ^ n ∧ A ∣ (∏ p ∈ S.filter Nat.Prime, p) ^ (n - 1) := by
  refine ⟨∏ p ∈ a.primeFactors, p ^ (a.factorization p % n),
    ∏ p ∈ a.primeFactors, p ^ (a.factorization p / n), ?_, ?_⟩
  · rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self ha.ne']
    rw [Finsupp.prod, Nat.support_factorization]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_mul, ← pow_add, Nat.mod_add_div' (a.factorization p) n]
  · rw [← Finset.prod_pow]
    have hsub : a.primeFactors ⊆ S.filter Nat.Prime := fun p hp =>
      Finset.mem_filter.mpr ⟨haS hp, Nat.prime_of_mem_primeFactors hp⟩
    refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _ fun p _ => ?_)
      (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
    exact pow_dvd_pow p (Nat.le_sub_one_of_lt (Nat.mod_lt _ hn))

end RP

-- fam
section FM

lemma fam (S : Finset ℕ) (n : ℕ) (hn : 0 < n)
    (hinf : {p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧ p.1.Coprime p.2 ∧
      (p.1 * p.2 * (p.1 + p.2)).primeFactors ⊆ S}.Infinite) :
    ∃ (A B : ℕ) (G : Set (ℕ × ℕ)), 0 < A ∧ 0 < B ∧
      (∀ q ∈ G, 0 < q.1 ∧ 0 < q.2 ∧ (A * q.1 ^ n).Coprime (B * q.2 ^ n) ∧
        (A * q.1 ^ n + B * q.2 ^ n).primeFactors ⊆ S) ∧
      (∀ q ∈ G, ∀ q' ∈ G, ∀ p ∈ S, p.Prime → q.1 ≡ q'.1 [MOD p] ∧ q.2 ≡ q'.2 [MOD p]) ∧
      ((fun q : ℕ × ℕ => A * q.1 ^ n + B * q.2 ^ n) '' G).Infinite := by
  set Sol := {p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧ p.1.Coprime p.2 ∧
      (p.1 * p.2 * (p.1 + p.2)).primeFactors ⊆ S} with hSol
  set Mp := ∏ p ∈ S.filter Nat.Prime, p with hMp
  have hMp0 : 0 < Mp := Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos
  have hpM : ∀ p ∈ S, p.Prime → p ∣ Mp := fun p hp hpp =>
    Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨hp, hpp⟩)
  -- the prime factors of the parts of a solution lie in `S`
  have hparts : ∀ q ∈ Sol, q.1.primeFactors ⊆ S ∧ q.2.primeFactors ⊆ S ∧
      (q.1 + q.2).primeFactors ⊆ S := by
    rintro q ⟨h1, h2, -, hS⟩
    have hne : q.1 * q.2 * (q.1 + q.2) ≠ 0 := by positivity
    refine ⟨?_, ?_, ?_⟩
    · exact (Nat.primeFactors_mono (Dvd.intro (q.2 * (q.1 + q.2)) (by ring)) hne).trans hS
    · exact (Nat.primeFactors_mono (Dvd.intro (q.1 * (q.1 + q.2)) (by ring)) hne).trans hS
    · exact (Nat.primeFactors_mono (Dvd.intro_left _ rfl) hne).trans hS
  have hrep : ∀ q ∈ Sol, ∃ A y B z : ℕ, q.1 = A * y ^ n ∧ A ∣ Mp ^ (n - 1) ∧
      q.2 = B * z ^ n ∧ B ∣ Mp ^ (n - 1) := by
    intro q hq
    obtain ⟨A, y, hy, hA⟩ := rep S n hn q.1 hq.1 (hparts q hq).1
    obtain ⟨B, z, hz, hB⟩ := rep S n hn q.2 hq.2.1 (hparts q hq).2.1
    exact ⟨A, y, B, z, hy, hA, hz, hB⟩
  choose! fA fy fB fz hfy hfA hfz hfB using hrep
  set κ : ℕ × ℕ → ℕ × ℕ × ℕ × ℕ := fun q => (fA q, fB q, fy q % Mp, fz q % Mp) with hκ
  set D := (Mp ^ (n - 1)).divisors with hD
  set T := D ×ˢ D ×ˢ Finset.range Mp ×ˢ Finset.range Mp with hT
  have hκT : ∀ q ∈ Sol, κ q ∈ T := by
    intro q hq
    have hM0 : Mp ^ (n - 1) ≠ 0 := pow_ne_zero _ hMp0.ne'
    simp only [hT, hD, hκ, Finset.mem_product, Nat.mem_divisors, Finset.mem_range]
    exact ⟨⟨hfA q hq, hM0⟩, ⟨hfB q hq, hM0⟩, Nat.mod_lt _ hMp0, Nat.mod_lt _ hMp0⟩
  -- pigeonhole: some fibre is infinite
  obtain ⟨k, -, hk⟩ : ∃ k ∈ T, {q | q ∈ Sol ∧ κ q = k}.Infinite := by
    by_contra hall
    push Not at hall
    refine hinf (Set.Finite.subset (Set.Finite.biUnion (t := fun k => {q | q ∈ Sol ∧ κ q = k})
      (T : Set (ℕ × ℕ × ℕ × ℕ)).toFinite fun k hk => hall k hk) ?_)
    intro q hq
    exact Set.mem_biUnion (x := κ q) (hκT q hq) ⟨hq, rfl⟩
  set Fb := {q | q ∈ Sol ∧ κ q = k} with hFb
  obtain ⟨q₀, hq₀, hκq₀⟩ := hk.nonempty
  have hAk : ∀ q ∈ Fb, fA q = k.1 := fun q hq => by
    have := hq.2; rw [hκ] at this; exact (Prod.ext_iff.mp this).1
  have hBk : ∀ q ∈ Fb, fB q = k.2.1 := fun q hq => by
    have := hq.2; rw [hκ] at this; exact (Prod.ext_iff.mp (Prod.ext_iff.mp this).2).1
  have hyk : ∀ q ∈ Fb, fy q % Mp = k.2.2.1 := fun q hq => by
    have := hq.2; rw [hκ] at this
    exact (Prod.ext_iff.mp (Prod.ext_iff.mp (Prod.ext_iff.mp this).2).2).1
  have hzk : ∀ q ∈ Fb, fz q % Mp = k.2.2.2 := fun q hq => by
    have := hq.2; rw [hκ] at this
    exact (Prod.ext_iff.mp (Prod.ext_iff.mp (Prod.ext_iff.mp this).2).2).2
  have hq1 : ∀ q ∈ Fb, q.1 = k.1 * fy q ^ n := fun q hq => by
    rw [← hAk q hq]; exact hfy q hq.1
  have hq2 : ∀ q ∈ Fb, q.2 = k.2.1 * fz q ^ n := fun q hq => by
    rw [← hBk q hq]; exact hfz q hq.1
  set A := k.1
  set B := k.2.1
  have hA : 0 < A := by
    rcases Nat.eq_zero_or_pos A with h | h
    · have := hq1 q₀ ⟨hq₀, hκq₀⟩; rw [h, zero_mul] at this; exact absurd this hq₀.1.ne'
    · exact h
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h | h
    · have := hq2 q₀ ⟨hq₀, hκq₀⟩; rw [h, zero_mul] at this; exact absurd this hq₀.2.1.ne'
    · exact h
  let φ : ℕ × ℕ → ℕ × ℕ := fun q => (fy q, fz q)
  set G := φ '' Fb with hG
  have hinj : Set.InjOn φ Fb := by
    intro q hq q' hq' h
    have h1 : fy q = fy q' := (Prod.ext_iff.mp h).1
    have h2 : fz q = fz q' := (Prod.ext_iff.mp h).2
    refine Prod.ext ?_ ?_
    · rw [hq1 q hq, hq1 q' hq', h1]
    · rw [hq2 q hq, hq2 q' hq', h2]
  have hGinf : G.Infinite := hk.image hinj
  have hGprop : ∀ q ∈ G, 0 < q.1 ∧ 0 < q.2 ∧ (A * q.1 ^ n).Coprime (B * q.2 ^ n) ∧
      (A * q.1 ^ n + B * q.2 ^ n).primeFactors ⊆ S := by
    rintro _ ⟨q, hq, rfl⟩
    have e1 := hq1 q hq
    have e2 := hq2 q hq
    have hs := hq.1
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos (fy q) with h | h
      · have := hs.1; rw [e1, h, zero_pow hn.ne', mul_zero] at this; exact absurd this (lt_irrefl 0)
      · exact h
    · rcases Nat.eq_zero_or_pos (fz q) with h | h
      · have := hs.2.1; rw [e2, h, zero_pow hn.ne', mul_zero] at this; exact absurd this (lt_irrefl 0)
      · exact h
    · show (A * fy q ^ n).Coprime (B * fz q ^ n)
      rw [← e1, ← e2]; exact hs.2.2.1
    · show (A * fy q ^ n + B * fz q ^ n).primeFactors ⊆ S
      rw [← e1, ← e2]; exact (hparts q hs).2.2
  refine ⟨A, B, G, hA, hB, hGprop, ?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩ _ ⟨q', hq', rfl⟩ p hp hpp
    refine ⟨Nat.ModEq.of_dvd (hpM p hp hpp) ?_, Nat.ModEq.of_dvd (hpM p hp hpp) ?_⟩
    · show fy q % Mp = fy q' % Mp
      rw [hyk q hq, hyk q' hq']
    · show fz q % Mp = fz q' % Mp
      rw [hzk q hq, hzk q' hq']
  · intro hfin
    obtain ⟨N, hN⟩ := hfin.bddAbove
    apply hGinf
    refine (Set.finite_Iic N |>.prod (Set.finite_Iic N)).subset ?_
    intro q hq
    have hc : A * q.1 ^ n + B * q.2 ^ n ≤ N := hN ⟨q, hq, rfl⟩
    have hp := hGprop q hq
    have h1 : q.1 ≤ A * q.1 ^ n :=
      (Nat.le_self_pow hn.ne' q.1).trans (Nat.le_mul_of_pos_left _ hA)
    have h2 : q.2 ≤ B * q.2 ^ n :=
      (Nat.le_self_pow hn.ne' q.2).trans (Nat.le_mul_of_pos_left _ hB)
    exact ⟨Set.mem_Iic.mpr (by omega), Set.mem_Iic.mpr (by omega)⟩

end FM

-- cell
section CL

/-- The share is nonnegative. -/
lemma CL_share_nonneg (c p : ℕ) (hc : 2 ≤ c) :
    0 ≤ (c.factorization p : ℝ) * Real.log p / Real.log c := by
  have hlc : 0 < Real.log c := Real.log_pos (by exact_mod_cast hc)
  have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  positivity

/-- The share is at most one. -/
lemma CL_share_le_one (c p : ℕ) (hc : 2 ≤ c) :
    (c.factorization p : ℝ) * Real.log p / Real.log c ≤ 1 := by
  have hlc : 0 < Real.log c := Real.log_pos (by exact_mod_cast hc)
  rw [div_le_one hlc, ← Real.log_pow]
  have hpos : (0 : ℝ) < ((p ^ c.factorization p : ℕ) : ℝ) := by
    exact_mod_cast Nat.ordProj_pos c p
  have hle : ((p ^ c.factorization p : ℕ) : ℝ) ≤ (c : ℝ) := by
    exact_mod_cast Nat.ordProj_le p (by omega)
  have := Real.log_le_log hpos hle
  push_cast at this
  exact this

lemma cell (S : Finset ℕ) (T : Set ℕ) (hT : T.Infinite) (hS : ∀ c ∈ T, c.primeFactors ⊆ S)
    (N L : ℕ) (hN : 0 < N) :
    ∃ c₁ ∈ T, ∃ c₂ ∈ T, 2 ≤ c₁ ∧ L ≤ c₁ ∧ c₁ ^ 5 ≤ c₂ ∧
      ∀ p ∈ S, (c₁.factorization p : ℝ) * Real.log p / Real.log c₁ - 1 / (N : ℝ) ≤
        (c₂.factorization p : ℝ) * Real.log p / Real.log c₂ := by
  set T' : Set ℕ := T \ Set.Iio 2 with hT'def
  have hT' : T'.Infinite := hT.sdiff (Set.finite_Iio 2)
  have hmem : ∀ c ∈ T', c ∈ T ∧ 2 ≤ c := fun c hc => ⟨hc.1, by
    have := hc.2; simp only [Set.mem_Iio, not_lt] at this; exact this⟩
  have : Infinite T' := hT'.to_subtype
  let f : T' → (S → Fin (N + 1)) := fun x p =>
    ⟨min ⌊(N : ℝ) * ((x.1.factorization p.1 : ℝ) * Real.log p.1 / Real.log x.1)⌋₊ N,
      Nat.lt_succ_of_le (min_le_right _ _)⟩
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber f
  set U : Set ℕ := Subtype.val '' (f ⁻¹' {y}) with hUdef
  have hU : U.Infinite :=
    (Set.infinite_coe_iff.mp hy).image Subtype.val_injective.injOn
  have hUT : ∀ c ∈ U, ∃ h : c ∈ T', f ⟨c, h⟩ = y := by
    rintro c ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  obtain ⟨c₁, hc₁U, hLc₁⟩ := hU.exists_gt L
  obtain ⟨c₂, hc₂U, h5⟩ := hU.exists_gt (c₁ ^ 5)
  obtain ⟨h₁, hf₁⟩ := hUT c₁ hc₁U
  obtain ⟨h₂, hf₂⟩ := hUT c₂ hc₂U
  obtain ⟨hT₁, h2₁⟩ := hmem c₁ h₁
  obtain ⟨hT₂, h2₂⟩ := hmem c₂ h₂
  refine ⟨c₁, hT₁, c₂, hT₂, h2₁, hLc₁.le, h5.le, ?_⟩
  intro p hp
  have hfeq := congrArg (fun g => (g ⟨p, hp⟩ : ℕ)) (hf₁.trans hf₂.symm)
  simp only [f] at hfeq
  set σ₁ := (c₁.factorization p : ℝ) * Real.log p / Real.log c₁ with hσ₁
  set σ₂ := (c₂.factorization p : ℝ) * Real.log p / Real.log c₂ with hσ₂
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h0₁ : 0 ≤ σ₁ := CL_share_nonneg c₁ p h2₁
  have h0₂ : 0 ≤ σ₂ := CL_share_nonneg c₂ p h2₂
  have hfl : ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 → ⌊(N : ℝ) * σ⌋₊ ≤ N := by
    intro σ h0 h1
    have : (N : ℝ) * σ ≤ N := by nlinarith
    calc ⌊(N : ℝ) * σ⌋₊ ≤ ⌊(N : ℝ)⌋₊ := Nat.floor_le_floor this
      _ = N := Nat.floor_natCast N
  rw [min_eq_left (hfl σ₁ h0₁ (CL_share_le_one c₁ p h2₁)),
    min_eq_left (hfl σ₂ h0₂ (CL_share_le_one c₂ p h2₂))] at hfeq
  have ha := Nat.lt_floor_add_one ((N : ℝ) * σ₁)
  have hb := Nat.floor_le (mul_nonneg hN'.le h0₂)
  rw [hfeq] at ha
  have hlt : (N : ℝ) * σ₁ - 1 < (N : ℝ) * σ₂ := by linarith
  have : σ₁ - 1 / (N : ℝ) = ((N : ℝ) * σ₁ - 1) / N := by field_simp
  rw [this, div_le_iff₀ hN']
  linarith

end CL

-- ineq
section IQ

/-- `log c = ∑_{p ∈ T} v_p(c) log p` for every finite set `T` containing the prime factors of
`c ≠ 0` (step (1) of the sketch, and step (2) when applied to a gcd). -/
lemma IQ_log_eq_sum (c : ℕ) (hc : c ≠ 0) (T : Finset ℕ) (hT : c.primeFactors ⊆ T) :
    Real.log (c : ℝ) = ∑ p ∈ T, (c.factorization p : ℝ) * Real.log (p : ℝ) := by
  have h1 : (c : ℝ) = ∏ p ∈ c.primeFactors, (p : ℝ) ^ (c.factorization p) := by
    have h := Nat.prod_factorization_pow_eq_self hc
    rw [Finsupp.prod, Nat.support_factorization] at h
    have h' := congrArg (fun x : ℕ => (x : ℝ)) h
    simp only [Nat.cast_prod, Nat.cast_pow] at h'
    exact h'.symm
  have h2 : Real.log (c : ℝ)
      = ∑ p ∈ c.primeFactors, (c.factorization p : ℝ) * Real.log (p : ℝ) := by
    have h3 : Real.log (∏ p ∈ c.primeFactors, (p : ℝ) ^ (c.factorization p))
        = ∑ p ∈ c.primeFactors, Real.log ((p : ℝ) ^ (c.factorization p)) := by
      apply Real.log_prod
      intro p hp
      have hp0 : (p : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
      exact pow_ne_zero _ hp0
    rw [← h1] at h3
    rw [h3]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Real.log_pow]
  rw [h2]
  refine Finset.sum_subset hT fun p _ hp => ?_
  have h0 : c.factorization p = 0 := by
    rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
    exact hp
  rw [h0]
  simp

/-- The real-variable inequality of step (3): `a = log 2`, `k = log K`, `l = log c₁`,
`L = log c₂`, `g = log gcd`. -/
lemma IQ_real (n m l L a k g : ℝ) (hn : 17 ≤ n) (hm : 1 ≤ m) (hl : 0 < l) (ha : 0 ≤ a)
    (hak : 2 * a + 2 * k ≤ l) (hL : L < (2 * m + 5) * l)
    (hg : (2 * m + 1) * l - L / 8 ≤ g) :
    n * (a + m * (k + l)) + l + L < n * g := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have h1 : n * ((2 * m + 1) * l - L / 8) ≤ n * g := mul_le_mul_of_nonneg_left hg hn0.le
  have h2 : m * k ≤ m * (l / 2 - a) := mul_le_mul_of_nonneg_left (by linarith) hm0
  have h2' : 0 ≤ (m - 1) * a := mul_nonneg (by linarith) ha
  have h3 : a + m * k ≤ m * l / 2 := by linarith
  have h4 : n * (a + m * k) ≤ n * (m * l / 2) := mul_le_mul_of_nonneg_left h3 hn0.le
  have h5 : (1 + n / 8) * L < (1 + n / 8) * ((2 * m + 5) * l) :=
    mul_lt_mul_of_pos_left hL (by linarith)
  have h6 : 0 ≤ l * ((n - 17) * (m / 4 + 3 / 8) + 9 / 4 * m + 3 / 8) := by
    apply mul_nonneg hl.le
    have : 0 ≤ (n - 17) * (m / 4 + 3 / 8) := mul_nonneg (by linarith) (by linarith)
    linarith
  linarith

/-- The inequality for one `m` with `1 ≤ m` and `c₁^(2m+1) ≤ c₂ < c₁^(2m+5)`. -/
lemma IQ_core (S : Finset ℕ) (n K : ℕ) (hn : 17 ≤ n) (hK : 1 ≤ K) (c₁ c₂ : ℕ)
    (h2 : 2 ≤ c₁) (hL : 4 * K ^ 2 ≤ c₁)
    (hS₁ : c₁.primeFactors ⊆ S)
    (hshare : ∀ p ∈ S, (c₁.factorization p : ℝ) * Real.log p / Real.log c₁
        - 1 / ((8 * (S.card + 1) : ℕ) : ℝ) ≤
      (c₂.factorization p : ℝ) * Real.log p / Real.log c₂)
    (m : ℕ) (hm : 1 ≤ m) (hlo : c₁ ^ (2 * m + 1) ≤ c₂) (hhi : c₂ < c₁ ^ (2 * m + 5)) :
    (2 * (K * c₁) ^ m) ^ n * c₁ * c₂ < (Nat.gcd (c₁ ^ (2 * m + 1)) c₂) ^ n := by
  have hc₁0 : c₁ ≠ 0 := by omega
  have hc₁pos : (0 : ℝ) < (c₁ : ℝ) := by exact_mod_cast (by omega : 0 < c₁)
  have hc₁R : (1 : ℝ) < (c₁ : ℝ) := by exact_mod_cast (by omega : 1 < c₁)
  have hc₂pos : 0 < c₂ := lt_of_lt_of_le (pow_pos (by omega) _) hlo
  have hc₂0 : c₂ ≠ 0 := hc₂pos.ne'
  have hc₂R : (0 : ℝ) < (c₂ : ℝ) := by exact_mod_cast hc₂pos
  have hKR : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < (K : ℝ) := by linarith
  have hl : 0 < Real.log (c₁ : ℝ) := Real.log_pos hc₁R
  -- the size of `log c₂` against `log c₁`
  have hLlo : (2 * (m : ℝ) + 1) * Real.log (c₁ : ℝ) ≤ Real.log (c₂ : ℝ) := by
    have h : ((c₁ : ℝ)) ^ (2 * m + 1) ≤ (c₂ : ℝ) := by exact_mod_cast hlo
    have h' := Real.log_le_log (pow_pos hc₁pos _) h
    rw [Real.log_pow] at h'
    push_cast at h'
    exact h'
  have hLhi : Real.log (c₂ : ℝ) < (2 * (m : ℝ) + 5) * Real.log (c₁ : ℝ) := by
    have h : (c₂ : ℝ) < ((c₁ : ℝ)) ^ (2 * m + 5) := by exact_mod_cast hhi
    have h' := Real.log_lt_log hc₂R h
    rw [Real.log_pow] at h'
    push_cast at h'
    exact h'
  have hLpos : 0 < Real.log (c₂ : ℝ) := lt_of_lt_of_le (by positivity) hLlo
  -- `c₁ ≥ 4 K^2`
  have hak : 2 * Real.log 2 + 2 * Real.log (K : ℝ) ≤ Real.log (c₁ : ℝ) := by
    have h : (2 : ℝ) ^ 2 * (K : ℝ) ^ 2 ≤ (c₁ : ℝ) := by
      have : ((4 * K ^ 2 : ℕ) : ℝ) ≤ (c₁ : ℝ) := by exact_mod_cast hL
      push_cast at this
      linarith
    have h' := Real.log_le_log (by positivity) h
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h'
    push_cast at h'
    exact h'
  -- the gcd and its factorization
  have hpow0 : c₁ ^ (2 * m + 1) ≠ 0 := pow_ne_zero _ hc₁0
  have hg0 : Nat.gcd (c₁ ^ (2 * m + 1)) c₂ ≠ 0 :=
    (Nat.gcd_pos_of_pos_right _ hc₂pos).ne'
  have hgR : (0 : ℝ) < ((Nat.gcd (c₁ ^ (2 * m + 1)) c₂ : ℕ) : ℝ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_right _ hc₂pos
  have hgsub : (Nat.gcd (c₁ ^ (2 * m + 1)) c₂).primeFactors ⊆ c₁.primeFactors := by
    have h := Nat.primeFactors_mono (Nat.gcd_dvd_left (c₁ ^ (2 * m + 1)) c₂) hpow0
    rwa [Nat.primeFactors_pow _ (by omega)] at h
  have hlg := IQ_log_eq_sum (Nat.gcd (c₁ ^ (2 * m + 1)) c₂) hg0 c₁.primeFactors hgsub
  have hll := IQ_log_eq_sum c₁ hc₁0 c₁.primeFactors (Finset.Subset.refl _)
  have hfac : ∀ p, (Nat.gcd (c₁ ^ (2 * m + 1)) c₂).factorization p
      = min ((2 * m + 1) * c₁.factorization p) (c₂.factorization p) := by
    intro p
    rw [Nat.factorization_gcd hpow0 hc₂0, Finsupp.inf_apply, Nat.factorization_pow]
    simp
  have hεpos : (0 : ℝ) < 1 / ((8 * (S.card + 1) : ℕ) : ℝ) := by positivity
  have hεS : (S.card : ℝ) * (1 / ((8 * (S.card + 1) : ℕ) : ℝ)) ≤ 1 / 8 := by
    have h : (1 / ((8 * (S.card + 1) : ℕ) : ℝ)) * (8 * ((S.card : ℝ) + 1)) = 1 := by
      push_cast
      field_simp
    linarith
  -- one prime of `c₁`
  have hterm : ∀ p ∈ c₁.primeFactors,
      (2 * (m : ℝ) + 1) * ((c₁.factorization p : ℝ) * Real.log (p : ℝ))
        - Real.log (c₂ : ℝ) * (1 / ((8 * (S.card + 1) : ℕ) : ℝ))
      ≤ ((Nat.gcd (c₁ ^ (2 * m + 1)) c₂).factorization p : ℝ) * Real.log (p : ℝ) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hlp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hpp.one_lt)
    have hv : 0 ≤ (c₁.factorization p : ℝ) * Real.log (p : ℝ) := by positivity
    have hLe : 0 ≤ Real.log (c₂ : ℝ) * (1 / ((8 * (S.card + 1) : ℕ) : ℝ)) :=
      mul_nonneg hLpos.le hεpos.le
    rw [hfac p]
    rcases min_choice ((2 * m + 1) * c₁.factorization p) (c₂.factorization p) with h | h
    · rw [h, Nat.cast_mul (2 * m + 1) (c₁.factorization p)]
      have hc : ((2 * m + 1 : ℕ) : ℝ) = 2 * (m : ℝ) + 1 := by push_cast; ring
      rw [hc]
      linarith
    · rw [h]
      have hs := hshare p (hS₁ hp)
      have h1 : (c₁.factorization p : ℝ) * Real.log (p : ℝ) / Real.log (c₁ : ℝ)
            * Real.log (c₂ : ℝ)
          - 1 / ((8 * (S.card + 1) : ℕ) : ℝ) * Real.log (c₂ : ℝ)
          ≤ (c₂.factorization p : ℝ) * Real.log (p : ℝ) := by
        have h1' := mul_le_mul_of_nonneg_right hs hLpos.le
        rw [div_mul_cancel₀ _ hLpos.ne'] at h1'
        linarith
      have h2' : (2 * (m : ℝ) + 1) * ((c₁.factorization p : ℝ) * Real.log (p : ℝ))
          ≤ (c₁.factorization p : ℝ) * Real.log (p : ℝ) / Real.log (c₁ : ℝ)
            * Real.log (c₂ : ℝ) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hl]
        have h3 := mul_le_mul_of_nonneg_left hLlo hv
        linarith
      linarith
  -- sum over the primes of `c₁`
  have hsum : (2 * (m : ℝ) + 1) * Real.log (c₁ : ℝ) - Real.log (c₂ : ℝ) / 8
      ≤ Real.log ((Nat.gcd (c₁ ^ (2 * m + 1)) c₂ : ℕ) : ℝ) := by
    rw [hlg]
    have h1 := Finset.sum_le_sum hterm
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hll, Finset.sum_const, nsmul_eq_mul] at h1
    have hcard : (c₁.primeFactors.card : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hS₁
    have hLe : 0 ≤ Real.log (c₂ : ℝ) * (1 / ((8 * (S.card + 1) : ℕ) : ℝ)) :=
      mul_nonneg hLpos.le hεpos.le
    have h8 : (c₁.primeFactors.card : ℝ)
        * (Real.log (c₂ : ℝ) * (1 / ((8 * (S.card + 1) : ℕ) : ℝ))) ≤ Real.log (c₂ : ℝ) / 8 := by
      have ha := mul_le_mul_of_nonneg_right hcard hLe
      have hb := mul_le_mul_of_nonneg_left hεS hLpos.le
      linarith
    linarith
  -- the real inequality
  have hfin := IQ_real (n : ℝ) (m : ℝ) (Real.log (c₁ : ℝ)) (Real.log (c₂ : ℝ)) (Real.log 2)
    (Real.log (K : ℝ)) (Real.log ((Nat.gcd (c₁ ^ (2 * m + 1)) c₂ : ℕ) : ℝ))
    (by exact_mod_cast hn) (by exact_mod_cast hm) hl (Real.log_nonneg (by norm_num)) hak hLhi hsum
  -- exponentiate
  have e1 : Real.log ((2 * ((K : ℝ) * (c₁ : ℝ)) ^ m) ^ n * (c₁ : ℝ) * (c₂ : ℝ))
      = (n : ℝ) * (Real.log 2 + (m : ℝ) * (Real.log (K : ℝ) + Real.log (c₁ : ℝ)))
        + Real.log (c₁ : ℝ) + Real.log (c₂ : ℝ) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_mul (by positivity) (by positivity)]
  have e2 : Real.log (((Nat.gcd (c₁ ^ (2 * m + 1)) c₂ : ℕ) : ℝ) ^ n)
      = (n : ℝ) * Real.log ((Nat.gcd (c₁ ^ (2 * m + 1)) c₂ : ℕ) : ℝ) := Real.log_pow _ _
  have hreal : (2 * ((K : ℝ) * (c₁ : ℝ)) ^ m) ^ n * (c₁ : ℝ) * (c₂ : ℝ)
      < ((Nat.gcd (c₁ ^ (2 * m + 1)) c₂ : ℕ) : ℝ) ^ n := by
    rw [← Real.log_lt_log_iff (by positivity) (by positivity), e1, e2]
    exact hfin
  exact_mod_cast hreal

/-- LEMMA `ineq`: the final inequality. -/
lemma ineq (S : Finset ℕ) (n K : ℕ) (hn : 17 ≤ n) (hK : 1 ≤ K) (c₁ c₂ : ℕ)
    (h2 : 2 ≤ c₁) (hL : 4 * K ^ 2 ≤ c₁) (h5 : c₁ ^ 5 ≤ c₂)
    (hS₁ : c₁.primeFactors ⊆ S) (hS₂ : c₂.primeFactors ⊆ S)
    (hshare : ∀ p ∈ S, (c₁.factorization p : ℝ) * Real.log p / Real.log c₁
        - 1 / ((8 * (S.card + 1) : ℕ) : ℝ) ≤
      (c₂.factorization p : ℝ) * Real.log p / Real.log c₂) :
    ∃ m : ℕ, ∀ m' : ℕ, (m' = m ∨ m' = m + 1) →
      (2 * (K * c₁) ^ m') ^ n * c₁ * c₂ < (Nat.gcd (c₁ ^ (2 * m' + 1)) c₂) ^ n := by
  have _hS₂ := hS₂
  have hc₁1 : 1 < c₁ := by omega
  have hc₂0 : c₂ ≠ 0 := (lt_of_lt_of_le (pow_pos (by omega) 5) h5).ne'
  have hk5 : 5 ≤ Nat.log c₁ c₂ := Nat.le_log_of_pow_le hc₁1 h5
  have hklo : c₁ ^ Nat.log c₁ c₂ ≤ c₂ := Nat.pow_log_le_self c₁ hc₂0
  have hkhi : c₂ < c₁ ^ (Nat.log c₁ c₂ + 1) := Nat.lt_pow_succ_log_self hc₁1 c₂
  have hmono : ∀ a b : ℕ, a ≤ b → c₁ ^ a ≤ c₁ ^ b := fun a b h =>
    Nat.pow_le_pow_right (by omega) h
  refine ⟨(Nat.log c₁ c₂ - 3) / 2, ?_⟩
  intro m' hm'
  apply IQ_core S n K hn hK c₁ c₂ h2 hL hS₁ hshare m'
  · omega
  · exact le_trans (hmono _ _ (by omega)) hklo
  · exact lt_of_lt_of_le hkhi (hmono _ _ (by omega))

end IQ

/-- Selection (proved from `cell` and `ineq`): an infinite set of `S`-units contains two members
violating the bound of `pair`. -/
theorem sel (S : Finset ℕ) (T : Set ℕ) (hT : T.Infinite) (hS : ∀ c ∈ T, c.primeFactors ⊆ S)
    (n K : ℕ) (hn : 17 ≤ n) (hK : 1 ≤ K) :
    ∃ c₁ ∈ T, ∃ c₂ ∈ T, ∃ m : ℕ, ∀ m' : ℕ, (m' = m ∨ m' = m + 1) →
      (2 * (K * c₁) ^ m') ^ n * c₁ * c₂ < (Nat.gcd (c₁ ^ (2 * m' + 1)) c₂) ^ n := by
  obtain ⟨c₁, h1, c₂, h2, h2le, hL, h5, hsh⟩ :=
    cell S T hT hS (8 * (S.card + 1)) (4 * K ^ 2) (by positivity)
  obtain ⟨m, hm⟩ := ineq S n K hn hK c₁ c₂ h2le hL h5 (hS c₁ h1) (hS c₂ h2) hsh
  exact ⟨c₁, h1, c₂, h2, m, hm⟩

/-- The S-unit theorem over `ℚ` in the form of `H1`. -/
theorem main : OMA.R_ABC_abc_R1.H1 := by
  intro S
  by_contra hfin
  have hinf : {p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧ p.1.Coprime p.2 ∧
      (p.1 * p.2 * (p.1 + p.2)).primeFactors ⊆ S}.Infinite := hfin
  obtain ⟨n, hnge, hnp⟩ := Nat.exists_infinite_primes (max 17 (S.sup id + 1))
  have hn17 : 17 ≤ n := le_trans (le_max_left _ _) hnge
  have hnS : n ∉ S := by
    intro h
    have h1 : n ≤ S.sup id := Finset.le_sup (f := id) h
    have h2 : S.sup id + 1 ≤ n := le_trans (le_max_right _ _) hnge
    omega
  obtain ⟨K, P, Q, hsys⟩ := pkg n hnp
  obtain ⟨A, B, G, hA, hB, hG, hcong, hGinf⟩ := fam S n hnp.pos hinf
  obtain ⟨c₁, hc₁, c₂, hc₂, m, hm⟩ :=
    sel S ((fun q : ℕ × ℕ => A * q.1 ^ n + B * q.2 ^ n) '' G) hGinf
      (by rintro c ⟨q, hq, rfl⟩; exact (hG q hq).2.2.2) n K hn17 hsys.one_le
  obtain ⟨q₁, hq₁, rfl⟩ := hc₁
  obtain ⟨q₂, hq₂, rfl⟩ := hc₂
  obtain ⟨h1y, h1z, h1c, h1S⟩ := hG q₁ hq₁
  obtain ⟨h2y, h2z, h2c, -⟩ := hG q₂ hq₂
  have hc₁pos : A * q₁.1 ^ n + B * q₁.2 ^ n ≠ 0 := by
    have := Nat.mul_pos hA (pow_pos h1y n)
    omega
  have hnc : ¬ n ∣ A * q₁.1 ^ n + B * q₁.2 ^ n := fun hdvd =>
    hnS (h1S (Nat.mem_primeFactors.mpr ⟨hnp, hdvd, hc₁pos⟩))
  obtain ⟨m', hm', hle⟩ := pair n K P Q hnp hsys A B q₁.1 q₁.2 q₂.1 q₂.2 hA hB h1y h1z h2y h2z
    h1c h2c hnc
    (fun p hp hp1 _ => hcong q₁ hq₁ q₂ hq₂ p
      (h1S (Nat.mem_primeFactors.mpr ⟨hp, hp1, hc₁pos⟩)) hp) m
  exact absurd (hm m' hm') (not_lt.mpr hle)

end OMA.SUnit

theorem OMA.solution : OMA.R_ABC_abc_R1.H1 := OMA.SUnit.main
