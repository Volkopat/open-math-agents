import OMAReductions.R_Erdos267_erdos_267_variants_generalisation_ratio_limit_to_infinity_R1

-- Step Erdos267.erdos_267.variants.generalisation_ratio_limit_to_infinity.R1.H1: hypothesis H1 of reduction Erdos267.erdos_267.variants.generalisation_ratio_limit_to_infinity.R1
-- Credit: @qu1r0ra
-- H1 := ∀ n : ℕ → ℕ, StrictMono n → (∃ c : ℝ, 1 < c ∧ ∀ᶠ k in atTop, c * n k ≤ n (k + 1)) →     Irrational (∑' k, 1 / (Nat.fib (n k) : ℝ))

/-
Provenance. Namespace `OMAH1Research` below is a mechanical port of the Lean proof of Erdős
Problem 267 (uniform ratio gap `c * n k ≤ n (k + 1)`, `c > 1`) by Will Blair:
https://github.com/williamjblair/lean-proofs/blob/4f915a323443bfb1709a6805a013812016dca88a/starfleet/erdos-267/Research/Erdos267Standalone.lean
To fit the 512 KiB proof cap, the port keeps only the declarations that the final theorem
`irrational_reciprocal_fib_of_ratio_gap` depends on, removes comments and docstrings, scopes each
`set_option` to its declaration, and renames the other top-level declarations to `Q<number>`.
The proof steps are unchanged. The bridge at the end of the file derives `H1` (an eventual
ratio bound, possibly with `n 0 = 0`) from that theorem by dropping a finite head of the series.

Original licence (MIT):
Copyright (c) 2026 Will Blair
Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the Software), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions: The above copyright notice and this
permission notice shall be included in all copies or substantial portions of the Software.
THE SOFTWARE IS PROVIDED AS IS, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
-/

namespace OMAH1Research
open Filter Topology
open Real goldenRatio
open scoped BigOperators
theorem Q354 (n : ℕ) (hn : 0 < n) :
    φ ^ n ≤ φ ^ 2 * (Nat.fib n : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have h := Real.goldenRatio_mul_fib_succ_add_fib k
  have hmono : (Nat.fib k : ℝ) ≤ Nat.fib (k + 1) := by
    exact_mod_cast Nat.fib_le_fib_succ
  calc
    φ ^ (k + 1) = φ * (Nat.fib (k + 1) : ℝ) + Nat.fib k := h.symm
    _ ≤ φ * (Nat.fib (k + 1) : ℝ) + Nat.fib (k + 1) := by gcongr
    _ = φ ^ 2 * (Nat.fib (k + 1) : ℝ) := by rw [Real.goldenRatio_sq]; ring
theorem Q372 (n : ℕ → ℕ) (hmono : StrictMono n)
    (N j : ℕ) : n N + j ≤ n (N + j) := by
  simpa [add_comm] using hmono.add_le_nat j N
theorem Q360 (m : ℕ) (hm : 0 < m) :
    (Nat.fib m : ℝ)⁻¹ ≤ φ ^ 2 * (φ⁻¹) ^ m := by
  have hf : (0 : ℝ) < Nat.fib m := by exact_mod_cast Nat.fib_pos.mpr hm
  have hp : 0 < φ ^ m := pow_pos Real.goldenRatio_pos _
  have h := Q354 m hm
  rw [inv_pow]
  have hdiv : (1 : ℝ) / Nat.fib m ≤ φ ^ 2 / φ ^ m :=
    (div_le_div_iff₀ hf hp).2 (by simpa [mul_comm] using h)
  simpa [one_div, div_eq_mul_inv, mul_assoc] using hdiv
theorem Q296
    (n : ℕ → ℕ) (hpos : ∀ k : ℕ, 0 < n k) (hmono : StrictMono n) (N : ℕ) :
    Summable (fun j : ℕ => (Nat.fib (n (N + j)) : ℝ)⁻¹) ∧
      (∑' j : ℕ, (Nat.fib (n (N + j)) : ℝ)⁻¹) ≤
        (φ ^ 2 * (φ⁻¹) ^ (n N)) * φ ^ 2 := by
  let r : ℝ := φ⁻¹
  let C : ℝ := φ ^ 2 * r ^ (n N)
  have hr0 : 0 ≤ r := by dsimp [r]; exact (inv_pos.mpr Real.goldenRatio_pos).le
  have hr1 : r < 1 := by dsimp [r]; exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have habs : |r| < 1 := by simpa [abs_of_nonneg hr0] using hr1
  have hg : Summable (fun j : ℕ => C * r ^ j) := by
    have h := (summable_geometric_of_abs_lt_one habs).const_smul C
    simpa only [smul_eq_mul] using h
  have hle (j : ℕ) :
      (Nat.fib (n (N + j)) : ℝ)⁻¹ ≤ C * r ^ j := by
    have hidx : n N + j ≤ n (N + j) := Q372 n hmono N j
    have hfirst := Q360 (n (N + j)) (hpos (N + j))
    have hpow : r ^ (n (N + j)) ≤ r ^ (n N + j) :=
      (pow_right_anti₀ hr0 hr1.le) hidx
    calc
      (Nat.fib (n (N + j)) : ℝ)⁻¹ ≤ φ ^ 2 * r ^ (n (N + j)) := by
        simpa [r] using hfirst
      _ ≤ φ ^ 2 * r ^ (n N + j) := by gcongr
      _ = C * r ^ j := by simp [C, pow_add]; ring
  have hf : Summable (fun j : ℕ => (Nat.fib (n (N + j)) : ℝ)⁻¹) :=
    hg.of_nonneg_of_le (fun _ => inv_nonneg.mpr (by positivity)) hle
  refine ⟨hf, ?_⟩
  have hsumle := Summable.tsum_le_tsum hle hf hg
  have hgeom : (1 - r)⁻¹ = φ ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    dsimp [r]
    field_simp [Real.goldenRatio_ne_zero]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  have hsumg : (∑' j : ℕ, C * r ^ j) = C * (1 - r)⁻¹ := by
    have h := (hasSum_geometric_of_abs_lt_one habs).const_smul C
    simpa only [smul_eq_mul] using h.tsum_eq
  rw [hsumg, hgeom] at hsumle
  simpa [C, r] using hsumle
end OMAH1Research
namespace OMAH1Research
open Filter Topology
open Real goldenRatio
open scoped BigOperators
def Q5 (n m : ℕ) : ℤ :=
  if Even n then
    if m % (2 * n) = n then 1 else 0
  else
    if m % (4 * n) = n then 1
    else if m % (4 * n) = 3 * n then -1 else 0
theorem Q278 (n m : ℕ) :
    Q5 n (m + 4 * n) = Q5 n m := by
  have h4 : (m + 4 * n) % (4 * n) = m % (4 * n) := by simp
  have h2 : (m + 4 * n) % (2 * n) = m % (2 * n) := by
    rw [show 4 * n = 2 * (2 * n) by omega]
    simp
  unfold Q5
  rw [h2, h4]
theorem Q205 (n m : ℕ) :
    |Q5 n m| ≤ 1 := by
  unfold Q5
  split_ifs <;> norm_num
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
def Q70 (n : ℕ → ℕ) (K m : ℕ) : ℤ :=
  ∑ k ∈ Finset.range K, Q5 (n k) m
theorem Q244 (n m t : ℕ) :
    Q5 n (m + t * (4 * n)) = Q5 n m := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [show m + (t + 1) * (4 * n) =
        (m + t * (4 * n)) + 4 * n by ring,
        Q278, ih]
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
theorem Q179
    (n m : ℕ) (_hn : 0 < n) (h : Q5 n m ≠ 0) :
    n ≤ m := by
  unfold Q5 at h
  split_ifs at h with he h₂ h₄ h₄' <;> try contradiction
  · have hm := Nat.mod_le m (2 * n)
    omega
  · have hm := Nat.mod_le m (4 * n)
    omega
  · have hm := Nat.mod_le m (4 * n)
    omega
theorem Q215
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n) (k : ℕ) :
    k + 1 ≤ n k := by
  have h := hmono.add_le_nat k 0
  have h0 := hpos 0
  simp only [add_zero] at h
  omega
theorem Q69
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    {m k : ℕ} (hmk : m ≤ k) :
    Q5 (n k) m = 0 := by
  by_contra hne
  have hidx := Q179 (n k) m (hpos k) hne
  have hposition := Q215 n hpos hmono k
  omega
def Q1 (n : ℕ → ℕ) (m : ℕ) : ℤ :=
  ∑ k ∈ Finset.range m, Q5 (n k) m
theorem Q35
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    {m K : ℕ} (hmK : m ≤ K) :
    Q70 n K m = Q1 n m := by
  rw [Q70, Q1]
  rw [← Finset.sum_subset (Finset.range_mono hmK)]
  intro k hkK hkm
  have hmk : m ≤ k := by
    simpa only [Finset.mem_range, not_lt] using hkm
  exact Q69 n hpos hmono hmk
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
theorem Q336 (A B : ℤ)
    (hAB : A ≠ 0 ∨ B ≠ 0) :
    (A : ℝ) + (B : ℝ) * φ ≠ 0 := by
  by_cases hB : B = 0
  · subst B
    simp only [Int.cast_zero, zero_mul, add_zero]
    exact_mod_cast hAB.resolve_right (by simp)
  · intro h
    have hrat := (irrational_iff_ne_rational φ).mp Real.goldenRatio_irrational
      (-A) B hB
    have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast hB
    apply hrat
    apply (eq_div_iff hB0).2
    push_cast
    linarith
theorem Q350 (A B : ℤ)
    (hAB : A ≠ 0 ∨ B ≠ 0) :
    (A : ℝ) + (B : ℝ) * ψ ≠ 0 := by
  by_cases hB : B = 0
  · subst B
    simp only [Int.cast_zero, zero_mul, add_zero]
    exact_mod_cast hAB.resolve_right (by simp)
  · intro h
    have hrat := (irrational_iff_ne_rational ψ).mp Real.goldenConj_irrational
      (-A) B hB
    have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast hB
    apply hrat
    apply (eq_div_iff hB0).2
    push_cast
    linarith
theorem Q337 (A B : ℤ) :
    ((A : ℝ) + (B : ℝ) * φ) * ((A : ℝ) + (B : ℝ) * ψ) =
      ((A * A + A * B - B * B : ℤ) : ℝ) := by
  calc
    ((A : ℝ) + (B : ℝ) * φ) * ((A : ℝ) + (B : ℝ) * ψ) =
        (A : ℝ) ^ 2 + (A : ℝ) * B * (φ + ψ) +
          (B : ℝ) ^ 2 * (φ * ψ) := by ring
    _ = ((A * A + A * B - B * B : ℤ) : ℝ) := by
      rw [Real.goldenRatio_add_goldenConj,
        Real.goldenRatio_mul_goldenConj]
      push_cast
      ring
theorem Q347 (A B : ℤ)
    (hAB : A ≠ 0 ∨ B ≠ 0) :
    (1 : ℝ) ≤
      |(A : ℝ) + (B : ℝ) * φ| * |(A : ℝ) + (B : ℝ) * ψ| := by
  have hφ := Q336 A B hAB
  have hψ := Q350 A B hAB
  have hnorm : A * A + A * B - B * B ≠ 0 := by
    intro h
    have hprod := Q337 A B
    rw [h, Int.cast_zero] at hprod
    exact mul_ne_zero hφ hψ hprod
  have hone : (1 : ℝ) ≤ |((A * A + A * B - B * B : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hnorm
  rw [← Q337, abs_mul] at hone
  exact hone
theorem Q276
    (A B : ℤ) (q : ℕ) (hq : 0 < q) (hAB : A ≠ 0 ∨ B ≠ 0) :
    ((q : ℝ)⁻¹) ^ 2 ≤
      |((A : ℝ) + (B : ℝ) * φ) / q| *
        |((A : ℝ) + (B : ℝ) * ψ) / q| := by
  have hbase := Q347 A B hAB
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [abs_div, abs_div, abs_of_pos hqR]
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqR
  calc
    ((q : ℝ)⁻¹) ^ 2 ≤
        (|(A : ℝ) + (B : ℝ) * φ| * |(A : ℝ) + (B : ℝ) * ψ|) *
          ((q : ℝ)⁻¹) ^ 2 := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hbase (sq_nonneg ((q : ℝ)⁻¹))
    _ = |(A : ℝ) + (B : ℝ) * φ| / q *
        (|(A : ℝ) + (B : ℝ) * ψ| / q) := by
          field_simp
end OMAH1Research
namespace OMAH1Research
open Filter Topology
open Real goldenRatio
open scoped BigOperators
set_option maxHeartbeats 800000 in
private theorem Q363
    (n : ℕ) (hn : 0 < n) (he : Even n) (j : ℕ) (r : ℝ) :
    (∑ x : Fin (2 * n),
      (Q5 n (j * (2 * n) + x) : ℝ) *
        r ^ (j * (2 * n) + x)) =
      r ^ (j * (2 * n) + n) := by
  have hnlt : n < 2 * n := by omega
  let y : Fin (2 * n) := ⟨n, hnlt⟩
  have hmod (x : Fin (2 * n)) :
      (j * (2 * n) + (x : ℕ)) % (2 * n) = x :=
    Nat.mul_add_mod_of_lt x.isLt
  have hcond (x : Fin (2 * n)) : ((x : ℕ) = n) ↔ x = y := by
    simp [y, Fin.ext_iff]
  simp only [Q5, if_pos he]
  simp_rw [hmod, hcond]
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul]
  rw [Fintype.sum_ite_eq' y]
set_option maxHeartbeats 800000 in
private theorem Q366
    (n : ℕ) (hn : 0 < n) (ho : ¬ Even n) (j : ℕ) (r : ℝ) :
    (∑ x : Fin (4 * n),
      (Q5 n (j * (4 * n) + x) : ℝ) *
        r ^ (j * (4 * n) + x)) =
      r ^ (j * (4 * n) + n) - r ^ (j * (4 * n) + 3 * n) := by
  have hnlt : n < 4 * n := by omega
  have h3nlt : 3 * n < 4 * n := by omega
  let y : Fin (4 * n) := ⟨n, hnlt⟩
  let z : Fin (4 * n) := ⟨3 * n, h3nlt⟩
  have hmod (x : Fin (4 * n)) :
      (j * (4 * n) + (x : ℕ)) % (4 * n) = x :=
    Nat.mul_add_mod_of_lt x.isLt
  have hcond (x : Fin (4 * n)) : ((x : ℕ) = n) ↔ x = y := by
    simp [y, Fin.ext_iff]
  have hcond3 (x : Fin (4 * n)) : ((x : ℕ) = 3 * n) ↔ x = z := by
    simp [z, Fin.ext_iff]
  simp only [Q5, if_neg ho]
  simp_rw [hmod, hcond, hcond3]
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, Int.cast_neg, ite_mul,
    one_mul, zero_mul, neg_mul]
  have hyz : y ≠ z := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [y, z] at hv
    omega
  calc
    (∑ x, if x = y then r ^ (j * (4 * n) + (x : ℕ))
      else if x = z then -r ^ (j * (4 * n) + (x : ℕ)) else 0) =
        (∑ x, if x = y then r ^ (j * (4 * n) + (x : ℕ)) else 0) +
        (∑ x, if x = z then -r ^ (j * (4 * n) + (x : ℕ)) else 0) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hxy : x = y
          · simp [hxy, hyz]
          · by_cases hxz : x = z <;> simp [hxy, hxz, Ne.symm hyz]
    _ = r ^ (j * (4 * n) + n) - r ^ (j * (4 * n) + 3 * n) := by
      rw [Fintype.sum_ite_eq' y, Fintype.sum_ite_eq' z]
      rfl
set_option maxHeartbeats 800000 in
theorem Q283 (n : ℕ) :
    Summable (fun m : ℕ =>
      (Q5 n m : ℝ) * (φ⁻¹) ^ m) := by
  let r : ℝ := φ⁻¹
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact (inv_pos.mpr Real.goldenRatio_pos).le
  have hr1 : r < 1 := by
    dsimp [r]
    exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  change Summable (fun m : ℕ =>
    (Q5 n m : ℝ) * r ^ m)
  have hgeom : Summable (fun m : ℕ => r ^ m) :=
    summable_geometric_of_norm_lt_one (by
      simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)
  apply Summable.of_norm_bounded hgeom
  intro m
  have hc : |(Q5 n m : ℝ)| ≤ 1 := by
    exact_mod_cast Q205 n m
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hr0]
  simpa [r] using mul_le_mul_of_nonneg_right hc (pow_nonneg hr0 m)
set_option maxHeartbeats 800000 in
theorem Q299
    (n : ℕ) (hn : 0 < n) :
    HasSum (fun m : ℕ =>
      (Q5 n m : ℝ) * (φ⁻¹) ^ m)
      ((φ⁻¹) ^ n *
        (1 - (-1 : ℝ) ^ n * (φ⁻¹) ^ (2 * n))⁻¹) := by
  let r : ℝ := φ⁻¹
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact (inv_pos.mpr Real.goldenRatio_pos).le
  have hr1 : r < 1 := by
    dsimp [r]
    exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hf : Summable (fun m : ℕ =>
      (Q5 n m : ℝ) * r ^ m) := by
    simpa [r] using Q283 n
  by_cases he : Even n
  · letI : NeZero (2 * n) := ⟨by omega⟩
    have hprod : HasSum
        (fun p : ℕ × Fin (2 * n) =>
          (Q5 n (p.1 * (2 * n) + p.2) : ℝ) *
            r ^ (p.1 * (2 * n) + p.2))
        (∑' m : ℕ, (Q5 n m : ℝ) * r ^ m) := by
      exact (Nat.divModEquiv (2 * n)).symm.hasSum_iff.mpr hf.hasSum
    have hrows : HasSum (fun j : ℕ => r ^ (j * (2 * n) + n))
        (∑' m : ℕ, (Q5 n m : ℝ) * r ^ m) := by
      apply hprod.prod_fiberwise
      intro j
      convert hasSum_fintype (fun x : Fin (2 * n) =>
        (Q5 n (j * (2 * n) + x) : ℝ) *
          r ^ (j * (2 * n) + x)) using 1
      exact (Q363 n hn he j r).symm
    have hgeom : HasSum (fun j : ℕ => r ^ (j * (2 * n) + n))
        (r ^ n * (1 - r ^ (2 * n))⁻¹) := by
      have hg := (hasSum_geometric_of_abs_lt_one
        (show |r ^ (2 * n)| < 1 by
          rw [abs_pow, abs_of_nonneg hr0]
          exact pow_lt_one₀ hr0 hr1 (by omega))).mul_left (r ^ n)
      simpa only [← pow_mul, ← pow_add, Nat.mul_comm, Nat.add_comm] using hg
    have hv := hrows.unique hgeom
    rw [Even.neg_one_pow he, one_mul]
    rw [← hv]
    simpa [r] using hf.hasSum
  · have ho : Odd n := Nat.not_even_iff_odd.mp he
    letI : NeZero (4 * n) := ⟨by omega⟩
    have hprod : HasSum
        (fun p : ℕ × Fin (4 * n) =>
          (Q5 n (p.1 * (4 * n) + p.2) : ℝ) *
            r ^ (p.1 * (4 * n) + p.2))
        (∑' m : ℕ, (Q5 n m : ℝ) * r ^ m) := by
      exact (Nat.divModEquiv (4 * n)).symm.hasSum_iff.mpr hf.hasSum
    have hrows : HasSum
        (fun j : ℕ => r ^ (j * (4 * n) + n) -
          r ^ (j * (4 * n) + 3 * n))
        (∑' m : ℕ, (Q5 n m : ℝ) * r ^ m) := by
      apply hprod.prod_fiberwise
      intro j
      convert hasSum_fintype (fun x : Fin (4 * n) =>
        (Q5 n (j * (4 * n) + x) : ℝ) *
          r ^ (j * (4 * n) + x)) using 1
      exact (Q366 n hn he j r).symm
    have hgeom : HasSum
        (fun j : ℕ => r ^ (j * (4 * n) + n) -
          r ^ (j * (4 * n) + 3 * n))
        ((r ^ n - r ^ (3 * n)) * (1 - r ^ (4 * n))⁻¹) := by
      have hg := (hasSum_geometric_of_abs_lt_one
        (show |r ^ (4 * n)| < 1 by
          rw [abs_pow, abs_of_nonneg hr0]
          exact pow_lt_one₀ hr0 hr1 (by omega))).mul_left
            (r ^ n - r ^ (3 * n))
      simpa only [sub_mul, ← pow_mul, ← pow_add, Nat.mul_comm,
        Nat.add_comm] using hg
    have hv := hrows.unique hgeom
    have h2lt : r ^ (2 * n) < 1 := pow_lt_one₀ hr0 hr1 (by omega)
    have hplus : 1 + r ^ (2 * n) ≠ 0 := by positivity
    have hminus : 1 - r ^ (4 * n) ≠ 0 := by
      have : r ^ (4 * n) < 1 := pow_lt_one₀ hr0 hr1 (by omega)
      linarith
    rw [Odd.neg_one_pow ho, neg_mul, sub_neg_eq_add, one_mul]
    change HasSum (fun m : ℕ =>
      (Q5 n m : ℝ) * r ^ m)
      (r ^ n * (1 + r ^ (2 * n))⁻¹)
    have hclosed :
        (r ^ n - r ^ (3 * n)) * (1 - r ^ (4 * n))⁻¹ =
          r ^ n * (1 + r ^ (2 * n))⁻¹ := by
      field_simp [hplus, hminus]
      rw [show r ^ (3 * n) = r ^ n * r ^ (2 * n) by
        rw [← pow_add]
        congr 1
        omega,
        show r ^ (4 * n) = r ^ (2 * n) * r ^ (2 * n) by
          rw [← pow_add]
          congr 1
          omega]
      ring
    rw [← hclosed, ← hv]
    exact hf.hasSum
set_option maxHeartbeats 800000 in
theorem Q190
    (n : ℕ) (hn : 0 < n) :
    HasSum (fun m : ℕ =>
      (Q5 n m : ℝ) * (φ⁻¹) ^ m)
      ((√5)⁻¹ * (Nat.fib n : ℝ)⁻¹) := by
  let r : ℝ := φ⁻¹
  let q : ℝ := (-1 : ℝ) ^ n * r ^ (2 * n)
  have hcoeff := Q299 n hn
  have hpsi : ψ = -r := by
    dsimp [r]
    linarith [Real.inv_goldenRatio]
  have hpsi_pow : ψ ^ n = (-1 : ℝ) ^ n * r ^ n := by
    rw [hpsi, neg_pow]
  have hunit : φ ^ n * r ^ n = 1 := by
    dsimp [r]
    rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ Real.goldenRatio_ne_zero)]
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact (inv_pos.mpr Real.goldenRatio_pos).le
  have hr1 : r < 1 := by
    dsimp [r]
    exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hqabs : |q| < 1 := by
    dsimp [q]
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_pow, abs_of_nonneg hr0]
    exact pow_lt_one₀ hr0 hr1 (by omega)
  have hqne : 1 - q ≠ 0 := by
    have habsne : |q| ≠ 1 := ne_of_lt hqabs
    intro h
    have hq : q = 1 := (sub_eq_zero.mp h).symm
    exact habsne (by rw [hq, abs_one])
  have hsqrt : √5 ≠ 0 := by positivity
  have hden : 1 - ((-1 : ℝ) ^ n * r ^ (2 * n)) ≠ 0 := by
    simpa [q] using hqne
  have hrr : r ^ n * r ^ n = r ^ (2 * n) := by
    rw [← pow_add]
    congr 1
    omega
  have hvalue :
      √5 * (r ^ n * (1 - (-1 : ℝ) ^ n * r ^ (2 * n))⁻¹) =
        (Nat.fib n : ℝ)⁻¹ := by
    symm
    apply inv_eq_of_mul_eq_one_right
    rw [Real.coe_fib_eq, hpsi_pow]
    field_simp [hden, hsqrt]
    rw [mul_sub, show r ^ n * φ ^ n = 1 by
      simpa [mul_comm] using hunit,
      show r ^ n * ((-1 : ℝ) ^ n * r ^ n) =
        (-1 : ℝ) ^ n * r ^ (2 * n) by rw [← hrr]; ring]
  have hclosed :
      r ^ n * (1 - (-1 : ℝ) ^ n * r ^ (2 * n))⁻¹ =
        (√5)⁻¹ * (Nat.fib n : ℝ)⁻¹ := by
    rw [← hvalue]
    field_simp
  change HasSum (fun m : ℕ =>
    (Q5 n m : ℝ) * r ^ m)
    (r ^ n * (1 - (-1 : ℝ) ^ n * r ^ (2 * n))⁻¹) at hcoeff
  rw [hclosed] at hcoeff
  simpa [r] using hcoeff
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
open scoped BigOperators
set_option maxHeartbeats 800000 in
private theorem Q334
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n) :
    Summable (Function.uncurry fun k m : ℕ =>
      (Q5 (n k) m : ℝ) * (φ⁻¹) ^ m) := by
  let r : ℝ := φ⁻¹
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact (inv_pos.mpr Real.goldenRatio_pos).le
  have hr1 : r < 1 := by
    dsimp [r]
    exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  let g : ℕ × ℕ → ℝ := fun p => if p.2 < p.1 then r ^ p.1 else 0
  have hg : Summable g := by
    have hg0 : ∀ p, 0 ≤ g p := by
      intro p
      dsimp [g]
      split_ifs <;> positivity
    rw [summable_prod_of_nonneg hg0]
    constructor
    · intro m
      apply summable_of_ne_finset_zero (s := Finset.range m)
      intro k hk
      simp only [Finset.mem_range, not_lt] at hk
      simp [g, hk]
    · have hrow : (fun m : ℕ => ∑' k : ℕ, g (m, k)) =
          (fun m : ℕ => (m : ℝ) * r ^ m) := by
        funext m
        rw [tsum_eq_sum (s := Finset.range m)]
        · calc
            (∑ k ∈ Finset.range m, g (m, k)) =
                ∑ _k ∈ Finset.range m, r ^ m := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  simp [g, Finset.mem_range.mp hk]
            _ = (m : ℝ) * r ^ m := by simp
        · intro k hk
          simp only [Finset.mem_range, not_lt] at hk
          simp [g, hk]
      rw [hrow]
      simpa only [pow_one] using
        (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
          (by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1))
  have hswap : Summable (fun p : ℕ × ℕ =>
      (Q5 (n p.2) p.1 : ℝ) * r ^ p.1) := by
    apply Summable.of_norm_bounded hg
    intro p
    by_cases hkm : p.2 < p.1
    · have hc : |(Q5 (n p.2) p.1 : ℝ)| ≤ 1 := by
        exact_mod_cast Q205 (n p.2) p.1
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hr0]
      simp only [g, if_pos hkm]
      simpa using mul_le_mul_of_nonneg_right hc (pow_nonneg hr0 p.1)
    · have hmk : p.1 ≤ p.2 := by omega
      have hz := Q69
        n hpos hmono hmk
      simp [hz, g, hkm]
  have horig : Summable (fun p : ℕ × ℕ =>
      (Q5 (n p.1) p.2 : ℝ) * r ^ p.2) := by
    exact ((Equiv.prodComm ℕ ℕ).summable_iff).mp (by
      simpa [Function.comp_def] using hswap)
  change Summable (fun p : ℕ × ℕ =>
    (Q5 (n p.1) p.2 : ℝ) * (φ⁻¹) ^ p.2)
  simpa [r] using horig
set_option maxHeartbeats 800000 in
private theorem Q232
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (m : ℕ) :
    (∑' k : ℕ,
      (Q5 (n k) m : ℝ) * (φ⁻¹) ^ m) =
      (Q1 n m : ℝ) * (φ⁻¹) ^ m := by
  rw [tsum_eq_sum (s := Finset.range m)]
  · rw [Q1]
    push_cast
    rw [Finset.sum_mul]
  · intro k hk
    have hmk : m ≤ k := by
      simpa only [Finset.mem_range, not_lt] using hk
    rw [Q69 n hpos hmono hmk]
    simp
set_option maxHeartbeats 800000 in
theorem Q54
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n) :
    HasSum (fun m : ℕ =>
      (Q1 n m : ℝ) * (φ⁻¹) ^ m)
      ((√5)⁻¹ * ∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹) := by
  have hd := Q334 n hpos hmono
  have hcomm := hd.tsum_comm
  have hleft :
      (∑' m : ℕ, ∑' k : ℕ,
        (Q5 (n k) m : ℝ) * (φ⁻¹) ^ m) =
      ∑' m : ℕ,
        (Q1 n m : ℝ) * (φ⁻¹) ^ m := by
    apply tsum_congr
    exact Q232 n hpos hmono
  have hright :
      (∑' k : ℕ, ∑' m : ℕ,
        (Q5 (n k) m : ℝ) * (φ⁻¹) ^ m) =
      (√5)⁻¹ * ∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹ := by
    calc
      (∑' k : ℕ, ∑' m : ℕ,
        (Q5 (n k) m : ℝ) * (φ⁻¹) ^ m) =
          ∑' k : ℕ, (√5)⁻¹ * (Nat.fib (n k) : ℝ)⁻¹ := by
            apply tsum_congr
            intro k
            exact (Q190
              (n k) (hpos k)).tsum_eq
      _ = (√5)⁻¹ * ∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹ := tsum_mul_left
  have hsum :
      (∑' m : ℕ,
        (Q1 n m : ℝ) * (φ⁻¹) ^ m) =
      (√5)⁻¹ * ∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹ := by
    rw [← hleft, hcomm, hright]
  have hsummable : Summable (fun m : ℕ =>
      (Q1 n m : ℝ) * (φ⁻¹) ^ m) := by
    have hdswap : Summable (fun p : ℕ × ℕ =>
        (Q5 (n p.2) p.1 : ℝ) * (φ⁻¹) ^ p.1) := by
      change Summable ((Function.uncurry fun k m : ℕ =>
        (Q5 (n k) m : ℝ) * (φ⁻¹) ^ m) ∘
          (Equiv.prodComm ℕ ℕ))
      exact ((Equiv.prodComm ℕ ℕ).summable_iff).mpr hd
    have hp : Summable (fun m : ℕ => ∑' k : ℕ,
        (Q5 (n k) m : ℝ) * (φ⁻¹) ^ m) := hdswap.prod
    convert hp using 1
    funext m
    exact (Q232 n hpos hmono m).symm
  rw [← hsum]
  exact hsummable.hasSum
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
open scoped BigOperators
def InScaledGoldenLattice (q : ℕ) (x : ℝ) : Prop :=
  ∃ A B : ℤ, x = ((A : ℝ) + (B : ℝ) * φ) / (q : ℝ)
theorem InScaledGoldenLattice.add {q : ℕ} (hq : 0 < q) {x y : ℝ}
    (hx : InScaledGoldenLattice q x) (hy : InScaledGoldenLattice q y) :
    InScaledGoldenLattice q (x + y) := by
  obtain ⟨A, B, rfl⟩ := hx
  obtain ⟨C, D, rfl⟩ := hy
  refine ⟨A + C, B + D, ?_⟩
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  push_cast
  field_simp
  ring
theorem InScaledGoldenLattice.neg {q : ℕ} {x : ℝ}
    (hx : InScaledGoldenLattice q x) :
    InScaledGoldenLattice q (-x) := by
  obtain ⟨A, B, rfl⟩ := hx
  refine ⟨-A, -B, ?_⟩
  push_cast
  ring
theorem InScaledGoldenLattice.sub {q : ℕ} (hq : 0 < q) {x y : ℝ}
    (hx : InScaledGoldenLattice q x) (hy : InScaledGoldenLattice q y) :
    InScaledGoldenLattice q (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hq hy.neg
theorem InScaledGoldenLattice.int_mul {q : ℕ} {x : ℝ}
    (C : ℤ) (hx : InScaledGoldenLattice q x) :
    InScaledGoldenLattice q ((C : ℝ) * x) := by
  obtain ⟨A, B, rfl⟩ := hx
  refine ⟨C * A, C * B, ?_⟩
  push_cast
  ring
theorem InScaledGoldenLattice.change_one_to_denominator
    {q : ℕ} (hq : 0 < q) {x : ℝ}
    (hx : InScaledGoldenLattice 1 x) :
    InScaledGoldenLattice q x := by
  obtain ⟨A, B, hAB⟩ := hx
  refine ⟨(q : ℤ) * A, (q : ℤ) * B, ?_⟩
  rw [hAB]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  push_cast
  field_simp
noncomputable def Q159 (C : ℕ → ℤ) (T : ℝ) (N : ℕ) : ℝ :=
  φ ^ N * T -
    ∑ m ∈ Finset.range N, (C m : ℝ) * φ ^ (N - m)
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
open scoped BigOperators
noncomputable def Q17 (C : ℕ → ℤ) (N : ℕ) : ℝ :=
  ∑' t : ℕ, (C (N + t) : ℝ) * (φ⁻¹) ^ t
private theorem Q234 (N t : ℕ) :
    φ ^ N * (φ⁻¹) ^ (t + N) = (φ⁻¹) ^ t := by
  rw [pow_add]
  have hu : φ ^ N * (φ⁻¹) ^ N = 1 := by
    rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ Real.goldenRatio_ne_zero)]
  rw [show φ ^ N * ((φ⁻¹) ^ t * (φ⁻¹) ^ N) =
    (φ⁻¹) ^ t * (φ ^ N * (φ⁻¹) ^ N) by ring, hu, mul_one]
private theorem Q326
    {N m : ℕ} (hmN : m ≤ N) :
    φ ^ N * (φ⁻¹) ^ m = φ ^ (N - m) := by
  rw [inv_pow, pow_sub₀ φ Real.goldenRatio_ne_zero hmN]
theorem Q378
    (C : ℕ → ℤ)
    (hsum : Summable (fun m : ℕ => (C m : ℝ) * (φ⁻¹) ^ m))
    (N : ℕ) :
    Summable (fun t : ℕ => (C (N + t) : ℝ) * (φ⁻¹) ^ t) := by
  have hshift : Summable (fun t : ℕ =>
      (C (t + N) : ℝ) * (φ⁻¹) ^ (t + N)) :=
    (summable_nat_add_iff N).mpr hsum
  have hmul := hshift.mul_left (φ ^ N)
  apply hmul.congr
  intro t
  rw [Nat.add_comm t N]
  rw [show φ ^ N * ((C (N + t) : ℝ) * (φ⁻¹) ^ (N + t)) =
    (C (N + t) : ℝ) * (φ ^ N * (φ⁻¹) ^ (t + N)) by
      rw [Nat.add_comm N t]
      ring,
    Q234]
theorem Q95
    (C : ℕ → ℤ) (T : ℝ)
    (hsum : HasSum (fun m : ℕ => (C m : ℝ) * (φ⁻¹) ^ m) T)
    (N : ℕ) :
    Q159 C T N = Q17 C N := by
  have hs := hsum.summable
  have hdecomp := hs.sum_add_tsum_nat_add N
  rw [hsum.tsum_eq] at hdecomp
  have hprefix :
      φ ^ N * (∑ m ∈ Finset.range N,
        (C m : ℝ) * (φ⁻¹) ^ m) =
      ∑ m ∈ Finset.range N, (C m : ℝ) * φ ^ (N - m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hmN : m ≤ N := (Finset.mem_range.mp hm).le
    rw [show φ ^ N * ((C m : ℝ) * (φ⁻¹) ^ m) =
      (C m : ℝ) * (φ ^ N * (φ⁻¹) ^ m) by ring,
      Q326 hmN]
  have htail :
      φ ^ N * (∑' t : ℕ,
        (C (t + N) : ℝ) * (φ⁻¹) ^ (t + N)) =
      Q17 C N := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro t
    rw [Nat.add_comm t N]
    rw [show φ ^ N * ((C (N + t) : ℝ) * (φ⁻¹) ^ (N + t)) =
      (C (N + t) : ℝ) * (φ ^ N * (φ⁻¹) ^ (t + N)) by
        rw [Nat.add_comm N t]
        ring,
      Q234]
  unfold Q159
  rw [← hprefix, ← htail]
  have hmuldecomp := congrArg (fun x : ℝ => φ ^ N * x) hdecomp
  rw [mul_add] at hmuldecomp
  linarith
theorem Q72
    (C : ℕ → ℤ)
    (hsum : Summable (fun m : ℕ => (C m : ℝ) * (φ⁻¹) ^ m))
    (N L : ℕ) :
    Q17 C N =
      (∑ t ∈ Finset.range L, (C (N + t) : ℝ) * (φ⁻¹) ^ t) +
        (φ⁻¹) ^ L * Q17 C (N + L) := by
  have htailSum := Q378 C hsum N
  have hdecomp := htailSum.sum_add_tsum_nat_add L
  unfold Q17
  rw [← hdecomp]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro t
  rw [show N + (t + L) = N + L + t by omega, pow_add]
  ring
theorem Q47
    (C : ℕ → ℤ)
    (hsum : Summable (fun m : ℕ => (C m : ℝ) * (φ⁻¹) ^ m))
    (N M L : ℕ)
    (hblock : ∀ t < L, C (N + t) = C (M + t)) :
    Q17 C N - Q17 C M =
      (φ⁻¹) ^ L *
        (Q17 C (N + L) - Q17 C (M + L)) := by
  rw [Q72 C hsum N L,
    Q72 C hsum M L]
  have hfinite :
      (∑ t ∈ Finset.range L, (C (N + t) : ℝ) * (φ⁻¹) ^ t) =
      ∑ t ∈ Finset.range L, (C (M + t) : ℝ) * (φ⁻¹) ^ t := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [hblock t (Finset.mem_range.mp ht)]
  rw [hfinite]
  ring
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
open scoped BigOperators
def InScaledGoldenPair (q : ℕ) (x y : ℝ) : Prop :=
  ∃ A B : ℤ,
    x = ((A : ℝ) + (B : ℝ) * φ) / (q : ℝ) ∧
    y = ((A : ℝ) + (B : ℝ) * ψ) / (q : ℝ)
theorem InScaledGoldenPair.add {q : ℕ} (hq : 0 < q)
    {x y x' y' : ℝ} (h : InScaledGoldenPair q x y)
    (h' : InScaledGoldenPair q x' y') :
    InScaledGoldenPair q (x + x') (y + y') := by
  obtain ⟨A, B, hx, hy⟩ := h
  obtain ⟨C, D, hx', hy'⟩ := h'
  refine ⟨A + C, B + D, ?_, ?_⟩
  · rw [hx, hx']
    push_cast
    field_simp
    ring
  · rw [hy, hy']
    push_cast
    field_simp
    ring
theorem InScaledGoldenPair.neg {q : ℕ} {x y : ℝ}
    (h : InScaledGoldenPair q x y) :
    InScaledGoldenPair q (-x) (-y) := by
  obtain ⟨A, B, hx, hy⟩ := h
  refine ⟨-A, -B, ?_, ?_⟩
  · rw [hx]
    push_cast
    ring
  · rw [hy]
    push_cast
    ring
theorem InScaledGoldenPair.sub {q : ℕ} (hq : 0 < q)
    {x y x' y' : ℝ} (h : InScaledGoldenPair q x y)
    (h' : InScaledGoldenPair q x' y') :
    InScaledGoldenPair q (x - x') (y - y') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact h.add hq h'.neg
theorem InScaledGoldenPair.int_mul {q : ℕ} (C : ℤ) {x y : ℝ}
    (h : InScaledGoldenPair q x y) :
    InScaledGoldenPair q ((C : ℝ) * x) ((C : ℝ) * y) := by
  obtain ⟨A, B, hx, hy⟩ := h
  refine ⟨C * A, C * B, ?_, ?_⟩
  · rw [hx]
    push_cast
    ring
  · rw [hy]
    push_cast
    ring
theorem InScaledGoldenPair.powers_mul {q : ℕ}
    {x y : ℝ} (h : InScaledGoldenPair q x y) (p : ℕ) :
    InScaledGoldenPair q (φ ^ p * x) (ψ ^ p * y) := by
  induction p with
  | zero => simpa using h
  | succ p ih =>
      obtain ⟨A, B, hx, hy⟩ := ih
      refine ⟨B, A + B, ?_, ?_⟩
      · rw [show φ ^ (p + 1) * x = φ * (φ ^ p * x) by
          rw [pow_succ]
          ring, hx]
        rw [← mul_div_assoc]
        congr 1
        push_cast
        rw [show φ * ((A : ℝ) + (B : ℝ) * φ) =
          (A : ℝ) * φ + (B : ℝ) * φ ^ 2 by ring,
          Real.goldenRatio_sq]
        ring
      · rw [show ψ ^ (p + 1) * y = ψ * (ψ ^ p * y) by
          rw [pow_succ]
          ring, hy]
        rw [← mul_div_assoc]
        congr 1
        push_cast
        rw [show ψ * ((A : ℝ) + (B : ℝ) * ψ) =
          (A : ℝ) * ψ + (B : ℝ) * ψ ^ 2 by ring,
          Real.goldenConj_sq]
        ring
theorem Q385 (p : ℕ) :
    InScaledGoldenPair 1 (φ ^ p) (ψ ^ p) := by
  have hone : InScaledGoldenPair 1 (1 : ℝ) (1 : ℝ) := by
    exact ⟨1, 0, by norm_num, by norm_num⟩
  simpa using hone.powers_mul p
theorem InScaledGoldenPair.change_one_to_denominator
    {q : ℕ} (hq : 0 < q) {x y : ℝ}
    (h : InScaledGoldenPair 1 x y) :
    InScaledGoldenPair q x y := by
  obtain ⟨A, B, hx, hy⟩ := h
  refine ⟨(q : ℤ) * A, (q : ℤ) * B, ?_, ?_⟩
  · rw [hx]
    push_cast
    field_simp
  · rw [hy]
    push_cast
    field_simp
theorem Q349
    (q : ℕ) (hq : 0 < q) (C : ℤ) (p : ℕ) :
    InScaledGoldenPair q ((C : ℝ) * φ ^ p) ((C : ℝ) * ψ ^ p) := by
  exact (Q385 p).int_mul C |>.change_one_to_denominator hq
theorem Q338
    {ι : Type*} {q : ℕ} (hq : 0 < q) (s : Finset ι)
    (f g : ι → ℝ) (hfg : ∀ i ∈ s, InScaledGoldenPair q (f i) (g i)) :
    InScaledGoldenPair q (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, by simp, by simp⟩
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (hfg a (Finset.mem_insert_self a s)).add hq
        (ih fun i hi => hfg i (Finset.mem_insert_of_mem hi))
theorem Q345
    (a : ℤ) (b : ℕ) (hb : 0 < b) :
    InScaledGoldenPair (5 * b)
      ((√5)⁻¹ * ((a : ℝ) / (b : ℝ)))
      (-((√5)⁻¹ * ((a : ℝ) / (b : ℝ)))) := by
  refine ⟨-a, 2 * a, ?_, ?_⟩
  · have hs : √(5 : ℝ) ≠ 0 := by positivity
    have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hb
    rw [show φ = (1 + √5) / 2 by rfl]
    push_cast
    field_simp
    rw [show (-1 : ℝ) + (1 + √5) = √5 by ring,
      show √5 * (a : ℝ) * √5 = (a : ℝ) * √5 ^ 2 by ring,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  · have hs : √(5 : ℝ) ≠ 0 := by positivity
    have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hb
    rw [show ψ = (1 - √5) / 2 by rfl]
    push_cast
    field_simp
    rw [show (-1 : ℝ) + (1 - √5) = -√5 by ring,
      show √5 * (a : ℝ) * (-√5) = -(a : ℝ) * √5 ^ 2 by ring,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    ring
noncomputable def Q60 (C : ℕ → ℤ)
    (Tconj : ℝ) (N : ℕ) : ℝ :=
  ψ ^ N * Tconj -
    ∑ m ∈ Finset.range N, (C m : ℝ) * ψ ^ (N - m)
theorem InScaledGoldenPair.norm_lower {q : ℕ} (hq : 0 < q)
    {x y : ℝ} (h : InScaledGoldenPair q x y) (hx : x ≠ 0) :
    ((q : ℝ)⁻¹) ^ 2 ≤ |x| * |y| := by
  obtain ⟨A, B, hxAB, hyAB⟩ := h
  have hAB : A ≠ 0 ∨ B ≠ 0 := by
    by_contra hz
    simp only [not_or, not_not] at hz
    rcases hz with ⟨rfl, rfl⟩
    simp at hxAB
    exact hx hxAB
  rw [hxAB, hyAB]
  exact Q276 A B q hq hAB
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
open scoped BigOperators
def Q49 (n : ℕ → ℕ) (m : ℕ) : Finset ℕ :=
  (Finset.range m).filter fun k => n k ≤ m
def Q41 (n : ℕ → ℕ) (m : ℕ) : ℕ :=
  (Q49 n m).card
theorem Q312
    (n : ℕ → ℕ) {a b : ℕ} (hab : a ≤ b) :
    Q49 n a ⊆ Q49 n b := by
  intro k hk
  simp only [Q49, Finset.mem_filter, Finset.mem_range] at hk ⊢
  exact ⟨lt_of_lt_of_le hk.1 hab, hk.2.trans hab⟩
theorem Q383
    (n : ℕ → ℕ) {a b : ℕ} (hab : a ≤ b) :
    Q41 n a ≤ Q41 n b :=
  Finset.card_le_card (Q312 n hab)
theorem Q365
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n) (m : ℕ) :
    Q41 n (m + 1) ≤ Q41 n m + 1 := by
  let S := Q49 n m
  let T := Q49 n (m + 1)
  have hST : S ⊆ T := Q312 n (by omega)
  have hdiff : (T \ S).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi j hj
    have hiT := (Finset.mem_sdiff.mp hi).1
    have hiS := (Finset.mem_sdiff.mp hi).2
    have hjT := (Finset.mem_sdiff.mp hj).1
    have hjS := (Finset.mem_sdiff.mp hj).2
    have hiData : i < m + 1 ∧ n i ≤ m + 1 := by
      simpa [T, Q49] using hiT
    have hjData : j < m + 1 ∧ n j ≤ m + 1 := by
      simpa [T, Q49] using hjT
    have hni : n i = m + 1 := by
      by_contra hne
      have hle : n i ≤ m := by omega
      have hipos := Q215 n hpos hmono i
      have hiMem : i ∈ S := by
        simp only [S, Q49, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hle⟩
      exact hiS hiMem
    have hnj : n j = m + 1 := by
      by_contra hne
      have hle : n j ≤ m := by omega
      have hjpos := Q215 n hpos hmono j
      have hjMem : j ∈ S := by
        simp only [S, Q49, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hle⟩
      exact hjS hjMem
    exact hmono.injective (hni.trans hnj.symm)
  have hunion := Finset.card_union_le (T \ S) S
  rw [Finset.sdiff_union_of_subset hST] at hunion
  change T.card ≤ S.card + 1
  omega
theorem Q373
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (N t : ℕ) :
    Q41 n (N + t) ≤ Q41 n N + t := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hs := Q365 n hpos hmono (N + t)
      rw [show N + (t + 1) = N + t + 1 by omega]
      omega
theorem Q126
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (m : ℕ) :
    |Q1 n m| ≤ (Q41 n m : ℤ) := by
  rw [Q1]
  calc
    |∑ k ∈ Finset.range m, Q5 (n k) m| ≤
        ∑ k ∈ Finset.range m, |Q5 (n k) m| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range m,
        if n k ≤ m then (1 : ℤ) else 0 := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hkm : n k ≤ m
      · simp only [if_pos hkm]
        exact Q205 (n k) m
      · have hz : Q5 (n k) m = 0 := by
          by_contra hne
          exact hkm (Q179
            (n k) m (hpos k) hne)
        simp [hkm, hz]
    _ = (Q41 n m : ℤ) := by
      rw [Q41, Q49]
      simp
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
open scoped BigOperators
noncomputable def Q7 (n : ℕ → ℕ) (N : ℕ) : ℝ :=
  (Q41 n N : ℝ) * (1 - φ⁻¹)⁻¹ +
    φ⁻¹ / (1 - φ⁻¹) ^ 2
noncomputable def Q6
    (n : ℕ → ℕ) (Tconj : ℝ) (N : ℕ) : ℝ :=
  |Tconj| + (Q41 n N : ℝ) * (1 - φ⁻¹)⁻¹
theorem Q42
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n) (N : ℕ) :
    |Q17 (Q1 n) N| ≤
      Q7 n N := by
  let r : ℝ := φ⁻¹
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact (inv_pos.mpr Real.goldenRatio_pos).le
  have hr1 : r < 1 := by
    dsimp [r]
    exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hrabs : |r| < 1 := by simpa [abs_of_nonneg hr0] using hr1
  let A : ℕ := Q41 n N
  let g : ℕ → ℝ := fun t => (A + t : ℕ) * r ^ t
  have hgeom : Summable (fun t : ℕ => r ^ t) :=
    summable_geometric_of_abs_lt_one hrabs
  have hlin : Summable (fun t : ℕ => (t : ℝ) * r ^ t) := by
    simpa only [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
        (by simpa [Real.norm_eq_abs] using hrabs))
  have hconst : Summable (fun t : ℕ => (A : ℝ) * r ^ t) :=
    hgeom.mul_left (A : ℝ)
  have hg : Summable g := by
    apply (hconst.add hlin).congr
    intro t
    dsimp [g]
    push_cast
    ring
  have hterm : ∀ t : ℕ,
      ‖(Q1 n (N + t) : ℝ) * r ^ t‖ ≤ g t := by
    intro t
    have hcZ := Q126 n hpos (N + t)
    have hcount := Q373 n hpos hmono N t
    have hc : |(Q1 n (N + t) : ℝ)| ≤ (A + t : ℕ) := by
      have hcR : |(Q1 n (N + t) : ℝ)| ≤
          (Q41 n (N + t) : ℝ) := by exact_mod_cast hcZ
      exact hcR.trans (by exact_mod_cast hcount)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hr0]
    exact mul_le_mul_of_nonneg_right hc (pow_nonneg hr0 t)
  have hf : Summable (fun t : ℕ =>
      (Q1 n (N + t) : ℝ) * r ^ t) :=
    Summable.of_norm_bounded hg hterm
  have hnorm := norm_tsum_le_tsum_norm hf.norm
  have hle := hf.norm.tsum_le_tsum hterm hg
  have hgvalue :
      (∑' t : ℕ, g t) =
        (A : ℝ) * (1 - r)⁻¹ + r / (1 - r) ^ 2 := by
    calc
      (∑' t : ℕ, g t) =
          ∑' t : ℕ, ((A : ℝ) * r ^ t + (t : ℝ) * r ^ t) := by
            apply tsum_congr
            intro t
            dsimp [g]
            push_cast
            ring
      _ = (∑' t : ℕ, (A : ℝ) * r ^ t) +
          ∑' t : ℕ, (t : ℝ) * r ^ t := hconst.tsum_add hlin
      _ = (A : ℝ) * (1 - r)⁻¹ + r / (1 - r) ^ 2 := by
        rw [tsum_mul_left, tsum_geometric_of_abs_lt_one hrabs,
          tsum_coe_mul_geometric_of_norm_lt_one
            (by simpa [Real.norm_eq_abs] using hrabs)]
  have hfinal := hnorm.trans hle
  rw [hgvalue] at hfinal
  change |∑' t : ℕ,
    (Q1 n (N + t) : ℝ) * r ^ t| ≤
      (A : ℝ) * (1 - r)⁻¹ + r / (1 - r) ^ 2
  rw [← Real.norm_eq_abs]
  exact hfinal
private theorem Q352 (N : ℕ) :
    (∑ m ∈ Finset.range N, |ψ| ^ (N - m)) ≤
      (1 - φ⁻¹)⁻¹ := by
  let r : ℝ := φ⁻¹
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact (inv_pos.mpr Real.goldenRatio_pos).le
  have hr1 : r < 1 := by
    dsimp [r]
    exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hrabs : |r| < 1 := by simpa [abs_of_nonneg hr0] using hr1
  have hψ : |ψ| = r := by
    dsimp [r]
    rw [Real.inv_goldenRatio, abs_of_neg Real.goldenConj_neg]
  rw [hψ]
  calc
    (∑ m ∈ Finset.range N, r ^ (N - m)) =
        ∑ j ∈ Finset.range N, r ^ (j + 1) := by
      rw [← Finset.sum_range_reflect (fun j => r ^ (j + 1)) N]
      apply Finset.sum_congr rfl
      intro m hm
      congr 1
      have hmN := Finset.mem_range.mp hm
      omega
    _ ≤ ∑ j ∈ Finset.range N, r ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      exact pow_le_pow_of_le_one hr0 hr1.le (by omega)
    _ ≤ ∑' j : ℕ, r ^ j := by
      exact (summable_geometric_of_abs_lt_one hrabs).sum_le_tsum
        (Finset.range N) (fun _ _ => pow_nonneg hr0 _)
    _ = (1 - φ⁻¹)⁻¹ := by
      simpa [r] using tsum_geometric_of_abs_lt_one hrabs
theorem Q118
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (_hmono : StrictMono n)
    (Tconj : ℝ) (N : ℕ) :
    |Q60 (Q1 n) Tconj N| ≤
      Q6 n Tconj N := by
  let A : ℕ := Q41 n N
  have hψabs1 : |ψ| ≤ 1 := by
    rw [abs_of_neg Real.goldenConj_neg]
    linarith [Real.neg_one_lt_goldenConj]
  have hfirst : |ψ ^ N * Tconj| ≤ |Tconj| := by
    rw [abs_mul, abs_pow]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (pow_le_one₀ (abs_nonneg _) hψabs1) (abs_nonneg Tconj)
  have hterm : ∀ m ∈ Finset.range N,
      |(Q1 n m : ℝ) * ψ ^ (N - m)| ≤
        (A : ℝ) * |ψ| ^ (N - m) := by
    intro m hm
    have hcZ := Q126 n hpos m
    have hcount := Q383 n (Finset.mem_range.mp hm).le
    have hc : |(Q1 n m : ℝ)| ≤ (A : ℝ) := by
      have hcR : |(Q1 n m : ℝ)| ≤
          (Q41 n m : ℝ) := by exact_mod_cast hcZ
      exact hcR.trans (by exact_mod_cast hcount)
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_right hc (pow_nonneg (abs_nonneg _) _)
  have hprefix :
      |∑ m ∈ Finset.range N,
        (Q1 n m : ℝ) * ψ ^ (N - m)| ≤
      (A : ℝ) * (1 - φ⁻¹)⁻¹ := by
    calc
      |∑ m ∈ Finset.range N,
        (Q1 n m : ℝ) * ψ ^ (N - m)| ≤
          ∑ m ∈ Finset.range N,
            |(Q1 n m : ℝ) * ψ ^ (N - m)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.range N, (A : ℝ) * |ψ| ^ (N - m) := by
        apply Finset.sum_le_sum
        exact hterm
      _ = (A : ℝ) * ∑ m ∈ Finset.range N, |ψ| ^ (N - m) := by
        rw [Finset.mul_sum]
      _ ≤ (A : ℝ) * (1 - φ⁻¹)⁻¹ := by
        exact mul_le_mul_of_nonneg_left (Q352 N)
          (by positivity)
  unfold Q60 Q6
  exact (abs_sub _ _).trans (add_le_add hfirst hprefix)
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
theorem Q224
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (N M L : ℕ)
    (hblock : ∀ t < L,
      Q1 n (N + t) =
        Q1 n (M + t)) :
    |Q17 (Q1 n) N -
      Q17 (Q1 n) M| ≤
      (φ⁻¹) ^ L *
        (Q7 n (N + L) +
          Q7 n (M + L)) := by
  have hsum := (Q54 n hpos hmono).summable
  rw [Q47
      (Q1 n) hsum N M L hblock,
    abs_mul, abs_pow, abs_of_nonneg (inv_nonneg.mpr Real.goldenRatio_pos.le)]
  apply mul_le_mul_of_nonneg_left _
    (pow_nonneg (inv_nonneg.mpr Real.goldenRatio_pos.le) _)
  exact (abs_sub _ _).trans <| add_le_add
    (Q42 n hpos hmono (N + L))
    (Q42 n hpos hmono (M + L))
theorem Q212
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (Tconj : ℝ) (N M : ℕ) :
    |Q60 (Q1 n) Tconj N -
      Q60 (Q1 n) Tconj M| ≤
      Q6 n Tconj N +
        Q6 n Tconj M := by
  exact (abs_sub _ _).trans <| add_le_add
    (Q118 n hpos hmono Tconj N)
    (Q118 n hpos hmono Tconj M)
end OMAH1Research
namespace OMAH1Research
theorem Q290
    (n : ℕ → ℕ) (_hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    {x K : ℕ} (hx : x < n K) :
    Q41 n x ≤ K := by
  have hsubset : Q49 n x ⊆ Finset.range K := by
    intro k hk
    simp only [Q49, Finset.mem_filter, Finset.mem_range] at hk
    simp only [Finset.mem_range]
    by_contra hnot
    have hKk : K ≤ k := by omega
    have hindex : n K ≤ n k := hmono.monotone hKk
    omega
  simpa [Q41] using Finset.card_le_card hsubset
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
theorem Q199
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (N M L J : ℕ)
    (hmismatch : Q1 n (N + L) ≠
      Q1 n (M + L))
    (hpost : ∀ t < J,
      Q1 n (N + L + 1 + t) =
        Q1 n (M + L + 1 + t))
    (hsmallPost :
      (φ⁻¹) ^ (J + 1) *
        (Q7 n (N + L + 1 + J) +
          Q7 n (M + L + 1 + J)) < 1) :
    Q17 (Q1 n) (N + L) ≠
      Q17 (Q1 n) (M + L) := by
  let C := Q1 n
  have hsum := (Q54 n hpos hmono).summable
  have hsplitN := Q72 C hsum (N + L) 1
  have hsplitM := Q72 C hsum (M + L) 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, mul_one, pow_one] at hsplitN hsplitM
  have hpostFactor := Q47 C hsum
    (N + L + 1) (M + L + 1) J hpost
  have hformula :
      Q17 C (N + L) - Q17 C (M + L) =
        ((C (N + L) - C (M + L) : ℤ) : ℝ) +
          (φ⁻¹) ^ (J + 1) *
            (Q17 C (N + L + 1 + J) -
              Q17 C (M + L + 1 + J)) := by
    rw [hsplitN, hsplitM]
    simp only [add_zero]
    push_cast
    calc
      (C (N + L) : ℝ) + φ⁻¹ * Q17 C (N + L + 1) -
          ((C (M + L) : ℝ) + φ⁻¹ * Q17 C (M + L + 1)) =
        ((C (N + L) : ℝ) - (C (M + L) : ℝ)) +
          φ⁻¹ * (Q17 C (N + L + 1) -
            Q17 C (M + L + 1)) := by ring
      _ = ((C (N + L) : ℝ) - (C (M + L) : ℝ)) +
          (φ⁻¹) ^ (J + 1) *
            (Q17 C (N + L + 1 + J) -
              Q17 C (M + L + 1 + J)) := by
        rw [hpostFactor, pow_succ]
        ring
  have hlater :
      |Q17 C (N + L + 1 + J) -
        Q17 C (M + L + 1 + J)| ≤
        Q7 n (N + L + 1 + J) +
          Q7 n (M + L + 1 + J) := by
    exact (abs_sub _ _).trans <| add_le_add
      (Q42 n hpos hmono
        (N + L + 1 + J))
      (Q42 n hpos hmono
        (M + L + 1 + J))
  have hr0 : 0 ≤ φ⁻¹ := inv_nonneg.mpr Real.goldenRatio_pos.le
  have hrem :
      |(φ⁻¹) ^ (J + 1) *
        (Q17 C (N + L + 1 + J) -
          Q17 C (M + L + 1 + J))| < 1 := by
    rw [abs_mul, abs_pow, abs_of_nonneg hr0]
    exact (mul_le_mul_of_nonneg_left hlater (pow_nonneg hr0 _)).trans_lt hsmallPost
  have hdZ : C (N + L) - C (M + L) ≠ 0 := sub_ne_zero.mpr hmismatch
  have hdLower : (1 : ℝ) ≤ |((C (N + L) - C (M + L) : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hdZ
  intro heq
  have hzero : Q17 C (N + L) - Q17 C (M + L) = 0 :=
    sub_eq_zero.mpr heq
  rw [hzero] at hformula
  have habsEq :
      |((C (N + L) - C (M + L) : ℤ) : ℝ)| =
      |(φ⁻¹) ^ (J + 1) *
        (Q17 C (N + L + 1 + J) -
          Q17 C (M + L + 1 + J))| := by
    rw [← abs_neg]
    congr 1
    linarith
  rw [habsEq] at hdLower
  exact (not_lt_of_ge hdLower) hrem
theorem Q182
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (N M L J : ℕ)
    (hpre : ∀ t < L,
      Q1 n (N + t) =
        Q1 n (M + t))
    (hmismatch : Q1 n (N + L) ≠
      Q1 n (M + L))
    (hpost : ∀ t < J,
      Q1 n (N + L + 1 + t) =
        Q1 n (M + L + 1 + t))
    (hsmallPost :
      (φ⁻¹) ^ (J + 1) *
        (Q7 n (N + L + 1 + J) +
          Q7 n (M + L + 1 + J)) < 1) :
    Q17 (Q1 n) N ≠
      Q17 (Q1 n) M := by
  have hsum := (Q54 n hpos hmono).summable
  have hfactor := Q47
    (Q1 n) hsum N M L hpre
  have hlater := Q199
    n hpos hmono N M L J hmismatch hpost hsmallPost
  intro heq
  have hz : Q17 (Q1 n) N -
      Q17 (Q1 n) M = 0 := sub_eq_zero.mpr heq
  rw [hz] at hfactor
  have hpne : (φ⁻¹ : ℝ) ^ L ≠ 0 :=
    pow_ne_zero _ (inv_ne_zero Real.goldenRatio_ne_zero)
  exact hlater (sub_eq_zero.mp
    (mul_eq_zero.mp hfactor.symm |>.resolve_left hpne))
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
theorem Q305
    (n m : ℕ) (h : Q5 n m ≠ 0) :
    n ∣ m := by
  unfold Q5 at h
  split_ifs at h with he h₂ h₄ h₄' <;> try contradiction
  · have hd : n ∣ 2 * n := ⟨2, by ring⟩
    have hm := Nat.mod_mod_of_dvd m hd
    rw [h₂, Nat.mod_self] at hm
    exact Nat.dvd_of_mod_eq_zero hm.symm
  · have hd : n ∣ 4 * n := ⟨4, by ring⟩
    have hm := Nat.mod_mod_of_dvd m hd
    rw [h₄, Nat.mod_self] at hm
    exact Nat.dvd_of_mod_eq_zero hm.symm
  · have hd : n ∣ 4 * n := ⟨4, by ring⟩
    have hm := Nat.mod_mod_of_dvd m hd
    rw [h₄'] at hm
    have hz : 3 * n % n = 0 := by simp
    rw [hz] at hm
    exact Nat.dvd_of_mod_eq_zero hm.symm
theorem Q32
    (n m : ℕ) (hndvd : ¬ n ∣ m) :
    Q5 n m = 0 := by
  by_contra hne
  exact hndvd (Q305 n m hne)
theorem Q100
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    {a b : ℕ}
    (hcomp : ∀ k, Q5 (n k) a = Q5 (n k) b) :
    Q1 n a = Q1 n b := by
  let Q := max a b
  have haQ : a ≤ Q := le_max_left _ _
  have hbQ : b ≤ Q := le_max_right _ _
  rw [← Q35 n hpos hmono haQ,
    ← Q35 n hpos hmono hbQ]
  unfold Q70
  apply Finset.sum_congr rfl
  intro k hk
  exact hcomp k
theorem Q214
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    {a b K : ℕ}
    (hK : Q5 (n K) a ≠ Q5 (n K) b)
    (hother : ∀ k, k ≠ K →
      Q5 (n k) a = Q5 (n k) b) :
    Q1 n a ≠ Q1 n b := by
  let Q := max (max a b) (K + 1)
  have haQ : a ≤ Q := le_trans (le_max_left _ _) (le_max_left _ _)
  have hbQ : b ≤ Q := le_trans (le_max_right _ _) (le_max_left _ _)
  have hKQ : K < Q := lt_of_lt_of_le (by omega) (le_max_right _ _)
  rw [← Q35 n hpos hmono haQ,
    ← Q35 n hpos hmono hbQ]
  unfold Q70
  intro hsum
  have hmem : K ∈ Finset.range Q := Finset.mem_range.mpr hKQ
  have hrest :
      (∑ k ∈ (Finset.range Q).erase K, Q5 (n k) a) =
      ∑ k ∈ (Finset.range Q).erase K, Q5 (n k) b := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hother k (Finset.ne_of_mem_erase hk)
  have haSplit := Finset.sum_erase_add (Finset.range Q)
    (fun k => Q5 (n k) a) hmem
  have hbSplit := Finset.sum_erase_add (Finset.range Q)
    (fun k => Q5 (n k) b) hmem
  apply hK
  omega
end OMAH1Research
namespace OMAH1Research
theorem Q371
    (a p q R : ℕ) (hq : 0 < q) :
    ((Finset.range R).filter fun t => q ∣ a + p * t).card ≤
      R / (q / q.gcd p) + 1 := by
  let S := (Finset.range R).filter fun t => q ∣ a + p * t
  let Q := q / q.gcd p
  have hQ : 0 < Q := Nat.div_pos (Nat.gcd_le_left p hq)
    (Nat.gcd_pos_of_pos_left p hq)
  have hinj : Set.InjOn (fun t : ℕ => t / Q) (S : Set ℕ) := by
    intro x hx y hy hdiv
    have hxData : x < R ∧ q ∣ a + p * x := by
      simpa [S] using hx
    have hyData : y < R ∧ q ∣ a + p * y := by
      simpa [S] using hy
    have hxmod : a + p * x ≡ 0 [MOD q] :=
      Nat.modEq_zero_iff_dvd.mpr hxData.2
    have hymod : a + p * y ≡ 0 [MOD q] :=
      Nat.modEq_zero_iff_dvd.mpr hyData.2
    have hadd : a + p * x ≡ a + p * y [MOD q] := hxmod.trans hymod.symm
    have hmul : p * x ≡ p * y [MOD q] :=
      (Nat.ModEq.refl a).add_left_cancel hadd
    have hxy : x ≡ y [MOD Q] := by
      simpa [Q, Nat.gcd_comm] using
        (Nat.ModEq.cancel_left_div_gcd hq hmul)
    have hrem : x % Q = y % Q := hxy
    change x / Q = y / Q at hdiv
    calc
      x = x % Q + Q * (x / Q) := (Nat.mod_add_div x Q).symm
      _ = y % Q + Q * (y / Q) := by rw [hrem, hdiv]
      _ = y := Nat.mod_add_div y Q
  have himage : Finset.image (fun t : ℕ => t / Q) S ⊆
      Finset.range (R / Q + 1) := by
    intro z hz
    obtain ⟨t, htS, rfl⟩ := Finset.mem_image.mp hz
    have htR : t < R := by
      have := (Finset.mem_filter.mp htS).1
      exact Finset.mem_range.mp this
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt htR))
  have hcardImage : (Finset.image (fun t : ℕ => t / Q) S).card = S.card :=
    Finset.card_image_iff.mpr hinj
  rw [← hcardImage]
  simpa [Q] using Finset.card_le_card himage
end OMAH1Research
namespace OMAH1Research
theorem Q252
    {ι : Type*} (I : Finset ι) (a q : ι → ℕ) (p R : ℕ)
    (hq : ∀ i ∈ I, 0 < q i) :
    (I.biUnion fun i =>
      (Finset.range R).filter fun t => q i ∣ a i + p * t).card ≤
      ∑ i ∈ I, (R / (q i / (q i).gcd p) + 1) := by
  classical
  calc
    (I.biUnion fun i =>
      (Finset.range R).filter fun t => q i ∣ a i + p * t).card ≤
        ∑ i ∈ I,
          ((Finset.range R).filter fun t => q i ∣ a i + p * t).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ i ∈ I, (R / (q i / (q i).gcd p) + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Q371 (a i) p (q i) R (hq i hi)
end OMAH1Research
namespace OMAH1Research
def Q0 (K H : ℕ) : Finset ℕ :=
  (Finset.range H).filter fun j => K < j
def Q56 (K H W : ℕ) : Finset ((ℕ × ℕ) × Bool) :=
  ((Q0 K H).product (Finset.range W)).product Finset.univ
def Q16 (A X : ℕ) (u : (ℕ × ℕ) × Bool) : ℕ :=
  A + u.1.2 + if u.2 then X else 0
def Q2 (n : ℕ → ℕ) (u : (ℕ × ℕ) × Bool) : ℕ :=
  n u.1.1
end OMAH1Research
namespace OMAH1Research
theorem Q198 (R q p : ℕ) (hq : 0 < q) :
    R / (q / q.gcd p) = (R * q.gcd p) / q := by
  have hg : 0 < q.gcd p := Nat.gcd_pos_of_pos_left p hq
  have hfactor : q / q.gcd p * q.gcd p = q :=
    Nat.div_mul_cancel (Nat.gcd_dvd_left q p)
  symm
  calc
    (R * q.gcd p) / q =
        (R * q.gcd p) / (q / q.gcd p * q.gcd p) := by rw [hfactor]
    _ = R / (q / q.gcd p) :=
      Nat.mul_div_mul_right (m := q.gcd p) R (q / q.gcd p) hg
end OMAH1Research
namespace OMAH1Research
theorem Q263
    (n m : ℕ) (hn : 0 < n) (h : Q5 n m ≠ 0) :
    m % (2 * n) = n := by
  unfold Q5 at h
  split_ifs at h with he h₂ h₄ h₄' <;> try contradiction
  · exact h₂
  · have hd : 2 * n ∣ 4 * n := ⟨2, by ring⟩
    have hm := Nat.mod_mod_of_dvd m hd
    rw [h₄, Nat.mod_eq_of_lt (by omega : n < 2 * n)] at hm
    exact hm.symm
  · have hd : 2 * n ∣ 4 * n := ⟨2, by ring⟩
    have hm := Nat.mod_mod_of_dvd m hd
    rw [h₄'] at hm
    have h3 : 3 * n % (2 * n) = n := by
      rw [show 3 * n = 2 * n + n by ring]
      simp [Nat.mod_eq_of_lt (by omega : n < 2 * n)]
    rw [h3] at hm
    exact hm.symm
theorem Q43
    (n m : ℕ) (hn : 0 < n) (hmod : m % (2 * n) ≠ n) :
    Q5 n m = 0 := by
  by_contra hne
  exact hmod (Q263 n m hn hne)
theorem Q308 (n : ℕ) (hn : 0 < n) :
    Q5 n n = 1 := by
  unfold Q5
  by_cases he : Even n
  · rw [if_pos he, if_pos]
    exact Nat.mod_eq_of_lt (by omega)
  · rw [if_neg he, if_pos]
    exact Nat.mod_eq_of_lt (by omega)
private theorem Q242
    (n m X r : ℕ) (hn : 0 < n) (hm : m < 2 * n)
    (hr : r = X % (2 * n))
    (hne₁ : m + r ≠ n) (hne₃ : m + r ≠ 3 * n) :
    (m + X) % (2 * n) ≠ n := by
  have hreduce : (m + X) % (2 * n) = (m + r) % (2 * n) := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt hm, ← hr]
  rw [hreduce]
  by_cases hsmall : m + r < 2 * n
  · rw [Nat.mod_eq_of_lt hsmall]
    exact hne₁
  · rw [Nat.mod_eq_sub_mod (by omega)]
    have hlt : m + r - 2 * n < 2 * n := by
      have hrlt : r < 2 * n := by
        rw [hr]
        exact Nat.mod_lt X (by omega)
      omega
    rw [Nat.mod_eq_of_lt hlt]
    intro heq
    apply hne₃
    omega
theorem Q177
    (n L J X r : ℕ) (hn : 0 < n) (hL : L < n) (hJ : J < n)
    (hr : r = X % (2 * n)) (hrLeft : L < r)
    (hrRight : r + J < 2 * n) :
    let A := n - L
    (∀ s < L,
      Q5 n (A + s + X) = Q5 n (A + s)) ∧
    Q5 n (A + L + X) ≠ Q5 n (A + L) ∧
    (∀ s < J,
      Q5 n (A + L + 1 + s + X) =
        Q5 n (A + L + 1 + s)) := by
  let A := n - L
  have hA : A + L = n := by dsimp [A]; omega
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    have hm : A + s < 2 * n := by dsimp [A]; omega
    have hbase : (A + s) % (2 * n) ≠ n := by
      rw [Nat.mod_eq_of_lt hm]
      dsimp [A]
      omega
    have hshift : (A + s + X) % (2 * n) ≠ n := by
      apply Q242 n (A + s) X r hn hm hr
      · dsimp [A]
        omega
      · have hrlt : r < 2 * n := by rw [hr]; exact Nat.mod_lt X (by omega)
        dsimp [A]
        omega
    rw [Q43 n _ hn hshift,
      Q43 n _ hn hbase]
  · rw [hA, Q308 n hn]
    have hm : n < 2 * n := by omega
    have hshift : (n + X) % (2 * n) ≠ n := by
      apply Q242 n n X r hn hm hr
      · omega
      · have hrlt : r < 2 * n := by rw [hr]; exact Nat.mod_lt X (by omega)
        omega
    rw [Q43 n _ hn hshift]
    norm_num
  · intro s hs
    have hm : A + L + 1 + s < 2 * n := by rw [hA]; omega
    have hbase : (A + L + 1 + s) % (2 * n) ≠ n := by
      rw [Nat.mod_eq_of_lt hm, hA]
      omega
    have hshift : (A + L + 1 + s + X) % (2 * n) ≠ n := by
      apply Q242 n (A + L + 1 + s) X r hn hm hr
      · rw [hA]
        omega
      · rw [hA]
        omega
    rw [Q43 n _ hn hshift,
      Q43 n _ hn hbase]
end OMAH1Research
namespace OMAH1Research
theorem Q257
    (a p q t : ℕ) (h : q ∣ a + p * t) :
    q.gcd p ∣ a := by
  have hsum : q.gcd p ∣ a + p * t :=
    dvd_trans (Nat.gcd_dvd_left q p) h
  have hpt : q.gcd p ∣ p * t :=
    dvd_mul_of_dvd_left (Nat.gcd_dvd_right q p) t
  exact (Nat.dvd_add_iff_left hpt).mpr hsum
def Q18
    (n : ℕ → ℕ) (K H W A X p : ℕ) : Finset ((ℕ × ℕ) × Bool) :=
  (Q56 K H W).filter fun u =>
    (Q2 n u).gcd p ∣ Q16 A X u
end OMAH1Research
namespace OMAH1Research
def Q11 (n : ℕ) : ℕ :=
  if Even n then 2 * n else 4 * n
theorem Q369 (n m : ℕ) :
    Q5 n (m + Q11 n) = Q5 n m := by
  by_cases he : Even n
  · simp [Q11, Q5, he]
  · simpa [Q11, he] using Q278 n m
theorem Q89 (n m t : ℕ) :
    Q5 n (m + t * Q11 n) =
      Q5 n m := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [show m + (t + 1) * Q11 n =
        (m + t * Q11 n) + Q11 n by ring,
        Q369, ih]
theorem Q94
    (n : ℕ → ℕ) (K X : ℕ)
    (hperiod : ∀ k < K, Q11 (n k) ∣ X)
    {a : ℕ} (k : ℕ) (hk : k < K) :
    Q5 (n k) (a + X) = Q5 (n k) a := by
  obtain ⟨t, ht⟩ := hperiod k hk
  subst X
  simpa [mul_comm] using
    Q89 (n k) a t
end OMAH1Research
namespace OMAH1Research
theorem Q184
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (K L J A X : ℕ)
    (hperiod : ∀ k < K, Q11 (n k) ∣ X)
    (htargetPre : ∀ s < L,
      Q5 (n K) (A + s + X) =
        Q5 (n K) (A + s))
    (htarget : Q5 (n K) (A + L + X) ≠
      Q5 (n K) (A + L))
    (htargetPost : ∀ s < J,
      Q5 (n K) (A + L + 1 + s + X) =
        Q5 (n K) (A + L + 1 + s))
    (havoid : ∀ k, K < k → ∀ u < L + 1 + J,
      (¬ n k ∣ A + u) ∧ (¬ n k ∣ A + u + X)) :
    (∀ s < L,
      Q1 n (A + s + X) =
        Q1 n (A + s)) ∧
    Q1 n (A + L + X) ≠
      Q1 n (A + L) ∧
    (∀ s < J,
      Q1 n (A + L + 1 + s + X) =
        Q1 n (A + L + 1 + s)) := by
  have hprefix (k : ℕ) (hk : k < K) (u : ℕ) :
      Q5 (n k) (A + u + X) =
        Q5 (n k) (A + u) := by
    exact Q94 n K X hperiod k hk
  have hlaterZero (k : ℕ) (hk : K < k) (u : ℕ)
      (hu : u < L + 1 + J) :
      Q5 (n k) (A + u + X) = 0 ∧
        Q5 (n k) (A + u) = 0 := by
    have ha := havoid k hk u hu
    constructor
    · exact Q32 _ _ ha.2
    · exact Q32 _ _ ha.1
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    apply Q100 n hpos hmono
    intro k
    by_cases hk₁ : k < K
    · exact hprefix k hk₁ s
    · by_cases hk₂ : k = K
      · subst k
        exact htargetPre s hs
      · have hKk : K < k := by omega
        have hz := hlaterZero k hKk s (by omega)
        rw [hz.1, hz.2]
  · apply Q214 n hpos hmono htarget
    intro k hkK
    by_cases hk : k < K
    · exact hprefix k hk L
    · have hKk : K < k := by omega
      have hz := hlaterZero k hKk L (by omega)
      rw [hz.1, hz.2]
  · intro s hs
    let u := L + 1 + s
    have hcore : Q1 n (A + u + X) =
        Q1 n (A + u) := by
      apply Q100 n hpos hmono
      intro k
      by_cases hk₁ : k < K
      · exact hprefix k hk₁ u
      · by_cases hk₂ : k = K
        · subst k
          simpa [u, add_assoc] using htargetPost s hs
        · have hKk : K < k := by omega
          have hz := hlaterZero k hKk u (by dsimp [u]; omega)
          rw [hz.1, hz.2]
    simpa [u, add_assoc] using hcore
end OMAH1Research
namespace OMAH1Research
def Q12 (n : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | K + 1 => Nat.lcm (Q12 n K) (Q11 (n K))
theorem Q71
    (n : ℕ → ℕ) {k K : ℕ} (hk : k < K) :
    Q11 (n k) ∣ Q12 n K := by
  induction K with
  | zero => omega
  | succ K ih =>
      simp only [Q12]
      by_cases h : k = K
      · subst k
        exact Nat.dvd_lcm_right _ _
      · exact dvd_trans (ih (by omega)) (Nat.dvd_lcm_left _ _)
theorem Q82
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) :
    ∀ K, 0 < Q12 n K := by
  intro K
  induction K with
  | zero => simp [Q12]
  | succ K ih =>
      simp only [Q12]
      apply Nat.lcm_pos ih
      unfold Q11
      split <;> nlinarith [hpos K]
theorem Q192
    (n : ℕ → ℕ) (B : ℕ)
    (habsorb : ∀ K, B < K →
      Q11 (n K) ∣ Q12 n K) :
    ∀ t, Q12 n (B + 1 + t) =
      Q12 n (B + 1) := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
      rw [show B + 1 + (t + 1) = (B + 1 + t) + 1 by omega,
        Q12,
        Nat.lcm_eq_left (habsorb (B + 1 + t) (by omega))]
      exact ih
theorem Q358
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (B : ℕ) :
    ∃ K, B < K ∧
      ¬ Q11 (n K) ∣ Q12 n K := by
  by_contra hnone
  push Not at hnone
  have hconst := Q192 n B hnone
  let P := Q12 n (B + 1)
  let K := B + 1 + (P + 1)
  have hBK : B < K := by dsimp [K]; omega
  have habs : Q11 (n K) ∣ Q12 n K := hnone K hBK
  have hPK : Q12 n K = P := by
    dsimp [K, P]
    exact hconst (P + 1)
  have hPpos : 0 < P := Q82 n hpos (B + 1)
  have hperiodLe : Q11 (n K) ≤ P := by
    rw [← hPK]
    exact Nat.le_of_dvd (Q82 n hpos K) habs
  have hKn : K ≤ n K := hmono.le_apply
  have hPKidx : P < K := by dsimp [K]; omega
  have hnP : P < n K := lt_of_lt_of_le hPKidx hKn
  have htwo : 2 * n K ≤ Q11 (n K) := by
    unfold Q11
    split <;> omega
  omega
end OMAH1Research
namespace OMAH1Research
theorem Q387
    (d x y : ℕ) (hx : d ∣ x) (hy : d ∣ y) :
    d ∣ x.dist y := by
  rcases le_total x y with hxy | hyx
  · rw [Nat.dist_eq_sub_of_le hxy]
    exact Nat.dvd_sub hy hx
  · rw [Nat.dist_eq_sub_of_le_right hyx]
    exact Nat.dvd_sub hx hy
theorem Q256
    (q p z A X s s₀ : ℕ) (_hq : 0 < q) (hz : 0 < z)
    (hcompat : q.gcd p ∣ A + s + X)
    (hspecial : p ∣ z * (A + s₀ + X)) :
    s = s₀ ∨ q.gcd p ≤ z * s.dist s₀ := by
  by_cases heq : s = s₀
  · exact Or.inl heq
  · right
    have hgCurrent : q.gcd p ∣ z * (A + s + X) :=
      dvd_mul_of_dvd_right hcompat z
    have hgSpecial : q.gcd p ∣ z * (A + s₀ + X) :=
      dvd_trans (Nat.gcd_dvd_right q p) hspecial
    have hd := Q387 (q.gcd p)
      (z * (A + s + X)) (z * (A + s₀ + X)) hgCurrent hgSpecial
    have hdist :
        (z * (A + s + X)).dist (z * (A + s₀ + X)) =
          z * s.dist s₀ := by
      rw [Nat.dist_mul_left]
      congr 1
      rw [show A + s + X = (A + X) + s by omega,
        show A + s₀ + X = (A + X) + s₀ by omega,
        Nat.dist_add_add_left]
    rw [hdist] at hd
    exact Nat.le_of_dvd (mul_pos hz (Nat.dist_pos_of_ne heq)) hd
theorem Q353
    (q n L s : ℕ) (hq : 0 < q) (hL : L ≤ n)
    (hcompat : q.gcd (4 * n) ∣ n - L + s) :
    s = L ∨ q.gcd (4 * n) ≤ 4 * s.dist L := by
  apply Q256 q (4 * n) 4 (n - L) 0 s L hq
    (by norm_num) (by simpa using hcompat)
  have hcenter : n - L + L = n := by omega
  rw [hcenter]
  exact ⟨1, by ring⟩
theorem Q344
    (q n A X s s₀ : ℕ) (hq : 0 < q)
    (hcompat : q.gcd (4 * n) ∣ A + s + X)
    (hspecial : 4 * n ∣ 2 * (A + s₀ + X)) :
    s = s₀ ∨ q.gcd (4 * n) ≤ 2 * s.dist s₀ := by
  exact Q256 q (4 * n) 2 A X s s₀
    hq (by norm_num) hcompat hspecial
end OMAH1Research
namespace OMAH1Research
theorem Q103
    (g Q u x : ℕ) (hg : 0 < g) (hcop : Q.Coprime u) :
    g * Q ∣ g * (u * x) ↔ Q ∣ x := by
  rw [Nat.mul_dvd_mul_iff_left hg]
  exact hcop.dvd_mul_left
theorem Q167
    (q n g Q u t : ℕ) (hg : 0 < g)
    (hq : q = g * Q) (hn : n = g * u) (hcop : Q.Coprime u) :
    q ∣ n + (4 * n) * t ↔ Q ∣ 4 * t + 1 := by
  subst q
  subst n
  rw [show g * u + 4 * (g * u) * t = g * (u * (4 * t + 1)) by ring,
    Q103 g Q u (4 * t + 1) hg hcop]
theorem Q162
    (q g Q u v t : ℕ) (hg : 0 < g)
    (hq : q = g * Q) (hcop : Q.Coprime u) :
    q ∣ g * u * (v + 1 + 2 * t) ↔ Q ∣ v + 1 + 2 * t := by
  subst q
  rw [show g * u * (v + 1 + 2 * t) =
    g * (u * (v + 1 + 2 * t)) by ring,
    Q103 g Q u (v + 1 + 2 * t) hg hcop]
end OMAH1Research
namespace OMAH1Research
theorem Q51
    (n : ℕ → ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (K r : ℕ) :
    c ^ r * (n K : ℝ) ≤ n (K + r) := by
  induction r with
  | zero => simp
  | succ r ih =>
      calc
        c ^ (r + 1) * (n K : ℝ) = c * (c ^ r * (n K : ℝ)) := by
          rw [pow_succ]
          ring
        _ ≤ c * (n (K + r) : ℝ) := by gcongr
        _ ≤ n (K + r + 1) := by
          simpa [add_assoc] using hratio (K + r)
theorem Q311
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (K : ℕ) :
    Summable (fun r : ℕ => ((n (K + 1 + r) : ℝ)⁻¹)) := by
  let ρ : ℝ := c⁻¹
  have hcpos : 0 < c := lt_trans (by norm_num) hc
  have hρpos : 0 < ρ := inv_pos.mpr hcpos
  have hρlt : ρ < 1 := by
    dsimp [ρ]
    exact (inv_lt_one₀ hcpos).2 hc
  have hρnorm : ‖ρ‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hρpos]
  have hgeom : Summable (fun r : ℕ => ρ ^ r) :=
    summable_geometric_of_norm_lt_one hρnorm
  have hmajor : Summable
      (fun r : ℕ => ρ ^ (r + 1) * (n K : ℝ)⁻¹) := by
    have h := (hgeom.mul_left ρ).mul_right (n K : ℝ)⁻¹
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using h
  apply hmajor.of_nonneg_of_le
  · intro r
    positivity
  · intro r
    have hgrowth := Q51 n c hcpos.le hratio K (r + 1)
    have hdenpos : 0 < c ^ (r + 1) * (n K : ℝ) :=
      mul_pos (pow_pos (lt_trans (by norm_num) hc) _) (by exact_mod_cast hpos K)
    have hinv : ((n (K + (r + 1)) : ℝ)⁻¹) ≤
        (c ^ (r + 1) * (n K : ℝ))⁻¹ :=
      inv_anti₀ hdenpos hgrowth
    calc
      (n (K + 1 + r) : ℝ)⁻¹ = (n (K + (r + 1)) : ℝ)⁻¹ := by
        rw [show K + 1 + r = K + (r + 1) by omega]
      _ ≤ (c ^ (r + 1) * (n K : ℝ))⁻¹ := hinv
      _ = ρ ^ (r + 1) * (n K : ℝ)⁻¹ := by
        simp [ρ, mul_inv_rev, inv_pow, mul_comm]
theorem Q377
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (K : ℕ) :
    (∑' r : ℕ, ((n (K + 1 + r) : ℝ)⁻¹)) ≤
      c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹ := by
  let ρ : ℝ := c⁻¹
  have hcpos : 0 < c := lt_trans (by norm_num) hc
  have hρpos : 0 < ρ := inv_pos.mpr hcpos
  have hρlt : ρ < 1 := by
    dsimp [ρ]
    exact (inv_lt_one₀ hcpos).2 hc
  have hρnorm : ‖ρ‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hρpos]
  have hgeom : Summable (fun r : ℕ => ρ ^ r) :=
    summable_geometric_of_norm_lt_one hρnorm
  have hmajor : Summable
      (fun r : ℕ => ρ ^ (r + 1) * (n K : ℝ)⁻¹) := by
    have h := (hgeom.mul_left ρ).mul_right (n K : ℝ)⁻¹
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using h
  have hterm (r : ℕ) : (n (K + 1 + r) : ℝ)⁻¹ ≤
      ρ ^ (r + 1) * (n K : ℝ)⁻¹ := by
    have hgrowth := Q51 n c hcpos.le hratio K (r + 1)
    have hdenpos : 0 < c ^ (r + 1) * (n K : ℝ) :=
      mul_pos (pow_pos (lt_trans (by norm_num) hc) _) (by exact_mod_cast hpos K)
    calc
      (n (K + 1 + r) : ℝ)⁻¹ = (n (K + (r + 1)) : ℝ)⁻¹ := by
        rw [show K + 1 + r = K + (r + 1) by omega]
      _ ≤ (c ^ (r + 1) * (n K : ℝ))⁻¹ := inv_anti₀ hdenpos hgrowth
      _ = ρ ^ (r + 1) * (n K : ℝ)⁻¹ := by
        simp [ρ, mul_inv_rev, inv_pow, mul_comm]
  have hsum := Q311 n hpos c hc hratio K
  calc
    (∑' r : ℕ, (n (K + 1 + r) : ℝ)⁻¹) ≤
        ∑' r : ℕ, ρ ^ (r + 1) * (n K : ℝ)⁻¹ :=
      hsum.tsum_le_tsum hterm hmajor
    _ = ρ * (1 - ρ)⁻¹ * (n K : ℝ)⁻¹ := by
      rw [show (fun r : ℕ => ρ ^ (r + 1) * (n K : ℝ)⁻¹) =
          (fun r : ℕ => (ρ * ρ ^ r) * (n K : ℝ)⁻¹) by
            funext r
            rw [pow_succ']]
      rw [tsum_mul_right, tsum_mul_left,
        tsum_geometric_of_norm_lt_one hρnorm]
    _ = c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹ := rfl
end OMAH1Research
namespace OMAH1Research
def Q23
    {ι : Type*} (C : Finset ι) (a q : ι → ℕ) (p R : ℕ) : Finset ℕ :=
  (Finset.range R).filter fun t => ∀ i ∈ C, ¬ q i ∣ a i + p * t
theorem Q154
    {ι : Type*} (C O : Finset ι) (a q : ι → ℕ) (p R : ℕ)
    (hq : ∀ i ∈ O, 0 < q i)
    (hbudget :
      (∑ i ∈ O, (R / (q i / (q i).gcd p) + 1)) <
        (Q23 C a q p R).card) :
    ∃ t < R,
      (∀ i ∈ C, ¬ q i ∣ a i + p * t) ∧
      (∀ i ∈ O, ¬ q i ∣ a i + p * t) := by
  classical
  let T := Q23 C a q p R
  let badO : Finset ℕ := O.biUnion fun i =>
    (Finset.range R).filter fun t => q i ∣ a i + p * t
  have hbadO : badO.card < T.card :=
    (Q252 O a q p R hq).trans_lt hbudget
  have hnsubset : ¬ T ⊆ badO := by
    intro hsub
    have hc := Finset.card_le_card hsub
    exact (not_le_of_gt hbadO) hc
  obtain ⟨t, htT, htbad⟩ := Finset.not_subset.mp hnsubset
  have htData := Finset.mem_filter.mp htT
  refine ⟨t, Finset.mem_range.mp htData.1, htData.2, ?_⟩
  intro i hi hdiv
  apply htbad
  apply Finset.mem_biUnion.mpr
  refine ⟨i, hi, ?_⟩
  exact Finset.mem_filter.mpr ⟨htData.1, hdiv⟩
end OMAH1Research
namespace OMAH1Research
theorem Q91
    (a p q : ℕ) (_hq : 0 < q) (hcop : q.gcd p = 1) :
    ((Finset.range q).filter fun t => q ∣ a + p * t).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  have hxData := Finset.mem_filter.mp hx
  have hyData := Finset.mem_filter.mp hy
  have hxmod : a + p * x ≡ 0 [MOD q] :=
    Nat.modEq_zero_iff_dvd.mpr hxData.2
  have hymod : a + p * y ≡ 0 [MOD q] :=
    Nat.modEq_zero_iff_dvd.mpr hyData.2
  have hadd : a + p * x ≡ a + p * y [MOD q] := hxmod.trans hymod.symm
  have hmul : p * x ≡ p * y [MOD q] :=
    (Nat.ModEq.refl a).add_left_cancel hadd
  have hxy : x ≡ y [MOD q] := Nat.ModEq.cancel_left_of_coprime hcop hmul
  exact hxy.eq_of_lt_of_lt (Finset.mem_range.mp hxData.1)
    (Finset.mem_range.mp hyData.1)
end OMAH1Research
namespace OMAH1Research
theorem Q80
    (g n M : ℕ) (hM : Odd M)
    (hfour : g ∣ 4 * n) (htwo : g ∣ 2 * n * M) :
    g ∣ 2 * n := by
  have hgcd : g ∣ (4 * n).gcd (2 * n * M) := Nat.dvd_gcd hfour htwo
  have hcop : Nat.Coprime 2 M := Nat.coprime_two_left.mpr hM
  have heq : (4 * n).gcd (2 * n * M) = 2 * n := by
    rw [show 4 * n = (2 * n) * 2 by ring,
      Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
  rwa [heq] at hgcd
theorem Q178
    (q n M : ℕ) (hq : 0 < q) (hn : 0 < n) (hnq : n < q)
    (hM : Odd M) (hcompat : q.gcd (4 * n) ∣ 2 * n * M) :
    Odd (q / q.gcd (4 * n)) ∧
      (q / q.gcd (4 * n) = 1 → q = 2 * n) := by
  let g := q.gcd (4 * n)
  let Q := q / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left (4 * n) hq
  have hgq : g ∣ q := Nat.gcd_dvd_left q (4 * n)
  have hgp : g ∣ 4 * n := Nat.gcd_dvd_right q (4 * n)
  have hg2n : g ∣ 2 * n :=
    Q80 g n M hM hgp hcompat
  have hqFactor : g * Q = q := by
    dsimp [Q]
    exact Nat.mul_div_cancel' hgq
  have hcopFull : Q.Coprime ((4 * n) / g) :=
    Nat.coprime_div_gcd_div_gcd hg
  have htwoFactor : 2 * ((2 * n) / g) = (4 * n) / g := by
    rw [show 4 * n = 2 * (2 * n) by ring,
      Nat.mul_div_assoc 2 hg2n]
  have htwoDvd : 2 ∣ (4 * n) / g := by
    rw [← htwoFactor]
    exact dvd_mul_right 2 ((2 * n) / g)
  have hcopTwo : Q.Coprime 2 :=
    hcopFull.of_dvd_right htwoDvd
  refine ⟨Nat.coprime_two_right.mp hcopTwo, ?_⟩
  intro hQ
  have hQ' : Q = 1 := by simpa [Q, g] using hQ
  have hqg : q = g := by
    rw [← hqFactor, hQ', mul_one]
  have hq2n : q ∣ 2 * n := by simpa [hqg] using hg2n
  obtain ⟨k, hk⟩ := hq2n
  have hkpos : 0 < k := by
    by_contra hk0
    have : k = 0 := Nat.eq_zero_of_not_pos hk0
    subst k
    simp at hk
    omega
  have hk1 : k = 1 := by
    by_contra hne
    have hk2 : 2 ≤ k := by omega
    have hle : 2 * q ≤ 2 * n := by
      rw [hk]
      nlinarith
    omega
  rw [hk1, mul_one] at hk
  exact hk.symm
theorem Q218
    (q n : ℕ) (hq : 0 < q) (hn : 0 < n) (hnq : n < q)
    (hcompat : q.gcd (4 * n) ∣ n) :
    Odd (q / q.gcd (4 * n)) ∧ 3 ≤ q / q.gcd (4 * n) := by
  let g := q.gcd (4 * n)
  let Q := q / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left (4 * n) hq
  have hgq : g ∣ q := Nat.gcd_dvd_left q (4 * n)
  have hgn : g ∣ n := by simpa [g] using hcompat
  have hqFactor : g * Q = q := by
    dsimp [Q]
    exact Nat.mul_div_cancel' hgq
  have hcopFull : Q.Coprime ((4 * n) / g) :=
    Nat.coprime_div_gcd_div_gcd hg
  have hfourFactor : 4 * (n / g) = (4 * n) / g := by
    rw [Nat.mul_div_assoc 4 hgn]
  have htwoDvd : 2 ∣ (4 * n) / g := by
    rw [← hfourFactor]
    exact ⟨2 * (n / g), by ring⟩
  have hoddQ : Odd Q := Nat.coprime_two_right.mp
    (hcopFull.of_dvd_right htwoDvd)
  have hQne : Q ≠ 1 := by
    intro hQ
    have hqg : q = g := by rw [← hqFactor, hQ, mul_one]
    have hqn : q ∣ n := by simpa [hqg] using hgn
    have hle := Nat.le_of_dvd hn hqn
    omega
  refine ⟨by simpa [Q, g] using hoddQ, ?_⟩
  have hQpos : 0 < Q := Nat.pos_of_ne_zero (by
    intro hQ0
    rw [hQ0, mul_zero] at hqFactor
    omega)
  have hQtwo : 2 ≤ Q := by omega
  have hQnotTwo : Q ≠ 2 := by
    intro hQ2
    rcases hoddQ with ⟨z, hz⟩
    omega
  have : 3 ≤ Q := by omega
  simpa [Q, g] using this
end OMAH1Research
namespace OMAH1Research
def Q26 (n R m : ℕ) : ℤ :=
  ∑ j ∈ Finset.range R, Q5 (n * 2 ^ j) m
theorem Q381
    (n R : ℕ) (hn : 0 < n) (hR : 0 < R) :
    Q26 n R n = 1 := by
  unfold Q26
  rw [Finset.sum_eq_single 0]
  · simpa using Q308 n hn
  · intro j hj hj0
    apply Q32
    intro hdvd
    have hle := Nat.le_of_dvd hn hdvd
    have hpow : 2 ≤ 2 ^ j := Nat.one_lt_two_pow hj0
    nlinarith
  · intro hnot
    exfalso
    apply hnot
    simp [hR]
theorem Q81
    (n R m : ℕ) (hndvd : ¬ n ∣ m) :
    Q26 n R m = 0 := by
  unfold Q26
  apply Finset.sum_eq_zero
  intro j _
  apply Q32
  intro hdvd
  apply hndvd
  exact dvd_trans (dvd_mul_right n (2 ^ j)) hdvd
end OMAH1Research
namespace OMAH1Research
def Q102 (q v : ℕ) : Finset ℕ :=
  (Finset.range q).filter fun t =>
    (¬ q ∣ 4 * t + 1) ∧ (¬ q ∣ v + 1 + 2 * t)
theorem Q323
    (q v : ℕ) (hq : 0 < q) (hodd : q.gcd 2 = 1) :
    q ≤ (Q102 q v).card + 2 := by
  classical
  let B₁ := (Finset.range q).filter fun t => q ∣ 1 + 4 * t
  let B₂ := (Finset.range q).filter fun t => q ∣ v + 1 + 2 * t
  let B := (Finset.range q).filter fun t =>
    q ∣ 4 * t + 1 ∨ q ∣ v + 1 + 2 * t
  have hcop4 : q.gcd 4 = 1 := by
    have hc2 : q.Coprime 2 := hodd
    simpa using (hc2.mul_right hc2).gcd_eq_one
  have hB₁ : B₁.card ≤ 1 := by
    dsimp [B₁]
    exact Q91 1 4 q hq hcop4
  have hB₂ : B₂.card ≤ 1 := by
    dsimp [B₂]
    exact Q91 (v + 1) 2 q hq hodd
  have hBunion : B = B₁ ∪ B₂ := by
    dsimp [B, B₁, B₂]
    rw [← Finset.filter_or]
    apply Finset.filter_congr
    intro t _
    simp [add_comm]
  have hB : B.card ≤ 2 := by
    rw [hBunion]
    calc
      (B₁ ∪ B₂).card ≤ B₁.card + B₂.card := Finset.card_union_le _ _
      _ ≤ 2 := by omega
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := Finset.range q)
    (fun t => q ∣ 4 * t + 1 ∨ q ∣ v + 1 + 2 * t)
  have hsafe :
      ((Finset.range q).filter fun t =>
        ¬(q ∣ 4 * t + 1 ∨ q ∣ v + 1 + 2 * t)) =
        Q102 q v := by
    ext t
    simp [Q102]
  have hpart : B.card + (Q102 q v).card = q := by
    rw [← hsafe]
    simpa [B] using hpartition
  omega
theorem Q320
    (q v : ℕ) (hq : 3 ≤ q) (hodd : q.gcd 2 = 1) :
    q - 2 ≤ (Q102 q v).card := by
  have h := Q323 q v (by omega) hodd
  omega
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
def Q46
    {r : ℕ} (p : Fin r → ℕ) (v : ℕ) : Finset ℕ :=
  (Finset.range (∏ i, p i)).filter fun t =>
    ∀ i, (¬ p i ∣ 4 * t + 1) ∧ (¬ p i ∣ v + 1 + 2 * t)
theorem Q292
    {r : ℕ} (p : Fin r → ℕ) (v : ℕ)
    (hp : ∀ i, 0 < p i)
    (hpair : ∀ i j, i ≠ j → (p i).Coprime (p j)) :
    (∏ i, (Q102 (p i) v).card) ≤
      (Q46 p v).card := by
  classical
  let S : Finset (Fin r) := Finset.univ
  have hpne : ∀ i ∈ S, p i ≠ 0 := by
    intro i _
    exact Nat.ne_of_gt (hp i)
  have hpairS : Set.Pairwise S (fun i j => (p i).Coprime (p j)) := by
    intro i _ j _ hij
    exact hpair i j hij
  let α := ∀ i : Fin r, {x // x ∈ Q102 (p i) v}
  let crt (x : α) : ℕ :=
    Nat.chineseRemainderOfFinset (fun i => (x i : ℕ)) p S hpne hpairS
  have hcrt_lt (x : α) : crt x < ∏ i, p i := by
    have h := Nat.chineseRemainderOfFinset_lt_prod
      (fun i => (x i : ℕ)) p hpne hpairS
    simpa [crt, S] using h
  have hcrt_safe (x : α) (i : Fin r) :
      (¬ p i ∣ 4 * crt x + 1) ∧
      (¬ p i ∣ v + 1 + 2 * crt x) := by
    have hz : crt x ≡ (x i : ℕ) [MOD p i] := by
      exact (Nat.chineseRemainderOfFinset
        (fun j => (x j : ℕ)) p S hpne hpairS).property i (by simp [S])
    have hx := Finset.mem_filter.mp (x i).property
    have hlin₁ : 4 * crt x + 1 ≡ 4 * (x i : ℕ) + 1 [MOD p i] :=
      (hz.mul_left 4).add_right 1
    have hlin₂ : v + 1 + 2 * crt x ≡
        v + 1 + 2 * (x i : ℕ) [MOD p i] :=
      (Nat.ModEq.refl (v + 1)).add (hz.mul_left 2)
    constructor
    · intro hd
      exact hx.2.1 ((hlin₁.dvd_iff dvd_rfl).mp hd)
    · intro hd
      exact hx.2.2 ((hlin₂.dvd_iff dvd_rfl).mp hd)
  let f : α → {t // t ∈ Q46 p v} := fun x =>
    ⟨crt x, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (hcrt_lt x), fun i => hcrt_safe x i⟩⟩
  have hf : Function.Injective f := by
    intro x y hxy
    funext i
    apply Subtype.ext
    have hzx : (crt x) ≡ (x i : ℕ) [MOD p i] :=
      (Nat.chineseRemainderOfFinset
        (fun j => (x j : ℕ)) p S hpne hpairS).property i (by simp [S])
    have hzy : (crt y) ≡ (y i : ℕ) [MOD p i] :=
      (Nat.chineseRemainderOfFinset
        (fun j => (y j : ℕ)) p S hpne hpairS).property i (by simp [S])
    have hcrt : crt x = crt y := congrArg Subtype.val hxy
    have hmod : (x i : ℕ) ≡ (y i : ℕ) [MOD p i] := by
      exact hzx.symm.trans (by simpa [hcrt] using hzy)
    have hxlt : (x i : ℕ) < p i :=
      Finset.mem_range.mp (Finset.mem_filter.mp (x i).property).1
    have hylt : (y i : ℕ) < p i :=
      Finset.mem_range.mp (Finset.mem_filter.mp (y i).property).1
    exact hmod.eq_of_lt_of_lt hxlt hylt
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe] at hcard
  simpa [α, Fintype.card_pi, Q46] using hcard
theorem Q273
    {r : ℕ} (p : Fin r → ℕ) (v : ℕ)
    (hp3 : ∀ i, 3 ≤ p i)
    (hodd : ∀ i, (p i).gcd 2 = 1)
    (hpair : ∀ i j, i ≠ j → (p i).Coprime (p j)) :
    (∏ i, (p i - 2)) ≤ (Q46 p v).card := by
  calc
    (∏ i, (p i - 2)) ≤ ∏ i, (Q102 (p i) v).card := by
      apply Finset.prod_le_prod
      · intro i hi
        exact Nat.zero_le _
      · intro i hi
        exact Q320 (p i) v (hp3 i) (hodd i)
    _ ≤ (Q46 p v).card :=
      Q292 p v
        (fun i => lt_of_lt_of_le (by norm_num) (hp3 i)) hpair
end OMAH1Research
namespace OMAH1Research
def Q20 (Q : Finset ℕ) : Finset ℕ :=
  Q.image Nat.minFac
theorem Q66
    (Q : Finset ℕ) (p : ℕ) :
    p ∈ Q20 Q ↔ ∃ q ∈ Q, q.minFac = p := by
  simp [Q20]
theorem Q163
    (Q : Finset ℕ)
    (hQ3 : ∀ q ∈ Q, 3 ≤ q)
    (hQodd : ∀ q ∈ Q, Odd q) :
    ∀ p ∈ Q20 Q,
      p.Prime ∧ Odd p ∧ 3 ≤ p := by
  intro p hp
  obtain ⟨q, hqQ, hqp⟩ := Q66 Q p |>.mp hp
  subst p
  have hq3 := hQ3 q hqQ
  have hqne : q ≠ 1 := by omega
  have hpprime : q.minFac.Prime := Nat.minFac_prime hqne
  have hpne2 : q.minFac ≠ 2 := by
    intro heq
    have htwo : 2 ∣ q := by simpa [← heq] using Nat.minFac_dvd q
    have heven : Even q := even_iff_two_dvd.mpr htwo
    exact (Nat.not_even_iff_odd.mpr (hQodd q hqQ)) heven
  have hpodd : Odd q.minFac := by
    exact Nat.coprime_two_right.mp
      ((Nat.coprime_primes hpprime Nat.prime_two).mpr hpne2)
  exact ⟨hpprime, hpodd, by
    have := hpprime.two_le
    omega⟩
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
theorem Q111
    (S : Finset ℕ) (hmin : ∀ p ∈ S, 3 ≤ p) :
    2 * (∏ p ∈ S, p) ≤
      (S.card + 1) * (S.card + 2) * (∏ p ∈ S, (p - 2)) := by
  classical
  have main : ∀ k : ℕ, ∀ T : Finset ℕ, T.card = k →
      (∀ p ∈ T, 3 ≤ p) →
      2 * (∏ p ∈ T, p) ≤
        (T.card + 1) * (T.card + 2) * (∏ p ∈ T, (p - 2)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro T hcard hTmin
        by_cases hT : T.Nonempty
        · let m := T.max' hT
          let U := T.erase m
          have hmT : m ∈ T := Finset.max'_mem T hT
          have hUcard : U.card = k - 1 := by
            dsimp [U]
            rw [Finset.card_erase_of_mem hmT, hcard]
          have hkpos : 0 < k := by
            rw [← hcard]
            exact Finset.card_pos.mpr hT
          have hUcardlt : U.card < k := by omega
          have hUmin : ∀ p ∈ U, 3 ≤ p := by
            intro p hp
            exact hTmin p (Finset.mem_of_mem_erase hp)
          have hIH := ih U.card hUcardlt U rfl hUmin
          have hUsub : U ⊆ Finset.Ico 3 m := by
            intro p hp
            have hpT := Finset.mem_of_mem_erase hp
            have hpmle : p ≤ m := Finset.le_max' T p hpT
            have hpne : p ≠ m := Finset.ne_of_mem_erase hp
            exact Finset.mem_Ico.mpr ⟨hTmin p hpT, lt_of_le_of_ne hpmle hpne⟩
          have hUbound : U.card ≤ m - 3 := by
            have hc := Finset.card_le_card hUsub
            simpa using hc
          have hm3 : 3 ≤ m := hTmin m hmT
          have hmrank : U.card + 3 ≤ m := by omega
          have hfactor : (U.card + 1) * m ≤
              (U.card + 3) * (m - 2) := by
            obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hmrank
            rw [hd]
            have hsub : U.card + 3 + d - 2 = U.card + 1 + d := by omega
            rw [hsub]
            nlinarith
          have hprod : (∏ p ∈ T, p) = (∏ p ∈ U, p) * m := by
            symm
            exact Finset.prod_erase_mul T (fun p => p) hmT
          have hprodSub : (∏ p ∈ T, (p - 2)) =
              (∏ p ∈ U, (p - 2)) * (m - 2) := by
            symm
            exact Finset.prod_erase_mul T (fun p => p - 2) hmT
          rw [hprod, hprodSub]
          have hkcard : T.card = U.card + 1 := by omega
          rw [hkcard]
          calc
            2 * ((∏ p ∈ U, p) * m) =
                (2 * (∏ p ∈ U, p)) * m := by ring
            _ ≤ ((U.card + 1) * (U.card + 2) *
                  (∏ p ∈ U, (p - 2))) * m :=
              Nat.mul_le_mul_right m hIH
            _ = (U.card + 2) * (∏ p ∈ U, (p - 2)) *
                  ((U.card + 1) * m) := by ring
            _ ≤ (U.card + 2) * (∏ p ∈ U, (p - 2)) *
                  ((U.card + 3) * (m - 2)) :=
              Nat.mul_le_mul_left _ hfactor
            _ = (U.card + 1 + 1) * (U.card + 1 + 2) *
                  ((∏ p ∈ U, (p - 2)) * (m - 2)) := by ring
        · have hEmpty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
          subst T
          norm_num
  exact main S.card S rfl hmin
end OMAH1Research
namespace OMAH1Research
theorem Q168
    (S : Finset ℕ) (v : ℕ)
    (hprime : ∀ p ∈ S, p.Prime)
    (hodd : ∀ p ∈ S, Odd p) :
    ∃ p : Fin S.card → ℕ,
      (∏ i, p i) = ∏ q ∈ S, q ∧
      (∀ i, (p i).Prime) ∧
      (∀ i, 3 ≤ p i) ∧
      (∀ i, (p i).gcd 2 = 1) ∧
      (∀ i j, i ≠ j → (p i).Coprime (p j)) ∧
      (∀ q ∈ S, ∃ i, p i = q) ∧
      2 * (∏ i, p i) ≤
        (S.card + 1) * (S.card + 2) *
          (Q46 p v).card := by
  classical
  let e : Fin S.card ≃ {x // x ∈ S} :=
    (Fin.castOrderIso (Fintype.card_coe S).symm).toEquiv.trans
      (Fintype.equivFin {x // x ∈ S}).symm
  let p : Fin S.card → ℕ := fun i => (e i : ℕ)
  have hpMem (i : Fin S.card) : p i ∈ S := (e i).property
  have hpPrime (i : Fin S.card) : (p i).Prime := hprime (p i) (hpMem i)
  have hpOdd (i : Fin S.card) : Odd (p i) := hodd (p i) (hpMem i)
  have hp3 (i : Fin S.card) : 3 ≤ p i := by
    have h2 := (hpPrime i).two_le
    have hne : p i ≠ 2 := by
      intro heq
      have heven : Even (p i) := by rw [heq]; norm_num
      exact (Nat.not_even_iff_odd.mpr (hpOdd i)) heven
    omega
  have hpPair : ∀ i j, i ≠ j → (p i).Coprime (p j) := by
    intro i j hij
    apply (Nat.coprime_primes (hpPrime i) (hpPrime j)).mpr
    intro hpij
    apply hij
    exact e.injective (Subtype.ext hpij)
  have hprod : (∏ i, p i) = ∏ q ∈ S, q := by
    calc
      (∏ i, p i) = ∏ x : {x // x ∈ S}, (x : ℕ) :=
        Equiv.prod_comp e (fun x : {x // x ∈ S} => (x : ℕ))
      _ = ∏ q ∈ S, q := Finset.prod_coe_sort S (fun q => q)
  have hprodSub : (∏ i, (p i - 2)) = ∏ q ∈ S, (q - 2) := by
    calc
      (∏ i, (p i - 2)) = ∏ x : {x // x ∈ S}, ((x : ℕ) - 2) :=
        Equiv.prod_comp e (fun x : {x // x ∈ S} => ((x : ℕ) - 2))
      _ = ∏ q ∈ S, (q - 2) := Finset.prod_coe_sort S (fun q => q - 2)
  have hglobal : (∏ i, (p i - 2)) ≤
      (Q46 p v).card :=
    Q273 p v hp3
      (fun i => Nat.coprime_two_right.mpr (hpOdd i) |>.gcd_eq_one) hpPair
  have hS3 : ∀ q ∈ S, 3 ≤ q := by
    intro q hq
    have hq2 := (hprime q hq).two_le
    have hqne : q ≠ 2 := by
      intro heq
      have heven : Even q := by rw [heq]; norm_num
      exact (Nat.not_even_iff_odd.mpr (hodd q hq)) heven
    omega
  have hdensity := Q111 S hS3
  have honto : ∀ q ∈ S, ∃ i, p i = q := by
    intro q hq
    obtain ⟨i, hi⟩ := e.surjective ⟨q, hq⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  refine ⟨p, hprod, hpPrime, hp3, ?_, hpPair, honto, ?_⟩
  · intro i
    exact (Nat.coprime_two_right.mpr (hpOdd i)).gcd_eq_one
  · calc
      2 * (∏ i, p i) = 2 * (∏ q ∈ S, q) := by rw [hprod]
      _ ≤ (S.card + 1) * (S.card + 2) * (∏ q ∈ S, (q - 2)) :=
        hdensity
      _ = (S.card + 1) * (S.card + 2) * (∏ i, (p i - 2)) := by
        rw [hprodSub]
      _ ≤ (S.card + 1) * (S.card + 2) *
          (Q46 p v).card :=
        Nat.mul_le_mul_left _ hglobal
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
def Q84
    {r : ℕ} (p : Fin r → ℕ) (v T : ℕ) : Finset ℕ :=
  ((Finset.range T).product (Q46 p v)).image fun z =>
    z.2 + (∏ i, p i) * z.1
lemma Q288
    {r : ℕ} (p : Fin r → ℕ) (v T : ℕ)
    (hM : 0 < ∏ i, p i) :
    (Q84 p v T).card =
      T * (Q46 p v).card := by
  classical
  unfold Q84
  rw [Finset.card_image_of_injOn]
  · simp
  · intro z hz w hw hzw
    have hzlt : z.2 < ∏ i, p i :=
      Finset.mem_range.mp (Finset.mem_filter.mp
        (Finset.mem_product.mp hz).2).1
    have hwlt : w.2 < ∏ i, p i :=
      Finset.mem_range.mp (Finset.mem_filter.mp
        (Finset.mem_product.mp hw).2).1
    have hrem := congrArg (fun x => x % (∏ i, p i)) hzw
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hzlt,
      Nat.mod_eq_of_lt hwlt] at hrem
    have hblock : z.1 = w.1 := by
      change z.2 + (∏ i, p i) * z.1 =
        w.2 + (∏ i, p i) * w.1 at hzw
      rw [hrem] at hzw
      exact Nat.mul_left_cancel hM (Nat.add_left_cancel hzw)
    cases z
    cases w
    simp_all
end OMAH1Research
namespace OMAH1Research
def Q28
    (n : ℕ → ℕ) (K H W A X p L sR : ℕ) :
    Finset ((ℕ × ℕ) × Bool) :=
  (Q18 n K H W A X p).filter fun u =>
    (u.2 = false ∧ u.1.2 = L) ∨ (u.2 = true ∧ u.1.2 = sR)
def Q188
    (n : ℕ → ℕ) (K H W A X p L sR : ℕ) :
    Finset ((ℕ × ℕ) × Bool) :=
  Q18 n K H W A X p \
    (Q28 n K H W A X p L sR)
def Q29
    (n : ℕ → ℕ) (K H W A X p L sR : ℕ) : Finset ℕ :=
  (Q28 n K H W A X p L sR).image fun u =>
    Q2 n u / (Q2 n u).gcd p
lemma Q65
    (q p d : ℕ) (hq : 0 < q) (hd : q.gcd p ∣ d) (hdp : d ∣ p) :
    (q / q.gcd p).Coprime (d / q.gcd p) := by
  let g := q.gcd p
  have hg : 0 < g := Nat.gcd_pos_of_pos_left p hq
  have hcop : (q / g).Coprime (p / g) :=
    Nat.coprime_div_gcd_div_gcd hg
  apply hcop.of_dvd_right
  apply (Nat.dvd_div_iff_mul_dvd (Nat.gcd_dvd_right q p)).mpr
  rw [Nat.mul_div_cancel' hd]
  exact hdp
theorem Q357
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (K H L J X r v R : ℕ) (hL : L < n K)
    (hX : X = r + (2 * n K) * v)
    (hrUpper : r ≤ n K + L)
    (hsRWindow : n K + L - r < L + 1 + J) :
    let A := n K - L
    let W := L + 1 + J
    let p := 4 * n K
    let sR := n K + L - r
    let O := Q188 n K H W A X p L sR
    (∑ u ∈ O, (R / (Q2 n u /
      (Q2 n u).gcd p) + 1)) ≤
      2 * W * ∑ j ∈ Q0 K H,
        ((R * (4 * W)) / n j + 1) := by
  classical
  let A := n K - L
  let W := L + 1 + J
  let p := 4 * n K
  let sR := n K + L - r
  let C := Q28 n K H W A X p L sR
  let I := Q18 n K H W A X p
  let O := Q188 n K H W A X p L sR
  have hcenterLeft : A + L = n K := by dsimp [A]; omega
  have hcenterRight : A + sR + X = 2 * n K * (v + 1) := by
    have hsrr : sR + r = n K + L := by dsimp [sR]; omega
    rw [hX]
    calc
      A + sR + (r + 2 * n K * v) =
          2 * n K + 2 * n K * v := by
        dsimp [A]
        omega
      _ = 2 * n K * (v + 1) := by ring
  have hspecialRight : 4 * n K ∣ 2 * (A + sR + X) := by
    rw [hcenterRight]
    exact ⟨v + 1, by ring⟩
  have hOsub : O ⊆ Q56 K H W := by
    intro u hu
    have huI : u ∈ I := (Finset.mem_sdiff.mp hu).1
    exact (Finset.mem_filter.mp huI).1
  have hgcd : ∀ u ∈ O,
      (Q2 n u).gcd p ≤ 4 * W := by
    intro u huO
    have huData := Finset.mem_sdiff.mp huO
    have huI := huData.1
    have huNotC := huData.2
    have huBase := (Finset.mem_filter.mp huI).1
    have huComp := (Finset.mem_filter.mp huI).2
    have huInner := (Finset.mem_product.mp huBase).1
    have huPair := Finset.mem_product.mp huInner
    have hsW := Finset.mem_range.mp huPair.2
    by_cases hside : u.2 = false
    · have hcomp : (n u.1.1).gcd (4 * n K) ∣ n K - L + u.1.2 := by
        simpa [Q2, Q16, p, A, hside] using huComp
      have hne : u.1.2 ≠ L := by
        intro heq
        apply huNotC
        apply Finset.mem_filter.mpr
        exact ⟨huI, Or.inl ⟨hside, heq⟩⟩
      have hbound := (Q353
        (n u.1.1) (n K) L u.1.2 (hpos u.1.1) hL.le hcomp).resolve_left hne
      have hdist : u.1.2.dist L ≤ W := by
        have hLW : L < W := by dsimp [W]; omega
        rcases le_total u.1.2 L with hle | hge
        · rw [Nat.dist_eq_sub_of_le hle]
          omega
        · rw [Nat.dist_eq_sub_of_le_right hge]
          omega
      dsimp [Q2, p]
      exact hbound.trans (Nat.mul_le_mul_left 4 hdist)
    · have hsideTrue : u.2 = true := Bool.eq_true_of_not_eq_false hside
      have hcomp : (n u.1.1).gcd (4 * n K) ∣
          A + u.1.2 + X := by
        simpa [Q2, Q16, p, hsideTrue] using huComp
      have hne : u.1.2 ≠ sR := by
        intro heq
        apply huNotC
        apply Finset.mem_filter.mpr
        exact ⟨huI, Or.inr ⟨hsideTrue, heq⟩⟩
      have hbound := (Q344
        (n u.1.1) (n K) A X u.1.2 sR (hpos u.1.1)
          hcomp hspecialRight).resolve_left hne
      have hdist : u.1.2.dist sR ≤ W := by
        rcases le_total u.1.2 sR with hle | hge
        · rw [Nat.dist_eq_sub_of_le hle]
          omega
        · rw [Nat.dist_eq_sub_of_le_right hge]
          omega
      dsimp [Q2, p]
      exact hbound.trans <| calc
        2 * u.1.2.dist sR ≤ 2 * W := Nat.mul_le_mul_left 2 hdist
        _ ≤ 4 * W := by omega
  calc
    (∑ u ∈ O, (R / (Q2 n u /
        (Q2 n u).gcd p) + 1)) =
        ∑ u ∈ O, ((R * (Q2 n u).gcd p) /
          Q2 n u + 1) := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [Q198 R (Q2 n u) p]
            exact hpos u.1.1
    _ ≤ ∑ u ∈ O, ((R * (4 * W)) / Q2 n u + 1) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Nat.add_le_add_right
      apply Nat.div_le_div_right
      exact Nat.mul_le_mul_left R (hgcd u hu)
    _ ≤ ∑ u ∈ Q56 K H W,
        ((R * (4 * W)) / Q2 n u + 1) :=
      Finset.sum_le_sum_of_subset hOsub
    _ = 2 * W * ∑ j ∈ Q0 K H,
        ((R * (4 * W)) / n j + 1) := by
      simp [Q56, Q2, Finset.sum_product]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
def Q248 (G H W : ℕ) :
    Finset ((ℕ × ℕ) × Bool) :=
  ((Finset.Ico G H).product (Finset.range W)).product Finset.univ
theorem Q298
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (K G H L J X r v R : ℕ) (_hKG : K < G) (_hGH : G ≤ H)
    (hL : L < n K) (hX : X = r + (2 * n K) * v)
    (hrUpper : r ≤ n K + L)
    (hsRWindow : n K + L - r < L + 1 + J) :
    let A := n K - L
    let W := L + 1 + J
    let p := 4 * n K
    let sR := n K + L - r
    let C0 := Q28 n K G W A X p L sR
    let O := Q18 n K H W A X p \ C0
    (∑ u ∈ O, (R / (Q2 n u /
      (Q2 n u).gcd p) + 1)) ≤
      2 * W * ∑ j ∈ Q0 K H,
        ((R * (4 * W)) / n j + 1) +
      2 * W * ∑ j ∈ Finset.Ico G H,
        ((R * (4 * n K)) / n j + 1) := by
  classical
  let A := n K - L
  let W := L + 1 + J
  let p := 4 * n K
  let sR := n K + L - r
  let C0 := Q28 n K G W A X p L sR
  let I := Q18 n K H W A X p
  let O := I \ C0
  let Oall := Q188 n K H W A X p L sR
  let Late := Q248 G H W
  have hOsub : O ⊆ Oall ∪ Late := by
    intro u huO
    have huData := Finset.mem_sdiff.mp huO
    have huI := huData.1
    have huNotC0 := huData.2
    by_cases huCH : u ∈ Q28 n K H W A X p L sR
    · apply Finset.mem_union.mpr
      right
      have huCompat := (Finset.mem_filter.mp huCH).1
      have huCenter := (Finset.mem_filter.mp huCH).2
      have huBase := (Finset.mem_filter.mp huCompat).1
      have huOuter := Finset.mem_product.mp huBase
      have huInner := Finset.mem_product.mp huOuter.1
      have hjRange := Finset.mem_filter.mp huInner.1
      have hjH := Finset.mem_range.mp hjRange.1
      have hKGj := hjRange.2
      have hGj : G ≤ u.1.1 := by
        by_contra hnot
        have hjG : u.1.1 < G := by omega
        apply huNotC0
        apply Finset.mem_filter.mpr
        refine ⟨?_, huCenter⟩
        apply Finset.mem_filter.mpr
        refine ⟨?_, (Finset.mem_filter.mp huCompat).2⟩
        simp [Q56, Q0, hjG, hKGj,
          Finset.mem_range.mp huInner.2]
      simp [Late, Q248, hGj, hjH,
        Finset.mem_range.mp huInner.2]
    · apply Finset.mem_union.mpr
      left
      exact Finset.mem_sdiff.mpr ⟨huI, huCH⟩
  let cost : ((ℕ × ℕ) × Bool) → ℕ := fun u =>
    R / (Q2 n u / (Q2 n u).gcd p) + 1
  have hsplit : (∑ u ∈ O, cost u) ≤
      (∑ u ∈ Oall, cost u) + ∑ u ∈ Late, cost u := by
    calc
      (∑ u ∈ O, cost u) ≤ ∑ u ∈ Oall ∪ Late, cost u :=
        Finset.sum_le_sum_of_subset hOsub
      _ ≤ (∑ u ∈ Oall, cost u) + ∑ u ∈ Late, cost u := by
        have hu := Finset.sum_union_inter (s₁ := Oall) (s₂ := Late)
          (f := cost)
        omega
  have hoff := Q357
    n hpos K H L J X r v R hL hX hrUpper hsRWindow
  have hlate : (∑ u ∈ Late, cost u) ≤
      2 * W * ∑ j ∈ Finset.Ico G H,
        ((R * (4 * n K)) / n j + 1) := by
    have hgcd (u : (ℕ × ℕ) × Bool) :
        (Q2 n u).gcd p ≤ 4 * n K := by
      dsimp [p]
      exact Nat.gcd_le_right _ (mul_pos (by norm_num) (hpos K))
    calc
      (∑ u ∈ Late, cost u) =
          ∑ u ∈ Late, ((R * (Q2 n u).gcd p) /
            Q2 n u + 1) := by
              apply Finset.sum_congr rfl
              intro u hu
              dsimp [cost]
              rw [Q198 R (Q2 n u) p]
              exact hpos u.1.1
      _ ≤ ∑ u ∈ Late, ((R * (4 * n K)) /
          Q2 n u + 1) := by
            apply Finset.sum_le_sum
            intro u hu
            apply Nat.add_le_add_right
            apply Nat.div_le_div_right
            exact Nat.mul_le_mul_left R (hgcd u)
      _ = 2 * W * ∑ j ∈ Finset.Ico G H,
          ((R * (4 * n K)) / n j + 1) := by
            simp [Late, Q248, Q2,
              Finset.sum_product]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
  dsimp [O, I, C0, cost] at hsplit ⊢
  exact hsplit.trans (Nat.add_le_add hoff hlate)
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
set_option maxHeartbeats 1200000 in
lemma Q88
    {α : Type*} (I : Finset α) (q : α → ℕ)
    (_hq : ∀ i ∈ I, 0 < q i) (A : ℕ) :
    ((∑ i ∈ I, (A / q i + 1) : ℕ) : ℝ) ≤
      (A : ℝ) * (∑ i ∈ I, ((q i : ℝ)⁻¹)) + I.card := by
  rw [Nat.cast_sum]
  calc
    (∑ i ∈ I, (((A / q i + 1 : ℕ) : ℝ))) ≤
        ∑ i ∈ I, ((A : ℝ) * (q i : ℝ)⁻¹ + 1) := by
          apply Finset.sum_le_sum
          intro i hi
          have hc := Nat.cast_div_le (α := ℝ) (m := A) (n := q i)
          push_cast at hc ⊢
          rw [div_eq_mul_inv] at hc
          linarith
    _ = (A : ℝ) * (∑ i ∈ I, ((q i : ℝ)⁻¹)) + I.card := by
      rw [Finset.sum_add_distrib]
      simp [Finset.mul_sum]
end OMAH1Research
namespace OMAH1Research
theorem Q217
    (n : ℕ → ℕ) (K G W A X p L sR : ℕ) :
    (Q28 n K G W A X p L sR).card ≤
      2 * (Q0 K G).card := by
  classical
  let C := Q28 n K G W A X p L sR
  let T := (Q0 K G).product (Finset.univ : Finset Bool)
  let f : ((ℕ × ℕ) × Bool) → ℕ × Bool := fun u => (u.1.1, u.2)
  have hmap : Set.MapsTo f (C : Set ((ℕ × ℕ) × Bool)) (T : Set (ℕ × Bool)) := by
    intro u huC
    have huCompat := (Finset.mem_filter.mp huC).1
    have huBase := (Finset.mem_filter.mp huCompat).1
    have huOuter := Finset.mem_product.mp huBase
    have huInner := Finset.mem_product.mp huOuter.1
    exact Finset.mem_product.mpr ⟨huInner.1, by simp⟩
  have hinj : Set.InjOn f (C : Set ((ℕ × ℕ) × Bool)) := by
    intro u hu v hv huv
    have huCenter := (Finset.mem_filter.mp hu).2
    have hvCenter := (Finset.mem_filter.mp hv).2
    change (u.1.1, u.2) = (v.1.1, v.2) at huv
    have hj : u.1.1 = v.1.1 :=
      congrArg (fun z : ℕ × Bool => z.1) huv
    have hb : u.2 = v.2 :=
      congrArg (fun z : ℕ × Bool => z.2) huv
    have hs : u.1.2 = v.1.2 := by
      rcases huCenter with huL | huR
      · have huSide := huL.1
        have huOff := huL.2
        rcases hvCenter with hvL | hvR
        · omega
        · rw [huSide, hvR.1] at hb
          contradiction
      · have huSide := huR.1
        have huOff := huR.2
        rcases hvCenter with hvL | hvR
        · rw [huSide, hvL.1] at hb
          contradiction
        · omega
    apply Prod.ext
    · exact Prod.ext hj hs
    · exact hb
  have hc := Finset.card_le_card_of_injOn f hmap hinj
  dsimp [C, T] at hc ⊢
  simpa [mul_comm] using hc
theorem Q107
    (n : ℕ → ℕ) (K G W A X p L sR : ℕ) :
    (Q20
      (Q29 n K G W A X p L sR)).card ≤
      2 * (Q0 K G).card := by
  calc
    (Q20
      (Q29 n K G W A X p L sR)).card ≤
        (Q29 n K G W A X p L sR).card :=
      Finset.card_image_le
    _ ≤ (Q28 n K G W A X p L sR).card :=
      Finset.card_image_le
    _ ≤ 2 * (Q0 K G).card :=
      Q217 n K G W A X p L sR
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
lemma Q348 (K H : ℕ) :
    Q0 K H = Finset.Ico (K + 1) H := by
  ext j
  simp [Q0]
  omega
theorem Q157
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (K H : ℕ) :
    (∑ j ∈ Q0 K H, ((n j : ℝ)⁻¹)) ≤
      c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹ := by
  have hsummable := Q311 n hpos c hc hratio K
  have hfinite :
      (∑ r ∈ Finset.range (H - (K + 1)),
        ((n (K + 1 + r) : ℝ)⁻¹)) ≤
      ∑' r : ℕ, ((n (K + 1 + r) : ℝ)⁻¹) :=
    hsummable.sum_le_tsum _ (fun r hr => by positivity)
  calc
    (∑ j ∈ Q0 K H, ((n j : ℝ)⁻¹)) =
        ∑ r ∈ Finset.range (H - (K + 1)),
          ((n (K + 1 + r) : ℝ)⁻¹) := by
            rw [Q348,
              Finset.sum_Ico_eq_sum_range]
    _ ≤ ∑' r : ℕ, ((n (K + 1 + r) : ℝ)⁻¹) := hfinite
    _ ≤ c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹ :=
      Q377 n hpos c hc hratio K
end OMAH1Research
namespace OMAH1Research
theorem Q62
    {ι : Type*} [DecidableEq ι]
    (Q : Finset ℕ) (C : Finset ι) (side : ι → Bool)
    (a qmod : ι → ℕ) (step v : ℕ)
    (hQ3 : ∀ q ∈ Q, 3 ≤ q)
    (hQodd : ∀ q ∈ Q, Odd q)
    (hcover : ∀ u ∈ C, ∃ q ∈ Q, ∀ t,
      qmod u ∣ a u + step * t →
        if side u then q ∣ v + 1 + 2 * t else q ∣ 4 * t + 1) :
    let S := Q20 Q
    ∃ M : ℕ, 0 < M ∧ M = ∏ z ∈ S, z ∧ ∀ T : ℕ,
      2 * (T * M) ≤ (S.card + 1) * (S.card + 2) *
        (Q23 C a qmod step (T * M)).card := by
  classical
  let S := Q20 Q
  have hSdata := Q163 Q hQ3 hQodd
  have hSprime : ∀ z ∈ S, z.Prime := fun z hz => (hSdata z hz).1
  have hSodd : ∀ z ∈ S, Odd z := fun z hz => (hSdata z hz).2.1
  obtain ⟨p, hprod, hpPrime, hp3, hpTwo, hpPair, hEnumCovers,
      hsafeBound⟩ :=
    Q168
      S v hSprime hSodd
  let M := ∏ i, p i
  have hMpos : 0 < M := by
    dsimp [M]
    apply Finset.prod_pos
    intro i hi
    exact lt_of_lt_of_le (by norm_num) (hp3 i)
  refine ⟨M, hMpos, hprod, ?_⟩
  intro T
  have hsubset : Q84 p v T ⊆
      Q23 C a qmod step (T * M) := by
    intro t htRep
    obtain ⟨z, hzProd, rfl⟩ := Finset.mem_image.mp htRep
    have hzT := Finset.mem_range.mp (Finset.mem_product.mp hzProd).1
    have hzSafe := (Finset.mem_product.mp hzProd).2
    have hzData := Finset.mem_filter.mp hzSafe
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, ?_⟩
    · have hzlt := Finset.mem_range.mp hzData.1
      dsimp [M]
      nlinarith
    · intro u huC hbad
      obtain ⟨q, hqQ, himp⟩ := hcover u huC
      have hform := himp (z.2 + M * z.1) hbad
      have hqne : q ≠ 1 := by have := hQ3 q hqQ; omega
      let prime := q.minFac
      have hprimeS : prime ∈ S := by
        apply (Q66 Q prime).mpr
        exact ⟨q, hqQ, rfl⟩
      obtain ⟨i, hpi⟩ := hEnumCovers prime hprimeS
      have hsafeI := hzData.2 i
      have hpM : p i ∣ M := by
        dsimp [M]
        exact Finset.dvd_prod_of_mem p (by simp)
      have hformReduceLeft : p i ∣ 4 * z.2 + 1 ↔
          p i ∣ 4 * (z.2 + M * z.1) + 1 := by
        have hd : p i ∣ 4 * M * z.1 := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpM 4) z.1
        rw [show 4 * (z.2 + M * z.1) + 1 =
          4 * M * z.1 + (4 * z.2 + 1) by ring]
        exact Nat.dvd_add_iff_right hd
      have hformReduceRight : p i ∣ v + 1 + 2 * z.2 ↔
          p i ∣ v + 1 + 2 * (z.2 + M * z.1) := by
        have hd : p i ∣ 2 * M * z.1 := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpM 2) z.1
        rw [show v + 1 + 2 * (z.2 + M * z.1) =
          2 * M * z.1 + (v + 1 + 2 * z.2) by ring]
        exact Nat.dvd_add_iff_right hd
      have hprimeDvd : prime ∣ q := Nat.minFac_dvd q
      split at hform
      · apply hsafeI.2
        rw [hformReduceRight]
        simpa [hpi] using dvd_trans hprimeDvd hform
      · apply hsafeI.1
        rw [hformReduceLeft]
        simpa [hpi] using dvd_trans hprimeDvd hform
  have hcard := Finset.card_le_card hsubset
  have hrepCard := Q288 p v T hMpos
  have hbaseScaled := Nat.mul_le_mul_left T hsafeBound
  calc
    2 * (T * M) = T * (2 * (∏ i, p i)) := by dsimp [M]; ring
    _ ≤ T * ((S.card + 1) * (S.card + 2) *
        (Q46 p v).card) := hbaseScaled
    _ = (S.card + 1) * (S.card + 2) *
        (Q84 p v T).card := by
      rw [hrepCard]
      ring
    _ ≤ (S.card + 1) * (S.card + 2) *
        (Q23 C a qmod step (T * M)).card :=
      Nat.mul_le_mul_left _ hcard
end OMAH1Research
namespace OMAH1Research
theorem Q116
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (K H L J X r v : ℕ) (_hKH : K < H)
    (hL : L < n K)
    (hX : X = r + (2 * n K) * v) (hv : Even v)
    (hrUpper : r ≤ n K + L)
    (_hsRWindow : n K + L - r < L + 1 + J)
    (hnoDouble : ∀ j, K < j → j < H → n j ≠ 2 * n K) :
    let A := n K - L
    let W := L + 1 + J
    let p := 4 * n K
    let sR := n K + L - r
    let C := Q28 n K H W A X p L sR
    let Q := Q29 n K H W A X p L sR
    let S := Q20 Q
    ∃ M : ℕ, 0 < M ∧ M = ∏ z ∈ S, z ∧ ∀ T : ℕ,
      2 * (T * M) ≤ (S.card + 1) * (S.card + 2) *
        (Q23 C (Q16 A X)
          (Q2 n) p (T * M)).card := by
  classical
  let A := n K - L
  let W := L + 1 + J
  let p := 4 * n K
  let sR := n K + L - r
  let C := Q28 n K H W A X p L sR
  let Q := Q29 n K H W A X p L sR
  have hn := hpos K
  have hcenterLeft : A + L = n K := by dsimp [A]; omega
  have hvOdd : Odd (v + 1) := by
    obtain ⟨z, hz⟩ := hv
    exact ⟨z, by omega⟩
  have hcenterRight : A + sR + X = 2 * n K * (v + 1) := by
    have hAr : A + L = n K := hcenterLeft
    have hsrr : sR + r = n K + L := by dsimp [sR]; omega
    rw [hX]
    calc
      A + sR + (r + 2 * n K * v) =
          2 * n K + 2 * n K * v := by omega
      _ = 2 * n K * (v + 1) := by ring
  have hQdata : ∀ q ∈ Q, Odd q ∧ 3 ≤ q := by
    intro q hqQ
    obtain ⟨u, huC, rfl⟩ := Finset.mem_image.mp hqQ
    have huCompat := (Finset.mem_filter.mp huC).1
    have huCenter := (Finset.mem_filter.mp huC).2
    have huBase := (Finset.mem_filter.mp huCompat).1
    have huComp := (Finset.mem_filter.mp huCompat).2
    have huPair := Finset.mem_product.mp (Finset.mem_product.mp huBase).1
    have hjData := Finset.mem_filter.mp huPair.1
    have hjH := Finset.mem_range.mp hjData.1
    have hKj := hjData.2
    have hnj := hpos u.1.1
    have hnlt : n K < n u.1.1 := hmono hKj
    rcases huCenter with hleft | hright
    · have hside : u.2 = false := hleft.1
      have hoff : u.1.2 = L := hleft.2
      have hcompLeft : (n u.1.1).gcd (4 * n K) ∣ n K := by
        simpa [Q2, Q16, p, A,
          hside, hoff, hcenterLeft] using huComp
      exact Q218
        (n u.1.1) (n K) hnj hn hnlt hcompLeft
    · have hside : u.2 = true := hright.1
      have hoff : u.1.2 = sR := hright.2
      have hcompRight : (n u.1.1).gcd (4 * n K) ∣
          2 * n K * (v + 1) := by
        simpa [Q2, Q16, p, A,
          sR, hside, hoff, hcenterRight] using huComp
      have hd := Q178
        (n u.1.1) (n K) (v + 1) hnj hn hnlt hvOdd hcompRight
      refine ⟨hd.1, ?_⟩
      have hqpos : 0 < n u.1.1 / (n u.1.1).gcd (4 * n K) := hd.1.pos
      have hqne : n u.1.1 / (n u.1.1).gcd (4 * n K) ≠ 1 := by
        intro heq
        have heqDouble := hd.2 heq
        exact hnoDouble u.1.1 hKj hjH heqDouble
      have hqneTwo : n u.1.1 / (n u.1.1).gcd (4 * n K) ≠ 2 := by
        intro heq
        obtain ⟨z, hz⟩ := hd.1
        omega
      change 3 ≤ n u.1.1 / (n u.1.1).gcd (4 * n K)
      omega
  apply Q62
    Q C (fun u => u.2) (Q16 A X) (Q2 n)
      p v
  · exact fun q hq => (hQdata q hq).2
  · exact fun q hq => (hQdata q hq).1
  · intro u huC
    let q0 := Q2 n u /
      (Q2 n u).gcd p
    refine ⟨q0, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨u, huC, rfl⟩
    · intro t hbad
      have huCompat := (Finset.mem_filter.mp huC).1
      have huCenter := (Finset.mem_filter.mp huC).2
      have huComp := (Finset.mem_filter.mp huCompat).2
      let g := (n u.1.1).gcd (4 * n K)
      have hg : 0 < g := Nat.gcd_pos_of_pos_left (4 * n K) (hpos u.1.1)
      have hqFactor : n u.1.1 = g * q0 := by
        dsimp [g, q0, p]
        exact (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
      rcases huCenter with hleft | hright
      · have hside : u.2 = false := hleft.1
        have hoff : u.1.2 = L := hleft.2
        have hgN : g ∣ n K := by
          simpa [g, p, Q2, Q16,
            A, hside, hoff, hcenterLeft] using huComp
        let u0 := n K / g
        have hnFactor : n K = g * u0 := by
          dsimp [u0]
          exact (Nat.mul_div_cancel' hgN).symm
        have hcop : q0.Coprime u0 := by
          dsimp [q0, u0, g, p]
          exact Q65
            (n u.1.1) (4 * n K) (n K) (hpos u.1.1)
              hgN (by exact ⟨4, by ring⟩)
        simp only [hside, Bool.false_eq_true, ↓reduceIte]
        apply (Q167
          (n u.1.1) (n K) g q0 u0 t hg hqFactor hnFactor hcop).mp
        simpa [Q2, Q16, p, A,
          hside, hoff, hcenterLeft] using hbad
      · have hside : u.2 = true := hright.1
        have hoff : u.1.2 = sR := hright.2
        have hgAligned : g ∣ 2 * n K * (v + 1) := by
          simpa [g, p, Q2, Q16,
            A, sR, hside, hoff, hcenterRight] using huComp
        have hgTwo : g ∣ 2 * n K :=
          Q80
            g (n K) (v + 1) hvOdd
            (by dsimp [g]; exact Nat.gcd_dvd_right _ _) hgAligned
        let u0 := (2 * n K) / g
        have htwoFactor : 2 * n K = g * u0 := by
          dsimp [u0]
          exact (Nat.mul_div_cancel' hgTwo).symm
        have hcop : q0.Coprime u0 := by
          dsimp [q0, u0, g, p]
          exact Q65
            (n u.1.1) (4 * n K) (2 * n K) (hpos u.1.1)
              hgTwo (by exact ⟨2, by ring⟩)
        simp only [hside, ite_true]
        apply (Q162
          (n u.1.1) g q0 u0 v t hg hqFactor hcop).mp
        have haligned : A + u.1.2 + X + p * t =
            g * u0 * (v + 1 + 2 * t) := by
          rw [hoff, hcenterRight, ← htwoFactor]
          dsimp [p]
          ring
        simpa [Q2, Q16, hside, haligned]
          using hbad
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
set_option maxHeartbeats 1200000 in
theorem Q231
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (K G H L J X r v : ℕ) (hKG : K < G) (hGH : G ≤ H)
    (hL : L < n K)
    (hX : X = r + (2 * n K) * v) (hv : Even v)
    (hrUpper : r ≤ n K + L)
    (hsRWindow : n K + L - r < L + 1 + J)
    (hnoDouble : ∀ j, K < j → j < G → n j ≠ 2 * n K)
    (hdensity :
      let A := n K - L
      let W := L + 1 + J
      let p := 4 * n K
      let sR := n K + L - r
      let Q := Q29 n K G W A X p L sR
      let S := Q20 Q
      let D := (S.card + 1) * (S.card + 2)
      (8 : ℝ) * D *
        (W ^ 2 * (∑ j ∈ Q0 K H, ((n j : ℝ)⁻¹)) +
          W * n K * (∑ j ∈ Finset.Ico G H, ((n j : ℝ)⁻¹))) < 1) :
    let A := n K - L
    let W := L + 1 + J
    let p := 4 * n K
    let sR := n K + L - r
    let C0 := Q28 n K G W A X p L sR
    let O := Q18 n K H W A X p \ C0
    let Q := Q29 n K G W A X p L sR
    let S := Q20 Q
    let D := (S.card + 1) * (S.card + 2)
    let Z₁ := (Q0 K H).card
    let Z₂ := (Finset.Ico G H).card
    ∃ M R : ℕ,
      0 < M ∧ M = ∏ z ∈ S, z ∧ 0 < R ∧
      (∑ u ∈ O, (R / (Q2 n u /
        (Q2 n u).gcd p) + 1)) <
        (Q23 C0 (Q16 A X)
          (Q2 n) p R).card ∧
      R ≤ M + 2 * D * W * (Z₁ + Z₂) := by
  classical
  let A := n K - L
  let W := L + 1 + J
  let p := 4 * n K
  let sR := n K + L - r
  let C0 := Q28 n K G W A X p L sR
  let O := Q18 n K H W A X p \ C0
  let Q := Q29 n K G W A X p L sR
  let S := Q20 Q
  let D := (S.card + 1) * (S.card + 2)
  let Z₁ := (Q0 K H).card
  let Z₂ := (Finset.Ico G H).card
  let sigma₁ : ℝ := ∑ j ∈ Q0 K H, ((n j : ℝ)⁻¹)
  let sigma₂ : ℝ := ∑ j ∈ Finset.Ico G H, ((n j : ℝ)⁻¹)
  have hdensity' : (8 : ℝ) * D *
      (W ^ 2 * sigma₁ + W * n K * sigma₂) < 1 := by
    simpa [A, W, p, sR, Q, S, D, sigma₁, sigma₂] using hdensity
  obtain ⟨M, hM, hMeq, hprotected⟩ :=
    Q116
      n hpos hmono K G L J X r v hKG hL hX hv hrUpper
        hsRWindow hnoDouble
  have hDpos : 0 < D := by dsimp [D]; positivity
  let delta : ℝ := 2 - 8 * D *
    (W ^ 2 * sigma₁ + W * n K * sigma₂)
  have hdeltaOne : 1 < delta := by
    dsimp [delta]
    nlinarith
  have hdelta : 0 < delta := lt_trans (by norm_num) hdeltaOne
  have hden : 0 < delta * (M : ℝ) :=
    mul_pos hdelta (by exact_mod_cast hM)
  let E : ℕ := 2 * D * W * (Z₁ + Z₂)
  let q : ℝ := (E : ℝ) / (delta * (M : ℝ))
  let T : ℕ := ⌊q⌋₊ + 1
  have hqnonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (by positivity) hden.le
  have hqT : q < (T : ℝ) := by
    dsimp [T]
    simpa using (Nat.lt_floor_add_one q)
  have hTpos : 0 < T := by dsimp [T]; omega
  let R := T * M
  have hRpos : 0 < R := mul_pos hTpos hM
  have hendpoint : (E : ℝ) < delta * (R : ℝ) := by
    have hm : (E : ℝ) < (T : ℝ) * (delta * (M : ℝ)) := by
      apply (div_lt_iff₀ hden).mp
      simpa [q] using hqT
    calc
      (E : ℝ) < (T : ℝ) * (delta * (M : ℝ)) := hm
      _ = delta * (R : ℝ) := by
        dsimp [R]
        push_cast
        ring
  have hRbound : R ≤ M + E := by
    have hfloor : ((⌊q⌋₊ : ℕ) : ℝ) ≤ q := Nat.floor_le hqnonneg
    have hTle : (T : ℝ) ≤ q + 1 := by
      dsimp [T]
      push_cast
      linarith
    have hqM : q * (M : ℝ) = (E : ℝ) / delta := by
      dsimp [q]
      field_simp
    have hdivle : (E : ℝ) / delta ≤ (E : ℝ) := by
      apply (div_le_iff₀ hdelta).mpr
      have hEnonneg : (0 : ℝ) ≤ E := by positivity
      nlinarith
    have hreal : (R : ℝ) ≤ (M + E : ℕ) := by
      calc
        (R : ℝ) = (T : ℝ) * (M : ℝ) := by simp [R]
        _ ≤ (q + 1) * (M : ℝ) := by gcongr
        _ = q * (M : ℝ) + (M : ℝ) := by ring
        _ = (E : ℝ) / delta + (M : ℝ) := by rw [hqM]
        _ ≤ (E : ℝ) + (M : ℝ) := by gcongr
        _ = (M + E : ℕ) := by push_cast; ring
    exact_mod_cast hreal
  let B := ∑ u ∈ O, (R / (Q2 n u /
    (Q2 n u).gcd p) + 1)
  have hBnat : B ≤
      2 * W * ∑ j ∈ Q0 K H,
        ((R * (4 * W)) / n j + 1) +
      2 * W * ∑ j ∈ Finset.Ico G H,
        ((R * (4 * n K)) / n j + 1) := by
    dsimp [B]
    exact Q298 n hpos K G H L J X r v R
      hKG hGH hL hX hrUpper hsRWindow
  have hsum₁ := Q88
    (Q0 K H) n (fun j hj => hpos j) (R * (4 * W))
  have hsum₂ := Q88
    (Finset.Ico G H) n (fun j hj => hpos j) (R * (4 * n K))
  have hBreal : (B : ℝ) ≤
      8 * (R : ℝ) *
          (W ^ 2 * sigma₁ + W * n K * sigma₂) +
        2 * W * (Z₁ + Z₂) := by
    have hc : (B : ℝ) ≤
        ((2 * W * ∑ j ∈ Q0 K H,
            ((R * (4 * W)) / n j + 1) +
          2 * W * ∑ j ∈ Finset.Ico G H,
            ((R * (4 * n K)) / n j + 1) : ℕ) : ℝ) := by
      exact_mod_cast hBnat
    push_cast at hc
    have hsum₁' :
        ((∑ j ∈ Q0 K H,
          ((R * (4 * W)) / n j + 1) : ℕ) : ℝ) ≤
          (R * (4 * W) : ℕ) * sigma₁ + Z₁ := by
      simpa [sigma₁, Z₁] using hsum₁
    have hsum₂' :
        ((∑ j ∈ Finset.Ico G H,
          ((R * (4 * n K)) / n j + 1) : ℕ) : ℝ) ≤
          (R * (4 * n K) : ℕ) * sigma₂ + Z₂ := by
      simpa [sigma₂, Z₂] using hsum₂
    have hs1 :
        ((∑ j ∈ Q0 K H,
          ((R * (4 * W)) / n j + 1) : ℕ) : ℝ) ≤
          (R : ℝ) * (4 * W : ℕ) * sigma₁ + Z₁ := by
      calc
        _ ≤ ((R * (4 * W) : ℕ) : ℝ) * sigma₁ + Z₁ := hsum₁'
        _ = (R : ℝ) * (4 * W : ℕ) * sigma₁ + Z₁ := by
          push_cast
          ring
    have hs2 :
        ((∑ j ∈ Finset.Ico G H,
          ((R * (4 * n K)) / n j + 1) : ℕ) : ℝ) ≤
          (R : ℝ) * (4 * n K : ℕ) * sigma₂ + Z₂ := by
      calc
        _ ≤ ((R * (4 * n K) : ℕ) : ℝ) * sigma₂ + Z₂ := hsum₂'
        _ = (R : ℝ) * (4 * n K : ℕ) * sigma₂ + Z₂ := by
          push_cast
          ring
    calc
      (B : ℝ) ≤
          (2 * W : ℕ) *
            ((∑ j ∈ Q0 K H,
              ((R * (4 * W)) / n j + 1) : ℕ) : ℝ) +
          (2 * W : ℕ) *
            ((∑ j ∈ Finset.Ico G H,
              ((R * (4 * n K)) / n j + 1) : ℕ) : ℝ) := by
        simpa using hc
      _ ≤ (2 * W : ℕ) *
            ((R : ℝ) * (4 * W : ℕ) * sigma₁ + Z₁) +
          (2 * W : ℕ) *
            ((R : ℝ) * (4 * n K : ℕ) * sigma₂ + Z₂) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hs1 (by positivity))
          (mul_le_mul_of_nonneg_left hs2 (by positivity))
      _ = 8 * (R : ℝ) *
          (W ^ 2 * sigma₁ + W * n K * sigma₂) +
            2 * W * (Z₁ + Z₂) := by
        push_cast
        ring
  have hDBreal : (D * B : ℕ) < 2 * R := by
    have hmain : (D : ℝ) * (B : ℝ) < 2 * (R : ℝ) := by
      have hscaled := mul_le_mul_of_nonneg_left hBreal
        (show (0 : ℝ) ≤ D by positivity)
      dsimp [delta, E] at hendpoint
      push_cast at hendpoint hscaled
      nlinarith
    exact_mod_cast hmain
  have hprot := hprotected T
  have hBcard : B < (Q23 C0 (Q16 A X)
      (Q2 n) p R).card := by
    have hchain : D * B < D *
        (Q23 C0 (Q16 A X)
          (Q2 n) p R).card := by
      calc
        D * B < 2 * R := hDBreal
        _ ≤ D * (Q23 C0 (Q16 A X)
          (Q2 n) p R).card := by
            simpa [D, R, S, Q, C0, A, W, p, sR] using hprot
    exact (Nat.mul_lt_mul_left hDpos).mp hchain
  refine ⟨M, R, hM, ?_, hRpos, hBcard, ?_⟩
  · simpa [S, Q, A, W, p, sR] using hMeq
  · simpa [E, D, W, Z₁, Z₂, S, Q, A, p, sR] using hRbound
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
theorem Q319
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (G H : ℕ) :
    (∑ j ∈ Finset.Ico G H, ((n j : ℝ)⁻¹)) ≤
      (1 - c⁻¹)⁻¹ * (n G : ℝ)⁻¹ := by
  let ρ : ℝ := c⁻¹
  have hcpos : 0 < c := lt_trans (by norm_num) hc
  have hρpos : 0 < ρ := inv_pos.mpr hcpos
  have hρlt : ρ < 1 := by
    dsimp [ρ]
    exact (inv_lt_one₀ hcpos).2 hc
  have hρnorm : ‖ρ‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_pos hρpos]
  have hmajor : Summable (fun r : ℕ => ρ ^ r * (n G : ℝ)⁻¹) :=
    (summable_geometric_of_norm_lt_one hρnorm).mul_right _
  have hterm (r : ℕ) : (n (G + r) : ℝ)⁻¹ ≤
      ρ ^ r * (n G : ℝ)⁻¹ := by
    have hgrowth := Q51
      n c hcpos.le hratio G r
    have hdenpos : 0 < c ^ r * (n G : ℝ) :=
      mul_pos (pow_pos hcpos _) (by exact_mod_cast hpos G)
    calc
      (n (G + r) : ℝ)⁻¹ ≤ (c ^ r * (n G : ℝ))⁻¹ :=
        inv_anti₀ hdenpos hgrowth
      _ = ρ ^ r * (n G : ℝ)⁻¹ := by
        simp [ρ, mul_inv_rev, inv_pow, mul_comm]
  have hsum : Summable (fun r : ℕ => (n (G + r) : ℝ)⁻¹) :=
    hmajor.of_nonneg_of_le (fun r => by positivity) hterm
  have hfinite :
      (∑ r ∈ Finset.range (H - G), ((n (G + r) : ℝ)⁻¹)) ≤
        ∑' r : ℕ, ((n (G + r) : ℝ)⁻¹) :=
    hsum.sum_le_tsum _ (fun r hr => by positivity)
  calc
    (∑ j ∈ Finset.Ico G H, ((n j : ℝ)⁻¹)) =
        ∑ r ∈ Finset.range (H - G), ((n (G + r) : ℝ)⁻¹) := by
      rw [Finset.sum_Ico_eq_sum_range]
    _ ≤ ∑' r : ℕ, ((n (G + r) : ℝ)⁻¹) := hfinite
    _ ≤ ∑' r : ℕ, ρ ^ r * (n G : ℝ)⁻¹ :=
      hsum.tsum_le_tsum hterm hmajor
    _ = (1 - c⁻¹)⁻¹ * (n G : ℝ)⁻¹ := by
      rw [tsum_mul_right, tsum_geometric_of_norm_lt_one hρnorm]
theorem Q379
    (n : ℕ → ℕ) (hmono : StrictMono n)
    (K B : ℕ) (hKB : K ≤ B) :
    ∃ G : ℕ, K < G ∧ B < n G ∧
      ∀ j, K < j → j < G → n j ≤ B := by
  have hex : ∃ G : ℕ, K < G ∧ B < n G := by
    refine ⟨B + 1, by omega, ?_⟩
    exact lt_of_lt_of_le (Nat.lt_succ_self B) hmono.le_apply
  let G := Nat.find hex
  have hG := Nat.find_spec hex
  refine ⟨G, hG.1, hG.2, ?_⟩
  intro j hKj hjG
  by_contra hnot
  have hjCandidate : K < j ∧ B < n j := ⟨hKj, by omega⟩
  have hGj := Nat.find_min' hex hjCandidate
  omega
theorem Q324
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (K G W A X p L sR B z : ℕ)
    (hbound : ∀ j, K < j → j < G → n j ≤ B)
    (hz : z ∈ Q20
      (Q29 n K G W A X p L sR)) :
    z ≤ B := by
  obtain ⟨q, hqQ, hqz⟩ :=
    (Q66
      (Q29 n K G W A X p L sR) z).mp hz
  obtain ⟨u, huC, hqu⟩ := Finset.mem_image.mp hqQ
  rw [← hqz, ← hqu]
  have huCompat := (Finset.mem_filter.mp huC).1
  have huBase := (Finset.mem_filter.mp huCompat).1
  have huOuter := Finset.mem_product.mp huBase
  have huInner := Finset.mem_product.mp huOuter.1
  have huPos := Finset.mem_filter.mp huInner.1
  have hjG := Finset.mem_range.mp huPos.1
  have hKj := huPos.2
  have hqpos : 0 < n u.1.1 / (n u.1.1).gcd p := by
    apply Nat.div_pos
    · exact Nat.gcd_le_left p (hpos u.1.1)
    · exact Nat.gcd_pos_of_pos_left p (hpos u.1.1)
  exact (Nat.minFac_le hqpos).trans <|
    (Nat.div_le_self _ _).trans (hbound u.1.1 hKj hjG)
theorem Q228
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (K G W A X p L sR B : ℕ) (hB : 0 < B)
    (hbound : ∀ j, K < j → j < G → n j ≤ B) :
    let S := Q20
      (Q29 n K G W A X p L sR)
    let d := (Q0 K G).card
    (∏ z ∈ S, z) ≤ B ^ (2 * d) := by
  let S := Q20
    (Q29 n K G W A X p L sR)
  let d := (Q0 K G).card
  have hprod : (∏ z ∈ S, z) ≤ B ^ S.card := by
    apply Finset.prod_le_pow_card
    intro z hz
    exact Q324
      n hpos K G W A X p L sR B z hbound hz
  have hcard : S.card ≤ 2 * d :=
    Q107
      n K G W A X p L sR
  exact hprod.trans (pow_le_pow_right₀ (by omega) hcard)
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
theorem Q216
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (K G H W A X p L sR : ℕ)
    (hbound :
      let d := (Q0 K G).card
      (8 : ℝ) * ((2 * d + 1) * (2 * d + 2) : ℕ) *
        (W ^ 2 *
            (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
          W * n K *
            ((1 - c⁻¹)⁻¹ * (n G : ℝ)⁻¹)) < 1) :
    let Q := Q29 n K G W A X p L sR
    let S := Q20 Q
    let D := (S.card + 1) * (S.card + 2)
    (8 : ℝ) * D *
      (W ^ 2 * (∑ j ∈ Q0 K H, ((n j : ℝ)⁻¹)) +
        W * n K * (∑ j ∈ Finset.Ico G H, ((n j : ℝ)⁻¹))) < 1 := by
  let Q := Q29 n K G W A X p L sR
  let S := Q20 Q
  let d := (Q0 K G).card
  let D := (S.card + 1) * (S.card + 2)
  let Dmax := (2 * d + 1) * (2 * d + 2)
  have hScard : S.card ≤ 2 * d :=
    Q107 n K G W A X p L sR
  have hD : D ≤ Dmax := by
    dsimp [D, Dmax]
    exact Nat.mul_le_mul (Nat.add_le_add_right hScard 1)
      (Nat.add_le_add_right hScard 2)
  have htail₁ := Q157
    n hpos c hc hratio K H
  have htail₂ := Q319 n hpos c hc hratio G H
  have hinner :
      W ^ 2 * (∑ j ∈ Q0 K H, ((n j : ℝ)⁻¹)) +
        W * n K * (∑ j ∈ Finset.Ico G H, ((n j : ℝ)⁻¹)) ≤
      W ^ 2 * (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
        W * n K * ((1 - c⁻¹)⁻¹ * (n G : ℝ)⁻¹) := by
    gcongr
  have hDreal : (D : ℝ) ≤ (Dmax : ℝ) := by exact_mod_cast hD
  calc
    (8 : ℝ) * D *
      (W ^ 2 * (∑ j ∈ Q0 K H, ((n j : ℝ)⁻¹)) +
        W * n K * (∑ j ∈ Finset.Ico G H, ((n j : ℝ)⁻¹))) ≤
      8 * (Dmax : ℝ) *
      (W ^ 2 * (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
        W * n K * ((1 - c⁻¹)⁻¹ * (n G : ℝ)⁻¹)) := by
      gcongr
    _ < 1 := by simpa [d, Dmax] using hbound
end OMAH1Research
namespace OMAH1Research
theorem Q115
    (n : ℕ → ℕ) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (K B Q : ℕ) (hKB : n K ≤ B)
    (hcross : (B : ℝ) < c ^ Q * (n K : ℝ)) :
    ∃ G : ℕ, K < G ∧ B < n G ∧
      (∀ j, K < j → j < G → n j ≤ B) ∧
      G ≤ K + Q ∧ (Q0 K G).card ≤ Q := by
  have hKleB : K ≤ B := by
    exact le_trans (hmono.le_apply) hKB
  obtain ⟨G, hKG, hBG, hfirst⟩ :=
    Q379 n hmono K B hKleB
  have hcpos : 0 < c := lt_trans (by norm_num) hc
  have hgrowth := Q51
    n c hcpos.le hratio K Q
  have hBQ : B < n (K + Q) := by exact_mod_cast hcross.trans_le hgrowth
  have hGQ : G ≤ K + Q := by
    by_contra hnot
    have hKQ : K < K + Q := by
      by_contra hQ0
      have : Q = 0 := by omega
      subst Q
      simp at hcross
      have hnKB : (n K : ℝ) ≤ B := by exact_mod_cast hKB
      linarith
    have hle := hfirst (K + Q) hKQ (by omega)
    omega
  have hcard : (Q0 K G).card ≤ Q := by
    have hsub : Q0 K G ⊆ Finset.Ico (K + 1) (K + Q + 1) := by
      intro j hj
      have hd := Finset.mem_filter.mp hj
      have hjG := Finset.mem_range.mp hd.1
      have hKj := hd.2
      simp only [Finset.mem_Ico]
      omega
    calc
      (Q0 K G).card ≤
          (Finset.Ico (K + 1) (K + Q + 1)).card :=
        Finset.card_le_card hsub
      _ = Q := by simp
  exact ⟨G, hKG, hBG, hfirst, hGQ, hcard⟩
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
noncomputable def Q8 (H : ℕ) : ℝ :=
  (H : ℝ) * (1 - φ⁻¹)⁻¹ + φ⁻¹ / (1 - φ⁻¹) ^ 2
noncomputable def Q10 (Tconj : ℝ) (H : ℕ) : ℝ :=
  |Tconj| + (H : ℝ) * (1 - φ⁻¹)⁻¹
lemma Q27
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    {x H : ℕ} (hx : x < n H) :
    Q7 n x ≤ Q8 H := by
  have hc := Q290 n hpos hmono hx
  unfold Q7 Q8
  have hfactor : 0 ≤ (1 - φ⁻¹)⁻¹ := by
    exact inv_nonneg.mpr (sub_nonneg.mpr
      ((inv_le_one₀ Real.goldenRatio_pos).mpr Real.one_lt_goldenRatio.le))
  have hcast : (Q41 n x : ℝ) ≤ H := by exact_mod_cast hc
  have hm := mul_le_mul_of_nonneg_right hcast hfactor
  linarith
lemma Q39
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (Tconj : ℝ) {x H : ℕ} (hx : x < n H) :
    Q6 n Tconj x ≤ Q10 Tconj H := by
  have hc := Q290 n hpos hmono hx
  unfold Q6 Q10
  have hfactor : 0 ≤ (1 - φ⁻¹)⁻¹ := by
    exact inv_nonneg.mpr (sub_nonneg.mpr
      ((inv_le_one₀ Real.goldenRatio_pos).mpr Real.one_lt_goldenRatio.le))
  have hcast : (Q41 n x : ℝ) ≤ H := by exact_mod_cast hc
  have hm := mul_le_mul_of_nonneg_right hcast hfactor
  linarith
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
theorem Q223
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (K G B L J X r v H : ℕ) (hKG : K < G) (hB : 0 < B)
    (hvalues : ∀ j, K < j → j < G → n j ≤ B)
    (hL : L < n K)
    (hX : X = r + (2 * n K) * v) (hv : Even v)
    (hrUpper : r ≤ n K + L)
    (hsRWindow : n K + L - r < L + 1 + J)
    (hnoDouble : ∀ j, K < j → j < G → n j ≠ 2 * n K)
    (hdensity :
      let W := L + 1 + J
      let d := (Q0 K G).card
      (8 : ℝ) * ((2 * d + 1) * (2 * d + 2) : ℕ) *
        (W ^ 2 *
            (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
          W * n K * ((1 - c⁻¹)⁻¹ * (n G : ℝ)⁻¹)) < 1)
    (hGH : G ≤ H)
    (haffine :
      let A := n K - L
      let W := L + 1 + J
      let p := 4 * n K
      let d := (Q0 K G).card
      let Dmax := (2 * d + 1) * (2 * d + 2)
      let Mmax := B ^ (2 * d)
      let U := A + p * Mmax + X + W
      let V := 4 * p * Dmax * W
      U + V * H < n H) :
    let A := n K - L
    let W := L + 1 + J
    let p := 4 * n K
    let sR := n K + L - r
    let C0 := Q28 n K G W A X p L sR
    ∃ R : ℕ, 0 < R ∧
      let O := Q18 n K H W A X p \ C0
      (∑ u ∈ O, (R / (Q2 n u /
        (Q2 n u).gcd p) + 1)) <
        (Q23 C0 (Q16 A X)
          (Q2 n) p R).card ∧
      A + p * R + X + W < n H := by
  classical
  let A := n K - L
  let W := L + 1 + J
  let p := 4 * n K
  let sR := n K + L - r
  let Q := Q29 n K G W A X p L sR
  let S := Q20 Q
  let d := (Q0 K G).card
  let D := (S.card + 1) * (S.card + 2)
  let Dmax := (2 * d + 1) * (2 * d + 2)
  let Mmax := B ^ (2 * d)
  let U := A + p * Mmax + X + W
  let V := 4 * p * Dmax * W
  have haffine' : U + V * H < n H := by
    simpa [A, W, p, d, Dmax, Mmax, U, V] using haffine
  have hdensityH :
      let Q' := Q29 n K G W A X p L sR
      let S' := Q20 Q'
      let D' := (S'.card + 1) * (S'.card + 2)
      (8 : ℝ) * D' *
        (W ^ 2 * (∑ j ∈ Q0 K H, ((n j : ℝ)⁻¹)) +
          W * n K * (∑ j ∈ Finset.Ico G H, ((n j : ℝ)⁻¹))) < 1 := by
    apply Q216
      n hpos c hc hratio K G H W A X p L sR
    simpa [W, d] using hdensity
  obtain ⟨M, R, hM, hMeq, hR, hbudget, hRbound⟩ :=
    Q231
      n hpos hmono K G H L J X r v hKG hGH hL hX hv hrUpper
        hsRWindow hnoDouble hdensityH
  have hMle : M ≤ Mmax := by
    rw [hMeq]
    dsimp [Mmax]
    exact Q228
      n hpos K G W A X p L sR B hB hvalues
  have hDle : D ≤ Dmax := by
    have hScard : S.card ≤ 2 * d :=
      Q107 n K G W A X p L sR
    dsimp [D, Dmax]
    exact Nat.mul_le_mul (Nat.add_le_add_right hScard 1)
      (Nat.add_le_add_right hScard 2)
  have hZ₁ : (Q0 K H).card ≤ H := by
    calc
      (Q0 K H).card ≤ (Finset.range H).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = H := Finset.card_range H
  have hZ₂ : (Finset.Ico G H).card ≤ H := by
    have hcard : (Finset.Ico G H).card = H - G := by simp
    omega
  have hZsum : (Q0 K H).card +
      (Finset.Ico G H).card ≤ 2 * H := by omega
  have hendpointCost :
      2 * D * W * ((Q0 K H).card +
        (Finset.Ico G H).card) ≤ 4 * Dmax * W * H := by
    calc
      2 * D * W * ((Q0 K H).card +
          (Finset.Ico G H).card) ≤
          2 * Dmax * W * (2 * H) := by gcongr
      _ = 4 * Dmax * W * H := by ring
  have hRcoarse : R ≤ Mmax + 4 * Dmax * W * H := by
    calc
      R ≤ M + 2 * D * W * ((Q0 K H).card +
          (Finset.Ico G H).card) := by
            simpa [D, S, Q, A, W, p, sR] using hRbound
      _ ≤ Mmax + 4 * Dmax * W * H :=
        Nat.add_le_add hMle hendpointCost
  have hcut : A + p * R + X + W < n H := by
    have hcost : A + p * R + X + W ≤ U + V * H := by
      calc
        A + p * R + X + W ≤
            A + p * (Mmax + 4 * Dmax * W * H) + X + W := by
          gcongr
        _ = U + V * H := by
          dsimp [U, V]
          ring
    exact hcost.trans_lt haffine'
  refine ⟨R, hR, ?_⟩
  simpa [A, W, p, sR] using And.intro hbudget hcut
end OMAH1Research
namespace OMAH1Research
theorem Q153
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (K H W A X p R : ℕ) (hA : 0 < A) (_hKH : K < H)
    (C O : Finset ((ℕ × ℕ) × Bool))
    (hpartition : C ∪ O = Q18 n K H W A X p)
    (hbudget :
      (∑ u ∈ O, (R / (Q2 n u /
        (Q2 n u).gcd p) + 1)) <
        (Q23 C (Q16 A X)
          (Q2 n) p R).card)
    (hcut : A + p * R + X + W < n H) :
    ∃ t < R, ∀ j, K < j → ∀ s < W,
      (¬ n j ∣ A + p * t + s) ∧
      (¬ n j ∣ A + p * t + s + X) := by
  classical
  let a := Q16 A X
  let q := Q2 n
  have hq : ∀ u ∈ O, 0 < q u := by
    intro u _
    exact hpos u.1.1
  have hbudget' :
      (∑ u ∈ O, (R / (q u / (q u).gcd p) + 1)) <
        (Q23 C a q p R).card := by
    simpa [a, q] using hbudget
  obtain ⟨t, htR, hC, hO⟩ :=
    Q154 C O a q p R hq hbudget'
  have havI : ∀ u ∈ Q56 K H W,
      ¬ q u ∣ a u + p * t := by
    intro u hu
    by_cases hc : (q u).gcd p ∣ a u
    · have huComp : u ∈ Q18 n K H W A X p := by
        exact Finset.mem_filter.mpr ⟨hu, hc⟩
      have huUnion : u ∈ C ∪ O := by rw [hpartition]; exact huComp
      rcases Finset.mem_union.mp huUnion with huC | huO
      · exact hC u huC
      · exact hO u huO
    · intro hdvd
      exact hc (Q257 (a u) p (q u) t hdvd)
  refine ⟨t, htR, ?_⟩
  intro j hKj s hsW
  by_cases hjH : j < H
  · have hjI : j ∈ Q0 K H := by
      simp [Q0, hjH, hKj]
    have hsI : s ∈ Finset.range W := Finset.mem_range.mpr hsW
    have hleft := havI ((j, s), false) (by
      simp [Q56, hjI, hsI])
    have hright := havI ((j, s), true) (by
      simp [Q56, hjI, hsI])
    dsimp [a, q, Q16, Q2] at hleft hright
    constructor
    · simpa [add_assoc, add_comm, add_left_comm] using hleft
    · simpa [add_assoc, add_comm, add_left_comm] using hright
  · have hHj : H ≤ j := by omega
    have hnHj : n H ≤ n j := hmono.monotone hHj
    have hleftPos : 0 < A + p * t + s := by omega
    have hrightPos : 0 < A + p * t + s + X := by omega
    have hpt : p * t ≤ p * R :=
      Nat.mul_le_mul_left p (Nat.le_of_lt htR)
    have hleftLt : A + p * t + s < n H := by omega
    have hrightLt : A + p * t + s + X < n H := by omega
    constructor
    · intro hdvd
      have hle := Nat.le_of_dvd hleftPos hdvd
      omega
    · intro hdvd
      have hle := Nat.le_of_dvd hrightPos hdvd
      omega
end OMAH1Research
namespace OMAH1Research
theorem Q83
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (q : ℕ) (hq : (2 : ℝ) ≤ c ^ q)
    (G U V : ℕ) :
    let A := U + V * G
    let B := V * q
    let N := A + B + 1
    let t := Nat.clog 2 N
    let s := 4 * t + 4
    let H := G + q * s
    G ≤ H ∧ U + V * H < n H := by
  let A := U + V * G
  let B := V * q
  let N := A + B + 1
  let t := Nat.clog 2 N
  let s := 4 * t + 4
  let H := G + q * s
  have hNpos : 0 < N := by dsimp [N]; omega
  have hNpow : N ≤ 2 ^ t := by
    exact Nat.le_pow_clog (by norm_num) N
  have hNpowSelf : N ≤ 2 ^ (2 * N) := by
    exact (show N ≤ 2 * N ^ 2 + 1 by nlinarith).trans
      (Nat.two_mul_sq_add_one_le_two_pow_two_mul N)
  have htN : t ≤ 2 * N := by
    calc
      t = Nat.clog 2 N := rfl
      _ ≤ Nat.clog 2 (2 ^ (2 * N)) :=
        Nat.clog_mono (by norm_num) le_rfl hNpowSelf
      _ = 2 * N := Nat.clog_pow 2 (2 * N) (by norm_num)
  have htarget : U + V * H = A + B * s := by
    dsimp [H, A, B]
    ring
  have hAle : A ≤ N := by dsimp [N]; omega
  have hBle : B ≤ N := by dsimp [N]; omega
  have hsle : s ≤ 8 * N + 4 := by dsimp [s]; omega
  have hBs : B * s ≤ N * (8 * N + 4) :=
    Nat.mul_le_mul hBle hsle
  have hNleN2 : N ≤ N ^ 2 := by
    simpa using (Nat.le_pow (a := N) (by norm_num : 0 < 2))
  have hN2leN4 : N ^ 2 ≤ N ^ 4 :=
    pow_le_pow_right₀ (by omega) (by omega)
  have htargetPoly : A + B * s < 16 * N ^ 4 := by
    nlinarith
  have hpowLower : 16 * N ^ 4 ≤ 2 ^ s := by
    have hp := Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hNpow 4)
    calc
      16 * N ^ 4 ≤ 16 * (2 ^ t) ^ 4 := hp
      _ = 2 ^ s := by
        dsimp [s]
        rw [pow_add, show 4 * t = t * 4 by omega, pow_mul]
        norm_num
        ring
  have htargetPow : U + V * H < 2 ^ s := by
    rw [htarget]
    exact htargetPoly.trans_le hpowLower
  have hcpos : 0 < c := lt_trans (by norm_num) hc
  have hbasePow : (2 : ℝ) ^ s ≤ (c ^ q) ^ s :=
    (pow_le_pow_left₀ (by norm_num) hq) s
  have hnGone : (1 : ℝ) ≤ n G := by exact_mod_cast hpos G
  have hgrowth := Q51
    n c hcpos.le hratio G (q * s)
  refine ⟨by omega, ?_⟩
  have hreal : ((U + V * H : ℕ) : ℝ) < (n H : ℕ) := by
    calc
      ((U + V * H : ℕ) : ℝ) < ((2 ^ s : ℕ) : ℝ) := by
        exact_mod_cast htargetPow
      _ = (2 : ℝ) ^ s := by norm_num
      _ ≤ (c ^ q) ^ s := hbasePow
      _ = c ^ (q * s) := (pow_mul c q s).symm
      _ ≤ c ^ (q * s) * (n G : ℝ) :=
        le_mul_of_one_le_right (pow_nonneg hcpos.le _) hnGone
      _ ≤ n (G + q * s) := hgrowth
      _ = n H := rfl
  exact_mod_cast hreal
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
theorem Q204
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (q : ℕ) (hq : (2 : ℝ) ≤ c ^ q)
    (K G B L J X r v : ℕ) (hKG : K < G) (hB : 0 < B)
    (hvalues : ∀ j, K < j → j < G → n j ≤ B)
    (hL : L < n K)
    (hX : X = r + (2 * n K) * v) (hv : Even v)
    (hrUpper : r ≤ n K + L)
    (hsRWindow : n K + L - r < L + 1 + J)
    (hnoDouble : ∀ j, K < j → j < G → n j ≠ 2 * n K)
    (hdensity :
      let W := L + 1 + J
      let d := (Q0 K G).card
      (8 : ℝ) * ((2 * d + 1) * (2 * d + 2) : ℕ) *
        (W ^ 2 *
            (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
          W * n K * ((1 - c⁻¹)⁻¹ * (n G : ℝ)⁻¹)) < 1) :
    let A := n K - L
    let W := L + 1 + J
    let p := 4 * n K
    let sR := n K + L - r
    let d := (Q0 K G).card
    let Dmax := (2 * d + 1) * (2 * d + 2)
    let Mmax := B ^ (2 * d)
    let U := A + p * Mmax + X + W
    let V := 4 * p * Dmax * W
    let A₀ := U + V * G
    let B₀ := V * q
    let N := A₀ + B₀ + 1
    let t := Nat.clog 2 N
    let H := G + q * (4 * t + 4)
    let C0 := Q28 n K G W A X p L sR
    ∃ R : ℕ, 0 < R ∧
      let O := Q18 n K H W A X p \ C0
      (∑ u ∈ O, (R / (Q2 n u /
        (Q2 n u).gcd p) + 1)) <
        (Q23 C0 (Q16 A X)
          (Q2 n) p R).card ∧
      A + p * R + X + W < n H := by
  let A := n K - L
  let W := L + 1 + J
  let p := 4 * n K
  let sR := n K + L - r
  let d := (Q0 K G).card
  let Dmax := (2 * d + 1) * (2 * d + 2)
  let Mmax := B ^ (2 * d)
  let U := A + p * Mmax + X + W
  let V := 4 * p * Dmax * W
  let A₀ := U + V * G
  let B₀ := V * q
  let N := A₀ + B₀ + 1
  let t := Nat.clog 2 N
  let H := G + q * (4 * t + 4)
  have hAff := Q83
    n hpos c hc hratio q hq G U V
  have hGH : G ≤ H := by omega
  have haffine : U + V * H < n H := by
    simpa [A₀, B₀, N, t, H] using hAff.2
  exact Q223
    n hpos hmono c hc hratio K G B L J X r v H hKG hB hvalues
      hL hX hv hrUpper hsRWindow hnoDouble hdensity hGH
      (by simpa [A, W, p, d, Dmax, Mmax, U, V] using haffine)
end OMAH1Research
namespace OMAH1Research
theorem Q144
    (P n : ℕ) (hn : 0 < n) (hndvd : ¬ 2 * n ∣ P) :
    let g := (4 * n).gcd P
    ∃ X r v : ℕ,
      P ∣ X ∧ X < (4 * n) * P ∧
      X = r + (2 * n) * v ∧ Even v ∧
      0 < r ∧ r < 2 * n ∧ 2 * r.dist n ≤ g := by
  let M := 4 * n
  let g := M.gcd P
  let q := M / g
  let P' := P / g
  have hM : 0 < M := by dsimp [M]; omega
  have hg : 0 < g := Nat.gcd_pos_of_pos_left P hM
  have hgM : g ∣ M := Nat.gcd_dvd_left M P
  have hgP : g ∣ P := Nat.gcd_dvd_right M P
  have hMFactor : g * q = M := by
    dsimp [q]
    exact Nat.mul_div_cancel' hgM
  have hPFactor : g * P' = P := by
    dsimp [P']
    exact Nat.mul_div_cancel' hgP
  have hqpos : 0 < q := by
    dsimp [q]
    exact Nat.div_pos (Nat.gcd_le_left P hM) hg
  have hq : 3 ≤ q := by
    by_contra hnot
    have hq12 : q = 1 ∨ q = 2 := by omega
    rcases hq12 with hq1 | hq2
    · have hgM' : g = M := by
        rw [hq1, mul_one] at hMFactor
        exact hMFactor
      apply hndvd
      exact dvd_trans (show 2 * n ∣ M by
        dsimp [M]
        exact ⟨2, by ring⟩) (by simpa [hgM'] using hgP)
    · have hg2n : g = 2 * n := by
        rw [hq2] at hMFactor
        dsimp [M] at hMFactor
        omega
      apply hndvd
      rw [← hg2n]
      exact hgP
  have hcop : P'.Coprime q := by
    have hc := Nat.coprime_div_gcd_div_gcd (m := M) (n := P) hg
    exact hc.symm
  let k := (q + 1) / 4
  have hkpos : 0 < k := by dsimp [k]; omega
  have hkltHalf : 2 * k < q := by
    dsimp [k]
    omega
  have hklt : k < q := by omega
  obtain ⟨u, huq, hu⟩ :=
    Nat.exists_mul_mod_eq_of_coprime k hcop (Nat.ne_of_gt hqpos)
  have hkmod : k % q = k := Nat.mod_eq_of_lt hklt
  rw [hkmod] at hu
  let r := g * k
  let X := P * u
  have hrmod : r = X % M := by
    dsimp [r, X]
    rw [← hPFactor, ← hMFactor, mul_assoc, Nat.mul_mod_mul_left, hu]
  have hrpos : 0 < r := mul_pos hg hkpos
  have hrlt : r < 2 * n := by
    have : 2 * (g * k) < g * q := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        Nat.mul_lt_mul_of_pos_left hkltHalf hg
    dsimp [r, M] at this ⊢
    omega
  have hnear : 2 * r.dist n ≤ g := by
    have hkLower : q ≤ 4 * k + 2 := by dsimp [k]; omega
    have hkUpper : 4 * k ≤ q + 2 := by dsimp [k]; omega
    have hdistK : (4 * k).dist q ≤ 2 := by
      rcases le_total (4 * k) q with hle | hge
      · rw [Nat.dist_eq_sub_of_le hle]
        omega
      · rw [Nat.dist_eq_sub_of_le_right hge]
        omega
    have hr4 : 4 * r = g * (4 * k) := by
      dsimp [r]
      ring
    have hn4 : 4 * n = g * q := by simpa [M] using hMFactor.symm
    have hdistScale : 4 * r.dist n = g * (4 * k).dist q := by
      rw [← Nat.dist_mul_left, hr4, hn4, Nat.dist_mul_left]
    have hscaled := Nat.mul_le_mul_left g hdistK
    omega
  let w := X / M
  let v := X / (2 * n)
  have hdecomp : X = r + (2 * n) * (w * 2) := by
    have hx := Nat.mod_add_div X M
    rw [← hrmod] at hx
    calc
      X = r + M * (X / M) := hx.symm
      _ = r + (2 * n) * (w * 2) := by dsimp [M, w]; ring
  have hv : v = w * 2 := by
    dsimp [v]
    rw [hdecomp, Nat.add_mul_div_left r (w * 2) (by omega : 0 < 2 * n),
      Nat.div_eq_of_lt hrlt]
    simp
  have hPne : P ≠ 0 := by
    intro hP0
    apply hndvd
    rw [hP0]
    exact dvd_zero (2 * n)
  have hPpos : 0 < P := Nat.pos_of_ne_zero hPne
  have hqM : q ≤ M := Nat.div_le_self M g
  have hXbound : X < (4 * n) * P := by
    dsimp [X, M] at hqM ⊢
    nlinarith
  refine ⟨X, r, v, ⟨u, rfl⟩, hXbound, ?_, ?_, hrpos, hrlt, hnear⟩
  · rw [hdecomp, hv]
  · rw [hv]
    exact ⟨w, by ring⟩
end OMAH1Research
namespace OMAH1Research
theorem Q346 (W : ℕ) :
    W ^ 8 < 2 ^ (8 * W) := by
  have hsq : W ^ 2 < 2 ^ (2 * W) := by
    calc
      W ^ 2 < 2 * W ^ 2 + 1 := by nlinarith
      _ ≤ 2 ^ (2 * W) := Nat.two_mul_sq_add_one_le_two_pow_two_mul W
  have hp := Nat.pow_lt_pow_left hsq (by norm_num : (4 : ℕ) ≠ 0)
  calc
    W ^ 8 = (W ^ 2) ^ 4 := by rw [← pow_mul]
    _ < (2 ^ (2 * W)) ^ 4 := hp
    _ = 2 ^ (8 * W) := by
      rw [← pow_mul]
      congr 1
      omega
theorem Q180
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (q : ℕ) (hq : (2 : ℝ) ≤ c ^ q)
    (K W : ℕ) (hW : 0 < W) :
    let B := n K * W ^ 8
    let Q := 8 * q * W
    ∃ G : ℕ, K < G ∧ B < n G ∧
      (∀ j, K < j → j < G → n j ≤ B) ∧
      G ≤ K + Q ∧ (Q0 K G).card ≤ Q := by
  let B := n K * W ^ 8
  let Q := 8 * q * W
  have hWpow : W ^ 8 < 2 ^ (8 * W) :=
    Q346 W
  have hbase : (2 : ℝ) ^ (8 * W) ≤ (c ^ q) ^ (8 * W) :=
    (pow_le_pow_left₀ (by norm_num) hq) (8 * W)
  have hcQ : (2 : ℝ) ^ (8 * W) ≤ c ^ Q := by
    calc
      (2 : ℝ) ^ (8 * W) ≤ (c ^ q) ^ (8 * W) := hbase
      _ = c ^ (q * (8 * W)) := (pow_mul c q (8 * W)).symm
      _ = c ^ Q := by
        congr 1
        dsimp [Q]
        ring
  have hcross : (B : ℝ) < c ^ Q * (n K : ℝ) := by
    have hmpos : (0 : ℝ) < n K := by exact_mod_cast hpos K
    have hwreal : ((W ^ 8 : ℕ) : ℝ) < (2 : ℝ) ^ (8 * W) := by
      exact_mod_cast hWpow
    have hwc : ((W ^ 8 : ℕ) : ℝ) < c ^ Q := hwreal.trans_le hcQ
    have hm := mul_lt_mul_of_pos_right hwc hmpos
    simpa [B, mul_comm] using hm
  have hKB : n K ≤ B := by
    dsimp [B]
    have hone : 1 ≤ W ^ 8 := one_le_pow₀ (by omega)
    nlinarith
  exact Q115
    n hmono c hc hratio K B Q hKB hcross
end OMAH1Research
namespace OMAH1Research
theorem Q135
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (c : ℝ) (hc : 1 < c)
    (q K G W d : ℕ) (hW : 0 < W)
    (hd : d ≤ 8 * q * W)
    (hBG : n K * W ^ 8 < n G)
    (hsimple :
      let B := n K * W ^ 8
      let Q := 8 * q * W
      (8 : ℝ) * ((2 * Q + 1) * (2 * Q + 2) : ℕ) *
        (W ^ 2 * (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
          W * n K * ((1 - c⁻¹)⁻¹ * (B : ℝ)⁻¹)) < 1) :
    (8 : ℝ) * ((2 * d + 1) * (2 * d + 2) : ℕ) *
      (W ^ 2 * (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
        W * n K * ((1 - c⁻¹)⁻¹ * (n G : ℝ)⁻¹)) < 1 := by
  let B := n K * W ^ 8
  let Q := 8 * q * W
  have hBpos : (0 : ℝ) < B := by
    exact_mod_cast mul_pos (hpos K) (pow_pos hW 8)
  have hBle : (B : ℝ) ≤ n G := by exact_mod_cast hBG.le
  have hinv : ((n G : ℝ)⁻¹) ≤ (B : ℝ)⁻¹ := inv_anti₀ hBpos hBle
  have hcpos : 0 < c := lt_trans (by norm_num) hc
  have hgeom : 0 ≤ (1 - c⁻¹)⁻¹ := by
    exact inv_nonneg.mpr
      (sub_nonneg.mpr ((inv_le_one₀ hcpos).mpr hc.le))
  have hinner :
      W ^ 2 * (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
        W * n K * ((1 - c⁻¹)⁻¹ * (n G : ℝ)⁻¹) ≤
      W ^ 2 * (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
        W * n K * ((1 - c⁻¹)⁻¹ * (B : ℝ)⁻¹) := by
    gcongr
  have hdQ : d ≤ Q := by simpa [Q] using hd
  have hD : (2 * d + 1) * (2 * d + 2) ≤
      (2 * Q + 1) * (2 * Q + 2) := by
    gcongr
  have hDreal :
      (((2 * d + 1) * (2 * d + 2) : ℕ) : ℝ) ≤
      (((2 * Q + 1) * (2 * Q + 2) : ℕ) : ℝ) := by
    exact_mod_cast hD
  calc
    (8 : ℝ) * ((2 * d + 1) * (2 * d + 2) : ℕ) *
      (W ^ 2 * (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
        W * n K * ((1 - c⁻¹)⁻¹ * (n G : ℝ)⁻¹)) ≤
      8 * ((2 * Q + 1) * (2 * Q + 2) : ℕ) *
      (W ^ 2 * (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
        W * n K * ((1 - c⁻¹)⁻¹ * (B : ℝ)⁻¹)) := by
      gcongr
    _ < 1 := by simpa [B, Q] using hsimple
end OMAH1Research
namespace OMAH1Research
theorem Q362 (c : ℝ) (hc : 1 < c) :
    ∃ q : ℕ, 0 < q ∧ (2 : ℝ) ≤ c ^ q := by
  have ht := tendsto_pow_atTop_atTop_of_one_lt hc
  have hev : ∀ᶠ q : ℕ in Filter.atTop, (2 : ℝ) ≤ c ^ q :=
    ht.eventually (Filter.eventually_ge_atTop 2)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨Q, hQ⟩ := hev
  let q := max Q 1
  exact ⟨q, by dsimp [q]; omega, hQ q (le_max_left _ _)⟩
end OMAH1Research
namespace OMAH1Research
theorem Q109
    (c : ℝ) (hc : 1 < c)
    (q W m : ℕ) (hq : 0 < q) (hW : 0 < W) (hm : 0 < m)
    (hfirst :
      (5184 : ℝ) * q ^ 2 *
        (c⁻¹ * (1 - c⁻¹)⁻¹) * W ^ 4 < m)
    (hsecond :
      (5184 : ℝ) * q ^ 2 * (1 - c⁻¹)⁻¹ < W ^ 5) :
    let B := m * W ^ 8
    let Q := 8 * q * W
    (8 : ℝ) * ((2 * Q + 1) * (2 * Q + 2) : ℕ) *
      (W ^ 2 * (c⁻¹ * (1 - c⁻¹)⁻¹ * (m : ℝ)⁻¹) +
        W * m * ((1 - c⁻¹)⁻¹ * (B : ℝ)⁻¹)) < 1 := by
  let B := m * W ^ 8
  let Q := 8 * q * W
  let C₁ : ℝ := c⁻¹ * (1 - c⁻¹)⁻¹
  let C₀ : ℝ := (1 - c⁻¹)⁻¹
  have hcpos : 0 < c := lt_trans (by norm_num) hc
  have hden : 0 < 1 - c⁻¹ := sub_pos.mpr
    (inv_lt_one_of_one_lt₀ hc)
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hqW : 1 ≤ q * W := mul_pos hq hW
  have hD : (2 * Q + 1) * (2 * Q + 2) ≤
      324 * q ^ 2 * W ^ 2 := by
    have h₁ : 2 * Q + 1 ≤ 18 * q * W := by dsimp [Q]; nlinarith
    have h₂ : 2 * Q + 2 ≤ 18 * q * W := by dsimp [Q]; nlinarith
    calc
      (2 * Q + 1) * (2 * Q + 2) ≤
          (18 * q * W) * (18 * q * W) := Nat.mul_le_mul h₁ h₂
      _ = 324 * q ^ 2 * W ^ 2 := by ring
  have hDreal : (((2 * Q + 1) * (2 * Q + 2) : ℕ) : ℝ) ≤
      ((324 * q ^ 2 * W ^ 2 : ℕ) : ℝ) := by exact_mod_cast hD
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have hhalf₁ :
      (2592 : ℝ) * q ^ 2 * C₁ * W ^ 4 / m < 1 / 2 := by
    apply (div_lt_iff₀ hmR).mpr
    nlinarith [hfirst]
  have hhalf₂ :
      (2592 : ℝ) * q ^ 2 * C₀ / W ^ 5 < 1 / 2 := by
    have hW5 : (0 : ℝ) < (W : ℝ) ^ 5 := pow_pos hWR _
    apply (div_lt_iff₀ hW5).mpr
    nlinarith [hsecond]
  have hrewrite :
      (2592 : ℝ) * q ^ 2 * W ^ 2 *
        (W ^ 2 * (C₁ * (m : ℝ)⁻¹) +
          W * m * (C₀ * (B : ℝ)⁻¹)) =
      2592 * q ^ 2 * C₁ * W ^ 4 / m +
        2592 * q ^ 2 * C₀ / W ^ 5 := by
    dsimp [B]
    push_cast
    field_simp
  have hcoef :
      (8 : ℝ) * (((2 * Q + 1) * (2 * Q + 2) : ℕ) : ℝ) ≤
        2592 * (q : ℝ) ^ 2 * (W : ℝ) ^ 2 := by
    calc
      (8 : ℝ) * (((2 * Q + 1) * (2 * Q + 2) : ℕ) : ℝ) ≤
          8 * (((324 * q ^ 2 * W ^ 2 : ℕ) : ℝ)) := by gcongr
      _ = 2592 * (q : ℝ) ^ 2 * (W : ℝ) ^ 2 := by
        push_cast
        ring
  calc
    (8 : ℝ) * ((2 * Q + 1) * (2 * Q + 2) : ℕ) *
      (W ^ 2 * (c⁻¹ * (1 - c⁻¹)⁻¹ * (m : ℝ)⁻¹) +
        W * m * ((1 - c⁻¹)⁻¹ * (B : ℝ)⁻¹)) ≤
      2592 * q ^ 2 * W ^ 2 *
      (W ^ 2 * (C₁ * (m : ℝ)⁻¹) +
        W * m * (C₀ * (B : ℝ)⁻¹)) := by
      have hinnerNonneg : 0 ≤
          W ^ 2 * (C₁ * (m : ℝ)⁻¹) +
            W * m * (C₀ * (B : ℝ)⁻¹) := by positivity
      dsimp [C₁, C₀] at hinnerNonneg ⊢
      exact mul_le_mul_of_nonneg_right hcoef hinnerNonneg
    _ = 2592 * q ^ 2 * C₁ * W ^ 4 / m +
        2592 * q ^ 2 * C₀ / W ^ 5 := hrewrite
    _ < 1 / 2 + 1 / 2 := add_lt_add hhalf₁ hhalf₂
    _ = 1 := by norm_num
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
def Q21
    (n : ℕ → ℕ) (K G B L J X q : ℕ) : ℕ :=
  let A := n K - L
  let W := L + 1 + J
  let p := 4 * n K
  let d := (Q0 K G).card
  let Dmax := (2 * d + 1) * (2 * d + 2)
  let Mmax := B ^ (2 * d)
  let U := A + p * Mmax + X + W
  let V := 4 * p * Dmax * W
  let N := U + V * G + V * q + 1
  G + q * (4 * Nat.clog 2 N + 4)
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
def Q59
    (n : ℕ → ℕ) (K w q : ℕ) : ℕ :=
  let m := n K
  let P := Q12 n K
  let W := w + 1 + w
  let B := m * W ^ 8
  let Q := 8 * q * W
  let D := (2 * Q + 1) * (2 * Q + 2)
  let M := B ^ (2 * Q)
  let U := m + (4 * m) * M + (4 * m) * P + W
  let V := 4 * (4 * m) * D * W
  let N := U + V * (K + Q) + V * q + 1
  K + Q + q * (4 * Nat.clog 2 N + 4)
theorem Q92
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (K w q X G : ℕ) (hw : 0 < w)
    (hX : X < (4 * n K) * Q12 n K)
    (hG : G ≤ K + 8 * q * (w + 1 + w))
    (hd : (Q0 K G).card ≤
      8 * q * (w + 1 + w)) :
    Q21 n K G
      (n K * (w + 1 + w) ^ 8) w w X q ≤
      Q59 n K w q := by
  let m := n K
  let P := Q12 n K
  let W := w + 1 + w
  let B := m * W ^ 8
  let Q := 8 * q * W
  let d := (Q0 K G).card
  let Da := (2 * d + 1) * (2 * d + 2)
  let D := (2 * Q + 1) * (2 * Q + 2)
  let Ma := B ^ (2 * d)
  let M := B ^ (2 * Q)
  let Aa := m - w
  let Ua := Aa + (4 * m) * Ma + X + W
  let Va := 4 * (4 * m) * Da * W
  let Na := Ua + Va * G + Va * q + 1
  let U := m + (4 * m) * M + (4 * m) * P + W
  let V := 4 * (4 * m) * D * W
  let N := U + V * (K + Q) + V * q + 1
  have hdQ : d ≤ Q := by simpa [d, Q, W] using hd
  have hB : 1 ≤ B := by
    have hWpos : 0 < W := by dsimp [W]; omega
    have hBpos : 0 < B := by
      dsimp [B, m]
      exact mul_pos (hpos K) (pow_pos hWpos _)
    omega
  have hMa : Ma ≤ M := by
    dsimp [Ma, M]
    exact pow_le_pow_right₀ hB (by omega)
  have hDa : Da ≤ D := by
    dsimp [Da, D]
    gcongr
  have hUa : Ua ≤ U := by
    dsimp [Ua, U, Aa]
    have hXle : X ≤ (4 * m) * P := by simpa [m, P] using hX.le
    gcongr
    omega
  have hVa : Va ≤ V := by
    dsimp [Va, V]
    gcongr
  have hG' : G ≤ K + Q := by simpa [Q, W] using hG
  have hNa : Na ≤ N := by
    dsimp [Na, N]
    gcongr
  have hclog : Nat.clog 2 Na ≤ Nat.clog 2 N :=
    Nat.clog_mono (by norm_num) le_rfl hNa
  unfold Q21 Q59
  dsimp only
  change G + q * (4 * Nat.clog 2 Na + 4) ≤
    K + Q + q * (4 * Nat.clog 2 N + 4)
  gcongr
lemma Q332 {H H' : ℕ} (hHH : H ≤ H') :
    Q8 H ≤ Q8 H' := by
  unfold Q8
  have hfactor : 0 ≤ (1 - φ⁻¹)⁻¹ := by
    exact inv_nonneg.mpr (sub_nonneg.mpr
      ((inv_le_one₀ Real.goldenRatio_pos).mpr Real.one_lt_goldenRatio.le))
  have hcast : (H : ℝ) ≤ H' := by exact_mod_cast hHH
  nlinarith [mul_le_mul_of_nonneg_right hcast hfactor]
lemma Q251 (T : ℝ) {H H' : ℕ} (hHH : H ≤ H') :
    Q10 T H ≤ Q10 T H' := by
  unfold Q10
  have hfactor : 0 ≤ (1 - φ⁻¹)⁻¹ := by
    exact inv_nonneg.mpr (sub_nonneg.mpr
      ((inv_le_one₀ Real.goldenRatio_pos).mpr Real.one_lt_goldenRatio.le))
  have hcast : (H : ℝ) ≤ H' := by exact_mod_cast hHH
  nlinarith [mul_le_mul_of_nonneg_right hcast hfactor]
end OMAH1Research
namespace OMAH1Research
theorem Q74 (x : ℕ) : x ≤ 2 ^ (2 * x) := by
  exact (show x ≤ 2 * x ^ 2 + 1 by nlinarith).trans
    (Nat.two_mul_sq_add_one_le_two_pow_two_mul x)
theorem Q37
    {x y a b : ℕ} (hx : x ≤ 2 ^ a) (hy : y ≤ 2 ^ b) :
    x * y ≤ 2 ^ (a + b) := by
  calc
    x * y ≤ 2 ^ a * 2 ^ b := Nat.mul_le_mul hx hy
    _ = 2 ^ (a + b) := (pow_add 2 a b).symm
theorem Q40
    {x y a b : ℕ} (hx : x ≤ 2 ^ a) (hy : y ≤ 2 ^ b) :
    x + y ≤ 2 ^ (a + b + 1) := by
  have ha : 2 ^ a ≤ 2 ^ (a + b) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hb : 2 ^ b ≤ 2 ^ (a + b) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    x + y ≤ 2 ^ a + 2 ^ b := Nat.add_le_add hx hy
    _ ≤ 2 ^ (a + b) + 2 ^ (a + b) := Nat.add_le_add ha hb
    _ = 2 ^ (a + b + 1) := by rw [pow_succ]; ring
theorem Q164
    {x a : ℕ} (hx : x ≤ 2 ^ a) (k : ℕ) :
    x ^ k ≤ 2 ^ (a * k) := by
  calc
    x ^ k ≤ (2 ^ a) ^ k := Nat.pow_le_pow_left hx k
    _ = 2 ^ (a * k) := (pow_mul 2 a k).symm
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
theorem Q304
    (n : ℕ → ℕ) (K : ℕ) :
    Q12 n K ∣
      ∏ k ∈ Finset.range K, Q11 (n k) := by
  induction K with
  | zero => simp [Q12]
  | succ K ih =>
      simp only [Q12, Finset.prod_range_succ]
      apply Nat.lcm_dvd
      · exact dvd_trans ih (dvd_mul_right _ _)
      · exact dvd_mul_left _ _
theorem Q233
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (K : ℕ) :
    Q12 n K ≤ (4 * n K) ^ K := by
  have hprod :
      (∏ k ∈ Finset.range K, Q11 (n k)) ≤
        (4 * n K) ^ K := by
    calc
      (∏ k ∈ Finset.range K, Q11 (n k)) ≤
          (4 * n K) ^ (Finset.range K).card := by
        apply Finset.prod_le_pow_card
        intro k hk
        have hkK : k ≤ K := by
          have := Finset.mem_range.mp hk
          omega
        have hnk : n k ≤ n K := hmono.monotone hkK
        unfold Q11
        split <;> omega
      _ = (4 * n K) ^ K := by simp
  have hPpos := Q82 n hpos K
  exact (Nat.le_of_dvd (by
    have hfactorPos : ∀ k ∈ Finset.range K,
        0 < Q11 (n k) := by
      intro k _
      unfold Q11
      split <;> nlinarith [hpos k]
    exact Finset.prod_pos hfactorPos)
    (Q304 n K)).trans hprod
end OMAH1Research
namespace OMAH1Research
def Q259
    (n : ℕ → ℕ) (K w q : ℕ) : ℕ :=
  let m := n K
  let W := w + 1 + w
  let Q := 8 * q * W
  let D := (2 * Q + 1) * (2 * Q + 2)
  let eB := 2 * m + (2 * W) * 8
  let eM := eB * (2 * Q)
  let eP := (2 + 2 * m) * K
  let eT₁ := 2 + 2 * m + eM
  let eT₂ := 2 + 2 * m + eP
  let eU := 2 * m + eT₁ + 1 + eT₂ + 1 + 2 * W + 1
  let eV := 4 + 2 * m + 2 * D + 2 * W
  let eG := 2 * (K + Q)
  let eQ := 2 * q
  eU + (eV + eG) + 1 + (eV + eQ) + 1 + 0 + 1
def Q143
    (n : ℕ → ℕ) (K w q : ℕ) : ℕ :=
  let W := w + 1 + w
  let Q := 8 * q * W
  let E := Q259 n K w q
  K + Q + q * (4 * E + 4)
theorem Q322
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (K w q : ℕ) :
    Q59 n K w q ≤ Q143 n K w q := by
  let m := n K
  let P := Q12 n K
  let W := w + 1 + w
  let B := m * W ^ 8
  let Q := 8 * q * W
  let D := (2 * Q + 1) * (2 * Q + 2)
  let M := B ^ (2 * Q)
  let U := m + (4 * m) * M + (4 * m) * P + W
  let V := 4 * (4 * m) * D * W
  let N := U + V * (K + Q) + V * q + 1
  let eB := 2 * m + (2 * W) * 8
  let eM := eB * (2 * Q)
  let eP := (2 + 2 * m) * K
  let eT₁ := 2 + 2 * m + eM
  let eT₂ := 2 + 2 * m + eP
  let eU := 2 * m + eT₁ + 1 + eT₂ + 1 + 2 * W + 1
  let eV := 4 + 2 * m + 2 * D + 2 * W
  let eG := 2 * (K + Q)
  let eQ := 2 * q
  let E := eU + (eV + eG) + 1 + (eV + eQ) + 1 + 0 + 1
  have hm : m ≤ 2 ^ (2 * m) := Q74 m
  have hW : W ≤ 2 ^ (2 * W) := Q74 W
  have h4 : 4 ≤ 2 ^ 2 := by norm_num
  have h16 : 16 ≤ 2 ^ 4 := by norm_num
  have hW8 : W ^ 8 ≤ 2 ^ ((2 * W) * 8) :=
    Q164 hW 8
  have hB : B ≤ 2 ^ eB := by
    dsimp [B, eB]
    exact Q37 hm hW8
  have hM : M ≤ 2 ^ eM := by
    dsimp [M, eM]
    exact Q164 hB (2 * Q)
  have h4m : 4 * m ≤ 2 ^ (2 + 2 * m) :=
    Q37 h4 hm
  have hPbase : P ≤ (4 * m) ^ K := by
    dsimp [P, m]
    exact Q233 n hpos hmono K
  have hP : P ≤ 2 ^ eP := by
    calc
      P ≤ (4 * m) ^ K := hPbase
      _ ≤ 2 ^ ((2 + 2 * m) * K) := Q164 h4m K
      _ = 2 ^ eP := rfl
  have hT₁ : (4 * m) * M ≤ 2 ^ eT₁ := by
    dsimp [eT₁]
    exact Q37 h4m hM
  have hT₂ : (4 * m) * P ≤ 2 ^ eT₂ := by
    dsimp [eT₂]
    exact Q37 h4m hP
  have hU₁ : m + (4 * m) * M ≤ 2 ^ (2 * m + eT₁ + 1) :=
    Q40 hm hT₁
  have hU₂ : m + (4 * m) * M + (4 * m) * P ≤
      2 ^ (2 * m + eT₁ + 1 + eT₂ + 1) :=
    Q40 hU₁ hT₂
  have hU : U ≤ 2 ^ eU := by
    dsimp [U, eU]
    exact Q40 hU₂ hW
  have hD : D ≤ 2 ^ (2 * D) := Q74 D
  have h44 : 4 * 4 ≤ 2 ^ (2 + 2) := Q37 h4 h4
  have h44m : (4 * 4) * m ≤ 2 ^ (2 + 2 + 2 * m) :=
    Q37 h44 hm
  have h44mD : (4 * 4) * m * D ≤
      2 ^ (2 + 2 + 2 * m + 2 * D) :=
    Q37 h44m hD
  have hV : V ≤ 2 ^ eV := by
    have hv' : (4 * 4) * m * D * W ≤
        2 ^ (2 + 2 + 2 * m + 2 * D + 2 * W) :=
      Q37 h44mD hW
    dsimp [V, eV]
    calc
      4 * (4 * m) * D * W = (4 * 4) * m * D * W := by ring
      _ ≤ 2 ^ (2 + 2 + 2 * m + 2 * D + 2 * W) := hv'
      _ = 2 ^ (4 + 2 * m + 2 * D + 2 * W) := by rfl
  have hG : K + Q ≤ 2 ^ eG := by
    dsimp [eG]
    exact Q74 (K + Q)
  have hq : q ≤ 2 ^ eQ := by
    dsimp [eQ]
    exact Q74 q
  have hVG : V * (K + Q) ≤ 2 ^ (eV + eG) :=
    Q37 hV hG
  have hVq : V * q ≤ 2 ^ (eV + eQ) :=
    Q37 hV hq
  have hN₁ : U + V * (K + Q) ≤
      2 ^ (eU + (eV + eG) + 1) :=
    Q40 hU hVG
  have hN₂ : U + V * (K + Q) + V * q ≤
      2 ^ (eU + (eV + eG) + 1 + (eV + eQ) + 1) :=
    Q40 hN₁ hVq
  have h1 : 1 ≤ 2 ^ 0 := by simp
  have hN : N ≤ 2 ^ E := by
    have hh := Q40
      (a := eU + (eV + eG) + 1 + (eV + eQ) + 1) (b := 0) hN₂ h1
    dsimp [N, E]
    simpa using hh
  have hclog : Nat.clog 2 N ≤ E := by
    calc
      Nat.clog 2 N ≤ Nat.clog 2 (2 ^ E) :=
        Nat.clog_mono (by norm_num) le_rfl hN
      _ = E := Nat.clog_pow 2 E (by norm_num)
  unfold Q59 Q143
  dsimp only
  change K + Q + q * (4 * Nat.clog 2 N + 4) ≤
    K + Q + q * (4 * E + 4)
  gcongr
end OMAH1Research
namespace OMAH1Research
theorem Q314
    (n : ℕ → ℕ) (K w q : ℕ) :
    Q143 n K w q ≤
      60000 * (n K + K + w + q + 2) ^ 5 := by
  let m := n K
  let s := m + K + w + q + 2
  let W := w + 1 + w
  let Q := 8 * q * W
  let D := (2 * Q + 1) * (2 * Q + 2)
  let eB := 2 * m + (2 * W) * 8
  let eM := eB * (2 * Q)
  let eP := (2 + 2 * m) * K
  let eT₁ := 2 + 2 * m + eM
  let eT₂ := 2 + 2 * m + eP
  let eU := 2 * m + eT₁ + 1 + eT₂ + 1 + 2 * W + 1
  let eV := 4 + 2 * m + 2 * D + 2 * W
  let eG := 2 * (K + Q)
  let eQ := 2 * q
  let E := eU + (eV + eG) + 1 + (eV + eQ) + 1 + 0 + 1
  have hs1 : 1 ≤ s := by dsimp [s]; omega
  have hm : m ≤ s := by dsimp [s]; omega
  have hK : K ≤ s := by dsimp [s]; omega
  have hw : w ≤ s := by dsimp [s]; omega
  have hq : q ≤ s := by dsimp [s]; omega
  have hs2 : 1 ≤ s ^ 2 := one_le_pow₀ hs1
  have hs3 : 1 ≤ s ^ 3 := one_le_pow₀ hs1
  have hs4 : 1 ≤ s ^ 4 := one_le_pow₀ hs1
  have hs_le_sq : s ≤ s ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul_left s hs1
  have hs2_le_s3 : s ^ 2 ≤ s ^ 3 := by
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hs3_le_s4 : s ^ 3 ≤ s ^ 4 := by
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hs4_le_s5 : s ^ 4 ≤ s ^ 5 := by
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hW : W ≤ 3 * s := by
    dsimp [W]
    omega
  have hQ : Q ≤ 24 * s ^ 2 := by
    calc
      Q = 8 * q * W := rfl
      _ ≤ 8 * s * (3 * s) := by gcongr
      _ = 24 * s ^ 2 := by ring
  have h2Q1 : 2 * Q + 1 ≤ 49 * s ^ 2 := by omega
  have h2Q2 : 2 * Q + 2 ≤ 50 * s ^ 2 := by omega
  have hD : D ≤ 2450 * s ^ 4 := by
    calc
      D = (2 * Q + 1) * (2 * Q + 2) := rfl
      _ ≤ (49 * s ^ 2) * (50 * s ^ 2) := Nat.mul_le_mul h2Q1 h2Q2
      _ = 2450 * s ^ 4 := by ring
  have heB : eB ≤ 50 * s := by
    dsimp [eB]
    omega
  have heM : eM ≤ 2400 * s ^ 3 := by
    calc
      eM = eB * (2 * Q) := rfl
      _ ≤ (50 * s) * (2 * (24 * s ^ 2)) := Nat.mul_le_mul heB (Nat.mul_le_mul_left 2 hQ)
      _ = 2400 * s ^ 3 := by ring
  have heP : eP ≤ 4 * s ^ 2 := by
    calc
      eP = (2 + 2 * m) * K := rfl
      _ ≤ (4 * s) * s := by
        apply Nat.mul_le_mul
        · omega
        · exact hK
      _ = 4 * s ^ 2 := by ring
  have heT₁ : eT₁ ≤ 2404 * s ^ 3 := by
    dsimp [eT₁]
    omega
  have heT₂ : eT₂ ≤ 8 * s ^ 3 := by
    dsimp [eT₂]
    omega
  have heU : eU ≤ 2423 * s ^ 3 := by
    dsimp [eU]
    omega
  have heV : eV ≤ 4912 * s ^ 4 := by
    dsimp [eV]
    omega
  have heG : eG ≤ 50 * s ^ 4 := by
    dsimp [eG]
    omega
  have heQ : eQ ≤ 2 * s ^ 4 := by
    dsimp [eQ]
    omega
  have hE : E ≤ 13000 * s ^ 4 := by
    dsimp [E]
    omega
  unfold Q143 Q259
  dsimp only
  change K + Q + q * (4 * E + 4) ≤ 60000 * s ^ 5
  calc
    K + Q + q * (4 * E + 4) ≤
        s + 24 * s ^ 2 + s * (4 * (13000 * s ^ 4) + 4) := by gcongr
    _ ≤ 60000 * s ^ 5 := by nlinarith
theorem Q351
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (K w q : ℕ) :
    Q59 n K w q ≤
      60000 * (n K + K + w + q + 2) ^ 5 :=
  (Q322 n hpos hmono K w q).trans
    (Q314 n K w q)
end OMAH1Research
namespace OMAH1Research
def Q3 (q w : ℕ) : ℕ :=
  60000 * (q + 5) ^ 5 * (w + 1) ^ 40
theorem Q125
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (K w q : ℕ) (hm : n K ≤ (w + 1) ^ 8) :
    Q59 n K w q ≤ Q3 q w := by
  let m := n K
  let R := (w + 1) ^ 8
  let s := m + K + w + q + 2
  have hKm : K ≤ m := by simpa [m] using hmono.le_apply
  have hKR : K ≤ R := hKm.trans (by simpa [m, R] using hm)
  have hmR : m ≤ R := by simpa [m, R] using hm
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hwR : w ≤ R := by
    calc
      w ≤ w + 1 := by omega
      _ ≤ (w + 1) ^ 8 := Nat.le_pow (by norm_num)
      _ = R := rfl
  have hqR : q ≤ q * R := Nat.le_mul_of_pos_right q hRpos
  have hRone : 1 ≤ R := by omega
  have h2R : 2 ≤ 2 * R := Nat.mul_le_mul_left 2 hRone
  have hs : s ≤ (q + 5) * R := by
    dsimp [s]
    calc
      m + K + w + q + 2 ≤ R + R + R + q * R + 2 * R := by gcongr
      _ = (q + 5) * R := by ring
  calc
    Q59 n K w q ≤ 60000 * s ^ 5 := by
      simpa [s, m] using Q351 n hpos hmono K w q
    _ ≤ 60000 * ((q + 5) * R) ^ 5 := by gcongr
    _ = Q3 q w := by
      simp only [Q3]
      dsimp [R]
      ring
end OMAH1Research
namespace OMAH1Research
open Filter Topology Real goldenRatio
noncomputable def Q13 : ℝ :=
  (1 - φ⁻¹)⁻¹ + φ⁻¹ / (1 - φ⁻¹) ^ 2
noncomputable def Q19 (T : ℝ) : ℝ :=
  |T| + (1 - φ⁻¹)⁻¹
lemma Q63 : 0 ≤ Q13 := by
  unfold Q13
  have hr : 0 < φ⁻¹ := inv_pos.mpr Real.goldenRatio_pos
  have hd : 0 < 1 - φ⁻¹ := sub_pos.mpr
    (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)
  positivity
lemma Q101 (T : ℝ) :
    0 ≤ Q19 T := by
  unfold Q19
  have hd : 0 < 1 - φ⁻¹ := sub_pos.mpr
    (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)
  positivity
lemma Q34 (H : ℕ) : 0 ≤ Q8 H := by
  unfold Q8
  have hr : 0 < φ⁻¹ := inv_pos.mpr Real.goldenRatio_pos
  have hd : 0 < 1 - φ⁻¹ := sub_pos.mpr
    (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)
  positivity
lemma Q36 (T : ℝ) (H : ℕ) :
    0 ≤ Q10 T H := by
  unfold Q10
  have hd : 0 < 1 - φ⁻¹ := sub_pos.mpr
    (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)
  positivity
lemma Q93 (H : ℕ) :
    Q8 H ≤ Q13 * ((H : ℝ) + 1) := by
  unfold Q8 Q13
  have hH : 0 ≤ (H : ℝ) := by positivity
  have hA : 0 ≤ (1 - φ⁻¹)⁻¹ := by
    have hd : 0 < 1 - φ⁻¹ := sub_pos.mpr
      (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)
    positivity
  have hB : 0 ≤ φ⁻¹ / (1 - φ⁻¹) ^ 2 := by
    have hr : 0 < φ⁻¹ := inv_pos.mpr Real.goldenRatio_pos
    have hd : 0 < 1 - φ⁻¹ := sub_pos.mpr
      (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)
    positivity
  nlinarith
lemma Q170 (T : ℝ) (H : ℕ) :
    Q10 T H ≤
      Q19 T * ((H : ℝ) + 1) := by
  unfold Q10 Q19
  have hH : 0 ≤ (H : ℝ) := by positivity
  have hA : 0 ≤ (1 - φ⁻¹)⁻¹ := by
    have hd : 0 < 1 - φ⁻¹ := sub_pos.mpr
      (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)
    positivity
  have hT : 0 ≤ |T| := abs_nonneg T
  nlinarith
lemma Q98 (q w : ℕ) :
    Q3 q w + 1 ≤
      (60000 * (q + 5) ^ 5 + 1) * (w + 1) ^ 40 := by
  unfold Q3
  have hp : 1 ≤ (w + 1) ^ 40 := one_le_pow₀ (by omega)
  calc
    60000 * (q + 5) ^ 5 * (w + 1) ^ 40 + 1 ≤
        60000 * (q + 5) ^ 5 * (w + 1) ^ 40 + (w + 1) ^ 40 := by
      gcongr
    _ = (60000 * (q + 5) ^ 5 + 1) * (w + 1) ^ 40 := by ring
theorem Q333 :
    Tendsto (fun w : ℕ =>
      (φ⁻¹) ^ (w + 1) *
        (2 * Q8 (Q3 q w)))
      atTop (𝓝 0) := by
  let C : ℝ :=
    2 * Q13 *
      (60000 * (q + 5) ^ 5 + 1 : ℕ)
  let g : ℕ → ℝ := fun w =>
    C * ((w + 1 : ℕ) : ℝ) ^ 40 * (φ⁻¹) ^ (w + 1)
  have hr0 : 0 ≤ (φ⁻¹ : ℝ) := (inv_pos.mpr Real.goldenRatio_pos).le
  have hr1 : (φ⁻¹ : ℝ) < 1 :=
    inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hg : Tendsto g atTop (𝓝 0) := by
    have hbase := tendsto_pow_const_mul_const_pow_of_lt_one 40 hr0 hr1
    have hshift := hbase.comp (Filter.tendsto_add_atTop_nat 1)
    have hconst := hshift.const_mul C
    simpa [g, mul_assoc] using hconst
  apply squeeze_zero
  · intro w
    have ht := Q34 (Q3 q w)
    positivity
  · intro w
    have hcap := Q93
      (Q3 q w)
    have hnat := Q98 q w
    have hcast :
        ((Q3 q w : ℕ) : ℝ) + 1 ≤
          ((60000 * (q + 5) ^ 5 + 1 : ℕ) : ℝ) *
            ((w + 1 : ℕ) : ℝ) ^ 40 := by
      exact_mod_cast hnat
    have hc := mul_le_mul_of_nonneg_left hcast
      Q63
    have hp : 0 ≤ (φ⁻¹ : ℝ) ^ (w + 1) := by positivity
    calc
      (φ⁻¹) ^ (w + 1) *
          (2 * Q8 (Q3 q w)) ≤
        (φ⁻¹) ^ (w + 1) *
          (2 * (Q13 *
            (((Q3 q w : ℕ) : ℝ) + 1))) := by
              gcongr
      _ ≤ (φ⁻¹) ^ (w + 1) *
          (2 * (Q13 *
            (((60000 * (q + 5) ^ 5 + 1 : ℕ) : ℝ) *
              ((w + 1 : ℕ) : ℝ) ^ 40))) := by gcongr
      _ = 2 * Q13 *
          ((60000 * (q + 5) ^ 5 + 1 : ℕ) : ℝ) *
          ((w + 1 : ℕ) : ℝ) ^ 40 * (φ⁻¹) ^ (w + 1) := by ring
  · exact hg
theorem Q313 (T : ℝ) :
    Tendsto (fun w : ℕ =>
      (φ⁻¹) ^ w *
        (2 * Q8 (Q3 q w)) *
        (2 * Q10 T (Q3 q w)))
      atTop (𝓝 0) := by
  let r : ℝ := φ⁻¹
  let A : ℝ := ((60000 * (q + 5) ^ 5 + 1 : ℕ) : ℝ)
  let C : ℝ :=
    4 * Q13 * Q19 T *
      A ^ 2 * r⁻¹
  let g : ℕ → ℝ := fun w =>
    C * ((w + 1 : ℕ) : ℝ) ^ 80 * r ^ (w + 1)
  have hrpos : 0 < r := by dsimp [r]; exact inv_pos.mpr Real.goldenRatio_pos
  have hr0 : 0 ≤ r := hrpos.le
  have hr1 : r < 1 := by
    dsimp [r]
    exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hg : Tendsto g atTop (𝓝 0) := by
    have hbase := tendsto_pow_const_mul_const_pow_of_lt_one 80 hr0 hr1
    have hshift := hbase.comp (Filter.tendsto_add_atTop_nat 1)
    have hconst := hshift.const_mul C
    simpa [g, mul_assoc] using hconst
  apply squeeze_zero
  · intro w
    have ht := Q34 (Q3 q w)
    have hc := Q36 T (Q3 q w)
    positivity
  · intro w
    have ht := Q93 (Q3 q w)
    have hc := Q170 T (Q3 q w)
    have hnat := Q98 q w
    have hcast :
        ((Q3 q w : ℕ) : ℝ) + 1 ≤
          A * ((w + 1 : ℕ) : ℝ) ^ 40 := by
      dsimp [A]
      exact_mod_cast hnat
    have ht' : Q8 (Q3 q w) ≤
        Q13 * A * ((w + 1 : ℕ) : ℝ) ^ 40 := by
      calc
        Q8 (Q3 q w) ≤
            Q13 *
              (((Q3 q w : ℕ) : ℝ) + 1) := ht
        _ ≤ Q13 *
            (A * ((w + 1 : ℕ) : ℝ) ^ 40) :=
          mul_le_mul_of_nonneg_left hcast Q63
        _ = Q13 * A *
            ((w + 1 : ℕ) : ℝ) ^ 40 := by ring
    have hc' : Q10 T (Q3 q w) ≤
        Q19 T * A *
          ((w + 1 : ℕ) : ℝ) ^ 40 := by
      calc
        Q10 T (Q3 q w) ≤
            Q19 T *
              (((Q3 q w : ℕ) : ℝ) + 1) := hc
        _ ≤ Q19 T *
            (A * ((w + 1 : ℕ) : ℝ) ^ 40) :=
          mul_le_mul_of_nonneg_left hcast
            (Q101 T)
        _ = Q19 T * A *
            ((w + 1 : ℕ) : ℝ) ^ 40 := by ring
    have ht0 := Q34 (Q3 q w)
    have hc0 := Q36 T (Q3 q w)
    have hAt : 0 ≤ Q13 * A *
        ((w + 1 : ℕ) : ℝ) ^ 40 := ht0.trans ht'
    have hAc : 0 ≤ Q19 T * A *
        ((w + 1 : ℕ) : ℝ) ^ 40 := hc0.trans hc'
    have h2t : 2 * Q8 (Q3 q w) ≤
        2 * (Q13 * A *
          ((w + 1 : ℕ) : ℝ) ^ 40) := by gcongr
    have h2c : 2 * Q10 T (Q3 q w) ≤
        2 * (Q19 T * A *
          ((w + 1 : ℕ) : ℝ) ^ 40) := by gcongr
    have hrpow : 0 ≤ r ^ w := pow_nonneg hr0 _
    have hfirst :
        r ^ w * (2 * Q8 (Q3 q w)) ≤
          r ^ w * (2 * (Q13 * A *
            ((w + 1 : ℕ) : ℝ) ^ 40)) :=
      mul_le_mul_of_nonneg_left h2t hrpow
    have hrshift : r⁻¹ * r ^ (w + 1) = r ^ w := by
      rw [pow_succ]
      field_simp
    change r ^ w *
        (2 * Q8 (Q3 q w)) *
        (2 * Q10 T (Q3 q w)) ≤
      4 * Q13 * Q19 T *
        A ^ 2 * r⁻¹ * ((w + 1 : ℕ) : ℝ) ^ 80 * r ^ (w + 1)
    calc
      r ^ w * (2 * Q8 (Q3 q w)) *
          (2 * Q10 T (Q3 q w)) ≤
        r ^ w *
          (2 * (Q13 * A *
            ((w + 1 : ℕ) : ℝ) ^ 40)) *
          (2 * Q10 T (Q3 q w)) :=
        mul_le_mul_of_nonneg_right hfirst (by positivity)
      _ ≤ r ^ w *
          (2 * (Q13 * A *
            ((w + 1 : ℕ) : ℝ) ^ 40)) *
          (2 * (Q19 T * A *
            ((w + 1 : ℕ) : ℝ) ^ 40)) := by
        exact mul_le_mul_of_nonneg_left h2c (mul_nonneg hrpow (by positivity))
      _ = 4 * Q13 * Q19 T *
          A ^ 2 * r⁻¹ * ((w + 1 : ℕ) : ℝ) ^ 80 * r ^ (w + 1) := by
            rw [← hrshift]
            ring
  · exact hg
theorem Q317 (q : ℕ) (T ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ w : ℕ in atTop,
      (φ⁻¹) ^ (w + 1) *
          (2 * Q8 (Q3 q w)) < 1 ∧
      (φ⁻¹) ^ w *
          (2 * Q8 (Q3 q w)) *
          (2 * Q10 T (Q3 q w)) < ε := by
  exact ((Q333 (q := q)).eventually
      (gt_mem_nhds zero_lt_one)).and
    ((Q313 (q := q) T).eventually
      (gt_mem_nhds hε))
end OMAH1Research
namespace OMAH1Research
open Filter Topology
theorem Q339 (A B : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ w : ℕ in atTop,
      A * (((w + 1 + w : ℕ) : ℝ) ^ 4) < (w : ℝ) ^ 8 ∧
      B < (((w + 1 + w : ℕ) : ℝ) ^ 5) := by
  have hpow4 : Tendsto (fun w : ℕ => (w : ℝ) ^ 4) atTop atTop :=
    (Filter.tendsto_pow_atTop (α := ℝ) (by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpow5 : Tendsto (fun w : ℕ => (w : ℝ) ^ 5) atTop atTop :=
    (Filter.tendsto_pow_atTop (α := ℝ) (by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop 1,
    hpow4.eventually_gt_atTop (81 * A),
    hpow5.eventually_gt_atTop B] with w hw h4 h5
  have hW : w + 1 + w ≤ 3 * w := by omega
  have hwpos : 0 < (w : ℝ) ^ 4 := by positivity
  constructor
  · have hstrict := mul_lt_mul_of_pos_right h4 hwpos
    calc
      A * (((w + 1 + w : ℕ) : ℝ) ^ 4) ≤
          A * ((3 * (w : ℝ)) ^ 4) := by
            gcongr
            exact_mod_cast hW
      _ = (81 * A) * (w : ℝ) ^ 4 := by ring
      _ < (w : ℝ) ^ 4 * (w : ℝ) ^ 4 := hstrict
      _ = (w : ℝ) ^ 8 := by ring
  · calc
      B < (w : ℝ) ^ 5 := h5
      _ ≤ (((w + 1 + w : ℕ) : ℝ) ^ 5) := by
        gcongr
        norm_num
theorem Q316
    (c : ℝ) (hc : 1 < c) (q : ℕ) :
    ∀ᶠ w : ℕ in atTop,
      let W : ℕ := w + 1 + w
      (5184 : ℝ) * q ^ 2 *
          (c⁻¹ * (1 - c⁻¹)⁻¹) * W ^ 4 < (w : ℝ) ^ 8 ∧
        (5184 : ℝ) * q ^ 2 * (1 - c⁻¹)⁻¹ < (W : ℝ) ^ 5 := by
  have hinvpos : 0 < c⁻¹ := inv_pos.mpr (lt_trans zero_lt_one hc)
  have hden : 0 < 1 - c⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hc)
  have hA : 0 ≤
      (5184 : ℝ) * q ^ 2 * (c⁻¹ * (1 - c⁻¹)⁻¹) := by positivity
  filter_upwards [Q339
    ((5184 : ℝ) * q ^ 2 * (c⁻¹ * (1 - c⁻¹)⁻¹))
    ((5184 : ℝ) * q ^ 2 * (1 - c⁻¹)⁻¹) hA] with w hw
  dsimp only
  constructor
  · simpa [mul_assoc] using hw.1
  · simpa [mul_assoc] using hw.2
theorem Q297
    (c : ℝ) (q w m : ℕ)
    (hfirst :
      let W : ℕ := w + 1 + w
      (5184 : ℝ) * q ^ 2 *
        (c⁻¹ * (1 - c⁻¹)⁻¹) * W ^ 4 < (w : ℝ) ^ 8)
    (hsecond :
      let W : ℕ := w + 1 + w
      (5184 : ℝ) * q ^ 2 * (1 - c⁻¹)⁻¹ < (W : ℝ) ^ 5)
    (hwm : w ^ 8 ≤ m) :
    let W : ℕ := w + 1 + w
    (5184 : ℝ) * q ^ 2 *
        (c⁻¹ * (1 - c⁻¹)⁻¹) * W ^ 4 < m ∧
      (5184 : ℝ) * q ^ 2 * (1 - c⁻¹)⁻¹ < W ^ 5 := by
  dsimp only at hfirst hsecond ⊢
  constructor
  · exact hfirst.trans_le (by exact_mod_cast hwm)
  · simpa using hsecond
end OMAH1Research
namespace OMAH1Research
open Filter Topology Real goldenRatio
theorem Q286
    (T : ℝ) (q w H : ℕ)
    (hH : H ≤ Q3 q w)
    (hpost :
      (φ⁻¹) ^ (w + 1) *
        (2 * Q8 (Q3 q w)) < 1)
    (hpre :
      (φ⁻¹) ^ w *
        (2 * Q8 (Q3 q w)) *
        (2 * Q10 T (Q3 q w)) < ε) :
    (φ⁻¹) ^ (w + 1) * (2 * Q8 H) < 1 ∧
      (φ⁻¹) ^ w * (2 * Q8 H) *
        (2 * Q10 T H) < ε := by
  have ht := Q332 hH
  have hc := Q251 T hH
  have hrw : 0 ≤ (φ⁻¹ : ℝ) ^ w := by positivity
  have hrw1 : 0 ≤ (φ⁻¹ : ℝ) ^ (w + 1) := by positivity
  have htB0 := Q34 (Q3 q w)
  have hc0 := Q36 T H
  have h2t : 2 * Q8 H ≤
      2 * Q8 (Q3 q w) :=
    mul_le_mul_of_nonneg_left ht (by norm_num)
  have h2c : 2 * Q10 T H ≤
      2 * Q10 T (Q3 q w) :=
    mul_le_mul_of_nonneg_left hc (by norm_num)
  constructor
  · exact (mul_le_mul_of_nonneg_left h2t hrw1).trans_lt hpost
  · have hfirst :
        (φ⁻¹) ^ w * (2 * Q8 H) ≤
          (φ⁻¹) ^ w *
            (2 * Q8 (Q3 q w)) :=
      mul_le_mul_of_nonneg_left h2t hrw
    have hfirst0 : 0 ≤
        (φ⁻¹) ^ w *
          (2 * Q8 (Q3 q w)) :=
      mul_nonneg hrw (mul_nonneg (by norm_num) htB0)
    calc
      (φ⁻¹) ^ w * (2 * Q8 H) *
          (2 * Q10 T H) ≤
        (φ⁻¹) ^ w *
          (2 * Q8 (Q3 q w)) *
          (2 * Q10 T H) :=
        mul_le_mul_of_nonneg_right hfirst
          (mul_nonneg (by norm_num) hc0)
      _ ≤ (φ⁻¹) ^ w *
          (2 * Q8 (Q3 q w)) *
          (2 * Q10 T
            (Q3 q w)) :=
        mul_le_mul_of_nonneg_left h2c hfirst0
      _ < ε := hpre
end OMAH1Research
namespace OMAH1Research
open Filter Topology
def Q55 (n : ℕ → ℕ) (K : ℕ) : ℕ :=
  Nat.nthRoot 8 (n K)
lemma Q171 (n : ℕ → ℕ) (K : ℕ) :
    Q55 n K ^ 8 ≤ n K := by
  exact Nat.pow_nthRoot_le (Or.inl (by norm_num))
lemma Q122 (n : ℕ → ℕ) (K : ℕ) :
    n K < (Q55 n K + 1) ^ 8 := by
  exact Nat.lt_pow_nthRoot_add_one (by norm_num) (n K)
theorem Q147
    (n : ℕ → ℕ) (hmono : StrictMono n) :
    Tendsto (Q55 n) atTop atTop := by
  rw [tendsto_atTop]
  intro W
  filter_upwards [hmono.tendsto_atTop.eventually_ge_atTop (W ^ 8)] with K hK
  exact (Nat.le_nthRoot_iff (by norm_num)).2 hK
end OMAH1Research
namespace OMAH1Research
theorem Q280
    (P n : ℕ) (hn : 0 < n) (hgdiv : (4 * n).gcd P ∣ n) :
    ∃ X v : ℕ,
      P ∣ X ∧ X < (4 * n) * P ∧
      X = n + (2 * n) * v ∧ Even v := by
  let g := (4 * n).gcd P
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left P (by omega)
  have hndvd : ¬ 2 * n ∣ P := by
    intro htwoP
    have htwoFour : 2 * n ∣ 4 * n := ⟨2, by ring⟩
    have htwoG : 2 * n ∣ g := by
      dsimp [g]
      exact Nat.dvd_gcd htwoFour htwoP
    have hgn : g ≤ n := Nat.le_of_dvd hn (by simpa [g] using hgdiv)
    have htwoLe : 2 * n ≤ g := Nat.le_of_dvd hgpos htwoG
    omega
  obtain ⟨X, r, v, hPX, hXbound, hX, hv, _hrpos, _hrlt, hnear⟩ :=
    Q144 P n hn hndvd
  have hgP : g ∣ P := by
    dsimp [g]
    exact Nat.gcd_dvd_right _ _
  have hgX : g ∣ X := dvd_trans hgP hPX
  have hgTwoNv : g ∣ (2 * n) * v := by
    exact dvd_mul_of_dvd_left (dvd_trans (by simpa [g] using hgdiv)
      (show n ∣ 2 * n by exact ⟨2, by ring⟩)) v
  have hgr : g ∣ r := by
    apply (Nat.dvd_add_iff_left hgTwoNv).mpr
    rw [← hX]
    exact hgX
  have hrn : r = n := by
    by_contra hne
    have hdistpos : 0 < r.dist n := Nat.dist_pos_of_ne hne
    obtain ⟨r0, hr0⟩ := hgr
    obtain ⟨n0, hn0⟩ := hgdiv
    have hgdist : g ∣ r.dist n := by
      refine ⟨r0.dist n0, ?_⟩
      rw [hr0, hn0, Nat.dist_mul_left]
    have hg_le_dist : g ≤ r.dist n := Nat.le_of_dvd hdistpos hgdist
    omega
  refine ⟨X, v, hPX, hXbound, ?_, hv⟩
  simpa [hrn] using hX
theorem Q265
    (P n w : ℕ) (hn : 0 < n)
    (hw : 2 * w < n) (hgdiv : (4 * n).gcd P ∣ n) :
    ∃ X r v : ℕ,
      P ∣ X ∧ X < (4 * n) * P ∧
      X = r + (2 * n) * v ∧ Even v ∧
      0 < r ∧ r < 2 * n ∧
      w < r ∧ r + w < 2 * n ∧
      r ≤ n + w ∧ n + w - r < w + 1 + w := by
  obtain ⟨X, v, hPX, hXbound, hX, hv⟩ :=
    Q280 P n hn hgdiv
  refine ⟨X, n, v, hPX, hXbound, hX, hv, hn, by omega,
    by omega, by omega, by omega, ?_⟩
  omega
end OMAH1Research
namespace OMAH1Research
theorem Q306
    (n P : ℕ) (hn : 0 < n) :
    ¬(4 * n).gcd P ∣ n ↔ 2 * n.gcd P ∣ P := by
  let d := n.gcd P
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.gcd_pos_of_pos_left P hn
  have hdn : d ∣ n := by dsimp [d]; exact Nat.gcd_dvd_left _ _
  have hdP : d ∣ P := by dsimp [d]; exact Nat.gcd_dvd_right _ _
  constructor
  · contrapose!
    intro hnot
    let a := n / d
    let b := P / d
    have hnFactor : d * a = n := by
      dsimp [a]
      exact Nat.mul_div_cancel' hdn
    have hPFactor : d * b = P := by
      dsimp [b]
      exact Nat.mul_div_cancel' hdP
    have htwoNot : ¬2 ∣ b := by
      intro htwo
      have hmul : d * 2 ∣ P :=
        (Nat.dvd_div_iff_mul_dvd hdP).mp (by simpa [b] using htwo)
      exact hnot (by simpa [mul_comm] using hmul)
    have hbOdd : Odd b := by
      rw [← Nat.not_even_iff_odd]
      simpa [even_iff_two_dvd] using htwoNot
    have hcopAB : a.Coprime b := by
      dsimp [a, b, d]
      exact Nat.coprime_div_gcd_div_gcd
        (Nat.gcd_pos_of_pos_left P hn)
    have hcop4B : (4 * a).Coprime b := by
      have htwo : (2 : ℕ).Coprime b := Nat.coprime_two_left.mpr hbOdd
      have hfour : (4 : ℕ).Coprime b := by
        simpa using htwo.mul_left htwo
      exact hfour.mul_left hcopAB
    have hgcd : (4 * n).gcd P = d := by
      rw [← hnFactor, ← hPFactor]
      calc
        (4 * (d * a)).gcd (d * b) = (d * (4 * a)).gcd (d * b) := by ring_nf
        _ = d * (4 * a).gcd b := Nat.gcd_mul_left d (4 * a) b
        _ = d := by rw [hcop4B.gcd_eq_one, mul_one]
    rw [hgcd]
    exact hdn
  · intro htwo hgdiv
    have htwoN : 2 * d ∣ 4 * n := by
      exact dvd_trans (Nat.mul_dvd_mul_left 2 hdn)
        (show 2 * n ∣ 4 * n by exact ⟨2, by ring⟩)
    have htwoG : 2 * d ∣ (4 * n).gcd P := by
      apply Nat.dvd_gcd htwoN
      simpa [d] using htwo
    have htwoDn : 2 * d ∣ n := dvd_trans htwoG hgdiv
    have htwoDd : 2 * d ∣ d := by
      have := Nat.dvd_gcd htwoDn (by simpa [d] using htwo)
      simpa [d] using this
    have hle : 2 * d ≤ d := Nat.le_of_dvd hdpos htwoDd
    omega
end OMAH1Research
namespace OMAH1Research
def Q15 (m : ℕ) : ℕ := m.factorization 2
lemma Q114 : Nat.factorization 2 2 = 1 := by
  norm_num [Nat.factorization]
lemma Q376 : Nat.factorization 4 2 = 2 := by
  change Nat.factorization (2 ^ 2) 2 = 2
  rw [Nat.factorization_pow]
  norm_num [Nat.factorization]
theorem Q104
    (n P : ℕ) (hn : 0 < n) (hP : 0 < P) :
    2 * n.gcd P ∣ P ↔ Q15 n < Q15 P := by
  let d := n.gcd P
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.gcd_pos_of_pos_left P hn
  have hdP : d ∣ P := by dsimp [d]; exact Nat.gcd_dvd_right _ _
  have hfacD : d.factorization 2 =
      min (n.factorization 2) (P.factorization 2) := by
    dsimp [d]
    rw [Nat.factorization_gcd (Nat.ne_of_gt hn) (Nat.ne_of_gt hP),
      Finsupp.inf_apply]
  constructor
  · intro hdvd
    have hfac := (Nat.factorization_le_iff_dvd
      (mul_ne_zero (by norm_num) (Nat.ne_of_gt hdpos))
      (Nat.ne_of_gt hP)).mpr hdvd
    have htwo := hfac 2
    rw [Nat.factorization_mul (by norm_num) (Nat.ne_of_gt hdpos),
      Finsupp.add_apply, Q114, hfacD] at htwo
    dsimp [Q15]
    omega
  · intro hlt
    apply (Nat.factorization_le_iff_dvd
      (mul_ne_zero (by norm_num) (Nat.ne_of_gt hdpos))
      (Nat.ne_of_gt hP)).mp
    intro p
    rw [Nat.factorization_mul (by norm_num) (Nat.ne_of_gt hdpos),
      Finsupp.add_apply]
    by_cases hp : p = 2
    · subst p
      rw [Q114, hfacD]
      dsimp [Q15] at hlt
      omega
    · have htwoZero : Nat.factorization 2 p = 0 := by
        by_cases hprime : Nat.Prime p
        · apply Nat.factorization_eq_zero_of_not_dvd
          intro hpdvd
          have hp12 := (Nat.dvd_prime Nat.prime_two).mp hpdvd
          rcases hp12 with hp1 | hp2
          · exact hprime.ne_one hp1
          · exact hp hp2
        · exact Nat.factorization_eq_zero_of_not_prime 2 hprime
      rw [htwoZero, zero_add]
      exact ((Nat.factorization_le_iff_dvd
        (Nat.ne_of_gt hdpos) (Nat.ne_of_gt hP)).mpr hdP) p
theorem Q258
    (m : ℕ) (hm : 0 < m) :
    Q15 (Q11 m) =
      if Even m then Q15 m + 1 else 2 := by
  unfold Q11 Q15
  split_ifs with he
  · rw [Nat.factorization_mul (by norm_num) (Nat.ne_of_gt hm),
      Finsupp.add_apply, Q114]
    omega
  · have htwoNot : ¬2 ∣ m := by
      simpa [even_iff_two_dvd] using he
    have hmzero : m.factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd htwoNot
    rw [Nat.factorization_mul (by norm_num) (Nat.ne_of_gt hm),
      Finsupp.add_apply, Q376, hmzero]
theorem Q315
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) {K v : ℕ}
    (h : v < Q15 (Q12 n K)) :
    ∃ i < K, v < Q15 (Q11 (n i)) := by
  induction K with
  | zero =>
      simp [Q12, Q15, Nat.factorization] at h
  | succ K ih =>
      have hPpos := Q82 n hpos K
      have hpPos : 0 < Q11 (n K) := by
        unfold Q11
        split <;> nlinarith [hpos K]
      have hmax : v < max
          (Q15 (Q12 n K))
          (Q15 (Q11 (n K))) := by
        simpa [Q12, Q15,
          Nat.factorization_lcm (Nat.ne_of_gt hPpos) (Nat.ne_of_gt hpPos),
          Finsupp.sup_apply] using h
      rcases (lt_max_iff.mp hmax) with hprev | hlast
      · obtain ⟨i, hiK, hi⟩ := ih hprev
        exact ⟨i, by omega, hi⟩
      · exact ⟨K, by omega, hlast⟩
def Q57 (n : ℕ → ℕ) (K : ℕ) : Prop :=
  2 ≤ Q15 (n K) ∧
    ∀ i < K, Q15 (n i) < Q15 (n K)
theorem Q247
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (K : ℕ)
    (hrec : Q57 n K) :
    ¬2 * (n K).gcd (Q12 n K) ∣
      Q12 n K := by
  intro hdvd
  have hPpos := Q82 n hpos K
  have hvlt : Q15 (n K) <
      Q15 (Q12 n K) :=
    (Q104
      (n K) (Q12 n K) (hpos K) hPpos).mp hdvd
  obtain ⟨i, hiK, hi⟩ := Q315
    n hpos hvlt
  have hv2 := hrec.1
  rw [Q258 (n i) (hpos i)] at hi
  split_ifs at hi with hie
  · have hir := hrec.2 i hiK
    omega
  · omega
end OMAH1Research
namespace OMAH1Research
theorem Q274
    {x y : ℕ} (hv : Q15 x < Q15 y)
    (hxy : y ≤ 2 * x) :
    ordCompl[2] y ≤ ordCompl[2] x := by
  let vx := Q15 x
  let vy := Q15 y
  let ox := ordCompl[2] x
  let oy := ordCompl[2] y
  have hxdec : 2 ^ vx * ox = x := by
    simpa [vx, ox, Q15] using Nat.ordProj_mul_ordCompl_eq_self x 2
  have hydec : 2 ^ vy * oy = y := by
    simpa [vy, oy, Q15] using Nat.ordProj_mul_ordCompl_eq_self y 2
  have hv' : vx < vy := by simpa [vx, vy] using hv
  obtain ⟨d, hvd0⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_iff.mpr hv')
  have hvd : vy = vx + 1 + d := by
    simpa [Nat.succ_eq_add_one] using hvd0
  have hfactor : 0 < 2 ^ (vx + 1) := pow_pos (by norm_num) _
  have hcancel : 2 ^ d * oy ≤ ox := by
    apply Nat.le_of_mul_le_mul_left (c := 2 ^ (vx + 1))
    · calc
        2 ^ (vx + 1) * (2 ^ d * oy) = 2 ^ vy * oy := by
          rw [hvd, pow_add]
          ring
        _ = y := hydec
        _ ≤ 2 * x := hxy
        _ = 2 ^ (vx + 1) * ox := by rw [← hxdec, pow_succ]; ring
    · exact hfactor
  have hoy : oy ≤ 2 ^ d * oy :=
    Nat.le_mul_of_pos_left oy (pow_pos (by norm_num) _)
  exact hoy.trans hcancel
theorem Q191
    {x y : ℕ} (hv : Q15 x < Q15 y)
    (hxy : y ≤ 2 * x)
    (hodd : ordCompl[2] y = ordCompl[2] x) :
    y = 2 * x := by
  let vx := Q15 x
  let vy := Q15 y
  let o := ordCompl[2] x
  have hxdec : 2 ^ vx * o = x := by
    simpa [vx, o, Q15] using Nat.ordProj_mul_ordCompl_eq_self x 2
  have hydec : 2 ^ vy * o = y := by
    simpa [vy, o, Q15, hodd] using
      Nat.ordProj_mul_ordCompl_eq_self y 2
  have hv' : vx < vy := by simpa [vx, vy] using hv
  obtain ⟨d, hvd0⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_iff.mpr hv')
  have hvd : vy = vx + 1 + d := by
    simpa [Nat.succ_eq_add_one] using hvd0
  apply le_antisymm hxy
  calc
    2 * x = 2 ^ (vx + 1) * o := by rw [← hxdec, pow_succ]; ring
    _ ≤ 2 ^ (vx + 1) * (2 ^ d * o) := by
      gcongr
      exact Nat.le_mul_of_pos_left o (pow_pos (by norm_num) _)
    _ = 2 ^ vy * o := by rw [hvd, pow_add]; ring
    _ = y := hydec
theorem Q141
    (x : ℕ → ℕ)
    (hv : ∀ t, Q15 (x t) < Q15 (x (t + 1)))
    (hbound : ∀ t, x (t + 1) ≤ 2 * x t) :
    ∃ T, ∀ t, T ≤ t → x (t + 1) = 2 * x t := by
  let o : ℕ → ℕ := fun t => ordCompl[2] (x t)
  have hoStep : ∀ t, o (t + 1) ≤ o t := by
    intro t
    exact Q274 (hv t) (hbound t)
  have hoAnti : Antitone o := antitone_nat_of_succ_le hoStep
  obtain ⟨T, hT⟩ := WellFoundedLT.antitone_chain_condition hoAnti
  refine ⟨T, fun t ht => ?_⟩
  apply Q191
    (hv t) (hbound t)
  exact (hT (t + 1) (by omega)).symm.trans (hT t ht)
end OMAH1Research
namespace OMAH1Research
theorem Q302 (m : ℕ) (hm : 0 < m) :
    Q15 (2 * m) = Q15 m + 1 := by
  unfold Q15
  rw [Nat.factorization_mul (by norm_num) (Nat.ne_of_gt hm),
    Finsupp.add_apply, Q114]
  omega
noncomputable def Q96 (n : ℕ → ℕ) (K : ℕ) : ℕ := by
  classical
  exact if h : ∃ i, K < i ∧ Q15 (n K) < Q15 (n i)
    then Nat.find h else K
lemma Q386 (n : ℕ → ℕ) (K : ℕ)
    (h : ∃ i, K < i ∧ Q15 (n K) < Q15 (n i)) :
    K < Q96 n K ∧
      Q15 (n K) < Q15 (n (Q96 n K)) := by
  classical
  rw [Q96, dif_pos h]
  exact Nat.find_spec h
lemma Q364 (n : ℕ → ℕ) (K j : ℕ)
    (h : ∃ i, K < i ∧ Q15 (n K) < Q15 (n i))
    (hj : K < j ∧ Q15 (n K) < Q15 (n j)) :
    Q96 n K ≤ j := by
  classical
  rw [Q96, dif_pos h]
  exact Nat.find_min' h hj
theorem Q78
    (n : ℕ → ℕ) (hmono : StrictMono n) (K j : ℕ)
    (hrec : Q57 n K)
    (hjK : K < j)
    (hjv : Q15 (n K) < Q15 (n j))
    (hjbound : n j ≤ 2 * n K) :
    Q57 n (Q96 n K) ∧
      K < Q96 n K ∧
      n (Q96 n K) ≤ 2 * n K := by
  let I := Q96 n K
  have hex : ∃ i, K < i ∧
      Q15 (n K) < Q15 (n i) := ⟨j, hjK, hjv⟩
  have hspec := Q386 n K hex
  have hIj : I ≤ j := by
    dsimp [I]
    exact Q364 n K j hex ⟨hjK, hjv⟩
  have hvalue : n I ≤ 2 * n K :=
    (hmono.monotone hIj).trans hjbound
  have hrecord : Q57 n I := by
    constructor
    · exact hrec.1.trans (hspec.2.le)
    · intro l hlI
      by_cases hlK : l < K
      · exact (hrec.2 l hlK).trans hspec.2
      · by_cases hlEq : l = K
        · simpa [hlEq] using hspec.2
        · have hKl : K < l := by omega
          have hnot : ¬Q15 (n K) < Q15 (n l) := by
            intro hlt
            have hIl : I ≤ l := by
              dsimp [I]
              exact Q364 n K l hex ⟨hKl, hlt⟩
            omega
          exact lt_of_le_of_lt (by omega) hspec.2
  exact ⟨hrecord, hspec.1, hvalue⟩
noncomputable def Q45 (n : ℕ → ℕ) (K : ℕ) : ℕ → ℕ
  | 0 => K
  | t + 1 => Q96 n (Q45 n K t)
theorem Q367
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (K₀ K : ℕ) (hK₀ : K₀ ≤ K) (hrecK : Q57 n K)
    (hdouble : ∀ i, K₀ ≤ i → Q57 n i →
      ∃ j, i < j ∧ n j = 2 * n i) :
    ∀ t,
      K₀ ≤ Q45 n K t ∧
      Q57 n (Q45 n K t) ∧
      Q45 n K t < Q45 n K (t + 1) ∧
      n (Q45 n K (t + 1)) ≤
        2 * n (Q45 n K t) := by
  intro t
  induction t with
  | zero =>
      dsimp [Q45]
      obtain ⟨j, hj, hjeq⟩ := hdouble K hK₀ hrecK
      have hjv : Q15 (n K) < Q15 (n j) := by
        rw [hjeq, Q302 (n K) (hpos K)]
        omega
      have hs := Q78
        n hmono K j hrecK hj hjv (by simp [hjeq])
      exact ⟨hK₀, hrecK, hs.2.1, hs.2.2⟩
  | succ t ih =>
      let I := Q45 n K (t + 1)
      have hI0 : K₀ ≤ I := ih.1.trans ih.2.2.1.le
      have hIrec : Q57 n I := by
        dsimp [I, Q45]
        obtain ⟨j, hj, hjeq⟩ := hdouble
          (Q45 n K t) ih.1 ih.2.1
        have hjv : Q15 (n (Q45 n K t)) <
            Q15 (n j) := by
          rw [hjeq, Q302
            (n (Q45 n K t)) (hpos _)]
          omega
        exact (Q78 n hmono
          (Q45 n K t) j ih.2.1 hj hjv
          (by simp [hjeq])).1
      obtain ⟨j, hj, hjeq⟩ := hdouble I hI0 hIrec
      have hjv : Q15 (n I) < Q15 (n j) := by
        rw [hjeq, Q302 (n I) (hpos I)]
        omega
      have hs := Q78
        n hmono I j hIrec hj hjv (by simp [hjeq])
      change K₀ ≤ I ∧ Q57 n I ∧
        I < Q45 n K (t + 1 + 1) ∧
        n (Q45 n K (t + 1 + 1)) ≤ 2 * n I
      simpa [I, Q45] using ⟨hI0, hIrec, hs.2.1, hs.2.2⟩
end OMAH1Research
namespace OMAH1Research
open Filter
open scoped BigOperators
def Q156 (n : ℕ → ℕ) : Prop :=
  ∀ V, ∃ K, V < Q15 (n K)
theorem Q279
    (n : ℕ → ℕ) (hunb : Q156 n) (K₀ : ℕ) :
    ∃ K, K₀ ≤ K ∧ Q57 n K := by
  classical
  let S := ∑ i ∈ Finset.range K₀, Q15 (n i)
  let V := S + 2
  let K := Nat.find (hunb V)
  have hKspec : V < Q15 (n K) := Nat.find_spec (hunb V)
  have hK₀ : K₀ ≤ K := by
    by_contra hnot
    have hKK₀ : K < K₀ := by omega
    have hmem : K ∈ Finset.range K₀ := Finset.mem_range.mpr hKK₀
    have hleS : Q15 (n K) ≤ S := by
      dsimp [S]
      exact Finset.single_le_sum
        (s := Finset.range K₀) (f := fun i => Q15 (n i))
        (fun i _ => Nat.zero_le _) hmem
    dsimp [V] at hKspec
    omega
  have hrecord : Q57 n K := by
    constructor
    · dsimp [V] at hKspec
      omega
    · intro i hiK
      have hnot : ¬V < Q15 (n i) := by
        intro hi
        have hKi : K ≤ i := Nat.find_min' (hunb V) hi
        omega
      omega
  exact ⟨K, hK₀, hrecord⟩
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
open scoped BigOperators
theorem Q79
    (C : ℕ → ℤ) (q : ℕ) (T Tconj : ℝ) (N : ℕ) (hq : 0 < q)
    (hpair : InScaledGoldenPair q T Tconj) :
    InScaledGoldenPair q
      (Q159 C T N)
      (Q60 C Tconj N) := by
  apply InScaledGoldenPair.sub hq
  · exact hpair.powers_mul N
  · apply Q338 hq
    intro m hm
    exact Q349 q hq (C m) (N - m)
theorem Q142
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (q : ℕ) (hq : 0 < q) (T Tconj : ℝ)
    (hsum : HasSum (fun m : ℕ =>
      (Q1 n m : ℝ) * (φ⁻¹) ^ m) T)
    (htotal : InScaledGoldenPair q T Tconj)
    (N M L : ℕ)
    (hblock : ∀ t < L,
      Q1 n (N + t) =
        Q1 n (M + t))
    (hne : Q17 (Q1 n) N ≠
      Q17 (Q1 n) M)
    (hsmall :
      (φ⁻¹) ^ L *
          (Q7 n (N + L) +
            Q7 n (M + L)) *
        (Q6 n Tconj N +
          Q6 n Tconj M) <
      (((q : ℕ) : ℝ)⁻¹) ^ 2) :
    False := by
  let C := Q1 n
  let x : ℝ := Q17 C N - Q17 C M
  let y : ℝ := Q60 C Tconj N -
    Q60 C Tconj M
  have hpairN := Q79
    C q T Tconj N hq htotal
  have hpairM := Q79
    C q T Tconj M hq htotal
  have hresN := Q95 C T hsum N
  have hresM := Q95 C T hsum M
  have hpair : InScaledGoldenPair q x y := by
    dsimp [x, y]
    rw [← hresN, ← hresM]
    exact hpairN.sub hq hpairM
  have hx : x ≠ 0 := sub_ne_zero.mpr hne
  have hlower := hpair.norm_lower hq hx
  have hxupper : |x| ≤
      (φ⁻¹) ^ L *
        (Q7 n (N + L) +
          Q7 n (M + L)) :=
    Q224
      n hpos hmono N M L hblock
  have hyupper : |y| ≤
      Q6 n Tconj N +
        Q6 n Tconj M :=
    Q212
      n hpos hmono Tconj N M
  have hpnonneg : 0 ≤
      (φ⁻¹) ^ L *
        (Q7 n (N + L) +
          Q7 n (M + L)) :=
    (abs_nonneg x).trans hxupper
  have hproduct : |x| * |y| ≤
      ((φ⁻¹) ^ L *
        (Q7 n (N + L) +
          Q7 n (M + L))) *
      (Q6 n Tconj N +
        Q6 n Tconj M) :=
    mul_le_mul hxupper hyupper (abs_nonneg _) hpnonneg
  exact (not_lt_of_ge (hlower.trans hproduct)) hsmall
theorem Q108
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (q : ℕ) (hq : 0 < q) (T Tconj : ℝ)
    (hsum : HasSum (fun m : ℕ =>
      (Q1 n m : ℝ) * (φ⁻¹) ^ m) T)
    (htotal : InScaledGoldenPair q T Tconj)
    (N M L J : ℕ)
    (hpre : ∀ t < L,
      Q1 n (N + t) =
        Q1 n (M + t))
    (hmismatch : Q1 n (N + L) ≠
      Q1 n (M + L))
    (hpost : ∀ t < J,
      Q1 n (N + L + 1 + t) =
        Q1 n (M + L + 1 + t))
    (hsmallPost :
      (φ⁻¹) ^ (J + 1) *
        (Q7 n (N + L + 1 + J) +
          Q7 n (M + L + 1 + J)) < 1)
    (hsmallPre :
      (φ⁻¹) ^ L *
          (Q7 n (N + L) +
            Q7 n (M + L)) *
        (Q6 n Tconj N +
          Q6 n Tconj M) <
      (((q : ℕ) : ℝ)⁻¹) ^ 2) :
    False := by
  apply Q142
    n hpos hmono q hq T Tconj hsum htotal N M L hpre
  · exact Q182
      n hpos hmono N M L J hpre hmismatch hpost hsmallPost
  · exact hsmallPre
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
theorem Q200
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (qden : ℕ) (hqden : 0 < qden) (T Tconj : ℝ)
    (hsum : HasSum (fun m : ℕ =>
      (Q1 n m : ℝ) * (φ⁻¹) ^ m) T)
    (htotal : InScaledGoldenPair qden T Tconj)
    (K H L J A X R : ℕ) (hA : 0 < A) (hKH : K < H)
    (hperiod : ∀ k < K, Q11 (n k) ∣ X)
    (htargetPre : ∀ s < L,
      Q5 (n K) (A + s + X) =
        Q5 (n K) (A + s))
    (htarget : Q5 (n K) (A + L + X) ≠
      Q5 (n K) (A + L))
    (htargetPost : ∀ s < J,
      Q5 (n K) (A + L + 1 + s + X) =
        Q5 (n K) (A + L + 1 + s))
    (C O : Finset ((ℕ × ℕ) × Bool))
    (hpartition : C ∪ O = Q18 n K H
      (L + 1 + J) A X (4 * n K))
    (hbudget :
      (∑ u ∈ O, (R / (Q2 n u /
        (Q2 n u).gcd (4 * n K)) + 1)) <
        (Q23 C (Q16 A X)
          (Q2 n) (4 * n K) R).card)
    (hcut : A + (4 * n K) * R + X + (L + 1 + J) < n H)
    (hsmallPost : ∀ t < R,
      let N := A + (4 * n K) * t
      (φ⁻¹) ^ (J + 1) *
        (Q7 n (N + L + 1 + J) +
          Q7 n (N + X + L + 1 + J)) < 1)
    (hsmallPre : ∀ t < R,
      let N := A + (4 * n K) * t
      (φ⁻¹) ^ L *
          (Q7 n (N + L) +
            Q7 n (N + X + L)) *
        (Q6 n Tconj N +
          Q6 n Tconj (N + X)) <
      (((qden : ℕ) : ℝ)⁻¹) ^ 2) :
    False := by
  obtain ⟨t, htR, hav⟩ :=
    Q153
      n hpos hmono K H (L + 1 + J) A X (4 * n K) R
      hA hKH C O hpartition hbudget hcut
  let N := A + (4 * n K) * t
  have htransport (u : ℕ) :
      Q5 (n K) (N + u) = Q5 (n K) (A + u) := by
    have hp := Q244 (n K) (A + u) t
    simpa [N, add_assoc, add_comm, add_left_comm, mul_comm] using hp
  have htransportX (u : ℕ) :
      Q5 (n K) (N + u + X) =
        Q5 (n K) (A + u + X) := by
    have hp := Q244 (n K) (A + u + X) t
    simpa [N, add_assoc, add_comm, add_left_comm, mul_comm] using hp
  have htargetPreN : ∀ s < L,
      Q5 (n K) (N + s + X) =
        Q5 (n K) (N + s) := by
    intro s hs
    rw [htransportX, htransport]
    exact htargetPre s hs
  have htargetN : Q5 (n K) (N + L + X) ≠
      Q5 (n K) (N + L) := by
    rw [htransportX, htransport]
    exact htarget
  have htargetPostN : ∀ s < J,
      Q5 (n K) (N + L + 1 + s + X) =
        Q5 (n K) (N + L + 1 + s) := by
    intro s hs
    have hx := htransportX (L + 1 + s)
    have hxbase := htransport (L + 1 + s)
    calc
      Q5 (n K) (N + L + 1 + s + X) =
          Q5 (n K) (A + L + 1 + s + X) := by
            simpa [add_assoc] using hx
      _ = Q5 (n K) (A + L + 1 + s) := htargetPost s hs
      _ = Q5 (n K) (N + L + 1 + s) := by
        simpa [add_assoc] using hxbase.symm
  have hpat := Q184
    n hpos hmono K L J N X hperiod htargetPreN htargetN htargetPostN hav
  apply Q108
    n hpos hmono qden hqden T Tconj hsum htotal N (N + X) L J
  · intro s hs
    simpa [add_assoc, add_comm, add_left_comm] using (hpat.1 s hs).symm
  · simpa [add_assoc, add_comm, add_left_comm] using ne_comm.mp hpat.2.1
  · intro s hs
    simpa [add_assoc, add_comm, add_left_comm] using (hpat.2.2 s hs).symm
  · simpa [N, add_assoc, add_comm, add_left_comm] using hsmallPost t htR
  · simpa [N, add_assoc, add_comm, add_left_comm] using hsmallPre t htR
theorem Q236
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (qden : ℕ) (Tconj : ℝ)
    (K H L J A X R : ℕ)
    (hcut : A + (4 * n K) * R + X + (L + 1 + J) < n H)
    (hpostCap :
      (φ⁻¹) ^ (J + 1) * (2 * Q8 H) < 1)
    (hpreCap :
      (φ⁻¹) ^ L * (2 * Q8 H) *
        (2 * Q10 Tconj H) <
        (((qden : ℕ) : ℝ)⁻¹) ^ 2) :
    (∀ t < R,
      let N := A + (4 * n K) * t
      (φ⁻¹) ^ (J + 1) *
        (Q7 n (N + L + 1 + J) +
          Q7 n (N + X + L + 1 + J)) < 1) ∧
    (∀ t < R,
      let N := A + (4 * n K) * t
      (φ⁻¹) ^ L *
          (Q7 n (N + L) +
            Q7 n (N + X + L)) *
        (Q6 n Tconj N +
          Q6 n Tconj (N + X)) <
      (((qden : ℕ) : ℝ)⁻¹) ^ 2) := by
  have hp : 0 < 4 * n K := by nlinarith [hpos K]
  have htailCapNonneg := Q34 H
  have hconjCapNonneg := Q36 Tconj H
  constructor
  · intro t ht
    let N := A + (4 * n K) * t
    have hpt : (4 * n K) * t < (4 * n K) * R :=
      (Nat.mul_lt_mul_left hp).mpr ht
    have hx₁ : N + L + 1 + J < n H := by dsimp [N]; omega
    have hx₂ : N + X + L + 1 + J < n H := by dsimp [N]; omega
    have hb₁ := Q27 n hpos hmono hx₁
    have hb₂ := Q27 n hpos hmono hx₂
    calc
      (φ⁻¹) ^ (J + 1) *
          (Q7 n (N + L + 1 + J) +
            Q7 n (N + X + L + 1 + J)) ≤
        (φ⁻¹) ^ (J + 1) * (2 * Q8 H) := by
          gcongr
          linarith
      _ < 1 := hpostCap
  · intro t ht
    let N := A + (4 * n K) * t
    have hpt : (4 * n K) * t < (4 * n K) * R :=
      (Nat.mul_lt_mul_left hp).mpr ht
    have hxN : N < n H := by dsimp [N]; omega
    have hxNX : N + X < n H := by dsimp [N]; omega
    have hxL : N + L < n H := by dsimp [N]; omega
    have hxXL : N + X + L < n H := by dsimp [N]; omega
    have ht₁ := Q27 n hpos hmono hxL
    have ht₂ := Q27 n hpos hmono hxXL
    have hc₁ := Q39
      n hpos hmono Tconj hxN
    have hc₂ := Q39
      n hpos hmono Tconj hxNX
    have htailSum :
        Q7 n (N + L) +
          Q7 n (N + X + L) ≤ 2 * Q8 H := by
      linarith
    have hconjSum :
        Q6 n Tconj N +
          Q6 n Tconj (N + X) ≤
        2 * Q10 Tconj H := by linarith
    have hconjSumNonneg : 0 ≤
        Q6 n Tconj N +
          Q6 n Tconj (N + X) := by
      unfold Q6
      have hden : 0 < 1 - φ⁻¹ := sub_pos.mpr
        (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)
      positivity
    have hfirstNonneg : 0 ≤
        (φ⁻¹) ^ L * (2 * Q8 H) := by positivity
    calc
      (φ⁻¹) ^ L *
          (Q7 n (N + L) +
            Q7 n (N + X + L)) *
        (Q6 n Tconj N +
          Q6 n Tconj (N + X)) ≤
        (φ⁻¹) ^ L * (2 * Q8 H) *
          (Q6 n Tconj N +
            Q6 n Tconj (N + X)) := by
          gcongr
      _ ≤ (φ⁻¹) ^ L * (2 * Q8 H) *
          (2 * Q10 Tconj H) :=
        mul_le_mul_of_nonneg_left hconjSum hfirstNonneg
      _ < (((qden : ℕ) : ℝ)⁻¹) ^ 2 := hpreCap
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
open scoped BigOperators
theorem Q195
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (qden : ℕ) (hqden : 0 < qden) (T Tconj : ℝ)
    (hsum : HasSum (fun m : ℕ =>
      (Q1 n m : ℝ) * (φ⁻¹) ^ m) T)
    (htotal : InScaledGoldenPair qden T Tconj)
    (q : ℕ) (hq : (2 : ℝ) ≤ c ^ q)
    (K G B L J X r v : ℕ) (hKG : K < G) (hB : 0 < B)
    (hvalues : ∀ j, K < j → j < G → n j ≤ B)
    (hL : L < n K) (hJ : J < n K)
    (hX : X = r + (2 * n K) * v) (hv : Even v)
    (hrlt : r < 2 * n K)
    (hrLeft : L < r) (hrRight : r + J < 2 * n K)
    (hrUpper : r ≤ n K + L)
    (hsRWindow : n K + L - r < L + 1 + J)
    (hprefix : Q12 n K ∣ X)
    (hnoDouble : ∀ j, K < j → j < G → n j ≠ 2 * n K)
    (hdensity :
      let W := L + 1 + J
      let d := (Q0 K G).card
      (8 : ℝ) * ((2 * d + 1) * (2 * d + 2) : ℕ) *
        (W ^ 2 *
            (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
          W * n K * ((1 - c⁻¹)⁻¹ * (n G : ℝ)⁻¹)) < 1)
    (hpostCap :
      let A := n K - L
      let W := L + 1 + J
      let p := 4 * n K
      let d := (Q0 K G).card
      let Dmax := (2 * d + 1) * (2 * d + 2)
      let Mmax := B ^ (2 * d)
      let U := A + p * Mmax + X + W
      let V := 4 * p * Dmax * W
      let A₀ := U + V * G
      let B₀ := V * q
      let N := A₀ + B₀ + 1
      let t := Nat.clog 2 N
      let H := G + q * (4 * t + 4)
      (φ⁻¹) ^ (J + 1) * (2 * Q8 H) < 1)
    (hpreCap :
      let A := n K - L
      let W := L + 1 + J
      let p := 4 * n K
      let d := (Q0 K G).card
      let Dmax := (2 * d + 1) * (2 * d + 2)
      let Mmax := B ^ (2 * d)
      let U := A + p * Mmax + X + W
      let V := 4 * p * Dmax * W
      let A₀ := U + V * G
      let B₀ := V * q
      let N := A₀ + B₀ + 1
      let t := Nat.clog 2 N
      let H := G + q * (4 * t + 4)
      (φ⁻¹) ^ L * (2 * Q8 H) *
        (2 * Q10 Tconj H) <
        (((qden : ℕ) : ℝ)⁻¹) ^ 2) :
    False := by
  classical
  let A := n K - L
  let W := L + 1 + J
  let p := 4 * n K
  let sR := n K + L - r
  let d := (Q0 K G).card
  let Dmax := (2 * d + 1) * (2 * d + 2)
  let Mmax := B ^ (2 * d)
  let U := A + p * Mmax + X + W
  let V := 4 * p * Dmax * W
  let A₀ := U + V * G
  let B₀ := V * q
  let N := A₀ + B₀ + 1
  let t := Nat.clog 2 N
  let H := G + q * (4 * t + 4)
  let C0 := Q28 n K G W A X p L sR
  let O := Q18 n K H W A X p \ C0
  have hcert := Q204
    n hpos hmono c hc hratio q hq K G B L J X r v hKG hB hvalues
      hL hX hv hrUpper hsRWindow hnoDouble hdensity
  change ∃ R : ℕ, 0 < R ∧
      (∑ u ∈ O, (R / (Q2 n u /
        (Q2 n u).gcd p) + 1)) <
        (Q23 C0 (Q16 A X)
          (Q2 n) p R).card ∧
      A + p * R + X + W < n H at hcert
  obtain ⟨R, hR, hbudget, hcut⟩ := hcert
  have hA : 0 < A := by dsimp [A]; omega
  have hGH : G ≤ H := by dsimp [H]; omega
  have hKH : K < H := lt_of_lt_of_le hKG hGH
  have hrmod : r = X % (2 * n K) := by
    rw [hX, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrlt]
  have htarget := Q177
    (n K) L J X r (hpos K) hL hJ hrmod hrLeft hrRight
  have hperiod : ∀ k < K, Q11 (n k) ∣ X := by
    intro k hk
    exact dvd_trans (Q71 n hk) hprefix
  have hCsub : C0 ⊆ Q18 n K H W A X p := by
    intro u hu
    have huG := (Finset.mem_filter.mp hu).1
    have huGdata := Finset.mem_filter.mp huG
    apply Finset.mem_filter.mpr
    refine ⟨?_, huGdata.2⟩
    have huOuter := Finset.mem_product.mp huGdata.1
    have huInner := Finset.mem_product.mp huOuter.1
    have hjData := Finset.mem_filter.mp huInner.1
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, huInner.2⟩, huOuter.2⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (lt_of_lt_of_le
      (Finset.mem_range.mp hjData.1) hGH), hjData.2⟩
  have hpartition : C0 ∪ O =
      Q18 n K H W A X p :=
    Finset.union_sdiff_of_subset hCsub
  have hnorm := Q236
    n hpos hmono qden Tconj K H L J A X R
    (by simpa [p, W] using hcut)
    (by simpa [A, W, p, d, Dmax, Mmax, U, V, A₀, B₀, N, t, H]
      using hpostCap)
    (by simpa [A, W, p, d, Dmax, Mmax, U, V, A₀, B₀, N, t, H]
      using hpreCap)
  exact Q200
    n hpos hmono qden hqden T Tconj hsum htotal
      K H L J A X R hA hKH hperiod
      htarget.1 htarget.2.1 htarget.2.2 C0 O hpartition
      (by simpa [p] using hbudget)
      (by simpa [p, W] using hcut) hnorm.1 hnorm.2
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
theorem Q245
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (qden : ℕ) (hqden : 0 < qden) (T Tconj : ℝ)
    (hsum : HasSum (fun m : ℕ =>
      (Q1 n m : ℝ) * (φ⁻¹) ^ m) T)
    (htotal : InScaledGoldenPair qden T Tconj)
    (q : ℕ) (hqpos : 0 < q) (hq : (2 : ℝ) ≤ c ^ q)
    (K w X r v : ℕ) (hwpos : 0 < w)
    (hPX : Q12 n K ∣ X)
    (hXbound : X < (4 * n K) * Q12 n K)
    (hX : X = r + (2 * n K) * v) (hv : Even v)
    (hrlt : r < 2 * n K)
    (hrLeft : w < r) (hrRight : r + w < 2 * n K)
    (hrUpper : r ≤ n K + w)
    (hsRWindow : n K + w - r < w + 1 + w)
    (hnoDouble : ∀ j, K < j → n j ≠ 2 * n K)
    (hfirst :
      let W := w + 1 + w
      (5184 : ℝ) * q ^ 2 *
        (c⁻¹ * (1 - c⁻¹)⁻¹) * W ^ 4 < n K)
    (hsecond :
      let W := w + 1 + w
      (5184 : ℝ) * q ^ 2 * (1 - c⁻¹)⁻¹ < W ^ 5)
    (hcaps :
      let P := Q12 n K
      let W := w + 1 + w
      let B := n K * W ^ 8
      let Q := 8 * q * W
      ∀ X G,
        X < (4 * n K) * P →
        G ≤ K + Q →
        (Q0 K G).card ≤ Q →
        let H := Q21 n K G B w w X q
        (φ⁻¹) ^ (w + 1) * (2 * Q8 H) < 1 ∧
        (φ⁻¹) ^ w * (2 * Q8 H) *
          (2 * Q10 Tconj H) <
          (((qden : ℕ) : ℝ)⁻¹) ^ 2) :
    False := by
  let P := Q12 n K
  let W := w + 1 + w
  let B := n K * W ^ 8
  let Q := 8 * q * W
  have hWpos : 0 < W := by dsimp [W]; omega
  have hmpos := hpos K
  obtain ⟨G, hKG, hBG, hvalues, hGbound, hdBound⟩ :=
    Q180
      n hpos hmono c hc hratio q hq K W hWpos
  let d := (Q0 K G).card
  have hBpos : 0 < B := by
    dsimp [B]
    exact mul_pos hmpos (pow_pos hWpos _)
  have hsimple := Q109
    c hc q W (n K) hqpos hWpos hmpos
    (by simpa [W] using hfirst) (by simpa [W] using hsecond)
  have hdensity := Q135
    n hpos c hc q K G W d hWpos
      (by simpa [d, Q] using hdBound)
      (by simpa [B] using hBG)
      (by simpa [B, Q] using hsimple)
  have hcap := hcaps X G
    (by simpa [P] using hXbound)
    (by simpa [Q] using hGbound)
    (by simpa [Q, d] using hdBound)
  apply Q195
    n hpos hmono c hc hratio qden hqden T Tconj hsum htotal q hq
      K G B w w X r v hKG hBpos hvalues
  · omega
  · omega
  · exact hX
  · exact hv
  · exact hrlt
  · exact hrLeft
  · exact hrRight
  · exact hrUpper
  · exact hsRWindow
  · exact hPX
  · intro j hKj _hjG
    exact hnoDouble j hKj
  · simpa [W, d] using hdensity
  · simpa [P, W, B, Q, Q21, d] using hcap.1
  · simpa [P, W, B, Q, Q21, d] using hcap.2
end OMAH1Research
namespace OMAH1Research
open Filter Topology Real goldenRatio
theorem Q161
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (qden : ℕ) (hqden : 0 < qden) (T Tconj : ℝ)
    (hsum : HasSum (fun m : ℕ =>
      (Q1 n m : ℝ) * (φ⁻¹) ^ m) T)
    (htotal : InScaledGoldenPair qden T Tconj)
    (q : ℕ) (hqpos : 0 < q) (hq : (2 : ℝ) ≤ c ^ q) :
    ∀ᶠ K : ℕ in atTop,
      ¬(4 * n K).gcd (Q12 n K) ∣ n K ∨
        ∃ j, K < j ∧ n j = 2 * n K := by
  let ε : ℝ := (((qden : ℕ) : ℝ)⁻¹) ^ 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hevent : ∀ᶠ w : ℕ in atTop,
      2 ≤ w ∧
      (let W : ℕ := w + 1 + w
       (5184 : ℝ) * q ^ 2 *
            (c⁻¹ * (1 - c⁻¹)⁻¹) * W ^ 4 < (w : ℝ) ^ 8 ∧
          (5184 : ℝ) * q ^ 2 * (1 - c⁻¹)⁻¹ < (W : ℝ) ^ 5) ∧
      ((φ⁻¹) ^ (w + 1) *
            (2 * Q8 (Q3 q w)) < 1 ∧
        (φ⁻¹) ^ w *
            (2 * Q8 (Q3 q w)) *
            (2 * Q10 Tconj
              (Q3 q w)) < ε) := by
    exact (eventually_ge_atTop 2).and
      ((Q316 c hc q).and
        (Q317 q Tconj ε hε))
  have hroot := Q147 n hmono
  filter_upwards [hroot.eventually hevent] with K hK
  let w := Q55 n K
  change ¬(4 * n K).gcd (Q12 n K) ∣ n K ∨
    ∃ j, K < j ∧ n j = 2 * n K
  by_contra hstruct
  push Not at hstruct
  rcases hstruct with ⟨hgdiv, hnoDouble⟩
  have hw : 2 ≤ w := hK.1
  have hd := hK.2.1
  have hncap := hK.2.2
  have hlow : w ^ 8 ≤ n K := Q171 n K
  have hupp : n K ≤ (w + 1) ^ 8 :=
    (Q122 n K).le
  have h2w_sq : 2 * w ≤ w ^ 2 := by nlinarith
  have hsquare_eighth : w ^ 2 < w ^ 8 :=
    Nat.pow_lt_pow_right (by omega) (by norm_num)
  have hwindow : 2 * w < n K :=
    (h2w_sq.trans_lt hsquare_eighth).trans_le hlow
  obtain ⟨hfirst, hsecond⟩ := Q297
    c q w (n K) hd.1 hd.2 hlow
  obtain ⟨X, r, v, hPX, hXbound, hX, hv, _hrpos, hrlt,
      hrLeft, hrRight, hrUpper, hsRWindow⟩ :=
    Q265
      (Q12 n K) (n K) w (hpos K) hwindow hgdiv
  apply Q245
    n hpos hmono c hc hratio qden hqden T Tconj hsum htotal
      q hqpos hq K w X r v (by omega) hPX hXbound hX hv hrlt
      hrLeft hrRight hrUpper hsRWindow hnoDouble hfirst hsecond
  let P := Q12 n K
  let W := w + 1 + w
  let B := n K * W ^ 8
  let Q := 8 * q * W
  dsimp only
  intro X' G hX' hG hdG
  let H := Q21 n K G B w w X' q
  have hHupper : H ≤ Q59 n K w q := by
    exact Q92
      n hpos K w q X' G (by omega)
        (by simpa [P] using hX')
        (by simpa [Q, W] using hG)
        (by simpa [Q, W] using hdG)
  have hUpperWindow : Q59 n K w q ≤
      Q3 q w :=
    Q125 n hpos hmono K w q hupp
  exact Q286
    Tconj q w H (hHupper.trans hUpperWindow) hncap.1
      (by simpa only [ε] using hncap.2)
end OMAH1Research
namespace OMAH1Research
open Filter
open Real goldenRatio
theorem Q155
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (qden : ℕ) (hqden : 0 < qden) (T Tconj : ℝ)
    (hsum : HasSum (fun m : ℕ =>
      (Q1 n m : ℝ) * (φ⁻¹) ^ m) T)
    (htotal : InScaledGoldenPair qden T Tconj)
    (q : ℕ) (hqpos : 0 < q) (hq : (2 : ℝ) ≤ c ^ q) :
    ∀ᶠ K : ℕ in atTop,
      Q57 n K →
        ∃ j, K < j ∧ n j = 2 * n K := by
  filter_upwards [Q161
    n hpos hmono c hc hratio qden hqden T Tconj hsum htotal
      q hqpos hq] with K hK
  intro hrec
  rcases hK with hg | hd
  · have hp : 2 * (n K).gcd (Q12 n K) ∣
        Q12 n K :=
      (Q306
        (n K) (Q12 n K) (hpos K)).mp hg
    exact False.elim
      (Q247 n hpos K hrec hp)
  · exact hd
theorem Q120
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (qden : ℕ) (hqden : 0 < qden) (T Tconj : ℝ)
    (hsum : HasSum (fun m : ℕ =>
      (Q1 n m : ℝ) * (φ⁻¹) ^ m) T)
    (htotal : InScaledGoldenPair qden T Tconj)
    (q : ℕ) (hqpos : 0 < q) (hq : (2 : ℝ) ≤ c ^ q)
    (hunb : Q156 n) :
    ∃ m : ℕ, 0 < m ∧ ∃ k : ℕ → ℕ, StrictMono k ∧
      ∀ s, n (k s) = m * 2 ^ s := by
  have hevent := Q155
    n hpos hmono c hc hratio qden hqden T Tconj hsum htotal q hqpos hq
  rw [eventually_atTop] at hevent
  obtain ⟨K₀, hdouble⟩ := hevent
  obtain ⟨K, hK₀, hrec⟩ :=
    Q279 n hunb K₀
  have hprops := Q367
    n hpos hmono K₀ K hK₀ hrec (fun i hi hirec => hdouble i hi hirec)
  let x : ℕ → ℕ := fun t => n (Q45 n K t)
  have hv : ∀ t, Q15 (x t) < Q15 (x (t + 1)) := by
    intro t
    have ht := hprops t
    have ht1 := hprops (t + 1)
    exact ht1.2.1.2 (Q45 n K t) ht.2.2.1
  have hxbound : ∀ t, x (t + 1) ≤ 2 * x t := fun t => (hprops t).2.2.2
  obtain ⟨R, hR⟩ :=
    Q141 x hv hxbound
  let m := x R
  let k : ℕ → ℕ := fun s => Q45 n K (R + s)
  have hkmono : StrictMono k := by
    apply strictMono_nat_of_lt_succ
    intro s
    exact (hprops (R + s)).2.2.1
  have hformula : ∀ s, n (k s) = m * 2 ^ s := by
    intro s
    induction s with
    | zero => simp [k, m, x]
    | succ s ih =>
        have hstep := hR (R + s) (by omega)
        change n (Q45 n K (R + (s + 1))) = m * 2 ^ (s + 1)
        have hidx : R + (s + 1) = (R + s) + 1 := by omega
        rw [hidx]
        change x (R + s + 1) = m * 2 ^ (s + 1)
        rw [hstep]
        change 2 * n (k s) = m * 2 ^ (s + 1)
        rw [ih, pow_succ]
        ring
  refine ⟨m, ?_, k, hkmono, hformula⟩
  exact hpos _
end OMAH1Research
namespace OMAH1Research
open Filter Topology
noncomputable def Q38 (k : ℕ → ℕ) : ℕ → ℕ :=
  Nat.nth (fun i => i ∉ Set.range k)
noncomputable def Q221
    (n k : ℕ → ℕ) : ℕ → ℕ :=
  fun t => n (Q38 k t)
lemma Q301
    (k : ℕ → ℕ)
    (hinf : {i : ℕ | i ∉ Set.range k}.Infinite) :
    StrictMono (Q38 k) := by
  exact Nat.nth_strictMono hinf
lemma Q281
    (k : ℕ → ℕ)
    (hinf : {i : ℕ | i ∉ Set.range k}.Infinite) (t : ℕ) :
    Q38 k t ∉ Set.range k := by
  exact Nat.nth_mem_of_infinite hinf t
lemma Q330
    (k : ℕ → ℕ)
    (hinf : {i : ℕ | i ∉ Set.range k}.Infinite) :
    Set.range (Q38 k) = (Set.range k)ᶜ := by
  exact Nat.range_nth_of_infinite hinf
theorem Q342
    (f : ℕ → ℝ) (hf : Summable f)
    (k : ℕ → ℕ) (hk : StrictMono k)
    (hinf : {i : ℕ | i ∉ Set.range k}.Infinite) :
    (∑' s : ℕ, f (k s)) +
      (∑' t : ℕ, f (Q38 k t)) =
        ∑' i : ℕ, f i := by
  let S : Set ℕ := Set.range k
  have hsplit := hf.tsum_subtype_add_tsum_subtype_compl S
  have htail : (∑' s : ℕ, f (k s)) = ∑' x : S, f x := by
    let e : ℕ ≃ S := Equiv.ofInjective k hk.injective
    calc
      (∑' s : ℕ, f (k s)) = ∑' s : ℕ, f (e s) := by
        apply tsum_congr
        intro s
        change f (k s) = f ((Equiv.ofInjective k hk.injective s : S).val)
        congr 1
      _ = ∑' x : S, f x := e.tsum_eq (fun x : S => f x)
  let C : Set ℕ := {i : ℕ | i ∉ Set.range k}
  have hCinf : C.Infinite := by simpa [C] using hinf
  have hcomp : (∑' t : ℕ, f (Q38 k t)) =
      ∑' x : C, f x := by
    let e : ℕ ≃o C := @Nat.Subtype.orderIsoOfNat C hCinf.to_subtype
    have heq (t : ℕ) : Q38 k t = (e t : ℕ) := by
      dsimp [Q38, e, C, S]
      exact Nat.nth_apply_eq_orderIsoOfNat hinf t
    calc
      (∑' t : ℕ, f (Q38 k t)) =
          ∑' t : ℕ, f (e t) := by
        apply tsum_congr
        intro t
        rw [heq]
      _ = ∑' x : C, f x := e.toEquiv.tsum_eq (fun x : C => f x)
  have hCS : C = (Sᶜ : Set ℕ) := by
    ext i
    simp [C, S]
  rw [hCS] at hcomp
  rw [htail, hcomp]
  exact hsplit
end OMAH1Research
namespace OMAH1Research
open Filter Topology
open scoped BigOperators
theorem Q375 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun j : ℕ => x ^ (2 ^ j) / (1 - x ^ (2 ^ (j + 1)))) (x / (1 - x)) := by
  let u : ℕ → ℝ := fun j => x ^ (2 ^ j) / (1 - x ^ (2 ^ j))
  have hpow : Tendsto (fun j : ℕ => x ^ (2 ^ j)) atTop (𝓝 0) := by
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one hx0 hx1).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
  have hu : Tendsto u atTop (𝓝 0) := by
    have hden : Tendsto (fun j : ℕ => 1 - x ^ (2 ^ j)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hpow
    change Tendsto
      ((fun j : ℕ => x ^ (2 ^ j)) / (fun j : ℕ => 1 - x ^ (2 ^ j)))
      atTop (𝓝 0)
    convert hpow.div hden (by norm_num : (1 - 0 : ℝ) ≠ 0) using 1
    norm_num
  have hden_pos (j : ℕ) : 0 < 1 - x ^ (2 ^ j) := by
    have hp : x ^ (2 ^ j) < 1 := pow_lt_one₀ hx0 hx1 (by positivity)
    linarith
  have hterm (j : ℕ) :
      x ^ (2 ^ j) / (1 - x ^ (2 ^ (j + 1))) = u j - u (j + 1) := by
    have hpow2 : x ^ (2 ^ (j + 1)) = (x ^ (2 ^ j)) ^ 2 := by
      rw [pow_succ, pow_mul]
    dsimp [u]
    rw [hpow2]
    have h₁ : 1 - x ^ (2 ^ j) ≠ 0 := ne_of_gt (hden_pos j)
    have h₂ : 1 - (x ^ (2 ^ j)) ^ 2 ≠ 0 := by
      rw [← hpow2]
      exact ne_of_gt (hden_pos (j + 1))
    field_simp
    ring
  have hnonneg (j : ℕ) : 0 ≤ x ^ (2 ^ j) / (1 - x ^ (2 ^ (j + 1))) := by
    exact div_nonneg (pow_nonneg hx0 _) (le_of_lt (hden_pos (j + 1)))
  rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg]
  have htel (N : ℕ) :
      (∑ j ∈ Finset.range N, x ^ (2 ^ j) / (1 - x ^ (2 ^ (j + 1)))) = u 0 - u N := by
    calc
      _ = ∑ j ∈ Finset.range N, (u j - u (j + 1)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hterm j
      _ = u 0 - u N := Finset.sum_range_sub' u N
  have hlim : Tendsto (fun N : ℕ => u 0 - u N) atTop (𝓝 (u 0 - 0)) :=
    tendsto_const_nhds.sub hu
  simpa [htel, u] using hlim
open Real goldenRatio
theorem Q388 (r : ℕ) (hr : 0 < r) :
    (Nat.fib (2 * r) : ℝ)⁻¹ =
      √5 * (φ⁻¹) ^ (2 * r) / (1 - ((φ⁻¹) ^ (2 * r)) ^ 2) := by
  have hpsi : ψ = -φ⁻¹ := by
    linarith [Real.inv_goldenRatio]
  have hpsi_pow : ψ ^ (2 * r) = (φ⁻¹) ^ (2 * r) := by
    rw [hpsi, pow_mul, pow_mul]
    congr 1
    ring
  have hphi_ne : φ ≠ 0 := Real.goldenRatio_ne_zero
  have hunit : φ ^ (2 * r) * (φ⁻¹) ^ (2 * r) = 1 := by
    rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hphi_ne)]
  have hinv0 : 0 ≤ φ⁻¹ := le_of_lt (inv_pos.mpr Real.goldenRatio_pos)
  have hinv1 : φ⁻¹ < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hy1 : (φ⁻¹) ^ (2 * r) < 1 :=
    pow_lt_one₀ hinv0 hinv1
      (Nat.ne_of_gt (Nat.mul_pos (by norm_num : 0 < (2 : ℕ)) hr))
  have hy0 : 0 ≤ (φ⁻¹) ^ (2 * r) := pow_nonneg hinv0 _
  have hden : 1 - ((φ⁻¹) ^ (2 * r)) ^ 2 ≠ 0 := by
    have hsquare : ((φ⁻¹) ^ (2 * r)) ^ 2 < 1 :=
      pow_lt_one₀ hy0 hy1 (by norm_num : (2 : ℕ) ≠ 0)
    linarith
  apply inv_eq_of_mul_eq_one_right
  rw [Real.coe_fib_eq, hpsi_pow]
  have hsqrt : √5 ≠ 0 := by positivity
  calc
    ((φ ^ (2 * r) - (φ⁻¹) ^ (2 * r)) / √5) *
        (√5 * (φ⁻¹) ^ (2 * r) / (1 - ((φ⁻¹) ^ (2 * r)) ^ 2)) =
        (φ ^ (2 * r) * (φ⁻¹) ^ (2 * r) - ((φ⁻¹) ^ (2 * r)) ^ 2) /
          (1 - ((φ⁻¹) ^ (2 * r)) ^ 2) := by
            field_simp [hsqrt, hden]
    _ = 1 := by rw [hunit]; exact div_self hden
theorem Q325 (r : ℕ) (hr : 0 < r) :
    HasSum (fun j : ℕ => (Nat.fib (2 * (r * 2 ^ j)) : ℝ)⁻¹)
      (√5 * ((φ⁻¹) ^ (2 * r) / (1 - (φ⁻¹) ^ (2 * r)))) := by
  let x : ℝ := (φ⁻¹) ^ (2 * r)
  have hinv0 : 0 ≤ φ⁻¹ := le_of_lt (inv_pos.mpr Real.goldenRatio_pos)
  have hinv1 : φ⁻¹ < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hx0 : 0 ≤ x := pow_nonneg hinv0 _
  have hx1 : x < 1 := by
    exact pow_lt_one₀ hinv0 hinv1
      (Nat.ne_of_gt (Nat.mul_pos (by norm_num : 0 < (2 : ℕ)) hr))
  have hscaled := (Q375 x hx0 hx1).const_smul √5
  have hscaled' :
      HasSum (fun j : ℕ => √5 * (x ^ (2 ^ j) / (1 - x ^ (2 ^ (j + 1)))))
        (√5 * (x / (1 - x))) := by
    simpa only [smul_eq_mul] using hscaled
  apply hscaled'.congr_fun
  intro j
  rw [Q388 (r * 2 ^ j) (Nat.mul_pos hr (by positivity))]
  have hexp : 2 * (r * 2 ^ j) = (2 * r) * 2 ^ j := by ring
  have hnext : x ^ (2 ^ (j + 1)) = (x ^ (2 ^ j)) ^ 2 := by
    rw [pow_succ, pow_mul]
  rw [hexp, pow_mul, ← hnext]
  dsimp [x]
  ring
theorem Q361 (r : ℕ) (hr : 0 < r) :
    φ ^ (2 * r) =
      ((Nat.fib (2 * r) : ℝ) / 2 + Nat.fib (2 * r - 1)) +
        ((Nat.fib (2 * r) : ℝ) / 2) * √5 := by
  have hn : (2 * r - 1) + 1 = 2 * r := by omega
  calc
    φ ^ (2 * r) = φ ^ ((2 * r - 1) + 1) := by rw [hn]
    _ = φ * Nat.fib ((2 * r - 1) + 1) + Nat.fib (2 * r - 1) :=
      (Real.goldenRatio_mul_fib_succ_add_fib (2 * r - 1)).symm
    _ = _ := by rw [hn]; change ((1 + √5) / 2) * _ + _ = _; ring
theorem Q368 (r : ℕ) (hr : 0 < r) :
    ψ ^ (2 * r) =
      ((Nat.fib (2 * r) : ℝ) / 2 + Nat.fib (2 * r - 1)) -
        ((Nat.fib (2 * r) : ℝ) / 2) * √5 := by
  have hn : (2 * r - 1) + 1 = 2 * r := by omega
  calc
    ψ ^ (2 * r) = ψ ^ ((2 * r - 1) + 1) := by rw [hn]
    _ = ψ * Nat.fib ((2 * r - 1) + 1) + Nat.fib (2 * r - 1) :=
      (Real.goldenConj_mul_fib_succ_add_fib (2 * r - 1)).symm
    _ = _ := by rw [hn]; change ((1 - √5) / 2) * _ + _ = _; ring
theorem Q340 (r : ℕ) (hr : 0 < r) :
    √5 / (φ ^ (2 * r) - 1) =
      5 * ((Nat.fib (2 * r) : ℝ) / 2) /
          (2 * ((Nat.fib (2 * r) : ℝ) / 2 + Nat.fib (2 * r - 1) - 1)) - √5 / 2 := by
  let F : ℝ := Nat.fib (2 * r)
  let G : ℝ := Nat.fib (2 * r - 1)
  let A : ℝ := F / 2 + G - 1
  let B : ℝ := F / 2
  have hp : φ ^ (2 * r) = A + 1 + B * √5 := by
    rw [Q361 r hr]
    dsimp [A, B, F, G]
    ring
  have hc : ψ ^ (2 * r) = A + 1 - B * √5 := by
    rw [Q368 r hr]
    dsimp [A, B, F, G]
    ring
  have hprod : φ ^ (2 * r) * ψ ^ (2 * r) = 1 := by
    rw [← mul_pow, Real.goldenRatio_mul_goldenConj, pow_mul]
    norm_num
  rw [hp, hc] at hprod
  have hsqrt_sq : (√5) ^ 2 = (5 : ℝ) := by norm_num
  have hnorm : A ^ 2 - 5 * B ^ 2 = -2 * A := by
    nlinarith
  have hn : 0 < 2 * r := Nat.mul_pos (by norm_num) hr
  have hnprev : 0 < 2 * r - 1 := by omega
  have hFpos : 0 < F := by
    dsimp [F]
    exact_mod_cast (Nat.fib_pos.mpr hn)
  have hGone : 1 ≤ G := by
    dsimp [G]
    exact_mod_cast (show 1 ≤ Nat.fib (2 * r - 1) by
      have := Nat.fib_pos.mpr hnprev
      omega)
  have hA : 0 < A := by dsimp [A]; linarith
  have heq : φ ^ (2 * r) - 1 = A + B * √5 := by rw [hp]; ring
  have hpgt : 1 < φ ^ (2 * r) :=
    one_lt_pow₀ Real.one_lt_goldenRatio (Nat.ne_of_gt hn)
  have hden : A + B * √5 ≠ 0 := by rw [← heq]; linarith
  have hden' : A + √5 * B ≠ 0 := by
    have he : A + √5 * B = A + B * √5 := by ring
    rwa [he]
  have habstract :
      √5 / (φ ^ (2 * r) - 1) = 5 * B / (2 * A) - √5 / 2 := by
    rw [heq]
    field_simp [hden, hden', ne_of_gt hA]
    linear_combination √5 * hnorm + A * B * hsqrt_sq
  simpa [A, B, F, G] using habstract
theorem Q380 (r : ℕ) (hr : 0 < r) :
    √5 * ((φ⁻¹) ^ (2 * r) / (1 - (φ⁻¹) ^ (2 * r))) =
      √5 / (φ ^ (2 * r) - 1) := by
  let a : ℝ := φ ^ (2 * r)
  let y : ℝ := (φ⁻¹) ^ (2 * r)
  have hphi_ne : φ ≠ 0 := Real.goldenRatio_ne_zero
  have hunit : a * y = 1 := by
    dsimp [a, y]
    rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hphi_ne)]
  have hn : 0 < 2 * r := Nat.mul_pos (by norm_num) hr
  have ha1 : 1 < a := by
    dsimp [a]
    exact one_lt_pow₀ Real.one_lt_goldenRatio (Nat.ne_of_gt hn)
  have hinv0 : 0 ≤ φ⁻¹ := le_of_lt (inv_pos.mpr Real.goldenRatio_pos)
  have hinv1 : φ⁻¹ < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hy1 : y < 1 := by
    dsimp [y]
    exact pow_lt_one₀ hinv0 hinv1 (Nat.ne_of_gt hn)
  have hya : 1 - y ≠ 0 := by linarith
  have hay : a - 1 ≠ 0 := by linarith
  have hfrac : y / (1 - y) = 1 / (a - 1) := by
    field_simp [hya, hay]
    nlinarith
  rw [hfrac]
  dsimp [a, y]
  ring
theorem Q277 (r : ℕ) (hr : 0 < r) :
    HasSum (fun j : ℕ => (Nat.fib (2 * (r * 2 ^ j)) : ℝ)⁻¹)
      (√5 / (φ ^ (2 * r) - 1)) := by
  rw [← Q380 r hr]
  exact Q325 r hr
theorem Q97 (m : ℕ) (hm : 0 < m) :
    HasSum (fun j : ℕ => (Nat.fib (m * 2 ^ j) : ℝ)⁻¹)
      ((Nat.fib m : ℝ)⁻¹ + √5 / (φ ^ (2 * m) - 1)) := by
  let f : ℕ → ℝ := fun j => (Nat.fib (m * 2 ^ j) : ℝ)⁻¹
  have htail := Q277 m hm
  have htail' : HasSum (fun j : ℕ => f (j + 1)) (√5 / (φ ^ (2 * m) - 1)) := by
    apply htail.congr_fun
    intro j
    dsimp [f]
    congr 3
    rw [pow_succ]
    ring
  simpa [f] using htail'.zero_add
theorem Q181 (m : ℕ) (hm : 0 < m) :
    (Nat.fib m : ℝ)⁻¹ + √5 / (φ ^ (2 * m) - 1) =
      (Nat.fib m : ℝ)⁻¹ +
        5 * ((Nat.fib (2 * m) : ℝ) / 2) /
          (2 * ((Nat.fib (2 * m) : ℝ) / 2 + Nat.fib (2 * m - 1) - 1)) - √5 / 2 := by
  rw [Q340 m hm]
  ring
theorem Q240
    (s : Finset ℕ) (hs : s.Nonempty) (hpos : ∀ m ∈ s, 0 < m) :
    Irrational
      (∑ m ∈ s, ((Nat.fib m : ℝ)⁻¹ + √5 / (φ ^ (2 * m) - 1))) := by
  let p : ℕ → ℚ := fun m =>
    (Nat.fib m : ℚ)⁻¹ +
      5 * ((Nat.fib (2 * m) : ℚ) / 2) /
        (2 * ((Nat.fib (2 * m) : ℚ) / 2 + Nat.fib (2 * m - 1) - 1))
  let Q : ℚ := ∑ m ∈ s, p m
  let C : ℚ := (s.card : ℚ) / 2
  have hterm (m : ℕ) (hm : m ∈ s) :
      (Nat.fib m : ℝ)⁻¹ + √5 / (φ ^ (2 * m) - 1) = (p m : ℝ) - √5 / 2 := by
    simpa [p] using Q181 m (hpos m hm)
  have hsum :
      (∑ m ∈ s, ((Nat.fib m : ℝ)⁻¹ + √5 / (φ ^ (2 * m) - 1))) =
        (Q : ℝ) - (C : ℝ) * √5 := by
    calc
      _ = ∑ m ∈ s, ((p m : ℝ) - √5 / 2) := by
        apply Finset.sum_congr rfl
        intro m hm
        exact hterm m hm
      _ = (Q : ℝ) - (C : ℝ) * √5 := by
        simp [Q, C]
        ring
  have hcard : s.card ≠ 0 := Finset.card_ne_zero.mpr hs
  have hC : C ≠ 0 := by
    dsimp [C]
    exact div_ne_zero (by exact_mod_cast hcard) (by norm_num)
  have hsqrt : Irrational (√5) :=
    Nat.Prime.irrational_sqrt (show Nat.Prime 5 by norm_num)
  have hscaled : Irrational ((C : ℝ) * √5) := hsqrt.ratCast_mul hC
  have hirr : Irrational ((Q : ℝ) - (C : ℝ) * √5) := hscaled.ratCast_sub Q
  rw [hsum]
  exact hirr
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
def InGoldenPair (x y : ℝ) : Prop :=
  ∃ q : ℕ, 0 < q ∧ InScaledGoldenPair q x y
theorem InScaledGoldenPair.to_mul_denominator
    {q : ℕ} {x y : ℝ} (h : InScaledGoldenPair q x y)
    (r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    InScaledGoldenPair (q * r) x y := by
  obtain ⟨A, B, hx, hy⟩ := h
  refine ⟨(r : ℤ) * A, (r : ℤ) * B, ?_, ?_⟩
  · rw [hx]
    push_cast
    field_simp
  · rw [hy]
    push_cast
    field_simp
theorem InGoldenPair.sub {x y x' y' : ℝ}
    (h : InGoldenPair x y) (h' : InGoldenPair x' y') :
    InGoldenPair (x - x') (y - y') := by
  obtain ⟨q, hq, hxy⟩ := h
  obtain ⟨r, hr, hxy'⟩ := h'
  refine ⟨q * r, mul_pos hq hr, ?_⟩
  exact (hxy.to_mul_denominator r hq hr).sub (mul_pos hq hr)
    (by simpa [mul_comm] using hxy'.to_mul_denominator q hr hq)
theorem InGoldenPair.add {x y x' y' : ℝ}
    (h : InGoldenPair x y) (h' : InGoldenPair x' y') :
    InGoldenPair (x + x') (y + y') := by
  obtain ⟨q, hq, hxy⟩ := h
  obtain ⟨r, hr, hxy'⟩ := h'
  refine ⟨q * r, mul_pos hq hr, ?_⟩
  exact (hxy.to_mul_denominator r hq hr).add (mul_pos hq hr)
    (by simpa [mul_comm] using hxy'.to_mul_denominator q hr hq)
theorem Q384 (p : ℚ) :
    InGoldenPair (p : ℝ) (p : ℝ) := by
  refine ⟨p.den, p.den_pos, p.num, 0, ?_, ?_⟩
  · simp only [Int.cast_zero, zero_mul, add_zero]
    rw [Rat.cast_def]
  · simp only [Int.cast_zero, zero_mul, add_zero]
    rw [Rat.cast_def]
theorem Q165 (p : ℚ) :
    InGoldenPair ((√5)⁻¹ * (p : ℝ)) (-((√5)⁻¹ * (p : ℝ))) := by
  refine ⟨5 * p.den, by positivity, ?_⟩
  have h := Q345 p.num p.den p.den_pos
  simpa only [Rat.cast_def] using h
def Q129 (m : ℕ) : ℚ :=
  (Nat.fib m : ℚ)⁻¹ +
    5 * ((Nat.fib (2 * m) : ℚ) / 2) /
      (2 * ((Nat.fib (2 * m) : ℚ) / 2 + Nat.fib (2 * m - 1) - 1))
noncomputable def Q67 (m : ℕ) : ℝ :=
  -((√5)⁻¹ * (Q129 m : ℝ)) - 1 / 2
theorem Q268
    (m : ℕ) (hm : 0 < m) :
    InGoldenPair
      ((√5)⁻¹ * (∑' s : ℕ, (Nat.fib (m * 2 ^ s) : ℝ)⁻¹))
      (Q67 m) := by
  have hp := Q165
    (Q129 m)
  have hh := Q384 (-(1 : ℚ) / 2)
  have hadd := hp.add hh
  have hsum := (Q97 m hm).tsum_eq
  have hdecomp :
      (Nat.fib m : ℝ)⁻¹ + √5 / (φ ^ (2 * m) - 1) =
        (Q129 m : ℝ) - √5 / 2 := by
    simpa [Q129] using
      Q181 m hm
  rw [hsum, hdecomp]
  dsimp only [Q67]
  have hs : √(5 : ℝ) ≠ 0 := by positivity
  convert hadd using 1
  · norm_num
    field_simp
    ring
  · norm_num
    ring
theorem Q250
    (n k : ℕ → ℕ) (hpos : ∀ i, 0 < n i) (hmono : StrictMono n)
    (hinf : {i : ℕ | i ∉ Set.range k}.Infinite)
    (m : ℕ) (hm : 0 < m) (hk : StrictMono k)
    (htail : ∀ s, n (k s) = m * 2 ^ s)
    (Tconj : ℝ)
    (horig : InGoldenPair
      ((√5)⁻¹ * (∑' i : ℕ, (Nat.fib (n i) : ℝ)⁻¹)) Tconj) :
    InGoldenPair
      ((√5)⁻¹ * (∑' t : ℕ,
        (Nat.fib (Q221 n k t) : ℝ)⁻¹))
      (Tconj - Q67 m) := by
  let f : ℕ → ℝ := fun i => (Nat.fib (n i) : ℝ)⁻¹
  have hf : Summable f := by
    simpa [f] using (Q296 n hpos hmono 0).1
  have hsplit := Q342 f hf k hk hinf
  have htailTsum : (∑' s : ℕ, f (k s)) =
      ∑' s : ℕ, (Nat.fib (m * 2 ^ s) : ℝ)⁻¹ := by
    apply tsum_congr
    intro s
    simp only [f, htail s]
  have hpairTail := Q268 m hm
  have hsub := horig.sub hpairTail
  convert hsub using 1
  dsimp [Q221, f] at hsplit ⊢
  dsimp [f] at htailTsum
  rw [← htailTsum]
  linear_combination (√5)⁻¹ * hsplit
end OMAH1Research
namespace OMAH1Research
theorem Q310
    (n : ℕ → ℕ) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ i, c * (n i : ℝ) ≤ n (i + 1))
    (q : ℕ) (hq : (2 : ℝ) ≤ c ^ q)
    (M : ℕ) (hM : 0 < M) (J : Finset ℕ)
    (hJ : ∀ i ∈ J, M ≤ n i ∧ n i < 2 * M) :
    J.card ≤ q := by
  by_contra hcard
  have hqcard : q < J.card := by omega
  have hJne : J.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he] at hqcard
    simp at hqcard
  let lo := J.min' hJne
  let hi := J.max' hJne
  have hloMem : lo ∈ J := Finset.min'_mem J hJne
  have hhiMem : hi ∈ J := Finset.max'_mem J hJne
  have hsubset : J ⊆ Finset.Icc lo hi := by
    intro i hiJ
    exact Finset.mem_Icc.mpr
      ⟨Finset.min'_le J i hiJ, Finset.le_max' J i hiJ⟩
  have hcardInterval := Finset.card_le_card hsubset
  have hqspan : lo + q ≤ hi := by
    have hlohi : lo ≤ hi := Finset.min'_le J hi hhiMem
    rw [Nat.card_Icc] at hcardInterval
    omega
  have hgrowth := Q51
    n c (le_trans (by norm_num : (0 : ℝ) ≤ 1) hc.le) hratio lo q
  have hnmono : n (lo + q) ≤ n hi := hmono.monotone hqspan
  have hnmonoR : (n (lo + q) : ℝ) ≤ n hi := by exact_mod_cast hnmono
  have hloWindow := (hJ lo hloMem).1
  have hhiWindow := (hJ hi hhiMem).2
  have hloWindowR : (M : ℝ) ≤ n lo := by exact_mod_cast hloWindow
  have hhiWindowR : (n hi : ℝ) < 2 * M := by exact_mod_cast hhiWindow
  have hcq0 : 0 ≤ c ^ q := pow_nonneg (le_trans (by norm_num) hc.le) _
  have hchain : (2 : ℝ) * M ≤ c ^ q * n lo := by
    calc
      (2 : ℝ) * M ≤ c ^ q * M := by gcongr
      _ ≤ c ^ q * n lo := by gcongr
  linarith [hchain, hgrowth, hnmonoR, hhiWindowR]
end OMAH1Research
namespace OMAH1Research
theorem Q327
    (m M : ℕ) (hm : 0 < m) (hmM : m ≤ M) :
    ∃ s : ℕ, M ≤ m * 2 ^ s ∧ m * 2 ^ s < 2 * M := by
  have hex : ∃ s : ℕ, M ≤ m * 2 ^ s := by
    obtain ⟨s, hs⟩ :=
      pow_unbounded_of_one_lt M (by norm_num : (1 : ℕ) < 2)
    refine ⟨s, ?_⟩
    have hpow : 2 ^ s ≤ m * 2 ^ s := by
      simpa using Nat.mul_le_mul_right (2 ^ s) hm
    exact hs.le.trans hpow
  let s := Nat.find hex
  have hsLower : M ≤ m * 2 ^ s := Nat.find_spec hex
  refine ⟨s, hsLower, ?_⟩
  rcases hsval : Nat.find hex with _ | t
  · have hs0 : s = 0 := by simpa [s] using hsval
    simp only [hs0, pow_zero, mul_one] at hsLower ⊢
    omega
  · have hsSucc : s = t + 1 := by simpa [s] using hsval
    have htlt : t < Nat.find hex := by rw [hsval]; omega
    have hprev : ¬ M ≤ m * 2 ^ t := Nat.find_min hex htlt
    have hprev' : m * 2 ^ t < M := Nat.lt_of_not_ge hprev
    rw [hsSucc, pow_succ]
    calc
      m * (2 ^ t * 2) = 2 * (m * 2 ^ t) := by ring
      _ < 2 * M := Nat.mul_lt_mul_of_pos_left hprev' (by omega)
theorem Q211
    {ι : Type*} [Fintype ι]
    (n : ℕ → ℕ) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ i, c * (n i : ℝ) ≤ n (i + 1))
    (q : ℕ) (hq : (2 : ℝ) ≤ c ^ q)
    (m : ι → ℕ) (hm : ∀ a, 0 < m a)
    (k : ι → ℕ → ℕ)
    (htail : ∀ a s, n (k a s) = m a * 2 ^ s)
    (hdisj : Pairwise fun a b =>
      Disjoint (Set.range (k a)) (Set.range (k b))) :
    Fintype.card ι ≤ q := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
      letI := hempty
      simp
  | inr hnonempty =>
      letI := hnonempty
      let M : ℕ := ∑ a : ι, m a
      have hM : 0 < M := by
        dsimp [M]
        exact Finset.sum_pos (fun a _ => hm a) Finset.univ_nonempty
      have hroot_le : ∀ a : ι, m a ≤ M := by
        intro a
        dsimp [M]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
      have hscale : ∀ a : ι, ∃ s : ℕ,
          M ≤ m a * 2 ^ s ∧ m a * 2 ^ s < 2 * M := by
        intro a
        exact Q327 (m a) M (hm a) (hroot_le a)
      choose s hs using hscale
      let pos : ι → ℕ := fun a => k a (s a)
      have hposinj : Function.Injective pos := by
        intro a b hab
        by_contra hne
        have hd := hdisj hne
        change Disjoint (Set.range (k a)) (Set.range (k b)) at hd
        change k a (s a) = k b (s b) at hab
        have ha : k a (s a) ∈ Set.range (k a) := ⟨s a, rfl⟩
        have hb : k a (s a) ∈ Set.range (k b) := ⟨s b, hab.symm⟩
        exact (Set.disjoint_left.mp hd ha) hb
      let J : Finset ℕ := Finset.univ.image pos
      have hcardJ : J.card = Fintype.card ι := by
        dsimp [J]
        rw [Finset.card_image_iff.mpr hposinj.injOn]
        simp
      have hJ : ∀ i ∈ J, M ≤ n i ∧ n i < 2 * M := by
        intro i hi
        rw [Finset.mem_image] at hi
        obtain ⟨a, -, rfl⟩ := hi
        dsimp [pos]
        rw [htail]
        exact hs a
      have hpack := Q310
        n hmono c hc hratio q hq M hM J hJ
      omega
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
structure EmbeddedCompleteDyadicTail (n : ℕ → ℕ) where
  root : ℕ
  root_pos : 0 < root
  positions : ℕ → ℕ
  positions_strictMono : StrictMono positions
  values : ∀ s, n (positions s) = root * 2 ^ s
structure DyadicDeletionConfig (n : ℕ → ℕ) where
  remainingPositions : ℕ → ℕ
  remaining_strictMono : StrictMono remainingPositions
  tails : List (EmbeddedCompleteDyadicTail n)
  tails_pairwise : tails.Pairwise fun A B =>
    Disjoint (Set.range A.positions) (Set.range B.positions)
  remaining_avoids : ∀ t A, A ∈ tails →
    remainingPositions t ∉ Set.range A.positions
  conjugate : ℝ
  total_pair : InGoldenPair
    ((√5)⁻¹ * (∑' t : ℕ,
      (Nat.fib (n (remainingPositions t)) : ℝ)⁻¹)) conjugate
def DyadicDeletionConfig.sequence {n : ℕ → ℕ}
    (cfg : DyadicDeletionConfig n) : ℕ → ℕ :=
  fun t => n (cfg.remainingPositions t)
lemma DyadicDeletionConfig.sequence_pos
    {n : ℕ → ℕ} (cfg : DyadicDeletionConfig n)
    (hpos : ∀ i, 0 < n i) :
    ∀ t, 0 < cfg.sequence t := by
  intro t
  exact hpos _
lemma DyadicDeletionConfig.sequence_strictMono
    {n : ℕ → ℕ} (cfg : DyadicDeletionConfig n)
    (hmono : StrictMono n) :
    StrictMono cfg.sequence := by
  exact hmono.comp cfg.remaining_strictMono
lemma DyadicDeletionConfig.sequence_ratioGap
    {n : ℕ → ℕ} (cfg : DyadicDeletionConfig n)
    (hmono : StrictMono n) (c : ℝ)
    (hratio : ∀ i, c * (n i : ℝ) ≤ n (i + 1)) :
    ∀ t, c * (cfg.sequence t : ℝ) ≤ cfg.sequence (t + 1) := by
  intro t
  have he : cfg.remainingPositions t + 1 ≤
      cfg.remainingPositions (t + 1) :=
    cfg.remaining_strictMono (Nat.lt_succ_self t)
  have hnle : n (cfg.remainingPositions t + 1) ≤
      n (cfg.remainingPositions (t + 1)) := hmono.monotone he
  have hnleR : (n (cfg.remainingPositions t + 1) : ℝ) ≤
      n (cfg.remainingPositions (t + 1)) := by exact_mod_cast hnle
  exact (hratio (cfg.remainingPositions t)).trans hnleR
def Q189
    (n : ℕ → ℕ) (Tconj : ℝ)
    (htotal : InGoldenPair
      ((√5)⁻¹ * (∑' i : ℕ, (Nat.fib (n i) : ℝ)⁻¹)) Tconj) :
    DyadicDeletionConfig n where
  remainingPositions := id
  remaining_strictMono := strictMono_id
  tails := []
  tails_pairwise := by simp
  remaining_avoids := by simp
  conjugate := Tconj
  total_pair := by simpa
def DyadicDeletionConfig.Terminal {n : ℕ → ℕ}
    (cfg : DyadicDeletionConfig n) : Prop :=
  ¬ Q156 cfg.sequence ∨
    ∃ m : ℕ, 0 < m ∧ ∃ k : ℕ → ℕ, StrictMono k ∧
      (∀ s, cfg.sequence (k s) = m * 2 ^ s) ∧
      {i : ℕ | i ∉ Set.range k}.Finite
theorem DyadicDeletionConfig.tails_length_le
    {n : ℕ → ℕ} (cfg : DyadicDeletionConfig n)
    (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ i, c * (n i : ℝ) ≤ n (i + 1))
    (q : ℕ) (hq : (2 : ℝ) ≤ c ^ q) :
    cfg.tails.length ≤ q := by
  classical
  let getTail : Fin cfg.tails.length → EmbeddedCompleteDyadicTail n :=
    fun a => cfg.tails.get a
  have hdisj : Pairwise fun a b : Fin cfg.tails.length =>
      Disjoint (Set.range (getTail a).positions)
        (Set.range (getTail b).positions) := by
    intro a b hab
    rcases lt_or_gt_of_ne hab with hablt | hbalt
    · exact (List.pairwise_iff_get.mp cfg.tails_pairwise) a b hablt
    · exact ((List.pairwise_iff_get.mp cfg.tails_pairwise) b a hbalt).symm
  have hpack := Q211
    n hmono c hc hratio q hq
    (fun a => (getTail a).root)
    (fun a => (getTail a).root_pos)
    (fun a => (getTail a).positions)
    (fun a s => (getTail a).values s) hdisj
  simpa using hpack
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
def DyadicDeletionConfig.CoversOriginal
    {n : ℕ → ℕ} (cfg : DyadicDeletionConfig n) : Prop :=
  ∀ i : ℕ,
    i ∈ Set.range cfg.remainingPositions ∨
      ∃ A ∈ cfg.tails, i ∈ Set.range A.positions
lemma Q249
    (n : ℕ → ℕ) (Tconj : ℝ)
    (htotal : InGoldenPair
      ((√5)⁻¹ * (∑' i : ℕ, (Nat.fib (n i) : ℝ)⁻¹)) Tconj) :
    (Q189 n Tconj htotal).CoversOriginal := by
  intro i
  left
  exact ⟨i, rfl⟩
theorem DyadicDeletionConfig.extend_by_complete_tail
    {n : ℕ → ℕ} (cfg : DyadicDeletionConfig n)
    (hcovers : cfg.CoversOriginal)
    (hpos : ∀ i, 0 < n i) (hmono : StrictMono n)
    (m : ℕ) (hm : 0 < m) (k : ℕ → ℕ) (hk : StrictMono k)
    (htail : ∀ s, cfg.sequence (k s) = m * 2 ^ s)
    (hinf : {i : ℕ | i ∉ Set.range k}.Infinite) :
    ∃ cfg' : DyadicDeletionConfig n,
      cfg'.tails.length = cfg.tails.length + 1 ∧
      cfg'.CoversOriginal := by
  classical
  have hposCur := cfg.sequence_pos hpos
  have hmonoCur := cfg.sequence_strictMono hmono
  let newTail : EmbeddedCompleteDyadicTail n :=
    { root := m
      root_pos := hm
      positions := cfg.remainingPositions ∘ k
      positions_strictMono := cfg.remaining_strictMono.comp hk
      values := by
        intro s
        simpa [DyadicDeletionConfig.sequence, Function.comp_def] using htail s }
  let newRemaining : ℕ → ℕ :=
    cfg.remainingPositions ∘ Q38 k
  have hnewRemainingMono : StrictMono newRemaining :=
    cfg.remaining_strictMono.comp
      (Q301 k hinf)
  have hnewPair := Q250
    cfg.sequence k hposCur hmonoCur hinf m hm hk htail
      cfg.conjugate
      (by simpa [DyadicDeletionConfig.sequence] using cfg.total_pair)
  have hnewPair' : InGoldenPair
      ((√5)⁻¹ * (∑' t : ℕ,
        (Nat.fib (n (newRemaining t)) : ℝ)⁻¹))
      (cfg.conjugate - Q67 m) := by
    simpa [newRemaining, Q221,
      DyadicDeletionConfig.sequence, Function.comp_def] using hnewPair
  let cfg' : DyadicDeletionConfig n :=
    { remainingPositions := newRemaining
      remaining_strictMono := hnewRemainingMono
      tails := newTail :: cfg.tails
      tails_pairwise := by
        rw [List.pairwise_cons]
        refine ⟨?_, cfg.tails_pairwise⟩
        intro A hA
        rw [Set.disjoint_left]
        intro x hx
        rcases hx with ⟨s, rfl⟩
        exact cfg.remaining_avoids (k s) A hA
      remaining_avoids := by
        intro t A hA
        rw [List.mem_cons] at hA
        rcases hA with rfl | hA
        · intro hmem
          rcases hmem with ⟨s, hs⟩
          have heq : k s = Q38 k t :=
            cfg.remaining_strictMono.injective (by
              simpa [newTail, newRemaining, Function.comp_def] using hs)
          exact (Q281 k hinf t)
            ⟨s, heq⟩
        · exact cfg.remaining_avoids
            (Q38 k t) A hA
      conjugate := cfg.conjugate - Q67 m
      total_pair := hnewPair' }
  refine ⟨cfg', by simp [cfg'], ?_⟩
  intro i
  rcases hcovers i with hi | ⟨A, hA, hiA⟩
  · rcases hi with ⟨j, rfl⟩
    by_cases hj : j ∈ Set.range k
    · right
      refine ⟨newTail, by simp [cfg'], ?_⟩
      rcases hj with ⟨s, rfl⟩
      exact ⟨s, by simp [newTail]⟩
    · left
      have hj' : j ∈ Set.range (Q38 k) := by
        rw [Q330 k hinf]
        exact hj
      rcases hj' with ⟨t, rfl⟩
      exact ⟨t, by simp [cfg', newRemaining, Function.comp_def]⟩
  · right
    exact ⟨A, by simp [cfg', hA], hiA⟩
theorem DyadicDeletionConfig.covered_terminal_or_extend
    {n : ℕ → ℕ} (cfg : DyadicDeletionConfig n)
    (hcovers : cfg.CoversOriginal)
    (hpos : ∀ i, 0 < n i) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ i, c * (n i : ℝ) ≤ n (i + 1))
    (q : ℕ) (hqpos : 0 < q) (hq : (2 : ℝ) ≤ c ^ q) :
    cfg.Terminal ∨
      ∃ cfg' : DyadicDeletionConfig n,
        cfg'.tails.length = cfg.tails.length + 1 ∧
        cfg'.CoversOriginal := by
  classical
  by_cases hunb : Q156 cfg.sequence
  · have hposCur := cfg.sequence_pos hpos
    have hmonoCur := cfg.sequence_strictMono hmono
    have hratioCur := cfg.sequence_ratioGap hmono c hratio
    obtain ⟨qden, hqden, hpair⟩ := cfg.total_pair
    have hsum := Q54 cfg.sequence hposCur hmonoCur
    obtain ⟨m, hm, k, hk, htail⟩ :=
      Q120
        cfg.sequence hposCur hmonoCur c hc hratioCur
        qden hqden
        ((√5)⁻¹ * (∑' t : ℕ,
          (Nat.fib (cfg.sequence t) : ℝ)⁻¹)) cfg.conjugate
        hsum (by simpa [DyadicDeletionConfig.sequence] using hpair)
        q hqpos hq hunb
    by_cases hinf : {i : ℕ | i ∉ Set.range k}.Infinite
    · right
      exact cfg.extend_by_complete_tail hcovers hpos hmono
        m hm k hk htail hinf
    · left
      right
      exact ⟨m, hm, k, hk, htail, Set.not_infinite.mp hinf⟩
  · left
    exact Or.inl hunb
theorem Q219
    (n : ℕ → ℕ) (hpos : ∀ i, 0 < n i) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ i, c * (n i : ℝ) ≤ n (i + 1))
    (q : ℕ) (hqpos : 0 < q) (hq : (2 : ℝ) ≤ c ^ q)
    (Tconj : ℝ)
    (htotal : InGoldenPair
      ((√5)⁻¹ * (∑' i : ℕ, (Nat.fib (n i) : ℝ)⁻¹)) Tconj) :
    ∃ cfg : DyadicDeletionConfig n,
      cfg.Terminal ∧ cfg.CoversOriginal := by
  classical
  let init := Q189 n Tconj htotal
  have hinitCover : init.CoversOriginal := by
    exact Q249 n Tconj htotal
  by_contra hterminal
  have hnot : ∀ cfg : DyadicDeletionConfig n,
      cfg.CoversOriginal → ¬ cfg.Terminal := by
    intro cfg hcov hterm
    exact hterminal ⟨cfg, hterm, hcov⟩
  have hstep : ∀ cfg : DyadicDeletionConfig n,
      cfg.CoversOriginal →
      ∃ cfg' : DyadicDeletionConfig n,
        cfg'.tails.length = cfg.tails.length + 1 ∧
        cfg'.CoversOriginal := by
    intro cfg hcov
    rcases cfg.covered_terminal_or_extend hcov hpos hmono
      c hc hratio q hqpos hq with hterm | hext
    · exact False.elim (hnot cfg hcov hterm)
    · exact hext
  let next : DyadicDeletionConfig n → DyadicDeletionConfig n :=
    fun cfg => if hcov : cfg.CoversOriginal then
      Classical.choose (hstep cfg hcov) else cfg
  have hnext : ∀ cfg : DyadicDeletionConfig n,
      ∀ hcov : cfg.CoversOriginal,
        (next cfg).tails.length = cfg.tails.length + 1 ∧
        (next cfg).CoversOriginal := by
    intro cfg hcov
    rw [show next cfg = Classical.choose (hstep cfg hcov) by
      simp [next, hcov]]
    exact Classical.choose_spec (hstep cfg hcov)
  let cfgAt : ℕ → DyadicDeletionConfig n :=
    fun r => (next^[r]) init
  have hdata : ∀ r,
      (cfgAt r).tails.length = r ∧ (cfgAt r).CoversOriginal := by
    intro r
    induction r with
    | zero =>
        exact ⟨by simp [cfgAt, init, Q189], hinitCover⟩
    | succ r ihr =>
        have heq : cfgAt (r + 1) = next (cfgAt r) := by
          simp [cfgAt, Function.iterate_succ_apply']
        rw [heq]
        have hn := hnext (cfgAt r) ihr.2
        constructor
        · rw [hn.1, ihr.1]
        · exact hn.2
  have hbound := (cfgAt (q + 1)).tails_length_le
    hmono c hc hratio q hq
  rw [(hdata (q + 1)).1] at hbound
  omega
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
set_option maxHeartbeats 1200000 in
theorem Q230
    (n : ℕ → ℕ) (hpos : ∀ i, 0 < n i) (hmono : StrictMono n)
    (cfg : DyadicDeletionConfig n) (hcovers : cfg.CoversOriginal)
    (m : ℕ) (hm : 0 < m) (k : ℕ → ℕ) (hk : StrictMono k)
    (htail : ∀ s, cfg.sequence (k s) = m * 2 ^ s)
    (hfinite : {i : ℕ | i ∉ Set.range k}.Finite) :
    Irrational (∑' i : ℕ, (Nat.fib (n i) : ℝ)⁻¹) := by
  classical
  let C : Set ℕ := {i : ℕ | i ∉ Set.range k}
  letI : Fintype C := hfinite.fintype
  let getTail : Fin cfg.tails.length → EmbeddedCompleteDyadicTail n :=
    fun a => cfg.tails.get a
  let f : ℕ → ℝ := fun i => (Nat.fib (n i) : ℝ)⁻¹
  let X := (C ⊕ ℕ) ⊕ (Fin cfg.tails.length × ℕ)
  let positionMap : X → ℕ
    | Sum.inl (Sum.inl j) => cfg.remainingPositions j
    | Sum.inl (Sum.inr s) => cfg.remainingPositions (k s)
    | Sum.inr p => (getTail p.1).positions p.2
  have hstoredDisjoint : ∀ a b : Fin cfg.tails.length, a ≠ b →
      Disjoint (Set.range (getTail a).positions)
        (Set.range (getTail b).positions) := by
    intro a b hab
    rcases lt_or_gt_of_ne hab with hablt | hbalt
    · exact (List.pairwise_iff_get.mp cfg.tails_pairwise) a b hablt
    · exact ((List.pairwise_iff_get.mp cfg.tails_pairwise) b a hbalt).symm
  have hmapInj : Function.Injective positionMap := by
    intro x y hxy
    rcases x with xL | xS
    · rcases xL with xE | xF
      · rcases y with yL | yS
        · rcases yL with yE | yF
          · apply congrArg Sum.inl
            apply congrArg Sum.inl
            apply Subtype.ext
            exact cfg.remaining_strictMono.injective hxy
          · exfalso
            have heq : (xE : ℕ) = k yF :=
              cfg.remaining_strictMono.injective hxy
            exact xE.property ⟨yF, heq.symm⟩
        · exfalso
          exact (cfg.remaining_avoids xE (getTail yS.1)
            (List.get_mem cfg.tails yS.1)) ⟨yS.2, hxy.symm⟩
      · rcases y with yL | yS
        · rcases yL with yE | yF
          · exfalso
            have heq : k xF = (yE : ℕ) :=
              cfg.remaining_strictMono.injective hxy
            exact yE.property ⟨xF, heq⟩
          · apply congrArg Sum.inl
            apply congrArg Sum.inr
            exact hk.injective (cfg.remaining_strictMono.injective hxy)
        · exfalso
          exact (cfg.remaining_avoids (k xF) (getTail yS.1)
            (List.get_mem cfg.tails yS.1)) ⟨yS.2, hxy.symm⟩
    · rcases y with yL | yS
      · rcases yL with yE | yF
        · exfalso
          exact (cfg.remaining_avoids yE (getTail xS.1)
            (List.get_mem cfg.tails xS.1)) ⟨xS.2, hxy⟩
        · exfalso
          exact (cfg.remaining_avoids (k yF) (getTail xS.1)
            (List.get_mem cfg.tails xS.1)) ⟨xS.2, hxy⟩
      · rcases xS with ⟨a, s⟩
        rcases yS with ⟨b, t⟩
        by_cases hab : a = b
        · subst b
          have hst : s = t := (getTail a).positions_strictMono.injective hxy
          subst t
          rfl
        · exfalso
          have hd := hstoredDisjoint a b hab
          exact (Set.disjoint_left.mp hd
            (show (getTail a).positions s ∈ Set.range (getTail a).positions
              from ⟨s, rfl⟩)) ⟨t, hxy.symm⟩
  have hmapSurj : Function.Surjective positionMap := by
    intro i
    rcases hcovers i with hi | ⟨A, hA, hiA⟩
    · rcases hi with ⟨j, rfl⟩
      by_cases hj : j ∈ Set.range k
      · rcases hj with ⟨s, rfl⟩
        exact ⟨Sum.inl (Sum.inr s), rfl⟩
      · let jC : C := ⟨j, hj⟩
        exact ⟨Sum.inl (Sum.inl jC), rfl⟩
    · obtain ⟨a, ha⟩ := List.get_of_mem hA
      rcases hiA with ⟨s, hs⟩
      refine ⟨Sum.inr (a, s), ?_⟩
      change (getTail a).positions s = i
      rw [show getTail a = A by simpa [getTail] using ha]
      exact hs
  let e : X ≃ ℕ := Equiv.ofBijective positionMap ⟨hmapInj, hmapSurj⟩
  have hf : Summable f := by
    simpa [f] using (Q296 n hpos hmono 0).1
  let g : X → ℝ := fun x => f (positionMap x)
  have hg : Summable g := by
    exact hf.comp_injective hmapInj
  have hgLeft : Summable (g ∘ Sum.inl) :=
    hg.comp_injective Sum.inl_injective
  have hgStored : Summable (g ∘ Sum.inr) :=
    hg.comp_injective Sum.inr_injective
  have hgExceptional : Summable ((g ∘ Sum.inl) ∘ Sum.inl) :=
    hgLeft.comp_injective Sum.inl_injective
  have hgFinal : Summable ((g ∘ Sum.inl) ∘ Sum.inr) :=
    hgLeft.comp_injective Sum.inr_injective
  have hsplitDomain :
      (∑' x : X, g x) =
        (∑' j : C, f (cfg.remainingPositions j)) +
        (∑' s : ℕ, f (cfg.remainingPositions (k s))) +
        (∑' p : Fin cfg.tails.length × ℕ,
          f ((getTail p.1).positions p.2)) := by
    have hinner := hgExceptional.hasSum.sum hgFinal.hasSum
    have houter := hinner.sum hgStored.hasSum
    simpa [g, positionMap, Function.comp_def] using houter.tsum_eq
  have horiginal :
      (∑' i : ℕ, f i) =
        (∑' j : C, f (cfg.remainingPositions j)) +
        (∑' s : ℕ, f (cfg.remainingPositions (k s))) +
        (∑' p : Fin cfg.tails.length × ℕ,
          f ((getTail p.1).positions p.2)) := by
    rw [← hsplitDomain]
    exact (e.tsum_eq f).symm
  let orbitValue (r : ℕ) : ℝ :=
    (Nat.fib r : ℝ)⁻¹ + √5 / (φ ^ (2 * r) - 1)
  have hfinalValue :
      (∑' s : ℕ, f (cfg.remainingPositions (k s))) = orbitValue m := by
    have heq : (∑' s : ℕ, f (cfg.remainingPositions (k s))) =
        ∑' s : ℕ, (Nat.fib (m * 2 ^ s) : ℝ)⁻¹ := by
      apply tsum_congr
      intro s
      have hv := htail s
      change n (cfg.remainingPositions (k s)) = m * 2 ^ s at hv
      simp only [f, hv]
    rw [heq]
    exact (Q97 m hm).tsum_eq
  have hgStored' : Summable (fun p : Fin cfg.tails.length × ℕ =>
      f ((getTail p.1).positions p.2)) := by
    simpa [g, positionMap, Function.comp_def] using hgStored
  have hstoredValue :
      (∑' p : Fin cfg.tails.length × ℕ,
        f ((getTail p.1).positions p.2)) =
      ∑ a : Fin cfg.tails.length, orbitValue (getTail a).root := by
    rw [hgStored'.tsum_prod, tsum_fintype]
    apply Finset.sum_congr rfl
    intro a _
    have heq : (∑' s : ℕ, f ((getTail a).positions s)) =
        ∑' s : ℕ, (Nat.fib ((getTail a).root * 2 ^ s) : ℝ)⁻¹ := by
      apply tsum_congr
      intro s
      simp only [f, (getTail a).values s]
    rw [heq]
    exact (Q97
      (getTail a).root (getTail a).root_pos).tsum_eq
  let root : Option (Fin cfg.tails.length) → ℕ
    | none => m
    | some a => (getTail a).root
  have hrootPos : ∀ a, 0 < root a := by
    intro a
    cases a with
    | none => exact hm
    | some a => exact (getTail a).root_pos
  have hrootInj : Function.Injective root := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some b =>
            exfalso
            have hvFinal : n (cfg.remainingPositions (k 0)) = m := by
              simpa [DyadicDeletionConfig.sequence] using htail 0
            have hvStored : n ((getTail b).positions 0) = (getTail b).root := by
              simpa using (getTail b).values 0
            have hpEq : cfg.remainingPositions (k 0) =
                (getTail b).positions 0 := hmono.injective
              (hvFinal.trans (hab.trans hvStored.symm))
            exact (cfg.remaining_avoids (k 0) (getTail b)
              (List.get_mem cfg.tails b)) ⟨0, hpEq.symm⟩
    | some a =>
        cases b with
        | none =>
            exfalso
            have hvFinal : n (cfg.remainingPositions (k 0)) = m := by
              simpa [DyadicDeletionConfig.sequence] using htail 0
            have hvStored : n ((getTail a).positions 0) = (getTail a).root := by
              simpa using (getTail a).values 0
            have hpEq : cfg.remainingPositions (k 0) =
                (getTail a).positions 0 := hmono.injective
              (hvFinal.trans (hab.symm.trans hvStored.symm))
            exact (cfg.remaining_avoids (k 0) (getTail a)
              (List.get_mem cfg.tails a)) ⟨0, hpEq.symm⟩
        | some b =>
            apply congrArg some
            by_contra hne
            have hvA : n ((getTail a).positions 0) = (getTail a).root := by
              simpa using (getTail a).values 0
            have hvB : n ((getTail b).positions 0) = (getTail b).root := by
              simpa using (getTail b).values 0
            have hpEq : (getTail a).positions 0 =
                (getTail b).positions 0 := hmono.injective
              (hvA.trans (hab.trans hvB.symm))
            have hd := hstoredDisjoint a b hne
            exact (Set.disjoint_left.mp hd
              (show (getTail a).positions 0 ∈ Set.range (getTail a).positions
                from ⟨0, rfl⟩)) ⟨0, hpEq.symm⟩
  let roots : Finset ℕ := Finset.univ.image root
  have hrootsNonempty : roots.Nonempty := by
    exact ⟨root none, Finset.mem_image.mpr ⟨none, Finset.mem_univ _, rfl⟩⟩
  have hrootsPos : ∀ r ∈ roots, 0 < r := by
    intro r hr
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hr
    exact hrootPos a
  have hirrRoots := Q240
    roots hrootsNonempty hrootsPos
  have hrootsSum :
      (∑ r ∈ roots, orbitValue r) =
        orbitValue m +
          ∑ a : Fin cfg.tails.length, orbitValue (getTail a).root := by
    dsimp [roots]
    rw [Finset.sum_image hrootInj.injOn]
    rw [Fintype.sum_option]
  have hirrTail : Irrational
      (orbitValue m +
        ∑ a : Fin cfg.tails.length, orbitValue (getTail a).root) := by
    rw [← hrootsSum]
    exact hirrRoots
  let qexc : ℚ := ∑ j : C,
    (Nat.fib (n (cfg.remainingPositions j)) : ℚ)⁻¹
  have hqexc : (qexc : ℝ) =
      ∑' j : C, f (cfg.remainingPositions j) := by
    rw [tsum_fintype]
    simp [qexc, f]
  rw [horiginal, hfinalValue, hstoredValue]
  rw [← hqexc]
  rw [add_assoc]
  exact hirrTail.ratCast_add qexc
end OMAH1Research
namespace OMAH1Research
open Real
theorem Q197
    (n : ℕ → ℕ) (hpos : ∀ i, 0 < n i) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ i, c * (n i : ℝ) ≤ n (i + 1))
    (q : ℕ) (hqpos : 0 < q) (hq : (2 : ℝ) ≤ c ^ q)
    (r : ℚ)
    (hrat : (∑' i : ℕ, (Nat.fib (n i) : ℝ)⁻¹) = (r : ℝ)) :
    ∃ cfg : DyadicDeletionConfig n,
      cfg.CoversOriginal ∧
      (∃ V : ℕ, ∀ K : ℕ,
        Q15 (cfg.sequence K) ≤ V) ∧
      cfg.tails.length ≤ q := by
  have hpair := Q165 r
  have hpair' : InGoldenPair
      ((√5)⁻¹ * (∑' i : ℕ, (Nat.fib (n i) : ℝ)⁻¹))
      (-((√5)⁻¹ * (r : ℝ))) := by
    simpa [hrat] using hpair
  obtain ⟨cfg, hterm, hcov⟩ :=
    Q219
      n hpos hmono c hc hratio q hqpos hq
      (-((√5)⁻¹ * (r : ℝ))) hpair'
  rcases hterm with hbdd | hfinite
  · have hV : ∃ V : ℕ, ∀ K : ℕ,
        Q15 (cfg.sequence K) ≤ V := by
      simpa only [Q156, not_forall, not_exists, not_lt] using hbdd
    exact ⟨cfg, hcov, hV,
      cfg.tails_length_le hmono c hc hratio q hq⟩
  · obtain ⟨m, hm, k, hk, htail, hcomp⟩ := hfinite
    have hirr := Q230
      n hpos hmono cfg hcov m hm k hk htail hcomp
    exact False.elim (hirr.ne_rat r hrat)
end OMAH1Research
namespace OMAH1Research
theorem Q148
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hle : Q15 a ≤ Q15 b) :
    Odd (a / a.gcd b) := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  have htwo : 2 ∣ a / a.gcd b := even_iff_two_dvd.mp heven
  obtain ⟨z, hz⟩ := htwo
  have hgcdA : a.gcd b ∣ a := Nat.gcd_dvd_left _ _
  have haFactor : a.gcd b * (a / a.gcd b) = a :=
    Nat.mul_div_cancel' hgcdA
  have htwoGcd : 2 * b.gcd a ∣ a := by
    refine ⟨z, ?_⟩
    calc
      a = a.gcd b * (a / a.gcd b) := haFactor.symm
      _ = a.gcd b * (2 * z) := by rw [hz]
      _ = 2 * b.gcd a * z := by
        rw [Nat.gcd_comm b a]
        ring
  have hlt : Q15 b < Q15 a :=
    (Q104 b a hb ha).mp htwoGcd
  omega
theorem Q241
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (V : ℕ) (hV : ∀ k, Q15 (n k) ≤ V) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ < K →
      Q15 (Q11 (n K)) ≤
        Q15 (Q12 n K) := by
  let ord : ℕ → ℕ := fun k => Q15 (Q11 (n k))
  have hordBound : ∀ k, ord k ≤ V + 2 := by
    intro k
    dsimp [ord]
    rw [Q258 (n k) (hpos k)]
    have hkV := hV k
    split_ifs
    · omega
    · omega
  have hbdd : BddAbove (Set.range ord) := by
    refine ⟨V + 2, ?_⟩
    rintro x ⟨k, rfl⟩
    exact hordBound k
  have hnonempty : (Set.range ord).Nonempty := Set.range_nonempty ord
  have hmaxMem := Nat.sSup_mem hnonempty hbdd
  obtain ⟨K₀, hK₀⟩ := hmaxMem
  refine ⟨K₀, ?_⟩
  intro K hK
  have hKleMax : ord K ≤ sSup (Set.range ord) :=
    le_csSup hbdd ⟨K, rfl⟩
  have hperiodDvd : Q11 (n K₀) ∣
      Q12 n K :=
    Q71 n hK
  have hperiodPos : 0 < Q11 (n K₀) := by
    unfold Q11
    split <;> nlinarith [hpos K₀]
  have hprefixPos : 0 < Q12 n K :=
    Q82 n hpos K
  have horderDvd : Q15 (Q11 (n K₀)) ≤
      Q15 (Q12 n K) := by
    have hfac := (Nat.factorization_le_iff_dvd
      (Nat.ne_of_gt hperiodPos) (Nat.ne_of_gt hprefixPos)).mpr hperiodDvd
    exact hfac 2
  change ord K ≤ Q15 (Q12 n K)
  calc
    ord K ≤ sSup (Set.range ord) := hKleMax
    _ = ord K₀ := hK₀.symm
    _ ≤ Q15 (Q12 n K) := horderDvd
theorem Q266
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (V : ℕ) (hV : ∀ k, Q15 (n k) ≤ V) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ < K →
      Odd (Q11 (n K) /
        (Q11 (n K)).gcd (Q12 n K)) := by
  obtain ⟨K₀, hK₀⟩ :=
    Q241 n hpos V hV
  refine ⟨K₀, ?_⟩
  intro K hK
  apply Q148
  · unfold Q11
    split <;> nlinarith [hpos K]
  · exact Q82 n hpos K
  · exact hK₀ K hK
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
def Q4
    (n : ℕ → ℕ) (B : Finset ℕ) (m : ℕ) : ℤ :=
  ∑ k ∈ B, Q5 (n k) m
theorem Q112
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (B : Finset ℕ) (H a b : ℕ)
    (hBH : ∀ k ∈ B, k < H)
    (hblock : Q4 n B a =
      Q4 n B b)
    (hout : ∀ k, k ∉ B →
      Q5 (n k) a = Q5 (n k) b) :
    Q1 n a = Q1 n b := by
  let Q := max (max a b) H
  have haQ : a ≤ Q := le_trans (le_max_left _ _) (le_max_left _ _)
  have hbQ : b ≤ Q := le_trans (le_max_right _ _) (le_max_left _ _)
  have hHQ : H ≤ Q := le_max_right _ _
  have hBsub : B ⊆ Finset.range Q := by
    intro k hk
    exact Finset.mem_range.mpr ((hBH k hk).trans_le hHQ)
  rw [← Q35 n hpos hmono haQ,
    ← Q35 n hpos hmono hbQ]
  unfold Q70
  have houtsum :
      (∑ k ∈ Finset.range Q \ B, Q5 (n k) a) =
        ∑ k ∈ Finset.range Q \ B, Q5 (n k) b := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hout k (Finset.mem_sdiff.mp hk).2
  have hsplitA := Finset.sum_sdiff
    (f := fun k => Q5 (n k) a) hBsub
  have hsplitB := Finset.sum_sdiff
    (f := fun k => Q5 (n k) b) hBsub
  unfold Q4 at hblock
  omega
theorem Q238
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (B : Finset ℕ) (H a b : ℕ)
    (hBH : ∀ k ∈ B, k < H)
    (hblock : Q4 n B a ≠
      Q4 n B b)
    (hout : ∀ k, k ∉ B →
      Q5 (n k) a = Q5 (n k) b) :
    Q1 n a ≠ Q1 n b := by
  intro heq
  apply hblock
  let Q := max (max a b) H
  have haQ : a ≤ Q := le_trans (le_max_left _ _) (le_max_left _ _)
  have hbQ : b ≤ Q := le_trans (le_max_right _ _) (le_max_left _ _)
  have hHQ : H ≤ Q := le_max_right _ _
  have hBsub : B ⊆ Finset.range Q := by
    intro k hk
    exact Finset.mem_range.mpr ((hBH k hk).trans_le hHQ)
  have heq' : Q70 n Q a =
      Q70 n Q b := by
    rw [Q35 n hpos hmono haQ,
      Q35 n hpos hmono hbQ]
    exact heq
  unfold Q70 at heq'
  have houtsum :
      (∑ k ∈ Finset.range Q \ B, Q5 (n k) a) =
        ∑ k ∈ Finset.range Q \ B, Q5 (n k) b := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hout k (Finset.mem_sdiff.mp hk).2
  have hsplitA := Finset.sum_sdiff
    (f := fun k => Q5 (n k) a) hBsub
  have hsplitB := Finset.sum_sdiff
    (f := fun k => Q5 (n k) b) hBsub
  unfold Q4
  omega
def Q127
    (K H W : ℕ) (B : Finset ℕ) : Finset ((ℕ × ℕ) × Bool) :=
  (Q56 K H W).filter fun u => u.1.1 ∉ B
def Q14
    (n : ℕ → ℕ) (K H W A X p : ℕ) (B : Finset ℕ) :
    Finset ((ℕ × ℕ) × Bool) :=
  (Q127 K H W B).filter fun u =>
    (Q2 n u).gcd p ∣ Q16 A X u
theorem Q61
    (n : ℕ → ℕ) (B : Finset ℕ) (p m t : ℕ)
    (hperiod : ∀ k ∈ B, Q11 (n k) ∣ p) :
    Q4 n B (m + p * t) =
      Q4 n B m := by
  unfold Q4
  apply Finset.sum_congr rfl
  intro k hk
  obtain ⟨z, hz⟩ := hperiod k hk
  have hp := Q89 (n k) m (z * t)
  simpa [hz, mul_assoc, mul_comm, mul_left_comm] using hp
end OMAH1Research
namespace OMAH1Research
theorem Q87
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (K H W A X p R : ℕ) (B : Finset ℕ)
    (hA : 0 < A) (_hKH : K < H)
    (C O : Finset ((ℕ × ℕ) × Bool))
    (hpartition : C ∪ O =
      Q14 n K H W A X p B)
    (hbudget :
      (∑ u ∈ O, (R / (Q2 n u /
        (Q2 n u).gcd p) + 1)) <
        (Q23 C (Q16 A X)
          (Q2 n) p R).card)
    (hcut : A + p * R + X + W < n H) :
    ∃ t < R, ∀ j, K < j → j ∉ B → ∀ s < W,
      (¬ n j ∣ A + p * t + s) ∧
      (¬ n j ∣ A + p * t + s + X) := by
  classical
  let I := Q127 K H W B
  let a := Q16 A X
  let q := Q2 n
  have hq : ∀ u ∈ O, 0 < q u := by
    intro u _
    exact hpos u.1.1
  have hbudget' :
      (∑ u ∈ O, (R / (q u / (q u).gcd p) + 1)) <
        (Q23 C a q p R).card := by
    simpa [a, q] using hbudget
  obtain ⟨t, htR, hC, hO⟩ :=
    Q154 C O a q p R hq hbudget'
  have havI : ∀ u ∈ I, ¬ q u ∣ a u + p * t := by
    intro u hu
    by_cases hc : (q u).gcd p ∣ a u
    · have huComp :
          u ∈ Q14 n K H W A X p B := by
        exact Finset.mem_filter.mpr ⟨hu, hc⟩
      have huUnion : u ∈ C ∪ O := by
        rw [hpartition]
        exact huComp
      rcases Finset.mem_union.mp huUnion with huC | huO
      · exact hC u huC
      · exact hO u huO
    · intro hdvd
      exact hc (Q257 (a u) p (q u) t hdvd)
  refine ⟨t, htR, ?_⟩
  intro j hKj hjB s hsW
  by_cases hjH : j < H
  · have hjI : j ∈ Q0 K H := by
      simp [Q0, hjH, hKj]
    have hsI : s ∈ Finset.range W := Finset.mem_range.mpr hsW
    have hleft := havI ((j, s), false) (by
      simp [I, Q127, Q56,
        hjI, hsI, hjB])
    have hright := havI ((j, s), true) (by
      simp [I, Q127, Q56,
        hjI, hsI, hjB])
    dsimp [a, q, Q16, Q2] at hleft hright
    constructor
    · simpa [add_assoc, add_comm, add_left_comm] using hleft
    · simpa [add_assoc, add_comm, add_left_comm] using hright
  · have hHj : H ≤ j := by omega
    have hnHj : n H ≤ n j := hmono.monotone hHj
    have hleftPos : 0 < A + p * t + s := by omega
    have hrightPos : 0 < A + p * t + s + X := by omega
    have hpt : p * t ≤ p * R :=
      Nat.mul_le_mul_left p (Nat.le_of_lt htR)
    have hleftLt : A + p * t + s < n H := by omega
    have hrightLt : A + p * t + s + X < n H := by omega
    constructor
    · intro hdvd
      have hle := Nat.le_of_dvd hleftPos hdvd
      omega
    · intro hdvd
      have hle := Nat.le_of_dvd hrightPos hdvd
      omega
theorem Q150
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (K H L J A X p R : ℕ) (B : Finset ℕ)
    (hA : 0 < A) (hKH : K < H)
    (hKB : K ∈ B) (hBupper : ∀ k ∈ B, k < H)
    (hprefix : ∀ k < K, Q11 (n k) ∣ X)
    (hblockPeriod : ∀ k ∈ B, Q11 (n k) ∣ p)
    (htargetPre : ∀ s < L,
      Q4 n B (A + s + X) =
        Q4 n B (A + s))
    (htarget : Q4 n B (A + L + X) ≠
      Q4 n B (A + L))
    (htargetPost : ∀ s < J,
      Q4 n B (A + L + 1 + s + X) =
        Q4 n B (A + L + 1 + s))
    (C O : Finset ((ℕ × ℕ) × Bool))
    (hpartition : C ∪ O = Q14 n K H
      (L + 1 + J) A X p B)
    (hbudget :
      (∑ u ∈ O, (R / (Q2 n u /
        (Q2 n u).gcd p) + 1)) <
        (Q23 C (Q16 A X)
          (Q2 n) p R).card)
    (hcut : A + p * R + X + (L + 1 + J) < n H) :
    ∃ t < R,
      let N := A + p * t
      (∀ s < L, Q1 n (N + s + X) =
        Q1 n (N + s)) ∧
      Q1 n (N + L + X) ≠
        Q1 n (N + L) ∧
      (∀ s < J, Q1 n (N + L + 1 + s + X) =
        Q1 n (N + L + 1 + s)) := by
  obtain ⟨t, htR, hav⟩ :=
    Q87
      n hpos hmono K H (L + 1 + J) A X p R B hA hKH
        C O hpartition hbudget hcut
  let N := A + p * t
  have htransport (u : ℕ) :
      Q4 n B (N + u) =
        Q4 n B (A + u) := by
    have hp := Q61
      n B p (A + u) t hblockPeriod
    simpa [N, add_assoc, add_comm, add_left_comm] using hp
  have htransportX (u : ℕ) :
      Q4 n B (N + u + X) =
        Q4 n B (A + u + X) := by
    have hp := Q61
      n B p (A + u + X) t hblockPeriod
    simpa [N, add_assoc, add_comm, add_left_comm] using hp
  have hout (u : ℕ) (hu : u < L + 1 + J) (k : ℕ) (hkB : k ∉ B) :
      Q5 (n k) (N + u + X) =
        Q5 (n k) (N + u) := by
    by_cases hkK : k < K
    · exact Q94 n K X hprefix k hkK
    · have hKle : K ≤ k := by omega
      have hkNe : k ≠ K := fun heq => hkB (heq ▸ hKB)
      have hKk : K < k := lt_of_le_of_ne hKle (Ne.symm hkNe)
      have hz := hav k hKk hkB u hu
      rw [Q32 _ _ hz.2,
        Q32 _ _ hz.1]
  refine ⟨t, htR, ?_, ?_, ?_⟩
  · intro s hs
    apply Q112
      n hpos hmono B H _ _ hBupper
    · rw [htransportX, htransport]
      exact htargetPre s hs
    · exact hout s (by omega)
  · apply Q238
      n hpos hmono B H _ _ hBupper
    · rw [htransportX, htransport]
      exact htarget
    · exact hout L (by omega)
  · intro s hs
    let u := L + 1 + s
    have hcore : Q1 n (N + u + X) =
        Q1 n (N + u) := by
      apply Q112
        n hpos hmono B H _ _ hBupper
      · have hx := htransportX u
        have hb := htransport u
        calc
          Q4 n B (N + u + X) =
              Q4 n B (A + u + X) := hx
          _ = Q4 n B (A + u) := by
            simpa [u, add_assoc] using htargetPost s hs
          _ = Q4 n B (N + u) := hb.symm
      · exact hout u (by dsimp [u]; omega)
    simpa [N, u, add_assoc] using hcore
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
theorem Q123
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (qden : ℕ) (hqden : 0 < qden) (T Tconj : ℝ)
    (hsum : HasSum (fun m : ℕ =>
      (Q1 n m : ℝ) * (φ⁻¹) ^ m) T)
    (htotal : InScaledGoldenPair qden T Tconj)
    (K H L J A X p R : ℕ) (B : Finset ℕ)
    (hA : 0 < A) (hKH : K < H)
    (hKB : K ∈ B) (hBupper : ∀ k ∈ B, k < H)
    (hprefix : ∀ k < K, Q11 (n k) ∣ X)
    (hblockPeriod : ∀ k ∈ B, Q11 (n k) ∣ p)
    (htargetPre : ∀ s < L,
      Q4 n B (A + s + X) =
        Q4 n B (A + s))
    (htarget : Q4 n B (A + L + X) ≠
      Q4 n B (A + L))
    (htargetPost : ∀ s < J,
      Q4 n B (A + L + 1 + s + X) =
        Q4 n B (A + L + 1 + s))
    (C O : Finset ((ℕ × ℕ) × Bool))
    (hpartition : C ∪ O = Q14 n K H
      (L + 1 + J) A X p B)
    (hbudget :
      (∑ u ∈ O, (R / (Q2 n u /
        (Q2 n u).gcd p) + 1)) <
        (Q23 C (Q16 A X)
          (Q2 n) p R).card)
    (hcut : A + p * R + X + (L + 1 + J) < n H)
    (hsmallPost : ∀ t < R,
      let N := A + p * t
      (φ⁻¹) ^ (J + 1) *
        (Q7 n (N + L + 1 + J) +
          Q7 n (N + X + L + 1 + J)) < 1)
    (hsmallPre : ∀ t < R,
      let N := A + p * t
      (φ⁻¹) ^ L *
          (Q7 n (N + L) +
            Q7 n (N + X + L)) *
        (Q6 n Tconj N +
          Q6 n Tconj (N + X)) <
      (((qden : ℕ) : ℝ)⁻¹) ^ 2) :
    False := by
  obtain ⟨t, htR, hpat⟩ :=
    Q150
      n hpos hmono K H L J A X p R B hA hKH hKB hBupper
        hprefix hblockPeriod htargetPre htarget htargetPost
        C O hpartition hbudget hcut
  let N := A + p * t
  apply Q108
    n hpos hmono qden hqden T Tconj hsum htotal N (N + X) L J
  · intro s hs
    simpa [N, add_assoc, add_comm, add_left_comm] using (hpat.1 s hs).symm
  · simpa [N, add_assoc, add_comm, add_left_comm] using ne_comm.mp hpat.2.1
  · intro s hs
    simpa [N, add_assoc, add_comm, add_left_comm] using (hpat.2.2 s hs).symm
  · simpa [N, add_assoc, add_comm, add_left_comm] using hsmallPost t htR
  · simpa [N, add_assoc, add_comm, add_left_comm] using hsmallPre t htR
theorem Q146
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (qden : ℕ) (Tconj : ℝ)
    (H L J A X p R : ℕ) (hp : 0 < p)
    (hcut : A + p * R + X + (L + 1 + J) < n H)
    (hpostCap :
      (φ⁻¹) ^ (J + 1) * (2 * Q8 H) < 1)
    (hpreCap :
      (φ⁻¹) ^ L * (2 * Q8 H) *
        (2 * Q10 Tconj H) <
        (((qden : ℕ) : ℝ)⁻¹) ^ 2) :
    (∀ t < R,
      let N := A + p * t
      (φ⁻¹) ^ (J + 1) *
        (Q7 n (N + L + 1 + J) +
          Q7 n (N + X + L + 1 + J)) < 1) ∧
    (∀ t < R,
      let N := A + p * t
      (φ⁻¹) ^ L *
          (Q7 n (N + L) +
            Q7 n (N + X + L)) *
        (Q6 n Tconj N +
          Q6 n Tconj (N + X)) <
      (((qden : ℕ) : ℝ)⁻¹) ^ 2) := by
  have htailCapNonneg := Q34 H
  have hconjCapNonneg := Q36 Tconj H
  constructor
  · intro t ht
    let N := A + p * t
    have hpt : p * t < p * R := (Nat.mul_lt_mul_left hp).mpr ht
    have hx₁ : N + L + 1 + J < n H := by dsimp [N]; omega
    have hx₂ : N + X + L + 1 + J < n H := by dsimp [N]; omega
    have hb₁ := Q27 n hpos hmono hx₁
    have hb₂ := Q27 n hpos hmono hx₂
    calc
      (φ⁻¹) ^ (J + 1) *
          (Q7 n (N + L + 1 + J) +
            Q7 n (N + X + L + 1 + J)) ≤
        (φ⁻¹) ^ (J + 1) * (2 * Q8 H) := by
          gcongr
          linarith
      _ < 1 := hpostCap
  · intro t ht
    let N := A + p * t
    have hpt : p * t < p * R := (Nat.mul_lt_mul_left hp).mpr ht
    have hxN : N < n H := by dsimp [N]; omega
    have hxNX : N + X < n H := by dsimp [N]; omega
    have hxL : N + L < n H := by dsimp [N]; omega
    have hxXL : N + X + L < n H := by dsimp [N]; omega
    have ht₁ := Q27 n hpos hmono hxL
    have ht₂ := Q27 n hpos hmono hxXL
    have hc₁ := Q39
      n hpos hmono Tconj hxN
    have hc₂ := Q39
      n hpos hmono Tconj hxNX
    have htailSum :
        Q7 n (N + L) +
          Q7 n (N + X + L) ≤ 2 * Q8 H := by
      linarith
    have hconjSum :
        Q6 n Tconj N +
          Q6 n Tconj (N + X) ≤
        2 * Q10 Tconj H := by
      linarith
    have hconjSumNonneg : 0 ≤
        Q6 n Tconj N +
          Q6 n Tconj (N + X) := by
      unfold Q6
      have hden : 0 < 1 - φ⁻¹ := sub_pos.mpr
        (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)
      positivity
    have hfirstNonneg : 0 ≤
        (φ⁻¹) ^ L * (2 * Q8 H) := by positivity
    calc
      (φ⁻¹) ^ L *
          (Q7 n (N + L) +
            Q7 n (N + X + L)) *
        (Q6 n Tconj N +
          Q6 n Tconj (N + X)) ≤
        (φ⁻¹) ^ L * (2 * Q8 H) *
          (Q6 n Tconj N +
            Q6 n Tconj (N + X)) := by
          gcongr
      _ ≤ (φ⁻¹) ^ L * (2 * Q8 H) *
          (2 * Q10 Tconj H) :=
        mul_le_mul_of_nonneg_left hconjSum hfirstNonneg
      _ < (((qden : ℕ) : ℝ)⁻¹) ^ 2 := hpreCap
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
def Q30
    (n : ℕ → ℕ) (K H W A X p L sR : ℕ) (B : Finset ℕ) :
    Finset ((ℕ × ℕ) × Bool) :=
  (Q28 n K H W A X p L sR).filter fun u =>
    u.1.1 ∉ B
def Q24
    (n : ℕ → ℕ) (K H W A X p L sR : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (Q30 n K H W A X p L sR B).image fun u =>
    Q2 n u / (Q2 n u).gcd p
theorem Q99
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (K H L J X r v : ℕ) (B : Finset ℕ) (_hKH : K < H)
    (hL : L < n K)
    (hX : X = r + (2 * n K) * v) (hv : Even v)
    (hrUpper : r ≤ n K + L)
    (_hsRWindow : n K + L - r < L + 1 + J)
    (hnoDoubleOutside : ∀ j, K < j → j < H → j ∉ B →
      n j ≠ 2 * n K) :
    let A := n K - L
    let W := L + 1 + J
    let p := 4 * n K
    let sR := n K + L - r
    let C := Q30
      n K H W A X p L sR B
    let Q := Q24
      n K H W A X p L sR B
    let S := Q20 Q
    ∃ M : ℕ, 0 < M ∧ M = ∏ z ∈ S, z ∧ ∀ T : ℕ,
      2 * (T * M) ≤ (S.card + 1) * (S.card + 2) *
        (Q23 C (Q16 A X)
          (Q2 n) p (T * M)).card := by
  classical
  let A := n K - L
  let W := L + 1 + J
  let p := 4 * n K
  let sR := n K + L - r
  let C := Q30
    n K H W A X p L sR B
  let Q := Q24
    n K H W A X p L sR B
  have hn := hpos K
  have hcenterLeft : A + L = n K := by dsimp [A]; omega
  have hvOdd : Odd (v + 1) := by
    obtain ⟨z, hz⟩ := hv
    exact ⟨z, by omega⟩
  have hcenterRight : A + sR + X = 2 * n K * (v + 1) := by
    have hsrr : sR + r = n K + L := by dsimp [sR]; omega
    rw [hX]
    calc
      A + sR + (r + 2 * n K * v) =
          2 * n K + 2 * n K * v := by
        dsimp [A]
        omega
      _ = 2 * n K * (v + 1) := by ring
  have hQdata : ∀ q ∈ Q, Odd q ∧ 3 ≤ q := by
    intro q hqQ
    obtain ⟨u, huC, rfl⟩ := Finset.mem_image.mp hqQ
    have huOldC := (Finset.mem_filter.mp huC).1
    have huNotB := (Finset.mem_filter.mp huC).2
    have huCompat := (Finset.mem_filter.mp huOldC).1
    have huCenter := (Finset.mem_filter.mp huOldC).2
    have huBase := (Finset.mem_filter.mp huCompat).1
    have huComp := (Finset.mem_filter.mp huCompat).2
    have huPair := Finset.mem_product.mp (Finset.mem_product.mp huBase).1
    have hjData := Finset.mem_filter.mp huPair.1
    have hjH := Finset.mem_range.mp hjData.1
    have hKj := hjData.2
    have hnj := hpos u.1.1
    have hnlt : n K < n u.1.1 := hmono hKj
    rcases huCenter with hleft | hright
    · have hside : u.2 = false := hleft.1
      have hoff : u.1.2 = L := hleft.2
      have hcompLeft : (n u.1.1).gcd (4 * n K) ∣ n K := by
        simpa [Q2, Q16, p, A,
          hside, hoff, hcenterLeft] using huComp
      exact Q218
        (n u.1.1) (n K) hnj hn hnlt hcompLeft
    · have hside : u.2 = true := hright.1
      have hoff : u.1.2 = sR := hright.2
      have hcompRight : (n u.1.1).gcd (4 * n K) ∣
          2 * n K * (v + 1) := by
        simpa [Q2, Q16, p, A,
          sR, hside, hoff, hcenterRight] using huComp
      have hd := Q178
        (n u.1.1) (n K) (v + 1) hnj hn hnlt hvOdd hcompRight
      refine ⟨hd.1, ?_⟩
      have hqpos : 0 < n u.1.1 / (n u.1.1).gcd (4 * n K) := hd.1.pos
      have hqne : n u.1.1 / (n u.1.1).gcd (4 * n K) ≠ 1 := by
        intro heq
        have heqDouble := hd.2 heq
        exact hnoDoubleOutside u.1.1 hKj hjH huNotB heqDouble
      have hqneTwo : n u.1.1 / (n u.1.1).gcd (4 * n K) ≠ 2 := by
        intro heq
        obtain ⟨z, hz⟩ := hd.1
        omega
      change 3 ≤ n u.1.1 / (n u.1.1).gcd (4 * n K)
      omega
  apply Q62
    Q C (fun u => u.2) (Q16 A X) (Q2 n)
      p v
  · exact fun q hq => (hQdata q hq).2
  · exact fun q hq => (hQdata q hq).1
  · intro u huC
    have huOldC := (Finset.mem_filter.mp huC).1
    let q0 := Q2 n u /
      (Q2 n u).gcd p
    refine ⟨q0, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨u, huC, rfl⟩
    · intro t hbad
      have huCompat := (Finset.mem_filter.mp huOldC).1
      have huCenter := (Finset.mem_filter.mp huOldC).2
      have huComp := (Finset.mem_filter.mp huCompat).2
      let g := (n u.1.1).gcd (4 * n K)
      have hg : 0 < g := Nat.gcd_pos_of_pos_left (4 * n K) (hpos u.1.1)
      have hqFactor : n u.1.1 = g * q0 := by
        dsimp [g, q0, p]
        exact (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
      rcases huCenter with hleft | hright
      · have hside : u.2 = false := hleft.1
        have hoff : u.1.2 = L := hleft.2
        have hgN : g ∣ n K := by
          simpa [g, p, Q2, Q16,
            A, hside, hoff, hcenterLeft] using huComp
        let u0 := n K / g
        have hnFactor : n K = g * u0 := by
          dsimp [u0]
          exact (Nat.mul_div_cancel' hgN).symm
        have hcop : q0.Coprime u0 := by
          dsimp [q0, u0, g, p]
          exact Q65
            (n u.1.1) (4 * n K) (n K) (hpos u.1.1)
              hgN (by exact ⟨4, by ring⟩)
        simp only [hside, Bool.false_eq_true, ↓reduceIte]
        apply (Q167
          (n u.1.1) (n K) g q0 u0 t hg hqFactor hnFactor hcop).mp
        simpa [Q2, Q16, p, A,
          hside, hoff, hcenterLeft] using hbad
      · have hside : u.2 = true := hright.1
        have hoff : u.1.2 = sR := hright.2
        have hgAligned : g ∣ 2 * n K * (v + 1) := by
          simpa [g, p, Q2, Q16,
            A, sR, hside, hoff, hcenterRight] using huComp
        have hgTwo : g ∣ 2 * n K :=
          Q80
            g (n K) (v + 1) hvOdd
            (by dsimp [g]; exact Nat.gcd_dvd_right _ _) hgAligned
        let u0 := (2 * n K) / g
        have htwoFactor : 2 * n K = g * u0 := by
          dsimp [u0]
          exact (Nat.mul_div_cancel' hgTwo).symm
        have hcop : q0.Coprime u0 := by
          dsimp [q0, u0, g, p]
          exact Q65
            (n u.1.1) (4 * n K) (2 * n K) (hpos u.1.1)
              hgTwo (by exact ⟨2, by ring⟩)
        simp only [hside, ite_true]
        apply (Q162
          (n u.1.1) g q0 u0 v t hg hqFactor hcop).mp
        have haligned : A + u.1.2 + X + p * t =
            g * u0 * (v + 1 + 2 * t) := by
          rw [hoff, hcenterRight, ← htwoFactor]
          dsimp [p]
          ring
        simpa [Q2, Q16, hside, haligned]
          using hbad
end OMAH1Research
namespace OMAH1Research
theorem Q187
    (P n : ℕ) (hn : 0 < n)
    (hnew : ¬Q11 n ∣ P)
    (hodd : Odd (Q11 n /
      (Q11 n).gcd P)) :
    ¬2 * n ∣ P := by
  intro htwoP
  by_cases he : Even n
  · apply hnew
    simpa [Q11, he] using htwoP
  · let d := Q11 n
    let g := d.gcd P
    let Q := d / g
    have hd : d = 4 * n := by simp [d, Q11, he]
    have hdpos : 0 < d := by rw [hd]; omega
    have hgpos : 0 < g := by
      dsimp [g]
      exact Nat.gcd_pos_of_pos_left P hdpos
    have hgd : g ∣ d := by
      dsimp [g]
      exact Nat.gcd_dvd_left _ _
    have hgP : g ∣ P := by
      dsimp [g]
      exact Nat.gcd_dvd_right _ _
    have htwoD : 2 * n ∣ d := by rw [hd]; exact ⟨2, by ring⟩
    have htwoG : 2 * n ∣ g := by
      dsimp [g]
      exact Nat.dvd_gcd htwoD htwoP
    have hfac : g * Q = d := by
      dsimp [Q]
      exact Nat.mul_div_cancel' hgd
    have hoddQ : Odd Q := by simpa [Q, d, g] using hodd
    obtain ⟨a, ha⟩ := hoddQ
    have hQone : Q = 1 := by
      by_contra hne
      have hQthree : 3 ≤ Q := by omega
      have hlarge : 3 * (2 * n) ≤ g * Q := by
        calc
          3 * (2 * n) ≤ 3 * g := Nat.mul_le_mul_left 3
            (Nat.le_of_dvd hgpos htwoG)
          _ ≤ g * Q := by nlinarith
      rw [hfac, hd] at hlarge
      omega
    have hgdEq : g = d := by
      rw [hQone, mul_one] at hfac
      exact hfac
    apply hnew
    change d ∣ P
    rw [← hgdEq]
    exact hgP
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
open scoped BigOperators
theorem Q183
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (N M B J : ℕ) (η : ℝ)
    (hblockLower : η ≤
      |∑ t ∈ Finset.range B,
        ((Q1 n (N + t) -
          Q1 n (M + t) : ℤ) : ℝ) * (φ⁻¹) ^ t|)
    (hpost : ∀ t < J,
      Q1 n (N + B + t) =
        Q1 n (M + B + t))
    (hsmallPost :
      (φ⁻¹) ^ (B + J) *
        (Q7 n (N + B + J) +
          Q7 n (M + B + J)) < η) :
    Q17 (Q1 n) N ≠
      Q17 (Q1 n) M := by
  let C := Q1 n
  let r : ℝ := φ⁻¹
  let D : ℝ := ∑ t ∈ Finset.range B,
    ((C (N + t) - C (M + t) : ℤ) : ℝ) * r ^ t
  have hsum := (Q54 n hpos hmono).summable
  have hsplitN := Q72 C hsum N B
  have hsplitM := Q72 C hsum M B
  have hpostFactor := Q47
    C hsum (N + B) (M + B) J hpost
  have hformula :
      Q17 C N - Q17 C M =
        D + r ^ (B + J) *
          (Q17 C (N + B + J) -
            Q17 C (M + B + J)) := by
    rw [hsplitN, hsplitM]
    calc
      (∑ t ∈ Finset.range B, (C (N + t) : ℝ) * φ⁻¹ ^ t) +
            φ⁻¹ ^ B * Q17 C (N + B) -
          ((∑ t ∈ Finset.range B, (C (M + t) : ℝ) * φ⁻¹ ^ t) +
            φ⁻¹ ^ B * Q17 C (M + B)) =
          ((∑ t ∈ Finset.range B, (C (N + t) : ℝ) * φ⁻¹ ^ t) -
            ∑ t ∈ Finset.range B, (C (M + t) : ℝ) * φ⁻¹ ^ t) +
            φ⁻¹ ^ B * (Q17 C (N + B) -
              Q17 C (M + B)) := by ring
      _ = D + φ⁻¹ ^ B * (Q17 C (N + B) -
              Q17 C (M + B)) := by
        apply congrArg₂ (· + ·)
        · dsimp [D, r]
          push_cast
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro t ht
          ring
        · rfl
      _ = D + r ^ (B + J) *
          (Q17 C (N + B + J) -
            Q17 C (M + B + J)) := by
        rw [hpostFactor, pow_add]
        dsimp [r]
        ring
  have hlater :
      |Q17 C (N + B + J) -
        Q17 C (M + B + J)| ≤
        Q7 n (N + B + J) +
          Q7 n (M + B + J) := by
    exact (abs_sub _ _).trans <| add_le_add
      (Q42 n hpos hmono (N + B + J))
      (Q42 n hpos hmono (M + B + J))
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact inv_nonneg.mpr Real.goldenRatio_pos.le
  have hrem :
      |r ^ (B + J) *
        (Q17 C (N + B + J) -
          Q17 C (M + B + J))| < η := by
    rw [abs_mul, abs_pow, abs_of_nonneg hr0]
    exact (mul_le_mul_of_nonneg_left hlater (pow_nonneg hr0 _)).trans_lt
      (by simpa [r] using hsmallPost)
  intro heq
  have hzero : Q17 C N - Q17 C M = 0 :=
    sub_eq_zero.mpr heq
  rw [hzero] at hformula
  have habsEq : |D| =
      |r ^ (B + J) *
        (Q17 C (N + B + J) -
          Q17 C (M + B + J))| := by
    rw [← abs_neg]
    congr 1
    linarith
  have hlower : η ≤ |D| := by
    simpa [D, r, C] using hblockLower
  rw [habsEq] at hlower
  exact (not_lt_of_ge hlower) hrem
theorem Q225
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (q : ℕ) (hq : 0 < q) (T Tconj : ℝ)
    (hsum : HasSum (fun m : ℕ =>
      (Q1 n m : ℝ) * (φ⁻¹) ^ m) T)
    (htotal : InScaledGoldenPair q T Tconj)
    (N M L B J : ℕ) (η : ℝ)
    (hpre : ∀ t < L,
      Q1 n (N + t) =
        Q1 n (M + t))
    (hblockLower : η ≤
      |∑ t ∈ Finset.range B,
        ((Q1 n (N + L + t) -
          Q1 n (M + L + t) : ℤ) : ℝ) * (φ⁻¹) ^ t|)
    (hpost : ∀ t < J,
      Q1 n (N + L + B + t) =
        Q1 n (M + L + B + t))
    (hsmallPost :
      (φ⁻¹) ^ (B + J) *
        (Q7 n (N + L + B + J) +
          Q7 n (M + L + B + J)) < η)
    (hsmallPre :
      (φ⁻¹) ^ L *
          (Q7 n (N + L) +
            Q7 n (M + L)) *
        (Q6 n Tconj N +
          Q6 n Tconj M) <
      (((q : ℕ) : ℝ)⁻¹) ^ 2) :
    False := by
  apply Q142
    n hpos hmono q hq T Tconj hsum htotal N M L hpre
  · have hne := Q183
      n hpos hmono (N + L) (M + L) B J η hblockLower
        (by
          intro t ht
          simpa [add_assoc] using hpost t ht)
        (by simpa [add_assoc] using hsmallPost)
    have hsummable := (Q54 n hpos hmono).summable
    have hfactor := Q47
      (Q1 n) hsummable N M L hpre
    intro heq
    have hz : Q17 (Q1 n) N -
        Q17 (Q1 n) M = 0 :=
      sub_eq_zero.mpr heq
    rw [hz] at hfactor
    have hpne : (φ⁻¹ : ℝ) ^ L ≠ 0 :=
      pow_ne_zero _ (inv_ne_zero Real.goldenRatio_ne_zero)
    exact hne (sub_eq_zero.mp
      (mul_eq_zero.mp hfactor.symm |>.resolve_left hpne))
  · exact hsmallPre
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
open scoped BigOperators
lemma Q166
    (n x : ℕ) (hx : 0 < x) (hxlt : x < 2 * n)
    (hxne : x ≠ n) :
    ¬n ∣ x := by
  rw [Nat.dvd_iff_mod_eq_zero]
  rcases lt_or_gt_of_ne hxne with hxn | hnx
  · rw [Nat.mod_eq_of_lt hxn]
    omega
  · rw [Nat.mod_eq_sub_mod hnx.le, Nat.mod_eq_of_lt (by omega)]
    omega
theorem Q287
    (n R z : ℕ) (hn : 0 < n) (hR : 2 ≤ R) :
    Q26 n R (2 * n + 4 * n * z) = 1 := by
  unfold Q26
  rw [Finset.sum_eq_single 1]
  · have heven : Even (2 * n) := ⟨n, by omega⟩
    have hp := Q89
      (2 * n) (2 * n) z
    have hself := Q308 (2 * n) (by omega)
    rw [hself] at hp
    simpa [Q11, heven, pow_one, mul_assoc, mul_comm,
      mul_left_comm] using hp
  · intro j hj hjne
    have hjR : j < R := Finset.mem_range.mp hj
    by_cases hj0 : j = 0
    · subst j
      simp only [pow_zero, mul_one]
      apply Q43 n _ hn
      have hdvd : 2 * n ∣ 2 * n + 4 * n * z := by
        refine ⟨1 + 2 * z, ?_⟩
        ring
      rw [Nat.mod_eq_zero_of_dvd hdvd]
      omega
    · have hjtwo : 2 ≤ j := by omega
      apply Q32
      intro hdvd
      have hfactor : 2 * n + 4 * n * z = n * (2 * (1 + 2 * z)) := by
        ring
      have hpowDvd : 2 ^ j ∣ 2 * (1 + 2 * z) := by
        apply (Nat.mul_dvd_mul_iff_left hn).mp
        simpa [hfactor] using hdvd
      have hpowEq : 2 ^ j = 2 * 2 ^ (j - 1) := by
        obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
        simp [pow_succ, mul_comm]
      have hrest : 2 ^ (j - 1) ∣ 1 + 2 * z := by
        apply (Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)).mp
        simpa [hpowEq] using hpowDvd
      have htwoPow : 2 ∣ 2 ^ (j - 1) := by
        simpa using Nat.pow_dvd_pow 2 (show 1 ≤ j - 1 by omega)
      have htwoOdd : 2 ∣ 1 + 2 * z := htwoPow.trans hrest
      obtain ⟨a, ha⟩ := htwoOdd
      omega
  · intro hnot
    exfalso
    apply hnot
    simp
    omega
theorem Q318
    (n R W t : ℕ) (hn : 0 < n) (hR : 0 < R)
    (hW : W < n) (ht : t < 2 * W + 1) :
    Q26 n R (n - W + t) = if t = W then 1 else 0 := by
  by_cases htw : t = W
  · subst t
    rw [show n - W + W = n by omega,
      Q381 n R hn hR]
    simp
  · have hxpos : 0 < n - W + t := by omega
    have hxlt : n - W + t < 2 * n := by omega
    have hxne : n - W + t ≠ n := by omega
    rw [Q81 n R _
      (Q166 n _ hxpos hxlt hxne)]
    simp [htw]
theorem Q169
    (n R W X r v e t : ℕ) (hn : 0 < n) (hR : 2 ≤ R)
    (hW : W < n) (hX : X = r + (2 * n) * v) (hv : Even v)
    (hWr : W < r) (hrW : r + W < 2 * n)
    (he : r - W + e = n)
    (ht : t < 2 * W + 1) :
    Q26 n R (n - W + t + X) =
      if t = e then 1 else 0 := by
  obtain ⟨z, hz⟩ := hv
  have hterm : (2 * n) * v = 4 * n * z := by rw [hz]; ring
  have hdecomp (u : ℕ) :
      n - W + u + X = (n + 4 * n * z) + (r - W + u) := by
    rw [hX, hterm]
    omega
  by_cases hte : t = e
  · subst t
    have hvalue : n - W + e + X = 2 * n + 4 * n * z := by
      rw [hdecomp, he]
      ring
    rw [hvalue, Q287 n R z hn hR]
    simp
  · have hztpos : 0 < r - W + t := by omega
    have hztlt : r - W + t < 2 * n := by omega
    have hztne : r - W + t ≠ n := by
      intro heq
      have : t = e := by omega
      exact hte this
    have hnot : ¬n ∣ n - W + t + X := by
      rw [hdecomp]
      have hknown : n ∣ n + 4 * n * z := by
        refine ⟨1 + 4 * z, ?_⟩
        ring
      intro hdvd
      exact (Q166 n _ hztpos hztlt hztne)
        ((Nat.dvd_add_iff_right hknown).mpr hdvd)
    rw [Q81 n R _ hnot]
    simp [hte]
private theorem Q328
    (D : ℕ) (hD : 0 < D) :
    (∑ t ∈ Finset.range (D + 1),
      (if t = 0 then (-1 : ℝ) else if t = D then 1 else 0) *
        (φ⁻¹) ^ t) = -(1 - (φ⁻¹) ^ D) := by
  let f₀ : ℕ → ℝ := fun t => if t = 0 then -(φ⁻¹) ^ t else 0
  let fD : ℕ → ℝ := fun t => if t = D then (φ⁻¹) ^ t else 0
  have hD0 : D ≠ 0 := Nat.ne_of_gt hD
  have h0D : (0 : ℕ) ≠ D := Ne.symm hD0
  have hsplit :
      (∑ t ∈ Finset.range (D + 1),
        (if t = 0 then (-1 : ℝ) else if t = D then 1 else 0) *
          (φ⁻¹) ^ t) =
      (∑ t ∈ Finset.range (D + 1), f₀ t) +
        ∑ t ∈ Finset.range (D + 1), fD t := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      simp [f₀, fD, h0D]
    · by_cases htD : t = D
      · subst t
        simp [f₀, fD, hD0]
      · simp [f₀, fD, ht0, htD]
  have hs0 : (∑ t ∈ Finset.range (D + 1), f₀ t) = -(φ⁻¹) ^ 0 := by
    calc
      (∑ t ∈ Finset.range (D + 1), f₀ t) = f₀ 0 := by
        apply Finset.sum_eq_single 0
        · intro b hb hb0
          simp [f₀, hb0]
        · simp [f₀]
      _ = -(φ⁻¹) ^ 0 := by simp [f₀]
  have hsD : (∑ t ∈ Finset.range (D + 1), fD t) = (φ⁻¹) ^ D := by
    calc
      (∑ t ∈ Finset.range (D + 1), fD t) = fD D := by
        apply Finset.sum_eq_single D
        · intro b hb hbD
          simp [fD, hbD]
        · intro hnot
          exfalso
          apply hnot
          simp
      _ = (φ⁻¹) ^ D := by simp [fD]
  rw [hsplit, hs0, hsD]
  simp
  ring
private theorem Q382
    (D : ℕ) (hD : 0 < D) :
    (∑ t ∈ Finset.range (D + 1),
      (if t = 0 then (1 : ℝ) else if t = D then -1 else 0) *
        (φ⁻¹) ^ t) = 1 - (φ⁻¹) ^ D := by
  have hneg := Q328 D hD
  have hD0 : D ≠ 0 := Nat.ne_of_gt hD
  calc
    (∑ t ∈ Finset.range (D + 1),
      (if t = 0 then (1 : ℝ) else if t = D then -1 else 0) *
        (φ⁻¹) ^ t) =
      -∑ t ∈ Finset.range (D + 1),
        (if t = 0 then (-1 : ℝ) else if t = D then 1 else 0) *
          (φ⁻¹) ^ t := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro t ht
            by_cases ht0 : t = 0
            · subst t
              simp
            · by_cases htD : t = D
              · subst t
                simp [hD0]
              · simp [ht0, htD]
    _ = 1 - (φ⁻¹) ^ D := by rw [hneg]; ring
theorem Q194
    (D : ℕ) (hD : 0 < D) (positiveFirst : Bool) :
    1 - φ⁻¹ ≤
      |∑ t ∈ Finset.range (D + 1),
        (if positiveFirst then
          (if t = 0 then (1 : ℝ) else if t = D then -1 else 0)
        else
          (if t = 0 then (-1 : ℝ) else if t = D then 1 else 0)) *
          (φ⁻¹) ^ t| := by
  have hr0 : 0 ≤ (φ⁻¹ : ℝ) := inv_nonneg.mpr Real.goldenRatio_pos.le
  have hrle : (φ⁻¹ : ℝ) ≤ 1 :=
    (inv_le_one₀ Real.goldenRatio_pos).mpr Real.one_lt_goldenRatio.le
  have hpow : (φ⁻¹ : ℝ) ^ D ≤ φ⁻¹ := by
    simpa using pow_le_pow_of_le_one hr0 hrle (show 1 ≤ D by omega)
  have hpowOne : (φ⁻¹ : ℝ) ^ D ≤ 1 := hpow.trans hrle
  cases positiveFirst
  · change 1 - φ⁻¹ ≤
      |∑ t ∈ Finset.range (D + 1),
        (if t = 0 then (-1 : ℝ) else if t = D then 1 else 0) *
          (φ⁻¹) ^ t|
    rw [Q328 D hD, abs_neg,
      abs_of_nonneg (sub_nonneg.mpr hpowOne)]
    linarith
  · change 1 - φ⁻¹ ≤
      |∑ t ∈ Finset.range (D + 1),
        (if t = 0 then (1 : ℝ) else if t = D then -1 else 0) *
          (φ⁻¹) ^ t|
    rw [Q382 D hD,
      abs_of_nonneg (sub_nonneg.mpr hpowOne)]
    linarith
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
open scoped BigOperators
theorem Q151
    (n R W X r v : ℕ) (hn : 0 < n) (hR : 2 ≤ R)
    (hWn : W < n) (hX : X = r + (2 * n) * v) (hv : Even v)
    (hWr : W < r) (hrW : r + W < 2 * n)
    (hrne : r ≠ n) (hclose : r.dist n < W) :
    ∃ L B J : ℕ,
      L + B + J = 2 * W + 1 ∧
      B = r.dist n + 1 ∧
      W - r.dist n ≤ L ∧ W - r.dist n ≤ J ∧
      (∀ t < L,
        Q26 n R (n - W + t + X) =
          Q26 n R (n - W + t)) ∧
      1 - φ⁻¹ ≤
        |∑ t ∈ Finset.range B,
          ((Q26 n R (n - W + L + t + X) -
            Q26 n R (n - W + L + t) : ℤ) : ℝ) *
              (φ⁻¹) ^ t| ∧
      (∀ t < J,
        Q26 n R (n - W + L + B + t + X) =
          Q26 n R (n - W + L + B + t)) := by
  let δ := r.dist n
  have hδpos : 0 < δ := Nat.dist_pos_of_ne hrne
  have hroot (t : ℕ) (ht : t < 2 * W + 1) :
      Q26 n R (n - W + t) = if t = W then 1 else 0 :=
    Q318 n R W t hn (by omega) hWn ht
  rcases lt_or_gt_of_ne hrne with hrn | hnr
  · have hδ : δ = n - r := Nat.dist_eq_sub_of_le hrn.le
    let e := W + δ
    have he : r - W + e = n := by dsimp [e]; rw [hδ]; omega
    have heRange : e < 2 * W + 1 := by dsimp [e]; omega
    have hshift (t : ℕ) (ht : t < 2 * W + 1) :
        Q26 n R (n - W + t + X) =
          if t = e then 1 else 0 :=
      Q169 n R W X r v e t hn hR
        hWn hX hv hWr hrW he ht
    refine ⟨W, δ + 1, W - δ, ?_, rfl, by omega, by omega, ?_, ?_, ?_⟩
    · omega
    · intro t ht
      rw [hshift t (by omega), hroot t (by omega)]
      have hte : t ≠ e := by dsimp [e]; omega
      have htw : t ≠ W := by omega
      simp [hte, htw]
    · calc
        1 - φ⁻¹ ≤
          |∑ t ∈ Finset.range (δ + 1),
            (if t = 0 then (-1 : ℝ) else if t = δ then 1 else 0) *
              (φ⁻¹) ^ t| :=
                Q194 δ hδpos false
        _ = |∑ t ∈ Finset.range (δ + 1),
          ((Q26 n R (n - W + W + t + X) -
            Q26 n R (n - W + W + t) : ℤ) : ℝ) *
              (φ⁻¹) ^ t| := by
          congr 1
          apply Finset.sum_congr rfl
          intro t ht
          have htδ : t < δ + 1 := Finset.mem_range.mp ht
          have hglobal : W + t < 2 * W + 1 := by omega
          rw [show n - W + W + t + X = n - W + (W + t) + X by omega,
            show n - W + W + t = n - W + (W + t) by omega,
            hshift (W + t) hglobal, hroot (W + t) hglobal]
          by_cases ht0 : t = 0
          · subst t
            simp [e, hδpos.ne']
          · by_cases htδeq : t = δ
            · subst t
              simp [e, hδpos.ne']
            · have hneE : W + t ≠ e := by dsimp [e]; omega
              simp [ht0, htδeq, hneE]
    · intro t ht
      let g := W + (δ + 1) + t
      have hg : g < 2 * W + 1 := by dsimp [g]; omega
      rw [show n - W + W + (δ + 1) + t + X =
          n - W + g + X by dsimp [g]; omega,
        show n - W + W + (δ + 1) + t = n - W + g by
          dsimp [g]; omega,
        hshift g hg, hroot g hg]
      have hge : g ≠ e := by dsimp [g, e]; omega
      have hgw : g ≠ W := by dsimp [g]; omega
      simp [hge, hgw]
  · have hδ : δ = r - n := Nat.dist_eq_sub_of_le_right hnr.le
    let e := W - δ
    have he : r - W + e = n := by dsimp [e]; rw [hδ]; omega
    have heRange : e < 2 * W + 1 := by dsimp [e]; omega
    have hshift (t : ℕ) (ht : t < 2 * W + 1) :
        Q26 n R (n - W + t + X) =
          if t = e then 1 else 0 :=
      Q169 n R W X r v e t hn hR
        hWn hX hv hWr hrW he ht
    refine ⟨W - δ, δ + 1, W, ?_, rfl, by omega, by omega, ?_, ?_, ?_⟩
    · omega
    · intro t ht
      rw [hshift t (by omega), hroot t (by omega)]
      have hte : t ≠ e := by dsimp [e]; omega
      have htw : t ≠ W := by omega
      simp [hte, htw]
    · calc
        1 - φ⁻¹ ≤
          |∑ t ∈ Finset.range (δ + 1),
            (if t = 0 then (1 : ℝ) else if t = δ then -1 else 0) *
              (φ⁻¹) ^ t| :=
                Q194 δ hδpos true
        _ = |∑ t ∈ Finset.range (δ + 1),
          ((Q26 n R (n - W + (W - δ) + t + X) -
            Q26 n R (n - W + (W - δ) + t) : ℤ) : ℝ) *
              (φ⁻¹) ^ t| := by
          congr 1
          apply Finset.sum_congr rfl
          intro t ht
          have htδ : t < δ + 1 := Finset.mem_range.mp ht
          have hglobal : W - δ + t < 2 * W + 1 := by omega
          rw [show n - W + (W - δ) + t + X =
              n - W + (W - δ + t) + X by omega,
            show n - W + (W - δ) + t =
              n - W + (W - δ + t) by omega,
            hshift (W - δ + t) hglobal,
            hroot (W - δ + t) hglobal]
          by_cases ht0 : t = 0
          · subst t
            have hsubne : W - δ ≠ W := by omega
            simp [e, hsubne]
          · by_cases htδeq : t = δ
            · subst t
              have hsum : W - δ + δ = W := by omega
              have hWne : W ≠ W - δ := by omega
              rw [hsum]
              simp [e, hWne, ht0]
            · have hneE : W - δ + t ≠ e := by dsimp [e]; omega
              have hneW : W - δ + t ≠ W := by omega
              simp [ht0, htδeq, hneE, hneW]
    · intro t ht
      let g := W - δ + (δ + 1) + t
      have hg : g < 2 * W + 1 := by dsimp [g]; omega
      rw [show n - W + (W - δ) + (δ + 1) + t + X =
          n - W + g + X by dsimp [g]; omega,
        show n - W + (W - δ) + (δ + 1) + t = n - W + g by
          dsimp [g]; omega,
        hshift g hg, hroot g hg]
      have hge : g ≠ e := by dsimp [g, e]; omega
      have hgw : g ≠ W := by dsimp [g]; omega
      simp [hge, hgw]
end OMAH1Research
namespace OMAH1Research
theorem Q213
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (B : Finset ℕ) (H a b : ℕ)
    (hBH : ∀ k ∈ B, k < H)
    (hout : ∀ k, k ∉ B →
      Q5 (n k) a = Q5 (n k) b) :
    Q1 n a - Q1 n b =
      Q4 n B a -
        Q4 n B b := by
  let Q := max (max a b) H
  have haQ : a ≤ Q := le_trans (le_max_left _ _) (le_max_left _ _)
  have hbQ : b ≤ Q := le_trans (le_max_right _ _) (le_max_left _ _)
  have hHQ : H ≤ Q := le_max_right _ _
  have hBsub : B ⊆ Finset.range Q := by
    intro k hk
    exact Finset.mem_range.mpr ((hBH k hk).trans_le hHQ)
  rw [← Q35 n hpos hmono haQ,
    ← Q35 n hpos hmono hbQ]
  unfold Q70
  have houtsum :
      (∑ k ∈ Finset.range Q \ B, Q5 (n k) a) =
        ∑ k ∈ Finset.range Q \ B, Q5 (n k) b := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hout k (Finset.mem_sdiff.mp hk).2
  have hsplitA := Finset.sum_sdiff
    (f := fun k => Q5 (n k) a) hBsub
  have hsplitB := Finset.sum_sdiff
    (f := fun k => Q5 (n k) b) hBsub
  unfold Q4
  omega
theorem Q138
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (K H W A X p R : ℕ) (B : Finset ℕ)
    (hA : 0 < A) (hKH : K < H)
    (hKB : K ∈ B) (hBupper : ∀ k ∈ B, k < H)
    (hprefix : ∀ k < K, Q11 (n k) ∣ X)
    (hblockPeriod : ∀ k ∈ B, Q11 (n k) ∣ p)
    (C O : Finset ((ℕ × ℕ) × Bool))
    (hpartition : C ∪ O =
      Q14 n K H W A X p B)
    (hbudget :
      (∑ u ∈ O, (R / (Q2 n u /
        (Q2 n u).gcd p) + 1)) <
        (Q23 C (Q16 A X)
          (Q2 n) p R).card)
    (hcut : A + p * R + X + W < n H) :
    ∃ t < R,
      let N := A + p * t
      ∀ u < W,
        Q1 n (N + u + X) -
            Q1 n (N + u) =
          Q4 n B (A + u + X) -
            Q4 n B (A + u) := by
  obtain ⟨t, htR, hav⟩ :=
    Q87
      n hpos hmono K H W A X p R B hA hKH C O hpartition hbudget hcut
  let N := A + p * t
  have htransport (u : ℕ) :
      Q4 n B (N + u) =
        Q4 n B (A + u) := by
    have hp := Q61
      n B p (A + u) t hblockPeriod
    simpa [N, add_assoc, add_comm, add_left_comm] using hp
  have htransportX (u : ℕ) :
      Q4 n B (N + u + X) =
        Q4 n B (A + u + X) := by
    have hp := Q61
      n B p (A + u + X) t hblockPeriod
    simpa [N, add_assoc, add_comm, add_left_comm] using hp
  have hout (u : ℕ) (hu : u < W) (k : ℕ) (hkB : k ∉ B) :
      Q5 (n k) (N + u + X) =
        Q5 (n k) (N + u) := by
    by_cases hkK : k < K
    · exact Q94 n K X hprefix k hkK
    · have hKle : K ≤ k := by omega
      have hkNe : k ≠ K := fun heq => hkB (heq ▸ hKB)
      have hKk : K < k := lt_of_le_of_ne hKle (Ne.symm hkNe)
      have hz := hav k hKk hkB u hu
      rw [Q32 _ _ hz.2,
        Q32 _ _ hz.1]
  refine ⟨t, htR, ?_⟩
  dsimp only
  intro u hu
  rw [Q213
    n hpos hmono B H _ _ hBupper (hout u hu),
    htransportX, htransport]
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
open scoped BigOperators
theorem Q124
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (qden : ℕ) (hqden : 0 < qden) (T Tconj : ℝ)
    (hsum : HasSum (fun m : ℕ =>
      (Q1 n m : ℝ) * (φ⁻¹) ^ m) T)
    (htotal : InScaledGoldenPair qden T Tconj)
    (K H L Bword J A X p R : ℕ) (B : Finset ℕ) (η : ℝ)
    (hA : 0 < A) (hKH : K < H)
    (hKB : K ∈ B) (hBupper : ∀ k ∈ B, k < H)
    (hprefix : ∀ k < K, Q11 (n k) ∣ X)
    (hblockPeriod : ∀ k ∈ B, Q11 (n k) ∣ p)
    (htargetPre : ∀ s < L,
      Q4 n B (A + s + X) =
        Q4 n B (A + s))
    (htargetBlockLower : η ≤
      |∑ s ∈ Finset.range Bword,
        ((Q4 n B (A + L + s + X) -
          Q4 n B (A + L + s) : ℤ) : ℝ) *
            (φ⁻¹) ^ s|)
    (htargetPost : ∀ s < J,
      Q4 n B (A + L + Bword + s + X) =
        Q4 n B (A + L + Bword + s))
    (C O : Finset ((ℕ × ℕ) × Bool))
    (hpartition : C ∪ O = Q14 n K H
      (L + Bword + J) A X p B)
    (hbudget :
      (∑ u ∈ O, (R / (Q2 n u /
        (Q2 n u).gcd p) + 1)) <
        (Q23 C (Q16 A X)
          (Q2 n) p R).card)
    (hcut : A + p * R + X + (L + Bword + J) < n H)
    (hsmallPost : ∀ t < R,
      let N := A + p * t
      (φ⁻¹) ^ (Bword + J) *
        (Q7 n (N + X + L + Bword + J) +
          Q7 n (N + L + Bword + J)) < η)
    (hsmallPre : ∀ t < R,
      let N := A + p * t
      (φ⁻¹) ^ L *
          (Q7 n (N + X + L) +
            Q7 n (N + L)) *
        (Q6 n Tconj (N + X) +
          Q6 n Tconj N) <
      (((qden : ℕ) : ℝ)⁻¹) ^ 2) :
    False := by
  obtain ⟨t, htR, hword⟩ :=
    Q138
      n hpos hmono K H (L + Bword + J) A X p R B hA hKH hKB
        hBupper hprefix hblockPeriod C O hpartition hbudget hcut
  let N := A + p * t
  apply Q225
    n hpos hmono qden hqden T Tconj hsum htotal
      (N + X) N L Bword J η
  · intro s hs
    have hd := hword s (by omega)
    apply sub_eq_zero.mp
    calc
      Q1 n (N + X + s) -
          Q1 n (N + s) =
        Q4 n B (A + s + X) -
          Q4 n B (A + s) := by
            simpa [N, add_assoc, add_comm, add_left_comm] using hd
      _ = 0 := sub_eq_zero.mpr (htargetPre s hs)
  · calc
      η ≤ |∑ s ∈ Finset.range Bword,
        ((Q4 n B (A + L + s + X) -
          Q4 n B (A + L + s) : ℤ) : ℝ) *
            (φ⁻¹) ^ s| := htargetBlockLower
      _ = |∑ s ∈ Finset.range Bword,
        ((Q1 n (N + X + L + s) -
          Q1 n (N + L + s) : ℤ) : ℝ) *
            (φ⁻¹) ^ s| := by
        congr 1
        apply Finset.sum_congr rfl
        intro s hs
        have hsB : s < Bword := Finset.mem_range.mp hs
        have hd := hword (L + s) (by omega)
        congr 1
        exact_mod_cast (by
          simpa [N, add_assoc, add_comm, add_left_comm] using hd.symm)
  · intro s hs
    have hd := hword (L + Bword + s) (by omega)
    apply sub_eq_zero.mp
    calc
      Q1 n (N + X + L + Bword + s) -
          Q1 n (N + L + Bword + s) =
        Q4 n B (A + L + Bword + s + X) -
          Q4 n B (A + L + Bword + s) := by
            simpa [N, add_assoc, add_comm, add_left_comm] using hd
      _ = 0 := sub_eq_zero.mpr (htargetPost s hs)
  · simpa [N, add_assoc, add_comm, add_left_comm] using hsmallPost t htR
  · simpa [N, add_assoc, add_comm, add_left_comm] using hsmallPre t htR
theorem Q121
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (qden : ℕ) (Tconj η : ℝ)
    (H L Bword J A X p R : ℕ) (hp : 0 < p)
    (hcut : A + p * R + X + (L + Bword + J) < n H)
    (hpostCap :
      (φ⁻¹) ^ (Bword + J) * (2 * Q8 H) < η)
    (hpreCap :
      (φ⁻¹) ^ L * (2 * Q8 H) *
        (2 * Q10 Tconj H) <
        (((qden : ℕ) : ℝ)⁻¹) ^ 2) :
    (∀ t < R,
      let N := A + p * t
      (φ⁻¹) ^ (Bword + J) *
        (Q7 n (N + X + L + Bword + J) +
          Q7 n (N + L + Bword + J)) < η) ∧
    (∀ t < R,
      let N := A + p * t
      (φ⁻¹) ^ L *
          (Q7 n (N + X + L) +
            Q7 n (N + L)) *
        (Q6 n Tconj (N + X) +
          Q6 n Tconj N) <
      (((qden : ℕ) : ℝ)⁻¹) ^ 2) := by
  have htailCapNonneg := Q34 H
  have hconjCapNonneg := Q36 Tconj H
  constructor
  · intro t ht
    let N := A + p * t
    have hpt : p * t < p * R := (Nat.mul_lt_mul_left hp).mpr ht
    have hx₁ : N + X + L + Bword + J < n H := by dsimp [N]; omega
    have hx₂ : N + L + Bword + J < n H := by dsimp [N]; omega
    have hb₁ := Q27 n hpos hmono hx₁
    have hb₂ := Q27 n hpos hmono hx₂
    calc
      (φ⁻¹) ^ (Bword + J) *
          (Q7 n (N + X + L + Bword + J) +
            Q7 n (N + L + Bword + J)) ≤
        (φ⁻¹) ^ (Bword + J) * (2 * Q8 H) := by
          gcongr
          linarith
      _ < η := hpostCap
  · intro t ht
    let N := A + p * t
    have hpt : p * t < p * R := (Nat.mul_lt_mul_left hp).mpr ht
    have hxN : N < n H := by dsimp [N]; omega
    have hxNX : N + X < n H := by dsimp [N]; omega
    have hxL : N + L < n H := by dsimp [N]; omega
    have hxXL : N + X + L < n H := by dsimp [N]; omega
    have ht₁ := Q27 n hpos hmono hxXL
    have ht₂ := Q27 n hpos hmono hxL
    have hc₁ := Q39
      n hpos hmono Tconj hxNX
    have hc₂ := Q39
      n hpos hmono Tconj hxN
    have htailSum :
        Q7 n (N + X + L) +
          Q7 n (N + L) ≤ 2 * Q8 H := by
      linarith
    have hconjSum :
        Q6 n Tconj (N + X) +
          Q6 n Tconj N ≤
        2 * Q10 Tconj H := by
      linarith
    have hconjSumNonneg : 0 ≤
        Q6 n Tconj (N + X) +
          Q6 n Tconj N := by
      unfold Q6
      have hden : 0 < 1 - φ⁻¹ := sub_pos.mpr
        (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)
      positivity
    have hfirstNonneg : 0 ≤
        (φ⁻¹) ^ L * (2 * Q8 H) := by positivity
    calc
      (φ⁻¹) ^ L *
          (Q7 n (N + X + L) +
            Q7 n (N + L)) *
        (Q6 n Tconj (N + X) +
          Q6 n Tconj N) ≤
        (φ⁻¹) ^ L * (2 * Q8 H) *
          (Q6 n Tconj (N + X) +
            Q6 n Tconj N) := by
          gcongr
      _ ≤ (φ⁻¹) ^ L * (2 * Q8 H) *
          (2 * Q10 Tconj H) :=
        mul_le_mul_of_nonneg_left hconjSum hfirstNonneg
      _ < (((qden : ℕ) : ℝ)⁻¹) ^ 2 := hpreCap
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
theorem Q68
    (n : ℕ → ℕ) (K G W A X p L sR : ℕ) (B : Finset ℕ) :
    (Q20
      (Q24
        n K G W A X p L sR B)).card ≤
      2 * (Q0 K G).card := by
  calc
    (Q20
      (Q24
        n K G W A X p L sR B)).card ≤
      (Q24
        n K G W A X p L sR B).card := Finset.card_image_le
    _ ≤ (Q30
        n K G W A X p L sR B).card := Finset.card_image_le
    _ ≤ (Q28 n K G W A X p L sR).card :=
      Finset.card_filter_le _ _
    _ ≤ 2 * (Q0 K G).card :=
      Q217 n K G W A X p L sR
theorem Q229
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (K G W A X p L sR Bval z : ℕ) (Block : Finset ℕ)
    (hbound : ∀ j, K < j → j < G → n j ≤ Bval)
    (hz : z ∈ Q20
      (Q24
        n K G W A X p L sR Block)) :
    z ≤ Bval := by
  obtain ⟨q, hqQ, hqz⟩ :=
    (Q66
      (Q24
        n K G W A X p L sR Block) z).mp hz
  obtain ⟨u, huC, hqu⟩ := Finset.mem_image.mp hqQ
  rw [← hqz, ← hqu]
  have huOld := (Finset.mem_filter.mp huC).1
  have huCompat := (Finset.mem_filter.mp huOld).1
  have huBase := (Finset.mem_filter.mp huCompat).1
  have huOuter := Finset.mem_product.mp huBase
  have huInner := Finset.mem_product.mp huOuter.1
  have huPos := Finset.mem_filter.mp huInner.1
  have hjG := Finset.mem_range.mp huPos.1
  have hqpos : 0 < n u.1.1 / (n u.1.1).gcd p := by
    apply Nat.div_pos
    · exact Nat.gcd_le_left p (hpos u.1.1)
    · exact Nat.gcd_pos_of_pos_left p (hpos u.1.1)
  exact (Nat.minFac_le hqpos).trans <|
    (Nat.div_le_self _ _).trans (hbound u.1.1 huPos.2 hjG)
theorem Q137
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (K G W A X p L sR Bval : ℕ) (Block : Finset ℕ)
    (hBval : 0 < Bval)
    (hbound : ∀ j, K < j → j < G → n j ≤ Bval) :
    let S := Q20
      (Q24
        n K G W A X p L sR Block)
    let d := (Q0 K G).card
    (∏ z ∈ S, z) ≤ Bval ^ (2 * d) := by
  let S := Q20
    (Q24
      n K G W A X p L sR Block)
  let d := (Q0 K G).card
  have hprod : (∏ z ∈ S, z) ≤ Bval ^ S.card := by
    apply Finset.prod_le_pow_card
    intro z hz
    exact Q229
      n hpos K G W A X p L sR Bval z Block hbound hz
  have hcard : S.card ≤ 2 * d :=
    Q68
      n K G W A X p L sR Block
  exact hprod.trans (pow_le_pow_right₀ (by omega) hcard)
theorem Q295
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (K G H L J X r v R : ℕ) (Block : Finset ℕ)
    (hKG : K < G) (hGH : G ≤ H) (hL : L < n K)
    (hX : X = r + (2 * n K) * v)
    (hrUpper : r ≤ n K + L)
    (hsRWindow : n K + L - r < L + 1 + J) :
    let A := n K - L
    let W := L + 1 + J
    let p := 4 * n K
    let sR := n K + L - r
    let C0 := Q30
      n K G W A X p L sR Block
    let O := Q14
      n K H W A X p Block \ C0
    (∑ u ∈ O, (R / (Q2 n u /
      (Q2 n u).gcd p) + 1)) ≤
      2 * W * ∑ j ∈ Q0 K H,
        ((R * (4 * W)) / n j + 1) +
      2 * W * ∑ j ∈ Finset.Ico G H,
        ((R * (4 * n K)) / n j + 1) := by
  classical
  let A := n K - L
  let W := L + 1 + J
  let p := 4 * n K
  let sR := n K + L - r
  let C0 := Q30
    n K G W A X p L sR Block
  let O := Q14
    n K H W A X p Block \ C0
  let Cold := Q28 n K G W A X p L sR
  let Oold := Q18 n K H W A X p \ Cold
  have hsub : O ⊆ Oold := by
    intro u hu
    have huData := Finset.mem_sdiff.mp hu
    have huOutside := Finset.mem_filter.mp huData.1
    have huBaseOutside := Finset.mem_filter.mp huOutside.1
    have huOldCompat : u ∈ Q18 n K H W A X p :=
      Finset.mem_filter.mpr ⟨huBaseOutside.1, huOutside.2⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨huOldCompat, ?_⟩
    intro huCold
    apply huData.2
    apply Finset.mem_filter.mpr
    refine ⟨huCold, ?_⟩
    exact huBaseOutside.2
  calc
    (∑ u ∈ O, (R / (Q2 n u /
        (Q2 n u).gcd p) + 1)) ≤
      ∑ u ∈ Oold, (R / (Q2 n u /
        (Q2 n u).gcd p) + 1) :=
          Finset.sum_le_sum_of_subset hsub
    _ ≤ 2 * W * ∑ j ∈ Q0 K H,
        ((R * (4 * W)) / n j + 1) +
      2 * W * ∑ j ∈ Finset.Ico G H,
        ((R * (4 * n K)) / n j + 1) := by
      exact Q298 n hpos K G H L J X r v R
        hKG hGH hL hX hrUpper hsRWindow
theorem Q133
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (K G H W A X p L sR : ℕ) (Block : Finset ℕ)
    (hbound :
      let d := (Q0 K G).card
      (8 : ℝ) * ((2 * d + 1) * (2 * d + 2) : ℕ) *
        (W ^ 2 *
            (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
          W * n K *
            ((1 - c⁻¹)⁻¹ * (n G : ℝ)⁻¹)) < 1) :
    let Q := Q24
      n K G W A X p L sR Block
    let S := Q20 Q
    let D := (S.card + 1) * (S.card + 2)
    (8 : ℝ) * D *
      (W ^ 2 * (∑ j ∈ Q0 K H, ((n j : ℝ)⁻¹)) +
        W * n K * (∑ j ∈ Finset.Ico G H, ((n j : ℝ)⁻¹))) < 1 := by
  let Q := Q24
    n K G W A X p L sR Block
  let S := Q20 Q
  let d := (Q0 K G).card
  let D := (S.card + 1) * (S.card + 2)
  let Dmax := (2 * d + 1) * (2 * d + 2)
  have hScard : S.card ≤ 2 * d :=
    Q68
      n K G W A X p L sR Block
  have hD : D ≤ Dmax := by
    dsimp [D, Dmax]
    exact Nat.mul_le_mul (Nat.add_le_add_right hScard 1)
      (Nat.add_le_add_right hScard 2)
  have htail₁ := Q157
    n hpos c hc hratio K H
  have htail₂ := Q319 n hpos c hc hratio G H
  have hinner :
      W ^ 2 * (∑ j ∈ Q0 K H, ((n j : ℝ)⁻¹)) +
        W * n K * (∑ j ∈ Finset.Ico G H, ((n j : ℝ)⁻¹)) ≤
      W ^ 2 * (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
        W * n K * ((1 - c⁻¹)⁻¹ * (n G : ℝ)⁻¹) := by
    gcongr
  have hDreal : (D : ℝ) ≤ (Dmax : ℝ) := by exact_mod_cast hD
  calc
    (8 : ℝ) * D *
      (W ^ 2 * (∑ j ∈ Q0 K H, ((n j : ℝ)⁻¹)) +
        W * n K * (∑ j ∈ Finset.Ico G H, ((n j : ℝ)⁻¹))) ≤
      8 * (Dmax : ℝ) *
      (W ^ 2 * (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
        W * n K * ((1 - c⁻¹)⁻¹ * (n G : ℝ)⁻¹)) := by
      gcongr
    _ < 1 := by simpa [d, Dmax] using hbound
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
set_option maxHeartbeats 1200000 in
theorem Q140
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (K G H L J X r v : ℕ) (Block : Finset ℕ) (hKG : K < G) (hGH : G ≤ H)
    (hL : L < n K)
    (hX : X = r + (2 * n K) * v) (hv : Even v)
    (hrUpper : r ≤ n K + L)
    (hsRWindow : n K + L - r < L + 1 + J)
    (hnoDoubleOutside : ∀ j, K < j → j < G → j ∉ Block →
      n j ≠ 2 * n K)
    (hdensity :
      let A := n K - L
      let W := L + 1 + J
      let p := 4 * n K
      let sR := n K + L - r
      let Q := Q24 n K G W A X p L sR Block
      let S := Q20 Q
      let D := (S.card + 1) * (S.card + 2)
      (8 : ℝ) * D *
        (W ^ 2 * (∑ j ∈ Q0 K H, ((n j : ℝ)⁻¹)) +
          W * n K * (∑ j ∈ Finset.Ico G H, ((n j : ℝ)⁻¹))) < 1) :
    let A := n K - L
    let W := L + 1 + J
    let p := 4 * n K
    let sR := n K + L - r
    let C0 := Q30 n K G W A X p L sR Block
    let O := Q14 n K H W A X p Block \ C0
    let Q := Q24 n K G W A X p L sR Block
    let S := Q20 Q
    let D := (S.card + 1) * (S.card + 2)
    let Z₁ := (Q0 K H).card
    let Z₂ := (Finset.Ico G H).card
    ∃ M R : ℕ,
      0 < M ∧ M = ∏ z ∈ S, z ∧ 0 < R ∧
      (∑ u ∈ O, (R / (Q2 n u /
        (Q2 n u).gcd p) + 1)) <
        (Q23 C0 (Q16 A X)
          (Q2 n) p R).card ∧
      R ≤ M + 2 * D * W * (Z₁ + Z₂) := by
  classical
  let A := n K - L
  let W := L + 1 + J
  let p := 4 * n K
  let sR := n K + L - r
  let C0 := Q30 n K G W A X p L sR Block
  let O := Q14 n K H W A X p Block \ C0
  let Q := Q24 n K G W A X p L sR Block
  let S := Q20 Q
  let D := (S.card + 1) * (S.card + 2)
  let Z₁ := (Q0 K H).card
  let Z₂ := (Finset.Ico G H).card
  let sigma₁ : ℝ := ∑ j ∈ Q0 K H, ((n j : ℝ)⁻¹)
  let sigma₂ : ℝ := ∑ j ∈ Finset.Ico G H, ((n j : ℝ)⁻¹)
  have hdensity' : (8 : ℝ) * D *
      (W ^ 2 * sigma₁ + W * n K * sigma₂) < 1 := by
    simpa [A, W, p, sR, Q, S, D, sigma₁, sigma₂] using hdensity
  obtain ⟨M, hM, hMeq, hprotected⟩ :=
    Q99
      n hpos hmono K G L J X r v Block hKG hL hX hv hrUpper
        hsRWindow hnoDoubleOutside
  have hDpos : 0 < D := by dsimp [D]; positivity
  let delta : ℝ := 2 - 8 * D *
    (W ^ 2 * sigma₁ + W * n K * sigma₂)
  have hdeltaOne : 1 < delta := by
    dsimp [delta]
    nlinarith
  have hdelta : 0 < delta := lt_trans (by norm_num) hdeltaOne
  have hden : 0 < delta * (M : ℝ) :=
    mul_pos hdelta (by exact_mod_cast hM)
  let E : ℕ := 2 * D * W * (Z₁ + Z₂)
  let q : ℝ := (E : ℝ) / (delta * (M : ℝ))
  let T : ℕ := ⌊q⌋₊ + 1
  have hqnonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (by positivity) hden.le
  have hqT : q < (T : ℝ) := by
    dsimp [T]
    simpa using (Nat.lt_floor_add_one q)
  have hTpos : 0 < T := by dsimp [T]; omega
  let R := T * M
  have hRpos : 0 < R := mul_pos hTpos hM
  have hendpoint : (E : ℝ) < delta * (R : ℝ) := by
    have hm : (E : ℝ) < (T : ℝ) * (delta * (M : ℝ)) := by
      apply (div_lt_iff₀ hden).mp
      simpa [q] using hqT
    calc
      (E : ℝ) < (T : ℝ) * (delta * (M : ℝ)) := hm
      _ = delta * (R : ℝ) := by
        dsimp [R]
        push_cast
        ring
  have hRbound : R ≤ M + E := by
    have hfloor : ((⌊q⌋₊ : ℕ) : ℝ) ≤ q := Nat.floor_le hqnonneg
    have hTle : (T : ℝ) ≤ q + 1 := by
      dsimp [T]
      push_cast
      linarith
    have hqM : q * (M : ℝ) = (E : ℝ) / delta := by
      dsimp [q]
      field_simp
    have hdivle : (E : ℝ) / delta ≤ (E : ℝ) := by
      apply (div_le_iff₀ hdelta).mpr
      have hEnonneg : (0 : ℝ) ≤ E := by positivity
      nlinarith
    have hreal : (R : ℝ) ≤ (M + E : ℕ) := by
      calc
        (R : ℝ) = (T : ℝ) * (M : ℝ) := by simp [R]
        _ ≤ (q + 1) * (M : ℝ) := by gcongr
        _ = q * (M : ℝ) + (M : ℝ) := by ring
        _ = (E : ℝ) / delta + (M : ℝ) := by rw [hqM]
        _ ≤ (E : ℝ) + (M : ℝ) := by gcongr
        _ = (M + E : ℕ) := by push_cast; ring
    exact_mod_cast hreal
  let B := ∑ u ∈ O, (R / (Q2 n u /
    (Q2 n u).gcd p) + 1)
  have hBnat : B ≤
      2 * W * ∑ j ∈ Q0 K H,
        ((R * (4 * W)) / n j + 1) +
      2 * W * ∑ j ∈ Finset.Ico G H,
        ((R * (4 * n K)) / n j + 1) := by
    dsimp [B]
    exact Q295 n hpos K G H L J X r v R Block
      hKG hGH hL hX hrUpper hsRWindow
  have hsum₁ := Q88
    (Q0 K H) n (fun j hj => hpos j) (R * (4 * W))
  have hsum₂ := Q88
    (Finset.Ico G H) n (fun j hj => hpos j) (R * (4 * n K))
  have hBreal : (B : ℝ) ≤
      8 * (R : ℝ) *
          (W ^ 2 * sigma₁ + W * n K * sigma₂) +
        2 * W * (Z₁ + Z₂) := by
    have hc : (B : ℝ) ≤
        ((2 * W * ∑ j ∈ Q0 K H,
            ((R * (4 * W)) / n j + 1) +
          2 * W * ∑ j ∈ Finset.Ico G H,
            ((R * (4 * n K)) / n j + 1) : ℕ) : ℝ) := by
      exact_mod_cast hBnat
    push_cast at hc
    have hsum₁' :
        ((∑ j ∈ Q0 K H,
          ((R * (4 * W)) / n j + 1) : ℕ) : ℝ) ≤
          (R * (4 * W) : ℕ) * sigma₁ + Z₁ := by
      simpa [sigma₁, Z₁] using hsum₁
    have hsum₂' :
        ((∑ j ∈ Finset.Ico G H,
          ((R * (4 * n K)) / n j + 1) : ℕ) : ℝ) ≤
          (R * (4 * n K) : ℕ) * sigma₂ + Z₂ := by
      simpa [sigma₂, Z₂] using hsum₂
    have hs1 :
        ((∑ j ∈ Q0 K H,
          ((R * (4 * W)) / n j + 1) : ℕ) : ℝ) ≤
          (R : ℝ) * (4 * W : ℕ) * sigma₁ + Z₁ := by
      calc
        _ ≤ ((R * (4 * W) : ℕ) : ℝ) * sigma₁ + Z₁ := hsum₁'
        _ = (R : ℝ) * (4 * W : ℕ) * sigma₁ + Z₁ := by
          push_cast
          ring
    have hs2 :
        ((∑ j ∈ Finset.Ico G H,
          ((R * (4 * n K)) / n j + 1) : ℕ) : ℝ) ≤
          (R : ℝ) * (4 * n K : ℕ) * sigma₂ + Z₂ := by
      calc
        _ ≤ ((R * (4 * n K) : ℕ) : ℝ) * sigma₂ + Z₂ := hsum₂'
        _ = (R : ℝ) * (4 * n K : ℕ) * sigma₂ + Z₂ := by
          push_cast
          ring
    calc
      (B : ℝ) ≤
          (2 * W : ℕ) *
            ((∑ j ∈ Q0 K H,
              ((R * (4 * W)) / n j + 1) : ℕ) : ℝ) +
          (2 * W : ℕ) *
            ((∑ j ∈ Finset.Ico G H,
              ((R * (4 * n K)) / n j + 1) : ℕ) : ℝ) := by
        simpa using hc
      _ ≤ (2 * W : ℕ) *
            ((R : ℝ) * (4 * W : ℕ) * sigma₁ + Z₁) +
          (2 * W : ℕ) *
            ((R : ℝ) * (4 * n K : ℕ) * sigma₂ + Z₂) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hs1 (by positivity))
          (mul_le_mul_of_nonneg_left hs2 (by positivity))
      _ = 8 * (R : ℝ) *
          (W ^ 2 * sigma₁ + W * n K * sigma₂) +
            2 * W * (Z₁ + Z₂) := by
        push_cast
        ring
  have hDBreal : (D * B : ℕ) < 2 * R := by
    have hmain : (D : ℝ) * (B : ℝ) < 2 * (R : ℝ) := by
      have hscaled := mul_le_mul_of_nonneg_left hBreal
        (show (0 : ℝ) ≤ D by positivity)
      dsimp [delta, E] at hendpoint
      push_cast at hendpoint hscaled
      nlinarith
    exact_mod_cast hmain
  have hprot := hprotected T
  have hBcard : B < (Q23 C0 (Q16 A X)
      (Q2 n) p R).card := by
    have hchain : D * B < D *
        (Q23 C0 (Q16 A X)
          (Q2 n) p R).card := by
      calc
        D * B < 2 * R := hDBreal
        _ ≤ D * (Q23 C0 (Q16 A X)
          (Q2 n) p R).card := by
            simpa [D, R, S, Q, C0, A, W, p, sR] using hprot
    exact (Nat.mul_lt_mul_left hDpos).mp hchain
  refine ⟨M, R, hM, ?_, hRpos, hBcard, ?_⟩
  · simpa [S, Q, A, W, p, sR] using hMeq
  · simpa [E, D, W, Z₁, Z₂, S, Q, A, p, sR] using hRbound
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
theorem Q196
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (K G B L J X r v H : ℕ) (Block : Finset ℕ) (hKG : K < G) (hB : 0 < B)
    (hvalues : ∀ j, K < j → j < G → n j ≤ B)
    (hL : L < n K)
    (hX : X = r + (2 * n K) * v) (hv : Even v)
    (hrUpper : r ≤ n K + L)
    (hsRWindow : n K + L - r < L + 1 + J)
    (hnoDoubleOutside : ∀ j, K < j → j < G → j ∉ Block →
      n j ≠ 2 * n K)
    (hdensity :
      let W := L + 1 + J
      let d := (Q0 K G).card
      (8 : ℝ) * ((2 * d + 1) * (2 * d + 2) : ℕ) *
        (W ^ 2 *
            (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
          W * n K * ((1 - c⁻¹)⁻¹ * (n G : ℝ)⁻¹)) < 1)
    (hGH : G ≤ H)
    (haffine :
      let A := n K - L
      let W := L + 1 + J
      let p := 4 * n K
      let d := (Q0 K G).card
      let Dmax := (2 * d + 1) * (2 * d + 2)
      let Mmax := B ^ (2 * d)
      let U := A + p * Mmax + X + W
      let V := 4 * p * Dmax * W
      U + V * H < n H) :
    let A := n K - L
    let W := L + 1 + J
    let p := 4 * n K
    let sR := n K + L - r
    let C0 := Q30 n K G W A X p L sR Block
    ∃ R : ℕ, 0 < R ∧
      let O := Q14 n K H W A X p Block \ C0
      (∑ u ∈ O, (R / (Q2 n u /
        (Q2 n u).gcd p) + 1)) <
        (Q23 C0 (Q16 A X)
          (Q2 n) p R).card ∧
      A + p * R + X + W < n H := by
  classical
  let A := n K - L
  let W := L + 1 + J
  let p := 4 * n K
  let sR := n K + L - r
  let Q := Q24 n K G W A X p L sR Block
  let S := Q20 Q
  let d := (Q0 K G).card
  let D := (S.card + 1) * (S.card + 2)
  let Dmax := (2 * d + 1) * (2 * d + 2)
  let Mmax := B ^ (2 * d)
  let U := A + p * Mmax + X + W
  let V := 4 * p * Dmax * W
  have haffine' : U + V * H < n H := by
    simpa [A, W, p, d, Dmax, Mmax, U, V] using haffine
  have hdensityH :
      let Q' := Q24 n K G W A X p L sR Block
      let S' := Q20 Q'
      let D' := (S'.card + 1) * (S'.card + 2)
      (8 : ℝ) * D' *
        (W ^ 2 * (∑ j ∈ Q0 K H, ((n j : ℝ)⁻¹)) +
          W * n K * (∑ j ∈ Finset.Ico G H, ((n j : ℝ)⁻¹))) < 1 := by
    apply Q133
      n hpos c hc hratio K G H W A X p L sR Block
    simpa [W, d] using hdensity
  obtain ⟨M, R, hM, hMeq, hR, hbudget, hRbound⟩ :=
    Q140
      n hpos hmono K G H L J X r v Block hKG hGH hL hX hv hrUpper
        hsRWindow hnoDoubleOutside hdensityH
  have hMle : M ≤ Mmax := by
    rw [hMeq]
    dsimp [Mmax]
    exact Q137
      n hpos K G W A X p L sR B Block hB hvalues
  have hDle : D ≤ Dmax := by
    have hScard : S.card ≤ 2 * d :=
      Q68
        n K G W A X p L sR Block
    dsimp [D, Dmax]
    exact Nat.mul_le_mul (Nat.add_le_add_right hScard 1)
      (Nat.add_le_add_right hScard 2)
  have hZ₁ : (Q0 K H).card ≤ H := by
    calc
      (Q0 K H).card ≤ (Finset.range H).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = H := Finset.card_range H
  have hZ₂ : (Finset.Ico G H).card ≤ H := by
    have hcard : (Finset.Ico G H).card = H - G := by simp
    omega
  have hZsum : (Q0 K H).card +
      (Finset.Ico G H).card ≤ 2 * H := by omega
  have hendpointCost :
      2 * D * W * ((Q0 K H).card +
        (Finset.Ico G H).card) ≤ 4 * Dmax * W * H := by
    calc
      2 * D * W * ((Q0 K H).card +
          (Finset.Ico G H).card) ≤
          2 * Dmax * W * (2 * H) := by gcongr
      _ = 4 * Dmax * W * H := by ring
  have hRcoarse : R ≤ Mmax + 4 * Dmax * W * H := by
    calc
      R ≤ M + 2 * D * W * ((Q0 K H).card +
          (Finset.Ico G H).card) := by
            simpa [D, S, Q, A, W, p, sR] using hRbound
      _ ≤ Mmax + 4 * Dmax * W * H :=
        Nat.add_le_add hMle hendpointCost
  have hcut : A + p * R + X + W < n H := by
    have hcost : A + p * R + X + W ≤ U + V * H := by
      calc
        A + p * R + X + W ≤
            A + p * (Mmax + 4 * Dmax * W * H) + X + W := by
          gcongr
        _ = U + V * H := by
          dsimp [U, V]
          ring
    exact hcost.trans_lt haffine'
  refine ⟨R, hR, ?_⟩
  simpa [A, W, p, sR] using And.intro hbudget hcut
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
theorem Q176
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (q : ℕ) (hq : (2 : ℝ) ≤ c ^ q)
    (K G B L J X r v : ℕ) (Block : Finset ℕ) (hKG : K < G) (hB : 0 < B)
    (hvalues : ∀ j, K < j → j < G → n j ≤ B)
    (hL : L < n K)
    (hX : X = r + (2 * n K) * v) (hv : Even v)
    (hrUpper : r ≤ n K + L)
    (hsRWindow : n K + L - r < L + 1 + J)
    (hnoDoubleOutside : ∀ j, K < j → j < G → j ∉ Block →
      n j ≠ 2 * n K)
    (hdensity :
      let W := L + 1 + J
      let d := (Q0 K G).card
      (8 : ℝ) * ((2 * d + 1) * (2 * d + 2) : ℕ) *
        (W ^ 2 *
            (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
          W * n K * ((1 - c⁻¹)⁻¹ * (n G : ℝ)⁻¹)) < 1) :
    let A := n K - L
    let W := L + 1 + J
    let p := 4 * n K
    let sR := n K + L - r
    let d := (Q0 K G).card
    let Dmax := (2 * d + 1) * (2 * d + 2)
    let Mmax := B ^ (2 * d)
    let U := A + p * Mmax + X + W
    let V := 4 * p * Dmax * W
    let A₀ := U + V * G
    let B₀ := V * q
    let N := A₀ + B₀ + 1
    let t := Nat.clog 2 N
    let H := G + q * (4 * t + 4)
    let C0 := Q30 n K G W A X p L sR Block
    ∃ R : ℕ, 0 < R ∧
      let O := Q14 n K H W A X p Block \ C0
      (∑ u ∈ O, (R / (Q2 n u /
        (Q2 n u).gcd p) + 1)) <
        (Q23 C0 (Q16 A X)
          (Q2 n) p R).card ∧
      A + p * R + X + W < n H := by
  let A := n K - L
  let W := L + 1 + J
  let p := 4 * n K
  let sR := n K + L - r
  let d := (Q0 K G).card
  let Dmax := (2 * d + 1) * (2 * d + 2)
  let Mmax := B ^ (2 * d)
  let U := A + p * Mmax + X + W
  let V := 4 * p * Dmax * W
  let A₀ := U + V * G
  let B₀ := V * q
  let N := A₀ + B₀ + 1
  let t := Nat.clog 2 N
  let H := G + q * (4 * t + 4)
  have hAff := Q83
    n hpos c hc hratio q hq G U V
  have hGH : G ≤ H := by omega
  have haffine : U + V * H < n H := by
    simpa [A₀, B₀, N, t, H] using hAff.2
  exact Q196
    n hpos hmono c hc hratio K G B L J X r v H Block hKG hB hvalues
      hL hX hv hrUpper hsRWindow hnoDoubleOutside hdensity hGH
      (by simpa [A, W, p, d, Dmax, Mmax, U, V] using haffine)
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
open scoped BigOperators
theorem Q86
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (qden : ℕ) (hqden : 0 < qden) (T Tconj : ℝ)
    (hsum : HasSum (fun m : ℕ =>
      (Q1 n m : ℝ) * (φ⁻¹) ^ m) T)
    (htotal : InScaledGoldenPair qden T Tconj)
    (q : ℕ) (hq : (2 : ℝ) ≤ c ^ q)
    (K G Bval w X r v : ℕ) (Block : Finset ℕ)
    (L Bword J : ℕ) (η : ℝ)
    (hKG : K < G) (hBval : 0 < Bval)
    (hvalues : ∀ j, K < j → j < G → n j ≤ Bval)
    (hw : w < n K)
    (hX : X = r + (2 * n K) * v) (hv : Even v)
    (hrUpper : r ≤ n K + w)
    (hsRWindow : n K + w - r < w + 1 + w)
    (hKB : K ∈ Block) (hBlockUpperG : ∀ k ∈ Block, k < G)
    (hnoDoubleOutside : ∀ j, K < j → j < G → j ∉ Block →
      n j ≠ 2 * n K)
    (hprefix : Q12 n K ∣ X)
    (hblockPeriod : ∀ k ∈ Block, Q11 (n k) ∣ 4 * n K)
    (hspan : L + Bword + J = w + 1 + w)
    (htargetPre : ∀ s < L,
      Q4 n Block (n K - w + s + X) =
        Q4 n Block (n K - w + s))
    (htargetBlockLower : η ≤
      |∑ s ∈ Finset.range Bword,
        ((Q4 n Block
              (n K - w + L + s + X) -
          Q4 n Block
              (n K - w + L + s) : ℤ) : ℝ) *
            (φ⁻¹) ^ s|)
    (htargetPost : ∀ s < J,
      Q4 n Block
          (n K - w + L + Bword + s + X) =
        Q4 n Block
          (n K - w + L + Bword + s))
    (hdensity :
      let W := w + 1 + w
      let d := (Q0 K G).card
      (8 : ℝ) * ((2 * d + 1) * (2 * d + 2) : ℕ) *
        (W ^ 2 *
            (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
          W * n K * ((1 - c⁻¹)⁻¹ * (n G : ℝ)⁻¹)) < 1)
    (hpostCap :
      let A := n K - w
      let W := w + 1 + w
      let p := 4 * n K
      let d := (Q0 K G).card
      let Dmax := (2 * d + 1) * (2 * d + 2)
      let Mmax := Bval ^ (2 * d)
      let U := A + p * Mmax + X + W
      let V := 4 * p * Dmax * W
      let A₀ := U + V * G
      let B₀ := V * q
      let N := A₀ + B₀ + 1
      let t := Nat.clog 2 N
      let H := G + q * (4 * t + 4)
      (φ⁻¹) ^ (Bword + J) * (2 * Q8 H) < η)
    (hpreCap :
      let A := n K - w
      let W := w + 1 + w
      let p := 4 * n K
      let d := (Q0 K G).card
      let Dmax := (2 * d + 1) * (2 * d + 2)
      let Mmax := Bval ^ (2 * d)
      let U := A + p * Mmax + X + W
      let V := 4 * p * Dmax * W
      let A₀ := U + V * G
      let B₀ := V * q
      let N := A₀ + B₀ + 1
      let t := Nat.clog 2 N
      let H := G + q * (4 * t + 4)
      (φ⁻¹) ^ L * (2 * Q8 H) *
        (2 * Q10 Tconj H) <
        (((qden : ℕ) : ℝ)⁻¹) ^ 2) :
    False := by
  classical
  let A := n K - w
  let W := w + 1 + w
  let p := 4 * n K
  let sR := n K + w - r
  let d := (Q0 K G).card
  let Dmax := (2 * d + 1) * (2 * d + 2)
  let Mmax := Bval ^ (2 * d)
  let U := A + p * Mmax + X + W
  let V := 4 * p * Dmax * W
  let A₀ := U + V * G
  let B₀ := V * q
  let N := A₀ + B₀ + 1
  let t := Nat.clog 2 N
  let H := G + q * (4 * t + 4)
  let C0 := Q30
    n K G W A X p w sR Block
  let O := Q14
    n K H W A X p Block \ C0
  have hcert := Q176
    n hpos hmono c hc hratio q hq K G Bval w w X r v Block
      hKG hBval hvalues hw hX hv hrUpper hsRWindow
      hnoDoubleOutside hdensity
  change ∃ R : ℕ, 0 < R ∧
      (∑ u ∈ O, (R / (Q2 n u /
        (Q2 n u).gcd p) + 1)) <
        (Q23 C0 (Q16 A X)
          (Q2 n) p R).card ∧
      A + p * R + X + W < n H at hcert
  obtain ⟨R, hR, hbudget, hcut⟩ := hcert
  have hA : 0 < A := by dsimp [A]; omega
  have hGH : G ≤ H := by dsimp [H]; omega
  have hKH : K < H := lt_of_lt_of_le hKG hGH
  have hperiod : ∀ k < K, Q11 (n k) ∣ X := by
    intro k hk
    exact dvd_trans (Q71 n hk) hprefix
  have hBlockUpperH : ∀ k ∈ Block, k < H := by
    intro k hk
    exact (hBlockUpperG k hk).trans_le hGH
  have hCsub : C0 ⊆
      Q14 n K H W A X p Block := by
    intro u hu
    have huOld := (Finset.mem_filter.mp hu).1
    have huNotBlock := (Finset.mem_filter.mp hu).2
    have huG := (Finset.mem_filter.mp huOld).1
    have huCenter := (Finset.mem_filter.mp huOld).2
    have huGdata := Finset.mem_filter.mp huG
    apply Finset.mem_filter.mpr
    refine ⟨?_, huGdata.2⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, huNotBlock⟩
    have huOuter := Finset.mem_product.mp huGdata.1
    have huInner := Finset.mem_product.mp huOuter.1
    have hjData := Finset.mem_filter.mp huInner.1
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, huInner.2⟩, huOuter.2⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (lt_of_lt_of_le
      (Finset.mem_range.mp hjData.1) hGH), hjData.2⟩
  have hpartition : C0 ∪ O =
      Q14 n K H W A X p Block :=
    Finset.union_sdiff_of_subset hCsub
  have hnorm := Q121
    n hpos hmono qden Tconj η H L Bword J A X p R
      (by dsimp [p]; omega)
      (by simpa [W, hspan] using hcut)
      (by simpa [A, W, p, d, Dmax, Mmax, U, V, A₀, B₀, N, t, H]
        using hpostCap)
      (by simpa [A, W, p, d, Dmax, Mmax, U, V, A₀, B₀, N, t, H]
        using hpreCap)
  exact Q124
    n hpos hmono qden hqden T Tconj hsum htotal
      K H L Bword J A X p R Block η hA hKH hKB hBlockUpperH
      hperiod hblockPeriod
      (by simpa [A] using htargetPre)
      (by simpa [A] using htargetBlockLower)
      (by simpa [A] using htargetPost)
      C0 O (by simpa [W, hspan] using hpartition) hbudget
      (by simpa [W, hspan] using hcut) hnorm.1 hnorm.2
end OMAH1Research
namespace OMAH1Research
lemma Q160 (a : ℕ) :
    Q11 a ∣ 4 * a := by
  unfold Q11
  split_ifs
  · exact ⟨2, by ring⟩
  · exact dvd_rfl
lemma Q73
    (n : ℕ → ℕ) (K m : ℕ) :
    Q4 n {K} m =
      Q5 (n K) m := by
  simp [Q4]
lemma Q172
    (n : ℕ → ℕ) (K j m : ℕ) (hKj : K < j)
    (hj : n j = 2 * n K) :
    Q4 n {K, j} m =
      Q26 (n K) 2 m := by
  have hKne : K ∉ ({j} : Finset ℕ) := by simp [ne_of_lt hKj]
  unfold Q4 Q26
  rw [Finset.sum_insert hKne]
  simp [hj, Finset.sum_range_succ]
  congr 1
  omega
lemma Q343
    (n : ℕ → ℕ) (K : ℕ) :
    ∀ k ∈ ({K} : Finset ℕ),
      Q11 (n k) ∣ 4 * n K := by
  intro k hk
  have hkEq : k = K := Finset.mem_singleton.mp hk
  subst k
  exact Q160 (n K)
lemma Q374
    (n : ℕ → ℕ) (K j : ℕ) (hj : n j = 2 * n K) :
    ∀ k ∈ ({K, j} : Finset ℕ),
      Q11 (n k) ∣ 4 * n K := by
  intro k hk
  rcases Finset.mem_insert.mp hk with hkEq | hk
  · subst k
    exact Q160 (n K)
  · have hkEq : k = j := Finset.mem_singleton.mp hk
    subst k
    rw [hj]
    have heven : Even (2 * n K) := ⟨n K, by ring⟩
    rw [Q11, if_pos heven]
    exact ⟨1, by ring⟩
end OMAH1Research
namespace OMAH1Research
theorem Q203
    (P n : ℕ) (hn : 0 < n)
    (hglt : (4 * n).gcd P < n) :
    let g := (4 * n).gcd P
    ∃ X r v : ℕ,
      P ∣ X ∧ X < (4 * n) * P ∧
      X = r + (2 * n) * v ∧ Even v ∧
      0 < r ∧ r < 2 * n ∧ r ≠ n ∧
      r.dist n ≤ g := by
  let M := 4 * n
  let g := M.gcd P
  have hndvd : ¬2 * n ∣ P := by
    intro hd
    have htwoM : 2 * n ∣ M := by dsimp [M]; exact ⟨2, by ring⟩
    have htwoG : 2 * n ∣ g := by
      dsimp [g]
      exact Nat.dvd_gcd htwoM hd
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left P (by dsimp [M]; omega)
    have := Nat.le_of_dvd hgpos htwoG
    change g < n at hglt
    omega
  obtain ⟨X, r, v, hPX, hXbound, hX, hv, hrpos, hrlt, hnear⟩ :=
    Q144 P n hn hndvd
  by_cases hrne : r ≠ n
  · refine ⟨X, r, v, hPX, hXbound, hX, hv, hrpos, hrlt, hrne, ?_⟩
    omega
  · have hrEq : r = n := not_ne_iff.mp hrne
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left P (by dsimp [g, M]; omega)
    have hgM : g ∣ M := Nat.gcd_dvd_left M P
    have hgP : g ∣ P := Nat.gcd_dvd_right M P
    have hgn : g ∣ n := by
      rw [← hrEq]
      have hrmod : r = X % M := by
        obtain ⟨z, hz⟩ := hv
        rw [hX, hz, show 2 * n * (z + z) = M * z by
          dsimp [M]; ring,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
        exact hrlt.trans (by dsimp [M]; omega)
      rw [hrmod]
      have hgX : g ∣ X := dvd_trans hgP hPX
      have hgTerm : g ∣ M * (X / M) := dvd_mul_of_dvd_left hgM _
      have hx := Nat.mod_add_div X M
      rw [← hx] at hgX
      exact (Nat.dvd_add_iff_left hgTerm).mpr hgX
    let q := M / g
    let P' := P / g
    let a := n / g
    let k := a + 1
    have hMFactor : g * q = M := by
      dsimp [q]
      exact Nat.mul_div_cancel' hgM
    have hPFactor : g * P' = P := by
      dsimp [P']
      exact Nat.mul_div_cancel' hgP
    have hnFactor : g * a = n := by
      dsimp [a]
      exact Nat.mul_div_cancel' hgn
    have hqpos : 0 < q := by
      dsimp [q]
      exact Nat.div_pos (Nat.gcd_le_left P (by dsimp [M]; omega)) hgpos
    have hcop : P'.Coprime q := by
      have hc := Nat.coprime_div_gcd_div_gcd (m := M) (n := P) hgpos
      exact hc.symm
    have hkpos : 0 < k := by dsimp [k]; exact Nat.succ_pos a
    have hklt : k < q := by
      have hqeq : g * q = g * (4 * a) := by
        calc
          g * q = M := hMFactor
          _ = 4 * n := rfl
          _ = 4 * (g * a) := by rw [hnFactor]
          _ = g * (4 * a) := by ring
      have hqeq' : q = 4 * a := Nat.mul_left_cancel hgpos hqeq
      dsimp [k]
      omega
    obtain ⟨u, huq, hu⟩ :=
      Nat.exists_mul_mod_eq_of_coprime k hcop (Nat.ne_of_gt hqpos)
    have hkmod : k % q = k := Nat.mod_eq_of_lt hklt
    rw [hkmod] at hu
    let r' := g * k
    let X' := P * u
    have hr'mod : r' = X' % M := by
      dsimp [r', X']
      rw [← hPFactor, ← hMFactor, mul_assoc, Nat.mul_mod_mul_left, hu]
    have hr'eq : r' = n + g := by dsimp [r', k]; rw [← hnFactor]; ring
    have hr'pos : 0 < r' := by rw [hr'eq]; omega
    have hr'lt : r' < 2 * n := by
      rw [hr'eq]
      change g < n at hglt
      omega
    let z := X' / M
    let v' := X' / (2 * n)
    have hdecomp : X' = r' + (2 * n) * (z * 2) := by
      have hx := Nat.mod_add_div X' M
      rw [← hr'mod] at hx
      calc
        X' = r' + M * (X' / M) := hx.symm
        _ = r' + (2 * n) * (z * 2) := by dsimp [M, z]; ring
    have hv' : v' = z * 2 := by
      dsimp [v']
      rw [hdecomp, Nat.add_mul_div_left r' (z * 2) (by omega : 0 < 2 * n),
        Nat.div_eq_of_lt hr'lt]
      simp
    have hPne : P ≠ 0 := by
      intro hP0
      apply hndvd
      rw [hP0]
      exact dvd_zero _
    have hPpos : 0 < P := Nat.pos_of_ne_zero hPne
    have hqM : q ≤ M := Nat.div_le_self M g
    have hX'bound : X' < (4 * n) * P := by
      dsimp [X', M] at hqM ⊢
      nlinarith
    refine ⟨X', r', v', ⟨u, rfl⟩, hX'bound, ?_, ?_, hr'pos,
      hr'lt, ?_, ?_⟩
    · rw [hdecomp, hv']
    · rw [hv']
      exact ⟨z, by ring⟩
    · rw [hr'eq]
      omega
    · have hdist : r'.dist n = g := by
        rw [hr'eq, Nat.dist_eq_sub_of_le_right (by omega)]
        omega
      rw [hdist]
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
open scoped BigOperators
private lemma Q255 {a b : ℕ} (hab : a ≤ b) :
    (φ⁻¹ : ℝ) ^ b ≤ (φ⁻¹ : ℝ) ^ a := by
  have hr0 : 0 ≤ (φ⁻¹ : ℝ) := inv_nonneg.mpr Real.goldenRatio_pos.le
  have hrle : (φ⁻¹ : ℝ) ≤ 1 :=
    (inv_le_one₀ Real.goldenRatio_pos).mpr Real.one_lt_goldenRatio.le
  exact pow_le_pow_of_le_one hr0 hrle hab
theorem Q202
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (qden : ℕ) (hqden : 0 < qden) (T Tconj : ℝ)
    (hsum : HasSum (fun m : ℕ =>
      (Q1 n m : ℝ) * (φ⁻¹) ^ m) T)
    (htotal : InScaledGoldenPair qden T Tconj)
    (q : ℕ) (hqpos : 0 < q) (hq : (2 : ℝ) ≤ c ^ q)
    (K w X r v : ℕ) (hwpos : 0 < w) (hsmall : 6 * w < n K)
    (hPX : Q12 n K ∣ X)
    (hXbound : X < (4 * n K) * Q12 n K)
    (hX : X = r + (2 * n K) * v) (hv : Even v)
    (hrlt : r < 2 * n K)
    (hrne : r ≠ n K) (hdist : r.dist (n K) < 2 * w)
    (hfirst :
      let a := 3 * w
      let W := a + 1 + a
      (5184 : ℝ) * q ^ 2 *
        (c⁻¹ * (1 - c⁻¹)⁻¹) * W ^ 4 < n K)
    (hsecond :
      let a := 3 * w
      let W := a + 1 + a
      (5184 : ℝ) * q ^ 2 * (1 - c⁻¹)⁻¹ < W ^ 5)
    (hcaps :
      let a := 3 * w
      let W := a + 1 + a
      let P := Q12 n K
      let Bval := n K * W ^ 8
      let Qpos := 8 * q * W
      ∀ X G,
        X < (4 * n K) * P →
        G ≤ K + Qpos →
        (Q0 K G).card ≤ Qpos →
        let H := Q21 n K G Bval a a X q
        (φ⁻¹) ^ w * (2 * Q8 H) < 1 - φ⁻¹ ∧
        (φ⁻¹) ^ w * (2 * Q8 H) *
          (2 * Q10 Tconj H) <
          (((qden : ℕ) : ℝ)⁻¹) ^ 2) :
    False := by
  classical
  let a := 3 * w
  let W := a + 1 + a
  let P := Q12 n K
  let Bval := n K * W ^ 8
  let Qpos := 8 * q * W
  let η : ℝ := 1 - φ⁻¹
  have hapos : 0 < a := by dsimp [a]; omega
  have hWpos : 0 < W := by dsimp [W]; omega
  have hηpos : 0 < η := by
    dsimp [η]
    exact sub_pos.mpr (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)
  have haN : a < n K := by dsimp [a]; omega
  have hWr : a < r := by
    rcases lt_or_gt_of_ne hrne with hrn | hnr
    · rw [Nat.dist_eq_sub_of_le hrn.le] at hdist
      dsimp [a]
      omega
    · dsimp [a]
      omega
  have hrW : r + a < 2 * n K := by
    rcases lt_or_gt_of_ne hrne with hrn | hnr
    · dsimp [a]
      omega
    · rw [Nat.dist_eq_sub_of_le_right hnr.le] at hdist
      dsimp [a]
      omega
  have hrUpper : r ≤ n K + a := by
    rcases le_total r (n K) with hrn | hnr
    · omega
    · rw [Nat.dist_eq_sub_of_le_right hnr] at hdist
      dsimp [a]
      omega
  have hsRWindow : n K + a - r < a + 1 + a := by
    rcases le_total r (n K) with hrn | hnr
    · rw [show n K + a - r = a + (n K - r) by omega]
      rw [Nat.dist_eq_sub_of_le hrn] at hdist
      dsimp [a]
      omega
    · have : n K + a - r ≤ a := by omega
      omega
  obtain ⟨G, hKG, hBG, hvalues, hGbound, hdBound⟩ :=
    Q180
      n hpos hmono c hc hratio q hq K W hWpos
  let d := (Q0 K G).card
  have hBvalPos : 0 < Bval := by
    dsimp [Bval]
    exact mul_pos (hpos K) (pow_pos hWpos _)
  have hsimple := Q109
    c hc q W (n K) hqpos hWpos (hpos K)
      (by simpa [a, W] using hfirst)
      (by simpa [a, W] using hsecond)
  have hdensity := Q135
    n hpos c hc q K G W d hWpos
      (by simpa [d, Qpos] using hdBound)
      (by simpa [Bval] using hBG)
      (by simpa [Bval, Qpos] using hsimple)
  have hcap := hcaps X G
    (by simpa [P] using hXbound)
    (by simpa [Qpos] using hGbound)
    (by simpa [Qpos, d] using hdBound)
  have htwoB : 2 * n K ≤ Bval := by
    have hWge : 2 ≤ W := by dsimp [W, a]; omega
    have hWtwo : 2 ≤ W ^ 8 :=
      (show 2 ≤ 2 ^ 8 by norm_num).trans (Nat.pow_le_pow_left hWge 8)
    dsimp [Bval]
    simpa [mul_comm] using Nat.mul_le_mul_left (n K) hWtwo
  by_cases hdouble : ∃ j, K < j ∧ n j = 2 * n K
  · obtain ⟨j, hKj, hj⟩ := hdouble
    have hjG : j < G := by
      apply (hmono.lt_iff_lt).mp
      rw [hj]
      exact htwoB.trans_lt hBG
    let Block : Finset ℕ := {K, j}
    have hKB : K ∈ Block := by simp [Block]
    have hBlockUpper : ∀ k ∈ Block, k < G := by
      intro k hk
      simp only [Block, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hKG
      · exact hjG
    have hnoOutside : ∀ l, K < l → l < G → l ∉ Block →
        n l ≠ 2 * n K := by
      intro l hKl hlG hlB hl
      have hlj : l = j := hmono.injective (hl.trans hj.symm)
      apply hlB
      simp [Block, hlj]
    obtain ⟨L, Bword, J, hspan, hBword, hLbound, hJbound,
        hpreChain, hblockChain, hpostChain⟩ :=
      Q151
        (n K) 2 a X r v (hpos K) (by omega) haN hX hv
          hWr hrW hrne (by dsimp [a]; omega)
    have hcoeff (m : ℕ) :
        Q4 n Block m =
          Q26 (n K) 2 m := by
      exact Q172
        n K j m hKj hj
    have hLw : w ≤ L := by
      dsimp [a] at hLbound
      omega
    have hJw : w ≤ J := by
      dsimp [a] at hJbound
      omega
    have hpostPow : (φ⁻¹ : ℝ) ^ (Bword + J) ≤ φ⁻¹ ^ w :=
      Q255 (by omega)
    have hprePow : (φ⁻¹ : ℝ) ^ L ≤ φ⁻¹ ^ w :=
      Q255 hLw
    have htailNonneg : 0 ≤ 2 * Q8
        (Q21 n K G Bval a a X q) := by
      have := Q34
        (Q21 n K G Bval a a X q)
      positivity
    have hconjNonneg : 0 ≤ 2 * Q10 Tconj
        (Q21 n K G Bval a a X q) := by
      have := Q36 Tconj
        (Q21 n K G Bval a a X q)
      positivity
    apply Q86
      n hpos hmono c hc hratio qden hqden T Tconj hsum htotal
        q hq K G Bval a X r v Block L Bword J η hKG hBvalPos
        hvalues haN hX hv hrUpper hsRWindow hKB hBlockUpper hnoOutside
        hPX (Q374 n K j hj)
        (by dsimp [W, a]; omega)
    · intro s hs
      simpa [hcoeff] using hpreChain s hs
    · simpa [hcoeff, η] using hblockChain
    · intro s hs
      simpa [hcoeff] using hpostChain s hs
    · simpa [W, d] using hdensity
    · dsimp only
      calc
        (φ⁻¹) ^ (Bword + J) *
            (2 * Q8
              (Q21 n K G Bval a a X q)) ≤
          (φ⁻¹) ^ w *
            (2 * Q8
              (Q21 n K G Bval a a X q)) :=
            mul_le_mul_of_nonneg_right hpostPow htailNonneg
        _ < η := by simpa [η, P, W, Bval, Qpos, a, d] using hcap.1
    · dsimp only
      have hfirstNonneg : 0 ≤ (φ⁻¹ : ℝ) ^ L *
          (2 * Q8
            (Q21 n K G Bval a a X q)) := by
        positivity
      calc
        (φ⁻¹) ^ L *
            (2 * Q8
              (Q21 n K G Bval a a X q)) *
            (2 * Q10 Tconj
              (Q21 n K G Bval a a X q)) ≤
          (φ⁻¹) ^ w *
            (2 * Q8
              (Q21 n K G Bval a a X q)) *
            (2 * Q10 Tconj
              (Q21 n K G Bval a a X q)) := by
            gcongr
        _ < (((qden : ℕ) : ℝ)⁻¹) ^ 2 := by
          simpa [P, W, Bval, Qpos, a, d] using hcap.2
  · let Block : Finset ℕ := {K}
    have hKB : K ∈ Block := by simp [Block]
    have hBlockUpper : ∀ k ∈ Block, k < G := by
      intro k hk
      have : k = K := by simpa [Block] using hk
      subst k
      exact hKG
    have hnoOutside : ∀ j, K < j → j < G → j ∉ Block →
        n j ≠ 2 * n K := by
      intro j hKj hjG hjB hj
      exact hdouble ⟨j, hKj, hj⟩
    have hrmod : r = X % (2 * n K) := by
      rw [hX, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrlt]
    have htarget := Q177
      (n K) a a X r (hpos K) haN haN hrmod hWr hrW
    have hcoeff (m : ℕ) :
        Q4 n Block m =
          Q5 (n K) m := by
      exact Q73 n K m
    let z : ℤ := Q4 n Block
          (n K - a + a + X) -
        Q4 n Block (n K - a + a)
    have hz : z ≠ 0 := by
      dsimp [z]
      exact sub_ne_zero.mpr (by simpa [hcoeff] using htarget.2.1)
    have hzone : (1 : ℝ) ≤ |(z : ℝ)| := by
      have hi := Int.one_le_abs hz
      exact_mod_cast hi
    have hηone : η ≤ 1 := by
      dsimp [η]
      have : 0 ≤ (φ⁻¹ : ℝ) := inv_nonneg.mpr Real.goldenRatio_pos.le
      linarith
    have hsingleLower : η ≤
        |∑ s ∈ Finset.range 1,
          ((Q4 n Block
                (n K - a + a + s + X) -
            Q4 n Block
                (n K - a + a + s) : ℤ) : ℝ) *
              (φ⁻¹) ^ s| := by
      simpa [z] using hηone.trans hzone
    have hpostPow : (φ⁻¹ : ℝ) ^ (1 + a) ≤ φ⁻¹ ^ w :=
      Q255 (by dsimp [a]; omega)
    have hprePow : (φ⁻¹ : ℝ) ^ a ≤ φ⁻¹ ^ w :=
      Q255 (by dsimp [a]; omega)
    have htailNonneg : 0 ≤ 2 * Q8
        (Q21 n K G Bval a a X q) := by
      have := Q34
        (Q21 n K G Bval a a X q)
      positivity
    have hconjNonneg : 0 ≤ 2 * Q10 Tconj
        (Q21 n K G Bval a a X q) := by
      have := Q36 Tconj
        (Q21 n K G Bval a a X q)
      positivity
    apply Q86
      n hpos hmono c hc hratio qden hqden T Tconj hsum htotal
        q hq K G Bval a X r v Block a 1 a η hKG hBvalPos
        hvalues haN hX hv hrUpper hsRWindow hKB hBlockUpper hnoOutside
        hPX (Q343 n K) (by rfl)
    · intro s hs
      simpa [hcoeff] using htarget.1 s hs
    · exact hsingleLower
    · intro s hs
      simpa [hcoeff] using htarget.2.2 s hs
    · simpa [W, d] using hdensity
    · dsimp only
      calc
        (φ⁻¹) ^ (1 + a) *
            (2 * Q8
              (Q21 n K G Bval a a X q)) ≤
          (φ⁻¹) ^ w *
            (2 * Q8
              (Q21 n K G Bval a a X q)) :=
            mul_le_mul_of_nonneg_right hpostPow htailNonneg
        _ < η := by simpa [η, P, W, Bval, Qpos, a, d] using hcap.1
    · dsimp only
      calc
        (φ⁻¹) ^ a *
            (2 * Q8
              (Q21 n K G Bval a a X q)) *
            (2 * Q10 Tconj
              (Q21 n K G Bval a a X q)) ≤
          (φ⁻¹) ^ w *
            (2 * Q8
              (Q21 n K G Bval a a X q)) *
            (2 * Q10 Tconj
              (Q21 n K G Bval a a X q)) := by
            gcongr
        _ < (((qden : ℕ) : ℝ)⁻¹) ^ 2 := by
          simpa [P, W, Bval, Qpos, a, d] using hcap.2
end OMAH1Research
namespace OMAH1Research
open Filter Topology Real goldenRatio
private lemma Q253 (q w : ℕ) :
    Q3 q (3 * w) + 1 ≤
      (60000 * (q + 5) ^ 5 + 1) * 4 ^ 40 * (w + 1) ^ 40 := by
  calc
    Q3 q (3 * w) + 1 ≤
        (60000 * (q + 5) ^ 5 + 1) * (3 * w + 1) ^ 40 :=
      Q98 q (3 * w)
    _ ≤ (60000 * (q + 5) ^ 5 + 1) *
        (4 * (w + 1)) ^ 40 := by gcongr; omega
    _ = (60000 * (q + 5) ^ 5 + 1) * 4 ^ 40 *
        (w + 1) ^ 40 := by rw [mul_pow]; ring
theorem Q355 (q : ℕ) :
    Tendsto (fun w : ℕ =>
      (φ⁻¹) ^ w *
        (2 * Q8 (Q3 q (3 * w))))
      atTop (𝓝 0) := by
  let r : ℝ := φ⁻¹
  let A : ℝ := ((60000 * (q + 5) ^ 5 + 1) * 4 ^ 40 : ℕ)
  let C : ℝ := 2 * Q13 * A * r⁻¹
  let g : ℕ → ℝ := fun w =>
    C * ((w + 1 : ℕ) : ℝ) ^ 40 * r ^ (w + 1)
  have hrpos : 0 < r := by dsimp [r]; exact inv_pos.mpr Real.goldenRatio_pos
  have hr0 : 0 ≤ r := hrpos.le
  have hr1 : r < 1 := by
    dsimp [r]
    exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hg : Tendsto g atTop (𝓝 0) := by
    have hbase := tendsto_pow_const_mul_const_pow_of_lt_one 40 hr0 hr1
    have hshift := hbase.comp (Filter.tendsto_add_atTop_nat 1)
    have hconst := hshift.const_mul C
    simpa [g, mul_assoc] using hconst
  apply squeeze_zero
  · intro w
    have ht := Q34 (Q3 q (3 * w))
    positivity
  · intro w
    have hcap := Q93
      (Q3 q (3 * w))
    have hnat := Q253 q w
    have hcast :
        ((Q3 q (3 * w) : ℕ) : ℝ) + 1 ≤
          A * ((w + 1 : ℕ) : ℝ) ^ 40 := by
      dsimp [A]
      exact_mod_cast hnat
    have hlinear : Q8 (Q3 q (3 * w)) ≤
        Q13 * A * ((w + 1 : ℕ) : ℝ) ^ 40 := by
      calc
        _ ≤ Q13 *
            (((Q3 q (3 * w) : ℕ) : ℝ) + 1) := hcap
        _ ≤ Q13 *
            (A * ((w + 1 : ℕ) : ℝ) ^ 40) :=
          mul_le_mul_of_nonneg_left hcast Q63
        _ = Q13 * A *
            ((w + 1 : ℕ) : ℝ) ^ 40 := by ring
    have hrpow : 0 ≤ r ^ w := pow_nonneg hr0 _
    calc
      r ^ w * (2 * Q8 (Q3 q (3 * w))) ≤
        r ^ w * (2 * (Q13 * A *
          ((w + 1 : ℕ) : ℝ) ^ 40)) := by gcongr
      _ = C * ((w + 1 : ℕ) : ℝ) ^ 40 * r ^ (w + 1) := by
        dsimp [C]
        rw [pow_succ]
        field_simp [hrpos.ne']; ring
  · exact hg
theorem Q329 (q : ℕ) (T : ℝ) :
    Tendsto (fun w : ℕ =>
      (φ⁻¹) ^ w *
        (2 * Q8 (Q3 q (3 * w))) *
        (2 * Q10 T
          (Q3 q (3 * w))))
      atTop (𝓝 0) := by
  let r : ℝ := φ⁻¹
  let A : ℝ := ((60000 * (q + 5) ^ 5 + 1) * 4 ^ 40 : ℕ)
  let C : ℝ := 4 * Q13 *
    Q19 T * A ^ 2 * r⁻¹
  let g : ℕ → ℝ := fun w =>
    C * ((w + 1 : ℕ) : ℝ) ^ 80 * r ^ (w + 1)
  have hrpos : 0 < r := by dsimp [r]; exact inv_pos.mpr Real.goldenRatio_pos
  have hr0 : 0 ≤ r := hrpos.le
  have hr1 : r < 1 := by
    dsimp [r]
    exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hg : Tendsto g atTop (𝓝 0) := by
    have hbase := tendsto_pow_const_mul_const_pow_of_lt_one 80 hr0 hr1
    have hshift := hbase.comp (Filter.tendsto_add_atTop_nat 1)
    have hconst := hshift.const_mul C
    simpa [g, mul_assoc] using hconst
  apply squeeze_zero
  · intro w
    have ht := Q34 (Q3 q (3 * w))
    have hc := Q36 T
      (Q3 q (3 * w))
    positivity
  · intro w
    have ht := Q93
      (Q3 q (3 * w))
    have hc := Q170 T
      (Q3 q (3 * w))
    have hnat := Q253 q w
    have hcast :
        ((Q3 q (3 * w) : ℕ) : ℝ) + 1 ≤
          A * ((w + 1 : ℕ) : ℝ) ^ 40 := by
      dsimp [A]
      exact_mod_cast hnat
    have ht' : Q8 (Q3 q (3 * w)) ≤
        Q13 * A * ((w + 1 : ℕ) : ℝ) ^ 40 := by
      calc
        _ ≤ Q13 *
            (((Q3 q (3 * w) : ℕ) : ℝ) + 1) := ht
        _ ≤ Q13 *
            (A * ((w + 1 : ℕ) : ℝ) ^ 40) :=
          mul_le_mul_of_nonneg_left hcast Q63
        _ = _ := by ring
    have hc' : Q10 T
          (Q3 q (3 * w)) ≤
        Q19 T * A *
          ((w + 1 : ℕ) : ℝ) ^ 40 := by
      calc
        _ ≤ Q19 T *
            (((Q3 q (3 * w) : ℕ) : ℝ) + 1) := hc
        _ ≤ Q19 T *
            (A * ((w + 1 : ℕ) : ℝ) ^ 40) :=
          mul_le_mul_of_nonneg_left hcast
            (Q101 T)
        _ = _ := by ring
    have ht0 := Q34 (Q3 q (3 * w))
    have hc0 := Q36 T
      (Q3 q (3 * w))
    have hAt : 0 ≤ Q13 * A *
        ((w + 1 : ℕ) : ℝ) ^ 40 := ht0.trans ht'
    have hAc : 0 ≤ Q19 T * A *
        ((w + 1 : ℕ) : ℝ) ^ 40 := hc0.trans hc'
    calc
      r ^ w * (2 * Q8 (Q3 q (3 * w))) *
          (2 * Q10 T
            (Q3 q (3 * w))) ≤
        r ^ w * (2 * (Q13 * A *
          ((w + 1 : ℕ) : ℝ) ^ 40)) *
          (2 * (Q19 T * A *
            ((w + 1 : ℕ) : ℝ) ^ 40)) := by gcongr
      _ = C * ((w + 1 : ℕ) : ℝ) ^ 80 * r ^ (w + 1) := by
        dsimp [C]
        rw [pow_succ]
        field_simp [hrpos.ne']; ring
  · exact hg
theorem Q267
    (c : ℝ) (hc : 1 < c) (q : ℕ) :
    ∀ᶠ w : ℕ in atTop,
      let a := 3 * w
      let W := a + 1 + a
      (5184 : ℝ) * q ^ 2 *
          (c⁻¹ * (1 - c⁻¹)⁻¹) * W ^ 4 < (w : ℝ) ^ 8 ∧
        (5184 : ℝ) * q ^ 2 * (1 - c⁻¹)⁻¹ < (W : ℝ) ^ 5 := by
  have hinvpos : 0 < c⁻¹ := inv_pos.mpr (lt_trans zero_lt_one hc)
  have hden : 0 < 1 - c⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hc)
  let A : ℝ := (5184 : ℝ) * q ^ 2 * (c⁻¹ * (1 - c⁻¹)⁻¹)
  let B : ℝ := (5184 : ℝ) * q ^ 2 * (1 - c⁻¹)⁻¹
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hp4 : Tendsto (fun w : ℕ => (w : ℝ) ^ 4) atTop atTop :=
    (Filter.tendsto_pow_atTop (α := ℝ) (by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hp5 : Tendsto (fun w : ℕ => (w : ℝ) ^ 5) atTop atTop :=
    (Filter.tendsto_pow_atTop (α := ℝ) (by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop 1,
    hp4.eventually_gt_atTop (7 ^ 4 * A),
    hp5.eventually_gt_atTop B] with w hw h4 h5
  have hW : 3 * w + 1 + 3 * w ≤ 7 * w := by omega
  have hw4 : 0 < (w : ℝ) ^ 4 := by positivity
  dsimp only
  constructor
  · have hstrict := mul_lt_mul_of_pos_right h4 hw4
    calc
      A * (((3 * w + 1 + 3 * w : ℕ) : ℝ) ^ 4) ≤
          A * ((7 * (w : ℝ)) ^ 4) := by
            gcongr
            exact_mod_cast hW
      _ = (7 ^ 4 * A) * (w : ℝ) ^ 4 := by ring
      _ < (w : ℝ) ^ 4 * (w : ℝ) ^ 4 := hstrict
      _ = (w : ℝ) ^ 8 := by ring
  · calc
      B < (w : ℝ) ^ 5 := h5
      _ ≤ (((3 * w + 1 + 3 * w : ℕ) : ℝ) ^ 5) := by
        gcongr
        omega
end OMAH1Research
namespace OMAH1Research
open Filter Topology Real goldenRatio
set_option maxHeartbeats 1200000 in
theorem Q220
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (qden : ℕ) (hqden : 0 < qden) (T Tconj : ℝ)
    (hsum : HasSum (fun m : ℕ =>
      (Q1 n m : ℝ) * (φ⁻¹) ^ m) T)
    (htotal : InScaledGoldenPair qden T Tconj)
    (q : ℕ) (hqpos : 0 < q) (hq : (2 : ℝ) ≤ c ^ q) :
    ∀ᶠ K : ℕ in atTop,
      2 * Q55 n K ≤
        (4 * n K).gcd (Q12 n K) := by
  let ε : ℝ := (((qden : ℕ) : ℝ)⁻¹) ^ 2
  let η : ℝ := 1 - φ⁻¹
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hη : 0 < η := by
    dsimp [η]
    exact sub_pos.mpr (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)
  have hevent : ∀ᶠ w : ℕ in atTop,
      2 ≤ w ∧
      (let a := 3 * w
       let W := a + 1 + a
       (5184 : ℝ) * q ^ 2 *
            (c⁻¹ * (1 - c⁻¹)⁻¹) * W ^ 4 < (w : ℝ) ^ 8 ∧
         (5184 : ℝ) * q ^ 2 * (1 - c⁻¹)⁻¹ < (W : ℝ) ^ 5) ∧
      ((φ⁻¹) ^ w *
          (2 * Q8
            (Q3 q (3 * w))) < η ∧
       (φ⁻¹) ^ w *
          (2 * Q8
            (Q3 q (3 * w))) *
          (2 * Q10 Tconj
            (Q3 q (3 * w))) < ε) := by
    exact (eventually_ge_atTop 2).and
      ((Q267 c hc q).and
        (((Q355 q).eventually
          (gt_mem_nhds hη)).and
         ((Q329 q Tconj).eventually
          (gt_mem_nhds hε))))
  have hroot := Q147 n hmono
  filter_upwards [hroot.eventually hevent] with K hK
  let w := Q55 n K
  change 2 * w ≤ (4 * n K).gcd (Q12 n K)
  by_contra hgnot
  have hgsmall : (4 * n K).gcd (Q12 n K) < 2 * w := by omega
  have hw : 2 ≤ w := hK.1
  have hdensity := hK.2.1
  have hnorm := hK.2.2
  have hlow : w ^ 8 ≤ n K := Q171 n K
  have hupp : n K ≤ (w + 1) ^ 8 :=
    (Q122 n K).le
  have h6cube : 6 ≤ w ^ 3 := by
    calc
      6 ≤ 2 ^ 3 := by norm_num
      _ ≤ w ^ 3 := Nat.pow_le_pow_left hw 3
  have h6four : 6 * w ≤ w ^ 4 := by
    calc
      6 * w ≤ w ^ 3 * w := Nat.mul_le_mul_right w h6cube
      _ = w ^ 4 := by ring
  have hfourEight : w ^ 4 < w ^ 8 :=
    Nat.pow_lt_pow_right (by omega) (by norm_num)
  have hsmall : 6 * w < n K :=
    (h6four.trans_lt hfourEight).trans_le hlow
  have hgltN : (4 * n K).gcd (Q12 n K) < n K :=
    hgsmall.trans (by omega)
  obtain ⟨X, r, v, hPX, hXbound, hX, hv, _hrpos, hrlt, hrne,
      hdistle⟩ :=
    Q203
      (Q12 n K) (n K) (hpos K) hgltN
  apply Q202
    n hpos hmono c hc hratio qden hqden T Tconj hsum htotal
      q hqpos hq K w X r v (by omega) hsmall hPX hXbound hX hv
      hrlt hrne (hdistle.trans_lt hgsmall)
  · dsimp only
    exact hdensity.1.trans_le (by exact_mod_cast hlow)
  · exact hdensity.2
  · let a := 3 * w
    let W := a + 1 + a
    let P := Q12 n K
    let Bval := n K * W ^ 8
    let Qpos := 8 * q * W
    dsimp only
    intro X' G hX' hG hdG
    let H := Q21 n K G Bval a a X' q
    have hHupper : H ≤ Q59 n K a q := by
      exact Q92
        n hpos K a q X' G (by dsimp [a]; omega)
          (by simpa [P] using hX')
          (by simpa [Qpos, W] using hG)
          (by simpa [Qpos, W] using hdG)
    have huppA : n K ≤ (a + 1) ^ 8 := by
      have hwa : w + 1 ≤ a + 1 := by dsimp [a]; omega
      exact hupp.trans (Nat.pow_le_pow_left hwa 8)
    have hUpperWindow : Q59 n K a q ≤
        Q3 q a :=
      Q125
        n hpos hmono K a q huppA
    let HB := Q3 q (3 * w)
    have hHH : H ≤ HB := by
      simpa [HB, a] using hHupper.trans hUpperWindow
    have ht : Q8 H ≤ Q8 HB :=
      Q332 hHH
    have hcj : Q10 Tconj H ≤
        Q10 Tconj HB :=
      Q251 Tconj hHH
    have ht2 : 2 * Q8 H ≤ 2 * Q8 HB :=
      mul_le_mul_of_nonneg_left ht (by norm_num)
    have hc2 : 2 * Q10 Tconj H ≤
        2 * Q10 Tconj HB :=
      mul_le_mul_of_nonneg_left hcj (by norm_num)
    have hpow : 0 ≤ (φ⁻¹ : ℝ) ^ w := by positivity
    have htailH :
        (φ⁻¹) ^ w * (2 * Q8 H) ≤
          (φ⁻¹) ^ w * (2 * Q8 HB) :=
      mul_le_mul_of_nonneg_left ht2 hpow
    constructor
    · exact htailH.trans_lt (by simpa [η, HB] using hnorm.1)
    · have hconjH : 0 ≤ 2 * Q10 Tconj H := by
        exact mul_nonneg (by norm_num) (Q36 Tconj H)
      have htailHB : 0 ≤
          (φ⁻¹) ^ w * (2 * Q8 HB) := by
        exact mul_nonneg hpow
          (mul_nonneg (by norm_num) (Q34 HB))
      calc
        (φ⁻¹) ^ w * (2 * Q8 H) *
            (2 * Q10 Tconj H) ≤
          (φ⁻¹) ^ w * (2 * Q8 HB) *
            (2 * Q10 Tconj H) :=
              mul_le_mul_of_nonneg_right htailH hconjH
        _ ≤ (φ⁻¹) ^ w * (2 * Q8 HB) *
            (2 * Q10 Tconj HB) :=
              mul_le_mul_of_nonneg_left hc2 htailHB
        _ < ε := by simpa [HB] using hnorm.2
end OMAH1Research
namespace OMAH1Research
theorem Q359
    (g A W : ℕ) (hg : 0 < g) :
    ((Finset.range W).filter fun s => g ∣ A + s).card ≤ W / g + 1 := by
  classical
  let S := (Finset.range W).filter fun s => g ∣ A + s
  let f : ℕ → ℕ := fun s => s / g
  have hmap : Set.MapsTo f (S : Set ℕ) (Finset.range (W / g + 1) : Set ℕ) := by
    intro s hs
    have hsW : s < W := Finset.mem_range.mp (Finset.mem_filter.mp hs).1
    apply Finset.mem_range.mpr
    change s / g < W / g + 1
    have hdiv : s / g ≤ W / g :=
      Nat.div_le_div_right (Nat.le_of_lt hsW)
    exact Nat.lt_succ_of_le hdiv
  have hinj : Set.InjOn f (S : Set ℕ) := by
    intro s hs t ht heq
    have hsD : g ∣ A + s := (Finset.mem_filter.mp hs).2
    have htD : g ∣ A + t := (Finset.mem_filter.mp ht).2
    rcases le_total s t with hst | hts
    · have hdiffD : g ∣ t - s := by
        have hsub : (A + t) - (A + s) = t - s := by omega
        rw [← hsub]
        exact Nat.dvd_sub htD hsD
      have hsmod : s % g < g := Nat.mod_lt s hg
      have htmod : t % g < g := Nat.mod_lt t hg
      have hsdecomp := Nat.mod_add_div s g
      have htdecomp := Nat.mod_add_div t g
      have hdiffLt : t - s < g := by
        dsimp [f] at heq
        rw [heq] at hsdecomp
        omega
      have hzero := Nat.eq_zero_of_dvd_of_lt hdiffD hdiffLt
      omega
    · have hdiffD : g ∣ s - t := by
        have hsub : (A + s) - (A + t) = s - t := by omega
        rw [← hsub]
        exact Nat.dvd_sub hsD htD
      have hsmod : s % g < g := Nat.mod_lt s hg
      have htmod : t % g < g := Nat.mod_lt t hg
      have hsdecomp := Nat.mod_add_div s g
      have htdecomp := Nat.mod_add_div t g
      have hdiffLt : s - t < g := by
        dsimp [f] at heq
        rw [heq] at hsdecomp
        omega
      have hzero := Nat.eq_zero_of_dvd_of_lt hdiffD hdiffLt
      omega
  have hc := Finset.card_le_card_of_injOn f hmap hinj
  simpa [S] using hc
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
theorem Q370
    (m p A W R : ℕ) (hm : 0 < m) :
    let g := m.gcd p
    (∑ _s ∈ (Finset.range W).filter fun s => g ∣ A + s,
      (R / (m / g) + 1)) ≤
      (W / g + 1) * (R / (m / g) + 1) := by
  let g := m.gcd p
  have hg : 0 < g := Nat.gcd_pos_of_pos_left p hm
  have hc := Q359 g A W hg
  calc
    (∑ _s ∈ (Finset.range W).filter fun s => g ∣ A + s,
      (R / (m / g) + 1)) =
        ((Finset.range W).filter fun s => g ∣ A + s).card *
          (R / (m / g) + 1) := by simp
    _ ≤ (W / g + 1) * (R / (m / g) + 1) :=
      Nat.mul_le_mul_right _ hc
theorem Q235
    (m p A W R : ℕ) (hm : 0 < m)
    (hgW : m.gcd p ≤ W) :
    ((∑ _s ∈ (Finset.range W).filter fun s => m.gcd p ∣ A + s,
      (R / (m / m.gcd p) + 1) : ℕ) : ℝ) ≤
      2 * (R : ℝ) * W / m + 2 * (W : ℝ) / m.gcd p := by
  let g := m.gcd p
  let q := m / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left p hm
  have hgm : g ∣ m := Nat.gcd_dvd_left m p
  have hq : 0 < q := Nat.div_pos (Nat.gcd_le_left p hm) hg
  have hsumNat := Q370 m p A W R hm
  have hsumCast :
      ((∑ s ∈ (Finset.range W).filter fun s => g ∣ A + s,
        (R / q + 1) : ℕ) : ℝ) ≤
      ((W / g + 1) * (R / q + 1) : ℕ) := by
    exact_mod_cast hsumNat
  have hcountCast : ((W / g + 1 : ℕ) : ℝ) ≤
      (W : ℝ) / g + 1 := by
    push_cast
    gcongr
    exact Nat.cast_div_le
  have htermCast : ((R / q + 1 : ℕ) : ℝ) ≤
      (R : ℝ) * g / m + 1 := by
    push_cast
    have hdiv : ((R / q : ℕ) : ℝ) ≤ (R : ℝ) / q := Nat.cast_div_le
    have hqcast : (q : ℝ) = (m : ℝ) / g := by
      dsimp [q, g]
      rw [Nat.cast_div hgm]
      exact_mod_cast (Nat.ne_of_gt hg)
    rw [hqcast] at hdiv
    have hmg : (0 : ℝ) < g := by exact_mod_cast hg
    have hmm : (0 : ℝ) < m := by exact_mod_cast hm
    calc
      ((R / q : ℕ) : ℝ) + 1 ≤ (R : ℝ) / ((m : ℝ) / g) + 1 := by
        linarith
      _ = (R : ℝ) * g / m + 1 := by field_simp
  have hWg : (1 : ℝ) ≤ (W : ℝ) / g := by
    have hgWreal : (g : ℝ) ≤ W := by exact_mod_cast hgW
    have hgreal : (0 : ℝ) < g := by exact_mod_cast hg
    exact (le_div_iff₀ hgreal).mpr (by simpa using hgWreal)
  have hcountTwo : (W : ℝ) / g + 1 ≤ 2 * (W : ℝ) / g := by
    calc
      (W : ℝ) / g + 1 ≤ (W : ℝ) / g + (W : ℝ) / g := by
        simpa using add_le_add_left hWg ((W : ℝ) / g)
      _ = 2 * (W : ℝ) / g := by ring
  have htermNonneg : 0 ≤ (R : ℝ) * g / m + 1 := by positivity
  have hcountNonneg : 0 ≤ ((W / g + 1 : ℕ) : ℝ) := by positivity
  calc
    ((∑ _s ∈ (Finset.range W).filter fun s => m.gcd p ∣ A + s,
      (R / (m / m.gcd p) + 1) : ℕ) : ℝ) ≤
        ((W / g + 1) * (R / q + 1) : ℕ) := by
          simpa [g, q] using hsumCast
    _ = ((W / g + 1 : ℕ) : ℝ) * ((R / q + 1 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((W / g + 1 : ℕ) : ℝ) *
        ((R : ℝ) * g / m + 1) :=
      mul_le_mul_of_nonneg_left htermCast hcountNonneg
    _ ≤ ((W : ℝ) / g + 1) * ((R : ℝ) * g / m + 1) :=
      mul_le_mul_of_nonneg_right hcountCast htermNonneg
    _ ≤ (2 * (W : ℝ) / g) * ((R : ℝ) * g / m + 1) :=
      mul_le_mul_of_nonneg_right hcountTwo htermNonneg
    _ = 2 * (R : ℝ) * W / m + 2 * (W : ℝ) / g := by
      have hgreal : (g : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hg)
      have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
      field_simp [hgreal, hmreal]
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
def Q50
    (n : ℕ → ℕ) (K H W A X p : ℕ) : Finset ((ℕ × ℕ) × Bool) :=
  (Q18 n K H W A X p).filter fun u =>
    (n u.1.1).gcd p ≤ W
theorem Q264
    (n : ℕ → ℕ) (K H W A X p R : ℕ) :
    (∑ u ∈ Q50 n K H W A X p,
      (R / (Q2 n u /
        (Q2 n u).gcd p) + 1)) =
    ∑ j ∈ Q0 K H,
      ((∑ _s ∈ (Finset.range W).filter fun s =>
          (n j).gcd p ∣ A + s,
          (R / (n j / (n j).gcd p) + 1)) +
       (∑ _s ∈ (Finset.range W).filter fun s =>
          (n j).gcd p ∣ A + X + s,
          (R / (n j / (n j).gcd p) + 1))) *
        (if (n j).gcd p ≤ W then 1 else 0) := by
  classical
  unfold Q50
  rw [Finset.sum_filter]
  unfold Q18
  rw [Finset.sum_filter]
  unfold Q56
  let F : ((ℕ × ℕ) × Bool) → ℕ := fun u =>
    if (Q2 n u).gcd p ∣ Q16 A X u then
      if (n u.1.1).gcd p ≤ W then
        R / (Q2 n u / (Q2 n u).gcd p) + 1
      else 0
    else 0
  change (∑ u ∈ ((Q0 K H).product
      (Finset.range W)).product Finset.univ, F u) = _
  calc
    (∑ u ∈ ((Q0 K H).product
        (Finset.range W)).product Finset.univ, F u) =
      ∑ js ∈ (Q0 K H).product (Finset.range W),
        ∑ b ∈ (Finset.univ : Finset Bool), F (js, b) :=
          Finset.sum_product _ _ F
    _ = ∑ j ∈ Q0 K H,
        ∑ s ∈ Finset.range W,
          ∑ b ∈ (Finset.univ : Finset Bool), F ((j, s), b) :=
      Finset.sum_product _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hg : (n j).gcd p ≤ W
      · simp [F, hg, Q2, Q16,
          add_assoc, add_comm, add_left_comm]
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [← Finset.sum_filter]
          simp
        · rw [← Finset.sum_filter]
          simp
      · simp [F, hg, Q2]
theorem Q335
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (K H W A X p R : ℕ) :
    ((∑ u ∈ Q50 n K H W A X p,
      (R / (Q2 n u /
        (Q2 n u).gcd p) + 1) : ℕ) : ℝ) ≤
      4 * (R : ℝ) * W *
          (∑ j ∈ Q0 K H, ((n j : ℝ)⁻¹)) +
        4 * W * (Q0 K H).card := by
  rw [Q264]
  push_cast
  calc
    _ ≤ ∑ j ∈ Q0 K H,
        (4 * (R : ℝ) * W / n j + 4 * W) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hgW : (n j).gcd p ≤ W
      · have hleft := Q235
          (n j) p A W R (hpos j) hgW
        have hright := Q235
          (n j) p (A + X) W R (hpos j) hgW
        have hgpos : 0 < (n j).gcd p :=
          Nat.gcd_pos_of_pos_left p (hpos j)
        have hWg : (W : ℝ) / (n j).gcd p ≤ W := by
          have hgOne : (1 : ℝ) ≤ (n j).gcd p := by exact_mod_cast hgpos
          have hWnonneg : (0 : ℝ) ≤ W := by positivity
          exact (div_le_iff₀ (by exact_mod_cast hgpos)).mpr <| by
            nlinarith
        push_cast at hleft hright
        simp only [hgW, if_true, mul_one]
        calc
          _ ≤ (2 * (R : ℝ) * W / n j +
              2 * (W : ℝ) / (n j).gcd p) +
            (2 * (R : ℝ) * W / n j +
              2 * (W : ℝ) / (n j).gcd p) :=
                add_le_add hleft hright
          _ = 4 * (R : ℝ) * W / n j +
              4 * (W : ℝ) / (n j).gcd p := by ring
          _ ≤ 4 * (R : ℝ) * W / n j + 4 * W := by
            have h4 : 4 * (W : ℝ) / (n j).gcd p ≤ 4 * W := by
              calc
                4 * (W : ℝ) / (n j).gcd p =
                    4 * ((W : ℝ) / (n j).gcd p) := by ring
                _ ≤ 4 * W := mul_le_mul_of_nonneg_left hWg (by norm_num)
            exact add_le_add_right h4 _
      · simp [hgW]
        have hnj : (0 : ℝ) < n j := by exact_mod_cast hpos j
        positivity
    _ = 4 * (R : ℝ) * W *
          (∑ j ∈ Q0 K H, ((n j : ℝ)⁻¹)) +
        4 * W * (Q0 K H).card := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp
      ring_nf
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
def Q53 (G H L sR : ℕ) :
    Finset ((ℕ × ℕ) × Bool) :=
  (((Finset.Ico G H).product ({L, sR} : Finset ℕ)).product
    (Finset.univ : Finset Bool))
theorem Q275
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (G H L sR p R : ℕ) (hp : 0 < p) :
    ((∑ u ∈ Q53 G H L sR,
      (R / (Q2 n u /
        (Q2 n u).gcd p) + 1) : ℕ) : ℝ) ≤
      4 * ((R : ℝ) * p *
        (∑ j ∈ Finset.Ico G H, ((n j : ℝ)⁻¹)) +
        (Finset.Ico G H).card) := by
  classical
  let cost : ((ℕ × ℕ) × Bool) → ℕ := fun u =>
    R / (Q2 n u /
      (Q2 n u).gcd p) + 1
  let upper : ℕ → ℕ := fun j => (R * p) / n j + 1
  have hpoint : ∀ u, cost u ≤ upper u.1.1 := by
    intro u
    dsimp [cost, upper]
    rw [Q198 R (Q2 n u) p]
    · apply Nat.add_le_add_right
      apply Nat.div_le_div_right
      exact Nat.mul_le_mul_left R (Nat.gcd_le_right _ hp)
    · exact hpos u.1.1
  have hnat : (∑ u ∈ Q53 G H L sR, cost u) ≤
      4 * ∑ j ∈ Finset.Ico G H, upper j := by
    calc
      (∑ u ∈ Q53 G H L sR, cost u) ≤
          ∑ u ∈ Q53 G H L sR, upper u.1.1 := by
            apply Finset.sum_le_sum
            intro u hu
            exact hpoint u
      _ = ({L, sR} : Finset ℕ).card * 2 *
          ∑ j ∈ Finset.Ico G H, upper j := by
            simp [Q53, Finset.sum_product]
            simp_rw [← mul_assoc]
            rw [← Finset.mul_sum]
      _ ≤ 4 * ∑ j ∈ Finset.Ico G H, upper j := by
        have hc : ({L, sR} : Finset ℕ).card ≤ 2 := by
          simpa using Finset.card_insert_le L ({sR} : Finset ℕ)
        have hc2 : ({L, sR} : Finset ℕ).card * 2 ≤ 4 := by omega
        exact Nat.mul_le_mul_right _ hc2
  have hcast :
      (((∑ u ∈ Q53 G H L sR, cost u) : ℕ) : ℝ) ≤
        (4 * ∑ j ∈ Finset.Ico G H, upper j : ℕ) := by
    exact_mod_cast hnat
  have hsum := Q88
    (Finset.Ico G H) n (fun j hj => hpos j) (R * p)
  dsimp [cost] at hcast
  calc
    ((∑ u ∈ Q53 G H L sR,
      (R / (Q2 n u /
        (Q2 n u).gcd p) + 1) : ℕ) : ℝ) ≤
        ((4 * ∑ j ∈ Finset.Ico G H, upper j : ℕ) : ℝ) := hcast
    _ = 4 * (((∑ j ∈ Finset.Ico G H, upper j) : ℕ) : ℝ) := by
      push_cast
      ring
    _ ≤ 4 * (((R * p : ℕ) : ℝ) *
        (∑ j ∈ Finset.Ico G H, ((n j : ℝ)⁻¹)) +
        (Finset.Ico G H).card) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [upper] using hsum
      · norm_num
    _ = 4 * ((R : ℝ) * p *
        (∑ j ∈ Finset.Ico G H, ((n j : ℝ)⁻¹)) +
        (Finset.Ico G H).card) := by
      push_cast
      ring
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
lemma Q145
    (g A s z : ℕ) (hgp : g ∣ A * 2 ^ s) (hgz : g ∣ A * z)
    (hz : Odd z) :
    g ∣ A := by
  have hcop : (2 ^ s).Coprime z :=
    (Nat.coprime_two_left.mpr hz).pow_left s
  have hgd : g ∣ (A * 2 ^ s).gcd (A * z) := Nat.dvd_gcd hgp hgz
  rw [Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one] at hgd
  exact hgd
end OMAH1Research
namespace OMAH1Research
theorem Q309
    (n R v : ℕ) (hn : 0 < n) (hR : 0 < R) :
    Q26 n R (n + (2 * n) * v) =
      if Even n ∨ Even v then 1 else -1 := by
  unfold Q26
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, mul_one]
    unfold Q5
    by_cases hen : Even n
    · simp only [hen, if_pos, true_or]
      rw [show n + 2 * n * v = n + (2 * n) * v by rfl,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      simp
    · simp only [hen, false_or]
      by_cases hev : Even v
      · obtain ⟨z, hz⟩ := hev
        have hev' : Even v := ⟨z, hz⟩
        have heq : n + 2 * n * v = n + (4 * n) * z := by rw [hz]; ring
        rw [heq, Nat.add_mul_mod_self_left]
        rw [Nat.mod_eq_of_lt (show n < 4 * n by omega)]
        simp [hev']
      · have hov : Odd v := Nat.not_even_iff_odd.mp hev
        obtain ⟨z, hz⟩ := hov
        have heq : n + 2 * n * v = 3 * n + (4 * n) * z := by
          rw [hz]
          ring
        rw [heq, Nat.add_mul_mod_self_left]
        rw [Nat.mod_eq_of_lt (show 3 * n < 4 * n by omega)]
        simp [hev, show 3 * n ≠ n by omega]
  · intro j hj hjne
    apply Q32
    intro hdvd
    have hjpos : 0 < j := Nat.pos_of_ne_zero hjne
    have htwoPow : 2 ∣ 2 ^ j := by
      simpa using Nat.pow_dvd_pow 2 hjpos
    have hfactor : n + (2 * n) * v = n * (1 + 2 * v) := by ring
    have hpowDvd : 2 ^ j ∣ 1 + 2 * v := by
      apply (Nat.mul_dvd_mul_iff_left hn).mp
      rw [hfactor] at hdvd
      exact hdvd
    have htwoOdd : 2 ∣ 1 + 2 * v := htwoPow.trans hpowDvd
    obtain ⟨a, ha⟩ := htwoOdd
    omega
  · intro hnot
    exfalso
    apply hnot
    simp [hR]
theorem Q210
    (n R W v t : ℕ) (hn : 0 < n) (hR : 0 < R)
    (hW : W < n) (ht : t < 2 * W + 1) :
    Q26 n R (n - W + t + (2 * n) * v) =
      if t = W then (if Even n ∨ Even v then 1 else -1) else 0 := by
  by_cases htw : t = W
  · subst t
    rw [show n - W + W + 2 * n * v = n + (2 * n) * v by omega,
      Q309 n R v hn hR]
    simp
  · apply Eq.trans (Q81 n R _ ?_)
      (by simp [htw])
    intro hdvd
    have hnPeriod : n ∣ (2 * n) * v := ⟨2 * v, by ring⟩
    have hdvd' : n ∣ (n - W + t) + (2 * n) * v := by
      simpa [add_assoc] using hdvd
    have hnBase : n ∣ n - W + t :=
      (Nat.dvd_add_iff_left hnPeriod).mpr hdvd'
    exact Q166 n _ (by omega) (by omega)
      (by omega) hnBase
theorem Q130
    (n R w X r v : ℕ) (hn : 0 < n) (hR : 0 < R)
    (hX : X = r + (2 * n) * v)
    (_hrpos : 0 < r) (hrn : r < n)
    (hwr : w < r) (hw : w < n - r) :
    let A := n - r - w
    (0 < A) ∧
    (∀ s < w, Q26 n R (A + s + X) =
      Q26 n R (A + s)) ∧
    Q26 n R (A + w + X) ≠
      Q26 n R (A + w) ∧
    (∀ s < w, Q26 n R (A + w + 1 + s + X) =
      Q26 n R (A + w + 1 + s)) := by
  let A := n - r - w
  have hAeq : A + r + w = n := by dsimp [A]; omega
  have hshift (t : ℕ) (_ht : t < 2 * w + 1) :
      A + t + X = n - w + t + (2 * n) * v := by
    rw [hX]
    omega
  have hlowPos (t : ℕ) : 0 < A + t := by dsimp [A]; omega
  have hlowLt (t : ℕ) (ht : t < 2 * w + 1) : A + t < n := by
    dsimp [A]
    omega
  have hlowZero (t : ℕ) (ht : t < 2 * w + 1) :
      Q26 n R (A + t) = 0 := by
    apply Q81
    exact Nat.not_dvd_of_pos_of_lt (hlowPos t) (hlowLt t ht)
  have hhigh (t : ℕ) (ht : t < 2 * w + 1) :
      Q26 n R (A + t + X) =
        if t = w then (if Even n ∨ Even v then 1 else -1) else 0 := by
    rw [hshift t ht]
    exact Q210
      n R w v t hn hR (by omega) ht
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro s hs
    rw [hhigh s (by omega), hlowZero s (by omega)]
    simp [show s ≠ w by omega]
  · rw [hhigh w (by omega), hlowZero w (by omega)]
    by_cases hpar : Even n ∨ Even v <;> simp [hpar]
  · intro s hs
    let t := w + 1 + s
    have ht : t < 2 * w + 1 := by dsimp [t]; omega
    have htw : t ≠ w := by dsimp [t]; omega
    rw [show n - r - w + w + 1 + s = A + t by
      dsimp [A, t]
      omega]
    rw [hhigh t ht, hlowZero t ht]
    simp [htw]
theorem Q134
    (P n : ℕ) (hn : 0 < n)
    (hodd : Odd ((2 * n) / (2 * n).gcd P))
    (hthree : 3 ≤ (2 * n) / (2 * n).gcd P) :
    let d := (2 * n).gcd P
    ∃ X r v : ℕ,
      P ∣ X ∧ X < (2 * n) * P ∧
      X = r + (2 * n) * v ∧
      0 < r ∧ r < n ∧
      2 * (n - r) = d := by
  let d := (2 * n).gcd P
  let q := (2 * n) / d
  have htwo : 0 < 2 * n := by omega
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.gcd_pos_of_pos_left P htwo
  have hdTwo : d ∣ 2 * n := by dsimp [d]; exact Nat.gcd_dvd_left _ _
  have hdP : d ∣ P := by dsimp [d]; exact Nat.gcd_dvd_right _ _
  have hfac : d * q = 2 * n := by
    dsimp [q]
    exact Nat.mul_div_cancel' hdTwo
  have hqodd : Odd q := by simpa [q, d] using hodd
  have hqthree : 3 ≤ q := by simpa [q, d] using hthree
  have hdEven : Even d := by
    apply Nat.not_odd_iff_even.mp
    intro hdOdd
    have hprodOdd : Odd (d * q) := hdOdd.mul hqodd
    rw [hfac] at hprodOdd
    exact (Nat.not_odd_iff_even.mpr ⟨n, by ring⟩) hprodOdd
  obtain ⟨d0, hd0⟩ := hdEven
  let k := (q - 1) / 2
  have hkpos : 0 < k := by dsimp [k]; omega
  have hklt : k < q := by dsimp [k]; omega
  have hqpos : 0 < q := by omega
  let P' := P / d
  have hPfac : d * P' = P := by
    dsimp [P']
    exact Nat.mul_div_cancel' hdP
  have hcop : P'.Coprime q := by
    have hc := Nat.coprime_div_gcd_div_gcd (m := 2 * n) (n := P) hdpos
    exact hc.symm
  obtain ⟨u, huq, hu⟩ :=
    Nat.exists_mul_mod_eq_of_coprime k hcop (Nat.ne_of_gt hqpos)
  have hkmod : k % q = k := Nat.mod_eq_of_lt hklt
  rw [hkmod] at hu
  let r := d * k
  let X := P * u
  have hrmod : r = X % (2 * n) := by
    dsimp [r, X]
    rw [← hPfac, ← hfac, mul_assoc, Nat.mul_mod_mul_left, hu]
  have hrpos : 0 < r := mul_pos hdpos hkpos
  have hqform : q = 2 * k + 1 := by
    obtain ⟨a, ha⟩ := hqodd
    dsimp [k]
    omega
  have hsum : 2 * r + d = 2 * n := by
    dsimp [r]
    rw [← hfac, hqform]
    ring
  have hrn : r < n := by omega
  let v := X / (2 * n)
  have hdecomp : X = r + (2 * n) * v := by
    have hx := Nat.mod_add_div X (2 * n)
    rw [← hrmod] at hx
    simpa [v] using hx.symm
  have hPpos : 0 < P := by
    by_contra hnot
    have hPzero : P = 0 := by omega
    dsimp [d, q] at hqthree
    simp only [hPzero, Nat.gcd_zero_right] at hqthree
    rw [Nat.div_self htwo] at hqthree
    omega
  have hqle : q ≤ 2 * n := Nat.div_le_self _ _
  have hXbound : X < (2 * n) * P := by
    dsimp [X]
    calc
      P * u < P * q := Nat.mul_lt_mul_of_pos_left huq hPpos
      _ ≤ P * (2 * n) := Nat.mul_le_mul_left P hqle
      _ = (2 * n) * P := by ring
  have hdist : 2 * (n - r) = d := by omega
  exact ⟨X, r, v, ⟨u, rfl⟩, hXbound, hdecomp,
    hrpos, hrn, hdist⟩
end OMAH1Research
namespace OMAH1Research
theorem Q341
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hodd : Odd (a / a.gcd b)) :
    Q15 a ≤ Q15 b := by
  by_contra hnot
  have hlt : Q15 b < Q15 a := by omega
  have htwoG : 2 * b.gcd a ∣ a :=
    (Q104 b a hb ha).mpr hlt
  let g := a.gcd b
  let q := a / g
  have hgpos : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_left b ha
  have hga : g ∣ a := by dsimp [g]; exact Nat.gcd_dvd_left _ _
  have hfac : g * q = a := by
    dsimp [q]
    exact Nat.mul_div_cancel' hga
  obtain ⟨z, hz⟩ := htwoG
  have hqeven : q = 2 * z := by
    have heq : g * q = g * (2 * z) := by
      calc
        g * q = a := hfac
        _ = 2 * b.gcd a * z := hz
        _ = g * (2 * z) := by dsimp [g]; rw [Nat.gcd_comm b a]; ring
    exact Nat.mul_left_cancel hgpos heq
  have : Even q := ⟨z, by rw [hqeven]; ring⟩
  exact (Nat.not_even_iff_odd.mpr (by simpa [q, g] using hodd)) this
theorem Q201
    (P n : ℕ) (hP : 0 < P) (hn : 0 < n)
    (hodd : Odd (Q11 n /
      (Q11 n).gcd P)) :
    Odd ((2 * n) / (2 * n).gcd P) := by
  have hsharpPos : 0 < Q11 n := by
    unfold Q11
    split <;> omega
  have horderSharp : Q15 (Q11 n) ≤
      Q15 P :=
    Q341
      (Q11 n) P hsharpPos hP hodd
  have htwoDvd : 2 * n ∣ Q11 n := by
    unfold Q11
    split_ifs
    · exact dvd_rfl
    · exact ⟨2, by ring⟩
  have horderTwo : Q15 (2 * n) ≤
      Q15 (Q11 n) := by
    have hfac := (Nat.factorization_le_iff_dvd
      (by omega : 2 * n ≠ 0) (Nat.ne_of_gt hsharpPos)).mpr htwoDvd
    exact hfac 2
  apply Q148 (2 * n) P (by omega) hP
  exact horderTwo.trans horderSharp
theorem Q132
    (P n : ℕ) (hP : 0 < P) (hn : 0 < n)
    (hnew : ¬Q11 n ∣ P)
    (hodd : Odd (Q11 n /
      (Q11 n).gcd P)) :
    Odd ((2 * n) / (2 * n).gcd P) ∧
      3 ≤ (2 * n) / (2 * n).gcd P := by
  have hoddTwo := Q201
    P n hP hn hodd
  refine ⟨hoddTwo, ?_⟩
  have hqpos : 0 < (2 * n) / (2 * n).gcd P :=
    Nat.div_pos (Nat.gcd_le_left P (by omega))
      (Nat.gcd_pos_of_pos_left P (by omega))
  have hqne : (2 * n) / (2 * n).gcd P ≠ 1 := by
    intro heq
    have hgEq : (2 * n).gcd P = 2 * n := by
      have hgd : (2 * n).gcd P ∣ 2 * n := Nat.gcd_dvd_left _ _
      have hfac := Nat.mul_div_cancel' hgd
      rw [heq, mul_one] at hfac
      exact hfac
    have htwoP : 2 * n ∣ P := by
      rw [← hgEq]
      exact Nat.gcd_dvd_right _ _
    exact Q187
      P n hn hnew hodd htwoP
  obtain ⟨z, hz⟩ := hoddTwo
  omega
theorem Q307
    (n P : ℕ) :
    (4 * n).gcd P ∣ 2 * (2 * n).gcd P := by
  have hleft : (4 * n).gcd P ∣ 2 * (2 * n) := by
    rw [show 2 * (2 * n) = 4 * n by ring]
    exact Nat.gcd_dvd_left _ _
  have hright : (4 * n).gcd P ∣ 2 * P :=
    dvd_mul_of_dvd_right (Nat.gcd_dvd_right (4 * n) P) 2
  have hg := Nat.dvd_gcd hleft hright
  simpa [Nat.gcd_mul_left, mul_assoc] using hg
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
def Q75
    (q a b c d : ℕ) : Finset ℕ :=
  (Finset.range q).filter fun t =>
    (¬q ∣ b + a * t) ∧ (¬q ∣ d + c * t)
theorem Q152
    (q a b c d : ℕ) (hq : 3 ≤ q)
    (ha : q.gcd a = 1) (hc : q.gcd c = 1) :
    q - 2 ≤ (Q75 q a b c d).card := by
  classical
  let B₁ := (Finset.range q).filter fun t => q ∣ b + a * t
  let B₂ := (Finset.range q).filter fun t => q ∣ d + c * t
  let B := (Finset.range q).filter fun t =>
    q ∣ b + a * t ∨ q ∣ d + c * t
  have hB₁ : B₁.card ≤ 1 := by
    dsimp [B₁]
    exact Q91 b a q (by omega) ha
  have hB₂ : B₂.card ≤ 1 := by
    dsimp [B₂]
    exact Q91 d c q (by omega) hc
  have hBunion : B = B₁ ∪ B₂ := by
    dsimp [B, B₁, B₂]
    rw [← Finset.filter_or]
  have hB : B.card ≤ 2 := by
    rw [hBunion]
    exact (Finset.card_union_le _ _).trans (by omega)
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := Finset.range q)
    (fun t => q ∣ b + a * t ∨ q ∣ d + c * t)
  have hsafe :
      ((Finset.range q).filter fun t =>
        ¬(q ∣ b + a * t ∨ q ∣ d + c * t)) =
        Q75 q a b c d := by
    ext t
    simp [Q75]
  have hpart : B.card + (Q75 q a b c d).card = q := by
    rw [← hsafe]
    simpa [B] using hpartition
  omega
end OMAH1Research
namespace OMAH1Research
theorem Q85
    (m n V : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hV : Q15 m ≤ V) :
    Odd (m / m.gcd ((4 * n) * 2 ^ V)) := by
  have hp : 0 < (4 * n) * 2 ^ V := by positivity
  have horderP : V ≤ Q15 ((4 * n) * 2 ^ V) := by
    unfold Q15
    rw [Nat.factorization_mul (by positivity : 4 * n ≠ 0)
      (by positivity : 2 ^ V ≠ 0), Finsupp.add_apply,
      Nat.factorization_pow]
    simp only [Finsupp.smul_apply, smul_eq_mul, Q114]
    omega
  exact Q148 m ((4 * n) * 2 ^ V)
    hm hp (hV.trans horderP)
def Q254
    (n : ℕ → ℕ) (K H W A X p w : ℕ) :
    Finset ((ℕ × ℕ) × Bool) :=
  (Q18 n K H W A X p).filter fun u =>
    u.1.2 = w
def Q44
    (n : ℕ → ℕ) (K H W A X p w : ℕ) :
    Finset ((ℕ × ℕ) × Bool) :=
  Q18 n K H W A X p \
    Q254 n K H W A X p w
lemma Q389 {g a b : ℕ} (ha : g ∣ a) (hb : g ∣ b) :
    g ∣ a.dist b := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab]
    exact Nat.dvd_sub hb ha
  · rw [Nat.dist_eq_sub_of_le_right hba]
    exact Nat.dvd_sub ha hb
theorem Q136
    (m n D w s X scale v : ℕ)
    (_hn : 0 < n) (hD : w < D) (hs : s < 2 * w + 1)
    (hX : D + X = n * (2 * v + 1))
    (hscale : 0 < scale)
    (hcomp : m.gcd (scale * n) ∣ D - w + s + X)
    (hoff : s ≠ w)
    (hlarge : scale * w < m.gcd (scale * n)) :
    False := by
  let g := m.gcd (scale * n)
  have hgStep : g ∣ scale * n := by
    dsimp [g]
    exact Nat.gcd_dvd_right _ _
  have hgScaleCenter : g ∣ scale * (D + X) := by
    rw [hX, show scale * (n * (2 * v + 1)) =
      (scale * n) * (2 * v + 1) by ring]
    exact dvd_mul_of_dvd_left hgStep _
  have hcomp' : g ∣ D - w + s + X := by simpa [g] using hcomp
  have hgScaleComp : g ∣ scale * (D - w + s + X) :=
    dvd_mul_of_dvd_right hcomp' scale
  have hdiff : (D - w + s + X).dist (D + X) = s.dist w := by
    rcases le_total s w with hsw | hws
    · rw [Nat.dist_eq_sub_of_le (by omega : D - w + s + X ≤ D + X),
        Nat.dist_eq_sub_of_le hsw]
      omega
    · rw [Nat.dist_eq_sub_of_le_right (by omega : D + X ≤ D - w + s + X),
        Nat.dist_eq_sub_of_le_right hws]
      omega
  have hgScaleDist : g ∣ scale * (s.dist w) := by
    have hd := Q389 hgScaleComp hgScaleCenter
    rw [Nat.dist_mul_left, hdiff] at hd
    exact hd
  have hdistPos : 0 < s.dist w := Nat.dist_pos_of_ne hoff
  have hgLe : g ≤ scale * (s.dist w) :=
    Nat.le_of_dvd (mul_pos hscale hdistPos) hgScaleDist
  have hdistLe : s.dist w ≤ w := by
    rcases le_total s w with hsw | hws
    · rw [Nat.dist_eq_sub_of_le hsw]
      omega
    · rw [Nat.dist_eq_sub_of_le_right hws]
      omega
  have : g ≤ scale * w :=
    hgLe.trans (Nat.mul_le_mul_left scale hdistLe)
  dsimp [g] at this
  omega
theorem Q321
    (m n D w s X scale v : ℕ)
    (hn : 0 < n) (hD : w < D) (hs : s < 2 * w + 1)
    (hroot : D + X = n * (2 * v + 1))
    (hscale : 0 < scale) (side : Bool)
    (hcomp : m.gcd (scale * n) ∣
      (if side then D - w + s + X else D - w + s))
    (hoff : s ≠ w)
    (hlarge : scale * w < m.gcd (scale * n)) :
    side = false ∧ ¬m.gcd (scale * n) ∣ D := by
  by_cases hside : side = true
  · subst side
    exfalso
    exact Q136
      m n D w s X scale v hn hD hs hroot hscale hcomp hoff hlarge
  · have hsideFalse : side = false := Bool.eq_false_of_not_eq_true hside
    refine ⟨hsideFalse, ?_⟩
    intro hgD
    let g := m.gcd (scale * n)
    have hcomp' : g ∣ D - w + s := by
      simpa [g, hsideFalse] using hcomp
    have hgDist : g ∣ s.dist w := by
      have hEq : (D - w + s).dist D = s.dist w := by
        rcases le_total s w with hsw | hws
        · rw [Nat.dist_eq_sub_of_le (by omega : D - w + s ≤ D),
            Nat.dist_eq_sub_of_le hsw]
          omega
        · rw [Nat.dist_eq_sub_of_le_right (by omega : D ≤ D - w + s),
            Nat.dist_eq_sub_of_le_right hws]
          omega
      rw [← hEq]
      exact Q389 hcomp' hgD
    have hgLe : g ≤ s.dist w :=
      Nat.le_of_dvd (Nat.dist_pos_of_ne hoff) hgDist
    have hdistLe : s.dist w ≤ w := by
      rcases le_total s w with hsw | hws
      · rw [Nat.dist_eq_sub_of_le hsw]; omega
      · rw [Nat.dist_eq_sub_of_le_right hws]; omega
    have : g ≤ w := hgLe.trans hdistLe
    dsimp [g] at this
    nlinarith
theorem Q185
    (m n D Q w s scale B : ℕ)
    (hn : 0 < n) (hm : n < m) (hD : w < D) (hQ : n = Q * D)
    (hs : s < 2 * w + 1) (hscale : 0 < scale)
    (hcomp : m.gcd (scale * n) ∣ D - w + s)
    (hincompat : ¬m.gcd (scale * n) ∣ D)
    (hsize : 2 * scale * B ^ 2 * w ≤ n) :
    B < m / m.gcd (scale * n) := by
  let g := m.gcd (scale * n)
  let q := m / g
  let E := D - w + s
  have hgpos : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_left (scale * n) (by omega)
  have hgM : g ∣ m := by dsimp [g]; exact Nat.gcd_dvd_left _ _
  have hfac : m = g * q := by
    dsimp [q]
    exact (Nat.mul_div_cancel' hgM).symm
  have hEpos : 0 < E := by dsimp [E]; omega
  have hcompE : g ∣ E := by simpa [g, E] using hcomp
  have hEle : E ≤ D + w := by dsimp [E]; omega
  have hgLtTwoD : g < 2 * D := by
    have hgE := Nat.le_of_dvd hEpos hcompE
    omega
  have hEneD : E ≠ D := by
    intro heq
    apply hincompat
    simpa [g, E, heq] using hcompE
  have hdistPos : 0 < E.dist D := Nat.dist_pos_of_ne hEneD
  have hdistLe : E.dist D ≤ w := by
    dsimp [E]
    rcases le_total s w with hsw | hws
    · rw [Nat.dist_eq_sub_of_le (by omega : D - w + s ≤ D)]
      omega
    · rw [Nat.dist_eq_sub_of_le_right (by omega : D ≤ D - w + s)]
      omega
  have hgScaleN : g ∣ scale * n := by
    dsimp [g]
    exact Nat.gcd_dvd_right _ _
  have hQpos : 0 < Q := by
    rw [hQ] at hn
    exact Nat.pos_of_mul_pos_right hn
  have hgScaleQD : g ∣ scale * Q * D := by
    simpa [hQ, mul_assoc] using hgScaleN
  have hgScaleQE : g ∣ scale * Q * E := by
    simpa [mul_assoc] using
      (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hcompE Q) scale)
  have hgDist : g ∣ scale * Q * (E.dist D) := by
    rcases le_total E D with hED | hDE
    · rw [Nat.dist_eq_sub_of_le hED, Nat.mul_sub_left_distrib]
      exact Nat.dvd_sub hgScaleQD hgScaleQE
    · rw [Nat.dist_eq_sub_of_le_right hDE, Nat.mul_sub_left_distrib]
      exact Nat.dvd_sub hgScaleQE hgScaleQD
  have hgBound : g ≤ scale * Q * w := by
    have hle := Nat.le_of_dvd
      (mul_pos (mul_pos hscale hQpos) hdistPos) hgDist
    exact hle.trans (Nat.mul_le_mul_left (scale * Q) hdistLe)
  by_contra hnot
  have hqB : q ≤ B := by simpa [q, g] using Nat.not_lt.mp hnot
  have hQlt : Q < 2 * q := by
    have hmLt : m < 2 * D * q := by
      rw [hfac]
      exact Nat.mul_lt_mul_of_pos_right hgLtTwoD (by
        have hqpos : 0 < q := by
          dsimp [q, g]
          exact Nat.div_pos (Nat.gcd_le_left (scale * n) (by omega)) hgpos
        exact hqpos)
    rw [hQ] at hm
    nlinarith
  have hQle : Q ≤ 2 * B := by omega
  have hmBound : m ≤ 2 * scale * B ^ 2 * w := calc
    m = g * q := hfac
    _ ≤ (scale * Q * w) * B :=
      Nat.mul_le_mul hgBound hqB
    _ ≤ (scale * (2 * B) * w) * B := by
      exact Nat.mul_le_mul_right B
        (Nat.mul_le_mul_right w (Nat.mul_le_mul_left scale hQle))
    _ = 2 * scale * B ^ 2 * w := by ring
  omega
theorem Q270
    (m n D V : ℕ) (hm : n < m) (hn : 0 < n) (hDpos : 0 < D)
    (horder : Q15 m ≤ V)
    (hcomp : m.gcd ((4 * n) * 2 ^ V) ∣ D)
    (hDn : D < n) :
    Odd (m / m.gcd ((4 * n) * 2 ^ V)) ∧
      3 ≤ m / m.gcd ((4 * n) * 2 ^ V) := by
  let p := (4 * n) * 2 ^ V
  let g := m.gcd p
  let q := m / g
  have hodd : Odd q := by
    simpa [q, g, p] using
      Q85
        m n V (by omega) hn horder
  have hgpos : 0 < g := by
    dsimp [g, p]
    exact Nat.gcd_pos_of_pos_left _ (by omega)
  have hgM : g ∣ m := by dsimp [g]; exact Nat.gcd_dvd_left _ _
  have hfac : m = g * q := by
    dsimp [q]
    exact (Nat.mul_div_cancel' hgM).symm
  have hqne : q ≠ 1 := by
    intro hq
    have hgleD : g ≤ D := Nat.le_of_dvd hDpos (by simpa [g, p] using hcomp)
    rw [hfac, hq, mul_one] at hm
    omega
  refine ⟨by simpa [q, g, p] using hodd, ?_⟩
  obtain ⟨z, hz⟩ := hodd
  change 3 ≤ q
  have hqpos : 0 < q := by
    dsimp [q, g, p]
    exact Nat.div_pos (Nat.gcd_le_left _ (by omega)) hgpos
  omega
theorem Q261
    (m n V v : ℕ) (hm : n < m) (hn : 0 < n)
    (horder : Q15 m ≤ V)
    (hcomp : m.gcd ((4 * n) * 2 ^ V) ∣ n * (2 * v + 1)) :
    Odd (m / m.gcd ((4 * n) * 2 ^ V)) ∧
      3 ≤ m / m.gcd ((4 * n) * 2 ^ V) := by
  let p := (4 * n) * 2 ^ V
  let g := m.gcd p
  let q := m / g
  have hodd : Odd q := by
    simpa [q, g, p] using
      Q85
        m n V (by omega) hn horder
  have hgpos : 0 < g := by
    dsimp [g, p]
    exact Nat.gcd_pos_of_pos_left _ (by omega)
  have hgM : g ∣ m := by dsimp [g]; exact Nat.gcd_dvd_left _ _
  have hfac : m = g * q := by
    dsimp [q]
    exact (Nat.mul_div_cancel' hgM).symm
  have hqne : q ≠ 1 := by
    intro hq
    have hgp : g ∣ n * 2 ^ (V + 2) := by
      have hg := Nat.gcd_dvd_right m p
      have hpEq : p = n * 2 ^ (V + 2) := by
        dsimp [p]
        rw [pow_succ, pow_succ]
        ring
      simpa [g, hpEq] using hg
    have hgo : g ∣ n * (2 * v + 1) := by simpa [g, p] using hcomp
    have hOdd : Odd (2 * v + 1) := ⟨v, by omega⟩
    have hgn : g ∣ n :=
      Q145
        g n (V + 2) (2 * v + 1) hgp hgo hOdd
    rw [hfac, hq, mul_one] at hm
    exact (not_le_of_gt hm) (Nat.le_of_dvd hn hgn)
  refine ⟨by simpa [q, g, p] using hodd, ?_⟩
  obtain ⟨z, hz⟩ := hodd
  change 3 ≤ q
  have hqpos : 0 < q := by
    dsimp [q, g, p]
    exact Nat.div_pos (Nat.gcd_le_left _ (by omega)) hgpos
  omega
theorem Q239
    (m n D Q V t : ℕ) (hm : 0 < m) (hnD : n = Q * D)
    (hcomp : m.gcd ((4 * n) * 2 ^ V) ∣ D) :
    m ∣ D + ((4 * n) * 2 ^ V) * t ↔
      m / m.gcd ((4 * n) * 2 ^ V) ∣
        1 + (4 * 2 ^ V * Q) * t := by
  let p := (4 * n) * 2 ^ V
  let g := m.gcd p
  let q := m / g
  let u := D / g
  have hgpos : 0 < g := by
    dsimp [g, p]
    exact Nat.gcd_pos_of_pos_left _ hm
  have hgm : m = g * q := by
    dsimp [q]
    exact (Nat.mul_div_cancel' (by dsimp [g]; exact Nat.gcd_dvd_left _ _)).symm
  have hgD : g ∣ D := by simpa [g, p] using hcomp
  have hD : D = g * u := by
    dsimp [u]
    exact (Nat.mul_div_cancel' hgD).symm
  have hDp : D ∣ p := by
    dsimp [p]
    rw [hnD]
    exact ⟨4 * 2 ^ V * Q, by ring⟩
  have hcop : q.Coprime u := by
    dsimp [q, u, g, p]
    exact Q65 m ((4 * n) * 2 ^ V) D
      hm hcomp hDp
  change m ∣ D + p * t ↔ q ∣ 1 + (4 * 2 ^ V * Q) * t
  rw [hgm, hD]
  have hpForm : p = 4 * (Q * (g * u)) * 2 ^ V := by
    dsimp [p]
    rw [hnD, hD]
  rw [hpForm]
  rw [show g * u + (4 * (Q * (g * u)) * 2 ^ V) * t =
    g * (u * (1 + (4 * 2 ^ V * Q) * t)) by ring]
  exact Q103 g q u _ hgpos hcop
theorem Q226
    (m n V v t : ℕ) (hm : 0 < m)
    (hcomp : m.gcd ((4 * n) * 2 ^ V) ∣ n * (2 * v + 1)) :
    m ∣ n * (2 * v + 1) + ((4 * n) * 2 ^ V) * t ↔
      m / m.gcd ((4 * n) * 2 ^ V) ∣
        (2 * v + 1) + (4 * 2 ^ V) * t := by
  let p := (4 * n) * 2 ^ V
  let g := m.gcd p
  let q := m / g
  have hgpos : 0 < g := by
    dsimp [g, p]
    exact Nat.gcd_pos_of_pos_left _ hm
  have hgm : m = g * q := by
    dsimp [q]
    exact (Nat.mul_div_cancel' (by dsimp [g]; exact Nat.gcd_dvd_left _ _)).symm
  have hgp : g ∣ n * 2 ^ (V + 2) := by
    have hg := Nat.gcd_dvd_right m p
    have hpEq : p = n * 2 ^ (V + 2) := by
      dsimp [p]
      rw [pow_succ, pow_succ]
      ring
    simpa [g, hpEq] using hg
  have hgo : g ∣ n * (2 * v + 1) := by simpa [g, p] using hcomp
  have hOdd : Odd (2 * v + 1) := ⟨v, by omega⟩
  have hgn : g ∣ n :=
    Q145
      g n (V + 2) (2 * v + 1) hgp hgo hOdd
  let u := n / g
  have hn : n = g * u := by
    dsimp [u]
    exact (Nat.mul_div_cancel' hgn).symm
  have hnp : n ∣ p := ⟨4 * 2 ^ V, by dsimp [p]; ring⟩
  have hcop : q.Coprime u := by
    dsimp [q, u, g, p]
    exact Q65 m ((4 * n) * 2 ^ V) n
      hm hgn hnp
  change m ∣ n * (2 * v + 1) + p * t ↔
    q ∣ (2 * v + 1) + (4 * 2 ^ V) * t
  rw [hgm, hn]
  have hpForm : p = 4 * (g * u) * 2 ^ V := by
    dsimp [p]
    rw [hn]
  rw [hpForm]
  rw [show g * u * (2 * v + 1) +
      (4 * (g * u) * 2 ^ V) * t =
    g * (u * ((2 * v + 1) + (4 * 2 ^ V) * t)) by ring]
  exact Q103 g q u _ hgpos hcop
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
def Q52
    (z Q scale root : ℕ) : Finset ℕ :=
  (Finset.range z).filter fun t =>
    (¬z ∣ root + scale * t) ∧
      (z.gcd Q = 1 → ¬z ∣ 1 + (scale * Q) * t)
theorem Q260
    (z Q scale root : ℕ) (hz : 3 ≤ z)
    (hscale : z.gcd scale = 1) :
    z - 2 ≤ (Q52 z Q scale root).card := by
  by_cases hQ : z.gcd Q = 1
  · have hprod : z.gcd (scale * Q) = 1 := by
      exact (show z.Coprime scale from hscale).mul_right
        (show z.Coprime Q from hQ) |>.gcd_eq_one
    have heq : Q52 z Q scale root =
        Q75 z (scale * Q) 1 scale root := by
      ext t
      simp [Q52, Q75, hQ,
        and_comm]
    rw [heq]
    exact Q152
      z (scale * Q) 1 scale root hz hprod hscale
  · have heq : Q52 z Q scale root =
        Q75 z scale root scale root := by
      ext t
      simp [Q52, Q75, hQ,
        and_self]
    rw [heq]
    exact Q152
      z scale root scale root hz hscale hscale
def Q33
    {r : ℕ} (p : Fin r → ℕ) (Q scale root : ℕ) : Finset ℕ :=
  (Finset.range (∏ i, p i)).filter fun t =>
    ∀ i, t % p i ∈ Q52 (p i) Q scale root
theorem Q227
    {r : ℕ} (p : Fin r → ℕ) (Q scale root : ℕ)
    (hp : ∀ i, 0 < p i)
    (hpair : ∀ i j, i ≠ j → (p i).Coprime (p j)) :
    (∏ i, (Q52 (p i) Q scale root).card) ≤
      (Q33 p Q scale root).card := by
  classical
  let S : Finset (Fin r) := Finset.univ
  have hpne : ∀ i ∈ S, p i ≠ 0 := by
    intro i _
    exact Nat.ne_of_gt (hp i)
  have hpairS : Set.Pairwise S (fun i j => (p i).Coprime (p j)) := by
    intro i _ j _ hij
    exact hpair i j hij
  let α := ∀ i : Fin r,
    {x // x ∈ Q52 (p i) Q scale root}
  let crt (x : α) : ℕ :=
    Nat.chineseRemainderOfFinset (fun i => (x i : ℕ)) p S hpne hpairS
  have hcrt_lt (x : α) : crt x < ∏ i, p i := by
    have h := Nat.chineseRemainderOfFinset_lt_prod
      (fun i => (x i : ℕ)) p hpne hpairS
    simpa [crt, S] using h
  have hcrt_mod (x : α) (i : Fin r) : crt x % p i = (x i : ℕ) := by
    have hz : crt x ≡ (x i : ℕ) [MOD p i] :=
      (Nat.chineseRemainderOfFinset
        (fun j => (x j : ℕ)) p S hpne hpairS).property i (by simp [S])
    have hxlt : (x i : ℕ) < p i :=
      Finset.mem_range.mp (Finset.mem_filter.mp (x i).property).1
    rw [Nat.ModEq] at hz
    simpa [Nat.mod_eq_of_lt hxlt] using hz
  let f : α → {t // t ∈ Q33 p Q scale root} :=
    fun x => ⟨crt x, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (hcrt_lt x), fun i => by
        rw [hcrt_mod x i]
        exact (x i).property⟩⟩
  have hf : Function.Injective f := by
    intro x y hxy
    funext i
    apply Subtype.ext
    have hcrt : crt x = crt y := congrArg Subtype.val hxy
    have hx := hcrt_mod x i
    have hy := hcrt_mod y i
    calc
      (x i : ℕ) = crt x % p i := hx.symm
      _ = crt y % p i := by rw [hcrt]
      _ = (y i : ℕ) := hy
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe] at hcard
  simpa [α, Fintype.card_pi, Q33] using hcard
theorem Q207
    {r : ℕ} (p : Fin r → ℕ) (Q scale root : ℕ)
    (hp3 : ∀ i, 3 ≤ p i)
    (hscale : ∀ i, (p i).gcd scale = 1)
    (hpair : ∀ i j, i ≠ j → (p i).Coprime (p j)) :
    (∏ i, (p i - 2)) ≤
      (Q33 p Q scale root).card := by
  calc
    (∏ i, (p i - 2)) ≤
        ∏ i, (Q52 (p i) Q scale root).card := by
      apply Finset.prod_le_prod
      · intro i hi
        exact Nat.zero_le _
      · intro i hi
        exact Q260
          (p i) Q scale root (hp3 i) (hscale i)
    _ ≤ (Q33 p Q scale root).card :=
      Q227 p Q scale root
        (fun i => by have := hp3 i; omega) hpair
theorem Q128
    (S : Finset ℕ) (Q scale root : ℕ)
    (hprime : ∀ z ∈ S, z.Prime)
    (hodd : ∀ z ∈ S, Odd z)
    (hscale : ∀ z ∈ S, z.gcd scale = 1) :
    ∃ p : Fin S.card → ℕ,
      (∏ i, p i) = ∏ z ∈ S, z ∧
      (∀ i, 3 ≤ p i) ∧
      (∀ i j, i ≠ j → (p i).Coprime (p j)) ∧
      (∀ z ∈ S, ∃ i, p i = z) ∧
      2 * (∏ i, p i) ≤
        (S.card + 1) * (S.card + 2) *
          (Q33 p Q scale root).card := by
  classical
  let e : Fin S.card ≃ {x // x ∈ S} :=
    (Fin.castOrderIso (Fintype.card_coe S).symm).toEquiv.trans
      (Fintype.equivFin {x // x ∈ S}).symm
  let p : Fin S.card → ℕ := fun i => (e i : ℕ)
  have hpMem (i : Fin S.card) : p i ∈ S := (e i).property
  have hpPrime (i : Fin S.card) : (p i).Prime :=
    hprime (p i) (hpMem i)
  have hpOdd (i : Fin S.card) : Odd (p i) := hodd (p i) (hpMem i)
  have hp3 (i : Fin S.card) : 3 ≤ p i := by
    have h2 := (hpPrime i).two_le
    have hne : p i ≠ 2 := by
      intro heq
      have heven : Even (p i) := by rw [heq]; norm_num
      exact (Nat.not_even_iff_odd.mpr (hpOdd i)) heven
    omega
  have hpPair : ∀ i j, i ≠ j → (p i).Coprime (p j) := by
    intro i j hij
    apply (Nat.coprime_primes (hpPrime i) (hpPrime j)).mpr
    intro hpij
    apply hij
    exact e.injective (Subtype.ext hpij)
  have hprod : (∏ i, p i) = ∏ z ∈ S, z := by
    calc
      (∏ i, p i) = ∏ x : {x // x ∈ S}, (x : ℕ) :=
        Equiv.prod_comp e (fun x : {x // x ∈ S} => (x : ℕ))
      _ = ∏ z ∈ S, z := Finset.prod_coe_sort S (fun z => z)
  have hprodSub : (∏ i, (p i - 2)) = ∏ z ∈ S, (z - 2) := by
    calc
      (∏ i, (p i - 2)) =
          ∏ x : {x // x ∈ S}, ((x : ℕ) - 2) :=
        Equiv.prod_comp e (fun x : {x // x ∈ S} => ((x : ℕ) - 2))
      _ = ∏ z ∈ S, (z - 2) :=
        Finset.prod_coe_sort S (fun z => z - 2)
  have hsafe : (∏ i, (p i - 2)) ≤
      (Q33 p Q scale root).card :=
    Q207 p Q scale root hp3
      (fun i => hscale (p i) (hpMem i)) hpPair
  have honto : ∀ z ∈ S, ∃ i, p i = z := by
    intro z hz
    obtain ⟨i, hi⟩ := e.surjective ⟨z, hz⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  have hS3 : ∀ z ∈ S, 3 ≤ z := by
    intro z hz
    have h2 := (hprime z hz).two_le
    have hne : z ≠ 2 := by
      intro heq
      have heven : Even z := by rw [heq]; norm_num
      exact (Nat.not_even_iff_odd.mpr (hodd z hz)) heven
    omega
  have hdensity := Q111 S hS3
  refine ⟨p, hprod, hp3, hpPair, honto, ?_⟩
  calc
    2 * (∏ i, p i) = 2 * (∏ z ∈ S, z) := by rw [hprod]
    _ ≤ (S.card + 1) * (S.card + 2) *
        (∏ z ∈ S, (z - 2)) := hdensity
    _ = (S.card + 1) * (S.card + 2) *
        (∏ i, (p i - 2)) := by rw [hprodSub]
    _ ≤ (S.card + 1) * (S.card + 2) *
        (Q33 p Q scale root).card :=
      Nat.mul_le_mul_left _ hsafe
def Q64
    {r : ℕ} (p : Fin r → ℕ) (Q scale root T : ℕ) : Finset ℕ :=
  ((Finset.range T).product
    (Q33 p Q scale root)).image fun z =>
      z.2 + (∏ i, p i) * z.1
lemma Q222
    {r : ℕ} (p : Fin r → ℕ) (Q scale root T : ℕ)
    (hM : 0 < ∏ i, p i) :
    (Q64 p Q scale root T).card =
      T * (Q33 p Q scale root).card := by
  classical
  unfold Q64
  rw [Finset.card_image_of_injOn]
  · simp
  · intro z hz w hw hzw
    have hzlt : z.2 < ∏ i, p i :=
      Finset.mem_range.mp (Finset.mem_filter.mp
        (Finset.mem_product.mp hz).2).1
    have hwlt : w.2 < ∏ i, p i :=
      Finset.mem_range.mp (Finset.mem_filter.mp
        (Finset.mem_product.mp hw).2).1
    have hrem := congrArg (fun x => x % (∏ i, p i)) hzw
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hzlt,
      Nat.mod_eq_of_lt hwlt] at hrem
    have hblock : z.1 = w.1 := by
      change z.2 + (∏ i, p i) * z.1 =
        w.2 + (∏ i, p i) * w.1 at hzw
      rw [hrem] at hzw
      exact Nat.mul_left_cancel hM (Nat.add_left_cancel hzw)
    cases z
    cases w
    simp_all
theorem Q110
    {ι : Type*} [DecidableEq ι]
    (Qmods : Finset ℕ) (C : Finset ι) (side : ι → Bool)
    (offset qmod : ι → ℕ) (step targetQ scale root : ℕ)
    (hQ3 : ∀ q ∈ Qmods, 3 ≤ q)
    (hQodd : ∀ q ∈ Qmods, Odd q)
    (hQscale : ∀ q ∈ Qmods, q.gcd scale = 1)
    (hcover : ∀ u ∈ C, ∃ q ∈ Qmods,
      (side u = false → q.gcd targetQ = 1) ∧
      ∀ t, qmod u ∣ offset u + step * t →
        if side u then q ∣ root + scale * t
        else q ∣ 1 + (scale * targetQ) * t) :
    let S := Q20 Qmods
    ∃ M : ℕ, 0 < M ∧ M = ∏ z ∈ S, z ∧ ∀ T : ℕ,
      2 * (T * M) ≤ (S.card + 1) * (S.card + 2) *
        (Q23 C offset qmod step (T * M)).card := by
  classical
  let S := Q20 Qmods
  have hSdata := Q163 Qmods hQ3 hQodd
  have hSprime : ∀ z ∈ S, z.Prime := fun z hz => (hSdata z hz).1
  have hSodd : ∀ z ∈ S, Odd z := fun z hz => (hSdata z hz).2.1
  have hSscale : ∀ z ∈ S, z.gcd scale = 1 := by
    intro z hz
    obtain ⟨q, hqQ, hqz⟩ := (Q66 Qmods z).mp hz
    have hzd : z ∣ q := by simpa [hqz] using Nat.minFac_dvd q
    exact (Nat.Coprime.of_dvd_left hzd (hQscale q hqQ)).gcd_eq_one
  obtain ⟨p, hprod, hp3, hpPair, honto, hsafeBound⟩ :=
    Q128
      S targetQ scale root hSprime hSodd hSscale
  let M := ∏ i, p i
  have hMpos : 0 < M := by
    dsimp [M]
    apply Finset.prod_pos
    intro i hi
    exact lt_of_lt_of_le (by norm_num) (hp3 i)
  refine ⟨M, hMpos, hprod, ?_⟩
  intro T
  have hsubset :
      Q64 p targetQ scale root T ⊆
        Q23 C offset qmod step (T * M) := by
    intro t htRep
    obtain ⟨z, hzProd, rfl⟩ := Finset.mem_image.mp htRep
    have hzT := Finset.mem_range.mp (Finset.mem_product.mp hzProd).1
    have hzSafe := (Finset.mem_product.mp hzProd).2
    have hzData := Finset.mem_filter.mp hzSafe
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, ?_⟩
    · have hzlt := Finset.mem_range.mp hzData.1
      dsimp [M]
      nlinarith
    · intro u huC hbad
      obtain ⟨q, hqQ, hlowCop, himp⟩ := hcover u huC
      have hform := himp (z.2 + M * z.1) hbad
      have hqne : q ≠ 1 := by have := hQ3 q hqQ; omega
      let prime := q.minFac
      have hprimeS : prime ∈ S :=
        (Q66 Qmods prime).mpr ⟨q, hqQ, rfl⟩
      obtain ⟨i, hpi⟩ := honto prime hprimeS
      have hsafeI := Finset.mem_filter.mp (hzData.2 i)
      have hpM : p i ∣ M := by
        dsimp [M]
        exact Finset.dvd_prod_of_mem p (by simp)
      have hprimeDvd : prime ∣ q := Nat.minFac_dvd q
      by_cases hside : side u = true
      · have hform' : q ∣ root + scale * (z.2 + M * z.1) := by
          simpa [hside] using hform
        have hpbad : p i ∣ root + scale * z.2 := by
          have hd : p i ∣ root + scale * (z.2 + M * z.1) := by
            simpa [hpi] using dvd_trans hprimeDvd hform'
          rw [show root + scale * (z.2 + M * z.1) =
            scale * M * z.1 + (root + scale * z.2) by ring] at hd
          have htail : p i ∣ scale * M * z.1 :=
            dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpM scale) z.1
          exact (Nat.dvd_add_iff_right htail).mpr hd
        apply hsafeI.2.1
        have hzmod : z.2 ≡ z.2 % p i [MOD p i] :=
          (Nat.mod_modEq z.2 (p i)).symm
        have hlin : root + scale * z.2 ≡
            root + scale * (z.2 % p i) [MOD p i] :=
          (Nat.ModEq.refl root).add (hzmod.mul_left scale)
        exact (hlin.dvd_iff dvd_rfl).mp hpbad
      · have hsideFalse : side u = false := Bool.eq_false_of_not_eq_true hside
        have hqCop : q.gcd targetQ = 1 := hlowCop hsideFalse
        have hpCop : (p i).gcd targetQ = 1 := by
          have hpq : p i ∣ q := by simpa [hpi] using hprimeDvd
          exact (Nat.Coprime.of_dvd_left hpq hqCop).gcd_eq_one
        have hform' : q ∣ 1 + (scale * targetQ) *
            (z.2 + M * z.1) := by simpa [hsideFalse] using hform
        have hpbad : p i ∣ 1 + (scale * targetQ) * z.2 := by
          have hd : p i ∣ 1 + (scale * targetQ) *
              (z.2 + M * z.1) := by
            simpa [hpi] using dvd_trans hprimeDvd hform'
          rw [show 1 + (scale * targetQ) * (z.2 + M * z.1) =
            (scale * targetQ) * M * z.1 +
              (1 + (scale * targetQ) * z.2) by ring] at hd
          have htail : p i ∣ (scale * targetQ) * M * z.1 :=
            dvd_mul_of_dvd_left
              (dvd_mul_of_dvd_right hpM (scale * targetQ)) z.1
          exact (Nat.dvd_add_iff_right htail).mpr hd
        apply hsafeI.2.2 hpCop
        have hzmod : z.2 ≡ z.2 % p i [MOD p i] :=
          (Nat.mod_modEq z.2 (p i)).symm
        have hlin : 1 + (scale * targetQ) * z.2 ≡
            1 + (scale * targetQ) * (z.2 % p i) [MOD p i] :=
          (Nat.ModEq.refl 1).add (hzmod.mul_left (scale * targetQ))
        exact (hlin.dvd_iff dvd_rfl).mp hpbad
  have hcard := Finset.card_le_card hsubset
  have hrepCard := Q222
    p targetQ scale root T hMpos
  have hbaseScaled := Nat.mul_le_mul_left T hsafeBound
  calc
    2 * (T * M) = T * (2 * (∏ i, p i)) := by dsimp [M]; ring
    _ ≤ T * ((S.card + 1) * (S.card + 2) *
        (Q33 p targetQ scale root).card) :=
      hbaseScaled
    _ = (S.card + 1) * (S.card + 2) *
        (Q64
          p targetQ scale root T).card := by
      rw [hrepCard]
      ring
    _ ≤ (S.card + 1) * (S.card + 2) *
        (Q23 C offset qmod step (T * M)).card :=
      Nat.mul_le_mul_left _ hcard
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
theorem Q131
    (n : ℕ → ℕ) (K H W A X p : ℕ) (S : Finset ((ℕ × ℕ) × Bool))
    (hsub : S ⊆ Q18 n K H W A X p)
    (hhigh : ∀ u ∈ S, W < (n u.1.1).gcd p) :
    Set.InjOn (fun u : ((ℕ × ℕ) × Bool) => (u.1.1, u.2)) S := by
  intro u hu v hv huv
  have huComp := hsub hu
  have hvComp := hsub hv
  have huBase := (Finset.mem_filter.mp huComp).1
  have hvBase := (Finset.mem_filter.mp hvComp).1
  have huSol := (Finset.mem_filter.mp huComp).2
  have hvSol := (Finset.mem_filter.mp hvComp).2
  have hsu : u.1.2 < W :=
    Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.mem_product.mp huBase).1).2
  have hsv : v.1.2 < W :=
    Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.mem_product.mp hvBase).1).2
  have hju : u.1.1 = v.1.1 :=
    congrArg (fun z : ℕ × Bool => z.1) huv
  have hbu : u.2 = v.2 :=
    congrArg (fun z : ℕ × Bool => z.2) huv
  let g := (n u.1.1).gcd p
  have hgW : W < g := by simpa [g] using hhigh u hu
  have huD : g ∣ A + u.1.2 + (if u.2 = true then X else 0) := by
    simpa [g, Q2, Q16] using huSol
  have hvD : g ∣ A + v.1.2 + (if u.2 = true then X else 0) := by
    simpa [g, Q2, Q16, hju, hbu] using hvSol
  have hsEq : u.1.2 = v.1.2 := by
    rcases le_total u.1.2 v.1.2 with hle | hle
    · have hd : g ∣ v.1.2 - u.1.2 := by
        have heq :
            (A + v.1.2 + (if u.2 = true then X else 0)) -
              (A + u.1.2 + (if u.2 = true then X else 0)) =
                v.1.2 - u.1.2 := by omega
        rw [← heq]
        exact Nat.dvd_sub hvD huD
      have hz := Nat.eq_zero_of_dvd_of_lt hd (by omega)
      omega
    · have hd : g ∣ u.1.2 - v.1.2 := by
        have heq :
            (A + u.1.2 + (if u.2 = true then X else 0)) -
              (A + v.1.2 + (if u.2 = true then X else 0)) =
                u.1.2 - v.1.2 := by omega
        rw [← heq]
        exact Nat.dvd_sub huD hvD
      have hz := Nat.eq_zero_of_dvd_of_lt hd (by omega)
      omega
  rcases u with ⟨⟨uj, us⟩, ub⟩
  rcases v with ⟨⟨vj, vs⟩, vb⟩
  simp only at hju hbu hsEq
  subst vj
  subst vs
  subst vb
  rfl
theorem Q284
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (K H W A X p R Z : ℕ) (S : Finset ((ℕ × ℕ) × Bool))
    (hsub : S ⊆ Q18 n K H W A X p)
    (hhigh : ∀ u ∈ S, W < (n u.1.1).gcd p)
    (hle : ∀ u ∈ S, (n u.1.1).gcd p ≤ Z) :
    ((∑ u ∈ S, (R / (Q2 n u /
      (Q2 n u).gcd p) + 1) : ℕ) : ℝ) ≤
      2 * (∑ j ∈ Q0 K H,
        ((R : ℝ) * Z / n j + 1)) := by
  classical
  let f : ((ℕ × ℕ) × Bool) → ℕ × Bool := fun u => (u.1.1, u.2)
  let T := (Q0 K H).product (Finset.univ : Finset Bool)
  let upper : ℕ × Bool → ℝ := fun y => (R : ℝ) * Z / n y.1 + 1
  have hmap : S.image f ⊆ T := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
    have huBase := (Finset.mem_filter.mp (hsub hu)).1
    have hj := (Finset.mem_product.mp (Finset.mem_product.mp huBase).1).1
    exact Finset.mem_product.mpr ⟨hj, Finset.mem_univ _⟩
  have hinj := Q131
    n K H W A X p S hsub hhigh
  have hpoint : ∀ u ∈ S,
      (((R / (Q2 n u /
        (Q2 n u).gcd p) + 1 : ℕ) : ℝ)) ≤ upper (f u) := by
    intro u hu
    let m := n u.1.1
    let g := m.gcd p
    have hm : 0 < m := hpos u.1.1
    have hdiv := Q198 R m p hm
    have hcast : (((R * g) / m : ℕ) : ℝ) ≤ (R : ℝ) * g / m := by
      have hc : (((R * g) / m : ℕ) : ℝ) ≤ ((R * g : ℕ) : ℝ) / m :=
        Nat.cast_div_le
      push_cast at hc
      exact hc
    have hgZreal : (g : ℝ) ≤ Z := by exact_mod_cast hle u hu
    have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
    have hmain : (((R / (m / g) + 1 : ℕ) : ℝ)) ≤
        (R : ℝ) * Z / m + 1 := by
      push_cast
      rw [show R / (m / g) = (R * g) / m by
        simpa [g] using hdiv]
      calc
        (((R * g) / m : ℕ) : ℝ) + 1 ≤ (R : ℝ) * g / m + 1 := by
          linarith
        _ ≤ (R : ℝ) * Z / m + 1 := by
          gcongr
    simpa [upper, f, m, g, Q2] using hmain
  calc
    ((∑ u ∈ S, (R / (Q2 n u /
      (Q2 n u).gcd p) + 1) : ℕ) : ℝ) =
        ∑ u ∈ S, (((R / (Q2 n u /
          (Q2 n u).gcd p) + 1 : ℕ) : ℝ)) := by push_cast; rfl
    _ ≤ ∑ u ∈ S, upper (f u) := by
      apply Finset.sum_le_sum
      intro u hu
      exact hpoint u hu
    _ = ∑ y ∈ S.image f, upper y := by
      symm
      exact Finset.sum_image hinj
    _ ≤ ∑ y ∈ T, upper y :=
      Finset.sum_le_sum_of_subset_of_nonneg hmap (by
        intro y hyT hyS
        dsimp [upper]
        positivity)
    _ = 2 * (∑ j ∈ Q0 K H,
        ((R : ℝ) * Z / n j + 1)) := by
      simp [T, upper, Finset.sum_product]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
theorem Q243
    (n : ℕ → ℕ) (_hpos : ∀ k, 0 < n k)
    (K H W A X p R B : ℕ) (S : Finset ((ℕ × ℕ) × Bool))
    (hB : 0 < B)
    (hsub : S ⊆ Q18 n K H W A X p)
    (hhigh : ∀ u ∈ S, W < (n u.1.1).gcd p)
    (hred : ∀ u ∈ S, B < n u.1.1 / (n u.1.1).gcd p) :
    ((∑ u ∈ S, (R / (Q2 n u /
      (Q2 n u).gcd p) + 1) : ℕ) : ℝ) ≤
      2 * (Q0 K H).card * ((R : ℝ) / B + 1) := by
  classical
  let f : ((ℕ × ℕ) × Bool) → ℕ × Bool := fun u => (u.1.1, u.2)
  let T := (Q0 K H).product (Finset.univ : Finset Bool)
  have hmap : S.image f ⊆ T := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
    have huBase := (Finset.mem_filter.mp (hsub hu)).1
    have hj := (Finset.mem_product.mp (Finset.mem_product.mp huBase).1).1
    exact Finset.mem_product.mpr ⟨hj, Finset.mem_univ _⟩
  have hinj := Q131
    n K H W A X p S hsub hhigh
  have hpoint : ∀ u ∈ S,
      (((R / (Q2 n u /
        (Q2 n u).gcd p) + 1 : ℕ) : ℝ)) ≤
        (R : ℝ) / B + 1 := by
    intro u hu
    let q := n u.1.1 / (n u.1.1).gcd p
    have hq : B < q := by simpa [q] using hred u hu
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le hB hq.le)
    have hBreal : (0 : ℝ) < B := by exact_mod_cast hB
    have hc : (((R / q : ℕ) : ℝ)) ≤ (R : ℝ) / q := Nat.cast_div_le
    have hmain : (((R / q + 1 : ℕ) : ℝ)) ≤ (R : ℝ) / B + 1 := by
      push_cast
      calc
        (((R / q : ℕ) : ℝ)) + 1 ≤ (R : ℝ) / q + 1 := by linarith
        _ ≤ (R : ℝ) / B + 1 := by
          have hdivle : (R : ℝ) / q ≤ (R : ℝ) / B :=
            div_le_div_of_nonneg_left (by positivity) hBreal
              (by exact_mod_cast hq.le)
          linarith
    simpa [q, Q2] using hmain
  have hcard : S.card ≤ 2 * (Q0 K H).card := by
    calc
      S.card = (S.image f).card := (Finset.card_image_iff.mpr hinj).symm
      _ ≤ T.card := Finset.card_le_card hmap
      _ = 2 * (Q0 K H).card := by simp [T, Nat.mul_comm]
  calc
    ((∑ u ∈ S, (R / (Q2 n u /
      (Q2 n u).gcd p) + 1) : ℕ) : ℝ) =
        ∑ u ∈ S, (((R / (Q2 n u /
          (Q2 n u).gcd p) + 1 : ℕ) : ℝ)) := by push_cast; rfl
    _ ≤ ∑ _u ∈ S, ((R : ℝ) / B + 1) := by
      apply Finset.sum_le_sum
      intro u hu
      exact hpoint u hu
    _ = S.card * ((R : ℝ) / B + 1) := by simp; ring
    _ ≤ (2 * (Q0 K H).card) * ((R : ℝ) / B + 1) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcard
      · positivity
    _ = 2 * (Q0 K H).card * ((R : ℝ) / B + 1) := by ring
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
def Q106
    (n : ℕ → ℕ) (K H W A X p w : ℕ) : Finset ((ℕ × ℕ) × Bool) :=
  (Q44 n K H W A X p w).filter fun u =>
    (n u.1.1).gcd p ≤ W
def Q105
    (n : ℕ → ℕ) (K H W A X p w Z : ℕ) : Finset ((ℕ × ℕ) × Bool) :=
  (Q44 n K H W A X p w).filter fun u =>
    W < (n u.1.1).gcd p ∧ (n u.1.1).gcd p ≤ Z
def Q113
    (n : ℕ → ℕ) (K H W A X p w Z : ℕ) : Finset ((ℕ × ℕ) × Bool) :=
  (Q44 n K H W A X p w).filter fun u =>
    Z < (n u.1.1).gcd p
theorem Q246
    (n : ℕ → ℕ) (K H W A X p w Z : ℕ) :
    Q44 n K H W A X p w ⊆
      Q106 n K H W A X p w ∪
        Q105 n K H W A X p w Z ∪
          Q113 n K H W A X p w Z := by
  intro u hu
  simp only [Q106,
    Q105, Q113,
    Finset.mem_union, Finset.mem_filter]
  by_cases hlo : (n u.1.1).gcd p ≤ W
  · exact Or.inl (Or.inl ⟨hu, hlo⟩)
  · by_cases hmid : (n u.1.1).gcd p ≤ Z
    · exact Or.inl (Or.inr ⟨hu, Nat.lt_of_not_ge hlo, hmid⟩)
    · exact Or.inr ⟨hu, Nat.lt_of_not_ge hmid⟩
theorem Q291
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (K H w D Q X V v R B : ℕ)
    (_hKH : K < H) (hw : 0 < w) (hD : w < D) (hB : 0 < B)
    (hQ : n K = Q * D) (hX : D + X = n K * (2 * v + 1))
    (hsize : 2 * (4 * 2 ^ V) * B ^ 2 * w ≤ n K) :
    let W := 2 * w + 1
    let A := D - w
    let p := (4 * n K) * 2 ^ V
    let Z := (4 * 2 ^ V) * w
    let O := Q44 n K H W A X p w
    ((∑ u ∈ O, (R / (Q2 n u /
      (Q2 n u).gcd p) + 1) : ℕ) : ℝ) ≤
      (4 * (R : ℝ) * W *
          (∑ j ∈ Q0 K H, ((n j : ℝ)⁻¹)) +
        4 * W * (Q0 K H).card) +
      2 * (∑ j ∈ Q0 K H,
        ((R : ℝ) * Z / n j + 1)) +
      2 * (Q0 K H).card * ((R : ℝ) / B + 1) := by
  classical
  let W := 2 * w + 1
  let A := D - w
  let p := (4 * n K) * 2 ^ V
  let scale := 4 * 2 ^ V
  let Z := scale * w
  let O := Q44 n K H W A X p w
  let Low := Q106 n K H W A X p w
  let Mid := Q105 n K H W A X p w Z
  let Exc := Q113 n K H W A X p w Z
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have hWZ : W ≤ Z := by
    dsimp [W, Z, scale]
    have hpow : 0 < 2 ^ V := pow_pos (by norm_num) V
    nlinarith
  have hcover : O ⊆ Low ∪ Mid ∪ Exc :=
    Q246
      n K H W A X p w Z
  let cost : ((ℕ × ℕ) × Bool) → ℕ := fun u =>
    R / (Q2 n u /
      (Q2 n u).gcd p) + 1
  have hsplitNat : (∑ u ∈ O, cost u) ≤
      (∑ u ∈ Low, cost u) + (∑ u ∈ Mid, cost u) +
        ∑ u ∈ Exc, cost u := by
    calc
      (∑ u ∈ O, cost u) ≤ ∑ u ∈ Low ∪ Mid ∪ Exc, cost u :=
        Finset.sum_le_sum_of_subset hcover
      _ ≤ (∑ u ∈ Low, cost u) + (∑ u ∈ Mid, cost u) +
          ∑ u ∈ Exc, cost u := by
        have h1 := Finset.sum_union_inter (s₁ := Low ∪ Mid) (s₂ := Exc)
          (f := cost)
        have h2 := Finset.sum_union_inter (s₁ := Low) (s₂ := Mid)
          (f := cost)
        omega
  have hsplit : (((∑ u ∈ O, cost u) : ℕ) : ℝ) ≤
      (((∑ u ∈ Low, cost u) : ℕ) : ℝ) +
        (((∑ u ∈ Mid, cost u) : ℕ) : ℝ) +
          (((∑ u ∈ Exc, cost u) : ℕ) : ℝ) := by
    exact_mod_cast hsplitNat
  have hLowSub : Low ⊆ Q50
      n K H W A X p := by
    intro u hu
    have huData := Finset.mem_filter.mp hu
    have huOff := huData.1
    have huComp := (Finset.mem_sdiff.mp huOff).1
    exact Finset.mem_filter.mpr ⟨huComp, huData.2⟩
  have hLowNat : (∑ u ∈ Low, cost u) ≤
      ∑ u ∈ Q50 n K H W A X p,
        cost u := Finset.sum_le_sum_of_subset hLowSub
  have hLowCast : (((∑ u ∈ Low, cost u) : ℕ) : ℝ) ≤
      ((∑ u ∈ Q50 n K H W A X p,
        cost u : ℕ) : ℝ) := by exact_mod_cast hLowNat
  have hLowBound := Q335
    n hpos K H W A X p R
  have hLow : (((∑ u ∈ Low, cost u) : ℕ) : ℝ) ≤
      4 * (R : ℝ) * W *
          (∑ j ∈ Q0 K H, ((n j : ℝ)⁻¹)) +
        4 * W * (Q0 K H).card := by
    exact hLowCast.trans (by simpa [cost] using hLowBound)
  have hMidSub : Mid ⊆ Q18 n K H W A X p := by
    intro u hu
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hu).1).1
  have hMidHigh : ∀ u ∈ Mid, W < (n u.1.1).gcd p := by
    intro u hu
    exact (Finset.mem_filter.mp hu).2.1
  have hMidLe : ∀ u ∈ Mid, (n u.1.1).gcd p ≤ Z := by
    intro u hu
    exact (Finset.mem_filter.mp hu).2.2
  have hMidBound := Q284
    n hpos K H W A X p R Z Mid hMidSub hMidHigh hMidLe
  have hMid : (((∑ u ∈ Mid, cost u) : ℕ) : ℝ) ≤
      2 * (∑ j ∈ Q0 K H,
        ((R : ℝ) * Z / n j + 1)) := by
    simpa [cost] using hMidBound
  have hExcSub : Exc ⊆ Q18 n K H W A X p := by
    intro u hu
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hu).1).1
  have hExcHigh : ∀ u ∈ Exc, W < (n u.1.1).gcd p := by
    intro u hu
    have hz := (Finset.mem_filter.mp hu).2
    exact lt_of_le_of_lt hWZ hz
  have hExcRed : ∀ u ∈ Exc,
      B < n u.1.1 / (n u.1.1).gcd p := by
    intro u hu
    have huData := Finset.mem_filter.mp hu
    have huOffData := Finset.mem_sdiff.mp huData.1
    have huComp := (Finset.mem_filter.mp huOffData.1).2
    have huBase := (Finset.mem_filter.mp huOffData.1).1
    have huPair := Finset.mem_product.mp (Finset.mem_product.mp huBase).1
    have hsW := Finset.mem_range.mp huPair.2
    have hoff : u.1.2 ≠ w := by
      intro heq
      apply huOffData.2
      exact Finset.mem_filter.mpr ⟨huOffData.1, heq⟩
    have hlarge : scale * w < (n u.1.1).gcd (scale * n K) := by
      simpa [Z, p, scale, mul_assoc, mul_comm, mul_left_comm] using huData.2
    have hcomp : (n u.1.1).gcd (scale * n K) ∣
        (if u.2 then D - w + u.1.2 + X else D - w + u.1.2) := by
      by_cases hside : u.2 = true
      · simpa [Q2, Q16, p, A, scale, hside,
          mul_assoc, mul_comm, mul_left_comm] using huComp
      · have hsideFalse : u.2 = false := Bool.eq_false_of_not_eq_true hside
        simpa [Q2, Q16, p, A, scale, hsideFalse,
          mul_assoc, mul_comm, mul_left_comm] using huComp
    obtain ⟨hside, hincompat⟩ := Q321
      (n u.1.1) (n K) D w u.1.2 X scale v (hpos K) hD hsW
        hX hscale u.2 hcomp hoff hlarge
    have hm : n K < n u.1.1 := by
      have hj := (Finset.mem_filter.mp huPair.1).2
      exact hmono hj
    have hleftComp : (n u.1.1).gcd (scale * n K) ∣
        D - w + u.1.2 := by simpa [hside] using hcomp
    have hgt := Q185
      (n u.1.1) (n K) D Q w u.1.2 scale B (hpos K) hm hD hQ
        hsW hscale hleftComp hincompat (by simpa [scale] using hsize)
    simpa [p, scale, mul_assoc, mul_comm, mul_left_comm] using hgt
  have hExcBound := Q243
    n hpos K H W A X p R B Exc hB hExcSub hExcHigh hExcRed
  have hExc : (((∑ u ∈ Exc, cost u) : ℕ) : ℝ) ≤
      2 * (Q0 K H).card * ((R : ℝ) / B + 1) := by
    simpa [cost] using hExcBound
  exact hsplit.trans (add_le_add (add_le_add hLow hMid) hExc)
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
def Q25
    (n : ℕ → ℕ) (K H W A X p w : ℕ) (Block : Finset ℕ) :
    Finset ((ℕ × ℕ) × Bool) :=
  (Q254 n K H W A X p w).filter fun u =>
    u.1.1 ∉ Block
def Q76
    (n : ℕ → ℕ) (K H W A X p w : ℕ) (Block : Finset ℕ) :
    Finset ((ℕ × ℕ) × Bool) :=
  Q14 n K H W A X p Block \
    Q25 n K H W A X p w Block
def Q22
    (n : ℕ → ℕ) (K H W A X p w : ℕ) (Block : Finset ℕ) : Finset ℕ :=
  (Q25 n K H W A X p w Block).image
    fun u => Q2 n u / (Q2 n u).gcd p
theorem Q193
    (n : ℕ → ℕ) (K G W A X p w : ℕ) (Block : Finset ℕ) :
    (Q25
      n K G W A X p w Block).card ≤
      2 * (Q0 K G).card := by
  classical
  let C := Q25
    n K G W A X p w Block
  let T := (Q0 K G).product (Finset.univ : Finset Bool)
  let f : ((ℕ × ℕ) × Bool) → ℕ × Bool := fun u => (u.1.1, u.2)
  have hmap : Set.MapsTo f C T := by
    intro u hu
    have huOld := (Finset.mem_filter.mp hu).1
    have huCompat := (Finset.mem_filter.mp huOld).1
    have huBase := (Finset.mem_filter.mp huCompat).1
    have huInner := (Finset.mem_product.mp
      (Finset.mem_product.mp huBase).1)
    exact Finset.mem_product.mpr ⟨huInner.1, Finset.mem_univ _⟩
  have hinj : Set.InjOn f C := by
    intro u hu v hv huv
    have huCenter := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
    have hvCenter := (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2
    have hj : u.1.1 = v.1.1 :=
      congrArg (fun z : ℕ × Bool => z.1) huv
    have hb : u.2 = v.2 :=
      congrArg (fun z : ℕ × Bool => z.2) huv
    have hs : u.1.2 = v.1.2 := by omega
    rcases u with ⟨⟨uj, us⟩, ub⟩
    rcases v with ⟨⟨vj, vs⟩, vb⟩
    simp only at hj hb hs
    subst vj
    subst vs
    subst vb
    rfl
  have hc := Finset.card_le_card_of_injOn f hmap hinj
  simpa [C, T, Nat.mul_comm] using hc
theorem Q58
    (n : ℕ → ℕ) (K G W A X p w : ℕ) (Block : Finset ℕ) :
    (Q20
      (Q22
        n K G W A X p w Block)).card ≤
      2 * (Q0 K G).card := by
  calc
    _ ≤ (Q22
        n K G W A X p w Block).card := Finset.card_image_le
    _ ≤ (Q25
        n K G W A X p w Block).card := Finset.card_image_le
    _ ≤ _ := Q193
      n K G W A X p w Block
theorem Q186
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (K G W A X p w B z : ℕ) (Block : Finset ℕ)
    (hvalues : ∀ j, K < j → j < G → n j ≤ B)
    (hz : z ∈ Q20
      (Q22
        n K G W A X p w Block)) :
    z ≤ B := by
  obtain ⟨q, hqQ, hqz⟩ :=
    (Q66
      (Q22
        n K G W A X p w Block) z).mp hz
  obtain ⟨u, huC, hqu⟩ := Finset.mem_image.mp hqQ
  have huOld := (Finset.mem_filter.mp huC).1
  have huCompat := (Finset.mem_filter.mp huOld).1
  have huBase := (Finset.mem_filter.mp huCompat).1
  have huPair := Finset.mem_product.mp (Finset.mem_product.mp huBase).1
  have hjData := Finset.mem_filter.mp huPair.1
  have hjG := Finset.mem_range.mp hjData.1
  have hqLe : q ≤ n u.1.1 := by
    calc
      q = Q2 n u /
          (Q2 n u).gcd p := hqu.symm
      _ ≤ Q2 n u := Nat.div_le_self _ _
      _ = n u.1.1 := rfl
  have hzLe : z ≤ q := by
    rw [← hqz]
    exact Nat.minFac_le (by
      have hqpos : 0 < q := by
        rw [← hqu]
        exact Nat.div_pos
          (Nat.gcd_le_left p (hpos u.1.1))
          (Nat.gcd_pos_of_pos_left p (hpos u.1.1))
      exact hqpos)
  exact hzLe.trans (hqLe.trans (hvalues u.1.1 hjData.2 hjG))
theorem Q119
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (K G W A X p w B : ℕ) (Block : Finset ℕ) (hB : 0 < B)
    (hvalues : ∀ j, K < j → j < G → n j ≤ B) :
    let S := Q20
      (Q22
        n K G W A X p w Block)
    let d := (Q0 K G).card
    (∏ z ∈ S, z) ≤ B ^ (2 * d) := by
  let S := Q20
    (Q22
      n K G W A X p w Block)
  let d := (Q0 K G).card
  have hprod : (∏ z ∈ S, z) ≤ B ^ S.card := by
    apply Finset.prod_le_pow_card
    intro z hz
    exact Q186
      n hpos K G W A X p w B z Block hvalues hz
  exact hprod.trans (Nat.pow_le_pow_right hB
    (Q58
      n K G W A X p w Block))
theorem Q90
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (K G w D Q X V v : ℕ) (Block : Finset ℕ) (_hKG : K < G)
    (hD : w < D) (hDn : D < n K) (hQ : n K = Q * D)
    (hX : D + X = n K * (2 * v + 1))
    (horder : ∀ j, K < j → j < G → j ∉ Block →
      Q15 (n j) ≤ V) :
    let W := 2 * w + 1
    let A := D - w
    let p := (4 * n K) * 2 ^ V
    let C := Q25
      n K G W A X p w Block
    let Qmods := Q22
      n K G W A X p w Block
    let S := Q20 Qmods
    ∃ M : ℕ, 0 < M ∧ M = ∏ z ∈ S, z ∧ ∀ T : ℕ,
      2 * (T * M) ≤ (S.card + 1) * (S.card + 2) *
        (Q23 C (Q16 A X)
          (Q2 n) p (T * M)).card := by
  classical
  let W := 2 * w + 1
  let A := D - w
  let p := (4 * n K) * 2 ^ V
  let scale := 4 * 2 ^ V
  let C := Q25
    n K G W A X p w Block
  let Qmods := Q22
    n K G W A X p w Block
  have hcenterLow : A + w = D := by dsimp [A]; omega
  have hcenterHigh : A + w + X = n K * (2 * v + 1) := by
    rw [hcenterLow]
    exact hX
  have hQdata : ∀ q ∈ Qmods, Odd q ∧ 3 ≤ q := by
    intro q hqQ
    obtain ⟨u, huC, rfl⟩ := Finset.mem_image.mp hqQ
    have huOld := (Finset.mem_filter.mp huC).1
    have huNot := (Finset.mem_filter.mp huC).2
    have huCompat := (Finset.mem_filter.mp huOld).1
    have huCenter := (Finset.mem_filter.mp huOld).2
    have huBase := (Finset.mem_filter.mp huCompat).1
    have huComp := (Finset.mem_filter.mp huCompat).2
    have huPair := Finset.mem_product.mp (Finset.mem_product.mp huBase).1
    have hjData := Finset.mem_filter.mp huPair.1
    have hjG := Finset.mem_range.mp hjData.1
    have hKj := hjData.2
    have hm := hmono hKj
    have hord := horder u.1.1 hKj hjG huNot
    by_cases hside : u.2 = true
    · have hc : (n u.1.1).gcd p ∣ n K * (2 * v + 1) := by
        simpa [Q2, Q16, hside, huCenter,
          A, hcenterHigh] using huComp
      simpa [Q2, p] using
        Q261
          (n u.1.1) (n K) V v hm (hpos K) hord (by simpa [p] using hc)
    · have hsideFalse : u.2 = false := Bool.eq_false_of_not_eq_true hside
      have hc : (n u.1.1).gcd p ∣ D := by
        simpa [Q2, Q16, hsideFalse, huCenter,
          A, hcenterLow] using huComp
      simpa [Q2, p] using
        Q270
          (n u.1.1) (n K) D V hm (hpos K) (by omega) hord
            (by simpa [p] using hc) hDn
  have hQscale : ∀ q ∈ Qmods, q.gcd scale = 1 := by
    intro q hq
    have ho := (hQdata q hq).1
    have hc : q.Coprime (2 ^ (V + 2)) :=
      (Nat.coprime_two_right.mpr ho).pow_right (V + 2)
    have hs : scale = 2 ^ (V + 2) := by
      dsimp [scale]
      rw [pow_succ, pow_succ]
      ring
    rw [hs]
    exact hc.gcd_eq_one
  apply Q110
    Qmods C (fun u => u.2) (Q16 A X)
      (Q2 n) p Q scale (2 * v + 1)
  · exact fun q hq => (hQdata q hq).2
  · exact fun q hq => (hQdata q hq).1
  · exact hQscale
  · intro u huC
    have huOld := (Finset.mem_filter.mp huC).1
    have huCompat := (Finset.mem_filter.mp huOld).1
    have huCenter := (Finset.mem_filter.mp huOld).2
    have huComp := (Finset.mem_filter.mp huCompat).2
    let m := n u.1.1
    let g := m.gcd p
    let q := m / g
    refine ⟨q, Finset.mem_image.mpr ⟨u, huC, rfl⟩, ?_, ?_⟩
    · intro hsideFalse
      have hcompLow : g ∣ D := by
        simpa [g, m, Q2, Q16, hsideFalse,
          huCenter, A, hcenterLow] using huComp
      have hgpos : 0 < g := by
        dsimp [g, m, p]
        exact Nat.gcd_pos_of_pos_left _ (hpos u.1.1)
      have hcopFull : q.Coprime (p / g) := by
        dsimp [q, g, m]
        exact Nat.coprime_div_gcd_div_gcd hgpos
      have hgQp : g * Q ∣ p := by
        obtain ⟨z, hz⟩ := hcompLow
        refine ⟨scale * z, ?_⟩
        dsimp [p, scale] at *
        rw [hQ, hz]
        ring
      have hQdiv : Q ∣ p / g := by
        apply (Nat.dvd_div_iff_mul_dvd
          (by dsimp [g]; exact Nat.gcd_dvd_right _ _)).mpr
        simpa [mul_comm] using hgQp
      exact (hcopFull.of_dvd_right hQdiv).gcd_eq_one
    · intro t hbad
      by_cases hside : u.2 = true
      · have hc : g ∣ n K * (2 * v + 1) := by
          simpa [g, m, Q2, Q16, hside,
            huCenter, A, hcenterHigh] using huComp
        simp only [hside, ite_true]
        apply (Q226
          m (n K) V v t (hpos u.1.1) (by simpa [g, m, p] using hc)).mp
        simpa [m, p, Q2, Q16, hside,
          huCenter, A, hcenterHigh] using hbad
      · have hsideFalse : u.2 = false := Bool.eq_false_of_not_eq_true hside
        have hc : g ∣ D := by
          simpa [g, m, Q2, Q16, hsideFalse,
            huCenter, A, hcenterLow] using huComp
        simp only [hsideFalse, Bool.false_eq_true, ↓reduceIte]
        apply (Q239
          m (n K) D Q V t (hpos u.1.1) hQ
            (by simpa [g, m, p] using hc)).mp
        simpa [m, p, Q2, Q16, hsideFalse,
          huCenter, A, hcenterLow] using hbad
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
theorem Q262
    (n : ℕ → ℕ) (K H W A X p w : ℕ) (Block : Finset ℕ) :
    Q76 n K H W A X p w Block ⊆
      Q44 n K H W A X p w := by
  intro u hu
  have huData := Finset.mem_sdiff.mp hu
  have huOutside := huData.1
  have huNotCenter := huData.2
  have huOutsideData := Finset.mem_filter.mp huOutside
  have huOldCompat : u ∈ Q18 n K H W A X p :=
    Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp huOutsideData.1).1, huOutsideData.2⟩
  apply Finset.mem_sdiff.mpr
  refine ⟨huOldCompat, ?_⟩
  intro huOldCenter
  apply huNotCenter
  exact Finset.mem_filter.mpr
    ⟨huOldCenter, (Finset.mem_filter.mp huOutsideData.1).2⟩
theorem Q271
    (n : ℕ → ℕ) (K G H W A X p w : ℕ) (Block : Finset ℕ) :
    let C0 := Q25
      n K G W A X p w Block
    let O := Q14 n K H W A X p Block \ C0
    let Oall := Q76
      n K H W A X p w Block
    O ⊆ Oall ∪ Q53 G H w w := by
  classical
  dsimp only
  intro u huO
  have huData := Finset.mem_sdiff.mp huO
  have huCompatH := huData.1
  have huNotC0 := huData.2
  by_cases huCH : u ∈ Q25
      n K H W A X p w Block
  · apply Finset.mem_union.mpr
    right
    have huOldCenter := (Finset.mem_filter.mp huCH).1
    have huCenter := (Finset.mem_filter.mp huOldCenter).2
    have huCompat := (Finset.mem_filter.mp huOldCenter).1
    have huBase := (Finset.mem_filter.mp huCompat).1
    have huOuter := Finset.mem_product.mp huBase
    have huInner := Finset.mem_product.mp huOuter.1
    have hjRange := Finset.mem_filter.mp huInner.1
    have hjH := Finset.mem_range.mp hjRange.1
    have hKj := hjRange.2
    have hGj : G ≤ u.1.1 := by
      by_contra hnot
      have hjG : u.1.1 < G := by omega
      apply huNotC0
      apply Finset.mem_filter.mpr
      refine ⟨?_, (Finset.mem_filter.mp huCH).2⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, huCenter⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, (Finset.mem_filter.mp huCompat).2⟩
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, huInner.2⟩, huOuter.2⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjG, hKj⟩
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ⟨hGj, hjH⟩,
      ?_⟩, Finset.mem_univ _⟩
    simp [huCenter]
  · exact Finset.mem_union.mpr (Or.inl
      (Finset.mem_sdiff.mpr ⟨huCompatH, huCH⟩))
theorem Q158
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (K G H w D Q X V v R B : ℕ) (Block : Finset ℕ)
    (hKH : K < H) (hw : 0 < w) (hD : w < D) (hB : 0 < B)
    (hQ : n K = Q * D) (hX : D + X = n K * (2 * v + 1))
    (hsize : 2 * (4 * 2 ^ V) * B ^ 2 * w ≤ n K) :
    let W := 2 * w + 1
    let A := D - w
    let p := (4 * n K) * 2 ^ V
    let Z := (4 * 2 ^ V) * w
    let C0 := Q25
      n K G W A X p w Block
    let O := Q14 n K H W A X p Block \ C0
    ((∑ u ∈ O, (R / (Q2 n u /
      (Q2 n u).gcd p) + 1) : ℕ) : ℝ) ≤
      (4 * (R : ℝ) * W *
          (∑ j ∈ Q0 K H, ((n j : ℝ)⁻¹)) +
        4 * W * (Q0 K H).card) +
      2 * (∑ j ∈ Q0 K H,
        ((R : ℝ) * Z / n j + 1)) +
      2 * (Q0 K H).card * ((R : ℝ) / B + 1) +
      4 * ((R : ℝ) * p *
        (∑ j ∈ Finset.Ico G H, ((n j : ℝ)⁻¹)) +
        (Finset.Ico G H).card) := by
  classical
  let W := 2 * w + 1
  let A := D - w
  let p := (4 * n K) * 2 ^ V
  let Z := (4 * 2 ^ V) * w
  let C0 := Q25
    n K G W A X p w Block
  let O := Q14 n K H W A X p Block \ C0
  let Oall := Q76
    n K H W A X p w Block
  let Full := Q44 n K H W A X p w
  let Late := Q53 G H w w
  have hsub : O ⊆ Oall ∪ Late :=
    Q271 n K G H W A X p w Block
  let cost : ((ℕ × ℕ) × Bool) → ℕ := fun u =>
    R / (Q2 n u /
      (Q2 n u).gcd p) + 1
  have hsplitNat : (∑ u ∈ O, cost u) ≤
      (∑ u ∈ Oall, cost u) + ∑ u ∈ Late, cost u := by
    calc
      _ ≤ ∑ u ∈ Oall ∪ Late, cost u := Finset.sum_le_sum_of_subset hsub
      _ ≤ _ := by
        have hu := Finset.sum_union_inter (s₁ := Oall) (s₂ := Late)
          (f := cost)
        omega
  have hsplit : (((∑ u ∈ O, cost u) : ℕ) : ℝ) ≤
      (((∑ u ∈ Oall, cost u) : ℕ) : ℝ) +
        (((∑ u ∈ Late, cost u) : ℕ) : ℝ) := by exact_mod_cast hsplitNat
  have hOsub : Oall ⊆ Full :=
    Q262 n K H W A X p w Block
  have hOnat : (∑ u ∈ Oall, cost u) ≤ ∑ u ∈ Full, cost u :=
    Finset.sum_le_sum_of_subset hOsub
  have hOcast : (((∑ u ∈ Oall, cost u) : ℕ) : ℝ) ≤
      (((∑ u ∈ Full, cost u) : ℕ) : ℝ) := by exact_mod_cast hOnat
  have hfull := Q291
    n hpos hmono K H w D Q X V v R B hKH hw hD hB hQ hX hsize
  have hfull' : (((∑ u ∈ Full, cost u) : ℕ) : ℝ) ≤
      (4 * (R : ℝ) * W *
          (∑ j ∈ Q0 K H, ((n j : ℝ)⁻¹)) +
        4 * W * (Q0 K H).card) +
      2 * (∑ j ∈ Q0 K H,
        ((R : ℝ) * Z / n j + 1)) +
      2 * (Q0 K H).card * ((R : ℝ) / B + 1) := by
    simpa [Full, cost, W, A, p, Z] using hfull
  have hp : 0 < p := by
    dsimp [p]
    exact mul_pos (mul_pos (by norm_num) (hpos K)) (pow_pos (by norm_num) V)
  have hlate := Q275
    n hpos G H w w p R hp
  exact hsplit.trans (add_le_add (hOcast.trans hfull')
    (by simpa [Late, cost, p] using hlate))
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
set_option maxHeartbeats 1200000 in
theorem Q139
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (K G H w Dtarget Q X V v B : ℕ) (Block : Finset ℕ)
    (hKG : K < G) (hKH : K < H) (hw : 0 < w)
    (hDtarget : w < Dtarget) (hDlt : Dtarget < n K) (hB : 0 < B)
    (hQ : n K = Q * Dtarget)
    (hX : Dtarget + X = n K * (2 * v + 1))
    (horder : ∀ j, K < j → j < G → j ∉ Block →
      Q15 (n j) ≤ V)
    (hsize : 2 * (4 * 2 ^ V) * B ^ 2 * w ≤ n K)
    (hdensity :
      let W := 2 * w + 1
      let A := Dtarget - w
      let p := (4 * n K) * 2 ^ V
      let Z := (4 * 2 ^ V) * w
      let Qmods := Q22
        n K G W A X p w Block
      let S := Q20 Qmods
      let D := (S.card + 1) * (S.card + 2)
      let Z₁ := (Q0 K H).card
      let sigma₁ := ∑ j ∈ Q0 K H, ((n j : ℝ)⁻¹)
      let sigma₂ := ∑ j ∈ Finset.Ico G H, ((n j : ℝ)⁻¹)
      (D : ℝ) *
        (4 * W * sigma₁ + 2 * Z * sigma₁ +
          2 * Z₁ / B + 4 * p * sigma₂) < 1) :
    let W := 2 * w + 1
    let A := Dtarget - w
    let p := (4 * n K) * 2 ^ V
    let C0 := Q25
      n K G W A X p w Block
    let O := Q14 n K H W A X p Block \ C0
    let Qmods := Q22
      n K G W A X p w Block
    let S := Q20 Qmods
    let D := (S.card + 1) * (S.card + 2)
    let Z₁ := (Q0 K H).card
    let Z₂ := (Finset.Ico G H).card
    ∃ M R : ℕ,
      0 < M ∧ M = ∏ z ∈ S, z ∧ 0 < R ∧
      (∑ u ∈ O, (R / (Q2 n u /
        (Q2 n u).gcd p) + 1)) <
        (Q23 C0 (Q16 A X)
          (Q2 n) p R).card ∧
      R ≤ M + D * (4 * W * Z₁ + 4 * Z₁ + 4 * Z₂) := by
  classical
  let W := 2 * w + 1
  let A := Dtarget - w
  let p := (4 * n K) * 2 ^ V
  let Z := (4 * 2 ^ V) * w
  let C0 := Q25
    n K G W A X p w Block
  let O := Q14 n K H W A X p Block \ C0
  let Qmods := Q22
    n K G W A X p w Block
  let S := Q20 Qmods
  let D := (S.card + 1) * (S.card + 2)
  let Z₁ := (Q0 K H).card
  let Z₂ := (Finset.Ico G H).card
  let sigma₁ : ℝ := ∑ j ∈ Q0 K H, ((n j : ℝ)⁻¹)
  let sigma₂ : ℝ := ∑ j ∈ Finset.Ico G H, ((n j : ℝ)⁻¹)
  let alpha : ℝ := 4 * W * sigma₁ + 2 * Z * sigma₁ +
    2 * Z₁ / B + 4 * p * sigma₂
  let endpoint : ℕ := 4 * W * Z₁ + 4 * Z₁ + 4 * Z₂
  have hdensity' : (D : ℝ) * alpha < 1 := by
    simpa [W, A, p, Z, Qmods, S, D, Z₁, sigma₁, sigma₂, alpha]
      using hdensity
  obtain ⟨M, hM, hMeq, hprotected⟩ :=
    Q90
      n hpos hmono K G w Dtarget Q X V v Block hKG hDtarget hDlt hQ hX
        horder
  have hDpos : 0 < D := by dsimp [D]; positivity
  let delta : ℝ := 2 - (D : ℝ) * alpha
  have hdeltaOne : 1 < delta := by dsimp [delta]; nlinarith
  have hdelta : 0 < delta := lt_trans (by norm_num) hdeltaOne
  have hden : 0 < delta * (M : ℝ) :=
    mul_pos hdelta (by exact_mod_cast hM)
  let E : ℕ := D * endpoint
  let q : ℝ := (E : ℝ) / (delta * (M : ℝ))
  let T : ℕ := ⌊q⌋₊ + 1
  have hqnonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (by positivity) hden.le
  have hqT : q < (T : ℝ) := by
    dsimp [T]
    simpa using Nat.lt_floor_add_one q
  have hTpos : 0 < T := by dsimp [T]; omega
  let R := T * M
  have hRpos : 0 < R := mul_pos hTpos hM
  have hendpoint : (E : ℝ) < delta * (R : ℝ) := by
    have hm : (E : ℝ) < (T : ℝ) * (delta * (M : ℝ)) := by
      apply (div_lt_iff₀ hden).mp
      simpa [q] using hqT
    calc
      (E : ℝ) < (T : ℝ) * (delta * (M : ℝ)) := hm
      _ = delta * (R : ℝ) := by dsimp [R]; push_cast; ring
  have hRbound : R ≤ M + E := by
    have hfloor : ((⌊q⌋₊ : ℕ) : ℝ) ≤ q := Nat.floor_le hqnonneg
    have hTle : (T : ℝ) ≤ q + 1 := by
      dsimp [T]
      push_cast
      linarith
    have hqM : q * (M : ℝ) = (E : ℝ) / delta := by
      dsimp [q]
      field_simp
    have hdivle : (E : ℝ) / delta ≤ (E : ℝ) := by
      apply (div_le_iff₀ hdelta).mpr
      have hEnonneg : (0 : ℝ) ≤ E := by positivity
      nlinarith
    have hreal : (R : ℝ) ≤ (M + E : ℕ) := by
      calc
        (R : ℝ) = (T : ℝ) * (M : ℝ) := by simp [R]
        _ ≤ (q + 1) * (M : ℝ) := by gcongr
        _ = q * (M : ℝ) + (M : ℝ) := by ring
        _ = (E : ℝ) / delta + (M : ℝ) := by rw [hqM]
        _ ≤ (E : ℝ) + (M : ℝ) := by gcongr
        _ = (M + E : ℕ) := by push_cast; ring
    exact_mod_cast hreal
  let Budget := ∑ u ∈ O, (R / (Q2 n u /
    (Q2 n u).gcd p) + 1)
  have hBudgetReal : (Budget : ℝ) ≤ (R : ℝ) * alpha + endpoint := by
    have hb := Q158
      n hpos hmono K G H w Dtarget Q X V v R B Block
        hKH hw hDtarget hB hQ hX hsize
    have hb' : (Budget : ℝ) ≤
        (4 * (R : ℝ) * W * sigma₁ + 4 * W * Z₁) +
        2 * (∑ j ∈ Q0 K H,
          ((R : ℝ) * Z / n j + 1)) +
        2 * Z₁ * ((R : ℝ) / B + 1) +
        4 * ((R : ℝ) * p * sigma₂ + Z₂) := by
      simpa [Budget, O, C0, W, A, p, Z, sigma₁, sigma₂, Z₁, Z₂]
        using hb
    calc
      (Budget : ℝ) ≤
          (4 * (R : ℝ) * W * sigma₁ + 4 * W * Z₁) +
          2 * (∑ j ∈ Q0 K H,
            ((R : ℝ) * Z / n j + 1)) +
          2 * Z₁ * ((R : ℝ) / B + 1) +
          4 * ((R : ℝ) * p * sigma₂ + Z₂) := hb'
      _ = (R : ℝ) * alpha + endpoint := by
        dsimp [alpha, endpoint]
        push_cast
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hsum : ∑ j ∈ Q0 K H,
            ((R : ℝ) * Z / n j) = (R : ℝ) * Z * sigma₁ := by
          dsimp [sigma₁]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        rw [hsum]
        ring
  have hDBudget : D * Budget < 2 * R := by
    have hmain : (D : ℝ) * (Budget : ℝ) < 2 * (R : ℝ) := by
      have hscaled := mul_le_mul_of_nonneg_left hBudgetReal
        (show (0 : ℝ) ≤ D by positivity)
      dsimp [delta, E] at hendpoint
      push_cast at hendpoint hscaled
      nlinarith
    exact_mod_cast hmain
  have hprot := hprotected T
  have hBudgetCard : Budget <
      (Q23 C0 (Q16 A X)
        (Q2 n) p R).card := by
    have hchain : D * Budget < D *
        (Q23 C0 (Q16 A X)
          (Q2 n) p R).card := by
      calc
        D * Budget < 2 * R := hDBudget
        _ ≤ D * (Q23 C0 (Q16 A X)
          (Q2 n) p R).card := by
            simpa [R, D, S, Qmods, C0, W, A, p] using hprot
    exact (Nat.mul_lt_mul_left hDpos).mp hchain
  refine ⟨M, R, hM, ?_, hRpos, hBudgetCard, ?_⟩
  · simpa [S, Qmods, W, A, p] using hMeq
  · simpa [E, endpoint, D, Z₁, Z₂, S, Qmods, W, A, p] using hRbound
end OMAH1Research
namespace OMAH1Research
theorem Q208
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (q : ℕ) (hq : (2 : ℝ) ≤ c ^ q)
    (K W : ℕ) (hW : 0 < W) :
    let B := n K * W ^ 8
    let l := Nat.clog 2 W
    let Q := q * (8 * l + 1)
    ∃ G : ℕ, K < G ∧ B < n G ∧
      (∀ j, K < j → j < G → n j ≤ B) ∧
      G ≤ K + Q ∧ (Q0 K G).card ≤ Q := by
  let B := n K * W ^ 8
  let l := Nat.clog 2 W
  let Q := q * (8 * l + 1)
  have hWle : W ≤ 2 ^ l := by
    dsimp [l]
    exact Nat.le_pow_clog (by norm_num) W
  have hWpow : W ^ 8 < 2 ^ (8 * l + 1) := by
    have hp : W ^ 8 ≤ (2 ^ l) ^ 8 := Nat.pow_le_pow_left hWle 8
    calc
      W ^ 8 ≤ (2 ^ l) ^ 8 := hp
      _ = 2 ^ (8 * l) := by rw [← pow_mul]; congr 1; omega
      _ < 2 ^ (8 * l + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hbase : (2 : ℝ) ^ (8 * l + 1) ≤
      (c ^ q) ^ (8 * l + 1) :=
    pow_le_pow_left₀ (by norm_num) hq (8 * l + 1)
  have hcQ : (2 : ℝ) ^ (8 * l + 1) ≤ c ^ Q := by
    calc
      _ ≤ (c ^ q) ^ (8 * l + 1) := hbase
      _ = c ^ (q * (8 * l + 1)) := (pow_mul c q (8 * l + 1)).symm
      _ = c ^ Q := rfl
  have hcross : (B : ℝ) < c ^ Q * (n K : ℝ) := by
    have hnreal : (0 : ℝ) < n K := by exact_mod_cast hpos K
    have hpowReal : ((W ^ 8 : ℕ) : ℝ) <
        (2 : ℝ) ^ (8 * l + 1) := by exact_mod_cast hWpow
    have hlt : ((W ^ 8 : ℕ) : ℝ) < c ^ Q := hpowReal.trans_le hcQ
    have hm := mul_lt_mul_of_pos_right hlt hnreal
    simpa [B, mul_comm] using hm
  have hKB : n K ≤ B := by
    dsimp [B]
    have hone : 1 ≤ W ^ 8 := one_le_pow₀ (by omega)
    nlinarith
  exact Q115
    n hmono c hc hratio K B Q hKB hcross
end OMAH1Research
namespace OMAH1Research
open scoped BigOperators
theorem Q272
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (K G H w Dtarget X V B : ℕ) (Block : Finset ℕ)
    (hbound :
      let W := 2 * w + 1
      let p := (4 * n K) * 2 ^ V
      let Z := (4 * 2 ^ V) * w
      let d := (Q0 K G).card
      let Dmax := (2 * d + 1) * (2 * d + 2)
      (Dmax : ℝ) *
        ((4 * W + 2 * Z) *
            (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
          2 * H / B +
          4 * p * ((1 - c⁻¹)⁻¹ * (n G : ℝ)⁻¹)) < 1) :
    let W := 2 * w + 1
    let A := Dtarget - w
    let p := (4 * n K) * 2 ^ V
    let Z := (4 * 2 ^ V) * w
    let Qmods := Q22
      n K G W A X p w Block
    let S := Q20 Qmods
    let D := (S.card + 1) * (S.card + 2)
    let Z₁ := (Q0 K H).card
    let sigma₁ := ∑ j ∈ Q0 K H, ((n j : ℝ)⁻¹)
    let sigma₂ := ∑ j ∈ Finset.Ico G H, ((n j : ℝ)⁻¹)
    (D : ℝ) *
      (4 * W * sigma₁ + 2 * Z * sigma₁ +
        2 * Z₁ / B + 4 * p * sigma₂) < 1 := by
  let W := 2 * w + 1
  let A := Dtarget - w
  let p := (4 * n K) * 2 ^ V
  let Z := (4 * 2 ^ V) * w
  let Qmods := Q22
    n K G W A X p w Block
  let S := Q20 Qmods
  let d := (Q0 K G).card
  let D := (S.card + 1) * (S.card + 2)
  let Dmax := (2 * d + 1) * (2 * d + 2)
  let Z₁ := (Q0 K H).card
  let sigma₁ : ℝ := ∑ j ∈ Q0 K H, ((n j : ℝ)⁻¹)
  let sigma₂ : ℝ := ∑ j ∈ Finset.Ico G H, ((n j : ℝ)⁻¹)
  have hScard : S.card ≤ 2 * d :=
    Q58
      n K G W A X p w Block
  have hD : D ≤ Dmax := by
    dsimp [D, Dmax]
    exact Nat.mul_le_mul (Nat.add_le_add_right hScard 1)
      (Nat.add_le_add_right hScard 2)
  have htail₁ := Q157
    n hpos c hc hratio K H
  have htail₂ := Q319 n hpos c hc hratio G H
  have hZ₁ : Z₁ ≤ H := by
    dsimp [Z₁]
    calc
      (Q0 K H).card ≤ (Finset.range H).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = H := Finset.card_range H
  have hinner :
      4 * (W : ℝ) * sigma₁ + 2 * (Z : ℝ) * sigma₁ +
          2 * (Z₁ : ℝ) / B + 4 * (p : ℝ) * sigma₂ ≤
        (4 * W + 2 * Z) *
            (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
          2 * H / B +
          4 * p * ((1 - c⁻¹)⁻¹ * (n G : ℝ)⁻¹) := by
    have hBnonneg : (0 : ℝ) ≤ B := by positivity
    have hZcast : (Z₁ : ℝ) ≤ H := by exact_mod_cast hZ₁
    calc
      4 * (W : ℝ) * sigma₁ + 2 * (Z : ℝ) * sigma₁ +
          2 * (Z₁ : ℝ) / B + 4 * (p : ℝ) * sigma₂ ≤
        4 * W * (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
          2 * Z * (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
          2 * H / B +
          4 * p * ((1 - c⁻¹)⁻¹ * (n G : ℝ)⁻¹) := by
            gcongr
      _ = (4 * W + 2 * Z) *
            (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
          2 * H / B +
          4 * p * ((1 - c⁻¹)⁻¹ * (n G : ℝ)⁻¹) := by ring
  have hDreal : (D : ℝ) ≤ Dmax := by exact_mod_cast hD
  calc
    (D : ℝ) * (4 * W * sigma₁ + 2 * Z * sigma₁ +
        2 * Z₁ / B + 4 * p * sigma₂) ≤
      (Dmax : ℝ) *
        ((4 * W + 2 * Z) *
            (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
          2 * H / B +
          4 * p * ((1 - c⁻¹)⁻¹ * (n G : ℝ)⁻¹)) := by
      gcongr
    _ < 1 := by simpa [W, p, Z, d, Dmax] using hbound
def Q31
    (n : ℕ → ℕ) (K G Bval w Dtarget X V q : ℕ) : ℕ :=
  let W := 2 * w + 1
  let A := Dtarget - w
  let p := (4 * n K) * 2 ^ V
  let d := (Q0 K G).card
  let Dmax := (2 * d + 1) * (2 * d + 2)
  let Mmax := Bval ^ (2 * d)
  let U := A + p * Mmax + X + W
  let Vaff := 12 * p * Dmax * W
  let A₀ := U + Vaff * G
  let B₀ := Vaff * q
  let N := A₀ + B₀ + 1
  let t := Nat.clog 2 N
  G + q * (4 * t + 4)
theorem Q175
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (qratio : ℕ) (hq : (2 : ℝ) ≤ c ^ qratio)
    (K G Bval w Dtarget Q X V v Bexc : ℕ) (Block : Finset ℕ)
    (hKG : K < G) (hBval : 0 < Bval)
    (hvalues : ∀ j, K < j → j < G → n j ≤ Bval)
    (hw : 0 < w) (hDtarget : w < Dtarget) (hDlt : Dtarget < n K)
    (hBexc : 0 < Bexc) (hQ : n K = Q * Dtarget)
    (hX : Dtarget + X = n K * (2 * v + 1))
    (horder : ∀ j, K < j → j < G → j ∉ Block →
      Q15 (n j) ≤ V)
    (hsize : 2 * (4 * 2 ^ V) * Bexc ^ 2 * w ≤ n K)
    (hdensity :
      let W := 2 * w + 1
      let p := (4 * n K) * 2 ^ V
      let Z := (4 * 2 ^ V) * w
      let d := (Q0 K G).card
      let Dmax := (2 * d + 1) * (2 * d + 2)
      let H := Q31
        n K G Bval w Dtarget X V qratio
      (Dmax : ℝ) *
        ((4 * W + 2 * Z) *
            (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
          2 * H / Bexc +
          4 * p * ((1 - c⁻¹)⁻¹ * (n G : ℝ)⁻¹)) < 1) :
    let W := 2 * w + 1
    let A := Dtarget - w
    let p := (4 * n K) * 2 ^ V
    let H := Q31
      n K G Bval w Dtarget X V qratio
    let C0 := Q25
      n K G W A X p w Block
    ∃ R : ℕ, 0 < R ∧
      let O := Q14 n K H W A X p Block \ C0
      (∑ u ∈ O, (R / (Q2 n u /
        (Q2 n u).gcd p) + 1)) <
        (Q23 C0 (Q16 A X)
          (Q2 n) p R).card ∧
      A + p * R + X + W < n H := by
  classical
  let W := 2 * w + 1
  let A := Dtarget - w
  let p := (4 * n K) * 2 ^ V
  let d := (Q0 K G).card
  let Dmax := (2 * d + 1) * (2 * d + 2)
  let Mmax := Bval ^ (2 * d)
  let U := A + p * Mmax + X + W
  let Vaff := 12 * p * Dmax * W
  let A₀ := U + Vaff * G
  let B₀ := Vaff * qratio
  let N := A₀ + B₀ + 1
  let t := Nat.clog 2 N
  let H := G + qratio * (4 * t + 4)
  have hAff := Q83
    n hpos c hc hratio qratio hq G U Vaff
  have hGH : G ≤ H := by omega
  have hKH : K < H := hKG.trans_le hGH
  have haffine : U + Vaff * H < n H := by
    simpa [A₀, B₀, N, t, H] using hAff.2
  have hdensityH := Q272
    n hpos c hc hratio K G H w Dtarget X V Bexc Block
      (by simpa [W, p, d, Dmax, H,
        Q31, A₀, B₀, N, t, U, Vaff]
        using hdensity)
  obtain ⟨M, R, hM, hMeq, hR, hbudget, hRbound⟩ :=
    Q139
      n hpos hmono K G H w Dtarget Q X V v Bexc Block hKG hKH hw
        hDtarget hDlt hBexc hQ hX horder hsize hdensityH
  have hMle : M ≤ Mmax := by
    rw [hMeq]
    dsimp [Mmax]
    exact Q119
      n hpos K G W A X p w Bval Block hBval hvalues
  let Qmods := Q22
    n K G W A X p w Block
  let S := Q20 Qmods
  let Dfac := (S.card + 1) * (S.card + 2)
  have hDle : Dfac ≤ Dmax := by
    have hScard : S.card ≤ 2 * d :=
      Q58
        n K G W A X p w Block
    dsimp [Dfac, Dmax]
    exact Nat.mul_le_mul (Nat.add_le_add_right hScard 1)
      (Nat.add_le_add_right hScard 2)
  have hZ₁ : (Q0 K H).card ≤ H := by
    calc
      _ ≤ (Finset.range H).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = H := Finset.card_range H
  have hZ₂ : (Finset.Ico G H).card ≤ H := by simp
  have hendpoint : Dfac *
      (4 * W * (Q0 K H).card +
        4 * (Q0 K H).card +
        4 * (Finset.Ico G H).card) ≤
      12 * Dmax * W * H := by
    calc
      _ ≤ Dmax * (4 * W * H + 4 * H + 4 * H) := by gcongr
      _ ≤ Dmax * (12 * W * H) := by
        gcongr
        have hWpos : 0 < W := by dsimp [W]; omega
        nlinarith
      _ = 12 * Dmax * W * H := by ring
  have hRcoarse : R ≤ Mmax + 12 * Dmax * W * H := by
    calc
      R ≤ M + Dfac *
          (4 * W * (Q0 K H).card +
            4 * (Q0 K H).card +
            4 * (Finset.Ico G H).card) := by
        simpa [Dfac, S, Qmods, W, A, p] using hRbound
      _ ≤ Mmax + 12 * Dmax * W * H :=
        Nat.add_le_add hMle hendpoint
  have hcut : A + p * R + X + W < n H := by
    have hcost : A + p * R + X + W ≤ U + Vaff * H := by
      calc
        _ ≤ A + p * (Mmax + 12 * Dmax * W * H) + X + W := by gcongr
        _ = U + Vaff * H := by dsimp [U, Vaff]; ring
    exact hcost.trans_lt haffine
  refine ⟨R, hR, ?_⟩
  simpa [W, A, p, H, Q31,
    d, Dmax, Mmax, U, Vaff, A₀, B₀, N, t] using And.intro hbudget hcut
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
open scoped BigOperators
theorem Q149
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (qden : ℕ) (hqden : 0 < qden) (T Tconj : ℝ)
    (hsum : HasSum (fun m : ℕ =>
      (Q1 n m : ℝ) * (φ⁻¹) ^ m) T)
    (htotal : InScaledGoldenPair qden T Tconj)
    (qratio : ℕ) (hq : (2 : ℝ) ≤ c ^ qratio)
    (K G Bval w Dtarget Q X V v Bexc : ℕ) (Block : Finset ℕ)
    (hKG : K < G) (hBval : 0 < Bval)
    (hvalues : ∀ j, K < j → j < G → n j ≤ Bval)
    (hw : 0 < w) (hDtarget : w < Dtarget) (hDlt : Dtarget < n K)
    (hBexc : 0 < Bexc) (hQ : n K = Q * Dtarget)
    (hXcenter : Dtarget + X = n K * (2 * v + 1))
    (horder : ∀ j, K < j → j < G → j ∉ Block →
      Q15 (n j) ≤ V)
    (hsize : 2 * (4 * 2 ^ V) * Bexc ^ 2 * w ≤ n K)
    (hKB : K ∈ Block) (hBlockUpper : ∀ k ∈ Block, k < G)
    (hprefix : Q12 n K ∣ X)
    (hblockPeriod : ∀ k ∈ Block,
      Q11 (n k) ∣ (4 * n K) * 2 ^ V)
    (htargetPre : ∀ s < w,
      Q4 n Block (Dtarget - w + s + X) =
        Q4 n Block (Dtarget - w + s))
    (htarget : Q4 n Block
        (Dtarget - w + w + X) ≠
      Q4 n Block (Dtarget - w + w))
    (htargetPost : ∀ s < w,
      Q4 n Block
          (Dtarget - w + w + 1 + s + X) =
        Q4 n Block
          (Dtarget - w + w + 1 + s))
    (hdensity :
      let W := 2 * w + 1
      let p := (4 * n K) * 2 ^ V
      let Z := (4 * 2 ^ V) * w
      let d := (Q0 K G).card
      let Dmax := (2 * d + 1) * (2 * d + 2)
      let H := Q31
        n K G Bval w Dtarget X V qratio
      (Dmax : ℝ) *
        ((4 * W + 2 * Z) *
            (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
          2 * H / Bexc +
          4 * p * ((1 - c⁻¹)⁻¹ * (n G : ℝ)⁻¹)) < 1)
    (hpostCap :
      let H := Q31
        n K G Bval w Dtarget X V qratio
      (φ⁻¹) ^ (w + 1) * (2 * Q8 H) < 1)
    (hpreCap :
      let H := Q31
        n K G Bval w Dtarget X V qratio
      (φ⁻¹) ^ w * (2 * Q8 H) *
        (2 * Q10 Tconj H) <
        (((qden : ℕ) : ℝ)⁻¹) ^ 2) :
    False := by
  classical
  let W := 2 * w + 1
  let A := Dtarget - w
  let p := (4 * n K) * 2 ^ V
  let H := Q31
    n K G Bval w Dtarget X V qratio
  let C0 := Q25
    n K G W A X p w Block
  let O := Q14 n K H W A X p Block \ C0
  obtain ⟨R, hR, hbudget, hcut⟩ :=
    Q175
      n hpos hmono c hc hratio qratio hq K G Bval w Dtarget Q X V v
        Bexc Block hKG hBval hvalues hw hDtarget hDlt hBexc hQ hXcenter
        horder hsize hdensity
  have hA : 0 < A := by dsimp [A]; omega
  have hWeq : W = w + 1 + w := by dsimp [W]; omega
  have hGH : G ≤ H := by
    dsimp [H, Q31]
    omega
  have hKH : K < H := hKG.trans_le hGH
  have hCsub : C0 ⊆
      Q14 n K H W A X p Block := by
    intro u hu
    have huOldG := (Finset.mem_filter.mp hu).1
    have huNot := (Finset.mem_filter.mp hu).2
    have huCompatG := (Finset.mem_filter.mp huOldG).1
    have huCenter := (Finset.mem_filter.mp huOldG).2
    have huData := Finset.mem_filter.mp huCompatG
    have huOuter := Finset.mem_product.mp huData.1
    have huInner := Finset.mem_product.mp huOuter.1
    have hjData := Finset.mem_filter.mp huInner.1
    apply Finset.mem_filter.mpr
    refine ⟨?_, huData.2⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, huNot⟩
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, huInner.2⟩, huOuter.2⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hjData.1).trans_le hGH),
        hjData.2⟩
  have hpartition : C0 ∪ O =
      Q14 n K H W A X p Block :=
    Finset.union_sdiff_of_subset hCsub
  have hperiod : ∀ k < K, Q11 (n k) ∣ X := by
    intro k hk
    exact dvd_trans (Q71 n hk) hprefix
  have hp : 0 < p := by
    dsimp [p]
    exact mul_pos (mul_pos (by norm_num) (hpos K)) (pow_pos (by norm_num) V)
  have hnorm := Q146
    n hpos hmono qden Tconj H w w A X p R hp
      (by simpa [A, p, H, ← hWeq] using hcut)
      (by simpa [H] using hpostCap)
      (by simpa [H] using hpreCap)
  exact Q123
    n hpos hmono qden hqden T Tconj hsum htotal
      K H w w A X p R Block hA hKH hKB
      (fun k hk => (hBlockUpper k hk).trans_le hGH)
      hperiod hblockPeriod
      (by simpa [A] using htargetPre)
      (by simpa [A] using htarget)
      (by simpa [A] using htargetPost)
      C0 O (by simpa [← hWeq] using hpartition)
      (by simpa [A, p, W, H] using hbudget)
      (by simpa [A, p, H, ← hWeq] using hcut) hnorm.1 hnorm.2
end OMAH1Research
namespace OMAH1Research
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 10000 in
theorem Q294
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (q K : ℕ) (hq : (2 : ℝ) ≤ c ^ q) :
    K ≤ q * (Nat.clog 2 (n K) + 1) := by
  have hqpos : 0 < q := by
    by_contra hnot
    have hq0 : q = 0 := by omega
    rw [hq0, pow_zero] at hq
    norm_num at hq
  let a := K / q
  have hqa : q * a ≤ K := by
    dsimp [a]
    simpa [mul_comm] using Nat.div_mul_le_self K q
  have hgrowth := Q51
    n c (le_of_lt (lt_trans zero_lt_one hc)) hratio 0 (q * a)
  have hpow : (2 : ℝ) ^ a ≤ (c ^ q) ^ a :=
    pow_le_pow_left₀ (by norm_num) hq a
  have hca : (c ^ q) ^ a = c ^ (q * a) := (pow_mul c q a).symm
  have hn0 : (1 : ℝ) ≤ n 0 := by exact_mod_cast hpos 0
  have htwoReal : (2 : ℝ) ^ a ≤ n K := by
    calc
      (2 : ℝ) ^ a ≤ (c ^ q) ^ a := hpow
      _ = c ^ (q * a) := hca
      _ ≤ c ^ (q * a) * (n 0 : ℝ) := by
        have hcPow : 0 ≤ c ^ (q * a) := by positivity
        nlinarith
      _ ≤ n (q * a) := by simpa using hgrowth
      _ ≤ n K := by exact_mod_cast hmono.monotone hqa
  have htwoNat : 2 ^ a ≤ n K := by exact_mod_cast htwoReal
  have haclog : a ≤ Nat.clog 2 (n K) := by
    rw [← Nat.clog_pow 2 a (by norm_num)]
    exact Nat.clog_mono (by norm_num) (by norm_num) htwoNat
  have hKlt : K < q * (a + 1) := by
    simpa [a] using Nat.lt_mul_div_succ K hqpos
  exact (Nat.le_of_lt hKlt).trans
    (Nat.mul_le_mul_left q (Nat.add_le_add_right haclog 1))
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 10000 in
theorem Q117
    (m W : ℕ) (hm : m ≤ (4 * W) ^ 8) :
    Nat.clog 2 m ≤ 8 * (Nat.clog 2 W + 2) := by
  let l := Nat.clog 2 W
  have hW : W ≤ 2 ^ l := Nat.le_pow_clog (by norm_num) W
  have h4W : 4 * W ≤ 2 ^ (l + 2) := by
    calc
      4 * W ≤ 4 * 2 ^ l := Nat.mul_le_mul_left 4 hW
      _ = 2 ^ (l + 2) := by rw [pow_add]; norm_num; ring
  have hp : (4 * W) ^ 8 ≤ 2 ^ (8 * (l + 2)) := by
    calc
      _ ≤ (2 ^ (l + 2)) ^ 8 := Nat.pow_le_pow_left h4W 8
      _ = 2 ^ (8 * (l + 2)) := by rw [← pow_mul]; congr 1; omega
  apply (Nat.clog_le_iff_le_pow (by norm_num)).mpr
  exact hm.trans hp
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 10000 in
theorem Q293
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (q K W : ℕ) (hq : (2 : ℝ) ≤ c ^ q)
    (hn : n K ≤ (4 * W) ^ 8) :
    K ≤ 17 * q * (Nat.clog 2 W + 1) := by
  have hK := Q294
    n hpos hmono c hc hratio q K hq
  have hclog := Q117 (n K) W hn
  calc
    K ≤ q * (Nat.clog 2 (n K) + 1) := hK
    _ ≤ q * (8 * (Nat.clog 2 W + 2) + 1) := by gcongr
    _ ≤ 17 * q * (Nat.clog 2 W + 1) := by
      nlinarith
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 10000 in
theorem Q174
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (q K G w Dtarget X V : ℕ) (hq : (2 : ℝ) ≤ c ^ q)
    (hDlt : Dtarget < n K)
    (hn : n K ≤ (4 * (2 * w + 1)) ^ 8)
    (hG : G ≤ K + q * (8 * Nat.clog 2 (2 * w + 1) + 1))
    (hd : (Q0 K G).card ≤
      q * (8 * Nat.clog 2 (2 * w + 1) + 1))
    (hX : X < (2 * n K) * Q12 n K) :
    Q31
      n K G (n K * (2 * w + 1) ^ 8) w Dtarget X V q ≤
      50000 * (q + V + 2) ^ 3 *
        (Nat.clog 2 (2 * w + 1) + 1) ^ 2 := by
  let W := 2 * w + 1
  let l := Nat.clog 2 W
  let L := l + 1
  let C := q + V + 2
  let d := (Q0 K G).card
  let Bval := n K * W ^ 8
  let A := Dtarget - w
  let p := (4 * n K) * 2 ^ V
  let Dmax := (2 * d + 1) * (2 * d + 2)
  let Mmax := Bval ^ (2 * d)
  let U := A + p * Mmax + X + W
  let Vaff := 12 * p * Dmax * W
  let A₀ := U + Vaff * G
  let B₀ := Vaff * q
  let N := A₀ + B₀ + 1
  let E := 10000 * C ^ 2 * L ^ 2
  have hLpos : 0 < L := by dsimp [L]; omega
  have hCpos : 0 < C := by dsimp [C]; omega
  have hWpow : W ≤ 2 ^ l := by
    dsimp [l]
    exact Nat.le_pow_clog (by norm_num) W
  have hnPow : n K ≤ 2 ^ (24 * L) := by
    have hclog := Q117
      (n K) W (by simpa [W] using hn)
    apply (Nat.clog_le_iff_le_pow (by norm_num)).mp
    calc
      Nat.clog 2 (n K) ≤ 8 * (l + 2) := by simpa [l] using hclog
      _ ≤ 24 * L := by dsimp [L]; nlinarith
  have hK : K ≤ 17 * q * L := by
    simpa [W, l, L] using Q293
      n hpos hmono c hc hratio q K W hq (by simpa [W] using hn)
  have hQpos : q * (8 * l + 1) ≤ 9 * q * L := by
    calc
      q * (8 * l + 1) ≤ q * (9 * L) := by
        apply Nat.mul_le_mul_left
        dsimp [L]
        omega
      _ = 9 * q * L := by ring
  have hG' : G ≤ 26 * q * L := by
    calc
      G ≤ K + q * (8 * l + 1) := by simpa [W, l] using hG
      _ ≤ 17 * q * L + 9 * q * L := Nat.add_le_add hK hQpos
      _ = 26 * q * L := by ring
  have hd' : d ≤ 9 * q * L := by
    have hd0 : d ≤ q * (8 * l + 1) := by
      simpa [d, W, l] using hd
    exact hd0.trans hQpos
  have hFourN : 4 * n K ≤ 2 ^ (26 * L) := by
    have h4 : 4 ≤ 2 ^ 2 := by norm_num
    have hm := Q37 h4 hnPow
    exact hm.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have hP : Q12 n K ≤ 2 ^ (442 * q * L ^ 2) := by
    have hp0 := Q233 n hpos hmono K
    have hp1 := Q164 hFourN K
    calc
      Q12 n K ≤ (4 * n K) ^ K := hp0
      _ ≤ 2 ^ ((26 * L) * K) := hp1
      _ ≤ 2 ^ (442 * q * L ^ 2) :=
        pow_le_pow_right₀ (by norm_num) (by
          calc
            (26 * L) * K ≤ (26 * L) * (17 * q * L) :=
              Nat.mul_le_mul_left (26 * L) hK
            _ = 442 * q * L ^ 2 := by ring)
  have hTwoN : 2 * n K ≤ 2 ^ (25 * L) := by
    have h2 : 2 ≤ 2 ^ 1 := by norm_num
    have hm := Q37 h2 hnPow
    exact hm.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have hXpow : X ≤ 2 ^ (467 * (q + 1) * L ^ 2) := by
    have hxle : X ≤ (2 * n K) * Q12 n K := hX.le
    have hm := Q37 hTwoN hP
    exact hxle.trans (hm.trans
      (pow_le_pow_right₀ (by norm_num) (by
        have hLL : L ≤ (q + 1) * L ^ 2 := by
          calc
            L ≤ L ^ 2 := by simpa [pow_two] using Nat.le_mul_self L
            _ ≤ (q + 1) * L ^ 2 := by
              have hq1 : 1 ≤ q + 1 := by omega
              simpa using Nat.mul_le_mul_right (L ^ 2) hq1
        have hfirst : 25 * L ≤ 25 * ((q + 1) * L ^ 2) :=
          Nat.mul_le_mul_left 25 hLL
        have hsecond : 442 * q * L ^ 2 ≤
            442 * ((q + 1) * L ^ 2) := by
          have hq1 : q ≤ q + 1 := by omega
          have hm2 := Nat.mul_le_mul_right (442 * L ^ 2) hq1
          simpa [mul_assoc, mul_comm, mul_left_comm] using hm2
        calc
          25 * L + 442 * q * L ^ 2 ≤
              25 * ((q + 1) * L ^ 2) +
                442 * ((q + 1) * L ^ 2) := Nat.add_le_add hfirst hsecond
          _ = 467 * (q + 1) * L ^ 2 := by ring)))
  have hpPow : p ≤ 2 ^ ((V + 26) * L ^ 2) := by
    have htwoV : 2 ^ V ≤ 2 ^ V := le_rfl
    have hm := Q37 hFourN htwoV
    dsimp [p]
    exact hm.trans (pow_le_pow_right₀ (by norm_num) (by
      have hLsq : 1 ≤ L ^ 2 := one_le_pow₀ (by omega)
      have hLLsq : L ≤ L ^ 2 := by
        simpa [pow_two] using Nat.le_mul_self L
      have hVmul : V ≤ V * L ^ 2 := by
        have hmV := Nat.mul_le_mul_left V hLsq
        simpa using hmV
      calc
        26 * L + V ≤ 26 * L ^ 2 + V * L ^ 2 :=
          Nat.add_le_add (Nat.mul_le_mul_left 26 hLLsq) hVmul
        _ = (V + 26) * L ^ 2 := by ring))
  have hBvalPow : Bval ≤ 2 ^ (32 * L) := by
    have hW8 := Q164 hWpow 8
    dsimp [Bval]
    exact (Q37 hnPow hW8).trans
      (pow_le_pow_right₀ (by norm_num) (by dsimp [L]; omega))
  have hMpow : Mmax ≤ 2 ^ (576 * q * L ^ 2) := by
    have hm := Q164 hBvalPow (2 * d)
    dsimp [Mmax]
    exact hm.trans (pow_le_pow_right₀ (by norm_num) (by
      calc
        32 * L * (2 * d) = 64 * L * d := by ring
        _ ≤ 64 * L * (9 * q * L) :=
          Nat.mul_le_mul_left (64 * L) hd'
        _ = 576 * q * L ^ 2 := by ring))
  have hA : A ≤ 2 ^ (24 * L) := by
    exact (Nat.sub_le _ _).trans (Nat.le_of_lt hDlt) |>.trans hnPow
  have hpM : p * Mmax ≤
      2 ^ (((V + 26) * L ^ 2) + 576 * q * L ^ 2) :=
    Q37 hpPow hMpow
  have hU1 : A + p * Mmax ≤
      2 ^ (24 * L +
        (((V + 26) * L ^ 2) + 576 * q * L ^ 2) + 1) :=
    Q40 hA hpM
  have hU2 : A + p * Mmax + X ≤
      2 ^ ((24 * L +
        (((V + 26) * L ^ 2) + 576 * q * L ^ 2) + 1) +
        (467 * (q + 1) * L ^ 2) + 1) :=
    Q40 hU1 hXpow
  have hUpow : U ≤ 2 ^ (1200 * C ^ 2 * L ^ 2) := by
    have hU3 := Q40 hU2 hWpow
    let Z0 := C ^ 2 * L ^ 2
    have hCself : C ≤ C ^ 2 := by
      simpa [pow_two] using Nat.le_mul_self C
    have hLL : L ≤ L ^ 2 := by
      simpa [pow_two] using Nat.le_mul_self L
    have hLZ : L ≤ Z0 := by
      dsimp [Z0]
      have hC2 : 1 ≤ C ^ 2 := by exact pow_pos hCpos 2
      exact hLL.trans (by simpa using Nat.mul_le_mul_right (L ^ 2) hC2)
    have hlZ : l ≤ Z0 := (by dsimp [L]; omega : l ≤ L).trans hLZ
    have hqZ : q * L ^ 2 ≤ Z0 := by
      dsimp [Z0]
      apply Nat.mul_le_mul_right
      exact (show q ≤ C by dsimp [C]; omega).trans hCself
    have hq1Z : (q + 1) * L ^ 2 ≤ Z0 := by
      dsimp [Z0]
      apply Nat.mul_le_mul_right
      exact (show q + 1 ≤ C by dsimp [C]; omega).trans hCself
    have hVZ : (V + 26) * L ^ 2 ≤ 13 * Z0 := by
      have hVC : V + 26 ≤ 13 * C := by dsimp [C]; omega
      calc
        (V + 26) * L ^ 2 ≤ (13 * C) * L ^ 2 :=
          Nat.mul_le_mul_right _ hVC
        _ ≤ 13 * (C ^ 2 * L ^ 2) := by
          have := Nat.mul_le_mul_right (13 * L ^ 2) hCself
          simpa [mul_assoc, mul_comm, mul_left_comm] using this
        _ = 13 * Z0 := rfl
    have hExp :
        ((24 * L + (((V + 26) * L ^ 2) + 576 * q * L ^ 2) + 1) +
          (467 * (q + 1) * L ^ 2) + 1) + l + 1 ≤ 1200 * Z0 := by
      have hZpos : 1 ≤ Z0 := by
        dsimp [Z0]
        exact mul_pos (pow_pos hCpos 2) (pow_pos hLpos 2)
      have h24 : 24 * L ≤ 24 * Z0 := Nat.mul_le_mul_left 24 hLZ
      have h576 : 576 * q * L ^ 2 ≤ 576 * Z0 := by
        simpa [mul_assoc] using Nat.mul_le_mul_left 576 hqZ
      have h467 : 467 * (q + 1) * L ^ 2 ≤ 467 * Z0 := by
        simpa [mul_assoc] using Nat.mul_le_mul_left 467 hq1Z
      omega
    dsimp [U]
    have hExp' :
        ((24 * L + (((V + 26) * L ^ 2) + 576 * q * L ^ 2) + 1) +
          (467 * (q + 1) * L ^ 2) + 1) + l + 1 ≤
            1200 * C ^ 2 * L ^ 2 := by
      calc
        _ ≤ 1200 * Z0 := hExp
        _ = 1200 * C ^ 2 * L ^ 2 := by dsimp [Z0]; ring
    exact hU3.trans (pow_le_pow_right₀ (by norm_num) hExp')
  have hDmax : Dmax ≤ 400 * (q + 1) ^ 2 * L ^ 2 := by
    have hab : q * L ≤ (q + 1) * L :=
      Nat.mul_le_mul_right L (by omega)
    have hbase : 2 ≤ 2 * ((q + 1) * L) := by
      have : 1 ≤ (q + 1) * L := mul_pos (by omega) hLpos
      omega
    have h18 : 18 * q * L ≤ 18 * (q + 1) * L := by
      have hh := Nat.mul_le_mul_left 18 hab
      simpa [mul_assoc] using hh
    have h2 : 2 ≤ 2 * (q + 1) * L := by
      simpa [mul_assoc] using hbase
    have h2d2 : 2 * d + 2 ≤ 20 * (q + 1) * L := by
      calc
        2 * d + 2 ≤ 18 * q * L + 2 := by
          have hh := Nat.add_le_add_right (Nat.mul_le_mul_left 2 hd') 2
          calc
            2 * d + 2 ≤ 2 * (9 * q * L) + 2 := hh
            _ = 18 * q * L + 2 := by ring
        _ ≤ 18 * (q + 1) * L + 2 * (q + 1) * L :=
          Nat.add_le_add h18 h2
        _ = 20 * (q + 1) * L := by ring
    have h2d1 : 2 * d + 1 ≤ 20 * (q + 1) * L := by omega
    dsimp [Dmax]
    calc
      (2 * d + 1) * (2 * d + 2) ≤
          (20 * (q + 1) * L) * (20 * (q + 1) * L) :=
        Nat.mul_le_mul h2d1 h2d2
      _ = 400 * (q + 1) ^ 2 * L ^ 2 := by ring
  have hDpow : Dmax ≤ 2 ^ (800 * C ^ 2 * L ^ 2) := by
    have hraw := Q74 Dmax
    have hqC : q + 1 ≤ C := by dsimp [C]; omega
    have hsq : (q + 1) ^ 2 ≤ C ^ 2 := Nat.pow_le_pow_left hqC 2
    have hbound : 2 * Dmax ≤ 800 * C ^ 2 * L ^ 2 := calc
      2 * Dmax ≤ 2 * (400 * (q + 1) ^ 2 * L ^ 2) :=
        Nat.mul_le_mul_left 2 hDmax
      _ ≤ 2 * (400 * C ^ 2 * L ^ 2) := by gcongr
      _ = 800 * C ^ 2 * L ^ 2 := by ring
    exact hraw.trans (pow_le_pow_right₀ (by norm_num) hbound)
  have h12 : 12 ≤ 2 ^ 4 := by norm_num
  have hVaffPow : Vaff ≤ 2 ^ (850 * C ^ 2 * L ^ 2) := by
    have h1 := Q37 h12 hpPow
    have h2 := Q37 h1 hDpow
    have h3 := Q37 h2 hWpow
    have hCL : C * L ^ 2 ≤ C ^ 2 * L ^ 2 := by
      have hc2 : C ≤ C ^ 2 := by simpa [pow_two] using Nat.le_mul_self C
      exact Nat.mul_le_mul_right (L ^ 2) hc2
    have hLCL : L ≤ C ^ 2 * L ^ 2 := by
      have hLL : L ≤ L ^ 2 := by simpa [pow_two] using Nat.le_mul_self L
      have hC2 : 1 ≤ C ^ 2 := by exact pow_pos hCpos 2
      exact hLL.trans (by simpa using Nat.mul_le_mul_right (L ^ 2) hC2)
    have hVC : V + 26 ≤ 13 * C := by dsimp [C]; omega
    have hvterm : (V + 26) * L ^ 2 ≤ 13 * (C ^ 2 * L ^ 2) := by
      calc
        _ ≤ (13 * C) * L ^ 2 := Nat.mul_le_mul_right _ hVC
        _ ≤ 13 * (C ^ 2 * L ^ 2) := by
          simpa [mul_assoc] using Nat.mul_le_mul_left 13 hCL
    have hexp : 4 + (V + 26) * L ^ 2 +
        800 * C ^ 2 * L ^ 2 + l ≤ 850 * C ^ 2 * L ^ 2 := by
      let Z0 := C ^ 2 * L ^ 2
      have hZpos : 1 ≤ Z0 := by
        dsimp [Z0]
        exact mul_pos (pow_pos hCpos 2) (pow_pos hLpos 2)
      have hl : l ≤ Z0 := by
        dsimp [Z0]
        exact (by dsimp [L]; omega : l ≤ L).trans hLCL
      have h4 : 4 ≤ 4 * Z0 := Nat.mul_le_mul_left 4 hZpos
      have hv : (V + 26) * L ^ 2 ≤ 13 * Z0 := by
        simpa [Z0] using hvterm
      calc
        4 + (V + 26) * L ^ 2 + 800 * C ^ 2 * L ^ 2 + l ≤
            4 * Z0 + 13 * Z0 + 800 * Z0 + Z0 := by
          dsimp [Z0] at *
          have h800 : 800 * C ^ 2 * L ^ 2 ≤ 800 * Z0 := by
            dsimp [Z0]
            simp [mul_assoc]
          exact Nat.add_le_add
            (Nat.add_le_add (Nat.add_le_add h4 hv) h800) hl
        _ = 818 * Z0 := by ring
        _ ≤ 850 * Z0 := Nat.mul_le_mul_right Z0 (by norm_num)
        _ = 850 * C ^ 2 * L ^ 2 := by dsimp [Z0]; ring
    dsimp [Vaff]
    exact h3.trans (pow_le_pow_right₀ (by norm_num) hexp)
  have hGpow : G ≤ 2 ^ (52 * q * L) := by
    have hh := hG'.trans (Q74 (26 * q * L))
    have heq : 2 * (26 * q * L) = 52 * q * L := by ring
    rw [heq] at hh
    exact hh
  have hqLZ : q * L ≤ C ^ 2 * L ^ 2 := by
    have hqC2 : q ≤ C ^ 2 := by
      exact (show q ≤ C by dsimp [C]; omega).trans
        (by simpa [pow_two] using Nat.le_mul_self C)
    have hLL : L ≤ L ^ 2 := by simpa [pow_two] using Nat.le_mul_self L
    exact Nat.mul_le_mul hqC2 hLL
  have hVG : Vaff * G ≤
      2 ^ (902 * C ^ 2 * L ^ 2) := by
    have hm := Q37 hVaffPow hGpow
    have hexp : 850 * C ^ 2 * L ^ 2 + 52 * q * L ≤
        902 * C ^ 2 * L ^ 2 := by
      calc
        _ ≤ 850 * C ^ 2 * L ^ 2 +
            52 * (C ^ 2 * L ^ 2) := by
          simpa [mul_assoc] using
            Nat.add_le_add_left (Nat.mul_le_mul_left 52 hqLZ)
              (850 * C ^ 2 * L ^ 2)
        _ = 902 * C ^ 2 * L ^ 2 := by ring
    exact hm.trans (pow_le_pow_right₀ (by norm_num) hexp)
  have hqPow : q ≤ 2 ^ (2 * q) := Q74 q
  have hVq : Vaff * q ≤ 2 ^ (852 * C ^ 2 * L ^ 2) := by
    have hm := Q37 hVaffPow hqPow
    have hqZ : q ≤ C ^ 2 * L ^ 2 := by
      calc
        q ≤ q * L := Nat.le_mul_of_pos_right q hLpos
        _ ≤ C ^ 2 * L ^ 2 := hqLZ
    have hexp : 850 * C ^ 2 * L ^ 2 + 2 * q ≤
        852 * C ^ 2 * L ^ 2 := by
      calc
        _ ≤ 850 * C ^ 2 * L ^ 2 +
            2 * (C ^ 2 * L ^ 2) := by
          exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 hqZ) _
        _ = 852 * C ^ 2 * L ^ 2 := by ring
    exact hm.trans (pow_le_pow_right₀ (by norm_num) hexp)
  have hZpos : 1 ≤ C ^ 2 * L ^ 2 :=
    mul_pos (pow_pos hCpos 2) (pow_pos hLpos 2)
  have hA0 : A₀ ≤ 2 ^ (2103 * C ^ 2 * L ^ 2) := by
    dsimp [A₀]
    have hexp : 1200 * C ^ 2 * L ^ 2 +
        902 * C ^ 2 * L ^ 2 + 1 ≤ 2103 * C ^ 2 * L ^ 2 := by
      calc
        _ ≤ 1200 * C ^ 2 * L ^ 2 +
            902 * C ^ 2 * L ^ 2 + C ^ 2 * L ^ 2 := by gcongr
        _ = _ := by ring
    exact (Q40 hUpow hVG).trans
      (pow_le_pow_right₀ (by norm_num) hexp)
  have hA0B0 : A₀ + B₀ ≤
      2 ^ (2956 * C ^ 2 * L ^ 2) := by
    dsimp [B₀]
    have hexp : 2103 * C ^ 2 * L ^ 2 +
        852 * C ^ 2 * L ^ 2 + 1 ≤ 2956 * C ^ 2 * L ^ 2 := by
      calc
        _ ≤ 2103 * C ^ 2 * L ^ 2 +
            852 * C ^ 2 * L ^ 2 + C ^ 2 * L ^ 2 := by gcongr
        _ = _ := by ring
    exact (Q40 hA0 hVq).trans
      (pow_le_pow_right₀ (by norm_num) hexp)
  have hNpow : N ≤ 2 ^ E := by
    have h1 : (1 : ℕ) ≤ 2 ^ 0 := by norm_num
    have hs := Q40 hA0B0 h1
    have hexp : 2956 * C ^ 2 * L ^ 2 + 0 + 1 ≤
        10000 * C ^ 2 * L ^ 2 := by
      calc
        2956 * C ^ 2 * L ^ 2 + 0 + 1 =
            2956 * (C ^ 2 * L ^ 2) + 1 := by ring
        _ ≤ 2956 * (C ^ 2 * L ^ 2) + (C ^ 2 * L ^ 2) :=
          Nat.add_le_add_left hZpos _
        _ = 2957 * (C ^ 2 * L ^ 2) := by ring
        _ ≤ 10000 * (C ^ 2 * L ^ 2) :=
          Nat.mul_le_mul_right _ (by norm_num)
        _ = 10000 * C ^ 2 * L ^ 2 := by ring
    dsimp [N, E]
    exact hs.trans (pow_le_pow_right₀ (by norm_num) hexp)
  have hclogN : Nat.clog 2 N ≤ E :=
    (Nat.clog_le_iff_le_pow (by norm_num)).mpr hNpow
  have hH : G + q * (4 * Nat.clog 2 N + 4) ≤
      50000 * C ^ 3 * L ^ 2 := by
    let Z3 := C ^ 3 * L ^ 2
    have hqC : q ≤ C := by dsimp [C]; omega
    have hC3 : C ^ 2 ≤ C ^ 3 := by
      rw [pow_succ]
      exact Nat.le_mul_of_pos_right (C ^ 2) hCpos
    have hqLZ3 : q * L ≤ Z3 := by
      calc
        q * L ≤ C * L := Nat.mul_le_mul_right L hqC
        _ ≤ C ^ 3 * L ^ 2 := Nat.mul_le_mul
          (by
            calc
              C ≤ C ^ 2 := by simpa [pow_two] using Nat.le_mul_self C
              _ ≤ C ^ 3 := hC3)
          (by simpa [pow_two] using Nat.le_mul_self L)
        _ = Z3 := rfl
    have hqE : q * E ≤ 10000 * Z3 := by
      have hh := Nat.mul_le_mul_right (C ^ 2 * L ^ 2) hqC
      dsimp [E, Z3]
      calc
        q * (10000 * C ^ 2 * L ^ 2) =
            10000 * (q * (C ^ 2 * L ^ 2)) := by ring
        _ ≤ 10000 * (C * (C ^ 2 * L ^ 2)) :=
          Nat.mul_le_mul_left 10000 (by
            simpa [mul_assoc] using hh)
        _ = 10000 * (C ^ 3 * L ^ 2) := by ring
    have hqZ3 : q ≤ Z3 := by
      calc
        q ≤ q * L := Nat.le_mul_of_pos_right q hLpos
        _ ≤ Z3 := hqLZ3
    have hGZ : G ≤ 26 * Z3 := by
      have hh := Nat.mul_le_mul_left 26 hqLZ3
      exact hG'.trans (by simpa [mul_assoc] using hh)
    have hsecond : q * (4 * Nat.clog 2 N + 4) ≤
        4 * (q * E) + 4 * q := by
      have hh := Nat.mul_le_mul_left 4 hclogN
      calc
        q * (4 * Nat.clog 2 N + 4) ≤ q * (4 * E + 4) := by gcongr
        _ = 4 * (q * E) + 4 * q := by ring
    calc
      _ ≤ 26 * Z3 + (4 * (q * E) + 4 * q) :=
        Nat.add_le_add hGZ hsecond
      _ ≤ 26 * Z3 + 4 * (10000 * Z3) + 4 * Z3 := by
        have he : 4 * (q * E) ≤ 4 * (10000 * Z3) :=
          Nat.mul_le_mul_left 4 hqE
        have hq' : 4 * q ≤ 4 * Z3 := Nat.mul_le_mul_left 4 hqZ3
        omega
      _ = 40030 * Z3 := by ring
      _ ≤ 50000 * Z3 := Nat.mul_le_mul_right Z3 (by norm_num)
      _ = 50000 * C ^ 3 * L ^ 2 := by dsimp [Z3]; ring
  simpa [Q31, W, l, L, C, d, Bval,
    A, p, Dmax, Mmax, U, Vaff, A₀, B₀, N] using hH
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 10000 in
theorem Q282 (w : ℕ) :
    (Nat.clog 2 (2 * w + 1) + 1) ^ 2 ≤ 25 * (w + 1) := by
  let s := Nat.sqrt w
  let x := s + 1
  have hwlt : w < x ^ 2 := by
    simpa [x, pow_two] using Nat.lt_succ_sqrt w
  have hW : 2 * w + 1 ≤ 2 * x ^ 2 + 1 := by omega
  have hpow : 2 * x ^ 2 + 1 ≤ 2 ^ (2 * x) := by
    simpa using Nat.two_mul_sq_add_one_le_two_pow_two_mul x
  have hclog : Nat.clog 2 (2 * w + 1) ≤ 2 * x :=
    (Nat.clog_le_iff_le_pow (by norm_num)).mpr (hW.trans hpow)
  have hsSq : s ^ 2 ≤ w := by
    simpa [pow_two] using Nat.sqrt_le w
  have hs : s ≤ w := Nat.sqrt_le_self w
  calc
    (Nat.clog 2 (2 * w + 1) + 1) ^ 2 ≤ (2 * x + 1) ^ 2 :=
      Nat.pow_le_pow_left (Nat.add_le_add_right hclog 1) 2
    _ ≤ 25 * (w + 1) := by
      dsimp [x]
      nlinarith
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 10000 in
theorem Q173
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (q K G w Dtarget X V : ℕ) (hq : (2 : ℝ) ≤ c ^ q)
    (hDlt : Dtarget < n K)
    (hn : n K ≤ (4 * (2 * w + 1)) ^ 8)
    (hG : G ≤ K + q * (8 * Nat.clog 2 (2 * w + 1) + 1))
    (hd : (Q0 K G).card ≤
      q * (8 * Nat.clog 2 (2 * w + 1) + 1))
    (hX : X < (2 * n K) * Q12 n K) :
    Q31
      n K G (n K * (2 * w + 1) ^ 8) w Dtarget X V q ≤
      1250000 * (q + V + 2) ^ 3 * (w + 1) := by
  have hbin := Q174
    n hpos hmono c hc hratio q K G w Dtarget X V hq hDlt hn hG hd hX
  calc
    _ ≤ 50000 * (q + V + 2) ^ 3 *
        (Nat.clog 2 (2 * w + 1) + 1) ^ 2 := hbin
    _ ≤ 50000 * (q + V + 2) ^ 3 * (25 * (w + 1)) := by
      gcongr
      exact Q282 w
    _ = 1250000 * (q + V + 2) ^ 3 * (w + 1) := by ring
end OMAH1Research
namespace OMAH1Research
open Filter Topology Real goldenRatio
set_option maxRecDepth 10000 in
def Q9 (q V w : ℕ) : ℕ :=
  1250000 * (q + V + 2) ^ 3 * (w + 1)
set_option maxRecDepth 10000 in
theorem Q269 (q V : ℕ) :
    Tendsto (fun w : ℕ =>
      (φ⁻¹) ^ w *
        (2 * Q8 (Q9 q V w)))
      atTop (𝓝 0) := by
  let r : ℝ := φ⁻¹
  let A : ℝ := (1250000 * (q + V + 2) ^ 3 : ℕ)
  let C : ℝ := 4 * Q13 * A * r⁻¹
  let g : ℕ → ℝ := fun w => C * ((w + 1 : ℕ) : ℝ) * r ^ (w + 1)
  have hrpos : 0 < r := by dsimp [r]; exact inv_pos.mpr Real.goldenRatio_pos
  have hr0 : 0 ≤ r := hrpos.le
  have hr1 : r < 1 := by
    dsimp [r]
    exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hg : Tendsto g atTop (𝓝 0) := by
    have hbase := tendsto_pow_const_mul_const_pow_of_lt_one 1 hr0 hr1
    have hshift := hbase.comp (Filter.tendsto_add_atTop_nat 1)
    have hconst := hshift.const_mul C
    simpa [g, mul_assoc] using hconst
  apply squeeze_zero
  · intro w
    have ht := Q34 (Q9 q V w)
    positivity
  · intro w
    have hcap := Q93 (Q9 q V w)
    have hbound : ((Q9 q V w : ℕ) : ℝ) + 1 ≤
        2 * A * ((w + 1 : ℕ) : ℝ) := by
      have hAnat : 1 ≤ 1250000 * (q + V + 2) ^ 3 := by
        have hp : 1 ≤ (q + V + 2) ^ 3 := one_le_pow₀ (by omega)
        exact hp.trans (Nat.le_mul_of_pos_left _ (by norm_num))
      have hA : (1 : ℝ) ≤ A := by
        dsimp [A]
        exact_mod_cast hAnat
      have hw : (1 : ℝ) ≤ ((w + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le w)
      have hAw : (1 : ℝ) ≤ A * ((w + 1 : ℕ) : ℝ) := by
        calc
          (1 : ℝ) = 1 * 1 := by ring
          _ ≤ A * ((w + 1 : ℕ) : ℝ) :=
            mul_le_mul hA hw (by norm_num) (le_trans (by norm_num) hA)
      have heq : ((Q9 q V w : ℕ) : ℝ) =
          A * ((w + 1 : ℕ) : ℝ) := by
        dsimp [Q9, A]
        push_cast
        ring
      rw [heq]
      linarith
    have hlinear : Q8 (Q9 q V w) ≤
        2 * Q13 * A * ((w + 1 : ℕ) : ℝ) := by
      calc
        _ ≤ Q13 *
            (((Q9 q V w : ℕ) : ℝ) + 1) := hcap
        _ ≤ Q13 *
            (2 * A * ((w + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hbound Q63
        _ = _ := by ring
    calc
      r ^ w * (2 * Q8 (Q9 q V w)) ≤
          r ^ w * (2 * (2 * Q13 * A *
            ((w + 1 : ℕ) : ℝ))) := by gcongr
      _ = g w := by
        dsimp [g, C]
        rw [pow_succ]
        field_simp [hrpos.ne']
        ring
  · exact hg
set_option maxRecDepth 10000 in
theorem Q237
    (q V : ℕ) (T : ℝ) :
    Tendsto (fun w : ℕ =>
      (φ⁻¹) ^ w *
        (2 * Q8 (Q9 q V w)) *
        (2 * Q10 T (Q9 q V w)))
      atTop (𝓝 0) := by
  let r : ℝ := φ⁻¹
  let A : ℝ := (1250000 * (q + V + 2) ^ 3 : ℕ)
  let C : ℝ := 16 * Q13 *
    Q19 T * A ^ 2 * r⁻¹
  let g : ℕ → ℝ := fun w =>
    C * ((w + 1 : ℕ) : ℝ) ^ 2 * r ^ (w + 1)
  have hrpos : 0 < r := by dsimp [r]; exact inv_pos.mpr Real.goldenRatio_pos
  have hr0 : 0 ≤ r := hrpos.le
  have hr1 : r < 1 := by
    dsimp [r]
    exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hg : Tendsto g atTop (𝓝 0) := by
    have hbase := tendsto_pow_const_mul_const_pow_of_lt_one 2 hr0 hr1
    have hshift := hbase.comp (Filter.tendsto_add_atTop_nat 1)
    have hconst := hshift.const_mul C
    simpa [g, mul_assoc] using hconst
  apply squeeze_zero
  · intro w
    have ht := Q34 (Q9 q V w)
    have hc := Q36 T (Q9 q V w)
    positivity
  · intro w
    have ht := Q93 (Q9 q V w)
    have hc := Q170 T
      (Q9 q V w)
    have hbound : ((Q9 q V w : ℕ) : ℝ) + 1 ≤
        2 * A * ((w + 1 : ℕ) : ℝ) := by
      have hAnat : 1 ≤ 1250000 * (q + V + 2) ^ 3 := by
        have hp : 1 ≤ (q + V + 2) ^ 3 := one_le_pow₀ (by omega)
        exact hp.trans (Nat.le_mul_of_pos_left _ (by norm_num))
      have hA : (1 : ℝ) ≤ A := by
        dsimp [A]
        exact_mod_cast hAnat
      have hw : (1 : ℝ) ≤ ((w + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le w)
      have hAw : (1 : ℝ) ≤ A * ((w + 1 : ℕ) : ℝ) := by
        calc
          (1 : ℝ) = 1 * 1 := by ring
          _ ≤ A * ((w + 1 : ℕ) : ℝ) :=
            mul_le_mul hA hw (by norm_num) (le_trans (by norm_num) hA)
      have heq : ((Q9 q V w : ℕ) : ℝ) =
          A * ((w + 1 : ℕ) : ℝ) := by
        dsimp [Q9, A]
        push_cast
        ring
      rw [heq]
      linarith
    have ht' : Q8 (Q9 q V w) ≤
        2 * Q13 * A * ((w + 1 : ℕ) : ℝ) := by
      calc
        _ ≤ Q13 *
            (((Q9 q V w : ℕ) : ℝ) + 1) := ht
        _ ≤ Q13 *
            (2 * A * ((w + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hbound Q63
        _ = _ := by ring
    have hc' : Q10 T (Q9 q V w) ≤
        2 * Q19 T * A *
          ((w + 1 : ℕ) : ℝ) := by
      calc
        _ ≤ Q19 T *
            (((Q9 q V w : ℕ) : ℝ) + 1) := hc
        _ ≤ Q19 T *
            (2 * A * ((w + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hbound
            (Q101 T)
        _ = _ := by ring
    have ht0 := Q34 (Q9 q V w)
    have hc0 := Q36 T (Q9 q V w)
    have htU : 0 ≤ 2 * Q13 * A *
        ((w + 1 : ℕ) : ℝ) := ht0.trans ht'
    have hcU : 0 ≤ 2 * Q19 T * A *
        ((w + 1 : ℕ) : ℝ) := hc0.trans hc'
    calc
      r ^ w * (2 * Q8 (Q9 q V w)) *
          (2 * Q10 T (Q9 q V w)) ≤
        r ^ w * (2 * (2 * Q13 * A *
          ((w + 1 : ℕ) : ℝ))) *
          (2 * (2 * Q19 T * A *
            ((w + 1 : ℕ) : ℝ))) := by gcongr
      _ = g w := by
        dsimp [g, C]
        rw [pow_succ]
        field_simp [hrpos.ne']
        ring
  · exact hg
set_option maxRecDepth 10000 in
theorem Q356
    (q w d : ℕ)
    (hd : d ≤ q * (8 * Nat.clog 2 (2 * w + 1) + 1)) :
    (2 * d + 1) * (2 * d + 2) ≤
      10000 * (q + 1) ^ 2 * (w + 1) := by
  let l := Nat.clog 2 (2 * w + 1)
  let L := l + 1
  have hqpos : q * (8 * l + 1) ≤ 9 * q * L := by
    calc
      _ ≤ q * (9 * L) := by
        apply Nat.mul_le_mul_left
        dsimp [L]
        omega
      _ = _ := by ring
  have hd0 : d ≤ q * (8 * l + 1) := by simpa [l] using hd
  have hd' : d ≤ 9 * q * L := hd0.trans hqpos
  have hab : q * L ≤ (q + 1) * L := Nat.mul_le_mul_right L (by omega)
  have hbase : 2 ≤ 2 * ((q + 1) * L) := by
    have : 0 < (q + 1) * L := mul_pos (by omega) (by dsimp [L]; omega)
    omega
  have h18 : 18 * q * L ≤ 18 * (q + 1) * L := by
    simpa [mul_assoc] using Nat.mul_le_mul_left 18 hab
  have h2 : 2 ≤ 2 * (q + 1) * L := by simpa [mul_assoc] using hbase
  have h2d2 : 2 * d + 2 ≤ 20 * (q + 1) * L := by
    calc
      2 * d + 2 ≤ 18 * q * L + 2 := by
        have hh := Nat.add_le_add_right (Nat.mul_le_mul_left 2 hd') 2
        calc
          _ ≤ 2 * (9 * q * L) + 2 := hh
          _ = 18 * q * L + 2 := by ring
      _ ≤ 18 * (q + 1) * L + 2 * (q + 1) * L :=
        Nat.add_le_add h18 h2
      _ = _ := by ring
  have h2d1 : 2 * d + 1 ≤ 20 * (q + 1) * L := by omega
  have hprod : (2 * d + 1) * (2 * d + 2) ≤
      400 * (q + 1) ^ 2 * L ^ 2 := by
    calc
      _ ≤ (20 * (q + 1) * L) * (20 * (q + 1) * L) :=
        Nat.mul_le_mul h2d1 h2d2
      _ = _ := by ring
  calc
    _ ≤ 400 * (q + 1) ^ 2 * L ^ 2 := hprod
    _ ≤ 400 * (q + 1) ^ 2 * (25 * (w + 1)) := by
      gcongr
      simpa [l, L] using Q282 w
    _ = 10000 * (q + 1) ^ 2 * (w + 1) := by ring
set_option maxRecDepth 10000 in
noncomputable def Q77
    (c : ℝ) (q V : ℕ) : ℝ :=
  let CD : ℝ := 10000 * (q + 1) ^ 2
  let AH : ℝ := 1250000 * (q + V + 2) ^ 3
  let scale : ℝ := 4 * 2 ^ V
  2 * CD * (12 + 2 * scale) * (c⁻¹ * (1 - c⁻¹)⁻¹) +
    2 * CD * AH +
    8 * CD * scale * (1 - c⁻¹)⁻¹
set_option maxRecDepth 10000 in
theorem Q303 (c : ℝ) (q V : ℕ) :
    Tendsto (fun w : ℕ =>
      Q77 c q V * (w : ℝ)⁻¹)
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun w : ℕ => (w : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa using hinv.const_mul (Q77 c q V)
set_option maxRecDepth 10000 in
theorem Q331
    (c : ℝ) (hc : 1 < c) (q V : ℕ) :
    ∀ᶠ w : ℕ in atTop, 0 < w ∧
      ∀ nval nG d H : ℕ,
        w ^ 8 ≤ nval →
        nval * (2 * w + 1) ^ 8 < nG →
        d ≤ q * (8 * Nat.clog 2 (2 * w + 1) + 1) →
        H ≤ Q9 q V w →
        let W : ℕ := 2 * w + 1
        let p : ℕ := (4 * nval) * 2 ^ V
        let Z : ℕ := (4 * 2 ^ V) * w
        let Dmax : ℕ := (2 * d + 1) * (2 * d + 2)
        let Bexc : ℕ := (w + 1) ^ 3
        (Dmax : ℝ) *
          (((4 * W + 2 * Z : ℕ) : ℝ) *
              (c⁻¹ * (1 - c⁻¹)⁻¹ * (nval : ℝ)⁻¹) +
            2 * (H : ℝ) / (Bexc : ℝ) +
            4 * (p : ℝ) * ((1 - c⁻¹)⁻¹ * (nG : ℝ)⁻¹)) < 1 := by
  have hden : 0 < 1 - c⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hc)
  let Cmaj := Q77 c q V
  have htend := Q303 c q V
  have hevent : ∀ᶠ w : ℕ in atTop, Cmaj * (w : ℝ)⁻¹ < 1 :=
    htend.eventually_lt_const (by norm_num)
  filter_upwards [eventually_ge_atTop 1, hevent] with w hw hmajor
  refine ⟨by omega, ?_⟩
  intro nval nG d H hnval hnG hd hH
  let W : ℕ := 2 * w + 1
  let p : ℕ := (4 * nval) * 2 ^ V
  let scale : ℕ := 4 * 2 ^ V
  let Z : ℕ := scale * w
  let Dmax : ℕ := (2 * d + 1) * (2 * d + 2)
  let Bexc : ℕ := (w + 1) ^ 3
  let CD : ℝ := 10000 * (q + 1) ^ 2
  let AH : ℝ := 1250000 * (q + V + 2) ^ 3
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hwOne : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hW : W ≤ 3 * w := by dsimp [W]; omega
  have hWlower : w ≤ W := by dsimp [W]; omega
  have hDnat : Dmax ≤ 10000 * (q + 1) ^ 2 * (w + 1) := by
    dsimp [Dmax]
    exact Q356 q w d hd
  have hDreal : (Dmax : ℝ) ≤ CD * (((w + 1 : ℕ) : ℝ)) := by
    dsimp [CD]
    exact_mod_cast hDnat
  have hDtwo : (Dmax : ℝ) ≤ 2 * CD * (w : ℝ) := by
    have hwadd : ((w + 1 : ℕ) : ℝ) ≤ 2 * (w : ℝ) := by
      exact_mod_cast (by omega : w + 1 ≤ 2 * w)
    calc
      (Dmax : ℝ) ≤ CD * ((w + 1 : ℕ) : ℝ) := hDreal
      _ ≤ CD * (2 * (w : ℝ)) :=
        mul_le_mul_of_nonneg_left hwadd (by dsimp [CD]; positivity)
      _ = 2 * CD * (w : ℝ) := by ring
  have hHreal : (H : ℝ) ≤ AH * (((w + 1 : ℕ) : ℝ)) := by
    dsimp [AH, Q9] at *
    exact_mod_cast hH
  have hnvalR : (w : ℝ) ^ 8 ≤ (nval : ℝ) := by exact_mod_cast hnval
  have hnvalPos : (0 : ℝ) < nval :=
    lt_of_lt_of_le (pow_pos hwR 8) hnvalR
  have hnGR : (nval : ℝ) * (W : ℝ) ^ 8 < (nG : ℝ) := by
    exact_mod_cast (by simpa [W] using hnG)
  have hscaleR : (scale : ℝ) = 4 * (2 : ℝ) ^ V := by
    dsimp [scale]
    push_cast
    ring
  have hpR : (p : ℝ) = (scale : ℝ) * (nval : ℝ) := by
    dsimp [p, scale]
    push_cast
    ring
  have hZr : (Z : ℝ) = (scale : ℝ) * (w : ℝ) := by
    dsimp [Z]
    push_cast
    ring
  have hcoeff : ((4 * W + 2 * Z : ℕ) : ℝ) ≤
      (12 + 2 * (scale : ℝ)) * (w : ℝ) := by
    push_cast
    rw [hZr]
    have hWR : (W : ℝ) ≤ 3 * (w : ℝ) := by exact_mod_cast hW
    nlinarith
  have hnvalInv : (nval : ℝ)⁻¹ ≤ ((w : ℝ) ^ 8)⁻¹ :=
    inv_anti₀ (pow_pos hwR 8) hnvalR
  have hterm1 : (Dmax : ℝ) *
      (((4 * W + 2 * Z : ℕ) : ℝ) *
        (c⁻¹ * (1 - c⁻¹)⁻¹ * (nval : ℝ)⁻¹)) ≤
      (2 * CD * (12 + 2 * (scale : ℝ)) *
        (c⁻¹ * (1 - c⁻¹)⁻¹)) * (w : ℝ)⁻¹ := by
    let tail : ℝ := c⁻¹ * (1 - c⁻¹)⁻¹
    have htail : 0 ≤ tail := by dsimp [tail]; positivity
    have hpair : (Dmax : ℝ) * ((4 * W + 2 * Z : ℕ) : ℝ) ≤
        (2 * CD * (w : ℝ)) *
          ((12 + 2 * (scale : ℝ)) * (w : ℝ)) :=
      mul_le_mul hDtwo hcoeff (by positivity) (by positivity)
    have hpairTail := mul_le_mul_of_nonneg_right hpair htail
    have hprod :
        ((Dmax : ℝ) * ((4 * W + 2 * Z : ℕ) : ℝ) * tail) *
            (nval : ℝ)⁻¹ ≤
          (((2 * CD * (w : ℝ)) *
              ((12 + 2 * (scale : ℝ)) * (w : ℝ))) * tail) *
            ((w : ℝ) ^ 8)⁻¹ :=
      mul_le_mul hpairTail hnvalInv (by positivity) (by positivity)
    have hi : (w : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hwR).mpr hwOne
    have hp : ((w : ℝ)⁻¹) ^ 5 ≤ 1 := pow_le_one₀ (by positivity) hi
    have hfac : 0 ≤
        (2 * CD * (12 + 2 * (scale : ℝ)) * tail) * (w : ℝ)⁻¹ := by
      positivity
    calc
      _ = ((Dmax : ℝ) * ((4 * W + 2 * Z : ℕ) : ℝ) * tail) *
          (nval : ℝ)⁻¹ := by dsimp [tail]; ring
      _ ≤ (((2 * CD * (w : ℝ)) *
              ((12 + 2 * (scale : ℝ)) * (w : ℝ))) * tail) *
            ((w : ℝ) ^ 8)⁻¹ := hprod
      _ = (2 * CD * (12 + 2 * (scale : ℝ)) * tail) *
          (w : ℝ)⁻¹ * ((w : ℝ)⁻¹) ^ 5 := by
        field_simp [hwR.ne']
      _ ≤ (2 * CD * (12 + 2 * (scale : ℝ)) * tail) *
          (w : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left hp hfac
      _ = _ := by dsimp [tail]; ring
  have hBexcR : (Bexc : ℝ) = (((w + 1 : ℕ) : ℝ)) ^ 3 := by
    dsimp [Bexc]
    push_cast
    rfl
  have hterm2 : (Dmax : ℝ) *
      (2 * (H : ℝ) / (Bexc : ℝ)) ≤
      (2 * CD * AH) * (w : ℝ)⁻¹ := by
    have hwaddPos : (0 : ℝ) < ((w + 1 : ℕ) : ℝ) := by positivity
    have hwCastLe : (w : ℝ) ≤ ((w + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show w ≤ w + 1 by omega)
    have hwInv : ((w + 1 : ℕ) : ℝ)⁻¹ ≤ (w : ℝ)⁻¹ :=
      inv_anti₀ hwR hwCastLe
    have hDH : (Dmax : ℝ) * (H : ℝ) ≤
        (CD * ((w + 1 : ℕ) : ℝ)) *
          (AH * ((w + 1 : ℕ) : ℝ)) :=
      mul_le_mul hDreal hHreal (by positivity) (by positivity)
    have htwoDH := mul_le_mul_of_nonneg_left hDH (by norm_num : (0 : ℝ) ≤ 2)
    have hwithInv := mul_le_mul_of_nonneg_right htwoDH
      (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ (Bexc : ℝ)))
    calc
      _ = (2 * ((Dmax : ℝ) * (H : ℝ))) * (Bexc : ℝ)⁻¹ := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ (2 * ((CD * ((w + 1 : ℕ) : ℝ)) *
          (AH * ((w + 1 : ℕ) : ℝ)))) * (Bexc : ℝ)⁻¹ := hwithInv
      _ = (2 * CD * AH) * (((w + 1 : ℕ) : ℝ))⁻¹ := by
        rw [hBexcR]
        field_simp [hwaddPos.ne']
      _ ≤ (2 * CD * AH) * (w : ℝ)⁻¹ := by
        exact mul_le_mul_of_nonneg_left hwInv (by positivity)
  have hpRatio : (p : ℝ) * (nG : ℝ)⁻¹ ≤
      (scale : ℝ) * ((W : ℝ) ^ 8)⁻¹ := by
    rw [hpR]
    have hprodPos : 0 < (nval : ℝ) * (W : ℝ) ^ 8 :=
      mul_pos hnvalPos (pow_pos (by positivity) 8)
    have hinv : (nG : ℝ)⁻¹ ≤
        ((nval : ℝ) * (W : ℝ) ^ 8)⁻¹ :=
      inv_anti₀ hprodPos hnGR.le
    calc
      (scale : ℝ) * (nval : ℝ) * (nG : ℝ)⁻¹ ≤
          (scale : ℝ) * (nval : ℝ) *
            ((nval : ℝ) * (W : ℝ) ^ 8)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (scale : ℝ) * ((W : ℝ) ^ 8)⁻¹ := by
        field_simp [hnvalPos.ne']
  have hpowW : (w : ℝ) ^ 8 ≤ (W : ℝ) ^ 8 := by
    have hwCast : (w : ℝ) ≤ (W : ℝ) := by exact_mod_cast hWlower
    exact pow_le_pow_left₀ (by positivity) hwCast 8
  have hWinv : ((W : ℝ) ^ 8)⁻¹ ≤ ((w : ℝ) ^ 8)⁻¹ :=
    inv_anti₀ (pow_pos hwR 8) hpowW
  have hterm3 : (Dmax : ℝ) *
      (4 * (p : ℝ) * ((1 - c⁻¹)⁻¹ * (nG : ℝ)⁻¹)) ≤
      (8 * CD * (scale : ℝ) * (1 - c⁻¹)⁻¹) * (w : ℝ)⁻¹ := by
    let u : ℝ := (1 - c⁻¹)⁻¹
    have hu : 0 ≤ u := by dsimp [u]; positivity
    have hpair : (Dmax : ℝ) * ((p : ℝ) * (nG : ℝ)⁻¹) ≤
        (2 * CD * (w : ℝ)) *
          ((scale : ℝ) * ((W : ℝ) ^ 8)⁻¹) :=
      mul_le_mul hDtwo hpRatio (by positivity) (by positivity)
    have hpair' : (Dmax : ℝ) * ((p : ℝ) * (nG : ℝ)⁻¹) ≤
        (2 * CD * (w : ℝ)) *
          ((scale : ℝ) * ((w : ℝ) ^ 8)⁻¹) := by
      refine hpair.trans ?_
      gcongr
    have hscaled := mul_le_mul_of_nonneg_left hpair'
      (show 0 ≤ 4 * u by positivity)
    have hi : (w : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hwR).mpr hwOne
    have hpw : ((w : ℝ)⁻¹) ^ 6 ≤ 1 := pow_le_one₀ (by positivity) hi
    have hfac : 0 ≤
        (8 * CD * (scale : ℝ) * u) * (w : ℝ)⁻¹ := by positivity
    calc
      _ = (4 * u) * ((Dmax : ℝ) *
          ((p : ℝ) * (nG : ℝ)⁻¹)) := by dsimp [u]; ring
      _ ≤ (4 * u) * ((2 * CD * (w : ℝ)) *
          ((scale : ℝ) * ((w : ℝ) ^ 8)⁻¹)) := hscaled
      _ = (8 * CD * (scale : ℝ) * u) *
          (w : ℝ)⁻¹ * ((w : ℝ)⁻¹) ^ 6 := by
        field_simp [hwR.ne']
        ring
      _ ≤ (8 * CD * (scale : ℝ) * u) *
          (w : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left hpw hfac
      _ = _ := by dsimp [u]; ring
  have hsum : (Dmax : ℝ) *
      (((4 * W + 2 * Z : ℕ) : ℝ) *
          (c⁻¹ * (1 - c⁻¹)⁻¹ * (nval : ℝ)⁻¹) +
        2 * (H : ℝ) / (Bexc : ℝ) +
        4 * (p : ℝ) * ((1 - c⁻¹)⁻¹ * (nG : ℝ)⁻¹)) ≤
      Cmaj * (w : ℝ)⁻¹ := by
    calc
      _ = (Dmax : ℝ) *
            (((4 * W + 2 * Z : ℕ) : ℝ) *
              (c⁻¹ * (1 - c⁻¹)⁻¹ * (nval : ℝ)⁻¹)) +
          (Dmax : ℝ) * (2 * (H : ℝ) / (Bexc : ℝ)) +
          (Dmax : ℝ) *
            (4 * (p : ℝ) * ((1 - c⁻¹)⁻¹ * (nG : ℝ)⁻¹)) := by ring
      _ ≤ (2 * CD * (12 + 2 * (scale : ℝ)) *
              (c⁻¹ * (1 - c⁻¹)⁻¹)) * (w : ℝ)⁻¹ +
          (2 * CD * AH) * (w : ℝ)⁻¹ +
          (8 * CD * (scale : ℝ) * (1 - c⁻¹)⁻¹) *
            (w : ℝ)⁻¹ := add_le_add (add_le_add hterm1 hterm2) hterm3
      _ = Cmaj * (w : ℝ)⁻¹ := by
        dsimp [Cmaj, Q77, CD, AH]
        rw [hscaleR]
        ring
  simpa [W, p, Z, Dmax, Bexc, scale] using hsum.trans_lt hmajor
end OMAH1Research
namespace OMAH1Research
open Filter Topology
def Q48 (n : ℕ → ℕ) (K : ℕ) : ℕ :=
  Q55 n K / 4
theorem Q206
    (n : ℕ → ℕ) (hmono : StrictMono n) :
    Tendsto (Q48 n) atTop atTop := by
  rw [tendsto_atTop]
  intro w
  have hroot := Q147 n hmono
  filter_upwards [hroot.eventually_ge_atTop (w * 4)] with K hK
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2
  simpa [mul_comm] using hK
theorem Q285
    (n : ℕ → ℕ) (K : ℕ) :
    let w := Q48 n K
    w ^ 8 ≤ n K ∧ n K ≤ (4 * (2 * w + 1)) ^ 8 := by
  let e := Q55 n K
  let w := Q48 n K
  have hwle : w ≤ e := by
    dsimp [w, Q48, e]
    exact Nat.div_le_self _ _
  have hrootUpper : n K ≤ (e + 1) ^ 8 :=
    (Q122 n K).le
  have heLt : e < 4 * (w + 1) := by
    dsimp [w, Q48, e]
    simpa using Nat.lt_mul_div_succ e (by norm_num : 0 < 4)
  have heOne : e + 1 ≤ 4 * (2 * w + 1) := by omega
  refine ⟨?_, hrootUpper.trans (Nat.pow_le_pow_left heOne 8)⟩
  exact (Nat.pow_le_pow_left hwle 8).trans
    (Q171 n K)
theorem Q300
    (n : ℕ → ℕ) (K : ℕ)
    (hroot : 0 < Q55 n K)
    (hgcd : 2 * Q55 n K ≤
      (4 * n K).gcd (Q12 n K)) :
    4 * Q48 n K <
      (4 * n K).gcd (Q12 n K) := by
  have hfour : 4 * Q48 n K ≤ Q55 n K := by
    dsimp [Q48]
    simpa [mul_comm] using Nat.mul_div_le (Q55 n K) 4
  omega
theorem Q209
    (n : ℕ → ℕ) (hmono : StrictMono n) (V : ℕ) :
    ∀ᶠ K : ℕ in atTop,
      let w := Q48 n K
      2 * (4 * 2 ^ V) * ((w + 1) ^ 3) ^ 2 * w ≤ n K := by
  have hradius := Q206 n hmono
  filter_upwards [hradius.eventually_ge_atTop (max 1 (2 ^ V))] with K hK
  let w := Q48 n K
  have hw1 : 1 ≤ w := (le_max_left _ _).trans hK
  have hwV : 2 ^ V ≤ w := (le_max_right _ _).trans hK
  have hsucc : w + 1 ≤ 2 * w := by omega
  have hfour : 4 * w ≤ Q55 n K := by
    dsimp [w, Q48]
    simpa [mul_comm] using Nat.mul_div_le (Q55 n K) 4
  calc
    2 * (4 * 2 ^ V) * ((w + 1) ^ 3) ^ 2 * w
        ≤ 2 * (4 * w) * (((2 * w) ^ 3) ^ 2) * w := by
          gcongr
    _ = 512 * w ^ 8 := by ring
    _ ≤ 65536 * w ^ 8 :=
      Nat.mul_le_mul_right (w ^ 8) (by norm_num)
    _ = (4 * w) ^ 8 := by ring
    _ ≤ Q55 n K ^ 8 := Nat.pow_le_pow_left hfour 8
    _ ≤ n K := Q171 n K
end OMAH1Research
namespace OMAH1Research
open Filter Topology Real goldenRatio
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 10000 in
theorem Q289
    (n : ℕ → ℕ) (hpos : ∀ k, 0 < n k) (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k, c * (n k : ℝ) ≤ n (k + 1))
    (qden : ℕ) (hqden : 0 < qden) (T Tconj : ℝ)
    (hsum : HasSum (fun m : ℕ =>
      (Q1 n m : ℝ) * (φ⁻¹) ^ m) T)
    (htotal : InScaledGoldenPair qden T Tconj)
    (V : ℕ) (hV : ∀ k, Q15 (n k) ≤ V)
    (q : ℕ) (hqpos : 0 < q) (hq : (2 : ℝ) ≤ c ^ q) :
    False := by
  classical
  let ε : ℝ := (((qden : ℕ) : ℝ)⁻¹) ^ 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hdensityW := Q331 c hc q V
  have htailW : ∀ᶠ w : ℕ in atTop,
      (φ⁻¹) ^ w *
        (2 * Q8 (Q9 q V w)) < 1 :=
    (Q269 q V).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hnormW : ∀ᶠ w : ℕ in atTop,
      (φ⁻¹) ^ w *
        (2 * Q8 (Q9 q V w)) *
        (2 * Q10 Tconj
          (Q9 q V w)) < ε :=
    (Q237 q V Tconj).eventually
      (gt_mem_nhds hε)
  have hradius := Q206 n hmono
  have hnumerical : ∀ᶠ K : ℕ in atTop,
      let w := Q48 n K
      (0 < w ∧
        ∀ nval nG d H : ℕ,
          w ^ 8 ≤ nval →
          nval * (2 * w + 1) ^ 8 < nG →
          d ≤ q * (8 * Nat.clog 2 (2 * w + 1) + 1) →
          H ≤ Q9 q V w →
          let W : ℕ := 2 * w + 1
          let p : ℕ := (4 * nval) * 2 ^ V
          let Z : ℕ := (4 * 2 ^ V) * w
          let Dmax : ℕ := (2 * d + 1) * (2 * d + 2)
          let Bexc : ℕ := (w + 1) ^ 3
          (Dmax : ℝ) *
            (((4 * W + 2 * Z : ℕ) : ℝ) *
                (c⁻¹ * (1 - c⁻¹)⁻¹ * (nval : ℝ)⁻¹) +
              2 * (H : ℝ) / (Bexc : ℝ) +
              4 * (p : ℝ) * ((1 - c⁻¹)⁻¹ * (nG : ℝ)⁻¹)) < 1) ∧
      (φ⁻¹) ^ w *
        (2 * Q8 (Q9 q V w)) < 1 ∧
      (φ⁻¹) ^ w *
        (2 * Q8 (Q9 q V w)) *
        (2 * Q10 Tconj
          (Q9 q V w)) < ε := by
    exact hradius.eventually (hdensityW.and (htailW.and hnormW))
  have hgcd := Q220
    n hpos hmono c hc hratio qden hqden T Tconj hsum htotal q hqpos hq
  have hsize := Q209 n hmono V
  obtain ⟨Kodd, hKodd⟩ :=
    Q266 n hpos V hV
  have hodd : ∀ᶠ K : ℕ in atTop,
      Odd (Q11 (n K) /
        (Q11 (n K)).gcd (Q12 n K)) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨Kodd + 1, ?_⟩
    intro K hK
    exact hKodd K (by omega)
  have hall := hgcd.and (hsize.and (hodd.and hnumerical))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hall
  obtain ⟨K, hNK, hnew⟩ :=
    Q358 n hpos hmono N
  have hdata := hN K hNK.le
  rcases hdata with ⟨hgcdK, hsizeK, hoddK, hnumK⟩
  let w := Q48 n K
  let P := Q12 n K
  have hw : 0 < w := hnumK.1.1
  have hrootPos : 0 < Q55 n K := by
    dsimp [w, Q48] at hw
    omega
  have hwindow : 4 * w < (4 * n K).gcd P := by
    exact Q300 n K hrootPos
      (by simpa [P] using hgcdK)
  have hP : 0 < P := Q82 n hpos K
  have htwoQuot :=
    Q132
      P (n K) hP (hpos K) (by simpa [P] using hnew)
        (by simpa [P] using hoddK)
  obtain ⟨X, r, v, hPX, hXbound, hX, hrpos, hrn, hdist⟩ :=
    Q134
      P (n K) (hpos K) htwoQuot.1 htwoQuot.2
  let Dtarget := n K - r
  have hDpos : 0 < Dtarget := by dsimp [Dtarget]; omega
  have hDlt : Dtarget < n K := by dsimp [Dtarget]; omega
  have hg4dvd : (4 * n K).gcd P ∣ 2 * (2 * n K).gcd P := by
    exact Q307 (n K) P
  have hg4le : (4 * n K).gcd P ≤ 2 * (2 * n K).gcd P :=
    Nat.le_of_dvd (by positivity) hg4dvd
  have hwD : w < Dtarget := by
    have : 4 * w < 4 * Dtarget := by
      calc
        4 * w < (4 * n K).gcd P := hwindow
        _ ≤ 2 * (2 * n K).gcd P := hg4le
        _ = 4 * Dtarget := by
          dsimp [Dtarget]
          rw [← hdist]
          ring
    omega
  have hwr : w < r := by
    let d := (2 * n K).gcd P
    have hdpos : 0 < d := by
      dsimp [d]
      exact Nat.gcd_pos_of_pos_left P (by omega)
    have hfac : d * ((2 * n K) / d) = 2 * n K :=
      Nat.mul_div_cancel' (by dsimp [d]; exact Nat.gcd_dvd_left _ _)
    have hmul := Nat.mul_le_mul_left d htwoQuot.2
    have hthreeD : 3 * Dtarget ≤ n K := by
      rw [hfac] at hmul
      have hdEq : d = 2 * Dtarget := by
        dsimp [d, Dtarget]
        omega
      rw [hdEq] at hmul
      nlinarith
    have hfourD : 4 * w < 4 * Dtarget := by
      exact (Nat.mul_lt_mul_left (by norm_num : 0 < 4)).2 hwD
    dsimp [Dtarget] at hthreeD ⊢
    omega
  obtain ⟨hA, hpre, hmid, hpost⟩ :=
    Q130
      (n K) 1 w X r v (hpos K) (by norm_num) hX hrpos hrn hwr hwD
  have hDdvd : Dtarget ∣ n K := by
    apply (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp
    rw [show 2 * Dtarget = (2 * n K).gcd P by
      dsimp [Dtarget]
      omega]
    exact Nat.gcd_dvd_left _ _
  let Q := n K / Dtarget
  have hQ : n K = Q * Dtarget := by
    dsimp [Q]
    exact (Nat.div_mul_cancel hDdvd).symm
  have hXcenter : Dtarget + X = n K * (2 * v + 1) := by
    have hDr : Dtarget + r = n K := by
      dsimp [Dtarget]
      omega
    rw [hX, ← add_assoc, hDr]
    ring
  let W := 2 * w + 1
  let Bval := n K * W ^ 8
  obtain ⟨G, hKG, hBG, hvalues, hGbound, hdcard⟩ :=
    Q208
      n hpos hmono c hc hratio q hq K W (by dsimp [W]; omega)
  let H := Q31
    n K G Bval w Dtarget X V q
  have hrootBounds := Q285 n K
  have hnlow : w ^ 8 ≤ n K := by simpa [w] using hrootBounds.1
  have hnupper : n K ≤ (4 * (2 * w + 1)) ^ 8 := by
    simpa [w] using hrootBounds.2
  have hHbound : H ≤ Q9 q V w := by
    dsimp [H]
    apply Q173
      n hpos hmono c hc hratio q K G w Dtarget X V hq
    · exact hDlt
    · exact hnupper
    · simpa [W] using hGbound
    · simpa [W] using hdcard
    · simpa [P] using hXbound
  have hdensity :
      let p := (4 * n K) * 2 ^ V
      let Z := (4 * 2 ^ V) * w
      let d := (Q0 K G).card
      let Dmax := (2 * d + 1) * (2 * d + 2)
      (Dmax : ℝ) *
        (((4 * W + 2 * Z : ℕ) : ℝ) *
            (c⁻¹ * (1 - c⁻¹)⁻¹ * (n K : ℝ)⁻¹) +
          2 * (H : ℝ) / (((w + 1) ^ 3 : ℕ) : ℝ) +
          4 * (p : ℝ) * ((1 - c⁻¹)⁻¹ * (n G : ℝ)⁻¹)) < 1 := by
    exact hnumK.1.2 (n K) (n G) (Q0 K G).card H
      hnlow (by simpa [Bval, W] using hBG)
      (by simpa [W] using hdcard) hHbound
  have htailMono : Q8 H ≤
      Q8 (Q9 q V w) :=
    Q332 hHbound
  have hconjMono : Q10 Tconj H ≤
      Q10 Tconj (Q9 q V w) :=
    Q251 Tconj hHbound
  have hpostCap :
      (φ⁻¹) ^ (w + 1) * (2 * Q8 H) < 1 := by
    have hr : 0 ≤ (φ⁻¹ : ℝ) := by positivity
    have hrle : φ⁻¹ ≤ (1 : ℝ) :=
      (inv_le_one₀ Real.goldenRatio_pos).2 Real.one_lt_goldenRatio.le
    have hpow : (φ⁻¹) ^ (w + 1) ≤ (φ⁻¹) ^ w := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hr w) hrle
    have ht0 : 0 ≤ 2 * Q8 H :=
      mul_nonneg (by norm_num) (Q34 H)
    have htB0 : 0 ≤ 2 * Q8
        (Q9 q V w) :=
      mul_nonneg (by norm_num)
        (Q34 (Q9 q V w))
    have htmono : 2 * Q8 H ≤
        2 * Q8 (Q9 q V w) :=
      mul_le_mul_of_nonneg_left htailMono (by norm_num)
    calc
      (φ⁻¹) ^ (w + 1) * (2 * Q8 H) ≤
          (φ⁻¹) ^ w *
            (2 * Q8 (Q9 q V w)) :=
        mul_le_mul hpow htmono ht0 (pow_nonneg hr w)
      _ < 1 := hnumK.2.1
  have hpreCap :
      (φ⁻¹) ^ w * (2 * Q8 H) *
        (2 * Q10 Tconj H) < ε := by
    have hpow : 0 ≤ (φ⁻¹ : ℝ) ^ w := by positivity
    have htmono : 2 * Q8 H ≤
        2 * Q8 (Q9 q V w) :=
      mul_le_mul_of_nonneg_left htailMono (by norm_num)
    have hcmono : 2 * Q10 Tconj H ≤
        2 * Q10 Tconj
          (Q9 q V w) :=
      mul_le_mul_of_nonneg_left hconjMono (by norm_num)
    have hfirst : (φ⁻¹) ^ w * (2 * Q8 H) ≤
        (φ⁻¹) ^ w *
          (2 * Q8 (Q9 q V w)) :=
      mul_le_mul_of_nonneg_left htmono hpow
    have hcH0 : 0 ≤ 2 * Q10 Tconj H :=
      mul_nonneg (by norm_num) (Q36 Tconj H)
    have hbaseB0 : 0 ≤ (φ⁻¹) ^ w *
        (2 * Q8 (Q9 q V w)) :=
      mul_nonneg hpow (mul_nonneg (by norm_num)
        (Q34 (Q9 q V w)))
    calc
      _ ≤ (φ⁻¹) ^ w *
          (2 * Q8 (Q9 q V w)) *
          (2 * Q10 Tconj H) :=
        mul_le_mul_of_nonneg_right hfirst hcH0
      _ ≤ (φ⁻¹) ^ w *
          (2 * Q8 (Q9 q V w)) *
          (2 * Q10 Tconj
            (Q9 q V w)) :=
        mul_le_mul_of_nonneg_left hcmono hbaseB0
      _ < ε := hnumK.2.2
  apply Q149
    n hpos hmono c hc hratio qden hqden T Tconj hsum htotal
      q hq K G Bval w Dtarget Q X V v ((w + 1) ^ 3) {K}
  · exact hKG
  · dsimp [Bval]
    exact mul_pos (hpos K) (pow_pos (by dsimp [W]; omega) 8)
  · simpa [Bval, W] using hvalues
  · exact hw
  · exact hwD
  · exact hDlt
  · positivity
  · exact hQ
  · exact hXcenter
  · intro j _ _ _
    exact hV j
  · simpa [w] using hsizeK
  · simp
  · intro k hk
    have hkEq : k = K := Finset.mem_singleton.mp hk
    subst k
    exact hKG
  · exact hPX
  · intro k hk
    have hkEq : k = K := Finset.mem_singleton.mp hk
    subst k
    exact dvd_trans (Q160 (n K))
      ⟨2 ^ V, by ring⟩
  · intro s hs
    simpa [Dtarget, Q73,
      Q26] using hpre s hs
  · simpa [Dtarget, Q73,
      Q26] using hmid
  · intro s hs
    simpa [Dtarget, Q73,
      Q26] using hpost s hs
  · simpa [H, W] using hdensity
  · simpa [H] using hpostCap
  · simpa [H, ε] using hpreCap
end OMAH1Research
namespace OMAH1Research
open Real goldenRatio
theorem irrational_reciprocal_fib_of_ratio_gap
    (n : ℕ → ℕ) (hpos : ∀ k : ℕ, 0 < n k)
    (hmono : StrictMono n)
    (c : ℝ) (hc : 1 < c)
    (hratio : ∀ k : ℕ, c * (n k : ℝ) ≤ n (k + 1)) :
    Irrational (∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹) := by
  rw [irrational_iff_ne_rational]
  intro a b hb hrat
  let r : ℚ := (a : ℚ) / (b : ℚ)
  have hcast : (r : ℝ) = (a : ℝ) / (b : ℝ) := by
    simp [r]
  have hrat' : (∑' k : ℕ, (Nat.fib (n k) : ℝ)⁻¹) = (r : ℝ) :=
    hrat.trans hcast.symm
  obtain ⟨q, hqpos, hq⟩ := Q362 c hc
  obtain ⟨cfg, _hcover, hbounded, _htails⟩ :=
    Q197
      n hpos hmono c hc hratio q hqpos hq r hrat'
  obtain ⟨V, hV⟩ := hbounded
  have hposCfg := cfg.sequence_pos hpos
  have hmonoCfg := cfg.sequence_strictMono hmono
  have hratioCfg := cfg.sequence_ratioGap hmono c hratio
  obtain ⟨qden, hqden, hpair⟩ := cfg.total_pair
  have hsumCfg :=
    Q54 cfg.sequence hposCfg hmonoCfg
  exact Q289
    cfg.sequence hposCfg hmonoCfg c hc hratioCfg
      qden hqden
      ((√5)⁻¹ * (∑' t : ℕ,
        (Nat.fib (cfg.sequence t) : ℝ)⁻¹))
      cfg.conjugate hsumCfg
      (by simpa [DyadicDeletionConfig.sequence] using hpair)
      V hV q hqpos hq
end OMAH1Research

namespace OMAH1Research

open Filter Finset

/-- `H1` from the uniform-gap theorem: shift past the eventual threshold (so every index is
positive) and add back the finite rational head. -/
theorem h1_of_uniform_gap :
    OMA.R_Erdos267_erdos_267_variants_generalisation_ratio_limit_to_infinity_R1.H1 := by
  intro n hn hgap
  obtain ⟨c, hc, hev⟩ := hgap
  obtain ⟨K0, hK0⟩ := eventually_atTop.mp hev
  have hpos : ∀ k, 0 < n (k + (K0 + 1)) := fun k =>
    lt_of_le_of_lt (Nat.zero_le _) (hn (show 0 < k + (K0 + 1) by omega))
  have hmono : StrictMono (fun k => n (k + (K0 + 1))) := fun a b hab => hn (by omega)
  have hratio : ∀ k, c * (n (k + (K0 + 1)) : ℝ) ≤ n (k + 1 + (K0 + 1)) := by
    intro k
    rw [show k + 1 + (K0 + 1) = k + (K0 + 1) + 1 by omega]
    exact hK0 _ (by omega)
  have hirr := irrational_reciprocal_fib_of_ratio_gap (fun k => n (k + (K0 + 1)))
    hpos hmono c hc hratio
  have hsum :=
    (OMA.R_Erdos267_erdos_267_variants_generalisation_ratio_limit_to_infinity_R1.summable_inv_fib
      n hn).sum_add_tsum_nat_add (K0 + 1)
  rw [← hsum]
  have hhead : ∑ i ∈ range (K0 + 1), 1 / (Nat.fib (n i) : ℝ) =
      ((∑ i ∈ range (K0 + 1), 1 / (Nat.fib (n i) : ℚ) : ℚ) : ℝ) := by
    push_cast
    rfl
  rw [hhead]
  simpa only [one_div] using
    Irrational.ratCast_add (q := ∑ i ∈ range (K0 + 1), 1 / (Nat.fib (n i) : ℚ)) hirr

end OMAH1Research

theorem OMA.solution : OMA.R_Erdos267_erdos_267_variants_generalisation_ratio_limit_to_infinity_R1.H1 :=
  OMAH1Research.h1_of_uniform_gap
