import OMAReductions.R_PartitionParity_zheng_odd_R1
import Mathlib

/-!
# Zheng's explicit lower bound for odd partition values

The following finite-counting and asymptotic arguments are adapted from
Axiom Math's MIT-licensed PartitionZheng formalization at commit
`9bfb4326c4ea1e00016a842d7cc145e5c4e0684a`. They formalize Qi-Yang Zheng's
Appendix A to Ken Ono and Ashvin Swaminathan's paper.

<https://github.com/AxiomMath/PartitionZheng/tree/9bfb4326c4ea1e00016a842d7cc145e5c4e0684a>
<https://arxiv.org/html/2509.09553v4>
-/

/-
MIT License

Copyright (c) 2026 Axiom Math.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# The two constants of Zheng's argument

`delta` is the density of admissible discriminants among the integers, and
`beta` bounds their average class number. The final constant
`243 / (64 * sqrt 6 * pi ^ 5)` is `delta ^ 2 / (4 * beta * sqrt 6)`.

## Main definitions

* `PartitionZheng.delta` — the density constant `3 / (8 * pi ^ 2)`.
* `PartitionZheng.beta` — the class-number constant `pi / 108`.
-/


namespace PartitionZheng

open Real

/-- The density of the admissible discriminants: `#D(Y) = delta * Y + O(sqrt Y)`. -/
private noncomputable def delta : ℝ := 3 / (8 * π ^ 2)

/-- The constant bounding the average class number:
`sum_{D in D(Y)} h(D) <= (beta + o(1)) * Y ^ (3/2)`. -/
private noncomputable def beta : ℝ := π / 108

/-- The density constant `delta` is positive. -/
lemma delta_pos : 0 < delta := by
  unfold delta; positivity

/-- The density factors as `δ = (1/24) · (9/π²)`.

The two factors are the density `1/24` of one residue class modulo `24` and the
series `∑_{(d,6)=1} μ(d)/d² = 9/π²` of `coprime_moebius_tsum`, the count of the
admissible discriminants up to `Y` being `(Y/24) · ∑_{(d,6)=1} μ(d)/d² + O(√Y)`. -/
theorem delta_eq : delta = (1 / 24) * (9 / π ^ 2) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  unfold delta
  field_simp
  ring

/-- The class-number constant factors as `β = (1/24) · (2/3) · (π/3)`.

The three factors are the prefactor `1/24` left by the two substitutions of the
area integral, the value `(2/3)(4-σ²)^{-1/2}` of the inner `α`-integral given by
`inner_integral`, and the value `π/3` of the resulting `σ`-integral given by
`arcsin_integral`. Their product is `(1/24)(2/3)(π/3) = 2π/216 = π/108`. -/
theorem beta_eq : beta = (1 / 24) * ((2 / 3) * (π / 3)) := by
  unfold beta
  ring

/-- The class-number constant `beta` is positive. -/
lemma beta_pos : 0 < beta := by
  unfold beta; positivity

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# Admissible discriminants, and recovering one from a partition index

For square-free `D ≡ 23 [MOD 24]` the parity theorem produces an `n` with
`24 * n = D * m ^ 2 + 1` and `p n` odd. This file fixes the set of such `D` up
to a bound, and the square-free part, which is what recovers `D` from `n`.

## Main definitions

* `PartitionZheng.admissible` — the `D` with `1 < D ≤ Y`, `D ≡ 23 [MOD 24]`,
  `D` square-free.
* `PartitionZheng.sqfPart` — the product of the primes dividing `N` to an odd
  power.
-/


namespace PartitionZheng

/-- The admissible discriminants up to `Y`: square-free `D` with `1 < D ≤ Y` and
`D ≡ 23 [MOD 24]`. A `Finset` rather than a `Set`, since `D ≤ Y` bounds it and
the counting argument needs its cardinality. -/
private noncomputable def admissible (Y : ℝ) : Finset ℕ :=
  (Finset.Icc 2 ⌊Y⌋₊).filter fun D => D % 24 = 23 ∧ Squarefree D

/-- The square-free part of `N`: the product of the primes dividing `N` to an
odd power. Zheng's injectivity step recovers the discriminant as
`sqfPart (24 * n - 1)`. -/
private noncomputable def sqfPart (N : ℕ) : ℕ :=
  N.primeFactors.prod fun q => if Odd (N.factorization q) then q else 1

/-- `D` is an admissible discriminant up to `Y` exactly when `2 ≤ D ≤ ⌊Y⌋₊`,
`D % 24 = 23` and `D` is square-free. -/
lemma mem_admissible {Y : ℝ} {D : ℕ} :
    D ∈ admissible Y ↔ (2 ≤ D ∧ D ≤ ⌊Y⌋₊) ∧ D % 24 = 23 ∧ Squarefree D := by
  simp [admissible, Finset.mem_filter, Finset.mem_Icc, and_assoc]

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# Reducedness bounds

Two consequences of `|b| ≤ a ≤ c`, both used to turn the count of reduced
triples of discriminant at most `Y` into a lattice count: the first coefficient
is bounded, and for fixed `a` and `b` the outer coefficient `c` is confined to
an interval of length `(Y + b ^ 2 - 4 * a ^ 2) / (4 * a)`.

The bound on `a` is stated as `3 * a ^ 2 ≤ Y` rather than the source's
`a ≤ sqrt (Y / 3)`. The two are equivalent for `a ≥ 0`, which reducedness
supplies, and the squared form is both what the argument produces and what the
summation over `a` consumes.

## Main results

* `PartitionZheng.three_sq_le_disc` — `3 * a ^ 2 ≤ 4 * a * c - b ^ 2`.
* `PartitionZheng.three_sq_le_of_disc_le` — hence `3 * a ^ 2 ≤ Y`.
* `PartitionZheng.c_upper` — the upper bound on `c`.
* `PartitionZheng.c_interval_length` — the length of the interval for `c`.
-/


namespace PartitionZheng

/-- Reducedness gives `4ac - b^2 ≥ 4a^2 - a^2 = 3a^2`. -/
theorem three_sq_le_disc {a b c : ℤ} (hb : |b| ≤ a) (hac : a ≤ c) :
    3 * a ^ 2 ≤ 4 * a * c - b ^ 2 := by
  have ha : 0 ≤ a := le_trans (abs_nonneg b) hb
  have hb2 : b ^ 2 ≤ a ^ 2 := by
    calc b ^ 2 = |b| ^ 2 := (sq_abs b).symm
      _ ≤ a ^ 2 := by nlinarith [abs_nonneg b]
  nlinarith [mul_le_mul_of_nonneg_left hac (by linarith : (0:ℤ) ≤ 4 * a)]

/-- A reduced triple of discriminant at most `Y` has `3 * a ^ 2 ≤ Y`; for
`a ≥ 0` this is the source's `a ≤ sqrt (Y / 3)`. -/
theorem three_sq_le_of_disc_le {a b c : ℤ} {Y : ℝ} (hb : |b| ≤ a) (hac : a ≤ c)
    (hY : ((4 * a * c - b ^ 2 : ℤ) : ℝ) ≤ Y) : 3 * ((a : ℝ)) ^ 2 ≤ Y := by
  have h := three_sq_le_disc hb hac
  have hcast : ((3 * a ^ 2 : ℤ) : ℝ) ≤ ((4 * a * c - b ^ 2 : ℤ) : ℝ) := by
    exact_mod_cast h
  push_cast at hcast hY
  linarith

/-- For `a ≥ 1`, the condition `4ac - b^2 ≤ Y` is an upper bound on `c`. -/
theorem c_upper {a b c : ℤ} {Y : ℝ} (ha : 1 ≤ a)
    (hY : ((4 * a * c - b ^ 2 : ℤ) : ℝ) ≤ Y) :
    (c : ℝ) ≤ (Y + (b : ℝ) ^ 2) / (4 * (a : ℝ)) := by
  have ha' : (0 : ℝ) < 4 * (a : ℝ) := by
    have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  rw [le_div_iff₀ ha']
  push_cast at hY
  linarith

/-- The admissible `c` for fixed `a ≥ 1` and `b` lie between `a` (reducedness)
and `(Y + b ^ 2) / (4 * a)` (the discriminant bound), an interval of length
`(Y + b ^ 2 - 4 * a ^ 2) / (4 * a)`. -/
theorem c_interval_length {a b : ℤ} {Y : ℝ} (ha : 1 ≤ a) :
    (Y + (b : ℝ) ^ 2) / (4 * (a : ℝ)) - (a : ℝ)
      = (Y + (b : ℝ) ^ 2 - 4 * (a : ℝ) ^ 2) / (4 * (a : ℝ)) := by
  have ha' : (0 : ℝ) < 4 * (a : ℝ) := by
    have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  field_simp

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# Binary quadratic forms of a given discriminant

The class number `h D` is *defined* here as the number of reduced primitive
positive-definite binary quadratic forms of discriminant `-D`. Reduced means
`|b| ≤ a ≤ c` together with the boundary condition `0 ≤ b` whenever `|b| = a`
or `a = c`; that condition is what makes the representative of a class unique
(Cox, Theorem 2.8), so without it the count exceeds the class number rather
than computing it.

Taking the correspondence definitionally is what keeps the ideal class group,
Gauss composition and reduction theory out of this development entirely — none
of which Mathlib has.

Only one direction is ever used: the argument needs an upper bound for `h D`,
so it is enough that every class is counted at least once. `classNumber_le`
discards the boundary condition and primitivity together, each of which can
only increase the count.

## Main definitions

* `PartitionZheng.IsReducedTriple` — `|b| ≤ a ≤ c` and `4ac - b² = D`.
* `PartitionZheng.reducedTriples` — the triples of discriminant `-D`.
* `PartitionZheng.reducedTriplesUpTo` — those of discriminant at most `Y`
  in the admissible congruence class.
* `PartitionZheng.reducedForms` — the primitive, boundary-normalised ones.
* `PartitionZheng.classNumber` — `h D`, their number.

## Main results

* `PartitionZheng.reducedTriples_finite` — the triple set is finite.
* `PartitionZheng.classNumber_le` — `h D ≤ #(reducedTriples D)`.
-/


namespace PartitionZheng

/-- `[a,b,c]` is a reduced triple of discriminant `-D`: `|b| ≤ a ≤ c` and
`4ac - b² = D`. Positive-definiteness is implied, since `D > 0` and `a ≤ c`
force `a > 0`. -/
private def IsReducedTriple (D a b c : ℤ) : Prop :=
  |b| ≤ a ∧ a ≤ c ∧ 4 * a * c - b ^ 2 = D

/-- `[a,b,c]` is moreover a *form*: primitive, and boundary-normalised so that
each class has exactly one such representative. -/
private def IsReducedForm (D a b c : ℤ) : Prop :=
  IsReducedTriple D a b c ∧ Int.gcd (Int.gcd a b) c = 1 ∧
    ((|b| = a ∨ a = c) → 0 ≤ b)

/-- The reduced triples of discriminant `-D`. -/
private def reducedTriples (D : ℤ) : Set (ℤ × ℤ × ℤ) :=
  {p | IsReducedTriple D p.1 p.2.1 p.2.2}

/-- The reduced triples of discriminant at most `Y`, in the admissible
congruence class modulo `24`. -/
private def reducedTriplesUpTo (Y : ℝ) : Set (ℤ × ℤ × ℤ) :=
  {p | |p.2.1| ≤ p.1 ∧ p.1 ≤ p.2.2 ∧
       0 < 4 * p.1 * p.2.2 - p.2.1 ^ 2 ∧
       ((4 * p.1 * p.2.2 - p.2.1 ^ 2 : ℤ) : ℝ) ≤ Y ∧
       (4 * p.1 * p.2.2 - p.2.1 ^ 2) % 24 = 23}

/-- The reduced primitive forms of discriminant `-D`. -/
private def reducedForms (D : ℤ) : Set (ℤ × ℤ × ℤ) :=
  {p | IsReducedForm D p.1 p.2.1 p.2.2}

/-- The class number `h D`, as the number of reduced primitive forms of
discriminant `-D`. -/
private noncomputable def classNumber (D : ℤ) : ℕ := (reducedForms D).ncard

/-- A reduced triple of positive discriminant has `a ≥ 1`: `a = 0` forces
`b = 0` and then the discriminant is `0`. -/
theorem one_le_a_of_mem {D a b c : ℤ} (hD : 0 < D) (h : IsReducedTriple D a b c) :
    1 ≤ a := by
  obtain ⟨hb, hac, hdisc⟩ := h
  have ha : 0 ≤ a := le_trans (abs_nonneg b) hb
  rcases eq_or_lt_of_le ha with rfl | ha1
  · have hb0 : b = 0 := abs_nonpos_iff.mp hb
    rw [hb0] at hdisc
    norm_num at hdisc
    omega
  · omega

/-- Every reduced triple of discriminant `-D` has all three coefficients in
`[-D, D]`, so the set is finite. -/
theorem reducedTriples_finite {D : ℤ} (hD : 0 < D) : (reducedTriples D).Finite := by
  -- There is no `LocallyFiniteOrder (ℤ × ℤ × ℤ)`, so bound by a product of
  -- interval *sets* rather than an `Icc` of the product.
  have hfin : (Set.Icc (-D) D ×ˢ (Set.Icc (-D) D ×ˢ Set.Icc (-D) D)).Finite :=
    (Set.finite_Icc _ _).prod ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _))
  refine hfin.subset ?_
  rintro ⟨a, b, c⟩ hp
  -- Ascribe the type so the projections beta-reduce to `a`, `b`, `c`;
  -- otherwise `omega` sees `(a, b, c).2.1` and `b` as distinct atoms.
  obtain ⟨hb, hac, hdisc⟩ : IsReducedTriple D a b c := hp
  have ha1 : 1 ≤ a := one_le_a_of_mem hD ⟨hb, hac, hdisc⟩
  have hb2 : b ^ 2 ≤ a ^ 2 := by
    calc b ^ 2 = |b| ^ 2 := (sq_abs b).symm
      _ ≤ a ^ 2 := by nlinarith [abs_nonneg b]
  have h3 : 3 * a ^ 2 ≤ D := by
    have h := three_sq_le_disc hb hac
    omega
  have haD : a ≤ D := by nlinarith [sq_nonneg a, sq_nonneg (a - 1)]
  have hbD : |b| ≤ D := le_trans hb haD
  have hbl : -D ≤ b := neg_le_of_abs_le hbD
  have hbu : b ≤ D := le_of_abs_le hbD
  have hcD : c ≤ D := by nlinarith [sq_nonneg a, sq_nonneg (c - a)]
  simp only [Set.mem_prod, Set.mem_Icc]
  omega

/-- Dropping primitivity and the boundary condition can only increase the
count, so the class number is at most the number of reduced triples. -/
theorem classNumber_le {D : ℤ} (hD : 0 < D) :
    classNumber D ≤ (reducedTriples D).ncard := by
  refine Set.ncard_le_ncard ?_ (reducedTriples_finite hD)
  rintro ⟨a, b, c⟩ ⟨htriple, _, _⟩
  exact htriple

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# The inner integral

The area integral of the lattice count reduces, after the substitutions
`a = sqrt Y * α` and `t = a * σ`, to an inner integral in `α` over the range
where the integrand is positive, namely `0 ≤ α < (4 - σ²)^{-1/2}`. Writing
`c = 4 - σ²` and `A = c^{-1/2}`, so that `c * A ^ 2 = 1`, that integral is

`∫_0^A (1 - c α²) dα = A - c A³/3 = A - A/3 = 2A/3`.

## Main results

* `PartitionZheng.integral_one_sub_const_mul_sq` — the polynomial integral.
* `PartitionZheng.inner_integral` — its value `2 * A / 3` when `c * A ^ 2 = 1`.
-/


namespace PartitionZheng

/-- The polynomial integral, with no relation assumed between `c` and `A`. -/
theorem integral_one_sub_const_mul_sq (c A : ℝ) :
    (∫ α in (0 : ℝ)..A, (1 - c * α ^ 2)) = A - c * A ^ 3 / 3 := by
  have hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume 0 A :=
    intervalIntegrable_const
  have hsq : IntervalIntegrable (fun α : ℝ => c * α ^ 2) MeasureTheory.volume 0 A :=
    (intervalIntegral.intervalIntegrable_pow 2).const_mul c
  rw [intervalIntegral.integral_sub hone hsq, intervalIntegral.integral_const_mul]
  simp
  ring

/-- With `c * A ^ 2 = 1`, the inner integral is `2 * A / 3`. This is the
`(2/3) * (4 - σ²)^{-1/2}` of the source. -/
theorem inner_integral {c A : ℝ} (h : c * A ^ 2 = 1) :
    (∫ α in (0 : ℝ)..A, (1 - c * α ^ 2)) = 2 * A / 3 := by
  rw [integral_one_sub_const_mul_sq]
  have hcube : c * A ^ 3 = A := by
    calc c * A ^ 3 = (c * A ^ 2) * A := by ring
      _ = A := by rw [h]; ring
  rw [show c * A ^ 3 / 3 = A / 3 by rw [hcube]]
  ring

/-- The area function of the lattice count:
`F_Y a = (1 / (24 a)) * ∫_{-a}^{a} (Y + t² - 4a²)_+ dt`, where `x_+ = max x 0`.
Its integral over `a > 0` is what produces the `pi / 108` of the class-number
average. -/
private noncomputable def areaF (Y a : ℝ) : ℝ :=
  (1 / (24 * a)) * ∫ t in (-a)..a, max (Y + t ^ 2 - 4 * a ^ 2) 0

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# The residue weight

For a fixed first coefficient `a`, the discriminant congruence confines the
outer coefficient `c` to a union of residue classes modulo `6`: those with
`a * c ≡ 0` when `b` is coprime to `3`, and those with `a * c ≡ 2` when
`3 ∣ b`. Counting the first case twice — once for each of `b ≡ 1, 5 [MOD 6]` —
gives the weight `w a`.

It depends on `a` only through `a` modulo `6`, and takes the values
`12, 3, 6, 6, 6, 3`, so its mean over a period is `6`. That mean is what lets
partial summation replace `w a / 6` by `1` in the lattice count.

## Main definitions

* `PartitionZheng.weight` — the weight `w a`.

## Main results

* `PartitionZheng.weight_values` — the six values.
* `PartitionZheng.weight_sum` — they sum to `36`, hence mean `6`.
-/


namespace PartitionZheng

/-- The total weight of the residue classes the congruence admits for the outer
coefficient, with the `a * c ≡ 0` count taken twice, once for each of
`b ≡ 1, 5 [MOD 6]`. -/
private def weight (a : ℤ) : ℕ :=
  2 * (Finset.univ.filter fun c : ZMod 6 => (a : ZMod 6) * c = 0).card
    + (Finset.univ.filter fun c : ZMod 6 => (a : ZMod 6) * c = 2).card

/-- `weight` reads its argument only through `ZMod 6`, so it is periodic with
period `6`. -/
theorem weight_eq_of_cast {a a' : ℤ} (h : (a : ZMod 6) = (a' : ZMod 6)) :
    weight a = weight a' := by
  unfold weight; rw [h]

/-- The six values of the weight: `12, 3, 6, 6, 6, 3` for
`a ≡ 0, 1, 2, 3, 4, 5 [MOD 6]`. -/
theorem weight_values :
    weight 0 = 12 ∧ weight 1 = 3 ∧ weight 2 = 6 ∧
    weight 3 = 6 ∧ weight 4 = 6 ∧ weight 5 = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The weight sums to `36` over a period, so its mean is `6`. -/
theorem weight_sum :
    weight 0 + weight 1 + weight 2 + weight 3 + weight 4 + weight 5 = 36 := by
  decide

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# The class-number average

The total class number of the admissible discriminants up to `Y` is at most
`(beta + ε) Y^{3/2}` for every `ε > 0` once `Y` is large, where
`beta = π / 108`.

The passage from class numbers to a lattice count is the content of this file.
Every reduced form of discriminant `-D` is a reduced triple, and for distinct
`D` those triple sets are disjoint — the discriminant `4ac - b²` separates
them — so the total class number is at most the number of triples in
`reducedTriplesUpTo Y`. Fibring that set over its first coefficient `a`, which
reducedness confines to `1 ≤ a ≤ sqrt (Y / 3)`, turns the count into a sum over
`a` of the per-`a` counts, which is what the lattice-point estimate bounds.

The two error sums are handled here: `∑_{a ≤ sqrt (Y/3)} 1/a` by Mathlib's
harmonic bound, and `∑_{a ≤ sqrt (Y/3)} a` by bounding every term by the number
of terms. Both are absorbed into `Y (1 + log Y)`, and
`Y (1 + log Y) ≤ ε Y^{3/2}` for large `Y` is proved by writing `Y = v⁴` with
`v` the fourth root, so that `log Y = 4 log v ≤ 4 v` reduces the claim to a
polynomial inequality in `v`.

Following the convention of `PartitionZheng.ZH`, `Y ^ (3/2)` is written
`Y * sqrt Y`, which agrees with it on the range `Y ≥ 0` where it is used and
avoids `rpow`.

## Main results

* `PartitionZheng.reducedTriplesUpTo_finite` — the lattice set is finite.
* `PartitionZheng.sum_classNumber_le_ncard` — the total class number is at most
  `#T*(Y)`.
* `PartitionZheng.ncard_reducedTriplesUpTo_le_sum` — fibring `T*(Y)` over `a`.
* `PartitionZheng.class_average` — the class-number average.
-/


namespace PartitionZheng

/- ### The lattice set and its fibres -/

/-- Membership in `reducedTriplesUpTo` spelled out on an explicit triple. The
ascription is what beta-reduces the projections `(a, b, c).2.1`, without which
`omega` treats them as atoms distinct from `b`. -/
theorem mem_reducedTriplesUpTo {Y : ℝ} {a b c : ℤ} :
    (a, b, c) ∈ reducedTriplesUpTo Y ↔
      |b| ≤ a ∧ a ≤ c ∧ 0 < 4 * a * c - b ^ 2 ∧
        ((4 * a * c - b ^ 2 : ℤ) : ℝ) ≤ Y ∧ (4 * a * c - b ^ 2) % 24 = 23 :=
  Iff.rfl

/-- Reducedness confines the first coefficient of a triple of discriminant at
most `Y` to `1 ≤ a ≤ sqrt (Y / 3)`. -/
theorem reducedTriplesUpTo_fst_bounds {Y : ℝ} {p : ℤ × ℤ × ℤ} (hp : p ∈ reducedTriplesUpTo Y) :
    1 ≤ p.1 ∧ (p.1 : ℝ) ≤ Real.sqrt (Y / 3) := by
  obtain ⟨a, b, c⟩ := p
  obtain ⟨hb, hac, hpos, hle, -⟩ := mem_reducedTriplesUpTo.mp hp
  refine ⟨one_le_a_of_mem hpos ⟨hb, hac, rfl⟩, ?_⟩
  have h := three_sq_le_of_disc_le hb hac hle
  exact Real.le_sqrt_of_sq_le (by linarith)

/-- The triples of discriminant at most `Y` form a finite set: the discriminant
`D = 4ac - b²` satisfies `0 < D ≤ ⌊Y⌋`, and `3a² ≤ D` with `|b| ≤ a ≤ c` bounds
all three coefficients by `D`. -/
theorem reducedTriplesUpTo_finite (Y : ℝ) : (reducedTriplesUpTo Y).Finite := by
  have hfin : (Set.Icc (-⌊Y⌋) ⌊Y⌋ ×ˢ
      (Set.Icc (-⌊Y⌋) ⌊Y⌋ ×ˢ Set.Icc (-⌊Y⌋) ⌊Y⌋)).Finite :=
    (Set.finite_Icc _ _).prod ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _))
  refine hfin.subset ?_
  rintro ⟨a, b, c⟩ hp
  obtain ⟨hb, hac, hpos, hle, -⟩ := mem_reducedTriplesUpTo.mp hp
  have hDN : 4 * a * c - b ^ 2 ≤ ⌊Y⌋ := Int.le_floor.mpr hle
  have ha1 : 1 ≤ a := one_le_a_of_mem hpos ⟨hb, hac, rfl⟩
  have h3 : 3 * a ^ 2 ≤ 4 * a * c - b ^ 2 := three_sq_le_disc hb hac
  have hbsq : b ^ 2 ≤ a ^ 2 := by
    calc b ^ 2 = |b| ^ 2 := (sq_abs b).symm
      _ ≤ a ^ 2 := by nlinarith [abs_nonneg b]
  have haa : a ≤ a ^ 2 := by nlinarith
  have haN : a ≤ ⌊Y⌋ := by nlinarith
  have hcN : c ≤ ⌊Y⌋ := by nlinarith
  have hbl : -⌊Y⌋ ≤ b := by
    have := neg_le_of_abs_le hb
    omega
  have hbu : b ≤ ⌊Y⌋ := le_trans (le_of_abs_le hb) haN
  simp only [Set.mem_prod, Set.mem_Icc]
  omega

/-- For an admissible `D ≤ Y`, every reduced triple of discriminant `-D` is a
triple of discriminant at most `Y` in the admissible congruence class. -/
theorem reducedTriples_subset_upTo {Y : ℝ} (hY : 0 ≤ Y) {D : ℕ} (hD : D ∈ admissible Y) :
    reducedTriples (D : ℤ) ⊆ reducedTriplesUpTo Y := by
  obtain ⟨⟨hD2, hDY⟩, hmod, -⟩ := mem_admissible.mp hD
  rintro ⟨a, b, c⟩ ⟨hb, hac, hdisc⟩
  refine ⟨hb, hac, ?_, ?_, ?_⟩
  · rw [hdisc]; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hD2
  · rw [hdisc]
    have h1 : (D : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by exact_mod_cast hDY
    have h2 : ((⌊Y⌋₊ : ℕ) : ℝ) ≤ Y := Nat.floor_le hY
    push_cast
    linarith
  · rw [hdisc]; omega

/-- Dropping the class-number normalisations and collecting the triple sets of
all admissible `D ≤ Y`: the total class number is at most `#T*(Y)`. The sets
`T(D)` are disjoint for distinct `D`, being separated by `4ac - b²`. -/
theorem sum_classNumber_le_ncard {Y : ℝ} (hY : 0 ≤ Y) :
    ∑ D ∈ admissible Y, classNumber (D : ℤ) ≤ (reducedTriplesUpTo Y).ncard := by
  classical
  have hfin := reducedTriplesUpTo_finite Y
  set t : ℕ → Finset (ℤ × ℤ × ℤ) :=
    fun D => hfin.toFinset.filter fun p => 4 * p.1 * p.2.2 - p.2.1 ^ 2 = (D : ℤ) with htdef
  have hcoe : ∀ D ∈ admissible Y, (↑(t D) : Set (ℤ × ℤ × ℤ)) = reducedTriples (D : ℤ) := by
    intro D hD
    ext p
    obtain ⟨a, b, c⟩ := p
    simp only [htdef, Finset.coe_filter, Set.mem_ofPred_eq, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨hb, hac, -, -, -⟩, hdisc⟩
      exact ⟨hb, hac, hdisc⟩
    · intro hmem
      exact ⟨reducedTriples_subset_upTo hY hD hmem, hmem.2.2⟩
  have hdisj : (↑(admissible Y) : Set ℕ).PairwiseDisjoint t := by
    intro D _ D' _ hne
    simp only [Function.onFun]
    refine Finset.disjoint_left.mpr ?_
    intro p hp hp'
    simp only [htdef, Finset.mem_filter] at hp hp'
    exact hne (by exact_mod_cast hp.2.symm.trans hp'.2)
  have hsub : (admissible Y).biUnion t ⊆ hfin.toFinset := by
    refine Finset.biUnion_subset.mpr fun D _ => ?_
    simp only [htdef]
    exact Finset.filter_subset _ _
  calc ∑ D ∈ admissible Y, classNumber (D : ℤ)
      ≤ ∑ D ∈ admissible Y, (reducedTriples (D : ℤ)).ncard := by
        refine Finset.sum_le_sum fun D hD => ?_
        have hD2 := (mem_admissible.mp hD).1.1
        exact classNumber_le (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hD2)
    _ = ∑ D ∈ admissible Y, (t D).card := by
        refine Finset.sum_congr rfl fun D hD => ?_
        rw [← hcoe D hD, Set.ncard_coe_finset]
    _ = ((admissible Y).biUnion t).card := (Finset.card_biUnion hdisj).symm
    _ ≤ hfin.toFinset.card := Finset.card_le_card hsub
    _ = (reducedTriplesUpTo Y).ncard := by
        rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]

/-- Fibring the triples of discriminant at most `Y` over their first
coefficient, which `reducedTriplesUpTo_fst_bounds` confines to `1 ≤ a ≤ sqrt (Y / 3)`. -/
theorem ncard_reducedTriplesUpTo_le_sum (Y : ℝ) :
    (reducedTriplesUpTo Y).ncard
      ≤ ∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊,
          {q : ℤ × ℤ | ((a : ℤ), q.1, q.2) ∈ reducedTriplesUpTo Y}.ncard := by
  classical
  have hfin := reducedTriplesUpTo_finite Y
  have hcard : (reducedTriplesUpTo Y).ncard = hfin.toFinset.card := by
    rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
  have hmapsto : Set.MapsTo (fun p : ℤ × ℤ × ℤ => p.1.toNat)
      ↑hfin.toFinset ↑(Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊) := by
    intro p hp
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hp
    obtain ⟨ha1, ha2⟩ := reducedTriplesUpTo_fst_bounds hp
    have h0 : (0 : ℤ) ≤ p.1 := by omega
    have hcast : ((p.1.toNat : ℕ) : ℝ) = (p.1 : ℝ) := by
      rw [← Int.cast_natCast (R := ℝ), Int.toNat_of_nonneg h0]
    have hlow : 1 ≤ p.1.toNat := by omega
    have hhigh : p.1.toNat ≤ ⌊Real.sqrt (Y / 3)⌋₊ :=
      Nat.le_floor (by rw [hcast]; exact ha2)
    simpa [Finset.mem_Icc] using And.intro hlow hhigh
  rw [hcard, Finset.card_eq_sum_card_fiberwise hmapsto]
  refine Finset.sum_le_sum fun a ha => ?_
  have hfibfin : {q : ℤ × ℤ | ((a : ℤ), q.1, q.2) ∈ reducedTriplesUpTo Y}.Finite := by
    have hpre : {q : ℤ × ℤ | ((a : ℤ), q.1, q.2) ∈ reducedTriplesUpTo Y}
        = (fun q : ℤ × ℤ => ((a : ℤ), q.1, q.2)) ⁻¹' reducedTriplesUpTo Y := rfl
    rw [hpre]
    refine Set.Finite.preimage ?_ hfin
    intro x _ y _ h
    simp only [Prod.mk.injEq, true_and] at h
    exact Prod.ext_iff.mpr h
  have hinj : Set.InjOn Prod.snd
      (↑({p ∈ hfin.toFinset | p.1.toNat = a}) : Set (ℤ × ℤ × ℤ)) := by
    intro p hp q hq h
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Set.Finite.mem_toFinset] at hp hq
    have hp1 := (reducedTriplesUpTo_fst_bounds hp.1).1
    have hq1 := (reducedTriplesUpTo_fst_bounds hq.1).1
    have hfsteq := hp.2.trans hq.2.symm
    exact Prod.ext_iff.mpr ⟨by omega, h⟩
  calc ({p ∈ hfin.toFinset | p.1.toNat = a}).card
      = (({p ∈ hfin.toFinset | p.1.toNat = a}).image Prod.snd).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ {q : ℤ × ℤ | ((a : ℤ), q.1, q.2) ∈ reducedTriplesUpTo Y}.ncard := by
        rw [← Set.ncard_coe_finset]
        refine Set.ncard_le_ncard ?_ hfibfin
        intro q hq
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter,
          Set.Finite.mem_toFinset] at hq
        obtain ⟨p, ⟨hpS, hpa⟩, rfl⟩ := hq
        have hp1 := (reducedTriplesUpTo_fst_bounds hpS).1
        have hfst : ((a : ℤ)) = p.1 := by omega
        rw [hfst]
        exact hpS

/- ### The error sums -/

/-- The harmonic sum over `1 ≤ a ≤ y`, from Mathlib's bound on the harmonic
numbers. -/
theorem sum_inv_le_one_add_log {y : ℝ} (hy : 1 ≤ y) :
    ∑ a ∈ Finset.Icc 1 ⌊y⌋₊, ((a : ℝ))⁻¹ ≤ 1 + Real.log y := by
  have h := harmonic_floor_le_one_add_log y hy
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  exact h

/-- The sum of `a` over `1 ≤ a ≤ sqrt (Y / 3)` is at most `Y / 3`, by bounding
every term by the number of terms. -/
theorem sum_natCast_le_div_three {Y : ℝ} (hY : 0 ≤ Y) :
    ∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊, (a : ℝ) ≤ Y / 3 := by
  have hN : ((⌊Real.sqrt (Y / 3)⌋₊ : ℕ) : ℝ) ≤ Real.sqrt (Y / 3) :=
    Nat.floor_le (Real.sqrt_nonneg _)
  have hsq : Real.sqrt (Y / 3) ^ 2 = Y / 3 := Real.sq_sqrt (by linarith)
  have hterm : ∀ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊,
      (a : ℝ) ≤ ((⌊Real.sqrt (Y / 3)⌋₊ : ℕ) : ℝ) :=
    fun a ha => Nat.cast_le.mpr (Finset.mem_Icc.mp ha).2
  calc ∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊, (a : ℝ)
      ≤ (Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊).card •
          ((⌊Real.sqrt (Y / 3)⌋₊ : ℕ) : ℝ) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = ((⌊Real.sqrt (Y / 3)⌋₊ : ℕ) : ℝ) * ((⌊Real.sqrt (Y / 3)⌋₊ : ℕ) : ℝ) := by
        simp [Nat.card_Icc]
    _ ≤ Y / 3 := by nlinarith [Nat.cast_nonneg (α := ℝ) ⌊Real.sqrt (Y / 3)⌋₊]

/-- The two error sums of the lattice count, absorbed into `Y (1 + log Y)`. -/
theorem sum_triple_error_le {Y C : ℝ} (hY : 3 ≤ Y) (hC : 0 < C) :
    ∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊, C * (Y / (a : ℝ) + (a : ℝ))
      ≤ 2 * C * (Y * (1 + Real.log Y)) := by
  have hsplit : ∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊, C * (Y / (a : ℝ) + (a : ℝ))
      = C * Y * (∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊, ((a : ℝ))⁻¹)
        + C * ∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊, (a : ℝ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [div_eq_mul_inv]; ring
  have h1 : (1 : ℝ) ≤ Real.sqrt (Y / 3) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hinv := sum_inv_le_one_add_log h1
  have hid := sum_natCast_le_div_three (Y := Y) (by linarith)
  have hlt : Real.sqrt (Y / 3) ≤ Y := by
    have h := Real.sqrt_le_sqrt (show Y / 3 ≤ Y ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by linarith : (0 : ℝ) ≤ Y)] at h
  have hlogsq : Real.log (Real.sqrt (Y / 3)) ≤ Real.log Y :=
    Real.log_le_log (by linarith) hlt
  have hlog0 : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hCY : (0 : ℝ) ≤ C * Y := mul_nonneg hC.le (by linarith)
  have hA : C * Y * (∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊, ((a : ℝ))⁻¹)
      ≤ C * Y * (1 + Real.log Y) :=
    mul_le_mul_of_nonneg_left (by linarith) hCY
  have hB : C * (∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊, (a : ℝ)) ≤ C * (Y / 3) :=
    mul_le_mul_of_nonneg_left hid hC.le
  have hD : C * (Y / 3) ≤ C * (Y * (1 + Real.log Y)) := by
    refine mul_le_mul_of_nonneg_left ?_ hC.le
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Y) hlog0]
  rw [hsplit]
  nlinarith [hA, hB, hD]

/- ### `Y log Y` is eventually below `ε Y^{3/2}` -/

/-- For every `K, ε > 0` there is a threshold past which
`K Y (1 + log Y) ≤ ε Y^{3/2}`.

Writing `Y = v⁴` with `v` the fourth root of `Y` turns `log Y = 4 log v` and
`log v ≤ v` into the polynomial inequality `K (v⁴ + 4v⁵) ≤ ε v⁶`, which holds
as soon as `v ≥ max 1 (5K/ε)`. -/
theorem exists_mul_log_le {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) :
    ∃ Y₀ : ℝ, 3 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      K * (Y * (1 + Real.log Y)) ≤ ε * (Y * Real.sqrt Y) := by
  have hM1 : (1 : ℝ) ≤ max 1 (5 * K / ε) := le_max_left _ _
  have hM2 : 5 * K / ε ≤ max 1 (5 * K / ε) := le_max_right _ _
  refine ⟨max 3 (max 1 (5 * K / ε) ^ 4), le_max_left _ _, fun Y hY => ?_⟩
  have hY3 : 3 ≤ Y := le_trans (le_max_left _ _) hY
  have hYM : max 1 (5 * K / ε) ^ 4 ≤ Y := le_trans (le_max_right _ _) hY
  have hY0 : (0 : ℝ) < Y := by linarith
  have hs0 : (0 : ℝ) ≤ Real.sqrt Y := Real.sqrt_nonneg Y
  obtain ⟨v, hv0, hv2⟩ : ∃ v : ℝ, 0 ≤ v ∧ v ^ 2 = Real.sqrt Y :=
    ⟨Real.sqrt (Real.sqrt Y), Real.sqrt_nonneg _, Real.sq_sqrt hs0⟩
  have hv4 : v ^ 4 = Y := by
    have h : v ^ 4 = (v ^ 2) ^ 2 := by ring
    rw [h, hv2, Real.sq_sqrt hY0.le]
  have hMs : max 1 (5 * K / ε) ^ 2 ≤ Real.sqrt Y :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hvM : max 1 (5 * K / ε) ≤ v := by nlinarith
  have hv1 : (1 : ℝ) ≤ v := le_trans hM1 hvM
  have hlogv : Real.log v ≤ v :=
    le_trans (Real.log_le_sub_one_of_pos (by linarith)) (by linarith)
  have hlogY : Real.log Y = 4 * Real.log v := by
    rw [← hv4, Real.log_pow]; norm_num
  have hεv : 5 * K ≤ ε * v := by
    have h := le_trans hM2 hvM
    rw [div_le_iff₀ hε] at h
    linarith
  have hv45 : v ^ 4 ≤ v ^ 5 := by
    nlinarith [mul_le_mul_of_nonneg_left hv1 (pow_nonneg hv0 4)]
  have key : K * (v ^ 4 * (1 + 4 * Real.log v)) ≤ ε * (v ^ 4 * v ^ 2) := by
    have h1 : K * (v ^ 4 * (1 + 4 * Real.log v)) ≤ K * (v ^ 4 * (1 + 4 * v)) := by
      nlinarith [mul_le_mul_of_nonneg_left hlogv (mul_nonneg hK.le (pow_nonneg hv0 4))]
    have h2 : K * (v ^ 4 * (1 + 4 * v)) ≤ 5 * K * v ^ 5 := by
      nlinarith [mul_le_mul_of_nonneg_left hv45 hK.le]
    have h3 : 5 * K * v ^ 5 ≤ ε * (v ^ 4 * v ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_right hεv (pow_nonneg hv0 5)]
    linarith
  rw [hlogY, ← hv2, ← hv4]
  exact key

/- ### The class-number average -/

/-- **The class-number average.** For every `ε > 0` there is a `Y₀ ≥ 2` such
that the total class number of the admissible discriminants up to `Y` is at
most `(beta + ε) Y^{3/2}` for every `Y ≥ Y₀`, where `Y^{3/2}` is written
`Y * sqrt Y` and `beta = π / 108`.

The two hypotheses are the lattice-point estimates the bound rests on:

* `hTriple` counts the pairs `(b, c)` completing a fixed first coefficient `a`
  to a triple of discriminant at most `Y`: their number is
  `weight a / 6 * areaF Y a` up to an error `C * (Y / a + a)`.
* `hSummation` sums the area function `areaF` against the residue weight
  `weight` over `1 ≤ a ≤ sqrt (Y / 3)`: the total is
  `π / 108 * Y^{3/2}` up to an error `C * (Y * log Y)`. -/
theorem class_average
    (hTriple : ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 1 ≤ Y → ∀ a : ℤ, 1 ≤ a →
      (a : ℝ) ≤ Real.sqrt (Y / 3) →
      ({q : ℤ × ℤ | (a, q.1, q.2) ∈ reducedTriplesUpTo Y}.ncard : ℝ)
        ≤ (weight a : ℝ) / 6 * areaF Y a + C * (Y / (a : ℝ) + (a : ℝ)))
    (hSummation : ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 2 ≤ Y →
      ∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊, (weight a : ℝ) / 6 * areaF Y a
        ≤ Real.pi / 108 * (Y * Real.sqrt Y) + C * (Y * Real.log Y)) :
    ∀ ε : ℝ, 0 < ε → ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      ∑ D ∈ admissible Y, (classNumber (D : ℤ) : ℝ) ≤ (beta + ε) * (Y * Real.sqrt Y) := by
  obtain ⟨C₁, hC₁, hT⟩ := hTriple
  obtain ⟨C₂, hC₂, hS⟩ := hSummation
  intro ε hε
  obtain ⟨Y₁, hY₁, hbound⟩ :=
    exists_mul_log_le (K := 2 * C₁ + C₂) (ε := ε) (by linarith) hε
  refine ⟨max 3 Y₁, le_trans (by norm_num) (le_max_left _ _), fun Y hY => ?_⟩
  have hY3 : 3 ≤ Y := le_trans (le_max_left _ _) hY
  have hlog0 : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have step1 : ∑ D ∈ admissible Y, (classNumber (D : ℤ) : ℝ)
      ≤ ((reducedTriplesUpTo Y).ncard : ℝ) := by
    exact_mod_cast sum_classNumber_le_ncard (Y := Y) hY0
  have step2 : ((reducedTriplesUpTo Y).ncard : ℝ)
      ≤ ∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊,
          ({q : ℤ × ℤ | ((a : ℤ), q.1, q.2) ∈ reducedTriplesUpTo Y}.ncard : ℝ) := by
    exact_mod_cast ncard_reducedTriplesUpTo_le_sum Y
  have step3 : ∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊,
        ({q : ℤ × ℤ | ((a : ℤ), q.1, q.2) ∈ reducedTriplesUpTo Y}.ncard : ℝ)
      ≤ (∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊, (weight a : ℝ) / 6 * areaF Y a)
        + ∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊, C₁ * (Y / (a : ℝ) + (a : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun a ha => ?_
    obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
    have haR : ((a : ℤ) : ℝ) ≤ Real.sqrt (Y / 3) := by
      have h : ((a : ℕ) : ℝ) ≤ Real.sqrt (Y / 3) := by
        rw [← Nat.le_floor_iff (Real.sqrt_nonneg _)]
        exact ha2
      exact_mod_cast h
    have h := hT Y (by linarith) (a : ℤ) (by exact_mod_cast ha1) haR
    push_cast at h ⊢
    exact h
  have step4 := hS Y (by linarith)
  have step5 := sum_triple_error_le (Y := Y) (C := C₁) hY3 hC₁
  have step6 := hbound Y (le_trans (le_max_right _ _) hY)
  have herr : C₂ * (Y * Real.log Y) ≤ C₂ * (Y * (1 + Real.log Y)) := by
    nlinarith [mul_nonneg hC₂.le hY0]
  have hbeta : beta = Real.pi / 108 := rfl
  rw [hbeta]
  linarith [step1, step2, step3, step4, step5, step6, herr]

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# The arcsine integral

After the substitutions of the lattice count, the outer integral is
`∫_{-1}^{1} (4 - σ²)^{-1/2} dσ`, which is `π / 3`. The antiderivative is
`arcsin (σ / 2)`: by the chain rule its derivative is
`(1/2) * (1 - (σ/2)²)^{-1/2}`, and `√(1 - σ²/4) = √(4 - σ²) / 2`, so that is
`(4 - σ²)^{-1/2}`.

Mathlib has `arcsin 1 = π / 2` but not `arcsin (1/2) = π / 6`, so that is proved
here from `sin (π / 6) = 1 / 2`.

## Main results

* `PartitionZheng.arcsin_half` — `arcsin (1/2) = π / 6`.
* `PartitionZheng.arcsin_integral` — `∫_{-1}^{1} (4 - σ²)^{-1/2} dσ = π / 3`.
-/


namespace PartitionZheng

open Real intervalIntegral

/-- `arcsin (1/2) = π / 6`, from `sin (π / 6) = 1 / 2`. -/
theorem arcsin_half : Real.arcsin (1 / 2) = π / 6 := by
  have hpi := Real.pi_pos
  have h : Real.sin (π / 6) = 1 / 2 := Real.sin_pi_div_six
  rw [← h, Real.arcsin_sin (by linarith) (by linarith)]

/-- `√(4 - σ²) = 2 * √(1 - σ² / 4)`, the algebra that identifies the chain-rule
derivative with the integrand. -/
theorem sqrt_four_sub_sq {σ : ℝ} (h : σ ^ 2 ≤ 4) :
    Real.sqrt (4 - σ ^ 2) = 2 * Real.sqrt (1 - σ ^ 2 / 4) := by
  have h4 : (0 : ℝ) ≤ 1 - σ ^ 2 / 4 := by linarith
  have : (4 : ℝ) - σ ^ 2 = 4 * (1 - σ ^ 2 / 4) := by ring
  rw [this, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
  rw [show Real.sqrt 4 = 2 by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]]

/-- On `|σ| ≤ 1`, the function `σ ↦ arcsin (σ / 2)` has derivative
`(4 - σ²)^{-1/2}`. -/
theorem hasDerivAt_arcsin_half {σ : ℝ} (h : |σ| ≤ 1) :
    HasDerivAt (fun s : ℝ => Real.arcsin (s / 2)) (1 / Real.sqrt (4 - σ ^ 2)) σ := by
  have habs : |σ / 2| ≤ 1 / 2 := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith
  have hne1 : σ / 2 ≠ 1 := by
    intro hc; rw [hc] at habs; norm_num at habs
  have hne2 : σ / 2 ≠ -1 := by
    intro hc; rw [hc] at habs; norm_num at habs
  have hinner : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) σ := by
    simpa using (hasDerivAt_id σ).div_const 2
  -- `.comp` yields `arcsin ∘ (· / 2)`; Lean will not higher-order-unify that
  -- with the lambda, so rewrite the composition rather than ascribing a type.
  have hchain := (Real.hasDerivAt_arcsin hne2 hne1).comp σ hinner
  rw [Function.comp_def] at hchain
  have hsq : σ ^ 2 ≤ 4 := by nlinarith [abs_le.mp h]
  have hpos : (0 : ℝ) < 1 - (σ / 2) ^ 2 := by nlinarith [abs_le.mp habs]
  have hkey : 1 / Real.sqrt (1 - (σ / 2) ^ 2) * (1 / 2)
      = 1 / Real.sqrt (4 - σ ^ 2) := by
    have hrw : (σ / 2) ^ 2 = σ ^ 2 / 4 := by ring
    rw [hrw, sqrt_four_sub_sq hsq]
    have hs : (0 : ℝ) < Real.sqrt (1 - σ ^ 2 / 4) := by
      apply Real.sqrt_pos.mpr; rw [← hrw]; exact hpos
    field_simp
  rw [hkey] at hchain
  exact hchain

/-- `∫_{-1}^{1} (4 - σ²)^{-1/2} dσ = π / 3`. -/
theorem arcsin_integral :
    (∫ σ in (-1 : ℝ)..1, 1 / Real.sqrt (4 - σ ^ 2)) = π / 3 := by
  have hcont : ContinuousOn (fun σ : ℝ => 1 / Real.sqrt (4 - σ ^ 2))
      (Set.uIcc (-1 : ℝ) 1) := by
    apply ContinuousOn.div continuousOn_const
    · exact (Real.continuous_sqrt.comp (by fun_prop)).continuousOn
    · intro σ hσ
      have hσ' : |σ| ≤ 1 := by
        rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] at hσ
        exact abs_le.mpr ⟨hσ.1, hσ.2⟩
      have : σ ^ 2 ≤ 1 := by nlinarith [abs_le.mp hσ']
      have : (0 : ℝ) < 4 - σ ^ 2 := by linarith
      exact ne_of_gt (Real.sqrt_pos.mpr this)
  have hderiv : ∀ σ ∈ Set.uIcc (-1 : ℝ) 1,
      HasDerivAt (fun s : ℝ => Real.arcsin (s / 2)) (1 / Real.sqrt (4 - σ ^ 2)) σ := by
    intro σ hσ
    rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] at hσ
    exact hasDerivAt_arcsin_half (abs_le.mpr ⟨hσ.1, hσ.2⟩)
  rw [integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  have h1 : Real.arcsin ((1 : ℝ) / 2) = π / 6 := arcsin_half
  have h2 : Real.arcsin ((-1 : ℝ) / 2) = -(π / 6) := by
    rw [show ((-1 : ℝ) / 2) = -(1 / 2) by ring, Real.arcsin_neg, h1]
  rw [h1, h2]
  ring

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# Comparing a step-`6` sum with an integral

The lattice count sums over the odd `b` with `|b| ≤ a`, grouped by `b` modulo
`6`. Each group is an arithmetic progression of step `6`, and the count is
compared with the corresponding integral. Mathlib's
`Mathlib.Analysis.SumIntegralComparisons` provides the step-`1` comparisons; the
step-`6` versions below come from substituting `u ↦ p + 6u`, whose interval
integral rescales by `intervalIntegral.mul_integral_comp_add_mul`:

`6 * ∫ x in 0..n, f (p + 6 * x) = ∫ x in p..p + 6 * n, f x`.

Both one-sided comparisons are recorded, since the error term of the lattice
count needs the sum trapped on both sides. Their difference is a boundary term
`f (p + 6n) - f p`, which for the lattice count is `O(Y/a)` — the source's error.

## Main results

* `PartitionZheng.sum_step_six_le_integral` — monotone: sum below the integral.
* `PartitionZheng.integral_le_sum_step_six` — monotone: integral below the
  shifted sum.
-/


namespace PartitionZheng

open Finset intervalIntegral

/-- Reindexing a step-`6` progression as a step-`1` one preserves monotonicity. -/
private theorem monotoneOn_comp_step_six {f : ℝ → ℝ} {p : ℝ} {n : ℕ}
    (hf : MonotoneOn f (Set.Icc p (p + 6 * (n : ℝ)))) :
    MonotoneOn (fun u : ℝ => f (p + 6 * u)) (Set.Icc 0 (0 + (n : ℝ))) := by
  intro u hu v hv huv
  simp only [zero_add, Set.mem_Icc] at hu hv
  refine hf ?_ ?_ (by linarith)
  · exact Set.mem_Icc.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  · exact Set.mem_Icc.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩

/-- The step-`6` integral rescaling: the integral of `u ↦ f (p + 6u)` over
`[0, n]` is a sixth of the integral of `f` over `[p, p + 6n]`. -/
theorem integral_step_six (f : ℝ → ℝ) (p : ℝ) (n : ℕ) :
    (∫ u in (0 : ℝ)..(n : ℝ), f (p + 6 * u))
      = (1 / 6) * ∫ x in p..(p + 6 * (n : ℝ)), f x := by
  have h := intervalIntegral.mul_integral_comp_add_mul
    (f := f) (a := (0 : ℝ)) (b := (n : ℝ)) (c := (6 : ℝ)) (d := p)
  -- `h : 6 * ∫ u in 0..n, f (p + 6 * u) = ∫ x in p + 6 * 0..p + 6 * n, f x`
  rw [show p + 6 * (0 : ℝ) = p by ring] at h
  linarith [h]

/-- **Monotone, sum below integral.** For `f` monotone on `[p, p + 6n]`, the
step-`6` sum starting at `p` is at most a sixth of the integral. -/
theorem sum_step_six_le_integral {f : ℝ → ℝ} {p : ℝ} {n : ℕ}
    (hf : MonotoneOn f (Set.Icc p (p + 6 * (n : ℝ)))) :
    ∑ i ∈ Finset.range n, f (p + 6 * (i : ℝ))
      ≤ (1 / 6) * ∫ x in p..(p + 6 * (n : ℝ)), f x := by
  have hg := monotoneOn_comp_step_six hf
  have hsum := MonotoneOn.sum_le_integral (x₀ := (0 : ℝ)) (a := n)
    (f := fun u : ℝ => f (p + 6 * u)) hg
  simp only [zero_add] at hsum
  rw [integral_step_six f p n] at hsum
  exact hsum

/-- **Monotone, integral below shifted sum.** For `f` monotone on
`[p, p + 6n]`, a sixth of the integral is at most the step-`6` sum taken at the
right endpoints. Together with `sum_step_six_le_integral` this traps the sum
within the boundary term `f (p + 6n) - f p`. -/
theorem integral_le_sum_step_six {f : ℝ → ℝ} {p : ℝ} {n : ℕ}
    (hf : MonotoneOn f (Set.Icc p (p + 6 * (n : ℝ)))) :
    (1 / 6) * (∫ x in p..(p + 6 * (n : ℝ)), f x)
      ≤ ∑ i ∈ Finset.range n, f (p + 6 * ((i : ℝ) + 1)) := by
  have hg := monotoneOn_comp_step_six hf
  have hint := MonotoneOn.integral_le_sum (x₀ := (0 : ℝ)) (a := n)
    (f := fun u : ℝ => f (p + 6 * u)) hg
  simp only [zero_add] at hint
  rw [integral_step_six f p n] at hint
  have hcast : ∑ x ∈ Finset.range n, f (p + 6 * ((x + 1 : ℕ) : ℝ))
      = ∑ i ∈ Finset.range n, f (p + 6 * ((i : ℝ) + 1)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    norm_num
  rw [hcast] at hint
  exact hint

/-- The interval-length function of the lattice count,
`L⁺(t) = (Y + t² - 4a²)₊ / (4a)`. This is the integrand of `def_F` divided by
`4a`, and `card_c_le` bounds the outer-coefficient count by a multiple of it. -/
private noncomputable def Lplus (Y a t : ℝ) : ℝ :=
  max (Y + t ^ 2 - 4 * a ^ 2) 0 / (4 * a)

/-- `L⁺` is even, so the two halves of `[-a, a]` mirror each other. -/
theorem Lplus_neg (Y a t : ℝ) : Lplus Y a (-t) = Lplus Y a t := by
  unfold Lplus
  rw [neg_pow_two]

/-- `L⁺` is monotone on `[0, ∞)`: `t²` increases there and `max`/division by
`4a > 0` preserve the order. -/
theorem Lplus_monotoneOn {Y a : ℝ} (ha : 0 < a) :
    MonotoneOn (Lplus Y a) (Set.Ici 0) := by
  intro u hu v hv huv
  simp only [Set.mem_Ici] at hu hv
  have ha4 : (0 : ℝ) < 4 * a := by linarith
  have hsq : u ^ 2 ≤ v ^ 2 := by nlinarith
  unfold Lplus
  apply div_le_div_of_nonneg_right ?_ ha4.le
  exact max_le_max (by linarith) (le_refl 0)

/-- `L⁺` is antitone on `(-∞, 0]`, by evenness. -/
theorem Lplus_antitoneOn {Y a : ℝ} (ha : 0 < a) :
    AntitoneOn (Lplus Y a) (Set.Iic 0) := by
  intro u hu v hv huv
  simp only [Set.mem_Iic] at hu hv
  rw [← Lplus_neg Y a u, ← Lplus_neg Y a v]
  exact Lplus_monotoneOn ha (Set.mem_Ici.mpr (by linarith))
    (Set.mem_Ici.mpr (by linarith)) (by linarith)

/-- The boundary term controlling the sum-to-integral error: on `[0, a]` the
total variation of `L⁺` is `L⁺(a) - L⁺(0) ≤ Y / (4a)`.

This is the source's `O(Y/a)`, with the constant exhibited: `1/4`. -/
theorem Lplus_variation_le {Y a : ℝ} (ha : 0 < a) (hY : 0 ≤ Y) :
    Lplus Y a a - Lplus Y a 0 ≤ Y / (4 * a) := by
  have ha4 : (0 : ℝ) < 4 * a := by linarith
  have hnn : 0 ≤ Lplus Y a 0 := by
    unfold Lplus
    exact div_nonneg (le_max_right _ _) ha4.le
  have hub : Lplus Y a a ≤ Y / (4 * a) := by
    unfold Lplus
    apply div_le_div_of_nonneg_right ?_ ha4.le
    apply max_le
    · nlinarith
    · exact hY
  linarith

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# The area integral

The area integral is `∫_0^∞ F_Y(a) da = (π/108) Y^{3/2}`. The argument
substitutes `t = aσ` in the inner integral, then `a = √Y α` in the outer one,
exchanges the order of integration, and evaluates the inner `α`-integral with
`inner_integral` and the resulting `σ`-integral with `arcsin_integral`.

After the two substitutions all the `Y` dependence sits in a prefactor `Y/24`
and the remaining double integral is a pure number — which is what produces the
constant `π/108`.

The improper outer integral is a `MeasureTheory.integral` over `Set.Ioi 0`
rather than an `intervalIntegral`. Since the integrand
`(α, σ) ↦ (1 - (4 - σ²)α²)_+` is nonnegative and vanishes off the bounded set
`(0, 1] × (-1, 1]`, it is integrable on the product and the exchange of order is
`MeasureTheory.integral_integral_swap`; no integrability hypothesis on the
improper integral itself is needed.

`Y ^ (3/2)` is written `Y * sqrt Y`: the two agree for `Y ≥ 0`, and the
hypothesis here is `0 < Y`.

## Main results

* `PartitionZheng.areaF_subst` — `F_Y(a) = (1/24) ∫_{-1}^{1} (Y + a²σ² - 4a²)_+ dσ`.
* `PartitionZheng.areaF_scaled` — `F_Y(√Y α) = (Y/24) ∫_{-1}^{1} (1 - (4-σ²)α²)_+ dσ`.
* `PartitionZheng.integral_areaF` — `∫_0^∞ F_Y(a) da = β Y^{3/2}`.
-/


namespace PartitionZheng

open intervalIntegral MeasureTheory Real

/-- **The inner substitution.** For `a > 0`,

`F_Y(a) = (1/24) ∫_{-1}^{1} (Y + a²σ² - 4a²)_+ dσ`.

Substituting `t = aσ` scales the integral by `a`, which cancels the `1/(24a)`
prefactor of `areaF`. The interval becomes `[-1, 1]`, independent of `a`, so the
region of integration is a product and the order of integration can later be
exchanged. -/
theorem areaF_subst {Y a : ℝ} (ha : 0 < a) :
    areaF Y a = (1 / 24) * ∫ σ in (-1 : ℝ)..1, max (Y + a ^ 2 * σ ^ 2 - 4 * a ^ 2) 0 := by
  have hane : a ≠ 0 := ne_of_gt ha
  -- `a * ∫_{-1}^{1} f (a σ) dσ = ∫_{-a}^{a} f`
  have h := intervalIntegral.mul_integral_comp_add_mul
    (f := fun t : ℝ => max (Y + t ^ 2 - 4 * a ^ 2) 0)
    (a := (-1 : ℝ)) (b := (1 : ℝ)) (c := a) (d := (0 : ℝ))
  rw [show (0 : ℝ) + a * (-1) = -a by ring, show (0 : ℝ) + a * 1 = a by ring] at h
  -- rewrite the integrand of the scaled integral
  have hint : (∫ σ in (-1 : ℝ)..1, max (Y + (0 + a * σ) ^ 2 - 4 * a ^ 2) 0)
      = ∫ σ in (-1 : ℝ)..1, max (Y + a ^ 2 * σ ^ 2 - 4 * a ^ 2) 0 := by
    refine intervalIntegral.integral_congr ?_
    intro σ _
    -- `integral_congr` leaves the integrands un-beta-reduced
    change max (Y + (0 + a * σ) ^ 2 - 4 * a ^ 2) 0
      = max (Y + a ^ 2 * σ ^ 2 - 4 * a ^ 2) 0
    rw [show (0 + a * σ) ^ 2 = a ^ 2 * σ ^ 2 by ring]
  rw [hint] at h
  -- `F_Y(a) = (1/(24a)) * (a * J) = J/24`
  unfold areaF
  rw [← h]
  field_simp

/-- **The outer substitution.** For `Y > 0` and `α > 0`,

`F_Y(√Y α) = (Y/24) ∫_{-1}^{1} (1 - (4 - σ²) α²)₊ dσ`.

With `a = √Y α` we have `a² = Y α²`, so
`Y + a²σ² - 4a² = Y (1 - (4 - σ²) α²)` and the positive part scales out of the
whole expression. The `Y` dependence is now entirely in the prefactor: the
remaining double integral is a pure number, which is what produces the constant
`π/108` after the two evaluations. -/
theorem areaF_scaled {Y α : ℝ} (hY : 0 < Y) (hα : 0 < α) :
    areaF Y (Real.sqrt Y * α)
      = (Y / 24) * ∫ σ in (-1 : ℝ)..1, max (1 - (4 - σ ^ 2) * α ^ 2) 0 := by
  have hsY : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY
  have ha : 0 < Real.sqrt Y * α := mul_pos hsY hα
  rw [areaF_subst ha]
  have hsq : (Real.sqrt Y * α) ^ 2 = Y * α ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hY.le]
  have hint : (∫ σ in (-1 : ℝ)..1,
        max (Y + (Real.sqrt Y * α) ^ 2 * σ ^ 2 - 4 * (Real.sqrt Y * α) ^ 2) 0)
      = ∫ σ in (-1 : ℝ)..1, Y * max (1 - (4 - σ ^ 2) * α ^ 2) 0 := by
    refine intervalIntegral.integral_congr ?_
    intro σ _
    -- `integral_congr` leaves the integrands un-beta-reduced
    change max (Y + (Real.sqrt Y * α) ^ 2 * σ ^ 2 - 4 * (Real.sqrt Y * α) ^ 2) 0
      = Y * max (1 - (4 - σ ^ 2) * α ^ 2) 0
    rw [hsq, show Y + Y * α ^ 2 * σ ^ 2 - 4 * (Y * α ^ 2)
          = Y * (1 - (4 - σ ^ 2) * α ^ 2) by ring]
    -- the positive part scales out, by cases on the sign
    rcases le_or_gt 0 (1 - (4 - σ ^ 2) * α ^ 2) with h | h
    · rw [max_eq_left h, max_eq_left (by positivity :
        (0 : ℝ) ≤ Y * (1 - (4 - σ ^ 2) * α ^ 2))]
    · rw [max_eq_right (le_of_lt h),
        max_eq_right (by nlinarith : Y * (1 - (4 - σ ^ 2) * α ^ 2) ≤ 0)]
      ring
  rw [hint, intervalIntegral.integral_const_mul]
  ring

/-- **The outer substitution, as a set integral.** `areaF_scaled` restated with a
`MeasureTheory` set integral over `Set.Ioc (-1) 1` in place of the interval
integral.

The exchange of integration order needs `MeasureTheory.integral` over
`Set.Ioi 0` in the outer variable and a Tonelli argument for the nonnegative
integrand; `intervalIntegral` — which both substitutions above are stated in —
does not reach it. `intervalIntegral.integral_of_le` is the conversion, valid
because `-1 ≤ 1`. -/
theorem areaF_scaled_setIntegral {Y α : ℝ} (hY : 0 < Y) (hα : 0 < α) :
    areaF Y (Real.sqrt Y * α)
      = (Y / 24) * ∫ σ in Set.Ioc (-1 : ℝ) 1, max (1 - (4 - σ ^ 2) * α ^ 2) 0 := by
  rw [areaF_scaled hY hα,
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]

/- ### The integrand of the double integral

The exchange of integration order needs the integrand
`(α, σ) ↦ (1 - (4 - σ²)α²)₊` to be integrable on the product
`(0, ∞) × (-1, 1]`. It is continuous, and it vanishes off the bounded set
`(0, 1] × (-1, 1]`, which is what makes it integrable despite the unbounded
`α`-range. -/

/-- The integrand of the area integral, as a function of the pair. -/
private noncomputable def posPart (p : ℝ × ℝ) : ℝ :=
  max (1 - (4 - p.2 ^ 2) * p.1 ^ 2) 0

/-- The integrand is continuous on the product: a polynomial composed with
`max`. -/
theorem posPart_continuous : Continuous posPart := by
  unfold posPart
  exact (continuous_const.sub
    ((continuous_const.sub (continuous_snd.pow 2)).mul (continuous_fst.pow 2))).max
      continuous_const

/-- The integrand is nonnegative: it is a positive part. -/
theorem posPart_nonneg (p : ℝ × ℝ) : 0 ≤ posPart p := le_max_right _ _

/-- The integrand vanishes once `α > 1`: with `|σ| ≤ 1` one has `4 - σ² ≥ 3`, so
`(4 - σ²)α² > 3 > 1`. -/
theorem posPart_eq_zero_of_one_lt {p : ℝ × ℝ} (hp : |p.2| ≤ 1) (h1 : 1 < p.1) :
    posPart p = 0 := by
  have hsq : p.2 ^ 2 ≤ 1 := by nlinarith [abs_le.mp hp]
  have hone : (1 : ℝ) < p.1 ^ 2 := by nlinarith
  exact max_eq_right (by nlinarith)

/-- The integrand is integrable on `(0, ∞) × (-1, 1]`.

The set is unbounded, but by `posPart_eq_zero_of_one_lt` the integrand vanishes
outside `(0, 1] × (-1, 1]`, and on that bounded set it is the restriction of a
continuous function to a subset of a compact one. -/
theorem posPart_integrableOn :
    IntegrableOn posPart (Set.Ioi (0 : ℝ) ×ˢ Set.Ioc (-1 : ℝ) 1) (volume.prod volume) := by
  have hsub : Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (-1 : ℝ) 1
      ⊆ Set.Ioi (0 : ℝ) ×ˢ Set.Ioc (-1 : ℝ) 1 :=
    Set.prod_mono Set.Ioc_subset_Ioi_self (subset_refl _)
  rw [← Set.union_sdiff_cancel hsub, integrableOn_union]
  refine ⟨?_, ?_⟩
  · refine (posPart_continuous.continuousOn.integrableOn_compact
      (K := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1)
      (isCompact_Icc.prod isCompact_Icc)).mono_set ?_
    exact Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self
  · refine integrableOn_zero.congr_fun (fun p hp => ?_)
      ((measurableSet_Ioi.prod measurableSet_Ioc).diff
        (measurableSet_Ioc.prod measurableSet_Ioc))
    obtain ⟨⟨h0, hσ⟩, hnot⟩ := hp
    have h1 : 1 < p.1 := by
      by_contra h
      exact hnot ⟨⟨h0, not_lt.mp h⟩, hσ⟩
    exact (posPart_eq_zero_of_one_lt (abs_le.mpr ⟨hσ.1.le, hσ.2⟩) h1).symm

/-- `posPart_integrableOn` phrased for the product of the two restricted
measures, which is the form `MeasureTheory.integral_integral_swap` takes. -/
theorem posPart_integrable :
    Integrable posPart
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioc (-1 : ℝ) 1))) := by
  rw [Measure.prod_restrict]
  exact posPart_integrableOn

/-- **The exchange of integration order.** -/
theorem integral_posPart_swap :
    (∫ α in Set.Ioi (0 : ℝ), ∫ σ in Set.Ioc (-1 : ℝ) 1, posPart (α, σ))
      = ∫ σ in Set.Ioc (-1 : ℝ) 1, ∫ α in Set.Ioi (0 : ℝ), posPart (α, σ) :=
  integral_integral_swap posPart_integrable

/- ### The inner integral after the exchange -/

/-- **The inner `α`-integral.** For `c > 0`,

`∫_0^∞ (1 - c α²)_+ dα = (2/3) c^{-1/2}`.

The integrand is positive exactly on `[0, c^{-1/2})`, so the improper integral
is the integral of the polynomial `1 - c α²` over `(0, c^{-1/2}]`, which
`inner_integral` evaluates — the hypothesis `c A² = 1` holding for
`A = c^{-1/2}`. -/
theorem integral_max_one_sub_const_mul_sq {c : ℝ} (hc : 0 < c) :
    (∫ α in Set.Ioi (0 : ℝ), max (1 - c * α ^ 2) 0) = 2 / 3 * (1 / Real.sqrt c) := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hA : (0 : ℝ) < 1 / Real.sqrt c := by positivity
  have hcA : c * (1 / Real.sqrt c) ^ 2 = 1 := by
    rw [div_pow, one_pow, Real.sq_sqrt hc.le]
    field_simp
  have hzero : ∀ α ∈ Set.Ioi (1 / Real.sqrt c), max (1 - c * α ^ 2) 0 = 0 := by
    intro α hα
    have hαA : 1 / Real.sqrt c < α := hα
    have hsum : (0 : ℝ) < α + 1 / Real.sqrt c := by linarith
    have hkey : 0 < c * ((α - 1 / Real.sqrt c) * (α + 1 / Real.sqrt c)) :=
      mul_pos hc (mul_pos (sub_pos.mpr hαA) hsum)
    exact max_eq_right (by nlinarith)
  rw [← Set.Ioc_union_Ioi_eq_Ioi hA.le,
    integral_union_eq_left_of_forall measurableSet_Ioi hzero]
  have hcongr : (∫ α in Set.Ioc (0 : ℝ) (1 / Real.sqrt c), max (1 - c * α ^ 2) 0)
      = ∫ α in Set.Ioc (0 : ℝ) (1 / Real.sqrt c), (1 - c * α ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioc ?_
    intro α hα
    obtain ⟨hα0, hαA⟩ := hα
    have hsum : (0 : ℝ) < α + 1 / Real.sqrt c := by linarith
    have hkey : 0 ≤ c * ((1 / Real.sqrt c - α) * (α + 1 / Real.sqrt c)) :=
      mul_nonneg hc.le (mul_nonneg (by linarith) hsum.le)
    exact max_eq_left (by nlinarith)
  rw [hcongr, ← intervalIntegral.integral_of_le hA.le, inner_integral hcA]
  ring

/-- **The pure number.** The double integral left by the two substitutions is

`∫_0^∞ ∫_{-1}^{1} (1 - (4 - σ²)α²)_+ dσ dα = (2/3)(π/3)`.

Exchange the order, evaluate the inner `α`-integral by
`integral_max_one_sub_const_mul_sq` with `c = 4 - σ² ≥ 3`, and evaluate the
resulting `σ`-integral of `(4 - σ²)^{-1/2}` by `arcsin_integral`. -/
theorem integral_posPart_double :
    (∫ α in Set.Ioi (0 : ℝ), ∫ σ in Set.Ioc (-1 : ℝ) 1, posPart (α, σ))
      = 2 / 3 * (π / 3) := by
  rw [integral_posPart_swap]
  have hinner : ∀ σ ∈ Set.Ioc (-1 : ℝ) 1,
      (∫ α in Set.Ioi (0 : ℝ), posPart (α, σ)) = 2 / 3 * (1 / Real.sqrt (4 - σ ^ 2)) := by
    intro σ hσ
    have habs : |σ| ≤ 1 := abs_le.mpr ⟨hσ.1.le, hσ.2⟩
    have hsq : σ ^ 2 ≤ 1 := by nlinarith [abs_le.mp habs]
    have hc : (0 : ℝ) < 4 - σ ^ 2 := by linarith
    simpa [posPart] using integral_max_one_sub_const_mul_sq hc
  rw [setIntegral_congr_fun measurableSet_Ioc hinner, MeasureTheory.integral_const_mul,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1), arcsin_integral]

/-- **The area integral.** For `Y > 0`,

`∫_0^∞ F_Y(a) da = β Y^{3/2}`, where `β = π/108`.

The substitution `a = √Y α` turns the improper integral into
`√Y ∫_0^∞ F_Y(√Y α) dα`; `areaF_scaled_setIntegral` replaces the integrand by
`(Y/24) ∫_{-1}^{1} (1 - (4 - σ²)α²)_+ dσ`; and `integral_posPart_double`
evaluates the remaining pure number as `(2/3)(π/3)`. The constant closes exactly
against `beta_eq`, `β = (1/24)(2/3)(π/3)`.

`Y ^ (3/2)` is written `Y * sqrt Y`, which agrees with it for `Y ≥ 0`. -/
theorem integral_areaF {Y : ℝ} (hY : 0 < Y) :
    (∫ a in Set.Ioi (0 : ℝ), areaF Y a) = beta * (Y * Real.sqrt Y) := by
  have hsY : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY
  have hscale : (∫ α in Set.Ioi (0 : ℝ), areaF Y (Real.sqrt Y * α))
      = (Real.sqrt Y)⁻¹ • ∫ a in Set.Ioi (Real.sqrt Y * 0), areaF Y a :=
    integral_comp_mul_left_Ioi (areaF Y) 0 hsY
  rw [mul_zero, smul_eq_mul] at hscale
  have hcongr : ∀ α ∈ Set.Ioi (0 : ℝ), areaF Y (Real.sqrt Y * α)
      = Y / 24 * ∫ σ in Set.Ioc (-1 : ℝ) 1, posPart (α, σ) := by
    intro α hα
    simpa [posPart] using areaF_scaled_setIntegral hY hα
  have hval : (∫ α in Set.Ioi (0 : ℝ), areaF Y (Real.sqrt Y * α))
      = Y / 24 * (2 / 3 * (π / 3)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, MeasureTheory.integral_const_mul,
      integral_posPart_double]
  have hI : (∫ a in Set.Ioi (0 : ℝ), areaF Y a)
      = Real.sqrt Y * (Y / 24 * (2 / 3 * (π / 3))) := by
    rw [← hval, hscale, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hsY), one_mul]
  rw [hI, beta_eq]
  ring

/-- **The integral of `L⁺` against `areaF`.** For `a > 0`,
`∫_{-a}^{a} L⁺(t) dt = 6 · F_Y(a)`.

`L⁺(t) = (Y + t² - 4a²)₊ / (4a)` and `F_Y(a) = (1/(24a)) ∫_{-a}^{a} (…)₊`, so the
two differ exactly by the factor `24a / 4a = 6`. -/
theorem integral_Lplus_eq {Y a : ℝ} (ha : 0 < a) :
    (∫ t in (-a)..a, Lplus Y a t) = 6 * areaF Y a := by
  have hane : a ≠ 0 := ne_of_gt ha
  unfold Lplus areaF
  rw [intervalIntegral.integral_div]
  field_simp
  ring

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# The weighted sum against the area function

The lattice count produces the weighted sum `∑_{1 ≤ a ≤ √(Y/3)} (w a / 6) F_Y(a)`,
and the class-number average needs it bounded by `(π/108) Y^{3/2} + C Y log Y`.

The mean of `w / 6` over a period of six is `1`, so the weighted sum ought to be
comparable with the unweighted one. Here the comparison is an inequality with no
error term at all, for a reason particular to how the six values sit in the
period: they are `1/2, 1, 1, 1, 1/2, 2` at `a ≡ 1, 2, 3, 4, 5, 0 [MOD 6]`, so on
a block `{6m+1, …, 6m+6}` the one coefficient exceeding `1` sits at the *last*
index, where the nonincreasing `F_Y` is smallest, and the two deficits of `1/2`
sit earlier, where it is larger. From `F_Y(6m+6) ≤ F_Y(6m+1)` and
`F_Y(6m+6) ≤ F_Y(6m+5)` one gets
`F_Y(6m+6) ≤ F_Y(6m+1)/2 + F_Y(6m+5)/2`, which says exactly that the weighted
block does not exceed the unweighted block. The residues `1, …, 5` of an
incomplete final block carry coefficients at most `1` and so need no
compensation. Hence the weight may be dropped outright, and since `F_Y` is
nonincreasing the remaining sum is at most `∫_0^∞ F_Y(a) da`.

`Y ^ (3/2)` is written `Y * sqrt Y`, as elsewhere in this development.

## Main results

* `PartitionZheng.areaF_antitoneOn` — `F_Y` is nonincreasing on `(0, ∞)`.
* `PartitionZheng.sum_areaF_le_integral` — `∑_{1 ≤ a ≤ N} F_Y(a) ≤ ∫_0^∞ F_Y(a) da`.
* `PartitionZheng.weighted_areaF_sum_le` — the weighted sum is at most
  `(π/108) Y^{3/2}`.
* `PartitionZheng.exists_weighted_areaF_sum_le` — the bound in the form the
  source states it, with an error term `C Y log Y`.
-/


namespace PartitionZheng

open MeasureTheory

/- ### The area function is nonnegative and nonincreasing -/

/-- `F_Y` is nonnegative for `a > 0`, being a positive multiple of the integral of
a positive part. -/
theorem areaF_nonneg (Y : ℝ) {a : ℝ} (ha : 0 < a) : 0 ≤ areaF Y a := by
  have h : (0 : ℝ) ≤ ∫ t in (-a)..a, max (Y + t ^ 2 - 4 * a ^ 2) 0 :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ => le_max_right _ _
  unfold areaF
  exact mul_nonneg (div_nonneg zero_le_one (by linarith)) h

/-- `F_Y` is nonincreasing on `(0, ∞)`. In the shape `areaF_subst` gives, the
integrand `(Y - a²(4 - σ²))₊` is nonincreasing in `a` pointwise, because
`4 - σ² ≥ 3 > 0` throughout the range of integration. -/
theorem areaF_antitoneOn (Y : ℝ) : AntitoneOn (areaF Y) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have hcont : ∀ c : ℝ, IntervalIntegrable
      (fun σ : ℝ => max (Y + c ^ 2 * σ ^ 2 - 4 * c ^ 2) 0) volume (-1) 1 := fun c =>
    (((continuous_const.add (continuous_const.mul (continuous_pow 2))).sub
      continuous_const).max continuous_const).intervalIntegrable _ _
  have key : (∫ σ in (-1 : ℝ)..1, max (Y + b ^ 2 * σ ^ 2 - 4 * b ^ 2) 0)
      ≤ ∫ σ in (-1 : ℝ)..1, max (Y + a ^ 2 * σ ^ 2 - 4 * a ^ 2) 0 := by
    refine intervalIntegral.integral_mono_on (by norm_num) (hcont b) (hcont a) fun σ hσ => ?_
    obtain ⟨hσ1, hσ2⟩ := hσ
    have hsq : σ ^ 2 ≤ 1 := by nlinarith
    have hab2 : a ^ 2 ≤ b ^ 2 := by nlinarith
    have hmul : a ^ 2 * (4 - σ ^ 2) ≤ b ^ 2 * (4 - σ ^ 2) :=
      mul_le_mul_of_nonneg_right hab2 (by linarith)
    exact max_le_max (by linarith) le_rfl
  rw [areaF_subst ha, areaF_subst hb]
  linarith

/- ### The weight as a real coefficient -/

/-- `weight` reads its argument modulo `6`, so on a natural number it is
determined by the remainder. -/
private theorem weight_natCast_mod (a : ℕ) : weight (a : ℤ) = weight ((a % 6 : ℕ) : ℤ) :=
  weight_eq_of_cast (by simp only [Int.cast_natCast, ZMod.natCast_mod])

/-- The coefficient `w a / 6` depends only on the remainder of `a` modulo `6`. -/
private theorem weight_div_six_of_mod {a r : ℕ} (h : a % 6 = r) :
    (weight (a : ℤ) : ℝ) / 6 = (weight (r : ℤ) : ℝ) / 6 := by
  rw [weight_natCast_mod, h]

/-- Away from `a ≡ 0 [MOD 6]` the coefficient `w a / 6` is at most `1`: the five
remaining values of `w` are `3, 6, 6, 6, 3`. -/
private theorem weight_div_six_le_one {a : ℕ} (h : a % 6 ≠ 0) :
    (weight (a : ℤ) : ℝ) / 6 ≤ 1 := by
  obtain ⟨-, w1, w2, w3, w4, w5⟩ := weight_values
  have h6 : a % 6 = 1 ∨ a % 6 = 2 ∨ a % 6 = 3 ∨ a % 6 = 4 ∨ a % 6 = 5 := by omega
  rw [weight_natCast_mod]
  rcases h6 with h' | h' | h' | h' | h' <;> rw [h'] <;> norm_num [w1, w2, w3, w4, w5]

/- ### Dropping the weight

The coefficient `w a / 6` can be replaced by `1` throughout, at no cost, for any
nonnegative nonincreasing `f` in place of `F_Y`. -/

section Dropping

variable {f : ℕ → ℝ}

/-- A sum over `Ioc p (p + n)` reindexed as a sum over `range n`. -/
private theorem sum_Ioc_eq_sum_range (g : ℕ → ℝ) (p n : ℕ) :
    ∑ a ∈ Finset.Ioc p (p + n), g a = ∑ j ∈ Finset.range n, g (p + (j + 1)) := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hstep : p + (k + 1) = p + k + 1 := rfl
      rw [hstep, Finset.sum_Ioc_succ_top (Nat.le_add_right p k), ih, Finset.sum_range_succ]
      rfl

/-- **One complete block of six.** The coefficients on `{6m+1, …, 6m+6}` are
`1/2, 1, 1, 1, 1/2, 2`, and the only one exceeding `1` sits at the last index,
where a nonincreasing `f` is smallest. Since `f (6m+6) ≤ f (6m+1)` and
`f (6m+6) ≤ f (6m+5)`, the excess `f (6m+6)` is covered by the two deficits
`f (6m+1)/2` and `f (6m+5)/2`. -/
private theorem weighted_block_le (hanti : ∀ i j : ℕ, 1 ≤ i → i ≤ j → f j ≤ f i) (m : ℕ) :
    ∑ a ∈ Finset.Ioc (6 * m) (6 * m + 6), (weight (a : ℤ) : ℝ) / 6 * f a
      ≤ ∑ a ∈ Finset.Ioc (6 * m) (6 * m + 6), f a := by
  obtain ⟨w0, w1, w2, w3, w4, w5⟩ := weight_values
  have c1 : (weight ((6 * m + 1 : ℕ) : ℤ) : ℝ) / 6 = 1 / 2 := by
    rw [weight_div_six_of_mod (show (6 * m + 1) % 6 = 1 from by omega)]; norm_num [w1]
  have c2 : (weight ((6 * m + 2 : ℕ) : ℤ) : ℝ) / 6 = 1 := by
    rw [weight_div_six_of_mod (show (6 * m + 2) % 6 = 2 from by omega)]; norm_num [w2]
  have c3 : (weight ((6 * m + 3 : ℕ) : ℤ) : ℝ) / 6 = 1 := by
    rw [weight_div_six_of_mod (show (6 * m + 3) % 6 = 3 from by omega)]; norm_num [w3]
  have c4 : (weight ((6 * m + 4 : ℕ) : ℤ) : ℝ) / 6 = 1 := by
    rw [weight_div_six_of_mod (show (6 * m + 4) % 6 = 4 from by omega)]; norm_num [w4]
  have c5 : (weight ((6 * m + 5 : ℕ) : ℤ) : ℝ) / 6 = 1 / 2 := by
    rw [weight_div_six_of_mod (show (6 * m + 5) % 6 = 5 from by omega)]; norm_num [w5]
  have c6 : (weight ((6 * m + 6 : ℕ) : ℤ) : ℝ) / 6 = 2 := by
    rw [weight_div_six_of_mod (show (6 * m + 6) % 6 = 0 from by omega)]; norm_num [w0]
  have h1 : f (6 * m + 6) ≤ f (6 * m + 1) := hanti _ _ (by omega) (by omega)
  have h5 : f (6 * m + 6) ≤ f (6 * m + 5) := hanti _ _ (by omega) (by omega)
  rw [sum_Ioc_eq_sum_range, sum_Ioc_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num only
  rw [c1, c2, c3, c4, c5, c6]
  linarith

/-- The weight can be dropped over a range consisting of complete blocks of
six. -/
private theorem weighted_sum_blocks_le (hanti : ∀ i j : ℕ, 1 ≤ i → i ≤ j → f j ≤ f i) (q : ℕ) :
    ∑ a ∈ Finset.Ioc 0 (6 * q), (weight (a : ℤ) : ℝ) / 6 * f a
      ≤ ∑ a ∈ Finset.Ioc 0 (6 * q), f a := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hq : 6 * (q + 1) = 6 * q + 6 := by ring
      rw [hq, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le (6 * q)) (Nat.le_add_right (6 * q) 6),
        ← Finset.sum_Ioc_consecutive _ (Nat.zero_le (6 * q)) (Nat.le_add_right (6 * q) 6)]
      exact add_le_add ih (weighted_block_le hanti q)

/-- **The weight drops out.** For nonnegative nonincreasing `f`, the weighted sum
over `1 ≤ a ≤ N` is at most the unweighted one: the complete blocks of six are
handled by `weighted_block_le`, and the at most five remaining indices are
congruent to `1, …, 5` modulo `6`, where the coefficient is already at most
`1`. -/
private theorem weighted_sum_le_sum (hnn : ∀ a : ℕ, 1 ≤ a → 0 ≤ f a)
    (hanti : ∀ i j : ℕ, 1 ≤ i → i ≤ j → f j ≤ f i) (N : ℕ) :
    ∑ a ∈ Finset.Ioc 0 N, (weight (a : ℤ) : ℝ) / 6 * f a ≤ ∑ a ∈ Finset.Ioc 0 N, f a := by
  obtain ⟨q, r, hr, hN⟩ : ∃ q r, r < 6 ∧ N = 6 * q + r := ⟨N / 6, N % 6, by omega, by omega⟩
  subst hN
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le (6 * q)) (Nat.le_add_right (6 * q) r),
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le (6 * q)) (Nat.le_add_right (6 * q) r)]
  refine add_le_add (weighted_sum_blocks_le hanti q) (Finset.sum_le_sum fun a ha => ?_)
  simp only [Finset.mem_Ioc] at ha
  calc (weight (a : ℤ) : ℝ) / 6 * f a
      ≤ 1 * f a :=
        mul_le_mul_of_nonneg_right (weight_div_six_le_one (by omega)) (hnn a (by omega))
    _ = f a := one_mul _

end Dropping

/- ### From the sum to the integral -/

/-- `lem_F_integral` forces `F_Y` to be integrable on `(0, ∞)`: were it not, the
integral would be `0` by convention, whereas the value the lemma assigns it is
positive. -/
theorem integrableOn_areaF {Y : ℝ} (hY : 0 < Y)
    (hFY : (∫ a in Set.Ioi (0 : ℝ), areaF Y a) = Real.pi / 108 * (Y * Real.sqrt Y)) :
    IntegrableOn (areaF Y) (Set.Ioi 0) := by
  by_contra hcon
  rw [MeasureTheory.integral_undef hcon] at hFY
  have hs : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY
  have hpos : 0 < Real.pi / 108 * (Y * Real.sqrt Y) :=
    mul_pos (by positivity) (mul_pos hY hs)
  linarith

/-- **The sum is below the integral.** Each term `F_Y(k+1)` is at most the
integral of `F_Y` over `(k, k+1]`, since `F_Y` is nonincreasing there and the
interval has length `1`; the unit intervals for `1 ≤ k + 1 ≤ N` tile `(0, N]`,
and the remaining part of `(0, ∞)` contributes nonnegatively. -/
theorem sum_areaF_le_integral {Y : ℝ} (hint : IntegrableOn (areaF Y) (Set.Ioi 0)) (N : ℕ) :
    ∑ a ∈ Finset.Ioc 0 N, areaF Y (a : ℝ) ≤ ∫ a in Set.Ioi (0 : ℝ), areaF Y a := by
  have hsub : ∀ k : ℕ, Set.Ioc (k : ℝ) ((k : ℝ) + 1) ⊆ Set.Ioi (0 : ℝ) := fun k x hx =>
    lt_of_le_of_lt (Nat.cast_nonneg k) hx.1
  have hii : ∀ k : ℕ, IntervalIntegrable (areaF Y) volume (k : ℝ) ((k : ℝ) + 1) := by
    intro k
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact hint.mono_set (hsub k)
  have hterm : ∀ k : ℕ, areaF Y ((k : ℝ) + 1) ≤ ∫ x in (k : ℝ)..((k : ℝ) + 1), areaF Y x := by
    intro k
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hle : ∀ x ∈ Set.Ioc (k : ℝ) ((k : ℝ) + 1), areaF Y ((k : ℝ) + 1) ≤ areaF Y x :=
      fun x hx => areaF_antitoneOn Y (hsub k hx) (Set.mem_Ioi.mpr hpos) hx.2
    have hfin : volume (Set.Ioc (k : ℝ) ((k : ℝ) + 1)) ≠ ⊤ := by
      rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    have h := setIntegral_ge_of_const_le_real measurableSet_Ioc hfin hle
      (hint.mono_set (hsub k))
    have hvol : (volume : Measure ℝ).real (Set.Ioc (k : ℝ) ((k : ℝ) + 1)) = 1 := by
      simp [Measure.real, Real.volume_Ioc]
    rw [hvol, mul_one] at h
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact h
  have htel : ∑ k ∈ Finset.range N, (∫ x in (k : ℝ)..((k : ℝ) + 1), areaF Y x)
      = ∫ x in (0 : ℝ)..(N : ℝ), areaF Y x := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (f := areaF Y) (μ := volume)
      (a := fun k : ℕ => (k : ℝ)) (n := N) fun k _ => by simpa using hii k
    simpa using h
  have hmono : (∫ x in Set.Ioc (0 : ℝ) (N : ℝ), areaF Y x)
      ≤ ∫ x in Set.Ioi (0 : ℝ), areaF Y x := by
    refine setIntegral_mono_set hint ?_ Set.Ioc_subset_Ioi_self.eventuallyLE
    exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun x hx => areaF_nonneg Y hx)
  calc ∑ a ∈ Finset.Ioc 0 N, areaF Y (a : ℝ)
      = ∑ k ∈ Finset.range N, areaF Y ((k : ℝ) + 1) := by
        simpa using sum_Ioc_eq_sum_range (fun a => areaF Y (a : ℝ)) 0 N
    _ ≤ ∑ k ∈ Finset.range N, ∫ x in (k : ℝ)..((k : ℝ) + 1), areaF Y x :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = ∫ x in (0 : ℝ)..(N : ℝ), areaF Y x := htel
    _ = ∫ x in Set.Ioc (0 : ℝ) (N : ℝ), areaF Y x :=
        intervalIntegral.integral_of_le (Nat.cast_nonneg N)
    _ ≤ ∫ x in Set.Ioi (0 : ℝ), areaF Y x := hmono

/- ### The weighted sum -/

/-- **The weighted sum, with no error term.** For every `N`,
`∑_{1 ≤ a ≤ N} (w a / 6) F_Y(a) ≤ (π/108) Y^{3/2}`.

The hypothesis `hFY` is `lem_F_integral` at `Y`. -/
theorem weighted_areaF_sum_le {Y : ℝ} (hY : 0 < Y)
    (hFY : (∫ a in Set.Ioi (0 : ℝ), areaF Y a) = Real.pi / 108 * (Y * Real.sqrt Y)) (N : ℕ) :
    ∑ a ∈ Finset.Icc 1 N, (weight (a : ℤ) : ℝ) / 6 * areaF Y (a : ℝ)
      ≤ Real.pi / 108 * (Y * Real.sqrt Y) := by
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hnn : ∀ a : ℕ, 1 ≤ a → 0 ≤ areaF Y (a : ℝ) := fun a ha =>
    areaF_nonneg Y (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one ha)
  have hanti : ∀ i j : ℕ, 1 ≤ i → i ≤ j → areaF Y (j : ℝ) ≤ areaF Y (i : ℝ) := by
    intro i j hi hij
    have hi' : (0 : ℝ) < (i : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hi
    have hj' : (0 : ℝ) < (j : ℝ) := lt_of_lt_of_le hi' (by exact_mod_cast hij)
    exact areaF_antitoneOn Y (Set.mem_Ioi.mpr hi') (Set.mem_Ioi.mpr hj') (by exact_mod_cast hij)
  rw [hIcc]
  calc ∑ a ∈ Finset.Ioc 0 N, (weight (a : ℤ) : ℝ) / 6 * areaF Y (a : ℝ)
      ≤ ∑ a ∈ Finset.Ioc 0 N, areaF Y (a : ℝ) := weighted_sum_le_sum hnn hanti N
    _ ≤ ∫ a in Set.Ioi (0 : ℝ), areaF Y a := sum_areaF_le_integral (integrableOn_areaF hY hFY) N
    _ = Real.pi / 108 * (Y * Real.sqrt Y) := hFY

/-- **`lem_partial_summation`.** There is a constant `C > 0` such that for every
real `Y ≥ 2`,

`∑_{1 ≤ a ≤ √(Y/3)} (w a / 6) F_Y(a) ≤ (π/108) Y^{3/2} + C Y log Y`.

The hypothesis `hF` is `lem_F_integral`, `∫_0^∞ F_Y(a) da = (π/108) Y^{3/2}` for
every `Y > 0`; it will be discharged once that lemma is available.

`weighted_areaF_sum_le` gives the bound without the error term, so any positive
`C` will do here. -/
theorem exists_weighted_areaF_sum_le
    (hF : ∀ Y : ℝ, 0 < Y →
      (∫ a in Set.Ioi (0 : ℝ), areaF Y a) = Real.pi / 108 * (Y * Real.sqrt Y)) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 2 ≤ Y →
      ∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊, (weight (a : ℤ) : ℝ) / 6 * areaF Y (a : ℝ)
        ≤ Real.pi / 108 * (Y * Real.sqrt Y) + C * (Y * Real.log Y) := by
  refine ⟨1, one_pos, fun Y hY2 => ?_⟩
  have hY : 0 < Y := by linarith
  have hlog : 0 < Y * Real.log Y := mul_pos hY (Real.log_pos (by linarith))
  have h := weighted_areaF_sum_le hY (hF Y hY) ⌊Real.sqrt (Y / 3)⌋₊
  linarith

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# Congruences modulo 24

The discriminant condition `4ac - b^2 ≡ 23 [ZMOD 24]` is turned into conditions
on `b` and on `a * c` modulo `6`. Everything here is elementary: squares of
integers coprime to `6` are `1` modulo `24`, and squares of odd multiples of `3`
are `9`.

The coprimality hypotheses are written `¬ (2 ∣ d)` and `¬ (3 ∣ d)` rather than
`Int.gcd d 6 = 1`. The two are equivalent, and the unfolded form is what every
consumer here has to hand.

## Main results

* `PartitionZheng.sq_emod_24` — `d` coprime to `6` gives `d ^ 2 % 24 = 1`.
* `PartitionZheng.sq_emod_24_of_three_dvd` — `b` odd with `3 ∣ b` gives
  `b ^ 2 % 24 = 9`.
* `PartitionZheng.odd_of_disc` — the discriminant congruence forces `b` odd.
* `PartitionZheng.coprime_six_of_sq_dvd` — a square divisor of an integer
  congruent to `23` modulo `24` is coprime to `6`.
-/


namespace PartitionZheng

/-- Reduce a claim about `d ^ 2 % 24` to the same claim about the residue
`d % 24`, which `interval_cases` can then check outright. -/
private lemma sq_emod_24_eq {d v : ℤ} (h : (d % 24) ^ 2 % 24 = v) :
    d ^ 2 % 24 = v := by
  have hmod : ((d % 24) ^ 2) ≡ d ^ 2 [ZMOD 24] := (Int.mod_modEq d 24).pow 2
  calc d ^ 2 % 24 = (d % 24) ^ 2 % 24 := hmod.symm
    _ = v := h

/-- The 24 residues, checked one at a time: an odd residue not divisible by `3`
squares to `1`. -/
private lemma residue_sq_one {r : ℤ} (h0 : 0 ≤ r) (h1 : r < 24)
    (h2 : r % 2 = 1) (h3 : r % 3 ≠ 0) : r ^ 2 % 24 = 1 := by
  interval_cases r <;> simp_all

/-- The 24 residues again: an odd residue divisible by `3` squares to `9`. -/
private lemma residue_sq_nine {r : ℤ} (h0 : 0 ≤ r) (h1 : r < 24)
    (h2 : r % 2 = 1) (h3 : r % 3 = 0) : r ^ 2 % 24 = 9 := by
  interval_cases r <;> simp_all

/-- `d % 24` has the same parity and the same residue modulo `3` as `d`, since
`2` and `3` both divide `24`. -/
private lemma emod_24_bounds (d : ℤ) :
    0 ≤ d % 24 ∧ d % 24 < 24 ∧ d % 24 % 2 = d % 2 ∧ d % 24 % 3 = d % 3 :=
  ⟨Int.emod_nonneg d (by norm_num), Int.emod_lt_of_pos d (by norm_num),
    Int.emod_emod_of_dvd d (by norm_num), Int.emod_emod_of_dvd d (by norm_num)⟩

/-- Squares of integers coprime to `6` are `1` modulo `24`. -/
theorem sq_emod_24 {d : ℤ} (h2 : ¬ (2 ∣ d)) (h3 : ¬ (3 ∣ d)) : d ^ 2 % 24 = 1 := by
  obtain ⟨hr0, hr1, e2, e3⟩ := emod_24_bounds d
  have h2' : d % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one d with h | h
    · exact absurd (Int.dvd_of_emod_eq_zero h) h2
    · exact h
  have h3' : d % 3 ≠ 0 := fun h => h3 (Int.dvd_of_emod_eq_zero h)
  exact sq_emod_24_eq (residue_sq_one hr0 hr1 (by rw [e2]; exact h2') (by rw [e3]; exact h3'))

/-- Squares of odd multiples of `3` are `9` modulo `24`. Together with
`sq_emod_24` this is the two-case computation the discriminant congruence needs. -/
theorem sq_emod_24_of_three_dvd {b : ℤ} (hodd : Odd b) (h3 : 3 ∣ b) :
    b ^ 2 % 24 = 9 := by
  obtain ⟨hr0, hr1, e2, e3⟩ := emod_24_bounds b
  have h2' : b % 2 = 1 := Int.odd_iff.mp hodd
  have h3' : b % 3 = 0 := Int.emod_eq_zero_of_dvd h3
  exact sq_emod_24_eq (residue_sq_nine hr0 hr1 (by rw [e2]; exact h2') (by rw [e3]; exact h3'))

/-- The discriminant congruence forces the middle coefficient to be odd:
modulo `2` it reads `-b ^ 2 ≡ 1`. -/
theorem odd_of_disc {a b c : ℤ} (h : (4 * a * c - b ^ 2) % 24 = 23) : Odd b := by
  rcases Int.even_or_odd b with he | ho
  · obtain ⟨k, hk⟩ := he
    obtain ⟨t, ht⟩ : (2 : ℤ) ∣ (4 * a * c - b ^ 2) :=
      ⟨2 * a * c - 2 * k ^ 2, by subst hk; ring⟩
    rw [ht] at h
    omega
  · exact ho

/-- A square divisor of an integer congruent to `23` modulo `24` is coprime to
`6`: such an integer is odd and is `2` modulo `3`. -/
theorem coprime_six_of_sq_dvd {N d : ℤ} (hN : N % 24 = 23) (hdvd : d ^ 2 ∣ N) :
    ¬ (2 ∣ d) ∧ ¬ (3 ∣ d) := by
  have hd : d ∣ N := dvd_trans (dvd_pow_self d (by norm_num)) hdvd
  refine ⟨fun h2 => ?_, fun h3 => ?_⟩
  · obtain ⟨t, ht⟩ := dvd_trans h2 hd
    omega
  · obtain ⟨t, ht⟩ := dvd_trans h3 hd
    omega

/-- With `b` coprime to `3`, the discriminant congruence says exactly that
`6 ∣ a * c`. This is the first case of the two-case reduction. -/
theorem disc_emod_iff_of_not_three_dvd {a b c : ℤ} (hb : Odd b) (h3 : ¬ (3 ∣ b)) :
    (4 * (a * c) - b ^ 2) % 24 = 23 ↔ (a * c) % 6 = 0 := by
  have h2 : ¬ (2 ∣ b) := by
    intro h
    have hodd := Int.odd_iff.mp hb
    omega
  have hb2 : b ^ 2 % 24 = 1 := sq_emod_24 h2 h3
  omega

/-- With `3 ∣ b`, the discriminant congruence says exactly that
`a * c ≡ 2 [ZMOD 6]`. This is the second case of the two-case reduction. -/
theorem disc_emod_iff_of_three_dvd {a b c : ℤ} (hb : Odd b) (h3 : 3 ∣ b) :
    (4 * (a * c) - b ^ 2) % 24 = 23 ↔ (a * c) % 6 = 2 := by
  have hb2 : b ^ 2 % 24 = 9 := sq_emod_24_of_three_dvd hb h3
  omega

/-- **Stripping the square factor from the congruence.** For `d` coprime to `6`,
`d² r ≡ 23 [ZMOD 24]` exactly when `r ≡ 23 [ZMOD 24]`, since `d² ≡ 1 [ZMOD 24]`.

This is what lets the count of admissible discriminants replace the condition
`d² r ≡ 23 (24)` on `N = d² r` by a condition on `r` alone, so that the inner
count becomes a residue count in a fixed class and
`card_residue_class_Icc_mod` applies at `q = 24`. -/
theorem dsq_mul_emod_24 {d r : ℤ} (h2 : ¬ (2 ∣ d)) (h3 : ¬ (3 ∣ d)) :
    (d ^ 2 * r) % 24 = 23 ↔ r % 24 = 23 := by
  have hd : d ^ 2 % 24 = 1 := sq_emod_24 h2 h3
  rw [Int.mul_emod, hd, one_mul, Int.emod_emod_of_dvd r (dvd_refl 24)]

/- ### Natural-number forms

The count of admissible discriminants works over `ℕ` — `admissible` is a
`Finset ℕ` and the fibre map is `r ↦ d² * r` on naturals — so the two
congruence facts are needed there too. They are cast from the `ℤ` versions
rather than reproved. -/

/-- `sq_emod_24` over `ℕ`. -/
theorem sq_emod_24_nat {d : ℕ} (h2 : ¬ (2 ∣ d)) (h3 : ¬ (3 ∣ d)) :
    d ^ 2 % 24 = 1 := by
  have h2' : ¬ ((2 : ℤ) ∣ (d : ℤ)) := fun h => h2 (by exact_mod_cast h)
  have h3' : ¬ ((3 : ℤ) ∣ (d : ℤ)) := fun h => h3 (by exact_mod_cast h)
  have hz : ((d : ℤ)) ^ 2 % 24 = 1 := sq_emod_24 h2' h3'
  have hcast : ((d ^ 2 % 24 : ℕ) : ℤ) = 1 := by push_cast; exact hz
  exact_mod_cast hcast

/-- `dsq_mul_emod_24` over `ℕ`: for `d` coprime to `6`, `d² r ≡ 23 [MOD 24]`
exactly when `r ≡ 23 [MOD 24]`. This is what lets the fibre over `d` be counted
as a residue class in `r` alone. -/
theorem dsq_mul_emod_24_nat {d r : ℕ} (h2 : ¬ (2 ∣ d)) (h3 : ¬ (3 ∣ d)) :
    (d ^ 2 * r) % 24 = 23 ↔ r % 24 = 23 := by
  have hd : d ^ 2 % 24 = 1 := sq_emod_24_nat h2 h3
  rw [Nat.mul_mod, hd, one_mul, Nat.mod_mod]

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# Counting integers of an interval in prescribed residue classes

The lattice count fixes `a` and `b` and confines the outer coefficient `c` to an
interval, intersected with those residue classes modulo `6` that the
discriminant congruence admits. This file supplies the counting step: an
interval with integer endpoints `lo ≤ hi` meets a single class modulo `q` in at
most `(hi - lo) / q + 1` integers, hence a union of `k` classes in at most
`k * (hi - lo) / q + k`.

The count is proved for an arbitrary modulus `q > 0`, since `lem_Dset_card`
needs `q = 24` while the lattice count needs `q = 6`; the mod-`6` statements are
wrappers.

The proof is an explicit injection. On a fixed class the map `c ↦ (c - lo) / q`
is injective, because two members of the class differ by a multiple of `q` and
so share a remainder; and it lands in `Finset.Icc 0 ((hi - lo) / q)`.

The hypothesis `lo ≤ hi` is necessary, not decorative: for `hi < lo` the count
is `0` but `(hi - lo) / q + 1` is negative, so the bound fails. Callers whose
interval may be empty case-split before applying these.

Fixing `a` and `b`, `card_c_le` then assembles the two constraints into a bound
on the number of admissible outer coefficients, in terms of the positive part
`(Y + b² - 4a²)_+` that `def_F` integrates.

## Main definitions

* `PartitionZheng.cClasses` — the classes modulo `6` admitted for `c`.

## Main results

* `PartitionZheng.card_residue_class_Icc_mod` — the single-class count, any `q`.
* `PartitionZheng.card_residue_class_Icc` — its `q = 6` case.
* `PartitionZheng.card_residue_classes_Icc` — the `k`-class count.
* `PartitionZheng.card_c_le` — the count of outer coefficients for fixed `a, b`.
-/


namespace PartitionZheng

open Finset

/-- On a fixed residue class modulo `q`, the map `c ↦ (c - lo) / q` is
injective: two members of the class share a remainder, so equal quotients force
equality. `omega` cannot close this directly, because a variable modulus makes
`q * ((c - lo) / q)` a product of two unknowns; the values are rebuilt from
quotient and remainder first. -/
private theorem ediv_injOn_class_mod {q : ℕ} {lo : ℤ} {r : ZMod q} :
    Set.InjOn (fun c : ℤ => (c - lo) / (q : ℤ)) {c : ℤ | (c : ZMod q) = r} := by
  intro c hc c' hc' h
  simp only [Set.mem_ofPred_eq] at hc hc'
  have hmod : c % (q : ℤ) = c' % (q : ℤ) := by
    have hcc : ((c : ZMod q)) = ((c' : ZMod q)) := by rw [hc, hc']
    exact (ZMod.intCast_eq_intCast_iff' c c' q).mp hcc
  have hsub : (c - lo) % (q : ℤ) = (c' - lo) % (q : ℤ) := Int.ModEq.sub hmod rfl
  have hc1 : (q : ℤ) * ((c - lo) / (q : ℤ)) + (c - lo) % (q : ℤ) = c - lo :=
    Int.mul_ediv_add_emod _ _
  have hc2 : (q : ℤ) * ((c' - lo) / (q : ℤ)) + (c' - lo) % (q : ℤ) = c' - lo :=
    Int.mul_ediv_add_emod _ _
  simp only at h
  -- rebuild each value from its quotient and remainder, which now agree
  have heq : c - lo = c' - lo := by rw [← hc1, ← hc2, h, hsub]
  omega

/-- Integer division by `q > 0` is bounded by real division. -/
private theorem ediv_le_real {q : ℕ} (hq : 0 < q) (n : ℤ) :
    ((n / (q : ℤ) : ℤ) : ℝ) ≤ (n : ℝ) / (q : ℝ) := by
  have hq0 : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqr : (q : ℤ) * (n / (q : ℤ)) + n % (q : ℤ) = n := Int.mul_ediv_add_emod _ _
  have hnn : 0 ≤ n % (q : ℤ) := Int.emod_nonneg n (by omega)
  have hz : (q : ℤ) * (n / (q : ℤ)) ≤ n := by omega
  have hz' : (((q : ℤ) * (n / (q : ℤ)) : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := by exact_mod_cast hz
  push_cast at hz'
  rw [le_div_iff₀ hqR]
  linarith

/-- **Single class, general modulus.** For `lo ≤ hi` and `q > 0`, the integers
of `Finset.Icc lo hi` lying in one residue class modulo `q` number at most
`(hi - lo) / q + 1`.

`lem_Dset_card` needs this at `q = 24`; the lattice count needs `q = 6`. -/
theorem card_residue_class_Icc_mod {q : ℕ} (hq : 0 < q) {lo hi : ℤ} (hle : lo ≤ hi)
    (r : ZMod q) :
    ((((Finset.Icc lo hi).filter fun c : ℤ => (c : ZMod q) = r)).card : ℝ)
      ≤ ((hi : ℝ) - (lo : ℝ)) / (q : ℝ) + 1 := by
  classical
  have hq0 : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hqnn : (0 : ℤ) ≤ (hi - lo) / (q : ℤ) := Int.ediv_nonneg (by omega) (by omega)
  have hkey : (((Finset.Icc lo hi).filter fun c : ℤ => (c : ZMod q) = r)).card
      ≤ (Finset.Icc (0 : ℤ) ((hi - lo) / (q : ℤ))).card := by
    refine Finset.card_le_card_of_injOn (fun c => (c - lo) / (q : ℤ)) (fun c hc => ?_) ?_
    · obtain ⟨hmem, -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hc)
      obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hmem
      refine Finset.mem_Icc.mpr ⟨Int.ediv_nonneg (by omega) (by omega), ?_⟩
      exact Int.ediv_le_ediv (by omega) (by omega)
    · intro c hc c' hc' h
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hc hc'
      exact ediv_injOn_class_mod hc.2 hc'.2 h
  have hcard : (Finset.Icc (0 : ℤ) ((hi - lo) / (q : ℤ))).card
      = ((hi - lo) / (q : ℤ) + 1).toNat := by
    rw [Int.card_Icc]; congr 1; omega
  have hcast : (((Finset.Icc (0 : ℤ) ((hi - lo) / (q : ℤ))).card : ℝ))
      = (((hi - lo) / (q : ℤ) : ℤ) : ℝ) + 1 := by
    rw [hcard]
    have h1 : ((((hi - lo) / (q : ℤ) + 1).toNat : ℕ) : ℤ) = (hi - lo) / (q : ℤ) + 1 :=
      Int.toNat_of_nonneg (by omega)
    have h2 : ((((hi - lo) / (q : ℤ) + 1).toNat : ℕ) : ℝ)
        = ((((hi - lo) / (q : ℤ) + 1 : ℤ)) : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h1
    rw [h2]; push_cast; ring
  have hqd : (((hi - lo) / (q : ℤ) : ℤ) : ℝ) ≤ ((hi : ℝ) - (lo : ℝ)) / (q : ℝ) := by
    have hd := ediv_le_real hq (hi - lo)
    push_cast at hd
    linarith
  have hmono : ((((Finset.Icc lo hi).filter fun c : ℤ => (c : ZMod q) = r)).card : ℝ)
      ≤ ((Finset.Icc (0 : ℤ) ((hi - lo) / (q : ℤ))).card : ℝ) := by exact_mod_cast hkey
  rw [hcast] at hmono
  linarith

/-- **Single class.** The `q = 6` case, which the lattice count uses. -/
theorem card_residue_class_Icc {lo hi : ℤ} (hle : lo ≤ hi) (r : ZMod 6) :
    ((((Finset.Icc lo hi).filter fun c : ℤ => (c : ZMod 6) = r)).card : ℝ)
      ≤ ((hi : ℝ) - (lo : ℝ)) / 6 + 1 := by
  have h := card_residue_class_Icc_mod (q := 6) (by norm_num) hle r
  norm_num at h
  exact h

/-- **`k` classes.** For `lo ≤ hi`, the integers of `Finset.Icc lo hi` lying in
any of the classes of `S` number at most `#S * ((hi - lo) / 6) + #S`. -/
theorem card_residue_classes_Icc {lo hi : ℤ} (hle : lo ≤ hi) (S : Finset (ZMod 6)) :
    ((((Finset.Icc lo hi).filter fun c : ℤ => (c : ZMod 6) ∈ S)).card : ℝ)
      ≤ S.card * (((hi : ℝ) - (lo : ℝ)) / 6) + S.card := by
  classical
  -- the filter over `S` is the disjoint union of the single-class filters
  have hbi : ((Finset.Icc lo hi).filter fun c : ℤ => (c : ZMod 6) ∈ S)
      = S.biUnion fun r => ((Finset.Icc lo hi).filter fun c : ℤ => (c : ZMod 6) = r) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hmem, hS⟩; exact ⟨_, hS, hmem, rfl⟩
    · rintro ⟨r, hr, hmem, rfl⟩; exact ⟨hmem, hr⟩
  have hdisj : ∀ r ∈ S, ∀ r' ∈ S, r ≠ r' →
      Disjoint ((Finset.Icc lo hi).filter fun c : ℤ => (c : ZMod 6) = r)
        ((Finset.Icc lo hi).filter fun c : ℤ => (c : ZMod 6) = r') := by
    intro r _ r' _ hne
    refine Finset.disjoint_left.mpr ?_
    intro c hc hc'
    simp only [Finset.mem_filter] at hc hc'
    exact hne (hc.2 ▸ hc'.2 ▸ rfl)
  rw [hbi, Finset.card_biUnion hdisj, Nat.cast_sum]
  calc (∑ r ∈ S, (((((Finset.Icc lo hi).filter fun c : ℤ => (c : ZMod 6) = r)).card : ℝ)))
      ≤ ∑ _r ∈ S, (((hi : ℝ) - (lo : ℝ)) / 6 + 1) :=
        Finset.sum_le_sum fun r _ => card_residue_class_Icc hle r
    _ = S.card * (((hi : ℝ) - (lo : ℝ)) / 6) + S.card := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- The residue classes modulo `6` that the congruence admits for the outer
coefficient, given the inner coefficient `a` and the target class `t`. The
weight of `def_weight` is `2 * #(cClasses a 0) + #(cClasses a 2)`. -/
private def cClasses (a : ℤ) (t : ZMod 6) : Finset (ZMod 6) :=
  Finset.univ.filter fun γ => (a : ZMod 6) * γ = t

/-- **The count for fixed `a` and `b`.** Any finite set of outer coefficients
that is bounded below by `a`, bounded above by the discriminant condition, and
confined to the class `t` modulo `6`, has size at most

`#(cClasses a t) * (Y + b² - 4a²)_+ / (4a) / 6 + #(cClasses a t)`.

The target class `t` is a parameter rather than a case split on `b`, so the
caller supplies it from `lem_congruence_ac`: `t = 0` when `gcd (b, 3) = 1` and
`t = 2` when `3 ∣ b`.

The positive part is not a hedge. It is the integrand of `def_F`, so the bound
matches what the area function integrates, and it makes the statement true with
no nonemptiness hypothesis: when `Y + b² - 4a² < 0` the interval of admissible
`c` is empty and the right side is still nonnegative. -/
theorem card_c_le {a b : ℤ} {Y : ℝ} {t : ZMod 6} (ha : 1 ≤ a) (T : Finset ℤ)
    (hlo : ∀ c ∈ T, a ≤ c)
    (hub : ∀ c ∈ T, ((4 * a * c - b ^ 2 : ℤ) : ℝ) ≤ Y)
    (hres : ∀ c ∈ T, ((a * c : ℤ) : ZMod 6) = t) :
    (T.card : ℝ)
      ≤ (cClasses a t).card * (max (Y + (b : ℝ) ^ 2 - 4 * (a : ℝ) ^ 2) 0 / (4 * (a : ℝ)) / 6)
        + (cClasses a t).card := by
  classical
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have ha4 : (0 : ℝ) < 4 * (a : ℝ) := by linarith
  have hmaxnn : (0 : ℝ) ≤ max (Y + (b : ℝ) ^ 2 - 4 * (a : ℝ) ^ 2) 0 := le_max_right _ _
  -- the integer ceiling of the discriminant bound
  set hi : ℤ := ⌊(Y + (b : ℝ) ^ 2) / (4 * (a : ℝ))⌋ with hhi
  -- every admissible `c` lies in `Icc a hi` and in one of the classes
  have hsub : T ⊆ (Finset.Icc a hi).filter fun c : ℤ => (c : ZMod 6) ∈ cClasses a t := by
    intro c hc
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlo c hc, ?_⟩, ?_⟩
    · -- `4 a c ≤ Y + b²` gives `c ≤ (Y + b²)/(4a)`, hence `c ≤ ⌊·⌋`
      rw [hhi, Int.le_floor, le_div_iff₀ ha4]
      have h := hub c hc
      push_cast at h
      linarith
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have h := hres c hc
      push_cast at h
      exact h
  rcases T.eq_empty_or_nonempty with hemp | ⟨c₀, hc₀⟩
  · -- empty: the right side is nonnegative
    rw [hemp]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · -- nonempty, so `a ≤ hi` and the interval count applies
    have hle : a ≤ hi := le_trans (hlo c₀ hc₀) (Finset.mem_Icc.mp
      (Finset.mem_filter.mp (hsub hc₀)).1).2
    have hcount := card_residue_classes_Icc (lo := a) (hi := hi) hle (cClasses a t)
    have hmono : (T.card : ℝ)
        ≤ ((((Finset.Icc a hi).filter fun c : ℤ => (c : ZMod 6) ∈ cClasses a t)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    -- `⌊(Y + b²)/(4a)⌋ - a ≤ (Y + b² - 4a²)_+ / (4a)`
    have hfloor : (hi : ℝ) ≤ (Y + (b : ℝ) ^ 2) / (4 * (a : ℝ)) := by
      rw [hhi]; exact Int.floor_le _
    have hgap : (hi : ℝ) - (a : ℝ)
        ≤ max (Y + (b : ℝ) ^ 2 - 4 * (a : ℝ) ^ 2) 0 / (4 * (a : ℝ)) := by
      have hid : (Y + (b : ℝ) ^ 2) / (4 * (a : ℝ)) - (a : ℝ)
          = (Y + (b : ℝ) ^ 2 - 4 * (a : ℝ) ^ 2) / (4 * (a : ℝ)) := by
        field_simp
      have hstep : (hi : ℝ) - (a : ℝ)
          ≤ (Y + (b : ℝ) ^ 2 - 4 * (a : ℝ) ^ 2) / (4 * (a : ℝ)) := by
        rw [← hid]; linarith
      have hmax : (Y + (b : ℝ) ^ 2 - 4 * (a : ℝ) ^ 2) / (4 * (a : ℝ))
          ≤ max (Y + (b : ℝ) ^ 2 - 4 * (a : ℝ) ^ 2) 0 / (4 * (a : ℝ)) :=
        div_le_div_of_nonneg_right (le_max_left _ _) ha4.le
      linarith
    have hSnn : (0 : ℝ) ≤ ((cClasses a t).card : ℝ) := Nat.cast_nonneg _
    calc (T.card : ℝ)
        ≤ ((((Finset.Icc a hi).filter fun c : ℤ => (c : ZMod 6) ∈ cClasses a t)).card : ℝ) :=
          hmono
      _ ≤ (cClasses a t).card * (((hi : ℝ) - (a : ℝ)) / 6) + (cClasses a t).card := hcount
      _ ≤ (cClasses a t).card
            * (max (Y + (b : ℝ) ^ 2 - 4 * (a : ℝ) ^ 2) 0 / (4 * (a : ℝ)) / 6)
          + (cClasses a t).card := by
          have : ((hi : ℝ) - (a : ℝ)) / 6
              ≤ max (Y + (b : ℝ) ^ 2 - 4 * (a : ℝ) ^ 2) 0 / (4 * (a : ℝ)) / 6 := by
            linarith
          nlinarith [hSnn]

/-- **The fibre of a pair set, as a set of second coordinates.** On the fibre
over `b` the map `p ↦ p.2` is injective, since the first coordinate is pinned.

This is the entry point of the `lem_triple_count_a` assembly:
`Finset.card_eq_sum_card_fiberwise` expresses the pair count as a sum over `b`
of fibre cardinalities, but `card_c_le` takes a `Finset ℤ` of outer
coefficients — not a set of pairs. This converts one to the other without loss. -/
theorem fibre_card_eq_image (b : ℤ) (P : Finset (ℤ × ℤ)) :
    (P.filter fun p => p.1 = b).card
      = ((P.filter fun p => p.1 = b).image Prod.snd).card := by
  classical
  refine (Finset.card_image_of_injOn ?_).symm
  intro p hp q hq h
  simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp hq
  exact Prod.ext_iff.mpr ⟨hp.2.trans hq.2.symm, h⟩

/-- The weight of `def_weight` counted through `cClasses`. -/
theorem weight_eq_cClasses (a : ℤ) :
    2 * (cClasses a 0).card + (cClasses a 2).card
      = 2 * (Finset.univ.filter fun c : ZMod 6 => (a : ZMod 6) * c = 0).card
        + (Finset.univ.filter fun c : ZMod 6 => (a : ZMod 6) * c = 2).card := rfl

/-- `weight a` in the real numbers, through `cClasses`. -/
theorem weight_cast (a : ℤ) :
    ((weight a : ℕ) : ℝ)
      = 2 * ((cClasses a 0).card : ℝ) + ((cClasses a 2).card : ℝ) := by
  unfold weight cClasses
  push_cast
  ring

/-- The classes admitted for `c` at a given `b`: the congruence gives
`a * c ≡ 2 [ZMOD 6]` when `3 ∣ b` and `a * c ≡ 0 [ZMOD 6]` otherwise, by
`lem_congruence_ac`. -/
private noncomputable def bClasses (a b : ℤ) : Finset (ZMod 6) :=
  open Classical in
  if 3 ∣ b then cClasses a 2 else cClasses a 0

/-- **The grouping.** A sum over `b` weighted by `#(bClasses a b)` splits into
the two class counts, since `bClasses` depends on `b` only through `3 ∣ b`.

Over the odd residues modulo `6` this is what produces `weight a`: the classes
`b ≡ 1, 5` each contribute `#(cClasses a 0)` and `b ≡ 3` contributes
`#(cClasses a 2)`, and `weight_cast` says `2 * #(cClasses a 0) +
#(cClasses a 2)` is exactly `weight a`. Turning the three class-sums into a
single multiple of `weight a` is the remaining step, and it is an
approximation, not an identity — it needs the sum-to-integral comparison. -/
theorem sum_bClasses_split (a : ℤ) (B : Finset ℤ) (g : ℤ → ℝ) :
    ∑ b ∈ B, ((bClasses a b).card : ℝ) * g b
      = ((cClasses a 2).card : ℝ) * (∑ b ∈ B with (3 ∣ b), g b)
        + ((cClasses a 0).card : ℝ) * (∑ b ∈ B with ¬ (3 ∣ b), g b) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not B (fun b => 3 ∣ b)
        (fun b => ((bClasses a b).card : ℝ) * g b)]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun b hb => ?_
    have h3 : (3 : ℤ) ∣ b := (Finset.mem_filter.mp hb).2
    rw [bClasses, if_pos h3]
  · refine Finset.sum_congr rfl fun b hb => ?_
    have h3 : ¬ ((3 : ℤ) ∣ b) := (Finset.mem_filter.mp hb).2
    rw [bClasses, if_neg h3]

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# Counting reduced triples with a given first coefficient

For a fixed inner coefficient `a`, the reduced triples of discriminant at most
`Y` in the admissible congruence class are counted by their remaining two
coefficients. The count is `w(a)/6 · F_Y(a) + O(Y/a + a)`, with the constant
exhibited: `18`. No asymptotic notation appears, since the summation over `a`
needs the constant uniform in both `Y` and `a`.

`card_c_le` bounds the outer coefficients for fixed `a` and `b` by
`#(bClasses a b) · L⁺(b)/6 + #(bClasses a b)` where `L⁺(t) = (Y + t² - 4a²)₊/(4a)`;
`sum_bClasses_split` groups the sum over `b` into the two class counts;
`weight_cast` recognises `2·#(cClasses a 0) + #(cClasses a 2)` as `w(a)`; and
`integral_Lplus_eq` converts the integral of `L⁺` into `6 F_Y(a)`.

The sum-to-integral comparison is one-sided and only ever needs an upper bound,
so each of the three odd residue classes modulo `6` is handled by
`sum_class_le`: split `[-a, a]` at `0`, reflect the negative half through the
evenness of `L⁺`, and on each monotone half drop the largest point of the
progression — which costs one boundary term `L⁺(a) ≤ Y/(4a)` — so that the
remaining points have their whole step-`6` block inside the interval and
`sum_step_six_le_integral` applies.

The constants close exactly. Each class contributes `(1/6)∫_0^a L⁺ = F_Y(a)/2`
per half, hence `F_Y(a)` per class; the classes `b ≡ 1, 5` carry
`#(cClasses a 0)` and `b ≡ 3` carries `#(cClasses a 2)`; and the `1/6` of
`card_c_le` survives. The main term is therefore
`(2·#(cClasses a 0) + #(cClasses a 2))/6 · F_Y(a) = w(a)/6 · F_Y(a)`, with
nothing left over to hide in the error.

## Main results

* `PartitionZheng.integral_Lplus_half` — `∫_0^a L⁺ = 3 F_Y(a)`.
* `PartitionZheng.sum_progression_le` — the step-`6` comparison on `[0, a]`.
* `PartitionZheng.sum_class_le` — one residue class modulo `6` over `[-a, a]`.
* `PartitionZheng.card_fibre_le` — the pairs with a fixed middle coefficient.
* `PartitionZheng.card_pairs_le` — the pair count, for a `Finset` of pairs.
* `PartitionZheng.exists_const_card_pairs_le` — the pair count with an explicit
  constant, for the triples of `reducedTriplesUpTo Y`.
-/


namespace PartitionZheng

open Finset

/-- `L⁺` is a polynomial composed with `max` and divided by a constant, hence
continuous. -/
theorem Lplus_continuous (Y a : ℝ) : Continuous (Lplus Y a) := by
  unfold Lplus
  fun_prop

/-- `L⁺` is interval integrable on every interval, being continuous. -/
theorem Lplus_intervalIntegrable (Y a u v : ℝ) :
    IntervalIntegrable (Lplus Y a) MeasureTheory.volume u v :=
  (Lplus_continuous Y a).intervalIntegrable u v

/-- `L⁺` is nonnegative for `a > 0`: it is a positive part divided by `4a`. -/
theorem Lplus_nonneg {Y a : ℝ} (ha : 0 < a) (t : ℝ) : 0 ≤ Lplus Y a t := by
  unfold Lplus
  exact div_nonneg (le_max_right _ _) (by linarith)

/-- `L⁺` is at most `Y / (4a)` on `[-2a, 2a]`, since there `t² - 4a² ≤ 0`. -/
theorem Lplus_le {Y a t : ℝ} (ha : 0 < a) (hY : 0 ≤ Y) (ht : t ^ 2 ≤ 4 * a ^ 2) :
    Lplus Y a t ≤ Y / (4 * a) := by
  have ha4 : (0 : ℝ) < 4 * a := by linarith
  unfold Lplus
  apply div_le_div_of_nonneg_right ?_ ha4.le
  exact max_le (by linarith) hY

/-- The two halves of `[-a, a]` carry the same integral of `L⁺`, by evenness. -/
theorem integral_Lplus_left_eq_right (Y a : ℝ) :
    (∫ t in (-a)..(0 : ℝ), Lplus Y a t) = ∫ t in (0 : ℝ)..a, Lplus Y a t := by
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := a) (f := Lplus Y a)
  rw [neg_zero] at h
  rw [← h]
  refine intervalIntegral.integral_congr ?_
  intro t _
  -- `integral_congr` leaves the integrands un-beta-reduced
  change Lplus Y a (-t) = Lplus Y a t
  rw [Lplus_neg]

/-- **Half the area integral.** For `a > 0`, `∫_0^a L⁺(t) dt = 3 · F_Y(a)`.

`integral_Lplus_eq` gives the integral over `[-a, a]`, and `L⁺` is even, so each
half is `3 · F_Y(a)`. -/
theorem integral_Lplus_half {Y a : ℝ} (ha : 0 < a) :
    (∫ t in (0 : ℝ)..a, Lplus Y a t) = 3 * areaF Y a := by
  have hsplit : (∫ t in (-a)..(0 : ℝ), Lplus Y a t) + (∫ t in (0 : ℝ)..a, Lplus Y a t)
      = ∫ t in (-a)..a, Lplus Y a t :=
    intervalIntegral.integral_add_adjacent_intervals
      (Lplus_intervalIntegrable Y a _ _) (Lplus_intervalIntegrable Y a _ _)
  rw [integral_Lplus_left_eq_right, integral_Lplus_eq ha] at hsplit
  linarith

/-- **The step-`6` progression bound on the monotone half.** For a progression
`p, p + 6, …, p + 6(n-1)` inside `[0, a]`, the sum of `L⁺` over it is at most a
sixth of `∫_0^a L⁺` plus one boundary term `Y / (4a)`.

Dropping the largest point and comparing the rest with the integral is what
makes the error a single boundary term: the remaining `n - 1` points have their
whole step-`6` block inside `[0, a]`, so `sum_step_six_le_integral` applies, and
the dropped point contributes at most `L⁺(a) ≤ Y / (4a)`. -/
theorem sum_progression_le {Y a : ℝ} (ha : 0 < a) (hY : 0 ≤ Y) {p : ℝ} (hp : 0 ≤ p)
    {n : ℕ} (hn : ∀ i < n, p + 6 * (i : ℝ) ≤ a) :
    ∑ i ∈ Finset.range n, Lplus Y a (p + 6 * (i : ℝ))
      ≤ (1 / 6) * (∫ t in (0 : ℝ)..a, Lplus Y a t) + Y / (4 * a) := by
  have hnn : ∀ t : ℝ, 0 ≤ Lplus Y a t := fun t => Lplus_nonneg ha t
  have hint0 : (0 : ℝ) ≤ ∫ t in (0 : ℝ)..a, Lplus Y a t :=
    intervalIntegral.integral_nonneg ha.le fun u _ => hnn u
  have hYa : (0 : ℝ) ≤ Y / (4 * a) := by positivity
  rcases n with _ | m
  · simp only [Finset.range_zero, Finset.sum_empty]
    linarith
  · rw [Finset.sum_range_succ]
    have hma : p + 6 * (m : ℝ) ≤ a := hn m (by omega)
    have hm0 : (0 : ℝ) ≤ 6 * (m : ℝ) := by positivity
    -- the dropped point contributes at most one boundary term
    have hlast : Lplus Y a (p + 6 * (m : ℝ)) ≤ Y / (4 * a) := by
      have h1 : Lplus Y a (p + 6 * (m : ℝ)) ≤ Lplus Y a a :=
        Lplus_monotoneOn ha (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr ha.le) hma
      have h2 : Lplus Y a a ≤ Y / (4 * a) := Lplus_le ha hY (by nlinarith)
      linarith
    -- the remaining points sit in blocks inside `[0, a]`
    have hmono : MonotoneOn (Lplus Y a) (Set.Icc p (p + 6 * (m : ℝ))) := by
      intro u hu v hv huv
      exact Lplus_monotoneOn ha (Set.mem_Ici.mpr (le_trans hp hu.1))
        (Set.mem_Ici.mpr (le_trans hp hv.1)) huv
    have hsum := sum_step_six_le_integral (f := Lplus Y a) (p := p) (n := m) hmono
    have hmi : (∫ x in p..(p + 6 * (m : ℝ)), Lplus Y a x)
        ≤ ∫ t in (0 : ℝ)..a, Lplus Y a t :=
      intervalIntegral.integral_mono_interval hp (by linarith) hma
        (Filter.Eventually.of_forall fun t => hnn t) (Lplus_intervalIntegrable Y a _ _)
    linarith

/-- **A residue class in `[0, a]`.** The integers of `[0, a]` congruent to
`s` modulo `6`, for `0 ≤ s`, carry a sum of `L⁺` at most a sixth of `∫_0^a L⁺`
plus `Y / (4a)`.

The class is contained in the step-`6` progression starting at `s`, truncated at
the last term not exceeding `a`; the containment is enough because `L⁺ ≥ 0`. -/
theorem sum_class_Icc_zero_le {Y : ℝ} (hY : 0 ≤ Y) {a : ℤ} (ha : 1 ≤ a) {s : ℤ}
    (hs : 0 ≤ s) :
    ∑ b ∈ {b ∈ Finset.Icc (0 : ℤ) a | b % 6 = s}, Lplus Y (a : ℝ) (b : ℝ)
      ≤ (1 / 6) * (∫ t in (0 : ℝ)..(a : ℝ), Lplus Y (a : ℝ) t) + Y / (4 * (a : ℝ)) := by
  classical
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < a)
  have hnn : ∀ t : ℝ, 0 ≤ Lplus Y (a : ℝ) t := fun t => Lplus_nonneg ha0 t
  -- the length of the truncated progression
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, (a - s) / 6 < (n : ℤ)
      ∧ ∀ i : ℕ, i < n → s + 6 * (i : ℤ) ≤ a :=
    ⟨((a - s) / 6 + 1).toNat, by omega, fun i hi => by omega⟩
  have hsub : {b ∈ Finset.Icc (0 : ℤ) a | b % 6 = s}
      ⊆ (Finset.range n).image fun i : ℕ => s + 6 * (i : ℤ) := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_Icc] at hb
    exact Finset.mem_image.mpr ⟨(b / 6).toNat, Finset.mem_range.mpr (by omega), by omega⟩
  calc ∑ b ∈ {b ∈ Finset.Icc (0 : ℤ) a | b % 6 = s}, Lplus Y (a : ℝ) (b : ℝ)
      ≤ ∑ b ∈ (Finset.range n).image fun i : ℕ => s + 6 * (i : ℤ),
          Lplus Y (a : ℝ) (b : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun b _ _ => hnn _
    _ = ∑ i ∈ Finset.range n, Lplus Y (a : ℝ) ((s : ℝ) + 6 * (i : ℝ)) := by
        rw [Finset.sum_image fun i _ j _ h => by omega]
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        push_cast
        ring
    _ ≤ (1 / 6) * (∫ t in (0 : ℝ)..(a : ℝ), Lplus Y (a : ℝ) t) + Y / (4 * (a : ℝ)) := by
        refine sum_progression_le ha0 hY (by exact_mod_cast hs) fun i hi => ?_
        have := hn2 i hi
        have : ((s + 6 * (i : ℤ) : ℤ) : ℝ) ≤ ((a : ℤ) : ℝ) := by exact_mod_cast this
        push_cast at this
        linarith

/-- **A residue class in `[-a, a]`.** For `0 ≤ r`, the integers of `[-a, a]`
congruent to `r` modulo `6` carry a sum of `L⁺` at most `F_Y(a) + Y / (2a)`.

The interval is split at `0`. On `[0, a]` this is `sum_class_Icc_zero_le`
directly; on `[-a, -1]` the map `b ↦ -b` carries the class into the class of
`-r` modulo `6` inside `[0, a]`, and `L⁺` is even, so the same bound applies.
Two halves at `(1/6) ∫_0^a L⁺ = F_Y(a)/2` each — by `integral_Lplus_half` — give
the main term `F_Y(a)`, and the two boundary terms give `Y / (2a)`. -/
theorem sum_class_le {Y : ℝ} (hY : 0 ≤ Y) {a : ℤ} (ha : 1 ≤ a) {r : ℤ} (hr : 0 ≤ r) :
    ∑ b ∈ {b ∈ Finset.Icc (-a) a | b % 6 = r}, Lplus Y (a : ℝ) (b : ℝ)
      ≤ areaF Y (a : ℝ) + Y / (2 * (a : ℝ)) := by
  classical
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < a)
  have hnn : ∀ t : ℝ, 0 ≤ Lplus Y (a : ℝ) t := fun t => Lplus_nonneg ha0 t
  -- the positive half
  have hpos := sum_class_Icc_zero_le hY ha hr
  -- the negative half, reflected
  have hneg : ∑ b ∈ {b ∈ Finset.Icc (-a) (-1) | b % 6 = r}, Lplus Y (a : ℝ) (b : ℝ)
      ≤ (1 / 6) * (∫ t in (0 : ℝ)..(a : ℝ), Lplus Y (a : ℝ) t) + Y / (4 * (a : ℝ)) := by
    have himg : (({b ∈ Finset.Icc (-a) (-1) | b % 6 = r}).image fun b : ℤ => -b)
        ⊆ {b ∈ Finset.Icc (0 : ℤ) a | b % 6 = (-r) % 6} := by
      intro c hc
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hc ⊢
      obtain ⟨b, ⟨⟨hb1, hb2⟩, hb3⟩, rfl⟩ := hc
      exact ⟨⟨by omega, by omega⟩, by omega⟩
    have heq : ∑ b ∈ {b ∈ Finset.Icc (-a) (-1) | b % 6 = r}, Lplus Y (a : ℝ) (b : ℝ)
        = ∑ c ∈ (({b ∈ Finset.Icc (-a) (-1) | b % 6 = r}).image fun b : ℤ => -b),
            Lplus Y (a : ℝ) (c : ℝ) := by
      rw [Finset.sum_image fun i _ j _ h => by omega]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [show (((-b : ℤ)) : ℝ) = -((b : ℤ) : ℝ) by push_cast; ring, Lplus_neg]
    rw [heq]
    calc ∑ c ∈ (({b ∈ Finset.Icc (-a) (-1) | b % 6 = r}).image fun b : ℤ => -b),
          Lplus Y (a : ℝ) (c : ℝ)
        ≤ ∑ c ∈ {b ∈ Finset.Icc (0 : ℤ) a | b % 6 = (-r) % 6},
            Lplus Y (a : ℝ) (c : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg himg fun c _ _ => hnn _
      _ ≤ (1 / 6) * (∫ t in (0 : ℝ)..(a : ℝ), Lplus Y (a : ℝ) t) + Y / (4 * (a : ℝ)) :=
          sum_class_Icc_zero_le hY ha (Int.emod_nonneg _ (by norm_num))
  -- the two halves partition the class
  have hunion : {b ∈ Finset.Icc (-a) a | b % 6 = r}
      = {b ∈ Finset.Icc (-a) (-1) | b % 6 = r}
        ∪ {b ∈ Finset.Icc (0 : ℤ) a | b % 6 = r} := by
    ext b
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
    omega
  have hdisj : Disjoint {b ∈ Finset.Icc (-a) (-1) | b % 6 = r}
      {b ∈ Finset.Icc (0 : ℤ) a | b % 6 = r} := by
    refine Finset.disjoint_left.mpr fun b hb hb' => ?_
    simp only [Finset.mem_filter, Finset.mem_Icc] at hb hb'
    omega
  rw [integral_Lplus_half ha0] at hpos hneg
  rw [hunion, Finset.sum_union hdisj]
  have h2a : Y / (4 * (a : ℝ)) + Y / (4 * (a : ℝ)) = Y / (2 * (a : ℝ)) := by
    field_simp
    ring
  linarith

/-- `bClasses` at a multiple of `3` is the `a * c ≡ 2` class set. -/
theorem bClasses_of_three_dvd (a : ℤ) {b : ℤ} (h : 3 ∣ b) :
    bClasses a b = cClasses a 2 := by
  rw [bClasses, if_pos h]

/-- `bClasses` away from the multiples of `3` is the `a * c ≡ 0` class set. -/
theorem bClasses_of_not_three_dvd (a : ℤ) {b : ℤ} (h : ¬ 3 ∣ b) :
    bClasses a b = cClasses a 0 := by
  rw [bClasses, if_neg h]

/-- A set of residue classes modulo `6` has at most `6` members. -/
theorem card_cClasses_le (a : ℤ) (t : ZMod 6) : (cClasses a t).card ≤ 6 := by
  have h : (cClasses a t).card ≤ (Finset.univ : Finset (ZMod 6)).card :=
    Finset.card_le_card (Finset.subset_univ _)
  rwa [Finset.card_univ, ZMod.card] at h

/-- The weight is at most `18`, since each of the three class counts it adds is
at most `6`. The exact maximum is `12`, by `weight_values`. -/
theorem weight_le (a : ℤ) : (weight a : ℝ) ≤ 18 := by
  rw [weight_cast]
  have h0 : ((cClasses a 0).card : ℝ) ≤ 6 := by exact_mod_cast card_cClasses_le a 0
  have h2 : ((cClasses a 2).card : ℝ) ≤ 6 := by exact_mod_cast card_cClasses_le a 2
  linarith

/-- **One fibre of the pair count.** For a finite set `P` of pairs `(b, c)` all
completing `a` to a triple of discriminant at most `Y` in the admissible class,
the fibre over a fixed `b` has size at most
`#(bClasses a b) · L⁺(b)/6 + #(bClasses a b)`.

The fibre becomes a set of outer coefficients by `fibre_card_eq_image`, and the
congruence fixes their class modulo `6`: `odd_of_disc` makes `b` odd, and then
`disc_emod_iff_of_three_dvd` and `disc_emod_iff_of_not_three_dvd` give
`a * c ≡ 2` when `3 ∣ b` and `a * c ≡ 0` otherwise — which is exactly the case
split defining `bClasses`. -/
theorem card_fibre_le {Y : ℝ} {a : ℤ} (ha : 1 ≤ a) {P : Finset (ℤ × ℤ)}
    (hP : ∀ p ∈ P, a ≤ p.2 ∧ ((4 * a * p.2 - p.1 ^ 2 : ℤ) : ℝ) ≤ Y ∧
      (4 * a * p.2 - p.1 ^ 2) % 24 = 23) (b : ℤ) :
    ((({p ∈ P | p.1 = b}).card : ℕ) : ℝ)
      ≤ ((bClasses a b).card : ℝ) * (Lplus Y (a : ℝ) (b : ℝ) / 6)
        + ((bClasses a b).card : ℝ) := by
  classical
  rw [fibre_card_eq_image]
  -- the fibre's outer coefficients, with the three constraints transported to `b`
  have hmem : ∀ c ∈ (({p ∈ P | p.1 = b}).image Prod.snd),
      a ≤ c ∧ ((4 * a * c - b ^ 2 : ℤ) : ℝ) ≤ Y ∧ (4 * a * c - b ^ 2) % 24 = 23 := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hpP, hpb⟩ := Finset.mem_filter.mp hp
    obtain ⟨h1, h2, h3⟩ := hP p hpP
    rw [hpb] at h2 h3
    exact ⟨h1, h2, h3⟩
  have key : ∀ t : ZMod 6, bClasses a b = cClasses a t →
      (∀ c ∈ (({p ∈ P | p.1 = b}).image Prod.snd), ((a * c : ℤ) : ZMod 6) = t) →
      (((({p ∈ P | p.1 = b}).image Prod.snd).card : ℕ) : ℝ)
        ≤ ((bClasses a b).card : ℝ) * (Lplus Y (a : ℝ) (b : ℝ) / 6)
          + ((bClasses a b).card : ℝ) := by
    intro t ht hres
    rw [ht]
    unfold Lplus
    exact card_c_le ha _ (fun c hc => (hmem c hc).1) (fun c hc => (hmem c hc).2.1) hres
  by_cases h3 : (3 : ℤ) ∣ b
  · refine key 2 (bClasses_of_three_dvd a h3) fun c hc => ?_
    obtain ⟨-, -, hdisc⟩ := hmem c hc
    have hodd : Odd b := odd_of_disc hdisc
    rw [mul_assoc] at hdisc
    have h6 : (a * c) % 6 = 2 := (disc_emod_iff_of_three_dvd hodd h3).mp hdisc
    have hcast : ((a * c : ℤ) : ZMod 6) = ((2 : ℤ) : ZMod 6) :=
      (ZMod.intCast_eq_intCast_iff' _ _ _).mpr (by push_cast; omega)
    simpa using hcast
  · refine key 0 (bClasses_of_not_three_dvd a h3) fun c hc => ?_
    obtain ⟨-, -, hdisc⟩ := hmem c hc
    have hodd : Odd b := odd_of_disc hdisc
    rw [mul_assoc] at hdisc
    have h6 : (a * c) % 6 = 0 := (disc_emod_iff_of_not_three_dvd hodd h3).mp hdisc
    have hcast : ((a * c : ℤ) : ZMod 6) = ((0 : ℤ) : ZMod 6) :=
      (ZMod.intCast_eq_intCast_iff' _ _ _).mpr (by push_cast; omega)
    simpa using hcast

/-- **The pair count for a fixed first coefficient, in `Finset` form.** Any
finite set `P` of pairs `(b, c)` completing `a` to a reduced triple of
discriminant at most `Y` in the admissible class satisfies

`#P ≤ w(a)/6 · F_Y(a) + 18 · (Y/a + a)`.

The constant `18` is explicit, no asymptotic notation appearing. It absorbs the
`w(a) ≤ 18` boundary terms of `card_c_le`, one for each of the at most `2a + 1`
values of `b`, and the `w(a)` sum-to-integral errors, each at most `Y/(4a)`, and
nothing further. The main term closes exactly — `card_c_le` carries a `1/6`, each
residue class modulo `6` contributes a sixth of the integral, and
`∫_{-a}^{a} L⁺ = 6 F_Y(a)`. -/
theorem card_pairs_le {Y : ℝ} (hY : 0 ≤ Y) {a : ℤ} (ha : 1 ≤ a) {P : Finset (ℤ × ℤ)}
    (hP : ∀ p ∈ P, |p.1| ≤ a ∧ a ≤ p.2 ∧ ((4 * a * p.2 - p.1 ^ 2 : ℤ) : ℝ) ≤ Y ∧
      (4 * a * p.2 - p.1 ^ 2) % 24 = 23) :
    ((P.card : ℕ) : ℝ)
      ≤ (weight a : ℝ) / 6 * areaF Y (a : ℝ) + 18 * (Y / (a : ℝ) + (a : ℝ)) := by
  classical
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < a)
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  set B : Finset ℤ := {b ∈ Finset.Icc (-a) a | b % 2 = 1} with hBdef
  -- the first coordinate is odd, and reducedness bounds it by `a`
  have hmaps : ∀ p ∈ P, p.1 ∈ B := by
    intro p hp
    obtain ⟨h1, -, -, h4⟩ := hP p hp
    have hodd : p.1 % 2 = 1 := Int.odd_iff.mp (odd_of_disc h4)
    rw [hBdef]
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨neg_le_of_abs_le h1, le_of_abs_le h1⟩, hodd⟩
  have hcard : ((P.card : ℕ) : ℝ)
      = ∑ b ∈ B, ((({p ∈ P | p.1 = b}).card : ℕ) : ℝ) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p : ℤ × ℤ => p.1) (t := B)
      fun p hp => hmaps p hp, Nat.cast_sum]
  have hstep : ((P.card : ℕ) : ℝ)
      ≤ ∑ b ∈ B, (((bClasses a b).card : ℝ) * (Lplus Y (a : ℝ) (b : ℝ) / 6)
          + ((bClasses a b).card : ℝ)) := by
    rw [hcard]
    refine Finset.sum_le_sum fun b _ => card_fibre_le ha (fun p hp => ?_) b
    obtain ⟨-, h2, h3, h4⟩ := hP p hp
    exact ⟨h2, h3, h4⟩
  rw [Finset.sum_add_distrib] at hstep
  -- the boundary terms: at most `6` classes for each of at most `2a + 1` values of `b`
  have hbdd : ∀ b : ℤ, ((bClasses a b).card : ℝ) ≤ 6 := by
    intro b
    by_cases h3 : (3 : ℤ) ∣ b
    · rw [bClasses_of_three_dvd a h3]
      exact_mod_cast card_cClasses_le a 2
    · rw [bClasses_of_not_three_dvd a h3]
      exact_mod_cast card_cClasses_le a 0
  have hBcard : ((B.card : ℕ) : ℝ) ≤ 2 * (a : ℝ) + 1 := by
    have h1 : B.card ≤ (Finset.Icc (-a) a).card := by
      rw [hBdef]; exact Finset.card_le_card (Finset.filter_subset _ _)
    rw [Int.card_Icc] at h1
    have h2 : ((B.card : ℕ) : ℤ) ≤ 2 * a + 1 := by omega
    exact_mod_cast h2
  have herr : ∑ b ∈ B, ((bClasses a b).card : ℝ) ≤ 6 * (2 * (a : ℝ) + 1) := by
    calc ∑ b ∈ B, ((bClasses a b).card : ℝ) ≤ ∑ _b ∈ B, (6 : ℝ) :=
          Finset.sum_le_sum fun b _ => hbdd b
      _ = ((B.card : ℕ) : ℝ) * 6 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 6 * (2 * (a : ℝ) + 1) := by linarith
  -- the three odd residue classes modulo `6`
  have hC3 : {b ∈ B | (3 : ℤ) ∣ b} = {b ∈ Finset.Icc (-a) a | b % 6 = 3} := by
    rw [hBdef]
    ext b
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have hC15 : {b ∈ B | ¬ ((3 : ℤ) ∣ b)}
      = {b ∈ Finset.Icc (-a) a | b % 6 = 1} ∪ {b ∈ Finset.Icc (-a) a | b % 6 = 5} := by
    rw [hBdef]
    ext b
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
    omega
  have hdisj15 : Disjoint ({b ∈ Finset.Icc (-a) a | b % 6 = 1} : Finset ℤ)
      {b ∈ Finset.Icc (-a) a | b % 6 = 5} := by
    refine Finset.disjoint_left.mpr fun b hb hb' => ?_
    simp only [Finset.mem_filter, Finset.mem_Icc] at hb hb'
    omega
  have e3 : (∑ b ∈ {b ∈ B | (3 : ℤ) ∣ b}, Lplus Y (a : ℝ) (b : ℝ) / 6)
      = (∑ b ∈ {b ∈ Finset.Icc (-a) a | b % 6 = 3}, Lplus Y (a : ℝ) (b : ℝ)) / 6 := by
    rw [hC3, Finset.sum_div]
  have e15 : (∑ b ∈ {b ∈ B | ¬ ((3 : ℤ) ∣ b)}, Lplus Y (a : ℝ) (b : ℝ) / 6)
      = (∑ b ∈ {b ∈ Finset.Icc (-a) a | b % 6 = 1}, Lplus Y (a : ℝ) (b : ℝ)) / 6
        + (∑ b ∈ {b ∈ Finset.Icc (-a) a | b % 6 = 5}, Lplus Y (a : ℝ) (b : ℝ)) / 6 := by
    rw [hC15, Finset.sum_union hdisj15, Finset.sum_div, Finset.sum_div]
  have hb1 := sum_class_le hY ha (r := 1) (by norm_num)
  have hb3 := sum_class_le hY ha (r := 3) (by norm_num)
  have hb5 := sum_class_le hY ha (r := 5) (by norm_num)
  have hc0 : (0 : ℝ) ≤ ((cClasses a 0).card : ℝ) := Nat.cast_nonneg _
  have hc2 : (0 : ℝ) ≤ ((cClasses a 2).card : ℝ) := Nat.cast_nonneg _
  -- the main term, with the weight assembled by `sum_bClasses_split`
  have hkey : (∑ b ∈ B, ((bClasses a b).card : ℝ) * (Lplus Y (a : ℝ) (b : ℝ) / 6))
      ≤ (weight a : ℝ) / 6 * areaF Y (a : ℝ)
        + (weight a : ℝ) * (Y / (2 * (a : ℝ))) / 6 := by
    rw [sum_bClasses_split a B fun b => Lplus Y (a : ℝ) (b : ℝ) / 6, e3, e15]
    have t1 : (∑ b ∈ {b ∈ Finset.Icc (-a) a | b % 6 = 3}, Lplus Y (a : ℝ) (b : ℝ)) / 6
        ≤ (areaF Y (a : ℝ) + Y / (2 * (a : ℝ))) / 6 := by linarith
    have t2 : (∑ b ∈ {b ∈ Finset.Icc (-a) a | b % 6 = 1}, Lplus Y (a : ℝ) (b : ℝ)) / 6
        + (∑ b ∈ {b ∈ Finset.Icc (-a) a | b % 6 = 5}, Lplus Y (a : ℝ) (b : ℝ)) / 6
        ≤ 2 * ((areaF Y (a : ℝ) + Y / (2 * (a : ℝ))) / 6) := by linarith
    have p1 := mul_le_mul_of_nonneg_left t1 hc2
    have p2 := mul_le_mul_of_nonneg_left t2 hc0
    calc ((cClasses a 2).card : ℝ)
            * ((∑ b ∈ {b ∈ Finset.Icc (-a) a | b % 6 = 3}, Lplus Y (a : ℝ) (b : ℝ)) / 6)
          + ((cClasses a 0).card : ℝ)
            * ((∑ b ∈ {b ∈ Finset.Icc (-a) a | b % 6 = 1}, Lplus Y (a : ℝ) (b : ℝ)) / 6
              + (∑ b ∈ {b ∈ Finset.Icc (-a) a | b % 6 = 5}, Lplus Y (a : ℝ) (b : ℝ)) / 6)
        ≤ ((cClasses a 2).card : ℝ) * ((areaF Y (a : ℝ) + Y / (2 * (a : ℝ))) / 6)
          + ((cClasses a 0).card : ℝ)
            * (2 * ((areaF Y (a : ℝ) + Y / (2 * (a : ℝ))) / 6)) := by linarith
      _ = (2 * ((cClasses a 0).card : ℝ) + ((cClasses a 2).card : ℝ))
            * ((areaF Y (a : ℝ) + Y / (2 * (a : ℝ))) / 6) := by ring
      _ = (weight a : ℝ) * ((areaF Y (a : ℝ) + Y / (2 * (a : ℝ))) / 6) := by
          rw [← weight_cast a]
      _ = (weight a : ℝ) / 6 * areaF Y (a : ℝ)
            + (weight a : ℝ) * (Y / (2 * (a : ℝ))) / 6 := by ring
  -- collect the two error contributions into `18 · (Y/a + a)`
  have hE : (0 : ℝ) ≤ Y / (2 * (a : ℝ)) := by positivity
  have hYd : Y / (2 * (a : ℝ)) = Y / (a : ℝ) / 2 := by rw [div_div, mul_comm]
  have hYa0 : (0 : ℝ) ≤ Y / (a : ℝ) := by positivity
  have hprod : (weight a : ℝ) * (Y / (2 * (a : ℝ))) / 6
      ≤ 18 * (Y / (2 * (a : ℝ))) / 6 := by
    have h := mul_le_mul_of_nonneg_right (weight_le a) hE
    linarith
  linarith

/-- The pairs `(b, c)` completing a fixed `a ≥ 1` to a reduced triple of
discriminant at most `Y` form a finite set: reducedness bounds `b` by `a`, and
the discriminant bound caps `c`. -/
theorem pairs_finite (Y : ℝ) {a : ℤ} (ha : 1 ≤ a) :
    {p : ℤ × ℤ | (a, p.1, p.2) ∈ reducedTriplesUpTo Y}.Finite := by
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < a)
  have hfin : (Set.Icc (-a) a ×ˢ Set.Icc a ⌈(Y + (a : ℝ) ^ 2) / (4 * (a : ℝ))⌉).Finite :=
    (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
  refine hfin.subset ?_
  rintro ⟨b, c⟩ hp
  obtain ⟨h1, h2, -, h4, -⟩ : |b| ≤ a ∧ a ≤ c ∧ 0 < 4 * a * c - b ^ 2 ∧
      ((4 * a * c - b ^ 2 : ℤ) : ℝ) ≤ Y ∧ (4 * a * c - b ^ 2) % 24 = 23 := hp
  have hb2 : ((b : ℝ)) ^ 2 ≤ ((a : ℝ)) ^ 2 := by
    have hz : b ^ 2 ≤ a ^ 2 := by
      calc b ^ 2 = |b| ^ 2 := (sq_abs b).symm
        _ ≤ a ^ 2 := by nlinarith [abs_nonneg b]
    exact_mod_cast hz
  have hc : (c : ℝ) ≤ (Y + (a : ℝ) ^ 2) / (4 * (a : ℝ)) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 4 * (a : ℝ))]
    push_cast at h4
    linarith
  refine Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨neg_le_of_abs_le h1, le_of_abs_le h1⟩,
    Set.mem_Icc.mpr ⟨h2, ?_⟩⟩
  exact Int.cast_le.mp (hc.trans (Int.le_ceil _))

/-- **`lem_triple_count_a`.** There is an explicit constant `C > 0` — namely
`C = 18` — such that for every `Y ≥ 1` and every integer `a` with `1 ≤ a` and
`3a² ≤ Y`,

`#{(b, c) : (a, b, c) ∈ T*(Y)} ≤ w(a)/6 · F_Y(a) + C · (Y/a + a)`.

The range is recorded as `3a² ≤ Y` rather than as `1 ≤ a ≤ √(Y/3)`; the two are
equivalent for `a ≥ 0`. The upper bound on `a` is not needed for the inequality:
`card_pairs_le` establishes it for every `a ≥ 1`, the positive part in `L⁺`
making the count vacuously bounded once `4a² > Y + b²`. -/
theorem exists_const_card_pairs_le :
    ∃ C > 0, ∀ Y : ℝ, 1 ≤ Y → ∀ a : ℤ, 1 ≤ a → 3 * (a : ℝ) ^ 2 ≤ Y →
      (({p : ℤ × ℤ | (a, p.1, p.2) ∈ reducedTriplesUpTo Y}.ncard : ℕ) : ℝ)
        ≤ (weight a : ℝ) / 6 * areaF Y (a : ℝ) + C * (Y / (a : ℝ) + (a : ℝ)) := by
  refine ⟨18, by norm_num, fun Y hY a ha _ => ?_⟩
  classical
  have hfin := pairs_finite Y ha
  rw [Set.ncard_eq_toFinset_card _ hfin]
  refine card_pairs_le (by linarith) ha fun p hp => ?_
  rw [Set.Finite.mem_toFinset] at hp
  obtain ⟨h1, h2, -, h4, h5⟩ := hp
  exact ⟨h1, h2, h4, h5⟩

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# Discharging the explicit hypotheses

Several results in this development are stated with their dependencies as
explicit hypotheses. Those hypotheses are discharged here, leaving statements
that depend on nothing but the parity theorem.

Two of them are phrased differently on the two sides and need a conversion
rather than a direct application:

* `exists_const_card_pairs_le` states its range condition as `3 a² ≤ Y`, while
  `class_average` states it as `a ≤ √(Y/3)`. The two are equivalent for `a ≥ 1`;
  `three_sq_le_of_sqrt` converts.
* `exists_weighted_areaF_sum_le` assumes the integral bound written with the
  literal `π / 108`, while `integral_areaF` writes it with `beta`. These are
  definitionally equal.

## Main results

* `PartitionZheng.exists_weighted_areaF_sum_le_unconditional` — the weighted sum of
  the areas `areaF Y a` bounded by `π / 108 * Y √Y + C * Y log Y`.
* `PartitionZheng.class_average_unconditional` — the class numbers of the admissible
  discriminants up to `Y` sum to at most `(beta + ε) * Y √Y` for all large `Y`.
-/


namespace PartitionZheng

open Real

/-- For `a ≥ 1`, `a ≤ √(Y/3)` gives `3 a² ≤ Y`. -/
theorem three_sq_le_of_sqrt {Y : ℝ} {a : ℤ} (ha : 1 ≤ a)
    (h : (a : ℝ) ≤ Real.sqrt (Y / 3)) : 3 * (a : ℝ) ^ 2 ≤ Y := by
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := by
    have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  have hs : (0 : ℝ) ≤ Real.sqrt (Y / 3) := Real.sqrt_nonneg _
  have hY3 : (0 : ℝ) ≤ Y / 3 := by
    by_contra hc
    rw [Real.sqrt_eq_zero_of_nonpos (by linarith : Y / 3 ≤ 0)] at h
    have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  have hsq : Real.sqrt (Y / 3) ^ 2 = Y / 3 := Real.sq_sqrt hY3
  nlinarith

/-- `exists_weighted_areaF_sum_le` with its hypothesis discharged from
`integral_areaF`: the two state the same integral bound, one writing `π / 108`
where the other writes `beta`, and those are definitionally equal. -/
theorem exists_weighted_areaF_sum_le_unconditional :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 2 ≤ Y →
      ∑ a ∈ Finset.Icc 1 ⌊Real.sqrt (Y / 3)⌋₊, (weight (a : ℤ) : ℝ) / 6 * areaF Y (a : ℝ)
        ≤ Real.pi / 108 * (Y * Real.sqrt Y) + C * (Y * Real.log Y) := by
  refine exists_weighted_areaF_sum_le ?_
  intro Y hY
  have h := integral_areaF hY
  unfold beta at h
  exact h

/-- `class_average` with both of its hypotheses discharged: for every `ε > 0`,
the class numbers of the admissible discriminants up to `Y` sum to at most
`(beta + ε) * Y √Y` once `Y` is large enough. -/
theorem class_average_unconditional :
    ∀ ε : ℝ, 0 < ε → ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      ∑ D ∈ admissible Y, (classNumber (D : ℤ) : ℝ) ≤ (beta + ε) * (Y * Real.sqrt Y) := by
  refine class_average ?_ exists_weighted_areaF_sum_le_unconditional
  obtain ⟨C, hC, hbound⟩ := exists_const_card_pairs_le
  refine ⟨C, hC, fun Y hY a ha hsqrt => ?_⟩
  exact hbound Y hY a ha (three_sq_le_of_sqrt ha hsqrt)

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# The Möbius series at two

The unrestricted series is

`∑_n μ(n) / n² = 1 / ζ(2) = 6 / π²`,

which comes from Mathlib: `LSeries_one_mul_Lseries_moebius` gives
`ζ(s) · L(μ,s) = 1` for `1 < re s`, and `riemannZeta_two` evaluates `ζ(2)`.

Restricting to the `n` coprime to `6` needs no Euler-product machinery: every
square-free `n` factors uniquely as `n = e * m` with `e` supported on `{2, 3}`
and `gcd (m, 6) = 1`, and `μ` is multiplicative on coprimes, so

`∑ₙ μ(n)/n² = (∑_{e ∣ 6} μ(e)/e²) * (∑_{(m,6)=1} μ(m)/m²)`.

The first factor is `(1 - 2⁻²)(1 - 3⁻²) = 2/3`, so the restricted sum is
`(6/π²) / (2/3) = 9/π²`. That value is the Euler product
`∏_{p ≥ 5} (1 - p⁻²) = 9 / π²` written as a series.

## Main definitions

* `PartitionZheng.coprimeSummand` — `μ(m)/m²` on the `m` coprime to `6`.

## Main results

* `PartitionZheng.moebius_lseries_two` — `L(μ, 2) = 6 / π²`.
* `PartitionZheng.summable_moebius_div_sq` — real summability.
* `PartitionZheng.moebius_tsum_real` — `∑ₙ μ(n)/n² = 6/π²` over `ℝ`.
* `PartitionZheng.coprime_moebius_tsum` — `∑_{(m,6)=1} μ(m)/m² = 9/π²`.
-/


namespace PartitionZheng

open Real Complex

/-- `1 < re 2`, the summability side condition of the Dirichlet identities. -/
private lemma one_lt_re_two : (1 : ℝ) < ((2 : ℂ)).re := by
  norm_num

/-- The Möbius `L`-series at `2` is `6 / π²`, i.e. `1 / ζ(2)`. -/
theorem moebius_lseries_two :
    LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) 2 = 6 / (Real.pi : ℂ) ^ 2 := by
  have hπ : ((Real.pi : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := LSeries_one_mul_Lseries_moebius one_lt_re_two
  rw [LSeries_one_eq_riemannZeta one_lt_re_two, riemannZeta_two] at h
  -- `h : (π : ℂ) ^ 2 / 6 * L(μ, 2) = 1`
  field_simp at h
  field_simp
  linear_combination h

/-- The Euler factor at `2` and `3`: `∑_{e ∣ 6} μ(e) / e² = 2/3`.

Equivalently `(1 - 2⁻²)(1 - 3⁻²) = (3/4)(8/9) = 2/3`. It is the constant relating
the unrestricted series to its restriction to the `n` coprime to `6`:
`(2/3) · (9/π²) = 6/π²`. -/
theorem moebius_factor_six :
    ∑ e ∈ Nat.divisors 6, (ArithmeticFunction.moebius e : ℚ) / (e : ℚ) ^ 2 = 2 / 3 := by
  have h6 : Nat.divisors 6 = {1, 2, 3, 6} := by decide
  have hmu6 : ArithmeticFunction.moebius 6 = 1 := by
    have h23 : (6 : ℕ) = 2 * 3 := by norm_num
    rw [h23, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by decide),
      ArithmeticFunction.moebius_apply_prime Nat.prime_two,
      ArithmeticFunction.moebius_apply_prime Nat.prime_three]
    norm_num
  rw [h6]
  simp [ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three, hmu6]
  norm_num

/-- Consistency of the two constants: `(2/3) * (9/π²) = 6/π²`. -/
theorem factor_six_consistent :
    (2 / 3 : ℝ) * (9 / Real.pi ^ 2) = 6 / Real.pi ^ 2 := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- `μ (p ^ e) = 0` for `e ≥ 2`: `p ^ e` is not square-free. -/
theorem moebius_prime_pow_eq_zero {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) :
    ArithmeticFunction.moebius (p ^ e) = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro hsf
  have hdvd : p * p ∣ p ^ e := by
    have : p ^ 2 ∣ p ^ e := pow_dvd_pow p he
    simpa [pow_two] using this
  have := hsf p hdvd
  exact hp.one_lt.ne' (Nat.isUnit_iff.mp this)

/-- The local Euler factor of the Möbius series at a prime `p`:
`∑_e μ(p^e) / (p^e)² = 1 - p⁻²`. Only `e = 0` and `e = 1` contribute, since
`p^e` is not square-free beyond that. -/
theorem local_factor {p : ℕ} (hp : p.Prime) :
    ∑' e : ℕ, (ArithmeticFunction.moebius (p ^ e) : ℝ) / ((p : ℝ) ^ e) ^ 2
      = 1 - ((p : ℝ) ^ 2)⁻¹ := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp.pos
  -- the summand vanishes for `e ≥ 2`, so the series is a two-term sum
  have hzero : ∀ e, 2 ≤ e →
      (ArithmeticFunction.moebius (p ^ e) : ℝ) / ((p : ℝ) ^ e) ^ 2 = 0 := by
    intro e he
    rw [moebius_prime_pow_eq_zero hp he]
    simp
  have hHS : HasSum (fun e : ℕ => (ArithmeticFunction.moebius (p ^ e) : ℝ) / ((p : ℝ) ^ e) ^ 2)
      (∑ e ∈ ({0, 1} : Finset ℕ),
        (ArithmeticFunction.moebius (p ^ e) : ℝ) / ((p : ℝ) ^ e) ^ 2) := by
    refine hasSum_sum_of_ne_finset_zero ?_
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
    exact hzero b (by omega)
  rw [hHS.tsum_eq, Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [pow_zero, pow_one, ArithmeticFunction.moebius_apply_one,
    ArithmeticFunction.moebius_apply_prime hp]
  have hpne : ((p : ℝ)) ≠ 0 := ne_of_gt hp0
  field_simp
  push_cast
  ring

/-- `|μ n| ≤ 1`: the Möbius function takes values in `{-1, 0, 1}`. -/
theorem abs_moebius_le_one (n : ℕ) :
    |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
  rcases eq_or_ne (ArithmeticFunction.moebius n) 0 with h | h
  · rw [h]; norm_num
  · rcases ArithmeticFunction.moebius_ne_zero_iff_eq_or.mp h with h1 | h1 <;>
      rw [h1] <;> norm_num

/-- The Möbius series at `2` is summable over the reals, by comparison with
`∑ 1/n²`. -/
theorem summable_moebius_div_sq :
    Summable (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2) := by
  have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow).mpr (by norm_num)
  refine hp.of_norm_bounded ?_
  intro n
  rw [Real.norm_eq_abs, abs_div]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsq : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    rw [abs_of_pos hsq, one_div]
    rw [div_le_iff₀ hsq]
    have := abs_moebius_le_one n
    calc |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := this
      _ = ((n : ℝ) ^ 2)⁻¹ * (n : ℝ) ^ 2 := by
          field_simp

/-- **The Möbius series at two, over the reals.** `∑ₙ μ(n)/n² = 6/π²`.

The real series and the `L`-series agree termwise with no special case at
`n = 0`: `LSeries.term` is `0` there by definition, and on the real side
`μ 0 = 0` makes the term `0 / 0`, which Lean evaluates to `0`. -/
theorem moebius_tsum_real :
    ∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2
      = 6 / Real.pi ^ 2 := by
  have hsum := summable_moebius_div_sq
  -- push the real `HasSum` into `ℂ`
  have hC : HasSum (fun n : ℕ =>
      ((((ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 : ℝ)) : ℂ))
      (((∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 : ℝ)) : ℂ) :=
    hsum.hasSum.map (Complex.ofRealHom : ℝ →+* ℂ).toAddMonoidHom
      Complex.continuous_ofReal
  -- termwise it is the `L`-series summand at `s = 2`
  have hterm : ∀ n : ℕ,
      ((((ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 : ℝ)) : ℂ)
        = LSeries.term (fun m => (ArithmeticFunction.moebius m : ℂ)) 2 n := by
    intro n
    rw [LSeries.term_def]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · rw [if_neg (by omega : ¬ (n = 0))]
      -- the `L`-series exponent is a `cpow`; convert it to a monoid power
      have hcast : ((n : ℂ)) ^ (2 : ℂ) = ((n : ℂ)) ^ (2 : ℕ) := by
        rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
      rw [hcast]
      push_cast
      ring
  have hC' : HasSum (LSeries.term (fun m => (ArithmeticFunction.moebius m : ℂ)) 2)
      (((∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 : ℝ)) : ℂ) := by
    simpa only [hterm] using hC
  -- so the real sum casts to `L(μ, 2) = 6/π²`
  have hval := hC'.tsum_eq
  rw [← LSeries, moebius_lseries_two] at hval
  have hre : (((∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 : ℝ)) : ℂ)
      = ((6 / Real.pi ^ 2 : ℝ) : ℂ) := by
    rw [← hval]; push_cast; ring
  exact_mod_cast hre

/-- The Euler factor at `2` and `3`, over the reals: `∑_{e ∣ 6} μ(e)/e² = 2/3`.
The `ℚ` version is `moebius_factor_six`. -/
theorem moebius_factor_six_real :
    ∑ e ∈ Nat.divisors 6, (ArithmeticFunction.moebius e : ℝ) / (e : ℝ) ^ 2 = 2 / 3 := by
  have h6 : Nat.divisors 6 = {1, 2, 3, 6} := by decide
  have hmu6 : ArithmeticFunction.moebius 6 = 1 := by
    have h23 : (6 : ℕ) = 2 * 3 := by norm_num
    rw [h23, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by decide),
      ArithmeticFunction.moebius_apply_prime Nat.prime_two,
      ArithmeticFunction.moebius_apply_prime Nat.prime_three]
    norm_num
  rw [h6]
  simp [ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three, hmu6]
  norm_num

/- ### The coprime decomposition `n = e * m`, `e ∣ 6`, `gcd (m, 6) = 1`

The arithmetic behind the factorization
`∑ₙ μ(n)/n² = (∑_{e ∣ 6} μ(e)/e²) * (∑_{(m,6)=1} μ(m)/m²)`: the decomposition
exists on the support of `μ`, it is unique, and the two factors are coprime so
`μ` splits across it. -/

/-- A divisor of `6` is coprime to anything coprime to `6`. -/
theorem coprime_of_dvd_six {e m : ℕ} (he : e ∣ 6) (hm : Nat.Coprime m 6) :
    Nat.Coprime e m := by
  have h1 : Nat.gcd e m ∣ 6 := dvd_trans (Nat.gcd_dvd_left e m) he
  have h2 : Nat.gcd e m ∣ m := Nat.gcd_dvd_right e m
  have h3 : Nat.gcd e m ∣ Nat.gcd m 6 := Nat.dvd_gcd h2 h1
  rw [hm] at h3
  exact Nat.dvd_one.mp h3

/-- The decomposition is unique: the `{2,3}`-part and the coprime part are each
determined. -/
theorem six_part_unique {e₁ e₂ m₁ m₂ : ℕ} (he₁ : e₁ ∣ 6) (he₂ : e₂ ∣ 6)
    (hm₁ : Nat.Coprime m₁ 6) (hm₂ : Nat.Coprime m₂ 6)
    (hp₁ : 0 < e₁) (h : e₁ * m₁ = e₂ * m₂) : e₁ = e₂ ∧ m₁ = m₂ := by
  have hc12 : Nat.Coprime e₁ m₂ := coprime_of_dvd_six he₁ hm₂
  have hc21 : Nat.Coprime e₂ m₁ := coprime_of_dvd_six he₂ hm₁
  have hd1 : e₁ ∣ e₂ := by
    have hdd : e₁ ∣ e₂ * m₂ := h ▸ (Dvd.intro m₁ rfl)
    exact hc12.dvd_of_dvd_mul_right hdd
  have hd2 : e₂ ∣ e₁ := by
    have hdd : e₂ ∣ e₁ * m₁ := h ▸ (Dvd.intro m₂ rfl)
    exact hc21.dvd_of_dvd_mul_right hdd
  have hee : e₁ = e₂ := Nat.dvd_antisymm hd1 hd2
  refine ⟨hee, ?_⟩
  rw [hee] at h
  exact Nat.eq_of_mul_eq_mul_left (by omega) h

/-- **The decomposition exists** on the support of `μ`: a square-free `n`
factors as `e * m` with `e ∣ 6` and `gcd (m, 6) = 1`, namely `e = gcd (n, 6)`.

Square-freeness is what makes this work — for `n = 4` the `{2,3}`-part is `4`,
not a divisor of `6`. That is harmless because `μ` vanishes there. -/
theorem exists_six_decomp {n : ℕ} (hsf : Squarefree n) :
    ∃ e m : ℕ, e ∣ 6 ∧ Nat.Coprime m 6 ∧ n = e * m := by
  set g : ℕ := Nat.gcd n 6 with hg
  have hgn : g ∣ n := Nat.gcd_dvd_left n 6
  have hg6 : g ∣ 6 := Nat.gcd_dvd_right n 6
  refine ⟨g, n / g, hg6, ?_, ?_⟩
  · -- `n / g` is coprime to `6`: a common prime `p` would give `p² ∣ n`
    by_contra hc
    obtain ⟨p, hp, hpk, hp6⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    have hpn : p ∣ n := dvd_trans hpk (Nat.div_dvd_of_dvd hgn)
    have hpg : p ∣ g := Nat.dvd_gcd hpn hp6
    have hsq : p * p ∣ n := by
      have hmul : n / g * g = n := Nat.div_mul_cancel hgn
      calc p * p ∣ (n / g) * g := mul_dvd_mul hpk hpg
        _ = n := hmul
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsf p hsq))
  · exact (Nat.div_mul_cancel hgn).symm ▸ (Nat.mul_div_cancel' hgn).symm

/- ### Reindexing the Möbius series along the decomposition -/

/-- The index type of the coprime decomposition: a divisor of `6` paired with a
natural coprime to `6`. -/
private abbrev SixIdx : Type := ↥(Nat.divisors 6) × {m : ℕ // Nat.Coprime m 6}

/-- The decomposition map `(e, m) ↦ e * m`. -/
private def sixMul (p : SixIdx) : ℕ := p.1.val * p.2.val

/-- `sixMul` is injective, by `six_part_unique`. -/
theorem sixMul_injective : Function.Injective sixMul := by
  rintro ⟨⟨e₁, he₁⟩, ⟨m₁, hm₁⟩⟩ ⟨⟨e₂, he₂⟩, ⟨m₂, hm₂⟩⟩ h
  simp only [sixMul] at h
  have hd₁ : e₁ ∣ 6 := (Nat.mem_divisors.mp he₁).1
  have hd₂ : e₂ ∣ 6 := (Nat.mem_divisors.mp he₂).1
  have hp₁ : 0 < e₁ := Nat.pos_of_mem_divisors he₁
  obtain ⟨hee, hmm⟩ := six_part_unique hd₁ hd₂ hm₁ hm₂ hp₁ h
  subst hee
  subst hmm
  rfl

/-- Off the range of `sixMul` the Möbius summand vanishes: such an `n` is not
square-free, since `exists_six_decomp` decomposes every square-free number. -/
theorem moebius_div_sq_eq_zero_of_notMem_range {n : ℕ} (h : n ∉ Set.range sixMul) :
    (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 = 0 := by
  by_cases hmu : ArithmeticFunction.moebius n = 0
  · rw [hmu]; simp
  · -- `μ n ≠ 0` makes `n` square-free, so it decomposes and lies in the range
    exfalso
    have hsf : Squarefree n := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu
    obtain ⟨e, m, he, hm, hnem⟩ := exists_six_decomp hsf
    refine h ⟨⟨⟨e, Nat.mem_divisors.mpr ⟨he, by norm_num⟩⟩, ⟨m, hm⟩⟩, ?_⟩
    simpa [sixMul] using hnem.symm

/-- **The tail bound.** Beyond `M` the Möbius series contributes at most
`2/(M+1)` in absolute value, since `|μ| ≤ 1` and `∑_{d > M} d⁻² ≤ 2/(M+1)`. The
constant is explicit rather than an `O()`. -/
theorem moebius_tail_le (M N : ℕ) :
    |∑ d ∈ Finset.Ioo M N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2|
      ≤ 2 / (M + 1) := by
  calc |∑ d ∈ Finset.Ioo M N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2|
      ≤ ∑ d ∈ Finset.Ioo M N, |(ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Ioo M N, (((d : ℝ)) ^ 2)⁻¹ := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hd1 : 1 ≤ d := by
          have := (Finset.mem_Ioo.mp hd).1
          omega
        have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
        have hsq : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
        rw [abs_div, abs_of_pos hsq, ← one_div, div_le_div_iff₀ hsq hsq]
        nlinarith [abs_moebius_le_one d]
    _ ≤ 2 / (M + 1) := sum_Ioo_inv_sq_le M N

/-- The summand `μ(m)/m²` restricted to the naturals coprime to `6`. -/
private noncomputable def coprimeSummand (m : {m : ℕ // Nat.Coprime m 6}) : ℝ :=
  (ArithmeticFunction.moebius m.val : ℝ) / (m.val : ℝ) ^ 2

/-- **`lem_euler_prod`.** `∑_{(m,6)=1} μ(m)/m² = 9/π²`.

Equivalently, the Euler product `∏_{p ≥ 5} (1 - p⁻²) = 9/π²`, reached here
without any Euler-product machinery: every square-free `n` factors uniquely as
`n = e * m` with `e ∣ 6` and `gcd (m, 6) = 1` (`exists_six_decomp`,
`six_part_unique`), the two factors are coprime so `μ` splits
(`coprime_of_dvd_six`), and reindexing the full series along that decomposition
gives

`6/π² = (∑_{e ∣ 6} μ(e)/e²) * (∑_{(m,6)=1} μ(m)/m²) = (2/3) * S`,

whence `S = 9/π²`. -/
theorem coprime_moebius_tsum :
    ∑' m : {m : ℕ // Nat.Coprime m 6}, coprimeSummand m = 9 / Real.pi ^ 2 := by
  classical
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  -- the full series, as a `HasSum`
  have hfull : HasSum (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2)
      (6 / Real.pi ^ 2) := by
    have h := summable_moebius_div_sq.hasSum
    rwa [moebius_tsum_real] at h
  -- reindex along the decomposition
  have hcomp : HasSum
      ((fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2) ∘ sixMul)
      (6 / Real.pi ^ 2) :=
    (sixMul_injective.hasSum_iff
      (fun x hx => moebius_div_sq_eq_zero_of_notMem_range hx)).mpr hfull
  -- the reindexed summand factors
  have hfac : ∀ p : SixIdx,
      ((fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2) ∘ sixMul) p
        = ((ArithmeticFunction.moebius p.1.val : ℝ) / (p.1.val : ℝ) ^ 2)
          * coprimeSummand p.2 := by
    rintro ⟨⟨e, he⟩, ⟨m, hm⟩⟩
    have hd : e ∣ 6 := (Nat.mem_divisors.mp he).1
    have hcop : Nat.Coprime e m := coprime_of_dvd_six hd hm
    simp only [Function.comp_apply, sixMul, coprimeSummand]
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]
    push_cast
    ring
  -- so the product-indexed sum splits
  have hsummable : Summable
      (fun p : SixIdx => ((ArithmeticFunction.moebius p.1.val : ℝ) / (p.1.val : ℝ) ^ 2)
        * coprimeSummand p.2) := by
    have := hcomp.summable
    rwa [funext hfac] at this
  have htot : ∑' p : SixIdx, ((ArithmeticFunction.moebius p.1.val : ℝ) / (p.1.val : ℝ) ^ 2)
      * coprimeSummand p.2 = 6 / Real.pi ^ 2 := by
    have := hcomp.tsum_eq
    rwa [funext hfac] at this
  -- split the product sum, pull the constant out of the inner sum
  rw [hsummable.tsum_prod] at htot
  have hinner : ∀ e : ↥(Nat.divisors 6),
      ∑' m : {m : ℕ // Nat.Coprime m 6},
          ((ArithmeticFunction.moebius e.val : ℝ) / (e.val : ℝ) ^ 2) * coprimeSummand m
        = ((ArithmeticFunction.moebius e.val : ℝ) / (e.val : ℝ) ^ 2)
          * ∑' m : {m : ℕ // Nat.Coprime m 6}, coprimeSummand m := by
    intro e
    exact tsum_mul_left
  rw [tsum_congr hinner, tsum_fintype, ← Finset.sum_mul] at htot
  -- the finite factor is `2/3`
  have hfactor : ∑ e : ↥(Nat.divisors 6),
      (ArithmeticFunction.moebius e.val : ℝ) / (e.val : ℝ) ^ 2 = 2 / 3 := by
    rw [← moebius_factor_six_real]
    exact Finset.sum_coe_sort (Nat.divisors 6)
      (fun e => (ArithmeticFunction.moebius e : ℝ) / (e : ℝ) ^ 2)
  rw [hfactor] at htot
  -- `(2/3) * S = 6/π²`
  have hS : (2 / 3 : ℝ) * ∑' m : {m : ℕ // Nat.Coprime m 6}, coprimeSummand m
      = 6 / Real.pi ^ 2 := htot
  field_simp at hS ⊢
  linarith [hS]

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# The square-free indicator as a Möbius sum

`∑_{d² ∣ N} μ(d) = 1` when `N` is square-free and `0` otherwise. Mathlib has
`μ n ^ 2 = if Squarefree n then 1 else 0` but not this sum form, which is what
the count of admissible discriminants inserts and then swaps.

The proof goes through `P = ∏ {p prime : p² ∣ N} p`. Only square-free `d`
contribute to the sum, and for square-free `d` the conditions `d² ∣ N` and
`d ∣ P` agree — both say `d.factorization p ≤ 1` exactly where `p² ∣ N`. So the
sum collapses to `∑_{d ∣ P} μ d`, which is `1` iff `P = 1`, which is iff `N` is
square-free.

## Main results

* `PartitionZheng.sum_moebius_divisors` — `∑_{d ∣ n} μ d = if n = 1 then 1 else 0`.
* `PartitionZheng.sqfree_indicator` — the identity.
-/


namespace PartitionZheng

open ArithmeticFunction Finset
-- the `μ` notation is scoped to the NESTED namespace, not to `ArithmeticFunction`
open scoped ArithmeticFunction.Moebius

/-- `∑_{d ∣ n} μ d = 1` if `n = 1` and `0` otherwise: the Dirichlet convolution
`μ * ζ = 1` read off pointwise. -/
theorem sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, μ d = if n = 1 then 1 else 0 := by
  -- Rewrite the goal's own left side into `(μ * ζ) n` and collapse it; this
  -- never names ζ (its notation is scoped elsewhere again) and never risks simp
  -- flattening the hypothesis to `True`.
  rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply]

/-- The product of the primes whose square divides `N`. -/
private def sqPrimes (N : ℕ) : ℕ := ∏ p ∈ N.primeFactors with p ^ 2 ∣ N, p

/-- `sqPrimes N = 1` exactly when `N` is square-free. -/
theorem sqPrimes_eq_one_iff {N : ℕ} (hN : N ≠ 0) :
    sqPrimes N = 1 ↔ Squarefree N := by
  classical
  rw [Nat.squarefree_iff_factorization_le_one hN]
  constructor
  · intro h p
    by_contra hc
    have h2 : 2 ≤ N.factorization p := by omega
    have hp : p.Prime := by
      by_contra hnp
      rw [Nat.factorization_eq_zero_of_not_prime N hnp] at h2
      omega
    have hpd : p ∣ N := Nat.dvd_of_factorization_pos (by omega)
    have hmem : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, hN⟩
    have hsq : p ^ 2 ∣ N := (Nat.Prime.pow_dvd_iff_le_factorization hp hN).mpr h2
    have : p ∈ N.primeFactors.filter (fun q => q ^ 2 ∣ N) :=
      Finset.mem_filter.mpr ⟨hmem, hsq⟩
    have hdvd : p ∣ sqPrimes N := Finset.dvd_prod_of_mem _ this
    rw [h] at hdvd
    exact hp.one_lt.ne' (Nat.dvd_one.mp hdvd)
  · intro h
    have : N.primeFactors.filter (fun q => q ^ 2 ∣ N) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr ?_
      intro p hmem hsq
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hmem
      have := (Nat.Prime.pow_dvd_iff_le_factorization hp hN).mp hsq
      have := h p
      omega
    rw [sqPrimes, this, Finset.prod_empty]

/-- The factorization of `sqPrimes N`: exponent `1` at each prime whose square
divides `N`, and `0` elsewhere. -/
theorem sqPrimes_factorization (N q : ℕ) :
    (sqPrimes N).factorization q =
      if q ∈ N.primeFactors.filter (fun p => p ^ 2 ∣ N) then 1 else 0 := by
  classical
  have hne : ∀ p ∈ N.primeFactors.filter (fun p => p ^ 2 ∣ N), p ≠ 0 := by
    intro p hp
    exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero
  rw [sqPrimes, Nat.factorization_prod hne]
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (fun p hp => by
    rw [(Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).factorization,
      Finsupp.single_apply])]
  by_cases hq : q ∈ N.primeFactors.filter (fun p => p ^ 2 ∣ N)
  · rw [if_pos hq, Finset.sum_eq_single q]
    · simp
    · intro b _ hbq; exact if_neg hbq
    · intro h; exact absurd hq h
  · rw [if_neg hq, Finset.sum_eq_zero]
    intro b hb
    have : b ≠ q := fun hc => hq (hc ▸ hb)
    simp [this]

/-- For square-free `d`, the conditions `d ^ 2 ∣ N` and `d ∣ sqPrimes N` agree:
both say `d.factorization p ≤ 1` exactly where `p ^ 2 ∣ N`. -/
theorem sq_dvd_iff_dvd_sqPrimes {N d : ℕ} (hN : N ≠ 0) (hd : d ≠ 0)
    (hdsq : Squarefree d) : d ^ 2 ∣ N ↔ d ∣ sqPrimes N := by
  classical
  have hsp : sqPrimes N ≠ 0 := by
    rw [sqPrimes]
    exact Finset.prod_ne_zero_iff.mpr (fun p hp =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero)
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero 2 hd) hN,
    ← Nat.factorization_le_iff_dvd hd hsp]
  constructor
  · intro h p
    rw [sqPrimes_factorization]
    have h2 : 2 * d.factorization p ≤ N.factorization p := by
      have := h p
      rwa [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at this
    have hle1 : d.factorization p ≤ 1 :=
      (Nat.squarefree_iff_factorization_le_one hd).mp hdsq p
    by_cases hmem : p ∈ N.primeFactors.filter (fun r => r ^ 2 ∣ N)
    · rw [if_pos hmem]; exact hle1
    · rw [if_neg hmem]
      by_contra hc
      have hdp : 1 ≤ d.factorization p := by omega
      have hp : p.Prime := Nat.prime_of_mem_primeFactors
        (Nat.mem_primeFactors.mpr ⟨by
          by_contra hnp
          rw [Nat.factorization_eq_zero_of_not_prime d hnp] at hdp; omega,
          Nat.dvd_of_factorization_pos (by omega), hd⟩)
      have hpN : p ^ 2 ∣ N := (Nat.Prime.pow_dvd_iff_le_factorization hp hN).mpr (by omega)
      exact hmem (Finset.mem_filter.mpr
        ⟨Nat.mem_primeFactors.mpr ⟨hp, dvd_trans (dvd_pow_self p two_ne_zero) hpN, hN⟩, hpN⟩)
  · intro h p
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    have hsp' := h p
    rw [sqPrimes_factorization] at hsp'
    by_cases hmem : p ∈ N.primeFactors.filter (fun r => r ^ 2 ∣ N)
    · rw [if_pos hmem] at hsp'
      have hpN : p ^ 2 ∣ N := (Finset.mem_filter.mp hmem).2
      have hp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hmem).1
      have : 2 ≤ N.factorization p := (Nat.Prime.pow_dvd_iff_le_factorization hp hN).mp hpN
      omega
    · rw [if_neg hmem] at hsp'
      omega

/-- `sqPrimes N` is square-free: its factorization is `0` or `1` everywhere. -/
theorem sqPrimes_squarefree (N : ℕ) : Squarefree (sqPrimes N) := by
  classical
  have hsp : sqPrimes N ≠ 0 := by
    rw [sqPrimes]
    exact Finset.prod_ne_zero_iff.mpr (fun p hp =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero)
  rw [Nat.squarefree_iff_factorization_le_one hsp]
  intro p
  rw [sqPrimes_factorization]
  split <;> norm_num

/-- **The square-free indicator as a Möbius sum.** For `N ≠ 0`,
`∑_{d ∣ N, d² ∣ N} μ d = 1` when `N` is square-free and `0` otherwise. -/
theorem sqfree_indicator {N : ℕ} (hN : N ≠ 0) :
    ∑ d ∈ N.divisors with d ^ 2 ∣ N, μ d = if Squarefree N then 1 else 0 := by
  classical
  have hsp : sqPrimes N ≠ 0 := by
    rw [sqPrimes]
    exact Finset.prod_ne_zero_iff.mpr (fun p hp =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero)
  -- Only square-free `d` contribute, and those are exactly the divisors of
  -- `sqPrimes N`.
  have hset : (N.divisors.filter fun d => d ^ 2 ∣ N).filter (fun d => Squarefree d)
      = (sqPrimes N).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨hdN, -⟩, hdsq⟩, hsf⟩
      exact ⟨(sq_dvd_iff_dvd_sqPrimes hN (by rintro rfl; simp at hdN; omega) hsf).mp hdsq, hsp⟩
    · rintro ⟨hdvd, -⟩
      have hd0 : d ≠ 0 := by rintro rfl; exact hsp (Nat.eq_zero_of_zero_dvd hdvd)
      have hsf : Squarefree d := (sqPrimes_squarefree N).squarefree_of_dvd hdvd
      have hdsq : d ^ 2 ∣ N := (sq_dvd_iff_dvd_sqPrimes hN hd0 hsf).mpr hdvd
      exact ⟨⟨⟨dvd_trans (dvd_pow_self d two_ne_zero) hdsq, hN⟩, hdsq⟩, hsf⟩
  -- Discard the non-square-free terms, on which `μ` vanishes.
  have hdrop : ∑ d ∈ (N.divisors.filter fun d => d ^ 2 ∣ N).filter (fun d => Squarefree d), μ d
      = ∑ d ∈ N.divisors.filter fun d => d ^ 2 ∣ N, μ d := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro x _ hx
    by_contra hne
    exact hx (Finset.mem_filter.mpr ⟨‹_›, moebius_ne_zero_iff_squarefree.mp hne⟩)
  rw [← hdrop, hset, sum_moebius_divisors]
  -- Rewriting `sqPrimes N = 1` into `Squarefree N` under an `ite` breaks the
  -- motive (the `Decidable` instances differ), so case-split instead.
  by_cases h : Squarefree N
  · rw [if_pos ((sqPrimes_eq_one_iff hN).mpr h), if_pos h]
  · rw [if_neg (fun hc => h ((sqPrimes_eq_one_iff hN).mp hc)), if_neg h]

/-- **The Möbius double-sum exchange.** For any finite set `S` of integers and
any bound `M`,

`∑_{N ∈ S} ∑_{d ≤ M, d² ∣ N} μ(d) = ∑_{d ≤ M} μ(d) · #{N ∈ S : d² ∣ N}`.

This is the swap the count of admissible discriminants performs after inserting
`sqfree_indicator`: the left side counts square-free `N` one at a time, the
right side groups by the square divisor. It is pure double counting — the
condition `d² ∣ N` is symmetric in the two summation variables, so
`Finset.sum_comm` applies once both filters are turned into `ite`s.

Stating it over an explicit `Finset.range (M+1)` rather than `N.divisors` is
what makes the exchange possible at all: the divisor set depends on `N`, so the
inner index set would otherwise vary with the outer variable. -/
theorem sum_moebius_swap (S : Finset ℕ) (M : ℕ) :
    ∑ N ∈ S, ∑ d ∈ (Finset.range (M + 1)).filter (fun d => d ^ 2 ∣ N),
        (μ d : ℝ)
      = ∑ d ∈ Finset.range (M + 1), (μ d : ℝ)
          * (((S.filter fun N => d ^ 2 ∣ N)).card : ℝ) := by
  classical
  -- turn both filters into `ite`s so the index sets no longer depend on each other
  have hL : ∀ N : ℕ, ∑ d ∈ (Finset.range (M + 1)).filter (fun d => d ^ 2 ∣ N), (μ d : ℝ)
      = ∑ d ∈ Finset.range (M + 1), if d ^ 2 ∣ N then (μ d : ℝ) else 0 := by
    intro N; rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl fun N _ => hL N, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  -- the inner sum is `μ d` on the fibre and `0` off it
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# Counting the admissible discriminants

`|#D(Y) - δY| ≤ C√Y` with `δ = 3/(8π²)` and the explicit constant `C = 7`. The
argument inserts `sqfree_indicator` to turn the square-free condition into a
divisor sum, swaps the order of summation, counts each inner residue class, and
evaluates the resulting series.

## Main definitions

* `PartitionZheng.mainTerm` — the per-`d` main term `(⌊Y⌋₊ / d²) / 24`.
* `PartitionZheng.mainTermReal` — the same with both roundings removed.
* `PartitionZheng.coprimeTerm` — `μ(d)/d²` on the `d` coprime to `6`, else `0`.

## Main results

* `PartitionZheng.card_admissible_eq_sum` — the count as a Möbius double sum.
* `PartitionZheng.card_admissible_eq_swapped` — the count with the sums swapped.
* `PartitionZheng.card_admissible_sub_mainSum_le` — the count against its main
  sum.
* `PartitionZheng.card_admissible_sub_delta_le` — `|#D(Y) - δY| ≤ 7√Y`.
-/


namespace PartitionZheng

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

/-- The admissible discriminants are the square-free elements of the residue
class, so `#D(Y)` is the double sum obtained from `sqfree_indicator`. -/
theorem card_admissible_eq_sum (Y : ℝ) :
    ((admissible Y).card : ℝ)
      = ∑ N ∈ (Finset.Icc 2 ⌊Y⌋₊).filter (fun N : ℕ => N % 24 = 23),
          ∑ d ∈ N.divisors.filter (fun d => d ^ 2 ∣ N), (μ d : ℝ) := by
  classical
  -- split the two conditions of `admissible`
  have hset : admissible Y
      = ((Finset.Icc 2 ⌊Y⌋₊).filter fun N : ℕ => N % 24 = 23).filter
          (fun N => Squarefree N) := by
    unfold admissible
    rw [Finset.filter_filter]
  rw [hset, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun N hN => ?_
  -- `N ≥ 2`, so `sqfree_indicator` applies
  have hN0 : N ≠ 0 := by
    have h1 := (Finset.mem_filter.mp hN).1
    have h2 := Finset.mem_Icc.mp h1
    omega
  have hZ := sqfree_indicator hN0
  have hcast : ∑ d ∈ N.divisors.filter (fun d => d ^ 2 ∣ N), (μ d : ℝ)
      = (((∑ d ∈ N.divisors.filter (fun d => d ^ 2 ∣ N), μ d : ℤ)) : ℝ) := by
    push_cast; ring
  rw [hcast, hZ]
  split <;> norm_num

/-- The inner index set may be taken to be a fixed range. For `N ≤ M²` the
divisors `d` with `d² ∣ N` are exactly the `d ≤ M` with `d² ∣ N`, since
`d² ∣ N` forces `d² ≤ N ≤ M²`.

Over `N.divisors` the inner index set depends on `N`, so the order of summation
cannot be exchanged; over a fixed range it can. -/
theorem divisor_filter_eq_range {N M : ℕ} (hN : N ≠ 0) (hM : N ≤ M ^ 2) :
    N.divisors.filter (fun d => d ^ 2 ∣ N)
      = (Finset.range (M + 1)).filter (fun d => d ^ 2 ∣ N) := by
  classical
  ext d
  simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨-, -⟩, hsq⟩
    refine ⟨?_, hsq⟩
    -- `d² ∣ N` gives `d² ≤ N ≤ M²`, hence `d ≤ M`
    have hle : d ^ 2 ≤ N := Nat.le_of_dvd (by omega) hsq
    by_contra hc
    have hMd : M < d := by omega
    have : M ^ 2 < d ^ 2 := Nat.pow_lt_pow_left hMd (by norm_num)
    omega
  · rintro ⟨-, hsq⟩
    have hd0 : d ≠ 0 := by
      rintro rfl
      simp only [pow_two, Nat.mul_zero] at hsq
      exact hN (Nat.eq_zero_of_zero_dvd hsq)
    exact ⟨⟨dvd_trans (dvd_pow_self d two_ne_zero) hsq, hN⟩, hsq⟩

/-- **The fibre over `d`.** For `d ≥ 1` coprime to `6`, the `N ≤ M` in the class
`23` modulo `24` divisible by `d²` correspond bijectively, via `N = d² r`, to the
`r ≤ M / d²` in the class `23` modulo `24`.

The lower bound `2 ≤ N` of `admissible` is automatic here and costs nothing:
`N ≡ 23 [MOD 24]` already forces `N ≥ 23`. -/
theorem fibre_card {M d : ℕ} (hd : 1 ≤ d) (h2 : ¬ (2 ∣ d)) (h3 : ¬ (3 ∣ d)) :
    (((Finset.Icc 2 M).filter fun N => N % 24 = 23).filter (fun N => d ^ 2 ∣ N)).card
      = ((Finset.Icc 1 (M / d ^ 2)).filter fun r => r % 24 = 23).card := by
  classical
  have hd2 : 0 < d ^ 2 := pow_pos hd 2
  refine Finset.card_bij' (fun N _ => N / d ^ 2) (fun r _ => d ^ 2 * r) ?_ ?_ ?_ ?_
  · -- `N ↦ N / d²` lands in the `r`-set
    intro N hN
    obtain ⟨hN1, hdvd⟩ := Finset.mem_filter.mp hN
    obtain ⟨hNIcc, hN23⟩ := Finset.mem_filter.mp hN1
    obtain ⟨-, hNM⟩ := Finset.mem_Icc.mp hNIcc
    obtain ⟨k, hk⟩ := hdvd
    have hkey : N / d ^ 2 = k := by rw [hk]; exact Nat.mul_div_cancel_left k hd2
    have hk23 : k % 24 = 23 := by
      rw [hk] at hN23; exact (dsq_mul_emod_24_nat h2 h3).mp hN23
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · change 1 ≤ N / d ^ 2
      rw [hkey]; omega
    · rw [hkey, Nat.le_div_iff_mul_le hd2, Nat.mul_comm]
      rw [hk] at hNM
      exact hNM
    · rw [hkey]; exact hk23
  · -- `r ↦ d² r` lands in the `N`-set
    intro r hr
    obtain ⟨hrIcc, hr23⟩ := Finset.mem_filter.mp hr
    obtain ⟨hr1, hrM⟩ := Finset.mem_Icc.mp hrIcc
    have h23 : (d ^ 2 * r) % 24 = 23 := (dsq_mul_emod_24_nat h2 h3).mpr hr23
    have hle : d ^ 2 * r ≤ M := by
      have hstep : d ^ 2 * r ≤ d ^ 2 * (M / d ^ 2) := Nat.mul_le_mul_left _ hrM
      have hdiv : d ^ 2 * (M / d ^ 2) ≤ M := by
        rw [Nat.mul_comm]; exact Nat.div_mul_le_self M (d ^ 2)
      omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by change 2 ≤ d ^ 2 * r; omega, hle⟩, h23⟩, Dvd.intro r rfl⟩
  · -- `d² * (N / d²) = N`
    intro N hN
    obtain ⟨-, hdvd⟩ := Finset.mem_filter.mp hN
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, Nat.mul_div_cancel_left k hd2]
  · -- `(d² * r) / d² = r`
    intro r _
    exact Nat.mul_div_cancel_left r hd2

/-- **The residue count over `ℕ`, modulus `24`.** For `lo ≤ hi`, the naturals of
`Finset.Icc lo hi` congruent to `r` modulo `24` number at most
`(hi - lo) / 24 + 1`. -/
theorem card_residue_class_Icc_nat24 {lo hi r : ℕ} (hle : lo ≤ hi) :
    ((((Finset.Icc lo hi).filter fun c : ℕ => c % 24 = r)).card : ℝ)
      ≤ ((hi : ℝ) - (lo : ℝ)) / 24 + 1 := by
  classical
  -- inject `c ↦ (c - lo) / 24` into `range ((hi - lo) / 24 + 1)`
  have hkey : ((Finset.Icc lo hi).filter fun c : ℕ => c % 24 = r).card
      ≤ (Finset.range ((hi - lo) / 24 + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun c => (c - lo) / 24) (fun c hc => ?_) ?_
    · obtain ⟨hIcc, -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hc)
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hIcc
      refine Finset.mem_range.mpr ?_
      change (c - lo) / 24 < (hi - lo) / 24 + 1
      omega
    · intro c hc c' hc' h
      simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hc hc'
      obtain ⟨⟨hc1, hc2⟩, hcr⟩ := hc
      obtain ⟨⟨hc1', hc2'⟩, hcr'⟩ := hc'
      simp only at h
      omega
  -- `#range n = n`, and `ℕ`-division is bounded by real division
  have hcard : ((Finset.range ((hi - lo) / 24 + 1)).card : ℝ)
      = (((hi - lo) / 24 : ℕ) : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hdiv : (((hi - lo) / 24 : ℕ) : ℝ) ≤ ((hi : ℝ) - (lo : ℝ)) / 24 := by
    have hz : (24 : ℕ) * ((hi - lo) / 24) ≤ hi - lo := Nat.mul_div_le (hi - lo) 24
    have hzR : (24 : ℝ) * (((hi - lo) / 24 : ℕ) : ℝ) ≤ ((hi - lo : ℕ) : ℝ) := by
      exact_mod_cast hz
    have hsub : ((hi - lo : ℕ) : ℝ) = (hi : ℝ) - (lo : ℝ) := by
      have : (lo : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hle
      push_cast [Nat.cast_sub hle]; ring
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 24)]
    rw [hsub] at hzR
    linarith
  have hmono : ((((Finset.Icc lo hi).filter fun c : ℕ => c % 24 = r)).card : ℝ)
      ≤ ((Finset.range ((hi - lo) / 24 + 1)).card : ℝ) := by exact_mod_cast hkey
  rw [hcard] at hmono
  linarith

/-- **The residue count over `ℕ`, lower bound.** For `r < 24`, the naturals of
`Finset.Icc lo hi` congruent to `r` modulo `24` number at least
`(hi - lo) / 24 - 1`.

The witness is the arithmetic progression starting at the least `lo' ≥ lo` in the
class, namely `lo' = lo + (r + 24 - lo % 24) % 24`, so `lo ≤ lo' ≤ lo + 23`. -/
theorem card_residue_class_Icc_nat24_ge {lo hi r : ℕ} (hr : r < 24) :
    ((hi : ℝ) - (lo : ℝ)) / 24 - 1
      ≤ ((((Finset.Icc lo hi).filter fun c : ℕ => c % 24 = r)).card : ℝ) := by
  classical
  set s : ℕ := (r + 24 - lo % 24) % 24 with hs
  set lo' : ℕ := lo + s with hlo'
  have hslt : s < 24 := by rw [hs]; omega
  have hsr : lo' % 24 = r := by rw [hlo', hs]; omega
  rcases le_or_gt lo' hi with hle' | hgt
  · set n : ℕ := (hi - lo') / 24 + 1 with hn
    have hinjf : Function.Injective (fun j : ℕ => lo' + 24 * j) := by
      intro a b h
      simp only at h
      omega
    have hsub : (Finset.range n).image (fun j : ℕ => lo' + 24 * j)
        ⊆ (Finset.Icc lo hi).filter (fun c : ℕ => c % 24 = r) := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      have hjlt : j < n := Finset.mem_range.mp hj
      rw [hn] at hjlt
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    have himg : ((Finset.range n).image (fun j : ℕ => lo' + 24 * j)).card = n := by
      rw [Finset.card_image_of_injective _ hinjf, Finset.card_range]
    have hle : n ≤ ((Finset.Icc lo hi).filter fun c : ℕ => c % 24 = r).card := by
      have hcc := Finset.card_le_card hsub
      rwa [himg] at hcc
    have hkey : hi ≤ lo + 24 * n + 23 := by rw [hn]; omega
    have hkeyR : (hi : ℝ) ≤ (lo : ℝ) + 24 * (n : ℝ) + 23 := by exact_mod_cast hkey
    have hleR : (n : ℝ)
        ≤ ((((Finset.Icc lo hi).filter fun c : ℕ => c % 24 = r)).card : ℝ) := by
      exact_mod_cast hle
    linarith
  · -- `lo' > hi` forces `hi - lo < 24`, so the bound is negative
    have hlt : hi < lo + 24 := by omega
    have hnn : (0 : ℝ)
        ≤ ((((Finset.Icc lo hi).filter fun c : ℕ => c % 24 = r)).card : ℝ) :=
      Nat.cast_nonneg _
    have hR : (hi : ℝ) < (lo : ℝ) + 24 := by exact_mod_cast hlt
    linarith

/-- **The non-coprime fibres are empty.** If `2 ∣ d` or `3 ∣ d` then no `N` in
the class `23` modulo `24` is divisible by `d²`.

This is `coprime_six_of_sq_dvd` read contrapositively. The `d = 0` case is
covered, since `2 ∣ 0`. -/
theorem fibre_empty_of_not_coprime {M d : ℕ} (h : 2 ∣ d ∨ 3 ∣ d) :
    ((Finset.Icc 2 M).filter fun N => N % 24 = 23).filter (fun N => d ^ 2 ∣ N)
      = ∅ := by
  classical
  refine Finset.filter_eq_empty_iff.mpr ?_
  intro N hN hdvd
  obtain ⟨hNIcc, hN23⟩ := Finset.mem_filter.mp hN
  -- transfer the two hypotheses to `ℤ` and apply `coprime_six_of_sq_dvd`
  have hNz : ((N : ℤ)) % 24 = 23 := by
    have : ((N % 24 : ℕ) : ℤ) = ((23 : ℕ) : ℤ) := by exact_mod_cast hN23
    push_cast at this
    omega
  have hdz : ((d : ℤ)) ^ 2 ∣ (N : ℤ) := by
    obtain ⟨k, hk⟩ := hdvd
    exact ⟨(k : ℤ), by exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) hk⟩
  obtain ⟨h2, h3⟩ := coprime_six_of_sq_dvd hNz hdz
  rcases h with hd | hd
  · exact h2 (by exact_mod_cast hd)
  · exact h3 (by exact_mod_cast hd)

/-- **The swapped form of the count.** For any `M` with `⌊Y⌋₊ ≤ M²`,

`#D(Y) = ∑_{d ≤ M} μ(d) · #{N ≤ ⌊Y⌋₊ : N ≡ 23 (24), d² ∣ N}`.

The hypothesis `⌊Y⌋₊ ≤ M²` is what makes the fixed inner range legal, and it
fails for `M = ⌊√Y⌋₊`: at `Y = 10` that gives `M² = 9 < 10`. It holds for
`M = ⌊√Y⌋₊ + 1`. -/
theorem card_admissible_eq_swapped (Y : ℝ) {M : ℕ} (hM : ⌊Y⌋₊ ≤ M ^ 2) :
    ((admissible Y).card : ℝ)
      = ∑ d ∈ Finset.range (M + 1), (μ d : ℝ)
          * ((((Finset.Icc 2 ⌊Y⌋₊).filter fun N : ℕ => N % 24 = 23).filter
              fun N => d ^ 2 ∣ N).card : ℝ) := by
  classical
  rw [card_admissible_eq_sum Y]
  have hinner : ∀ N ∈ (Finset.Icc 2 ⌊Y⌋₊).filter (fun N : ℕ => N % 24 = 23),
      ∑ d ∈ N.divisors.filter (fun d => d ^ 2 ∣ N), (μ d : ℝ)
        = ∑ d ∈ (Finset.range (M + 1)).filter (fun d => d ^ 2 ∣ N), (μ d : ℝ) := by
    intro N hN
    obtain ⟨hIcc, -⟩ := Finset.mem_filter.mp hN
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hIcc
    rw [divisor_filter_eq_range (M := M) (by omega) (by omega)]
  rw [Finset.sum_congr rfl hinner]
  exact sum_moebius_swap _ M

/-- **The per-`d` estimate.** For `d ≥ 1` coprime to `6`, the fibre over `d`
differs from `(M / d²) / 24` by at most `2`.

The constant `2` rather than `1` absorbs the `(K - 1)` versus `K` discrepancy in
the interval `Icc 1 K`, which costs `1/24`. -/
theorem fibre_approx {M d : ℕ} (hd : 1 ≤ d) (h2 : ¬ (2 ∣ d)) (h3 : ¬ (3 ∣ d)) :
    |((((Finset.Icc 2 M).filter fun N => N % 24 = 23).filter
        fun N => d ^ 2 ∣ N).card : ℝ) - ((M / d ^ 2 : ℕ) : ℝ) / 24| ≤ 2 := by
  classical
  rw [fibre_card hd h2 h3]
  set K : ℕ := M / d ^ 2 with hK
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  -- lower bound holds unconditionally
  have hge : ((K : ℝ) - 1) / 24 - 1
      ≤ ((((Finset.Icc 1 K).filter fun r : ℕ => r % 24 = 23)).card : ℝ) := by
    have h := card_residue_class_Icc_nat24_ge (lo := 1) (hi := K) (r := 23)
      (by norm_num)
    push_cast at h ⊢
    linarith
  -- upper bound needs `1 ≤ K`; for `K = 0` the set is empty
  have hle : ((((Finset.Icc 1 K).filter fun r : ℕ => r % 24 = 23)).card : ℝ)
      ≤ ((K : ℝ) - 1) / 24 + 1 := by
    rcases Nat.eq_zero_or_pos K with hK0 | hK1
    · rw [hK0]
      rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) from Finset.Icc_eq_empty (by omega)]
      simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero, Nat.cast_zero]
      norm_num
    · have h := card_residue_class_Icc_nat24 (lo := 1) (hi := K) (r := 23) (by omega)
      push_cast at h ⊢
      linarith
  rw [abs_le]
  constructor <;> [linarith; linarith]

/-- **The aggregation.** If `f` and `g` agree to within `E` at every index and
the weights are bounded by `1`, then the weighted sums agree to within
`E * (M + 1)`.

No `0 ≤ E` hypothesis is needed: `hfg` at `d = 0` gives it, since
`Finset.range (M + 1)` is never empty. -/
theorem sum_weighted_error_le {M : ℕ} {E : ℝ} (f g w : ℕ → ℝ)
    (hfg : ∀ d ∈ Finset.range (M + 1), |f d - g d| ≤ E)
    (hw : ∀ d, |w d| ≤ 1) :
    |∑ d ∈ Finset.range (M + 1), w d * f d
      - ∑ d ∈ Finset.range (M + 1), w d * g d| ≤ E * ((M : ℝ) + 1) := by
  have hcomb : ∑ d ∈ Finset.range (M + 1), w d * f d
      - ∑ d ∈ Finset.range (M + 1), w d * g d
      = ∑ d ∈ Finset.range (M + 1), w d * (f d - g d) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hcomb]
  calc |∑ d ∈ Finset.range (M + 1), w d * (f d - g d)|
      ≤ ∑ d ∈ Finset.range (M + 1), |w d * (f d - g d)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Finset.range (M + 1), E := by
        refine Finset.sum_le_sum fun d hd => ?_
        rw [abs_mul]
        have h1 := hw d
        have h2 := hfg d hd
        have hnn : 0 ≤ |f d - g d| := abs_nonneg _
        have hwn : 0 ≤ |w d| := abs_nonneg _
        nlinarith
    _ = E * ((M : ℝ) + 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast; ring

/-- **The choice of `M`.** `⌊Y⌋₊ ≤ (⌊√Y⌋₊ + 1)²`.

The `+ 1` is not slack: with `M = ⌊√Y⌋₊` the inequality is false, as `Y = 10`
shows, where `⌊√10⌋₊² = 9 < 10 = ⌊Y⌋₊`. -/
theorem floor_le_sq_succ {Y : ℝ} (hY : 0 ≤ Y) :
    ⌊Y⌋₊ ≤ (⌊Real.sqrt Y⌋₊ + 1) ^ 2 := by
  have hs : Real.sqrt Y < (⌊Real.sqrt Y⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one (Real.sqrt Y)
  have hsq : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY
  have hsnn : (0 : ℝ) ≤ Real.sqrt Y := Real.sqrt_nonneg Y
  have hYlt : Y < ((⌊Real.sqrt Y⌋₊ : ℝ) + 1) ^ 2 := by nlinarith
  have hfl : ((⌊Y⌋₊ : ℕ) : ℝ) ≤ Y := Nat.floor_le hY
  have hcast : (((⌊Real.sqrt Y⌋₊ + 1) ^ 2 : ℕ) : ℝ)
      = ((⌊Real.sqrt Y⌋₊ : ℝ) + 1) ^ 2 := by push_cast; ring
  have : ((⌊Y⌋₊ : ℕ) : ℝ) < (((⌊Real.sqrt Y⌋₊ + 1) ^ 2 : ℕ) : ℝ) := by
    rw [hcast]; linarith
  exact le_of_lt (by exact_mod_cast this)

/-- **The size of the `d`-range.** `M + 1 ≤ √Y + 2` for `M = ⌊√Y⌋₊ + 1`.

No hypothesis on `Y` is needed: `Real.sqrt_nonneg` holds unconditionally, so the
floor bound does too. -/
theorem range_size_le (Y : ℝ) :
    ((⌊Real.sqrt Y⌋₊ + 1 : ℕ) : ℝ) + 1 ≤ Real.sqrt Y + 2 := by
  have hfl : ((⌊Real.sqrt Y⌋₊ : ℕ) : ℝ) ≤ Real.sqrt Y :=
    Nat.floor_le (Real.sqrt_nonneg Y)
  push_cast
  linarith

/-- The per-`d` main term: `(⌊Y⌋₊ / d²) / 24` on the `d` coprime to `6`, and `0`
elsewhere.

The guard is **required**, not cosmetic. `fibre_approx` only bounds the fibre for
`d` coprime to `6`; for other `d` the fibre is empty
(`fibre_empty_of_not_coprime`) while `(⌊Y⌋₊ / d²) / 24` is large, so comparing
against the unguarded expression is false for every even `d`. It also disposes of
`d = 0`, which is not coprime to `6` since `2 ∣ 0`. -/
private noncomputable def mainTerm (Y : ℝ) (d : ℕ) : ℝ :=
  open Classical in
  if ¬ (2 ∣ d) ∧ ¬ (3 ∣ d) then ((⌊Y⌋₊ / d ^ 2 : ℕ) : ℝ) / 24 else 0

/-- **The per-`d` bound, for every `d`.** The fibre over `d` differs from
`mainTerm Y d` by at most `2`, with no coprimality hypothesis: on the coprime `d`
this is `fibre_approx`, and off them both sides vanish. -/
theorem fibre_sub_mainTerm_le (Y : ℝ) (d : ℕ) :
    |((((Finset.Icc 2 ⌊Y⌋₊).filter fun N => N % 24 = 23).filter
        fun N => d ^ 2 ∣ N).card : ℝ) - mainTerm Y d| ≤ 2 := by
  classical
  unfold mainTerm
  by_cases hcop : ¬ (2 ∣ d) ∧ ¬ (3 ∣ d)
  · obtain ⟨h2, h3⟩ := hcop
    have hd : 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with rfl | h
      · exact absurd (dvd_zero 2) h2
      · exact h
    rw [if_pos ⟨h2, h3⟩]
    exact fibre_approx hd h2 h3
  · -- not coprime: the fibre is empty and the main term is `0`
    rw [if_neg hcop]
    have hor : 2 ∣ d ∨ 3 ∣ d := by
      by_cases h2 : 2 ∣ d
      · exact Or.inl h2
      · exact Or.inr (by tauto)
    rw [fibre_empty_of_not_coprime hor]
    simp only [Finset.card_empty, Nat.cast_zero, sub_zero, abs_zero]
    norm_num

/-- **The count against its main sum.** For `Y ≥ 0`,

`|#D(Y) - ∑_{d ≤ ⌊√Y⌋₊+1} μ(d) · mainTerm Y d| ≤ 2 (√Y + 2)`. -/
theorem card_admissible_sub_mainSum_le {Y : ℝ} (hY : 0 ≤ Y) :
    |((admissible Y).card : ℝ)
      - ∑ d ∈ Finset.range (⌊Real.sqrt Y⌋₊ + 1 + 1), (μ d : ℝ) * mainTerm Y d|
      ≤ 2 * (Real.sqrt Y + 2) := by
  classical
  set M : ℕ := ⌊Real.sqrt Y⌋₊ + 1 with hM
  have hMsq : ⌊Y⌋₊ ≤ M ^ 2 := by rw [hM]; exact floor_le_sq_succ hY
  rw [card_admissible_eq_swapped Y hMsq]
  have hagg := sum_weighted_error_le (M := M) (E := 2)
    (f := fun d => ((((Finset.Icc 2 ⌊Y⌋₊).filter fun N => N % 24 = 23).filter
        fun N => d ^ 2 ∣ N).card : ℝ))
    (g := mainTerm Y) (w := fun d => (μ d : ℝ))
    (fun d _ => fibre_sub_mainTerm_le Y d)
    (fun d => PartitionZheng.abs_moebius_le_one d)
  have hrange : ((M : ℕ) : ℝ) + 1 ≤ Real.sqrt Y + 2 := by
    rw [hM]; exact range_size_le Y
  have hstep : (2 : ℝ) * (((M : ℕ) : ℝ) + 1) ≤ 2 * (Real.sqrt Y + 2) := by linarith
  exact le_trans hagg hstep

/-- **Replacing `⌊Y⌋₊` and `ℕ`-division by `Y` and real division.** For `d ≥ 1`
and `Y ≥ 0`, `|(⌊Y⌋₊ / d² : ℕ) - Y / d²| ≤ 2`.

Two roundings are absorbed at once: `⌊Y⌋₊` loses less than `1` against `Y`, and
truncating `ℕ`-division loses less than `d²`, which is `1` after dividing. Their
sum is `(1 + d²)/d² = 1/d² + 1 ≤ 2`. -/
theorem floorDiv_sub_div_le {Y : ℝ} (hY : 0 ≤ Y) {d : ℕ} (hd : 1 ≤ d) :
    |((⌊Y⌋₊ / d ^ 2 : ℕ) : ℝ) - Y / (d : ℝ) ^ 2| ≤ 2 := by
  have hq : 0 < d ^ 2 := pow_pos hd 2
  have hqR : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  have hqR0 : (0 : ℝ) < (d : ℝ) ^ 2 := by linarith
  -- `⌊Y⌋₊ = d² * Q + R` with `0 ≤ R < d²`
  set K : ℕ := ⌊Y⌋₊ with hK
  set Q : ℕ := K / d ^ 2 with hQ
  set R : ℕ := K % d ^ 2 with hR
  have hdm : d ^ 2 * Q + R = K := Nat.div_add_mod K (d ^ 2)
  have hRlt : R < d ^ 2 := Nat.mod_lt K hq
  have hfl : (K : ℝ) ≤ Y := Nat.floor_le hY
  have hlt : Y < (K : ℝ) + 1 := Nat.lt_floor_add_one Y
  -- cast the division identity
  have hdmR : (d : ℝ) ^ 2 * (Q : ℝ) + (R : ℝ) = (K : ℝ) := by
    have : ((d ^ 2 * Q + R : ℕ) : ℝ) = ((K : ℕ) : ℝ) := by exact_mod_cast hdm
    push_cast at this
    linarith
  have hRnn : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg _
  have hRltR : (R : ℝ) < (d : ℝ) ^ 2 := by exact_mod_cast hRlt
  -- `Q ≤ Y/d² ≤ Q + 2`
  have hA : (Q : ℝ) ≤ Y / (d : ℝ) ^ 2 := by
    rw [le_div_iff₀ hqR0]; nlinarith
  have hB : Y / (d : ℝ) ^ 2 ≤ (Q : ℝ) + 2 := by
    rw [div_le_iff₀ hqR0]; nlinarith
  rw [abs_le]
  constructor <;> linarith

/- ### The restricted Möbius series and its partial sums -/

/-- Coprimality to `6` is the conjunction of the two divisibility conditions. -/
theorem coprime_six_iff (d : ℕ) : Nat.Coprime d 6 ↔ ¬ (2 ∣ d) ∧ ¬ (3 ∣ d) := by
  have h6 : (6 : ℕ) = 2 * 3 := by norm_num
  rw [h6, Nat.coprime_mul_iff_right]
  constructor
  · intro h
    exact ⟨(Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp h.1.symm,
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp h.2.symm⟩
  · intro h
    exact ⟨((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h.1).symm,
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h.2).symm⟩

/-- The Möbius summand `μ(d)/d²`, extended by `0` off the `d` coprime to `6`.

This is `coprimeSummand` transported from the subtype `{m // Nat.Coprime m 6}`
to all of `ℕ`. -/
private noncomputable def coprimeTerm (d : ℕ) : ℝ :=
  if Nat.Coprime d 6 then (μ d : ℝ) / (d : ℝ) ^ 2 else 0

/-- `|μ(d)/d²| ≤ 1/d²`, uniformly in `d`. At `d = 0` both sides are `0`: `0` is
not coprime to `6`, and `(0 : ℝ)⁻¹ = 0`. -/
theorem abs_coprimeTerm_le (d : ℕ) : |coprimeTerm d| ≤ ((d : ℝ) ^ 2)⁻¹ := by
  unfold coprimeTerm
  by_cases h : Nat.Coprime d 6
  · rw [if_pos h]
    have hd : 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · exact absurd h (by decide)
      · exact hd
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hsq : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
    have h1 : |((μ d : ℤ) : ℝ)| ≤ 1 := abs_moebius_le_one d
    rw [abs_div, abs_of_pos hsq, ← one_div]
    gcongr
  · rw [if_neg h, abs_zero]
    positivity

/-- `∑ 1/d²` converges, in the inverse form the tail bound uses. -/
theorem summable_inv_sq : Summable (fun d : ℕ => ((d : ℝ) ^ 2)⁻¹) := by
  have h : Summable (fun d : ℕ => 1 / (d : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  simpa only [one_div] using h

/-- The restricted Möbius series is summable, by comparison with `∑ 1/d²`. -/
theorem summable_coprimeTerm : Summable coprimeTerm := by
  refine summable_inv_sq.of_norm_bounded ?_
  intro d
  rw [Real.norm_eq_abs]
  exact abs_coprimeTerm_le d

/-- **The value of the restricted series.** `∑_d coprimeTerm d = 9/π²`.

This is `coprime_moebius_tsum` with the subtype index `{m // Nat.Coprime m 6}`
replaced by all of `ℕ`. The reindexing is legal because `coprimeTerm` is
supported on the coprime `d` by construction. -/
theorem coprimeTerm_tsum : ∑' d : ℕ, coprimeTerm d = 9 / Real.pi ^ 2 := by
  have hsupp : Function.support coprimeTerm
      ⊆ Set.range (Subtype.val : {m : ℕ // Nat.Coprime m 6} → ℕ) := by
    intro d hd
    have h : Nat.Coprime d 6 := by
      by_contra hc
      exact hd (by unfold coprimeTerm; rw [if_neg hc])
    exact ⟨⟨d, h⟩, rfl⟩
  rw [← Subtype.val_injective.tsum_eq hsupp, ← coprime_moebius_tsum]
  refine tsum_congr fun m => ?_
  unfold coprimeTerm coprimeSummand
  rw [if_pos m.2]

/-- **The tail of a series dominated by `1/d²`.** Past the index `M` such a
series contributes at most `2/(M+1)`.

No separate convergence argument for the tail is needed: `summable_inv_sq`
dominates the shifted series termwise. -/
theorem abs_tsum_nat_add_le {f : ℕ → ℝ} (hf : Summable f)
    (hbd : ∀ d, |f d| ≤ ((d : ℝ) ^ 2)⁻¹) (M : ℕ) :
    |∑' i : ℕ, f (i + (M + 1))| ≤ 2 / ((M : ℝ) + 1) := by
  have habs : Summable (fun i : ℕ => |f (i + (M + 1))|) :=
    summable_abs_iff.mpr ((summable_nat_add_iff (M + 1)).mpr hf)
  have h1 : |∑' i : ℕ, f (i + (M + 1))| ≤ ∑' i : ℕ, |f (i + (M + 1))| := by
    have hnorm : Summable fun i : ℕ => ‖f (i + (M + 1))‖ := by
      simpa only [Real.norm_eq_abs] using habs
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
  have h2 : ∑' i : ℕ, |f (i + (M + 1))| ≤ 2 / ((M : ℝ) + 1) := by
    refine Real.tsum_le_of_sum_range_le (fun i => abs_nonneg _) fun n => ?_
    have hio : Finset.Ico (M + 1) (M + 1 + n) = Finset.Ioo M (M + 1 + n) := by
      ext j
      simp only [Finset.mem_Ico, Finset.mem_Ioo]
      omega
    have hre : ∑ j ∈ Finset.Ico (M + 1) (M + 1 + n), (((j : ℕ) : ℝ) ^ 2)⁻¹
        = ∑ i ∈ Finset.range n, (((i + (M + 1) : ℕ) : ℝ) ^ 2)⁻¹ := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_left]
      exact Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm]
    calc ∑ i ∈ Finset.range n, |f (i + (M + 1))|
        ≤ ∑ i ∈ Finset.range n, (((i + (M + 1) : ℕ) : ℝ) ^ 2)⁻¹ :=
          Finset.sum_le_sum fun i _ => hbd _
      _ = ∑ j ∈ Finset.Ioo M (M + 1 + n), (((j : ℕ) : ℝ) ^ 2)⁻¹ := by rw [← hio, hre]
      _ ≤ 2 / ((M : ℝ) + 1) := sum_Ioo_inv_sq_le M (M + 1 + n)
  linarith

/-- **The partial restricted series against its value.** For every `M`,

`|∑_{d ≤ M} coprimeTerm d - 9/π²| ≤ 2/(M+1)`,

an explicit error rather than an `O(1/M)`. -/
theorem abs_coprimeTerm_range_sub_le (M : ℕ) :
    |∑ d ∈ Finset.range (M + 1), coprimeTerm d - 9 / Real.pi ^ 2|
      ≤ 2 / ((M : ℝ) + 1) := by
  have hsplit := summable_coprimeTerm.sum_add_tsum_nat_add (M + 1)
  rw [coprimeTerm_tsum] at hsplit
  have hkey : ∑ d ∈ Finset.range (M + 1), coprimeTerm d - 9 / Real.pi ^ 2
      = -(∑' i : ℕ, coprimeTerm (i + (M + 1))) := by linarith
  rw [hkey, abs_neg]
  exact abs_tsum_nat_add_le summable_coprimeTerm abs_coprimeTerm_le M

/- ### From the main sum to `δY` -/

/-- The per-`d` main term with both roundings removed: `Y` in place of `⌊Y⌋₊`,
and real division in place of `ℕ`-division.

The coprimality guard is retained for the same reason as in `mainTerm`: off the
`d` coprime to `6` the fibre is empty while `Y/(24d²)` is large. -/
private noncomputable def mainTermReal (Y : ℝ) (d : ℕ) : ℝ :=
  if Nat.Coprime d 6 then Y / (d : ℝ) ^ 2 / 24 else 0

/-- **The per-`d` cost of removing the roundings**, namely `2/24 = 1/12`.

On the `d` coprime to `6` this is `floorDiv_sub_div_le` divided by `24`, and off
them both sides vanish. -/
theorem mainTerm_sub_mainTermReal_le {Y : ℝ} (hY : 0 ≤ Y) (d : ℕ) :
    |mainTerm Y d - mainTermReal Y d| ≤ 1 / 12 := by
  unfold mainTerm mainTermReal
  by_cases h : Nat.Coprime d 6
  · obtain ⟨h2, h3⟩ := (coprime_six_iff d).mp h
    have hd : 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · exact absurd (dvd_zero 2) h2
      · exact hd
    rw [if_pos ⟨h2, h3⟩, if_pos h]
    have hkey := floorDiv_sub_div_le hY hd
    have hrw : ((⌊Y⌋₊ / d ^ 2 : ℕ) : ℝ) / 24 - Y / (d : ℝ) ^ 2 / 24
        = (((⌊Y⌋₊ / d ^ 2 : ℕ) : ℝ) - Y / (d : ℝ) ^ 2) / 24 := by ring
    rw [hrw, abs_div, show |(24 : ℝ)| = 24 from by norm_num]
    linarith
  · have hnc : ¬ (¬ (2 ∣ d) ∧ ¬ (3 ∣ d)) := fun hc => h ((coprime_six_iff d).mpr hc)
    rw [if_neg hnc, if_neg h, sub_zero, abs_zero]
    norm_num

/-- **The main sum with the roundings removed.** For `Y ≥ 0`,

`|∑_{d ≤ ⌊√Y⌋₊+1} μ(d) · mainTerm Y d - ∑_{d ≤ ⌊√Y⌋₊+1} μ(d) · mainTermReal Y d|
  ≤ (1/12)(√Y + 2)`. -/
theorem mainSum_sub_realSum_le {Y : ℝ} (hY : 0 ≤ Y) :
    |∑ d ∈ Finset.range (⌊Real.sqrt Y⌋₊ + 1 + 1), (μ d : ℝ) * mainTerm Y d
      - ∑ d ∈ Finset.range (⌊Real.sqrt Y⌋₊ + 1 + 1), (μ d : ℝ) * mainTermReal Y d|
      ≤ 1 / 12 * (Real.sqrt Y + 2) := by
  set M : ℕ := ⌊Real.sqrt Y⌋₊ + 1 with hM
  have hagg := sum_weighted_error_le (M := M) (E := 1 / 12)
    (f := mainTerm Y) (g := mainTermReal Y) (w := fun d => (μ d : ℝ))
    (fun d _ => mainTerm_sub_mainTermReal_le hY d)
    (fun d => PartitionZheng.abs_moebius_le_one d)
  have hrange : ((M : ℕ) : ℝ) + 1 ≤ Real.sqrt Y + 2 := by
    rw [hM]; exact range_size_le Y
  have hstep : (1 : ℝ) / 12 * (((M : ℕ) : ℝ) + 1) ≤ 1 / 12 * (Real.sqrt Y + 2) := by
    linarith
  exact le_trans hagg hstep

/-- **The rounding-free main sum, factored.** `μ(d) · mainTermReal Y d` is
`(Y/24) · coprimeTerm d`, so the sum is `(Y/24)` times a partial sum of the
restricted Möbius series. -/
theorem realSum_eq (Y : ℝ) (M : ℕ) :
    ∑ d ∈ Finset.range (M + 1), (μ d : ℝ) * mainTermReal Y d
      = Y / 24 * ∑ d ∈ Finset.range (M + 1), coprimeTerm d := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  unfold mainTermReal coprimeTerm
  by_cases h : Nat.Coprime d 6
  · rw [if_pos h, if_pos h]; ring
  · rw [if_neg h, if_neg h]; ring

/-- **The rounding-free main sum against `δY`.** For `Y ≥ 1`,

`|∑_{d ≤ ⌊√Y⌋₊+1} μ(d) · mainTermReal Y d - δY| ≤ √Y/12`.

The constants close exactly, with nothing absorbed into the error: the partial
sum `S_M` lies within `2/(M+1) ≤ 2/√Y` of `9/π²`, and `(Y/24)(2/√Y) = √Y/12`. -/
theorem realSum_sub_delta_le {Y : ℝ} (hY : 1 ≤ Y) :
    |∑ d ∈ Finset.range (⌊Real.sqrt Y⌋₊ + 1 + 1), (μ d : ℝ) * mainTermReal Y d
      - delta * Y| ≤ Real.sqrt Y / 12 := by
  set M : ℕ := ⌊Real.sqrt Y⌋₊ + 1 with hM
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hs1 : (1 : ℝ) ≤ Real.sqrt Y := by
    have h : Real.sqrt 1 ≤ Real.sqrt Y := Real.sqrt_le_sqrt hY
    rwa [Real.sqrt_one] at h
  have hs0 : (0 : ℝ) < Real.sqrt Y := by linarith
  have hsq : Real.sqrt Y * Real.sqrt Y = Y := Real.mul_self_sqrt hY0
  have hdelta : delta * Y = Y / 24 * (9 / Real.pi ^ 2) := by rw [delta_eq]; ring
  rw [realSum_eq, hdelta]
  -- the truncation error, transported to the `√Y` scale
  have hfl : Real.sqrt Y < ((⌊Real.sqrt Y⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hMR : Real.sqrt Y ≤ ((M : ℕ) : ℝ) + 1 := by
    rw [hM]; push_cast; linarith
  have hdiv : 2 / (((M : ℕ) : ℝ) + 1) ≤ 2 / Real.sqrt Y := by
    gcongr
  have hbound : |∑ d ∈ Finset.range (M + 1), coprimeTerm d - 9 / Real.pi ^ 2|
      ≤ 2 / Real.sqrt Y := le_trans (abs_coprimeTerm_range_sub_le M) hdiv
  have hfac : Y / 24 * ∑ d ∈ Finset.range (M + 1), coprimeTerm d
      - Y / 24 * (9 / Real.pi ^ 2)
      = Y / 24 * (∑ d ∈ Finset.range (M + 1), coprimeTerm d - 9 / Real.pi ^ 2) := by
    ring
  have hkey : Y / 24 * (2 / Real.sqrt Y) = Real.sqrt Y / 12 := by
    have hne : Real.sqrt Y ≠ 0 := ne_of_gt hs0
    field_simp
    nlinarith [hsq]
  rw [hfac, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ Y / 24)]
  calc Y / 24 * |∑ d ∈ Finset.range (M + 1), coprimeTerm d - 9 / Real.pi ^ 2|
      ≤ Y / 24 * (2 / Real.sqrt Y) :=
        mul_le_mul_of_nonneg_left hbound (by linarith)
    _ = Real.sqrt Y / 12 := hkey

/-- **`lem_Dset_card`.** `|#D(Y) - δY| ≤ 7√Y` for every `Y ≥ 1`, with
`δ = 3/(8π²)`.

The constant is existentially quantified rather than hidden in `O()`-notation,
and the proof exhibits `C = 7`.

The three errors that make up `C`, all for `Y ≥ 1`, where `√Y ≥ 1`:

* `2(√Y + 2) ≤ 6√Y` from `card_admissible_sub_mainSum_le`, the residue count in
  each fibre;
* `(1/12)(√Y + 2) ≤ (1/4)√Y` from `mainSum_sub_realSum_le`, the two roundings;
* `√Y/12` from `realSum_sub_delta_le`, the truncation of the Möbius series.

Their sum is at most `(19/3)√Y`, and `19/3 < 7`. -/
theorem card_admissible_sub_delta_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 1 ≤ Y →
      |((admissible Y).card : ℝ) - delta * Y| ≤ C * Real.sqrt Y := by
  refine ⟨7, by norm_num, fun Y hY => ?_⟩
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hs1 : (1 : ℝ) ≤ Real.sqrt Y := by
    have h : Real.sqrt 1 ≤ Real.sqrt Y := Real.sqrt_le_sqrt hY
    rwa [Real.sqrt_one] at h
  have h1 := card_admissible_sub_mainSum_le hY0
  have h2 := mainSum_sub_realSum_le hY0
  have h3 := realSum_sub_delta_le hY
  rw [abs_le] at h1 h2 h3 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# The range bound and the good discriminants

For a threshold `H`, a discriminant is *good* when its class number is at most
`H * sqrt Y`; the parity theorem then gives an admissible `m ≤ 12 * H * sqrt Y + 2`,
so the resulting partition index is at most

`Z_H Y = 6 H² Y² + 2 H Y^{3/2} + Y/6 + 1/24`.

`Y ^ (3/2)` is written `Y * sqrt Y`, which agrees with it for `Y ≥ 0` — the only
range where `Z_H` is used — and avoids `rpow`.

## Main definitions

* `PartitionZheng.good` — the good discriminants up to `Y`.
* `PartitionZheng.ZH` — the range bound `Z_H Y`.

## Main results

* `PartitionZheng.ZH_strictMonoOn` — `Z_H` is strictly increasing on `[0, ∞)`,
  which is what makes the change of variable `Z_H Y_X = X` well posed.
-/


namespace PartitionZheng

open Real

open Classical in
/-- The good discriminants up to `Y`: those whose class number is at most
`H * sqrt Y`. -/
private noncomputable def good (Y H : ℝ) : Finset ℕ :=
  (admissible Y).filter fun D => ((classNumber (D : ℤ) : ℝ) ≤ H * Real.sqrt Y)

/-- The range bound: every partition index produced by a good discriminant up to
`Y` is at most `ZH H Y`. -/
private noncomputable def ZH (H Y : ℝ) : ℝ :=
  6 * H ^ 2 * Y ^ 2 + 2 * H * (Y * Real.sqrt Y) + Y / 6 + 1 / 24

/-- `ZH H` is strictly increasing on `[0, ∞)`. The quadratic and the `Y^{3/2}`
term are increasing there, and the linear term `Y / 6` is strictly increasing,
so the sum is. -/
theorem ZH_strictMonoOn {H : ℝ} (hH : 0 < H) :
    StrictMonoOn (ZH H) (Set.Ici 0) := by
  intro x hx y hy hxy
  have hx0 : (0 : ℝ) ≤ x := hx
  have hy0 : (0 : ℝ) ≤ y := hy
  have hsq : x ^ 2 ≤ y ^ 2 := by nlinarith
  have hs : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy.le
  have hxs : x * Real.sqrt x ≤ y * Real.sqrt y := by
    have h1 : x * Real.sqrt x ≤ y * Real.sqrt x :=
      mul_le_mul_of_nonneg_right hxy.le (Real.sqrt_nonneg x)
    have h2 : y * Real.sqrt x ≤ y * Real.sqrt y :=
      mul_le_mul_of_nonneg_left hs hy0
    linarith
  have hH2 : 0 ≤ 6 * H ^ 2 := by positivity
  unfold ZH
  have hq : 6 * H ^ 2 * x ^ 2 ≤ 6 * H ^ 2 * y ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hH2
  have hc : 2 * H * (x * Real.sqrt x) ≤ 2 * H * (y * Real.sqrt y) :=
    mul_le_mul_of_nonneg_left hxs (by linarith)
  linarith

/-- `D` is good for `Y` and `H` exactly when it is admissible up to `Y` and its class
number is at most `H * sqrt Y`. -/
theorem mem_good_iff {Y H : ℝ} {D : ℕ} :
    D ∈ good Y H ↔ D ∈ admissible Y ∧ ((classNumber (D : ℤ) : ℝ) ≤ H * Real.sqrt Y) := by
  classical
  simp [good, Finset.mem_filter]

/-- The partition index produced by a discriminant `D ≤ Y` whose admissible `m`
satisfies `m ≤ 12 H sqrt Y + 2` is at most `ZH H Y`. Expanding
`(12 H sqrt Y + 2) ^ 2 = 144 H² Y + 48 H sqrt Y + 4` and multiplying by `Y`
gives exactly the four terms of `ZH`. -/
theorem nD_le_ZH {Y H : ℝ} (hY : 0 ≤ Y) {D m n : ℕ}
    (hDY : (D : ℝ) ≤ Y) (hmle : (m : ℝ) ≤ 12 * H * Real.sqrt Y + 2)
    (hn : 24 * n = D * m ^ 2 + 1) : (n : ℝ) ≤ ZH H Y := by
  have hs : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY
  have hs0 : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg Y
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hcast : (24 : ℝ) * (n : ℝ) = (D : ℝ) * (m : ℝ) ^ 2 + 1 := by
    have := congrArg (fun k : ℕ => (k : ℝ)) hn
    push_cast at this
    linarith
  have hmsq : (m : ℝ) ^ 2 ≤ (12 * H * Real.sqrt Y + 2) ^ 2 := by
    have h2 : (0 : ℝ) ≤ 12 * H * Real.sqrt Y + 2 := le_trans hm0 hmle
    nlinarith
  have hDm : (D : ℝ) * (m : ℝ) ^ 2 ≤ Y * (12 * H * Real.sqrt Y + 2) ^ 2 := by
    have hsq0 : (0 : ℝ) ≤ (m : ℝ) ^ 2 := by positivity
    nlinarith
  have hexp : Y * (12 * H * Real.sqrt Y + 2) ^ 2
      = 144 * H ^ 2 * Y ^ 2 + 48 * H * (Y * Real.sqrt Y) + 4 * Y := by
    have hsq : (12 * H * Real.sqrt Y + 2) ^ 2
        = 144 * H ^ 2 * Real.sqrt Y ^ 2 + 48 * H * Real.sqrt Y + 4 := by ring
    rw [hsq, hs]
    ring
  rw [hexp] at hDm
  unfold ZH
  linarith

/-- `ZH H` is continuous. -/
theorem ZH_continuous {H : ℝ} : Continuous (ZH H) := by
  unfold ZH
  have : Continuous (fun Y : ℝ => Real.sqrt Y) := Real.continuous_sqrt
  fun_prop

/-- `ZH H` is injective on `[0, ∞)`. -/
theorem ZH_injOn {H : ℝ} (hH : 0 < H) : Set.InjOn (ZH H) (Set.Ici 0) :=
  (ZH_strictMonoOn hH).injOn

/-- The change of variable is well posed: for `X ≥ ZH H 0` there is exactly one
`Y ≥ 0` with `ZH H Y = X`. Existence is the intermediate value theorem on
`[0, 6X]`, using `ZH H Y ≥ Y / 6`; uniqueness is strict monotonicity. -/
theorem exists_unique_YX {H X : ℝ} (hH : 0 < H) (hX : ZH H 0 ≤ X) :
    ∃! Y, 0 ≤ Y ∧ ZH H Y = X := by
  have hZH0 : ZH H 0 = 1 / 24 := by unfold ZH; norm_num
  have hX0 : (0 : ℝ) ≤ X := by rw [hZH0] at hX; linarith
  have hB6 : (0 : ℝ) ≤ 6 * X := by linarith
  have hB : X ≤ ZH H (6 * X) := by
    unfold ZH
    have h1 : (0 : ℝ) ≤ 6 * H ^ 2 * (6 * X) ^ 2 := by positivity
    have hs : (0 : ℝ) ≤ Real.sqrt (6 * X) := Real.sqrt_nonneg _
    have h2 : (0 : ℝ) ≤ 2 * H * ((6 * X) * Real.sqrt (6 * X)) := by
      have : (0 : ℝ) ≤ (6 * X) * Real.sqrt (6 * X) := mul_nonneg hB6 hs
      positivity
    linarith
  have hcont : ContinuousOn (ZH H) (Set.Icc 0 (6 * X)) :=
    ZH_continuous.continuousOn
  have hsub := intermediate_value_Icc hB6 hcont
  have hmem : X ∈ Set.Icc (ZH H 0) (ZH H (6 * X)) := ⟨hX, hB⟩
  obtain ⟨Y, hYmem, hYeq⟩ := hsub hmem
  refine ⟨Y, ⟨hYmem.1, hYeq⟩, ?_⟩
  rintro Z ⟨hZ0, hZeq⟩
  exact ZH_injOn hH hZ0 hYmem.1 (by rw [hZeq, hYeq])

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# The change of variable

`YX H X` is the unique `Y ≥ 0` with `Z_H Y = X`. This file names it and proves
the asymptotic `Y_X / sqrt X → 1 / (sqrt 6 * H)`.

Since `Z_H Y = 6 H² Y² + 2 H Y^{3/2} + Y/6 + 1/24` has nonnegative lower-order
terms, `6 H² Y² ≤ X` outright, giving the exact upper bound
`Y ≤ sqrt X / (sqrt 6 H)`. In the other direction the tail is eventually at
most `δ` times the quadratic term, so `X ≤ (1 + δ) 6 H² Y²` and
`Y ≥ sqrt X / (sqrt 6 H sqrt (1 + δ))`. The two bounds squeeze the ratio, and
`1 - 1/sqrt (1 + d) ≤ d` turns the squeeze into an explicit modulus, avoiding
any continuity argument for `d ↦ 1/sqrt (1 + d)` at `0`.

## Main definitions

* `PartitionZheng.YX` — the solution of `Z_H Y = X`.

## Main results

* `PartitionZheng.YX_le_sqrt` — the exact upper bound.
* `PartitionZheng.sqrt_le_YX` — the lower bound for each fixed `δ > 0`.
* `PartitionZheng.YX_asymptotic` — the asymptotic.
-/


namespace PartitionZheng

open Real

open Classical in
/-- The solution of `Z_H Y = X` with `Y ≥ 0`, junk value `0` when there is
none. `lem_YX_exists` shows it exists and is unique for `X ≥ Z_H 0`. -/
private noncomputable def YX (H X : ℝ) : ℝ :=
  if h : ∃ Y, 0 ≤ Y ∧ ZH H Y = X then h.choose else 0

/-- `YX` solves the equation, when a solution exists. -/
theorem YX_spec {H X : ℝ} (hH : 0 < H) (hX : ZH H 0 ≤ X) :
    0 ≤ YX H X ∧ ZH H (YX H X) = X := by
  classical
  have hex : ∃ Y, 0 ≤ Y ∧ ZH H Y = X := (exists_unique_YX hH hX).exists
  rw [YX, dif_pos hex]
  exact hex.choose_spec

/-- The three lower-order terms of `Z_H` are nonnegative at `YX H X`. -/
theorem YX_tail_nonneg {H X : ℝ} (hH : 0 < H) (hX : ZH H 0 ≤ X) :
    0 ≤ 2 * H * (YX H X * Real.sqrt (YX H X)) + YX H X / 6 + 1 / 24 := by
  obtain ⟨hY0, _⟩ := YX_spec hH hX
  have hs : 0 ≤ Real.sqrt (YX H X) := Real.sqrt_nonneg _
  have h1 : 0 ≤ YX H X * Real.sqrt (YX H X) := mul_nonneg hY0 hs
  have h2 : 0 ≤ 2 * H * (YX H X * Real.sqrt (YX H X)) := by positivity
  linarith

/-- `X` minus the lower-order tail is at most the quadratic term. A restatement
of `Z_H (YX H X) = X`, recorded because the limit argument starts here. -/
theorem YX_quadratic_lower {H X : ℝ} (hH : 0 < H) (hX : ZH H 0 ≤ X) :
    X - (2 * H * (YX H X * Real.sqrt (YX H X)) + YX H X / 6 + 1 / 24)
      ≤ 6 * H ^ 2 * (YX H X) ^ 2 := by
  obtain ⟨_, heq⟩ := YX_spec hH hX
  -- Unfold in the hypothesis; rewriting `X` in the goal would also rewrite the
  -- `X` inside `YX H X` and blow it up.
  unfold ZH at heq
  linarith

/-- `6 H² Y² ≤ X`: the quadratic term alone cannot exceed `X`, since the other
three terms of `Z_H` are nonnegative. -/
theorem quad_le {H X : ℝ} (hH : 0 < H) (hX : ZH H 0 ≤ X) :
    6 * H ^ 2 * (YX H X) ^ 2 ≤ X := by
  obtain ⟨hY0, heq⟩ := YX_spec hH hX
  have htail := YX_tail_nonneg hH hX
  -- Unfold in the HYPOTHESIS: rewriting `X` would also rewrite it inside
  -- `YX H X` and blow the goal up.
  unfold ZH at heq
  linarith

/-- Hence the exact upper bound `Y ≤ sqrt X / (sqrt 6 * H)`. -/
theorem YX_le_sqrt {H X : ℝ} (hH : 0 < H) (hX : ZH H 0 ≤ X) :
    YX H X ≤ Real.sqrt X / (Real.sqrt 6 * H) := by
  obtain ⟨hY0, _⟩ := YX_spec hH hX
  have hq := quad_le hH hX
  have h6 : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hden : (0 : ℝ) < Real.sqrt 6 * H := mul_pos h6 hH
  rw [le_div_iff₀ hden]
  -- `(Y * (√6 * H))² = 6 H² Y² ≤ X = (√X)²`, and both sides are nonneg.
  have hX0 : (0 : ℝ) ≤ X := le_trans (by positivity) hq
  have hsq6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hsqX : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX0
  nlinarith [Real.sqrt_nonneg X, mul_nonneg hY0 (le_of_lt hden)]

/-- `YX H X` is at least `M` as soon as `X` is at least `Z_H M`: strict
monotonicity of `Z_H` inverts the inequality. -/
theorem le_YX {H X M : ℝ} (hH : 0 < H) (hM : 0 ≤ M) (hX : ZH H M ≤ X) :
    M ≤ YX H X := by
  have hmono := ZH_strictMonoOn hH
  have h0M : ZH H 0 ≤ ZH H M := by
    rcases eq_or_lt_of_le hM with h | h
    · subst h; exact le_refl _
    · exact le_of_lt (hmono Set.self_mem_Ici (Set.mem_Ici.mpr hM) h)
  have hX0 : ZH H 0 ≤ X := le_trans h0M hX
  obtain ⟨hY0, heq⟩ := YX_spec hH hX0
  by_contra hc
  have hlt : YX H X < M := by linarith [not_le.mp hc]
  have := hmono (Set.mem_Ici.mpr hY0) (Set.mem_Ici.mpr hM) hlt
  rw [heq] at this
  linarith

/-- For `Y` large, the three lower-order terms of `Z_H` are at most `δ` times
the quadratic term. Concretely, for `Y ≥ 1` they are all at most a constant
times `Y * sqrt Y`, and `Y * sqrt Y / Y² = 1 / sqrt Y → 0`. -/
theorem tail_le_of_large {H δ : ℝ} (hH : 0 < H) (hδ : 0 < δ) :
    ∃ Y₀ : ℝ, 1 ≤ Y₀ ∧ ∀ Y, Y₀ ≤ Y →
      2 * H * (Y * Real.sqrt Y) + Y / 6 + 1 / 24 ≤ δ * (6 * H ^ 2 * Y ^ 2) := by
  set C : ℝ := 2 * H + 5 / 24 with hC
  have hC0 : 0 < C := by rw [hC]; positivity
  refine ⟨max 1 ((C / (6 * H ^ 2 * δ)) ^ 2 + 1), le_max_left _ _, ?_⟩
  intro Y hY
  have hY1 : (1 : ℝ) ≤ Y := le_trans (le_max_left _ _) hY
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hs : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY0
  have hs1 : (1 : ℝ) ≤ Real.sqrt Y := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hY1
  -- each lower-order term is at most `Y * sqrt Y`
  have hle1 : Y ≤ Y * Real.sqrt Y := by nlinarith
  have hle2 : (1 : ℝ) ≤ Y * Real.sqrt Y := by nlinarith
  have hsum : 2 * H * (Y * Real.sqrt Y) + Y / 6 + 1 / 24 ≤ C * (Y * Real.sqrt Y) := by
    rw [hC]; nlinarith
  -- and `C * Y * sqrt Y ≤ δ * 6 H² Y²` once `sqrt Y ≥ C / (6 H² δ)`
  have hbig : C / (6 * H ^ 2 * δ) ≤ Real.sqrt Y := by
    have hsq : (C / (6 * H ^ 2 * δ)) ^ 2 ≤ Y := by
      have := le_trans (le_max_right 1 ((C / (6 * H ^ 2 * δ)) ^ 2 + 1)) hY
      linarith
    have hnn : 0 ≤ C / (6 * H ^ 2 * δ) := by positivity
    nlinarith [Real.sqrt_nonneg Y]
  have hden : (0 : ℝ) < 6 * H ^ 2 * δ := by positivity
  have hstep : C * (Y * Real.sqrt Y) ≤ δ * (6 * H ^ 2 * Y ^ 2) := by
    rw [div_le_iff₀ hden] at hbig
    have hmul := mul_le_mul_of_nonneg_right hbig (mul_nonneg hY0 (Real.sqrt_nonneg Y))
    calc C * (Y * Real.sqrt Y)
        ≤ Real.sqrt Y * (6 * H ^ 2 * δ) * (Y * Real.sqrt Y) := hmul
      _ = 6 * H ^ 2 * δ * Y * Real.sqrt Y ^ 2 := by ring
      _ = δ * (6 * H ^ 2 * Y ^ 2) := by rw [hs]; ring
  linarith

/-- The lower half of the asymptotic: once `X` is large, `Y` is at least
`sqrt X / (sqrt 6 * H * sqrt (1 + δ))`. From `X ≤ (1 + δ) * 6 H² Y²`. -/
theorem sqrt_le_YX {H δ : ℝ} (hH : 0 < H) (hδ : 0 < δ) :
    ∃ X₀ : ℝ, ∀ X, X₀ ≤ X →
      Real.sqrt X / (Real.sqrt 6 * H * Real.sqrt (1 + δ)) ≤ YX H X := by
  obtain ⟨Y₀, hY₀1, hY₀⟩ := tail_le_of_large hH hδ
  refine ⟨max (ZH H Y₀) (ZH H 0), ?_⟩
  intro X hX
  have hX0 : ZH H 0 ≤ X := le_trans (le_max_right _ _) hX
  have hXY₀ : ZH H Y₀ ≤ X := le_trans (le_max_left _ _) hX
  obtain ⟨hY0, heq⟩ := YX_spec hH hX0
  have hYbig : Y₀ ≤ YX H X := le_YX hH (by linarith) hXY₀
  -- `X = Z_H Y ≤ (1 + δ) * 6 H² Y²`
  have hub : X ≤ (1 + δ) * (6 * H ^ 2 * (YX H X) ^ 2) := by
    have htail := hY₀ (YX H X) hYbig
    unfold ZH at heq
    linarith
  have hXnn : (0 : ℝ) ≤ X := le_trans (by positivity) (quad_le hH hX0)
  have h6 : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hd : (0 : ℝ) < Real.sqrt (1 + δ) := Real.sqrt_pos.mpr (by linarith)
  have hden : (0 : ℝ) < Real.sqrt 6 * H * Real.sqrt (1 + δ) := by positivity
  rw [div_le_iff₀ hden]
  have hs6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hsd : Real.sqrt (1 + δ) ^ 2 = 1 + δ := Real.sq_sqrt (by linarith)
  have hk : (0 : ℝ) ≤ YX H X * (Real.sqrt 6 * H * Real.sqrt (1 + δ)) :=
    mul_nonneg hY0 (le_of_lt hden)
  -- Square both sides explicitly; `nlinarith` will not find this on its own.
  have hsq : X ≤ (YX H X * (Real.sqrt 6 * H * Real.sqrt (1 + δ))) ^ 2 := by
    have hexp : (YX H X * (Real.sqrt 6 * H * Real.sqrt (1 + δ))) ^ 2
        = YX H X ^ 2 * Real.sqrt 6 ^ 2 * H ^ 2 * Real.sqrt (1 + δ) ^ 2 := by ring
    rw [hexp, hs6, hsd]
    linarith
  calc Real.sqrt X
      ≤ Real.sqrt ((YX H X * (Real.sqrt 6 * H * Real.sqrt (1 + δ))) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = YX H X * (Real.sqrt 6 * H * Real.sqrt (1 + δ)) := Real.sqrt_sq hk

/-- `1 - 1/sqrt (1+d) ≤ d` for `0 ≤ d`: squaring, `(1-d)²(1+d) ≤ 1` reduces to
`d² ≤ 1 + d`. This is the explicit modulus that replaces a continuity argument
for `d ↦ 1/sqrt (1+d)` at `0`. -/
theorem one_sub_inv_sqrt_le {d : ℝ} (hd : 0 ≤ d) :
    1 - 1 / Real.sqrt (1 + d) ≤ d := by
  have h1 : (0 : ℝ) < 1 + d := by linarith
  have hs : (0 : ℝ) < Real.sqrt (1 + d) := Real.sqrt_pos.mpr h1
  have hsq : Real.sqrt (1 + d) ^ 2 = 1 + d := Real.sq_sqrt (le_of_lt h1)
  rcases le_or_gt 1 d with hge | hlt
  · have hle1 : 1 / Real.sqrt (1 + d) ≤ 1 := by
      rw [div_le_one hs]
      nlinarith [Real.sqrt_nonneg (1 + d)]
    have hnn : (0 : ℝ) ≤ 1 / Real.sqrt (1 + d) := by positivity
    linarith
  · -- `1 - d > 0`; show `(1 - d) * sqrt (1 + d) ≤ 1`, then divide
    have hkey : (1 - d) * Real.sqrt (1 + d) ≤ 1 := by
      nlinarith [Real.sqrt_nonneg (1 + d), hsq]
    have hstep : 1 - d ≤ 1 / Real.sqrt (1 + d) := by
      rw [le_div_iff₀ hs]; exact hkey
    linarith

/-- **The change of variable, asymptotically.** `Y_X / sqrt X → 1 / (sqrt 6 H)`.

`YX_le_sqrt` gives the exact upper bound, so the ratio never exceeds the limit.
`sqrt_le_YX` gives `1 / sqrt (1 + d)` of it for each `d > 0`, and
`one_sub_inv_sqrt_le` bounds the shortfall by `d` — so choosing `d` small
against `ε * sqrt 6 * H` closes the gap without any continuity argument. -/
theorem YX_asymptotic {H : ℝ} (hH : 0 < H) :
    Filter.Tendsto (fun X : ℝ => YX H X / Real.sqrt X) Filter.atTop
      (nhds (1 / (Real.sqrt 6 * H))) := by
  have h6 : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hden : (0 : ℝ) < Real.sqrt 6 * H := mul_pos h6 hH
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- pick `d` so the shortfall `(1/(√6 H)) * d` is below `ε`
  set d : ℝ := min 1 (ε * (Real.sqrt 6 * H) / 2) with hdd
  have hd0 : 0 < d := by
    rw [hdd]; exact lt_min one_pos (by positivity)
  have hdle : d ≤ ε * (Real.sqrt 6 * H) / 2 := by rw [hdd]; exact min_le_right _ _
  obtain ⟨X₀, hX₀⟩ := sqrt_le_YX hH hd0
  refine ⟨max X₀ 1, fun X hX => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hsX : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.mpr hXpos
  have hZ0 : ZH H 0 ≤ X := by
    have hz : ZH H 0 = 1 / 24 := by unfold ZH; norm_num
    rw [hz]; linarith
  have hsd : (0 : ℝ) < Real.sqrt (1 + d) := Real.sqrt_pos.mpr (by linarith)
  -- the two bounds on the ratio
  have hupp : YX H X / Real.sqrt X ≤ 1 / (Real.sqrt 6 * H) := by
    have h := YX_le_sqrt hH hZ0
    rw [le_div_iff₀ hden] at h
    rw [div_le_div_iff₀ hsX hden]
    linarith
  have hlow : 1 / (Real.sqrt 6 * H * Real.sqrt (1 + d)) ≤ YX H X / Real.sqrt X := by
    have h := hX₀ X (le_trans (le_max_left _ _) hX)
    rw [div_le_iff₀ (by positivity : (0:ℝ) < Real.sqrt 6 * H * Real.sqrt (1 + d))] at h
    rw [div_le_div_iff₀ (by positivity) hsX]
    linarith
  -- the shortfall is at most `(1/(√6 H)) * d ≤ ε/2 < ε`
  have hgap : 1 / (Real.sqrt 6 * H) - 1 / (Real.sqrt 6 * H * Real.sqrt (1 + d))
      ≤ 1 / (Real.sqrt 6 * H) * d := by
    have hfac : 1 / (Real.sqrt 6 * H * Real.sqrt (1 + d))
        = 1 / (Real.sqrt 6 * H) * (1 / Real.sqrt (1 + d)) := by
      field_simp
    rw [hfac]
    have := one_sub_inv_sqrt_le (le_of_lt hd0)
    have hpos : (0 : ℝ) < 1 / (Real.sqrt 6 * H) := by positivity
    nlinarith
  have hhalf : 1 / (Real.sqrt 6 * H) * d ≤ ε / 2 := by
    have hpos : (0 : ℝ) < 1 / (Real.sqrt 6 * H) := by positivity
    have : d ≤ ε * (Real.sqrt 6 * H) / 2 := hdle
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hden] at *
    nlinarith
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  linarith

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# The partition function and its odd-value counting function

This file fixes the two objects the corollary of Qi-Yang Zheng is stated about:
the partition function `p` and the counting function `N_odd`.

## Main definitions

* `PartitionZheng.pFun n` — the number of partitions of `n`.
* `PartitionZheng.Nodd X` — the number of `n ≤ X` with `p n` odd.
-/


namespace PartitionZheng

/-- The partition function `p n`: the number of partitions of `n`. -/
private def pFun (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- `Nodd X` counts the integers `0 ≤ n ≤ X` whose partition number is odd,
written `N_odd(X)` in the source. Oddness is spelled `pFun n % 2 = 1` so that
the predicate is decidable without an instance argument. -/
private def Nodd (X : ℕ) : ℕ :=
  ((Finset.range (X + 1)).filter fun n => pFun n % 2 = 1).card

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# Recovering the discriminant from the partition index

Zheng's injectivity step: the map `D ↦ n_D` is injective because `D` can be
recovered from `n_D`. Concretely `24 * n - 1 = D * m ^ 2`, and since `D` is
square-free the primes dividing `D * m ^ 2` to an odd power are exactly those
dividing `D`, whose product is `D` again.

## Main results

* `PartitionZheng.odd_factorization_iff` — the exponent of `q` in `D * m ^ 2`
  is odd exactly when `q ∣ D`.
* `PartitionZheng.sqfPart_mul_sq` — hence `sqfPart (D * m ^ 2) = D`.
* `PartitionZheng.recover_disc` — hence `sqfPart (24 * n - 1) = D`.
-/


namespace PartitionZheng

/-- For square-free `D` and `m ≠ 0`, the exponent of a prime `q` in `D * m ^ 2`
is odd exactly when `q ∣ D`: the exponent is `D.factorization q + 2 * _`, and
square-freeness pins the first summand to `0` or `1`. -/
theorem odd_factorization_iff {D m q : ℕ} (hD : Squarefree D) (hm : m ≠ 0)
    (hq : q.Prime) :
    Odd ((D * m ^ 2).factorization q) ↔ q ∣ D := by
  have hD0 : D ≠ 0 := hD.ne_zero
  have hpow : (m ^ 2) ≠ 0 := pow_ne_zero 2 hm
  have hfac : (D * m ^ 2).factorization q
      = D.factorization q + 2 * m.factorization q := by
    rw [Nat.factorization_mul hD0 hpow, Nat.factorization_pow]
    simp
  have hle : D.factorization q ≤ 1 :=
    (Nat.squarefree_iff_factorization_le_one hD0).mp hD q
  rw [hfac, Nat.odd_iff, hq.dvd_iff_one_le_factorization hD0]
  omega

/-- The square-free part of `D * m ^ 2` is `D`, for square-free `D`. -/
theorem sqfPart_mul_sq {D m : ℕ} (hD : Squarefree D) (hm : m ≠ 0) :
    sqfPart (D * m ^ 2) = D := by
  have hD0 : D ≠ 0 := hD.ne_zero
  have hpow : (m ^ 2) ≠ 0 := pow_ne_zero 2 hm
  have hne : D * m ^ 2 ≠ 0 := mul_ne_zero hD0 hpow
  unfold sqfPart
  -- Replace the parity test by divisibility of `D`, which is what it means.
  have hstep : ∀ q ∈ (D * m ^ 2).primeFactors,
      (if Odd ((D * m ^ 2).factorization q) then q else 1)
        = (if q ∣ D then q else 1) := by
    intro q hq
    have hqp : q.Prime := (Nat.mem_primeFactors.mp hq).1
    by_cases hdvd : q ∣ D
    · have : Odd ((D * m ^ 2).factorization q) :=
        (odd_factorization_iff hD hm hqp).mpr hdvd
      simp [this, hdvd]
    · have hnodd : ¬ Odd ((D * m ^ 2).factorization q) := fun h =>
        hdvd ((odd_factorization_iff hD hm hqp).mp h)
      simp [hnodd, hdvd]
  rw [Finset.prod_congr rfl hstep, ← Finset.prod_filter]
  -- The primes of `D * m ^ 2` that divide `D` are exactly the primes of `D`.
  have hfilter : ((D * m ^ 2).primeFactors.filter fun q => q ∣ D) = D.primeFactors := by
    ext q
    simp only [Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hqp, _, _⟩, hdvd⟩
      exact ⟨hqp, hdvd, hD0⟩
    · rintro ⟨hqp, hdvd, _⟩
      exact ⟨⟨hqp, hdvd.trans (dvd_mul_right D (m ^ 2)), hne⟩, hdvd⟩
  rw [hfilter, Nat.prod_primeFactors_of_squarefree hD]

/-- The discriminant is recovered from the partition index: if `D` is square-free
and `24 * n = D * m ^ 2 + 1`, then `sqfPart (24 * n - 1) = D`. This is what
makes `D ↦ n_D` injective. -/
theorem recover_disc {D m n : ℕ} (hD : Squarefree D) (hm : m ≠ 0)
    (h : 24 * n = D * m ^ 2 + 1) : sqfPart (24 * n - 1) = D := by
  have : 24 * n - 1 = D * m ^ 2 := by omega
  rw [this]
  exact sqfPart_mul_sq hD hm

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# From good discriminants to odd values

This is the counting step. The parity theorem supplies, for each admissible
discriminant `D`, an `m` bounded in terms of the class number and an `n` with
`24 n = D m² + 1` and `p n` odd. For a *good* `D` the bound on `m` makes
`n ≤ Z_H Y`, and `D` is recoverable from `n` as the square-free part of
`24 n - 1`, so distinct good `D` give distinct `n`. Counting the `n` gives the
lower bound on `N_odd`.

## The one external input

`ParityInput` is the statement of the paper's main theorem, odd half only — the
single result this development assumes. It is a `Prop`, not an `axiom`: every
consumer takes it as an explicit hypothesis, so it never enters the kernel's
axiom list and `#print axioms` stays clean on everything below. Only the odd
half is stated; the appendix uses neither the companion bound on the least `m`
giving an even value nor the infinitude claim.

## Main definitions

* `PartitionZheng.ParityInput` — the assumed parity theorem.

## Main results

* `PartitionZheng.Nodd_lower` — `#good(Y,H) ≤ N_odd ⌊Z_H Y⌋`.
-/


namespace PartitionZheng

open Real

/-- The parity theorem of Ono and Swaminathan, **odd half only**: for square-free
`D > 1` with `D ≡ 23 [MOD 24]` there are `m` coprime to `6` with
`m ≤ 12 h(D) + 2`, and `n` with `24 n = D m² + 1` and `p n` odd.

This is the development's single external input. Stated as a `Prop` and taken as
a hypothesis by every consumer, so it never becomes an axiom. -/
private def ParityInput : Prop :=
  ∀ D : ℕ, 1 < D → Squarefree D → D % 24 = 23 →
    ∃ m n : ℕ, 1 ≤ m ∧ Nat.Coprime m 6 ∧
      m ≤ 12 * classNumber (D : ℤ) + 2 ∧ 24 * n = D * m ^ 2 + 1 ∧ Odd (pFun n)

/-- Each good discriminant yields a distinct `n ≤ Z_H Y` with `p n` odd, so
`N_odd` at `Z_H Y` is at least the number of good discriminants. -/
theorem Nodd_lower (hp : ParityInput) {Y H : ℝ} (hY : 0 ≤ Y) :
    (good Y H).card ≤ Nodd ⌊ZH H Y⌋₊ := by
  classical
  -- Choose, for every `D`, the witnesses the parity theorem provides.
  choose! mw nw hm1 hmcop hmle hneq hnodd using hp
  refine Finset.card_le_card_of_injOn nw ?_ ?_
  · -- every good `D` maps into the set `Nodd` counts
    intro D hD
    obtain ⟨hDadm, hDh⟩ := mem_good_iff.mp hD
    obtain ⟨⟨hD2, hDfl⟩, hD24, hDsqf⟩ := mem_admissible.mp hDadm
    have hD1 : 1 < D := by omega
    have hDY : (D : ℝ) ≤ Y := by
      have : ((D : ℝ)) ≤ ((⌊Y⌋₊ : ℝ)) := by exact_mod_cast hDfl
      exact this.trans (Nat.floor_le hY)
    -- the bound on `m`, pushed through the class-number bound
    have hmR : ((mw D : ℕ) : ℝ) ≤ 12 * H * Real.sqrt Y + 2 := by
      have h := hmle D hD1 hDsqf hD24
      have hcast : ((mw D : ℕ) : ℝ)
          ≤ 12 * (classNumber (D : ℤ) : ℝ) + 2 := by exact_mod_cast h
      have : 12 * (classNumber (D : ℤ) : ℝ) ≤ 12 * (H * Real.sqrt Y) := by linarith
      linarith
    have hbound : ((nw D : ℕ) : ℝ) ≤ ZH H Y :=
      nD_le_ZH hY hDY hmR (hneq D hD1 hDsqf hD24)
    have hfloor : nw D ≤ ⌊ZH H Y⌋₊ := Nat.le_floor hbound
    have hodd := hnodd D hD1 hDsqf hD24
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Nat.odd_iff.mp hodd⟩
  · -- injective: `D` is the square-free part of `24 * n - 1`
    intro D hD D' hD' heq
    obtain ⟨hDadm, _⟩ := mem_good_iff.mp (Finset.mem_coe.mp hD)
    obtain ⟨hD'adm, _⟩ := mem_good_iff.mp (Finset.mem_coe.mp hD')
    obtain ⟨⟨hD2, _⟩, hD24, hDsqf⟩ := mem_admissible.mp hDadm
    obtain ⟨⟨hD'2, _⟩, hD'24, hD'sqf⟩ := mem_admissible.mp hD'adm
    have hD1 : 1 < D := by omega
    have hD'1 : 1 < D' := by omega
    have hrec : sqfPart (24 * nw D - 1) = D :=
      recover_disc hDsqf (by have := hm1 D hD1 hDsqf hD24; omega)
        (hneq D hD1 hDsqf hD24)
    have hrec' : sqfPart (24 * nw D' - 1) = D' :=
      recover_disc hD'sqf (by have := hm1 D' hD'1 hD'sqf hD'24; omega)
        (hneq D' hD'1 hD'sqf hD'24)
    rw [← hrec, ← hrec', heq]

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# Few discriminants have a large class number

A discriminant is *bad* for the threshold `H` when its class number exceeds
`H * sqrt Y`, the complement in `admissible Y` of the good ones. Since every bad
discriminant contributes more than `H * sqrt Y` to `∑_{D ∈ D(Y)} h(D)` and all
terms of that sum are nonnegative, the class-number average bounds the number of
bad discriminants: dividing `(beta + ε H) Y ^ (3/2)` by `H sqrt Y` leaves
`(beta / H + ε) Y`.

`Y ^ (3/2)` is written `Y * sqrt Y`, as in `PartitionZheng.ZH`.

## Main definitions

* `PartitionZheng.bad` — the bad discriminants up to `Y`.

## Main results

* `PartitionZheng.bad_count` — `#bad(Y,H) ≤ (beta / H + ε) Y` for `Y` large.
-/


namespace PartitionZheng

open Real

open Classical in
/-- The bad discriminants up to `Y`: those whose class number exceeds
`H * sqrt Y`. This is the complement in `admissible Y` of `good Y H`. -/
private noncomputable def bad (Y H : ℝ) : Finset ℕ :=
  (admissible Y).filter fun D => (H * Real.sqrt Y < (classNumber (D : ℤ) : ℝ))

/-- A natural number lies in `bad Y H` exactly when it is admissible up to `Y`
and its class number exceeds `H * sqrt Y`. -/
theorem mem_bad_iff {Y H : ℝ} {D : ℕ} :
    D ∈ bad Y H ↔ D ∈ admissible Y ∧ (H * Real.sqrt Y < (classNumber (D : ℤ) : ℝ)) := by
  classical
  simp [bad, Finset.mem_filter]

/-- Every admissible discriminant is good or bad, so the two counts together
cover `#D(Y)`. -/
theorem card_admissible_le_card_good_add_card_bad {Y H : ℝ} :
    (admissible Y).card ≤ (good Y H).card + (bad Y H).card := by
  classical
  calc (admissible Y).card ≤ (good Y H ∪ bad Y H).card := by
        refine Finset.card_le_card ?_
        intro D hD
        rcases le_or_gt ((classNumber (D : ℤ) : ℝ)) (H * Real.sqrt Y) with h | h
        · exact Finset.mem_union_left _ (mem_good_iff.mpr ⟨hD, h⟩)
        · exact Finset.mem_union_right _ (mem_bad_iff.mpr ⟨hD, h⟩)
    _ ≤ (good Y H).card + (bad Y H).card := Finset.card_union_le _ _

/-- The bad discriminants each contribute more than `H * sqrt Y` to the
class-number sum over `admissible Y`, whose other terms are nonnegative. -/
theorem card_bad_mul_le_sum {Y H : ℝ} :
    ((bad Y H).card : ℝ) * (H * Real.sqrt Y)
      ≤ ∑ D ∈ admissible Y, (classNumber (D : ℤ) : ℝ) := by
  classical
  calc ((bad Y H).card : ℝ) * (H * Real.sqrt Y)
      = (bad Y H).card • (H * Real.sqrt Y) := by rw [nsmul_eq_mul]
    _ ≤ ∑ D ∈ bad Y H, (classNumber (D : ℤ) : ℝ) := by
        refine Finset.card_nsmul_le_sum _ _ _ ?_
        intro D hD
        exact le_of_lt (mem_bad_iff.mp hD).2
    _ ≤ ∑ D ∈ admissible Y, (classNumber (D : ℤ) : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro D _ _
        positivity

/-- **`lem_bad_count`.** For every `ε > 0` the number of discriminants up to `Y`
whose class number exceeds `H * sqrt Y` is at most `(beta / H + ε) * Y`, once
`Y` is large.

The hypothesis `hclass` asserts the class-number average: for every `ε > 0`,
`∑_{D ∈ D(Y)} h(D) ≤ (beta + ε) Y ^ (3/2)` once `Y` is large. -/
theorem bad_count {H : ℝ} (hH : 0 < H)
    (hclass : ∀ ε : ℝ, 0 < ε → ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      ∑ D ∈ admissible Y, (classNumber (D : ℤ) : ℝ) ≤ (beta + ε) * (Y * Real.sqrt Y))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      ((bad Y H).card : ℝ) ≤ (beta / H + ε) * Y := by
  obtain ⟨Y₀, hY₀, hbound⟩ := hclass (ε * H) (by positivity)
  refine ⟨Y₀, hY₀, fun Y hY => ?_⟩
  have hY2 : (2 : ℝ) ≤ Y := le_trans hY₀ hY
  have hY0 : (0 : ℝ) < Y := by linarith
  have hs : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY0
  have hK : 0 < H * Real.sqrt Y := by positivity
  have hne : H ≠ 0 := ne_of_gt hH
  have hrw : (beta / H + ε) * Y * (H * Real.sqrt Y)
      = (beta + ε * H) * (Y * Real.sqrt Y) := by
    field_simp
  refine le_of_mul_le_mul_right ?_ hK
  rw [hrw]
  exact le_trans card_bad_mul_le_sum (hbound Y hY)

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# Many good discriminants

The good discriminants are what is left of `admissible Y` after the bad ones are
removed, so their number is at least `#D(Y)` minus the number of bad ones. The
count of admissible discriminants supplies `#D(Y) ≥ delta * Y - C * sqrt Y` and
`bad_count` supplies `#bad(Y,H) ≤ (beta / H + ε / 2) * Y`; the error term
`C * sqrt Y` is absorbed into `(ε / 2) * Y` once `Y ≥ (2C/ε)²`.

## Main results

* `PartitionZheng.sqrt_error_le` — `C * sqrt Y ≤ (ε / 2) * Y` once
  `Y ≥ (2C/ε)²`.
* `PartitionZheng.good_count` — `#good(Y,H) ≥ (delta - beta / H - ε) Y` for `Y`
  large.
-/


namespace PartitionZheng

open Real

/-- A square-root error term is eventually below a linear one: `C * sqrt Y` is at
most `(ε / 2) * Y` as soon as `Y ≥ (2C/ε)²`. -/
theorem sqrt_error_le {C ε Y : ℝ} (hε : 0 < ε) (hY : (2 * C / ε) ^ 2 ≤ Y) :
    C * Real.sqrt Y ≤ ε / 2 * Y := by
  have hY0 : (0 : ℝ) ≤ Y := le_trans (sq_nonneg _) hY
  have hss : Real.sqrt Y * Real.sqrt Y = Y := Real.mul_self_sqrt hY0
  rcases le_or_gt C 0 with hC | hC
  · have h1 : C * Real.sqrt Y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC (Real.sqrt_nonneg Y)
    have h2 : (0 : ℝ) ≤ ε / 2 * Y := by positivity
    linarith
  · have h1 : 2 * C / ε ≤ Real.sqrt Y := by
      rw [show 2 * C / ε = Real.sqrt ((2 * C / ε) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt hY
    rw [div_le_iff₀ hε] at h1
    nlinarith [Real.sqrt_nonneg Y]

/-- **`lem_good_count`.** For every `ε > 0` the number of good discriminants up
to `Y` is at least `(delta - beta / H - ε) * Y`, once `Y` is large.

The hypothesis `hDset` asserts the count of admissible discriminants,
`|#D(Y) - delta * Y| ≤ C * sqrt Y` for some `C > 0`, and `hclass` asserts the
class-number average, `∑_{D ∈ D(Y)} h(D) ≤ (beta + ε) Y ^ (3/2)` for every
`ε > 0` once `Y` is large. -/
theorem good_count {H : ℝ} (hH : 0 < H)
    (hDset : ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 1 ≤ Y →
      |((admissible Y).card : ℝ) - delta * Y| ≤ C * Real.sqrt Y)
    (hclass : ∀ ε : ℝ, 0 < ε → ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      ∑ D ∈ admissible Y, (classNumber (D : ℤ) : ℝ) ≤ (beta + ε) * (Y * Real.sqrt Y))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      (delta - beta / H - ε) * Y ≤ ((good Y H).card : ℝ) := by
  obtain ⟨C, _, hDcard⟩ := hDset
  obtain ⟨Y₁, hY₁, hbad⟩ := bad_count hH hclass (half_pos hε)
  refine ⟨max Y₁ (max 2 ((2 * C / ε) ^ 2)), ?_, fun Y hY => ?_⟩
  · exact le_trans (le_max_left 2 _) (le_max_right Y₁ _)
  · have hY1' : Y₁ ≤ Y := le_trans (le_max_left _ _) hY
    have hY2 : (2 : ℝ) ≤ Y := le_trans (le_trans (le_max_left 2 _) (le_max_right Y₁ _)) hY
    have hYsq : (2 * C / ε) ^ 2 ≤ Y :=
      le_trans (le_trans (le_max_right 2 _) (le_max_right Y₁ _)) hY
    have hadm : delta * Y - C * Real.sqrt Y ≤ ((admissible Y).card : ℝ) := by
      have h := abs_le.mp (hDcard Y (by linarith))
      linarith [h.1]
    have hb := hbad Y hY1'
    have hsplit : ((admissible Y).card : ℝ)
        ≤ ((good Y H).card : ℝ) + ((bad Y H).card : ℝ) := by
      have h := card_admissible_le_card_good_add_card_bad (Y := Y) (H := H)
      exact_mod_cast h
    have herr : C * Real.sqrt Y ≤ ε / 2 * Y := sqrt_error_le hε hYsq
    have hexp : (beta / H + ε / 2) * Y = beta / H * Y + ε / 2 * Y := by ring
    rw [hexp] at hb
    have hgoal : (delta - beta / H - ε) * Y
        = delta * Y - beta / H * Y - ε / 2 * Y - ε / 2 * Y := by ring
    rw [hgoal]
    linarith

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# Limits inferior of real functions, formed in `EReal`

The corollary bounds `liminf_{X → ∞} N_odd(X) / sqrt X` from below. That limit
inferior is taken in `EReal`, not in `ℝ`, and the reason is not cosmetic:
`Filter.liminf` is `sSup {a | ∀ᶠ X, a ≤ u X}`, and `Real.sSup` of a set
unbounded above is the junk value `0`. Nothing available bounds
`N_odd(X) / sqrt X` from above — the expected truth is that it tends to infinity,
which would make the set unbounded and the real-valued limit inferior equal to
`0`. In `EReal`, a complete lattice, the limit inferior always exists and agrees
with the classical one, so the inequality means what it says.

## Main results

* `PartitionZheng.le_liminf_of_eventually_sub_le` — an `ε`-`δ` lower bound gives
  a lower bound on the limit inferior.
-/


namespace PartitionZheng

/-- If for every `ε > 0` the function `u` is eventually at least `c - ε`, then
its limit inferior at infinity, formed in `EReal`, is at least `c`.

This is the passage from the explicit quantified form in which the argument
produces its estimates to the limit inferior the statement is about. -/
theorem le_liminf_of_eventually_sub_le {c : ℝ} {u : ℝ → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ X in Filter.atTop, c - ε ≤ u X) :
    (c : EReal) ≤ Filter.liminf (fun X : ℝ => ((u X : ℝ) : EReal)) Filter.atTop := by
  have key : ∀ r : ℝ, r < c →
      ((r : ℝ) : EReal) ≤ Filter.liminf (fun X : ℝ => ((u X : ℝ) : EReal)) Filter.atTop := by
    intro r hr
    have hev : ∀ᶠ X in Filter.atTop, ((r : ℝ) : EReal) ≤ ((u X : ℝ) : EReal) := by
      filter_upwards [h (c - r) (by linarith)] with X hX
      exact EReal.coe_le_coe_iff.mpr (by linarith)
    exact Filter.le_liminf_of_le (h := hev)
  refine le_of_forall_lt ?_
  intro z
  induction z using EReal.rec with
  | bot =>
      intro _
      exact lt_of_lt_of_le (EReal.bot_lt_coe (c - 1)) (key (c - 1) (by linarith))
  | coe r =>
      intro hz
      have hrc : r < c := EReal.coe_lt_coe_iff.mp hz
      exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr (by linarith : r < (r + c) / 2))
        (key ((r + c) / 2) (by linarith))
  | top => intro hz; exact absurd hz not_top_lt

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# The lower bound at a fixed threshold

For a threshold `H` with `delta - beta / H > 0` the argument closes. Write
`A = delta - beta / H` and `K = 1 / (sqrt 6 * H)`. At `X = Z_H(Y_X)` the counting
step gives `N_odd(X) ≥ #good(Y_X, H)`, the count of good discriminants gives
`#good(Y_X, H) ≥ (A - ε₁) Y_X`, and the change of variable gives
`Y_X / sqrt X ≥ K - ε₂`. Multiplying,

`N_odd(X) / sqrt X ≥ (A - ε₁)(K - ε₂) ≥ A * K - ε`

once `ε₁ * K ≤ ε / 2` and `A * ε₂ ≤ ε / 2`, which is what the choices
`ε₁ = min A (ε / (2K))` and `ε₂ = min K (ε / (2A))` arrange; the two minima also
keep both factors nonnegative, which is what lets the product be bounded.

The two counting inputs enter as explicit hypotheses: `hDset` says the number of
admissible discriminants up to `Y` is `delta * Y` up to an error `O(sqrt Y)`, and
`hclass` that for every `ε > 0` the class numbers of those discriminants sum to
at most `(beta + ε) * Y * sqrt Y` once `Y` is large. `hp` is the parity theorem
`ParityInput`.

## Main results

* `PartitionZheng.Nodd_eventually_ge` — the explicit quantified form.
* `PartitionZheng.liminf_Nodd_ge` — the limit inferior at a fixed threshold.
-/


namespace PartitionZheng

open Real

/-- At `X = Z_H(Y_X)`, `N_odd(X)` is at least the number of good discriminants
up to `Y_X`. -/
theorem card_good_le_Nodd (hp : ParityInput) {H X : ℝ} (hH : 0 < H)
    (hX : ZH H 0 ≤ X) : ((good (YX H X) H).card : ℝ) ≤ (Nodd ⌊X⌋₊ : ℝ) := by
  obtain ⟨hY0, heq⟩ := YX_spec hH hX
  have h := Nodd_lower hp (Y := YX H X) (H := H) hY0
  rw [heq] at h
  exact_mod_cast h

/-- For a threshold `H` with `delta - beta / H > 0` and every `ε > 0`, the ratio
`N_odd(X) / sqrt X` is eventually at least `(delta - beta / H) / (sqrt 6 * H) - ε`. -/
theorem Nodd_eventually_ge (hp : ParityInput) {H : ℝ} (hH : 0 < H)
    (hadm : 0 < delta - beta / H)
    (hDset : ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 1 ≤ Y →
      |((admissible Y).card : ℝ) - delta * Y| ≤ C * Real.sqrt Y)
    (hclass : ∀ ε : ℝ, 0 < ε → ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      ∑ D ∈ admissible Y, (classNumber (D : ℤ) : ℝ) ≤ (beta + ε) * (Y * Real.sqrt Y))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X in Filter.atTop,
      (delta - beta / H) / (Real.sqrt 6 * H) - ε ≤ (Nodd ⌊X⌋₊ : ℝ) / Real.sqrt X := by
  have h6 : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hden : (0 : ℝ) < Real.sqrt 6 * H := mul_pos h6 hH
  set A : ℝ := delta - beta / H with hAdef
  set K : ℝ := 1 / (Real.sqrt 6 * H) with hKdef
  have hK : 0 < K := by rw [hKdef]; positivity
  -- the two slacks, chosen so that `ε₁ * K` and `A * ε₂` are each at most `ε / 2`
  set ε₁ : ℝ := min A (ε / (2 * K)) with hε₁def
  set ε₂ : ℝ := min K (ε / (2 * A)) with hε₂def
  have hε₁ : 0 < ε₁ := by rw [hε₁def]; exact lt_min hadm (by positivity)
  have hε₂ : 0 < ε₂ := by rw [hε₂def]; exact lt_min hK (by positivity)
  have hA1 : 0 ≤ A - ε₁ := by
    have : ε₁ ≤ A := by rw [hε₁def]; exact min_le_left _ _
    linarith
  have hε₁K : ε₁ * K ≤ ε / 2 := by
    have h1 : ε₁ ≤ ε / (2 * K) := by rw [hε₁def]; exact min_le_right _ _
    have h2 : ε / (2 * K) * K = ε / 2 := by field_simp
    calc ε₁ * K ≤ ε / (2 * K) * K := mul_le_mul_of_nonneg_right h1 hK.le
      _ = ε / 2 := h2
  have hAε₂ : A * ε₂ ≤ ε / 2 := by
    have h1 : ε₂ ≤ ε / (2 * A) := by rw [hε₂def]; exact min_le_right _ _
    have h2 : A * (ε / (2 * A)) = ε / 2 := by field_simp
    calc A * ε₂ ≤ A * (ε / (2 * A)) := mul_le_mul_of_nonneg_left h1 hadm.le
      _ = ε / 2 := h2
  have hprod : A * K - ε ≤ (A - ε₁) * (K - ε₂) := by
    nlinarith [mul_pos hε₁ hε₂]
  obtain ⟨Y₀, hY₀, hgood⟩ := good_count hH hDset hclass hε₁
  have hlim := YX_asymptotic hH
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨X₁, hX₁⟩ := hlim ε₂ hε₂
  refine Filter.eventually_atTop.mpr ⟨max (max X₁ (ZH H Y₀)) 1, fun X hX => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := le_trans (le_max_right _ _) hX
  have hsX : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.mpr (by linarith)
  have hZ0 : ZH H 0 ≤ X := by
    have hz : ZH H 0 = 1 / 24 := by unfold ZH; norm_num
    rw [hz]; linarith
  have hXY₀ : ZH H Y₀ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hYbig : Y₀ ≤ YX H X := le_YX hH (by linarith) hXY₀
  -- `N_odd(X) ≥ #good(Y_X, H) ≥ (A - ε₁) Y_X`
  have hNodd : (A - ε₁) * YX H X ≤ (Nodd ⌊X⌋₊ : ℝ) :=
    le_trans (hgood (YX H X) hYbig) (card_good_le_Nodd hp hH hZ0)
  -- `Y_X / sqrt X ≥ K - ε₂`
  have hratio : (K - ε₂) * Real.sqrt X ≤ YX H X := by
    have h := hX₁ X (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX)
    rw [Real.dist_eq, abs_lt] at h
    have h1 : K - ε₂ ≤ YX H X / Real.sqrt X := by
      rw [hKdef]; linarith [h.1]
    rw [← le_div_iff₀ hsX]
    exact h1
  have hAK : A / (Real.sqrt 6 * H) = A * K := by rw [hKdef, mul_one_div]
  rw [le_div_iff₀ hsX, hAK]
  have hstep1 : (A * K - ε) * Real.sqrt X ≤ (A - ε₁) * (K - ε₂) * Real.sqrt X :=
    mul_le_mul_of_nonneg_right hprod hsX.le
  have hstep2 : (A - ε₁) * (K - ε₂) * Real.sqrt X ≤ (A - ε₁) * YX H X := by
    calc (A - ε₁) * (K - ε₂) * Real.sqrt X = (A - ε₁) * ((K - ε₂) * Real.sqrt X) := by ring
      _ ≤ (A - ε₁) * YX H X := mul_le_mul_of_nonneg_left hratio hA1
  linarith

/-- **`lem_liminf_H`.** For a threshold `H` with `delta - beta / H > 0`,

`liminf_{X → ∞} N_odd(X) / sqrt X ≥ (delta - beta / H) / (sqrt 6 * H)`.

The limit inferior is formed in `EReal`; see `le_liminf_of_eventually_sub_le` for
why the real-valued one would be junk. -/
theorem liminf_Nodd_ge (hp : ParityInput) {H : ℝ} (hH : 0 < H)
    (hadm : 0 < delta - beta / H)
    (hDset : ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 1 ≤ Y →
      |((admissible Y).card : ℝ) - delta * Y| ≤ C * Real.sqrt Y)
    (hclass : ∀ ε : ℝ, 0 < ε → ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      ∑ D ∈ admissible Y, (classNumber (D : ℤ) : ℝ) ≤ (beta + ε) * (Y * Real.sqrt Y)) :
    (((delta - beta / H) / (Real.sqrt 6 * H) : ℝ) : EReal) ≤
      Filter.liminf (fun X : ℝ => (((Nodd ⌊X⌋₊ : ℝ) / Real.sqrt X : ℝ) : EReal))
        Filter.atTop :=
  le_liminf_of_eventually_sub_le fun _ hδ => Nodd_eventually_ge hp hH hadm hDset hclass hδ

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# The optimal threshold and the constant

The lower bound of the argument is `(delta - beta / H) / (sqrt 6 * H)` for any
threshold `H > beta / delta`. This file maximises it. The maximum is at
`H = 2 * beta / delta`, where the value is `delta ^ 2 / (4 * beta * sqrt 6)`,
and that equals `243 / (64 * sqrt 6 * pi ^ 5)`.

The `sqrt 6` is a constant factor common to both sides, so every statement here
is phrased with it divided out: `H_admissible` and `optimal_value` are about
`(delta - beta / H) / H`, and `constant_value` about
`delta ^ 2 / (4 * beta)`. Reinstating the factor is a single division, done
where the limit inferior is assembled. This keeps the arithmetic exact and this
module's imports small.

## Main results

* `PartitionZheng.H_admissible` — the optimal threshold is admissible.
* `PartitionZheng.optimal_value` — the value there, `delta ^ 2 / (4 * beta)`.
* `PartitionZheng.constant_value` — that equals `243 / (64 * pi ^ 5)`.
-/


namespace PartitionZheng

open Real

/-- At the optimal threshold `H = 2 * beta / delta` the numerator
`delta - beta / H` equals `delta / 2`, which is positive; so the threshold is
admissible, i.e. it exceeds `beta / delta`. -/
theorem H_admissible : 0 < delta - beta / (2 * beta / delta) := by
  have hb : beta ≠ 0 := ne_of_gt beta_pos
  have hd : delta ≠ 0 := ne_of_gt delta_pos
  have key : beta / (2 * beta / delta) = delta / 2 := by
    field_simp
  rw [key]
  have := delta_pos
  linarith

/-- The value at the optimal threshold, with the common `sqrt 6` divided out. -/
theorem optimal_value :
    (delta - beta / (2 * beta / delta)) / (2 * beta / delta)
      = delta ^ 2 / (4 * beta) := by
  have hb : beta ≠ 0 := ne_of_gt beta_pos
  have hd : delta ≠ 0 := ne_of_gt delta_pos
  field_simp
  ring

/-- The constant: `delta ^ 2 / (4 * beta) = 243 / (64 * pi ^ 5)`. With the
`sqrt 6` reinstated this is the corollary's `243 / (64 * sqrt 6 * pi ^ 5)`. -/
theorem constant_value : delta ^ 2 / (4 * beta) = 243 / (64 * π ^ 5) := by
  have hpi : π ≠ 0 := ne_of_gt pi_pos
  unfold delta beta
  field_simp
  ring

end PartitionZheng

end

section

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Axiom Math
-/


/-
# Zheng's lower bound

The corollary of Qi-Yang Zheng: the number of `n ≤ X` with `p n` odd is at least
`(243 / (64 * sqrt 6 * pi ^ 5) + o(1)) * sqrt X`, in the sense that

`liminf_{X → ∞} N_odd(X) / sqrt X ≥ 243 / (64 * sqrt 6 * pi ^ 5)`.

The bound of `liminf_Nodd_ge` holds for every threshold `H` with
`delta - beta / H > 0`; this file takes `H = 2 * beta / delta`, admissible by
`H_admissible`, where `optimal_value` and `constant_value` identify the bound as
`delta ^ 2 / (4 * beta * sqrt 6) = 243 / (64 * sqrt 6 * pi ^ 5)`.

## Main results

* `PartitionZheng.liminf_Nodd_ge_const` — the corollary.
* `PartitionZheng.Nodd_eventually_ge_const` — its explicit quantified form.
-/


namespace PartitionZheng

open Real

/-- At the threshold `H = 2 * beta / delta`,
`(delta - beta / H) / (sqrt 6 * H) = 243 / (64 * sqrt 6 * pi ^ 5)`. -/
theorem optimal_bound_eq :
    (delta - beta / (2 * beta / delta)) / (Real.sqrt 6 * (2 * beta / delta))
      = 243 / (64 * Real.sqrt 6 * π ^ 5) := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have h6 : Real.sqrt 6 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have h1 : (delta - beta / (2 * beta / delta)) / (Real.sqrt 6 * (2 * beta / delta))
      = (delta - beta / (2 * beta / delta)) / (2 * beta / delta) / Real.sqrt 6 := by
    rw [mul_comm (Real.sqrt 6) (2 * beta / delta), ← div_div]
  rw [h1, optimal_value, constant_value]
  field_simp

/-- The optimal threshold is positive. -/
theorem optimal_threshold_pos : 0 < 2 * beta / delta := by
  have hb := beta_pos
  have hd := delta_pos
  positivity

/-- **`thm_main`. Zheng's lower bound.**

`liminf_{X → ∞} N_odd(X) / sqrt X ≥ 243 / (64 * sqrt 6 * pi ^ 5)`,

the limit inferior being over real `X` and formed in `EReal` (see
`le_liminf_of_eventually_sub_le`: the real-valued limit inferior of an
expression with no available upper bound is the junk value `0`).

The hypothesis `hp` is the parity theorem `ParityInput`; the count of the
admissible discriminants and the average of their class numbers come from
`card_admissible_sub_delta_le` and `class_average_unconditional`. -/
theorem liminf_Nodd_ge_const (hp : ParityInput) :
    ((243 / (64 * Real.sqrt 6 * π ^ 5) : ℝ) : EReal) ≤
      Filter.liminf (fun X : ℝ => (((Nodd ⌊X⌋₊ : ℝ) / Real.sqrt X : ℝ) : EReal))
        Filter.atTop := by
  rw [← optimal_bound_eq]
  exact liminf_Nodd_ge hp optimal_threshold_pos H_admissible
    card_admissible_sub_delta_le class_average_unconditional

/-- For every `ε > 0` the ratio `N_odd(X) / sqrt X` is eventually at least
`243 / (64 * sqrt 6 * pi ^ 5) - ε`, with `hp` the parity theorem
`ParityInput`. -/
theorem Nodd_eventually_ge_const (hp : ParityInput)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X in Filter.atTop,
      243 / (64 * Real.sqrt 6 * π ^ 5) - ε ≤ (Nodd ⌊X⌋₊ : ℝ) / Real.sqrt X := by
  rw [← optimal_bound_eq]
  exact Nodd_eventually_ge hp optimal_threshold_pos H_admissible
    card_admissible_sub_delta_le class_average_unconditional hε

end PartitionZheng

end

namespace OMA.R_PartitionParity_zheng_odd_R1_H1_R1

open scoped BigOperators
open Filter

private theorem reduced_form_count_eq (D : ℕ) :
    PartitionZheng.classNumber (D : ℤ) =
      {p : ℤ × ℤ × ℤ | PartitionParity.IsReducedForm D p.1 p.2.1 p.2.2}.ncard := by
  unfold PartitionZheng.classNumber
  congr 1
  ext ⟨a, b, c⟩
  change PartitionZheng.IsReducedForm (D : ℤ) a b c ↔ PartitionParity.IsReducedForm D a b c
  unfold PartitionZheng.IsReducedForm PartitionZheng.IsReducedTriple PartitionParity.IsReducedForm
  constructor
  · rintro ⟨⟨hb, hc, hD⟩, hprim, hboundary⟩
    exact ⟨by linarith, hb, hc, hprim, hboundary⟩
  · rintro ⟨hD, hb, hc, hprim, hboundary⟩
    exact ⟨⟨hb, hc, by linarith⟩, hprim, hboundary⟩

private theorem numerator_dvd {D m : ℕ} (hD : D % 24 = 23) (hm : m.Coprime 6) :
    24 ∣ D * m^2 + 1 := by
  have hnd (p : ℕ) (hp6 : p ∣ 6) (hp1 : ¬ p ∣ 1) : ¬ p ∣ m := by
    intro he
    have hg : p ∣ Nat.gcd m 6 := Nat.dvd_gcd he hp6
    change Nat.gcd m 6 = 1 at hm
    exact hp1 (hm ▸ hg)
  have hs := PartitionZheng.sq_emod_24_nat
    (hnd 2 (by decide) (by decide)) (hnd 3 (by decide) (by decide))
  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.add_mod, Nat.mul_mod D (m^2), hD, hs]

private theorem Nodd_floor_eq (X : ℝ) (hX : 0 ≤ X) :
    PartitionZheng.Nodd ⌊X⌋₊ =
      {n : ℕ | (n : ℝ) ≤ X ∧ Odd (Nat.partitionNumber n)}.ncard := by
  unfold PartitionZheng.Nodd
  rw [← Set.ncard_coe_finset]
  congr 1
  ext n
  change n ∈ (Finset.range (⌊X⌋₊ + 1)).filter (fun k => PartitionZheng.pFun k % 2 = 1) ↔
    (n : ℝ) ≤ X ∧ Odd (Nat.partitionNumber n)
  constructor
  · intro hn
    obtain ⟨hRange, hOdd⟩ := Finset.mem_filter.mp hn
    have hFloor : n ≤ ⌊X⌋₊ := Nat.le_of_lt_succ (Finset.mem_range.mp hRange)
    exact ⟨(Nat.le_floor_iff hX).mp hFloor, Nat.odd_iff.mpr hOdd⟩
  · rintro ⟨hn, hOdd⟩
    have hFloor := (Nat.le_floor_iff hX).mpr hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hFloor),
      Nat.odd_iff.mp hOdd⟩

/-- Ono and Swaminathan's bound for the first admissible odd value. -/
def H1 : Prop :=
  ∀ (D : ℕ) (hD : 1 < D), Squarefree D → D % 24 = 23 →
    haveI : Fact (Irreducible (Polynomial.X ^ 2 + Polynomial.C (D : ℚ))) :=
      ⟨Polynomial.irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by omega))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (Polynomial.X ^ 2 + Polynomial.C (D : ℚ))) + 2 ∧
      Odd (Nat.partitionNumber ((D * m ^ 2 + 1) / 24))

/-- The class number is the cardinality of the set of reduced primitive
binary quadratic forms of fundamental discriminant `-D`. -/
def H2 : Prop :=
  ∀ (D : ℕ), Squarefree D → ∀ (hD : D % 4 = 3),
    haveI : Fact (Irreducible (Polynomial.X ^ 2 + Polynomial.C (D : ℚ))) :=
      ⟨Polynomial.irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by omega))⟩
    NumberField.classNumber (AdjoinRoot (Polynomial.X ^ 2 + Polynomial.C (D : ℚ))) =
      {p : ℤ × ℤ × ℤ | PartitionParity.IsReducedForm D p.1 p.2.1 p.2.2}.ncard

theorem main : H1 → H2 → OMA.R_PartitionParity_zheng_odd_R1.H1 := by
  intro hOdd hClass
  have hp : PartitionZheng.ParityInput := by
    intro D hD hSq h23
    obtain ⟨m, hm, hBound, hOdd⟩ := hOdd D hD hSq h23
    have h4 : D % 4 = 3 := by omega
    have hcl := hClass D hSq h4
    rw [hcl, ← reduced_form_count_eq] at hBound
    have hm1 : 1 ≤ m := by
      by_contra! h
      have hz : m = 0 := by omega
      simp [hz, Nat.Coprime] at hm
    have hnum := Nat.div_mul_cancel (numerator_dvd h23 hm)
    exact ⟨m, (D*m^2+1)/24, hm1, hm, hBound, by omega, hOdd⟩
  have hb := PartitionZheng.liminf_Nodd_ge_const hp
  have he :
      (fun X : ℝ => (((PartitionZheng.Nodd ⌊X⌋₊ : ℝ) / Real.sqrt X : ℝ) : EReal))
        =ᶠ[atTop]
      (fun X : ℝ => ((({n : ℕ | (n : ℝ) ≤ X ∧ Odd (Nat.partitionNumber n)}.ncard : ℝ)
        / Real.sqrt X : ℝ) : EReal)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
    rw [Nodd_floor_eq X hX]
  unfold OMA.R_PartitionParity_zheng_odd_R1.H1
  rw [← Filter.liminf_congr he]
  exact hb

end OMA.R_PartitionParity_zheng_odd_R1_H1_R1
