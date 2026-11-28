import OMAReductions.R_WeierstrassCurve_Affine_Rat_weakBSD_R1_H2_R1

/-!
# `Ш(E)[2]` is finite for every elliptic curve over `ℚ`

Step `H1` of the reduction `WeierstrassCurve.Affine.Rat.weakBSD.R1.H2.R1`: for every elliptic
curve `E` over `ℚ` the subgroup of the registered Tate-Shafarevich group
`WeierstrassCurve.Affine.tateShafarevich` killed by `2` is finite. The proof works over every
number field and is specialised to `ℚ` in the last line. It uses neither the Mordell-Weil theorem
nor any analytic input.

Credit: @carterleffen

## The argument

1. *From continuous cohomology to cocycles* (`DegreeOne`, `ShaBridge`). A class of the registered
   group is represented by a continuous crossed homomorphism `Gal(K̄/K) → E(K̄)` that becomes
   principal over every completion; two classes are equal when the crossed homomorphisms differ
   by a principal one. This gives an injection `shaMap` of the registered group into the explicit
   quotient `sha E` of locally trivial cocycles by coboundaries, compatible with multiplication by
   `n`. So it is enough that the classes of `sha E` killed by `2` form a finite set.
2. *Two-torsion representatives.* Over `K̄` every point is a double (`exists_two_nsmul_eq`, from
   the explicit halving formula `exists_half`), so a class killed by `2` has a representative
   cocycle `d` with values in `E[2]`.
3. *Kummer theory over `F = K(E[2])`* (`exists_descent_radical`). On `Gal(K̄/F)` such a `d` is a
   homomorphism. If `d σ ≠ 0` there is `s` with `s² ∈ F`, `σ s = -s`, fixed by the kernel of `d`.
4. *The radical is unramified outside a finite set* (`radical_even`). Local triviality of `d` at
   a prime `w` of `F`, together with the halving formula, shows that `s²` has even valuation at
   every `w` outside an explicit finite set `S` (`finite_not_goodPrime`).
5. *Finiteness of the Selmer group.* The square classes of `F` with even valuation outside `S`
   form the finite group `F(S, 2)` (`IsDedekindDomain.finite_selmerGroup_of_numberField`, from the
   finiteness of the class group and Dirichlet's unit theorem). Adjoining to `F` a square root of
   a representative of each class gives one finite extension `N` of `K` on whose absolute Galois
   group every `d` as in step 2 vanishes (`exists_common_splitting_field`).
6. *Counting* (`finite_shaMultiple_two`). The cocycle identity makes such a `d` constant on the
   cosets of `Gal(K̄/N)`, so `d` is a function from a finite coset space to the finite set `E[2]`
   (`finite_two_torsion`). There are finitely many of these, hence finitely many classes.

## Provenance

This file is assembled by a script from three sources. Nothing in it is taken from the proof of
any other step of the reduction.

**(a) EllipticCurves**, by Michael Stoll and the other contributors to that repository,
https://github.com/MichaelStollBayreuth/EllipticCurves, commit
c4c72f486112ab61eca3b1a69135ec06789897f8, licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). The four modules

  EllipticCurves/Mathlib/Basic.lean
  EllipticCurves/Mathlib/FractionalIdeal.lean
  EllipticCurves/Mathlib/SIntegers.lean
  EllipticCurves/Mathlib/SelmerGroup.lean

are the general-purpose part of that project (described there as support material intended for
Mathlib; the project itself grew out of the same author's Heights project). They supply step 5:
the ring of `S`-integers is a Dedekind domain with finite class group, the `S`-units are finitely
generated, and the Selmer group `K(S, n)` is finite. Mathlib defines `IsDedekindDomain.selmerGroup`
and records its finiteness as a TODO; no Mathlib lemma could be used in its place. The module
comment at the head of each of the four blocks is the original one and describes the whole
source module, of which only the declarations needed here are kept.

**(b) A local library on the Birch and Swinnerton-Dyer conjecture** by @carterleffen (not
published; namespace `BSDResearch`), modules

  statements/wp-birch-and-swinnerton-dyer-conjecture.lean   (the three cocycle definitions)
  BSD/ShaTorsion.lean, BSD/ShaDescent.lean, BSD/ShaKummer.lean
  BSD/LocalKummerRestriction.lean, BSD/UnramifiedKummer.lean
  BSD/TwoDescentLocal.lean, BSD/ShaTwoDescentFinite.lean      (steps 3 to 5)
  DegreeOne.lean, ShaBridge.lean                              (step 1)

The head comment of the `statements` module is kept as it stands; the declarations it says are
adapted from formal-conjectures (period, Tamagawa factors, height pairing) are not among the
three definitions kept here.

**(c) Written for this file**: the one-line instance under `glue`, and the last block
(`exists_two_nsmul_eq`, `finite_two_torsion`, `finite_shaMultiple_two`, the four-line transfer to
the registered group, and `OMA.solution`). In the local library the count of step 6 went through
the Mordell-Weil theorem over the splitting field, and step 2 through the cardinality of `E[n]`;
both are replaced here by the elementary statements about `E[2]`, which is why neither appears.

## Changes made to the sources

All changes are made by the assembling script; all are mechanical except the proof edits listed
last. No kept declaration changes its statement (one is re-spelled, see the composition sign).

* Each source module becomes one block between `begin` / `end` marker comments, in dependency
  order. `module`, `import` and `@[expose] public section` lines are dropped (the latter becomes a
  plain `section`); a module of the local library is wrapped in a `section`, so that `open`,
  `variable` and local instances stay inside their block.
* Only the declarations the final theorem depends on are kept (for the four EllipticCurves
  modules, 91 of 298). With them go the sections, section headings, `variable` and `open` lines
  that no longer contain or affect anything. Three declarations the proof terms do not mention are
  kept because elaboration needs them: `Units.modPow`, `FractionalIdeal.coe_unitOfPrime`,
  `IsDedekindDomain.sUnitValuation_apply`.
* Constructs the registry does not admit in a submission are removed or written out:
  linter `set_option` lines; `to_additive` attributes (the additive copies are not used);
  `@[reducible] def` is written `abbrev`; the local notation `A` of `ShaBridge` is expanded to
  `Affine.galoisRepresentation E`; the `attribute [local reducible]` line of `DegreeOne` is
  dropped (the kept proofs do not need it); section-level module docstrings become plain comments.
* The private abbreviations `C` and `V` occur with identical definitions in several modules of
  the local library; the repeated definitions are dropped.
* The composition sign of category theory in three statements of `DegreeOne` is written
  `CategoryStruct.comp`, because formal-conjectures declares a global notation with the same
  symbol for functions `ℕ → ℝ`.
* Proof edits. The local library was compiled with the file-level option
  `backward.isDefEq.respectTransparency false`, which is not admitted here. Without it, rewriting
  does not identify the group structure of `Gal(K̄/K)` with that of `Field.absoluteGaloisGroup K`.
  Six proof steps are adjusted for this, all inside proofs: in `exists_descent_radical` three
  local `have` statements carry a type ascription `(_ : G K)`, one `rw` is replaced by the
  equivalent `refine (_).trans ?_`, and one `rw [hd, hd, add_zero]` by the term it stood for; in
  `local_kummer_point` one `simp only` step is replaced by the three equations it produced.

The portions of this file taken from EllipticCurves are licensed under the Apache License,
Version 2.0 (the "License"); you may not use them except in compliance with the License. You may
obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0. Unless required by
applicable law or agreed to in writing, software distributed under the License is distributed on
an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
License for the specific language governing permissions and limitations under the License.
-/

/- ===== begin EllipticCurves/Mathlib/Basic.lean (EllipticCurves @ c4c72f486112) ===== -/
section

/-
# Material for Mathlib

This file collects the general-purpose results developed for `EllipticCurves.WeakMordellWeil`
that have nothing to do with elliptic curves and look like candidates for Mathlib.

* `MonoidHom.ofMapMulMulEqOne`: build a `MonoidHom` from `f 1 = 1` and
  `a * b * c = 1 → f a * f b * f c = 1`.
* `Valuation.map_eval_eq_of_one_lt` and `Valuation.le_one_of_root_monic`: dominance of the
  leading term of a monic polynomial with integral coefficients, and integrality of its roots.
  `Valuation.eq_one_of_mul_eq_one`: a factor of a unit is a unit, provided both factors are
  integral.
* `IsDedekindDomain.HeightOneSpectrum.finite_setOf_valuation_ne_one`,
  `.below` (the prime lying below a prime of an integral extension), `.primesAbove` and its
  finiteness `.primesAbove_finite`,
  `IsDedekindDomain.selmerGroupAbove`, `.valuationOfNeZero_eq_iff`,
  `.dvd_toAdd_valuationOfNeZero`, `.valuationOfNeZeroMod_mk` and
  `.valuationOfNeZeroMod_mk_eq_one_iff`, which turns the Selmer condition into a
  divisibility of valuations; `Set.integer_mono` and `Set.unit_mono`, monotonicity of the
  `S`-integers and `S`-units in `S`. (`Mathlib.RingTheory.DedekindDomain.SelmerGroup` has a
  `TODO` about the `Multiplicative`/`Additive` defeq abuse in `valuationOfNeZeroMod`
  and provides no API for it.)
* `Units.modPow`, the group of `n`-th power classes of units, which
  `Mathlib.RingTheory.DedekindDomain.SelmerGroup` has only as a local notation, together
  with `map`, `congr` and `piEquiv`.
* Division with remainder by a monic polynomial: `Polynomial.Monic.divByMonic_mul_add`,
  `.modByMonic_mul_add`, `modByMonic_mem_degreeLT`, `divByMonic_mem_degreeLT`.
* `isIntegralClosure_int_integralClosure`, `NumberField.finite_classGroup_integralClosure` and
  `NumberField.fg_units_integralClosure`: the class number theorem and the finite generation of
  the unit group for the integral closure of `𝓞 K` in a finite extension of a number field `K`;
  `NumberField.subsingleton_classGroup_integralClosure` and
  `NumberField.finrank_additive_units_integralClosure` transport triviality of the class
  group and the unit rank from `𝓞 L`.
* `AdjoinRoot.discr_powerBasis_eq_discr`, `NumberField.exists_eq_discr_mul_sq`,
  `RingOfIntegers.isPrincipalIdealRing_of_finrank_eq_three_of_abs_discr_le` and
  `RingOfIntegers.finrank_additive_units_of_discr_neg`/`_pos`: the discriminant of the power
  basis of `K[X]/(f)` is `f.discr`; the field discriminant is any integral power-basis
  discriminant divided by a square; a cubic field with `|discr| ≤ 49` has trivial class group
  (Minkowski bound), and the sign of its discriminant determines the unit rank (Dirichlet).
* `AdjoinRoot.norm_mk_eq_resultant`: for monic `g`, the norm of `AdjoinRoot.mk g p` is the
  resultant of `g` and `p`. This links `Polynomial.resultant` to `Algebra.norm`.
* `AdjoinRoot.equivPiFactors`: for nonzero squarefree `f`, `K[X]/(f)` is the product of the
  fields `K[X]/(p)` over the monic irreducible factors `p` of `f`, and the induced
  `AdjoinRoot.modPowEquivPiFactors` on `n`-th power classes of units.
* `Polynomial.discr_X_sub_C_mul`: splitting off a linear factor multiplies the discriminant
  by the square of the evaluation, `((X - C x) * g).discr = g.discr * g.eval x ^ 2`.
* `Matrix.det_blockDiagonal'`, `LinearMap.det_pi'`, `Algebra.norm_prod`, `Algebra.norm_pi`:
  determinants and norms on (dependent) products decompose as products; together with
  `AdjoinRoot.norm_eq_prod_norm_projFactor`, the norm on `K[X]/(f)` as the product of the
  norms on the field factors.
* General helpers extracted from the rank example: `Squarefree.map` (transport along a
  `MulEquiv`), `Polynomial.Monic.irreducible_map_fraction_map_of_irreducible_map`
  (irreducibility over the fraction field via reduction modulo a prime),
  `Polynomial.Factors.coe_eq`, `AdjoinRoot.isIntegralElem_root_of_map`,
  `AdjoinRoot.finrank_eq_natDegree`, and the `IsPrincipalIdealRing (𝓞 ℚ)` instance.
-/

section modPow

/-- The group of `n`-th power classes of units of `α`. This is the group underlying the
Selmer groups of `Mathlib.RingTheory.DedekindDomain.SelmerGroup`, where it only exists
as a local notation. -/
abbrev Units.modPow (α : Type*) [CommMonoid α] (n : ℕ) : Type _ :=
  αˣ ⧸ (powMonoidHom n : αˣ →* αˣ).range

end modPow

section DedekindDomain

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A nonzero element of the fraction field of a Dedekind domain has trivial valuation at all
but finitely many primes. -/
lemma IsDedekindDomain.HeightOneSpectrum.finite_setOf_valuation_ne_one {x : K} (hx : x ≠ 0) :
    {v : HeightOneSpectrum R | v.valuation K x ≠ 1}.Finite := by
  refine ((Support.finite R x).union (Support.finite R x⁻¹)).subset fun v hv ↦ ?_
  rcases lt_or_gt_of_ne hv with h | h
  · refine .inr ?_
    rw [Support, Set.mem_ofPred_eq, map_inv₀,
      one_lt_inv₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx))]
    exact h
  · exact .inl h

lemma Set.unit_mono {S T : Set (HeightOneSpectrum R)} (hST : S ⊆ T) : S.unit K ≤ T.unit K :=
  fun _ hx v hv ↦ hx v fun hvS ↦ hv (hST hvS)

/-- Ideal-level divisibility characterization of `Associates.count`: the multiplicity of `v` in
`J` is at least `k` iff `v ^ k` divides `J`. -/
lemma IsDedekindDomain.HeightOneSpectrum.le_count_iff_le {A : Type*} [CommRing A]
    [IsDedekindDomain A] (v : HeightOneSpectrum A) {J : Ideal A} (hJ : J ≠ ⊥) (k : ℕ) :
    k ≤ (Associates.mk v.asIdeal).count (Associates.mk J).factors ↔ J ≤ v.asIdeal ^ k := by
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ) v.associates_irreducible,
    ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]

/-- Divisibility characterization of `Associates.count` for a height one prime: the `v`-adic
valuation of `x` is at least `k` iff `x ∈ v ^ k`. -/
lemma IsDedekindDomain.HeightOneSpectrum.le_count_iff {A : Type*} [CommRing A]
    [IsDedekindDomain A] (v : HeightOneSpectrum A) {x : A} (hx : x ≠ 0) (k : ℕ) :
    k ≤ Associates.count (Associates.mk v.asIdeal) (Associates.mk (Ideal.span {x})).factors ↔
      x ∈ v.asIdeal ^ k := by
  rw [v.le_count_iff_le (fun h ↦ hx (Ideal.span_singleton_eq_bot.mp h)) k,
    Ideal.span_singleton_le_iff_mem]

/-- The `Multiplicative ℤ`-valued valuation of a unit is determined by the `ℤᵐ⁰`-valued one. -/
lemma IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq_iff (v : HeightOneSpectrum R)
    (u : Kˣ) (m : Multiplicative ℤ) :
    v.valuationOfNeZero u = m ↔ v.valuation K (u : K) = (m : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.coe_inj, valuationOfNeZero_eq]

/-- The image of the class of a unit `u` under the `v`-adic valuation mod `n` is the class in
`ZMod n` of the `v`-adic order of `u`. This is the computation rule that
`Mathlib.RingTheory.DedekindDomain.SelmerGroup` lacks; it holds by definition, but the
`Multiplicative`/`Additive` defeq abuse in `valuationOfNeZeroMod` blocks unfolding it by hand. -/
lemma IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroMod_mk (v : HeightOneSpectrum R)
    (n : ℕ) (u : Kˣ) :
    v.valuationOfNeZeroMod n (QuotientGroup.mk u) =
      Multiplicative.ofAdd ((Multiplicative.toAdd (v.valuationOfNeZero u) : ℤ) : ZMod n) :=
  rfl

/-- The class of a unit `u` in `Units.modPow K n` has trivial image under the `v`-adic valuation
mod `n` exactly when the `v`-adic valuation of `u` is divisible by `n`. -/
lemma IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff
    (v : HeightOneSpectrum R) (n : ℕ) (u : Kˣ) :
    v.valuationOfNeZeroMod n (QuotientGroup.mk u) = 1 ↔
      (n : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero u) := by
  rw [valuationOfNeZeroMod_mk, ofAdd_eq_one, ZMod.intCast_zmod_eq_zero_iff_dvd]

end DedekindDomain

end
/- ===== end EllipticCurves/Mathlib/Basic.lean ===== -/

/- ===== begin EllipticCurves/Mathlib/FractionalIdeal.lean (EllipticCurves @ c4c72f486112) ===== -/
section

/-
# The group of fractional ideals is free abelian on the primes

Let `R` be a Dedekind domain with fraction field `K`. The nonzero fractional ideals of `R` form a
group `(FractionalIdeal R⁰ K)ˣ` (every nonzero fractional ideal is invertible), and unique
factorization says this group is free abelian on the height one primes. Mathlib has all the
valuation bookkeeping (`IsDedekindDomain.HeightOneSpectrum.count` and the factorization lemmas in
`Mathlib.RingTheory.DedekindDomain.Factorization`) but does not package the isomorphism itself;
this file does.

## Main definitions and results

* `FractionalIdeal.factorization`: the isomorphism
  `(FractionalIdeal R⁰ K)ˣ ≃* Multiplicative (HeightOneSpectrum R →₀ ℤ)`, sending a fractional
  ideal to its tuple of valuations.
* `FractionalIdeal.exists_pow_eq`: **`n`-th roots** — a fractional ideal all of whose valuations
  are divisible by `n` is an `n`-th power. This is the key input to the fundamental exact sequence
  of the Selmer group.
* `FractionalIdeal.prod_count`, `count_injective`: a nonzero fractional ideal is the product of
  `v ^ (count v)` over the primes, and is determined by its valuations.

This is general material, candidate for upstreaming to Mathlib.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors Classical

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

namespace FractionalIdeal

/-
### The kernel of the principal-ideal map

The principal fractional ideal `(x)` is trivial exactly when `x` comes from a unit of `R`. This
identifies `ker toPrincipalIdeal` with the units of `R`, the left end of the ideal class exact
sequence. This part needs `R` to be a domain only.
-/

section PrincipalIdeal

variable [IsDomain R]

lemma spanSingleton_eq_one_iff {x : K} (hx : x ≠ 0) :
    spanSingleton R⁰ x = 1 ↔ ∃ a : Rˣ, algebraMap R K a = x := by
  constructor
  · intro h
    have hinv : spanSingleton R⁰ x⁻¹ = 1 := by rw [← spanSingleton_inv, h, inv_one]
    obtain ⟨a, ha⟩ := (mem_one_iff R⁰).mp (h ▸ mem_spanSingleton_self R⁰ x)
    obtain ⟨b, hb⟩ := (mem_one_iff R⁰).mp (hinv ▸ mem_spanSingleton_self R⁰ x⁻¹)
    have hab : a * b = 1 := IsFractionRing.injective R K (by
      rw [map_mul, ha, hb, mul_inv_cancel₀ hx, map_one])
    exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩
  · rintro ⟨a, rfl⟩
    rw [← coeIdeal_span_singleton, Ideal.span_singleton_eq_top.mpr a.isUnit, coeIdeal_top]

/-- `toPrincipalIdeal x = 1` exactly when `x` is a unit of `R`: the kernel of the principal-ideal
map is the image of `Rˣ`. -/
lemma toPrincipalIdeal_eq_one_iff (u : Kˣ) :
    toPrincipalIdeal R K u = 1 ↔ ∃ a : Rˣ, Units.map (algebraMap R K : R →* K) a = u := by
  rw [← Units.val_inj, coe_toPrincipalIdeal, Units.val_one, spanSingleton_eq_one_iff u.ne_zero]
  exact ⟨fun ⟨a, ha⟩ ↦ ⟨a, Units.ext ha⟩, fun ⟨a, ha⟩ ↦ ⟨a, by rw [← ha]; rfl⟩⟩

/-- `ClassGroup.mk I = 1` exactly when the unit fractional ideal `I` is principal, with the
generator provided as a unit of `K`. Variant of `ClassGroup.mk_eq_one_iff` avoiding
`Submodule.IsPrincipal`. -/
lemma _root_.ClassGroup.mk_eq_one_iff_exists {I : (FractionalIdeal R⁰ K)ˣ} :
    ClassGroup.mk K I = 1 ↔ ∃ x : Kˣ, toPrincipalIdeal R K x = I := by
  rw [ClassGroup.mk_eq_one_iff]
  constructor
  · intro hI
    obtain ⟨x, hx⟩ := hI.principal
    have hx' : (I : FractionalIdeal R⁰ K) = spanSingleton R⁰ x := by
      apply Subtype.coe_injective
      simp only [val_eq_coe, hx, coe_spanSingleton]
    have hx0 : x ≠ 0 := fun h ↦ Units.ne_zero I (by rw [hx', h, spanSingleton_zero])
    exact ⟨Units.mk0 x hx0, by rw [← Units.val_inj, coe_toPrincipalIdeal, hx']; rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨(x : K), by rw [coe_toPrincipalIdeal, coe_spanSingleton]⟩⟩

end PrincipalIdeal

variable [IsDedekindDomain R]

/-- A nonzero fractional ideal is the product `∏ v ^ (count v)` over the height one primes. -/
theorem prod_count {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ count K v I = I := by
  obtain ⟨a, J, ha, haJ⟩ := exists_eq_spanSingleton_mul I
  simp_rw [fun v ↦ count_well_defined K v hI haJ]
  exact finprod_heightOneSpectrum_factorization hI haJ

/-- The prime `v` as a unit of the group of fractional ideals. -/
noncomputable def unitOfPrime (v : HeightOneSpectrum R) : (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal R⁰ K) (coeIdeal_ne_zero.mpr v.ne_bot)

@[simp] lemma coe_unitOfPrime (v : HeightOneSpectrum R) :
    ((unitOfPrime v : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) = v.asIdeal := rfl

/-- The finitely-supported tuple of valuations of a unit fractional ideal. -/
noncomputable def toFinsupp (I : (FractionalIdeal R⁰ K)ˣ) : HeightOneSpectrum R →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v ↦ count K v (I : FractionalIdeal R⁰ K)) (by
    have := finite_factors (I : FractionalIdeal R⁰ K)
    simpa [Function.support, Filter.eventually_cofinite] using this)

@[simp] lemma toFinsupp_apply (I : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    toFinsupp I v = count K v (I : FractionalIdeal R⁰ K) := rfl

/-- The unit fractional ideal `∏ v ^ (g v)`. -/
noncomputable def ofFinsupp (g : HeightOneSpectrum R →₀ ℤ) : (FractionalIdeal R⁰ K)ˣ :=
  g.prod (fun v e ↦ unitOfPrime v ^ e)

lemma coe_ofFinsupp (g : HeightOneSpectrum R →₀ ℤ) :
    ((ofFinsupp g : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K)
      = g.prod (fun v e ↦ (v.asIdeal : FractionalIdeal R⁰ K) ^ e) := by
  rw [ofFinsupp, ← Units.coeHom_apply, map_finsuppProd]
  simp [Units.coeHom]

lemma count_ofFinsupp (g : HeightOneSpectrum R →₀ ℤ) (v : HeightOneSpectrum R) :
    count K v ((ofFinsupp g : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) = g v := by
  rw [coe_ofFinsupp, count_finsuppProd]

/-- A unit fractional ideal is determined by its valuations. -/
lemma count_injective {I J : (FractionalIdeal R⁰ K)ˣ}
    (h : ∀ v, count K v (I : FractionalIdeal R⁰ K) = count K v (J : FractionalIdeal R⁰ K)) :
    I = J := by
  apply Units.ext
  rw [← prod_count (Units.ne_zero I), ← prod_count (Units.ne_zero J)]
  exact finprod_congr fun v ↦ by rw [h v]

/-- The `v`-adic valuation of `x : K` is `exp (- count v (x))`: the `count` of the principal
fractional ideal generated by `x` recovers the adic valuation. -/
theorem valuation_eq_exp_neg_count (v : HeightOneSpectrum R) {x : K} (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (- count K v (spanSingleton R⁰ x)) := by
  have key (r : R) (hr : r ≠ 0) : v.valuation K (algebraMap R K r) =
      WithZero.exp (- count K v (spanSingleton R⁰ (algebraMap R K r))) := by
    rw [valuation_of_algebraMap, intValuation_apply, v.intValuationDef_if_neg hr,
      ← coeIdeal_span_singleton, count_coe K v (by simpa using hr)]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have hsa : spanSingleton R⁰ (algebraMap R K a) ≠ 0 := by
    rwa [spanSingleton_ne_zero_iff, ne_eq, _root_.map_eq_zero_iff _ (IsFractionRing.injective R K)]
  have hsb : spanSingleton R⁰ (algebraMap R K (b:R)) ≠ 0 := by
    rwa [spanSingleton_ne_zero_iff, ne_eq, _root_.map_eq_zero_iff _ (IsFractionRing.injective R K)]
  have hcount : count K v (spanSingleton R⁰ (algebraMap R K a / algebraMap R K (b:R))) =
      count K v (spanSingleton R⁰ (algebraMap R K a)) -
        count K v (spanSingleton R⁰ (algebraMap R K (b:R))) := by
    rw [← spanSingleton_div_spanSingleton, div_eq_mul_inv, count_mul K v hsa (inv_ne_zero hsb),
      count_inv, sub_eq_add_neg]
  rw [map_div₀, key a ha0, key (b:R) hb0, hcount, div_eq_mul_inv, ← WithZero.exp_neg,
    ← WithZero.exp_add]
  congr 1
  ring

/-- The `v`-adic order of a unit `x : Kˣ` is `- count v (x)`: the additive form of
`valuation_eq_exp_neg_count`. -/
theorem toAdd_valuationOfNeZero (v : HeightOneSpectrum R) (x : Kˣ) :
    Multiplicative.toAdd (v.valuationOfNeZero x) =
      - count K v (spanSingleton R⁰ (x : K)) := by
  have h : (v.valuationOfNeZero x : WithZero (Multiplicative ℤ)) =
      WithZero.exp (- count K v (spanSingleton R⁰ (x : K))) := by
    rw [HeightOneSpectrum.valuationOfNeZero_eq, valuation_eq_exp_neg_count v x.ne_zero]
  rw [WithZero.exp_eq_coe_ofAdd, WithZero.coe_inj] at h
  rw [h, toAdd_ofAdd]

/-
### The `n`-th root as a homomorphism

On the subgroup of fractional ideals all of whose valuations are divisible by `n`, the `n`-th
root is a genuine group homomorphism (not merely an existence statement): dividing every
valuation by `n` is additive there.
-/

section NthRoot

variable (R K)

/-- The subgroup of fractional ideals whose valuations are all divisible by `n`. -/
def nDivisible (n : ℕ) : Subgroup (FractionalIdeal R⁰ K)ˣ where
  carrier := {I | ∀ v, (n : ℤ) ∣ count K v (I : FractionalIdeal R⁰ K)}
  one_mem' v := by rw [Units.val_one, count_one]; exact dvd_zero _
  mul_mem' {I J} hI hJ v := by
    rw [Units.val_mul, count_mul K v (Units.ne_zero I) (Units.ne_zero J)]
    exact dvd_add (hI v) (hJ v)
  inv_mem' {I} hI v := by
    rw [Units.val_inv_eq_inv_val, count_inv]; exact (hI v).neg_right

/-- The `n`-th root ideal of `I`: its valuations divided by `n`. -/
noncomputable def nthRootFun (n : ℕ) (I : (FractionalIdeal R⁰ K)ˣ) : (FractionalIdeal R⁰ K)ˣ :=
  ofFinsupp (Finsupp.mapRange (· / (n:ℤ)) (by simp) (toFinsupp I))

lemma count_nthRootFun (n : ℕ) (I : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    count K v (nthRootFun R K n I : FractionalIdeal R⁰ K) =
      count K v (I : FractionalIdeal R⁰ K) / n := by
  rw [nthRootFun, count_ofFinsupp, Finsupp.mapRange_apply, toFinsupp_apply]

/-- The `n`-th root as a group homomorphism on the `n`-divisible subgroup. -/
noncomputable def nthRootHom (n : ℕ) : nDivisible R K n →* (FractionalIdeal R⁰ K)ˣ where
  toFun I := nthRootFun R K n (I : (FractionalIdeal R⁰ K)ˣ)
  map_one' := count_injective fun v ↦ by
    simp only [count_nthRootFun, Subgroup.coe_one, Units.val_one, count_one, Int.zero_ediv]
  map_mul' I J := count_injective fun v ↦ by
    rw [count_nthRootFun, Units.val_mul, count_mul K v (Units.ne_zero _) (Units.ne_zero _),
      count_nthRootFun, count_nthRootFun, Subgroup.coe_mul, Units.val_mul,
      count_mul K v (Units.ne_zero _) (Units.ne_zero _), Int.add_ediv_of_dvd_left (I.2 v)]

variable {R K} in
@[simp] lemma nthRootHom_apply (n : ℕ) (I : nDivisible R K n) :
    nthRootHom R K n I = nthRootFun R K n (I : (FractionalIdeal R⁰ K)ˣ) := rfl

/-- The `n`-th root homomorphism is a genuine `n`-th root. -/
lemma nthRootHom_pow (n : ℕ) (I : nDivisible R K n) :
    (nthRootHom R K n I) ^ n = (I : (FractionalIdeal R⁰ K)ˣ) := by
  apply count_injective
  intro v
  rw [Units.val_pow_eq_pow_val, count_pow, nthRootHom_apply,
    count_nthRootFun, Int.mul_ediv_cancel' (I.2 v)]

end NthRoot

/-
### The `n`-th-root class map and its kernel

For a unit `u : Kˣ` whose principal ideal has all valuations divisible by `n`, the `n`-th root
`𝔞` of `(u)` has a well-defined class in `ClassGroup R`. The class vanishes exactly when `u` is
a unit of `R` times an `n`-th power in `Kˣ` — the exactness of the fundamental sequence
`1 → Rˣ/(Rˣ)ⁿ → K(∅,n) → Cl(R)[n]` at the middle spot, stated here before any quotients are
taken.
-/

section NthRootClass

variable (R K)

/-- The units of `K` whose principal fractional ideal has all valuations divisible by `n`. -/
def unitsNDivisible (n : ℕ) : Subgroup Kˣ :=
  Subgroup.comap (toPrincipalIdeal R K) (nDivisible R K n)

/-- The restriction of `toPrincipalIdeal` to `unitsNDivisible`, into the `n`-divisible
subgroup. -/
noncomputable def unitsNDivisibleToNDivisible (n : ℕ) :
    unitsNDivisible R K n →* nDivisible R K n :=
  ((toPrincipalIdeal R K).comp (unitsNDivisible R K n).subtype).codRestrict _ (fun x ↦ x.2)

@[simp] lemma coe_unitsNDivisibleToNDivisible (n : ℕ) (u : unitsNDivisible R K n) :
    (unitsNDivisibleToNDivisible R K n u : (FractionalIdeal R⁰ K)ˣ) =
      toPrincipalIdeal R K (u : Kˣ) := rfl

/-- The `n`-th-root class map: the class of the `n`-th root of the principal ideal `(u)`. -/
noncomputable def nthRootClass (n : ℕ) : unitsNDivisible R K n →* ClassGroup R :=
  (ClassGroup.mk K).comp ((nthRootHom R K n).comp (unitsNDivisibleToNDivisible R K n))

@[simp]
lemma nthRootClass_apply (n : ℕ) (u : unitsNDivisible R K n) :
    nthRootClass R K n u =
      ClassGroup.mk K (nthRootHom R K n (unitsNDivisibleToNDivisible R K n u)) :=
  rfl

/-- **Exactness of the fundamental sequence at the middle spot**: the `n`-th-root class of `u`
vanishes exactly when `u` is a unit of `R` times an `n`-th power. -/
lemma nthRootClass_eq_one_iff {n : ℕ} (hn : n ≠ 0) (u : unitsNDivisible R K n) :
    nthRootClass R K n u = 1 ↔
      ∃ (a : Rˣ) (w : Kˣ), Units.map (algebraMap R K : R →* K) a * w ^ n = (u : Kˣ) := by
  rw [nthRootClass_apply, ClassGroup.mk_eq_one_iff_exists]
  constructor
  · intro ⟨w, hw⟩
    -- the `n`-th power of the found generator `w` generates `(u)`, so `u / wⁿ` is a unit of `R`
    have hpow : toPrincipalIdeal R K (w ^ n) = toPrincipalIdeal R K (u : Kˣ) := by
      rw [map_pow, hw, nthRootHom_pow, coe_unitsNDivisibleToNDivisible]
    have h1 : toPrincipalIdeal R K ((u : Kˣ) * (w ^ n)⁻¹) = 1 := by
      rw [map_mul, map_inv, hpow, mul_inv_cancel]
    obtain ⟨a, ha⟩ := (toPrincipalIdeal_eq_one_iff _).mp h1
    exact ⟨a, w, by rw [ha]; group⟩
  · intro ⟨a, w, hw⟩
    -- `w` generates the `n`-th root: its valuations are `count (u) / n`
    refine ⟨w, count_injective fun v ↦ ?_⟩
    have hcu : count K v ((toPrincipalIdeal R K (u : Kˣ) : (FractionalIdeal R⁰ K)ˣ) :
        FractionalIdeal R⁰ K) = n * count K v
          ((toPrincipalIdeal R K w : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) := by
      rw [← hw, map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val,
        count_mul K v (Units.ne_zero _) (pow_ne_zero _ (Units.ne_zero _)), count_pow,
        (toPrincipalIdeal_eq_one_iff _).mpr ⟨a, rfl⟩, Units.val_one, count_one, zero_add]
    rw [nthRootHom_apply, count_nthRootFun, coe_unitsNDivisibleToNDivisible, hcu,
      Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr hn)]

end NthRootClass

end FractionalIdeal

end
/- ===== end EllipticCurves/Mathlib/FractionalIdeal.lean ===== -/

/- ===== begin EllipticCurves/Mathlib/SIntegers.lean (EllipticCurves @ c4c72f486112) ===== -/
section

/-
# The ring of `S`-integers is a Dedekind domain

Let `R` be a Dedekind domain with fraction field `K` and let `S` be a set of primes of `R`.
`Mathlib.RingTheory.DedekindDomain.SInteger` defines the subalgebra `Set.integer S K` of
`S`-integers, `𝒪_S = {x : K | ∀ v ∉ S, v x ≤ 1} = ⋂_{v ∉ S} R_v`, but proves nothing about its
ring structure. This file develops it. The goal is:

* `𝒪_S` is a Dedekind domain with fraction field `K`;
* its height one primes are exactly the `v ∉ S`, via `v ↦ 𝒪_S ∩ v`;
* its class group is `Cl(R)` modulo the subgroup generated by the classes of the `v ∈ S`.

These are the facts needed in `EllipticCurves.Mathlib.SelmerGroup` to construct the right-hand
map of the fundamental exact sequence, and they reduce the whole exact sequence to the case
`S = ∅`, where the map to the class group is simply `x ↦ [𝔞]` for the ideal with `𝔞 ^ n = (x)`.
They are of independent interest, and Mathlib has none of them.

## A warning

`𝒪_S` is **not** in general a localization of `R`. Localizing at
`M = {r : R | r ≠ 0 ∧ ∀ v ∉ S, v r = 1}` gives a subring of `𝒪_S`, but it can be strictly
smaller: if `Cl(R) ≅ ℤ` is generated by the class of a single prime `v` and `S = {v}`, then
`M = Rˣ`, because no power `v ^ k` with `k ≠ 0` is principal; yet `𝒪_S ⊋ R`, since for any
integral ideal `𝔞` in the class of `v` the fractional ideal `𝔞 * v⁻¹` is principal, generated by
some `x` with `v x < 1` and `w x ≤ 1` for `w ≠ v`. So `𝒪_S` has to be handled as a general
overring of `R`, not as a ring of fractions.

The classical statement in the appropriate generality is that *every* overring of a Dedekind
domain (i.e. every ring between `R` and `K`) is a Dedekind domain. The proofs below use the
`S`-integer description directly (via the denominator-ideal argument in `map_comap_eq`), which
keeps them short; upstreaming to Mathlib might instead aim for the general overring statement.

## Implementation notes

`Set.integer S K` is a `Subalgebra R K`. Since it sits between `R` and `K`, the instance
`Localization.subalgebra.instIsFractionRingSubtypeMemSubalgebra` already makes `K` its fraction
field, so `HeightOneSpectrum`-style valuation theory applies as soon as we know it is a Dedekind
domain.

## Main statements

* `IsDedekindDomain.SInteger.isIntegrallyClosed`: `𝒪_S` is integrally closed.
* `IsDedekindDomain.SInteger.isDedekindDomain`: `𝒪_S` is a Dedekind domain.
* `IsDedekindDomain.SInteger.heightOneSpectrumEquiv`: the primes of `𝒪_S` are the `v ∉ S`, and
  `valuation_heightOneSpectrumEquiv`: the valuations restrict those of `R`.
* `IsDedekindDomain.SInteger.extendedHom_surjective` and `finite_classGroup`: extension of ideals
  `Cl(R) → Cl(𝒪_S)` is surjective, so `Cl(𝒪_S)` is finite whenever `Cl(R)` is.
* `IsDedekindDomain.SInteger.classGroupEquiv`: `Cl(𝒪_S) ≃* Cl(R) ⧸ ⟨[v] : v ∈ S⟩`.

-/

open IsDedekindDomain FractionalIdeal

open scoped nonZeroDivisors Classical

section DenomIdeal

variable {R : Type*} [CommRing R] (K : Type*) [CommRing K] [Algebra R K]

/-- The denominator ideal of `x : K`: the colon ideal `(R : x) = {r : R | r • x ∈ R}`. -/
abbrev IsDedekindDomain.SInteger.denomIdeal (x : K) : Ideal R := (1 : Submodule R K).colon {x}

lemma IsDedekindDomain.SInteger.mem_denomIdeal_iff {x : K} {r : R} :
    r ∈ denomIdeal K x ↔ ∃ s : R, algebraMap R K r * x = algebraMap R K s := by
  rw [Submodule.mem_colon_singleton, Algebra.smul_def, Submodule.mem_one]
  exact exists_congr fun s ↦ eq_comm

end DenomIdeal

namespace IsDedekindDomain.SInteger

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (S : Set (HeightOneSpectrum R))

lemma toSubring_le_valuationSubring {v : HeightOneSpectrum R} (hv : v ∉ S) :
    (S.integer K).toSubring ≤ (v.valuation K).valuationSubring.toSubring :=
  fun _ hx ↦ hx v hv

/-- The fraction field of the ring of `S`-integers is `K`. This is already an instance, as
`Set.integer S K` is a subalgebra of `K` over `R`. -/
example : IsFractionRing (S.integer K) K := inferInstance

/-- The ring of `S`-integers is integrally closed: it is an intersection of valuation subrings
of `K`, each of which is integrally closed in `K`. -/
instance isIntegrallyClosed : IsIntegrallyClosed (S.integer K) := by
  rw [isIntegrallyClosed_iff K]
  intro x hx
  refine ⟨⟨x, fun v hv ↦ ?_⟩, rfl⟩
  -- work inside the valuation subring `V` of `v`, which contains `𝒪_S`
  set V := (v.valuation K).valuationSubring with hV
  let _ : Algebra (S.integer K) V :=
    (Subring.inclusion (toSubring_le_valuationSubring K S hv)).toAlgebra
  have _ : IsScalarTower (S.integer K) V K := .of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff K).mp inferInstance (hx.tower_top (A := V))
  rw [← hy]
  exact y.property

/-
### Primes in `S` become the unit ideal

For `v ∈ S` the inverse `v⁻¹` of `v` as a fractional ideal consists of `S`-integers, because an
element `y` with `y * v ⊆ R` can have a pole only at `v`. As `v * v⁻¹ = 1`, the extension of `v`
to `𝒪_S` is therefore the unit ideal. This is the one place where the Dedekind property of `R`
enters, and it is what makes `𝒪_S` bigger than `R`.
-/

/-- A height one prime is not contained in any other one. -/
lemma exists_mem_notMem {v w : HeightOneSpectrum R} (h : w ≠ v) :
    ∃ a ∈ v.asIdeal, a ∉ w.asIdeal := by
  by_contra! hc
  exact h (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hc).symm)

/-- For `v ∈ S`, the fractional ideal `v⁻¹` consists of `S`-integers. -/
lemma mem_integer_of_mem_inv {v : HeightOneSpectrum R} (hv : v ∈ S) {y : K}
    (hy : y ∈ (v.asIdeal : FractionalIdeal R⁰ K)⁻¹) : y ∈ S.integer K := by
  intro w hw
  obtain ⟨a, ha, haw⟩ := exists_mem_notMem (show w ≠ v by rintro rfl; exact hw hv)
  have h1 : y * algebraMap R K a ∈ (1 : FractionalIdeal R⁰ K) :=
    (FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)).mp hy _
      (FractionalIdeal.mem_coeIdeal_of_mem R⁰ ha)
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp h1
  have h2 : w.valuation K (y * algebraMap R K a) ≤ 1 := hr ▸ w.valuation_le_one r
  rwa [map_mul, w.valuation_eq_one_iff_notMem.mpr haw, mul_one] at h2

/-- For `v ∈ S`, the extension of `v` to the ring of `S`-integers is the unit ideal. -/
lemma map_asIdeal_eq_top {v : HeightOneSpectrum R} (hv : v ∈ S) :
    Ideal.map (algebraMap R (S.integer K)) v.asIdeal = ⊤ := by
  set A := S.integer K with hA
  set M := Ideal.map (algebraMap R A) v.asIdeal with hM
  -- `1 ∈ v * v⁻¹`, as a submodule of `K`
  have h1 : (1 : K) ∈
      (v.asIdeal : FractionalIdeal R⁰ K) * (v.asIdeal : FractionalIdeal R⁰ K)⁻¹ := by
    rw [FractionalIdeal.coe_ideal_mul_inv _ v.ne_bot]
    exact (FractionalIdeal.mem_one_iff _).mpr ⟨1, map_one _⟩
  rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at h1
  -- every element of the product that is an `S`-integer lies in `M`
  refine Ideal.eq_top_iff_one M |>.mpr ?_
  suffices H : ∀ x ∈ (v.asIdeal : FractionalIdeal R⁰ K) * (v.asIdeal : FractionalIdeal R⁰ K)⁻¹,
      ∃ hx : x ∈ A, (⟨x, hx⟩ : A) ∈ M by
    obtain ⟨hx, hx'⟩ := H 1 (by rwa [← FractionalIdeal.coe_mul, FractionalIdeal.mem_coe] at h1)
    exact (show (⟨1, hx⟩ : A) = 1 from rfl) ▸ hx'
  intro x hx
  rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at hx
  refine Submodule.mul_induction_on hx (fun a ha y hy ↦ ?_) (fun x y hx hy ↦ ?_)
  · obtain ⟨a, ha', rfl⟩ := (FractionalIdeal.mem_coeIdeal R⁰).mp
      ((FractionalIdeal.mem_coe (I := (v.asIdeal : FractionalIdeal R⁰ K))).mpr ha)
    have hyA : y ∈ A := mem_integer_of_mem_inv K S hv
      ((FractionalIdeal.mem_coe (I := (v.asIdeal : FractionalIdeal R⁰ K)⁻¹)).mpr hy)
    have haA : algebraMap R K a ∈ A := A.algebraMap_mem a
    refine ⟨mul_mem haA hyA, ?_⟩
    have he : (⟨algebraMap R K a * y, mul_mem haA hyA⟩ : A) = algebraMap R A a * ⟨y, hyA⟩ := rfl
    rw [he]
    exact Ideal.mul_mem_right _ M (Ideal.mem_map_of_mem _ ha')
  · obtain ⟨hx, hx'⟩ := hx
    obtain ⟨hy, hy'⟩ := hy
    exact ⟨add_mem hx hy, add_mem hx' hy'⟩

/-
### Ideals of `𝒪_S` are extended from `R`

Let `I` be an ideal of `𝒪_S` and `J = I ∩ R` its contraction. For `x ∈ I` the denominator ideal
`𝔡 x = {r : R | r * x ∈ R}` is divisible only by primes in `S`, because `x` is `w`-integral for
`w ∉ S`. Hence `𝔡 x * 𝒪_S = ⊤` by `map_asIdeal_eq_top`, so `1 = ∑ dᵢ cᵢ` with `dᵢ ∈ 𝔡 x` and
`cᵢ ∈ 𝒪_S`, and `x = ∑ (dᵢ * x) * cᵢ` exhibits `x` as an element of `J * 𝒪_S`, since
`dᵢ * x ∈ R ∩ I = J`.

Noetherianity is immediate from this: `J` is finitely generated as `R` is Noetherian, hence so
is its extension `I`.
-/

/-- The denominator ideal of an `S`-integer is not contained in any prime off `S`: at such a
prime `x` is integral, so it has a denominator away from the prime. -/
lemma denomIdeal_not_le {x : K} (hx : x ∈ S.integer K) {w : HeightOneSpectrum R} (hw : w ∉ S) :
    ¬ denomIdeal K x ≤ w.asIdeal := by
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer w x (hx w hw)
  refine fun hle ↦ d.property (hle ?_)
  rw [mem_denomIdeal_iff]
  exact ⟨n, by rw [mul_comm]; exact hnd⟩

/-- The denominator ideal of any `x : K` is nonzero: a common denominator lies in it. -/
lemma denomIdeal_ne_bot (x : K) : denomIdeal K x ≠ (⊥ : Ideal R) := by
  obtain ⟨⟨a, b, hb⟩, hab⟩ := IsLocalization.surj R⁰ x
  refine fun h0 ↦ nonZeroDivisors.ne_zero hb ?_
  have : b ∈ denomIdeal K x := by rw [mem_denomIdeal_iff]; exact ⟨a, by rw [mul_comm]; exact hab⟩
  simpa [h0] using this

/-- The denominator ideal of an `S`-integer extends to the unit ideal of `𝒪_S`: all its prime
factors lie in `S`, and each of those extends to the unit ideal by `map_asIdeal_eq_top`. -/
lemma map_denomIdeal_eq_top {x : K} (hx : x ∈ S.integer K) :
    Ideal.map (algebraMap R (S.integer K)) (denomIdeal K x) = ⊤ := by
  by_contra h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
  have h𝔭le : denomIdeal K x ≤ M.comap (algebraMap R (S.integer K)) :=
    (Ideal.le_comap_map).trans (Ideal.comap_mono hle)
  have h𝔭ne : M.comap (algebraMap R (S.integer K)) ≠ ⊥ :=
    fun h0 ↦ denomIdeal_ne_bot K x (le_bot_iff.mp (h0 ▸ h𝔭le))
  have hprime : (M.comap (algebraMap R (S.integer K))).IsPrime := hM.isPrime.comap _
  have hwS : (⟨_, hprime, h𝔭ne⟩ : HeightOneSpectrum R) ∈ S :=
    by_contra fun hwn ↦ denomIdeal_not_le K S hx hwn h𝔭le
  have htop := map_asIdeal_eq_top K S hwS
  exact hM.ne_top (top_le_iff.mp (htop.ge.trans Ideal.map_comap_le))

/-- **Every ideal of `𝒪_S` is extended from `R`.** -/
theorem map_comap_eq (I : Ideal (S.integer K)) :
    Ideal.map (algebraMap R (S.integer K)) (I.comap (algebraMap R (S.integer K))) = I := by
  refine le_antisymm Ideal.map_comap_le fun x hx ↦ ?_
  set f := algebraMap R (S.integer K) with hf
  set J' := Ideal.map f (I.comap f) with hJ'
  have coeval (r : R) : ((f r : S.integer K) : K) = algebraMap R K r := by
    rw [IsScalarTower.algebraMap_apply R (S.integer K) K]; rfl
  -- for a denominator `d` of `x`, the product `f d * x` is extended from `R` and lies in `I`
  have key (d : R) (hd : d ∈ denomIdeal K (x : K)) : f d * x ∈ J' := by
    rw [mem_denomIdeal_iff] at hd
    obtain ⟨s, hs⟩ := hd
    have hfx : f d * x = f s := by
      apply Subtype.val_injective
      rw [Subalgebra.coe_mul, coeval d, coeval s, hs]
    rw [hfx]
    exact Ideal.mem_map_of_mem f (show f s ∈ I from hfx ▸ I.mul_mem_left _ hx)
  -- the elements `r` with `r * x ∈ J'` form an ideal containing the extension of `denomIdeal`
  let K' : Ideal (S.integer K) :=
    { carrier := {r | r * x ∈ J'}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb ↦ by simpa [add_mul] using J'.add_mem ha hb
      smul_mem' := fun c {a} ha ↦ by
        simpa only [smul_eq_mul, Set.mem_ofPred_eq, mul_assoc] using J'.mul_mem_left c ha }
  have hsub : Ideal.map f (denomIdeal K (x : K)) ≤ K' := Ideal.map_le_iff_le_comap.mpr key
  have hmtop : Ideal.map f (denomIdeal K (x : K)) = ⊤ := map_denomIdeal_eq_top K S x.property
  have h1 : (1 : S.integer K) * x ∈ J' := hsub (hmtop.ge Submodule.mem_top)
  simpa using h1

/-
### The Dedekind property
-/

/-- The ring of `S`-integers is Noetherian: every ideal is extended from the Noetherian
ring `R` by `map_comap_eq`. -/
instance isNoetherianRing : IsNoetherianRing (S.integer K) := by
  refine (isNoetherianRing_iff_ideal_fg _).mpr fun I ↦ ?_
  rw [← map_comap_eq K S I]
  exact Ideal.FG.map (IsNoetherian.noetherian (R := R) (I.comap (algebraMap R (S.integer K))))
    (algebraMap R (S.integer K))

/-- The contraction to `R` of a nonzero prime of `𝒪_S` is a nonzero prime: if it were zero, the
prime would be `map ⊥ = ⊥` by `map_comap_eq`. -/
lemma comap_ne_bot {P : Ideal (S.integer K)} (hP : P ≠ ⊥) :
    P.comap (algebraMap R (S.integer K)) ≠ ⊥ := by
  intro h0
  exact hP (by rw [← map_comap_eq K S P, h0, Ideal.map_bot])

/-- The ring of `S`-integers has Krull dimension at most `1`: the contraction to `R` of a
nonzero prime is maximal, and equalities of ideals lift back through `map_comap_eq`. -/
instance dimensionLEOne : Ring.DimensionLEOne (S.integer K) := by
  refine ⟨fun {P} hP hPp ↦ ?_⟩
  set f := algebraMap R (S.integer K) with hf
  -- pass to a maximal ideal `M` above `P` and compare contractions in `R`
  obtain ⟨M, hM, hPM⟩ := P.exists_le_maximal hPp.ne_top
  have hcP : P.comap f ≠ ⊥ := comap_ne_bot K S hP
  have hMne : M ≠ ⊥ := fun h ↦ hP (le_bot_iff.mp (h ▸ hPM))
  have hcM : M.comap f ≠ ⊥ := comap_ne_bot K S hMne
  -- both contractions are maximal in `R`, and one contains the other, so they are equal
  have hcPmax : (P.comap f).IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime hcP (hPp.comap f)
  have hcMprime : (M.comap f).IsPrime := hM.isPrime.comap f
  have heq : P.comap f = M.comap f :=
    hcPmax.eq_of_le hcMprime.ne_top (Ideal.comap_mono hPM)
  -- lift the equality back through `map_comap_eq`
  rwa [← map_comap_eq K S P, heq, map_comap_eq K S M]

/-- **The ring of `S`-integers of a Dedekind domain is a Dedekind domain.** -/
instance isDedekindDomain : IsDedekindDomain (S.integer K) where

/-
### The height one spectrum

The primes of `𝒪_S` are the primes `v ∉ S`, via `v ↦ 𝒪_S ∩ v`. Under this correspondence the
`v`-adic valuation of `𝒪_S` is the restriction of the `v`-adic valuation of `R`, so the Selmer
group of `𝒪_S` relative to `∅` is the Selmer group of `R` relative to `S`.
-/

/-- For `v ∉ S`, the extension of `v` to `𝒪_S` is a proper ideal: it is contained in the proper
ideal of `S`-integers with `v`-valuation `< 1` (which does not contain `1`). -/
lemma map_asIdeal_ne_top {v : HeightOneSpectrum R} (hv : v ∉ S) :
    Ideal.map (algebraMap R (S.integer K)) v.asIdeal ≠ ⊤ := by
  set f := algebraMap R (S.integer K) with hf
  have coeval (r : R) : ((f r : S.integer K) : K) = algebraMap R K r := by
    rw [IsScalarTower.algebraMap_apply R (S.integer K) K]; rfl
  let 𝔪 : Ideal (S.integer K) :=
    { carrier := {x | v.valuation K (x : K) < 1}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb ↦ by
        rw [Set.mem_ofPred_eq, Subalgebra.coe_add]
        exact lt_of_le_of_lt ((v.valuation K).map_add _ _) (max_lt ha hb)
      smul_mem' := fun c {a} ha ↦ by
        have hc : v.valuation K (c : K) ≤ 1 := c.property v hv
        rw [Set.mem_ofPred_eq, smul_eq_mul, Subalgebra.coe_mul, map_mul]
        calc v.valuation K (c : K) * v.valuation K (a : K)
            ≤ 1 * v.valuation K (a : K) := by gcongr
          _ = v.valuation K (a : K) := one_mul _
          _ < 1 := ha }
  have hle : Ideal.map f v.asIdeal ≤ 𝔪 :=
    Ideal.map_le_iff_le_comap.mpr fun a ha ↦ by
      show v.valuation K ((f a : S.integer K) : K) < 1
      rw [coeval]; exact (v.valuation_lt_one_iff_mem a).mpr ha
  intro htop
  have h1 : v.valuation K ((1 : S.integer K) : K) < 1 := le_trans htop.ge hle Submodule.mem_top
  simp at h1

lemma comap_map_asIdeal {v : HeightOneSpectrum R} (hv : v ∉ S) :
    (Ideal.map (algebraMap R (S.integer K)) v.asIdeal).comap (algebraMap R (S.integer K)) =
      v.asIdeal := by
  set f := algebraMap R (S.integer K) with hf
  refine (v.isMaximal.eq_of_le ?_ Ideal.le_comap_map).symm
  rw [Ne, Ideal.comap_eq_top_iff]
  exact map_asIdeal_ne_top K S hv

lemma isMaximal_map_asIdeal {v : HeightOneSpectrum R} (hv : v ∉ S) :
    (Ideal.map (algebraMap R (S.integer K)) v.asIdeal).IsMaximal := by
  set f := algebraMap R (S.integer K) with hf
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ (map_asIdeal_ne_top K S hv)
  have hcle : v.asIdeal ≤ M.comap f := (comap_map_asIdeal K S hv).ge.trans (Ideal.comap_mono hle)
  have hceq : M.comap f = v.asIdeal :=
    (v.isMaximal.eq_of_le (hM.isPrime.comap f).ne_top hcle).symm
  rwa [← map_comap_eq K S M, hceq] at hM

/-- The extension of `v` to `𝒪_S` is a nonzero ideal: `v` is nonzero and the map is injective. -/
lemma map_asIdeal_ne_bot {v : HeightOneSpectrum R} (hv : v ∉ S) :
    Ideal.map (algebraMap R (S.integer K)) v.asIdeal ≠ ⊥ := by
  intro h
  refine v.ne_bot ?_
  rw [← comap_map_asIdeal K S hv, h,
    Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective R (S.integer K))]

/-- The prime of `𝒪_S` above a prime `v ∉ S` of `R`: the extension of `v`. -/
noncomputable def primeOfNotMem {v : HeightOneSpectrum R} (hv : v ∉ S) :
    HeightOneSpectrum (S.integer K) where
  asIdeal := Ideal.map (algebraMap R (S.integer K)) v.asIdeal
  isPrime := (isMaximal_map_asIdeal K S hv).isPrime
  ne_bot := map_asIdeal_ne_bot K S hv

@[simp] lemma primeOfNotMem_asIdeal {v : HeightOneSpectrum R} (hv : v ∉ S) :
    (primeOfNotMem K S hv).asIdeal = Ideal.map (algebraMap R (S.integer K)) v.asIdeal :=
  rfl

/-- The prime of `R` below a prime `P` of `𝒪_S`. -/
noncomputable def primeBelow (P : HeightOneSpectrum (S.integer K)) : HeightOneSpectrum R where
  asIdeal := P.asIdeal.comap (algebraMap R (S.integer K))
  isPrime := P.isPrime.comap _
  ne_bot := comap_ne_bot K S P.ne_bot

@[simp] lemma primeBelow_asIdeal (P : HeightOneSpectrum (S.integer K)) :
    (primeBelow K S P).asIdeal = P.asIdeal.comap (algebraMap R (S.integer K)) :=
  rfl

lemma primeBelow_notMem (P : HeightOneSpectrum (S.integer K)) : primeBelow K S P ∉ S := by
  intro hv
  have h1 := map_asIdeal_eq_top K S hv
  rw [primeBelow_asIdeal, map_comap_eq] at h1
  exact P.isPrime.ne_top h1

/-- The primes of `𝒪_S` are exactly the primes of `R` not in `S`. -/
noncomputable def heightOneSpectrumEquiv :
    {v : HeightOneSpectrum R // v ∉ S} ≃ HeightOneSpectrum (S.integer K) where
  toFun v := primeOfNotMem K S v.property
  invFun P := ⟨primeBelow K S P, primeBelow_notMem K S P⟩
  left_inv v := Subtype.ext <| HeightOneSpectrum.ext <| comap_map_asIdeal K S v.property
  right_inv P := HeightOneSpectrum.ext <| map_comap_eq K S P.asIdeal

/-- For `v ∉ S`, the contraction of the extension of `v ^ n` is `v ^ n`: the contraction divides
`v ^ n`, so it is `v ^ j`; extending back gives `Pⱼ = Pₙ`, whence `j = n`. -/
lemma comap_map_pow {v : HeightOneSpectrum R} (hv : v ∉ S) (n : ℕ) :
    (Ideal.map (algebraMap R (S.integer K)) (v.asIdeal ^ n)).comap
        (algebraMap R (S.integer K)) = v.asIdeal ^ n := by
  set f := algebraMap R (S.integer K) with hf
  have hP0 : Ideal.map f v.asIdeal ≠ 0 := map_asIdeal_ne_bot K S hv
  have hPnu : ¬ IsUnit (Ideal.map f v.asIdeal) :=
    fun h ↦ map_asIdeal_ne_top K S hv (Ideal.isUnit_iff.mp h)
  refine le_antisymm ?_ Ideal.le_comap_map
  have hdvd : (Ideal.map f (v.asIdeal ^ n)).comap f ∣ v.asIdeal ^ n :=
    Ideal.dvd_iff_le.mpr Ideal.le_comap_map
  obtain ⟨j, -, hassoc⟩ := (dvd_prime_pow v.prime n).mp hdvd
  rw [associated_iff_eq] at hassoc
  have hmapQ : Ideal.map f ((Ideal.map f (v.asIdeal ^ n)).comap f) =
      Ideal.map f (v.asIdeal ^ n) := map_comap_eq K S _
  rw [hassoc, Ideal.map_pow, Ideal.map_pow] at hmapQ
  rw [hassoc, (pow_inj_of_not_isUnit hPnu hP0).mp hmapQ]

/-- For `v ∉ S`, the `Pᵥ`-adic valuation on `R` (computed in `𝒪_S`) is the `v`-adic valuation:
the two chains of prime powers `v ^ k` and `Pᵥ ^ k` have matching membership. -/
lemma intValuationDef_map {v : HeightOneSpectrum R} (hv : v ∉ S) (a : R) :
    (primeOfNotMem K S hv).intValuationDef (algebraMap R (S.integer K) a) =
      v.intValuationDef a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hfa : algebraMap R (S.integer K) a ≠ 0 := fun h ↦ ha
    (FaithfulSMul.algebraMap_injective R (S.integer K)
      (h.trans (map_zero (algebraMap R (S.integer K))).symm))
  have hmem (k : ℕ) : a ∈ v.asIdeal ^ k ↔
      algebraMap R (S.integer K) a ∈ (primeOfNotMem K S hv).asIdeal ^ k := by
    rw [primeOfNotMem_asIdeal, ← Ideal.map_pow, ← Ideal.mem_comap, comap_map_pow K S hv]
  suffices h : Associates.count (Associates.mk (primeOfNotMem K S hv).asIdeal)
        (Associates.mk (Ideal.span {algebraMap R (S.integer K) a})).factors =
      Associates.count (Associates.mk v.asIdeal) (Associates.mk (Ideal.span {a})).factors by
    rw [v.intValuationDef_if_neg ha, (primeOfNotMem K S hv).intValuationDef_if_neg hfa, h]
  refine Nat.le_antisymm ?_ ?_
  · exact (v.le_count_iff ha _).mpr
      ((hmem _).mpr (((primeOfNotMem K S hv).le_count_iff hfa _).mp le_rfl))
  · exact ((primeOfNotMem K S hv).le_count_iff hfa _).mpr
      ((hmem _).mp ((v.le_count_iff ha _).mp le_rfl))

/-- The valuation of `𝒪_S` at the prime above `v` is the valuation of `R` at `v`. -/
lemma valuation_heightOneSpectrumEquiv (v : {v : HeightOneSpectrum R // v ∉ S}) (x : K) :
    (heightOneSpectrumEquiv K S v).valuation K x = (v : HeightOneSpectrum R).valuation K x := by
  have hR (a : R) : (heightOneSpectrumEquiv K S v).valuation K (algebraMap R K a) =
      (v : HeightOneSpectrum R).valuation K (algebraMap R K a) := by
    have e1 : (heightOneSpectrumEquiv K S v).valuation K (algebraMap R K a) =
        (primeOfNotMem K S v.property).intValuationDef (algebraMap R (S.integer K) a) := by
      rw [IsScalarTower.algebraMap_apply R (S.integer K) K a,
        HeightOneSpectrum.valuation_of_algebraMap]; rfl
    rw [e1, intValuationDef_map K S v.property a, HeightOneSpectrum.valuation_of_algebraMap]; rfl
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  rw [map_div₀, map_div₀, hR a, hR b]

/-
### The class group
-/

/-- `𝒪_S` is torsion-free over `R`, as `R` embeds into it. -/
instance : Module.IsTorsionFree R (S.integer K) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  exact FaithfulSMul.algebraMap_injective R (S.integer K)

/-- Extension of ideals `Cl(R) → Cl(𝒪_S)` is surjective: every ideal of `𝒪_S` is extended from
`R` (`map_comap_eq`). -/
lemma extendedHom_surjective :
    Function.Surjective (ClassGroup.extendedHom R (S.integer K)) := by
  intro c
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  have hI : (I : Ideal (S.integer K)) ≠ ⊥ := by
    have := I.2; rwa [mem_nonZeroDivisors_iff_ne_zero] at this
  refine ⟨ClassGroup.mk0 ⟨(I : Ideal (S.integer K)).comap (algebraMap R (S.integer K)),
    mem_nonZeroDivisors_iff_ne_zero.mpr (comap_ne_bot K S hI)⟩, ?_⟩
  rw [ClassGroup.extendedHom_mk0]
  exact congrArg _ (Subtype.ext (map_comap_eq K S _))

/-- The class group of `𝒪_S` is finite as soon as that of `R` is, being a quotient of it. -/
instance finite_classGroup [Finite (ClassGroup R)] : Finite (ClassGroup (S.integer K)) :=
  .of_surjective _ (extendedHom_surjective K S)

end IsDedekindDomain.SInteger

end
/- ===== end EllipticCurves/Mathlib/SIntegers.lean ===== -/

/- ===== begin EllipticCurves/Mathlib/SelmerGroup.lean (EllipticCurves @ c4c72f486112) ===== -/
section

/-
# Finiteness of Selmer groups

Let `R` be a Dedekind domain with fraction field `K`, let `S` be a set of primes of `R` and let
`n` be a positive integer. `Mathlib.RingTheory.DedekindDomain.SelmerGroup` defines the Selmer
group `K(S,n) ≤ Kˣ/(Kˣ)ⁿ` as the classes whose `v`-adic valuation is divisible by `n` for all
`v ∉ S`, and records as a `TODO` both the maps in the fundamental exact sequence and the
finiteness of `K(S,n)`. This file supplies them, and deduces the finiteness of the Selmer group
of a finite étale `K`-algebra, which is what the proof of the Weak Mordell-Weil theorem
(`EllipticCurves.WeakMordellWeil`, Step 7) needs.

## The hypotheses

The finiteness of `K(S,n)` is *not* automatic for a general Dedekind domain: it fails already for
`R = K` a field with `Kˣ` not `n`-divisible-of-finite-index. The fundamental exact sequence
```
1 → 𝒪_S(K)ˣ / (𝒪_S(K)ˣ)ⁿ → K(S,n) → Cl_S(R)[n] → 1
```
shows that the two things one needs are

* the `S`-unit group `Set.unit S K` is finitely generated, and
* the `S`-class group `Cl_S(R)` is finite.

Each of these follows from the corresponding statement for `S = ∅` together with `S` being finite:
`Cl_S(R)` is by construction a quotient of `Cl(R)`, and `𝒪_S(K)ˣ` is an extension of a subgroup
of the free abelian group `ℤ^S` by `Rˣ`. So the weakest reasonable hypotheses, and the ones used
below, are

* `[Finite (ClassGroup R)]`,
* `[Group.FG Rˣ]`,
* `S.Finite`, and
* `[NeZero n]`.

For `R` the ring of integers of a number field, the first is the class number theorem
(`Fintype (ClassGroup (𝓞 K))`) and the second is Dirichlet's unit theorem
(`Monoid.FG (𝓞 K)ˣ`), both in Mathlib; see the section `NumberField` at the end. Nothing here
needs `R` to be of *arithmetic* type beyond these two properties, and in particular the results
apply verbatim to the ring of integers of a function field.

Note that `[NeZero n]` cannot be dropped: `K(S,0) = Kˣ`.

## Implementation

The `S`-class group is realized as `ClassGroup (S.integer K)`, the class group of the ring
`𝒪_S = Set.integer S K` of `S`-integers, which `EllipticCurves.Mathlib.SIntegers` shows to be a
Dedekind domain
with fraction field `K`, height one spectrum `{v | v ∉ S}` (valuation-compatibly) and finite
class group whenever `Cl(R)` is finite. Via this dictionary the Selmer condition on a class
`u(Kˣ)ⁿ ∈ K(S,n)` says exactly that the principal fractional ideal `(u)` of `𝒪_S` has all its
valuations divisible by `n` (`mem_selmerGroup_iff_unitsNDivisible`), so the `n`-th-root class
map of `EllipticCurves.Mathlib.FractionalIdeal` (`FractionalIdeal.nthRootClass`, built from the
isomorphism of
the group of fractional ideals with the free abelian group on the primes) descends to the
right-hand map `toSClassGroup : K(S,n) →* Cl(𝒪_S)` of the fundamental exact sequence.

Note that `toSClassGroup` is *not* surjective onto `Cl(𝒪_S)` in general: its image is the
`n`-torsion subgroup (`range_toSClassGroup`), as the sequence above says.

## Main definitions

* `IsDedekindDomain.sUnitValuation`: the tuple of `v`-adic valuations of an `S`-unit,
  for `v ∈ S`.
* `IsDedekindDomain.sUnitToSelmer` and `IsDedekindDomain.sUnitModPowToSelmer`: the left-hand map
  of the fundamental exact sequence.
* `IsDedekindDomain.toSClassGroup`: the right-hand map of the fundamental exact sequence.
* `IsDedekindDomain.selmerGroupPi` and `IsDedekindDomain.selmerGroupOfEquiv`: the Selmer group of
  a finite étale algebra, presented through a decomposition into fields.

## Main statements

* `IsDedekindDomain.fg_sUnit`: finite generation of the `S`-unit group, and `finrank_sUnit`:
  its rank is `rank Rˣ + |S|` when moreover the class group of `R` is finite.
* `IsDedekindDomain.ker_toSClassGroup`: exactness of the fundamental sequence in the middle.
* `IsDedekindDomain.range_toSClassGroup`: exactness on the right; the image is the `n`-torsion
  of the class group.
* `IsDedekindDomain.finite_selmerGroup`: **the main result**, `K(S,n)` is finite.
* `IsDedekindDomain.finite_selmerGroupOfEquiv`: the Selmer group of a finite étale algebra is
  finite.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal

open scoped nonZeroDivisors

/-
### Quotients of finitely generated commutative groups
-/

/-- A commutative group is finitely generated iff it is finitely generated as a `ℤ`-module. -/
theorem Module.finite_int_additive (G : Type*) [CommGroup G] [Group.FG G] :
    Module.Finite ℤ (Additive G) :=
  Module.Finite.iff_addGroup_fg.mpr (AddGroup.fg_iff_mul_fg.mpr ‹_›)

/-- A commutative group that is finitely generated as a `ℤ`-module is finitely generated as a
group; converse direction of `Module.finite_int_additive`. -/
theorem Group.fg_of_module_finite_int {G : Type*} [CommGroup G]
    (h : Module.Finite ℤ (Additive G)) : Group.FG G :=
  AddGroup.fg_iff_mul_fg.mp (Module.Finite.iff_addGroup_fg.mp h)

/-- A subgroup of a finitely generated commutative group is finitely generated, as `ℤ` is a
Noetherian ring. (The proof passes through `Additive G`, so `to_additive` cannot translate it;
an additive version would have to be stated by hand.) -/
theorem Subgroup.fg_of_commGroup_fg {G : Type*} [CommGroup G] [Group.FG G] (H : Subgroup G) :
    Group.FG H :=
  have : Module.Finite ℤ (Additive G) := Module.finite_int_additive G
  Group.fg_of_module_finite_int <| Module.Finite.iff_fg.mpr <|
    IsNoetherian.noetherian (R := ℤ) (AddSubgroup.toIntSubmodule H.toAddSubgroup)

/-- An extension of finitely generated groups is finitely generated: if the kernel and the range
of `φ : G →* H` are finitely generated, then so is `G`. Generators: preimages of generators of
the range together with generators of the kernel. -/
theorem Group.fg_of_fg_ker_of_fg_range {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (hker : Group.FG φ.ker) (hrange : Group.FG φ.range) : Group.FG G := by
  obtain ⟨T, hT, hTfin⟩ := Group.fg_iff.mp hrange
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp hker
  set σ : φ.range → G := Function.surjInv φ.rangeRestrict_surjective with hσ
  set U : Set G := σ '' T ∪ (φ.ker.subtype '' S) with hU
  refine Group.fg_iff.mpr ⟨U, ?_, (hTfin.image σ).union (hSfin.image _)⟩
  -- the kernel is contained in the closure of `U`
  have hkerle : φ.ker ≤ Subgroup.closure U := by
    calc φ.ker = (⊤ : Subgroup φ.ker).map φ.ker.subtype := by
          rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      _ = (Subgroup.closure S).map φ.ker.subtype := by rw [hS]
      _ = Subgroup.closure (φ.ker.subtype '' S) := MonoidHom.map_closure ..
      _ ≤ Subgroup.closure U := Subgroup.closure_mono Set.subset_union_right
  -- the closure of `U` surjects onto the range
  have hmap : (Subgroup.closure U).map φ.rangeRestrict = ⊤ := by
    rw [eq_top_iff, ← hT]
    refine (Subgroup.closure_mono ?_).trans_eq (MonoidHom.map_closure ..).symm
    intro t ht
    exact ⟨σ t, Set.mem_union_left _ ⟨t, ht, rfl⟩, Function.surjInv_eq _ t⟩
  -- conclude via `comap_map_eq`
  have h := Subgroup.comap_map_eq φ.rangeRestrict (Subgroup.closure U)
  rw [hmap, Subgroup.comap_top, MonoidHom.ker_rangeRestrict,
    sup_eq_left.mpr hkerle] at h
  exact h.symm

/-- A finitely generated commutative group of finite exponent is finite. -/
theorem CommGroup.finite_of_fg_of_pow_eq_one {G : Type*} [CommGroup G] [Group.FG G] (n : ℕ)
    [NeZero n] (hn : ∀ x : G, x ^ n = 1) : Finite G := by
  let _ : Module (ZMod n) (Additive G) := AddCommGroup.zmodModule (n := n) hn
  have h₁ : Module.Finite ℤ (Additive G) :=
    Module.Finite.iff_addGroup_fg.mpr (by rwa [AddGroup.fg_iff_mul_fg])
  have h₂ : Module.Finite (ZMod n) (Additive G) :=
    Module.Finite.of_restrictScalars_finite ℤ (ZMod n) (Additive G)
  have := Module.finite_of_finite (ZMod n) (M := Additive G)
  exact Finite.of_equiv _ (Additive.toMul (α := G))

/-- The group of `n`-th power classes of a finitely generated commutative group is finite. -/
theorem CommGroup.finite_modPow {G : Type*} [CommGroup G] [Group.FG G] (n : ℕ) [NeZero n] :
    Finite (G ⧸ (powMonoidHom n : G →* G).range) := by
  have : Group.FG (G ⧸ (powMonoidHom n : G →* G).range) :=
    Group.fg_of_surjective (QuotientGroup.mk'_surjective _)
  refine finite_of_fg_of_pow_eq_one n fun x ↦ ?_
  induction x using QuotientGroup.induction_on with
  | H g => exact (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩

namespace IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

/-
### `S`-units

`Set.unit S K` is the subgroup of `x : Kˣ` with `v x = 1` for all `v ∉ S`. Sending `x` to its
tuple of valuations at the primes *in* `S` gives a homomorphism to `ℤ^S` whose kernel is the
group of `∅`-units, i.e. `Rˣ`. When `S` is finite this exhibits `Set.unit S K` as an extension
of a subgroup of a free abelian group of finite rank by `Rˣ`.
-/

variable (S : Set (HeightOneSpectrum R))

/-- The tuple of `v`-adic valuations of an `S`-unit at the primes `v ∈ S`. -/
noncomputable def sUnitValuation : S.unit K →* (S → Multiplicative ℤ) where
  toFun x v := (v : HeightOneSpectrum R).valuationOfNeZero (x : Kˣ)
  map_one' := funext fun _ ↦ map_one _
  map_mul' x y := by simp only [Subgroup.coe_mul, map_mul]; rfl

@[simp]
lemma sUnitValuation_apply (x : S.unit K) (v : S) :
    sUnitValuation K S x v = (v : HeightOneSpectrum R).valuationOfNeZero (x : Kˣ) :=
  rfl

/-- The kernel of `sUnitValuation` consists of the `∅`-units, i.e. of the units of `R`. -/
theorem ker_sUnitValuation :
    (sUnitValuation K S).ker =
      ((∅ : Set (HeightOneSpectrum R)).unit K).subgroupOf (S.unit K) := by
  ext x
  simp only [MonoidHom.mem_ker, funext_iff, Pi.one_apply, sUnitValuation_apply,
    Subgroup.mem_subgroupOf]
  refine ⟨fun hx v _ ↦ ?_, fun hx v ↦ ?_⟩
  · by_cases hv : v ∈ S
    · simpa using (v.valuationOfNeZero_eq_iff (x : Kˣ) 1).mp (hx ⟨v, hv⟩)
    · exact x.property v hv
  · exact (v.1.valuationOfNeZero_eq_iff (x : Kˣ) 1).mpr (by
      simpa using hx v.1 (Set.notMem_empty _))

variable (R) in
/-- The `∅`-units of `K` are the units of `R`. -/
noncomputable def unitsEquivEmptyUnit : Rˣ ≃* (∅ : Set (HeightOneSpectrum R)).unit K :=
  let e₁ : R ≃ₐ[R] (⊥ : Subalgebra R K) :=
    (Algebra.botEquivOfInjective (IsFractionRing.injective R K)).symm
  let e₂ : (⊥ : Subalgebra R K) ≃ₐ[R] (∅ : Set (HeightOneSpectrum R)).integer K :=
    Subalgebra.equivOfEq _ _ (IsDedekindDomain.integer_empty R K).symm
  (Units.mapEquiv (e₁.trans e₂).toRingEquiv.toMulEquiv).trans (Set.unitEquivUnitsInteger _ K).symm

/-- **Dirichlet's `S`-unit theorem**, weak form: if `Rˣ` is finitely generated and `S` is finite,
then the group of `S`-units is finitely generated.

The map `sUnitValuation` has finitely generated image (a subgroup of the free abelian group
`ℤ^S` of finite rank) and kernel isomorphic to `Rˣ` (`ker_sUnitValuation`,
`unitsEquivEmptyUnit`), and an extension of a finitely generated group by a finitely generated
group is finitely generated. -/
theorem fg_sUnit [Group.FG Rˣ] (hS : S.Finite) : Group.FG (S.unit K) := by
  have : Finite S := hS.to_subtype
  refine Group.fg_of_fg_ker_of_fg_range (sUnitValuation K S) ?_ (Subgroup.fg_of_commGroup_fg _)
  rw [ker_sUnitValuation]
  have : Group.FG ((∅ : Set (HeightOneSpectrum R)).unit K) :=
    Group.fg_of_surjective (f := (unitsEquivEmptyUnit R K).toMonoidHom)
      (unitsEquivEmptyUnit R K).surjective
  have hle : (∅ : Set (HeightOneSpectrum R)).unit K ≤ S.unit K := Set.unit_mono S.empty_subset
  exact Group.fg_of_surjective
    (f := (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hle).symm.surjective

/-
### The fundamental exact sequence
-/

variable (S : Set (HeightOneSpectrum R)) (n : ℕ)

/-- The class of an `S`-unit lies in the Selmer group `K(S,n)`. -/
noncomputable def sUnitToSelmer : S.unit K →* selmerGroup (K := K) (S := S) (n := n) where
  toFun x := ⟨QuotientGroup.mk (x : Kˣ), fun v hv ↦ by
    rw [HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff]
    have : v.valuationOfNeZero (x : Kˣ) = 1 :=
      (v.valuationOfNeZero_eq_iff (x : Kˣ) 1).mpr (by rw [x.property v hv, WithZero.coe_one])
    simp [this]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The left-hand map of the fundamental exact sequence: an `S`-unit modulo `n`-th powers of
`S`-units maps to the Selmer group `K(S,n)`. -/
noncomputable def sUnitModPowToSelmer :
    (S.unit K ⧸ (powMonoidHom n : S.unit K →* S.unit K).range) →*
      selmerGroup (K := K) (S := S) (n := n) :=
  QuotientGroup.lift _ (sUnitToSelmer K S n) <| by
    rintro _ ⟨x, rfl⟩
    refine Subtype.ext ?_
    exact (QuotientGroup.eq_one_iff _).mpr ⟨(x : Kˣ), rfl⟩

@[simp]
lemma range_sUnitModPowToSelmer :
    (sUnitModPowToSelmer K S n).range = (sUnitToSelmer K S n).range := by
  ext
  exact ⟨by rintro ⟨y, rfl⟩; induction y using QuotientGroup.induction_on with
    | H y => exact ⟨y, rfl⟩, fun ⟨y, hy⟩ ↦ ⟨QuotientGroup.mk y, hy⟩⟩

/-- Transport of the integer-valued valuation along the spectrum correspondence between the
primes of `R` off `S` and the primes of `𝒪_S`. -/
lemma SInteger.valuationOfNeZero_heightOneSpectrumEquiv (v : {v : HeightOneSpectrum R // v ∉ S})
    (u : Kˣ) : (SInteger.heightOneSpectrumEquiv K S v).valuationOfNeZero u
      = (v : HeightOneSpectrum R).valuationOfNeZero u := by
  rw [← WithZero.coe_inj,
    show ((_ : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = _ from
      HeightOneSpectrum.valuationOfNeZero_eq _ u, HeightOneSpectrum.valuationOfNeZero_eq,
    SInteger.valuation_heightOneSpectrumEquiv K S v (u : K)]

/-- The class of `u` lies in the Selmer group `K(S,n)` exactly when
the principal fractional ideal `(u)` of the `S`-integers is `n`-divisible. -/
lemma mem_selmerGroup_iff_unitsNDivisible (u : Kˣ) :
    (QuotientGroup.mk u : Units.modPow K n) ∈ selmerGroup (R := R) (K := K) (S := S) (n := n) ↔
      u ∈ unitsNDivisible (S.integer K) K n := by
  have lhs : (QuotientGroup.mk u : Units.modPow K n) ∈
        selmerGroup (R := R) (K := K) (S := S) (n := n) ↔
      ∀ v ∉ S, (n : ℤ) ∣ Multiplicative.toAdd
        ((v : HeightOneSpectrum R).valuationOfNeZero u) :=
    forall₂_congr fun v _ ↦ HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff v n u
  have rhs : u ∈ unitsNDivisible (S.integer K) K n ↔
      ∀ w : HeightOneSpectrum (S.integer K),
        (n : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
    refine forall_congr' fun w ↦ ?_
    rw [toAdd_valuationOfNeZero, Int.dvd_neg]
    show (n : ℤ) ∣ count K w ((toPrincipalIdeal (S.integer K) K u :
      (FractionalIdeal (S.integer K)⁰ K)ˣ) : FractionalIdeal (S.integer K)⁰ K) ↔ _
    rw [coe_toPrincipalIdeal]
  rw [lhs, rhs]
  constructor
  · intro h w
    rw [show w = SInteger.heightOneSpectrumEquiv K S
        ((SInteger.heightOneSpectrumEquiv K S).symm w) from
        ((SInteger.heightOneSpectrumEquiv K S).apply_symm_apply w).symm,
      SInteger.valuationOfNeZero_heightOneSpectrumEquiv]
    exact h _ ((SInteger.heightOneSpectrumEquiv K S).symm w).property
  · intro h v hv
    have := h (SInteger.heightOneSpectrumEquiv K S ⟨v, hv⟩)
    rwa [SInteger.valuationOfNeZero_heightOneSpectrumEquiv] at this

/-- The surjection from the `n`-divisible units onto the Selmer group. -/
noncomputable def selmerGroupFromUnits :
    unitsNDivisible (S.integer K) K n →* selmerGroup (R := R) (K := K) (S := S) (n := n) :=
  ((QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range).comp
    (unitsNDivisible (S.integer K) K n).subtype).codRestrict _
      (fun u ↦ (mem_selmerGroup_iff_unitsNDivisible K S n (u : Kˣ)).mpr u.2)

lemma selmerGroupFromUnits_surjective :
    Function.Surjective (selmerGroupFromUnits K S n) := by
  intro ⟨c, hc⟩
  induction c using QuotientGroup.induction_on with
  | H u =>
    exact ⟨⟨u, (mem_selmerGroup_iff_unitsNDivisible K S n u).mp hc⟩, rfl⟩

/-- The kernel of `selmerGroupFromUnits` is contained in that of the `n`-th-root class map:
an `n`-th power has principal `n`-th root. -/
lemma ker_selmerGroupFromUnits_le [NeZero n] :
    (selmerGroupFromUnits K S n).ker ≤ (nthRootClass (S.integer K) K n).ker := by
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  have : (QuotientGroup.mk (u : Kˣ) : Units.modPow K n) = 1 := congrArg Subtype.val hu
  obtain ⟨w, hw⟩ := (QuotientGroup.eq_one_iff _).mp this
  exact (nthRootClass_eq_one_iff _ _ (NeZero.ne n) u).mpr ⟨1, w, by
    rw [map_one, one_mul]; exact hw⟩

/-- The right-hand map of the fundamental exact sequence: a Selmer class is sent to the ideal
class of the `n`-th root of the principal ideal `(u)` of any representative `u`, in the class
group of the ring of `S`-integers. Obtained by descending `FractionalIdeal.nthRootClass` along
`selmerGroupFromUnits`. -/
noncomputable def toSClassGroup [NeZero n] :
    selmerGroup (R := R) (K := K) (S := S) (n := n) →* ClassGroup (S.integer K) :=
  (QuotientGroup.lift _ (nthRootClass (S.integer K) K n)
      (ker_selmerGroupFromUnits_le K S n)).comp
    (QuotientGroup.quotientKerEquivOfSurjective _
      (selmerGroupFromUnits_surjective K S n)).symm.toMonoidHom

lemma toSClassGroup_selmerGroupFromUnits [NeZero n] (u : unitsNDivisible (S.integer K) K n) :
    toSClassGroup K S n (selmerGroupFromUnits K S n u) =
      nthRootClass (S.integer K) K n u := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective _
      (selmerGroupFromUnits_surjective K S n)).symm (selmerGroupFromUnits K S n u) =
        QuotientGroup.mk u := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [toSClassGroup, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, QuotientGroup.lift_mk']

lemma coe_unitEquivUnitsInteger_symm (a : (S.integer K)ˣ) :
    ((S.unitEquivUnitsInteger K).symm a : Kˣ) =
      Units.map (algebraMap (S.integer K) K : S.integer K →* K) a := by
  apply Units.ext
  rw [Set.unitEquivUnitsInteger_symm_apply_coe]
  rfl

/-- Exactness of the fundamental exact sequence in the middle: a Selmer class has trivial
`n`-th-root ideal class exactly when it is represented by an `S`-unit. -/
theorem ker_toSClassGroup [NeZero n] :
    (toSClassGroup K S n).ker = (sUnitToSelmer K S n).range := by
  ext x
  obtain ⟨u, rfl⟩ := selmerGroupFromUnits_surjective K S n x
  rw [MonoidHom.mem_ker, toSClassGroup_selmerGroupFromUnits,
    nthRootClass_eq_one_iff _ _ (NeZero.ne n)]
  constructor
  · intro ⟨a, w, hw⟩
    refine ⟨(S.unitEquivUnitsInteger K).symm a, Subtype.ext ?_⟩
    show (QuotientGroup.mk _ : Units.modPow K n) = QuotientGroup.mk (u : Kˣ)
    have hwn : (QuotientGroup.mk (w ^ n) : Units.modPow K n) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨w, rfl⟩
    rw [coe_unitEquivUnitsInteger_symm, ← hw, QuotientGroup.mk_mul, hwn]
    exact (mul_one _).symm
  · intro ⟨s, hs⟩
    have hcoe : (QuotientGroup.mk (s : Kˣ) : Units.modPow K n) = QuotientGroup.mk (u : Kˣ) :=
      congrArg Subtype.val hs
    obtain ⟨w, hw⟩ := QuotientGroup.eq.mp hcoe
    refine ⟨S.unitEquivUnitsInteger K s, w, ?_⟩
    have hmap : Units.map (algebraMap (S.integer K) K : S.integer K →* K)
        (S.unitEquivUnitsInteger K s) = (s : Kˣ) := by
      rw [← coe_unitEquivUnitsInteger_symm, MulEquiv.symm_apply_apply]
    rw [powMonoidHom_apply] at hw
    rw [hmap, hw]
    group

/-
### Finiteness
-/

variable (R) in
/-- **The Selmer group `K(S,n)` is finite**, provided that the class group of `R` is finite, that
`Rˣ` is finitely generated, that `S` is finite and that `n ≠ 0`.

The image of `sUnitModPowToSelmer` is finite, since its source is the quotient of a finitely
generated commutative group (`fg_sUnit`) by its `n`-th powers (`CommGroup.finite_modPow`).
By `ker_toSClassGroup` that image is the kernel of `toSClassGroup`, whose target
`ClassGroup (S.integer K)` is finite by `SInteger.finite_classGroup`. -/
theorem finite_selmerGroup [Finite (ClassGroup R)] [Group.FG Rˣ] (hS : S.Finite) [NeZero n] :
    Finite (selmerGroup (K := K) (S := S) (n := n)) := by
  have := fg_sUnit K S hS
  have hker : Finite (toSClassGroup K S n).ker := by
    rw [ker_toSClassGroup, ← range_sUnitModPowToSelmer]
    have := CommGroup.finite_modPow (G := S.unit K) n
    exact Finite.Set.finite_range _
  have hquot : Finite (selmerGroup (K := K) (S := S) (n := n) ⧸ (toSClassGroup K S n).ker) :=
    .of_injective _ (QuotientGroup.kerLift_injective (toSClassGroup K S n))
  exact Finite.of_subgroup_quotient (toSClassGroup K S n).ker

/-
### Number fields

For the ring of integers of a number field both hypotheses are theorems of Mathlib, so the
finiteness of `K(S,n)` holds for every finite `S` and every `n ≠ 0`.
-/

section NumberField

open NumberField

variable (F : Type*) [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 F))) (n : ℕ)

/-- **Dirichlet's unit theorem**, `Group.FG` version: the unit group of the ring of integers of
a number field is finitely generated. -/
instance instGroupFGUnitsRingOfIntegers : Group.FG (𝓞 F)ˣ :=
  Group.fg_iff_monoid_fg.mpr inferInstance

/-- The Selmer group `K(S,n)` of a number field is finite for `S` finite and `n ≠ 0`. -/
theorem finite_selmerGroup_of_numberField [NeZero n] (hS : S.Finite) :
    Finite (selmerGroup (K := F) (S := S) (n := n)) :=
  finite_selmerGroup (𝓞 F) F S n hS

end NumberField

end IsDedekindDomain

end
/- ===== end EllipticCurves/Mathlib/SelmerGroup.lean ===== -/

/- ===== glue (written for this file) ===== -/

/-- The base change of an elliptic curve is elliptic. Mathlib states this for `W.map f`;
`W.baseChange A` is `W.map (algebraMap R A)` by definition. -/
instance WeierstrassCurve.isElliptic_baseChange_of_isElliptic {R : Type*} {A : Type*}
    [CommRing R] [CommRing A] [Algebra R A] (W : WeierstrassCurve R) [W.IsElliptic] :
    (W.baseChange A).IsElliptic :=
  inferInstanceAs (W.map (algebraMap R A)).IsElliptic

/- ===== begin statements/wp-birch-and-swinnerton-dyer-conjecture.lean (local BSD library) ===== -/
section

/-
# Birch and Swinnerton-Dyer conjecture

Source: https://en.wikipedia.org/wiki/Birch_and_Swinnerton-Dyer_conjecture
Credit: @carterleffen

We use the strong form for elliptic curves over number fields from the introduction.
The displayed formula in the article is its specialization to the rationals.
For a general number field we use the relative height and discriminant conventions of
Dokchitser and Dokchitser, Ann. of Math. 172 (2010), Conjecture 2.1.

The period, Tamagawa factors and height pairing are adapted from google-deepmind/formal-conjectures
at 9097e2f90e66, copyright 2026 The Formal Conjectures Authors and The Tau Ceti contributors,
licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
-/

namespace OMA.S_wp_birch_and_swinnerton_dyer_conjecture

open WeierstrassCurve NumberField IsDedekindDomain
open scoped Classical

noncomputable section

variable {K : Type*} [Field K]

/-- A global 1-cocycle becomes a coboundary with coefficients in the geometric points
over the completion V. The compatibility equation expresses restriction of a local
Galois automorphism along the chosen embedding of algebraic closures. -/
def locallyTrivial (E : Affine K)
    (c : Field.absoluteGaloisGroup K → Affine.Point (E⁄(AlgebraicClosure K)))
    (V : Type*) [Field V] [Algebra K V] : Prop :=
  ∀ j : AlgebraicClosure K →ₐ[K] AlgebraicClosure V,
    ∃ P : Affine.Point (E⁄(AlgebraicClosure V)),
      ∀ (τ : Field.absoluteGaloisGroup V) (σ : Field.absoluteGaloisGroup K),
        (∀ x, τ.toAlgHom (j x) = j (σ.toAlgHom x)) →
          Affine.Point.map (W' := E) j (c σ) =
            Affine.Point.map (W' := E) (τ.restrictScalars K).toAlgHom P - P

/-- Continuous cocycles that split at every place. Continuity into the discrete
group of geometric points means that each fibre is open. -/
def locallyTrivialCocycles [NumberField K] (E : Affine K) :=
  {c : Field.absoluteGaloisGroup K → Affine.Point (E⁄(AlgebraicClosure K)) //
    (∀ P, IsOpen {σ | c σ = P}) ∧
    (∀ σ τ, c (σ * τ) = c σ + Affine.Point.map (W' := E) σ.toAlgHom (c τ)) ∧
    (∀ v : InfinitePlace K, locallyTrivial E c v.Completion) ∧
    (∀ v : HeightOneSpectrum (𝓞 K), locallyTrivial E c (v.adicCompletion K))}

/-- The underlying set of the Tate–Shafarevich group. Two locally trivial cocycles
represent the same class precisely when their difference is a global coboundary. -/
def sha [NumberField K] (E : Affine K) :=
  Quot fun c d : locallyTrivialCocycles E ↦ ∃ P : Affine.Point (E⁄(AlgebraicClosure K)),
    ∀ σ, c.val σ - d.val σ = Affine.Point.map (W' := E) σ.toAlgHom P - P

end

end OMA.S_wp_birch_and_swinnerton_dyer_conjecture

end
/- ===== end statements/wp-birch-and-swinnerton-dyer-conjecture.lean ===== -/

/- ===== begin BSD/ShaTorsion.lean (local BSD library) ===== -/
section

/-
# Torsion of the locally trivial Galois cohomology classes

A continuous cocycle into the discrete geometric point group has finite image.
The twisted Galois action permutes that image. Summing its elements produces a
coboundary witness for the multiple of the cocycle by its image cardinality.
-/

namespace BSDResearch

noncomputable section

open scoped Classical
open WeierstrassCurve NumberField
open OMA.S_wp_birch_and_swinnerton_dyer_conjecture

variable {K : Type*} [Field K] [NumberField K] {E : Affine K}

/-- Multiplication of a cocycle, retaining its trivializations over every completion. -/
def multipleCocycle (n : ℕ) (c : locallyTrivialCocycles E) : locallyTrivialCocycles E := by
  refine ⟨fun σ ↦ n • c.val σ, ?_, ?_, ?_, ?_⟩
  · exact ((IsLocallyConstant.iff_isOpen_fiber.mpr c.property.1).comp (n • ·)).isOpen_fiber
  · intro σ τ
    simp [c.property.2.1, nsmul_add]
  · intro v j
    obtain ⟨P, hP⟩ := c.property.2.2.1 v j
    exact ⟨n • P, fun τ σ h ↦ by simp [hP τ σ h, nsmul_sub]⟩
  · intro v j
    obtain ⟨P, hP⟩ := c.property.2.2.2 v j
    exact ⟨n • P, fun τ σ h ↦ by simp [hP τ σ h, nsmul_sub]⟩

def zeroCocycle (E : Affine K) : locallyTrivialCocycles E := by
  refine ⟨fun _ ↦ 0, (IsLocallyConstant.const _).isOpen_fiber, by simp, ?_, ?_⟩
  all_goals exact fun _ _ ↦ ⟨0, by simp⟩

def shaZero (E : Affine K) : sha E := Quot.mk _ (zeroCocycle E)

/-- The operation on the submitted quotient induced by pointwise multiplication. -/
def shaMultiple (n : ℕ) : sha E → sha E := by
  refine Quot.map (multipleCocycle n) ?_
  rintro c d ⟨P, hP⟩
  refine ⟨n • P, fun σ ↦ ?_⟩
  change n • c.val σ - n • d.val σ = _
  rw [← nsmul_sub, hP, nsmul_sub, map_nsmul]

end

end BSDResearch

end
/- ===== end BSD/ShaTorsion.lean ===== -/

/- ===== begin BSD/ShaDescent.lean (local BSD library) ===== -/
section

/- # Prime-order descent on the actual locally trivial cocycle quotient -/

namespace BSDResearch
open WeierstrassCurve NumberField
open OMA.S_wp_birch_and_swinnerton_dyer_conjecture
open scoped Classical

variable {K : Type*} [Field K] [NumberField K] {E : Affine K}

/-- Equality in the public quotient has an actual global coboundary witness. -/
theorem sha_eq_iff (c d : locallyTrivialCocycles E) :
    (Quot.mk _ c : sha E) = Quot.mk _ d ↔
      ∃ P : Affine.Point (E⁄(AlgebraicClosure K)), ∀ σ,
        c.val σ - d.val σ = Affine.Point.map (W' := E) σ.toAlgHom P - P := by
  let S : Setoid (locallyTrivialCocycles E) := {
    r c d := ∃ P : Affine.Point (E⁄(AlgebraicClosure K)), ∀ σ : Field.absoluteGaloisGroup K,
      c.val σ - d.val σ = Affine.Point.map (W' := E) σ.toAlgHom P - P
    iseqv := {
      refl c := ⟨0,by simp⟩
      symm := by
        rintro c d ⟨P,h⟩
        exact ⟨-P,fun σ ↦ by rw [map_neg]; linear_combination (norm := abel) -(h σ)⟩
      trans := by
        rintro c d e ⟨P,hP⟩ ⟨Q,hQ⟩
        exact ⟨P+Q,fun σ ↦ by rw [map_add]; linear_combination (norm := abel) hP σ+hQ σ⟩ } }
  exact ⟨@Quotient.exact _ S c d,fun h ↦ Quot.sound h⟩

end BSDResearch

end
/- ===== end BSD/ShaDescent.lean ===== -/

/- ===== begin BSD/ShaKummer.lean (local BSD library) ===== -/
section

/- # Two-torsion representatives for locally trivial Galois cohomology -/

namespace BSDResearch
noncomputable section
open WeierstrassCurve NumberField
open OMA.S_wp_birch_and_swinnerton_dyer_conjecture
open scoped Classical Topology

variable {K : Type*} [Field K] [NumberField K] {E : Affine K}

omit [NumberField K] in
private theorem coordinate_locallyConstant (x : AlgebraicClosure K) :
    IsLocallyConstant (fun σ : Gal(AlgebraicClosure K/K) ↦ σ x) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro σ
  have ho := stabilizer_isOpen_of_isIntegral (K := K) x
  have hc : Continuous (fun τ : Gal(AlgebraicClosure K/K) ↦ σ⁻¹ * τ) := continuous_const.mul continuous_id
  have h := (ho.preimage hc).mem_nhds (x := σ) (by simp)
  filter_upwards [h] with τ ht
  change ((σ⁻¹ * τ) x) = x at ht
  simpa using congrArg σ ht

omit [NumberField K] in
theorem geometricOrbit_locallyConstant (P : Affine.Point (E⁄(AlgebraicClosure K))) :
    IsLocallyConstant (fun σ : Field.absoluteGaloisGroup K ↦ Affine.Point.map (W' := E) σ.toAlgHom P) := by
  cases P with
  | zero => exact IsLocallyConstant.const _
  | some x y h =>
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro σ
    filter_upwards [(coordinate_locallyConstant x).eventually_eq σ,(coordinate_locallyConstant y).eventually_eq σ] with τ hx hy
    simp only [Affine.Point.map_some,Affine.Point.some.injEq]
    exact ⟨hx,hy⟩

private theorem shift_local (c : locallyTrivialCocycles E) (Q : Affine.Point (E⁄(AlgebraicClosure K)))
    (V : Type*) [Field V] [Algebra K V] (hc : locallyTrivial E c.val V) :
    locallyTrivial E (fun σ ↦ c.val σ - (Affine.Point.map (W' := E) σ.toAlgHom Q - Q)) V := by
  intro j
  obtain ⟨P,hP⟩ := hc j
  refine ⟨P - Affine.Point.map (W' := E) j Q,fun τ σ h ↦ ?_⟩
  have he : j.comp σ.toAlgHom = (τ.restrictScalars K).toAlgHom.comp j := AlgHom.ext fun x ↦ (h x).symm
  simp only [map_sub,hP τ σ h,Affine.Point.map_map,he]
  abel

/-- Subtract a global coboundary, transporting the witnesses at every place. -/
def shiftCocycle (c : locallyTrivialCocycles E) (Q : Affine.Point (E⁄(AlgebraicClosure K))) :
    locallyTrivialCocycles E := by
  refine ⟨fun σ ↦ c.val σ - (Affine.Point.map (W' := E) σ.toAlgHom Q - Q), ?_, ?_, ?_, ?_⟩
  · exact ((IsLocallyConstant.iff_isOpen_fiber.mpr c.property.1).comp₂
      (geometricOrbit_locallyConstant Q) (fun a b ↦ a - (b-Q))).isOpen_fiber
  · intro σ τ
    simp only [c.property.2.1,map_sub,Affine.Point.map_map]
    change _ - (Affine.Point.map (W' := E) (σ.toAlgHom.comp τ.toAlgHom) Q - Q) = _
    abel
  · exact fun v ↦ shift_local c Q _ (c.property.2.2.1 v)
  · exact fun v ↦ shift_local c Q _ (c.property.2.2.2 v)

end
end BSDResearch

end
/- ===== end BSD/ShaKummer.lean ===== -/

/- ===== begin BSD/LocalKummerRestriction.lean (local BSD library) ===== -/
section

/- # A vanishing local Kummer condition at divisible places -/
namespace BSDResearch
open WeierstrassCurve OMA.S_wp_birch_and_swinnerton_dyer_conjecture
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {E : Affine K} [E.IsElliptic] {V : Type*} [Field V] [Algebra K V]
private abbrev C (K : Type*) [Field K] := AlgebraicClosure K
private abbrev pts (E : Affine K) (F : Type*) [Field F] [Algebra K F] := Affine.Point (E⁄F)
private abbrev gmap {A B : Type*} [Field A] [Field B] [Algebra K A] [Algebra K B] (j : A →ₐ[K] B) :=
  Affine.Point.map (W' := E) j

omit [E.IsElliptic] in
private theorem local_fixed_descends (P : pts E (C V))
    (hf : ∀ τ : Gal(C V/V), gmap (τ.restrictScalars K).toAlgHom P=P) :
    ∃ Q : pts E V, gmap (IsScalarTower.toAlgHom K V (C V)) Q=P := by
  have : CharZero V := charZero_of_injective_algebraMap (algebraMap K V).injective
  have : IsGalois V (C V) := IsGalois.mk
  cases P with
  | zero => exact ⟨0,map_zero _⟩
  | some x y H =>
    have h (τ : Gal(C V/V)) : τ x=x ∧ τ y=y := Affine.Point.some.inj (hf τ)
    obtain ⟨u,rfl⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr fun τ ↦ (h τ).1
    obtain ⟨v,rfl⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed y).mpr fun τ ↦ (h τ).2
    let j := IsScalarTower.toAlgHom K V (C V)
    exact ⟨.some u v ((E.baseChange_nonsingular j.injective u v).mp H),rfl⟩

omit [E.IsElliptic] in
/-- A local coboundary witness for a torsion-valued representative is a division
point of a rational point over the completion. -/
theorem local_kummer_point {n : ℕ} (d : locallyTrivialCocycles E)
    (hd : ∀ σ, n • d.val σ=0) (hl : locallyTrivial E d.val V) (j : C K →ₐ[K] C V) :
    ∃ (P : pts E (C V)) (R : pts E V), gmap (IsScalarTower.toAlgHom K V (C V)) R=n • P ∧
      ∀ (τ : Gal(C V/V)) (σ : Gal(C K/K)), (∀ x, τ (j x)=j (σ x)) →
        gmap j (d.val σ)=gmap (τ.restrictScalars K).toAlgHom P-P := by
  have : CharZero V := charZero_of_injective_algebraMap (algebraMap K V).injective
  obtain ⟨P,hP⟩ := hl j
  have compat (τ : Gal(C V/V)) : ∃ σ : Gal(C K/K), ∀ x, τ (j x)=j (σ x) := by
    let : Algebra (C K) (C V) := j.toRingHom.toAlgebra
    let : IsScalarTower K (C K) (C V) := IsScalarTower.of_algebraMap_eq fun x ↦ (j.commutes x).symm
    exact ⟨(τ.restrictScalars K).restrictNormal (C K),fun x ↦ ((τ.restrictScalars K).restrictNormal_commutes (C K) x).symm⟩
  have hf (τ : Gal(C V/V)) : gmap (τ.restrictScalars K).toAlgHom (n • P)=n • P := by
    obtain ⟨σ,hσ⟩ := compat τ
    have hz : n • gmap j (d.val σ) = 0 :=
      (map_nsmul (gmap j) n (d.val σ)).symm.trans
        ((congrArg (gmap j) (hd σ)).trans (map_zero (gmap j)))
    have hh : n • gmap j (d.val σ) = n • (gmap (τ.restrictScalars K).toAlgHom P - P) :=
      congrArg (n • ·) (hP τ σ hσ)
    rw [hz, nsmul_sub, ← map_nsmul] at hh
    exact sub_eq_zero.mp hh.symm
  obtain ⟨R,hR⟩ := local_fixed_descends (n • P) hf
  exact ⟨P,R,hR,hP⟩

end
end BSDResearch

end
/- ===== end BSD/LocalKummerRestriction.lean ===== -/

/- ===== begin BSD/UnramifiedKummer.lean (local BSD library) ===== -/
section

/- # Unramifiedness of locally soluble torsion cocycles at good places -/
namespace BSDResearch
open WeierstrassCurve NumberField IsDedekindDomain
open OMA.S_wp_birch_and_swinnerton_dyer_conjecture
open scoped Classical
noncomputable section

/-- Extension of a valuation subring to an arbitrary extension field. -/
theorem exists_valuation_extension {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (R : ValuationSubring K) : ∃ A : ValuationSubring L, A.comap f=R := by
  let g := f.comp R.subtype
  obtain ⟨A,hA,hg⟩ := IsLocalRing.exists_factor_valuationRing g
  let e := g.codRestrict A.toSubring hA
  refine ⟨A,SetLike.ext fun x ↦ ?_⟩
  change f x ∈ A ↔ x ∈ R
  refine ⟨fun hx ↦ ?_,fun hx ↦ hA ⟨x,hx⟩⟩
  by_contra hn
  have h₀ : x≠0 := fun h ↦ hn (h ▸ R.zero_mem)
  let z : R := ⟨x⁻¹,(R.mem_or_inv_mem x).resolve_left hn⟩
  have hu : IsUnit (e z) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨f x,hx⟩,Subtype.ext ?_⟩
    change f x⁻¹*f x=1
    rw [← map_mul,inv_mul_cancel₀ h₀,map_one]
  have hz := IsUnit.of_map e z hu
  obtain ⟨u,hu'⟩ := hz
  have he : ((↑u⁻¹ : R) : K)=x := by
    apply mul_left_cancel₀ (inv_ne_zero h₀)
    have hh := congrArg (fun t : R ↦ (t:K)) u.mul_inv
    change ((↑u : R):K)*((↑u⁻¹:R):K)=1 at hh
    rw [hu'] at hh
    exact hh.trans (inv_mul_cancel₀ h₀).symm
  exact hn (he ▸ (↑u⁻¹ : R).property)

variable {K : Type*} [Field K] [NumberField K] {E : Affine K} [E.IsElliptic]
variable (v : HeightOneSpectrum (𝓞 K))
private abbrev V := v.adicCompletion K
private abbrev R := v.adicCompletionIntegers K

theorem exists_adic_valuation_extension : ∃ A : ValuationSubring (C (V v)),
    (A.comap (algebraMap (V v) (C (V v)))).toSubring = (algebraMap (R v) (V v)).range := by
  obtain ⟨A,hA⟩ := exists_valuation_extension (algebraMap (V v) (C (V v))) Valued.v.valuationSubring
  refine ⟨A,?_⟩
  rw [hA]
  ext x
  exact ⟨fun hx ↦ ⟨⟨x,hx⟩,rfl⟩,fun ⟨y,hy⟩ ↦ hy ▸ y.property⟩

end
end BSDResearch

end
/- ===== end BSD/UnramifiedKummer.lean ===== -/

/- ===== begin BSD/TwoDescentLocal.lean (local BSD library) ===== -/
section

/-
# Algebraic input for the finiteness of `Sha[2]`

Curve-level, field-level and valuation-level statements used by `BSD.ShaTwoDescentFinite`.
Nothing here mentions cocycles.

* `exists_half`: the explicit halving formula on a Weierstrass curve whose two-division
  polynomial splits, valid in every characteristic different from two and for arbitrary
  `a₁`, `a₃`.
* `two_torsion_cases`: the points killed by two.
* `sq_mem_triple`: an element of a triquadratic extension with square in the base is a base
  multiple of a product of the adjoined square roots.
* `val_radicand`: the valuations of `x - eᵢ` at a point are squares of valuations of elements
  of the field of definition, when the `eᵢ` are integral with unit differences.
* `two_dvd_valuation_of_sq`: comparison of an arbitrary valuation centred at a height one
  prime of a Dedekind domain with the normalized valuation of that prime.
-/

namespace BSDResearch.TwoDescent

open WeierstrassCurve IsDedekindDomain
open scoped Classical WithZero

noncomputable section

/- ### Halving -/

section Halving

variable {Ω : Type*} [Field Ω]

/-- The two-division polynomial `4X³ + b₂X² + 2b₄X + b₆` equals `4(X-e₁)(X-e₂)(X-e₃)`. -/
structure TwoDivRoots (W : Affine Ω) (e₁ e₂ e₃ : Ω) : Prop where
  b₂ : W.b₂ = -4 * (e₁ + e₂ + e₃)
  b₄ : W.b₄ = 2 * (e₁ * e₂ + e₁ * e₃ + e₂ * e₃)
  b₆ : W.b₆ = -4 * (e₁ * e₂ * e₃)

variable {W : Affine Ω} {e₁ e₂ e₃ : Ω}

theorem four_ne_zero_of_two (h2 : (2 : Ω) ≠ 0) : (4 : Ω) ≠ 0 := by
  have : (4 : Ω) = 2 * 2 := by norm_num
  rw [this]
  exact mul_ne_zero h2 h2

theorem TwoDivRoots.equation_iff (he : TwoDivRoots W e₁ e₂ e₃) (h2 : (2 : Ω) ≠ 0) (x y : Ω) :
    W.Equation x y ↔ (2 * y + W.a₁ * x + W.a₃) ^ 2 = 4 * ((x - e₁) * (x - e₂) * (x - e₃)) := by
  have hb2 := he.b₂
  have hb4 := he.b₄
  have hb6 := he.b₆
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at hb2 hb4 hb6
  rw [Affine.equation_iff]
  constructor
  · intro h
    linear_combination 4 * h + x ^ 2 * hb2 + 2 * x * hb4 + hb6
  · intro h
    apply mul_left_cancel₀ (four_ne_zero_of_two h2)
    linear_combination h - x ^ 2 * hb2 - 2 * x * hb4 - hb6

theorem TwoDivRoots.Δ_eq (he : TwoDivRoots W e₁ e₂ e₃) :
    W.Δ = 16 * ((e₁ - e₂) * (e₁ - e₃) * (e₂ - e₃)) ^ 2 := by
  have h8 := W.b_relation
  rw [WeierstrassCurve.Δ, he.b₂, he.b₄, he.b₆] at *
  linear_combination (-4 * (e₁ + e₂ + e₃) ^ 2) * h8

/-- The `x`-coordinate of the half determined by the three square roots. -/
def halfX (x s₁ s₂ s₃ : Ω) : Ω := x + s₁ * s₂ + s₁ * s₃ + s₂ * s₃

/-- The `y`-coordinate of the half determined by the three square roots. -/
def halfY (W : Affine Ω) (x s₁ s₂ s₃ : Ω) : Ω :=
  (s₁ + s₂) * (s₁ + s₃) * (s₂ + s₃) - (W.a₁ * halfX x s₁ s₂ s₃ + W.a₃) / 2

/-- **Explicit halving.** If `x - eᵢ = sᵢ²` and the signs are normalized by
`2y + a₁x + a₃ = 2s₁s₂s₃`, then `(halfX, halfY)` is a point whose double is `(x, y)`. -/
theorem exists_half [W.IsElliptic] (he : TwoDivRoots W e₁ e₂ e₃) (h2 : (2 : Ω) ≠ 0)
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃) {x y : Ω} (h : W.Nonsingular x y)
    {s₁ s₂ s₃ : Ω} (hs₁ : s₁ ^ 2 = x - e₁) (hs₂ : s₂ ^ 2 = x - e₂) (hs₃ : s₃ ^ 2 = x - e₃)
    (hy : 2 * y + W.a₁ * x + W.a₃ = 2 * (s₁ * s₂ * s₃)) :
    ∃ hQ : W.Nonsingular (halfX x s₁ s₂ s₃) (halfY W x s₁ s₂ s₃),
      2 • Affine.Point.some _ _ hQ = Affine.Point.some x y h := by
  obtain rfl : e₁ = x - s₁ ^ 2 := by rw [hs₁]; ring
  obtain rfl : e₂ = x - s₂ ^ 2 := by rw [hs₂]; ring
  obtain rfl : e₃ = x - s₃ ^ 2 := by rw [hs₃]; ring
  have h4 := four_ne_zero_of_two h2
  obtain ⟨α, hα⟩ : ∃ α, W.a₁ = 2 * α := ⟨W.a₁ / 2, by field_simp⟩
  obtain ⟨β, hβ⟩ : ∃ β, W.a₃ = 2 * β := ⟨W.a₃ / 2, by field_simp⟩
  have hb2 := he.b₂
  have hb4 := he.b₄
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄] at hb2 hb4
  rw [hα] at hb2
  rw [hα, hβ] at hb4
  have ha2 : W.a₂ = -(x - s₁ ^ 2 + (x - s₂ ^ 2) + (x - s₃ ^ 2)) - α ^ 2 :=
    mul_left_cancel₀ h4 (by linear_combination hb2)
  have ha4 : W.a₄ = (x - s₁ ^ 2) * (x - s₂ ^ 2) + (x - s₁ ^ 2) * (x - s₃ ^ 2) +
      (x - s₂ ^ 2) * (x - s₃ ^ 2) - 2 * α * β :=
    mul_left_cancel₀ h2 (by linear_combination hb4)
  have hyv : y = s₁ * s₂ * s₃ - α * x - β := by
    rw [hα, hβ] at hy
    exact mul_left_cancel₀ h2 (by linear_combination hy)
  set xQ := halfX x s₁ s₂ s₃ with hxQ
  have hYQ : halfY W x s₁ s₂ s₃ = (s₁ + s₂) * (s₁ + s₃) * (s₂ + s₃) - α * xQ - β := by
    rw [halfY, hα, hβ, ← hxQ]
    field_simp
    ring
  set yQ := halfY W x s₁ s₂ s₃ with hyQ
  have hsum : ∀ {a b : Ω}, a ^ 2 ≠ b ^ 2 → a + b ≠ 0 := by
    intro a b hab h0
    apply hab
    rw [eq_neg_of_add_eq_zero_left h0]
    ring
  have hP : (s₁ + s₂) * (s₁ + s₃) * (s₂ + s₃) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (hsum fun hh ↦ h12 ?_) (hsum fun hh ↦ h13 ?_))
      (hsum fun hh ↦ h23 ?_) <;> rw [hh]
  have hEq : W.Equation xQ yQ := by
    rw [he.equation_iff h2, hYQ, hα, hβ, hxQ, halfX]
    ring
  have hQ : W.Nonsingular xQ yQ :=
    (Affine.equation_iff_nonsingular_of_Δ_ne_zero W.isUnit_Δ.ne_zero).mp hEq
  have hD : yQ - W.negY xQ yQ = 2 * ((s₁ + s₂) * (s₁ + s₃) * (s₂ + s₃)) := by
    rw [Affine.negY, hYQ, hα, hβ]
    ring
  have hne : yQ ≠ W.negY xQ yQ := fun hh ↦ by
    have h0 : yQ - W.negY xQ yQ = 0 := sub_eq_zero.mpr hh
    rw [hD] at h0
    exact mul_ne_zero h2 hP h0
  have hL : W.slope xQ xQ yQ yQ = s₁ + s₂ + s₃ - α := by
    rw [Affine.slope_of_Y_ne rfl hne, div_eq_iff (sub_ne_zero.mpr hne), hD, ha2, ha4, hYQ, hα,
      hxQ, halfX]
    ring
  refine ⟨hQ, ?_⟩
  rw [two_nsmul, Affine.Point.add_self_of_Y_ne hne]
  simp only [Affine.Point.some.injEq, Affine.addX, Affine.addY, Affine.negAddY, Affine.negY, hL]
  constructor
  · rw [ha2, hα, hxQ, halfX]
    ring
  · rw [ha2, hYQ, hyv, hα, hβ, hxQ, halfX]
    ring

/-- The points killed by two are the origin and the three points over the `eᵢ`. -/
theorem two_torsion_cases (he : TwoDivRoots W e₁ e₂ e₃) (h2 : (2 : Ω) ≠ 0) (P : W.Point)
    (hP : 2 • P = 0) :
    P = 0 ∨ ∃ x y h, P = Affine.Point.some x y h ∧ (x = e₁ ∨ x = e₂ ∨ x = e₃) ∧
      2 * y + W.a₁ * x + W.a₃ = 0 := by
  cases P with
  | zero => exact Or.inl rfl
  | some x y h =>
    right
    have hneg : Affine.Point.some x y h = -Affine.Point.some x y h := by
      rw [two_nsmul] at hP
      exact eq_neg_of_add_eq_zero_left hP
    rw [Affine.Point.neg_some] at hneg
    have hy : y = W.negY x y := (Affine.Point.some.inj hneg).2
    have hz : 2 * y + W.a₁ * x + W.a₃ = 0 := by
      rw [Affine.negY] at hy
      linear_combination hy
    have heq := (he.equation_iff h2 x y).mp ((Affine.nonsingular_iff x y).mp h).1
    rw [hz] at heq
    have h0 : (x - e₁) * (x - e₂) * (x - e₃) = 0 := by
      have heq' : 4 * ((x - e₁) * (x - e₂) * (x - e₃)) = 0 := by
        rw [← heq]
        ring
      exact (mul_eq_zero.mp heq').resolve_left (four_ne_zero_of_two h2)
    refine ⟨x, y, h, rfl, ?_, hz⟩
    rcases mul_eq_zero.mp h0 with h0 | h0
    · rcases mul_eq_zero.mp h0 with h0 | h0
      · exact Or.inl (sub_eq_zero.mp h0)
      · exact Or.inr (Or.inl (sub_eq_zero.mp h0))
    · exact Or.inr (Or.inr (sub_eq_zero.mp h0))

/-- Over each root there is a point of order two. -/
theorem exists_two_torsion [W.IsElliptic] (he : TwoDivRoots W e₁ e₂ e₃) (h2 : (2 : Ω) ≠ 0)
    {e : Ω} (hroot : e = e₁ ∨ e = e₂ ∨ e = e₃) :
    ∃ (y : Ω) (h : W.Nonsingular e y), 2 * y + W.a₁ * e + W.a₃ = 0 ∧
      2 • Affine.Point.some e y h = 0 := by
  have hz : 2 * (-(W.a₁ * e + W.a₃) / 2) + W.a₁ * e + W.a₃ = 0 := by
    field_simp
    ring
  have hEq : W.Equation e (-(W.a₁ * e + W.a₃) / 2) := by
    rw [he.equation_iff h2, hz]
    rcases hroot with rfl | rfl | rfl <;> ring
  refine ⟨_, (Affine.equation_iff_nonsingular_of_Δ_ne_zero W.isUnit_Δ.ne_zero).mp hEq, hz, ?_⟩
  rw [two_nsmul]
  apply Affine.Point.add_of_Y_eq rfl
  rw [Affine.negY]
  linear_combination hz

end Halving

/- ### Square roots in multiquadratic extensions -/

section Kummer

variable {F₀ Ω : Type*} [Field F₀] [Field Ω] [Algebra F₀ Ω]

theorem mem_adjoin_sqrt (k : IntermediateField F₀ Ω) {t : Ω} (ht : t ^ 2 ∈ k) {z : Ω}
    (hz : z ∈ IntermediateField.adjoin F₀ ((k : Set Ω) ∪ {t})) :
    ∃ p ∈ k, ∃ q ∈ k, z = p + q * t := by
  by_cases htk : t ∈ k
  · refine ⟨z, ?_, 0, k.zero_mem, by simp⟩
    refine (IntermediateField.adjoin_le_iff.mpr ?_) hz
    rintro x (hx | hx)
    · exact hx
    · rw [Set.mem_singleton_iff.mp hx]
      exact htk
  · induction hz using IntermediateField.adjoin_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact ⟨x, hx, 0, k.zero_mem, by simp⟩
      · exact ⟨0, k.zero_mem, 1, k.one_mem, by rw [Set.mem_singleton_iff.mp hx]; simp⟩
    | algebraMap x => exact ⟨_, k.algebraMap_mem x, 0, k.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨p, hp, q, hq, rfl⟩ := hx
      obtain ⟨p', hp', q', hq', rfl⟩ := hy
      exact ⟨p + p', k.add_mem hp hp', q + q', k.add_mem hq hq', by ring⟩
    | inv x _ hx =>
      obtain ⟨p, hp, q, hq, rfl⟩ := hx
      by_cases hq0 : q = 0
      · subst hq0
        exact ⟨p⁻¹, k.inv_mem hp, 0, k.zero_mem, by simp⟩
      · have hN : p ^ 2 - q ^ 2 * t ^ 2 ≠ 0 := by
          intro h0
          apply htk
          have hprod : (t - p / q) * (t + p / q) = 0 := by
            field_simp
            linear_combination -h0
          rcases mul_eq_zero.mp hprod with hh | hh
          · rw [sub_eq_zero.mp hh]
            exact k.div_mem hp hq
          · rw [eq_neg_of_add_eq_zero_left hh]
            exact k.neg_mem (k.div_mem hp hq)
        have hN' : p ^ 2 - q ^ 2 * t ^ 2 ∈ k :=
          k.sub_mem (pow_mem hp 2) (k.mul_mem (pow_mem hq 2) ht)
        have hne : p + q * t ≠ 0 := by
          intro hh
          apply hN
          linear_combination (p - q * t) * hh
        refine ⟨p / (p ^ 2 - q ^ 2 * t ^ 2), k.div_mem hp hN', -q / (p ^ 2 - q ^ 2 * t ^ 2),
          k.div_mem (k.neg_mem hq) hN', ?_⟩
        field_simp
        ring
    | mul x y _ _ hx hy =>
      obtain ⟨p, hp, q, hq, rfl⟩ := hx
      obtain ⟨p', hp', q', hq', rfl⟩ := hy
      exact ⟨p * p' + q * q' * t ^ 2, k.add_mem (k.mul_mem hp hp') (k.mul_mem (k.mul_mem hq hq') ht),
        p * q' + q * p', k.add_mem (k.mul_mem hp hq') (k.mul_mem hq hp'), by ring⟩

theorem sq_mem_cases (h2 : (2 : Ω) ≠ 0) (k : IntermediateField F₀ Ω) {t : Ω} (ht : t ^ 2 ∈ k)
    {z : Ω} (hz : z ∈ IntermediateField.adjoin F₀ ((k : Set Ω) ∪ {t})) (hz2 : z ^ 2 ∈ k) :
    z ∈ k ∨ (t ≠ 0 ∧ ∃ c ∈ k, z = c * t) := by
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_adjoin_sqrt k ht hz
  by_cases hq0 : q = 0
  · left
    rw [hq0, zero_mul, add_zero]
    exact hp
  by_cases hp0 : p = 0
  · by_cases ht0 : t = 0
    · left
      rw [hp0, ht0, mul_zero, add_zero]
      exact k.zero_mem
    · exact Or.inr ⟨ht0, q, hq, by rw [hp0, zero_add]⟩
  left
  have hmem : (p + q * t) ^ 2 - p ^ 2 - q ^ 2 * t ^ 2 ∈ k :=
    k.sub_mem (k.sub_mem hz2 (pow_mem hp 2)) (k.mul_mem (pow_mem hq 2) ht)
  have ht' : t = ((p + q * t) ^ 2 - p ^ 2 - q ^ 2 * t ^ 2) / (2 * p * q) := by
    field_simp
    ring
  have htk : t ∈ k := by
    rw [ht']
    refine k.div_mem hmem (k.mul_mem (k.mul_mem ?_ hp) hq)
    have : (2 : Ω) = algebraMap F₀ Ω 2 := by rw [map_ofNat]
    rw [this]
    exact k.algebraMap_mem 2
  exact k.add_mem hp (k.mul_mem hq htk)

/-- An element of `k(s₁,s₂,s₃)` whose square lies in `k` is an element of `k` times a
monomial in the `sᵢ`. -/
theorem sq_mem_triple (h2 : (2 : Ω) ≠ 0) (k : IntermediateField F₀ Ω) {s₁ s₂ s₃ : Ω}
    (h₁ : s₁ ^ 2 ∈ k) (h₂ : s₂ ^ 2 ∈ k) (h₃ : s₃ ^ 2 ∈ k) {z : Ω}
    (hz : z ∈ IntermediateField.adjoin F₀ ((k : Set Ω) ∪ {s₁, s₂, s₃})) (hz2 : z ^ 2 ∈ k) :
    ∃ c ∈ k, ∃ i₁ i₂ i₃ : ℕ, z = c * s₁ ^ i₁ * s₂ ^ i₂ * s₃ ^ i₃ := by
  let k₁ := IntermediateField.adjoin F₀ ((k : Set Ω) ∪ {s₁})
  let k₂ := IntermediateField.adjoin F₀ ((k₁ : Set Ω) ∪ {s₂})
  have hk₁ : k ≤ k₁ := fun x hx ↦ IntermediateField.subset_adjoin F₀ _ (Or.inl hx)
  have hk₂ : k₁ ≤ k₂ := fun x hx ↦ IntermediateField.subset_adjoin F₀ _ (Or.inl hx)
  have hz₃ : z ∈ IntermediateField.adjoin F₀ ((k₂ : Set Ω) ∪ {s₃}) := by
    refine (IntermediateField.adjoin_le_iff.mpr ?_) hz
    rintro x (hx | hx)
    · exact IntermediateField.subset_adjoin F₀ _ (Or.inl (hk₂ (hk₁ hx)))
    · rcases hx with rfl | rfl | hx
      · exact IntermediateField.subset_adjoin F₀ _ (Or.inl (hk₂
          (IntermediateField.subset_adjoin F₀ _ (Or.inr rfl))))
      · exact IntermediateField.subset_adjoin F₀ _ (Or.inl
          (IntermediateField.subset_adjoin F₀ _ (Or.inr rfl)))
      · exact IntermediateField.subset_adjoin F₀ _ (Or.inr hx)
  have A₁ : ∀ y ∈ k₁, y ^ 2 ∈ k → ∃ c ∈ k, ∃ i₁ : ℕ, y = c * s₁ ^ i₁ := by
    intro y hy hy2
    rcases sq_mem_cases h2 k h₁ hy hy2 with hh | ⟨-, c, hc, rfl⟩
    · exact ⟨y, hh, 0, by simp⟩
    · exact ⟨c, hc, 1, by simp⟩
  have quot : ∀ {c t : Ω}, t ≠ 0 → (c * t) ^ 2 ∈ k → t ^ 2 ∈ k → c ^ 2 ∈ k := by
    intro c t ht hct ht2
    have : c ^ 2 = (c * t) ^ 2 / t ^ 2 := by
      field_simp
    rw [this]
    exact k.div_mem hct ht2
  have A₂ : ∀ y ∈ k₂, y ^ 2 ∈ k → ∃ c ∈ k, ∃ i₁ i₂ : ℕ, y = c * s₁ ^ i₁ * s₂ ^ i₂ := by
    intro y hy hy2
    rcases sq_mem_cases h2 k₁ (hk₁ h₂) hy (hk₁ hy2) with hh | ⟨ht, c, hc, rfl⟩
    · obtain ⟨c, hc, i₁, rfl⟩ := A₁ y hh hy2
      exact ⟨c, hc, i₁, 0, by simp⟩
    · obtain ⟨c', hc', i₁, rfl⟩ := A₁ c hc (quot ht hy2 h₂)
      exact ⟨c', hc', i₁, 1, by simp⟩
  rcases sq_mem_cases h2 k₂ (hk₂ (hk₁ h₃)) hz₃ (hk₂ (hk₁ hz2)) with hh | ⟨ht, c, hc, rfl⟩
  · obtain ⟨c, hc, i₁, i₂, rfl⟩ := A₂ z hh hz2
    exact ⟨c, hc, i₁, i₂, 0, by simp⟩
  · obtain ⟨c', hc', i₁, i₂, rfl⟩ := A₂ c hc (quot ht hz2 h₃)
    exact ⟨c', hc', i₁, i₂, 1, by simp⟩

end Kummer

/- ### Valuations of the radicands -/

section Val

variable {Ω Γ : Type*} [Field Ω] [LinearOrderedCommGroupWithZero Γ] (val : Valuation Ω Γ)

theorem val_root_le_one {c₂ c₁ c₀ e : Ω} (h₂ : val c₂ ≤ 1) (h₁ : val c₁ ≤ 1) (h₀ : val c₀ ≤ 1)
    (he : e ^ 3 + c₂ * e ^ 2 + c₁ * e + c₀ = 0) : val e ≤ 1 := by
  by_contra hcon
  have hlt : 1 < val e := not_le.mp hcon
  have h3 : e ^ 3 = -(c₂ * e ^ 2 + c₁ * e + c₀) := by linear_combination he
  have hpow : val e ^ 2 < val e ^ 3 := pow_lt_pow_right₀ hlt (by norm_num)
  have hle : val (-(c₂ * e ^ 2 + c₁ * e + c₀)) ≤ val e ^ 2 := by
    rw [Valuation.map_neg]
    refine val.map_add_le (val.map_add_le ?_ ?_) ?_
    · rw [map_mul, map_pow]
      exact (mul_le_mul' h₂ le_rfl).trans_eq (one_mul _)
    · rw [map_mul]
      exact ((mul_le_mul' h₁ le_rfl).trans_eq (one_mul _)).trans
        (le_self_pow₀ hlt.le (by norm_num))
    · exact h₀.trans (one_le_pow₀ hlt.le)
  rw [← h3, map_pow] at hle
  exact absurd hle (not_le.mpr hpow)

private theorem eq_one_of_mul {a b : Γ} (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 :=
  le_antisymm ha (h ▸ (mul_le_mul' le_rfl hb).trans_eq (mul_one a))

theorem val_diff_eq_one {e₁ e₂ e₃ : Ω} (h₁ : val e₁ ≤ 1) (h₂ : val e₂ ≤ 1) (h₃ : val e₃ ≤ 1)
    (hD : val (((e₁ - e₂) * (e₁ - e₃) * (e₂ - e₃)) ^ 2) = 1) :
    val (e₁ - e₂) = 1 ∧ val (e₁ - e₃) = 1 ∧ val (e₂ - e₃) = 1 := by
  have a := val.map_sub_le h₁ h₂
  have b := val.map_sub_le h₁ h₃
  have c := val.map_sub_le h₂ h₃
  rw [map_pow, map_mul, map_mul, sq] at hD
  have hab : val (e₁ - e₂) * val (e₁ - e₃) ≤ 1 := (mul_le_mul' a b).trans_eq (one_mul 1)
  have habc : val (e₁ - e₂) * val (e₁ - e₃) * val (e₂ - e₃) ≤ 1 :=
    (mul_le_mul' hab c).trans_eq (one_mul 1)
  have h1 := eq_one_of_mul habc habc hD
  have h2 := eq_one_of_mul hab c h1
  have h3 := eq_one_of_mul a b h2
  refine ⟨h3, ?_, ?_⟩
  · rw [h3, one_mul] at h2
    exact h2
  · rw [h2, one_mul] at h1
    exact h1

/-- If the `eᵢ` are integral with unit differences and `y'² = (x-e₁)(x-e₂)(x-e₃)`, then the
valuation of a nonzero `x - e₁` is the square of the valuation of one of `1`, `y'`, `y'/x`. -/
theorem val_radicand {e₁ e₂ e₃ : Ω} (h₁ : val e₁ ≤ 1) (h₂ : val e₂ ≤ 1) (h₃ : val e₃ ≤ 1)
    (d₁₂ : val (e₁ - e₂) = 1) (d₁₃ : val (e₁ - e₃) = 1)
    {x y' : Ω} (hy : y' ^ 2 = (x - e₁) * (x - e₂) * (x - e₃)) (hne : x - e₁ ≠ 0) :
    ∃ c, (c = 1 ∨ c = y' ∨ c = y' / x) ∧ c ≠ 0 ∧ val (x - e₁) = val c ^ 2 := by
  by_cases hA : x - e₂ = 0
  · refine ⟨1, Or.inl rfl, one_ne_zero, ?_⟩
    rw [sub_eq_zero.mp hA, Valuation.map_sub_swap, d₁₂, map_one, one_pow]
  by_cases hB : x - e₃ = 0
  · refine ⟨1, Or.inl rfl, one_ne_zero, ?_⟩
    rw [sub_eq_zero.mp hB, Valuation.map_sub_swap, d₁₃, map_one, one_pow]
  have hy0 : y' ≠ 0 := by
    intro h0
    rw [h0] at hy
    exact mul_ne_zero (mul_ne_zero hne hA) hB (by simpa using hy.symm)
  have hvy : val y' ^ 2 = val (x - e₁) * val (x - e₂) * val (x - e₃) := by
    rw [← map_pow, hy, map_mul, map_mul]
  by_cases hx : 1 < val x
  · have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have e (e' : Ω) (he' : val e' ≤ 1) : val (x - e') = val x :=
      val.map_sub_eq_of_lt_left (he'.trans_lt hx)
    refine ⟨y' / x, Or.inr (Or.inr rfl), div_ne_zero hy0 hx0, ?_⟩
    rw [e e₁ h₁, e e₂ h₂, e e₃ h₃] at hvy
    rw [e e₁ h₁, map_div₀, div_pow, hvy]
    have hvx : val x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
    field_simp
  · have hx1 : val x ≤ 1 := not_lt.mp hx
    have hr₁ : val (x - e₁) ≤ 1 := val.map_sub_le hx1 h₁
    by_cases hu : val (x - e₁) = 1
    · exact ⟨1, Or.inl rfl, one_ne_zero, by rw [hu, map_one, one_pow]⟩
    · have hlt : val (x - e₁) < 1 := lt_of_le_of_ne hr₁ hu
      have e2 : val (x - e₂) = 1 := by
        have : x - e₂ = (e₁ - e₂) + (x - e₁) := by ring
        rw [this, val.map_add_eq_of_lt_left (by rw [d₁₂]; exact hlt), d₁₂]
      have e3 : val (x - e₃) = 1 := by
        have : x - e₃ = (e₁ - e₃) + (x - e₁) := by ring
        rw [this, val.map_add_eq_of_lt_left (by rw [d₁₃]; exact hlt), d₁₃]
      refine ⟨y', Or.inr (Or.inl rfl), hy0, ?_⟩
      rw [hvy, e2, e3, mul_one, mul_one]

/-- In an algebraic extension every value is bounded by the value of a nonzero element of
the base field. -/
theorem exists_base_bound {V : Type*} [Field V] [Algebra V Ω] [Algebra.IsAlgebraic V Ω] (y : Ω) :
    ∃ t : V, t ≠ 0 ∧ val y ≤ val (algebraMap V Ω t) := by
  by_contra hcon
  push Not at hcon
  have h1 : 1 < val y := by simpa using hcon 1 one_ne_zero
  have h0 : (0 : Γ) < val y := (zero_lt_iff.mpr one_ne_zero).trans h1
  have hc : ∀ t : V, val (algebraMap V Ω t) < val y := fun t ↦ by
    by_cases ht : t = 0
    · rw [ht, map_zero, map_zero]
      exact h0
    · exact hcon t ht
  have hint : IsIntegral V y := Algebra.IsIntegral.isIntegral y
  set p := minpoly V y with hp
  have hm : p.Monic := minpoly.monic hint
  set n := p.natDegree with hn
  have hroot : Polynomial.aeval y (Polynomial.X ^ n +
      ∑ i ∈ Finset.range n, Polynomial.C (p.coeff i) * Polynomial.X ^ i) = 0 := by
    rw [hn, ← hm.as_sum]
    exact minpoly.aeval V y
  simp only [map_add, map_pow, Polynomial.aeval_X, map_sum, map_mul, Polynomial.aeval_C] at hroot
  have hy : y ^ n = -∑ i ∈ Finset.range n, algebraMap V Ω (p.coeff i) * y ^ i :=
    eq_neg_of_add_eq_zero_left hroot
  have hlt : val (∑ i ∈ Finset.range n, algebraMap V Ω (p.coeff i) * y ^ i) < val y ^ n := by
    apply Valuation.map_sum_lt _ (pow_ne_zero _ h0.ne')
    intro i hi
    rw [map_mul, map_pow]
    calc val (algebraMap V Ω (p.coeff i)) * val y ^ i < val y * val y ^ i :=
          mul_lt_mul_of_pos_right (hc _) (pow_pos h0 i)
      _ = val y ^ (i + 1) := (pow_succ' _ _).symm
      _ ≤ val y ^ n := pow_le_pow_right₀ h1.le (Finset.mem_range.mp hi)
  rw [← Valuation.map_neg, ← hy, map_pow] at hlt
  exact lt_irrefl _ hlt

end Val

/- ### Comparison with the normalized valuation of a Dedekind prime -/

section Dedekind

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (w : HeightOneSpectrum R)

/-- An element that is integral at `w` is a fraction whose denominator is a unit at `w`. -/
theorem exists_frac_of_valuation_le_one {z : K} (hz : w.valuation K z ≤ 1) :
    ∃ α β : R, β ∉ w.asIdeal ∧ z * algebraMap R K β = algebraMap R K α := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) z
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap R K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb0
  have hvb0 : w.intValuation b ≠ 0 := w.intValuation_ne_zero' ⟨b, hb⟩
  set m : ℕ := (-(WithZero.log (w.intValuation b))).toNat with hm
  have hlog : WithZero.log (w.intValuation b) ≤ 0 := by
    rw [← WithZero.log_one]
    exact (WithZero.log_le_log hvb0 one_ne_zero).mpr (w.intValuation_le_one b)
  have hvb : w.intValuation b = WithZero.exp (-(m : ℤ)) := by
    rw [hm, Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hvb0]
  have hva : w.intValuation a ≤ WithZero.exp (-(m : ℤ)) := by
    rw [map_div₀, w.valuation_of_algebraMap, w.valuation_of_algebraMap,
      div_le_one₀ (zero_lt_iff.mpr hvb0)] at hz
    exact hz.trans_eq hvb
  obtain ⟨𝔟, h𝔟⟩ := (w.intValuation_le_pow_iff_dvd b m).mp hvb.le
  have hnot : ¬ 𝔟 ≤ w.asIdeal := by
    intro hle
    obtain ⟨𝔠, rfl⟩ := Ideal.dvd_iff_le.mpr hle
    have hdvd : w.asIdeal ^ (m + 1) ∣ Ideal.span {b} := ⟨𝔠, by rw [h𝔟, pow_succ, mul_assoc]⟩
    have := (w.intValuation_le_pow_iff_dvd b (m + 1)).mpr hdvd
    rw [hvb, WithZero.exp_le_exp] at this
    push_cast at this
    omega
  obtain ⟨x, hx𝔟, hxw⟩ := Set.not_subset.mp hnot
  have ha : a ∈ w.asIdeal ^ m :=
    Ideal.dvd_iff_le.mp ((w.intValuation_le_pow_iff_dvd a m).mp hva)
      (Ideal.mem_span_singleton_self a)
  have hmem : a * x ∈ Ideal.span {b} := by
    rw [h𝔟]
    exact Ideal.mul_mem_mul ha hx𝔟
  obtain ⟨δ, hδ⟩ := Ideal.mem_span_singleton.mp hmem
  refine ⟨δ, x, hxw, ?_⟩
  rw [div_mul_eq_mul_div, div_eq_iff hbK, ← map_mul, ← map_mul, hδ, mul_comm]

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (u : Valuation K Γ)

/-- A valuation that is integral on `R` with centre `w` has the same integers as `w`. -/
theorem le_one_of_valuation_le_one (hint : ∀ r : R, u (algebraMap R K r) ≤ 1)
    (hlt : ∀ r : R, u (algebraMap R K r) < 1 ↔ r ∈ w.asIdeal) {z : K}
    (hz : w.valuation K z ≤ 1) : u z ≤ 1 ∧ (w.valuation K z < 1 → u z < 1) ∧
      (w.valuation K z = 1 → u z = 1) := by
  obtain ⟨α, β, hβ, hzβ⟩ := exists_frac_of_valuation_le_one w hz
  have huβ : u (algebraMap R K β) = 1 :=
    le_antisymm (hint β) (not_lt.mp (mt (hlt β).mp hβ))
  have hwβ : w.valuation K (algebraMap R K β) = 1 :=
    le_antisymm (w.valuation_le_one β) (not_lt.mp (mt (w.valuation_lt_one_iff_mem β).mp hβ))
  have huz : u z = u (algebraMap R K α) := by
    rw [← hzβ, map_mul, huβ, mul_one]
  have hwz : w.valuation K z = w.valuation K (algebraMap R K α) := by
    rw [← hzβ, map_mul, hwβ, mul_one]
  refine ⟨huz ▸ hint α, fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [huz, hlt, ← w.valuation_lt_one_iff_mem (K := K), ← hwz]
    exact h
  · rw [huz]
    refine le_antisymm (hint α) (not_lt.mp fun hh ↦ ?_)
    have := (w.valuation_lt_one_iff_mem (K := K) α).mpr ((hlt α).mp hh)
    rw [← hwz, h] at this
    exact lt_irrefl _ this

/-- **Parity transfer.** If `u a = (u b)²` for a valuation `u` centred at `w`, then the
normalized `w`-adic valuation of `a` is even. -/
theorem two_dvd_valuation_of_sq (hint : ∀ r : R, u (algebraMap R K r) ≤ 1)
    (hlt : ∀ r : R, u (algebraMap R K r) < 1 ↔ r ∈ w.asIdeal) (a b : Kˣ)
    (h : u a = u b ^ 2) : (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero a) := by
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer K
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hπlt : w.valuation K π < 1 := by
    rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  set γ := u π with hγ
  have hγ1 : γ < 1 := (le_one_of_valuation_le_one w u hint hlt hπlt.le).2.1 hπlt
  have hγ0 : γ ≠ 0 := (Valuation.ne_zero_iff _).mpr hπ0
  have key : ∀ z : Kˣ, u z = γ ^ (-(Multiplicative.toAdd (w.valuationOfNeZero z))) := by
    intro z
    set n := Multiplicative.toAdd (w.valuationOfNeZero z) with hn
    have hwz : w.valuation K (z : K) = WithZero.exp n := (w.valuationOfNeZero_eq z).symm
    have hone : w.valuation K ((z : K) * π ^ n) = 1 := by
      rw [map_mul, map_zpow₀, hwz, hπ, ← WithZero.exp_zsmul, ← WithZero.exp_add]
      simp
    have := (le_one_of_valuation_le_one w u hint hlt hone.le).2.2 hone
    rw [map_mul, map_zpow₀] at this
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_left this
  rw [key a, key b, ← zpow_natCast, ← zpow_mul] at h
  have hinj := zpow_right_injective₀ (zero_lt_iff.mpr hγ0) hγ1.ne h
  exact ⟨Multiplicative.toAdd (w.valuationOfNeZero b), by push_cast at hinj; omega⟩

end Dedekind

end

end BSDResearch.TwoDescent

end
/- ===== end BSD/TwoDescentLocal.lean ===== -/

/- ===== begin BSD/ShaTwoDescentFinite.lean (local BSD library) ===== -/
section

/-
# Unconditional finiteness of `Sha(E)[2]` over a number field

The classes of the public quotient `sha E` killed by two form a finite set, for every
elliptic curve over every number field and with no hypothesis on the Weierstrass equation.

Let `F = K(E[2])`. A two-torsion valued locally trivial cocycle restricts to a homomorphism
on `Gal(K̄/F)`. Whenever it is nonzero at `σ`, there is `s` with `s² ∈ F`, `σ s = -s`, fixed by
the kernel of the restricted homomorphism (`exists_descent_radical`). Local triviality and
explicit halving on the curve show that `s²` has even valuation at every prime of `F` outside
an explicit finite set (`radical_even`). The squareclasses with that property form the finite
Selmer group `F(S, 2)`, so all these cocycles vanish on the absolute Galois group of one
finite extension `N`, and `finite_shaSplitBy` concludes.
-/

namespace BSDResearch

open WeierstrassCurve NumberField IsDedekindDomain
open OMA.S_wp_birch_and_swinnerton_dyer_conjecture
open TwoDescent
open scoped Classical Pointwise

noncomputable section

theorem exists_vieta {Ω : Type*} [Field Ω] [IsAlgClosed Ω] (c₂ c₁ c₀ : Ω) :
    ∃ e₁ e₂ e₃ : Ω, c₂ = -(e₁ + e₂ + e₃) ∧ c₁ = e₁ * e₂ + e₁ * e₃ + e₂ * e₃ ∧
      c₀ = -(e₁ * e₂ * e₃) := by
  obtain ⟨e₁, h₁⟩ := IsAlgClosed.exists_root
    (Polynomial.C (1 : Ω) * Polynomial.X ^ 3 + Polynomial.C c₂ * Polynomial.X ^ 2 +
      Polynomial.C c₁ * Polynomial.X + Polynomial.C c₀)
    (by rw [Polynomial.degree_cubic one_ne_zero]; norm_num)
  obtain ⟨e₂, h₂⟩ := IsAlgClosed.exists_root
    (Polynomial.C (1 : Ω) * Polynomial.X ^ 2 + Polynomial.C (c₂ + e₁) * Polynomial.X +
      Polynomial.C (c₁ + e₁ * c₂ + e₁ ^ 2))
    (by rw [Polynomial.degree_quadratic one_ne_zero]; norm_num)
  simp only [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X] at h₁ h₂
  refine ⟨e₁, e₂, -c₂ - e₁ - e₂, by ring, ?_, ?_⟩
  · linear_combination h₂
  · linear_combination h₁ - e₁ * h₂

theorem two_torsion_eq_of_x {A : Type*} [Field A] {W : Affine A} {x y y' : A} (h2 : (2 : A) ≠ 0)
    {h : W.Nonsingular x y} {h' : W.Nonsingular x y'} (hy : 2 * y + W.a₁ * x + W.a₃ = 0)
    (hy' : 2 * y' + W.a₁ * x + W.a₃ = 0) :
    Affine.Point.some x y h = Affine.Point.some x y' h' := by
  have hyy : y = y' := mul_left_cancel₀ h2 (by linear_combination hy - hy')
  subst hyy
  rfl

private theorem pigeon {α : Type*} {e₁ e₂ e₃ a b c d : α} (ha : a = e₁ ∨ a = e₂ ∨ a = e₃)
    (hb : b = e₁ ∨ b = e₂ ∨ b = e₃) (hc : c = e₁ ∨ c = e₂ ∨ c = e₃)
    (hd : d = e₁ ∨ d = e₂ ∨ d = e₃) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a)
    (hdb : d ≠ b) : c = d := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl <;> simp_all

variable {K : Type*} [Field K] [NumberField K]

private abbrev G (K : Type*) [Field K] := Gal(C K/K)

local instance : IsGalois K (C K) := IsGalois.mk

variable (E : Affine K)

/- ### Roots of the two-division polynomial -/

section Roots

variable {A B : Type*} [Field A] [Field B] [Algebra K A] [Algebra K B]

omit [NumberField K] in
theorem bc_b₂ : (E⁄A).b₂ = algebraMap K A E.b₂ := E.map_b₂ _

omit [NumberField K] in
theorem bc_b₄ : (E⁄A).b₄ = algebraMap K A E.b₄ := E.map_b₄ _

omit [NumberField K] in
theorem bc_b₆ : (E⁄A).b₆ = algebraMap K A E.b₆ := E.map_b₆ _

omit [NumberField K] in
theorem bc_Δ : (E⁄A).Δ = algebraMap K A E.Δ := E.map_Δ _

theorem two_ne_zero_of_algebra (K : Type*) [Field K] [NumberField K] {A : Type*} [Field A]
    [Algebra K A] : (2 : A) ≠ 0 := by
  have : CharZero A := charZero_of_injective_algebraMap (algebraMap K A).injective
  exact two_ne_zero

omit [NumberField K] in
theorem twoDivRoots_map (j : A →ₐ[K] B) {e₁ e₂ e₃ : A} (h : TwoDivRoots (E⁄A) e₁ e₂ e₃) :
    TwoDivRoots (E⁄B) (j e₁) (j e₂) (j e₃) := by
  have hb2 := congrArg j h.b₂
  have hb4 := congrArg j h.b₄
  have hb6 := congrArg j h.b₆
  rw [bc_b₂] at hb2
  rw [bc_b₄] at hb4
  rw [bc_b₆] at hb6
  simp only [AlgHom.commutes, map_mul, map_add, map_neg, map_ofNat] at hb2 hb4 hb6
  exact ⟨(bc_b₂ E).trans hb2, (bc_b₄ E).trans hb4, (bc_b₆ E).trans hb6⟩

omit [NumberField K] in
theorem exists_twoDivRoots [IsAlgClosed A] (h2 : (2 : A) ≠ 0) :
    ∃ e₁ e₂ e₃ : A, TwoDivRoots (E⁄A) e₁ e₂ e₃ := by
  obtain ⟨e₁, e₂, e₃, h₂, h₁, h₀⟩ := exists_vieta ((E⁄A).b₂ / 4) ((E⁄A).b₄ / 2) ((E⁄A).b₆ / 4)
  have h4 := four_ne_zero_of_two h2
  rw [div_eq_iff h4] at h₂ h₀
  rw [div_eq_iff h2] at h₁
  exact ⟨e₁, e₂, e₃, by linear_combination h₂, by linear_combination h₁, by linear_combination h₀⟩

omit [NumberField K] in
/-- An automorphism fixing the three roots fixes every point killed by two. -/
theorem torsion_fixed {e₁ e₂ e₃ : A} (he : TwoDivRoots (E⁄A) e₁ e₂ e₃) (h2 : (2 : A) ≠ 0)
    (f : A →ₐ[K] A) (h₁ : f e₁ = e₁) (h₂ : f e₂ = e₂) (h₃ : f e₃ = e₃)
    (P : Affine.Point (E⁄A)) (hP : 2 • P = 0) : Affine.Point.map (W' := E) f P = P := by
  rcases two_torsion_cases he h2 P hP with rfl | ⟨x, y, h, rfl, hx, hy⟩
  · exact map_zero _
  · have hfx : f x = x := by rcases hx with rfl | rfl | rfl <;> assumption
    have ha1 : f (E⁄A).a₁ = (E⁄A).a₁ := f.commutes E.a₁
    have ha3 : f (E⁄A).a₃ = (E⁄A).a₃ := f.commutes E.a₃
    have hfy : f y = y := by
      have hh := congrArg f hy
      simp only [map_add, map_mul, map_ofNat, map_zero, ha1, ha3, hfx] at hh
      exact mul_left_cancel₀ h2 (by linear_combination hh - hy)
    rw [Affine.Point.map_some]
    simp only [Affine.Point.some.injEq]
    exact ⟨hfx, hfy⟩

end Roots

/- ### The two-division field -/

/-- The field generated by the `x`-coordinates of the points of order two. -/
def divField (e₁ e₂ e₃ : C K) : IntermediateField K (C K) :=
  IntermediateField.adjoin K {e₁, e₂, e₃}

variable {e₁ e₂ e₃ : C K}

omit [NumberField K] in
theorem mem_divField₁ : e₁ ∈ divField e₁ e₂ e₃ :=
  IntermediateField.subset_adjoin K _ (by simp)

omit [NumberField K] in
theorem mem_divField₂ : e₂ ∈ divField e₁ e₂ e₃ :=
  IntermediateField.subset_adjoin K _ (by simp)

omit [NumberField K] in
theorem mem_divField₃ : e₃ ∈ divField e₁ e₂ e₃ :=
  IntermediateField.subset_adjoin K _ (by simp)

instance divField_finite : FiniteDimensional K (divField e₁ e₂ e₃) :=
  IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x

local instance intermediateNumberField (F : IntermediateField K (C K)) [FiniteDimensional K F] :
    NumberField F :=
  NumberField.of_module_finite K F

variable {E}

theorem divField_normal (he : TwoDivRoots (E⁄(C K)) e₁ e₂ e₃) : Normal K (divField e₁ e₂ e₃) := by
  have h4 : (4 : C K) ≠ 0 := four_ne_zero_of_two (two_ne_zero_of_algebra K)
  have cubic (z : C K) : 4 * ((z - e₁) * (z - e₂) * (z - e₃)) =
      4 * z ^ 3 + algebraMap K (C K) E.b₂ * z ^ 2 + 2 * algebraMap K (C K) E.b₄ * z +
        algebraMap K (C K) E.b₆ := by
    have hb2 : algebraMap K (C K) E.b₂ = -4 * (e₁ + e₂ + e₃) := (bc_b₂ E).symm.trans he.b₂
    have hb4 : algebraMap K (C K) E.b₄ = 2 * (e₁ * e₂ + e₁ * e₃ + e₂ * e₃) :=
      (bc_b₄ E).symm.trans he.b₄
    have hb6 : algebraMap K (C K) E.b₆ = -4 * (e₁ * e₂ * e₃) := (bc_b₆ E).symm.trans he.b₆
    rw [hb2, hb4, hb6]
    ring
  rw [IntermediateField.normal_iff_forall_map_le']
  intro σ
  rw [divField, IntermediateField.adjoin_map]
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨x, hx, rfl⟩
  have hroot : (x - e₁) * (x - e₂) * (x - e₃) = 0 := by
    rcases hx with rfl | rfl | rfl <;> simp
  have h0 := cubic x
  rw [hroot, mul_zero] at h0
  have h1 := congrArg σ h0
  simp only [map_zero, map_add, map_mul, map_pow, map_ofNat, AlgEquiv.commutes] at h1
  have h3 : (σ x - e₁) * (σ x - e₂) * (σ x - e₃) = 0 := by
    apply mul_left_cancel₀ h4
    rw [mul_zero, cubic]
    exact h1.symm
  apply IntermediateField.subset_adjoin
  rcases mul_eq_zero.mp h3 with h3 | h3
  · rcases mul_eq_zero.mp h3 with h3 | h3
    · exact Or.inl (sub_eq_zero.mp h3)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h3))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h3))

/- ### The Kummer generator attached to a nonzero value -/

/-- If a two-torsion valued cocycle is nonzero at `σ ∈ Gal(K̄/F)`, some `s` with `s² ∈ F`
is negated by `σ` and fixed by the kernel of the cocycle on `Gal(K̄/F)`. -/
theorem exists_descent_radical [E.IsElliptic] (he : TwoDivRoots (E⁄(C K)) e₁ e₂ e₃)
    (h12 : e₁ ≠ e₂) (d : locallyTrivialCocycles E) (hd : ∀ σ, 2 • d.val σ = 0) (σ : G K)
    (hσ : σ ∈ (divField e₁ e₂ e₃).fixingSubgroup) (hne : d.val σ ≠ 0) :
    ∃ s : C K, s ≠ 0 ∧ s ^ 2 ∈ divField e₁ e₂ e₃ ∧ σ s = -s ∧
      ∀ τ ∈ (divField e₁ e₂ e₃).fixingSubgroup, d.val τ = 0 → τ s = s := by
  set F := divField e₁ e₂ e₃ with hF
  have h2 : (2 : C K) ≠ 0 := two_ne_zero_of_algebra K
  have hom : ∀ τ₁ : G K, τ₁ ∈ F.fixingSubgroup → ∀ τ₂ : G K,
      d.val (τ₁ * τ₂ : G K) = d.val τ₁ + d.val τ₂ := by
    intro τ₁ h₁ τ₂
    refine (d.property.2.1 τ₁ τ₂).trans ?_
    congr 1
    rw [IntermediateField.mem_fixingSubgroup_iff] at h₁
    exact torsion_fixed E he h2 τ₁.toAlgHom (h₁ e₁ mem_divField₁) (h₁ e₂ mem_divField₂)
      (h₁ e₃ mem_divField₃) _ (hd τ₂)
  have hd1 : d.val (1 : G K) = 0 := by
    have hh := hom 1 (one_mem _) 1
    rw [mul_one] at hh
    exact add_left_cancel (a := d.val 1) (by rw [add_zero]; exact hh.symm)
  have hnegP : ∀ P : Affine.Point (E⁄(C K)), 2 • P = 0 → -P = P := fun P hP ↦ by
    rw [two_nsmul] at hP
    exact neg_eq_of_add_eq_zero_left hP
  have hinv : ∀ τ ∈ F.fixingSubgroup, d.val (τ⁻¹ : G K) = d.val τ := by
    intro τ hτ
    have hh := hom τ⁻¹ (inv_mem hτ) τ
    rw [inv_mul_cancel, hd1] at hh
    rw [← hnegP _ (hd τ)]
    exact eq_neg_of_add_eq_zero_left hh.symm
  rcases two_torsion_cases he h2 (d.val σ) (hd σ) with h0 | ⟨xg, yg, hg, hgeq, hxg, hyg⟩
  · exact absurd h0 hne
  obtain ⟨e, hemem, hene⟩ : ∃ e, (e = e₁ ∨ e = e₂ ∨ e = e₃) ∧ e ≠ xg := by
    by_cases h : xg = e₁
    · exact ⟨e₂, Or.inr (Or.inl rfl), fun hh ↦ h12 (h.symm.trans hh.symm)⟩
    · exact ⟨e₁, Or.inl rfl, fun hh ↦ h hh.symm⟩
  obtain ⟨yT, hT, hyT, hT2⟩ := exists_two_torsion he h2 hemem
  set T := Affine.Point.some e yT hT with hTdef
  have hTT : T + T = 0 := (two_nsmul T).symm.trans hT2
  let H' : Subgroup (G K) :=
    { carrier := {τ | τ ∈ F.fixingSubgroup ∧ (d.val τ = 0 ∨ d.val τ = T)}
      mul_mem' := by
        rintro a b ⟨ha, hBa⟩ ⟨hb, hBb⟩
        refine ⟨mul_mem ha hb, ?_⟩
        rw [hom a ha]
        rcases hBa with h | h <;> rcases hBb with h' | h' <;> rw [h, h']
        · exact Or.inl (add_zero _)
        · exact Or.inr (zero_add _)
        · exact Or.inr (add_zero _)
        · exact Or.inl hTT
      one_mem' := ⟨one_mem _, Or.inl hd1⟩
      inv_mem' := by
        rintro a ⟨ha, hBa⟩
        exact ⟨inv_mem ha, by rw [hinv a ha]; exact hBa⟩ }
  have hH'mem : ∀ τ, τ ∈ H' ↔ τ ∈ F.fixingSubgroup ∧ (d.val τ = 0 ∨ d.val τ = T) :=
    fun τ ↦ Iff.rfl
  have hσH : σ ∉ H' := by
    rintro ⟨-, h | h⟩
    · exact hne h
    · exact hene (Affine.Point.some.inj (hgeq.symm.trans h)).1.symm
  have dich : ∀ τ ∈ F.fixingSubgroup, τ ∈ H' ∨ σ⁻¹ * τ ∈ H' := by
    intro τ hτ
    by_cases h0 : d.val τ = 0
    · exact Or.inl ⟨hτ, Or.inl h0⟩
    by_cases hT' : d.val τ = T
    · exact Or.inl ⟨hτ, Or.inr hT'⟩
    right
    refine ⟨mul_mem (inv_mem hσ) hτ, ?_⟩
    rw [hom _ (inv_mem hσ), hinv σ hσ]
    by_cases hg' : d.val τ = d.val σ
    · left
      rw [hg', ← two_nsmul]
      exact hd σ
    right
    rcases two_torsion_cases he h2 (d.val τ) (hd τ) with h0' | ⟨xt, yt, ht, hteq, hxt, hyt⟩
    · exact absurd h0' h0
    have hu2 : 2 • (d.val σ + d.val τ) = 0 := by
      rw [nsmul_add]
      exact (congrArg₂ (· + ·) (hd σ) (hd τ)).trans (add_zero 0)
    rcases two_torsion_cases he h2 _ hu2 with h0' | ⟨xu, yu, hu, hueq, hxu, hyu⟩
    · exfalso
      apply hg'
      rw [← hnegP _ (hd σ)]
      exact eq_neg_of_add_eq_zero_right h0'
    have hgt : xg ≠ xt := by
      rintro rfl
      exact hg' (hteq.trans ((two_torsion_eq_of_x h2 hyt hyg).trans hgeq.symm))
    have hug : xu ≠ xg := by
      rintro rfl
      apply h0
      have hh := hueq.trans ((two_torsion_eq_of_x h2 hyu hyg).trans hgeq.symm)
      exact add_left_cancel (a := d.val σ) (by rw [add_zero]; exact hh)
    have hut : xu ≠ xt := by
      rintro rfl
      apply hne
      have hh := hueq.trans ((two_torsion_eq_of_x h2 hyu hyt).trans hteq.symm)
      exact add_right_cancel (b := d.val τ) (by rw [zero_add]; exact hh)
    have het : e ≠ xt := by
      rintro rfl
      exact hT' (hteq.trans (two_torsion_eq_of_x h2 hyt hyT))
    have hxe : xu = e := pigeon hxg hxt hxu hemem hgt hug hut hene het
    subst hxe
    exact hueq.trans (two_torsion_eq_of_x h2 hyu hyT)
  have ho : IsOpen (H' : Set (G K)) := by
    have hset : (H' : Set (G K)) =
        (F.fixingSubgroup : Set (G K)) ∩ ({τ | d.val τ = 0} ∪ {τ | d.val τ = T}) :=
      Set.ext fun τ ↦ Iff.rfl
    rw [hset]
    exact (IntermediateField.fixingSubgroup_isOpen F).inter
      ((d.property.1 0).union (d.property.1 T))
  have hL : (IntermediateField.fixedField H').fixingSubgroup = H' :=
    InfiniteGalois.fixingSubgroup_fixedField (⟨H', H'.isClosed_of_isOpen ho⟩ : ClosedSubgroup (G K))
  have hσL : σ ∉ (IntermediateField.fixedField H').fixingSubgroup := by rwa [hL]
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσL
  push Not at hσL
  obtain ⟨x, hx, hxne⟩ := hσL
  rw [IntermediateField.mem_fixedField_iff] at hx
  have hσσ : σ * σ ∈ H' := ⟨mul_mem hσ hσ, Or.inl (by rw [hom σ hσ, ← two_nsmul]; exact hd σ)⟩
  have hconj : ∀ τ ∈ H', σ⁻¹ * τ * σ ∈ H' := by
    rintro τ ⟨hτ, hB⟩
    refine ⟨mul_mem (mul_mem (inv_mem hσ) hτ) hσ, ?_⟩
    rw [hom _ (mul_mem (inv_mem hσ) hτ), hom _ (inv_mem hσ), hinv σ hσ]
    have hcomm : d.val σ + d.val τ + d.val σ = d.val τ := by
      rw [add_comm (d.val σ) (d.val τ), add_assoc, ← two_nsmul, hd σ, add_zero]
    rw [hcomm]
    exact hB
  have hsH : ∀ τ ∈ H', τ (x - σ x) = x - σ x := by
    intro τ hτ
    have h1 := hx τ hτ
    have h2' := hx _ (hconj τ hτ)
    have h3 : τ (σ x) = σ x := by
      have hh := congrArg σ h2'
      simpa [mul_assoc] using hh
    rw [map_sub, h1, h3]
  have hσs : σ (x - σ x) = -(x - σ x) := by
    have hh : σ (σ x) = x := hx _ hσσ
    rw [map_sub, hh]
    ring
  have hall : ∀ τ ∈ F.fixingSubgroup, τ (x - σ x) = x - σ x ∨ τ (x - σ x) = -(x - σ x) := by
    intro τ hτ
    rcases dich τ hτ with h | h
    · exact Or.inl (hsH τ h)
    · right
      have hh := congrArg σ (hsH _ h)
      rw [hσs] at hh
      simpa using hh
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hxne), ?_, hσs, fun τ hτ h0 ↦ hsH τ ⟨hτ, Or.inl h0⟩⟩
  rw [← InfiniteGalois.fixedField_fixingSubgroup F, IntermediateField.mem_fixedField_iff]
  intro τ hτ
  rw [map_pow]
  rcases hall τ hτ with h | h <;> rw [h]
  ring

/- ### Valuation rings of `K̄ᵥ` over the completed integers -/

section Local

private abbrev Rv (v : HeightOneSpectrum (𝓞 K)) := v.adicCompletionIntegers K

variable (v : HeightOneSpectrum (𝓞 K)) (A : ValuationSubring (C (V v)))
  (hA : (A.comap (algebraMap (V v) (C (V v)))).toSubring = (algebraMap (Rv v) (V v)).range)

include hA

theorem valA_le_one_iff (y : V v) :
    A.valuation (algebraMap (V v) (C (V v)) y) ≤ 1 ↔ Valued.v y ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff]
  have h : y ∈ (A.comap (algebraMap (V v) (C (V v)))).toSubring ↔
      y ∈ (algebraMap (Rv v) (V v)).range := by rw [hA]
  constructor
  · intro hy
    obtain ⟨r, rfl⟩ := h.mp hy
    exact r.property
  · intro hy
    exact h.mpr ⟨⟨y, hy⟩, rfl⟩

theorem valA_lt_one_iff (y : V v) :
    A.valuation (algebraMap (V v) (C (V v)) y) < 1 ↔ Valued.v y < 1 := by
  by_cases hy : y = 0
  · subst hy
    simp
  · have h := valA_le_one_iff v A hA y⁻¹
    have hy' : algebraMap (V v) (C (V v)) y ≠ 0 := (map_ne_zero _).mpr hy
    have h1 : A.valuation (algebraMap (V v) (C (V v)) y⁻¹) ≤ 1 ↔
        1 ≤ A.valuation (algebraMap (V v) (C (V v)) y) := by
      rw [map_inv₀, map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hy'))]
    have h2 : Valued.v y⁻¹ ≤ 1 ↔ 1 ≤ Valued.v y := by
      rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hy))]
    rw [← not_le, ← not_le, ← h1, ← h2, h]

omit hA in
theorem valued_algebraMap (x : K) : Valued.v (algebraMap K (V v) x) = v.valuation K x :=
  v.valuedAdicCompletion_eq_valuation' x

theorem valA_global_lt_one_iff (x : K) :
    A.valuation (algebraMap K (C (V v)) x) < 1 ↔ v.valuation K x < 1 := by
  rw [IsScalarTower.algebraMap_apply K (V v) (C (V v)), valA_lt_one_iff v A hA,
    valued_algebraMap]

omit hA in
theorem exists_approx (x : V v) : ∃ z : K, Valued.v (x - algebraMap K (V v) z) ≤ 1 := by
  have hball : {y | Valued.v (y - x) < 1} ∈ nhds x := by
    rw [Valued.mem_nhds]
    exact ⟨1, fun y hy ↦ by simpa using hy⟩
  obtain ⟨w, hwball, z, rfl⟩ :=
    mem_closure_iff_nhds.mp (HeightOneSpectrum.denseRange_algebraMap K v x) _ hball
  have hw : Valued.v (algebraMap K (V v) z - x) < 1 := hwball
  exact ⟨z, by rw [Valuation.map_sub_swap]; exact hw.le⟩

/-- **Density.** A nonzero element of the compositum `Kᵥ · j(F)` has the valuation of an
element of `j(F)`. -/
theorem exists_global_same_valuation (j : C K →ₐ[K] C (V v)) (F : IntermediateField K (C K))
    {c : C (V v)}
    (hc : c ∈ IntermediateField.adjoin (V v) (Set.range fun z : F ↦ j (z : C K))) (hc0 : c ≠ 0) :
    ∃ b : F, b ≠ 0 ∧ A.valuation c = A.valuation (j (b : C K)) := by
  set S : Set (C (V v)) := Set.range fun z : F ↦ j (z : C K) with hS
  have hSmul : S * S ⊆ S := by
    rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
    exact ⟨a * b, by simp⟩
  have hone : (1 : C (V v)) ∈ S := ⟨1, by simp⟩
  have halg : (IntermediateField.adjoin (V v) S).toSubalgebra = Algebra.adjoin (V v) S :=
    IntermediateField.adjoin_toSubalgebra_of_isAlgebraic fun x _ ↦
      Algebra.IsAlgebraic.isAlgebraic x
  have hc' : c ∈ Algebra.adjoin (V v) S := by
    rw [← halg]
    exact hc
  have hspan : c ∈ Submodule.span (V v) S := by
    refine Algebra.adjoin_induction (p := fun x _ ↦ x ∈ Submodule.span (V v) S)
      (fun x hx ↦ Submodule.subset_span hx) (fun r ↦ ?_) (fun x y _ _ hx hy ↦ add_mem hx hy)
      (fun x y _ _ hx hy ↦ ?_) hc'
    · rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hone)
    · have hxy := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at hxy
      exact Submodule.span_mono hSmul hxy
  obtain ⟨n, f, g, hsum⟩ := Submodule.mem_span_set'.mp hspan
  have hg : ∀ i, ∃ z : F, j (z : C K) = (g i : C (V v)) := fun i ↦ (g i).property
  choose z hz using hg
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  set ϖV : V v := algebraMap K (V v) π with hϖV
  have hϖVv : Valued.v ϖV = WithZero.exp (-1 : ℤ) := (valued_algebraMap v π).trans hπ
  have hϖV0 : ϖV ≠ 0 := (map_ne_zero _).mpr hπ0
  set ϖ : C (V v) := algebraMap (V v) (C (V v)) ϖV with hϖ
  have hϖ0 : ϖ ≠ 0 := (map_ne_zero _).mpr hϖV0
  have hϖ1 : A.valuation ϖ < 1 := by
    rw [hϖ, valA_lt_one_iff v A hA, hϖVv, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have arch : ∀ y : C (V v), ∃ N : ℕ, A.valuation (ϖ ^ N * y) < 1 := by
    intro y
    obtain ⟨t, ht0, hty⟩ := exists_base_bound A.valuation (V := V v) y
    have hvt : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).mpr ht0
    set N := (WithZero.log (Valued.v t) + 1).toNat with hN
    refine ⟨N, ?_⟩
    have hNt : A.valuation (ϖ ^ N * algebraMap (V v) (C (V v)) t) < 1 := by
      rw [hϖ, ← map_pow, ← map_mul, valA_lt_one_iff v A hA, map_mul, map_pow, hϖVv,
        ← WithZero.exp_log hvt, ← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero,
        WithZero.exp_lt_exp]
      have := Int.self_le_toNat (WithZero.log (Valued.v t) + 1)
      simp only [nsmul_eq_mul, mul_neg, mul_one]
      omega
    rw [map_mul] at hNt ⊢
    exact lt_of_le_of_lt (mul_le_mul' le_rfl hty) hNt
  choose N hN using fun i ↦ arch (j (z i : C K) / c)
  set M := ∑ i, N i with hM
  have hMi : ∀ i, A.valuation (ϖ ^ M * (j (z i : C K) / c)) < 1 := by
    intro i
    have hle : N i ≤ M := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    have hsplit : ϖ ^ M * (j (z i : C K) / c) =
        ϖ ^ (M - N i) * (ϖ ^ N i * (j (z i : C K) / c)) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    rw [hsplit, map_mul]
    have h1 : A.valuation (ϖ ^ (M - N i)) ≤ 1 := by
      rw [map_pow]
      exact pow_le_one' hϖ1.le _
    exact lt_of_le_of_lt ((mul_le_mul' h1 le_rfl).trans_eq (one_mul _)) (hN i)
  choose k hk using fun i ↦ exists_approx v (f i / ϖV ^ M)
  set b : F := ∑ i, (π ^ M * k i) • z i with hb
  have hjb : j (b : C K) = ∑ i, algebraMap K (C (V v)) (π ^ M * k i) * j (z i : C K) := by
    have hcoe : (b : C K) = ∑ i, (π ^ M * k i) • (z i : C K) := by
      rw [hb]
      push_cast
      rfl
    rw [hcoe, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, Algebra.smul_def]
  have hdiff : (c - j (b : C K)) / c =
      ∑ i, algebraMap (V v) (C (V v)) (f i / ϖV ^ M - algebraMap K (V v) (k i)) *
        (ϖ ^ M * (j (z i : C K) / c)) := by
    rw [hjb, ← hsum, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← hz i, Algebra.smul_def, IsScalarTower.algebraMap_apply K (V v) (C (V v)), hϖ]
    simp only [map_sub, map_mul, map_pow, map_div₀]
    rw [← hϖV]
    have hne : (algebraMap (V v) (C (V v))) ϖV ≠ 0 := hϖ0
    field_simp
  have hsmall : A.valuation ((c - j (b : C K)) / c) < 1 := by
    rw [hdiff]
    apply Valuation.map_sum_lt _ one_ne_zero
    intro i _
    rw [map_mul]
    exact lt_of_le_of_lt ((mul_le_mul' ((valA_le_one_iff v A hA _).mpr (hk i)) le_rfl).trans_eq
      (one_mul _)) (hMi i)
  have hquot : A.valuation (j (b : C K) / c) = 1 := by
    have h1 := Valuation.map_one_sub_of_lt _ hsmall
    rwa [show 1 - (c - j (b : C K)) / c = j (b : C K) / c by field_simp; ring] at h1
  have hc0' : A.valuation c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc0
  have hval : A.valuation c = A.valuation (j (b : C K)) := by
    rw [map_div₀, div_eq_one_iff_eq hc0'] at hquot
    exact hquot.symm
  refine ⟨b, fun h0 ↦ hc0' ?_, hval⟩
  rw [hval, h0]
  simp

end Local

/-- Every prime of a finite Galois extension `F` of `K` inside `K̄` is the centre on `F` of a
valuation ring of `K̄ᵥ` lying over the completed integers, for some prime `v` of `K` and some
embedding of `K̄` into `K̄ᵥ`. -/
theorem exists_centred_valuation (F : IntermediateField K (C K)) [FiniteDimensional K F]
    [IsGalois K F] (w : HeightOneSpectrum (𝓞 F)) :
    ∃ (v : HeightOneSpectrum (𝓞 K)) (j : C K →ₐ[K] C (V v)) (A : ValuationSubring (C (V v))),
      (A.comap (algebraMap (V v) (C (V v)))).toSubring = (algebraMap (Rv v) (V v)).range ∧
      (∀ r : 𝓞 F, A.valuation (j (algebraMap F (C K) (algebraMap (𝓞 F) F r))) ≤ 1) ∧
      ∀ r : 𝓞 F, A.valuation (j (algebraMap F (C K) (algebraMap (𝓞 F) F r))) < 1 ↔
        r ∈ w.asIdeal := by
  let p : Ideal (𝓞 K) := w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 F))
  have hp : p.IsPrime := Ideal.comap_isPrime _ _
  have hp0 : p ≠ ⊥ := fun h ↦ w.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)
  let v : HeightOneSpectrum (𝓞 K) := ⟨p, hp, hp0⟩
  obtain ⟨A, hA⟩ := exists_adic_valuation_extension v
  let j₀ : C K →ₐ[K] C (V v) := IsAlgClosed.lift
  have hmemA : ∀ (f : C K →ₐ[K] C (V v)) (r : 𝓞 F),
      f (algebraMap F (C K) (algebraMap (𝓞 F) F r)) ∈ A := by
    intro f r
    have h1 : IsIntegral ℤ (algebraMap (𝓞 F) F r) := RingOfIntegers.isIntegral_coe r
    have h3 : IsIntegral A (f (algebraMap F (C K) (algebraMap (𝓞 F) F r))) :=
      h1.map_of_comp_eq (Int.castRingHom A) ((f : C K →+* C (V v)).comp (algebraMap F (C K)))
        (RingHom.ext_int _ _)
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h3
    rw [← hy]
    exact y.property
  let ι : 𝓞 F →+* C (V v) :=
    (j₀ : C K →+* C (V v)).comp ((algebraMap F (C K)).comp (algebraMap (𝓞 F) F))
  have hι : ∀ r, A.valuation (ι r) ≤ 1 := fun r ↦
    (ValuationSubring.valuation_le_one_iff A _).mpr (hmemA j₀ r)
  let 𝔮 : Ideal (𝓞 F) :=
    { carrier := {r | A.valuation (ι r) < 1}
      add_mem' := fun {a b} ha hb ↦ by
        change A.valuation (ι (a + b)) < 1
        rw [map_add]
        exact Valuation.map_add_lt _ ha hb
      zero_mem' := by
        change A.valuation (ι 0) < 1
        rw [map_zero, map_zero]
        exact zero_lt_iff.mpr one_ne_zero
      smul_mem' := fun c x hx ↦ by
        change A.valuation (ι (c * x)) < 1
        rw [map_mul, map_mul]
        exact lt_of_le_of_lt ((mul_le_mul' (hι c) le_rfl).trans_eq (one_mul _)) hx }
  have h𝔮mem : ∀ r, r ∈ 𝔮 ↔ A.valuation (ι r) < 1 := fun r ↦ Iff.rfl
  have h𝔮prime : 𝔮.IsPrime := by
    refine ⟨(Ideal.ne_top_iff_one _).mpr fun h ↦ ?_, fun {x y} hxy ↦ ?_⟩
    · rw [h𝔮mem, map_one, map_one] at h
      exact lt_irrefl _ h
    · by_contra hcon
      push Not at hcon
      have hx1 : A.valuation (ι x) = 1 :=
        le_antisymm (hι x) (not_lt.mp ((h𝔮mem x).not.mp hcon.1))
      have hy1 : A.valuation (ι y) = 1 :=
        le_antisymm (hι y) (not_lt.mp ((h𝔮mem y).not.mp hcon.2))
      rw [h𝔮mem, map_mul, map_mul, hx1, hy1, one_mul] at hxy
      exact lt_irrefl _ hxy
  have h𝔮over : 𝔮.comap (algebraMap (𝓞 K) (𝓞 F)) = p := by
    ext x
    rw [Ideal.mem_comap, h𝔮mem]
    have hx : ι (algebraMap (𝓞 K) (𝓞 F) x) = algebraMap K (C (V v)) (algebraMap (𝓞 K) K x) := by
      change j₀ (algebraMap F (C K) (algebraMap (𝓞 F) F (algebraMap (𝓞 K) (𝓞 F) x))) = _
      rw [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 F) F,
        IsScalarTower.algebraMap_apply (𝓞 K) K F, ← IsScalarTower.algebraMap_apply K F (C K),
        j₀.commutes]
    rw [hx, valA_global_lt_one_iff v A hA]
    exact v.valuation_lt_one_iff_mem x
  have h𝔮P : 𝔮 ∈ p.primesOver (𝓞 F) := ⟨h𝔮prime, ⟨h𝔮over.symm⟩⟩
  have hwP : w.asIdeal ∈ p.primesOver (𝓞 F) := ⟨w.isPrime, ⟨rfl⟩⟩
  obtain ⟨σ, hσ⟩ := Ideal.exists_comap_galRestrict_eq (𝓞 K) K F (𝓞 F) h𝔮P hwP
  let g : G K := σ.liftNormal (C K)
  let j : C K →ₐ[K] C (V v) := j₀.comp (g : C K →ₐ[K] C K)
  have hj : ∀ r : 𝓞 F, j (algebraMap F (C K) (algebraMap (𝓞 F) F r)) =
      ι (galRestrict (𝓞 K) K F (𝓞 F) σ r) := by
    intro r
    change j₀ (g (algebraMap F (C K) (algebraMap (𝓞 F) F r))) =
      j₀ (algebraMap F (C K) (algebraMap (𝓞 F) F (galRestrict (𝓞 K) K F (𝓞 F) σ r)))
    rw [algebraMap_galRestrict_apply]
    exact congrArg j₀ (σ.liftNormal_commutes (C K) _)
  refine ⟨v, j, A, hA, fun r ↦ ?_, fun r ↦ ?_⟩
  · rw [hj]
    exact hι _
  · rw [hj, ← h𝔮mem, ← hσ, Ideal.mem_comap]

/- ### Parity at the good primes of the two-division field -/

/-- The primes of `F` at which the monic two-division cubic is integral with unit
discriminant. No condition is imposed at the primes above two. -/
def GoodPrime (E : Affine K) (F : IntermediateField K (C K)) [FiniteDimensional K F]
    (w : HeightOneSpectrum (𝓞 F)) : Prop :=
  w.valuation F (algebraMap K F (E.b₂ / 4)) ≤ 1 ∧ w.valuation F (algebraMap K F (E.b₄ / 2)) ≤ 1 ∧
    w.valuation F (algebraMap K F (E.b₆ / 4)) ≤ 1 ∧ w.valuation F (algebraMap K F (E.Δ / 16)) = 1

theorem finite_not_goodPrime (E : Affine K) [E.IsElliptic] (F : IntermediateField K (C K))
    [FiniteDimensional K F] : {w : HeightOneSpectrum (𝓞 F) | ¬ GoodPrime E F w}.Finite := by
  have hle : ∀ x : F, {w : HeightOneSpectrum (𝓞 F) | ¬ w.valuation F x ≤ 1}.Finite := by
    intro x
    by_cases hx : x = 0
    · subst hx
      refine Set.finite_empty.subset fun w hw ↦ hw ?_
      rw [map_zero]
      exact zero_le
    · exact (HeightOneSpectrum.finite_setOf_valuation_ne_one hx).subset fun w hw h1 ↦ hw h1.le
  have hΔ : algebraMap K F (E.Δ / 16) ≠ 0 :=
    (map_ne_zero _).mpr (div_ne_zero E.isUnit_Δ.ne_zero (by norm_num))
  refine ((((hle (algebraMap K F (E.b₂ / 4))).union (hle (algebraMap K F (E.b₄ / 2)))).union
    (hle (algebraMap K F (E.b₆ / 4)))).union
    (HeightOneSpectrum.finite_setOf_valuation_ne_one hΔ)).subset fun w hw ↦ ?_
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hcon
  exact hw ⟨hcon.1.1.1, hcon.1.1.2, hcon.1.2, hcon.2⟩

/-- **Parity.** A Kummer generator fixed by the kernel of a locally trivial two-torsion
valued cocycle has even valuation at every good prime of the two-division field. -/
theorem radical_even [E.IsElliptic] (he : TwoDivRoots (E⁄(C K)) e₁ e₂ e₃)
    (F : IntermediateField K (C K)) [FiniteDimensional K F] [IsGalois K F]
    (he₁F : e₁ ∈ F) (he₂F : e₂ ∈ F) (he₃F : e₃ ∈ F)
    (d : locallyTrivialCocycles E) (hd : ∀ σ, 2 • d.val σ = 0)
    {s : C K} (a : F) (ha : (a : C K) = s ^ 2) (ha0 : a ≠ 0)
    (hfix : ∀ τ ∈ F.fixingSubgroup, d.val τ = 0 → τ s = s)
    (w : HeightOneSpectrum (𝓞 F)) (hgood : GoodPrime E F w) :
    (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero (Units.mk0 a ha0)) := by
  obtain ⟨v, j, A, hA, hint, hlt⟩ := exists_centred_valuation F w
  set val := A.valuation with hval
  let u : Valuation F A.ValueGroup :=
    val.comap ((j : C K →+* C (V v)).comp (algebraMap F (C K)))
  have hu : ∀ z : F, u z = val (j (z : C K)) := fun z ↦ rfl
  have hw := fun (z : F) (hz : w.valuation F z ≤ 1) ↦
    le_one_of_valuation_le_one w u hint hlt hz
  have hK : ∀ x : K, u (algebraMap K F x) = val (algebraMap K (C (V v)) x) := by
    intro x
    rw [hu]
    change val (j (algebraMap F (C K) (algebraMap K F x))) = _
    rw [← IsScalarTower.algebraMap_apply K F (C K), j.commutes]
  have h2Ω : (2 : C (V v)) ≠ 0 := two_ne_zero_of_algebra K
  have h4Ω : (4 : C (V v)) ≠ 0 := four_ne_zero_of_two h2Ω
  have h16Ω : (16 : C (V v)) ≠ 0 := by
    have : (16 : C (V v)) = 4 * 4 := by norm_num
    rw [this]
    exact mul_ne_zero h4Ω h4Ω
  have he' := twoDivRoots_map E j he
  set e₁' := j e₁ with he₁'
  set e₂' := j e₂ with he₂'
  set e₃' := j e₃ with he₃'
  have hc2 : algebraMap K (C (V v)) (E.b₂ / 4) = -(e₁' + e₂' + e₃') := by
    rw [map_div₀, ← bc_b₂, he'.b₂, map_ofNat]
    field_simp
  have hc1 : algebraMap K (C (V v)) (E.b₄ / 2) = e₁' * e₂' + e₁' * e₃' + e₂' * e₃' := by
    rw [map_div₀, ← bc_b₄, he'.b₄, map_ofNat]
    field_simp
  have hc0 : algebraMap K (C (V v)) (E.b₆ / 4) = -(e₁' * e₂' * e₃') := by
    rw [map_div₀, ← bc_b₆, he'.b₆, map_ofNat]
    field_simp
  have hcΔ : algebraMap K (C (V v)) (E.Δ / 16) =
      ((e₁' - e₂') * (e₁' - e₃') * (e₂' - e₃')) ^ 2 := by
    rw [map_div₀, ← bc_Δ, he'.Δ_eq, map_ofNat]
    field_simp
  have hv2 : val (algebraMap K (C (V v)) (E.b₂ / 4)) ≤ 1 := hK _ ▸ (hw _ hgood.1).1
  have hv1 : val (algebraMap K (C (V v)) (E.b₄ / 2)) ≤ 1 := hK _ ▸ (hw _ hgood.2.1).1
  have hv0 : val (algebraMap K (C (V v)) (E.b₆ / 4)) ≤ 1 := hK _ ▸ (hw _ hgood.2.2.1).1
  have hvΔ : val (algebraMap K (C (V v)) (E.Δ / 16)) = 1 :=
    hK _ ▸ (hw _ hgood.2.2.2.le).2.2 hgood.2.2.2
  have hr₁ : val e₁' ≤ 1 := val_root_le_one val hv2 hv1 hv0 (by rw [hc2, hc1, hc0]; ring)
  have hr₂ : val e₂' ≤ 1 := val_root_le_one val hv2 hv1 hv0 (by rw [hc2, hc1, hc0]; ring)
  have hr₃ : val e₃' ≤ 1 := val_root_le_one val hv2 hv1 hv0 (by rw [hc2, hc1, hc0]; ring)
  rw [hcΔ] at hvΔ
  obtain ⟨d12, d13, d23⟩ := val_diff_eq_one val hr₁ hr₂ hr₃ hvΔ
  have hdist : ∀ {x y : C (V v)}, val (x - y) = 1 → x ≠ y := by
    rintro x y h rfl
    rw [sub_self, map_zero] at h
    exact zero_ne_one h
  have h12 := hdist d12
  have h13 := hdist d13
  have h23 := hdist d23
  have : CharZero (V v) := charZero_of_injective_algebraMap (algebraMap K (V v)).injective
  have : IsGalois (V v) (C (V v)) := IsGalois.mk
  obtain ⟨P, R, hR, hP⟩ := local_kummer_point d hd (d.property.2.2.2 v) j
  set k₀ : IntermediateField (V v) (C (V v)) :=
    IntermediateField.adjoin (V v) (Set.range fun z : F ↦ j (z : C K)) with hk₀
  have hjF : ∀ z : F, j (z : C K) ∈ k₀ := fun z ↦ IntermediateField.subset_adjoin _ _ ⟨z, rfl⟩
  have hke₁ : e₁' ∈ k₀ := hjF ⟨e₁, he₁F⟩
  have hke₂ : e₂' ∈ k₀ := hjF ⟨e₂, he₂F⟩
  have hke₃ : e₃' ∈ k₀ := hjF ⟨e₃, he₃F⟩
  have hKk : ∀ t : K, algebraMap K (C (V v)) t ∈ k₀ := fun t ↦ by
    rw [IsScalarTower.algebraMap_apply K (V v) (C (V v))]
    exact k₀.algebraMap_mem _
  have h2k : (2 : C (V v)) ∈ k₀ := by
    have h : (2 : C (V v)) = algebraMap (V v) (C (V v)) 2 := by rw [map_ofNat]
    rw [h]
    exact k₀.algebraMap_mem 2
  have compat : ∀ τ : Gal(C (V v)/V v), ∃ σ : G K, ∀ x, τ (j x) = j (σ x) := by
    intro τ
    let _ : Algebra (C K) (C (V v)) := j.toRingHom.toAlgebra
    let _ : IsScalarTower K (C K) (C (V v)) :=
      IsScalarTower.of_algebraMap_eq fun x ↦ (j.commutes x).symm
    exact ⟨(τ.restrictScalars K).restrictNormal (C K),
      fun x ↦ ((τ.restrictScalars K).restrictNormal_commutes (C K) x).symm⟩
  have hGal : ∀ τ : Gal(C (V v)/V v), τ ∈ k₀.fixingSubgroup →
      Affine.Point.map (W' := E) (τ.restrictScalars K).toAlgHom P = P → τ (j s) = j s := by
    intro τ hτ hτP
    obtain ⟨σ, hσ⟩ := compat τ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
    have hσF : σ ∈ F.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro z hz
      apply j.injective
      change j (σ z) = j z
      rw [← hσ]
      exact hτ _ (hjF ⟨z, hz⟩)
    have hdσ : d.val σ = 0 := by
      apply Affine.Point.map_injective j
      rw [map_zero, hP τ σ hσ, hτP, sub_self]
    rw [hσ, hfix σ hσF hdσ]
  have hfixe : ∀ τ : Gal(C (V v)/V v), τ ∈ k₀.fixingSubgroup →
      ∀ Q : Affine.Point (E⁄(C (V v))), 2 • Q = 0 →
        Affine.Point.map (W' := E) (τ.restrictScalars K).toAlgHom Q = Q := by
    intro τ hτ Q hQ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
    exact torsion_fixed E he' h2Ω (τ.restrictScalars K).toAlgHom (hτ _ hke₁) (hτ _ hke₂)
      (hτ _ hke₃) Q hQ
  have haj : j (a : C K) = j s ^ 2 := by rw [ha, map_pow]
  have ha0' : j (a : C K) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact fun h ↦ ha0 (Subtype.ext h)
  have main : ∃ c ∈ k₀, c ≠ 0 ∧ val (j (a : C K)) = val c ^ 2 := by
    cases R with
    | zero =>
      have hR0 : 2 • P = 0 := hR.symm.trans
        (map_zero (Affine.Point.map (W' := E) (IsScalarTower.toAlgHom K (V v) (C (V v)))))
      have hjs : j s ∈ k₀ := by
        rw [← InfiniteGalois.fixedField_fixingSubgroup k₀, IntermediateField.mem_fixedField_iff]
        exact fun τ hτ ↦ hGal τ hτ (hfixe τ hτ P hR0)
      exact ⟨j s, hjs, fun h ↦ ha0' (by rw [haj, h]; ring), by rw [haj, map_pow]⟩
    | some x₀ y₀ h₀ =>
      rw [Affine.Point.map_some] at hR
      set x : C (V v) := algebraMap (V v) (C (V v)) x₀ with hx
      set y : C (V v) := algebraMap (V v) (C (V v)) y₀ with hy
      obtain ⟨hxy, hR'⟩ : ∃ hxy : (E⁄(C (V v))).toAffine.Nonsingular x y,
          Affine.Point.some x y hxy = 2 • P := ⟨_, hR⟩
      have hxk : x ∈ k₀ := k₀.algebraMap_mem x₀
      have hyk : y ∈ k₀ := k₀.algebraMap_mem y₀
      have ha1 : (E⁄(C (V v))).a₁ ∈ k₀ := hKk E.a₁
      have ha3 : (E⁄(C (V v))).a₃ ∈ k₀ := hKk E.a₃
      set y' : C (V v) := y + ((E⁄(C (V v))).a₁ * x + (E⁄(C (V v))).a₃) / 2 with hy'
      have hy'k : y' ∈ k₀ :=
        k₀.add_mem hyk (k₀.div_mem (k₀.add_mem (k₀.mul_mem ha1 hxk) ha3) h2k)
      have heqn := (he'.equation_iff h2Ω x y).mp ((Affine.nonsingular_iff x y).mp hxy).1
      have hy'2 : y' ^ 2 = (x - e₁') * (x - e₂') * (x - e₃') := by
        apply mul_left_cancel₀ h4Ω
        rw [← heqn, hy']
        field_simp
        ring
      obtain ⟨s₁, hs₁⟩ := IsAlgClosed.exists_pow_nat_eq (x - e₁') (n := 2) two_pos
      obtain ⟨s₂, hs₂⟩ := IsAlgClosed.exists_pow_nat_eq (x - e₂') (n := 2) two_pos
      obtain ⟨s₃₀, hs₃₀⟩ := IsAlgClosed.exists_pow_nat_eq (x - e₃') (n := 2) two_pos
      obtain ⟨s₃, hs₃, hsign⟩ : ∃ s₃, s₃ ^ 2 = x - e₃' ∧
          2 * y + (E⁄(C (V v))).a₁ * x + (E⁄(C (V v))).a₃ = 2 * (s₁ * s₂ * s₃) := by
        have hsq : (2 * y + (E⁄(C (V v))).a₁ * x + (E⁄(C (V v))).a₃) ^ 2 =
            (2 * (s₁ * s₂ * s₃₀)) ^ 2 := by
          rw [heqn, ← hs₁, ← hs₂, ← hs₃₀]
          ring
        rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with h | h
        · exact ⟨s₃₀, hs₃₀, h⟩
        · exact ⟨-s₃₀, by rw [neg_sq]; exact hs₃₀, by rw [h]; ring⟩
      obtain ⟨hQ, hQ2⟩ := exists_half he' h2Ω h12 h13 h23 hxy hs₁ hs₂ hs₃ hsign
      set Q := Affine.Point.some _ _ hQ with hQdef
      have hT : 2 • (P - Q) = 0 := by rw [nsmul_sub, hQ2, hR', sub_self]
      set k₃ : IntermediateField (V v) (C (V v)) :=
        IntermediateField.adjoin (V v) ((k₀ : Set (C (V v))) ∪ {s₁, s₂, s₃}) with hk₃
      have hk₀₃ : k₀ ≤ k₃ := fun z hz ↦ IntermediateField.subset_adjoin _ _ (Or.inl hz)
      have hs₁k : s₁ ∈ k₃ := IntermediateField.subset_adjoin _ _ (Or.inr (by simp))
      have hs₂k : s₂ ∈ k₃ := IntermediateField.subset_adjoin _ _ (Or.inr (by simp))
      have hs₃k : s₃ ∈ k₃ := IntermediateField.subset_adjoin _ _ (Or.inr (by simp))
      have hjs : j s ∈ k₃ := by
        rw [← InfiniteGalois.fixedField_fixingSubgroup k₃, IntermediateField.mem_fixedField_iff]
        intro τ hτ
        have hτ₀ : τ ∈ k₀.fixingSubgroup := IntermediateField.fixingSubgroup_antitone hk₀₃ hτ
        rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
        refine hGal τ hτ₀ ?_
        set f := (τ.restrictScalars K).toAlgHom with hf
        have hfx : f x = x := τ.commutes x₀
        have hf1 : f s₁ = s₁ := hτ _ hs₁k
        have hf2 : f s₂ = s₂ := hτ _ hs₂k
        have hf3 : f s₃ = s₃ := hτ _ hs₃k
        have hfa1 : f (E⁄(C (V v))).a₁ = (E⁄(C (V v))).a₁ := f.commutes E.a₁
        have hfa3 : f (E⁄(C (V v))).a₃ = (E⁄(C (V v))).a₃ := f.commutes E.a₃
        have hτQ : Affine.Point.map (W' := E) f Q = Q := by
          rw [hQdef, Affine.Point.map_some]
          simp only [halfX, halfY, map_sub, map_add, map_mul, map_div₀, map_ofNat, hfx, hf1, hf2,
            hf3, hfa1, hfa3]
        have hτT := hfixe τ hτ₀ (P - Q) hT
        have hPQ : P = Q + (P - Q) := by abel
        rw [hPQ, map_add, hτQ, hτT]
      have hs₁0 : s₁ ^ 2 ∈ k₀ := hs₁ ▸ k₀.sub_mem hxk hke₁
      have hs₂0 : s₂ ^ 2 ∈ k₀ := hs₂ ▸ k₀.sub_mem hxk hke₂
      have hs₃0 : s₃ ^ 2 ∈ k₀ := hs₃ ▸ k₀.sub_mem hxk hke₃
      obtain ⟨c, hc, i₁, i₂, i₃, hcs⟩ :=
        sq_mem_triple h2Ω k₀ hs₁0 hs₂0 hs₃0 hjs (haj ▸ hjF a)
      have hexp : j (a : C K) = c ^ 2 * (x - e₁') ^ i₁ * (x - e₂') ^ i₂ * (x - e₃') ^ i₃ := by
        rw [haj, hcs, ← hs₁, ← hs₂, ← hs₃]
        ring
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact ha0' (by rw [hexp]; ring)
      have hp₁ : (x - e₁') ^ i₁ ≠ 0 := fun h ↦ ha0' (by rw [hexp, h]; ring)
      have hp₂ : (x - e₂') ^ i₂ ≠ 0 := fun h ↦ ha0' (by rw [hexp, h]; ring)
      have hp₃ : (x - e₃') ^ i₃ ≠ 0 := fun h ↦ ha0' (by rw [hexp, h]; ring)
      have hrad : ∀ (r : C (V v)) (i : ℕ), r ^ i ≠ 0 →
          (r ≠ 0 → ∃ c, (c = 1 ∨ c = y' ∨ c = y' / x) ∧ c ≠ 0 ∧ val r = val c ^ 2) →
          ∃ c ∈ k₀, c ≠ 0 ∧ val (r ^ i) = val c ^ 2 := by
        intro r i hri hr
        by_cases hi : i = 0
        · exact ⟨1, k₀.one_mem, one_ne_zero, by rw [hi, pow_zero, map_one, one_pow]⟩
        · obtain ⟨c, hcc, hc0, hvc⟩ := hr fun h ↦ hri (by rw [h, zero_pow hi])
          refine ⟨c ^ i, pow_mem ?_ i, pow_ne_zero i hc0, ?_⟩
          · rcases hcc with rfl | rfl | rfl
            · exact k₀.one_mem
            · exact hy'k
            · exact k₀.div_mem hy'k hxk
          · rw [map_pow, hvc, map_pow, ← pow_mul, ← pow_mul, mul_comm]
      have d21 : val (e₂' - e₁') = 1 := by rw [Valuation.map_sub_swap]; exact d12
      have d31 : val (e₃' - e₁') = 1 := by rw [Valuation.map_sub_swap]; exact d13
      have d32 : val (e₃' - e₂') = 1 := by rw [Valuation.map_sub_swap]; exact d23
      obtain ⟨c₁, hc₁, hc₁0, hv₁⟩ := hrad _ i₁ hp₁ fun h ↦
        val_radicand val hr₁ hr₂ hr₃ d12 d13 hy'2 h
      obtain ⟨c₂, hc₂, hc₂0, hv₂⟩ := hrad _ i₂ hp₂ fun h ↦
        val_radicand val hr₂ hr₁ hr₃ d21 d23 (hy'2.trans (by ring)) h
      obtain ⟨c₃, hc₃, hc₃0, hv₃⟩ := hrad _ i₃ hp₃ fun h ↦
        val_radicand val hr₃ hr₁ hr₂ d31 d32 (hy'2.trans (by ring)) h
      refine ⟨c * c₁ * c₂ * c₃, k₀.mul_mem (k₀.mul_mem (k₀.mul_mem hc hc₁) hc₂) hc₃,
        mul_ne_zero (mul_ne_zero (mul_ne_zero hc0 hc₁0) hc₂0) hc₃0, ?_⟩
      rw [hexp, map_mul, map_mul, map_mul, hv₁, hv₂, hv₃, map_pow, map_mul, map_mul, map_mul]
      simp only [mul_pow]
  obtain ⟨c, hc, hc0, hvc⟩ := main
  obtain ⟨b, hb0, hb⟩ := exists_global_same_valuation v A hA j F hc hc0
  refine two_dvd_valuation_of_sq w u hint hlt (Units.mk0 a ha0) (Units.mk0 b hb0) ?_
  change val (j (a : C K)) = val (j (b : C K)) ^ 2
  rw [hvc, hb]

/- ### Finiteness -/

/-- All two-torsion valued locally trivial cocycles vanish on the absolute Galois group of a
single finite extension: the two-division field with the square roots of representatives of
the finite Selmer group `F(S, 2)` adjoined. -/
theorem exists_common_splitting_field (E : Affine K) [E.IsElliptic] :
    ∃ N : IntermediateField K (C K), FiniteDimensional K N ∧
      ∀ d : locallyTrivialCocycles E, (∀ σ, 2 • d.val σ = 0) →
        ∀ σ ∈ N.fixingSubgroup, d.val σ = 0 := by
  have h2 : (2 : C K) ≠ 0 := two_ne_zero_of_algebra K
  obtain ⟨e₁, e₂, e₃, he⟩ := exists_twoDivRoots E (A := C K) h2
  have hΔ : (E⁄(C K)).Δ ≠ 0 := by
    rw [bc_Δ]
    exact (map_ne_zero _).mpr E.isUnit_Δ.ne_zero
  have h12 : e₁ ≠ e₂ := by
    rintro rfl
    apply hΔ
    rw [he.Δ_eq]
    ring
  have hnormal : Normal K (divField e₁ e₂ e₃) := divField_normal he
  have hgal : IsGalois K (divField e₁ e₂ e₃) := IsGalois.mk
  let S : Set (HeightOneSpectrum (𝓞 (divField e₁ e₂ e₃))) :=
    {w | ¬ GoodPrime E (divField e₁ e₂ e₃) w}
  have hS : S.Finite := finite_not_goodPrime E (divField e₁ e₂ e₃)
  let Sel := selmerGroup (R := 𝓞 (divField e₁ e₂ e₃)) (K := divField e₁ e₂ e₃) (S := S) (n := 2)
  have hfin : Finite Sel := finite_selmerGroup_of_numberField (divField e₁ e₂ e₃) S 2 hS
  let rep : Sel → (divField e₁ e₂ e₃)ˣ := fun m ↦ Quotient.out m.val
  have hrep : ∀ m : Sel, (QuotientGroup.mk (rep m) :
      (divField e₁ e₂ e₃)ˣ ⧸ (powMonoidHom 2 : (divField e₁ e₂ e₃)ˣ →* _).range) = m.val :=
    fun m ↦ QuotientGroup.out_eq' _
  have hroot : ∀ m : Sel, ∃ r : C K, r ^ 2 = (((rep m : (divField e₁ e₂ e₃)ˣ) :
      divField e₁ e₂ e₃) : C K) := fun m ↦ IsAlgClosed.exists_pow_nat_eq _ two_pos
  choose r hr using hroot
  have hfinr : FiniteDimensional K (IntermediateField.adjoin K (Set.range r)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x
  refine ⟨divField e₁ e₂ e₃ ⊔ IntermediateField.adjoin K (Set.range r), inferInstance,
    fun d hd σ hσ ↦ ?_⟩
  by_contra hne
  have hσF : σ ∈ (divField e₁ e₂ e₃).fixingSubgroup :=
    IntermediateField.fixingSubgroup_antitone le_sup_left hσ
  obtain ⟨s, hs0, hs2, hσs, hfix⟩ := exists_descent_radical he h12 d hd σ hσF hne
  let a : divField e₁ e₂ e₃ := ⟨s ^ 2, hs2⟩
  have ha0 : a ≠ 0 := fun h ↦ hs0 (pow_eq_zero_iff two_ne_zero |>.mp (congrArg Subtype.val h))
  have hmem : (QuotientGroup.mk (Units.mk0 a ha0) :
      (divField e₁ e₂ e₃)ˣ ⧸ (powMonoidHom 2 : (divField e₁ e₂ e₃)ˣ →* _).range) ∈ Sel := by
    refine fun w hw ↦ ?_
    rw [HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff]
    exact_mod_cast radical_even he (divField e₁ e₂ e₃) mem_divField₁ mem_divField₂ mem_divField₃
      d hd a rfl ha0 hfix w (not_not.mp hw)
  have heq := hrep ⟨_, hmem⟩
  rw [QuotientGroup.eq] at heq
  obtain ⟨q, hq⟩ := heq
  set m : Sel := ⟨_, hmem⟩ with hm
  have hq' : ((q : divField e₁ e₂ e₃) : C K) ^ 2 * (((rep m : (divField e₁ e₂ e₃)ˣ) :
      divField e₁ e₂ e₃) : C K) = s ^ 2 := by
    have h1 := congrArg (fun t : (divField e₁ e₂ e₃)ˣ ↦ ((t : divField e₁ e₂ e₃) : C K)) hq
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_mk0, IntermediateField.coe_pow, IntermediateField.coe_mul,
      IntermediateField.coe_inv] at h1
    have hne' : (((rep m : (divField e₁ e₂ e₃)ˣ) : divField e₁ e₂ e₃) : C K) ≠ 0 :=
      fun h ↦ Units.ne_zero (rep m) (Subtype.ext h)
    rw [h1]
    field_simp
    rfl
  have hsN : s ∈ divField e₁ e₂ e₃ ⊔ IntermediateField.adjoin K (Set.range r) := by
    have hrN : r m ∈ divField e₁ e₂ e₃ ⊔ IntermediateField.adjoin K (Set.range r) :=
      (le_sup_right : _ ≤ divField e₁ e₂ e₃ ⊔ _) (IntermediateField.subset_adjoin K _ ⟨m, rfl⟩)
    have hqN : ((q : divField e₁ e₂ e₃) : C K) ∈
        divField e₁ e₂ e₃ ⊔ IntermediateField.adjoin K (Set.range r) :=
      (le_sup_left : divField e₁ e₂ e₃ ≤ _) (q : divField e₁ e₂ e₃).property
    have hsq : s ^ 2 = (((q : divField e₁ e₂ e₃) : C K) * r m) ^ 2 := by
      rw [mul_pow, hr m, hq']
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with h | h
    · rw [h]
      exact mul_mem hqN hrN
    · rw [h]
      exact neg_mem (mul_mem hqN hrN)
  have hfixs : σ s = s := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ s hsN
  rw [hσs] at hfixs
  apply hs0
  have h2s : 2 * s = 0 := by linear_combination -hfixs
  exact (mul_eq_zero.mp h2s).resolve_left h2

end

end BSDResearch

end
/- ===== end BSD/ShaTwoDescentFinite.lean ===== -/

/- ===== begin DegreeOne.lean (local BSD library) ===== -/
section

/-
# Degree-one continuous cohomology in terms of inhomogeneous cocycles

Mathlib's `continuousCohomology 1 X` is the homology of the complex of homogeneous cochains
in `TopModuleCat`. This file unwinds it: every class is represented by a cycle `z`, and
`inhom X z : G → X`, `σ ↦ F(1)(σ)` is a continuous crossed homomorphism; the class of `z`
vanishes exactly when `inhom X z` is a principal crossed homomorphism `σ ↦ σ a - a`.
Restriction along a continuous group homomorphism is precomposition.
-/

open CategoryTheory Limits

namespace BSDResearch.ShaBridge

universe u v w

section Complex

variable {k : Type u} [Ring k] [TopologicalSpace k]
  (K : CochainComplex (TopModuleCat.{w} k) ℕ) (i : ℕ)

theorem iCycles_injective : Function.Injective (K.iCycles i) := by
  let e := IsLimit.conePointUniqueUpToIso (K.cyclesIsKernel i (i + 1) (by simp))
    (TopModuleCat.isLimitKer (K.d i (i + 1)))
  have he : CategoryStruct.comp e.hom (TopModuleCat.kerι (K.d i (i + 1))) = K.iCycles i :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero
  intro a b h
  have key (a) : (e.hom a).1 = K.iCycles i a :=
    (TopModuleCat.kerι_apply _ _).symm.trans
      ((ConcreteCategory.comp_apply _ _ _).symm.trans (ConcreteCategory.congr_hom he a))
  have h1 : e.hom a = e.hom b := Subtype.ext ((key a).trans (h.trans (key b).symm))
  calc a = e.inv (e.hom a) := by
        rw [← ConcreteCategory.comp_apply, e.hom_inv_id, ConcreteCategory.id_apply]
    _ = e.inv (e.hom b) := by rw [h1]
    _ = b := by rw [← ConcreteCategory.comp_apply, e.hom_inv_id, ConcreteCategory.id_apply]

theorem d_iCycles (z : K.cycles i) : K.d i (i + 1) (K.iCycles i z) = 0 :=
  ConcreteCategory.congr_hom (K.iCycles_d i (i + 1)) z

theorem iCycles_toCycles (b : K.X i) :
    K.iCycles (i + 1) (K.toCycles i (i + 1) b) = K.d i (i + 1) b :=
  ConcreteCategory.congr_hom (K.toCycles_i i (i + 1)) b

theorem homologyπ_toCycles (b : K.X i) : K.homologyπ (i + 1) (K.toCycles i (i + 1) b) = 0 :=
  ConcreteCategory.congr_hom (K.toCycles_comp_homologyπ i (i + 1)) b

section

variable (e' : K.homology (i + 1) ≅ TopModuleCat.coker (K.toCycles i (i + 1)))
  (he' : CategoryStruct.comp (K.homologyπ (i + 1)) e'.hom =
    TopModuleCat.cokerπ (K.toCycles i (i + 1)))

include he' in
private theorem surj_aux : Function.Surjective (K.homologyπ (i + 1)) := by
  intro x
  obtain ⟨z, hz⟩ := TopModuleCat.cokerπ_surjective (K.toCycles i (i + 1)) (e'.hom x)
  refine ⟨z, ?_⟩
  have h1 : e'.hom (K.homologyπ (i + 1) z) = e'.hom x := (ConcreteCategory.congr_hom he' z).trans hz
  calc K.homologyπ (i + 1) z = e'.inv (e'.hom (K.homologyπ (i + 1) z)) := by
        rw [← ConcreteCategory.comp_apply e'.hom, e'.hom_inv_id, ConcreteCategory.id_apply]
    _ = e'.inv (e'.hom x) := by rw [h1]
    _ = x := by rw [← ConcreteCategory.comp_apply, e'.hom_inv_id, ConcreteCategory.id_apply]

include he' in
private theorem zero_aux (z : K.cycles (i + 1)) (h : K.homologyπ (i + 1) z = 0) :
    ∃ b : K.X i, K.toCycles i (i + 1) b = z := by
  have h1 : (K.toCycles i (i + 1)).hom.range.mkQ z = e'.hom (K.homologyπ (i + 1) z) :=
    (ConcreteCategory.congr_hom he' z).symm
  rw [h, map_zero] at h1
  have h2 : z ∈ (K.toCycles i (i + 1)).hom.range := (Submodule.Quotient.mk_eq_zero _).mp h1
  exact h2

end

private noncomputable def cokerIso :
    K.homology (i + 1) ≅ TopModuleCat.coker (K.toCycles i (i + 1)) :=
  IsColimit.coconePointUniqueUpToIso (K.homologyIsCokernel i (i + 1) (by simp))
    (TopModuleCat.isColimitCoker (K.toCycles i (i + 1)))

private theorem cokerIso_spec :
    CategoryStruct.comp (K.homologyπ (i + 1)) (cokerIso K i).hom =
      TopModuleCat.cokerπ (K.toCycles i (i + 1)) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (K.homologyIsCokernel i (i + 1) (by simp))
    (TopModuleCat.isColimitCoker (K.toCycles i (i + 1))) WalkingParallelPair.one

theorem homologyπ_surjective : Function.Surjective (K.homologyπ (i + 1)) :=
  surj_aux K i _ (cokerIso_spec K i)

theorem exists_toCycles_of_homologyπ_eq_zero (z : K.cycles (i + 1))
    (h : K.homologyπ (i + 1) z = 0) : ∃ b : K.X i, K.toCycles i (i + 1) b = z :=
  zero_aux K i _ (cokerIso_spec K i) z h

end Complex

section Rep

open TopRep ContRepresentation ContinuousCohomology

variable {k : Type u} {G H : Type v} [Ring k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable (X : TopRep k G)

theorem inv₀ (b : (homogeneousCochains X).X 0) (g x : G) :
    X.ρ g (b.1 (g⁻¹ * x)) = b.1 x :=
  DFunLike.congr_fun (b.2 g) x

theorem inv₁ (s : (homogeneousCochains X).X 1) (g x y : G) :
    X.ρ g (s.1 (g⁻¹ * x) (g⁻¹ * y)) = s.1 x y :=
  DFunLike.congr_fun (DFunLike.congr_fun (s.2 g) x) y

theorem d₀_apply (b : (homogeneousCochains X).X 0) (x y : G) :
    (((homogeneousCochains X).d 0 1).hom b).1 x y = b.1 y - b.1 x := by
  rw [homogeneousCochains.d_apply]
  rfl

theorem d₁_apply (s : (homogeneousCochains X).X 1) (x y z : G) :
    (((homogeneousCochains X).d 1 2).hom s).1 x y z = s.1 y z - (s.1 x z - s.1 x y) := by
  rw [homogeneousCochains.d_apply]
  rfl

/-- The inhomogeneous cocycle `σ ↦ F(1)(σ)` attached to a degree-one cycle. -/
noncomputable def inhom (z : cocycles X 1) : G → X :=
  fun σ ↦ ((homogeneousCochains X).iCycles 1 z).1 1 σ

variable {X}

theorem continuous_inhom (z : cocycles X 1) : Continuous (inhom X z) :=
  (((homogeneousCochains X).iCycles 1 z).1 1).continuous

theorem cochain_eq (z : cocycles X 1) (x y : G) :
    ((homogeneousCochains X).iCycles 1 z).1 x y = inhom X z y - inhom X z x := by
  have h := d_iCycles (homogeneousCochains X) 1 z
  have h2 := d₁_apply X ((homogeneousCochains X).iCycles 1 z) 1 x y
  have h3 : (((homogeneousCochains X).d 1 2).hom ((homogeneousCochains X).iCycles 1 z)).1 1 x y
      = 0 := congrArg (fun t ↦ t.1 1 x y) h
  rw [h3] at h2
  show _ = ((homogeneousCochains X).iCycles 1 z).1 1 y - ((homogeneousCochains X).iCycles 1 z).1 1 x
  exact (sub_eq_zero.mp h2.symm)

/-- `inhom z` is a crossed homomorphism. -/
theorem inhom_mul (z : cocycles X 1) (σ τ : G) :
    inhom X z (σ * τ) = inhom X z σ + X.ρ σ (inhom X z τ) := by
  have h1 := cochain_eq z σ (σ * τ)
  have h2 := inv₁ X ((homogeneousCochains X).iCycles 1 z) σ σ (σ * τ)
  rw [inv_mul_cancel, inv_mul_cancel_left] at h2
  rw [h1] at h2
  show _ = _ + X.ρ σ (((homogeneousCochains X).iCycles 1 z).1 1 τ)
  rw [h2]
  abel

theorem inhom_sub (z z' : cocycles X 1) (σ : G) :
    inhom X (z - z') σ = inhom X z σ - inhom X z' σ := by
  show ((homogeneousCochains X).iCycles 1 (z - z')).1 1 σ = _
  rw [map_sub]
  rfl

theorem inhom_zero (σ : G) : inhom X (0 : cocycles X 1) σ = 0 := by
  show ((homogeneousCochains X).iCycles 1 0).1 1 σ = _
  rw [map_zero]
  rfl

theorem inhom_nsmul (n : ℕ) (z : cocycles X 1) (σ : G) :
    inhom X (n • z) σ = n • inhom X z σ := by
  show ((homogeneousCochains X).iCycles 1 (n • z)).1 1 σ = _
  rw [map_nsmul]
  rfl

/-- A cycle whose class vanishes has a principal inhomogeneous cocycle. -/
theorem inhom_of_π_eq_zero (z : cocycles X 1) (h : π X 1 z = 0) :
    ∃ a : X, ∀ σ, inhom X z σ = X.ρ σ a - a := by
  obtain ⟨b, hb⟩ := exists_toCycles_of_homologyπ_eq_zero (homogeneousCochains X) 0 z h
  refine ⟨b.1 1, fun σ ↦ ?_⟩
  have h1 : (homogeneousCochains X).iCycles 1 z = (homogeneousCochains X).d 0 1 b := by
    rw [← hb]
    exact iCycles_toCycles _ 0 b
  have h2 := inv₀ X b σ σ
  rw [inv_mul_cancel] at h2
  show ((homogeneousCochains X).iCycles 1 z).1 1 σ = _
  rw [h1, h2]
  exact d₀_apply X b 1 σ

/-- A cycle with principal inhomogeneous cocycle has vanishing class. The degree-zero cochain
`σ ↦ σ a` is continuous because it equals `inhom z + a`. -/
theorem π_eq_zero_of_inhom (z : cocycles X 1) (a : X) (h : ∀ σ, inhom X z σ = X.ρ σ a - a) :
    π X 1 z = 0 := by
  let f : C(G, X) := ((homogeneousCochains X).iCycles 1 z).1 1 + ContinuousMap.const G a
  have hf (σ : G) : f σ = X.ρ σ a := by
    show inhom X z σ + a = _
    rw [h σ]
    abel
  have hmem : f ∈ ((resolution' X).X 0).ρ.invariants := by
    intro g
    ext x
    show X.ρ g (f (g⁻¹ * x)) = f x
    have hm : X.ρ g (X.ρ (g⁻¹ * x) a) = X.ρ (g * (g⁻¹ * x)) a := by
      rw [map_mul X.ρ g (g⁻¹ * x)]; rfl
    rw [hf, hf, hm, mul_inv_cancel_left]
  let b : (homogeneousCochains X).X 0 := ⟨f, hmem⟩
  have hb : (homogeneousCochains X).toCycles 0 1 b = z := by
    apply iCycles_injective
    rw [iCycles_toCycles (homogeneousCochains X) 0 b]
    apply Subtype.ext
    ext x y
    rw [cochain_eq z x y, h, h]
    refine (d₀_apply X b x y).trans ?_
    show f y - f x = _
    rw [hf, hf]
    abel
  rw [← hb]
  exact homologyπ_toCycles _ 0 b

theorem π_one_surjective (X : TopRep k G) (x : continuousCohomology 1 X) :
    ∃ z : cocycles X 1, π X 1 z = x :=
  homologyπ_surjective (homogeneousCochains X) 0 x

variable (φ : H →ₜ* G)

theorem map_π (z : cocycles X 1) :
    ContinuousCohomology.map φ (𝟙 (res (φ : H →* G) X)) 1 (π X 1 z) =
      π (res (φ : H →* G) X) 1 (cocyclesMap φ (𝟙 (res (φ : H →* G) X)) 1 z) :=
  ConcreteCategory.congr_hom (π_map φ (𝟙 (res (φ : H →* G) X)) 1) z

/-- Restriction is precomposition on inhomogeneous cocycles. -/
theorem inhom_cocyclesMap (z : cocycles X 1) (τ : H) :
    inhom (res (φ : H →* G) X) (cocyclesMap φ (𝟙 (res (φ : H →* G) X)) 1 z) τ =
      inhom X z (φ τ) := by
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (cochainsMap φ (𝟙 (res (φ : H →* G) X))) 1) z
  show ((homogeneousCochains (res (φ : H →* G) X)).iCycles 1
    (cocyclesMap φ (𝟙 (res (φ : H →* G) X)) 1 z)).1 1 τ = _
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  rw [h]
  show ((homogeneousCochains X).iCycles 1 z).1 (φ 1) (φ τ) = _
  rw [map_one]
  rfl

/-- If the restriction of the class of `z` along `φ` vanishes, then `inhom z ∘ φ` is principal. -/
theorem inhom_of_map_eq_zero (z : cocycles X 1)
    (h : ContinuousCohomology.map φ (𝟙 (res (φ : H →* G) X)) 1 (π X 1 z) = 0) :
    ∃ a : X, ∀ τ : H, inhom X z (φ τ) = X.ρ (φ τ) a - a := by
  rw [map_π] at h
  obtain ⟨a, ha⟩ := inhom_of_π_eq_zero _ h
  exact ⟨a, fun τ ↦ (inhom_cocyclesMap φ z τ).symm.trans (ha τ)⟩

end Rep

end BSDResearch.ShaBridge

end
/- ===== end DegreeOne.lean ===== -/

/- ===== begin ShaBridge.lean (local BSD library) ===== -/
section

/-
# Injection of the registry Tate–Shafarevich group into the explicit cocycle quotient

`WeierstrassCurve.Affine.tateShafarevich` (registry, continuous cohomology) is mapped
injectively into `OMA.S_wp_birch_and_swinnerton_dyer_conjecture.sha` (explicit cocycles modulo
global coboundaries), compatibly with multiplication by natural numbers.
-/

open CategoryTheory WeierstrassCurve NumberField IsDedekindDomain ContinuousCohomology
open OMA.S_wp_birch_and_swinnerton_dyer_conjecture
open scoped Classical

namespace BSDResearch.ShaBridge

noncomputable section

/- ### Two embeddings of a normal algebraic extension differ by an automorphism -/

theorem exists_algEquiv_of_ringHom {K L M : Type*} [Field K] [Field L] [Field M] [Algebra K L]
    [Normal K L] (f g : L →+* M) (hfg : ∀ r : K, g (algebraMap K L r) = f (algebraMap K L r)) :
    ∃ ρ : L ≃ₐ[K] L, ∀ x, g x = f (ρ x) := by
  let _ : Algebra K M := (f.comp (algebraMap K L)).toAlgebra
  let f' : L →ₐ[K] M := { f with commutes' := fun _ ↦ rfl }
  let g' : L →ₐ[K] M := { g with commutes' := fun r ↦ hfg r }
  let e : L ≃ₐ[K] f'.fieldRange := AlgEquiv.ofInjectiveField f'
  have : Normal K f'.fieldRange := Normal.of_algEquiv e
  have hr : (g'.comp e.symm.toAlgHom).fieldRange = f'.fieldRange :=
    AlgHom.fieldRange_of_normal (E := f'.fieldRange) _
  have hmem (x : L) : g' x ∈ f'.range := by
    have h1 : g' x ∈ (g'.comp e.symm.toAlgHom).fieldRange := ⟨e x, by simp⟩
    rw [hr] at h1
    exact h1
  let ρ' : L →ₐ[K] L := e.symm.toAlgHom.comp
    ((g'.codRestrict f'.range hmem).comp (AlgHom.id K L))
  have hρ' (x : L) : f (ρ' x) = g x := by
    have h1 : e (ρ' x) = ⟨g' x, hmem x⟩ := e.apply_symm_apply ⟨g' x, hmem x⟩
    exact congrArg Subtype.val h1
  exact ⟨AlgEquiv.ofBijective ρ' (Algebra.IsAlgebraic.algHom_bijective ρ'), fun x ↦ (hρ' x).symm⟩

/- ### Conjugating a principal crossed homomorphism -/

theorem crossed_conj {G M : Type*} [Group G] [AddCommGroup M] (act : G → M →+ M)
    (hmul : ∀ a b m, act (a * b) m = act a (act b m)) (hone : ∀ m, act 1 m = m)
    (c : G → M) (hc : ∀ a b, c (a * b) = c a + act a (c b))
    (t r s : G) (hrs : t * r = r * s) (Q : M) (hQ : c t = act t Q - Q) :
    c s = act s (act r⁻¹ (Q + c r)) - act r⁻¹ (Q + c r) := by
  have hs : s = r⁻¹ * (t * r) := by rw [hrs, inv_mul_cancel_left]
  have h1 : c 1 = 0 := by
    have := hc 1 1
    rw [mul_one, hone] at this
    exact left_eq_add.mp this
  have hinv : c r⁻¹ = -act r⁻¹ (c r) := by
    have := hc r⁻¹ r
    rw [inv_mul_cancel, h1] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  have h2 : act s (act r⁻¹ (Q + c r)) = act r⁻¹ (act t (Q + c r)) := by
    rw [← hmul, ← hmul, hs, mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
  rw [h2, hs, hc, hc, hinv, hQ]
  simp only [map_add, map_sub]
  abel

/- ### The restriction map of absolute Galois groups -/

universe u

/-- `Field.absoluteGaloisGroup.map f` is restriction along some embedding of algebraic closures
extending `f`. -/
theorem absoluteGaloisGroup_map_spec {K V : Type u} [Field K] [Field V] (f : K →+* V) :
    ∃ g₀ : AlgebraicClosure K →+* AlgebraicClosure V,
      (∀ r : K, g₀ (algebraMap K (AlgebraicClosure K) r) =
        algebraMap V (AlgebraicClosure V) (f r)) ∧
      ∀ (τ : Field.absoluteGaloisGroup V) (x : AlgebraicClosure K),
        g₀ ((Field.absoluteGaloisGroup.map f τ).toAlgHom x) = τ.toAlgHom (g₀ x) := by
  let _ : Algebra K V := f.toAlgebra
  let g : AlgebraicClosure K →ₐ[K] AlgebraicClosure V := IsAlgClosed.lift
  let _ : Algebra (AlgebraicClosure K) (AlgebraicClosure V) := g.toAlgebra
  refine ⟨g, fun r ↦ g.commutes r, fun τ x ↦ ?_⟩
  exact AlgEquiv.restrictNormal_commutes (τ.restrictScalars K) (AlgebraicClosure K) x

variable {K : Type u} [Field K] (E : Affine K)

/-- Degree-one cycles of the registry Galois representation, with universes pinned to those of
`WeierstrassCurve.Affine.tateShafarevich`. -/
abbrev Z1 : Type u := ContinuousCohomology.cocycles.{0, u, u} (Affine.galoisRepresentation E) 1

/-- The projection from cycles to `H¹`. -/
abbrev cls (z : Z1 E) : continuousCohomology.{0, u, u} 1 (Affine.galoisRepresentation E) :=
  ContinuousCohomology.π.{0, u, u} (Affine.galoisRepresentation E) 1 z

/-- The explicit cocycle of a cycle. -/
abbrev coc (z : Z1 E) : Field.absoluteGaloisGroup K → Affine.Point (E⁄(AlgebraicClosure K)) :=
  inhom.{0, u, u} (Affine.galoisRepresentation E) z

theorem cls_sub (z z' : Z1 E) : cls E (z - z') = cls E z - cls E z' :=
  map_sub (ConcreteCategory.hom
    (ContinuousCohomology.π.{0, u, u} (Affine.galoisRepresentation E) 1)) z z'

theorem cls_zero : cls E 0 = 0 :=
  map_zero (ConcreteCategory.hom
    (ContinuousCohomology.π.{0, u, u} (Affine.galoisRepresentation E) 1))

theorem cls_nsmul (n : ℕ) (z : Z1 E) : cls E (n • z) = n • cls E z :=
  map_nsmul (ConcreteCategory.hom
    (ContinuousCohomology.π.{0, u, u} (Affine.galoisRepresentation E) 1)) n z

/-- **Easy direction of the local condition.** If the class of `z` restricts to zero in
`H¹(G_V, E(K̄))`, then `inhom z` is locally trivial at `V` in the sense of the explicit
statement: a witness among global algebraic points is pushed into the local geometric points,
for *every* embedding `j` of algebraic closures. -/
theorem locallyTrivial_of_restriction (z : Z1 E) (V : Type u) [Field V] [Algebra K V]
    (h : (ContinuousCohomology.map (Field.absoluteGaloisGroup.map (algebraMap K V))
      (𝟙 _) 1).hom (cls E z) = 0) :
    locallyTrivial E (coc E z) V := by
  intro j
  obtain ⟨(Q : Affine.Point (E⁄(AlgebraicClosure K))), hQ⟩ := inhom_of_map_eq_zero (Field.absoluteGaloisGroup.map (algebraMap K V)) z h
  obtain ⟨g₀, hg₀K, hg₀⟩ := absoluteGaloisGroup_map_spec (algebraMap K V)
  obtain ⟨ρ, hρ⟩ := exists_algEquiv_of_ringHom (K := K) g₀ j.toRingHom (fun r ↦ by
    rw [hg₀K]
    exact (j.commutes r).trans
      (IsScalarTower.algebraMap_apply K V (AlgebraicClosure V) r))
  let ρ' : Field.absoluteGaloisGroup K := ρ
  refine ⟨Affine.Point.map (W' := E) j
    (Affine.Point.map (W' := E) (ρ'⁻¹).toAlgHom (Q + coc E z ρ')), fun τ σ hτσ ↦ ?_⟩
  have hrs : Field.absoluteGaloisGroup.map (algebraMap K V) τ * ρ' = ρ' * σ := by
    apply AlgEquiv.ext
    intro x
    apply g₀.injective
    show g₀ ((Field.absoluteGaloisGroup.map (algebraMap K V) τ).toAlgHom (ρ x)) = g₀ (ρ (σ.toAlgHom x))
    rw [hg₀, ← hρ, ← hρ]
    exact hτσ x
  have key := crossed_conj (fun a : Field.absoluteGaloisGroup K ↦
      Affine.Point.map (W' := E) a.toAlgHom)
    (fun a b m ↦ (Affine.Point.map_map (W' := E) b.toAlgHom a.toAlgHom m).symm)
    (fun m ↦ Affine.Point.map_id' m)
    (coc E z) (fun a b ↦ inhom_mul z a b)
    (Field.absoluteGaloisGroup.map (algebraMap K V) τ) ρ' σ hrs Q (hQ τ)
  have hcomp : j.comp σ.toAlgHom = (τ.restrictScalars K).toAlgHom.comp j :=
    AlgHom.ext fun x ↦ (hτσ x).symm
  have e1 (R : Affine.Point (E⁄(AlgebraicClosure K))) :
      Affine.Point.map (W' := E) j (Affine.Point.map (W' := E) σ.toAlgHom R) =
        Affine.Point.map (W' := E) (τ.restrictScalars K).toAlgHom
          (Affine.Point.map (W' := E) j R) := by
    rw [Affine.Point.map_map, Affine.Point.map_map, hcomp]
  rw [key, map_sub, e1]

theorem sub_coboundary (z z' : Z1 E) (h : cls E z = cls E z') :
    ∃ P : Affine.Point (E⁄(AlgebraicClosure K)), ∀ σ : Field.absoluteGaloisGroup K,
      coc E z σ - coc E z' σ = Affine.Point.map (W' := E) σ.toAlgHom P - P := by
  have h0 : cls E (z - z') = 0 := by rw [cls_sub, h, sub_self]
  obtain ⟨a, ha⟩ := inhom_of_π_eq_zero _ h0
  exact ⟨a, fun σ ↦ (inhom_sub z z' σ).symm.trans (ha σ)⟩

theorem π_surjective (x : continuousCohomology.{0, u, u} 1 (Affine.galoisRepresentation E)) :
    ∃ z : Z1 E, cls E z = x :=
  π_one_surjective.{0, u, u} (Affine.galoisRepresentation E) x

variable [NumberField K]

/-- The explicit locally trivial cocycle of a cycle whose class is in the registry group. -/
def toCocycle (z : Z1 E) (hz : cls E z ∈ E.tateShafarevich) :
    locallyTrivialCocycles E := by
  refine ⟨coc E z, fun P ↦ ?_, fun σ τ ↦ inhom_mul z σ τ, fun v ↦ ?_, fun v ↦ ?_⟩
  · have : DiscreteTopology (Affine.galoisRepresentation E).V :=
      ⟨(Affine.galoisRepresentation E).hV3.ext_iff.mpr fun _ ↦ Iff.rfl⟩
    exact (continuous_inhom z).isOpen_preimage {P} (isOpen_discrete _)
  · exact locallyTrivial_of_restriction E z _ ((mem_tateShafarevich _ _ _ _).mp hz.1 v)
  · exact locallyTrivial_of_restriction E z _ ((mem_tateShafarevich _ _ _ _).mp hz.2 v)

/-- **The comparison map** from the registry Tate–Shafarevich group to the explicit quotient. -/
def shaMap (x : E.tateShafarevich) : sha E :=
  Quot.mk _ (toCocycle E (π_surjective E x.1).choose
    ((π_surjective E x.1).choose_spec.symm ▸ x.2))

theorem shaMap_mk (z : Z1 E) (hz : cls E z ∈ E.tateShafarevich) :
    shaMap E ⟨cls E z, hz⟩ = Quot.mk _ (toCocycle E z hz) :=
  Quot.sound (sub_coboundary E _ _ (π_surjective E (cls E z)).choose_spec)

/-- **Injectivity.** If two registry classes have explicit cocycles differing by a global
coboundary `σ P - P`, they are equal in continuous cohomology. -/
theorem shaMap_injective : Function.Injective (shaMap E) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  obtain ⟨z, rfl⟩ := π_surjective E x
  obtain ⟨z', rfl⟩ := π_surjective E y
  rw [shaMap_mk, shaMap_mk] at h
  obtain ⟨P, hP⟩ := (sha_eq_iff _ _).mp h
  apply Subtype.ext
  have h0 : cls E (z - z') = 0 :=
    π_eq_zero_of_inhom _ P (fun σ ↦ (inhom_sub z z' σ).trans (hP σ))
  rw [cls_sub] at h0
  exact sub_eq_zero.mp h0

theorem shaMap_zero : shaMap E 0 = shaZero E := by
  have h1 : (0 : E.tateShafarevich) =
      ⟨cls E 0, by rw [cls_zero]; exact zero_mem _⟩ := Subtype.ext (cls_zero E).symm
  rw [h1, shaMap_mk]
  exact congrArg (Quot.mk _) (Subtype.ext (funext fun σ ↦ inhom_zero σ))

theorem shaMap_nsmul (n : ℕ) (x : E.tateShafarevich) :
    shaMap E (n • x) = shaMultiple n (shaMap E x) := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨z, rfl⟩ := π_surjective E x
  have h1 : n • (⟨cls E z, hx⟩ : E.tateShafarevich) =
      ⟨cls E (n • z), by rw [cls_nsmul]; exact nsmul_mem hx n⟩ :=
    Subtype.ext (cls_nsmul E n z).symm
  rw [h1, shaMap_mk, shaMap_mk]
  exact congrArg (Quot.mk _) (Subtype.ext (funext fun σ ↦ inhom_nsmul n z σ))

end

end BSDResearch.ShaBridge

end
/- ===== end ShaBridge.lean ===== -/

/- ===== the end of the argument (written for this file) ===== -/
section

namespace BSDResearch

open WeierstrassCurve NumberField IsDedekindDomain
open OMA.S_wp_birch_and_swinnerton_dyer_conjecture
open TwoDescent
open scoped Classical

noncomputable section

/-- On a curve over an algebraically closed field of characteristic different from two whose
two-division polynomial has the three distinct roots `e₁ e₂ e₃`, every point is a double: take
square roots of the three `x - eᵢ`, fix the sign of one of them, and apply `exists_half`. -/
theorem exists_two_nsmul_eq {Ω : Type*} [Field Ω] [IsAlgClosed Ω] {W : Affine Ω} [W.IsElliptic]
    {e₁ e₂ e₃ : Ω} (he : TwoDivRoots W e₁ e₂ e₃) (h2 : (2 : Ω) ≠ 0) (h12 : e₁ ≠ e₂)
    (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃) (P : W.Point) : ∃ Q : W.Point, 2 • Q = P := by
  cases P with
  | zero => exact ⟨0, smul_zero 2⟩
  | some x y h =>
    obtain ⟨s₁, hs₁⟩ := IsAlgClosed.exists_pow_nat_eq (x - e₁) two_pos
    obtain ⟨s₂, hs₂⟩ := IsAlgClosed.exists_pow_nat_eq (x - e₂) two_pos
    obtain ⟨s₃, hs₃⟩ := IsAlgClosed.exists_pow_nat_eq (x - e₃) two_pos
    have heq := (he.equation_iff h2 x y).mp ((Affine.nonsingular_iff x y).mp h).1
    have hsq : (2 * y + W.a₁ * x + W.a₃) ^ 2 = (2 * (s₁ * s₂ * s₃)) ^ 2 := by
      rw [heq, ← hs₁, ← hs₂, ← hs₃]
      ring
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with hy | hy
    · obtain ⟨hQ, hQ2⟩ := exists_half he h2 h12 h13 h23 h hs₁ hs₂ hs₃ hy
      exact ⟨_, hQ2⟩
    · have hs₁' : (-s₁) ^ 2 = x - e₁ := by rw [neg_sq, hs₁]
      obtain ⟨hQ, hQ2⟩ := exists_half he h2 h12 h13 h23 h hs₁' hs₂ hs₃ (by rw [hy]; ring)
      exact ⟨_, hQ2⟩

/-- The points killed by two form a finite set: the origin and at most one point over each
root of the two-division polynomial. -/
theorem finite_two_torsion {Ω : Type*} [Field Ω] {W : Affine Ω} {e₁ e₂ e₃ : Ω}
    (he : TwoDivRoots W e₁ e₂ e₃) (h2 : (2 : Ω) ≠ 0) : {P : W.Point | 2 • P = 0}.Finite := by
  have hsub (e : Ω) : {P : W.Point | ∃ y h, P = Affine.Point.some e y h ∧
      2 * y + W.a₁ * e + W.a₃ = 0}.Subsingleton := by
    rintro _ ⟨y, h, rfl, hy⟩ _ ⟨y', h', rfl, hy'⟩
    exact two_torsion_eq_of_x h2 hy hy'
  refine ((Set.finite_singleton (0 : W.Point)).union (((hsub e₁).finite.union
    (hsub e₂).finite).union (hsub e₃).finite)).subset fun P hP ↦ ?_
  rcases two_torsion_cases he h2 P hP with rfl | ⟨x, y, h, rfl, hx | hx | hx, hy⟩
  · exact Or.inl rfl
  · subst hx
    exact Or.inr (Or.inl (Or.inl ⟨y, h, rfl, hy⟩))
  · subst hx
    exact Or.inr (Or.inl (Or.inr ⟨y, h, rfl, hy⟩))
  · subst hx
    exact Or.inr (Or.inr ⟨y, h, rfl, hy⟩)

variable {K : Type*} [Field K] [NumberField K]

/-- **The classes of the explicit cocycle quotient killed by two form a finite set**, for every
elliptic curve over every number field.

Every such class has a representative with values in `E[2]` (halve the coboundary witness).
By `exists_common_splitting_field` all these representatives vanish on the fixing subgroup `H`
of one finite extension, so the cocycle identity makes each of them constant on the cosets of
`H`: it is a function from the finite coset space to the finite set `E[2]`. -/
theorem finite_shaMultiple_two (E : Affine K) [E.IsElliptic] :
    Finite {a : sha E // shaMultiple 2 a = shaZero E} := by
  have h2 : (2 : AlgebraicClosure K) ≠ 0 := two_ne_zero_of_algebra K
  obtain ⟨e₁, e₂, e₃, he⟩ := exists_twoDivRoots E (A := AlgebraicClosure K) h2
  have hΔ : (E⁄(AlgebraicClosure K)).Δ ≠ 0 := by
    rw [bc_Δ]
    exact (map_ne_zero _).mpr E.isUnit_Δ.ne_zero
  have h12 : e₁ ≠ e₂ := by
    rintro rfl
    apply hΔ
    rw [he.Δ_eq]
    ring
  have h13 : e₁ ≠ e₃ := by
    rintro rfl
    apply hΔ
    rw [he.Δ_eq]
    ring
  have h23 : e₂ ≠ e₃ := by
    rintro rfl
    apply hΔ
    rw [he.Δ_eq]
    ring
  obtain ⟨N, hN, hvanish⟩ := exists_common_splitting_field E
  have hfinQ : Finite (Field.absoluteGaloisGroup K ⧸ N.fixingSubgroup) :=
    Nat.finite_of_card_ne_zero (by
      change N.fixingSubgroup.index ≠ 0
      rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
      exact Module.finrank_pos.ne')
  have hfinT : Finite {P : Affine.Point (E⁄(AlgebraicClosure K)) // 2 • P = 0} :=
    Set.finite_coe_iff.mpr (finite_two_torsion he h2)
  -- the representatives with values in `E[2]` are determined by their values on one
  -- representative of each coset
  have hfinD : Finite {d : locallyTrivialCocycles E // ∀ σ, 2 • d.val σ = 0} := by
    refine Finite.of_injective (β := Field.absoluteGaloisGroup K ⧸ N.fixingSubgroup →
        {P : Affine.Point (E⁄(AlgebraicClosure K)) // 2 • P = 0})
      (fun d q ↦ ⟨d.val.val q.out, d.property q.out⟩) fun d d' hdd ↦ ?_
    have key (d : {d : locallyTrivialCocycles E // ∀ σ, 2 • d.val σ = 0})
        (σ : Field.absoluteGaloisGroup K) :
        d.val.val (QuotientGroup.mk σ : Field.absoluteGaloisGroup K ⧸ N.fixingSubgroup).out =
          d.val.val σ := by
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul N.fixingSubgroup σ
      have h := d.val.property.2.1 σ k.val
      rw [hvanish d.val d.property k.val k.property, map_zero, add_zero] at h
      exact (congrArg d.val.val hk).trans h
    apply Subtype.ext
    apply Subtype.ext
    funext σ
    rw [← key d σ, ← key d' σ]
    exact congrArg Subtype.val (congrFun hdd (QuotientGroup.mk σ))
  refine Set.finite_coe_iff.mpr ((Set.finite_range fun d : {d : locallyTrivialCocycles E //
    ∀ σ, 2 • d.val σ = 0} ↦ (Quot.mk _ d.val : sha E)).subset fun a ha ↦ ?_)
  -- every class killed by two has such a representative
  change shaMultiple 2 a = shaZero E at ha
  revert ha
  refine Quot.inductionOn a fun c ha ↦ ?_
  obtain ⟨P, hP⟩ := (sha_eq_iff (multipleCocycle 2 c) (zeroCocycle E)).mp ha
  obtain ⟨Q, rfl⟩ := exists_two_nsmul_eq he h2 h12 h13 h23 P
  refine ⟨⟨shiftCocycle c Q, fun σ ↦ ?_⟩, (sha_eq_iff _ _).mpr ⟨-Q, fun σ ↦ ?_⟩⟩
  · change 2 • (c.val σ - (_ - Q)) = 0
    have hp : 2 • c.val σ = Affine.Point.map (W' := E) σ.toAlgHom (2 • Q) - 2 • Q := by
      simpa [multipleCocycle, zeroCocycle] using hP σ
    simp only [nsmul_sub, hp, map_nsmul, sub_self]
  · change c.val σ - (_ - Q) - c.val σ = _
    rw [map_neg]
    abel

end

namespace ShaBridge

universe u

variable {K : Type u} [Field K] [NumberField K] (E : Affine K)

/-- The comparison map sends registry classes killed by `n` to explicit classes killed by `n`. -/
theorem shaMultiple_shaMap_of_nsmul {n : ℕ} (x : E.tateShafarevich) (hx : n • x = 0) :
    shaMultiple n (shaMap E x) = shaZero E := by
  rw [← shaMap_nsmul, hx, shaMap_zero]

/-- The injection of `n`-torsion: registry `Ш(E)[n]` into the explicit cocycle quotient's `[n]`. -/
noncomputable def torsionMap (n : ℕ) (x : {x : E.tateShafarevich // n • x = 0}) :
    {a : sha E // shaMultiple n a = shaZero E} :=
  ⟨shaMap E x.1, shaMultiple_shaMap_of_nsmul E x.1 x.2⟩

theorem torsionMap_injective (n : ℕ) : Function.Injective (torsionMap E n) :=
  fun _ _ h ↦ Subtype.ext (shaMap_injective E (congrArg Subtype.val h))

/-- **Finiteness transfer.** If the classes of the explicit locally trivial cocycle quotient
killed by `n` form a finite set, so do the classes of the registry Tate-Shafarevich group killed
by `n`. No hypothesis on `E` (not even that it is elliptic). -/
theorem finite_registry_torsion_of_explicit (n : ℕ)
    (h : Finite {a : sha E // shaMultiple n a = shaZero E}) :
    Finite {x : E.tateShafarevich // n • x = 0} :=
  Finite.of_injective (torsionMap E n) (torsionMap_injective E n)

end ShaBridge

end BSDResearch

end

/-- **`Ш(E)[2]` is finite** for every elliptic curve `E` over `ℚ`, where `Ш(E)` is the registered
group `WeierstrassCurve.Affine.tateShafarevich`: step `H1` of the reduction
`WeierstrassCurve.Affine.Rat.weakBSD.R1.H2.R1`. -/
theorem OMA.solution : OMA.R_WeierstrassCurve_Affine_Rat_weakBSD_R1_H2_R1.H1 := by
  intro E _
  exact BSDResearch.ShaBridge.finite_registry_torsion_of_explicit E 2
    (BSDResearch.finite_shaMultiple_two E)
