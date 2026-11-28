import OMAReductions.R_KaplanskyUInvariant_u_invariant_values_variants_kaplansky_conjecture_R1

/-!
# Proof of `KaplanskyUInvariant.u_invariant_values.variants.kaplansky_conjecture.R1.H1`

We construct an explicit countable field of characteristic not `2` carrying a biquaternion division
algebra: take `K = RatFunc ℚ`, `F = RatFunc K`, and the biquaternion algebra
`QuaternionAlgebra F (-1) 0 (-1) ⊗[F] QuaternionAlgebra F (RatFunc.C RatFunc.X) 0 RatFunc.X`.

To prove it has no zero divisors, we apply a single elementary degree argument twice:
for any ring `D` with no zero divisors and injective ring endomorphism `σ : D →+* D`, the twisted
quadratic extension of `Polynomial D` with `v^2 = X` and `v * d = σ d * v` has no zero divisors
(comparing `natDegree` in the four parity cases of the leading term). Starting from
`D₀ = QuaternionAlgebra ℚ (-1) 0 (-1)` (which has no zero divisors via `normSq`), the first
application (with `σ = id`) shows `D₁ = Q(-1, -1)_K ⊗ K[u]/(u^2 - t)` has no zero divisors, and
the second application (with `σ(x + y u) = x - y u`) shows the full biquaternion algebra over
`F = K(s)` has no zero divisors.
-/

namespace OMA.Proof_Kaplansky_H1

noncomputable section

open Polynomial
open scoped TensorProduct

/- ### Generic degree lemma for twisted quadratic extensions of polynomial rings -/

private lemma coeff_mul_add_natDegree {D : Type*} [Ring D] [NoZeroDivisors D]
    {p q : Polynomial D} (_hp : p ≠ 0) (_hq : q ≠ 0) :
    (p * q).coeff (p.natDegree + q.natDegree) = p.leadingCoeff * q.leadingCoeff := by
  rw [Polynomial.coeff_mul]
  rw [Finset.sum_eq_single (p.natDegree, q.natDegree)]
  · rfl
  · intro x hx hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have hlt : p.natDegree < x.1 ∨ q.natDegree < x.2 := by
      by_contra h
      push Not at h
      apply hne
      ext <;> omega
    rcases hlt with h1 | h2
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h1, zero_mul]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h2, mul_zero]
  · intro hmem
    exact False.elim (hmem (Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl))

private lemma coeff_mul_eq_zero_of_lt {D : Type*} [Ring D]
    (p q : Polynomial D) {k : ℕ}
    (hk : p = 0 ∨ q = 0 ∨ p.natDegree + q.natDegree < k) :
    (p * q).coeff k = 0 := by
  rcases hk with rfl | rfl | hlt
  · simp
  · simp
  · rw [Polynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have h : p.natDegree < x.1 ∨ q.natDegree < x.2 := by omega
    rcases h with h1 | h2
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h1, zero_mul]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h2, mul_zero]

private lemma coeff_X_mul_eq_zero_of_lt {D : Type*} [Ring D]
    (p q : Polynomial D) {k : ℕ}
    (hk : k = 0 ∨ p = 0 ∨ q = 0 ∨ p.natDegree + q.natDegree + 1 < k) :
    (Polynomial.X * (p * q)).coeff k = 0 := by
  rcases hk with rfl | h
  · exact Polynomial.coeff_X_mul_zero _
  · rcases k with _ | k'
    · exact Polynomial.coeff_X_mul_zero _
    · rw [Polynomial.coeff_X_mul]
      apply coeff_mul_eq_zero_of_lt
      rcases h with hp | hq | hlt
      · exact Or.inl hp
      · exact Or.inr (Or.inl hq)
      · exact Or.inr (Or.inr (by omega))

private lemma skewPoly_mul_ne_zero {D : Type*} [Ring D] [NoZeroDivisors D]
    (σ : D →+* D) (hσ : Function.Injective σ)
    {x₁ y₁ x₂ y₂ : Polynomial D} (h1 : x₁ ≠ 0 ∨ y₁ ≠ 0) (h2 : x₂ ≠ 0 ∨ y₂ ≠ 0) :
    x₁ * x₂ + Polynomial.X * (y₁ * y₂.map σ) ≠ 0 ∨
      x₁ * y₂ + y₁ * x₂.map σ ≠ 0 := by
  have hmap_ne : ∀ p : Polynomial D, p ≠ 0 → p.map σ ≠ 0 := by
    intro p hp h0
    apply hp
    ext i
    apply hσ
    have := congrArg (fun r => r.coeff i) h0
    simpa [Polynomial.coeff_map] using this
  have hmap_deg : ∀ p : Polynomial D, (p.map σ).natDegree = p.natDegree :=
    fun p => Polynomial.natDegree_map_eq_of_injective hσ p
  have hmap_lc : ∀ p : Polynomial D, (p.map σ).leadingCoeff = σ p.leadingCoeff :=
    fun p => Polynomial.leadingCoeff_map_of_injective hσ p
  by_cases he1 : x₁ ≠ 0 ∧ (y₁ = 0 ∨ y₁.natDegree < x₁.natDegree)
  · by_cases he2 : x₂ ≠ 0 ∧ (y₂ = 0 ∨ y₂.natDegree < x₂.natDegree)
    · -- Even, Even
      left
      intro h0
      have hc := congrArg (fun r => r.coeff (x₁.natDegree + x₂.natDegree)) h0
      rw [Polynomial.coeff_add, Polynomial.coeff_zero,
        coeff_mul_add_natDegree he1.1 he2.1] at hc
      have hsec : (Polynomial.X * (y₁ * y₂.map σ)).coeff (x₁.natDegree + x₂.natDegree) = 0 := by
        apply coeff_X_mul_eq_zero_of_lt
        rcases he1.2 with hy1 | hlt1
        · exact Or.inr (Or.inl hy1)
        · rcases he2.2 with hy2 | hlt2
          · exact Or.inr (Or.inr (Or.inl (by simp [hy2])))
          · right; right; right
            rw [hmap_deg]
            omega
      rw [hsec, add_zero] at hc
      exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr he1.1)
        (Polynomial.leadingCoeff_ne_zero.mpr he2.1) hc
    · -- Even, Odd
      have ho2 : y₂ ≠ 0 ∧ (x₂ = 0 ∨ x₂.natDegree ≤ y₂.natDegree) := by
        rcases h2 with hx2 | hy2
        · by_cases hy2 : y₂ = 0
          · exact absurd ⟨hx2, Or.inl hy2⟩ he2
          · refine ⟨hy2, Or.inr ?_⟩
            by_contra hlt
            exact he2 ⟨hx2, Or.inr (by omega)⟩
        · by_cases hx2 : x₂ = 0
          · exact ⟨hy2, Or.inl hx2⟩
          · refine ⟨hy2, Or.inr ?_⟩
            by_contra hlt
            exact he2 ⟨hx2, Or.inr (by omega)⟩
      right
      intro h0
      have hc := congrArg (fun r => r.coeff (x₁.natDegree + y₂.natDegree)) h0
      rw [Polynomial.coeff_add, Polynomial.coeff_zero,
        coeff_mul_add_natDegree he1.1 ho2.1] at hc
      have hsec : (y₁ * x₂.map σ).coeff (x₁.natDegree + y₂.natDegree) = 0 := by
        apply coeff_mul_eq_zero_of_lt
        rcases he1.2 with hy1 | hlt1
        · exact Or.inl hy1
        · rcases ho2.2 with hx2 | hle2
          · exact Or.inr (Or.inl (by simp [hx2]))
          · right; right
            rw [hmap_deg]
            omega
      rw [hsec, add_zero] at hc
      exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr he1.1)
        (Polynomial.leadingCoeff_ne_zero.mpr ho2.1) hc
  · have ho1 : y₁ ≠ 0 ∧ (x₁ = 0 ∨ x₁.natDegree ≤ y₁.natDegree) := by
      rcases h1 with hx1 | hy1
      · by_cases hy1 : y₁ = 0
        · exact absurd ⟨hx1, Or.inl hy1⟩ he1
        · refine ⟨hy1, Or.inr ?_⟩
          by_contra hlt
          exact he1 ⟨hx1, Or.inr (by omega)⟩
      · by_cases hx1 : x₁ = 0
        · exact ⟨hy1, Or.inl hx1⟩
        · refine ⟨hy1, Or.inr ?_⟩
          by_contra hlt
          exact he1 ⟨hx1, Or.inr (by omega)⟩
    by_cases he2 : x₂ ≠ 0 ∧ (y₂ = 0 ∨ y₂.natDegree < x₂.natDegree)
    · -- Odd, Even
      right
      intro h0
      have hc := congrArg (fun r => r.coeff (y₁.natDegree + x₂.natDegree)) h0
      rw [Polynomial.coeff_add, Polynomial.coeff_zero] at hc
      have hfst : (x₁ * y₂).coeff (y₁.natDegree + x₂.natDegree) = 0 := by
        apply coeff_mul_eq_zero_of_lt
        rcases ho1.2 with hx1 | hle1
        · exact Or.inl hx1
        · rcases he2.2 with hy2 | hlt2
          · exact Or.inr (Or.inl hy2)
          · exact Or.inr (Or.inr (by omega))
      have hmx2 : x₂.map σ ≠ 0 := hmap_ne x₂ he2.1
      rw [hfst, zero_add, ← hmap_deg x₂, coeff_mul_add_natDegree ho1.1 hmx2] at hc
      exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr ho1.1)
        (Polynomial.leadingCoeff_ne_zero.mpr hmx2) hc
    · -- Odd, Odd
      have ho2 : y₂ ≠ 0 ∧ (x₂ = 0 ∨ x₂.natDegree ≤ y₂.natDegree) := by
        rcases h2 with hx2 | hy2
        · by_cases hy2 : y₂ = 0
          · exact absurd ⟨hx2, Or.inl hy2⟩ he2
          · refine ⟨hy2, Or.inr ?_⟩
            by_contra hlt
            exact he2 ⟨hx2, Or.inr (by omega)⟩
        · by_cases hx2 : x₂ = 0
          · exact ⟨hy2, Or.inl hx2⟩
          · refine ⟨hy2, Or.inr ?_⟩
            by_contra hlt
            exact he2 ⟨hx2, Or.inr (by omega)⟩
      left
      intro h0
      have hc := congrArg (fun r => r.coeff (y₁.natDegree + y₂.natDegree + 1)) h0
      rw [Polynomial.coeff_add, Polynomial.coeff_zero] at hc
      have hfst : (x₁ * x₂).coeff (y₁.natDegree + y₂.natDegree + 1) = 0 := by
        apply coeff_mul_eq_zero_of_lt
        rcases ho1.2 with hx1 | hle1
        · exact Or.inl hx1
        · rcases ho2.2 with hx2 | hle2
          · exact Or.inr (Or.inl hx2)
          · exact Or.inr (Or.inr (by omega))
      have hmy2 : y₂.map σ ≠ 0 := hmap_ne y₂ ho2.1
      rw [hfst, zero_add, Polynomial.coeff_X_mul, ← hmap_deg y₂,
        coeff_mul_add_natDegree ho1.1 hmy2] at hc
      exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr ho1.1)
        (Polynomial.leadingCoeff_ne_zero.mpr hmy2) hc

/- ### Additive coefficient map on polynomials -/

private def mapAdd {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+ B) (p : Polynomial A) : Polynomial B :=
  p.sum fun n a => Polynomial.monomial n (f a)

private lemma coeff_mapAdd {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+ B) (p : Polynomial A) (n : ℕ) :
    (mapAdd f p).coeff n = f (p.coeff n) := by
  classical
  unfold mapAdd Polynomial.sum
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq', Polynomial.mem_support_iff]
  split_ifs with h
  · rfl
  · push Not at h
    rw [h, map_zero]

private lemma mapAdd_add {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+ B) (p q : Polynomial A) :
    mapAdd f (p + q) = mapAdd f p + mapAdd f q := by
  ext n
  simp [coeff_mapAdd]

private lemma mapAdd_monomial {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+ B) (n : ℕ) (a : A) :
    mapAdd f (Polynomial.monomial n a) = Polynomial.monomial n (f a) := by
  ext k
  by_cases h : n = k
  · subst h; simp [coeff_mapAdd]
  · simp [coeff_mapAdd, Polynomial.coeff_monomial, h]

/- ### Common denominators and countability for `RatFunc` -/

private lemma exists_common_denom {R : Type*} [Field R] {ι : Type*} [Fintype ι]
    (v : ι → RatFunc R) :
    ∃ (d : Polynomial R) (p : ι → Polynomial R),
      d ≠ 0 ∧ ∀ i, algebraMap (Polynomial R) (RatFunc R) d * v i =
        algebraMap (Polynomial R) (RatFunc R) (p i) := by
  classical
  choose z hz using fun i => IsLocalization.surj (nonZeroDivisors (Polynomial R)) (v i)
  refine ⟨∏ i : ι, ((z i).2 : Polynomial R),
    fun i => (∏ j ∈ Finset.univ.erase i, ((z j).2 : Polynomial R)) * (z i).1, ?_, ?_⟩
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact nonZeroDivisors.ne_zero (z i).2.2
  · intro i
    have hsplit : (∏ j : ι, ((z j).2 : Polynomial R)) =
        (∏ j ∈ Finset.univ.erase i, ((z j).2 : Polynomial R)) * ((z i).2 : Polynomial R) := by
      rw [mul_comm]
      exact (Finset.mul_prod_erase Finset.univ (fun j : ι => ((z j).2 : Polynomial R))
        (Finset.mem_univ i)).symm
    rw [hsplit, map_mul, mul_assoc, mul_comm (algebraMap (Polynomial R) (RatFunc R) ((z i).2 : Polynomial R)),
      hz i, ← map_mul]

private lemma countable_polynomial {R : Type*} [Semiring R] [Countable R] :
    Countable (Polynomial R) := by
  classical
  refine Function.Injective.countable
    (f := fun p : Polynomial R => (⟨p.support, p.coeff, fun _ => Polynomial.mem_support_iff⟩ : ℕ →₀ R)) ?_
  intro p q h
  ext n
  exact congrArg (fun g : ℕ →₀ R => g n) h

private lemma countable_ratFunc {R : Type*} [Field R] [Countable R] :
    Countable (RatFunc R) := by
  have : Countable (Polynomial R) := countable_polynomial
  have hsurj : Function.Surjective (fun pair : Polynomial R × nonZeroDivisors (Polynomial R) =>
      IsLocalization.mk' (RatFunc R) pair.1 pair.2) := by
    intro x
    obtain ⟨⟨p, q⟩, h⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (Polynomial R)) x
    exact ⟨⟨p, q⟩, h⟩
  exact hsurj.countable

/- ### Layer 0: Hamilton quaternions over `ℚ` have no zero divisors -/

private abbrev Q₀ := QuaternionAlgebra ℚ (-1) 0 (-1)

private def normQ₀ (q : Q₀) : ℚ :=
  q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2

private lemma normQ₀_mul (x y : Q₀) : normQ₀ (x * y) = normQ₀ x * normQ₀ y := by
  dsimp only [normQ₀]
  simp
  ring

private lemma noZeroDivisors_Q₀ : NoZeroDivisors Q₀ := by
  refine ⟨fun {x y} hxy => ?_⟩
  have hnorm : ∀ q : Q₀, normQ₀ q = 0 → q = 0 := by
    intro q hq
    dsimp only [normQ₀] at hq
    have h1 : q.re = 0 := by nlinarith
    have h2 : q.imI = 0 := by nlinarith
    have h3 : q.imJ = 0 := by nlinarith
    have h4 : q.imK = 0 := by nlinarith
    ext <;> assumption
  have hmul : normQ₀ x * normQ₀ y = 0 := by
    rw [← normQ₀_mul, hxy]
    simp [normQ₀]
  rcases mul_eq_zero.mp hmul with hx | hy
  · exact Or.inl (hnorm x hx)
  · exact Or.inr (hnorm y hy)

/- ### Layer 1: `D₁ = Q(-1, -1)_K ⊗ K[u]/(u^2 - t)` over `K = RatFunc ℚ` -/

private abbrev K := RatFunc ℚ
private abbrev QK := QuaternionAlgebra K (-1) 0 (-1)

private structure D₁ where
  e : QK
  o : QK

private lemma D₁.ext {x y : D₁} (he : x.e = y.e) (ho : x.o = y.o) : x = y := by
  cases x; cases y; congr

private instance : Zero D₁ := ⟨⟨0, 0⟩⟩
private instance : One D₁ := ⟨⟨1, 0⟩⟩
private instance : Add D₁ := ⟨fun x y => ⟨x.e + y.e, x.o + y.o⟩⟩
private instance : Neg D₁ := ⟨fun x => ⟨-x.e, -x.o⟩⟩
private instance : Sub D₁ := ⟨fun x y => ⟨x.e - y.e, x.o - y.o⟩⟩
private instance : Mul D₁ :=
  ⟨fun x y => ⟨x.e * y.e + (RatFunc.X : K) • (x.o * y.o), x.e * y.o + x.o * y.e⟩⟩

private lemma D₁.zero_e : (0 : D₁).e = 0 := rfl
private lemma D₁.zero_o : (0 : D₁).o = 0 := rfl
private lemma D₁.one_e : (1 : D₁).e = 1 := rfl
private lemma D₁.one_o : (1 : D₁).o = 0 := rfl
private lemma D₁.add_e (x y : D₁) : (x + y).e = x.e + y.e := rfl
private lemma D₁.add_o (x y : D₁) : (x + y).o = x.o + y.o := rfl
private lemma D₁.neg_e (x : D₁) : (-x).e = -x.e := rfl
private lemma D₁.neg_o (x : D₁) : (-x).o = -x.o := rfl
private lemma D₁.sub_e (x y : D₁) : (x - y).e = x.e - y.e := rfl
private lemma D₁.sub_o (x y : D₁) : (x - y).o = x.o - y.o := rfl
private lemma D₁.mul_e (x y : D₁) :
    (x * y).e = x.e * y.e + (RatFunc.X : K) • (x.o * y.o) := rfl
private lemma D₁.mul_o (x y : D₁) : (x * y).o = x.e * y.o + x.o * y.e := rfl

private instance : Ring D₁ where
  add_assoc a b c := by apply D₁.ext <;> simp [D₁.add_e, D₁.add_o, add_assoc]
  zero_add a := by apply D₁.ext <;> simp [D₁.add_e, D₁.add_o, D₁.zero_e, D₁.zero_o]
  add_zero a := by apply D₁.ext <;> simp [D₁.add_e, D₁.add_o, D₁.zero_e, D₁.zero_o]
  nsmul := nsmulRec
  add_comm a b := by apply D₁.ext <;> simp [D₁.add_e, D₁.add_o, add_comm]
  zsmul := zsmulRec
  neg_add_cancel a := by apply D₁.ext <;> simp [D₁.add_e, D₁.add_o, D₁.neg_e, D₁.neg_o, D₁.zero_e, D₁.zero_o]
  sub_eq_add_neg a b := by apply D₁.ext <;> simp [D₁.sub_e, D₁.sub_o, D₁.add_e, D₁.add_o, D₁.neg_e, D₁.neg_o, sub_eq_add_neg]
  left_distrib a b c := by
    apply D₁.ext <;> simp [D₁.mul_e, D₁.mul_o, D₁.add_e, D₁.add_o, mul_add, smul_add] <;> abel
  right_distrib a b c := by
    apply D₁.ext <;> simp [D₁.mul_e, D₁.mul_o, D₁.add_e, D₁.add_o, add_mul, smul_add] <;> abel
  zero_mul a := by apply D₁.ext <;> simp [D₁.mul_e, D₁.mul_o, D₁.zero_e, D₁.zero_o]
  mul_zero a := by apply D₁.ext <;> simp [D₁.mul_e, D₁.mul_o, D₁.zero_e, D₁.zero_o]
  mul_assoc a b c := by
    apply D₁.ext
    · simp only [D₁.mul_e, D₁.mul_o, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
        smul_add, mul_assoc]
      abel
    · simp only [D₁.mul_e, D₁.mul_o, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
        mul_assoc]
      abel
  one_mul a := by apply D₁.ext <;> simp [D₁.mul_e, D₁.mul_o, D₁.one_e, D₁.one_o]
  mul_one a := by apply D₁.ext <;> simp [D₁.mul_e, D₁.mul_o, D₁.one_e, D₁.one_o]

private def σ₁ : D₁ →+* D₁ where
  toFun x := ⟨x.e, -x.o⟩
  map_one' := by apply D₁.ext <;> simp [D₁.one_e, D₁.one_o]
  map_mul' x y := by apply D₁.ext <;> simp [D₁.mul_e, D₁.mul_o]; abel
  map_zero' := by apply D₁.ext <;> simp [D₁.zero_e, D₁.zero_o]
  map_add' x y := by apply D₁.ext <;> simp [D₁.add_e, D₁.add_o]; abel

private lemma σ₁_apply (x : D₁) : σ₁ x = ⟨x.e, -x.o⟩ := rfl

private lemma σ₁_injective : Function.Injective σ₁ := by
  intro x y h
  rw [σ₁_apply, σ₁_apply] at h
  injection h with he ho
  exact D₁.ext he (neg_inj.mp ho)

private def liftQ₀ : Q₀ →+* QK where
  toFun q := ⟨RatFunc.C q.re, RatFunc.C q.imI, RatFunc.C q.imJ, RatFunc.C q.imK⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

private def evalQ₀ (p : Polynomial Q₀) : QK :=
  p.eval₂ liftQ₀ (algebraMap K QK (RatFunc.X : K))

private lemma evalQ₀_zero : evalQ₀ 0 = 0 := by
  unfold evalQ₀
  exact Polynomial.eval₂_zero _ _

private lemma evalQ₀_add (p q : Polynomial Q₀) : evalQ₀ (p + q) = evalQ₀ p + evalQ₀ q := by
  unfold evalQ₀
  exact Polynomial.eval₂_add _ _

private lemma evalQ₀_mul (p q : Polynomial Q₀) : evalQ₀ (p * q) = evalQ₀ p * evalQ₀ q := by
  unfold evalQ₀
  apply Polynomial.eval₂_mul_noncomm
  intro a
  exact (Algebra.commutes _ _).symm

private lemma evalQ₀_X_mul (p : Polynomial Q₀) :
    evalQ₀ (Polynomial.X * p) = (RatFunc.X : K) • evalQ₀ p := by
  rw [evalQ₀_mul]
  have hX : evalQ₀ Polynomial.X = algebraMap K QK (RatFunc.X : K) := by
    unfold evalQ₀
    exact Polynomial.eval₂_X _ _
  rw [hX, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

private def reQ₀ : Q₀ →+ ℚ := ⟨⟨QuaternionAlgebra.re, rfl⟩, fun _ _ => rfl⟩
private def imIQ₀ : Q₀ →+ ℚ := ⟨⟨QuaternionAlgebra.imI, rfl⟩, fun _ _ => rfl⟩
private def imJQ₀ : Q₀ →+ ℚ := ⟨⟨QuaternionAlgebra.imJ, rfl⟩, fun _ _ => rfl⟩
private def imKQ₀ : Q₀ →+ ℚ := ⟨⟨QuaternionAlgebra.imK, rfl⟩, fun _ _ => rfl⟩

private lemma evalQ₀_coords (p : Polynomial Q₀) :
    (evalQ₀ p).re = algebraMap (Polynomial ℚ) K (mapAdd reQ₀ p) ∧
    (evalQ₀ p).imI = algebraMap (Polynomial ℚ) K (mapAdd imIQ₀ p) ∧
    (evalQ₀ p).imJ = algebraMap (Polynomial ℚ) K (mapAdd imJQ₀ p) ∧
    (evalQ₀ p).imK = algebraMap (Polynomial ℚ) K (mapAdd imKQ₀ p) := by
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ ih₁ ih₂ =>
    simp only [evalQ₀_add, mapAdd_add, map_add]
    exact ⟨by change (evalQ₀ p₁).re + (evalQ₀ p₂).re = _; rw [ih₁.1, ih₂.1],
      by change (evalQ₀ p₁).imI + (evalQ₀ p₂).imI = _; rw [ih₁.2.1, ih₂.2.1],
      by change (evalQ₀ p₁).imJ + (evalQ₀ p₂).imJ = _; rw [ih₁.2.2.1, ih₂.2.2.1],
      by change (evalQ₀ p₁).imK + (evalQ₀ p₂).imK = _; rw [ih₁.2.2.2, ih₂.2.2.2]⟩
  | monomial n q =>
    have hm : evalQ₀ (Polynomial.monomial n q) =
        (algebraMap (Polynomial ℚ) K (Polynomial.X ^ n)) • liftQ₀ q := by
      unfold evalQ₀
      rw [Polynomial.eval₂_monomial, ← map_pow, Algebra.algebraMap_eq_smul_one,
        mul_smul_comm, mul_one]
      congr 1
      rw [map_pow]
      rfl
    rw [hm]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [liftQ₀, mapAdd_monomial, reQ₀, imIQ₀, imJQ₀, imKQ₀, mul_comm]

private lemma evalQ₀_injective : Function.Injective evalQ₀ := by
  intro p q h
  have hp := evalQ₀_coords p
  have hq := evalQ₀_coords q
  have hinj : Function.Injective (algebraMap (Polynomial ℚ) K) :=
    IsFractionRing.injective (Polynomial ℚ) K
  have h1 : mapAdd reQ₀ p = mapAdd reQ₀ q := hinj (by rw [← hp.1, ← hq.1, h])
  have h2 : mapAdd imIQ₀ p = mapAdd imIQ₀ q := hinj (by rw [← hp.2.1, ← hq.2.1, h])
  have h3 : mapAdd imJQ₀ p = mapAdd imJQ₀ q := hinj (by rw [← hp.2.2.1, ← hq.2.2.1, h])
  have h4 : mapAdd imKQ₀ p = mapAdd imKQ₀ q := hinj (by rw [← hp.2.2.2, ← hq.2.2.2, h])
  apply Polynomial.ext
  intro i
  have c1 := congrArg (fun r => r.coeff i) h1
  have c2 := congrArg (fun r => r.coeff i) h2
  have c3 := congrArg (fun r => r.coeff i) h3
  have c4 := congrArg (fun r => r.coeff i) h4
  simp only [coeff_mapAdd, reQ₀, imIQ₀, imJQ₀, imKQ₀, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at c1 c2 c3 c4
  ext <;> assumption

private def polyQ₀OfCoords (f : Fin 4 → Polynomial ℚ) : Polynomial Q₀ :=
  ∑ n ∈ Finset.univ.biUnion (fun i : Fin 4 => (f i).support),
    Polynomial.monomial n ⟨(f 0).coeff n, (f 1).coeff n, (f 2).coeff n, (f 3).coeff n⟩

private lemma coeff_polyQ₀OfCoords (f : Fin 4 → Polynomial ℚ) (n : ℕ) :
    (polyQ₀OfCoords f).coeff n = ⟨(f 0).coeff n, (f 1).coeff n, (f 2).coeff n, (f 3).coeff n⟩ := by
  classical
  unfold polyQ₀OfCoords
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_biUnion, Finset.mem_univ,
    true_and, Polynomial.mem_support_iff]
  split_ifs with h
  · rfl
  · push Not at h
    ext
    · exact (h 0).symm
    · exact (h 1).symm
    · exact (h 2).symm
    · exact (h 3).symm

private lemma evalQ₀_polyQ₀OfCoords (f : Fin 4 → Polynomial ℚ) :
    evalQ₀ (polyQ₀OfCoords f) =
      ⟨algebraMap (Polynomial ℚ) K (f 0), algebraMap (Polynomial ℚ) K (f 1),
       algebraMap (Polynomial ℚ) K (f 2), algebraMap (Polynomial ℚ) K (f 3)⟩ := by
  have hc := evalQ₀_coords (polyQ₀OfCoords f)
  have h0 : mapAdd reQ₀ (polyQ₀OfCoords f) = f 0 := by
    ext n; simp [coeff_mapAdd, coeff_polyQ₀OfCoords, reQ₀]
  have h1 : mapAdd imIQ₀ (polyQ₀OfCoords f) = f 1 := by
    ext n; simp [coeff_mapAdd, coeff_polyQ₀OfCoords, imIQ₀]
  have h2 : mapAdd imJQ₀ (polyQ₀OfCoords f) = f 2 := by
    ext n; simp [coeff_mapAdd, coeff_polyQ₀OfCoords, imJQ₀]
  have h3 : mapAdd imKQ₀ (polyQ₀OfCoords f) = f 3 := by
    ext n; simp [coeff_mapAdd, coeff_polyQ₀OfCoords, imKQ₀]
  ext
  · rw [hc.1, h0]
  · rw [hc.2.1, h1]
  · rw [hc.2.2.1, h2]
  · rw [hc.2.2.2, h3]

private lemma exists_poly_rep_D₁ (z : D₁) :
    ∃ (d : Polynomial ℚ) (p q : Polynomial Q₀),
      d ≠ 0 ∧
      ⟨algebraMap (Polynomial ℚ) K d • z.e, algebraMap (Polynomial ℚ) K d • z.o⟩ =
        (⟨evalQ₀ p, evalQ₀ q⟩ : D₁) := by
  let v : Fin 8 → K := ![z.e.re, z.e.imI, z.e.imJ, z.e.imK, z.o.re, z.o.imI, z.o.imJ, z.o.imK]
  obtain ⟨d, f, hd, hf⟩ := exists_common_denom v
  refine ⟨d, polyQ₀OfCoords (fun i : Fin 4 => f ⟨i.val, by omega⟩),
    polyQ₀OfCoords (fun i : Fin 4 => f ⟨i.val + 4, by omega⟩), hd, ?_⟩
  apply D₁.ext
  · dsimp only
    rw [evalQ₀_polyQ₀OfCoords]
    ext
    · exact hf 0
    · exact hf 1
    · exact hf 2
    · exact hf 3
  · dsimp only
    rw [evalQ₀_polyQ₀OfCoords]
    ext
    · exact hf 4
    · exact hf 5
    · exact hf 6
    · exact hf 7

private lemma noZeroDivisors_D₁ : NoZeroDivisors D₁ := by
  have : NoZeroDivisors Q₀ := noZeroDivisors_Q₀
  refine ⟨fun {z₁ z₂} hmul => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨d₁, p₁, q₁, hd₁, hrep₁⟩ := exists_poly_rep_D₁ z₁
  obtain ⟨d₂, p₂, q₂, hd₂, hrep₂⟩ := exists_poly_rep_D₁ z₂
  let k₁ : K := algebraMap (Polynomial ℚ) K d₁
  let k₂ : K := algebraMap (Polynomial ℚ) K d₂
  have hk₁ : k₁ ≠ 0 := by
    intro h0
    exact hd₁ (IsFractionRing.injective (Polynomial ℚ) K (by simpa [k₁] using h0))
  have hk₂ : k₂ ≠ 0 := by
    intro h0
    exact hd₂ (IsFractionRing.injective (Polynomial ℚ) K (by simpa [k₂] using h0))
  have hpq₁ : p₁ ≠ 0 ∨ q₁ ≠ 0 := by
    by_contra h
    push Not at h
    apply hne.1
    have he : k₁ • z₁.e = 0 := by
      have := congrArg D₁.e hrep₁
      simpa [k₁, h.1, evalQ₀] using this
    have ho : k₁ • z₁.o = 0 := by
      have := congrArg D₁.o hrep₁
      simpa [k₁, h.2, evalQ₀] using this
    exact D₁.ext ((smul_eq_zero.mp he).resolve_left hk₁) ((smul_eq_zero.mp ho).resolve_left hk₁)
  have hpq₂ : p₂ ≠ 0 ∨ q₂ ≠ 0 := by
    by_contra h
    push Not at h
    apply hne.2
    have he : k₂ • z₂.e = 0 := by
      have := congrArg D₁.e hrep₂
      simpa [k₂, h.1, evalQ₀] using this
    have ho : k₂ • z₂.o = 0 := by
      have := congrArg D₁.o hrep₂
      simpa [k₂, h.2, evalQ₀] using this
    exact D₁.ext ((smul_eq_zero.mp he).resolve_left hk₂) ((smul_eq_zero.mp ho).resolve_left hk₂)
  have hprod : (⟨evalQ₀ p₁, evalQ₀ q₁⟩ : D₁) * ⟨evalQ₀ p₂, evalQ₀ q₂⟩ = 0 := by
    rw [← hrep₁, ← hrep₂]
    have hme : (k₁ • z₁.e) * (k₂ • z₂.e) + (RatFunc.X : K) • ((k₁ • z₁.o) * (k₂ • z₂.o)) =
        (k₁ * k₂) • (z₁ * z₂).e := by
      simp only [D₁.mul_e, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
      rw [mul_comm k₂ k₁, mul_comm (RatFunc.X : K) (k₁ * k₂)]
    have hmo : (k₁ • z₁.e) * (k₂ • z₂.o) + (k₁ • z₁.o) * (k₂ • z₂.e) =
        (k₁ * k₂) • (z₁ * z₂).o := by
      simp only [D₁.mul_o, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
      rw [mul_comm k₂ k₁]
    apply D₁.ext
    · change (k₁ • z₁.e) * (k₂ • z₂.e) + (RatFunc.X : K) • ((k₁ • z₁.o) * (k₂ • z₂.o)) = 0
      rw [hme, hmul, D₁.zero_e, smul_zero]
    · change (k₁ • z₁.e) * (k₂ • z₂.o) + (k₁ • z₁.o) * (k₂ • z₂.e) = 0
      rw [hmo, hmul, D₁.zero_o, smul_zero]
  have he_zero : evalQ₀ (p₁ * p₂ + Polynomial.X * (q₁ * q₂)) = 0 := by
    rw [evalQ₀_add, evalQ₀_mul, evalQ₀_X_mul, evalQ₀_mul]
    exact congrArg D₁.e hprod
  have ho_zero : evalQ₀ (p₁ * q₂ + q₁ * p₂) = 0 := by
    rw [evalQ₀_add, evalQ₀_mul, evalQ₀_mul]
    exact congrArg D₁.o hprod
  have h1 := evalQ₀_injective (he_zero.trans evalQ₀_zero.symm)
  have h2 := evalQ₀_injective (ho_zero.trans evalQ₀_zero.symm)
  rcases skewPoly_mul_ne_zero (RingHom.id Q₀) Function.injective_id hpq₁ hpq₂ with ha | hb
  · exact ha (by simpa using h1)
  · exact hb (by simpa using h2)

/- ### Layer 2: Full biquaternion algebra over `F = RatFunc K` -/

private abbrev F := RatFunc K
private abbrev tF : F := RatFunc.C (RatFunc.X : K)
private abbrev sF : F := (RatFunc.X : F)
private abbrev Q₁F := QuaternionAlgebra F (-1) 0 (-1)
private abbrev Q₂F := QuaternionAlgebra F tF 0 sF
private abbrev Biquat := Q₁F ⊗[F] Q₂F

private def embedQK : QK →+* Q₁F where
  toFun q := ⟨RatFunc.C q.re, RatFunc.C q.imI, RatFunc.C q.imJ, RatFunc.C q.imK⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

private def i₂ : Q₂F := ⟨0, 1, 0, 0⟩
private def j₂ : Q₂F := ⟨0, 0, 1, 0⟩
private def k₂ : Q₂F := ⟨0, 0, 0, 1⟩

private lemma i₂_mul_i₂ : i₂ * i₂ = algebraMap F Q₂F tF := by
  ext <;> simp [i₂, QuaternionAlgebra.algebraMap_eq]

private lemma j₂_mul_j₂ : j₂ * j₂ = algebraMap F Q₂F sF := by
  ext <;> simp [j₂, QuaternionAlgebra.algebraMap_eq]

private lemma i₂_mul_j₂ : i₂ * j₂ = k₂ := by
  ext <;> simp [i₂, j₂, k₂]

private lemma j₂_mul_i₂ : j₂ * i₂ = -k₂ := by
  ext <;> simp [i₂, j₂, k₂]

private lemma embedQK_smul_X (q : QK) :
    embedQK ((RatFunc.X : K) • q) = tF • embedQK q := by
  ext <;> simp [embedQK, tF]

private def liftD₁ : D₁ →+* Biquat where
  toFun z := embedQK z.e ⊗ₜ[F] (1 : Q₂F) + embedQK z.o ⊗ₜ[F] i₂
  map_one' := by
    simp [D₁.one_e, D₁.one_o, TensorProduct.zero_tmul]
    rfl
  map_zero' := by
    simp [D₁.zero_e, D₁.zero_o, TensorProduct.zero_tmul]
  map_add' x y := by
    simp only [D₁.add_e, D₁.add_o, map_add, TensorProduct.add_tmul]
    abel
  map_mul' x y := by
    simp only [D₁.mul_e, D₁.mul_o, map_add, map_mul, embedQK_smul_X, add_mul, mul_add,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, i₂_mul_i₂,
      Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul,
      TensorProduct.add_tmul]
    abel

private lemma liftD₁_apply (z : D₁) :
    liftD₁ z = embedQK z.e ⊗ₜ[F] (1 : Q₂F) + embedQK z.o ⊗ₜ[F] i₂ := rfl

private def vB : Biquat := (1 : Q₁F) ⊗ₜ[F] j₂

private lemma vB_mul_vB : vB * vB = algebraMap F Biquat sF := by
  dsimp only [vB]
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, j₂_mul_j₂,
    Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul]
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

private lemma vB_mul_liftD₁ (z : D₁) : vB * liftD₁ z = liftD₁ (σ₁ z) * vB := by
  rw [liftD₁_apply, σ₁_apply, liftD₁_apply]
  dsimp only [vB]
  rw [mul_add, add_mul,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, one_mul, mul_one, mul_one, mul_one, one_mul,
    j₂_mul_i₂, i₂_mul_j₂, map_neg, TensorProduct.tmul_neg, TensorProduct.neg_tmul]

private def evalD₁ (p : Polynomial D₁) : Biquat :=
  p.eval₂ liftD₁ (algebraMap F Biquat sF)

private lemma evalD₁_add (p q : Polynomial D₁) : evalD₁ (p + q) = evalD₁ p + evalD₁ q := by
  unfold evalD₁
  exact Polynomial.eval₂_add _ _

private lemma evalD₁_mul (p q : Polynomial D₁) : evalD₁ (p * q) = evalD₁ p * evalD₁ q := by
  unfold evalD₁
  apply Polynomial.eval₂_mul_noncomm
  intro a
  exact (Algebra.commutes _ _).symm

private lemma evalD₁_X_mul (p : Polynomial D₁) :
    evalD₁ (Polynomial.X * p) = algebraMap F Biquat sF * evalD₁ p := by
  rw [evalD₁_mul]
  have hX : evalD₁ Polynomial.X = algebraMap F Biquat sF := by
    unfold evalD₁
    exact Polynomial.eval₂_X _ _
  rw [hX]

private lemma vB_mul_evalD₁ (p : Polynomial D₁) : vB * evalD₁ p = evalD₁ (p.map σ₁) * vB := by
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ ih₁ ih₂ =>
    rw [evalD₁_add, Polynomial.map_add, evalD₁_add, mul_add, add_mul, ih₁, ih₂]
  | monomial n z =>
    unfold evalD₁
    rw [Polynomial.map_monomial, Polynomial.eval₂_monomial, Polynomial.eval₂_monomial]
    calc vB * (liftD₁ z * algebraMap F Biquat sF ^ n)
        = (vB * liftD₁ z) * algebraMap F Biquat sF ^ n := (mul_assoc _ _ _).symm
      _ = (liftD₁ (σ₁ z) * vB) * algebraMap F Biquat sF ^ n := by rw [vB_mul_liftD₁]
      _ = liftD₁ (σ₁ z) * (vB * algebraMap F Biquat sF ^ n) := mul_assoc _ _ _
      _ = liftD₁ (σ₁ z) * (algebraMap F Biquat sF ^ n * vB) := by
          rw [← map_pow, Algebra.commutes]
      _ = (liftD₁ (σ₁ z) * algebraMap F Biquat sF ^ n) * vB := (mul_assoc _ _ _).symm

private noncomputable abbrev B16 :=
  (QuaternionAlgebra.basisOneIJK (-1 : F) 0 (-1)).tensorProduct
    (QuaternionAlgebra.basisOneIJK tF 0 sF)

private def coordQK : Fin 4 → QK →+ K
  | 0 => ⟨⟨QuaternionAlgebra.re, rfl⟩, fun _ _ => rfl⟩
  | 1 => ⟨⟨QuaternionAlgebra.imI, rfl⟩, fun _ _ => rfl⟩
  | 2 => ⟨⟨QuaternionAlgebra.imJ, rfl⟩, fun _ _ => rfl⟩
  | 3 => ⟨⟨QuaternionAlgebra.imK, rfl⟩, fun _ _ => rfl⟩

private def coordD₁ (i : Fin 4) (b : Bool) : D₁ →+ K :=
  if b then (coordQK i).comp ⟨⟨D₁.o, rfl⟩, fun _ _ => rfl⟩
  else (coordQK i).comp ⟨⟨D₁.e, rfl⟩, fun _ _ => rfl⟩

private lemma repr_evalD₁_add_mul_vB (p q : Polynomial D₁) (i j : Fin 4) :
    B16.repr (evalD₁ p + evalD₁ q * vB) (i, j) =
      match j with
      | 0 => algebraMap (Polynomial K) F (mapAdd (coordD₁ i false) p)
      | 1 => algebraMap (Polynomial K) F (mapAdd (coordD₁ i true) p)
      | 2 => algebraMap (Polynomial K) F (mapAdd (coordD₁ i false) q)
      | 3 => algebraMap (Polynomial K) F (mapAdd (coordD₁ i true) q) := by
  have hterm : ∀ (r : Polynomial D₁) (w : Q₂F),
      ∀ (cw : Fin 4 → F),
        (∀ j' : Fin 4, (QuaternionAlgebra.basisOneIJK tF 0 sF).repr w j' = cw j') →
        ∀ (w2 : Q₂F) (cw2 : Fin 4 → F),
          (∀ j' : Fin 4, (QuaternionAlgebra.basisOneIJK tF 0 sF).repr w2 j' = cw2 j') →
          (∀ z : D₁, liftD₁ z * ((1 : Q₁F) ⊗ₜ[F] w) =
            embedQK z.e ⊗ₜ[F] w + embedQK z.o ⊗ₜ[F] w2) →
          B16.repr (evalD₁ r * ((1 : Q₁F) ⊗ₜ[F] w)) (i, j) =
            algebraMap (Polynomial K) F (mapAdd (coordD₁ i false) r) * cw j +
            algebraMap (Polynomial K) F (mapAdd (coordD₁ i true) r) * cw2 j := by
    intro r w cw hcw w2 cw2 hcw2 hmulw
    induction r using Polynomial.induction_on' with
    | add r₁ r₂ ih₁ ih₂ =>
      simp only [evalD₁_add, add_mul, map_add, Finsupp.coe_add, Pi.add_apply, mapAdd_add,
        ih₁, ih₂]
      ring
    | monomial n z =>
      have hm : evalD₁ (Polynomial.monomial n z) * ((1 : Q₁F) ⊗ₜ[F] w) =
          (algebraMap (Polynomial K) F (Polynomial.X ^ n)) •
            (embedQK z.e ⊗ₜ[F] w + embedQK z.o ⊗ₜ[F] w2) := by
        unfold evalD₁
        rw [Polynomial.eval₂_monomial]
        have hs : (algebraMap F Biquat sF) ^ n =
            algebraMap F Biquat (algebraMap (Polynomial K) F (Polynomial.X ^ n)) := by
          rw [← map_pow]
          congr 1
          rw [map_pow, RatFunc.algebraMap_X]
        rw [hs, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc, hmulw]
      have hcoord : ∀ u : QK,
          (QuaternionAlgebra.basisOneIJK (-1 : F) 0 (-1)).repr (embedQK u) i =
            RatFunc.C (coordQK i u) := by
        intro u
        fin_cases i <;> simp [embedQK, coordQK, QuaternionAlgebra.coe_basisOneIJK_repr]
      have hX : ∀ c : K, algebraMap (Polynomial K) F (Polynomial.X ^ n) * RatFunc.C c =
          algebraMap (Polynomial K) F (Polynomial.monomial n c) := by
        intro c
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, mul_comm]
        rfl
      rw [hm, map_smul, map_add, Finsupp.coe_smul, Finsupp.coe_add, Pi.smul_apply, Pi.add_apply,
        smul_eq_mul]
      simp only [B16, Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul, hcoord, hcw, hcw2,
        mapAdd_monomial, coordD₁]
      simp only [Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply, AddMonoidHom.coe_mk,
        ZeroHom.coe_mk, mul_add]
      rw [← hX, ← hX]
      ring
  have hp := hterm p (1 : Q₂F) (fun j' => if j' = 0 then 1 else 0)
    (fun j' => by fin_cases j' <;> simp [QuaternionAlgebra.coe_basisOneIJK_repr])
    i₂ (fun j' => if j' = 1 then 1 else 0)
    (fun j' => by fin_cases j' <;> simp [i₂, QuaternionAlgebra.coe_basisOneIJK_repr])
    (fun z => by
      rw [liftD₁_apply, add_mul, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one, mul_one, mul_one])
  have hq := hterm q j₂ (fun j' => if j' = 2 then 1 else 0)
    (fun j' => by fin_cases j' <;> simp [j₂, QuaternionAlgebra.coe_basisOneIJK_repr])
    k₂ (fun j' => if j' = 3 then 1 else 0)
    (fun j' => by fin_cases j' <;> simp [k₂, QuaternionAlgebra.coe_basisOneIJK_repr])
    (fun z => by
      rw [liftD₁_apply, add_mul, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one, one_mul, i₂_mul_j₂])
  have h1 : evalD₁ p = evalD₁ p * ((1 : Q₁F) ⊗ₜ[F] (1 : Q₂F)) := (mul_one _).symm
  rw [map_add, Finsupp.coe_add, Pi.add_apply, h1, hp, show vB = (1 : Q₁F) ⊗ₜ[F] j₂ from rfl, hq]
  fin_cases j <;> simp

private lemma evalD₁_pair_injective {p q : Polynomial D₁}
    (h : evalD₁ p + evalD₁ q * vB = 0) : p = 0 ∧ q = 0 := by
  have hinj : Function.Injective (algebraMap (Polynomial K) F) :=
    IsFractionRing.injective (Polynomial K) F
  have hcoord : ∀ (i j : Fin 4), B16.repr (evalD₁ p + evalD₁ q * vB) (i, j) = 0 := fun i j => by
    rw [h, map_zero]; rfl
  have hp0 : ∀ (i : Fin 4) (n : ℕ), coordD₁ i false (p.coeff n) = 0 := by
    intro i n
    have h0 := hcoord i 0
    rw [repr_evalD₁_add_mul_vB] at h0
    have hmap : mapAdd (coordD₁ i false) p = 0 := hinj (by simpa using h0)
    have := congrArg (fun r => r.coeff n) hmap
    simpa [coeff_mapAdd] using this
  have hp1 : ∀ (i : Fin 4) (n : ℕ), coordD₁ i true (p.coeff n) = 0 := by
    intro i n
    have h0 := hcoord i 1
    rw [repr_evalD₁_add_mul_vB] at h0
    have hmap : mapAdd (coordD₁ i true) p = 0 := hinj (by simpa using h0)
    have := congrArg (fun r => r.coeff n) hmap
    simpa [coeff_mapAdd] using this
  have hq0 : ∀ (i : Fin 4) (n : ℕ), coordD₁ i false (q.coeff n) = 0 := by
    intro i n
    have h0 := hcoord i 2
    rw [repr_evalD₁_add_mul_vB] at h0
    have hmap : mapAdd (coordD₁ i false) q = 0 := hinj (by simpa using h0)
    have := congrArg (fun r => r.coeff n) hmap
    simpa [coeff_mapAdd] using this
  have hq1 : ∀ (i : Fin 4) (n : ℕ), coordD₁ i true (q.coeff n) = 0 := by
    intro i n
    have h0 := hcoord i 3
    rw [repr_evalD₁_add_mul_vB] at h0
    have hmap : mapAdd (coordD₁ i true) q = 0 := hinj (by simpa using h0)
    have := congrArg (fun r => r.coeff n) hmap
    simpa [coeff_mapAdd] using this
  constructor
  · ext n
    exact D₁.ext (by ext; exact hp0 0 n; exact hp0 1 n; exact hp0 2 n; exact hp0 3 n)
      (by ext; exact hp1 0 n; exact hp1 1 n; exact hp1 2 n; exact hp1 3 n)
  · ext n
    exact D₁.ext (by ext; exact hq0 0 n; exact hq0 1 n; exact hq0 2 n; exact hq0 3 n)
      (by ext; exact hq1 0 n; exact hq1 1 n; exact hq1 2 n; exact hq1 3 n)

private def polyD₁OfCoords (f : Fin 4 → Bool → Polynomial K) : Polynomial D₁ :=
  ∑ n ∈ Finset.univ.biUnion (fun p : Fin 4 × Bool => (f p.1 p.2).support),
    Polynomial.monomial n
      ⟨⟨(f 0 false).coeff n, (f 1 false).coeff n, (f 2 false).coeff n, (f 3 false).coeff n⟩,
       ⟨(f 0 true).coeff n, (f 1 true).coeff n, (f 2 true).coeff n, (f 3 true).coeff n⟩⟩

private lemma coeff_polyD₁OfCoords (f : Fin 4 → Bool → Polynomial K) (n : ℕ) :
    (polyD₁OfCoords f).coeff n =
      ⟨⟨(f 0 false).coeff n, (f 1 false).coeff n, (f 2 false).coeff n, (f 3 false).coeff n⟩,
       ⟨(f 0 true).coeff n, (f 1 true).coeff n, (f 2 true).coeff n, (f 3 true).coeff n⟩⟩ := by
  classical
  unfold polyD₁OfCoords
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_biUnion, Finset.mem_univ,
    true_and, Polynomial.mem_support_iff]
  split_ifs with h
  · rfl
  · push Not at h
    exact D₁.ext
      (by ext; exact (h (0, false)).symm; exact (h (1, false)).symm;
          exact (h (2, false)).symm; exact (h (3, false)).symm)
      (by ext; exact (h (0, true)).symm; exact (h (1, true)).symm;
          exact (h (2, true)).symm; exact (h (3, true)).symm)

private lemma exists_poly_rep_Biquat (x : Biquat) :
    ∃ (d : Polynomial K) (p q : Polynomial D₁),
      d ≠ 0 ∧ algebraMap (Polynomial K) F d • x = evalD₁ p + evalD₁ q * vB := by
  obtain ⟨d, f, hd, hf⟩ := exists_common_denom (fun ij : Fin 4 × Fin 4 => B16.repr x ij)
  let p := polyD₁OfCoords (fun i b => if b then f (i, 1) else f (i, 0))
  let q := polyD₁OfCoords (fun i b => if b then f (i, 3) else f (i, 2))
  refine ⟨d, p, q, hd, ?_⟩
  apply B16.repr.injective
  ext ⟨i, j⟩
  rw [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, hf (i, j), repr_evalD₁_add_mul_vB]
  fin_cases j
  · congr 1; ext n; fin_cases i <;> simp [p, coeff_polyD₁OfCoords, coeff_mapAdd, coordD₁, coordQK]
  · congr 1; ext n; fin_cases i <;> simp [p, coeff_polyD₁OfCoords, coeff_mapAdd, coordD₁, coordQK]
  · congr 1; ext n; fin_cases i <;> simp [q, coeff_polyD₁OfCoords, coeff_mapAdd, coordD₁, coordQK]
  · congr 1; ext n; fin_cases i <;> simp [q, coeff_polyD₁OfCoords, coeff_mapAdd, coordD₁, coordQK]

private lemma noZeroDivisors_Biquat : NoZeroDivisors Biquat := by
  have : NoZeroDivisors D₁ := noZeroDivisors_D₁
  refine ⟨fun {x y} hxy => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨dx, px, qx, hdx, hrepx⟩ := exists_poly_rep_Biquat x
  obtain ⟨dy, py, qy, hdy, hrepy⟩ := exists_poly_rep_Biquat y
  let fx : F := algebraMap (Polynomial K) F dx
  let fy : F := algebraMap (Polynomial K) F dy
  have hfx : fx ≠ 0 := fun h0 =>
    hdx (IsFractionRing.injective (Polynomial K) F (by simpa [fx] using h0))
  have hfy : fy ≠ 0 := fun h0 =>
    hdy (IsFractionRing.injective (Polynomial K) F (by simpa [fy] using h0))
  have hpqx : px ≠ 0 ∨ qx ≠ 0 := by
    by_contra h
    push Not at h
    apply hne.1
    have h0 : fx • x = 0 := by simpa [fx, h.1, h.2, evalD₁] using hrepx
    exact (smul_eq_zero.mp h0).resolve_left hfx
  have hpqy : py ≠ 0 ∨ qy ≠ 0 := by
    by_contra h
    push Not at h
    apply hne.2
    have h0 : fy • y = 0 := by simpa [fy, h.1, h.2, evalD₁] using hrepy
    exact (smul_eq_zero.mp h0).resolve_left hfy
  have hprod0 : (evalD₁ px + evalD₁ qx * vB) * (evalD₁ py + evalD₁ qy * vB) = 0 := by
    rw [← hrepx, ← hrepy, smul_mul_assoc, mul_smul_comm, hxy, smul_zero, smul_zero]
  have hmul_expand : (evalD₁ px + evalD₁ qx * vB) * (evalD₁ py + evalD₁ qy * vB) =
      evalD₁ (px * py + Polynomial.X * (qx * qy.map σ₁)) +
        evalD₁ (px * qy + qx * py.map σ₁) * vB := by
    rw [evalD₁_add, evalD₁_mul, evalD₁_X_mul, evalD₁_mul, evalD₁_add, evalD₁_mul, evalD₁_mul,
      add_mul, mul_add, mul_add, add_mul]
    have hterm1 : evalD₁ qx * vB * evalD₁ py = evalD₁ qx * evalD₁ (py.map σ₁) * vB := by
      rw [mul_assoc, vB_mul_evalD₁, ← mul_assoc]
    have hterm2 : evalD₁ qx * vB * (evalD₁ qy * vB) =
        algebraMap F Biquat sF * (evalD₁ qx * evalD₁ (qy.map σ₁)) := by
      calc evalD₁ qx * vB * (evalD₁ qy * vB)
          = evalD₁ qx * ((vB * evalD₁ qy) * vB) := by simp only [mul_assoc]
        _ = evalD₁ qx * (evalD₁ (qy.map σ₁) * (vB * vB)) := by
            rw [vB_mul_evalD₁, mul_assoc]
        _ = evalD₁ qx * (evalD₁ (qy.map σ₁) * algebraMap F Biquat sF) := by rw [vB_mul_vB]
        _ = algebraMap F Biquat sF * (evalD₁ qx * evalD₁ (qy.map σ₁)) := by
            rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, mul_smul_comm,
              smul_mul_assoc, one_mul]
    rw [hterm1, hterm2, ← mul_assoc (evalD₁ px) (evalD₁ qy) vB]
    abel
  rw [hmul_expand] at hprod0
  obtain ⟨h1, h2⟩ := evalD₁_pair_injective hprod0
  rcases skewPoly_mul_ne_zero σ₁ σ₁_injective hpqx hpqy with ha | hb
  · exact ha h1
  · exact hb h2

private lemma countable_F : Countable F := by
  have : Countable K := countable_ratFunc
  exact countable_ratFunc

end

end OMA.Proof_Kaplansky_H1

theorem OMA.solution :
    OMA.R_KaplanskyUInvariant_u_invariant_values_variants_kaplansky_conjecture_R1.H1 :=
  ⟨OMA.Proof_Kaplansky_H1.F, inferInstance, inferInstance, OMA.Proof_Kaplansky_H1.countable_F,
    -1, -1, OMA.Proof_Kaplansky_H1.tF, OMA.Proof_Kaplansky_H1.sF,
    OMA.Proof_Kaplansky_H1.noZeroDivisors_Biquat⟩
