import FormalConjectures.GreensOpenProblems.«28»
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic.Linarith

/-!
# A polynomial reduction for Green's Problem 28

Normalized generating polynomials turn convolution of the finite-support PMFs
into multiplication of monic nonnegative real polynomials. For the known
palindromic case, the proof only needs agreement with the reflected product
through the smaller factor degree. This is the Krasner–Ranulac argument with
just the necessary range of matching coefficients; see Ghidelli, arXiv:2209.09843.
The formal PMF connection is related to @koolkao's earlier MathOverflow 339137
equivalence, with explicit support extrema and their normalization here.
-/

open scoped Polynomial
open Polynomial

namespace GreenFactorBounds

theorem coeff_product_lower (P Q : ℝ[X]) (hP : ∀ i, 0 ≤ P.coeff i)
    (hQ : ∀ j, 0 ≤ Q.coeff j) (i j : ℕ) :
    P.coeff i * Q.coeff j ≤ (P*Q).coeff (i+j) := by
  rw [Polynomial.coeff_mul]
  have hmem : (i,j) ∈ Finset.HasAntidiagonal.antidiagonal (i+j) := Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl
  exact Finset.single_le_sum (f := fun ij : ℕ × ℕ => P.coeff ij.1 * Q.coeff ij.2)
    (fun ij _ => mul_nonneg (hP _) (hQ _)) hmem

theorem coeff_product_two_lower (P Q : ℝ[X]) (hP : ∀ i, 0 ≤ P.coeff i)
    (hQ : ∀ j, 0 ≤ Q.coeff j) {n : ℕ} (u v : ℕ × ℕ)
    (hu : u.1+u.2 = n) (hv : v.1+v.2 = n) (distinct : u ≠ v) :
    P.coeff u.1 * Q.coeff u.2 + P.coeff v.1 * Q.coeff v.2 ≤ (P*Q).coeff n := by
  classical
  have hsub : ({u,v} : Finset (ℕ×ℕ)) ⊆ Finset.HasAntidiagonal.antidiagonal n := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Finset.HasAntidiagonal.mem_antidiagonal.mpr hu
    · exact Finset.HasAntidiagonal.mem_antidiagonal.mpr hv
  let val (ij : ℕ×ℕ) := P.coeff ij.1 * Q.coeff ij.2
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := val)
    (fun ij _ _ => mul_nonneg (hP _) (hQ _))
  rw [Finset.sum_pair distinct] at h
  rwa [Polynomial.coeff_mul]

theorem factor_coeff_upper (P Q : ℝ[X]) (hP : ∀ i, 0 ≤ P.coeff i)
    (hQ : ∀ j, 0 ≤ Q.coeff j) (monicQ : Q.Monic)
    (hk : ∀ k, (P*Q).coeff k = 0 ∨ (P*Q).coeff k = 1) (i : ℕ) :
    P.coeff i ≤ 1 := by
  have first := coeff_product_lower P Q hP hQ i Q.natDegree
  rw [monicQ.coeff_natDegree, mul_one] at first
  rcases hk (i+Q.natDegree) with he | he <;> linarith

theorem constant_one (P Q : ℝ[X])
    (monicP : P.Monic) (monicQ : Q.Monic)
    (hP : ∀ i, 0 ≤ P.coeff i) (hQ : ∀ j, 0 ≤ Q.coeff j)
    (hk : ∀ k, (P*Q).coeff k = 0 ∨ (P*Q).coeff k = 1)
    (posProd : 0 < (P*Q).coeff 0) : P.coeff 0 = 1 ∧ Q.coeff 0 = 1 := by
  have first := factor_coeff_upper P Q hP hQ monicQ hk 0
  have second := factor_coeff_upper Q P hQ hP monicP (by simpa only [mul_comm Q P] using hk) 0
  have hprod : P.coeff 0 * Q.coeff 0 = 1 := by
    have hon : (P*Q).coeff 0 = 1 := (hk 0).resolve_left (ne_of_gt posProd)
    simpa [Polynomial.coeff_mul] using hon
  have left := mul_le_of_le_one_right (hP 0) second
  have right := mul_le_of_le_one_left (hQ 0) first
  exact ⟨by linarith,by linarith⟩

theorem degree_or_constant (P Q : ℝ[X]) (monicP : P.Monic) (monicQ : Q.Monic)
    (hP : ∀ i, 0 ≤ P.coeff i) (hQ : ∀ j, 0 ≤ Q.coeff j)
    (hk : ∀ k, (P*Q).coeff k = 0 ∨ (P*Q).coeff k = 1)
    (h0P : P.coeff 0 = 1) (h0Q : Q.coeff 0 = 1) :
    P = 1 ∨ Q = 1 ∨ P.natDegree ≠ Q.natDegree := by
  by_cases he : P.natDegree = Q.natDegree
  · let d := P.natDegree
    by_cases hz : d = 0
    · left
      exact Polynomial.eq_one_of_monic_natDegree_zero monicP hz
    · exfalso
      have hne : (0,d) ≠ (d,0) := fun h => hz (congrArg Prod.snd h)
      have cross := coeff_product_two_lower P Q hP hQ (0,d) (d,0)
        (Nat.zero_add d) (Nat.add_zero d) hne
      change P.coeff 0 * Q.coeff P.natDegree + P.coeff P.natDegree * Q.coeff 0 ≤ _ at cross
      have qtop : Q.coeff P.natDegree = 1 := he.symm ▸ monicQ.coeff_natDegree
      rw [qtop, monicP.coeff_natDegree, h0P, h0Q] at cross
      rcases hk d with eq | eq <;> linarith
  · exact Or.inr (Or.inr he)

theorem degree_le_one_binary (P : ℝ[X]) (monic : P.Monic)
    (h0 : P.coeff 0 = 1) (hs : P.natDegree ≤ 1) :
    ∀ i, P.coeff i = 0 ∨ P.coeff i = 1 := by
  intro i
  by_cases high : P.natDegree < i
  · exact Or.inl (Polynomial.coeff_eq_zero_of_natDegree_lt high)
  · have either : i = 0 ∨ i = P.natDegree := by omega
    rcases either with rfl | rfl
    · exact Or.inr h0
    · exact Or.inr monic.coeff_natDegree

theorem degree_two_binary (P Q : ℝ[X]) (monic : P.Monic)
    (hP : ∀ i, 0 ≤ P.coeff i) (hQ : ∀ j, 0 ≤ Q.coeff j)
    (h0 : P.coeff 0 = 1) (h0Q : Q.coeff 0 = 1) (hdeg : P.natDegree = 2)
    (hk : ∀ k, (P*Q).coeff k = 0 ∨ (P*Q).coeff k = 1) :
    ∀ i, P.coeff i = 0 ∨ P.coeff i = 1 := by
  have two : P.coeff 2 = 1 := hdeg ▸ monic.coeff_natDegree
  have oneConv : (P*Q).coeff 1 = P.coeff 1 + Q.coeff 1 := by
    rw [Polynomial.coeff_mul]
    have hset : Finset.HasAntidiagonal.antidiagonal 1 = {(0,1),(1,0)} := by decide
    rw [hset, Finset.sum_pair (by decide), h0, h0Q, one_mul, mul_one, add_comm]
  have cap := coeff_product_two_lower P Q hP hQ (n := 2) (2,0) (1,1) (by decide) (by decide) (by decide)
  change P.coeff 2 * Q.coeff 0 + P.coeff 1 * Q.coeff 1 ≤ (P*Q).coeff 2 at cap
  rw [two,h0Q,mul_one] at cap
  have zeroProd : P.coeff 1 * Q.coeff 1 = 0 := by
    have hbound : (P*Q).coeff 2 ≤ 1 := by rcases hk 2 with v | v <;> linarith
    exact le_antisymm (by linarith) (mul_nonneg (hP 1) (hQ 1))
  have one : P.coeff 1 = 0 ∨ P.coeff 1 = 1 := by
    rcases mul_eq_zero.mp zeroProd with hp | hq
    · exact Or.inl hp
    · simpa only [oneConv, hq, add_zero] using hk 1
  intro i
  by_cases hi : 2 < i
  · exact Or.inl (Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [hdeg]))
  · have vals : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases vals with rfl | rfl | rfl
    · exact Or.inr h0
    · exact one
    · exact Or.inr two

end GreenFactorBounds

namespace Green28PalindromicFactors

private theorem summand_le_coeff {P Q : ℝ[X]} {i j : ℕ}
    (hP : ∀ k, 0 ≤ P.coeff k) (hQ : ∀ k, 0 ≤ Q.coeff k) :
    P.coeff i * Q.coeff j ≤ (P * Q).coeff (i + j) := by
  rw [Polynomial.coeff_mul]
  have hij : (i, j) ∈ Finset.HasAntidiagonal.antidiagonal (i + j) := Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl
  exact Finset.single_le_sum (f := fun z : ℕ × ℕ => P.coeff z.1 * Q.coeff z.2)
    (fun z _ => mul_nonneg (hP z.1) (hQ z.2)) hij

/-- A summand already equal to 1 exhausts the coefficient budget. -/
private theorem zero_of_saturated_coeff {P Q : ℝ[X]} {i j s t k : ℕ}
    (hP : ∀ l, 0 ≤ P.coeff l) (hQ : ∀ l, 0 ≤ Q.coeff l)
    (hle : (P * Q).coeff k ≤ 1) (hij : i + j = k) (hst : s + t = k)
    (hne : (i, j) ≠ (s, t)) (hone : P.coeff s * Q.coeff t = 1) :
    P.coeff i * Q.coeff j = 0 := by
  let A := Finset.HasAntidiagonal.antidiagonal k
  let f := fun z : ℕ × ℕ => P.coeff z.1 * Q.coeff z.2
  have hOne : (s, t) ∈ A := Finset.HasAntidiagonal.mem_antidiagonal.mpr hst
  have hTerm : (i, j) ∈ A.erase (s, t) :=
    Finset.mem_erase.mpr ⟨hne, Finset.HasAntidiagonal.mem_antidiagonal.mpr hij⟩
  have hrest : (∑ z ∈ A.erase (s, t), f z) + 1 ≤ 1 := by
    have he := Finset.sum_erase_add A f hOne
    change (∑ z ∈ A.erase (s, t), f z) + P.coeff s * Q.coeff t = ∑ z ∈ A, f z at he
    rw [hone, ← Polynomial.coeff_mul] at he
    rwa [he]
  have hsmall : f (i, j) ≤ ∑ z ∈ A.erase (s, t), f z :=
    Finset.single_le_sum (fun z _ => mul_nonneg (hP z.1) (hQ z.2)) hTerm
  change P.coeff i * Q.coeff j ≤ _ at hsmall
  exact le_antisymm (by linarith) (mul_nonneg (hP i) (hQ j))

private theorem coeff_end_sum {P Q : ℝ[X]} {k : ℕ}
    (hk : 0 < k) (hP0 : P.coeff 0 = 1) (hQ0 : Q.coeff 0 = 1) :
    (P * Q).coeff k = P.coeff k + Q.coeff k +
      ∑ z ∈ ((Finset.HasAntidiagonal.antidiagonal k).erase (k, 0)).erase (0, k),
        P.coeff z.1 * Q.coeff z.2 := by
  let A := Finset.HasAntidiagonal.antidiagonal k
  let f := fun z : ℕ × ℕ => P.coeff z.1 * Q.coeff z.2
  have hK : (k, 0) ∈ A := Finset.HasAntidiagonal.mem_antidiagonal.mpr (Nat.add_zero k)
  have hZero : (0, k) ∈ A.erase (k, 0) := by
    refine Finset.mem_erase.mpr ⟨?_, Finset.HasAntidiagonal.mem_antidiagonal.mpr (Nat.zero_add k)⟩
    intro h
    exact hk.ne' (congrArg Prod.fst h).symm
  have hA := Finset.sum_erase_add A f hK
  have hB := Finset.sum_erase_add (A.erase (k, 0)) f hZero
  rw [Polynomial.coeff_mul]
  change (∑ z ∈ A, f z) = P.coeff k + Q.coeff k + ∑ z ∈ (A.erase (k, 0)).erase (0, k), f z
  rw [← hA, ← hB]
  simp only [f, hP0, hQ0, mul_one, one_mul]
  linarith

private theorem interior_lt {k i j : ℕ}
    (h : (i, j) ∈ ((Finset.HasAntidiagonal.antidiagonal k).erase (k, 0)).erase (0, k)) :
    i < k ∧ j < k := by
  obtain ⟨h0, h'⟩ := Finset.mem_erase.mp h
  obtain ⟨hk, hsum⟩ := Finset.mem_erase.mp h'
  have hij : i + j = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hsum
  constructor
  · by_contra! hge
    have hi : i = k := by omega
    have hj : j = 0 := by omega
    exact hk (by rw [hi, hj])
  · by_contra! hge
    have hi : i = 0 := by omega
    have hj : j = k := by omega
    exact h0 (by rw [hi, hj])

/-- A finite sum of 0–1 summands is zero or at least one. -/
private theorem zero_or_one_le_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (h : ∀ i ∈ S, f i = 0 ∨ f i = 1) :
    (∑ i ∈ S, f i) = 0 ∨ 1 ≤ ∑ i ∈ S, f i := by
  classical
  by_cases hOne : ∃ i ∈ S, f i = 1
  · obtain ⟨i, hi, hf⟩ := hOne
    right
    rw [← hf]
    apply Finset.single_le_sum (f := f) _ hi
    intro j hj
    rcases h j hj with h0 | h1
    · rw [h0]
    · rw [h1]
      exact zero_le_one
  · left
    exact Finset.sum_eq_zero fun j hj => (h j hj).resolve_right fun hj' => hOne ⟨j, hj, hj'⟩

private theorem product_binary {x y : ℝ}
    (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) : x * y = 0 ∨ x * y = 1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp

/-- Equal total mass, zero crossed products, and nonnegative entries
identify the two edge coefficients individually. -/
private theorem resolve_edges {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hsame : a + b = c + d) (had : a * d = 0) (hcb : c * b = 0)
    (hbin : a + b = 0 ∨ a + b = 1) :
    (a = 0 ∨ a = 1) ∧ (b = 0 ∨ b = 1) ∧ c = a ∧ d = b := by
  by_cases ha0 : a = 0
  · have hc0 : c = 0 := by
      by_cases hb0 : b = 0
      · linarith
      · exact (mul_eq_zero.mp hcb).resolve_right hb0
    exact ⟨Or.inl ha0, by simpa only [ha0, zero_add] using hbin, hc0.trans ha0.symm, by linarith⟩
  · have hd0 : d = 0 := (mul_eq_zero.mp had).resolve_left ha0
    have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hcPos : 0 < c := by linarith
    have hb0 : b = 0 := (mul_eq_zero.mp hcb).resolve_left hcPos.ne'
    exact ⟨by simpa only [hb0, add_zero] using hbin, Or.inl hb0, by linarith, hd0.trans hb0.symm⟩

/-- Once the constant term of the first polynomial is one, a first factor
with 0–1 coefficients determines 0–1 coefficients of the other factor by
induction on the degree of each coefficient. -/
theorem second_binary_of_first {P Q : ℝ[X]} (hP0 : P.coeff 0 = 1) (hQ : ∀ k, 0 ≤ Q.coeff k)
    (hPbin : ∀ k, P.coeff k = 0 ∨ P.coeff k = 1)
    (hProd : ∀ k, (P * Q).coeff k = 0 ∨ (P * Q).coeff k = 1) :
    ∀ k, Q.coeff k = 0 ∨ Q.coeff k = 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      let A := Finset.HasAntidiagonal.antidiagonal k
      let f := fun z : ℕ × ℕ => P.coeff z.1 * Q.coeff z.2
      have h0 : (0, k) ∈ A := Finset.HasAntidiagonal.mem_antidiagonal.mpr (Nat.zero_add k)
      have hRec : (∑ z ∈ A.erase (0, k), f z) + Q.coeff k = (P * Q).coeff k := by
        have hEq := Finset.sum_erase_add A f h0
        rw [Polynomial.coeff_mul]
        simpa only [f, hP0, one_mul] using hEq
      have hRest := zero_or_one_le_sum (A.erase (0, k)) f (by
        rintro ⟨i, j⟩ hz
        change (i, j) ∈ (Finset.HasAntidiagonal.antidiagonal k).erase (0, k) at hz
        obtain ⟨hne, hsum⟩ := Finset.mem_erase.mp hz
        have hij : i + j = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hsum
        have hj : j < k := by
          by_contra! hge
          have hi0 : i = 0 := by omega
          have hjk : j = k := by omega
          exact hne (by rw [hi0, hjk])
        exact product_binary (hPbin i) (ih j hj))
      rcases hRest with hZero | hOne
      · have hqEq : Q.coeff k = (P * Q).coeff k := by linarith
        rw [hqEq]
        exact hProd k
      · left
        have hle : (P * Q).coeff k ≤ 1 := by rcases hProd k with h | h <;> linarith
        linarith [hQ k]

/-- Agreement of the product with its reverse up to the smaller degree
forces the smaller factor to be symmetric and both factors to be binary. -/
theorem smaller_factor_of_reciprocal_prefix {P Q : ℝ[X]}
    (hPm : P.Monic) (hQm : Q.Monic) (hP : ∀ k, 0 ≤ P.coeff k) (hQ : ∀ k, 0 ≤ Q.coeff k)
    (hEnds : ∀ k ≤ P.natDegree, (P * Q).reverse.coeff k = (P * Q).coeff k)
    (hBin : ∀ k, (P * Q).coeff k = 0 ∨ (P * Q).coeff k = 1)
    (hDegrees : P.natDegree ≤ Q.natDegree) :
    ((∀ k, P.coeff k = 0 ∨ P.coeff k = 1) ∧ P.reverse = P) ∧
      (∀ k, Q.coeff k = 0 ∨ Q.coeff k = 1) := by
  have hle (k : ℕ) : (P * Q).coeff k ≤ 1 := by
    rcases hBin k with hk | hk <;> linarith
  have hpq : P.coeff 0 * Q.coeff 0 = 1 := by
    rw [← Polynomial.mul_coeff_zero, ← hEnds 0 (Nat.zero_le _), Polynomial.coeff_zero_reverse,
      (hPm.mul hQm).leadingCoeff]
  have hLp : P.coeff 0 ≤ 1 := by
    have ht := summand_le_coeff (i := 0) (j := Q.natDegree) hP hQ
    simpa only [hQm.coeff_natDegree, mul_one] using ht.trans (hle _)
  have hLq : Q.coeff 0 ≤ 1 := by
    have ht := summand_le_coeff (i := P.natDegree) (j := 0) hP hQ
    simpa only [hPm.coeff_natDegree, one_mul] using ht.trans (hle _)
  have hP0 : P.coeff 0 = 1 := le_antisymm hLp (by
    calc
      1 = P.coeff 0 * Q.coeff 0 := hpq.symm
      _ ≤ P.coeff 0 * 1 := mul_le_mul_of_nonneg_left hLq (hP 0)
      _ = P.coeff 0 := mul_one _)
  have hQ0 : Q.coeff 0 = 1 := by simpa only [hP0, one_mul] using hpq
  have hPr0 : P.reverse.coeff 0 = 1 := by rw [Polynomial.coeff_zero_reverse, hPm.leadingCoeff]
  have hQr0 : Q.reverse.coeff 0 = 1 := by rw [Polynomial.coeff_zero_reverse, hQm.leadingCoeff]
  have hEdges (k : ℕ) : k ≤ P.natDegree →
      (P.coeff k = 0 ∨ P.coeff k = 1) ∧ (Q.coeff k = 0 ∨ Q.coeff k = 1) ∧
        P.reverse.coeff k = P.coeff k ∧ Q.reverse.coeff k = Q.coeff k := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk
        by_cases hk0 : k = 0
        · subst k
          exact ⟨Or.inr hP0, Or.inr hQ0, hPr0.trans hP0.symm, hQr0.trans hQ0.symm⟩
        have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        let S := ((Finset.HasAntidiagonal.antidiagonal k).erase (k, 0)).erase (0, k)
        let f := fun z : ℕ × ℕ => P.coeff z.1 * Q.coeff z.2
        let g := fun z : ℕ × ℕ => P.reverse.coeff z.1 * Q.reverse.coeff z.2
        have hRestEq : ∑ z ∈ S, f z = ∑ z ∈ S, g z := by
          apply Finset.sum_congr rfl
          intro z hz
          obtain ⟨hi, hj⟩ := interior_lt hz
          dsimp [f, g]
          rw [(ih _ hi (hi.le.trans hk)).2.2.1, (ih _ hj (hj.le.trans hk)).2.2.2]
        have hLow : (P * Q).coeff k = P.coeff k + Q.coeff k + ∑ z ∈ S, f z :=
          coeff_end_sum hkpos hP0 hQ0
        have hHigh : (P * Q).coeff k = P.reverse.coeff k + Q.reverse.coeff k + ∑ z ∈ S, g z := by
          rw [← hEnds k hk, Polynomial.reverse_mul_of_domain]
          exact coeff_end_sum hkpos hPr0 hQr0
        have hTotal : P.coeff k + Q.coeff k = P.reverse.coeff k + Q.reverse.coeff k := by
          linarith [hLow, hHigh, hRestEq]
        have hRest := zero_or_one_le_sum S f (by
          intro z hz
          obtain ⟨hi, hj⟩ := interior_lt hz
          exact product_binary (ih _ hi (hi.le.trans hk)).1 (ih _ hj (hj.le.trans hk)).2.1)
        have hBinSum : P.coeff k + Q.coeff k = 0 ∨ P.coeff k + Q.coeff k = 1 := by
          rcases hRest with hZero | hOne
          · have he : P.coeff k + Q.coeff k = (P * Q).coeff k := by linarith
            rw [he]
            exact hBin k
          · left
            linarith [hLow, hle k, hP k, hQ k]
        have hCross1 : P.coeff k * Q.reverse.coeff k = 0 := by
          rw [Polynomial.coeff_reverse, Polynomial.revAt_le (hk.trans hDegrees)]
          exact zero_of_saturated_coeff hP hQ (hle Q.natDegree)
            (Nat.add_sub_of_le (hk.trans hDegrees)) (Nat.zero_add Q.natDegree)
            (fun h => hk0 (congrArg Prod.fst h)) (by rw [hP0, hQm.coeff_natDegree, one_mul])
        have hCross2 : P.reverse.coeff k * Q.coeff k = 0 := by
          rw [Polynomial.coeff_reverse, Polynomial.revAt_le hk]
          exact zero_of_saturated_coeff hP hQ (hle P.natDegree)
            (Nat.sub_add_cancel hk) (Nat.add_zero P.natDegree)
            (fun h => hk0 (congrArg Prod.snd h)) (by rw [hPm.coeff_natDegree, hQ0, one_mul])
        exact resolve_edges (hP k) (hQ k) (by rw [Polynomial.coeff_reverse]; exact hP _)
          (by rw [Polynomial.coeff_reverse]; exact hQ _) hTotal hCross1 hCross2 hBinSum
  have hPbin (k : ℕ) : P.coeff k = 0 ∨ P.coeff k = 1 := by
    by_cases hk : k ≤ P.natDegree
    · exact (hEdges k hk).1
    · exact Or.inl (Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hk))
  have hPpal : P.reverse = P := by
    ext k
    by_cases hk : k ≤ P.natDegree
    · exact (hEdges k hk).2.2.1
    · rw [Polynomial.coeff_reverse, Polynomial.revAt_eq_self_of_lt (lt_of_not_ge hk)]
  exact ⟨⟨hPbin, hPpal⟩, second_binary_of_first hP0 hQ hPbin hBin⟩

/-- A product whose two coefficient prefixes agree through the smaller
factor degree already has 0–1 factors. -/
theorem factors_binary_of_reciprocal_prefix {P Q : ℝ[X]}
    (hPm : P.Monic) (hQm : Q.Monic) (hP : ∀ k, 0 ≤ P.coeff k) (hQ : ∀ k, 0 ≤ Q.coeff k)
    (hEnds : ∀ k ≤ min P.natDegree Q.natDegree, (P * Q).reverse.coeff k = (P * Q).coeff k)
    (hBin : ∀ k, (P * Q).coeff k = 0 ∨ (P * Q).coeff k = 1) :
    (∀ k, P.coeff k = 0 ∨ P.coeff k = 1) ∧ (∀ k, Q.coeff k = 0 ∨ Q.coeff k = 1) := by
  rcases le_total P.natDegree Q.natDegree with h | h
  · have hPrefix k (hk : k ≤ P.natDegree) := hEnds k (le_min hk (hk.trans h))
    have hResult := smaller_factor_of_reciprocal_prefix hPm hQm hP hQ hPrefix hBin h
    exact ⟨hResult.1.1, hResult.2⟩
  · have hPrefix k (hk : k ≤ Q.natDegree) : (Q * P).reverse.coeff k = (Q * P).coeff k := by
      rw [mul_comm Q P]
      exact hEnds k (le_min (hk.trans h) hk)
    have hBin' (k : ℕ) : (Q * P).coeff k = 0 ∨ (Q * P).coeff k = 1 := by
      rw [mul_comm Q P]
      exact hBin k
    have hResult := smaller_factor_of_reciprocal_prefix hQm hPm hQ hP hPrefix hBin' h
    exact ⟨hResult.2, hResult.1.1⟩

end Green28PalindromicFactors

namespace OMA.Green28Transport

open Finset Polynomial
open scoped BigOperators Polynomial ENNReal

private noncomputable def points (p : PMF ℤ) (h : p.support.Finite) : Finset ℤ :=
  h.toFinset

@[simp]
theorem mem_points (p : PMF ℤ) (h : p.support.Finite) (x : ℤ) :
    x ∈ points p h ↔ x ∈ p.support := h.mem_toFinset

private theorem points_nonempty (p : PMF ℤ) (h : p.support.Finite) : (points p h).Nonempty := by
  obtain ⟨x,hx⟩ := p.support_nonempty
  exact ⟨x,(mem_points p h x).mpr hx⟩

private noncomputable def lower (p : PMF ℤ) (h : p.support.Finite) : ℤ :=
  (points p h).min' (points_nonempty p h)

private noncomputable def upper (p : PMF ℤ) (h : p.support.Finite) : ℤ :=
  (points p h).max' (points_nonempty p h)

theorem lower_mem (p : PMF ℤ) (h : p.support.Finite) : lower p h ∈ p.support :=
  (mem_points _ _ _).mp (Finset.min'_mem _ _)

theorem upper_mem (p : PMF ℤ) (h : p.support.Finite) : upper p h ∈ p.support :=
  (mem_points _ _ _).mp (Finset.max'_mem _ _)

theorem lower_le (p : PMF ℤ) (h : p.support.Finite) {x : ℤ} (hx : x ∈ p.support) :
    lower p h ≤ x :=
  Finset.min'_le _ _ ((mem_points p h x).mpr hx)

theorem le_upper (p : PMF ℤ) (h : p.support.Finite) {x : ℤ} (hx : x ∈ p.support) :
    x ≤ upper p h :=
  Finset.le_max' _ _ ((mem_points p h x).mpr hx)

theorem toReal_ne_zero_iff (p : PMF ℤ) (z : ℤ) : (p z).toReal ≠ 0 ↔ z ∈ p.support := by
  rw [ENNReal.toReal_ne_zero, p.mem_support_iff]
  exact and_iff_left (p.apply_ne_top z)

theorem indepSum_mem_support (p q : PMF ℤ) (z : ℤ) :
    z ∈ (Green28.indepSum p q).support ↔ ∃ x ∈ p.support, ∃ y ∈ q.support, x+y=z := by
  change z ∈ (p.bind (fun x => q.bind (fun y => PMF.pure (x+y)))).support ↔ _
  simp only [PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, eq_comm]

theorem finite_indepSum (p q : PMF ℤ) (hp : p.support.Finite) (hq : q.support.Finite) :
    (Green28.indepSum p q).support.Finite := by
  classical
  let W := ((points p hp) ×ˢ (points q hq)).image (fun a : ℤ × ℤ => a.1+a.2)
  apply W.finite_toSet.subset
  intro z hz
  obtain ⟨x,hx,y,hy,rfl⟩ := (indepSum_mem_support p q z).mp hz
  exact mem_image.mpr ⟨(x,y),mem_product.mpr ⟨(mem_points _ _ _).mpr hx,
    (mem_points _ _ _).mpr hy⟩,rfl⟩

theorem lower_indepSum (p q : PMF ℤ) (hp : p.support.Finite) (hq : q.support.Finite)
    (hs : (Green28.indepSum p q).support.Finite) :
    lower (Green28.indepSum p q) hs = lower p hp + lower q hq := by
  apply le_antisymm
  · apply lower_le
    exact (indepSum_mem_support p q _).mpr ⟨_,lower_mem p hp,_,lower_mem q hq,rfl⟩
  · obtain ⟨x,hx,y,hy,he⟩ :=
      (indepSum_mem_support p q _).mp (lower_mem (Green28.indepSum p q) hs)
    rw [← he]
    exact add_le_add (lower_le p hp hx) (lower_le q hq hy)

theorem upper_indepSum (p q : PMF ℤ) (hp : p.support.Finite) (hq : q.support.Finite)
    (hs : (Green28.indepSum p q).support.Finite) :
    upper (Green28.indepSum p q) hs = upper p hp + upper q hq := by
  apply le_antisymm
  · obtain ⟨x,hx,y,hy,he⟩ :=
      (indepSum_mem_support p q _).mp (upper_mem (Green28.indepSum p q) hs)
    rw [← he]
    exact add_le_add (le_upper p hp hx) (le_upper q hq hy)
  · apply le_upper
    exact (indepSum_mem_support p q _).mpr ⟨_,upper_mem p hp,_,upper_mem q hq,rfl⟩

/-- Raw generating polynomial translated so that its least exponent is zero. -/
private noncomputable def raw (p : PMF ℤ) (h : p.support.Finite) : ℝ[X] :=
  ∑ z ∈ points p h, monomial (z-lower p h).toNat ((p z).toReal)

theorem raw_coeff (p : PMF ℤ) (h : p.support.Finite) (i : ℕ) :
    (raw p h).coeff i = (p (lower p h + i)).toReal := by
  classical
  rw [raw, finsetSum_coeff]
  have hcoeff (z : ℤ) (hz : z ∈ points p h) :
      (monomial (z-lower p h).toNat (p z).toReal : ℝ[X]).coeff i =
        if z = lower p h + i then (p z).toReal else 0 := by
    rw [coeff_monomial]
    have hh := lower_le p h ((mem_points _ _ _).mp hz)
    have he : (z-lower p h).toNat = i ↔ z = lower p h + i := by omega
    simp only [he]
  rw [sum_congr rfl hcoeff, Finset.sum_ite_eq']
  split_ifs with hi
  · rfl
  · have hz : p (lower p h+i) = 0 :=
      (p.apply_eq_zero_iff _).mpr (fun hm => hi ((mem_points _ _ _).mpr hm))
    rw [hz, ENNReal.toReal_zero]

theorem raw_coeff_zero_pos (p : PMF ℤ) (h : p.support.Finite) : 0 < (raw p h).coeff 0 := by
  rw [raw_coeff]
  simp only [Nat.cast_zero, add_zero]
  exact lt_of_le_of_ne ENNReal.toReal_nonneg
    (((toReal_ne_zero_iff p (lower p h)).mpr (lower_mem p h)).symm)

theorem raw_ne_zero (p : PMF ℤ) (h : p.support.Finite) : raw p h ≠ 0 := by
  intro he
  have ht := raw_coeff_zero_pos p h
  rw [he, coeff_zero] at ht
  exact (lt_irrefl _ ht)

theorem raw_natDegree (p : PMF ℤ) (h : p.support.Finite) :
    (raw p h).natDegree = (upper p h-lower p h).toNat := by
  have hlu : lower p h ≤ upper p h := lower_le p h (upper_mem p h)
  apply le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [raw_coeff]
    have hZ : p (lower p h+i) = 0 := (p.apply_eq_zero_iff _).mpr (fun hm => by
      have hh := le_upper p h hm
      omega)
    rw [hZ, ENNReal.toReal_zero]
  · apply le_natDegree_of_ne_zero
    rw [raw_coeff, show lower p h + ((upper p h-lower p h).toNat : ℤ) = upper p h by omega]
    exact (toReal_ne_zero_iff p _).mpr (upper_mem p h)

theorem raw_leadingCoeff (p : PMF ℤ) (h : p.support.Finite) :
    (raw p h).leadingCoeff = (p (upper p h)).toReal := by
  have hlu : lower p h ≤ upper p h := lower_le p h (upper_mem p h)
  rw [leadingCoeff, raw_natDegree, raw_coeff]
  congr 2
  omega

/-- Divide the translated generating polynomial by the largest-exponent mass. -/
private noncomputable def normalized (p : PMF ℤ) (h : p.support.Finite) : ℝ[X] :=
  raw p h * C ((p (upper p h)).toReal)⁻¹

theorem normalized_coeff (p : PMF ℤ) (h : p.support.Finite) (i : ℕ) :
    (normalized p h).coeff i = (p (lower p h + i)).toReal * ((p (upper p h)).toReal)⁻¹ := by
  rw [normalized, coeff_mul_C, raw_coeff]

theorem normalized_monic (p : PMF ℤ) (h : p.support.Finite) : (normalized p h).Monic := by
  unfold normalized
  rw [← raw_leadingCoeff p h]
  exact monic_mul_leadingCoeff_inv (raw_ne_zero p h)

theorem normalized_nonneg (p : PMF ℤ) (h : p.support.Finite) (i : ℕ) :
    0 ≤ (normalized p h).coeff i := by
  rw [normalized_coeff]
  exact mul_nonneg ENNReal.toReal_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)

theorem normalized_coeff_ne_zero_iff (p : PMF ℤ) (h : p.support.Finite) (i : ℕ) :
    (normalized p h).coeff i ≠ 0 ↔ lower p h + i ∈ p.support := by
  rw [normalized_coeff, mul_ne_zero_iff, toReal_ne_zero_iff]
  exact and_iff_left (inv_ne_zero ((toReal_ne_zero_iff p _).mpr (upper_mem p h)))

end OMA.Green28Transport

namespace OMA.Green28Transport

open Finset Polynomial
open scoped Polynomial BigOperators ENNReal

/-- A binary polynomial has every nonzero coefficient equal to one. -/
private def Binary (P : ℝ[X]) : Prop := ∀ i : ℕ, P.coeff i ≠ 0 → P.coeff i = 1

private theorem mass_eq_of_uniform {p : PMF ℤ} (h : Green28.IsUniformOnSupport p)
    {x y : ℤ} (hx : x ∈ p.support) (hy : y ∈ p.support) : p x = p y := by
  obtain ⟨S,hS,rfl⟩ := h
  exact (PMF.uniformOfFinset_apply_of_mem hS ((PMF.mem_support_uniformOfFinset_iff _ _).mp hx)).trans
    (PMF.uniformOfFinset_apply_of_mem hS ((PMF.mem_support_uniformOfFinset_iff _ _).mp hy)).symm

private theorem uniform_of_constant_mass (p : PMF ℤ) (h : p.support.Finite)
    (c : ℝ≥0∞) (hc : ∀ x ∈ p.support, p x = c) : Green28.IsUniformOnSupport p := by
  classical
  let S := points p h
  have hS : S.Nonempty := by
    obtain ⟨a,ha⟩ := p.support_nonempty
    exact ⟨a,(mem_points p h a).mpr ha⟩
  have hm (x : ℤ) (hx : x ∉ S) : p x = 0 :=
    (p.apply_eq_zero_iff x).mpr (fun hx' => hx ((mem_points p h x).mpr hx'))
  have hsum : c * (S.card : ℝ≥0∞) = 1 := by
    calc
      _ = ∑ x ∈ S, c := by simp [mul_comm]
      _ = ∑ x ∈ S, p x := sum_congr rfl fun x hx => (hc x ((mem_points p h x).mp hx)).symm
      _ = ∑' x, p x := (tsum_eq_sum (s := S) hm).symm
      _ = 1 := p.tsum_coe
  have hc' : c = (S.card : ℝ≥0∞)⁻¹ := ENNReal.eq_inv_of_mul_eq_one_left hsum
  refine ⟨S,hS,PMF.ext fun x => ?_⟩
  by_cases hx : x ∈ S
  · rw [PMF.uniformOfFinset_apply_of_mem hS hx, hc x ((mem_points p h x).mp hx), hc']
  · rw [PMF.uniformOfFinset_apply_of_notMem hS hx, hm x hx]

theorem uniform_iff_normalized_binary (p : PMF ℤ) (h : p.support.Finite) :
    Green28.IsUniformOnSupport p ↔ Binary (normalized p h) := by
  constructor
  · intro hp i hi
    have hm := (normalized_coeff_ne_zero_iff p h i).mp hi
    rw [normalized_coeff, mass_eq_of_uniform hp hm (upper_mem p h),
      mul_inv_cancel₀ ((toReal_ne_zero_iff p _).mpr (upper_mem p h))]
  · intro hb
    refine uniform_of_constant_mass p h (p (upper p h)) (fun x hx => ?_)
    have hl := lower_le p h hx
    let i := (x-lower p h).toNat
    have hx' : x = lower p h + i := by dsimp only [i]; omega
    have hi : (normalized p h).coeff i = 1 :=
      hb i ((normalized_coeff_ne_zero_iff p h i).mpr (by rw [← hx']; exact hx))
    rw [normalized_coeff, ← hx'] at hi
    have hc : (p (upper p h)).toReal ≠ 0 :=
      (toReal_ne_zero_iff p _).mpr (upper_mem p h)
    apply (ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top x) (p.apply_ne_top _)).mp
    calc
      _ = ((p x).toReal * ((p (upper p h)).toReal)⁻¹) * (p (upper p h)).toReal := by
        rw [mul_assoc, inv_mul_cancel₀ hc, mul_one]
      _ = _ := by rw [hi,one_mul]

theorem convolution_mass_finite (p q : PMF ℤ) (hp : p.support.Finite) (hq : q.support.Finite)
    (z : ℤ) :
    Green28.indepSum p q z =
      ∑ x ∈ points p hp, ∑ y ∈ points q hq, if x+y=z then p x * q y else 0 := by
  classical
  change (p.bind (fun x => q.bind (fun y => PMF.pure (x+y)))) z = _
  rw [PMF.bind_apply, tsum_eq_sum (s := points p hp)]
  · apply sum_congr rfl
    intro x _
    rw [PMF.bind_apply, tsum_eq_sum (s := points q hq)]
    · rw [mul_sum]
      apply sum_congr rfl
      intro y _
      by_cases he : x+y=z
      · simp [he]
      · simp [he,Ne.symm he]
    · intro y hy
      rw [(q.apply_eq_zero_iff y).mpr (fun h => hy ((mem_points q hq y).mpr h)),zero_mul]
  · intro x hx
    rw [(p.apply_eq_zero_iff x).mpr (fun h => hx ((mem_points p hp x).mpr h)),zero_mul]

theorem convolution_real_mass (p q : PMF ℤ) (hp : p.support.Finite) (hq : q.support.Finite)
    (z : ℤ) :
    (Green28.indepSum p q z).toReal =
      ∑ x ∈ points p hp, ∑ y ∈ points q hq, if x+y=z then (p x).toReal * (q y).toReal else 0 := by
  classical
  have ht (x y : ℤ) : (if x+y=z then p x * q y else 0) ≠ ⊤ := by
    split_ifs
    · exact ENNReal.mul_ne_top (p.apply_ne_top x) (q.apply_ne_top y)
    · exact ENNReal.zero_ne_top
  rw [convolution_mass_finite p q hp hq z, ENNReal.toReal_sum
    (fun x _ => ENNReal.sum_ne_top.mpr (fun y _ => ht x y))]
  apply sum_congr rfl
  intro x _
  rw [ENNReal.toReal_sum (fun y _ => ht x y)]
  apply sum_congr rfl
  intro y _
  split_ifs
  · exact ENNReal.toReal_mul
  · exact ENNReal.toReal_zero

/-- The generating polynomial is multiplicative under discrete convolution. -/
theorem raw_indepSum (p q : PMF ℤ) (hp : p.support.Finite) (hq : q.support.Finite)
    (hs : (Green28.indepSum p q).support.Finite) :
    raw (Green28.indepSum p q) hs = raw p hp * raw q hq := by
  classical
  ext i
  rw [raw_coeff, lower_indepSum p q hp hq hs, convolution_real_mass p q hp hq]
  unfold raw
  rw [sum_mul]
  simp only [mul_sum, finsetSum_coeff]
  apply sum_congr rfl
  intro x hx
  apply sum_congr rfl
  intro y hy
  rw [monomial_mul_monomial, coeff_monomial]
  have hx' := lower_le p hp ((mem_points p hp x).mp hx)
  have hy' := lower_le q hq ((mem_points q hq y).mp hy)
  have he : ((x-lower p hp).toNat + (y-lower q hq).toNat : ℕ) = i ↔
      x+y = lower p hp + lower q hq + i := by omega
  simp only [he]

private theorem normalized_eq_leading (p : PMF ℤ) (h : p.support.Finite) :
    normalized p h = raw p h * C ((raw p h).leadingCoeff)⁻¹ := by
  rw [normalized, raw_leadingCoeff]

theorem normalized_indepSum (p q : PMF ℤ) (hp : p.support.Finite) (hq : q.support.Finite)
    (hs : (Green28.indepSum p q).support.Finite) :
    normalized (Green28.indepSum p q) hs = normalized p hp * normalized q hq := by
  simp only [normalized_eq_leading, raw_indepSum p q hp hq hs,
    leadingCoeff_mul, mul_inv_rev, map_mul]
  ring

/-- The support-uniformity problem transfers to the first factor of a
binary polynomial through the normalized probability generating polynomials. -/
theorem first_factor_transport
    (hFactor : ∀ P Q : ℝ[X], P.Monic → Q.Monic →
      (∀ i, 0 ≤ P.coeff i) → (∀ i, 0 ≤ Q.coeff i) → Binary (P*Q) → Binary P) :
    ∀ p q : PMF ℤ, p.support.Finite → q.support.Finite →
      Green28.IsUniformOnSupport (Green28.indepSum p q) → Green28.IsUniformOnSupport p := by
  intro p q hp hq hU
  let hs := finite_indepSum p q hp hq
  have hb := (uniform_iff_normalized_binary (Green28.indepSum p q) hs).mp hU
  rw [normalized_indepSum p q hp hq hs] at hb
  exact (uniform_iff_normalized_binary p hp).mpr
    (hFactor (normalized p hp) (normalized q hq) (normalized_monic p hp) (normalized_monic q hq)
      (normalized_nonneg p hp) (normalized_nonneg q hq) hb)

theorem normalized_coeff_zero_pos (p : PMF ℤ) (h : p.support.Finite) :
    0 < (normalized p h).coeff 0 := by
  rw [normalized, coeff_mul_C]
  refine mul_pos (raw_coeff_zero_pos p h) (inv_pos.mpr ?_)
  exact lt_of_le_of_ne ENNReal.toReal_nonneg
    (((toReal_ne_zero_iff p (upper p h)).mpr (upper_mem p h)).symm)

theorem normalized_product_coeff_zero_pos (p q : PMF ℤ)
    (hp : p.support.Finite) (hq : q.support.Finite) :
    0 < (normalized p hp * normalized q hq).coeff 0 := by
  rw [mul_coeff_zero]
  exact mul_pos (normalized_coeff_zero_pos p hp) (normalized_coeff_zero_pos q hq)

/-- The exact Green28 conclusion from the corresponding binary-factor theorem,
with positive constant coefficient on the product. -/
theorem both_factors_transport
    (hFactor : ∀ P Q : ℝ[X], P.Monic → Q.Monic →
      (∀ i, 0 ≤ P.coeff i) → (∀ i, 0 ≤ Q.coeff i) →
        0 < (P*Q).coeff 0 → Binary (P*Q) → Binary P ∧ Binary Q) :
    ∀ p q : PMF ℤ, p.support.Finite ∧ q.support.Finite ∧
      Green28.IsUniformOnSupport (Green28.indepSum p q) →
      Green28.IsUniformOnSupport p ∧ Green28.IsUniformOnSupport q := by
  rintro p q ⟨hp,hq,hU⟩
  let hs := finite_indepSum p q hp hq
  have hb := (uniform_iff_normalized_binary (Green28.indepSum p q) hs).mp hU
  rw [normalized_indepSum p q hp hq hs] at hb
  obtain ⟨hP,hQ⟩ := hFactor (normalized p hp) (normalized q hq) (normalized_monic p hp)
    (normalized_monic q hq) (normalized_nonneg p hp) (normalized_nonneg q hq)
    (normalized_product_coeff_zero_pos p q hp hq) hb
  exact ⟨(uniform_iff_normalized_binary p hp).mpr hP, (uniform_iff_normalized_binary q hq).mpr hQ⟩

end OMA.Green28Transport

namespace GreenSmallDegree

open GreenFactorBounds

private theorem convolution_one (P Q : ℝ[X]) (p0 : P.coeff 0 = 1) (q0 : Q.coeff 0 = 1) :
    (P*Q).coeff 1 = P.coeff 1 + Q.coeff 1 := by
  rw [Polynomial.coeff_mul]
  have hset : Finset.HasAntidiagonal.antidiagonal 1 = {(0,1),(1,0)} := by decide
  rw [hset, Finset.sum_pair (by decide), p0, q0, one_mul, mul_one, add_comm]

private theorem convolution_two (P Q : ℝ[X]) (p0 : P.coeff 0 = 1) (q0 : Q.coeff 0 = 1) :
    (P*Q).coeff 2 = P.coeff 2 + P.coeff 1 * Q.coeff 1 + Q.coeff 2 := by
  rw [Polynomial.coeff_mul]
  have hset : Finset.HasAntidiagonal.antidiagonal 2 = {(0,2),(1,1),(2,0)} := by decide
  rw [hset, Finset.sum_insert (by decide), Finset.sum_pair (by decide), p0, q0, one_mul, mul_one]
  ring

private theorem convolution_three (P Q : ℝ[X]) (p0 : P.coeff 0 = 1) (q0 : Q.coeff 0 = 1) :
    (P*Q).coeff 3 =
      P.coeff 3 + P.coeff 2 * Q.coeff 1 + P.coeff 1 * Q.coeff 2 + Q.coeff 3 := by
  rw [Polynomial.coeff_mul]
  have hset : Finset.HasAntidiagonal.antidiagonal 3 = {(0,3),(1,2),(2,1),(3,0)} := by decide
  rw [hset, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_pair (by decide), p0, q0, one_mul, mul_one]
  ring

private theorem r1_positive {x : ℝ} (h : x = 0 ∨ x = 1) (hx : 0 < x) : x = 1 :=
  h.resolve_left hx.ne'

private theorem rf_forbid {x : ℝ} (h : x = 0 ∨ x = 1) (h0 : 0 < x) (h1 : x < 1) : False :=
  h1.ne (r1_positive h h0)

private theorem saturated {P Q : ℝ[X]} (monic : P.Monic) (q0 : Q.coeff 0 = 1)
    (pnon : ∀ i, 0 ≤ P.coeff i) (qnon : ∀ i, 0 ≤ Q.coeff i)
    (bin : ∀ i, (P*Q).coeff i = 0 ∨ (P*Q).coeff i = 1)
    (i j : ℕ) (hs : i+j = P.natDegree) (hj : 0 < j) : P.coeff i * Q.coeff j = 0 := by
  have hl := coeff_product_two_lower P Q pnon qnon
    (P.natDegree,0) (i,j) (Nat.add_zero _) hs (fun h => (Nat.ne_of_gt hj) (congrArg Prod.snd h).symm)
  change P.coeff P.natDegree * Q.coeff 0 + P.coeff i * Q.coeff j ≤ _ at hl
  rw [monic.coeff_natDegree, q0, one_mul] at hl
  have hu : (P*Q).coeff P.natDegree ≤ 1 := by rcases bin _ with he | he <;> linarith
  exact le_antisymm (by linarith) (mul_nonneg (pnon i) (qnon j))

private theorem first_binary {P Q : ℝ[X]} (mp : P.Monic) (mq : Q.Monic)
    (hp : ∀ i, 0 ≤ P.coeff i) (hq : ∀ i, 0 ≤ Q.coeff i)
    (p0 : P.coeff 0 = 1) (q0 : Q.coeff 0 = 1)
    (hid : P.natDegree = 3 ∨ P.natDegree = 4)
    (hb : ∀ i, (P*Q).coeff i = 0 ∨ (P*Q).coeff i = 1) :
    P.coeff 1 = 0 ∨ P.coeff 1 = 1 := by
  by_cases aa : P.coeff 1 = 0
  · exact Or.inl aa
  by_cases ab : P.coeff 1 = 1
  · exact Or.inr ab
  exfalso
  have apos : 0 < P.coeff 1 := lt_of_le_of_ne (hp 1) (Ne.symm aa)
  have alt : P.coeff 1 < 1 := lt_of_le_of_ne (factor_coeff_upper P Q hp hq mq hb 1) ab
  have r1 : P.coeff 1 + Q.coeff 1 = 1 := by
    have he := convolution_one P Q p0 q0
    exact he.symm.trans (r1_positive (hb 1) (by rw [he]; linarith [hq 1]))
  have qpos : 0 < Q.coeff 1 := by linarith
  have qlt : Q.coeff 1 < 1 := by linarith
  have pp : 0 < P.coeff 1 * Q.coeff 1 := mul_pos apos qpos
  have pt : P.coeff 1 * Q.coeff 1 < 1 :=
    (mul_le_of_le_one_right apos.le qlt.le).trans_lt alt
  rcases hid with d3 | d4
  · have m21 := saturated mp q0 hp hq hb 2 1 (by rw [d3]) (by decide)
    have m12 := saturated mp q0 hp hq hb 1 2 (by rw [d3]) (by decide)
    have zP := (mul_eq_zero.mp m21).resolve_right qpos.ne'
    have zQ := (mul_eq_zero.mp m12).resolve_left apos.ne'
    have r2 := convolution_two P Q p0 q0
    rw [zP,zQ,zero_add,add_zero] at r2
    exact rf_forbid (hb 2) (r2.symm ▸ pp) (r2.symm ▸ pt)
  · have m31 := saturated mp q0 hp hq hb 3 1 (by rw [d4]) (by decide)
    have m13 := saturated mp q0 hp hq hb 1 3 (by rw [d4]) (by decide)
    have m22 := saturated mp q0 hp hq hb 2 2 (by rw [d4]) (by decide)
    have zP := (mul_eq_zero.mp m31).resolve_right qpos.ne'
    have zQ := (mul_eq_zero.mp m13).resolve_left apos.ne'
    have r2 := convolution_two P Q p0 q0
    have r2one : (P*Q).coeff 2 = 1 := r1_positive (hb 2) (by rw [r2]; linarith [hp 2,hq 2])
    have r3 := convolution_three P Q p0 q0
    rw [zP,zQ,zero_add,add_zero] at r3
    rcases mul_eq_zero.mp m22 with z | z
    · rw [z,zero_mul,zero_add] at r3
      have q2p : 0 < Q.coeff 2 := by rw [z,zero_add] at r2; linarith
      have q2t : Q.coeff 2 ≤ 1 := by rw [z,zero_add] at r2; linarith
      have lt := (mul_le_of_le_one_right apos.le q2t).trans_lt alt
      exact rf_forbid (hb 3) (r3.symm ▸ mul_pos apos q2p) (r3.symm ▸ lt)
    · rw [z,mul_zero,add_zero] at r3
      have p2p : 0 < P.coeff 2 := by rw [z,add_zero] at r2; linarith
      have p2t : P.coeff 2 < 1 := by rw [z,add_zero] at r2; linarith
      have lt := (mul_le_of_le_one_right p2p.le qlt.le).trans_lt p2t
      exact rf_forbid (hb 3) (r3.symm ▸ mul_pos p2p qpos) (r3.symm ▸ lt)

private theorem middle_binary {P Q : ℝ[X]} (monic : P.Monic)
    (hp : ∀ i, 0 ≤ P.coeff i) (hq : ∀ i, 0 ≤ Q.coeff i)
    (p0 : P.coeff 0 = 1) (q0 : Q.coeff 0 = 1) (hd : P.natDegree = 4)
    (hb : ∀ i, (P*Q).coeff i = 0 ∨ (P*Q).coeff i = 1)
    (first : P.coeff 1 = 0 ∨ P.coeff 1 = 1) : P.coeff 2 = 0 ∨ P.coeff 2 = 1 := by
  have original : P.coeff 1 * Q.coeff 1 = 0 := by
    rcases first with he | he
    · rw [he,zero_mul]
    · rw [he,one_mul]
      have hx := convolution_one P Q p0 q0
      have upper : (P*Q).coeff 1 ≤ 1 := by rcases hb 1 with hz | hz <;> linarith
      linarith [hq 1]
  have hsat := saturated monic q0 hp hq hb 2 2 (by rw [hd]) (by decide)
  rcases mul_eq_zero.mp hsat with hP | hQ
  · exact Or.inl hP
  · simpa only [convolution_two P Q p0 q0, original,hQ,add_zero] using hb 2

private theorem reverseFacts (P : ℝ[X]) (monic : P.Monic)
    (nonnegative : ∀ i, 0 ≤ P.coeff i) (h0 : P.coeff 0 = 1) :
    P.reverse.Monic ∧ (∀ i, 0 ≤ P.reverse.coeff i) ∧
      P.reverse.coeff 0 = 1 ∧ P.reverse.natDegree = P.natDegree := by
  have ht : P.natTrailingDegree = 0 :=
    (Polynomial.natTrailingDegree_eq_zero).mpr (Or.inr (by rw [h0]; exact (one_ne_zero : (1:ℝ) ≠ 0)))
  have hc : P.trailingCoeff = 1 := by rw [Polynomial.trailingCoeff, ht,h0]
  refine ⟨by change _ = 1; rw [Polynomial.reverse_leadingCoeff,hc],
    fun i => by rw [Polynomial.coeff_reverse]; exact nonnegative _, ?_, ?_⟩
  · rw [Polynomial.coeff_zero_reverse,monic.leadingCoeff]
  · rw [Polynomial.reverse_natDegree,ht,Nat.sub_zero]

theorem degree_three_or_four_binary {P Q : ℝ[X]} (mp : P.Monic) (mq : Q.Monic)
    (hp : ∀ i, 0 ≤ P.coeff i) (hq : ∀ i, 0 ≤ Q.coeff i)
    (p0 : P.coeff 0 = 1) (q0 : Q.coeff 0 = 1)
    (hid : P.natDegree = 3 ∨ P.natDegree = 4)
    (hb : ∀ i, (P*Q).coeff i = 0 ∨ (P*Q).coeff i = 1) :
    ∀ i, P.coeff i = 0 ∨ P.coeff i = 1 := by
  have first := first_binary mp mq hp hq p0 q0 hid hb
  obtain ⟨mpr,hpr,p0r,pdeg⟩ := reverseFacts P mp hp p0
  obtain ⟨mqr,hqr,q0r,_⟩ := reverseFacts Q mq hq q0
  have hbr (i : ℕ) : (P.reverse*Q.reverse).coeff i = 0 ∨ (P.reverse*Q.reverse).coeff i = 1 := by
    rw [← Polynomial.reverse_mul_of_domain, Polynomial.coeff_reverse]
    exact hb _
  have last := first_binary mpr mqr hpr hqr p0r q0r (by rwa [pdeg]) hbr
  have degPos : 1 ≤ P.natDegree := by omega
  rw [Polynomial.coeff_reverse, Polynomial.revAt_le degPos] at last
  intro i
  by_cases hi : P.natDegree < i
  · exact Or.inl (Polynomial.coeff_eq_zero_of_natDegree_lt hi)
  rcases hid with d3 | d4
  · have values : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = P.natDegree := by omega
    rcases values with rfl | rfl | rfl | rfl
    · exact Or.inr p0
    · exact first
    · simpa only [d3] using last
    · exact Or.inr mp.coeff_natDegree
  · have values : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = P.natDegree := by omega
    rcases values with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr p0
    · exact first
    · exact middle_binary mp hp hq p0 q0 d4 hb first
    · simpa only [d4] using last
    · exact Or.inr mp.coeff_natDegree

end GreenSmallDegree

namespace OMA.R_Green28_green_28_R2

open GreenFactorBounds

/-- The smaller factor of degree five when a reflected coefficient differs. -/
def H1 : Prop :=
  ∀ P Q : ℝ[X], P.Monic → Q.Monic →
    (∀ i, 0 ≤ P.coeff i) → (∀ i, 0 ≤ Q.coeff i) →
    P.coeff 0 = 1 → Q.coeff 0 = 1 → P.natDegree = 5 →
    P.natDegree < Q.natDegree →
    (∃ k ≤ P.natDegree, (P*Q).reverse.coeff k ≠ (P*Q).coeff k) →
    (∀ i, (P*Q).coeff i = 0 ∨ (P*Q).coeff i = 1) →
    ∀ i, P.coeff i = 0 ∨ P.coeff i = 1

/-- The smaller factor of higher degree when a reflected coefficient differs. -/
def H2 : Prop :=
  ∀ P Q : ℝ[X], P.Monic → Q.Monic →
    (∀ i, 0 ≤ P.coeff i) → (∀ i, 0 ≤ Q.coeff i) →
    P.coeff 0 = 1 → Q.coeff 0 = 1 → 6 ≤ P.natDegree →
    P.natDegree < Q.natDegree →
    (∃ k ≤ P.natDegree, (P*Q).reverse.coeff k ≠ (P*Q).coeff k) →
    (∀ i, (P*Q).coeff i = 0 ∨ (P*Q).coeff i = 1) →
    ∀ i, P.coeff i = 0 ∨ P.coeff i = 1

theorem main : H1 → H2 → type_of% @Green28.green_28 := by
  intro low high
  apply OMA.Green28Transport.both_factors_transport
  intro P Q monicP monicQ posP posQ productConst binary
  have hk (i : ℕ) : (P*Q).coeff i = 0 ∨ (P*Q).coeff i = 1 := by
    by_cases h : (P*Q).coeff i = 0
    · exact Or.inl h
    · exact Or.inr (binary i h)
  obtain ⟨hP0,hQ0⟩ := constant_one P Q monicP monicQ posP posQ hk productConst
  have factors : (∀ i, P.coeff i = 0 ∨ P.coeff i = 1) ∧
      (∀ i, Q.coeff i = 0 ∨ Q.coeff i = 1) := by
    by_cases reflected : ∀ k ≤ min P.natDegree Q.natDegree,
        (P*Q).reverse.coeff k = (P*Q).coeff k
    · exact Green28PalindromicFactors.factors_binary_of_reciprocal_prefix
        monicP monicQ posP posQ reflected hk
    push Not at reflected
    have sorted (A B : ℝ[X]) (mA : A.Monic) (mB : B.Monic)
        (posA : ∀ i, 0 ≤ A.coeff i) (posB : ∀ i, 0 ≤ B.coeff i)
        (a0 : A.coeff 0 = 1) (b0 : B.coeff 0 = 1)
        (ord : A.natDegree < B.natDegree)
        (nonpal : ∃ k ≤ A.natDegree, (A*B).reverse.coeff k ≠ (A*B).coeff k)
        (bin : ∀ i, (A*B).coeff i = 0 ∨ (A*B).coeff i = 1) :
        (∀ i, A.coeff i = 0 ∨ A.coeff i = 1) ∧
        (∀ i, B.coeff i = 0 ∨ B.coeff i = 1) := by
      have first : ∀ i, A.coeff i = 0 ∨ A.coeff i = 1 := by
        by_cases lowDegree : A.natDegree ≤ 1
        · exact degree_le_one_binary A mA a0 lowDegree
        by_cases degreeTwo : A.natDegree = 2
        · exact degree_two_binary A B mA posA posB a0 b0 degreeTwo bin
        by_cases small : A.natDegree ≤ 4
        · exact GreenSmallDegree.degree_three_or_four_binary mA mB posA posB a0 b0 (by omega) bin
        by_cases middle : A.natDegree = 5
        · exact low A B mA mB posA posB a0 b0 middle ord nonpal bin
        · exact high A B mA mB posA posB a0 b0 (by omega) ord nonpal bin
      exact ⟨first, Green28PalindromicFactors.second_binary_of_first a0 posB first bin⟩
    have hkSwap (i : ℕ) : (Q*P).coeff i = 0 ∨ (Q*P).coeff i = 1 := by
      simpa only [mul_comm Q P] using hk i
    by_cases hdeg : P.natDegree < Q.natDegree
    · exact sorted P Q monicP monicQ posP posQ hP0 hQ0 hdeg
        (by simpa only [min_eq_left hdeg.le] using reflected) hk
    by_cases hdeg' : Q.natDegree < P.natDegree
    · exact (sorted Q P monicQ monicP posQ posP hQ0 hP0 hdeg'
        (by simpa only [min_eq_right hdeg'.le, mul_comm Q P] using reflected) hkSwap).symm
    rcases degree_or_constant P Q monicP monicQ posP posQ hk hP0 hQ0 with h | h | h
    · subst P
      exact ⟨degree_le_one_binary _ monicP hP0 (by simp),
        fun i => by simpa only [one_mul] using hk i⟩
    · subst Q
      exact ⟨fun i => by simpa only [mul_one] using hk i,
        degree_le_one_binary _ monicQ hQ0 (by simp)⟩
    · exact (h (le_antisymm (le_of_not_gt hdeg') (le_of_not_gt hdeg))).elim
  exact ⟨fun i h => (factors.1 i).resolve_left h, fun i h => (factors.2 i).resolve_left h⟩

end OMA.R_Green28_green_28_R2
