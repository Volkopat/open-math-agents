import OMAStatements.S_mo_139071
import Mathlib

/-!
# Vandermonde factorization of alternating polynomials

Source: zen-dev, https://mathoverflow.net/questions/139071 (CC BY-SA 3.0).
Credit: @connoranderson. Identifying two variables kills an alternating
polynomial. Each earlier factor in the product survives the next identification,
so each remaining quotient still vanishes on that diagonal. The determinant
formula for the Vandermonde matrix then gives symmetry of the final quotient.
This shortening uses standard swap-invariance, coefficient-map injectivity and
product-difference divisibility lemmas in the same argument.
-/

namespace OMA.S_mo_139071
open MvPolynomial Finset Equiv

variable {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
private abbrev P (n : ℕ) (R : Type*) [CommRing R] := MvPolynomial (Fin n) R

private def collapse (i j k : Fin n) : Fin n := if k = j then i else k

omit [IsDomain R] in
private lemma factorDifference (i j : Fin n) (p : P n R) :
    X j - X i ∣ p - rename (collapse i j) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add, add_sub_add_comm]
    exact dvd_add hp hq
  | mul_X p k hp =>
    rw [map_mul, rename_X]
    have h : X j - X i ∣ X k - (X (collapse i j k) : P n R) := by
      by_cases hk : k = j <;> simp [collapse, hk]
    exact dvd_mul_sub_mul hp h

private lemma collapseZero (h₂ : (2 : R) ≠ 0) (p : P n R)
    (hp : ∀ σ : Perm (Fin n), rename σ p = σ.sign • p) {i j : Fin n} (hij : i < j) :
    rename (collapse i j) p = 0 := by
  have he : collapse i j ∘ swap i j = collapse i j := by
    funext t
    exact Equiv.apply_swap_eq_self (by simp [collapse]) t
  have hs : rename (swap i j) p = -p := by simpa [Perm.sign_swap hij.ne] using hp (swap i j)
  have hh := congrArg (rename (collapse i j) (R := R)) hs
  rw [rename_rename, he, map_neg] at hh
  have hn : (2 : P n R) ≠ 0 := by
    simpa only [map_ofNat] using (C_ne_zero (σ := Fin n)).mpr h₂
  apply (mul_eq_zero.mp (show 2 * rename (collapse i j) p = 0 by linear_combination hh)).resolve_left hn

private lemma remainsDistinct {i j u v : Fin n} (hij : i < j) (huv : u < v)
    (hne : (u, v) ≠ (i, j)) : collapse i j v ≠ collapse i j u := by
  simp only [collapse]
  split_ifs with hv hu hu <;> simp_all [Prod.ext_iff] <;> omega

private lemma productDivides (h₂ : (2 : R) ≠ 0) (p : P n R)
    (hp : ∀ σ : Perm (Fin n), rename σ p = σ.sign • p) (s : Finset (Fin n × Fin n))
    (hs : ∀ b ∈ s, b.1 < b.2) :
    (∏ b ∈ s, (X b.2 - X b.1)) ∣ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert b s hb ih =>
    rcases b with ⟨i,j⟩
    have hrest : ∀ c ∈ s, c.1 < c.2 := fun c hc => hs c (mem_insert_of_mem hc)
    have hij : i < j := hs (i,j) (mem_insert_self ..)
    obtain ⟨q, hq⟩ := ih hrest
    have hh := collapseZero h₂ p hp hij
    rw [hq, map_mul, map_prod] at hh
    have hn : (∏ b ∈ s, rename (collapse i j) (X b.2 - X b.1 : P n R)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro b hbs
      rw [map_sub, rename_X, rename_X]
      refine sub_ne_zero.mpr (X_injective.ne (remainsDistinct hij (hrest b hbs) ?_))
      intro he
      exact hb (he ▸ hbs)
    have hz := (mul_eq_zero.mp hh).resolve_left hn
    obtain ⟨t, ht⟩ : X j - X i ∣ q := by
      simpa [hz] using factorDifference i j q
    refine ⟨t, ?_⟩
    rw [prod_insert hb, hq, ht]
    ring

omit [IsDomain R] in
private lemma vandermondeRename (σ : Perm (Fin n)) :
    let D := (Matrix.vandermonde (X : Fin n → P n R)).det
    rename σ D = σ.sign • D := by
  dsimp only
  change (rename σ (R := R)).toRingHom _ = _
  rw [RingHom.map_det (rename σ (R := R)).toRingHom]
  have he : (rename σ (R := R)).toRingHom.mapMatrix (Matrix.vandermonde X) =
      (Matrix.vandermonde (X : Fin n → P n R)).submatrix σ id := by
    ext i j
    simp [Matrix.vandermonde_apply]
  rw [he, Matrix.det_permute]
  simp [Units.smul_def]

theorem factorization (h₂ : (2 : R) ≠ 0) (p : P n R)
    (hp : ∀ σ : Perm (Fin n), rename σ p = σ.sign • p) :
    ∃ q : P n R, q.IsSymmetric ∧
      p = (∏ i : Fin n, ∏ j ∈ Ioi i, (X j - X i)) * q := by
  classical
  let s := (univ : Finset (Fin n × Fin n)).filter fun b => b.1 < b.2
  have hs (b : Fin n × Fin n) : b ∈ s ↔ b.1 < b.2 := by simp [s]
  have hprod := Finset.prod_finset_product' (β := P n R) s univ Ioi
    (fun b => by simp [hs b]) (f := fun i j => X j - X i)
  obtain ⟨q, hq⟩ := productDivides h₂ p hp s (fun b hb => (hs b).mp hb)
  rw [hprod] at hq
  refine ⟨q, ?_, hq⟩
  rw [← Matrix.det_vandermonde] at hq
  let D := (Matrix.vandermonde (X : Fin n → P n R)).det
  have hn : D ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr X_injective
  intro σ
  have hh := hp σ
  rw [hq, map_mul, vandermondeRename] at hh
  change (σ.sign • D) * rename σ q = σ.sign • (D * q) at hh
  rw [smul_mul_assoc] at hh
  exact mul_left_cancel₀ hn ((MulAction.injective σ.sign) hh)

end OMA.S_mo_139071

theorem OMA.solution : type_of% @OMA.S_mo_139071.main := by
  intro R _ _ h₂ n p hp
  exact OMA.S_mo_139071.factorization h₂ p hp
