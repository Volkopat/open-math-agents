import OMAStatements.S_mo_244114
import Mathlib

-- Retains @AkiRA-COM-FP's specialization counterexample from PR #16217.
-- Standard image, principal-ideal, and radical APIs replace auxiliary proofs.

open Polynomial

open OMA.S_mo_244114

private noncomputable def badIdeal : Ideal (MvPolynomial (Fin 2) ℂ) :=
  Ideal.span ({MvPolynomial.X 0 + MvPolynomial.X 1, MvPolynomial.X 0 ^ 2} :
    Set (MvPolynomial (Fin 2) ℂ))

private noncomputable def diagonalEvaluation : MvPolynomial (Fin 2) ℂ →+* ℂ[X] :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => if i = 0 then Polynomial.X else -Polynomial.X)

private theorem bad_not_radical : ¬ badIdeal.IsRadical := by
  intro h
  have hsq : MvPolynomial.X 0 ^ 2 ∈ badIdeal :=
    Ideal.subset_span (by simp)
  have hRad : MvPolynomial.X 0 ∈ badIdeal.radical := ⟨2,hsq⟩
  have hx : MvPolynomial.X 0 ∈ badIdeal := h hRad
  have hImage : badIdeal.map diagonalEvaluation = Ideal.span ({Polynomial.X ^ 2} : Set ℂ[X]) := by
    rw [badIdeal,Ideal.map_span,Set.image_pair]
    simp [diagonalEvaluation]
  have hMem := Ideal.mem_map_of_mem diagonalEvaluation hx
  rw [hImage] at hMem
  have hd : Polynomial.X ^ 2 ∣ (Polynomial.X : ℂ[X]) := by
    apply Ideal.mem_span_singleton.mp
    simpa [diagonalEvaluation] using hMem
  have hDeg := Polynomial.natDegree_le_of_dvd hd (Polynomial.X_ne_zero (R := ℂ))
  simp at hDeg

private theorem radical_x : (Ideal.span ({Polynomial.X} : Set ℂ[X])).IsRadical := by
  exact (Ideal.isPrime_span_singleton_of_prime Polynomial.prime_X).isRadical

private theorem radical_specialize_zero (a : Fin 2 → ℂ) :
    (badIdeal.map (specialize 0 a)).IsRadical := by
  have he : badIdeal.map (specialize 0 a) =
      Ideal.span ({Polynomial.X + Polynomial.C (a 1), Polynomial.X^2} : Set ℂ[X]) := by
    rw [badIdeal,Ideal.map_span,Set.image_pair]
    simp [specialize]
  rw [he]
  by_cases ha : a 1 = 0
  · have hSpan : Ideal.span ({Polynomial.X + Polynomial.C (a 1), Polynomial.X^2} : Set ℂ[X]) =
        Ideal.span ({Polynomial.X} : Set ℂ[X]) := by
      simp only [ha,map_zero,add_zero]
      exact Ideal.span_pair_eq_span_left_iff_dvd.mpr (dvd_pow_self _ (by decide))
    rw [hSpan]
    exact radical_x
  · let J := Ideal.span ({Polynomial.X + Polynomial.C (a 1), Polynomial.X^2} : Set ℂ[X])
    have hx : Polynomial.X + Polynomial.C (a 1) ∈ J := Ideal.subset_span (by simp)
    have hsq : Polynomial.X^2 ∈ J := Ideal.subset_span (by simp)
    have hc : Polynomial.C ((a 1)^2) ∈ J := by
      rw [map_pow,show Polynomial.C (a 1)^2 =
        (Polynomial.C (a 1)-Polynomial.X)*(Polynomial.X+Polynomial.C (a 1)) + Polynomial.X^2 by ring]
      exact J.add_mem (J.mul_mem_left _ hx) hsq
    have htop : J = ⊤ := Ideal.eq_top_of_isUnit_mem J hc (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (pow_ne_zero 2 ha)))
    change J.IsRadical
    rw [htop]
    intro p _
    simp

private theorem radical_specialize_one (a : Fin 2 → ℂ) :
    (badIdeal.map (specialize 1 a)).IsRadical := by
  have he : badIdeal.map (specialize 1 a) =
      Ideal.span ({Polynomial.C (a 0) + Polynomial.X, Polynomial.C (a 0)^2} : Set ℂ[X]) := by
    rw [badIdeal,Ideal.map_span,Set.image_pair]
    simp [specialize]
  rw [he]
  by_cases ha : a 0 = 0
  · simpa [ha,Ideal.span_insert_zero,Set.pair_comm] using radical_x
  · let J := Ideal.span ({Polynomial.C (a 0) + Polynomial.X, Polynomial.C (a 0)^2} : Set ℂ[X])
    have hc : Polynomial.C (a 0)^2 ∈ J := Ideal.subset_span (by simp)
    have hu : IsUnit (Polynomial.C (a 0) : ℂ[X]) :=
      Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha)
    have htop : J = ⊤ := Ideal.eq_top_of_isUnit_mem J hc (hu.pow _)
    change J.IsRadical
    rw [htop]
    intro p _
    simp

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_244114.main) := by
  intro h
  apply bad_not_radical
  apply h ℂ 2 (by decide) badIdeal
  intro i a
  fin_cases i
  · exact radical_specialize_zero a
  · exact radical_specialize_one a
