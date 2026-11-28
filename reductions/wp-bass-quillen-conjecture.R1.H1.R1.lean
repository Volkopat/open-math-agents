import OMAReductions.R_wp_bass_quillen_conjecture_R1
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.RegularLocalRing.Defs

-- Reduction wp-bass-quillen-conjecture.R1.H1.R1 of Local Bass–Quillen conjecture
-- Credit: @tongenspace

/-!
# Split of the Local Bass–Quillen Conjecture into Equicharacteristic and Mixed Characteristic

Separates the local Bass–Quillen conjecture (`OMA.R_wp_bass_quillen_conjecture_R1.H1`) over a
regular local ring `R` into its two classical regimes:

* `H1`: **Equicharacteristic case** — `R` contains a field `K`. This is a known theorem due to
  Lindel (1981) and Popescu (1986), via Popescu's Néron desingularization theorem.
* `H2`: **Mixed-characteristic case** — some rational prime `p` lies in the maximal ideal of `R`
  and is nonzero in `R`. This is the genuinely open case of the Bass–Quillen conjecture in full
  generality (known in the unramified case by Popescu 1989 / Swan 1998, open in general for
  ramified regular local rings).
-/

namespace OMA.R_wp_bass_quillen_conjecture_R1_H1_R1

/-- Equicharacteristic Local Bass–Quillen (Lindel 1981, Popescu 1986): over any regular local ring
containing a field, every finitely generated projective module over `R[t₁, ..., tₙ]` is free. -/
def H1 : Prop :=
  ∀ (R : Type) [CommRing R] [IsRegularLocalRing R],
    (∃ (K : Type) (_ : Field K), Nonempty (K →+* R)) →
    ∀ (n : ℕ) (P : Type) [AddCommGroup P] [Module (MvPolynomial (Fin n) R) P]
      [Module.Finite (MvPolynomial (Fin n) R) P]
      [Module.Projective (MvPolynomial (Fin n) R) P],
      Module.Free (MvPolynomial (Fin n) R) P

/-- Mixed-characteristic Local Bass–Quillen (open in full generality): over any regular local ring
of mixed characteristic `(0, p)` (some prime `p` lies in the maximal ideal and is nonzero in `R`),
every finitely generated projective module over `R[t₁, ..., tₙ]` is free. -/
def H2 : Prop :=
  ∀ (R : Type) [CommRing R] [IsRegularLocalRing R],
    (∃ p : ℕ, Nat.Prime p ∧ (p : R) ∈ IsLocalRing.maximalIdeal R ∧ (p : R) ≠ 0) →
    ∀ (n : ℕ) (P : Type) [AddCommGroup P] [Module (MvPolynomial (Fin n) R) P]
      [Module.Finite (MvPolynomial (Fin n) R) P]
      [Module.Projective (MvPolynomial (Fin n) R) P],
      Module.Free (MvPolynomial (Fin n) R) P

lemma contains_field_or_mixed_char (R : Type) [CommRing R] [IsLocalRing R] :
    (∃ (K : Type) (_ : Field K), Nonempty (K →+* R)) ∨
    (∃ p : ℕ, Nat.Prime p ∧ (p : R) ∈ IsLocalRing.maximalIdeal R ∧ (p : R) ≠ 0) := by
  by_cases hfield : ∃ (K : Type) (_ : Field K), Nonempty (K →+* R)
  · exact Or.inl hfield
  · right
    have hex_prime : ∃ p : ℕ, Nat.Prime p ∧ (p : R) ∈ IsLocalRing.maximalIdeal R := by
      by_contra hno
      push Not at hno
      have hnat_unit : ∀ m : ℕ, m ≠ 0 → IsUnit (m : R) := by
        intro m
        induction m using Nat.strong_induction_on with
        | h m ih =>
          intro hm0
          by_cases hm1 : m = 1
          · subst hm1; simp
          · obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
            obtain ⟨k, rfl⟩ := hpm
            have hk0 : k ≠ 0 := by intro hk; subst hk; simp at hm0
            have hklt : k < p * k := lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hk0) hp.one_lt
            have hpu : IsUnit (p : R) := IsLocalRing.notMem_maximalIdeal.mp (hno p hp)
            have hku : IsUnit (k : R) := ih k hklt hk0
            rw [Nat.cast_mul]
            exact hpu.mul hku
      have hint_unit : ∀ z : nonZeroDivisors ℤ, IsUnit ((Int.castRingHom R) z.1) := by
        intro ⟨z, hz⟩
        have hz0 : z ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hz
        have habs0 : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz0
        have hu : IsUnit (z.natAbs : R) := hnat_unit z.natAbs habs0
        rcases Int.natAbs_eq z with h | h
        · have hcast : (z : R) = (z.natAbs : R) := by
            conv_lhs => rw [h]
            simp
          simpa [hcast] using hu
        · have hcast : (z : R) = - (z.natAbs : R) := by
            conv_lhs => rw [h]
            simp
          simpa [hcast] using hu.neg
      let φ : ℚ →+* R := IsLocalization.lift (M := nonZeroDivisors ℤ) (S := ℚ)
        (g := Int.castRingHom R) hint_unit
      exact hfield ⟨ℚ, inferInstance, ⟨φ⟩⟩
    obtain ⟨p, hp, hpm⟩ := hex_prime
    refine ⟨p, hp, hpm, ?_⟩
    intro hp0
    have _ : Fact p.Prime := ⟨hp⟩
    let qHom : (ℤ ⧸ Ideal.span {(p : ℤ)}) →+* R :=
      Ideal.Quotient.lift (Ideal.span {(p : ℤ)}) (Int.castRingHom R) fun a ha => by
        rw [Ideal.mem_span_singleton] at ha
        obtain ⟨k, rfl⟩ := ha
        simp [hp0]
    let φ : ZMod p →+* R := qHom.comp (Int.quotientSpanNatEquivZMod p).symm.toRingHom
    exact hfield ⟨ZMod p, inferInstance, ⟨φ⟩⟩

theorem main : H1 → H2 → OMA.R_wp_bass_quillen_conjecture_R1.H1 := by
  intro h1 h2 R _ _ n P _ _ _ _
  rcases contains_field_or_mixed_char R with hfield | hmixed
  · exact h1 R hfield n P
  · exact h2 R hmixed n P

end OMA.R_wp_bass_quillen_conjecture_R1_H1_R1
