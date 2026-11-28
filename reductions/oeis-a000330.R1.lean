import OMAStatements.S_oeis_a000330
import Mathlib

/-! Separate local solubility from the height of integral representatives.
The first step rules out every finite congruence obstruction. The second is
a uniform bound, depending on the order and target, for the minimum height
of a triple whenever a congruence is soluble. A single large enough modulus
then forces equality inside that fixed box. -/
namespace OMA.R_oeis_a000330_R1
open OMA.S_oeis_a000330 Finset

/-- Local representation at every positive modulus. -/
def H1 : Prop := ∀ (r : ℕ), 3 ≤ r → ∀ (z : ℤ) (m : ℕ), 0 < m →
  ∃ a b c : ℤ, z ≡ generalizedPolygonalPyramidal r a + generalizedPolygonalPyramidal r b +
    generalizedPolygonalPyramidal r c [ZMOD (m : ℤ)]

/-- Uniform height bound for representatives of soluble congruences.
The bound may depend on the target and order. -/
def H2 : Prop := ∀ (r : ℕ), 3 ≤ r → ∀ z : ℤ, ∃ B : ℕ, ∀ m : ℕ, 0 < m →
  (∃ a b c : ℤ, z ≡ generalizedPolygonalPyramidal r a + generalizedPolygonalPyramidal r b +
    generalizedPolygonalPyramidal r c [ZMOD (m : ℤ)]) →
  ∃ a b c : ℤ, a ∈ Icc (-(B:ℤ)) B ∧ b ∈ Icc (-(B:ℤ)) B ∧ c ∈ Icc (-(B:ℤ)) B ∧
    z ≡ generalizedPolygonalPyramidal r a + generalizedPolygonalPyramidal r b +
      generalizedPolygonalPyramidal r c [ZMOD (m : ℤ)]

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a000330.main := by
  classical
  intro localSol height r hr z
  obtain ⟨B,hB⟩ := height r hr z
  let box := Icc (-(B:ℤ)) B
  let gap (a b c : ℤ) := generalizedPolygonalPyramidal r a + generalizedPolygonalPyramidal r b +
    generalizedPolygonalPyramidal r c - z
  let upper := box.sup (fun a => box.sup (fun b => box.sup (fun c => (gap a b c).natAbs)))
  obtain ⟨a,b,c,ha,hb,hc,congr⟩ := hB (upper+1) (by omega) (localSol r hr z _ (by omega))
  have bound : (gap a b c).natAbs ≤ upper :=
    (le_sup (s:=box) (f:=fun c => (gap a b c).natAbs) hc).trans
      ((le_sup (s:=box) (f:=fun b => box.sup (fun c => (gap a b c).natAbs)) hb).trans
       (le_sup (s:=box) (f:=fun a => box.sup (fun b => box.sup (fun c => (gap a b c).natAbs))) ha))
  refine ⟨a,b,c,?_⟩
  by_contra bad
  have nz : gap a b c ≠ 0 := by dsimp [gap]; omega
  have divisible : ((upper+1 : ℕ) : ℤ) ∣ gap a b c := congr.dvd
  have large : upper+1 ≤ (gap a b c).natAbs := Int.natAbs_le_of_dvd_ne_zero divisible nz
  exact (Nat.not_succ_le_self upper) (large.trans bound)
end OMA.R_oeis_a000330_R1
