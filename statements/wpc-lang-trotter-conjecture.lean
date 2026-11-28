import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

namespace OMA.S_wpc_lang_trotter_conjecture

open Filter IsDedekindDomain NumberField
open scoped Topology

/-- The rational j-invariants of elliptic curves with complex multiplication. -/
def cmInvariants : Finset ℚ :=
  {0, 1728, -3375, 8000, -32768, 54000, 287496, -12288000, 16581375,
    -884736, -884736000, -147197952000, -262537412640768000}

abbrev FinitePlace := HeightOneSpectrum (𝓞 ℚ)

/-- The residue field size of a finite place of the rationals is the underlying prime. -/
noncomputable def residueSize (v : FinitePlace) : ℕ :=
  Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))

/-- The finite places of good reduction with the specified Frobenius trace. -/
def goodPlacesWithTrace (E : WeierstrassCurve ℚ) (r : ℤ) : Set FinitePlace :=
  {v | let R := v.adicCompletionIntegers ℚ
       letI W := (E.baseChange (v.adicCompletion ℚ)).minimal R
       W.HasGoodReduction R ∧
         (residueSize v : ℤ) + 1 - (Nat.card (W.reduction R).toAffine.Point : ℤ) = r}

abbrev GeometricPoints (E : WeierstrassCurve ℚ) :=
  (E.toAffine.baseChange (AlgebraicClosure ℚ)).Point

open Classical in
/-- The subgroup killed by multiplication by m. -/
noncomputable def torsion (E : WeierstrassCurve ℚ) (m : ℕ) :
    AddSubgroup (GeometricPoints E) :=
  (nsmulAddMonoidHom m : GeometricPoints E →+ GeometricPoints E).ker

open Classical in
/-- Action of an absolute Galois element on geometric points. -/
noncomputable def pointAction (E : WeierstrassCurve ℚ) (g : Field.absoluteGaloisGroup ℚ) :
    GeometricPoints E →+ GeometricPoints E :=
  let gAlg : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := g
  WeierstrassCurve.Affine.Point.map (W' := E.toAffine) gAlg.toAlgHom

open Classical in
/-- Restrict Galois conjugation to points killed by m. -/
noncomputable def torsionAction {E : WeierstrassCurve ℚ} {m : ℕ}
    (g : Field.absoluteGaloisGroup ℚ) (P : torsion E m) : torsion E m :=
  ⟨pointAction E g P.val, by
    change m • pointAction E g P.val = 0
    have hP : m • P.val = 0 := P.property
    rw [← map_nsmul, hP, map_zero]⟩

open Classical in
/-- Galois image on the m-torsion, in additive coordinates over ZMod m. -/
def galoisImage {E : WeierstrassCurve ℚ} {m : ℕ}
    (coordinates : torsion E m ≃+ (Fin 2 → ZMod m)) :
    Set (Matrix (Fin 2) (Fin 2) (ZMod m)) :=
  {M | ∃ g : Field.absoluteGaloisGroup ℚ,
    ∀ P : torsion E m, coordinates (torsionAction g P) = M.mulVec (coordinates P)}

open Classical in
/-- The normalized trace proportion in the finite Galois image at modulus m. -/
noncomputable def traceDensity {E : WeierstrassCurve ℚ} {m : ℕ}
    (coordinates : torsion E m ≃+ (Fin 2 → ZMod m)) (r : ℤ) : ℝ :=
  let image := galoisImage coordinates
  (m : ℝ) * ({M ∈ image | M.trace = (r : ZMod m)}.ncard : ℝ) / (image.ncard : ℝ)

open Classical in
/-- The fixed-trace Lang–Trotter conjecture for elliptic curves over the rationals
without complex multiplication, including finiteness when the constant vanishes. -/
theorem main :
    ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], E.j ∉ cmInvariants →
    ∀ r : ℤ,
      ∃ (coordinates : ∀ n : ℕ, torsion E n.factorial ≃+ (Fin 2 → ZMod n.factorial))
        (C : ℝ), 0 ≤ C ∧
        Tendsto (fun n : ℕ => (2 / Real.pi) * traceDensity (coordinates n) r)
          atTop (𝓝 C) ∧
        Tendsto (fun x : ℝ =>
          ({v ∈ goodPlacesWithTrace E r | (residueSize v : ℝ) ≤ x}.ncard : ℝ) *
            Real.log x / Real.sqrt x) atTop (𝓝 C) ∧
        (C = 0 → (goodPlacesWithTrace E r).Finite) := by
  sorry

end OMA.S_wpc_lang_trotter_conjecture
