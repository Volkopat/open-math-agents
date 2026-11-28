import Mathlib

/-!
# The determinant of Trummer's matrix

Source: Jeannette, https://mathoverflow.net/questions/262273 (CC BY-SA 3.0).
Credit: @connoranderson.

For distinct complex points the determinant is the sum, over perfect
matchings, of the product of reciprocal squared differences on each edge.
The matching type chooses the partner of the least remaining index, so
each unoriented matching occurs once. The odd determinant vanishes.
For the unit-circle case asked about in the source, every even determinant
is nonzero.
-/

namespace OMA.S_mo_262273

/-- Choose the partner of the first remaining vertex, then pair the rest. -/
def Pairing : ℕ → Type
  | 0 => Unit
  | 1 => Empty
  | n+2 => Fin (n+1) × Pairing n

instance pairingFintype : (n : ℕ) → Fintype (Pairing n)
  | 0 => inferInstanceAs (Fintype Unit)
  | 1 => inferInstanceAs (Fintype Empty)
  | n+2 => @instFintypeProd (Fin (n+1)) (Pairing n) _ (pairingFintype n)

/-- Product of reciprocal squared differences over the edges of a matching. -/
noncomputable def pairWeight : (n : ℕ) → (Fin n → ℂ) → Pairing n → ℂ
  | 0, _, _ => 1
  | 1, _, p => nomatch p
  | n+2, z, (j,p) => ((z 0 - z j.succ)⁻¹)^2 *
      pairWeight n (fun i => z (j.succAbove i).succ) p

/-- Complex inversion sends zero to zero, giving the stated zero diagonal. -/
noncomputable def trummer {n : ℕ} (z : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of (fun i j => (z i - z j)⁻¹)

theorem main :
    (∀ (n : ℕ) (z : Fin n → ℂ), Function.Injective z →
      (trummer z).det = ∑ p : Pairing n, pairWeight n z p) ∧
    (∀ (k : ℕ) (z : Fin (2*k+1) → ℂ), Function.Injective z → (trummer z).det = 0) ∧
    (∀ (k : ℕ) (z : Fin (2*k) → ℂ), Function.Injective z →
      (∀ i, ‖z i‖=1) → (trummer z).det ≠ 0) := by
  sorry

end OMA.S_mo_262273
