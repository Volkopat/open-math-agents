import FormalConjectures.Wikipedia.CongruentNumber
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Reduction of `CongruentNumber.Tunnell_odd`

Reduces the necessary direction of Tunnell's theorem for odd squarefree congruent numbers to
three independent classical theorems on the congruent-number elliptic curve
`E_n : y² = x³ - n² x` over `ℚ`:
1. `H1`: Torsion structure `E_n(ℚ)_tors = E_n(ℚ)[2]` (every torsion point satisfies `2 • P = 0`).
2. `H2`: Coates–Wiles theorem for the CM curve `E_n` (a point of infinite order forces any entire
   analytic continuation `L` of `E_n.LSeries` from `{Re s > 2}` to satisfy `L 1 = 0`).
3. `H3`: Tunnell's weight-3/2 special-value formula via Shimura–Waldspurger (existence of an entire
   continuation `L` of `E_n.LSeries` with `L 1 = K * (2 * |A n| - |B n|)²` for some `K ≠ 0`).

Inside `main`, we prove Conrad's Theorem 4.1 (rational right triangle of area `n` yields a
nonsingular rational point `P = (a(a+c)/2, a²(a+c)/2)` on `E_n` with `y ≠ 0`), deduce `2 • P ≠ 0`
in the elliptic-curve group law, combine `H1`–`H3` to get `(2 * |A n| - |B n|)² = 0`, and conclude
`2 * (A n).ncard = (B n).ncard`.

References:
- J. B. Tunnell, "A classical Diophantine problem and modular forms of weight 3/2",
  Invent. Math. 72 (1983), 323–334.
- J. Coates & A. Wiles, "On the conjecture of Birch and Swinnerton-Dyer",
  Invent. Math. 39 (1977), 223–251.
- K. Conrad, "The Congruent Number Problem", Theorem 4.1.

Thanks to @johndfrance (Conrad Theorem 4.1 Lean proof) and @MechaNuggan (torsion, LSeries
continuation, and signed-count analysis).
Credit: @tkaiman
-/

namespace OMA.R_CongruentNumber_Tunnell_odd_R1

open CongruentNumber

private lemma exists_rationalPoint_of_congruentNumber (n : ℕ) (hn : n ≠ 0)
    (h : congruentNumber n) :
    ∃ x y : ℚ, y ≠ 0 ∧ y ^ 2 = x ^ 3 - (n : ℚ) ^ 2 * x := by
  obtain ⟨a, b, c, htriangle, harea⟩ := h
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have ha : a ≠ 0 := by
    intro ha
    apply hnq
    simpa [ha] using harea
  have hb : b ≠ 0 := by
    intro hb
    apply hnq
    simpa [hb] using harea
  have hac : a + c ≠ 0 := by
    intro hac
    have hc : c = -a := by linarith
    have hbzero : b = 0 := by
      rw [hc] at htriangle
      nlinarith [sq_nonneg b]
    exact hb hbzero
  refine ⟨a * (a + c) / 2, a ^ 2 * (a + c) / 2, ?_, ?_⟩
  · exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 ha) hac) (by norm_num)
  · rw [harea]
    linear_combination (a ^ 3 * (a + c) / 8) * htriangle

/-- **Torsion of the congruent-number elliptic curve `E_n : y² = x³ - n² x`**:
for every nonzero natural number `n`, every torsion point of `E_n(ℚ)` has order dividing `2`
(`E_n(ℚ)_tors = E_n(ℚ)[2] ≅ ℤ/2ℤ × ℤ/2ℤ`). -/
def H1 : Prop :=
  ∀ (n : ℕ), n ≠ 0 →
    ∀ (P : (⟨0, 0, 0, -((n : ℚ) ^ 2), 0⟩ : WeierstrassCurve ℚ).toAffine.Point) (m : ℕ),
      0 < m → m • P = 0 → (2 : ℕ) • P = 0

/-- **Coates–Wiles theorem for the CM elliptic curve `E_n : y² = x³ - n² x`**:
if `E_n(ℚ)` contains a point of infinite order, then any entire analytic continuation `L : ℂ → ℂ`
of `E_n.LSeries` from `{s : ℂ | 2 < s.re}` vanishes at `s = 1`. -/
def H2 : Prop :=
  ∀ (n : ℕ), n ≠ 0 →
    ∀ (L : ℂ → ℂ), Differentiable ℂ L →
      (∀ s : ℂ, 2 < s.re → L s = (⟨0, 0, 0, -((n : ℚ) ^ 2), 0⟩ : WeierstrassCurve ℚ).LSeries s) →
      (∃ P : (⟨0, 0, 0, -((n : ℚ) ^ 2), 0⟩ : WeierstrassCurve ℚ).toAffine.Point,
        ∀ m : ℕ, 0 < m → m • P ≠ 0) →
      L 1 = 0

/-- **Tunnell's weight-3/2 special-value formula (odd squarefree case)**:
for every odd squarefree natural number `n`, the L-series of `E_n : y² = x³ - n² x` admits an
entire analytic continuation `L : ℂ → ℂ` whose central value satisfies
`L 1 = K * (2 * |A n| - |B n|)²` for some nonzero complex constant `K`. -/
def H3 : Prop :=
  ∀ (n : ℕ), Squarefree n → Odd n →
    ∃ (L : ℂ → ℂ) (K : ℂ),
      Differentiable ℂ L ∧
      (∀ s : ℂ, 2 < s.re → L s = (⟨0, 0, 0, -((n : ℚ) ^ 2), 0⟩ : WeierstrassCurve ℚ).LSeries s) ∧
      K ≠ 0 ∧
      L 1 = K * ((2 * (CongruentNumber.A n).ncard : ℂ) - (CongruentNumber.B n).ncard) ^ 2

theorem main : H1 → H2 → H3 → type_of% @CongruentNumber.Tunnell_odd := by
  intro h1 h2 h3 n hsqf hodd hcong
  have hn : n ≠ 0 := hsqf.ne_zero
  obtain ⟨x, y, hy, heq⟩ := exists_rationalPoint_of_congruentNumber n hn hcong
  let E : WeierstrassCurve ℚ := ⟨0, 0, 0, -((n : ℚ) ^ 2), 0⟩
  have hns : E.toAffine.Nonsingular x y := by
    rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff]
    refine ⟨?_, Or.inr ?_⟩
    · dsimp [E, WeierstrassCurve.toAffine]
      linarith
    · dsimp [E, WeierstrassCurve.toAffine]
      intro h2y
      apply hy
      linarith
  let P : E.toAffine.Point := WeierstrassCurve.Affine.Point.some x y hns
  have h2P : (2 : ℕ) • P ≠ 0 := by
    intro hzero
    rw [two_nsmul, add_eq_zero_iff_eq_neg] at hzero
    simp only [P, WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.some.injEq] at hzero
    have hyneg : y = -y := by
      simpa [E, WeierstrassCurve.Affine.negY] using hzero.2
    apply hy
    linarith
  have hinf : ∀ m : ℕ, 0 < m → m • P ≠ 0 := fun m hm hmp => h2P (h1 n hn P m hm hmp)
  obtain ⟨L, K, hLdiff, hLser, hKne, hL1⟩ := h3 n hsqf hodd
  have hLzero : L 1 = 0 := h2 n hn L hLdiff hLser ⟨P, hinf⟩
  rw [hLzero] at hL1
  have hsq : ((2 * (A n).ncard : ℂ) - (B n).ncard) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hL1.symm with hK0 | h0
    · exact (hKne hK0).elim
    · exact h0
  have hsub : (2 * (A n).ncard : ℂ) = (B n).ncard := sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  have hnat : ((2 * (A n).ncard : ℕ) : ℂ) = ((B n).ncard : ℂ) := by
    simpa [Nat.cast_mul] using hsub
  exact Nat.cast_injective hnat

end OMA.R_CongruentNumber_Tunnell_odd_R1
