import Mathlib

/-!
# A two-parameter value formula for two inverse quadratic forms

Source: Drew Brady, https://mathoverflow.net/questions/476806 (CC BY-SA 4.0).
Credit: @connoranderson. The answer by loup blanc derives the interior
stationarity conditions and examines the optimization in dimension two.

For positive definite P,Q and a common test vector v of any dimension n,
the supremum with a unit trace budget equals the maximum of an explicit
function on a fixed planar disk. With H = [[a,b],[b,1-a]], K = I ⊗ H,
S the inverse of the block diagonal matrix with blocks P and Q, and
w the vector with both column slices equal to v, that function is
wᵀ S(K+S)⁻¹ K w. The inverse in this formula exists on the entire
closed disk. The two algebraic conditions in optimality identify precisely the maximizing
points, including on the boundary. Every such point gives the exact
value of the original supremum. The final conclusion gives a strict-threshold
test using the positive definite two-dimensional budgets.
-/
namespace OMA.S_mo_476806
open Matrix Finset
abbrev Sq (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev Vec (n : ℕ) := Fin n → ℝ

noncomputable def quad {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  x ⬝ᵥ (A *ᵥ x)

noncomputable def objective {n : ℕ} (P Q X : Sq n) (v : Vec n) : ℝ :=
  quad (P+X⁻¹)⁻¹ v + quad (Q+X⁻¹)⁻¹ v

noncomputable def small (a b : ℝ) : Sq 2 := !![a,b;b,1-a]

/-- The two diagonal n-by-n blocks are P and Q. The other term is
the tensor product of the n-dimensional identity and the inverse budget. -/
noncomputable def reducedMatrix {n : ℕ} (P Q : Sq n) (H : Sq 2) :
    Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ :=
  blockDiagonal ![P,Q] + Matrix.of (fun i j => if i.1 = j.1 then H⁻¹ i.2 j.2 else 0)

noncomputable def reduced {n : ℕ} (P Q : Sq n) (v : Vec n) (a b : ℝ) : ℝ :=
  quad (reducedMatrix P Q (small a b))⁻¹ (fun i => v i.1)

noncomputable def lift2 (n : ℕ) (H : Sq 2) :
    Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ :=
  Matrix.of (fun i j => if i.1 = j.1 then H i.2 j.2 else 0)

/-- A formula continuous through the boundary of the parameter disk. -/
noncomputable def diskValue {n : ℕ} (P Q : Sq n) (v : Vec n) (a b : ℝ) : ℝ :=
  let S := (blockDiagonal ![P,Q])⁻¹
  let K := lift2 n (small a b)
  quad (S*(K+S)⁻¹*K) (fun i => v i.1)

def disk : Set (ℝ × ℝ) := {z | (z.1-1/2)^2 + z.2^2 ≤ 1/4}

noncomputable def response {n : ℕ} (P Q : Sq n) (v : Vec n) (z : ℝ × ℝ) :
    Fin n × Fin 2 → ℝ :=
  let S := (blockDiagonal ![P,Q])⁻¹
  (lift2 n (small z.1 z.2) + S)⁻¹ *ᵥ (S *ᵥ (fun i => v i.1))

noncomputable def score {n : ℕ} (g : Fin n × Fin 2 → ℝ) : ℝ × ℝ :=
  (∑ i, ((g (i,0))^2-(g (i,1))^2), 2*∑ i, g (i,0)*g (i,1))

/-- The first-order conditions after eliminating the optimization variables
apart from the two entries a,b. All quantities are rational in the input. -/
def optimality (z d : ℝ × ℝ) : Prop :=
  0 ≤ (z.1-1/2)*d.1 + z.2*d.2 ∧
  4*((z.1-1/2)*d.1 + z.2*d.2)^2 = d.1^2+d.2^2

theorem main : ∀ {n : ℕ}, 0 < n → ∀ (P Q : Sq n) (v : Vec n), P.PosDef → Q.PosDef →
    (∃ z ∈ disk, optimality z (score (response P Q v z))) ∧
    (∀ z ∈ disk, optimality z (score (response P Q v z)) ↔
      sSup {y | ∃ X : Sq n, X.PosDef ∧ X.trace ≤ 1 ∧ y = objective P Q X v} =
        diskValue P Q v z.1 z.2) ∧
    (∀ t : ℝ, (∃ X : Sq n, X.PosDef ∧ X.trace ≤ 1 ∧ t < objective P Q X v) ↔
      ∃ a b : ℝ, 0 < a ∧ b^2 < a*(1-a) ∧ t < reduced P Q v a b) := by
  sorry

end OMA.S_mo_476806
