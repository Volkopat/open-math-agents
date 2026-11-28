import Mathlib

/-!
# A globally convergent method for product-constrained matrix least squares

Source: Yin Mingzhou, https://mathoverflow.net/questions/355729 (CC BY-SA 4.0).
Credit: @connoranderson.

A family has m+1 square factors and the ordered product multiplies the
last factor on the left. Loss is the sum of the squared Frobenius
residuals. Invertibility of each Xᵢ gives compact feasible sublevels.
The result allows arbitrary Yᵢ, including the full-rank case requested.

Enumerate rational tuples of the first m factors, for example by increasing
numerator and denominator height. If the prefix product is nonsingular,
append its inverse to enforce the constraint exactly. Use identity factors
for singular prefixes. Keep the smallest of the losses inspected so far.
These values converge to the global minimum for any exhaustive enumeration,
and the corresponding best feasible tuples have a globally minimizing
subsequential limit. The method is exhaustive and gives no efficiency rate.
-/

namespace OMA.S_mo_355729
open Matrix
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev Family (m n : ℕ) := Fin (m+1) → Mat n
def orderedProduct {l n : ℕ} (Q : Fin l → Mat n) : Mat n := (List.ofFn Q).reverse.prod
def feasible {m n : ℕ} (Q : Family m n) : Prop := orderedProduct Q=1
noncomputable def loss {m n : ℕ} (X Y Q : Family m n) : ℝ :=
  ∑ k,∑ i,∑ j,((Q k*X k-Y k) i j)^2
abbrev RatPrefix (m n : ℕ) := Fin m → Matrix (Fin n) (Fin n) ℚ
def castPrefix {m n : ℕ} (q : RatPrefix m n) : Fin m → Mat n := fun k i j => (q k i j:ℝ)
noncomputable def completePrefix {m n : ℕ} (q : Fin m → Mat n) : Family m n :=
  if (orderedProduct q).det = 0 then fun _ => 1 else Fin.snoc q (orderedProduct q)⁻¹
noncomputable def candidate {m n : ℕ} (q : RatPrefix m n) : Family m n := completePrefix (castPrefix q)
noncomputable def bestThrough {m n : ℕ} (X Y : Family m n) (e : ℕ → RatPrefix m n) (N : ℕ) : ℝ :=
  ((Finset.range (N+1)).image (fun k => loss X Y (candidate (e k)))).min' (by simp)

open Filter Topology
theorem main :
    (∀ m n : ℕ, ∃ e : ℕ → RatPrefix m n, Function.Surjective e) ∧
    (∀ m n : ℕ, ∀ q : RatPrefix m n,feasible (candidate q)) ∧
    ∀ m n : ℕ, ∀ X Y : Family m n, (∀ k, IsUnit (X k)) →
      (∀ c : ℝ,IsCompact {Q | feasible Q ∧ loss X Y Q≤c}) ∧
      ∃ Z : Family m n, feasible Z ∧ (∀ W,feasible W → loss X Y Z ≤ loss X Y W) ∧
        ∀ e : ℕ → RatPrefix m n, Function.Surjective e →
          (∀ N,∃ k≤N,bestThrough X Y e N=loss X Y (candidate (e k))) ∧
          Tendsto (bestThrough X Y e) atTop (𝓝 (loss X Y Z)) ∧
          ∀ v : ℕ → ℕ, (∀ N,loss X Y (candidate (e (v N)))=bestThrough X Y e N) →
            ∃ W : Family m n, feasible W ∧ (∀ V,feasible V → loss X Y W ≤ loss X Y V) ∧
              ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun N => candidate (e (v (φ N)))) atTop (𝓝 W) := by
  sorry
end OMA.S_mo_355729
