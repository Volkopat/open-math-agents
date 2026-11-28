import Mathlib

/-!
# Entrywise bounds for the pseudoinverse of a graph Laplacian

Source: sd24, https://mathoverflow.net/questions/463379 (CC BY-SA 4.0).
Credit: @connoranderson.

There are N=m+1 vertices. Positive weight on every nontrivial cut expresses
connectivity. The centering matrix J has every entry equal to 1/N, and
green is the Moore-Penrose inverse (L+J)⁻¹-J from the question.

For cuts of size k let c(k)>0 be any lower bound on their total weights.
In a decreasing rearrangement of a Green column, summing its equations on
the first k vertices bounds the next potential difference by
(N-k)/(N c(k)). Summing the differences gives separate upper and lower
entry bounds. At constant c=1 the largest possible entry is
(N-1)(2N-1)/(6N) and the smallest is -(N²-1)/(6N). A single endpoint
column of the unit path attains both. The spectral estimate improves
the source bound 1/λ₂ by the factor (N-1)/N for every connected graph.
-/

namespace OMA.S_mo_463379
open Matrix Finset
abbrev V (m : ℕ) := Fin (m+1)
abbrev M (m : ℕ) := Matrix (V m) (V m) ℝ
def cut {m : ℕ} (w : M m) (S : Finset (V m)) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ univ \ S,w i j
def network {m : ℕ} (w : M m) : Prop :=
  (∀ i j,w i j=w j i) ∧ (∀ i j,0≤w i j) ∧
    ∀ S : Finset (V m), S.Nonempty → S≠univ → 0<cut w S
def profile {m : ℕ} (w : M m) (c : Fin m → ℝ) : Prop :=
  ∀ t, 0<c t ∧ ∀ S : Finset (V m), S.card=t.val+1 → c t≤cut w S
def greenColumn {m : ℕ} (w : M m) (s : V m) (x : V m → ℝ) : Prop :=
  (∑ i,x i)=0 ∧ ∀ i, (∑ j,w i j*(x i-x j))=(if i=s then 1 else 0)-(m+1:ℝ)⁻¹
noncomputable def lap {m : ℕ} (w : M m) : M m := diagonal (fun i => ∑ j,w i j) - w
noncomputable def J (m : ℕ) : M m := fun _ _ => (m+1:ℝ)⁻¹
noncomputable def green {m : ℕ} (w : M m) : M m := (lap w+J m)⁻¹-J m
noncomputable def upper {m : ℕ} (c : Fin m → ℝ) : ℝ :=
  (∑ t : Fin m, ((m:ℝ)-t.val)^2/c t)/(m+1:ℝ)^2
noncomputable def lowerMag {m : ℕ} (c : Fin m → ℝ) : ℝ :=
  (∑ t : Fin m, ((t.val:ℝ)+1)*((m:ℝ)-t.val)/c t)/(m+1:ℝ)^2
def pathWeight (m : ℕ) : M m := fun i j => if i.val+1=j.val ∨ j.val+1=i.val then 1 else 0
def spectralLower {m : ℕ} (w : M m) (l : ℝ) : Prop := ∀ x : V m → ℝ, (∑ i,x i)=0 →
  l*(∑ i,x i^2) ≤ ∑ i,x i*(∑ j,w i j*(x i-x j))

theorem main :
    (∀ (m : ℕ) (w : M m), network w →
      ((lap w)*(green w)*(lap w)=lap w ∧ (green w)*(lap w)*(green w)=green w ∧
        ((lap w)*(green w)).IsSymm ∧ ((green w)*(lap w)).IsSymm) ∧
      (∀ c : Fin m → ℝ, profile w c → ∀ i j, -lowerMag c ≤ green w i j ∧ green w i j ≤ upper c) ∧
      (∀ l : ℝ, 0<l → spectralLower w l → ∀ i j, |green w i j| ≤ (m:ℝ)/((m+1)*l))) ∧
    (∀ (m : ℕ) (a : ℝ), 0<a →
      upper (fun _ : Fin m => a) = (m:ℝ)*(2*m+1)/(6*(m+1)*a) ∧
      lowerMag (fun _ : Fin m => a) = (m:ℝ)*(m+2)/(6*(m+1)*a)) ∧
    (∀ m : ℕ, network (pathWeight m) ∧ profile (pathWeight m) (fun _ => 1) ∧
      green (pathWeight m) 0 0=upper (fun _ : Fin m => 1) ∧
      green (pathWeight m) (Fin.last m) 0= -lowerMag (fun _ : Fin m => 1)) := by
  sorry
end OMA.S_mo_463379
