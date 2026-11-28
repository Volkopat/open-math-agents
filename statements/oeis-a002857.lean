import Mathlib

namespace OMA.S_oeis_a002857

open scoped Classical

/-- Action of a variable permutation `σ ∈ S_n` on Boolean functions `(Fin n → Bool) → Bool`. -/
def permActBoolFn {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : (Fin n → Bool) → Bool) :
    (Fin n → Bool) → Bool :=
  fun v => f (v ∘ σ)

/-- Action of a point permutation `σ ∈ S_n` on families of subsets (hypergraphs) of `Fin n`. -/
def permActHypergraph {n : ℕ} (σ : Equiv.Perm (Fin n)) (H : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  H.image (fun s => s.map σ.toEmbedding)

/-- `S_n`-equivalence of Boolean functions of `n` variables. -/
def boolFnEquiv (n : ℕ) (f g : (Fin n → Bool) → Bool) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), permActBoolFn σ f = g

/-- `S_n`-equivalence of hypergraphs on `Fin n`. -/
def hypergraphEquiv (n : ℕ) (H₁ H₂ : Finset (Finset (Fin n))) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), permActHypergraph σ H₁ = H₂

/-- A Post function of `n` variables is an `S_n`-equivalence class of Boolean functions
preserving both `false` and `true` (`f(0,...,0) = false` and `f(1,...,1) = true`). -/
def IsPostBoolFn (n : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  f (fun _ => false) = false ∧ f (fun _ => true) = true

/-- A cover of `Fin n`: a family of nonempty subsets of `Fin n` whose union is `Fin n`. -/
def IsCover (n : ℕ) (H : Finset (Finset (Fin n))) : Prop :=
  ∅ ∉ H ∧ ∀ i : Fin n, ∃ s ∈ H, i ∈ s

/-- A proper cover of `Fin n`: a cover of `Fin n` that does not contain the full set `Finset.univ`. -/
def IsProperCover (n : ℕ) (H : Finset (Finset (Fin n))) : Prop :=
  IsCover n H ∧ Finset.univ ∉ H

/-- OEIS A002857(`n`): Number of Post functions of `n` variables
(`S_n`-equivalence classes of Boolean functions with `f(0,...,0) = false`, `f(1,...,1) = true`). -/
noncomputable def a002857 (n : ℕ) : ℕ :=
  Nat.card (Quot (fun x y : { f : (Fin n → Bool) → Bool // IsPostBoolFn n f } =>
    boolFnEquiv n x.val y.val))

/-- OEIS A055621(`n`): Number of covers of an unlabeled `n`-set (`S_n`-orbits of covers). -/
noncomputable def a055621 (n : ℕ) : ℕ :=
  Nat.card (Quot (fun x y : { H : Finset (Finset (Fin n)) // IsCover n H } =>
    hypergraphEquiv n x.val y.val))

/-- OEIS A055152(`n`): Number of proper covers of an unlabeled `n`-set (`S_n`-orbits of proper covers). -/
noncomputable def a055152 (n : ℕ) : ℕ :=
  Nat.card (Quot (fun x y : { H : Finset (Finset (Fin n)) // IsProperCover n H } =>
    hypergraphEquiv n x.val y.val))

/-- OEIS A002857 Conjecture (R. J. Mathar, Oct 14 2022):
For all `n ≥ 1`, `A002857(n) = A055621(n) - A055152(n)`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → a002857 n = a055621 n - a055152 n := by
  sorry

end OMA.S_oeis_a002857
