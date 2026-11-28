import Mathlib

/-!
# There is no prime functional digraph

Source: https://arxiv.org/abs/2509.19940 (Adrien Richard, "There is no prime functional digraph:
Seifert's proof revisited", 2025)
Credit: Sudharsan Rajendiran

A functional digraph is a finite digraph in which each vertex has a unique out-neighbor.
Considered up to isomorphism, functional digraphs carry a (direct) product. A functional digraph
`X` divides a functional digraph `A` if there is a functional digraph `Y` with `XY ≅ A`. The
digraph `X` is prime if it is not the identity for the product and, for all functional digraphs
`A` and `B`, `X ∣ AB` implies `X ∣ A` or `X ∣ B`. Porreca asked whether prime functional digraphs
exist and conjectured that they do not. This was proved by Seifert (1971); the paper gives a
self-contained proof. We state the theorem: no functional digraph is prime.

Conventions:
- A functional digraph on a finite vertex type `V` is a map `f : V → V` (`f v` is the unique
  out-neighbor of `v`; loops are allowed).
- The product of `f : V → V` and `g : W → W` is `Prod.map f g` on `V × W`, the direct (tensor)
  product of digraphs: `(v, w) → (f v, g w)`.
- An isomorphism `f ≅ g` is a bijection `e : V ≃ W` with `e (f v) = g (e v)` for all `v`.
- The identity for the product is the digraph with one vertex and a loop, `id : Unit → Unit`.
- Up to isomorphism every functional digraph has vertex type `Fin n` for some `n`, so the
  digraphs `Y`, `A`, `B` are quantified over maps `Fin n → Fin n`.
- `X` is required to have at least one vertex. The empty digraph is the zero of the product
  (`X · ∅ ≅ ∅`), and it satisfies the divisibility condition trivially, like `0` in a ring; it is
  not a prime in the intended sense.
-/

namespace OMA.S_arxiv_2509_19940

/-- `f ≅ g`: an isomorphism of functional digraphs. -/
def Iso {V W : Type} (f : V → V) (g : W → W) : Prop :=
  ∃ e : V ≃ W, ∀ v, e (f v) = g (e v)

/-- `X ∣ A`: there is a functional digraph `Y` with `X Y ≅ A`. -/
def Divides {V W : Type} (x : V → V) (a : W → W) : Prop :=
  ∃ (n : ℕ) (y : Fin n → Fin n), Iso (Prod.map x y) a

/-- `X` is prime: it is not the identity for the product, and whenever it divides a product
`A B` it divides `A` or `B`. -/
def IsPrime {V : Type} (x : V → V) : Prop :=
  ¬ Iso x (id : Unit → Unit) ∧
    ∀ (n m : ℕ) (a : Fin n → Fin n) (b : Fin m → Fin m),
      Divides x (Prod.map a b) → Divides x a ∨ Divides x b

/-- There is no prime functional digraph (Seifert 1971; Richard 2025). -/
theorem main : ∀ (k : ℕ) (x : Fin k → Fin k), 0 < k → ¬ IsPrime x := by
  sorry

end OMA.S_arxiv_2509_19940
