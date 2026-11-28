import Mathlib

/-!
# A368096: column `k = 2` of the triangle of non-isomorphic set-systems

Source: https://oeis.org/A368096
Credit: @avivorly

A368096 (Gus Wiseman, Dec 2023) is the triangle read by rows where `T(n,k)` is the number of non-isomorphic
set-systems of length `k` and weight `n`. A set-system is a finite set of finite nonempty sets; its length is the
number of its blocks (sets) and its weight is the sum of the sizes of its blocks.

Conjecture (in the entry): Column k = 2 is A101881.

A101881: Write two numbers, skip one, write two, skip two, write two, skip three ... and so on.
That is `1, 2, (skip 3), 4, 5, (skip 6, 7), 8, 9, (skip 10, 11, 12), 13, 14, ...`.

Conventions:
- Offsets: A368096 has offset 0 (rows `n = 0, 1, 2, ...`, row `n` holding `T(n,0), ..., T(n,n)`). Its example
  triangle gives column `k = 2` as `T(n,2) = 1, 2, 4, 5, 8, 9, 13, 14, 19` for `n = 2, ..., 10` (and `T(1,2) = 0`,
  since two distinct nonempty blocks have weight at least 2). A101881 has offset 0 and starts `1, 2, 4, 5, 8, ...`.
  So the conjecture reads `T(n,2) = A101881(n - 2)` for every `n ≥ 2`.
- Vertices: a set-system of weight `n` has at most `n` vertices, so every such system is isomorphic to one whose
  vertices lie in `Fin n`. Two set-systems on `Fin n` are isomorphic (a bijection between their vertex sets, the
  unions of their blocks, mapping the blocks of one onto the blocks of the other) iff some permutation of `Fin n`
  maps one onto the other: extend the bijection by any bijection between the complements, which have the same size.
  So `T n k` is the number of orbits of `Equiv.Perm (Fin n)` acting on the set-systems on `Fin n` of length `k` and
  weight `n`.
- `orb n S` is the orbit of `S`, the finset of all images of `S` under permutations of `Fin n`; `T n k` counts the
  distinct orbits, that is, the isomorphism classes.
- A101881 from its name: the `t`-th written pair (counting from `t = 0`) starts at `st t`, with `st 0 = 1` and
  `st (t + 1) = st t + t + 3` (the pair, then `t + 1` skipped numbers), and `A101881 n = st (n / 2) + n % 2`.
-/

namespace OMA.S_oeis_a368096

/-- `S` is a set-system on the vertex set `Fin n` of length `k` and weight `n`: its blocks are nonempty, there are
`k` of them, and their sizes sum to `n`. -/
abbrev IsSys (n k : ℕ) (S : Finset (Finset (Fin n))) : Prop :=
  (∀ s ∈ S, s.Nonempty) ∧ S.card = k ∧ ∑ s ∈ S, s.card = n

/-- The isomorphism class (orbit) of `S`: all images of `S` under permutations of `Fin n`. -/
def orb (n : ℕ) (S : Finset (Finset (Fin n))) : Finset (Finset (Finset (Fin n))) :=
  Finset.univ.image (fun σ : Equiv.Perm (Fin n) => S.image (fun s => s.map σ.toEmbedding))

/-- `T n k`: the number of non-isomorphic set-systems of length `k` and weight `n`. -/
def T (n k : ℕ) : ℕ := ((Finset.univ.filter (IsSys n k)).image (orb n)).card

/-- Start of the `t`-th written pair of A101881: `1, 4, 8, 13, 19, ...`. -/
def st : ℕ → ℕ
  | 0 => 1
  | t + 1 => st t + t + 3

/-- A101881 (offset 0): `1, 2, 4, 5, 8, 9, 13, 14, 19, 20, ...`. -/
def A101881 (n : ℕ) : ℕ := st (n / 2) + n % 2

theorem main : ∀ n : ℕ, 2 ≤ n → T n 2 = A101881 (n - 2) := by
  sorry

end OMA.S_oeis_a368096
