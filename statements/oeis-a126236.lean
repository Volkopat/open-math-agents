import Mathlib

/-!
# A126236: Maximum length of a codeword in Huffman encoding of n symbols, where the k-th symbol has frequency k.

Source: https://oeis.org/a126236
Credit: @w601sxs

OEIS a126236 (offset 2): a(n) is the maximum length of a codeword in a Huffman encoding of n symbols, where the k-th
symbol has frequency k. Conjecture (OEIS, formula section): a(n) = floor(log_2(n)) + floor(log_2(2n/3)).

Conventions, following the source and Wikipedia (Huffman coding):
- Huffman's algorithm keeps a forest of weighted binary trees, starting from one leaf per symbol,
  and repeatedly removes two trees of smallest weight and replaces them by a new node having
  them as children, until one tree remains. The codeword of a symbol is the path from the root
  to its leaf, so its length is the depth of that leaf.
- The source does not fix how ties between equal weights are broken. We quantify over every
  tie-breaking rule: `HuffmanStep` may merge any two trees whose weights are both at most every
  other weight in the forest, and `IsHuffmanTree n T` says that some run of the algorithm on the
  weights 1, ..., n ends with the single tree T. The statement says that a Huffman tree exists and
  that EVERY Huffman tree satisfies the formula; in particular the sequence is well defined.
  (Checked by exhaustive search over all tie-breaks for 2 <= n <= 40.)
- The offset of the sequence is 2, hence the hypothesis 2 <= n. The floors and base-2 logarithms
  are those of the source, taken over the reals.
-/

namespace OMA.S_oeis_a126236

/-- A binary code tree whose leaves carry symbols (here: natural numbers). -/
inductive CodeTree
  | leaf (s : ℕ)
  | node (l r : CodeTree)

namespace CodeTree

/-- Total frequency of a tree, where symbol k has frequency k. -/
def weight : CodeTree → ℕ
  | leaf s => s
  | node l r => weight l + weight r

/-- Length of the longest codeword: the largest depth of a leaf. -/
def maxCodewordLength : CodeTree → ℕ
  | leaf _ => 0
  | node l r => max (maxCodewordLength l) (maxCodewordLength r) + 1

/-- Length of the shortest codeword: the smallest depth of a leaf. -/
def minCodewordLength : CodeTree → ℕ
  | leaf _ => 0
  | node l r => min (minCodewordLength l) (minCodewordLength r) + 1

end CodeTree

open CodeTree

/-- One step of Huffman's algorithm on a forest: two trees `a` and `b`, each of weight at most
the weight of every other tree in the forest (i.e. two trees of smallest weight, with any
tie-breaking), are replaced by the tree `node a b`. -/
inductive HuffmanStep : Multiset CodeTree → Multiset CodeTree → Prop
  | merge (F : Multiset CodeTree) (a b : CodeTree)
      (ha : ∀ t ∈ F, a.weight ≤ t.weight) (hb : ∀ t ∈ F, b.weight ≤ t.weight) :
      HuffmanStep (a ::ₘ b ::ₘ F) ({node a b} + F)

/-- The initial forest: one leaf for each symbol 1, ..., n (symbol k has frequency k). -/
def initialForest (n : ℕ) : Multiset CodeTree :=
  (Finset.Icc 1 n).val.map leaf

/-- `T` is the tree produced by some run of Huffman's algorithm on the symbols 1, ..., n. -/
def IsHuffmanTree (n : ℕ) (T : CodeTree) : Prop :=
  Relation.ReflTransGen HuffmanStep (initialForest n) {T}

theorem main :
    ∀ n : ℕ, 2 ≤ n →
      (∃ T : CodeTree, IsHuffmanTree n T) ∧
      ∀ T : CodeTree, IsHuffmanTree n T →
        ((T.maxCodewordLength : ℕ) : ℤ) = ⌊Real.logb 2 n⌋ + ⌊Real.logb 2 (2 * n / 3)⌋ := by
  sorry

end OMA.S_oeis_a126236
