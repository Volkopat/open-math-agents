import Mathlib

/-!
# OEIS A209861

Row k has inputs 2^k+x, 0 ≤ x < 2^k. A209642 encodes each of their
bits in order from least to most significant. At stage i the current
code has 2i bits. On a zero input bit its numerical update is 4s+1
(append 01), and on a one it is 2(s+4^i) (prepend 1 and append 0).
The fixed most significant one supplies the outer 1 and 0. The codes
in row k therefore have 2k+2 bits with leading one. Their ranks in the
increasing list A209641 are their lexicographic ranks in that row
plus the preceding 2^k entries, including the initial code for zero.

A054429 reverses each row by sending offset x to 2^k-1-x. The asserted
commutation with A209861 says that the two output indices add to the
sum of the row's endpoints. At the additional index zero both maps fix
zero.

Sources: https://oeis.org/A209861 and https://oeis.org/A209642
-/

namespace OMA.S_oeis_a209861

def putBit (s : List Bool) (b : Bool) : List Bool :=
  if b then true::(s++[false]) else s++[false,true]

def treeCode (w : List Bool) : List Bool := true::(w.foldl putBit [] ++ [false])

def bits {k : ℕ} (x : Fin (2^k)) : Fin k → Bool := fun i => x.val.testBit i.val

def rowRank {k : ℕ} (f : Fin k → Bool) : ℕ :=
  (Finset.univ.filter (fun u : Fin k → Bool => treeCode (List.ofFn u) < treeCode (List.ofFn f))).card

def output {k : ℕ} (x : Fin (2^k)) := 2^k+rowRank (bits x)

def reversed {k : ℕ} (x : Fin (2^k)) : Fin (2^k) := ⟨2^k-(x.val+1),by have := x.isLt; omega⟩

theorem main : ∀ k : ℕ, ∀ x : Fin (2^k),
    output x+output (reversed x) = 2^k+(2^(k+1)-1) := by
  sorry

end OMA.S_oeis_a209861
