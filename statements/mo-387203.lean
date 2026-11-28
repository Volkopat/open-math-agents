import Mathlib

/-!
# Vector version of subset sum

Source: https://mathoverflow.net/questions/387203 (yupbank, CC BY-SA 4.0).
Credit: @connoranderson

An executable meet-in-the-middle test handles both allowed targets for signed integer
vectors, including a repeated vector if the input is presented as an indexed family.
The smaller half's sums are indexed in a balanced search tree. The other half
requires at most one lookup per sum. Complementation exchanges the two targets.
A single marker realizes a reduction from ordinary subset sum even for distinct
inputs. This last point makes precise the complexity observation in the source
comments. The meet-in-the-middle technique is due to Horowitz and Sahni.
-/

namespace OMA.S_mo_387203

abbrev Vec := ℤ × ℤ

def reaches {G : Type*} [AddMonoid G] (v : List G) (c : G) : Prop :=
  ∃ s : List G, s.Sublist v ∧ s.sum = c

def sums : List Vec → List Vec
  | [] => [0]
  | v :: vs => let ys := sums vs; ys ++ ys.map (v + ·)

def query (v : List Vec) (c : Vec) : Bool :=
  let k := v.length / 2
  let tree := Std.TreeSet.ofList (sums (v.take k)) lexOrd.compare
  (sums (v.drop k)).any (fun y => tree.contains (c-y))

def vert (v : List Vec) : Vec := (0, v.sum.2)
def horiz (v : List Vec) : Vec := (v.sum.1, 0)

def encode (v : List ℤ) (t : ℤ) : List Vec := (-t,1) :: v.map (fun x => (x,0))

theorem main :
    (∀ (v : List Vec) (c : Vec), query v c = true ↔ reaches v c) ∧
    (∀ v : List Vec, (sums (v.take (v.length/2))).length = 2^(v.length/2) ∧
      (sums (v.drop (v.length/2))).length = 2^(v.length-v.length/2)) ∧
    (∀ v : List Vec, reaches v (vert v) ↔ reaches v (horiz v)) ∧
    (∀ (v : List ℤ) (t : ℤ), (v.Nodup → (encode v t).Nodup) ∧
      (reaches v t ↔ reaches (encode v t) (vert (encode v t))) ∧
      (reaches v t ↔ reaches (encode v t) (horiz (encode v t)))) := by
  sorry

end OMA.S_mo_387203
