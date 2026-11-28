import Mathlib

namespace OMA.S_opg_mso_alternation_hierarchy_over_pictures

abbrev Pixel (side : ℕ) := Fin side × Fin side
abbrev Picture (side colors : ℕ) := Pixel side → Fin colors

inductive PixelRelation (colors marks : ℕ) : ℕ → Type
  | horizontal : PixelRelation colors marks 2
  | vertical : PixelRelation colors marks 2
  | color (c : Fin colors) : PixelRelation colors marks 1
  | mark (i : Fin marks) : PixelRelation colors marks 1

abbrev pixelLanguage (colors marks : ℕ) : FirstOrder.Language where
  Functions := fun _ => Empty
  Relations := PixelRelation colors marks

/-- Pixels have their letter and the two directed successor relations.
Each mark interprets a quantified monadic predicate in the first-order body. -/
abbrev pixelStructure {side colors marks : ℕ} (P : Picture side colors)
    (marking : Fin marks → Set (Pixel side)) :
    (pixelLanguage colors marks).Structure (Pixel side) where
  funMap := fun symbol => nomatch symbol
  RelMap := fun rel =>
    match rel with
    | .horizontal => fun x => (x 0).1 = (x 1).1 ∧ (x 0).2.val + 1 = (x 1).2.val
    | .vertical => fun x => (x 0).2 = (x 1).2 ∧ (x 0).1.val + 1 = (x 1).1.val
    | .color c => fun x => P (x 0) = c
    | .mark i => fun x => x 0 ∈ marking i

/-- Interpret each block as a tuple of subsets of the pixel domain.
Empty blocks allow padding to a fixed level without changing truth. -/
def realizePrefix {α : Type} (existential : Bool) :
    (widths : List ℕ) → ((Fin widths.sum → Set α) → Prop) → Prop
  | [], body => body Fin.elim0
  | width :: tail, body =>
      let next (sets : Fin width → Set α) : Prop :=
        realizePrefix (!existential) tail (fun rest => body (Fin.addCases sets rest))
      if existential then ∃ sets, next sets else ∀ sets, next sets

/-- An existential-first monadic prefix with k alternating blocks and a first-order body. -/
structure SigmaSentence (colors k : ℕ) where
  widths : List ℕ
  blockCount : widths.length = k
  matrix : (pixelLanguage colors widths.sum).Sentence

def SigmaSentence.Holds {colors k side : ℕ} (φ : SigmaSentence colors k)
    (P : Picture side colors) : Prop :=
  realizePrefix true φ.widths fun marking =>
    letI := pixelStructure P marking
    φ.matrix.Realize (Pixel side)

/-- The MSO quantifier alternation hierarchy over nonempty square pictures is strict. -/
theorem main :
    ∀ k : ℕ, ∃ colors : ℕ, 0 < colors ∧
      ∃ upper : SigmaSentence colors (k + 1), ∀ lower : SigmaSentence colors k,
        ∃ side : ℕ, 0 < side ∧ ∃ P : Picture side colors,
          ¬ (upper.Holds P ↔ lower.Holds P) := by
  sorry

end OMA.S_opg_mso_alternation_hierarchy_over_pictures
