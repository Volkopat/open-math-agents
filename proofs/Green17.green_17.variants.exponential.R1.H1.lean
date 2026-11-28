import OMAReductions.R_Green17_green_17_variants_exponential_R1
import Mathlib

/-! Product construction for restricted-progression-free sets in finite-vector-space blocks. -/

-- Step Green17.green_17.variants.exponential.R1.H1: hypothesis H1 of reduction Green17.green_17.variants.exponential.R1
-- Credit: @Ciphore

namespace Green17Product

open Green17

def emb {m n : ℕ} : (𝔽₃ m × 𝔽₃ n) → 𝔽₃ (m + n)
  | (a, b) => Fin.append a b

lemma emb_injective {m n : ℕ} : Function.Injective (@emb m n) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  congr 1
  · ext i
    have hh := congrFun h (Fin.castAdd n i)
    simpa [emb] using hh
  · ext j
    have hh := congrFun h (Fin.natAdd m j)
    simpa [emb] using hh

def left (m n : ℕ) (x : 𝔽₃ (m + n)) : 𝔽₃ m := fun i => x (Fin.castAdd n i)
def right (m n : ℕ) (x : 𝔽₃ (m + n)) : 𝔽₃ n := fun j => x (Fin.natAdd m j)

lemma left_emb (m n : ℕ) (a : 𝔽₃ m) (b : 𝔽₃ n) :
    left m n (emb (a, b)) = a := by
  ext i; simp [left, emb]

lemma right_emb (m n : ℕ) (a : 𝔽₃ m) (b : 𝔽₃ n) :
    right m n (emb (a, b)) = b := by
  ext j; simp [right, emb]

lemma mem_left {m n : ℕ} {A : Finset (𝔽₃ m)} {B : Finset (𝔽₃ n)}
    {x : 𝔽₃ (m + n)}
    (hx : x ∈ (A.product B).map ⟨emb, emb_injective⟩) :
    left m n x ∈ A := by
  rw [Finset.mem_map] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  rcases p with ⟨a, b⟩
  have hp2 := Finset.mem_product.mp hp
  change left m n (emb (a, b)) ∈ A
  rw [left_emb]
  exact hp2.1

lemma mem_right {m n : ℕ} {A : Finset (𝔽₃ m)} {B : Finset (𝔽₃ n)}
    {x : 𝔽₃ (m + n)}
    (hx : x ∈ (A.product B).map ⟨emb, emb_injective⟩) :
    right m n x ∈ B := by
  rw [Finset.mem_map] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  rcases p with ⟨a, b⟩
  have hp2 := Finset.mem_product.mp hp
  change right m n (emb (a, b)) ∈ B
  rw [right_emb]
  exact hp2.2

lemma proj_eq_zero {m n : ℕ} {x : 𝔽₃ (m + n)}
    (hl : left m n x = 0) (hr : right m n x = 0) : x = 0 := by
  ext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · have hh := congrFun hl i
    simpa [left] using hh
  · have hh := congrFun hr j
    simpa [right] using hh

theorem product_free (m n : ℕ) (A : Finset (𝔽₃ m)) (B : Finset (𝔽₃ n))
    (hA : ¬ HasRestrictedAP A) (hB : ¬ HasRestrictedAP B) :
    ∃ C : Finset (𝔽₃ (m + n)), C.card = A.card * B.card ∧ ¬ HasRestrictedAP C := by
  let C := (A.product B).map ⟨emb, emb_injective⟩
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    rw [Finset.card_map, Finset.card_product]
  · rintro ⟨x, d, hd0, hd01, hx, hxd, hx2d⟩
    have hleft01 : ∀ i, left m n d i = 0 ∨ left m n d i = 1 := fun i => hd01 _
    have hright01 : ∀ j, right m n d j = 0 ∨ right m n d j = 1 := fun j => hd01 _
    have hxA : left m n x ∈ A := mem_left hx
    have hxdA : left m n x + left m n d ∈ A := by
      have hh := mem_left hxd
      have e : left m n (x + d) = left m n x + left m n d := by ext i; rfl
      rw [e] at hh
      exact hh
    have hx2dA : left m n x + 2 • left m n d ∈ A := by
      have hh := mem_left hx2d
      have e : left m n (x + 2 • d) = left m n x + 2 • left m n d := by ext i; rfl
      rw [e] at hh
      exact hh
    have hxB : right m n x ∈ B := mem_right hx
    have hxdB : right m n x + right m n d ∈ B := by
      have hh := mem_right hxd
      have e : right m n (x + d) = right m n x + right m n d := by ext j; rfl
      rw [e] at hh
      exact hh
    have hx2dB : right m n x + 2 • right m n d ∈ B := by
      have hh := mem_right hx2d
      have e : right m n (x + 2 • d) = right m n x + 2 • right m n d := by ext j; rfl
      rw [e] at hh
      exact hh
    by_cases hl : left m n d = 0
    · have hr : right m n d ≠ 0 := fun hr => hd0 (proj_eq_zero hl hr)
      exact hB ⟨right m n x, right m n d, hr, hright01, hxB, hxdB, hx2dB⟩
    · exact hA ⟨left m n x, left m n d, hl, hleft01, hxA, hxdA, hx2dA⟩

end Green17Product

theorem OMA.solution : OMA.R_Green17_green_17_variants_exponential_R1.H1 :=
  Green17Product.product_free
