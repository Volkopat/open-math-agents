import OMAReductions.R_Erdos20_erdos_20_R1_H2_R1_H1_R1_H1_R2

/-!
# Matrix rank bounds for four-site tensor restrictions

The tensor comparison arguments are from OpenAI, Euclidean geometry in the asymptotic spectrum of tensors,
openai/math at 3344da59991ed94f9ba711217b29c1d760badfa6. The coordinate to tensor-class adapter and
pinned-version compatibility fixes are adapted from TheWaler, open-math-agents PR 4572.
-/

/-
Brouwer and Kakutani fixed-point theorems, adapted from harfe/fixed-point-theorems-lean4,
commit 0684d5803ab318f7c02b0878928bc0cd0d655d9d.

Copyright (c) 2026 harfe

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
-/

section

open Classical

/-
The Cubical Sperner's Lemma.
We mostly follow Kuhn 1960 "Some Combinatorial Lemmas in Topology"
-/

structure SpernerCube where
  n : ℕ
  p : ℕ
  RL : (Fin n → Fin (p+1)) → ℕ
  rl_proper : ∀ (I: Fin n → Fin (p+1) ), RL I ≤ n ∧
      ∀ (k : Fin n), (I k = 0 → RL I ≠ k.1) ∧ (I k = p → RL I ≤ k.1)

namespace SpernerCube

def G (SC : SpernerCube) := Fin SC.n → Fin (SC.p+1)

instance Gfin (SC : SpernerCube): Fintype SC.G := by {
  exact Pi.instFintype
}

end SpernerCube

variable (SC : SpernerCube)
variable {n1 : ℕ}
variable {hn1 : n1 + 1 = SC.n}

def simplex (m:ℕ ) (I : Fin (m+1)→ SC.G) := Function.Injective I
    ∧ ∀ i < m, ∀ j : Fin SC.n, (I (Fin.ofNat _ i) j).1 ≤ (I (Fin.ofNat _ (i+1)) j).1
    ∧ (I (Fin.last m) j).1 ≤ (I 0 j).1 + 1

def complete_simplex (m:ℕ ) (I : Fin (m+1) → SC.G ) := simplex SC m I
    ∧ Set.range (fun (i:Fin (m+1))↦ SC.RL (I i)) = {j : ℕ | j ≤ m}

def is_face I J :=
    simplex SC n1 I ∧ simplex SC SC.n J ∧ Set.range I ⊆ Set.range J

def is_boundary_face I := ∃! J, @is_face SC n1 I J

def complete_boundary_face I := is_boundary_face SC I ∧ complete_simplex SC n1 I

def case_A (I : Fin (n1 +1) → SC.G) := ∃ j, ∀ k, I k j = 0

def case_B (I : Fin (n1 +1) → SC.G) := ∃ j, ∀ k, I k j = Fin.last SC.p

def case_C (I : Fin (n1 +1) → SC.G) :=
    ∃ j, ∃ (q : Fin (SC.p + 1)), (q ≠ 0 ∧ q ≠ Fin.last SC.p ) ∧ ∀ k, I k j = q

def case_D (I : Fin (n1 +1) → SC.G) := ∀ j, ∀ q, ∃ k,I k j ≠ q

lemma one_of_ABCD (I : Fin (n1 +1) → SC.G) :
    case_A SC I ∨ case_B SC I ∨ case_C SC I ∨ case_D SC I := by {
  by_cases h1 : case_D SC I
  exact Or.inr (Or.inr (Or.inr h1))
  unfold case_D at h1
  push Not at h1
  obtain ⟨j , ⟨ q, h2 ⟩⟩ := h1
  by_cases q0 : q = 0
  {
    apply Or.inl
    use j
    rwa [← q0]
  }
  by_cases qp : q = Fin.last SC.p
  {
    apply Or.inr (Or.inl _)
    use j
    intro k
    rwa [h2 k]
  }
  suffices h3 : case_C SC I by {
    simp only [h3, true_or, or_true]
  }
  use j, q
}

section simplex_properties

lemma monotone_1_of_simplex {m:ℕ } (I : Fin (m+1)→ SC.G) (hs : simplex SC m I) (i1 i2 : Fin (m+1))
    (h1 : i1 ≤ i2) : ∀ j, I i1 j ≤ I i2 j := by {
  intro j
  let f := fun i ↦ I i j
  have h2 := @Fin.monotone_iff_le_succ m _ _ f
  suffices h3 : Monotone f by exact (h3 h1)
  rw [h2]
  clear i1 i2 h1
  intro i1
  have h3 := (hs.2 i1.1 i1.2 j).1
  simp only [Fin.val_fin_le] at h3
  convert h3 <;> ext <;> simp [Fin.ofNat_eq_cast, Nat.mod_eq_of_lt]
}

lemma monotone_2_of_simplex {m:ℕ } (I : Fin (m+1)→ SC.G) (hs : simplex SC m I) (i1 i2 : Fin (m+1)) :
    i1 ≤ i2 ↔ ∀ j, I i1 j ≤ I i2 j := by {
  apply Iff.intro
  {
    intro h1 j
    apply monotone_1_of_simplex _ I hs i1 i2 h1
  }
  {
    intro h1
    by_contra h2
    have h3 : i1 ≠ i2 := ne_of_not_le h2
    apply h3
    apply hs.1
    apply funext
    intro j
    apply le_antisymm (h1 j)
    apply monotone_1_of_simplex _ _ hs i2 i1 (le_of_not_ge h2)
  }
}

lemma last_of_simplex {m: ℕ} I (hs : simplex SC m I) j :
    (I (Fin.last m) j).1 ≤ (I 0 j).1 + 1 := by {
  cases m
  simp only [Fin.last_zero, Fin.isValue, le_add_iff_nonneg_right, zero_le]
  rename_i m
  have h3 : 0 < m + 1 := by omega
  exact (hs.2 0 h3 j).2
}

lemma le_add_one_of_simplex {m: ℕ} I (hs : simplex SC m I) (i1 i2 : Fin (m+1)) j :
    (I i1 j).1 ≤ (I i2 j).1 + 1 := by {
  have h1 := last_of_simplex SC I hs j
  apply le_trans _ (le_trans h1 _)
  apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last i1)
  apply Nat.add_le_add_right
  apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le i2)
}

end simplex_properties

lemma p_ne_zero_of_cube {hn1 : n1 + 1 = SC.n}: Fin.last SC.p ≠ 0 := by {
  simp only [ne_eq, Fin.last_eq_zero_iff]
  intro h1
  let v : Fin SC.n → Fin (SC.p + 1) := fun _ ↦ 0
  have h3 : NeZero SC.n := by {
    rw [←hn1]
    exact instNeZeroNatHAdd_1
  }
  have h4 : v 0 = 0 := by {rfl}
  have h2 := (SC.rl_proper v).2 0
  simp only [Fin.val_zero, ne_eq, h1, Fin.val_eq_zero_iff, nonpos_iff_eq_zero] at h2
  exact h2.1 h4 (h2.2 h4)
}

section simplex_child

def insert_index (j : Fin (SC.n+1)) (a: Fin (n1 +1 )) : Fin (SC.n+1) :=
{ val := if a.val < j.val then a.val else a.val+1,
  isLt := by {
    by_cases hlt : a.val < j.val
    {
      simp only [hlt, ↓reduceIte]
      exact Nat.lt_trans hlt j.2
    }
    {
      simp only [hlt, ↓reduceIte, add_lt_add_iff_right]
      rw [← hn1]
      exact a.2
    }
} }

def delete_vertex (j: Fin (SC.n+1)) (I : Fin (SC.n+1)→ SC.G) : Fin (n1 + 1) → SC.G :=
  fun a ↦ I (@insert_index SC n1 hn1 j a)

lemma insert_index_ne j a : @insert_index SC n1 hn1 j a ≠ j := by {
  apply Fin.ne_of_val_ne
  unfold insert_index
  by_cases hlt : a.val < j.val
  {
    simp only [hlt, ↓reduceIte]
    omega
  }
  {
    simp only [hlt, ↓reduceIte, ne_eq]
    omega
  }
}

lemma almost_surjective_of_insert_index (j : Fin (SC.n+1)) (a : Fin (SC.n+1)) (h : a ≠ j)
    : ∃ k : Fin (n1 + 1) , a = @insert_index SC n1 hn1 j k := by {
  unfold insert_index
  by_cases hlt : a.1 < j.1
  {
    use (Fin.ofNat _ a.1)
    have h2 : a.1 = (Fin.ofNat (n1 + 1) a.1) := by {
      rw [Fin.ofNat_eq_cast, Fin.val_cast_of_lt]
      rw [hn1]
      apply lt_of_lt_of_le hlt
      exact Fin.is_le j
    }
    simp only [← h2, hlt]
    rfl
  }
  {
    have h2 : j.1 < a.1 := by {
      have := Fin.val_ne_of_ne (id (Ne.symm h))
      omega
    }
    let a1 := a.1 - 1
    have h3 : a1 + 1 = a.1 := by {
      show a.1 - 1 + 1 = a.1
      omega
    }
    let a1f := Fin.ofNat (n1 + 1) a1
    use a1f
    ext
    have h4 : a1 < n1 +1 := by {
      have h5 := a.2
      show a.1 - 1 < n1 + 1
      omega
    }
    have h6 : a1f.1 = a1 := by {
      unfold a1f
      simp only [Fin.ofNat_eq_cast, Fin.val_natCast, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
      exact h4
    }
    have h5 : ¬ (a1f < j.1) := by {
      simp only [not_lt, h6]
      show j.1 ≤ a.1 - 1
      omega
    }
    simp only [h5, ↓reduceIte]
    rw [← h3, h6]
  }
}

lemma insert_index_strict_mono j : StrictMono (@insert_index SC n1 hn1 j) := by {
  intro a b h1
  have h2 : a.1 < b.1 := by {exact h1}
  have h21 : a.1 < b.1 + 1 := by omega
  unfold insert_index
  by_cases h3 : a.1 < j.1
  {
    by_cases h4 : b.1 < j.1
    repeat {
      simp only [h3, ↓reduceIte, h4, Fin.mk_lt_mk, Fin.val_fin_lt, gt_iff_lt]
      assumption
    }
  }
  {
    by_cases h4 : b.1 < j.1
    {
      simp only [h3, ↓reduceIte, h4, Fin.mk_lt_mk, gt_iff_lt]
      omega
    }
    {
      simp only [h3, ↓reduceIte, h4, Fin.mk_lt_mk, gt_iff_lt]
      omega
    }
  }
}

lemma insert_index_inj j : Function.Injective (@insert_index SC n1 hn1 j) := by {
  apply StrictMono.injective
  apply insert_index_strict_mono
}

lemma delete_vertex_inj J {hs : simplex SC SC.n J} i1 i2
    (h1 : @delete_vertex SC n1 hn1 i1 J = @delete_vertex SC n1 hn1 i2 J ) : i1 = i2 := by {
  by_contra h2
  obtain ⟨k, h3 ⟩ := @almost_surjective_of_insert_index SC n1 hn1 i2 i1 h2
  apply @insert_index_ne SC n1 hn1 i1 k
  apply hs.1
  nth_rewrite 2 [h3]
  exact (congrFun h1) k
}

lemma delete_vertex_simplex J {hs : simplex SC SC.n J} i :
    simplex SC n1 (@delete_vertex SC n1 hn1 i J) := by {
  apply And.intro
  {
    intro k1 k2 h2
    apply insert_index_inj SC i
    apply hs.1 h2
  }
  {
    intro i2 hi2 j
    unfold delete_vertex
    apply And.intro
    {
      apply monotone_1_of_simplex SC J hs
      rw [StrictMono.le_iff_le]
      {
        simp only [Fin.ofNat_eq_cast]
        apply Fin.natCast_mono hi2
        exact Nat.le_add_right i2 1
      }
      apply insert_index_strict_mono
    }
    apply le_add_one_of_simplex SC J hs
  }
}

lemma delete_vertex_is_face J {hs : simplex SC SC.n J} i :
    is_face SC (@delete_vertex SC n1 hn1 i J) J := by {
  apply And.intro
  {
    apply delete_vertex_simplex
    exact hs
  }
  {
    apply And.intro hs
    intro c hc
    obtain ⟨ i2, hi2 ⟩ := hc
    use @insert_index SC n1 hn1 i i2
    exact hi2
  }
}

lemma is_id_of_strict_mono (m: ℕ ) (f : Fin m → Fin m) (hsm : StrictMono f)
    : ∀ k, f k = k := by {
  suffices h1 : ∀ (a : ℕ), ∀ k, k.1 < a → f k = k by {
    intro k
    exact h1 m k k.2
  }
  intro a
  induction' a with a ha
  {
    intro k h1
    omega
  }
  {
    have h1 : Function.Injective f := by {exact StrictMono.injective hsm}
    have h2 : Function.Surjective f := Finite.surjective_of_injective h1
    intro k hk
    have h3 j : j < k → f j = j := by {
      intro hj
      apply ha
      omega
    }
    by_cases h4 : f k < k
    apply h1 (h3 (f k) h4)
    simp only [not_lt] at h4
    apply le_antisymm _ h4
    obtain ⟨l, h9⟩ := h2 k
    suffices h8 : k ≤ l by {rwa [← hsm.le_iff_le, h9] at h8}
    by_contra! h6
    have h7 := h3 l h6
    rw [h9] at h7
    rw [h7] at h6
    exact (lt_self_iff_false l).mp h6
  }
}

lemma is_insert_index_of_strict_mono f (hsm : StrictMono f)
    : ∃ j, f = @insert_index SC n1 hn1 j := by {
  have h31 : Function.Injective f := by {exact hsm.injective}
  have hns : ∃ j, ∀ i, f i ≠ j := by {
    by_contra! h1
    have h2 : Function.Surjective f := by {exact h1 }
    have h5 : Function.Bijective f :=  And.intro h31 h2
    have h4 := Nat.card_eq_of_bijective f h5
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.add_right_cancel_iff] at h4
    rw [h4] at hn1
    simp only [Nat.add_eq_left, one_ne_zero] at hn1
  }
  obtain ⟨ j, hj⟩ := hns
  use j
  have h1 : ∀ k1, ∃ k2, f k1 = @insert_index SC n1 hn1 j k2 := by {
    intro k1
    apply almost_surjective_of_insert_index
    exact hj k1
  }
  obtain ⟨g, hg⟩ := axiomOfChoice h1
  have h2 : StrictMono g := by {
    intro k1 k2
    contrapose!
    intro h4
    rw [←hsm.le_iff_le, hg k1, hg k2]
    have h5 := @insert_index_strict_mono SC n1 hn1 j
    rw [h5.le_iff_le]
    exact h4
  }
  have h3 := is_id_of_strict_mono _ g h2
  ext1 k
  rw [hg k, h3 k]
}

lemma child_simplex_char (I : Fin (n1 +1) → SC.G) J {hs : simplex SC SC.n J}
    : is_face SC I J ↔ ∃ i, I = @delete_vertex SC n1 hn1 i J := by {
  apply Iff.intro
  {
    intro h1
    have h2 : ∃ (f : Fin (n1+1) → Fin (SC.n+1)), ∀ k, I k = J (f k) := by {
      have h2 := h1.2.2
      have h3 : ∀ k, ∃ j, I k = J j := by {
        intro k
        have h4 : I k ∈ Set.range I := by {
          exact Set.mem_range_self k
        }
        have h3 := h2 h4
        obtain ⟨j, hj⟩ := h2 h4
        use j
        exact hj.symm
      }
      apply axiom_of_choice h3
    }
    obtain ⟨f, hf ⟩ := h2
    have h31 : Function.Injective f := by {
      intro k1 k2 h2
      apply h1.1.1
      rw [hf k1, hf k2, h2]
    }
    have h3 : StrictMono f := by {
      apply Monotone.strictMono_of_injective _ h31
      intro k1 k2 h2
      rw [monotone_2_of_simplex SC J hs]
      rw [← hf k1, ← hf k2]
      rwa [←monotone_2_of_simplex SC I h1.1]
    }
    obtain ⟨j, hj⟩ := is_insert_index_of_strict_mono SC f h3
    use j
    ext k
    unfold delete_vertex
    rw [hf k, hj]
  }
  {
    intro h1
    obtain ⟨ i, hi⟩ := h1
    rw [hi]
    apply @delete_vertex_is_face SC _ _ J hs
  }
}

end simplex_child

section cases_ABCD

lemma insert_vertex I (v : SC.G) j :
    ∃ J, I = @delete_vertex SC n1 hn1 j J ∧ J j = v := by {
  have h1 : ∀ j2, ∃ w, (j2 = j → w = v)
      ∧ ∀ i, @insert_index SC n1 hn1 j i = j2 → I i = w := by {
    intro j2
    by_cases h1 : j2 = j
    {
      use v
      simp only [implies_true, true_and]
      intro i
      have h3 : @insert_index SC n1 hn1 j i ≠ j := by {apply insert_index_ne}
      simp only [h1, h3, IsEmpty.forall_iff]
    }
    {
      have h3 : ∃ i, j2 = @insert_index SC n1 hn1 j i := by {
        apply almost_surjective_of_insert_index
        exact h1
      }
      obtain ⟨ i, hi⟩ := h3
      use (I i)
      simp only [h1, IsEmpty.forall_iff, true_and]
      intro i2 h2
      congr!
      apply insert_index_inj SC j
      rw [h2, hi]
    }
  }
  obtain ⟨J, h2⟩ := axiomOfChoice h1
  use J
  apply And.intro
  {
    ext i
    exact (h2 (@insert_index SC n1 hn1 j i)).2 i rfl
  }
  exact (h2 j).1 rfl
}

lemma surround_index (j : Fin (SC.n + 1)) (i : Fin (n1 + 1)) (hij : i.1 + 1 = j.1 )
    (hj1 : j ≠ Fin.last SC.n): ((@insert_index SC n1 hn1 j i).1 + 1 = j.1
    ∧ j.1 + 1 = @insert_index SC n1 hn1 j (i+1)) := by {
  unfold insert_index
  have h2 : i.1 < j.1 := by omega
  have h3 : (i+1).1 = i.1 + 1 := by {
    refine Fin.val_add_one_of_lt ?_
    simp only [Nat.succ_eq_add_one]
    show i.1 < n1
    have h6 := Fin.val_lt_last hj1
    omega
  }
  apply And.intro
  {
    simp only [h2, ↓reduceIte]
    exact hij
  }
  simp only [h3, hij, lt_self_iff_false, ↓reduceIte]
}

lemma parent_injective I (hs : simplex SC n1 I) J j
    (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ∉ Set.range I)
    : Function.Injective J := by {
  have h5 j3 : j3 ≠ j → ∃ i3, j3 = @insert_index SC n1 hn1 j i3
    := by {apply almost_surjective_of_insert_index}
  intro j1 j2 h4
  have h7 j3 : J j3 = J j → j3 = j := by {
      intro h7
      by_contra h51
      apply h2
      obtain ⟨i3, hi3⟩ := h5 j3 h51
      use i3
      rw [←h7,h1,hi3]
      rfl
  }
  by_cases h8 : j1 = j
  {
    rw [h8, h7 j2]
    rw [←h8,h4]
  }
  by_cases h9 : j2 = j
  {
    rw [h9, h7 j1]
    rw [←h9,h4]
  }
  obtain ⟨i1, hi1⟩ := h5 j1 h8
  obtain ⟨i2, hi2⟩ := h5 j2 h9
  suffices h11 : i1 = i2 by {rw [hi1,hi2,h11] }
  apply hs.1
  rw [h1]
  unfold delete_vertex
  rw [← hi1,← hi2, h4]
}

lemma parent_simplex_case_BC I (hs : simplex SC n1 I) J
    (h1 : I = @delete_vertex SC n1 hn1 0 J) (h2 : J 0 ≠ I 0)
    (h3 : ∀ k, J 0 k ≤ I 0 k ∧ (I (Fin.last n1) k).1 ≤ (J 0 k).1 + 1) : is_face SC I J := by {
  suffices h4 : simplex SC SC.n J by {
    rw [child_simplex_char]
    use 0
    exact h4
  }
  have h4 : J 0 ∉ Set.range I := by {
    intro h5
    obtain ⟨i1, hi1⟩ := h5
    apply h2
    apply funext
    intro k
    apply le_antisymm (h3 k).1
    rw [←hi1]
    apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le i1)
  }
  apply And.intro ( parent_injective SC I hs J 0 h1 h4)
  have h5 j2 : j2 < n1 + 1 →  J (Fin.ofNat _ (j2+1)) = I (Fin.ofNat _ j2) := by {
    rw [h1]
    unfold delete_vertex insert_index
    congr! with h7
    simp only [Fin.ofNat_eq_cast, Fin.val_zero, not_lt_zero, ↓reduceIte]
    rw [Fin.val_cast_of_lt, Fin.val_cast_of_lt h7]
    omega
  }
  intro j1 hj1 k1
  apply And.intro
  {
    rw [←hn1] at hj1
    rw [h5 j1 hj1]
    cases j1
    {
      simp only [Fin.ofNat_eq_cast, Fin.val_fin_le]
      exact (h3 k1).1
    }
    rename_i j2
    rw [h5 j2]
    apply monotone_1_of_simplex SC I hs
    simp only [Fin.ofNat_eq_cast]
    apply Fin.natCast_mono
    exact Nat.le_of_lt_succ hj1
    exact Nat.le_add_right j2 1
    exact Nat.lt_of_succ_lt hj1
  }
  {
    have h6 := h5 n1 (lt_add_one n1)
    have e1 : (Fin.ofNat (SC.n + 1) (n1 + 1) : Fin (SC.n + 1)) = Fin.last SC.n := by
      rw [← hn1]; simp [Fin.ofNat_eq_cast, Fin.natCast_eq_last]
    have e2 : (Fin.ofNat (n1 + 1) n1 : Fin (n1 + 1)) = Fin.last n1 := by
      simp [Fin.ofNat_eq_cast, Fin.natCast_eq_last]
    rw [e1, e2] at h6
    rw [congrFun h6 k1]
    exact (h3 k1).2
  }
}

lemma parent_simplex_case_AC I (hs : simplex SC n1 I) J j (hj : j = Fin.last SC.n)
    (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ≠ I (Fin.last n1))
    (h3 : ∀ k, I (Fin.last n1) k ≤ J j k ∧ (J j k).1 ≤ (I 0 k).1 + 1) : is_face SC I J := by {
  suffices h4 : simplex SC SC.n J by {
    rw [child_simplex_char]
    use j
    exact h4
  }
  have h4 : J j ∉ Set.range I := by {
    intro h5
    obtain ⟨i1, hi1⟩ := h5
    apply h2
    apply funext
    intro k
    apply le_antisymm _ (h3 k).1
    rw [←hi1]
    apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last i1)
  }
  have h5 j2 : j2 < SC.n → J (Fin.ofNat _ j2) = I (Fin.ofNat _ j2) := by {
    intro h6
    rw [h1,hj]
    unfold delete_vertex insert_index
    congr!
    have h7 : (Fin.ofNat (n1+1) j2).1 < (Fin.last SC.n).1 := by {
      simp only [Fin.ofNat_eq_cast, Fin.val_last]
      rw [Fin.val_cast_of_lt]
      exact h6
      rwa [←hn1] at h6
    }
    simp only [h7,↓reduceIte]
    simp only [Fin.ofNat_eq_cast]
    rw [Fin.val_cast_of_lt, Fin.val_cast_of_lt]
    rwa [←hn1] at h6
    exact Nat.lt_add_right 1 h6
  }
  apply And.intro ( parent_injective SC I hs J j h1 h4)
  intro j1 hj1 k1
  apply And.intro
  {
    rw [h5 _ hj1]
    by_cases h12 : j1 + 1 < SC.n
    {
      rw [h5 _ h12]
      apply monotone_1_of_simplex SC I hs
      simp only [Fin.ofNat_eq_cast]
      apply Fin.natCast_mono
      apply Nat.le_of_lt_add_one
      rwa [hn1]
      exact Nat.le_add_right j1 1
    }
    have h16 : j1+1 = SC.n := by omega
    have h13 : Fin.ofNat _ j1 = Fin.last n1 := by {
      suffices h15 : j1 = n1 by {
        simp only [h15, Fin.ofNat_eq_cast, Fin.natCast_eq_last]
      }
      omega
    }
    have h14 : Fin.ofNat _ (j1+1) = j := by {
      rw [hj]
      simp only [h16, Fin.ofNat_eq_cast, Fin.natCast_eq_last]
    }
    rw [h13,h14]
    exact (h3 k1).1
  }
  {
    have h7 : J 0 = I 0 := by {
      have h6 := h5 0 (Nat.zero_lt_of_lt hj1)
      simp only [Fin.ofNat_eq_cast] at h6
      exact h6
    }
    rw [h7,←hj]
    exact (h3 k1).2
  }
}

lemma parent_simplex_case_D I (hs : simplex SC n1 I) J j i
    (hij : i.1 + 1 = j.1 ) (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ∉ Set.range I)
    (h3 : ∀ k, I i k ≤ J j k ∧ J j k ≤ I (i+1) k) : is_face SC I J := by {
  suffices h4 : simplex SC SC.n J by {
    rw [child_simplex_char]
    use j
    exact h4
  }
  have h5 j3 : j3 ≠ j → ∃ i3, j3 = @insert_index SC n1 hn1 j i3 := by {
    apply almost_surjective_of_insert_index
  }
  have h6 j3 : j3 ≠ j → ∃ i3, I i3 = J j3 := by {
    intro h7
    obtain ⟨i3, hi3⟩ := h5 j3 h7
    use i3
    rw [h1, hi3]
    rfl
  }
  apply And.intro (parent_injective SC I hs J j h1 h2)
  intro i2 h4 k2
  have h5 := h3 k2
  apply And.intro
  {
    simp only [Fin.ofNat_eq_cast, Fin.val_fin_le]
    rw [h1] at h5
    unfold delete_vertex at h5
    have h6 : (@insert_index SC n1 hn1 j i).1 + 1 = j := by {
      unfold insert_index
      have h7 : i.1 < j.1 := by omega
      simp only [h7, ↓reduceIte]
      exact hij
    }
    by_cases h8 : i2 = j.1
    {
      convert h5.2
      simp only [h8, Fin.cast_val_eq_self]
      have h11 : j ≠ Fin.last SC.n := by {
        suffices h12 : j.1 ≠ SC.n by exact Ne.symm (Fin.ne_of_val_ne (Ne.symm h12))
        rw [←h8]
        exact Nat.ne_of_lt h4
      }
      have h9 := @surround_index SC n1 hn1 j i hij h11
      rw [h8, h9.2]
      exact Fin.cast_val_eq_self (insert_index SC j (i + 1))
    }
    by_cases h9 : i2 + 1 = j.1
    {
      rw [←h9] at h6
      simp only [Nat.add_right_cancel_iff] at h6
      convert h5.1
      rw [←h6]
      simp only [Fin.cast_val_eq_self]
      rw [h9]
      simp only [Fin.cast_val_eq_self]
    }
    have h11 : ∃ i3, (Fin.ofNat _ i2) = @insert_index SC n1 hn1 j i3 := by {
      apply almost_surjective_of_insert_index
      intro h12
      apply h8
      rw [← h12]
      simp only [Fin.ofNat_eq_cast]
      rw [Fin.val_cast_of_lt]
      apply lt_trans h4 (lt_add_one SC.n)
    }
    have h12 : ∃ i3, (Fin.ofNat _ (i2+1)) = @insert_index SC n1 hn1 j i3 := by {
      apply almost_surjective_of_insert_index
      intro h12
      apply h9
      rw [← h12]
      simp only [Fin.ofNat_eq_cast]
      rw [Fin.val_cast_of_lt]
      omega
    }
    simp only [Fin.ofNat_eq_cast] at h11 h12
    obtain ⟨i3, hi3⟩ := h11
    obtain ⟨i4, hi4⟩ := h12
    rw [hi3, hi4]
    suffices h21 : I i3 k2 ≤ I i4 k2 by {rwa [h1] at h21}
    apply monotone_1_of_simplex SC I hs
    have h21 : StrictMono (@insert_index SC n1 hn1 j) := by {
      apply insert_index_strict_mono
    }
    rw [←h21.le_iff_le]
    rw [←hi3, ← hi4]
    refine (Fin.natCast_le_natCast ?_ h4).mpr ?_
    exact Nat.le_of_succ_le h4
    exact Nat.le_succ i2
  }
  {
    have h11 : (J (Fin.last SC.n) k2).1 ≤ (I (Fin.last n1) k2).1 := by {
      simp only [Fin.val_fin_le]
      by_cases h12 : Fin.last SC.n = j
      {
        rw [h12]
        apply le_trans h5.2
        apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last _)
      }
      obtain ⟨ i3, hi3⟩ := h6 _ h12
      rw [←hi3]
      apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last _)
    }
    have h13 := last_of_simplex SC I hs k2
    apply le_trans h11 (le_trans h13 _)
    simp only [add_le_add_iff_right, Fin.val_fin_le]
    by_cases h14 : 0 = j
    {
      rw [h14]
      apply le_trans _ h5.1
      apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le _)
    }
    {
      obtain ⟨i3, hi3⟩ := h6 _ h14
      rw [← hi3]
      apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le _)
    }
  }
}

noncomputable def coord_change_count (v1 v2 : SC.G) := Finset.card {i | v1 i ≠ v2 i}

lemma ccc_add {m} I (hs : simplex SC m I) (i1 i2 i3) (h1 : i1 ≤ i2 ∧ i2 ≤ i3) :
    coord_change_count SC (I i1) (I i3) =
    coord_change_count SC (I i1) (I i2) + coord_change_count SC (I i2) (I i3) := by {
  unfold coord_change_count
  rw [←Finset.card_union_of_disjoint]
  congr
  apply Finset.ext_iff.mpr
  intro k2
  simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  rw [←Decidable.not_and_iff_not_or_not]
  apply Iff.intro
  {
    intro h3 h4
    apply h3
    rw [h4.1, h4.2]
  }
  {
    intro h2 h3
    apply h2
    have h4 := monotone_1_of_simplex SC I hs i1 i2 h1.1 k2
    have h5 := monotone_1_of_simplex SC I hs i2 i3 h1.2 k2
    rw [h3] at h4 ⊢
    suffices h1 : I i3 k2 = I i2 k2 by exact ⟨h1, Eq.symm h1⟩
    exact Fin.le_antisymm h4 h5
  }
  {
    apply Finset.disjoint_filter.mpr
    intro k1 hk1 h2 h3
    apply h3
    have h4 : ∀ k, I i1 k ≤ I i2 k :=  monotone_1_of_simplex SC I hs i1 i2 h1.1
    have h5 : I i1 k1 < I i2 k1 := lt_of_le_of_ne (h4 k1) h2
    have h6 : (I i3 k1).1 ≤ (I i1 k1).1 + 1 := by {
      apply le_add_one_of_simplex _ _ hs
    }
    apply le_antisymm ( monotone_1_of_simplex SC I hs i2 i3 h1.2 k1)
    apply le_trans h6 h5
  }
}

lemma ccc_pos {m} I (hs : simplex SC m I) i1 i2 (h1 : i1 ≠ i2)
    : 0 < coord_change_count SC (I i1) (I i2) := by {
  unfold coord_change_count
  by_contra! h2
  apply h1
  apply hs.1
  simp only [ne_eq, nonpos_iff_eq_zero, Finset.card_eq_zero] at h2
  apply funext
  intro k
  rw [Finset.filter_eq_empty_iff] at h2
  simp only [Finset.mem_univ, Decidable.not_not, forall_const] at h2
  apply h2
}

noncomputable def ccc_fun {m} (I : Fin (m+1)→ SC.G) (i : Fin (m+1)) : Fin (SC.n + 1 )
    := ⟨ coord_change_count SC (I 0) (I i), by {
      refine Nat.lt_succ_of_le ?_
      exact card_finset_fin_le {i_1 | I 0 i_1 ≠ I i i_1}
    } ⟩

lemma ccc_fun_strict_mono {m} I (hs : simplex SC m I) :
    StrictMono (ccc_fun SC I) := by {
  intro i1 i2 h1
  unfold ccc_fun
  simp only [Fin.mk_lt_mk]
  have h3 : 0 ≤ i1 ∧ i1 ≤ i2 := ⟨ (Fin.zero_le i1), (Fin.le_of_lt h1) ⟩
  rw [ccc_add SC I hs 0 i1 i2 h3]
  simp only [lt_add_iff_pos_right, gt_iff_lt]
  apply ccc_pos SC I hs _ _ $ Fin.ne_of_lt h1
}

lemma ccc_fun_is_insert_index I (hs : simplex SC n1 I) :
    ∃ j, ccc_fun SC I = @insert_index SC n1 hn1 j := by {
  apply is_insert_index_of_strict_mono
  apply ccc_fun_strict_mono SC I hs
}

lemma ccc_fun_case_D_iff {m} I (hs : simplex SC m I) :
    case_D SC I ↔ ccc_fun SC I (Fin.last m) = Fin.last SC.n := by {
  have h1 : (ccc_fun SC I (Fin.last m) = Fin.last SC.n) ↔ ∀ k, I 0 k ≠ I (Fin.last m) k  := by {
    unfold ccc_fun coord_change_count
    rw [Fin.ext_iff]
    have h3 : SC.n = Fintype.card (Fin SC.n) := by {exact Eq.symm (Fintype.card_fin SC.n)}
    simp only [ne_eq, Fin.val_last]
    nth_rewrite 7 [h3]
    rw [Finset.card_eq_iff_eq_univ, Finset.eq_univ_iff_forall]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  }
  apply Iff.trans _ h1.symm
  unfold case_D
  apply Iff.intro
  {
    intro h2 k1
    obtain ⟨i2, hi2⟩ := h2 k1 (I 0 k1)
    intro h3
    apply hi2
    apply le_antisymm
    {
      rw [h3]
      apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last i2)
    }
    exact monotone_1_of_simplex SC I hs _ _ (Fin.zero_le i2) k1
  }
  {
    contrapose!
    intro h2
    obtain ⟨k2, ⟨q, hq⟩ ⟩ := h2
    use k2
    rw [hq, hq]
  }
}

lemma last_eq_first_add_one J (hs : simplex SC SC.n J)
    : ∀ k, (J (Fin.last SC.n) k).1 = (J 0 k).1 + 1 := by {
  have h3 : ∀ j3, ccc_fun SC J j3 = j3 := by {
    apply is_id_of_strict_mono
    apply ccc_fun_strict_mono SC J hs
  }
  have h2 := (ccc_fun_case_D_iff SC J hs).mpr (h3 _)
  unfold case_D at h2
  intro k
  apply le_antisymm  (last_of_simplex SC J hs k)
  apply Nat.add_one_le_of_lt
  obtain ⟨j1, hj1⟩ := h2 k (J 0 k)
  have h4 := monotone_1_of_simplex SC J hs _ _ (Fin.le_last j1) k
  apply lt_of_lt_of_le _ h4
  apply lt_of_le_of_ne (monotone_1_of_simplex SC J hs _ _ (Fin.zero_le j1) k) hj1.symm
}

lemma delete_vertex_ccc_fun_match J (hs : simplex SC SC.n J) j1 j2
    ( h1 : ccc_fun SC (@delete_vertex SC n1 hn1 j1 J) = @insert_index SC n1 hn1 j2)
    : (j1 = 0 → j2 = Fin.last SC.n) ∧ (j1 ≠ 0 → j1 = j2) := by {
  let I := @delete_vertex SC n1 hn1 j1 J
  have hsI : simplex SC n1 I := by {
    suffices h2 : is_face SC I J by { exact h2.1}
    rw [@child_simplex_char SC n1 hn1 I J hs]
    use j1
  }
  have scnpos : 0 < SC.n := by omega
  by_cases h4 : j1 = 0
  {
    simp only [h4, forall_const, ne_eq, not_true_eq_false, IsEmpty.forall_iff, and_true]
    have h5 : I 0 = J 1 := by {
      unfold I delete_vertex insert_index
      congr!
      rw [h4]
      simp only [Fin.val_zero, lt_self_iff_false, ↓reduceIte, zero_add]
      simp only [Fin.val_one']
      refine Eq.symm (Nat.mod_eq_of_lt ?_)
      exact Nat.lt_add_of_pos_left scnpos
    }
    symm
    by_contra h6
    obtain ⟨i1, hi1⟩ := @almost_surjective_of_insert_index SC n1 hn1 _ _ h6
    have h8 : (ccc_fun SC I i1).1 = SC.n := by {
      unfold I
      rw [h1, ← hi1]
      simp only [Fin.val_last]
    }
    unfold ccc_fun at h8
    simp only [h5] at h8
    unfold I delete_vertex at h8
    let c2 := coord_change_count SC (J 0) (J 1)
    have c2pos : 0 < c2 := by {
      apply ccc_pos _ _ hs
      simp only [ne_eq, Fin.zero_eq_one_iff, Nat.add_eq_right]
      omega
    }
    let j3 := @insert_index SC n1 hn1 j1 i1
    have h9 : (ccc_fun SC J j3).1 = c2 + SC.n:= by {
      simp only [← h8]
      apply ccc_add SC J hs
      simp only [Fin.zero_le, true_and]
      suffices h9 : j3 ≠ j1 by {
        rw [h4] at h9
        exact Fin.one_le_of_ne_zero h9
      }
      apply insert_index_ne
    }
    have h10 : c2 + SC.n ≤ SC.n := by {
      rw [←h9]
      exact Fin.is_le (ccc_fun SC J j3)
    }
    simp only [add_le_iff_nonpos_left, nonpos_iff_eq_zero] at h10
    omega
  }
  simp only [h4, IsEmpty.forall_iff, ne_eq, not_false_eq_true, forall_const, true_and]
  have h2 : I 0 = J 0 := by {
    unfold I delete_vertex
    congr!
    unfold insert_index
    simpa only [Fin.val_zero, Fin.val_pos_iff, zero_add, Fin.mk_eq_zero,
        ite_eq_left_iff, not_lt,Fin.le_zero_iff, one_ne_zero, imp_false]
  }
  have h3 : ∀ j3, ccc_fun SC J j3 = j3 := by {
    apply is_id_of_strict_mono
    apply ccc_fun_strict_mono SC J hs
  }
  symm
  by_contra h5
  obtain ⟨i1, hi1⟩ := @almost_surjective_of_insert_index SC n1 hn1 _ _ h5
  have h6 : ccc_fun SC I i1 = ccc_fun SC J j2 := by {
    unfold ccc_fun
    simp [h2]
    congr
    rw [hi1]
    rfl
  }
  rw [h1, h3 j2] at h6
  contrapose h6
  apply insert_index_ne
}

lemma case_D_iff_not_end_1 I (hs : simplex SC n1 I) j
    (h1 : ccc_fun SC I = @insert_index SC n1 hn1 j) :
    case_D SC I ↔ j ≠ 0 ∧ j ≠ Fin.last SC.n := by {
  rw [ccc_fun_case_D_iff SC I hs, h1]
  have h2 : j ≠ 0 := by {
    intro h3
    apply @insert_index_ne SC n1 hn1 j 0
    rw [←h1, h3]
    unfold ccc_fun coord_change_count
    simp only [ne_eq, not_true_eq_false, Finset.filter_false, Finset.card_empty, Fin.zero_eta]
  }
  simp only [ne_eq, h2, not_false_eq_true, true_and]
  apply Iff.intro
  {
    intro h3 h4
    apply @insert_index_ne SC n1 hn1 j (Fin.last n1)
    rw [h3,h4]
  }
  {
    intro h3
    have h32 : Fin.last SC.n ≠ j := fun a ↦ h3 (Eq.symm a)
    obtain ⟨i2, hi2⟩  := @almost_surjective_of_insert_index SC n1 hn1 j (Fin.last SC.n) h32
    apply le_antisymm
    exact Fin.le_last (insert_index SC j (Fin.last n1))
    rw [hi2]
    have h4 := @insert_index_strict_mono SC n1 hn1 j
    rw [h4.le_iff_le]
    exact Fin.le_last i2
  }
}

lemma case_D_iff_not_end_2 J (hs : simplex SC SC.n J) j :
    case_D SC (@delete_vertex SC n1 hn1 j J) ↔ j ≠ 0 ∧ j ≠ Fin.last SC.n := by {
  let I := @delete_vertex SC n1 hn1 j J
  have hsI : simplex SC n1 I := by {
    suffices h2 : is_face SC I J by exact h2.1
    rw [@child_simplex_char SC n1 hn1 I J hs]
    use j
  }
  obtain ⟨j2, hj2⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hsI
  have h1 := @delete_vertex_ccc_fun_match SC n1 hn1 J hs j j2 hj2
  by_cases h2 : j = 0
  {
    rw [ccc_fun_case_D_iff SC I hsI]
    simp only [h2, ne_eq, not_true_eq_false, Fin.zero_eq_last_iff, false_and, iff_false]
    rw [←h1.1 h2, hj2]
    apply insert_index_ne
  }
  rw [@case_D_iff_not_end_1 SC n1 hn1 I hsI]
  rw [hj2, ← h1.2 h2]
}

lemma same_delete_index_eq_iff J1 J2 j
    (h1 : @delete_vertex SC n1 hn1 j J1 = @delete_vertex SC n1 hn1 j J2)
    : J1 = J2 ↔ J1 j = J2 j := by {
  apply Iff.intro (fun a ↦ congrFun a j)
  intro h2
  ext j2
  by_cases h3 : j2 = j
  rw [h3,h2]
  obtain ⟨i1, hi1⟩ := @almost_surjective_of_insert_index SC n1 hn1 j j2 h3
  rw [hi1]
  exact congrFun h1 i1
}

lemma case_D_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h1 : case_D SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 2 := by {
  obtain ⟨ j1, hj1 ⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hs
  have h2 : j1 ≠ 0 ∧ j1 ≠ Fin.last SC.n := by {
    rw [←case_D_iff_not_end_1 SC I hs j1 hj1]
    exact h1
  }
  have h3 : ∃ (i1: Fin (n1 + 1)), i1.1 + 1 = j1.1 := by {
    obtain ⟨a, ha⟩ := Fin.exists_succ_eq_of_ne_zero h2.1
    rw [← ha]
    simp only [Fin.val_succ, Nat.add_right_cancel_iff]
    use ⟨ a.1, by {rw [hn1]; exact a.2}⟩
  }
  obtain ⟨ i1, hi1⟩ := h3
  have h32 : i1 ≤ i1 + 1 := by {
    refine Fin.le_of_lt ?_
    refine Fin.lt_add_one_iff.mpr ?_
    show i1.1 < n1
    have h3 := Fin.val_lt_last h2.2
    omega
  }
  have h11 := @surround_index SC n1 hn1 j1 i1 hi1 h2.2
  have h12 : @insert_index SC n1 hn1 j1 i1 ≤ j1 ∧ j1 ≤ @insert_index SC n1 hn1 j1 (i1+1) := by {
    rw [Fin.le_def, Fin.le_def, ←h11.2]
    apply And.intro
    rw [←h11.1]
    apply Nat.le_add_right
    apply Nat.le_add_right
  }
  have h3 : coord_change_count SC (I i1) (I (i1+1)) = 2 := by {
    have h3 : (@insert_index SC n1 hn1 j1 i1).1 + 2
        = (@insert_index SC n1 hn1 j1 (i1 +1)).1 := by {
      rw [← h11.2, ←h11.1]
    }
    have h4 : (ccc_fun SC I (i1+1)).1 = (ccc_fun SC I i1).1
        + coord_change_count SC (I i1) (I (i1 + 1)) := by {
      apply ccc_add SC I hs
      simp only [Fin.zero_le, true_and, h32]
    }
    rw [← hj1, h4 ] at h3
    simp only [Nat.add_left_cancel_iff] at h3
    exact h3.symm
  }
  have h4 : ∃ k1, ∃ k2, k1 ≠ k2 ∧ {k | I i1 k ≠ I (i1 +1) k} = {k1, k2} := by {
    unfold coord_change_count at h3
    rw [Finset.card_eq_two] at h3
    convert h3
    simp only [ne_eq]
    rw [←Finset.coe_eq_pair]
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
  }
  obtain ⟨k1, ⟨k2, h4⟩ ⟩ := h4
  have hk1 : I i1 k1 ≠ I (i1+1) k1 := by {
    have h5 := Set.mem_insert k1 {k2}
    rwa [←h4.2] at h5
  }
  have hk2 : I i1 k2 ≠ I (i1+1) k2 := by {
    have h5 : k2 ∈ ({k1, k2} : Set _) := Set.mem_insert_of_mem k1 rfl
    rwa [←h4.2] at h5
  }
  have h5 k3 : I i1 k3 ≠ I (i1+1) k3 → ∃ J3,
      I = @delete_vertex SC n1 hn1 j1 J3 ∧ is_face SC I J3 ∧ J3 j1 k3 ≠ I i1 k3 := by {
    intro h21
    let ins : SC.G := fun k ↦ if k = k3 then I (i1 + 1) k else I i1 k
    obtain ⟨J3, hJ3⟩ := @insert_vertex SC n1 hn1 I ins j1
    have h6 : ∀ k, I i1 k ≤ ins k ∧ ins k ≤ I (i1+1) k := by {
      intro k
      unfold ins
      have h13 : I i1 k3 ≤ I (i1+1) k3 := monotone_1_of_simplex SC I hs _ _ h32 k3
      by_cases h12 : k = k3
      simp only [h12, ↓reduceIte, le_refl, and_true, ge_iff_le]
      exact monotone_1_of_simplex SC I hs _ _ h32 k3
      simp only [h12, ↓reduceIte, le_refl, true_and, ge_iff_le]
      exact monotone_1_of_simplex SC I hs _ _ h32 k
    }
    have h22 : J3 j1 k3 ≠ I i1 k3 := by {
      rw [hJ3.2]
      unfold ins
      simp only [↓reduceIte, ne_eq]
      exact h21.symm
    }
    have h23 : ∃ k4, k3 ≠ k4 ∧ I i1 k4 ≠ I (i1+1) k4 := by {
      by_cases h24 : k3 = k1
      use k2
      rw [h24]
      apply And.intro h4.1 hk2
      use k1
    }
    have h7 : ins ∉ Set.range I := by {
      intro h9
      obtain ⟨i2,hi2⟩ := h9
      rw [forall_and, ← hi2] at h6
      rw [← monotone_2_of_simplex _ _ hs,← monotone_2_of_simplex _ _ hs] at h6
      have h13 : i2 = i1 ∨ i2 = i1 + 1 := by {
        refine (WCovBy.le_and_le_iff ?_).mp h6
        apply And.intro h32
        intro i3 h33
        simp only [not_lt]
        exact Fin.add_one_le_of_lt h33
      }
      cases' h13 with h13 h13
      apply h22
      rw [hJ3.2, ←hi2, h13]
      obtain ⟨k4, hk4⟩ := h23
      apply hk4.2
      rw [←h13, hi2]
      unfold ins
      simp only [right_eq_ite_iff]
      intro h33
      exact False.elim $ hk4.1 h33.symm
    }
    use J3
    apply And.intro hJ3.1 (And.intro _ h22)
    apply @parent_simplex_case_D SC n1 hn1 I hs J3 _ _ hi1 hJ3.1
    rwa [hJ3.2]
    rwa [hJ3.2]
  }
  obtain ⟨J1, hJ1⟩ := h5 k1 hk1
  obtain ⟨J2, hJ2⟩ := h5 k2 hk2
  have h6 J3 : I = @delete_vertex SC n1 hn1 j1 J3 → is_face SC I J3
    → ∀ k, I i1 k ≤ J3 j1 k ∧ J3 j1 k ≤ I (i1+1) k := by {
    intro h14 h13 k3
    rw [h14]
    apply And.intro
    apply monotone_1_of_simplex SC J3 h13.2.1 _ _ h12.1
    apply monotone_1_of_simplex SC J3 h13.2.1 _ _ h12.2
  }
  have h7 J3 k3 : I = @delete_vertex SC n1 hn1 j1 J3 ∧ is_face SC I J3 ∧ J3 j1 k3 ≠ I i1 k3
      → J3 j1 k3 = I (i1+1) k3 ∧ ∀ k4, k3 ≠ k4 → J3 j1 k4 = I i1 k4 := by {
    intro h9
    have h6 := h6 J3 h9.1 h9.2.1
    have h31 := h3
    rw [h9.1] at h31
    have h21 := ccc_add SC J3 h9.2.1.2.1 _ _ _ h12
    unfold delete_vertex at h31
    rw [h31] at h21
    have h22 c1 c2 : 2 = c1 + c2 → 0 < c2 → c1 ≤ 1 := by omega
    have h23 : coord_change_count SC (I i1) (J3 j1) ≤ 1 := by {
      rw [h9.1]
      apply h22 _ _ h21
      apply ccc_pos SC
      exact h9.2.1.2.1
      symm
      apply insert_index_ne
    }
    apply And.intro
    {
      apply le_antisymm (h6 k3).2
      rw [Fin.le_def]
      have h24 := le_add_one_of_simplex SC I hs (i1+1) i1 k3
      apply le_trans h24
      apply Fin.val_add_one_le_of_lt (lt_of_le_of_ne (h6 k3).1 h9.2.2.symm)
    }
    intro k4 hk4
    contrapose! h23
    refine Finset.one_lt_card_iff.mpr ?_
    use k3, k4
    simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and]
    exact And.intro h9.2.2.symm ( And.intro h23.symm hk4)
  }
  refine Finset.card_eq_two.mpr ?_
  use J1, J2
  apply And.intro
  {
    have h71 := (h7 J1 k1 hJ1).2 k2 h4.1
    intro h9
    apply hJ2.2.2
    rw [←h9, h71]
  }
  apply subset_antisymm
  {
    intro J3
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    intro hJ3
    have h14 := (@child_simplex_char SC n1 hn1 I J3 hJ3.2.1).mp hJ3
    obtain ⟨j2, hj2⟩ := h14
    rw [hj2] at hj1
    have h13 := @delete_vertex_ccc_fun_match SC n1 hn1 J3 hJ3.2.1 j2 j1 hj1
    have h15 := @case_D_iff_not_end_2 SC n1 hn1 J3 hJ3.2.1 j2
    rw [←hj2] at h15
    have h16 : j2 = j1 := h13.2 (h15.mp h1).1
    rw [h16] at hj2
    rw [same_delete_index_eq_iff SC J3 J1 j1, same_delete_index_eq_iff SC J3 J2 j1]
    have h71 := h7 J1 k1 hJ1
    have h72 := h7 J2 k2 hJ2
    have h18 : ∃ k5, J3 j1 k5 ≠ I i1 k5 := by {
      suffices h19 : J3 j1 ≠ I i1 by exact Function.ne_iff.mp h19
      intro h19
      apply @insert_index_ne SC n1 hn1 j1 i1
      apply hJ3.2.1.1
      rw [h19, hj2]
      rfl
    }
    obtain ⟨k5, hk5⟩ := h18
    have h73 := h7 J3 k5 ⟨hj2, ⟨ hJ3, hk5⟩ ⟩
    clear h15 h13
    have h19 : k5 = k1 ∨ k5 = k2 := by {
      have h21 : I i1 k5 ≠ I (i1+1) k5 := by {
        rw [←h73.1]
        exact hk5.symm
      }
      exact h4.2.subset h21
    }
    have h20 (J4 : _ → SC.G) : (J4 j1 k5 = I (i1+1) k5 ∧ ∀ k4, k5 ≠ k4 → J4 j1 k4 = I i1 k4)
        → J3 j1 = J4 j1:= by {
      intro h21
      apply funext
      intro k6
      by_cases h22 : k5 = k6
      rw [←h22,h21.1,h73.1]
      rw [h21.2 k6 h22, h73.2 k6 h22]
    }
    cases h19
    left
    rename_i h21
    apply h20
    rwa [h21]
    right
    rename_i h21
    apply h20
    rwa [h21]
    rw [←hJ2.1, ←hj2]
    any_goals exact hn1
    rw [←hJ1.1, ←hj2]
  }
  {
    refine Finset.insert_subset ?_ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hJ1.2.1
    simp only [Finset.singleton_subset_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hJ2.2.1
  }
}

lemma unique_const_ABC {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) k1 q1
    (h1 : ∀ i, I i k1 = q1): ∀ k2, k1 ≠ k2 → I 0 k2 ≠ I (Fin.last n1) k2 := by {
  intro k2 h3 h2
  let s : Finset (Fin SC.n) := {i | I 0 i ≠ I (Fin.last n1) i}
  have h4 : n1 ≤ s.card := by {
    obtain ⟨j, hj⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hs
    show n1 ≤ (ccc_fun SC I (Fin.last n1)).1
    rw [hj]
    unfold insert_index
    simp only [Fin.val_last]
    by_cases h11 : n1 < j.1
    simp only [h11, ↓reduceIte, le_refl]
    simp only [h11, ↓reduceIte, le_add_iff_nonneg_right, zero_le]
  }
  have h6 : 2 ≤ sᶜ.card := by {
    show 1 < sᶜ.card
    rw [Finset.one_lt_card]
    use k2
    unfold s
    simp only [ne_eq, Finset.compl_filter, Decidable.not_not, Finset.mem_filter,
        Finset.mem_univ,h2, and_self, true_and]
    use k1
    apply And.intro _ h3.symm
    rw [h1,h1]
  }
  have h7 := add_le_add h4 h6
  simp only [Finset.card_add_card_compl, Fintype.card_fin] at h7
  rw [←hn1,add_le_add_iff_left] at h7
  simp only [Nat.not_ofNat_le_one] at h7
}

lemma case_AC_ex_unique I (hs : simplex SC n1 I) k1 q
    (hABC : ∀ i, I i k1 = q) (hAC : q ≠ Fin.last SC.p)
    : ∃! J, I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J := by {
  have h1 k2 : I 0 k2 ≠ Fin.last SC.p := by {
    intro h11
    have h12 : k1 ≠ k2 := by {
      intro h13
      apply hAC
      rw [←hABC 0,h13,h11]
    }
    apply @unique_const_ABC SC n1 hn1 I hs k1 q hABC k2 h12
    apply le_antisymm
    apply monotone_1_of_simplex SC I hs
    exact Fin.zero_le (Fin.last n1)
    rw [h11]
    exact Fin.le_last (I (Fin.last n1) k2)
  }
  let ins2 : SC.G := fun k ↦ (I 0 k) + 1
  have h2 k : (ins2 k).1 = (I 0 k).1 + 1 := by {
    apply Fin.val_add_one_of_lt
    rw [Fin.lt_last_iff_ne_last]
    exact h1 k
  }
  obtain ⟨J1, hJ1⟩ := @insert_vertex SC n1 hn1 I ins2 (Fin.last SC.n)
  have h3 : J1 (Fin.last SC.n) ≠ I (Fin.last n1) := by {
    intro h12
    have h11 : I 0 k1 = I 0 k1 + 1 := by {
      show I 0 k1 = ins2 k1
      rw [←hJ1.2, h12,hABC,hABC]
    }
    simp only [left_eq_add, Fin.one_eq_zero_iff, Nat.add_eq_right] at h11
    apply @p_ne_zero_of_cube SC n1 hn1
    simp only [Fin.last_eq_zero_iff, h11]
  }
  have h4 : is_face SC I J1 := by {
    apply parent_simplex_case_AC SC I hs J1 (Fin.last SC.n) rfl hJ1.1 h3
    intro k2
    rw [hJ1.2]
    apply And.intro
    {
      rw [Fin.le_def, h2 k2]
      apply le_add_one_of_simplex SC I hs
    }
    rw [h2 k2]
  }
  use J1
  simp only
  apply And.intro (And.intro hJ1.1 h4)
  intro J2 hJ2
  rw [@same_delete_index_eq_iff SC n1 hn1 _ _ _ (hJ2.1.symm.trans hJ1.1)]
  rw [hJ1.2]
  apply funext
  intro k1
  ext
  have h5 := last_eq_first_add_one SC J2 hJ2.2.2.1 k1
  rw [h5, h2 k1]
  suffices h6 : I 0 = J2 0 by {rw [h6]}
  rw [hJ2.1]
  unfold delete_vertex insert_index
  congr!
  simp only [Fin.val_zero, Fin.val_last, zero_add, ite_eq_left_iff,
    not_lt, nonpos_iff_eq_zero,one_ne_zero, imp_false]
  rw [←hn1]
  omega
}

lemma case_B_not_last I (h1 : case_B SC I) J
    (h2 : I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J) : False := by {
  have h3 := last_eq_first_add_one SC J h2.2.2.1
  obtain ⟨k1, hk1⟩ := h1
  have h4 : I 0 = J 0 := by {
    rw [h2.1]
    unfold delete_vertex insert_index
    congr!
    simp only [Fin.val_zero, Fin.val_last, zero_add, ite_eq_left_iff,
        not_lt, nonpos_iff_eq_zero,one_ne_zero, imp_false]
    rw [←hn1]
    omega
  }
  have h5 := (J (Fin.last SC.n) k1).is_le
  rw [h3 k1,←h4,hk1 0] at h5
  contrapose! h5
  exact lt_add_one SC.p
}

lemma case_BC_ex_unique I (hs : simplex SC n1 I) k1 q
    (hABC : ∀ i, I i k1 = q) (hBC : q ≠ 0)
    : ∃! J, I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J := by {
  have h1 k2 : I (Fin.last n1) k2 ≠ 0 := by {
    intro h11
    have h12 : k1 ≠ k2 := by {
      intro h13
      apply hBC
      rw [←hABC (Fin.last n1),h13,h11]
    }
    apply @unique_const_ABC SC n1 hn1 I hs k1 q hABC k2 h12
    apply le_antisymm
    apply monotone_1_of_simplex SC I hs
    exact Fin.zero_le (Fin.last n1)
    rw [h11]
    exact Fin.zero_le (I 0 k2)
  }
  let ins2 : SC.G := fun k ↦ (I (Fin.last n1) k) - 1
  have h22 k := Fin.val_sub_one_of_ne_zero (h1 k)
  have h21 k : (ins2 k).1 + 1 = (I (Fin.last n1) k).1  := by {
    rw [h22]
    apply Nat.sub_one_add_one ( Fin.val_ne_zero_iff.mpr (h1 k))
  }
  obtain ⟨J1, hJ1⟩ := @insert_vertex SC n1 hn1 I ins2 0
  have h3 : J1 0 ≠ I 0 := by {
    intro h12
    have h11 : (ins2 k1).1 + 1 = ins2 k1 := by {
      rw [h21 k1, hABC, ←hJ1.2,h12,hABC]
    }
    simp only [Nat.add_eq_left, one_ne_zero] at h11
  }
  have h4 : is_face SC I J1 := by {
    apply parent_simplex_case_BC SC I hs J1 hJ1.1 h3
    intro k2
    rw [hJ1.2]
    apply And.intro
    rw [Fin.le_def, ←add_le_add_iff_right 1, h21 k2]
    exact le_add_one_of_simplex SC I hs (Fin.last n1) 0 k2
    rw [h21 k2]
  }
  use J1
  simp only
  apply And.intro (And.intro hJ1.1 h4)
  intro J2 hJ2
  rw [@same_delete_index_eq_iff SC n1 hn1 _ _ _ (hJ2.1.symm.trans hJ1.1), hJ1.2]
  apply funext
  intro k1
  ext
  have h5 := last_eq_first_add_one SC J2 hJ2.2.2.1 k1
  have h6 : I (Fin.last n1) = J2 (Fin.last SC.n) := by {
    rw [hJ2.1]
    unfold delete_vertex insert_index
    simp only [Fin.val_last, Fin.val_zero, not_lt_zero, ↓reduceIte]
    congr!
  }
  rw [←h6, ←h21 k1] at h5
  omega
}

lemma zero_ne_last {hn1 : n1 + 1 = SC.n} : 0 ≠ Fin.last SC.n := by {
  simp only [ne_eq, Fin.zero_eq_last_iff]
  rw [←hn1]
  omega
}

lemma case_A_not_zero I (h1 : case_A SC I) J
    (h2 : I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J) : False := by {
  have h3 := last_eq_first_add_one SC J h2.2.2.1
  obtain ⟨k1, hk1⟩ := h1
  have h4 : I (Fin.last n1) = J (Fin.last SC.n) := by {
    rw [h2.1]
    unfold delete_vertex insert_index
    simp only [Fin.val_last, Fin.val_zero, not_lt_zero, ↓reduceIte]
    congr!
  }
  apply Nat.zero_ne_add_one (J 0 k1).1
  rw [←h3 k1,← h4,hk1]
  rfl
}

lemma case_ABC_count_disj {hn1 : n1 + 1 = SC.n} I k1 q
    (hABC : ∀ i, I i k1 = q) : Finset.card { J | is_face SC I J}
    = Finset.card {J | I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J}
    + Finset.card {J | I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J} := by {
  have hnd : ¬ case_D SC I := by {
    contrapose! hABC
    exact hABC k1 q
  }
  rw [←Finset.card_union_of_disjoint]
  congr
  ext J
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  apply Iff.intro
  {
    intro h1
    simp only [h1, and_true]
    rw [child_simplex_char] at h1
    obtain ⟨j1, hj1⟩ := h1
    have h2 := @case_D_iff_not_end_2 SC n1 hn1 J h1.2.1 j1
    rw [hj1,h2] at hnd
    have h3 := Decidable.or_iff_not_not_and_not.mpr hnd
    cases' h3 with h3 h3
    rw [hj1,h3]
    exact Or.inl rfl
    rw [hj1,h3]
    exact Or.inr rfl
    · exact hn1
    · exact h1.2.1
  }
  {
    intro h1
    rw [←or_and_right] at h1
    exact h1.2
  }
  apply Finset.disjoint_filter.mpr
  intro J h1 h2 h3
  apply @zero_ne_last SC n1 hn1
  apply @delete_vertex_inj SC n1 hn1 J h2.2.2.1
  rw [←h2.1,←h3.1]
}

lemma case_C_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h1 : case_C SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 2 := by {
  obtain ⟨k1,q, h1⟩  := h1
  have h2 := @case_AC_ex_unique SC n1 hn1 I hs k1 q h1.2 h1.1.2
  have h3 := @case_BC_ex_unique SC n1 hn1 I hs k1 q h1.2 h1.1.1
  rw [Fintype.existsUnique_iff_card_one] at h2 h3
  rw [case_ABC_count_disj SC I k1 q h1.2,h2,h3]
  exact hn1
}

lemma case_B_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h2 : case_B SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 1 := by {
  obtain ⟨k1, h1⟩  := id h2
  have h4 : Fin.last SC.p ≠ 0 := @p_ne_zero_of_cube SC n1 hn1
  have h3 := @case_BC_ex_unique SC n1 hn1 I hs k1 _ h1 h4
  rw [Fintype.existsUnique_iff_card_one] at h3
  rw [case_ABC_count_disj SC I k1 (Fin.last SC.p) h1, h3]
  simp only [Nat.add_eq_left]
  apply Finset.card_filter_eq_zero_iff.mpr
  intro J h5
  apply case_B_not_last SC I h2
  exact hn1
}

lemma case_A_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h2 : case_A SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 1 := by {
  obtain ⟨k1, h1⟩  := id h2
  have h4 : Fin.last SC.p ≠ 0 := @p_ne_zero_of_cube SC n1 hn1
  have h3 := @case_AC_ex_unique SC n1 hn1 I hs k1 _ h1 h4.symm
  rw [Fintype.existsUnique_iff_card_one] at h3
  rw [case_ABC_count_disj SC I k1 0 h1, h3]
  simp only [Nat.add_eq_right]
  apply Finset.card_filter_eq_zero_iff.mpr
  intro J h5
  apply case_A_not_zero SC I h2
  exact hn1
}

end cases_ABCD

-- used in other file
lemma boundary_is_A_or_B {hn1 : n1 + 1 = SC.n} I (hbf : @is_boundary_face SC n1 I)
    : case_A SC I ∨ case_B SC I := by {
  have hs : simplex SC n1 I := by {
    obtain ⟨J,hJ⟩ := hbf
    exact hJ.1.1
  }
  unfold is_boundary_face at hbf
  rw [Fintype.existsUnique_iff_card_one] at hbf
  have h1 := one_of_ABCD SC I
  rw [←or_assoc] at h1
  cases' h1 with h1 h1
  assumption
  cases' h1 with h1 h1
  rw [@case_C_parent_count SC n1 hn1 I hs h1] at hbf
  simp only [OfNat.ofNat_ne_one] at hbf
  rw [@case_D_parent_count SC n1 hn1 I hs h1] at hbf
  simp only [OfNat.ofNat_ne_one] at hbf
}

-- used in other file
lemma case_B_boundary {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I)
    (h1 : case_B SC I) : is_boundary_face SC I :=
  (Fintype.existsUnique_iff_card_one _).mpr (@case_B_parent_count SC n1 hn1 I hs h1)

-- used in other file
lemma parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) :
    Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} ∈ {c | c = 1 ∨ c = 2} := by {
  simp only [Set.mem_ofPred_eq]
  have h1 := one_of_ABCD SC I
  rw [←or_assoc] at h1
  cases' h1 with h1 h1
  left
  cases' h1 with h2 h2
  exact @case_A_parent_count SC n1 hn1 I hs h2
  exact @case_B_parent_count SC n1 hn1 I hs h2
  right
  cases' h1 with h2 h2
  exact @case_C_parent_count SC n1 hn1 I hs h2
  exact @case_D_parent_count SC n1 hn1 I hs h2
}

end

section

open Classical

section completeness

lemma complete_simplex_iff {SC} m I(hs : simplex SC m I) :
    complete_simplex SC m I ↔ ∀ c, c ≤ m → ∃ i, SC.RL (I i) = c := by {
  apply Iff.intro
  {
    intro h1 c hc
    rwa [← Set.mem_range, h1.2, Set.mem_ofPred_eq]
  }
  {
    intro c1
    apply And.intro hs
    refine Set.toFinset_inj.mp ?_
    refine (Finset.eq_iff_card_ge_of_superset ?_).mp ?_
    {
      simp only [Set.toFinset_range, Set.toFinset_subset, Finset.coe_image, Finset.coe_univ,
        Set.image_univ]
      intro c hc
      simp only [Set.mem_range, c1 c hc]
    }
    let f1 := fun (j : ℕ ) ↦ SC.RL (I (Fin.ofNat _ j))
    apply Finset.card_le_card_of_surjOn f1
    intro j h1
    simp only [Set.toFinset_range, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_range] at h1
    obtain ⟨ i, hi⟩ := h1
    use i
    simp only [Set.coe_toFinset, Set.mem_ofPred_eq]
    apply And.intro (Fin.is_le i)
    unfold f1
    rw [← hi]
    simp only [Fin.ofNat_eq_cast, Fin.cast_val_eq_self]
  }
}

lemma rl_inj_of_complete {SC} m I (hcs : complete_simplex SC m I):
    ∀ i1 i2, SC.RL (I i1) = SC.RL (I i2) → i1 = i2 := by {
  let f1 : Fin (m+1) → Fin (m+1) := fun j ↦ Fin.ofNat _ (SC.RL (I j))
  suffices h1 : Function.Injective f1 by {
    intro i1 i2 h2
    apply h1
    unfold f1
    rw [h2]
  }
  have h2 := hcs.2
  apply Function.Surjective.injective_of_finite
  rfl
  rw [complete_simplex_iff _ _ hcs.1] at hcs
  intro c
  obtain ⟨a, ha⟩ := hcs c (Fin.is_le c)
  use a
  unfold f1
  rw [ha]
  exact Fin.cast_val_eq_self c
}

lemma char_complete_face {SC n1 hn1} I J (hs : simplex SC SC.n J) :
    complete_simplex SC n1 I ∧ is_face SC I J
    ↔ ∃ i, I = @delete_vertex SC n1 hn1 i J
    ∧ ∀ (c:ℕ ), c ≤ n1 → ∃ i2, i2 ≠ i ∧ SC.RL (J i2) = c := by {
  apply Iff.intro
  {
    rw [child_simplex_char]
    intro h1
    obtain ⟨i, hi1 ⟩ := h1.2
    use i
    apply And.intro hi1
    intro c hc
    have h2 := (complete_simplex_iff n1 I h1.1.1).mp h1.1 c hc
    obtain ⟨j, hj⟩ := h2
    rw [← hj, hi1]
    unfold delete_vertex
    use @insert_index SC n1 hn1 i j
    apply And.intro _ rfl
    apply insert_index_ne
    exact hn1
    exact hs
  }
  {
    intro h1
    obtain ⟨i, hi1 ⟩ := h1
    have hface : is_face SC I J := by {
      rw [child_simplex_char]
      use i
      exact hi1.1
      exact hs
    }
    apply And.intro _ hface
    rw [complete_simplex_iff n1 I hface.1]
    intro c hc
    obtain ⟨i2, hi2⟩ := hi1.2 c hc
    have h3 := @almost_surjective_of_insert_index SC n1 hn1 i i2 hi2.1
    obtain ⟨j, hj⟩ := h3
    use j
    rw [hi1.1, ← hi2.2, hj]
    rfl
  }
}

lemma complete_child_uniq {SC n1} {hn1 : n1 + 1 = SC.n} J (hcs : complete_simplex SC SC.n J) :
    ∃! (I : Fin (n1+1) → SC.G), complete_simplex SC n1 I ∧ is_face SC I J := by {
  have h4 : ∃ i, SC.RL (J i) = SC.n := by {
    rw [← Set.mem_range, hcs.2]
    simp only [Set.mem_ofPred_eq, le_refl]
  }
  obtain ⟨ i, hi⟩ := h4
  let I := @delete_vertex SC n1 hn1 i J
  have hs2 : simplex SC n1 I := by {
    apply delete_vertex_simplex
    exact hcs.1
  }
  use I
  have h1 : complete_simplex SC n1 I ∧ is_face SC I J := by
  {
    rw [@char_complete_face SC n1 hn1 _ _ hcs.1]
    use i
    apply And.intro rfl
    rw [complete_simplex_iff] at hcs
    {
      intro c hc
      have h3 : c ≤ SC.n := by omega
      obtain ⟨i2, hi2 ⟩ := hcs c h3
      use i2
      apply And.intro _ hi2
      intro h4
      rw [h4, hi, ← hn1] at hi2
      rw [← hi2] at hc
      revert hc
      simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, imp_self]
    }
    {
      exact hcs.1
    }
  }
  simp only
  apply And.intro h1
  intro I2 h2
  rw [@char_complete_face SC n1 hn1 _ _ hcs.1] at h2
  obtain ⟨ i2, hi2 ⟩ := h2
  have h2 : SC.RL (J i2) = SC.n := by {
    let c2 := SC.RL (J i2)
    suffices h3 : ¬ (c2 ≤ n1) by {
      apply le_antisymm (SC.rl_proper (J i2)).1
      omega
    }
    intro h2
    obtain ⟨i3, hi3⟩ := hi2.2 c2 h2
    apply hi3.1
    apply rl_inj_of_complete SC.n J hcs
    exact hi3.2
  }
  suffices h3 : i2 = i by {
    rw [hi2.1, h3]
  }
  apply rl_inj_of_complete SC.n J hcs
  rw [h2]
  exact (Eq.symm hi)
}

lemma incomplete_childs {SC n1} {hn1 : n1 + 1 = SC.n} J (hs : simplex SC SC.n J)
    (hnc : ¬ complete_simplex SC SC.n J):
    Even (Finset.card { I : Fin (n1 + 1) → SC.G | complete_simplex SC n1 I ∧ is_face SC I J}) := by {
  let S : Finset _:= { I : Fin (n1 + 1) → SC.G | complete_simplex SC n1 I ∧ is_face SC I J}
  let c := S.card
  suffices h1 : c > 0 → c = 2 by {
    suffices h2 : Even c by {exact h2}
    by_cases h3 : c > 0
    rw [h1 h3]
    exact even_two
    use 0
    omega
  }
  intro cpos
  have h1 : Finset.Nonempty S := by {
    apply Finset.card_ne_zero.mp
    omega
  }
  obtain ⟨I1, h1 ⟩ := h1
  have hI1S := h1
  unfold S at h1
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1
  obtain ⟨i1, hi1 ⟩ := (@char_complete_face SC n1 hn1 I1 J hs).mp h1
  apply Finset.card_eq_two.mpr
  have h2 : SC.RL (J i1) ≤ n1 := by {
    by_contra h3
    apply hnc
    rw [complete_simplex_iff _ _ hs]
    intro c hc
    by_cases h4 : c ≤ n1
    {
      obtain ⟨i2, hi2 ⟩ := hi1.2 c h4
      use i2
      exact hi2.2
    }
    {
      use i1
      have h6 : c = SC.n := le_antisymm hc (le_of_eq_of_le hn1.symm (not_le.mp h4))
      rw [h6]
      apply le_antisymm (SC.rl_proper (J i1)).1
      exact le_of_eq_of_le hn1.symm (not_le.mp h3)
    }
  }
  obtain ⟨i2, hi2⟩ := hi1.2 (SC.RL (J i1)) h2
  let I2 := @delete_vertex SC n1 hn1 i2 J
  have hI2S : I2 ∈ S := by {
    unfold S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [@char_complete_face SC n1 hn1 I2 J hs]
    use i2
    apply And.intro rfl
    intro c hc
    obtain ⟨i3, hi3⟩ := hi1.2 c hc
    by_cases h4 : i3 = i2
    {
      use i1
      rw [← hi3.2,h4, hi2.2]
      exact And.intro hi2.1.symm rfl
    }
    {
      use i3
      exact And.imp_left (fun a ↦ h4) hi3
    }
  }
  use I1, I2
  apply And.intro
  {
    intro h3
    apply hi2.1
    apply @delete_vertex_inj SC n1 hn1 J hs
    rw [← hi1.1, h3]
  }
  ext I3
  simp only [Finset.mem_insert, Finset.mem_singleton]
  apply Iff.intro
  {
    intro h3
    unfold S at h3
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h3
    have h31 := h3
    rw [@char_complete_face SC n1 hn1 I3 J hs] at h3
    obtain ⟨ i3, hi3 ⟩ := h3
    by_contra h4
    simp only [not_or] at h4
    rw [hi1.1] at h4
    have h7 : ∀ i4, ¬ (I3 = @delete_vertex SC n1 hn1 i4 J) → i4 ≠ i3 := by {
      intro i4 h8 h9
      apply h8
      rw [hi3.1, h9]
    }
    have h5 := @almost_surjective_of_insert_index SC n1 hn1 i3
    obtain ⟨ k1, hk1 ⟩ := h5 i1 (h7 i1 h4.1)
    obtain ⟨ k2, hk2 ⟩ := h5 i2 (h7 i2 h4.2)
    apply hi2.1
    suffices h7 : k1 = k2 by {
      rw [hk1, hk2, h7]
    }
    apply rl_inj_of_complete n1 I3 h31.1
    rw [hi3.1]
    unfold delete_vertex
    rw [← hk1, ← hk2]
    exact hi2.2.symm
  }
  {
    intro h5
    cases h5
    rename_i h9
    rwa [h9]
    rename_i h9
    rwa [h9]
  }
}

lemma complete_boundary_face_last {SC n1} {hn1 : n1 + 1 = SC.n} (I : Fin (n1 + 1) → SC.G)
    (hcbf : complete_boundary_face SC I) :
    ∀ i, ∀ j, j.1 + 1 = SC.n →  (I i j).1 = SC.p := by {
  intro i j hj
  revert i
  have h3 := @boundary_is_A_or_B SC n1 hn1 I hcbf.1
  have h1 : j.1 = n1 := by omega
  have h4 : ∀ n2, n2 ≤ n1 → ∃ i, SC.RL (I i) = n2 := by {
    intro n2 hn2
    rw [← Set.mem_range, hcbf.2.2]
    simp only [Set.mem_ofPred_eq, hn2]
  }
  have h6 (j2 : Fin SC.n) : j2.1 ≤ n1 := by omega
  cases h3
  {
    rename_i h1
    obtain ⟨ j2, hj2⟩ := h1
    exfalso
    obtain ⟨i, hi⟩ := h4 j2.1 (h6 j2)
    have h5 := ((SC.rl_proper (I i)).2 j2).1 (hj2 i)
    exact h5 hi
  }
  {
    rename_i h1
    obtain ⟨ j2, hj2⟩ := h1
    have hj3 i : (I i j2).1 = SC.p := by {
      rw [hj2 i]
      exact Fin.val_last SC.p
    }
    suffices h3 : j = j2 by {
      intro i
      rw [h3, hj3 i]
    }
    have h3 := SC.rl_proper
    obtain ⟨i, hi⟩ := h4 n1 (Nat.le_refl n1)
    have h5 := ((SC.rl_proper (I i)).2 j2).2 (hj3 i)
    rw [hi] at h5
    ext
    rw [h1]
    exact Nat.le_antisymm h5 (h6 j2)
  }
}

end completeness

section handshake

variable {A B : Type*}
variable [Fintype A] [Fintype B]

lemma handshake_3 (r : A → B → Prop) (c : A → Prop)
    (h1 : ∀ a, c a ↔ Odd (Finset.card {b | r a b}))
    : Odd (Finset.card {a | c a}) ↔ Odd (∑ a, Finset.card {b | r a b}) := by {
  rw [Finset.odd_sum_iff_odd_card_odd]
  rw [iff_eq_eq]
  congr
  ext a
  exact h1 a
}

lemma handshake_2 (r : A → B → Prop)
    (c : A → Prop) (d : B → Prop)
    (h1 : ∀ a, c a ↔ Odd (Finset.card {b | r a b}))
    (h2 : ∀ b, d b ↔ Odd (Finset.card {a | r a b})) :
    Odd (Finset.card {a | c a}) → Odd (Finset.card {b | d b}) := by {
  intro h3
  have h5 : ∑ a, Finset.card {b | r a b} = ∑ b, Finset.card {a | r a b} := by {
    apply Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
  }
  let r2 b a := r a b
  rw [handshake_3 r2 d h2, ←h5]
  rwa [←handshake_3 r c h1]
}

lemma handshake_1 (r : A → B → Prop)
    (c1 c2 c3: A → Prop) (d1 d2: B → Prop)
    (h1 : ∀ b, d1 b → ∃! a, c2 a ∧ r a b)
    (h2 : ∀ b, d2 b → ¬ d1 b → Even (Finset.card { a | c2 a ∧ r a b}))
    (h3 : ∀ a, c3 a → Finset.card { b | r a b} ∈ {c | c = 1 ∨ c = 2})
    (h5 : ∀ a, c1 a ↔ (∃! b, r a b) ∧ c2 a)
    (h6 : ∀ a, c2 a → c3 a) (h7 : ∀ b, ∀ a, r a b → d2 b)
    : Odd (Finset.card {a : A | c1 a}) → Odd (Finset.card {b : B | d1 b}) := by {
  let r2 a b := c2 a ∧ r a b
  apply handshake_2 r2
  {
    intro a
    rw [h5]
    by_cases p1 : c2 a
    unfold r2
    simp only [p1, and_true, true_and]
    rw [Fintype.existsUnique_iff_card_one]
    apply Iff.intro
    {
      intro p2
      use 0
      rwa [mul_zero, zero_add]
    }
    {
      intro p2
      have p3 := h3 a (h6 a p1)
      simp only [Set.mem_ofPred_eq] at p3
      cases p3
      rename_i p4
      exact p4
      rename_i p4
      rw [p4] at p2
      exfalso
      revert p2
      simp only [imp_false, Nat.not_odd_iff_even, even_two]
    }
    {
      unfold r2
      simp only [p1, and_false, false_and, Finset.filter_false, Finset.card_empty, Nat.not_odd_zero]
    }
  }
  {
    intro b
    by_cases p1 : d1 b
    {
      simp only [p1, true_iff]
      use 0
      rw [mul_zero, zero_add]
      rw [← Fintype.existsUnique_iff_card_one]
      exact h1 b p1
    }
    {
      simp only [p1, false_iff]
      intro p2
      have p5 : Finset.Nonempty {a | r2 a b} := by {
        have p3 : Odd (Finset.card { a | r2 a b}) := by {
          convert p2
        }
        apply Finset.card_ne_zero.mp
        intro p4
        revert p3
        rw [p4]
        simp only [Nat.not_odd_zero, imp_self]
      }
      have p3 : d2 b := by {
        obtain ⟨a, p6⟩ := p5
        apply h7 b a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at p6
        exact p6.2
      }
      revert p2
      have p4 := h2 b p3 p1
      simp only [imp_false, Nat.not_odd_iff_even]
      convert p4
    }
  }
}

end handshake

lemma odd_of_boundary_faces SC {n1} {hn1 : n1 + 1 = SC.n}:
    Odd (Finset.card { I : Fin (n1 + 1) → SC.G | complete_boundary_face SC I})
    → Odd (Finset.card { I | complete_simplex SC SC.n I}) := by {
  apply handshake_1 (is_face SC)
  apply @complete_child_uniq SC n1 hn1
  apply @incomplete_childs SC n1 hn1
  apply @parent_count SC n1 hn1
  {
    intro I
    rfl
  }
  exact fun _ h1 ↦ h1.1
  exact fun _ _ h1 ↦ h1.2.1
}

section induction_step

variable (SC : SpernerCube)
variable {n1 : ℕ}

def child_map (v : Fin n1 → Fin (SC.p+1) ) : SC.G := fun i ↦
  match n1 with
  | 0 => Fin.last SC.p
  | Nat.succ _ => if i.1 + 1 = SC.n then Fin.last SC.p else v (Fin.ofNat _ i.1)

lemma child_map_last (v : Fin n1 → Fin (SC.p +1 ))
    : ∀ j, j.1 + 1 = SC.n → child_map SC v j = SC.p := by {
  intro j hj
  unfold child_map
  cases n1
  rfl
  simp only [hj, ↓reduceIte, Fin.val_last]
}

lemma child_map_applied [NeZero SC.n] {hn1 : n1 + 1 = SC.n} (v : Fin n1 → Fin (SC.p + 1))
    : ∀ (i : Fin n1), child_map SC v (Fin.ofNat _ i.1) = v i := by {
  intro i
  dsimp only [child_map]
  cases n1
  exact Fin.elim0 i
  rename_i n2
  simp only [Nat.succ_eq_add_one]
  have h5 : i.1 + 1 < SC.n := by omega
  have h2 : i.1 < SC.n := by omega
  have h3 := Fin.val_cast_of_lt h2
  rw [Fin.ofNat_eq_cast, h3]
  have h6 : i.1 + 1 ≠ SC.n := by omega
  simp only [h6, ↓reduceIte, Fin.ofNat_eq_cast, Fin.cast_val_eq_self]
}

lemma child_map_inj {hn1 : n1 + 1 = SC.n }: Function.Injective (@child_map SC n1) := by {
  intro v1 v2 h1
  ext i
  have h0 : NeZero SC.n := by {
    rw [← hn1]
    exact instNeZeroNatHAdd_1
  }
  rw [← child_map_applied SC v1]
  rw [← child_map_applied SC v2]
  rwa [h1]
  exact hn1
}

lemma child_map_surj_on {hn1 : n1 + 1 = SC.n} w
    (h1 : ∀ j, j.1 + 1 = SC.n → w j = SC.p)
    : ∃ v, @child_map SC n1 v = w := by {
  have h0 : NeZero SC.n := by {
    rw [← hn1]
    exact instNeZeroNatHAdd_1
  }
  let v2 : Fin n1 → Fin (SC.p +1) := fun i ↦ w (Fin.ofNat _ i.1)
  use v2
  apply funext
  intro i
  unfold child_map
  cases n1
  {
    simp only
    have h2 := h1 0
    simp only [Fin.val_zero, zero_add] at h2 hn1
    have h3 : i = 0 := by {
      have h4 := i.2
      simp only [← hn1] at h4
      ext
      simp only [Fin.val_zero]
      exact Nat.lt_one_iff.mp h4
    }
    rw [h3]
    exact Fin.eq_of_val_eq (id (Eq.symm (h2 hn1)))
  }
  {
    rename_i n2
    have h2 := h1 i
    by_cases h3 : i.1 +1 = SC.n
    {
      simp only [h3, ↓reduceIte]
      exact Eq.symm (Fin.eq_of_val_eq (h1 i h3))
    }
    simp only [h3, ↓reduceIte, Nat.succ_eq_add_one]
    unfold v2
    congr
    simp only [Fin.ofNat_eq_cast]
    rw [Fin.val_cast_of_lt]
    exact Fin.cast_val_eq_self i
    have h4 := i.2
    simp only [← hn1] at h3 h4
    omega
  }
}

def child_cube {hn1 : n1 + 1 = SC.n}: SpernerCube where
  n := n1
  p := SC.p
  RL := fun v ↦ SC.RL (child_map SC v)
  rl_proper := by {
    intro v
    have h0 : NeZero SC.n := by {
      rw [← hn1]
      exact instNeZeroNatHAdd_1
    }
    have h1 := child_map_last SC v
    have h2 := SC.rl_proper (child_map SC v)
    apply And.intro
    {
      have h3 := (h2.2 (Fin.ofNat _ n1)).2
      have h4 : n1 < SC.n := by omega
      simp only [Fin.ofNat_eq_cast] at h3
      rw [Fin.val_cast_of_lt h4] at h3
      apply h3
      apply child_map_last
      rw [Fin.val_cast_of_lt h4]
      exact hn1
    }
    intro i
    have h3 := h2.2 (Fin.ofNat _ i.1)
    rw [child_map_applied] at h3
    have h4 : (Fin.ofNat SC.n i.1).1 = i.1 := by {
      apply Fin.val_cast_of_lt
      omega
    }
    rwa [h4] at h3
    exact hn1
  }

end induction_step

lemma induction_start (SC : SpernerCube) (h0 : 0 = SC.n)
    : Odd (Finset.card { I | complete_simplex SC SC.n I}) := by {
  use 0
  simp only [mul_zero, zero_add]
  rw [←Fintype.existsUnique_iff_card_one]
  let b : SC.G := fun _ ↦ 0
  let a : Fin (SC.n + 1) → SC.G := fun _ ↦ b
  use a
  simp only
  have h1 (x : Fin (SC.n+1)) : x = 0 := by {
    ext
    simp only [Fin.val_zero]
    rw [← Nat.lt_one_iff]
    apply Fin.val_lt_of_le x
    rw [←h0]
  }
  have hf (j : Fin SC.n) : False := by {
    apply Fin.elim0
    rwa [h0]
  }
  apply And.intro
  apply And.intro
  apply And.intro
  {
    intro x1 x2 _
    rw [h1 x1, h1 x2]
  }
  {
    intro i hi j
    exact False.elim ( hf j )
  }
  {
    ext i
    simp only [← h0]
    simp only [Set.mem_range, nonpos_iff_eq_zero, Set.ofPred_eq_eq_singleton, Set.mem_singleton_iff]
    have h3 : ∀ c, SC.RL (a c) = 0 := by {
      intro c
      have h2 := (SC.rl_proper (a c)).1
      simp only [← h0] at h2
      omega
    }
    apply Iff.intro
    {
      intro h2
      cases h2
      rename_i c hc
      rw [h3 c] at hc
      exact (Eq.symm hc)
    }
    {
      intro hi0
      use 0
      rw [hi0]
      exact h3 0
    }
  }
  {
    intro a2 h2
    ext i
    apply funext
    intro j
    exact False.elim ( hf j )
  }
}

theorem strong_cubical_sperner (k: ℕ ) : ∀ (SC : SpernerCube), k = SC.n →
    Odd (Finset.card { I | complete_simplex SC SC.n I}) := by {
  induction' k with k hind
  {
    intro SC hk
    exact induction_start SC hk
  }
  {
    intro SC1 hk1
    apply @odd_of_boundary_faces SC1 k hk1
    let SC2 := @child_cube SC1 k hk1
    have hnz : NeZero SC1.n := by {
      rw [← hk1]
      exact instNeZeroNatHAdd_1
    }
    have h2 : Odd (Finset.card { I : Fin (k+1) → SC2.G | complete_simplex SC2 SC2.n I}) :=
      hind SC2 rfl
    apply Eq.mpr _ h2
    apply congrArg
    let f1 : SC2.G → SC1.G := child_map SC1
    let f2 : (Fin (k+1)→ SC2.G) → (Fin (k+1)→ SC1.G) := fun a ↦ fun b ↦ f1 (a b)
    have hf1inj : Function.Injective f1 := by {
      apply child_map_inj SC1
      rw [← hk1]
      rfl
    }
    symm
    have hcomp I : complete_boundary_face SC1 (f2 I) ↔ complete_simplex SC2 SC2.n I := by {
      unfold complete_boundary_face complete_simplex
      have h_last j k: j.1 + 1 = SC1.n → f2 I k j = SC1.p := by {
        apply child_map_last
      }
      have h_bf : simplex SC1 k (f2 I) ↔ is_boundary_face SC1 (f2 I) ∧ simplex SC1 k (f2 I):= by {
        simp only [iff_and_self]
        intro hs
        apply @case_B_boundary SC1 k hk1
        exact hs
        use (Fin.ofNat _ k)
        intro i
        ext
        apply h_last
        simp [← hk1]
      }
      rw [← and_assoc, ←h_bf]
      have h3 : SC2.n = k := rfl
      apply and_congr
      apply and_congr
      {
        apply Iff.intro
        {
          intro h4 i1 i2 h5
          exact h4 (congrArg f1 h5)
        }
        {
          intro h4 i1 i2 h5
          apply h4
          apply hf1inj h5
        }
      }
      {
        simp only [h3]
        apply forall₂_congr
        intro i hi1
        apply Iff.intro
        {
          intro h4 j
          have h6 k : (f2 I k (Fin.ofNat _ j.1)) = (I k j) := by {
            unfold f2
            apply child_map_applied
            rw [← hk1]
            rfl
          }
          have h7 := h4 (Fin.ofNat _ j.1)
          rw [h6, h6, h6, h6] at h7
          exact h7
        }
        {
          intro h4 j
          by_cases h5 : j.1 + 1 = SC1.n
          {
            rw [h_last, h_last, h_last, h_last]
            simp only [le_refl, le_add_iff_nonneg_right, zero_le,
              and_self]
            repeat' exact h5
          }
          {
            have h7 : j.1 < SC2.n := by {
              rw [h3]
              have h6 := j.2
              simp only [← hk1] at h5 h6
              omega
            }
            have hn02 : NeZero SC2.n := by {
              exact NeZero.of_gt hi1
            }
            let j2 : Fin SC2.n := (Fin.ofNat _ j.1)
            have h8 : j = (Fin.ofNat _ j2.1) := by {
              unfold j2
              simp only [Fin.ofNat_eq_cast,]
              rw [Fin.val_cast_of_lt]
              exact Eq.symm (Fin.cast_val_eq_self j)
              exact h7
            }
            have h6 k : (f2 I k j) = (I k j2) := by {
              unfold f2
              rw [h8]
              apply child_map_applied
              exact hk1
            }
            rw [h6, h6, h6, h6]
            exact h4 j2
          }
        }
      }
      exact Eq.congr_right rfl
    }
    apply Finset.card_nbij f2
    {
      intro I hI
      have hI' : complete_simplex SC2 SC2.n I :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp hI)).2
      exact Finset.mem_coe.mpr
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hcomp I).mpr hI'⟩)
    }
    {
      intro I1 h41 I2 h42 h5
      ext i
      apply hf1inj
      exact congrFun h5 i
    }
    {
      simp only [Finset.coe_filter, Finset.mem_univ, true_and]
      intro J
      simp only [Set.mem_ofPred_eq, Set.mem_image]
      intro h3
      have h4 : ∃ I, f2 I = J := by {
        suffices h6 : ∀ i, ∃ ii, f1 ii = J i by {
          obtain ⟨I, h5⟩  := axiomOfChoice h6
          use I
          ext i
          exact h5 i
        }
        intro i
        have h5 := @child_map_surj_on SC1 k hk1
        apply h5
        exact @complete_boundary_face_last SC1 k hk1 J h3 i
      }
      obtain ⟨I, h4⟩ := h4
      use I
      simp only [h4, and_true]
      exact Set.mem_ofPred.mpr ((hcomp I).mp (h4 ▸ h3))
    }
  }

}

theorem weaker_cubical_sperner SC : ∃ I, complete_simplex SC SC.n I := by {
  have h1 := strong_cubical_sperner SC.n SC rfl
  obtain ⟨k1, hk1⟩ := h1
  have h2 : 0 < 2 * k1 + 1 := by omega
  rw [←hk1, Finset.card_pos] at h2
  obtain ⟨I, hI1⟩ := h2
  use I
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hI1
  exact hI1
}

end

section

open Classical

/-
shows the fixed-point theorem for the unit cube
by applying the cubical sperner's lemma
-/

variable {n : ℕ}

def unit_cube := { v : Fin n → ℝ | 0 ≤ v ∧ v ≤ 1 }

noncomputable def rl_point {f : @unit_cube n → @unit_cube n} (x : @unit_cube n) : ℕ :=
  match (Finset.min { i | (f x).1 i < x.1 i ∨ x.1 i = 1}) with
    | some k => k.1
    | none => n

lemma reduced_label_props_1 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n)
    : @rl_point n f x ≤ n ∧ ∀ k,
    (@rl_point n f x = k.1 → (f x).1 k < x.1 k ∨ x.1 k = 1)
    ∧ ((f x).1 k < x.1 k ∨ x.1 k = 1 → @rl_point n f x ≤ k.1) := by {
  let s : Finset (Fin n) := {i | (f x).1 i < x.1 i ∨ x.1 i = 1}
  let minval := Finset.min s
  let rlp := match minval with
    | some k => k.1
    | none => n
  by_cases he : s = ∅
  {
    have h1 : @rl_point n f x = n := by {
      show rlp = n
      unfold rlp minval
      rw [he]
      simp only [Finset.min_empty]
    }
    rw [h1]
    simp only [le_refl, true_and]
    intro k
    have h2 : n ≠ k.1 := by omega
    simp only [h2, IsEmpty.forall_iff, true_and]
    intro h3
    have h4 : k ∈ s := by {
      unfold s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h3
    }
    rw [he] at h4
    simp only [Finset.notMem_empty] at h4
  }
  have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
  obtain ⟨m, hm⟩ := Finset.min_of_nonempty hne
  have h1 : @rl_point n f x = m.1 := by {
    show rlp = m.1
    unfold rlp minval
    rw [hm]
  }
  rw [h1]
  simp only [Fin.is_le', Fin.val_fin_le, true_and]
  intro k1
  apply And.intro
  {
    intro h2
    suffices h3 : k1 ∈ s by {
      unfold s at h3
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h3
      exact h3
    }
    apply Finset.mem_of_min
    rw [hm]
    simp only [WithTop.coe_eq_coe]
    ext
    exact h2
  }
  {
    intro h2
    have h3 : k1 ∈ s := by {
      unfold s
      simp only [Finset.mem_filter, Finset.mem_univ, h2, and_self]
    }
    exact Finset.min_le_of_eq h3 hm
  }
}

lemma reduced_label_props_2 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n)
    : @rl_point n f x ≤ n ∧
    ∀ k, (x.1 k = 0 → @rl_point n f x ≠ k.1) ∧ (x.1 k = 1 → @rl_point n f x ≤ k.1):= by {
  have h1 := reduced_label_props_1 f x
  apply And.intro h1.1
  intro k
  apply And.intro
  {
    intro h2 h3
    have h4 := (h1.2 k).1 h3
    rw [h2] at h4
    simp only [zero_ne_one, or_false] at h4
    contrapose! h4
    exact (f x).2.1 k
  }
  {
    intro h2
    apply (h1.2 k).2
    exact Or.inr h2
  }
}

lemma reduced_label_props_3 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n) (k : Fin n)
    : (@rl_point n f x = k → (f x).1 k ≤ x.1 k) ∧ (@rl_point n f x > k → (f x).1 k ≥ x.1 k) := by {
  have h1 := (reduced_label_props_1 f x).2 k
  apply And.intro
  {
    intro h2
    cases h1.1 h2
    (expose_names; exact le_of_lt h)
    rename_i h3
    rw [h3]
    exact (f x).2.2 k
  }
  {
    contrapose!
    intro h2
    apply h1.2
    exact Or.inl h2
  }
}

noncomputable def discrete_map (p : ℕ ) (v : Fin n → Fin (p+1)) : @unit_cube n :=
  ⟨ fun i ↦ ((v i).1 : ℝ ) / p , by {
    unfold unit_cube
    simp only [Set.mem_ofPred_eq]
    rw [Pi.le_def, Pi.le_def, ←forall_and]
    intro i
    simp only [Pi.zero_apply, Pi.one_apply]
    apply And.intro
    exact div_nonneg (Nat.cast_nonneg' ↑(v i)) (Nat.cast_nonneg' p)
    apply div_le_one_of_le₀ ?_ (Nat.cast_nonneg' p)
    simp only [Nat.cast_le]
    exact Fin.is_le (v i)
  }⟩

noncomputable def sperner_cube_of_function (f : @unit_cube n → @unit_cube n)
  (p : ℕ ) {ppos : 0 < p} : SpernerCube where
  n := n
  p := p
  RL := fun v ↦ @rl_point _ f (discrete_map p v)
  rl_proper := by {
    intro v
    let x := discrete_map p v
    have h1 := reduced_label_props_2 f x
    apply And.intro h1.1
    intro k
    apply And.intro
    {
      intro h2
      apply (h1.2 k).1
      unfold x discrete_map
      simp only [div_eq_zero_iff, Nat.cast_eq_zero, Fin.val_eq_zero_iff]
      exact Or.inl h2
    }
    {
      intro h2
      apply (h1.2 k).2
      unfold x discrete_map
      simp only [h2]
      refine (div_eq_one_iff_eq ?_).mpr rfl
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    }
  }

lemma dist_discrete_map p (ppos: 0 < p) (v1 v2 : Fin n → Fin (p+1))
    (h1 : ∀ k, (v1 k).1 ≤ (v2 k).1 + 1 ∧ (v2 k).1 ≤ (v1 k).1 + 1) :
    dist (discrete_map p v1) (discrete_map p v2) ≤ 1 / p := by {
  let x1 := (discrete_map p v1).1
  let x2 := (discrete_map p v2).1
  show dist x1 x2 ≤ 1 / p
  refine (dist_pi_le_iff ?_).mpr ?_
  simp only [one_div, inv_nonneg, Nat.cast_nonneg]
  intro k
  have hx1 : x1 k = (v1 k).1 / p := by {rfl}
  have hx2 : x2 k = (v2 k).1 / p := by {rfl}
  rw [hx1, hx2]
  rw [Real.dist_eq, abs_sub_le_iff]
  have h1k := (h1 k).1
  have h2k := (h1 k).2
  apply And.intro
  repeat {
    rw [sub_le_iff_le_add', ← add_div]
    have ppos2 : 0 < (p : ℝ) := Nat.cast_pos'.mpr ppos
    rwa [div_le_div_iff_of_pos_right ppos2, ←Nat.cast_add_one, Nat.cast_le]
  }
}

lemma nearby_points (f : @unit_cube n → @unit_cube n) (p0:ℕ):
    ∃ x0 : @unit_cube n, ∀ k, (f x0).1 k ≥ x0.1 k ∧
    ∃ xk : @unit_cube n, dist x0 xk ≤ 1 / ↑(p0 +1) ∧ (f xk).1 k ≤ xk.1 k := by {
  let p := p0 + 1
  have ppos : 0 < p := by omega
  let SC := @sperner_cube_of_function n f p ppos
  obtain ⟨I, h3⟩ := weaker_cubical_sperner SC
  have h4 j : j ≤ n → ∃ i, SC.RL (I i) = j := by {
    intro h4
    exact h3.2.symm.subset h4
  }
  obtain ⟨i0, hi0⟩ := h4 n (Nat.le_refl n)
  let x0 := discrete_map SC.p (I i0)
  use x0
  intro k
  apply And.intro
  {
    apply (reduced_label_props_3 f x0 k).2
    have h6 : @rl_point _ f x0 = n := by exact hi0
    rw [h6]
    simp only [gt_iff_lt, Fin.is_lt]
  }
  obtain ⟨ik, hik⟩ := h4 k.1 k.is_le'
  let xk := discrete_map SC.p (I ik)
  use xk
  apply And.intro _ $ (reduced_label_props_3 f xk k).1 hik
  unfold x0 xk
  apply dist_discrete_map p ppos
  have h5 := le_add_one_of_simplex SC I h3.1
  intro k
  exact ⟨h5 i0 ik k, h5 ik i0 k⟩
}

theorem fixed_point_unit_cube (f : C(@unit_cube n, @unit_cube n)) : ∃ x, f x = x := by {
  obtain ⟨x0s, hx0⟩ := axiomOfChoice (nearby_points f)
  have hc1 : ∃ xx : @unit_cube n, ∃ (φ:ℕ → ℕ ), StrictMono φ ∧
      Filter.Tendsto (x0s ∘ φ ) Filter.atTop (nhds xx) := by {
    have hc1 : IsCompact (@unit_cube n) := isCompact_Icc
    let x0 : ℕ → Fin n → ℝ := fun i ↦ (x0s i).1
    have h2 : ∀ i, x0 i ∈ unit_cube := fun i ↦ (x0s i).2
    obtain ⟨a, ⟨ha, ⟨φ,h3⟩ ⟩ ⟩ := hc1.isSeqCompact h2
    use ⟨a, ha⟩
    use φ
    exact And.intro h3.1 $ tendsto_subtype_rng.mpr h3.2
  }
  obtain ⟨xxx, ⟨φ, h2⟩ ⟩ := hc1
  let y0 := x0s ∘ φ
  let g : Fin n → @unit_cube n → ℝ := fun k x ↦ x.1 k
  have hc2 k : Continuous (g k) := by {
    exact (continuous_apply k).comp continuous_subtype_val
  }
  have h3 k : xxx.1 k ≤ (f xxx).1 k := by {
    show g k xxx ≤ g k (f xxx)
    have h6 :=  (hc2 k).seqContinuous h2.2
    have h7 := (hc2 k).seqContinuous $ f.2.seqContinuous h2.2
    apply le_of_tendsto_of_tendsto' h6 h7
    exact fun i ↦ (hx0 (φ i) k).1
  }
  have h4 k : (f xxx).1 k ≤ xxx.1 k := by {
    show g k (f xxx) ≤ g k xxx
    have h5 n:= (hx0 (φ n) k).2
    obtain ⟨yk, h6⟩ := axiomOfChoice h5
    have h4 : Filter.Tendsto yk Filter.atTop (nhds xxx) := by {
      apply tendsto_of_tendsto_of_dist h2.2
      have h7 := @tendsto_one_div_add_atTop_nhds_zero_nat ℝ _ _ _ _
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h7 _
      {
        intro i
        apply le_trans (h6 i).1
        simp only [Nat.cast_add, Nat.cast_one, one_div]
        apply inv_anti₀ (Nat.cast_add_one_pos i)
        simp only [add_le_add_iff_right, Nat.cast_le, h2.1.le_apply]
      }
      exact fun _ ↦ dist_nonneg
    }
    have h7 := (hc2 k).seqContinuous h4
    have h8 := (hc2 k).seqContinuous $ f.2.seqContinuous h4
    apply le_of_tendsto_of_tendsto' h8 h7
    exact fun i ↦ (h6 i).2
  }
  use xxx
  ext k
  apply le_antisymm (h4 k) (h3 k)
}

end

section

/-
some helper lemmas involving homeomorphisms.
-/

lemma homeo_unit_ball {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s: Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s)
    (hni : (interior s).Nonempty):
    Nonempty (s ≃ₜ Metric.closedBall (0: V) 1) := by {
  have h1 := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hcvx hni
  have h2 : Bornology.IsBounded s := IsCompact.isBounded hcmpct
  cases (h1 h2)
  rename_i e he
  have h4 := closure_eq_iff_isClosed.mpr (IsCompact.isClosed hcmpct)
  have e2 := Homeomorph.image e s
  rw [h4] at he
  rw [he.2.1] at e2
  exact Nonempty.intro e2
}

theorem homeo_of_finrank_eq {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (hreq : Module.finrank ℝ V = Module.finrank ℝ W) :
    Nonempty (Metric.closedBall (0: V) 1 ≃ₜ Metric.closedBall (0: W) 1) := by {
  have L := ContinuousLinearEquiv.ofFinrankEq hreq
  let pL := L ⁻¹' (Metric.closedBall (0:W) 1)
  have hpL : pL = L.toHomeomorph ⁻¹' (Metric.closedBall (0:W) 1) := rfl
  have h4 : Convex ℝ pL := Convex.linear_preimage (convex_closedBall 0 1) L.toLinearMap
  have h5 : IsCompact pL := by {
    rw [hpL,Homeomorph.isCompact_preimage]
    exact isCompact_closedBall 0 1
  }
  have h6 : (interior pL).Nonempty := by {
    rw [hpL, ← Homeomorph.preimage_interior]
    refine (Function.Surjective.nonempty_preimage ?_).mpr ?_
    exact Homeomorph.surjective L.toHomeomorph
    use 0
    rw [interior_closedBall]
    {simp only [Metric.mem_ball, dist_self, zero_lt_one]}
    {exact Ne.symm (zero_ne_one' ℝ)}
  }
  have e1 : pL ≃ₜ Metric.closedBall (0:W) 1 := by {
    rw [hpL]
    exact L.toHomeomorph.sets hpL
  }
  have h7 := homeo_unit_ball _ h4 h5 h6
  cases h7
  rename_i e2
  apply Nonempty.intro
  exact e2.symm.trans e1
}

lemma unit_cube_homeo_unit_ball {n}
    : Nonempty (Set.Icc (0 : Fin n → ℝ) 1 ≃ₜ Metric.closedBall (0 : Fin n → ℝ) 1 ) := by
  apply homeo_unit_ball _ (convex_Icc 0 1) isCompact_Icc
  have h1 : Set.Icc (0 : Fin n → ℝ) 1 = Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1) := by
    ext x; simp [Set.mem_Icc, Pi.le_def]
  rw [h1, interior_pi_set Set.finite_univ]
  exact Set.univ_pi_nonempty_iff.mpr fun _ => by
    rw [interior_Icc]; exact ⟨1/2, by norm_num, by norm_num⟩

lemma homeo_unit_cube_of_convex_compact {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s: Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : s.Nonempty)
    : ∃ k, Nonempty (s ≃ₜ Set.Icc (0 : Fin k → ℝ) 1) := by {
  have := hne.coe_sort
  let W := affineSpan ℝ s
  obtain ⟨ps, hps⟩ := hne
  let pss : W := ⟨ps, mem_affineSpan ℝ hps⟩
  let g2 := AffineIsometryEquiv.constVSub ℝ pss
  let g1 : W → V := fun x ↦ x.1
  let s2 := g1 ⁻¹' s
  let s3 := g2.symm ⁻¹' s2
  have h32 : Convex ℝ s3 := by {
    exact hcvx.affine_preimage
      ((affineSpan ℝ s).subtype.comp
      (AffineIsometryEquiv.constVSub ℝ pss).symm.toAffineMap)
  }
  have h34 : (interior s3).Nonempty := by {
    refine (Convex.interior_nonempty_iff_affineSpan_eq_top h32).mpr ?_
    unfold s3
    rw [←AffineIsometryEquiv.coe_toAffineEquiv]
    rw [← AffineSubspace.comap_span]
    rw [affineSpan_coe_preimage_eq_top]
    rfl
  }
  let g3 := g1.comp g2.symm
  have h4 : Topology.IsEmbedding g3 := by {
    apply Topology.IsEmbedding.subtypeVal.comp g2.symm.toHomeomorph.isEmbedding
  }
  have h5 : Set.MapsTo g3 s3 s := by {
    intro w h1
    unfold s3 s2 at h1
    rwa [Set.mem_preimage, Set.mem_preimage] at h1
  }
  have h6 : Function.Surjective (Set.MapsTo.restrict g3 s3 s h5) := by {
    refine (Set.MapsTo.restrict_surjective_iff h5).mpr ?_
    refine Set.SurjOn.comp_right ?_ ?_
    exact AffineIsometryEquiv.surjective g2.symm
    intro v h1
    refine (Set.mem_image g1 (g1 ⁻¹' s) v).mpr ?_
    have h11 : v ∈ affineSpan ℝ s := mem_affineSpan ℝ h1
    use ⟨v, h11⟩
    simp only [Set.mem_preimage]
    apply And.intro h1 rfl
  }
  let e1 := (h4.restrict h5).toHomeomorphOfSurjective h6
  have h31 : IsCompact s3 := by {
    have h51 : _ → IsCompact Set.univ := (Homeomorph.isCompact_image e1).mp
    simp only [Set.image_univ, EquivLike.range_eq_univ] at h51
    apply isCompact_iff_isCompact_univ.mpr
    apply h51 $ isCompact_iff_isCompact_univ.mp hcmpct
  }
  obtain ⟨e2⟩ := homeo_unit_ball s3 h32 h31 h34
  let k := Module.finrank ℝ W.direction
  obtain ⟨e3⟩ := @unit_cube_homeo_unit_ball k
  have h2 : k = Module.finrank ℝ (Fin k → ℝ) := (Module.finrank_fin_fun ℝ).symm
  obtain ⟨e4⟩ := homeo_of_finrank_eq h2
  let e5 := (e1.symm.trans e2).trans (e4.trans e3.symm)
  use k
  exact Nonempty.intro e5
}

end

section

/- Brouwer fixed-point theorem:
Every continuous function mapping a nonempty compact convex set to itself has a fixed point
(the set should be a subset of a finite dimensional vector space).

https://en.wikipedia.org/wiki/Brouwer_fixed-point_theorem
-/

theorem brouwer_fixed_point {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    : ∀ (s : Set V), Convex ℝ s → IsCompact s → Set.Nonempty s →
    ∀ (f : C(s, s)), ∃ x, f x = x := by {
  intro s hcvx hcmpct hne f
  obtain ⟨k, ⟨e⟩ ⟩ := homeo_unit_cube_of_convex_compact s hcvx hcmpct hne
  let g := (toContinuousMap e).comp (f.comp (toContinuousMap e.symm))
  obtain ⟨y, hy⟩ := @fixed_point_unit_cube k g
  use (toContinuousMap e.symm) y
  have h1 : e.symm (e (f (e.symm y))) = e.symm y := congrArg e.symm hy
  rwa [e.symm_apply_apply] at h1
}

end
section
/-! Compatibility lemmas for porting from a newer Lean core. -/

theorem ite_eq_right {c : Prop} {_ : Decidable c} {α : Sort*} {a b : α} (h : ¬ c) :
    (if c then a else b) = b := if_neg h

theorem ite_eq_left {c : Prop} {_ : Decidable c} {α : Sort*} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h

end

-- OAI.LinearAlgebra.SpectralBooks.Crossing
section
/-!
# Expanding a restriction of a power of a direct sum of wires

A wire is given by the sum of the coordinate basis tensors indexed by its possible
bit strings. Direct sum tags those basis tensors at every site, while tensor power
takes tuples of independently chosen basis tensors. We expand arbitrary local linear
images of these tensors into an ordinary sum of networks with the same output legs.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace Crossing

noncomputable section

variable {I : Type*} [Fintype I] {F : Type*} [CommSemiring F]

/-- An ordered description of an unoriented wire between distinct sites. -/
structure Wire (I : Type*) where
  left : I
  right : I
  distinct : left ≠ right
  width : ℕ

/-- A local index has one bit per wire bit at an endpoint and no bits elsewhere. -/
abbrev Wire.Leg (e : Wire I) (i : I) :=
  {_t : Fin e.width // i = e.left ∨ i = e.right} → Bool

/-- Coefficients of a tensor presented as a finite sum of coordinate basis tensors. -/
def basisTensor {A : I → Type*} {S : Type*} [Fintype S]
    (term : S → ∀ i, A i) (x : ∀ i, A i) : F :=
  ∑ s, if x = term s then 1 else 0

/-- The matrix-coefficient definition of restriction by local linear maps. -/
def IsRestriction {A B : I → Type*} [∀ i, Fintype (A i)]
    (X : (∀ i, B i) → F) (Y : (∀ i, A i) → F) : Prop :=
  ∃ M : ∀ i, B i → A i → F, ∀ x,
    X x = ∑ a, Y a * ∏ i, M i (x i) (a i)

/-- Applying matrices to a sum of basis tensors sums the transformed pure tensors. -/
theorem restriction_basisTensor_iff {A B : I → Type*} [∀ i, Fintype (A i)]
    {S : Type*} [Fintype S] (term : S → ∀ i, A i) (X : (∀ i, B i) → F) :
    IsRestriction X (basisTensor term) ↔
      ∃ M : ∀ i, B i → A i → F, ∀ x, X x = ∑ s, ∏ i, M i (x i) (term s i) := by
  unfold IsRestriction basisTensor
  congr! 3 with M x
  simp_rw [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

end
end Crossing

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.SiteTensor.Restriction
section
/-!
# Composition and reindexing of tensor restrictions
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor

open Crossing

variable {I : Type*} [Fintype I] {F : Type*} [CommSemiring F]
variable {A B C : I → Type*} [∀ i, Fintype (A i)]

/-- Relabeling the coordinate basis at each site gives a restriction. -/
theorem restrict_of_equiv {X : (∀ i, B i) → F} {Y : (∀ i, A i) → F}
    (e : ∀ i, B i ≃ A i) (h : ∀ x, X x = Y (fun i => e i (x i))) :
    IsRestriction X Y := by
  classical
  refine ⟨fun i b a => if a = e i b then 1 else 0, fun x => ?_⟩
  rw [h x]
  simp_rw [Fintype.prod_boole]
  have heq (a : ∀ i, A i) : (∀ i, a i = e i (x i)) ↔ a = fun i => e i (x i) :=
    funext_iff.symm
  simp [heq, mul_ite]

/-- Identity matrices give the reflexive restriction. -/
theorem restrict_refl (X : (∀ i, A i) → F) : IsRestriction X X :=
  restrict_of_equiv (fun i => Equiv.refl (A i)) fun _ => rfl

/-- Local matrix multiplication composes two restrictions. -/
theorem restrict_trans [∀ i, Fintype (B i)] {X : (∀ i, C i) → F}
    {Y : (∀ i, B i) → F} {Z : (∀ i, A i) → F}
    (hXY : IsRestriction X Y) (hYZ : IsRestriction Y Z) : IsRestriction X Z := by
  classical
  obtain ⟨M, hM⟩ := hXY
  obtain ⟨N, hN⟩ := hYZ
  refine ⟨fun i c a => ∑ b, N i b a * M i c b, fun x => ?_⟩
  rw [hM x]
  simp_rw [hN, Finset.sum_mul, Fintype.prod_sum, Finset.mul_sum, Finset.prod_mul_distrib,
    mul_assoc]
  exact Finset.sum_comm

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.SiteTensor.Raw
section
/-! # Finite coefficient tensors and local restriction

The coordinate type at each site is arbitrary and finite. Keeping the local
types in the format lets the tensor product use pairs of basis indices and the
direct sum use disjoint unions. Mutual restriction identifies changes of basis
and redundant local dimensions.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

universe v u w

/-- A finite local format, together with the tensor's coefficients. -/
structure Raw (I : Type u) (K : Type w) where
  Leg : I → Type v
  finiteLeg : ∀ i, Fintype (Leg i)
  coeff : (∀ i, Leg i) → K

instance Raw.instFintypeLeg {I : Type u} {K : Type w} (X : Raw.{v} I K) (i : I) :
    Fintype (X.Leg i) := X.finiteLeg i

namespace Raw

variable {I : Type u} {K : Type w}

noncomputable section
open scoped Classical

/-- Restriction by one matrix at each site, expressed in the chosen bases. -/
abbrev Restricts [Fintype I] [CommSemiring K] (X Y : Raw.{v} I K) :=
  Crossing.IsRestriction X.coeff Y.coeff

/-- The equivalence relation used to form the tensor semiring. -/
def Equivalent [Fintype I] [CommSemiring K] (X Y : Raw.{v} I K) : Prop :=
  X.Restricts Y ∧ Y.Restricts X

/-- Mutual restriction is a setoid by composition of local matrices. -/
def setoid (I : Type u) (K : Type w) [Fintype I] [CommSemiring K] : Setoid (Raw.{v} I K) where
  r := Equivalent
  iseqv := ⟨fun X => ⟨restrict_refl X.coeff, restrict_refl X.coeff⟩,
    fun h => And.symm h, fun h g => ⟨restrict_trans h.1 g.1, restrict_trans g.2 h.2⟩⟩

/-- Relabeling each coordinate basis by a bijection preserves mutual restriction. -/
theorem reindex_equivalent [Fintype I] [CommSemiring K] {X Y : Raw.{v} I K}
    (e : ∀ i, X.Leg i ≃ Y.Leg i) (h : ∀ x, X.coeff x = Y.coeff (fun i => e i (x i))) :
    X.Equivalent Y := by
  refine ⟨restrict_of_equiv e h, restrict_of_equiv (fun i => (e i).symm) ?_⟩
  intro y
  simpa using (h (fun i => (e i).symm (y i))).symm

/-- The empty local format represents the additive identity. -/
def zero (I : Type u) (K : Type w) [Zero K] : Raw.{v} I K :=
  ⟨fun _ => PEmpty, fun _ => inferInstance, fun _ => 0⟩

/-- The scalar unit has one basis vector at each site. -/
def one (I : Type u) (K : Type w) [One K] : Raw.{v} I K :=
  ⟨fun _ => PUnit, fun _ => inferInstance, fun _ => 1⟩

/-- Tensor multiplication groups the two local factors at each site. -/
def mul [Mul K] (X Y : Raw.{v} I K) : Raw.{v} I K :=
  ⟨fun i => X.Leg i × Y.Leg i, fun _ => inferInstance,
    fun x => X.coeff (fun i => (x i).1) * Y.coeff (fun i => (x i).2)⟩

/-- The common-label diagonal, with one summand per label. -/
def diagonal (I : Type u) (K : Type w) (α : Type v) [Fintype α] [CommSemiring K] : Raw.{v} I K :=
  ⟨fun _ => α, fun _ => inferInstance, fun x => ∑ a : α, if x = fun _ => a then 1 else 0⟩

end
end Raw

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.Spectrum
section
/-!
# Compactness of the normalized spectrum

The direct sum and tensor product of restriction classes give a semiring. It suffices here that
each class is a restriction of a natural number, represented by a diagonal tensor. We view a
point as a function into the nonnegative reals with the topology of pointwise convergence.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Set NNReal

variable {S : Type*} [Semiring S]

/-- Normalized restriction-monotone semiring homomorphisms, as their pointwise evaluations. -/
def normalizedSpectrum (restricts : S → S → Prop) : Set (S → ℝ≥0) :=
  {f | f 0 = 0 ∧ f 1 = 1 ∧ (∀ x y, f (x + y) = f x + f y) ∧
    (∀ x y, f (x * y) = f x * f y) ∧ ∀ x y, restricts x y → f x ≤ f y}

/-- A spectral point preserves the semiring operations. -/
def normalizedSpectrum.toRingHom {restricts : S → S → Prop}
    (f : normalizedSpectrum restricts) : S →+* ℝ≥0 where
  toFun := f.1
  map_zero' := f.2.1
  map_one' := f.2.2.1
  map_add' := f.2.2.2.1
  map_mul' := f.2.2.2.2.1

/-- Pointwise limits preserve all the spectral axioms, including every restriction comparison. -/
theorem isClosed_normalizedSpectrum (restricts : S → S → Prop) :
    IsClosed (normalizedSpectrum restricts) := by
  have hmono : IsClosed {f : S → ℝ≥0 | ∀ x y, restricts x y → f x ≤ f y} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ isClosed_iInter fun _ ↦
      isClosed_le (continuous_apply x) (continuous_apply y)
  exact (isClosed_setOfPred_map_zero S ℝ≥0).inter <|
    (isClosed_setOfPred_map_one S ℝ≥0).inter <|
    (isClosed_setOfPred_map_add S ℝ≥0).inter ((isClosed_setOfPred_map_mul S ℝ≥0).inter hmono)

/-- Finite tensor rank bounds every coordinate of the normalized spectrum. -/
theorem isCompact_normalizedSpectrum (restricts : S → S → Prop)
    (hfinite : ∀ x : S, ∃ r : ℕ, restricts x r) : IsCompact (normalizedSpectrum restricts) := by
  choose r hr using hfinite
  apply IsCompact.of_isClosed_subset
    (isCompact_univ_pi (fun x ↦ isCompact_Icc (a := (0 : ℝ≥0)) (b := (r x : ℝ≥0))))
    (isClosed_normalizedSpectrum restricts)
  intro f hf x _
  have hle := hf.2.2.2.2 x _ (hr x)
  have hcast : f (r x : S) = (r x : ℝ≥0) := map_natCast (normalizedSpectrum.toRingHom ⟨f, hf⟩) _
  exact ⟨bot_le, hle.trans_eq hcast⟩

/-- On any tensor admitting a restriction to the unit, normalized logarithmic price is
continuous on the entire spectrum. -/
theorem continuous_log_price {restricts : S → S → Prop} {x : S} (hx : restricts 1 x) :
    Continuous (fun f : normalizedSpectrum restricts ↦ Real.logb 2 (f.val x : ℝ)) := by
  apply (continuous_subtype_val.comp ((continuous_apply x).comp continuous_subtype_val)).logb
  intro f
  have hone := f.2.2.2.2.2 1 x hx
  rw [f.2.2.1] at hone
  change (f.val x : ℝ) ≠ 0
  exact_mod_cast (zero_lt_one.trans_le hone).ne'

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.SiteSpectrum
section
/-!
# Finite-party diagonal bounds and simultaneous extension constraints

Each coordinate tensor is a restriction of the full diagonal indexed by its
coordinate positions. Conversely a nonzero coefficient supplies a restriction
to the scalar unit. The resulting bounds give compactness for spectral
evaluations, which lets the old tensor prices in a site extension be prescribed
simultaneously once every finite list can be matched.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical NNReal
noncomputable section

section

namespace Crossing

variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
variable {B : I → Type*} [∀ i, Fintype (B i)]

/-- Expand a tensor in the local coordinate bases. A common diagonal label
selects the entire coordinate tuple. A distinguished site supplies its coefficient. -/
theorem restricts_from_coordinate_diagonal_equiv {L : Type*} [Fintype L]
    (e : L ≃ (∀ i, B i)) (T : (∀ i, B i) → K) :
    IsRestriction T (basisTensor (I := I) (fun (l : L) _ ↦ l)) := by
  classical
  let o : I := Classical.choice inferInstance
  let M (i : I) (b : B i) (a : ∀ i, B i) : K :=
    (if b = a i then 1 else 0) * (if i = o then T a else 1)
  apply (restriction_basisTensor_iff _ _).mpr
  refine ⟨fun i b l ↦ M i b (e l), fun b ↦ ?_⟩
  have hprod (a : ∀ i, B i) :
      (∏ i, M i (b i) a) = if b = a then T a else 0 := by
    simp only [M, Finset.prod_mul_distrib, Fintype.prod_boole, ← funext_iff]
    simp
  rw [e.sum_comp (fun a ↦ ∏ i, M i (b i) a)]
  simp [hprod]

/-- A single nonzero coefficient makes the scalar unit a local linear image. -/
theorem unit_restricts_of_nonzero {T : (∀ i, B i) → K} (h : T ≠ 0) :
    IsRestriction (fun _ : I → PUnit ↦ (1 : K)) T := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, T a ≠ 0 := by
    by_contra! hn
    exact h (funext hn)
  let o : I := Classical.choice inferInstance
  let M (i : I) (_ : PUnit) (b : B i) : K :=
    (if b = a i then 1 else 0) * (if i = o then (T a)⁻¹ else 1)
  refine ⟨M, fun _ ↦ ?_⟩
  have hprod (b : ∀ i, B i) :
      (∏ i, M i PUnit.unit (b i)) = if b = a then (T a)⁻¹ else 0 := by
    simp only [M, Finset.prod_mul_distrib, Fintype.prod_boole, ← funext_iff]
    simp
  simp [hprod, mul_ite, ha]

end Crossing

namespace SiteTensor.Raw

universe v

/-- A concrete diagonal of finite size supplies every coefficient array,
even if the coordinate spaces and the set of sites use different universes. -/
theorem restricts_diagonal (I : Type*) [Fintype I] [Nonempty I]
    {K : Type*} [Field K] (X : Raw.{v} I K) :
    X.Restricts (diagonal I K (ULift.{v} (Fin (Fintype.card (∀ i, X.Leg i))))) := by
  classical
  let e : ULift.{v} (Fin (Fintype.card (∀ i, X.Leg i))) ≃ (∀ i, X.Leg i) :=
    Equiv.ulift.trans (Fintype.equivFin _).symm
  have h := Crossing.restricts_from_coordinate_diagonal_equiv e X.coeff
  unfold Crossing.basisTensor at h
  convert! h using 1
  funext x
  simp only [diagonal]
  congr 1
  funext a
  split_ifs <;> simp_all

/-- Conversely the multiplicative unit is a restriction of every nonzero tensor. -/
theorem one_restricts_of_nonzero {I : Type*} [Fintype I] [Nonempty I]
    {K : Type*} [Field K] (X : Raw.{v} I K) (h : X.coeff ≠ 0) :
    (one I K).Restricts X :=
  Crossing.unit_restricts_of_nonzero h

end SiteTensor.Raw

end

end

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.SiteTensor.Product
section
/-!
# Products preserve tensor restriction

The site matrices for two restrictions act on paired basis indices by their
Kronecker products.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor

variable {I F : Type*} [Fintype I] [CommSemiring F]
  {A B C D : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

/-- The tensor product of two local restrictions is a local restriction. -/
theorem restrict_product
    {X : (∀ i, A i) → F} {Y : (∀ i, B i) → F}
    {X' : (∀ i, C i) → F} {Y' : (∀ i, D i) → F}
    (hX : Crossing.IsRestriction X' X) (hY : Crossing.IsRestriction Y' Y) :
    Crossing.IsRestriction
      (fun a : ∀ i, C i × D i => X' (fun i => (a i).1) * Y' (fun i => (a i).2))
      (fun a : ∀ i, A i × B i => X (fun i => (a i).1) * Y (fun i => (a i).2)) := by
  classical
  obtain ⟨M, hM⟩ := hX
  obtain ⟨N, hN⟩ := hY
  refine ⟨fun i x a => M i x.1 a.1 * N i x.2 a.2, fun x => ?_⟩
  dsimp
  rw [hM, hN, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow I A B).symm _ _ fun a => ?_
  simp only [Finset.prod_mul_distrib]
  ac_rfl

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.SiteTensor.SumDef
section
/-! # Direct sums in coordinates

The direct sum of tensors extends their coefficient functions by zero along the
two summand inclusions at every site and adds the resulting coefficients.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor

noncomputable section

variable {X Y Z K : Type*} [Fintype X]

/-- Push coefficients forward by summing on fibers. -/
def pushCoeff [AddCommMonoid K] (f : X → Y) (T : X → K) (y : Y) : K :=
  ∑ x, if f x = y then T x else 0

/-- Successive pushes sum over the fibers of the composite. -/
theorem pushCoeff_comp [AddCommMonoid K] [Fintype Y]
    (g : Y → Z) (f : X → Y) (T : X → K) :
    pushCoeff g (pushCoeff f T) = pushCoeff (g ∘ f) T := by
  funext z
  unfold pushCoeff
  have hs (y : Y) : (if g y = z then ∑ x, if f x = y then T x else 0 else 0) =
      ∑ x, if g y = z then if f x = y then T x else 0 else 0 := by
    by_cases h : g y = z <;> simp [h]
  simp_rw [hs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (f x)]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · simp

/-- Fiberwise summation preserves addition. -/
theorem pushCoeff_add [AddCommMonoid K] (f : X → Y) (T U : X → K) :
    pushCoeff f (T + U) = pushCoeff f T + pushCoeff f U := by
  funext y
  simp only [pushCoeff, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  split <;> simp

/-- A bijection transports each coefficient to its new index. -/
theorem pushCoeff_equiv [AddCommMonoid K] (e : X ≃ Y) (T : X → K) (y : Y) :
    pushCoeff e T y = T (e.symm y) := by
  simp [pushCoeff, ← e.eq_symm_apply]

/-- Contracting a pushed tensor pulls the test coefficients back. -/
theorem sum_pushCoeff_mul [Semiring K] [Fintype Y] (f : X → Y) (T : X → K) (g : Y → K) :
    ∑ y, pushCoeff f T y * g y = ∑ x, T x * g (f x) := by
  simp only [pushCoeff, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

variable {I : Type*} [Fintype I] {A B : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [AddCommMonoid K]

/-- Block direct sum, with a copy of the summand label at every site. -/
def sumCoeff (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) (y : ∀ i, A i ⊕ B i) : K :=
  pushCoeff (fun x i => Sum.inl (x i)) T y + pushCoeff (fun x i => Sum.inr (x i)) U y

/-- The all-left block carries the first tensor. -/
theorem sumCoeff_inl [Nonempty I] (T : (∀ i, A i) → K) (U : (∀ i, B i) → K)
    (x : ∀ i, A i) : sumCoeff T U (fun i => Sum.inl (x i)) = T x := by
  have hl (y : ∀ i, A i) : (fun i => (Sum.inl (y i) : A i ⊕ B i)) =
      (fun i => Sum.inl (x i)) ↔ y = x := by
    simp [funext_iff]
  have hr (y : ∀ i, B i) : (fun i => (Sum.inr (y i) : A i ⊕ B i)) ≠
      (fun i => Sum.inl (x i)) := by
    intro h
    cases congrFun h (Classical.arbitrary I)
  simp [sumCoeff, pushCoeff, hl, hr]

/-- The all-right block carries the second tensor. -/
theorem sumCoeff_inr [Nonempty I] (T : (∀ i, A i) → K) (U : (∀ i, B i) → K)
    (x : ∀ i, B i) : sumCoeff T U (fun i => Sum.inr (x i)) = U x := by
  have hr (y : ∀ i, B i) : (fun i => (Sum.inr (y i) : A i ⊕ B i)) =
      (fun i => Sum.inr (x i)) ↔ y = x := by
    simp [funext_iff]
  have hl (y : ∀ i, A i) : (fun i => (Sum.inl (y i) : A i ⊕ B i)) ≠
      (fun i => Sum.inr (x i)) := by
    intro h
    cases congrFun h (Classical.arbitrary I)
  simp [sumCoeff, pushCoeff, hl, hr]

/-- Every mixed block has zero coefficient. -/
theorem sumCoeff_mixed (T : (∀ i, A i) → K) (U : (∀ i, B i) → K)
    (y : ∀ i, A i ⊕ B i)
    (hl : ∀ x : ∀ i, A i, (fun i => Sum.inl (x i)) ≠ y)
    (hr : ∀ x : ∀ i, B i, (fun i => Sum.inr (x i)) ≠ y) :
    sumCoeff T U y = 0 := by
  simp [sumCoeff, pushCoeff, hl, hr]

end

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.SiteTensor.Ops
section
/-! # Direct sum of finite coefficient tensors -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor.Raw

universe v u w

variable {I : Type u} {K : Type w} [Fintype I]

/-- The direct sum uses a disjoint union at every site. -/
noncomputable def add [AddCommMonoid K] (X Y : Raw.{v} I K) : Raw.{v} I K :=
  ⟨fun i => X.Leg i ⊕ Y.Leg i, fun _ => inferInstance, sumCoeff X.coeff Y.coeff⟩

/-- Tensoring the local restricting maps restricts a product. -/
theorem mul_restricts [CommSemiring K] {X Y U V : Raw.{v} I K}
    (h : X.Restricts Y) (h' : U.Restricts V) : (X.mul U).Restricts (Y.mul V) :=
  restrict_product h h'

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.SiteTensor.Quotient
section
/-! # Tensor classes ordered by restriction

Mutual restriction identifies precisely those tensors with the same upper and lower
bounds in the local restriction preorder.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

universe v u w

/-- Finite site tensors up to mutual restriction. -/
def TensorClass (I : Type u) (K : Type w) [Fintype I] [CommSemiring K] :=
  Quotient (Raw.setoid.{v} I K)

variable {I : Type u} {K : Type w} [Fintype I] [CommSemiring K]

/-- Pass a coefficient tensor to its class under mutual restriction. -/
def ofRaw (X : Raw.{v} I K) : TensorClass.{v} I K :=
  Quotient.mk _ X

@[simp] theorem ofRaw_eq_iff {X Y : Raw.{v} I K} :
    ofRaw X = ofRaw Y ↔ X.Equivalent Y := Quotient.eq

instance : LE (TensorClass.{v} I K) where
  le := Quotient.lift₂ Raw.Restricts fun _ _ _ _ hX hY => propext
    ⟨fun h => restrict_trans hX.2 (restrict_trans h hY.1),
     fun h => restrict_trans hX.1 (restrict_trans h hY.2)⟩

@[simp] theorem ofRaw_le_iff {X Y : Raw.{v} I K} :
    ofRaw X ≤ ofRaw Y ↔ X.Restricts Y := Iff.rfl

instance : PartialOrder (TensorClass.{v} I K) where
  le_refl X := Quotient.inductionOn X fun x => restrict_refl x.coeff
  le_trans X Y Z := Quotient.inductionOn₃ X Y Z fun _ _ _ => restrict_trans
  le_antisymm X Y := Quotient.inductionOn₂ X Y fun _ _ h g => Quotient.sound ⟨h, g⟩

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.SiteTensor.Sum
section
/-! # Direct sums preserve tensor restrictions -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor

open Crossing

variable {I : Type*} [Fintype I] {K : Type*} [CommSemiring K]
variable {A B C D : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    [∀ i, Fintype (C i)] [∀ i, Fintype (D i)]

omit [∀ i, Fintype (C i)] in
/-- Pushing output indices after a restriction sums the rows of each local matrix
over the corresponding fibers. -/
theorem pushCoeff_restriction {X : (∀ i, B i) → K} {T : (∀ i, A i) → K}
    (M : ∀ i, B i → A i → K)
    (hM : ∀ x, X x = ∑ a, T a * ∏ i, M i (x i) (a i))
    (f : ∀ i, B i → C i) (y : ∀ i, C i) :
    pushCoeff (fun x i => f i (x i)) X y =
      ∑ a, T a * ∏ i, ∑ b, if f i b = y i then M i b (a i) else 0 := by
  simp only [Fintype.prod_sum, Finset.mul_sum, Fintype.prod_ite_zero, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  unfold pushCoeff
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hM x, funext_iff]
  split <;> simp [*]

/-- Apply the two given restrictions on their respective diagonal blocks. -/
theorem restrict_sum {X : (∀ i, B i) → K} {Y : (∀ i, D i) → K}
    {T : (∀ i, A i) → K} {U : (∀ i, C i) → K}
    (h : IsRestriction X T) (h' : IsRestriction Y U) :
    IsRestriction (sumCoeff X Y) (sumCoeff T U) := by
  obtain ⟨M, hM⟩ := h
  obtain ⟨N, hN⟩ := h'
  let L (i : I) : B i ⊕ D i → A i ⊕ C i → K
    | .inl b, .inl a => M i b a
    | .inr d, .inr c => N i d c
    | _, _ => 0
  refine ⟨L, fun y => ?_⟩
  simp only [sumCoeff, add_mul, Finset.sum_add_distrib, sum_pushCoeff_mul]
  rw [pushCoeff_restriction M hM, pushCoeff_restriction N hN]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => congrArg (T a * ·) ?_
    refine Finset.prod_congr rfl fun i _ => ?_
    cases y i <;> simp [L]
  · refine Finset.sum_congr rfl fun c _ => congrArg (U c * ·) ?_
    refine Finset.prod_congr rfl fun i _ => ?_
    cases y i <;> simp [L]

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.SiteTensor.AddLaws
section
/-!
# Relabeling laws for direct sums of site tensors
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor

variable {I K : Type*} [Fintype I] [AddCommMonoid K]
variable {A B C : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [∀ i, Fintype (C i)]

private theorem pushCoeff_relabel {X Y Z : Type*} [Fintype X]
    (e : Y ≃ Z) (f : X → Y) (g : X → Z) (h : ∀ x, e (f x) = g x)
    (T : X → K) (y : Y) : pushCoeff f T y = pushCoeff g T (e y) := by
  classical
  unfold pushCoeff
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← h, e.injective.eq_iff]

private theorem pushCoeff_add_apply {X Y : Type*} [Fintype X]
    (f : X → Y) (T U : X → K) (y : Y) :
    pushCoeff f (fun x => T x + U x) y = pushCoeff f T y + pushCoeff f U y :=
  congrFun (pushCoeff_add f T U) y

/-- Interchanging the two summands interchanges their tags at every site. -/
theorem sumCoeff_comm (T : (∀ i, A i) → K) (U : (∀ i, B i) → K)
    (x : ∀ i, A i ⊕ B i) :
    sumCoeff T U x = sumCoeff U T (fun i => Equiv.sumComm _ _ (x i)) := by
  let e := Equiv.piCongrRight fun i => Equiv.sumComm (A i) (B i)
  unfold sumCoeff
  rw [add_comm]
  exact congrArg₂ (· + ·) (pushCoeff_relabel e _ _ (fun _ => rfl) U x)
    (pushCoeff_relabel e _ _ (fun _ => rfl) T x)

/-- Reassociating three direct summands reassociates their tags site by site. -/
theorem sumCoeff_assoc (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) (V : (∀ i, C i) → K)
    (x : ∀ i, (A i ⊕ B i) ⊕ C i) :
    sumCoeff (sumCoeff T U) V x =
      sumCoeff T (sumCoeff U V) (fun i => Equiv.sumAssoc _ _ _ (x i)) := by
  let e := Equiv.piCongrRight fun i => Equiv.sumAssoc (A i) (B i) (C i)
  unfold sumCoeff
  simp_rw [pushCoeff_add_apply, pushCoeff_comp, add_assoc]
  exact congrArg₂ (· + ·) (pushCoeff_relabel e _ _ (fun _ => rfl) T x)
    (congrArg₂ (· + ·) (pushCoeff_relabel e _ _ (fun _ => rfl) U x)
      (pushCoeff_relabel e _ _ (fun _ => rfl) V x))

/-- Adding the tensor with empty local bases on the right preserves coefficients. -/
theorem sumCoeff_zero [∀ i, IsEmpty (B i)] (T : (∀ i, A i) → K) (x : ∀ i, A i ⊕ B i) :
    sumCoeff T (0 : (∀ i, B i) → K) x = T (fun i => Equiv.sumEmpty _ _ (x i)) := by
  let e := Equiv.piCongrRight fun i => Equiv.sumEmpty (A i) (B i)
  unfold sumCoeff
  rw [pushCoeff_relabel e _ (Equiv.refl _) (fun _ => rfl) T, pushCoeff_equiv]
  simp only [pushCoeff, Pi.zero_apply, ite_self, Finset.sum_const_zero, add_zero]
  rfl

/-- Adding the tensor with empty local bases on the left preserves coefficients. -/
theorem zero_sumCoeff [∀ i, IsEmpty (A i)] (U : (∀ i, B i) → K) (x : ∀ i, A i ⊕ B i) :
    sumCoeff (0 : (∀ i, A i) → K) U x = U (fun i => Equiv.emptySum _ _ (x i)) := by
  rw [sumCoeff_comm, sumCoeff_zero]
  rfl

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.SiteTensor.MulLaws
section
/-! # Multiplication laws for finite tensors up to mutual restriction -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor.Raw

variable {I K : Type*} [Fintype I] [CommSemiring K]

/-- The tensor product is associative after relabeling the paired bases. -/
theorem mul_assoc_equivalent (X Y Z : Raw I K) :
    ((X.mul Y).mul Z).Equivalent (X.mul (Y.mul Z)) := by
  apply reindex_equivalent (fun _ => Equiv.prodAssoc _ _ _)
  intro x
  apply mul_assoc

/-- Swapping the local product factors commutes the tensor product. -/
theorem mul_comm_equivalent (X Y : Raw I K) :
    (X.mul Y).Equivalent (Y.mul X) := by
  apply reindex_equivalent (fun _ => Equiv.prodComm _ _)
  intro x
  apply mul_comm

/-- Dropping the singleton basis index identifies a unit product with its other factor. -/
theorem one_mul_equivalent (X : Raw I K) : ((one I K).mul X).Equivalent X := by
  apply reindex_equivalent (fun _ => Equiv.punitProd _)
  intro x
  apply one_mul

/-- Tensoring with the empty tensor gives an empty basis at each site. -/
theorem zero_mul_equivalent [Nonempty I] (X : Raw I K) :
    ((zero I K).mul X).Equivalent (zero I K) := by
  apply reindex_equivalent (fun _ => Equiv.pemptyProd _)
  intro x
  exact (x (Classical.arbitrary I)).1.elim

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.SiteTensor.Distrib
section
/-! # Tensor product distributes over the direct sum

The relabeling at each site sends a paired index with a left (respectively,
right) tag to a left (respectively, right) tagged pair. All sites must choose
the same tag for a coefficient of the direct sum to contribute.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

variable {I K : Type*} [Fintype I] [Nonempty I] [CommSemiring K]
  {A B C : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [∀ i, Fintype (C i)]

/-- Left distributivity of the coefficient tensor product over the direct
sum, up to the canonical relabeling at each site. -/
theorem sumCoeff_product_distrib (T : (∀ i, A i) → K) (U : (∀ i, B i) → K)
    (V : (∀ i, C i) → K) (x : ∀ i, A i × (B i ⊕ C i)) :
    T (fun i => (x i).1) * sumCoeff U V (fun i => (x i).2) =
      sumCoeff (fun y : ∀ i, A i × B i => T (fun i => (y i).1) * U (fun i => (y i).2))
        (fun y : ∀ i, A i × C i => T (fun i => (y i).1) * V (fun i => (y i).2))
        (fun i => Equiv.prodSumDistrib _ _ _ (x i)) := by
  classical
  let u (i : I) := (x i).1
  let v (i : I) := (x i).2
  change T u * sumCoeff U V v = sumCoeff _ _ (fun i => Equiv.prodSumDistrib _ _ _ (u i, v i))
  generalize v = w
  by_cases hl : ∃ y : ∀ i, B i, (fun i => Sum.inl (y i)) = w
  · obtain ⟨y, rfl⟩ := hl
    simp only [Equiv.prodSumDistrib_apply_left, sumCoeff_inl]
  by_cases hr : ∃ y : ∀ i, C i, (fun i => Sum.inr (y i)) = w
  · obtain ⟨y, rfl⟩ := hr
    simp only [Equiv.prodSumDistrib_apply_right, sumCoeff_inr]
  have hleft (z : ∀ i, A i × B i) :
      (fun i => Sum.inl (z i)) ≠ (fun i => Equiv.prodSumDistrib _ _ _ (u i, w i)) := by
    intro eq
    refine hl ⟨fun i => (z i).2, funext fun i => ?_⟩
    have h := congrArg (fun t => ((Equiv.prodSumDistrib (A i) (B i) (C i)).symm t).2)
      (congrFun eq i)
    simpa using h
  have hright (z : ∀ i, A i × C i) :
      (fun i => Sum.inr (z i)) ≠ (fun i => Equiv.prodSumDistrib _ _ _ (u i, w i)) := by
    intro eq
    refine hr ⟨fun i => (z i).2, funext fun i => ?_⟩
    have h := congrArg (fun t => ((Equiv.prodSumDistrib (A i) (B i) (C i)).symm t).2)
      (congrFun eq i)
    simpa using h
  rw [sumCoeff_mixed _ _ _ (not_exists.mp hl) (not_exists.mp hr),
    sumCoeff_mixed _ _ _ hleft hright, mul_zero]

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.TensorSemiring
section
/-! # The semiring of tensors up to mutual restriction

The sites, coefficient semiring, and finite coordinate spaces at each site
are arbitrary. Addition is the block direct sum and multiplication is the
tensor product grouped at each site. Both operations preserve local restriction.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

universe v u w

variable {I : Type u} {K : Type w} [Fintype I] [CommSemiring K]

noncomputable section

instance : Add (TensorClass.{v} I K) where
  add := Quotient.map₂ Raw.add fun _ _ h _ _ g =>
    ⟨restrict_sum h.1 g.1, restrict_sum h.2 g.2⟩

instance : Mul (TensorClass.{v} I K) where
  mul := Quotient.map₂ Raw.mul fun _ _ h _ _ g =>
    ⟨Raw.mul_restricts h.1 g.1, Raw.mul_restricts h.2 g.2⟩

instance : Zero (TensorClass.{v} I K) := ⟨ofRaw (Raw.zero I K)⟩
instance : One (TensorClass.{v} I K) := ⟨ofRaw (Raw.one I K)⟩

@[simp] theorem ofRaw_add (X Y : Raw.{v} I K) : ofRaw (X.add Y) = ofRaw X + ofRaw Y := rfl

@[simp] theorem ofRaw_mul (X Y : Raw.{v} I K) : ofRaw (X.mul Y) = ofRaw X * ofRaw Y := rfl

@[simp] theorem ofRaw_zero : ofRaw (Raw.zero.{v} I K) = 0 := rfl

@[simp] theorem ofRaw_one : ofRaw (Raw.one.{v} I K) = 1 := rfl

private theorem class_add_comm (X Y : TensorClass.{v} I K) : X + Y = Y + X :=
  Quotient.inductionOn₂ X Y fun x y => Quotient.sound <|
    Raw.reindex_equivalent (fun _ => Equiv.sumComm _ _) (sumCoeff_comm x.coeff y.coeff)

private theorem class_zero_add (X : TensorClass.{v} I K) : 0 + X = X := by
  let (i : I) : IsEmpty ((Raw.zero.{v} I K).Leg i) := inferInstanceAs (IsEmpty PEmpty)
  exact
  Quotient.inductionOn X fun x => Quotient.sound <|
    Raw.reindex_equivalent (fun _ => Equiv.emptySum _ _) (zero_sumCoeff x.coeff)

private theorem class_mul_comm (X Y : TensorClass.{v} I K) : X * Y = Y * X :=
  Quotient.inductionOn₂ X Y fun x y => Quotient.sound (x.mul_comm_equivalent y)

private theorem class_one_mul (X : TensorClass.{v} I K) : 1 * X = X :=
  Quotient.inductionOn X fun x => Quotient.sound (x.one_mul_equivalent)

variable [Nonempty I]

private theorem class_zero_mul (X : TensorClass.{v} I K) : 0 * X = 0 :=
  Quotient.inductionOn X fun x => Quotient.sound (x.zero_mul_equivalent)

private theorem class_left_distrib (X Y Z : TensorClass.{v} I K) :
    X * (Y + Z) = X * Y + X * Z :=
  Quotient.inductionOn₃ X Y Z fun x y z => Quotient.sound <|
    Raw.reindex_equivalent (fun _ => Equiv.prodSumDistrib _ _ _)
      (sumCoeff_product_distrib x.coeff y.coeff z.coeff)

/-- The restriction classes form the tensor semiring of the manuscript. -/
instance : CommSemiring (TensorClass.{v} I K) where
  add_assoc X Y Z := Quotient.inductionOn₃ X Y Z fun x y z => Quotient.sound <|
    Raw.reindex_equivalent (fun _ => Equiv.sumAssoc _ _ _) (sumCoeff_assoc x.coeff y.coeff z.coeff)
  add_comm := class_add_comm
  zero_add := class_zero_add
  add_zero X := (class_add_comm X 0).trans (class_zero_add X)
  nsmul := nsmulRec
  mul_assoc X Y Z := Quotient.inductionOn₃ X Y Z fun x y z =>
    Quotient.sound (x.mul_assoc_equivalent y z)
  mul_comm := class_mul_comm
  one_mul := class_one_mul
  mul_one X := (class_mul_comm X 1).trans (class_one_mul X)
  zero_mul := class_zero_mul
  mul_zero X := (class_mul_comm X 0).trans (class_zero_mul X)
  left_distrib := class_left_distrib
  right_distrib X Y Z := by rw [class_mul_comm, class_left_distrib, class_mul_comm Z X, class_mul_comm Z Y]

omit [Nonempty I] in
/-- Both arguments of block direct sum are monotone under restriction. -/
theorem add_mono {X Y U V : TensorClass.{v} I K} (h : X ≤ Y) (g : U ≤ V) :
    X + U ≤ Y + V := by
  induction X using Quotient.inductionOn
  induction Y using Quotient.inductionOn
  induction U using Quotient.inductionOn
  induction V using Quotient.inductionOn
  exact restrict_sum h g

omit [Nonempty I] in
/-- Both arguments of tensor product are monotone under restriction. -/
theorem mul_mono {X Y U V : TensorClass.{v} I K} (h : X ≤ Y) (g : U ≤ V) :
    X * U ≤ Y * V := by
  induction X using Quotient.inductionOn
  induction Y using Quotient.inductionOn
  induction U using Quotient.inductionOn
  induction V using Quotient.inductionOn
  exact Raw.mul_restricts h g

end
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.SiteTensor.Nonzero
section
/-! # Nonzero tensors up to restriction -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

universe v u w

variable {I : Type u} [Fintype I] {K : Type w}

section Semiring

variable [CommSemiring K]

/-- The zero tensor is a restriction of every tensor. -/
theorem zero_le_tensor [Nonempty I] (X : TensorClass.{v} I K) : 0 ≤ X := by
  induction X using Quotient.inductionOn with
  | h x =>
    change (Raw.zero I K).Restricts x
    refine ⟨fun _ _ _ => 0, fun y => ?_⟩
    exact (y (Classical.arbitrary I)).elim

/-- A tensor represents zero precisely when every coefficient vanishes. -/
theorem ofRaw_eq_zero_iff (X : Raw.{v} I K) : ofRaw X = 0 ↔ X.coeff = 0 := by
  change ofRaw X = ofRaw (Raw.zero I K) ↔ _
  rw [ofRaw_eq_iff]
  constructor
  · rintro ⟨⟨M, hM⟩, _⟩
    funext x
    simpa [Raw.zero] using hM x
  · intro h
    constructor
    · refine ⟨fun _ _ _ => 0, fun x => ?_⟩
      simp [Raw.zero, h]
    · refine ⟨fun _ _ _ => 0, fun y => ?_⟩
      simp [Raw.zero, h]

instance [Nonempty I] [Nontrivial K] : Nontrivial (TensorClass.{v} I K) := by
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have h' := (ofRaw_eq_zero_iff (Raw.one.{v} I K)).mp h
  exact one_ne_zero (congrFun h' (fun _ => PUnit.unit))

instance [Nonempty I] [NoZeroDivisors K] : NoZeroDivisors (TensorClass.{v} I K) where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} := by
    induction a using Quotient.inductionOn with | h X =>
    induction b using Quotient.inductionOn with | h Y =>
    change ofRaw (X.mul Y) = 0 → ofRaw X = 0 ∨ ofRaw Y = 0
    simp only [ofRaw_eq_zero_iff]
    intro h
    by_cases hX : X.coeff = 0
    · exact Or.inl hX
    · apply Or.inr
      obtain ⟨x, hx⟩ : ∃ x, X.coeff x ≠ 0 := by
        by_contra! h0
        exact hX (funext h0)
      funext y
      exact (mul_eq_zero.mp (congrFun h (fun i => (x i, y i)))).resolve_left hx

end Semiring

/-- A nonzero class dominates the unit, by contracting onto a nonzero coefficient. -/
theorem one_le_of_ne_zero [Nonempty I] [Field K] {X : TensorClass.{v} I K}
    (h : X ≠ 0) : 1 ≤ X := by
  induction X using Quotient.inductionOn with
  | h x =>
    exact x.one_restricts_of_nonzero (fun h0 => h ((ofRaw_eq_zero_iff x).mpr h0))

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.SiteTensor.DiagonalRaw
section
/-! # Diagonal tensors and their direct sums -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor.Raw

universe v
variable (I K : Type*) [Fintype I] [CommSemiring K]

/-- The common-label diagonal only depends on the label type up to equivalence. -/
theorem diagonal_equiv {α β : Type v} [Fintype α] [Fintype β] (e : α ≃ β) :
    (diagonal I K α).Equivalent (diagonal I K β) := by
  classical
  apply reindex_equivalent (fun _ => e)
  intro (x : I → α)
  simp only [diagonal]
  refine Fintype.sum_equiv e _ _ fun a => ?_
  have h : (fun i => e (x i)) = (fun _ => e a) ↔ x = (fun _ => a) := by
    simp [funext_iff]
  congr! 1
  exact h.symm

/-- The empty diagonal is the zero tensor. -/
theorem diagonal_empty_equivalent :
    (diagonal I K PEmpty.{v + 1}).Equivalent (zero I K) := by
  classical
  apply reindex_equivalent (fun _ => Equiv.refl _)
  intro x
  simp [diagonal]

/-- The one-label diagonal is the scalar unit. -/
theorem diagonal_unit_equivalent :
    (diagonal I K PUnit.{v + 1}).Equivalent (one I K) := by
  classical
  apply reindex_equivalent (X := diagonal I K _) (Y := one I K) (fun _ => Equiv.refl _)
  intro (x : I → PUnit.{v + 1})
  simp [diagonal, one, Subsingleton.elim x (fun _ => PUnit.unit)]

private theorem push_constant_labels (α : Type v) [Fintype α] {Y : Type*}
    (f : (I → α) → Y) (y : Y) :
    pushCoeff f (diagonal I K α).coeff y =
      ∑ a : α, if f (fun _ => a) = y then 1 else 0 := by
  classical
  let c (a : α) : I → α := fun _ => a
  have hc : (diagonal I K α).coeff = pushCoeff c (fun _ => 1) := by
    funext x
    apply Finset.sum_congr rfl
    intro a _
    change (if x = c a then (1 : K) else 0) = (if c a = x then 1 else 0)
    congr! 1
    exact eq_comm
  rw [hc, pushCoeff_comp]
  rfl

/-- A direct sum of diagonals has all the labels of the disjoint union. -/
theorem diagonal_sum_equivalent (α β : Type v) [Fintype α] [Fintype β] :
    ((diagonal I K α).add (diagonal I K β)).Equivalent (diagonal I K (α ⊕ β)) := by
  classical
  apply reindex_equivalent (X := (diagonal I K α).add (diagonal I K β))
    (Y := diagonal I K (α ⊕ β)) (fun _ => Equiv.refl _)
  intro (x : I → α ⊕ β)
  let f (y : I → α) (i : I) : α ⊕ β := Sum.inl (y i)
  let g (y : I → β) (i : I) : α ⊕ β := Sum.inr (y i)
  change pushCoeff f (diagonal I K α).coeff x +
    pushCoeff g (diagonal I K β).coeff x = (diagonal I K (α ⊕ β)).coeff x
  rw [push_constant_labels I K α, push_constant_labels I K β]
  simp only [diagonal, Fintype.sum_sum_type]
  apply congrArg₂ (· + ·) <;> apply Finset.sum_congr rfl <;> intro a _ <;>
    congr! 1 <;> exact eq_comm

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.SiteTensor.Diagonal
section
/-! # Natural numbers in the tensor semiring -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

universe v
variable (I K : Type*) [Fintype I] [Nonempty I] [CommSemiring K]

/-- A natural number in the tensor semiring is the class of the common-label
diagonal of that size. -/
@[simp] theorem ofRaw_diagonal_eq_natCast (α : Type v) [Fintype α] :
    ofRaw (Raw.diagonal I K α) = (Fintype.card α : TensorClass.{v} I K) := by
  classical
  refine Fintype.induction_empty_option (P := fun β _ =>
    ofRaw (Raw.diagonal I K β) = (Fintype.card β : TensorClass.{v} I K)) ?_ ?_ ?_ α
  · intro β γ _ e ih
    let := Fintype.ofEquiv γ e.symm
    rw [← Fintype.card_congr e, ← ih]
    exact ofRaw_eq_iff.mpr (Raw.diagonal_equiv I K e.symm)
  · rw [Fintype.card_pempty, Nat.cast_zero, ← ofRaw_zero]
    exact ofRaw_eq_iff.mpr (Raw.diagonal_empty_equivalent I K)
  · intro β _ ih
    rw [Fintype.card_option, Nat.cast_add, Nat.cast_one, ← ih, ← ofRaw_one]
    have h := Raw.diagonal_equiv I K (Equiv.optionEquivSumPUnit.{v} β)
    rw [ofRaw_eq_iff.mpr h, ← ofRaw_eq_iff.mpr (Raw.diagonal_sum_equivalent I K β PUnit.{v + 1}),
      ofRaw_add, ofRaw_eq_iff.mpr (Raw.diagonal_unit_equivalent I K)]

@[simp] theorem ofRaw_diagonal_fin_eq_natCast (n : ℕ) :
    ofRaw (Raw.diagonal I K (Fin n)) = (n : TensorClass.{0} I K) := by
  simpa only [Fintype.card_fin] using ofRaw_diagonal_eq_natCast I K (Fin n)

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.ConcreteSpectrum
section
/-! # The compact spectrum of actual finite-party tensors -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped NNReal

namespace SiteTensor

universe v
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]

/-- The full diagonal indexed by the coefficient positions bounds the tensor class. -/
theorem exists_le_natCast (X : TensorClass.{v} I K) : ∃ n : ℕ, X ≤ n := by
  classical
  induction X using Quotient.inductionOn with
  | _ T =>
    refine ⟨Fintype.card (∀ i, T.Leg i), ?_⟩
    change ofRaw T ≤ (Fintype.card (∀ i, T.Leg i) : TensorClass.{v} I K)
    simpa only [ofRaw_diagonal_eq_natCast, Fintype.card_ulift, Fintype.card_fin] using
        (ofRaw_le_iff.mpr (T.restricts_diagonal I))

/-- The compactness assertion of the spectral comparison proposition with
the genuine tensor semiring and local restriction order. -/
theorem isCompact_spectrum :
    IsCompact (normalizedSpectrum (S := TensorClass.{v} I K) (· ≤ ·)) :=
  isCompact_normalizedSpectrum _ exists_le_natCast

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.Doubling
section
/-!
# Selecting a single spectral price

This is the compactness and separation argument in the proof of the doubling
theorem. Nonzero tensors modulo mutual restriction form a commutative monoid
under tensor product. We use additive notation for that monoid, so `n • t`
means a tensor power and a log spectral evaluation is an additive map.

The submonoid `G` is generated by the private tensors and the binary diagonal
on their union. The finite comparison hypothesis applies only to targets of
the form `Δ + x` with `x ∈ G`. Thus the separating construction keeps a
positive power of the diagonal in every target.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Finset Set

/-- Clear denominators in a strict comparison of two nonnegative ratios. -/
private theorem exists_integral_cut {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hd : 0 < d) (hab : a / b < c / d) :
    ∃ m n : ℕ, (n : ℝ) * a < m * b ∧ (m : ℝ) * d < n * c := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hab)
  let n := k + 1
  have hn : (0 : ℝ) < n := by dsimp [n]; positivity
  have hgap : 1 < (c / d - a / b) * n := by
    apply (div_lt_iff₀ hn).mp
    simpa [n] using hk
  let m := ⌊a / b * n⌋₊ + 1
  have hm₁ : a / b * n < m := by simpa [m] using Nat.lt_floor_add_one (a / b * n)
  have hm₂ : (m : ℝ) < c / d * n := by
    have hfloor := Nat.floor_le (mul_nonneg (div_nonneg ha hb.le) hn.le : 0 ≤ a / b * n)
    dsimp [m]
    push_cast
    linarith only [hfloor, hgap]
  refine ⟨m, n, ?_, ?_⟩
  · calc
      (n : ℝ) * a = (a / b * n) * b := by field_simp
      _ < m * b := mul_lt_mul_of_pos_right hm₁ hb
  · calc
      (m : ℝ) * d < (c / d * n) * d := mul_lt_mul_of_pos_right hm₂ hd
      _ = n * c := by field_simp

variable {T : Type*} [AddCommMonoid T]

/-- At a single normalized point, failure of every rescaling yields two actual
tensor products in opposite strict order. The more expensive product for
`h` belongs to the submonoid generated by the equality requirements. -/
private theorem local_price_separator
    (F h : T →+ ℝ) (G : AddSubmonoid T) {u : T} (hu : u ∈ G)
    (hU : 0 < h u) (hF : ∀ t, 0 ≤ F t) (hh : ∀ t, 0 ≤ h t)
    (hfull : ∃ t, 0 < F t)
    (hfail : ¬ ∃ c : ℝ, 0 < c ∧ (∀ t, c * F t ≤ h t) ∧
      ∀ t ∈ G, c * F t = h t) :
    ∃ x ∈ G, ∃ y : T, F x < F y ∧ h y < h x := by
  by_cases hzero : F u = 0
  · obtain ⟨y, hpos⟩ := hfull
    obtain ⟨n, hn⟩ := exists_nat_gt (h y / h u)
    refine ⟨n • u, G.nsmul_mem hu n, y, ?_, ?_⟩
    · simpa [hzero] using hpos
    · simpa [nsmul_eq_mul] using (div_lt_iff₀ hU).mp hn
  have hFu : 0 < F u := lt_of_le_of_ne (hF u) (Ne.symm hzero)
  by_cases hover : ∃ t, h t / h u < F t / F u
  · obtain ⟨t, ht⟩ := hover
    obtain ⟨m, n, h₁, h₂⟩ := exists_integral_cut (hh t) hU hFu ht
    refine ⟨m • u, G.nsmul_mem hu m, n • t, ?_, ?_⟩
    · simpa [nsmul_eq_mul] using h₂
    · simpa [nsmul_eq_mul] using h₁
  by_cases hunder : ∃ t ∈ G, F t / F u < h t / h u
  · obtain ⟨t, htG, ht⟩ := hunder
    obtain ⟨m, n, h₁, h₂⟩ := exists_integral_cut (hF t) hFu hU ht
    refine ⟨n • t, G.nsmul_mem htG n, m • u, ?_, ?_⟩
    · simpa [nsmul_eq_mul] using h₁
    · simpa [nsmul_eq_mul] using h₂
  push Not at hover hunder
  exfalso
  apply hfail
  refine ⟨h u / F u, div_pos hU hFu, ?_, ?_⟩
  · intro t
    have hle := (div_le_div_iff₀ hFu hU).mp (hover t)
    rw [div_mul_eq_mul_div, div_le_iff₀ hFu]
    linarith
  · intro t ht
    have heq := (div_eq_div_iff hFu.ne' hU.ne').mp
      (le_antisymm (hover t) (hunder t ht))
    rw [div_mul_eq_mul_div, div_eq_iff hFu.ne']
    linarith

/-- Given finite strict spectral comparison for stretched targets, a single
rescaled point is bounded above by `h` everywhere and attains `h` on `G`.

Take `G` to be the submonoid generated by the private tensors and `Δ`.
In the doubling theorem `h = λ a + b + c` and `u` is the binary diagonal
on the first private set. The estimate turning an ordinary sum into the
finite comparison hypothesis is a separate input to this theorem. -/
theorem select_spectral_price_of_finite_comparison
    {S : Type*} [TopologicalSpace S] [CompactSpace S] [Nonempty S]
    (F : S → T →+ ℝ) (h : T →+ ℝ) (G : AddSubmonoid T) (Δ u : T)
    (hcont : ∀ t, Continuous (fun s => F s t)) (hF : ∀ s t, 0 ≤ F s t)
    (hh : ∀ t, 0 ≤ h t) (hu : u ∈ G) (hU : 0 < h u)
    (hfull : ∀ s, ∃ t, 0 < F s t)
    (hcompare : ∀ (x : T), x ∈ G → ∀ (j : ℕ) (y : Fin j → T),
      (∀ s, ∃ i, F s (Δ + x) < F s (y i)) → ∃ i, h (Δ + x) ≤ h (y i)) :
    ∃ (s : S) (c : ℝ), 0 < c ∧ (∀ t, c * F s t ≤ h t) ∧
      ∀ t ∈ G, c * F s t = h t := by
  classical
  by_contra hnone
  have hlocal (s : S) := local_price_separator (F s) h G hu hU (hF s) hh (hfull s)
    (fun he => hnone ⟨s, he⟩)
  choose x hx y hxy hyx using hlocal
  let U (s : S) := {q : S | F q (x s) < F q (y s)}
  have hcover : (univ : Set S) ⊆ ⋃ s, U s := fun q _ => mem_iUnion.mpr ⟨q, hxy q⟩
  obtain ⟨J, hJ⟩ := isCompact_univ.elim_finite_subcover U
    (fun s => isOpen_lt (hcont _) (hcont _)) hcover
  let E := Fintype.equivFin ↥J
  let X := ∑ s ∈ J, x s
  let Y (s : S) := Δ + (∑ q ∈ J.erase s, x q) + y s
  have hX : X ∈ G := G.sum_mem fun s _ => hx s
  have hrewrite (s : ↥J) : X = (∑ q ∈ J.erase s.val, x q) + x s :=
    (Finset.sum_erase_add J x s.property).symm
  have hdominates (q : S) : ∃ i, F q (Δ + X) < F q (Y ((E.symm i).val)) := by
    obtain ⟨s, hs⟩ := mem_iUnion.mp (hJ (mem_univ q))
    obtain ⟨hsJ, hqs⟩ := mem_iUnion.mp hs
    let i : ↥J := ⟨s, hsJ⟩
    refine ⟨E i, ?_⟩
    rw [Equiv.symm_apply_apply, hrewrite i]
    simpa [Y, i, add_assoc] using
      add_lt_add_left (show F q (x s) < F q (y s) from hqs)
        (F q Δ + F q (∑ a ∈ J.erase s, x a))
  obtain ⟨i, hi⟩ := hcompare X hX _ (fun i => Y (E.symm i).val) hdominates
  rw [hrewrite (E.symm i)] at hi
  exact (not_le.mpr (hyx (E.symm i).val)) (by simpa only [Y, map_add, ← add_assoc, add_le_add_iff_left] using hi)

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.StrictComparison
section
/-!
# Selecting a summand by amplified strict comparison

In this file addition in `T` denotes tensor product of nonzero tensors, so a
logarithmic price is an additive homomorphism. Ordinary sums and restrictions
remain separate relations. We use the consequence of strict comparison obtained
by expanding a restriction of `K` direct copies of a tensor power and dropping
the zero images. The constant `K` may vary with the initial power `k`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators

variable {T : Type*} [AddCommMonoid T]

/-- The expanded conclusion of strict spectral comparison for a finite direct sum.
Every nonzero summand in the target is the image of a word of length `n` in the
sources. Its price will be bounded using restriction monotonicity. -/
def ExpandedStrictComparison (spectrum : Set (T →+ ℝ))
    (restricts : T → T → Prop) (ordinarySum : T → (L : ℕ) → (Fin L → T) → Prop) : Prop :=
  ∀ {J : ℕ} (X : T) (Y : Fin J → T), 0 < J →
    (∀ f ∈ spectrum, ∃ i, f X < f (Y i)) →
    ∃ K : ℕ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      ∃ L : ℕ, 0 < L ∧ L ≤ K * J ^ n ∧ ∃ Z : Fin L → T,
        ordinarySum (n • X) L Z ∧
        ∀ l, ∃ w : Fin n → Fin J, restricts (Z l) (∑ t, Y (w t))

private theorem remove_constant {a b c : ℝ}
    (h : ∀ n : ℕ, 0 < n → (n : ℝ) * a ≤ c + n * b) : a ≤ b := by
  by_contra! hab
  obtain ⟨m, hm⟩ := exists_lt_nsmul (sub_pos.mpr hab) c
  have hh := h (m + 1) (Nat.succ_pos _)
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hm hh
  linarith

/-- The finite alternative used in the proof of doubling. If each normalized
point prefers some `Y i` to `X`, a monotone price satisfying the ordinary-sum
estimate on all positive powers of `X` weakly prefers some `Y i` as well.
The two amplifications absorb first the constant number of direct copies and
then the cost of choosing one of the `J` sources. -/
theorem finite_comparison_of_ordinary_sum
    {spectrum : Set (T →+ ℝ)} {restricts : T → T → Prop}
    {ordinarySum : T → (L : ℕ) → (Fin L → T) → Prop}
    (compare : ExpandedStrictComparison spectrum restricts ordinarySum)
    (h : T →+ ℝ) (mono : ∀ {x y}, restricts x y → h x ≤ h y)
    {C : ℝ} (hC : 0 ≤ C) {X : T}
    (stretch : ∀ (m L : ℕ) (Z : Fin L → T), 0 < m →
      ordinarySum (m • X) L Z → ∃ l, h (m • X) ≤ h (Z l) + C * Real.logb 2 L)
    {J : ℕ} (hJ : 0 < J) (Y : Fin J → T)
    (cover : ∀ f ∈ spectrum, ∃ i, f X < f (Y i)) : ∃ i, h X ≤ h (Y i) := by
  classical
  have : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  obtain ⟨i, _, hmax⟩ := Finset.univ.exists_max_image (fun j => h (Y j)) Finset.univ_nonempty
  refine ⟨i, remove_constant (c := C * Real.logb 2 J) fun k hk => ?_⟩
  have hlarge (f : T →+ ℝ) (hf : f ∈ spectrum) : ∃ j, f (k • X) < f (k • Y j) := by
    obtain ⟨j, hj⟩ := cover f hf
    refine ⟨j, ?_⟩
    simpa only [map_nsmul, nsmul_eq_mul] using
      mul_lt_mul_of_pos_left hj (show (0 : ℝ) < k by exact_mod_cast hk)
  obtain ⟨K, hK, decompose⟩ := compare (k • X) (fun j => k • Y j) hJ hlarge
  apply remove_constant (c := C * Real.logb 2 K)
  intro n hn
  obtain ⟨L, hL, hcount, Z, hZ, hword⟩ := decompose n hn
  have hsum : ordinarySum ((n * k) • X) L Z := by rwa [Nat.mul_comm, mul_nsmul]
  obtain ⟨l, hprice⟩ := stretch (n * k) L Z (Nat.mul_pos hn hk) hsum
  obtain ⟨w, hw⟩ := hword l
  have hfactor : h (Z l) ≤ n * (k * h (Y i)) := calc
    h (Z l) ≤ h (∑ t, k • Y (w t)) := mono hw
    _ = ∑ t, k * h (Y (w t)) := by simp
    _ ≤ ∑ _t : Fin n, k * h (Y i) := Finset.sum_le_sum fun t _ =>
      mul_le_mul_of_nonneg_left (hmax (w t) (Finset.mem_univ _)) (Nat.cast_nonneg _)
    _ = n * (k * h (Y i)) := by simp
  have hlog : Real.logb 2 L ≤ Real.logb 2 K + n * Real.logb 2 J := calc
    Real.logb 2 L ≤ Real.logb 2 ((K * J ^ n : ℕ) : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hL) (by exact_mod_cast hcount)
    _ = _ := by
      rw [Nat.cast_mul, Nat.cast_pow, Real.logb_mul (by positivity) (by positivity), Real.logb_pow]
  simp only [map_nsmul, nsmul_eq_mul, Nat.cast_mul] at hprice
  linarith only [hprice, hfactor, mul_le_mul_of_nonneg_left hlog hC]

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.PriceSelection
section
/-!
# Doubling via the normalized spectrum

The rank bound makes the space of normalized spectral points compact. On the
multiplicative monoid of nonzero tensors, taking logarithms gives additive
real-valued maps. The subsequent selection argument uses the restriction
expansion from strict comparison and the permutation-stretch estimate.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section
open scoped NNReal

variable {A : Type*} [CommSemiring A] {res : A → A → Prop} {P : Submonoid A}

/-- The log price is nonnegative because every nonzero tensor restricts to the unit. -/
theorem one_le_spectral_value (f : normalizedSpectrum res) {t : A} (ht : res 1 t) :
    1 ≤ f.val t := by
  simpa only [f.property.2.1] using f.property.2.2.2.2 1 t ht

/-- The nonzero tensor classes use tensor product as their additive operation.
The logarithm is base two, as in the manuscript. -/
def spectralLogHom (hunit : ∀ t : P, res 1 t) (f : normalizedSpectrum res) :
    Additive P →+ ℝ where
  toFun x := Real.logb 2 (f.val x.toMul.val : ℝ)
  map_zero' := by simp [f.property.2.1]
  map_add' x y := by
    have hpos (t : P) : (f.val t.val : ℝ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans_le (one_le_spectral_value f (hunit t))).ne'
    simp only [toMul_add, Submonoid.coe_mul, f.property.2.2.2.1, NNReal.coe_mul]
    exact Real.logb_mul (hpos x.toMul) (hpos y.toMul)

theorem spectralLogHom_nonneg (hunit : ∀ t : P, res 1 t) (f : normalizedSpectrum res)
    (x : Additive P) : 0 ≤ spectralLogHom hunit f x := by
  apply Real.logb_nonneg (by norm_num)
  exact_mod_cast one_le_spectral_value f (hunit x.toMul)

theorem continuous_spectralLogHom (hunit : ∀ t : P, res 1 t) (x : Additive P) :
    Continuous (fun f : normalizedSpectrum res => spectralLogHom hunit f x) :=
  continuous_log_price (hunit x.toMul)

/-- A spectral price is a common positive multiple of a normalized log
evaluation, or the zero price of a collapsed placement. -/
def IsSpectralPrice (hunit : ∀ t : P, res 1 t) (g : Additive P →+ ℝ) : Prop :=
  g = 0 ∨ ∃ (f : normalizedSpectrum res) (c : ℝ), 0 < c ∧ g = c • spectralLogHom hunit f

theorem IsSpectralPrice.nonneg {hunit : ∀ t : P, res 1 t} {g : Additive P →+ ℝ}
    (hg : IsSpectralPrice hunit g) (t : Additive P) : 0 ≤ g t := by
  rcases hg with rfl | ⟨f, c, hc, rfl⟩
  · rfl
  · exact mul_nonneg hc.le (spectralLogHom_nonneg hunit f t)

theorem IsSpectralPrice.mono {hunit : ∀ t : P, res 1 t} {g : Additive P →+ ℝ}
    (hg : IsSpectralPrice hunit g) {x y : Additive P} (hxy : res x.toMul.val y.toMul.val) :
    g x ≤ g y := by
  rcases hg with rfl | ⟨f, c, hc, rfl⟩
  · rfl
  · apply mul_le_mul_of_nonneg_left _ hc.le
    apply Real.logb_le_logb_of_le (by norm_num)
    · exact_mod_cast zero_lt_one.trans_le (one_le_spectral_value f (hunit x.toMul))
    · exact_mod_cast f.property.2.2.2.2 _ _ hxy

end

end

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.ComparisonExpansion
section
/-!
# From strict tensor comparison to an ordinary sum

The comparison theorem gives a restriction of `K` direct copies of
`(⊕ j, Y j)^⊗n`. In coordinates each input to those local maps carries a
copy label and a word of direct-sum tags. Keeping a fixed copy and word
gives a local image of the corresponding product of `Y`'s. Summing the
nonzero images gives the ordinary sum needed by the doubling argument.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace ComparisonExpansion

open scoped BigOperators Classical
open Crossing

noncomputable section

variable {F I : Type*} [CommSemiring F] [Fintype I]

/-- The coefficient function obtained by summing weighted coordinate basis tensors. -/
private def basisSum {A : I → Type*} {S : Type*} [Fintype S]
    (coord : S → ∀ i, A i) (weight : S → F) (x : ∀ i, A i) : F :=
  ∑ s, if x = coord s then weight s else 0

/-- A finite direct sum tags every local coordinate with the same summand index. -/
def directSum {J : Type*} [Fintype J] {A : J → I → Type*} [∀ j i, Fintype (A j i)]
    (Y : (j : J) → (∀ i, A j i) → F) : (∀ i, Σ j, A j i) → F :=
  basisSum (fun p : Σ j, ∀ i, A j i => fun i => ⟨p.1, p.2 i⟩) (fun p => Y p.1 p.2)

/-- Reindex the nonzero terms of a nonzero finite sum. The map back to the
original index set retains the source of each surviving term. -/
theorem nonzero_terms_of_sum {P M : Type*} [Fintype P] [AddCommMonoid M]
    {x : M} (hx : x ≠ 0) (z : P → M) (hsum : x = ∑ p, z p) :
    ∃ L : ℕ, 0 < L ∧ L ≤ Fintype.card P ∧ ∃ idx : Fin L → P,
      (∀ l, z (idx l) ≠ 0) ∧ x = ∑ l, z (idx l) := by
  let S := {p : P // z p ≠ 0}
  let e := Fintype.equivFin S
  have hex : ∃ p, z p ≠ 0 := by
    by_contra! hz
    exact hx (hsum.trans (by simp [hz]))
  obtain ⟨p, hp⟩ := hex
  refine ⟨Fintype.card S, Fintype.card_pos_iff.mpr ⟨⟨p, hp⟩⟩, Fintype.card_subtype_le _,
    fun l => (e.symm l).1, fun l => (e.symm l).2, ?_⟩
  calc
    x = ∑ p, z p := hsum
    _ = ∑ p ∈ Finset.univ.filter (fun p => z p ≠ 0), z p := (Finset.sum_filter_ne_zero _).symm
    _ = ∑ p : S, z p.1 := Finset.sum_subtype _ (by simp) _
    _ = _ := Fintype.sum_equiv e _ _ fun p => by simp

end
end ComparisonExpansion

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.ClassComparison
section
/-!
# Strict comparison on the nonzero tensor classes

The ground-field comparison theorem is isolated as `StrictSpectralComparison`.
From a restriction to a sum of classes we extract local images in the target's
own format. Distributing powers over the direct sum and retaining its nonzero
images gives the expanded comparison used by the doubling argument.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace SiteTensor

open scoped BigOperators NNReal Classical

universe v u w

variable (I : Type u) (K : Type w) [Fintype I] [Nonempty I] [Field K]

/-- Nonzero tensors are closed under tensor product. -/
def nonzeroClasses : Submonoid (TensorClass.{v} I K) where
  carrier := {t | t ≠ 0}
  one_mem' := one_ne_zero
  mul_mem' := mul_ne_zero

/-- Addition denotes tensor product, for taking logarithms of multiplicative prices. -/
abbrev NonzeroProduct := Additive (nonzeroClasses.{v} I K)

variable {I K}

/-- Forget the proof that a tensor class is nonzero. -/
abbrev classOfProduct (x : NonzeroProduct.{v} I K) : TensorClass.{v} I K := x.toMul.val

theorem unit_le_nonzeroClass (x : nonzeroClasses.{v} I K) : 1 ≤ x.val :=
  one_le_of_ne_zero x.property

/-- The normalized base-two log price of an actual ground-field spectral point. -/
abbrev logPoint (f : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop)) :
    NonzeroProduct.{v} I K →+ ℝ := spectralLogHom unit_le_nonzeroClass f

/-- Representatives for an ordinary sum all have the target's local coordinates. -/
def ClassOrdinarySum (X : NonzeroProduct.{v} I K) (L : ℕ) (Z : Fin L → NonzeroProduct.{v} I K) :
    Prop :=
  ∃ (R : Raw.{v} I K) (z : Fin L → (∀ i, R.Leg i) → K),
    ofRaw R = classOfProduct X ∧ R.coeff = ∑ l, z l ∧
    ∀ l, ofRaw { R with coeff := z l } = classOfProduct (Z l)

/-- The strict comparison assertion of Proposition 2.1, without any expansion
or finite-family cost information built into it. -/
def StrictSpectralComparison (I : Type u) (K : Type w) [Fintype I] [Nonempty I] [Field K] : Prop :=
  ∀ X Y : TensorClass.{v} I K, X ≠ 0 → Y ≠ 0 →
    (∀ f : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop), f.val X < f.val Y) →
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 0 < n → X ^ n ≤ C • (Y ^ n)

omit [Nonempty I] in
private theorem split_add (R : Raw.{v} I K) (Y V : TensorClass.{v} I K)
    (h : ofRaw R ≤ Y + V) :
    ∃ A B : (∀ i, R.Leg i) → K, R.coeff = A + B ∧
      ofRaw { R with coeff := A } ≤ Y ∧ ofRaw { R with coeff := B } ≤ V := by
  induction Y using Quotient.inductionOn with | h Y =>
  induction V using Quotient.inductionOn with | h V =>
  obtain ⟨M, hM⟩ := h
  let image {B : I → Type v} [∀ i, Fintype (B i)] (T : (∀ i, B i) → K)
      (N : ∀ i, R.Leg i → B i → K) (x : ∀ i, R.Leg i) := ∑ a, T a * ∏ i, N i (x i) (a i)
  let left := fun i x a => M i x (Sum.inl a)
  let right := fun i x a => M i x (Sum.inr a)
  refine ⟨image Y.coeff left, image V.coeff right, ?_, ⟨left, fun _ => rfl⟩, ⟨right, fun _ => rfl⟩⟩
  funext x
  have hh := hM x
  change R.coeff x = ∑ a, sumCoeff Y.coeff V.coeff a * ∏ i, M i (x i) (a i) at hh
  simpa [sumCoeff, add_mul, Finset.sum_add_distrib, sum_pushCoeff_mul, image, left, right] using hh

/-- A restriction to a finite direct sum gives an ordinary sum in *any given*
representative of the target, with one local image for each source class. -/
theorem images_of_le_sum {J : Type*} [Fintype J] (R : Raw.{v} I K)
    (Y : J → TensorClass.{v} I K) (h : ofRaw R ≤ ∑ j, Y j) :
    ∃ Z : J → (∀ i, R.Leg i) → K, R.coeff = ∑ j, Z j ∧
      ∀ j, ofRaw { R with coeff := Z j } ≤ Y j := by
  have aux (s : Finset J) (x : (∀ i, R.Leg i) → K)
      (hx : ofRaw { R with coeff := x } ≤ ∑ j ∈ s, Y j) :
      ∃ Z : J → (∀ i, R.Leg i) → K, x = ∑ j ∈ s, Z j ∧
        ∀ j ∈ s, ofRaw { R with coeff := Z j } ≤ Y j := by
    induction s using Finset.induction_on generalizing x with
    | empty =>
      have hx' : ofRaw { R with coeff := x } = 0 :=
        le_antisymm (by simpa using hx) (zero_le_tensor _)
      exact ⟨0, by simpa using (ofRaw_eq_zero_iff _).mp hx', by simp⟩
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj] at hx
      obtain ⟨a, b, heq, ha, hb⟩ := split_add {R with coeff := x} _ _ hx
      obtain ⟨Z, hZ, hle⟩ := ih b hb
      refine ⟨Function.update Z j a, ?_, ?_⟩
      · rw [Finset.sum_insert hj, Function.update_self]
        rw [show ∑ l ∈ s, Function.update Z j a l = ∑ l ∈ s, Z l from
          Finset.sum_congr rfl fun l hl => Function.update_of_ne (show l ≠ j from fun h => hj (h ▸ hl)) ..]
        exact heq.trans (congrArg (a + ·) hZ)
      · intro l hl
        rcases Finset.mem_insert.mp hl with rfl | hs
        · simpa using ha
        · simpa [Function.update_of_ne (show l ≠ j from fun e => hj (e ▸ hs))] using hle l hs
  obtain ⟨Z, hsum, hle⟩ := aux Finset.univ R.coeff h
  exact ⟨Z, hsum, fun j => hle j (Finset.mem_univ _)⟩

/-- On the concrete tensor semiring, strict comparison for two classes suffices
for the expansion with a bounded number of nonzero ordinary summands. -/
theorem expandedStrictComparison_of_strict (strict : StrictSpectralComparison.{v} I K) :
    ExpandedStrictComparison (Set.range (logPoint.{v} (I := I) (K := K)))
      (fun x y => classOfProduct x ≤ classOfProduct y) ClassOrdinarySum := by
  intro J X Y hJ hlog
  let y := fun i => classOfProduct (Y i)
  have summand_le (j : Fin J) : y j ≤ ∑ i, y i := by
    rw [← Finset.sum_erase_add Finset.univ y (Finset.mem_univ j)]
    simpa using add_mono (zero_le_tensor (∑ i ∈ Finset.univ.erase j, y i)) (le_refl (y j))
  have hnonzero : ∑ i, y i ≠ 0 := by
    let j : Fin J := ⟨0, hJ⟩
    intro hz
    exact (Y j).toMul.property (le_antisymm ((summand_le j).trans_eq hz) (zero_le_tensor _))
  have greater (f : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop)) :
      f.val (classOfProduct X) < f.val (∑ i, y i) := by
    obtain ⟨i, hi⟩ := hlog (logPoint f) ⟨f, rfl⟩
    apply lt_of_lt_of_le _ (f.property.2.2.2.2 _ _ (summand_le i))
    by_contra! hh
    apply hi.not_ge
    apply Real.logb_le_logb_of_le (by norm_num)
    · exact_mod_cast zero_lt_one.trans_le (one_le_spectral_value f (unit_le_nonzeroClass (Y i).toMul))
    · exact_mod_cast hh
  obtain ⟨C, hC, hx⟩ := strict _ _ X.toMul.property hnonzero greater
  refine ⟨C, hC, fun n hn => ?_⟩
  let P := Fin C × (Fin n → Fin J)
  let W (p : P) := ∑ t, Y (p.2 t)
  have prod (w : Fin n → Fin J) : classOfProduct (∑ t, Y (w t)) = ∏ t, y (w t) := by
    simp [classOfProduct, toMul_sum, y]
  have distrib : C • (∑ j, y j)^n = ∑ p : P, classOfProduct (W p) := by
    change _ = ∑ p : Fin C × (Fin n → Fin J), classOfProduct (∑ t, Y (p.2 t))
    rw [Fintype.sum_prod_type]
    simp only [prod, ← Fintype.prod_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.sum_const]
  obtain ⟨R, hR⟩ := Quotient.exists_rep (classOfProduct (n • X))
  change ofRaw R = classOfProduct (n • X) at hR
  have hr : ofRaw R ≤ ∑ p : P, classOfProduct (W p) := by
    rw [hR, ← distrib]
    simpa [classOfProduct, y] using hx n hn
  obtain ⟨z, hsum, hle⟩ := images_of_le_sum R _ hr
  have hnz : R.coeff ≠ 0 := fun heq => (n • X).toMul.property
    (hR.symm.trans ((ofRaw_eq_zero_iff _).mpr heq))
  obtain ⟨L, hL, hcount, idx, hnz', heq⟩ := ComparisonExpansion.nonzero_terms_of_sum hnz z hsum
  let images (l : Fin L) : NonzeroProduct.{v} I K :=
    Additive.ofMul ⟨ofRaw { R with coeff := z (idx l) },
      fun h => hnz' l ((ofRaw_eq_zero_iff _).mp h)⟩
  exact ⟨L, hL, hcount.trans_eq (by simp [P]), images,
    ⟨R, z ∘ idx, hR, heq, fun _ => rfl⟩, fun l => ⟨(idx l).2, hle _⟩⟩

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.PriceOrdinary
section
/-! # Spectral price of an ordinary sum

For a normalized spectral point on the occupied sites, restriction
monotonicity and direct-sum additivity bound the value of the sum by the
sum of the values. Taking logarithms selects one nonzero summand.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators NNReal

/-- Taking the logarithm of a sum bound selects a positive summand. The scale
is allowed to vanish so that this includes a collapsed placement. -/
private theorem exists_logb_summand {L : Type*} [Fintype L] {v : ℝ≥0} (f : L → ℝ≥0)
    (hv : 0 < v) (hs : v ≤ ∑ j, f j) {c : ℝ} (hc : 0 ≤ c) :
    ∃ j, 0 < f j ∧ c * Real.logb 2 v ≤ c * Real.logb 2 (f j) + c * Real.logb 2 (Fintype.card L) := by
  classical
  cases isEmpty_or_nonempty L with
  | inl h => simp at hs; exact False.elim (hv.ne' hs)
  | inr h =>
    obtain ⟨j, hj⟩ := Finite.exists_max f
    have hsum : v ≤ (Fintype.card L : ℝ≥0) * f j := calc
      _ ≤ ∑ l, f l := hs
      _ ≤ ∑ _l : L, f j := Finset.sum_le_sum fun l _ => hj l
      _ = _ := by simp
    have hp : 0 < (f j : ℝ) := by exact_mod_cast pos_of_mul_pos_right (hv.trans_le hsum) (by positivity)
    have hn : 0 < (Fintype.card L : ℝ) := by exact_mod_cast (Fintype.card_pos (α := L))
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast hv : 0 < (v : ℝ)) (show (v : ℝ) ≤ (Fintype.card L : ℝ) * f j by exact_mod_cast hsum)
    rw [Real.logb_mul hn.ne' hp.ne'] at hlog
    exact ⟨j, by exact_mod_cast hp, by linarith [mul_le_mul_of_nonneg_left hlog hc]⟩

namespace SiteTensor

/-- The local map at each site adds its two direct-sum blocks. Applying all
these maps to a tensor direct sum gives ordinary addition in the fixed format. -/
theorem ordinary_add_restricts {I K : Type*} [Fintype I] [CommSemiring K]
    {A : I → Type*} [∀ i, Fintype (A i)] (T U : (∀ i, A i) → K) :
    Crossing.IsRestriction (T + U) (sumCoeff T U) := by
  classical
  let fold (i : I) (a : A i) (s : A i ⊕ A i) : K := if Sum.elim id id s = a then 1 else 0
  refine ⟨fold, fun x => ?_⟩
  simp only [sumCoeff, add_mul, Finset.sum_add_distrib, Pi.add_apply]
  rw [sum_pushCoeff_mul, sum_pushCoeff_mul]
  have elim (V : (∀ i, A i) → K) :
      (∑ a, V a * ∏ i, (if a i = x i then (1 : K) else 0)) = V x := by
    simp_rw [Fintype.prod_boole]
    simp [← funext_iff, mul_ite]
  exact congrArg₂ (· + ·) (elim T).symm (elim U).symm

universe v
noncomputable section

variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
variable {A : I → Type v} [∀ i, Fintype (A i)]

/-- The restriction class of a coefficient tensor in its given finite format. -/
def ofCoeffs (T : (∀ i, A i) → K) : TensorClass.{v} I K :=
  ofRaw ⟨A, inferInstance, T⟩

@[simp] theorem ofCoeffs_zero : ofCoeffs (0 : (∀ i, A i) → K) = 0 := by
  apply ofRaw_eq_iff.mpr
  constructor <;> exact ⟨fun _ _ _ => 0, fun _ => by simp [Raw.zero]⟩

/-- Local block addition also gives a restriction from a finite direct sum. -/
theorem ordinary_sum_le {J : Type*} [Fintype J] (T : J → (∀ i, A i) → K) :
    ofCoeffs (∑ j, T j) ≤ ∑ j, ofCoeffs (T j) := by
  classical
  generalize (Finset.univ : Finset J) = s
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (ofRaw_le_iff.mpr (ordinary_add_restricts _ _)).trans (add_mono le_rfl ih)

variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop))

/-- Evaluation by an actual normalized spectral point in fixed tensor spaces. -/
def coeffValue (T : (∀ i, A i) → K) : ℝ≥0 := φ.val (ofCoeffs T)

@[simp] theorem coeffValue_zero : coeffValue φ (0 : (∀ i, A i) → K) = 0 := by
  simp [coeffValue, φ.2.1]

theorem coeffValue_one_le {T : (∀ i, A i) → K} (h : T ≠ 0) : 1 ≤ coeffValue φ T := by
  have hle : (1 : TensorClass.{v} I K) ≤ ofCoeffs T :=
    ofRaw_le_iff.mpr (Crossing.unit_restricts_of_nonzero h)
  simpa [coeffValue, φ.2.2.1] using φ.2.2.2.2.2 _ _ hle

theorem ordinary_sum_value_le {J : Type*} [Fintype J] (T : J → (∀ i, A i) → K) :
    coeffValue φ (∑ j, T j) ≤ ∑ j, coeffValue φ (T j) := by
  have h := φ.2.2.2.2.2 _ _ (ordinary_sum_le T)
  change coeffValue φ (∑ j, T j) ≤ normalizedSpectrum.toRingHom φ (∑ j, ofCoeffs (T j)) at h
  rw [map_sum] at h
  exact h

/-- Equation `price-ordinary` for a nonnegative multiple of the log of a point
normalized on the occupied site set. Among the nonzero summands, one attains
the stated bound. This also covers zero summands and a collapsed price. -/
theorem ordinary_sum_logb_le {J : Type*} [Fintype J] (T : J → (∀ i, A i) → K)
    (hT : ∑ j, T j ≠ 0) {c : ℝ} (hc : 0 ≤ c) :
    ∃ j, T j ≠ 0 ∧ c * Real.logb 2 (coeffValue φ (∑ k, T k)) ≤
      c * Real.logb 2 (coeffValue φ (T j)) + c * Real.logb 2 (Fintype.card J) := by
  obtain ⟨j, hj, h⟩ := exists_logb_summand _ (zero_lt_one.trans_le (coeffValue_one_le φ hT))
    (ordinary_sum_value_le φ T) hc
  exact ⟨j, fun h0 => by simp [h0] at hj, h⟩

end
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.RawLogPrice
section
/-!
# Scaled logarithmic prices on finite-site tensor classes

A nonzero field tensor restricts to the scalar unit, so every normalized point takes
values in `{0} ∪ [1,∞)`. Lean's convention `log 0 = 0` therefore extends a log
price monotonically to the zero tensor.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open scoped NNReal

namespace SiteTensor

universe v
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → _))

/-- The price of a raw tensor at a normalized spectral point and a common scale. -/
def rawLogPrice (c : ℝ) (X : Raw.{v} I K) : ℝ :=
  c * Real.logb 2 (φ.val (ofRaw X) : ℝ)

/-- The positivity needed when taking the logarithm of a nonzero tensor. -/
theorem one_le_raw_spectralValue (X : Raw.{v} I K) (h : X.coeff ≠ 0) :
    1 ≤ φ.val (ofRaw X) :=
  one_le_spectral_value φ (X.one_restricts_of_nonzero h)

/-- The zero tensor has price zero. -/
theorem rawLogPrice_zero (c : ℝ) (X : Raw.{v} I K) (h : X.coeff = 0) :
    rawLogPrice φ c X = 0 := by
  simp [rawLogPrice, (ofRaw_eq_zero_iff X).mpr h, φ.property.1]

/-- At a nonnegative scale every tensor has nonnegative price. -/
theorem rawLogPrice_nonneg {c : ℝ} (hc : 0 ≤ c) (X : Raw.{v} I K) :
    0 ≤ rawLogPrice φ c X := by
  by_cases h : X.coeff = 0
  · rw [rawLogPrice_zero φ c X h]
  · apply mul_nonneg hc (Real.logb_nonneg (by norm_num) _)
    exact_mod_cast one_le_raw_spectralValue φ X h

/-- Scaled log price respects the actual local-matrix restriction preorder,
including when a restriction annihilates the input. -/
theorem rawLogPrice_mono {c : ℝ} (hc : 0 ≤ c) {X Y : Raw.{v} I K}
    (h : X.Restricts Y) : rawLogPrice φ c X ≤ rawLogPrice φ c Y := by
  by_cases hX : X.coeff = 0
  · rw [rawLogPrice_zero φ c X hX]
    exact rawLogPrice_nonneg φ hc _
  · apply mul_le_mul_of_nonneg_left _ hc
    apply Real.logb_le_logb_of_le (by norm_num)
    · exact_mod_cast zero_lt_one.trans_le (one_le_raw_spectralValue φ X hX)
    · exact_mod_cast φ.property.2.2.2.2 (ofRaw X) (ofRaw Y) h

/-- Multiplicativity of a normalized point gives additivity of price on nonzero
tensor factors. -/
theorem rawLogPrice_mul (c : ℝ) (X Y : Raw.{v} I K)
    (hX : X.coeff ≠ 0) (hY : Y.coeff ≠ 0) :
    rawLogPrice φ c (X.mul Y) = rawLogPrice φ c X + rawLogPrice φ c Y := by
  have pos (T : Raw.{v} I K) (h : T.coeff ≠ 0) : (φ.val (ofRaw T) : ℝ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans_le (one_le_raw_spectralValue φ T h)).ne'
  simp only [rawLogPrice, ofRaw_mul, φ.property.2.2.2.1, NNReal.coe_mul,
    Real.logb_mul (pos X hX) (pos Y hY), mul_add]

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.ContractionPrice
section
/-!
# Old tensor prices after contracting a new party

A covector on the extra party contracts an enlarged tensor to the old sites.
Taking the supremum of the old prices over all covectors gives a monotone
cost on restriction classes, including for covectors on grouped wire copies.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators NNReal Classical
noncomputable section

namespace SiteTensor

universe v
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]

namespace Raw

/-- Contract the party indexed by `none` against a covector. -/
def contractNew (T : Raw.{v} (Option I) K) (ξ : T.Leg none → K) : Raw.{v} I K where
  Leg i := T.Leg (some i)
  finiteLeg _ := inferInstance
  coeff a := ∑ b, ξ b * T.coeff (Equiv.piOptionEquivProd.symm (b,a))

omit [Nonempty I] in
/-- A restriction on the enlarged site set pulls the new covector back by the
transpose of the new site's local map. The old sites keep their local maps. -/
theorem contractNew_restricts {X Y : Raw.{v} (Option I) K} (h : X.Restricts Y)
    (ξ : X.Leg none → K) : ∃ η : Y.Leg none → K, (X.contractNew ξ).Restricts (Y.contractNew η) := by
  classical
  let : DecidableEq (Option I) := fun _ _ ↦ Classical.propDecidable _
  obtain ⟨M, hm⟩ := h
  let η (b : Y.Leg none) := ∑ c, ξ c * M none c b
  refine ⟨η, fun i ↦ M (some i), ?_⟩
  intro (x : ∀ i, X.Leg (some i))
  change (∑ c, ξ c * X.coeff (Equiv.piOptionEquivProd.symm (c,x))) =
    ∑ a, (∑ b, η b * Y.coeff (Equiv.piOptionEquivProd.symm (b,a))) * _
  have he (c : X.Leg none) (x : ∀ i, X.Leg (some i)) :
      X.coeff (Equiv.piOptionEquivProd.symm (c,x)) =
        ∑ b, ∑ a, Y.coeff (Equiv.piOptionEquivProd.symm (b,a)) *
          (M none c b * ∏ i, M (some i) (x i) (a i)) := by
    rw [hm, ← Fintype.sum_prod_type']
    apply Fintype.sum_equiv (Equiv.piOptionEquivProd (β := Y.Leg))
    intro y
    rw [Equiv.symm_apply_apply, Fintype.prod_option]
    rfl
  simp_rw [he]
  simp only [η, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
    Finset.sum_congr rfl fun _ _ ↦ ?_
  dsimp [Equiv.piOptionEquivProd]
  ring

end Raw

variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop))

/-- The old log price of the most expensive contraction, as a supremum. -/
def contractionPrice (T : Raw.{v} (Option I) K) : ℝ :=
  ⨆ ξ : T.Leg none → K, rawLogPrice φ 1 (T.contractNew ξ)

private theorem contraction_bdd (T : Raw.{v} (Option I) K) :
    BddAbove (Set.range fun ξ : T.Leg none → K ↦ rawLogPrice φ 1 (T.contractNew ξ)) := by
  classical
  let d := Fintype.card (∀ i, T.Leg (some i))
  refine ⟨rawLogPrice φ 1 (Raw.diagonal I K (ULift.{v} (Fin d))), ?_⟩
  rintro _ ⟨ξ, rfl⟩
  exact rawLogPrice_mono φ zero_le_one ((T.contractNew ξ).restricts_diagonal I)

theorem le_contractionPrice (T : Raw.{v} (Option I) K) (ξ : T.Leg none → K) :
    rawLogPrice φ 1 (T.contractNew ξ) ≤ contractionPrice φ T := le_ciSup (contraction_bdd φ T) ξ

theorem contractionPrice_mono {X Y : Raw.{v} (Option I) K} (h : X.Restricts Y) :
    contractionPrice φ X ≤ contractionPrice φ Y := by
  apply ciSup_le
  intro ξ
  obtain ⟨η, hη⟩ := Raw.contractNew_restricts h ξ
  exact (rawLogPrice_mono φ zero_le_one hη).trans (le_contractionPrice φ Y η)

theorem contractionPrice_nonneg (T : Raw.{v} (Option I) K) : 0 ≤ contractionPrice φ T :=
  (rawLogPrice_nonneg φ zero_le_one _).trans (le_contractionPrice φ T 0)

omit [Fintype I] [Nonempty I] in
@[simp] theorem contractNew_coeff_sum {T : Raw.{v} (Option I) K} {L : ℕ}
    (ξ : T.Leg none → K) (Z : Fin L → (∀ i, T.Leg i) → K)
    (hs : T.coeff = ∑ l, Z l) :
    (T.contractNew ξ).coeff = ∑ l, (({T with coeff := Z l} : Raw _ K).contractNew ξ).coeff := by
  funext (a : ∀ i, T.Leg (some i))
  change (∑ b, ξ b * T.coeff (Equiv.piOptionEquivProd.symm (b,a))) = _
  simp only [hs, Finset.sum_apply, Finset.mul_sum, Raw.contractNew]
  rw [Finset.sum_comm]
  exact (Finset.sum_apply a Finset.univ (fun l : Fin L ↦ fun y : (∀ i, T.Leg (some i)) ↦ ∑ b, ξ b * Z l (Equiv.piOptionEquivProd.symm (b,y)))).symm

/-- The contraction estimate is independent of the tensor representative. -/
def classContractionPrice (X : TensorClass.{v} (Option I) K) : ℝ :=
  Quotient.liftOn X (contractionPrice φ) fun _ _ h ↦
    le_antisymm (contractionPrice_mono φ h.1) (contractionPrice_mono φ h.2)

theorem classContractionPrice_mono {X Y : TensorClass.{v} (Option I) K} (h : X ≤ Y) :
    classContractionPrice φ X ≤ classContractionPrice φ Y := by
  induction X, Y using Quotient.inductionOn₂ with | _ X Y =>
    exact contractionPrice_mono φ h

/-- One already-chosen summand realizes the largest contraction supremum.
Every covector bounds the price of the contracted sum by that supremum and
the cost of the summand tag, so the same holds after maximizing in the covector. -/
theorem classContractionPrice_ordinary_sum
    (X : NonzeroProduct.{v} (Option I) K) (L : ℕ) (Z : Fin L → NonzeroProduct.{v} (Option I) K)
    (h : ClassOrdinarySum X L Z) :
    ∃ l, classContractionPrice φ (classOfProduct X) ≤
      classContractionPrice φ (classOfProduct (Z l)) + Real.logb 2 L := by
  classical
  obtain ⟨T, z, hT, hsum, hz⟩ := h
  have hL : 0 < L := by
    by_contra! hL
    obtain rfl : L = 0 := Nat.eq_zero_of_le_zero hL
    exact X.toMul.property (hT.symm.trans ((ofRaw_eq_zero_iff T).mpr (by simpa using hsum)))
  have : Nonempty (Fin L) := ⟨⟨0,hL⟩⟩
  obtain ⟨j, hj⟩ := Finite.exists_max (fun l ↦ classContractionPrice φ (classOfProduct (Z l)))
  refine ⟨j, ?_⟩
  rw [← hT]
  change contractionPrice φ T ≤ _
  apply ciSup_le
  intro ξ
  letI : ∀ i, Fintype (T.Leg (some i)) := fun i => T.finiteLeg (some i)
  have hh := contractNew_coeff_sum ξ z hsum
  by_cases he : (T.contractNew ξ).coeff = 0
  · rw [rawLogPrice_zero φ 1 _ he, ← hz j]
    exact add_nonneg (contractionPrice_nonneg φ _) (Real.logb_nonneg (by norm_num)
      (by exact_mod_cast hL : (1 : ℝ) ≤ L))
  let zz (l : Fin L) := ({T with coeff := z l} : Raw _ K).contractNew ξ
  let C (l : Fin L) : (∀ i, T.Leg (some i)) → K := (zz l).coeff
  change (T.contractNew ξ).coeff = ∑ l, C l at hh
  obtain ⟨l, _, hp⟩ := ordinary_sum_logb_le φ C (hh ▸ he) zero_le_one
  have hprice : rawLogPrice φ 1 (T.contractNew ξ) ≤ rawLogPrice φ 1 (zz l) + Real.logb 2 L := by
    have heq := congrArg (coeffValue φ (A := fun i => T.Leg (some i))) hh
    simp only [← heq, Fintype.card_fin, one_mul] at hp
    have same (u : ∀ i, Fintype (T.Leg (some i))) (V : (∀ i, T.Leg (some i)) → K) :
        ofRaw (⟨_, u, V⟩ : Raw.{v} I K) =
          ofRaw (⟨_, fun i => T.finiteLeg (some i), V⟩ : Raw.{v} I K) :=
      congrArg (fun w => ofRaw (⟨_, w, V⟩ : Raw.{v} I K)) (Subsingleton.elim _ _)
    simp only [rawLogPrice, one_mul, coeffValue, ofCoeffs, C, zz, Raw.contractNew] at hp ⊢
    simpa only [same] using hp
  refine hprice.trans (add_le_add_left (?_ : rawLogPrice φ 1 (zz l) ≤ _) _)
  exact (le_contractionPrice φ {T with coeff := z l} ξ).trans (by
    change classContractionPrice φ (ofRaw _) ≤ _
    rw [hz]
    exact hj l)

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.SiteTensor.ExtensionStar
section
/-! # A pair of wires meeting at one new party

A covector at the new party has one entry for each pair of endpoint labels.
Contracting the two wires reads that entry at the two old endpoints.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical
noncomputable section

namespace SiteTensor.Raw

variable {I : Type*} (K : Type*) [Field K]

/-- The new party holds both labels, and each old endpoint holds its own label. -/
def newStar (a b : I) (A B : Type) [Fintype A] [Fintype B] : Raw.{0} (Option I) K where
  Leg := Option.rec (A × B) (fun i ↦ (i = a → A) × (i = b → B))
  finiteLeg := Option.rec (inferInstanceAs (Fintype (A × B))) (fun i ↦
    Fintype.ofFinite ((i = a → A) × (i = b → B)))
  coeff x := (if (x none).1 = (x (some a)).1 rfl then 1 else 0) *
    (if (x none).2 = (x (some b)).2 rfl then 1 else 0)

/-- Contracting the common end of the two wires gives the matrix of the covector. -/
theorem contractNew_newStar_coeff [Fintype I] (a b : I) (A B : Type) [Fintype A] [Fintype B]
    (ξ : A × B → K) (x : ∀ i, (i = a → A) × (i = b → B)) :
    ((newStar K a b A B).contractNew ξ).coeff x = ξ ((x a).1 rfl, (x b).2 rfl) := by
  change (∑ s : A × B, ξ s * ((if s.1 = (x a).1 rfl then 1 else 0) *
    (if s.2 = (x b).2 rfl then 1 else 0))) = _
  rw [Fintype.sum_prod_type]
  simp [mul_ite]

end SiteTensor.Raw

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.DiagonalProduct
section
/-! # Restriction and multiplication of common-label diagonals -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

open scoped BigOperators Classical

universe v
variable {I K : Type*} {α β : Type v} [Fintype I] [CommSemiring K]

namespace Raw

/-- A diagonal coefficient is one when all sites agree with the fixed site. -/
theorem diagonal_coeff_at (i₀ : I) [Fintype α] (x : I → α) :
    (diagonal I K α).coeff x = if ∀ i, x i = x i₀ then 1 else 0 := by
  classical
  simp only [diagonal]
  rw [Finset.sum_eq_single (x i₀)]
  · simp [funext_iff]
  · intro b _ hb
    apply ite_eq_right
    intro hx
    exact hb (congrFun hx i₀).symm
  · simp

end Raw
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.SpectralSpace
section
/-! # Prices of tensors placed in a metric space

Each tensor has one finite-dimensional coordinate space per index. A map of the
indices groups all factors in each fiber at one site, including the scalar slot
of an empty fiber. Thus prices indexed by arbitrary lists of sites also handle
collisions, relabelings and insertion of trivial slots.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical
section

namespace SiteTensor.Raw

variable {I J K : Type*} [Fintype I]

/-- Group the local coordinates over the fibers of a placement. -/
def group (T : SiteTensor.Raw I K) (σ : I → J) : SiteTensor.Raw J K where
  Leg := fun j => (i : {i : I // σ i = j}) → T.Leg i.1
  finiteLeg := fun _ => inferInstance
  coeff := fun x => T.coeff (fun i => x (σ i) ⟨i, rfl⟩)

/-- Grouping sites preserves the underlying array of coefficients up to a bijection. -/
theorem group_ne_zero_iff [Zero K] (T : SiteTensor.Raw I K) (σ : I → J) :
    (T.group σ).coeff ≠ 0 ↔ T.coeff ≠ 0 := by
  constructor
  · intro h hzero
    exact h (funext fun x => congrFun hzero _)
  · intro h hzero
    apply h
    exact funext fun x => congrFun hzero (fun _ i => x i.1)

end SiteTensor.Raw

open SiteTensor

/-- Prices of finite nonzero placed tensors over a fixed field, with the price at
the zero tensor extended by zero. The normalization is the price of the binary
diagonal on the occupied sites. The transport and diameter bounds are the
corresponding estimates in the manuscript's preliminaries. -/
structure SpectralPlacementPrices (K : Type*) [Field K] (X : Type*) [PseudoMetricSpace X] where
  price {I : Type} [Fintype I] (T : Raw.{0} I K) (x : I → X) : ℝ
  zero_tensor {I : Type} [Fintype I] (T : Raw.{0} I K) (h : T.coeff = 0) (x : I → X) :
    price T x = 0
  collapsed {I : Type} [Fintype I] (T : Raw.{0} I K) (p : X) : price T (fun _ => p) = 0
  group {I J : Type} [Fintype I] [Fintype J] (T : Raw.{0} I K) (σ : I → J) (x : J → X) :
    price T (x ∘ σ) = price (T.group σ) x
  wire (x : Fin 2 → X) : price (Raw.diagonal (Fin 2) K (Fin 2)) x = dist (x 0) (x 1)
  transport {I : Type} [Fintype I] (T : Raw.{0} I K) (x y : I → X) :
    dist (price T x) (price T y) ≤ ∑ i, dist (x i) (y i) * Real.logb 2 (Fintype.card (T.Leg i))
  dist_le_diagonal {I : Type} [Fintype I] (x : I → X) (i j : I) :
    dist (x i) (x j) ≤ price (Raw.diagonal I K (Fin 2)) x
  normalized {I : Type} [Fintype I] [Nontrivial I] (x : I ↪ X) :
    ∃ φ : normalizedSpectrum (fun a b : TensorClass.{0} I K => a ≤ b), ∀ T : Raw.{0} I K,
      T.coeff ≠ 0 → price T x =
        price (Raw.diagonal I K (Fin 2)) x * Real.logb 2 (φ.val (ofRaw T) : ℝ)

namespace SpectralPlacementPrices

variable {K X : Type*} [Field K] [PseudoMetricSpace X]

end SpectralPlacementPrices

end

end

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.SiteTensor.ExtensionGenerator
section
/-! # Factoring the two wires incident to a new party -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical

namespace SiteTensor

variable {I : Type*} (K : Type*) [Field K]

private abbrev wireFiber (a : I) (s : Option I) :=
  {j : Fin 2 // ![none, some a] j = s}

private theorem wireFiber_ext (a : I) (s : Option I) (u v : wireFiber a s) : u = v := by
  apply Subtype.ext
  have h := u.property.trans v.property.symm
  rcases u with ⟨u, _⟩
  rcases v with ⟨v, _⟩
  fin_cases u <;> fin_cases v <;> simp_all

private theorem wireFiber_eq {a i : I} (j : wireFiber a (some i)) : i = a := by
  obtain ⟨j, h⟩ := j
  fin_cases j <;> simp_all

private def newLegEquiv (a : I) (A : Type) (s : Option I) :
    Option.rec A (fun i ↦ i = a → A) s ≃ (wireFiber a s → A) :=
  match s with
  | none =>
    { toFun := fun x _ ↦ x
      invFun := fun f ↦ f ⟨0, rfl⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun f ↦ funext fun j ↦ congrArg f (wireFiber_ext _ _ _ j) }
  | some i =>
    { toFun := fun f j ↦ f (wireFiber_eq j)
      invFun := fun g hi ↦ g ⟨1, by subst i; rfl⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun f ↦ funext fun j ↦ congrArg f (wireFiber_ext _ _ _ j) }

private theorem twoDiagonal_coeff (A : Type) [Fintype A] (x : Fin 2 → A) :
    (Raw.diagonal (Fin 2) K A).coeff x = if x 0 = x 1 then 1 else 0 := by
  rw [Raw.diagonal_coeff_at (1 : Fin 2)]
  simp [Fin.forall_fin_two]

/-- Pairing the labels at the common new party and at each old party gives
the product of the independently grouped endpoint wires. -/
theorem ofRaw_newStar [Fintype I] (a b : I) (A B : Type) [Fintype A] [Fintype B] :
    ofRaw (Raw.newStar K a b A B) =
      ofRaw ((Raw.diagonal (Fin 2) K A).group ![none, some a]) *
      ofRaw ((Raw.diagonal (Fin 2) K B).group ![none, some b]) := by
  let W (i : I) (D : Type) [Fintype D] := (Raw.diagonal (Fin 2) K D).group ![none, some i]
  let e (s : Option I) : (Raw.newStar K a b A B).Leg s ≃ ((W a A).mul (W b B)).Leg s :=
    match s with
    | none => (newLegEquiv a A none).prodCongr (newLegEquiv b B none)
    | some i => (newLegEquiv a A (some i)).prodCongr (newLegEquiv b B (some i))
  rw [← ofRaw_mul]
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent e ?_)
  intro x
  let u (j : Fin 2) : A := (e (![none, some a] j) (x _)).1 ⟨j, rfl⟩
  let v (j : Fin 2) : B := (e (![none, some b] j) (x _)).2 ⟨j, rfl⟩
  change _ = (Raw.diagonal (Fin 2) K A).coeff u * (Raw.diagonal (Fin 2) K B).coeff v
  rw [twoDiagonal_coeff K A u, twoDiagonal_coeff K B v]
  rfl

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.SiteTensor.ExtensionMatrix
section
/-! # Endpoint matrices and their two wire bounds

A matrix on two occupied slots is obtained by applying its columns or its rows
to one end of an identity wire. All other tensor sites have trivial factors.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical BigOperators

namespace SiteTensor.Raw

variable {I K : Type*}

/-- A matrix placed at two named slots. The equality witnesses index exactly the
local factors present at a site. -/
def endpointMatrix (a b : I) (A B : Type) [Fintype A] [Fintype B] (M : A → B → K) :
    Raw.{0} I K :=
  ⟨fun i ↦ (i = a → A) × (i = b → B), fun _ ↦ Fintype.ofFinite _,
    fun x ↦ M ((x a).1 rfl) ((x b).2 rfl)⟩

variable [Fintype I] [Field K]

private theorem grouped_diagonal_coeff_basis (a b : I) (D : Type) [Fintype D] :
    ((diagonal (Fin 2) K D).group ![a,b]).coeff =
      Crossing.basisTensor (F := K)
        (fun (d : D) (i : I) (_ : {j : Fin 2 // ![a,b] j = i}) ↦ d) := by
  funext x
  apply Finset.sum_congr rfl
  intro d _
  let z (j : Fin 2) : D := x (![a,b] j) ⟨j, rfl⟩
  have he : (z = fun _ ↦ d) ↔ x = fun _ _ ↦ d := by
    constructor
    · intro h
      funext i ⟨j, hj⟩
      subst i
      exact congrFun h j
    · rintro rfl
      rfl
  by_cases h : z = fun _ ↦ d
  · exact (ite_eq_left h).trans (ite_eq_left (he.mp h)).symm
  · exact (ite_eq_right h).trans (ite_eq_right (h ∘ he.mpr)).symm

private theorem endpointMatrix_restricts_factor (a b : I) {A B D : Type}
    [Fintype A] [Fintype B] [Fintype D] (M : A → B → K) (L : A → D → K) (R : B → D → K)
    (hM : ∀ x y, M x y = ∑ d, L x d * R y d) :
    (endpointMatrix a b A B M).Restricts ((diagonal (Fin 2) K D).group ![a,b]) := by
  unfold Restricts
  rw [grouped_diagonal_coeff_basis]
  apply (Crossing.restriction_basisTensor_iff _ _).mpr
  refine ⟨fun i x y ↦
    (if h : i = a then L (x.1 h) (y ⟨0,h.symm⟩) else 1) *
    (if h : i = b then R (x.2 h) (y ⟨1,h.symm⟩) else 1), fun x ↦ ?_⟩
  change M ((x a).1 rfl) ((x b).2 rfl) = _
  rw [hM]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.prod_mul_distrib]
  congr 1
  · rw [Finset.prod_eq_single a] <;> simp_all
  · rw [Finset.prod_eq_single b] <;> simp_all

/-- The identity wire on row labels restricts to the matrix. -/
theorem endpointMatrix_restricts_leftWire (a b : I) {A B : Type} [Fintype A] [Fintype B]
    (M : A → B → K) :
    (endpointMatrix a b A B M).Restricts ((diagonal (Fin 2) K A).group ![a,b]) := by
  apply endpointMatrix_restricts_factor a b M (fun x d ↦ if d = x then 1 else 0)
    (fun y d ↦ M d y)
  intro x y
  simp [ite_mul]

/-- The identity wire on column labels restricts to the matrix. -/
theorem endpointMatrix_restricts_rightWire (a b : I) {A B : Type} [Fintype A] [Fintype B]
    (M : A → B → K) :
    (endpointMatrix a b A B M).Restricts ((diagonal (Fin 2) K B).group ![a,b]) := by
  apply endpointMatrix_restricts_factor a b M (fun x d ↦ M x d)
    (fun y d ↦ if d = y then 1 else 0)
  intro x y
  simp [mul_ite]

private def endpointLegEquiv (a b i : I) (D : Type) :
    ({j : Fin 2 // ![a,b] j = i} → D) ≃ ((i = a → D) × (i = b → D)) where
  toFun x := (fun h ↦ x ⟨0,h.symm⟩, fun h ↦ x ⟨1,h.symm⟩)
  invFun x t := by
    obtain ⟨t,ht⟩ := t
    by_cases h : t = 0
    · exact x.1 ((h ▸ ht : ![a,b] (0 : Fin 2) = i).symm)
    · have h1 : t = 1 := by omega
      exact x.2 ((h1 ▸ ht : ![a,b] (1 : Fin 2) = i).symm)
  left_inv x := by
    funext ⟨t,ht⟩
    fin_cases t <;> rfl
  right_inv x := by rfl

/-- An identity endpoint matrix is the placed two-slot diagonal. -/
theorem ofRaw_endpointMatrix_diagonal (a b : I) (A : Type) [Fintype A] :
    ofRaw (endpointMatrix a b A A (fun x y ↦ if x = y then (1 : K) else 0)) =
      ofRaw ((diagonal (Fin 2) K A).group ![a,b]) := by
  symm
  apply ofRaw_eq_iff.mpr (reindex_equivalent (fun i ↦ endpointLegEquiv a b i A) ?_)
  intro x
  let z (j : Fin 2) : A := x (![a,b] j) ⟨j,rfl⟩
  change (diagonal (Fin 2) K A).coeff z = if z 0 = z 1 then 1 else 0
  rw [diagonal_coeff_at (1 : Fin 2)]
  simp [Fin.forall_fin_two]

end SiteTensor.Raw

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.TensorGroupRaw
section
/-! # Grouping local indices along a placement

A matrix acting at an occupied site is the tensor product of the matrices
on its preimages. This makes grouping monotone for arbitrary placements.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

open scoped Classical

/-- Regrouping a coordinate tuple over the fibers of a placement is a bijection. -/
def groupIndexEquiv {I J : Type*} (σ : I → J) (A : I → Type*) :
    (∀ i, A i) ≃ (∀ j, (t : {i // σ i = j}) → A t.1) :=
  Equiv.piCongrFiberwise (fun _ => Equiv.refl _)

@[simp] theorem groupIndexEquiv_apply {I J : Type*} (σ : I → J) (A : I → Type*)
    (a : ∀ i, A i) (j : J) (t : {i // σ i = j}) : groupIndexEquiv σ A a j t = a t.1 := rfl

@[simp] theorem groupIndexEquiv_symm_apply {I J : Type*} (σ : I → J) (A : I → Type*)
    (a : ∀ j, (t : {i // σ i = j}) → A t.1) (i : I) :
    (groupIndexEquiv σ A).symm a i = a (σ i) ⟨i, rfl⟩ := rfl

namespace Raw

variable {I J K : Type*} [Fintype I] [Fintype J] [CommSemiring K]

/-- Grouped matrices are Kronecker products inside each fiber of the placement. -/
theorem group_restricts (σ : I → J) {X Y : Raw I K} (h : X.Restricts Y) :
    (X.group σ).Restricts (Y.group σ) := by
  classical
  obtain ⟨M, hM⟩ := h
  refine ⟨fun j b a => ∏ i : {i // σ i = j}, M i.1 (b i) (a i), fun x => ?_⟩
  change X.coeff ((groupIndexEquiv σ X.Leg).symm x) = _
  rw [hM]
  refine Fintype.sum_equiv (groupIndexEquiv σ Y.Leg) _ _ fun a => ?_
  apply congrArg (Y.coeff a * ·)
  let w (p : Σ j, {i // σ i = j}) := M p.2.1 (x p.1 p.2) (a p.2.1)
  calc
    _ = ∏ p, w p := Fintype.prod_equiv (Equiv.sigmaFiberEquiv σ).symm _ _ (fun i => rfl)
    _ = _ := Fintype.prod_sigma w

/-- Grouping commutes with the tensor product by collecting first and second coordinates. -/
theorem group_mul_equivalent (σ : I → J) (X Y : Raw I K) :
    ((X.mul Y).group σ).Equivalent ((X.group σ).mul (Y.group σ)) := by
  apply reindex_equivalent (fun j =>
    Equiv.arrowProdEquivProdArrow {i // σ i = j} (fun i => X.Leg i.1) (fun i => Y.Leg i.1))
  intro x
  rfl

/-- A grouped product of singleton bases still represents the scalar unit. -/
theorem group_one_equivalent (σ : I → J) :
    ((one I K).group σ).Equivalent (one J K) := by
  let (j : J) : Unique (((one I K).group σ).Leg j) := inferInstanceAs (Unique (∀ _ : {i // σ i = j}, PUnit))
  apply reindex_equivalent (fun _ => Equiv.equivPUnit _)
  intro x
  rfl

/-- A nonempty fiber contains an empty factor when every original leg is empty. -/
theorem group_zero_equivalent (σ : I → J) (hs : Function.Surjective σ) :
    ((zero I K).group σ).Equivalent (zero J K) := by
  classical
  have (j : J) : IsEmpty (((zero I K).group σ).Leg j) := by
    obtain ⟨i, hi⟩ := hs j
    exact ⟨fun x => (x ⟨i, hi⟩).elim⟩
  apply reindex_equivalent (fun _ => Equiv.equivPEmpty _)
  intro x
  rfl

end Raw
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.SiteTensor.Push
section
/-! # Padding the local coordinate spaces with zeros -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor

open Crossing

variable {I K : Type*} [Fintype I] [CommSemiring K]
variable {A B : I → Type*} [∀ i, Fintype (A i)]

/-- Pushing the coefficients along local functions is a restriction, with each
basis vector sent to the basis vector indexed by its image. -/
theorem pushCoeff_restricts (f : ∀ i, A i → B i) (X : (∀ i, A i) → K) :
    IsRestriction (pushCoeff (fun x i => f i (x i)) X) X := by
  refine ⟨fun i b a => if f i a = b then 1 else 0, fun x => ?_⟩
  simp only [pushCoeff, Fintype.prod_boole, ← funext_iff, mul_ite, mul_one, mul_zero]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp_all

/-- An injection of basis indices at each site pads a tensor with zeros.
The coordinate projections restrict the padded tensor back to the original. -/
theorem equivalent_pushCoeff [∀ i, Fintype (B i)] (f : ∀ i, A i ↪ B i)
    (X : (∀ i, A i) → K) :
    IsRestriction X (pushCoeff (fun x i => f i (x i)) X) ∧
    IsRestriction (pushCoeff (fun x i => f i (x i)) X) X := by
  refine ⟨?_, pushCoeff_restricts (fun i => f i) X⟩
  refine ⟨fun i a b => if b = f i a then 1 else 0, fun x => ?_⟩
  rw [sum_pushCoeff_mul]
  simp [Fintype.prod_boole, ← funext_iff, mul_ite]

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.TensorGroupAdd
section
/-! # Grouping a direct sum over occupied sites -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped Classical

namespace SiteTensor.Raw

universe v

variable {I J K : Type*} [Fintype I] [Fintype J] [CommSemiring K]

/-- Grouping sends uniform summand tags to uniform tags at every old site in a fiber.
Surjectivity ensures at least one old site is available to distinguish the tags. -/
private def groupedTags (σ : I → J) (hs : Function.Surjective σ) (A B : I → Type v) (j : J) :
    ((∀ t : {i // σ i = j}, A t.1) ⊕ (∀ t : {i // σ i = j}, B t.1)) ↪
      (∀ t : {i // σ i = j}, A t.1 ⊕ B t.1) where
  toFun := Sum.elim (fun a t => Sum.inl (a t)) (fun b t => Sum.inr (b t))
  inj' := by
    obtain ⟨i, hi⟩ := hs j
    intro a b h
    cases a <;> cases b
    · congr 1
      funext t
      exact Sum.inl.inj (congrFun h t)
    · cases congrFun h ⟨i, hi⟩
    · cases congrFun h ⟨i, hi⟩
    · congr 1
      funext t
      exact Sum.inr.inj (congrFun h t)

omit [Fintype J] in
private theorem group_eq_push (σ : I → J) (X : Raw.{v} I K) :
    (X.group σ).coeff = pushCoeff (groupIndexEquiv σ X.Leg) X.coeff := by
  funext x
  exact (pushCoeff_equiv (groupIndexEquiv σ X.Leg) X.coeff x).symm

/-- Grouping sites along a surjection preserves direct sums up to local restriction. -/
theorem group_add_equivalent (σ : I → J) (hs : Function.Surjective σ) (X Y : Raw.{v} I K) :
    ((X.add Y).group σ).Equivalent ((X.group σ).add (Y.group σ)) := by
  let g := groupedTags σ hs X.Leg Y.Leg
  let e := groupIndexEquiv σ (fun i => X.Leg i ⊕ Y.Leg i)
  let S := (X.group σ).add (Y.group σ)
  have h : ((X.add Y).group σ).coeff = pushCoeff (fun x j => g j (x j)) S.coeff := by
    rw [group_eq_push]
    change pushCoeff e (pushCoeff (fun x i => Sum.inl (x i)) X.coeff +
      pushCoeff (fun y i => Sum.inr (y i)) Y.coeff) =
      pushCoeff (fun (x : ∀ j, (X.group σ).Leg j ⊕ (Y.group σ).Leg j) j => g j (x j)) (pushCoeff (fun x j => Sum.inl (x j)) (X.group σ).coeff +
        pushCoeff (fun y j => Sum.inr (y j)) (Y.group σ).coeff)
    rw [group_eq_push, group_eq_push, pushCoeff_add, pushCoeff_add]
    congr 1 <;> (erw [pushCoeff_comp, pushCoeff_comp, pushCoeff_comp]) <;> rfl
  have hg := equivalent_pushCoeff g S.coeff
  unfold Equivalent Restricts
  rw [h]
  exact ⟨hg.2, hg.1⟩

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.SiteTensor.DiagonalEmbedding
section
/-! # Embedding the labels of a diagonal tensor -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor.Raw

universe u v w

variable (I : Type u) (K : Type w) [Fintype I] [Nonempty I] [CommSemiring K]
variable {α β : Type v} [Fintype α] [Fintype β]

/-- Coordinate projections at every site restrict a diagonal to an embedded label set. -/
theorem diagonal_restricts_of_embedding (e : α ↪ β) :
    (diagonal I K α).Restricts (diagonal I K β) := by
  classical
  unfold Restricts diagonal
  refine ⟨fun _ a b => if b = e a then 1 else 0, fun x => ?_⟩
  simp_rw [Fintype.prod_boole]
  have heq (y : I → β) : (∀ i, y i = e (x i)) ↔ y = fun i => e (x i) :=
    funext_iff.symm
  simp only [heq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  let i₀ : I := Classical.choice inferInstance
  rw [Finset.sum_eq_single (x i₀), Finset.sum_eq_single (e (x i₀))]
  · simp [funext_iff]
  · intro b _ hb
    exact ite_eq_right fun h => (hb (congrFun h i₀).symm).elim
  · simp
  · intro a _ ha
    exact ite_eq_right fun h => (ha (congrFun h i₀).symm).elim
  · simp

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.PolynomialOverhead
section
/-! # Removing polynomial overheads from tensor-power inequalities -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter
open scoped Topology NNReal

/-- A uniformly bounded error between all natural multiples forces equality. -/
theorem eq_of_nat_mul_close {a b C : ℝ}
    (h : ∀ m : ℕ, |(m : ℝ) * (a - b)| ≤ C) : a = b := by
  by_contra hab
  obtain ⟨m, hm⟩ := exists_lt_nsmul (abs_pos.mpr (sub_ne_zero.mpr hab)) C
  rw [nsmul_eq_mul] at hm
  have hbound := h m
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)] at hbound
  exact hm.not_ge hbound

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.DimensionLaw
section
/-! # Logarithmic dependence on wire dimension

Restricting a wire to fewer labels is monotone, and tensoring wires multiplies
the number of labels. Comparing powers with consecutive powers of two then
determines every positive-dimensional value from the binary wire.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

/-- Every nondecreasing wire price that adds on products of positive dimensions
equals its binary price times the logarithm of the dimension. -/
theorem dimension_price_eq_logb {p : ℕ → ℝ} (hmono : ∀ i j, 0 < i → i ≤ j → p i ≤ p j)
    (hone : p 1 = 0) (hmul : ∀ i j, 0 < i → 0 < j → p (i * j) = p i + p j)
    {q : ℕ} (hq : 0 < q) : p q = p 2 * Real.logb 2 q := by
  have hp (i : ℕ) (hi : 0 < i) (n : ℕ) : p (i ^ n) = n * p i := by
    induction n with
    | zero => simp [hone]
    | succ n ih => rw [pow_succ, hmul _ _ (pow_pos hi _) hi, ih, Nat.cast_succ, add_mul, one_mul]
  have hp2 : 0 ≤ p 2 := by simpa [hone] using hmono 1 2 (by decide) (by decide)
  have happrox (k : ℕ) : k * p q ≤ k * (p 2 * Real.logb 2 q) + p 2 ∧
      k * (p 2 * Real.logb 2 q) ≤ k * p q + p 2 := by
    let b := Nat.log 2 (q ^ k)
    have hlo : 2 ^ b ≤ q ^ k := Nat.pow_log_le_self _ (pow_pos hq _).ne'
    have hhi : q ^ k ≤ 2 ^ (b + 1) := (Nat.lt_pow_succ_log_self (by decide) _).le
    have hplo := hmono _ _ (pow_pos (by decide : 0 < 2) _) hlo
    have hphi := hmono _ _ (pow_pos hq _) hhi
    rw [hp _ (by decide) _, hp _ hq _] at hplo
    rw [hp _ hq _, hp _ (by decide) _, Nat.cast_add_one] at hphi
    have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : 0 < (2 : ℝ) ^ b) (by exact_mod_cast hlo : (2 : ℝ)^b ≤ (q : ℝ)^k)
    have hu := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : 0 < (q : ℝ)^k) (by exact_mod_cast hhi : (q : ℝ)^k ≤ (2 : ℝ)^(b+1))
    simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
      Nat.cast_add_one, mul_one] at hl hu
    constructor <;> nlinarith only [hphi, hplo, mul_le_mul_of_nonneg_left hl hp2,
      mul_le_mul_of_nonneg_left hu hp2]
  apply eq_of_nat_mul_close (C := p 2)
  intro k
  rw [abs_le, mul_sub]
  obtain ⟨hu, hl⟩ := happrox k
  constructor <;> linarith

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.NatSpectralExponent
section
/-! # Natural diagonal evaluations

Monotonicity on positive integer diagonals and multiplicativity force their
evaluation to be a single power, determined by the binary diagonal.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Real
open scoped NNReal

variable {A : Type*} [Semiring A] (v : A →* ℝ≥0)
  (hmono : ∀ {a b : ℕ}, 0 < a → a ≤ b → v (a : A) ≤ v (b : A))

include hmono in
theorem spectral_natCast_one_le (n : ℕ) (hn : 0 < n) : 1 ≤ v (n : A) := by
  simpa using hmono (a := 1) (b := n) (by decide) hn

include hmono in
private theorem spectral_natCast_logb_mono {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    logb 2 (v (a : A)) ≤ logb 2 (v (b : A)) :=
  logb_le_logb_of_le (by norm_num)
    (by exact_mod_cast zero_lt_one.trans_le (spectral_natCast_one_le v hmono a ha))
    (by exact_mod_cast hmono ha hab)

include hmono in
/-- The logarithmic price of the `n`-diagonal is the binary price times
`log₂ n`. -/
theorem spectral_natCast_logb (n : ℕ) (hn : 0 < n) :
    logb 2 (v (n : A)) = logb 2 (v (2 : A)) * logb 2 n := by
  refine dimension_price_eq_logb (p := fun i => logb 2 (v (i : A)))
    (fun _ _ => spectral_natCast_logb_mono v hmono) (by simp) ?_ hn
  intro i j hi hj
  have hpos {k : ℕ} (hk : 0 < k) : (v (k : A) : ℝ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans_le (spectral_natCast_one_le v hmono k hk)).ne'
  rw [Nat.cast_mul, map_mul, NNReal.coe_mul, logb_mul (hpos hi) (hpos hj)]

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.SiteTensor.TensorGrouping
section
/-! # Grouping placed tensors on restriction classes

Even with unoccupied sites, grouping commutes with tensor products and is
monotone for restriction. Applied to a diagonal of arbitrary label dimension,
any normalized spectral point therefore evaluates a power of that dimension.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

noncomputable section
open scoped NNReal

universe v u u' w
variable {I : Type u} {J : Type u'} {K : Type w} [Fintype I] [Fintype J] [CommSemiring K]

/-- Group local indices over the fibers of a placement at the level of tensor classes. -/
def groupClass (σ : I → J) : TensorClass.{v} I K → TensorClass.{max u v} J K :=
  Quotient.map (fun X => X.group σ) fun _ _ h =>
    ⟨Raw.group_restricts σ h.1, Raw.group_restricts σ h.2⟩

@[simp] theorem groupClass_ofRaw (σ : I → J) (X : Raw.{v} I K) :
    groupClass σ (ofRaw X) = ofRaw (X.group σ) := rfl

theorem groupClass_mono (σ : I → J) : Monotone (groupClass (K := K) σ) :=
  fun X Y => Quotient.inductionOn₂ X Y fun _ _ => Raw.group_restricts σ

/-- Arbitrary (possibly colliding) placements preserve products and the scalar unit. -/
def groupMulHom [Nonempty I] [Nonempty J] (σ : I → J) :
    TensorClass.{v} I K →* TensorClass.{max u v} J K where
  toFun := groupClass σ
  map_one' := ofRaw_eq_iff.mpr (Raw.group_one_equivalent σ)
  map_mul' X Y := Quotient.inductionOn₂ X Y fun x y =>
    ofRaw_eq_iff.mpr (Raw.group_mul_equivalent σ x y)

/-- Grouping along a surjection also preserves direct sums, because each grouped
site can distinguish the two uniform tags. -/
def groupRingHom [Nonempty I] [Nonempty J] (σ : I → J) (hs : Function.Surjective σ) :
    TensorClass.{v} I K →+* TensorClass.{max u v} J K where
  __ := groupMulHom σ
  map_zero' := ofRaw_eq_iff.mpr (Raw.group_zero_equivalent σ hs)
  map_add' X Y := Quotient.inductionOn₂ X Y fun x y =>
    ofRaw_eq_iff.mpr (Raw.group_add_equivalent σ hs x y)

section Logarithms

variable {A B : Type} {F : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] [Field F]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} B F → _ → Prop))

/-- A grouped diagonal, including a wire with arbitrary endpoints, has log price
equal to its binary price times the base-two logarithm of its dimension. -/
theorem rawLogPrice_group_diagonal (σ : A → B) (c : ℝ) {α : Type} [Fintype α] [Nonempty α] :
    rawLogPrice φ c ((Raw.diagonal A F α).group σ) =
      rawLogPrice φ c ((Raw.diagonal A F (Fin 2)).group σ) * Real.logb 2 (Fintype.card α) := by
  let v : TensorClass.{0} A F →* ℝ≥0 := (normalizedSpectrum.toRingHom φ).toMonoidHom.comp (groupMulHom σ)
  have hv : ∀ {m n : ℕ}, 0 < m → m ≤ n → v m ≤ v n := by
    intro m n _ h
    apply φ.property.2.2.2.2
    apply groupClass_mono σ
    rw [← ofRaw_diagonal_fin_eq_natCast A F m, ← ofRaw_diagonal_fin_eq_natCast A F n]
    exact Raw.diagonal_restricts_of_embedding A F (Fin.castLEEmb h)
  have h := spectral_natCast_logb v hv (Fintype.card α) Fintype.card_pos
  have eval (β : Type) [Fintype β] : φ.val (ofRaw ((Raw.diagonal A F β).group σ)) =
      v (Fintype.card β : TensorClass.{0} A F) := by
    rw [← ofRaw_diagonal_eq_natCast A F β]
    rfl
  rw [rawLogPrice, rawLogPrice, eval α, eval (Fin 2), Fintype.card_fin, Nat.cast_ofNat, h, mul_assoc]

end Logarithms
end
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI

end

-- OAI.LinearAlgebra.SpectralBooks.SiteTensor.ExtensionPower
section
/-! # Powers of placed diagonals

A diagonal whose common label consists of an `n`-tuple of symbols is a
product of `n` single-symbol diagonals, at every placement of its slots.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

variable {A I : Type} [Fintype A] [Nonempty A] [Fintype I] [Nonempty I]
variable (K : Type*) [CommSemiring K] (σ : A → I)

/-- The same power identity with the symbols presented as a word of length `n`. -/
theorem ofRaw_group_diagonal_fun_fin (D : Type) [Fintype D] (n : ℕ) :
    ofRaw ((Raw.diagonal A K (Fin n → D)).group σ) =
      ofRaw ((Raw.diagonal A K D).group σ) ^ n := by
  change groupMulHom σ (ofRaw (Raw.diagonal A K (Fin n → D))) =
    groupMulHom σ (ofRaw (Raw.diagonal A K D)) ^ n
  rw [ofRaw_diagonal_eq_natCast, ofRaw_diagonal_eq_natCast, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow, map_pow]

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.WireSymmetry
section
/-! # Relabeling the ends of a placed wire -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor.Raw

open scoped Classical
universe u

/-- Permuting the indices of a common-label tensor does not change its
mutual-restriction class at the occupied sites. -/
theorem grouped_diagonal_reindex {A B : Type u} {J : Type*} [Fintype A] [Fintype B] [Fintype J]
    (K D : Type*) [CommSemiring K] [Fintype D] (e : A ≃ B) (σ : B → J) :
    ((diagonal B K D).group σ).Equivalent ((diagonal A K D).group (σ ∘ e)) := by
  let fiber (j : J) : {i : A // σ (e i) = j} ≃ {i : B // σ i = j} :=
    e.subtypeEquiv (fun _ => Iff.rfl)
  apply reindex_equivalent (fun j => Equiv.arrowCongr (fiber j).symm (Equiv.refl D))
  intro x
  apply Finset.sum_congr rfl
  intro d _
  change (if (fun i => x (σ i) ⟨i, rfl⟩) = (fun _ => d) then (1 : K) else 0) =
    (if (fun i => x (σ (e i)) ⟨e i, rfl⟩) = (fun _ => d) then 1 else 0)
  let labels (i : B) : D := x (σ i) ⟨i, rfl⟩
  have heq : (labels = fun _ => d) ↔ ((labels ∘ e) = fun _ => d) := by
    constructor
    · intro h
      exact funext fun i => congrFun h (e i)
    · intro h
      exact funext fun i => by simpa [Function.comp] using congrFun h (e.symm i)
  exact if_congr heq rfl rfl

/-- Interchanging the ends of a placed wire gives a mutual restriction,
including when the two endpoints coincide. -/
theorem grouped_wire_symm {J : Type*} [Fintype J] (K D : Type*) [CommSemiring K]
    [Fintype D] (s t : J) :
    ((diagonal (Fin 2) K D).group ![s, t]).Equivalent
      ((diagonal (Fin 2) K D).group ![t, s]) := by
  have h : ![s, t] ∘ Fin.revPerm = ![t, s] := by
    funext i
    fin_cases i <;> rfl
  rw [← h]
  exact grouped_diagonal_reindex K D (Fin.revPerm (n := 2)) ![s, t]

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.WireTransport
section
/-!
# Moving one index along an identity wire

For two placements differing only at one index, its old site contracts that
index with the first end of a wire of the same dimension. Its new site reads
the second end of the wire. The equality of the two wire labels recovers
exactly the coefficients of the original tensor at the new placement.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor.Raw

open scoped Classical BigOperators

variable {I J K : Type*} [Fintype I] [Fintype J] [CommSemiring K]

private theorem diagonal_pair_coeff {D : Type*} [Fintype D] (z : Fin 2 → D) :
    (diagonal (Fin 2) K D).coeff z = if z 0 = z 1 then 1 else 0 := by
  classical
  have he (a : D) : (z = fun _ => a) ↔ z 0 = a ∧ z 1 = a := by
    constructor
    · rintro rfl
      exact ⟨rfl,rfl⟩
    · intro h
      funext i
      fin_cases i <;> simp [h]
  unfold diagonal
  dsimp only
  rw [Finset.sum_eq_single (z 0)]
  · simp only [he, true_and, eq_comm]
  · intro a _ ha
    exact ite_eq_right (fun h => ha ((he a).mp h).1.symm)
  · simp

/-- Moving a single index between two placed tensors is a local restriction
after tensoring with the two-site diagonal of that index dimension. -/
theorem move_restricts_with_wire (T : Raw I K) (p q : I → J) (i₀ : I)
    (hagree : ∀ i, i ≠ i₀ → p i = q i) :
    (T.group q).Restricts ((T.group p).mul ((diagonal (Fin 2) K (T.Leg i₀)).group
      ![p i₀, q i₀])) := by
  classical
  let loc : Fin 2 → J := ![p i₀, q i₀]
  let W := (diagonal (Fin 2) K (T.Leg i₀)).group loc
  let S := (T.group p).mul W
  let ok (j : J) (x : (T.group q).Leg j) (y : S.Leg j) : Prop :=
    (∀ (i : I), i ≠ i₀ → ∀ (h : p i = j) (h' : q i = j),
      y.1 ⟨i, h⟩ = x ⟨i, h'⟩) ∧
    (∀ h : p i₀ = j, y.1 ⟨i₀, h⟩ = y.2 ⟨0, h⟩) ∧
    (∀ h : q i₀ = j, y.2 ⟨1, h⟩ = x ⟨i₀, h⟩)
  refine ⟨fun j x y => if ok j x y then 1 else 0, ?_⟩
  intro x
  let v (i : I) := x (q i) ⟨i, rfl⟩
  let keep (j : J) : S.Leg j := (fun i => v i.val, fun _ => v i₀)
  have hok (j : J) : ok j (x j) (keep j) := by
    refine ⟨?_, fun _ => rfl, ?_⟩
    · rintro i _ h rfl
      rfl
    · rintro rfl
      rfl
  have hcoeff (y : ∀ j, S.Leg j) : S.coeff y =
      T.coeff (fun i => (y (p i)).1 ⟨i, rfl⟩) *
        (if (y (p i₀)).2 ⟨0, rfl⟩ = (y (q i₀)).2 ⟨1, rfl⟩ then 1 else 0) :=
    congrArg (_ * ·) (diagonal_pair_coeff (fun k => (y (loc k)).2 ⟨k, rfl⟩))
  change T.coeff v = ∑ y : ∀ j, S.Leg j, S.coeff y * ∏ j, if ok j (x j) (y j) then 1 else 0
  have hp (y : ∀ j, S.Leg j) : (∏ j, if ok j (x j) (y j) then (1 : K) else 0) =
      if ∀ j, ok j (x j) (y j) then 1 else 0 := Fintype.prod_boole
  simp_rw [hp]
  rw [Finset.sum_eq_single keep]
  · rw [hcoeff keep]
    have hw : (keep (p i₀)).2 ⟨0, rfl⟩ = (keep (q i₀)).2 ⟨1, rfl⟩ := rfl
    rw [ite_eq_left hw, ite_eq_left hok, mul_one, mul_one]
  · intro y _ hy
    by_cases hc : ∀ j, ok j (x j) (y j)
    · by_cases hw : (y (p i₀)).2 ⟨0, rfl⟩ = (y (q i₀)).2 ⟨1, rfl⟩
      · exfalso
        apply hy
        have hright : (y (q i₀)).2 ⟨1,rfl⟩ = v i₀ := (hc _).2.2 rfl
        have hleft := hw.trans hright
        funext j
        apply Prod.ext
        · funext ⟨i, hi⟩
          subst j
          by_cases h : i = i₀
          · subst i
            exact ((hc _).2.1 rfl).trans hleft
          · have transport (j : J) (hj : q i = j) : x j ⟨i, hj⟩ = v i := by
              subst j
              rfl
            exact ((hc _).1 i h rfl (hagree i h).symm).trans (transport _ _)
        · funext ⟨k, hk⟩
          subst j
          fin_cases k
          · exact hleft
          · exact hright
      · simp [hcoeff, hw]
    · simp [hc]
  · simp

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.RawPriceTransport
section
/-! # Transport and collapse for an actual spectral point

A move of one index uses one wire of the appropriate dimension. Adding such
moves gives the transport inequality for any two placements in the finite
site set. Moving indices across wires of price zero preserves the price.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

noncomputable section
open scoped NNReal

variable {I J : Type} {K : Type*} [Fintype I] [Fintype J] [Nonempty J] [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ)

/-- Binary wire distance in the placement supplied by a scaled spectral point. -/
def rawWireDistance (s t : J) : ℝ :=
  rawLogPrice φ c ((Raw.diagonal (Fin 2) K (Fin 2)).group ![s, t])

theorem rawWireDistance_symm (s t : J) : rawWireDistance φ c s t = rawWireDistance φ c t s := by
  unfold rawWireDistance rawLogPrice
  rw [ofRaw_eq_iff.mpr (Raw.grouped_wire_symm K (Fin 2) s t)]

private theorem diagonal_pair_ne_zero (D : Type) [Fintype D] [Nonempty D] :
    (Raw.diagonal (Fin 2) K D).coeff ≠ 0 := by
  classical
  let d := Classical.arbitrary D
  intro hzero
  have h := congrFun hzero (fun _ => d)
  have he (a : D) : (fun _ : Fin 2 => d) = (fun _ => a) ↔ d = a :=
    ⟨fun h => congrFun h 0, by rintro rfl; rfl⟩
  change (Raw.diagonal (Fin 2) K D).coeff (fun _ => d) = (0 : K) at h
  simp [Raw.diagonal, he] at h

omit [Nonempty J] in
/-- At a single occupied site the tensor is an ordinary vector, supplied by a
local map from the one-dimensional unit. -/
theorem Raw.group_const_restricts_one (T : Raw.{0} I K) (s : J) :
    (T.group (fun _ => s)).Restricts (Raw.one J K) := by
  classical
  let M (j : J) (b : (T.group (fun _ => s)).Leg j) (_ : (Raw.one J K).Leg j) : K :=
    if h : s = j then T.coeff (fun i => b ⟨i, h⟩) else 1
  refine ⟨M, fun x => ?_⟩
  let (j : J) : Unique ((Raw.one J K).Leg j) := inferInstanceAs (Unique PUnit)
  rw [Fintype.sum_unique]
  change T.coeff (fun i => x s ⟨i, rfl⟩) = 1 * ∏ j, M j (x j) PUnit.unit
  rw [one_mul, Finset.prod_eq_single s]
  · simp [M]
  · intro j _ hj
    simp [M, Ne.symm hj]
  · simp

/-- A placement with all indices at one point has price zero. -/
theorem rawLogPrice_const (hc : 0 ≤ c) (T : Raw.{0} I K) (s : J) :
    rawLogPrice φ c (T.group (fun _ => s)) = 0 := by
  apply le_antisymm _ (rawLogPrice_nonneg φ hc _)
  have h := rawLogPrice_mono φ hc (T.group_const_restricts_one s)
  simpa [rawLogPrice, φ.property.2.1] using h

@[simp] theorem rawWireDistance_self (hc : 0 ≤ c) (s : J) : rawWireDistance φ c s s = 0 := by
  have h : (![s, s] : Fin 2 → J) = fun _ => s := by funext i; fin_cases i <;> rfl
  simpa only [rawWireDistance, h] using rawLogPrice_const φ c hc (Raw.diagonal (Fin 2) K (Fin 2)) s

/-- The price increase under one move is bounded by the binary wire distance
times the base-two logarithm of the transported local dimension. -/
theorem rawLogPrice_move_le (hc : 0 ≤ c) (T : Raw.{0} I K) (hT : T.coeff ≠ 0)
    (a b : I → J) (i : I) (hagree : ∀ j, j ≠ i → a j = b j) :
    rawLogPrice φ c (T.group b) ≤ rawLogPrice φ c (T.group a) +
      rawWireDistance φ c (a i) (b i) * Real.logb 2 (Fintype.card (T.Leg i)) := by
  classical
  obtain ⟨x, _⟩ : ∃ x, T.coeff x ≠ 0 := by
    by_contra! h
    exact hT (funext h)
  let : Nonempty (T.Leg i) := ⟨x i⟩
  let f := ![a i, b i]
  have hd := ((Raw.diagonal (Fin 2) K (T.Leg i)).group_ne_zero_iff f).mpr
    (diagonal_pair_ne_zero (K := K) (T.Leg i))
  have h := rawLogPrice_mono φ hc (Raw.move_restricts_with_wire T a b i hagree)
  rw [rawLogPrice_mul φ c _ _ ((T.group_ne_zero_iff a).mpr hT) hd,
    rawLogPrice_group_diagonal] at h
  exact h

/-- Transporting one end of a binary wire through a third site gives the
triangle inequality for its price. -/
theorem rawWireDistance_triangle (hc : 0 ≤ c) (s t u : J) :
    rawWireDistance φ c s u ≤ rawWireDistance φ c s t + rawWireDistance φ c t u := by
  let W := Raw.diagonal (Fin 2) K (Fin 2)
  have h := rawLogPrice_move_le φ c hc W (diagonal_pair_ne_zero (Fin 2))
    ![s, t] ![s, u] 1 (by intro i hi; fin_cases i <;> simp_all)
  simpa [W, rawWireDistance, Raw.diagonal, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    using h

end
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.SiteTensor.ExtensionContraction
section
/-! # Contraction prices for the two wires through the new party

A contraction yields an arbitrary matrix on the two old endpoints. Both the
row-label and the column-label wire supply this matrix. When the two label
types agree, the equality covector attains the old wire.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical NNReal
noncomputable section

namespace SiteTensor

variable {I : Type} {K : Type*} [Fintype I] [Nonempty I] [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop))

omit [Nonempty I] in
private theorem contractNew_newStar_eq (a b : I) (A B : Type) [Fintype A] [Fintype B]
    (ξ : A × B → K) :
    (Raw.newStar K a b A B).contractNew ξ =
      Raw.endpointMatrix a b A B (fun s t ↦ ξ (s,t)) := by
  exact congrArg (Raw.mk _ _) (funext (Raw.contractNew_newStar_coeff K a b A B ξ))

/-- Every covector on the two new-party wires yields a matrix supplied by
either old endpoint wire. -/
theorem contractionPrice_newStar_le (a b : I) (A B : Type) [Fintype A] [Fintype B] :
    contractionPrice φ (Raw.newStar K a b A B) ≤
      min (rawLogPrice φ 1 ((Raw.diagonal (Fin 2) K A).group ![a,b]))
          (rawLogPrice φ 1 ((Raw.diagonal (Fin 2) K B).group ![a,b])) := by
  apply ciSup_le
  intro ξ
  rw [contractNew_newStar_eq a b A B ξ]
  exact le_min (rawLogPrice_mono φ zero_le_one (Raw.endpointMatrix_restricts_leftWire a b _))
    (rawLogPrice_mono φ zero_le_one (Raw.endpointMatrix_restricts_rightWire a b _))

/-- Choosing the equality covector on a pair of wires with the same label
space realizes exactly the old wire joining their other endpoints. -/
theorem contractionPrice_newStar_self (a b : I) (A : Type) [Fintype A] :
    contractionPrice φ (Raw.newStar K a b A A) =
      rawLogPrice φ 1 ((Raw.diagonal (Fin 2) K A).group ![a,b]) := by
  apply le_antisymm ((contractionPrice_newStar_le φ a b A A).trans (min_le_left _ _))
  let ξ (s : A × A) : K := if s.1 = s.2 then 1 else 0
  have h := le_contractionPrice φ (Raw.newStar K a b A A) ξ
  rw [contractNew_newStar_eq, rawLogPrice, Raw.ofRaw_endpointMatrix_diagonal] at h
  exact h

private theorem logPrice_wire_power (a b : I) (n : ℕ) :
    rawLogPrice φ 1 ((Raw.diagonal (Fin 2) K (Fin n → Fin 2)).group ![a,b]) =
      n * rawWireDistance φ 1 a b := by
  rw [rawLogPrice, ofRaw_group_diagonal_fun_fin]
  change 1 * Real.logb 2 (normalizedSpectrum.toRingHom φ (_ ^ n) : ℝ≥0) = _
  rw [map_pow, NNReal.coe_pow, Real.logb_pow, one_mul]
  simp [rawWireDistance, rawLogPrice, normalizedSpectrum.toRingHom]

private theorem ofRaw_newStar_words (a b : I) (m n : ℕ) :
    ofRaw (Raw.newStar K a b (Fin m → Fin 2) (Fin n → Fin 2)) =
      ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![none,some a]) ^ m *
      ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![none,some b]) ^ n := by
  rw [ofRaw_newStar, ofRaw_group_diagonal_fun_fin, ofRaw_group_diagonal_fun_fin]

/-- The smaller of the two wire multiplicities bounds the old contraction
price in units of the old endpoint distance. -/
theorem classContractionPrice_wire_powers_le (a b : I) (m n : ℕ) :
    classContractionPrice φ
      (ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![none,some a]) ^ m *
       ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![none,some b]) ^ n) ≤
      min (m : ℝ) n * rawWireDistance φ 1 a b := by
  rw [← ofRaw_newStar_words]
  have h := contractionPrice_newStar_le φ a b (Fin m → Fin 2) (Fin n → Fin 2)
  have hdist : 0 ≤ rawWireDistance φ 1 a b := rawLogPrice_nonneg φ zero_le_one _
  rw [logPrice_wire_power, logPrice_wire_power, ← min_mul_of_nonneg _ _ hdist] at h
  exact h

/-- Equal powers of the new wires attain the prescribed old distance. -/
theorem classContractionPrice_wire_powers_self (a b : I) (m : ℕ) :
    classContractionPrice φ
      (ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![none,some a]) ^ m *
       ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![none,some b]) ^ m) =
      (m : ℝ) * rawWireDistance φ 1 a b := by
  rw [← ofRaw_newStar_words]
  exact (contractionPrice_newStar_self φ a b (Fin m → Fin 2)).trans
    (logPrice_wire_power φ a b m)

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.ScalarRestriction
section
/-! # Absorbing a scalar in one tensor leg -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

variable {I K : Type*} [Fintype I] [Nonempty I] [CommSemiring K]
  {A : I → Type*} [∀ i, Fintype (A i)]

/-- Scaling the identity matrix at one site realizes a scalar multiple as a
restriction. The scalar may be zero. -/
theorem scalar_mul_restricts (c : K) (T : (∀ i, A i) → K) :
    Crossing.IsRestriction (c • T) T := by
  classical
  let i₀ := Classical.arbitrary I
  refine ⟨fun i y x ↦ if x = y then (if i = i₀ then c else 1) else 0, fun x ↦ ?_⟩
  simp_rw [Fintype.prod_ite_zero]
  simp [← funext_iff, mul_ite, mul_comm]

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.OldSiteEmbedding
section
/-! # Adjoining an unoccupied tensor site

The new leg has a single basis vector, so adjoining it preserves old
restrictions, products and nonvanishing.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped BigOperators Classical

namespace SiteTensor

universe v u w
variable {I : Type u} {K : Type w}

namespace Raw

/-- Extend a tensor on the old sites by the one-dimensional new leg. -/
def embedOld (X : Raw.{v} I K) : Raw.{v} (Option I) K where
  Leg := fun j => j.elim PUnit X.Leg
  finiteLeg := fun j => by cases j <;> dsimp <;> infer_instance
  coeff := fun x => X.coeff fun i => x (some i)

/-- The enlarged coordinates are in bijection with the original ones. -/
def embedOldCoords (X : Raw.{v} I K) :
    (∀ j, X.embedOld.Leg j) ≃ (∀ i, X.Leg i) where
  toFun x i := x (some i)
  invFun x j := match j with
    | none => PUnit.unit
    | some i => x i
  left_inv x := by funext j; cases j <;> rfl
  right_inv x := rfl

@[simp] theorem embedOld_coeff_ne_zero_iff [Zero K] (X : Raw.{v} I K) :
    X.embedOld.coeff ≠ 0 ↔ X.coeff ≠ 0 := by
  constructor
  · intro h he
    exact h (funext fun x => congrFun he (X.embedOldCoords x))
  · intro h he
    exact h (funext fun x => congrFun he (X.embedOldCoords.symm x))

variable [Fintype I] [CommSemiring K]

/-- Extend each old local map by the identity on the new scalar leg. -/
theorem embedOld_restricts {X Y : Raw.{v} I K} (h : X.Restricts Y) :
    X.embedOld.Restricts Y.embedOld := by
  let : DecidableEq (Option I) := fun _ _ ↦ Classical.propDecidable _
  obtain ⟨M, hM⟩ := h
  let N : ∀ j, X.embedOld.Leg j → Y.embedOld.Leg j → K
    | none => fun _ _ => 1
    | some i => M i
  refine ⟨N, fun x => ?_⟩
  change X.coeff (fun i => x (some i)) = _
  refine (hM (X.embedOldCoords x)).trans ?_
  apply Fintype.sum_equiv Y.embedOldCoords.symm
  intro y
  rw [Fintype.prod_option]
  simp [embedOld, embedOldCoords, N]
  rfl

/-- A map on the scalar leg acts by a scalar which an old site can absorb. -/
@[simp] theorem embedOld_restricts_iff [Nonempty I] {X Y : Raw.{v} I K} :
    X.embedOld.Restricts Y.embedOld ↔ X.Restricts Y := by
  refine ⟨?_, embedOld_restricts⟩
  rintro ⟨M, hM⟩
  let : DecidableEq (Option I) := Classical.decEq _
  let c := M none PUnit.unit PUnit.unit
  let Z : Raw.{v} I K := {Y with coeff := c • Y.coeff}
  have hZ : Z.Restricts Y := scalar_mul_restricts c Y.coeff
  refine restrict_trans (Y := Z.coeff) ?_ hZ
  refine ⟨fun i => M (some i), fun x => ?_⟩
  refine (hM (X.embedOldCoords.symm x)).trans ?_
  apply Fintype.sum_equiv Y.embedOldCoords
  intro y
  rw [Fintype.prod_option]
  let P := ∏ i, M (some i) (x i) (y (some i))
  change Y.coeff (Y.embedOldCoords y) * (c * P) = (c * Y.coeff (Y.embedOldCoords y)) * P
  ac_rfl

private theorem embedOld_one_equivalent :
    (one I K).embedOld.Equivalent (one (Option I) K : Raw.{v} _ _) := by
  refine reindex_equivalent (fun j => ?_) (fun _ => rfl)
  cases j <;> exact Equiv.refl _

private theorem embedOld_mul_equivalent (X Y : Raw.{v} I K) :
    (X.mul Y).embedOld.Equivalent (X.embedOld.mul Y.embedOld) := by
  let e : ∀ j, (X.mul Y).embedOld.Leg j ≃ (X.embedOld.mul Y.embedOld).Leg j
    | none => (Equiv.punitProd PUnit).symm
    | some i => Equiv.refl _
  exact reindex_equivalent e fun _ => rfl

end Raw

variable [Fintype I] [CommSemiring K]

/-- The old restriction class on the enlarged site set. -/
def embedOldClass : TensorClass.{v} I K → TensorClass.{v} (Option I) K :=
  Quotient.map Raw.embedOld fun _ _ h => ⟨Raw.embedOld_restricts h.1, Raw.embedOld_restricts h.2⟩

@[simp] theorem embedOldClass_ofRaw (X : Raw.{v} I K) :
    embedOldClass (ofRaw X) = ofRaw X.embedOld := rfl

@[simp] theorem embedOldClass_one [Nonempty I] :
    embedOldClass (1 : TensorClass.{v} I K) = 1 :=
  ofRaw_eq_iff.mpr Raw.embedOld_one_equivalent

@[simp] theorem embedOldClass_mul [Nonempty I] (X Y : TensorClass.{v} I K) :
    embedOldClass (X * Y) = embedOldClass X * embedOldClass Y :=
  Quotient.inductionOn₂ X Y fun x y => ofRaw_eq_iff.mpr (Raw.embedOld_mul_equivalent x y)

/-- Restriction order on the old classes is preserved and reflected. -/
@[simp] theorem embedOldClass_le_iff [Nonempty I] (X Y : TensorClass.{v} I K) :
    embedOldClass X ≤ embedOldClass Y ↔ X ≤ Y :=
  Quotient.inductionOn₂ X Y fun _ _ => Raw.embedOld_restricts_iff

section Field

variable {I : Type u} {K : Type w} [Fintype I] [Nonempty I] [Field K]

omit [Nonempty I] in
theorem embedOldClass_ne_zero_iff (X : TensorClass.{v} I K) :
    embedOldClass X ≠ 0 ↔ X ≠ 0 := by
  induction X using Quotient.inductionOn with | _ X =>
    change ofRaw X.embedOld ≠ 0 ↔ ofRaw X ≠ 0
    simp only [ne_eq, ofRaw_eq_zero_iff]
    exact X.embedOld_coeff_ne_zero_iff

/-- Adjoining the new scalar leg gives an additive homomorphism in log-product notation. -/
def embedOldProduct : NonzeroProduct.{v} I K →+ NonzeroProduct.{v} (Option I) K where
  toFun x := Additive.ofMul ⟨embedOldClass (classOfProduct x),
    (embedOldClass_ne_zero_iff _).2 x.toMul.property⟩
  map_zero' := Subtype.ext embedOldClass_one
  map_add' _ _ := Subtype.ext (embedOldClass_mul _ _)

@[simp] theorem classOfProduct_embedOldProduct (x : NonzeroProduct.{v} I K) :
    classOfProduct (embedOldProduct x) = embedOldClass (classOfProduct x) := rfl

end Field

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.TensorGroupCompose
section
/-! # Identity and composition of tensor groupings -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor.Raw

universe u v
variable {I J : Type u} {D K : Type*} [Fintype I] [Fintype J] [Fintype D] [CommSemiring K]

/-- Grouping first over the fibers of `p` and then of `q` reindexes the local
basis of the tensor grouped directly along their composite. -/
theorem group_group_equivalent (T : Raw.{max u v} I K) (p : I → J) (q : J → D) :
    ((T.group p).group q).Equivalent (T.group (q ∘ p)) := by
  apply reindex_equivalent (X := (T.group p).group q) (Y := T.group (q ∘ p)) (fun d => {
    toFun := fun f t => f ⟨p t.1, t.2⟩ ⟨t.1, rfl⟩
    invFun := fun f j i => f ⟨i.1, (congrArg q i.2).trans j.2⟩
    left_inv := by
      intro f
      funext ⟨j, hj⟩ ⟨i, hi⟩
      change p i = j at hi
      subst j
      rfl
    right_inv := fun _ => rfl })
  intro x
  rfl

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.SiteTensor.ExtensionPlacement
section
/-! # Old placements after adjoining a site

Grouping along the inclusion of the old sites contributes an empty product of
coordinate bases at the new site. This scalar factor realizes the old tensor
embedding, including when several slots occupy the same old site.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

universe v
variable {A I : Type} {K : Type*} [Fintype A] [Fintype I] [CommSemiring K]

private def groupSomeLegEquiv (T : Raw.{v} I K) (j : Option I) :
    (T.group some).Leg j ≃ T.embedOld.Leg j := by
  cases j with
  | none =>
    exact ⟨fun _ => PUnit.unit, fun _ t => (nomatch t.property),
      fun _ => funext fun t => (nomatch t.property), fun _ => rfl⟩
  | some i =>
    exact ⟨fun x => x ⟨i, rfl⟩,
      fun x t => (Option.some.inj t.property).symm ▸ x,
      fun x => by
        funext ⟨k, hk⟩
        cases Option.some.inj hk
        rfl,
      fun _ => rfl⟩

/-- The tensor with a trivial new slot is the old tensor placed by inclusion. -/
theorem ofRaw_embedOld_eq_group_some (T : Raw.{v} I K) :
    ofRaw T.embedOld = ofRaw (T.group some) := by
  symm
  exact ofRaw_eq_iff.mpr (Raw.reindex_equivalent (groupSomeLegEquiv T) (fun _ => rfl))

section Prices

variable {F : Type*} [Field F] [Nonempty I]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I F → _ → Prop))
variable (ψ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} (Option I) F → _ → Prop))

end Prices
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.SiteFlattening
section
/-! # Matrix flattenings of finite-party coefficient tensors -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open scoped BigOperators Classical

namespace Crossing

variable {I : Type*} (s : I → Prop) [DecidablePred s]

/-- Separate the indices across the two sides of a cut. -/
abbrev cutEquiv (B : I → Type*) := Equiv.piEquivPiSubtypeProd s B

private theorem cut_symm_left {D : I → Type*} (u : ∀ i : {i // s i}, D i)
      (v : ∀ i : {i // ¬ s i}, D i) (i : {i // s i}) :
      (cutEquiv s D).symm (u,v) i = u i := by
    simp [cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, i.property]
private theorem cut_symm_right {D : I → Type*} (u : ∀ i : {i // s i}, D i)
      (v : ∀ i : {i // ¬ s i}, D i) (i : {i // ¬ s i}) :
      (cutEquiv s D).symm (u,v) i = v i := by
    simp [cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, i.property]

/-- Flattening places the indices from the first side of the cut in the rows
and those from the other side in the columns. -/
def cutMatrix {K : Type*} {B : I → Type*} (T : (∀ i, B i) → K) :
    Matrix (∀ i : {i // s i}, B i) (∀ i : {i // ¬ s i}, B i) K :=
  fun r c ↦ T ((cutEquiv s B).symm (r, c))

variable {K : Type*} [Field K] [Fintype I] {A B : I → Type*}
variable [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

omit [∀ i, Fintype (B i)] in
/-- Local linear maps multiply the flattened matrix on its left and right.
Both multipliers are products of the local entries on their respective sides. -/
theorem cutMatrix_factor_of_restriction (X : (∀ i, B i) → K) (Y : (∀ i, A i) → K)
    (h : IsRestriction X Y) :
    ∃ (P : Matrix (∀ i : {i // s i}, B i) (∀ i : {i // s i}, A i) K)
      (Q : Matrix (∀ i : {i // ¬s i}, A i) (∀ i : {i // ¬s i}, B i) K),
      cutMatrix s X = P * cutMatrix s Y * Q := by
  classical
  obtain ⟨M, hm⟩ := h
  let P : Matrix (∀ i : {i // s i}, B i) (∀ i : {i // s i}, A i) K :=
    fun r a ↦ ∏ i : {i // s i}, M i.val (r i) (a i)
  let Q : Matrix (∀ i : {i // ¬ s i}, A i) (∀ i : {i // ¬ s i}, B i) K :=
    fun a c ↦ ∏ i : {i // ¬ s i}, M i.val (c i) (a i)
  refine ⟨P, Q, ?_⟩
  ext r c
  rw [cutMatrix, hm, ← Equiv.sum_comp (cutEquiv s A).symm, Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  rw [← Fintype.prod_subtype_mul_prod_subtype s]
  simp only [cut_symm_left, cut_symm_right, P, Q, cutMatrix]
  ring
/-- Matrix rank across any cut decreases under tensor restriction. -/
theorem cutMatrix_rank_le_of_restriction (X : (∀ i, B i) → K) (Y : (∀ i, A i) → K)
    (h : IsRestriction X Y) : (cutMatrix s X).rank ≤ (cutMatrix s Y).rank := by
  obtain ⟨P, Q, e⟩ := cutMatrix_factor_of_restriction s X Y h
  rw [e]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

end Crossing

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.BlockDiagRank
section
/-! # Ranks of matrices with two independent blocks -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

/-- The rank of a rectangular block diagonal matrix is the sum of its block ranks. -/
theorem rank_fromBlocks_diagonal {F I J I' J' : Type*} [Field F] [Fintype J] [Fintype J']
    (A : Matrix I J F) (B : Matrix I' J' F) :
    (Matrix.fromBlocks A 0 0 B).rank = A.rank + B.rank := by
  let e := LinearEquiv.sumArrowLequivProdArrow I I' F F
  let d := LinearEquiv.sumArrowLequivProdArrow J J' F F
  have h : (Matrix.fromBlocks A 0 0 B).mulVecLin =
      e.symm.toLinearMap ∘ₗ (A.mulVecLin.prodMap B.mulVecLin) ∘ₗ d.toLinearMap := by
    apply LinearMap.ext
    intro x
    ext (i | i) <;> simp [Matrix.fromBlocks_mulVec, e, d] <;> rfl
  let p := LinearMap.range A.mulVecLin
  let q := LinearMap.range B.mulVecLin
  let iso : (p.prod q) ≃ₗ[F] (p × q) :=
    { toFun x := (⟨x.val.1, x.property.1⟩, ⟨x.val.2, x.property.2⟩)
      invFun y := ⟨(y.1.val, y.2.val), y.1.property, y.2.property⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  rw [Matrix.rank, h, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range,
    Submodule.map_top, LinearEquiv.finrank_map_eq, LinearMap.range_prodMap,
    iso.finrank_eq, Module.finrank_prod]
  rfl

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.SiteFlatteningOperations
section
/-! # Additivity of bipartite flattening rank

Rows and columns of a tensor direct sum have tags at each site. Across a proper
cut the two homogeneous tags on each side select a block diagonal submatrix.
All remaining rows and columns vanish.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

noncomputable section

section

/-- Deleting all-zero rows and columns preserves the rank. -/
private theorem rank_eq_rank_on_support {K R C R' C' : Type*} [Field K]
    [Fintype R'] [Fintype C'] [Fintype C] (M : Matrix R C K)
    (r : R' ↪ R) (c : C' ↪ C)
    (hr : ∀ x ∉ Set.range r, ∀ y, M x y = 0)
    (hc : ∀ y ∉ Set.range c, ∀ x, M x y = 0) :
    M.rank = (M.submatrix r c).rank := by
  classical
  let P : Matrix R R' K := fun i a => if i = r a then 1 else 0
  let Q : Matrix C' C K := fun b j => if c b = j then 1 else 0
  have left (x : R) (b : C') : (P * M.submatrix r c) x b = M x (c b) := by
    rw [Matrix.mul_apply]
    by_cases hx : x ∈ Set.range r
    · obtain ⟨a, rfl⟩ := hx
      simp [P, Matrix.submatrix, r.injective.eq_iff, ite_mul]
    · have h (a : R') : x ≠ r a := fun e => hx ⟨a, e.symm⟩
      simp [P, h, hr _ hx]
  have eq : M = P * M.submatrix r c * Q := by
    ext x y
    rw [Matrix.mul_apply]
    simp only [left]
    by_cases hy : y ∈ Set.range c
    · obtain ⟨b, rfl⟩ := hy
      simp [Q, c.injective.eq_iff, mul_ite]
    · have h (b : C') : c b ≠ y := fun e => hy ⟨b, e⟩
      simp [Q, h, hc _ hy]
  exact le_antisymm (calc
    M.rank = (P * M.submatrix r c * Q).rank := congrArg Matrix.rank eq
    _ ≤ (P * M.submatrix r c).rank := Matrix.rank_mul_le_left _ _
    _ ≤ _ := Matrix.rank_mul_le_right _ _) (Matrix.rank_submatrix_le M r c)

namespace SiteTensor

/-- Include the two homogeneous tag assignments in all assignments on one side. -/
private def homogeneousTags {J : Type*} [Nonempty J] (A B : J → Type*) :
    ((∀ j, A j) ⊕ (∀ j, B j)) ↪ (∀ j, A j ⊕ B j) where
  toFun := Sum.elim (fun a j => Sum.inl (a j)) (fun b j => Sum.inr (b j))
  inj' := by
    rintro (x|x) (y|y) h
    · exact congrArg Sum.inl (funext fun j => Sum.inl.inj (congrFun h j))
    · cases congrFun h (Classical.arbitrary J)
    · cases congrFun h (Classical.arbitrary J)
    · exact congrArg Sum.inr (funext fun j => Sum.inr.inj (congrFun h j))

@[simp] private theorem homogeneousTags_inl {J : Type*} [Nonempty J] (A B : J → Type*)
    (a : ∀ j, A j) (j : J) : homogeneousTags A B (Sum.inl a) j = Sum.inl (a j) := rfl

@[simp] private theorem homogeneousTags_inr {J : Type*} [Nonempty J] (A B : J → Type*)
    (b : ∀ j, B j) (j : J) : homogeneousTags A B (Sum.inr b) j = Sum.inr (b j) := rfl

variable {I K : Type*} {A B : I → Type*}
variable (s : I → Prop) [DecidablePred s] [Fintype I] [Field K]
variable [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

open Crossing

/-- Across a cut with sites on each side the two summands give independent
diagonal blocks. -/
theorem cutMatrix_rank_sumCoeff [Nonempty {i // s i}] [Nonempty {i // ¬ s i}]
    (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) :
    (cutMatrix s (sumCoeff T U)).rank = (cutMatrix s T).rank + (cutMatrix s U).rank := by
  classical
  let : Nonempty I := ⟨(Classical.arbitrary {i // s i}).val⟩
  let r := homogeneousTags (fun i : {i // s i} => A i) (fun i => B i)
  let c := homogeneousTags (fun i : {i // ¬ s i} => A i) (fun i => B i)
  let M := cutMatrix s (sumCoeff T U)
  have support (x y) (h : x ∉ Set.range r ∨ y ∉ Set.range c) : M x y = 0 := by
    apply sumCoeff_mixed
    · intro a he
      have e := (cutEquiv s (fun i => A i ⊕ B i)).apply_symm_apply (x,y)
      rw [← he] at e
      exact h.elim (fun hx => hx ⟨Sum.inl (fun i => a i), congrArg Prod.fst e⟩)
        (fun hy => hy ⟨Sum.inl (fun i => a i), congrArg Prod.snd e⟩)
    · intro b he
      have e := (cutEquiv s (fun i => A i ⊕ B i)).apply_symm_apply (x,y)
      rw [← he] at e
      exact h.elim (fun hx => hx ⟨Sum.inr (fun i => b i), congrArg Prod.fst e⟩)
        (fun hy => hy ⟨Sum.inr (fun i => b i), congrArg Prod.snd e⟩)
  have block : M.submatrix r c = Matrix.fromBlocks (cutMatrix s T) 0 0 (cutMatrix s U) := by
    ext x y
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        change sumCoeff T U _ = T _
        convert sumCoeff_inl T U ((cutEquiv s A).symm (x,y)) using 1
        congr 1
        funext i
        by_cases hi : s i <;> simp [cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply,
          r, c, hi]
      | inr y =>
        apply sumCoeff_mixed
        · intro a he
          have h := congrFun he (Classical.arbitrary {i // ¬ s i}).val
          simp [r, c, cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply,
            (Classical.arbitrary {i // ¬ s i}).property] at h
        · intro b he
          have h := congrFun he (Classical.arbitrary {i // s i}).val
          simp [r, c, cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply,
            (Classical.arbitrary {i // s i}).property] at h
    | inr x =>
      cases y with
      | inl y =>
        apply sumCoeff_mixed
        · intro a he
          have h := congrFun he (Classical.arbitrary {i // s i}).val
          simp [r, c, cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply,
            (Classical.arbitrary {i // s i}).property] at h
        · intro b he
          have h := congrFun he (Classical.arbitrary {i // ¬ s i}).val
          simp [r, c, cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply,
            (Classical.arbitrary {i // ¬ s i}).property] at h
      | inr y =>
        change sumCoeff T U _ = U _
        convert sumCoeff_inr T U ((cutEquiv s B).symm (x,y)) using 1
        congr 1
        funext i
        by_cases hi : s i <;> simp [cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply,
          r, c, hi]
  change M.rank = _
  rw [rank_eq_rank_on_support M r c (fun x hx y => support x y (Or.inl hx))
    (fun y hy x => support x y (Or.inr hy)), block, rank_fromBlocks_diagonal]

namespace Raw

universe v

/-- The zero tensor gives the zero matrix across every cut. -/
theorem cutMatrix_rank_zero (F : Type*) [Field F] :
    (cutMatrix s (zero.{v} I F).coeff).rank = 0 :=
  Matrix.rank_zero

/-- Each side of the scalar unit has just one coordinate tuple. -/
theorem cutMatrix_rank_one (F : Type*) [Field F] :
    (cutMatrix s (one.{v} I F).coeff).rank = 1 := by
  classical
  let r : ({i // s i} → PUnit.{v+1}) ≃ Unit := Equiv.ofUnique _ _
  let c : ({i // ¬s i} → PUnit.{v+1}) ≃ Unit := Equiv.ofUnique _ _
  have eq : cutMatrix s (one.{v} I F).coeff = (1 : Matrix Unit Unit F).submatrix r c := by
    ext x y
    change 1 = (1 : Matrix Unit Unit F) (r x) (c y)
    simp
  rw [eq]
  exact (Matrix.rank_submatrix (1 : Matrix Unit Unit F) r c).trans
    ((Matrix.rank_one (R := F)).trans Fintype.card_unit)

end Raw

end SiteTensor

end

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.KroneckerRank
section
/-! # Rank of a Kronecker product

In tensor product bases the image of a Kronecker product is the tensor
product of the images. Over a field, the natural inclusion of this tensor
product into the ambient space is injective.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped Kronecker

/-- Matrix rank is multiplicative for Kronecker products over every field. -/
theorem rank_kronecker {K m n p q : Type*} [Field K]
    [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    (A : Matrix m n K) (B : Matrix p q K) :
    (A ⊗ₖ B).rank = A.rank * B.rank := by
  classical
  let bm := Pi.basisFun K m
  let bn := Pi.basisFun K n
  let bp := Pi.basisFun K p
  let bq := Pi.basisFun K q
  rw [(A ⊗ₖ B).rank_eq_finrank_range_toLin (bm.tensorProduct bp) (bn.tensorProduct bq),
    Matrix.toLin_kronecker, A.rank_eq_finrank_range_toLin bm bn,
    B.rank_eq_finrank_range_toLin bp bq, TensorProduct.range_map, ← TensorProduct.range_mapIncl,
    LinearMap.finrank_range_of_inj (Module.Flat.tensorProduct_mapIncl_injective_of_right _ _),
    Module.finrank_tensorProduct]

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.SiteFlatteningProduct
section
/-! # Multiplicativity of matrix rank across a cut of tensor sites -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped Classical Kronecker
noncomputable section

namespace SiteTensor

open Crossing

variable {I K : Type*} (s : I → Prop) [DecidablePred s]
  {A B : I → Type*}

/-- Flattening a sitewise tensor product pairs the row coordinates of its two
factors, and likewise pairs their column coordinates. -/
theorem cutMatrix_product [Mul K] (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) :
    cutMatrix s (fun z : ∀ i, A i × B i ↦ T (fun i ↦ (z i).1) * U (fun i ↦ (z i).2)) =
      ((cutMatrix s T) ⊗ₖ (cutMatrix s U)).submatrix
        (Equiv.arrowProdEquivProdArrow {i // s i} (fun i ↦ A i.val) (fun i ↦ B i.val))
        (Equiv.arrowProdEquivProdArrow {i // ¬s i} (fun i ↦ A i.val) (fun i ↦ B i.val)) := by
  ext r c
  change T _ * U _ = T _ * U _
  apply congrArg₂ (· * ·)
  · apply congrArg T
    funext i
    by_cases h : s i <;> simp [cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, h,
      Equiv.arrowProdEquivProdArrow]
  · apply congrArg U
    funext i
    by_cases h : s i <;> simp [cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, h,
      Equiv.arrowProdEquivProdArrow]

/-- The flattening rank across any fixed cut is multiplicative under sitewise
tensor product. -/
theorem cutMatrix_rank_product [Field K] [Fintype I] [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) :
    (cutMatrix s (fun z : ∀ i, A i × B i ↦ T (fun i ↦ (z i).1) * U (fun i ↦ (z i).2))).rank =
      (cutMatrix s T).rank * (cutMatrix s U).rank := by
  rw [cutMatrix_product, Matrix.rank_submatrix, rank_kronecker]

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.CutSpectrum
section
/-! # Spectral points from proper bipartitions of the sites

The flattening rank depends only on the mutual-restriction class. Each proper
bipartition gives a normalized spectral point over any field.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped NNReal Classical

noncomputable section

namespace SiteTensor

universe v u w

open Crossing

variable {I : Type u} (s : I → Prop) [DecidablePred s] [Fintype I] (K : Type w) [Field K]

/-- The matrix rank across the cut of a tensor class. -/
def cutRank : TensorClass.{v} I K → ℕ :=
  Quotient.lift (fun X : Raw.{v} I K => (cutMatrix s X.coeff).rank) fun X Y h =>
    le_antisymm (cutMatrix_rank_le_of_restriction s X.coeff Y.coeff h.1)
      (cutMatrix_rank_le_of_restriction s Y.coeff X.coeff h.2)

@[simp] theorem cutRank_ofRaw (X : Raw.{v} I K) :
    cutRank s K (ofRaw X) = (cutMatrix s X.coeff).rank := rfl

/-- Across every cut restriction induces a matrix rank comparison. -/
theorem monotone_cutRank : Monotone (cutRank.{v} s K) := by
  intro x y
  refine Quotient.inductionOn₂ x y fun X Y h => ?_
  exact cutMatrix_rank_le_of_restriction s X.coeff Y.coeff h

variable [Nonempty I] [Nonempty {i // s i}] [Nonempty {i // ¬ s i}]

/-- The normalized spectral point associated to a proper cut. -/
def cutSpectrum : normalizedSpectrum (fun x y : TensorClass.{v} I K => x ≤ y) := by
  refine ⟨fun x => (cutRank s K x : ℝ≥0), ?_, ?_, ?_, ?_, ?_⟩
  · change ((cutMatrix s (Raw.zero.{v} I K).coeff).rank : ℝ≥0) = 0
    rw [Raw.cutMatrix_rank_zero, Nat.cast_zero]
  · change ((cutMatrix s (Raw.one.{v} I K).coeff).rank : ℝ≥0) = 1
    rw [Raw.cutMatrix_rank_one, Nat.cast_one]
  · intro x y
    refine Quotient.inductionOn₂ x y fun X Y => ?_
    change ((cutMatrix s (sumCoeff X.coeff Y.coeff)).rank : ℝ≥0) =
      ((cutMatrix s X.coeff).rank : ℝ≥0) + (cutMatrix s Y.coeff).rank
    exact_mod_cast cutMatrix_rank_sumCoeff s X.coeff Y.coeff
  · intro x y
    refine Quotient.inductionOn₂ x y fun X Y => ?_
    change ((cutMatrix s (X.mul Y).coeff).rank : ℝ≥0) =
      ((cutMatrix s X.coeff).rank : ℝ≥0) * (cutMatrix s Y.coeff).rank
    exact_mod_cast cutMatrix_rank_product s X.coeff Y.coeff
  · exact fun x y h => Nat.cast_le.mpr ((monotone_cutRank s K) h)

@[simp] theorem cutSpectrum_ofRaw (X : Raw.{v} I K) :
    (cutSpectrum s K).val (ofRaw X) = ((cutMatrix s X.coeff).rank : ℝ≥0) := rfl

/-- Every site set with at least two sites admits a normalized spectral point. -/
theorem spectrum_nonempty (I : Type u) [Fintype I] [Nontrivial I] (K : Type w) [Field K] :
    (normalizedSpectrum (fun x y : TensorClass.{v} I K => x ≤ y)).Nonempty := by
  classical
  obtain ⟨i, j, hij⟩ := exists_pair_ne I
  let s (x : I) := x = i
  let : Nonempty {x // s x} := ⟨⟨i, rfl⟩⟩
  let : Nonempty {x // ¬ s x} := ⟨⟨j, Ne.symm hij⟩⟩
  exact Set.nonempty_of_mem (cutSpectrum.{v} s K).property

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.IntervalPlacement
section
/-! # Wire generators for inserting an interval point -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped Classical NNReal
noncomputable section

namespace SiteTensor

variable {I : Type} {K : Type*} [Fintype I] [Nonempty I] [Field K]

/-- The binary wire from the new party to an old site. -/
def intervalWire (K : Type*) [Field K] (a : I) : NonzeroProduct.{0} (Option I) K := by
  let W := Raw.diagonal (Fin 2) K (Fin 2)
  have hn : W.coeff ≠ 0 := by
    intro he
    have h : W.coeff (fun _ => (0 : Fin 2)) = (0 : K) := congrFun he (fun _ => (0 : Fin 2))
    simp [W, Raw.diagonal, funext_iff] at h
  let X := W.group ![none, some a]
  exact Additive.ofMul ⟨ofRaw X, fun h ↦ (W.group_ne_zero_iff _).mpr hn ((ofRaw_eq_zero_iff X).mp h)⟩

@[simp] theorem classOfProduct_intervalWire (a : I) :
    classOfProduct (intervalWire K a) =
      ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![none, some a]) := rfl

variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop))

theorem contractionPrice_intervalWires_le (a b : I) (m n : ℕ) :
    classContractionPrice φ (classOfProduct (m • intervalWire K a + n • intervalWire K b)) ≤
      min (m : ℝ) n * rawWireDistance φ 1 a b :=
  classContractionPrice_wire_powers_le φ a b m n

theorem contractionPrice_intervalWires_equal (a b : I) (m : ℕ) :
    classContractionPrice φ (classOfProduct (m • intervalWire K a + m • intervalWire K b)) =
      m * rawWireDistance φ 1 a b :=
  classContractionPrice_wire_powers_self φ a b m

/-- Agreement on old products gives agreement on every old raw tensor, including zero. -/
theorem group_some_logPrice_of_old_logPoint
    (ψ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Option I) K → _ → Prop))
    (hold : ∀ X, logPoint ψ (embedOldProduct X) = logPoint φ X) (T : Raw.{0} I K) :
    rawLogPrice ψ 1 (T.group some) = rawLogPrice φ 1 T := by
  by_cases h : T.coeff = 0
  · have hh : (T.group some).coeff = 0 := not_not.mp (fun hn => ((T.group_ne_zero_iff some).mp hn) h)
    rw [rawLogPrice_zero _ _ _ h, rawLogPrice_zero _ _ _ hh]
  let X : NonzeroProduct.{0} I K := Additive.ofMul ⟨ofRaw T, fun he => h ((ofRaw_eq_zero_iff _).mp he)⟩
  have he := hold X
  change Real.logb 2 (ψ.val (ofRaw T.embedOld) : ℝ) = Real.logb 2 (φ.val (ofRaw T) : ℝ) at he
  simpa only [rawLogPrice, one_mul, ofRaw_embedOld_eq_group_some] using he

theorem logPoint_intervalWire_eq
    (ψ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Option I) K → _ → Prop)) (a : I) :
    logPoint ψ (intervalWire K a) = rawWireDistance ψ 1 none (some a) := by
  simp only [rawWireDistance, rawLogPrice, one_mul]
  rfl

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.ComparisonCatalyst
section
/-!
# Removing an additive catalyst from strict comparison

A one-unit gain in an ordered semiring can be amplified while reusing its
additive catalyst. Bounding the resulting multiplicative catalyst by a natural
number gives a uniform comparison of all positive powers.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

variable {S : Type*} [CommSemiring S] [Preorder S] [IsOrderedAddMonoid S] [IsOrderedMonoid S]

omit [IsOrderedMonoid S] in
private theorem reuse_additive_catalyst {a b w : S} (h : a + w ≤ b + w) (n : ℕ) :
    (n : S) * a + w ≤ n * b + w := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      ((n + 1 : ℕ) : S) * a + w = a + (n * a + w) := by push_cast; ring
      _ ≤ a + (n * b + w) := add_le_add_right ih _
      _ = n * b + (a + w) := by ring
      _ ≤ n * b + (b + w) := add_le_add_right h _
      _ = ((n + 1 : ℕ) : S) * b + w := by push_cast; ring

/-- A strict additive gain yields a single natural overhead for every power. -/
theorem powerComparison_of_additiveGain
    (hzero : ∀ z : S, 0 ≤ z) (hbound : ∀ z : S, ∃ n : ℕ, z ≤ (n : S))
    {x y : S} (hy : 1 ≤ y) (gain : ∃ s w : S, 1 + s * x + w ≤ s * y + w) :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 0 < n → x ^ n ≤ C • y ^ n := by
  obtain ⟨s, w, hgain⟩ := gain
  obtain ⟨j, hj⟩ := hbound w
  let J : S := (j : S) + 1
  have hJ : 1 ≤ J := by
    simpa only [J, zero_add] using add_le_add_left (hzero (j : S)) 1
  have hw : w ≤ J * y := calc
    w ≤ (j : S) := hj
    _ ≤ J := by simpa only [J, add_zero] using add_le_add_right (hzero 1) (j : S)
    _ = J * 1 := (mul_one _).symm
    _ ≤ J * y := mul_le_mul_right hy J
  obtain ⟨r, hr⟩ := hbound (J * x)
  let t : S := r * s + J
  have ht : 1 ≤ t := hJ.trans (by
    simpa only [t, zero_add] using add_le_add_left (hzero ((r : S) * s)) J)
  have hxy : t * x ≤ t * y := calc
    t * x = r * s * x + J * x := by dsimp [t]; ring
    _ ≤ r * s * x + r := add_le_add_right hr _
    _ = r * (1 + s * x) + 0 := by ring
    _ ≤ r * (1 + s * x) + w := add_le_add_right (hzero w) _
    _ ≤ r * (s * y) + w := reuse_additive_catalyst hgain r
    _ ≤ r * (s * y) + J * y := add_le_add_right hw _
    _ = t * y := by dsimp [t]; ring
  have hpow (n : ℕ) : t * x ^ n ≤ t * y ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        t * x ^ (n + 1) = (t * x ^ n) * x := by rw [pow_succ, mul_assoc]
        _ ≤ (t * y ^ n) * x := mul_le_mul_left ih x
        _ = (t * x) * y ^ n := by ring
        _ ≤ (t * y) * y ^ n := mul_le_mul_left hxy _
        _ = t * y ^ (n + 1) := by ring
  obtain ⟨c, hc⟩ := hbound t
  refine ⟨c + 1, Nat.succ_pos _, fun n _ => ?_⟩
  calc
    x ^ n = 1 * x ^ n := (one_mul _).symm
    _ ≤ t * x ^ n := mul_le_mul_left ht _
    _ ≤ t * y ^ n := hpow n
    _ ≤ (c : S) * y ^ n := mul_le_mul_left hc _
    _ ≤ (c + 1) • y ^ n := by
      simpa only [succ_nsmul, nsmul_eq_mul, add_zero] using
        add_le_add_right (hzero (y ^ n)) ((c : S) * y ^ n)

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.ComparisonPreorder
section
/-!
# Adjoining a reversed tensor comparison

To separate `x` from `y`, impose the comparison `y ≤ x` and allow tensor
multipliers and a common direct summand. A compression of a positive natural
number in this enlarged preorder is a trade giving a scalar gain in the
original restriction order.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

variable {S : Type*} [CommSemiring S] [Preorder S]

/-- Compare after trading a multiple of `x` on the left for a multiple of `y`
on the right, retaining an arbitrary common summand. -/
def TradeLE (x y a b : S) : Prop := ∃ s w : S, a + s * x + w ≤ b + s * y + w

theorem TradeLE.of_le {x y a b : S} (h : a ≤ b) : TradeLE x y a b :=
  ⟨0, 0, by simpa using h⟩

theorem TradeLE.reversed (x y : S) : TradeLE x y y x :=
  ⟨1, 0, by simp [add_comm]⟩

variable [IsOrderedAddMonoid S]

theorem TradeLE.trans {x y a b c : S} (h : TradeLE x y a b) (g : TradeLE x y b c) :
    TradeLE x y a c := by
  obtain ⟨s, w, hs⟩ := h
  obtain ⟨t, v, ht⟩ := g
  refine ⟨s + t, w + v, ?_⟩
  calc
    _ = (a + s*x + w) + (t*x + v) := by ring
    _ ≤ (b + s*y + w) + (t*x + v) := add_le_add_left hs _
    _ = (s*y + w) + (b + t*x + v) := by ring
    _ ≤ (s*y + w) + (c + t*y + v) := add_le_add_right ht _
    _ = _ := by ring

theorem TradeLE.add {x y a b c d : S} (h : TradeLE x y a b) (g : TradeLE x y c d) :
    TradeLE x y (a + c) (b + d) := by
  obtain ⟨s, w, hs⟩ := h
  obtain ⟨t, v, ht⟩ := g
  refine ⟨s + t, w + v, ?_⟩
  calc
    _ = (a + s*x + w) + (c + t*x + v) := by ring
    _ ≤ (b + s*y + w) + (d + t*y + v) := add_le_add hs ht
    _ = _ := by ring

variable [IsOrderedMonoid S]

omit [IsOrderedAddMonoid S] in
theorem TradeLE.mul_left {x y a b : S} (z : S) (h : TradeLE x y a b) :
    TradeLE x y (z*a) (z*b) := by
  obtain ⟨s, w, hs⟩ := h
  refine ⟨z*s, z*w, ?_⟩
  calc
    _ = z * (a + s*x + w) := by ring
    _ ≤ z * (b + s*y + w) := mul_le_mul_right hs z
    _ = _ := by ring

/-- The enlarged preorder is installed only while extracting a separating state. -/
abbrev tradePreorder (x y : S) : Preorder S where
  le := TradeLE x y
  lt a b := TradeLE x y a b ∧ ¬ TradeLE x y b a
  le_refl a := TradeLE.of_le (le_refl a)
  le_trans _ _ _ := TradeLE.trans

/-- A compression in the enlarged preorder pays for all tensor powers in the
original order. -/
theorem powerComparison_of_tradeCompression (hzero : ∀ a : S, 0 ≤ a)
    (hbound : ∀ a : S, ∃ n : ℕ, a ≤ (n : S)) {x y : S} (hy : 1 ≤ y)
    {D : S} {m : ℕ} (hm : 0 < m) (h : TradeLE x y (D + m) D) :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 0 < n → x ^ n ≤ C • y ^ n := by
  obtain ⟨s, w, hs⟩ := h
  have hm' : (1 : S) ≤ (m : S) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    simpa using add_le_add_left (hzero (n : S)) (1 : S)
  apply powerComparison_of_additiveGain hzero hbound hy
  refine ⟨s, D + w, ?_⟩
  calc
    _ ≤ (m : S) + s*x + (D+w) := add_le_add_left (add_le_add_left hm' _) _
    _ = D + m + s*x + w := by ring
    _ ≤ D + s*y + w := hs
    _ = _ := by ring

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.FixedPoint
section
namespace OAI

/-! Fixed points of continuous maps on compact convex sets of real-valued functions. -/

namespace MatrixMultiplication.AuxiliarySeparation

open Set
open scoped BigOperators

private def weightSimplex (J : Type*) [Fintype J] : Set (J → ℝ) :=
  {w | (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1}

private theorem weightSimplex_convex (J : Type*) [Fintype J] :
    Convex ℝ (weightSimplex J) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro j
    exact add_nonneg (mul_nonneg ha (hx.1 j)) (mul_nonneg hb (hy.1 j))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx.2, hy.2]
    simpa using hab

private theorem weightSimplex_compact (J : Type*) [Fintype J] :
    IsCompact (weightSimplex J) := by
  have hc : IsClosed (weightSimplex J) := by
    change IsClosed ({w : J → ℝ | ∀ j, 0 ≤ w j} ∩ {w | ∑ j, w j = 1})
    have hn : IsClosed {w : J → ℝ | ∀ j, 0 ≤ w j} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun j => isClosed_le continuous_const
        (continuous_apply j : Continuous (fun w : J → ℝ => w j))
    exact hn.inter
      (isClosed_eq (continuous_finsetSum _ fun _ _ => continuous_apply _) continuous_const)
  apply isCompact_Icc.of_isClosed_subset hc
  intro w hw
  constructor
  · exact hw.1
  · intro j
    calc
      w j ≤ ∑ k, w k := Finset.single_le_sum (fun k _ => hw.1 k) (Finset.mem_univ j)
      _ = 1 := hw.2

/-- A finite continuous system of barycentric weights gives an approximate fixed point.
The approximation is measured on any prescribed finite set of coordinates. -/
theorem exists_approximate_fixedPoint_of_weights
    {I J : Type*} [Fintype J] [Nonempty J]
    {K : Set (I → ℝ)} (hK : Convex ℝ K) (f : C(K, K))
    (a : J → K) (w : J → C(K, ℝ))
    (hw0 : ∀ j x, 0 ≤ w j x) (hw1 : ∀ x, ∑ j, w j x = 1)
    (s : Finset I) (ε : ℝ)
    (hclose : ∀ x j, w j x ≠ 0 → ∀ i ∈ s, |(a j).val i - x.val i| ≤ ε) :
    ∃ x : K, ∀ i ∈ s, |(f x).val i - x.val i| ≤ ε := by
  classical
  let D := weightSimplex J
  let b : D → K := fun v =>
    ⟨∑ j, v.val j • (a j).val,
      hK.sum_mem (fun j _ => v.property.1 j) v.property.2 (fun j _ => (a j).property)⟩
  have hb : Continuous b := by
    apply Continuous.subtype_mk
    exact continuous_finsetSum _ fun j _ =>
      ((continuous_apply j).comp continuous_subtype_val).smul continuous_const
  let q : K → D := fun x => ⟨fun j => w j x, (fun j => hw0 j x), hw1 x⟩
  have hq : Continuous q := by
    exact (continuous_pi fun j => (w j).continuous).subtype_mk _
  let g : C(D, D) := ⟨fun v => q (f (b v)), hq.comp (f.continuous.comp hb)⟩
  have hDne : D.Nonempty := by
    let j₀ : J := Classical.choice inferInstance
    refine ⟨Pi.single j₀ 1, ?_, ?_⟩
    · intro j
      by_cases h : j = j₀ <;> simp [h]
    · simp
  obtain ⟨v, hv⟩ := brouwer_fixed_point D (weightSimplex_convex J)
    (weightSimplex_compact J) hDne g
  let x := b v
  have hwv (j : J) : w j (f x) = v.val j := congrArg (fun t : D => t.val j) hv
  refine ⟨x, fun i hi => ?_⟩
  have hx : x.val i - (f x).val i = ∑ j, v.val j * ((a j).val i - (f x).val i) := by
    change (∑ j, v.val j • (a j).val) i - (f x).val i = _
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, v.property.2, one_mul]
  rw [abs_sub_comm, hx]
  calc
    |∑ j, v.val j * ((a j).val i - (f x).val i)|
        ≤ ∑ j, |v.val j * ((a j).val i - (f x).val i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, v.val j * |(a j).val i - (f x).val i| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_mul, abs_of_nonneg (v.property.1 j)]
    _ ≤ ∑ j, v.val j * ε := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : v.val j = 0
      · simp [hj]
      · exact mul_le_mul_of_nonneg_left
          (hclose (f x) j (by rwa [hwv]) i hi) (v.property.1 j)
    _ = ε := by rw [← Finset.sum_mul, v.property.2, one_mul]

theorem exists_finite_partition_weights {I : Type*} {K : Set (I → ℝ)}
    (hK : IsCompact K) (s : Finset I) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ a : Fin n → K, ∃ w : Fin n → C(K, ℝ),
      (∀ x j, 0 ≤ w j x) ∧ (∀ x, ∑ j, w j x = 1) ∧
      (∀ x j, w j x ≠ 0 → ∀ i ∈ s, |(a j).val i - x.val i| < ε) := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let U : K → Set K := fun a => {x | ∀ i ∈ s, |a.val i - x.val i| < ε}
  have hUo : ∀ a, IsOpen (U a) := by
    intro a
    have hUa : U a = ⋂ i ∈ s, {x : K | |a.val i - x.val i| < ε} := by
      ext x
      simp [U]
    rw [hUa]
    apply isOpen_biInter_finset
    intro i hi
    exact isOpen_lt (continuous_const.sub ((continuous_apply i).comp continuous_subtype_val)).abs continuous_const
  have hUc : (univ : Set K) ⊆ ⋃ a, U a := by
    intro x hx
    refine mem_iUnion.mpr ⟨x, ?_⟩
    intro i hi
    simpa using hε
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo hUc
  have htc : (univ : Set K) ⊆ ⋃ a : t, U a.val := by
    intro x hx
    obtain ⟨a, ha⟩ := mem_iUnion.mp (ht hx)
    obtain ⟨hat, hax⟩ := mem_iUnion.mp ha
    exact mem_iUnion.mpr ⟨⟨a, hat⟩, hax⟩
  obtain ⟨w, hw⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun a : t => U a.val) (fun a => hUo a.val) htc
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  refine ⟨Fintype.card t, (fun j => (e j).val), (fun j => w (e j)), ?_, ?_, ?_⟩
  · intro x j
    exact w.nonneg (e j) x
  · intro x
    change ∑ j, w (e j) x = 1
    calc
      ∑ j, w (e j) x = ∑ a : t, w a x := e.sum_comp (fun a => w a x)
      _ = 1 := by simpa only [finsum_eq_sum_of_fintype] using w.sum_eq_one (mem_univ x)
  · intro x j hj i hi
    exact hw (e j) (subset_closure hj) i hi

theorem exists_finite_partition_weights_nonempty {I : Type*} {K : Set (I → ℝ)}
    (hK : IsCompact K) (hne : K.Nonempty) (s : Finset I) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ a : Fin n → K, ∃ w : Fin n → C(K, ℝ),
      (∀ x j, 0 ≤ w j x) ∧ (∀ x, ∑ j, w j x = 1) ∧
      (∀ x j, w j x ≠ 0 → ∀ i ∈ s, |(a j).val i - x.val i| < ε) := by
  obtain ⟨n, a, w, hw0, hw1, hwa⟩ := exists_finite_partition_weights hK s hε
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    obtain ⟨x, hx⟩ := hne
    simpa using hw1 ⟨x, hx⟩
  exact ⟨n, hn, a, w, hw0, hw1, hwa⟩

theorem compact_approx_limit {I : Type*} {K : Set (I → ℝ)}
    (hK : IsCompact K) (_hne : K.Nonempty) (f : K → (I → ℝ)) (hf : Continuous f)
    (happrox : ∀ s : Finset I, ∀ ε : ℝ, 0 < ε →
      ∃ x : K, ∀ i ∈ s, |f x i - x.val i| ≤ ε) :
    ∃ x : K, f x = x.val := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let C : (I × {ε : ℝ // 0 < ε}) → Set K :=
    fun p => {x | |f x p.1 - x.val p.1| ≤ p.2.val}
  have hclosed (p : I × {ε : ℝ // 0 < ε}) : IsClosed (C p) := by
    exact isClosed_le
      (((continuous_apply p.1).comp hf).sub
        ((continuous_apply p.1).comp continuous_subtype_val)).abs continuous_const
  have hfinite (s : Finset (I × {ε : ℝ // 0 < ε})) :
      (⋂ p ∈ s, C p).Nonempty := by
    let es : Finset ℝ := insert 1 (s.image fun p => p.2.val)
    have hes : es.Nonempty := ⟨1, by simp [es]⟩
    have he : 0 < es.min' hes := by
      rw [Finset.lt_min'_iff]
      intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · norm_num
      · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
        exact p.2.property
    obtain ⟨x, hx⟩ := happrox (s.image Prod.fst) (es.min' hes) he
    refine ⟨x, ?_⟩
    simp only [Set.mem_iInter]
    intro p hp
    exact (hx p.1 (Finset.mem_image.mpr ⟨p, hp, rfl⟩)).trans
      (Finset.min'_le es p.2.val (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨p, hp, rfl⟩)))
  obtain ⟨x, hx⟩ := CompactSpace.iInter_nonempty hclosed hfinite
  refine ⟨x, funext fun i => ?_⟩
  have hzero : |f x i - x.val i| ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    simpa only [C, Set.mem_ofPred_eq, zero_add] using
      (Set.mem_iInter.mp hx (i, ⟨ε, hε⟩))
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _)))

/-- Schauder--Tychonoff for an arbitrary product of real lines. Compactness of the
set, rather than finite dimensionality of the ambient space, is the hypothesis. -/
theorem compact_convex_fixedPoint {I : Type*} {K : Set (I → ℝ)}
    (hKcompact : IsCompact K) (hKconvex : Convex ℝ K) (hKne : K.Nonempty)
    (f : C(K, K)) : ∃ x : K, f x = x := by
  have happrox : ∀ s : Finset I, ∀ ε : ℝ, 0 < ε →
      ∃ x : K, ∀ i ∈ s, |(f x).val i - x.val i| ≤ ε := by
    intro s ε hε
    obtain ⟨n, hn, a, w, hw0, hw1, hwa⟩ :=
      exists_finite_partition_weights_nonempty hKcompact hKne s hε
    let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact exists_approximate_fixedPoint_of_weights hKconvex f a w
      (fun j x => hw0 x j) hw1 s ε
      (fun x j hj i hi => (hwa x j hj i hi).le)
  obtain ⟨x, hx⟩ := compact_approx_limit hKcompact hKne
    (fun x => (f x).val) (continuous_subtype_val.comp f.continuous) happrox
  exact ⟨x, Subtype.ext hx⟩

/-- An unbundled form of the product-space fixed-point theorem. -/
theorem compact_convex_fixedPoint_of_continuous {I : Type*} {K : Set (I → ℝ)}
    (hKcompact : IsCompact K) (hKconvex : Convex ℝ K) (hKne : K.Nonempty)
    (f : K → K) (hf : Continuous f) : ∃ x : K, f x = x :=
  compact_convex_fixedPoint hKcompact hKconvex hKne ⟨f, hf⟩

end MatrixMultiplication.AuxiliarySeparation

end OAI
end

-- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.NormalizedStates
section
namespace OAI

/-!
# Compact convex spaces of normalized additive states

These are the closed linear constraints in Appendix A. The nonemptiness of
this state space, and its instantiation by the tensor restriction semiring,
are separate statements.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

open Set

variable {S : Type*} [CommSemiring S] [Preorder S]

/-- Additive restriction-monotone states with a fixed detector inequality. -/
def normalizedStates (R : S → ℝ) (d : S) (k : ℝ) : Set (S → ℝ) :=
  {f | (∀ x, 0 ≤ f x ∧ f x ≤ R x) ∧ f 1 = 1 ∧
    (∀ x y, f (x + y) = f x + f y) ∧
    (∀ x y, x ≤ y → f x ≤ f y) ∧
    (∀ x, k * f x ≤ f (d * x))}

theorem normalizedStates_isClosed (R : S → ℝ) (d : S) (k : ℝ) :
    IsClosed (normalizedStates R d k) := by
  unfold normalizedStates
  have hb : IsClosed {f : S → ℝ | ∀ x, 0 ≤ f x ∧ f x ≤ R x} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro x
    exact (isClosed_le continuous_const (continuous_apply x)).inter
      (isClosed_le (continuous_apply x) continuous_const)
  have hn : IsClosed {f : S → ℝ | f 1 = 1} :=
    isClosed_eq (continuous_apply 1) continuous_const
  have ha : IsClosed {f : S → ℝ | ∀ x y, f (x + y) = f x + f y} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_apply (x + y))
        ((continuous_apply x).add (continuous_apply y))
  have hm : IsClosed {f : S → ℝ | ∀ x y, x ≤ y → f x ≤ f y} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_iInter fun _ => isClosed_le (continuous_apply x) (continuous_apply y)
  have hd : IsClosed {f : S → ℝ | ∀ x, k * f x ≤ f (d * x)} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun x =>
      isClosed_le (continuous_const.mul (continuous_apply x)) (continuous_apply (d * x))
  exact hb.inter (hn.inter (ha.inter (hm.inter hd)))

theorem normalizedStates_isCompact (R : S → ℝ) (d : S) (k : ℝ) :
    IsCompact (normalizedStates R d k) := by
  apply (isCompact_univ_pi (fun x => isCompact_Icc (a := (0 : ℝ)) (b := R x))).of_isClosed_subset
    (normalizedStates_isClosed R d k)
  intro f hf x _
  exact hf.1 x

theorem normalizedStates_convex (R : S → ℝ) (d : S) (k : ℝ) :
    Convex ℝ (normalizedStates R d k) := by
  intro f hf g hg a b ha hb hab
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change 0 ≤ a * f x + b * g x ∧ a * f x + b * g x ≤ R x
    constructor
    · exact add_nonneg (mul_nonneg ha (hf.1 x).1) (mul_nonneg hb (hg.1 x).1)
    · calc
        a * f x + b * g x ≤ a * R x + b * R x :=
          add_le_add (mul_le_mul_of_nonneg_left (hf.1 x).2 ha)
            (mul_le_mul_of_nonneg_left (hg.1 x).2 hb)
        _ = R x := by rw [← add_mul, hab, one_mul]
  · change a * f 1 + b * g 1 = 1
    rw [hf.2.1, hg.2.1, mul_one, mul_one, hab]
  · intro x y
    change a * f (x + y) + b * g (x + y) =
      (a * f x + b * g x) + (a * f y + b * g y)
    rw [hf.2.2.1, hg.2.2.1]
    ring
  · intro x y hxy
    exact add_le_add (mul_le_mul_of_nonneg_left (hf.2.2.2.1 x y hxy) ha)
      (mul_le_mul_of_nonneg_left (hg.2.2.2.1 x y hxy) hb)
  · intro x
    change k * (a * f x + b * g x) ≤ a * f (d * x) + b * g (d * x)
    calc
      k * (a * f x + b * g x) = a * (k * f x) + b * (k * g x) := by ring
      _ ≤ a * f (d * x) + b * g (d * x) :=
        add_le_add (mul_le_mul_of_nonneg_left (hf.2.2.2.2 x) ha)
          (mul_le_mul_of_nonneg_left (hg.2.2.2.2 x) hb)

theorem state_zero {R : S → ℝ} {d : S} {k : ℝ} {f : S → ℝ}
    (hf : f ∈ normalizedStates R d k) : f 0 = 0 := by
  have h := hf.2.2.1 0 0
  rw [zero_add] at h
  linarith

theorem state_nat_mul {R : S → ℝ} {d : S} {k : ℝ} {f : S → ℝ}
    (hf : f ∈ normalizedStates R d k) (n : ℕ) (x : S) :
    f ((n : S) * x) = (n : ℝ) * f x := by
  induction n with
  | zero => simp [state_zero hf]
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, hf.2.2.1, ih]
    push_cast
    ring

theorem state_one_le {R : S → ℝ} {d : S} {k : ℝ} {f : S → ℝ}
    (hf : f ∈ normalizedStates R d k) {z : S} (hz : 1 ≤ z) : 1 ≤ f z := by
  simpa only [hf.2.1] using hf.2.2.2.1 1 z hz

/-- Translation followed by normalization preserves every state constraint.
The two order hypotheses are exactly those supplied by tensor multiplication
and the finite rank bound in the restriction semiring. -/
theorem state_rescale {R : S → ℕ} {d : S} {k : ℝ} {f : S → ℝ}
    (hf : f ∈ normalizedStates (fun x => (R x : ℝ)) d k) (z : S)
    (hz : 1 ≤ z)
    (hmulmono : ∀ x y : S, x ≤ y → z * x ≤ z * y)
    (hdom : ∀ x : S, z * x ≤ (R x : S) * z) :
    (fun x => f (z * x) / f z) ∈ normalizedStates (fun x => (R x : ℝ)) d k := by
  have hfz : 0 < f z := lt_of_lt_of_le zero_lt_one (state_one_le hf hz)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    refine ⟨div_nonneg (hf.1 (z * x)).1 hfz.le, ?_⟩
    apply (div_le_iff₀ hfz).mpr
    have h := hf.2.2.2.1 (z * x) ((R x : S) * z) (hdom x)
    simpa only [state_nat_mul hf] using h
  · simp [mul_one, ne_of_gt hfz]
  · intro x y
    change f (z * (x + y)) / f z = f (z * x) / f z + f (z * y) / f z
    rw [mul_add, hf.2.2.1, add_div]
  · intro x y hxy
    exact div_le_div_of_nonneg_right (hf.2.2.2.1 _ _ (hmulmono x y hxy)) hfz.le
  · intro x
    have h := hf.2.2.2.2 (z * x)
    have hc : d * (z * x) = z * (d * x) := by ring
    rw [hc] at h
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right h hfz.le

end MatrixMultiplication.AuxiliarySeparation

end

end OAI
end

-- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.MultiplicativeStates
section
namespace OAI

/-! Multiplicative states obtained by normalizing translates of additive states. -/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

open Set

variable {S : Type*} [CommSemiring S]

/-- Translate a state by multiplication, then normalize at the unit. -/
def normalizedTranslate (z : S) (f : S → ℝ) : S → ℝ :=
  fun x => f (z * x) / f z

theorem normalizedTranslate_continuousOn {K : Set (S → ℝ)} (z : S)
    (hz : ∀ f ∈ K, f z ≠ 0) :
    Continuous (fun f : K => normalizedTranslate z f.val) := by
  apply continuous_pi
  intro x
  exact ((continuous_apply (z * x)).comp continuous_subtype_val).div
    ((continuous_apply z).comp continuous_subtype_val) (fun f => hz f.val f.property)

def frozenConstraint (z : S) (c : ℝ) : Set (S → ℝ) :=
  {f | ∀ x, f (z * x) = c * f x}

def frozenSlice (C : Set (S → ℝ)) (z : S) (c : ℝ) : Set (S → ℝ) :=
  C ∩ frozenConstraint z c

theorem frozenConstraint_isClosed (z : S) (c : ℝ) :
    IsClosed (frozenConstraint z c) := by
  unfold frozenConstraint
  simp only [ofPred_forall]
  exact isClosed_iInter fun x =>
    isClosed_eq (continuous_apply (z * x)) (continuous_const.mul (continuous_apply x))

theorem frozenSlice_isCompact {C : Set (S → ℝ)} (hC : IsCompact C) (z : S) (c : ℝ) :
    IsCompact (frozenSlice C z c) :=
  hC.inter_right (frozenConstraint_isClosed z c)

theorem frozenConstraint_convex (z : S) (c : ℝ) :
    Convex ℝ (frozenConstraint z c) := by
  intro f hf g hg a b _ _ _ x
  change a * f (z * x) + b * g (z * x) = c * (a * f x + b * g x)
  rw [hf x, hg x]
  ring

theorem frozenSlice_convex {C : Set (S → ℝ)} (hC : Convex ℝ C) (z : S) (c : ℝ) :
    Convex ℝ (frozenSlice C z c) :=
  hC.inter (frozenConstraint_convex z c)

theorem normalizedTranslate_mem_frozenConstraint {z w : S} {c : ℝ} {f : S → ℝ}
    (hf : f ∈ frozenConstraint z c) :
    normalizedTranslate w f ∈ frozenConstraint z c := by
  intro x
  change f (w * (z * x)) / f w = c * (f (w * x) / f w)
  rw [show w * (z * x) = z * (w * x) by ac_rfl, hf (w * x)]
  ring

theorem frozenSlice_mapsTo_normalizedTranslate {C : Set (S → ℝ)} {z w : S} {c : ℝ}
    (hC : MapsTo (normalizedTranslate w) C C) :
    MapsTo (normalizedTranslate w) (frozenSlice C z c) (frozenSlice C z c) := by
  intro f hf
  exact ⟨hC hf.1, normalizedTranslate_mem_frozenConstraint hf.2⟩

theorem frozenConstraint_value {z : S} {c : ℝ} {f : S → ℝ}
    (hf : f ∈ frozenConstraint z c) (hf1 : f 1 = 1) : f z = c := by
  simpa only [mul_one, hf1] using hf 1

theorem normalizedTranslate_eq_mem_frozenConstraint {z : S} {f : S → ℝ}
    (hfz : f z ≠ 0) (hf : normalizedTranslate z f = f) :
    f ∈ frozenConstraint z (f z) := by
  intro x
  have hx : f (z * x) / f z = f x := congrFun hf x
  exact (div_eq_iff hfz).mp hx |>.trans (mul_comm _ _)

theorem normalizedTranslate_eq_nonzero {z : S} {f : S → ℝ}
    (hf1 : f 1 = 1) (hf : normalizedTranslate z f = f) : f z ≠ 0 := by
  intro hfz
  have hx := congrFun hf 1
  simp [normalizedTranslate, hfz, hf1] at hx

theorem normalizedTranslate_eq_mem_frozenConstraint_of_normalized {z : S} {f : S → ℝ}
    (hf1 : f 1 = 1) (hf : normalizedTranslate z f = f) :
    f ∈ frozenConstraint z (f z) :=
  normalizedTranslate_eq_mem_frozenConstraint (normalizedTranslate_eq_nonzero hf1 hf) hf

theorem normalizedTranslate_eq_mem_frozenSlice {C : Set (S → ℝ)} {z : S} {f : S → ℝ}
    (hfC : f ∈ C) (hf1 : f 1 = 1) (hf : normalizedTranslate z f = f) :
    f ∈ frozenSlice C z (f z) :=
  ⟨hfC, normalizedTranslate_eq_mem_frozenConstraint_of_normalized hf1 hf⟩

/-- Every finite collection of multiplication identities holds throughout a
nonempty compact convex subset that remains invariant under all translates. -/
theorem exists_finite_multiplicative_slice {K : Set (S → ℝ)}
    (hKcompact : IsCompact K) (hKconvex : Convex ℝ K) (hKne : K.Nonempty)
    (hKnorm : ∀ f ∈ K, f 1 = 1)
    (hKnonzero : ∀ f ∈ K, ∀ z : S, z ≠ 0 → f z ≠ 0)
    (hKmap : ∀ z : S, z ≠ 0 → MapsTo (normalizedTranslate z) K K)
    (t : Finset {z : S // z ≠ 0}) :
    ∃ C : Set (S → ℝ), C ⊆ K ∧ C.Nonempty ∧ IsCompact C ∧ Convex ℝ C ∧
      (∀ z : S, z ≠ 0 → MapsTo (normalizedTranslate z) C C) ∧
      ∀ f ∈ C, ∀ z ∈ t, ∀ x, f (z.val * x) = f z.val * f x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      exact ⟨K, Subset.rfl, hKne, hKcompact, hKconvex, hKmap, by simp⟩
  | @insert z t hzt ih =>
      obtain ⟨C, hCK, hCne, hCcompact, hCconvex, hCmap, hCt⟩ := ih
      let P : C → C := fun f =>
        ⟨normalizedTranslate z.val f.val, hCmap z.val z.property f.property⟩
      have hP : Continuous P := by
        apply Continuous.subtype_mk
        exact normalizedTranslate_continuousOn z.val
          (fun f hf => hKnonzero f (hCK hf) z.val z.property)
      obtain ⟨g, hg⟩ := compact_convex_fixedPoint_of_continuous
        hCcompact hCconvex hCne P hP
      have hg' : normalizedTranslate z.val g.val = g.val := congrArg Subtype.val hg
      let c : ℝ := g.val z.val
      let D := frozenSlice C z.val c
      have hDC : D ⊆ C := fun _ hf => hf.1
      have hDK : D ⊆ K := hDC.trans hCK
      refine ⟨D, hDK, ?_, frozenSlice_isCompact hCcompact z.val c,
        frozenSlice_convex hCconvex z.val c, ?_, ?_⟩
      · exact ⟨g.val, normalizedTranslate_eq_mem_frozenSlice g.property
          (hKnorm g.val (hCK g.property)) hg'⟩
      · intro w hw
        exact frozenSlice_mapsTo_normalizedTranslate (hCmap w hw)
      · intro f hf w hw x
        rcases Finset.mem_insert.mp hw with rfl | hwt
        · have hfc : f w.val = c := frozenConstraint_value hf.2 (hKnorm f (hDK hf))
          rw [hfc]
          exact hf.2 x
        · exact hCt f (hDC hf) w hwt x

/-- A compact convex normalized state space invariant under multiplication
translates contains a multiplicative state. Frozen eigenvalue slices preserve
convexity at each finite fixed-point step. -/
theorem exists_multiplicative_of_invariant_states {K : Set (S → ℝ)}
    (hKcompact : IsCompact K) (hKconvex : Convex ℝ K) (hKne : K.Nonempty)
    (hKnorm : ∀ f ∈ K, f 1 = 1) (hKzero : ∀ f ∈ K, f 0 = 0)
    (hKnonzero : ∀ f ∈ K, ∀ z : S, z ≠ 0 → f z ≠ 0)
    (hKmap : ∀ z : S, z ≠ 0 → MapsTo (normalizedTranslate z) K K) :
    ∃ f ∈ K, ∀ x y, f (x * y) = f x * f y := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  let F : {z : S // z ≠ 0} → Set K :=
    fun z => {f | ∀ x, f.val (z.val * x) = f.val z.val * f.val x}
  have hFclosed (z : {z : S // z ≠ 0}) : IsClosed (F z) := by
    change IsClosed {f : K | ∀ x, f.val (z.val * x) = f.val z.val * f.val x}
    simp only [ofPred_forall]
    exact isClosed_iInter fun x =>
      isClosed_eq ((continuous_apply (z.val * x)).comp continuous_subtype_val)
        (((continuous_apply z.val).comp continuous_subtype_val).mul
          ((continuous_apply x).comp continuous_subtype_val))
  have hFfinite (t : Finset {z : S // z ≠ 0}) : (⋂ z ∈ t, F z).Nonempty := by
    obtain ⟨C, hCK, hCne, _, _, _, hCt⟩ := exists_finite_multiplicative_slice
      hKcompact hKconvex hKne hKnorm hKnonzero hKmap t
    obtain ⟨f, hf⟩ := hCne
    refine ⟨⟨f, hCK hf⟩, ?_⟩
    simp only [mem_iInter]
    intro z hz
    exact hCt f hf z hz
  obtain ⟨f, hf⟩ := CompactSpace.iInter_nonempty hFclosed hFfinite
  refine ⟨f.val, f.property, fun x y => ?_⟩
  by_cases hx : x = 0
  · simp [hx, hKzero f.val f.property]
  · exact mem_iInter.mp hf ⟨x, hx⟩ y

/-- Appendix A.2 for a ranked restriction semiring: once the preliminary
normalized state set is nonempty, it contains a multiplicative state. -/
theorem normalizedStates_exists_multiplicative [Preorder S]
    (R : S → ℕ) (d : S) (k : ℝ)
    (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    (hmulmono : ∀ z x y : S, x ≤ y → z * x ≤ z * y)
    (hdom : ∀ z x : S, z * x ≤ (R x : S) * z)
    (hne : (normalizedStates (fun x => (R x : ℝ)) d k).Nonempty) :
    ∃ f ∈ normalizedStates (fun x => (R x : ℝ)) d k,
      ∀ x y, f (x * y) = f x * f y := by
  apply exists_multiplicative_of_invariant_states
    (normalizedStates_isCompact _ d k) (normalizedStates_convex _ d k) hne
  · exact fun _ hf => hf.2.1
  · exact fun _ hf => state_zero hf
  · intro f hf z hz
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (state_one_le hf (hunit z hz)))
  · intro z hz f hf
    exact state_rescale hf z (hunit z hz) (hmulmono z) (hdom z)

/-- The multiplicative state as a normalized monotone semiring homomorphism,
with the original rank bounds and detector inequality preserved. -/
theorem exists_monotone_semiringHom_of_normalizedStates [Preorder S]
    (R : S → ℕ) (d : S) (k : ℝ)
    (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    (hmulmono : ∀ z x y : S, x ≤ y → z * x ≤ z * y)
    (hdom : ∀ z x : S, z * x ≤ (R x : S) * z)
    (hne : (normalizedStates (fun x => (R x : ℝ)) d k).Nonempty) :
    ∃ χ : S →+* ℝ, Monotone χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ R x) ∧ k ≤ χ d := by
  obtain ⟨f, hf, hfmul⟩ :=
    normalizedStates_exists_multiplicative R d k hunit hmulmono hdom hne
  let χ : S →+* ℝ :=
    { toFun := f
      map_zero' := state_zero hf
      map_one' := hf.2.1
      map_add' := hf.2.2.1
      map_mul' := hfmul }
  refine ⟨χ, ?_, hf.1, ?_⟩
  · intro x y hxy
    exact hf.2.2.2.1 x y hxy
  · simpa only [χ, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      mul_one, hf.2.1] using hf.2.2.2.2 1

end MatrixMultiplication.AuxiliarySeparation

end

end OAI
end

-- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.RationalSpan
section
namespace OAI

/-!
# Descent of rational linear systems

A rational linear system which has a real solution also has a rational solution.
The proof applies a rational-linear projection from the reals onto the rationals.
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- A rational-linear functional on the reals taking `1` to `1`. -/
theorem exists_ratLinear_one :
    ∃ p : ℝ →ₗ[ℚ] ℚ, p 1 = 1 :=
  Module.Projective.exists_dual_eq_one ℚ (one_ne_zero : (1 : ℝ) ≠ 0)

/-- A rational-linear projection from the reals to the rationals. -/
theorem exists_ratLinear_retraction :
    ∃ p : ℝ →ₗ[ℚ] ℚ, ∀ q : ℚ, p (q : ℝ) = q := by
  obtain ⟨p, hp⟩ := exists_ratLinear_one
  refine ⟨p, fun q ↦ ?_⟩
  have h := p.map_smul q (1 : ℝ)
  simpa [hp] using h

end MatrixMultiplication.AuxiliarySeparation

end OAI
end

-- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.RationalDenominators
section
namespace OAI

/-!
# Clearing denominators in nonnegative rational families
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- Every natural multiple of a denominator clears its nonnegative rational. -/
theorem exists_nat_eq_mul_rat_of_den_dvd {q : ℚ} (hq : 0 ≤ q)
    {D : ℕ} (hD : q.den ∣ D) :
    ∃ c : ℕ, (D : ℚ) * q = (c : ℚ) := by
  obtain ⟨k, rfl⟩ := hD
  refine ⟨k * q.num.toNat, ?_⟩
  have hnum : (q.num.toNat : ℚ) = (q.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)
  push_cast
  rw [hnum]
  calc
    (q.den : ℚ) * k * q = k * ((q.den : ℚ) * q) := by ring
    _ = k * (q.num : ℚ) := by rw [Rat.den_mul_eq_num]

/-- A finite nonnegative rational family has a common positive denominator
which turns every coefficient into a natural number. -/
theorem exists_nat_mul_eq_nat {I : Type*} [Fintype I]
    (q : I → ℚ) (hq : ∀ i, 0 ≤ q i) :
    ∃ D : ℕ, 0 < D ∧ ∃ c : I → ℕ, ∀ i, (D : ℚ) * q i = (c i : ℚ) := by
  classical
  let D : ℕ := ∏ i, (q i).den
  have hD : 0 < D := Finset.prod_pos fun i _ ↦ (q i).den_pos
  have hc : ∀ i, ∃ c : ℕ, (D : ℚ) * q i = (c : ℚ) := by
    intro i
    exact exists_nat_eq_mul_rat_of_den_dvd (hq i)
      (Finset.dvd_prod_of_mem (fun j ↦ (q j).den) (Finset.mem_univ i))
  choose c hc using hc
  exact ⟨D, hD, c, hc⟩

end MatrixMultiplication.AuxiliarySeparation

end OAI
end

-- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.RationalCone
section
namespace OAI

/-!+# Rational nonnegative certificates

Finite rational linear systems with a nonnegative real solution have a
nonnegative rational solution. Affinely independent convex representations
allow a rational-linear projection to preserve the coefficients exactly.
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- Coordinatewise inclusion of rational vectors into real vectors. -/
def rationalVectorCast {J : Type*} (v : J → ℚ) : J → ℝ := fun j ↦ v j

@[simp] theorem rationalVectorCast_apply {J : Type*} (v : J → ℚ) (j : J) :
    rationalVectorCast v j = (v j : ℝ) := rfl

/-- In an affinely independent rational family, the coefficients of a real
convex representation of a rational point are rational. -/
theorem exists_rat_convex_weights_of_affineIndependent
    {I J : Type*} [Fintype I] (v : I → J → ℚ) (b : J → ℚ)
    (w : I → ℝ)
    (hpos : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (heq : ∑ i, w i • rationalVectorCast (v i) = rationalVectorCast b)
    (hind : AffineIndependent ℝ (fun i ↦ rationalVectorCast (v i))) :
    ∃ q : I → ℚ, (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 ∧
      ∑ i, q i • v i = b := by
  classical
  obtain ⟨p, hp⟩ := exists_ratLinear_retraction
  have hpone : p 1 = 1 := by simpa using hp 1
  let q : I → ℚ := fun i ↦ p (w i)
  have hqsum : ∑ i, q i = 1 := by
    simpa only [q, map_sum, hpone] using congrArg p hsum
  have hqeq : ∑ i, q i • v i = b := by
    funext j
    have hj := congrFun heq j
    simp only [Finset.sum_apply, Pi.smul_apply, rationalVectorCast_apply,
      smul_eq_mul] at hj
    have hj' := congrArg p hj
    simp only [map_sum, hp] at hj'
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    convert hj' using 1
    apply Finset.sum_congr rfl
    intro i _
    have hm := p.map_smul (v i j) (w i)
    simpa only [q, Rat.smul_def, smul_eq_mul, mul_comm] using hm.symm
  have hqsumReal : ∑ i, (q i : ℝ) = 1 := by exact_mod_cast hqsum
  have hqeqReal :
      ∑ i, (q i : ℝ) • rationalVectorCast (v i) = rationalVectorCast b := by
    funext j
    have hj := congrFun hqeq j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hj
    simpa only [Finset.sum_apply, Pi.smul_apply, rationalVectorCast_apply,
      smul_eq_mul] using (show (∑ i, (q i : ℝ) * (v i j : ℝ)) = (b j : ℝ) by
        exact_mod_cast hj)
  have hqw : ∀ i, (q i : ℝ) = w i := by
    intro i
    exact hind.eq_of_sum_eq_sum (s := Finset.univ)
      (hqsumReal.trans hsum.symm) (hqeqReal.trans heq.symm) i (Finset.mem_univ i)
  refine ⟨q, ?_, hqsum, hqeq⟩
  intro i
  exact_mod_cast (hqw i ▸ hpos i : 0 ≤ (q i : ℝ))

/-- Taking the convex hull of rational vectors in real space does not create
new rational points. -/
theorem rationalVectorCast_mem_convexHull_descend
    {J : Type*} {s : Set (J → ℚ)} {b : J → ℚ}
    (h : rationalVectorCast b ∈ convexHull ℝ (rationalVectorCast '' s)) :
    b ∈ convexHull ℚ s := by
  classical
  obtain ⟨I, hI, z, w, hz, hind, hpos, hsum, heq⟩ :=
    eq_pos_convex_span_of_mem_convexHull h
  let : Fintype I := hI
  have hv : ∀ i, ∃ v ∈ s, rationalVectorCast v = z i := by
    intro i
    exact hz (Set.mem_range_self i)
  choose v hv hvc using hv
  obtain ⟨q, hqpos, hqsum, hqeq⟩ :=
    exists_rat_convex_weights_of_affineIndependent v b w (fun i ↦ (hpos i).le)
      hsum (by simpa only [hvc] using heq) (by simpa only [hvc] using hind)
  exact mem_convexHull_of_exists_fintype q v hqpos hqsum hv hqeq

/-- A rational point in the real cone generated by a finite rational family
already lies in the rational cone generated by that family. -/
theorem mem_rationalCone_of_nonneg_real_solution
    {I J : Type*} [Fintype I] (A : I → J → ℚ) (b : J → ℚ)
    (x : I → ℝ) (hxpos : ∀ i, 0 ≤ x i)
    (hxeq : ∀ j, ∑ i, x i * (A i j : ℝ) = (b j : ℝ)) :
    b ∈ PointedCone.hull ℚ (Set.range A) := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (∑ i, x i)
  have hNpos : (0 : ℝ) < N :=
    (Finset.sum_nonneg fun i _ ↦ hxpos i).trans_lt hN
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hNrat : (N : ℚ) ≠ 0 := by exact_mod_cast hNne
  let scaled : J → ℚ := fun j ↦ b j / N
  let v : Option I → J → ℚ := fun i ↦ match i with
    | none => 0
    | some i => A i
  let w : Option I → ℝ := fun i ↦ match i with
    | none => 1 - (∑ i, x i) / N
    | some i => x i / N
  have hwpos : ∀ i, 0 ≤ w i := by
    intro i
    cases i with
    | none =>
      change 0 ≤ 1 - (∑ i, x i) / N
      exact sub_nonneg.mpr ((div_le_one hNpos).2 hN.le)
    | some i => exact div_nonneg (hxpos i) hNpos.le
  have hwsum : ∑ i, w i = 1 := by
    simp only [Fintype.sum_option, w, ← Finset.sum_div]
    ring
  have hweq : ∑ i, w i • rationalVectorCast (v i) = rationalVectorCast scaled := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Fintype.sum_option, w, v, rationalVectorCast_apply, Pi.zero_apply,
      Rat.cast_zero, mul_zero, zero_add, scaled, Rat.cast_div, Rat.cast_natCast]
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, hxeq]
  let s : Set (J → ℚ) := insert 0 (Set.range A)
  have hv : ∀ i, rationalVectorCast (v i) ∈ rationalVectorCast '' s := by
    intro i
    refine ⟨v i, ?_, rfl⟩
    cases i with
    | none => exact Set.mem_insert 0 _
    | some i => exact Set.mem_insert_of_mem 0 (Set.mem_range_self i)
  have hcReal : rationalVectorCast scaled ∈
      convexHull ℝ (rationalVectorCast '' s) :=
    mem_convexHull_of_exists_fintype w (fun i ↦ rationalVectorCast (v i))
      hwpos hwsum hv hweq
  have hcRat : scaled ∈ convexHull ℚ s :=
    rationalVectorCast_mem_convexHull_descend hcReal
  have hs : s ⊆ PointedCone.hull ℚ (Set.range A) := by
    intro a ha
    rcases ha with rfl | ha
    · exact Submodule.zero_mem _
    · exact PointedCone.subset_hull ha
  have hscaled : scaled ∈ PointedCone.hull ℚ (Set.range A) :=
    convexHull_min hs (PointedCone.convex _) hcRat
  have hscale : (N : ℚ) • scaled = b := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, scaled]
    field_simp
  rw [← hscale]
  exact PointedCone.smul_mem _ (Nat.cast_nonneg N) hscaled

/-- Nonnegative solvability of a finite rational linear system descends from
real coefficients to rational coefficients. The equation index type may be
infinite. -/
theorem exists_nonneg_rat_solution_of_real
    {I J : Type*} [Fintype I] (A : I → J → ℚ) (b : J → ℚ)
    (h : ∃ x : I → ℝ, (∀ i, 0 ≤ x i) ∧
      ∀ j, ∑ i, x i * (A i j : ℝ) = (b j : ℝ)) :
    ∃ q : I → ℚ, (∀ i, 0 ≤ q i) ∧ ∀ j, ∑ i, q i * A i j = b j := by
  obtain ⟨x, hxpos, hxeq⟩ := h
  have hb := mem_rationalCone_of_nonneg_real_solution A b x hxpos hxeq
  obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun ({x : ℚ // 0 ≤ x})).1 hb
  refine ⟨fun i ↦ (q i : ℚ), fun i ↦ (q i).property, ?_⟩
  intro j
  have hj := congrFun hq j
  simpa only [Finset.sum_apply, Pi.smul_apply, ← Nonneg.coe_smul, smul_eq_mul] using hj

/-- Clearing denominators turns a nonnegative real solution of a rational
system into a positive integer multiple with natural coefficients. -/
theorem exists_nat_scaled_solution_of_nonneg_real
    {I J : Type*} [Fintype I] (A : I → J → ℚ) (b : J → ℚ)
    (h : ∃ x : I → ℝ, (∀ i, 0 ≤ x i) ∧
      ∀ j, ∑ i, x i * (A i j : ℝ) = (b j : ℝ)) :
    ∃ D : ℕ, 0 < D ∧ ∃ c : I → ℕ,
      ∀ j, ∑ i, (c i : ℚ) * A i j = (D : ℚ) * b j := by
  obtain ⟨q, hqpos, hqeq⟩ := exists_nonneg_rat_solution_of_real A b h
  obtain ⟨D, hDpos, c, hc⟩ := exists_nat_mul_eq_nat q hqpos
  refine ⟨D, hDpos, c, fun j ↦ ?_⟩
  calc
    ∑ i, (c i : ℚ) * A i j = ∑ i, ((D : ℚ) * q i) * A i j := by simp only [hc]
    _ = (D : ℚ) * ∑ i, q i * A i j := by rw [Finset.mul_sum]; simp only [mul_assoc]
    _ = (D : ℚ) * b j := by rw [hqeq]

/-- Integer form of finite cone certificate extraction. This is the form used
when the selected additive relations have integral coefficients. -/
theorem exists_nat_scaled_int_solution_of_nonneg_real
    {I J : Type*} [Fintype I] (A : I → J → ℤ) (b : J → ℤ)
    (h : ∃ x : I → ℝ, (∀ i, 0 ≤ x i) ∧
      ∀ j, ∑ i, x i * (A i j : ℝ) = (b j : ℝ)) :
    ∃ D : ℕ, 0 < D ∧ ∃ c : I → ℕ,
      ∀ j, ∑ i, (c i : ℤ) * A i j = (D : ℤ) * b j := by
  obtain ⟨x, hxpos, hxeq⟩ := h
  obtain ⟨D, hDpos, c, hc⟩ :=
    exists_nat_scaled_solution_of_nonneg_real
      (fun i j ↦ (A i j : ℚ)) (fun j ↦ (b j : ℚ))
      ⟨x, hxpos, by simpa using hxeq⟩
  refine ⟨D, hDpos, c, fun j ↦ ?_⟩
  exact_mod_cast hc j

end MatrixMultiplication.AuxiliarySeparation

end OAI
end

-- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.ConeSupport
section
namespace OAI

/-!
# Independent generators for a finite conical combination

Every conical combination can be expressed using a linearly independent
subfamily of its original generators.
-/

namespace MatrixMultiplication.AuxiliarySeparation

variable {I E : Type*} [AddCommGroup E] [Module ℝ E]

private theorem exists_positive_relation (A : I → E) (s : Finset I)
    (h : ¬ LinearIndependent ℝ (fun i : s ↦ A i)) :
    ∃ g : I → ℝ, (∑ i ∈ s, g i • A i) = 0 ∧ ∃ i ∈ s, 0 < g i := by
  classical
  obtain ⟨g, hg, i, hi, hgi⟩ :=
    (not_linearIndepOn_finset_iff (R := ℝ) (v := A)).mp h
  rcases lt_or_gt_of_ne hgi with hneg | hpos
  · refine ⟨fun j ↦ -g j, ?_, i, hi, neg_pos.mpr hneg⟩
    simp_rw [neg_smul, Finset.sum_neg_distrib, hg, neg_zero]
  · exact ⟨g, hg, i, hi, hpos⟩

private theorem exists_nonneg_representation_erase [DecidableEq I] (A : I → E) (s : Finset I)
    (w : I → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (h : ¬ LinearIndependent ℝ (fun i : s ↦ A i)) :
    ∃ i ∈ s, ∃ v : I → ℝ, (∀ j ∈ s.erase i, 0 ≤ v j) ∧
      (∑ j ∈ s.erase i, v j • A j) = ∑ j ∈ s, w j • A j := by
  classical
  obtain ⟨g, hg, i, hi, hgi⟩ := exists_positive_relation A s h
  let p := s.filter fun i ↦ 0 < g i
  obtain ⟨i₀, hi₀, hmin⟩ :
      ∃ i₀ ∈ p, ∀ j ∈ p, w i₀ / g i₀ ≤ w j / g j := by
    apply p.exists_min_image
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  have hi₀s : i₀ ∈ s := (Finset.mem_filter.mp hi₀).1
  have hgi₀ : 0 < g i₀ := (Finset.mem_filter.mp hi₀).2
  let v : I → ℝ := fun j ↦ w j - w i₀ / g i₀ * g j
  have hvi₀ : v i₀ = 0 := by simp [v, ne_of_gt hgi₀]
  refine ⟨i₀, hi₀s, v, ?_, ?_⟩
  · intro j hj
    have hjs : j ∈ s := Finset.mem_of_mem_erase hj
    dsimp [v]
    apply sub_nonneg.mpr
    by_cases hjp : j ∈ p
    · have hgj : 0 < g j := (Finset.mem_filter.mp hjp).2
      exact (le_div_iff₀ hgj).mp (hmin j hjp)
    · have hgj : g j ≤ 0 := by
        simpa only [p, Finset.mem_filter, hjs, true_and, not_lt] using hjp
      exact (mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (hw i₀ hi₀s) hgi₀.le) hgj).trans (hw j hjs)
  · calc
      (∑ j ∈ s.erase i₀, v j • A j) = ∑ j ∈ s, v j • A j := by
        apply Finset.sum_erase
        rw [hvi₀, zero_smul]
      _ = ∑ j ∈ s, w j • A j := by
        simp only [v, sub_smul, mul_smul, Finset.sum_sub_distrib,
          ← Finset.smul_sum, hg, smul_zero, sub_zero]

/-- A nonnegative finite combination uses a linearly independent subfamily
after possibly changing its coefficients. -/
theorem exists_nonneg_representation_linearIndependent (A : I → E) (s : Finset I)
    (w : I → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    ∃ t : Finset I, t ⊆ s ∧ LinearIndependent ℝ (fun i : t ↦ A i) ∧
      ∃ v : I → ℝ, (∀ i ∈ t, 0 ≤ v i) ∧
        (∑ i ∈ t, v i • A i) = ∑ i ∈ s, w i • A i := by
  classical
  induction s using Finset.strongInductionOn generalizing w with
  | _ s ih =>
    by_cases hs : LinearIndependent ℝ (fun i : s ↦ A i)
    · exact ⟨s, Finset.Subset.refl _, hs, w, hw, rfl⟩
    · obtain ⟨i, hi, v, hv, heq⟩ := exists_nonneg_representation_erase A s w hw hs
      obtain ⟨t, hts, ht, z, hz, hzeq⟩ := ih (s.erase i) (Finset.erase_ssubset hi) v hv
      exact ⟨t, hts.trans (Finset.erase_subset _ _), ht, z, hz, hzeq.trans heq⟩

/-- Every element of a finitely generated cone belongs to the cone generated
by some linearly independent subfamily of the given generators. -/
theorem exists_linearIndependent_subcone [Fintype I] (A : I → E) {x : E}
    (hx : x ∈ PointedCone.hull ℝ (Set.range A)) :
    ∃ s : Finset I, LinearIndependent ℝ (fun i : s ↦ A i) ∧
      x ∈ PointedCone.hull ℝ (Set.range (fun i : s ↦ A i)) := by
  classical
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun ({x : ℝ // 0 ≤ x})).mp hx
  obtain ⟨s, _, hs, v, hv, heq⟩ :=
    exists_nonneg_representation_linearIndependent A Finset.univ
      (fun i ↦ (w i : ℝ)) (fun i _ ↦ (w i).property)
  refine ⟨s, hs, ?_⟩
  have hsum : (∑ i ∈ s, v i • A i) = x := by
    exact heq.trans (by simpa only [← Nonneg.coe_smul] using hw)
  rw [← hsum]
  apply Submodule.sum_mem
  intro i hi
  exact PointedCone.smul_mem _ (hv i hi)
    (PointedCone.subset_hull ⟨⟨i, hi⟩, rfl⟩)

end MatrixMultiplication.AuxiliarySeparation

end OAI
end

-- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.FiniteConeClosed
section
namespace OAI

/-!
# Closed finitely generated cones
-/

open Topology

namespace MatrixMultiplication.AuxiliarySeparation

/-- A finite conic combination is a sum with nonnegative coefficients. -/
theorem mem_pointedCone_hull_range_iff {I E : Type*} [Fintype I]
    [AddCommGroup E] [Module ℝ E] (A : I → E) (x : E) :
    x ∈ PointedCone.hull ℝ (Set.range A) ↔
      ∃ c : I → ℝ, (∀ i, 0 ≤ c i) ∧ ∑ i, c i • A i = x := by
  rw [PointedCone.hull, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨fun i ↦ (c i : ℝ), fun i ↦ (c i).2, hc⟩
  · rintro ⟨c, hc, hcx⟩
    exact ⟨fun i ↦ ⟨c i, hc i⟩, hcx⟩

/-- The cone spanned by a finite linearly independent family is closed. -/
theorem isClosed_pointedCone_hull_range_of_linearIndependent
    {I E : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : I → E) (hA : LinearIndependent ℝ A) :
    IsClosed (PointedCone.hull ℝ (Set.range A) : Set E) := by
  let f := Fintype.linearCombination ℝ A
  have hf : IsClosedEmbedding f :=
    LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.mpr hA.fintypeLinearCombination_injective)
  have hnonneg : IsClosed {c : I → ℝ | ∀ i, 0 ≤ c i} := by
    simpa only [Set.ofPred_forall] using
      isClosed_iInter fun i ↦ isClosed_le (continuous_const : Continuous fun _ : I → ℝ ↦ (0 : ℝ)) (continuous_apply i)
  have heq : (PointedCone.hull ℝ (Set.range A) : Set E) =
      f '' {c : I → ℝ | ∀ i, 0 ≤ c i} := by
    ext x
    change x ∈ PointedCone.hull ℝ (Set.range A) ↔ _
    rw [mem_pointedCone_hull_range_iff]
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    rfl
  rw [heq]
  exact hf.isClosedMap _ hnonneg

/-- A cone generated by a finite family of real vectors is closed. -/
theorem isClosed_pointedCone_hull_range
    {I E : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : I → E) :
    IsClosed (PointedCone.hull ℝ (Set.range A) : Set E) := by
  classical
  let S := {s : Finset I // LinearIndependent ℝ (fun i : s ↦ A i)}
  have heq : (PointedCone.hull ℝ (Set.range A) : Set E) =
      ⋃ s : S, (PointedCone.hull ℝ (Set.range (fun i : s.1 ↦ A i)) : Set E) := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, hx⟩ := exists_linearIndependent_subcone A hx
      exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, hx⟩
    · intro hx
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
      apply Submodule.span_mono _ hs
      rintro _ ⟨i, rfl⟩
      exact ⟨i.1, rfl⟩
  rw [heq]
  exact isClosed_iUnion_of_finite fun s : S ↦
    isClosed_pointedCone_hull_range_of_linearIndependent _ s.2

end MatrixMultiplication.AuxiliarySeparation

end OAI
end

-- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.Farkas
section
namespace OAI

/-!
# Finite rational cone duality

A finite family of integral vectors admits a normalized nonnegative linear
functional whenever the negative normalizing vector has no positive integral
multiple in the monoid generated by the family.
-/

namespace MatrixMultiplication.AuxiliarySeparation

/-- Closed-cone separation followed by rational certificate extraction yields
a normalized nonnegative linear functional. -/
theorem exists_normalized_nonneg_linear_of_no_nat_certificate_of_isClosed
    {I J : Type*} [Fintype I] [Fintype J]
    (A : I → J → ℤ) (u : J → ℤ)
    (hclosed : IsClosed (PointedCone.hull ℝ
      (Set.range (fun i j ↦ (A i j : ℝ))) : Set (J → ℝ)))
    (hno : ¬ ∃ D : ℕ, 0 < D ∧ ∃ c : I → ℕ,
      ∀ j, ∑ i, (c i : ℤ) * A i j = -(D : ℤ) * u j) :
    ∃ L : (J → ℝ) →ₗ[ℝ] ℝ,
      L (fun j ↦ (u j : ℝ)) = 1 ∧
      ∀ i, 0 ≤ L (fun j ↦ (A i j : ℝ)) := by
  classical
  let C : ProperCone ℝ (J → ℝ) :=
    { toSubmodule := PointedCone.hull ℝ (Set.range (fun i j ↦ (A i j : ℝ)))
      isClosed' := hclosed }
  have houtside : -(fun j ↦ (u j : ℝ)) ∉ C := by
    intro hmem
    obtain ⟨x, hx⟩ :=
      (Submodule.mem_span_range_iff_exists_fun ({x : ℝ // 0 ≤ x})).1 hmem
    have hreal : ∃ x : I → ℝ, (∀ i, 0 ≤ x i) ∧
        ∀ j, ∑ i, x i * (A i j : ℝ) = ((-u j : ℤ) : ℝ) := by
      refine ⟨fun i ↦ (x i : ℝ), fun i ↦ (x i).property, fun j ↦ ?_⟩
      have hj := congrFun hx j
      simpa only [Finset.sum_apply, Pi.smul_apply, ← Nonneg.coe_smul,
        smul_eq_mul, Pi.neg_apply, Int.cast_neg] using hj
    obtain ⟨D, hD, c, hc⟩ :=
      exists_nat_scaled_int_solution_of_nonneg_real A (fun j ↦ -u j) hreal
    exact hno ⟨D, hD, c, fun j ↦ by simpa only [mul_neg, neg_mul] using hc j⟩
  obtain ⟨f, hf, hfu⟩ := C.hyperplane_separation_point houtside
  have hpos : 0 < f (fun j ↦ (u j : ℝ)) := by
    simpa only [map_neg, neg_neg, neg_lt_zero] using hfu
  refine ⟨(f (fun j ↦ (u j : ℝ)))⁻¹ • f.toLinearMap, ?_, fun i ↦ ?_⟩
  · simp only [LinearMap.smul_apply, ContinuousLinearMap.coe_coe, smul_eq_mul]
    exact inv_mul_cancel₀ hpos.ne'
  · change 0 ≤ (f (fun j ↦ (u j : ℝ)))⁻¹ * f (fun j ↦ (A i j : ℝ))
    exact mul_nonneg (inv_nonneg.mpr hpos.le)
      (hf _ (PointedCone.subset_hull (Set.mem_range_self i)))

/-- A finite integral cone either contains a positive integer multiple of the
negative normalizing vector, or admits a linear functional which is
nonnegative on the generators and takes value one on that vector. -/
theorem exists_normalized_nonneg_linear_of_no_nat_certificate
    {I J : Type*} [Fintype I] [Fintype J]
    (A : I → J → ℤ) (u : J → ℤ)
    (hno : ¬ ∃ D : ℕ, 0 < D ∧ ∃ c : I → ℕ,
      ∀ j, ∑ i, (c i : ℤ) * A i j = -(D : ℤ) * u j) :
    ∃ L : (J → ℝ) →ₗ[ℝ] ℝ,
      L (fun j ↦ (u j : ℝ)) = 1 ∧
      ∀ i, 0 ≤ L (fun j ↦ (A i j : ℝ)) :=
  exists_normalized_nonneg_linear_of_no_nat_certificate_of_isClosed A u
    (isClosed_pointedCone_hull_range _) hno

end MatrixMultiplication.AuxiliarySeparation

end OAI
end

-- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.Catalyst
section
namespace OAI

/-!
# Catalysts from additive completion certificates

Equality in the Grothendieck additive group means equality after adding a
common element of the original semiring. This gives catalytic inequalities
without assuming additive cancellation.
-/

namespace MatrixMultiplication.AuxiliarySeparation

open Algebra

variable {S : Type*} [CommSemiring S] [Preorder S]

/-- A negative-unit certificate in the additive completion gives a catalytic
inequality in the original semiring, even when its addition is not cancellative. -/
theorem exists_catalyst_of_completion_eq
    (hadd : ∀ a b c d : S, a ≤ b → c ≤ d → a + c ≤ b + d)
    (m k : ℕ) (d X Y s : S) (hXY : X ≤ Y)
    (heq : -(m : ℤ) • GrothendieckAddGroup.of (1 : S) =
      GrothendieckAddGroup.of Y - GrothendieckAddGroup.of X +
        GrothendieckAddGroup.of (d * s) - k • GrothendieckAddGroup.of s) :
    ∃ D : S, D + (m : S) + d * s ≤ D + (k : S) * s := by
  let η : S →+ GrothendieckAddGroup S := GrothendieckAddGroup.of
  have hm : η (m : S) = m • η 1 := by
    rw [← nsmul_one m, map_nsmul]
  have hk : η ((k : S) * s) = k • η s := by
    rw [← nsmul_eq_mul, map_nsmul]
  have heq' : η ((m : S) + Y + d * s) = η (X + (k : S) * s) := by
    simp only [map_add, hm, hk]
    change -(m : ℤ) • η 1 = η Y - η X + η (d * s) - k • η s at heq
    simp only [neg_zsmul, natCast_zsmul] at heq
    calc
      m • η 1 + η Y + η (d * s) =
          m • η 1 + (η Y - η X + η (d * s) - k • η s) + η X + k • η s := by abel
      _ = m • η 1 + -(m • η 1) + η X + k • η s := by rw [← heq]
      _ = η X + k • η s := by abel
  obtain ⟨C, hC⟩ := (AddLocalization.addMonoidOf (⊤ : AddSubmonoid S)).exists_of_eq heq'
  refine ⟨(C : S) + Y, ?_⟩
  calc
    ((C : S) + Y) + (m : S) + d * s = (C : S) + ((m : S) + Y + d * s) := by ac_rfl
    _ = (C : S) + (X + (k : S) * s) := hC
    _ ≤ (C : S) + (Y + (k : S) * s) :=
      hadd _ _ _ _ le_rfl (hadd _ _ _ _ hXY le_rfl)
    _ = ((C : S) + Y) + (k : S) * s := by ac_rfl

/-- A finite nonnegative integral combination of completion relations gives
one catalytic inequality. The catalyst absorbs the aggregate of the ordered
relations, and the resulting test element is the same combination of the
original test elements. -/
theorem exists_catalyst_of_completion_sum_eq
    (hadd : ∀ a b c d : S, a ≤ b → c ≤ d → a + c ≤ b + d)
    {I : Type*} [Fintype I] (m k : ℕ) (d : S)
    (n : I → ℕ) (X Y Z : I → S) (hXY : ∀ i, X i ≤ Y i)
    (heq : -(m : ℤ) • GrothendieckAddGroup.of (1 : S) =
      ∑ i, n i • (GrothendieckAddGroup.of (Y i) - GrothendieckAddGroup.of (X i) +
        GrothendieckAddGroup.of (d * Z i) - k • GrothendieckAddGroup.of (Z i))) :
    ∃ D : S, D + (m : S) + d * (∑ i, n i • Z i) ≤
      D + (k : S) * (∑ i, n i • Z i) := by
  classical
  have hnsmul (a b : S) (hab : a ≤ b) (l : ℕ) : l • a ≤ l • b := by
    induction l with
    | zero => simp
    | succ l ih => simpa only [succ_nsmul] using hadd _ _ _ _ ih hab
  have hsum (t : Finset I) : ∑ i ∈ t, n i • X i ≤ ∑ i ∈ t, n i • Y i := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih =>
      simpa only [Finset.sum_insert hi] using
        hadd _ _ _ _ (hnsmul (X i) (Y i) (hXY i) (n i)) ih
  apply exists_catalyst_of_completion_eq hadd m k d
    (∑ i, n i • X i) (∑ i, n i • Y i) (∑ i, n i • Z i) (hsum Finset.univ)
  convert heq using 1
  simp only [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    map_sum, map_nsmul, Finset.mul_sum, mul_smul_comm, ← smul_comm k]
  rw [Finset.smul_sum]

end MatrixMultiplication.AuxiliarySeparation

end OAI
end

-- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.Coordinates
section
namespace OAI

/-!
# Extending a finite coordinate functional

A linear functional on a finite coordinate set determines a state on the
whole index type by evaluating coordinate indicators. Its value on any
finitely supported integral vector depends only on those finite coordinates.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

/-- Extend a functional on a finite coordinate set by zero outside that set. -/
def finiteCoordinateState {S : Type*} (H : Finset S)
    (L : (H → ℝ) →ₗ[ℝ] ℝ) (x : S) : ℝ := by
  classical
  exact L (fun j : H ↦ if (j : S) = x then 1 else 0)

@[simp] theorem finiteCoordinateState_eq_zero_of_not_mem {S : Type*}
    (H : Finset S) (L : (H → ℝ) →ₗ[ℝ] ℝ) {x : S} (hx : x ∉ H) :
    finiteCoordinateState H L x = 0 := by
  classical
  unfold finiteCoordinateState
  have hz : (fun j : H ↦ if (j : S) = x then (1 : ℝ) else 0) = 0 := by
    funext j
    simp only [Pi.zero_apply, ite_eq_right_iff, one_ne_zero, imp_false]
    exact fun h ↦ hx (h ▸ j.property)
  rw [hz, map_zero]

/-- Evaluating a finitely supported integral vector against the extended
state agrees with restricting its coordinates and applying the functional. -/
theorem linearCombination_finiteCoordinateState {S : Type*}
    (H : Finset S) (L : (H → ℝ) →ₗ[ℝ] ℝ) (v : S →₀ ℤ) :
    Finsupp.linearCombination ℤ (finiteCoordinateState H L) v =
      L (fun j : H ↦ (v j : ℝ)) := by
  classical
  induction v using Finsupp.induction with
  | zero =>
    simp only [map_zero, Finsupp.zero_apply, Int.cast_zero]
    exact (L.map_zero).symm
  | single_add x n v _ _ ih =>
    rw [map_add, Finsupp.linearCombination_single, ih]
    have hsingle :
        (fun j : H ↦ ((Finsupp.single x n : S →₀ ℤ) j : ℝ)) =
          n • (fun j : H ↦ if (j : S) = x then (1 : ℝ) else 0) := by
      funext j
      by_cases hj : (j : S) = x
      · simp [hj]
      · simp [hj]
    have hadd :
        (fun j : H ↦ ((Finsupp.single x n + v) j : ℝ)) =
          (fun j : H ↦ ((Finsupp.single x n : S →₀ ℤ) j : ℝ)) +
            (fun j : H ↦ (v j : ℝ)) := by
      funext j
      simp
    rw [hadd, map_add, hsingle, map_zsmul]
    rfl

end MatrixMultiplication.AuxiliarySeparation

end

end OAI
end

-- OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.StateObstruction
section
namespace OAI

/-!+# Finite obstructions to normalized additive states

The state equations are homogeneous integer inequalities, except for the
normalization at the unit. Their finite certificates are interpreted in the
additive group completion, preserving catalysts in the original semiring.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

open Set

variable {S : Type*} [CommSemiring S] [Preorder S]

/-- The homogeneous inequalities defining a normalized additive state. Both
signs of the additive relation are included. -/
inductive StateConstraint (S : Type*) [Preorder S] where
  | lower (x : S)
  | upper (x : S)
  | addPos (x y : S)
  | addNeg (x y : S)
  | order (x y : S) (h : x ≤ y)
  | detector (x : S)

/-- Integer coefficient vector of a homogeneous state constraint. -/
def stateConstraintVector (R : S → ℕ) (d : S) (k : ℕ)
    (c : StateConstraint S) : S →₀ ℤ := by
  classical
  exact match c with
  | .lower x => Finsupp.single x 1
  | .upper x => Finsupp.single (1 : S) (R x : ℤ) - Finsupp.single x 1
  | .addPos x y => Finsupp.single (x + y) 1 - Finsupp.single x 1 - Finsupp.single y 1
  | .addNeg x y => -(Finsupp.single (x + y) 1 - Finsupp.single x 1 - Finsupp.single y 1)
  | .order x y _ => Finsupp.single y 1 - Finsupp.single x 1
  | .detector x => Finsupp.single (d * x) 1 - Finsupp.single x (k : ℤ)

/-- Evaluation of a finite integer coefficient vector on a real-valued function. -/
def statePairing (f : S → ℝ) : (S →₀ ℤ) →ₗ[ℤ] ℝ :=
  Finsupp.linearCombination ℤ f

omit [CommSemiring S] [Preorder S] in
theorem statePairing_apply (f : S → ℝ) (v : S →₀ ℤ) :
    statePairing f v = ∑ x ∈ v.support, (v x : ℝ) * f x := by
  simp [statePairing, Finsupp.linearCombination_apply, Finsupp.sum, zsmul_eq_mul]

omit [CommSemiring S] [Preorder S] in
@[simp] theorem statePairing_single (f : S → ℝ) (x : S) (n : ℤ) :
    statePairing f (Finsupp.single x n) = (n : ℝ) * f x := by
  simp [statePairing, zsmul_eq_mul]

omit [CommSemiring S] [Preorder S] in
theorem continuous_statePairing (v : S →₀ ℤ) :
    Continuous (fun f : S → ℝ ↦ statePairing f v) := by
  simp only [statePairing_apply]
  exact continuous_finsetSum _ fun x _ ↦ continuous_const.mul (continuous_apply x)

theorem normalizedStates_iff_stateConstraint (R : S → ℕ) (d : S) (k : ℕ)
    (f : S → ℝ) :
    f ∈ normalizedStates (fun x ↦ (R x : ℝ)) d k ↔
      f 1 = 1 ∧ ∀ c : StateConstraint S, 0 ≤ statePairing f (stateConstraintVector R d k c) := by
  classical
  constructor
  · intro hf
    refine ⟨hf.2.1, ?_⟩
    intro c
    cases c with
    | lower x => simpa [stateConstraintVector] using (hf.1 x).1
    | upper x =>
      simp only [stateConstraintVector, map_sub, statePairing_single, Int.cast_natCast,
        Int.cast_one, one_mul, hf.2.1, mul_one, sub_nonneg]
      exact (hf.1 x).2
    | addPos x y => simp [stateConstraintVector, hf.2.2.1]
    | addNeg x y => simp [stateConstraintVector, hf.2.2.1]
    | order x y h => simpa [stateConstraintVector, sub_nonneg] using hf.2.2.2.1 x y h
    | detector x => simpa [stateConstraintVector, sub_nonneg] using hf.2.2.2.2 x
  · rintro ⟨hn, hc⟩
    refine ⟨?_, hn, ?_, ?_, ?_⟩
    · intro x
      constructor
      · simpa [stateConstraintVector] using hc (.lower x)
      · simpa [stateConstraintVector, hn, sub_nonneg] using hc (.upper x)
    · intro x y
      have hp := hc (.addPos x y)
      have hm := hc (.addNeg x y)
      simp [stateConstraintVector] at hp hm
      linarith
    · intro x y hxy
      simpa [stateConstraintVector, sub_nonneg] using hc (.order x y hxy)
    · intro x
      simpa [stateConstraintVector, sub_nonneg] using hc (.detector x)

/-- The ordinary monotonicity difference in a state constraint. -/
def stateConstraintLower (c : StateConstraint S) : S :=
  match c with
  | .lower _ => 0
  | .upper x => x
  | .order x _ _ => x
  | _ => 0

def stateConstraintUpper (R : S → ℕ) (c : StateConstraint S) : S :=
  match c with
  | .lower x => x
  | .upper x => R x
  | .order _ y _ => y
  | _ => 0

/-- The multiplier of the distinguished detector difference. -/
def stateConstraintDetector (c : StateConstraint S) : S :=
  match c with
  | .detector x => x
  | _ => 0

theorem stateConstraintLower_le_upper (R : S → ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (c : StateConstraint S) :
    stateConstraintLower c ≤ stateConstraintUpper R c := by
  cases c with
  | lower x => exact hzero x
  | upper x => exact hbound x
  | order _ _ h => exact h
  | addPos _ _ => exact le_rfl
  | addNeg _ _ => exact le_rfl
  | detector _ => exact le_rfl

/-- Interpreting a constraint in the group completion separates its ordinary
order difference from its detector difference. -/
theorem stateConstraintVector_completion (R : S → ℕ) (d : S) (k : ℕ)
    (c : StateConstraint S) :
    Finsupp.linearCombination ℤ (Algebra.GrothendieckAddGroup.of (M := S))
        (stateConstraintVector R d k c) =
      Algebra.GrothendieckAddGroup.of (stateConstraintUpper R c) -
        Algebra.GrothendieckAddGroup.of (stateConstraintLower c) +
      Algebra.GrothendieckAddGroup.of (d * stateConstraintDetector c) -
        k • Algebra.GrothendieckAddGroup.of (stateConstraintDetector c) := by
  classical
  have hcast (n : ℕ) : Algebra.GrothendieckAddGroup.of (n : S) =
      n • Algebra.GrothendieckAddGroup.of (1 : S) := by
    rw [← nsmul_one, map_nsmul]
  cases c <;>
    simp [stateConstraintVector, stateConstraintLower, stateConstraintUpper,
      stateConstraintDetector, hcast, Nat.cast_smul_eq_nsmul, map_add] <;> abel

/-- In the absence of a catalytic obstruction, no positive multiple of the
negative unit is a natural combination of state-constraint vectors. -/
theorem no_stateConstraint_certificate (R : S → ℕ) (d : S) (k : ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (hadd : ∀ a b c e : S, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hno : ∀ (D s : S) (m : ℕ), 0 < m →
      ¬D + (m : S) + d * s ≤ D + (k : S) * s)
    {I : Type*} [Fintype I] (cs : I → StateConstraint S) :
    ¬∃ m : ℕ, 0 < m ∧ ∃ n : I → ℕ,
      ∑ i, n i • stateConstraintVector R d k (cs i) =
        -(m : ℤ) • Finsupp.single (1 : S) (1 : ℤ) := by
  classical
  rintro ⟨m, hm, n, hn⟩
  have heq := congrArg
    (Finsupp.linearCombination ℤ (Algebra.GrothendieckAddGroup.of (M := S))) hn
  simp only [map_sum, map_nsmul, map_smul, Finsupp.linearCombination_single,
    one_smul, stateConstraintVector_completion] at heq
  obtain ⟨D, hD⟩ := exists_catalyst_of_completion_sum_eq hadd m k d n
    (fun i ↦ stateConstraintLower (cs i)) (fun i ↦ stateConstraintUpper R (cs i))
    (fun i ↦ stateConstraintDetector (cs i))
    (fun i ↦ stateConstraintLower_le_upper R hzero hbound (cs i)) heq.symm
  exact hno D _ m hm hD

/-- Every finite family of constraints supported on `H` has a normalized
solution that vanishes outside `H`, provided no positive catalyst exists. -/
theorem finite_stateConstraint_solution (R : S → ℕ) (d : S) (k : ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (hadd : ∀ a b c e : S, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hno : ∀ (D s : S) (m : ℕ), 0 < m →
      ¬D + (m : S) + d * s ≤ D + (k : S) * s)
    {I : Type*} [Fintype I] (cs : I → StateConstraint S) (H : Finset S) (hOne : (1 : S) ∈ H)
    (hH : ∀ i, (stateConstraintVector R d k (cs i)).support ⊆ H) :
    ∃ f : S → ℝ, f 1 = 1 ∧
      (∀ i, 0 ≤ statePairing f (stateConstraintVector R d k (cs i))) ∧
      ∀ x ∉ H, f x = 0 := by
  classical
  let A : I → H → ℤ := fun i j ↦ stateConstraintVector R d k (cs i) j
  let u : H → ℤ := fun j ↦ (Finsupp.single (1 : S) (1 : ℤ)) j
  have hcert : ¬∃ m : ℕ, 0 < m ∧ ∃ n : I → ℕ,
      ∀ j, ∑ i, (n i : ℤ) * A i j = -(m : ℤ) * u j := by
    rintro ⟨m, hm, n, hn⟩
    apply no_stateConstraint_certificate R d k hzero hbound hadd hno cs
    refine ⟨m, hm, n, ?_⟩
    ext x
    by_cases hx : x ∈ H
    · have heq := hn ⟨x, hx⟩
      by_cases hx1 : (1 : S) = x <;>
        simpa [A, u, Finsupp.coe_finsetSum, Finset.sum_apply,
          Finsupp.smul_apply, nsmul_eq_mul, zsmul_eq_mul, Finsupp.single_apply, hx1] using heq
    · have hz : ∀ i, stateConstraintVector R d k (cs i) x = 0 := by
        intro i
        apply Finsupp.notMem_support_iff.mp
        exact fun h ↦ hx (hH i h)
      simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
        hz, smul_zero, Finset.sum_const_zero]
      have hx1 : x ≠ 1 := by
        rintro rfl
        exact hx hOne
      simp [hx1]
  obtain ⟨L, hLu, hLA⟩ :=
    exists_normalized_nonneg_linear_of_no_nat_certificate A u hcert
  let f := finiteCoordinateState H L
  refine ⟨f, ?_, ?_, ?_⟩
  · have heq := linearCombination_finiteCoordinateState H L
      (Finsupp.single (1 : S) (1 : ℤ))
    simpa [f, u] using heq.trans hLu
  · intro i
    simpa only [statePairing, f, linearCombination_finiteCoordinateState, A] using hLA i
  · intro x hx
    exact finiteCoordinateState_eq_zero_of_not_mem H L hx

/-- A finite collection of state constraints can be solved while keeping all
coordinates in their rank intervals. -/
theorem bounded_finite_stateConstraint_solution (R : S → ℕ) (d : S) (k : ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (hadd : ∀ a b c e : S, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hno : ∀ (D s : S) (m : ℕ), 0 < m →
      ¬D + (m : S) + d * s ≤ D + (k : S) * s)
    (F : Finset (StateConstraint S)) :
    ∃ f : S → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ R x) ∧ f 1 = 1 ∧
      ∀ c ∈ F, 0 ≤ statePairing f (stateConstraintVector R d k c) := by
  classical
  let H : Finset S := insert 1 (F.biUnion fun c ↦ (stateConstraintVector R d k c).support)
  have hOne : (1 : S) ∈ H := Finset.mem_insert_self _ _
  let cs : F ⊕ (Bool × H) → StateConstraint S
    | .inl c => c
    | .inr (false, x) => .lower x
    | .inr (true, x) => .upper x
  have hH : ∀ i, (stateConstraintVector R d k (cs i)).support ⊆ H := by
    intro i a ha
    cases i with
    | inl c =>
      exact Finset.mem_insert_of_mem
        (Finset.mem_biUnion.mpr ⟨c, c.property, ha⟩)
    | inr i =>
      rcases i with ⟨tag, x⟩
      by_contra hnot
      have ha1 : a ≠ 1 := by
        rintro rfl
        exact hnot hOne
      have hax : a ≠ (x : S) := by
        rintro rfl
        exact hnot x.property
      have ha0 := Finsupp.mem_support_iff.mp ha
      cases tag <;>
        simp [cs, stateConstraintVector, ha1, hax] at ha0
  obtain ⟨f, hf1, hfc, hfzero⟩ :=
    finite_stateConstraint_solution R d k hzero hbound hadd hno cs H hOne hH
  refine ⟨f, ?_, hf1, ?_⟩
  · intro x
    by_cases hx : x ∈ H
    · have hlo := hfc (.inr (false, ⟨x, hx⟩))
      have hhi := hfc (.inr (true, ⟨x, hx⟩))
      constructor
      · simpa [cs, stateConstraintVector] using hlo
      · simpa [cs, stateConstraintVector, hf1, sub_nonneg] using hhi
    · rw [hfzero x hx]
      exact ⟨le_rfl, Nat.cast_nonneg _⟩
  · intro c hc
    exact hfc (.inl ⟨c, hc⟩)

/-- Absence of positive scalar-gain catalysts guarantees the existence of a
normalized additive monotone state satisfying the detector inequality. -/
theorem normalizedStates_nonempty_of_no_catalyst (R : S → ℕ) (d : S) (k : ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (hadd : ∀ a b c e : S, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hno : ∀ (D s : S) (m : ℕ), 0 < m →
      ¬D + (m : S) + d * s ≤ D + (k : S) * s) :
    (normalizedStates (fun x ↦ (R x : ℝ)) d k).Nonempty := by
  let B : Set (S → ℝ) := {f | ∀ x, 0 ≤ f x ∧ f x ≤ R x}
  let K : Set (S → ℝ) := B ∩ {f | f 1 = 1}
  let t : StateConstraint S → Set (S → ℝ) :=
    fun c ↦ {f | 0 ≤ statePairing f (stateConstraintVector R d k c)}
  have hBcompact : IsCompact B :=
    isCompact_pi_infinite (fun x ↦ isCompact_Icc (a := (0 : ℝ)) (b := (R x : ℝ)))
  have hKcompact : IsCompact K :=
    hBcompact.inter_right (isClosed_eq (continuous_apply 1) continuous_const)
  have htclosed : ∀ c, IsClosed (t c) := fun c ↦
    isClosed_le continuous_const (continuous_statePairing (stateConstraintVector R d k c))
  have hfinite : ∀ F : Finset (StateConstraint S), (K ∩ ⋂ c ∈ F, t c).Nonempty := by
    intro F
    obtain ⟨f, hfb, hf1, hfc⟩ :=
      bounded_finite_stateConstraint_solution R d k hzero hbound hadd hno F
    refine ⟨f, ⟨hfb, hf1⟩, ?_⟩
    simp only [Set.mem_iInter]
    exact hfc
  obtain ⟨f, hfK, hft⟩ := hKcompact.inter_iInter_nonempty t htclosed hfinite
  refine ⟨f, (normalizedStates_iff_stateConstraint R d k f).mpr ?_⟩
  exact ⟨hfK.2, fun c ↦ Set.mem_iInter.mp hft c⟩

end MatrixMultiplication.AuxiliarySeparation

end

end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.ComparisonStates
section
/-! # A spectral point from absence of additive compression

We apply the compact state-space construction with a zero detector. The
resulting multiplicative state takes nonnegative real values, so it defines a
point of the normalized spectrum.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open MatrixMultiplication.AuxiliarySeparation

/-- A bounded Strassen preorder which cannot absorb a positive scalar into an
additive catalyst admits a normalized monotone semiring homomorphism. -/
theorem spectralPoint_of_no_compression {S : Type*} [CommSemiring S] [Preorder S]
    (R : S → ℕ) (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (hadd : ∀ a b c d : S, a ≤ b → c ≤ d → a + c ≤ b + d)
    (hmul : ∀ z a b : S, a ≤ b → z * a ≤ z * b)
    (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    (hno : ∀ (D : S) (m : ℕ), 0 < m → ¬ D + (m : S) ≤ D) :
    (normalizedSpectrum ((· ≤ ·) : S → S → Prop)).Nonempty := by
  have hstates := normalizedStates_nonempty_of_no_catalyst R 0 0 hzero hbound hadd
    (fun D s m hm => by simpa only [Nat.cast_zero, zero_mul, add_zero] using hno D m hm)
  have hdom (z x : S) : z * x ≤ (R x : S) * z :=
    (hmul z _ _ (hbound x)).trans_eq (mul_comm _ _)
  obtain ⟨f, hf, hfbound, _⟩ :=
    exists_monotone_semiringHom_of_normalizedStates R 0 0 hunit hmul hdom (by simpa only [Nat.cast_zero] using hstates)
  refine ⟨fun x => ⟨f x, (hfbound x).1⟩, ?_⟩
  exact ⟨Subtype.ext (map_zero f), Subtype.ext (map_one f),
    fun x y => Subtype.ext (map_add f x y), fun x y => Subtype.ext (map_mul f x y),
    fun _ _ h => hf h⟩

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.SiteTensor.ComparisonBound
section
/-! # Bounding one tensor by copies of a nonzero tensor

A finite upper bound for tensor rank and a restriction to the unit from any
nonzero tensor give Strassen's boundedness condition for the restriction order.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

universe v

variable {I K : Type*} [Fintype I] [Nonempty I]

instance [CommSemiring K] : IsOrderedAddMonoid (TensorClass.{v} I K) where
  add_le_add_left _ _ h _ := add_mono h le_rfl

instance [CommSemiring K] : IsOrderedMonoid (TensorClass.{v} I K) where
  mul_le_mul_left _ _ h _ := mul_mono h le_rfl

variable [Field K]

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end

-- OAI.LinearAlgebra.SpectralBooks.GroundFieldComparison
section
/-!
# Strict spectral comparison over every field

Adjoin the comparison `y ≤ x` to the restriction order. A normalized spectral
point for the enlarged order would contradict the strict price gap. The state
existence theorem therefore supplies a compression in that order, which pays
for the tensor powers in the original order.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open scoped NNReal

/-- Strict separation by all spectral points forces one uniform comparison for
all positive powers. Boundedness by naturals and the unit lower bound on
nonzero elements are the rank hypotheses in Strassen's restriction semiring. -/
theorem powerComparison_of_spectral_lt {S : Type*} [CommSemiring S] [Preorder S]
    [IsOrderedAddMonoid S] [IsOrderedMonoid S] (hzero : ∀ z : S, 0 ≤ z)
    (hbound : ∀ z : S, ∃ n : ℕ, z ≤ (n : S)) (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    {x y : S} (hy : y ≠ 0)
    (hgap : ∀ f : normalizedSpectrum ((· ≤ ·) : S → S → Prop), f.val x < f.val y) :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 0 < n → x ^ n ≤ C • y ^ n := by
  classical
  by_contra hnone
  let R (a : S) : ℕ := (hbound a).choose
  have hno (D : S) (m : ℕ) (hm : 0 < m) : ¬ TradeLE x y (D + m) D :=
    fun h => hnone (powerComparison_of_tradeCompression hzero hbound (hunit y hy) hm h)
  obtain ⟨f, hf⟩ := @spectralPoint_of_no_compression S _ (tradePreorder x y) R
    (fun a => TradeLE.of_le (hzero a)) (fun a => TradeLE.of_le (hbound a).choose_spec)
    (fun _ _ _ _ h g => TradeLE.add h g) (fun z _ _ h => TradeLE.mul_left z h)
    (fun z hz => TradeLE.of_le (hunit z hz)) hno
  have point : f ∈ normalizedSpectrum ((· ≤ ·) : S → S → Prop) :=
    ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, fun a b h => hf.2.2.2.2 a b (TradeLE.of_le h)⟩
  exact (hgap ⟨f, point⟩).not_ge (hf.2.2.2.2 y x (TradeLE.reversed x y))

namespace SiteTensor

universe v
variable (I K : Type*) [Fintype I] [Nonempty I] [Field K]

/-- Strict comparison in Proposition 2.1, for local linear restriction of
actual finite tensors, over the given ground field. -/
theorem strictSpectralComparison : StrictSpectralComparison.{v} I K :=
  fun _ _ _ hy hgap => powerComparison_of_spectral_lt zero_le_tensor exists_le_natCast
    (fun _ => one_le_of_ne_zero) hy hgap

/-- The finite-family ordinary-sum expansion now has no external
strict-comparison hypothesis. -/
theorem expandedStrictComparison :
    ExpandedStrictComparison (Set.range (logPoint.{v} (I := I) (K := K)))
      (fun x y => classOfProduct x ≤ classOfProduct y) ClassOrdinarySum :=
  expandedStrictComparison_of_strict (strictSpectralComparison I K)

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
end


namespace OAI.LinearAlgebra.SpectralBooks.SiteTensor
universe v
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
theorem spectral_value_pos
    (φ : normalizedSpectrum (S := TensorClass.{v} I K) (· ≤ ·))
    {X : TensorClass.{v} I K} (h : X ≠ 0) : 0 < φ.val X := by
  have hu := φ.property.2.2.2.2 1 X (one_le_of_ne_zero h)
  rw [φ.property.2.1] at hu
  exact zero_lt_one.trans_le hu

end OAI.LinearAlgebra.SpectralBooks.SiteTensor
namespace OMAPort
abbrev T (I : Type) := Σ d : I → ℕ, (∀ i, Fin (d i)) → ℂ


variable {I : Type} [Fintype I] [DecidableEq I]
def sigAdd (X Y : T I) : T I :=
  ⟨fun i => X.1 i + Y.1 i, fun z =>
          if h : ∀ i, (z i : ℕ) < X.1 i then X.2 (fun i => ⟨z i, h i⟩)
          else if h' : ∀ i, X.1 i ≤ z i then
            Y.2 (fun i => ⟨z i - X.1 i, by have h2 : (z i : ℕ) < X.1 i + Y.1 i := (z i).2; have := h' i; omega⟩)
          else 0⟩

/-- The coordinate tensor product, as in the target statement. -/
def sigMul (X Y : T I) : T I :=
  ⟨fun i => X.1 i * Y.1 i, fun z => X.2 (fun i => (finProdFinEquiv.symm (z i)).1) *
          Y.2 (fun i => (finProdFinEquiv.symm (z i)).2)⟩


end OMAPort
namespace OMA.PlanarInterval

open OMAPort OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical

variable {I : Type} [Fintype I] [DecidableEq I]

def CoordMono (F : T I → ℝ) : Prop :=
  ∀ X Y : T I, (∃ A : ∀ i, Matrix (Fin (Y.1 i)) (Fin (X.1 i)) ℂ,
    ∀ y, Y.2 y = ∑ z, (∏ i, A i (y i) (z i)) * X.2 z) → F Y ≤ F X

def CoordPoint (F : T I → ℝ) : Prop :=
  (∀ X, 0 ≤ F X) ∧ F ⟨fun _ => 1, fun _ => 1⟩ = 1 ∧
  (∀ X, (∀ z, X.2 z = 0) → F X = 0) ∧ CoordMono F ∧
  (∀ X Y, F (sigMul X Y) = F X * F Y) ∧ ∀ X Y, F (sigAdd X Y) = F X + F Y

def wireCoord (a b : I) : T I :=
  ⟨fun i => if i = a ∨ i = b then 2 else 1, fun z => if (z a : ℕ) = z b then 1 else 0⟩

abbrev coordRaw (X : T I) : Raw.{0} I ℂ :=
  ⟨fun i => Fin (X.1 i), fun _ => inferInstance, X.2⟩

noncomputable def coordEval [Nonempty I]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop)) (X : T I) : ℝ :=
  (φ.val (ofRaw (coordRaw X)) : ℝ)

theorem coord_eval_mono [Nonempty I]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop)) : CoordMono (coordEval φ) := by
  intro X Y h
  apply NNReal.coe_le_coe.mpr
  apply φ.property.2.2.2.2
  apply ofRaw_le_iff.mpr
  obtain ⟨A,hA⟩ := h
  exact ⟨A, fun y => (hA y).trans (Finset.sum_congr (by ext; simp) fun z _ => mul_comm _ _)⟩

theorem coord_mul (X Y : T I) :
    ofRaw (coordRaw (sigMul X Y)) = ofRaw ((coordRaw X).mul (coordRaw Y)) := by
  symm
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent (fun _ => finProdFinEquiv) ?_)
  intro x
  change (∀ i, Fin (X.1 i) × Fin (Y.1 i)) at x
  change X.2 (fun i => (x i).1) * Y.2 (fun i => (x i).2) =
    X.2 (fun i => (finProdFinEquiv.symm (finProdFinEquiv (x i))).1) *
    Y.2 (fun i => (finProdFinEquiv.symm (finProdFinEquiv (x i))).2)
  simp only [Equiv.symm_apply_apply]

theorem coord_add [Nonempty I] (X Y : T I) :
    ofRaw (coordRaw (sigAdd X Y)) = ofRaw ((coordRaw X).add (coordRaw Y)) := by
  classical
  symm
  apply ofRaw_eq_iff.mpr
  apply Raw.reindex_equivalent (fun i => finSumFinEquiv)
  intro x
  change (∀ i, Fin (X.1 i) ⊕ Fin (Y.1 i)) at x
  change sumCoeff X.2 Y.2 x = (sigAdd X Y).2 (fun i => finSumFinEquiv (x i))
  dsimp only [sigAdd]
  by_cases hL : ∀ i, ∃ a, x i = Sum.inl a
  · choose a ha using hL
    obtain rfl : x = fun i => Sum.inl (a i) := funext ha
    rw [sumCoeff_inl, dif_pos (by simpa only [finSumFinEquiv_apply_left, Fin.val_castAdd] using fun i => (a i).isLt)]
    apply congrArg X.2
    funext i
    exact Fin.ext (by simp [finSumFinEquiv_apply_left])
  · by_cases hR : ∀ i, ∃ b, x i = Sum.inr b
    · choose b hb using hR
      obtain rfl : x = fun i => Sum.inr (b i) := funext hb
      have hn : ¬∀ i, (finSumFinEquiv (Sum.inr (b i) : Fin (X.1 i) ⊕ Fin (Y.1 i)) : ℕ) < X.1 i := by
        intro hall
        have h := hall (Classical.choice ‹Nonempty I›)
        simpa [finSumFinEquiv_apply_right] using h
      rw [sumCoeff_inr, dif_neg hn, dif_pos (by simp [finSumFinEquiv_apply_right])]
      apply congrArg Y.2
      funext i
      exact Fin.ext (by simp [finSumFinEquiv_apply_right])
    · rw [sumCoeff_mixed]
      · rw [dif_neg, dif_neg]
        · intro hall
          apply hR
          intro i
          have hi := hall i
          cases hx : x i with
          | inl a => simp [hx, finSumFinEquiv_apply_left, a.isLt.not_ge] at hi
          | inr b => exact ⟨b,rfl⟩
        · intro hall
          apply hL
          intro i
          have hi := hall i
          cases hx : x i with
          | inl a => exact ⟨a,rfl⟩
          | inr b => simp [hx, finSumFinEquiv_apply_right] at hi
      · rintro a rfl
        exact hL fun i => ⟨a i,rfl⟩
      · rintro b rfl
        exact hR fun i => ⟨b i,rfl⟩

theorem coord_eval_point [Nonempty I]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop)) : CoordPoint (coordEval φ) := by
  refine ⟨fun _ => NNReal.coe_nonneg _, ?_, ?_, coord_eval_mono φ, ?_, ?_⟩
  · have h : ofRaw (coordRaw (I := I) ⟨fun _ => 1,fun _ => 1⟩) = 1 :=
      ofRaw_eq_iff.mpr (Raw.reindex_equivalent (fun _ => Equiv.equivPUnit (Fin 1)) (fun _ => rfl))
    simp [coordEval, h, φ.property.2.1]
  · intro X h
    have hz : ofRaw (coordRaw X) = 0 := (ofRaw_eq_zero_iff _).mpr (funext h)
    simp [coordEval, hz, φ.property.1]
  · intro X Y
    simp only [coordEval, coord_mul, ofRaw_mul, φ.property.2.2.2.1, NNReal.coe_mul]
  · intro X Y
    simp only [coordEval, coord_add, ofRaw_add, φ.property.2.2.1, NNReal.coe_add]


end OMA.PlanarInterval
namespace OMA.FourSiteComparison

open OMAPort OMA.PlanarInterval
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

abbrev FourTensor := T (Fin 4)
abbrev FourClass := TensorClass.{0} (Fin 4) ℂ
abbrev cls (X : FourTensor) : FourClass := ofRaw (coordRaw X)
def unit : FourTensor := ⟨fun _ => 1, fun _ => 1⟩
def null : FourTensor := ⟨fun _ => 1, fun _ => 0⟩
def power (X : FourTensor) (n : ℕ) : FourTensor := Nat.rec unit (fun _ Z => sigMul Z X) n
def copies (X : FourTensor) (c : ℕ) : FourTensor := Nat.rec null (fun _ Z => sigAdd Z X) c
def matching (a b c d : Fin 4) : FourTensor := sigMul (wireCoord a b) (wireCoord c d)

theorem cls_pow (X : FourTensor) (n : ℕ) : cls (power X n) = cls X ^ n := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact ofRaw_eq_iff.mpr (Raw.reindex_equivalent (fun _ => Equiv.equivPUnit (Fin 1)) (fun _ => rfl))
  | succ n ih =>
    change cls (sigMul (power X n) X) = _
    change ofRaw (coordRaw (sigMul (power X n) X)) = _
    rw [coord_mul, ofRaw_mul, pow_succ]
    exact congrArg (· * cls X) ih

theorem cls_copies (X : FourTensor) (c : ℕ) : cls (copies X c) = c • cls X := by
  induction c with
  | zero => exact ((ofRaw_eq_zero_iff _).mpr rfl).trans (zero_nsmul _).symm
  | succ c ih =>
    change ofRaw (coordRaw (sigAdd (copies X c) X)) = _
    rw [coord_add, ofRaw_add, succ_nsmul]
    exact congrArg (· + cls X) ih

theorem wire_ne (a b : Fin 4) : cls (wireCoord a b) ≠ 0 := by
  intro h
  have zero := (ofRaw_eq_zero_iff _).mp h
  let x (j : Fin 4) : Fin ((wireCoord a b).1 j) := ⟨0, by
    change 0 < (if j = a ∨ j = b then 2 else 1)
    split <;> decide⟩
  have h0 := congrFun zero x
  change (if (x a : ℕ) = x b then (1 : ℂ) else 0) = 0 at h0
  simp [x] at h0

theorem matching_ne (a b c d : Fin 4) : cls (matching a b c d) ≠ 0 := by
  change ofRaw (coordRaw (sigMul (wireCoord a b) (wireCoord c d))) ≠ 0
  rw [coord_mul, ofRaw_mul]
  exact mul_ne_zero (wire_ne a b) (wire_ne c d)

theorem eval_pow {F : FourTensor → ℝ} (hF : CoordPoint F) (X : FourTensor) (k : ℕ) :
    F (power X k) = F X ^ k := by
  induction k with
  | zero => exact hF.2.1.trans (pow_zero _).symm
  | succ k ih =>
    change F (sigMul (power X k) X) = _
    rw [hF.2.2.2.2.1, ih, pow_succ]

theorem matching_comparison
    (ht : ∀ F : FourTensor → ℝ, CoordPoint F →
      let d := fun i j => Real.logb 2 (F (wireCoord i j))
      d 0 1 + d 2 3 ≤ max (d 0 2 + d 1 3) (d 0 3 + d 1 2))
    (k : ℕ) :
    let U := matching 0 1 2 3
    let V := matching 0 2 1 3
    let W := matching 0 3 1 2
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      cls (power (power U k) n) ≤ cls (copies (power (sigAdd (power V k) (power W k)) n) C) := by
  let U := matching 0 1 2 3
  let V := matching 0 2 1 3
  let W := matching 0 3 1 2
  let B := sigAdd (power V k) (power W k)
  have hB : cls B ≠ 0 := by
    intro h
    change ofRaw (coordRaw (sigAdd (power V k) (power W k))) = 0 at h
    rw [coord_add, ofRaw_add] at h
    change cls (power V k) + cls (power W k) = 0 at h
    rw [cls_pow, cls_pow] at h
    have hh : cls V ^ k ≤ cls V ^ k + cls W ^ k := le_add_of_nonneg_right (zero_le_tensor _)
    rw [h] at hh
    exact (pow_ne_zero k (matching_ne 0 2 1 3)) (le_antisymm hh (zero_le_tensor _))
  have gap (φ : normalizedSpectrum ((· ≤ ·) : FourClass → _ → Prop)) :
      φ.val (cls (power U k)) < φ.val (cls B) := by
    let F := coordEval φ
    have hF : CoordPoint F := coord_eval_point φ
    have pos (i j : Fin 4) : 0 < F (wireCoord i j) :=
      NNReal.coe_pos.mpr (spectral_value_pos φ (wire_ne i j))
    have mp (i j l m : Fin 4) : F (matching i j l m) = F (wireCoord i j) * F (wireCoord l m) :=
      hF.2.2.2.2.1 _ _
    have hpos (i j l m : Fin 4) : 0 < F (matching i j l m) := (mp i j l m) ▸ mul_pos (pos i j) (pos l m)
    have price (i j l m : Fin 4) : Real.logb 2 (F (matching i j l m)) =
        Real.logb 2 (F (wireCoord i j)) + Real.logb 2 (F (wireCoord l m)) := by
      rw [mp, Real.logb_mul (pos _ _).ne' (pos _ _).ne']
    have ht' := ht F hF
    change _ + _ ≤ max (_ + _) (_ + _) at ht'
    rw [← price, ← price, ← price] at ht'
    change F (power U k) < F (sigAdd (power V k) (power W k))
    rw [hF.2.2.2.2.2, eval_pow hF, eval_pow hF, eval_pow hF]
    have positiveV : 0 < F V ^ k := pow_pos (hpos 0 2 1 3) k
    have positiveW : 0 < F W ^ k := pow_pos (hpos 0 3 1 2) k
    rcases le_max_iff.mp ht' with h | h
    · have q : F U ≤ F V := (Real.logb_le_logb (by norm_num : 1 < (2 : ℝ))
        (hpos 0 1 2 3) (hpos 0 2 1 3)).mp h
      exact (pow_le_pow_left₀ (hF.1 U) q k).trans_lt (lt_add_of_pos_right _ positiveW)
    · have q : F U ≤ F W := (Real.logb_le_logb (by norm_num : 1 < (2 : ℝ))
        (hpos 0 1 2 3) (hpos 0 3 1 2)).mp h
      exact (pow_le_pow_left₀ (hF.1 U) q k).trans_lt (lt_add_of_pos_left _ positiveV)
  obtain ⟨C,hC,cmp⟩ := powerComparison_of_spectral_lt zero_le_tensor exists_le_natCast
    (fun _ => one_le_of_ne_zero) hB gap
  refine ⟨C,hC,fun n hn => ?_⟩
  simpa only [cls_pow, cls_copies] using cmp n hn

end OMA.FourSiteComparison

open OMA.FourSiteComparison OMA.PlanarInterval OMAPort
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

theorem OMA.FourSiteRanksComparison : OMA.R_Erdos20_erdos_20_R1_H2_R1_H1_R1_H1_R2.H2 := by
  intro ht k _
  obtain ⟨C,hC,cmp⟩ := matching_comparison ht k
  refine ⟨C,hC,fun n hn => ?_⟩
  obtain ⟨M,hM⟩ := ofRaw_le_iff.mp (cmp n hn)
  refine ⟨M, fun y => (hM y).trans (Finset.sum_congr ?_ fun _ _ => mul_comm _ _)⟩
  exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)


/-! Rank tests shared by the two alternative pairings in the four-site tensor condition. -/

namespace OMA.FourSiteRanks

open OMAPort OMA.PlanarInterval OMA.FourSiteComparison
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical NNReal

abbrev leftCut (i : Fin 4) : Prop := i = 0 ∨ i = 2
abbrev rightCut (i : Fin 4) : Prop := i = 1 ∨ i = 2

def Aligned {L : Fin 4 → Type} {Q : Type} (s : Fin 4 → Prop)
    (x : Q → Q → ∀ i, L i) : Prop :=
  (∀ r c d i, s i → x r c i = x r d i) ∧
  (∀ r t c i, ¬s i → x r c i = x t c i)

def sample {L : Fin 4 → Type} {Q : Type} (x : Q → Q → ∀ i, L i)
    (f : (∀ i, L i) → ℂ) : Matrix Q Q ℂ := fun r c => f (x r c)

theorem rank_inst {m n : Type} (M : Matrix m n ℂ) (a b : Fintype n) :
    @Matrix.rank m n ℂ a _ M = @Matrix.rank m n ℂ b _ M :=
  congrArg (fun t => @Matrix.rank m n ℂ t _ M) (Subsingleton.elim a b)

theorem card_inst {n : Type} (a b : Fintype n) : @Fintype.card n a = @Fintype.card n b :=
  congrArg (@Fintype.card n) (Subsingleton.elim a b)

theorem sample_rank_le (R : Raw.{0} (Fin 4) ℂ) {Q : Type} [Fintype Q]
    (p : Q) (s : Fin 4 → Prop) [DecidablePred s] (x : Q → Q → ∀ i, R.Leg i)
    (h : Aligned s x) :
    (sample x R.coeff).rank ≤ cutRank s ℂ (ofRaw R) := by
  let rows (r : Q) (i : {i // s i}) := x r p i
  let cols (c : Q) (i : {i // ¬s i}) := x p c i
  have entry : (Crossing.cutMatrix s R.coeff).submatrix rows cols = sample x R.coeff := by
    ext r c
    change R.coeff ((Crossing.cutEquiv s R.Leg).symm (rows r, cols c)) = R.coeff (x r c)
    apply congrArg R.coeff
    funext i
    by_cases hi : s i
    · simpa [Crossing.cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, hi, rows]
        using h.1 r p c i hi
    · simpa [Crossing.cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, hi, cols]
        using h.2 p r c i hi
  have hle := (Crossing.cutMatrix s R.coeff).rank_submatrix_le rows cols
  rw [entry] at hle
  rw [cutRank_ofRaw]
  exact hle.trans_eq (rank_inst _ _ _)

/-- All compatible matrix samples from every local restriction of X have rank at most b. -/
def Bounded (X : FourClass) (b : ℕ) : Prop :=
  ∀ (R : Raw.{0} (Fin 4) ℂ) (Q : Type) [Fintype Q] (p : Q)
    (x : Q → Q → ∀ i, R.Leg i),
    Aligned leftCut x → Aligned rightCut x → ofRaw R ≤ X → (sample x R.coeff).rank ≤ b

theorem Bounded.weaken {X : FourClass} {a b : ℕ} (h : Bounded X a) (hab : a ≤ b) :
    Bounded X b := fun R Q _ p x hs ht hR => (h R Q p x hs ht hR).trans hab

theorem Bounded.left (X : FourClass) : Bounded X (cutRank leftCut ℂ X) := by
  intro R Q _ p x hs _ h
  exact (sample_rank_le R p leftCut x hs).trans (monotone_cutRank leftCut ℂ h)

theorem Bounded.right (X : FourClass) : Bounded X (cutRank rightCut ℂ X) := by
  intro R Q _ p x _ ht h
  exact (sample_rank_le R p rightCut x ht).trans (monotone_cutRank rightCut ℂ h)

theorem matrix_rank_add_le {Q : Type} [Fintype Q] (A B : Matrix Q Q ℂ) :
    (A+B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc
    _ ≤ Module.finrank ℂ (LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin :
          Submodule ℂ (Q → ℂ)) := Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

theorem Bounded.add {X Y : FourClass} {a b : ℕ} (ha : Bounded X a) (hb : Bounded Y b) :
    Bounded (X+Y) (a+b) := by
  intro R Q _ p x hs ht h
  have hsum : ofRaw R ≤ ∑ j : Fin 2, (![X,Y] : Fin 2 → FourClass) j := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h
  obtain ⟨z, eq, le⟩ := images_of_le_sum R (![X,Y] : Fin 2 → FourClass) hsum
  have e : sample x R.coeff = sample x (z 0) + sample x (z 1) := by
    rw [eq, Fin.sum_univ_two]
    rfl
  rw [e]
  exact (matrix_rank_add_le _ _).trans (Nat.add_le_add
    (ha {R with coeff := z 0} Q p x hs ht (le 0))
    (hb {R with coeff := z 1} Q p x hs ht (le 1)))

theorem Bounded.zero : Bounded (0 : FourClass) 0 := by
  apply (Bounded.left _).weaken
  haveI : Nonempty {i // leftCut i} := ⟨⟨0, by decide⟩⟩
  haveI : Nonempty {i // ¬ leftCut i} := ⟨⟨3, by decide⟩⟩
  have e := map_zero (normalizedSpectrum.toRingHom (cutSpectrum.{0} leftCut ℂ))
  change (cutRank leftCut ℂ 0 : ℝ≥0) = 0 at e
  exact_mod_cast e.le

theorem Bounded.copies {X : FourClass} {b : ℕ} (h : Bounded X b) (C : ℕ) :
    Bounded (C • X) (C*b) := by
  induction C with
  | zero => simpa using Bounded.zero
  | succ n ih => simpa only [succ_nsmul, Nat.succ_mul] using ih.add h

end OMA.FourSiteRanks


/-! Identity matrices inside the actual powers of the target matching. -/

namespace OMA.FourSiteRanks

open OMAPort OMA.PlanarInterval OMA.FourSiteComparison
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical

def HasIdentity (X : FourTensor) (n : ℕ) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (p : Q) (x : Q → Q → ∀ i, (coordRaw X).Leg i),
    Fintype.card Q = n ∧ Aligned leftCut x ∧ Aligned rightCut x ∧
    sample x X.2 = (1 : Matrix Q Q ℂ)

theorem HasIdentity.lower {X : FourTensor} {Y : FourClass} {a b : ℕ}
    (h : HasIdentity X a) (upper : Bounded Y b) (res : cls X ≤ Y) : a ≤ b := by
  obtain ⟨Q,_,p,x,card,hs,ht,hm⟩ := h
  have z := upper (coordRaw X) Q p x hs ht res
  change (sample x X.2).rank ≤ b at z
  simpa only [hm, Matrix.rank_one, card] using z

theorem aligned_product {X Y : FourTensor} {Q S : Type}
    {x : Q → Q → ∀ i, (coordRaw X).Leg i} {y : S → S → ∀ i, (coordRaw Y).Leg i}
    {s : Fin 4 → Prop} (hx : Aligned s x) (hy : Aligned s y) :
    Aligned (L := (coordRaw (sigMul X Y)).Leg) s
      (fun (r c : Q × S) i => finProdFinEquiv (x r.1 c.1 i, y r.2 c.2 i)) := by
  constructor
  · intro r c d i hi
    exact congrArg finProdFinEquiv (Prod.ext (hx.1 r.1 c.1 d.1 i hi) (hy.1 r.2 c.2 d.2 i hi))
  · intro r t c i hi
    exact congrArg finProdFinEquiv (Prod.ext (hx.2 r.1 t.1 c.1 i hi) (hy.2 r.2 t.2 c.2 i hi))

theorem HasIdentity.mul {X Y : FourTensor} {a b : ℕ} (hx : HasIdentity X a)
    (hy : HasIdentity Y b) : HasIdentity (sigMul X Y) (a*b) := by
  obtain ⟨Q,_,p,x,cx,lx,rx,ex⟩ := hx
  obtain ⟨S,_,q,y,cy,ly,ry,ey⟩ := hy
  let z (r c : Q × S) (i : Fin 4) : (coordRaw (sigMul X Y)).Leg i :=
    finProdFinEquiv (x r.1 c.1 i, y r.2 c.2 i)
  refine ⟨Q × S, inferInstance, (p,q), z, by simp [cx,cy],
    aligned_product lx ly, aligned_product rx ry, ?_⟩
  ext r c
  have h1 := congrFun (congrFun ex r.1) c.1
  have h2 := congrFun (congrFun ey r.2) c.2
  change X.2 (x r.1 c.1) = _ at h1
  change Y.2 (y r.2 c.2) = _ at h2
  change X.2 (fun i => (finProdFinEquiv.symm (z r c i)).1) *
    Y.2 (fun i => (finProdFinEquiv.symm (z r c i)).2) = _
  simp only [z, Equiv.symm_apply_apply, h1, h2, Matrix.one_apply]
  by_cases h : r.1 = c.1 <;> by_cases g : r.2 = c.2 <;> simp [h,g,Prod.ext_iff]

theorem identity_unit : HasIdentity unit 1 := by
  let x (_ _ : Unit) (i : Fin 4) : (coordRaw unit).Leg i := (0 : Fin 1)
  refine ⟨Unit, inferInstance, (), x, by simp, ⟨by intros; rfl, by intros; rfl⟩,
    ⟨by intros; rfl, by intros; rfl⟩, ?_⟩
  ext i j
  cases i
  cases j
  simp [sample, unit]

theorem HasIdentity.power {X : FourTensor} {a : ℕ} (h : HasIdentity X a) (n : ℕ) :
    HasIdentity (power X n) (a^n) := by
  induction n with
  | zero =>
    change HasIdentity unit (a^0)
    simpa using identity_unit
  | succ n ih =>
    change HasIdentity (sigMul (FourSiteComparison.power X n) X) (a^(n+1))
    simpa only [pow_succ] using ih.mul h

theorem wire_trivial (a b : Fin 4) : HasIdentity (wireCoord a b) 1 := by
  let x (_ _ : Unit) (i : Fin 4) : (coordRaw (wireCoord a b)).Leg i :=
    ⟨0, by change 0 < (if i = a ∨ i = b then 2 else 1); split <;> decide⟩
  refine ⟨Unit, inferInstance, (), x, by simp, ⟨by intros; rfl, by intros; rfl⟩,
    ⟨by intros; rfl, by intros; rfl⟩, ?_⟩
  ext i j
  cases i
  cases j
  simp [sample, wireCoord, x]

def endpointIndex (r c : Fin 2) (i : Fin 4) : (coordRaw (wireCoord (2 : Fin 4) 3)).Leg i :=
  if h : i = 2 then ⟨r.val, by change r.val < (if i = 2 ∨ i = 3 then 2 else 1); rw [if_pos (Or.inl h)]; exact r.isLt⟩
  else if h' : i = 3 then ⟨c.val, by change c.val < (if i = 2 ∨ i = 3 then 2 else 1); rw [if_pos (Or.inr h')]; exact c.isLt⟩
  else ⟨0, by simp [wireCoord, h, h']⟩

theorem aligned_endpoint (s : Fin 4 → Prop) (h2 : s 2) (h3 : ¬s 3) :
    Aligned s endpointIndex := by
  constructor
  · intro r c d i hi
    by_cases h : i = 3
    · exact False.elim (h3 (h ▸ hi))
    · simp [endpointIndex, h]
  · intro r t c i hi
    by_cases h : i = 2
    · exact False.elim (hi (h ▸ h2))
    · simp [endpointIndex, h]

theorem wire_identity : HasIdentity (wireCoord (2 : Fin 4) 3) 2 := by
  refine ⟨Fin 2, inferInstance, 0, endpointIndex, Fintype.card_fin _,
    aligned_endpoint _ (by decide) (by decide), aligned_endpoint _ (by decide) (by decide), ?_⟩
  ext r c
  simp [sample, endpointIndex, wireCoord, Matrix.one_apply, Fin.ext_iff]

theorem matching_identity : HasIdentity (matching 0 1 2 3) 2 := by
  simpa [matching] using (wire_trivial 0 1).mul wire_identity

end OMA.FourSiteRanks


/-! Upper bounds for compatible matrix samples of the two source matchings. -/

namespace OMA.FourSiteRanks
open OMAPort OMA.PlanarInterval OMA.FourSiteComparison
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical NNReal

local instance : Nonempty {i // leftCut i} := ⟨⟨2, by decide⟩⟩
local instance : Nonempty {i // ¬ leftCut i} := ⟨⟨3, by decide⟩⟩
local instance : Nonempty {i // rightCut i} := ⟨⟨2, by decide⟩⟩
local instance : Nonempty {i // ¬ rightCut i} := ⟨⟨3, by decide⟩⟩

def sideWidth (s : Fin 4 → Prop) [DecidablePred s] (a b : Fin 4) : ℕ :=
  ∏ i : Fin 4, if s i then (if i = a ∨ i = b then 2 else 1) else 1

theorem side_card (s : Fin 4 → Prop) [DecidablePred s] (a b : Fin 4) :
    Fintype.card (∀ i : {i // s i}, (coordRaw (wireCoord a b)).Leg i) = sideWidth s a b := by
  rw [Fintype.card_pi]
  change (∏ i : {i // s i}, Fintype.card (Fin ((wireCoord a b).1 i))) = _
  simp only [Fintype.card_fin]
  unfold sideWidth
  rw [← Finset.prod_subtype (Finset.univ.filter s) (by simp : ∀ i, i ∈ Finset.univ.filter s ↔ s i)
    (fun i => (wireCoord a b).1 i)]
  exact Finset.prod_filter s _

theorem wire_cap (s : Fin 4 → Prop) [DecidablePred s] (a b : Fin 4) :
    cutRank s ℂ (cls (wireCoord a b)) ≤ min (sideWidth s a b) (sideWidth (fun i => ¬s i) a b) := by
  let M := Crossing.cutMatrix s (coordRaw (wireCoord a b)).coeff
  have hrow := M.rank_le_card_height
  have hcol := M.rank_le_card_width
  rw [← side_card s a b, ← side_card (fun i => ¬s i) a b, cutRank_ofRaw]
  refine le_min ?_ ?_
  · exact (rank_inst M _ _).le.trans (hrow.trans_eq (card_inst _ _))
  · exact (rank_inst M _ _).le.trans (hcol.trans_eq (card_inst _ _))

theorem cut_mul (s : Fin 4 → Prop) [DecidablePred s]
    [Nonempty {i // s i}] [Nonempty {i // ¬s i}] (X Y : FourClass) :
    cutRank s ℂ (X*Y) = cutRank s ℂ X * cutRank s ℂ Y := by
  have e := map_mul (normalizedSpectrum.toRingHom (cutSpectrum.{0} s ℂ)) X Y
  change (cutRank s ℂ (X*Y) : ℝ≥0) = (cutRank s ℂ X : ℝ≥0) * (cutRank s ℂ Y : ℝ≥0) at e
  exact_mod_cast e

theorem cut_pow (s : Fin 4 → Prop) [DecidablePred s]
    [Nonempty {i // s i}] [Nonempty {i // ¬s i}] (X : FourClass) (k : ℕ) :
    cutRank s ℂ (X^k) = cutRank s ℂ X ^ k := by
  have e := map_pow (normalizedSpectrum.toRingHom (cutSpectrum.{0} s ℂ)) X k
  change (cutRank s ℂ (X^k) : ℝ≥0) = (cutRank s ℂ X : ℝ≥0)^k at e
  exact_mod_cast e

abbrev V : FourClass := cls (matching 0 2 1 3)
abbrev W : FourClass := cls (matching 0 3 1 2)

theorem matching_cap (s : Fin 4 → Prop) [DecidablePred s]
    [Nonempty {i // s i}] [Nonempty {i // ¬s i}] (a b c e : Fin 4) :
    cutRank s ℂ (cls (matching a b c e)) ≤
      min (sideWidth s a b) (sideWidth (fun i => ¬s i) a b) *
      min (sideWidth s c e) (sideWidth (fun i => ¬s i) c e) := by
  change cutRank s ℂ (ofRaw (coordRaw (sigMul (wireCoord a b) (wireCoord c e)))) ≤ _
  rw [coord_mul, ofRaw_mul, cut_mul]
  exact Nat.mul_le_mul (wire_cap s a b) (wire_cap s c e)

theorem left_V : cutRank leftCut ℂ V ≤ 1 := by
  simpa [sideWidth, Fin.prod_univ_four, leftCut] using matching_cap leftCut 0 2 1 3

theorem left_W : cutRank leftCut ℂ W ≤ 4 := by
  simpa [sideWidth, Fin.prod_univ_four, leftCut] using matching_cap leftCut 0 3 1 2

theorem right_V : cutRank rightCut ℂ V ≤ 4 := by
  simpa [sideWidth, Fin.prod_univ_four, rightCut] using matching_cap rightCut 0 2 1 3

theorem right_W : cutRank rightCut ℂ W ≤ 1 := by
  simpa [sideWidth, Fin.prod_univ_four, rightCut] using matching_cap rightCut 0 3 1 2

theorem Bounded.min {X : FourClass} {a b : ℕ} (ha : Bounded X a) (hb : Bounded X b) :
    Bounded X (min a b) := by
  intro R Q _ p x hs ht h
  exact le_min (ha R Q p x hs ht h) (hb R Q p x hs ht h)

theorem mixed_bound (k i j : ℕ) :
    Bounded ((V^k)^i * (W^k)^j) (min ((4^k)^j) ((4^k)^i)) := by
  apply Bounded.min
  · apply (Bounded.left _).weaken
    simp only [cut_mul, cut_pow]
    have a := Nat.pow_le_pow_left (Nat.pow_le_pow_left left_V k) i
    have b := Nat.pow_le_pow_left (Nat.pow_le_pow_left left_W k) j
    simpa only [one_pow, one_mul] using Nat.mul_le_mul a b
  · apply (Bounded.right _).weaken
    simp only [cut_mul, cut_pow]
    have a := Nat.pow_le_pow_left (Nat.pow_le_pow_left right_V k) i
    have b := Nat.pow_le_pow_left (Nat.pow_le_pow_left right_W k) j
    simpa only [one_pow, mul_one] using Nat.mul_le_mul a b

theorem Bounded.sum {J : Type} (s : Finset J) (T : J → FourClass) (b : J → ℕ)
    (h : ∀ j ∈ s, Bounded (T j) (b j)) : Bounded (∑ j ∈ s, T j) (∑ j ∈ s, b j) := by
  induction s using Finset.induction_on with
  | empty => simpa using Bounded.zero
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self ..)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

def sliceBudget (k n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n+1), n.choose i * min ((4^k)^(n-i)) ((4^k)^i)

theorem source_bound (k n : ℕ) : Bounded ((V^k + W^k)^n) (sliceBudget k n) := by
  rw [add_pow]
  unfold sliceBudget
  apply Bounded.sum
  intro i _
  simpa only [nsmul_eq_mul, mul_comm (n.choose i : FourClass)] using
    (mixed_bound k i (n-i)).copies (n.choose i)

end OMA.FourSiteRanks


/-! Explicit failures of tensor restriction for the matching powers in the registered statement. -/

namespace OMA.FourSiteRanks
open OMAPort OMA.PlanarInterval OMA.FourSiteComparison
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

/-- The exact matrix restrictions used in the four-site problem. -/
def Test (k C n : ℕ) : Prop :=
  let Y := power (power (matching 0 1 2 3) k) n
  let X := copies (power (sigAdd (power (matching 0 2 1 3) k) (power (matching 0 3 1 2) k)) n) C
  ∃ A : ∀ j, Matrix (Fin (Y.1 j)) (Fin (X.1 j)) ℂ,
    ∀ y, Y.2 y = ∑ z, (∏ j, A j (y j) (z j)) * X.2 z

theorem capacity_necessary {k C n : ℕ} (h : Test k C n) :
    (2^k)^n ≤ C * sliceBudget k n := by
  let U := matching 0 1 2 3
  let B := sigAdd (power (matching 0 2 1 3) k) (power (matching 0 3 1 2) k)
  have res : cls (power (power U k) n) ≤ cls (copies (power B n) C) := by
    obtain ⟨M,eq⟩ := h
    refine ⟨M,fun y => (eq y).trans (Finset.sum_congr ?_ fun _ _ => mul_comm _ _)⟩
    exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)
  have base : cls B = V^k + W^k := by
    change ofRaw (coordRaw (sigAdd _ _)) = _
    rw [coord_add, ofRaw_add]
    exact congrArg₂ (· + ·) (cls_pow _ _) (cls_pow _ _)
  rw [cls_copies, cls_pow B, base] at res
  exact ((matching_identity.power k).power n).lower ((source_bound k n).copies C) res

theorem test_fails_of_rank {k C n : ℕ} (small : C * sliceBudget k n < (2^k)^n) :
    ¬ Test k C n := fun h => (Nat.not_le_of_lt small) (capacity_necessary h)

theorem one_copy_power_obstruction {k C : ℕ} (small : 2*C < 2^k) : ¬ Test k C 1 := by
  apply test_fails_of_rank
  have hp : 1 ≤ (4:ℕ)^k := Nat.succ_le_of_lt (by positivity)
  simpa [sliceBudget, Finset.sum_range_succ, min_eq_left hp, min_eq_right hp, Nat.mul_comm] using small

theorem fourth_power_seven_copies : ¬ Test 4 7 1 :=
  test_fails_of_rank (by decide)

theorem fourth_power_three_factors : ¬ Test 4 2 3 :=
  test_fails_of_rank (by decide)

theorem finite_failures_for_every_copy_count (C : ℕ) : ∃ k, 2 ≤ k ∧ ¬ Test k C 1 := by
  refine ⟨2*C+2,by omega,one_copy_power_obstruction ?_⟩
  have h : 2*C+2 < 2^(2*C+2) := Nat.lt_two_pow_self
  omega

/-- At every exponent the middle term already puts this necessary bound within a factor 2^k
of the target. This identifies exactly why these rank tests alone do not prove the witness. -/
theorem central_term_bound (k n : ℕ) : (2^k)^n ≤ (2^k) * sliceBudget k n := by
  let i := n / 2
  have hi : i ≤ n := Nat.div_le_self _ _
  have hij : i ≤ n-i := by dsimp [i]; omega
  have hcover : n ≤ 1+2*i := by dsimp [i]; omega
  have hmin : min (((4:ℕ)^k)^(n-i)) ((4^k)^i) = (4^k)^i :=
    min_eq_right (Nat.pow_le_pow_right (by positivity) hij)
  have hchoose : 1 ≤ n.choose i := Nat.choose_pos hi
  have hterm : (4^k)^i ≤ sliceBudget k n := by
    have a : n.choose i * min (((4:ℕ)^k)^(n-i)) ((4^k)^i) ≤ sliceBudget k n :=
      Finset.single_le_sum (f := fun j => n.choose j * min (((4:ℕ)^k)^(n-j)) ((4^k)^j))
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega : i < n+1))
    rw [hmin] at a
    exact (show (4^k)^i ≤ n.choose i * (4^k)^i by
      simpa only [one_mul] using Nat.mul_le_mul_right ((4^k)^i) hchoose).trans a
  calc
    (2^k)^n ≤ (2^k)^(1+2*i) := Nat.pow_le_pow_right (by positivity) hcover
    _ = 2^k * (4^k)^i := by
      rw [pow_add, pow_one, pow_mul]
      congr 2
      rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
      norm_num
    _ ≤ _ := Nat.mul_le_mul_left _ hterm

end OMA.FourSiteRanks



/-! Crossing rank bound from Arth Singh and contributors, Lower bounds for Naslund’s crossing problem.
Adapted from https://github.com/Arth-Singh/crossing-lower-bounds/blob/31ce9aac07ca04c2d12e50635339ebda1fc37417/SwapSplit.lean
under Apache-2.0. The module header and imports have been adapted to Lean 4.33.1.
-/

open Matrix

namespace SwapSplit

/-- The swap matrix: rows (x, y), columns (u, v), entry [u = y][v = x]. -/
def swapMat (F : Type*) [Field F] (N : ℕ) : Matrix (Fin N × Fin N) (Fin N × Fin N) F :=
  fun p q => if q.1 = p.2 ∧ q.2 = p.1 then 1 else 0

/-- The realignment (x, y), (u, v) ↦ (x, u), (y, v); its rank is the operator Schmidt rank. -/
def realign {F : Type*} [Field F] {N : ℕ} (C : Matrix (Fin N × Fin N) (Fin N × Fin N) F) :
    Matrix (Fin N × Fin N) (Fin N × Fin N) F :=
  fun p q => C (p.1, q.1) (p.2, q.2)

/-! ### Rank facts -/

/-- Rank is subadditive. -/
theorem rank_add_le' {m n K : Type*} [Fintype m] [Fintype n] [Field K]
    (A B : Matrix m n K) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc Module.finrank K (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ Module.finrank K ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin : Submodule K (m → K)) :=
        Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

/-- Sylvester's rank inequality: rank A + rank B ≤ rank (A * B) + (inner dimension). -/
theorem sylvester_rank {F : Type*} [Field F] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq n] [DecidableEq p] (A : Matrix m n F) (B : Matrix n p F) :
    A.rank + B.rank ≤ (A * B).rank + Fintype.card n := by
  classical
  set f := A.mulVecLin
  set g := B.mulVecLin
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.range g)
  have hdim : Module.finrank F (LinearMap.range g) + Module.finrank F W = Fintype.card n := by
    have := Submodule.finrank_add_eq_of_isCompl hW
    simpa using this
  have hrange : LinearMap.range f ≤ (LinearMap.range g).map f ⊔ W.map f := by
    rw [← Submodule.map_sup, hW.sup_eq_top, Submodule.map_top]
  have h1 : Module.finrank F (LinearMap.range f) ≤
      Module.finrank F ((LinearMap.range g).map f) + Module.finrank F (W.map f) :=
    le_trans (Submodule.finrank_mono hrange) (Submodule.finrank_add_le_finrank_add_finrank _ _)
  have h2 : Module.finrank F (W.map f) ≤ Module.finrank F W := Submodule.finrank_map_le f W
  have h3 : (LinearMap.range g).map f = LinearMap.range (A * B).mulVecLin := by
    rw [Matrix.mulVecLin_mul, LinearMap.range_comp]
  have hA : A.rank = Module.finrank F (LinearMap.range f) := rfl
  have hB : B.rank = Module.finrank F (LinearMap.range g) := rfl
  have hAB : (A * B).rank = Module.finrank F (LinearMap.range (A * B).mulVecLin) := rfl
  rw [h3] at h1
  omega

/-- A matrix of rank r is a sum of r matrices of rank one. -/
theorem exists_sum_vecMulVec_of_rank {F m n : Type*} [Field F] [Fintype m] [Fintype n]
    (A : Matrix m n F) :
    ∃ (U : Fin A.rank → m → F) (V : Fin A.rank → n → F), A = ∑ k, Matrix.vecMulVec (U k) (V k) := by
  classical
  set W : Submodule F (m → F) := Submodule.span F (Set.range A.col) with hW
  have hr : Module.finrank F W = A.rank := (Matrix.rank_eq_finrank_span_cols A).symm
  let b : Module.Basis (Fin A.rank) F W := Module.finBasisOfFinrankEq F W hr
  have hcol : ∀ j, A.col j ∈ W := fun j => Submodule.subset_span ⟨j, rfl⟩
  refine ⟨fun k => (b k : m → F), fun k j => b.repr ⟨A.col j, hcol j⟩ k, ?_⟩
  ext i j
  have hsum := b.sum_repr ⟨A.col j, hcol j⟩
  have hi := congrArg (fun w : W => (w : m → F) i) hsum
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hi
  rw [Matrix.sum_apply]
  simp only [Matrix.vecMulVec_apply]
  have hA : A i j = A.col j i := rfl
  rw [hA, ← hi]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

/-! ### Slices of a split -/

/-- A split S_N = B + C gives slice matrices X_y, Y_u (width rank B) and P_u, Q_y (width rank (R C)) with
X_y Y_uᵀ + P_u Q_yᵀ = [y = u] 1. -/
theorem exists_slices {F : Type*} [Field F] (N : ℕ) (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F)
    (h : swapMat F N = B + C) :
    ∃ (X Y : Fin N → Matrix (Fin N) (Fin B.rank) F) (P Q : Fin N → Matrix (Fin N) (Fin (realign C).rank) F),
      (∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1) ∧ (∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) := by
  obtain ⟨U, V, hB⟩ := exists_sum_vecMulVec_of_rank B
  obtain ⟨P, Q, hC⟩ := exists_sum_vecMulVec_of_rank (realign C)
  have hent : ∀ x y u v : Fin N, (∑ i, U i (x, y) * V i (u, v)) + (∑ l, P l (x, u) * Q l (y, v)) =
      if u = y ∧ v = x then 1 else 0 := by
    intro x y u v
    have e1 : B (x, y) (u, v) = ∑ i, U i (x, y) * V i (u, v) := by
      have := congrFun (congrFun hB (x, y)) (u, v)
      simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
    have e2 : C (x, y) (u, v) = ∑ l, P l (x, u) * Q l (y, v) := by
      have := congrFun (congrFun hC (x, u)) (y, v)
      have h0' : C (x, y) (u, v) = realign C (x, u) (y, v) := rfl
      rw [h0']
      simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
    rw [← e1, ← e2, ← Matrix.add_apply, ← h]
    rfl
  let X : Fin N → Matrix (Fin N) (Fin B.rank) F := fun y => Matrix.of fun x i => U i (x, y)
  let Y : Fin N → Matrix (Fin N) (Fin B.rank) F := fun u => Matrix.of fun v i => V i (u, v)
  let PP : Fin N → Matrix (Fin N) (Fin (realign C).rank) F := fun u => Matrix.of fun x l => P l (x, u)
  let QQ : Fin N → Matrix (Fin N) (Fin (realign C).rank) F := fun y => Matrix.of fun v l => Q l (y, v)
  have hslice : ∀ y u, X y * (Y u)ᵀ + PP u * (QQ y)ᵀ = if y = u then 1 else 0 := by
    intro y u
    ext x v
    have := hent x y u v
    simp only [X, Y, PP, QQ, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    rw [this]
    by_cases hyu : y = u
    · subst hyu
      by_cases hxv : x = v
      · subst hxv; simp
      · have hvx : ¬ v = x := fun h' => hxv h'.symm
        simp [hxv, hvx]
    · have huy : ¬ u = y := fun h' => hyu h'.symm
      simp [hyu, huy]
  exact ⟨X, Y, PP, QQ, fun y => by simpa using hslice y y, fun y u hyu => by simpa [hyu] using hslice y u⟩

/-- Submodularity: dim (A ⊔ C) + dim B ≤ dim (A ⊔ B) + dim (B ⊔ C). -/
theorem finrank_sup_triangle {F : Type*} [Field F] {N : ℕ} (A B C : Submodule F (Fin N → F)) :
    Module.finrank F ↥(A ⊔ C) + Module.finrank F B ≤ Module.finrank F ↥(A ⊔ B) + Module.finrank F ↥(B ⊔ C) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (A ⊔ B) (B ⊔ C)
  have h1 : Module.finrank F ↥(A ⊔ C) ≤ Module.finrank F ↥((A ⊔ B) ⊔ (B ⊔ C)) :=
    Submodule.finrank_mono (sup_le (le_sup_of_le_left le_sup_left) (le_sup_of_le_right le_sup_right))
  have h2 : Module.finrank F B ≤ Module.finrank F ↥((A ⊔ B) ⊓ (B ⊔ C)) :=
    Submodule.finrank_mono (le_inf le_sup_right le_sup_left)
  omega

/-! ### The bound 4 N / 3 -/

/-- The rank form of the excess lemma. For slices a ≠ b, X_a Y_bᵀ = −P_b Q_aᵀ has its column space in
col X_a ⊓ col P_b, and by Sylvester its rank is at least rank X_a + rank Y_b − r and at least
rank P_b + rank Q_a − k. Hence dim (col X_a ⊔ col P_b) + rank Y_b ≤ dim col P_b + r and
dim (col P_b ⊔ col X_a) + rank Q_a ≤ dim col X_a + k. -/
theorem slice_excess_rank {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (a b : Fin N) (hab : a ≠ b) :
    Module.finrank F ↥(LinearMap.range (X a).mulVecLin ⊔ LinearMap.range (P b).mulVecLin) + (Y b).rank ≤
        Module.finrank F (LinearMap.range (P b).mulVecLin) + r ∧
    Module.finrank F ↥(LinearMap.range (P b).mulVecLin ⊔ LinearMap.range (X a).mulVecLin) + (Q a).rank ≤
        Module.finrank F (LinearMap.range (X a).mulVecLin) + k := by
  have hcol : ∀ {m p : ℕ} (A : Matrix (Fin N) (Fin m) F) (G : Matrix (Fin m) (Fin p) F),
      LinearMap.range (A * G).mulVecLin ≤ LinearMap.range A.mulVecLin := by
    intro m p A G
    rw [Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  have e : X a * (Y b)ᵀ = P b * (-(Q a)ᵀ) := by
    rw [Matrix.mul_neg]
    exact eq_neg_of_add_eq_zero_left (ho a b hab)
  constructor
  · have hle : LinearMap.range (X a * (Y b)ᵀ).mulVecLin ≤
        LinearMap.range (X a).mulVecLin ⊓ LinearMap.range (P b).mulVecLin :=
      le_inf (hcol _ _) (by rw [e]; exact hcol _ _)
    have h1 := Submodule.finrank_mono hle
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (X a).mulVecLin)
      (LinearMap.range (P b).mulVecLin)
    have h3 := sylvester_rank (X a) (Y b)ᵀ
    simp only [Fintype.card_fin, Matrix.rank_transpose] at h3
    have h4 : (X a * (Y b)ᵀ).rank = Module.finrank F (LinearMap.range (X a * (Y b)ᵀ).mulVecLin) := rfl
    have h5 : (X a).rank = Module.finrank F (LinearMap.range (X a).mulVecLin) := rfl
    omega
  · have e' : P b * (Q a)ᵀ = X a * (-(Y b)ᵀ) := by
      rw [Matrix.mul_neg]
      exact eq_neg_of_add_eq_zero_right (ho a b hab)
    have hle : LinearMap.range (P b * (Q a)ᵀ).mulVecLin ≤
        LinearMap.range (P b).mulVecLin ⊓ LinearMap.range (X a).mulVecLin :=
      le_inf (hcol _ _) (by rw [e']; exact hcol _ _)
    have h1 := Submodule.finrank_mono hle
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (P b).mulVecLin)
      (LinearMap.range (X a).mulVecLin)
    have h3 := sylvester_rank (P b) (Q a)ᵀ
    simp only [Fintype.card_fin, Matrix.rank_transpose] at h3
    have h4 : (P b * (Q a)ᵀ).rank = Module.finrank F (LinearMap.range (P b * (Q a)ᵀ).mulVecLin) := rfl
    have h5 : (P b).rank = Module.finrank F (LinearMap.range (P b).mulVecLin) := rfl
    omega

/-- The rank three-cycles. For distinct slices a, b, c:
N + rank Q_c + rank Y_b + rank Q_a ≤ rank X_a + r + 2 k, N + rank Y_c + rank Q_b + rank Y_a ≤ rank P_a + 2 r + k,
and N ≤ rank X_a + rank P_a. -/
theorem slice_rank_cycle {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (a b c : Fin N) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    N + (Q c).rank + (Y b).rank + (Q a).rank ≤ (X a).rank + r + 2 * k ∧
    N + (Y c).rank + (Q b).rank + (Y a).rank ≤ (P a).rank + 2 * r + k ∧
    N ≤ (X a).rank + (P a).rank := by
  have hR3 : ∀ z, LinearMap.range (X z).mulVecLin ⊔ LinearMap.range (P z).mulVecLin = ⊤ := by
    intro z
    rw [eq_top_iff]
    intro x _
    have hx : x = (X z) *ᵥ ((Y z)ᵀ *ᵥ x) + (P z) *ᵥ ((Q z)ᵀ *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, hd z, Matrix.one_mulVec]
    rw [hx]
    exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
  have htop : ∀ z, Module.finrank F ↥(LinearMap.range (X z).mulVecLin ⊔ LinearMap.range (P z).mulVecLin) = N := by
    intro z
    rw [hR3 z, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have htop' : ∀ z, Module.finrank F ↥(LinearMap.range (P z).mulVecLin ⊔ LinearMap.range (X z).mulVecLin) = N := by
    intro z
    rw [sup_comm]
    exact htop z
  have hX : ∀ z, (X z).rank = Module.finrank F (LinearMap.range (X z).mulVecLin) := fun z => rfl
  have hP : ∀ z, (P z).rank = Module.finrank F (LinearMap.range (P z).mulVecLin) := fun z => rfl
  refine ⟨?_, ?_, ?_⟩
  · have E1 := (slice_excess_rank X Y P Q ho c a (Ne.symm hac)).2
    have E2 := (slice_excess_rank X Y P Q ho c b (Ne.symm hbc)).1
    have E3 := (slice_excess_rank X Y P Q ho a b hab).2
    have T1 := finrank_sup_triangle (LinearMap.range (P a).mulVecLin) (LinearMap.range (X c).mulVecLin)
      (LinearMap.range (X a).mulVecLin)
    have T2 := finrank_sup_triangle (LinearMap.range (X c).mulVecLin) (LinearMap.range (P b).mulVecLin)
      (LinearMap.range (X a).mulVecLin)
    have h1 := htop' a
    have h2 := hX a
    omega
  · have E1 := (slice_excess_rank X Y P Q ho a c hac).1
    have E2 := (slice_excess_rank X Y P Q ho b c hbc).2
    have E3 := (slice_excess_rank X Y P Q ho b a (Ne.symm hab)).1
    have T1 := finrank_sup_triangle (LinearMap.range (X a).mulVecLin) (LinearMap.range (P c).mulVecLin)
      (LinearMap.range (P a).mulVecLin)
    have T2 := finrank_sup_triangle (LinearMap.range (P c).mulVecLin) (LinearMap.range (X b).mulVecLin)
      (LinearMap.range (P a).mulVecLin)
    have h1 := htop a
    have h2 := hP a
    omega
  · have h1 := htop a
    have h2 := Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range (X a).mulVecLin)
      (LinearMap.range (P a).mulVecLin)
    rw [hX a, hP a]
    omega

/-- The slice identities force 4 N ≤ 3 (r + k) for N ≥ 3: the rank three-cycles on slices 0, 1, 2 in three
rotations, for the system and for its transpose Y_u X_yᵀ + Q_y P_uᵀ = [y = u] 1. -/
theorem slice_four_thirds {F : Type*} [Field F] {N r k : ℕ} (hN : 3 ≤ N)
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) : 4 * N ≤ 3 * (r + k) := by
  have hd' : ∀ y, Y y * (X y)ᵀ + Q y * (P y)ᵀ = 1 := fun y => by
    have := congrArg Matrix.transpose (hd y)
    simpa [Matrix.transpose_add, Matrix.transpose_mul] using this
  have ho' : ∀ y u, y ≠ u → Y y * (X u)ᵀ + Q u * (P y)ᵀ = 0 := fun y u hyu => by
    have := congrArg Matrix.transpose (ho u y (Ne.symm hyu))
    simpa [Matrix.transpose_add, Matrix.transpose_mul, add_comm] using this
  set s0 : Fin N := ⟨0, by omega⟩
  set s1 : Fin N := ⟨1, by omega⟩
  set s2 : Fin N := ⟨2, by omega⟩
  have h01 : s0 ≠ s1 := by simp [s0, s1, Fin.ext_iff]
  have h02 : s0 ≠ s2 := by simp [s0, s2, Fin.ext_iff]
  have h12 : s1 ≠ s2 := by simp [s1, s2, Fin.ext_iff]
  have a1 := slice_rank_cycle X Y P Q hd ho s0 s1 s2 h01 h02 h12
  have a2 := slice_rank_cycle X Y P Q hd ho s1 s2 s0 h12 (Ne.symm h01) (Ne.symm h02)
  have a3 := slice_rank_cycle X Y P Q hd ho s2 s0 s1 (Ne.symm h02) (Ne.symm h12) h01
  have b1 := slice_rank_cycle Y X Q P hd' ho' s0 s1 s2 h01 h02 h12
  have b2 := slice_rank_cycle Y X Q P hd' ho' s1 s2 s0 h12 (Ne.symm h01) (Ne.symm h02)
  have b3 := slice_rank_cycle Y X Q P hd' ho' s2 s0 s1 (Ne.symm h02) (Ne.symm h12) h01
  omega

/-- For N ≥ 3, every split S_N = B + C over a field has 4 N ≤ 3 (rank B + rank (R C)). -/
theorem swap_split_ge_four_thirds {F : Type*} [Field F] (N : ℕ) (hN : 3 ≤ N)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F)
    (h : swapMat F N = B + C) : 4 * N ≤ 3 * (B.rank + (realign C).rank) := by
  obtain ⟨X, Y, P, Q, hd, ho⟩ := exists_slices N B C h
  exact slice_four_thirds hN X Y P Q hd ho


end SwapSplit



/-! The registered target contains the full crossing tensor, with independently chosen local indices. -/

namespace OMA.FourSiteRanks
open OMAPort OMA.PlanarInterval OMA.FourSiteComparison
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical

def pairCondition {Q : Type} (z : Fin 4 → Q) : Prop := z 0 = z 1 ∧ z 2 = z 3

def FullGrid (X : FourTensor) (N : ℕ) : Prop :=
  ∃ f : ∀ i, Fin N → (coordRaw X).Leg i, ∀ z : Fin 4 → Fin N,
    X.2 (fun i => f i (z i)) = if pairCondition z then 1 else 0

theorem grid_unit : FullGrid unit 1 := by
  refine ⟨fun _ _ => (0 : Fin 1),fun z => ?_⟩
  have h : pairCondition z := ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  simp [unit,h]

theorem FullGrid.mul {X Y : FourTensor} {a b : ℕ} (hX : FullGrid X a) (hY : FullGrid Y b) :
    FullGrid (sigMul X Y) (a*b) := by
  obtain ⟨f,hf⟩ := hX
  obtain ⟨g,hg⟩ := hY
  let decode : Fin (a*b) ≃ Fin a × Fin b := finProdFinEquiv.symm
  refine ⟨fun i t => finProdFinEquiv (f i (decode t).1, g i (decode t).2),fun z => ?_⟩
  let u := fun i => (decode (z i)).1
  let v := fun i => (decode (z i)).2
  have pair (i j : Fin 4) : z i = z j ↔ u i = u j ∧ v i = v j := by
    rw [← decode.injective.eq_iff, Prod.ext_iff]
  have eq : pairCondition z ↔ pairCondition u ∧ pairCondition v := by
    simp only [pairCondition,pair]
    tauto
  change X.2 _ * Y.2 _ = _
  simp only [Equiv.symm_apply_apply]
  rw [hf u, hg v]
  by_cases hu : pairCondition u <;> by_cases hv : pairCondition v <;> simp [eq, hu,hv]

theorem FullGrid.power {X : FourTensor} {q : ℕ} (h : FullGrid X q) (n : ℕ) :
    FullGrid (power X n) (q^n) := by
  induction n with
  | zero =>
    change FullGrid unit (q^0)
    simpa using grid_unit
  | succ n ih =>
    change FullGrid (sigMul (FourSiteComparison.power X n) X) (q^(n+1))
    simpa only [pow_succ] using ih.mul h

def wireSymbol (a b i : Fin 4) (x : Fin 2) : (coordRaw (wireCoord a b)).Leg i :=
  if h : i = a ∨ i = b then ⟨x.val, by simpa [wireCoord,h] using x.isLt⟩
  else ⟨0,by simp [wireCoord,h]⟩

theorem wireSymbol_at (a b i : Fin 4) (h : i = a ∨ i = b) (v : Fin 2) :
    (wireSymbol a b i v).val = v.val := by simp only [wireSymbol, dif_pos h]

theorem matching_grid : FullGrid (matching 0 1 2 3) 2 := by
  refine ⟨fun i x => finProdFinEquiv (wireSymbol 0 1 i x,wireSymbol 2 3 i x),fun z => ?_⟩
  simp only [matching,sigMul,Equiv.symm_apply_apply]
  change (if (wireSymbol 0 1 0 (z 0)).val = (wireSymbol 0 1 1 (z 1)).val then (1:ℂ) else 0) *
    (if (wireSymbol 2 3 2 (z 2)).val = (wireSymbol 2 3 3 (z 3)).val then 1 else 0) = _
  rw [wireSymbol_at 0 1 0 (Or.inl rfl),wireSymbol_at 0 1 1 (Or.inr rfl),
    wireSymbol_at 2 3 2 (Or.inl rfl),wireSymbol_at 2 3 3 (Or.inr rfl)]
  simp only [← Fin.ext_iff,pairCondition]
  by_cases h : z 0 = z 1 <;> by_cases g : z 2 = z 3 <;> simp [h,g]

def reindexFour {N : ℕ} (p q : Fin N × Fin N) : Fin 4 → Fin N :=
  ![p.1,q.2,p.2,q.1]

def gridMatrix {N : ℕ} {L : Fin 4 → Type} (f : ∀ i, Fin N → L i)
    (Z : (∀ i, L i) → ℂ) : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ :=
  fun p q => Z (fun i => f i (reindexFour p q i))

theorem grid_matrix_swap {N : ℕ} {X : FourTensor} (f : ∀ i, Fin N → (coordRaw X).Leg i)
    (h : ∀ z : Fin 4 → Fin N, X.2 (fun i => f i (z i)) = if pairCondition z then 1 else 0) :
    gridMatrix f X.2 = SwapSplit.swapMat ℂ N := by
  ext p q
  change X.2 _ = _
  rw [h (reindexFour p q)]
  simp [pairCondition,reindexFour,SwapSplit.swapMat,and_comm,eq_comm]

/-- Left and right flattenings of the four-index sample are submatrices of the two
corresponding flattenings of the starting tensor. -/
theorem grid_left_le {N : ℕ} (q : Fin N) (R : Raw.{0} (Fin 4) ℂ)
    (f : ∀ i, Fin N → R.Leg i) :
    (gridMatrix f R.coeff).rank ≤ cutRank leftCut ℂ (ofRaw R) := by
  let x (p r : Fin N × Fin N) (i : Fin 4) := f i (reindexFour p r i)
  apply sample_rank_le R (q,q) leftCut x
  constructor <;> intro a b c i hi <;> fin_cases i <;>
    simp_all [leftCut,x,reindexFour]

theorem grid_right_le {N : ℕ} (q : Fin N) (R : Raw.{0} (Fin 4) ℂ)
    (f : ∀ i, Fin N → R.Leg i) :
    (SwapSplit.realign (gridMatrix f R.coeff)).rank ≤ cutRank rightCut ℂ (ofRaw R) := by
  let x (p r : Fin N × Fin N) (i : Fin 4) := f i (reindexFour (r.1,p.1) (r.2,p.2) i)
  have e : Matrix.transpose (SwapSplit.realign (gridMatrix f R.coeff)) = sample x R.coeff := rfl
  rw [← Matrix.rank_transpose (SwapSplit.realign (gridMatrix f R.coeff)), e]
  apply sample_rank_le R (q,q) rightCut x
  constructor <;> intro a b c i hi <;> fin_cases i <;>
    simp_all [rightCut,x,reindexFour]

end OMA.FourSiteRanks


/-! Transfer a restriction of two matchings to a split of the swap matrix. -/

namespace OMA.FourSiteRanks
open OMAPort OMA.PlanarInterval OMA.FourSiteComparison
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical NNReal

local instance : Nonempty {i // leftCut i} := ⟨⟨2, by decide⟩⟩
local instance : Nonempty {i // ¬ leftCut i} := ⟨⟨3, by decide⟩⟩
local instance : Nonempty {i // rightCut i} := ⟨⟨2, by decide⟩⟩
local instance : Nonempty {i // ¬ rightCut i} := ⟨⟨3, by decide⟩⟩

theorem cut_add (s : Fin 4 → Prop) [DecidablePred s]
    [Nonempty {i // s i}] [Nonempty {i // ¬s i}] (X Y : FourClass) :
    cutRank s ℂ (X+Y) = cutRank s ℂ X + cutRank s ℂ Y := by
  have e := map_add (normalizedSpectrum.toRingHom (cutSpectrum.{0} s ℂ)) X Y
  change (cutRank s ℂ (X+Y) : ℝ≥0) = (cutRank s ℂ X : ℝ≥0)+(cutRank s ℂ Y : ℝ≥0) at e
  exact_mod_cast e

theorem cut_zero (s : Fin 4 → Prop) [DecidablePred s]
    [Nonempty {i // s i}] [Nonempty {i // ¬s i}] : cutRank s ℂ (0 : FourClass) = 0 := by
  have e := map_zero (normalizedSpectrum.toRingHom (cutSpectrum.{0} s ℂ))
  change (cutRank s ℂ 0 : ℝ≥0) = 0 at e
  exact_mod_cast e

def SplitBudget (X : FourClass) (b : ℕ) : Prop :=
  ∃ A B : FourClass, X = A+B ∧ cutRank leftCut ℂ A + cutRank rightCut ℂ B ≤ b

theorem SplitBudget.zero : SplitBudget 0 0 :=
  ⟨0,0,by simp,by simp [cut_zero]⟩

theorem SplitBudget.add {X Y : FourClass} {a b : ℕ} (hx : SplitBudget X a) (hy : SplitBudget Y b) :
    SplitBudget (X+Y) (a+b) := by
  obtain ⟨L,R,rfl,h⟩ := hx
  obtain ⟨L',R',rfl,h'⟩ := hy
  refine ⟨L+L',R+R',by ac_rfl,?_⟩
  rw [cut_add,cut_add]
  omega

theorem SplitBudget.copies {X : FourClass} {b : ℕ} (h : SplitBudget X b) (C : ℕ) :
    SplitBudget (C • X) (C*b) := by
  induction C with
  | zero => simpa using SplitBudget.zero
  | succ n ih => simpa only [succ_nsmul,Nat.succ_mul] using ih.add h

theorem SplitBudget.sum {J : Type} (s : Finset J) (T : J → FourClass) (b : J → ℕ)
    (h : ∀ j ∈ s, SplitBudget (T j) (b j)) : SplitBudget (∑ j ∈ s, T j) (∑ j ∈ s, b j) := by
  induction s using Finset.induction_on with
  | empty => simpa using SplitBudget.zero
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self ..)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem mixed_split (k i j : ℕ) :
    SplitBudget ((V^k)^i * (W^k)^j) (min ((4^k)^j) ((4^k)^i)) := by
  by_cases h : ((4:ℕ)^k)^j ≤ (4^k)^i
  · refine ⟨_,0,(add_zero _).symm,?_⟩
    rw [cut_zero,add_zero,min_eq_left h]
    simp only [cut_mul,cut_pow]
    simpa only [one_pow,one_mul] using Nat.mul_le_mul
      (Nat.pow_le_pow_left (Nat.pow_le_pow_left left_V k) i)
      (Nat.pow_le_pow_left (Nat.pow_le_pow_left left_W k) j)
  · refine ⟨0,_,(zero_add _).symm,?_⟩
    rw [cut_zero,zero_add,min_eq_right (le_of_not_ge h)]
    simp only [cut_mul,cut_pow]
    simpa only [one_pow,mul_one] using Nat.mul_le_mul
      (Nat.pow_le_pow_left (Nat.pow_le_pow_left right_V k) i)
      (Nat.pow_le_pow_left (Nat.pow_le_pow_left right_W k) j)

theorem source_split (k n : ℕ) : SplitBudget ((V^k + W^k)^n) (sliceBudget k n) := by
  rw [add_pow]
  unfold sliceBudget
  apply SplitBudget.sum
  intro i _
  simpa only [nsmul_eq_mul, mul_comm (n.choose i : FourClass)] using
    (mixed_split k i (n-i)).copies (n.choose i)

theorem test_class_le {k C n : ℕ} (h : Test k C n) :
    cls (power (power (matching 0 1 2 3) k) n) ≤ C • ((V^k+W^k)^n) := by
  let B := sigAdd (power (matching 0 2 1 3) k) (power (matching 0 3 1 2) k)
  have base : cls B = V^k + W^k := by
    change ofRaw (coordRaw (sigAdd _ _)) = _
    rw [coord_add,ofRaw_add]
    exact congrArg₂ (· + ·) (cls_pow _ _) (cls_pow _ _)
  rw [← base, ← cls_pow B n, ← cls_copies (power B n) C]
  obtain ⟨M,e⟩ := h
  refine ⟨M,fun y => (e y).trans (Finset.sum_congr ?_ fun _ _ => mul_comm _ _)⟩
  exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)

theorem swap_split_of_test {k C n : ℕ} (h : Test k C n) :
    let N := (2^k)^n
    ∃ A B : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ,
      SwapSplit.swapMat ℂ N = A+B ∧ A.rank + (SwapSplit.realign B).rank ≤ C * sliceBudget k n := by
  let N : ℕ := (2^k)^n
  let X := power (power (matching 0 1 2 3) k) n
  let R := coordRaw X
  obtain ⟨f,hf⟩ := (matching_grid.power k).power n
  have iden : gridMatrix f R.coeff = SwapSplit.swapMat ℂ N := grid_matrix_swap f hf
  obtain ⟨L,H,eq,cap⟩ := (source_split k n).copies C
  have hsum : ofRaw R ≤ ∑ j : Fin 2, (![L,H] : Fin 2 → FourClass) j := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      using (test_class_le h).trans_eq eq
  obtain ⟨z,split,bounds⟩ := images_of_le_sum R (![L,H] : Fin 2 → FourClass) hsum
  let p : Fin N := ⟨0,by dsimp [N]; positivity⟩
  refine ⟨gridMatrix f (z 0),gridMatrix f (z 1),?_,?_⟩
  · rw [← iden,split,Fin.sum_univ_two]
    rfl
  · exact (Nat.add_le_add
      ((grid_left_le p {R with coeff := z 0} f).trans (monotone_cutRank leftCut ℂ (bounds 0)))
      ((grid_right_le p {R with coeff := z 1} f).trans (monotone_cutRank rightCut ℂ (bounds 1)))).trans cap

theorem crossing_necessary {k C n : ℕ} (hN : 3 ≤ (2^k)^n) (h : Test k C n) :
    4 * (2^k)^n ≤ 3 * (C * sliceBudget k n) := by
  obtain ⟨A,B,e,bound⟩ := swap_split_of_test h
  exact (SwapSplit.swap_split_ge_four_thirds _ hN A B e).trans (Nat.mul_le_mul_left _ bound)

theorem fourth_power_ten_copies : ¬ Test 4 10 1 := by
  intro h
  have bad := crossing_necessary (k:=4) (C:=10) (n:=1) (by decide) h
  exact (by decide : ¬ (4 * (2^4)^1 ≤ 3 * (10 * sliceBudget 4 1))) bad

theorem fourth_power_three_copies_three_factors : ¬ Test 4 3 3 := by
  intro h
  have bad := crossing_necessary (k:=4) (C:=3) (n:=3) (by decide) h
  exact (by decide : ¬ (4 * (2^4)^3 ≤ 3 * (3 * sliceBudget 4 3))) bad

end OMA.FourSiteRanks



/-! A polynomial crossing-rank lower bound suffices for the registered spectral witness. -/

namespace OMA.FourSiteRanks
open OMA.FourSiteComparison
open scoped Classical

theorem budget_le (k n : ℕ) : sliceBudget k n ≤ 2^n * (2^k)^n := by
  have powers (i : ℕ) : ((4:ℕ)^k)^i = (2^k)^(2*i) := by
    rw [pow_mul, ← pow_mul _ k 2, Nat.mul_comm k 2, pow_mul]
    norm_num
  have term (i : ℕ) (hi : i ≤ n) : min (((4:ℕ)^k)^(n-i)) ((4^k)^i) ≤ (2^k)^n := by
    by_cases h : i ≤ n-i
    · exact (min_le_right ..).trans ((powers i).le.trans (Nat.pow_le_pow_right (by positivity) (by omega)))
    · exact (min_le_left ..).trans ((powers (n-i)).le.trans (Nat.pow_le_pow_right (by positivity) (by omega)))
  unfold sliceBudget
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), n.choose i * (2^k)^n :=
      Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _ (term i (by simpa using Finset.mem_range.mp hi))
    _ = 2^n * (2^k)^n := by rw [← Finset.sum_mul, Nat.sum_range_choose]

/-- An integer-power formulation of a superlinear lower bound in Naslund's crossing problem. -/
def PolynomialCrossingLower : Prop :=
  ∃ d : ℕ, 0 < d ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A B : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ,
      SwapSplit.swapMat ℂ N = A+B → N^(d+1) ≤ (A.rank+(SwapSplit.realign B).rank)^d

set_option maxHeartbeats 1800000 in
theorem crossing_obstruction (hard : PolynomialCrossingLower) :
    OMA.R_Erdos20_erdos_20_R1_H2_R1_H1_R1_H1_R2.H1 := by
  obtain ⟨d,hd,N₀,lower⟩ := hard
  let k := d+1
  refine ⟨k,by dsimp [k]; omega,?_⟩
  intro C hC
  let n := max N₀ (C^d)+1
  refine ⟨n,by dsimp [n]; omega,?_⟩
  change ¬ Test k C n
  intro h
  let N : ℕ := (2^k)^n
  have hq : 2 ≤ (2:ℕ)^k := by
    calc
      2 = 2^1 := by decide
      _ ≤ 2^k := Nat.pow_le_pow_right (by decide) (by dsimp [k]; omega)
  have hn : n < (2:ℕ)^n := Nat.lt_two_pow_self
  have enough : N₀ ≤ N := (show N₀ ≤ n by dsimp [n]; omega).trans
    (hn.le.trans (Nat.pow_le_pow_left hq n))
  obtain ⟨A,B,eq,bound⟩ := swap_split_of_test h
  have cost : A.rank+(SwapSplit.realign B).rank ≤ C * (2^n*N) :=
    bound.trans (Nat.mul_le_mul_left _ (budget_le k n))
  have key : N^d * N ≤ N^d * ((2^n)^d * C^d) := calc
    _ = N^(d+1) := (pow_succ _ _).symm
    _ ≤ _ := lower N enough A B eq
    _ ≤ (C * (2^n*N))^d := Nat.pow_le_pow_left cost d
    _ = _ := by simp only [mul_pow]; ac_rfl
  have hN : 0 < N := by dsimp [N]; positivity
  have short : N ≤ (2^n)^d * C^d := Nat.le_of_mul_le_mul_left key (pow_pos hN d)
  have ex : N = (2^n)^d * 2^n := by
    change (2^(d+1))^n = _
    calc
      _ = (2^n)^(d+1) := by rw [← pow_mul, ← pow_mul, Nat.mul_comm (d+1) n]
      _ = _ := pow_succ _ _
  rw [ex] at short
  have impossible : 2^n ≤ C^d := Nat.le_of_mul_le_mul_left short (by positivity)
  have hn' : C^d < n := by dsimp [n]; omega
  omega

theorem four_point_witness_of_crossing_lower (hard : PolynomialCrossingLower) :
    OMA.R_Erdos20_erdos_20_R1_H2_R1_H1_R1.H1 :=
  OMA.R_Erdos20_erdos_20_R1_H2_R1_H1_R1_H1_R2.main (crossing_obstruction hard) OMA.FourSiteRanksComparison

/-- A constant-factor crossing lower bound alone is consistent with the numeric budget at every power. -/
theorem linear_bound_compatible (a k n : ℕ) :
    a * (2^k)^n ≤ (a * 2^k) * sliceBudget k n := by
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left a (central_term_bound k n)

end OMA.FourSiteRanks



namespace OMA.FourSiteRanks

/-- For the fourth power the ratio between the target size and the binomial
budget is at most eight. Equality holds at one factor. -/
theorem fourth_power_le_eight_budgets (n : ℕ) : (16:ℕ)^n ≤ 8 * sliceBudget 4 n := by
  by_cases near : n < 2
  · interval_cases n <;> decide
  have hn : 2 ≤ n := by omega
  let i := n/2
  have hi : i ≤ n-i := by dsimp [i]; omega
  have ci : 2 ≤ n.choose i := hn.trans (by simpa [i] using Nat.choose_le_middle 1 n)
  have term : n.choose i * min (((4:ℕ)^4)^(n-i)) ((4^4)^i) ≤ sliceBudget 4 n :=
    Finset.single_le_sum (f := fun j => n.choose j * min (((4:ℕ)^4)^(n-j)) ((4^4)^j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by dsimp [i]; omega : i < n+1))
  rw [min_eq_right (Nat.pow_le_pow_right (by decide : 0 < (4:ℕ)^4) hi)] at term
  have twoTerms : 2*(256:ℕ)^i ≤ sliceBudget 4 n :=
    (Nat.mul_le_mul_right _ ci).trans term
  have size : (16:ℕ)^n ≤ 16 * 256^i := calc
    _ ≤ 16^(1+2*i) := Nat.pow_le_pow_right (by decide) (by dsimp [i]; omega)
    _ = _ := by rw [pow_add, pow_one, pow_mul]; norm_num
  omega

/-- At k = 4 the numerical consequence of the crossing lower bound holds at
all positive powers exactly when there are at least eleven copies. -/
theorem crossing_inequality_all_powers_iff (C : ℕ) :
    (∀ n : ℕ, 0 < n → 4 * (2^4)^n ≤ 3 * (C * sliceBudget 4 n)) ↔ 11 ≤ C := by
  constructor
  · intro h
    have b := h 1 (by decide)
    rw [show sliceBudget 4 1 = 2 by decide] at b
    norm_num at b
    omega
  · intro eleven n _
    have bound := fourth_power_le_eight_budgets n
    have mono := Nat.mul_le_mul_right (sliceBudget 4 n) eleven
    change 4 * 16^n ≤ 3 * (C * sliceBudget 4 n)
    omega

/-- Any uniform restriction furnished by the comparison at the fourth power
needs at least eleven copies. -/
theorem fourth_copy_floor (k : ℕ)
    (existsC : ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 0 < n → Test k C n) :
    ∃ C : ℕ, 0 < C ∧ (k = 4 → 11 ≤ C) ∧ ∀ n : ℕ, 0 < n → Test k C n := by
  obtain ⟨C,pos,works⟩ := existsC
  refine ⟨C,pos,?_,works⟩
  rintro rfl
  apply (crossing_inequality_all_powers_iff C).mp
  intro n hn
  have enough : 3 ≤ (2^4)^n := calc
    3 ≤ (2^4)^1 := by decide
    _ ≤ (2^4)^n := Nat.pow_le_pow_right (by decide) hn
  exact crossing_necessary enough (works n hn)

end OMA.FourSiteRanks


/- Apache-2.0 license for the adapted OpenAI and crossing-lower-bounds material.
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/

namespace OMA.FourSiteRanks
theorem comparison_copy_floor (k : ℕ)
    (existsC : ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 0 < n → Test k C n) :
    ∃ C : ℕ, 0 < C ∧ 2^k ≤ 2*C ∧ ∀ n : ℕ, 0 < n → Test k C n := by
  obtain ⟨C,positive,works⟩ := existsC
  refine ⟨C,positive,?_,works⟩
  by_contra missing
  exact (one_copy_power_obstruction (k := k) (C := C) (Nat.lt_of_not_ge missing)) (works 1 (by decide))
end OMA.FourSiteRanks


/- Product-vector restrictions in Naslund's crossing problem.
The linear bound is Theorem 1(a) of Evan Green, doi:10.5281/zenodo.24522729.
The proof below uses a cycle of four evaluations of the product-vector identities. -/

namespace OMA.ProductVectors

open Matrix
open scoped BigOperators Matrix Classical

abbrev Vec (N : ℕ) := Fin N → ℂ
abbrev Family (N r : ℕ) := Fin r → Matrix (Fin N) (Fin N) ℂ

def out {N r : ℕ} (A : Family N r) (x : Vec N) : Matrix (Fin N) (Fin r) ℂ :=
  fun i a => (x ᵥ* A a) i

def inc {N r : ℕ} (A : Family N r) (x : Vec N) : Matrix (Fin N) (Fin r) ℂ :=
  fun i a => (A a *ᵥ x) i

def delta {N : ℕ} (i j : Fin N) : ℂ := if i=j then 1 else 0

def Cycle {N r s : ℕ} (A C : Family N r) (B D : Family N s) : Prop :=
  ∀ i j k l, delta i k * delta j l =
    (∑ a, A a i j * C a k l) + ∑ b, B b j k * D b l i

theorem Cycle.rotate {N r s} {A C : Family N r} {B D : Family N s}
    (h : Cycle A C B D) : Cycle D B A C := by
  intro l i j k
  calc
    delta l j * delta i k = delta i k * delta j l := by
      rw [mul_comm,show delta l j = delta j l by simp [delta,eq_comm]]
    _ = _ := h i j k l
    _ = _ := by rw [add_comm]; congr 1; apply Finset.sum_congr rfl; intro b _; apply mul_comm

theorem Cycle.slice {N r s} {A C : Family N r} {B D : Family N s}
    (h : Cycle A C B D) (w : Vec N) (i j k : Fin N) :
    delta i k * w j =
      (∑ a, A a i j * inc C w k a) + ∑ b, B b j k * out D w i b := by
  calc
    _ = ∑ l, (delta i k * delta j l) * w l := by
      simp [delta,ite_mul]
    _ = ∑ l, ((∑ a, A a i j * C a k l) + ∑ b, B b j k * D b l i) * w l :=
      Finset.sum_congr rfl fun l _ => congrArg (· * w l) (h i j k l)
    _ = _ := by
      simp only [add_mul,Finset.sum_add_distrib,Finset.sum_mul]
      congr 1
      · rw [Finset.sum_comm]
        simp [inc,Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc]
      · rw [Finset.sum_comm]
        simp only [out,Matrix.vecMul,dotProduct,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro l _
        ring

theorem Cycle.cover {N r s} {A C : Family N r} {B D : Family N s}
    (h : Cycle A C B D) (w : Vec N) (hw : w ≠ 0) :
    N ≤ (inc C w).rank + (out D w).rank := by
  obtain ⟨j,hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra! a
    exact hw (funext a)
  let U : Matrix (Fin r) (Fin N) ℂ := fun a i => A a i j
  let V : Matrix (Fin N) (Fin s) ℂ := fun k b => B b j k
  have eq : w j • (1 : Matrix (Fin N) (Fin N) ℂ) = (inc C w)*U + V*(out D w)ᵀ := by
    ext k i
    simp only [Matrix.add_apply,Matrix.mul_apply,Matrix.transpose_apply]
    simpa [U,V,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,delta,mul_comm,eq_comm] using h.slice w i j k
  have m := SwapSplit.rank_add_le' ((inc C w)*U) (V*(out D w)ᵀ)
  rw [← eq,Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hj),
    Matrix.rank_one,Fintype.card_fin] at m
  exact m.trans (Nat.add_le_add (Matrix.rank_mul_le_left _ _)
    ((Matrix.rank_mul_le_right _ _).trans_eq (Matrix.rank_transpose _)))

theorem Cycle.product {N r s} {A C : Family N r} {B D : Family N s}
    (h : Cycle A C B D) (x w : Vec N) (kill : (out D w)ᵀ *ᵥ x = 0) :
    (out A x) * (inc C w)ᵀ = Matrix.vecMulVec w x := by
  ext j k
  have g : ∑ i, x i * (delta i k * w j) = w j * x k := by
    simp [delta,mul_ite,mul_comm]
  rw [← Matrix.vecMulVec_apply] at g
  rw [← g]
  simp_rw [h.slice w, mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  have zeroPart : (∑ i, ∑ b, x i * (B b j k * out D w i b)) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro b _
    have e := congrFun kill b
    change ∑ i, out D w i b * x i = 0 at e
    calc
      _ = B b j k * ∑ i, out D w i b * x i := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
      _ = 0 := by rw [e,mul_zero]
  rw [zeroPart,add_zero,Finset.sum_comm]
  simp [Matrix.mul_apply, out, Matrix.vecMul, dotProduct, Finset.sum_mul, mul_assoc]

theorem interchange {N r} (A : Family N r) (w x : Vec N) :
    (out A w)ᵀ *ᵥ x = (inc A x)ᵀ *ᵥ w := by
  funext a
  change (w ᵥ* A a) ⬝ᵥ x = (A a *ᵥ x) ⬝ᵥ w
  rw [← Matrix.dotProduct_mulVec,dotProduct_comm]

theorem kernel_vector {N r : ℕ} (M : Matrix (Fin N) (Fin r) ℂ) (small : M.rank < N) :
    ∃ w : Vec N, w ≠ 0 ∧ Mᵀ *ᵥ w = 0 := by
  let L := Mᵀ.mulVecLin
  have e := LinearMap.finrank_range_add_finrank_ker L
  have re : Module.finrank ℂ (LinearMap.range L) = M.rank := M.rank_transpose
  rw [re,Module.finrank_fintype_fun_eq_card,Fintype.card_fin] at e
  have h : LinearMap.ker L ≠ ⊥ := by
    intro eq
    rw [eq,finrank_bot,add_zero] at e
    omega
  obtain ⟨w,hw,wn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  exact ⟨w,wn,hw⟩

noncomputable def peak {N r} (A : Family N r) : ℕ :=
  Nat.findGreatest (fun k => ∃ x, (out A x).rank = k) r

theorem peak_attained {N r} (A : Family N r) : ∃ x, (out A x).rank = peak A :=
  Nat.findGreatest_spec (P := fun k => ∃ x, (out A x).rank = k) (Matrix.rank_le_width (out A 0)) ⟨0,rfl⟩

theorem le_peak {N r} (A : Family N r) (x : Vec N) : (out A x).rank ≤ peak A :=
  Nat.le_findGreatest (Matrix.rank_le_width _) ⟨x,rfl⟩

theorem peak_le {N r} (A : Family N r) : peak A ≤ r := Nat.findGreatest_le _

theorem Cycle.step {N r s} {A C : Family N r} {B D : Family N s}
    (h : Cycle A C B D) (small : ∀ x, (inc D x).rank < N) :
    peak A + N ≤ r + 1 + peak D := by
  obtain ⟨x,ax⟩ := peak_attained A
  obtain ⟨w,hw,kill⟩ := kernel_vector (inc D x) (small x)
  rw [← interchange] at kill
  have e := h.product x w kill
  have rankone : (Matrix.vecMulVec w x).rank ≤ 1 := by
    rw [Matrix.vecMulVec_eq (Fin 1)]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
  have sy := SwapSplit.sylvester_rank (out A x) (inc C w)ᵀ
  rw [Matrix.rank_transpose,e,Fintype.card_fin,ax] at sy
  have c := h.cover w hw
  have upper := le_peak D w
  omega

theorem Cycle.small_widths {N r s} {A C : Family N r} {B D : Family N s}
    (h : Cycle A C B D) (hr : r < N) (hs : s < N) :
    2*N ≤ r+s+2 := by
  have sr (T : Family N r) (x : Vec N) := lt_of_le_of_lt (Matrix.rank_le_width (inc T x)) hr
  have ss (T : Family N s) (x : Vec N) := lt_of_le_of_lt (Matrix.rank_le_width (inc T x)) hs
  have a := h.step (ss D)
  have b := h.rotate.step (sr C)
  have c := h.rotate.rotate.step (ss B)
  have d := h.rotate.rotate.rotate.step (sr A)
  omega

def flipFamily {N r : ℕ} (A : Family N r) : Family N r := fun a => (A a)ᵀ

theorem out_flip {N r} (A : Family N r) (x : Vec N) : out (flipFamily A) x = inc A x := by
  ext j a
  simp [out,inc,flipFamily,Matrix.vecMul_transpose]

theorem Cycle.flip {N r s} {A C : Family N r} {B D : Family N s}
    (h : Cycle A C B D) : Cycle (flipFamily A) (flipFamily C) (flipFamily D) (flipFamily B) := by
  intro j i l k
  simp only [flipFamily,Matrix.transpose_apply]
  rw [mul_comm (delta j l) (delta i k),h i j k l]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  exact mul_comm _ _

theorem Cycle.bound_of_small {N r s} {A C : Family N r} {B D : Family N s}
    (h : Cycle A C B D) (hs : s < N) : 2*N ≤ r+s+2 := by
  by_contra! bad
  have ss (T : Family N s) (x : Vec N) := lt_of_le_of_lt (Matrix.rank_le_width (inc T x)) hs
  have sr {U V : Family N r} {Y Z : Family N s} (g : Cycle U V Y Z) (x : Vec N) :
      (inc U x).rank < N := by
    have e := g.flip.step (ss (flipFamily Y))
    have f := peak_le (flipFamily Y)
    have t := le_peak (flipFamily U) x
    rw [out_flip] at t
    omega
  have a := h.step (ss D)
  have b := h.rotate.step (sr h.rotate.rotate)
  have c := h.rotate.rotate.step (ss B)
  have d := h.rotate.rotate.rotate.step (sr h)
  omega

theorem Cycle.bound {N r s} {A C : Family N r} {B D : Family N s}
    (h : Cycle A C B D) : 2*N ≤ r+s+2 := by
  by_cases hs : s < N
  · exact h.bound_of_small hs
  by_cases hr : r < N
  · simpa only [Nat.add_comm s r] using h.rotate.bound_of_small hr
  omega

theorem cycle_of_swap {N : ℕ} (M H : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ)
    (e : SwapSplit.swapMat ℂ N = M+H) :
    ∃ (A C : Family N M.rank) (B D : Family N (SwapSplit.realign H).rank), Cycle A C B D := by
  obtain ⟨a,c,hm⟩ := SwapSplit.exists_sum_vecMulVec_of_rank M
  obtain ⟨d,b,hh⟩ := SwapSplit.exists_sum_vecMulVec_of_rank (SwapSplit.realign H)
  refine ⟨(fun t i j => a t (i,j)),(fun t l k => c t (k,l)),
    (fun t j l => b t (j,l)),(fun t k i => d t (i,k)),?_⟩
  intro i j l k
  have val := congrFun (congrFun e (i,j)) (k,l)
  have m := congrFun (congrFun hm (i,j)) (k,l)
  have z := congrFun (congrFun hh (i,k)) (j,l)
  simp only [Matrix.sum_apply,Matrix.vecMulVec_apply] at m z
  change H (i,j) (k,l) = _ at z
  rw [Matrix.add_apply,m,z] at val
  have eq : delta i l * delta j k = (SwapSplit.swapMat ℂ N) (i,j) (k,l) := by
    by_cases h₁ : i=l <;> by_cases h₂ : j=k <;> simp [delta,SwapSplit.swapMat,h₁,h₂,eq_comm]
  rw [eq,val]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  exact mul_comm _ _

theorem swap_lower {N : ℕ} (M H : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ)
    (e : SwapSplit.swapMat ℂ N = M+H) : 2*N ≤ M.rank + (SwapSplit.realign H).rank + 2 := by
  obtain ⟨A,C,B,D,h⟩ := cycle_of_swap M H e
  exact h.bound

end OMA.ProductVectors



namespace OMA.FourSiteRanks

theorem product_vector_necessary {k C n : ℕ} (h : Test k C n) :
    2 * (2^k)^n ≤ C * sliceBudget k n + 2 := by
  obtain ⟨A,B,e,cost⟩ := swap_split_of_test h
  exact (OMA.ProductVectors.swap_lower A B e).trans (Nat.add_le_add_right cost 2)

theorem fourth_power_fourteen (C : ℕ) (hC : C ≤ 14) : ¬ Test 4 C 1 := by
  intro res
  have e := product_vector_necessary res
  rw [show sliceBudget 4 1 = 2 by decide] at e
  norm_num at e
  omega

theorem two_target_le_fifteen_budgets {n : ℕ} (large : 3 ≤ n) :
    2 * (16:ℕ)^n ≤ 15 * sliceBudget 4 n := by
  let i := n/2
  have hi : i ≤ n-i := by dsimp [i]; omega
  have ci : 3 ≤ n.choose i := large.trans (by simpa [i] using Nat.choose_le_middle 1 n)
  have term : n.choose i * min (((4:ℕ)^4)^(n-i)) ((4^4)^i) ≤ sliceBudget 4 n :=
    Finset.single_le_sum (f := fun j => n.choose j * min (((4:ℕ)^4)^(n-j)) ((4^4)^j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by dsimp [i]; omega : i < n+1))
  rw [min_eq_right (Nat.pow_le_pow_right (by decide : 0 < (4:ℕ)^4) hi)] at term
  have center : 3*(256:ℕ)^i ≤ sliceBudget 4 n := (Nat.mul_le_mul_right _ ci).trans term
  have size : (16:ℕ)^n ≤ 16 * 256^i := calc
    _ ≤ 16^(1+2*i) := Nat.pow_le_pow_right (by decide) (by dsimp [i]; omega)
    _ = _ := by rw [pow_add, pow_one, pow_mul]; norm_num
  omega

theorem product_inequality_all_powers_iff (C : ℕ) :
    (∀ n : ℕ, 0 < n → 2 * (2^4)^n ≤ C * sliceBudget 4 n + 2) ↔ 15 ≤ C := by
  constructor
  · intro h
    have e := h 1 (by decide)
    rw [show sliceBudget 4 1 = 2 by decide] at e
    norm_num at e
    omega
  · intro enough n hn
    have least : 2 * (2^4)^n ≤ 15 * sliceBudget 4 n + 2 := by
      by_cases big : 3 ≤ n
      · exact (two_target_le_fifteen_budgets big).trans (Nat.le_add_right _ 2)
      · interval_cases n <;> decide
    exact least.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ enough) 2)

theorem product_comparison_floor (k : ℕ)
    (ex : ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, 0 < n → Test k C n) :
    ∃ C : ℕ, 0 < C ∧ (k=4 → 15 ≤ C) ∧ ∀ n : ℕ, 0 < n → Test k C n := by
  obtain ⟨C,hC,works⟩ := ex
  refine ⟨C,hC,?_,works⟩
  rintro rfl
  exact (product_inequality_all_powers_iff C).mp fun n hn => product_vector_necessary (works n hn)

end OMA.FourSiteRanks



/- The binomial loss at k = 4 permits a lower bound at the critical exponent 5/4. -/

namespace OMA.FourSiteRanks

theorem central_square_budget (m : ℕ) : (m+1) * m.centralBinom^2 ≤ 16^m := by
  induction m with
  | zero => decide
  | succ m ih =>
    have step : (m+2) * (2*(2*m+1))^2 ≤ (m+1)^2 * 16 * (m+1) := by nlinarith
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < (m+1)^2 by positivity)
    calc
      (m+1)^2 * ((m+1+1) * (m+1).centralBinom^2)
          = (m+2) * ((m+1)*(m+1).centralBinom)^2 := by ring
      _ = ((m+2)*(2*(2*m+1))^2) * m.centralBinom^2 := by
        rw [Nat.succ_mul_centralBinom_succ]; ring
      _ ≤ ((m+1)^2 * 16 * (m+1)) * m.centralBinom^2 := Nat.mul_le_mul_right _ step
      _ = ((m+1)^2*16) * ((m+1)*m.centralBinom^2) := by ring
      _ ≤ ((m+1)^2*16) * 16^m := Nat.mul_le_mul_left _ ih
      _ = (m+1)^2 * 16^(m+1) := by rw [pow_succ]; ring

theorem geometric_quarter (m : ℕ) : (∑ i ∈ Finset.range (m+1), (256:ℕ)^i) ≤ 2*256^m := by
  induction m with
  | zero => decide
  | succ m ih => rw [Finset.sum_range_succ,pow_succ]; omega

theorem even_budget (m : ℕ) :
    sliceBudget 4 (2*m) ≤ 4 * m.centralBinom * 256^m := by
  let f (i : ℕ) := min ((256:ℕ)^(2*m-i)) (256^i)
  have low : (∑ i ∈ Finset.range (m+1), f i) ≤ 2*256^m :=
    (Finset.sum_le_sum (fun i _ => min_le_right ..)).trans (geometric_quarter m)
  have high : (∑ i ∈ Finset.range m, f (m+1+i)) ≤ 2*256^m := calc
    _ ≤ ∑ i ∈ Finset.range m, (256:ℕ)^(m-1-i) := by
      apply Finset.sum_le_sum
      intro i hi
      have ex : 2*m-(m+1+i) = m-1-i := by omega
      exact (min_le_left ..).trans_eq (congrArg ((256:ℕ)^·) ex)
    _ = ∑ i ∈ Finset.range m, (256:ℕ)^i := Finset.sum_range_reflect _ _
    _ ≤ ∑ i ∈ Finset.range (m+1), (256:ℕ)^i := by rw [Finset.sum_range_succ]; omega
    _ ≤ _ := geometric_quarter m
  have ctr : (∑ i ∈ Finset.range (2*m+1), f i) ≤ 4*256^m := by
    rw [show 2*m+1 = (m+1)+m by omega,Finset.sum_range_add]
    omega
  unfold sliceBudget
  calc
    _ ≤ ∑ i ∈ Finset.range (2*m+1), m.centralBinom * f i :=
      Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (Nat.choose_le_centralBinom i m)
    _ = m.centralBinom * ∑ i ∈ Finset.range (2*m+1), f i := (Finset.mul_sum ..).symm
    _ ≤ m.centralBinom * (4*256^m) := Nat.mul_le_mul_left _ ctr
    _ = _ := by ring

theorem squared_budget_at_four (m : ℕ) :
    (m+1) * (sliceBudget 4 (2*m))^2 ≤ 16 * ((1024:ℕ)^m)^2 := calc
  _ ≤ (m+1) * (4*m.centralBinom*256^m)^2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (even_budget m) 2)
  _ = (16*(256^m)^2) * ((m+1)*m.centralBinom^2) := by ring
  _ ≤ (16*(256^m)^2) * 16^m := Nat.mul_le_mul_left _ (central_square_budget m)
  _ = _ := by
    have b : ((256:ℕ)^m)^2 * 16^m = (1024^m)^2 := by
      rw [← pow_mul, Nat.mul_comm m 2, pow_mul, ← mul_pow, ← pow_mul, Nat.mul_comm m 2, pow_mul]
      norm_num
    rw [Nat.mul_assoc,b]

/-- A lower bound by a constant fraction of N^(5/4) on an unbounded
subsequence N = 256^m. Uniformity at every dimension is unnecessary. -/
def CriticalCrossingLower : Prop :=
  ∃ K : ℕ, ∀ m₀ : ℕ, ∃ m ≥ m₀,
    ∀ A B : Matrix (Fin (256^m) × Fin (256^m)) (Fin (256^m) × Fin (256^m)) ℂ,
      SwapSplit.swapMat ℂ (256^m) = A+B → 1024^m ≤ K*(A.rank + (SwapSplit.realign B).rank)

theorem fourth_power_failure_of_critical (hard : CriticalCrossingLower) (C : ℕ) :
    ∃ n : ℕ, 0 < n ∧ ¬ Test 4 C n := by
  obtain ⟨K,lower⟩ := hard
  obtain ⟨m,hm,cur⟩ := lower (16*(K*C)^2+1)
  refine ⟨2*m,by omega,?_⟩
  intro h
  have split := swap_split_of_test h
  change ∃ A B : Matrix (Fin ((2^4)^(2*m)) × Fin ((2^4)^(2*m)))
      (Fin ((2^4)^(2*m)) × Fin ((2^4)^(2*m))) ℂ, _ at split
  have eqN : ((2:ℕ)^4)^(2*m) = 256^m := by rw [pow_mul]; rfl
  rw [eqN] at split
  obtain ⟨A,B,e,hcost⟩ := split
  have key : (1024:ℕ)^m ≤ (K*C) * sliceBudget 4 (2*m) := calc
    _ ≤ _ := cur A B e
    _ ≤ _ := (Nat.mul_le_mul_left K hcost).trans_eq (Nat.mul_assoc ..).symm
  have restrict : ((1024:ℕ)^m)^2 * (m+1) ≤ ((1024:ℕ)^m)^2 * (16*(K*C)^2) := calc
    _ ≤ ((K*C)*sliceBudget 4 (2*m))^2 * (m+1) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left key 2)
    _ = (K*C)^2 * ((m+1)*(sliceBudget 4 (2*m))^2) := by ring
    _ ≤ (K*C)^2 * (16*(1024^m)^2) := Nat.mul_le_mul_left _ (squared_budget_at_four m)
    _ = _ := by ring
  have := Nat.le_of_mul_le_mul_left restrict (by positivity)
  omega

set_option maxHeartbeats 1400000 in
theorem four_point_witness_of_critical (hard : CriticalCrossingLower) :
    OMA.R_Erdos20_erdos_20_R1_H2_R1_H1_R1.H1 := by
  apply OMA.R_Erdos20_erdos_20_R1_H2_R1_H1_R1_H1_R2.main _ OMA.FourSiteRanksComparison
  refine ⟨4,by decide,?_⟩
  intro C _
  exact fourth_power_failure_of_critical hard C

end OMA.FourSiteRanks



/- Off-target cancellation required by any complex restriction at the fourth power. -/

namespace OMA.FourSiteRanks

open Matrix
open scoped Classical

abbrev SwapMatrix (N : ℕ) := Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ

theorem swap_rank (N : ℕ) : (SwapSplit.swapMat ℂ N).rank = N^2 := by
  let e := Equiv.prodComm (Fin N) (Fin N)
  let q := Equiv.refl (Fin N × Fin N)
  have eq : SwapSplit.swapMat ℂ N = (1 : SwapMatrix N).submatrix e q := by
    ext p r
    rcases p with ⟨x,y⟩
    rcases r with ⟨u,v⟩
    simp [e,q,SwapSplit.swapMat,Matrix.submatrix,Matrix.one_apply,Prod.ext_iff,eq_comm]
  rw [eq,Matrix.rank_submatrix,Matrix.rank_one,Fintype.card_prod,Fintype.card_fin,pow_two]

theorem swap_realign (N : ℕ) : SwapSplit.realign (SwapSplit.swapMat ℂ N) = SwapSplit.swapMat ℂ N := by
  ext p q
  simp [SwapSplit.realign,SwapSplit.swapMat,eq_comm]

/-- The part of H that changes when the two middle indices are interchanged
has rank at least the size of the full permutation matrix minus the split cost. -/
theorem cancellation_necessary {N : ℕ} {A H : SwapMatrix N}
    (h : SwapSplit.swapMat ℂ N = A+H) :
    N^2 ≤ (A.rank + (SwapSplit.realign H).rank) + (H - SwapSplit.realign H).rank := by
  have eq : SwapSplit.swapMat ℂ N = (A + SwapSplit.realign H) + (H - SwapSplit.realign H) := by
    rw [h]; abel
  calc
    _ = (SwapSplit.swapMat ℂ N).rank := (swap_rank N).symm
    _ = _ := congrArg Matrix.rank eq
    _ ≤ _ := SwapSplit.rank_add_le' _ _
    _ ≤ _ := Nat.add_le_add_right (SwapSplit.rank_add_le' _ _) _

/-- If the sampled split cancels nowhere on the zero entries with unequal
middle indices, its second part is already invariant under realignment. -/
theorem realign_fixed_of_off_diagonal_zero {N : ℕ} (H : SwapMatrix N)
    (z : ∀ x y u v, y ≠ u → H (x,y) (u,v)=0) :
    SwapSplit.realign H = H := by
  ext ⟨x,y⟩ ⟨u,v⟩
  by_cases h : y=u
  · subst u; rfl
  · change H (x,u) (y,v) = H (x,y) (u,v)
    rw [z _ _ _ _ (Ne.symm h),z _ _ _ _ h]

theorem swap_square_capacity (n : ℕ) : (8:ℕ)^n * (32:ℕ)^n = ((2^4)^n)^2 := by
  rw [← mul_pow,← pow_mul,Nat.mul_comm n 2,pow_mul]
  rfl

theorem budget_four (n : ℕ) : sliceBudget 4 n ≤ (32:ℕ)^n := by
  calc
    _ ≤ 2^n * (2^4)^n := budget_le 4 n
    _ = _ := by rw [← mul_pow]; norm_num

theorem half_rank_cancellation {C n : ℕ} (many : 2*C ≤ 8^n) {A H : SwapMatrix ((2^4)^n)}
    (h : SwapSplit.swapMat ℂ ((2^4)^n) = A+H)
    (cost : A.rank + (SwapSplit.realign H).rank ≤ C * sliceBudget 4 n) :
    ((2^4)^n)^2 ≤ 2 * (H - SwapSplit.realign H).rank := by
  have halfCost : 2*(A.rank + (SwapSplit.realign H).rank) ≤ ((2^4)^n)^2 := calc
    _ ≤ 2*(C*sliceBudget 4 n) := Nat.mul_le_mul_left 2 cost
    _ = (2*C)*sliceBudget 4 n := (Nat.mul_assoc ..).symm
    _ ≤ 8^n * 32^n := Nat.mul_le_mul many (budget_four n)
    _ = _ := swap_square_capacity n
  have total := cancellation_necessary h
  omega

/-- At all powers with 2*C <= 8^n, every split within the restriction
budget cancels two nonzero complex entries away from the target support. -/
theorem cancellation_entry {C n : ℕ} (many : 2*C ≤ 8^n) {A H : SwapMatrix ((2^4)^n)}
    (h : SwapSplit.swapMat ℂ ((2^4)^n) = A+H)
    (cost : A.rank + (SwapSplit.realign H).rank ≤ C * sliceBudget 4 n) :
    ∃ x y u v, y ≠ u ∧ H (x,y) (u,v) ≠ 0 ∧ A (x,y) (u,v) = -H (x,y) (u,v) := by
  have rank := half_rank_cancellation many h cost
  have neq : SwapSplit.realign H ≠ H := by
    intro same
    rw [same,sub_self,Matrix.rank_zero,mul_zero] at rank
    have pos : 0 < (((2:ℕ)^4)^n)^2 := by positivity
    omega
  obtain ⟨x,y,u,v,diff,nz⟩ : ∃ x y u v, y ≠ u ∧ H (x,y) (u,v) ≠ 0 := by
    by_contra! none
    apply neq
    exact realign_fixed_of_off_diagonal_zero H none
  refine ⟨x,y,u,v,diff,nz,?_⟩
  have e := congrFun (congrFun h (x,y)) (u,v)
  have zero : A (x,y) (u,v) + H (x,y) (u,v) = 0 := by
    simpa [Matrix.add_apply,SwapSplit.swapMat,diff.symm] using e.symm
  exact eq_neg_of_add_eq_zero_left zero

/-- A tensor power for every copy count at which any restriction must
produce a high-rank discrepancy and off-support cancellation. -/
theorem every_copy_requires_cancellation (C : ℕ) :
    ∃ n : ℕ, 0 < n ∧ (Test 4 C n →
      ∃ A H : SwapMatrix ((2^4)^n), SwapSplit.swapMat ℂ ((2^4)^n) = A+H ∧
        ((2^4)^n)^2 ≤ 2*(H-SwapSplit.realign H).rank ∧
        ∃ x y u v, y ≠ u ∧ H (x,y) (u,v) ≠ 0 ∧ A (x,y) (u,v) = -H (x,y) (u,v)) := by
  let n := C+1
  have h2 : C+1 < (2:ℕ)^(C+1) := Nat.lt_two_pow_self
  have h8 : 2^(C+1)*2 ≤ (8:ℕ)^n := by
    change 2^(C+1)*2 ≤ 8^(C+1)
    have u := Nat.pow_le_pow_left (by decide : 2 ≤ 8) C
    rw [pow_succ,pow_succ]
    omega
  have many : 2*C ≤ 8^n := by omega
  refine ⟨n,by dsimp [n]; omega,?_⟩
  intro res
  obtain ⟨A,H,h,cost⟩ := swap_split_of_test res
  exact ⟨A,H,h,half_rank_cancellation many h cost,cancellation_entry many h cost⟩

/-- Positions with unequal middle indices where the second summand is nonzero.
The swap vanishes at every such position, so the first summand must cancel it. -/
noncomputable def cancelled {N : ℕ} (H : SwapMatrix N) :=
  (Finset.univ : Finset ((Fin N × Fin N) × (Fin N × Fin N))).filter
    fun z => z.1.2 ≠ z.2.1 ∧ H z.1 z.2 ≠ 0

theorem discrepancy_le_entries {N : ℕ} (H : SwapMatrix N) :
    (H - SwapSplit.realign H).rank ≤ 2*(cancelled H).card := by
  let S := cancelled H
  let crossed (z : (Fin N × Fin N) × (Fin N × Fin N)) := (z.1.1,z.2.1)
  let rows := S.image Prod.fst ∪ S.image crossed
  have bound : (H - SwapSplit.realign H).rank ≤ rows.card := by
    apply Matrix.rank_le_card_of_support_subset
    rw [Function.support_subset_iff']
    rintro ⟨x,y⟩ absent
    funext ⟨u,v⟩
    change H (x,y) (u,v) - H (x,u) (y,v) = 0
    by_cases same : y=u
    · subst u; exact sub_self _
    have left : H (x,y) (u,v) = 0 := by
      by_contra nz
      have pos : ((x,y),(u,v)) ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,same,nz⟩
      exact absent (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_,pos,rfl⟩))
    have right : H (x,u) (y,v) = 0 := by
      by_contra nz
      have pos : ((x,u),(y,v)) ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,Ne.symm same,nz⟩
      exact absent (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,pos,rfl⟩))
    rw [left,right,sub_self]
  have size := (Finset.card_union_le (S.image Prod.fst) (S.image crossed)).trans
    (Nat.add_le_add (Finset.card_image_le (f:=Prod.fst)) (Finset.card_image_le (f:=crossed)))
  exact bound.trans (by simpa [rows,S,two_mul] using size)

theorem cancellation_count {k C n : ℕ} {A H : SwapMatrix ((2^k)^n)}
    (h : SwapSplit.swapMat ℂ ((2^k)^n) = A+H)
    (cost : A.rank + (SwapSplit.realign H).rank ≤ C*sliceBudget k n) :
    ((2^k)^n)^2 ≤ C*sliceBudget k n + 2*(cancelled H).card :=
  (cancellation_necessary h).trans (Nat.add_le_add cost (discrepancy_le_entries H))

/-- For fixed copy count, no fixed number of cancelled positions can suffice
at all tensor powers, even when the entries are arbitrary complex numbers. -/
theorem unbounded_cancellation (C B : ℕ) :
    ∃ n : ℕ, 0 < n ∧ ∀ A H : SwapMatrix ((2^4)^n),
      SwapSplit.swapMat ℂ ((2^4)^n) = A+H →
      A.rank + (SwapSplit.realign H).rank ≤ C*sliceBudget 4 n → B < (cancelled H).card := by
  let n := 4*B + 2*C + 1
  have two : n < (2:ℕ)^n := Nat.lt_two_pow_self
  have ge8 := Nat.pow_le_pow_left (by decide : 2 ≤ 8) n
  have ge256 := Nat.pow_le_pow_left (by decide : 2 ≤ 256) n
  have enough : 2*C ≤ 8^n := by dsimp [n] at *; omega
  have size : 4*B < (((2:ℕ)^4)^n)^2 := by
    rw [←pow_mul,Nat.mul_comm n 2,pow_mul]
    change 4*B < 256^n
    dsimp [n] at *
    omega
  refine ⟨n,by dsimp [n]; omega,?_⟩
  intro A H h cost
  have rank := half_rank_cancellation enough h cost
  have bound := discrepancy_le_entries H
  omega

theorem fifteen_two_cancellation {A H : SwapMatrix 256}
    (h : SwapSplit.swapMat ℂ 256 = A+H)
    (cost : A.rank + (SwapSplit.realign H).rank ≤ 15*sliceBudget 4 2) :
    57826 ≤ (H - SwapSplit.realign H).rank ∧ 28913 ≤ (cancelled H).card := by
  have total := cancellation_necessary h
  have s := discrepancy_le_entries H
  rw [show sliceBudget 4 2 = 514 by decide] at cost
  norm_num at total cost
  omega

end OMA.FourSiteRanks



/- A constructive upper bound for the number of copies at each fixed power. -/

namespace OMA.FourSiteRanks

open OMAPort OMA.PlanarInterval OMA.FourSiteComparison
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical

/-- A full two-label diagonal can supply a binary wire on any two sites. -/
theorem wire_le_two (a b : Fin 4) : cls (wireCoord a b) ≤ 2 := by
  apply le_trans (b := ofRaw (Raw.diagonal (Fin 4) ℂ (Fin 2))) _ (by simp)
  apply ofRaw_le_iff.mpr
  let term (t : Fin 2) (_ : Fin 4) := t
  have coeff : (Raw.diagonal (Fin 4) ℂ (Fin 2)).coeff = Crossing.basisTensor term := by
    funext x
    simp only [Raw.diagonal,Crossing.basisTensor,term]
    apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> simp_all
  unfold Raw.Restricts
  rw [coeff]
  apply (Crossing.restriction_basisTensor_iff term _).mpr
  let M (i : Fin 4) (p : Fin ((wireCoord a b).1 i)) (t : Fin 2) : ℂ :=
    (if i=a then (if p.val=t.val then 1 else 0) else 1) *
    (if i=b then (if p.val=t.val then 1 else 0) else 1)
  refine ⟨M,fun x => ?_⟩
  have ha : (x a).val < 2 := by simpa [wireCoord] using (x a).isLt
  have hb : (x b).val < 2 := by simpa [wireCoord] using (x b).isLt
  change (if (x a).val = (x b).val then (1 : ℂ) else 0) = _
  simp only [M,term,Finset.prod_mul_distrib,Finset.prod_ite_eq',Finset.mem_univ,if_true,
    Fin.sum_univ_two,Fin.val_zero,Fin.val_one]
  split_ifs <;> norm_num <;> omega

theorem matching_le_four (a b c d : Fin 4) : cls (matching a b c d) ≤ 4 := by
  change ofRaw (coordRaw (sigMul (wireCoord a b) (wireCoord c d))) ≤ _
  rw [coord_mul,ofRaw_mul]
  exact (mul_mono (wire_le_two a b) (wire_le_two c d)).trans_eq (by norm_num)

theorem class_le_test {k C n : ℕ}
    (h : cls (power (power (matching 0 1 2 3) k) n) ≤ C • ((V^k+W^k)^n)) :
    Test k C n := by
  let B := sigAdd (power (matching 0 2 1 3) k) (power (matching 0 3 1 2) k)
  have base : cls B = V^k+W^k := by
    change ofRaw (coordRaw (sigAdd _ _)) = _
    rw [coord_add,ofRaw_add]
    exact congrArg₂ (· + ·) (cls_pow _ _) (cls_pow _ _)
  rw [← base,← cls_pow B n,← cls_copies (power B n) C] at h
  obtain ⟨M,e⟩ := ofRaw_le_iff.mp h
  refine ⟨M,fun y => (e y).trans (Finset.sum_congr ?_ fun _ _ => mul_comm _ _)⟩
  exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)

/-- A counterexample at power n needs strictly fewer than 128^n copies. -/
theorem fourth_power_available {C n : ℕ} (copies : 128^n ≤ C) : Test 4 C n := by
  apply class_le_test
  rw [cls_pow,cls_pow,nsmul_eq_mul]
  have hv : (1 : FourClass) ≤ V^4 := one_le_of_ne_zero (pow_ne_zero _ (matching_ne 0 2 1 3))
  have hw : (1 : FourClass) ≤ W^4 := one_le_of_ne_zero (pow_ne_zero _ (matching_ne 0 3 1 2))
  have low : (2 : FourClass) ≤ V^4+W^4 := by simpa only [one_add_one_eq_two] using add_mono hv hw
  have power_mono {X Y : FourClass} (le : X ≤ Y) (m : ℕ) : X^m ≤ Y^m := by
    induction m with
    | zero => simp
    | succ m ih => simpa only [pow_succ] using mul_mono ih le
  have mapNat {a b : ℕ} (le : a ≤ b) : (a : FourClass) ≤ b := by
    obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le le
    rw [Nat.cast_add]
    exact le_add_of_nonneg_right (zero_le_tensor _)
  calc
    _ ≤ ((4 : FourClass)^4)^n := power_mono (power_mono (matching_le_four 0 1 2 3) 4) n
    _ = ((128 : ℕ)^n : ℕ) * (2 : FourClass)^n := by push_cast; rw [← mul_pow]; norm_num
    _ ≤ _ := mul_mono (mapNat copies) (power_mono low n)

theorem no_bounded_power_search (cap : ℕ) :
    ∃ C ≥ 15, ∀ n ≤ cap, Test 4 C n := by
  refine ⟨128^(cap+1),?_,fun n hn => fourth_power_available ?_⟩
  · exact (by decide : 15 ≤ 128^1).trans (Nat.pow_le_pow_right (by decide) (by omega))
  · exact Nat.pow_le_pow_right (by decide) (by omega)

end OMA.FourSiteRanks



/- Equality conditions for the first copy count left by the scalar bound. -/

namespace OMA.ProductVectors

open Matrix
open scoped Classical

theorem Cycle.equal_peaks {k : ℕ} {A C B D : Family (k+1) k}
    (h : Cycle A C B D) : peak A = peak D ∧ peak D = peak C ∧ peak C = peak B := by
  have small (T : Family (k+1) k) (x : Vec (k+1)) : (inc T x).rank < k+1 :=
    Nat.lt_succ_of_le (Matrix.rank_le_width _)
  have a := h.step (small D)
  have b := h.rotate.step (small C)
  have c := h.rotate.rotate.step (small B)
  have d := h.rotate.rotate.rotate.step (small A)
  omega

/-- Every nonzero annihilating vector paired with a maximizing vector forces
the two remaining evaluations to have complementary ranks. -/
theorem Cycle.equality_slice {k : ℕ} {A C B D : Family (k+1) k} (h : Cycle A C B D)
    (x w : Vec (k+1)) (maximal : (out A x).rank = peak A) (nz : w ≠ 0)
    (kill : (out D w)ᵀ *ᵥ x = 0) :
    (out D w).rank = peak A ∧ (inc C w).rank + peak A = k+1 := by
  have sy := SwapSplit.sylvester_rank (out A x) (inc C w)ᵀ
  rw [Matrix.rank_transpose,h.product x w kill,Fintype.card_fin,maximal] at sy
  have rankone : (Matrix.vecMulVec w x).rank ≤ 1 := by
    rw [Matrix.vecMulVec_eq (Fin 1)]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
  have cover := h.cover w nz
  have upper := (le_peak D w).trans_eq h.equal_peaks.1.symm
  omega

end OMA.ProductVectors

namespace OMA.FourSiteRanks

open Matrix
open OMAPort OMA.PlanarInterval OMA.FourSiteComparison OMA.ProductVectors
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical NNReal

local instance : Nonempty {i // leftCut i} := ⟨⟨2,by decide⟩⟩
local instance : Nonempty {i // ¬leftCut i} := ⟨⟨3,by decide⟩⟩
local instance : Nonempty {i // rightCut i} := ⟨⟨2,by decide⟩⟩
local instance : Nonempty {i // ¬rightCut i} := ⟨⟨3,by decide⟩⟩

theorem cut_copies (s : Fin 4 → Prop) [DecidablePred s]
    [Nonempty {i // s i}] [Nonempty {i // ¬s i}] (C : ℕ) (X : FourClass) :
    cutRank s ℂ (C • X) = C * cutRank s ℂ X := by
  induction C with
  | zero => simp [cut_zero]
  | succ C ih => rw [succ_nsmul,cut_add,ih,Nat.succ_mul]

/-- At one tensor factor each of the two ranks has its own copy budget. -/
theorem one_factor_split {k C : ℕ} (h : Test k C 1) :
    ∃ A H : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ,
    SwapSplit.swapMat ℂ (2^k) = A+H ∧ A.rank ≤ C ∧ (SwapSplit.realign H).rank ≤ C := by
  let X := power (power (matching 0 1 2 3) k) 1
  let R := coordRaw X
  have grid : FullGrid X (2^k) := by simpa only [pow_one] using (matching_grid.power k).power 1
  obtain ⟨f,hf⟩ := grid
  let L := C • V^k
  let Y := C • W^k
  have hsum : ofRaw R ≤ ∑ j : Fin 2, (![L,Y] : Fin 2 → FourClass) j := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      pow_one,nsmul_add,L,Y] using test_class_le h
  obtain ⟨z,split,bounds⟩ := images_of_le_sum R (![L,Y] : Fin 2 → FourClass) hsum
  let p : Fin (2^k) := ⟨0,by positivity⟩
  refine ⟨gridMatrix f (z 0),gridMatrix f (z 1),?_,?_,?_⟩
  · rw [← grid_matrix_swap f hf,show X.2 = R.coeff from rfl,split,Fin.sum_univ_two]
    rfl
  · apply ((grid_left_le p {R with coeff := z 0} f).trans (monotone_cutRank leftCut ℂ (bounds 0))).trans
    change cutRank leftCut ℂ (C • V^k) ≤ C
    rw [cut_copies,cut_pow]
    simpa only [one_pow,mul_one] using Nat.mul_le_mul_left C (Nat.pow_le_pow_left left_V k)
  · apply ((grid_right_le p {R with coeff := z 1} f).trans (monotone_cutRank rightCut ℂ (bounds 1))).trans
    change cutRank rightCut ℂ (C • W^k) ≤ C
    rw [cut_copies,cut_pow]
    simpa only [one_pow,mul_one] using Nat.mul_le_mul_left C (Nat.pow_le_pow_left right_W k)

theorem fifteen_rigid (res : Test 4 15 1) :
    ∃ A C B D : Family 16 15, Cycle A C B D ∧ peak A = peak D ∧ peak D = peak C ∧
      peak C = peak B ∧ ∀ x w, (out A x).rank = peak A → w ≠ 0 → (out D w)ᵀ *ᵥ x = 0 →
      (out D w).rank = peak A ∧ (inc C w).rank + peak A = 16 := by
  obtain ⟨M,H,e,r,s⟩ := one_factor_split res
  have cost := swap_lower M H e
  norm_num at cost
  have eqr : M.rank=15 := by omega
  have eqs : (SwapSplit.realign H).rank=15 := by omega
  obtain ⟨A,C,B,D,h⟩ := (show ∃ A C B D : Family 16 15, Cycle A C B D by
    have z := cycle_of_swap M H e
    rw [eqr,eqs] at z
    exact z)
  obtain ⟨a,b,c⟩ := h.equal_peaks (k:=15)
  exact ⟨A,C,B,D,h,a,b,c,h.equality_slice (k:=15)⟩

/-- Only the N=16 instance of the 2N-1 bound in Green, Theorem 1(b),
is needed here. That stronger matrix lower bound is an explicit hypothesis. -/
theorem fifteen_of_rank_thirty_one
    (lb : ∀ A H : Matrix (Fin 16 × Fin 16) (Fin 16 × Fin 16) ℂ,
      SwapSplit.swapMat ℂ 16 = A+H → 31 ≤ A.rank + (SwapSplit.realign H).rank) :
    ¬ Test 4 15 1 := by
  intro h
  obtain ⟨A,H,eq,r,s⟩ := one_factor_split h
  have lower := lb A H eq
  omega

/-- Even a 2N crossing estimate at every dimension leaves all copy counts
from sixteen onward numerically possible at every positive tensor power. -/
theorem twice_dimension_all_powers_iff (C : ℕ) :
    (∀ n : ℕ, 0 < n → 2*(2^4)^n ≤ C*sliceBudget 4 n) ↔ 16 ≤ C := by
  constructor
  · intro all
    have lower := all 1 (by decide)
    rw [show sliceBudget 4 1 = 2 by decide] at lower
    norm_num at lower
    omega
  · intro enough n _
    change 2*16^n ≤ C*sliceBudget 4 n
    have lower := fourth_power_le_eight_budgets n
    have cost := Nat.mul_le_mul_right (sliceBudget 4 n) enough
    omega

end OMA.FourSiteRanks



/- Polynomial continuation of vectors in the kernel of a matrix of maximal rank. -/

namespace OMA.GreenChart

open Matrix Polynomial Filter
open scoped Classical
noncomputable section

variable {a b c : Type} [Fintype a] [Fintype b] [Fintype c]

/-- A matrix of rank d contains an invertible d by d compression. -/
theorem pivot (M : Matrix a b ℂ) : ∃ (L : Matrix (Fin M.rank) a ℂ) (K : Matrix b (Fin M.rank) ℂ),
    L*M*K=1 := by
  let f := M.mulVecLin
  let W := LinearMap.range f
  let e := (Module.finBasis ℂ W).equivFun
  obtain ⟨g,hg⟩ := W.subtype.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr W.subtype_injective)
  obtain ⟨s,hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr f.surjective_rangeRestrict)
  let l := e.toLinearMap.comp g
  let k := s.comp e.symm.toLinearMap
  change ∃ (L : Matrix (Fin (Module.finrank ℂ W)) a ℂ) (K : Matrix b (Fin (Module.finrank ℂ W)) ℂ), L*M*K=1
  refine ⟨l.toMatrix',k.toMatrix',?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul,Matrix.toLin'_mul,Matrix.toLin'_toMatrix',Matrix.toLin'_toMatrix',Matrix.toLin'_one]
  apply LinearMap.ext
  intro v
  have he : (l.comp (f.comp k)) v = v := by
    have h1 := LinearMap.congr_fun hs (e.symm v)
    have h2 := LinearMap.congr_fun hg (e.symm v)
    change f.rangeRestrict (s (e.symm v)) = e.symm v at h1
    change g ((e.symm v : W) : a → ℂ) = e.symm v at h2
    change e (g (f (s (e.symm v)))) = v
    rw [show f (s (e.symm v)) = ((e.symm v : W) : a → ℂ) from congrArg Subtype.val h1,h2]
    exact e.apply_symm_apply v
  exact he

abbrev PMat (a b : Type) := Matrix a b ℂ[X]

def ev (t : ℂ) (P : PMat a b) : Matrix a b ℂ := P.map (Polynomial.eval t)
def ec (M : Matrix a b ℂ) : PMat a b := M.map Polynomial.C
def val (t : ℂ) (v : b → ℂ[X]) : b → ℂ := fun i => (v i).eval t
def con (x : b → ℂ) : b → ℂ[X] := fun i => C (x i)

@[simp] theorem ev_ec (t : ℂ) (M : Matrix a b ℂ) : ev t (ec M)=M := by ext; simp [ev,ec]
@[simp] theorem val_con (t : ℂ) (x : b → ℂ) : val t (con x)=x := by ext; simp [val,con]
@[simp] theorem ev_mul (t : ℂ) (M : PMat a b) (K : PMat b c) : ev t (M*K)=ev t M*ev t K := by
  ext i j; simp [ev,Matrix.mul_apply,Polynomial.eval_finsetSum]
@[simp] theorem ev_tr (t : ℂ) (M : PMat a b) : ev t Mᵀ=(ev t M)ᵀ := rfl
@[simp] theorem val_mulVec (t : ℂ) (M : PMat a b) (v : b → ℂ[X]) :
    val t (M *ᵥ v)=ev t M *ᵥ val t v := by
  ext i; simp [val,ev,Matrix.mulVec,dotProduct,Polynomial.eval_finsetSum]
@[simp] theorem val_sub (t : ℂ) (u v : b → ℂ[X]) : val t (u-v)=val t u-val t v := by
  ext; simp [val]
@[simp] theorem val_smul (t : ℂ) (p : ℂ[X]) (v : b → ℂ[X]) :
    val t (p • v)=p.eval t • val t v := by ext; simp [val,smul_eq_mul]
@[simp] theorem ev_det [DecidableEq a] (t : ℂ) (M : PMat a a) : M.det.eval t = (ev t M).det :=
  (Polynomial.evalRingHom t).map_det M

theorem often_ne {p : ℂ[X]} {t : ℂ} (h : p.eval t ≠ 0) : ∀ᶠ u in cofinite, p.eval u ≠ 0 := by
  have nz : p ≠ 0 := by intro e; simp [e] at h
  rw [Filter.eventually_cofinite]
  simpa only [not_not,Polynomial.IsRoot] using Polynomial.finite_setOfPred_isRoot nz

theorem middle_le (L : Matrix a b ℂ) {d e : Type} [Fintype d] [Fintype e]
    (M : Matrix b d ℂ) (K : Matrix d e ℂ) : (L*M*K).rank ≤ M.rank :=
  (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem generic_rank (M : PMat a b) (t : ℂ) : ∀ᶠ u in cofinite, (ev t M).rank ≤ (ev u M).rank := by
  obtain ⟨L,K,h⟩ := pivot (ev t M)
  let S := ec L*M*ec K
  have h0 : S.det.eval t ≠ 0 := by simp [S,h]
  filter_upwards [often_ne h0] with u hu
  rw [ev_det] at hu
  have rr := Matrix.rank_of_det_ne_zero hu
  simp only [Fintype.card_fin] at rr
  exact rr.symm.trans_le (by simpa [S] using middle_le L (ev u M) K)

theorem ker_of_compress (L : Matrix c a ℂ) (M : Matrix a b ℂ) (rank : M.rank ≤ (L*M).rank)
    {x : b → ℂ} (z : (L*M) *ᵥ x = 0) : M *ᵥ x = 0 := by
  have inc : LinearMap.ker M.mulVecLin ≤ LinearMap.ker (L*M).mulVecLin := by
    intro v hv
    change (L*M) *ᵥ v = 0
    rw [← Matrix.mulVec_mulVec,show M *ᵥ v=0 from hv,Matrix.mulVec_zero]
  have d := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have e := LinearMap.finrank_range_add_finrank_ker (L*M).mulVecLin
  change M.rank + _ = _ at d
  change (L*M).rank + _ = _ at e
  have same := Submodule.eq_of_le_of_finrank_le inc (by omega)
  have mem : x ∈ LinearMap.ker (L*M).mulVecLin := z
  rw [← same] at mem
  exact mem

/-- A polynomial kernel vector through a prescribed vector at a maximal-rank parameter. -/
theorem lift_kernel (M : PMat a b) (t : ℂ) (x : b → ℂ) (z : ev t M *ᵥ x=0)
    (top : ∀ u, (ev u M).rank ≤ (ev t M).rank) :
    ∃ v : b → ℂ[X], val t v=x ∧ ∀ᶠ u in cofinite, ev u M *ᵥ val u v=0 := by
  obtain ⟨L,K,p⟩ := pivot (ev t M)
  let S := ec L*M*ec K
  let v := S.det • con x - ec K *ᵥ (S.adjugate *ᵥ (ec L *ᵥ (M *ᵥ con x)))
  have one : S.det.eval t=1 := by simp [S,p]
  refine ⟨v,by simp only [v,val_sub,val_smul,val_con,val_mulVec,ev_ec,one,z,Matrix.mulVec_zero,one_smul,sub_zero],?_⟩
  have rel : (ec L*M) *ᵥ v=0 := by
    rw [show v = _ from rfl,Matrix.mulVec_sub,Matrix.mulVec_smul,Matrix.mulVec_mulVec]
    change S.det • ((ec L*M) *ᵥ con x) - S *ᵥ (S.adjugate *ᵥ _) = 0
    rw [Matrix.mulVec_mulVec,Matrix.mul_adjugate,Matrix.smul_mulVec,Matrix.one_mulVec,
      Matrix.mulVec_mulVec,sub_self]
  filter_upwards [often_ne (one ▸ one_ne_zero : S.det.eval t ≠ 0)] with u hu
  have eql := congrArg (val u) rel
  have zero : (L*ev u M) *ᵥ val u v=0 := by simpa only [val_mulVec,ev_mul,ev_ec,show val u (0 : Fin (ev t M).rank → ℂ[X])=0 by ext; simp [val]] using eql
  apply ker_of_compress L (ev u M) _ zero
  rw [ev_det] at hu
  have rr := Matrix.rank_of_det_ne_zero hu
  simp only [Fintype.card_fin] at rr
  apply (top u).trans (rr.symm.trans_le ?_)
  simpa [S] using Matrix.rank_mul_le_left (L*ev u M) K

end
end OMA.GreenChart


/- The equality case in dimension sixteen. -/
namespace OMA.ProductVectors
open Matrix Polynomial Filter OMA.GreenChart
open scoped Classical
noncomputable section

variable {r s : ℕ} {A C : Family 16 r} {B D : Family 16 s}

theorem Cycle.small_inc (h : Cycle A C B D) (size : r+s=30) (x : Vec 16) : (inc A x).rank < 16 := by
  by_cases hr : r < 16
  · exact lt_of_le_of_lt (Matrix.rank_le_width _) hr
  have sm (y : Vec 16) : (inc (flipFamily B) y).rank < 16 := by
    have t := Matrix.rank_le_width (inc (flipFamily B) y); omega
  have e := h.flip.step sm
  have b := peak_le (flipFamily B)
  have v := le_peak (flipFamily A) x
  rw [out_flip] at v
  omega

theorem Cycle.tight_step (h : Cycle A C B D) (size : r+s=30) : peak A + 16 = r+1+peak D := by
  have d := h.step (h.rotate.small_inc (by omega))
  have c := h.rotate.step (h.rotate.rotate.small_inc size)
  have b := h.rotate.rotate.step (h.rotate.rotate.rotate.small_inc (by omega))
  have a := h.rotate.rotate.rotate.step (h.small_inc size)
  omega

theorem rank_product_one {N : ℕ} (x w : Vec N) : (Matrix.vecMulVec w x).rank ≤ 1 := by
  rw [Matrix.vecMulVec_eq (Fin 1)]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)

theorem Cycle.hit_max (h : Cycle A C B D) (size : r+s=30) (x w : Vec 16)
    (ax : (out A x).rank=peak A) (hw : w≠0) (kill : (out D w)ᵀ *ᵥ x=0) :
    (out D w).rank=peak D := by
  have sy := SwapSplit.sylvester_rank (out A x) (inc C w)ᵀ
  rw [Matrix.rank_transpose,h.product x w kill,Fintype.card_fin,ax] at sy
  have c := h.cover w hw
  have ro := rank_product_one x w
  have d := le_peak D w
  have t := h.tight_step size
  omega

def outPoly {N r : ℕ} (A : Family N r) (v : Fin N → ℂ[X]) : PMat (Fin N) (Fin r) :=
  fun j a => ∑ i, v i * Polynomial.C (A a i j)

@[simp] theorem ev_outPoly {N r : ℕ} (A : Family N r) (v : Fin N → ℂ[X]) (t : ℂ) :
    ev t (outPoly A v) = out A (val t v) := by
  ext; simp [ev,outPoly,out,val,Matrix.vecMul,dotProduct,Polynomial.eval_finsetSum]

def linePoly {N : ℕ} (w z : Vec N) (i : Fin N) : ℂ[X] :=
  Polynomial.C (w i) + X * Polynomial.C (z i - w i)
@[simp] theorem line_zero {N} (w z : Vec N) : val 0 (linePoly w z)=w := by ext; simp [val,linePoly]
@[simp] theorem line_one {N} (w z : Vec N) : val 1 (linePoly w z)=z := by ext; simp [val,linePoly]

/-- The opposite family attains its maximum along an incidence with a maximizing first family. -/
theorem Cycle.opposite_sum (h : Cycle A C B D) (size : r+s=30) : peak A+peak (flipFamily C) ≤ r+1 := by
  obtain ⟨x,ax⟩ := peak_attained A
  obtain ⟨w,wn,kill⟩ := kernel_vector (inc D x) (h.rotate.small_inc (by omega) x)
  rw [← interchange] at kill
  have dw := h.hit_max size x w ax wn kill
  obtain ⟨z,cz⟩ := peak_attained (flipFamily C)
  let path := linePoly w z
  let M := (outPoly D path)ᵀ
  have at0 : ev 0 M *ᵥ x = 0 := by simpa [M,path] using kill
  have top (t : ℂ) : (ev t M).rank ≤ (ev 0 M).rank := by
    simp only [M,ev_tr,ev_outPoly,Matrix.rank_transpose,path,line_zero,dw]
    exact le_peak _ _
  obtain ⟨v,v0,good⟩ := lift_kernel M 0 x at0 top
  have genA := generic_rank (outPoly A v) 0
  have genC := generic_rank (outPoly (flipFamily C) path) 1
  obtain ⟨t,ht,ha,hc⟩ := (good.and (genA.and genC)).exists
  simp only [M,ev_tr,ev_outPoly] at ht
  simp only [ev_outPoly,v0,ax] at ha
  simp only [ev_outPoly,path,line_one,out_flip] at hc
  have sy := SwapSplit.sylvester_rank (out A (val t v)) (inc C (val t path))ᵀ
  rw [Matrix.rank_transpose,h.product _ _ ht,Fintype.card_fin] at sy
  have one := rank_product_one (val t v) (val t path)
  change (inc C z).rank ≤ (inc C (val t path)).rank at hc
  rw [←out_flip C z,cz] at hc
  omega

theorem Cycle.exact_cover (h : Cycle A C B D) (size : r+s=30) (w : Vec 16) (nz : w ≠ 0) :
    (inc C w).rank+(out D w).rank=16 := by
  have a := h.cover w nz
  have b := h.opposite_sum size
  have d := h.tight_step size
  have c := le_peak (flipFamily C) w
  rw [out_flip] at c
  have g := le_peak D w
  omega

theorem Cycle.orth (h : Cycle A C B D) (size : r+s=30) (x : Vec 16) :
    (inc D x)ᵀ * out A x = 0 := by
  by_cases hx : x=0
  · subst x
    have z : out A 0=0 := by ext; simp [out,Matrix.vecMul,dotProduct]
    rw [z,Matrix.mul_zero]
  have sum := h.rotate.rotate.rotate.exact_cover (by omega) x hx
  let K := (inc D x)ᵀ.mulVecLin
  let L := (out A x).mulVecLin
  have sub : LinearMap.ker K ≤ LinearMap.range L := by
    intro w hw
    have p := h.product x w (by rw [interchange]; exact hw)
    obtain ⟨i,hi⟩ : ∃ i, x i ≠ 0 := by by_contra! z; exact hx (funext z)
    let v : Fin 16 → ℂ := Pi.single i (x i)⁻¹
    have col := congrArg (fun m : Matrix (Fin 16) (Fin 16) ℂ => m *ᵥ v) p
    refine ⟨(inc C w)ᵀ *ᵥ v,?_⟩
    change out A x *ᵥ ((inc C w)ᵀ *ᵥ v) = w
    rw [Matrix.mulVec_mulVec,col]
    ext j
    simp [v,Matrix.mulVec,dotProduct,Matrix.vecMulVec_apply,Pi.single_apply,mul_assoc,hi]
  have dim := LinearMap.finrank_range_add_finrank_ker K
  change (inc D x)ᵀ.rank + Module.finrank ℂ (LinearMap.ker K) = _ at dim
  rw [Matrix.rank_transpose,Module.finrank_fintype_fun_eq_card,Fintype.card_fin] at dim
  have eq := Submodule.eq_of_le_of_finrank_le sub (by change (out A x).rank ≤ _; omega)
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [←Matrix.mulVec_mulVec,Matrix.zero_mulVec]
  have mem : L v ∈ LinearMap.range L := LinearMap.mem_range_self L v
  rw [←eq] at mem
  exact mem

end
end OMA.ProductVectors



/- Matrix-unit commutator relations in coefficient spaces of dimension at most fifteen. -/
namespace OMA.GreenLie
open Matrix
open scoped Classical
noncomputable section

abbrev I := Fin 16
abbrev Sq (r : ℕ) := Matrix (Fin r) (Fin r) ℂ

def MatrixUnits {r} (T : I → I → Sq r) : Prop := ∀ i j k l,
  T i j * T k l - T k l * T i j =
  (if j=k then T i l else 0) - (if l=i then T k j else 0)

private def weight (i : I) : ℂ := ⟨(i.val : ℝ),(i.val : ℝ)^2⟩
private abbrev Edges := ↥(Finset.univ.offDiag : Finset (I × I))
private def freq (e : Edges) : ℂ := weight e.val.1 - weight e.val.2

private theorem freq_injective : Function.Injective freq := by
  rintro ⟨⟨i,j⟩,hij⟩ ⟨⟨k,l⟩,hkl⟩ eq
  have h : i≠j := by simpa [Finset.mem_offDiag] using hij
  have re := congrArg Complex.re eq
  have im := congrArg Complex.im eq
  change (i.val : ℝ)-j.val = k.val-l.val at re
  change (i.val : ℝ)^2-(j.val : ℝ)^2 = (k.val : ℝ)^2-(l.val : ℝ)^2 at im
  have nz : (i.val : ℝ)-j.val ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (Fin.val_ne_of_ne h))
  have sums : (i.val : ℝ)+j.val = k.val+l.val := by
    apply mul_left_cancel₀ nz
    calc
      _ = (i.val : ℝ)^2-(j.val : ℝ)^2 := by ring
      _ = _ := im
      _ = _ := by rw [re]; ring
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext; exact_mod_cast (show (i.val : ℝ)=k.val by linarith)
  · apply Fin.ext; exact_mod_cast (show (j.val : ℝ)=l.val by linarith)

private def ad {r} (D : Sq r) : Sq r →ₗ[ℂ] Sq r where
  toFun M := D*M-M*D
  map_add' M N := by noncomm_ring
  map_smul' a M := by simp [Matrix.mul_smul,Matrix.smul_mul,smul_sub]

private theorem zero_edge {r} (T : I → I → Sq r) (comm : MatrixUnits T) (small : r ≤ 15) :
    ∃ i j, i≠j ∧ T i j=0 := by
  by_contra! nz
  let H := ∑ i : I, weight i • T i i
  let v (e : Edges) := T e.val.1 e.val.2
  have eigen (e : Edges) : Module.End.HasEigenvector (ad H) (freq e) (v e) := by
    obtain ⟨⟨i,j⟩,hij⟩ := e
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_,nz i j (by simpa [Finset.mem_offDiag] using hij)⟩
    change H*T i j-T i j*H = (weight i-weight j) • T i j
    calc
      _ = ∑ k : I, weight k • (T k k*T i j-T i j*T k k) := by
        simp only [H,Finset.sum_mul,Finset.mul_sum,smul_sub,Finset.sum_sub_distrib,
          Matrix.smul_mul,Matrix.mul_smul,Finset.smul_sum]
      _ = ∑ k : I, weight k • ((if k=i then T k j else 0) - (if j=k then T i k else 0)) :=
        Finset.sum_congr rfl fun k _ => congrArg (weight k • ·) (comm k k i j)
      _ = _ := by simp [smul_sub,Finset.sum_sub_distrib,smul_ite,sub_smul,eq_comm]
  have ind := Module.End.eigenvectors_linearIndependent' (ad H) freq freq_injective v eigen
  have bound := ind.fintype_card_le_finrank
  have count : Fintype.card Edges = 240 := by rw [Fintype.card_coe,Finset.offDiag_card]; decide
  rw [count,Module.finrank_matrix] at bound
  simp only [Fintype.card_fin,Module.finrank_self,mul_one] at bound
  have cap := Nat.mul_le_mul small small
  omega

/-- The off-diagonal generators vanish and all diagonal generators coincide. -/
theorem scalar_units {r} (T : I → I → Sq r) (comm : MatrixUnits T) (small : r ≤ 15) :
    ∃ E : Sq r, ∀ i j, T i j = if i=j then E else 0 := by
  obtain ⟨i,j,ij,z⟩ := zero_edge T comm small
  have diag {a b : I} (zero : T a b=0) : T a a=T b b := by
    have e := comm a b b a
    simpa [zero,sub_eq_zero,eq_comm] using e.symm
  have d := diag z
  have row (k : I) (ik : i≠k) : T i k=0 := by
    by_cases jk : j=k
    · simpa [←jk] using z
    have p := comm i i i k
    have q := comm j j i k
    rw [d] at p
    simpa [ik,Ne.symm ik,ij,Ne.symm ij,jk,Ne.symm jk] using p.symm.trans q
  have equal (k : I) : T k k=T i i := by
    by_cases same : i=k
    · rw [same]
    · exact (diag (row k same)).symm
  refine ⟨T i i,fun a b => ?_⟩
  by_cases ab : a=b
  · subst b; simpa using equal a
  rw [if_neg ab]
  obtain ⟨c,ca,cb⟩ : ∃ c : I, c≠a ∧ c≠b := by
    by_contra! no
    have sub : (Finset.univ : Finset I) ⊆ {a,b} := by
      intro c _; by_cases h : c=a
      · simp [h]
      · simp [no c h]
    have card := (Finset.card_le_card sub).trans (Finset.card_insert_le a {b})
    norm_num [I] at card
  have p := comm a a a b
  have q := comm c c a b
  rw [(equal a).trans (equal c).symm] at p
  simpa [ab,Ne.symm ab,ca,cb,Ne.symm cb] using p.symm.trans q

end
end OMA.GreenLie



/- A small coefficient space cannot satisfy the four-site equality identities. -/
namespace OMA.GreenLie
open Matrix
open scoped Classical
noncomputable section

structure Frame (r s : ℕ) where
  P : I → Matrix I (Fin r) ℂ
  Q : I → Matrix (Fin r) I ℂ
  B : I → Matrix I (Fin s) ℂ
  T : I → Matrix (Fin s) I ℂ
  cut : ∀ i j, P i * Q j + B j * T i = if i=j then 1 else 0
  zeroTP : ∀ i, T i * P i=0
  antiTP : ∀ i j, T i * P j = -(T j * P i)
  antiQB : ∀ i j, Q i * B j = -(Q j * B i)

variable {r s : ℕ} (G : Frame r s)

theorem Frame.units : MatrixUnits (fun i j => G.Q i * G.P j) := by
  have prod (i j k l : I) : G.Q i * G.P j * (G.Q k * G.P l) =
      (if j=k then G.Q i*G.P l else 0) - (G.Q i*G.B k)*(G.T j*G.P l) := by
    have cut : G.P j*G.Q k = (if j=k then 1 else 0) - G.B k*G.T j := eq_sub_of_add_eq (G.cut j k)
    calc
      _ = G.Q i * (G.P j*G.Q k) * G.P l := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [cut]; split_ifs <;> simp [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
  intro i j k l
  rw [prod,prod k l i j]
  have exch : (G.Q i*G.B k)*(G.T j*G.P l)=(G.Q k*G.B i)*(G.T l*G.P j) := by
    rw [G.antiQB i k,G.antiTP j l,Matrix.neg_mul,Matrix.mul_neg,neg_neg]
  rw [exch]; abel

private theorem rank_factor {J : Type} [Fintype J] [DecidableEq J] {s : ℕ}
    (F : Matrix J (Fin s) ℂ) (K : Matrix (Fin s) J ℂ) (a : ℂ) (nz : a ≠ 0)
    (eq : F*K = a • (1 : Matrix J J ℂ)) : Fintype.card J ≤ s := by
  have b := (Matrix.rank_mul_le_left F K).trans (F.rank_le_card_width.trans_eq (Fintype.card_fin s))
  rw [eq,Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero nz),Matrix.rank_one] at b
  exact b

private def lo (i : Fin 8) : I := ⟨i.val,by omega⟩
private def hi (i : Fin 8) : I := ⟨i.val+8,by omega⟩
private theorem mixed (i j : Fin 8) : lo i ≠ hi j := by simp [lo,hi,Fin.ext_iff]; omega
private theorem lo_inj : Function.Injective lo := fun _ _ h => Fin.ext (congrArg (fun t : I => t.val) h)
private theorem hi_inj : Function.Injective hi := by
  intro a b h; apply Fin.ext; have t := congrArg Fin.val h; change a.val+8=b.val+8 at t; omega

include G in
theorem Frame.too_small (small : r ≤ 15) (other : s ≤ 30) : False := by
  obtain ⟨E,units⟩ := scalar_units _ G.units small
  have same (i : I) : G.Q i * G.P i=E := by simpa using units i i
  have fix (i : I) : G.P i * E=G.P i := by
    have h := congrArg (fun M : Matrix I I ℂ => M * G.P i) (G.cut i i)
    simpa [Matrix.add_mul,Matrix.mul_assoc,same,G.zeroTP] using h
  have idem : E*E=E := calc
    _ = (G.Q 0 * G.P 0)*E := by rw [same]
    _ = E := by rw [Matrix.mul_assoc,fix,same]
  by_cases zero : E=0
  · have Pz (i : I) : G.P i=0 := by simpa [zero] using (fix i).symm
    let f (i : Fin 2) : I := ⟨i.val, by omega⟩
    let F : Matrix (Fin 2 × I) (Fin s) ℂ := fun p t => G.B (f p.1) p.2 t
    let K : Matrix (Fin s) (Fin 2 × I) ℂ := fun t p => G.T (f p.1) t p.2
    have eq : F*K = (1:ℂ) • 1 := by
      rw [one_smul]; ext ⟨j,a⟩ ⟨i,b⟩
      have t := congrFun (congrFun (G.cut (f i) (f j)) a) b
      change (G.B (f j) * G.T (f i)) a b = _
      by_cases ij : i=j
      · subst j; simpa [Pz,Matrix.one_apply,Prod.ext_iff] using t
      · have diff : f i ≠ f j := fun e => ij (Fin.ext (congrArg (fun t : I => t.val) e))
        simpa [Pz,Matrix.one_apply,Prod.ext_iff,diff,ij,Ne.symm ij] using t
    have bound := rank_factor F K 1 one_ne_zero eq
    simp [I] at bound
    omega
  obtain ⟨a,b,nz⟩ : ∃ a b, E a b ≠ 0 := by
    by_contra! all; exact zero (Matrix.ext all)
  let F : Matrix (Fin 8 × Fin 8) (Fin s) ℂ := fun p t => (G.Q (lo p.1)*G.B (hi p.2)) a t
  let K : Matrix (Fin s) (Fin 8 × Fin 8) ℂ := fun t p => (G.T (lo p.1)*G.P (hi p.2)) t b
  have eq : F*K = (-E a b) • 1 := by
    ext ⟨k,j⟩ ⟨i,l⟩
    have z := G.cut (lo i) (hi j)
    rw [if_neg (mixed i j)] at z
    have z' : G.B (hi j)*G.T (lo i) = -(G.P (lo i)*G.Q (hi j)) := eq_neg_of_add_eq_zero_right z
    have entry : (G.Q (lo k)*G.B (hi j))*(G.T (lo i)*G.P (hi l)) =
        -((G.Q (lo k)*G.P (lo i))*(G.Q (hi j)*G.P (hi l))) := by
      calc
        _ = G.Q (lo k) * (G.B (hi j)*G.T (lo i)) * G.P (hi l) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [z']; simp [Matrix.mul_neg,Matrix.neg_mul,Matrix.mul_assoc]
    change ((G.Q (lo k)*G.B (hi j))*(G.T (lo i)*G.P (hi l))) a b = _
    rw [entry,units,units]
    by_cases ki : k=i <;> by_cases jl : j=l <;>
      simp [lo_inj.eq_iff,hi_inj.eq_iff,ki,jl,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Prod.ext_iff,idem]
  have bound := rank_factor F K _ (neg_ne_zero.mpr nz) eq
  simp at bound
  omega

end
end OMA.GreenLie


/- The dimension-sixteen case of Evan Green's crossing bound (Theorem 1(b),
https://doi.org/10.5281/zenodo.24522729). The proof uses polynomial kernel
continuation, matrix-unit commutators and two finite block-matrix rank tests. -/
namespace OMA.ProductVectors
open Matrix OMA.GreenLie
open scoped Classical
noncomputable section

private def basisVec (i : Fin 16) : Vec 16 := Pi.single i 1

private theorem out_add {r} (A : Family 16 r) (x y : Vec 16) : out A (x+y)=out A x+out A y := by
  ext i j; simp [out,Matrix.add_vecMul]
private theorem inc_add {r} (A : Family 16 r) (x y : Vec 16) : inc A (x+y)=inc A x+inc A y := by
  ext i j; simp [inc,Matrix.mulVec_add]
private theorem out_basis {r} (A : Family 16 r) (i j a) : out A (basisVec i) j a = A a i j := by
  simp [out,basisVec,Matrix.vecMul,dotProduct,Pi.single_apply,ite_mul]
private theorem inc_basis {r} (A : Family 16 r) (i j a) : inc A (basisVec i) j a = A a j i := by
  simp [inc,basisVec,Matrix.mulVec,dotProduct,Pi.single_apply,mul_ite]

variable {r s : ℕ} {A C : Family 16 r} {B D : Family 16 s}

private theorem Cycle.orth_swap (h : Cycle A C B D) (size : r+s=30) (x y : Vec 16) :
    (inc D x)ᵀ*out A y = -((inc D y)ᵀ*out A x) := by
  have e := h.orth size (x+y)
  rw [out_add,inc_add,Matrix.transpose_add,Matrix.add_mul,Matrix.mul_add,Matrix.mul_add,
    h.orth size x,h.orth size y,zero_add,add_zero] at e
  exact eq_neg_of_add_eq_zero_left e

private def Cycle.frame (h : Cycle A C B D) (size : r+s=30) : Frame r s where
  P i := out A (basisVec i)
  Q j := (out C (basisVec j))ᵀ
  B j := inc B (basisVec j)
  T i := (inc D (basisVec i))ᵀ
  cut i k := by
    ext j l
    have v := h i j k l
    simp only [Matrix.add_apply,Matrix.mul_apply,Matrix.transpose_apply,out_basis,inc_basis]
    rw [←v]
    by_cases eq : i=k <;> simp [delta,Matrix.one_apply,eq]
  zeroTP i := h.orth size _
  antiTP i j := h.orth_swap size _ _
  antiQB i j := by
    have e := congrArg Matrix.transpose (h.rotate.rotate.orth_swap size (basisVec j) (basisVec i))
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_neg] using e

/-- Every split of the sixteen-dimensional complex swap costs at least 31. -/
theorem green_sixteen (M H : Matrix (Fin 16 × Fin 16) (Fin 16 × Fin 16) ℂ)
    (e : SwapSplit.swapMat ℂ 16 = M+H) : 31 ≤ M.rank + (SwapSplit.realign H).rank := by
  obtain ⟨A,C,B,D,h⟩ := cycle_of_swap M H e
  have lower := h.bound
  by_contra! small
  have cost : M.rank + (SwapSplit.realign H).rank=30 := by omega
  by_cases le : M.rank ≤ 15
  · exact (h.frame cost).too_small le (by omega)
  · exact (h.rotate.frame (by omega)).too_small (by omega) (by omega)

end
end OMA.ProductVectors

namespace OMA.FourSiteRanks

theorem fourth_power_fifteen (C : ℕ) (small : C ≤ 15) : ¬ Test 4 C 1 := by
  by_cases h : C ≤ 14
  · exact fourth_power_fourteen C h
  · have : C=15 := by omega
    subst C
    exact fifteen_of_rank_thirty_one OMA.ProductVectors.green_sixteen

end OMA.FourSiteRanks



/- Natural-number coefficient arrays that count the supported paths of a complex restriction.
Scalar extension and the coordinate identification below are adapted from OpenAI's
ScalarExtensionSpectrum.lean and the earlier coordinate port, under the MIT license.
Source: https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/ScalarExtensionSpectrum.lean -/
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical NNReal

namespace SiteTensor

universe v
variable {I K L : Type*} [Fintype I] [CommSemiring K] [CommSemiring L]

/-- Apply a scalar homomorphism at every coefficient in the given format. -/
def Raw.mapScalars (h : K →+* L) (X : Raw.{v} I K) : Raw.{v} I L :=
  ⟨X.Leg, X.finiteLeg, fun a => h (X.coeff a)⟩

/-- The original local restrictions supply local restrictions after applying
the homomorphism to each matrix entry. -/
theorem Raw.mapScalars_restricts (h : K →+* L) {X Y : Raw.{v} I K} (hXY : X.Restricts Y) :
    (X.mapScalars h).Restricts (Y.mapScalars h) := by
  obtain ⟨A, hA⟩ := hXY
  refine ⟨fun i x y => h (A i x y), fun x => ?_⟩
  have t := congrArg h (hA x)
  simp only [map_sum, map_mul, map_prod] at t
  exact t

private theorem map_sumCoeff {A B : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (h : K →+* L) (X : (∀ i, A i) → K) (Y : (∀ i, B i) → K) (a : ∀ i, A i ⊕ B i) :
    h (sumCoeff X Y a) = sumCoeff (fun b => h (X b)) (fun b => h (Y b)) a := by
  simp [sumCoeff, pushCoeff, apply_ite h]

variable [Nonempty I]

/-- Scalar extension on the tensor semiring. -/
noncomputable def mapScalars (h : K →+* L) : TensorClass.{v} I K →+* TensorClass.{v} I L where
  toFun := Quotient.map (Raw.mapScalars h) fun _ _ hXY =>
    ⟨Raw.mapScalars_restricts h hXY.1, Raw.mapScalars_restricts h hXY.2⟩
  map_zero' := Quotient.sound <| Raw.reindex_equivalent (fun _ => Equiv.refl _) (fun _ => h.map_zero)
  map_one' := Quotient.sound <| Raw.reindex_equivalent (fun _ => Equiv.refl _) (fun _ => h.map_one)
  map_mul' x y := Quotient.inductionOn₂ x y fun X Y => Quotient.sound <|
    Raw.reindex_equivalent (fun _ => Equiv.refl _) fun a =>
      map_mul h (X.coeff (fun i => (a i).1)) (Y.coeff (fun i => (a i).2))
  map_add' x y := Quotient.inductionOn₂ x y fun X Y => Quotient.sound <|
    Raw.reindex_equivalent (fun _ => Equiv.refl _) fun a => map_sumCoeff h X.coeff Y.coeff a

@[simp] theorem mapScalars_ofRaw (h : K →+* L) (X : Raw.{v} I K) :
    mapScalars h (ofRaw X) = ofRaw (X.mapScalars h) := rfl

/-- Scalar extension preserves the local restriction order. -/
theorem mapScalars_mono (h : K →+* L) :
    Monotone (mapScalars (I := I) h : TensorClass.{v} I K → TensorClass.{v} I L) := by
  intro x y
  induction x using Quotient.inductionOn
  induction y using Quotient.inductionOn
  exact Raw.mapScalars_restricts h

end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI

namespace OMA.GreenSupport
open OMAPort OMA.PlanarInterval OMA.FourSiteComparison
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical
noncomputable section

abbrev NC := TensorClass.{0} (Fin 4) ℕ
abbrev castClass : NC →+* FourClass := mapScalars (Nat.castRingHom ℂ)
abbrev ind (X : FourTensor) := ∀ i, Fin (X.1 i)
abbrev nr (X : FourTensor) (q : ind X → ℕ) : Raw.{0} (Fin 4) ℕ :=
  ⟨fun i => Fin (X.1 i), fun _ => inferInstance, q⟩

def Model (X : FourTensor) (Z : NC) : Prop :=
  ∃ q : ind X → ℕ, (∀ x, (q x : ℂ) = X.2 x) ∧ ofRaw (nr X q)=Z

theorem Model.cast {X Z} (h : Model X Z) : castClass Z=cls X := by
  obtain ⟨q,val,rfl⟩ := h
  change ofRaw ((nr X q).mapScalars (Nat.castRingHom ℂ))=ofRaw (coordRaw X)
  apply ofRaw_eq_iff.mpr
  exact Raw.reindex_equivalent (X := (nr X q).mapScalars (Nat.castRingHom ℂ))
    (Y := coordRaw X) (fun _ => Equiv.refl _) val

theorem Model.mul {X Y Z W} (h : Model X Z) (g : Model Y W) : Model (sigMul X Y) (Z*W) := by
  obtain ⟨p,hp,rfl⟩ := h
  obtain ⟨q,hq,rfl⟩ := g
  let a (x : ind (sigMul X Y)) := p (fun i => (finProdFinEquiv.symm (x i)).1) * q (fun i => (finProdFinEquiv.symm (x i)).2)
  refine ⟨a,fun _ => by simp only [a,Nat.cast_mul,hp,hq]; rfl,?_⟩
  symm
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent (fun _ => finProdFinEquiv) ?_)
  intro x
  change (∀ i, Fin (X.1 i) × Fin (Y.1 i)) at x
  change p (fun i => (x i).1)*q (fun i => (x i).2) = a (fun i => finProdFinEquiv (x i))
  simp only [a,Equiv.symm_apply_apply]

private theorem add_value (X Y : FourTensor) (x : ∀ i, Fin (X.1 i) ⊕ Fin (Y.1 i)) :
    sumCoeff X.2 Y.2 x = (sigAdd X Y).2 (fun i => finSumFinEquiv (x i)) := by
  classical
  dsimp only [sigAdd]
  by_cases hL : ∀ i, ∃ a, x i = Sum.inl a
  · choose a ha using hL
    obtain rfl : x = fun i => Sum.inl (a i) := funext ha
    rw [sumCoeff_inl, dif_pos (by simpa only [finSumFinEquiv_apply_left, Fin.val_castAdd] using fun i => (a i).isLt)]
    apply congrArg X.2
    funext i
    exact Fin.ext (by simp [finSumFinEquiv_apply_left])
  · by_cases hR : ∀ i, ∃ b, x i = Sum.inr b
    · choose b hb using hR
      obtain rfl : x = fun i => Sum.inr (b i) := funext hb
      have hn : ¬∀ i, (finSumFinEquiv (Sum.inr (b i) : Fin (X.1 i) ⊕ Fin (Y.1 i)) : ℕ) < X.1 i := by
        intro hall
        have h := hall ((0 : Fin 4))
        simpa [finSumFinEquiv_apply_right] using h
      rw [sumCoeff_inr, dif_neg hn, dif_pos (by simp [finSumFinEquiv_apply_right])]
      apply congrArg Y.2
      funext i
      exact Fin.ext (by simp [finSumFinEquiv_apply_right])
    · rw [sumCoeff_mixed]
      · rw [dif_neg, dif_neg]
        · intro hall
          apply hR
          intro i
          have hi := hall i
          cases hx : x i with
          | inl a => simp [hx, finSumFinEquiv_apply_left, a.isLt.not_ge] at hi
          | inr b => exact ⟨b,rfl⟩
        · intro hall
          apply hL
          intro i
          have hi := hall i
          cases hx : x i with
          | inl a => exact ⟨a,rfl⟩
          | inr b => simp [hx, finSumFinEquiv_apply_right] at hi
      · rintro a rfl
        exact hL fun i => ⟨a i,rfl⟩
      · rintro b rfl
        exact hR fun i => ⟨b i,rfl⟩

theorem Model.add {X Y Z W} (h : Model X Z) (g : Model Y W) : Model (sigAdd X Y) (Z+W) := by
  obtain ⟨p,hp,rfl⟩ := h
  obtain ⟨q,hq,rfl⟩ := g
  let a (x : ind (sigAdd X Y)) := sumCoeff p q (fun i => finSumFinEquiv.symm (x i))
  refine ⟨a,?_,?_⟩
  · intro x
    change (∀ i, Fin (X.1 i+Y.1 i)) at x
    have val := add_value X Y (fun i => finSumFinEquiv.symm (x i))
    simp only [Equiv.apply_symm_apply] at val
    rw [←val]
    simp [a,sumCoeff,pushCoeff,←hp,←hq,Nat.cast_ite]
  · symm
    apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent (fun _ => finSumFinEquiv) ?_)
    intro x
    change (∀ i, Fin (X.1 i) ⊕ Fin (Y.1 i)) at x
    change sumCoeff p q x = a (fun i => finSumFinEquiv (x i))
    simp only [a,Equiv.symm_apply_apply]

theorem Model.pow {X Z} (h : Model X Z) (n : ℕ) : Model (power X n) (Z^n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    refine ⟨fun _ => 1,fun _ => by simp [power,unit],?_⟩
    exact ofRaw_eq_iff.mpr (Raw.reindex_equivalent (fun _ => Equiv.equivPUnit (Fin 1)) (fun _ => rfl))
  | succ n ih => simpa [power,pow_succ] using ih.mul h

theorem Model.nsmul {X Z} (h : Model X Z) (n : ℕ) : Model (copies X n) (n • Z) := by
  induction n with
  | zero =>
    rw [zero_nsmul]
    exact ⟨0,fun _ => by simp [copies,null], (ofRaw_eq_zero_iff _).mpr rfl⟩
  | succ n ih => simpa only [copies,succ_nsmul] using ih.add h

theorem wire_model (a b : Fin 4) : ∃ Z, Model (wireCoord a b) Z := by
  let q (x : ind (wireCoord a b)) : ℕ := if (x a).val=(x b).val then 1 else 0
  exact ⟨_,q,fun x => by simp [q,wireCoord],rfl⟩

theorem matching_model (a b c d : Fin 4) : ∃ Z, Model (matching a b c d) Z := by
  obtain ⟨X,h⟩ := wire_model a b
  obtain ⟨Y,g⟩ := wire_model c d
  exact ⟨_,h.mul g⟩

end
end OMA.GreenSupport


/- Splitting a path-count tensor over the naturals preserves its zero entries. -/
namespace OMA.GreenSupport
open OMAPort OMA.PlanarInterval OMA.FourSiteComparison OMA.FourSiteRanks
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical
noncomputable section

local instance : Nonempty {i // leftCut i} := ⟨⟨2,by decide⟩⟩
local instance : Nonempty {i // ¬leftCut i} := ⟨⟨3,by decide⟩⟩
local instance : Nonempty {i // rightCut i} := ⟨⟨2,by decide⟩⟩
local instance : Nonempty {i // ¬rightCut i} := ⟨⟨3,by decide⟩⟩

def Budget (X : NC) (b : ℕ) : Prop := ∃ L R : NC, X=L+R ∧
  cutRank leftCut ℂ (castClass L) + cutRank rightCut ℂ (castClass R) ≤ b

theorem Budget.zero : Budget 0 0 := ⟨0,0,by simp,by simp [cut_zero]⟩
theorem Budget.add {X Y b d} (h : Budget X b) (g : Budget Y d) : Budget (X+Y) (b+d) := by
  obtain ⟨L,R,rfl,f⟩ := h
  obtain ⟨S,T,rfl,t⟩ := g
  exact ⟨L+S,R+T,by ac_rfl,by rw [map_add,map_add,cut_add,cut_add]; omega⟩
theorem Budget.copies {X b} (h : Budget X b) (C : ℕ) : Budget (C • X) (C*b) := by
  induction C with
  | zero => simpa using Budget.zero
  | succ n ih => simpa only [succ_nsmul,Nat.succ_mul] using ih.add h

theorem Budget.sum {J : Type} (s : Finset J) (T : J → NC) (b : J → ℕ)
    (h : ∀ j ∈ s, Budget (T j) (b j)) : Budget (∑ j ∈ s,T j) (∑ j ∈ s,b j) := by
  induction s using Finset.induction_on with
  | empty => simpa using Budget.zero
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj,Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self ..)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem budget_term {X Y : NC} (x : castClass X=V) (y : castClass Y=W) (k i j : ℕ) :
    Budget ((X^k)^i*(Y^k)^j) (min ((4^k)^j) ((4^k)^i)) := by
  by_cases c : ((4:ℕ)^k)^j ≤ (4^k)^i
  · refine ⟨_,0,(add_zero _).symm,?_⟩
    simp only [map_zero,cut_zero,add_zero,min_eq_left c,map_mul,map_pow,x,y,cut_mul,cut_pow]
    simpa only [one_pow,one_mul] using Nat.mul_le_mul
      (Nat.pow_le_pow_left (Nat.pow_le_pow_left left_V k) i)
      (Nat.pow_le_pow_left (Nat.pow_le_pow_left left_W k) j)
  · refine ⟨0,_,(zero_add _).symm,?_⟩
    simp only [map_zero,cut_zero,zero_add,min_eq_right (le_of_not_ge c),map_mul,map_pow,x,y,cut_mul,cut_pow]
    simpa only [one_pow,mul_one] using Nat.mul_le_mul
      (Nat.pow_le_pow_left (Nat.pow_le_pow_left right_V k) i)
      (Nat.pow_le_pow_left (Nat.pow_le_pow_left right_W k) j)

theorem source_budget {X Y : NC} (x : castClass X=V) (y : castClass Y=W) (k n : ℕ) :
    Budget ((X^k+Y^k)^n) (sliceBudget k n) := by
  rw [add_pow]
  unfold sliceBudget
  apply Budget.sum
  intro i _
  simpa only [nsmul_eq_mul,mul_comm (n.choose i : NC)] using
    (budget_term x y k i (n-i)).copies (n.choose i)

/-- Binary direct sum decomposition, specialized to the natural-number semiring.
The block-restriction calculation is the one in StrictSpectralComparison. -/
theorem split_nat (R : Raw.{0} (Fin 4) ℕ) (Y V : NC) (h : ofRaw R ≤ Y+V) :
    ∃ A B : (∀ i,R.Leg i) → ℕ, R.coeff=A+B ∧
      ofRaw {R with coeff := A} ≤ Y ∧ ofRaw {R with coeff := B} ≤ V := by
  induction Y using Quotient.inductionOn with | h Y =>
  induction V using Quotient.inductionOn with | h V =>
  obtain ⟨M,hM⟩ := h
  let image {D : Fin 4 → Type} [∀ i,Fintype (D i)] (v : (∀ i,D i) → ℕ)
      (N : ∀ i,R.Leg i → D i → ℕ) (x : ∀ i,R.Leg i) := ∑ a, v a * ∏ i,N i (x i) (a i)
  let left := fun i x a => M i x (Sum.inl a)
  let right := fun i x a => M i x (Sum.inr a)
  refine ⟨image Y.coeff left,image V.coeff right,?_,⟨left,fun _ => Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) (fun _ _ => rfl)⟩,⟨right,fun _ => Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) (fun _ _ => rfl)⟩⟩
  funext x
  have e : R.coeff x=∑ a,sumCoeff Y.coeff V.coeff a * ∏ i,M i (x i) (a i) :=
    (hM x).trans (Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) (fun _ _ => rfl))
  simp only [sumCoeff,add_mul,Finset.sum_add_distrib,sum_pushCoeff_mul] at e
  apply e.trans
  apply congrArg₂ (· + ·) <;> exact Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) (fun _ _ => rfl)

abbrev dst (k n : ℕ) := power (power (matching 0 1 2 3) k) n
abbrev src (k C n : ℕ) := copies (power (sigAdd (power (matching 0 2 1 3) k)
    (power (matching 0 3 1 2) k)) n) C

theorem source_model (k C n : ℕ) : ∃ Z : NC, Model (src k C n) Z ∧ Budget Z (C*sliceBudget k n) := by
  obtain ⟨X,h⟩ := matching_model 0 2 1 3
  obtain ⟨Y,g⟩ := matching_model 0 3 1 2
  exact ⟨_,(((h.pow k).add (g.pow k)).pow n).nsmul C,(source_budget h.cast g.cast k n).copies C⟩

abbrev Maps (Y X : FourTensor) := ∀ i, Matrix (Fin (Y.1 i)) (Fin (X.1 i)) ℂ

def term {Y X : FourTensor} (M : Maps Y X) (y : ind Y) (z : ind X) : ℂ :=
  (∏ i,M i (y i) (z i))* X.2 z

def count {Y X : FourTensor} (M : Maps Y X) (q : ind X → ℕ) (y : ind Y) : ℕ :=
  ∑ z, q z * ∏ i, if M i (y i) (z i)=0 then 0 else 1

theorem count_support {Y X : FourTensor} (M : Maps Y X) (q : ind X → ℕ)
    (data : ∀ z, (q z : ℂ)=X.2 z) (y : ind Y) :
    count M q y≠0 ↔ ∃ z, term M y z≠0 := by
  simp only [count,ne_eq,Finset.sum_eq_zero_iff_of_nonneg (f:=fun z : ind X => _)
    (fun _ _ => Nat.zero_le _),Finset.mem_univ,true_implies]
  push Not
  apply exists_congr
  intro z
  simp [term,←data z,Finset.prod_eq_zero_iff,mul_eq_zero,or_comm]

theorem count_class_le {Y X : FourTensor} (M : Maps Y X) (q : ind X → ℕ) :
    ofRaw (nr Y (count M q)) ≤ ofRaw (nr X q) := by
  exact ⟨fun i y z => if M i y z = 0 then 0 else 1,fun _ => Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) (fun _ _ => rfl)⟩

/-- The two rank-controlled summands here count actual paths in the original coefficient formula. -/
theorem count_split {k C n : ℕ} (M : Maps (dst k n) (src k C n)) :
    ∃ (q : ind (src k C n) → ℕ) (a b : ind (dst k n) → ℕ),
      (∀ z,(q z : ℂ)=(src k C n).2 z) ∧ count M q=a+b ∧
      cutRank leftCut ℂ (castClass (ofRaw (nr (dst k n) a))) +
      cutRank rightCut ℂ (castClass (ofRaw (nr (dst k n) b))) ≤ C*sliceBudget k n := by
  obtain ⟨Z,⟨q,data,eq⟩,⟨L,R,split,cap⟩⟩ := source_model k C n
  obtain ⟨a,b,total,left,right⟩ := split_nat _ L R ((count_class_le M q).trans_eq (eq.trans split))
  refine ⟨q,a,b,data,total,?_⟩
  apply le_trans (Nat.add_le_add (monotone_cutRank leftCut ℂ (mapScalars_mono (Nat.castRingHom ℂ) left))
    (monotone_cutRank rightCut ℂ (mapScalars_mono (Nat.castRingHom ℂ) right))) cap

end
end OMA.GreenSupport


/- Count distinct target zeros at which a local restriction must cancel nonzero terms. -/
namespace OMA.GreenSupport
open OMAPort OMA.PlanarInterval OMA.FourSiteComparison OMA.FourSiteRanks
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical
noncomputable section

abbrev P (N : ℕ) := Fin N × Fin N
abbrev sw {N : ℕ} (p : P N) : P N := (p.2,p.1)
abbrev NatMat (N : ℕ) := Matrix (P N) (P N) ℕ
abbrev cmat {N : ℕ} (f : NatMat N) : SwapMatrix N := fun p q => (f p q : ℂ)

def bad {N : ℕ} (f : NatMat N) : Finset (P N × P N) :=
  Finset.univ.filter fun z => z.2≠sw z.1 ∧ f z.1 z.2≠0

def weighted {N : ℕ} (f : NatMat N) : SwapMatrix N :=
  fun p q => if q=sw p then (f p q : ℂ) else 0

theorem weighted_rank {N : ℕ} (f : NatMat N) (pos : ∀ p, f p (sw p)≠0) :
    (weighted f).rank=N^2 := by
  let e := Equiv.prodComm (Fin N) (Fin N)
  let d (p : P N) : ℂ := f (sw p) p
  have eq : weighted f=(Matrix.diagonal d).submatrix e (Equiv.refl _) := by
    ext p q
    by_cases h : q=sw p
    · subst q; rcases p with ⟨x,y⟩; simp [weighted,Matrix.submatrix,Matrix.diagonal,e,d,sw]
    · have g : e p≠q := Ne.symm h
      simp [weighted,h,Matrix.submatrix,Matrix.diagonal, g]
  have nozero (p : P N) : d p≠0 := by
    change (f (sw p) p : ℂ) ≠ 0
    exact_mod_cast pos (sw p)
  rw [eq,Matrix.rank_submatrix,Matrix.rank_diagonal]
  simp [nozero,Fintype.card_prod,pow_two]

/-- The weighted diagonal of the natural path-count matrix has full rank.
Each leaked entry can affect at most two rows after realignment. -/
theorem count_rank {N : ℕ} (f a b : NatMat N) (total : ∀ p q, f p q=a p q+b p q)
    (pos : ∀ p,f p (sw p)≠0) :
    N^2 ≤ (cmat a).rank+(SwapSplit.realign (cmat b)).rank+2*(bad f).card := by
  let S := bad f
  let cross (z : P N × P N) := (z.1.1,z.2.1)
  let rows := S.image Prod.fst ∪ S.image cross
  let J := cmat a + SwapSplit.realign (cmat b)
  have support : (weighted f-J).rank ≤ rows.card := by
    apply Matrix.rank_le_card_of_support_subset
    rw [Function.support_subset_iff']
    rintro ⟨x,y⟩ absent
    funext ⟨u,v⟩
    change (if (u,v)=(y,x) then (f (x,y) (u,v):ℂ) else 0) -
      ((a (x,y) (u,v):ℂ)+(b (x,u) (y,v):ℂ)) = 0
    by_cases h : (u,v)=(y,x)
    · obtain ⟨rfl,rfl⟩ := Prod.ext_iff.mp h
      simp only [if_true, sub_eq_zero]
      exact_mod_cast total (v,u) (u,v)
    · rw [if_neg h]
      have za : f (x,y) (u,v)=0 := by
        by_contra nz
        have mem : ((x,y),(u,v))∈S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h,nz⟩
        exact absent (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_,mem,rfl⟩))
      have zb : f (x,u) (y,v)=0 := by
        by_contra nz
        have nh : (y,v)≠(u,x) := by simpa [Prod.ext_iff,eq_comm] using h
        have mem : ((x,u),(y,v))∈S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,nh,nz⟩
        exact absent (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,mem,rfl⟩))
      have e := total (x,y) (u,v)
      have g := total (x,u) (y,v)
      rw [show a (x,y) (u,v)=0 by omega,show b (x,u) (y,v)=0 by omega]
      simp
  have rowsize := (Finset.card_union_le (S.image Prod.fst) (S.image cross)).trans
    (Nat.add_le_add (Finset.card_image_le (f:=Prod.fst)) (Finset.card_image_le (f:=cross)))
  calc
    N^2 = (weighted f).rank := (weighted_rank f pos).symm
    _ = (J+(weighted f-J)).rank := congrArg Matrix.rank (by abel)
    _ ≤ J.rank+(weighted f-J).rank := SwapSplit.rank_add_le' _ _
    _ ≤ _ := Nat.add_le_add (SwapSplit.rank_add_le' _ _) (support.trans (by simpa [rows,S,two_mul] using rowsize))

end
end OMA.GreenSupport


/- Count distinct target zeros at which a local restriction must cancel nonzero terms. -/
namespace OMA.GreenSupport
open OMAPort OMA.PlanarInterval OMA.FourSiteComparison OMA.FourSiteRanks
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical
noncomputable section

def interference {Y X : FourTensor} (M : Maps Y X) : Finset (ind Y) :=
  Finset.univ.filter fun y => Y.2 y=0 ∧ ∃ z w, z≠w ∧ term M y z≠0 ∧ term M y w≠0

private theorem two_terms {Y X : FourTensor} (M : Maps Y X) {y : ind Y}
    (res : Y.2 y=∑ z,term M y z) (zero : Y.2 y=0) (nz : ∃ z,term M y z≠0) :
    y ∈ interference M := by
  obtain ⟨z,hz⟩ := nz
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,zero,z,?_⟩
  by_contra! onlyTerm
  have single : (∑ t,term M y t)=term M y z :=
    Finset.sum_eq_single z (fun t _ h => onlyTerm t (Ne.symm h) hz) (by simp)
  exact hz (single.symm.trans (res.symm.trans zero))

private theorem grid_inj {Y : FourTensor} {N : ℕ} (g : ∀ i,Fin N → (coordRaw Y).Leg i)
    (hg : ∀ z : Fin 4 → Fin N, Y.2 (fun i => g i (z i)) = if pairCondition z then 1 else 0)
    (i : Fin 4) : Function.Injective (g i) := by
  intro a b eq
  let z := Function.update (fun _ : Fin 4 => a) i b
  have same : (fun j => g j (z j))=fun j => g j a := by
    funext j
    by_cases h : j=i
    · subst j; simpa [z] using eq.symm
    · simp [z,Function.update_of_ne h]
  have one := hg (fun _ => a)
  have hz := hg z
  rw [same,one,if_pos (by exact ⟨rfl,rfl⟩)] at hz
  have pair : pairCondition z := by
    by_contra h
    rw [if_neg h] at hz
    exact one_ne_zero hz
  fin_cases i <;> simp [z,pairCondition,Function.update] at pair <;> tauto

/-- Every local restriction must cancel terms at this many distinct target zeros. -/
theorem actual_interference_bound {k C n : ℕ} (M : Maps (dst k n) (src k C n))
    (res : ∀ y,(dst k n).2 y=∑ z,term M y z) :
    ((2^k)^n)^2 ≤ C*sliceBudget k n+2*(interference M).card := by
  let N := (2^k)^n
  let Y := dst k n
  obtain ⟨g,hg⟩ := (matching_grid.power k).power n
  let pt (v : P N × P N) : ind Y := fun i => g i (reindexFour v.1 v.2 i)
  have inj : Function.Injective pt := by
    rintro ⟨⟨x,y⟩,⟨u,v⟩⟩ ⟨⟨a,b⟩,⟨c,d⟩⟩ h
    have hi (i : Fin 4) := grid_inj g hg i (congrFun h i)
    have A : x=a := hi 0
    have B : y=b := hi 2
    have D : v=d := hi 1
    have E : u=c := hi 3
    simp [A,B,D,E]
  have val (p q : P N) : Y.2 (pt (p,q))=if q=sw p then 1 else 0 := by
    have h := congrFun (congrFun (grid_matrix_swap g hg) p) q
    simpa [gridMatrix,pt,SwapSplit.swapMat,sw,Prod.ext_iff,eq_comm,and_comm] using h
  obtain ⟨m,a,b,data,total,cap⟩ := count_split M
  let F : NatMat N := fun p q => count M m (pt (p,q))
  let A : NatMat N := fun p q => a (pt (p,q))
  let B : NatMat N := fun p q => b (pt (p,q))
  have pos (p : P N) : F p (sw p)≠0 := by
    apply (count_support M m data _).mpr
    by_contra! none
    have h := res (pt (p,sw p))
    rw [val,if_pos rfl] at h
    simp [none] at h
  have rg := count_rank F A B (fun p q => congrFun total (pt (p,q))) pos
  let j : Fin N := ⟨0,by dsimp [N]; positivity⟩
  have cost : (cmat A).rank+(SwapSplit.realign (cmat B)).rank ≤ C*sliceBudget k n :=
    (Nat.add_le_add
      (grid_left_le j ((nr Y a).mapScalars (Nat.castRingHom ℂ)) g)
      (grid_right_le j ((nr Y b).mapScalars (Nat.castRingHom ℂ)) g)).trans cap
  have sub : (bad F).image pt ⊆ interference M := by
    intro y hy
    obtain ⟨⟨p,q⟩,hz,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨_,neq,nz⟩ := Finset.mem_filter.mp hz
    apply two_terms M (res _) (by rw [val,if_neg neq])
    exact (count_support M m data _).mp nz
  have card := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ inj] at card
  exact rg.trans (Nat.add_le_add cost (Nat.mul_le_mul_left 2 card))

theorem half_actual_interference {C n : ℕ} (many : 2*C≤8^n) (M : Maps (dst 4 n) (src 4 C n))
    (res : ∀ y,(dst 4 n).2 y=∑ z,term M y z) :
    ((2^4)^n)^2 ≤ 4*(interference M).card := by
  have cap : 2*(C*sliceBudget 4 n) ≤ ((2^4)^n)^2 := calc
    _ = (2*C)*sliceBudget 4 n := (Nat.mul_assoc ..).symm
    _ ≤ 8^n*32^n := Nat.mul_le_mul many (budget_four n)
    _ = _ := swap_square_capacity n
  have h := actual_interference_bound M res
  omega

theorem sixteen_squared_interference (M : Maps (dst 4 2) (src 4 16 2))
    (res : ∀ y,(dst 4 2).2 y=∑ z,term M y z) : 28656 ≤ (interference M).card := by
  have h := actual_interference_bound M res
  rw [show sliceBudget 4 2=514 by decide] at h
  norm_num at h
  omega

end
end OMA.GreenSupport


/- Any restriction with many cancelling outputs has many negative real inner
products between actual source contributions. This rules out all nonnegative
local restrictions at a tensor power depending on the number of copies. -/
namespace OMA.GreenSupport
open OMAPort OMA.PlanarInterval OMA.FourSiteComparison OMA.FourSiteRanks
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical
noncomputable section

/-- Count target zeros with two terms more than a right angle apart. -/
def phaseConflict {Y X : FourTensor} (M : Maps Y X) : Finset (ind Y) :=
  Finset.univ.filter fun y => Y.2 y=0 ∧ ∃ z w,
    (term M y w * (starRingEnd ℂ) (term M y z)).re<0

theorem interference_phases {Y X : FourTensor} (M : Maps Y X)
    (res : ∀ y,Y.2 y=∑ z,term M y z) : interference M ⊆ phaseConflict M := by
  intro y hy
  obtain ⟨_,zero,z,w,_,hz,_⟩ := Finset.mem_filter.mp hy
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,zero,z,?_⟩
  by_contra! compatible
  let x := term M y z
  have strict : 0 < (term M y z*(starRingEnd ℂ) x).re := by
    rw [show (term M y z)*(starRingEnd ℂ) x=(Complex.normSq x:ℂ) from Complex.mul_conj x]
    exact Complex.normSq_pos.mpr hz
  have sumPos := strict.trans_le (Finset.single_le_sum
    (f:=fun t => (term M y t*(starRingEnd ℂ) x).re)
    (fun t _ => compatible t) (Finset.mem_univ z))
  rw [←Complex.re_sum,←Finset.sum_mul,←res,zero,zero_mul,Complex.zero_re] at sumPos
  exact lt_irrefl _ sumPos

theorem all_copy_phase_bound (C : ℕ) :
    ∃ n : ℕ,0<n ∧ ∀ M : Maps (dst 4 n) (src 4 C n),
      (∀ y,(dst 4 n).2 y=∑ z,term M y z) → ((2^4)^n)^2 ≤ 4*(phaseConflict M).card := by
  let n := C+1
  have h : C+1 < (2:ℕ)^(C+1) := Nat.lt_two_pow_self
  have ge : 2^(C+1)*2 ≤ (8:ℕ)^n := by
    change 2^(C+1)*2 ≤ 8^(C+1)
    have u := Nat.pow_le_pow_left (by decide : 2 ≤ 8) C
    rw [pow_succ,pow_succ]
    omega
  refine ⟨n,by dsimp [n]; omega,?_⟩
  intro M res
  exact (half_actual_interference (by omega) M res).trans
    (Nat.mul_le_mul_left 4 (Finset.card_le_card (interference_phases M res)))

/-- The restriction tested on the desk with the additional requirement that
its local matrices have nonnegative real entries. -/
def NonnegativeTest (k C n : ℕ) : Prop :=
  let Y := dst k n
  let X := src k C n
  ∃ R : ∀ i, Matrix (Fin (Y.1 i)) (Fin (X.1 i)) ℝ,
    (∀ i u v,0≤R i u v) ∧ ∀ y,Y.2 y=∑ z,term (Y:=Y) (X:=X) (fun i u v => (R i u v : ℂ)) y z

theorem nonnegative_copy_floor {C n : ℕ} (h : NonnegativeTest 4 C n) : 8^n≤C := by
  obtain ⟨R,nonneg,res⟩ := h
  let Y := dst 4 n
  let X := src 4 C n
  let M : Maps Y X := fun i u v => (R i u v : ℂ)
  obtain ⟨_,⟨q,data,_⟩,_⟩ := source_model 4 C n
  let t (y : ind Y) (z : ind X) : ℝ := (∏ i,R i (y i) (z i))*(q z : ℝ)
  have hnneg (y z) : 0≤t y z := mul_nonneg (Finset.prod_nonneg (fun i _ => nonneg i _ _)) (Nat.cast_nonneg _)
  have eq (y z) : term M y z = (t y z : ℂ) := by
    simp only [term,t,M,Complex.ofReal_mul,Complex.ofReal_prod,Complex.ofReal_natCast]
    exact congrArg (_ * ·) (data z).symm
  have empty : phaseConflict M=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    obtain ⟨_,_,z,w,neg⟩ := Finset.mem_filter.mp hy
    rw [eq,eq] at neg
    simp only [Complex.conj_ofReal,←Complex.ofReal_mul,Complex.ofReal_re] at neg
    exact (not_lt_of_ge (mul_nonneg (hnneg y w) (hnneg y z))) neg
  have no := Finset.card_le_card (interference_phases M res)
  rw [empty,Finset.card_empty] at no
  have cap := actual_interference_bound M res
  rw [Nat.eq_zero_of_le_zero no,mul_zero,add_zero,←swap_square_capacity] at cap
  have le := cap.trans (Nat.mul_le_mul_left C (budget_four n))
  exact Nat.le_of_mul_le_mul_right le (by positivity)

theorem every_copy_excludes_nonnegative (C : ℕ) : ∃ n : ℕ,0<n ∧ ¬NonnegativeTest 4 C n := by
  refine ⟨C+1,by omega,?_⟩
  intro h
  have floor := nonnegative_copy_floor h
  have ge := Nat.pow_le_pow_left (by decide : 2 ≤ 8) (C+1)
  have gt : C+1 < (2:ℕ)^(C+1) := Nat.lt_two_pow_self
  omega

end
end OMA.GreenSupport


/- A balanced word in the two source matchings can route a full wire.
Its central binomial multiplicity gives an explicit restriction at every even power. -/
namespace OMA.GreenRouting
open OMAPort OMA.PlanarInterval OMA.FourSiteComparison OMA.FourSiteRanks
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical
noncomputable section

abbrev wc (a b : Fin 4) := cls (wireCoord a b)
abbrev loc (a b i : Fin 4) := Fin ((wireCoord a b).1 i)
abbrev ep (a b i : Fin 4) := (i=a → Fin 2) × (i=b → Fin 2)

private def digit {a b i : Fin 4} (h : i=a ∨ i=b) (t : loc a b i) : Fin 2 :=
  ⟨t.val,by simpa [wireCoord,h] using t.isLt⟩

private def endpoints (a b i : Fin 4) (x : loc a b i) : ep a b i :=
  (fun e => digit (Or.inl e) x,fun e => digit (Or.inr e) x)

private def legEquiv (a b i : Fin 4) (diff : a≠b) : loc a b i ≃ ep a b i :=
  Equiv.ofBijective (endpoints a b i) (by
    constructor
    · intro x y eq
      apply Fin.ext
      by_cases ha : i=a
      · exact congrArg (fun t : Fin 2 => t.val) (congrFun (congrArg Prod.fst eq) ha)
      by_cases hb : i=b
      · exact congrArg (fun t : Fin 2 => t.val) (congrFun (congrArg Prod.snd eq) hb)
      have hx := x.isLt
      have hy := y.isLt
      simp [wireCoord,ha,hb] at hx hy
      omega
    · rintro ⟨x,y⟩
      by_cases ha : i=a
      · subst i
        refine ⟨⟨(x rfl).val,by simpa [wireCoord] using (x rfl).isLt⟩,Prod.ext (funext fun _ => Fin.ext rfl) (funext fun h => (diff h).elim)⟩
      by_cases hb : i=b
      · subst i
        refine ⟨⟨(y rfl).val,by simpa [wireCoord] using (y rfl).isLt⟩,Prod.ext (funext fun h => (ha h).elim) (funext fun _ => Fin.ext rfl)⟩
      exact ⟨⟨0,by simp [wireCoord,ha,hb]⟩,Prod.ext (funext fun h => (ha h).elim) (funext fun h => (hb h).elim)⟩)

abbrev D := Raw.diagonal (Fin 2) ℂ (Fin 2)

theorem wire_group (a b : Fin 4) (diff : a≠b) : wc a b=ofRaw (D.group ![a,b]) := by
  rw [← Raw.ofRaw_endpointMatrix_diagonal (K:=ℂ) a b (Fin 2)]
  apply ofRaw_eq_iff.mpr
  apply Raw.reindex_equivalent (X:=coordRaw (wireCoord a b))
    (Y:=Raw.endpointMatrix a b (Fin 2) (Fin 2) (fun x y => @ite ℂ (x=y) (Classical.propDecidable _) 1 0)) (fun i => legEquiv a b i diff)
  intro x
  change (if (x a).val=(x b).val then (1:ℂ) else 0) =
    @ite ℂ (digit (Or.inl rfl) (x a)=digit (Or.inr rfl) (x b)) (Classical.propDecidable _) 1 0
  simp only [Fin.ext_iff,digit]

private theorem triangle (a b c : Fin 4) (ab : a≠b) (ac : a≠c) (bc : b≠c) :
    wc a c ≤ wc a b * wc c b := by
  rw [wire_group a c ac,wire_group a b ab,wire_group c b bc.symm]
  rw [← ofRaw_eq_iff.mpr (Raw.grouped_wire_symm ℂ (Fin 2) b c),←ofRaw_mul]
  apply ofRaw_le_iff.mpr
  exact Raw.move_restricts_with_wire D ![a,b] ![a,c] 1 (by intro i hi; fin_cases i <;> simp_all)

private theorem matching_cls (a b c d : Fin 4) : cls (matching a b c d) = wc a b * wc c d := by
  change ofRaw (coordRaw (sigMul _ _)) = _
  rw [coord_mul,ofRaw_mul]

theorem paired_paths : (wc 0 1)^2 ≤ V*W := by
  have p := triangle 0 2 1 (by decide) (by decide) (by decide)
  have q := triangle 0 3 1 (by decide) (by decide) (by decide)
  rw [show V = wc 0 2 * wc 1 3 from matching_cls 0 2 1 3,
    show W = wc 0 3 * wc 1 2 from matching_cls 0 3 1 2,pow_two]
  exact (mul_mono p q).trans_eq (by ac_rfl)

private theorem powMono {A B : FourClass} (le : A≤B) (m : ℕ) : A^m≤B^m := by
  induction m with
  | zero => simp
  | succ m ih => simpa only [pow_succ] using mul_mono ih le

private theorem castMono {a b : ℕ} (le : a≤b) : (a : FourClass) ≤ b := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le le
  rw [Nat.cast_add]
  exact le_add_of_nonneg_right (zero_le_tensor _)

/-- With C times the central binomial coefficient at least the wire dimension,
the source realizes the target by routing through the opposite matching. -/
theorem even_routing {k C m : ℕ} (enough : (2^k)^(2*m)≤C*((2*m).choose m)) :
    Test k C (2*m) := by
  apply class_le_test
  rw [cls_pow,cls_pow,matching_cls,nsmul_eq_mul]
  let v := (V^k)^m
  let w := (W^k)^m
  have x : ((wc 0 1)^k)^(2*m) ≤ v*w := by
    have path := powMono paired_paths (k*m)
    convert path using 1 <;> simp only [←pow_mul,mul_pow,v,w] <;> ring_nf
  have y := powMono (powMono (wire_le_two 2 3) k) (2*m)
  have term : ((2*m).choose m : FourClass)*(v*w) ≤ (V^k+W^k)^(2*m) := by
    rw [add_pow]
    have h := Finset.single_le_sum (f:=fun i => (V^k)^i*(W^k)^(2*m-i)*((2*m).choose i : FourClass))
      (fun i _ => zero_le_tensor _) (Finset.mem_range.mpr (by omega : m<2*m+1))
    simpa only [show 2*m-m=m by omega,v,w,mul_comm ((2*m).choose m : FourClass)] using h
  have z := castMono enough
  push_cast at z
  calc
    _ = ((wc 0 1)^k)^(2*m)*((wc 2 3)^k)^(2*m) := by simp only [mul_pow]
    _ ≤ (v*w)*(((2 : FourClass)^k)^(2*m)) := mul_mono x y
    _ ≤ (v*w)*((C:FourClass)*((2*m).choose m:FourClass)) := mul_mono (le_refl _) z
    _ = (C:FourClass)*(((2*m).choose m:FourClass)*(v*w)) := by ac_rfl
    _ ≤ _ := mul_mono (le_refl _) term

theorem even_four_copies (m C : ℕ) (enough : (2*m+1)*8^(2*m)≤C) :
    Test 4 C (2*m) := by
  apply even_routing
  calc
    (2^4)^(2*m) = 8^(2*m)*4^m := by rw [pow_mul,pow_mul,←mul_pow]; rfl
    _ ≤ 8^(2*m)*((2*m+1)*((2*m).choose m)) :=
      Nat.mul_le_mul_left _ (Nat.four_pow_le_two_mul_add_one_mul_central_binom m)
    _ = ((2*m+1)*8^(2*m))*((2*m).choose m) := by ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right _ enough

theorem two_factors_available (C : ℕ) (h : 128≤C) : Test 4 C 2 := by
  apply even_routing (m:=1)
  norm_num
  omega

end
end OMA.GreenRouting


/- Four complex local maps acting on real tensors can be replaced by eight
real local restrictions. The constant is independent of the tensor power. -/
namespace OMA.GreenSupport
open OMAPort OMA.PlanarInterval OMA.FourSiteComparison OMA.FourSiteRanks
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical
noncomputable section

abbrev rawR (X : FourTensor) : Raw.{0} (Fin 4) ℝ :=
  ⟨fun i => Fin (X.1 i),fun _ => inferInstance,fun z => (X.2 z).re⟩
abbrev RC := TensorClass.{0} (Fin 4) ℝ
abbrev rcls (X : FourTensor) : RC := ofRaw (rawR X)
abbrev toR : NC →+* RC := mapScalars (Nat.castRingHom ℝ)

theorem Model.real_class {X Z} (h : Model X Z) : toR Z=rcls X := by
  obtain ⟨q,val,rfl⟩ := h
  apply ofRaw_eq_iff.mpr
  apply Raw.reindex_equivalent (X := (nr X q).mapScalars (Nat.castRingHom ℝ))
    (Y := rawR X) (fun _ => Equiv.refl _)
  intro x
  exact_mod_cast congrArg Complex.re (val x)

private theorem Model.real_data {X Z} (h : Model X Z) (x : ind X) :
    ((X.2 x).re : ℂ) = X.2 x := by
  obtain ⟨q,val,_⟩ := h
  rw [← val x]
  simp

private theorem real_copies {X Z} (h : Model X Z) (C : ℕ) : rcls (copies X C)=C • rcls X := by
  rw [←(h.nsmul C).real_class,←h.real_class,map_nsmul]

private theorem real_source_eight (k C n : ℕ) :
    rcls (src k (8*C) n) = 8 • rcls (src k C n) := by
  obtain ⟨_,a⟩ := matching_model 0 2 1 3
  obtain ⟨_,b⟩ := matching_model 0 3 1 2
  have h := ((a.pow k).add (b.pow k)).pow n
  exact (real_copies h (8*C)).trans ((smul_smul (8:ℕ) C _).symm.trans (congrArg (fun t : RC => 8 • t) (real_copies h C).symm))

private def mask : Fin 8 → Fin 4 → Bool :=
  ![![false,false,false,false],![true,true,false,false],![true,false,true,false],
    ![true,false,false,true],![false,true,true,false],![false,true,false,true],
    ![false,false,true,true],![true,true,true,true]]

private def component (j : Fin 8) (i : Fin 4) (x : ℂ) : ℝ :=
  (if i=0 ∧ j≠0 ∧ j≠7 then -1 else 1) * (if mask j i then x.im else x.re)

private theorem component_sum (x : Fin 4 → ℂ) :
    (∏ i,x i).re=∑ j : Fin 8,∏ i,component j i (x i) := by
  simp [Fin.sum_univ_succ,Fin.prod_univ_four,component,mask,Complex.mul_re,Complex.mul_im]
  <;> ring

/-- The registered restriction formula with the same standard bases over the reals. -/
def RealTest (k C n : ℕ) : Prop := rcls (dst k n) ≤ rcls (src k C n)

theorem realTest_coordinates {k C n} : RealTest k C n ↔
    ∃ M : ∀ i, Matrix (Fin ((dst k n).1 i)) (Fin ((src k C n).1 i)) ℝ,
      ∀ y,((dst k n).2 y).re = ∑ z, (∏ i,M i (y i) (z i))*((src k C n).2 z).re := by
  change (rawR (dst k n)).Restricts (rawR (src k C n)) ↔ _
  constructor <;> rintro ⟨M,e⟩ <;> refine ⟨M,fun y => (e y).trans ?_⟩ <;>
    exact Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) (fun _ _ => mul_comm ..)

/-- Real restrictions are complex restrictions with the same copy count. -/
theorem complex_of_realTest {k C n : ℕ} (h : RealTest k C n) : Test k C n := by
  obtain ⟨M,res⟩ := realTest_coordinates.mp h
  obtain ⟨_,hx,_⟩ := source_model k C n
  obtain ⟨_,hy⟩ := matching_model 0 1 2 3
  have dstReal := (hy.pow k).pow n
  refine ⟨fun i u v => (M i u v : ℂ),fun y => ?_⟩
  have e := congrArg Complex.ofReal (res y)
  simpa only [Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_prod,Model.real_data hx,
    Model.real_data dstReal] using e

/-- Taking the real part of the four local factors uses precisely the eight
even choices of imaginary factors. Each choice is absorbed into a direct summand. -/
theorem realTest_of_complex {k C n : ℕ} (h : Test k C n) : RealTest k (8*C) n := by
  obtain ⟨M,res⟩ := h
  let Y := dst k n
  let X := src k C n
  obtain ⟨_,hx,_⟩ := source_model k C n
  let T (j : Fin 8) (y : ind Y) := ∑ z : ind X, (X.2 z).re * ∏ i,component j i (M i (y i) (z i))
  have total : (rawR Y).coeff=∑ j,T j := by
    funext y
    have e := congrArg Complex.re (res y)
    change (Y.2 y).re = _ at e ⊢
    rw [e,Complex.re_sum,Finset.sum_apply]
    unfold T
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    have eq := hx.real_data z
    change _ = ∑ j,(X.2 z).re * _
    rw [←Finset.mul_sum,←component_sum]
    change ((_ * (X.2 z))).re = (X.2 z).re * _
    rw [←eq,Complex.re_mul_ofReal,Complex.ofReal_re,mul_comm]
  have one (j : Fin 8) : ofCoeffs (T j) ≤ rcls X := by
    apply ofRaw_le_iff.mpr
    refine ⟨fun i u v => component j i (M i u v),fun y => ?_⟩
    exact Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) (fun _ _ => rfl)
  change rcls Y ≤ rcls (src k (8*C) n)
  rw [real_source_eight]
  change ofCoeffs (rawR Y).coeff ≤ _
  rw [total]
  apply (ordinary_sum_le T).trans
  exact (Finset.sum_le_sum (fun j _ => one j)).trans_eq (by simp [X])

/-- At fixed k, ruling out every uniform real copy count is equivalent to
ruling out every uniform complex copy count. No sign restriction is imposed. -/
theorem all_copy_real_iff (k : ℕ) :
    (∀ C : ℕ,0<C → ∃ n : ℕ,0<n ∧ ¬Test k C n) ↔
    (∀ C : ℕ,0<C → ∃ n : ℕ,0<n ∧ ¬RealTest k C n) := by
  constructor
  · intro fail C hC
    obtain ⟨n,hn,h⟩ := fail C hC
    exact ⟨n,hn,fun r => h (complex_of_realTest r)⟩
  · intro fail C hC
    obtain ⟨n,hn,h⟩ := fail (8*C) (by positivity)
    exact ⟨n,hn,fun r => h (realTest_of_complex r)⟩

theorem remaining_iff_signed_real :
    (∀ C : ℕ,16≤C → ∃ n : ℕ,0<n ∧ ¬Test 4 C n) ↔
    (∀ C : ℕ,16≤C → ∃ n : ℕ,0<n ∧ ¬RealTest 4 (8*C) n) := by
  constructor
  · intro fail C large
    obtain ⟨n,hn,h⟩ := fail (8*C) (by omega)
    exact ⟨n,hn,fun real => h (complex_of_realTest real)⟩
  · intro fail C large
    obtain ⟨n,hn,h⟩ := fail C large
    exact ⟨n,hn,fun complex => h (realTest_of_complex complex)⟩

end
end OMA.GreenSupport



/- A fixed number of nonnegative real restrictions suffices on each side
of a difference. Failure for all copy counts is exactly preserved. -/
namespace OMA.GreenSupport
open OMAPort OMA.PlanarInterval OMA.FourSiteComparison OMA.FourSiteRanks
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical
noncomputable section

abbrev MapsR (Y X : FourTensor) := ∀ i,Matrix (Fin (Y.1 i)) (Fin (X.1 i)) ℝ
def imageR {Y X : FourTensor} (M : MapsR Y X) (y : ind Y) : ℝ :=
  ∑ z : ind X,(∏ i,M i (y i) (z i))*(X.2 z).re

/-- In each output coefficient, the positive sum exceeds the negative sum by
exactly the target value. Both families have eight nonnegative local maps. -/
def DifferenceTest (k C n : ℕ) : Prop :=
  let Y := dst k n
  let X := src k C n
  ∃ P Q : Fin 8 → MapsR Y X,
    (∀ j i u v,0≤P j i u v) ∧ (∀ j i u v,0≤Q j i u v) ∧ ∀ y,
      (Y.2 y).re + ∑ j,imageR (Q j) y = ∑ j,imageR (P j) y

private def evenBits : Fin 8 → Fin 4 → Bool :=
  ![![false,false,false,false],![true,true,false,false],![true,false,true,false],
    ![true,false,false,true],![false,true,true,false],![false,true,false,true],
    ![false,false,true,true],![true,true,true,true]]
private def pick (odd : Bool) (j : Fin 8) (i : Fin 4) (p q : ℝ) :=
  if (if i=0 ∧ odd=true then !(evenBits j i) else evenBits j i) then q else p

private theorem four_factors (a b : Fin 4 → ℝ) :
    (∏ i,(a i-b i)) + (∑ j : Fin 8,∏ i,pick true j i (a i) (b i)) =
    ∑ j : Fin 8,∏ i,pick false j i (a i) (b i) := by
  simp [Fin.sum_univ_succ,Fin.prod_univ_four,pick,evenBits]
  <;> ring

private def part (odd : Bool) (j : Fin 8) (i : Fin 4) (x : ℝ) :=
  pick odd j i (max x 0) (max (-x) 0)
private theorem part_nonneg (odd j i x) : 0≤part odd j i x := by
  unfold part pick
  split_ifs <;> exact le_max_right _ _
private theorem parts (x : Fin 4 → ℝ) :
    (∏ i,x i) + (∑ j : Fin 8,∏ i,part true j i (x i)) = ∑ j : Fin 8,∏ i,part false j i (x i) := by
  have sub (z : ℝ) : max z 0-max (-z) 0=z := by rcases le_total 0 z with h|h <;> simp_all
  simpa only [part,sub] using four_factors (fun i => max (x i) 0) (fun i => max (-(x i)) 0)

theorem difference_of_realTest {k C n : ℕ} (h : RealTest k C n) : DifferenceTest k C n := by
  obtain ⟨M,res⟩ := realTest_coordinates.mp h
  let R (odd : Bool) (j : Fin 8) : MapsR (dst k n) (src k C n) := fun i u v => part odd j i (M i u v)
  refine ⟨R false,R true,fun j i u v => part_nonneg ..,fun j i u v => part_nonneg ..,?_⟩
  intro y
  rw [res]
  unfold imageR
  rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun (j : Fin 8) (z : ind (src k C n)) => (∏ i,R true j i (y i) (z i))*((src k C n).2 z).re),
    Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun (j : Fin 8) (z : ind (src k C n)) => (∏ i,R false j i (y i) (z i))*((src k C n).2 z).re),
    ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  rw [←Finset.sum_mul,←Finset.sum_mul,←add_mul]
  exact congrArg (· * _) (parts (fun i => M i (y i) (z i)))

private theorem real_source_mul (a k C n : ℕ) : rcls (src k (a*C) n)=a • rcls (src k C n) := by
  obtain ⟨_,h⟩ := matching_model 0 2 1 3
  obtain ⟨_,g⟩ := matching_model 0 3 1 2
  have model := ((h.pow k).add (g.pow k)).pow n
  rw [←(model.nsmul (a*C)).real_class,←(model.nsmul C).real_class,map_nsmul,map_nsmul,smul_smul]

private theorem real_of_sum {J : Type} [Fintype J] {k C n : ℕ}
    (R : J → MapsR (dst k n) (src k C n))
    (sum : ∀ y,((dst k n).2 y).re=∑ j,imageR (R j) y) : RealTest k (Fintype.card J*C) n := by
  let T := fun j => imageR (R j)
  have total : (rawR (dst k n)).coeff=∑ j,T j := by
    funext y
    simpa only [Finset.sum_apply] using sum y
  have each (j) : ofCoeffs (T j)≤rcls (src k C n) := by
    apply ofRaw_le_iff.mpr
    exact ⟨R j,fun y => Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) (fun _ _ => mul_comm ..)⟩
  change rcls _ ≤ _
  rw [real_source_mul]
  change ofCoeffs (rawR _).coeff ≤ _
  rw [total]
  exact (ordinary_sum_le T).trans <| (Finset.sum_le_sum (fun j _ => each j)).trans_eq (by simp)

private def negative {Y X : FourTensor} (R : MapsR Y X) : MapsR Y X :=
  fun i u v => (if i=0 then -1 else 1)*R i u v
private theorem image_neg {Y X} (R : MapsR Y X) (y) : imageR (negative R) y = -imageR R y := by
  simp only [imageR,negative,Finset.prod_mul_distrib,Finset.prod_ite_eq',Finset.mem_univ,if_true,
    neg_one_mul,neg_mul,one_mul,Finset.sum_neg_distrib]

theorem realTest_of_difference {k C n : ℕ} (h : DifferenceTest k C n) : RealTest k (16*C) n := by
  obtain ⟨P,Q,_,_,eq⟩ := h
  let R : Fin 8 ⊕ Fin 8 → MapsR (dst k n) (src k C n) := Sum.elim P (fun j => negative (Q j))
  have sum (y) : ((dst k n).2 y).re = ∑ j,imageR (R j) y := by
    rw [Fintype.sum_sum_type]
    simp only [R,Sum.elim_inl,Sum.elim_inr,image_neg,Finset.sum_neg_distrib]
    linarith [eq y]
  simpa using real_of_sum R sum

/-- The open case can be expressed using only nonnegative matrices with one
subtraction between two sums. Both directions allow a constant copy overhead. -/
theorem remaining_iff_nonnegative_difference :
    (∀ C : ℕ,16≤C → ∃ n : ℕ,0<n ∧ ¬Test 4 C n) ↔
    (∀ C : ℕ,16≤C → ∃ n : ℕ,0<n ∧ ¬DifferenceTest 4 (8*C) n) := by
  constructor
  · intro fail C hC
    obtain ⟨n,hn,h⟩ := fail (16*(8*C)) (by omega)
    exact ⟨n,hn,fun d => h (complex_of_realTest (realTest_of_difference d))⟩
  · intro fail C hC
    obtain ⟨n,hn,h⟩ := fail C hC
    exact ⟨n,hn,fun z => h (difference_of_realTest (realTest_of_complex z))⟩

end
end OMA.GreenSupport


namespace OMA.GreenSupport

theorem four_point_of_signed_real_failure
    (hard : ∀ C : ℕ, 16≤C → ∃ n : ℕ, 0<n ∧ ¬RealTest 4 (8*C) n) :
    OMA.R_Erdos20_erdos_20_R1_H2_R1_H1_R1.H1 := by
  apply OMA.R_Erdos20_erdos_20_R1_H2_R1_H1_R1_H1_R2.main _ OMA.FourSiteRanksComparison
  refine ⟨4,by decide,?_⟩
  intro C hC
  change ∃ n : ℕ,0<n ∧ ¬OMA.FourSiteRanks.Test 4 C n
  by_cases small : C≤15
  · exact ⟨1,by decide,OMA.FourSiteRanks.fourth_power_fifteen C small⟩
  · exact (remaining_iff_signed_real.mpr hard) C (by omega)

theorem four_point_of_nonnegative_difference_failure
    (hard : ∀ C : ℕ, 16≤C → ∃ n : ℕ, 0<n ∧ ¬DifferenceTest 4 (8*C) n) :
    OMA.R_Erdos20_erdos_20_R1_H2_R1_H1_R1.H1 :=
  four_point_of_signed_real_failure (remaining_iff_signed_real.mp
    (remaining_iff_nonnegative_difference.mpr hard))

end OMA.GreenSupport

namespace OMA.FourSiteRanks

theorem green_comparison_floor (k : ℕ) (ex : ∃ C : ℕ, 0<C ∧ ∀ n : ℕ, 0<n → Test k C n) :
    ∃ C : ℕ, 0<C ∧ (k=4 → 16≤C) ∧
      (k=4 → ∀ n : ℕ, 0<n → 2*C≤8^n →
        ∃ M : GreenSupport.Maps (GreenSupport.dst 4 n) (GreenSupport.src 4 C n),
          (∀ y,(GreenSupport.dst 4 n).2 y=∑ z,GreenSupport.term M y z) ∧
          ((2^4)^n)^2 ≤ 4*(GreenSupport.phaseConflict M).card) ∧
      ∀ n : ℕ, 0<n → Test k C n := by
  obtain ⟨C,pos,works⟩ := ex
  refine ⟨C,pos,?_,?_,works⟩
  · rintro rfl
    by_contra! small
    exact fourth_power_fifteen C (by omega) (works 1 (by decide))
  · rintro rfl n hn many
    obtain ⟨M,res⟩ := works n hn
    exact ⟨M,res,(GreenSupport.half_actual_interference many M res).trans
      (Nat.mul_le_mul_left 4 (Finset.card_le_card (GreenSupport.interference_phases M res)))⟩

end OMA.FourSiteRanks

theorem OMA.solution : OMA.R_Erdos20_erdos_20_R1_H2_R1_H1_R1_H1_R2.H2 := by
  intro tree k hk
  obtain ⟨C,pos,_,_,works⟩ := OMA.FourSiteRanks.green_comparison_floor k (OMA.FourSiteRanksComparison tree k hk)
  exact ⟨8*C,by positivity,fun n hn => OMA.GreenSupport.complex_of_realTest
    (OMA.GreenSupport.realTest_of_complex (works n hn))⟩
