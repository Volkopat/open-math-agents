import OMAReductions.R_HyperbolicGroupsResiduallyFinite_hyperbolic_exists_finiteIndex_ne_top_R3_H1_R1

namespace ReducedWordPowers

open Monoid.CoprodI

variable {A : Type} [Group A]

private abbrev F (A : Type) := fun _ : Fin 2 => A
private abbrev W (A : Type) [Group A] := NeWord (F A)

private theorem length_inv {i j} (w : W A i j) :
    w.inv.toList.length = w.toList.length := by
  induction w with
  | singleton => rfl
  | append _ _ _ ih₁ ih₂ => simp [NeWord.inv, ih₁, ih₂, Nat.add_comm]

private theorem split_head {i j} (w : W A i j) :
    (i = j ∧ w.toList.length = 1 ∧ ∃ a : A, w.prod = of (i := i) a) ∨
      ∃ (k : Fin 2) (v : W A k j) (a : A), i ≠ k ∧
        w.toList.length = v.toList.length + 1 ∧ w.prod = of (i := i) a * v.prod := by
  induction w with
  | singleton a ha =>
    exact Or.inl ⟨rfl, rfl, a, NeWord.prod_singleton a ha⟩
  | @append i j k l u hjk v ihu _ =>
    rcases ihu with ⟨rfl, hlen, a, ha⟩ | ⟨m, z, a, him, hlen, ha⟩
    · refine Or.inr ⟨k, v, a, hjk, ?_, ?_⟩
      · simp [hlen, Nat.add_comm]
      · rw [NeWord.append_prod, ha]
    · refine Or.inr ⟨m, z.append hjk v, a, him, ?_, ?_⟩
      · simp [hlen, Nat.add_right_comm]
      · simp only [NeWord.append_prod, ha, mul_assoc]

private theorem word_ne_one {i j} (w : W A i j) : w.prod ≠ 1 := by
  classical
  intro h
  have hword : w.toWord = (Word.empty : Word (F A)) := by
    apply (Word.equiv (M := F A)).symm.injective
    change w.prod = (Word.empty : Word (F A)).prod
    simpa only [Word.prod_empty] using h
  exact w.toList_ne_nil (congrArg Word.toList hword)

private theorem cyclic_power_ne_one {i j} (w : W A i j) (hij : i ≠ j) :
    ∀ n : ℕ, w.prod ^ (n + 1) ≠ 1 := by
  have word (n : ℕ) : ∃ v : W A i j, v.prod = w.prod ^ (n + 1) := by
    induction n with
    | zero => exact ⟨w, by simp⟩
    | succ n ih =>
      obtain ⟨v, hv⟩ := ih
      refine ⟨v.append hij.symm w, ?_⟩
      rw [NeWord.append_prod, hv]
      exact (pow_succ w.prod (n + 1)).symm
  intro n h
  obtain ⟨v, hv⟩ := word n
  exact word_ne_one v (hv.trans h)

private theorem conjugate_power {G : Type*} [Group G] {g : G} {n : ℕ}
    (h : g ^ n = 1) (a : G) : (a⁻¹ * g * a) ^ n = 1 := by
  let e := MulAut.conj a⁻¹
  have he := congrArg e h
  rw [map_pow, map_one] at he
  simpa [e, MulAut.conj_apply] using he

private theorem reduced_power_ne_one
    (ht : ∀ (a : A) (n : ℕ), 0 < n → a ^ n = 1 → a = 1)
    (n : ℕ) (hn : 0 < n) (L : ℕ) :
    ∀ i j (w : W A i j), w.toList.length = L → w.prod ^ n ≠ 1 := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
    intro i j w hL hw
    by_cases hij : i = j
    · subst j
      rcases split_head w with ⟨_, _, a, ha⟩ | ⟨k, v, a, hik, hl, ha⟩
      · rw [ha, ← map_pow, ← map_one (of (i := i))] at hw
        have h1 := ht a n hn (of_injective i hw)
        exact word_ne_one w (by simp [ha, h1])
      · rcases split_head v.inv with ⟨hik', _, _⟩ | ⟨l, z, b, hil, hlz, hb⟩
        · exact hik hik'
        have hv : v.prod = z.inv.prod * of (i := i) b⁻¹ := by
          simpa only [NeWord.inv_prod, mul_inv_rev, ← map_inv, inv_inv] using
            congrArg Inv.inv hb
        have hp : (v.prod * of (i := i) a) ^ n = 1 := by
          have hconj := conjugate_power hw (of (i := i) a)
          rwa [ha, ← mul_assoc, inv_mul_cancel, one_mul] at hconj
        rw [hv, mul_assoc, ← map_mul] at hp
        by_cases hba : b⁻¹ * a = 1
        · have hz : z.inv.toList.length < L := by
            rw [length_inv]
            rw [length_inv] at hlz
            omega
          exact ih _ hz _ _ z.inv rfl (by simpa [hba] using hp)
        · let y := z.inv.append hil.symm (NeWord.singleton (b⁻¹ * a) hba)
          have hy : y.toList.length < L := by
            simp only [y, NeWord.toList, List.length_append, List.length_singleton, length_inv]
            rw [length_inv] at hlz
            omega
          exact ih _ hy _ _ y rfl (by simpa [y] using hp)
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      exact cyclic_power_ne_one w hij m hw

theorem torsionFree
    (ht : ∀ (a : A) (n : ℕ), 0 < n → a ^ n = 1 → a = 1)
    (g : Monoid.CoprodI (F A)) (n : ℕ) (hn : 0 < n) (hg : g ^ n = 1) : g = 1 := by
  classical
  let w := (Word.equiv (M := F A)) g
  by_contra h
  have hne : w ≠ Word.empty := by
    intro he
    have := congrArg (Word.equiv (M := F A)).symm he
    exact h (by simpa [w, Word.equiv, Word.prod_empty] using this)
  obtain ⟨i, j, v, hv⟩ := NeWord.of_word w hne
  have hprod : v.prod = g := by
    change v.toWord.prod = g
    rw [hv]
    exact (Word.equiv (M := F A)).symm_apply_apply g
  exact reduced_power_ne_one ht n hn _ i j v rfl (by simpa [hprod] using hg)

end ReducedWordPowers

theorem OMA.solution :
    OMA.R_HyperbolicGroupsResiduallyFinite_hyperbolic_exists_finiteIndex_ne_top_R3_H1_R1.H3 := by
  intro A _ h
  exact ReducedWordPowers.torsionFree h