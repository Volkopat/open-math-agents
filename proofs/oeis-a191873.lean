import OMAStatements.S_oeis_a191873
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
Alekseyev's A191873 conjecture equates the zero-diagonal and unrestricted
Zarankiewicz maxima and relates them to the first forcing weight.
Source: https://oeis.org/A191873
Related sequences: https://oeis.org/A072567 and https://oeis.org/A001197
Official statement credit: @LDJAI
Proof credit: @grp06
-/

open OMA.S_oeis_a191873

namespace OMA.A191873Proof

private theorem filter_eq_of_deciders {α : Type*} (s : Finset α) (p : α → Prop)
    (d₁ d₂ : DecidablePred p) : @Finset.filter α p d₁ s = @Finset.filter α p d₂ s := by
  have h : d₁ = d₂ := funext (fun x => Subsingleton.elim (d₁ x) (d₂ x))
  cases h
  rfl

private theorem emptyDiagonal {n : ℕ} {A : Board n} (hA : rectangleFree A)
    (hrow : ∀ i, ∃ j, (i, j) ∉ A) (hcol : ∀ j, ∃ i, (i, j) ∉ A) :
    ∃ B : Board n, rectangleFree B ∧ (∀ i, (i, i) ∉ B) ∧ B.card = A.card := by
  classical
  let R : Fin n → Fin n → Prop := fun i j => (i, j) ∉ A
  have hall : ∀ S : Finset (Fin n),
      S.card ≤ (Finset.univ.filter (fun j => ∃ i ∈ S, R i j)).card := by
    intro S
    let N : Finset (Fin n) := Finset.univ.filter (fun j => ∃ i ∈ S, R i j)
    change S.card ≤ N.card
    have neighbor (j : Fin n) : j ∈ N ↔ ∃ i ∈ S, R i j := by simp [N]
    have hS : S.card ≤ n := by simpa using S.card_le_univ
    by_cases hfull : S.card = n
    · have hSuniv : S = Finset.univ := S.eq_univ_of_card (by simpa using hfull)
      have hNuniv : N = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro j
        obtain ⟨i, hi⟩ := hcol j
        exact (neighbor j).2 ⟨i, by simp [hSuniv], hi⟩
      simp [hNuniv, hfull]
    by_cases hsmall : S.card ≤ 1
    · by_cases hzero : S.card = 0
      · simp [hzero]
      have hpos : 0 < S.card := by omega
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
      obtain ⟨j, hj⟩ := hrow i
      have hNpos : 0 < N.card := Finset.card_pos.mpr ⟨j, (neighbor j).2 ⟨i, hi, hj⟩⟩
      omega
    · by_contra hle
      have hlt : N.card < S.card := lt_of_not_ge hle
      let M : Finset (Fin n) := Finset.univ \ N
      have hM : M.card = n - N.card := by
        simp [M, Finset.card_sdiff_of_subset (Finset.subset_univ N)]
      have hMlarge : 1 < M.card := by omega
      have hSlarge : 1 < S.card := by omega
      obtain ⟨i, k, hi, hk, hik⟩ := Finset.one_lt_card_iff.mp hSlarge
      obtain ⟨j, l, hj, hl, hjl⟩ := Finset.one_lt_card_iff.mp hMlarge
      have occupied (r c : Fin n) (hr : r ∈ S) (hc : c ∈ M) : (r, c) ∈ A := by
        by_contra h
        have hcN : c ∉ N := (Finset.mem_sdiff.mp hc).2
        exact hcN ((neighbor c).2 ⟨r, hr, h⟩)
      exact hA i k j l hik hjl (occupied i j hi hj) (occupied i l hi hl)
        (occupied k j hk hj) (occupied k l hk hl)
  have matching : ∃ f : Fin n → Fin n, Function.Injective f ∧ ∀ i, R i (f i) := by
    apply (Fintype.all_card_le_filter_rel_iff_exists_injective R).mp
    intro S
    refine (hall S).trans (le_of_eq ?_)
    exact congrArg Finset.card (filter_eq_of_deciders Finset.univ (fun j => ∃ i ∈ S, R i j) _ _)
  obtain ⟨f, hf, hz⟩ := matching
  let e : Equiv.Perm (Fin n) := Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
  let p : Equiv.Perm (Fin n × Fin n) := (Equiv.refl (Fin n)).prodCongr e
  let B := A.map p.symm.toEmbedding
  have memB (i j : Fin n) : (i, j) ∈ B ↔ (i, e j) ∈ A := by
    change (i, j) ∈ A.map p.symm.toEmbedding ↔ p (i, j) ∈ A
    simpa only [Equiv.symm_symm] using
      (Finset.mem_map_equiv (s := A) (f := p.symm) (b := (i, j)))
  refine ⟨B, ?_, ?_, Finset.card_map _⟩
  · intro i k j l hik hjl hij hil hkj hkl
    exact hA i k (e j) (e l) hik (fun h => hjl (e.injective h))
      ((memB i j).1 hij) ((memB i l).1 hil) ((memB k j).1 hkj) ((memB k l).1 hkl)
  · intro i hi
    have hm : (i, f i) ∈ A := (memB i i).1 hi
    exact hz i hm

/-- The successor in a cyclic row or column index. -/
private def next {n : ℕ} (i : Fin n) : Fin n :=
  if h : i.val + 1 < n then ⟨i.val + 1, h⟩ else ⟨0, i.pos⟩

private theorem next_val {n : ℕ} (i : Fin n) :
    (next i).val = if i.val + 1 < n then i.val + 1 else 0 := by
  unfold next
  split <;> simp_all

private theorem cyclic {n : ℕ} (hn : 3 ≤ n) : 2 * n ∈ weights n := by
  classical
  have neNext (i : Fin n) : next i ≠ i := by
    intro h
    have hv := congrArg Fin.val h
    rw [next_val] at hv
    have hi := i.isLt
    split at hv <;> omega
  have injNext : Function.Injective (next : Fin n → Fin n) := by
    intro i k h
    apply Fin.ext
    have hv := congrArg Fin.val h
    rw [next_val i, next_val k] at hv
    have hi := i.isLt
    have hk := k.isLt
    by_cases hi' : i.val + 1 < n <;> by_cases hk' : k.val + 1 < n <;>
      simp only [hi', hk', if_true, if_false] at hv <;> omega
  have noTwoCycle (i : Fin n) : next (next i) ≠ i := by
    intro h
    have hv := congrArg Fin.val h
    rw [next_val (next i)] at hv
    have hstep := next_val i
    have hi := i.isLt
    by_cases hi' : i.val + 1 < n
    · rw [if_pos hi'] at hstep
      rw [hstep] at hv
      split at hv <;> omega
    · rw [if_neg hi'] at hstep
      rw [hstep, if_pos (show 0 + 1 < n by omega)] at hv
      omega
  let D : Fin n × Bool → Fin n × Fin n :=
    fun (i, b) => (i, if b then next i else i)
  have hD : Function.Injective D := by
    rintro ⟨i, b⟩ ⟨k, c⟩ h
    have hik : i = k := congrArg Prod.fst h
    subst k
    have hc := congrArg Prod.snd h
    change (if b then next i else i) = (if c then next i else i) at hc
    cases b <;> cases c
    · rfl
    · exact (neNext i hc.symm).elim
    · exact (neNext i hc).elim
    · rfl
  let A : Board n := Finset.univ.map ⟨D, hD⟩
  have cols {i j : Fin n} (h : (i, j) ∈ A) : j = i ∨ j = next i := by
    obtain ⟨⟨k, b⟩, _, heq⟩ := Finset.mem_map.mp h
    have hik : k = i := congrArg Prod.fst heq
    subst k
    have hj := congrArg Prod.snd heq
    change (if b then next i else i) = j at hj
    cases b
    · exact Or.inl hj.symm
    · exact Or.inr hj.symm
  have overlap {i k : Fin n} (hik : i ≠ k) {j : Fin n}
      (hj : j = i ∨ j = next i) (hk : j = k ∨ j = next k) :
      (j = i ∧ i = next k) ∨ (j = k ∧ k = next i) := by
    rcases hj with h | h <;> rcases hk with h' | h'
    · exact (hik (h.symm.trans h')).elim
    · exact Or.inl ⟨h, h.symm.trans h'⟩
    · exact Or.inr ⟨h', h'.symm.trans h⟩
    · exact (hik (injNext (h.symm.trans h'))).elim
  refine ⟨A, ?_, ?_⟩
  · intro i k j l hik hjl hij hil hkj hkl
    rcases overlap hik (cols hij) (cols hkj) with ⟨hji, hik'⟩ | ⟨hjk, hki'⟩
    · rcases overlap hik (cols hil) (cols hkl) with ⟨hli, _⟩ | ⟨_, hki'⟩
      · exact hjl (hji.trans hli.symm)
      · exact noTwoCycle i ((congrArg next hki').symm.trans hik'.symm)
    · rcases overlap hik (cols hil) (cols hkl) with ⟨_, hik'⟩ | ⟨hlk, _⟩
      · exact noTwoCycle i ((congrArg next hki').symm.trans hik'.symm)
      · exact hjl (hjk.trans hlk.symm)
  · simp [A, Fintype.card_prod, Fintype.card_bool, Nat.mul_comm]

private theorem fullRowBound {n : ℕ} {A : Board n} (hA : rectangleFree A)
    {r : Fin n} (hr : ∀ j, (r, j) ∈ A) : A.card ≤ 2 * n - 1 := by
  classical
  let tag (p : Fin n × Fin n) : Fin n ⊕ Fin n :=
    if p.1 = r then .inl p.2 else .inr p.1
  have h : A.card ≤ ((Finset.univ : Finset (Fin n)).disjSum (Finset.univ.erase r)).card := by
    apply Finset.card_le_card_of_injOn tag
    · intro p _
      by_cases hp : p.1 = r <;> simp [tag, hp]
    · rintro ⟨i, j⟩ hij ⟨k, l⟩ hkl heq
      by_cases hi : i = r <;> by_cases hk : k = r <;> simp [tag, hi, hk] at heq
      · exact Prod.ext (hi.trans hk.symm) heq
      · subst k
        refine Prod.ext rfl ?_
        by_contra hjl
        exact hA i r j l hi hjl hij hkl (hr j) (hr l)
  simp [Finset.card_erase_of_mem (Finset.mem_univ r)] at h
  omega

private theorem fullColBound {n : ℕ} {A : Board n} (hA : rectangleFree A)
    {c : Fin n} (hc : ∀ i, (i, c) ∈ A) : A.card ≤ 2 * n - 1 := by
  let e := Equiv.prodComm (Fin n) (Fin n)
  let B := A.map e.toEmbedding
  have memB (i j : Fin n) : (i, j) ∈ B ↔ (j, i) ∈ A :=
    Finset.mem_map_equiv
  have hB : rectangleFree B := by
    intro i k j l hik hjl hij hil hkj hkl
    exact hA j l i k hjl hik ((memB i j).1 hij) ((memB k j).1 hkj)
      ((memB i l).1 hil) ((memB k l).1 hkl)
  have h := fullRowBound hB (fun j => (memB c j).2 (hc j))
  simpa only [B, Finset.card_map] using h

private theorem weightBound {n : ℕ} (A : Board n) : A.card ≤ n * n := by
  simpa only [Fintype.card_prod, Fintype.card_fin] using A.card_le_univ

private theorem strictWeightBound {n : ℕ} (hn : 3 ≤ n) {A : Board n}
    (hA : rectangleFree A) : A.card < n * n := by
  have hne : A ≠ Finset.univ := by
    intro h
    let i : Fin n := ⟨0, by omega⟩
    let k : Fin n := ⟨1, by omega⟩
    have hik : i ≠ k := by
      intro heq
      have hv : (0 : ℕ) = 1 := congrArg Fin.val heq
      omega
    have all (p : Fin n × Fin n) : p ∈ A := by
      rw [h]
      exact Finset.mem_univ p
    exact hA i k i k hik hik (all _) (all _) (all _) (all _)
  simpa only [Fintype.card_prod, Fintype.card_fin] using A.card_lt_iff_ne_univ.mpr hne

theorem solve (n : ℕ) (hn : 3 ≤ n) :
    ∃ d z k : ℕ, IsGreatest (diagonalWeights n) d ∧ IsGreatest (weights n) z ∧
      IsLeast (forcingWeights n) k ∧ d = z ∧ z = k-1 := by
  classical
  let P : ℕ → Prop := fun w => w ∈ weights n
  have bound {w : ℕ} (hw : P w) : w ≤ n * n := by
    obtain ⟨A, _, hcard⟩ := hw
    exact hcard ▸ weightBound A
  let z := Nat.findGreatest P (n * n)
  have cyc : P (2 * n) := cyclic hn
  have hz : P z := Nat.findGreatest_spec (bound cyc) cyc
  have maximal {w : ℕ} (hw : P w) : w ≤ z := Nat.le_findGreatest (bound hw) hw
  have hlarge := maximal cyc
  obtain ⟨A, hA, hcard⟩ := hz
  have hrow (i : Fin n) : ∃ j, (i, j) ∉ A := by
    by_contra h
    have hfull (j : Fin n) : (i, j) ∈ A := by
      by_contra hj
      exact h ⟨j, hj⟩
    have hsmall := fullRowBound hA hfull
    omega
  have hcol (j : Fin n) : ∃ i, (i, j) ∉ A := by
    by_contra h
    have hfull (i : Fin n) : (i, j) ∈ A := by
      by_contra hi
      exact h ⟨i, hi⟩
    have hsmall := fullColBound hA hfull
    omega
  obtain ⟨B, hB, hdiag, hBA⟩ := emptyDiagonal hA hrow hcol
  refine ⟨z, z, z + 1, ?_, ⟨⟨A, hA, hcard⟩, ?_⟩, ?_, rfl, by omega⟩
  · refine ⟨⟨B, hB, hdiag, hBA.trans hcard⟩, ?_⟩
    intro w hw
    obtain ⟨C, hC, _, hCcard⟩ := hw
    exact maximal ⟨C, hC, hCcard⟩
  · intro w hw
    exact maximal hw
  · have hstrict : z < n * n := hcard ▸ strictWeightBound hn hA
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · intro C hCcard hC
      have hc : z + 1 ≤ z := maximal ⟨C, hC, hCcard⟩
      omega
    · intro w hw
      change w ≤ n * n ∧ ∀ C : Board n, C.card = w → ¬rectangleFree C at hw
      by_contra h
      have hwle : w ≤ A.card := by omega
      obtain ⟨C, hCA, hCcard⟩ := Finset.exists_subset_card_eq hwle
      have hC : rectangleFree C := by
        intro i k j l hik hjl hij hil hkj hkl
        exact hA i k j l hik hjl (hCA hij) (hCA hil) (hCA hkj) (hCA hkl)
      exact hw.2 C hCcard hC

end OMA.A191873Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a191873.main :=
  OMA.A191873Proof.solve
