import OMAStatements.S_mo_121243
import Mathlib

/-!
# Determinant of a loopless Fibonacci-sum graph

Source: zoha, MathOverflow 121243. Credit: @connoranderson.
Jack D’Aurizio identified the forced partner of a largest Fibonacci vertex
in the linked Math Stack Exchange discussion (answer 2013). Arman, Gunderson
and Li (arXiv:1710.10303) describe the bipartiteness and outerplanar structure
of this graph. The proof below uses a two-vertex determinant recurrence.

The largest remaining label has at most two possible neighbors. A leaf and its
neighbor can be eliminated. When the upper neighbor is present, eliminating
that pair cancels the edge between the two lower neighbors. We maintain that
an edge of Fibonacci sum F(k+2) is still present whenever its two potential
upper neighbors of complementary sum F(k+4) are both present. Each elimination
therefore preserves the entry conditions and negates the smaller determinant.
-/

namespace OMA.S_mo_121243
open Matrix
variable {V : Type} [Fintype V] [DecidableEq V]

private abbrev Others (x y : V) := {z : V // z ≠ x ∧ z ≠ y}

private def pairAt (x y : V) (i : Fin 2) : V := if i=0 then x else y

private noncomputable def partition (x y : V) (hxy : x ≠ y) : Fin 2 ⊕ Others x y ≃ V :=
  Equiv.ofBijective (Sum.elim (pairAt x y) Subtype.val) (by
    constructor
    · rintro (i|u) (j|v)
      · fin_cases i <;> fin_cases j <;> simp [pairAt, hxy, Ne.symm hxy]
      · fin_cases i <;> simp [pairAt, Ne.symm v.2.1, Ne.symm v.2.2]
      · fin_cases j <;> simp [pairAt, u.2.1, u.2.2]
      · simp [Subtype.ext_iff]
    · intro z
      by_cases hx : z=x
      · exact ⟨.inl 0, by simp [pairAt,hx]⟩
      by_cases hy : z=y
      · exact ⟨.inl 1, by simp [pairAt,hy]⟩
      exact ⟨.inr ⟨z,hx,hy⟩,rfl⟩)

private def pivot {x y : V} (M : Matrix V V ℤ) : Matrix (Others x y) (Others x y) ℤ :=
  Matrix.of fun a b => M a b - (M a x * M y b + M a y * M x b)

private lemma det_pivot (x y : V) (hxy : x ≠ y) (M : Matrix V V ℤ) (hxx : M x x = 0)
    (hyy : M y y = 0) (h₁ : M x y = 1) (h₂ : M y x = 1) :
    M.det = -(pivot (x:=x) (y:=y) M).det := by
  classical
  let e := partition x y hxy
  let A : Matrix (Fin 2) (Fin 2) ℤ := !![0,1;1,0]
  let B : Matrix (Fin 2) (Others x y) ℤ := fun i j => M (pairAt x y i) j
  let C : Matrix (Others x y) (Fin 2) ℤ := fun i j => M i (pairAt x y j)
  let D : Matrix (Others x y) (Others x y) ℤ := M.submatrix Subtype.val Subtype.val
  have ha : A * A = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [A, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  let _ : Invertible A := ⟨A, ha, ha⟩
  have he : M.submatrix e e = Matrix.fromBlocks A B C D := by
    ext i j
    rcases i with i|i <;> rcases j with j|j
    · change M (pairAt x y i) (pairAt x y j) = A i j
      fin_cases i <;> fin_cases j <;> simp [pairAt,A,hxx,hyy,h₁,h₂]
    · rfl
    · rfl
    · rfl
  have hd : A.det = -1 := by norm_num [A, Matrix.det_fin_two]
  rw [← Matrix.det_submatrix_equiv_self e M, he, Matrix.det_fromBlocks₁₁, hd, neg_one_mul]
  congr 1
  apply congrArg Matrix.det
  change D - C * A * B = _
  ext i j
  rw [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply,
    Fin.sum_univ_two, Fin.sum_univ_two]
  simp [pivot, D, C, A, B, pairAt]
  ring

private lemma remaining_card (x y : V) (hxy : x ≠ y) :
    Fintype.card (Others x y) + 2 = Fintype.card V := by
  simpa [Nat.add_comm] using Fintype.card_congr (partition x y hxy)


private lemma fib_window (v : ℕ) (h : 2 ≤ v) :
    ∃ k, Nat.fib (k+3) ≤ v ∧ v < Nat.fib (k+4) := by
  induction v, h using Nat.le_induction with
  | base => exact ⟨0, by decide, by decide⟩
  | succ v hv ih =>
    obtain ⟨k,hlo,hhi⟩ := ih
    by_cases h : v+1 < Nat.fib (k+4)
    · exact ⟨k, by omega, h⟩
    · refine ⟨k+1, ?_, ?_⟩
      · change Nat.fib (k+4) ≤ _; omega
      change v+1 < Nat.fib (k+5)
      have hh : Nat.fib (k+4) < Nat.fib (k+5) := Nat.fib_lt_fib_succ (n:=k+4) (by omega)
      omega

private lemma neighbor_options {k u v t : ℕ} (hu : 0 < u) (hub : u < Nat.fib (k+4))
    (hv : Nat.fib (k+3) ≤ v) (hvb : v < Nat.fib (k+4)) (h : u+v = Nat.fib t) :
    u+v = Nat.fib (k+4) ∨ u+v = Nat.fib (k+5) := by
  have ha : k+3 < t := by
    by_contra! hn
    have := Nat.fib_mono hn
    omega
  have hb : t < k+6 := by
    by_contra! hn
    have h₁ := Nat.fib_mono hn
    have h₂ := Nat.fib_mono (show k+4 ≤ k+5 by omega)
    have he : Nat.fib (k+6) = Nat.fib (k+4) + Nat.fib (k+5) := Nat.fib_add_two
    omega
  rcases (show t=k+4 ∨ t=k+5 by omega) with rfl|rfl <;> simp [h]

private structure Good (z : V → ℕ) (M : Matrix V V ℤ) : Prop where
  symm : ∀ i j, M i j = M j i
  diag : ∀ i, M i i = 0
  bit : ∀ i j, M i j = 0 ∨ M i j = 1
  support : ∀ i j, M i j ≠ 0 → ∃ k, z i + z j = Nat.fib k
  base : ∀ i j u v k, i ≠ j → z i + z j = Nat.fib (k+2) →
    z i + z u = Nat.fib (k+4) → z j + z v = Nat.fib (k+4) → M i j = 1

omit [Fintype V] [DecidableEq V] in
private lemma pivot_good {z : V → ℕ} (hz : Function.Injective z) {M : Matrix V V ℤ}
    (H : Good z M) {x y : V}
    (changeEdge : ∀ a b : Others x y, pivot M a b = M a b ∨
      (pivot M a b = 0 ∧ ∃ k, z a + z b = Nat.fib (k+2) ∧
        (z a + z x = Nat.fib (k+4) ∨ z a + z y = Nat.fib (k+4)))) :
    Good (fun a : Others x y => z a) (pivot M) := by
  constructor
  · intro a b
    change M a b - _ = M b a - _
    rw [H.symm (a:V) (b:V), H.symm (a:V) x, H.symm (a:V) y,
        H.symm y (b:V),H.symm x (b:V)]
    ring
  · intro a
    rcases changeEdge a a with h|h
    · exact h.trans (H.diag _)
    · exact h.1
  · intro a b
    rcases changeEdge a b with h|h
    · rw [h]; exact H.bit _ _
    · exact Or.inl h.1
  · intro a b h
    rcases changeEdge a b with he|he
    · exact H.support _ _ (he ▸ h)
    · exact (h he.1).elim
  · intro a b u v k hab hab' hau hbv
    rcases changeEdge a b with he|⟨_,l,hl,hx|hy⟩
    · exact he.trans (H.base _ _ _ _ k (Subtype.val_injective.ne hab) hab' hau hbv)
    · have hlk : l = k := Nat.fib_add_two_strictMono.injective (hl.symm.trans hab')
      subst l
      exact (u.2.1 (hz (Nat.add_left_cancel (hau.trans hx.symm)))).elim
    · have hlk : l = k := Nat.fib_add_two_strictMono.injective (hl.symm.trans hab')
      subst l
      exact (u.2.2 (hz (Nat.add_left_cancel (hau.trans hy.symm)))).elim


omit [Fintype V] [DecidableEq V] in
private lemma find_pivot {z : V → ℕ} (hz : Function.Injective z) (hpos : ∀ i, 0 < z i)
    {M : Matrix V V ℤ} (H : Good z M) (x : V) (hm : ∀ i, z i ≤ z x)
    (w : V) (hw : M x w ≠ 0) :
    ∃ y : V, x ≠ y ∧ M x y = 1 ∧ Good (fun a : Others x y => z a) (pivot M) := by
  classical
  have hwx : w ≠ x := fun h => hw (h ▸ H.diag _)
  have hz₂ : 2 ≤ z x := by
    have h₁ := hpos w
    have h₂ := hm w
    have h₃ := hz.ne hwx
    omega
  obtain ⟨k, hlo,hhi⟩ := fib_window _ hz₂
  let b := Nat.fib (k+3)
  let c := Nat.fib (k+4)
  let d := Nat.fib (k+5)
  have hcd : d = b+c := Nat.fib_add_two
  have hbc : c = Nat.fib (k+2) + b := Nat.fib_add_two
  have hin (i : V) : z i < c := (hm i).trans_lt hhi
  have opts {i j : V} (hi : b ≤ z i) (he : M j i ≠ 0) :
      z j + z i = c ∨ z j + z i = d := by
    obtain ⟨t,ht⟩ := H.support _ _ he
    exact neighbor_options (hpos j) (hin j) hi (hin i) ht
  have hone {i j : V} (h : M i j ≠ 0) := (H.bit i j).resolve_left h
  by_cases high : ∃ y, M x y ≠ 0 ∧ z y + z x = d
  · obtain ⟨y, hxy, hs⟩ := high
    have hne : x ≠ y := fun h => hxy (h ▸ H.diag _)
    have hy : b ≤ z y := by have := hin x; omega
    refine ⟨y,hne,hone hxy,pivot_good hz H ?_⟩
    intro a b'
    have onlyLow {p q t : V} (hp : b ≤ z p) (hpq : z p + z q=d)
        (ht : t ≠ q) (he : M t p ≠ 0) : z t + z p = c := by
      rcases opts hp he with h|h
      · exact h
      · exact (ht (hz (by omega))).elim
    have ear {u v : V} (hu : b ≤ z u) (hv : b ≤ z v) (huv : u ≠ v)
        (hsum : z u + z v=d) (hav : (a:V) ≠ v) (hau : (a:V) ≠ u)
        (hbu : (b':V) ≠ u) (he : M a u * M v b' ≠ 0) :
        M a b' = 1 ∧ M a u * M v b' = 1 ∧ M a v * M u b' = 0 ∧
          z a + z b' = Nat.fib (k+2) ∧ z a + z u = c := by
      obtain ⟨h₁,h₂⟩ := mul_ne_zero_iff.mp he
      have ha := onlyLow hu hsum hav h₁
      have hb := onlyLow hv (by omega) hbu (show M b' v ≠ 0 by rwa [H.symm])
      have huv' := hz.ne huv
      have hab : (a:V) ≠ b' := fun h => by rw [h] at ha; omega
      have hzab : z a + z b' = Nat.fib (k+2) := by omega
      refine ⟨H.base _ _ _ _ k hab hzab ha hb, by rw [hone h₁,hone h₂,one_mul], ?_, hzab, ha⟩
      have : M a v = 0 := by
        by_contra hm'
        have := onlyLow hv (by omega) hau hm'
        omega
      rw [this, zero_mul]
    by_cases hc : M a x * M y b' ≠ 0
    · obtain ⟨h,f,g,t,u⟩ := ear hlo hy hne (by omega) a.2.2 a.2.1 b'.2.1 hc
      exact Or.inr ⟨by simp [pivot,h,f,g], k, t, Or.inl u⟩
    · by_cases hc' : M a y * M x b' ≠ 0
      · obtain ⟨h,f,g,t,u⟩ := ear hy hlo (Ne.symm hne) hs a.2.1 a.2.2 b'.2.2 hc'
        exact Or.inr ⟨by simp [pivot,h,f,g], k, t, Or.inr u⟩
      · exact Or.inl (by simp [pivot, not_ne_iff.mp hc, not_ne_iff.mp hc'])
  · have hl {i : V} (he : M x i ≠ 0) : z i + z x = c :=
      (opts hlo (show M i x ≠ 0 by rwa [H.symm])).resolve_right (fun h => high ⟨i,he,h⟩)
    refine ⟨w, Ne.symm hwx, hone hw, pivot_good hz H ?_⟩
    intro a b'
    have leaf (t : Others x w) : M x t = 0 := by
      by_contra he
      exact t.2.2 (hz (Nat.add_right_cancel ((hl he).trans (hl hw).symm)))
    exact Or.inl (by simp [pivot, H.symm (a:V) x, leaf])


private theorem determinant_bound (m : ℕ) :
    ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V = m →
    ∀ (z : V → ℕ), Function.Injective z → (∀ i, 0 < z i) →
    ∀ M : Matrix V V ℤ, Good z M →
      M.det = 0 ∨ (Even m ∧ (M.det = 1 ∨ M.det = -1)) := by
  classical
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro V _ _ hv z hz hpos M H
    cases isEmpty_or_nonempty V with
    | inl h =>
      let _ := h
      have hm : m=0 := hv.symm.trans Fintype.card_eq_zero
      exact Or.inr ⟨hm ▸ (show Even 0 by decide), Or.inl Matrix.det_isEmpty⟩
    | inr h =>
      let _ := h
      obtain ⟨x,_,hx⟩ := Finset.exists_max_image Finset.univ z Finset.univ_nonempty
      by_cases hr : ∀ y, M x y = 0
      · exact Or.inl (Matrix.det_eq_zero_of_row_eq_zero x hr)
      · obtain ⟨w,hw⟩ := not_forall.mp hr
        obtain ⟨y,hxy,he,hG⟩ := find_pivot hz hpos H x (fun i => hx i (Finset.mem_univ _)) w hw
        have hc := (remaining_card x y hxy).trans hv
        rw [det_pivot x y hxy M (H.diag _) (H.diag _) he ((H.symm y x).trans he)]
        obtain he' | ⟨hem, h₁ | h₂⟩ := ih _ (by omega) (Others x y) rfl
          (fun a => z a.val) (hz.comp Subtype.val_injective) (fun a => hpos a.val) _ hG
        · exact Or.inl (by rw [he', neg_zero])
        · obtain ⟨t, ht⟩ := hem
          exact Or.inr ⟨⟨t+1, by omega⟩, Or.inr (by rw [h₁])⟩
        · obtain ⟨t, ht⟩ := hem
          exact Or.inr ⟨⟨t+1, by omega⟩, Or.inl (by rw [h₂,neg_neg])⟩

theorem graph_determinant (n : ℕ) :
    (adjacency n).det = 0 ∨ (Even n ∧ ((adjacency n).det = 1 ∨ (adjacency n).det = -1)) := by
  classical
  let z (i : Fin n) := i.val + 1
  apply determinant_bound n (Fin n) (Fintype.card_fin n) z
  · intro i j h; exact Fin.ext (Nat.add_right_cancel h)
  · intro i; exact Nat.zero_lt_succ _
  constructor
  · intro i j
    simp only [adjacency,Matrix.of_apply]
    congr 1
    exact propext (by rw [ne_comm, Nat.add_comm (i.val+1)])
  · intro i; simp [adjacency]
  · intro i j; simp only [adjacency, Matrix.of_apply]; split <;> simp
  · intro i j h; simp [adjacency] at h; exact h.2
  · intro i j u v k hij he _ _
    simp [adjacency,hij, show ∃ l, i.val+1+(j.val+1)=Nat.fib l from ⟨k+2,he⟩]

end OMA.S_mo_121243

theorem OMA.solution : type_of% @OMA.S_mo_121243.main := by
  intro n _
  rcases OMA.S_mo_121243.graph_determinant n with h|⟨he,h|h⟩
  · exact ⟨fun _ => h, fun _ => Or.inr (Or.inr h)⟩
  · exact ⟨fun ho => (Nat.not_even_iff_odd.mpr ho he).elim, fun _ => Or.inl h⟩
  · exact ⟨fun ho => (Nat.not_even_iff_odd.mpr ho he).elim, fun _ => Or.inr (Or.inl h)⟩
