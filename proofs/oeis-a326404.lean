import OMAStatements.S_oeis_a326404
import Mathlib.Tactic

open OMA.S_oeis_a326404 Finset Filter Topology
open scoped Classical

namespace CircularNeighbors

private lemma rotGeometry {n : ℕ} (hn : 3 ≤ n) (x : Fin n) :
    finRotate n x ≠ x ∧ finRotate n (finRotate n x) ≠ x := by
  have : NeZero n := ⟨by omega⟩
  have one : (1 : Fin n) ≠ 0 := by
    intro eq
    have v := congrArg Fin.val eq
    change 1%n=0 at v
    rw [Nat.mod_eq_of_lt (by omega)] at v
    omega
  have two : (2 : Fin n) ≠ 0 := by
    intro eq
    have v := congrArg Fin.val eq
    change 2%n=0 at v
    rw [Nat.mod_eq_of_lt (by omega)] at v
    omega
  have twoOnes : (1 : Fin n)+1=2 := by
    apply Fin.ext
    change (1%n+1%n)%n=2%n
    rw [Nat.mod_eq_of_lt (by omega : 1<n)]
  constructor
  · intro e
    apply one
    apply add_left_cancel (a:=x)
    simpa only [add_zero,finRotate_apply] using e
  · intro e
    apply two
    apply add_left_cancel (a:=x)
    calc
      x+(2:Fin n) = (x+1)+1 := by rw [add_assoc,twoOnes]
      _ = x+0 := by simpa only [add_zero,finRotate_apply] using e

private lemma geometry {n : ℕ} (hn : 3 ≤ n) {c : Equiv.Perm (Fin n)}
    (hc : c ∈ circles n) (x : Fin n) : c x ≠ x ∧ c (c x) ≠ x := by
  classical
  obtain ⟨σ,_,rfl⟩ := mem_image.mp hc
  obtain ⟨y,rfl⟩ := σ.surjective x
  simpa [relabel] using rotGeometry hn y

private lemma relabel_closed {n : ℕ} (σ : Equiv.Perm (Fin n)) {c : Equiv.Perm (Fin n)}
    (hc : c ∈ circles n) : relabel σ c ∈ circles n := by
  classical
  obtain ⟨t,_,rfl⟩ := mem_image.mp hc
  exact mem_image.mpr ⟨t.trans σ,mem_univ _,rfl⟩

private lemma neighbors {n : ℕ} (hn : 3 ≤ n) {c : Equiv.Perm (Fin n)}
    (hc : c ∈ circles n) (x : Fin n) :
    ((univ.erase x).filter (adjacent c x)).card = 2 := by
  classical
  obtain ⟨h₁,h₂⟩ := geometry hn hc x
  have prev : c.symm x ≠ x := by
    intro e
    exact h₁ ((congrArg c e).symm.trans (c.apply_symm_apply x))
  have different : c x ≠ c.symm x := by
    intro e
    exact h₂ ((congrArg c e).trans (c.apply_symm_apply x))
  have iffPrev (y : Fin n) : c y = x ↔ y = c.symm x := by
    constructor
    · intro e
      apply c.injective
      simpa using e
    · rintro rfl
      exact c.apply_symm_apply x
  have ident : (univ.erase x).filter (adjacent c x) = {c x,c.symm x} := by
    ext y
    simp only [mem_filter,mem_erase,mem_univ,and_true,adjacent,iffPrev,
      mem_insert,mem_singleton]
    grind
  rw [ident]
  simp [different]

private noncomputable def edgeCount {n : ℕ} (x y : Fin n) : ℕ := by
  classical
  exact ((circles n).filter (fun c => adjacent c x y)).card

-- A permutation fixing x can exchange any two possible neighbors of x.
private lemma exchange {n : ℕ} {x y z : Fin n} (hy : y ≠ x) (hz : z ≠ x) :
    edgeCount x y = edgeCount x z := by
  classical
  let σ := Equiv.swap y z
  have hx : σ x = x := Equiv.swap_apply_of_ne_of_ne hy.symm hz.symm
  have hσ (c : Equiv.Perm (Fin n)) : relabel σ (relabel σ c) = c := by
    ext i
    simp [relabel,σ]
  have adj (c : Equiv.Perm (Fin n)) (a b : Fin n) :
      adjacent (relabel σ c) (σ a) (σ b) ↔ adjacent c a b := by
    simp [adjacent,relabel]
  have yz : σ y = z := Equiv.swap_apply_left _ _
  have zy : σ z = y := Equiv.swap_apply_right _ _
  unfold edgeCount
  apply card_bij' (fun c _ => relabel σ c) (fun c _ => relabel σ c)
  · intro c hc
    obtain ⟨inside,yes⟩ := mem_filter.mp hc
    exact mem_filter.mpr ⟨relabel_closed σ inside, by simpa only [hx,yz] using (adj c x y).mpr yes⟩
  · intro c hc
    obtain ⟨inside,yes⟩ := mem_filter.mp hc
    exact mem_filter.mpr ⟨relabel_closed σ inside, by simpa only [hx,zy] using (adj c x z).mpr yes⟩
  · exact fun c _ => hσ c
  · exact fun c _ => hσ c

private lemma incidence {n : ℕ} (hn : 3 ≤ n) (x : Fin n) :
    (n-1) * edgeCount x (finRotate n x) = (circles n).card * 2 := by
  classical
  have rot := (rotGeometry hn x).1
  calc
    (n-1) * edgeCount x (finRotate n x) =
        ∑ _y ∈ univ.erase x, edgeCount x (finRotate n x) := by simp
    _ = ∑ y ∈ univ.erase x, edgeCount x y := by
      apply sum_congr rfl
      intro y hy
      exact exchange rot (mem_erase.mp hy).1
    _ = ∑ c ∈ circles n, ((univ.erase x).filter (adjacent c x)).card := by
      simp only [edgeCount,card_filter]
      rw [sum_comm]
    _ = ∑ _c ∈ circles n, 2 := sum_congr rfl (fun c hc => neighbors hn hc x)
    _ = _ := by simp

private lemma totals (n : ℕ) :
    (∑ k ∈ range (n+1), entry n k) = (circles n).card ∧
    (∑ k ∈ range (n+1), k*entry n k) = ∑ x : Fin n, edgeCount x (finRotate n x) := by
  classical
  have less (c : Equiv.Perm (Fin n)) : kept c ∈ range (n+1) := by
    apply mem_range.mpr
    have f := card_filter_le (s:= (univ : Finset (Fin n))) (fun x => adjacent c x (finRotate n x))
    simpa only [card_univ,Fintype.card_fin,Nat.lt_succ_iff,kept] using f
  constructor
  · simpa only [entry] using card_eq_sum_card_fiberwise (s:=circles n) (t:=range (n+1))
        (f:=kept) (fun c _ => less c) |>.symm
  · calc
      (∑ k ∈ range (n+1), k*entry n k) = ∑ c ∈ circles n, kept c := by
        simp only [entry,card_filter,mul_sum,mul_ite,mul_one,mul_zero]
        rw [sum_comm]
        apply sum_congr rfl
        intro c _
        simp [less]
      _ = _ := by
        simp only [kept,edgeCount,card_filter]
        rw [sum_comm]

private lemma exactMean (n : ℕ) (hn : 3 ≤ n) : mean n = 2/((n:ℝ)-1)+2 := by
  classical
  obtain ⟨den,num⟩ := totals n
  have S : (n-1)*(∑ k ∈ range (n+1), k*entry n k) = n*((circles n).card*2) := by
    rw [num,mul_sum]
    simp only [incidence hn]
    simp
  have existsCircle : (circles n).Nonempty :=
    ⟨_,mem_image.mpr ⟨Equiv.refl _,mem_univ _,rfl⟩⟩
  have positive : (0:ℝ) < (circles n).card := by exact_mod_cast card_pos.mpr existsCircle
  have D : (∑ k ∈ range (n+1), (entry n k:ℝ)) = (circles n).card := by exact_mod_cast den
  have S' : (((n-1:ℕ):ℝ))*(∑ k ∈ range (n+1), (k:ℝ)*entry n k) =
      (n:ℝ)*((circles n).card*2) := by exact_mod_cast S
  rw [Nat.cast_sub (by omega : 1≤n),Nat.cast_one] at S'
  have pn : (0:ℝ)<(n:ℝ)-1 := by
    have h : (3:ℝ)≤n := by exact_mod_cast hn
    linarith
  unfold mean
  rw [D]
  field_simp [positive.ne',pn.ne']
  nlinarith only [S']

end CircularNeighbors

theorem OMA.solution : type_of% @OMA.S_oeis_a326404.main := by
  refine ⟨CircularNeighbors.exactMean,?_⟩
  apply (tendsto_add_atTop_iff_nat 3).mp
  have z := (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp (tendsto_add_atTop_nat 2)
  have h := ((tendsto_const_nhds (x:=(2:ℝ))).mul z).add (tendsto_const_nhds (x:=(2:ℝ)))
  simp only [mul_zero,zero_add] at h
  apply h.congr
  intro n
  rw [CircularNeighbors.exactMean _ (by omega)]
  dsimp only [Function.comp_apply]
  push_cast
  ring_nf
