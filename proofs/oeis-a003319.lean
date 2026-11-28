import OMAStatements.S_oeis_a003319
import Mathlib

/-! For Mikhail Kurkov’s array conjecture, adding a return to state zero gives a factorial array. A first-return decomposition and the decomposition of permutations at their least invariant prefix give the same recurrence. -/
namespace Deldor14.ConnectedArray
open Finset OMA.S_oeis_a003319
private def B : ℕ → ℕ → ℕ
  | 0,_ => 1
  | n+1,k => (k+1)*B n (k+1)+∑ j ∈ range (k+1), B n j
private lemma closed (n k : ℕ) : B n k=(n+1).factorial*(k+n).choose n := by
  induction n generalizing k with
  | zero => simp [B]
  | succ n ih =>
    rw [B,ih]
    simp_rw [ih]
    rw [←mul_sum,Nat.sum_range_add_choose,Nat.factorial_succ (n+1)]
    have e : (k+1)*(k+n+1).choose n=(n+1)*(k+n+1).choose (n+1) := by
      have h1 := Nat.choose_mul_succ_eq (k+n) n
      have h2 := Nat.add_one_mul_choose_eq (k+n) n
      rw [show k+n+1-n=k+1 by omega] at h1
      nlinarith
    rw [show k+1+n=k+n+1 by omega,show k+(n+1)=k+n+1 by omega]
    nlinarith [congrArg (fun z : ℕ => (n+1).factorial*z) e]
private lemma at_zero (n : ℕ) : B n 0=(n+1).factorial := by simp [closed]
private lemma first_return (n k : ℕ) : B n (k+1)=A n k+
    ∑ j ∈ range n, A j k * B (n-1-j) 0 := by
  induction n generalizing k with
  | zero => simp [B,A]
  | succ n ih =>
    rw [B,sum_range_succ' (fun u => B n u),ih k.succ]
    simp_rw [ih]
    rw [sum_add_distrib,mul_add,mul_sum]
    have swap :
        ∑ x ∈ range (k+1), ∑ j ∈ range n, A j x * B (n-1-j) 0 =
        ∑ j ∈ range n, (∑ x ∈ range (k+1), A j x)*B (n-1-j) 0 := by
      rw [sum_comm]
      simp_rw [sum_mul]
    rw [swap]
    rw [sum_range_succ' (fun j => A j k * B (n+1-1-j) 0)]
    have term (j r : ℕ) : A (j+1) k*r=(k+2)*(A j (k+1)*r)+(∑ x ∈ range (k+1), A j x)*r := by
      rw [A,add_mul,mul_assoc]
    simp only [Nat.add_sub_cancel,Nat.sub_zero,term,show A 0 k=1 from rfl,one_mul,
      Finset.sum_add_distrib,Nat.sub_sub,Nat.add_comm 1,Nat.succ_eq_add_one]
    rw [show A (n+1) k=(k+2)*A n (k+1)+∑ x ∈ range (k+1), A n x from by rw [A]]
    simp only [show k+1+1=k+2 by omega]
    ac_nf
    omega
theorem convolution (n : ℕ) :
    (n+2).factorial=(n+1).factorial+A n 0+
      ∑ j ∈ range n, A j 0*(n-j).factorial := by
  have eq := at_zero (n+1)
  rw [B] at eq
  simp only [zero_add,one_mul,sum_range_one] at eq
  rw [first_return,at_zero] at eq
  have sums : ∑ j ∈ range n, A j 0 * B (n-1-j) 0 =
      ∑ j ∈ range n, A j 0*(n-j).factorial := by
    apply sum_congr rfl
    intro j hj
    have := mem_range.mp hj
    rw [at_zero,show n-1-j+1=n-j by omega]
  rw [sums] at eq
  exact eq.symm.trans (by ac_rfl)
end Deldor14.ConnectedArray

namespace Deldor14.ConnectedBlock
open Equiv Finset OMA.S_oeis_a003319
private def Keeps {n : ℕ} (s : Perm (Fin n)) (j : ℕ) : Prop :=
  ∀ i : Fin n, i.val < j → (s i).val < j
private noncomputable def first {n : ℕ} (s : Perm (Fin n)) : ℕ :=
  sInf {j : ℕ | 0 < j ∧ Keeps s j}
private lemma first_spec {n : ℕ} (s : Perm (Fin n)) (hn : 0 < n) :
    0 < first s ∧ Keeps s (first s) ∧ first s ≤ n := by
  have m : n ∈ {j : ℕ | 0 < j ∧ Keeps s j} := ⟨hn,fun i _ => (s i).isLt⟩
  obtain ⟨a,b⟩ := Nat.sInf_mem (Set.nonempty_of_mem m)
  exact ⟨a,b,Nat.sInf_le m⟩
private lemma first_le {n j : ℕ} (s : Perm (Fin n)) (hj : 0 < j) (h : Keeps s j) :
    first s ≤ j := Nat.sInf_le (show j ∈ {u : ℕ | 0 < u ∧ Keeps s u} from ⟨hj,h⟩)
private def split {n j : ℕ} (h : j ≤ n) : (Fin j ⊕ Fin (n-j)) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (by omega))
private def join {n j : ℕ} (h : j ≤ n) (p : Perm (Fin j)) (q : Perm (Fin (n-j))) :
    Perm (Fin n) := (split h).permCongr (p.sumCongr q)
private lemma left_val {n j : ℕ} (h : j ≤ n) (i : Fin j) :
    ((split h) (Sum.inl i)).val=i.val := rfl
private lemma right_val {n j : ℕ} (h : j ≤ n) (i : Fin (n-j)) :
    ((split h) (Sum.inr i)).val=j+i.val := rfl
private lemma left_join {n j : ℕ} (h : j ≤ n) (p : Perm (Fin j)) (q : Perm (Fin (n-j))) (i : Fin j) :
    ((join h p q) (split h (Sum.inl i))).val=(p i).val := by
  simp [join,permCongr_apply,left_val]
private lemma keeps_join {n j t : ℕ} (h : j ≤ n) (p : Perm (Fin j)) (q : Perm (Fin (n-j))) (ht : t ≤ j) :
    Keeps (join h p q) t ↔ Keeps p t := by
  constructor
  · intro s i hi
    exact (left_join h p q i) ▸ s (split h (.inl i)) (by simpa [left_val] using hi)
  · intro s i hi
    let a : Fin j := ⟨i.val,by omega⟩
    have e : i = split h (.inl a) := Fin.ext rfl
    rw [e,left_join]
    exact s a hi
private lemma represent {n j : ℕ} (h : j ≤ n) (s : Perm (Fin n)) (hs : Keeps s j) :
    ∃ p q, join h p q = s := by
  let e := split h
  let u := e.symm.permCongr s
  have maps : Set.MapsTo u (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro _ ⟨i,rfl⟩
    have val : (s (e (.inl i))).val < j := hs _ (by exact i.isLt)
    have eq : e (u (.inl i))=s (e (.inl i)) := by simp [u,permCongr_apply]
    cases v : u (.inl i) with
    | inl x => exact ⟨x,rfl⟩
    | inr y =>
      rw [v] at eq
      rw [← eq] at val
      have bad : j+y.val<j := val
      omega
  obtain ⟨⟨p,q⟩,hpu⟩ := Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl maps
  refine ⟨p,q,?_⟩
  change e.permCongr (p.sumCongr q)=s
  change p.sumCongr q=u at hpu
  rw [hpu]
  exact e.permCongr.apply_symm_apply s
private lemma join_inj {n j : ℕ} (h : j ≤ n) :
    Function.Injective (fun z : Perm (Fin j) × Perm (Fin (n-j)) => join h z.1 z.2) := by
  intro x y eq
  exact Perm.sumCongrHom_injective ((split h).permCongr.injective eq)
private noncomputable def ix {n : ℕ} (s : Perm (Fin (n+1))) : Fin (n+1) :=
  ⟨first s-1,by have e:=first_spec s (by omega);omega⟩
private lemma ix_iff {n : ℕ} (s : Perm (Fin (n+1))) (i : Fin (n+1)) :
    ix s=i ↔ first s=i.val+1 := by
  have pos := (first_spec s (by omega)).1
  rw [Fin.ext_iff]
  change first s-1=i.val ↔ _
  omega
set_option maxHeartbeats 1200000 in
private lemma fiber_equiv {n : ℕ} (i : Fin (n+1)) :
    Nonempty (({p : Perm (Fin (i.val+1)) // IsConnected p} × Perm (Fin ((n+1)-(i.val+1)))) ≃
      {s : Perm (Fin (n+1)) // ix s=i}) := by
  classical
  let j:=i.val+1
  have hj : j≤n+1 := i.isLt
  have jp : 0<j := by dsimp [j];omega
  let combine (v : {p : Perm (Fin j) // IsConnected p} × Perm (Fin (n+1-j))) :
      {s : Perm (Fin (n+1)) // ix s=i} := by
    let w:=join hj v.1.val v.2
    refine ⟨w,(ix_iff w i).mpr ?_⟩
    have h0 : Keeps w j := (keeps_join hj _ _ le_rfl).mpr (fun x _ => (v.1.val x).isLt)
    have bound := first_le w jp h0
    have spec := first_spec w (by omega)
    by_contra hh
    have small : first w < j := by change first w ≠ j at hh;omega
    exact v.1.2 (first w) spec.1 small ((keeps_join hj _ _ bound).mp spec.2.1)
  refine ⟨Equiv.ofBijective combine ⟨?_,?_⟩⟩
  · intro x y h
    have he := join_inj hj (a₁:=(x.1.val,x.2)) (a₂:=(y.1.val,y.2)) (congrArg Subtype.val h)
    have hfst : x.1.val = y.1.val := congrArg Prod.fst he
    have hsnd := congrArg (fun z : Perm (Fin j) × Perm (Fin (n+1-j)) => z.2) he
    exact Prod.ext (Subtype.ext hfst) hsnd
  · rintro ⟨s,hs⟩
    have eq : first s=j := (ix_iff s i).mp hs
    have spec := first_spec s (by omega)
    obtain ⟨p,q,hpq⟩ := represent hj s (eq ▸ spec.2.1)
    have connected : IsConnected p := by
      intro t tp tj ht
      have hkeep := (keeps_join hj p q tj.le).mpr ht
      rw [hpq] at hkeep
      have := first_le s tp hkeep
      omega
    exact ⟨(⟨p,connected⟩,q),Subtype.ext hpq⟩
theorem factorial_blocks (n : ℕ) :
    (n+1).factorial=∑ j ∈ range (n+1), a (j+1)*(n-j).factorial := by
  classical
  have full := Nat.card_congr (Equiv.sigmaFiberEquiv (@ix n))
  rw [Nat.card_sigma,Nat.card_perm,Nat.card_fin] at full
  rw [←full,←Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i _
  have h := Nat.card_congr (fiber_equiv i).some
  rw [Nat.card_prod,Nat.card_perm,Nat.card_fin] at h
  simpa [a] using h.symm
end Deldor14.ConnectedBlock

namespace Deldor14.ConnectedConjecture
open Finset OMA.S_oeis_a003319 Deldor14.ConnectedBlock Deldor14.ConnectedArray
private lemma agree (n : ℕ) : a (n+2)=A n 0 := by
  have one : a 1=1 := by simpa using (factorial_blocks 0).symm
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have f := factorial_blocks (n+1)
    rw [sum_range_succ,sum_range_succ' (fun j => a (j+1)*((n+1)-j).factorial)] at f
    simp only [zero_add,Nat.sub_zero,Nat.sub_self,Nat.factorial_zero,mul_one,one,one_mul,
      Nat.add_sub_add_right] at f
    have s : ∑ j ∈ range n, a (j+1+1)*(n-j).factorial =
        ∑ j ∈ range n, A j 0*(n-j).factorial := by
      apply sum_congr rfl
      intro j hj
      rw [ih j (mem_range.mp hj)]
    rw [s] at f
    have g := convolution n
    simp only [show n+1+1=n+2 by omega] at f
    omega
theorem full : type_of% @OMA.S_oeis_a003319.main := by
  intro n hn
  simpa [Nat.sub_add_cancel (show 2≤n by omega)] using agree (n-2)
end Deldor14.ConnectedConjecture
theorem OMA.solution : type_of% @OMA.S_oeis_a003319.main := Deldor14.ConnectedConjecture.full
