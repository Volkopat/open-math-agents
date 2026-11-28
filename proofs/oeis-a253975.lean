import OMAStatements.S_oeis_a253975
import Mathlib

open OMA.S_oeis_a253975 in
theorem OMA.solution : type_of% @OMA.S_oeis_a253975.main := by
  intro n _
  let e := 2*n
  have pred (j : ℕ) : 3^j-1+1=3^j := Nat.sub_add_cancel (Nat.succ_le_of_lt (pow_pos (by decide) j))
  have mono {i j : ℕ} : 3^i≤3^j ↔ i≤j := Nat.pow_le_pow_iff_right (by decide)
  have inj := Nat.pow_right_injective (a:=3) (by decide)
  have prod (x y : ℕ) : x*y+x+y=3^e-1 ↔ (x+1)*(y+1)=3^e := by
    have := pred e
    constructor <;> intro h <;> nlinarith
  let F (i : Fin n) : Representations (3^e-1) := by
    let j := i.val+1
    have lo : 3^1≤3^j := mono.mpr (by dsimp [j]; omega)
    have hi : j≤e-j := by dsimp [j,e]; omega
    refine ⟨(3^(e-j)-1,3^j-1),by dsimp; omega,Nat.sub_le_sub_right (mono.mpr hi) _,(prod ..).mpr ?_⟩
    rw [pred,pred,←pow_add,Nat.sub_add_cancel (by omega : j≤e)]
  refine ⟨_,⟨Equiv.ofBijective F ⟨?_,?_⟩⟩⟩
  · intro i j h
    have h := congrArg (fun v : Representations (3^e-1) ↦ v.1.2+1) h
    simp only [F,pred] at h
    exact Fin.ext (by have := inj h; omega)
  · rintro ⟨⟨x,y⟩,hy,order,h⟩
    change 1<y at hy
    change y≤x at order
    have eq := (prod x y).mp h
    obtain ⟨u,_,hu⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (eq ▸ dvd_mul_right (x+1) (y+1))
    obtain ⟨v,_,hv⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (eq ▸ dvd_mul_left (y+1) (x+1))
    rw [hu,hv,←pow_add] at eq
    have sum := inj eq
    have le := mono.mp (show 3^v≤3^u by omega)
    have pos : 0<v := by by_contra! z; simp [show v=0 by omega] at hv; omega
    refine ⟨⟨v-1,by dsimp [e] at sum; omega⟩,Subtype.ext ?_⟩
    change (3^(e-(v-1+1))-1,3^(v-1+1)-1)=(x,y)
    rw [show v-1+1=v by omega,show e-v=u by omega,←hu,←hv]
    simp
