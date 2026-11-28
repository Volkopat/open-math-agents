import OMAStatements.S_oeis_a187156

/-!
# Two diagonal moves of a one-space bishop

In either coordinate the three visited positions are a translate of 010, 101,
012 or 210. Exclude the four pairs in which both coordinates return to their
starting point. For each remaining pair the translations in the two coordinates
are independent. This counts the directed tours on every board at once.
-/

namespace BishopTwoMoves

open Finset OMA.S_oeis_a187156

private def off (d : Fin 4) (j : Fin 3) : ℕ :=
  ![![0,1,0], ![1,0,1], ![0,1,2], ![2,1,0]] d j

private def slots (n : ℕ) (d : Fin 4) : ℕ := if d.val < 2 then n+1 else n

private theorem off_le (d : Fin 4) (j : Fin 3) :
    off d j ≤ if d.val < 2 then 1 else 2 := by decide +revert

private def coord {n : ℕ} (d : Fin 4) (t : Fin (slots n d)) (j : Fin 3) : Fin (n+2) :=
  ⟨t.val + off d j, by
    have ht := t.isLt
    have ho := off_le d j
    unfold slots at ht
    split_ifs at ht ho with h <;> omega⟩

private theorem classify {n : ℕ} (a b c : Fin (n+2))
    (hab : (b:ℤ)-a=1 ∨ (b:ℤ)-a= -1) (hbc : (c:ℤ)-b=1 ∨ (c:ℤ)-b= -1) :
    ∃ (d : Fin 4) (t : Fin (slots n d)),
       coord d t 0 = a ∧ coord d t 1 = b ∧ coord d t 2 = c := by
  rcases hab with h|h <;> rcases hbc with j|j
  · refine ⟨2, ⟨a.val, ?_⟩, ?_⟩
    · change a.val < n; omega
    · simp only [Fin.ext_iff]
      change a.val+0=a.val ∧ a.val+1=b.val ∧ a.val+2=c.val
      omega
  · refine ⟨0, ⟨a.val, ?_⟩, ?_⟩
    · change a.val < n+1; omega
    · simp only [Fin.ext_iff]
      change a.val+0=a.val ∧ a.val+1=b.val ∧ a.val+0=c.val
      omega
  · refine ⟨1, ⟨b.val, ?_⟩, ?_⟩
    · change b.val < n+1; omega
    · simp only [Fin.ext_iff]
      change b.val+1=a.val ∧ b.val+0=b.val ∧ b.val+1=c.val
      omega
  · refine ⟨3, ⟨c.val, ?_⟩, ?_⟩
    · change c.val < n; omega
    · simp only [Fin.ext_iff]
      change c.val+2=a.val ∧ c.val+1=b.val ∧ c.val+0=c.val
      omega

private theorem direction_unique (d e : Fin 4) (x y : ℕ)
    (h0 : x+off d 0=y+off e 0) (h1 : x+off d 1=y+off e 1)
    (h2 : x+off d 2=y+off e 2) : d=e := by
  have key (u v : Fin 4)
      (a : (off u 1 : ℤ)-off u 0 = (off v 1 : ℤ)-off v 0)
      (b : (off u 2 : ℤ)-off u 1 = (off v 2 : ℤ)-off v 1) : u=v := by decide +revert
  apply key <;> omega

private def shapes : Fin 12 → Fin 4 × Fin 4 :=
  ![(0,2),(0,3),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1),(2,2),(2,3),(3,2),(3,3)]

private theorem shape_inj : Function.Injective shapes := by decide +revert

private theorem shape_complete (d e : Fin 4)
    (h : off d 0 ≠ off d 2 ∨ off e 0 ≠ off e 2) :
    ∃ s, shapes s = (d,e) := by decide +revert

private abbrev Placement (n : ℕ) :=
  (s : Fin 12) × (Fin (slots n (shapes s).1) × Fin (slots n (shapes s).2))

private def path {n : ℕ} (z : Placement n) (j : Fin 3) : Square (n+2) :=
  (coord (shapes z.1).1 z.2.1 j, coord (shapes z.1).2 z.2.2 j)

private theorem signs (d : Fin 4) (i j : Fin 3) (h : j.val=i.val+1) :
    (off d j:ℤ)-off d i=1 ∨ (off d j:ℤ)-off d i= -1 := by decide +revert

private theorem distinct (s : Fin 12) (i j : Fin 3) (h : i≠j) :
    off (shapes s).1 i ≠ off (shapes s).1 j ∨ off (shapes s).2 i ≠ off (shapes s).2 j := by
  decide +revert

private theorem good {n : ℕ} (z : Placement n) : IsTour (path z) := by
  constructor
  · intro i j eq
    by_contra ne
    have hx := congrArg (fun p : Square (n+2) => p.1.val) eq
    have hy := congrArg (fun p : Square (n+2) => p.2.val) eq
    simp only [path,coord] at hx hy
    rcases distinct z.1 i j ne with h|h <;> omega
  · have diag (i j : Fin 3) (h : j.val=i.val+1) : IsDiag (delta (path z i) (path z j)) := by
      have hx := signs (shapes z.1).1 i j h
      have hy := signs (shapes z.1).2 i j h
      simp only [IsDiag,delta,path,coord,Nat.cast_add]
      omega
    exact ⟨diag 0 1 rfl, diag 1 2 rfl⟩

private theorem inject {n : ℕ} : Function.Injective (@path n) := by
  rintro ⟨s, x, y⟩ ⟨t, u, v⟩ h
  have hx (j : Fin 3) := congrArg (fun p : Square (n+2) => p.1.val) (congrFun h j)
  have hy (j : Fin 3) := congrArg (fun p : Square (n+2) => p.2.val) (congrFun h j)
  simp only [path, coord] at hx hy
  have e := shape_inj (Prod.ext (direction_unique _ _ _ _ (hx 0) (hx 1) (hx 2))
    (direction_unique _ _ _ _ (hy 0) (hy 1) (hy 2)))
  subst t
  have xx : x=u := Fin.ext (Nat.add_right_cancel (hx 0))
  have yy : y=v := Fin.ext (Nat.add_right_cancel (hy 0))
  subst u; subst v; rfl

private theorem cover {n : ℕ} (p : Fin 3 → Square (n+2)) (h : IsTour p) :
    ∃ z, path z = p := by
  obtain ⟨inj, h01, h12⟩ := h
  obtain ⟨dx,x,x0,x1,x2⟩ := classify _ _ _ h01.1 h12.1
  obtain ⟨dy,y,y0,y1,y2⟩ := classify _ _ _ h01.2 h12.2
  have ne : off dx 0 ≠ off dx 2 ∨ off dy 0 ≠ off dy 2 := by
    by_contra! both
    have bad : p 0 = p 2 := by
      apply Prod.ext
      · rw [←x0,←x2]; exact Fin.ext (by simp only [coord, both.1])
      · rw [←y0,←y2]; exact Fin.ext (by simp only [coord, both.2])
    exact (by decide : (0 : Fin 3) ≠ 2) (inj bad)
  obtain ⟨s, hs⟩ := shape_complete dx dy ne
  have ex := congrArg Prod.fst hs
  have ey := congrArg Prod.snd hs
  dsimp at ex ey
  subst dx; subst dy
  refine ⟨⟨s,x,y⟩, ?_⟩
  funext j
  fin_cases j
  · exact Prod.ext x0 y0
  · exact Prod.ext x1 y1
  · exact Prod.ext x2 y2

private theorem count (n : ℕ) : a (n+2) = 8 * (n+1)*n + 4*n^2 := by
  classical
  let f : Placement n → {p : Fin 3 → Square (n+2) // IsTour p} := fun z => ⟨path z,good z⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y eq; exact inject (congrArg Subtype.val eq)
    · rintro ⟨p,h⟩
      obtain ⟨z,hz⟩ := cover p h
      exact ⟨z, Subtype.ext hz⟩
  have eq := Fintype.card_congr (Equiv.ofBijective f hf)
  rw [Fintype.card_subtype] at eq
  change (univ.filter IsTour).card = _
  rw [←eq,Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  simp only [Fin.sum_univ_succ, Finset.univ_unique, Finset.sum_singleton]
  simp [shapes, slots, Fin.isValue, Matrix.cons_val] <;> ring

private theorem quad (n : ℕ) (hn : 1 < n) :
    (a n : ℤ) = 12*(n:ℤ)^2 - 40*n + 32 := by
  obtain ⟨m,rfl⟩ : ∃ m, n=m+2 := ⟨n-2, by omega⟩
  rw [count]
  push_cast
  ring

private theorem rec (n : ℕ) (hn : 4<n) :
    (a n : ℤ) = 3 * a (n-1) - 3*a (n-2) + a (n-3) := by
  rw [quad n (by omega),quad (n-1) (by omega),quad (n-2) (by omega),quad (n-3) (by omega)]
  push_cast [show 1≤n by omega, show 2≤n by omega, show 3≤n by omega]
  ring

open PowerSeries in
private theorem series :
    mk (fun n => (a n : ℤ)) * (1-X)^3 = 4*X^3*(5+X) := by
  let A : ℤ⟦X⟧ := mk fun n => (a n : ℤ)
  change A * _ = _
  have den : A*(1-X)^3 = A - C (3:ℤ)*(A*X^1) + C (3:ℤ)*(A*X^2) - A*X^3 := by
    simp only [map_ofNat]
    ring
  have num : 4*(X : ℤ⟦X⟧)^3*(5+X) = C (20:ℤ)*X^3 + C (4:ℤ)*X^4 := by
    simp only [map_ofNat]
    ring
  rw [den,num]
  ext n
  simp only [map_sub,map_add,coeff_C_mul_X_pow]
  simp only [coeff_C_mul,coeff_mul_X_pow',A,coeff_mk]
  by_cases small : n≤4
  · have a0 : a 0 = 0 := by decide
    have a1 : a 1 = 0 := by decide
    interval_cases n <;> norm_num [a0,a1,count]
  · have h := rec n (by omega)
    simp only [show 1≤n by omega, show 2≤n by omega, show 3≤n by omega,
      show n≠3 by omega,show n≠4 by omega,if_true,if_false]
    linarith

end BishopTwoMoves

theorem OMA.solution : type_of% @OMA.S_oeis_a187156.main :=
  ⟨BishopTwoMoves.quad, BishopTwoMoves.rec, BishopTwoMoves.series⟩
