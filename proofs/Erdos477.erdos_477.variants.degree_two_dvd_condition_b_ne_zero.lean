import FormalConjectures.ErdosProblems.«477»
open Polynomial

set_option maxHeartbeats 800000 in

theorem OMA.solution : type_of% @Erdos477.erdos_477.variants.degree_two_dvd_condition_b_ne_zero := by
  classical
  intro a b c ha hb _ F A
  by_contra hn
  push_neg at hn
  let f : ℤ → ℤ := fun x => a*x^2+b*x+c
  have hf (x : ℤ) : F.eval x = f x := by simp [F,f]
  have hM : 2*b ≠ 0 := by omega
  have hd (x : ℤ) : f x - f (-x) = 2*b*x := by dsimp [f]; ring
  have hinj : Set.InjOn (fun u : ℤ => u % (2*b)) A := by
    intro u hu v hv he
    obtain ⟨k,hk⟩ := Int.ModEq.dvd (show u ≡ v [ZMOD 2*b] from he)
    obtain ⟨p,_,hp⟩ := hn (u + f k)
    have h1 := hp (u, f k) ⟨⟨hu,⟨k,hf k⟩⟩,rfl⟩
    have h2 := hp (v, f (-k)) ⟨⟨hv,⟨-k,hf (-k)⟩⟩,by
      change u + f k = v + f (-k)
      linarith [hd k]⟩
    exact congrArg Prod.fst (h1.trans h2.symm)
  have hfin : A.Finite := by
    apply Set.Finite.of_finite_image (f := fun u : ℤ => u % (2*b))
    · apply (Set.finite_Ico (0 : ℤ) |2*b|).subset
      rintro _ ⟨x,_,rfl⟩
      exact ⟨Int.emod_nonneg x hM, Int.emod_lt_abs x hM⟩
    · exact hinj
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · obtain ⟨U,hU⟩ := hfin.bddAbove
    obtain ⟨p,⟨⟨hp,⟨x,hx⟩⟩,hz⟩,_⟩ := hn (U+c+b^2+1)
    have h1 := hU hp
    have h2 : a*x^2+b*x+c ≤ c+b^2 := by
      nlinarith [sq_nonneg x, sq_nonneg (2*x-b), mul_nonneg (by omega : (0:ℤ) ≤ -a-1) (sq_nonneg x)]
    change F.eval x = p.2 at hx
    rw [hf] at hx
    dsimp [f] at hx
    linarith
  · obtain ⟨L,hL⟩ := hfin.bddBelow
    obtain ⟨p,⟨⟨hp,⟨x,hx⟩⟩,hz⟩,_⟩ := hn (L+c-b^2-1)
    have h1 := hL hp
    have h2 : c-b^2 ≤ a*x^2+b*x+c := by
      nlinarith [sq_nonneg x, sq_nonneg (2*x+b), mul_nonneg (by omega : (0:ℤ) ≤ a-1) (sq_nonneg x)]
    change F.eval x = p.2 at hx
    rw [hf] at hx
    dsimp [f] at hx
    linarith
