import OMAStatements.S_oeis_a269202
import Mathlib

namespace OMA.Allow269202
open OMA.S_oeis_a269202 Finset PowerSeries

private abbrev Col := Fin 2 → Fin 4
private abbrev Word (n : ℕ) := Fin n → Col
private abbrev Budget := Fin 2
private def hit (d e : Fin 4) : ℕ := if d.val + e.val = 3 then 1 else 0
private def cost (p q : Col) : ℕ :=
  (∑ r, hit (p r) (q r)) + hit (p 0) (q 1) + hit (p 1) (q 0)
private def weight (n : ℕ) (p : Col) (x : Word n) : ℕ :=
  ∑ i : Fin n, cost ((Fin.cons p x : Word (n+1)) i.castSucc) (x i)

private theorem original (m : ℕ) (x : Fin 2 → Fin (m+1) → Fin 4) :
    pairsTotallingThree m x = weight m (fun r => x r 0) (fun i r => x r i.succ) := by
  have e : (Fin.cons (fun r => x r 0) (fun (i : Fin m) r => x r i.succ) : Word (m+1))
      = (fun i r => x r i) := Fin.cons_self_tail (fun (i : Fin (m+1)) (r : Fin 2) => x r i)
  unfold pairsTotallingThree weight
  rw [e]
  simp only [cost, hit, sum_add_distrib]
  rw [← Fintype.sum_prod_type_right' (fun (r : Fin 2) (i : Fin m) => if (x r i.castSucc).val + (x r i.succ).val = 3 then (1 : ℕ) else 0)]
  simp only [sum_boole,Nat.cast_id]

private abbrev W (n : ℕ) (b : Budget) (p : Col) := {x : Word n // weight n p x ≤ b.val}
private abbrev Next (b : Budget) (p : Col) := {q : Col // cost p q ≤ b.val}
private def leftOver (b : Budget) (p q : Col) : Budget := ⟨b.val - cost p q,by omega⟩

private theorem addWeight (n : ℕ) (p q : Col) (x : Word n) :
    weight (n+1) p (Fin.cons q x) = cost p q + weight n q x := by
  unfold weight
  rw [Fin.sum_univ_succ]
  rfl

private def split (n : ℕ) (b : Budget) (p : Col) :
    W (n+1) b p ≃ (Σ q : Next b p, W n (leftOver b p q.val) q.val) where
  toFun z := by
    let x := z.val
    let t := fun i : Fin n => x i.succ
    have h := z.property
    change weight (n+1) p x ≤ b.val at h
    have e : Fin.cons (x 0) t = x := Fin.cons_self_tail x
    rw [← e,addWeight] at h
    exact ⟨⟨x 0,by omega⟩,⟨t,by change weight n (x 0) t ≤ b.val - cost p (x 0); omega⟩⟩
  invFun z := by
    refine ⟨Fin.cons z.1.val z.2.val,?_⟩
    rw [addWeight]
    have h := z.2.property
    change _ ≤ b.val - cost p z.1.val at h
    have := z.1.property
    omega
  left_inv z := Subtype.ext (Fin.cons_self_tail _)
  right_inv z := by rcases z with ⟨⟨q,hq⟩,⟨x,hx⟩⟩; rfl

private def op (f : Budget → Col → ℤ) (b : Budget) (p : Col) :=
  ∑ q : Next b p, f (leftOver b p q.val) q.val
private def c : ℕ → Budget → Col → ℤ
  | 0, _, _ => 1
  | n+1, b, p => op (c n) b p

private theorem paths (n : ℕ) (b : Budget) (p : Col) : (Fintype.card (W n b p) : ℤ) = c n b p := by
  induction n generalizing b p with
  | zero =>
    have : Unique (W 0 b p) :=
      { default := ⟨Fin.elim0,by simp [weight]⟩
        uniq := fun z => Subtype.ext (funext fun i => i.elim0) }
    simp [c]
  | succ n ih =>
    rw [Fintype.card_congr (split n b p),Fintype.card_sigma,Nat.cast_sum]
    apply Fintype.sum_congr
    intro q
    exact ih _ _

private def splitFirst (m : ℕ) :
    {x : Fin 2 → Fin (m+1) → Fin 4 // pairsTotallingThree m x ≤ 1} ≃
      (Σ p : Col, W m 1 p) where
  toFun z := ⟨fun r => z.val r 0,⟨fun i r => z.val r i.succ,by
    rw [← original]; exact z.property⟩⟩
  invFun z := ⟨fun r i => (Fin.cons z.1 z.2.val : Word (m+1)) i r,by
    rw [original]; exact z.2.property⟩
  left_inv z := by
    apply Subtype.ext
    funext r i
    exact congrFun (congrFun (Fin.cons_self_tail (fun j s => z.val s j)) i) r
  right_inv z := by rcases z with ⟨p,⟨x,hx⟩⟩; rfl

private theorem count (n : ℕ) : (a (n+1) : ℤ) = ∑ p, c n 1 p := by
  have h := Fintype.card_congr (splitFirst n)
  rw [Fintype.card_subtype,Fintype.card_sigma] at h
  change (#{x : Fin 2 → Fin (n+1) → Fin 4 | pairsTotallingThree n x ≤ 1} : ℤ) = _
  rw [h,Nat.cast_sum]
  apply Fintype.sum_congr
  exact paths n 1

/-- Continuation counts indexed by length, allowance, and whether the two entries agree. -/
private def table (k : Fin 5) (b : Budget) (p : Col) : ℤ :=
  let vals : Fin 5 → Fin 2 → Fin 2 → ℤ :=
    ![![![1,1],![1,1]], ![![9,4],![9,12]], ![![51,26],![99,74]],
      ![![309,154],![741,554]], ![![1851,926],![5547,3822]]]
  vals k b (if p 0 = p 1 then 0 else 1)

private theorem stepTable : ∀ k : Fin 4, ∀ b p,
    table k.succ b p = op (table k.castSucc) b p := by decide +kernel

private theorem tab (k : Fin 5) : c k.val = table k := by
  induction k using Fin.induction with
  | zero =>
    funext b p
    change 1 = table 0 b p
    revert b p
    decide +kernel
  | succ k ih =>
    change c k.val = table k.castSucc at ih
    funext b p
    change op (c k.val) b p = _
    rw [ih,stepTable]

private theorem vectorRec (n : ℕ) (b : Budget) (p : Col) :
    c (n+4) b p = 10*c (n+3) b p - 13*c (n+2) b p - 60*c (n+1) b p - 36*c n b p := by
  induction n generalizing b p with
  | zero =>
    simp only [Nat.zero_add,show c 4 = table 4 from tab 4,show c 3 = table 3 from tab 3,
      show c 2 = table 2 from tab 2,show c 1 = table 1 from tab 1,show c 0 = table 0 from tab 0]
    revert b p
    decide +kernel
  | succ n ih =>
    change op (c (n+4)) b p = 10*op (c (n+3)) b p - 13*op (c (n+2)) b p -
      60*op (c (n+1)) b p - 36*op (c n) b p
    unfold op
    simp_rw [ih]
    simp only [sum_sub_distrib,← mul_sum]

private theorem initial : ∀ k : Fin 5,
    (∑ p, table k 1 p) = ![16,180,1284,9612,68052] k := by decide +kernel

private theorem term1 : a 1 = 16 := by
  have h := count 0
  rw [show c 0 = table 0 from tab 0,initial] at h
  change (a 1 : ℤ) = 16 at h
  exact_mod_cast h

private theorem term2 : a 2 = 180 := by
  have h := count 1
  rw [show c 1 = table 1 from tab 1,initial] at h
  change (a 2 : ℤ) = 180 at h
  exact_mod_cast h

private theorem term3 : a 3 = 1284 := by
  have h := count 2
  rw [show c 2 = table 2 from tab 2,initial] at h
  change (a 3 : ℤ) = 1284 at h
  exact_mod_cast h

private theorem term4 : a 4 = 9612 := by
  have h := count 3
  rw [show c 3 = table 3 from tab 3,initial] at h
  change (a 4 : ℤ) = 9612 at h
  exact_mod_cast h

private theorem recInt (m : ℕ) :
    (a (m+5) : ℤ) = 10*a (m+4) - 13*a (m+3) - 60*a (m+2) - 36*a (m+1) := by
  have h := Finset.sum_congr (s₁:=(univ : Finset Col)) rfl (fun p _ => vectorRec m 1 p)
  simp only [sum_sub_distrib,← mul_sum] at h
  simpa only [count] using h

private theorem recQ (m : ℕ) :
    (a (m+5) : ℚ) = 10*a (m+4) - 13*a (m+3) - 60*a (m+2) - 36*a (m+1) := by
  exact_mod_cast recInt m

private def f (n : ℕ) : ℚ :=
  (6 * (-678 * (-1) ^ n + 335 * 6 ^ n) + 56 * (144 * (-1) ^ n + 25 * 6 ^ n) * n) / 1029

private theorem explicit (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = f n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n ≤ 4
    · interval_cases n <;> norm_num [term1,term2,term3,term4,f]
    obtain ⟨m,rfl⟩ : ∃ m, n=m+5 := ⟨n-5,by omega⟩
    rw [recQ,ih (m+4) (by omega) (by omega),ih (m+3) (by omega) (by omega),
      ih (m+2) (by omega) (by omega),ih (m+1) (by omega) (by omega)]
    simp only [f,pow_add,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
    ring

private theorem generating :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1 + X) ^ 2 * (1 - 6 * X) ^ 2) =
      4 * X * (4 + 5 * X - 77 * X ^ 2 + 18 * X ^ 3) := by
  let S := PowerSeries.mk (fun n => (a n : ℚ))
  change S * _ = _
  have lhs : S*((1+X)^2*(1-6*X)^2) = S - 10 • (S*X^1) + 13 • (S*X^2) +
      60 • (S*X^3) + 36 • (S*X^4) := by simp only [nsmul_eq_mul]; ring
  have rhs : (4*X*(4+5*X-77*X^2+18*X^3) : PowerSeries ℚ) =
      16 • X^1 + 20 • X^2 - 308 • X^3 + 72 • X^4 := by simp only [nsmul_eq_mul]; ring
  rw [lhs,rhs]
  ext n
  simp only [map_add,map_sub,map_nsmul,coeff_mul_X_pow',coeff_X_pow,S,coeff_mk]
  by_cases h : n ≤ 4
  · interval_cases n <;> norm_num [term1,term2,term3,term4,show a 0 = 0 from rfl]
  obtain ⟨m,rfl⟩ : ∃ m, n=m+5 := ⟨n-5,by omega⟩
  simp only [if_pos (show 1 ≤ m+5 by omega),if_pos (show 2 ≤ m+5 by omega),
    if_pos (show 3 ≤ m+5 by omega),if_pos (show 4 ≤ m+5 by omega),
    if_neg (show m+5 ≠ 1 by omega),if_neg (show m+5 ≠ 2 by omega),
    if_neg (show m+5 ≠ 3 by omega),if_neg (show m+5 ≠ 4 by omega),
    nsmul_eq_mul,show m+5-1=m+4 by omega,show m+5-2=m+3 by omega,
    show m+5-3=m+2 by omega,show m+5-4=m+1 by omega]
  norm_num
  linarith only [recQ m]

theorem result : type_of% @OMA.S_oeis_a269202.main := by
  refine ⟨?_,generating,explicit⟩
  intro n hn
  obtain ⟨m,rfl⟩ : ∃ m, n=m+5 := ⟨n-5,by omega⟩
  exact recInt m

end OMA.Allow269202

theorem OMA.solution : type_of% @OMA.S_oeis_a269202.main := OMA.Allow269202.result
