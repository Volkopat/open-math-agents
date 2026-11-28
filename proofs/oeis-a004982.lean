import OMAStatements.S_oeis_a004982

namespace A004982Proof

open OMA.S_oeis_a004982

/-- Modulo any odd modulus one can translate the progression to four times consecutive integers. -/
private theorem shifted_progression (d t : ℕ) (ht : 3 ≡ 4*t [MOD d]) (n : ℕ) :
    (∏ k ∈ Finset.range n, (4*k+3)) ≡ 4^n * t.ascFactorial n [MOD d] := by
  induction n with
  | zero => simp [Nat.ModEq]
  | succ n ih =>
    rw [Finset.prod_range_succ, pow_succ, Nat.ascFactorial_succ]
    have hterm : 4*n+3 ≡ 4*(t+n) [MOD d] := by
      simpa only [mul_add, add_comm (4*t)] using ht.add_left (4*n)
    convert ih.mul hterm using 1
    ring

theorem factorial_dvd_numerator (n : ℕ) :
    n.factorial ∣ 2^n * ∏ k ∈ Finset.range n, (4*k+3) := by
  let d := ordCompl[2] n.factorial
  have hodd : Odd d := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact Nat.not_dvd_ordCompl Nat.prime_two n.factorial_ne_zero
  obtain ⟨r,hr⟩ := hodd
  let t := 3*(r+1)^2
  have ht : 3 ≡ 4*t [MOD d] := by
    have h : 4*t = 3 + (3*(d+2))*d := by dsimp [t]; rw [hr]; ring
    rw [h, Nat.modEq_add_mul_modulus_iff]
  have hfac : d ∣ t.ascFactorial n :=
    (Nat.ordCompl_dvd n.factorial 2).trans (t.factorial_dvd_ascFactorial n)
  have hd : d ∣ ∏ k ∈ Finset.range n, (4*k+3) :=
    Nat.modEq_zero_iff_dvd.mp ((shifted_progression d t ht n).trans
      (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right hfac _)))
  have htwo : ordProj[2] n.factorial ∣ 2^n := by
    apply pow_dvd_pow
    simpa using Nat.factorization_factorial_le_div_pred Nat.prime_two n
  simpa only [d,Nat.ordProj_mul_ordCompl_eq_self] using Nat.mul_dvd_mul htwo hd

private abbrev numeratorUnits (p j : ℕ) := ∏ r ∈ Finset.Ico 1 p, (r + (4*j + (3-r%4))*p)
private abbrev denominatorUnits (p j : ℕ) := ∏ r ∈ Finset.Ico 1 p, (r + j*p)

/-- An injective change of variable preserving a finite set permutes its factors. -/
private theorem prod_reindex_self (s : Finset ℕ) (idx f : ℕ → ℕ)
    (hmaps : ∀ r ∈ s, idx r ∈ s) (hinj : Set.InjOn idx (s : Set ℕ)) :
    (∏ r ∈ s, f (idx r)) = ∏ r ∈ s, f r := by
  have hi : s.image idx = s := Finset.eq_of_subset_of_card_le
    (Finset.image_subset_iff.mpr hmaps) (Finset.card_image_of_injOn hinj).ge
  calc
    _ = ∏ x ∈ s.image idx, f x := (Finset.prod_image hinj).symm
    _ = _ := by rw [hi]

/-- Lift a residue to the unique number congruent to three mod four in the block. -/
theorem numerator_block (p j : ℕ) (hp : p.Prime) (hp4 : p ≡ 1 [MOD 4]) :
    (∏ k ∈ Finset.range p, (4*(p*j+k)+3)) =
      p*(4*j+3) * ∏ r ∈ Finset.Ico 1 p, (r+(4*j+(3-r%4))*p) := by
  change p%4 = 1 at hp4
  let lift (r : ℕ) := r + (3-r%4)*p
  let idx (r : ℕ) := lift r / 4
  have hl (r : ℕ) : 4*idx r+3 = lift r := by
    have h : lift r % 4 = 3 := by
      dsimp [lift]
      rw [Nat.add_mod, Nat.mul_mod, hp4]
      have hr := Nat.mod_lt r (by decide : 0 < 4)
      omega
    dsimp [idx]
    omega
  have hmaps (r : ℕ) (hr : r ∈ Finset.range p) : idx r ∈ Finset.range p := by
    simp only [Finset.mem_range] at *
    have hb : (3-r%4)*p ≤ 3*p := Nat.mul_le_mul_right p (Nat.sub_le ..)
    dsimp [idx,lift]
    omega
  have hinj : Set.InjOn idx ((Finset.range p : Finset ℕ) : Set ℕ) := by
    intro u hu v hv he
    have hh : lift u = lift v := by rw [← hl u, ← hl v, he]
    have hm := congrArg (fun x => x % p) hh
    simpa [lift, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Finset.mem_range.mp hu),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hv)] using hm
  calc
    _ = ∏ r ∈ Finset.range p, (4*(p*j+idx r)+3) :=
      (prod_reindex_self (Finset.range p) idx (fun k => 4*(p*j+k)+3) hmaps hinj).symm
    _ = ∏ r ∈ Finset.range p, (r+(4*j+(3-r%4))*p) := by
      apply Finset.prod_congr rfl
      intro r _
      have h := hl r
      dsimp [lift] at h
      nlinarith
    _ = _ := by
      rw [Finset.prod_range_eq_mul_Ico _ hp.pos]
      congr 1
      simp [Nat.mul_comm]

/-- The even and odd residues select the even representatives in the doubled block. -/
theorem doubled_residues (p : ℕ) (hp : p.Prime) (hp4 : p ≡ 1 [MOD 4]) :
    2^(p-1) * (∏ r ∈ Finset.Ico 1 p, r) =
      ∏ r ∈ Finset.Ico 1 p, (r + (r%2)*p) := by
  change p%4 = 1 at hp4
  have hp2 : p%2=1 := hp.eq_two_or_odd.resolve_left (by omega)
  let lift (r : ℕ) := r+(r%2)*p
  let idx (r : ℕ) := lift r/2
  have hl (r : ℕ) : 2*idx r=lift r := by
    have h : lift r % 2 = 0 := by
      dsimp [lift]
      rw [Nat.add_mod, Nat.mul_mod, hp2]
      omega
    dsimp [idx]
    omega
  have hmaps (r : ℕ) (hr : r ∈ Finset.Ico 1 p) : idx r ∈ Finset.Ico 1 p := by
    simp only [Finset.mem_Ico] at *
    have hb : (r%2)*p ≤ 1*p := Nat.mul_le_mul_right p (by omega)
    have h := hl r
    dsimp [lift] at h
    omega
  have hinj : Set.InjOn idx ((Finset.Ico 1 p : Finset ℕ) : Set ℕ) := by
    intro u hu v hv he
    have hh : lift u = lift v := by rw [← hl u, ← hl v, he]
    have hm := congrArg (fun x => x%p) hh
    simpa [lift, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Finset.mem_Ico.mp hu).2,
      Nat.mod_eq_of_lt (Finset.mem_Ico.mp hv).2] using hm
  calc
    _ = ∏ r ∈ Finset.Ico 1 p, (2*r) := by
      rw [Finset.prod_mul_distrib]
      simp
    _ = ∏ r ∈ Finset.Ico 1 p, (2*idx r) :=
      (prod_reindex_self (Finset.Ico 1 p) idx (fun k => 2*k) hmaps hinj).symm
    _ = _ := Finset.prod_congr rfl (fun r _ => hl r)

/-- The four lifts of paired nonzero residues contribute only their total
difference of weights to the first-order term. -/
private theorem four_lifts (p r a b c d : ℤ) :
    (r+a*p)*(r+b*p)*((-r+c*p)*(-r+d*p)) ≡
    r^4 + (a+b-c-d)*r^3*p [ZMOD p^2] := by
  have expand (x u v : ℤ) :
      (x+u*p)*(x+v*p) ≡ x^2+x*(u+v)*p [ZMOD p^2] :=
    Int.modEq_iff_dvd.mpr ⟨-(u*v), by ring⟩
  apply ((expand r a b).mul (expand (-r) c d)).trans
  exact Int.modEq_iff_dvd.mpr ⟨r^2*(a+b)*(c+d), by ring⟩

private theorem product_by_pairs (p : ℕ) (hp4 : p % 4 = 1) (f : ℕ → ℕ) :
    ∏ r ∈ Finset.Ico 1 p, f r =
      ∏ r ∈ Finset.Icc 1 (p/2), f r * f (p-r) := by
  let lo := Finset.Icc 1 (p/2)
  let hi := Finset.Ico (p/2+1) p
  have cover : Finset.Ico 1 p = lo ∪ hi := by
    ext x
    simp [lo, hi]
    omega
  have sep : Disjoint lo hi := Finset.disjoint_left.mpr (by
    intro x h₁ h₂
    simp [lo, hi] at h₁ h₂
    omega)
  have reflect : (∏ r ∈ lo, f (p-r)) = ∏ t ∈ hi, f t := by
    apply Finset.prod_bij (fun r _ => p-r)
    · intro r hr
      simp [lo, hi] at *
      omega
    · intro r hr s hs h
      simp [lo] at hr hs
      omega
    · intro t ht
      simp [hi] at ht
      refine ⟨p-t, ?_, by omega⟩
      simp [lo]
      omega
    · intros
      rfl
  rw [cover, Finset.prod_union sep, ← reflect, Finset.prod_mul_distrib]

theorem paired_products (p j : ℕ) (_hp : p.Prime) (hp4 : p ≡ 1 [MOD 4]) :
    (∏ r ∈ Finset.Ico 1 p, (r+(4*j+(3-r%4))*p)*(r+(r%2)*p)) ≡
    (∏ r ∈ Finset.Ico 1 p, (r+j*p)*r) [MOD p^2] := by
  change p % 4 = 1 at hp4
  rw [product_by_pairs p hp4, product_by_pairs p hp4]
  apply Nat.ModEq.prod
  intro r hr
  obtain ⟨hpos, hhalf⟩ := Finset.mem_Icc.mp hr
  have hle : r ≤ p := by omega
  have w : 3 - r%4 + r%2 = 3 - (p-r)%4 + (p-r)%2 := by omega
  let a := (4*j+(3-r%4) : ℕ)
  let b := r%2
  let c := (4*j+(3-(p-r)%4) : ℕ)
  let d := (p-r)%2
  have hab : (a : ℤ)+b=c+(d : ℤ) := by
    exact_mod_cast (show a+b=c+d by dsimp [a,b,c,d]; omega)
  apply Int.natCast_modEq_iff.mp
  push_cast [Nat.cast_sub hle]
  have hn := four_lifts p r a b ((c:ℤ)+1) ((d:ℤ)+1)
  have hd := four_lifts p r j 0 ((j:ℤ)+1) 1
  have match_terms :
      (a:ℤ)+b-((c:ℤ)+1)-((d:ℤ)+1) = (j:ℤ)+0-((j:ℤ)+1)-1 := by omega
  rw [match_terms] at hn
  convert hn.trans hd.symm using 1 <;> try simp only [a, b, c, d]
  all_goals
    push_cast [Nat.cast_sub hle]
    ring

private def progression (n : ℕ) := ∏ k ∈ Finset.range n, (4*k+3)

private theorem all_numerator_blocks (p n : ℕ) (hp : p.Prime) (hp4 : p ≡ 1 [MOD 4]) :
    progression (p*n) = p^n * progression n * ∏ j ∈ Finset.range n, numeratorUnits p j := by
  induction n with
  | zero => simp [progression]
  | succ n ih =>
    have step : progression (p*n+p) = progression (p*n) * (p*(4*n+3)*numeratorUnits p n) :=
      (Finset.prod_range_add (fun k => 4*k+3) (p*n) p).trans
        (congrArg (progression (p*n) * ·) (numerator_block p n hp hp4))
    rw [Nat.mul_succ, step, ih, Finset.prod_range_succ, pow_succ,
      show progression (n+1) = progression n * (4*n+3) by exact Finset.prod_range_succ _ n]
    ring

private theorem denominator_block (p j : ℕ) (hp : 0 < p) :
    (p*j+1).ascFactorial p = denominatorUnits p j * (p*(j+1)) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  rw [Nat.ascFactorial_eq_prod_range, Finset.prod_range_succ]
  unfold denominatorUnits
  rw [Finset.prod_Ico_eq_prod_range]
  congr 1
  · apply Finset.prod_congr rfl
    intro r _
    ring
  · simp only [Nat.succ_eq_add_one]; ring

private theorem all_denominator_blocks (p n : ℕ) (hp : 0 < p) :
    (p*n).factorial = p^n * n.factorial * ∏ j ∈ Finset.range n, denominatorUnits p j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, ← Nat.factorial_mul_ascFactorial, ih, denominator_block p n hp,
      pow_succ, Nat.factorial_succ, Finset.prod_range_succ]
    ring

/-- Cancel the common factors exactly before taking either side modulo p squared. -/
theorem cross_product (p n : ℕ) (hp : p.Prime) (hp4 : p ≡ 1 [MOD 4]) :
    a (p*n) * (∏ j ∈ Finset.range n, denominatorUnits p j) =
      a n * (∏ j ∈ Finset.range n, 2^(p-1)*numeratorUnits p j) := by
  have ha (k : ℕ) : a k * k.factorial = 2^k * progression k :=
    Nat.div_mul_cancel (factorial_dvd_numerator k)
  have split_exp : p*n = n+(p-1)*n := by
    conv_lhs => rw [show p = 1+(p-1) by have := hp.pos; omega, Nat.add_mul, one_mul]
  have hpow : 2^(p*n) = 2^n*(2^(p-1))^n := by rw [split_exp, pow_add, pow_mul]
  have hprod : (∏ j ∈ Finset.range n, 2^(p-1)*numeratorUnits p j) =
      (2^(p-1))^n * ∏ j ∈ Finset.range n, numeratorUnits p j := by simp [Finset.prod_mul_distrib]
  apply Nat.eq_of_mul_eq_mul_right (show 0 < p^n*n.factorial by exact Nat.mul_pos (pow_pos hp.pos _) n.factorial_pos)
  calc
    _ = a (p*n) * (p*n).factorial := by rw [all_denominator_blocks p n hp.pos]; ring
    _ = 2^(p*n) * progression (p*n) := ha _
    _ = (2^n * progression n) * ((2^(p-1))^n * (∏ j ∈ Finset.range n, numeratorUnits p j) * p^n) := by
      rw [hpow, all_numerator_blocks p n hp hp4]; ring
    _ = _ := by rw [← ha n, hprod]; ring

private theorem coprime_residue {p r : ℕ} (hp : p.Prime) (hr : r ∈ Finset.Ico 1 p) :
    p.Coprime r := by
  obtain ⟨hpos,hlt⟩ := Finset.mem_Ico.mp hr
  exact hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hpos hlt)

private theorem one_block (p j : ℕ) (hp : p.Prime) (hp4 : p ≡ 1 [MOD 4]) :
    2^(p-1) * numeratorUnits p j ≡ denominatorUnits p j [MOD p^2] := by
  have h := paired_products p j hp hp4
  simp only [Finset.prod_mul_distrib] at h
  rw [← doubled_residues p hp hp4] at h
  apply Nat.ModEq.cancel_right_of_coprime
      (Nat.Coprime.pow_left 2 (Nat.Coprime.prod_right (fun r hr => coprime_residue hp hr)))
  simpa only [numeratorUnits, denominatorUnits, mul_assoc, mul_left_comm, mul_comm] using h

private theorem full_congruence (p n : ℕ) (hp : p.Prime) (hp4 : p ≡ 1 [MOD 4]) :
    a (p*n) ≡ a n [MOD p^2] := by
  have blocks (k : ℕ) : (∏ j ∈ Finset.range k, 2^(p-1) * numeratorUnits p j) ≡
      (∏ j ∈ Finset.range k, denominatorUnits p j) [MOD p^2] := by
    induction k with
    | zero => simpa only [Finset.prod_range_zero] using (Nat.ModEq.rfl : 1 ≡ 1 [MOD p^2])
    | succ k ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      exact ih.mul (one_block p k hp hp4)
  have units : p.Coprime (∏ j ∈ Finset.range n, denominatorUnits p j) := by
    apply Nat.Coprime.prod_right
    intro j _
    apply Nat.Coprime.prod_right
    intro r hr
    exact (Nat.coprime_add_mul_right_right p r j).mpr (coprime_residue hp hr)
  apply Nat.ModEq.cancel_right_of_coprime (units.pow_left 2)
  rw [cross_product p n hp hp4]
  exact Nat.ModEq.rfl.mul (blocks n)

end A004982Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a004982.main := by
  intro p n hp hp4 _
  exact A004982Proof.full_congruence p n hp hp4
