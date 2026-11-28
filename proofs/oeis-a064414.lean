import OMAStatements.S_oeis_a064414

-- Credit: @cjchaffin
open OMA.S_oeis_a064414

namespace FibExcursion

variable {j : ℕ}

private abbrev State (j : ℕ) := ZMod j × ZMod j

private def step (j : ℕ) : Equiv.Perm (State j) where
  toFun p := (p.2, p.1 + p.2)
  invFun p := (p.2 - p.1, p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

private def line (x : ZMod j) : State j := (0, x)

private theorem line_iter (x : ZMod j) (n : ℕ) :
    (step j ^ n) (line x) = (Nat.fib n • x, Nat.fib (n+1) • x) := by
  induction n with
  | zero => simp [line]
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    change (_, Nat.fib n • x + Nat.fib (n+1) • x) = _
    rw [Nat.fib_add_two, add_nsmul]

private theorem hit_iff (x : ZMod j) (n : ℕ) :
    ((step j ^ n) (line x)).1 = 0 ↔ addOrderOf x ∣ Nat.fib n := by
  rw [line_iter]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.symm

private theorem alpha_spec [NeZero j] (x : ZMod j) :
    0 < alpha (addOrderOf x) ∧ ((step j ^ alpha (addOrderOf x)) (line x)).1 = 0 := by
  have h : {n : ℕ | 0 < n ∧ addOrderOf x ∣ Nat.fib n}.Nonempty := by
    refine ⟨orderOf (step j), orderOf_pos _, (hit_iff x _).1 ?_⟩
    simp [line]
  exact ⟨(Nat.sInf_mem h).1, (hit_iff x _).2 (Nat.sInf_mem h).2⟩

private abbrev Segment (j : ℕ) := (x : ZMod j) × Fin (alpha (addOrderOf x))

private def place (q : Segment j) : State j := (step j ^ q.2.val) (line q.1)

private theorem no_collision {x y : ZMod j} {i k : ℕ} (hlt : i < k)
    (hk : k < alpha (addOrderOf y))
    (h : (step j ^ i) (line x) = (step j ^ k) (line y)) : False := by
  have h' : line x = (step j ^ (k-i)) (line y) := by
    apply (step j ^ i).injective
    rwa [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_of_le hlt.le]
  have hzero : ((step j ^ (k-i)) (line y)).1 = 0 := by rw [← h']; rfl
  have hmin : alpha (addOrderOf y) ≤ k-i :=
    Nat.sInf_le ⟨by omega, (hit_iff y _).1 hzero⟩
  omega

private theorem place_inj : Function.Injective (@place j) := by
  rintro ⟨x, i⟩ ⟨y, k⟩ h
  change (step j ^ i.val) (line x) = (step j ^ k.val) (line y) at h
  have he : i.val = k.val := by
    rcases lt_trichotomy i.val k.val with hlt | he | hgt
    · exact False.elim (no_collision hlt k.isLt h)
    · exact he
    · exact False.elim (no_collision hgt i.isLt h.symm)
  rw [he] at h
  have hxy := congrArg Prod.snd ((step j ^ k.val).injective h)
  change x = y at hxy
  subst y
  exact congrArg (Sigma.mk x) (Fin.ext he)

private theorem line_covered [NeZero j] (n : ℕ) (x : ZMod j) :
    ∃ q : Segment j, place q = (step j ^ n) (line x) := by
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    let a := alpha (addOrderOf x)
    by_cases hn : n < a
    · exact ⟨⟨x, ⟨n, hn⟩⟩, rfl⟩
    have hs := alpha_spec x
    have ha : 0 < a := hs.1
    have hnext : (step j ^ a) (line x) = line (((step j ^ a) (line x)).2) :=
      Prod.ext hs.2 rfl
    rcases ih (n-a) (by omega) (((step j ^ a) (line x)).2) with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    rw [hq, ← hnext, ← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel (by omega)]

private theorem surj_iff_hit [NeZero j] :
    Function.Surjective (@place j) ↔ ∀ p : State j, ∃ k : ℕ, ((step j ^ k) p).1 = 0 := by
  constructor
  · intro h p
    obtain ⟨⟨x, k⟩, rfl⟩ := h p
    let a := alpha (addOrderOf x)
    refine ⟨a-k.val, ?_⟩
    change ((step j ^ (a-k.val)) ((step j ^ k.val) (line x))).1 = 0
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel k.isLt.le]
    exact (alpha_spec x).2
  · intro h p
    obtain ⟨k, hk⟩ := h p
    let m := orderOf (step j)
    have hm : 0 < m := orderOf_pos _
    have hkm : k ≤ m*k := by simpa using Nat.mul_le_mul_right k hm
    have he : (step j ^ k) p = line (((step j ^ k) p).2) := Prod.ext hk rfl
    obtain ⟨q, hq⟩ := line_covered (m*k-k) (((step j ^ k) p).2)
    refine ⟨q, ?_⟩
    rw [hq, ← he, ← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hkm,
      pow_mul, pow_orderOf_eq_one, one_pow]
    rfl

private theorem G_iter (a b k : ℕ) :
    (step j ^ k) ((a : ZMod j), (b : ZMod j)) =
      ((G a b k : ZMod j), (G a b (k+1) : ZMod j)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    change (_, (G a b k : ZMod j) + (G a b (k+1) : ZMod j)) = _
    simp [G]

private theorem inputs_iff (hj : 0 < j) [NeZero j] :
    (∀ a b : ℕ, 0 < a → 0 < b → ∃ k, j ∣ G a b k) ↔
      ∀ p : State j, ∃ k : ℕ, ((step j ^ k) p).1 = 0 := by
  constructor
  · intro h ⟨x,y⟩
    obtain ⟨k,hk⟩ := h (x.val+j) (y.val+j) (by omega) (by omega)
    refine ⟨k, ?_⟩
    have h' := congrArg Prod.fst (G_iter (j := j) (x.val+j) (y.val+j) k)
    simpa using h'.trans ((ZMod.natCast_eq_zero_iff _ _).2 hk)
  · intro h a b _ _
    obtain ⟨k,hk⟩ := h ((a : ZMod j), (b : ZMod j))
    rw [G_iter] at hk
    exact ⟨k, (ZMod.natCast_eq_zero_iff _ _).1 hk⟩

private theorem segment_card [NeZero j] :
    Fintype.card (Segment j) = ∑ d ∈ j.divisors, Nat.totient d * alpha d := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  have hd (x : ZMod j) : addOrderOf x ∣ j := by
    simpa only [ZMod.card] using (addOrderOf_dvd_card (x := x))
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := j.divisors)
    (g := addOrderOf) (fun x _ => Nat.mem_divisors.mpr ⟨hd x, NeZero.ne j⟩)]
  apply Finset.sum_congr rfl
  intro d h
  have hc := IsAddCyclic.card_addOrderOf_eq_totient (α := ZMod j)
    (d := d) (by simpa only [ZMod.card] using (Nat.mem_divisors.mp h).1)
  calc
    _ = ∑ _x ∈ (Finset.univ.filter fun x : ZMod j => addOrderOf x = d), alpha d := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = _ := by simp [hc]

private theorem result : ∀ j : ℕ, 0 < j →
    ((∀ a b : ℕ, 0 < a → 0 < b → ∃ k, j ∣ G a b k) ↔
      j ^ 2 = ∑ d ∈ j.divisors, Nat.totient d * alpha d) := by
  intro j hj
  let : NeZero j := ⟨hj.ne'⟩
  rw [inputs_iff hj, ← surj_iff_hit, ← segment_card]
  have hc : Fintype.card (State j) = j^2 := by simp [sq]
  rw [← hc, eq_comm]
  constructor
  · exact fun hs => Fintype.card_of_bijective ⟨place_inj, hs⟩
  · exact fun h => ((Fintype.bijective_iff_injective_and_card _).2 ⟨place_inj, h⟩).2

end FibExcursion

theorem OMA.solution : type_of% @OMA.S_oeis_a064414.main := FibExcursion.result
