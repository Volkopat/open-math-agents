import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1
import Mathlib

/-!
# Two cosets of a class-two normal subgroup

For the regular odd-order matching problem, rule out a noncommuting repeated
quotient shift, at any subgroup index. Twelve two-edge horizontal moves and
eight switches give a simple 32-cycle. In H1 every triple of distinct shifts
below stays distinct modulo each proper class-two normal subgroup. H2 treats
a repeated shift that commutes with its conjugate across the separating edge.

This reduction builds on the three-matching presentation (PR 5246), the
regular odd-order reduction (PR 7828), and the voltage-graph reduction
(PR 9593). The formal result here is the noncommuting two-coset case.
-/

namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1_H2_R2

open SimpleGraph
open scoped commutatorElement

/-- No two of the three matching shifts coalesce modulo a proper class-two normal subgroup. -/
def H1 : Prop :=
  ∀ (A : Type) [Group A] [Fintype A] (a b : A),
    Subgroup.closure ({a,b} : Set A) = ⊤ → a ≠ 1 → b ≠ 1 → a ≠ b → Odd (Nat.card A) →
    (∀ N : Subgroup A, N.Normal → IsMulCommutative N → N.index ≠ 11) →
    (∃ x y : commutator A, x * y ≠ y * x) →
    (∀ N : Subgroup A, N.Normal → N ≠ ⊤ →
      (∀ u ∈ N, ∀ v ∈ N, ∀ w ∈ N, Commute ⁅u,v⁆ w) → a ∉ N ∧ b ∉ N ∧ a⁻¹*b ∉ N) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ (SimpleGraph.fromRel (fun u v : Bool × A =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=a*u.2 ∨ v.2=b*u.2)))

/-- A repeated quotient shift commutes with its conjugate in the neighboring coset. -/
def H2 : Prop :=
  ∀ (A : Type) [Group A] [Fintype A] (s t : A), Odd (Nat.card A) → s ≠ 1 →
    ∀ N : Subgroup A, N.Normal → (∀ u ∈ N, ∀ v ∈ N, ∀ w ∈ N, Commute ⁅u,v⁆ w) →
    s ∈ N → t ∉ N → Commute (t⁻¹*s*t) s →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ (SimpleGraph.fromRel (fun u v : Bool × A =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=s*u.2 ∨ v.2=t*u.2)))

variable {A : Type*} [Group A]

private theorem collect {s r c : A} (rel : r*s = s*r*c)
    (sc : Commute s c) (rc : Commute r c) (x y z : ℕ) :
    r * (s ^ (x : ℕ) * r ^ (y : ℕ) * c ^ ((y : ℕ) + (z : ℕ))) = (s ^ (x : ℕ) * r ^ (y : ℕ) * c ^ ((y : ℕ) + (z : ℕ))) * c^x * r := by
  have conjS : MulAut.conj r s = s*c := by
    rw [MulAut.conj_apply, rel, mul_assoc s, rc.eq, ← mul_assoc s]; group
  have conjR : MulAut.conj r r = r := by simp [MulAut.conj_apply]
  have conjC : MulAut.conj r c = c := by rw [MulAut.conj_apply, rc.eq]; group
  have action := congrArg (fun g : A => g*r)
    (show MulAut.conj r ((s ^ (x : ℕ) * r ^ (y : ℕ) * c ^ ((y : ℕ) + (z : ℕ)))) =
      (s ^ (x : ℕ) * r ^ (y : ℕ) * c ^ ((y : ℕ) + (z : ℕ))) * c^x from by
        simp only [map_mul, map_pow, conjS, conjR, conjC, sc.mul_pow]
        have pass := ((rc.symm.pow_pow x y).mul_right (Commute.pow_pow_self c x (y+z))).eq
        simpa only [mul_assoc] using congrArg (fun g : A => s^x*g) pass)
  simpa [MulAut.conj_apply, mul_assoc] using action

private theorem collect_other {s r c : A} (rel : r*s = s*r*c)
    (sc : Commute s c) (rc : Commute r c) (x y z : ℕ) :
    MulAut.conj s⁻¹ ((s ^ (x : ℕ) * r ^ (y : ℕ) * c ^ ((y : ℕ) + (z : ℕ)))) = (s ^ (x : ℕ) * r ^ (y : ℕ) * c ^ ((y : ℕ) + (z : ℕ))) * c^y := by
  have conjS : MulAut.conj s⁻¹ s = s := by simp
  have conjR : MulAut.conj s⁻¹ r = r*c := by
    rw [MulAut.conj_apply, inv_inv, mul_assoc, rel]; group
  have conjC : MulAut.conj s⁻¹ c = c := by
    rw [MulAut.conj_apply, inv_inv, mul_assoc, ← sc.eq]; group
  simp only [map_mul, map_pow, conjS, conjR, conjC, rc.mul_pow]
  have pass := (Commute.pow_pow_self c y (y+z)).eq
  simpa only [mul_assoc] using congrArg (fun g : A => s^x*(r^y*g)) pass

private theorem position_injective {s r c : A} (rel : r*s = s*r*c)
    (sc : Commute s c) (rc : Commute r c) (order : 3 ≤ orderOf c)
    {i j : (Bool × Bool × Fin 3 × Fin 3 × Fin 3)} (eq : (s ^ (i.2.2.1 : ℕ) * r ^ (i.2.2.2.1 : ℕ) * c ^ ((i.2.2.2.1 : ℕ) + (i.2.2.2.2 : ℕ))) = (s ^ (j.2.2.1 : ℕ) * r ^ (j.2.2.2.1 : ℕ) * c ^ ((j.2.2.2.1 : ℕ) + (j.2.2.2.2 : ℕ)))) :
    i.2.2.1 = j.2.2.1 ∧ i.2.2.2.1 = j.2.2.2.1 ∧ i.2.2.2.2 = j.2.2.2.2 := by
  have powers {a b : Fin 3} (h : c^a.val = c^b.val) : a = b :=
    Fin.ext (pow_injOn_Iio_orderOf (a.isLt.trans_le order) (b.isLt.trans_le order) h)
  have h := congrArg (r * ·) eq
  rw [collect rel sc rc, collect rel sc rc, eq] at h
  have hx := powers (mul_left_cancel (mul_right_cancel h))
  have h' := congrArg (MulAut.conj s⁻¹) eq
  rw [collect_other rel sc rc, collect_other rel sc rc, eq] at h'
  have hy := powers (mul_left_cancel h')
  simp only [hx, hy, pow_add, mul_assoc] at eq
  exact ⟨hx, hy, powers (mul_left_cancel (mul_left_cancel (mul_left_cancel eq)))⟩

/-- An explicit dyadic cycle for the noncommuting case inside two cosets. -/
theorem contains_cycle32 (N : Subgroup A) (s t r c : A)
    (s_mem : s ∈ N) (r_mem : r ∈ N) (c_mem : c ∈ N) (t_out : t ∉ N)
    (conjugate : t*r = s*t) (rel : r*s = s*r*c)
    (sc : Commute s c) (rc : Commute r c) (order : 3 ≤ orderOf c) :
    cycleGraph 32 ⊑ (SimpleGraph.fromRel (fun u v : Bool × A =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=s*u.2 ∨ v.2=t*u.2))) := by
  let trace : Fin 32 → (Bool × Bool × Fin 3 × Fin 3 × Fin 3) :=
    ![
      ⟨false, false, 1, 0, 0⟩, ⟨true, false, 2, 0, 0⟩, ⟨false, false, 2, 0, 0⟩, ⟨true, true, 2, 0, 0⟩,
      ⟨false, true, 2, 0, 0⟩, ⟨true, true, 2, 1, 1⟩, ⟨false, true, 2, 1, 1⟩, ⟨true, true, 2, 2, 2⟩,
      ⟨false, false, 2, 2, 2⟩, ⟨true, false, 2, 2, 2⟩, ⟨false, false, 1, 2, 2⟩, ⟨true, true, 1, 2, 2⟩,
      ⟨false, true, 1, 1, 2⟩, ⟨true, true, 1, 1, 2⟩, ⟨false, true, 1, 0, 2⟩, ⟨true, true, 1, 0, 2⟩,
      ⟨false, false, 1, 0, 2⟩, ⟨true, false, 1, 0, 2⟩, ⟨false, false, 0, 0, 2⟩, ⟨true, true, 0, 0, 2⟩,
      ⟨false, true, 0, 0, 2⟩, ⟨true, true, 0, 1, 1⟩, ⟨false, true, 0, 1, 1⟩, ⟨true, true, 0, 2, 0⟩,
      ⟨false, false, 0, 2, 0⟩, ⟨true, false, 1, 2, 0⟩, ⟨false, false, 1, 2, 0⟩, ⟨true, true, 1, 2, 0⟩,
      ⟨false, true, 1, 1, 0⟩, ⟨true, true, 1, 1, 0⟩, ⟨false, true, 1, 0, 0⟩, ⟨true, true, 1, 0, 0⟩]

  let edge (u v : (Bool × Bool × Fin 3 × Fin 3 × Fin 3)) : Prop :=
    u.1 = false ∧ v.1 = true ∧
    ((u.2.2.1 = v.2.2.1 ∧ u.2.2.2.1 = v.2.2.2.1 ∧ u.2.2.2.2 = v.2.2.2.2 ∧ (u.2.1 = v.2.1 ∨ u.2.1 = false ∧ v.2.1 = true)) ∨
     (u.2.1 = false ∧ v.2.1 = false ∧ v.2.2.1.val = u.2.2.1.val + 1 ∧ u.2.2.2.1 = v.2.2.2.1 ∧ u.2.2.2.2 = v.2.2.2.2) ∨
     (u.2.1 = true ∧ v.2.1 = true ∧ u.2.2.1 = v.2.2.1 ∧ v.2.2.2.1.val = u.2.2.2.1.val + 1 ∧
        v.2.2.2.2.val + 1 = u.2.2.2.2.val + u.2.2.1.val))

  let _ (u v : (Bool × Bool × Fin 3 × Fin 3 × Fin 3)) : Decidable (edge u v) := by dsimp only [edge]; infer_instance

  have trace_distinct : Function.Injective trace := by
    change ∀ i j : Fin 32, trace i = trace j → i = j
    dsimp only [trace]
    decide

  have trace_edges : ∀ i : Fin 32,
      edge (trace i) (trace (i+1)) ∨ edge (trace (i+1)) (trace i) := by
    dsimp only [edge, trace]
    decide
  let val (i : (Bool × Bool × Fin 3 × Fin 3 × Fin 3)) := (s ^ (i.2.2.1 : ℕ) * r ^ (i.2.2.2.1 : ℕ) * c ^ ((i.2.2.2.1 : ℕ) + (i.2.2.2.2 : ℕ)))
  let lift (i : (Bool × Bool × Fin 3 × Fin 3 × Fin 3)) : Bool × A := (i.1, if i.2.1 then t * val i else val i)
  have mem (i : (Bool × Bool × Fin 3 × Fin 3 × Fin 3)) : val i ∈ N :=
    N.mul_mem (N.mul_mem (N.pow_mem s_mem _) (N.pow_mem r_mem _)) (N.pow_mem c_mem _)
  have disjoint (i j : (Bool × Bool × Fin 3 × Fin 3 × Fin 3)) : t * val i ≠ val j := by
    intro h
    have both := N.mul_mem (mem j) (N.inv_mem (mem i))
    rw [← h] at both
    exact t_out (by simpa [mul_assoc] using both)
  have inj : Function.Injective lift := by
    intro i j h
    have side := congrArg Prod.fst h
    have same := congrArg Prod.snd h
    change i.1 = j.1 at side
    change (if i.2.1 then t * val i else val i) = (if j.2.1 then t * val j else val j) at same
    have parts : i.2.1 = j.2.1 ∧ val i = val j := by
      cases hi : i.2.1 <;> cases hj : j.2.1 <;> simp [hi,hj] at same ⊢
      · exact same
      · exact (disjoint j i same.symm).elim
      · exact (disjoint i j same).elim
      · exact same
    obtain ⟨hx,hy,hz⟩ := position_injective rel sc rc order parts.2
    exact Prod.ext side (Prod.ext parts.1 (Prod.ext hx (Prod.ext hy hz)))
  have maps {i j : (Bool × Bool × Fin 3 × Fin 3 × Fin 3)} (h : edge i j) : ((SimpleGraph.fromRel (fun u v : Bool × A =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=s*u.2 ∨ v.2=t*u.2)))).Adj (lift i) (lift j) := by
    obtain ⟨hs,hd,same | lower | upper⟩ := h
    all_goals
      apply (SimpleGraph.fromRel_adj ..).mpr
      refine ⟨?_,Or.inl ⟨hs,hd,?_⟩⟩
    any_goals exact fun e => Bool.false_ne_true (hs.symm.trans ((congrArg Prod.fst e).trans hd))
    · obtain ⟨hx,hy,hz, h | ⟨hi,hj⟩⟩ := same
      · exact Or.inl (by simp [lift, val, hx,hy,hz,h])
      · exact Or.inr (Or.inr (by simp [lift, val, hx,hy,hz,hi,hj]))
    · obtain ⟨hi,hj,hx,hy,hz⟩ := lower
      exact Or.inr (Or.inl (by simp [lift,val,hi,hj,hx,hy,hz,pow_succ',mul_assoc]))
    · obtain ⟨hi,hj,hx,hy,hz⟩ := upper
      have step : r * val i = val j := by
        rw [show r * val i = _ from collect rel sc rc _ _ _]
        have pass := (rc.symm.pow_left (i.2.2.2.1.val+i.2.2.2.2.val+i.2.2.1.val)).eq
        have ex : j.2.2.2.1.val+j.2.2.2.2.val = i.2.2.2.1.val+i.2.2.2.2.val+i.2.2.1.val := by omega
        simp only [val,← hx,hy,pow_succ,mul_assoc]
        simp only [← mul_assoc, ← pow_add] at *
        grind [mul_assoc, rc.eq]
      exact Or.inr (Or.inl (by
        change (if j.2.1 then t*val j else val j) = s*(if i.2.1 then t*val i else val i)
        simp only [hi,hj,if_true]
        rw [← step,← mul_assoc,conjugate,mul_assoc]))
  apply isContained_iff_exists_le_comap.mpr
  refine ⟨⟨lift ∘ trace, inj.comp trace_distinct⟩, ?_⟩
  intro i j h
  have next (i : Fin 32) : ((SimpleGraph.fromRel (fun u v : Bool × A =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=s*u.2 ∨ v.2=t*u.2)))).Adj (lift (trace i)) (lift (trace (i+1))) :=
    (trace_edges i).elim (fun e => maps e) (fun e => (maps e).symm)
  rcases cycleGraph_adj.mp h with h | h
  · exact (sub_eq_iff_eq_add.mp h ▸ (by simpa [add_comm] using (next j).symm))
  · exact (sub_eq_iff_eq_add.mp h ▸ (by simpa [add_comm] using next i))

/-- In an odd-order group, the order condition follows as soon as the two
horizontal moves fail to commute. Normality puts both moves in the same
subgroup. The central-commutator hypothesis says its class is at most two.
This local conclusion works at any subgroup index. -/
theorem odd_classTwo_noncommuting [Finite A] (odd : Odd (Nat.card A))
    (N : Subgroup A) [normal : N.Normal]
    (classTwo : ∀ u ∈ N, ∀ v ∈ N, ∀ w ∈ N, Commute ⁅u,v⁆ w)
    (s t : A) (hs : s ∈ N) (ht : t ∉ N) (hne : ¬ Commute (t⁻¹*s*t) s) :
    cycleGraph 32 ⊑ (SimpleGraph.fromRel (fun u v : Bool × A =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=s*u.2 ∨ v.2=t*u.2))) := by
  let r := t⁻¹*s*t
  let c := ⁅r⁻¹,s⁻¹⁆
  have hr : r ∈ N := by simpa [r] using normal.conj_mem s hs t⁻¹
  have hc : c ∈ N := by
    simpa [c,commutatorElement_def] using
      N.mul_mem (N.mul_mem (N.mul_mem (N.inv_mem hr) (N.inv_mem hs)) hr) hs
  have relation : r*s = s*r*c := by simp [c,commutatorElement_def,mul_assoc]
  have nontrivial : c ≠ 1 := fun h => hne (show r*s = s*r by simpa only [h,mul_one] using relation)
  have positive := orderOf_pos c
  have neOne : orderOf c ≠ 1 := fun h => nontrivial (orderOf_eq_one_iff.mp h)
  have neTwo : orderOf c ≠ 2 := by
    intro h
    have divides := orderOf_dvd_natCard c
    rw [h] at divides
    obtain ⟨k,hk⟩ := odd
    omega
  apply contains_cycle32 N s t r c hs hr hc ht (by dsimp [r]; group) relation
  · exact (classTwo _ (N.inv_mem hr) _ (N.inv_mem hs) s hs).symm
  · exact (classTwo _ (N.inv_mem hr) _ (N.inv_mem hs) r hr).symm
  · omega


/-- Multiplying all right labels by h embeds the renormalized matching graph. -/
theorem change_labels (a b h s t : A)
    (labels : ∀ d : A, d = 1 ∨ d = s ∨ d = t → h*d = 1 ∨ h*d = a ∨ h*d = b) :
    (SimpleGraph.fromRel (fun u v : Bool × A =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=s*u.2 ∨ v.2=t*u.2))) ⊑ (SimpleGraph.fromRel (fun u v : Bool × A =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=a*u.2 ∨ v.2=b*u.2))) := by
  let f (u : Bool × A) : Bool × A := (u.1, if u.1 then h*u.2 else u.2)
  have inj : Function.Injective f := by
    rintro ⟨i,x⟩ ⟨j,y⟩ eq
    have eq₁ : i = j := congrArg Prod.fst eq
    subst j
    have eq₂ := congrArg Prod.snd eq
    cases i <;> simpa [f] using eq₂
  have send {x y : A} (e : y=x ∨ y=s*x ∨ y=t*x) :
      h*y=x ∨ h*y=a*x ∨ h*y=b*x := by
    obtain ⟨d,hd,he⟩ : ∃ d : A, (d=1 ∨ d=s ∨ d=t) ∧ y=d*x := by
      rcases e with e | e | e
      · exact ⟨1,Or.inl rfl,by simpa using e⟩
      · exact ⟨s,Or.inr (Or.inl rfl),e⟩
      · exact ⟨t,Or.inr (Or.inr rfl),e⟩
    rw [he,← mul_assoc]
    rcases labels d hd with h₁ | h₂ | h₃ <;> simp [*]
  apply isContained_iff_exists_le_comap.mpr
  refine ⟨⟨f,inj⟩,?_⟩
  intro u v adj
  change (SimpleGraph.fromRel (fun u v : Bool × A =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=a*u.2 ∨ v.2=b*u.2))).Adj (f u) (f v)
  apply (SimpleGraph.fromRel_adj ..).mpr
  obtain ⟨ne,e | e⟩ := (SimpleGraph.fromRel_adj ..).mp adj
  · exact ⟨fun z => ne (inj z), Or.inl ⟨e.1,e.2.1,by simpa [f,e.1,e.2.1] using send e.2.2⟩⟩
  · exact ⟨fun z => ne (inj z), Or.inr ⟨e.1,e.2.1,by simpa [f,e.1,e.2.1] using send e.2.2⟩⟩

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1.H2 := by
  intro distinct commuting A _ _ a b gen ha hb hab odd eleven derived
  classical
  by_cases allDistinct : ∀ N : Subgroup A, N.Normal → N ≠ ⊤ →
      (∀ u ∈ N, ∀ v ∈ N, ∀ w ∈ N, Commute ⁅u,v⁆ w) → a ∉ N ∧ b ∉ N ∧ a⁻¹*b ∉ N
  · exact distinct A a b gen ha hb hab odd eleven derived allDistinct
  push Not at allDistinct
  obtain ⟨N,hN,proper,classTwo,fails⟩ := allDistinct
  let _ : N.Normal := hN
  have apart (h₁ : a ∈ N) (h₂ : b ∈ N) : False := by
    apply proper
    apply top_unique
    rw [← gen,Subgroup.closure_le]
    intro x hx
    rcases (show x=a ∨ x=b by simpa using hx) with rfl | rfl <;> assumption
  have solve (s t : A) (hs : s ∈ N) (ht : t ∉ N) (ne : s ≠ 1) :
      ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ (SimpleGraph.fromRel (fun u v : Bool × A =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=s*u.2 ∨ v.2=t*u.2))) := by
    by_cases comm : Commute (t⁻¹*s*t) s
    · exact commuting A s t odd ne N hN classTwo hs ht comm
    · exact ⟨5, by decide, odd_classTwo_noncommuting odd N classTwo s t hs ht comm⟩
  by_cases ain : a ∈ N
  · exact solve a b ain (apart ain) ha
  by_cases bin : b ∈ N
  · obtain ⟨k,hk,c⟩ := solve b a bin ain hb
    exact ⟨k,hk,c.trans (change_labels a b 1 b a (by
      intro d hd; rcases hd with rfl | rfl | rfl <;> simp))⟩
  have abN : a⁻¹*b ∈ N := by tauto
  have invOut : a⁻¹ ∉ N := fun h => ain (by simpa using N.inv_mem h)
  have ne : a⁻¹*b ≠ 1 := fun h => hab (by
    have e := congrArg (a*·) h
    simpa [← mul_assoc] using e.symm)
  obtain ⟨k,hk,c⟩ := solve (a⁻¹*b) a⁻¹ abN invOut ne
  exact ⟨k,hk,c.trans (change_labels a b a (a⁻¹*b) a⁻¹ (by
    intro d hd; rcases hd with rfl | rfl | rfl <;> simp [← mul_assoc]))⟩

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1_H2_R2
