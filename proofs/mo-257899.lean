import OMAStatements.S_mo_257899

/-!
Complete proof by @connoranderson, linked from statement PR #24841 and desk DONE #113804.
Pinned companion: https://github.com/connoranderson/open-math-agents/blob/a4d4ac7cb9b32fe4f5d969f3bb3dd11f9fd0e1a2/proofs/mo-257899.lean
All mathematical code is retained unchanged. This port adds provenance and current-checker validation.
Credit HolyMonk's original question https://mathoverflow.net/questions/257899 (CC BY-SA 3.0).
Marshall Hall's theorem and the explanatory reference below are retained. Port: @rodolfoquint.
-/

/-!
Marshall Hall, Jr., “A combinatorial problem on abelian groups”, Proceedings of the AMS 3 (1952), 584–587, DOI 10.1090/S0002-9939-1952-0050579-7. The two-row adjustment is also described by Rudi Mrazović, Oxford doctoral thesis, Theorem 5.9.1. Here the finite orbit between the two distinguished rows is expressed as a reachability set. The application to inventory uses constant cyclic interval coverage.
-/

namespace OMA.S_mo_257899

open Finset

/-- A finite partial injection extends to a permutation of the ambient type. -/
private lemma extend_except {I : Type*} [Finite I] (u : I) (g : I → I)
    (hg : Set.InjOn g {j | j ≠ u}) :
    ∃ σ : Equiv.Perm I, ∀ j, j ≠ u → σ j = g j := by
  let p : {j : I // j ≠ u} → I := Subtype.val
  have hinj : Function.Injective (g ∘ p) := by
    intro x y h
    exact Subtype.ext (hg x.2 y.2 h)
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair p (g ∘ p) Subtype.val_injective hinj
  exact ⟨σ, fun j hj => hσ ⟨j,hj⟩⟩

/-- Along the forward orbit of v, stop before visiting u. The two partial shifts
can each be completed at u, which is the unconstrained row. -/
private lemma shift_indices {I : Type*} [Finite I] (T : Equiv.Perm I)
    {u v : I} (huv : u ≠ v) :
    ∃ p q : Equiv.Perm I, p v = u ∧ q v = T v ∧
      ∀ j, j ≠ u → j ≠ v → (p j = j ∧ q j = j) ∨ (p j = T.symm j ∧ q j = T j) := by
  classical
  let S (j : I) := Relation.ReflTransGen (fun a b => b = T a ∧ b ≠ u) v j
  have hv : S v := .refl
  have havoid {j} (hj : S j) : j ≠ u := by
    rcases hj.cases_tail with h | ⟨k,_,_,h⟩
    · exact h.trans_ne huv.symm
    · exact h
  have hsuc {j} (hj : S j) (h : T j ≠ u) : S (T j) := hj.tail ⟨rfl,h⟩
  have hpre {j} (hj : S j) (h : j ≠ v) : S (T.symm j) := by
    rcases hj.cases_tail with he | ⟨k,hk,he,_⟩
    · exact (h he).elim
    · simpa [he] using hk
  let f (j : I) := if j = v then u else if S j then T.symm j else j
  let g (j : I) := if S j then T j else j
  have hf : Set.InjOn f {j | j ≠ u} := by
    intro j hju k hku he
    change j ≠ u at hju
    change k ≠ u at hku
    by_cases hjv : j = v <;> by_cases hkv : k = v <;> by_cases hj : S j <;> by_cases hk : S k <;>
      simp only [f, if_pos, hjv,hkv,hj,hk,if_false] at he <;>
      first | exact hjv.trans hkv.symm | exact T.symm.injective he | exact he |
        grind
  have hg : Set.InjOn g {j | j ≠ u} := by
    intro j hju k hku he
    change j ≠ u at hju
    change k ≠ u at hku
    by_cases hj : S j <;> by_cases hk : S k <;>
      simp only [g, hj, hk, if_true, if_false] at he <;>
      first | exact T.injective he | exact he | grind
  obtain ⟨p,hp⟩ := extend_except u f hf
  obtain ⟨q,hq⟩ := extend_except u g hg
  refine ⟨p,q,by simp [hp v huv.symm,f],by simp [hq v huv.symm,g,hv],?_⟩
  intro j hju hjv
  rw [hp j hju, hq j hju]
  by_cases hj : S j <;> simp [f,g,hj,hjv]

private lemma change_one {I G : Type*} [Fintype I] [AddCommGroup G]
    (a b : I ≃ G) {u v : I} (huv : u ≠ v) (target : G) :
    ∃ a' b' : I ≃ G, a' v + b' v = target ∧
      ∀ j, j ≠ u → j ≠ v → a' j + b' j = a j + b j := by
  let d := target - a u - a v
  let T := (a.trans (Equiv.addRight d)).trans b.symm
  have hb (j : I) : b (T j) = a j + d := by simp [T]
  obtain ⟨p,q,hpv,hqv,hpq⟩ := shift_indices T huv
  refine ⟨p.trans a,q.trans b,?_,?_⟩
  · change a (p v) + b (q v) = _
    rw [hpv,hqv,hb]
    dsimp [d]
    abel
  · intro j hju hjv
    change a (p j) + b (q j) = _
    rcases hpq j hju hjv with ⟨hp,hq⟩ | ⟨hp,hq⟩
    · rw [hp,hq]
    · have hprev := hb (T.symm j)
      rw [T.apply_symm_apply] at hprev
      rw [hp,hq,hb,hprev]
      abel

private lemma hall_differences {I G : Type*} [Fintype I] [Fintype G] [AddCommGroup G]
    (e : I ≃ G) (u : I) (f : I → G) (hf : ∑ j, f j = 0) :
    ∃ a b : I ≃ G, ∀ j, b j - a j = f j := by
  classical
  have extend (s : Finset I) (hs : u ∉ s) : ∃ a b : I ≃ G, ∀ j ∈ s, a j + b j = f j := by
    induction s using Finset.induction_on with
    | empty => exact ⟨e,e,by simp⟩
    | @insert v s hv ih =>
      obtain ⟨a,b,hab⟩ := ih (fun h => hs (mem_insert_of_mem h))
      have huv : u ≠ v := by intro h; exact hs (h ▸ mem_insert_self ..)
      obtain ⟨a',b',ht,hrest⟩ := change_one a b huv (f v)
      refine ⟨a',b',fun j hj => ?_⟩
      rcases mem_insert.mp hj with rfl | hj
      · exact ht
      · exact (hrest j (fun he => hs (he ▸ mem_insert_of_mem hj)) (fun he => hv (he ▸ hj))).trans (hab j hj)
  obtain ⟨a,b,hab⟩ := extend (univ.erase u) (by simp)
  let A := a.trans (Equiv.neg G)
  have hrow (j : I) (h : j ≠ u) : b j - A j = f j := by
    simpa [A, add_comm] using hab j (mem_erase.mpr ⟨h,mem_univ _⟩)
  refine ⟨A,b,fun j => ?_⟩
  by_cases hj : j = u
  · subst j
    have htotal : ∑ j, (b j - A j - f j) = 0 := by
      rw [sum_sub_distrib, sum_sub_distrib,hf,sub_zero,sub_eq_zero]
      exact (b.sum_comp id).trans (A.sum_comp id).symm
    rw [Finset.sum_eq_single u] at htotal
    · exact sub_eq_zero.mp htotal
    · intro j _ hju
      rw [hrow j hju,sub_self]
    · simp
  · exact hrow j hj

end OMA.S_mo_257899
namespace OMA.S_mo_257899

open Finset

private def hit {N : ℕ} (a x : ZMod N) : ℤ := if a = x then 1 else 0

private def piece {N : ℕ} (a : ZMod N) (k : ℕ) (x : ZMod N) : ℤ :=
  ∑ j ∈ range k, hit (a + (j : ZMod N)) x

private def cover {n : ℕ} (a : Fin (n+1) ≃ ZMod (n+1)) (k : Fin (n+1) → ℕ)
    (x : ZMod (n+1)) : ℤ := ∑ i, piece (a i) (k i) x

private lemma piece_step {N : ℕ} (a : ZMod N) (k : ℕ) (x : ZMod N) :
    piece a k (x+1) - piece a k x = hit a (x+1) - hit (a+(k : ZMod N)) (x+1) := by
  induction k with
  | zero => simp [piece]
  | succ k ih =>
    have hs : hit (a+((k+1:ℕ):ZMod N)) (x+1) = hit (a+(k : ZMod N)) x := by simp [hit,Nat.cast_succ,← add_assoc]
    simp only [piece,sum_range_succ] at ih ⊢
    rw [hs]
    omega

private lemma cover_constant {n : ℕ} (a b : Fin (n+1) ≃ ZMod (n+1)) (k : Fin (n+1) → ℕ)
    (hab : ∀ i, b i - a i = k i) (s t : ZMod (n+1)) : cover a k s = cover a k t := by
  have hstep (x : ZMod (n+1)) : cover a k (x+1) = cover a k x := by
    apply sub_eq_zero.mp
    rw [cover,cover, ← sum_sub_distrib]
    simp only [piece_step, sum_sub_distrib]
    have he (i) : a i + k i = b i := by rw [← hab i]; abel
    simp only [he]
    exact sub_eq_zero.mpr ((a.sum_comp (fun j => hit j (x+1))).trans
      (b.sum_comp (fun j => hit j (x+1))).symm)
  have hnat (m : ℕ) : cover a k m = cover a k 0 := by
    induction m with
    | zero => simp
    | succ m ih => rw [Nat.cast_succ,hstep,ih]
  simpa using (hnat s.val).trans (hnat t.val).symm

private lemma sum_prefix {R : Type*} [AddCommMonoid R] {m K : ℕ} (hm : m ≤ K) (f : ℕ → R) :
    (∑ j ∈ range K, if j < m then f j else 0) = ∑ j ∈ range m, f j := by
  rw [← sum_filter]
  congr 1
  ext j
  simp only [mem_filter, mem_range]
  omega

private lemma total_inventory {n : ℕ} (k : Fin (n+1) → ℕ)
    (hk : ∀ i, k i ≤ k (Fin.last n)) (σ : Equiv.Perm (Fin (n+1))) :
    ∑ s, inventory k σ s = ∑ i, k i := by
  unfold inventory
  rw [sum_comm]
  calc
    _ = ∑ j ∈ range (k (Fin.last n)), ∑ i, (if j < k i then 1 else 0) := by
      refine sum_congr rfl fun j _ => ?_
      exact Equiv.sum_comp (σ ^ (k (Fin.last n)-j-1)) (fun i => if j < k i then 1 else 0)
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      simpa using sum_prefix (hk i) (fun _ => (1:ℕ))

private lemma inventory_cover {n : ℕ} (k : Fin (n+1) → ℕ)
    (hk : ∀ i, k i ≤ k (Fin.last n)) (a : Fin (n+1) ≃ ZMod (n+1)) :
    ∃ σ : Equiv.Perm (Fin (n+1)), ∀ s,
      (inventory k σ s : ℤ) = cover a k (a s + (k (Fin.last n)-1:ℕ)) := by
  let σ := (a.trans (Equiv.addRight (1:ZMod (n+1)))).trans a.symm
  have hpow (s) (j : ℕ) : a ((σ^j) s) = a s + j := by
    induction j with
    | zero => simp
    | succ j ih => simp [pow_succ',Equiv.Perm.mul_apply,σ,ih,add_assoc]
  refine ⟨σ,fun s => ?_⟩
  let M := k (Fin.last n)
  let x : ZMod (n+1) := a s + (M-1:ℕ)
  change ((∑ j ∈ range M, if j < k ((σ ^ (M-j-1)) s) then 1 else 0 : ℕ) : ℤ) =
    ∑ i, piece (a i) (k i) x
  push_cast
  calc
    _ = ∑ j ∈ range M, ∑ i, (if j < k i then hit (a i + (j : ZMod (n+1))) x else 0) := by
      apply sum_congr rfl
      intro j hj
      let t := (σ ^ (M-j-1)) s
      have hc : ((M-j-1 : ℕ) : ZMod (n+1)) + (j:ZMod (n+1)) = ((M-1:ℕ):ZMod (n+1)) := by
        rw [← Nat.cast_add]
        congr 1
        simp only [mem_range] at hj
        omega
      have ht : a t + j = x := by
        rw [show a t = a s + (M-j-1 : ℕ) from hpow s _]
        exact (add_assoc ..).trans (congrArg (a s + ·) hc)
      rw [Finset.sum_eq_single t]
      · change ((if j < k t then 1 else 0) : ℤ) = if j < k t then hit (a t + (j : ZMod (n+1))) x else 0
        simp [hit,ht]
      · intro i _ hi
        have hi' : a i + j ≠ x := by
          intro he
          exact hi (a.injective (add_right_cancel (he.trans ht.symm)))
        simp [hit,hi']
      · simp
    _ = _ := by
      rw [sum_comm]
      exact sum_congr rfl fun i _ => sum_prefix (hk i) _

end OMA.S_mo_257899
theorem OMA.solution : type_of% @OMA.S_mo_257899.main := by
  intro n k hk _
  have hmax (i : Fin (n+1)) : k i ≤ k (Fin.last n) := hk.monotone (Fin.le_last i)
  constructor
  · rintro ⟨σ,hσ⟩
    refine ⟨OMA.S_mo_257899.inventory k σ 0,?_⟩
    rw [← OMA.S_mo_257899.total_inventory k hmax σ]
    calc
      _ = ∑ _ : Fin (n+1), OMA.S_mo_257899.inventory k σ 0 :=
        Finset.sum_congr rfl fun i _ => hσ i 0
      _ = _ := by simp
  · intro hd
    have hz : ∑ i, (k i : ZMod (n+1)) = 0 := by
      rw [← Nat.cast_sum]
      exact (ZMod.natCast_eq_zero_iff ..).mpr hd
    obtain ⟨a,b,hab⟩ := OMA.S_mo_257899.hall_differences (ZMod.finEquiv (n+1)).toEquiv
      0 (fun i => (k i : ZMod (n+1))) hz
    obtain ⟨σ,hσ⟩ := OMA.S_mo_257899.inventory_cover k hmax a
    refine ⟨σ,fun s t => ?_⟩
    exact_mod_cast (hσ s).trans ((OMA.S_mo_257899.cover_constant a b k hab _ _).trans (hσ t).symm)
