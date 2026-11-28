import OMAStatements.S_mo_261687

/-!
# Strictness of the distinct-root bound for three or more prime factors

Source: user6671, https://mathoverflow.net/questions/261687 (CC BY-SA 3.0).
Credit: @connoranderson.

An even integer between the first and third primes gives a value of P
with absolute value above one. Maximizing the square of P between the
endpoint roots supplies a critical point outside the zero sets of P
and P+1. Counting repeated roots in these two disjoint fibers, together
with the additional critical point, yields the strict Mason–Stothers bound.
-/

namespace OMA.S_mo_261687

lemma critical_away (P : Polynomial ℝ) (a b t : ℝ) (hat : a < t) (htb : t < b)
    (ha : P.eval a=0) (hb : P.eval b=0) (ht : 1 < |P.eval t|) :
    ∃ c : ℝ, P.derivative.eval c=0 ∧ 1 < |P.eval c| := by
  let f (x : ℝ) := (P.eval x)^2
  obtain ⟨c, hc, hmax⟩ : ∃ c ∈ Set.Icc a b, IsMaxOn f (Set.Icc a b) c :=
    isCompact_Icc.exists_isMaxOn ⟨t, hat.le, htb.le⟩ (P.continuous.pow 2).continuousOn
  have htc : (P.eval t)^2 ≤ (P.eval c)^2 := hmax ⟨hat.le, htb.le⟩
  have hval : 1 < |P.eval c| := ht.trans_le (sq_le_sq.mp htc)
  have hac : a < c := hc.1.lt_of_ne (by rintro rfl; norm_num [ha] at hval)
  have hcb : c < b := hc.2.lt_of_ne (by rintro rfl; norm_num [hb] at hval)
  have he := (hmax.isLocalMax (Icc_mem_nhds hac hcb)).hasDerivAt_eq_zero ((P.hasDerivAt c).pow 2)
  have hne : P.eval c ≠ 0 := by rintro h; norm_num [h] at hval
  refine ⟨c, ?_, hval⟩
  simpa [hne] using he

end OMA.S_mo_261687

namespace OMA.S_mo_261687
open Polynomial

/-- Keep all but the first copy of each distinct root. -/
private noncomputable def repeated (P : ℂ[X]) : Multiset ℂ :=
  P.roots - P.roots.dedup

private lemma count_repeated_le (P : ℂ[X]) (a : ℂ) :
    (repeated P).count a ≤ P.derivative.roots.count a := by
  classical
  by_cases ha : a ∈ P.roots
  · simpa [repeated, Multiset.count_sub, Multiset.count_dedup, ha, count_roots]
      using rootMultiplicity_sub_one_le_derivative_rootMultiplicity P a
  · simp [repeated, Multiset.count_sub, ha]

private lemma count_repeated_zero (P : ℂ[X]) (a : ℂ) (h : a ∉ P.roots) :
    (repeated P).count a = 0 := by
  simp [repeated, Multiset.count_sub, Multiset.count_eq_zero.mpr h]

private lemma card_repeated (P : ℂ[X]) :
    (repeated P).card = P.natDegree - P.roots.toFinset.card := by
  classical
  rw [repeated, Multiset.card_sub (Multiset.dedup_le _), ← (IsAlgClosed.splits P).natDegree_eq_card_roots]
  rfl

lemma strict_count (P : Polynomial ℂ) (hd : 0 < P.natDegree) (c : ℂ)
    (hcrit : P.derivative.eval c = 0) (h0 : P.eval c ≠ 0) (h1 : (P+1).eval c ≠ 0) :
    P.natDegree + 1 < P.roots.toFinset.card + (P+1).roots.toFinset.card := by
  classical
  have hcP : c ∉ P.roots := fun h => h0 (isRoot_of_mem_roots h)
  have hcQ : c ∉ (P+1).roots := fun h => h1 (isRoot_of_mem_roots h)
  have hcD : c ∈ P.derivative.roots := (mem_roots (derivative_ne_zero.mpr hd.ne')).mpr hcrit
  have hle : c ::ₘ (repeated P + repeated (P+1)) ≤ P.derivative.roots := by
    apply Multiset.le_iff_count.mpr
    intro a
    by_cases hac : a = c
    · subst a
      simpa only [Multiset.count_cons_self, Multiset.count_add, count_repeated_zero _ _ hcP,
        count_repeated_zero _ _ hcQ, zero_add] using Nat.succ_le_of_lt (Multiset.count_pos.mpr hcD)
    rw [Multiset.count_cons_of_ne hac, Multiset.count_add]
    by_cases ha : a ∈ P.roots
    · have haQ : a ∉ (P+1).roots := by
        intro hh
        have h : (P+1).eval a = 0 := isRoot_of_mem_roots hh
        simp [show P.eval a = 0 from isRoot_of_mem_roots ha] at h
      rw [count_repeated_zero _ _ haQ, add_zero]
      exact count_repeated_le P a
    · rw [count_repeated_zero _ _ ha, zero_add]
      simpa using count_repeated_le (P+1) a
  have hcard := Multiset.card_le_card hle
  have degQ : (P+1).natDegree = P.natDegree := by simpa only [C_1] using (natDegree_add_C (p:=P) (a:=1))
  rw [Multiset.card_cons, Multiset.card_add, card_repeated, card_repeated,
    ← (IsAlgClosed.splits P.derivative).natDegree_eq_card_roots, natDegree_derivative, degQ] at hcard
  omega

end OMA.S_mo_261687

namespace OMA.S_mo_261687

open Polynomial

private lemma factor_eval (n : ℕ) (t : ℝ) :
    (primePoly ℝ n).eval t = (n.primeFactorsList.map (fun p : ℕ => t-(p:ℝ))).prod := by
  simp [primePoly,eval_list_prod,List.map_map,Function.comp_def]

private lemma abs_prod_factors (l : List ℕ) (t : ℝ) (h : ∀ p ∈ l, 1 ≤ |t-(p:ℝ)|) :
    1 ≤ |(l.map (fun p : ℕ => t-(p:ℝ))).prod| ∧
    ((∃ p ∈ l, 1 < |t-(p:ℝ)|) → 1 < |(l.map (fun p : ℕ => t-(p:ℝ))).prod|) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (List.mem_cons_self ..)
    obtain ⟨hl,hs⟩ := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
    change 1 ≤ |(t-(a:ℝ)) * (l.map (fun p : ℕ => t-(p:ℝ))).prod| ∧ _
    rw [abs_mul]
    change _ ∧ ((∃ p ∈ a::l, 1 < |t-(p:ℝ)|) → 1 < |(t-(a:ℝ)) * (l.map (fun p : ℕ => t-(p:ℝ))).prod|)
    rw [abs_mul]
    refine ⟨one_le_mul_of_one_le_of_one_le ha hl,?_⟩
    rintro ⟨p,hp,hp'⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact one_lt_mul_of_lt_of_le hp' hl
    · exact one_lt_mul_of_le_of_lt ha (hs ⟨p,hp,hp'⟩)

private lemma prime_gap (n : ℕ) (hn : 3 ≤ n.primeFactors.card) :
    ∃ a b t : ℝ, a < t ∧ t < b ∧ (primePoly ℝ n).eval a=0 ∧
      (primePoly ℝ n).eval b=0 ∧ 1 < |(primePoly ℝ n).eval t| := by
  classical
  let s := n.primeFactors
  have hs : 3 ≤ s.card := hn
  let e := s.orderEmbOfFin rfl
  let i : Fin s.card := ⟨0,by omega⟩
  let j : Fin s.card := ⟨1,by omega⟩
  let k : Fin s.card := ⟨2,by omega⟩
  let a := e i
  let m := e j
  let b := e k
  have ham : a < m := e.strictMono (by change (0:ℕ)<1; decide)
  have hmb : m < b := e.strictMono (by change (1:ℕ)<2; decide)
  have hmem (u : Fin s.card) : e u ∈ n.primeFactors := s.orderEmbOfFin_mem rfl u
  have ha := Nat.prime_of_mem_primeFactors (hmem i)
  have hm := Nat.prime_of_mem_primeFactors (hmem j)
  have hb := Nat.prime_of_mem_primeFactors (hmem k)
  change Nat.Prime a at ha
  change Nat.Prime m at hm
  change Nat.Prime b at hb
  have hmodm := hm.eq_two_or_odd
  have hmodb := hb.eq_two_or_odd
  have htwo := ha.two_le
  have htb : m+1 < b := by omega
  have hnp : ¬ Nat.Prime (m+1) := by
    intro hp
    have hh := hp.eq_two_or_odd
    omega
  have hne (p : ℕ) (hp : p ∈ n.primeFactorsList) : m+1 ≠ p :=
    fun h => hnp (h ▸ Nat.prime_of_mem_primeFactorsList hp)
  have hunit (p : ℕ) (hp : p ∈ n.primeFactorsList) : 1 ≤ |((m+1 : ℕ) : ℝ)-(p:ℝ)| := by
    rcases lt_or_gt_of_ne (hne p hp) with h|h
    · rw [abs_of_nonpos (by exact_mod_cast (show (m+1:ℤ) - p ≤ 0 by omega))]
      exact_mod_cast (show (1:ℤ) ≤ -((m+1:ℤ)-p) by omega)
    · rw [abs_of_nonneg (by exact_mod_cast (show (0:ℤ) ≤ (m+1:ℤ)-p by omega))]
      exact_mod_cast (show (1:ℤ) ≤ (m+1:ℤ)-p by omega)
  have hal : a ∈ n.primeFactorsList := Nat.mem_primeFactors_iff_mem_primeFactorsList.mp (hmem i)
  have hbl : b ∈ n.primeFactorsList := Nat.mem_primeFactors_iff_mem_primeFactorsList.mp (hmem k)
  have hr (x : ℕ) (hx : x ∈ n.primeFactorsList) : (primePoly ℝ n).eval (x:ℝ) = 0 := by
    rw [factor_eval,List.prod_eq_zero_iff]
    exact List.mem_map.mpr ⟨x,hx,sub_self _⟩
  have hat : a < m+1 := by omega
  refine ⟨a,b,((m+1:ℕ):ℝ),by exact_mod_cast hat,by exact_mod_cast htb,hr a hal,hr b hbl,?_⟩
  rw [factor_eval]
  apply (abs_prod_factors _ _ hunit).2
  refine ⟨a,hal,?_⟩
  rw [abs_of_nonneg (by exact_mod_cast (show (0:ℤ) ≤ (m+1:ℤ)-a by omega))]
  exact_mod_cast (show (1:ℤ) < (m+1:ℤ)-a by omega)

end OMA.S_mo_261687

namespace OMA.S_mo_261687

open Polynomial

private lemma root_data (n : ℕ) :
    (primePoly ℂ n).natDegree = n.primeFactorsList.length ∧
      (primePoly ℂ n).roots.toFinset.card = n.primeFactors.card := by
  classical
  constructor
  · unfold primePoly
    rw [natDegree_multiset_prod_X_sub_C_eq_card]
    simp
  · have h : (primePoly ℂ n).roots.toFinset =
        n.primeFactors.image (fun p : ℕ => (p : ℂ)) := by
      ext z
      unfold primePoly
      rw [roots_multiset_prod_X_sub_C]
      simp only [Multiset.mem_toFinset,Multiset.mem_map,Multiset.mem_coe,Finset.mem_image,
        Nat.mem_primeFactors_iff_mem_primeFactorsList]
    rw [h,Finset.card_image_of_injective _ Nat.cast_injective]

private lemma map_factors (n : ℕ) :
    (primePoly ℝ n).map (algebraMap ℝ ℂ) = primePoly ℂ n := by
  simp [primePoly,Polynomial.map_list_prod,List.map_map,Function.comp_def]

lemma result (n : ℕ) (hn : 3 ≤ n.primeFactors.card) :
    n.primeFactorsList.length - n.primeFactors.card + 1 <
      ((primePoly ℂ n)+1).roots.toFinset.card := by
  obtain ⟨a,b,t,hat,htb,ha,hb,ht⟩ := prime_gap n hn
  obtain ⟨c,hc,hm⟩ := critical_away _ a b t hat htb ha hb ht
  let P := primePoly ℂ n
  have hval : P.eval (c:ℂ) = (↑((primePoly ℝ n).eval c) : ℂ) := by
    rw [show P = (primePoly ℝ n).map (algebraMap ℝ ℂ) from (map_factors n).symm]
    exact Polynomial.eval_map_apply (algebraMap ℝ ℂ) c
  have hder : P.derivative.eval (c:ℂ) = 0 := by
    rw [show P = (primePoly ℝ n).map (algebraMap ℝ ℂ) from (map_factors n).symm,
      Polynomial.derivative_map]
    change _ = algebraMap ℝ ℂ (0:ℝ)
    rw [← hc]
    exact Polynomial.eval_map_apply (algebraMap ℝ ℂ) c
  have h0 : P.eval (c:ℂ) ≠ 0 := by
    rw [hval,Complex.ofReal_ne_zero]
    intro h; norm_num [h] at hm
  have h1 : (P+1).eval (c:ℂ) ≠ 0 := by
    rw [eval_add,eval_one,hval]
    intro h
    have hh : (primePoly ℝ n).eval c + 1 = 0 := by exact_mod_cast h
    have he : (primePoly ℝ n).eval c = -1 := by linarith
    simp [he] at hm
  obtain ⟨hd,hr⟩ := root_data n
  have hl : n.primeFactors.card ≤ n.primeFactorsList.length := List.toFinset_card_le ..
  have hd' : 0 < P.natDegree := by change 0 < (primePoly ℂ n).natDegree; omega
  have h := strict_count P hd' c hder h0 h1
  dsimp only [P] at h
  omega

end OMA.S_mo_261687

theorem OMA.solution : type_of% @OMA.S_mo_261687.main := OMA.S_mo_261687.result
