import OMAStatements.S_oeis_a249280
import Mathlib.NumberTheory.PowModTotient

/-!
# Finite tests for pandigital reverse-and-add trajectories

Charles R. Greathouse IV asked whether positive decimal reverse-and-add orbits reach all
ten digits in uniformly bounded time. The entry reports a 73-step example and a search
through one billion initial values (https://oeis.org/A249280). We verify a 75-step first hit.

For any proposed horizon T, every orbit avoiding full digit coverage through T has a
shorter such orbit with at most 54 * 12^T + 1 digits in its starting value. The proof
cuts matching pairs of blocks from every row of a finite orbit. Matching low and high
carries preserve addition. When an extra leading digit appears, the corresponding
output digits must match too. A potential on the two end digits bounds the number of
length increases by (T+3)/2. These observations give a finite search equivalent to each
proposed uniform bound, and two smaller finite searches sufficient for the conjecture.

We also prove exact orbit embeddings using separated decimal copies and digit
complements. The existence of a successful uniform bound remains open.
-/

namespace Reverse249
open OMA.S_oeis_a249280

theorem digits_copy (n s : ℕ) (hn : 0 < n) (hs : (Nat.digits 10 n).length ≤ s) :
    Nat.digits 10 (n+10^s*n) =
      Nat.digits 10 n ++ List.replicate (s-(Nat.digits 10 n).length) 0 ++ Nat.digits 10 n := by
  have h := Nat.digits_append_zeroes_append_digits (b:=10) (n:=n)
    (k:=s-(Nat.digits 10 n).length) (by decide) hn
  simpa only [Nat.add_sub_of_le hs] using h.symm

theorem rev_copy (n s : ℕ) (hn : 0 < n) (hs : (Nat.digits 10 n).length ≤ s) :
    Nat.ofDigits 10 (Nat.digits 10 (n+10^s*n)).reverse =
      Nat.ofDigits 10 (Nat.digits 10 n).reverse + 10^s * Nat.ofDigits 10 (Nat.digits 10 n).reverse := by
  rw [digits_copy n s hn hs]
  simp only [List.reverse_append,List.reverse_replicate,Nat.ofDigits_append,Nat.ofDigits_replicate_zero,
    List.length_replicate,List.length_reverse,zero_add]
  rw [← Nat.mul_assoc, ← pow_add, Nat.add_sub_of_le hs]

theorem revAdd_copy (n s : ℕ) (hn : 0 < n) (hs : (Nat.digits 10 n).length ≤ s) :
    revAdd (n+10^s*n) = revAdd n+10^s*revAdd n := by
  simp only [revAdd,rev_copy n s hn hs]
  ring

theorem iterate_mono (n i j : ℕ) (h : i≤j) :
    revAdd^[i] n ≤ revAdd^[j] n := by
  apply monotone_nat_of_le_succ (f:=fun k => revAdd^[k] n) _ h
  intro k
  rw [Function.iterate_succ_apply']
  exact Nat.le_add_right _ _

theorem iterate_copy (n s t k : ℕ) (hn : 0 < n) (hk : k≤t)
    (hs : (Nat.digits 10 (revAdd^[t] n)).length ≤ s) :
    revAdd^[k] (n+10^s*n) = revAdd^[k] n+10^s*(revAdd^[k] n) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih (by omega),Function.iterate_succ_apply',revAdd_copy]
    · exact hn.trans_le (iterate_mono n 0 k (by omega))
    · exact (Nat.le_length_digits_le 10 _ _ (iterate_mono n k t (by omega))).trans hs

theorem pandigital_copy_iff (n s : ℕ) (hn : 0 < n) (hs : (Nat.digits 10 n).length < s) :
    IsPandigital (n+10^s*n) ↔ ∀ d, 0 < d → d < 10 → d ∈ Nat.digits 10 n := by
  unfold IsPandigital
  rw [digits_copy n s hn hs.le]
  constructor
  · intro h d hd h10
    specialize h d h10
    simpa [List.mem_replicate, Nat.ne_of_gt hd] using h
  · intro h d hd
    by_cases hz : d=0
    · subst d
      simp [List.mem_replicate,show s-(Nat.digits 10 n).length ≠ 0 by omega]
    · simp [h d (Nat.pos_of_ne_zero hz) hd]

theorem iterate_pandigital_copy_iff (n s t k : ℕ) (hn : 0 < n) (hk : k≤t)
    (hs : (Nat.digits 10 (revAdd^[t] n)).length < s) :
    IsPandigital (revAdd^[k] (n+10^s*n)) ↔ ∀ d, 0 < d → d < 10 → d ∈ Nat.digits 10 (revAdd^[k] n) := by
  rw [iterate_copy n s t k hn hk hs.le]
  exact pandigital_copy_iff _ _ (hn.trans_le (iterate_mono n 0 k (by omega)))
    ((Nat.le_length_digits_le 10 _ _ (iterate_mono n k t hk)).trans_lt hs)

end Reverse249

namespace Reverse249
open OMA.S_oeis_a249280

/- A bound on decimal growth and a simultaneous compression of every finite orbit avoiding pandigitality.
The shorter orbit uses only digits that occurred at the same time in the original. -/
set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8000 in
theorem decimal_compression_results :
    (∀ x T : ℕ, 0 < x → (Nat.digits 10 (revAdd^[T] x)).length ≤ (Nat.digits 10 x).length+(T+3)/2) ∧
    (∀ T n : ℕ, 0 < n → (∀ k ≤ T, ¬IsPandigital (revAdd^[k] n)) → ∃ m : ℕ, 0 < m ∧ (Nat.digits 10 m).length ≤ 2*(4^T*9^(min T ((T+3)/2)))+1 ∧
      ∀ k ≤ T, ∀ d ∈ Nat.digits 10 (revAdd^[k] m), d ∈ Nat.digits 10 (revAdd^[k] n)) := by
  let cut (x k d : ℕ) : ℕ := x % 10^k + 10^k*(x/10^(k+d))

  let shrink (x l u : ℕ) : ℕ := cut (cut x ((Nat.digits 10 x).length-u) (u-l)) l (u-l)

  let rev (x : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 x).reverse

  let carry (x w : ℕ) : ℕ := (x%10^w+rev x%10^w)/10^w

  have digit_carry_lt_two (a b k : ℕ) :
      (a % 10^k + b % 10^k) / 10^k < 2 := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).2
    have ha := Nat.mod_lt a (show 0 < 10^k by positivity)
    have hb := Nat.mod_lt b (show 0 < 10^k by positivity)
    omega

  -- When the incoming carries at both cuts match, deleting a block commutes with addition.
  have splice_add (a b k d : ℕ)
      (same : (a % 10^(k+d) + b % 10^(k+d)) / 10^(k+d) =
        (a % 10^k + b % 10^k) / 10^k) :
      (a+b) % 10^k + 10^k * ((a+b) / 10^(k+d)) =
        (a % 10^k + 10^k * (a / 10^(k+d))) +
        (b % 10^k + 10^k * (b / 10^(k+d))) := by
    have quot (v : ℕ) (hv : 0 < v) :
        (a+b)/v = (a%v+b%v)/v + (a/v+b/v) := by
      calc
        (a+b)/v = (a%v+b%v+v*(a/v+b/v))/v := by
          congr 1
          calc
            a+b = (a%v+v*(a/v))+(b%v+v*(b/v)) := by
              rw [Nat.mod_add_div, Nat.mod_add_div]
            _ = _ := by ring
        _ = _ := Nat.add_mul_div_left _ _ hv
    rw [Nat.add_mod,quot _ (by positivity),same]
    calc
      _ = ((a % 10^k + b % 10^k) % 10^k + 10^k*((a % 10^k + b % 10^k) / 10^k)) +
        10^k*(a/10^(k+d)+b/10^(k+d)) := by ring
      _ = _ := by rw [Nat.mod_add_div]; ring

  have splice_shift (x k d : ℕ)
      (same : x / 10^k % 10 = x / 10^(k+d) % 10) :
      x % 10^k + 10^k * (x / 10^(k+d)) =
        x % 10^(k+1) + 10^(k+1) * (x / 10^(k+1+d)) := by
    have h : k+1+d = k+d+1 := by omega
    rw [h, pow_succ, Nat.mod_mul, same, pow_succ, ← Nat.div_div_eq_div_mul]
    calc
      _ = x % 10^k + 10^k * ((x/10^(k+d))%10+10*((x/10^(k+d))/10)) := by rw [Nat.mod_add_div]
      _ = _ := by ring

  have splice_low_mod (x k d w : ℕ) (hw : w≤k) :
      (x % 10^k + 10^k*(x / 10^(k+d))) % 10^w = x % 10^w := by
    have hd : 10^w ∣ 10^k := pow_dvd_pow 10 hw
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hd _),
      Nat.add_zero,Nat.mod_mod,Nat.mod_mod_of_dvd _ hd]

  have cut_word (A B C : List ℕ) (hAB : ∀ z∈A++B, z<10) :
      cut (Nat.ofDigits 10 (A++B++C)) A.length B.length =
        Nat.ofDigits 10 (A++C) := by
    have ha : Nat.ofDigits 10 A < 10^A.length :=
      Nat.ofDigits_lt_base_pow_length (by decide) fun z hz => hAB z (List.mem_append_left _ hz)
    have hab := Nat.ofDigits_lt_base_pow_length (by decide : 1<10) hAB
    have low : (Nat.ofDigits 10 (A++B++C)) % 10^A.length = Nat.ofDigits 10 A := by
      rw [List.append_assoc,Nat.ofDigits_append,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt ha]
    have high : Nat.ofDigits 10 (A++B++C) / 10^(A.length+B.length) = Nat.ofDigits 10 C := by
      rw [Nat.ofDigits_append, List.length_append,Nat.add_mul_div_left _ _ (by positivity)]
      simpa only [List.length_append] using
        (show Nat.ofDigits 10 (A++B) / 10^(A++B).length + Nat.ofDigits 10 C = Nat.ofDigits 10 C by
          rw [Nat.div_eq_of_lt hab,Nat.zero_add])
    dsimp only [cut]
    rw [low,high,Nat.ofDigits_append]

  -- Remove two matching-width blocks, one at each end, while retaining the same leading digit.
  have double_cut_word (A B C D E : List ℕ)
      (hD : D.length = B.length)
      (hd : ∀z∈A++B++C++D++E, z<10) :
      cut (cut (Nat.ofDigits 10 (A++B++C++D++E)) (A++B++C).length B.length) A.length B.length =
        Nat.ofDigits 10 (A++C++E) := by
    have hh := cut_word (A++B++C) D E (fun z hz => hd z (List.mem_append_left _ hz))
    rw [hD] at hh
    rw [hh]
    have hl := cut_word A B (C++E) (fun z hz => hd z (by simp only [List.mem_append] at *; grind))
    simpa only [List.append_assoc] using hl

  have split_symmetric_word (W : List ℕ) (l u : ℕ) (hlu : l≤u) (room : 2*u≤W.length) :
      ∃ A B C D E : List ℕ, W=A++B++C++D++E ∧ A.length=l ∧ B.length=u-l ∧
        C.length=W.length-2*u ∧ D.length=u-l ∧ E.length=l := by
    have split (w : List ℕ) (i : ℕ) (h : i≤w.length) :
        ∃ a b : List ℕ, w=a++b ∧ a.length=i ∧ b.length=w.length-i := by
      exact ⟨w.take i,w.drop i,(List.take_append_drop _ _).symm,
        by simp [Nat.min_eq_left h],List.length_drop⟩
    obtain ⟨A,w₁,h₁,hA,hw₁⟩ := split W l (by omega)
    obtain ⟨B,w₂,h₂,hB,hw₂⟩ := split w₁ (u-l) (by omega)
    obtain ⟨C,w₃,h₃,hC,hw₃⟩ := split w₂ (W.length-2*u) (by omega)
    obtain ⟨D,E,h₄,hD,hE⟩ := split w₃ (u-l) (by omega)
    refine ⟨A,B,C,D,E,?_,hA,hB,hC,hD,by omega⟩
    rw [h₁,h₂,h₃,h₄]
    simp only [List.append_assoc]

  have shrink_word (x l u : ℕ) (hl : 0<l) (hlu : l≤u)
      (hroom : 2*u≤(Nat.digits 10 x).length) :
      0<shrink x l u ∧ ((Nat.digits 10 (shrink x l u)).length + 2*(u-l) =
        (Nat.digits 10 x).length) ∧
      (∀ z∈Nat.digits 10 (shrink x l u), z∈Nat.digits 10 x) ∧
      rev (shrink x l u) = cut (cut (rev x) ((Nat.digits 10 x).length-u) (u-l)) l (u-l) := by
    obtain ⟨A,B,C,D,E,hW,ha,hb,hc,hd,he⟩ := split_symmetric_word (Nat.digits 10 x) l u hlu hroom
    have hE : E ≠ [] := by intro h; simp [h] at he; omega
    have hx : x ≠ 0 := by intro h; simp [h] at hroom; omega
    have hdigits : ∀ z∈A++B++C++D++E, z<10 := by
      intro z hz
      exact Nat.digits_lt_base (by decide) (hW ▸ hz)
    have hsub : ∀ z∈A++C++E, z∈Nat.digits 10 x := by
      rw [hW]
      simp only [List.mem_append]
      grind
    have hlen₁ : (A++B++C).length = (Nat.digits 10 x).length-u := by
      simp only [List.length_append]; omega
    have hcut := double_cut_word A B C D E (by omega) hdigits
    rw [← hW,Nat.ofDigits_digits,hlen₁,ha,hb] at hcut
    change shrink x l u = Nat.ofDigits 10 (A++C++E) at hcut
    have hdr : Nat.digits 10 (shrink x l u) = A++C++E := by
      rw [hcut]
      apply Nat.digits_ofDigits _ (by decide) _ (fun z hz => Nat.digits_lt_base (by decide) (hsub z hz))
      intro hn
      have hold := Nat.getLast_digit_ne_zero 10 hx
      rw [List.getLast_congr _ (by simp [hE]) hW,
        List.getLast_append_of_ne_nil _ hE] at hold
      rw [List.getLast_append_of_ne_nil _ hE]
      exact hold
    have hrevDigits : (Nat.digits 10 x).reverse =
        E.reverse++D.reverse++C.reverse++B.reverse++A.reverse := by
      rw [hW]; simp only [List.reverse_append,List.append_assoc]
    have hlen₂ : (E.reverse++D.reverse++C.reverse).length = (Nat.digits 10 x).length-u := by
      simp only [List.length_append,List.length_reverse]; omega
    have hr := double_cut_word E.reverse D.reverse C.reverse B.reverse A.reverse
      (by simp only [List.length_reverse]; omega) (by
        intro z hz
        rw [←hrevDigits,List.mem_reverse] at hz
        exact Nat.digits_lt_base (by decide) hz)
    rw [←hrevDigits,hlen₂,List.length_reverse,List.length_reverse,he,hd] at hr
    refine ⟨Nat.pos_of_ne_zero (Nat.digits_ne_nil_iff_ne_zero.mp (by rw [hdr]; simp [hE])),
      ?_, by rwa [hdr], ?_⟩
    · rw [hdr]
      simp only [List.length_append]
      omega
    · unfold rev
      rw [hdr,hr]
      simp only [List.reverse_append,List.append_assoc]

  have shrink_spec (x l u : ℕ) (hl : 0<l) (hlu : l≤u)
      (hroom : 2*u≤(Nat.digits 10 x).length) :
      0<shrink x l u ∧ ((Nat.digits 10 (shrink x l u)).length + 2*(u-l) =
        (Nat.digits 10 x).length) ∧
      ∀ z∈Nat.digits 10 (shrink x l u), z∈Nat.digits 10 x := by
    obtain ⟨h₁,h₂,h₃,_⟩ := shrink_word x l u hl hlu hroom
    exact ⟨h₁,h₂,h₃⟩

  have revAdd_length_le (x : ℕ) :
      (Nat.digits 10 (revAdd x)).length ≤ (Nat.digits 10 x).length+1 := by
    apply (Nat.digits_length_le_iff (by decide : 1<10) _).2
    have h := Nat.lt_base_pow_length_digits (m:=x) (by decide : 1<10)
    have hr := Nat.ofDigits_lt_base_pow_length (b:=10) (l:=(Nat.digits 10 x).reverse)
      (by decide) (fun z hz => Nat.digits_lt_base (by decide) (List.mem_reverse.mp hz))
    rw [List.length_reverse] at hr
    unfold revAdd
    rw [pow_succ]
    omega

  -- A new leading digit shifts the high cut by one column. The boundary digit resolves that shift.
  have revAdd_shrink (x l u : ℕ) (hl : 0<l) (hlu : l≤u)
      (hroom : 2*u≤(Nat.digits 10 x).length)
      (low : carry x l = carry x u)
      (high : carry x ((Nat.digits 10 x).length-l) = carry x ((Nat.digits 10 x).length-u))
      (edge : (Nat.digits 10 (revAdd x)).length ≠ (Nat.digits 10 x).length →
        (revAdd x)/10^((Nat.digits 10 x).length-l)%10 =
          (revAdd x)/10^((Nat.digits 10 x).length-u)%10) :
      revAdd (shrink x l u) = shrink (revAdd x) l u := by
    let k := (Nat.digits 10 x).length-u
    let d := u-l
    have hhi : k+d = (Nat.digits 10 x).length-l := by dsimp [k,d]; omega
    have hlo : l+d = u := by dsimp [d]; omega
    have hk : u≤k := by dsimp [k]; omega
    have hhi_add : cut (revAdd x) k d = cut x k d + cut (rev x) k d := by
      apply splice_add
      change carry x (k+d) = carry x k
      rw [hhi]
      exact high
    have hmod (w : ℕ) (hw : w≤u) :
        ((cut x k d)%10^w + (cut (rev x) k d)%10^w)/10^w = carry x w := by
      unfold cut carry
      rw [splice_low_mod x k d w (hw.trans hk),splice_low_mod (rev x) k d w (hw.trans hk)]
    have hlo_add : cut (cut x k d + cut (rev x) k d) l d =
        cut (cut x k d) l d + cut (cut (rev x) k d) l d := by
      apply splice_add
      rw [hlo,hmod u (by omega),hmod l hlu,low]
    have hs : revAdd (shrink x l u) = cut (cut (revAdd x) k d) l d := by
      change shrink x l u + rev (shrink x l u) = _
      rw [(shrink_word x l u hl hlu hroom).2.2.2,hhi_add,hlo_add]
    rw [hs]
    unfold shrink
    change cut (cut (revAdd x) k d) l d = cut (cut (revAdd x) ((Nat.digits 10 (revAdd x)).length-u) d) l d
    by_cases hn : (Nat.digits 10 (revAdd x)).length = (Nat.digits 10 x).length
    · rw [hn]
    · have hlen₀ := Nat.le_length_digits_le 10 x (revAdd x) (Nat.le_add_right _ _)
      have hlen₁ := revAdd_length_le x
      have hs₁ : (Nat.digits 10 (revAdd x)).length-u = k+1 := by dsimp [k]; omega
      rw [hs₁]
      congr 1
      apply splice_shift
      rw [hhi]
      exact (edge hn).symm

  -- The potential is indexed by the sum of the first and last digits, which is at most eighteen.
  let endPotential (s : ℕ) : ℕ :=
    ([0,0,0,0,1,0,1,1,1,2,1,1,1,2,1,2,2,2,3] : List ℕ).getD s 0

  let endSum (x : ℕ) : ℕ := x/10^((Nat.digits 10 x).length-1)+x%10

  have end_potential_table (s : Fin 19) (c : Fin 2) :
      let a := s.val+c.val
      2*(a/10) + endPotential ((if a/10=0 then a else 1)+s.val%10) ≤ endPotential s+1 := by
    revert s c
    decide +kernel

  have decimal_ends (x : ℕ) (hx : 0<x) :
      0 < x/10^((Nat.digits 10 x).length-1) ∧
      x/10^((Nat.digits 10 x).length-1)<10 ∧
      rev x%10 = x/10^((Nat.digits 10 x).length-1) ∧
      rev x/10^((Nat.digits 10 x).length-1) = x%10 := by
    have endpoints (w : List ℕ) (hw : w ≠ []) (hd : ∀z∈w,z<10) :
        Nat.ofDigits 10 w%10 = w.head hw ∧ Nat.ofDigits 10 w / 10^(w.length-1) = w.getLast hw := by
      constructor
      · obtain ⟨y,t,rfl⟩ := List.exists_cons_of_ne_nil hw
        rw [Nat.ofDigits_cons, Nat.add_mul_mod_self_left]
        simpa using Nat.mod_eq_of_lt (hd y (by simp))
      · have hlow : Nat.ofDigits 10 w.dropLast < 10^w.dropLast.length :=
          Nat.ofDigits_lt_base_pow_length (by decide) (fun z hz => hd z (List.mem_of_mem_dropLast hz))
        conv_lhs => lhs; rw [← List.dropLast_append_getLast hw, Nat.ofDigits_append,Nat.ofDigits_singleton]
        rw [←List.length_dropLast,Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlow, Nat.zero_add]
    have hw : Nat.digits 10 x ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hx.ne'
    have ⟨low,high⟩ := endpoints (Nat.digits 10 x) hw (fun _ hz => Nat.digits_lt_base (by decide) hz)
    rw [Nat.ofDigits_digits] at low high
    have ⟨lowR,highR⟩ := endpoints (Nat.digits 10 x).reverse (by simpa using hw)
      (fun _ hz => Nat.digits_lt_base (by decide) (List.mem_reverse.mp hz))
    rw [List.head_reverse] at lowR
    rw [List.getLast_reverse, List.length_reverse] at highR
    rw [high]
    exact ⟨Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero 10 hx.ne'),
      Nat.digits_lt_base (by decide) (List.getLast_mem _),lowR,highR.trans low.symm⟩

  have end_sum_lt (x : ℕ) (hx : 0<x) : endSum x<19 := by
    have hb := (decimal_ends x hx).2.1
    have hm := Nat.mod_lt x (by decide : 0<10)
    unfold endSum
    omega

  have end_growth_step (x : ℕ) (hx : 0<x) :
      2*(Nat.digits 10 (revAdd x)).length + endPotential (endSum (revAdd x)) ≤
      2*(Nat.digits 10 x).length + endPotential (endSum x)+1 := by
    let L := (Nat.digits 10 x).length
    let k := L-1
    let c := carry x k
    have hL : 0<L := List.length_pos_iff.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr hx.ne')
    have hk : k+1=L := by dsimp [k]; omega
    have hc : c<2 := digit_carry_lt_two x (rev x) k
    obtain ⟨_,_,hrevLo,hrevHi⟩ := decimal_ends x hx
    have hlow : revAdd x%10 = endSum x%10 := by
      change (x+rev x)%10 = _
      rw [Nat.add_mod,hrevLo]
      simp only [endSum,Nat.add_comm]
    have high : revAdd x / 10^k = endSum x+c := by
      let v := 10^k
      have hv : 0<v := by dsimp [v]; positivity
      have h : x+rev x = (x%v+rev x%v) + v*(x/v+rev x/v) := by
        calc
          x+rev x = (x%v+v*(x/v))+(rev x%v+v*(rev x/v)) := by rw [Nat.mod_add_div,Nat.mod_add_div]
          _ = _ := by ring
      change (x+rev x)/v = _
      rw [h,Nat.add_mul_div_left _ _ hv]
      change c + (x/10^((Nat.digits 10 x).length-1) + rev x/10^((Nat.digits 10 x).length-1)) = _
      rw [hrevHi]
      exact Nat.add_comm _ _
    have tab := end_potential_table ⟨endSum x, end_sum_lt x hx⟩ ⟨c,hc⟩
    dsimp only at tab
    let M := (Nat.digits 10 (revAdd x)).length
    have hM₀ : L≤M := Nat.le_length_digits_le 10 x (revAdd x) (Nat.le_add_right _ _)
    have hM₁ : M≤L+1 := revAdd_length_le x
    obtain ⟨pos,lt10,_⟩ := decimal_ends (revAdd x) (hx.trans_le (Nat.le_add_right _ _))
    change 0<revAdd x/10^(M-1) at pos
    change revAdd x/10^(M-1)<10 at lt10
    change 2*M+endPotential (endSum (revAdd x)) ≤ 2*L+endPotential (endSum x)+1
    by_cases hML : M=L
    · have htop : revAdd x/10^(M-1) = endSum x+c := by rw [hML]; exact high
      rw [htop] at lt10
      have hn : (endSum x+c)/10=0 := Nat.div_eq_of_lt lt10
      rw [hn] at tab
      simp only [ite_true, Nat.mul_zero, Nat.zero_add] at tab
      have hs : endSum (revAdd x) = endSum x+c+endSum x%10 := by
        change revAdd x/10^(M-1)+revAdd x%10 = _
        rw [htop,hlow]
      rw [hs,hML]
      omega
    · have hM : M=L+1 := by omega
      have hh : M-1=k+1 := by omega
      have htop : revAdd x/10^(M-1) = (endSum x+c)/10 := by
        rw [hh,pow_succ,←Nat.div_div_eq_div_mul,high]
      rw [htop] at pos
      have hsx := end_sum_lt x hx
      have hn : (endSum x+c)/10=1 := by omega
      rw [hn] at tab htop
      simp only [Nat.one_ne_zero, if_false, Nat.mul_one] at tab
      have hs : endSum (revAdd x) = 1+endSum x%10 := by
        change revAdd x/10^(M-1)+revAdd x%10 = _
        rw [htop,hlow]
      rw [hs,hM]
      omega

  -- Telescope the potential inequality along the orbit to bound the total number of length increases.
  have revAdd_length_iterate (x T : ℕ) (hx : 0<x) :
      (Nat.digits 10 (revAdd^[T] x)).length ≤ (Nat.digits 10 x).length+(T+3)/2 := by
    have accum (t : ℕ) :
        2*(Nat.digits 10 (revAdd^[t] x)).length + endPotential (endSum (revAdd^[t] x)) ≤
        2*(Nat.digits 10 x).length + endPotential (endSum x)+t := by
      induction t with
      | zero => simp
      | succ t ih =>
        have hpos (i : ℕ) : 0<revAdd^[i] x := by
          induction i with
          | zero => exact hx
          | succ i ih => rw [Function.iterate_succ_apply']; exact ih.trans_le (Nat.le_add_right _ _)
        have step := end_growth_step (revAdd^[t] x) (hpos t)
        rw [Function.iterate_succ_apply']
        omega
    have bound : ∀ s : Fin 19, endPotential s ≤ 3 := by decide +kernel
    have hp := bound ⟨endSum x,end_sum_lt x hx⟩
    dsimp only at hp
    have := accum T
    omega

  have finite_signature_collision {A : Type} [Fintype A] (N L : ℕ)
      (signature : ℕ → A) (hcard : Fintype.card A ≤ N) (hL : 2*(N+1) ≤ L) :
      ∃ l u : ℕ, 0 < l ∧ l < u ∧ 2*u ≤ L ∧ signature l = signature u := by
    let f (i : Fin (N+1)) := signature (i.val+1)
    obtain ⟨x,y,hxy,eq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simpa using Nat.lt_succ_of_le hcard)
    have xy : x.val ≠ y.val := fun e => hxy (Fin.ext e)
    rcases lt_or_gt_of_ne xy with h | h
    · exact ⟨x.val+1,y.val+1,by omega,by omega,by have := y.isLt; omega,eq⟩
    · exact ⟨y.val+1,x.val+1,by omega,by omega,by have := x.isLt; omega,eq.symm⟩

  have count_growth (w : ℕ → ℕ) (lo : ∀ j, w j ≤ w (j+1))
      (hi : ∀ j, w (j+1) ≤ w j+1) (T : ℕ) :
      ((Finset.range T).filter (fun j => w (j+1) ≠ w j)).card + w 0 = w T := by
    induction T with
    | zero => simp
    | succ k ih =>
      rw [Finset.range_add_one,Finset.filter_insert]
      split
      · rw [Finset.card_insert_of_notMem (by simp)]
        have := lo k
        have := hi k
        omega
      · omega

  have pack_digit_inj (a b e : ℕ) (ha : a ≠ e) (hb : b ≠ e)
      (h : (if a < e then a else a-1) = (if b < e then b else b-1)) : a=b := by
    split at h <;> split at h <;> omega

  have digit_at_mem (x k : ℕ) (hk : k<(Nat.digits 10 x).length) :
      x/10^k%10 ∈ Nat.digits 10 x := by
    rw [Nat.self_div_pow_eq_ofDigits_drop _ _ (by decide : 2≤10)]
    cases h : (Nat.digits 10 x).drop k with
    | nil =>
      have hlen := congrArg List.length h
      simp at hlen
      omega
    | cons z zs =>
      have hmem : z ∈ Nat.digits 10 x := List.mem_of_mem_drop (i:=k) (by rw [h]; simp)
      rw [Nat.ofDigits_cons,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (Nat.digits_lt_base (by decide) hmem)]
      exact hmem

  -- At each cut encode two carry bits per step, plus one of nine possible digits per length increase.
  have compress_survivor_digits (T n : ℕ) (hn : 0 < n)
      (survive : ∀ k≤T, ¬IsPandigital (revAdd^[k] n)) :
      ∃ m : ℕ, 0 < m ∧ (Nat.digits 10 m).length ≤ 2*(4^T*9^(min T ((T+3)/2)))+1 ∧
        ∀ k ≤ T, ∀ d ∈ Nat.digits 10 (revAdd^[k] m), d ∈ Nat.digits 10 (revAdd^[k] n) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases small : (Nat.digits 10 n).length ≤ 2*(4^T*9^(min T ((T+3)/2)))+1
      · exact ⟨n,hn,small,fun _ _ _ hd => hd⟩
      let X (k : ℕ) := revAdd^[k] n
      let w (j : ℕ) := (Nat.digits 10 (X j)).length
      let G := (Finset.range T).filter (fun j => w (j+1) ≠ w j)
      have lo (j : ℕ) : w j ≤ w (j+1) :=
        Nat.le_length_digits_le 10 _ _ (iterate_mono n j (j+1) (by omega))
      have hi (j : ℕ) : w (j+1) ≤ w j+1 := by
        simpa only [w,X,Function.iterate_succ_apply'] using revAdd_length_le (X j)
      have count : G.card + w 0 = w T := count_growth w lo hi T
      have large : w T ≤ w 0+(T+3)/2 := revAdd_length_iterate n T hn
      have cg : G.card ≤ min T ((T+3)/2) := by
        refine le_min ?_ (by omega)
        exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range T)
      have misses (j : G) : ∃ e : Fin 10, e.val ∉ Nat.digits 10 (revAdd (X j.val)) := by
        obtain ⟨hj,_⟩ := Finset.mem_filter.mp j.property
        have hjT : j.val < T := Finset.mem_range.mp hj
        have h := survive (j.val+1) (by omega)
        rw [Function.iterate_succ_apply'] at h
        by_contra! h'
        apply h
        exact fun e he => h' ⟨e, he⟩
      let missing (j : G) := Classical.choose (misses j)
      let digit (j : G) (i : ℕ) := revAdd (X j.val)/10^(w j.val-i)%10
      have digit_ok (j : G) (i : ℕ) : digit j i ≠ (missing j).val := by
        intro eq
        apply Classical.choose_spec (misses j)
        change (missing j).val ∈ _
        rw [←eq]
        apply digit_at_mem
        obtain ⟨_,diff⟩ := Finset.mem_filter.mp j.property
        have h := lo j.val
        have row : (Nat.digits 10 (revAdd (X j.val))).length = w (j.val+1) := by
          simp only [w, X, Function.iterate_succ_apply']
        rw [row]
        omega
      let pack (j : G) (i : ℕ) : Fin 9 :=
        ⟨if digit j i < (missing j).val then digit j i else digit j i-1, by
          have h := digit_ok j i
          have h' := (missing j).isLt
          have hd : digit j i < 10 := Nat.mod_lt _ (by decide)
          split <;> omega⟩
      have unpack {j : G} {l u : ℕ} (h : pack j l = pack j u) : digit j l = digit j u := by
        exact pack_digit_inj _ _ _ (digit_ok j l) (digit_ok j u) (congrArg Fin.val h)
      let sig (i : ℕ) : (Fin T → Fin 2 × Fin 2) × (G → Fin 9) :=
        (fun j => (⟨carry (X j.val) i,digit_carry_lt_two _ _ _⟩,
          ⟨carry (X j.val) (w j.val-i),digit_carry_lt_two _ _ _⟩),
         fun j => pack j i)
      have cards : Fintype.card ((Fin T → Fin 2 × Fin 2) × (G → Fin 9)) ≤ 4^T*9^(min T ((T+3)/2)) := by
        simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe]
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) cg)
      obtain ⟨l,u,hl,hlu,room,heq⟩ := finite_signature_collision _ (Nat.digits 10 n).length sig cards (by omega)
      have rooms (j : ℕ) : 2*u ≤ (Nat.digits 10 (X j)).length := by
        exact room.trans (Nat.le_length_digits_le 10 _ _ (iterate_mono n 0 j (by omega)))
      have hs (j : ℕ) := shrink_spec (X j) l u hl hlu.le (rooms j)
      have shifted (k : ℕ) (hk : k≤T) : revAdd^[k] (shrink n l u) = shrink (X k) l u := by
        induction k with
        | zero => rfl
        | succ k ihk =>
          have cj := congrFun (congrArg Prod.fst heq) (⟨k,by omega⟩ : Fin T)
          have e1 := congrArg (fun a : Fin 2 × Fin 2 => a.1.val) cj
          have e2 := congrArg (fun a : Fin 2 × Fin 2 => a.2.val) cj
          have edge (diff : (Nat.digits 10 (revAdd (X k))).length ≠ w k) :
              (revAdd (X k))/10^(w k-l)%10 = (revAdd (X k))/10^(w k-u)%10 := by
            have kg : k∈G := by
              apply Finset.mem_filter.mpr
              exact ⟨Finset.mem_range.mpr (by omega),by simpa only [w,X,Function.iterate_succ_apply'] using diff⟩
            exact unpack (congrFun (congrArg Prod.snd heq) (⟨k,kg⟩ : G))
          rw [Function.iterate_succ_apply',ihk (by omega)]
          exact (revAdd_shrink (X k) l u hl hlu.le (rooms k) e1 e2 edge).trans
            (congrArg (fun z => shrink z l u) (Function.iterate_succ_apply' revAdd k n).symm)
      have first := hs 0
      change 0 < shrink n l u ∧ (Nat.digits 10 (shrink n l u)).length + 2*(u-l) = (Nat.digits 10 n).length ∧ _ at first
      have smaller : shrink n l u < n := by
        by_contra! h
        have := Nat.le_length_digits_le 10 _ _ h
        have := first.2.1
        omega
      have surviv (k : ℕ) (hk : k≤T) : ¬IsPandigital (revAdd^[k] (shrink n l u)) := by
        intro hp
        apply survive k hk
        intro e he
        have hd := hp e he
        rw [shifted k hk] at hd
        exact (hs k).2.2 e hd
      obtain ⟨m,hm,mwidth,hsub⟩ := ih _ smaller first.1 surviv
      refine ⟨m,hm,mwidth,?_⟩
      intro k hk d hd
      have z := hsub k hk d hd
      rw [shifted k hk] at z
      exact (hs k).2.2 d z

  exact ⟨revAdd_length_iterate,compress_survivor_digits⟩

end Reverse249

namespace Reverse249
open OMA.S_oeis_a249280

theorem survivor_width (T n : ℕ) (hn : 0 < n) (survive : ∀ k≤T, ¬IsPandigital (revAdd^[k] n)) :
    ∃ m : ℕ, 0 < m ∧ (Nat.digits 10 m).length ≤ 54*12^T+1 ∧
      ∀ k≤T, ¬IsPandigital (revAdd^[k] m) := by
  obtain ⟨m,hm,hw,hd⟩ := decimal_compression_results.2 T n hn survive
  have p : 9^(min T ((T+3)/2)) ≤ 3^(T+3) := by
    rw [show 9 = (3:ℕ)^2 by decide, ←pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    omega
  have b : 2*(4^T*9^(min T ((T+3)/2))) ≤ 54*12^T := by
    calc
      _ ≤ 2*(4^T*3^(T+3)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ p)
      _ = 54*12^T := by rw [pow_add,show 12=(4:ℕ)*3 by decide,mul_pow]; ring
  refine ⟨m,hm,by omega,?_⟩
  intro k hk hp
  exact survive k hk (fun d hd' => hd k hk d (hp d hd'))

/-- A finite test for a digit condition implied by pandigitality. The initial condition
passes to subsets of the initial digits, and the target passes to supersets. -/
theorem finite_survivor_test (T : ℕ) (initial hit : ℕ → Prop)
    (start_sub : ∀ x y : ℕ, (∀ e∈Nat.digits 10 y, e∈Nat.digits 10 x) → initial x → initial y)
    (hit_sup : ∀ x y : ℕ, (∀ e∈Nat.digits 10 x, e∈Nat.digits 10 y) → hit x → hit y)
    (full : ∀ x : ℕ, IsPandigital x → hit x) :
    (∀ n : ℕ, 0 < n → initial n → ∃ k ≤ T, hit (revAdd^[k] n)) ↔
    (∀ n : Fin (10^(2*(4^T*9^(min T ((T+3)/2)))+1)), 0 < n.val → initial n.val →
      ∃ k : Fin (T+1), hit (revAdd^[k.val] n.val)) := by
  constructor
  · intro h n hn hi
    obtain ⟨k,hk,yes⟩ := h n.val hn hi
    exact ⟨⟨k,by omega⟩,yes⟩
  · intro h n hn hi
    by_contra! no
    have survives (k : ℕ) (hk : k≤T) : ¬IsPandigital (revAdd^[k] n) :=
      fun hp => no k hk (full _ hp)
    obtain ⟨m,hm,hw,hs⟩ := decimal_compression_results.2 T n hn survives
    have m_lt : m < 10^(2*(4^T*9^(min T ((T+3)/2)))+1) :=
      (Nat.digits_length_le_iff (by decide : 1<10) m).mp hw
    have mi : initial m := start_sub n m (hs 0 (by omega)) hi
    obtain ⟨k,hk⟩ := h ⟨m,m_lt⟩ hm mi
    have kt : k.val ≤ T := by have := k.isLt; omega
    exact no k.val kt (hit_sup _ _ (hs k.val kt) hk)


end Reverse249

namespace Reverse249
open OMA.S_oeis_a249280

theorem finite_decimal_test (T : ℕ) :
    (∀ n : ℕ, 0 < n → ∃ k ≤ T, IsPandigital (revAdd^[k] n)) ↔
    (∀ n : Fin (10^(2*(4^T*9^(min T ((T+3)/2)))+1)), 0 < n.val →
      ∃ k : Fin (T+1), ∀ d : Fin 10, d.val ∈ Nat.digits 10 (revAdd^[k.val] n.val)) := by
  have h := finite_survivor_test T (fun _ => True) IsPandigital
    (fun _ _ _ _ => trivial) (fun _ _ incl pan d hd => incl d (pan d hd)) (fun _ h => h)
  constructor
  · intro hit n hn
    obtain ⟨k,hk,yes⟩ := hit n.val hn
    exact ⟨⟨k,by omega⟩,fun d => yes d.val d.isLt⟩
  · intro test n hn
    apply h.mpr _ n hn trivial
    intro m hm _
    obtain ⟨k,hk⟩ := test m hm
    exact ⟨k,fun d hd => hk ⟨d,hd⟩⟩

/-- A computable search over horizons is a semidecision procedure for the full conjecture. -/
theorem bounded_search_equivalence :
    let test := fun T : ℕ => decide (∀ n : Fin (10^(2*(4^T*9^(min T ((T+3)/2)))+1)), 0 < n.val →
      ∃ k : Fin (T+1), ∀ d : Fin 10, d.val ∈ Nat.digits 10 (revAdd^[k.val] n.val))
    (type_of% @OMA.S_oeis_a249280.main) ↔ ∃ T : ℕ, test T = true := by
  dsimp only
  constructor
  · rintro ⟨_,c,allHit⟩
    refine ⟨c,decide_eq_true ((finite_decimal_test c).mp ?_)⟩
    intro n hn
    obtain ⟨k,hk,y⟩ := allHit n hn
    exact ⟨k,hk.le,y⟩
  · rintro ⟨T,pass⟩
    have allHit := (finite_decimal_test T).mpr (of_decide_eq_true pass)
    refine ⟨?_,T+1,?_⟩
    · intro n hn
      obtain ⟨k,_,yes⟩ := allHit n hn
      exact ⟨k,yes⟩
    · intro n hn
      obtain ⟨k,hk,yes⟩ := allHit n hn
      exact ⟨k,by omega,yes⟩

end Reverse249

namespace Reverse249
open OMA.S_oeis_a249280

/-- The two finite tests separately ask for the nine nonzero digits and
for all ten digits when the initial decimal expansion has no zero. -/
theorem finite_tests_suffice (W : ℕ → ℕ)
    (compression : ∀ T n : ℕ, 0 < n → (∀ k ≤ T, ¬ IsPandigital (revAdd^[k] n)) → ∃ m : ℕ, 0 < m ∧ (Nat.digits 10 m).length ≤ W T ∧
      ∀ k ≤ T, ∀ d ∈ Nat.digits 10 (revAdd^[k] m), d ∈ Nat.digits 10 (revAdd^[k] n))
    (nonzero : ∃ T : ℕ, ∀ n : Fin (10^(W T)), 0 < n.val →
      ∃ k : Fin (T+1), ∀ d : Fin 9, d.val+1 ∈ Nat.digits 10 (revAdd^[k.val] n.val))
    (zeroFree : ∃ T : ℕ, ∀ n : Fin (10^(W T)), 0 < n.val → 0 ∉ Nat.digits 10 n.val →
      ∃ k : Fin (T+1), ∀ d : Fin 10, d.val ∈ Nat.digits 10 (revAdd^[k.val] n.val)) :
    type_of% @OMA.S_oeis_a249280.main := by
  obtain ⟨B,hB⟩ := nonzero
  obtain ⟨C,hC⟩ := zeroFree
  have full (n : ℕ) (hn : 0 < n) : ∃ k < B+C+1, IsPandigital (revAdd^[k] n) := by
    by_contra noHit
    have miss (k : ℕ) (hk : k < B+C+1) : ¬ IsPandigital (revAdd^[k] n) := fun hit => noHit ⟨k,hk,hit⟩
    obtain ⟨m,hm,hw,hs⟩ := compression B n hn (fun k hk => miss k (by omega))
    have mw := (Nat.digits_length_le_iff (by decide : 1<10) m).mp hw
    obtain ⟨j,hj⟩ := hB ⟨m,mw⟩ hm
    have jb : j.val ≤ B := by have := j.isLt; omega
    let x := revAdd^[j.val] n
    have allNZ (d : ℕ) (hd : 0 < d) (hlt : d < 10) : d ∈ Nat.digits 10 x := by
      obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
      exact hs j.val jb _ (hj ⟨i,by omega⟩)
    by_cases hasZero : 0 ∈ Nat.digits 10 x
    · apply miss j.val (by omega)
      intro d hd
      rcases Nat.eq_zero_or_pos d with rfl | h
      · exact hasZero
      · exact allNZ d h hd
    · have xp : 0 < x := hn.trans_le (iterate_mono n 0 j.val (by omega))
      have noNext (k : ℕ) (hk : k≤C) : ¬ IsPandigital (revAdd^[k] x) := by
        intro z
        apply miss (k+j.val) (by omega)
        simpa only [Function.iterate_add_apply] using z
      obtain ⟨q,hq,qw,qs⟩ := compression C x xp noNext
      have qBound := (Nat.digits_length_le_iff (by decide : 1<10) q).mp qw
      have qz : 0 ∉ Nat.digits 10 q := fun hz => hasZero (qs 0 (by omega) 0 hz)
      obtain ⟨i,hi⟩ := hC ⟨q,qBound⟩ hq qz
      have ic : i.val ≤ C := by have := i.isLt; omega
      apply miss (i.val+j.val) (by omega)
      rw [Function.iterate_add_apply]
      intro d hd
      exact qs i.val ic d (hi ⟨d,hd⟩)
  exact ⟨fun n hn => let ⟨k,_,hk⟩ := full n hn; ⟨k,hk⟩,B+C+1,full⟩

end Reverse249

namespace Reverse249

open OMA.S_oeis_a249280

private theorem complement_eval (L : List ℕ) (h : ∀ d ∈ L, d < 10) :
    Nat.ofDigits 10 (L.map (9 - ·)) + Nat.ofDigits 10 L + 1 = 10 ^ L.length := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have ha : a < 10 := h a (by simp)
    have ht := ih (fun d hd => h d (by simp [hd]))
    simp only [List.map_cons, Nat.ofDigits_cons, List.length_cons, pow_succ]
    omega

private theorem complement_nines (k : ℕ) :
    Nat.ofDigits 10 (List.replicate k 9) + 1 = 10^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, Nat.ofDigits_cons, pow_succ]
    omega

theorem digits_complement_embed (d k : ℕ) (hd : 0 < d) :
    let L := Nat.digits 10 d
    Nat.digits 10 ((10^(L.length+k)-1)*(d+1)) =
      (L.map (9 - ·) ++ List.replicate k 9) ++ L := by
  let L := Nat.digits 10 d
  change Nat.digits 10 ((10^(L.length+k)-1)*(d+1)) = _
  have hL (v) (hv : v ∈ L) : v < 10 := Nat.digits_lt_base (by decide) hv
  have hz : L ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hd.ne'
  have eval : Nat.ofDigits 10 L = d := Nat.ofDigits_digits 10 d
  have comp := complement_eval L hL
  have nines := complement_nines k
  have length : (L.map (9 - ·) ++ List.replicate k 9).length = L.length+k := by simp
  have v : Nat.ofDigits 10 ((L.map (9 - ·) ++ List.replicate k 9) ++ L) =
      ((10:ℕ)^(L.length+k)-1)*(d+1) := by
    rw [Nat.ofDigits_append,length,Nat.ofDigits_append,List.length_map,eval,pow_add]
    rw [eval] at comp
    have hpow : (1:ℕ) ≤ 10^L.length*10^k := by exact Nat.succ_le_of_lt (by positivity)
    zify [hpow] at comp nines ⊢
    nlinarith only [comp,nines,congrArg (fun a : ℤ => (10:ℤ)^L.length*a) nines]
  rw [← v]
  apply Nat.digits_ofDigits _ (by decide)
  · intro x hx
    simp only [List.mem_append, List.mem_map, List.mem_replicate] at hx
    rcases hx with ((⟨z,hz, rfl⟩ | ⟨_,rfl⟩) | hx)
    · omega
    · decide
    · exact hL _ hx
  · intro hn
    rw [List.getLast_append_of_ne_nil hn hz]
    exact Nat.getLast_digit_ne_zero _ hd.ne'

theorem complement_orbits :
    let deficitStep (d : ℕ) : ℕ := 10^(Nat.digits 10 d).length + d - Nat.ofDigits 10 (Nat.digits 10 d).reverse
    (∀ d M t k : ℕ, 0 < d → k ≤ t → (Nat.digits 10 (deficitStep^[t] d)).length ≤ M →
      (IsPandigital (revAdd^[k] ((10^M-1)*(d+1))) ↔ ∀ z < 5, z ∈ Nat.digits 10 (deficitStep^[k] d) ∨
        9-z ∈ Nat.digits 10 (deficitStep^[k] d))) ∧
    ((∀ t : ℕ, ∃ d, 0 < d ∧ ∀ k < t, ∃ z < 5, z ∉ Nat.digits 10 (deficitStep^[k] d) ∧ 9-z ∉ Nat.digits 10 (deficitStep^[k] d)) →
      ¬ ∃ c : ℕ, ∀ n > 0, ∃ k < c, IsPandigital (revAdd^[k] n)) := by
  let deficitStep (d : ℕ) : ℕ := 10^(Nat.digits 10 d).length + d - Nat.ofDigits 10 (Nat.digits 10 d).reverse
  have revAdd_complement_embed (d k : ℕ) (hd : 0 < d) :
      let L := Nat.digits 10 d
      revAdd ((10^(L.length+k)-1)*(d+1)) =
        (10^(L.length+k)-1)*(deficitStep d+1) := by
    let L := Nat.digits 10 d
    change revAdd ((10^(L.length+k)-1)*(d+1)) = _
    have hL (v) (h : v ∈ L.reverse) : v < 10 :=
      Nat.digits_lt_base (by decide) (List.mem_reverse.mp h)
    have comp := complement_eval L.reverse hL
    have hr : Nat.ofDigits 10 L.reverse < 10^L.length := by
      simpa using Nat.ofDigits_lt_base_pow_length (by decide : 1 < 10) hL
    have nines := complement_nines k
    simp only [List.length_reverse] at comp
    unfold revAdd
    rw [digits_complement_embed d k hd]
    change _ + Nat.ofDigits 10 (((L.map (9 - ·) ++ List.replicate k 9) ++ L).reverse) = _
    simp only [List.reverse_append,List.reverse_replicate,← List.map_reverse,Nat.ofDigits_append,
      List.length_reverse,List.length_replicate]
    unfold deficitStep
    change _ = (10^(L.length+k)-1) * (10^L.length + d - Nat.ofDigits 10 L.reverse + 1)
    have hpow : 1 ≤ (10:ℕ)^L.length * 10^k := by exact Nat.succ_le_of_lt (by positivity)
    have hsub : Nat.ofDigits 10 L.reverse ≤ 10^L.length+d := by omega
    rw [pow_add]
    zify [hpow,hsub] at comp nines ⊢
    linear_combination ((10:ℤ)^L.length * 10^k) * comp + (10:ℤ)^L.length * nines

  have deficitStep_increases (d : ℕ) : d < deficitStep d := by
    let L := Nat.digits 10 d
    have hL (v) (hv : v ∈ L.reverse) : v < 10 :=
      Nat.digits_lt_base (by decide) (List.mem_reverse.mp hv)
    have hr : Nat.ofDigits 10 L.reverse < 10 ^ L.length := by
      simpa using Nat.ofDigits_lt_base_pow_length (by decide : 1 < 10) hL
    change d < 10 ^ L.length + d - Nat.ofDigits 10 L.reverse
    omega

  have deficit_iterate_mono (d i j : ℕ) (h : i ≤ j) :
      deficitStep^[i] d ≤ deficitStep^[j] d := by
    apply monotone_nat_of_le_succ (f := fun k => deficitStep^[k] d) _ h
    intro k
    rw [Function.iterate_succ_apply']
    exact (deficitStep_increases _).le

  have iterate_complement_embed (d M t k : ℕ) (hd : 0 < d) (hk : k ≤ t)
      (hM : (Nat.digits 10 (deficitStep^[t] d)).length ≤ M) :
      revAdd^[k] ((10 ^ M - 1) * (d + 1)) =
        (10 ^ M - 1) * (deficitStep^[k] d + 1) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have hle := (Nat.le_length_digits_le 10 _ _ (deficit_iterate_mono d k t (by omega))).trans hM
      have hpos := hd.trans_le (deficit_iterate_mono d 0 k (by omega))
      have hs := revAdd_complement_embed (deficitStep^[k] d)
        (M - (Nat.digits 10 (deficitStep^[k] d)).length) hpos
      rw [Function.iterate_succ_apply', ih (by omega), Function.iterate_succ_apply']
      simpa only [Nat.add_sub_of_le hle] using hs

  have pandigital_complement_iff (d M : ℕ) (hd : 0 < d)
      (hM : (Nat.digits 10 d).length ≤ M) :
      IsPandigital ((10 ^ M - 1) * (d + 1)) ↔
        ∀ z < 5, z ∈ Nat.digits 10 d ∨ 9 - z ∈ Nat.digits 10 d := by
    let L := Nat.digits 10 d
    have he := digits_complement_embed d (M - L.length) hd
    change Nat.digits 10 ((10 ^ (L.length + (M-L.length)) - 1) * (d + 1)) = _ at he
    rw [Nat.add_sub_of_le hM] at he
    unfold IsPandigital
    rw [he]
    simp only [List.mem_append, List.mem_map, List.mem_replicate]
    change (∀ z < 10, (((∃ a ∈ L, 9-a=z) ∨ _) ∨ z ∈ L)) ↔ ∀ z < 5, z ∈ L ∨ 9-z ∈ L
    constructor
    · intro h z hz
      rcases h z (by omega) with ((⟨a,ha,heq⟩ | ⟨_,heq⟩) | hmem)
      · have ha10 : a < 10 := Nat.digits_lt_base (by decide) ha
        exact Or.inr (by rwa [show 9-z = a by omega])
      · omega
      · exact Or.inl hmem
    · intro h z hz
      by_cases hsmall : z < 5
      · rcases h z hsmall with hm | hm
        · exact Or.inr hm
        · exact Or.inl (Or.inl ⟨9-z,hm,by omega⟩)
      · rcases h (9-z) (by omega) with hm | hm
        · exact Or.inl (Or.inl ⟨9-z,hm,by omega⟩)
        · exact Or.inr (by simpa only [show 9-(9-z) = z by omega] using hm)

  have iterate_pandigital_complement_iff (d M t k : ℕ) (hd : 0 < d) (hk : k ≤ t)
      (hM : (Nat.digits 10 (deficitStep^[t] d)).length ≤ M) :
      IsPandigital (revAdd^[k] ((10 ^ M - 1) * (d + 1))) ↔
        ∀ z < 5, z ∈ Nat.digits 10 (deficitStep^[k] d) ∨
          9-z ∈ Nat.digits 10 (deficitStep^[k] d) := by
    rw [iterate_complement_embed d M t k hd hk hM]
    exact pandigital_complement_iff _ _ (hd.trans_le (deficit_iterate_mono d 0 k (by omega)))
      ((Nat.le_length_digits_le 10 _ _ (deficit_iterate_mono d k t hk)).trans hM)

  have no_uniform_bound_of_deficit_delays
      (h : ∀ t : ℕ, ∃ d, 0 < d ∧ ∀ k < t, ∃ z < 5,
        z ∉ Nat.digits 10 (deficitStep^[k] d) ∧ 9-z ∉ Nat.digits 10 (deficitStep^[k] d)) :
      ¬ ∃ c : ℕ, ∀ n > 0, ∃ k < c, IsPandigital (revAdd^[k] n) := by
    rintro ⟨c,hc⟩
    obtain ⟨d,hd,hdelay⟩ := h c
    let m := (Nat.digits 10 (deficitStep^[c] d)).length
    have hpow : 0 < (10 : ℕ)^m := by positivity
    have hpositive : 0 < ((10:ℕ)^(m+1)-1)*(d+1) := by
      apply Nat.mul_pos _ (by omega)
      rw [pow_succ]
      omega
    obtain ⟨k,hk,hpan⟩ := hc _ hpositive
    obtain ⟨z,hz,h1,h2⟩ := hdelay k hk
    have hp := (iterate_pandigital_complement_iff d (m+1) c k hd hk.le (Nat.le_succ m)).mp hpan z hz
    exact hp.elim h1 h2

  exact ⟨iterate_pandigital_complement_iff,no_uniform_bound_of_deficit_delays⟩

end Reverse249

namespace Reverse249

open OMA.S_oeis_a249280

/-- Verify a complete first-hit certificate for any prescribed collection of decimal digits. -/
private theorem verify_delay (wanted : List ℕ) (d k n : ℕ) :
    let places : ℕ → ℕ → List ℕ := Nat.rec (fun _ => [])
      (fun _ prior z => if z=0 then [] else z%10 :: prior (z/10))
    let allPresent (ds : List ℕ) := wanted.all fun digit => ds.contains digit
    let hit : ℕ → ℕ → Bool := Nat.rec (fun z => decide (z<10^d) && allPresent (places d z))
      (fun _ prior z => decide (z<10^d) && !(allPresent (places d z)) &&
        prior (z + Nat.ofDigits 10 (places d z).reverse))
    hit k n = true →
      (∀ j : ℕ, j < k → ¬ ∀ t ∈ wanted, t ∈ Nat.digits 10 (revAdd^[j] n)) ∧
      (∀ t ∈ wanted, t ∈ Nat.digits 10 (revAdd^[k] n)) := by
  intro places allPresent hit checked
  have correct (b z : ℕ) (h : z < 10^b) : places b z = Nat.digits 10 z := by
    induction b generalizing z with
    | zero =>
      have : z = 0 := by simpa using h
      simp [places,this]
    | succ b ih =>
      by_cases hz : z=0
      · simp [places,hz]
      · change (if z = 0 then [] else z%10 :: places b (z/10)) = _
        rw [if_neg hz, Nat.digits_eq_cons_digits_div (by decide) hz, ih]
        exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 10)).mpr (by simpa only [pow_succ] using h)
  have all_iff (ds : List ℕ) : allPresent ds = true ↔ ∀ t ∈ wanted, t ∈ ds := by
    simp [allPresent]
  induction k generalizing n with
  | zero =>
    change (decide (n<10^d) && allPresent (places d n)) = true at checked
    simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
    exact ⟨by omega, (all_iff _).mp (correct d n checked.1 ▸ checked.2)⟩
  | succ k ih =>
    change (decide (n<10^d) && !(allPresent (places d n)) &&
      hit k (n + Nat.ofDigits 10 (places d n).reverse)) = true at checked
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at checked
    rw [correct d n checked.1.1] at checked
    have hn := ih (revAdd n) checked.2
    refine ⟨?_, by simpa only [Function.iterate_succ_apply] using hn.2⟩
    intro j hj
    cases j with
    | zero =>
      intro h
      have ht := (all_iff _).mpr h
      simp [checked.1.2] at ht
    | succ j =>
      simpa only [Function.iterate_succ_apply] using hn.1 j (by omega)

theorem first_hit_75 :
    (∀ k : ℕ, k < 75 → ¬ IsPandigital (revAdd^[k] 10205893945)) ∧
      IsPandigital (revAdd^[75] 10205893945) := by
  simpa only [IsPandigital, List.mem_range] using
    verify_delay (List.range 10) 64 75 10205893945 (by decide +kernel)

theorem first_nonzero_hit_73 :
    (∀ k : ℕ, k < 73 → ¬ ∀ d : ℕ, 0 < d → d < 10 →
      d ∈ Nat.digits 10 (revAdd^[k] 4998140)) ∧
    (∀ d : ℕ, 0 < d → d < 10 → d ∈ Nat.digits 10 (revAdd^[73] 4998140)) := by
  have h := verify_delay ((List.range 10).filter (fun t => 0 < t)) 64 73 4998140 (by decide +kernel)
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, and_imp] at h
  constructor
  · intro k hk hd
    exact h.1 k hk (fun t ht hp => hd t hp ht)
  · intro t hp ht
    exact h.2 t ht hp

end Reverse249

namespace Reverse249

open OMA.S_oeis_a249280

/-- All decimal blocks have equal size, with a positive number of zeroes between
consecutive blocks. Reversal respects the block multiplier even when the original
number ends in zeroes. -/
theorem replica_structure (s n r : ℕ) (hn : 0 < n) (hs : (Nat.digits 10 n).length < s) :
    let C := ∑ i ∈ Finset.range (r+1), 10^(s*i)
    (Nat.digits 10 (C*n)).length = s*r+(Nat.digits 10 n).length ∧
    Nat.ofDigits 10 (Nat.digits 10 (C*n)).reverse =
      C * Nat.ofDigits 10 (Nat.digits 10 n).reverse ∧
    (∀ z : ℕ, z ∈ Nat.digits 10 (C*n) ↔ z ∈ Nat.digits 10 n ∨ z=0 ∧ 0<r) := by
  let C (j : ℕ) := ∑ i ∈ Finset.range (j+1), 10^(s*i)
  change (Nat.digits 10 (C r*n)).length = _ ∧ _ = C r * _ ∧
    (∀ z : ℕ, z ∈ Nat.digits 10 (C r*n) ↔ _)
  have hright (j : ℕ) : C (j+1) = C j + 10^(s*(j+1)) := by
    exact Finset.sum_range_succ _ _
  have hleft (j : ℕ) : C (j+1) = 1 + 10^s * C j := by
    unfold C
    rw [Finset.sum_range_succ', Finset.mul_sum]
    simp only [Nat.mul_zero,pow_zero, Nat.mul_succ, pow_add]
    ring_nf
  have hp (j : ℕ) : 0 < C j := by
    cases j with
    | zero => simp [C]
    | succ j => rw [hleft]; omega
  induction r with
  | zero => simp [C]
  | succ r ih =>
    have he : C (r+1)*n = n + 10^s*(C r*n) := by rw [hleft]; ring
    have digits := (Nat.digits_append_zeroes_append_digits (b:=10) (n:=n)
      (k:=s-(Nat.digits 10 n).length) (by decide) (Nat.mul_pos (hp r) hn)).symm
    rw [Nat.add_sub_of_le hs.le, ← he] at digits
    obtain ⟨hsize,hrev,hmem⟩ := ih
    change Nat.ofDigits 10 (Nat.digits 10 (C r*n)).reverse = C r * _ at hrev
    have hgap : s*r+(Nat.digits 10 n).length+(s-(Nat.digits 10 n).length) = s*(r+1) := by
      rw [Nat.mul_succ]; omega
    rw [digits]
    refine ⟨?_,?_,?_⟩
    · simp only [List.length_append, List.length_replicate,hsize,Nat.mul_succ]
      omega
    · simp only [List.reverse_append,List.reverse_replicate,Nat.ofDigits_append,
        Nat.ofDigits_replicate_zero,List.length_replicate,List.length_reverse,hsize,hrev,zero_add]
      rw [← Nat.mul_assoc, ← pow_add, hgap, hright]
      ring
    · intro z
      simp [List.mem_replicate, hmem, show s-(Nat.digits 10 n).length ≠ 0 by omega]
      tauto

theorem replica_iterate (s n r t k : ℕ) (hn : 0 < n) (hk : k ≤ t)
    (hs : (Nat.digits 10 (revAdd^[t] n)).length < s) :
    let C := ∑ i ∈ Finset.range (r+1), 10^(s*i)
    revAdd^[k] (C*n) = C*(revAdd^[k] n) := by
  let C := ∑ i ∈ Finset.range (r+1), 10^(s*i)
  change revAdd^[k] (C*n) = C*(revAdd^[k] n)
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkt : k ≤ t := by omega
    have hp : 0 < revAdd^[k] n := hn.trans_le (iterate_mono n 0 k (by omega))
    have hw := (Nat.le_length_digits_le 10 _ _ (iterate_mono n k t hkt)).trans_lt hs
    have hr := (replica_structure s (revAdd^[k] n) r hp hw).2.1
    change Nat.ofDigits 10 (Nat.digits 10 (C*(revAdd^[k] n))).reverse = C * _ at hr
    rw [Function.iterate_succ_apply', ih hkt, Function.iterate_succ_apply']
    simp only [revAdd, hr, Nat.mul_add]

theorem replica_pandigital_iff (s n r t k : ℕ) (hn : 0 < n) (hr : 0 < r) (hk : k ≤ t)
    (hs : (Nat.digits 10 (revAdd^[t] n)).length < s) :
    let C := ∑ i ∈ Finset.range (r+1), 10^(s*i)
    IsPandigital (revAdd^[k] (C*n)) ↔
      ∀ d : ℕ, 0 < d → d < 10 → d ∈ Nat.digits 10 (revAdd^[k] n) := by
  dsimp only
  rw [replica_iterate s n r t k hn hk hs]
  have hp : 0 < revAdd^[k] n := hn.trans_le (iterate_mono n 0 k (by omega))
  have hw := (Nat.le_length_digits_le 10 _ _ (iterate_mono n k t hk)).trans_lt hs
  have hm := (replica_structure s (revAdd^[k] n) r hp hw).2.2
  constructor
  · intro h d hd hd'
    exact ((hm d).mp (h d hd')).resolve_right (by omega)
  · intro h d hd
    apply (hm d).mpr
    obtain rfl | hpos := Nat.eq_zero_or_pos d
    · exact Or.inr ⟨rfl,hr⟩
    · exact Or.inl (h d hpos hd)

theorem first_hit_73_multiple (q B : ℕ) (hq : 0 < q) (hc : q.Coprime 10) :
    ∃ m > B, q ∣ m ∧ (∀ k < 73, ¬ IsPandigital (revAdd^[k] m)) ∧
      IsPandigital (revAdd^[73] m) := by
  let n : ℕ := 4998140
  let L := (Nat.digits 10 (revAdd^[73] n)).length
  let s := q.totient * (B+L+1)
  let r := 2*q-1
  let C := ∑ i ∈ Finset.range (r+1), 10^(s*i)
  have hn : 0 < n := by decide
  have hr : 0 < r := by dsimp [r]; omega
  have hrq : r+1 = 2*q := by dsimp [r]; omega
  have hs0 : B+L+1 ≤ s := Nat.le_mul_of_pos_left _ (Nat.totient_pos.mpr hq)
  have hs : (Nat.digits 10 (revAdd^[73] n)).length < s := by change L < s; omega
  have hpow : 10^s ≡ 1 [MOD q] := by
    dsimp [s]
    rw [pow_mul]
    simpa using (Nat.ModEq.pow_totient hc.symm).pow (B+L+1)
  have hsum (j : ℕ) : (∑ i ∈ Finset.range j, 10^(s*i)) ≡ j [MOD q] := by
    induction j with
    | zero => simp only [Finset.range_zero, Finset.sum_empty]; rfl
    | succ j ih =>
      rw [Finset.sum_range_succ, pow_mul]
      simpa using ih.add (hpow.pow j)
  have hd : q ∣ C := Nat.modEq_zero_iff_dvd.mp
    ((hsum (r+1)).trans (hrq ▸ (dvd_mul_left q 2).modEq_zero_nat))
  have hlarge : 10^s ≤ C := by
    have h1 : 1 ∈ Finset.range (r+1) := Finset.mem_range.mpr (by omega)
    simpa [C] using Finset.single_le_sum (f:=fun i => 10^(s*i)) (fun i _ => Nat.zero_le _) h1
  have hs' : s < 10^s := (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_left (by decide) s)
  refine ⟨C*n, (show B < s by omega).trans_le (hs'.le.trans (hlarge.trans (Nat.le_mul_of_pos_right _ hn))),
    dvd_mul_of_dvd_left hd n, ?_, ?_⟩
  · intro k hk h
    exact first_nonzero_hit_73.1 k hk ((replica_pandigital_iff s n r 73 k hn hr hk.le hs).mp h)
  · exact (replica_pandigital_iff s n r 73 73 hn hr le_rfl hs).mpr first_nonzero_hit_73.2

end Reverse249

namespace Reverse249
open OMA.S_oeis_a249280

theorem strict_uniform_bound_ge_76 (c : ℕ)
    (h : ∀ n : ℕ, 0 < n → ∃ k < c, IsPandigital (revAdd^[k] n)) : 76 ≤ c := by
  obtain ⟨k,hk,hit⟩ := h 10205893945 (by decide)
  by_contra! hc
  exact first_hit_75.1 k (by omega) hit

end Reverse249

namespace OMA.R_oeis_a249280_R1
open OMA.S_oeis_a249280
open Reverse249

/-- Can some bounded search ensure the simultaneous appearance of digits 1 through 9? -/
def H1 : Prop := ∃ T : ℕ, ∀ n : Fin (10^(2*(4^T*9^(min T ((T+3)/2)))+1)), 0 < n.val →
  ∃ k : Fin (T+1), ∀ d : Fin 9, d.val+1 ∈ Nat.digits 10 (revAdd^[k.val] n.val)

/-- Can a bounded search certify all ten digits when the start has no zero? -/
def H2 : Prop := ∃ T : ℕ, ∀ n : Fin (10^(2*(4^T*9^(min T ((T+3)/2)))+1)), 0 < n.val →
  0 ∉ Nat.digits 10 n.val → ∃ k : Fin (T+1), ∀ d : Fin 10, d.val ∈ Nat.digits 10 (revAdd^[k.val] n.val)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a249280.main :=
  finite_tests_suffice _ decimal_compression_results.2

theorem both_tests_necessary (h : type_of% @OMA.S_oeis_a249280.main) : H1 ∧ H2 := by
  obtain ⟨c,bound⟩ := h.2
  constructor
  · refine ⟨c,?_⟩
    intro n hn
    obtain ⟨k,hk,hp⟩ := bound n.val hn
    exact ⟨⟨k,by omega⟩,fun d => hp (d.val+1) (by have := d.isLt; omega)⟩
  · refine ⟨c,?_⟩
    intro n hn _
    obtain ⟨k,hk,hp⟩ := bound n.val hn
    exact ⟨⟨k,by omega⟩,fun d => hp d.val d.isLt⟩

end OMA.R_oeis_a249280_R1
