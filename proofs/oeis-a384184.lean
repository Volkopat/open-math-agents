import OMAStatements.S_oeis_a384184
import Mathlib

/-!
# The order of the A384184 shuffle

Credit: @VestigeClub.
Conjecture: Mia Boudreau, https://oeis.org/A384184 .
The parity/deletion and odd doubling-orbit outline is acknowledged from
https://github.com/lefttosolve2/open-math-agents/pull/30895 .

We first compute the final position of each token in the ordered swap fold.
For even deck sizes, the shuffle changes parity and its square on the even
positions is the shuffle on a deck of half the size. For size 2^d+1, doubling
modulo the size changes to negation after d steps. Counting odd visits over
a full 2d steps proves the exponent d for the first-return map. Negation
transfers this to the other parity class, and the orbit of position 1 shows
that d is the exact order. Repeated doubling gives the claimed formula.
-/

namespace ShuffleProof
abbrev shuffle := OMA.S_oeis_a384184.shuffle

def step (N i x : ℕ) : ℕ := if x = i then (i+i)%N else if x = (i+i)%N then i else x

def run (N k len x : ℕ) : ℕ := (List.range' k len).foldl (fun x i => step N i x) x

lemma fold_apply {N : ℕ} (l : List (Fin N)) (p : Equiv.Perm (Fin N)) (x : Fin N) :
    (l.foldl (fun p i => p.trans (Equiv.swap i (i+i))) p) x =
      l.foldl (fun x i => Equiv.swap i (i+i) x) (p x) := by
  induction l generalizing p x with
  | nil => rfl
  | cons i l ih => simpa only [List.foldl_cons, Equiv.trans_apply] using ih (p.trans (Equiv.swap i (i+i))) x

lemma swap_val {N : ℕ} (i x : Fin N) :
    (Equiv.swap i (i+i) x).val = step N i.val x.val := by
  simp only [step, Equiv.swap_apply_def, Fin.ext_iff, Fin.val_add]
  split_ifs <;> rfl

lemma fold_val {N : ℕ} (l : List (Fin N)) (x : Fin N) :
    (l.foldl (fun x i => Equiv.swap i (i+i) x) x).val =
      (l.map Fin.val).foldl (fun x i => step N i x) x.val := by
  induction l generalizing x with
  | nil => rfl
  | cons i l ih => simpa only [List.foldl_cons, List.map_cons, swap_val] using ih (Equiv.swap i (i+i) x)


lemma finRange_vals (N : ℕ) : (List.finRange N).map Fin.val = List.range N := by
  ext i
  simp

lemma shuffle_val (N : ℕ) (x : Fin N) : (shuffle N x).val = run N 0 N x.val := by
  rw [shuffle, OMA.S_oeis_a384184.shuffle, fold_apply, fold_val, finRange_vals]
  simp [run, List.range_eq_range']

lemma run_zero (N k x : ℕ) : run N k 0 x = x := rfl
lemma run_succ (N k l x : ℕ) : run N k (l+1) x = run N (k+1) l (step N k x) := by
  simp [run, List.range'_succ]

lemma run_add (N k a b x : ℕ) :
    run N k (a+b) x = run N (k+a) b (run N k a x) := by
  simp only [run, ← List.range'_append, one_mul, List.foldl_append]

lemma run_fixed (N k l x : ℕ) (h : ∀ i, k ≤ i → i < k+l → step N i x = x) :
    run N k l x = x := by
  induction l generalizing k with
  | zero => rfl
  | succ l ih =>
    rw [run_succ, h k (by omega) (by omega)]
    exact ih (k+1) (fun i hi hj => h i (by omega) (by omega))

lemma step_fixed (N i x : ℕ) (h1 : x ≠ i) (h2 : x ≠ (i+i)%N) : step N i x = x := by
  simp [step, h1, h2]

lemma mod_double_cases (N i : ℕ) (hi : i < N) :
    (i+i)%N = if i+i < N then i+i else i+i-N := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

end ShuffleProof

namespace ShuffleProof

lemma run_skip (N k j x : ℕ) (hkj : k ≤ j) (hj : j ≤ N)
    (h : ∀ i, k ≤ i → i < j → step N i x = x) :
    run N k (N-k) x = run N j (N-j) x := by
  have he : N-k = (j-k)+(N-j) := by omega
  rw [he, run_add]
  have hk : k+(j-k)=j := by omega
  rw [hk, run_fixed N k (j-k) x (by intro i hi hij; exact h i hi (by omega))]

def up (N x : ℕ) : ℕ :=
  if h0 : x = 0 then 0 else if h : N ≤ x+x then x+x-N else up N (x+x)
termination_by N-x
decreasing_by omega

lemma run_up (N x : ℕ) (hx : 0 < x) (hN : x < N) :
    run N x (N-x) x = up N x := by
  rw [up]
  simp only [ne_eq, Nat.ne_of_gt hx, ↓reduceDIte]
  have hl : N-x = (N-(x+1))+1 := by omega
  rw [hl, run_succ]
  simp only [step, ↓reduceIte]
  by_cases h : N ≤ x+x
  · simp only [h, ↓reduceDIte]
    rw [mod_double_cases N x hN, if_neg (by omega)]
    apply run_fixed
    intro i hi hij
    apply step_fixed
    · omega
    · rw [mod_double_cases N i (by omega)]
      split_ifs <;> omega
  · simp only [h, ↓reduceDIte]
    rw [Nat.mod_eq_of_lt (by omega : x+x<N)]
    rw [run_skip N (x+1) (x+x) (x+x) (by omega) (by omega)]
    · exact run_up N (x+x) (by omega) (by omega)
    · intro i hi hij
      apply step_fixed
      · omega
      · rw [mod_double_cases N i (by omega)]
        split_ifs <;> omega
termination_by N-x
decreasing_by omega

lemma prefix_odd (N x : ℕ) (hx : x < N) (ho : x % 2 = 1) :
    run N 0 x x = x := by
  apply run_fixed
  intro i hi hij
  apply step_fixed
  · omega
  · rw [mod_double_cases N i (by omega)]
    split_ifs <;> omega

lemma odd_token (N x : ℕ) (hx : x < N) (ho : x % 2 = 1) :
    run N 0 N x = up N x := by
  change run N 0 (N-0) x = up N x
  rw [run_skip N 0 x x (by omega) (by omega)]
  · exact run_up N x (by omega) hx
  · intro i hi hij
    apply step_fixed
    · omega
    · rw [mod_double_cases N i (by omega)]
      split_ifs <;> omega

end ShuffleProof

namespace ShuffleProof

def strip (t : ℕ) : ℕ :=
  if t = 0 then 0 else if t % 2 = 0 then strip (t/2) else t
termination_by t
decreasing_by omega

lemma run_down (N t : ℕ) (ht : 0<t) (hN : t≤N) :
    run N (N-t+1) (N-(N-t+1)) (N-t) = N-strip t := by
  rw [strip]
  simp only [Nat.ne_of_gt ht, ↓reduceIte]
  by_cases he : t%2=0
  · simp only [he, ↓reduceIte]
    have ht2 : 0<t/2 := by omega
    have hmid : N-t+1 ≤ N-t/2 := by omega
    rw [run_skip N (N-t+1) (N-t/2) (N-t) hmid (by omega)]
    · have hlen : N-(N-t/2) = (N-(N-t/2+1))+1 := by omega
      rw [hlen, run_succ]
      have hs : step N (N-t/2) (N-t) = N-t/2 := by
        have hm : ((N-t/2)+(N-t/2))%N = N-t := by
          rw [mod_double_cases N (N-t/2) (by omega), if_neg (by omega)]
          omega
        simp [step, hm, show N-t ≠ N-t/2 by omega]
      rw [hs]
      exact run_down N (t/2) ht2 (by omega)
    · intro i hi hij
      apply step_fixed
      · omega
      · rw [mod_double_cases N i (by omega)]
        split_ifs <;> omega
  · simp only [he, ↓reduceIte]
    apply run_fixed
    intro i hi hij
    apply step_fixed
    · omega
    · rw [mod_double_cases N i (by omega)]
      split_ifs <;> omega
termination_by t
decreasing_by omega

lemma even_token (N j : ℕ) (hj : j+j<N) :
    run N 0 N (j+j) = N-strip (N-j) := by
  change run N 0 (N-0) (j+j) = _
  rw [run_skip N 0 j (j+j) (by omega) (by omega)]
  · have hlen : N-j = (N-(j+1))+1 := by omega
    conv_lhs => rw [hlen, run_succ]
    have hs : step N j (j+j) = j := by
      rw [step, Nat.mod_eq_of_lt hj]
      by_cases hz : j=0
      · subst j; simp
      · simp [show j+j≠j by omega]
    rw [hs]
    have hr := run_down N (N-j) (by omega) (by omega)
    have he : N-(N-j)=j := by omega
    simpa only [he] using hr
  · intro i hi hij
    apply step_fixed
    · omega
    · rw [Nat.mod_eq_of_lt (by omega : i+i<N)]
      omega

end ShuffleProof

namespace ShuffleProof

lemma strip_pos (t : ℕ) (ht : 0<t) : 0<strip t := by
  rw [strip]
  simp only [Nat.ne_of_gt ht, ↓reduceIte]
  split_ifs with h
  · exact strip_pos (t/2) (by omega)
  · exact ht
termination_by t
decreasing_by omega

lemma strip_le (t : ℕ) : strip t ≤ t := by
  rw [strip]
  split_ifs with hz he
  · omega
  · exact (strip_le (t/2)).trans (Nat.div_le_self _ _)
  · exact le_rfl
termination_by t
decreasing_by omega

lemma strip_odd (t : ℕ) (ht : 0<t) : strip t % 2 = 1 := by
  rw [strip]
  simp only [Nat.ne_of_gt ht, ↓reduceIte]
  split_ifs with h
  · exact strip_odd (t/2) (by omega)
  · omega
termination_by t
decreasing_by omega

lemma strip_twice (t : ℕ) (ht : 0<t) : strip (t+t) = strip t := by
  rw [strip]
  simp [show t≠0 by omega, show t+t≠0 by omega, show (t+t)%2=0 by omega,
    show (t+t)/2=t by omega]

lemma strip_of_odd (t : ℕ) (ht : t%2=1) : strip t=t := by
  rw [strip]
  simp [show t≠0 by omega, show t%2≠0 by omega]

lemma up_lt (N x : ℕ) (hx : 0<x) (hN : x<N) : up N x < N := by
  rw [up]
  simp only [Nat.ne_of_gt hx, ↓reduceDIte]
  split_ifs with h
  · omega
  · exact up_lt N (x+x) (by omega) (by omega)
termination_by N-x
decreasing_by omega

lemma up_parity (N x : ℕ) (hx : 0<x) (hN : x<N) : up N x % 2 = N%2 := by
  rw [up]
  simp only [Nat.ne_of_gt hx, ↓reduceDIte]
  split_ifs with h
  · omega
  · exact up_parity N (x+x) (by omega) (by omega)
termination_by N-x
decreasing_by omega

lemma up_scale (N x : ℕ) (hx : 0<x) (hN : x<N) :
    up (N+N) (x+x) = up N x + up N x := by
  conv_lhs => rw [up]
  conv_rhs => rw [up]
  simp only [show x+x≠0 by omega, Nat.ne_of_gt hx, ↓reduceDIte]
  by_cases h : N≤x+x
  · simp only [h, show N+N≤(x+x)+(x+x) by omega, ↓reduceDIte]
    omega
  · simp only [h, show ¬N+N≤(x+x)+(x+x) by omega, ↓reduceDIte]
    exact up_scale N (x+x) (by omega) (by omega)
termination_by N-x
decreasing_by omega

lemma up_half_start (N x : ℕ) (hx : 0<x) (hN : x<N) :
    up (N+N) x = up N x + up N x := by
  conv_lhs => rw [up]
  simp only [Nat.ne_of_gt hx, show ¬N+N≤x+x by omega, ↓reduceDIte]
  exact up_scale N x hx hN

lemma shuffle_odd_val (N : ℕ) (x : Fin N) (ho : x.val%2=1) :
    (shuffle N x).val = up N x.val := by
  rw [shuffle_val, odd_token N x.val x.isLt ho]

lemma shuffle_even_val (N : ℕ) (j : ℕ) (hj : j+j<N) :
    (shuffle N ⟨j+j,hj⟩).val = N-strip (N-j) := by
  rw [shuffle_val, even_token N j hj]

lemma shuffle_parity (M : ℕ) (x : Fin (M+M)) :
    (shuffle (M+M) x).val%2 = 1-x.val%2 := by
  by_cases he : x.val%2=0
  · have hx : x.val=x.val/2+x.val/2 := by omega
    have h := shuffle_even_val (M+M) (x.val/2) (by omega)
    have hh : (⟨x.val/2+x.val/2,by omega⟩ : Fin (M+M))=x := by ext; exact hx.symm
    rw [hh] at h
    rw [h]
    have hs := strip_odd (M+M-x.val/2) (by have:=x.isLt; omega)
    have hl := strip_le (M+M-x.val/2)
    omega
  · have ho : x.val%2=1 := by omega
    rw [shuffle_odd_val (M+M) x ho, up_parity (M+M) x.val (by omega) x.isLt]
    omega

lemma shuffle_twice_even (M j : ℕ) (hj : j<M) :
    (shuffle (M+M) (shuffle (M+M) ⟨j+j,by omega⟩)).val =
      (shuffle M ⟨j,hj⟩).val + (shuffle M ⟨j,hj⟩).val := by
  have hfirst := shuffle_even_val (M+M) j (by omega)
  have hsodd := strip_odd (M+M-j) (by omega)
  have hsle := strip_le (M+M-j)
  have hp : (shuffle (M+M) ⟨j+j,by omega⟩).val % 2 = 1 := by rw [hfirst]; omega
  rw [shuffle_odd_val _ _ hp, hfirst]
  by_cases he : j%2=0
  · obtain ⟨k,hk⟩ : ∃ k, j=k+k := ⟨j/2, by omega⟩
    have hdiff : M+M-j=(M-k)+(M-k) := by omega
    rw [hdiff, strip_twice (M-k) (by omega)]
    have hlt := strip_le (M-k)
    have hpos := strip_pos (M-k) (by omega)
    have hright := shuffle_even_val M k (by omega)
    have hfin : (⟨k+k,by omega⟩ : Fin M)=⟨j,hj⟩ := by apply Fin.ext; exact hk.symm
    rw [hfin] at hright
    rw [hright, up]
    simp only [show M+M-strip (M-k)≠0 by omega,
      show M+M≤(M+M-strip (M-k))+(M+M-strip (M-k)) by omega, ↓reduceDIte]
    omega
  · have ho : j%2=1 := by omega
    have hdiff : (M+M-j)%2=1 := by omega
    rw [strip_of_odd _ hdiff]
    have heq : M+M-(M+M-j)=j := by omega
    rw [heq, shuffle_odd_val M ⟨j,hj⟩ ho]
    exact up_half_start M j (by omega) hj

end ShuffleProof

namespace ShuffleProof

def trace (N x t : ℕ) : ℕ := (2^t*x)%N

lemma trace_zero (N x : ℕ) (hx : x<N) : trace N x 0=x := by simp [trace, Nat.mod_eq_of_lt hx]
lemma trace_next (N x t : ℕ) : trace N x (t+1) =
    (trace N x t + trace N x t)%N := by
  change (2^(t+1)*x)%N = ((2^t*x)%N + (2^t*x)%N)%N
  rw [← Nat.add_mod]
  congr 1
  rw [pow_succ]
  ring

lemma double_pos (N x : ℕ) (hN : N%2=1) (hx : 0<x) (hlt : x<N) :
    0<(x+x)%N := by
  rw [mod_double_cases N x hlt]
  split_ifs <;> omega

lemma trace_pos (N x t : ℕ) (hN : N%2=1) (hx : 0<x) (hlt : x<N) :
    0<trace N x t ∧ trace N x t<N := by
  induction t with
  | zero => simpa [trace_zero N x hlt] using And.intro hx hlt
  | succ t ih =>
    rw [trace_next]
    exact ⟨double_pos N _ hN ih.1 ih.2, Nat.mod_lt _ (by omega)⟩

lemma trace_half (d x t : ℕ) (hd : 0<d) (hx : 0<x) (hlt : x<2^d+1) :
    trace (2^d+1) x (d+t) = (2^d+1)-trace (2^d+1) x t := by
  have hodd : (2^d+1)%2=1 := by
    have he : 2∣2^d := dvd_pow_self 2 (by omega : d≠0)
    omega
  have hp := trace_pos (2^d+1) x t hodd hx hlt
  have he : 2^d * trace (2^d+1) x t =
      (2^d+1)*(trace (2^d+1) x t-1)+((2^d+1)-trace (2^d+1) x t) := by
    nlinarith [Nat.sub_add_cancel (show 1≤trace (2^d+1) x t by omega), Nat.sub_add_cancel (Nat.le_of_lt hp.2)]
  calc
    trace (2^d+1) x (d+t) = (2^d * trace (2^d+1) x t) % (2^d+1) := by
      simp only [trace, pow_add, Nat.mul_mod_mod, Nat.mul_assoc]
    _ = (2^d+1)-trace (2^d+1) x t := by
      rw [he, Nat.add_mod]
      simp [Nat.mod_eq_of_lt (show (2^d+1)-trace (2^d+1) x t <2^d+1 by omega)]

lemma up_step (N x : ℕ) (hN : N%2=1) (hx : 0<x) (hlt : x<N) :
    up N ((x+x)%N) =
      if ((x+x)%N)%2=1 then run N 0 N (up N x) else up N x := by
  by_cases h : N≤x+x
  · have he : (x+x)%N=x+x-N := by rw [mod_double_cases N x hlt, if_neg (by omega)]
    have ho : ((x+x)%N)%2=1 := by rw [he]; omega
    have hu : up N x=(x+x)%N := by
      conv_lhs => rw [up]
      simp [Nat.ne_of_gt hx, h, he]
    rw [if_pos ho, hu, odd_token N _ (Nat.mod_lt _ (by omega)) ho]
  · have he : (x+x)%N=x+x := Nat.mod_eq_of_lt (by omega)
    have ho : ((x+x)%N)%2≠1 := by rw [he]; omega
    rw [if_neg ho, he]
    conv_rhs => rw [up]
    simp [Nat.ne_of_gt hx, h]

def visits (N x t : ℕ) : ℕ := ∑ i ∈ Finset.range t, if trace N x (i+1)%2=1 then 1 else 0

lemma visits_succ (N x t : ℕ) : visits N x (t+1) =
    visits N x t + if trace N x (t+1)%2=1 then 1 else 0 := by
  exact Finset.sum_range_succ _ _

lemma visits_full (d x : ℕ) (hd : 0<d) (hx : 0<x) (hlt : x<2^d+1) :
    visits (2^d+1) x (d+d) = d := by
  have hodd : (2^d+1)%2=1 := by
    have he : 2∣2^d := dvd_pow_self 2 (by omega : d≠0)
    omega
  rw [visits, Finset.sum_range_add, ← Finset.sum_add_distrib]
  calc
    _ = ∑ i ∈ Finset.range d, 1 := by
      apply Finset.sum_congr rfl
      intro i hi
      have hp := trace_pos (2^d+1) x (i+1) hodd hx hlt
      have hh := trace_half d x (i+1) hd hx hlt
      rw [show d+i+1=d+(i+1) by omega, hh]
      split_ifs <;> omega
    _ = d := by simp

lemma trace_full (d x : ℕ) (hd : 0<d) (hx : 0<x) (hlt : x<2^d+1) :
    trace (2^d+1) x (d+d) = x := by
  have hh := trace_half d x 0 hd hx hlt
  simp only [Nat.add_zero, trace_zero _ _ hlt] at hh
  rw [trace_half d x d hd hx hlt, hh]
  omega

lemma visits_apply (N x t : ℕ) (hN : N%2=1) (hx : 0<x) (hlt : x<N) :
    (shuffle N ^ visits N x t) ⟨up N x,up_lt N x hx hlt⟩ =
      ⟨up N (trace N x t), up_lt N _ (trace_pos N x t hN hx hlt).1
        (trace_pos N x t hN hx hlt).2⟩ := by
  induction t with
  | zero => apply Fin.ext; simp [visits, trace_zero N x hlt]
  | succ t ih =>
    have hp := trace_pos N x t hN hx hlt
    have hu := up_step N (trace N x t) hN hp.1 hp.2
    rw [← trace_next] at hu
    rw [visits_succ]
    by_cases he : trace N x (t+1)%2=1
    · rw [if_pos he, pow_succ', Equiv.Perm.mul_apply, ih]
      apply Fin.ext
      rw [shuffle_val]
      exact (if_pos he ▸ hu).symm
    · rw [if_neg he, Nat.add_zero, ih]
      apply Fin.ext
      exact (if_neg he ▸ hu).symm

lemma odd_power (d : ℕ) (hd : 0<d) (z : Fin (2^d+1)) (hz : z.val%2=1) :
    (shuffle (2^d+1)^d) z=z := by
  have hN : (2^d+1)%2=1 := by
    have he : 2∣2^d := dvd_pow_self 2 (by omega : d≠0)
    omega
  have hx : 0<z.val := by omega
  have h := visits_apply (2^d+1) z.val (d+d) hN hx z.isLt
  rw [visits_full d z.val hd hx z.isLt] at h
  have ht := trace_full d z.val hd hx z.isLt
  have hs : (⟨up (2^d+1) z.val, up_lt _ _ hx z.isLt⟩ : Fin (2^d+1))=
      shuffle (2^d+1) z := by apply Fin.ext; exact (shuffle_odd_val _ _ hz).symm
  have hh : (shuffle (2^d+1)^d) (shuffle (2^d+1) z)=shuffle (2^d+1) z := by
    simpa only [ht, hs] using h
  apply (shuffle (2^d+1)).injective
  change (shuffle (2^d+1) * shuffle (2^d+1)^d) z=shuffle (2^d+1) z
  rw [← pow_succ', pow_succ, Equiv.Perm.mul_apply]
  exact hh

end ShuffleProof

namespace ShuffleProof

def flip (N : ℕ) (x : Fin N) : Fin N :=
  ⟨if x.val=0 then 0 else N-x.val, by split_ifs with h <;> have := x.isLt <;> omega⟩

lemma flip_val (N : ℕ) (x : Fin N) (hx : 0<x.val) : (flip N x).val=N-x.val := by
  simp [flip, show x.val≠0 by omega]

lemma flip_flip (N : ℕ) (x : Fin N) : flip N (flip N x)=x := by
  apply Fin.ext
  dsimp [flip]
  split_ifs <;> have := x.isLt <;> omega

lemma strip_up (N x : ℕ) (hx : 0<x) (hlt : x<N) :
    strip ((N+up N x)/2)=strip x := by
  conv_lhs => rw [up]
  simp only [Nat.ne_of_gt hx, ↓reduceDIte]
  by_cases h : N≤x+x
  · simp only [h, ↓reduceDIte]
    rw [show (N+(x+x-N))/2=x by omega]
  · simp only [h, ↓reduceDIte]
    rw [strip_up N (x+x) (by omega) (by omega), strip_twice x hx]
termination_by N-x
decreasing_by omega

lemma shuffle_odd_parity (N : ℕ) (hN : N%2=1) (x : Fin N) (hx : x.val%2=1) :
    (shuffle N x).val%2=1 := by
  rw [shuffle_odd_val _ _ hx, up_parity N x.val (by omega) x.isLt, hN]

lemma shuffle_neg_pair (N : ℕ) (hN : N%2=1) (x : Fin N) (hx : x.val%2=1) :
    shuffle N (flip N (shuffle N x)) = flip N x := by
  have hp := shuffle_odd_parity N hN x hx
  have hlt := (shuffle N x).isLt
  have hxlt := x.isLt
  have hpos : 0<(shuffle N x).val := by omega
  have hf := flip_val N (shuffle N x) hpos
  have he : (N-(shuffle N x).val)%2=0 := by omega
  have hk : (N-(shuffle N x).val)/2+(N-(shuffle N x).val)/2=N-(shuffle N x).val := by omega
  have hj : (N-(shuffle N x).val)/2+(N-(shuffle N x).val)/2<N := by omega
  have hid : (⟨(N-(shuffle N x).val)/2+(N-(shuffle N x).val)/2,hj⟩ : Fin N)=
      flip N (shuffle N x) := by apply Fin.ext; rw [hf]; exact hk
  have hs := shuffle_even_val N ((N-(shuffle N x).val)/2) hj
  rw [hid] at hs
  apply Fin.ext
  rw [hs, flip_val N x (by omega)]
  have hhalf : N-(N-(shuffle N x).val)/2=(N+(shuffle N x).val)/2 := by omega
  rw [hhalf, shuffle_odd_val N x hx, strip_up N x.val (by omega) x.isLt,
    strip_of_odd x.val hx]

lemma shuffle_pow_odd_parity (N : ℕ) (hN : N%2=1) (x : Fin N) (hx : x.val%2=1) (k : ℕ) :
    ((shuffle N ^k) x).val%2=1 := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact shuffle_odd_parity N hN _ ih

lemma shuffle_neg_iterate (N : ℕ) (hN : N%2=1) (x : Fin N) (hx : x.val%2=1) (k : ℕ) :
    (shuffle N^k) (flip N ((shuffle N^k) x))=flip N x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hp := shuffle_pow_odd_parity N hN x hx k
    have hs := shuffle_neg_pair N hN ((shuffle N^k) x) hp
    calc
      (shuffle N^(k+1)) (flip N ((shuffle N^(k+1)) x)) =
          (shuffle N^k) (shuffle N (flip N (shuffle N ((shuffle N^k) x)))) := by
            conv_lhs => arg 1; rw [pow_succ]
            simp only [Equiv.Perm.mul_apply]
            rw [pow_succ', Equiv.Perm.mul_apply]
      _ = (shuffle N^k) (flip N ((shuffle N^k) x)) := by rw [hs]
      _ = flip N x := ih

lemma shuffle_zero (N : ℕ) (hN : N%2=1) :
    shuffle N ⟨0,by omega⟩=⟨0,by omega⟩ := by
  apply Fin.ext
  have h := shuffle_even_val N 0 (by omega)
  simpa [strip_of_odd N hN] using h

lemma full_odd_power (d : ℕ) (hd : 0<d) : shuffle (2^d+1)^d=1 := by
  have hN : (2^d+1)%2=1 := by
    have he : 2∣2^d := dvd_pow_self 2 (by omega : d≠0)
    omega
  ext x
  by_cases hx : x.val%2=1
  · exact congrArg Fin.val (odd_power d hd x hx)
  · by_cases hz : x.val=0
    · have hzero := shuffle_zero (2^d+1) hN
      have hp : ∀ k, (shuffle (2^d+1)^k) ⟨0,by omega⟩=⟨0,by omega⟩ := by
        intro k; induction k with
        | zero => rfl
        | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, hzero]
      have he : x=(⟨0,by omega⟩ : Fin (2^d+1)) := by apply Fin.ext; exact hz
      rw [he]
      exact congrArg Fin.val (hp d)
    · have hv := x.isLt
      have hf := flip_val (2^d+1) x (by omega)
      have ho : (flip (2^d+1) x).val%2=1 := by rw [hf]; omega
      have hs := shuffle_neg_iterate (2^d+1) hN (flip (2^d+1) x) ho d
      rw [odd_power d hd _ ho, flip_flip] at hs
      exact congrArg Fin.val hs

end ShuffleProof

namespace ShuffleProof

lemma up_pow (d k : ℕ) (hk : k≤d) : up (2^d+1) (2^k)=2^d-1 := by
  have hp : 0<2^k := by positivity
  have hd : 0<2^d := by positivity
  conv_lhs => rw [up]
  simp only [Nat.ne_of_gt hp, ↓reduceDIte]
  by_cases he : k=d
  · subst k
    simp only [show 2^d+1≤2^d+2^d by omega, ↓reduceDIte]
    omega
  · have hkd : k+1≤d := by omega
    have hpow : 2^(k+1)≤2^d := Nat.pow_le_pow_right (by decide) hkd
    have heq : 2^k+2^k=2^(k+1) := by rw [pow_succ]; omega
    simp only [show ¬2^d+1≤2^k+2^k by omega, ↓reduceDIte]
    rw [heq]
    exact up_pow d (k+1) hkd
termination_by d-k
decreasing_by omega

lemma one_iterate (d k : ℕ) (hd : 0<d) (hk : 0<k) (hkd : k≤d) :
    ((shuffle (2^d+1)^k) ⟨1,by have hp : 0<2^d := (by positivity); omega⟩).val =
      2^d+1-2^k := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  by_cases hj : j=0
  · subst j
    simp only [Nat.zero_add, pow_one]
    rw [shuffle_odd_val _ _ (by change 1%2=1; decide)]
    have hh := up_pow d 0 (by omega)
    simpa using hh
  · have hpow : 2^(j+1)≤2^d := Nat.pow_le_pow_right (by decide) hkd
    have hp : 0<2^j := by positivity
    have heq : 2^j+2^j=2^(j+1) := by rw [pow_succ]; omega
    have hodd : (2^d+1)%2=1 := by
      have he : 2∣2^d := dvd_pow_self 2 (by omega : d≠0)
      omega
    have hpar := shuffle_pow_odd_parity (2^d+1) hodd
      (⟨1,by have hp : 0<2^d := (by positivity); omega⟩ : Fin (2^d+1)) (by change 1%2=1; decide) j
    rw [pow_succ', Equiv.Perm.mul_apply, shuffle_odd_val _ _ hpar,
      one_iterate d j hd (by omega) (by omega)]
    conv_lhs => rw [up]
    simp only [show 2^d+1-2^j≠0 by omega,
      show 2^d+1≤(2^d+1-2^j)+(2^d+1-2^j) by omega, ↓reduceDIte]
    omega
termination_by k
decreasing_by omega

lemma odd_order (d : ℕ) (hd : 0<d) : orderOf (shuffle (2^d+1))=d := by
  apply (orderOf_eq_iff hd).2
  refine ⟨full_odd_power d hd, ?_⟩
  intro k hkd hk he
  have h := one_iterate d k hd hk (by omega)
  rw [he] at h
  have hp : 2^k<2^d := Nat.pow_lt_pow_right (by decide) hkd
  have hkpow : 2≤2^k := by
    exact Nat.le_self_pow (by omega) 2
  change 1=2^d+1-2^k at h
  omega

end ShuffleProof

namespace ShuffleProof

lemma power_commute_apply {α : Type*} (p : Equiv.Perm α) (t : ℕ) (x : α) :
    (p^t) (p x) = p ((p^t) x) := by
  change (p^t*p) x=(p*p^t) x
  rw [← pow_succ, ← pow_succ']

lemma even_iterate (M j t : ℕ) (hj : j<M) :
    ((shuffle (M+M)^(t+t)) ⟨j+j,by omega⟩).val =
      ((shuffle M^t) ⟨j,hj⟩).val + ((shuffle M^t) ⟨j,hj⟩).val := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have he : t+1+(t+1)=2+(t+t) := by omega
    rw [he, pow_add, Equiv.Perm.mul_apply]
    let y : Fin M := (shuffle M^t) ⟨j,hj⟩
    have hid : (shuffle (M+M)^(t+t)) ⟨j+j,by omega⟩ =
        (⟨y.val+y.val,by have:=y.isLt; omega⟩ : Fin (M+M)) := by
      apply Fin.ext; exact ih
    rw [hid, pow_two, Equiv.Perm.mul_apply, shuffle_twice_even M y.val y.isLt]
    rw [pow_succ', Equiv.Perm.mul_apply]

lemma even_pow_eq_iff (M t : ℕ) : shuffle (M+M)^(t+t)=1 ↔ shuffle M^t=1 := by
  constructor
  · intro h
    ext j
    have hh := even_iterate M j.val t j.isLt
    rw [h] at hh
    change j.val+j.val = ((shuffle M^t) j).val + ((shuffle M^t) j).val at hh
    change ((shuffle M^t) j).val=j.val
    omega
  · intro h
    have hev : ∀ x : Fin (M+M), x.val%2=0 → (shuffle (M+M)^(t+t)) x=x := by
      intro x hx
      let j := x.val/2
      have hj : j<M := by dsimp [j]; have:=x.isLt; omega
      have he : (⟨j+j,by omega⟩ : Fin (M+M))=x := by
        apply Fin.ext; dsimp [j]; omega
      have hh := even_iterate M j t hj
      rw [he,h] at hh
      apply Fin.ext
      change ((shuffle (M+M)^(t+t)) x).val = x.val
      simpa [j, show x.val/2+x.val/2=x.val by omega] using hh
    ext x
    by_cases hx : x.val%2=0
    · exact congrArg Fin.val (hev x hx)
    · have hp := shuffle_parity M x
      have hh := hev (shuffle (M+M) x) (by omega)
      rw [power_commute_apply] at hh
      exact congrArg Fin.val ((shuffle (M+M)).injective hh)

lemma even_power_parity (M t : ℕ) (hM : 0<M) :
    ((shuffle (M+M)^t) ⟨0,by omega⟩).val%2=t%2 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, shuffle_parity]
    omega

lemma even_order (M : ℕ) (hM : 0<M) : orderOf (shuffle (M+M))=2*orderOf (shuffle M) := by
  have hq := orderOf_pos (shuffle M)
  apply (orderOf_eq_iff (by omega : 0<2*orderOf (shuffle M))).2
  constructor
  · have h := (even_pow_eq_iff M (orderOf (shuffle M))).2 (pow_orderOf_eq_one _)
    simpa [two_mul] using h
  · intro k hk hkp h
    have he := even_power_parity M k hM
    rw [h] at he
    have hke : k%2=0 := by simpa using he.symm
    have hhalf : k=k/2+k/2 := by omega
    rw [hhalf] at h
    have hqpow := (even_pow_eq_iff M (k/2)).1 h
    have hd := orderOf_dvd_of_pow_eq_one hqpow
    have hle := Nat.le_of_dvd (show 0<k/2 by omega) hd
    omega

end ShuffleProof

namespace ShuffleProof

lemma scaled_order (n d : ℕ) (hd : 0<d) :
    orderOf (shuffle (2^n*(2^d+1))) = 2^n*d := by
  induction n with
  | zero =>
    rw [show 2^0*(2^d+1)=2^d+1 by omega]
    simpa using odd_order d hd
  | succ n ih =>
    have hN : 0<2^n*(2^d+1) := by positivity
    have he : 2^(n+1)*(2^d+1)=2^n*(2^d+1)+2^n*(2^d+1) := by rw [pow_succ]; ring
    rw [he, even_order _ hN, ih, pow_succ]
    ring

lemma complete (n x : ℕ) (h : n<x) :
    orderOf (shuffle (2^n+2^x))=2^n*(x-n) := by
  have he : 2^n+2^x=2^n*(2^(x-n)+1) := by
    have hx : x=n+(x-n) := by omega
    conv_lhs => arg 2; rw [hx, pow_add]
    ring
  rw [he]
  exact scaled_order n (x-n) (by omega)

end ShuffleProof

theorem OMA.solution : type_of% @OMA.S_oeis_a384184.main :=
  ShuffleProof.complete
