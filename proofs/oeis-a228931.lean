import OMAStatements.S_oeis_a228931

namespace OMA.S_oeis_a228931

private def traceState (z : ℝ) (q : ℤ) : Prop :=
  0 < |z| ∧ |z| < 1/2 ∧ (q:ℝ)*|z| = 1 + |z|^2

private theorem state_mag {z : ℝ} {q : ℤ} (h : traceState z q) : magnitude z=q := by
  obtain ⟨hp,hb,he⟩ := h
  have hr : 1/|z| = (q:ℝ)-|z| := (div_eq_iff (ne_of_gt hp)).mpr (by nlinarith)
  unfold magnitude
  rw [round_eq_iff,hr]
  exact ⟨by linarith,by linarith⟩

private theorem step_eq {z : ℝ} {q : ℤ} (h : traceState z q) : step z = |z|^2 := by
  simp only [step,state_mag h]
  linarith [h.2.2]

private theorem next_state {z : ℝ} {q : ℤ} (h : traceState z q) :
    traceState (step z) (q^2-2) := by
  rw [step_eq h]
  rcases h with ⟨hp,hb,he⟩
  simp only [traceState,abs_of_nonneg (sq_nonneg |z|),Int.cast_sub,Int.cast_pow,Int.cast_ofNat]
  refine ⟨sq_pos_of_pos hp,by nlinarith [mul_pos hp (by linarith : 0<1-|z|)],?_⟩
  have hs := congrArg (fun x:ℝ => x^2) he
  nlinarith only [hs]

private theorem initial :
    magnitude (residual 0)=2 ∧ 0<residual 0 ∧ residual 1<0 ∧ traceState (residual 1) 6 := by
  let s := Real.sqrt 2
  have h2 : s^2=2 := Real.sq_sqrt (by norm_num)
  have hs : 7/5 < s := by dsimp [s]; nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  have ht : s<3/2 := by nlinarith
  have h0 : residual 0=s-1 := rfl
  have hp : 0<residual 0 := by rw [h0]; linarith
  have hq : magnitude (residual 0)=2 := by
    unfold magnitude
    rw [round_eq_iff,abs_of_pos hp,h0]
    constructor
    · apply (le_div_iff₀ (by linarith : 0<s-1)).mpr; norm_num; linarith
    · apply (div_lt_iff₀ (by linarith : 0<s-1)).mpr; norm_num; linarith
  have h1 : residual 1=2*s-3 := by
    change step (residual 0)=_
    rw [step,abs_of_pos hp,hq,h0]; push_cast; ring
  have hneg : residual 1<0 := by rw [h1]; linarith
  refine ⟨hq,hp,hneg,?_⟩
  unfold traceState
  rw [abs_of_neg hneg,h1]
  norm_num
  exact ⟨by linarith,by linarith,by nlinarith⟩

private theorem states (k : ℕ) : ∃ q, traceState (residual (k+1)) q := by
  induction k with
  | zero => exact ⟨6,initial.2.2.2⟩
  | succ k ih =>
    obtain ⟨q,h⟩ := ih
    exact ⟨q^2-2,next_state h⟩

private theorem recurrence (k : ℕ) :
    digit (residual (k+2)) = digit (residual (k+1))^2-2 ∧ 0 < digit (residual (k+2)) := by
  obtain ⟨q,h⟩ := states k
  have hnext := next_state h
  have hpos : 0<residual (k+2) := by
    change 0<step _
    rw [step_eq h]
    exact sq_pos_of_pos h.1
  have hm : magnitude (residual (k+2))=q^2-2 := state_mag hnext
  have hpositive : 0 < ((q^2-2:ℤ):ℝ) := pos_of_mul_pos_left
    (hnext.2.2.symm ▸ by positivity) hnext.1.le
  have hi : (0:ℤ) < q^2-2 := by exact_mod_cast hpositive
  simp only [digit,not_lt_of_gt hpos,if_false,hm,state_mag h]
  split_ifs <;> simp <;> omega

end OMA.S_oeis_a228931

open OMA.S_oeis_a228931 in
theorem OMA.solution : type_of% @OMA.S_oeis_a228931.main := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa [a,digit,not_lt_of_gt initial.2.1] using initial.1
  · simp [a,digit,initial.2.2.1,state_mag initial.2.2.2]
  · intro n hn
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
    simpa [a,show 3+k-1=k+2 by omega] using (recurrence k).2
  · intro n hn
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
    simpa [a,show 2+k-1=k+1 by omega,add_comm _ k] using (recurrence k).1
