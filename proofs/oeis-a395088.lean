import OMAStatements.S_oeis_a395088

namespace OMA.S_oeis_a395088

lemma expand_append (u v : List Bool) : expand (u++v) = expand u ++ expand v := by
  simp [expand]

lemma growth (t : ℕ) : ∃ c cs, stage (t+1) = stage t ++ c :: cs := by
  induction t with
  | zero => exact ⟨true, [true], rfl⟩
  | succ t ih =>
    obtain ⟨c, cs, h⟩ := ih
    change ∃ b bs, expand (stage (t+1)) = expand (stage t) ++ b :: bs
    rw [h, expand_append]
    cases c
    · exact ⟨false, true :: true :: expand cs, rfl⟩
    · exact ⟨false, expand cs, rfl⟩

lemma extend {u : List Bool} (hu : LimitPrefix u) :
    ∃ b, LimitPrefix (u ++ [b]) := by
  obtain ⟨t, v, hv⟩ := hu
  obtain ⟨b, bs, hb⟩ := growth t
  cases v with
  | nil =>
    simp at hv
    exact ⟨b, t+1, bs, by simp [hb, ← hv]⟩
  | cons c cs => exact ⟨c, t, cs, by simpa [List.append_assoc] using hv⟩

lemma double_expand (u : List Bool) :
    expand (expand u) ++ [false, true, true] = predicted u := by
  induction u with
  | nil => rfl
  | cons b bs ih =>
    rw [show b :: bs = [b] ++ bs from rfl, expand_append]
    rw [expand_append, List.append_assoc, ih]
    cases b <;> rfl

lemma predicted_prefix {u : List Bool} (hu : LimitPrefix u) :
    LimitPrefix (predicted u) := by
  obtain ⟨b, t, v, hv⟩ := extend hu
  refine ⟨t+2, ?_⟩
  change predicted u <+: expand (expand (stage t))
  rw [← hv, expand_append, expand_append, expand_append, expand_append, ← double_expand]
  cases b
  · exact ⟨[false, false] ++ expand (expand v), by simp [expand, List.append_assoc]⟩
  · exact ⟨expand (expand v), by simp [expand, List.append_assoc]⟩

theorem solution :
    (∀ n : ℕ, ∃ u : List Bool, u.length = n ∧ LimitPrefix u) ∧
    (∀ u : List Bool, LimitPrefix u → LimitPrefix (predicted u)) := by
  refine ⟨?_, fun _ => predicted_prefix⟩
  intro n
  induction n with
  | zero => exact ⟨[], rfl, 0, [false], rfl⟩
  | succ n ih =>
    obtain ⟨u, hl, hu⟩ := ih
    obtain ⟨b, hb⟩ := extend hu
    exact ⟨u++[b], by simp [hl], hb⟩

end OMA.S_oeis_a395088

theorem OMA.solution : type_of% @OMA.S_oeis_a395088.main :=
  OMA.S_oeis_a395088.solution
