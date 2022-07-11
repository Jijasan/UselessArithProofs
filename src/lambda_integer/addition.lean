import lambda_integer.definition natural.definition natural.addition tactic.nth_rewrite

set_option pp.all false

namespace Z'

private lemma double_succ_gt (a b : N) : N.to_N (a + b) < N.to_N(N.succ a + N.succ b) := begin
  rw N.add_succ,
  rw N.succ_add,
  repeat {rw N.to_N},
  cases N.to_N (a + b),
  repeat {rw nat.add_one},
  simp,
  have q := nat.lt.base 0,
  have t := nat.lt.step q,
  exact t,
  have q := nat.lt.base n.succ,
  have t := nat.lt.step q,
  exact t,
end

private def eqq : (N × N) -> (N × N)
| (0, 0) := (0, 0)
| (0, N.succ a) := (0, N.succ a)
| (N.succ a, 0) := (N.succ a, 0)
| (N.succ a, N.succ b) := begin
  exact have N.to_N (a + b) < N.to_N (a.succ + b.succ) := double_succ_gt a b, 
    eqq (a, b)
end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ a, begin
  cases a with x y,
  exact N.to_N (x + y),
end)⟩] }

lemma eqq_0_0 : eqq (0, 0) = (0, 0) := by { rw eqq }
lemma eqq_0_succ_a (a : N) : eqq (0, N.succ a) = (0, N.succ a) := by { rw eqq }
lemma eqq_succ_a_0 (a : N) : eqq (N.succ a, 0) = (N.succ a, 0) := by { rw eqq }
lemma eqq_succ_succ (a b : N) : eqq (N.succ a, N.succ b) = eqq (a, b) := by { rw eqq }

lemma eqq_0_a (a : N) : eqq (0, a) = (0, a) := begin
  cases a,
  exact eqq_0_0,
  exact eqq_0_succ_a a,
end
lemma eqq_a_0 (a : N) : eqq (a, 0) = (a, 0) := begin
  cases a,
  rw N.zero_eq_zero,
  exact eqq_0_0,
  exact eqq_succ_a_0 _,
end

lemma eqq_plus_a_fir (a b : N) : eqq (a + b, a) = (b, 0) :=
begin
  induction a with a ah,
  rw N.zero_eq_zero,
  rw N.zero_add,
  exact eqq_a_0 _,
  rw N.succ_add,
  rw eqq_succ_succ,
  exact ah,
end
lemma eqq_a_plus_fir (a b : N) : eqq (b + a, a) = (b, 0) :=
begin
  rw N.add_comm,
  exact eqq_plus_a_fir _ _,
end

lemma eqq_plus_a_sec (a b : N) : eqq (a, a + b) = (0, b) :=
begin
  induction a with a ah,
  rw N.zero_eq_zero,
  rw N.zero_add,
  exact eqq_0_a _,
  rw N.succ_add,
  rw eqq_succ_succ,
  exact ah,
end
lemma eqq_a_plus_sec (a b : N) : eqq (a, b + a) = (0, b) :=
begin
  rw N.add_comm,
  exact eqq_plus_a_sec _ _,
end

private def fst_eq (a b : N) : (a, b).fst = a := rfl
private def snd_eq (a b : N) : (a, b).snd = b := rfl

private def eqq_eq_helper: ∀ (a b c d : N), z_rel (a, b) (c, d) -> eqq (a, b) = eqq (c, d)
| 0 b c d := begin
  intro h,
    rw z_rel at h,
    repeat {rw fst_eq at h, rw snd_eq at h},
    rw N.zero_add at h,
    rw h,
    rw eqq_0_a,
    rw eqq_a_plus_sec _ _,
end
| a 0 c d := begin
  intro h,
  rw z_rel at h,
  repeat {rw fst_eq at h, rw snd_eq at h},
  rw N.zero_add at h,
  rw ← h,
  rw eqq_a_0,
  rw eqq_a_plus_fir,
end
| (N.succ a) (N.succ b) c d := begin
  intro h,
  rw z_rel at h,
  repeat {rw fst_eq at h, rw snd_eq at h},
  repeat {rw N.succ_add at h},
  have q := N.succ_eq _ _ h,
  rw eqq_succ_succ,
  exact eqq_eq_helper a b c d q,
end

lemma eqq_cont_zero : ∀ (a b : N), (eqq (a, b)).fst = 0 ∨ (eqq (a, b)).snd = 0
| 0 b := begin
  rw eqq_0_a,
  rw fst_eq,
  left,
  refl,
end
| a 0 := begin
  rw eqq_a_0,
  rw snd_eq,
  right,
  refl,
end
| (N.succ a) (N.succ b) := begin
  rw eqq_succ_succ,
  exact eqq_cont_zero a b,
end

private def eqq_eq (a b : N × N) : z_rel a b -> eqq a = eqq b :=
begin
  cases a,
  cases b,
  exact eqq_eq_helper a_fst a_snd b_fst b_snd,
end

lemma paren_eq_mk (a : N × N): ⟦a⟧ = quot.mk z_rel a := rfl

lemma a_norm_eq_a_helper: ∀ (a b : N), (eqq (a, b)).fst + b = (eqq (a, b)).snd + a
| 0 b := begin
  rw eqq_0_a,
  rw fst_eq,
  rw snd_eq,
  rw N.add_comm,
end
| a 0 := begin
  rw eqq_a_0,
  rw fst_eq,
  rw snd_eq,
  rw N.add_comm,
end
| (N.succ a) (N.succ b) := begin
  rw eqq_succ_succ,
  repeat {rw N.add_succ},
  rw a_norm_eq_a_helper a b,
end

def norm (a : Z') : N × N := quot.lift eqq eqq_eq a
lemma norm_deconstruction (a b : N) : norm ⟦(a, b)⟧ = eqq (a, b) := rfl
lemma a_norm_eq_a (a : Z') : ⟦((norm a).fst, (norm a).snd)⟧ = a := begin
  rw paren_eq_mk,
  induction a,
  apply quot.sound,
  rw z_rel,
  rw fst_eq,
  rw snd_eq (norm (quot.mk z_rel a)).fst (norm (quot.mk z_rel a)).snd,
  rw ← paren_eq_mk,
  cases a,
  rw norm_deconstruction,
  exact a_norm_eq_a_helper a_fst a_snd,
  refl,
end
lemma zero_norm : norm 0 = (0, 0) := begin
  rw zero_eq_zero, rw zero,
  rw norm_deconstruction,
  rw eqq_0_0,
end

lemma norm_cont_zero (a : Z') : ((norm a).fst = 0) ∨ ((norm a).snd = 0) := begin
  induction a,
  cases a,
  rw ← paren_eq_mk,
  rw norm_deconstruction,
  exact eqq_cont_zero a_fst a_snd,
  refl,
end

def add (a b : Z') : Z' := ⟦((norm a).fst + (norm b).fst, (norm b).snd + (norm a).snd)⟧

instance : has_add Z' := ⟨ add ⟩

lemma add_deconstruct (a b : Z') : a + b = ⟦((norm a).fst + (norm b).fst, (norm b).snd + (norm a).snd)⟧ := rfl

def pair_add (a b : N × N) : N × N := begin
  cases a,
  cases b,
  exact (a_fst + b_fst, a_snd + b_snd),
end

instance : has_add (N × N) := ⟨ pair_add ⟩ 

lemma pair_add_deconstruction (a b c d : N) : (a, b) + (c, d) = (a + c, b + d) := rfl

lemma pair_add_fst (a b : N × N) : a.fst + b.fst = (a + b).fst := begin
  cases a,
  cases b,
  rw pair_add_deconstruction,
end

lemma pair_add_snd (a b : N × N) : a.snd + b.snd = (a + b).snd := begin
  cases a,
  cases b,
  rw pair_add_deconstruction,
end

lemma add_eq_eqq (a b : Z') : norm (a + b) = eqq (norm a + norm b) := begin
  rw add_deconstruct,
  rw norm_deconstruction,
  cases a.norm,
  cases b.norm,
  repeat {rw fst_eq, rw snd_eq},
  rw pair_add_deconstruction,
  rw N.add_comm snd snd_1,
end

theorem add_zero (a : Z') : a + 0 = a := begin
  rw add_deconstruct,
  rw zero_norm,
  rw fst_eq 0 0,
  rw snd_eq 0 0,
  rw N.add_zero,
  rw N.zero_add,
  exact a_norm_eq_a a,
end

theorem zero_add (a : Z') : 0 + a = a := begin
  rw add_deconstruct,
  rw zero_norm,
  rw fst_eq,
  rw snd_eq 0 0,
  rw N.zero_add,
  rw N.add_zero,
  exact a_norm_eq_a a,
end

theorem add_comm (a b : Z') : a + b = b + a := begin
  repeat {rw add_deconstruct},
  rw N.add_comm b.norm.fst,
  rw N.add_comm b.norm.snd,
end

instance : has_add (quot z_rel) := ⟨ add ⟩ 

lemma add_eqq_left : ∀ (a b c d : N), (a + c = b + d) -> ((eqq (a, b)).fst + c = (eqq (a, b)).snd + d)
| 0 b c d := begin
  intro h,
  rw eqq_0_a,
  rw fst_eq,
  rw snd_eq,
  exact h,
end
| a 0 c d := begin
  intro h,
  rw eqq_a_0,
  rw fst_eq,
  rw snd_eq,
  exact h,
end
| (N.succ a) (N.succ b) c d := begin
  intro h,
  repeat {rw N.succ_add at h},
  have q := N.succ_eq _ _ h,
  rw eqq_succ_succ,
  exact add_eqq_left _ _ _ _ q,
end

theorem add_distrib (a b: N × N): quot.mk z_rel a + quot.mk z_rel b = quot.mk z_rel (a + b) := begin
  rw ← paren_eq_mk,
  rw add_deconstruct,
  repeat {rw paren_eq_mk},
  rw quot.sound,
  rw z_rel,
  rw fst_eq,
  rw snd_eq ((norm (quot.mk z_rel a)).fst + (norm (quot.mk z_rel b)).fst) ((norm (quot.mk z_rel b)).snd + (norm (quot.mk z_rel a)).snd),
  repeat {rw ← paren_eq_mk},
  cases a,
  cases b,
  repeat {rw norm_deconstruction},
  rw pair_add_deconstruction,
  rw snd_eq,
  rw fst_eq (a_fst + b_fst) (a_snd + b_snd),
  rw N.add_assoc,
  rw N.add_comm (eqq(b_fst, b_snd)).snd (eqq (a_fst, a_snd)).snd,
  rw N.add_assoc,
  apply add_eqq_left,
  repeat {rw ← N.add_assoc},
  rw N.add_comm a_fst,
  rw N.add_comm a_snd,
  repeat {rw N.add_assoc},
  apply add_eqq_left,
  rw N.add_comm a_snd,
  rw ← N.add_assoc a_fst,
  rw N.add_comm a_fst,
  repeat {rw ← N.add_assoc b_fst},
  rw N.add_comm b_fst,
  rw N.add_assoc,
  rw N.add_comm a_fst,
  rw N.add_assoc,
  rw ← N.add_assoc b_fst,
  rw N.add_comm b_fst,
  rw N.add_assoc,
  rw N.add_comm b_fst,
end

theorem add_assoc (a b c : Z') : (a + b) + c = a + (b + c) := begin
  rw ← a_norm_eq_a a,
  rw ← a_norm_eq_a b,
  rw ← a_norm_eq_a c,
  repeat {rw paren_eq_mk},
  repeat {rw add_distrib},
  repeat {rw pair_add_deconstruction},
  repeat {rw N.add_assoc},
end

end Z'