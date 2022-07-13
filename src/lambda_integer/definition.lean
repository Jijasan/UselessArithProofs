import natural.definition natural.addition natural.equality

def z_rel (a b : N × N) := a.1 + b.2 = a.2 + b.1
def Z' : Type := quot z_rel

namespace Z'

def reflex : reflexive z_rel := begin 
  intro h,
  rw z_rel,
  rw N.add_comm,
end
def symmet : symmetric z_rel := begin
  intro x,
  intro y,
  intro h,
  rw z_rel,
  rw z_rel at h,
  rw N.add_comm at h,
  rw h,
  rw N.add_comm,
end
def trans : transitive z_rel := begin
  intros x y z,
  repeat {rw z_rel},
  intro p,
  intro q,
  rw ← N.eq_add _ _ z.fst at p,
  rw N.add_assoc at p,
  rw ← q at p,
  rw N.add_assoc x.snd _ _ at p,
  repeat {rw N.add_comm y.fst _ at p},
  repeat {rw ← N.add_assoc at p},
  rw N.eq_add _ _ y.fst at p,
  exact p,
end

instance : setoid (N × N) := ⟨ z_rel, ⟨ reflex, symmet, trans ⟩ ⟩ 

def one : Z' := ⟦(1, 0)⟧
instance : has_one Z' := ⟨ one ⟩ 

lemma one_eq_one : 1 = one := rfl

def zero : Z' := ⟦(0, 0)⟧
instance : has_zero Z' := ⟨ zero ⟩ 

lemma zero_eq_zero : 0 = zero := rfl

def fromN (a : N) : Z' := ⟦(a, 0)⟧

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

def eqq : (N × N) -> (N × N)
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
lemma eqq_a_a (a : N) : eqq (a, a) = (0, 0) := begin
  induction a with a ah,
  rw N.zero_eq_zero,
  rw eqq_0_0,
  rw eqq_succ_succ,
  exact ah,
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

lemma eqq_plus_right (a b c : N) : eqq (a + c, b + c) = eqq (a, b) :=
begin
  induction c with c ch,
  rw N.zero_eq_zero,
  repeat {rw N.add_zero},
  repeat {rw N.add_succ},
  rw eqq_succ_succ,
  exact ch,
end
lemma eqq_plus_left (a b c : N) : eqq (c + a, c + b) = eqq (a, b) :=
begin
  repeat {rw N.add_comm c},
  exact eqq_plus_right _ _ _,
end

lemma fst_eq (a b : N) : (a, b).fst = a := rfl
lemma snd_eq (a b : N) : (a, b).snd = b := rfl
lemma pair_deconstruct (a : N × N) : a = (a.fst, a.snd) := begin
  cases a,
  rw fst_eq,
end

lemma eqq_symm: ∀ (a b : N), eqq (a, b) = ((eqq (b, a)).snd, (eqq (b, a)).fst)
| 0 b := begin
  rw eqq_0_a,
  rw eqq_a_0,
end
| a 0 := begin
  rw eqq_0_a,
  rw eqq_a_0,
end
| (N.succ a) (N.succ b) := begin
  repeat {rw eqq_succ_succ},
  exact eqq_symm a b,
end

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

def eqq_eq (a b : N × N) : z_rel a b -> eqq a = eqq b :=
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
lemma norm_eq_a (a: Z') : ⟦norm a⟧ = a := begin
  rw pair_deconstruct (a.norm),
  exact a_norm_eq_a a,
end
lemma zero_norm : norm 0 = (0, 0) := begin
  rw zero_eq_zero, rw zero,
  rw norm_deconstruction,
  rw eqq_0_0,
end
lemma one_norm : norm 1 = (1, 0) := begin
  rw one_eq_one,
  rw one,
  rw norm_deconstruction,
  rw eqq_a_0,
end

lemma norm_cont_zero (a : Z') : ((norm a).fst = 0) ∨ ((norm a).snd = 0) := begin
  induction a,
  cases a,
  rw ← paren_eq_mk,
  rw norm_deconstruction,
  exact eqq_cont_zero a_fst a_snd,
  refl,
end

lemma norm_symm (a b : N) : norm ⟦(b, a)⟧ = ((norm ⟦(a, b)⟧).snd, (norm ⟦(a, b)⟧).fst) := begin
  rw norm_deconstruction,
  rw norm_deconstruction,
  rw eqq_symm,
end

end Z'