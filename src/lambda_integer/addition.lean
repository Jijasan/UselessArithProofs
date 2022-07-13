import lambda_integer.definition natural.definition natural.addition tactic.nth_rewrite

set_option pp.all false

namespace Z'

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

def nsmul: ∀ (a : ℕ) (b : Z'), Z'
| 0 b := 0
| (nat.succ a) b := b + nsmul a b
lemma nsmul_zero (b : Z') : nsmul 0 b = 0 := rfl
lemma nsmul_succ (a : ℕ) (b : Z') : nsmul (nat.succ a) b = b + nsmul a b := rfl

def nat_cast (a : ℕ): Z' := ⟦(N.nat_cast a, 0)⟧
lemma nat_cast_zero : nat_cast 0 = 0 := rfl
lemma nat_cast_succ (a : ℕ) : nat_cast (a.succ) = (nat_cast a) + 1 := begin
  rw nat_cast,
  rw N.nat_cast,
  rw nat_cast,
  rw one_eq_one, rw one,
  rw add_deconstruct,
  repeat {rw norm_deconstruction},
  repeat {rw eqq_a_0},
  repeat {rw fst_eq},
  repeat {rw snd_eq},
  rw N.add_zero,
  rw N.succ_eq_inc,
end

end Z'