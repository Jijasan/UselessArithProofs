import natural.addition natural.definition natural.multiplication

namespace N

def le (a b : N) := ∃ c: N, a + c = b

instance : has_le N := ⟨ le ⟩ 

def lt (a b : N) := (a ≤ b) ∧ ¬(a = b)

instance : has_lt N := ⟨ lt ⟩ 

lemma eq_comm (a b : N) : (a = b) -> (b = a) := 
begin
  intro h,
  rw h,
end

lemma zero_neq_succ (a : N): ¬(0 = succ a) := 
begin
  trivial,
end

lemma succ_neq_zero (a : N): ¬(succ a = 0) := 
begin
  intro h,
  let p := eq_comm (succ a) 0 h,
  apply zero_neq_succ a,
  exact p,
end

lemma zero_le_all (a : N): 0 ≤ a :=
begin
  existsi a,
  rw zero_add,
end

lemma zero_lt_succ (a : N): 0 < succ a :=
begin
  split,
  exact zero_le_all (succ a),
  exact zero_neq_succ a,
end

theorem eq_add (a b d : N) : (a + d = b + d) -> (a = b) :=
begin
  induction d with d hd,
  rw zero_eq_zero,
  repeat {rw add_zero},
  intro h,
  exact h,
  intro h,
  repeat {rw add_succ at h},
  exact hd (succ_eq (a + d) (b + d) h),
end

theorem add_eq (a b d : N) : (d + a = d + b) -> (a = b) :=
begin
  intro h,
  rw add_comm d a at h,
  rw add_comm d b at h,
  exact eq_add a b d h,
end

theorem zero_sum (a b : N) : (a + b = 0) -> (a = 0 ∧ b = 0) :=
begin
  intro h,
  cases a,
  cases b,
  split,
  exact zero_eq_zero,
  exact zero_eq_zero,
  exfalso,
  rw zero_eq_zero at h,
  rw zero_add at h,
  apply succ_neq_zero b,
  exact h,
  exfalso,
  rw succ_add at h,
  apply succ_neq_zero (a + b),
  exact h,
end

end N