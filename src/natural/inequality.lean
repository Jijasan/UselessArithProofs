import natural.definition natural.addition natural.multiplication

namespace N

open ordering

def cmp : N -> N -> ordering
| 0 0 := eq
| 0 _ := lt
| _ 0 := gt
| (succ a) (succ b) := cmp a b

instance : has_lt N := ⟨λ a b, cmp a b = lt⟩
instance : has_le N := ⟨λ a b, ¬ b < a⟩

lemma lt_eq (a b : N) : (a < b) -> (cmp a b = lt) :=
begin
  intro h,
  exact h,
end

lemma succ_lt (a b : N) : (succ a < succ b) -> (a < b) :=
begin
  intro h,
  exact h,
end

lemma lt_succ (a b : N) : (a < b) -> (succ a < succ b) :=
begin
  intro h,
  exact h,
end

lemma lt_add (a b d : N) : (a + d < b + d) -> (a < b) :=
begin
  induction d with d hd,
  rw zero_eq_zero,
  repeat {rw add_zero},
  intro h,
  exact h,
  intro h,
  repeat {rw add_succ at h},
  exact hd (succ_lt (a + d) (b + d) h),
end

lemma add_lt (a b d : N) : (d + a < d + b) -> (a < b) :=
begin
  rw add_comm d a,
  rw add_comm d b,
  exact lt_add a b d,
end

lemma lt_add_rev (a b d : N) : (a < b) -> (a + d < b + d) :=
begin
  induction d with d hd,
  rw zero_eq_zero,
  repeat {rw add_zero},
  intro h,
  exact h,
  intro h,
  repeat {rw add_succ},
  exact lt_succ (a + d) (b + d) (hd h),
end

lemma add_lt_rev (a b d : N) : (a < b) -> (d + a < d + b) :=
begin
  intro h,
  have hd := lt_add_rev a b d h,
  rw add_comm d a,
  rw add_comm d b,
  exact hd,
end

theorem lt_mean (a b: N) : (a < b) -> (2 * a < a + b ∧ a + b < 2 * b) :=
begin
  intro h,
  rw two_mul,
  rw two_mul,
  split,
  exact add_lt_rev a b a h,
  exact lt_add_rev a b b h,
end

end N