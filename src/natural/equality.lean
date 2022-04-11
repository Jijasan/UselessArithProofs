import natural.addition natural.definition natural.multiplication

namespace N

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

end N