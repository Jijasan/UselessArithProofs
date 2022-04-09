import natural.definition natural.addition

namespace N

def mul : N -> N -> N
| a 0 := 0
| a (succ b) := (mul a b) + a

instance : has_mul N := ⟨ mul ⟩ 

lemma mul_zero (a : N) : a * 0 = 0 := rfl
lemma mul_succ (a b : N) : a * (succ b) = a * b + a := rfl

lemma zero_mul (a : N) : 0 * a = 0 :=
begin
  induction a with d hd,
  rw zero_eq_zero,
  rw mul_zero,
  rw mul_succ,
  rw add_zero,
  rw hd,
end

lemma succ_mul (a b : N) : (succ a) * b = a * b + b :=
begin
  induction b with d hd,
  rw zero_eq_zero,
  rw mul_zero,
  rw mul_zero,
  rw add_zero,
  rw mul_succ,
  rw hd,
  rw mul_succ,
  repeat {rw add_succ},
  rw add_assoc,
  rw add_comm d a,
  rw ← add_assoc,
end

theorem mul_left_distrib_add (a b c : N) : a * (b + c) = a * b + a * c :=
begin
  induction a with d hd,
  rw zero_eq_zero,
  repeat {rw zero_mul},
  rw add_zero,
  repeat {rw succ_mul},
  rw hd,
  rw add_assoc (d * b) b (d * c + c),
  rw ← add_assoc b (d * c) c,
  rw add_comm b (d * c),
  repeat {rw ← add_assoc},
end

theorem mul_assoc (a b c : N) : (a * b) * c = a * (b * c) :=
begin
  induction c with d hd,
  rw zero_eq_zero,
  repeat {rw mul_zero},
  rw mul_succ,
  rw hd,
  rw mul_succ,
  rw mul_left_distrib_add,
end

theorem mul_comm (a b : N) : a * b = b * a :=
begin
  induction b with d hd,
  rw zero_eq_zero,
  rw mul_zero,
  rw zero_mul,
  rw mul_succ,
  rw succ_mul,
  rw hd,
end

theorem mul_right_distrib_add (a b c : N) : (a + b) * c = a * c + b * c :=
begin
  rw mul_comm (a + b),
  rw mul_left_distrib_add,
  rw mul_comm c a,
  rw mul_comm c b,
end

lemma mul_one (a : N) : a * 1 = a := 
begin
  rw ← one_eq_one,
  rw one,
  rw mul_succ,
  rw mul_zero,
  rw zero_add,
end

lemma one_mul (a : N) : 1 * a = a :=
begin
  rw mul_comm,
  rw mul_one,
end

theorem mul_one_idemp (a : N) : a * 1 * 1 = a :=
begin
  rw mul_one,
  rw mul_one,
end

end N