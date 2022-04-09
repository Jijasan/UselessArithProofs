import natural.definition natural.add

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

end N