import natural.definition

namespace N

def add : N -> N -> N
| a 0 := a
| a (succ b) := succ (add a b)

instance : has_add N := ⟨ N.add ⟩ 

lemma add_zero (a : N) : a + 0 = a := rfl
lemma add_succ (a b : N) : a + succ b = succ (a + b) := rfl

lemma zero_add (a : N) : 0 + a = a :=
begin
  induction a with d hd,
  rw zero_eq_zero,
  rw add_zero 0,
  rw add_succ,
  rw hd,
end

lemma succ_add (a b : N) : (succ a) + b = succ (a + b) :=
begin
  induction b with d hd,
  rw zero_eq_zero,
  rw add_zero,
  rw add_zero,
  rw add_succ,
  rw add_succ,
  rw hd,
end

theorem add_assoc (a b c : N) : (a + b) + c = a + (b + c) :=
begin
  induction c with d hd,
  rw zero_eq_zero,
  rw add_zero,
  rw add_zero,
  rw add_succ,
  rw add_succ,
  rw add_succ,
  rw hd,
end

theorem add_comm (a b : N) : a + b = b + a :=
begin 
  induction b with d hd,
  rw zero_eq_zero,
  rw add_zero,
  rw zero_add,
  rw succ_add,
  rw add_succ,
  rw hd,
end

lemma succ_eq_inc (a : N) : succ a = a + 1 :=
begin
  rw ← add_zero a,
  rw ← add_succ,
  rw add_assoc,
  rw zero_add,
  rw ← one_eq_one,
  rw one,
end

end N