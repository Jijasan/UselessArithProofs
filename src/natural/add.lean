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

end N