import natural.definition
import algebra.order.ring

namespace N

def add : N -> N -> N
| a 0 := a
| a (succ b) := succ (add a b)

def pred : N -> N
| 0 := 0
| (succ a) := a

instance : has_add N := ⟨ N.add ⟩ 

def two := succ 1
theorem two_eq_two : two = 2 := rfl

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

def nsmul : ℕ -> N -> N
| 0 b := 0
| (nat.succ a) b := b + nsmul a b

lemma nsmul_zero (b : N) : nsmul 0 b = 0 := rfl
lemma nsmul_succ (a : ℕ) (b : N) : nsmul (nat.succ a) b = b + nsmul a b := rfl

@[simp]
instance : add_comm_monoid N := ⟨ add, add_assoc, 0, zero_add, add_zero, nsmul, nsmul_zero, nsmul_succ, add_comm ⟩ 

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