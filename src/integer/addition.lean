import integer.definition natural.addition

namespace Z

def sub_helper : N -> N -> Z
| 0 0                   := 0
| 0 (N.succ a)          := neg_succ a
| a 0                   := pos a
| (N.succ a) (N.succ b) := sub_helper a b

def add : Z -> Z -> Z
| (pos a) (pos b)           := pos (a + b)
| (pos a) (neg_succ b)      := sub_helper a (b + 1)
| (neg_succ a) (pos b)      := sub_helper b (a + 1)
| (neg_succ a) (neg_succ b) := neg_succ (a + b)

def sub : Z -> Z -> Z
| (pos a) (pos b)           := sub_helper a b
| (pos a) (neg_succ b)      := pos (a + b + 1)
| (neg_succ a) (pos b)      := neg_succ (a + b)
| (neg_succ a) (neg_succ b) := sub_helper b a

def neg : Z -> Z
| (pos 0)          := pos 0
| (pos (N.succ a)) := neg_succ a
| (neg_succ a)     := pos (a + 1)

instance : has_add Z := ⟨ Z.add ⟩ 
instance : has_sub Z := ⟨ Z.sub ⟩ 
instance : has_neg Z := ⟨ Z.neg ⟩

def two := pos (N.succ 1)
theorem two_eq_two : two = 2 := rfl

lemma zero_sub_helper_zero : sub_helper 0 0 = 0 := rfl
lemma zero_sub_helper_succ (a : N) : sub_helper 0 (N.succ a) = neg_succ a := rfl
lemma succ_sub_helper_zero (a : N) : sub_helper (N.succ a) 0 = pos (N.succ a) := rfl
lemma succ_sub_helper_succ (a b : N) : sub_helper (N.succ a) (N.succ b) = sub_helper a b := rfl

lemma pos_sub_pos (a b : N) : (pos a) - (pos b) = sub_helper a b := rfl
lemma pos_sub_neg (a b : N) : (pos a) - (neg_succ b) = pos (a + b + 1) := rfl
lemma neg_sub_pos (a b : N) : (neg_succ a) - (pos b) = neg_succ (a + b) := rfl
lemma neg_sub_neg (a b : N) : (neg_succ a) - (neg_succ b) = sub_helper b a := rfl

lemma neg_zero : neg 0 = 0 := rfl
lemma neg_pos_succ (a : N) : neg (pos (N.succ a)) = neg_succ a := rfl
lemma neg_neg_succ (a : N) : neg (neg_succ a) = pos (a + 1) := rfl

lemma zero_sub (a : Z) : 0 - a = neg a :=
begin
  rw ← zero_eq_zero,
  cases a,
  rw pos_sub_pos,
  rw N.zero_eq_zero,
  cases a,
  rw N.zero_eq_zero,
  rw zero_sub_helper_zero,
  rw ← N.zero_eq_zero,
  rw zero_eq_zero,
  rw neg_zero,
  rw zero_sub_helper_succ,
  rw neg_pos_succ,
  rw pos_sub_neg,
  rw neg_neg_succ,
  rw N.zero_eq_zero,
  rw N.zero_add,
end

lemma sub_helper_eq (a : N) : sub_helper a a = 0 := 
begin
  induction a,
  rw N.zero_eq_zero,
  rw zero_sub_helper_zero,
  rw succ_sub_helper_succ,
  exact a_ih,
end

lemma sub_eq (a : Z) : a - a = 0 :=
begin
  cases a,
  rw pos_sub_pos,
  rw sub_helper_eq,
  rw neg_sub_neg,
  rw sub_helper_eq,
end

lemma neg_succ_sub (a b : N) : (neg_succ a) - (pos b) = neg_succ (a + b) :=
begin
  rw neg_sub_pos,
end

lemma neg_zero_eq_zero : neg 0 = 0 := rfl
lemma neg_pos_eq_neg_pred (a : N) : neg (pos (N.succ a)) = neg_succ a := rfl
lemma neg_succ_eq_neg_succ (a : N) : neg_succ a = neg (pos a)-1 := 
begin
  cases a,
  rw zero_eq_zero,
  rw neg_zero_eq_zero,
  rw zero_sub,
  rw ← one_eq_one,
  rw one,
  rw neg_pos_succ,
  rw N.zero_eq_zero,
  rw neg_pos_succ,
  rw ← one_eq_one,
  rw one,
  rw neg_succ_sub,
  rw N.add_succ,
  rw N.add_zero,
end

def neg_succ_Z (a : Z) := -a-1

lemma neg_succ_Z_eq_neg_succ (a : Z) : neg_succ_Z a = (neg a) - 1 := rfl

theorem double_neg_succ_is_eq (a : Z) : neg_succ_Z (neg_succ_Z a) = a :=
begin
  rw neg_succ_Z_eq_neg_succ,
  rw neg_succ_Z_eq_neg_succ,
  cases a,
  cases a,
  rw zero_eq_zero,
  rw neg_zero,
  rw zero_sub,
  rw ← one_eq_one,
  rw one,
  rw neg_pos_succ,
  rw neg_neg_succ,
  rw N.zero_add,
  rw ← N.one_eq_one,
  rw N.one,
  rw sub_eq,
  rw neg_pos_succ,
  rw ← one_eq_one,
  rw one,
  rw neg_succ_sub,
  rw neg_neg_succ,
  rw pos_sub_pos,
  rw N.add_succ,
  rw N.succ_add,
  rw succ_sub_helper_succ,
  rw N.add_zero,
  rw ← N.one_eq_one,
  rw N.one,
  rw N.add_succ,
  rw succ_sub_helper_zero,
  rw N.add_zero,
  rw neg_neg_succ,
  rw ← one_eq_one,
  rw one,
  rw pos_sub_pos,
  rw ← N.one_eq_one,
  rw N.one,
  rw N.add_succ,
  rw succ_sub_helper_succ,
  rw N.add_zero,
  cases a,
  rw N.zero_eq_zero,
  rw zero_sub_helper_zero,
  rw neg_zero,
  rw zero_sub,
  rw neg_pos_succ,
  rw succ_sub_helper_zero,
  rw neg_pos_succ,
  rw neg_sub_pos,
  rw N.add_succ,
  rw N.add_zero,
end

end Z