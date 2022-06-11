import integer.definition natural.addition tactic.nth_rewrite natural.equality

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
| (neg_succ a) (neg_succ b) := neg_succ (a + b + 1)

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

lemma pos_add_pos (a b : N) : (pos a) + (pos b) = pos (a + b) := rfl
lemma pos_add_neg (a b : N) : (pos a) + (neg_succ b) = sub_helper a (b + 1) := rfl
lemma neg_add_pos (a b : N) : (neg_succ a) + (pos b) = sub_helper b (a + 1) := rfl
lemma neg_add_neg (a b : N) : (neg_succ a) + (neg_succ b) = neg_succ (a + b + 1) := rfl

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

lemma zero_sub_helper_eq_r (a : N) : (sub_helper 0 a = 0) -> (a = 0) := 
begin
  intro h,
  cases a,
  rw N.zero_eq_zero,
  exfalso,
  rw zero_sub_helper_succ at h,
  cases h,
end

lemma zero_sub_helper_eq_l (a : N) : (sub_helper a 0 = 0) -> (a = 0) := 
begin
  intro h,
  cases a,
  rw N.zero_eq_zero,
  exfalso,
  rw succ_sub_helper_zero at h,
  cases h,
end

lemma zero_sub_helper_eq : ∀ a b : N, (sub_helper a b = 0) -> (a = b)
| 0 0 := 
begin
  intro h,
  refl,
end
| 0 (N.succ a) := 
begin
  intro h,
  exfalso,
  have s := zero_sub_helper_eq_r (N.succ a) h,
  cases h,
end
| (N.succ a) 0 := 
begin
  intro h,
  exfalso,
  have s := zero_sub_helper_eq_l (N.succ a) h,
  cases h,
end
| (N.succ a) (N.succ b) := 
begin
  intro h,
  rw succ_sub_helper_succ at h,
  have q := zero_sub_helper_eq a b h,
  exact (N.eq_succ a b q),
end

lemma pos_eq_pos (a b : N) : (pos a = pos b) -> a = b :=
begin
  intro h,
  have s := sub_eq (pos a),
  nth_rewrite 1 h at s,
  rw pos_sub_pos at s,
  exact (zero_sub_helper_eq a b s),
end

lemma neg_eq_neg (a b : N) : (neg_succ a = neg_succ b) -> (a = b) :=
begin
  intro h,
  have s := sub_eq (neg_succ a),
  nth_rewrite 1 h at s,
  rw neg_sub_neg at s,
  have t := zero_sub_helper_eq b a s,
  rw t,
end

lemma neg_succ_sub (a b : N) : (neg_succ a) - (pos b) = neg_succ (a + b) :=
begin
  rw neg_sub_pos,
end

lemma neg_succ_eq_neg_succ (a : N) : neg_succ a = neg (pos a)-1 := 
begin
  cases a,
  rw zero_eq_zero,
  rw neg_zero,
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

lemma zero_add (a : Z) : 0 + a = a :=
begin
  rw ← zero_eq_zero,
  cases a,
  rw pos_add_pos,
  rw N.zero_eq_zero,
  rw N.zero_add,
  rw pos_add_neg,
  rw ← N.one_eq_one,
  rw N.one,
  rw N.add_succ,
  rw N.add_zero,
  rw N.zero_eq_zero,
  rw zero_sub_helper_succ,
end

lemma succ_eq_inc (a : N) : pos (N.succ a) = pos a + 1 := begin
  rw ← one_eq_one,
  rw one,
  rw pos_add_pos,
  rw N.add_succ,
  rw N.add_zero,
end

lemma succ_eq_inc_l (a : N) : pos (N.succ a) = 1 + pos a :=
begin
  rw ← one_eq_one,
  rw one,
  rw pos_add_pos,
  rw N.succ_add,
  rw N.zero_add,
end

lemma left_add_one_eq (a b : Z) : (1 + a = 1 + b) -> (a = b) :=
begin
  intro h,
  cases a,
  cases b,
  rw ← one_eq_one at h,
  rw one at h,
  repeat {rw pos_add_pos at h},
  have q := pos_eq_pos (N.succ 0 + a) (N.succ 0 + b) h,
  have t := N.add_eq a b (N.succ 0) q,
  exact (eq_pos_eq a b t),
  rw ← one_eq_one at h, rw one at h,
  rw pos_add_pos at h,
  rw N.succ_add at h,
  rw N.zero_add at h,
  rw pos_add_neg at h,
  rw ← N.one_eq_one at h, rw N.one at h,
  rw N.add_succ at h,
  rw N.add_zero at h,
  rw succ_sub_helper_succ at h,
  cases b,
  rw N.zero_eq_zero at h,
  rw zero_sub_helper_zero at h,
  rw ← zero_eq_zero at h,
  have q := pos_eq_pos (N.succ a) (N.zero) h,
  exfalso,
  rw N.zero_eq_zero at q,
  have t := N.eq_comm (N.succ a) 0 q,
  exact (N.zero_neq_succ a t),
  rw zero_sub_helper_succ at h,
  exfalso,
  exact (pos_neq_neg (N.succ a) b h),
  cases b,
  rw ← one_eq_one at h, rw one at h,
  rw pos_add_pos at h,
  rw N.succ_add at h,
  rw N.zero_add at h,
  rw pos_add_neg at h,
  rw ← N.one_eq_one at h, rw N.one at h,
  rw N.add_succ at h,
  rw N.add_zero at h,
  rw succ_sub_helper_succ at h,
  cases a,
  rw N.zero_eq_zero at h,
  rw zero_sub_helper_zero at h,
  rw ← zero_eq_zero at h,
  rw N.zero_eq_zero at h,
  have q := pos_eq_pos 0 (N.succ b) h,
  exfalso,
  exact (N.zero_neq_succ b q),
  rw zero_sub_helper_succ at h,
  exfalso,
  exact (neg_neq_pos a (N.succ b) h),
  rw ← one_eq_one at h, rw one at h,
  repeat {rw pos_add_neg at h},
  rw ← N.one_eq_one at h, rw N.one at h,
  repeat {rw N.add_succ at h,rw N.add_zero at h},
  repeat {rw succ_sub_helper_succ at h},
  cases a,
  rw N.zero_eq_zero at h,
  rw zero_sub_helper_zero at h,
  cases b,
  refl,
  rw zero_sub_helper_succ at h,
  exfalso,
  exact (pos_neq_neg 0 b h),
  rw zero_sub_helper_succ at h,
  cases b,
  rw N.zero_eq_zero at h,
  rw zero_sub_helper_zero at h,
  exfalso,
  exact (neg_neq_pos a 0 h),
  rw zero_sub_helper_succ at h,
  have t := neg_eq_neg a b h,
  exact (eq_neg_eq (N.succ a) (N.succ b) (N.eq_succ a b t)),
end

theorem add_eq (a b d : Z) : (d + a = d + b) -> (a = b) :=
begin
  intro h,
  cases d,
  induction d,
  rw zero_eq_zero at h,
  rw zero_add at h,
  rw zero_add at h,
  exact h,
end

theorem add_assoc (a b c : Z) : a + b + c = a + (b + c) :=
begin
  cases a,
  induction a,
  rw zero_eq_zero,
  rw zero_add,
  rw zero_add,
  rw succ_eq_inc_l,
end

end Z