import natural.definition

@[derive decidable_eq]
inductive Z
| pos (n : N) : Z
| neg_succ (n : N) : Z

namespace Z

instance : has_zero Z := ⟨ pos N.zero ⟩ 
theorem zero_eq_zero : pos N.zero = 0 := rfl

def one : Z := pos (N.succ 0)

instance : has_one Z := ⟨ Z.one ⟩ 
theorem one_eq_one : one = 1 := rfl

lemma reduce_one : 1 = pos (N.succ 0) := rfl

theorem eq_comm (a b : Z) : (a = b) -> (b = a) :=
begin
  intro h,
  rw h,
end

lemma eq_pos_eq (a b : N) : (a = b) -> (pos a = pos b) := 
begin
  intro h,
  rw h,
end

lemma eq_neg_eq (a b : N) : (a = b) -> (neg_succ a = neg_succ b) :=
begin
  intro h,
  rw h,
end

lemma pos_neq_neg (a b : N) : pos a ≠ neg_succ b :=
begin
  intro h,
  cases h,
end

lemma neg_neq_pos (a b : N) : neg_succ a ≠ pos b :=
begin
  intro h,
  cases h,
end

theorem int1_to_nat (q : Prop) : (∀ (a: Z), q) -> (∀ (b: N), q) :=
begin
  intro h,
  intro a,
  have b := pos a,
  exact h b,
end

theorem int2_to_nat (q : Prop) : (∀ (a b: Z), q) -> (∀ (c d: N), q) :=
begin
  intro h,
  intros a b,
  have c := pos a,
  have d := pos b,
  exact h c d,
end

end Z