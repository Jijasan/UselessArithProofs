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