import natural.definition natural.addition natural.multiplication natural.equality

namespace N

def le (a b : N) := ∃ c: N, a + c = b

instance : has_le N := ⟨ le ⟩ 

def lt (a b : N) := (a ≤ b) ∧ ¬(a = b)

instance : has_lt N := ⟨ lt ⟩ 

lemma zero_neq_succ (a : N): ¬(0 = succ a) := 
begin
  trivial,
end

lemma succ_neq_zero (a : N): ¬(succ a = 0) := 
begin
  intro h,
  let p := eq_comm (succ a) 0 h,
  apply zero_neq_succ a,
  exact p,
end

lemma zero_le_all (a : N): 0 ≤ a :=
begin
  existsi a,
  rw zero_add,
end

lemma zero_lt_succ (a : N): 0 < succ a :=
begin
  split,
  exact zero_le_all (succ a),
  exact zero_neq_succ a,
end

end N