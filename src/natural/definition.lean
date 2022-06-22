@[derive decidable_eq]
inductive N
| zero : N
| succ (n : N) : N

namespace N

instance : has_zero N := ⟨ N.zero ⟩ 
theorem zero_eq_zero : zero = 0 := rfl

def one : N := succ 0

instance : has_one N := ⟨ N.one ⟩ 
theorem one_eq_one : one = 1 := rfl

theorem eq (a : N) : a = a := rfl

theorem succ_eq (a b : N) : (succ a = succ b) -> (a = b) :=
begin
  intro h,
  cases h,
  refl,
end

theorem eq_succ (a b : N) : (a = b) -> (succ a = succ b) :=
begin
  intro h,
  cases h,
  refl,
end

theorem zero_neq_succ (a : N) : 0 ≠ succ a := 
begin
  intro h,
  cases h,
end

end N