@[derive decidable_eq]
inductive N
| zero : N
| succ (n : N) : N

namespace N

instance : has_zero N := ⟨ N.zero ⟩ 
theorem zero_eq_zero : zero = 0 := rfl

def one : N := succ 0

instance : has_one N := ⟨ N.one ⟩ 

theorem succ_eq (a b : N) : succ a = succ b -> a = b :=
begin
  intro h,
  cases h,
  refl,
end

end N