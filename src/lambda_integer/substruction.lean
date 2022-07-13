import lambda_integer.definition lambda_integer.addition natural.addition natural.definition

namespace Z'

def neg (a : Z') : Z' := ⟦(a.norm.snd, a.norm.fst)⟧

instance : has_neg Z' := ⟨ neg ⟩

lemma neg_deconstruct (a : Z') : neg a = -a := rfl
lemma neg_pair (a b : N) : neg ⟦(a, b)⟧ = ⟦(b, a)⟧ := begin
  rw neg,
  rw norm_deconstruction,
  rw ← eqq_symm,
  rw ← norm_deconstruction,
  rw norm_eq_a,
end

def sub (a b : Z') : Z' := a + (-b)

instance : has_sub Z' := ⟨ sub ⟩ 

lemma sub_eq_add_neg (a b : Z') : a - b = a + -b := rfl

lemma add_left_neg (a : Z') : -a + a = 0 := begin
  rw ← neg_deconstruct, rw neg,
  rw add_deconstruct,
  have q := norm_cont_zero a,
  cases q,
  rw q,
  rw norm_deconstruction,
  rw eqq_a_0,
  rw fst_eq,
  rw snd_eq _ 0,
  rw ← norm_eq_a ⟦(a.norm.snd + 0, a.norm.snd + 0)⟧,
  rw norm_deconstruction,
  rw eqq_a_a,
  rw ← zero,
  rw zero_eq_zero,
  rw q,
  rw norm_deconstruction,
  rw eqq_0_a,
  rw fst_eq,
  rw snd_eq,
  rw ← norm_eq_a ⟦(0 + a.norm.fst, 0 + a.norm.fst)⟧,
  rw norm_deconstruction,
  rw eqq_a_a,
  rw ← zero,
  rw zero_eq_zero,
end

def int_cast: ℤ -> Z'
| (int.of_nat a) := ⟦(N.nat_cast a, 0)⟧
| (int.neg_succ_of_nat a) := ⟦(0, N.nat_cast (a.succ))⟧

lemma int_cast_of_nat (a : ℕ) : int_cast (int.of_nat a) = nat_cast a := rfl
lemma int_cast_neg_succ_of_nat (a : ℕ) : int_cast (int.neg_succ_of_nat a) = -(nat_cast (a + 1)) := begin
  rw int_cast,
  rw ← neg_deconstruct,
  rw nat_cast,
  rw neg,
  rw norm_deconstruction,
  rw eqq_a_0,
end
lemma int_cast_zero : int_cast 0 = 0 := rfl

end Z'