import natural.definition natural.addition natural.multiplication
import lambda_integer.definition lambda_integer.addition lambda_integer.substruction

namespace Z'

def mul (a b : Z'): Z' := ⟦((norm a).fst * (norm b).fst + (norm a).snd * (norm b).snd, (norm a).fst * (norm b).snd + (norm a).snd * (norm b).fst)⟧

instance : has_mul Z' := ⟨ mul ⟩

lemma mul_deconstruct (a b : Z'): a * b = ⟦((norm a).fst * (norm b).fst + (norm a).snd * (norm b).snd, (norm a).fst * (norm b).snd + (norm a).snd * (norm b).fst)⟧ := rfl

def pair_mul (a b : N × N) : N × N := (a.fst * b.fst + a.snd * b.snd, a.fst * b.snd + a.snd * b.fst)

instance : has_mul (N × N) := ⟨ pair_mul ⟩

lemma pair_mul_deconstruct (a b : N × N) : a * b = (a.fst * b.fst + a.snd * b.snd, a.fst * b.snd + a.snd * b.fst) := rfl

theorem mul_zero (a : Z') : a * 0 = 0 := begin
  rw mul_deconstruct,
  rw zero_norm,
  rw fst_eq 0,
  rw snd_eq 0 0,
  repeat {rw N.mul_zero},
  rw N.zero_add,
  rw zero_eq_zero, rw zero,
end

theorem zero_mul (a: Z') : 0 * a = 0 := begin
  rw mul_deconstruct,
  rw zero_norm,
  rw fst_eq 0,
  rw snd_eq 0 0,
  repeat {rw N.zero_mul},
  rw N.zero_add,
  rw zero_eq_zero, rw zero,
end

theorem mul_comm (a b : Z') : a * b = b * a := begin
  repeat {rw mul_deconstruct},
  repeat {rw N.mul_comm a.norm.fst},
  repeat {rw N.mul_comm a.norm.snd},
  rw N.add_comm (b.norm.fst * a.norm.snd),
end

theorem one_mul (a : Z') : 1 * a = a := begin
  rw mul_deconstruct,
  rw one_norm,
  rw fst_eq 1 0,
  rw snd_eq 1 0,
  repeat {rw N.one_mul},
  repeat {rw N.zero_mul},
  repeat {rw N.add_zero},
  rw a_norm_eq_a,
end

theorem mul_one (a : Z') : a * 1 = a := begin
  rw mul_comm,
  exact one_mul a,
end

instance : has_mul (quot z_rel) := ⟨ mul ⟩

lemma mul_neg_eqq: ∀ (b c d : N), (0, b) * (eqq (c, d)) = eqq (b * d, b * c)
| b 0 d := begin
  rw eqq_0_a,
  rw N.mul_zero,
  rw eqq_a_0,
  rw pair_mul_deconstruct,
  repeat {rw fst_eq},
  repeat {rw snd_eq},
  repeat {rw N.mul_zero},
  rw N.zero_mul,
  repeat {rw N.zero_add},
end
| b c 0 := begin
  rw eqq_a_0,
  rw N.mul_zero,
  rw eqq_0_a,
  rw pair_mul_deconstruct,
  repeat {rw fst_eq},
  repeat {rw snd_eq},
  repeat {rw N.zero_mul},
  rw N.mul_zero,
  repeat {rw N.zero_add},
end
| b (N.succ c) (N.succ d) := begin
  rw eqq_succ_succ,
  repeat {rw N.mul_succ},
  rw eqq_plus_right _ _ _,
  exact mul_neg_eqq _ _ _,
end

lemma mul_pos_eqq: ∀ (a c d : N), (a, 0) * (eqq (c, d)) = eqq (a * c, a * d)
| a 0 d := begin
  rw N.mul_zero,
  repeat {rw eqq_0_a},
  rw pair_mul_deconstruct,
  repeat {rw fst_eq},
  repeat {rw snd_eq},
  repeat {rw N.zero_mul},
  rw N.mul_zero,
  repeat {rw N.add_zero},
end
| a c 0 := begin
  rw N.mul_zero,
  repeat {rw eqq_a_0},
  rw pair_mul_deconstruct,
  repeat {rw fst_eq},
  repeat {rw snd_eq},
  repeat {rw N.mul_zero},
  rw N.zero_mul,
  repeat {rw N.add_zero},
end
| a (N.succ c) (N.succ d) := begin
  rw eqq_succ_succ,
  repeat {rw N.mul_succ},
  rw eqq_plus_right,
  exact mul_pos_eqq _ _ _,
end

lemma eqq_mul: ∀ (a b c d : N), eqq ((a, b) * (c, d)) = (eqq (a, b)) * (eqq (c, d)) 
| 0 b c d := begin
  rw eqq_0_a,
  rw pair_mul_deconstruct,
  repeat {rw fst_eq},
  repeat {rw snd_eq},
  repeat {rw N.zero_mul},
  repeat {rw N.zero_add},
  rw mul_neg_eqq _ _ _,
end
| a 0 c d := begin
  rw eqq_a_0,
  rw pair_mul_deconstruct,
  repeat {rw fst_eq},
  repeat {rw snd_eq},
  repeat {rw N.zero_mul},
  repeat {rw N.add_zero},
  rw mul_pos_eqq _ _ _,
end
| (N.succ a) (N.succ b) c d := begin
  rw eqq_succ_succ,
  rw pair_mul_deconstruct,
  repeat {rw fst_eq},
  repeat {rw snd_eq},
  repeat {rw N.succ_mul},
  rw N.add_assoc (a * c) c _,
  rw N.add_comm c _,
  rw ← N.add_assoc (a * c) _ _,
  rw ← N.add_assoc (a * d + d) _ _,
  rw eqq_plus_right,
  rw ← N.add_assoc,
  rw N.add_assoc (a * d) _ _,
  rw N.add_comm d _,
  rw ← N.add_assoc,
  rw eqq_plus_right,
  rw ← fst_eq a b,
  rw ← fst_eq c d,
  rw ← snd_eq a b,
  rw ← snd_eq c d,
  rw ← pair_mul_deconstruct,
  repeat {rw fst_eq},
  repeat {rw snd_eq},
  exact eqq_mul a b c d,
end

lemma mul_distrib (a b : N × N): quot.mk z_rel a * quot.mk z_rel b = quot.mk z_rel (a * b) := begin
  rw mul_deconstruct,
  rw ← pair_mul_deconstruct,
  cases a,
  cases b,
  repeat {rw ← paren_eq_mk},
  repeat {rw norm_deconstruction},
  rw ← eqq_mul,
  cases ((a_fst, a_snd) * (b_fst, b_snd)),
  rw ← norm_deconstruction,
  rw norm_eq_a,
end

lemma pair_mul_assoc (a b c : N × N) : (a * b) * c = a * (b * c) := begin
  repeat {rw pair_mul_deconstruct},
  cases a,
  cases b,
  cases c,
  repeat {rw fst_eq},
  repeat {rw snd_eq},
  repeat {rw N.mul_left_distrib_add},
  repeat {rw N.mul_right_distrib_add},
  repeat {rw N.mul_assoc},
  repeat {rw N.add_assoc},
  rw N.add_comm (a_snd * (b_snd * c_fst)) _,
  rw N.add_comm (a_snd * (b_snd * c_snd)) _,
  repeat {rw N.add_assoc},
end

theorem mul_assoc (a b c : Z') : (a * b) * c = a * (b * c) := begin
  rw ← a_norm_eq_a a,
  rw ← a_norm_eq_a b,
  rw ← a_norm_eq_a c,
  repeat {rw paren_eq_mk},
  repeat {rw mul_distrib},
  rw pair_mul_assoc,
end

theorem left_distrib (a b c : Z') : a * (b + c) = a * b + a * c := begin
  rw ← a_norm_eq_a a,
  rw ← a_norm_eq_a b,
  rw ← a_norm_eq_a c,
  repeat {rw paren_eq_mk},
  repeat {rw mul_distrib},
  repeat {rw add_distrib},
  rw pair_add_deconstruction,
  rw mul_distrib,
  rw pair_mul_deconstruct,
  rw fst_eq (b.norm.fst + c.norm.fst) (b.norm.snd + c.norm.snd),
  rw snd_eq (b.norm.fst + c.norm.fst) (b.norm.snd + c.norm.snd),
  repeat {rw pair_mul_deconstruct},
  rw fst_eq a.norm.fst a.norm.snd,
  rw snd_eq a.norm.fst a.norm.snd,
  rw fst_eq b.norm.fst b.norm.snd,
  rw snd_eq b.norm.fst b.norm.snd,
  rw fst_eq c.norm.fst c.norm.snd,
  rw snd_eq c.norm.fst c.norm.snd,
  rw pair_add_deconstruction,
  repeat {rw N.add_assoc},
  rw ← N.add_assoc (a.norm.snd * b.norm.snd) _ _,
  rw N.add_comm (a.norm.snd * b.norm.snd) _,
  rw ← N.add_assoc (a.norm.snd * b.norm.fst) _ _,
  rw N.add_comm (a.norm.snd * b.norm.fst) _,
  repeat {rw N.add_assoc},
  rw ← N.add_assoc (a.norm.fst * b.norm.fst) _ _,
  rw ← N.add_assoc (a.norm.fst * b.norm.snd) _ _,
  repeat {rw N.mul_left_distrib_add},
end

theorem right_distrib (a b c : Z') : (a + b) * c = a * c + b * c := begin
  rw mul_comm (a + b) _,
  rw left_distrib,
  repeat {rw mul_comm c _},
end

lemma n_mul_norm_fst (a : N) (b : Z') : a * b.norm.fst = ((fromN a) * b).norm.fst := begin
  rw fromN,
  rw mul_deconstruct,
  rw norm_deconstruction a 0,
  rw eqq_a_0,
  rw fst_eq a 0,
  rw snd_eq a 0,
  repeat {rw N.zero_mul},
  repeat {rw N.add_zero},
  have q := norm_cont_zero b,
  cases q,
  rw q,
  rw N.mul_zero,
  rw norm_deconstruction,
  rw eqq_0_a,
  rw q,
  rw N.mul_zero,
  rw norm_deconstruction,
  rw eqq_a_0,
end

lemma n_mul_norm_snd (a : N) (b : Z') : a * b.norm.snd = ((fromN a) * b).norm.snd := begin
  rw fromN,
  rw mul_deconstruct,
  rw norm_deconstruction a 0,
  rw eqq_a_0,
  rw fst_eq a 0,
  rw snd_eq a 0,
  repeat {rw N.zero_mul},
  repeat {rw N.add_zero},
  have q := norm_cont_zero b,
  cases q,
  rw q,
  rw N.mul_zero,
  rw norm_deconstruction,
  rw eqq_0_a,
  rw q,
  rw N.mul_zero,
  rw norm_deconstruction,
  rw eqq_a_0,
end

private lemma neg_distrib_left_helper (a b c d : N) : neg (⟦(a, b)⟧ * ⟦(c, d)⟧) = (neg ⟦(a, b)⟧) * ⟦(c, d)⟧ := begin
  rw neg_pair,
  rw mul_deconstruct,
  rw neg_pair,
  rw norm_symm b a,
  rw fst_eq,
  rw snd_eq ((norm ⟦(b, a)⟧).snd) ((norm ⟦(b, a)⟧).fst),
  rw N.add_comm (((norm ⟦(b, a)⟧).snd) * ((norm ⟦(c, d)⟧).snd)) _,
  rw N.add_comm ((norm ⟦(b, a)⟧).snd * (norm ⟦(c, d)⟧).fst) _,
  rw ← mul_deconstruct,
end

lemma neg_distrib_left (a b : Z') : neg (a * b) = (neg a) * b := begin
  rw ← a_norm_eq_a a,
  rw ← a_norm_eq_a b,
  exact neg_distrib_left_helper _ _ _ _,
end

def zsmul (a : ℤ) (b : Z') : Z' := (int_cast a) * b
lemma zsmul_zero (b : Z') : zsmul 0 b = 0 := begin
  rw zsmul,
  rw int_cast_zero,
  rw zero_mul,
end
lemma zsmul_succ (a : ℕ) (b : Z') : zsmul (int.of_nat (a.succ)) b = b + zsmul (int.of_nat a) b := begin
  repeat {rw zsmul},
  rw int_cast,
  rw mul_deconstruct,
  rw norm_deconstruction,
  rw eqq_a_0,
  rw fst_eq,
  rw snd_eq _ 0,
  repeat {rw N.zero_mul},
  repeat {rw N.add_zero},
  rw N.nat_cast,
  repeat {rw N.succ_mul},
  rw N.add_comm _ b.norm.snd,
  rw n_mul_norm_fst,
  rw n_mul_norm_snd,
  rw ← add_deconstruct,
  rw add_comm,
  rw fromN,
  rw int_cast,
end
lemma zsmul_neg (a : ℕ) (b : Z') : zsmul (int.neg_succ_of_nat a) b = -zsmul (int.of_nat (a.succ)) b := begin
  repeat {rw zsmul},
  repeat {rw int_cast},
  rw ← neg_deconstruct,
  rw neg_distrib_left,
  rw neg_pair,
end

def npow: ∀ (a : ℕ) (b : Z'), Z'
| 0 b := 1
| (nat.succ a) b := b * (npow a b)

lemma npow_zero (b : Z') : npow 0 b = 1 := rfl
lemma npow_succ (a : ℕ) (b : Z') : npow (a.succ) b = b * (npow a b) := rfl

instance : comm_ring Z' := ⟨ add, add_assoc, zero, zero_add, add_zero, nsmul, nsmul_zero, nsmul_succ, neg, sub, sub_eq_add_neg, zsmul, zsmul_zero, zsmul_succ, zsmul_neg, add_left_neg, add_comm, mul, mul_assoc, one, one_mul, mul_one, npow, npow_zero, npow_succ, left_distrib, right_distrib, mul_comm, ⟩

end Z'