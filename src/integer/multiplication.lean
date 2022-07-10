import integer.definition natural.addition natural.equality natural.multiplication

namespace Z

def mul : Z -> Z -> Z
| 0 _ := 0
| _ 0 := 0
| (pos (N.succ a)) (pos (N.succ b)) := pos ((a + 1) * (b + 1))
| (neg_succ a) (pos (N.succ b)) := neg_succ (N.pred ((a + 1) * (b + 1)))
| (pos (N.succ a)) (neg_succ b) := neg_succ (N.pred ((a + 1) * (b + 1)))
| (neg_succ a) (neg_succ b) := neg_succ (N.pred ((a + 1) * (b + 1)))

instance : has_mul Z := ⟨ mul ⟩ 

lemma zero_mul (a : Z) : 0 * a = 0 := rfl
lemma pos_succ_mul_pos_succ (a b : N) : mul (pos (N.succ a)) (pos (N.succ b)) = pos ((a + 1) * (b + 1)) := rfl
lemma 

lemma pos_mul_pos (a b : N) : mul (pos a) (pos b) = pos (a * b) := begin

end

end Z