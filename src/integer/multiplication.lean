import integer.definition natural.addition natural.equality natural.multiplication

namespace Z

def mul : Z -> Z -> Z
| (pos a) (pos b) := pos (a * b)
| (neg_succ _) (pos 0) := pos 0
| (neg_succ a) (pos b) := neg_succ (N.pred ((a + 1) * b))
| (pos 0) (neg_succ _) := pos 0
| (pos a) (neg_succ b) := neg_succ (N.pred (a * (b + 1)))
| (neg_succ a) (neg_succ b) := neg_succ (N.pred ((a + 1) * (b + 1)))

instance : has_mul Z := ⟨ mul ⟩ 

lemma pos_mul_pos (a b : N) : mul (pos a) (pos b) = pos (a * b) := by rw [mul]

end Z