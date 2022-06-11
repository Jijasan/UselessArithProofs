import natural.addition

universe u

@[derive decidable_eq]
inductive Seq (α : Type u)
| Nil : Seq
| Cons : α -> Seq -> Seq

namespace Seq

def add : Seq N -> Seq N -> Seq N
| (Nil N) a := a
| a (Nil N) := a
| (Cons a as) (Cons b bs) := Cons (a + b) (add as bs)

end Seq