import natural.addition

universe u

@[derive decidable_eq]
inductive Seq (α : Type u)
| Nil : Seq
| Cons : α -> Seq -> Seq

namespace Seq

def append : Seq N -> Seq N -> Seq N
| Nil a := a
| a Nil := a
| (Cons a as) b := Cons a (append as b)

inductive NatSeq (α : Type u)
| Cons : (N -> α) -> NatSeq

def add (α : Type u) [has_add α] : NatSeq α -> NatSeq α -> NatSeq α
| (NatSeq.Cons f) (NatSeq.Cons g) := NatSeq.Cons (λ x, f x + g x)

end Seq