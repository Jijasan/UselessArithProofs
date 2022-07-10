import natural.definition natural.addition natural.equality

def z_rel (a b : N × N) := a.1 + b.2 = a.2 + b.1
def Z' : Type := quot z_rel

namespace Z'

def reflex : reflexive z_rel := begin 
  intro h,
  rw z_rel,
  rw N.add_comm,
end
def symmet : symmetric z_rel := begin
  intro x,
  intro y,
  intro h,
  rw z_rel,
  rw z_rel at h,
  rw N.add_comm at h,
  rw h,
  rw N.add_comm,
end
def trans : transitive z_rel := begin
  intros x y z,
  repeat {rw z_rel},
  intro p,
  intro q,
  rw ← N.eq_add _ _ z.fst at p,
  rw N.add_assoc at p,
  rw ← q at p,
  rw N.add_assoc x.snd _ _ at p,
  repeat {rw N.add_comm y.fst _ at p},
  repeat {rw ← N.add_assoc at p},
  rw N.eq_add _ _ y.fst at p,
  exact p,
end

instance : setoid (N × N) := ⟨ z_rel, ⟨ reflex, symmet, trans ⟩ ⟩ 

def one : Z' := ⟦(1, 0)⟧
instance : has_one Z' := ⟨ one ⟩ 

def zero : Z' := ⟦(0, 0)⟧
instance : has_zero Z' := ⟨ zero ⟩ 

lemma zero_eq_zero : 0 = zero := rfl

end Z'