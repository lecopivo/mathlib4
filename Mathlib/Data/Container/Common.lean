import Mathlib.Data.Container.Basic

instance (α) [Inhabited α] : Cont (Array α) Nat α :=
{
  toFun := λ arr i => arr.get! i 
}

instance (α) [Inhabited α] : Cont.Active (Array α) :=
{
  active := λ arr i => if i < arr.size then true else false
  finite := sorry
}

-- TODO: Define `Cont.SetActive` that is a `set` on active elements

def NArray (n : Nat) (α : Type u) := { a : Array α // a.size = n }

instance (n α) : Cont (NArray n α) (Fin n) α :=
{
  toFun := λ arr i => arr.1.getLit i.1 arr.2 i.2
}

instance (n α) : Cont.Set (NArray n α) :=
{
  set := λ arr i a=> ⟨arr.1.set ⟨i, sorry⟩ a, sorry⟩
  valid := sorry
}

def ByteNArray (n : Nat) := { a : ByteArray // a.size = n }

instance (n) : Cont (ByteNArray n) (Fin n) UInt8 :=
{
  toFun := λ arr i => arr.1.get ⟨i.1,sorry⟩
}

instance (n) : Cont.Set (ByteNArray n) :=
{
  set := λ arr i c => ⟨arr.1.set ⟨i, sorry⟩ c, sorry⟩
  valid := sorry
}

--- TODO: Add others like FloatNArray, NString, ...

namespace List

  -- Maybe this form is not the nices to prove stuff, I don't know
  -- Also it needs some changes such that we can mutate the element we point at without iterating from start.
  structure Iterator {α} (list : List α) where
    head : α       -- pointer to current value
    tail : List α  -- pointer to the rest
    counter : Fin list.length  -- count how far from start we are for fast comparison
    valid : (list.get counter.1 counter.2 = head) ∧ (list.drop (counter.1+1) = tail)

  theorem counter_eq (l : List α) (i j : Iterator l) 
          : (i = j) ↔ i.counter = j.counter := sorry

  instance (l : List α) (i j : Iterator l) : Decidable (Eq i j) := by rw[counter_eq] infer_instance done

  instance {α} (l : List α) : Iterable (List.Iterator l) :=
  {
    first := match l with
               | [] => none
               | a :: as => some ⟨a, as, ⟨0, sorry⟩, sorry⟩
    next := λ it => match it.tail with
                      | [] => none 
                      | a :: as => some ⟨a, as, ⟨it.counter.1+1, sorry⟩, sorry⟩
    decEq := by infer_instance
  }

  -- How to implement this efficiently? O(1)? 
  -- I want to avoid iterating from the start   
  -- This will probably utilize `Iterator.prev`
  -- Can this be implemented in Lean such that `l` gets mutated in place? (assuming `it` is the only owner of `l`)
  def Iterator.set {l : List α} (it : Iterator l) (a : α) : ((l' : List α) ×' Iterator l') := sorry

  -- TODO: Change the definition of container from `Cont (C ι α : Type)` 
  -- to `Cont {C} (c : C) (ι α : Type) where toFun : ι → α`
  -- Then we can write:
  -- instance (l : List α) : Cont l (Iterator l) α :=
  -- {
  --   toFun := λ it => it.head
  -- }

end List
