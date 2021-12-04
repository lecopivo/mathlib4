import Mathlib.Data.Table.Basic

structure NDArray (ι : Type u) (α : Type v) [Enumtype ι] where
  (data : Array α)
  (h_size : data.size = numOf ι)

namespace NDArray

  open Enumtype

  variable {α} {ι} [Enumtype ι] (v : NDArray ι α) [Inhabited α]
          
  def lget  (i : Fin (numOf ι)) : α := v.data.get ⟨i.1, by rw [v.h_size]; apply i.2; done⟩ 
  def lget! (i : Nat) : α := v.data.get! i
  def lset  (i : Fin (numOf ι)) (val : α) : NDArray ι α
      := ⟨v.data.set ⟨i.1, by rw [v.h_size]; apply i.2; done⟩ val, sorry⟩
  def lset! (i : Nat) (val : α) : NDArray ι α := ⟨v.data.set! i val, sorry⟩
      
  instance : Table (NDArray ι α) ι α :=
  {
    toFun := λ v index => v.lget (toFin index)
  }

  variable [ForIn Id (Range ι) (ι × Nat)]

  instance instIntroNDArray : Table.Intro (NDArray ι α) :=
  {
    intro := λ f => do
               let mut arr := Array.mkEmpty (numOf ι)
               for (i,li) in fullRange ι do
                 arr := arr.push (f i)
               ⟨arr, sorry⟩
    valid := sorry
  }

  -- to get `v.map` notation
  -- TODO: Why do I have to assign the class manually? 
  -- BUD:  I think it might be potentially a bug.
  abbrev intro (f : ι → α) : NDArray ι α := Table.intro f

  instance : Table.Set (NDArray ι α) := 
  {
    set := λ v index val => v.lset (toFin index) val
    valid := sorry
  }

  -- to get `v.set` notation
  abbrev set (v : NDArray ι α) (id val) := Table.set v id val

  instance instMapIdxNDArray : Table.MapIdx (NDArray ι α) := 
  {
    mapIdx := λ f v₀ => do
                let mut v := v₀
                for (i,li) in fullRange ι do
                  v := v.lset! li (f i (v.lget! li))
                v
    valid := sorry
  }

  -- to get `v.map` notation
  abbrev mapIdx (f : ι → α → α) (v : NDArray ι α) : NDArray ι α := Table.mapIdx f v

  instance : Table.Map (NDArray ι α) := 
  {
    map := λ f v => mapIdx (λ _ x => f x) v
    valid := sorry
  }

  abbrev map (f : α → α) (v : NDArray ι α) : NDArray ι α := Table.map f v

  --- Specialized ForIn because we can use linear index to access elements 
  --- This saves us the conversion from structured index to linear
  open Enumtype Table in
  instance {m} [Monad m] 
           [Enumtype ι] [ForIn m (Range ι) (ι × Nat)]
           : ForIn m (NDArray ι α) (α × ι × Nat) :=
  {
    forIn := λ v init f => do
      let mut val := init
      for (i,li) in fullRange ι do
        -- Here we are using linear index to acces the table
        -- Not sure if it is worth it ... 
        match (← f (v.lget ⟨li,sorry⟩, i, li) val) with
          | ForInStep.done d => return d
          | ForInStep.yield d => val ← d
      pure init
  }
 
end NDArray



section Examples

  abbrev Vector (n : Nat) := NDArray (Fin n) Float
  abbrev Matrix (n m : Nat) := NDArray (Fin n × Fin m) Float
  abbrev RowMatrix (n m : Nat) := NDArray (Fin n × Fin m) Float
  abbrev ColMatrix (n m : Nat) := NDArray (Fin n ×ₗ Fin m) Float

  -- TODO: Define tensor with notation `Tensor [n1,n2,n3]`
  -- @[reducible]
  -- abbrev Tensor.indexOf (l : List Nat) :=
  --   match l with
  --     | [] => Fin 0
  --     | [n] => Fin n
  --     | n::ns => Fin n × (indexOf ns)
  -- instance (l : List Nat) : Enumtype (Tensor.indexOf l) := HOW TO DO THIS??
  -- abbrev Tensor (dims : List Nat) := NDArray (Tensor.indexOf dims)

  instance : ToString (Vector n) :=
    ⟨λ v => do
       let mut str := "("
       for (vi,i,li) in v do
         str := str ++ toString vi ++ " "
       str := str ++ ")\n"
       str⟩

  instance : ToString (Matrix n m) :=
    ⟨λ A => do
       let mut str := ""
       for i in Iterable.fullRange (Fin n) do
         str := str ++ "("
         for j in Iterable.fullRange (Fin m) do
           str := str ++ s!"{A[i,j]} "
         str := str ++ s!")\n"
       str⟩

  open Table
  open Enumtype

  #eval ((do 
    let mut m : Matrix 4 4 := intro λ (i,j) => j.1.toFloat
    let mut v : Vector 4 := intro λ i : Fin 4 => i.1.toFloat

    IO.println m
    IO.println v

    for (i,li) in allIdx v do
      v := set v i (2 * v[i])

    IO.println v

    for (i, li) in allIdx m do
      m := set m i li.toFloat

    -- By default we do not execute the multiplication but just build and expression
    let u1 := m*v -- : Fin ↦ ℝ 
    let u2 : Vector 4 := m*v
    let u : Vector 4 := table i => ∑ j, m[i,j]*v[j]

    IO.println s!"m*v:\n {u}"

    -- I want notation: 
    -- for (a, i, li) in m do
    --   a := f i

    -- !!! This is a trap !!!
    -- It does not change `m`!
    -- for (a, i, li) in m do
    --   m := set m i (li.toFloat : ℝ) 

    IO.print m
  ) : IO Unit)

end Examples
