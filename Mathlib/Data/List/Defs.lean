/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Lean
import Mathlib.Init.Data.Nat.Basic

/-!
## Definitions on lists

This file contains various definitions on lists. It does not contain
proofs about these definitions, those are contained in other files in `data/list`.
-/

variable {α β : Type _}

namespace List

/-- Given a function `f : ℕ → α → β` and `as : list α`, `as = [a₀, a₁, ...]`, returns the list
`[f 0 a₀, f 1 a₁, ...]`. -/
def mapWithIndex (f : ℕ → α → β) (as : List α) : List β :=
  let rec loop : ℕ → List α → List β
  | _,  [] => return []
  | n, a :: as => f n a :: loop (n + 1) as
  loop 0 as

/-- Applicative variant of `mapWithIndex`. -/
def mmapWithIndex {m : Type v → Type w} [Applicative m] (f : ℕ → α → m β) (as : List α) :
  m (List β) :=
  let rec loop : ℕ → List α → m (List β)
  | _,  [] => return []
  | n, a :: as => List.cons <$> f n a <*> loop (n + 1) as
  loop 0 as

end List
