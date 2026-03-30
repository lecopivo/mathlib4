module

public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic



@[expose] public section

open Filter Topology

----------------------------------------------------------------------------------------------------
-- Setup  ------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

attribute [fun_prop out l₂] Tendsto

theorem tendsto_fun_id {x : Filter α} : Tendsto (fun x : α => x) x x :=
  le_refl x

theorem Tendsto.congr_l₂ {f : α → β} {l₁ : Filter α} {l₂ l₂' : Filter β}
  (t : Tendsto f l₁ l₂) (h : l₂' = l₂) : Tendsto f l₁ l₂' := h ▸ t

theorem Tendsto.comp' {f : α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ}
    (hf : Tendsto f x y) (hg : Tendsto g y z) : Tendsto (g ∘ f) x z := fun _ hs => hf (hg hs)

theorem tendsto_apply {ι : Type*} {α : ι → Type*} (f : ∀ i, Filter (α i)) (i : ι) :
    Tendsto (fun (f : (i : ι) → α i) => f i) (Filter.pi f) (f i) := by apply tendsto_eval_pi

alias ⟨_, tendsto_pi''⟩ := tendsto_pi

-- lambda theorems
attribute [fun_prop]
  tendsto_fun_id
  tendsto_const_nhds
  Tendsto.comp'
  tendsto_pi''
  tendsto_apply

-- product theorems
attribute [fun_prop]
  Tendsto.prodMk
  tendsto_fst
  Tendsto.fst
  Tendsto.fst_nhds
  tendsto_snd
  Tendsto.snd
  Tendsto.snd_nhds

attribute [fun_prop]
  Continuous.tendsto
  ContinuousAt.tendsto

-- others
attribute [fun_prop]
  Tendsto.add
  Tendsto.add_atTop
  Tendsto.atTop_add
  Tendsto.sub
  Tendsto.mul
  Tendsto.div

  Tendsto.neg
  Tendsto.inv
  Tendsto.inv₀
  Tendsto.pow
  Tendsto.zpow


----------------------------------------------------------------------------------------------------


variable {f g k : ℝ → ℝ}

-- Constant function
example : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · simp

-- Single atom, identity
example (h : Tendsto f atTop (nhds 3)) :
    Tendsto (fun z => f z) atTop (nhds 3) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · simp

-- Single atom, scalar multiply
example (h : Tendsto f atTop (nhds 0)) :
    Tendsto (fun z => 2 * f z) atTop (nhds 0) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · simp

-- Two atoms, sum
example (h₁ : Tendsto f atTop (nhds 1)) (h₂ : Tendsto g atTop (nhds 2)) :
    Tendsto (fun z => f z + g z) atTop (nhds 3) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · norm_num


-- Two atoms, polynomial
example (h₁ : Tendsto f atTop (nhds 0)) (h₂ : Tendsto g atTop (nhds 1)) :
    Tendsto (fun z => f z ^ 2 + f z * g z + g z ^ 2) atTop (nhds 1) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · norm_num


-- Three atoms, subtraction
example (h₁ : Tendsto f atTop (nhds 0)) (h₂ : Tendsto g atTop (nhds 1))
    (h₃ : Tendsto k atTop (nhds 1)) :
    Tendsto (fun z => f z + g z - k z) atTop (nhds 0) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · norm_num


-- Unused hypotheses in context don't interfere
example (h₁ : Tendsto f atTop (nhds 0)) (h₂ : Tendsto g atTop (nhds 1))
    (_h_unrelated : Tendsto f atBot (nhds 5)) :
    Tendsto (fun z => f z * g z) atTop (nhds 0) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · norm_num

-- ══════════════════════════════════════════════════════════════
-- Issue 1: Non-last-argument matching (isDefEq-based)
-- ══════════════════════════════════════════════════════════════

-- Atom where bound variable is not the last argument
example (H : ℝ → ℝ → ℝ) (hH : Tendsto (fun z => H z 5) atTop (nhds 3)) :
    Tendsto (fun z => H z 5 + 1) atTop (nhds 4) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · norm_num

-- ══════════════════════════════════════════════════════════════
-- Issue 2: Symbolic target limits (ring fallback)
-- ══════════════════════════════════════════════════════════════

-- Commutativity: target says b + a, computed limit is a + b
example (h₁ : Tendsto f atTop (nhds 1)) (h₂ : Tendsto g atTop (nhds 2)) :
    Tendsto (fun z => g z + f z) atTop (nhds 3) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · norm_num


-- Symbolic commutativity: target limit (b + a) differs from computed (a + b)
example {a b : ℝ} (h₁ : Tendsto f atTop (nhds a)) (h₂ : Tendsto g atTop (nhds b)) :
    Tendsto (fun z => f z + g z) atTop (nhds (b + a)) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · grind

-- Symbolic associativity: target limit a + (b + c) vs computed order
example {a b c : ℝ} (h₁ : Tendsto f atTop (nhds a)) (h₂ : Tendsto g atTop (nhds b))
    (h₃ : Tendsto k atTop (nhds c)) :
    Tendsto (fun z => f z + g z + k z) atTop (nhds (a + (b + c))) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · grind

-- ══════════════════════════════════════════════════════════════
-- Issue 3: Duplicate (same limit) hypotheses succeed
-- ══════════════════════════════════════════════════════════════

-- Two hypotheses for same atom with same limit should not error
example (h₁ : Tendsto f atTop (nhds 0)) (_h₂ : Tendsto f atTop (nhds 0)) :
    Tendsto (fun z => f z + 1) atTop (nhds 1) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · grind


-- ══════════════════════════════════════════════════════════════
-- Issue 3: Ambiguity detection (different limits for same atom)
-- ══════════════════════════════════════════════════════════════

/--
error: unsolved goals
case h
f g k : ℝ → ℝ
h₁ : Tendsto f atTop (𝓝 0)
h₂ : Tendsto f atTop (𝓝 1)
⊢ False
-/
#guard_msgs(error, drop info) in
example (h₁ : Tendsto f atTop (nhds 0)) (h₂ : Tendsto f atTop (nhds 1)) :
    Tendsto (fun z => f z + 1) atTop (nhds 1) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · simp -- unprovable state, fun_prop eagerally applies h₁


-- ══════════════════════════════════════════════════════════════
-- Issue 4a: Zero atoms, no candidates for filter
-- ══════════════════════════════════════════════════════════════

/-- error: `simp` made no progress -/
#guard_msgs(error, drop info) in
example : Tendsto (fun z : ℝ => z + 1) atTop (nhds 0) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · simp -- unprovable

example : Tendsto (fun z : ℝ => z + 1) atTop atTop := by
  apply Tendsto.congr_l₂
  · fun_prop
  · simp


-- ══════════════════════════════════════════════════════════════
-- Issue 4b: Zero atoms, candidates exist but none matched
-- ══════════════════════════════════════════════════════════════

/--
error: `fun_prop` was unable to prove `Tendsto (fun z => g z + 1) atTop ?l₂`

Issues:
  No theorems found for `g` in order to prove `[?l₂], Tendsto (fun z => g z) atTop ?l₂`
  No theorems found for `g` in order to prove `[?l₂], Tendsto (fun a => g a) atTop ?l₂`
---
error: `simp` made no progress
---
error: unsolved goals
case l₂
f g k : ℝ → ℝ
h : Tendsto f atTop (𝓝 0)
⊢ Filter ℝ
-/
#guard_msgs(error, drop info) in
example (h : Tendsto f atTop (nhds 0)) :
    Tendsto (fun z => g z + 1) atTop (nhds 0) := by
  apply Tendsto.congr_l₂
  · fun_prop -- nothing known about `g`
  · simp


-- ══════════════════════════════════════════════════════════════
-- Non-polynomial continuous functions (sin, exp)
-- ══════════════════════════════════════════════════════════════

-- sin of a convergent function
example (h : Tendsto f atTop (nhds 0)) :
    Tendsto (fun z => Real.sin (f z)) atTop (nhds 0) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · simp

-- exp of a convergent function
example (h : Tendsto f atTop (nhds 0)) :
    Tendsto (fun z => Real.exp (f z)) atTop (nhds 1) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · simp

-- Mixed: polynomial + sin
example (h₁ : Tendsto f atTop (nhds 0)) (h₂ : Tendsto g atTop (nhds 1)) :
    Tendsto (fun z => f z ^ 2 + Real.sin (g z)) atTop (nhds (Real.sin 1)) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · simp

-- exp * sin composition
example (h : Tendsto f atTop (nhds 0)) :
    Tendsto (fun z => Real.exp (f z) * Real.sin (f z)) atTop (nhds 0) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · simp

-- ══════════════════════════════════════════════════════════════
-- Complex numbers
-- ══════════════════════════════════════════════════════════════

section Complex
open Complex

variable {fc gc : ℝ → ℂ}

-- Complex: sum
example (h₁ : Tendsto fc atTop (nhds 1)) (h₂ : Tendsto gc atTop (nhds I)) :
    Tendsto (fun z => fc z + gc z) atTop (nhds (1 + I)) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · simp

-- Complex: polynomial
example (h₁ : Tendsto fc atTop (nhds 0)) (h₂ : Tendsto gc atTop (nhds 1)) :
    Tendsto (fun z => fc z ^ 2 + fc z * gc z + gc z ^ 2) atTop (nhds 1) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · simp

-- Complex: exp
example (h : Tendsto fc atTop (nhds 0)) :
    Tendsto (fun z => Complex.exp (fc z)) atTop (nhds 1) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · simp

-- Complex.re composition (pattern from PR #307: continuous_re.tendsto.comp)
example (h : Tendsto fc atTop (nhds 1)) :
    Tendsto (fun z => (fc z).re) atTop (nhds 1) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · simp

-- Complex.im composition
example (h : Tendsto fc atTop (nhds I)) :
    Tendsto (fun z => (fc z).im) atTop (nhds 1) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · simp

end Complex

-- ══════════════════════════════════════════════════════════════
-- Goal function behind a reducible definition (whnfR needed)
-- ══════════════════════════════════════════════════════════════

-- When the goal function is a reducible definition (abbrev), tendsto_cont
-- should reduce it via whnfR to find the lambda (no `change` or `show` needed).
noncomputable abbrev myExpr (f g : ℝ → ℝ) : ℝ → ℝ := fun z => f z ^ 2 + g z

example (hf : Tendsto f atTop (nhds 1)) (hg : Tendsto g atTop (nhds 2)) :
    Tendsto (myExpr f g) atTop (nhds 3) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · norm_num

noncomputable abbrev myExprMul (f g : ℝ → ℝ) : ℝ → ℝ := fun z => f z * g z

example (hf : Tendsto f atTop (nhds 2)) (hg : Tendsto g atTop (nhds 3)) :
    Tendsto (myExprMul f g) atTop (nhds 6) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · norm_num


-- ══════════════════════════════════════════════════════════════
-- General topological ring
-- ══════════════════════════════════════════════════════════════

section GeneralRing

-- Sum over a general topological ring
example {R : Type*} [TopologicalSpace R] [Ring R] [IsTopologicalRing R]
    {α : Type*} {l : Filter α}
    {f g : α → R} {a b : R}
    (h₁ : Tendsto f l (nhds a)) (h₂ : Tendsto g l (nhds b)) :
    Tendsto (fun z => f z + g z) l (nhds (a + b)) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · simp

-- Product over a general topological ring
example {R : Type*} [TopologicalSpace R] [Ring R] [IsTopologicalRing R]
    {α : Type*} {l : Filter α}
    {f g : α → R} {a b : R}
    (h₁ : Tendsto f l (nhds a)) (h₂ : Tendsto g l (nhds b)) :
    Tendsto (fun z => f z * g z) l (nhds (a * b)) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · simp

-- Polynomial over a commutative topological ring (ring fallback)
example {R : Type*} [TopologicalSpace R] [CommRing R] [IsTopologicalRing R]
    {α : Type*} {l : Filter α}
    {f g : α → R} {a b : R}
    (h₁ : Tendsto f l (nhds a)) (h₂ : Tendsto g l (nhds b)) :
    Tendsto (fun z => f z * g z + g z * f z) l (nhds (2 * a * b)) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · ring_nf

end GeneralRing

-- ══════════════════════════════════════════════════════════════
-- Non-atTop filters (nhds 0, etc.)
-- ══════════════════════════════════════════════════════════════

-- Limit at nhds 0 (not atTop/atBot)
example (h : Tendsto f (nhds 0) (nhds 1)) :
    Tendsto (fun x => 2 * f x) (nhds 0) (nhds 2) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · simp


-- Two hypotheses with different filters: picks the right one
example (_h₁ : Tendsto f (nhds 0) (nhds 1)) (h₂ : Tendsto f atTop (nhds 0)) :
    Tendsto (fun x => 2 * f x) atTop (nhds 0) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · simp

-- ══════════════════════════════════════════════════════════════
-- Composition: f(g(x)) as a single atom
-- ══════════════════════════════════════════════════════════════

-- Hypothesis about f(g(x)) treated as one atom
/--
error: `fun_prop` was unable to prove `Tendsto (fun x => 2 * f (g x)) (𝓝 0) ?l₂`

Issues:
  No theorems found for `g` in order to prove `[?l₂], Tendsto (fun x => g x) (𝓝 0) ?l₂`
---
error: `simp` made no progress
---
error: unsolved goals
case l₂
f g k : ℝ → ℝ
h : Tendsto (fun x => f (g x)) (𝓝 0) (𝓝 1)
⊢ Filter ℝ
-/
#guard_msgs in
example (h : Tendsto (fun x => f (g x)) (nhds 0) (nhds 1)) :
    Tendsto (fun x => 2 * f (g x)) (nhds 0) (nhds 2) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · simp

-- ══════════════════════════════════════════════════════════════
-- Composition via continuity: g(f(x)) where g is continuous
-- ══════════════════════════════════════════════════════════════

-- g continuous + f → 1 at 0 gives g(f(x)) → g(1) at 0
example (hf : Tendsto f (nhds 0) (nhds 1)) (hg : Continuous g) :
    Tendsto (fun x => g (f x)) (nhds 0) (nhds (g 1)) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · simp

-- Without continuity hypothesis, fun_prop can't prove ContinuousAt g
/--
error: `fun_prop` was unable to prove `Tendsto (fun x => g (f x)) (𝓝 0) ?l₂`

Issues:
  No theorems found for `g` in order to prove `[?l₂], Tendsto (fun x0 => g x0) (𝓝 1) ?l₂`
---
error: `simp` made no progress
---
error: unsolved goals
case l₂
f g k : ℝ → ℝ
hf : Tendsto f (𝓝 0) (𝓝 1)
⊢ Filter ℝ
-/
#guard_msgs(error, drop info) in
example (hf : Tendsto f (nhds 0) (nhds 1)) :
    Tendsto (fun x => g (f x)) (nhds 0) (nhds (g 1)) := by
  apply Tendsto.congr_l₂
  · fun_prop -- no theorem for `g`
  · simp

-- But known continuous functions (Real.sin, etc.) work fine via fun_prop
example (hf : Tendsto f (nhds 0) (nhds 1)) :
    Tendsto (fun x => Real.sin (f x)) (nhds 0) (nhds (Real.sin 1)) := by
  apply Tendsto.congr_l₂
  · fun_prop
  · simp



-- ══════════════════════════════════════════════════════════════
-- disch := ... (discharger for fun_prop side conditions)
-- ══════════════════════════════════════════════════════════════

-- Inverse requires nonzero side condition
example (h : Tendsto f atTop (nhds 3)) :
    Tendsto (fun z => (f z)⁻¹) atTop (nhds 3⁻¹) := by
  apply Tendsto.congr_l₂
  · fun_prop (disch := norm_num)
  · simp


attribute [fun_prop] ContinuousAt.tendsto

/--
error: `fun_prop` was unable to prove `Tendsto (fun z => f z / g z) atTop ?l₂`

Issues:
  No theorems found for `HDiv.hDiv` in order to prove `[?l₂], Tendsto (fun z4z5 => z4z5.1 / z4z5.2) (𝓝 6 ×ˢ 𝓝 3) ?l₂`
  No theorems found for `HDiv.hDiv` in order to prove `[?l₂], Tendsto (fun z => f z / g z) atTop ?l₂`
---
error: `simp` made no progress
---
error: unsolved goals
case l₂
f g k : ℝ → ℝ
h₁ : Tendsto f atTop (𝓝 6)
h₂ : Tendsto g atTop (𝓝 3)
⊢ Filter ℝ
-/
#guard_msgs in
example (h₁ : Tendsto f atTop (nhds 6)) (h₂ : Tendsto g atTop (nhds 3)) :
    Tendsto (fun z => f z / g z) atTop (nhds 2) := by
  apply Tendsto.congr_l₂
  · fun_prop (disch := norm_num) -- for some reason `ContinuousAt.tendsto` does not fire :(, this is bug in `fun_prop`
  · simp


-- disch combined with inline args
example (h₁ : Tendsto f atTop (nhds 6)) :
    Tendsto (fun z => f z / 3) atTop (nhds 2) := by
  apply Tendsto.congr_l₂
  · fun_prop (disch := norm_num)
  · norm_num


example (h : Tendsto f atTop (nhds 3)) :
    Tendsto (fun z => (f z)⁻¹) atTop (nhds 3⁻¹) := by
  apply Tendsto.congr_l₂
  · fun_prop (disch := norm_num)
  · norm_num




/--
error: unsolved goals
case h
f g k : ℝ → ℝ
⊢ Set.Ioi 0 ∈ 𝓝 2
-/
#guard_msgs in
example : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (nhdsWithin 2 (Set.Ioi 0)) := by
  apply Tendsto.congr_l₂
  · fun_prop (disch := norm_num)
  · simp -- how to show `𝓝[Set.Ioi 0] 2 = 𝓝 2` ??

/--
error: unsolved goals
case h
f g k : ℝ → ℝ
h : Tendsto f atTop (𝓝 3)
hpos : ∀ (x : ℝ), 0 < f x
⊢ Set.Ioi 0 ∈ 𝓝 3
-/
#guard_msgs in
example (h : Tendsto f atTop (nhds 3))
    (hpos : ∀ x, 0 < f x) :
    Tendsto (fun z => f z) atTop (nhdsWithin 3 (Set.Ioi 0)) := by
  apply Tendsto.congr_l₂
  · fun_prop (disch := norm_num)
  · simp -- how to show `𝓝[Set.Ioi 0] 3 = 𝓝 3`


/--
error: unsolved goals
case h
f g k : ℝ → ℝ
h : Tendsto f atTop (𝓝 3)
hpos : ∀ (x : ℝ), 0 < f x
⊢ Set.Ioi 0 ∈ 𝓝 3⁻¹
-/
#guard_msgs in
example (h : Tendsto f atTop (nhds 3))
    (hpos : ∀ x, 0 < f x) :
    Tendsto (fun z => (f z)⁻¹) atTop (nhdsWithin 3⁻¹ (Set.Ioi 0)) := by
  apply Tendsto.congr_l₂
  · fun_prop (disch := norm_num)
  · simp -- how to show `𝓝[Set.Ioi 0] 3⁻¹ = 𝓝 3⁻¹`

-- Reversed option order works
/--
error: unsolved goals
case h
f g k : ℝ → ℝ
h : Tendsto f atTop (𝓝 3)
hpos : ∀ (x : ℝ), 0 < f x
⊢ Set.Ioi 0 ∈ 𝓝 3⁻¹
-/
#guard_msgs in
example (h : Tendsto f atTop (nhds 3))
    (hpos : ∀ x, 0 < f x) :
    Tendsto (fun z => (f z)⁻¹) atTop (nhdsWithin 3⁻¹ (Set.Ioi 0)) := by
  apply Tendsto.congr_l₂
  · fun_prop (disch := norm_num)
  · simp -- `Set.Ioi 0 ∈ 𝓝 3⁻¹` ?

-- within_disch with a direct ∀ᶠ-level tactic (no pointwise lift needed)
-- Uses filter_upwards which assumption can't match
/--
error: unsolved goals
case h
f g k : ℝ → ℝ
h : Tendsto f atTop (𝓝 3)
hpos : ∀ (x : ℝ), 0 < f x
⊢ Set.Ioi 0 ∈ 𝓝 3
-/
#guard_msgs in
example (h : Tendsto f atTop (nhds 3))
    (hpos : ∀ x, 0 < f x) :
    Tendsto (fun z => f z) atTop (nhdsWithin 3 (Set.Ioi 0)) := by
  apply Tendsto.congr_l₂
  · fun_prop (disch := norm_num)
  · simp -- `𝓝[Set.Ioi 0] 3 = 𝓝 3` ?
