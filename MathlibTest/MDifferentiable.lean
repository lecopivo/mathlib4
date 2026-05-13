import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

open scoped Manifold
open Manifold

noncomputable section

section BasicManifoldRules

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners 𝕜 F' G'}
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  {f : M → M'} {g : M' → M''} {f₁ : M → M'} {f₂ : M → M''}
  {p : M × N → M'} {q : M × N → N'} {u : M → M' × M''}

example : MDiff fun x : M => x := by
  fun_prop

example (y : M') : MDifferentiable I I' (fun _ : M => y) := by
  fun_prop

example (hf : MDifferentiable I I' f) (hg : MDifferentiable I' I'' g) :
    MDifferentiable I I'' (fun x => g (f x)) := by
  fun_prop

example (hf₁ : MDifferentiable I I' f₁) (hf₂ : MDifferentiable I I'' f₂) :
    MDifferentiable I (I'.prod I'') (fun x => (f₁ x, f₂ x)) := by
  fun_prop

example (hu : MDifferentiable I (I'.prod I'') u) :
    MDifferentiable I I' (fun x => (u x).1) := by
  fun_prop

example (hu : MDifferentiable I (I'.prod I'') u) :
    MDifferentiable I I'' (fun x => (u x).2) := by
  fun_prop

example (hp : MDifferentiable (I.prod J) I' p) (hq : MDifferentiable (I.prod J) J' q) :
    MDifferentiable (I.prod J) (I'.prod J') (fun x => (p x, q x)) := by
  fun_prop

end BasicManifoldRules

section ModelSpaceRules

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {F₄ : Type*} [NormedAddCommGroup F₄] [NormedSpace 𝕜 F₄]

example (L : E →L[𝕜] E') : MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, E') (fun x => L x) := by
  fun_prop

example (e : E ≃L[𝕜] E') : MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, E') (fun x => e x) := by
  fun_prop

example {f : E → E'} {g : E' → E''}
    (hf : MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, E') f)
    (hg : Differentiable 𝕜 g) :
    MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, E'') (fun x => g (f x)) := by
  fun_prop

example {A : E → F₁ →L[𝕜] F₂}
    (hA : MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, F₁ →L[𝕜] F₂) A) :
    MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃))
      (fun x => (A x).precomp F₃ : E → (F₂ →L[𝕜] F₃) →L[𝕜] (F₁ →L[𝕜] F₃)) := by
  fun_prop

example {A : E → F₂ →L[𝕜] F₃}
    (hA : MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, F₂ →L[𝕜] F₃) A) :
    MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃))
      (fun x => (A x).postcomp F₁ : E → (F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₃)) := by
  fun_prop

example {A : E → F₁ →L[𝕜] F₃} {B : E → F₂ →L[𝕜] F₁}
    (hA : MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, F₁ →L[𝕜] F₃) A)
    (hB : MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, F₂ →L[𝕜] F₁) B) :
    MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, F₂ →L[𝕜] F₃) (fun x => (A x).comp (B x)) := by
  fun_prop

example {A : E → F₁ →L[𝕜] F₂} {v : E → F₁}
    (hA : MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, F₁ →L[𝕜] F₂) A)
    (hv : MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, F₁) v) :
    MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, F₂) (fun x => (A x) (v x) : E → F₂) := by
  fun_prop (disch:=first | assumption | find_model)

example {A : E → F₁ →L[𝕜] F₃} {B : E → F₂ →L[𝕜] F₄}
    (hA : MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, F₁ →L[𝕜] F₃) A)
    (hB : MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, F₂ →L[𝕜] F₄) B) :
    MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, (F₁ × F₂) →L[𝕜] F₃ × F₄)
      (fun x => (A x).prodMap (B x)) := by
  fun_prop

end ModelSpaceRules

section ArithmeticRules

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {ι : Type} {t : Finset ι}
  {f g : M → E'} {A : ι → M → E'}

example (hf : MDiff f) (hg : MDiff g) : MDiff fun x => f x + g x := by
  fun_prop

example (hA : ∀ i ∈ t, MDifferentiable I 𝓘(𝕜, E') (A i)) :
    MDifferentiable I 𝓘(𝕜, E') (fun x => ∑ i ∈ t, A i x) := by
  exact MDifferentiable.fun_sum hA

example (c : 𝕜) (hf : MDiff f) : MDiff fun x => c • f x := by
  fun_prop

example (hf : MDiff f) : MDiff fun x => -f x := by
  fun_prop

example (hf : MDiff f) (hg : MDiff g) : MDiff fun x => f x - g x := by
  fun_prop

end ArithmeticRules

section AlgebraRules

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {R : Type*} [NormedRing R] [NormedAlgebra 𝕜 R]
  {S : Type*} [NormedCommRing S] [NormedAlgebra 𝕜 S]
  {K : Type*} [NormedDivisionRing K] [NormedAlgebra 𝕜 K]
  {ι : Type} {t : Finset ι}
  {p q : M → R} {a b : M → S} {c d : M → K} {A : ι → M → S}

example (hp : MDifferentiable I 𝓘(𝕜, R) p) (hq : MDifferentiable I 𝓘(𝕜, R) q) :
    MDifferentiable I 𝓘(𝕜, R) (fun x => p x * q x) := by
  fun_prop

example (hp : MDifferentiable I 𝓘(𝕜, R) p) (n : ℕ) :
    MDifferentiable I 𝓘(𝕜, R) (fun x => p x ^ n) := by
  fun_prop

example (hA : ∀ i ∈ t, MDifferentiable I 𝓘(𝕜, S) (A i)) :
    MDifferentiable I 𝓘(𝕜, S) (fun x => ∏ i ∈ t, A i x) := by
  fun_prop (disch:=assumption)

example (hc : MDifferentiable I 𝓘(𝕜, K) c) (hc_ne : ∀ x, c x ≠ 0) :
    MDifferentiable I 𝓘(𝕜, K) (fun x => (c x)⁻¹) := by
  fun_prop (disch := assumption)

example (hc : MDifferentiable I 𝓘(𝕜, K) c) (hd : MDifferentiable I 𝓘(𝕜, K) d)
    (hd_ne : ∀ x, d x ≠ 0) :
    MDifferentiable I 𝓘(𝕜, K) (fun x => c x / d x) := by
  fun_prop (disch := assumption)

example {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {r : M → 𝕜} {v : M → V} (hr : MDiff r) (hv : MDiff v) :
    MDiff fun x => r x • v x := by
  fun_prop

end AlgebraRules
