/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
## Continuous representations

This file defines continuous representations of a monoid `G` on a `R`-module `V` and
related basic results.

## Main Results

* `ContRepresentation R G V` is the type of continuous representations of a monoid `G` on a
  `R`-module `V` which is a topological addgroup (where the action of `G` on `V` is
  *not* assumed to be continuous). The reason for this more general definition is that it allows us
  to define the coinduced representation of a continuous representation as also a continuous
  representation without any restriction on the topology on `G`.

* `ContIntertwiningMap π₁ π₂` is the type of continuous intertwining maps between two continuous
  representations `π₁` and `π₂`.

* `ContRepresentation.coind₁ π` is the coinduced continuous representation on the space of
  continuous functions from `G` to `V` for a continuous representation `π`.

## Tags
continuous representation, algebra
-/

@[expose] public section

variable (R G V W U X : Type*) [Monoid G] [Ring R] [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [Module R V] [AddCommGroup W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [Module R W] [AddCommGroup U] [Module R U] [TopologicalSpace U]
  [IsTopologicalAddGroup U] [AddCommGroup X] [Module R X] [TopologicalSpace X]
  [IsTopologicalAddGroup X]

/-- A continuous representation of a group `G` on a `R`-module `V` which is a topological addgroup
  is a homomorphism `G →* V →L[R] V`. -/
abbrev ContRepresentation := G →* V →L[R] V

/-- Every continuous representation "is" a representation. -/
abbrev ContRepresentation.toRepresentation (π : ContRepresentation R G V) :
    Representation R G V :=
  .comp ContinuousLinearMap.toLinearMapRingHom.toMonoidHom π

variable {R G V W U}

/-- A continuous intertwining map between two continuous representations is an intertwining map
  which is also continuous. -/
structure ContIntertwiningMap (π₁ : ContRepresentation R G V) (π₂ : ContRepresentation R G W)
    extends V →L[R] W where
  isIntertwining' (g : G) : toContinuousLinearMap ∘L π₁ g = π₂ g ∘L toContinuousLinearMap

/-- notation for continuous intertwining maps -/
scoped[ContRepresentation] notation:30 π₁ " →ⁱL " π₂ =>
  ContIntertwiningMap π₁ π₂

namespace ContIntertwiningMap

open ContRepresentation

variable {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
  {π₃ : ContRepresentation R G U} {π₄ : ContRepresentation R G X}

/-- Any continuous intertwining map is an intertwining map. -/
abbrev toIntertwiningMap (f : π₁ →ⁱL π₂) :
    Representation.IntertwiningMap π₁.toRepresentation π₂.toRepresentation where
  __ := f.toContinuousLinearMap.toLinearMap
  isIntertwining' g := congr(ContinuousLinearMap.toLinearMap $(f.2 g))

/-- The identity continuous intertwining map. -/
def id : π₁ →ⁱL π₁ where
  __ := ContinuousLinearMap.id R V
  isIntertwining' g := by simp

@[ext]
lemma ext {f g : π₁ →ⁱL π₂} (h : f.toContinuousLinearMap = g.toContinuousLinearMap) : f = g := by
  cases f; cases g; congr

lemma toIntertwiningMap_injective :
    Function.Injective fun f : π₁ →ⁱL π₂ ↦ f.toContinuousLinearMap :=
  fun _ _ ↦ ext

lemma toFun_injective : Function.Injective fun f : π₁ →ⁱL π₂ ↦ f.toFun := fun f g h ↦ by
  ext x; exact congr_fun h x

instance : FunLike (π₁ →ⁱL π₂) V W where
  coe f := f.toFun
  coe_injective' := toFun_injective

lemma isIntertwining (f : π₁ →ⁱL π₂) (g : G) (v : V) : f (π₁ g v) = π₂ g (f v) :=
  f.toIntertwiningMap.isIntertwining _ _ g v

instance : ContinuousLinearMapClass (π₁ →ⁱL π₂) R V W where
  map_add f := f.map_add
  map_smulₛₗ f := f.map_smul
  map_continuous f := f.cont

open ContinuousLinearMap in
/-- The composition of two continuous intertwining maps is a continuous intertwining map. -/
def comp (f : π₂ →ⁱL π₃) (g : π₁ →ⁱL π₂) : π₁ →ⁱL π₃ where
  __ := f.toContinuousLinearMap.comp g.toContinuousLinearMap
  isIntertwining' h := by rw [comp_assoc, g.2, ← comp_assoc, f.2, comp_assoc]

infixr:80 " ∘ⁱL " => ContIntertwiningMap.comp

@[simp]
lemma comp_toContinuousLinearMap (f : π₂ →ⁱL π₃) (g : π₁ →ⁱL π₂) :
    (f ∘ⁱL g).toContinuousLinearMap = f.toContinuousLinearMap.comp g.toContinuousLinearMap := rfl

@[simp]
lemma comp_apply (f : π₂ →ⁱL π₃) (g : π₁ →ⁱL π₂) (v : V) :
    (f ∘ⁱL g) v = f (g v) := rfl

lemma comp_assoc (f : π₃ →ⁱL π₄) (g : π₂ →ⁱL π₃)
    (h : π₁ →ⁱL π₂) : f ∘ⁱL (g ∘ⁱL h) = (f ∘ⁱL g) ∘ⁱL h := by
  ext1; simp [ContinuousLinearMap.comp_assoc]

lemma id_apply (v : V) : (id : π₁ →ⁱL π₁) v = v := rfl

@[simp]
lemma id_toContinuousLinearMap :
    (id : π₁ →ⁱL π₁).toContinuousLinearMap = ContinuousLinearMap.id R V := rfl

@[simp] lemma comp_id (f : π₁ →ⁱL π₂) : f ∘ⁱL id = f := by ext; simp

@[simp] lemma id_comp (f : π₁ →ⁱL π₂) : id ∘ⁱL f = f := by ext; simp

instance : Zero (π₁ →ⁱL π₂) where
  zero := ⟨0, by simp⟩

@[simp] lemma zero_toContinuousLinearMap : (0 : π₁ →ⁱL π₂).toContinuousLinearMap = 0 := rfl

@[simp] lemma zero_apply (v : V) : (0 : π₁ →ⁱL π₂) v = 0 := rfl

@[simp] lemma zero_comp (f : π₂ →ⁱL π₃) : (0 : π₃ →ⁱL π₄) ∘ⁱL f = 0 := by
  simp [ContIntertwiningMap.ext_iff, ContIntertwiningMap.comp_toContinuousLinearMap]

@[simp] lemma comp_zero (f : π₂ →ⁱL π₃) : f ∘ⁱL (0 : π₁ →ⁱL π₂) = 0 := by
  simp [ContIntertwiningMap.ext_iff, ContIntertwiningMap.comp_toContinuousLinearMap]

instance : Add (π₁ →ⁱL π₂) where
  add f g := ⟨f.toContinuousLinearMap + g.toContinuousLinearMap, fun _ ↦ by simp [f.2, g.2]⟩

@[simp]
lemma add_toContinuousLinearMap (f g : π₁ →ⁱL π₂) :
    (f + g).toContinuousLinearMap = f.toContinuousLinearMap + g.toContinuousLinearMap := rfl

lemma add_apply (f g : π₁ →ⁱL π₂) (v : V) : (f + g) v = f v + g v := rfl

lemma add_comp (f₁ f₂ : π₂ →ⁱL π₃) (g : π₁ →ⁱL π₂) :
    (f₁ + f₂) ∘ⁱL g = f₁ ∘ⁱL g + f₂ ∘ⁱL g := by ext; simp [ContinuousLinearMap.add_comp]

lemma comp_add (f : π₂ →ⁱL π₃) (g₁ g₂ : π₁ →ⁱL π₂) :
    f ∘ⁱL (g₁ + g₂) = f ∘ⁱL g₁ + f ∘ⁱL g₂ := by ext; simp [ContinuousLinearMap.comp_add]

lemma add_assoc' (f g h : π₁ →ⁱL π₂) : (f + g) + h = f + (g + h) := by ext; simp [add_assoc]

lemma add_comm' (f g : π₁ →ⁱL π₂) : f + g = g + f := by ext; simp [add_comm]

lemma zero_add' (f : π₁ →ⁱL π₂) : 0 + f = f := by ext; simp [zero_apply]

lemma add_zero' (f : π₁ →ⁱL π₂) : f + 0 = f := by ext; simp [zero_apply]

instance : Neg (π₁ →ⁱL π₂) where
  neg f := ⟨-f.toContinuousLinearMap, by simp [f.2]⟩

@[simp]
lemma neg_toContinuousLinearMap (f : π₁ →ⁱL π₂) :
    (-f).toContinuousLinearMap = -f.toContinuousLinearMap := rfl

lemma neg_apply (f : π₁ →ⁱL π₂) (v : V) : (-f) v = -f v := rfl

lemma neg_comp (f : π₂ →ⁱL π₃) (g : π₁ →ⁱL π₂) : (-f) ∘ⁱL g = -(f ∘ⁱL g) := by
  ext; simp [ContinuousLinearMap.neg_comp]

lemma comp_neg (f : π₂ →ⁱL π₃) (g : π₁ →ⁱL π₂) : f ∘ⁱL (-g) = -(f ∘ⁱL g) := by
  ext; simp [ContinuousLinearMap.comp_neg]

lemma add_neg_cancel' (f : π₁ →ⁱL π₂) : f + (-f) = 0 := by ext; simp

lemma neg_add_cancel' (f : π₁ →ⁱL π₂) : (-f) + f = 0 := by ext; simp

section smul

variable {S : Type*} [Monoid S] [DistribMulAction S W] [SMulCommClass R S W]
    [LinearMap.CompatibleSMul W W S R] [ContinuousConstSMul S W]

instance : SMul S (π₁ →ⁱL π₂) where
  smul s f := ⟨s • f.toContinuousLinearMap, fun _ ↦ by
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, f.2]⟩

@[simp]
lemma smul_toContinuousLinearMap (s : S) (f : π₁ →ⁱL π₂) :
    (s • f).toContinuousLinearMap = s • f.toContinuousLinearMap := rfl

lemma smul_apply (s : S) (f : π₁ →ⁱL π₂) (v : V) : (s • f) v = s • f v := rfl

@[simp] lemma smul_zero (s : S) : s • (0 : π₁ →ⁱL π₂) = 0 := by ext; simp

instance : MulAction S (π₁ →ⁱL π₂) where
  mul_smul _ _ _ := by ext; simp [SemigroupAction.mul_smul]
  one_smul _     := by ext; simp

end smul

instance : AddCommGroup (π₁ →ⁱL π₂) where
  add_assoc := add_assoc'
  zero_add := zero_add'
  add_zero := add_zero'
  add_comm := add_comm'
  nsmul := (· • ·)
  nsmul_zero _ := by ext; simp
  nsmul_succ _ _ := by ext; simp [add_smul]
  zsmul := (· • ·)
  zsmul_zero' _ := by ext; simp
  zsmul_succ' _ _ := by ext; simp [add_smul]
  zsmul_neg' _ _ := by ext; simp [add_smul]
  neg_add_cancel := neg_add_cancel'

end ContIntertwiningMap

namespace ContRepresentation

/-- The equivalence between continuous representations. -/
structure Equiv (π₁ : ContRepresentation R G V) (π₂ : ContRepresentation R G W) extends
    V ≃L[R] W, ContIntertwiningMap π₁ π₂  where mk'' ::

attribute [coe] Equiv.toContIntertwiningMap

/-- Underlying continuous linear isomorphism of an equivalence of continuous representations. -/
add_decl_doc Equiv.toContinuousLinearEquiv

/-- The continuous intertwining map underlying an equivalence of continuous representations. -/
add_decl_doc Equiv.toContIntertwiningMap

variable {ρ : ContRepresentation R G V} {σ : ContRepresentation R G W}
  {τ : ContRepresentation R G U}
namespace Equiv

variable (φ : Equiv ρ σ)

lemma isIntertwining (g : G) :
    φ.toContinuousLinearEquiv.toContinuousLinearMap ∘L (ρ g) =
      (σ g) ∘L φ.toContinuousLinearEquiv.toContinuousLinearMap :=
  φ.isIntertwining' g

/-- An `Equiv` between representations could be built from a `LinearEquiv` and an assumption
  proving the `G`-equivariance. -/
def mk (e : V ≃L[R] W) (he : ∀ g, e ∘L (ρ g) = (σ g) ∘L e) : ρ.Equiv σ where
  __ := e
  cont := e.continuous
  isIntertwining' := he

lemma toContinuousLinearEquiv_mk' {e : V ≃L[R] W} (he : ∀ g, e ∘L (ρ g) = (σ g) ∘L e) :
    (mk e he).toContinuousLinearEquiv = e := rfl

lemma toContIntertwiningMap_mk' (e : V ≃L[R] W) (he : ∀ g, e ∘L (ρ g) = (σ g) ∘L e) :
    (mk e he).toContIntertwiningMap = ⟨e.toContinuousLinearMap, he⟩ := rfl

@[simp]
lemma toContinuousLinearMap_mk' (e : V ≃L[R] W) (he : ∀ g, e ∘L (ρ g) = (σ g) ∘L e) :
    (mk e he).toContinuousLinearMap = e.toContinuousLinearMap := rfl

lemma toContinuousLinearEquiv_injective :
    Function.Injective (toContinuousLinearEquiv : (σ.Equiv ρ) → _) :=
  fun φ ψ h ↦ by cases φ; cases ψ; simpa [ContIntertwiningMap.ext_iff] using h

lemma toContinuousLinearEquiv_inj (φ ψ : σ.Equiv ρ) :
    φ.toContinuousLinearEquiv = ψ.toContinuousLinearEquiv ↔ φ = ψ :=
  toContinuousLinearEquiv_injective.eq_iff

instance : EquivLike (Equiv ρ σ) V W where
  coe φ := φ.toContinuousLinearEquiv
  inv φ := φ.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' φ ψ h1 h2 := by cases φ; cases ψ; simp_all

instance : ContinuousLinearEquivClass (σ.Equiv ρ) R W V where
  map_add f := f.map_add
  map_smulₛₗ f := f.map_smul
  map_continuous f := f.cont
  inv_continuous f := f.continuous_invFun

@[simp]
lemma mk_apply {e : V ≃L[R] W} (he : ∀ g, e ∘L (ρ g) = (σ g) ∘L e) (v : V) :
    (mk e he) v = e v := rfl

@[ext]
lemma ext {φ ψ : Equiv ρ σ} (h : (φ : V → W) = ψ) : φ = ψ := by
  cases φ; cases ψ
  simpa using h

variable (ρ) in
/-- Any continuous representation is equivalent to itself. -/
def refl : Equiv ρ ρ := mk (ContinuousLinearEquiv.refl R V) (by simp)

@[simp] lemma toContIntertwiningMap_refl : (refl ρ).toContIntertwiningMap = .id := rfl

@[simp] lemma toContinuousLinearMap_refl :
    (refl ρ).toContinuousLinearMap = ContinuousLinearMap.id R V := rfl

@[simp] lemma refl_apply (v : V) : refl ρ v = v := rfl

@[simp] lemma coe_toContIntertwiningMap : ⇑φ.toContIntertwiningMap = φ := rfl

lemma coe_toContinuousLinearMap : ⇑φ.toContinuousLinearMap = φ := rfl

lemma coe_invFun : φ.invFun = φ.symm := rfl

theorem toContinuousLinearEquiv_toContinuousLinearMap :
    φ.toContinuousLinearEquiv.toContinuousLinearMap =
      φ.toContIntertwiningMap.toContinuousLinearMap := rfl

theorem toContinuousLinearEquiv_apply (v : V) :
    φ.toContinuousLinearEquiv v = φ.toContIntertwiningMap v := rfl

open ContinuousLinearMap in
/-- The equiv between continuous representations are symmetric. -/
@[symm]
def symm : Equiv σ ρ := mk φ.toContinuousLinearEquiv.symm <| fun g ↦ by
  rw [← cancel_left' (g := φ.toContinuousLinearEquiv.toContinuousLinearMap)
    φ.toContinuousLinearEquiv.injective, ← comp_assoc, ← comp_assoc]
  simp [φ.isIntertwining g, comp_assoc]

open ContinuousLinearMap

lemma _root_.ContinuousLinearEquiv.isIntertwining_symm_isIntertwining {e : V ≃L[R] W}
    (he : ∀ g, e ∘L (ρ g) = (σ g) ∘L e) (g : G) :
    e.symm ∘L (σ g) = (ρ g) ∘L e.symm :=
  (mk e he).symm.isIntertwining g

@[simp]
lemma mk_symm {e : V ≃L[R] W} (he : ∀ g, e ∘L (ρ g) = (σ g) ∘L e) :
    (mk e he).symm = mk e.symm (e.isIntertwining_symm_isIntertwining he) := rfl

lemma toLinearMap_symm (φ : Equiv ρ σ) : (symm φ).toLinearMap = φ.toLinearEquiv.symm := rfl

lemma coe_symm (φ : Equiv ρ σ) : ⇑φ.toLinearEquiv.symm = φ.symm := rfl

/-- Composition of two `Equiv`s. -/
@[trans]
def trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) : Equiv ρ τ := mk
  (φ.toContinuousLinearEquiv.trans ψ.toContinuousLinearEquiv) <| fun g ↦ by
  rw [← ContinuousLinearEquiv.comp_coe, comp_assoc,
    φ.isIntertwining, ← comp_assoc, ψ.isIntertwining, comp_assoc]

@[simp]
lemma toContIntertwiningMap_trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) :
    (φ.trans ψ).toContIntertwiningMap = ψ.toContIntertwiningMap.comp φ.toContIntertwiningMap := rfl

@[simp]
lemma toContinuousLinearMap_trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) :
    (trans φ ψ).toContinuousLinearMap = ψ.toContinuousLinearMap.comp φ.toContinuousLinearMap := rfl

@[simp]
lemma trans_apply (φ : Equiv ρ σ) (ψ : Equiv σ τ) (v : V) :
    trans φ ψ v = ψ (φ v) := rfl

@[simp]
lemma apply_symm_apply (φ : Equiv ρ σ) (v : W) : φ (φ.symm v) = v := φ.right_inv v

@[simp]
lemma symm_apply_apply (φ : Equiv ρ σ) (v : V) : φ.symm (φ v) = v := φ.left_inv v

@[simp]
lemma trans_symm (φ : Equiv ρ σ) : φ.trans φ.symm = .refl ρ := by ext; simp

@[simp]
lemma symm_trans (φ : Equiv ρ σ) : φ.symm.trans φ = .refl σ := by ext; simp

end Equiv

variable (R G V) in
/-- The trivial continuous representation of a group `G` on a `R`-module `V`. -/
def trivial : ContRepresentation R G V := 1

@[simp]
lemma trivial_apply (g : G) (v : V) : trivial R G V g v = v := rfl



/-- The restriction of a continuous representation along a monoid homomorphism. -/
@[simps!]
def restrict {H : Type*} [Monoid H] (π : ContRepresentation R G V) (φ : H →* G) :
    ContRepresentation R H V := .comp π φ

-- TODO : define `IsTopologicalMonoid` and then replace `Homeomorph.mulLeft g⁻¹` with the
-- `ContinuousMap.mulRight g` to make `coind₁` work for monoids.
variable {G H : Type*} [Group G] [TopologicalSpace G] [TopologicalSpace R]
  [ContinuousSMul R V] [ContinuousSMul R W] [Group H] [TopologicalSpace H]
  (φ : G →ₜ* H) (π : ContRepresentation R G V)

/-- The underlying module of the coinduced continuous representation. -/
@[simps]
def coindV : Submodule R C(H, V) where
  carrier   := {f | ∀ g h, f (φ g * h) = π g (f h)}
  add_mem'  := by simp +contextual
  zero_mem' := by simp
  smul_mem' := by simp +contextual

@[simp]
lemma mem_coindV (f : C(H, V)) : f ∈ π.coindV φ ↔ ∀ g h, f (φ g * h) = π g (f h) := Iff.rfl

instance : ContinuousSMul R (π.coindV φ) where
  continuous_smul := by continuity

variable [IsTopologicalRing R] [IsTopologicalGroup G] [IsTopologicalGroup H]

/-- The coinduced continuous representation where the action of `H` is defined by
  `h ↦ f ↦ f ∘ (· * h)`. -/
@[simps]
def coind (π : ContRepresentation R G V) : ContRepresentation R H (π.coindV φ) where
  toFun h := {
    toFun | ⟨f, hf⟩ => ⟨f.comp (ContinuousMap.mulRight h), by simp [mul_assoc, hf _]⟩
    map_add' _ _ := by simp
    map_smul' _ _ := by simp
    cont := continuous_induced_rng.2 <| by
      simpa using! (ContinuousMap.mulRight h).continuous_precomp.comp continuous_subtype_val}
  map_one' := by ext; simp
  map_mul' h1 h2 := by ext; simp [ContinuousMap.mulRight_mul]

open ContinuousMap

/-- Given a continuous representation `π` of `G` on `V`,
this defines a Continuous representation `π.coind₁` of `G` on the function space `C(G,V)`.
The action of an element `g : G` is defined by `f ↦ (x ↦ π g (f (g⁻¹ * x)))`.
This new representation of `G` is isomorphic to the continuous coinduction
of the trivial representation of the trivial subgroup of `G`, but the action has been
twisted so that the map `const : V → C(G,V)` is an intertwining map. -/
@[simps]
def coind₁ (π : ContRepresentation R G V) :
    ContRepresentation R G C(G, V) where
  toFun g := {
    toFun f := .comp (π g) (f.comp (ContinuousMap.mulLeft g⁻¹))
    map_add' _ _ := by ext; simp
    map_smul' _ _ := by ext; simp
    cont := (continuous_postcomp _).comp (continuous_precomp _)
  }
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc]

/-- The functoriality of `coind₁`. -/
@[simps]
def _root_.ContIntertwiningMap.coind₁_map {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W} (f : π₁ →ⁱL π₂) :
    coind₁ π₁ →ⁱL coind₁ π₂ where
  toFun := (f : ContinuousMap _ _).comp
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  isIntertwining' g := by ext; simp [f.isIntertwining]
  cont := continuous_postcomp _

/-- The naturality of the transformation from `𝟭 ⟶ coind₁`. -/
@[simps]
def coind₁_ι (π : ContRepresentation R G V) : π →ⁱL coind₁ π where
  toFun := .const G
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' := by aesop
  cont := continuous_const'

/-- The equivalence between `coind₁` and `coind` of the trivial representation of trivial
  subgroup of `G`. -/
def coind₁Equivcoind : (coind₁ (.trivial R (⊥ : Subgroup G) V)).Equiv
  (coind 1 (.trivial R G V)) := .mk (Submodule.topContEquiv.symm.trans <|
    ContinuousLinearEquiv.ofEq _ _ (by simp [SetLike.ext_iff])) <| fun g ↦ by
    simp [Subsingleton.elim g 1, ContinuousLinearMap.one_def]

end ContRepresentation
