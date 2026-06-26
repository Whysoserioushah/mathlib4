import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.RingTheory.SimpleModule.Basic

universe u v

open CategoryTheory
variable (R S : Type*) [DivisionRing R] [DivisionRing S] (e : ModuleCat R ≌ ModuleCat S)

lemma division_ring_exists_unique_isSimpleModule (N : Type*) [AddCommGroup N] [Module S N]
    [IsSimpleModule S N] : Nonempty (N ≃ₗ[S] S) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹_›
  exact ⟨e ≪≫ₗ I.quotEquivOfEqBot ((eq_bot_or_eq_top I).resolve_right hI.ne_top)⟩

lemma isSimpleModule_iff_injective_or_eq_zero (R : Type u) (M : Type v) [Ring R] [AddCommGroup M]
    [Module R M] : IsSimpleModule R M ↔ (Nontrivial M ∧ ∀ (N : Type v) [AddCommGroup N]
    [Module R N] (f : M →ₗ[R] N), f = 0 ∨ Function.Injective f) :=
  ⟨fun hM ↦ ⟨Submodule.nontrivial_iff _|>.1 hM.1.1, fun N _ _ f ↦ hM.1.2 (LinearMap.ker f)|>.elim
    (fun h ↦ Or.inr <| by rwa [LinearMap.ker_eq_bot] at h) (fun h ↦ Or.inl <|by simp_all)⟩,
  fun ⟨hM1, hM2⟩ ↦ isSimpleModule_iff R M|>.2 ⟨fun p ↦ (hM2 (M ⧸ p) p.mkQ).elim
  (fun h ↦ Or.inr <| by simpa [Submodule.ext_iff, LinearMap.ext_iff] using h)
  (fun h ↦ Or.inl <| eq_bot_iff.2 fun x hx ↦ h (by simp [hx]))⟩⟩

open ZeroObject

variable {R S} in
instance _root_.CategoryTheory.Equivalence.nontrivial (R S : Type*) [Ring R] [Ring S]
    (e : ModuleCat R ≌ ModuleCat S) (M : ModuleCat R) [h : Nontrivial M] :
    Nontrivial (e.functor.obj M) := by
  by_contra! inst1
  have hM : Limits.IsZero M := Functor.id_obj M ▸ CategoryTheory.Iso.isZero_iff (e.unitIso.app M)|>.2
    <| Functor.map_isZero e.inverse <| ModuleCat.isZero_of_subsingleton <| e.functor.obj M
  exact (@not_nontrivial M <| ModuleCat.subsingleton_of_isZero hM) h

variable (K : Type u) [Field K]

lemma IsSimpleModule.functor
    (R S : Type*) [Ring R] [Ring S] (e : ModuleCat R ≌ ModuleCat S)
    (M : ModuleCat R) [simple_module : IsSimpleModule R M] :
    IsSimpleModule S (e.functor.obj M) := by
  rw [isSimpleModule_iff_injective_or_eq_zero] at simple_module ⊢
  rcases simple_module with ⟨nontriv, H⟩
  refine ⟨e.nontrivial (h := nontriv), fun N _ _ f => ?_⟩
  let F := e.unit.app M ≫ e.inverse.map (ModuleCat.ofHom f)
  rcases H _ F.hom with H | H
  · simp only [Functor.id_obj, ModuleCat.hom_comp, F] at H
    change _ ∘ₗ (e.unitIso.app M).toLinearEquiv.toLinearMap = 0 at H
    rw [eq_comm, ← LinearEquiv.comp_toLinearMap_symm_eq, LinearMap.zero_comp,
      ← ModuleCat.hom_zero, ← ModuleCat.hom_ext_iff, eq_comm] at H
    left
    apply_fun ModuleCat.ofHom using fun _ _ h ↦ by simpa [ModuleCat.hom_ext_iff] using h
    apply e.inverse.map_injective
    rw [H, ModuleCat.ofHom_zero, Functor.map_zero]
    rfl
  · simp only [Functor.id_obj, F] at H
    refine Or.inr ?_
    change Function.Injective (_ ∘ (e.unitIso.app M).toLinearEquiv.toLinearMap) at H
    have := Function.Injective.of_comp_right H <| (e.unitIso.app M).toLinearEquiv.surjective
    exact ModuleCat.mono_iff_injective _|>.1 <| Functor.mono_of_mono_map e.inverse <|
      (ModuleCat.mono_iff_injective (e.inverse.map (ModuleCat.ofHom f))).2 this
