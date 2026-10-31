import BC4lean.KasparovFiniteAveraging
import BC4lean.KasparovGroupChange
import BC4lean.GroupUniverseParityGroup
import BC4lean.GroupUniverseParityFunctoriality
import BC4lean.CZeroAlgebra
import BC4lean.UnitPointCutoff

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Restriction, inflation and twists for trivial actions

Let `Γ` act trivially on `A` and on `B`. Write `KK^Γ` for the even (resp. odd) KK group of
`Γ`-equivariant cycles and `UnitKK` for the group over the trivial group with trivial actions.

* `res : KK^Γ → KK` reads a cycle over the trivial group (pull back along `Unit →* Γ`,
  `KasparovHomotopyClass.resHom`, `OddKK.resHom`);
* `infl : KK → KK^Γ` lets `Γ` act trivially on the module (pull back along `Γ →* Unit`,
  `inflHom`);
* `res ∘ infl = id`, and `res ∘ twist χ ∘ infl = id` for every character `χ : Γ →* U(1)`
  (`resHom_inflHom`, `resHom_twist_inflHom`); on cycles, if every `h` acts by the scalar `ψ h`,
  then inflating the restriction and twisting by `ψ` gives back the cycle (`inflResIso`).

The action of `Γ` on `C₀(X)` for a one-point space `X` is trivial (`CZero.isTrivial_action`), and
`C₀(X)` is separable (`cZero_separableSpace_of_subsingleton`). An equivariant `*`-isomorphism
`e : A ≃⋆ₐ B` gives an additive equivalence `KK^Γ_p(B, C) ≃+ KK^Γ_p(A, C)` (`sourcePullbackEquiv`;
pullback along `e`, inverse pullback along `e.symm`). -/

noncomputable section
universe uΓ uA uB uC uE u
namespace BC4lean.KKTheory

open scoped InnerProductSpace

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {E : Type uE} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

/-! ## Compatibility of the trivial actions with `Unit →* Γ` and `Γ →* Unit` -/

namespace CStarAlgebraAction

variable {C : Type*} [NonUnitalCStarAlgebra C]

theorem trivial_unit_apply (γ : CStarAlgebraAction Γ C) (h : Unit) (c : C) :
    (CStarAlgebraAction.trivial : CStarAlgebraAction Unit C).automorphism h c =
      γ.automorphism ((1 : Unit →* Γ) h) c := by
  simp [CStarAlgebraAction.trivial]

theorem apply_eq_trivial_unit (γ : CStarAlgebraAction Γ C) [γ.IsTrivial] (h : Γ) (c : C) :
    γ.automorphism h c =
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit C).automorphism
        ((1 : Γ →* Unit) h) c := by
  rw [CStarAlgebraAction.IsTrivial.apply_eq]
  simp [CStarAlgebraAction.trivial]

end CStarAlgebraAction

/-! ## Cycle-level facts -/

omit [StarOrderedRing B] [CompleteSpace E] in
/-- A projection that vanishes has the zero module as its range. -/
theorem projectionModule_subsingleton_of_eq_zero {P : AdjointableMap B E E} (hP : P = 0) :
    Subsingleton (ProjectionModule P) :=
  ⟨fun x y => Subtype.ext (by
    have hx : P (x : E) = x := x.property
    have hy : P (y : E) = y := y.property
    have h0 : ∀ z : E, P z = 0 := fun z => by rw [hP]; rfl
    rw [← hx, ← hy, h0, h0])⟩

/-! ## Restriction, inflation and the twist on cycles -/

section Change

variable [α.IsTrivial] [β.IsTrivial]

namespace KasparovCycle

/-- Restrict to the trivial group, then inflate and twist by `ψ`: if every `h` already acts by
the scalar `ψ h`, this gives back the cycle. -/
def inflResIso (c : KasparovCycle α β E) (ψ : Γ →* unitary ℂ)
    (hc : ∀ h x, c.groupAction.action h x = ((ψ h : unitary ℂ) : ℂ) • x) :
    KasparovCycleIso (((c.comap (1 : Unit →* Γ) (CStarAlgebraAction.trivial_unit_apply α)
      (CStarAlgebraAction.trivial_unit_apply β)).comap (1 : Γ →* Unit)
      (CStarAlgebraAction.apply_eq_trivial_unit α)
      (CStarAlgebraAction.apply_eq_trivial_unit β)).twist ψ) c where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine h x := by
    change ((ψ h : unitary ℂ) : ℂ) •
      c.groupAction.action ((1 : Unit →* Γ) ((1 : Γ →* Unit) h)) x = c.groupAction.action h x
    rw [MonoidHom.one_apply, EquivariantHilbertModule.one_apply, hc]
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

variable (c : KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit A)
  (CStarAlgebraAction.trivial : CStarAlgebraAction Unit B) E)

/-- Inflating a cycle over the trivial group and restricting it back gives the cycle. -/
def resInflIso :
    KasparovCycleIso ((c.comap (1 : Γ →* Unit) (CStarAlgebraAction.apply_eq_trivial_unit α)
      (CStarAlgebraAction.apply_eq_trivial_unit β)).comap (1 : Unit →* Γ)
      (CStarAlgebraAction.trivial_unit_apply α) (CStarAlgebraAction.trivial_unit_apply β)) c where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

/-- Inflating, twisting and restricting back gives the cycle. -/
def resTwistInflIso (ψ : Γ →* unitary ℂ) :
    KasparovCycleIso (((c.comap (1 : Γ →* Unit) (CStarAlgebraAction.apply_eq_trivial_unit α)
      (CStarAlgebraAction.apply_eq_trivial_unit β)).twist ψ).comap (1 : Unit →* Γ)
      (CStarAlgebraAction.trivial_unit_apply α) (CStarAlgebraAction.trivial_unit_apply β)) c where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine h x := by
    change ((ψ ((1 : Unit →* Γ) h) : unitary ℂ) : ℂ) •
      c.groupAction.action ((1 : Γ →* Unit) ((1 : Unit →* Γ) h)) x = c.groupAction.action h x
    rw [MonoidHom.one_apply, map_one, OneMemClass.coe_one, one_smul]
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

end KasparovCycle

end Change

/-! ## Restriction and inflation of even classes -/

section EvenClasses

variable [Fintype Γ] [α.IsTrivial] [β.IsTrivial] (χ : Γ →* unitary ℂ)

namespace KasparovHomotopyClass

variable (A B) in
/-- Even KK over the trivial group with trivial actions. -/
abbrev UnitKK := KasparovHomotopyClass.{0, uA, uB, uE}
  (CStarAlgebraAction.trivial : CStarAlgebraAction Unit A)
  (CStarAlgebraAction.trivial : CStarAlgebraAction Unit B)

/-- Restriction to the trivial group. -/
def resHom : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β →+ UnitKK.{uA, uB, uE} A B :=
  comap (1 : Unit →* Γ) (CStarAlgebraAction.trivial_unit_apply α)
    (CStarAlgebraAction.trivial_unit_apply β)

/-- Inflation from the trivial group: `Γ` acts trivially on the module. -/
def inflHom : UnitKK.{uA, uB, uE} A B →+ KasparovHomotopyClass.{uΓ, uA, uB, uE} α β :=
  comap (1 : Γ →* Unit) (CStarAlgebraAction.apply_eq_trivial_unit α)
    (CStarAlgebraAction.apply_eq_trivial_unit β)

omit [Fintype Γ] in
theorem resHom_inflHom (a : UnitKK.{uA, uB, uE} A B) :
    resHom (α := α) (β := β) (inflHom a) = a := by
  induction a using Quotient.inductionOn with
  | h c => exact mk_eq_of_iso (c.cycle.resInflIso (Γ := Γ))

omit [Fintype Γ] in
theorem resHom_twist_inflHom (b : UnitKK.{uA, uB, uE} A B) :
    resHom (α := α) (β := β) (twist χ (inflHom b)) = b := by
  induction b using Quotient.inductionOn with
  | h c => exact mk_eq_of_iso (c.cycle.resTwistInflIso χ)

end KasparovHomotopyClass

end EvenClasses

/-! ## Odd cycles -/

section OddChange

variable [α.IsTrivial] [β.IsTrivial]

namespace OddKasparovCycle

/-- Restrict to the trivial group, then inflate and twist by `ψ`: if every `h` already acts by
the scalar `ψ h`, this gives back the cycle. -/
def inflResIso (c : OddKasparovCycle α β E) (ψ : Γ →* unitary ℂ)
    (hc : ∀ h x, c.groupAction.action h x = ((ψ h : unitary ℂ) : ℂ) • x) :
    OddKasparovCycleIso (((c.comap (1 : Unit →* Γ) (CStarAlgebraAction.trivial_unit_apply α)
      (CStarAlgebraAction.trivial_unit_apply β)).comap (1 : Γ →* Unit)
      (CStarAlgebraAction.apply_eq_trivial_unit α)
      (CStarAlgebraAction.apply_eq_trivial_unit β)).twist ψ) c where
  moduleEquiv := HilbertModuleEquiv.refl
  action_intertwine h x := by
    change ((ψ h : unitary ℂ) : ℂ) •
      c.groupAction.action ((1 : Unit →* Γ) ((1 : Γ →* Unit) h)) x = c.groupAction.action h x
    rw [MonoidHom.one_apply, EquivariantHilbertModule.one_apply, hc]
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

variable (c : OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit A)
  (CStarAlgebraAction.trivial : CStarAlgebraAction Unit B) E)

/-- Inflating a cycle over the trivial group and restricting it back gives the cycle. -/
def resInflIso :
    OddKasparovCycleIso ((c.comap (1 : Γ →* Unit) (CStarAlgebraAction.apply_eq_trivial_unit α)
      (CStarAlgebraAction.apply_eq_trivial_unit β)).comap (1 : Unit →* Γ)
      (CStarAlgebraAction.trivial_unit_apply α) (CStarAlgebraAction.trivial_unit_apply β)) c where
  moduleEquiv := HilbertModuleEquiv.refl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

/-- Inflating, twisting and restricting back gives the cycle. -/
def resTwistInflIso (ψ : Γ →* unitary ℂ) :
    OddKasparovCycleIso (((c.comap (1 : Γ →* Unit) (CStarAlgebraAction.apply_eq_trivial_unit α)
      (CStarAlgebraAction.apply_eq_trivial_unit β)).twist ψ).comap (1 : Unit →* Γ)
      (CStarAlgebraAction.trivial_unit_apply α) (CStarAlgebraAction.trivial_unit_apply β)) c where
  moduleEquiv := HilbertModuleEquiv.refl
  action_intertwine h x := by
    change ((ψ ((1 : Unit →* Γ) h) : unitary ℂ) : ℂ) •
      c.groupAction.action ((1 : Γ →* Unit) ((1 : Unit →* Γ) h)) x = c.groupAction.action h x
    rw [MonoidHom.one_apply, map_one, OneMemClass.coe_one, one_smul]
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

end OddKasparovCycle

end OddChange

section OddClasses

variable [Fintype Γ] [α.IsTrivial] [β.IsTrivial] (χ : Γ →* unitary ℂ)

namespace OddKK

variable [TopologicalSpace.SeparableSpace B]

variable (A B) in
/-- Odd KK over the trivial group with trivial actions. -/
abbrev UnitKK := OddKK.{0, uA, uB, uE}
  (CStarAlgebraAction.trivial : CStarAlgebraAction Unit A)
  (CStarAlgebraAction.trivial : CStarAlgebraAction Unit B)

/-- Restriction to the trivial group. -/
def resHom : OddKK.{uΓ, uA, uB, uE} α β →+ UnitKK.{uA, uB, uE} A B :=
  comap (1 : Unit →* Γ) (CStarAlgebraAction.trivial_unit_apply α)
    (CStarAlgebraAction.trivial_unit_apply β)

/-- Inflation from the trivial group: `Γ` acts trivially on the module. -/
def inflHom : UnitKK.{uA, uB, uE} A B →+ OddKK.{uΓ, uA, uB, uE} α β :=
  comap (1 : Γ →* Unit) (CStarAlgebraAction.apply_eq_trivial_unit α)
    (CStarAlgebraAction.apply_eq_trivial_unit β)

omit [Fintype Γ] in
theorem resHom_inflHom (a : UnitKK.{uA, uB, uE} A B) :
    resHom (α := α) (β := β) (inflHom a) = a := by
  induction a using Quotient.inductionOn with
  | h c => exact mk_eq_of_iso (c.cycle.resInflIso (Γ := Γ))

omit [Fintype Γ] in
theorem resHom_twist_inflHom (b : UnitKK.{uA, uB, uE} A B) :
    resHom (α := α) (β := β) (twist χ (inflHom b)) = b := by
  induction b using Quotient.inductionOn with
  | h c => exact mk_eq_of_iso (c.cycle.resTwistInflIso χ)

end OddKK

end OddClasses

section CZeroTrivial

open GroupUniverseParityGroup

/-- On a space with at most one point, the induced action on `C₀(X)` is trivial. -/
instance CZero.isTrivial_action {X : Type*} [TopologicalSpace X] [Subsingleton X] [MulAction Γ X]
    [ContinuousConstSMul Γ X] : (CZero.action Γ (X := X)).IsTrivial :=
  ⟨fun g a => by
    ext x
    rw [CZero.action_apply, Subsingleton.elim (g⁻¹ • x) x]⟩

end CZeroTrivial

/-! ## Pullback along an isomorphism of sources; one-point sources -/

open GroupUniverseParityGroup GroupUniverseParityFunctoriality

section Equiv
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

omit [PartialOrder A] [StarOrderedRing A] in
theorem sourcePullback_congr (p : Bool) {f f' : A →⋆ₙₐ[ℂ] B} (h : f = f')
    (hact : ∀ k a, f (α.automorphism k a) = β.automorphism k (f a))
    (hact' : ∀ k a, f' (α.automorphism k a) = β.automorphism k (f' a))
    (x : KKParityGroup.{uΓ,uB,uC,max u (max uA (max uB uC))} p β γ) :
    sourcePullback.{uΓ,uA,uB,uC,u} p f hact x = sourcePullback.{uΓ,uA,uB,uC,u} p f' hact' x := by
  subst h; rfl

/-- An equivariant `*`-isomorphism of sources gives an additive equivalence of KK groups. -/
def sourcePullbackEquiv (p : Bool) (e : A ≃⋆ₐ[ℂ] B)
    (hact : ∀ k a, e (α.automorphism k a) = β.automorphism k (e a)) :
    KKParityGroup.{uΓ,uB,uC,max u (max uA (max uB uC))} p β γ ≃+
      KKParityGroup.{uΓ,uA,uC,max u (max uA (max uB uC))} p α γ where
  toFun := sourcePullback.{uΓ,uA,uB,uC,max u (max uA uB)} p (e : A →⋆ₙₐ[ℂ] B) hact
  invFun := sourcePullback.{uΓ,uB,uA,uC,max u (max uA uB)} p (e.symm : B →⋆ₙₐ[ℂ] A) fun k b => by
    apply EquivLike.injective e
    change e (e.symm _) = e (α.automorphism k (e.symm b))
    rw [hact, e.apply_symm_apply, e.apply_symm_apply]
  left_inv x := by
    refine (sourcePullback_comp.{uΓ,uB,uA,uB,uC,max u uA} p (e.symm : B →⋆ₙₐ[ℂ] A)
      (e : A →⋆ₙₐ[ℂ] B) _ hact x).trans ?_
    refine (sourcePullback_congr.{uΓ,uB,uB,uC,max u uA} p (f' := NonUnitalStarAlgHom.id ℂ B)
      (by ext b; exact e.apply_symm_apply b) _ (fun _ _ => rfl) x).trans ?_
    exact sourcePullback_id.{uΓ,uB,uC,max u uA} p x
  right_inv x := by
    refine (sourcePullback_comp.{uΓ,uA,uB,uA,uC,max u uB} p (e : A →⋆ₙₐ[ℂ] B)
      (e.symm : B →⋆ₙₐ[ℂ] A) hact _ x).trans ?_
    refine (sourcePullback_congr.{uΓ,uA,uA,uC,max u uB} p (f' := NonUnitalStarAlgHom.id ℂ A)
      (by ext a; exact e.symm_apply_apply a) _ (fun _ _ => rfl) x).trans ?_
    exact sourcePullback_id.{uΓ,uA,uC,max u uB} p x
  map_add' := sourcePullback_add.{uΓ,uA,uB,uC,max u (max uA uB)} p _ hact

end Equiv

section Point

open UnitPointCutoff
open scoped ZeroAtInfty ComplexOrder

variable {Γ : Type uΓ} [Group Γ] (X : Type) [TopologicalSpace X] [Subsingleton X] [MulAction Γ X]
  [ContinuousConstSMul Γ X]

/-- `C₀` of a one-point space is separable: it is the image of `ℂ` under `pointCZeroEquiv`. -/
theorem cZero_separableSpace_of_subsingleton (x : X) : TopologicalSpace.SeparableSpace C₀(X, ℂ) :=
  (pointCZeroEquiv X x).surjective.denseRange.separableSpace
    (LinearMap.continuous_of_finiteDimensional (LinearMap.mk ⟨pointCZeroEquiv X x,
      map_add (pointCZeroEquiv X x)⟩ (map_smul (pointCZeroEquiv X x)) : ℂ →ₗ[ℂ] C₀(X, ℂ)))

end Point

end BC4lean.KKTheory
