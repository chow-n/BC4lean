import BC4lean.OrderTwoPointKK
import BC4lean.KasparovReducingCompressionFibre
import BC4lean.ProjectionModuleEquiv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The eigenspace splitting is well defined on classes

Fix a finite group `Γ`, a central involution `g` acting trivially on `A`, and a coefficient
action that fixes every element of `B`. Every cycle `c` has a canonical equivariant
representative: symmetrize the operator to `(F + F*)/2`, then average it over `Γ`
(`KasparovCycle.equivariantCycle`). Its compressions to the eigenprojections
`P_s = (1 + s U_g)/2` (`s = ±1`) are the eigen parts `c.eigenPart s`.

This file shows that the eigen parts respect the generating relation of the KK group:

* a cycle isomorphism `c ≅ d` intertwines the canonical operators and the eigenprojections,
  so it restricts to an isomorphism of eigen parts;
* for a full interval homotopy, the fibres of the canonical operator and of the eigenprojections
  of the interval cycle are the canonical operator and the eigenprojections of the fibre, so the
  eigen part of the interval cycle is a full homotopy between the eigen parts of its endpoints.

Hence `c ↦ [c.eigenPart s]` descends to the KK group (`KasparovHomotopyClass.eigenClass`). -/

noncomputable section
universe uΓ uA uB uE uF
namespace BC4lean.KKTheory

open scoped InnerProductSpace

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {E : Type uE} {F : Type uF} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
  [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

/-! ## Isomorphisms restrict to compressions -/

namespace KasparovCycleIso

variable {c : KasparovCycle α β E} {d : KasparovCycle α β F}
  {P : AdjointableMap B E E} {Q : AdjointableMap B F F}

/-- An isomorphism carrying one reducing projection to another restricts to an isomorphism of
the compressions. -/
def compress (u : KasparovCycleIso c d) (hP : c.ReducingProjection P)
    (hQ : d.ReducingProjection Q) (h : ∀ x, u (P x) = Q (u x)) :
    KasparovCycleIso (c.compress hP) (d.compress hQ) where
  moduleEquiv := u.moduleEquiv.restrictProjection P Q h
  grading_intertwine x := Subtype.ext (u.grading_intertwine (x : E))
  action_intertwine g x := Subtype.ext (u.action_intertwine g (x : E))
  representation_intertwine a x := Subtype.ext (by
    change u ((c.compress hP).representation a x : E) =
      ((d.compress hQ).representation a (u.moduleEquiv.restrictProjection P Q h x) : F)
    rw [KasparovCycle.compress_representation_coe, KasparovCycle.compress_representation_coe]
    exact u.representation_intertwine a (x : E))
  operator_intertwine x := Subtype.ext (by
    change u ((c.compress hP).operator x : E) =
      ((d.compress hQ).operator (u.moduleEquiv.restrictProjection P Q h x) : F)
    rw [KasparovCycle.compress_operator_coe, KasparovCycle.compress_operator_coe]
    exact u.operator_intertwine (x : E))

theorem symm_action_intertwine (u : KasparovCycleIso c d) (g : Γ) (y : F) :
    u.moduleEquiv.symm (d.groupAction.action g y) =
      c.groupAction.action g (u.moduleEquiv.symm y) := by
  apply u.moduleEquiv.injective
  rw [HilbertModuleEquiv.apply_symm_apply]
  rw [u.action_intertwine, HilbertModuleEquiv.apply_symm_apply]

/-- An isomorphism intertwines conjugation by the group action. -/
theorem transport_conjugateOperator (u : KasparovCycleIso c d) (g : Γ)
    (T : AdjointableMap B E E) :
    u.moduleEquiv.transport (c.groupAction.conjugateOperator g T) =
      d.groupAction.conjugateOperator g (u.moduleEquiv.transport T) := by
  ext y
  rw [HilbertModuleEquiv.transport_apply]
  change u (c.groupAction.action g (T (c.groupAction.action g⁻¹ (u.moduleEquiv.symm y)))) =
    d.groupAction.action g (u (T (u.moduleEquiv.symm (d.groupAction.action g⁻¹ y))))
  rw [u.action_intertwine, u.symm_action_intertwine]

end KasparovCycleIso

/-! ## The canonical equivariant representative -/

namespace KasparovCycle

variable [Fintype Γ]

/-- The cycle with the symmetrized operator `(F + F*)/2`. -/
def symmetrizedCycle (c : KasparovCycle α β E) : KasparovCycle α β E :=
  c.withOperator (c.operator + c.symmetrizingPerturbation) c.operatorConditions_symmetrization

/-- The canonical equivariant operator: the group average of `(F + F*)/2`. -/
def equivariantOperator (c : KasparovCycle α β E) : AdjointableMap B E E :=
  c.symmetrizedCycle.averagedOperator

theorem operatorConditions_equivariantOperator (c : KasparovCycle α β E) :
    c.OperatorConditions c.equivariantOperator := by
  have h₁ := c.symmetrizedCycle.operatorConditions_averagedOperator
    c.symmetrizedOperator_selfadjoint
  exact ⟨h₁.1, h₁.2, h₁.3, h₁.4, h₁.5⟩

/-- The canonical equivariant representative of a cycle. -/
def equivariantCycle (c : KasparovCycle α β E) : KasparovCycle α β E :=
  c.withOperator c.equivariantOperator c.operatorConditions_equivariantOperator

theorem conjugateOperator_equivariantOperator (c : KasparovCycle α β E) (g : Γ) :
    c.groupAction.conjugateOperator g c.equivariantOperator = c.equivariantOperator :=
  c.symmetrizedCycle.conjugateOperator_averagedOperator g

/-- The canonical representative has the class of the cycle. -/
theorem mk_equivariantCycle (c : KasparovCycle α β E) :
    KasparovHomotopyClass.mk.{uΓ,uA,uB,uE} (BundledKasparovCycle.of c) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of c.equivariantCycle) := by
  have h₀ : KasparovHomotopyClass.mk.{uΓ,uA,uB,uE} (BundledKasparovCycle.of c) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of c.symmetrizedCycle) := by
    have h := KasparovHomotopyClass.mk_eq_of_full
      (FullKasparovHomotopy.ofOperatorHomotopy c.symmetrizationHomotopy)
    rwa [withOperator_self] at h
  exact h₀.trans (c.symmetrizedCycle.mk_averagedCycle c.symmetrizedOperator_selfadjoint)

end KasparovCycle

namespace KasparovCycleIso

variable [Fintype Γ] {c : KasparovCycle α β E} {d : KasparovCycle α β F}

/-- An isomorphism transports the canonical equivariant operator. -/
theorem transport_equivariantOperator (u : KasparovCycleIso c d) :
    u.moduleEquiv.transport c.equivariantOperator = d.equivariantOperator := by
  have hsum : ∀ T : AdjointableMap B E E, u.moduleEquiv.transport
      (∑ g, c.groupAction.conjugateOperator g T) =
        ∑ g, d.groupAction.conjugateOperator g (u.moduleEquiv.transport T) := by
    intro T
    change u.moduleEquiv.transportStarAlgEquiv _ = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun g _ => u.transport_conjugateOperator g T
  simp only [KasparovCycle.equivariantOperator, KasparovCycle.averagedOperator,
    KasparovCycle.symmetrizedCycle, KasparovCycle.withOperator_operator,
    KasparovCycle.withOperator_groupAction, KasparovCycle.symmetrizingPerturbation,
    HilbertModuleEquiv.transport_smul, hsum, HilbertModuleEquiv.transport_add,
    HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_star, u.transport_operator]

/-- An isomorphism of cycles is an isomorphism of their canonical representatives. -/
def equivariantCycle (u : KasparovCycleIso c d) :
    KasparovCycleIso c.equivariantCycle d.equivariantCycle where
  moduleEquiv := u.moduleEquiv
  grading_intertwine := u.grading_intertwine
  action_intertwine := u.action_intertwine
  representation_intertwine := u.representation_intertwine
  operator_intertwine x := by
    change u.moduleEquiv (c.equivariantOperator x) = d.equivariantOperator (u.moduleEquiv x)
    rw [← transport_equivariantOperator u, HilbertModuleEquiv.transport_apply,
      HilbertModuleEquiv.symm_apply_apply]

omit [Fintype Γ] in
/-- An isomorphism intertwines the eigenprojections of the group action. -/
theorem eigenProjection_intertwine [β.IsTrivial] (u : KasparovCycleIso c d) (g : Γ) (s : ℂ)
    (x : E) : u (c.groupAction.eigenProjection g s x) =
      d.groupAction.eigenProjection g s (u x) := by
  simp only [EquivariantHilbertModule.eigenProjection, AdjointableMap.coe_smul_apply,
    AdjointableMap.coe_add_apply, AdjointableMap.one_apply,
    EquivariantHilbertModule.actionOperator_apply, HilbertModuleEquiv.map_smul,
    HilbertModuleEquiv.map_add]
  rw [show u.moduleEquiv (c.groupAction.action g x) = d.groupAction.action g (u x) from
    u.action_intertwine g x]

end KasparovCycleIso

/-! ## Eigen parts -/

/-- A central involution acting trivially on the source algebra. -/
structure CentralInvolution (α : CStarAlgebraAction Γ A) (g : Γ) : Prop where
  mul_self : g * g = 1
  central : ∀ h, h * g = g * h
  fixes : ∀ a, α.automorphism g a = a

namespace KasparovCycle

variable [Fintype Γ] [β.IsTrivial] {g : Γ} (hg : CentralInvolution α g)
  {s : ℂ} (hs : s * s = 1) (hsr : star s = s)

include hg hs hsr in
theorem reducingProjection_equivariantCycle (c : KasparovCycle α β E) :
    c.equivariantCycle.ReducingProjection (c.groupAction.eigenProjection g s) :=
  c.equivariantCycle.reducingProjection_eigenProjection hg.mul_self hg.central hg.fixes
    (c.conjugateOperator_equivariantOperator g) hs hsr

/-- The `s`-eigen part: the compression of the canonical representative to `P_s`. -/
def eigenPart (c : KasparovCycle α β E) :
    KasparovCycle α β (ProjectionModule (c.groupAction.eigenProjection g s)) :=
  c.equivariantCycle.compress (c.reducingProjection_equivariantCycle hg hs hsr)

end KasparovCycle

namespace KasparovCycleIso

variable [Fintype Γ] [β.IsTrivial] {g : Γ} (hg : CentralInvolution α g)
  {s : ℂ} (hs : s * s = 1) (hsr : star s = s)
  {c : KasparovCycle α β E} {d : KasparovCycle α β F}

/-- An isomorphism of cycles restricts to an isomorphism of eigen parts. -/
def eigenPart (u : KasparovCycleIso c d) :
    KasparovCycleIso (c.eigenPart hg hs hsr) (d.eigenPart hg hs hsr) :=
  u.equivariantCycle.compress _ _ (u.eigenProjection_intertwine g s)

end KasparovCycleIso

/-! ## Fibres of interval cycles -/

section Fibre

variable {X M : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

namespace EquivariantHilbertModule

variable [β.IsTrivial] (U : EquivariantHilbertModule (β.continuousSections (X := X)) M)

/-- The fibre of `U_g` is `U_g` on the fibre. -/
theorem fibre_actionOperator (t : X) (g : Γ) :
    hilbertModuleFibreOperator (B := B) t (U.actionOperator g) =
      (U.fibre t).actionOperator g := by
  apply hilbertModuleFibreOperator_ext t
  intro x
  rw [hilbertModuleFibreOperator_mk, actionOperator_apply, actionOperator_apply, fibre_action_mk]

/-- The fibre of an eigenprojection is the eigenprojection on the fibre. -/
theorem fibre_eigenProjection (t : X) (g : Γ) (s : ℂ) :
    hilbertModuleFibreOperator (B := B) t (U.eigenProjection g s) =
      (U.fibre t).eigenProjection g s := by
  simp only [eigenProjection, hilbertModuleFibreOperator_smul, hilbertModuleFibreOperator_add,
    hilbertModuleFibreOperator_one, U.fibre_actionOperator]

end EquivariantHilbertModule

namespace KasparovCycle

variable [Fintype Γ]

/-- The fibre of the canonical equivariant operator is the canonical operator of the fibre. -/
theorem fibre_equivariantOperator (c : KasparovCycle α (β.continuousSections (X := X)) M)
    (t : X) : hilbertModuleFibreOperator (B := B) t c.equivariantOperator =
      (c.fibre t).equivariantOperator := by
  have hsum : ∀ T : AdjointableMap C(X, B) M M, hilbertModuleFibreOperator (B := B) t
      (∑ g, c.groupAction.conjugateOperator g T) =
        ∑ g, (c.fibre t).groupAction.conjugateOperator g (hilbertModuleFibreOperator t T) := by
    intro T
    change hilbertModuleFibreOperatorHom (B := B) (M := M) t _ = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun g _ => (c.groupAction.fibre_conjugateOperator t g T).symm
  simp only [equivariantOperator, averagedOperator, symmetrizedCycle, withOperator_operator,
    withOperator_groupAction, symmetrizingPerturbation, hilbertModuleFibreOperator_smul, hsum,
    hilbertModuleFibreOperator_add, hilbertModuleFibreOperator_sub,
    hilbertModuleFibreOperator_star]
  rfl

/-- The fibre of the canonical representative is the canonical representative of the fibre. -/
def fibreEquivariantCycleIso (c : KasparovCycle α (β.continuousSections (X := X)) M) (t : X) :
    KasparovCycleIso (c.equivariantCycle.fibre t) (c.fibre t).equivariantCycle where
  moduleEquiv := HilbertModuleEquiv.refl (B := B)
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine x := by
    change hilbertModuleFibreOperator (B := B) t c.equivariantOperator x =
      (c.fibre t).equivariantOperator x
    rw [c.fibre_equivariantOperator t]

variable [β.IsTrivial] {g : Γ} (hg : CentralInvolution α g)
  {s : ℂ} (hs : s * s = 1) (hsr : star s = s)

/-- The fibre of an eigen part is the eigen part of the fibre. -/
def fibreEigenPartIso (c : KasparovCycle α (β.continuousSections (X := X)) M) (t : X) :
    KasparovCycleIso ((c.eigenPart hg hs hsr).fibre t) ((c.fibre t).eigenPart hg hs hsr) :=
  (c.equivariantCycle.compressFibreIso (c.reducingProjection_equivariantCycle hg hs hsr) t).trans
    ((c.fibreEquivariantCycleIso t).compress _ _ fun x => by
      change hilbertModuleFibreOperator (B := B) t (c.groupAction.eigenProjection g s) x =
        (c.fibre t).groupAction.eigenProjection g s x
      rw [c.groupAction.fibre_eigenProjection t g s]
      rfl)

end KasparovCycle

end Fibre

/-! ## Descent to classes -/

section EvenDescent

variable [Fintype Γ] [β.IsTrivial] {g : Γ} (hg : CentralInvolution α g)
  {s : ℂ} (hs : s * s = 1) (hsr : star s = s)

namespace FullKasparovHomotopy

/-- The eigen part of the interval cycle of a full homotopy is a full homotopy between the
eigen parts of its endpoints. -/
def eigenPart {c d : BundledKasparovCycle.{uΓ, uA, uB, uE} α β}
    (h : FullKasparovHomotopy c d) :
    FullKasparovHomotopy (BundledKasparovCycle.of (c.cycle.eigenPart hg hs hsr))
      (BundledKasparovCycle.of (d.cycle.eigenPart hg hs hsr)) where
  intervalCycle := BundledKasparovCycle.of (h.intervalCycle.cycle.eigenPart hg hs hsr)
  sourceIso := (h.intervalCycle.cycle.fibreEigenPartIso hg hs hsr 0).trans
    (h.sourceIso.eigenPart hg hs hsr)
  targetIso := (h.intervalCycle.cycle.fibreEigenPartIso hg hs hsr 1).trans
    (h.targetIso.eigenPart hg hs hsr)

end FullKasparovHomotopy

namespace KasparovHomotopyClass

/-- The class of the `s`-eigen part; well defined because eigen parts respect cycle
isomorphisms and full homotopies. -/
def eigenClass :
    KasparovHomotopyClass.{uΓ, uA, uB, uE} α β → KasparovHomotopyClass.{uΓ, uA, uB, uE} α β :=
  Quotient.lift (fun c => mk (BundledKasparovCycle.of (c.cycle.eigenPart hg hs hsr)))
    (fun c d h => by
      change BundledKasparovCycle.Homotopic c d at h
      induction h with
      | rel a b h =>
          change a.Isomorphic b ∨ Nonempty (FullKasparovHomotopy a b) at h
          rcases h with h | h
          · obtain ⟨u⟩ := h
            exact mk_eq_of_iso (u.eigenPart hg hs hsr)
          · obtain ⟨h⟩ := h
            exact mk_eq_of_full (h.eigenPart hg hs hsr)
      | refl => rfl
      | symm a b _ ih => exact ih.symm
      | trans a b k _ _ hab hbk => exact hab.trans hbk)

@[simp] theorem eigenClass_mk (c : BundledKasparovCycle.{uΓ, uA, uB, uE} α β) :
    eigenClass hg hs hsr (mk c) = mk (BundledKasparovCycle.of (c.cycle.eigenPart hg hs hsr)) :=
  rfl

/-- Every class is the sum of its `+1` and `-1` eigen classes. -/
theorem eigenClass_add_eigenClass
    (x : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β) :
    eigenClass hg (s := 1) (by norm_num) (by simp) x +
      eigenClass hg (s := -1) (by norm_num) (by simp) x = x := by
  induction x using Quotient.inductionOn with
  | h c =>
    change mk _ + mk _ = mk c
    have hP := c.cycle.reducingProjection_equivariantCycle hg (s := 1) (by norm_num) (by simp)
    have hm : mk.{uΓ, uA, uB, uE} (BundledKasparovCycle.of (c.cycle.equivariantCycle.compress
        hP.one_sub)) =
        mk (BundledKasparovCycle.of (c.cycle.eigenPart hg (s := -1) (by norm_num) (by simp))) :=
      mk_eq_of_iso ((KasparovCycleIso.refl c.cycle.equivariantCycle).compress hP.one_sub _
        fun x => by
          change (1 - c.cycle.groupAction.eigenProjection g 1) x =
            c.cycle.groupAction.eigenProjection g (-1) x
          rw [c.cycle.groupAction.one_sub_eigenProjection])
    rw [← hm]
    exact ((c.cycle.mk_equivariantCycle.trans
      (c.cycle.equivariantCycle.mk_eq_add_compress hP))).symm

end KasparovHomotopyClass

end EvenDescent

/-! ## Odd cycles

The same construction without the grading. -/

section Odd

namespace OddKasparovCycleIso

variable {c : OddKasparovCycle α β E} {d : OddKasparovCycle α β F}
  {P : AdjointableMap B E E} {Q : AdjointableMap B F F}

/-- An isomorphism carrying one reducing projection to another restricts to the compressions. -/
def compress (u : OddKasparovCycleIso c d) (hP : c.ReducingProjection P)
    (hQ : d.ReducingProjection Q) (h : ∀ x, u.moduleEquiv (P x) = Q (u.moduleEquiv x)) :
    OddKasparovCycleIso (c.compress hP) (d.compress hQ) where
  moduleEquiv := u.moduleEquiv.restrictProjection P Q h
  action_intertwine g x := Subtype.ext (u.action_intertwine g (x : E))
  representation_intertwine a x := Subtype.ext (by
    change u.moduleEquiv ((c.compress hP).representation a x : E) =
      ((d.compress hQ).representation a (u.moduleEquiv.restrictProjection P Q h x) : F)
    rw [OddKasparovCycle.compress_representation_coe,
      OddKasparovCycle.compress_representation_coe]
    exact u.representation_intertwine a (x : E))
  operator_intertwine x := Subtype.ext (by
    change u.moduleEquiv ((c.compress hP).operator x : E) =
      ((d.compress hQ).operator (u.moduleEquiv.restrictProjection P Q h x) : F)
    rw [OddKasparovCycle.compress_operator_coe, OddKasparovCycle.compress_operator_coe]
    exact u.operator_intertwine (x : E))

theorem transport_operator (u : OddKasparovCycleIso c d) :
    u.moduleEquiv.transport c.operator = d.operator := by
  ext y
  rw [HilbertModuleEquiv.transport_apply, u.operator_intertwine,
    HilbertModuleEquiv.apply_symm_apply]

theorem symm_action_intertwine (u : OddKasparovCycleIso c d) (g : Γ) (y : F) :
    u.moduleEquiv.symm (d.groupAction.action g y) =
      c.groupAction.action g (u.moduleEquiv.symm y) := by
  apply u.moduleEquiv.injective
  rw [HilbertModuleEquiv.apply_symm_apply, u.action_intertwine,
    HilbertModuleEquiv.apply_symm_apply]

theorem transport_conjugateOperator (u : OddKasparovCycleIso c d) (g : Γ)
    (T : AdjointableMap B E E) :
    u.moduleEquiv.transport (c.groupAction.conjugateOperator g T) =
      d.groupAction.conjugateOperator g (u.moduleEquiv.transport T) := by
  ext y
  rw [HilbertModuleEquiv.transport_apply]
  change u.moduleEquiv (c.groupAction.action g
      (T (c.groupAction.action g⁻¹ (u.moduleEquiv.symm y)))) =
    d.groupAction.action g (u.moduleEquiv (T (u.moduleEquiv.symm (d.groupAction.action g⁻¹ y))))
  rw [u.action_intertwine, u.symm_action_intertwine]

end OddKasparovCycleIso

namespace OddKasparovCycle

variable [Fintype Γ]

/-- The canonical equivariant operator: the group average of `(F + F*)/2`. -/
def equivariantOperator (c : OddKasparovCycle α β E) : AdjointableMap B E E :=
  c.symmetrized.averagedOperator

theorem operatorConditions_equivariantOperator (c : OddKasparovCycle α β E) :
    c.OperatorConditions c.equivariantOperator := by
  have h₁ := c.symmetrized.operatorConditions_averagedOperator c.symmetrizedOperator_selfadjoint
  exact ⟨h₁.1, h₁.2, h₁.3, h₁.4⟩

/-- The canonical equivariant representative of an odd cycle. -/
def equivariantCycle (c : OddKasparovCycle α β E) : OddKasparovCycle α β E :=
  c.withOperator c.equivariantOperator c.operatorConditions_equivariantOperator

theorem conjugateOperator_equivariantOperator (c : OddKasparovCycle α β E) (g : Γ) :
    c.groupAction.conjugateOperator g c.equivariantOperator = c.equivariantOperator :=
  c.symmetrized.conjugateOperator_averagedOperator g

/-- The canonical representative has the class of the cycle. -/
theorem mk_equivariantCycle [TopologicalSpace.SeparableSpace B] (c : OddKasparovCycle α β E) :
    OddKK.mk.{uΓ,uA,uB,uE} (BundledOddKasparovCycle.of c) =
      OddKK.mk (BundledOddKasparovCycle.of c.equivariantCycle) := by
  have h₀ : OddKK.mk.{uΓ,uA,uB,uE} (BundledOddKasparovCycle.of c) =
      OddKK.mk (BundledOddKasparovCycle.of c.symmetrized) := by
    have h := OddKK.mk_eq_of_full
      (FullOddKasparovHomotopy.ofOperatorHomotopy c.symmetrizationHomotopy)
    rwa [withOperator_self] at h
  exact h₀.trans (c.symmetrized.mk_averagedCycle c.symmetrizedOperator_selfadjoint)

end OddKasparovCycle

namespace OddKasparovCycleIso

variable [Fintype Γ] {c : OddKasparovCycle α β E} {d : OddKasparovCycle α β F}

theorem transport_equivariantOperator (u : OddKasparovCycleIso c d) :
    u.moduleEquiv.transport c.equivariantOperator = d.equivariantOperator := by
  have hsum : ∀ T : AdjointableMap B E E, u.moduleEquiv.transport
      (∑ g, c.groupAction.conjugateOperator g T) =
        ∑ g, d.groupAction.conjugateOperator g (u.moduleEquiv.transport T) := by
    intro T
    change u.moduleEquiv.transportStarAlgEquiv _ = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun g _ => u.transport_conjugateOperator g T
  simp only [OddKasparovCycle.equivariantOperator, OddKasparovCycle.averagedOperator,
    OddKasparovCycle.symmetrized, OddKasparovCycle.withOperator_operator,
    OddKasparovCycle.withOperator_groupAction, OddKasparovCycle.symmetrizingPerturbation,
    HilbertModuleEquiv.transport_smul, hsum, HilbertModuleEquiv.transport_add,
    HilbertModuleEquiv.transport_sub, HilbertModuleEquiv.transport_star, u.transport_operator]

/-- An isomorphism of odd cycles is an isomorphism of their canonical representatives. -/
def equivariantCycle (u : OddKasparovCycleIso c d) :
    OddKasparovCycleIso c.equivariantCycle d.equivariantCycle where
  moduleEquiv := u.moduleEquiv
  action_intertwine := u.action_intertwine
  representation_intertwine := u.representation_intertwine
  operator_intertwine x := by
    change u.moduleEquiv (c.equivariantOperator x) = d.equivariantOperator (u.moduleEquiv x)
    rw [← transport_equivariantOperator u, HilbertModuleEquiv.transport_apply,
      HilbertModuleEquiv.symm_apply_apply]

omit [Fintype Γ] in
theorem eigenProjection_intertwine [β.IsTrivial] (u : OddKasparovCycleIso c d) (g : Γ)
    (s : ℂ) (x : E) : u.moduleEquiv (c.groupAction.eigenProjection g s x) =
      d.groupAction.eigenProjection g s (u.moduleEquiv x) := by
  simp only [EquivariantHilbertModule.eigenProjection, AdjointableMap.coe_smul_apply,
    AdjointableMap.coe_add_apply, AdjointableMap.one_apply,
    EquivariantHilbertModule.actionOperator_apply, HilbertModuleEquiv.map_smul,
    HilbertModuleEquiv.map_add, u.action_intertwine]

end OddKasparovCycleIso

namespace OddKasparovCycle

variable [Fintype Γ] [β.IsTrivial] {g : Γ} (hg : CentralInvolution α g)
  {s : ℂ} (hs : s * s = 1) (hsr : star s = s)

include hg hs hsr in
theorem reducingProjection_equivariantCycle (c : OddKasparovCycle α β E) :
    c.equivariantCycle.ReducingProjection (c.groupAction.eigenProjection g s) :=
  c.equivariantCycle.reducingProjection_eigenProjection hg.mul_self hg.central hg.fixes
    (c.conjugateOperator_equivariantOperator g) hs hsr

/-- The `s`-eigen part of an odd cycle. -/
def eigenPart (c : OddKasparovCycle α β E) :
    OddKasparovCycle α β (ProjectionModule (c.groupAction.eigenProjection g s)) :=
  c.equivariantCycle.compress (c.reducingProjection_equivariantCycle hg hs hsr)

end OddKasparovCycle

namespace OddKasparovCycleIso

variable [Fintype Γ] [β.IsTrivial] {g : Γ} (hg : CentralInvolution α g)
  {s : ℂ} (hs : s * s = 1) (hsr : star s = s)
  {c : OddKasparovCycle α β E} {d : OddKasparovCycle α β F}

/-- An isomorphism of odd cycles restricts to an isomorphism of eigen parts. -/
def eigenPart (u : OddKasparovCycleIso c d) :
    OddKasparovCycleIso (c.eigenPart hg hs hsr) (d.eigenPart hg hs hsr) :=
  u.equivariantCycle.compress _ _ (u.eigenProjection_intertwine g s)

end OddKasparovCycleIso

section Fibre

variable {X M : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup M] [NormedSpace ℂ M]
  [SMul C(X, B)ᵐᵒᵖ M] [CStarModule C(X, B)ᵐᵒᵖ M] [CompleteSpace M]

namespace OddKasparovCycle

variable [Fintype Γ]

theorem fibre_equivariantOperator (c : OddKasparovCycle α (β.continuousSections (X := X)) M)
    (t : X) : hilbertModuleFibreOperator (B := B) t c.equivariantOperator =
      (c.fibre t).equivariantOperator := by
  have hsum : ∀ T : AdjointableMap C(X, B) M M, hilbertModuleFibreOperator (B := B) t
      (∑ g, c.groupAction.conjugateOperator g T) =
        ∑ g, (c.fibre t).groupAction.conjugateOperator g (hilbertModuleFibreOperator t T) := by
    intro T
    change hilbertModuleFibreOperatorHom (B := B) (M := M) t _ = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun g _ => (c.groupAction.fibre_conjugateOperator t g T).symm
  simp only [equivariantOperator, averagedOperator, symmetrized, withOperator_operator,
    withOperator_groupAction, symmetrizingPerturbation, hilbertModuleFibreOperator_smul, hsum,
    hilbertModuleFibreOperator_add, hilbertModuleFibreOperator_sub,
    hilbertModuleFibreOperator_star]
  rfl

/-- The fibre of the canonical representative is the canonical representative of the fibre. -/
def fibreEquivariantCycleIso (c : OddKasparovCycle α (β.continuousSections (X := X)) M)
    (t : X) : OddKasparovCycleIso (c.equivariantCycle.fibre t) (c.fibre t).equivariantCycle where
  moduleEquiv := HilbertModuleEquiv.refl (B := B)
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine x := by
    change hilbertModuleFibreOperator (B := B) t c.equivariantOperator x =
      (c.fibre t).equivariantOperator x
    rw [c.fibre_equivariantOperator t]

variable [β.IsTrivial] {g : Γ} (hg : CentralInvolution α g)
  {s : ℂ} (hs : s * s = 1) (hsr : star s = s)

/-- The fibre of an odd eigen part is the eigen part of the fibre. -/
def fibreEigenPartIso (c : OddKasparovCycle α (β.continuousSections (X := X)) M) (t : X) :
    OddKasparovCycleIso ((c.eigenPart hg hs hsr).fibre t) ((c.fibre t).eigenPart hg hs hsr) :=
  (c.equivariantCycle.compressFibreIso (c.reducingProjection_equivariantCycle hg hs hsr) t).trans
    ((c.fibreEquivariantCycleIso t).compress _ _ fun x => by
      change hilbertModuleFibreOperator (B := B) t (c.groupAction.eigenProjection g s) x =
        (c.fibre t).groupAction.eigenProjection g s x
      rw [c.groupAction.fibre_eigenProjection t g s]
      rfl)

end OddKasparovCycle

end Fibre

variable [Fintype Γ] [β.IsTrivial] {g : Γ} (hg : CentralInvolution α g)
  {s : ℂ} (hs : s * s = 1) (hsr : star s = s) [TopologicalSpace.SeparableSpace B]

namespace FullOddKasparovHomotopy

/-- The eigen part of an odd full homotopy. -/
def eigenPart {c d : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β}
    (h : FullOddKasparovHomotopy c d) :
    FullOddKasparovHomotopy (BundledOddKasparovCycle.of (c.cycle.eigenPart hg hs hsr))
      (BundledOddKasparovCycle.of (d.cycle.eigenPart hg hs hsr)) where
  intervalCycle := BundledOddKasparovCycle.of (h.intervalCycle.cycle.eigenPart hg hs hsr)
  sourceIso := (h.intervalCycle.cycle.fibreEigenPartIso hg hs hsr 0).trans
    (h.sourceIso.eigenPart hg hs hsr)
  targetIso := (h.intervalCycle.cycle.fibreEigenPartIso hg hs hsr 1).trans
    (h.targetIso.eigenPart hg hs hsr)

end FullOddKasparovHomotopy

namespace OddKK

/-- The class of the `s`-eigen part of an odd cycle. -/
def eigenClass : OddKK.{uΓ, uA, uB, uE} α β → OddKK.{uΓ, uA, uB, uE} α β :=
  Quotient.lift (fun c => mk (BundledOddKasparovCycle.of (c.cycle.eigenPart hg hs hsr)))
    (fun _ _ h => by
      obtain ⟨h⟩ := h
      exact Quotient.sound ⟨h.eigenPart hg hs hsr⟩)

@[simp] theorem eigenClass_mk (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE} α β) :
    eigenClass hg hs hsr (mk c) =
      mk (BundledOddKasparovCycle.of (c.cycle.eigenPart hg hs hsr)) :=
  rfl

/-- Every odd class is the sum of its `+1` and `-1` eigen classes. -/
theorem eigenClass_add_eigenClass
    (x : OddKK.{uΓ, uA, uB, uE} α β) :
    eigenClass hg (s := 1) (by norm_num) (by simp) x +
      eigenClass hg (s := -1) (by norm_num) (by simp) x = x := by
  induction x using Quotient.inductionOn with
  | h c =>
    change mk _ + mk _ = mk c
    have hP := c.cycle.reducingProjection_equivariantCycle hg (s := 1) (by norm_num) (by simp)
    have hm : mk.{uΓ, uA, uB, uE} (BundledOddKasparovCycle.of
        (c.cycle.equivariantCycle.compress hP.one_sub)) =
        mk (BundledOddKasparovCycle.of
          (c.cycle.eigenPart hg (s := -1) (by norm_num) (by simp))) :=
      mk_eq_of_iso ((OddKasparovCycleIso.refl c.cycle.equivariantCycle).compress hP.one_sub _
        fun x => by
          change (1 - c.cycle.groupAction.eigenProjection g 1) x =
            c.cycle.groupAction.eigenProjection g (-1) x
          rw [c.cycle.groupAction.one_sub_eigenProjection])
    rw [← hm]
    exact ((c.cycle.mk_equivariantCycle.trans
      (c.cycle.equivariantCycle.mk_eq_add_compress hP))).symm

end OddKK

end Odd

end BC4lean.KKTheory
