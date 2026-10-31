import BC4lean.OrderTwoPointKK
import BC4lean.KasparovEquivariantRepresentative

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

namespace KasparovCycleIso

variable [Fintype Γ] {c : KasparovCycle α β E} {d : KasparovCycle α β F}

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

/-- The fibre of an eigenprojection is the eigenprojection on the fibre. -/
theorem fibre_eigenProjection (t : X) (g : Γ) (s : ℂ) :
    hilbertModuleFibreOperator (B := B) t (U.eigenProjection g s) =
      (U.fibre t).eigenProjection g s := by
  simp only [eigenProjection, hilbertModuleFibreOperator_smul, hilbertModuleFibreOperator_add,
    hilbertModuleFibreOperator_one, U.fibre_actionOperator]

end EquivariantHilbertModule

namespace KasparovCycle

variable [Fintype Γ]

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

variable [Fintype Γ] {c : OddKasparovCycle α β E} {d : OddKasparovCycle α β F}

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
