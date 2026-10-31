import BC4lean.OrderTwoEigenSplitInvariance
import BC4lean.KasparovEquivariantDirectSum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The eigen classes are additive

A diagonal projection `P ⊕ Q` reduces a direct sum `c ⊕ d` when `P` reduces `c` and `Q` reduces
`d`, and the compression of `c ⊕ d` to `P ⊕ Q` is the direct sum of the compressions. The
canonical equivariant operator and the eigenprojections of a direct sum are diagonal. Hence the
eigen part of `c ⊕ d` is isomorphic to the direct sum of the eigen parts, and the eigen class
maps `KasparovHomotopyClass.eigenClass` and `OddKK.eigenClass` are additive. -/

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

/-! ## Even cycles -/

section EigenSum

variable [β.IsTrivial]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The eigenprojections of a direct-sum action are diagonal. -/
theorem EquivariantHilbertModule.sum_eigenProjection (U : EquivariantHilbertModule β E)
    (V : EquivariantHilbertModule β F) (g : Γ) (s : ℂ) :
    (U.sum V).eigenProjection g s = sumMap (U.eigenProjection g s) (V.eigenProjection g s) := by
  rw [EquivariantHilbertModule.eigenProjection, EquivariantHilbertModule.eigenProjection,
    EquivariantHilbertModule.eigenProjection, sum_actionOperator, ← sumMap_smul, ← sumMap_one,
    ← sumMap_add, ← sumMap_smul]

end EigenSum

section EvenAdditive

variable [Fintype Γ] [β.IsTrivial] {g : Γ} (hg : CentralInvolution α g)
  {s : ℂ} (hs : s * s = 1) (hsr : star s = s)

/-- The eigen part of a direct sum is the direct sum of the eigen parts. -/
def KasparovCycle.eigenPartDirectSumIso (c : KasparovCycle α β E) (d : KasparovCycle α β F) :
    KasparovCycleIso ((c.directSum d).eigenPart hg hs hsr)
      ((c.eigenPart hg hs hsr).directSum (d.eigenPart hg hs hsr)) :=
  ((c.equivariantCycleDirectSumIso d).compress
    ((c.directSum d).reducingProjection_equivariantCycle hg hs hsr)
    ((c.reducingProjection_equivariantCycle hg hs hsr).directSum
      (d.reducingProjection_equivariantCycle hg hs hsr))
    (fun x => by
      change (c.groupAction.sum d.groupAction).eigenProjection g s x = _
      rw [EquivariantHilbertModule.sum_eigenProjection]
      rfl)).trans
    (KasparovCycle.compressDirectSumDiagIso _ _)

namespace KasparovHomotopyClass

theorem eigenClass_add (x y : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β) :
    eigenClass hg hs hsr (x + y) = eigenClass hg hs hsr x + eigenClass hg hs hsr y := by
  induction x using Quotient.inductionOn with
  | h c =>
    induction y using Quotient.inductionOn with
    | h d =>
      exact mk_eq_of_iso (c.cycle.eigenPartDirectSumIso hg hs hsr d.cycle)

/-- The `s`-eigen class as an additive map. -/
def eigenClassHom :
    KasparovHomotopyClass.{uΓ, uA, uB, uE} α β →+ KasparovHomotopyClass.{uΓ, uA, uB, uE} α β :=
  AddMonoidHom.mk' (eigenClass hg hs hsr) (eigenClass_add hg hs hsr)

@[simp] theorem eigenClassHom_apply (x : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β) :
    eigenClassHom hg hs hsr x = eigenClass hg hs hsr x := rfl

end KasparovHomotopyClass

end EvenAdditive

/-! ## Odd cycles -/

section OddAdditive

variable [Fintype Γ] [β.IsTrivial] {g : Γ} (hg : CentralInvolution α g)
  {s : ℂ} (hs : s * s = 1) (hsr : star s = s)

/-- The eigen part of an odd direct sum is the direct sum of the eigen parts. -/
def OddKasparovCycle.eigenPartDirectSumIso (c : OddKasparovCycle α β E)
    (d : OddKasparovCycle α β F) :
    OddKasparovCycleIso ((c.directSum d).eigenPart hg hs hsr)
      ((c.eigenPart hg hs hsr).directSum (d.eigenPart hg hs hsr)) :=
  ((c.equivariantCycleDirectSumIso d).compress
    ((c.directSum d).reducingProjection_equivariantCycle hg hs hsr)
    ((c.reducingProjection_equivariantCycle hg hs hsr).directSum
      (d.reducingProjection_equivariantCycle hg hs hsr))
    (fun x => by
      change (c.groupAction.sum d.groupAction).eigenProjection g s x = _
      rw [EquivariantHilbertModule.sum_eigenProjection]
      rfl)).trans
    (OddKasparovCycle.compressDirectSumDiagIso _ _)

namespace OddKK

variable [TopologicalSpace.SeparableSpace B]

theorem eigenClass_add (x y : OddKK.{uΓ, uA, uB, uE} α β) :
    eigenClass hg hs hsr (x + y) = eigenClass hg hs hsr x + eigenClass hg hs hsr y := by
  induction x using Quotient.inductionOn with
  | h c =>
    induction y using Quotient.inductionOn with
    | h d =>
      exact mk_eq_of_iso (c.cycle.eigenPartDirectSumIso hg hs hsr d.cycle)

/-- The `s`-eigen class of odd classes as an additive map. -/
def eigenClassHom : OddKK.{uΓ, uA, uB, uE} α β →+ OddKK.{uΓ, uA, uB, uE} α β :=
  AddMonoidHom.mk' (eigenClass hg hs hsr) (eigenClass_add hg hs hsr)

@[simp] theorem eigenClassHom_apply (x : OddKK.{uΓ, uA, uB, uE} α β) :
    eigenClassHom hg hs hsr x = eigenClass hg hs hsr x := rfl

end OddKK

end OddAdditive

end BC4lean.KKTheory
