import BC4lean.KasparovHomotopyGroup
import BC4lean.GroupUniverseParityGroup

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Restriction of equivariant KK along a group homomorphism

For `f : Γ →* Γ'`, a `Γ'`-equivariant cycle restricts to a `Γ`-equivariant
cycle on the same module, with the same grading, representation and operator;
only the group action is precomposed with `f`. Isomorphisms and full interval
homotopies restrict in the same way, so restriction is well defined on both
parity quotients and additive.

For a one-element group `Γ` with trivial coefficient actions, restriction
along `Unit →* Γ` and `Γ →* Unit` are inverse additive equivalences between
`KK^Γ` and ordinary (`Unit`-group) KK, in both parities.
-/

noncomputable section
universe uΓ uΓ' uA uB uE
namespace BC4lean.KKTheory.GroupRestriction

section Actions
variable {Γ : Type uΓ} {Γ' : Type uΓ'} [Group Γ] [Group Γ'] (f : Γ →* Γ')
  {B : Type uB} [NonUnitalCStarAlgebra B]

/-- Restriction of a coefficient action along a group homomorphism. -/
def actionComap (β : CStarAlgebraAction Γ' B) : CStarAlgebraAction Γ B where
  automorphism := β.automorphism.comp f

@[simp] theorem actionComap_apply (β : CStarAlgebraAction Γ' B) (g : Γ) (b : B) :
    (actionComap f β).automorphism g b = β.automorphism (f g) b := rfl

/-- Restricting a trivial action gives the trivial action, definitionally. -/
theorem actionComap_trivial :
    actionComap f (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' B) =
      CStarAlgebraAction.trivial := rfl

variable [PartialOrder B] [StarOrderedRing B]

/-- Restriction commutes with pointwise interval sections, definitionally. -/
theorem actionComap_continuousSections (β : CStarAlgebraAction Γ' B) :
    actionComap f (β.continuousSections (X := unitInterval)) =
      (actionComap f β).continuousSections (X := unitInterval) := rfl

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E]

/-- Restriction of a compatible module action. -/
def moduleComap {β : CStarAlgebraAction Γ' B} (U : EquivariantHilbertModule β E) :
    EquivariantHilbertModule (actionComap f β) E where
  action := U.action.comp f
  inner_action g x y := U.inner_action (f g) x y

omit [StarOrderedRing B] in
theorem moduleComap_conjugateOperator {β : CStarAlgebraAction Γ' B}
    (U : EquivariantHilbertModule β E) (g : Γ) (T : AdjointableMap B E E) :
    (moduleComap f U).conjugateOperator g T = U.conjugateOperator (f g) T := by
  apply AdjointableMap.ext
  intro x
  simp [moduleComap, map_inv]

end Actions

section Cycles
variable {Γ : Type uΓ} {Γ' : Type uΓ'} [Group Γ] [Group Γ'] (f : Γ →* Γ')
  {A : Type uA} {B : Type uB} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  {α : CStarAlgebraAction Γ' A} {β : CStarAlgebraAction Γ' B}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
  [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]

/-- Restriction of an even cycle: same module, grading, representation and operator. -/
def cycleComap (c : KasparovCycle α β E) :
    KasparovCycle (actionComap f α) (actionComap f β) E where
  countablyGenerated := c.countablyGenerated
  grading := c.grading
  groupAction := moduleComap f c.groupAction
  grading_preserved g x := c.grading_preserved (f g) x
  representation := c.representation
  representation_even := c.representation_even
  representation_equivariant g a := by
    rw [moduleComap_conjugateOperator]
    exact c.representation_equivariant (f g) a
  operator := c.operator
  operator_odd := c.operator_odd
  selfadjoint_mod_compact := c.selfadjoint_mod_compact
  square_mod_compact := c.square_mod_compact
  commutator_compact := c.commutator_compact
  equivariance_mod_compact g a := by
    rw [moduleComap_conjugateOperator]
    exact c.equivariance_mod_compact (f g) a

/-- Restriction of an odd cycle: same module, representation and operator. -/
def oddCycleComap (c : OddKasparovCycle α β E) :
    OddKasparovCycle (actionComap f α) (actionComap f β) E where
  countablyGenerated := c.countablyGenerated
  groupAction := moduleComap f c.groupAction
  representation := c.representation
  representation_equivariant g a := by
    rw [moduleComap_conjugateOperator]
    exact c.representation_equivariant (f g) a
  operator := c.operator
  selfadjoint_mod_compact := c.selfadjoint_mod_compact
  square_mod_compact := c.square_mod_compact
  commutator_compact := c.commutator_compact
  equivariance_mod_compact g a := by
    rw [moduleComap_conjugateOperator]
    exact c.equivariance_mod_compact (f g) a

/-- Restriction of an even cycle isomorphism. -/
def isoComap {c : KasparovCycle α β E} {d : KasparovCycle α β F} (u : KasparovCycleIso c d) :
    KasparovCycleIso (cycleComap f c) (cycleComap f d) where
  moduleEquiv := u.moduleEquiv
  grading_intertwine := u.grading_intertwine
  action_intertwine g x := u.action_intertwine (f g) x
  representation_intertwine := u.representation_intertwine
  operator_intertwine := u.operator_intertwine

/-- Restriction of an odd cycle isomorphism. -/
def oddIsoComap {c : OddKasparovCycle α β E} {d : OddKasparovCycle α β F}
    (u : OddKasparovCycleIso c d) :
    OddKasparovCycleIso (oddCycleComap f c) (oddCycleComap f d) where
  moduleEquiv := u.moduleEquiv
  action_intertwine g x := u.action_intertwine (f g) x
  representation_intertwine := u.representation_intertwine
  operator_intertwine := u.operator_intertwine

/-- Restriction commutes with an evaluated interval fibre (even cycles). -/
def fibreComapIso {M : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
    [SMul (C(unitInterval, B))ᵐᵒᵖ M] [CStarModule (C(unitInterval, B))ᵐᵒᵖ M] [CompleteSpace M]
    (c : KasparovCycle α (β.continuousSections (X := unitInterval)) M) (t : unitInterval) :
    KasparovCycleIso ((cycleComap f c).fibre t) (cycleComap f (c.fibre t)) where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

/-- Restriction commutes with an evaluated interval fibre (odd cycles). -/
def oddFibreComapIso {M : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
    [SMul (C(unitInterval, B))ᵐᵒᵖ M] [CStarModule (C(unitInterval, B))ᵐᵒᵖ M] [CompleteSpace M]
    (c : OddKasparovCycle α (β.continuousSections (X := unitInterval)) M) (t : unitInterval) :
    OddKasparovCycleIso ((oddCycleComap f c).fibre t) (oddCycleComap f (c.fibre t)) where
  moduleEquiv := HilbertModuleEquiv.refl
  action_intertwine _ _ := rfl
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

end Cycles

section Bundled
variable {Γ : Type uΓ} {Γ' : Type uΓ'} [Group Γ] [Group Γ'] (f : Γ →* Γ')
  {A : Type uA} {B : Type uB} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  {α : CStarAlgebraAction Γ' A} {β : CStarAlgebraAction Γ' B}

/-- Restriction of a bundled even cycle; the carrier is unchanged. -/
def bundledComap (c : BundledKasparovCycle.{uΓ', uA, uB, uE} α β) :
    BundledKasparovCycle.{uΓ, uA, uB, uE} (actionComap f α) (actionComap f β) :=
  BundledKasparovCycle.of (cycleComap f c.cycle)

/-- Restriction of a bundled odd cycle; the carrier is unchanged. -/
def bundledOddComap (c : BundledOddKasparovCycle.{uΓ', uA, uB, uE} α β) :
    BundledOddKasparovCycle.{uΓ, uA, uB, uE} (actionComap f α) (actionComap f β) :=
  BundledOddKasparovCycle.of (oddCycleComap f c.cycle)

/-- Restriction of a full even interval homotopy. -/
def fullComap {c d : BundledKasparovCycle.{uΓ', uA, uB, uE} α β}
    (h : FullKasparovHomotopy c d) :
    FullKasparovHomotopy (bundledComap f c) (bundledComap f d) where
  intervalCycle := bundledComap f h.intervalCycle
  sourceIso := (fibreComapIso f h.intervalCycle.cycle 0).trans (isoComap f h.sourceIso)
  targetIso := (fibreComapIso f h.intervalCycle.cycle 1).trans (isoComap f h.targetIso)

/-- Restriction of a full odd interval homotopy. -/
def oddFullComap {c d : BundledOddKasparovCycle.{uΓ', uA, uB, uE} α β}
    (h : FullOddKasparovHomotopy c d) :
    FullOddKasparovHomotopy (bundledOddComap f c) (bundledOddComap f d) where
  intervalCycle := bundledOddComap f h.intervalCycle
  sourceIso := (oddFibreComapIso f h.intervalCycle.cycle 0).trans (oddIsoComap f h.sourceIso)
  targetIso := (oddFibreComapIso f h.intervalCycle.cycle 1).trans (oddIsoComap f h.targetIso)

theorem homotopic_comap {c d : BundledKasparovCycle.{uΓ', uA, uB, uE} α β}
    (h : c.Homotopic d) : (bundledComap f c).Homotopic (bundledComap f d) := by
  induction h with
  | rel a b h =>
      rcases h with h | h
      · obtain ⟨u⟩ := h
        exact BundledKasparovCycle.homotopic_of_iso (isoComap f u)
      · obtain ⟨h⟩ := h
        exact BundledKasparovCycle.homotopic_of_full (fullComap f h)
  | refl => exact BundledKasparovCycle.homotopic_refl _
  | symm a b _ ih => exact BundledKasparovCycle.homotopic_symm ih
  | trans a b k _ _ hab hbk => exact BundledKasparovCycle.homotopic_trans hab hbk

/-- Restriction on even equivariant KK classes. -/
def evenComap :
    KasparovHomotopyClass.{uΓ', uA, uB, uE} α β →
      KasparovHomotopyClass.{uΓ, uA, uB, uE} (actionComap f α) (actionComap f β) :=
  Quotient.map (bundledComap f) (fun _ _ h => homotopic_comap f h)

@[simp] theorem evenComap_mk (c : BundledKasparovCycle.{uΓ', uA, uB, uE} α β) :
    evenComap f (KasparovHomotopyClass.mk c) = KasparovHomotopyClass.mk (bundledComap f c) :=
  rfl

theorem evenComap_add (x y : KasparovHomotopyClass.{uΓ', uA, uB, uE} α β) :
    evenComap f (x + y) = evenComap f x + evenComap f y := by
  induction x using Quotient.inductionOn
  induction y using Quotient.inductionOn
  rfl

variable [TopologicalSpace.SeparableSpace B]

/-- Restriction on odd equivariant KK classes. -/
def oddComap :
    OddKK.{uΓ', uA, uB, uE} α β → OddKK.{uΓ, uA, uB, uE} (actionComap f α) (actionComap f β) :=
  Quotient.map (bundledOddComap f) (fun _ _ h => by obtain ⟨h⟩ := h; exact ⟨oddFullComap f h⟩)

@[simp] theorem oddComap_mk (c : BundledOddKasparovCycle.{uΓ', uA, uB, uE} α β) :
    oddComap f (OddKK.mk c) = OddKK.mk (bundledOddComap f c) :=
  rfl

theorem oddComap_add (x y : OddKK.{uΓ', uA, uB, uE} α β) :
    oddComap f (x + y) = oddComap f x + oddComap f y := by
  induction x using Quotient.inductionOn
  induction y using Quotient.inductionOn
  rfl

end Bundled

section Subsingleton
open GroupUniverseParityGroup
variable {Γ : Type uΓ} [Group Γ] [Subsingleton Γ]
  {A : Type uA} {B : Type uB} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]

/-- The unique homomorphism from a one-element group to `Unit`. -/
def toUnitHom : Γ →* Unit := 1

/-- The unique homomorphism from `Unit` to a one-element group. -/
def fromUnitHom : Unit →* Γ := 1

/-- Restricting to `Unit` and back gives an isomorphic even cycle. -/
def comapComapIso (c : BundledKasparovCycle.{uΓ, uA, uB, uE}
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ A)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B)) :
    BundledKasparovCycle.Iso
      (bundledComap (toUnitHom (Γ := Γ)) (bundledComap (fromUnitHom (Γ := Γ)) c)) c where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine g x := by
    change c.cycle.groupAction.action (fromUnitHom (toUnitHom g)) x = c.cycle.groupAction.action g x
    rw [Subsingleton.elim (fromUnitHom (toUnitHom g)) g]
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

/-- Restricting to `Γ` and back to `Unit` gives an isomorphic even cycle. -/
def comapComapIso' (c : BundledKasparovCycle.{0, uA, uB, uE}
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit A)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit B)) :
    BundledKasparovCycle.Iso
      (bundledComap (fromUnitHom (Γ := Γ)) (bundledComap (toUnitHom (Γ := Γ)) c)) c where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine g x := by
    change c.cycle.groupAction.action (toUnitHom (fromUnitHom (Γ := Γ) g)) x =
      c.cycle.groupAction.action g x
    rw [Subsingleton.elim (toUnitHom (fromUnitHom (Γ := Γ) g)) g]
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

/-- Restricting to `Unit` and back gives an isomorphic odd cycle. -/
def oddComapComapIso (c : BundledOddKasparovCycle.{uΓ, uA, uB, uE}
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ A)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B)) :
    BundledOddKasparovCycle.Iso
      (bundledOddComap (toUnitHom (Γ := Γ)) (bundledOddComap (fromUnitHom (Γ := Γ)) c)) c where
  moduleEquiv := HilbertModuleEquiv.refl
  action_intertwine g x := by
    change c.cycle.groupAction.action (fromUnitHom (toUnitHom g)) x = c.cycle.groupAction.action g x
    rw [Subsingleton.elim (fromUnitHom (toUnitHom g)) g]
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

/-- Restricting to `Γ` and back to `Unit` gives an isomorphic odd cycle. -/
def oddComapComapIso' (c : BundledOddKasparovCycle.{0, uA, uB, uE}
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit A)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit B)) :
    BundledOddKasparovCycle.Iso
      (bundledOddComap (fromUnitHom (Γ := Γ)) (bundledOddComap (toUnitHom (Γ := Γ)) c)) c where
  moduleEquiv := HilbertModuleEquiv.refl
  action_intertwine g x := by
    change c.cycle.groupAction.action (toUnitHom (fromUnitHom (Γ := Γ) g)) x =
      c.cycle.groupAction.action g x
    rw [Subsingleton.elim (toUnitHom (fromUnitHom (Γ := Γ) g)) g]
  representation_intertwine _ _ := rfl
  operator_intertwine _ := rfl

/-- Even KK for trivial actions of a one-element group is ordinary even KK. -/
def subsingletonEvenEquiv :
    KasparovHomotopyClass.{uΓ, uA, uB, uE} (CStarAlgebraAction.trivial : CStarAlgebraAction Γ A)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B) ≃+
    KasparovHomotopyClass.{0, uA, uB, uE} (CStarAlgebraAction.trivial : CStarAlgebraAction Unit A)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit B) where
  toFun := evenComap (fromUnitHom (Γ := Γ))
  invFun := evenComap (toUnitHom (Γ := Γ))
  left_inv x := by
    induction x using Quotient.inductionOn with
    | h c => exact KasparovHomotopyClass.mk_eq_of_iso (comapComapIso c)
  right_inv y := by
    induction y using Quotient.inductionOn with
    | h c => exact KasparovHomotopyClass.mk_eq_of_iso (comapComapIso' (Γ := Γ) c)
  map_add' := evenComap_add _

variable [TopologicalSpace.SeparableSpace B]

/-- Odd KK for trivial actions of a one-element group is ordinary odd KK. -/
def subsingletonOddEquiv :
    OddKK.{uΓ, uA, uB, uE} (CStarAlgebraAction.trivial : CStarAlgebraAction Γ A)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B) ≃+
    OddKK.{0, uA, uB, uE} (CStarAlgebraAction.trivial : CStarAlgebraAction Unit A)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit B) where
  toFun := oddComap (fromUnitHom (Γ := Γ))
  invFun := oddComap (toUnitHom (Γ := Γ))
  left_inv x := by
    induction x using Quotient.inductionOn with
    | h c => exact OddKK.mk_eq_of_iso (oddComapComapIso c)
  right_inv y := by
    induction y using Quotient.inductionOn with
    | h c => exact OddKK.mk_eq_of_iso (oddComapComapIso' (Γ := Γ) c)
  map_add' := oddComap_add _

/-- Both parities: `KK^Γ_p` with trivial actions of a one-element group is ordinary `KK_p`. -/
def subsingletonParityEquiv (p : Bool) :
    KKParityGroup.{uΓ, uA, uB, uE} p (CStarAlgebraAction.trivial : CStarAlgebraAction Γ A)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B) ≃+
    KKParityGroup.{0, uA, uB, uE} p (CStarAlgebraAction.trivial : CStarAlgebraAction Unit A)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit B) := by
  cases p
  · exact subsingletonEvenEquiv
  · exact subsingletonOddEquiv

end Subsingleton

end BC4lean.KKTheory.GroupRestriction
