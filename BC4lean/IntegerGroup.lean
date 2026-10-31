import Mathlib.Data.Countable.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Int

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The integers as a discrete group

BC4lean's groups are multiplicative, so the integers enter as `Multiplicative ℤ`. Mathlib gives it
the discrete topology. The assembly map also needs `Countable`, which Mathlib does not provide for
`Multiplicative`; this module supplies it once, for every countable type. -/

namespace BC4lean

/-- `Multiplicative α` is countable when `α` is. -/
instance countable_multiplicative {α : Type*} [Countable α] : Countable (Multiplicative α) :=
  inferInstanceAs (Countable α)

example : DiscreteTopology (Multiplicative ℤ) := inferInstance

example : Countable (Multiplicative ℤ) := inferInstance

end BC4lean
