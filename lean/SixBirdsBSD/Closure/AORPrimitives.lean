/-!
Local AOR carrier primitives for the BSD closure axis.

This is the minimal syntactic AOR vocabulary needed by the BSD
`AORInstance` module. The full TsiokosAOR2026 meta-theory is cited at
paper level and is not re-derived here.
-/

namespace SixBirdsBSD.Closure.AORPrimitives

/-- Residual categories used by the BSD AOR discharge register. -/
inductive ResidualType : Type where
  | source : ResidualType
  | transport : ResidualType
  | role : ResidualType
  | target : ResidualType
  | limit : ResidualType
  | presentation : ResidualType
  | «meta» : ResidualType
  deriving DecidableEq

/-- Closed discharge statuses used locally by the BSD AOR presentation. -/
inductive DischargeStatus : Type where
  | zero : DischargeStatus
  | bridged : DischargeStatus
  | approved_other : DischargeStatus
  | outside_scope : DischargeStatus
  | nonclaim : DischargeStatus
  | by_construction : DischargeStatus
  | asymptotic_budgeted : DischargeStatus
  deriving DecidableEq

/-- One typed residual atom in the AOR discharge register. -/
structure DischargeAtom : Type where
  primary : ResidualType
  forced_secondaries : List ResidualType
  status : DischargeStatus
  deriving DecidableEq

/--
The eight-field local AOR carrier, plus a witness that the nonclaim
register is populated.
-/
structure AORInstanceCarrier : Type where
  carrier_id : String
  observations : List String
  routes : List String
  sources : List String
  interfaces : List String
  constraints : List String
  discharges : List DischargeAtom
  nonclaims : List String
  nonclaims_nonempty : nonclaims ≠ []

/--
Local closed-status predicate for non-eliminative AOR membership. A
zeroed residual is not closed: the BSD AOR register may reclassify
open arithmetic as bridged or externally approved, but it may not
erase it as `zero`.
-/
def ClosedStatus : DischargeStatus → Prop
  | DischargeStatus.zero => False
  | _ => True

/--
Local refinement-stable AOR membership: the nonclaim register is
nonempty, and every discharge atom has a closed local status.
-/
def RefStableAOR (carrier : AORInstanceCarrier) : Prop :=
  carrier.nonclaims ≠ [] ∧
    ∀ atom : DischargeAtom, atom ∈ carrier.discharges →
      ClosedStatus atom.status

end SixBirdsBSD.Closure.AORPrimitives
