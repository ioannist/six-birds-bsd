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

/-- Closed local register. This is a syntactic condition and does not assert
that a `bridged` or externally approved arithmetic proposition is proved. -/
def ClosedAORRegister (carrier : AORInstanceCarrier) : Prop :=
  carrier.nonclaims ≠ [] ∧
    ∀ atom : DischargeAtom, atom ∈ carrier.discharges →
      ClosedStatus atom.status

/-- Refining one atom may expose more secondary defects, but must retain
its primary role and accounting status. In particular it cannot erase open
arithmetic by changing `bridged` to `zero` or `by_construction`. -/
def AtomRefines (fine coarse : DischargeAtom) : Prop :=
  fine.primary = coarse.primary ∧ fine.status = coarse.status ∧
    ∀ residual, residual ∈ coarse.forced_secondaries → residual ∈ fine.forced_secondaries

/-- The declared local refinement relation preserves recorded information
and covers every old atom, while every new atom refines an old one. It
describes diagnostic enrichment with fixed statuses, not the unrestricted
refinement relation of the external AOR meta-theory. -/
structure RegisterRefinement (coarse fine : AORInstanceCarrier) : Prop where
  sameCarrier : fine.carrier_id = coarse.carrier_id
  observationsKept : ∀ x, x ∈ coarse.observations → x ∈ fine.observations
  routesKept : ∀ x, x ∈ coarse.routes → x ∈ fine.routes
  sourcesKept : ∀ x, x ∈ coarse.sources → x ∈ fine.sources
  interfacesKept : ∀ x, x ∈ coarse.interfaces → x ∈ fine.interfaces
  constraintsKept : ∀ x, x ∈ coarse.constraints → x ∈ fine.constraints
  nonclaimsKept : ∀ x, x ∈ coarse.nonclaims → x ∈ fine.nonclaims
  atomsKept : ∀ a, a ∈ coarse.discharges →
    ∃ b, b ∈ fine.discharges ∧ AtomRefines b a
  atomsAccounted : ∀ b, b ∈ fine.discharges →
    ∃ a, a ∈ coarse.discharges ∧ AtomRefines b a

theorem atomRefinesRefl (atom : DischargeAtom) : AtomRefines atom atom :=
  ⟨rfl, rfl, fun _ h => h⟩

theorem atomRefinesTrans {a b c : DischargeAtom}
    (hab : AtomRefines a b) (hbc : AtomRefines b c) : AtomRefines a c :=
  ⟨hab.1.trans hbc.1, hab.2.1.trans hbc.2.1,
    fun r hr => hab.2.2 r (hbc.2.2 r hr)⟩

theorem registerRefinementRefl (carrier : AORInstanceCarrier) :
    RegisterRefinement carrier carrier :=
  ⟨rfl, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h,
    fun _ h => h, fun _ h => h,
    fun a ha => ⟨a, ha, atomRefinesRefl a⟩,
    fun a ha => ⟨a, ha, atomRefinesRefl a⟩⟩

theorem registerRefinementTrans {a b c : AORInstanceCarrier}
    (hab : RegisterRefinement a b) (hbc : RegisterRefinement b c) :
    RegisterRefinement a c := by
  refine ⟨hbc.sameCarrier.trans hab.sameCarrier,
    fun x hx => hbc.observationsKept x (hab.observationsKept x hx),
    fun x hx => hbc.routesKept x (hab.routesKept x hx),
    fun x hx => hbc.sourcesKept x (hab.sourcesKept x hx),
    fun x hx => hbc.interfacesKept x (hab.interfacesKept x hx),
    fun x hx => hbc.constraintsKept x (hab.constraintsKept x hx),
    fun x hx => hbc.nonclaimsKept x (hab.nonclaimsKept x hx), ?_, ?_⟩
  · intro atom hatom
    obtain ⟨mid, hmid, hma⟩ := hab.atomsKept atom hatom
    obtain ⟨fine, hfine, hfm⟩ := hbc.atomsKept mid hmid
    exact ⟨fine, hfine, atomRefinesTrans hfm hma⟩
  · intro atom hatom
    obtain ⟨mid, hmid, ham⟩ := hbc.atomsAccounted atom hatom
    obtain ⟨coarse, hcoarse, hmc⟩ := hab.atomsAccounted mid hmid
    exact ⟨coarse, hcoarse, atomRefinesTrans ham hmc⟩

theorem closedRegisterUnderRefinement {coarse fine : AORInstanceCarrier}
    (hclosed : ClosedAORRegister coarse) (href : RegisterRefinement coarse fine) :
    ClosedAORRegister fine := by
  refine ⟨fine.nonclaims_nonempty, ?_⟩
  intro atom hatom
  obtain ⟨parent, hparent, hrelation⟩ := href.atomsAccounted atom hatom
  rw [hrelation.2.1]
  exact hclosed.2 parent hparent

/-- Local membership now includes actual stability under the declared
register refinement relation. It remains non-eliminative and syntactic. -/
def RefStableAOR (carrier : AORInstanceCarrier) : Prop :=
  ClosedAORRegister carrier ∧
    ∀ fine, RegisterRefinement carrier fine → ClosedAORRegister fine

theorem refStableOfClosed {carrier : AORInstanceCarrier}
    (hclosed : ClosedAORRegister carrier) : RefStableAOR carrier :=
  ⟨hclosed, fun _ href => closedRegisterUnderRefinement hclosed href⟩

end SixBirdsBSD.Closure.AORPrimitives
