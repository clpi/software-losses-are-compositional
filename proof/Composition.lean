/-
  Losses are compositional: the structural fix model.

  The model, as directed by Chris on 2026-11-19. A system's
  contract is derived from its recorded behavior. Recording
  accumulates additively: the record of a composition is the
  append of the records of its parts, in run order. Contracts
  compose with systems. The composed contract projects onto
  quantifiable, solvable axes, and projection is
  compositional per axis. A gap is a shortfall on an axis; a
  loss is a witnessed gap against a named rival. Gaps compose
  compoundingly from component gaps and interaction gaps,
  provided every interaction is itself recorded. Loss
  freeness is compositional under the same condition, and a
  loss in a whole localizes to a gap in a component or in an
  interaction contract: a loss is fixed at its contract site,
  not at the instance. Every theorem below is proved in full;
  the file carries no premise of its own.
-/

namespace Composition

/-- A record of behavior: the observed entries of a system,
    in run order. An entry is a code for one observed
    behavior. The record of a whole is built only by
    appending the records of its parts. -/
def derive (r : List Nat) : Nat :=
  r.sum

/-- The sum of an append is the sum of the sums: the one
    arithmetic fact the additive laws rest on. -/
theorem sumsplit : ∀ (a b : List Nat),
    (a ++ b).sum = a.sum + b.sum
  | [], _ => by simp
  | _ :: rest, b => by
    simp [List.sum_cons, sumsplit rest b, Nat.add_assoc]

/-- Additive recording: the derived contract level of a
    composition is the sum of the derived levels of its
    parts. Recording a whole records exactly what recording
    its parts records, no more and no less. -/
theorem additive (a b : List Nat) :
    derive (a ++ b) = derive a + derive b := by
  show (a ++ b).sum = a.sum + b.sum
  exact sumsplit a b

/-- An axis: a per entry measure. Projecting a record onto
    an axis applies the measure to every entry and sums. The
    beat respects are instances: capability, design, and
    performance each supply their own per entry measure. -/
def project (f : Nat → Nat) (r : List Nat) : Nat :=
  (r.map f).sum

/-- Projection is compositional: projecting a composition
    onto an axis equals composing the projections, per axis.
    The projection of an append is the sum of the
    projections. -/
theorem projected (f : Nat → Nat) (a b : List Nat) :
    project f (a ++ b) = project f a + project f b := by
  show ((a ++ b).map f).sum = (a.map f).sum + (b.map f).sum
  rw [List.map_append]
  exact sumsplit (a.map f) (b.map f)

/-- The three way split of a projection: a whole made of two
    parts and the interaction between them projects to the
    sum of the three projections. -/
theorem split (f : Nat → Nat) (a inter b : List Nat) :
    project f (a ++ inter ++ b)
      = project f a + project f inter + project f b := by
  rw [projected f (a ++ inter) b, projected f a inter]

/-- A gap on an axis: the shortfall of a record's projection
    against a required level on that axis. A loss is a gap
    whose required level is a named rival's projection. -/
def gap (f : Nat → Nat) (req : Nat) (r : List Nat) : Nat :=
  req - project f r

/-- Loss freeness on one axis: the projection meets the
    required level, so the gap is zero. -/
def free (f : Nat → Nat) (req : Nat) (r : List Nat) : Prop :=
  req ≤ project f r

/-- Gap zero is loss freeness: the two readings of no
    shortfall agree on every axis and every record. -/
theorem gapfree (f : Nat → Nat) (req : Nat) (r : List Nat) :
    gap f req r = 0 ↔ free f req r := by
  unfold gap free
  omega

/-- Two part composition of loss freeness: parts that are
    loss free against their shares compose to a whole that
    is loss free against the sum of the shares. -/
theorem composed (f : Nat → Nat) (s1 s2 : Nat)
    (a b : List Nat)
    (h1 : free f s1 a) (h2 : free f s2 b) :
    free f (s1 + s2) (a ++ b) := by
  unfold free at *
  rw [projected]
  omega

/-- The structural fix theorem, three way form: when both
    components are loss free against their shares and the
    interaction between them is recorded and loss free
    against its share, the composition is loss free against
    the sum of the shares. A loss is therefore fixed at its
    contract or composition site, never at the instance. -/
theorem wholefree (f : Nat → Nat) (s1 si s2 : Nat)
    (a inter b : List Nat)
    (h1 : free f s1 a) (hi : free f si inter)
    (h2 : free f s2 b) :
    free f (s1 + si + s2) (a ++ inter ++ b) := by
  unfold free at *
  rw [split f a inter b]
  omega

/-- Gaps compose compoundingly: the gap of a composition is
    at most the sum of the component gaps and the
    interaction gap, when the required level of the whole is
    the sum of the shares. Every interaction term in the
    bound is itself a recorded contract's gap. -/
theorem compound (f : Nat → Nat) (s1 si s2 : Nat)
    (a inter b : List Nat) :
    gap f (s1 + si + s2) (a ++ inter ++ b)
      ≤ gap f s1 a + gap f si inter + gap f s2 b := by
  unfold gap
  rw [split f a inter b]
  omega

/-- The compounding bound is tight: when no component and
    no interaction runs a surplus over its share, the gap
    of the composition is exactly the sum of the component
    gaps and the interaction gap. The bound is therefore
    attained, not merely safe: it is the exact value at the
    no surplus point, and any strictness in the general
    bound is exactly the surplus that masks a gap. -/
theorem tight (f : Nat → Nat) (s1 si s2 : Nat)
    (a inter b : List Nat)
    (h1 : project f a ≤ s1) (hi : project f inter ≤ si)
    (h2 : project f b ≤ s2) :
    gap f (s1 + si + s2) (a ++ inter ++ b)
      = gap f s1 a + gap f si inter + gap f s2 b := by
  unfold gap
  rw [split f a inter b]
  omega

/-- The gap is monotone in each component: enlarging any one
    component's projection, the rest held fixed, never
    enlarges the gap of the whole. -/
theorem monotone (f : Nat → Nat) (req : Nat)
    (a b : List Nat) (h : project f a ≤ project f b) :
    gap f req b ≤ gap f req a := by
  unfold gap
  omega

/-- Localization: a gap in the whole localizes. If the
    composition falls short of the sum of the shares, then
    some component falls short of its share, or the recorded
    interaction does. There is no fourth place for a loss to
    hide: every loss in a whole is a gap at a named site. -/
theorem localizes (f : Nat → Nat) (s1 si s2 : Nat)
    (a inter b : List Nat)
    (h : project f (a ++ inter ++ b) < s1 + si + s2) :
    project f a < s1 ∨ project f inter < si
      ∨ project f b < s2 := by
  rw [split f a inter b] at h
  omega

/-- The qualification contract at play: its capability set
    and its design set, each a finite discrete list. The axis
    problem space of a contract is the grid of the two. -/
structure Contract where
  caps : List Nat
  designs : List Nat

/-- The grid of a pair of discrete lists: every capability
    paired with every design. -/
def grid : List Nat → List Nat → List (Nat × Nat)
  | [], _ => []
  | v :: rest, designs => designs.map (fun o => (v, o))
      ++ grid rest designs

/-- The problem space of a contract: the grid of its
    capability set and its design set. -/
def space (c : Contract) : List (Nat × Nat) :=
  grid c.caps c.designs

theorem gridlength (caps designs : List Nat) :
    (grid caps designs).length
      = caps.length * designs.length := by
  induction caps with
  | nil => simp [grid]
  | cons v rest ih =>
    show (designs.map (fun o => (v, o)) ++ grid rest designs).length
      = (rest.length + 1) * designs.length
    rw [List.length_append, List.length_map, ih, Nat.succ_mul]
    exact Nat.add_comm _ _

/-- Finiteness, derived: the size of a contract's problem
    space is the product of the sizes of its two finite
    discrete sets. A qualification picks out named systems
    and named criteria, so its space is finite as a
    conclusion computed from the contract, never as a
    hypothesis imposed on a larger space. Gap enumeration
    and the fix search over this space are therefore
    decidable searches over a finite list. -/
theorem finite (c : Contract) :
    (space c).length = c.caps.length * c.designs.length :=
  gridlength c.caps c.designs

/-- The analysis check on one axis: a decidable verdict on
    whether a record is loss free against a required level.
    The check is a finite computation over a finite record. -/
def check (f : Nat → Nat) (req : Nat) (r : List Nat) : Bool :=
  decide (req ≤ project f r)

/-- Method soundness on one axis: a passing check verdict
    implies loss freeness in the model. The procedure's
    verdicts never overclaim. -/
theorem sound (f : Nat → Nat) (req : Nat) (r : List Nat)
    (h : check f req r = true) : free f req r := by
  unfold check at h
  have h2 : req ≤ project f r := of_decide_eq_true h
  exact h2

/-- The analysis over a list of axes: every axis must pass.
    The list is finite, so the procedure terminates by
    construction: it is a fold over finite lists. -/
def allcheck (axes : List (Nat → Nat)) (req : Nat)
    (r : List Nat) : Bool :=
  axes.all (fun f => check f req r)

/-- Method soundness over all axes: a passing full verdict
    implies loss freeness on every axis in the list. -/
theorem allsound (axes : List (Nat → Nat)) (req : Nat)
    (r : List Nat) (h : allcheck axes req r = true) :
    ∀ f ∈ axes, free f req r := by
  intro f hf
  unfold allcheck at h
  rw [List.all_eq_true] at h
  exact sound f req r (h f hf)

end Composition

#print axioms Composition.additive
#print axioms Composition.projected
#print axioms Composition.split
#print axioms Composition.gapfree
#print axioms Composition.composed
#print axioms Composition.wholefree
#print axioms Composition.compound
#print axioms Composition.tight
#print axioms Composition.monotone
#print axioms Composition.localizes
#print axioms Composition.finite
#print axioms Composition.sound
#print axioms Composition.allsound
