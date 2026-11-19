/-
  Adversarial controls for the composition model. Each
  control weakens one condition of the model and proves, by
  a concrete counterexample, that the corresponding law then
  fails. A control that stopped failing would mean the
  condition it weakens was never load bearing.
-/

import Composition

namespace Composition

/-- Control one: an unrecorded interaction breaks the
    compositionality of the gap. Two parts each project to
    one on the identity axis; the interaction between them
    projects to five. The composition computed without the
    interaction reads two; the true composition reads seven.
    The two readings differ, so no gap law stated over the
    unrecorded composition can hold. -/
theorem controlone :
    project id ([1] ++ [1]) ≠ project id ([1] ++ [5] ++ [1]) := by
  decide

/-- A non additive recording: duplicates in the record are
    collapsed before the contract is derived. Each entry is
    kept once, at its first place, and later repeats are
    dropped. -/
def squash (r : List Nat) : List Nat :=
  go r []
where
  go : List Nat → List Nat → List Nat
    | [], _ => []
    | x :: rest, seen =>
      if x ∈ seen then go rest seen else x :: go rest (x :: seen)

/-- Control two: a non additive recording breaks the
    projection law. Under the collapsed recording, the
    projection of a composition of two identical parts reads
    one, while the sum of the projections of the parts reads
    two. Additivity of recording is load bearing for the
    projection law. -/
theorem controltwo :
    project id (squash ([1] ++ [1]))
      ≠ project id (squash [1]) + project id (squash [1]) := by
  decide

/-- Control three: component wise loss freeness does not
    save a composition whose interaction is unrecorded. Each
    component meets its share of one, yet the recorded whole
    projects to two against a required level of seven, the
    sum of the two shares and the interaction share of five.
    The whole loses, and the loss sits exactly at the
    unrecorded interaction site. -/
theorem controlthree :
    (1 ≤ project id [1]) ∧ (1 ≤ project id [1])
      ∧ ¬ (7 ≤ project id ([1] ++ [1])) := by
  refine ⟨by decide, by decide, by decide⟩

end Composition

#print axioms Composition.controlone
#print axioms Composition.controltwo
#print axioms Composition.controlthree
