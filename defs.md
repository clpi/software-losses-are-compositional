# Definitions

Every term of the model, at implementer resolution, each
tied to its counterpart in the proof folder. States:
the definitions here are settled intent; the Lean
counterparts named are implemented and verified at the
repo head recorded in the spec.

## Record

A record is the observed behavior of a system: a list of
entries in run order, one entry per observed behavior.
Recording is the only way a contract comes to exist.
Lean: a record is a list of naturals; an entry is a code
for one observed behavior.

## Additive recording

Recording accumulates additively: the record of a
composition is the append of the records of its parts,
in run order. Nothing is dropped, merged, or reweighted
at recording time. Lean: append of lists, and the theorem
named additive: the derived level of an append is the sum
of the derived levels.

## Derived contract

A contract is derived from a record by a derivation: the
contract of a system is built from its recorded behavior
and from nothing else. In the model the derivation is the
sum of the entries; a richer derivation is admissible
exactly when it respects append the way the sum does.
Lean: the function named derive.

## System and composition

A system, for the model, is its record. Two systems
compose by appending their records; a whole with an
interaction composes as part, interaction, part, in that
order. Composition is associative in the model because
append is.

## Axis

An axis is a per entry measure: a function from an entry
to a natural, summed over the record. Capability, design,
and performance are the three standing axes; the beat
program's power, compactness, and speed respects are
instances of them. An axis is quantifiable because its
value is a number, and solvable because its problem space
is finite (see the qualification contract).
Lean: the function named project, taking the per entry
measure and the record.

## Projection

Projection is applying an axis to a record. Projection is
compositional: projecting a composition equals composing
the projections, per axis. Lean: the theorem named
projected, and its three way form named split.

## Required level and share

A required level is the level an axis projection must
meet. A share is the part of a whole's required level
assigned to one component or to one interaction. Shares
are how a whole's requirement is distributed over its
composition sites before any verdict is read.

## Gap

A gap on an axis is the shortfall of a projection against
its required level: the required level minus the
projection, floored at zero. A gap of zero is loss
freeness on that axis. Lean: the function named gap, the
predicate named free, and the theorem named gapfree
tying them.

## Loss

A loss is a witnessed gap: a gap whose required level is
a named rival's projection on the same axis, under the
same contract, at a named pin. A gap without a rival is a
shortfall; a loss is a shortfall with a witness.

## Interaction

An interaction is the behavior that arises between two
components and belongs to neither alone. An interaction
is recorded when its behavior has its own record, hence
its own derived contract, its own projections, and its
own gap on every axis. An unrecorded interaction is the
one case where the composition laws can fail, and the
controls prove they do fail there.

## Composition site

A composition site is a place a loss can live: a component
contract or an interaction contract. The localization
theorem says every loss in a whole lives at a named site.
A structural fix is a change at the site: a producer or
contract change, never a patch at the instance that
happened to witness the loss.

## Compounding

Gaps compose compoundingly: the gap of a composition is
bounded by the sum of the component gaps and the
interaction gaps, and it shrinks monotonically as any
component's projection grows. Lean: the theorems named
compound and monotone.

## Qualification contract

The contract at play for a measurement: a finite discrete
list of capability values and a finite discrete list of
design values. Its problem space is the grid of the two
lists. Lean: the structure named Contract, the function
named space.

## Finiteness

The problem space is finite because a qualification picks
out named systems and named criteria: its size is the
product of the two list sizes, computed from the contract.
Finiteness is a derived conclusion here, never a
hypothesis. Lean: the theorem named finite.

## Analysis procedure

The method: derive contracts from recordings, compose,
project per axis, enumerate gaps over the finite space,
fix each gap at its site, re-measure. Its per axis check
is a decidable verdict over a finite record; its full
verdict is the conjunction over a finite axis list, so
the procedure terminates by construction. Lean: the
functions named check and allcheck.

## Soundness

A verdict is sound when a passing verdict implies loss
freeness in the model. Soundness is proved, per axis and
over the whole axis list. Lean: the theorems named sound
and allsound. Soundness of verdicts is all the model
claims about a concrete campaign; that a campaign's
records faithfully capture a real system's behavior is
the campaign's evidence, not a theorem.
