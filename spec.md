# Spec: losses are compositional

## Settled intent

Directed by Chris on 2026-11-19: fix all losses
structurally through composition, through all additively
recorded behaviorally derived contracts, projected as
quantifiable solvable axes of capability, design, and
performance, composing all gaps compoundingly and
provably; and develop a constructive proved model and
method for analysis on this foundation for any arbitrary
software system.

The model's one sentence: a loss is fixed at its contract
or composition site, not at the instance that witnessed
it, because every loss in a whole localizes to a gap in a
component contract or in a recorded interaction contract.

## Proven

Thirteen theorems, all proved in full at the head recorded
in the completion section, zero sorries, family gate cold,
printed axioms within the standard set. Names are the
single word theorem names in the proof folder.

1. Additive recording (additive): the derived contract
   level of a composition is the sum of the levels of its
   parts.
2. Compositional projection (projected): projecting a
   composition onto an axis is the sum of the projections,
   per axis; three way form (split) for part, interaction,
   part.
3. Gap reading (gapfree): gap zero and loss freeness are
   the same fact on every axis.
4. Composition of loss freeness (composed): two loss free
   parts compose to a loss free whole against the summed
   shares.
5. The structural fix theorem (wholefree): components
   loss free on an axis, plus the interaction recorded and
   loss free on that axis, give the composition loss free
   on that axis.
6. Compounding (compound): the gap of a composition is at
   most the sum of the component gaps and the interaction
   gap. The bound is certified tight (tight): when no
   component and no interaction runs a surplus over its
   share, the gap of the composition is exactly that sum;
   any strictness in the general bound is exactly the
   surplus that masks a gap.
7. Monotonicity (monotone): growing any component's
   projection never grows the whole's gap.
8. Localization (localizes): a gap in a whole implies a
   gap in a component or in the recorded interaction.
   There is no fourth place for a loss to hide.
9. Finiteness (finite): a qualification contract's
   problem space has size equal to the product of its two
   list sizes; finiteness is derived from the contract's
   definition, never assumed.
10. Method soundness (sound, allsound): a passing check
    verdict, per axis and over a finite axis list, implies
    loss freeness in the model.

## Controls

Three standing controls, each a proved negation over a
concrete counterexample. A control that stopped failing
would mean its condition was never load bearing.

1. Control one: an unrecorded interaction breaks the
   compositionality of the gap. The composition read
   without the interaction is two; read with it, seven.
2. Control two: a non additive recording (duplicates
   collapsed) breaks the projection law: one against two.
3. Control three: component wise loss freeness does not
   save a composition whose interaction is unrecorded:
   both components meet their shares and the whole still
   loses, at exactly the unrecorded interaction site.

## Premises, named

The model proves structure. Two things are premises, not
theorems, and are never claimed as theorems:

1. Record fidelity: that a concrete campaign's records
   capture the behavior of a real system is the campaign's
   evidence, established by the campaign's own execution.
2. Re-measure: the model flips no beat cell. A cell flips
   only on a same-contract re-measure at a current pin,
   executed against the real rival and the real system.

## Proposed, open

1. Richer derivations: the model uses the sum derivation.
   Any derivation respecting append inherits every law
   here; a general derivation interface is proposed, not
   formalized.
2. Weighted axes: an axis whose per entry measure depends
   on position or on the qualification contract is
   proposed; the parametric form is not formalized.
3. Continuous axes: axes valued in ordered structures
   beyond the naturals are proposed, not formalized.

## The method, executable

Eight steps, each with its measure. The procedure is the
analysis the theorems license; run it on any software
system whose behavior can be recorded.

1. Record: capture the system's behavior as records, one
   per component and one per interaction. Measure: every
   interaction has a record, or is named unrecorded.
2. Derive: build each contract from its record alone.
   Measure: no contract cites behavior outside its record.
3. Compose: form the whole's contract by composition.
   Measure: the whole's projection equals the composed
   projections, per axis, checked by execution.
4. Project: read every axis. Measure: one number per axis
   per site, at a named pin.
5. Enumerate: list every gap over the finite problem
   space, each gap at its site, each loss with its rival.
   Measure: the enumeration is complete for the space.
6. Fix at the site: change the producer or contract at
   the gap's site. Measure: the fix names its site; an
   instance patch is refused as a fix.
7. Control: land a standing test or gate with the fix, or
   record the fix as ungated with the reason. Measure:
   the control fails when the defect returns.
8. Re-measure: same contract, current pin. Measure: the
   cell flips only on this step's executed numbers.

## Completion

Landed: the proof folder carries the core file with
thirteen theorems and the controls file with three
controls; the family gate passes cold under Lean 4.19.0
with warnings as errors; printed axioms across all
sixteen audited declarations are within the set of
propext, choice, and the quotient soundness axiom, and
three declarations depend on no axioms at all. The
definitions file defines every model term at implementer
resolution, tied to its Lean counterpart. This spec
carries the method with its measures. The repo head at
landing is recorded in the program record in the research
folder, not here, because the head names the commit that
carries this file.
