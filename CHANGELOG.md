# Changelog

## inqlog-v0.5.1 (2024-10-13)

### Changes

* Splitted file in multiple ones. [Max Ole Elliger]

* Cleaned up imports in FO/Formulas.v. [Max Ole Elliger]

### Fix

* Added Autosubst as dependency for CI. [Max Ole Elliger]

## inqlog-v0.5.0 (2024-10-13)

### New

* Finished the proof of the empty state property. [Max Ole Elliger]

* Stated `state_eq` [Max Ole Elliger]

  This includes
  - definition of `state_eq`
  - declaration of `state_eq` as an equivalence
  - declaration of `state_eq` as a congruence with respect to substate,
    support

* Proved persistency for FO. [Max Ole Elliger]

* Defined the support relation. [Max Ole Elliger]

* Defined states. [Max Ole Elliger]

* Defined the referent of a term. [Max Ole Elliger]

* Defined variable assignments. [Max Ole Elliger]

* Defined Models. [Max Ole Elliger]

  Models for first-order inquisitive logic are now defined.

  Possible improvements:
  - Add some documentation
  - Add some nice notation

* Defined more connectives. [Max Ole Elliger]

  The following connectives are now defined:
  - `Neg`
  - `Top`
  - `Disj`
  - `Exists`
  - `Iquest`

  Possible improvements:
  - Add some nice notation

* Autosubst for FO-formulas. [Max Ole Elliger]

  Autosubst provides support for binding signatures. To use it, our
  signature had to be updated: The `Bot`-operator now needs a variable as
  argument which isn't used further.

  Possible improvements:
  - Find a workaround to ignore this useless argument for `Bot`.
  - Improve documentation about the use of Autosubst.

* Basic syntax for first-order formulas. [Max Ole Elliger]

  Standard generic first-order signatures are used to provide a generic
  framework. A boolean predicate `rigid` was added to indicate which
  function symbols shall we rigid amoung all worlds in some model (which
  have to be defined later).

  Possible improvements:
  - Add Equality
  - Add some documentation
  - Add some nice notation

* Added a helpful fact about `ruling_out` [Max Ole Elliger]

  This fact points out, that if a consistent state rules out a formula, it
  can't support it.

* Defined the truth set of a formula. [Max Ole Elliger]

* Added intersection states. [Max Ole Elliger]

## inqlog-v0.4.0 (2024-07-31)

### New

* Proved `classical_truth_set` [Max Ole Elliger]

* Proved `satisfies_disj` [Max Ole Elliger]

  This was possible thanks to the decidability of `satisfies`.

* Proved the decidability of `satisfies` [Max Ole Elliger]

  This was done via reflection.

* Defined `satisfies'` [Max Ole Elliger]

  The alternative definition of satisfaction is defined directly without
  states.

### Changes

* Redefined `satisfies` [Max Ole Elliger]

  `satisfies` is now defined directly via recursion. The original
  definition is now covered by the Theorem `satisfies_singleton_support`.

* Simplified proof of prop_3_3_5. [Max Ole Elliger]

* Some reordering and coqdoc-sectioning. [Max Ole Elliger]

  - Restricted models are now located in InqLog.Prop.Models
  - Some further reordering in InqLog.Prop.LP

* Removed theories/Prop/Formulas.v and /LPC.v. [Max Ole Elliger]

* Simplified the proof of `satisfies_bot` by use of `singleton_false` [Max Ole Elliger]

## inqlog-v0.3.0 (2024-07-30)

### New

* Added some documentation to Prop/Formulas. [Max Ole Elliger]

* Documentation to theories/Prop/Models. [Max Ole Elliger]

* Examples for (in)consistent states. [Max Ole Elliger]

* Notation for `worlds_eq` and `state_eq` [Max Ole Elliger]

### Changes

* Updated some proofs to improve compile time. [Max Ole Elliger]

  Some parts of the proof of locality were updated. Concrete, some uses of
  `firstorder` were replaced.

* Improvements to notation scopes. [Max Ole Elliger]

  - New Notation: `|=`
  - Different scopes for worlds and states.

* Updated the first model example. [Max Ole Elliger]

  Instead of using a defined world-set, we now use the function space
  `bool -> bool`.

## inqlog-v0.2.0 (2024-07-29)

### New

* Proof of `support_iff` [Max Ole Elliger]

* Proof of `support_disj` [Max Ole Elliger]

* Classical variant of a formula. [Max Ole Elliger]

  This also includes the definition of a statement and a question.

* Added Proposition 3.3.5. [Max Ole Elliger]

  This proposition relates the truth set of a formula to the supporting
  states.

* Proposition 3.3.4. [Max Ole Elliger]

  This proposition claimes the truth conditions for `idisj`.

* Added definition of `truth_conditional` [Max Ole Elliger]

* Added `restricted_state` [Max Ole Elliger]

* Added `restricted_Model` [Max Ole Elliger]

* Added `singleton_proper` [Max Ole Elliger]

* Added example 3.2.5. [Max Ole Elliger]

* Added an example model `ex_Model_1` [Max Ole Elliger]

  This model only cares about to atoms, namely
  - `p` (represented by 0) and
  - `q` (represented by 1).
  It offers a world for every truth value combination of them, which are
  simply called `pq`, `p`, `q` and `e`.

### Changes

* Moved section `prop_3_1_7` from LPC to LP. [Max Ole Elliger]

* Updated section `prop_3_1_8` to use `truth_conditional` [Max Ole Elliger]

* Added `worlds_eq` [Max Ole Elliger]

  By this, many definitions had to be extended.
  In addition, some proofs had to be adjusted.

* Prop 3.1.4 to Prop 3.1.6 are proven only once. [Max Ole Elliger]

  This was achieved by declaring LPC as a subclass of LP.

### Fix

* Corrected `support_disj` [Max Ole Elliger]

## inqlog-v0.1.0 (2024-07-29)

### New

* Added information about CONTRIBUTING. [Max Ole Elliger]

* Created CHANGELOG.md. [Max Ole Elliger]

  The changelog is currently manually generated by
  [`gitchangelog`](https://github.com/vaab/gitchangelog).

  Commits updating the CHANGELOG should have the following style:

  ```
  chg: doc: Updated CHANGELOG.md !minor

  Further Information if needed...
  ```

* Proved Proposition 3.18. [Max Ole Elliger]

* Finished Proposition 3.17. [Max Ole Elliger]

  Added missing props:
  - `satisfies_neg`
  - `satisfies_top`
  - `satisfies_disj` (only stated, not proven because of missing classical
    logic)
  - `satisfies_iff`

* Added `singleton_true` and `singleton_false` [Max Ole Elliger]

* Proof of `substate_singleton` [Max Ole Elliger]

* `support_proper` [Max Ole Elliger]

* Some Instances. [Max Ole Elliger]

  Defined `state_equiv`
  Declared `state_equiv` as an `Equivalence`
  Declared `Proper (state_equiv ==> state_equiv ==> iff) substate`
  Declared `substate` as a reflexive relation

* `satisfies`-relation for LPC. [Max Ole Elliger]

  Added `worlds_deceq`
  Added `singleton` states
  Added `satisfies`

* Added theories/Support.v. [Max Ole Elliger]

* Executed generate.sh initially. [Max Ole Elliger]

### Changes

* New tag design. [Max Ole Elliger]

  - Removed old misleading tags
  - Updated the [changelog](CHANGELOG.md) by this.
  - Updated the version-tag-design.

* Excluded merge commits from CHANGELOG.md. [Max Ole Elliger]

* Restated `singleton_true` and `singleton_false` [Max Ole Elliger]

* Extracted `lpc_support` [Max Ole Elliger]

* Updated the definition of states. [Max Ole Elliger]

  states are now functions to bool instead of Prop.

* Initialized meta.yml. [Max Ole Elliger]

### Fix

* Updated workflow. [Max Ole Elliger]

  The workflow didn't name the artifact correct. This is now fixed

* Updated Makefile for chosen namespace InqLog. [Max Ole Elliger]

### Other

* Initial commit. [Max Ole Elliger]
