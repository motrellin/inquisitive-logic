# Changelog

## inqlog-v0.16.1 (2025-03-17)

### Changes

* Simplified the proof of `support_CasariImpl_IES_other_direction` [Max Ole Elliger]

  This was possible by the new definition of `unnamed_helper_Casari_3`.

* Simplified `unnamed_helper_Casari_3` [Max Ole Elliger]

  new state definition and less assumptions

## inqlog-v0.16.0 (2025-03-16)

### Changes

* Optimized Casari.v with multiple changes. [Max Ole Elliger]

  - Simplified `counter_state` in Casari
  - Moved all assumptions of classical logic for the Casari
    Counter-Example to `support_CasariAnt_IES`
  - By this, all real `_other_direction`-proofs were eliminated.
  - The contraposition variants of them were renamed.
  - Used the keywords `Lemma`, `Proposition`, `Theorem`, `Corollary` more
    consistently.
  - Simplified proofs.
  - Extracted state construction for `unnamed_helper_Casari_3` to a local
    definition.
  - Improved documentation
  - Simplified proofs for the bounded validity of the Casari Scheme

## inqlog-v0.15.0 (2025-03-14)

### New

* Analysed the support validity of DNE. [Max Ole Elliger]

  DNE is truth-valid, but not support-valid. It is valid for every
  classical formula.

* Defined the most inconsistent state. [Max Ole Elliger]

* Defined example model `two_Worlds_Model` [Max Ole Elliger]

* Defined `pointed_assignment` [Max Ole Elliger]

* Defined Kuroda and derived it via `Seq` [Max Ole Elliger]

* Proved `Seq_Neg_l` [Max Ole Elliger]

### Changes

* Moved assignments from Support.v -> Models.v. [Max Ole Elliger]

* Removed unnecessary uses of NNPP in Seq.v. [Max Ole Elliger]

* Simplified and comment `satisfaction_conseq_Pred_r` [Max Ole Elliger]

* More `Print Assumptions` for soundness. [Max Ole Elliger]

  This makes the use of classical logic more transparent.

* Replaced some anonymous functions in Consequence.v. [Max Ole Elliger]

* Redefined the highest occ variable. [Max Ole Elliger]

  By using the `option`-type, we can also state that a formula doesn't
  have any free variable. This means, that is is invariant under
  substitutions.

### Fix

* Renamed `Seq_Bot_r` to `Seq_Neg_r` [Max Ole Elliger]

## inqlog-v0.14.0 (2025-03-04)

### New

* Proved `Seq_Bot_r` [Max Ole Elliger]

* Syntax-Modules for example signatures. [Max Ole Elliger]

  New Models:
  - `Syntax_single_unary_predicate`
  - `Syntax_single_binary_predicate`

### Changes

* Removed axiom of functional extensionality. [Max Ole Elliger]

  This was gained by multiple steps:
  - Defined the notion of extensional equality of functions.
  - Used this notion for congruence properties.
  - Proved similar Autosubst-Lemmas with respect to `term_eq` and `form_eq`.

  In addition, some `Print Assumptions`-lines were added, at least for
  every proposition, theorem and corollary.

* Documentation for States.v. [Max Ole Elliger]

* Simplified `singleton` by `==b` [Max Ole Elliger]

* Simplified Pred' and used it for Casari.v. [Max Ole Elliger]

* Updated documentation on FO/Support.v. [Max Ole Elliger]

  Just some small improvements

* Renamed `rigid_term` to `term_rigid` [Max Ole Elliger]

* Replaced `state_eq` by `==` in FO/States.v. [Max Ole Elliger]

* Updated documentation on FO/Syntax.v. [Max Ole Elliger]

  Just some small improvements

* Updated documentation on FO/Signatures.v. [Max Ole Elliger]

  Just some small improvements

* Renamed Module-names in Signature.v. [Max Ole Elliger]

* Redefined `lb_form_eq` [Max Ole Elliger]

  This is now done by a `Inductive` as this might make stuff somehow
  smoother.

* Renamed ListBib.v -> ListLib.v. [Max Ole Elliger]

* Added a prelude to manage Imports more easily. [Max Ole Elliger]

### Fix

* Rm unnecessary Setoid instance for nat. [Max Ole Elliger]

## inqlog-v0.13.0 (2025-02-05)

### New

* Finished adaptions to the new model def. [Max Ole Elliger]

* Defined `form_eq` and proved its decidability. [Max Ole Elliger]

* Defined `term_eq` and proved its decidability. [Max Ole Elliger]

* Proved `finite_choice` [Max Ole Elliger]

### Changes

* Polished definitions and so on. [Max Ole Elliger]

  Here are some patterns that have changed:
  - Increased the use of the standard library regarding lists
  - Names of substition lemmas match better to Autosubst-library (`_hsubst`)
  - Moved `support_conseq` to new file `FO/Consequence.v`

* Moved `support_valid_Casari_bd` from Seq.v to Casari.v. [Max Ole Elliger]

## inqlog-v0.12.0 (2025-01-23)

### New

* Finished proof of `support_valid_Casari_bd` [Max Ole Elliger]

  ToDo:
  - The notion of boundness should be checked again.

* Proved `In_sublist_dec` [Max Ole Elliger]

* Proved `support_valid_Casari_bd` [Max Ole Elliger]

* Defined `highest_occ_free_var` [Max Ole Elliger]

* Proved `length_order_wf` [Max Ole Elliger]

  By this, we get wellfounded induction on the length of a list.

* Added some docs regarding theories/FO/Seq.v. [Max Ole Elliger]

* Proved `Seq_mon` [Max Ole Elliger]

* Added rule of cut. [Max Ole Elliger]

* Added Proper-statements for `satisfaction_{forall,exists}` [Max Ole Elliger]

### Changes

* Rewrote cut-rule, almost finished the proof of `Seq_Casari` [Max Ole Elliger]

* Proved some properties about `In_eq` regarding cons, app. [Max Ole Elliger]

* Redefined satisfaction_{forall,exists} [Max Ole Elliger]

  Now using List.Forall, List.Exists for definition

* Changed order of universal quantified vars in Seq. [Max Ole Elliger]

### Fix

* Fixed the definition of `Casari` [Max Ole Elliger]

  Previously, we defined `Casari : (var -> form) -> form`. Unfortunately,
  this definition isn't useful, as one doesn't know the dependence from
  the argument for Casari from their variable argument. This is now fixed
  by using the free variable 0 all the time.

## inqlog-v0.11.0 (2025-01-11)

### New

* Proved `ex_4_5` in FO/Seq.v. [Max Ole Elliger]

* Defined `In_sublist` and proved stuff about it. [Max Ole Elliger]

* Proved Lemma `In_eq_nil` [Max Ole Elliger]

* Proved `mapping_state_Proper` [Max Ole Elliger]

* Defined `In_eq` [Max Ole Elliger]

  Two lists are equivalent via `In_eq`, if they contain the same elements.

### Changes

* Used `In_sublist` for `Seq` [Max Ole Elliger]

* Some improvements regarding `inb`-lemmas. [Max Ole Elliger]

### Fix

* Fixed `Seq_id` [Max Ole Elliger]

  It is enough to enforce, that the two labels are equivalent via `In_eq`.

## inqlog-v0.10.0 (2025-01-08)

### New

* Print Assumptions for `soundness` of Seq. [Max Ole Elliger]

  This concludes thes soundness proof for the sequent calculus.

* Proved `satisfaction_conseq_Iexists_l` [Max Ole Elliger]

* Proved `satisfaction_conseq_Iexists_r` [Max Ole Elliger]

  This includes a small improvement of the statement and `Seq_Iexists_r`.

* Proved `satisfaction_conseq_Forall_l` [Max Ole Elliger]

  This includes a small improvement of the statement and `Seq_Forall_l`.

* Proved `satisfaction_conseq_Forall_r` [Max Ole Elliger]

  This commit also includes various improvements:
  - Introduction of some defining names, e.g. `label` or 'lb_form'
  - Defined `satisfaction_forall` and `satisfaction_exists` to make
    `satisfaction_conseq` more readable.
  - Proved some helping lemmas about them.

* Proved `satisfaction_conseq_Impl_r` [Max Ole Elliger]

  This includes various helper lemmas and the definition of
  `excluding_states`.

* `Proved satisfaction_conseq_Impl_l` [Max Ole Elliger]

* Proved `satisfaction_conseq_Pred_r` [Max Ole Elliger]

* Proved `satisfaction_conseq_Bot_l` [Max Ole Elliger]

* Proved `satisfaction_conseq_Pred_l` [Max Ole Elliger]

  This includes proofs for
  - `In_iff_inb`
  - `substate_mapping_state`

* Proved `satisfaction_conseq_empty` [Max Ole Elliger]

* Proved `satisfaction_conseq_Idisj_l` [Max Ole Elliger]

* Proved `satisfaction_conseq_Idisj_r` [Max Ole Elliger]

* Proved `satisfaction_conseq_Conj_l` [Max Ole Elliger]

* Proved `satisfaction_conseq_Conj_r` [Max Ole Elliger]

* Proved `satisfaction_conseq_id` [Max Ole Elliger]

* Setup structure for soundness of Seq. [Max Ole Elliger]

* Defined `satisfaction` and `satisfaction_conseq` [Max Ole Elliger]

  Both are for labelled formulas and sequents.

  This also includes the definition of `mapping_state`.

* Proved some examples. [Max Ole Elliger]

  Proved
  - Example 4.7 from inqbq_aiml
  - Example 4.8 from inqbq_aiml

* Proved prop_4_6 from inqbq_aiml. [Max Ole Elliger]

* Defined the rules for sequent calculus. [Max Ole Elliger]

* Defined `inb` [Max Ole Elliger]

  `inb` is the boolean twin of the list predicate `In`. It is defined for
  lists of types with decidable equality.

* Proved `singleton_substate` [Max Ole Elliger]

### Changes

* Proved some `support_conseq`-lemmas in Truth.v. [Max Ole Elliger]

  This includes
  - `truth_subst`
  - `support_conseq_Forall_E_classical`
  - `support_conseq_CRAA`
  - `support_conseq_CD`

* Simplified `referent_subst` [Max Ole Elliger]

  It is not necessary that `t` is rigid.

## inqlog-v0.9.0 (2025-01-01)

### New

* More useful `support_conseq`-lemmas. [Max Ole Elliger]

  Proved
  - `support_conseq_in`
  - `support_conseq_trans`
  - `support_conseq_weakening_nil`
  - `support_conseq_weakening_cons_tl`
  - `support_conseq_Bot_I`
  - Changed the style of `support_conseq_Bot_E` from `Bot x` to `Bot 0`

* Proved `support_multiple_charac` [Max Ole Elliger]

* Proved more stuff about `support_conseq` [Max Ole Elliger]

  Proved
  - `support_conseq_Forall_E_rigid`
  - `support_conseq_Iexists_I`
  - and some helper lemmas

* Proved `rigidity_referent` [Max Ole Elliger]

* Some rewrite lemmas for `classical` [Max Ole Elliger]

  - Added a new example formula `EM` (excluded middle)
  - Rewrite lemmas for `classical`
  - `classical_hsubst`

* Some more `support_conseq`-proofs. [Max Ole Elliger]

  This commit includes proofs for
  - `support_multiple_app`
  - `support_conseq_weakening_1`
  - `support_conseq_weakening_2`
  - `support_conseq_Iexists_E`

* Proved some prop. properties of `support_conseq` [Max Ole Elliger]

* Proved `support_conseq_Forall_I` (new version) [Max Ole Elliger]

  This includes some helper lemmas regarding lifting.

* Defined support for multiple formulas. [Max Ole Elliger]

* Defined `rigid_term : term -> Prop` [Max Ole Elliger]

### Changes

* Used new `support_conseq`-rules for CasariAtomic. [Max Ole Elliger]

* Rearranged stuff about Support and Truth. [Max Ole Elliger]

  - Changed some headings
  - Simplified some definitions/proofs
  - Rewrote the Truth-Library with respect to classical (meta) logic
  - Defined `truth_multiple`
  - Defined `truth_conseq`
  - Defined `truth_valid`
  - Added various rewrite-lemmas

* Renamed `classic` to `classical` [Max Ole Elliger]

  As we probably want to use more classic logic, this could be helpful.

* Changed the whole `support_conseq` section. [Max Ole Elliger]

  `support_conseq` can now have multiple assumptions.

## inqlog-v0.8.2 (2024-12-21)

### Fix

* Fixed an undone renaming after merge. [Max Ole Elliger]

## inqlog-v0.8.1 (2024-12-21)

### New

* Added some documentation to Support.v. [Max Ole Elliger]

* Proved `substate_empty_state` [Max Ole Elliger]

* Proved `singleton_refl` [Max Ole Elliger]

* Added some explanation regarding states. [Max Ole Elliger]

* Added explanation regarding models. [Max Ole Elliger]

* Proved [infinitely_many_Proper] [Max Ole Elliger]

* Proved [finitely_many_Proper] [Max Ole Elliger]

### Changes

* Simplified some proofs in Casari.v. [Max Ole Elliger]

* Simplified some proofs in Truth.v. [Max Ole Elliger]

* Simplified some proofs in Support.v. [Max Ole Elliger]

* Proved both directions of `empty_state_not_consistent` [Max Ole Elliger]

* Simplified some proofs in States.v. [Max Ole Elliger]

* Added documentation to Syntax.v. [Max Ole Elliger]

* Documentation for Signatures.v. [Max Ole Elliger]

  This includes the definition of our instances for Casari inside this
  file, so that they can be used as example signatures.

## inqlog-v0.8.0 (2024-12-11)

### New

* Proved `not_support_valid_Casari_IES` [Max Ole Elliger]

  For this, classical logic is used at the level of meta-logic.

* Added rewrite-lemmatas for std. support relation. [Max Ole Elliger]

* Notation for support, ruling_out. [Max Ole Elliger]

* Added notation syntax for formulae. [Max Ole Elliger]

* Added some preliminary headlines. [Max Ole Elliger]

### Changes

* Used new notations for Casari section. [Max Ole Elliger]

* Rm some `firstorder`-Calls to improve runtime. [Max Ole Elliger]

## inqlog-v0.7.0 (2024-11-14)

### New

* Proved `support_valid_CasariAtomic` [Max Ole Elliger]

* Defined support consequence and validity. [Max Ole Elliger]

  This involves some useful lemmas and renamings of existing theorems.

  In addition, I defined a formula called `DNE`, for double negation
  elimination.

* Proved support_CasariDNA. [Max Ole Elliger]

* Proved Casari_truth_conditional. [Max Ole Elliger]

* Defined Truth-Conditionality. [Max Ole Elliger]

  Furthermore, it has been proven that classic formulas are indeed
  truth-conditional.

* Defined classic formulas. [Max Ole Elliger]

  Classic Formulas are formulas without inquisitive disjunction or
  inquisitive existency quantifiers. It can be proven, that any classical
  variant of a formula is indeed classical.

* Introduced `truth` and classical formulas. [Max Ole Elliger]

  Truth is defined as support at singleton states. I implemented a
  subclass of Models (`TDModel`), where truth becomes decidable. By this,
  it can be proven, that any formula and its classical variant are
  truth-equivalent.

### Changes

* Used the `FO/Truth` for `truth_CasariDNA` [Max Ole Elliger]

## inqlog-v0.6.0 (2024-11-02)

### New

* Started working on Casari. [Max Ole Elliger]

  - Defined a signature with exact one predicate (of arity 1) and no
    function symbols.
  - Provided a proof of double negated atomic Casari in Coq's `Prop`.
  - Defined the Casari Scheme as a `form`ula in our syntax.
  - Proved, that Casari Scheme with double negated atoms holds in every
    world.

* Proved Lemma `support_dne_Pred` [Max Ole Elliger]

* Decidable equality for individuals. [Max Ole Elliger]

* Support-properties for defined connectives. [Max Ole Elliger]

  The following propositions are proven:
  - `support_Neg`
  - `support_Top`
  - `support_Disj`
  - `support_Iff`

  This includes the definition of a state ruling out a formula.

* Defined consistent states. [Max Ole Elliger]

  A state is called consistent, if it contains at least one world. It
  follows immediately that every singleton is consistent. Conversly, the
  empty state is inconsistent.

* Characterized the substates of a singleton. [Max Ole Elliger]

* Some properties of singleton. [Max Ole Elliger]

  Proved `singleton_true` and `singleton_false` to use singleton states
  more efficiently.

* Defined singleton states. [Max Ole Elliger]

* Added decidable equality to the type of Worlds. [Max Ole Elliger]

  Using this, one can define singleton states. Another way would be to
  change the type of states to `World -> Prop`.

* Proved substate as a PreOrder. [Max Ole Elliger]

  substate is indeed reflexive and transitive

### Changes

* `PInterpretation` now evaluates to bool. [Max Ole Elliger]

## inqlog-v0.5.2 (2024-10-16)

### Fix

* Fixed the definition of Forall. [Max Ole Elliger]

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
