From InqLog.FO Require Export Support.

(** * Truth satisfaction *)

Definition truth `{Model} (phi : form) (w : World) (a : assignment) : Prop :=
  (singleton w), a |= phi.

(** ** Truth satisfaction for basic connectives *)

Lemma truth_Pred `{Model} :
  forall p args w a,
    truth <{Pred p args}> w a <->
    PInterpretation w p (fun arg => referent (args arg) w a) = true.
Proof.
  intros p ari w a.
  split.
  -
    intros H1.
    apply H1.
    apply singleton_refl.
  -
    intros H1 w' H2.
    apply singleton_true in H2.
    rewrite <- H1.
    assert (H3 : PInterpretation w' = PInterpretation w).
    {
      rewrite H2.
      reflexivity.
    }
    rewrite H3.
    f_equiv.
    intros arg.
    rewrite H2.
    reflexivity.
Qed.

Lemma truth_Bot `{Model} :
  forall v w a,
    (truth <{Bot v}> w a) <-> False.
Proof.
  intros ? w a.
  split.
  -
    intros H1.
    specialize (H1 w).
    rewrite singleton_refl in H1.
    discriminate.
  -
    contradiction.
Qed.

Lemma truth_Impl `{Model} :
  forall phi1 phi2 w a,
  truth <{phi1 -> phi2}> w a <->
  (truth phi1 w a -> truth phi2 w a).
Proof.
  intros phi1 phi2 w a.
  split.
  -
    firstorder.
  -
    intros H1 t H2 H3.
    apply substate_singleton in H2 as [H2|H2].
    +
      rewrite H2.
      apply empty_state_property.
    +
      rewrite H2 in *.
      apply H1.
      exact H3.
Qed.

Lemma truth_Conj `{Model} :
  forall phi1 phi2 w a,
    truth <{phi1 /\ phi2}> w a <->
    truth phi1 w a /\ truth phi2 w a.
Proof.
  firstorder.
Qed.

Lemma truth_Idisj `{Model} :
  forall phi1 phi2 w a,
    truth <{phi1 \\/ phi2}> w a <->
    truth phi1 w a \/ truth phi2 w a.
Proof.
  firstorder.
Qed.

Lemma truth_Forall `{Model} :
  forall phi w a,
    truth <{forall phi}> w a <->
    forall i,
      truth phi w (i .: a).
Proof.
  firstorder.
Qed.

Lemma truth_Iexists `{Model} :
  forall phi w a,
    truth <{iexists phi}> w a <->
    exists i,
      truth phi w (i .: a).
Proof.
  firstorder.
Qed.

(** ** Truth satisfaction for defined connectives *)

Lemma truth_Neg `{Model} :
  forall phi w a,
    truth <{~ phi}> w a <->
    ~ truth phi w a.
Proof.
  intros phi w a.
  unfold Neg.
  rewrite truth_Impl.
  rewrite truth_Bot.
  reflexivity.
Qed.

Lemma truth_Top `{Model} :
  forall w a,
    truth Top w a <-> True.
Proof.
  intros w a.
  unfold Top.
  rewrite truth_Neg.
  rewrite truth_Bot.
  easy.
Qed.

Lemma truth_Disj `{Model} :
  forall phi1 phi2 w a,
    truth <{phi1 \/ phi2}> w a <->
    truth phi1 w a \/ truth phi2 w a.
Proof.
  intros phi1 phi2 w a.
  unfold Disj.
  rewrite truth_Neg.
  rewrite truth_Conj.
  do 2 rewrite truth_Neg.
  apply NNPP.
  firstorder.
Qed.

Lemma truth_Iff `{Model} :
  forall phi1 phi2 w a,
    truth <{phi1 <-> phi2}> w a <->
    (truth phi1 w a <-> truth phi2 w a).
Proof.
  intros phi1 phi2 w a.
  unfold Iff.
  rewrite truth_Conj.
  do 2 rewrite truth_Impl.
  reflexivity.
Qed.

Lemma truth_Exists `{Model} :
  forall phi w a,
    truth <{exists phi}> w a <->
    exists i,
      truth phi w (i .: a).
Proof.
  intros phi w a.
  unfold Exists.
  rewrite truth_Neg.
  rewrite truth_Forall.
  split.
  -
    intros H1.
    apply NNPP.
    intros H2.
    apply H1.
    intros i.
    rewrite truth_Neg.
    firstorder.
  -
    intros [i H1] H2.
    specialize (H2 i).
    rewrite truth_Neg in H2.
    contradiction.
Qed.

Lemma truth_Iquest `{Model} :
  forall phi w a,
    truth <{? phi}> w a <-> True.
Proof.
  intros phi w a.
  unfold Iquest.
  rewrite truth_Idisj.
  rewrite truth_Neg.
  apply NNPP.
  firstorder.
Qed.

(** ** Other Truth satisfaction rules *)

Proposition truth_classical_variant `{Model} :
  forall phi w a,
    truth (classical_variant phi) w a <->
    truth phi w a.
Proof.
  induction phi as
  [p args
  |?
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1
  |phi1 IH1].
  all: intros w a.
  all: simpl.
  all: try reflexivity.
  -
    specialize (IH1 w a).
    specialize (IH2 w a).
    do 2 rewrite truth_Impl.
    firstorder.
  -
    specialize (IH1 w a).
    specialize (IH2 w a).
    firstorder.
  -
    rewrite truth_Idisj.
    rewrite truth_Disj.
    rewrite IH1, IH2.
    reflexivity.
  -
    do 2 rewrite truth_Forall.
    split.
    all: intros H1 i.
    all: apply IH1.
    all: exact (H1 i).
  -
    rewrite truth_Iexists.
    rewrite truth_Exists.
    split.
    all: intros [i H1].
    all: exists i.
    all: apply IH1.
    all: exact H1.
Qed.

Print Assumptions truth_classical_variant.

(** ** Truth of multiple formulas *)

Definition truth_mult
  `{Model}
  (w : World)
  (a : assignment) :
  list form -> Prop :=

  List.Forall (fun phi => truth phi w a).

Remark truth_mult_support_mult `{Model} :
  forall Phi w a,
    truth_mult w a Phi <->
    support_mult (singleton w) a Phi.
Proof.
  firstorder.
Qed.

(** ** Truth of some formulas *)

Definition truth_some
  `{Model}
  (w : World)
  (a : assignment) :
  list form -> Prop :=

  List.Exists (fun phi => truth phi w a).

Remark truth_some_support_some `{Model} :
  forall Phi w a,
    truth_some w a Phi <->
    support_some (singleton w) a Phi.
Proof.
  firstorder.
Qed.

(** * Truth-conditional formulas *)

Definition truth_conditional `{S : Signature} (phi : form) : Prop :=
  forall `(M : @Model S) (s : state) (a : assignment),
    (forall w, s w = true -> truth phi w a) ->
    s, a |= phi.

Remark truth_conditional_other_direction `{S : Signature} :
  forall phi `(M : @Model S) s a,
    s, a |= phi ->
    forall w,
      s w = true ->
      truth phi w a.
Proof.
  intros phi M s a H1 w H2.
  eapply persistency.
  -
    exact H1.
  -
    intros w' H3.
    apply singleton_true in H3.
    rewrite H3.
    exact H2.
Qed.

Lemma truth_conditional_Pred `{Signature} :
  forall p args,
    truth_conditional (Pred p args).
Proof.
  intros p args M s a.
  intros H1 w1 H2.
  apply truth_Pred.
  auto using truth_Pred.
Qed.

Lemma truth_conditional_Bot `{Signature} :
  forall x,
    truth_conditional (Bot x).
Proof.
  intros x M s a H1 w.
  specialize (H1 w).
  rewrite truth_Bot in H1.
  destruct (s w); easy.
Qed.

Lemma truth_conditional_Impl `{Signature} :
  forall phi psi,
    truth_conditional psi ->
    truth_conditional <{phi -> psi}>.
Proof.
  intros phi psi H1 M s a H2 t H3 H4.
  apply H1.
  intros w H5.
  specialize (H2 w).
  rewrite truth_Impl in H2.
  eauto using truth_conditional_other_direction.
Qed.

Lemma truth_conditional_Conj `{Signature} :
  forall phi psi,
    truth_conditional phi ->
    truth_conditional psi ->
    truth_conditional <{phi /\ psi}>.
Proof.
  intros phi psi H1 H2 M s a H3.
  split.
  -
    apply H1.
    intros w H4.
    apply H3.
    exact H4.
  -
    apply H2.
    intros w H4.
    apply H3.
    exact H4.
Qed.

Lemma truth_conditional_Forall `{Signature} :
  forall phi,
    truth_conditional phi ->
    truth_conditional <{forall phi}>.
Proof.
  intros phi H1 M s a H2 i.
  apply H1.
  intros w H3.
  apply H2.
  exact H3.
Qed.

Lemma truth_conditional_Neg `{Signature} :
  forall phi,
    truth_conditional <{~ phi}>.
Proof.
  intros phi M s a H1.
  unfold Neg.
  apply truth_conditional_Impl.
  -
    apply truth_conditional_Bot.
  -
    exact H1.
Qed.

Lemma truth_conditional_Disj `{Signature} :
  forall phi psi,
    truth_conditional <{phi \/ psi}>.
Proof.
  intros phi psi.
  unfold Disj.
  apply truth_conditional_Neg.
Qed.

Lemma truth_conditional_Iff `{Signature} :
  forall phi psi,
    truth_conditional phi ->
    truth_conditional psi ->
    truth_conditional <{phi <-> psi}>.
Proof.
  intros phi psi H1 H2.
  unfold Iff.
  apply truth_conditional_Conj.
  all: apply truth_conditional_Impl.
  all: assumption.
Qed.

Lemma truth_conditional_Exists `{Signature} :
  forall phi,
    truth_conditional <{exists phi}>.
Proof.
  intros phi.
  unfold Exists.
  apply truth_conditional_Neg.
Qed.

Proposition classical_truth_conditional `{S : Signature} :
  forall phi,
    classical phi = true ->
    truth_conditional phi.
Proof.
  induction phi as
  [p args
  |?
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1
  |phi1 IH1].
  all: intros H1.
  -
    apply truth_conditional_Pred.
  -
    apply truth_conditional_Bot.
  -
    simpl in H1.
    apply andb_true_iff in H1 as [_ H1].
    auto using truth_conditional_Impl.
  -
    simpl in H1.
    apply andb_true_iff in H1 as [H1 H2].
    auto using truth_conditional_Conj.
  -
    discriminate.
  -
    auto using truth_conditional_Forall.
  -
    discriminate.
Qed.

Print Assumptions classical_truth_conditional.

Lemma truth_hsubst `{Model} :
  forall phi w a sigma,
    truth phi w (fun x => referent (sigma x) w a) <->
    truth phi.|[sigma] w a.
Proof.
  induction phi as
  [p args
  |?
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1 phi2 IH2
  |phi1 IH1
  |phi1 IH1].
  all: intros w a sigma.
  -
    split.
    all: intros H1.
    all: apply truth_Pred.
    all: apply truth_Pred in H1.
    all: rewrite <- H1.
    all: f_equiv.
    all: intros arg.
    +
      apply referent_subst.
    +
      symmetry.
      apply referent_subst.
  -
    reflexivity.
  -
    split.
    all: intros H1.
    all: apply truth_Impl.
    all: intros H2.
    all: apply IH2.
    all: simpl hsubst in H1.
    all: rewrite truth_Impl in H1.
    all: apply H1.
    all: apply IH1.
    all: exact H2.
  -
    simpl hsubst.
    do 2 rewrite truth_Conj.
    rewrite IH1, IH2.
    reflexivity.
  -
    simpl hsubst.
    do 2 rewrite truth_Idisj.
    rewrite IH1, IH2.
    reflexivity.
  -
    simpl hsubst.
    do 2 rewrite truth_Forall.
    split.
    all: intros H1 i.
    all: specialize (H1 i).
    +
      apply IH1.
      red.
      rewrite unnamed_helper_Support_24.
      exact H1.
    +
      apply IH1 in H1.
      red.
      rewrite <- unnamed_helper_Support_24.
      exact H1.
  -
    simpl hsubst.
    do 2 rewrite truth_Iexists.
    split.
    all: intros [i H1].
    all: exists i.
    +
      apply IH1.
      red.
      rewrite unnamed_helper_Support_24.
      exact H1.
    +
      apply IH1 in H1.
      red.
      rewrite <- unnamed_helper_Support_24.
      exact H1.
Qed.

(** * Validiy of [DNE]

   In this section, we want to point out that [DNE] is not
   schematically support-valid.

   For this, we will first try to prove this property to
   see, where the proof fails.

   After this, we will point out that [DNE] is at least
   valid for [classical] formulas.

   Last, we will present a counterexample with a
   non-classical formula.
 *)

Theorem support_valid_DNE `{Signature} :
  forall phi,
    support_valid (DNE phi).
Proof.
  intros phi M s1 a s2 H1 H2.
  destruct (classic (consistent s2)) as [H3|H3].
  -
    apply NNPP.
    intros H4.
    rewrite support_Neg in H2.
    apply H2.
    exists s2.
    repeat split.
    +
      exact H3.
    +
      reflexivity.
    +
      rewrite support_Neg.
      intros [s3 [H5 [H6 H7]]].
      apply H4.
      eapply persistency.
      *
        exact H7.
      *
        Fail apply H6.
Abort.

Lemma truth_valid_DNE `{Model} :
  forall phi w a,
    truth (DNE phi) w a.
Proof.
  intros phi w a.
  unfold DNE.
  rewrite truth_Impl.
  intros H1.
  do 2 rewrite truth_Neg in H1.
  apply NNPP.
  exact H1.
Qed.

Theorem support_valid_DNE_classical `{Signature} :
  forall phi,
    classical phi = true ->
    support_valid (DNE phi).
Proof.
  intros phi H1 M s a.
  apply classical_truth_conditional.
  {
    simpl.
    rewrite H1.
    reflexivity.
  }
  intros w H2.
  apply truth_valid_DNE.
Qed.

Module not_support_valid_DNE.

  Import Syntax_single_unary_predicate.
  Existing Instance two_Worlds_Model.

  Lemma DNE_counterex_part_1 :
      most_inconsistent,pointed_assignment |=
        <{~ ~ ? Pred' (Var 0)}>.
  Proof.
    rewrite support_Neg.
    intros [s2 [[w H1] [H2 H3]]].
    rewrite support_Neg in H3.
    apply H3.
    exists (singleton w).
    repeat split.
    -
      apply singleton_consistent.
    -
      intros w' H4.
      apply singleton_true in H4.
      rewrite H4.
      exact H1.
    -
      apply truth_Iquest.
      exact I.
  Qed.

  Lemma DNE_counterex_part_2 :
    ~ (
        most_inconsistent,pointed_assignment |=
        <{? Pred' (Var 0)}>
    ).
  Proof.
    intros [H1|H1].
    -
      simpl in H1.
      specialize (H1 false eq_refl).
      discriminate.
    -
      simpl in H1.
      specialize (H1
        (singleton true)
        (substate_most_inconsistent _)
      ).
      assert (H2 :
        forall w, singleton true w = true -> w = true
      ).
      {
        intros w H2.
        apply singleton_true in H2.
        exact H2.
      }
      specialize (H1 H2 true).
      apply singleton_false in H1.
      apply H1.
      reflexivity.
  Qed.

  Theorem DNE_counterex :
    ~ (
        most_inconsistent,pointed_assignment |=
        DNE <{? Pred' (Var 0)}>
      ).
  Proof.
    intros H1.
    eapply DNE_counterex_part_2.
    apply H1; try reflexivity.
    apply DNE_counterex_part_1.
  Qed.

  Corollary not_support_valid_DNE :
    ~ forall phi,
        support_valid (DNE phi).
  Proof.
    intros H1.
    apply DNE_counterex.
    apply H1.
  Qed.

End not_support_valid_DNE.

(** * Validity of [Kuroda] *)

Example support_valid_Kuroda `{Signature} :
  forall phi,
    support_valid (Kuroda phi).
Proof.
  intros phi.
  intros m s1 a.
  intros s2 H1 H2.
  apply truth_conditional_Neg.
  intros w H3.
  rewrite truth_Neg.
  intros H4.
  rewrite truth_Neg in H4.
  apply H4.
  rewrite truth_Forall.
  intros i.
  rewrite support_Forall in H2.
  specialize (H2 i).
  eapply truth_valid_DNE; try reflexivity.
  fold support.
  eapply persistency; try exact H2.
  intros w' H5.
  apply singleton_true in H5.
  rewrite H5.
  exact H3.
Qed.
