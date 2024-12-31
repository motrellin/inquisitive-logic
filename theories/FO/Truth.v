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
    subst w'.
    exact H1.
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

(** ** Truth of multiple formulas *)

Fixpoint truth_multiple `{Model} (Phi : list form) :
  World -> assignment -> Prop :=

  match Phi with
  | nil =>
      fun _ _ =>
      True
  | phi :: Phi' =>
      fun w a =>
      truth phi w a /\
      truth_multiple Phi' w a
  end.

Remark truth_multiple_support_multiple `{Model} :
  forall Phi w a,
    truth_multiple Phi w a <->
    support_multiple Phi (singleton w) a.
Proof.
  induction Phi; firstorder.
Qed.

Fact truth_multiple_truth `{Model} :
  forall phi w a,
    truth_multiple (phi :: nil) w a <->
    truth phi w a.
Proof.
  firstorder.
Qed.

Lemma truth_multiple_app `{Model} :
  forall Phi Psi w a,
    truth_multiple (Phi ++ Psi) w a <->
    truth_multiple Phi w a /\
    truth_multiple Psi w a.
Proof.
  induction Phi; firstorder.
Qed.

(** * Truth consequence *)

Definition truth_conseq
  `{S : Signature}
  (cxt : list form)
  (phi : form) :
  Prop :=

  forall `(M : @Model S) w a,
    truth_multiple cxt w a ->
    truth phi w a.

(** * Truth validity *)

Definition truth_valid `{Signature} (phi : form) : Prop :=
  truth_conseq nil phi.

Remark truth_valid_charac `{S : Signature} :
  forall phi,
    (forall `(M : @Model S) w a, truth phi w a) <->
    truth_valid phi.
Proof.
  firstorder.
Qed.

Example truth_valid_EM `{Signature} :
  forall phi,
    truth_valid (EM phi).
Proof.
  intros phi.
  apply truth_valid_charac.
  intros M w a.
  unfold EM.
  rewrite truth_Disj.
  rewrite truth_Neg.
  apply classic.
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
    subst w'.
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
