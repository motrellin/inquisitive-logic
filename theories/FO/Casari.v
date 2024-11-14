From InqLog Require Export Truth.

Instance signature : Signature :=
  {|
    PSymb := unit;
    PAri := fun p => match p with tt => unit end;
    FSymb := Empty_set;
    FAri := fun f => match f with end;
    rigid := fun _ => true
  |}.

Definition Pred' (t : term) := Pred tt (fun arg => t).

Theorem CasariProp (P : var -> Prop) :
  (
    forall x,
      (
        (P x)
        ->
        (forall x, ~ ~ P x)
      )
      ->
      (forall x, ~ ~ P x)
  )
  ->
  (
    forall x, ~ ~ P x
  ).
Proof.
  firstorder.
Qed.

Print Assumptions CasariProp.

Definition Casari (phi : var -> form) : form :=
  Impl
  (
    Forall
    (
      Impl
      (
        Impl
        (
          phi 0
        )
        (
          Forall (phi 0)
        )
      )
      (
        Forall (phi 0)
      )
    )
  )
  (
    Forall (phi 0)
  ).

Theorem Casari_truth_conditional :
  forall phi,
    (forall x, classic (phi x) = true) ->
    truth_conditional (Casari phi).
Proof.
  intros phi H1.
  apply classic_truth_conditional.
  simpl.
  rewrite H1.
  reflexivity.
Qed.

Definition CasariDNA : form :=
  Casari (fun x => Neg (Neg (Pred' (Var x)))).

Definition CasariAtomic : form :=
  Casari (fun x => Pred' (Var x)).

Theorem truth_CasariDNA `{@Model signature} :
  forall w a,
    truth CasariDNA w a.
Proof.
  intros w1 a.

  intros s2 H1 H2.

  apply substate_singleton in H1 as [H1|H1]; rewrite H1 in *; clear s2 H1.
  now apply empty_state_property.

  intros i1.
  rewrite support_Neg.
  intros [s3 [[w2 H3] [H4 H5]]].

  enough (
    exists s,
      support (Forall (Neg (Neg (Pred' (Var 0))))) s (i1 .: a) /\
      substate s3 s
  ) as [s4 [H6 H7]].
  {
    specialize (H6 i1). fold support in H6.

    rewrite support_Neg in H6.
    apply H6.
    exists s3.
    firstorder.
  }

  specialize (H2 i1). fold support in H2.
  remember (Neg (Neg (Pred' (Var 0)))) as phi1 eqn:eq1.
  remember (Forall phi1) as phi2 eqn:eq2.
  remember (Impl phi1 phi2) as phi3 eqn:eq3.


  eexists.
  split.

  apply H2. exact H4.

  fold support.
  subst phi3.

  apply substate_singleton in H4 as [H4|H4]; rewrite H4 in *; clear s3 H4.
  now apply empty_state_property.

  intros s4 H6 H7.

  apply substate_singleton in H6 as [H6|H6]; rewrite H6 in *; clear s4 H6.
  now apply empty_state_property.

  exfalso.

  rewrite eq1 in H7.
  rewrite support_Neg in H7.
  apply H7.

  eexists.
  repeat split.
  -
    eexists.
    exact H3.
  -
    reflexivity.
  -
    exact H5.
  -
    reflexivity.
Qed.

Corollary support_valid_CasariDNA :
  support_valid CasariDNA.
Proof.
  intros M s a.
  apply Casari_truth_conditional.
  -
    reflexivity.
  -
    intros w H1.
    apply truth_CasariDNA.
Qed.

Theorem support_conseq_CasariDNA_CasariAtomic :
  support_conseq CasariDNA CasariAtomic.
Proof.
  unfold CasariDNA.
  unfold CasariAtomic.
  unfold Casari.

  apply support_conseq_Impl.
  apply support_conseq_Forall.
  apply support_conseq_Impl.
  apply support_conseq_Impl.

  firstorder.

  apply support_conseq_Forall.

  apply support_valid_Impl_conseq.
  intros *.
  apply support_valid_DNE_Pred.

  apply support_conseq_Forall.

  firstorder.

  apply support_conseq_Forall.
  apply support_valid_Impl_conseq.
  intros *.
  apply support_valid_DNE_Pred.
Qed.

Corollary support_valid_CasariAtomic :
  support_valid CasariAtomic.
Proof.
  eapply support_valid_conseq_valid.
  -
    exact support_valid_CasariDNA.
  -
    exact support_conseq_CasariDNA_CasariAtomic.
Qed.
