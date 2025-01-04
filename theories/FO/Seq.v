From InqLog.FO Require Export Truth.

(* whole section from inqbq_aiml *)

Inductive Seq `{Signature} :
  relation (list ((list nat)*form)) :=
  | Seq_empty :
      forall ls rs phi,
        In (pair nil phi) rs ->
        Seq ls rs
  | Seq_id :
      forall ns ls rs p args,
        In (pair ns (Pred p args)) ls ->
        In (pair ns (Pred p args)) rs ->
        Seq ls rs
  | Seq_Bot_l :
      forall n ns ls rs x,
        In (pair ns (Bot x)) ls ->
        In n ns ->
        Seq ls rs
  | Seq_Pred_r :
      forall ns ls rs p args,
        In (pair ns (Pred p args)) rs ->
        (forall n,
          In n ns ->
          Seq ls ((pair (n :: nil) (Pred p args)) :: rs)
        ) ->
        Seq ls rs
  | Seq_Pred_l :
      forall ns1 ns2 ls rs p args,
        In (pair ns1 (Pred p args)) ls ->
        (forall n,
          In n ns2 ->
          In n ns1
        ) ->
        Seq ((pair ns2 (Pred p args)) :: ls) rs ->
        Seq ls rs
  | Seq_Impl_r :
      forall ns ls rs phi psi,
        In (pair ns <{phi -> psi}>) rs ->
        (forall ns',
          (forall n,
            In n ns' ->
            In n ns
          ) ->
          Seq ((pair ns' phi) :: ls) ((pair ns' psi) :: rs)
        ) ->
        Seq ls rs
  | Seq_Impl_l :
      forall ns1 ns2 ls rs phi psi,
        In (pair ns1 <{phi -> psi}>) ls ->
        (forall n,
          In n ns2 ->
          In n ns1
        ) ->
        Seq ls ((pair ns2 phi) :: rs) ->
        Seq ((pair ns2 psi) :: ls) rs ->
        Seq ls rs
  | Seq_Conj_r :
      forall ns ls rs phi psi,
        In (pair ns <{phi /\ psi}>) rs ->
        Seq ls ((pair ns phi) :: rs) ->
        Seq ls ((pair ns psi) :: rs) ->
        Seq ls rs
  | Seq_Conj_l :
      forall ns ls rs phi psi,
        In (pair ns <{phi /\ psi}>) ls ->
        Seq ((pair ns phi) :: (pair ns psi) :: ls) rs ->
        Seq ls rs
  | Seq_Idisj_r :
      forall ns ls rs phi psi,
        In (pair ns <{phi \\/ psi}>) rs ->
        Seq ls ((pair ns phi) :: (pair ns psi) :: rs) ->
        Seq ls rs
  | Seq_Idisj_l :
      forall ns ls rs phi psi,
        In (pair ns <{phi \\/ psi}>) ls ->
        Seq ((pair ns phi) :: ls) rs ->
        Seq ((pair ns psi) :: ls) rs ->
        Seq ls rs
  | Seq_Forall_r :
      forall ns ls rs phi,
        In (pair ns <{forall phi}>) rs ->
        Seq
        (
          map (fun x => pair (fst x) (snd x).|[ren (+1)]) ls
        )
        (
          (pair ns phi) ::
          map (fun x => pair (fst x) (snd x).|[ren (+1)]) rs
        ) ->
        Seq ls rs
  | Seq_Forall_l :
      forall ns ls rs phi t,
        In (pair ns <{forall phi}>) ls ->
        rigid_term t ->
        Seq
        (
          (pair ns phi.|[t/]) ::
          (pair ns <{forall phi}>) ::
          ls
        )
        (
          rs
        ) ->
        Seq ls rs
  | Seq_Iexists_r :
      forall ns ls rs phi t,
        In (pair ns <{iexists phi}>) rs ->
        rigid_term t ->
        Seq ls
        (
          (pair ns phi.|[t/]) ::
          (pair ns <{iexists phi}>) ::
          rs
        ) ->
        Seq ls rs
  | Seq_Iexists_l :
      forall ns ls rs phi,
        In (pair ns <{iexists phi}>) ls ->
        Seq
        (
          (pair ns phi) ::
          map (fun x => pair (fst x) (snd x).|[ren (+1)]) ls
        )
        (
          map (fun x => pair (fst x) (snd x).|[ren (+1)]) rs
        ) ->
        Seq ls rs.
