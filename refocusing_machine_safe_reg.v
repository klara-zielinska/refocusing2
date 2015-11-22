Require Import Util.
Require Import abstract_machine refocusing_machine.
Require Import reduction_semantics reduction_semantics_facts 
               reduction_semantics_props refocusing_semantics.



Module RefEAMSafeReg (R : RED_LANG) (S : RED_REF_SEM R) (AM : REF_EVAL_APPLY_MACHINE R S)
                         (RedReg : SAFE_RED_REGION R) <: AM_SAFE_REGION AM.

  Module RF   := RED_LANG_Facts R.
(*  Module RegF := SAFE_RED_REGION_Facts R RedReg.*)
  Import AM R S.ST.

  Definition safe st := 
      match st with
      | c_eval t k1 k2 c  => RedReg.safe k1 c[t] /\ k1 = init_ckind /\ ~dead_ckind k2
      | c_apply k1 k2 c v => RedReg.safe k1 c[v] /\ k1 = init_ckind /\ ~dead_ckind k2
      end.

  Lemma preservation : forall c1 c2, safe c1 -> c1 → c2 -> safe c2.
  Proof.
    intros st1 st2 H H0.
    destruct H0;
        match goal with
        | G : dec_term ?t ?k = _ |- _ => assert (DTC := dec_term_correct t k);
                                         rewrite G in DTC
        | G : dec_context ?ec ?k ?v = _ |- _ =>
                                         assert (DCC := dec_context_correct ec k v);
                                         rewrite G in DCC;
                                         simpl in H; rewrite DCC in H
        end;
        destruct H as [H [? H2]];
        subst;

    solve 
    [ split; eauto using dec_term_next_alive, dec_context_next_alive,
                       RF.death_propagation2
    | match goal with G : contract ?r = Some ?t |- _ => 
          destruct (RedReg.progresvation _ _ H) as [t2 [? ?]];
          replace t with t2 by congruence;
          split;
          eauto using RF.death_propagation2 end ].
  Qed.


  Local Hint Constructors conf trans.

  Lemma progress : forall c, safe c -> 
                       (exists v, c = c_final v) \/ (exists c', c → c').
  Proof.
    intros st H.
    destruct st;
        destruct H as [H [? H0]];
        subst.

    - remember (dec_term t k2) as d eqn:H1.
      symmetry in H1.
      destruct d;
          assert (DTC := dec_term_correct t k2);
          rewrite H1 in DTC;
          subst;
      try solve 
    (*+*)[eautof].
      +  right.
         destruct (RedReg.progresvation _ _ H) as [t' [? ?]].
         eauto.
    - destruct c.
      + eauto.
      + remember (dec_context ec k2 v) as d eqn:H1.
        symmetry in H1.
        destruct d;
            assert (DCC := dec_context_correct ec k2 v);
            rewrite H1 in DCC;
            subst;
      try solve 
    (***)[eautof].
      *  right.
         simpl in H; rewrite DCC in H.
         destruct (RedReg.progresvation _ _ H) as [t' [? ?]].
         eauto.
  Qed.

End RefEAMSafeReg.
