Require Import Util.
Require Import Program.
Require Import refocusing_semantics.
Require Import refocusing_machine.
Require Import reduction_semantics_facts.
Require Import refocusing_semantics_facts.




Module PreAbstractMachine_Correct (R : RED_LANG) (RS : RED_REF_SEM R)
                                  (PAM : PRE_ABSTRACT_MACHINE R RS). 

  Import R.
  Module RF := RED_LANG_Facts R.
  Import RF.


  Lemma dec_RS2PAM : forall {t k1 k2} {c : context k1 k2} {d}, 
                         RS.dec t c d -> PAM.dec t c d.
  Proof with eauto.
    induction 1 using RS.dec_Ind with 
    (P := fun t _ _ c d (_ : RS.dec t c d)    => PAM.dec t c d)
    (P0:= fun _ v _ c d (_ : RS.decctx v c d) => PAM.decctx v c d);
    solve 
    [ econstructor; eauto
    | eapply PAM.d_term; eauto
    | eapply PAM.dc_term; eauto ].
  Qed.


  Lemma dec_PAM2RS : forall {t k1 k2} {c : context k1 k2} {d}, 
                         PAM.dec t c d -> RS.dec t c d.
  Proof with eauto.
    induction 1 using PAM.dec_Ind with 
    (P := fun t _ _ c d (_ : PAM.dec t c d)    => RS.dec t c d)
    (P0:= fun _ v _ c d (_ : PAM.decctx v c d) => RS.decctx v c d);
    solve
    [ econstructor; eauto
    | eapply RS.d_term; eauto
    | eapply RS.dc_term; eauto ].
  Qed.


  Lemma dec_eqv: forall {t k1 k2} {c : context k1 k2} {d}, 
                     RS.dec t c d <-> PAM.dec t c d.
  Proof with auto using dec_RS2PAM, dec_PAM2RS.
    intuition...
  Qed.


  Lemma iter_RS2PAM : forall {k} {d : decomp k} {v}, 
                          RS.iter d v -> PAM.iter d v.
  Proof with eauto.
    induction 1.
    - constructor...
    - econstructor...
      dependent destruction H0.
      apply dec_RS2PAM.
      apply RS.dec_plug in H0.
      + erewrite (compose_empty _)...
      + eapply (proper_death2 [.])...
  Qed.


  Lemma iter_PAM2RS : forall {k} {d : decomp k} {v}, 
                          PAM.iter d v -> RS.iter d v.
  Proof with eauto.
    induction 1.
    - constructor.
    - econstructor...
      constructor.
      apply RS.dec_plug_rev.
      + eapply (proper_death2 [.])...
      + rewrite <- compose_empty...
        apply dec_PAM2RS...
  Qed.


  Lemma iter_eqv : forall {k} {d : decomp k} {v}, 
                       RS.iter d v <-> PAM.iter d v.

  Proof with auto using iter_RS2PAM, iter_PAM2RS.
    intuition...
  Qed.


  Lemma eval_RS2PAM : forall {t v}, RS.eval t v -> PAM.eval t v.
  Proof with eauto.
    intros t v H.
    dependent destruction H; econstructor.
    - dependent destruction H.
      apply dec_RS2PAM...
    - apply iter_RS2PAM...
  Qed.


  Lemma eval_PAM2RS : forall {t v}, PAM.eval t v -> RS.eval t v.
  Proof with eauto.
    intros t v H.
    dependent destruction H; econstructor.
    - constructor.
      eapply dec_PAM2RS...
    - apply iter_PAM2RS...
  Qed.


  Theorem eval_OK : forall {t v} , RS.eval t v <-> PAM.eval t v.

  Proof with auto using eval_PAM2RS, eval_RS2PAM.
    intuition...
  Qed.

End PreAbstractMachine_Correct.




Module StagedAbstractMachine_Correct (R : RED_LANG) (RS : RED_REF_SEM R)
                                     (SAM : STAGED_ABSTRACT_MACHINE R RS).

  Module RF   := RED_LANG_Facts R.
  Module RSF  := RED_SEM_Facts R RS.
  Module RSD  := RedRefSemDet R RS.
  Module PAM := PreAbstractMachine R RS.
  Module PAMC := PreAbstractMachine_Correct R RS PAM.
  Import R.
  Import RF.
  Import RSF.



  Lemma dec_PAM2SAM : forall {t k1 k2} {c : context k1 k2} {d v},
                          PAM.dec t c d -> SAM.iter d v -> SAM.dec t c v.
  Proof with eauto.
    induction 1 using PAM.dec_Ind with
    (P  := fun t _ _ c d (_ : PAM.dec t c d)    => 
               forall v,  SAM.iter d v  -> SAM.dec t c v)
    (P0 := fun _ v _ c d (_ : PAM.decctx v c d) => 
               forall v', SAM.iter d v' -> SAM.decctx v c v');
    intros; simpl; solve 
    [ econstructor; eauto
    | eapply SAM.d_v; eauto
    | eapply SAM.d_many; eauto 
    | eapply SAM.dc_val; eauto
    | eapply SAM.dc_term; eauto ].
  Qed.


  Lemma dec_SAM2PAM : forall {t k1 k2} {c : context k1 k2} {d v},
                          SAM.dec t c v -> PAM.dec t c d -> PAM.iter d v.

  Proof with eauto using proper_death2, (proper_death2 [.]).
    intros t k1 k2 c d v H; revert d.

    induction H using SAM.dec_Ind with
    (P  := fun t _ _ c v  (_ : SAM.dec t c v)     => 
               forall d, PAM.dec t c d -> PAM.iter d v)
    (P0 := fun _ v _ c v' (_ : SAM.decctx v c v') => 
               forall d, PAM.decctx v c d -> PAM.iter d v')
    (P1 := fun _ d v      (_ : SAM.iter d v)      => 
               PAM.iter d v);

        try (intros d0 G; 
             dependent destruction G; 
             try match goal with H : _ =: _ ~= _ =: _ |- _ => inversion_ccons H end);

    try solve 
    [ constructor

    | eauto

    | match goal       with H0 : ?x = ?d0,  H1 : ?x = ?d1 |- _ => 
      match type of d0 with SAM.ST.interm_dec _ => 
          rewrite H0 in H1; inversion H1; subst; eauto 
      end end ].

    (* the last case *)
    - destruct (dec_total c[t] k1) as (d, H0)...
      assert (PAM.dec t c d).
      {
          rewrite <- PAMC.dec_eqv.
          dependent destruction H0.
          apply RS.dec_plug in H0...
          rewrite <- compose_empty in H0.
          assumption.
      }
      econstructor...
  Qed.


  Lemma iter_PAM2SAM : forall {k} {d : decomp k} {v}, PAM.iter d v -> SAM.iter d v.

  Proof with eauto using dec_PAM2SAM.
    induction 1; [ constructor 1 | econstructor 2 ]...
  Qed.


  Lemma eval_PAM2SAM : forall {t} {v : value init_ckind}, PAM.eval t v -> SAM.eval t v.

  Proof with eauto using iter_PAM2SAM, dec_PAM2SAM.
    intros t v H; dependent destruction H; constructor...
  Qed.


  Lemma eval_SAM2PAM : forall {t v}, SAM.eval t v -> PAM.eval t v.

  Proof with eauto using (proper_death2 [.]), PAMC.dec_eqv.
    intros t v H.
    dependent destruction H.
    destruct (dec_total t init_ckind) as (d, H0).
    - dependent destruction H...
      + inversion H0; dep_subst...
      + intro G; rewrite SAM.ST.dec_term_from_dead in H...
    - dependent destruction H0. econstructor...
      + eapply PAMC.dec_eqv...
      + eapply dec_SAM2PAM...
        apply PAMC.dec_eqv...
  Qed.


  Theorem eval_OK : forall {t v}, RS.eval t v <-> SAM.eval t v.

  Proof with auto using PAMC.eval_OK, eval_SAM2PAM, eval_PAM2SAM.
    etransitivity...
    intuition...
  Qed.

End StagedAbstractMachine_Correct.




Module EvalApplyMachine_Correct (R : RED_LANG) (RS : RED_REF_SEM R)
                                (EAM : EVAL_APPLY_MACHINE R RS).

  Module SAM  := StagedAbstractMachine R RS.
  Module SAMC := StagedAbstractMachine_Correct R RS SAM.
  Import R.
  Import RS.
  Export ST.



  Local Hint Constructors EAM.dec EAM.decctx EAM.eval.

  Lemma dec_SAM2EAM : forall {t k1 k2} {c : context k1 k2} {v}, 
                          SAM.dec t c v -> EAM.dec t c v.
  Proof.
    intros t k1 k2 c v.

    induction 1 using SAM.dec_Ind with
    (P := fun t _ _ c v  (_ : SAM.dec t c v)     => EAM.dec t c v)
    (P0:= fun _ v _ c v' (_ : SAM.decctx v c v') => EAM.decctx v c v')
    (P1:= fun k d v      (_ : SAM.iter d v)      => 
              match d with
              | d_val v'    => ~ dead_ckind k -> EAM.decctx v [.] v'
              | d_red _ r c => forall t, contract r = Some t -> EAM.dec t c v
              end);
        intros;

    match goal with 

    | _ => solve [eauto]

    | H : SAM.iter _ _ |- _ => 
          inversion H; dep_subst; 
          solve [eauto] 

    | H0 : contract ?r = ?t0 , H1 : contract ?r = ?t1 |- _ =>
          rewrite H0 in H1; 
          inversion H1; subst; 
          solve [eauto]
    end.
  Qed.


  Local Hint Constructors SAM.dec SAM.decctx SAM.iter SAM.eval.

  Lemma dec_EAM2SAM : forall {t k1 k2} {c : context k1 k2} {v}, 
                          EAM.dec t c v -> SAM.dec t c v.
  Proof with eauto.
    induction 1 using EAM.dec_Ind with
    (P := fun t _ _ c v  (_ : EAM.dec t c v)     => SAM.dec t c v)
    (P0:= fun _ v _ c v' (_ : EAM.decctx v c v') => SAM.decctx v c v')
    ...
  Qed.


  Lemma eval_SAM_EAM : forall {t v}, SAM.eval t v <-> EAM.eval t v.

  Proof.
    split; 

    solve
    [ intro H;
      dependent destruction H; 
      eauto using dec_SAM2EAM, dec_EAM2SAM ].
  Qed.


  Theorem eval_OK : forall {t v}, RS.eval t v <-> EAM.eval t v.
  Proof with eauto using SAMC.eval_OK, eval_SAM_EAM.
    etransitivity...
  Qed.

End EvalApplyMachine_Correct.




Module ProperEAMachine_Correct (R : RED_LANG) (RS : RED_REF_SEM R) 
                               (PEAM : PROPER_EA_MACHINE R RS).

  Module EAM  := EvalApplyMachine R RS.
  Module EAMC := EvalApplyMachine_Correct R RS EAM.
  Import R.
  Import RS.ST.
  Import PEAM.


  Local Hint Constructors PEAM.trans PEAM.trans_close.

  Lemma dec_EAM2PEAM : forall {t k1 k2} (c : context k1 k2) {v}, 
                           EAM.dec t c v -> c_eval t c →+ c_apply [.] v.
  Proof with eauto.
    induction 1 using EAM.dec_Ind with
    (P := fun t _ _ c v  (_ : EAM.dec t c v)     => 
              c_eval t c  →+ c_apply [.] v)
    (P0:= fun k2 v k1 c v' (_ : EAM.decctx v c v') => 
              c_apply c v →+ c_apply [.] v' \/ k1 = k2 /\ [.](k1) ~= c /\ v ~=v');

    intuition; dep_subst...
  Qed.


  Lemma eval_EAM2PEAM : forall {t v}, 
                            EAM.eval t v -> PEAM.eval t v.
  Proof with eauto using dec_EAM2PEAM.
    intros t v H.
    dependent destruction H; constructor...
  Qed.


  Local Hint Constructors EAM.dec EAM.decctx.

  Lemma trans_PEAM2EAM : forall {t k1 k2} {c : context k1 k2} {v}, 
                             c_eval t c →+ c_apply [.] v -> EAM.dec t c v.
  Proof with eautof.
    intros t k1 k2 c v; revert t k2 c.

    cut (forall co, co →+ c_apply [.] v -> 
         match co with 
         | c_eval t k1' _ c   => k1 = k1' -> forall v', v ~= v' -> EAM.dec t c v'
         | c_apply k1' _ c v0 => k1 = k1' -> forall v', v ~= v' -> EAM.decctx v0 c v'
         end).
    {
        intros H t k2 c H0; apply (H _ H0)...
    }

    intros co H.

    dependent induction H;
        match goal with H : _ → _ |- _ => 
              dependent_destruction2 H end;
        match goal with 
        | H : dec_term _ ?k = _ |- _=> 
              assert (~ dead_ckind k);
              [ intro; rewrite dec_term_from_dead in H; solve[eauto] 
              | ]
        | H : dec_context _ ?k _ = _ |- _=> 
              assert (~ dead_ckind k);
              [ intro; rewrite dec_context_from_dead in H; 
                solve [eauto using death_propagation] 
              | ]
        end;

    intros; dep_subst...
  Qed.

  
  Lemma eval_PEAM2EAM : forall {t v}, PEAM.eval t v -> EAM.eval t v.

  Proof with eauto using trans_PEAM2EAM.
    intros.
    dependent destruction H; constructor...
  Qed.


  Theorem eval_OK : forall {t v}, RS.eval t v <-> PEAM.eval t v.
  Proof with auto using EAMC.eval_OK, eval_PEAM2EAM, eval_EAM2PEAM.
    etransitivity...
    intuition...
  Qed.

End ProperEAMachine_Correct.




Module PushEnterMachine_Correct (R : RED_LANG) (PERS : PE_RED_REF_SEM R) 
                                (PEM : PUSH_ENTER_MACHINE R PERS).

  Module RS   := PERS.
  Module EAM  := EvalApplyMachine R PERS.
  Module EAMC := EvalApplyMachine_Correct R PERS EAM.
  Import R.
  Import PEM.ST.



  Local Hint Constructors PEM.dec EAM.dec EAM.decctx.

  Lemma dec_EAM2PEM : forall {t k1 k2} {c : context k1 k2} {v}, 
                          EAM.dec t c v -> PEM.dec t c v.
  Proof with eauto.
    induction 1 using EAM.dec_Ind with
    (P := fun t _ _ c v  (_ : EAM.dec t c v) => PEM.dec t c v)
    (P0:= fun _ v _ c v0 (_ : EAM.decctx v c v0) =>
      match c in context _ k2' return value k2' -> Prop with
      | [.] => fun v => PEM.dec v [.] v0
      | ccons ec _ c => fun v => forall d, dec_context ec _ v = d ->
        match d with
        | PEM.ST.in_red r => forall t, contract r = Some t -> PEM.dec t c v0
        | in_term t ec0 => PEM.dec t (ec0=:c) v0
        | in_val v => False
        | in_dead => False
        end
      end v); intros...

    - dependent destruction d; subst...
      + eapply PEM.dec_red...
        eapply (IHdec (in_red _))...
      + contradict (PERS.dec_context_not_val _ _ _ H).
      + eapply PEM.dec_v_t...
        eapply (IHdec (in_term _ _))...

    - constructor; apply PERS.dec_term_value...

    - rewrite e in H0;  inversion H0; subst.
      intros.
      rewrite e0 in H0; inversion H0; subst...

    - contradict (PERS.dec_context_not_val _ _ _ e).

    - rewrite e in H0; subst...
  Qed.


  Lemma dec_PEM2EAM : forall {t k1 k2} {c : context k1 k2} {v}, 
                          PEM.dec t c v -> EAM.dec t c v.
  Proof with eauto.
    induction 1...
    - assert (~ dead_ckind k).
      {
          intro; rewrite dec_term_from_dead in *; autof.
      }
      eauto.
  Qed.



  Lemma eval_EAM2PEM : forall {t v}, EAM.eval t v -> PEM.eval t v.

  Proof with eauto using dec_EAM2PEM.
    intros t v H.
    dependent destruction H; constructor...
  Qed.


  Lemma eval_PEM2EAM : forall {t v}, PEM.eval t v -> EAM.eval t v.

  Proof with eauto using dec_PEM2EAM.
    intros t v H.
    dependent destruction H; constructor...
  Qed.


  Theorem eval_OK : forall {t v}, RS.eval t v <-> PEM.eval t v.
  Proof with eauto using EAMC.eval_OK, eval_PEM2EAM, eval_EAM2PEM.
    etransitivity...
    intuition...
  Qed.

End PushEnterMachine_Correct.




Module ProperPEMachine_Correct (R : RED_LANG) (PRS : PE_RED_REF_SEM R) 
                               (PPEM : PROPER_PE_MACHINE R PRS).

  Module RS   := PRS.
  Module PEM  := PushEnterMachine R PRS.
  Module PEMC := PushEnterMachine_Correct R PRS PEM.
  Import R.
  Import RS.ST.
  Import PPEM.



  Local Hint Constructors PPEM.trans PPEM.trans_close PEM.dec.

  Lemma dec_PEM2PPEM : forall {t} {k1 k2} {c : context k1 k2} {v}, 
                           PEM.dec t c v -> c_eval t c →+ c_fin v.
  Proof with eauto.
    induction 1...
  Qed.


  Lemma eval_PEM2PPEM : forall {t v}, PEM.eval t v -> PPEM.eval t v.

  Proof with eauto using dec_PEM2PPEM.
    intros t v H.
    dependent destruction H; constructor...
  Qed.


  Lemma trans_PPEM2PEM : forall {t k1 k2} {c : context k1 k2} {v}, 
                             c_eval t c →+ c_fin v -> PEM.dec t c v.
  Proof with eauto.
    intros t k1 k2 c v H.
    dependent induction H;
        match goal with H : _ → _ |- _ => 
            dependent_destruction2 H end;
    solve 
    [ eauto 
    | inversion H0 as [? ? H | ? ? ? H ]; inversion H ].
  Qed.


  Lemma eval_PPEM2PEM : forall {t v}, PPEM.eval t v -> PEM.eval t v.

  Proof with eauto using trans_PPEM2PEM.
    intros t v H.
    destruct H; constructor...
  Qed.


  Theorem eval_OK : forall {t v}, RS.eval t v <-> PPEM.eval t v.
  Proof with eauto using PEMC.eval_OK, eval_PEM2PPEM, eval_PPEM2PEM.
    etransitivity...
    intuition...
  Qed.

End ProperPEMachine_Correct.
