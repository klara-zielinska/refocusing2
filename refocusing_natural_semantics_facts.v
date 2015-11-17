Require Import Util.
Require Import Program.
Require Import refocusing_semantics.
Require Import reduction_semantics_facts.
Require Import refocusing_semantics_facts.
Require Import refocusing_natural_semantics.




Module PreRefNaturalSem_Facts (R : RED_LANG) (RS : RED_REF_SEM R)
                                      (PNS : PRE_REF_NATURAL_SEM R RS). 

  Import R.
  Module RF := RED_LANG_Facts R.
  Import RF.


  Theorem dec_preserved : forall {t k1 k2} {c : context k1 k2} {d}, 
                              RS.dec t c d <-> PNS.dec t c d.
  Proof.
    intros t k1 k2 c d; split; intro H.

  (* -> *) {
    induction H using RS.dec_Ind with 
    (P := fun t _ _ c d (_ : RS.dec t c d)    => PNS.dec t c d)
    (P0:= fun _ v _ c d (_ : RS.decctx v c d) => PNS.decctx v c d);
    solve 
    [ econstructor; eauto
    | eapply PNS.d_term; eauto
    | eapply PNS.dc_term; eauto ].
  }

  (* <- *) {
    induction H using PNS.dec_Ind with 
    (P := fun t _ _ c d (_ : PNS.dec t c d)    => RS.dec t c d)
    (P0:= fun _ v _ c d (_ : PNS.decctx v c d) => RS.decctx v c d);
    solve
    [ econstructor; eauto
    | eapply RS.d_term; eauto
    | eapply RS.dc_term; eauto ].
  }
  Qed.



  Theorem decctx_preserved : forall {k1 k2} {v : value k2} {c : context k1 k2} {d}, 
                                 RS.decctx v c d <-> PNS.decctx v c d.
  Proof.
    intros k1 k2 v c d; split; intro H.

  (* -> *) {
    induction H using RS.decctx_Ind with 
    (P  := fun t _ _ c d (_ : RS.dec t c d)    => PNS.dec t c d)
    (P0 := fun _ v _ c d (_ : RS.decctx v c d) => PNS.decctx v c d);
    solve 
    [ econstructor; eauto
    | eapply PNS.d_term; eauto
    | eapply PNS.dc_term; eauto ].
  }

  (* <- *) {
    induction H using PNS.decctx_Ind with 
    (P := fun t _ _ c d (_ : PNS.dec t c d)    => RS.dec t c d)
    (P0:= fun _ v _ c d (_ : PNS.decctx v c d) => RS.decctx v c d);
    solve
    [ econstructor; eauto
    | eapply RS.d_term; eauto
    | eapply RS.dc_term; eauto ].
  }
  Qed.



  Theorem iter_preserved : forall {k} {d : decomp k} {v}, 
                               RS.iter d v <-> PNS.iter d v.
  Proof with eauto.
    intros k d v; split; intro H.

  (* -> *) {
    induction H.
    - constructor...
    - econstructor...
      dependent destruction H0.
      apply dec_preserved.
      apply RS.dec_plug in H0.
      + erewrite (compose_empty _)...
      + eapply (proper_death2 [.])...
  }

  (* <- *) {
    induction H.
    - constructor.
    - econstructor...
      constructor.
      apply RS.dec_plug_rev.
      + eapply (proper_death2 [.])...
      + rewrite <- compose_empty...
        apply dec_preserved...
  }
  Qed.


  Theorem eval_preserved : forall {t v}, RS.eval t v <-> PNS.eval t v.

  Proof with eauto.
    intros t v; split; intro H.

  (* -> *) {
    dependent destruction H; econstructor.
    - dependent destruction H. apply dec_preserved...
    - apply iter_preserved...
  }

  (* <- *) {
    dependent destruction H; econstructor.
    - constructor. eapply dec_preserved...
    - apply iter_preserved...
  }
  Qed.

End PreRefNaturalSem_Facts.




Module StagedRefNaturalSem_Facts (R : RED_LANG) (RS : RED_REF_SEM R)
                                     (SNS : STAGED_REF_NATURAL_SEM R RS).

  Module RF   := RED_LANG_Facts R.
  Module RSF  := RED_SEM_Facts R RS.
  Module RSD  := RedRefSemDet R RS.
  Module PNS  := PreRefNaturalSem R RS.
  Module PNSF := PreRefNaturalSem_Facts R RS PNS.
  Import R.
  Import RF.
  Import RSF.



  Local Hint Constructors PNS.dec PNS.decctx PNS.iter.


  Lemma dec_PNS2SNS : 
      forall {t k1 k2} {c : context k1 k2} {d v},
          PNS.dec t c d -> SNS.iter d v -> SNS.dec t c v.

  Proof.
    induction 1 using PNS.dec_Ind with
    (P  := fun t _ _ c d (_ : PNS.dec t c d)    => 
               forall v,  SNS.iter d v  -> SNS.dec t c v)
    (P0 := fun _ v _ c d (_ : PNS.decctx v c d) => 
               forall v', SNS.iter d v' -> SNS.decctx v c v');
    intros; simpl; solve 
    [ econstructor; eauto
    | eapply SNS.d_v; eauto
    | eapply SNS.d_many; eauto 
    | eapply SNS.dc_val; eauto
    | eapply SNS.dc_term; eauto ].
  Qed.



  Lemma decctx_PNS2SNS : 
      forall {k1 k2} {c : context k1 k2} {d v0 v1},
          PNS.decctx v0 c d -> SNS.iter d v1 -> SNS.decctx v0 c v1.

  Proof.
    induction 1 using PNS.decctx_Ind with
    (P  := fun t _ _ c d (_ : PNS.dec t c d)    => 
               forall v,  SNS.iter d v  -> SNS.dec t c v)
    (P0 := fun _ v _ c d (_ : PNS.decctx v c d) => 
               forall v', SNS.iter d v' -> SNS.decctx v c v');
    intros; simpl; solve 
    [ econstructor; eauto
    | eapply SNS.d_v; eauto
    | eapply SNS.d_many; eauto 
    | eapply SNS.dc_val; eauto
    | eapply SNS.dc_term; eauto ].
  Qed.



  Lemma dec_SNS2PNS : 
      forall {t k1 k2} {c : context k1 k2} {v},
          SNS.dec t c v -> exists d, PNS.dec t c d /\ PNS.iter d v.

  Proof with eauto using proper_death2, (proper_death2 [.]).
    intros k1 k2 v0 c v1 H.

    induction H using SNS.dec_Ind with
    (P  := fun t _ _ c v  (_ : SNS.dec t c v)     => 
               exists d, PNS.dec t c d /\ PNS.iter d v)
    (P0 := fun _ v _ c v' (_ : SNS.decctx v c v') => 
               exists d, PNS.decctx v c d /\ PNS.iter d v')
    (P1 := fun _ d v      (_ : SNS.iter d v)      => 
               PNS.iter d v);

    solve
    [ try destruct IHdec; eexists; intuition eauto
    | try destruct IHdec; intuition eauto ]. 
  Qed.



  Lemma decctx_SNS2PNS : 
      forall {k1 k2} {c : context k1 k2} {v0 v1},
          SNS.decctx v0 c v1 -> exists d, PNS.decctx v0 c d /\ PNS.iter d v1.

  Proof with eauto using proper_death2, (proper_death2 [.]).
    intros k1 k2 v0 c v1 H.

    induction H using SNS.decctx_Ind with
    (P  := fun t _ _ c v  (_ : SNS.dec t c v)     => 
               exists d, PNS.dec t c d /\ PNS.iter d v)
    (P0 := fun _ v _ c v' (_ : SNS.decctx v c v') => 
               exists d, PNS.decctx v c d /\ PNS.iter d v')
    (P1 := fun _ d v      (_ : SNS.iter d v)      => 
               PNS.iter d v);

    solve
    [ try destruct IHdecctx; eexists; intuition eauto
    | try destruct IHdecctx; intuition eauto ]. 
  Qed.



  Lemma iter_PNS_eqv_SNS : 
      forall {k} {d : decomp k} {v}, PNS.iter d v <-> SNS.iter d v.

  Proof with eauto.
    intros k d v; split; intro H.

  (* -> *) {
    induction H; 
    [ constructor 1 | econstructor 2 ];
    eauto using dec_PNS2SNS.
  }

  (* <- *) {
    induction H.
    - constructor 1. 
    - destruct (dec_SNS2PNS H0) as [? [? ?]].
      econstructor 2...
  }
  Qed.



  Lemma dec_iter_PNS_eqv_dec_SNS : 
      forall {t k1 k2} {c : context k1 k2} {v},
          (exists d, PNS.dec t c d /\ PNS.iter d v) <-> SNS.dec t c v.

  Proof with eauto. 
    intros t k1 k2 c v; split; intro H.

  (* -> *) { 
    destruct H as [? [? ?]]; 
    eapply dec_PNS2SNS.
    - eauto.
    - apply iter_PNS_eqv_SNS...
  }
  (* <- *) { 
    intuition eauto using (dec_SNS2PNS H). 
  }
  Qed.



  Lemma decctx_iter_PNS_eqv_decctx_SNS : 
      forall {k1 k2} {c : context k1 k2} {v0 v1},
          (exists d, PNS.decctx v0 c d /\ PNS.iter d v1) <-> SNS.decctx v0 c v1.

  Proof with eauto.
    intros t k1 k2 c v; split; intro H.

  (* -> *) {
    destruct H as [? [? ?]]; 
    eapply decctx_PNS2SNS.
    - eauto.
    - apply iter_PNS_eqv_SNS...
  }
  (* <- *) { 
    intuition eauto using (decctx_SNS2PNS H). 
  }
 Qed. 



  Lemma eval_PNS_eqv_SNS : forall {t v}, PNS.eval t v <-> SNS.eval t v.

  Proof with eauto using dec_PNS2SNS, (proper_death2 [.]), PNSF.dec_preserved.

    intros t v; split; intro H.

  (* -> *) {
    dependent destruction H.
    constructor.
    apply dec_iter_PNS_eqv_dec_SNS...
  }

  (* <- *) {
    dependent destruction H.
    destruct (dec_total t init_ckind) as (d, H0).
    - dependent destruction H...
      + inversion H0; dep_subst...
      + intro G; rewrite SNS.ST.dec_term_from_dead in H...
    - dependent destruction H0.
      destruct (dec_SNS2PNS H) as [? [? ?]].
      econstructor...
  }
  Qed.



  Theorem dec_iter_composition : 
      forall {t k1 k2} {c : context k1 k2} {v},
          (exists d, RS.dec t c d /\ RS.iter d v) <-> SNS.dec t c v.

  Proof with eauto.
    etransitivity.
  Focus 2. 
    eauto using dec_iter_PNS_eqv_dec_SNS.
  Focus 1.
    split; intro H; destruct H as [d [? ?]];
    solve 
    [ 
        exists d; split; 
        [ apply PNSF.dec_preserved | apply PNSF.iter_preserved ]; eauto
    ].
  Qed.



  Theorem decctx_iter_composition : 
      forall {k1 k2} {c : context k1 k2} {v0 v1},
          (exists d, RS.decctx v0 c d /\ RS.iter d v1) <-> SNS.decctx v0 c v1.

  Proof with eauto.
    etransitivity.
  Focus 2. 
    eauto using decctx_iter_PNS_eqv_decctx_SNS.
  Focus 1.
    split; intro H; destruct H as [d [? ?]];
    solve 
    [ 
        exists d; split; 
        [ apply PNSF.decctx_preserved | apply PNSF.iter_preserved ]; eauto
    ].
  Qed.


  Theorem iter_preserved :
      forall {k} {d : decomp k} {v}, RS.iter d v <-> SNS.iter d v.

  Proof.
    etransitivity; eauto using PNSF.iter_preserved, iter_PNS_eqv_SNS.
  Qed.



  Theorem eval_preserved : forall {t v}, RS.eval t v <-> SNS.eval t v.

  Proof. etransitivity; eauto using PNSF.eval_preserved, eval_PNS_eqv_SNS. Qed.

End StagedRefNaturalSem_Facts.




Module RefNaturalSem_Facts (R : RED_LANG) (RS : RED_REF_SEM R)
                                             (RNS : REF_NATURAL_SEM R RS).

  Module SNS  := StagedRefNaturalSem R RS.
  Module SNSF := StagedRefNaturalSem_Facts R RS SNS.
  Import R.



  Local Hint Constructors RNS.dec RNS.decctx RNS.eval.
  Local Hint Constructors SNS.dec SNS.decctx SNS.iter SNS.eval.


  Lemma dec_SNS_eqv_RNS : forall {t k1 k2} {c : context k1 k2} {v}, 
                              SNS.dec t c v <-> RNS.dec t c v.

  Proof with eauto.
    intros t k1 k2 c v; split; intro H.

  (* -> *) {
    induction H using SNS.dec_Ind with
    (P := fun t _ _ c v  (_ : SNS.dec t c v)     => RNS.dec t c v)
    (P0:= fun _ v _ c v' (_ : SNS.decctx v c v') => RNS.decctx v c v')
    (P1:= fun k d v      (_ : SNS.iter d v)      => 
              match d with
              | d_val v'    => ~ dead_ckind k -> RNS.decctx v [.] v'
              | d_red _ r c => forall t, contract r = Some t -> RNS.dec t c v
              end);
        intros;

    match goal with 

    | _ => solve [eauto]

    | H : SNS.iter _ _ |- _ => 
          inversion H; dep_subst; 
          solve [eauto] 

    | H0 : contract ?r = ?t0 , H1 : contract ?r = ?t1 |- _ =>
          rewrite H0 in H1; 
          inversion H1; subst; 
          solve [eauto]
    end.
  }

  (* <- *) {
    induction H using RNS.dec_Ind with
    (P := fun t _ _ c v  (_ : RNS.dec t c v)     => SNS.dec t c v)
    (P0:= fun _ v _ c v' (_ : RNS.decctx v c v') => SNS.decctx v c v')
    ...
  }
  Qed.



  Lemma decctx_SNS_eqv_RNS : forall {k1 k2} {c : context k1 k2} {v0 v1}, 
                                 SNS.decctx v0 c v1 <-> RNS.decctx v0 c v1.

  Proof with eauto.
    intros k1 k2 v0 c v1; split; intro H.

  (* -> *) {
    induction H using SNS.decctx_Ind with
    (P := fun t _ _ c v  (_ : SNS.dec t c v)     => RNS.dec t c v)
    (P0:= fun _ v _ c v' (_ : SNS.decctx v c v') => RNS.decctx v c v')
    (P1:= fun k d v      (_ : SNS.iter d v)      => 
              match d with
              | d_val v'    => ~ dead_ckind k -> RNS.decctx v [.] v'
              | d_red _ r c => forall t, contract r = Some t -> RNS.dec t c v
              end);
        intros;

    match goal with 

    | _ => solve [eauto]

    | H : SNS.iter _ _ |- _ => 
          inversion H; dep_subst; 
          solve [eauto] 

    | H0 : contract ?r = ?t0 , H1 : contract ?r = ?t1 |- _ =>
          rewrite H0 in H1; 
          inversion H1; subst; 
          solve [eauto]
    end.
  }

  (* <- *) {
    induction H using RNS.decctx_Ind with
    (P := fun t _ _ c v  (_ : RNS.dec t c v)     => SNS.dec t c v)
    (P0:= fun _ v _ c v' (_ : RNS.decctx v c v') => SNS.decctx v c v')
    ...
  }
  Qed.



  Lemma eval_SNS_eqv_RNS : forall {t v}, SNS.eval t v <-> RNS.eval t v.

  Proof.
    intros t v; split; intro H;

    solve 
    [ dependent destruction H; 
      constructor; apply dec_SNS_eqv_RNS; eauto ].
  Qed.



  Theorem dec_iter_composition :
      forall {t k1 k2} {c : context k1 k2} {v},
          (exists d, RS.dec t c d /\ RS.iter d v) <-> RNS.dec t c v.

  Proof.
    etransitivity; eauto using dec_SNS_eqv_RNS, SNSF.dec_iter_composition.
  Qed.



  Theorem decctx_iter_composition :
      forall {k1 k2} {c : context k1 k2} {v0 v1},
          (exists d, RS.decctx v0 c d /\ RS.iter d v1) <-> RNS.decctx v0 c v1.

  Proof.
    etransitivity; eauto using decctx_SNS_eqv_RNS, SNSF.decctx_iter_composition.
  Qed.



  Theorem eval_preserved : forall {t v}, RS.eval t v <-> RNS.eval t v.

  Proof.
    etransitivity; eauto using SNSF.eval_preserved, eval_SNS_eqv_RNS.
  Qed.

End RefNaturalSem_Facts.




Module PE_RefNaturalSem_Facts (R : RED_LANG) (PERS : PE_RED_REF_SEM R) 
                                           (PENS : PE_REF_NATURAL_SEM R PERS).

  Module RNS  := RefNaturalSem R PERS.
  Module RNSF := RefNaturalSem_Facts R PERS RNS.
  Import R PERS.ST.



  Local Hint Constructors PENS.dec RNS.dec RNS.decctx.


  Lemma dec_RNS_eqv_PENS : forall {t k1 k2} {c : context k1 k2} {v},
                               RNS.dec t c v <-> PENS.dec t c v.

  Proof with eauto.
    intros t k1 k2 c v; split; intro H.

  (* -> *) {
    induction H using RNS.dec_Ind with
    (P := fun t _ _ c v  (_ : RNS.dec t c v) => PENS.dec t c v)
    (P0:= fun _ v _ c v0 (_ : RNS.decctx v c v0) =>
      match c in context _ k2' return value k2' -> Prop with
      | [.] => fun v => PENS.dec v [.] v0
      | ccons ec _ c => fun v => forall d, dec_context ec _ v = d ->
        match d with
        | PENS.ST.in_red r => forall t, contract r = Some t -> PENS.dec t c v0
        | in_term t ec0 => PENS.dec t (ec0=:c) v0
        | in_val v => False
        | in_dead => False
        end
      end v); intros...

    - dependent destruction d; subst...
      + eapply PENS.dec_red...
        eapply (IHdec (in_red _))...
      + contradict (PERS.dec_context_not_val _ _ _ H).
      + eapply PENS.dec_v_t...
        eapply (IHdec (in_term _ _))...

    - constructor...
      apply PERS.dec_term_value...

    - rewrite e in H0;  inversion H0; subst.
      intros.
      rewrite e0 in H0; inversion H0; subst...

    - contradict (PERS.dec_context_not_val _ _ _ e).

    - rewrite e in H0; subst...
  }

  (* <- *) {
    induction H...
  }
  Qed.



  Lemma decctx_RNS_eqv_dec_PENS : forall {k1 k2} {c : context k1 k2} {v0 v1}, 
                                      RNS.decctx v0 c v1 <-> PENS.dec v0 c v1.

  Proof with eauto.
    intros k1 k2 c v0 v1; split; intro H.

  (* -> *) {
    induction H; dep_subst.
    - auto using PERS.dec_term_value.
    - econstructor 4; eauto using PERS.dec_term_value, dec_RNS_eqv_PENS.
      apply dec_RNS_eqv_PENS...
    - exfalso; eapply PENS.dec_context_not_val...
    - econstructor 3; eauto using PERS.dec_term_value.
      apply dec_RNS_eqv_PENS...
  }

  (* <- *) {
    assert (H0 := PERS.dec_term_value v0).
    inversion H; dep_subst;
        match goal with
        | H0 : dec_term ?v ?k = _ , H1 : dec_term ?v ?k = _ |- _ =>
            rewrite H0 in H1; inversion H1; subst
        end.
    - eauto.
    - econstructor 4...
      apply dec_RNS_eqv_PENS...
    - econstructor 2...
      apply dec_RNS_eqv_PENS...
  }
  Qed.



  Lemma eval_RNS_eqv_PENS : forall {t v}, RNS.eval t v <-> PENS.eval t v.

  Proof.
    intros t v; split; intro H;
    solve
    [ dependent destruction H; constructor; apply dec_RNS_eqv_PENS; eauto ].
  Qed.



  Theorem dec_iter_composition : 
      forall {t k1 k2} {c : context k1 k2} {v},
          (exists d, PERS.dec t c d /\ PERS.iter d v) <-> PENS.dec t c v.

  Proof.
    etransitivity; eauto using dec_RNS_eqv_PENS, RNSF.dec_iter_composition.
  Qed.



  Theorem decctx_iter_composition :
      forall {k1 k2} {c : context k1 k2} {v0 v1},
          (exists d, PERS.decctx v0 c d /\ PERS.iter d v1) <-> PENS.dec v0 c v1.

  Proof.
    etransitivity; eauto using decctx_RNS_eqv_dec_PENS, RNSF.decctx_iter_composition.
  Qed.



  Theorem eval_preserved : forall {t v}, PERS.eval t v <-> PENS.eval t v.

  Proof. etransitivity; eauto using RNSF.eval_preserved, eval_RNS_eqv_PENS. Qed.

End PE_RefNaturalSem_Facts.

