Require Import Util.
Require Import Program.
Require Import refocusing_semantics.
Require Import refocusing_natural_semantics.
Require Import refocusing_machine.
Require Import reduction_semantics_facts.
Require Import refocusing_semantics_facts.
Require Import refocusing_natural_semantics_facts.




Module RefEvalApplyMachine_Facts (R : RED_LANG) (RS : RED_REF_SEM R) 
                                        (EAM : REF_EVAL_APPLY_MACHINE R RS).

  Module RNS  := RefNaturalSem R RS.
  Module RNSF := RefNaturalSem_Facts R RS RNS.
  Import R.
  Import RS.ST.
  Import EAM.


  Local Hint Constructors EAM.trans EAM.trans_close.
  Local Hint Constructors RNS.dec RNS.decctx.


  Lemma dec_RNS_eqv_EAM : forall {t k1 k2} (c : context k1 k2) {v}, 
                              RNS.dec t c v <-> c_eval t c →+ c_apply [.] v.
  Proof with eauto.
    intros t k1 k2 c v; split; intro H.

  (* -> *) {
    induction H using RNS.dec_Ind with
    (P := fun t _ _ c v  (_ : RNS.dec t c v) => 
              c_eval t c  →+ c_apply [.] v)
    (P0:= fun k2 v k1 c v' (_ : RNS.decctx v c v') => 
              c_apply c v →+ c_apply [.] v' \/ k1 = k2 /\ [.](k1) ~= c /\ v ~=v');

    intuition; dep_subst...
  }

  (* <- *) {
    revert t k2 c H.

    cut (forall st, st →+ c_apply [.] v -> 
         match st with 
         | c_eval t k1' _ c   => k1 = k1' -> forall v', v ~= v' -> RNS.dec t c v'
         | c_apply k1' _ c v0 => k1 = k1' -> forall v', v ~= v' -> RNS.decctx v0 c v'
         end).
    { intros H t k2 c H0; apply (H _ H0)... }

    intros st H.

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
  }
  Qed.



  Lemma decctx_RNS_eqv_EAM : 
      forall {k1 k2} (c : context k1 k2) {v0 v1}, 
          RNS.decctx v0 c v1 <-> c_apply c v0 →+ c_apply [.] v1 \/
                                 c_apply c v0 = c_apply [.] v1 /\ ~dead_ckind k1.

  Proof with eauto.
    intros k1 k2 c v0 v1; split; intro H.

  (* -> *) {
    induction H using RNS.decctx_Ind with
    (P := fun t _ _ c v  (_ : RNS.dec t c v)     => 
              c_eval t c  →+ c_apply [.] v)
    (P0:= fun k2 v k1 c v' (_ : RNS.decctx v c v') => 
              c_apply c v →+ c_apply [.] v' \/ 
              c_apply c v = c_apply [.] v' /\ ~dead_ckind k1);

    solve
    [ intuition; dep_subst; eauto
    | destruct IHdecctx as [H0 | [H0 H1]]; inversion H0; dep_subst; eauto ].

  }

  (* <- *) {
    revert k2 v0 c H.

    cut (forall st, st →+ c_apply [.] v1 -> 
         match st with 
         | c_eval t k1' _ c   => k1 = k1' -> forall v', v1 ~= v' -> RNS.dec t c v'
         | c_apply k1' _ c v0 => k1 = k1' -> forall v', v1 ~= v' -> RNS.decctx v0 c v'
         end).
    { intros H t k2 c H0.
      destruct H0 as [H0 | [H0 H1]]. 
      - apply (H _ H0)...
      - inversion H0; dep_subst... }

    intros st H.
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
  }
  Qed.



  Lemma eval_RNS_eqv_EAM : forall {t v}, RNS.eval t v <-> EAM.eval t v.
  Proof.
    intros t v; split; intro H;
    solve 
    [ dependent destruction H; constructor; apply dec_RNS_eqv_EAM; eauto ].
  Qed.



  Theorem dec_iter_composition :
      forall {t k1 k2} {c : context k1 k2} {v},
          (exists d, RS.dec t c d /\ RS.iter d v) <-> c_eval t c →+ c_apply [.] v.

  Proof.
    etransitivity; eauto using dec_RNS_eqv_EAM, RNSF.dec_iter_composition.
  Qed.



  Theorem decctx_iter_composition : forall {k1 k2} {c : context k1 k2} {v0 v1},

          (exists d, RS.decctx v0 c d /\ RS.iter d v1) <-> 

          c_apply c v0 →+ c_apply [.] v1 \/
          c_apply c v0 = c_apply [.] v1 /\ ~dead_ckind k1.

  Proof.
    etransitivity; eauto using decctx_RNS_eqv_EAM, RNSF.decctx_iter_composition.
  Qed.



  Theorem eval_preservation : forall {t v}, RS.eval t v <-> EAM.eval t v.

  Proof. etransitivity; eauto using RNSF.eval_preserved, eval_RNS_eqv_EAM. Qed.

End RefEvalApplyMachine_Facts.




Module PushEnterMachine_Facts (R : RED_LANG) (PERS : PE_RED_REF_SEM R) 
                                        (PEM : REF_PUSH_ENTER_MACHINE R PERS).

  Module PENS  := PE_RefNaturalSem R PERS.
  Module PENSF := PE_RefNaturalSem_Facts R PERS PENS.
  Import R PERS.ST.
  Import PEM.



  Local Hint Constructors PEM.trans PEM.trans_close PENS.dec.


  Lemma dec_PENS_eqv_PEM : forall {t} {k1 k2} {c : context k1 k2} {v}, 
                           PENS.dec t c v <-> c_eval t c →+ c_fin v.
  Proof with eauto.
    intros t k1 k2 v; split; intro H.

  (* -> *) {
    induction H...
  }

  (* <- *) {
    dependent induction H;
        match goal with H : _ → _ |- _ => 
            dependent_destruction2 H end;
    solve 
    [ eauto
    | inversion H0 as [? ? H | ? ? ? H ]; inversion H
    | constructor; auto;
      intro H; 
      assert (H0 := dec_term_from_dead t _ H); rewrite H0 in *; 
      discriminate ].
  }
  Qed.


  Lemma eval_PENS_eqv_PEM : forall {t v}, PENS.eval t v <-> PEM.eval t v.
  Proof.
    intros t v; split; intro H;
    solve
    [ dependent destruction H; constructor; apply dec_PENS_eqv_PEM; eauto ].
  Qed.


  Theorem dec_iter_composition :
      forall {t k1 k2} {c : context k1 k2} {v},
          (exists d, PERS.dec t c d /\ PERS.iter d v) <-> c_eval t c →+ c_fin v.
  Proof.
    etransitivity; eauto using PENSF.dec_iter_composition, dec_PENS_eqv_PEM.
  Qed.


  Theorem eval_preserved : forall {t v}, PERS.eval t v <-> PEM.eval t v.

  Proof. etransitivity; eauto using PENSF.eval_preserved, eval_PENS_eqv_PEM. Qed.

End PushEnterMachine_Facts.
