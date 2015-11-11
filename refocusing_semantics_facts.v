Require Import Util.
Require Import Program.
Require Import refocusing_semantics.
Require Import reduction_semantics_facts.




(* Refocusing semantics is deterministic. *)

Module RedRefSemDet (R : RED_LANG) (RS : RED_REF_SEM R) : DET_RED_SEM R 
                                                            with Module RS := RS.RS.

  Import R.
  Module RLF := RED_LANG_Facts R.
  Import RLF.
  Export RS.


  Lemma dec_is_function : forall {t k} {d0 d1 : decomp k}, 
                              decempty t d0 -> decempty t d1 -> d0 = d1.
  Proof.
    intros t k d0 d1 DE0 DE1.
    dependent destruction DE0; dependent destruction DE1.

    induction H using dec_Ind with 
    (P  := fun t _ _ c d _ => forall d1, dec t c d1    -> d = d1)
    (P0 := fun _ v _ c d _ => forall d1, decctx v c d1 -> d = d1);

    intros;

    (* automated cases *)
    match goal with

    | [ RD : (dec ?t ?c ?d), DT1 : (dec_term ?t ?k = _) |- _ ] => 
             inversion RD; dep_subst; 
             match goal with DT2 : (dec_term ?t ?k = _) |- _ => 
                 rewrite DT2 in DT1; inversion DT1 end

    | [ RC : (decctx ?v (?ec=:?c) ?d), DC1 : (dec_context ?ec ?k ?v = _) |- _ ] => 
             dependent_destruction2 RC; inversion_ccons x2; dep_subst;
             match goal with DC2 : (dec_context ?ec' ?k' ?v' = _) |- _ => 
                 rewrite DC2 in DC1; inversion DC1 end

    | [ RC : (decctx ?v [.] ?d) |- _] => 
             dependent_destruction2 RC

    end;

    subst; eauto.
  Qed.


  Lemma iter_is_function : forall {k} {d : decomp k} {v0 v1}, 
                               iter d v0 -> iter d v1 -> v0 = v1.
  Proof with eauto.
    intros k d v0 v1.
    induction 1; intro H2.
    - dependent destruction H2...
    - dependent destruction H2; subst. 
      rewrite H2 in H; inversion H; subst.
      apply IHiter.
      erewrite (dec_is_function)...
  Qed.


  Lemma eval_is_function : forall {t} {v0 v1 : value init_ckind}, 
                               eval t v0 -> eval t v1 -> v0 = v1.
  Proof with eauto.
    intros t v0 v1 H H0.
    dependent destruction H.
    dependent destruction H1.
    eapply iter_is_function.
    - apply H0.
    - erewrite dec_is_function...
  Qed.


  Module RS := RS.RS.

End RedRefSemDet.