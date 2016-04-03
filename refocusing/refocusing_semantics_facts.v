Require Import Util.
Require Import Program.
Require Import rewriting_system refocusing_semantics.
Require Import reduction_languages_facts.




Module RED_REF_SEM_Facts (R : RED_REF_SEM).

  Module RF := RED_LANG_Facts R.
  Import R RF.


  Lemma refocus_in_starts_alive :                 forall t {k1 k2} (c : context k1 k2) d,
      refocus_in t c d -> ~dead_ckind k2.

  Proof.
    intros t k1 k2 c d H H0.
    apply dec_term_from_dead with t k2 in H0.
    assert (G := dec_term_correct t k2).
    destruct H;
    match goal with H : dec_term ?t ?k = _ |- _ =>
    rewrite H in G
    end;
    solve [congruence].
  Qed.


  Lemma refocus_out_starts_alive :                        forall {k2} (v : value k2) {k1}
                                                                   (c : context k1 k2) d,
     refocus_out v c d -> ~dead_ckind k2.

  Proof with auto.
    intros k2 v k1 c d H H0.
    destruct c as [| ec k2 c].
    - inversion H; dep_subst...
    - apply dec_context_from_dead with ec k2 v in H0.
      assert (G := dec_context_correct ec k2 v).
      dependent destruction H; inversion_ccons x; dep_subst; (* WARRNING: unbound x *)
      match goal with H : dec_context ?ec ?k ?v = _ |- _ =>
      rewrite H in G
      end;
      solve [congruence].
  Qed.


  Lemma refocus_in_is_pfunction :             forall t {k1 k2} (c : context k1 k2) d0 d1,
      refocus_in t c d0 -> refocus_in t c d1 -> d0 = d1.

  Proof.
    intros t k1 k2 c d0 d1 DE0 DE1. revert d1 DE1.

    induction DE0 using refocus_in_Ind with 
    (P  := fun _ t c d _ => forall d1, refocus_in  t c d1    -> d = d1)
    (P0 := fun _ v c d _ => forall d1, refocus_out v c d1 -> d = d1);

    intros;

    (* automated cases *)
    match goal with

    | [ RD : (refocus_in ?t ?c ?d), DT1 : (dec_term ?t ?k = _) |- _ ] => 
             inversion RD; dep_subst; 
             match goal with DT2 : (dec_term ?t ?k = _) |- _ => 
                 rewrite DT2 in DT1; inversion DT1 end

    | [ RC : (refocus_out ?v (?ec=:?c) ?d), DC1 : (dec_context ?ec ?k ?v = _) |- _ ] => 
             dependent_destruction2 RC; inversion_ccons x2; dep_subst;
             match goal with DC2 : (dec_context ?ec' ?k' ?v' = _) |- _ => 
                 rewrite DC2 in DC1; inversion DC1 end

    | [ RC : (refocus_out ?v [.] ?d) |- _] => 
             dependent_destruction2 RC

    end;

    subst; eauto.
  Qed.



  Lemma dec_is_det :                                   forall t {k} (d0 d1 : decomp k),
      dec t k d0 -> dec t k d1 -> d0 = d1.

  Proof with auto.
    intros t k d0 d1 H H0.
    assert (~dead_ckind k) by apply H.
    rewrite <- (plug_empty t k) in H, H0.
    apply refocus_in_eqv_dec in H...
    apply refocus_in_eqv_dec in H0...
    eauto 10 using refocus_in_is_pfunction.
  Qed.


End RED_REF_SEM_Facts.