Require Export refocusing_lang.
Require Import Program.
Require Import Eqdep.


Module RED_LANG_Facts (R : RED_LANG).

  Import R.
  
  Lemma ccons_inj : 
      forall ec {k1 k2} (c : context k1 k2) ec' {k2'} (c' : context k1 k2'), 
          k2 +> ec = k2' +> ec' -> ec=:c ~= ec'=:c' ->
          ec = ec' /\ k2 = k2' /\ c ~= c'.
  Proof.
    intros.
    assert (H1 := JMeq_eq_depT _ _ _ _ _ _ H H0).
    assert (H2 := eq_dep_eq_sigT _ _ _ _ _ _ H1). 
    inversion H2; subst.
    dep_subst.
    auto.
  Qed.


  Lemma death_propagation2 : 
      forall k ec, ~ dead_ckind (k+>ec) -> ~ dead_ckind k.
  Proof.
    intuition.
    apply H.
    apply death_propagation.
    assumption.
  Qed.


  Lemma proper_death2 : forall k1 k2, context k1 k2 -> redex k2 -> ~ dead_ckind k1.
  Proof.
    intuition.
    eapply proper_death;
    eauto.
  Qed.


  Ltac inversion_ccons H :=

      match type of H with ?ec1 =: ?c1  ~=  ?ec2 =: ?c2 => 

      let H0 := fresh in 
      assert (H0 : eq_dep _ _ _ (ec1=:c1) _ (ec2=:c2));

      [ apply JMeq_eq_depT; eauto

      | inversion H0; dep_subst; clear H0 (*; 
        match goal with H1 : existT _ _ _ = existT _ _ _ |- _ => 
        let tmp := fresh in 
        assert (tmp := H1); clear H1;
        dependent destruction tmp
        end;
        clear H0*) ]

      end.


  Lemma plug_empty : forall t k, [.](k)[t] = t.
  Proof.
    intuition.
  Qed.


  Lemma compose_empty : forall {k1 k2} (c : context k1 k2), c = c ~+ [.].
  Proof.
    induction c.
    - trivial.
    - simpl; rewrite <- IHc; trivial.
  Qed.


  Lemma plug_compose  : 
      forall {k1 k2 k3} (c0 : context k1 k2) (c1 : context k3 k1) t, 
          (c0 ~+ c1)[t] = c1[c0[t]].
  Proof.
    induction c0; intros.
    - trivial.
    - simpl; rewrite IHc0; trivial.
  Qed.


  Lemma context_snoc : forall ec0 {k1 k2} (c0 : context k1 k2),
                           exists ec1 c1, (ec0=:c0) = (c1~+ec1=:[.]).
  Proof.
    intros; revert ec0.
    induction c0; intros.
    - exists ec0; eexists [.]; trivial.
    - destruct IHc0 with ec as (ec1, (c1, IH)).
      exists ec1; eexists (ec0=:c1); rewrite IH; trivial.
  Qed.


  Lemma dead_contex_dead : 
      forall {k1 k2}, context k1 k2 -> dead_ckind k1 -> dead_ckind k2.
  Proof with auto.
    intros ? ? c H; revert c.
    induction 1.
    - trivial.
    - apply death_propagation...
  Qed.

End RED_LANG_Facts.
