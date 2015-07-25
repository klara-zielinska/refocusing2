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
    assert (H7' := inj_pair2 _ _ _ _ _ H7); subst; clear H7.
    assert (H7'' := inj_pair2 _ _ _ _ _ H7'); subst; clear H7'.
    auto.
  Qed.


  Lemma context_tail_liveness : 
      forall k ec, ~ dead_ckind (k+>ec) -> ~ dead_ckind k.
  Proof.
    intuition.
    apply H.
    apply ckind_death_propagation.
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

      | inversion H0; subst; 
        match goal with H1 : existT _ _ _ = existT _ _ _ |- _ => 
        let tmp := fresh in 
        assert (tmp := H1); clear H1;
        dependent destruction tmp
        end;
        clear H0 ]

      end.


  Lemma plug_empty : forall t k, plug t (@empty k) = t.
  Proof.
    intuition.
  Qed.


  Lemma compose_empty : forall {k1 k2} (c : context k1 k2), c = c ~+ [_].
  Proof.
    induction c.
    - trivial.
    - simpl; rewrite <- IHc; trivial.
  Qed.


  Lemma plug_compose  : 
      forall {k1 k2 k3} (c0 : context k1 k2) (c1 : context k3 k1) t, 
          plug t (c0 ~+ c1) = plug (plug t c0) c1.
  Proof.
    induction c0; intros.
    - trivial.
    - simpl; rewrite IHc0; trivial.
  Qed.


  Lemma context_snoc : forall ec0 {k1 k2} (c0 : context k1 k2),
                           exists ec1 c1, (ec0=:c0) = (c1~+ec1=:[_]).
  Proof.
    intros; revert ec0.
    induction c0; intros.
    - exists ec0; eexists [_]; trivial.
    - destruct IHc0 with ec as (ec1, (c1, IH)).
      exists ec1; eexists (ec0=:c1); rewrite IH; trivial.
  Qed.


  Lemma dead_contex_dead : 
      forall {k1 k2}, context k1 k2 -> dead_ckind k1 -> dead_ckind k2.
  Proof with auto.
    intros ? ? c H; revert c.
    induction 1.
    - trivial.
    - apply ckind_death_propagation...
  Qed.

End RED_LANG_Facts.


Module RED_REF_LANG_Facts (R : RED_REF_LANG).

  Import R.R.
  Import R.

  Lemma elem_context_det2 : 
      forall t k ec0 ec1,  k, t |~ ec0 << ec1 -> 
          forall t1,  atom_plug t1 ec1 = t ->
              exists (v : value (k+>ec1)), t1 = v.
  Proof with eauto.
    intros.    
    destruct (elem_context_det _ _ _ _ H).
    exists x.
    eapply atom_plug_injective1.
    etransitivity...
  Qed.

End RED_REF_LANG_Facts.