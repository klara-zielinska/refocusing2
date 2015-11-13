Require Import Util.
Require Import Program.
Require Import Eqdep.
Require Export reduction_semantics.




Module Type PRE_RED_LANG.

  Parameters term elem_context ckind : Set. 
  Parameter  ckind_trans : ckind -> elem_context -> ckind.
  Infix "+>" := ckind_trans (at level 50, left associativity).
  Parameter dead_ckind : ckind -> Prop.


  Inductive context (k1 : ckind) : ckind -> Set :=
  | empty : context k1 k1
  | ccons : forall (ec : elem_context) {k2}, context k1 k2 -> context k1 (k2+>ec).
  Arguments empty {k1}. Arguments ccons {k1} _ {k2} _.

  Notation "[.]"      := empty.
  Notation "[.]( k )" := (@empty k).
  Infix    "=:"       := ccons (at level 60, right associativity).


  Parameter elem_plug : term -> elem_context -> term.
  Notation "ec :[ t ]" := (elem_plug t ec) (at level 0).

(*  

  Axiom elem_plug_injective1 : forall ec {t0 t1}, ec:[t0] = ec:[t1] -> t0 = t1.*)

  Definition immediate_ec ec t := exists t', ec:[t'] = t.

  Parameters value redex : ckind -> Set.

  Parameter value_to_term : forall {k}, value k -> term.
  Coercion  value_to_term : value >-> term.
  Parameter redex_to_term : forall {k}, redex k -> term.
  Coercion  redex_to_term : redex >-> term.

(*
  Axiom value_to_term_injective : 
      forall {k} (v v' : value k), value_to_term v = value_to_term v' -> v = v'.
  Axiom redex_to_term_injective : 
      forall {k} (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.*)

End PRE_RED_LANG.




Module RED_LANG_Facts (R : PRE_RED_LANG).

  Import R.
  

  Fixpoint plug (t : term) {k1 k2} (c : context k1 k2) : term :=
      match c with
      | [.]    => t 
      | ec=:c' => plug ec:[t] c'
      end.
  Notation "c [ t ]" := (plug t c) (at level 0).


  Fixpoint compose {k1 k2} (c0 : context k1 k2) 
                      {k3} (c1 : context k3 k1) : context k3 k2 := 
      match c0 in context _ k2' return context k3 k2' with
      | [.]     => c1
      | ec=:c0' => ec =: compose c0' c1
      end.
  Infix "~+" := compose (at level 60, right associativity).


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


  Ltac inversion_ccons H :=

      match type of H with ?ec1 =: ?c1  ~=  ?ec2 =: ?c2 => 

      let H0 := fresh in 
      assert (H0 : eq_dep _ _ _ (ec1=:c1) _ (ec2=:c2));

      [ apply JMeq_eq_depT; eauto

      | inversion H0; dep_subst; clear H0 ]

      end.


  Lemma plug_empty : forall t k, [.](k)[t] = t.
  Proof. intuition. Qed.


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
    - auto.
    - apply IHc0.
  Qed.


  Lemma context_cons_snoc : forall ec0 {k1 k2} (c0 : context k1 k2),
                                exists ec1 c1, (ec0=:c0) = (c1~+ec1=:[.]).
  Proof.
    intros; revert ec0.
    induction c0; intros.
    - exists ec0; eexists [.]; trivial.
    - destruct IHc0 with ec as (ec1, (c1, IH)).
      exists ec1; eexists (ec0=:c1); rewrite IH; trivial.
  Qed.



  Section Death.

  Axiom death_propagation : 
      forall k, dead_ckind k -> forall ec, dead_ckind (k+>ec).
  Axiom proper_death : 
      forall k, dead_ckind k -> ~ exists (r : redex k), True.


  Lemma death_propagation2 : 
      forall k ec, ~ dead_ckind (k+>ec) -> ~ dead_ckind k.

  Proof.
    intuition.
    apply H.
    apply death_propagation.
    assumption.
  Qed.


  Lemma dead_context_dead : 
      forall {k1 k2}, context k1 k2 -> dead_ckind k1 -> dead_ckind k2.

  Proof with auto.
    intros ? ? c H; revert c.
    induction 1.
    - trivial.
    - apply death_propagation...
  Qed.


  Lemma proper_death_trans :
      forall k1, dead_ckind k1 ->
          ~ exists {k2} (c : context k1 k2) (r : redex k2), True.

  Proof with auto.
    intros k1 H [k2 [c [ r _]]].
    eapply proper_death.
    - apply (dead_context_dead c)...
    - eauto.
  Qed.


  Lemma proper_death2 : 
      forall {k1 k2}, context k1 k2 -> redex k2 -> ~ dead_ckind k1.

  Proof with eauto.
    intros k1 k2 c r H.
    apply (proper_death_trans k1)...
  Qed.

  End Death.



  Section Values.

  Axiom value_trivial1 : forall {k} (v : value k) ec {t}, 
                             ~dead_ckind (k+>ec) -> ec:[t] = v -> 
                                 exists (v' : value (k+>ec)), t = v'.

  Definition only_trivial t k :=
      forall t' {k'} (c : context k k'), c[t'] = t -> ~ dead_ckind k' -> 
          k = k' /\ c ~= [.](k) \/ exists (v : value k'), t' = v.

  Lemma value_trivial : forall {k} (v : value k), only_trivial v k.

  Proof.
    intros k1 v (*&*) t k2 c; revert t.
    induction c;
        intros t H H0.
    - auto.
    - right.
      destruct (IHc ec:[t]) as [H1 | [v' H1]]; 
      solve 
      [ eauto using death_propagation2 
      | try rec_subst H1; eauto using value_trivial1, death_propagation2 ].
  Qed.

  End Values.

End RED_LANG_Facts.




Module RED_SEM_Facts (R : RED_LANG) (RS : RED_SEM R).

  Module RF := RED_LANG_Facts R.
  Import R.
  Import RS.
  Import RF.



  Lemma dec_total : forall t k, ~ dead_ckind k -> 
                        exists (d : decomp k), decempty t d.
  Proof with eauto.
    intros t k H.
    destruct (decompose t k H) as [(v, H0) | (k', (r, (c, H0)))];
        subst t.
    - exists (d_val v). 
      constructor.
      apply dec_value_self...
    - exists (d_red r c).
      constructor.
      apply dec_plug_rev.
      + eapply (proper_death2 [.] r).
      + rewrite <- compose_empty.
        apply dec_redex_self.
  Qed.

End RED_SEM_Facts.



(* Facts about a deterministic red. semantics.

  Lemma unique_decomposition :

      forall (t : term) k1, ~ dead_ckind k1 ->  

         (exists v : value k1, t = v) \/

         (exists k2 (r : redex k2) (c : context k1 k2), t = c[r] /\ 
	      forall k2' (r' : redex k2') (c' : context k1 k2'), ~ dead_ckind k2' -> 
                  t = c'[r'] -> k2' = k2 /\ r ~= r' /\ c ~= c').

  Proof.
    intros t k1 H.
    destruct (dec_total t k1 H) as (d, H0); destruct H0.
    destruct d.
    - right.
      exists k' r c.
      split. apply (dec_correct H0).
      intros k2' r' c' H1 H2.
      assert (d_red r c = d_red r' c').
      eapply dec_is_function. constructor.
    apply H0.
    subst.
    apply dec_plug_rev. auto.
    rewrite <- compose_empty.
    apply dec_redex_self.
    inversion H3; dep_subst.
    auto.
    - left. exists v. apply (dec_correct H0).
  Qed. *)

