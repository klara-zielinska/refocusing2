Require Import Util.
Require Import Program.
Require Import Eqdep.




Module Type RED_MINI_LANG.

  Parameters
  (term         : Set)
  (elem_context : Set)
  (ckind        : Set)
  (dead_ckind   : ckind -> Prop)
  (ckind_trans  : ckind -> elem_context -> ckind)
  (elem_plug    : term -> elem_context -> term)

  (value : ckind -> Set)
  (redex : ckind -> Set)
  (value_to_term : forall {k}, value k -> term)
  (redex_to_term : forall {k}, redex k -> term).

  Infix "+>"           := ckind_trans (at level 50, left associativity).
  Notation "ec :[ t ]" := (elem_plug t ec) (at level 0).
  Coercion  value_to_term : value >-> term.
  Coercion  redex_to_term : redex >-> term.



  Inductive context (k1 : ckind) : ckind -> Set :=
  | empty : context k1 k1
  | ccons : forall (ec : elem_context) {k2}, context k1 k2 -> context k1 (k2+>ec).
  Arguments empty {k1}. Arguments ccons {k1} _ {k2} _.

  Notation "[.]"      := empty.
  Notation "[.]( k )" := (@empty k).
  Infix    "=:"       := ccons (at level 60, right associativity).

  Fixpoint compose {k1 k2} (c0 : context k1 k2) 
                      {k3} (c1 : context k3 k1) : context k3 k2 := 
      match c0 in context _ k2' return context k3 k2' with
      | [.]     => c1
      | ec=:c0' => ec =: compose c0' c1
      end.
  Infix "~+" := compose (at level 60, right associativity).

  Fixpoint plug (t : term) {k1 k2} (c : context k1 k2) : term :=
      match c with
      | [.]    => t 
      | ec=:c' => plug ec:[t] c'
      end.
  Notation "c [ t ]" := (plug t c) (at level 0).


  Axioms
  (death_propagation :                                                       forall k ec,
       dead_ckind k -> dead_ckind (k+>ec))

  (proper_death :                                                               forall k,
       dead_ckind k -> ~ exists (r : redex k), True)

  (value_trivial1 :                                                      forall {k} ec t,
       forall (v : value k),  ~dead_ckind (k+>ec)  -> ec:[t] = v -> 
           exists (v' : value (k+>ec)), t = v').

End RED_MINI_LANG.





Module RED_LANG_Facts (R : RED_MINI_LANG).

  Import R.


  (* Contexts *)

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


  Lemma context_cons_snoc :                                               forall {k1 k2},
      forall ec0 (c0 : context k1 k2), exists ec1 c1, (ec0=:c0) = (c1~+ec1=:[.]).

  Proof.
    intros; revert ec0.
    induction c0; intros.
    - exists ec0; eexists [.]; trivial.
    - destruct IHc0 with ec as (ec1, (c1, IH)).
      exists ec1; eexists (ec0=:c1); rewrite IH; trivial.
  Qed.


  Lemma mid_ccons_as_append :                      forall {k1 k2} (c1 : context k1 k2) ec
                                                         {k3} (c2 : context (k2+>ec) k3),
      c2 ~+ ec =: c1  =  c2 ~+ (ec =: [.]) ~+ c1.

  Proof.
    intros k1 k2 c1 ec k3 c2.
    induction c2;
    solve [ auto ].
  Qed.


  Lemma append_assoc :      forall {k4 k3} (c1 : context k3 k4) {k2} (c2 : context k2 k3)
                                                               {k1} (c3 : context k1 k2),
      c1 ~+ c2 ~+ c3 = (c1 ~+ c2) ~+ c3.

  Proof.
    induction c1; intros; 
    solve [simpl; f_equal; eauto].
  Qed.


  Lemma ccons_append_empty_self_JM :                         forall {k1 k2 k3},
      forall (c1 : context k1 k2) (c2 : context k2 k3), 
          k2 = k3 -> c1 ~= c2 ~+ c1 -> c2 ~= [.](k2).

  Proof with eauto.
    intros k1 k2 k3 c1; revert k3.
    induction c1 as [ | ec k c1]; 
        intros k3 c2 H H0;
        destruct c2 as [ | ec0 k0 c2]...
    - discriminateJM H0.
    - exfalso.
      simpl in H0.
      inversion_ccons H0.
      assert (H1 : c2 ~+ ec0 =: [.](k0) ~= [.](k0)). 
      {
          eapply IHc1...
          rewrite <- append_assoc. 
          rewrite <- (mid_ccons_as_append c1 ec0 c2).
          replace (c2 ~+ ec0 =: c1) with c1 by auto.
          reflexivity.
      }
      revert H1; clear; revert c2.
      cut (forall k (c : context (k0 +> ec0) k), 
               k = k0 -> ~ (c ~+ ec0 =: [.](k0) ~= [.](k0))).
      { intros H c2 H1; eapply H... }
      intros k c G H.
      destruct c;
      discriminateJM H.
  Qed.


  Lemma ccons_append_empty_self :                     forall {k1 k2} (c1 : context k1 k2)
                                                                    (c2 : context k2 k2),
      c1 = c2 ~+ c1 -> c2 = [.](k2).

  Proof with eauto. 
    intros k1 k2 c1 c2 H.
    cut (c2 ~= [.](k2)).
    { intro H0; rewrite H0... }
    eapply ccons_append_empty_self_JM with c1...
    rewrite <- H.
    reflexivity.
  Qed.


  (* Death *)

  Lemma death_propagation2 : 
      forall k ec, ~dead_ckind (k+>ec) -> ~dead_ckind k.

  Proof. eauto using death_propagation. Qed.


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



  (* Values *)

  Lemma value_trivial : forall {k} (v : value k) {k'} (c : context k k') t, 
                            ~dead_ckind k' -> c[t] = v -> exists (v' : value k'), t = v'.

  Proof.
    intros k v k' c t; revert t.
    induction c;
        intros t H H0.
    - eauto.
    - destruct (IHc ec:[t]) as [v' H1];
      try solve 
      [ eauto using death_propagation2 
      | try rec_subst H1; eauto using value_trivial1, death_propagation2 ].
  Qed.

End RED_LANG_Facts.




Module Type RED_MINI_LANG2.

  Include RED_MINI_LANG.

  Inductive decomp k : Set :=
  | d_red : forall {k'}, redex k' -> context k k' -> decomp k
  | d_val : value k -> decomp k.
  Arguments d_val {k} _. Arguments d_red {k} {k'} _ _.

  Definition decomp_to_term {k} (d : decomp k) :=
      match d with
      | d_val v   => value_to_term v
      | d_red r c => c[r]
      end.
  Coercion decomp_to_term : decomp >-> term.

  Definition dec (t : term) k (d : decomp k) : Prop := 
      ~dead_ckind k /\ t = d.

  Axioms
  (decompose :                                                                forall t k,
       ~dead_ckind k -> exists d : decomp k, dec t k d)

  (value_redex :                                  forall {k} (v : value k) (r : redex k),
       value_to_term v <> redex_to_term r).

End RED_MINI_LANG2.




Module RED_LANG2_Facts (R : RED_MINI_LANG2).

  Import R.


  Definition only_trivial_dec t k :=                                        forall t' k',
      forall (c : context k k'), ~dead_ckind k' -> c[t'] = t -> 
          k = k' /\ [.](k) ~= c \/ exists (v : value k'), t' = v.


  Lemma trivial_val_red :                                                     forall t k,
      ~dead_ckind k -> only_trivial_dec t k ->
          (exists (v : value k), t = v) \/ (exists (r : redex k), t = r).

  Proof with eauto.
    intros t k H H0.
    destruct (decompose t k H) as [[k' r c | v]].
    - destruct (H0 r _ c) as [[H2 H3] | [v H2]]; dep_subst.
      + intro H2; apply (proper_death _ H2)...
      + symmetry; apply H1.
      + right. exists r; apply H1.
      + symmetry in H2. apply value_redex in H2. autof.
    - left. exists v; apply H1.
  Qed.

End RED_LANG2_Facts.




Module Type RED_MINI_LANG_WD <: RED_MINI_LANG.

  Include RED_MINI_LANG.

  Inductive decomp k : Set :=
  | d_red : forall {k'}, redex k' -> context k k' -> decomp k
  | d_val : value k -> decomp k.
  Arguments d_val {k} _. Arguments d_red {k} {k'} _ _.

  Definition decomp_to_term {k} (d : decomp k) :=
      match d with
      | d_val v   => value_to_term v
      | d_red r c => c[r]
      end.
  Coercion decomp_to_term : decomp >-> term.

  Definition dec (t : term) k (d : decomp k) : Prop := 
      ~dead_ckind k /\ t = d.

End RED_MINI_LANG_WD.



Module RedDecProcEqvDec (R : RED_MINI_LANG_WD).

  Module RF := RED_LANG_Facts R.
  Import R RF.


  Section S.

  Variable dec_proc : forall {k1 k2}, term -> context k1 k2 -> decomp k1 -> Prop.
  Arguments dec_proc {k1 k2} _ _ _.


  Hypotheses
  (dec_proc_correct :                             forall t {k1 k2} (c : context k1 k2) d,
       dec_proc t c d -> c[t] = d)

  (dec_proc_plug :      forall {k1 k2} (c : context k1 k2) {k3} (c0 : context k3 k1) t d,
       ~dead_ckind k2 -> dec_proc c[t] c0 d -> dec_proc t (c ~+ c0) d)

  (dec_proc_plug_rev :  forall {k1 k2} (c : context k1 k2) {k3} (c0 : context k3 k1) t d,
       dec_proc t (c ~+ c0) d -> dec_proc c[t] c0 d)

  (dec_proc_redex_self :             forall {k2} (r : redex k2) {k1} (c : context k1 k2),
       dec_proc r c (d_red r c))

  (dec_proc_value_self :                                        forall {k} (v : value k),
       ~dead_ckind k -> dec_proc v [.] (d_val v)).



  Theorem dec_proc_eqv_dec :                      forall t {k1 k2} (c : context k1 k2) d,
      ~dead_ckind k2 -> (dec_proc t c d <-> dec c[t] k1 d).

  Proof with eauto using (proper_death2 [.]), dead_context_dead.
    intros; split; intro.
    - split; [|apply dec_proc_correct]...
    - destruct H0 as [H1 H0].
      rewrite (compose_empty c).
      apply dec_proc_plug...
      rewrite H0.
      destruct d.
      + apply dec_proc_plug_rev...
        rewrite <- compose_empty.
        apply dec_proc_redex_self.
      + apply dec_proc_value_self...
  Qed.

  End S.

End RedDecProcEqvDec.

