


(*** Interface ***)


Require Import Program
               Util
               rewriting_system
               reduction_languages_facts.
Require Export Subset
               reduction_semantics
               reduction_strategy.





Module Type PRE_REF_SEM <: RED_STRATEGY_LANG.

  Include RED_STRATEGY_LANG.


  Parameter contract : forall {k}, redex k -> option term.


  Definition immediate_subterm t0 t := exists ec, t = ec:[t0].
  Definition subterm_order          := clos_trans_1n term immediate_subterm.
  Definition reduce k t1 t2 := 
      exists {k'} (c : context k k') (r : redex k') t,  dec t1 k (d_red r c) /\
          contract r = Some t /\ t2 = c[t].

  Instance lrws : LABELED_REWRITING_SYSTEM ckind term :=
  { ltransition := reduce }. 
  Instance rws : REWRITING_SYSTEM term := 
  { transition := reduce init_ckind }.

  Notation "t1 <| t2"      := (subterm_order t1 t2)      (no associativity, at level 70).

  Axioms
  (redex_trivial1 :                                        forall {k} (r : redex k) ec t,
       ~dead_ckind (k+>ec) -> ec:[t] = r -> exists (v : value (k+>ec)), t = v)
  (wf_immediate_subterm : well_founded immediate_subterm)
  (wf_subterm_order     : well_founded subterm_order).


  Class SafeKRegion (k : ckind) (P : term -> Prop) :=
  { 
      preservation :                                                        forall t1 t2,
          P t1  ->  k |~ t1 → t2  ->  P t2;
      progress :                                                               forall t1,
          P t1  ->  (exists (v : value k), t1 = v) \/ (exists t2, k |~ t1 → t2)
  }.

End PRE_REF_SEM.





Module Type PRE_PRECISE_REF_SEM.

  Include PRE_REF_SEM.
  Axiom dead_is_comp : CompPred _ dead_ckind.

End PRE_PRECISE_REF_SEM.





Module Type REF_STRATEGY (PR : PRE_REF_SEM) <: RED_STRATEGY PR.

  Import PR.

  Include RED_STRATEGY PR.

  Axioms 
  (wf_search :                                                                forall k t,
       well_founded (search_order k t))

  (search_order_trans :                                           forall k t ec0 ec1 ec2,
       k, t |~ ec0 << ec1 -> k, t |~ ec1 << ec2 -> k,t |~ ec0 << ec2)

  (search_order_comp_if :                                             forall t ec0 ec1 k,
       immediate_ec ec0 t -> immediate_ec ec1 t -> 
       ~dead_ckind (k+>ec0) -> ~dead_ckind (k+>ec1) ->
           k, t |~ ec0 << ec1  \/  k, t |~ ec1 << ec0  \/  ec0 = ec1)

  (search_order_comp_fi :                                             forall k t ec0 ec1,
       k, t |~ ec0 << ec1 -> 
           immediate_ec ec0 t /\ immediate_ec ec1 t /\ 
           ~dead_ckind (k+>ec0) /\ ~dead_ckind (k+>ec1)).

End REF_STRATEGY.





Module Type RED_REF_SEM <: RED_SEM.

  Declare Module R  : RED_SEM.
  Declare Module ST : RED_STRATEGY_STEP R.

  Include R.
  Export ST.


  Inductive dec_proc {k1} : forall {k2}, term -> context k1 k2 -> decomp k1 -> Prop :=

  | d_dec  : forall t {k2} (c : context k1 k2) r,
               dec_term t k2 = in_red r -> 
               dec_proc t c (d_red r c)
  | d_v    : forall t {k2} (c : context k1 k2) d v,
               dec_term t k2 = in_val v ->
               decctx_proc v c d ->
               dec_proc t c d
  | d_term : forall t {k2} (c : context k1 k2) d t0 ec,
               dec_term t k2 = in_term t0 ec ->
               dec_proc t0 (ec=:c) d ->
               dec_proc t c d

  with decctx_proc {k1} : forall {k2}, value k2 -> context k1 k2 -> decomp k1 -> Prop :=

  | dc_end  : forall (v : value k1),
                ~ dead_ckind k1 ->
                decctx_proc v [.] (d_val v)
  | dc_dec  : forall ec {k2} (c : context k1 k2) (v : value (k2+>ec)) r,
                dec_context ec k2 v = in_red r ->
                decctx_proc v (ec=:c) (d_red r c)
  | dc_val  : forall ec {k2} (c  : context k1 k2) (v : value (k2+>ec)) d v0,
                dec_context ec k2 v = in_val v0 ->
                decctx_proc v0 c d ->
                decctx_proc v (ec=:c) d
  | dc_term : forall ec {k2} (c : context k1 k2) (v : value (k2+>ec)) d t ec0,
                dec_context ec k2 v = in_term t ec0 ->
                dec_proc t (ec0=:c) d ->
                decctx_proc v (ec=:c) d.

  Scheme dec_proc_Ind    := Induction for dec_proc    Sort Prop
    with decctx_proc_Ind := Induction for decctx_proc Sort Prop.


  Axioms
  (dec_proc_val_eqv_decctx :       forall {k2} (v : value k2) {k1} (c : context k1 k2) d,
       dec_proc v c d <-> decctx_proc v c d)
  (dec_proc_eqv_dec :                             forall t {k1 k2} (c : context k1 k2) d,
      ~dead_ckind k2 -> (dec_proc t c d <-> dec c[t] k1 d)). 

End RED_REF_SEM.





Module Type PRECISE_RED_REF_SEM.

  Include RED_REF_SEM.
  Axiom dead_is_comp : CompPred _ dead_ckind.

End PRECISE_RED_REF_SEM.





Module Type RED_PE_REF_SEM <: RED_REF_SEM.

  Include RED_REF_SEM.
  Import R.

  Axioms
  (dec_context_not_val :                                 forall ec {k} (v1 : value k) v0,
       dec_context ec k v0 <> in_val v1)
  (dec_term_value :                                             forall {k} (v : value k),
       dec_term v k = in_val v).

End RED_PE_REF_SEM.





Module REF_LANG_Help.

  Ltac prove_st_wf := 
      intro t; constructor; induction t; 
      (
          intros ? H; 
          inversion H as [ec DECT]; subst; 
          destruct ec; inversion DECT; subst; 
          constructor; auto
      ).

  Context `{term : Set}.
  Context `{immediate_subterm : term -> term -> Prop}.
  Context `{wf_immediate_subterm : well_founded immediate_subterm}.

  Ltac prove_sto_wf :=
      exact (wf_clos_trans_l _ _ wf_immediate_subterm).

  Ltac prove_ec_wf := 
      intros k t ec; destruct k, t, ec; repeat 
      (
          constructor; 
          intros ec H; 
          destruct ec; inversion H; dep_subst; clear H
      ).

End REF_LANG_Help.





(*** Implementation ***)


Module RedRefSem (PR : PRE_REF_SEM) (ST : REF_STRATEGY PR) <: RED_REF_SEM.

  Module RLF := RED_LANG_Facts PR.
  Import PR RLF.



  Module ST := ST.
  Export ST.

  Module R <: RED_SEM.

    Include PR.

    Lemma decompose :                                                forall (t : term) k,
        ~dead_ckind k -> exists (d : decomp k), dec t k d.

    Proof with unfold dec; eauto using dec_context_next_alive, dec_term_next_alive.
      induction t using (well_founded_ind wf_subterm_order); intros.

      remember (dec_term t k); assert (hh := dec_term_correct t k);
      symmetry in Heqi;
      destruct i; rewrite Heqi in hh.

      - exists (d_red r [.])...

      - destruct (H t0) with (k := k+>e) as [[k2 r c | v] [? Hd]];
            unfold dec in *.
            repeat econstructor...
            eapply dec_term_next_alive...

        + exists (d_red r (c~+(e=:[.]))).
          subst t0; simpl; rewrite plug_compose...

        + { subst t0.
          assert (~dead_ckind (k+>e))...
          clear Heqi; generalize dependent v.
          induction e using (well_founded_ind (wf_search k t)); intros.

          remember (dec_context e _ v); assert (ht := dec_context_correct e _ v); 
          destruct i; rewrite <- Heqi in ht; try 
          ( compute in hh; rewrite <- hh in ht).

          - exists (d_red r [.])...

          - destruct (H t0) with (k := k+>e0) as [[k2 r c | v0] [? Hd]].
                repeat econstructor...
                eapply dec_context_next_alive...

            + exists (d_red r (c~+e0=:[.])).
              subst t0; simpl; rewrite plug_compose...

            + symmetry in Heqi.
              destruct (dec_context_term_next _ _ _ Heqi) as (H5, _).

              subst t0.
              rewrite <- hh in H5...

          - eexists (d_val v0)...

          - intuition.
          }

      - eexists (d_val v)...

      - intuition.
    Qed.

  End R.

  Include R.



  Inductive dec_proc {k1} : forall {k2}, term -> context k1 k2 -> decomp k1 -> Prop :=

  | d_dec  : forall t {k2} (c : context k1 k2) r,
               dec_term t k2 = in_red r -> 
               dec_proc t c (d_red r c)
  | d_v    : forall t {k2} (c : context k1 k2) d v,
               dec_term t k2 = in_val v ->
               decctx_proc v c d ->
               dec_proc t c d
  | d_term : forall t {k2} (c : context k1 k2) d t0 ec,
               dec_term t k2 = in_term t0 ec ->
               dec_proc t0 (ec=:c) d ->
               dec_proc t c d

  with decctx_proc {k1} : forall {k2}, value k2 -> context k1 k2 -> decomp k1 -> Prop :=

  | dc_end  : forall (v : value k1),
                ~ dead_ckind k1 ->
                decctx_proc v [.] (d_val v)
  | dc_dec  : forall ec {k2} (c : context k1 k2) (v : value (k2+>ec)) r,
                dec_context ec k2 v = in_red r ->
                decctx_proc v (ec=:c) (d_red r c)
  | dc_val  : forall ec {k2} (c  : context k1 k2) (v : value (k2+>ec)) d v0,
                dec_context ec k2 v = in_val v0 ->
                decctx_proc v0 c d ->
                decctx_proc v (ec=:c) d
  | dc_term : forall ec {k2} (c : context k1 k2) (v : value (k2+>ec)) d t ec0,
                dec_context ec k2 v = in_term t ec0 ->
                dec_proc t (ec0=:c) d ->
                decctx_proc v (ec=:c) d.

  Scheme dec_proc_Ind    := Induction for dec_proc    Sort Prop
    with decctx_proc_Ind := Induction for decctx_proc Sort Prop.



  Lemma dec_not_dead :                          forall {t k1 k2} {c : context k1 k2} {d},
      dec_proc t c d -> ~dead_ckind k2.

  Proof.
    intros; intro.
    assert (hh := dec_term_from_dead t k2 H0).
    destruct H;
    solve
    [ rewrite H in hh;
      discriminate hh ].
  Qed.


  Lemma decctx_not_dead :                         forall {k1 k2} (c : context k1 k2) v d,
      decctx_proc v c d -> ~dead_ckind k2.

  Proof with auto.
    intros; intro.
    destruct H;
    solve 
    [ intuition
    | assert (hh := dec_context_from_dead ec k2 v H0);
      rewrite H in hh;
      discriminate hh ].
  Qed.


  Lemma dec_correct :                             forall t {k1 k2} (c : context k1 k2) d,
      dec_proc t c d -> c[t] = d.

  Proof.
    intros t k1 k2 c d.
    induction 1 using dec_proc_Ind with
    (P := fun _ t c d (_ : dec_proc t c d)     => c[t] = d)
    (P0:= fun _ v c d (_ : decctx_proc v c d)  => c[v] = d);

    simpl; auto;
    match goal with
    | _ : dec_term ?t ?k2 = _      |- _ => assert (hh := dec_term_correct t k2)
    | _ : dec_context ?ec _ ?v = _ |- _ => assert (hh := dec_context_correct ec _ v)
    end;
    rewrite e in hh; simpl in *; 
    rewrite hh;
    solve [auto].
  Qed.


  Lemma dec_val :                  forall {k2} (v : value k2) {k1} (c : context k1 k2) d,
      dec_proc v c d -> decctx_proc v c d.

  Proof with eauto.
    intros k2 v k1; remember (value_to_term v) as t; revert k2 v Heqt.
    induction t using (well_founded_ind wf_subterm_order); intros; subst.

    dependent destruction H0;
        assert (hh := dec_term_correct (v:term) k2); rewrite H in hh.

    - contradiction (value_redex _ _ hh).

    - rewrite (value_to_term_injective _ _ hh)...

    - destruct (value_trivial v (ec=:[.]) t0); auto;
          try solve [eapply dec_term_next_alive; eassumption];
          subst t0;
          capture_all value @value_to_term.

      clear H; revert x H0 hh.
      induction ec using (well_founded_ind (wf_search k2 (v:term))); intros.

      assert (decctx_proc x (ec=:c) d).
      { apply (H1 x)... do 2 econstructor... }

      dependent destruction H2;
          assert (G1 := ccons_inj _ _ _ _ x1 x);
          subst; rec_subst G1;

          assert (gg := dec_context_correct ec k2 x0); rewrite H2 in gg.

      + contradiction (value_redex v r); congruence.

      + assert (v1 = v).
        { apply (value_to_term_injective v1 v); congruence. }
        subst...

      + assert (~ dead_ckind (k2+>ec1)).
        {
            destruct search_order_comp_fi with k2 (v:term) ec1 ec as (?, (?, (?, ?)))...
            - rewrite hh; eapply dec_context_term_next...
        }

        destruct (value_trivial v (ec1=:[.]) t); auto;
            try solve [ simpl; congruence ];
            subst t.
        eapply (H ec1); eauto.
        * rewrite hh; eapply dec_context_term_next; eauto.
        * congruence. 
  Qed.


  Lemma val_dec :                forall {k2} {v : value k2} {k1} {c : context k1 k2} {d},
      decctx_proc v c d -> dec_proc v c d.

  Proof with eauto.
    intros k2 v k1; remember (value_to_term v); revert k2 v Heqt.
    induction t using (well_founded_ind wf_subterm_order); intros; subst.

    remember (dec_term v k2) as i;
    assert (hh := dec_term_correct v k2);
    destruct i; rewrite <- Heqi in hh; symmetry in Heqi.

    - contradict (value_redex _ _ hh).

    - apply (d_term _ _ _ _ _ Heqi).

      assert (~ dead_ckind (k2+>e)) as Hndk.
      { eapply dec_term_next_alive... }
      destruct (value_trivial v (e=:[.]) t);
          try solve [auto];
          subst t;
          capture_all value @value_to_term.

      clear Heqi; revert e x hh Hndk.
      induction e using (well_founded_ind (wf_search k2 v)); intros.

      apply (H x) with (v := x)...
      { do 2 econstructor... }
      remember (dec_context e _ x) as i.
      assert (gg := dec_context_correct e _ x);
      destruct i; rewrite <- Heqi in gg; subst;
      symmetry in Heqi.

      + contradiction (value_redex v r); congruence.

      + assert (~ dead_ckind (k2+>e0)).
        {
            destruct search_order_comp_fi with k2 v e0 e as (?, (?, (?, ?)))...
            - rewrite hh; eapply dec_context_term_next...
        }

        destruct (value_trivial v (e0=:[.]) t);
            try solve [simpl; congruence];
            subst t.

        apply dc_term with (x0:R.term) e0...
        apply (H1 e0)...
        * rewrite hh; eapply dec_context_term_next...
        * compute; congruence.

      + eapply dc_val...
        assert (v0 = v).
        * apply (value_to_term_injective v0 v); congruence.
        * subst...

      + intuition.

    - assert (H1 := value_to_term_injective _ _ hh); subst; 
      econstructor...

    - contradiction (decctx_not_dead _ _ _ H0).
  Qed.


  Lemma dec_redex_self_e :                                      forall {k} (r : redex k),
      dec_proc r [.] (d_red r [.]).

  Proof with eauto.
    intros; 
    remember (dec_term r k).
    assert (~ dead_ckind k).
    { eapply proper_death2... apply [.]. }

    destruct i;
        assert (hh := dec_term_correct r k);
        rewrite <- Heqi in hh; 
        simpl in hh; try symmetry in hh.

    - apply redex_to_term_injective in hh; subst; constructor...

    - symmetry in Heqi; assert (H0 := dec_term_term_top _ _ Heqi).
      assert (~ dead_ckind (k+>e)) as Hndk.
      { eapply dec_term_next_alive... } 
      econstructor 3...
      destruct (redex_trivial1 r e t Hndk hh) as (v, H1)...

      subst t.
      clear H0 Heqi; 
      generalize dependent v; generalize dependent e.
      induction e using (well_founded_ind (wf_search k r)); intros.

      apply val_dec.
      remember (dec_context e _ v); assert (ht := dec_context_correct e _ v);
      rewrite <- Heqi in ht; symmetry in Heqi.

      destruct i; simpl in ht.

      + rewrite hh in ht.
        apply redex_to_term_injective in ht; subst.
        constructor...

      + econstructor 4...
        rewrite ht in hh.
        assert (~ dead_ckind (k+>e0)).
        { eapply dec_context_next_alive... }
        destruct (redex_trivial1 r e0 t H1 hh) as (v1, H4)...
        subst t.
        destruct (dec_context_term_next _ _ _ Heqi).
        apply H0...
        * congruence.

      + rewrite ht in hh; contradiction (value_redex _ _ hh).

      + intuition. 

    - contradict hh; apply value_redex.

    - intuition.
  Qed.


  Lemma dec_redex_self :             forall {k2} (r : redex k2) {k1} (c : context k1 k2),
      dec_proc r c (d_red r c).

  Proof with eauto.
      intros;
      assert (H := dec_redex_self_e r);
      generalize c.

      (* induction on H *)
      apply dec_proc_Ind with

      (P  := fun k2' t c0 d (_ : dec_proc t c0 d) => 
                 match d with
                 | d_val v      => True
                 | d_red r' c1 => forall (c : context k1 k2), 
                                         dec_proc t (c0~+c) (d_red r' (c1~+c))
                 end)
      (P0 := fun k2' v c0 d (_ : decctx_proc v c0 d) => 
                 match d with
                 | d_val v      => True
                 | d_red r' c1 => forall (c : context k1 k2), 
                                         decctx_proc v (c0~+c) (d_red r' (c1~+c))
                 end)
      (d0 := H);
      
      intros;
      try destruct d;
      unfold dec in *;
      solve 
      [ auto
      | econstructor;   eauto
      | econstructor 3; eauto
      | econstructor 4; eauto ].
  Qed.





  Lemma dec_under_redex :          forall ec t {k} (r : redex k) {k0} (c : context k0 k),
       ec:[t] = r -> ~dead_ckind (k+>ec) -> dec_proc t (ec=:c) (d_red r c).

  Proof.
    intros ec t k r k0 c H H0.
    assert (exists (v : value (k+>ec)), t = v) as [v H1];
              eauto using redex_trivial1.
    subst.
    apply val_dec.
    induction ec using (well_founded_ind (wf_search k r)).
    remember (dec_context ec _ v) as D eqn:HeqD; destruct D;
    assert (H2 := dec_context_correct ec _ v);
    rewrite <- HeqD in H2.
    - constructor 2. 
      assert (r = r0). 
      { apply redex_to_term_injective; congruence. }
      congruence.
    - econstructor 4.
      symmetry; apply HeqD.
      assert (exists (v' : value (k+>e)), t = v') as [v' H3].
      { rewrite H2 in H; eauto using redex_trivial1, dec_context_next_alive. }
      subst. 
      apply val_dec.
      apply H1.
      + symmetry in HeqD; destruct (dec_context_term_next _ _ _ HeqD) as [H3 _].
        congruence. 
      + eauto using dec_context_next_alive.
      + congruence.
    - assert ((v0 : term) = r).
      { compute; congruence. }
      exfalso; eauto using (value_redex v0 r).
    - autof.
  Qed.


  Lemma dec_under_value :        forall ec t {k} (v : value k) {k0} (c : context k0 k) d,
      ec:[t] = v -> ~dead_ckind (k+>ec) -> decctx_proc v c d -> dec_proc t (ec=:c) d.

  Proof.
    intros ec t k v k0 c d H H0 H1.
    assert (exists (v : value (k+>ec)), t = v) as [v0 H2];
              eauto using value_trivial1.
    subst.
    apply val_dec.
    induction ec using (well_founded_ind (wf_search k v)).
    remember (dec_context ec _ v0) as D eqn:HeqD; destruct D;
    assert (H3 := dec_context_correct ec _ v0);
    rewrite <- HeqD in H3.
    - assert ((v : term) = r).
      { compute; congruence. }
      exfalso; eauto using (value_redex v r).
    - econstructor 4.
      + symmetry; apply HeqD.
      + assert (exists (v' : value (k+>e)), t = v') as [v' H4].
        { rewrite H3 in H; eauto using value_trivial1, dec_context_next_alive. }
        subst. 
        apply val_dec.
        apply H2.
        * symmetry in HeqD; destruct (dec_context_term_next _ _ _ HeqD) as [H4 _].
          congruence. 
        * eauto using dec_context_next_alive.
        * congruence.
    - assert (v = v1).
      { apply value_to_term_injective; congruence. }
      subst.
      econstructor 3; eauto.
    - autof.
  Qed.


  Lemma dec_plug :    forall {k1 k2} (c : context k1 k2) {k3} {c0 : context k3 k1} {t d},
      ~dead_ckind k2 -> dec_proc c[t] c0 d -> dec_proc t (c~+c0) d.

  Proof with eauto.
      induction c; intros; simpl.
      - trivial.

      - apply IHc in H0; clear IHc;
        [ | apply (death_propagation2 _ _ H) ].
        inversion H0; dep_subst;
            match goal with H : dec_term ec:[t] k2 = _ |- _ =>
            assert (hh := dec_term_correct (ec:[t]) k2);
            rewrite H in hh
            end.

        + auto using dec_under_redex.

        + eauto using dec_under_value.

        + destruct search_order_comp_if with ec:[t] ec0 ec k2 as [H3 | [H3 | H3]].
              compute...
              compute...
              eapply dec_term_next_alive...
              apply H.

          * contradiction (dec_term_term_top _ _ H2 ec).
          * destruct (elem_context_det _ _ hh _ _ H3) as (v, H4)...
            subst t1.
            {
                clear H2; generalize dependent v; generalize dependent ec0.
                induction ec0 using (well_founded_ind (wf_search k2 ec:[t])); intros.
                
                assert (H4 := dec_val _ _ _ H5).
                dependent destruction H4;
                inversion_ccons x.
                - rewrite hh in H3; 
                  contradiction (dec_context_red_bot _ _ _ H2 _ H3).
                - rewrite hh in H3; 
                  contradiction (dec_context_val_bot _ _ _ H2 _ H3).
                - assert (ht := dec_context_correct ec0 _ v).
                  rewrite H2 in ht.
                  rewrite <- hh in ht.
                  destruct (dec_context_term_next _ _ _ H2) as (H4', H6).
                  destruct search_order_comp_if with ec:[t] ec2 ec k2 as [H7|[H7|H7]].
                      compute...
                      compute...
                      assert (H7 := search_order_comp_fi _ _ _ _ H4'); intuition.
                      assert (H7 := search_order_comp_fi _ _ _ _ H3); intuition.

                  + contradiction (H6 ec); rewrite <- hh...
                  + destruct (elem_context_det _ _ ht _ _ H7) as (v1, h4)...
                    subst t0.
                    apply H1 with ec2 v1...
                      { congruence. }
                  + subst; assert (H8 := elem_plug_injective1 _ _ _ ht).
                    subst...
            }

          * subst; assert (H8 := elem_plug_injective1 _ _ _ hh).
            subst...
  Qed.


  Lemma dec_plug_rev :       forall {k1 k2} (c : context k1 k2) {k3} (c0 : context k3 k1)
                                                                                     t d,
          dec_proc t (c~+c0) d -> dec_proc c[t] c0 d.

  Proof with eauto.
      induction c; intros; simpl.

      - trivial.

      - apply IHc; clear IHc;
            eauto using death_propagation2.

        remember (dec_term ec:[t] k2) as D;
        symmetry in HeqD;
        destruct D;
        assert (DTC2 := dec_term_correct ec:[t] k2);
        rewrite HeqD in DTC2;
        subst.
        + cut (d = d_red r (c~+c0)).
          { intro; subst; constructor; auto. }

          destruct (redex_trivial1 _ _ _ (dec_not_dead H) DTC2) as [v ?]; subst t.
          eapply dec_val in H.

          clear HeqD.
          induction ec using (well_founded_ind (wf_search k2 r)).

          dependent destruction H; dep_subst; 
          simpl in x; inversion_ccons x;
          assert (DCC := dec_context_correct ec k2 v);
          rewrite H in DCC.
          * assert (r = r0).
            { apply redex_to_term_injective; congruence. }
            subst.
            constructor...
          * assert ((v1 : term) = r).
            { compute; congruence. }
            exfalso; eauto using (value_redex v1 r).
          * assert (H3 := dec_context_next_alive _ _ _ _ _ H).
            destruct (redex_trivial1 r ec1 t) as [v' ?]; 
                try solve [auto | congruence].
            subst t.
            eapply (H0 ec1);
            try solve
            [ rewrite <- DTC2; destruct (dec_context_term_next _ _ _ H); auto
            | eauto using dec_val
            | compute; congruence ]. 

        + destruct search_order_comp_if with ec:[t] e ec k2 as [H1 | [H1 | H1]].
              compute...
              compute...
              eapply dec_term_next_alive...
              eauto using dec_not_dead.

          * contradict (dec_term_term_top _ _ HeqD _ H1).

          * destruct (elem_context_det _ _ DTC2 _ _ H1) as (v, H2)...
            subst t0.
            econstructor 3; eauto.
            {
              clear HeqD; generalize dependent v; generalize dependent e.
              induction e using (well_founded_ind (wf_search k2 ec:[t])); intros.

              apply val_dec.
              remember (dec_context e _ v) as D.
              destruct D;
                  symmetry in HeqD;
                  assert (ht := dec_context_correct e _ v); 
                  rewrite HeqD in ht.

              - rewrite DTC2 in H1;
                contradiction (dec_context_red_bot _ _ _ HeqD _ H1).

              - destruct (dec_context_term_next _ _ _ HeqD) as (H3, H4).
                econstructor 4...
                rewrite <- DTC2 in ht.
                destruct search_order_comp_if with ec:[t] e0 ec k2 as [H5 | [H5 | H5]].
                    compute...
                    compute...
                    apply (search_order_comp_fi _ _ _ _ H3).
                    apply (search_order_comp_fi _ _ _ _ H1).

                + rewrite DTC2 in H1; 
                  contradiction (H4 ec H1). 
                  congruence.
                + destruct (elem_context_det _ _ ht _ _ H5) as (v0, H6)...
                  subst t0.
                  apply H0...
                  { congruence. }
                + subst.
                  assert (H5 := elem_plug_injective1 _ _ _ ht).
                  subst...

              - rewrite DTC2 in H1;
                contradiction (dec_context_val_bot _ _ _ HeqD _ H1).

              - contradict ht.
                eapply search_order_comp_fi...
            }

          * subst.
            assert (H5 := elem_plug_injective1 _ _ _ DTC2).
            subst.
            econstructor 3...

        + cut (decctx_proc v (c~+c0) d).
          { intro; econstructor; eauto. }
          
          destruct (value_trivial1 _ _ _ (dec_not_dead H) DTC2) as [v' ?]; subst t.
          capture_all value @value_to_term.
          eapply dec_val in H.

          clear HeqD.
          induction ec using (well_founded_ind (wf_search k2 v)).

          assert (DCC := dec_context_correct ec k2 v').
          dependent destruction H; simpl in x; inversion_ccons x;
          rewrite H in DCC.
          * exfalso.
            assert ((v : term) = r).
            { congruence. }
            eauto using (value_redex v r).
          * replace v1 with v in * by (apply value_to_term_injective; congruence).
            eauto.
          * destruct (@value_trivial1 _ ec1 t v) as [v'' ?];
                try solve [eauto using dec_context_next_alive | congruence].
            capture_all value @value_to_term.
            subst t.
            apply (H0 ec1) with (v':=v'');
            solve
            [ destruct (dec_context_term_next ec k2 v' H); rewrite <- DTC2; eauto
            | eauto using dec_context_next_alive, dec_val
            | congruence ].

        + exfalso; 
          eapply dec_not_dead; 
          eauto using death_propagation.
  Qed.


  Lemma dec_value_self :                                        forall {k} (v : value k),
      ~ dead_ckind k -> dec_proc v [.] (d_val v).

  Proof with auto.
    intros.
    apply val_dec.
    constructor...
  Qed.


  Theorem dec_proc_val_eqv_decctx :                       forall {k2} (v : value k2) {k1}
                                                                   (c : context k1 k2) d,
       dec_proc v c d <-> decctx_proc v c d.

  Proof.
    split; [apply dec_val | apply val_dec].
  Qed.


  Module DPT := RedDecProcEqvDec R.

  Theorem dec_proc_eqv_dec :                      forall t {k1 k2} (c : context k1 k2) d,
      ~dead_ckind k2 -> (dec_proc t c d <-> dec c[t] k1 d).

  Proof. eauto 6 using DPT.dec_proc_eqv_dec, dec_correct, dec_plug, dec_plug_rev, 
                         dec_redex_self, dec_value_self. Qed.

End RedRefSem.





Module PreciseRedRefSem (PR : PRE_PRECISE_REF_SEM) (ST : REF_STRATEGY PR) 
                                                                  <: PRECISE_RED_REF_SEM.

  Include RedRefSem PR ST.

  Definition dead_is_comp := PR.dead_is_comp.

End PreciseRedRefSem.
