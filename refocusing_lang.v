Require Import Program.
Require Import Util.
Require Export reduction_semantics.
Require Import reduction_semantics_facts.
Require Export reduction_strategy.




Module Type REF_LANG <: RED_STRATEGY_LANG.

  Include RED_STRATEGY_LANG.



  (* A property of deterministic reduction semantics: *)
  Axiom redex_trivial1 : forall {k} (r : redex k) ec t, 
                             ~dead_ckind (k+>ec) -> ec:[t] = r -> 
                                 exists (v : value (k+>ec)), t = v.


  Definition immediate_subterm t0 t := exists ec, t = ec:[t0].
  Axiom wf_immediate_subterm : well_founded immediate_subterm.


  Definition subterm_order := clos_trans_1n term immediate_subterm.
  Notation "t1 <| t2" := (subterm_order t1 t2) (at level 70, no associativity).
  Definition wf_subterm_order : well_founded subterm_order
      := wf_clos_trans_l _ _ wf_immediate_subterm.


  Parameter contract : forall {k}, redex k -> option term.

End REF_LANG.




Module Type REF_STRATEGY (R : REF_LANG) <: RED_STRATEGY R.

  Import R.

  Include RED_STRATEGY R.



  Axiom wf_search : forall k t, well_founded (search_order k t).

  Axiom search_order_antisym : forall k t ec ec0, 
      k, t |~ ec << ec0 -> ~ k, t |~ ec0 << ec.

  Axiom search_order_trans   : forall k t ec0 ec1 ec2,
      k, t |~ ec0 << ec1 -> k, t |~ ec1 << ec2 -> k,t |~ ec0 << ec2.

  Axiom search_order_comp_if : 
      forall t ec0 ec1, immediate_ec ec0 t -> immediate_ec ec1 t -> 
          forall k, ~ dead_ckind (k+>ec0) -> ~ dead_ckind (k+>ec1) ->
              k, t |~ ec0 << ec1  \/  k, t |~ ec1 << ec0  \/  ec0 = ec1.

  Axiom search_order_comp_fi : 
      forall k t ec0 ec1,  k, t |~ ec0 << ec1 ->  
          immediate_ec ec0 t /\ immediate_ec ec1 t /\ 
              ~ dead_ckind (k+>ec0) /\ ~ dead_ckind (k+>ec1).

End REF_STRATEGY.




Module RedRefLang (R : REF_LANG) (ST : REF_STRATEGY R) <: RED_LANG.

  Module RF := RED_LANG_Facts R.

  Include R.
  Import ST RF.



  Lemma decompose : 
      forall (t : term) k1, ~ dead_ckind k1 ->
          (exists (v : value k1), t = v) \/
          (exists k2 (r : redex k2) (c : context k1 k2), t = c[r : term]).

  Proof with eauto.
    induction t using (well_founded_ind wf_subterm_order); intros.

    remember (dec_term t k1); assert (hh := dec_term_correct t k1);
    symmetry in Heqi;
    destruct i; rewrite Heqi in hh.

    - right; exists k1; exists r; eexists [.]...

    - destruct (H t0) with (k1 := k1+>e) as [(v, Hv) | (k2, (r, (c, Hrc)))].
          repeat econstructor...
          eapply dec_term_next_alive... 

      + { subst t0.
        assert (~ dead_ckind (k1+>e)) as Hndk.
          { eapply dec_term_next_alive... } 
        clear Heqi; generalize dependent v.
        induction e using (well_founded_ind (wf_search k1 t)); intros.

        remember (dec_context e _ v); assert (ht := dec_context_correct e _ v); 
        destruct i; rewrite <- Heqi in ht; try 
        (   compute in hh; rewrite <- hh in ht).

        - right; exists k1; exists r; eexists [.]...

        - destruct (H t0) with (k1 := k1+>e0) as [(v0, Hv) | (k2, (r, (c, Hrc)))].
              repeat econstructor...
              eapply dec_context_next_alive...

          + symmetry in Heqi.
            destruct (dec_context_term_next _ _ _ Heqi) as (H2, _).

            subst t0.
            assert (~ dead_ckind (k1+>e0)) as Hndk2.
              { eapply dec_context_next_alive... }
            rewrite <- hh in H2.
            destruct (H1 e0 H2 Hndk2 v0 ht) as [(v1, Hv1) | (k2, (r, (c, Hrc)))].
            * left; exists v1...
            * right; exists k2; exists r; exists c...

          + right; exists k2; exists r; exists (c~+e0=:[.]).
            subst t0; rewrite plug_compose...

        - left; exists v0...

        - intuition. 
        }

      + right; exists k2; exists r; exists (c~+(e=:[.])).
        subst t0; rewrite plug_compose...

    - left; exists v...

    - intuition.
  Qed.

End RedRefLang.




Module REF_LANG_Help.

  Ltac prove_st_wf := 
      intro t; constructor; induction t; 
      (
          intros ? H; 
          inversion H as [ec DECT]; subst; 
          destruct ec; inversion DECT; subst; 
          constructor; auto
      ).

  Ltac prove_ec_wf := 
      intros k t ec; destruct k, t, ec; repeat 
      (
          constructor; 
          intros ec H; 
          destruct ec; inversion H; dep_subst; clear H
      ).

End REF_LANG_Help.

