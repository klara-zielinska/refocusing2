Require Import Program.
Require Import Util.
Require Export reduction_semantics.
Require Import reduction_semantics_facts.
Require Export refocusing_step.



Module Type RED_REF_LANG.

  Declare Module R  : RED_LANG.
  Declare Module ST : STRATEGY_STEP R.
  Export R ST.


  (* A property of deterministic reduction semantics: *)
  Axiom redex_trivial1 : forall {k} (r : redex k) ec t, 
                             ~dead_ckind (k+>ec) -> ec:[t] = r -> 
                                 exists (v : value (k+>ec)), t = v.


  Definition subterm_one_step t0 t := exists ec, t = ec:[t0].
  Axiom wf_st1 : well_founded subterm_one_step.


  Definition subterm_order := clos_trans_1n term subterm_one_step.
  Notation "t1 <| t2" := (subterm_order t1 t2) (at level 40, no associativity).
  Definition wf_sto : well_founded subterm_order := wf_clos_trans_l _ _ wf_st1.


  Parameter ec_order : ckind -> term -> elem_context -> elem_context -> Prop.
  Notation "k , t |~  ec1 << ec2 " := (ec_order k t ec1 ec2) (at level 40, no associativity).
  Axiom wf_eco : forall k t, well_founded (ec_order k t).

  Axiom ec_order_antisym : forall k t ec ec0, 
      k, t |~ ec << ec0 -> ~ k, t |~ ec0 << ec.

  Axiom ec_order_trans   : forall k t ec0 ec1 ec2,
      k, t |~ ec0 << ec1 -> k, t |~ ec1 << ec2 -> k,t |~ ec0 << ec2.

  Axiom ec_order_comp_if : 
      forall t ec0 ec1, immediate_ec ec0 t -> immediate_ec ec1 t -> 
      forall k, ~ dead_ckind (k+>ec0) -> ~ dead_ckind (k+>ec1) ->
          k, t |~ ec0 << ec1  \/  k, t |~ ec1 << ec0  \/  ec0 = ec1.

  Axiom ec_order_comp_fi : forall k t ec0 ec1,
      k, t |~ ec0 << ec1  ->  immediate_ec ec0 t /\ immediate_ec ec1 t /\ 
                                  ~ dead_ckind (k+>ec0) /\ ~ dead_ckind (k+>ec1).


  Axiom dec_term_red_empty : 
      forall t k {r : redex k}, dec_term t k = in_red r -> only_empty t k.

  Axiom dec_term_val_empty : 
      forall t k {v : value k}, dec_term t k = in_val v -> only_empty t k.

  Axiom dec_term_term_top : 
      forall t k {t' ec}, dec_term t k = in_term t' ec -> 
          forall ec',  ~ k, t |~ ec << ec'.

  Axiom dec_context_red_bot : 
      forall k ec v {r : redex k}, dec_context ec k v = in_red r -> 
          forall ec',  ~ k, ec:[v] |~ ec' << ec.

  Axiom dec_context_val_bot : 
      forall k ec v {v' : value k}, dec_context ec k v = in_val v' -> 
          forall ec',  ~ k, ec:[v] |~ ec' << ec.

  Axiom dec_context_term_next : 
      forall ec0 k v {t ec1}, dec_context ec0 k v = in_term t ec1 -> 
      (*1*) k, ec0:[v] |~ ec1 << ec0 /\ 
      (*2*) forall ec,  k, ec0:[v] |~ ec << ec0  ->  ~ k, ec0:[v] |~ ec1 << ec.


  Axiom elem_context_det : 
      forall t ec {t'}, t = ec:[t'] -> 
          forall k ec',  k, t |~ ec' << ec -> 
              exists (v : value (k+>ec)), t' = v.

End RED_REF_LANG.





Module Type RED_REF_LANG_minus.

  (* Inhered from RED_REF_LANG : *)

  Declare Module SX : RED_SYNTAX.
  Declare Module ST : STRATEGY_STEP SX.
  Export SX ST.


  Axiom death_propagation : 
      forall k, dead_ckind k -> forall ec, dead_ckind (k+>ec).
  Axiom proper_death : 
      forall k, dead_ckind k -> ~ exists (r : redex k), True.


  Parameter  init_ckind : ckind.


  Axiom value_trivial1 : 
      forall {k} (v : value k) ec t, 
          ~dead_ckind (k+>ec) -> ec:[t] = v -> 
              exists (v' : value (k+>ec)), t = v'.
  Axiom value_redex    : forall {k} (v : value k) (r : redex k), 
                             value_to_term v <> redex_to_term r.


  Parameter contract : forall {k}, redex k -> option term.


  Axiom redex_trivial1 : forall {k} (r : redex k) ec t, 
                             ~dead_ckind (k+>ec) -> ec:[t] = r -> 
                                 exists (v : value (k+>ec)), t = v.

  Definition only_empty t k :=
      forall t' {k'} (c : context k k'), c[t'] = t -> ~ dead_ckind k' -> 
          k = k' /\ c ~= [.](k).
  Definition only_trivial t k :=
      forall t' {k'} (c : context k k'), c[t'] = t -> ~ dead_ckind k' -> 
          k = k' /\ c ~= [.](k) \/ exists (v : value k'), t' = v.


  Definition subterm_one_step t0 t := exists ec, t = ec:[t0].
  Axiom wf_st1 : well_founded subterm_one_step.


  Definition subterm_order := clos_trans_1n term subterm_one_step.
  Notation "t1 <| t2" := (subterm_order t1 t2) (at level 40, no associativity).
  Definition wf_sto : well_founded subterm_order := wf_clos_trans_l _ _ wf_st1.


  Parameter ec_order : ckind -> term -> elem_context -> elem_context -> Prop.
  Notation "k , t |~  ec1 << ec2 " := (ec_order k t ec1 ec2) (at level 40, no associativity).
  Axiom wf_eco : forall k t, well_founded (ec_order k t).

  Axiom ec_order_antisym : forall k t ec ec0, 
      k, t |~ ec << ec0 -> ~ k, t |~ ec0 << ec.

  Axiom ec_order_trans   : forall k t ec0 ec1 ec2,
      k, t |~ ec0 << ec1 -> k, t |~ ec1 << ec2 -> k,t |~ ec0 << ec2.

  Axiom ec_order_comp_if : forall t ec0 ec1,
      immediate_ec ec0 t -> immediate_ec ec1 t -> 
      forall k, ~ dead_ckind (k+>ec0) -> ~ dead_ckind (k+>ec1) ->
          k, t |~ ec0 << ec1  \/  k, t |~ ec1 << ec0  \/  ec0 = ec1.

  Axiom ec_order_comp_fi : forall k t ec0 ec1,
      k, t |~ ec0 << ec1  ->  immediate_ec ec0 t /\ immediate_ec ec1 t /\ 
                                  ~ dead_ckind (k+>ec0) /\ ~ dead_ckind (k+>ec1).



  Axiom dec_term_red_empty : 
      forall t k {r : redex k}, dec_term t k = in_red r -> only_empty t k.

  Axiom dec_term_val_empty : 
      forall t k {v : value k}, dec_term t k = in_val v -> only_empty t k.

  Axiom dec_term_term_top : 
      forall t k {t' ec}, dec_term t k = in_term t' ec -> 
          forall ec',  ~ k, t |~ ec << ec'.

  Axiom dec_context_red_bot : 
      forall k ec v {r : redex k}, dec_context ec k v = in_red r -> 
          forall ec',  ~ k, ec:[v] |~ ec' << ec.

  Axiom dec_context_val_bot : 
      forall k ec v {v' : value k}, dec_context ec k v = in_val v' -> 
          forall ec',  ~ k, ec:[v] |~ ec' << ec.

  Axiom dec_context_term_next : 
      forall ec0 k v {t ec1}, dec_context ec0 k v = in_term t ec1 -> 
      (*1*) k, ec0:[v] |~ ec1 << ec0 /\ 
      (*2*) forall ec,  k, ec0:[v] |~ ec << ec0  ->  ~ k, ec0:[v] |~ ec1 << ec.


  Axiom elem_context_det : 
      forall t ec {t'}, t = ec:[t'] -> 
          forall k ec',  k, t |~ ec' << ec -> 
              exists (v : value (k+>ec)), t' = v.

End RED_REF_LANG_minus.




Module mk_RedRefLang (PR : RED_REF_LANG_minus) <: RED_REF_LANG.

  Module SXF := RED_SYNTAX_Facts PR.SX.
  Import SXF.


  Module R <: RED_LANG.

    Include PR.SX.

    Definition death_propagation : 
        forall k, dead_ckind k -> forall ec, dead_ckind (k+>ec)

        := PR.death_propagation.

    Definition proper_death : 
        forall k, dead_ckind k -> ~ exists (r : redex k), True

        := PR.proper_death.

    Definition only_empty t k :=
        forall t' {k'} (c : context k k'), c[t'] = t -> ~ dead_ckind k' -> 
            k = k' /\ c ~= [.](k).
    Definition only_trivial t k :=
        forall t' {k'} (c : context k k'), c[t'] = t -> ~ dead_ckind k' -> 
            k = k' /\ c ~= [.](k) \/ exists (v : value k'), t' = v.

    Definition value_trivial1 : 
        forall {k} (v : value k) ec t, 
            ~dead_ckind (k+>ec) -> ec:[t] = v -> 
                exists (v' : value (k+>ec)), t = v'

        := @PR.value_trivial1.
    Definition value_redex   : forall {k} (v : value k) (r : redex k), 
                            value_to_term v <> redex_to_term r
        := @PR.value_redex.


    Lemma decompose : 
        forall (t : term) k1, ~ dead_ckind k1 ->
            (exists (v : value k1), t = v) \/
            (exists k2 (r : redex k2) (c : context k1 k2), t = c[r]).

    Proof with eauto.
      induction t using (well_founded_ind PR.wf_sto); intros.

      remember (PR.ST.dec_term t k1); assert (hh := PR.ST.dec_term_correct t k1);
      symmetry in Heqi;
      destruct i; rewrite Heqi in hh.

      - right; exists k1; exists r; eexists [.]...

      - destruct (H t0) with (k1 := k1+>e) as [(v, Hv) | (k2, (r, (c, Hrc)))].
            repeat econstructor...
            eapply PR.ST.dec_term_next_alive... 

        + { subst t0.
          assert (~ dead_ckind (k1+>e)) as Hndk.
            { eapply PR.ST.dec_term_next_alive... } 
          clear Heqi; generalize dependent v.
          induction e using (well_founded_ind (PR.wf_eco k1 t)); intros.

          remember (PR.ST.dec_context e _ v); assert (ht := PR.ST.dec_context_correct e _ v); 
          destruct i; rewrite <- Heqi in ht; try 
          (   compute in hh; rewrite <- hh in ht).

          - right; exists k1; exists r; eexists [.]...

          - destruct (H t0) with (k1 := k1+>e0) as [(v0, Hv) | (k2, (r, (c, Hrc)))].
                repeat econstructor...
                eapply PR.ST.dec_context_next_alive...

            + symmetry in Heqi.
              destruct (PR.dec_context_term_next _ _ _ Heqi) as (H2, _).

              subst t0.
              assert (~ dead_ckind (k1+>e0)) as Hndk2.
                { eapply PR.ST.dec_context_next_alive... }
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

    Inductive decomp k : Set :=
    | d_red : forall {k'}, redex k' -> context k k' -> decomp k
    | d_val : value k -> decomp k.
    Arguments d_val {k} _. Arguments d_red {k} {k'} _ _.


    Definition decomp_to_term {k} (d : decomp k) :=
        match d with
        | d_val v     => value_to_term v
        | d_red _ r c => c[r]
        end.
    Coercion decomp_to_term : decomp >-> term.


    Definition contract {k} r := @PR.contract k r.

    Definition init_ckind := PR.init_ckind.

  End R.


  Module ST := PR.ST.

  Export R ST.

  Definition redex_trivial1 {k} := @PR.redex_trivial1 k.
  Definition subterm_one_step t0 t := exists ec, t = ec:[t0].
  Definition wf_st1 := PR.wf_st1.


  Definition subterm_order := clos_trans_1n term subterm_one_step.
  Notation "t1 <| t2" := (subterm_order t1 t2) (at level 40, no associativity).
  Definition wf_sto := wf_clos_trans_l _ _ wf_st1.


  Definition ec_order := PR.ec_order.
  Notation "k , t |~  ec1 << ec2 " := (ec_order k t ec1 ec2) (at level 40, no associativity).
  Definition wf_eco := PR.wf_eco.

  Definition ec_order_antisym := PR.ec_order_antisym.
  Definition ec_order_trans   := PR.ec_order_trans.
  Definition ec_order_comp_if := PR.ec_order_comp_if.
  Definition ec_order_comp_fi := PR.ec_order_comp_fi.


  Definition dec_term_red_empty := PR.dec_term_red_empty.
  Definition dec_term_val_empty := PR.dec_term_val_empty.
  Definition dec_term_term_top  := PR.dec_term_term_top.

  Definition dec_context_red_bot   := PR.dec_context_red_bot.
  Definition dec_context_val_bot   := PR.dec_context_val_bot.
  Definition dec_context_term_next := PR.dec_context_term_next.


  Definition elem_context_det := PR.elem_context_det.

End mk_RedRefLang.



Module RED_REF_LANG_Help.

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

End RED_REF_LANG_Help.

