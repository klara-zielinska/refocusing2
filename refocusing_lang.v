Require Import Util.
Require Export reduction_semantics.
Require Export refocusing_step.



Module Type RED_REF_LANG.

  Declare Module R   : RED_LANG.
  Declare Module DEC : REF_STEP R.
  Export R.
  Export DEC.


  (* A property of deterministic reduction semantics: *)
  Axiom redex_trivial : forall {k} (r : redex k), only_trivial r k.


  Inductive subterm_one_step : term -> term -> Prop :=
  | st_1 : forall {t t0} ec, t = ec:[t0] -> subterm_one_step t0 t.
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

End RED_REF_LANG.




Module RED_REF_LANG_Help.

  Ltac prove_st_wf := 
      intro t; constructor; induction t; 
      (
          intros ? H; 
          inversion H as [? ? ec DECT]; subst; 
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

