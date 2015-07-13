Require Import Program.
Require Import Setoid.
Require Export refocusing_signatures.
Require Import Wellfounded.Inclusion.
Require Import Wellfounded.Inverse_Image.

Module Lang_Prop (R : RED_LANG) : LANG_PROP R.

  Lemma plug_empty : forall t k, R.plug t (@R.empty k) = t.
  Proof.
    intros; auto.
  Qed.
  Hint Resolve plug_empty : prop.

  Lemma compose_empty : forall k1 k2 (c : R.context k1 k2), c = R.compose c R.empty.
  Proof.
    intros; induction c.
    - auto.
    - simpl; rewrite<- IHc; auto.
  Qed.
  Hint Resolve compose_empty : prop.

  Lemma plug_compose : forall k1 k2 k3 (c : R.context k1 k2) (c' : R.context k3 k1) 
                               (t : R.term), 
                           R.plug t (R.compose c c') = R.plug (R.plug t c) c'.
  Proof.
    intros ? ? ?; induction c; intros.
    - auto.
    - apply IHc.
  Qed.
  Hint Resolve plug_compose : prop.

End Lang_Prop.

Module RedRefSem (R : RED_REF_LANG) <: RED_REF_SEM R.R.

  Definition dec_term := R.dec_term.
  Definition dec_context := R.dec_context.
  Inductive dec : R.R.term -> forall {k1 k2}, R.R.context k1 k2 -> R.R.decomp k1 -> Prop :=
  | d_dec  : forall t {k1 k2} (c : R.R.context k1 k2) (r : R.R.redex k2),
               dec_term t k2 = R.R.in_red r -> 
               dec t c (R.R.d_red r c)
  | d_v    : forall t {k1 k2} (c : R.R.context k1 k2) (v : R.R.value k2) (d : R.R.decomp k1),
               dec_term t k2 = R.R.in_val v ->
               decctx v c d ->
               dec t c d
  | d_term : forall t t0 {k1 k2} (c : R.R.context k1 k2) ec (d : R.R.decomp k1),
               dec_term t k2 = R.R.in_term t0 ec ->
               dec t0 (R.R.ccons ec c) d ->
               dec t c d
  with decctx : forall {k2}, R.R.value k2 -> forall {k1}, R.R.context k1 k2 -> R.R.decomp k1 -> Prop :=
  | dc_end  : forall {k} (v : R.R.value k), decctx v (@R.R.empty k) (R.R.d_val v)
  | dc_dec  : forall ec {k2} (v : R.R.value (R.R.ckind_trans k2 ec)) 
                        {k1} (c : R.R.context k1 k2) (r : R.R.redex k2),
                dec_context ec k2 v = R.R.in_red r ->
                decctx v (R.R.ccons ec c) (R.R.d_red r c)
  | dc_val  : forall {k2} (v0 : R.R.value k2) ec   (v : R.R.value (R.R.ckind_trans k2 ec)) 
                     {k1} (c  : R.R.context k1 k2) (d : R.R.decomp k1),
                dec_context ec k2 v = R.R.in_val v0 ->
                decctx v0 c d ->
                decctx v (R.R.ccons ec c) d
  | dc_term : forall ec ec0 {k2} (v : R.R.value (R.R.ckind_trans k2 ec)) 
                            {k1} (c : R.R.context k1 k2) (t : R.R.term) (d : R.R.decomp k1),
                dec_context ec k2 v = R.R.in_term t ec0 ->
                dec t (R.R.ccons ec0 c) d ->
                decctx v (R.R.ccons ec c) d.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.
    
  Notation "a <| b" := (R.subterm_order a b) (at level 40, no associativity).
  Notation "k |~  a << b " := (R.ec_order k a b) (at level 40, no associativity).

  Definition dec_term_correct := R.dec_term_correct.

  Lemma sto_trans : forall t t0 t1, t <| t0 -> t0 <| t1 -> t <| t1.
  Proof with eauto.
    induction 1.
    - econstructor 2...
    - econstructor 2. 
      * eauto.
      * apply IHclos_trans_1n...
  Qed.

  Lemma plug_le_eq : forall k1 k2 (c : R.R.context k1 k2) t t0, R.R.plug t0 c = t -> 
                         t0 <| t \/ (c ~= @R.R.empty k1 /\ t = t0).
  Proof with eauto.
    intros k1 k2;
    induction c; intros.
    - simpl in H...
    - left; simpl in H. 
      destruct (IHc t (R.R.atom_plug t0 ec)). 
      * eauto.
      * apply t1n_trans with (y := R.R.atom_plug t0 ec).
        + econstructor... 
        + assumption. 
      * destruct H0. 
        subst; rewrite H1.
        do 2 econstructor...
  Qed.


  Lemma st_c : forall t0 t1, t0 <| t1 -> 
                   forall k1, exists k2 (c : R.R.context k1 k2), R.R.plug t0 c = t1.
  Proof with eauto.
    intros t0 t1 H k1;
    induction H; intros.
    - inversion H; subst. 
      exists (R.R.ckind_trans k1 ec).
      exists (R.R.ccons ec (@R.R.empty k1)).
      simpl...
    - destruct IHclos_trans_1n as [k2 [c H1]]. 
      inversion H.
      subst.
      exists (R.R.ckind_trans k2 ec).
      exists (R.R.ccons ec c)...
  Qed.

(*
  Definition value_one_step {k1} (v : R.R.value k1) {k2} (v0 : R.R.value k2) : Prop := 
      R.subterm_one_step (R.R.value_to_term v) (R.R.value_to_term v0).
  Definition value_order k := clos_trans_1n (R.R.value k) value_one_step.
    
  Notation "k |- a <v| b" := (@value_order k a b) (at level 40).
    
  Lemma wf_vo : forall {k}, well_founded (value_order k).
  Proof.
    intro k.
    apply wf_clos_trans_l. unfold value_one_step. apply wf_inverse_image. apply R.wf_st1.
  Qed.
*)
    (*Reserved Notation " a <v| b " (at level 40).

    Inductive value_order : R.R.value -> R.R.value -> Prop :=
    | vc_1 : forall v0 v1 ec (ATOM: R.R.atom_plug (R.R.value_to_term v0) ec = (R.R.value_to_term v1)), v0 <v| v1
    | vc_m : forall v0 v1 v2 ec (REC: v0 <v| v1) (ATOM: R.R.atom_plug (R.R.value_to_term v1) ec = (R.R.value_to_term v2)), v0 <v| v2
    where " a <v| b " := (value_order a b).

    Definition hp (v v0 : R.R.value) := (R.R.value_to_term v) <| (R.R.value_to_term v0).

    Lemma wf_vo : well_founded value_order.
    Proof with auto.
      apply wf_incl with hp.
      unfold inclusion; intros; induction H; [ econstructor | econstructor 2]; eauto; econstructor; eauto.
      apply wf_inverse_image; apply R.wf_sto.
    Qed.*)


(*
Lemma decctx_des : forall ec {k2} (v : R.R.value (R.R.ckind_trans k2 ec)) 
                             {k1} (c : R.R.context k1 k2) (d : R.R.decomp k1),
                             decctx v (R.R.ccons ec c) d ->

  (exists r, d = R.R.d_red r c /\ R.dec_context ec k2 v = R.R.in_red r) \/
  (exists v0, R.dec_context ec k2 v = R.R.in_val v0 /\ decctx v0 c d) \/
  (exists ec0 t, R.dec_context ec k2 v = R.R.in_term t ec0 /\
                 dec t (R.R.ccons ec0 c) d).
Proof.
intros.
dependent destruction H;
assert (H1 := xxx _ _ _ _ _ _ _ x0 x);

destruct H1 as (H1a,(H1b, H1c)); destruct H1a; destruct H1b; subst.

left; exists r; auto.

right; left; exists v0; auto.

right; right; exists ec1; exists t; auto.
Qed.
*)

    Include RED_LANG_Facts R.R.

    Lemma dec_val : forall k1 k2 (v : R.R.value k2) (c : R.R.context k1 k2) 
                                (d : R.R.decomp k1),

                        dec (R.R.value_to_term v) c d  ->  decctx v c d.

    Proof with eauto.
      intros k1 k2 v; remember (R.R.value_to_term v); revert k2 v Heqt.
      induction t using (well_founded_ind R.wf_sto); intros.
      subst.

      dependent destruction H0;
          unfold dec_term in *;
          assert (hh := R.dec_term_correct (R.R.value_to_term v) k2); rewrite H0 in hh.

      - symmetry in hh; contradiction (R.R.value_redex _ _ _ hh).

      - rewrite<- (R.R.value_to_term_injective _ _ _ hh)...

      - destruct (R.R.value_trivial _ v t0 _ (R.R.ccons ec R.R.empty)); 
            try solve [auto];
            destruct H2.

        * discriminateJM H3.

        * { clear H0; revert t0 H1 x hh H2.
          induction ec using (well_founded_ind (R.wf_eco k2)); intros.

          assert (decctx x (R.R.ccons ec c) d).
          + apply (H t0)... 
            do 2 econstructor...

          + { dependent destruction H3;
                assert (G1 := ccons_inj _ _ _ _ x1 x);
                subst; rec_subst G1;
                unfold dec_context in *;

                assert (gg := R.dec_context_correct ec k2 x0); rewrite H3 in gg.

            - contradiction (R.R.value_redex _ v r); symmetry; etransitivity...

            - assert (v0 = v).
              * apply (R.R.value_to_term_injective _ v0 v ); etransitivity...
              * subst...

            - destruct (R.R.value_trivial _ v t _ (R.R.ccons ec1 R.R.empty));
                  try solve [etransitivity; eauto];
                  destruct H2.
              * discriminateJM H5.
              * eapply (H0 ec1)...
                + destruct (R.dec_context_term_next _ _ _ _ _ H3)...
                + etransitivity... 
            }
          }
    Qed.


    Lemma val_dec : forall k1 k2 (v : R.R.value k2) (c : R.R.context k1 k2) 
                                (d : R.R.decomp k1),

                        decctx v c d -> dec (R.R.value_to_term v) c d.

    Proof with eauto.
      intros k1 k2 v; remember (R.R.value_to_term v); revert k2 v Heqt.
      induction t using (well_founded_ind R.wf_sto); intros.
      subst.

      remember (R.dec_term (R.R.value_to_term v) k2).
      assert (hh := R.dec_term_correct (R.R.value_to_term v) k2).
      destruct i; rewrite <- Heqi in hh.

      - symmetry in hh; contradiction (R.R.value_redex _ _ _ hh).

      - assert (H1 := R.R.value_to_term_injective _ _ _ hh); subst; econstructor...

      - symmetry in Heqi.
        apply (d_term _ _ _ _ _ Heqi).

        clear Heqi;
        destruct (R.R.value_trivial _ v t _ (R.R.ccons e R.R.empty));
            try solve [auto];
            destruct H1.

        * discriminateJM H2.

        * { revert e t hh x H1;
          induction e using (well_founded_ind (R.wf_eco k2)); intros.

          apply (H t) with (v := x).

          - do 2 econstructor...

          - auto.

          - remember (R.dec_context e _ x); assert (gg := R.dec_context_correct e _ x);
            destruct i; rewrite<- Heqi in gg; subst.

            * contradiction (R.R.value_redex _ v r); symmetry; etransitivity...

            * apply (dc_val v0)...
              assert (v0 = v).
              + apply (R.R.value_to_term_injective _ v0 v ); etransitivity...
              + subst...

            * { destruct (R.R.value_trivial _ v t0 _ (R.R.ccons e0 R.R.empty));
                  try solve [etransitivity; eauto];
                  destruct H2.

                - discriminateJM H3.

                - apply dc_term with (ec0:=e0) (t:=t0)...
                  apply (H1 e0) with (x := x0)...
                  * symmetry in Heqi;
                    destruct (R.dec_context_term_next _ _ _ _ _ Heqi)...
                  * etransitivity...
               }
            }
    Qed.

  Module RS : RED_SEM R.R with Definition dec := dec.
    Definition dec := dec.

    Module LP := Lang_Prop R.R.

    Lemma decompose : forall (t : R.R.term) (k1 : R.R.ckind), 
      (exists (v : R.R.value k1), t = R.R.value_to_term v) \/
      (exists k2 (r : R.R.redex k2) (c : R.R.context k1 k2), R.R.plug (R.R.redex_to_term r) c = t).

    Proof with eauto.
      induction t using (well_founded_ind R.wf_sto); intros.

      remember (R.dec_term t k1); assert (hh := R.dec_term_correct t k1);
      destruct i; rewrite <- Heqi in hh.

      - right; exists k1; exists r; exists (@R.R.empty k1)...

      - left; exists v...

      - destruct (H t0) with (k1 := R.R.ckind_trans k1 e) as [(v, Hv) | (k2, (r, (c, Hrc)))].
            repeat econstructor...

        * { subst t0; clear Heqi; generalize dependent v. 
          induction e using (well_founded_ind (R.wf_eco k1)); intros.

          remember (R.dec_context e _ v); assert (ht := R.dec_context_correct e _ v); 
          destruct i; rewrite <- Heqi in ht; rewrite hh in ht.

          - right; exists k1; exists r; exists (@R.R.empty k1)...

          - left; exists v0...

          - destruct (H t0) with (k1 := R.R.ckind_trans k1 e0) 
                              as [(v0, Hv) | (k2, (r, (c, Hrc)))].
            + repeat econstructor...

            + symmetry in Heqi; 
              destruct (R.dec_context_term_next _ _ _ _ _ Heqi) as (H1, _).

              subst t0.
              destruct (H0 e0 H1 v0 ht) as [(v1, Hv1) | (k2, (r, (c, Hrc)))].
              * left; exists v1...
              * right; exists k2; exists r; exists c...

            + right; exists k2; exists r; exists (R.R.compose c (R.R.ccons e0 R.R.empty)).
              subst t0; rewrite LP.plug_compose...
          }

        * right; exists k2; exists r; exists (R.R.compose c (R.R.ccons e R.R.empty)).
          subst t0; rewrite LP.plug_compose...
    Qed. 

    Lemma dec_redex_self_e : forall {k} (r : R.R.redex k), 

                dec (R.R.redex_to_term r) _ _ (R.R.empty) (R.R.d_red r R.R.empty).

    Proof with eauto.
      intros; 
      remember (dec_term (R.R.redex_to_term r) k).

      destruct i; unfold dec_term in Heqi;
          assert (hh := R.dec_term_correct (R.R.redex_to_term r) k);
          rewrite <- Heqi in hh; 
          simpl in hh.

      - apply R.R.redex_to_term_injective in hh; subst; constructor...

      - contradict hh;  apply R.R.value_redex.

      - symmetry in Heqi; assert (H := R.dec_term_term_top _ _ _ _ Heqi).
        econstructor 3. apply Heqi.
        destruct (R.R.redex_trivial _ r t _ (R.R.ccons e R.R.empty) hh) 
            as [(H1, H2) | (v, H1)].

        * discriminateJM H2. 

        * { subst t; clear H Heqi; generalize dependent v; generalize dependent e.
          induction e using (well_founded_ind (R.wf_eco k)); intros.

          apply val_dec.
          remember (R.dec_context e _ v); assert (ht := R.dec_context_correct e _ v);
          rewrite <- Heqi in ht.

          destruct i; simpl in ht.

          - rewrite hh in ht.
            apply R.R.redex_to_term_injective in ht; subst.
            constructor...

          - rewrite <- ht in hh; contradiction (R.R.value_redex _ _ _ hh).

          - econstructor 4. symmetry; apply Heqi.
            rewrite hh in ht; 
            destruct (R.R.redex_trivial _ r t _ (R.R.ccons e0 R.R.empty) ht) 
                as [(H4, H5) | (v1, H4)].
            * discriminateJM H5.
            * subst t; symmetry in Heqi.
              destruct (R.dec_context_term_next _ _ _ _ _ Heqi). 
              apply H...
          }
    Qed.

    Lemma dec_redex_self : forall {k1 k2} (r : R.R.redex k2) (c : R.R.context k1 k2), 
                               dec (R.R.redex_to_term r) _ _ c (R.R.d_red r c).
    Proof with eauto.
      intros;
      assert (hh := dec_redex_self_e r);
      generalize c.

      apply dec_Ind with

      (P  := fun t k1' k2' c0 d (H : dec t k1' k2' c0 d) => match d with
        | R.R.d_val v => True
        | R.R.d_red k' r' c1 => forall c : R.R.context k1 k1', 
                                dec t _ _ (R.R.compose c0 c) (R.R.d_red r' (R.R.compose c1 c))
      end)

      (P0 := fun k2' v k1' c0 d (H : @decctx k2' v k1' c0 d) => match d with
        | R.R.d_val v => True
        | R.R.d_red k' r' c1 => forall c : R.R.context k1 k1', 
                                decctx v (R.R.compose c0 c) (R.R.d_red r' (R.R.compose c1 c))
      end)

      (d0 := hh);
      
          intros; try destruct d; auto.

      - constructor...
      - econstructor...
      - econstructor 3... apply H.
      - constructor... 
      - econstructor...
      - econstructor 4... apply H.

    Qed.

    Lemma dec_correct : 
        forall t {k1 k2} c d, dec t k1 k2 c d -> R.R.decomp_to_term d = R.R.plug t c.
  
    Proof.
      induction 1 using dec_Ind with

      (P := fun t k1 k2 c d (H:dec t k1 k2 c d) => 
                 R.R.decomp_to_term d = R.R.plug t c)

      (P0:= fun k2 v k1 c d (H:decctx v c d) => 
                 R.R.decomp_to_term d = R.R.plug (R.R.value_to_term v) c);

      let final_tac := 
          try rewrite IHdec;
          rewrite <- hh;
          subst; auto
      in

      simpl; auto; solve
      [ unfold dec_term in e; 
        assert (hh := R.dec_term_correct t k2); 
        rewrite e in hh; 
        final_tac

      | unfold dec_context in e; 
        assert (hh := R.dec_context_correct ec _ v); 
        rewrite e in hh; 
        final_tac ].
    Qed.

    (*Module RF := RED_REF_LANG_Facts R LP.

    Lemma L : forall {k1 k2} (c1 c2 : R.R.context k1 k2) ec1 ec2, 
                  R.R.ckind_trans k2 ec1 = R.R.ckind_trans k2 ec2 -> 
                  R.R.ccons ec1 c1 ~= R.R.ccons ec2 c2 -> 
                  ec1 = ec2 /\ c1 = c2.
    Proof.
    intros.
    assert (H1 := JMeq_eq_depT _ _ _ _ _ _  H H0).
    inversion H1.
    dependent destruction H6.
    eauto.
    Qed.*)


(* REFACTOR *)
Require Import Eqdep.

Ltac injection_ccons H :=
match type of H with R.R.ccons ?ec1 ?c1 ~= R.R.ccons ?ec2 ?c2 => 
let H0 := fresh in 
assert (H0 : eq_dep _ _ _ (R.R.ccons ec1 c1) _ (R.R.ccons ec2 c2)); 
[ apply JMeq_eq_depT; eauto
| inversion H0; subst; 
match goal with 
H1 : existT _ _ _ = existT _ _ _ |- _ => 
let tmp := fresh in 
assert (tmp := H1); clear H1;
dependent destruction tmp
end;
clear H0 ]
end.

    Lemma dec_plug : 
        forall k1 k2 c k3 c0 t d, 
            ~ R.R.dead_ckind k2 -> dec (R.R.plug t c) k3 k1 c0 d -> 
            dec t k3 k2 (R.R.compose c c0) d.

    Proof with eauto.
      induction c; intros; simpl.
      - trivial.

      - apply IHc in H0; clear IHc;
        [ | apply (context_tail_liveness _ _ H) ].
        inversion H0; subst;
            unfold dec_term in H6; clear H0;
            assert (hh := R.dec_term_correct (R.R.atom_plug t ec) k2); 
            rewrite H6 in hh.

        * destruct (R.dec_term_red_empty _ _ _ H6 t _ (R.R.ccons ec R.R.empty))...
          discriminateJM H2.

        * destruct (R.dec_term_val_empty _ _ _ H6 t _ (R.R.ccons ec R.R.empty))...
          discriminateJM H3.

        * dependent destruction H2.
          destruct R.ec_order_comp_if with ec0 ec k2 as [H2 | [H2 | H2]].
              compute...
              eapply R.dec_term_ec_most_transitable...
              apply H.

          + contradiction (R.dec_term_term_top _ _ _ _ H6 ec).
          + symmetry in hh.
            destruct (R.elem_context_det _ _ _ _ _ H2 hh) as (v, H3); subst t1.
            {
                clear H6; generalize dependent v; generalize dependent ec0.
                induction ec0 using (well_founded_ind (R.wf_eco k2)); intros.
                
                assert (H3 := dec_val _ _ _ _ _ H7).
                dependent destruction H3;
                injection_ccons x.
                - contradiction (R.dec_context_red_bot _ _ _ _ H1 ec).
                - contradiction (R.dec_context_val_bot _ _ _ _ H1 ec).
                - assert (ht := R.dec_context_correct ec0 _ v).
                  unfold dec_context in H1; rewrite H1 in ht. 
                  rewrite <- hh in ht.
                  destruct (R.dec_context_term_next _ _ _ _ _ H1).
                  destruct R.ec_order_comp_if with ec2 ec k2 as [hq | [hq | hq]].
                      compute...
                      assert (H6 := R.ec_order_comp_fi _ _ _ H4); intuition.
                      assert (H6 := R.ec_order_comp_fi _ _ _ H2); intuition.
                      
                      * contradiction (H5 ec).
                      * symmetry in ht.
                        destruct (R.elem_context_det _ _ _ _ _ hq ht) as (v1, h4); subst t0.
                        apply H0 with ec2 v1...
                      * subst; assert (H8 := R.R.atom_plug_injective1 _ _ _ ht).
                        subst...
            }
          + subst; assert (H8 := R.R.atom_plug_injective1 _ _ _ hh).
            subst...
    Qed.


    Lemma dec_plug_rev : 
        forall k1 k2 c k3 c0 t d, 
            ~ R.R.dead_ckind k2 -> dec t k3 k2 (R.R.compose c c0) d -> 
            dec (R.R.plug t c) k3 k1 c0 d.

    Proof with eauto.
      induction c; intros; simpl.
      - trivial.

      - apply IHc; clear IHc.
        eapply context_tail_liveness...
        remember (R.dec_term (R.R.atom_plug t ec) k2) as i.
        destruct i;
          assert (hh := R.dec_term_correct (R.R.atom_plug t ec) k2);
          rewrite <- Heqi in hh.

        * symmetry in Heqi.
          destruct ( R.dec_term_red_empty _ _ _ Heqi t _ (R.R.ccons ec R.R.empty))...
          discriminateJM H2.

        * symmetry in Heqi.
          destruct (R.dec_term_val_empty _ _ _ Heqi t _ (R.R.ccons ec R.R.empty))...
          discriminateJM H2.

        * destruct (R.ec_order_comp_if e ec) with k2 as [H1 | [H1 | H1]].
              unfold R.R.ec_siblings...
              symmetry in Heqi.
              apply (R.dec_term_ec_most_transitable H Heqi).
              apply H.

          + symmetry in Heqi.
            contradict (R.dec_term_term_top _ _ _ _ Heqi _ H1).

          + symmetry in hh.
            destruct (R.elem_context_det _ _ _ _ _ H1 hh) as (v, H2); subst t0.
            econstructor 3; eauto.
            {
              clear H Heqi; generalize dependent v; generalize dependent e.
              induction e using (well_founded_ind (R.wf_eco k2)); intros.

              apply val_dec.
              remember (R.dec_context e _ v).
              destruct i;
                  symmetry in Heqi;
                  assert (ht := R.dec_context_correct e _ v); 
                  rewrite Heqi in ht.

              - contradiction (R.dec_context_red_bot _ _ _ _ Heqi ec).
              - contradiction (R.dec_context_val_bot _ _ _ _ Heqi ec).
              - destruct (R.dec_context_term_next _ _ _ _ _ Heqi) as (H3, H4).
                econstructor 4; eauto; rewrite <- hh in ht.
                destruct R.ec_order_comp_if with e0 ec k2 as [H5 | [H5 | H5]].
                    compute...
                    destruct R.ec_order_comp_fi with e0 e k2 as (?, (?, ?))...
                    destruct R.ec_order_comp_fi with ec e k2 as (?, (?, ?))...
                * contradiction (H4 ec H1).
                * symmetry in ht; clear H4. 
                  destruct (R.elem_context_det _ _ _ _ _ H5 ht) as (v0, H6); subst t0.
                  apply H...
                * subst.
                  assert (H5 := R.R.atom_plug_injective1 _ _ _ ht).
                  subst...
            }
        + subst.
          assert (H5 := R.R.atom_plug_injective1 _ _ _ hh).
          subst.
          econstructor 3...
    Qed.
(*
Lemma des_decctx : forall k2 v k1 c d P, @decctx k2 v k1 c d -> 

(k2 = k1 -> c ~= @R.R.empty k2 -> d ~= R.R.d_val v -> P) ->

(forall k3 ec (_  : k2 = R.R.ckind_trans k3 ec) 
              (v0 : R.R.value (R.R.ckind_trans k3 ec))
              (_  : v ~= v0)
              (c0 : R.R.context k1 k3)
              (_  : c ~= R.R.ccons ec c0)
              (r  : R.R.redex k3)
              (_  : d ~= R.R.d_red r c0)
              (_  : dec_context ec k3 v0 = R.R.in_red r), P) ->

(forall k3 (v1 : R.R.value k3) 
        ec (v0 : R.R.value (R.R.ckind_trans k3 ec))
           (_ : v ~=v0)
              (c  : R.R.context k1 k2) (d : R.R.decomp k1),
                dec_context ec k2 v = R.R.in_val v0 ->
                decctx v0 c d ->
                decctx v (R.R.ccons ec c) d
  | dc_term : forall ec ec0 {k2} (v : R.R.value (R.R.ckind_trans k2 ec)) 
                            {k1} (c : R.R.context k1 k2) (t : R.R.term) (d : R.R.decomp k1),
                dec_context ec k2 v = R.R.in_term t ec0 ->
                dec t (R.R.ccons ec0 c) d ->
                decctx v (R.R.ccons ec c) d.

refine (match H3 as H3' in @decctx k2' v0 k1' c3 d0 
return 
forall (Hk2 : (R.R.ckind_trans k2 ec0) = k2')
(Hk1 : k3 = k1'),
match Hk1 in _ = k1'' return R.R.context k1'' k2'  -> Prop with eq_refl =>
fun c3 => match Hk2 in _ = k2'' return (*R.R.value k2'' ->*) R.R.context k3 k2'' -> Prop with eq_refl =>
fun c3 => forall (Hv0 : v ~= v0) (Hc3 : R.R.ccons ec0 (R.R.compose c c0) = c3),
dec t k3 (R.R.ckind_trans k2 ec) (R.R.ccons ec (R.R.compose c c0)) d 
end
 c3
end
c3
with
  | dc_end k' v' => _
  | dc_dec ec' k2' v' k1' c' r' H' =>  _
  | dc_val k2' v0' ec' v' k1' c' d' H' H0' => _
  | dc_term ec' ec0' k2' v' k1' c' t' d' H' H0' => _
  end eq_refl eq_refl JMeq_refl eq_refl);
  intros.*)

(* Require Import Eqdep.
            refine (match H3 as H3' in @decctx k2' v0 k1' c3 d0 
return 
forall (Hk2 : (R.R.ckind_trans k2 ec0) = k2')
(Hk1 : k3 = k1'),
match Hk1 in _ = k1'' return R.R.context k1'' k2'  -> Prop with eq_refl =>
fun c3 => match Hk2 in _ = k2'' return (*R.R.value k2'' ->*) R.R.context k3 k2'' -> Prop with eq_refl =>
fun c3 => forall (Hv0 : v ~= v0) (Hc3 : R.R.ccons ec0 (R.R.compose c c0) = c3),
dec t k3 (R.R.ckind_trans k2 ec) (R.R.ccons ec (R.R.compose c c0)) d 
end
 c3
end
c3
with
  | dc_end k' v' => _
  | dc_dec ec' k2' v' k1' c' r' H' =>  _
  | dc_val k2' v0' ec' v' k1' c' d' H' H0' => _
  | dc_term ec' ec0' k2' v' k1' c' t' d' H' H0' => _
  end eq_refl eq_refl JMeq_refl eq_refl);
  intros. Focus 3. destruct Hk1. (*remember v'.*) remember (R.R.ccons ec' c'). (*assert (eq_dep _ _ _ v0 _ v'. subst...*) assert (eq_dep _ _ _ c1 _ (R.R.ccons ec' c')). subst... clear Heqc1. destruct Hk2. intros. subst. 
inversion H1. subst. dependent destruction H10. clear H1 H5 H6. subst.
discriminate Hc3. *)

  Inductive decempty : R.R.term -> forall {k}, R.R.decomp k -> Prop :=
  | d_intro : forall (t : R.R.term) {k} (d : R.R.decomp k), dec t _ _(@R.R.empty k) d -> decempty t d.

  Inductive iter : forall {k}, R.R.decomp k -> R.R.value k -> Prop :=
  | i_val : forall {k} (v : R.R.value k), iter (R.R.d_val v) v
  | i_red : forall {k} (r : R.R.redex k) t {k'} (c : R.R.context k' k) d v,
              R.R.contract r = Some t -> decempty (R.R.plug t c) d -> iter d v ->
              iter (R.R.d_red r c) v.

  Inductive eval : R.R.term -> forall {k}, R.R.value k -> Prop :=
  | e_intro : forall t {k} (d : R.R.decomp k) v, decempty t d -> iter d v -> eval t v.

  End RS.

  Definition dec_context_correct := R.dec_context_correct.

  Lemma dec_val_self : forall k2 (v : R.R.value k2) k1 (c : R.R.context k1 k2) d, 
                           dec (R.R.value_to_term v) c d <-> decctx v c d.
  Proof.
    split; [apply dec_val | apply val_dec]; auto.
  Qed.

End RedRefSem.
