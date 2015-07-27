Require Import Program.
(*Require Import Setoid.*)
Require Export refocusing_signatures.
Require Import refocusing_lang_facts.
Require Import Wellfounded.Inclusion.
Require Import Wellfounded.Inverse_Image.


Module RedRefSem (R : RED_REF_LANG) <: RED_REF_SEM R.R.

  Import R.R.
  Import R.
  Module RRF := RED_LANG_Facts R.R.
  Import RRF.

  Inductive dec : term -> forall {k1 k2}, context k1 k2 -> decomp k1 -> Prop :=
  | d_dec  : forall t {k1 k2} (c : context k1 k2) {r},
               dec_term t k2 = in_red r -> 
               dec t c (d_red r c)
  | d_v    : forall t {k1 k2} {c : context k1 k2} {v d},
               dec_term t k2 = in_val v ->
               decctx v c d ->
               dec t c d
  | d_term : forall t {t0 k1 k2} {c : context k1 k2} {ec d},
               dec_term t k2 = in_term t0 ec ->
               dec t0 (ec=:c) d ->
               dec t c d

  with decctx : forall {k2}, value k2 -> forall {k1}, context k1 k2 -> decomp k1 -> Prop :=
  | dc_end  : forall {k} (v : value k), 
                ~ dead_ckind k ->
                decctx v [_] (d_val v)
  | dc_dec  : forall ec {k2} (v : value (k2+>ec)) {k1} (c : context k1 k2) {r},
                dec_context ec k2 v = in_red r ->
                decctx v (ec=:c) (d_red r c)
  | dc_val  : forall {k2} {v0 : value k2} ec (v : value (k2+>ec)) 
                     {k1} {c  : context k1 k2} {d},
                dec_context ec k2 v = in_val v0 ->
                decctx v0 c d ->
                decctx v (ec=:c) d
  | dc_term : forall ec {ec0 k2} (v : value (k2+>ec)) 
                            {k1} {c : context k1 k2} {t d},
                dec_context ec k2 v = in_term t ec0 ->
                dec t (ec0=:c) d ->
                decctx v (ec=:c) d.

  Scheme dec_Ind := Induction for dec Sort Prop
   with decctx_Ind := Induction for decctx Sort Prop.
(*    
  Notation "a <| b" := (R.subterm_order a b) (at level 40, no associativity).
  Notation "k |~  a << b " := (R.ec_order k a b) (at level 40, no associativity).
*)


  Lemma sto_trans : forall t t0 t1,  t <| t0  ->  t0 <| t1  ->  t <| t1.
  Proof with eauto.
    induction 1.
    - econstructor 2...
    - econstructor 2. 
      + eauto.
      + apply IHclos_trans_1n...
  Qed.


  Lemma plug_le_eq : forall {k1 k2} (c : context k1 k2) t t0, c[t0] = t -> 
                         t0 <| t \/ (c ~= @empty k1 /\ t = t0).
  Proof with eauto.
    intros k1 k2;
    induction c; intros.
    - simpl in H...
    - left; simpl in H.
      destruct (IHc t ec:[t0]). 
      + eauto.
      + apply t1n_trans with (y := ec:[t0]).
        * econstructor... 
        * assumption. 
      + destruct H0. 
        subst; rewrite H1.
        do 2 econstructor...
  Qed.


  Lemma st_c : forall t0 t1, t0 <| t1 -> 
                   forall k1, exists k2 (c : context k1 k2), c[t0] = t1.
  Proof with eauto.
    intros t0 t1 H k1;
    induction H; intros.
    - inversion H; subst.
      exists (k1+>ec); eexists (ec=:[_]).
      simpl...
    - destruct IHclos_trans_1n as (k2, (c, H1)). 
      inversion H.
      subst.
      exists (k2+>ec); exists (ec=:c)...
  Qed.


  Lemma dec_not_dead : forall {t k1 k2} {c : context k1 k2} {d},
                           dec t c d -> ~ dead_ckind k2.
  Proof.
    intros; intro.
    assert (hh := dec_term_from_dead t k2 H0).
    destruct H;
    solve
    [   rewrite H in hh;
        discriminate hh ].
  Qed.


  Lemma decctx_not_dead : forall {k1 k2} {c : context k1 k2} {v d},
                              decctx v c d -> ~ dead_ckind k2.
  Proof with auto.
    intros; intro.
    destruct H;
    solve 
    [   intuition
    |   assert (hh := dec_context_from_dead ec k2 v H0);
        rewrite H in hh;
        discriminate hh ].
  Qed.


  Lemma dec_context_not_dead : 
      forall ec1 k v ec2 t, ~ dead_ckind (k+>ec1) -> 
          dec_context ec1 k v = in_term t ec2 -> ~ dead_ckind (k+>ec2).
  Proof.
    intros.
    destruct (dec_context_term_next _ _ _ H0) as (H1, _).
    apply (ec_order_comp_fi _ _ _ _ H1).
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

  Lemma dec_val : forall {k2} (v : value k2) {k1} {c : context k1 k2} {d},
                      dec v c d -> decctx v c d.
  Proof with eauto.
    intros k2 v k1; remember (value_to_term v) as t; revert k2 v Heqt.
    induction t using (well_founded_ind wf_sto); intros; subst.

    dependent destruction H0;
        assert (hh := dec_term_correct v k2); rewrite H0 in hh.

    - contradiction (value_redex _ _ hh).

    - rewrite (value_to_term_injective _ _ hh)...

    - destruct (value_trivial v t0 _ (ec=:[_])); auto;
          try solve [eapply dec_term_next_alive; eassumption];
          destruct H2.

      + discriminateJM H3.

      + { clear H0; revert t0 H1 x hh H2.
        induction ec using (well_founded_ind (wf_eco k2 v)); intros.

        assert (decctx x (ec=:c) d).
          { apply (H t0)... do 2 econstructor... }

        dependent destruction H3;
            assert (G1 := ccons_inj _ _ _ _ x1 x);
            subst; rec_subst G1;

            assert (gg := dec_context_correct ec k2 x0); rewrite H3 in gg.

        - contradiction (value_redex v r); congruence.

        - assert (v0 = v).
            { apply (value_to_term_injective v0 v); congruence. }
          subst...

        - assert (~ dead_ckind (k2+>ec1)).
          {
              destruct ec_order_comp_fi with k2 v ec1 ec as (?, (?, (?, ?)))...
              - rewrite hh; eapply dec_context_term_next...
          }

          destruct (value_trivial v t _ (ec1=:[_])); auto;
              try solve 
              [ simpl; congruence];
              destruct H5.
          + discriminateJM H6.
          + eapply (H0 ec1); eauto.
            * rewrite hh; apply (dec_context_term_next _ _ _ H3).
            * congruence.
        }
  Qed.


  Lemma val_dec : forall {k2} {v : value k2} {k1} {c : context k1 k2} {d},
                      decctx v c d -> dec v c d.
  Proof with eauto.
    intros k2 v k1; remember (value_to_term v); revert k2 v Heqt.
    induction t using (well_founded_ind wf_sto); intros; subst.

    remember (dec_term v k2);
    assert (hh := dec_term_correct v k2);
    destruct i; rewrite <- Heqi in hh; symmetry in Heqi.

    - contradict (value_redex _ _ hh).

    - assert (H1 := value_to_term_injective _ _ hh); subst; econstructor...

    - apply (d_term _ Heqi).

      assert (~ dead_ckind (k2+>e)) as Hndk.
        { eapply dec_term_next_alive... }
      destruct (value_trivial v t _ (e=:[_]));
          try solve [auto];
          destruct H1.

      + discriminateJM H2.

      + { clear Heqi; revert e t hh Hndk x H1.
        induction e using (well_founded_ind (wf_eco k2 v)); intros.

        apply (H t) with (v := x)...
          { do 2 econstructor... }
        remember (dec_context e _ x) as i.
        assert (gg := dec_context_correct e _ x);
        destruct i; rewrite <- Heqi in gg; subst;
        symmetry in Heqi.

        - contradiction (value_redex v r); congruence.

        - eapply dc_val...
          assert (v0 = v).
          + apply (value_to_term_injective v0 v); congruence.
          + subst...

        - assert (~ dead_ckind (k2+>e0)).
          {
              destruct ec_order_comp_fi with k2 v e0 e as (?, (?, (?, ?)))...
              - rewrite hh; eapply dec_context_term_next...
          }

          destruct (value_trivial v t0 _ (e0=:[_]));
              try solve [simpl; congruence];
              destruct H3.

          + discriminateJM H4.

          + apply dc_term with e0 t0...
            apply (H1 e0) with x0...
            * rewrite hh; apply (dec_context_term_next _ _ _ Heqi).
            * congruence.

        - intuition.
      }

    - contradiction (decctx_not_dead H0).
  Qed.


  Module RS : RED_SEM R.R with Definition dec := dec.

    Lemma decompose : forall (t : term) k1, ~ dead_ckind k1 ->
      (exists (v : value k1), t = v) \/
      (exists k2 (r : redex k2) (c : context k1 k2), t = c[r]).
    Proof with eauto.
      induction t using (well_founded_ind wf_sto); intros.

      remember (dec_term t k1); assert (hh := dec_term_correct t k1);
      symmetry in Heqi;
      destruct i; rewrite Heqi in hh.

      - right; exists k1; exists r; eexists [_]...

      - left; exists v...

      - destruct (H t0) with (k1 := k1+>e) as [(v, Hv) | (k2, (r, (c, Hrc)))].
            repeat econstructor...
            eapply dec_term_next_alive... 

        * { subst t0.
          assert (~ dead_ckind (k1+>e)) as Hndk.
            { eapply dec_term_next_alive... } 
          clear Heqi; generalize dependent v.
          induction e using (well_founded_ind (wf_eco k1 t)); intros.

          remember (dec_context e _ v); assert (ht := dec_context_correct e _ v); 
          destruct i; rewrite <- Heqi in ht; try rewrite <- hh in ht.

          - right; exists k1; exists r; eexists [_]...

          - left; exists v0...

          - destruct (H t0) with (k1 := k1+>e0) as [(v0, Hv) | (k2, (r, (c, Hrc)))].
                repeat econstructor...
                eapply dec_context_not_dead...

            + symmetry in Heqi.
              destruct (dec_context_term_next _ _ _ Heqi) as (H2, _).

              subst t0.
              assert (~ dead_ckind (k1+>e0)) as Hndk2.
                { eapply dec_context_not_dead... }
              rewrite <- hh in H2.
              destruct (H1 e0 H2 Hndk2 v0 ht) as [(v1, Hv1) | (k2, (r, (c, Hrc)))].
              * left; exists v1...
              * right; exists k2; exists r; exists c...

            + right; exists k2; exists r; exists (c~+e0=:[_]).
              subst t0; rewrite plug_compose...

          - intuition. 
          }

        * right; exists k2; exists r; exists (c~+(e=:[_])).
          subst t0; rewrite plug_compose...

      - intuition.
    Qed. 


    Lemma dec_redex_self_e : forall {k} (r : redex k), dec r [_] (d_red r [_]).
    Proof with eauto.
      intros; 
      remember (dec_term r k).
      assert (~ dead_ckind k).
        { eapply proper_death2... apply [_]. }

      destruct i;
          assert (hh := dec_term_correct r k);
          rewrite <- Heqi in hh; 
          simpl in hh; try symmetry in hh.

      - apply redex_to_term_injective in hh; subst; constructor...

      - contradict hh; apply value_redex.

      - symmetry in Heqi; assert (H0 := dec_term_term_top _ _ Heqi).
        assert (~ dead_ckind (k+>e)) as Hndk.
          { eapply dec_term_next_alive... } 
        econstructor 3...
        destruct (redex_trivial r t _ (e=:[_]) hh) as [(H1, H2) | (v, H1)]...

        * discriminateJM H2. 

        * { subst t.
          clear H0 Heqi; generalize dependent v; generalize dependent e.
          induction e using (well_founded_ind (wf_eco k r)); intros.

          apply val_dec.
          remember (dec_context e _ v); assert (ht := dec_context_correct e _ v);
          rewrite <- Heqi in ht; symmetry in Heqi.

          destruct i; simpl in ht.

          - rewrite hh in ht.
            apply redex_to_term_injective in ht; subst.
            constructor...

          - rewrite ht in hh; contradiction (value_redex _ _ hh).

          - econstructor 4...
            rewrite ht in hh.
            assert (~ dead_ckind (k+>e0)).
              { eapply dec_context_not_dead... }
            destruct (redex_trivial r t _ (e0=:[_]) hh) as [(H4, H5) | (v1, H4)]...
            + discriminateJM H5.
            + subst t.
              destruct (dec_context_term_next _ _ _ Heqi). 
              apply H0...
              * congruence.

          - intuition. 
          }

      - intuition.
    Qed.


    Lemma dec_redex_self : forall {k2} (r : redex k2) {k1} (c : context k1 k2), 
                               dec r c (d_red r c).
    Proof with eauto.
      intros;
      assert (hh := dec_redex_self_e r);
      generalize c.

      apply dec_Ind with

      (P  := fun t k1' k2' c0 d (_ : dec t c0 d) => 
      match d with
        | d_val v => True
        | d_red k' r' c1 => forall (c : context k1 k1'), dec t (c0~+c) (d_red r' (c1~+c))
      end)

      (P0 := fun k2' v k1' c0 d (_ : decctx v c0 d) => 
      match d with
        | d_val v => True
        | d_red k' r' c1 => forall (c : context k1 k1'), decctx v (c0~+c) (d_red r' (c1~+c))
      end)

      (d0 := hh);
      
          intros;
          try destruct d;
          auto.

      - constructor...
      - econstructor...
      - econstructor 3...
      - constructor... 
      - econstructor...
      - econstructor 4...
    Qed.


    Lemma dec_correct : 
        forall t {k1 k2} (c : context k1 k2) d, dec t c d -> c[t] = d.
    Proof.
      induction 1 using dec_Ind with
      (P := fun t _ _ c d (_ : dec t c d)     => c[t] = d)
      (P0:= fun _ v _ c d (_ : decctx v c d)  => c[v] = d);

      simpl; auto;
      match goal with
      | _ : dec_term ?t ?k2 = _      |- _ => assert (hh := dec_term_correct t k2)
      | _ : dec_context ?ec _ ?v = _ |- _ => assert (hh := dec_context_correct ec _ v)
      end;
      rewrite e in hh; simpl in *; 
      congruence.
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


    Lemma dec_plug : forall {k1 k2} (c : context k1 k2) {k3} (c0 : context k3 k1) t d, 
                         ~ dead_ckind k2 -> dec c[t] c0 d -> dec t (c~+c0) d.
    Proof with eauto.
      induction c; intros; simpl.
      - trivial.

      - apply IHc in H0; clear IHc;
        [ | apply (context_tail_liveness _ _ H) ].
        inversion H0; subst;
            clear H0;
            assert (hh := dec_term_correct (ec:[t]) k2); 
            rewrite H6 in hh.

        + destruct (dec_term_red_empty _ _ H6 t _ (ec=:[_]))...
          discriminateJM H2.

        + destruct (dec_term_val_empty _ _ H6 t _ (ec=:[_]))...
          discriminateJM H3.

        + dependent destruction H2.
          destruct ec_order_comp_if with ec:[t] ec0 ec k2 as [H2 | [H2 | H2]].
              compute...
              compute...
              eapply dec_term_next_alive...
              apply H.

          * contradiction (dec_term_term_top _ _ H6 ec).
          * destruct (elem_context_det _ _ hh _ _ H2) as (v, H3)...
            subst t1.
            {
                clear H6; generalize dependent v; generalize dependent ec0.
                induction ec0 using (well_founded_ind (wf_eco k2 ec:[t])); intros.
                
                assert (H3 := dec_val _ H7).
                dependent destruction H3;
                inversion_ccons x.
                - rewrite hh in H2; 
                  contradiction (dec_context_red_bot _ _ _ H1 _ H2).
                - rewrite hh in H2; 
                  contradiction (dec_context_val_bot _ _ _ H1 _ H2).
                - assert (ht := dec_context_correct ec0 _ v).
                  rewrite H1 in ht.
                  rewrite <- hh in ht.
                  destruct (dec_context_term_next _ _ _ H1).
                  destruct ec_order_comp_if with ec:[t] ec2 ec k2 as [H6 | [H6 | H6]].
                      compute...
                      compute...
                      assert (H6 := ec_order_comp_fi _ _ _ _ H4); intuition.
                      assert (H6 := ec_order_comp_fi _ _ _ _ H2); intuition.

                  + contradiction (H5 ec); rewrite <- hh...
                  + destruct (elem_context_det _ _ ht _ _ H6) as (v1, h4)...
                    subst t0.
                    apply H0 with ec2 v1...
                      { congruence. }
                  + subst; assert (H8 := atom_plug_injective1 _ ht).
                    subst...
            }

          * subst; assert (H8 := atom_plug_injective1 _ hh).
            subst...
    Qed.


    Lemma dec_plug_rev : forall {k1 k2} (c : context k1 k2) {k3} (c0 : context k3 k1) t d, 
                             ~ dead_ckind k2 -> dec t (c~+c0) d -> dec c[t] c0 d.
    Proof with eauto.
      induction c; intros; simpl.
      - trivial.

      - apply IHc; clear IHc.
        eapply context_tail_liveness...
        remember (dec_term ec:[t] k2) as i.
        destruct i;
        assert (hh := dec_term_correct (atom_plug t ec) k2);
        rewrite <- Heqi in hh;
        symmetry in Heqi.

        + destruct (dec_term_red_empty _ _ Heqi t _ (ec=:[_]))...
          discriminateJM H2.

        + destruct (dec_term_val_empty _ _ Heqi t _ (ec=:[_]))...
          discriminateJM H2.

        + destruct ec_order_comp_if with ec:[t] e ec k2 as [H1 | [H1 | H1]].
              compute...
              compute...
              eapply dec_term_next_alive...
              assumption.

          * contradict (dec_term_term_top _ _ Heqi _ H1).

          * destruct (elem_context_det _ _ hh _ _ H1) as (v, H2)...
            subst t0.
            econstructor 3; eauto.
            {
              clear H Heqi; generalize dependent v; generalize dependent e.
              induction e using (well_founded_ind (wf_eco k2 ec:[t])); intros.

              apply val_dec.
              remember (dec_context e _ v).
              destruct i;
                  symmetry in Heqi;
                  assert (ht := dec_context_correct e _ v); 
                  rewrite Heqi in ht.

              - rewrite hh in H1;
                contradiction (dec_context_red_bot _ _ _ Heqi _ H1).
              - rewrite hh in H1;
                contradiction (dec_context_val_bot _ _ _ Heqi _ H1).
              - destruct (dec_context_term_next _ _ _ Heqi) as (H3, H4).
                econstructor 4...
                rewrite <- hh in ht.
                destruct ec_order_comp_if with ec:[t] e0 ec k2 as [H5 | [H5 | H5]].
                    compute...
                    compute...
                    apply (ec_order_comp_fi _ _ _ _ H3).
                    apply (ec_order_comp_fi _ _ _ _ H1).

                + rewrite hh in H1; 
                  contradiction (H4 ec H1). 
                  congruence.
                + destruct (elem_context_det _ _ ht _ _ H5) as (v0, H6)...
                  subst t0.
                  apply H...
                    { congruence. }
                + subst.
                  assert (H5 := atom_plug_injective1 _ ht).
                  subst...

              - contradict ht.
                eapply ec_order_comp_fi...
            }

          * subst.
            assert (H5 := atom_plug_injective1 _ hh).
            subst.
            econstructor 3...

        + contradict H...
          apply ckind_death_propagation...
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


  Inductive decempty : term -> forall {k}, decomp k -> Prop :=
  | d_intro : forall {t k} {d : decomp k}, dec t [_] d -> decempty t d.

  Inductive iter : forall {k}, decomp k -> value k -> Prop :=
  | i_val : forall {k} (v : value k), iter (d_val v) v
  | i_red : forall {k2} (r : redex k2) {t k1} (c : context k1 k2) {d v},
              contract r = Some t -> decempty c[t] d -> iter d v ->
              iter (d_red r c) v.

  Inductive eval : term -> forall {k}, value k -> Prop :=
  | e_intro : forall {t k} {d : decomp k} {v}, decempty t d -> iter d v -> eval t v.


  Definition dec := dec.

  End RS.


  Lemma dec_val_self : forall {k2} (v : value k2) {k1} (c : context k1 k2) d, 
                           dec v c d <-> decctx v c d.
  Proof.
    split; [apply dec_val | apply val_dec].
  Qed.

  Definition dec_term    := R.dec_term.
  Definition dec_context := R.dec_context.

  Definition dec_term_correct    := R.dec_term_correct.
  Definition dec_context_correct := R.dec_context_correct.

End RedRefSem.


Module Red_Sem_Proper (R : RED_LANG) (RS : RED_REF_SEM R) : RED_SEM_PROPER R RS.RS.

  Import R.
  Import RS.RS.
  Import RS.
  Module RLF := RED_LANG_Facts R.
  Import RLF.


  Lemma dec_is_function : forall {t k} {d d0 : decomp k}, 
                              decempty t d -> decempty t d0 -> d = d0.
  Proof.
    intros t k d d0 DE DE0.
    dependent destruction DE; dependent destruction DE0.

    induction H using dec_Ind with 
    (P := fun t _ _ c d _ => 
              forall d0, dec t c d0    -> d = d0)
    (P0 := fun _ v _ c d _ => 
              forall d0, decctx v c d0 -> d = d0);

    intros;

    (* automated cases *)
    match goal with

    | [ RD : (dec ?t ?c ?d), DT : (dec_term ?t ?k = _) |- _ ] => 
             inversion RD; dep_subst; 
             try match goal with DT2 : (dec_term ?t ?k = _) |- _ => 
                     rewrite DT2 in DT; inversion DT end

    | [ RC : (decctx ?v (?ec=:?c) ?d), DC : (dec_context ?ec ?k ?v = _) |- _ ] => 
             dependent_destruction2 RC; inversion_ccons x; do 2 dep_subst;
             try match goal with DC2 : (dec_context ?ec' ?k' ?v' = _) |- _ => 
                     rewrite DC2 in DC; inversion DC end

    | [ RC : (decctx ?v [_] ?d) |- _] => 
             dependent_destruction2 RC

    end; 

    subst; eauto.
  Qed.
  Hint Resolve dec_is_function : prop.


  Lemma iter_is_function : forall {k} {d : decomp k} {v v0}, 
                               iter d v -> iter d v0 -> v = v0.
  Proof with eauto with prop.
    induction 1; intros.
    - dependent destruction H...
    - dependent destruction H2; subst. 
      rewrite H2 in H; inversion H; subst.
      apply IHiter.
      cutrewrite (d = d0)...
  Qed.
  Hint Resolve iter_is_function : prop.


  Lemma eval_is_function : forall {t k} {v v0 : value k}, 
                              eval t v -> eval t v0 -> v = v0.
  Proof with eauto with prop.
    induction 1; intros.
    - dependent destruction H1.
      cutrewrite (d = d0) in H0...
  Qed.


  Lemma dec_correct : forall {t k1 k2} {c : context k1 k2} {d}, 
                          dec t c d -> decomp_to_term d = c[t].
  Proof.
    induction 1 using dec_Ind with
    (P := fun t _ _ c d (H : dec t c d) => 
              decomp_to_term d = c[t])
    (P0:= fun P_ v _ c d (H:RS.decctx v c d) => 
              decomp_to_term d = c[v]);
    simpl; auto;

    try solve 
    [ assert (hh := dec_term_correct t k2); rewrite e in hh; simpl in hh; 
      try rewrite IHdec; subst; auto
    | assert (hh := dec_context_correct ec k2 v); rewrite e in hh; simpl in hh; 
      try rewrite IHdec;
      try (contradiction hh); 
      rewrite hh; auto ].
  Qed.


  Lemma dec_total : forall t k, ~ dead_ckind k -> exists (d : decomp k), decempty t d.
  Proof with auto.
    intros t k H.
    destruct (decompose t k H) as [(v, Hv) | (k', (r, (c, Hp)))]; intros; subst t.
    - exists (d_val v); constructor; rewrite dec_val_self; constructor...
    - exists (d_red r c); constructor; apply dec_plug_rev.
        { apply (proper_death2 _ _ [_] r). }
      rewrite <- compose_empty;
      apply dec_redex_self.
  Qed.


  Lemma unique_decomposition :
 
      forall (t : term) k1, ~ dead_ckind k1 ->

          (exists v : value k1, t = v) \/ 

          (exists k2 (r : redex k2) (c : context k1 k2),  t = c[r] /\ 
	      forall k2' (r0 : redex k2') (c0 : context k1 k2'), 
                  t = c0[r0] -> k2' = k2 /\ r ~= r0 /\ c ~= c0).

  Proof with eauto.
    intros.
    destruct (decompose t k1 H) as [(v, H0) | (k', (r, (c, H0)))]; intros.
    - left; exists v...
    - right; exists k' r; exists c; split.
      + congruence.
      + intros.
        assert (decempty t (d_red r c) /\ decempty t (d_red r0 c0)).
        { split;
          constructor; 
          [rewrite H0 | rewrite H1]; 
          apply dec_plug_rev;
          solve
          [ apply (proper_death2 _ _ [_]); auto
          | rewrite <- compose_empty; apply dec_redex_self ]. 
        }
        destruct H2.
        assert (hh := dec_is_function H2 H3); dependent destruction hh.
        intuition.
  Qed.

End Red_Sem_Proper.



Module PreAbstractMachine (R : RED_LANG) (RS : RED_REF_SEM R) <: PRE_ABSTRACT_MACHINE R.

  Import R.
  Module RF := RED_LANG_Facts R.
  Import RF.
  Import RS.


  (** A decomposition function specified in terms of the atomic functions above *)
  Inductive dec : term -> forall {k1 k2}, context k1 k2 -> decomp k1 -> Prop :=
  | d_dec  : forall t {k1 k2} (c : context k1 k2) {r},
               dec_term t k2 = in_red r -> 
               dec t c (d_red r c)
  | d_v    : forall t {k1 k2} {c : context k1 k2} {v d},
               dec_term t k2 = in_val v ->
               decctx v c d ->
               dec t c d
  | d_term : forall t {t0 k1 k2} {c : context k1 k2} {ec d},
               dec_term t k2 = in_term t0 ec ->
               dec t0 (ec=:c) d ->
               dec t c d

  with decctx : forall {k2}, value k2 -> forall {k1}, context k1 k2 -> decomp k1 -> Prop :=
  | dc_end  : forall {k} (v : value k), 
                ~ dead_ckind k ->
                decctx v [_] (d_val v)
  | dc_dec  : forall ec {k2} (v : value (k2+>ec)) {k1} (c : context k1 k2) {r},
                dec_context ec k2 v = in_red r ->
                decctx v (ec=:c) (d_red r c)
  | dc_val  : forall {k2} {v0 : value k2} ec (v : value (k2+>ec)) 
                     {k1} {c  : context k1 k2} {d},
                dec_context ec k2 v = in_val v0 ->
                decctx v0 c d ->
                decctx v (ec=:c) d
  | dc_term : forall ec {ec0 k2} (v : value (k2+>ec)) 
                            {k1} {c : context k1 k2} {t d},
                dec_context ec k2 v = in_term t ec0 ->
                dec t (ec0=:c) d ->
                decctx v (ec=:c) d.

  Scheme dec_Ind := Induction for dec Sort Prop
    with decctx_Ind := Induction for decctx Sort Prop.

  Inductive iter : forall {k}, decomp k -> value k -> Prop :=
  | i_val : forall {k} (v : value k), iter (d_val v) v
  | i_red : forall {k2} (r : redex k2) {t k1} {c : context k1 k2} {d v},
              contract r = Some t -> dec t c d -> iter d v ->
              iter (d_red r c) v.

  Inductive eval : term -> forall {k}, value k -> Prop :=
  | e_intro : forall {t k} {d : decomp k} {v},
                dec t [_] d -> iter d v -> eval t v.


  Lemma dec_id_l : forall {t k1 k2} {c : context k1 k2} {d}, 
                       RS.RS.dec t c d -> dec t c d.
  Proof with eauto.
    induction 1 using RS.dec_Ind with 
    (P := fun t _ _ c d (_ : RS.RS.dec t c d) => dec t c d)
    (P0:= fun _ v _ c d (_ : RS.decctx v c d) => decctx v c d);
    solve 
    [ econstructor; eauto
    | eapply d_term; eauto
    | eapply dc_term; eauto ].
  Qed.
  Hint Resolve dec_id_l.


  Lemma dec_id_r : forall {t k1 k2} {c : context k1 k2} {d}, 
                       dec t c d -> RS.RS.dec t c d.
  Proof with eauto.
    induction 1 using dec_Ind with 
    (P := fun t _ _ c d (_ : dec t c d)    => RS.RS.dec t c d)
    (P0:= fun _ v _ c d (_ : decctx v c d) => RS.decctx v c d);
    solve
    [ econstructor; eauto
    | eapply RS.d_term; eauto
    | eapply RS.dc_term; eauto ].
  Qed.
  Hint Resolve dec_id_r.


  Lemma iterRedPam : forall {k} {d : decomp k} {v}, RS.RS.iter d v -> iter d v.
  Proof with eauto.
    induction 1; econstructor...
    dependent destruction H0.
    apply dec_id_l.
    apply RS.RS.dec_plug in H0.
    - rewrite <- compose_empty in H0...
    - eapply proper_death2... exact [_].
  Qed.


  Lemma evalRedPam : forall {t k} {v : value k},  RS.RS.eval t v -> eval t v.
  Proof with eauto.
    intros.
    dependent destruction H;
    econstructor;
    dependent destruction H...
    apply iterRedPam...
  Qed.
  Hint Resolve evalRedPam.


  Lemma iterPamRed : forall {k} {d : decomp k} {v}, iter d v -> RS.RS.iter d v.
  Proof with eauto.
    induction 1.
    - constructor.
    - econstructor...
      constructor.
      apply RS.RS.dec_plug_rev.
      + eapply proper_death2... exact [_].
      + rewrite <- compose_empty...
  Qed.


  Lemma evalPamRed : forall {t k} {v : value k}, eval t v -> RS.RS.eval t v.
  Proof with eauto.
    intros.
    dependent destruction H.
    econstructor.
    - constructor...
    - apply iterPamRed...
  Qed.
  Hint Resolve evalPamRed.


  Theorem evalPam : forall {t k} {v : value k}, RS.RS.eval t v <-> eval t v.
  Proof with auto.
    split...
  Qed.


  Definition dec_term            := RS.dec_term.
  Definition dec_context         := RS.dec_context.
  Definition dec_term_correct    := RS.dec_term_correct.
  Definition dec_context_correct := RS.dec_context_correct.

End PreAbstractMachine.
