Require Import Util.
Require Import Program.
Require Export refocusing_semantics.
Require Import refocusing_lang.
Require Import reduction_semantics_facts.



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

  with decctx : forall {k2}, value k2 -> 
                    forall {k1}, context k1 k2 -> decomp k1 -> Prop :=

  | dc_end  : forall {k} (v : value k), 
                ~ dead_ckind k ->
                decctx v [.] (d_val v)
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

  Scheme dec_Ind    := Induction for dec Sort Prop
    with decctx_Ind := Induction for decctx Sort Prop.


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
    induction H.
    - destruct H as [ec H]; subst.
      exists (k1+>ec); eexists (ec=:[.]).
      simpl...
    - destruct IHclos_trans_1n as (k2, (c, H1)). 
      destruct H as [ec H]; subst.
      exists (k2+>ec); exists (ec=:c)...
  Qed.


  Lemma dec_not_dead : forall {t k1 k2} {c : context k1 k2} {d},
                           dec t c d -> ~ dead_ckind k2.
  Proof.
    intros; intro.
    assert (hh := dec_term_from_dead t k2 H0).
    destruct H;
    solve
    [ rewrite H in hh;
      discriminate hh ].
  Qed.


  Lemma decctx_not_dead : forall {k1 k2} {c : context k1 k2} {v d},
                              decctx v c d -> ~ dead_ckind k2.
  Proof with auto.
    intros; intro.
    destruct H;
    solve 
    [ intuition
    | assert (hh := dec_context_from_dead ec k2 v H0);
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


  Lemma dec_val : forall {k2} (v : value k2) {k1} {c : context k1 k2} {d},
                      dec v c d -> decctx v c d.
  Proof with eauto.
    intros k2 v k1; remember (value_to_term v) as t; revert k2 v Heqt.
    induction t using (well_founded_ind wf_sto); intros; subst.

    dependent destruction H0;
        assert (hh := dec_term_correct v k2); rewrite H0 in hh.

    - contradiction (value_redex _ _ hh).

    - rewrite (value_to_term_injective _ _ hh)...

    - destruct (value_trivial v t0 _ (ec=:[.])); auto;
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

          destruct (value_trivial v t _ (ec1=:[.])); auto;
              try solve 
              [ simpl; congruence];
              destruct H5.
          + discriminateJM H6.
          + eapply (H0 ec1); eauto.
            * rewrite hh; eapply dec_context_term_next; eauto.
            * congruence.
        }
  Qed.


  Lemma val_dec : forall {k2} {v : value k2} {k1} {c : context k1 k2} {d},
                      decctx v c d -> dec v c d.
  Proof with eauto.
    intros k2 v k1; remember (value_to_term v); revert k2 v Heqt.
    induction t using (well_founded_ind wf_sto); intros; subst.

    remember (dec_term v k2) as i;
    assert (hh := dec_term_correct v k2);
    destruct i; rewrite <- Heqi in hh; symmetry in Heqi.

    - contradict (value_redex _ _ hh).

    - apply (d_term _ Heqi).

      assert (~ dead_ckind (k2+>e)) as Hndk.
        { eapply dec_term_next_alive... }
      destruct (value_trivial v t _ (e=:[.]));
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

        - assert (~ dead_ckind (k2+>e0)).
          {
              destruct ec_order_comp_fi with k2 v e0 e as (?, (?, (?, ?)))...
              - rewrite hh; eapply dec_context_term_next...
          }

          destruct (value_trivial v t0 _ (e0=:[.]));
              try solve [simpl; congruence];
              destruct H3.

          + discriminateJM H4.

          + apply dc_term with e0 t0...
            apply (H1 e0) with x0...
            * rewrite hh; eapply dec_context_term_next...
            * congruence.

        - eapply dc_val...
          assert (v0 = v).
          + apply (value_to_term_injective v0 v); congruence.
          + subst...

        - intuition.
      }

    - assert (H1 := value_to_term_injective _ _ hh); subst; econstructor...

    - contradiction (decctx_not_dead H0).
  Qed.



  Module RS : RED_SEM R.R with Definition dec := dec.

    Lemma decompose : 
        forall (t : term) k1, ~ dead_ckind k1 ->
            (exists (v : value k1), t = v) \/
            (exists k2 (r : redex k2) (c : context k1 k2), t = c[r]).

    Proof with eauto.
      induction t using (well_founded_ind wf_sto); intros.

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
          induction e using (well_founded_ind (wf_eco k1 t)); intros.

          remember (dec_context e _ v); assert (ht := dec_context_correct e _ v); 
          destruct i; rewrite <- Heqi in ht; try rewrite <- hh in ht.

          - right; exists k1; exists r; eexists [.]...

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


    Lemma dec_redex_self_e : forall {k} (r : redex k), dec r [.] (d_red r [.]).
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

        { subst t.
          clear H0 Heqi; generalize dependent v; generalize dependent e.
          induction e using (well_founded_ind (wf_eco k r)); intros.

          apply val_dec.
          remember (dec_context e _ v); assert (ht := dec_context_correct e _ v);
          rewrite <- Heqi in ht; symmetry in Heqi.

          destruct i; simpl in ht.

          - rewrite hh in ht.
            apply redex_to_term_injective in ht; subst.
            constructor...

          - econstructor 4...
            rewrite ht in hh.
            assert (~ dead_ckind (k+>e0)).
              { eapply dec_context_not_dead... }
            destruct (redex_trivial1 r e0 t H1 hh) as (v1, H4)...
            subst t.
            destruct (dec_context_term_next _ _ _ Heqi).
            apply H0...
            + congruence.

          - rewrite ht in hh; contradiction (value_redex _ _ hh).

          - intuition. 
          }

      - contradict hh; apply value_redex.

      - intuition.
    Qed.


    Lemma dec_redex_self : forall {k2} (r : redex k2) {k1} (c : context k1 k2), 
                               dec r c (d_red r c).
    Proof with eauto.
      intros;
      assert (H := dec_redex_self_e r);
      generalize c.

      (* induction on H *)
      apply dec_Ind with

      (P  := fun t k1' k2' c0 d (_ : dec t c0 d) => 
                 match d with
                 | d_val v        => True
                 | d_red k' r' c1 => forall (c : context k1 k1'), 
                                         dec t (c0~+c) (d_red r' (c1~+c))
                 end)
      (P0 := fun k2' v k1' c0 d (_ : decctx v c0 d) => 
                 match d with
                 | d_val v => True
                 | d_red k' r' c1 => forall (c : context k1 k1'), 
                                         decctx v (c0~+c) (d_red r' (c1~+c))
                 end)
      (d0 := H);
      
      intros;
      try destruct d;
      solve 
      [ auto
      | econstructor;   eauto
      | econstructor 3; eauto
      | econstructor 4; eauto ].
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


    Lemma dec_plug : 
        forall {k1 k2} (c : context k1 k2) {k3} {c0 : context k3 k1} {t d}, 
            ~ dead_ckind k2 -> dec c[t] c0 d -> dec t (c~+c0) d.

    Proof with eauto.
      induction c; intros; simpl.
      - trivial.

      - apply IHc in H0; clear IHc;
        [ | apply (death_propagation2 _ _ H) ].
        inversion H0; subst;
            assert (hh := dec_term_correct (ec:[t]) k2); 
            rewrite H6 in hh.

        + destruct (dec_term_red_empty _ _ H6 t _ (ec=:[.]))...
          discriminateJM H3.

        + destruct (dec_term_val_empty _ _ H6 t _ (ec=:[.]))...
          discriminateJM H4.

        + dep_subst.
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
                  contradiction (dec_context_red_bot _ _ _ H3 _ H2).
                - rewrite hh in H2; 
                  contradiction (dec_context_val_bot _ _ _ H3 _ H2).
                - assert (ht := dec_context_correct ec0 _ v).
                  rewrite H3 in ht.
                  rewrite <- hh in ht.
                  destruct (dec_context_term_next _ _ _ H3) as (H4', H5).
                  destruct ec_order_comp_if with ec:[t] ec2 ec k2 as [H6 | [H6 | H6]].
                      compute...
                      compute...
                      assert (H6 := ec_order_comp_fi _ _ _ _ H4'); intuition.
                      assert (H6 := ec_order_comp_fi _ _ _ _ H2); intuition.

                  + contradiction (H5 ec); rewrite <- hh...
                  + destruct (elem_context_det _ _ ht _ _ H6) as (v1, h4)...
                    subst t0.
                    apply H1 with ec2 v1...
                      { congruence. }
                  + subst; assert (H8 := elem_plug_injective1 _ ht).
                    subst...
            }

          * subst; assert (H8 := elem_plug_injective1 _ hh).
            subst...
    Qed.


    Lemma dec_plug_rev : 
        forall {k1 k2} (c : context k1 k2) {k3} {c0 : context k3 k1} {t d}, 
            ~ dead_ckind k2 -> dec t (c~+c0) d -> dec c[t] c0 d.

    Proof with eauto.
      induction c; intros; simpl.

      - trivial.

      - apply IHc; clear IHc.
        eapply death_propagation2...
        remember (dec_term ec:[t] k2) as i.
        destruct i;
        assert (hh := dec_term_correct ec:[t] k2);
        rewrite <- Heqi in hh;
        symmetry in Heqi.

        + destruct (dec_term_red_empty _ _ Heqi t _ (ec=:[.]))...
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
                  assert (H5 := elem_plug_injective1 _ ht).
                  subst...

              - rewrite hh in H1;
                contradiction (dec_context_val_bot _ _ _ Heqi _ H1).

              - contradict ht.
                eapply ec_order_comp_fi...
            }

          * subst.
            assert (H5 := elem_plug_injective1 _ hh).
            subst.
            econstructor 3...

        + destruct (dec_term_val_empty _ _ Heqi t _ (ec=:[.]))...
          discriminateJM H2.

        + contradict H...
          apply death_propagation...
    Qed.


    Inductive decempty : term -> forall {k}, decomp k -> Prop :=
    | d_intro : forall {t k} {d : decomp k}, dec t [.] d -> decempty t d.

    Inductive iter : forall {k}, decomp k -> value k -> Prop :=
    | i_val : forall {k} (v : value k), iter (d_val v) v
    | i_red : forall {k2} (r : redex k2) {t k1} (c : context k1 k2) {d v},
                contract r = Some t -> decempty c[t] d -> iter d v ->
                iter (d_red r c) v.

    Inductive eval : term -> value init_ckind -> Prop :=
    | e_intro : forall {t} {d : decomp init_ckind} {v : value init_ckind}, 
                  decempty t d -> iter d v -> eval t v.


    Lemma dec_value_self : forall {k} (v : value k), 
                             ~ dead_ckind k -> dec v [.] (d_val v).
    Proof with auto.
      intros.
      apply val_dec.
      constructor...
    Qed.


    Definition dec := dec.

  End RS.



  Lemma dec_val_self : forall {k2} (v : value k2) {k1} (c : context k1 k2) d, 
                           dec v c d <-> decctx v c d.
  Proof.
    split; [apply dec_val | apply val_dec].
  Qed.


  Module ST := ST.

  Definition dec_term    := dec_term.
  Definition dec_context := dec_context.

  Definition dec_term_correct      := dec_term_correct.
  Definition dec_context_correct   := dec_context_correct.
  Definition dec_term_next_alive   := dec_term_next_alive.
  Definition dec_term_from_dead    := dec_term_from_dead.
  Definition dec_context_from_dead := dec_context_from_dead.

End RedRefSem.

