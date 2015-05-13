Require Import Setoid.
Require Export refocusing_signatures.
Require Import Wellfounded.Inclusion.
Require Import Wellfounded.Inverse_Image.
Require Import Program.

Module Lang_Prop (R : RED_LANG) : LANG_PROP R.

  Lemma plug_empty : forall t k, R.plug t (R.empty k) = t.
  Proof.
    intros; simpl; auto.
  Qed.
  Hint Resolve plug_empty : prop.

  Lemma compose_empty : forall k1 k2 (c : R.context k1 k2), c = R.compose c (R.empty _).
  Proof.
    intros. induction c. auto. simpl. rewrite<- IHc. auto.
  Qed.
  Hint Resolve compose_empty : prop.

  Lemma plug_compose : forall k1 k2 (c : R.context k1 k2) k3 (c' : R.context k3 k1) (t : R.term), R.plug t (R.compose c c') = R.plug (R.plug t c) c'.
  Proof.
    intros ? ? ? ? ?. induction c; intro. auto. apply IHc.
  Qed.
  Hint Resolve plug_compose : prop.

End Lang_Prop.

Module RedRefSem (R : RED_REF_LANG) <: RED_REF_SEM R.R.

  Definition dec_term := R.dec_term.
  Definition dec_context := @R.dec_context. Arguments dec_context {k} _ _.
  Inductive dec : R.R.term -> forall {k1 k2}, R.R.context k1 k2 -> R.R.decomp k1 -> Prop :=
  | d_dec  : forall (t : R.R.term) {k1 k2} (c : R.R.context k1 k2) (r : R.R.redex k2)
               (DT  : dec_term t k2 = R.R.in_red r),
               dec t c (R.R.d_red r c)
  | d_v    : forall (t : R.R.term) {k1 k2} (c : R.R.context k1 k2) (v : R.R.value k2) (d : R.R.decomp k1)
               (DT  : dec_term t k2 = R.R.in_val v)
               (R_C : decctx v c d),
               dec t c d
  | d_term : forall (t t0 : R.R.term) {k1 k2} (c : R.R.context k1 k2) (ec : R.R.elem_context k2) (d : R.R.decomp k1)
               (DT  : dec_term t k2 = R.R.in_term t0 ec)
               (R_T : dec t0 (R.R.ccons ec c) d),
               dec t c d
  with decctx : forall {k2}, R.R.value k2 -> forall {k1}, R.R.context k1 k2 -> R.R.decomp k1 -> Prop :=
  | dc_end  : forall {k} (v : R.R.value k), decctx v (R.R.empty _) (R.R.d_val v)
  | dc_dec  : forall {k2} (ec : R.R.elem_context k2) v {k1} (c : R.R.context k1 k2) (r : R.R.redex k2),
                dec_context ec v = R.R.in_red r ->
                decctx v (R.R.ccons ec c) (R.R.d_red r c)
  | dc_val  : forall {k2} (v0 : R.R.value k2) (ec : R.R.elem_context k2) v {k1} (c : R.R.context k1 k2) 
                         (d : R.R.decomp k1)
                (DC  : dec_context ec v = R.R.in_val v0)
                (R_C : decctx v0 c d),
                decctx v (R.R.ccons ec c) d
  | dc_term : forall {k2} (ec ec0 : R.R.elem_context k2) v {k1} (c : R.R.context k1 k2) (t : R.R.term) (d : R.R.decomp k1)
                (DC  : dec_context ec v = R.R.in_term t ec0)
                (R_T : dec t (R.R.ccons ec0 c) d),
                decctx v (R.R.ccons ec c) d.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.
    
  Notation " a <| b " := (R.subterm_order a b) (at level 40).
  Notation " a <: b " := (R.ec_order a b) (at level 40).

  Lemma sto_trans : forall t t0 t1, t <| t0 -> t0 <| t1 -> t <| t1.
  Proof with auto.
    induction 1.
    econstructor 2; eauto.
    econstructor 2; eauto; apply IHclos_trans_1n; auto.  
  Qed.


  Lemma plug_le_eq : forall k1 k2 (c : R.R.context k1 k2) t t0, R.R.plug t0 c = t -> 
                         t0 <| t \/ (c ~= R.R.empty k1 /\ t = t0).
  Proof with auto.
    intros k1 k2.
    induction c; intros.
    simpl in H; right; auto.
    left; simpl in H. destruct (IHc t (R.R.atom_plug t0 ec)); auto. Print t1n_trans.
      apply t1n_trans with (y := R.R.atom_plug t0 ec). econstructor. reflexivity. assumption. 
      destruct H0. subst. rewrite H1. do 2 econstructor. reflexivity.
  Qed.


  Lemma st_c : forall t0 t1, t0 <| t1 -> exists k1 k2 (c : R.R.context k1 k2), R.R.plug t0 c = t1.
  (* zonk *)

  Proof with auto.
    intros t0 t1 H. induction H. inversion H; subst.
    exists (R.R.ccons ec R.R.empty); simpl; auto.
    destruct IHclos_trans_n1 as [c H1].
    exists (c ++ (existT _ k ec :: nil)); unfold R.R.plug in *; rewrite fold_left_app; simpl; subst; auto.
  Qed.

  Definition value_one_step {k} (v v0 : R.R.value k) : Prop := 
      R.subterm_one_step (R.R.value_to_term v) (R.R.value_to_term v0).
  Definition value_order k := clos_trans_n1 (R.R.value k) value_one_step.
    
  Notation " a <v| b " := (value_order a b) (at level 40).
    
  Lemma wf_vo : forall {k}, well_founded (value_order k).
  Proof.
    intro k.
    apply wf_clos_trans_r. unfold value_one_step. apply wf_inverse_image. apply R.wf_st1.
  Qed.

    Reserved Notation " a <v| b " (at level 40).

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
    Qed.

    Lemma dec_val : forall {k} (v : R.R.value k) (c : R.R.context k) (d : R.R.decomp), dec (R.R.value_to_term v) c d -> decctx v c d.
    Proof with eauto.
      intro k.
      induction v using (well_founded_ind wf_vo); intros.

      dependent destruction H0; unfold dec_term in *;
      assert (hh := R.dec_term_correct k (R.R.value_to_term v)); rewrite DT in hh.

      symmetry in hh; contradiction (R.R.value_redex _ _ _ hh).

      rewrite<- (R.R.value_to_term_injective _ _ _ hh).
      assumption.

      destruct (R.R.value_trivial v t (e :: nil)); simpl...
      discriminate H1.
      destruct H1 as [v0 H1]; subst t.
      symmetry in hh; assert (ht := R.st_1 _ _ _ hh);
      apply (tn1_step _ value_one_step) in ht; change (v0 <v| v) in ht.
      inversion H0; subst; unfold dec_term in DT; rewrite DT in Heqi; inversion Heqi; subst.
      clear H0 Heqi DT; assert (H0 := H _ ht _ _ R_T); clear ht R_T.
      generalize dependent v0.
      induction ec using (well_founded_ind R.wf_eco); intros.
      remember (R.dec_context ec v0); assert (hc := R.dec_context_correct ec v0);
      destruct i; rewrite <- Heqi in hc; rewrite <- hh in hc.
      symmetry in hc; contradiction (R.R.value_redex _ _ hc).
      clear H H0; apply R.R.value_to_term_injective in hc; subst.
      inversion H1; subst; unfold dec_context in DC; rewrite DC in Heqi; inversion Heqi; subst; auto.
      destruct (R.R.value_trivial v t (e :: nil)); simpl...
      discriminate.
      destruct H2 as [v1 H2]; subst t.
      inversion H1; subst; unfold dec_context in DC; rewrite DC in Heqi; inversion Heqi; subst.
      clear Heqi H1.
      apply H0 with ec1 v1...
      destruct (R.dec_context_term_next _ _ _ _ DC)...
      apply H...
      repeat econstructor...
    Qed.

    Lemma val_dec : forall v c d, decctx v c d -> dec (R.R.value_to_term v) c d.
    Proof with eauto.
      induction v using (well_founded_ind wf_vo); intros.
      remember (R.dec_term (R.R.value_to_term v)); assert (hh := R.dec_term_correct (R.R.value_to_term v));
      destruct i; rewrite <- Heqi in hh.
      symmetry in hh; contradiction (R.R.value_redex _ _ hh).
      apply R.R.value_to_term_injective in hh; subst; econstructor...
      destruct (R.R.value_trivial v t (e :: nil)); simpl...
      discriminate H1.
      destruct H1 as [v0 H1]; subst t; econstructor 3...
      apply H; [ repeat econstructor | clear Heqi; generalize dependent v0]...
      induction e using (well_founded_ind R.wf_eco); intros.
      remember (R.dec_context e v0); assert (hc := R.dec_context_correct e v0);
      destruct i; rewrite <- Heqi in hc; rewrite hh in hc.
      symmetry in hc; contradiction (R.R.value_redex _ _ hc).
      clear H H1; apply R.R.value_to_term_injective in hc; subst; econstructor...
      destruct (R.R.value_trivial v t (e0 :: nil)); simpl...
      discriminate.
      destruct H2 as [v1 H2]; subst t; econstructor 4...
      apply H.
      repeat econstructor...
      apply H1...
      symmetry in Heqi; destruct (R.dec_context_term_next _ _ _ _ Heqi)...
    Qed.

  Module RS : RED_SEM R.R with Definition dec := dec.
    Definition dec := dec.

    Lemma decompose : forall t : R.R.term, (exists v:R.R.value, t = R.R.value_to_term v) \/
      (exists r:R.R.redex, exists c:R.R.context, R.R.plug (R.R.redex_to_term r) c = t).
    Proof with eauto.
      induction t using (well_founded_ind R.wf_sto); intros.


      remember (R.dec_term t); assert (hh := R.dec_term_correct t); destruct i;
      rewrite <- Heqi in hh.
      right; exists r; exists R.R.empty...
      left; exists v...
      destruct (H t0) as [[v Hv] | [r [c Hrc]]].
      repeat econstructor...
      subst t0; clear Heqi; generalize dependent v; induction e using (well_founded_ind R.wf_eco); intros.
      remember (R.dec_context e v); assert (ht := R.dec_context_correct e v); destruct i;
      rewrite <- Heqi in ht; rewrite hh in ht.
      right; exists r; exists R.R.empty...
      left; exists v0...
      destruct (H t0) as [[v0 Hv] | [r [c Hrc]]].
      repeat econstructor...
      symmetry in Heqi; destruct (R.dec_context_term_next _ _ _ _ Heqi) as [H1 _].
      subst t0; destruct (H0 e0 H1 v0 ht) as [[v1 Hv1] | [r [c Hrc]]].
      left; exists v1...
      right; exists r; exists c...
      right; exists r; exists (c ++ (e0 :: nil)); 
      subst t0; unfold R.R.plug in *; rewrite fold_left_app...
      right; exists r; exists (c ++ (e :: nil));
      subst t0; unfold R.R.plug in *; rewrite fold_left_app...
    Qed.

    Lemma dec_redex_self_e : forall (r : R.R.redex), dec (R.R.redex_to_term r) (R.R.empty) (R.R.d_red r R.R.empty).
    Proof with eauto.
      intros; remember (dec_term (R.R.redex_to_term r)); destruct i; unfold dec_term in Heqi;
      assert (hh := R.dec_term_correct (R.R.redex_to_term r)); rewrite <- Heqi in hh; simpl in hh.
      apply R.R.redex_to_term_injective in hh; subst; constructor...
      contradict hh;  apply R.R.value_redex.
      symmetry in Heqi; assert (H := R.dec_term_term_top _ _ _ Heqi).
      econstructor 3; simpl; eauto.
      destruct (R.R.redex_trivial r t (e :: R.R.empty) hh) as [H1 | [v H1]]; [ discriminate | subst t].
      clear H Heqi.
      generalize dependent v; generalize dependent e.
      induction e using (well_founded_ind R.wf_eco); intros.
      apply val_dec.
      remember (R.dec_context e v); assert (ht := R.dec_context_correct e v);
      rewrite <- Heqi in ht; destruct i; simpl in ht.
      rewrite hh in ht; apply R.R.redex_to_term_injective in ht; subst.
      constructor...
      rewrite <- ht in hh; contradiction (R.R.value_redex _ _ hh).
      econstructor 4; simpl; eauto.
      rewrite hh in ht; destruct (R.R.redex_trivial r t (e0 :: R.R.empty) ht) as [H4 | [v1 H4]].
      discriminate.
      subst t; symmetry in Heqi; destruct (R.dec_context_term_next _ _ _ _ Heqi); apply H...
    Qed.

    Lemma dec_redex_self : forall (r : R.R.redex) (c : R.R.context), dec (R.R.redex_to_term r) c (R.R.d_red r c).
    Proof with eauto.
      intros.
      assert (hh := dec_redex_self_e r).
      induction hh using dec_Ind with
      (P := fun t c0 d (H : dec t c0 d) => match d with
        | R.R.d_val v => True
        | R.R.d_red r' c1 => dec t (R.R.compose c0 c) (R.R.d_red r' (R.R.compose c1 c))
      end)
      (P0:= fun v c0 d (H : decctx v c0 d) => match d with
        | R.R.d_val v => True
        | R.R.d_red r' c1 => decctx v (R.R.compose c0 c) (R.R.d_red r' (R.R.compose c1 c))
      end); try destruct d; auto; 
      [ constructor | econstructor | econstructor 3 | constructor | econstructor | econstructor 4]...
    Qed.

    Lemma dec_correct : forall t c d, dec t c d -> R.R.decomp_to_term d = R.R.plug t c.    
    Proof.
      induction 1 using dec_Ind with
      (P := fun t c d (H:dec t c d) => R.R.decomp_to_term d = R.R.plug t c)
      (P0:= fun v c d (H:decctx v c d) => R.R.decomp_to_term d = R.R.plug (R.R.value_to_term v) c); 
      simpl; auto; match goal with
      | [ DT: (dec_term ?t = ?int) |- _ ] => unfold dec_term in DT; assert (hh := R.dec_term_correct t); rewrite DT in hh
      | [ DC: (dec_context ?ec ?v = ?int) |- _ ] => unfold dec_context in DC; assert (hh := R.dec_context_correct ec v); rewrite DC in hh
      end; try rewrite IHdec; rewrite <- hh; subst; auto.
    Qed.

    Lemma dec_plug_rev : forall c c0 t d, dec t (R.R.compose c c0) d -> dec (R.R.plug t c) c0 d.
    Proof with auto.
      induction c; intros; simpl; auto.
      apply IHc; clear IHc; remember (R.dec_term (R.R.atom_plug t a)); destruct i;
      assert (hh := R.dec_term_correct (R.R.atom_plug t a)); rewrite <- Heqi in hh.
      symmetry in Heqi; discriminate ( R.dec_term_red_empty _ _ Heqi t (a :: nil)); reflexivity.
      symmetry in Heqi; discriminate (R.dec_term_val_empty _ _ Heqi t (a :: nil))...
      destruct (R.dec_ec_ord t0 t e a hh) as [H0 | [H0 | [H0 H1]]]; try (subst; econstructor 3; eauto; fail).
      symmetry in Heqi; contradict (R.dec_term_term_top _ _ _ Heqi _ H0).
      symmetry in hh; destruct (R.elem_context_det _ _ _ _ H0 hh) as [v H1]; subst t0.
      econstructor 3; eauto.
      clear Heqi; generalize dependent v; generalize dependent e.
      induction e using (well_founded_ind R.wf_eco); intros.
      apply val_dec.
      remember (R.dec_context e v); destruct i; symmetry in Heqi;
      assert (ht := R.dec_context_correct e v); rewrite Heqi in ht.
      contradiction (R.dec_context_red_bot _ _ _ Heqi a).
      contradiction (R.dec_context_val_bot _ _ _ Heqi a).
      destruct (R.dec_context_term_next _ _ _ _ Heqi) as [H2 H3].
      econstructor 4; eauto; rewrite <- hh in ht.
      destruct (R.dec_ec_ord _ _ _ _ ht) as [H4 | [H4 | [H4 H5]]]; try (subst; auto; fail).
      contradiction (H3 a H1).
      symmetry in ht; clear H3; destruct (R.elem_context_det _ _ _ _ H4 ht) as [v0 H5]; subst t0.
      apply H0; auto.
    Qed.

    Lemma dec_plug : forall c c0 t d, dec (R.R.plug t c) c0 d -> dec t (R.R.compose c c0) d.
    Proof with auto.
      induction c; intros; simpl; auto.
      apply IHc in H; clear IHc; inversion H; subst; unfold dec_term in DT; clear H;
      assert (hh := R.dec_term_correct (R.R.atom_plug t a)); rewrite DT in hh.
      discriminate (R.dec_term_red_empty _ _ DT t (a :: nil)); reflexivity.
      symmetry in hh; discriminate (R.dec_term_val_empty _ _ DT t (a :: R.R.empty))...
      destruct (R.dec_ec_ord t1 t ec a hh) as [H2 | [H2 | [H2 H3]]].
      contradiction (R.dec_term_term_top _ _ _ DT a).
      symmetry in hh; destruct (R.elem_context_det _ _ _ _ H2 hh) as [v H3]; subst t1.
      clear DT; generalize dependent v; generalize dependent ec.
      induction ec using (well_founded_ind R.wf_eco); intros.
      assert (H0 := dec_val _ _ _ R_T); inversion H0; subst; clear R_T;
      assert (ht := R.dec_context_correct ec v); unfold dec_context in DC; rewrite DC in ht; simpl in ht.
      contradiction (R.dec_context_red_bot _ _ _ DC a).
      contradiction (R.dec_context_val_bot _ _ _ DC a).
      clear H0.
      rewrite <- hh in ht.
      destruct (R.dec_context_term_next _ _ _ _ DC).
      destruct (R.dec_ec_ord _ _ _ _ ht) as [hq | [hq | [hq hw]]].
      contradiction (H1 a).
      symmetry in ht; destruct (R.elem_context_det _ _ _ _ hq ht) as [v1 h4]; subst t0.
      apply H with ec1 v1; auto.
      subst; auto.
      subst; auto.
    Qed.

    Inductive decempty : R.R.term -> R.R.decomp -> Prop :=
    | d_intro : forall (t : R.R.term) (d : R.R.decomp), dec t R.R.empty d -> decempty t d.

    Inductive iter : R.R.decomp -> R.R.value -> Prop :=
    | i_val : forall (v : R.R.value), iter (R.R.d_val v) v
    | i_red : forall (r : R.R.redex) (t : R.R.term) (c : R.R.context) (d : R.R.decomp) (v : R.R.value),
                R.R.contract r = Some t -> decempty (R.R.plug t c) d -> iter d v -> iter (R.R.d_red r c) v.

    Inductive eval : R.R.term -> R.R.value -> Prop :=
    | e_intro : forall (t : R.R.term) (d : R.R.decomp) (v : R.R.value), decempty t d -> iter d v -> eval t v.

  End RS.

  Definition dec_term_correct := R.dec_term_correct.
  Definition dec_context_correct := R.dec_context_correct.

  Lemma dec_val_self : forall v c d, dec (R.R.value_to_term v) c d <-> decctx v c d.
  Proof.
    split; [apply dec_val | apply val_dec]; auto.
  Qed.

End RedRefSem.