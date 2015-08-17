Require Import Utils.
Require Import Program.
Require Import no_ecca.
Require Import refocusing_lang_facts.



Module no_ECCa_Sem <: RED_SEM no_ECCa.

  Import no_ECCa.


  Inductive dec' : term -> forall {k1 k2}, context k1 k2 -> decomp k1 -> Prop :=

  | d_CVar   : forall x {k1} (c : context k1 C) d,
                decctx (vCVar x) c d ->
                dec' (Var x) c d 
  | d_ECaVar : forall x {k1} (c : context k1 ECa) d,
                decctx (vECaVar x) c d ->
                dec' (Var x) c d 
  | d_CLam  : forall x t {k1} (c : context k1 C) d,
                dec' t (lam_c x =: c) d ->
                dec' (Lam x t) c d
  | d_ECaLam : forall x t {k1} (c : context k1 ECa) d,
                decctx (vECaLam x t) c d ->
                dec' (Lam x t) c d
  | d_CApp   : forall t1 t2 {k1} (c : context k1 C) d,
                dec' t1 (ap_r t2 =: c) d ->
                dec' (App t1 t2) c d
  | d_ECaApp : forall t1 t2 {k1} (c : context k1 ECa) d,
                dec' t1 (ap_r t2 =: c) d ->
                dec' (App t1 t2) c d

  with decctx : forall {k2}, value k2 -> 
                forall {k1}, context k1 k2 -> decomp k1 -> Prop :=

  | dc_em       : forall {k} (v : value k),
                   ~ dead_ckind k ->
                   decctx v [.] (d_val v)
  | dc_CAp_r1   : forall x t0 t {k1} (c : context k1 C),
                   decctx (vECaLam x t0) (ap_r t =: c) (d_red (rCApp x t0 t) c)
  | dc_CAp_r2   : forall x t {k1} (c : context k1 C) d,
                   dec' t (ap_l (vCaVar x) =: c) d ->
                   decctx (vECaVar x) (ap_r t =: c) d
  | dc_CAp_r3   : forall v1 v2 t {k1} (c : context k1 C) d,
                   dec' t (ap_l (vCaApp v1 v2) =: c) d ->
                   decctx (vECaApp v1 v2) (ap_r t =: c) d
  | dc_ECaAp_r1 : forall x t0 t {k1} (c : context k1 ECa),
                   decctx (vECaLam x t0) (ap_r t =: c) (d_red (rECaApp x t0 t) c)
  | dc_ECaAp_r2 : forall x t {k1} (c : context k1 ECa) d,
                   dec' t (ap_l (vCaVar x) =: c) d ->
                   decctx (vECaVar x) (ap_r t =: c) d
  | dc_ECaAp_r3 : forall v1 v2 t {k1} (c : context k1 ECa) d,
                   dec' t (ap_l (vCaApp v1 v2) =: c) d ->
                   decctx (vECaApp v1 v2) (ap_r t =: c) d
  | dc_CAp_l    : forall v1 v2 {k1} (c : context k1 C) d,
                   decctx (vCApp v1 v2) c d ->
                   decctx v2 (ap_l v1 =: c) d
  | dc_ECaAp_l  : forall v1 v2 {k1} (c : context k1 ECa) d,
                   decctx (vECaApp v1 v2) c d ->
                   decctx v2 (ap_l v1 =: c) d
  | dc_CLam     : forall v x {k1} (c : context k1 C) d,
                   decctx (vCLam x v) c d ->
                   decctx v (lam_c x =: c) d.

  Definition dec t {k1 k2} (c : context k1 k2) d := dec' t c d.
  Scheme dec_Ind := Induction for dec' Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Lemma dead_decctx_dead : forall k1 (c : context k1 CBot) v d, ~ decctx v c d.
  Proof.
  intros. intro.
  dependent destruction H.
  simpl in H.
  compute in H; auto.
  Qed.

  Ltac inj_vr := match goal with
  | [Hv : value_to_term _ = value_to_term _ |- _] => apply value_to_term_injective in Hv
  | [Hv : valCa_to_term _ = valCa_to_term _ |- _] => apply valCa_to_term_injective in Hv
  | [Hr : redex_to_term _ = redex_to_term _ |- _] => apply redex_to_term_injective in Hr
  | [ |- _] => idtac
  end.
(*
  Lemma L3 : forall x t y v, vECaLam x t <> vECaApp (vCaVar y) v.
  Proof.
  intros.
  intro.
  discriminate H.
  Qed.*)

  Lemma dec_val_self : forall {k2} (v : value k2) {k1} (c : context k1 k2) d, 
      dec v c d <-> decctx v c d.

  Proof with auto. 
    induction v using val_Ind with
    (P := fun k2 (v : value k2) => forall (k1 : ckind) (c : context k1 k2)
              (d : decomp k1), dec v c d <-> decctx v c d)
    (P0:= fun v0 => forall (k1 k2 : ckind) (c : context k1 k2) (v : value k2)
              (d : decomp k1), (v0 : term) = (v : term) -> 
              (dec v c d <-> decctx v c d));

    intros;
    try match goal with [ H: (valCa_to_term ?v0) = (value_to_term ?v1) |- _ ] => 
        match type of v0 with valCa => 
            destruct v1; autof; 
            inversion H; repeat inj_vr; subst; 
            clear H
        end
    end;

    split; intro H1;

    dependent destruction H1;
    solve
    (* Cases of: dec v c d -> decctx v c d. *)
    [ rewrite IHv in H1;
      dependent destruction H1;
      auto
    | match goal with v : valCa |- _ =>
      destruct valCa_is_valECa with v as (v', H2);
      destruct v; dependent destruction v'; autof;
      inversion H2; repeat inj_vr; subst;
      rewrite H2 in H1;
      rewrite IHv in H1; auto;
      dependent destruction H1;
      rewrite IHv0 in H;
      dependent destruction H;
      auto
      end 

    (* Cases of: dec v c d <- decctx v c d. *)
    | constructor; (* imaginary fold *)
      try (rewrite IHv; constructor); 
      constructor; 
      auto
    | match goal with v : valCa |- _ =>
      constructor; (* imaginary fold *) fold valCa_to_term;
      destruct valCa_is_valECa with v as (v', H2);
      destruct v; dependent destruction v'; autof;
      inversion H2; repeat inj_vr; subst;
      rewrite H2;
      rewrite IHv; auto; constructor;
      rewrite IHv0; constructor;
      constructor;
      auto
      end

    (* Cases of both implications. *)
    | autof ].
  Qed.


  (** A redex in context will only ever be reduced to itself *)
  Lemma dec_redex_self : forall {k2} (r : redex k2) {k1} (c : context k1 k2), 
                             dec (redex_to_term r) c (d_red r c).
  Proof with auto.
    destruct r; intros; constructor;
    rewrite (dec_val_self (vECaLam v t)); constructor.
  Qed.

  Lemma decompose : forall (t : term) k1, ~ dead_ckind k1 ->
      (exists (v : value k1), t = v) \/
      (exists k2 (r : redex k2) (c : context k1 k2), t = c[r]).

  Proof with auto.
    induction t; intros.
    - destruct IHt1 with ECa as [(v1, H1) | (k2, (r1, (c1, H1)))].
          discriminate.
      assert (G0 : ~ dead_ckind C).
          discriminate.
      assert (G := IHt2 C G0);
      clear IHt1 IHt2;
      subst.
      + dependent destruction v1; subst.
        * right. exists k1. 
          destruct k1; 
              try solve [contradict H; compute; trivial];
          [ eexists (rCApp _ _ _), [.]
          | eexists (rECaApp _ _ _), [.] ];
          reflexivity.
        *{
          destruct G as [(v2, H1) | (k2, (r2, (c2, H1)))]; subst.
          - left. 
            destruct k1;  
                try solve [contradict H; compute; trivial];
            [ exists (vCApp (vCaVar v) v2)
            | exists (vECaApp (vCaVar v) v2) ];
            auto.
          - right.
            destruct k1; 
              try solve [contradict H; compute; trivial];
            [ exists k2 r2 (c2 ~+ ap_l (vCaVar v) =: (@empty C))
            | exists k2 r2 (c2 ~+ ap_l (vCaVar v) =: (@empty ECa)) ];
            simpl; rewrite plug_compose; auto. }
        * {
          destruct G as [(v2, H1) | (k2, (r2, (c2, H1)))]; subst.
          - left.
            destruct k1; 
                try solve [contradict H; compute; trivial];
            [ exists (vCApp (vCaApp v v1) v2)
            | exists (vECaApp (vCaApp v v1) v2) ];
            auto.
          - right.
            destruct k1; 
                try solve [contradict H; compute; trivial];
            [ exists k2 r2 (c2 ~+ ap_l (vCaApp v v1) =: (@empty C))
            | exists k2 r2 (c2 ~+ ap_l (vCaApp v v1) =: (@empty ECa)) ];
            rewrite plug_compose; auto. }
      + right.
        destruct k1; 
              try solve [contradict H; compute; trivial];
        [ exists k2 r1 (c1 ~+ ap_r t2 =: (@empty C))
        | exists k2 r1 (c1 ~+ ap_r t2 =: (@empty ECa)) ];
        rewrite plug_compose; simpl; congruence.
    - left. 
      destruct k1; 
          try solve [contradict H; compute; trivial];
      [ exists (vCVar v)
      | exists (vECaVar v) ];
      auto.
    - destruct k1; 
          try solve [contradict H; compute; trivial].
      + destruct (IHt C) as [(v1, ?) | (k, (r1, (c, ?)))]; subst...
        * left. exists (vCLam v v1)...
        * right. exists k r1 (c ~+ lam_c v =: (@empty C)).
          rewrite plug_compose; auto.
      + left. exists (vECaLam v t)...
    Qed.

  (** dec is left inverse of plug *)
  Lemma dec_correct : forall {t k1 k2} {c : context k1 k2} {d}, 
                          dec t c d -> c[t] = d.
  Proof.
    induction 1 using dec_Ind with
    (P := fun t _ _ c d (H:dec t c d) => c[t] = d)
    (P0 := fun _ v _ c d (H:decctx v c d) => c[v] = d);
    intros; simpl; auto.
  Qed.

  Include RED_LANG_Facts no_ECCa.

  Lemma dec_plug : forall k1 k2 (c : context k1 k2) k3 (c0 : context k3 k1) t d, 
                          ~ dead_ckind k2 -> dec (plug t c) c0 d -> 
                          dec t (c ~+ c0) d.
  Proof.
    induction c; simpl; auto; destruct ec0;
    intros ? c0 t0 d H DEC; assert (hh := IHc _ _ _ _ (death_propagation2 _ _ H) DEC);
    dependent destruction hh; subst; auto; simpl in H; try solve [contradict H; compute; trivial];
      destruct (valCa_is_valECa v) as (vc, G);
      rewrite G in hh; rewrite dec_val_self in hh;
      dependent destruction hh; destruct v; try discriminate;
      inversion G; repeat (inj_vr; subst); auto.
  Qed.

  Lemma dec_plug_rev : forall k1 k2 (c : context k1 k2) k3 (c0 : context k3 k1) t d, 
                          ~ dead_ckind k2 ->  dec t (c ~+ c0) d -> 
                          dec (plug t c) c0 d.
  Proof.
    induction c; simpl; auto; destruct ec0; intros; apply IHc;
    try solve [ eapply context_tail_liveness; eauto ];
    destruct k2; simpl in H; try solve [discriminate | contradict H; compute; auto | constructor; auto | auto];
      destruct (valCa_is_valECa v);
      simpl; constructor; rewrite H1;
      apply dec_val_self;
      destruct v; dependent destruction x; try discriminate H1; 
      inversion H1; repeat (inj_vr; subst);
      constructor; auto.
  Qed.

  Inductive decempty : term -> forall {k}, decomp k -> Prop :=
  | d_intro : forall (t : term) {k} (d : decomp k), dec t (@empty k) d -> decempty t d.

  Inductive iter : forall {k}, decomp k -> value k -> Prop :=
  | i_val : forall {k} (v : value k), iter (d_val v) v
  | i_red : forall {k} (r : redex k) t {k'} (c : context k' k) d v,
              contract r = Some t -> decempty (plug t c) d -> iter d v ->
              iter (d_red r c) v.

  Inductive eval : term -> value init_ckind -> Prop :=
  | e_intro : forall {t d v}, decempty t d -> iter d v -> eval t v.



  Lemma redex_trivial : forall k (r : redex k), only_trivial r k.
  Proof with auto.
    intros k1 r t k2 c; revert t.
    induction c.
    - intuition.
    - intros.
      right.
      destruct IHc with (ec0:[t]) as [(H1, H2) | (v0, H1)]; auto;
          try solve [contradict H0; apply death_propagation; auto];
      dep_subst; 
      simpl in *;
      match goal with
      | [Hvr : ?ec :[ ?t ] = _ ?r |- _] => 
            destruct ec; destruct r; 
            dependent_destruction2 Hvr
      end; simpl in *;
      try solve [ contradict H0; compute; trivial
                | exists (vECaLam v t1); auto 
                | dependent destruction v; discriminate
                | eexists; eauto
                | apply valCa_is_valECa
                | eexists (vCBot _); simpl; eauto ].
  Qed.

End no_ECCa_Sem.


Lemma dec_sem_ref : forall t k1 k2 (c : no_ECCa.context k1 k2) d, 
                        no_ECCa_Sem.dec t c d -> no_ECCa_REF_SEM.dec t c d.
Proof.
  induction 1 using no_ECCa_Sem.dec_Ind with
  (P := fun t _ _ c d (H : no_ECCa_Sem.dec t c d) => no_ECCa_REF_SEM.dec t c d)
  (P0:= fun _ v _ c d (H : no_ECCa_Sem.decctx v c d) => no_ECCa_REF_SEM.decctx v c d);
  try solve 
  [ econstructor; simpl; eauto
  | econstructor 3; simpl; eauto
  | eapply (@no_ECCa_REF_SEM.dc_dec)  with (ec:=no_ECCa.ap_r t)(k2:= no_ECCa.C); simpl; auto
  | eapply (@no_ECCa_REF_SEM.dc_term) with (ec:=no_ECCa.ap_r t)(k2:= no_ECCa.C); simpl; eauto 
  | eapply (@no_ECCa_REF_SEM.dc_dec)  with (ec:=no_ECCa.ap_r t)(k2:= no_ECCa.ECa); simpl; auto
  | eapply (@no_ECCa_REF_SEM.dc_term) with (ec:=no_ECCa.ap_r t)(k2:= no_ECCa.ECa); simpl; eauto
  | eapply (@no_ECCa_REF_SEM.dc_val)  with (ec:=no_ECCa.ap_l v1)(k2:= no_ECCa.C); simpl; auto
  | eapply (@no_ECCa_REF_SEM.dc_val)  with (ec:=no_ECCa.ap_l v1)(k2:= no_ECCa.ECa); simpl; auto
  | eapply (@no_ECCa_REF_SEM.dc_val)  with (ec:=no_ECCa.lam_c x)(k2:= no_ECCa.C); simpl; auto
].
Qed.
Hint Resolve dec_sem_ref.
 
Lemma dec_ref_sem : forall t k1 k2 (c : no_ECCa.context k1 k2) d, 
                        no_ECCa_REF_SEM.dec t c d -> no_ECCa_Sem.dec t c d.
Proof.
  induction 1 using no_ECCa_REF_SEM.dec_Ind with
  (P := fun t _ _ c d (H : no_ECCa_REF_SEM.dec t c d) => no_ECCa_Sem.dec t c d)
  (P0:= fun _ v _ c d (H : no_ECCa_REF_SEM.decctx v c d) => no_ECCa_Sem.decctx v c d);
  try (destruct t, k2); try inversion e; subst;
  try solve 
  [ discriminate 
  | constructor; auto 
  | destruct ec; try destruct k2; dependent destruction v; inversion e; subst; constructor; auto ].
Qed.
Hint Resolve dec_ref_sem.

Lemma iter_sem_ref : forall k (d : no_ECCa.decomp k) v, 
                         no_ECCa_Sem.iter d v <-> no_ECCa_REF_SEM.RS.iter d v.
Proof with eauto with no_ecca.
split; intros H; dependent induction H; subst; simpl in *; auto; try solve [constructor];
dependent destruction H0; econstructor 2; simpl in *; eauto; constructor; first [apply dec_sem_ref | apply dec_ref_sem]; eauto.
Qed.

Lemma eval_sem_ref : forall t v, 
                         no_ECCa_Sem.eval t v <-> no_ECCa_REF_SEM.RS.eval t v.
Proof with auto.
  split;
  (
      intro H;
      dependent destruction H; econstructor;
      try solve 
      [ apply iter_sem_ref; eauto
      | dependent destruction H; constructor; 
        first [apply dec_sem_ref | apply dec_ref_sem]; eauto ]
  ).
Qed.



Module ECCa_Machine <: ABSTRACT_MACHINE.

Import no_ECCa.
Import ECCa_EAM.


Notation " [$ t $] " := (c_init t) (at level 60, no associativity).
Notation " [: v :] " := (c_final v) (at level 60).
Notation " [$ t , c $] " := (c_eval t c) (at level 60).
Notation " [: c , v :] " := (c_apply c v) (at level 60).
Notation " [; c , v ;] " := (@c_apply _ ECa c v) (at level 60).


Reserved Notation " a → b " (at level 40).


Definition vVar k x := match k with C => vCVar x | ECa => vECaVar x | CBot => vCBot (Var x) end.

Inductive trans : configuration -> configuration -> Prop :=
| t_evarC    : forall x {k1} (c : context k1 C),
                  [$ Var x,   c $]   → [: c, vCVar x :]
| t_evarECa  : forall x {k1} (c : context k1 ECa),
                  [$ Var x,   c $]   → [: c, vECaVar x :]
| t_elamC    : forall x t {k1} (c : context k1 C),
                  [$ Lam x t, c $]   → [$ t, lam_c x=:c $]
| t_elamECa  : forall x t {k1} (c : context k1 ECa),
                  [$ Lam x t, c $]   → [: c, vECaLam x t :]
| t_eappC    : forall t1 t2 {k1} (c : context k1 C),
                  [$ App t1 t2, c $] → [$ t1, ap_r t2=:c $]
| t_eappECa  : forall t1 t2 {k1} (c : context k1 ECa),
                  [$ App t1 t2, c $] → [$ t1, ap_r t2=:c $]

| t_alamC    : forall x t1 t2 {k1} (c : context k1 C) {t0},
                   contract (rCApp x t1 t2) = Some t0 ->
                   [: ap_r t2=:c, vECaLam x t1 :] → [$ t0, c $]
| t_alamECa  : forall x t1 t2 {k1} (c : context k1 ECa) {t0},
                   contract (rECaApp x t1 t2) = Some t0 ->
                   [: ap_r t2=:c, vECaLam x t1 :] → [$ t0, c $]
| t_aVarC    : forall x t {k1} (c : context k1 C),
                   [: ap_r t=:c, vECaVar x :]     → [$ t, ap_l (vCaVar x)=:c $]
| t_aVarECa  : forall x t {k1} (c : context k1 ECa),
                   [: ap_r t=:c, vECaVar x :]     → [$ t, ap_l (vCaVar x)=:c $]
| t_aAppC    : forall v1 v2 t {k1} (c : context k1 C),
                   [: ap_r t=:c, vECaApp v1 v2 :] → [$ t, ap_l (vCaApp v1 v2)=:c $]
| t_aAppECa  : forall v1 v2 t {k1} (c : context k1 ECa),
                   [: ap_r t=:c, vECaApp v1 v2 :] → [$ t, ap_l (vCaApp v1 v2)=:c $]
| t_aValC    : forall v1 v2 {k1} (c : context k1 C),
                   [: ap_l v1=:c, v2 :]           → [: c, vCApp v1 v2 :]
| t_aValECa  : forall v1 v2 {k1} (c : context k1 ECa),
                   [: ap_l v1=:c, v2 :]           → [: c, vECaApp v1 v2 :]
| t_aValCLam : forall x v {k1} (c : context k1 C),
                   [: lam_c x=:c, v :]            → [: c, vCLam x v :]
where " a → b " := (trans a b).
Definition transition := trans.

Notation " a >> b " := (ECCa_EAM.transition a b) (at level 40).
Notation " a >>+ b " := (ECCa_EAM.AM.trans_close a b) (at level 40).

Reserved Notation " a →+ b " (at level 40, no associativity).


  Inductive trans_close : configuration -> configuration -> Prop :=
  | one_step   : forall (c0 c1 : configuration), 
                     (c0 → c1) -> trans_close c0 c1
  | multi_step : forall (c0 c1 c2 : configuration), 
                     (c0 → c1) -> trans_close c1 c2 -> trans_close c0 c2
  where " a →+ b " := (trans_close a b).

  Inductive eval : term -> value init_ckind -> Prop :=
  | e_intro : forall t v, trans_close (c_init t) (c_final v) -> eval t v.


Lemma trans_eam_mlm : forall c0 c1, c0 >> c1 -> c0 → c1.
Proof with auto.
  intros c0 c1 T; inversion T; subst;
  let dec_term    := no_ECCa_REF_SEM.DEC.dec_term in
  let dec_context := no_ECCa_REF_SEM.DEC.dec_context in
  match goal with
  | [ DT : dec_term ?t ?k2 = ?int |- _ ] => destruct t, k2; inversion DT
  | [ DC : dec_context ?ec ?k2 ?v = ?int |- _ ] => destruct ec, k2; dependent_destruction2 v; inversion DC
  | [ |- _ ] => idtac
  end; subst; try constructor; auto.
Qed.
Hint Resolve trans_eam_mlm.


Lemma tcl_eam_mlm : forall c0 c1, c0 >>+ c1 -> c0 →+ c1.
Proof with eauto.
  intros c0 c1 TC; induction TC; unfold ECCa_EAM.AM.transition in *;
  [econstructor | econstructor 2]...
Qed.


Lemma eval_eam_mlm : forall t v, ECCa_EAM.AM.eval t v -> eval t v.
Proof.
  intros t v E; dependent destruction E; constructor; apply tcl_eam_mlm; auto.
Qed.


Lemma trans_mlm_eam : forall c0 c1, c0 → c1 -> c0 >> c1.
Proof with auto.
  intros w w' H; inversion H; subst; econstructor; simpl...
Qed.
Hint Resolve trans_mlm_eam.


Lemma tcl_mlm_eam : forall c0 c1, c0 →+ c1 -> c0 >>+ c1.
Proof with eauto.
  induction 1; subst; [econstructor | econstructor 2]; unfold ECCa_EAM.AM.transition...
Qed.


Lemma eval_mlm_eam : forall t v, eval t v -> ECCa_EAM.AM.eval t v.
Proof.
  intros t v E; inversion_clear E; constructor; apply tcl_mlm_eam; auto.
Qed.


Theorem ECCa_Machine_correct : forall t v, no_ECCa_Sem.eval t v <-> eval t v.
Proof.
  intros; rewrite eval_sem_ref; rewrite ECCa_EAM.eval_apply_correct;
  split; [apply eval_eam_mlm | apply eval_mlm_eam].
Qed.



Definition term  := term.
Definition value := value init_ckind.

Definition configuration := configuration.
Definition c_init  := c_init.
Definition c_final := c_final.

End ECCa_Machine.