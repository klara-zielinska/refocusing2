Require Import Utils.
Require Import Program.
Require Import no_ecca.
Require Import refocusing_lang_facts.



Module no_ECCa_HandSem <: RED_SEM no_ECCa.

  Module RF := RED_LANG_Facts no_ECCa.
  Import no_ECCa.
  Import RF.


  Lemma decompose : forall (t : term) k1, ~ dead_ckind k1 ->
      (exists (v : value k1), t = v) \/
      (exists k2 (r : redex k2) (c : context k1 k2), t = c[r]).

  Proof with autof.
    induction t; intros k1 H.

    - destruct IHt1 with ECa as [(v1, ?) | (k2, (r1, (c1, ?)))]; autof;
          assert (~ dead_ckind C) as G; autof;
          assert (G0 := IHt2 C G);
          clear IHt1 IHt2;
          subst.

      +{ dependent destruction v1; subst.

         - right.
           exists k1.
           destruct k1...
           + eexists (rCApp _ _ _),   [.]; simpl...
           + eexists (rECaApp _ _ _), [.]; simpl...

         - destruct G0 as [(v2, ?) | (k2, (r2, (c2, ?)))]; subst.
           + left.
             destruct k1...
             * exists (vCApp (vCaVar v) v2)...
             * exists (vECaApp (vCaVar v) v2)...
           + right.
             destruct k1; autof;
             [ exists k2 r2 (c2 ~+ ap_l (vCaVar v) =: [.](C))
             | exists k2 r2 (c2 ~+ ap_l (vCaVar v) =: [.](ECa)) ];
             rewrite plug_compose...

         - destruct G0 as [(v2, ?) | (k2, (r2, (c2, ?)))]; subst.
           + left.
             destruct k1...
             * exists (vCApp (vCaApp v v1) v2)...
             * exists (vECaApp (vCaApp v v1) v2)...
           + right.
             destruct k1; autof;
             [ exists k2 r2 (c2 ~+ ap_l (vCaApp v v1) =: [.](C))
             | exists k2 r2 (c2 ~+ ap_l (vCaApp v v1) =: [.](ECa)) ];
             rewrite plug_compose... }

      + right.
        destruct k1; autof;
        [ exists k2 r1 (c1 ~+ ap_r t2 =: [.](C))
        | exists k2 r1 (c1 ~+ ap_r t2 =: [.](ECa)) ];
        rewrite plug_compose...

    - left.
      destruct k1...
      + exists (vCVar v)...
      + exists (vECaVar v)...

    - destruct k1...
      + destruct (IHt C) as [(v1, ?) | (k, (r1, (c, ?)))]; subst...
        * left; exists (vCLam v v1)...
        * right.
          exists k r1 (c ~+ lam_c v =: [.](C)).
          rewrite plug_compose...
      + left; exists (vECaLam v t)...
  Qed.



  Inductive __dec : term -> forall {k1 k2}, context k1 k2 -> decomp k1 -> Prop :=

  | d_CVar   : forall x {k1} (c : context k1 C) d,
                 decctx (vCVar x) c d ->
                 __dec (Var x) c d 
  | d_ECaVar : forall x {k1} (c : context k1 ECa) d,
                 decctx (vECaVar x) c d ->
                 __dec (Var x) c d 

  | d_CLam   : forall x t {k1} (c : context k1 C) d,
                 __dec t (lam_c x =: c) d -> (*!*)
                 __dec (Lam x t) c d
  | d_ECaLam : forall x t {k1} (c : context k1 ECa) d,
                 decctx (vECaLam x t) c d -> (*!*)
                 __dec (Lam x t) c d

  | d_CApp   : forall t1 t2 {k1} (c : context k1 C) d,
                 __dec t1 (ap_r t2 =: c) d ->
                 __dec (App t1 t2) c d
  | d_ECaApp : forall t1 t2 {k1} (c : context k1 ECa) d,
                 __dec t1 (ap_r t2 =: c) d ->
                 __dec (App t1 t2) c d

  with decctx : forall {k2}, value k2 -> 
                forall {k1}, context k1 k2 -> decomp k1 -> Prop :=

  | dc_em       : forall {k} (v : value k),
                    ~ dead_ckind k ->
                    decctx v [.] (d_val v)

  | dc_CAp_r1   : forall x t0 t {k1} (c : context k1 C),
                    decctx (vECaLam x t0) (ap_r t =: c) (d_red (rCApp x t0 t) c)
  | dc_ECaAp_r1 : forall x t0 t {k1} (c : context k1 ECa),
                    decctx (vECaLam x t0) (ap_r t =: c) (d_red (rECaApp x t0 t) c)

  | dc_CAp_r2   : forall x t {k1} (c : context k1 C) d,
                    __dec t (ap_l (vCaVar x) =: c) d ->
                    decctx (vECaVar x) (ap_r t =: c) d
  | dc_ECaAp_r2 : forall x t {k1} (c : context k1 ECa) d,
                    __dec t (ap_l (vCaVar x) =: c) d ->
                    decctx (vECaVar x) (ap_r t =: c) d

  | dc_CAp_r3   : forall v1 v2 t {k1} (c : context k1 C) d,
                    __dec t (ap_l (vCaApp v1 v2) =: c) d ->
                    decctx (vECaApp v1 v2) (ap_r t =: c) d
  | dc_ECaAp_r3 : forall v1 v2 t {k1} (c : context k1 ECa) d,
                    __dec t (ap_l (vCaApp v1 v2) =: c) d ->
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

  Definition dec := __dec. Arguments dec t {k1 k2} c d.

  Scheme dec_Ind    := Induction for __dec Sort Prop
    with decctx_Ind := Induction for decctx Sort Prop.


  (* Non-signature entries (helpers) *)

  Lemma dead_decctx_dead : 
      forall {k1} (c : context k1 CBot) v d, ~ decctx v c d.

  Proof with autof.
    intros; intro H.
    dependent destruction H...
  Qed.


  Ltac inj_vr := 
      match goal with
      | [Hv : value_to_term _ = value_to_term _ |- _] => 
            apply value_to_term_injective in Hv
      | [Hv : valCa_to_term _ = valCa_to_term _ |- _] => 
            apply valCa_to_term_injective in Hv
      | [Hr : redex_to_term _ = redex_to_term _ |- _] => 
            apply redex_to_term_injective in Hr
      | [ |- _] => idtac
      end.


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



  (* Signature entries *)

  Lemma dec_correct : forall {t k1 k2} {c : context k1 k2} {d}, 
                          dec t c d -> c[t] = d.
  Proof with auto.
    induction 1 using dec_Ind with
    (P  := fun t _ _ c d (_ : dec t c d)    => c[t] = d)
    (P0 := fun _ v _ c d (_ : decctx v c d) => c[v] = d)...
  Qed.


  Lemma dec_plug :
      forall {k1 k2} (c : context k1 k2) {k3} {c0 : context k3 k1} {t d}, 
          ~ dead_ckind k2 -> dec c[t] c0 d -> dec t (c ~+ c0) d.
  Proof.
    induction c.
    - auto.
    - intros k3 c0 t0 d H H0.
      destruct ec0;
          assert (hh := IHc _ _ _ _ (death_propagation2 _ _ H) H0);
          dependent destruction hh; subst;
      solve
      [ autof
      | destruct valCa_is_valECa with v as (v', H2);
        destruct v; dependent destruction v'; 
        solve
        [ autof
        | inversion H2; repeat inj_vr; subst;
          rewrite H2 in hh;
          rewrite dec_val_self in hh;
          dependent destruction hh;
          auto 
      ] ].
  Qed.


  Lemma dec_plug_rev :
      forall {k1 k2} (c : context k1 k2) {k3} {c0 : context k3 k1} {t d}, 
          ~ dead_ckind k2 -> dec t (c ~+ c0) d -> dec c[t] c0 d.
  Proof.
    induction c.
    - auto.
    - intros k3 c0 t d H H0.
      simpl.
      apply IHc; eauto using death_propagation2.
      destruct ec0, k2;
      solve 
      [ autof 
      | constructor; auto
      | match goal with v : valCa |- _ =>
        destruct (valCa_is_valECa v) as (v', H1);
        destruct v; dependent destruction v'; 
        inversion H1; repeat inj_vr; subst;
        constructor;
        rewrite H1;
        apply dec_val_self;
        constructor;
        assumption
        end ].
  Qed.


  Lemma dec_redex_self : forall {k2} (r : redex k2) {k1} (c : context k1 k2), 
                             dec (redex_to_term r) c (d_red r c).
  Proof with auto.
    destruct r as [x t1 t2 | x t1 t2];
    solve
    [ intros;
      constructor;
      rewrite (dec_val_self (vECaLam x t1));
      constructor ].
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

End no_ECCa_HandSem.



Module no_ECCa_REF_SEM_Check.

  Import no_ECCa_Ref.

  Module HS := no_ECCa_HandSem.
  Module RS := no_ECCa_REF_SEM.


  Lemma HS_dec_imp_RS_dec : 
      forall t {k1 k2} (c : context k1 k2) d, HS.dec t c d -> RS.dec t c d.

  Proof.
    induction 1 using HS.dec_Ind with
    (P := fun t _ _ c d (_ : HS.dec t c d)    =>  RS.dec t c d)
    (P0:= fun _ v _ c d (_ : HS.decctx v c d) =>  RS.decctx v c d);
    solve
    [ econstructor; simpl; eauto
    | eapply @RS.d_term; simpl; eauto 
    | eapply @RS.dc_dec  with (ec:=ap_r _) (k2:= C);   simpl; auto
    | eapply @RS.dc_term with (ec:=ap_r _) (k2:= C);   simpl; eauto 
    | eapply @RS.dc_dec  with (ec:=ap_r _) (k2:= ECa); simpl; auto
    | eapply @RS.dc_term with (ec:=ap_r _) (k2:= ECa); simpl; eauto
    | eapply @RS.dc_val  with (ec:=ap_l _) (k2:= C);   simpl; auto
    | eapply @RS.dc_val  with (ec:=ap_l _) (k2:= ECa); simpl; auto
    | eapply @RS.dc_val  with (ec:=lam_c _)(k2:= C);   simpl; auto ].
  Qed.
  (*Hint Resolve dec_sem_ref.*)
 

  Lemma RS_dec_imp_HS_dec : 
      forall t {k1 k2} (c : context k1 k2) d, RS.dec t c d -> HS.dec t c d.

  Proof.
    induction 1 using RS.dec_Ind with
    (P := fun t _ _ c d (_ : RS.dec t c d)    => HS.dec t c d)
    (P0:= fun _ v _ c d (_ : RS.decctx v c d) => HS.decctx v c d);
    solve 
  [ match goal with H : dec_term _ _ = _ |- _ =>
    destruct t, k2; 
    inversion H; subst; 
    constructor; auto
    end
  | match goal with H : dec_context _ _ _ = _ |- _ =>
    destruct ec0, k2; dependent destruction v; 
    inversion H; subst; 
    constructor; auto
    end 
  | constructor; auto ].
  Qed.
  (*Hint Resolve dec_ref_sem.*)


  Lemma dec_eqv : 
      forall t {k1 k2} (c : context k1 k2) d, HS.dec t c d <-> RS.dec t c d.

  Proof.
    split;
    eauto using RS_dec_imp_HS_dec, HS_dec_imp_RS_dec.
  Qed.


  Lemma decempty_eqv : 
      forall t {k} (d : decomp k), HS.decempty t d <-> RS.RS.decempty t d.

  Proof with auto.
    split; 
    (
        intro H;
        dependent_destruction2 H;
        constructor;
        apply dec_eqv; auto
    ).
  Qed.


  Lemma iter_eqv : forall {k} (d : decomp k) v, 
                           HS.iter d v <-> RS.RS.iter d v.
  Proof.
    split; intro H;
    dependent induction H;
    solve
    [ constructor
    | econstructor; 
      solve 
      [ eauto
      | eapply decempty_eqv; eauto
    ] ].
  Qed.


  Lemma eval_eqv : 
      forall t v, HS.eval t v <-> RS.RS.eval t v.

  Proof with auto.
    split; intro H;
    (
        dependent destruction H;
        econstructor;
        [ apply decempty_eqv; eauto
        | apply iter_eqv; eauto ]
    ).
  Qed.

End no_ECCa_REF_SEM_Check.



Module ECCa_Machine <: ABSTRACT_MACHINE.

  Import no_ECCa.
  Import ECCa_EAM.


  Notation " [$ t $] " := (c_init t) (at level 60, no associativity).
  Notation " [: v :] " := (c_final v) (at level 60).
  Notation " [$ t , c $] " := (c_eval t c) (at level 60).
  Notation " [: c , v :] " := (c_apply c v) (at level 60).
  Notation " [; c , v ;] " := (@c_apply _ ECa c v) (at level 60).


  Reserved Notation " a → b " (at level 40).


  Inductive trans : configuration -> configuration -> Prop :=

  | t_eVarC    : forall x {k1} (c : context k1 C),
                    [$ Var x,   c $]   → [: c, vCVar x :]
  | t_eVarECa  : forall x {k1} (c : context k1 ECa),
                    [$ Var x,   c $]   → [: c, vECaVar x :]

  | t_eLamC    : forall x t {k1} (c : context k1 C),
                    [$ Lam x t, c $]   → [$ t, lam_c x=:c $]  (*!*)
  | t_eLamECa  : forall x t {k1} (c : context k1 ECa),
                    [$ Lam x t, c $]   → [: c, vECaLam x t :] (*!*)

  | t_eAppC    : forall t1 t2 {k1} (c : context k1 C),
                    [$ App t1 t2, c $] → [$ t1, ap_r t2=:c $]
  | t_eAppECa  : forall t1 t2 {k1} (c : context k1 ECa),
                    [$ App t1 t2, c $] → [$ t1, ap_r t2=:c $]

  | t_aLamC    : forall x t1 t2 {k1} (c : context k1 C) {t0},
                     contract (rCApp x t1 t2) = Some t0 ->
                     [: ap_r t2=:c, vECaLam x t1 :] → [$ t0, c $]
  | t_aLamECa  : forall x t1 t2 {k1} (c : context k1 ECa) {t0},
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


  Definition term  := term.
  Definition value := value init_ckind.

  Definition configuration := configuration.
  Definition c_init  := c_init.
  Definition c_final := c_final.

End ECCa_Machine.



Module ECCa_Machine_Check.

  Import ECCa_Machine.

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


  Theorem ECCa_Machine_correct : forall t v, no_ECCa_HandSem.eval t v <-> eval t v.
  Proof.
    intros; rewrite no_ECCa_REF_SEM_Check.eval_eqv; rewrite ECCa_EAM.eval_apply_correct;
    split; [apply eval_eam_mlm | apply eval_mlm_eam].
  Qed.

End ECCa_Machine_Check.